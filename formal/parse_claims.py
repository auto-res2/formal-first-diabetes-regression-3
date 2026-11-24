"""パーサー。Spec.lean（claims の宣言）と verification.json（値の取り方）からスキーマを作り、
検証器を呼び、Lean の値と定理のファイルを書き、Lean の出力から判定を読む。"""
import json
import re
from fractions import Fraction
from pathlib import Path

from verifiers import QUERIES

FORMAL = Path(__file__).parent
LEAN = FORMAL / "lean"
STANDARD_AXIOMS = ["propext", "Classical.choice", "Quot.sound"]
LITERAL = {
    "String": lambda value: json.dumps(value, ensure_ascii=False),
    "Bool": lambda value: str(bool(value)).lower(),
    "ℕ": lambda value: str(int(value)),
    "ℚ": lambda value: f"(({Fraction(value).numerator} : ℚ) / {Fraction(value).denominator})",
    "String × String": lambda value: f"({json.dumps(value[0], ensure_ascii=False)}, {json.dumps(value[1], ensure_ascii=False)})",
}
# proved% は、証明が通った定理だけを参照する。通らなかった定理は Lean が sorry で埋めて残すので、名前があるだけでは使えない
HEADER = ["import Spec", "import Values", "open Spec Values",
          "open Lean Elab Term in",
          "elab \"proved% \" theoremName:ident : term => do",
          "  let name ← realizeGlobalConstNoOverloadWithInfo theoremName",
          "  if (← collectAxioms name).contains ``sorryAx then throwError \"{name} は証明されていない\"",
          "  return mkConst name"]


def lean_literal(lean_type: str, value) -> str:
    if lean_type.startswith("List "):
        item_type = lean_type.removeprefix("List ").strip("()")
        return "[" + ", ".join(lean_literal(item_type, item) for item in value) + "]"
    return LITERAL[lean_type](value)


def _binders(signature: str) -> list[tuple[str, str]]:
    """明示の引数 (a b : T) を、(名前, 型) の組にする。"""
    return [(name, binder_type.strip()) for names, binder_type in re.findall(r"\(([^():]+):((?:[^()]|\([^()]*\))+)\)", signature)
            for name in names.split()]


def read_spec() -> list[dict]:
    """Spec.lean から、claims（abbrev C01 など）を、ID の順に読む。"""
    text = (LEAN / "Spec.lean").read_text(encoding="utf-8")
    claims = []
    for match in re.finditer(r"/-- ((?:(?!-/).)*?) -/\nabbrev (C\d\d)\b(.*?) : Prop :=(.*?)(?=\n\n|\n/--|\ntheorem |\naxiom )", text, re.S):
        explanation, claim_id, signature, body = match.groups()
        # 見出しの階層（## 信頼性条件 / ### 宣言どおりに実行されたか / #### データセット）が、ツリーでの位置になる
        path = {}
        for level, title in re.findall(r"^/-! (#{2,4}) ([^\n]*?) -/$", text[:match.start()], re.M):
            path = {depth: name for depth, name in path.items() if depth < len(level)} | {len(level): title}
        group = " / ".join(path.values())
        claims.append({
            "id": claim_id, "group": group, "explanation": explanation,
            "proposition": f"abbrev {claim_id}{signature} : Prop :={body}",
            "arguments": [{"name": name, "type": binder_type} for name, binder_type in _binders(signature)],
            "proved_in_spec": f"theorem {claim_id}_holds" in text,
            "axiom_in_spec": f"axiom {claim_id}_axiom" in text,
        })
    return sorted(claims, key=lambda claim: claim["id"])


def build_schema() -> dict:
    """宣言の部分のスキーマ。手で書かず、Spec.lean と verification.json から作る。"""
    verification = json.loads((FORMAL / "verification.json").read_text(encoding="utf-8"))
    claims = read_spec()
    for claim in claims:
        claim_id = claim["id"]
        claim["main"] = claim_id == verification["main_claim"]
        if claim_id in verification["unverifiable"]:
            claim["kind"], claim["verifier"], claim["unverifiable"] = "axiom", None, verification["unverifiable"][claim_id]
        elif claim["proved_in_spec"]:
            claim["kind"], claim["verifier"] = "declaration", "Lean"
        elif claim_id in verification["derived"]:
            claim["kind"], claim["verifier"], claim["derived"] = "derived", "Lean", verification["derived"][claim_id]
        else:
            claim["kind"], claim["verifier"] = "", "GitHub"
        unknown = [a["name"] for a in claim["arguments"] if a["name"] not in verification["variables"] and a["name"] != "observed"]
        if unknown:
            raise ValueError(f"{claim_id}: 値の取り方が verification.json に無い: {unknown}")
    return {"instruction": verification["instruction"], "claims": claims,
            "variables": verification["variables"], "axioms": STANDARD_AXIOMS}


def declaration_part(record: dict) -> dict:
    """スキーマから、検証の結果（result、verified）を除いたもの。"""
    return {"instruction": record["instruction"], "axioms": record["axioms"],
            "claims": [{k: v for k, v in claim.items() if k != "result"} for claim in record["claims"]],
            "variables": {name: {k: v for k, v in variable.items() if k != "verified"}
                          for name, variable in record["variables"].items()}}


def query_values(record: dict, repository: str, mode: str) -> tuple[dict, dict[str, str]]:
    """変数を、検証器に問い合わせる。(JSON の値, 取れなかった理由) を返す。"""
    values, errors = {}, {}
    for name, variable in record["variables"].items():
        try:
            values[name] = QUERIES[variable["verifier"]][variable["query"]](repository, mode, name, **variable.get("args", {}))
        except Exception as error:  # 取れなかった値を使う claim だけを、未検証にする
            errors[name] = str(error)
    return values, errors


def write_values(record: dict) -> None:
    """検証済みの値から、Values.lean を書く。Used の項目がすべて揃っていれば、まとめた observed も置く。"""
    lines = ["import Spec", "/-! 検証済みの値。parse_claims.py が生成する。手で編集しない。 -/", "namespace Values"]
    verified = {name: variable for name, variable in record["variables"].items() if "verified" in variable}
    for name, variable in verified.items():
        lines.append(f"def {name} : {variable['type']} := {lean_literal(variable['type'], variable['verified']['value'])}")
    spec = (LEAN / "Spec.lean").read_text(encoding="utf-8")
    fields = re.findall(r"^  (\w+) : ", re.search(r"structure Used where\n(.*?)\n  deriving", spec, re.S).group(1), re.M)
    # Used の項目 dataSha256 には、変数 observedDataSha256 の値が入る
    observed = {field: "observed" + field[0].upper() + field[1:] for field in fields}
    if all(variable in verified for variable in observed.values()):
        lines += ["def observed : Spec.Used where"] + [f"  {field} := {variable}" for field, variable in observed.items()]
    (LEAN / "Values.lean").write_text("\n".join(lines + ["end Values", ""]), encoding="utf-8")


def _statement(claim: dict) -> str:
    return " ".join([claim["id"]] + [argument["name"] for argument in claim["arguments"]])


def _proof(claim: dict) -> str:
    return f"{claim['id']}_axiom" if claim["kind"] == "axiom" else f"{claim['id']}_holds"


def candidates(record: dict, available: set[str]) -> list[str]:
    """各 claim の、真である定理と偽である（否定の）定理。通ったほうが判定になる。値が揃った claim だけを書く。"""
    claims = {claim["id"]: claim for claim in record["claims"]}
    spec = (LEAN / "Spec.lean").read_text(encoding="utf-8")
    axioms, lines, derived = [], [], {}
    for claim in record["claims"]:
        name, statement = claim["id"], _statement(claim)
        if not {a["name"] for a in claim["arguments"]} <= available:
            continue
        if claim["kind"] == "declaration":
            lines.append(f"#print axioms Spec.{name}_holds")
        elif claim["kind"] == "axiom":
            # 値を含む公理は、検証された値に対してだけ宣言する
            if not claim["axiom_in_spec"]:
                axioms.append(f"axiom {name}_axiom : {statement}")
            lines.append(f"#print axioms {name}_axiom")
        elif claim["kind"] == "derived":
            theorem, premises = claim["derived"]["theorem"], claim["derived"]["from"]
            signature = re.search(rf"theorem {theorem}\b(.*?) :\n", spec, re.S).group(1)
            holes = " ".join("_" for _ in _binders(signature))
            # by_comparison は，前提のあとに，値の比較（Lean が計算で決める）を 1 つ渡す
            compared = " (by decide +kernel)" if claim["derived"].get("by_comparison") else ""
            derived[name] = [f"theorem {name}_holds : {statement} := {theorem} {holes} " + " ".join(_proof(claims[i]) for i in premises) + compared,
                             f"#print axioms {name}_holds"]
            if refutation := claim["derived"].get("refutation"):
                derived[name] += [f"theorem {name}_fails : ¬ ({statement}) := {refutation} {holes} " + " ".join(_proof(claims[i]) for i in premises) + compared,
                                  f"#print axioms {name}_fails"]
            # 連言の claim は、偽の成分が 1 つあれば偽。成分の並びは、前提の並びと同じ
            if re.search(r"\bC\d\d\b.*∧", claim["proposition"].split(":=", 1)[1], re.S):
                parts = [".1" if i == 0 else ".2" * i + (".1" if i < len(premises) - 1 else "") for i in range(len(premises))]
                derived[name] += [f"theorem {name}_fails : ¬ ({statement}) := fun h => by first "
                                  + " ".join(f"| exact (proved% {premise}_fails) h{part}" for premise, part in zip(premises, parts)),
                                  f"#print axioms {name}_fails"]
        else:
            lines += [f"theorem {name}_holds : {statement} := by decide +kernel",
                      f"theorem {name}_fails : ¬ ({statement}) := by decide +kernel",
                      f"#print axioms {name}_holds", f"#print axioms {name}_fails"]
    # 導く claims は、verification.json に書いた順（前提が先）に置く
    order = [name for name in json.loads((FORMAL / "verification.json").read_text(encoding="utf-8"))["derived"] if name in derived]
    return axioms + lines + [line for name in order for line in derived[name]]


def read_axioms(lean_output: str) -> dict[str, list[str] | None]:
    """定理ごとの、依存する公理。証明が通らなかった定理は sorryAx に依存する。出力に無い定理は None。"""
    flat = re.sub(r"\s+", " ", lean_output)
    short = lambda name: name.removeprefix("Spec.")
    axioms = {short(name): [] for name in re.findall(r"'([\w.]+)' does not depend on any axioms", flat)}
    axioms |= {short(name): [short(axiom) for axiom in listed.split(", ")]
               for name, listed in re.findall(r"'([\w.]+)' depends on axioms: \[([^\]]*)\]", flat)}
    return axioms


def judge(record: dict, axioms: dict, errors: dict[str, str]) -> dict[str, dict]:
    """claim ごとの結果。真か偽かは、通った定理で決まる。前提が欠けた claim は inconclusive にする。"""
    claims = {claim["id"]: claim for claim in record["claims"]}
    declared = {f"{claim['id']}_axiom" for claim in record["claims"] if claim["kind"] == "axiom"}
    allowed = set(record["axioms"]) | declared
    results = {}

    def passed(name: str) -> list[str] | None:
        used = axioms.get(name)
        return used if used is not None and "sorryAx" not in used and set(used) <= allowed else None

    for claim in record["claims"]:
        name = claim["id"]
        lacking = sorted({a["name"] for a in claim["arguments"]} & set(errors))
        if claim["kind"] == "axiom":
            results[name] = {"status": "unverifiable", "reason": claim["unverifiable"],
                             "axiom": f"{name}_axiom" if axioms.get(f"{name}_axiom") is not None else None}
        elif lacking:
            results[name] = {"status": "unverified", "reason": "値が取れない: " + "、".join(f"{n}（{errors[n]}）" for n in lacking)}
        elif (used := passed(f"{name}_holds")) is not None:
            results[name] = {"status": "verified", "verdict": "真", "axioms": sorted(used)}
        elif (used := passed(f"{name}_fails")) is not None:
            results[name] = {"status": "verified", "verdict": "偽", "axioms": sorted(used)}
        else:
            results[name] = {"status": "inconclusive"}
    # inconclusive の理由: 成り立たなかった前提
    for claim in record["claims"]:
        result = results[claim["id"]]
        if result["status"] != "inconclusive":
            continue
        failed = [i for i in claim.get("derived", {}).get("from", [])
                  if not (results[i]["status"] == "unverifiable" and results[i]["axiom"]) and results[i].get("verdict") != "真"]
        result["reason"] = ("成り立たなかった前提: " + "、".join(failed)) if failed else "真の定理も偽の定理も通らなかった"
    return results


def write_theorems(record: dict, results: dict, available: set[str]) -> None:
    """判定が付いた命題を、真なら定理、偽なら否定の定理として Theorems.lean に書く。"""
    keep = {f"{name}_{'holds' if result['verdict'] == '真' else 'fails'}" for name, result in results.items() if "verdict" in result}
    lines = HEADER + ["/-! 各命題の判定。parse_claims.py が生成する。手で編集しない。 -/"]
    for line in candidates(record, available):
        theorem = re.match(r"theorem (\w+)", line)
        if line.startswith("axiom ") or (theorem and theorem.group(1) in keep):
            lines.append(line)
    (LEAN / "Theorems.lean").write_text("\n".join(lines) + "\n", encoding="utf-8")
