"""ワークフローが呼ぶ入口。

  python formal/cli.py run full|sanity     宣言された実験を実行し、artifact にするものを run-output/ に集める
  python formal/cli.py schema              Spec.lean と verification.json から、スキーマ（claims.json）の宣言の部分を作る
  python formal/cli.py verify full|sanity  変数の値を検証器から取り、Lean で各 claim を判定し、結果をスキーマに書く
"""
import hashlib
import json
import os
import shutil
import subprocess
import sys
import urllib.request
from pathlib import Path

FORMAL = Path(__file__).parent
RUN_OUTPUT = Path("run-output")
SCHEMA = FORMAL / "claims.json"


def run(mode: str) -> None:
    declaration = json.loads((FORMAL / "declaration.json").read_text(encoding="utf-8"))
    subprocess.run(declaration["command"] + (declaration["sanity_arguments"] if mode == "sanity" else []), check=True)
    # 実験の出力は outputs/ の下に写す。取得の記録と同じ場所に書かせない
    shutil.rmtree(RUN_OUTPUT, ignore_errors=True)
    for path in declaration["outputs"]:
        target = RUN_OUTPUT / "outputs" / path
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(path, target)
    # 取得の記録は実験の後に、実験コードとは別に書く
    fetched = {url: hashlib.sha256(urllib.request.urlopen(url).read()).hexdigest()
               for url in declaration["fetch_urls"]}
    (RUN_OUTPUT / "fetched_urls.json").write_text(json.dumps(fetched, indent=2) + "\n", encoding="utf-8")


def write_schema(record: dict) -> None:
    # 有理数（Fraction）は "分子/分母" の文字列で書く。Values.lean を作るときに有理数に戻る
    SCHEMA.write_text(json.dumps(record, ensure_ascii=False, indent=2, default=str) + "\n", encoding="utf-8")


def schema() -> None:
    import parse_claims
    write_schema(parse_claims.build_schema())


def verify(mode: str) -> None:
    """検証器の値と判定の結果を、スキーマの verified と result に書き足す。宣言の部分は、作り直したものと同じでなければならない。"""
    import parse_claims
    repository = os.environ.get("GITHUB_REPOSITORY") or subprocess.run(
        ["gh", "repo", "view", "--json", "nameWithOwner", "--jq", ".nameWithOwner"],
        check=True, capture_output=True, text=True).stdout.strip()
    record = parse_claims.build_schema()
    committed = json.loads(SCHEMA.read_text(encoding="utf-8"))
    if parse_claims.declaration_part(committed) != json.loads(json.dumps(parse_claims.declaration_part(record))):
        sys.exit("claims.json の宣言の部分が、Spec.lean と verification.json から作ったものと違う（手で書き換えられている）")

    values, errors = parse_claims.query_values(record, repository, mode)
    for name, value in values.items():
        record["variables"][name]["verified"] = {"value": value, "mode": mode, "verify_run": os.environ.get("GITHUB_RUN_ID")}
    for name, reason in errors.items():
        print(f"値が取れない {name}: {reason}")
    parse_claims.write_values(record)
    lean = FORMAL / "lean"
    subprocess.run(["lake", "build", "Spec", "Values"], cwd=lean, check=True)

    available = set(values) | ({"observed"} if "def observed" in (lean / "Values.lean").read_text(encoding="utf-8") else set())
    path = lean / "Candidates.lean"
    path.write_text("\n".join(parse_claims.HEADER + parse_claims.candidates(record, available)) + "\n", encoding="utf-8")
    output = subprocess.run(["lake", "env", "lean", path.name], cwd=lean, capture_output=True, text=True).stdout
    path.unlink()
    results = parse_claims.judge(record, parse_claims.read_axioms(output), errors)
    for claim in record["claims"]:
        claim["result"] = results[claim["id"]]
    parse_claims.write_theorems(record, results, available)
    write_schema(record)
    for name, result in results.items():
        print(f"{name}: {result['status']} {result.get('verdict', '')}" + (f"（{result['reason']}）" if "reason" in result else ""))
    # 真か偽か inconclusive かは研究の結果。検証として失敗なのは、未検証の claim か、公理が宣言されていない claim があるときだけ
    if any(result["status"] == "unverified" or (result["status"] == "unverifiable" and result["axiom"] is None)
           for result in results.values()):
        sys.exit(1)


if __name__ == "__main__":
    command, arguments = sys.argv[1], sys.argv[2:]
    {"run": run, "schema": schema, "verify": verify}[command](*arguments)
