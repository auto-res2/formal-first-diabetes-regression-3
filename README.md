# formal-first-diabetes-regression-3

メインの claim の検証と、信頼性条件の検証を分けて、実験の前に Lean で宣言する試行。

研究の指示: Efron らの糖尿病データセットに線形回帰モデルを当てはめ，テストデータに対する MSE が 3400 を下回るかを調べる

```
C00: 出力された MSE は、信頼性条件を満たす
├─ C01（メインの claim）: 出力された MSE < 3400
│   └─ 宣言（C02〜C09）: データセット、読み込み、分割、当てはめ、予測、MSE、ライブラリの版、計算環境
└─ 信頼性条件
    ├─ 公理（C10〜C12）
    ├─ 宣言どおりに実行されたか（C13〜C36）
    ├─ HARKing をしていない（C37）
    └─ チェリーピッキングをしていない（C38）
```

- claims の宣言: [`formal/lean/Spec.lean`](formal/lean/Spec.lean)（claim 1 つが命題 1 つで、命題の名前が claim の ID）
- 値の取り方: [`formal/verification.json`](formal/verification.json)（どの値を、どの検証器のどの取り方で取るか）
- スキーマ: [`formal/claims.json`](formal/claims.json)（上の 2 つから生成する。検証の結果もここに書く）
- 実験コード: [`src/run_experiment.py`](src/run_experiment.py)

## 流れ

```bash
python3 formal/cli.py schema                      # Spec.lean と verification.json から claims.json を作る
gh workflow run run_experiment.yml -f mode=full   # 実験（GitHub Actions）
gh workflow run verify_claims.yml -f mode=full    # 検証（GitHub Actions）。結果は artifact の claims.json
```
