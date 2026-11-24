import Mathlib
/-!
研究の指示: Efron らの糖尿病データセットに線形回帰モデルを当てはめ，テストデータに対する MSE が 3400 を下回るかを調べる。

実験の前に宣言するもの。claim 1 つが命題 1 つで，命題の名前が claim の ID。
ID はツリーの順（C00 → メインの claim → 宣言 → 信頼性条件）に振る。
ファイルの中の並びは，Lean が使う前に宣言を求めるので，この順ではない（C00 と C13 が後ろに来る）。
検証器が取る値は，命題の引数で受ける。

既存のライブラリにある計算は，数学的な定義を書かず，そのライブラリの関数として置く。
-/

namespace Spec

/-! ## メインの claim -/

/-- 出力された MSE は 3400 を下回る。 -/
abbrev C01 (outputTestMse : ℚ) : Prop := outputTestMse < 3400

/-! ## 宣言 -/

/-! ### データセット -/

def datasetUrl : String := "https://www4.stat.ncsu.edu/~boos/var.select/diabetes.tab.txt"
def datasetSha256 : String := "4733febee697862c22139cdac87478a300ce0d101593deb07ed6c0f3328a99cd"
abbrev sampleCount : ℕ := 442
abbrev featureCount : ℕ := 10
def featureColumns : List String := ["AGE", "SEX", "BMI", "BP", "S1", "S2", "S3", "S4", "S5", "S6"]
def targetColumn : String := "Y"
/-- Efron らが用いた糖尿病データセットのファイルの SHA-256（中身の無い記号）。 -/
opaque efronDatasetSha256 : String

/-- データセット: Efron らの糖尿病データセットを使用する。
- 配布元の URL から取得する
- 取得するファイルの SHA-256 を固定する
- 442 件，説明変数は 10 個（AGE，SEX，BMI，BP，S1〜S6），目的変数は Y -/
abbrev C02 : Prop :=
  datasetUrl = "https://www4.stat.ncsu.edu/~boos/var.select/diabetes.tab.txt" ∧
  datasetSha256 = "4733febee697862c22139cdac87478a300ce0d101593deb07ed6c0f3328a99cd" ∧
  sampleCount = 442 ∧ featureCount = 10 ∧
  featureColumns = ["AGE", "SEX", "BMI", "BP", "S1", "S2", "S3", "S4", "S5", "S6"] ∧ targetColumn = "Y"
theorem C02_holds : C02 := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ### 読み込み -/

def loadFunction : String := "numpy.loadtxt"
/-- numpy.loadtxt に渡す引数。1 行目（列名）を読み飛ばす。 -/
def loadArguments : List (String × String) := [("skiprows", "1")]
/-- NumPy の loadtxt が返す表の，1〜10 列目（説明変数）。 -/
opaque loadedFeatures (arguments : List (String × String)) : Fin sampleCount → Fin featureCount → ℝ
/-- NumPy の loadtxt が返す表の，11 列目（目的変数）。 -/
opaque loadedTarget (arguments : List (String × String)) : Fin sampleCount → ℝ
def features : Fin sampleCount → Fin featureCount → ℝ := loadedFeatures loadArguments
def target : Fin sampleCount → ℝ := loadedTarget loadArguments

/-- 読み込み: numpy.loadtxt を，skiprows=1 で使用する。
- 1〜10 列目を説明変数，11 列目を目的変数とする
- 読み込んだ値は加工しない -/
abbrev C03 : Prop :=
  loadFunction = "numpy.loadtxt" ∧ loadArguments = [("skiprows", "1")] ∧
  features = loadedFeatures [("skiprows", "1")] ∧ target = loadedTarget [("skiprows", "1")]
theorem C03_holds : C03 := ⟨rfl, rfl, rfl, rfl⟩

/-! ### 分割 -/

def splitFunction : String := "sklearn.model_selection.train_test_split"
/-- train_test_split に渡す引数。シード 0，テストデータの割合 20%。ほかの引数は渡さない。 -/
def splitArguments : List (String × String) := [("test_size", "0.2"), ("random_state", "0")]
/-- scikit-learn の train_test_split が返す，テストデータの行。 -/
opaque trainTestSplit (arguments : List (String × String)) : Finset (Fin sampleCount)
def testRows : Finset (Fin sampleCount) := trainTestSplit splitArguments
def trainRows : Finset (Fin sampleCount) := testRowsᶜ

/-- 分割: train_test_split を，シード 0（random_state=0），テストデータの割合 20%（test_size=0.2）で使用する。
- ほかの引数は渡さない
- テストデータ以外の行を訓練データとする -/
abbrev C04 : Prop :=
  splitFunction = "sklearn.model_selection.train_test_split" ∧
  splitArguments = [("test_size", "0.2"), ("random_state", "0")] ∧
  testRows = trainTestSplit [("test_size", "0.2"), ("random_state", "0")] ∧ trainRows = testRowsᶜ
theorem C04_holds : C04 := ⟨rfl, rfl, rfl, rfl⟩

/-! ### 当てはめ -/

def fitFunction : String := "sklearn.linear_model.LinearRegression.fit"
/-- 当てはめるときの LinearRegression のパラメータ。LinearRegression には引数を渡さないので，scikit-learn 1.7.2 の既定値。 -/
def fitParameters : List (String × String) :=
  [("copy_X", "True"), ("fit_intercept", "True"), ("n_jobs", "None"), ("positive", "False"), ("tol", "1e-06")]
opaque FittedModelType : NonemptyType
/-- 当てはめたモデル。 -/
def FittedModel : Type := FittedModelType.type
instance : Nonempty FittedModel := FittedModelType.property
/-- scikit-learn の LinearRegression.fit が返す，当てはめたモデル。 -/
noncomputable opaque fit (parameters : List (String × String)) (rows : Finset (Fin sampleCount))
    (features : Fin sampleCount → Fin featureCount → ℝ) (target : Fin sampleCount → ℝ) : FittedModel
noncomputable def fittedModel : FittedModel := fit fitParameters trainRows features target

/-- 当てはめ: LinearRegression.fit を使用する。
- LinearRegression には引数を渡さない（パラメータは既定値）
- 訓練データの説明変数 10 個すべてと目的変数を，そのまま渡す -/
abbrev C05 : Prop :=
  fitFunction = "sklearn.linear_model.LinearRegression.fit" ∧
  fitParameters =
    [("copy_X", "True"), ("fit_intercept", "True"), ("n_jobs", "None"), ("positive", "False"), ("tol", "1e-06")] ∧
  fittedModel = fit fitParameters trainRows features target
theorem C05_holds : C05 := ⟨rfl, rfl, rfl⟩

/-! ### 予測 -/

def predictFunction : String := "sklearn.linear_model.LinearRegression.predict"
/-- scikit-learn の LinearRegression.predict が返す予測値。 -/
opaque predict (model : FittedModel) (x : Fin featureCount → ℝ) : ℝ
noncomputable def prediction (i : Fin sampleCount) : ℝ := predict fittedModel (features i)

/-- 予測: LinearRegression.predict を使用する。
- 当てはめたモデルに，説明変数をそのまま渡す -/
abbrev C06 : Prop :=
  predictFunction = "sklearn.linear_model.LinearRegression.predict" ∧
  prediction = fun i => predict fittedModel (features i)
theorem C06_holds : C06 := ⟨rfl, rfl⟩

/-! ### MSE -/

def mseFunction : String := "sklearn.metrics.mean_squared_error"
/-- scikit-learn の mean_squared_error が返す値。 -/
opaque meanSquaredError (rows : Finset (Fin sampleCount)) (target prediction : Fin sampleCount → ℝ) : ℝ
/-- 宣言したとおりに計算した，テストデータに対する MSE。 -/
noncomputable def specifiedTestMse : ℝ := meanSquaredError testRows target prediction

/-- MSE: mean_squared_error を使用する。
- テストデータの目的変数と予測値を渡す。ほかの引数は渡さない -/
abbrev C07 : Prop :=
  mseFunction = "sklearn.metrics.mean_squared_error" ∧
  specifiedTestMse = meanSquaredError testRows target prediction
theorem C07_holds : C07 := ⟨rfl, rfl⟩

/-! ### ライブラリの版 -/

def scikitLearnVersion : String := "1.7.2"
def numpyVersion : String := "2.3.4"
def scipyVersion : String := "1.18.1"

/-- ライブラリの版: scikit-learn 1.7.2，NumPy 2.3.4，SciPy 1.18.1 を使用する。
- SciPy は，LinearRegression.fit が内部で呼ぶ -/
abbrev C08 : Prop := scikitLearnVersion = "1.7.2" ∧ numpyVersion = "2.3.4" ∧ scipyVersion = "1.18.1"
theorem C08_holds : C08 := ⟨rfl, rfl, rfl⟩

/-! ### 計算環境 -/

def pythonVersion : String := "3.13.3"
def operatingSystem : String := "ubuntu-24.04"
def cpuArchitecture : String := "x86_64"

/-- 計算環境: Python 3.13.3，ubuntu-24.04，x86_64 を使用する。 -/
abbrev C09 : Prop := pythonVersion = "3.13.3" ∧ operatingSystem = "ubuntu-24.04" ∧ cpuArchitecture = "x86_64"
theorem C09_holds : C09 := ⟨rfl, rfl, rfl⟩

/-! ## 信頼性条件 -/

/-- 実行が使ったもの。 -/
structure Used where
  dataSha256 : String
  sampleCount : ℕ
  featureCount : ℕ
  featureColumns : List String
  targetColumn : String
  loadFunction : String
  loadArguments : List (String × String)
  splitFunction : String
  splitArguments : List (String × String)
  fitFunction : String
  fitParameters : List (String × String)
  fitFeatureCount : ℕ
  predictFunction : String
  mseFunction : String
  scikitLearnVersion : String
  numpyVersion : String
  scipyVersion : String
  pythonVersion : String
  operatingSystem : String
  cpuArchitecture : String
  deriving Inhabited

/-! ### 宣言どおりに実行されたか -/

/-- 出力された MSE は，宣言したとおりに計算した MSE である。 -/
abbrev C13 (outputTestMse : ℚ) : Prop := (outputTestMse : ℝ) = specifiedTestMse

/-! #### データセット -/

/-- 実行が読んだファイルの SHA-256 は，宣言した SHA-256 と一致する。 -/
abbrev C14 (observedDataSha256 : String) : Prop := observedDataSha256 = datasetSha256
/-- 宣言した URL から取得したファイルの SHA-256 は，宣言した SHA-256 と一致する。 -/
abbrev C15 (fetchedSha256 : String) : Prop := fetchedSha256 = datasetSha256
/-- 実行が読んだファイルは，Efron らが用いた糖尿病データセットである。 -/
abbrev C16 (observedDataSha256 : String) : Prop := observedDataSha256 = efronDatasetSha256
/-- 実行が読んだデータの件数は，宣言した件数と一致する。 -/
abbrev C17 (observedSampleCount : ℕ) : Prop := observedSampleCount = sampleCount
/-- 実行が読んだ説明変数の数は，宣言した数と一致する。 -/
abbrev C18 (observedFeatureCount : ℕ) : Prop := observedFeatureCount = featureCount
/-- 実行が説明変数として読んだ列は，宣言した列と一致する。 -/
abbrev C19 (observedFeatureColumns : List String) : Prop := observedFeatureColumns = featureColumns
/-- 実行が目的変数として読んだ列は，宣言した列と一致する。 -/
abbrev C20 (observedTargetColumn : String) : Prop := observedTargetColumn = targetColumn

/-! #### 読み込み -/

/-- 実行が読み込みに呼んだ関数は，宣言した関数と一致する。 -/
abbrev C21 (observedLoadFunction : String) : Prop := observedLoadFunction = loadFunction
/-- 実行が読み込みの関数に渡した引数は，宣言した引数と一致する。 -/
abbrev C22 (observedLoadArguments : List (String × String)) : Prop := observedLoadArguments = loadArguments

/-! #### 分割 -/

/-- 実行が分割に呼んだ関数は，宣言した関数と一致する。 -/
abbrev C23 (observedSplitFunction : String) : Prop := observedSplitFunction = splitFunction
/-- 実行が分割の関数に渡した引数は，宣言した引数と一致する。 -/
abbrev C24 (observedSplitArguments : List (String × String)) : Prop := observedSplitArguments = splitArguments
/-- 実行が使った訓練データの行とテストデータの行は，重ならず，合わせると宣言した全件になる。 -/
abbrev C25 (observedTrainIndex observedTestIndex : List ℕ) : Prop :=
  Disjoint observedTrainIndex.toFinset observedTestIndex.toFinset ∧
  observedTrainIndex.toFinset ∪ observedTestIndex.toFinset = Finset.range sampleCount

/-! #### 当てはめ -/

/-- 実行が当てはめに呼んだ関数は，宣言した関数と一致する。 -/
abbrev C26 (observedFitFunction : String) : Prop := observedFitFunction = fitFunction
/-- 実行が当てはめたときの LinearRegression のパラメータは，宣言したパラメータと一致する。 -/
abbrev C27 (observedFitParameters : List (String × String)) : Prop := observedFitParameters = fitParameters
/-- 実行が当てはめに使った説明変数の数は，宣言した説明変数の数と一致する。 -/
abbrev C28 (observedFitFeatureCount : ℕ) : Prop := observedFitFeatureCount = featureCount

/-! #### 予測 -/

/-- 実行が予測に呼んだ関数は，宣言した関数と一致する。 -/
abbrev C29 (observedPredictFunction : String) : Prop := observedPredictFunction = predictFunction

/-! #### MSE -/

/-- 実行が MSE の計算に呼んだ関数は，宣言した関数と一致する。 -/
abbrev C30 (observedMseFunction : String) : Prop := observedMseFunction = mseFunction

/-! #### ライブラリの版 -/

/-- 実行が使った scikit-learn の版は，宣言した版と一致する。 -/
abbrev C31 (observedScikitLearnVersion : String) : Prop := observedScikitLearnVersion = scikitLearnVersion
/-- 実行が使った NumPy の版は，宣言した版と一致する。 -/
abbrev C32 (observedNumpyVersion : String) : Prop := observedNumpyVersion = numpyVersion
/-- 実行が使った SciPy の版は，宣言した版と一致する。 -/
abbrev C33 (observedScipyVersion : String) : Prop := observedScipyVersion = scipyVersion

/-! #### 計算環境 -/

/-- 実行が使った Python の版は，宣言した版と一致する。 -/
abbrev C34 (observedPythonVersion : String) : Prop := observedPythonVersion = pythonVersion
/-- 実行が使った OS（GitHub Actions の runner の種類）は，宣言した OS と一致する。 -/
abbrev C35 (observedOperatingSystem : String) : Prop := observedOperatingSystem = operatingSystem
/-- 実行が使った CPU のアーキテクチャは，宣言したアーキテクチャと一致する。 -/
abbrev C36 (observedCpuArchitecture : String) : Prop := observedCpuArchitecture = cpuArchitecture

/-- 使ったものが，すべて宣言したものである。 -/
def UsedAsDeclared (used : Used) : Prop :=
  C16 used.dataSha256 ∧ C17 used.sampleCount ∧ C18 used.featureCount ∧ C19 used.featureColumns ∧
  C20 used.targetColumn ∧ C21 used.loadFunction ∧ C22 used.loadArguments ∧
  C23 used.splitFunction ∧ C24 used.splitArguments ∧
  C26 used.fitFunction ∧ C27 used.fitParameters ∧ C28 used.fitFeatureCount ∧
  C29 used.predictFunction ∧ C30 used.mseFunction ∧
  C31 used.scikitLearnVersion ∧ C32 used.numpyVersion ∧ C33 used.scipyVersion ∧
  C34 used.pythonVersion ∧ C35 used.operatingSystem ∧ C36 used.cpuArchitecture

/-! ### 公理 -/

/-- 実行が実際に使ったもの（中身の無い記号）。 -/
opaque actualUsed : Used
/-- 実行が実際に計算した，テストデータに対する MSE（中身の無い記号）。 -/
opaque actualTestMse : ℝ
/-- 実験コードは，宣言（C03〜C07）のとおりに，データを関数へ渡す（中身の無い記号）。 -/
opaque CodePassesDataAsDeclared : Prop

/-- Efron らが用いた糖尿病データセットは，配布元の URL から取得したファイルである。
- 値が入った後に，その値に対して公理として宣言する -/
abbrev C10 (fetchedSha256 : String) : Prop := efronDatasetSha256 = fetchedSha256

/-- 実験コードは，仕様を満たす。
- 使ったものを，そのまま出力に記録する
- 計算した MSE を，そのまま出力に記録する
- 宣言（C03〜C07）のとおりに，データを関数へ渡す
- この実行に当てはめるには，訓練データの行とテストデータの行が，重ならず，合わせると全件になること（C25）が要る
- 値が入った後に，その値に対して公理として宣言する（任意の値に対して宣言すると，すべての値が等しいことになってしまう） -/
abbrev C11 (observedTrainIndex observedTestIndex : List ℕ) (observed : Used) (outputTestMse : ℚ) : Prop :=
  C25 observedTrainIndex observedTestIndex →
  observed = actualUsed ∧ (outputTestMse : ℝ) = actualTestMse ∧ CodePassesDataAsDeclared

/-- ライブラリは信用できる。
- 宣言したデータセット，関数，引数，版，計算環境を使い，宣言のとおりにデータを渡せば，ライブラリが計算する MSE は，宣言したとおりに計算した MSE である
- 関数の中身（何を計算するか）は主張しない -/
abbrev C12 : Prop := UsedAsDeclared actualUsed → CodePassesDataAsDeclared → actualTestMse = specifiedTestMse
axiom C12_axiom : C12

/-- C10（公理），C14，C15 から C16 を導く。 -/
theorem C16_of_C10_C14_C15 (observedDataSha256 fetchedSha256 : String) :
    C10 fetchedSha256 → C14 observedDataSha256 → C15 fetchedSha256 → C16 observedDataSha256 :=
  fun c10 c14 c15 => c14.trans (c15.symm.trans c10.symm)

/-- 公理（C11，C12）と C16〜C36 から C13 を導く。 -/
theorem C13_of_C11_C12_C16_to_C36 (observedTrainIndex observedTestIndex : List ℕ) (observed : Used)
    (outputTestMse : ℚ) :
    C11 observedTrainIndex observedTestIndex observed outputTestMse → C12 →
    C16 observed.dataSha256 → C17 observed.sampleCount → C18 observed.featureCount →
    C19 observed.featureColumns → C20 observed.targetColumn →
    C21 observed.loadFunction → C22 observed.loadArguments →
    C23 observed.splitFunction → C24 observed.splitArguments → C25 observedTrainIndex observedTestIndex →
    C26 observed.fitFunction → C27 observed.fitParameters → C28 observed.fitFeatureCount →
    C29 observed.predictFunction → C30 observed.mseFunction →
    C31 observed.scikitLearnVersion → C32 observed.numpyVersion → C33 observed.scipyVersion →
    C34 observed.pythonVersion → C35 observed.operatingSystem → C36 observed.cpuArchitecture →
    C13 outputTestMse := by
  intro c11 c12 c16 c17 c18 c19 c20 c21 c22 c23 c24 c25 c26 c27 c28 c29 c30 c31 c32 c33 c34 c35 c36
  obtain ⟨recorded, output, passes⟩ := c11 c25
  have used : UsedAsDeclared actualUsed := by
    rw [← recorded]
    exact ⟨c16, c17, c18, c19, c20, c21, c22, c23, c24, c26, c27, c28, c29, c30, c31, c32, c33,
      c34, c35, c36⟩
  exact output.trans (c12 used passes)

/-! ### HARKing をしていない -/

/-- 本番の run は，失敗したものも含めてすべて，判定に使う宣言と同じ宣言の commit で実行された。
- 宣言は，このファイル（Spec.lean）と，値の取り方（verification.json）
- 最初の本番の run より前に宣言があり，その後に宣言を書き換えていないことを示す -/
abbrev C37 (fullRunDeclarationSha256s : List String) (verifiedDeclarationSha256 : String) : Prop :=
  ∀ sha256 ∈ fullRunDeclarationSha256s, sha256 = verifiedDeclarationSha256

/-! ### チェリーピッキングをしていない -/

/-- 成功した本番の run が出力した MSE は，すべて，判定に使う MSE と一致する。 -/
abbrev C38 (fullRunTestMses : List ℚ) (outputTestMse : ℚ) : Prop := ∀ mse ∈ fullRunTestMses, mse = outputTestMse

/-! ## 出力された MSE の信頼性 -/

/-- 出力された MSE は，信頼性条件を満たす。
- 宣言どおりに実行された（C13），HARKing をしていない（C37），チェリーピッキングをしていない（C38） -/
abbrev C00 (outputTestMse : ℚ) (fullRunDeclarationSha256s : List String) (verifiedDeclarationSha256 : String)
    (fullRunTestMses : List ℚ) : Prop :=
  C13 outputTestMse ∧ C37 fullRunDeclarationSha256s verifiedDeclarationSha256 ∧ C38 fullRunTestMses outputTestMse

/-- C13，C37，C38 から C00 を導く。 -/
theorem C00_of_C13_C37_C38 (outputTestMse : ℚ) (fullRunDeclarationSha256s : List String)
    (verifiedDeclarationSha256 : String) (fullRunTestMses : List ℚ) :
    C13 outputTestMse → C37 fullRunDeclarationSha256s verifiedDeclarationSha256 →
    C38 fullRunTestMses outputTestMse →
    C00 outputTestMse fullRunDeclarationSha256s verifiedDeclarationSha256 fullRunTestMses :=
  fun c13 c37 c38 => ⟨c13, c37, c38⟩

end Spec
