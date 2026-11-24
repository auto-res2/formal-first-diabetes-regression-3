import Spec
/-! 証明に必要なもの（宣言が成り立つことの証明，claims を導く定理，値を含まない公理の宣言）。claims の形式化（claims.json）とは別に置く。 -/

namespace Spec

theorem C03_holds : C03 := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem C04_holds : C04 := ⟨rfl, rfl, rfl, rfl⟩

theorem C05_holds : C05 := ⟨rfl, rfl, rfl, rfl⟩

theorem C06_holds : C06 := ⟨rfl, rfl, rfl⟩

theorem C07_holds : C07 := ⟨rfl, rfl⟩

theorem C08_holds : C08 := ⟨rfl, rfl⟩

theorem C09_holds : C09 := ⟨rfl, rfl, rfl, rfl⟩

theorem C10_holds : C10 := rfl

theorem C02_holds : C02 :=
  ⟨C03_holds, C04_holds, C05_holds, C06_holds, C07_holds, C08_holds, C09_holds, C10_holds, _, rfl⟩

/-- C02 と，出力された MSE が 3400 を下回ることから，C01 を導く。 -/
theorem C01_of_C02 (outputTestMse : ℚ) :
    C02 → outputTestMse < 3400 → C01 outputTestMse :=
  fun _ below => below

/-- C02 と，出力された MSE が 3400 を下回らないことから，C01 の否定を導く。 -/
theorem not_C01_of_C02 (outputTestMse : ℚ) :
    C02 → ¬ outputTestMse < 3400 → ¬ C01 outputTestMse :=
  fun _ notBelow => notBelow

/-- R06〜R30 から R05 を導く。 -/
theorem R05_of_R06_to_R30 (observedRepositoryCommit fetchedSha256 : String) (observedTrainIndex observedTestIndex : List ℕ)
    (observedFitInputSha256 loadedTrainRowsSha256 observedPredictInputSha256 loadedTestFeaturesSha256 : String)
    (observedMseTargetSha256 loadedTestTargetSha256 : String) (observed : Used) :
  R06 observedRepositoryCommit → R07 observed.dataSha256 → R08 fetchedSha256 →
  R09 observed.dataSha256 → R10 observed.sampleCount → R11 observed.featureCount →
  R12 observed.featureColumns → R13 observed.targetColumn → R14 observed.loadFunction →
  R15 observed.loadArguments → R16 observed.splitFunction → R17 observed.splitArguments →
  R18 observedTrainIndex observedTestIndex → R19 observed.fitFunction → R20 observed.fitParameters →
  R21 observed.fitFeatureCount → R22 observedFitInputSha256 loadedTrainRowsSha256 → R23 observed.predictFunction →
  R24 observedPredictInputSha256 loadedTestFeaturesSha256 → R25 observed.mseFunction → R26 observedMseTargetSha256 loadedTestTargetSha256 →
  R27 observed.operatingSystem → R28 observed.cpuArchitecture → R29 observed.cpuCount →
  R30 observed.memoryGibibytes →
    R05 observedRepositoryCommit fetchedSha256 observedTrainIndex observedTestIndex observedFitInputSha256 loadedTrainRowsSha256
      observedPredictInputSha256 loadedTestFeaturesSha256 observedMseTargetSha256 loadedTestTargetSha256 observed :=
  fun r06 r07 r08 r09 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 r28 r29 r30 =>
    ⟨r06, r07, r08, r09, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30⟩

axiom R04_axiom : R04

/-- R02（公理），R07，R08 から R09 を導く。 -/
theorem R09_of_R02_R07_R08 (observedDataSha256 fetchedSha256 : String) :
    R02 fetchedSha256 → R07 observedDataSha256 → R08 fetchedSha256 → R09 observedDataSha256 :=
  fun r02 r07 r08 => r07.trans (r08.symm.trans r02.symm)

/-- 公理（R03，R04）と R05 から，出力された MSE が，宣言したとおりに計算した MSE であることを導く。 -/
theorem outputTestMse_eq_specifiedTestMse (observedRepositoryCommit fetchedSha256 : String) (observedTrainIndex observedTestIndex : List ℕ)
    (observedFitInputSha256 loadedTrainRowsSha256 observedPredictInputSha256 loadedTestFeaturesSha256 : String)
    (observedMseTargetSha256 loadedTestTargetSha256 : String) (observed : Used) (outputTestMse : ℚ) :
    R03 observed outputTestMse → R04 →
    R05 observedRepositoryCommit fetchedSha256 observedTrainIndex observedTestIndex observedFitInputSha256 loadedTrainRowsSha256
      observedPredictInputSha256 loadedTestFeaturesSha256 observedMseTargetSha256 loadedTestTargetSha256 observed →
    outputTestMse = specifiedTestMse := by
  intro r03 r04 r05
  obtain ⟨_, _, _, r09, r10, r11, r12, r13, r14, r15, r16, r17, _, r19, r20, r21, _, r23, _, r25, _, r27, r28, r29, r30⟩ := r05
  obtain ⟨recorded, output, passes⟩ := r03
  have used : UsedAsDeclared actualUsed := by
    rw [← recorded]
    exact ⟨r09, r10, r11, r12, r13, r14, r15, r16, r17, r19, r20, r21, r23, r25, r27, r28, r29, r30⟩
  exact output.trans (r04 used passes)

/-- R02〜R05，R31，R32 から R01 を導く。 -/
theorem R01_of_R02_R03_R04_R05_R31_R32 (observedRepositoryCommit fetchedSha256 : String) (observedTrainIndex observedTestIndex : List ℕ)
    (observedFitInputSha256 loadedTrainRowsSha256 observedPredictInputSha256 loadedTestFeaturesSha256 : String)
    (observedMseTargetSha256 loadedTestTargetSha256 : String) (observed : Used) (outputTestMse : ℚ)
    (fullRunDeclarationSha256s : List String) (verifiedDeclarationSha256 : String) (fullRunTestMses : List ℚ) :
    R02 fetchedSha256 → R03 observed outputTestMse → R04 →
    R05 observedRepositoryCommit fetchedSha256 observedTrainIndex observedTestIndex observedFitInputSha256 loadedTrainRowsSha256
      observedPredictInputSha256 loadedTestFeaturesSha256 observedMseTargetSha256 loadedTestTargetSha256 observed →
    R31 fullRunDeclarationSha256s verifiedDeclarationSha256 → R32 fullRunTestMses outputTestMse →
    R01 observedRepositoryCommit fetchedSha256 observedTrainIndex observedTestIndex observedFitInputSha256 loadedTrainRowsSha256
      observedPredictInputSha256 loadedTestFeaturesSha256 observedMseTargetSha256 loadedTestTargetSha256 observed outputTestMse
      fullRunDeclarationSha256s verifiedDeclarationSha256 fullRunTestMses :=
  fun r02 r03 r04 r05 r31 r32 => ⟨r02, r03, r04, r05, r31, r32⟩

/-- C01，R01 から C00 を導く。 -/
theorem C00_of_C01_R01 (observedRepositoryCommit fetchedSha256 : String) (observedTrainIndex observedTestIndex : List ℕ)
    (observedFitInputSha256 loadedTrainRowsSha256 observedPredictInputSha256 loadedTestFeaturesSha256 : String)
    (observedMseTargetSha256 loadedTestTargetSha256 : String) (observed : Used) (outputTestMse : ℚ)
    (fullRunDeclarationSha256s : List String) (verifiedDeclarationSha256 : String) (fullRunTestMses : List ℚ) :
    C01 outputTestMse →
    R01 observedRepositoryCommit fetchedSha256 observedTrainIndex observedTestIndex observedFitInputSha256 loadedTrainRowsSha256
      observedPredictInputSha256 loadedTestFeaturesSha256 observedMseTargetSha256 loadedTestTargetSha256 observed outputTestMse
      fullRunDeclarationSha256s verifiedDeclarationSha256 fullRunTestMses →
    C00 observedRepositoryCommit fetchedSha256 observedTrainIndex observedTestIndex observedFitInputSha256 loadedTrainRowsSha256
      observedPredictInputSha256 loadedTestFeaturesSha256 observedMseTargetSha256 loadedTestTargetSha256 observed outputTestMse
      fullRunDeclarationSha256s verifiedDeclarationSha256 fullRunTestMses :=
  fun c01 r01 => ⟨c01, r01⟩

end Spec
