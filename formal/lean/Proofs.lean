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

/-- R06〜R31 から R05 を導く。 -/
theorem R05_of_R06_to_R31 (observedRepositoryCommit fetchedSha256 : String) (observedFetchedUrls : List String)
    (observedTrainIndex observedTestIndex : List ℕ)
    (observedFitInputSha256 loadedTrainRowsSha256 observedPredictInputSha256 loadedTestFeaturesSha256 : String)
    (observedMseTargetSha256 loadedTestTargetSha256 : String) (observed : Used) :
  R06 observedRepositoryCommit → R07 observed.dataSha256 → R08 observedFetchedUrls →
  R09 fetchedSha256 → R10 observed.dataSha256 → R11 observed.sampleCount →
  R12 observed.featureCount → R13 observed.featureColumns → R14 observed.targetColumn →
  R15 observed.loadFunction → R16 observed.loadArguments → R17 observed.splitFunction →
  R18 observed.splitArguments → R19 observedTrainIndex observedTestIndex → R20 observed.fitFunction →
  R21 observed.fitParameters → R22 observed.fitFeatureCount → R23 observedFitInputSha256 loadedTrainRowsSha256 →
  R24 observed.predictFunction → R25 observedPredictInputSha256 loadedTestFeaturesSha256 → R26 observed.mseFunction →
  R27 observedMseTargetSha256 loadedTestTargetSha256 → R28 observed.operatingSystem → R29 observed.cpuArchitecture →
  R30 observed.cpuCount → R31 observed.memoryGibibytes →
    R05 observedRepositoryCommit fetchedSha256 observedFetchedUrls observedTrainIndex observedTestIndex
      observedFitInputSha256 loadedTrainRowsSha256 observedPredictInputSha256 loadedTestFeaturesSha256
      observedMseTargetSha256 loadedTestTargetSha256 observed := by
  intro r06 r07 r08 r09 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 r28 r29 r30 r31 declaration
  cases declaration
  · exact And.intro C03_holds (And.intro r07 (And.intro r08 (And.intro r09 (And.intro r10 (And.intro r11 (And.intro r12 (And.intro r13 (r14))))))))
  · exact And.intro C04_holds (And.intro r15 (r16))
  · exact And.intro C05_holds (And.intro r17 (And.intro r18 (r19)))
  · exact And.intro C06_holds (And.intro r20 (And.intro r21 (And.intro r22 (r23))))
  · exact And.intro C07_holds (And.intro r24 (r25))
  · exact And.intro C08_holds (And.intro r26 (r27))
  · exact And.intro C09_holds (And.intro r28 (And.intro r29 (And.intro r30 (r31))))
  · exact And.intro C10_holds (r06)

axiom R04_axiom : R04

/-- R02（公理），R07，R09 から R10 を導く。 -/
theorem R10_of_R02_R07_R09 (observedDataSha256 fetchedSha256 : String) :
    R02 fetchedSha256 → R07 observedDataSha256 → R09 fetchedSha256 → R10 observedDataSha256 :=
  fun r02 r07 r09 => r07.trans (r09.symm.trans r02.symm)

/-- 公理（R03，R04）と R05 から，出力された MSE が，宣言したとおりに計算した MSE であることを導く。 -/
theorem outputTestMse_eq_specifiedTestMse (observedRepositoryCommit fetchedSha256 : String) (observedFetchedUrls : List String)
    (observedTrainIndex observedTestIndex : List ℕ)
    (observedFitInputSha256 loadedTrainRowsSha256 observedPredictInputSha256 loadedTestFeaturesSha256 : String)
    (observedMseTargetSha256 loadedTestTargetSha256 : String) (observed : Used) (outputTestMse : ℚ) :
    R03 observed outputTestMse → R04 →
    R05 observedRepositoryCommit fetchedSha256 observedFetchedUrls observedTrainIndex observedTestIndex
      observedFitInputSha256 loadedTrainRowsSha256 observedPredictInputSha256 loadedTestFeaturesSha256
      observedMseTargetSha256 loadedTestTargetSha256 observed →
    outputTestMse = specifiedTestMse := by
  intro r03 r04 r05
  obtain ⟨_, _, _, _, r10, r11, r12, r13, r14⟩ := r05 .dataset
  obtain ⟨_, r15, r16⟩ := r05 .load
  obtain ⟨_, r17, r18, _⟩ := r05 .split
  obtain ⟨_, r20, r21, r22, _⟩ := r05 .fit
  obtain ⟨_, r24, _⟩ := r05 .predict
  obtain ⟨_, r26, _⟩ := r05 .mse
  obtain ⟨_, r28, r29, r30, r31⟩ := r05 .environment
  obtain ⟨recorded, output, passes⟩ := r03
  have used : UsedAsDeclared actualUsed := by
    rw [← recorded]
    exact ⟨r10, r11, r12, r13, r14, r15, r16, r17, r18, r20, r21, r22, r24, r26, r28, r29, r30, r31⟩
  exact output.trans (r04 used passes)

/-- R02〜R05，R32，R33 から R01 を導く。 -/
theorem R01_of_R02_R03_R04_R05_R32_R33 (observedRepositoryCommit fetchedSha256 : String) (observedFetchedUrls : List String)
    (observedTrainIndex observedTestIndex : List ℕ)
    (observedFitInputSha256 loadedTrainRowsSha256 observedPredictInputSha256 loadedTestFeaturesSha256 : String)
    (observedMseTargetSha256 loadedTestTargetSha256 : String) (observed : Used) (outputTestMse : ℚ)
    (fullRunDeclarationSha256s : List String) (verifiedDeclarationSha256 : String) (fullRunTestMses : List ℚ) :
    R02 fetchedSha256 → R03 observed outputTestMse → R04 →
    R05 observedRepositoryCommit fetchedSha256 observedFetchedUrls observedTrainIndex observedTestIndex
      observedFitInputSha256 loadedTrainRowsSha256 observedPredictInputSha256 loadedTestFeaturesSha256
      observedMseTargetSha256 loadedTestTargetSha256 observed →
    R32 fullRunDeclarationSha256s verifiedDeclarationSha256 → R33 fullRunTestMses outputTestMse →
    R01 observedRepositoryCommit fetchedSha256 observedFetchedUrls observedTrainIndex observedTestIndex
      observedFitInputSha256 loadedTrainRowsSha256 observedPredictInputSha256 loadedTestFeaturesSha256
      observedMseTargetSha256 loadedTestTargetSha256 observed outputTestMse
      fullRunDeclarationSha256s verifiedDeclarationSha256 fullRunTestMses :=
  fun r02 r03 r04 r05 r32 r33 => ⟨r02, r03, r04, r05, r32, r33⟩

/-- C01，R01 から C00 を導く。 -/
theorem C00_of_C01_R01 (observedRepositoryCommit fetchedSha256 : String) (observedFetchedUrls : List String)
    (observedTrainIndex observedTestIndex : List ℕ)
    (observedFitInputSha256 loadedTrainRowsSha256 observedPredictInputSha256 loadedTestFeaturesSha256 : String)
    (observedMseTargetSha256 loadedTestTargetSha256 : String) (observed : Used) (outputTestMse : ℚ)
    (fullRunDeclarationSha256s : List String) (verifiedDeclarationSha256 : String) (fullRunTestMses : List ℚ) :
    C01 outputTestMse →
    R01 observedRepositoryCommit fetchedSha256 observedFetchedUrls observedTrainIndex observedTestIndex
      observedFitInputSha256 loadedTrainRowsSha256 observedPredictInputSha256 loadedTestFeaturesSha256
      observedMseTargetSha256 loadedTestTargetSha256 observed outputTestMse
      fullRunDeclarationSha256s verifiedDeclarationSha256 fullRunTestMses →
    C00 observedRepositoryCommit fetchedSha256 observedFetchedUrls observedTrainIndex observedTestIndex
      observedFitInputSha256 loadedTrainRowsSha256 observedPredictInputSha256 loadedTestFeaturesSha256
      observedMseTargetSha256 loadedTestTargetSha256 observed outputTestMse
      fullRunDeclarationSha256s verifiedDeclarationSha256 fullRunTestMses :=
  fun c01 r01 => ⟨c01, r01⟩

end Spec
