import Spec
import Proofs
import Values
open Spec Values
open Lean Elab Term in
elab "proved% " theoremName:ident : term => do
  let name ← realizeGlobalConstNoOverloadWithInfo theoremName
  if (← collectAxioms name).contains ``sorryAx then throwError "{name} は証明されていない"
  return mkConst name
/-! 各命題の判定。parse_claims.py が生成する。手で編集しない。 -/
axiom R02_axiom : R02 fetchedSha256
axiom R03_axiom : R03 observed outputTestMse
theorem R06_holds : R06 observedRepositoryCommit := by decide +kernel
theorem R07_holds : R07 observedDataSha256 := by decide +kernel
theorem R08_holds : R08 observedFetchedUrls := by decide +kernel
theorem R09_holds : R09 fetchedSha256 := by decide +kernel
theorem R11_holds : R11 observedSampleCount := by decide +kernel
theorem R12_holds : R12 observedFeatureCount := by decide +kernel
theorem R13_holds : R13 observedFeatureColumns := by decide +kernel
theorem R14_holds : R14 observedTargetColumn := by decide +kernel
theorem R15_holds : R15 observedLoadFunction := by decide +kernel
theorem R16_holds : R16 observedLoadArguments := by decide +kernel
theorem R17_holds : R17 observedSplitFunction := by decide +kernel
theorem R18_holds : R18 observedSplitArguments := by decide +kernel
theorem R19_holds : R19 observedTrainIndex observedTestIndex := by decide +kernel
theorem R20_holds : R20 observedFitFunction := by decide +kernel
theorem R21_holds : R21 observedFitParameters := by decide +kernel
theorem R22_holds : R22 observedFitFeatureCount := by decide +kernel
theorem R23_holds : R23 observedFitInputSha256 loadedTrainRowsSha256 := by decide +kernel
theorem R24_holds : R24 observedPredictFunction := by decide +kernel
theorem R25_holds : R25 observedPredictInputSha256 loadedTestFeaturesSha256 := by decide +kernel
theorem R26_holds : R26 observedMseFunction := by decide +kernel
theorem R27_holds : R27 observedMseTargetSha256 loadedTestTargetSha256 := by decide +kernel
theorem R28_holds : R28 observedOperatingSystem := by decide +kernel
theorem R29_holds : R29 observedCpuArchitecture := by decide +kernel
theorem R30_holds : R30 observedCpuCount := by decide +kernel
theorem R31_holds : R31 observedMemoryGibibytes := by decide +kernel
theorem R32_holds : R32 fullRunDeclarationSha256s verifiedDeclarationSha256 := by decide +kernel
theorem R33_holds : R33 fullRunTestMses outputTestMse := by decide +kernel
theorem R10_holds : R10 observedDataSha256 := R10_of_R02_R07_R09 _ _ R02_axiom R07_holds R09_holds
theorem R05_holds : R05 observedRepositoryCommit fetchedSha256 observedFetchedUrls observedTrainIndex observedTestIndex observedFitInputSha256 loadedTrainRowsSha256 observedPredictInputSha256 loadedTestFeaturesSha256 observedMseTargetSha256 loadedTestTargetSha256 observed := R05_of_R06_to_R31 _ _ _ _ _ _ _ _ _ _ _ _ R06_holds R07_holds R08_holds R09_holds R10_holds R11_holds R12_holds R13_holds R14_holds R15_holds R16_holds R17_holds R18_holds R19_holds R20_holds R21_holds R22_holds R23_holds R24_holds R25_holds R26_holds R27_holds R28_holds R29_holds R30_holds R31_holds
theorem C01_fails : ¬ (C01 outputTestMse) := not_C01_of_C02 _ C02_holds (by decide +kernel)
theorem R01_holds : R01 observedRepositoryCommit fetchedSha256 observedFetchedUrls observedTrainIndex observedTestIndex observedFitInputSha256 loadedTrainRowsSha256 observedPredictInputSha256 loadedTestFeaturesSha256 observedMseTargetSha256 loadedTestTargetSha256 observed outputTestMse fullRunDeclarationSha256s verifiedDeclarationSha256 fullRunTestMses := R01_of_R02_R03_R04_R05_R32_R33 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R02_axiom R03_axiom R04_axiom R05_holds R32_holds R33_holds
theorem C00_fails : ¬ (C00 observedRepositoryCommit fetchedSha256 observedFetchedUrls observedTrainIndex observedTestIndex observedFitInputSha256 loadedTrainRowsSha256 observedPredictInputSha256 loadedTestFeaturesSha256 observedMseTargetSha256 loadedTestTargetSha256 observed outputTestMse fullRunDeclarationSha256s verifiedDeclarationSha256 fullRunTestMses) := fun h => by first | exact (proved% C01_fails) h.1 | exact (proved% R01_fails) h.2
