import FCommonCountableProfileTimes
import FIndependentLinearProfileReindex

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000
open Filter
open scoped Topology

namespace HartreeF.CommonProfileTimes
open ProfileEnergy EnergySpace SobolevStretch StationarySelfTest
open LinearProfileIndependentReview

/-- The actual accepted family admits one time-normalizing subsequence. -/
theorem exists_common_profile_time_regimes (P : LinearProfileFamily) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧
      ∀ j : ℕ, TimeRegime ((reindexFamily P σ).time j) :=
  exists_common_time_regimes P.time

/-- The same subsequence normalizes every label and preserves all four original
linear-profile fields. The literal accepted reindexing keeps profiles and active
count fixed and composes scales, centers and times with that one subsequence. -/
theorem exists_common_profile_time_normalization (hDensity : OrdinaryH1Density)
    {K : ℝ} (hSob : OrdinarySobolev K) {u : ℕ → EnergyState}
    {P : LinearProfileFamily} (hP : LinearProfileProperties hDensity hSob u P) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧
      LinearProfileProperties hDensity hSob (u ∘ σ) (reindexFamily P σ) ∧
      ∀ j : ℕ, TimeRegime ((reindexFamily P σ).time j) := by
  obtain ⟨σ, hσ, ht⟩ := exists_common_profile_time_regimes P
  exact ⟨σ, hσ, linearProfileProperties_reindex hDensity hSob hP hσ, ht⟩

/-- Extraction followed by common time normalization. Ordinary linear extraction
remains an explicit premise, with only the original pure-gradient bound. This is
neither a nonlinear superposition theorem nor a scattering theorem. -/
theorem ordinary_extraction_common_time_normalization (hDensity : OrdinaryH1Density)
    {K : ℝ} (hSob : OrdinarySobolev K)
    (hExtract : OrdinaryLinearProfileExtraction hDensity hSob)
    (u : ℕ → EnergyState) (B : ℝ) (hB : ∀ n, pureGradientNorm (u n) ≤ B) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∃ P : LinearProfileFamily,
      LinearProfileProperties hDensity hSob (u ∘ σ) P ∧
      ∀ j : ℕ, TimeRegime (P.time j) := by
  obtain ⟨τ, hτ, P, hP⟩ := hExtract.extract u B hB
  obtain ⟨σ, hσ, hQ, ht⟩ := exists_common_profile_time_normalization hDensity hSob hP
  exact ⟨τ ∘ σ, hτ.comp hσ, reindexFamily P σ, hQ, ht⟩

end HartreeF.CommonProfileTimes
