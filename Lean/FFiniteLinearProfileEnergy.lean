import FNormalizedTimeSubsequence
import FOrdinaryLinearProfileInterface

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000
open MeasureTheory Filter
open scoped ENNReal Topology RealInnerProductSpace
namespace HartreeF.ProfileEnergy
open EnergySpace SobolevStretch StationarySelfTest ActualStrichartz
open StateEnergy ForcingDomain SharpOrdinary LocalRellich FramedEnergyIndependentReview
attribute [local irreducible] energySubmodule

/-- Finitely many arbitrary normalized-time stages admit one common energy
subsequence. Each induction step composes the actual previous subsequence. -/
theorem finite_profile_stage_subsequence (hDensity : OrdinaryH1Density)
    (hRel : OrdinaryRellichBall) {K C alpha : ℝ} (hSob : OrdinarySobolev K)
    (hS : OrdinaryHomogeneousStrichartz C) (hH : SharpOrdinaryHLS alpha)
    (hOrd : OrdinaryHLS alpha (HeatRiesz.standardRieszConstant alpha))
    (B : ℕ → ℝ) (lambda : ℕ → ℕ → ℝ) (hlambda : ∀ j n, 0<lambda j n)
    (y : ℕ → ℕ → Space) (s : ℕ → ℕ → ℝ) (phi : ℕ → EnergyState)
    (u : ℕ → ℕ → EnergyState) (J : ℕ)
    (hstep : ∀ j, j<J → ∀ n, u (j+1) n=u j n-
      linearProfileFrame hDensity hSob (lambda j n) (hlambda j n) (y j n) (s j n) (phi j))
    (hB : ∀ j, j<J → ∀ n, pureGradientNorm (u j n)≤B j)
    (hw : ∀ j, j<J → GradientWeakLimit (fun n =>
      (linearProfileFrame hDensity hSob (lambda j n) (hlambda j n) (y j n) (s j n)).symm (u j n)) (phi j)) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∀ j, j<J →
      Tendsto (fun n => totalEnergy alpha (u j (σ n))-totalEnergy alpha (u (j+1) (σ n))-
        totalEnergy alpha (linearProfileFrame hDensity hSob (lambda j (σ n)) (hlambda j (σ n))
          (y j (σ n)) (s j (σ n)) (phi j))) atTop (𝓝 0) := by
  induction J with
  | zero => exact ⟨id,strictMono_id,fun _ h => (Nat.not_lt_zero _ h).elim⟩
  | succ J ih =>
    obtain ⟨σ,hσ,he⟩ := ih (fun j hj => hstep j (Nat.lt_succ_of_lt hj))
      (fun j hj => hB j (Nat.lt_succ_of_lt hj)) (fun j hj => hw j (Nat.lt_succ_of_lt hj))
    have hwt : GradientWeakLimit (fun n =>
        (linearProfileFrame hDensity hSob (lambda J (σ n)) (hlambda J (σ n))
          (y J (σ n)) (s J (σ n))).symm (u J (σ n))) (phi J) :=
      fun k v => (hw J (Nat.lt_succ_self J) k v).comp hσ.tendsto_atTop
    obtain ⟨τ,hτ,ht⟩ := profile_energy_split_subsequence hDensity hRel hSob hS hH hOrd
      (lambda J ∘ σ) (fun n => hlambda J (σ n)) (y J ∘ σ) (s J ∘ σ) (phi J)
      (fun n => hB J (Nat.lt_succ_self J) (σ n)) hwt
    refine ⟨σ ∘ τ,hσ.comp hτ,?_⟩
    intro j hj
    rcases lt_or_eq_of_le (Nat.le_of_lt_succ hj) with hj | rfl
    · exact (he j hj).comp hτ.tendsto_atTop
    · simpa only [Function.comp_apply, hstep j (Nat.lt_succ_self j)] using ht

/-- The actual finite mixed-time energy telescope. Atom energies remain at
actual varying normalized times; a finite nonzero limit is not silently reset. -/
theorem finite_profile_energy_subsequence (hDensity : OrdinaryH1Density)
    (hRel : OrdinaryRellichBall) {K C alpha : ℝ} (hSob : OrdinarySobolev K)
    (hS : OrdinaryHomogeneousStrichartz C) (hH : SharpOrdinaryHLS alpha)
    (hOrd : OrdinaryHLS alpha (HeatRiesz.standardRieszConstant alpha))
    (B : ℕ → ℝ) (lambda : ℕ → ℕ → ℝ) (hlambda : ∀ j n, 0<lambda j n)
    (y : ℕ → ℕ → Space) (s : ℕ → ℕ → ℝ) (phi : ℕ → EnergyState)
    (u : ℕ → ℕ → EnergyState) (J : ℕ)
    (hstep : ∀ j, j<J → ∀ n, u (j+1) n=u j n-
      linearProfileFrame hDensity hSob (lambda j n) (hlambda j n) (y j n) (s j n) (phi j))
    (hB : ∀ j, j<J → ∀ n, pureGradientNorm (u j n)≤B j)
    (hw : ∀ j, j<J → GradientWeakLimit (fun n =>
      (linearProfileFrame hDensity hSob (lambda j n) (hlambda j n) (y j n) (s j n)).symm (u j n)) (phi j)) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧
      Tendsto (fun n => totalEnergy alpha (u 0 (σ n))-totalEnergy alpha (u J (σ n))-
        ∑ j ∈ Finset.range J, totalEnergy alpha (linearProfileFrame hDensity hSob
          (lambda j (σ n)) (hlambda j (σ n)) (y j (σ n)) (s j (σ n)) (phi j))) atTop (𝓝 0) := by
  obtain ⟨σ,hσ,he⟩ := finite_profile_stage_subsequence hDensity hRel hSob hS hH hOrd
    B lambda hlambda y s phi u J hstep hB hw
  refine ⟨σ,hσ,?_⟩
  have ht := tendsto_finsetSum (Finset.range J) (fun j hj => he j (Finset.mem_range.mp hj))
  simpa only [finite_energy_defect_identity, Finset.sum_const_zero] using ht

/-- Ordinary linear extraction plus the native Hartree argument. For each fixed
active depth a further common subsequence yields the actual energy split. This
is not a uniform-in-depth diagonal statement or a nonlinear profile theorem. -/
theorem ordinary_linear_profiles_with_finite_energy (hDensity : OrdinaryH1Density)
    (hRel : OrdinaryRellichBall) {K C alpha : ℝ} (hSob : OrdinarySobolev K)
    (hS : OrdinaryHomogeneousStrichartz C) (hH : SharpOrdinaryHLS alpha)
    (hOrd : OrdinaryHLS alpha (HeatRiesz.standardRieszConstant alpha))
    (hLP : OrdinaryLinearProfileExtraction hDensity hSob)
    (u : ℕ → EnergyState) (B : ℝ) (hB : ∀ n, pureGradientNorm (u n)≤B) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∃ P : LinearProfileFamily,
      LinearProfileProperties hDensity hSob (u ∘ σ) P ∧
      ∀ J : ℕ, (J : WithTop ℕ)≤P.count → ∃ τ : ℕ → ℕ, StrictMono τ ∧
        Tendsto (fun n => totalEnergy alpha (u (σ (τ n)))-
          totalEnergy alpha (profileRemainder hDensity hSob P (u ∘ σ) J (τ n))-
          ∑ j ∈ Finset.range J, totalEnergy alpha (profileAtom hDensity hSob P j (τ n))) atTop (𝓝 0) := by
  obtain ⟨σ,hσ,P,hP⟩ := hLP.extract u B hB
  refine ⟨σ,hσ,P,hP,?_⟩
  intro J hJ
  have hw (j : ℕ) (hj : j<J) : GradientWeakLimit (fun n =>
      (linearProfileFrame hDensity hSob (P.scale j n) (P.scale_pos j n) (P.center j n) (P.time j n)).symm
        (profileRemainder hDensity hSob P (u ∘ σ) j n)) (P.profile j) := by
    apply profileRemainder_stage_weak
    apply hP.weak_remainder (j+1) j (Nat.lt_succ_self j)
    exact le_trans (by exact_mod_cast Nat.succ_le_of_lt hj) hJ
  obtain ⟨τ,hτ,he⟩ := finite_profile_energy_subsequence hDensity hRel hSob hS hH hOrd
    (fun j => B+∑ k ∈ Finset.range j, pureGradientNorm (P.profile k))
    P.scale P.scale_pos P.center P.time P.profile
    (profileRemainder hDensity hSob P (u ∘ σ)) J
    (fun j _ n => profileRemainder_succ hDensity hSob P (u ∘ σ) j n)
    (fun j _ n => profileRemainder_pureGradient_bound hDensity hSob P (u ∘ σ) (fun n => hB (σ n)) j n) hw
  refine ⟨τ,hτ,?_⟩
  simpa only [profileRemainder_zero, Function.comp_apply, profileAtom] using he

#print axioms finite_profile_stage_subsequence
#print axioms finite_profile_energy_subsequence
#print axioms ordinary_linear_profiles_with_finite_energy
end HartreeF.ProfileEnergy
