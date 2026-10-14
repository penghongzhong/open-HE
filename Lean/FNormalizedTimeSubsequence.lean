import FFiniteTimeProfileEnergySplit
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Sequences

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000
open MeasureTheory Filter
open scoped ENNReal Topology RealInnerProductSpace
namespace HartreeF.ProfileEnergy
open EnergySpace SobolevStretch StationarySelfTest ActualStrichartz
open StateEnergy ForcingDomain SharpOrdinary LocalRellich
attribute [local irreducible] energySubmodule

/-- Native compactification of an arbitrary real time sequence. No normalized
finite-time or divergent-time clause is added to the ordinary profile oracle. -/
theorem exists_normalized_time_subsequence (s : ℕ → ℝ) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧
      ((∃ t : ℝ, Tendsto (s ∘ σ) atTop (𝓝 t)) ∨
        Tendsto (s ∘ σ) atTop atTop ∨ Tendsto (s ∘ σ) atTop atBot) := by
  obtain ⟨t,σ,hσ,ht⟩ := CompactSpace.tendsto_subseq (fun n => (s n : EReal))
  refine ⟨σ,hσ,?_⟩
  induction t using EReal.rec with
  | bot => exact Or.inr (Or.inr (EReal.tendsto_coe_nhds_bot_iff.mp ht))
  | coe t => exact Or.inl ⟨t,EReal.tendsto_coe.mp ht⟩
  | top => exact Or.inr (Or.inl (EReal.tendsto_coe_nhds_top_iff.mp ht))

/-- The first unconditional-in-time native Hartree profile consumer. The source
full-frame weak limit and a pure-gradient bound suffice; a time branch is selected
natively and no original scalar L2 or a.e. hypothesis is required. -/
theorem profile_energy_split_subsequence (hDensity : OrdinaryH1Density)
    (hRel : OrdinaryRellichBall) {K C alpha B : ℝ} (hSob : OrdinarySobolev K)
    (hS : OrdinaryHomogeneousStrichartz C) (hH : SharpOrdinaryHLS alpha)
    (hOrd : OrdinaryHLS alpha (HeatRiesz.standardRieszConstant alpha))
    (lambda : ℕ → ℝ) (hlambda : ∀ n, 0 < lambda n) (y : ℕ → Space) (s : ℕ → ℝ)
    {u : ℕ → EnergyState} (phi : EnergyState) (hB : ∀ n, pureGradientNorm (u n) ≤ B)
    (hw : GradientWeakLimit
      (fun n => (linearProfileFrame hDensity hSob (lambda n) (hlambda n) (y n) (s n)).symm (u n)) phi) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧
      Tendsto (fun n => totalEnergy alpha (u (σ n))-totalEnergy alpha
        (u (σ n)-linearProfileFrame hDensity hSob (lambda (σ n)) (hlambda (σ n)) (y (σ n)) (s (σ n)) phi)-
        totalEnergy alpha (linearProfileFrame hDensity hSob (lambda (σ n)) (hlambda (σ n)) (y (σ n)) (s (σ n)) phi))
        atTop (𝓝 0) := by
  obtain ⟨τ,hτ,ht⟩ := exists_normalized_time_subsequence s
  have hb (n : ℕ) : ‖u (τ n)‖ ≤ max (K^((6:ℝ)⁻¹)) 1*B :=
    (energyState_le_pureGradient hSob _).trans
      (mul_le_mul_of_nonneg_left (hB (τ n)) (le_trans zero_le_one (le_max_right _ _)))
  have hwt : GradientWeakLimit
      (fun n => (linearProfileFrame hDensity hSob (lambda (τ n)) (hlambda (τ n)) (y (τ n)) (s (τ n))).symm (u (τ n))) phi :=
    fun j v => (hw j v).comp hτ.tendsto_atTop
  rcases ht with ⟨t,ht⟩ | ht
  · obtain ⟨η,hη,he⟩ := finite_time_profile_energy_split hDensity hRel hSob hH hOrd
      (lambda ∘ τ) (fun n => hlambda (τ n)) (y ∘ τ) (s ∘ τ) phi hb hwt ht
    exact ⟨τ ∘ η,hτ.comp hη,he⟩
  · exact ⟨τ,hτ,divergent_profile_energy_split hDensity hSob hS hH hOrd
      (lambda ∘ τ) (fun n => hlambda (τ n)) (y ∘ τ) (s ∘ τ) phi hb hwt ht⟩

#print axioms exists_normalized_time_subsequence
#print axioms profile_energy_split_subsequence
end HartreeF.ProfileEnergy
