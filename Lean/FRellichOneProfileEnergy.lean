import FLocalRellichAEExtraction
import FOneProfileEnergySplit

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1500000
open MeasureTheory Filter
open scoped ENNReal Topology RealInnerProductSpace
namespace HartreeF.LocalRellich
open EnergySpace SobolevStretch EnergyVariation StateEnergy ForcingDomain SharpOrdinary
attribute [local irreducible] energySubmodule

/-- A supplied genuine gradient-weak limit now yields a common subsequence
with actual a.e. convergence and one-profile Hartree energy splitting.
The a.e. hypothesis of the independently checked BL theorem is produced here.
This theorem does not extract the weak limit or a family of profiles. -/
theorem exists_energy_split_subsequence_of_gradient_weak
    (hRel : OrdinaryRellichBall) {K : ℝ} (hSob : OrdinarySobolev K)
    {alpha B : ℝ} (hH : SharpOrdinaryHLS alpha)
    (hOrd : OrdinaryHLS alpha (HeatRiesz.standardRieszConstant alpha))
    {u : ℕ → EnergyState} (f : EnergyState) (hB : ∀ n, ‖u n‖ ≤ B)
    (hweak : ∀ j : Fin 3, ∀ v : L2,
      Tendsto (fun n => inner ℝ (energyGradient j (u n)) v) atTop
        (𝓝 (inner ℝ (energyGradient j f) v))) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧
      (∀ᵐ x ∂volume, Tendsto (fun n => energyValue (u (σ n)) x) atTop (𝓝 (energyValue f x))) ∧
      (∀ j : Fin 3, ∀ v : L2,
        Tendsto (fun n => inner ℝ (energyGradient j (u (σ n))) v) atTop
          (𝓝 (inner ℝ (energyGradient j f) v))) ∧
      Tendsto (fun n => totalEnergy alpha (u (σ n))-
        totalEnergy alpha (u (σ n)-f)-totalEnergy alpha f) atTop (𝓝 0) := by
  obtain ⟨σ,hσ,hae⟩ := exists_ae_subsequence_of_gradient_weak hRel hSob hB hweak
  have hw (j : Fin 3) (v : L2) :
      Tendsto (fun n => inner ℝ (energyGradient j (u (σ n))) v) atTop
        (𝓝 (inner ℝ (energyGradient j f) v)) := (hweak j v).comp hσ.tendsto_atTop
  refine ⟨σ,hσ,hae,hw,?_⟩
  exact NonlocalBL.totalEnergy_split_one_profile hH hOrd f
    (fun n => (energyState_value_norm_le _).trans (hB (σ n))) hae hw

#print axioms exists_energy_split_subsequence_of_gradient_weak
end HartreeF.LocalRellich
