import FLinearProfileFrame
import FBoundedEnergyContinuity
import FIndependentDivergentFreeFrames

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000
open MeasureTheory Filter
open scoped ENNReal Topology RealInnerProductSpace
namespace HartreeF.ProfileEnergy
open EnergySpace SobolevStretch StationarySelfTest ActualStrichartz CriticalAffine
open EnergyVariation StateEnergy ForcingDomain SharpOrdinary FreeFrameIndependentReview
attribute [local irreducible] energySubmodule

/-- Source-order atoms have a uniform graph bound derived from their preserved
pure-gradient norm, independent of all scale, translation and time parameters. -/
theorem linearProfileFrame_norm_bound (hDensity : OrdinaryH1Density) {K : ℝ} (hSob : OrdinarySobolev K)
    (lambda : ℝ) (hlambda : 0 < lambda) (y : Space) (s : ℝ) (phi : EnergyState) :
    ‖linearProfileFrame hDensity hSob lambda hlambda y s phi‖ ≤
      max (K^((6:ℝ)⁻¹)) 1*pureGradientNorm phi := by
  have h := energyState_le_pureGradient hSob (linearProfileFrame hDensity hSob lambda hlambda y s phi)
  rwa [linearProfileFrame_pureGradientNorm] at h

/-- Genuine Hartree energy splitting for a divergent-time atom. Interaction
decay and the full-frame kinetic cross term are proved separately. -/
theorem divergent_profile_energy_split (hDensity : OrdinaryH1Density)
    {K C alpha B : ℝ} (hSob : OrdinarySobolev K) (hS : OrdinaryHomogeneousStrichartz C)
    (hH : SharpOrdinaryHLS alpha)
    (hOrd : OrdinaryHLS alpha (HeatRiesz.standardRieszConstant alpha))
    (lambda : ℕ → ℝ) (hlambda : ∀ n, 0 < lambda n) (y : ℕ → Space) (s : ℕ → ℝ)
    {u : ℕ → EnergyState} (phi : EnergyState) (hB : ∀ n, ‖u n‖ ≤ B)
    (hw : GradientWeakLimit
      (fun n => (linearProfileFrame hDensity hSob (lambda n) (hlambda n) (y n) (s n)).symm (u n)) phi)
    (hs : Tendsto s atTop atTop ∨ Tendsto s atTop atBot) :
    Tendsto (fun n => totalEnergy alpha (u n)-totalEnergy alpha
      (u n-linearProfileFrame hDensity hSob (lambda n) (hlambda n) (y n) (s n) phi)-
      totalEnergy alpha (linearProfileFrame hDensity hSob (lambda n) (hlambda n) (y n) (s n) phi))
      atTop (𝓝 0) := by
  let b (n : ℕ) := linearProfileFrame hDensity hSob (lambda n) (hlambda n) (y n) (s n) phi
  let D := max (K^((6:ℝ)⁻¹)) 1*pureGradientNorm phi
  have hD : 0 ≤ D := mul_nonneg (le_trans zero_le_one (le_max_right _ _)) (pureGradientNorm_nonneg phi)
  have hb (n : ℕ) : ‖b n‖ ≤ D := linearProfileFrame_norm_bound hDensity hSob _ _ _ _ phi
  have hv (n : ℕ) : ‖energyValue (u n-b n)‖ ≤ B+D :=
    (energyState_value_norm_le _).trans ((norm_sub_le _ _).trans (add_le_add (hB n) (hb n)))
  have hu (n : ℕ) : ‖energyValue (u n)‖ ≤ B+D :=
    ((energyState_value_norm_le _).trans (hB n)).trans (le_add_of_nonneg_right hD)
  have htail := divergent_free_spatial_frame_tails hDensity hSob hS hOrd phi s lambda hlambda y hs
  have hl6 : Tendsto (fun n => ‖energyValue (b n)‖) atTop (𝓝 0) := htail.2.1
  have hbi : Tendsto (fun n => interactionLp alpha (energyValue (b n))) atTop (𝓝 0) := htail.2.2.1
  have hdiff : Tendsto (fun n => ‖energyValue (u n)-energyValue (u n-b n)‖) atTop (𝓝 0) := by
    have he (n) : energyValue (u n)-energyValue (u n-b n)=energyValue (b n) := by
      rw [map_sub]
      abel
    simpa only [he] using hl6
  have hi := (interactionLp_difference_tendsto_zero hH hOrd hu hv hdiff).sub hbi
  have hk := linearProfileFrame_kinetic_split hDensity hSob lambda hlambda y s phi hw
  have ht := (hk.div_const 2).sub (hi.div_const (2*(3+alpha)))
  simp only [sub_self, zero_div] at ht
  change Tendsto (fun n => totalEnergy alpha (u n)-totalEnergy alpha (u n-b n)-totalEnergy alpha (b n))
    atTop (𝓝 0)
  convert ht using 1
  funext n
  have hbk : gradientSquared (b n)=gradientSquared phi :=
    linearProfileFrame_gradientSquared hDensity hSob _ _ _ _ phi
  simp only [totalEnergy, hbk]
  ring

#print axioms linearProfileFrame_norm_bound
#print axioms divergent_profile_energy_split
end HartreeF.ProfileEnergy
