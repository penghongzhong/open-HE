import FRegularizedFreeProductRule

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory Filter
open scoped Topology ENNReal
namespace HartreeF.Regularization.Actual
open EnergySpace EnergyRegularizer SobolevStretch StationarySelfTest
attribute [local irreducible] energySubmodule
local instance : SecondCountableTopologyEither ℝ EnergyState :=
  secondCountableTopologyEither_of_left ℝ EnergyState

def energyDuhamel (hDensity : OrdinaryH1Density) {K : ℝ} (hSob : OrdinarySobolev K)
    (a : ℝ) (v0 : EnergyState) (f : ℝ → EnergyState) (t : ℝ) : EnergyState :=
  freeEnergyState hDensity hSob (t-a) v0 + Complex.I •
    ∫ s in a..t, freeEnergyState hDensity hSob (t-s) (f s)

def interactionState (hDensity : OrdinaryH1Density) {K : ℝ} (hSob : OrdinarySobolev K)
    (a : ℝ) (v0 : EnergyState) (f : ℝ → EnergyState) (t : ℝ) : EnergyState :=
  freeEnergyState hDensity hSob (-a) v0 + Complex.I •
    ∫ s in a..t, freeEnergyState hDensity hSob (-s) (f s)

theorem interactionState_hasDerivAt (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) (a : ℝ) (v0 : EnergyState) (f : ℝ → EnergyState)
    (hf : Continuous f) (t : ℝ) :
    HasDerivAt (interactionState hDensity hSob a v0 f)
      (Complex.I • freeEnergyState hDensity hSob (-t) (f t)) t := by
  have hc := freeEnergyState_continuous_path hDensity hSob (fun s : ℝ => -s) f
    continuous_neg hf
  exact (intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable (μ := volume) a t)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt).const_smul Complex.I
    |>.const_add (freeEnergyState hDensity hSob (-a) v0)

theorem energyDuhamel_factor (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) (a : ℝ) (v0 : EnergyState) (f : ℝ → EnergyState)
    (hf : Continuous f) (t : ℝ) :
    energyDuhamel hDensity hSob a v0 f t =
      freeEnergyState hDensity hSob t (interactionState hDensity hSob a v0 f t) := by
  have hc := freeEnergyState_continuous_path hDensity hSob (fun s : ℝ => -s) f
    continuous_neg hf
  have hi := (freeEnergyCLM hDensity hSob t).intervalIntegral_comp_comm
    (hc.intervalIntegrable (μ := volume) a t)
  simp only [energyDuhamel, interactionState, freeEnergyState_add, freeEnergyState_smul]
  congr 1
  · rw [← freeEnergyState_add_time, sub_eq_add_neg]
  · congr 1
    change _ = freeEnergyCLM hDensity hSob t (∫ s in a..t,
      freeEnergyState hDensity hSob (-s) (f s))
    rw [← hi]
    apply intervalIntegral.integral_congr
    intro s _
    change freeEnergyState hDensity hSob (t-s) (f s) =
      freeEnergyState hDensity hSob t (freeEnergyState hDensity hSob (-s) (f s))
    rw [← freeEnergyState_add_time, sub_eq_add_neg]

/-- The single-time domain certificate comes from the actual mild value.
The source remains merely a continuous EnergyState path. -/
theorem energyDuhamel_hasDerivAt_of_J (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) (a : ℝ) (v0 : EnergyState) (f : ℝ → EnergyState)
    (hf : Continuous f) (n : ℕ) (u : EnergyState) (t : ℝ)
    (hval : energyDuhamel hDensity hSob a v0 f t = J hDensity hSob n u) :
    HasDerivAt (energyDuhamel hDensity hSob a v0 f)
      (Complex.I • deltaJ hDensity hSob n u + Complex.I • f t) t := by
  have hwval : interactionState hDensity hSob a v0 f t =
      J hDensity hSob n (freeEnergyState hDensity hSob (-t) u) := by
    calc
      _ = freeEnergyState hDensity hSob (-t)
          (freeEnergyState hDensity hSob t (interactionState hDensity hSob a v0 f t)) := by
        rw [← freeEnergyState_add_time, neg_add_cancel, freeEnergyState_zero_time]
      _ = freeEnergyState hDensity hSob (-t) (energyDuhamel hDensity hSob a v0 f t) :=
        congrArg (freeEnergyState hDensity hSob (-t))
          (energyDuhamel_factor hDensity hSob a v0 f hf t).symm
      _ = _ := by rw [hval, J_free]
  have h := free_product_hasDerivAt_of_J hDensity hSob n
    (freeEnergyState hDensity hSob (-t) u)
    (interactionState_hasDerivAt hDensity hSob a v0 f hf t) hwval
  have he : energyDuhamel hDensity hSob a v0 f =
      fun s => freeEnergyState hDensity hSob s (interactionState hDensity hSob a v0 f s) :=
    funext (energyDuhamel_factor hDensity hSob a v0 f hf)
  rw [he]
  simpa only [deltaJ_free, freeEnergyState_smul, freeEnergyState_inverse] using h

#print axioms energyDuhamel_hasDerivAt_of_J
end HartreeF.Regularization.Actual
