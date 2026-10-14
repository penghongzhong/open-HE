import FOrdinaryHomogeneousStrichartz

noncomputable section
set_option autoImplicit false
set_option warningAsError true
open MeasureTheory Filter
open scoped ENNReal Topology
namespace HartreeF.FreeTimeDecay
open EnergySpace SobolevStretch StationarySelfTest ActualStrichartz CriticalTimeSobolev TimeHolder
attribute [local irreducible] energySubmodule
attribute [local instance 101] secondCountableTopologyEither_of_left

/-- Actual global S membership and its scalar norm on canonical value representatives.
Only the previously retained numerical homogeneous Strichartz premise is used. -/
theorem freeEnergyState_global_value_ten (hDensity : OrdinaryH1Density)
    {K C : ℝ} (hSob : OrdinarySobolev K) (hS : OrdinaryHomogeneousStrichartz C)
    (u : EnergyState) :
    (∀ᵐ t ∂(volume : Measure ℝ), MemLp (energyValue (freeEnergyState hDensity hSob t u)) 10 volume) ∧
    MemLp (fun t : ℝ => (eLpNorm (energyValue (freeEnergyState hDensity hSob t u)) 10 volume).toReal)
      10 volume := by
  let g : ℝ → EnergyState := fun t => freeEnergyState hDensity hSob t u
  have hg : AEStronglyMeasurable g volume :=
    (freeEnergyState_time_continuous hDensity hSob u).stronglyMeasurable.aestronglyMeasurable
  have hfin (L : ℂ →L[ℝ] ℝ) (hL : ∀ z, ‖L z‖≤‖z‖) :
      mixedNorm volume volume 10 (ENNReal.ofReal (30/13:ℝ))
        (fun t => energyProjectedGradient L (g t)) ≠ ∞ :=
    freeEnergyState_projected_finite hDensity hSob hS u L hL
  have hmem (L : ℂ →L[ℝ] ℝ) (hL : ∀ z, ‖L z‖≤‖z‖) :
      ∀ᵐ t ∂(volume : Measure ℝ), MemLp (energyProjectedGradient L (g t))
        (ENNReal.ofReal (30/13:ℝ)) volume :=
    finite_mixedNorm_ae_slice_memLp volume volume 10 _ (by norm_num) (by norm_num) _ (hfin L hL)
  have hre : ∀ z : ℂ, ‖Complex.reCLM z‖≤‖z‖ := fun z => Complex.abs_re_le_norm z
  have him : ∀ z : ℂ, ‖Complex.imCLM z‖≤‖z‖ := fun z => Complex.abs_im_le_norm z
  have hout := energyJointFields_critical_finite_and_bound hDensity hSob volume g hg
    (hmem Complex.reCLM hre) (hmem Complex.imCLM him) (hfin Complex.reCLM hre) (hfin Complex.imCLM him)
  let r := energyJointFields volume g hg
  have hr : MemLp (fun t => eLpNorm (r.u t) 10 volume) 10 volume := hout.2.2.2.1
  have hreal : MemLp (fun t => (eLpNorm (r.u t) 10 volume).toReal) 10 volume := by
    apply hr.of_le_enorm hr.aestronglyMeasurable.aemeasurable.ennreal_toReal.aestronglyMeasurable
    filter_upwards [] with t
    rw [Real.enorm_eq_ofReal ENNReal.toReal_nonneg, enorm_eq_self]
    exact ENNReal.ofReal_toReal_le
  constructor
  · filter_upwards [r.slice_eq, hout.2.1] with t ht hm
    exact (memLp_congr_ae ht.1).mp hm
  · apply (memLp_congr_ae ?_).mp hreal
    filter_upwards [r.slice_eq] with t ht
    exact congrArg ENNReal.toReal (eLpNorm_congr_ae ht.1)

#print axioms freeEnergyState_global_value_ten
end HartreeF.FreeTimeDecay
