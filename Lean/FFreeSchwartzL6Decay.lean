import FUniformContinuousLpDecay
import FFreeOrbitUniformContinuity
import FL6L2L10Interpolation
import FFreeGlobalValueS

noncomputable section
set_option autoImplicit false
set_option warningAsError true
open MeasureTheory Filter
open scoped ENNReal Topology
namespace HartreeF.FreeTimeDecay
open EnergySpace SobolevStretch StationarySelfTest ActualStrichartz

/-- Scalar L2 is used only for the actual Schwartz approximant, never for the target datum. -/
theorem freeEnergyState_schwartz_value_L2 (hDensity : OrdinaryH1Density)
    {K : ℝ} (hSob : OrdinarySobolev K) (phi : Test) (t : ℝ) :
    MemLp (energyValue (freeEnergyState hDensity hSob t (schwartzEnergyState phi))) 2 volume ∧
    (eLpNorm (energyValue (freeEnergyState hDensity hSob t (schwartzEnergyState phi))) 2 volume).toReal =
      ‖phi.toLp 2 volume‖ := by
  have hae : (energyValue (freeEnergyState hDensity hSob t (schwartzEnergyState phi)) : Space → ℂ) =ᵐ[volume]
      (FreeFlow.freeSchwartz t phi).toLp 2 volume := by
    rw [freeEnergyState_schwartz]
    exact (schwartzEnergyState_value_ae _).trans ((FreeFlow.freeSchwartz t phi).coeFn_toLp 2 volume).symm
  constructor
  · exact (memLp_congr_ae hae).mpr (Lp.memLp _)
  · rw [eLpNorm_congr_ae hae, ← Lp.norm_def, FreeFlow.freeSchwartz_toL2, FreeFlow.freeL2_norm]

/-- Conserved L2 on Schwartz and actual global S give the exact time-L12 budget. -/
theorem freeEnergyState_schwartz_value_integrable_twelfth (hDensity : OrdinaryH1Density)
    {K C : ℝ} (hSob : OrdinarySobolev K) (hS : OrdinaryHomogeneousStrichartz C) (phi : Test) :
    Integrable (fun t : ℝ => ‖energyValue (freeEnergyState hDensity hSob t (schwartzEnergyState phi))‖^12)
      volume := by
  let u := schwartzEnergyState phi
  have hglobal := freeEnergyState_global_value_ten hDensity hSob hS u
  have hint : Integrable (fun t : ℝ =>
      (eLpNorm (energyValue (freeEnergyState hDensity hSob t u)) 10 volume).toReal^10) volume := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg] using
      hglobal.2.integrable_norm_pow (by decide : (10:ℕ)≠0)
  apply (hint.const_mul (‖phi.toLp 2 volume‖^2)).mono'
    (((freeEnergyState_value_norm_uniformContinuous hDensity hSob u).continuous.pow 12).aestronglyMeasurable)
  filter_upwards [hglobal.1] with t ht
  have h2 := freeEnergyState_schwartz_value_L2 hDensity hSob phi t
  have hi := l6_twelfth_le_l2_sq_mul_l10_tenth h2.1 ht
  rw [h2.2] at hi
  change |‖energyValue (freeEnergyState hDensity hSob t u)‖^12| ≤ _
  rw [abs_of_nonneg (pow_nonneg (norm_nonneg _) 12)]
  simpa only [Lp.norm_def, u] using hi

/-- Both tails are proved before passing to an arbitrary homogeneous datum. -/
theorem freeEnergyState_schwartz_value_norm_decay (hDensity : OrdinaryH1Density)
    {K C : ℝ} (hSob : OrdinarySobolev K) (hS : OrdinaryHomogeneousStrichartz C) (phi : Test) :
    Tendsto (fun t : ℝ => ‖energyValue (freeEnergyState hDensity hSob t (schwartzEnergyState phi))‖)
      atTop (𝓝 0) ∧
    Tendsto (fun t : ℝ => ‖energyValue (freeEnergyState hDensity hSob t (schwartzEnergyState phi))‖)
      atBot (𝓝 0) := by
  have hu := freeEnergyState_value_norm_uniformContinuous hDensity hSob (schwartzEnergyState phi)
  have hi := freeEnergyState_schwartz_value_integrable_twelfth hDensity hSob hS phi
  exact ⟨uniformContinuous_integrable_pow_tendsto_zero_atTop hu (fun _ => norm_nonneg _) hi,
    uniformContinuous_integrable_pow_tendsto_zero_atBot hu (fun _ => norm_nonneg _) hi⟩

#print axioms freeEnergyState_schwartz_value_L2
#print axioms freeEnergyState_schwartz_value_integrable_twelfth
#print axioms freeEnergyState_schwartz_value_norm_decay
end HartreeF.FreeTimeDecay
