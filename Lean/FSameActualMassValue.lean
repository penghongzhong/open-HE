import FActualEndpointTailDecay

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 500000
open MeasureTheory Filter Set LineDeriv
open scoped ENNReal Topology
namespace HartreeF.MassAsymptotics
open EnergySpace EnergySpace.Highpass MassRecovery YoungSource Retarded SobolevStretch StationarySelfTest

variable (hDensity : OrdinaryH1Density) {K : ℝ} (hSob : OrdinarySobolev K)
variable {C0 : ℝ} (hE : OrdinaryEndpointBound C0) (q : Cutoff)
variable {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)

/-- A fixed, actual L2 representative recovered at cutoff one. All other cutoffs will identify it. -/
def actualValue (F : EndpointOne) (t : ℝ) (u : EnergyState) : L2 :=
  recoveredValueL2 hDensity hSob hE q (L := 1) (by norm_num) hσ t u
    (projectedSource q (L := 1) (by norm_num) F)

theorem actualValue_distribution (F : EndpointOne) (t : ℝ) (u : EnergyState)
    (hNW : OriginalScalarNoWaste σ t u F) :
    Lp.toTemperedDistribution (actualValue hDensity hSob hE q hσ F t u) = energyDistribution u :=
  recoveredValueL2_distribution hDensity hSob hE q (by norm_num) hσ t u F
    (projectedSource q (L := 1) (by norm_num) F)
    (projectedSource_tail_distribution q (by norm_num) F t) hNW

theorem actualValue_same_value (F : EndpointOne) (t : ℝ) (u : EnergyState)
    (hNW : OriginalScalarNoWaste σ t u F) :
    (actualValue hDensity hSob hE q hσ F t u : V → ℂ) =ᵐ[volume] energyValue u :=
  CriticalPathSpace.spatial_ae_eq_of_distribution_eq _ _
    (actualValue_distribution hDensity hSob hE q hσ F t u hNW)

theorem actualValue_actual_weak_gradient (F : EndpointOne) (t : ℝ) (u : EnergyState)
    (hNW : OriginalScalarNoWaste σ t u F) (A : ℂ →L[ℝ] ℝ) :
    HasWeakGradient (fun x => A (actualValue hDensity hSob hE q hσ F t u x))
      (energyProjectedGradient A u) :=
  recoveredValueL2_actual_weak_gradient hDensity hSob hE q (by norm_num) hσ t u F
    (projectedSource q (L := 1) (by norm_num) F)
    (projectedSource_tail_distribution q (by norm_num) F t) hNW A

/-- Same original distribution forces all positive-frequency recoveries to be the same L2 class. -/
theorem actualValue_eq_recovery (F : EndpointOne) (t : ℝ) (u : EnergyState)
    (hNW : OriginalScalarNoWaste σ t u F) {L : ℝ} (hL : 0 < L) :
    actualValue hDensity hSob hE q hσ F t u =
      recoveredValueL2 hDensity hSob hE q hL hσ t u (projectedSource q hL F) := by
  apply FreeFlow.l2_distribution_injective
  exact (actualValue_distribution hDensity hSob hE q hσ F t u hNW).trans
    (recoveredValueL2_distribution hDensity hSob hE q hL hσ t u F
      (projectedSource q hL F) (projectedSource_tail_distribution q hL F t) hNW).symm

theorem actualValue_budget (F : EndpointOne) (t : ℝ) (u : EnergyState)
    (hNW : OriginalScalarNoWaste σ t u F) {L : ℝ} (hL : 0 < L)
    {B : ℝ} (hB : pureGradientNorm u ≤ B) :
    ‖actualValue hDensity hSob hE q hσ F t u‖ ≤
      B/L + (C0 * cutoffYoungConstant q) * Real.sqrt L * tailNorm t F := by
  rw [actualValue_eq_recovery hDensity hSob hE q hσ F t u hNW hL]
  exact recoveredValueL2_mass_budget hDensity hSob hE q hL hσ t u F
    (projectedSource q hL F) hB (projectedSource_tail_norm q hL F t)

theorem actualValue_low_error (F : EndpointOne) (t : ℝ) (u : EnergyState)
    (hNW : OriginalScalarNoWaste σ t u F) {L : ℝ} (hL : 0 < L) :
    ‖actualValue hDensity hSob hE q hσ F t u - highValueL2 hDensity hSob q hL u‖ ≤
      (C0 * cutoffYoungConstant q) * Real.sqrt L * tailNorm t F := by
  rw [actualValue_eq_recovery hDensity hSob hE q hσ F t u hNW hL,
    recoveredValueL2, add_sub_cancel_left]
  exact (recoveredLowL2_norm hE hσ t (projectedSource q hL F)).trans
    ((mul_le_mul_of_nonneg_left (projectedSource_tail_norm q hL F t) hE.1).trans_eq (by ring))

theorem actualValue_low_error_uniform (F : EndpointOne) (t : ℝ) (u : EnergyState)
    (hNW : OriginalScalarNoWaste σ t u F) {L : ℝ} (hL : 0 < L) :
    ‖actualValue hDensity hSob hE q hσ F t u - highValueL2 hDensity hSob q hL u‖ ≤
      (C0 * cutoffYoungConstant q) * Real.sqrt L * ‖F‖ := by
  exact (actualValue_low_error hDensity hSob hE q hσ F t u hNW hL).trans
    (mul_le_mul_of_nonneg_left (tailNorm_le_norm F t)
      (mul_nonneg (mul_nonneg hE.1 (cutoffYoungConstant_nonneg q)) (Real.sqrt_nonneg L)))

theorem originalValue_memLp_and_norm (F : EndpointOne) (t : ℝ) (u : EnergyState)
    (hNW : OriginalScalarNoWaste σ t u F) :
    MemLp (energyValue u : V → ℂ) 2 volume ∧
      (eLpNorm (energyValue u : V → ℂ) 2 volume).toReal =
        ‖actualValue hDensity hSob hE q hσ F t u‖ := by
  have ha := actualValue_same_value hDensity hSob hE q hσ F t u hNW
  refine ⟨(memLp_congr_ae ha).mp (Lp.memLp _), ?_⟩
  rw [← eLpNorm_congr_ae ha]
  exact (Lp.norm_def _).symm

end HartreeF.MassAsymptotics
