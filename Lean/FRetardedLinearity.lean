import FRetardedGradient

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory LineDeriv
open scoped ENNReal SchwartzMap
namespace HartreeF.Retarded
open FreeFlow

theorem restrictedL2_add {C : ℝ} (h : OrdinaryEndpointBound C)
    (J : Set ℝ) (hJ : MeasurableSet J) (t : ℝ) (F G : EndpointSource) :
    restrictedL2 h J hJ t (F+G) = restrictedL2 h J hJ t F + restrictedL2 h J hJ t G := by
  apply l2_distribution_injective
  ext φ
  change Lp.toTemperedDistribution (restrictedL2 h J hJ t (F+G)) φ =
    ((Lp.toTemperedDistributionCLM ℂ (volume : Measure V) 2)
      (restrictedL2 h J hJ t F + restrictedL2 h J hJ t G)) φ
  rw [map_add]
  change _ = Lp.toTemperedDistribution (restrictedL2 h J hJ t F) φ +
    Lp.toTemperedDistribution (restrictedL2 h J hJ t G) φ
  rw [restrictedL2_scalar, restrictedL2_scalar, restrictedL2_scalar,
    ← integral_add (h.2 J hJ t F φ).1 (h.2 J hJ t G φ).1]
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae (Lp.coeFn_add F G)] with s hs
  unfold scalarIntegrand
  rw [hs]
  change ((Lp.toTemperedDistributionCLM ℂ (volume : Measure V)
    (ENNReal.ofReal (6/5 : ℝ))) (F s + G s)) _ = _
  rw [map_add]
  rfl

theorem restrictedL2_smul {C : ℝ} (h : OrdinaryEndpointBound C)
    (J : Set ℝ) (hJ : MeasurableSet J) (t : ℝ) (c : ℂ) (F : EndpointSource) :
    restrictedL2 h J hJ t (c • F) = c • restrictedL2 h J hJ t F := by
  apply l2_distribution_injective
  ext φ
  change Lp.toTemperedDistribution (restrictedL2 h J hJ t (c • F)) φ =
    ((Lp.toTemperedDistributionCLM ℂ (volume : Measure V) 2)
      (c • restrictedL2 h J hJ t F)) φ
  rw [map_smul]
  change _ = c • Lp.toTemperedDistribution (restrictedL2 h J hJ t F) φ
  rw [restrictedL2_scalar, restrictedL2_scalar, ← integral_smul]
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae (Lp.coeFn_smul c F)] with s hs
  unfold scalarIntegrand
  rw [hs]
  change ((Lp.toTemperedDistributionCLM ℂ (volume : Measure V)
    (ENNReal.ofReal (6/5 : ℝ))) (c • F s)) _ = _
  rw [map_smul]
  rfl

/-- The constructed source-to-L2 map is complex linear and bounded. -/
def restrictedL2CLM {C : ℝ} (h : OrdinaryEndpointBound C)
    (J : Set ℝ) (hJ : MeasurableSet J) (t : ℝ) : EndpointSource →L[ℂ] L2 :=
  LinearMap.mkContinuous
    { toFun := restrictedL2 h J hJ t
      map_add' := restrictedL2_add h J hJ t
      map_smul' := fun c F => restrictedL2_smul h J hJ t c F }
    C (restrictedL2_norm h J hJ t)

theorem restrictedL2CLM_apply {C : ℝ} (h : OrdinaryEndpointBound C)
    (J : Set ℝ) (hJ : MeasurableSet J) (t : ℝ) (F : EndpointSource) :
    restrictedL2CLM h J hJ t F = restrictedL2 h J hJ t F := rfl

theorem restrictedL2CLM_norm {C : ℝ} (h : OrdinaryEndpointBound C)
    (J : Set ℝ) (hJ : MeasurableSet J) (t : ℝ) : ‖restrictedL2CLM h J hJ t‖ ≤ C :=
  ContinuousLinearMap.opNorm_le_bound _ h.1 (restrictedL2_norm h J hJ t)

theorem restrictedL2_sub {C : ℝ} (h : OrdinaryEndpointBound C)
    (J : Set ℝ) (hJ : MeasurableSet J) (t : ℝ) (F G : EndpointSource) :
    restrictedL2 h J hJ t (F-G) = restrictedL2 h J hJ t F - restrictedL2 h J hJ t G :=
  (restrictedL2CLM h J hJ t).map_sub F G

theorem restrictedL2_difference_bound {C : ℝ} (h : OrdinaryEndpointBound C)
    (J : Set ℝ) (hJ : MeasurableSet J) (t : ℝ) (F G : EndpointSource) :
    ‖restrictedL2 h J hJ t F - restrictedL2 h J hJ t G‖ ≤ C * ‖F-G‖ := by
  rw [← restrictedL2_sub]
  exact restrictedL2_norm h J hJ t _

theorem endpoint_sharp_admissible : (2 : ℝ) ≤ 2 ∧ 2 ≤ 6 ∧
    1/2 + (3/2)/6 = (3/2)/2 := by norm_num

theorem w_sharp_admissible : (2 : ℝ) ≤ 10 ∧ 2 ≤ 30/13 ∧
    1/10 + (3/2)/(30/13) = (3/2)/2 := by norm_num

theorem endpoint_dual_exponents : (1 : ℝ)/2 + 1/2 = 1 ∧ 1/6 + 1/(6/5) = 1 := by
  norm_num

end HartreeF.Retarded
