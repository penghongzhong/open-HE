import FActualSpatialDualPairing

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 700000
open MeasureTheory Filter Set
open scoped ENNReal Topology RealInnerProductSpace
namespace HartreeF.LocalDualSource
open EnergySpace LocalChargeBridge LocalChargeRigidity

/-- The real L2 inner product is the real part of the actual sesquilinear integral. -/
theorem real_inner_spatialPair (f g : L2) : inner ℝ f g = (spatialPair 2 2 f g).re := by
  rw [spatialPair_eq_integral, MeasureTheory.L2.inner_def]
  change _ = Complex.reCLM _
  rw [← Complex.reCLM.integral_comp_comm (spatialPair_integrable f g)]
  apply integral_congr_ae
  filter_upwards [] with x
  simp [Complex.inner, Complex.mul_re]
  ring

/-- Exact mixed charge integrand, not only its diagonal mass. -/
def physicalChargeIntegrand (R : ℝ) (u w : EnergyState) (x : V) : ℂ :=
  (chargeCutoff R x : ℂ) * energyValue u x * star (energyValue w x)

theorem physicalChargeValue_pair_ae {R : ℝ} (hR : 0 < R) (u w : EnergyState) :
    (fun x : V => physicalChargeValue hR u x * star (physicalChargeValue hR w x)) =ᵐ[volume]
      physicalChargeIntegrand R u w := by
  have hu := cutoffL6L2_ae
    (Real.continuous_sqrt.comp (chargeCutoff_smooth R).continuous)
    ((chargeCutoff_compact hR).comp_left Real.sqrt_zero) (energyValue u)
  have hw := cutoffL6L2_ae
    (Real.continuous_sqrt.comp (chargeCutoff_smooth R).continuous)
    ((chargeCutoff_compact hR).comp_left Real.sqrt_zero) (energyValue w)
  filter_upwards [hu, hw] with x hx hy
  change physicalChargeValue hR u x = _ at hx
  change physicalChargeValue hR w x = _ at hy
  rw [hx, hy]
  simp only [Function.comp_apply, Complex.real_smul]
  have hs : Real.sqrt (chargeCutoff R x)^2 = chargeCutoff R x :=
    Real.sq_sqrt (chargeCutoff_nonneg R x)
  have hsC : (Real.sqrt (chargeCutoff R x) : ℂ) * (Real.sqrt (chargeCutoff R x) : ℂ) =
      (chargeCutoff R x : ℂ) := by
    norm_cast
    nlinarith [hs]
  calc
    _ = ((Real.sqrt (chargeCutoff R x) : ℂ) * (Real.sqrt (chargeCutoff R x) : ℂ)) *
        energyValue u x * star (energyValue w x) := by
      simp only [Complex.star_def, map_mul, Complex.conj_ofReal]
      ring
    _ = _ := by rw [hsC]; rfl

theorem physicalChargeIntegrand_integrable {R : ℝ} (hR : 0 < R) (u w : EnergyState) :
    Integrable (physicalChargeIntegrand R u w) volume :=
  (spatialPair_integrable (physicalChargeValue hR u) (physicalChargeValue hR w)).congr
    (physicalChargeValue_pair_ae hR u w)

/-- The exact bounded dual appearing in the accepted quadratic rule is the original cutoff test. -/
theorem physicalChargeForm_eq_integral {R : ℝ} (hR : 0 < R) (u w : EnergyState) :
    physicalChargeForm hR u w = (∫ x : V, physicalChargeIntegrand R u w x).re := by
  change inner ℝ (physicalChargeValue hR u) (physicalChargeValue hR w) = _
  rw [real_inner_spatialPair, spatialPair_eq_integral,
    integral_congr_ae (physicalChargeValue_pair_ae hR u w)]

/-- Same-time scalar pairing, valid for any exact time domain without adding time regularity. -/
theorem physicalChargeForm_apply_path {R : ℝ} (hR : 0 < R)
    (u : ℝ → EnergyState) (t : ℝ) (w : EnergyState) :
    physicalChargeForm hR (u t) w =
      (∫ x : V, (chargeCutoff R x : ℂ) * energyValue (u t) x * star (energyValue w x)).re :=
  physicalChargeForm_eq_integral hR (u t) w

end HartreeF.LocalDualSource
