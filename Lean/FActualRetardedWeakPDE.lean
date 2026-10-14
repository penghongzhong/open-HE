import FActualFreeKernelIntegrability
import FVolterraTriangleFubini

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory Filter LineDeriv Laplacian
open scoped ENNReal Topology SchwartzMap

namespace HartreeF.LinearWeakEquation
open EnergySpace Retarded FreeTestBounds SobolevStretch StationarySelfTest
open ActualStrichartz ActualDuhamelPath CriticalPathSpace IntervalTimeTransport

variable (hDensity : OrdinaryH1Density) {K C0 C a b : ℝ}
  (hSob : OrdinarySobolev K) (h0 : OrdinaryEndpointBound C0)
  (hret : OrdinaryRetardedStrichartz h0 C) (hab : a ≤ b)
  (E : CompatibleL1IntervalSource a b)

/-- The already constructed pure retarded path, evaluated as a tempered distribution. -/
def actualPureRetardedDistribution (t : ℝ) : TD :=
  energyDistribution (energyPath _ (E.retardedCriticalPath hDensity hSob h0 hret)
    (Set.projIcc a b hab t))

theorem actualPureRetardedDistribution_scalar {t : ℝ} (ht : t ∈ Set.Icc a b) (φ : Test) :
    actualPureRetardedDistribution hDensity hSob h0 hret hab E t φ =
      ∫ s in Set.Icc a b ∩ Set.Iio t,
        Lp.toTemperedDistribution (E.value s) (freeTest (t-s) φ) := by
  unfold actualPureRetardedDistribution
  rw [Set.projIcc_of_mem hab ht]
  exact E.retardedCriticalPath_scalar hDensity hSob h0 hret ⟨t, ht⟩ φ

theorem actualPureRetardedDistribution_weakOperator (η : TimeTest) (φ : Test)
    {t : ℝ} (ht : t ∈ Set.Icc a b) :
    weakOperator (actualPureRetardedDistribution hDensity hSob h0 hret hab E) η φ t =
      ∫ s in Set.Icc a b ∩ Set.Iio t,
        kernelWeakTest (Lp.toTemperedDistribution (E.value s)) η φ s t := by
  have h1 := (E.retarded_scalar_integrable hDensity hSob t φ).const_mul (-Complex.I * deriv η t)
  have h2 := (E.retarded_scalar_integrable hDensity hSob t (Δ φ)).const_mul (η t)
  simp only [kernelWeakTest]
  rw [integral_add h1 h2, integral_const_mul, integral_const_mul]
  simp only [weakOperator, actualPureRetardedDistribution_scalar hDensity hSob h0 hret hab E ht]

theorem timeTest_right_zero (η : TimeTest) (hη : tsupport η ⊆ Set.Ioo a b) : η b = 0 := by
  apply image_eq_zero_of_notMem_tsupport
  intro hb
  exact (lt_irrefl b) (hη hb).2

theorem timeTest_left_zero (η : TimeTest) (hη : tsupport η ⊆ Set.Ioo a b) : η a = 0 := by
  apply image_eq_zero_of_notMem_tsupport
  intro ha
  exact (lt_irrefl a) (hη ha).1

theorem interval_future_eq_Ioc {s : ℝ} (hs : s ∈ Set.Icc a b) :
    Set.Icc a b ∩ Set.Ioi s = Set.Ioc s b := by
  ext t
  constructor
  · intro ht
    exact ⟨ht.2, ht.1.2⟩
  · intro ht
    exact ⟨⟨hs.1.trans ht.1.le, ht.2⟩, ht.1⟩

/-- The actual unnormalized retarded integral solves i R_t + Delta R = i F.
All scalar integrability, the triangular Fubini swap and its FTC boundary term
are produced here from the original L1 source. No candidate PDE is assumed. -/
theorem actualPureRetardedDistribution_weakEquation
    (hgen : OrdinaryFreeDistributionScalarGenerator) :
    WeakEquation a b (actualPureRetardedDistribution hDensity hSob h0 hret hab E)
      (fun t => Complex.I • Lp.toTemperedDistribution (E.value t)) := by
  intro η hη φ
  have hH := actualKernelWeakTest_prod_integrable hDensity hSob E.value E.value_integrable η φ
  obtain ⟨hPast, hFuture, hSwap⟩ := VolterraTriangle.interval_triangle_fubini hH
  have hleft : (fun t => ∫ s in Set.Icc a b ∩ Set.Iio t,
      kernelWeakTest (Lp.toTemperedDistribution (E.value s)) η φ s t) =ᵐ[volume.restrict (Set.Icc a b)]
      weakOperator (actualPureRetardedDistribution hDensity hSob h0 hret hab E) η φ := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact (actualPureRetardedDistribution_weakOperator hDensity hSob h0 hret hab E η φ ht).symm
  have hright : (fun s => ∫ t in Set.Icc a b ∩ Set.Ioi s,
      kernelWeakTest (Lp.toTemperedDistribution (E.value s)) η φ s t) =ᵐ[volume.restrict (Set.Icc a b)]
      (fun s => η s * (Complex.I • Lp.toTemperedDistribution (E.value s)) φ) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    rw [interval_future_eq_Ioc hs, kernelWeakTest_integral hgen _ η φ hs.2
      (timeTest_right_zero η hη)]
    simp only [smul_apply, smul_eq_mul]
    ring
  refine ⟨hPast.congr hleft, hFuture.congr hright, ?_⟩
  rw [← integral_congr_ae hleft, ← integral_congr_ae hright]
  exact hSwap

end HartreeF.LinearWeakEquation
