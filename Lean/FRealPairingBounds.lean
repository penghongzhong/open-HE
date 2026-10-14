import FConjugateWeakPairing
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.Complex.OperatorNorm

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory Filter
open scoped ENNReal Topology
namespace HartreeF.RegularizedEnergyPairing
open EnergySpace WeakSourcePairing
local instance : Fact (1 ≤ ENNReal.ofReal (6/5 : ℝ)) := ⟨by norm_num⟩
local instance : ENNReal.HolderConjugate (ENNReal.ofReal (6/5 : ℝ)) 6 := by
  have h : Real.HolderTriple (6/5) 6 1 := by constructor <;> norm_num
  simpa only [ENNReal.ofReal_ofNat, ENNReal.ofReal_one] using h.ennrealOfReal

section Bilinear
variable {X E F G : Type*} [MeasurableSpace X] (μ : Measure X)
  [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedAddCommGroup G]
  [NormedSpace ℝ E] [NormedSpace ℝ F] [NormedSpace ℝ G] [CompleteSpace G]
  {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q]

theorem lpPairing_apply_bound (B : E →L[ℝ] F →L[ℝ] G)
    (f : Lp E p μ) (g : Lp F q μ) :
    ‖B.lpPairing μ p q f g‖ ≤ ‖B‖ * ‖f‖ * ‖g‖ := by
  have he : B.lpPairing μ p q f g = L1.integral (B.holder 1 f g) := by
    rw [B.lpPairing_eq_integral, L1.integral_eq_integral]
    exact (integral_congr_ae (B.coeFn_holder f g)).symm
  rw [he]
  exact (L1.norm_integral_le _).trans (B.norm_holder_apply_apply_le f g)

theorem lpPairing_norm_bound (B : E →L[ℝ] F →L[ℝ] G) :
    ‖B.lpPairing μ p q‖ ≤ ‖B‖ := by
  apply (B.lpPairing μ p q).opNorm_le_bound (norm_nonneg B)
  intro f
  apply (B.lpPairing μ p q f).opNorm_le_bound (mul_nonneg (norm_nonneg B) (norm_nonneg f))
  intro g
  exact lpPairing_apply_bound μ B f g

omit [CompleteSpace G] [Fact (1 ≤ p)] [Fact (1 ≤ q)] in
theorem lpPairing_integrable (B : E →L[ℝ] F →L[ℝ] G)
    (f : Lp E p μ) (g : Lp F q μ) : Integrable (fun t => B (f t) (g t)) μ :=
  memLp_one_iff_integrable.mp (B.memLp_of_bilin 1 (Lp.memLp f) (Lp.memLp g))
end Bilinear

def scalarIPair : ℂ →L[ℝ] ℂ →L[ℝ] ℝ :=
  (innerSL ℝ : ℂ →L[ℝ] ℂ →L[ℝ] ℝ).flip.comp
    ((ContinuousLinearMap.mul ℝ ℂ) Complex.I)

theorem scalarIPair_apply (f h : ℂ) : scalarIPair f h = inner ℝ h (Complex.I * f) := rfl

theorem scalarIPair_norm_bound : ‖scalarIPair‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  simp only [one_mul]
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro h
  change ‖inner ℝ h (Complex.I * f)‖ ≤ ‖f‖ * ‖h‖
  simpa only [norm_mul, Complex.norm_I, one_mul, mul_one, mul_comm] using
    (norm_inner_le_norm h (Complex.I * f) : ‖inner ℝ h (Complex.I * f)‖ ≤ _)

def sourceIPair : Source →L[ℝ] L6 →L[ℝ] ℝ :=
  scalarIPair.lpPairing volume (ENNReal.ofReal (6/5 : ℝ)) 6

theorem sourceIPair_integral (f : Source) (h : L6) :
    sourceIPair f h = ∫ x, inner ℝ (h x) (Complex.I * f x) :=
  scalarIPair.lpPairing_eq_integral f h

theorem sourceIPair_norm_bound : ‖sourceIPair‖ ≤ 1 :=
  (lpPairing_norm_bound volume scalarIPair).trans scalarIPair_norm_bound

theorem sourceIPair_bound (f : Source) (h : L6) :
    ‖sourceIPair f h‖ ≤ ‖f‖ * ‖h‖ := by
  calc
    _ ≤ ‖scalarIPair‖ * ‖f‖ * ‖h‖ := lpPairing_apply_bound volume scalarIPair f h
    _ ≤ 1 * ‖f‖ * ‖h‖ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right scalarIPair_norm_bound (norm_nonneg _)) (norm_nonneg _)
    _ = _ := by ring

/-- Genuine real Bochner integrability of each gradient error pairing. -/
theorem gradient_error_integrable {T : Type*} [MeasurableSpace T] (μ : Measure T)
    (R : Lp Source 2 μ) (v : Lp L6 2 μ) :
    Integrable (fun t => sourceIPair (R t) (v t)) μ :=
  lpPairing_integrable μ sourceIPair R v

/-- Holder twice gives the coefficient-one spacetime error bound. -/
theorem gradient_error_integral_bound {T : Type*} [MeasurableSpace T] (μ : Measure T)
    (R : Lp Source 2 μ) (v : Lp L6 2 μ) :
    ‖∫ t, sourceIPair (R t) (v t) ∂μ‖ ≤ ‖R‖ * ‖v‖ := by
  rw [← sourceIPair.lpPairing_eq_integral]
  calc
    _ ≤ ‖sourceIPair‖ * ‖R‖ * ‖v‖ := lpPairing_apply_bound μ sourceIPair R v
    _ ≤ 1 * ‖R‖ * ‖v‖ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right sourceIPair_norm_bound (norm_nonneg _)) (norm_nonneg _)
    _ = _ := by ring

def l2IPair : EnergySpace.L2 →L[ℝ] EnergySpace.L2 →L[ℝ] ℝ :=
  (innerSL ℝ : EnergySpace.L2 →L[ℝ] EnergySpace.L2 →L[ℝ] ℝ).flip.comp
    ((Complex.I • ContinuousLinearMap.id ℂ EnergySpace.L2).restrictScalars ℝ)

theorem l2IPair_apply (f h : EnergySpace.L2) : l2IPair f h = inner ℝ h (Complex.I • f) := rfl

theorem l2IPair_norm_bound : ‖l2IPair‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  simp only [one_mul]
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro h
  change ‖inner ℝ h (Complex.I • f)‖ ≤ ‖f‖ * ‖h‖
  simpa only [norm_smul, Complex.norm_I, one_mul, mul_comm] using
    (norm_inner_le_norm h (Complex.I • f) : ‖inner ℝ h (Complex.I • f)‖ ≤ _)

theorem scalar_error_integrable {T : Type*} [MeasurableSpace T] (μ : Measure T)
    (R N : Lp EnergySpace.L2 2 μ) : Integrable (fun t => inner ℝ (N t) (Complex.I • R t)) μ :=
  lpPairing_integrable μ l2IPair R N

theorem scalar_error_integral_bound {T : Type*} [MeasurableSpace T] (μ : Measure T)
    (R N : Lp EnergySpace.L2 2 μ) :
    ‖∫ t, inner ℝ (N t) (Complex.I • R t) ∂μ‖ ≤ ‖R‖ * ‖N‖ := by
  change ‖∫ t, l2IPair (R t) (N t) ∂μ‖ ≤ _
  rw [← l2IPair.lpPairing_eq_integral]
  calc
    _ ≤ ‖l2IPair‖ * ‖R‖ * ‖N‖ := lpPairing_apply_bound μ l2IPair R N
    _ ≤ 1 * ‖R‖ * ‖N‖ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right l2IPair_norm_bound (norm_nonneg _)) (norm_nonneg _)
    _ = _ := by ring

#print axioms sourceIPair_bound
#print axioms gradient_error_integrable
#print axioms gradient_error_integral_bound
#print axioms scalar_error_integrable
#print axioms scalar_error_integral_bound
end HartreeF.RegularizedEnergyPairing
