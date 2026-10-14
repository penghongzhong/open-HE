import FLinearRetardedCandidate

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000
open MeasureTheory LineDeriv Laplacian
open scoped ENNReal Topology SchwartzMap

namespace HartreeF.LinearWeakEquation
open EnergySpace Retarded

/-- Exact ordinary free Fourier evolution theorem, kept as an explicit Prop.
Le Coz Prop.2.3.1 p.17: the displayed Fourier group on every T in S' is smooth
and solves i U_t + Delta U = 0. Complex-linear evaluation therefore has derivative
i U(Delta phi). `Retarded.free_apply` below is the already-proved literal transpose.
No retarded integral, inhomogeneous PDE, or Hartree conclusion is an interface field. -/
structure OrdinaryFreeDistributionScalarGenerator : Prop where
  derivative : ∀ (T : TD) (φ : Test) (t : ℝ),
    HasDerivAt (fun r => FreeFlow.free r T φ)
      (Complex.I * FreeFlow.free t T (Δ φ)) t

/-- Native conversion of the ordinary distribution theorem into its actual bilinear transpose. -/
theorem freeTestPair_hasDerivAt (hgen : OrdinaryFreeDistributionScalarGenerator)
    (T : TD) (φ : Test) (t : ℝ) :
    HasDerivAt (fun r => T (freeTest r φ)) (Complex.I * T (freeTest t (Δ φ))) t := by
  simpa only [free_apply] using hgen.derivative T φ t

theorem freeTestPair_continuous (hgen : OrdinaryFreeDistributionScalarGenerator)
    (T : TD) (φ : Test) : Continuous (fun t => T (freeTest t φ)) :=
  continuous_iff_continuousAt.mpr (fun t => (freeTestPair_hasDerivAt hgen T φ t).continuousAt)

set_option backward.isDefEq.respectTransparency false in
theorem freeTestPair_shift_hasDerivAt (hgen : OrdinaryFreeDistributionScalarGenerator)
    (T : TD) (φ : Test) (s t : ℝ) :
    HasDerivAt (fun r => T (freeTest (r-s) φ))
      (Complex.I * T (freeTest (t-s) (Δ φ))) t := by
  simpa only [one_smul, Function.comp_def, id_eq] using (freeTestPair_hasDerivAt hgen T φ (t-s)).scomp t
    ((hasDerivAt_id t).sub_const s)

theorem freeTestPair_zero (T : TD) (φ : Test) : T (freeTest 0 φ) = T φ := by
  rw [← free_apply, FreeFlow.free_zero]

/-- Kernel obtained by testing the pure, unnormalized retarded integral. -/
def kernelWeakTest (T : TD) (η : TimeTest) (φ : Test) (s t : ℝ) : ℂ :=
  -Complex.I * deriv η t * T (freeTest (t-s) φ) + η t * T (freeTest (t-s) (Δ φ))

theorem kernelWeakTest_continuous (hgen : OrdinaryFreeDistributionScalarGenerator)
    (T : TD) (η : TimeTest) (φ : Test) (s : ℝ) :
    Continuous (kernelWeakTest T η φ s) := by
  exact ((continuous_const.mul ((η.smooth 1).continuous_deriv_one)).mul
    ((freeTestPair_continuous hgen T φ).comp (continuous_id.sub continuous_const))).add
    (η.continuous.mul ((freeTestPair_continuous hgen T (Δ φ)).comp
      (continuous_id.sub continuous_const)))

/-- The kernel is -i times the derivative of eta times the literal free-test pairing. -/
theorem kernelWeakTest_antiderivative (hgen : OrdinaryFreeDistributionScalarGenerator)
    (T : TD) (η : TimeTest) (φ : Test) (s t : ℝ) :
    HasDerivAt (fun r => -Complex.I * (η r * T (freeTest (r-s) φ)))
      (kernelWeakTest T η φ s t) t := by
  have h := (η.differentiableAt.hasDerivAt.mul
    (freeTestPair_shift_hasDerivAt hgen T φ s t)).const_mul (-Complex.I)
  convert h using 1
  dsimp [kernelWeakTest]
  ring_nf
  simp only [Complex.I_sq]
  ring

/-- Genuine scalar FTC, valid for every S' source slice; this is not an assumed
inhomogeneous Duhamel identity. The positive i boundary sign is explicit. -/
theorem kernelWeakTest_integral (hgen : OrdinaryFreeDistributionScalarGenerator)
    (T : TD) (η : TimeTest) (φ : Test) {s b : ℝ} (hsb : s ≤ b) (hηb : η b = 0) :
    (∫ t in Set.Ioc s b, kernelWeakTest T η φ s t) = Complex.I * η s * T φ := by
  have hi : IntervalIntegrable (kernelWeakTest T η φ s) volume s b :=
    (kernelWeakTest_continuous hgen T η φ s).intervalIntegrable s b
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => kernelWeakTest_antiderivative hgen T η φ s t) hi
  rw [intervalIntegral.integral_of_le hsb] at h
  simpa only [hηb, zero_mul, mul_zero, sub_self, freeTestPair_zero,
    zero_sub, neg_mul, neg_neg, mul_assoc] using h

end HartreeF.LinearWeakEquation
