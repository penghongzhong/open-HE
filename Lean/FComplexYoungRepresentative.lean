import FActualL1LpConvolution
import FSchwartzYoungDistribution
import Mathlib.Basic.Real.ConjExponents

/-!
F-only static proof candidate. NOT COMPILED.
Identify the existing complex Lp-valued Young integral with the literal
complex convolution. The real-density representative theorem is applied to
Re f and Im f. Its Fubini hypotheses follow from the actual L1 assumptions;
there is no joint pointwise measurability or desired Young conclusion premise.
-/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory Filter
open scoped ENNReal Topology SchwartzMap

namespace HartreeF.ComplexYoungRepresentative
open EnergySpace YoungSource MassRecovery ProfileSpatialSmoothing RieszL1LocalDomains

/-- Scalar decomposition valid in the actual complex Lp module as well as in ℂ. -/
theorem complex_smul_re_im {E : Type*} [AddCommGroup E] [Module ℂ E] [Module ℝ E]
    [IsScalarTower ℝ ℂ E] (c : ℂ) (v : E) :
    c • v = c.re • v + Complex.I • (c.im • v) := by
  calc
    c • v = ((c.re : ℂ) + (c.im : ℂ) * Complex.I) • v :=
      congrArg (fun z : ℂ => z • v) (Complex.re_add_im c).symm
    _ = c.re • v + c.im • (Complex.I • v) := by
      rw [add_smul, mul_smul]
      rw [show (c.re : ℂ) • v = c.re • v from algebraMap_smul ℂ c.re v]
      rw [show (c.im : ℂ) • (Complex.I • v) = c.im • (Complex.I • v) from
        algebraMap_smul ℂ c.im (Complex.I • v)]
    _ = c.re • v + Complex.I • (c.im • v) := by
      rw [smul_comm c.im Complex.I v]

/-- The literal convolution, using the actual representative of the input. -/
def actualComplexConvolution (f k : Space → ℂ) (x : Space) : ℂ :=
  ∫ y, f y * k (x - y)

/-- Global product integrability is derived from the two actual L1 inputs. -/
theorem actualComplexConvolution_integrand_integrable {f k : Space → ℂ}
    (hf : Integrable f volume) (hk : Integrable k volume) :
    Integrable (fun z : Space × Space => f z.2 * k (z.1 - z.2))
      (volume.prod volume) := by
  simpa only [ContinuousLinearMap.lsmul_apply, smul_eq_mul] using
    hf.convolution_integrand (ContinuousLinearMap.lsmul ℂ ℂ) hk

/-- Thus the literal integral exists at almost every point, with no extra premise. -/
theorem actualComplexConvolution_sections {f k : Space → ℂ}
    (hf : Integrable f volume) (hk : Integrable k volume) :
    ∀ᵐ x ∂volume, Integrable (fun y => f y * k (x - y)) volume :=
  (actualComplexConvolution_integrand_integrable hf hk).prod_right_ae

theorem actualComplexConvolution_integrable {f k : Space → ℂ}
    (hf : Integrable f volume) (hk : Integrable k volume) :
    Integrable (actualComplexConvolution f k) volume :=
  (actualComplexConvolution_integrand_integrable hf hk).integral_prod_left

/-- The complex convolution is the sum of its two real-density convolutions.
Both sections are supplied by the actual L1 convolution/Fubini theorem. -/
theorem actualComplexConvolution_re_im_ae {f k : Space → ℂ}
    (hf : Integrable f volume) (hk : Integrable k volume) :
    actualComplexConvolution f k =ᵐ[volume]
      fun x => actualConvolution (fun y => (f y).re) k x +
        Complex.I • actualConvolution (fun y => (f y).im) k x := by
  have hR : ∀ᵐ x ∂volume,
      Integrable (fun y => (f y).re • k (x - y)) volume :=
    hf.re.ae_convolution_exists (ContinuousLinearMap.lsmul ℝ ℝ) hk
  have hI : ∀ᵐ x ∂volume,
      Integrable (fun y => (f y).im • k (x - y)) volume :=
    hf.im.ae_convolution_exists (ContinuousLinearMap.lsmul ℝ ℝ) hk
  filter_upwards [hR, hI] with x hxR hxI
  unfold actualComplexConvolution actualConvolution
  calc
    (∫ y, f y * k (x - y)) =
        ∫ y, (f y).re • k (x - y) + Complex.I • ((f y).im • k (x - y)) := by
      apply integral_congr_ae
      filter_upwards [] with y
      exact complex_smul_re_im (f y) (k (x - y))
    _ = _ := by
      have hIx : Integrable (fun y => Complex.I • ((f y).im • k (x - y))) volume :=
        hxI.fun_smul Complex.I
      rw [integral_add hxR hIx, integral_smul]

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Decomposition of the existing complex Young value, not a new realization. -/
theorem youngValue_re_im (hp : p ≠ ∞) (K : Lp ℂ p (volume : Measure Space))
    (f : OneSpace) :
    youngValue K f = lpAverage (fun y => (f y).re) K +
      Complex.I • lpAverage (fun y => (f y).im) K := by
  have hf : Integrable (f : Space → ℂ) volume := memLp_one_iff_integrable.mp (Lp.memLp f)
  have hR : Integrable (fun y : Space => (f y).re • lpShift (-y) K) volume :=
    lpAverage_integrable hp hf.re K
  have hI : Integrable (fun y : Space => (f y).im • lpShift (-y) K) volume :=
    lpAverage_integrable hp hf.im K
  unfold youngValue lpAverage
  calc
    (∫ y : Space, f y • lpShift (-y) K) =
        ∫ y : Space, (f y).re • lpShift (-y) K +
          Complex.I • ((f y).im • lpShift (-y) K) := by
      apply integral_congr_ae
      filter_upwards [] with y
      exact complex_smul_re_im (f y) (lpShift (-y) K)
    _ = _ := by
      have hIc : Integrable (fun y => Complex.I • ((f y).im • lpShift (-y) K)) volume :=
        hI.fun_smul Complex.I
      rw [integral_add hR hIc, integral_smul]

/-- Every finite p ≥ 1 is covered. The auxiliary conjugate is constructed here,
including q = ∞ when p = 1; it is not an additional caller-supplied hypothesis. -/
theorem youngValue_coe_ae (hp : p ≠ ∞) {k : Space → ℂ}
    (hk1 : Integrable k volume) (hkp : MemLp k p volume) (f : OneSpace) :
    (youngValue (hkp.toLp k) f : Space → ℂ) =ᵐ[volume]
      actualComplexConvolution (f : Space → ℂ) k := by
  let q := ENNReal.conjExponent p
  let : ENNReal.HolderConjugate q p := by
    change ENNReal.HolderConjugate (ENNReal.conjExponent p) p
    infer_instance
  let : Fact (1 ≤ q) := ⟨ENNReal.HolderConjugate.one_le q p⟩
  have hf : Integrable (f : Space → ℂ) volume := memLp_one_iff_integrable.mp (Lp.memLp f)
  let A := lpAverage (fun y => (f y).re) (hkp.toLp k)
  let B := lpAverage (fun y => (f y).im) (hkp.toLp k)
  have hA : (A : Space → ℂ) =ᵐ[volume] actualConvolution (fun y => (f y).re) k :=
    lpAverage_coe_ae (q := q) hp hf.re hk1 hkp
  have hB : (B : Space → ℂ) =ᵐ[volume] actualConvolution (fun y => (f y).im) k :=
    lpAverage_coe_ae (q := q) hp hf.im hk1 hkp
  rw [youngValue_re_im hp]
  change ((A + Complex.I • B : Lp ℂ p (volume : Measure Space)) : Space → ℂ) =ᵐ[volume]
    actualComplexConvolution (f : Space → ℂ) k
  filter_upwards [Lp.coeFn_add A (Complex.I • B), Lp.coeFn_smul Complex.I B,
    hA, hB, actualComplexConvolution_re_im_ae hf hk1] with x hadd hsmul hax hbx hsplit
  calc
    (A + Complex.I • B) x = A x + (Complex.I • B) x := hadd
    _ = actualConvolution (fun y => (f y).re) k x +
        Complex.I • actualConvolution (fun y => (f y).im) k x := by
      change (Complex.I • B) x = Complex.I • B x at hsmul
      rw [hsmul, hax, hbx]
    _ = actualComplexConvolution (f : Space → ℂ) k x := hsplit.symm

theorem youngCLM_coe_ae (hp : p ≠ ∞) {k : Space → ℂ}
    (hk1 : Integrable k volume) (hkp : MemLp k p volume) (f : OneSpace) :
    (youngCLM hp (hkp.toLp k) f : Space → ℂ) =ᵐ[volume]
      actualComplexConvolution (f : Space → ℂ) k :=
  youngValue_coe_ae hp hk1 hkp f

/-- Genuine complex L1→Lp membership of this exact literal integral. -/
theorem actualComplexConvolution_memLp (hp : p ≠ ∞) {k : Space → ℂ}
    (hk1 : Integrable k volume) (hkp : MemLp k p volume) (f : OneSpace) :
    MemLp (actualComplexConvolution (f : Space → ℂ) k) p volume :=
  (Lp.memLp (youngValue (hkp.toLp k) f)).ae_eq (youngValue_coe_ae hp hk1 hkp f)

/-- Specialization to the exact Schwartz kernel realization used by YoungSource. -/
theorem young_schwartz_coe_ae (hp : p ≠ ∞) (k : Test) (f : OneSpace) :
    (youngCLM hp (k.toLp p volume) f : Space → ℂ) =ᵐ[volume]
      fun x => ∫ y, f y * k (x - y) :=
  youngCLM_coe_ae hp k.integrable (k.memLp p volume) f

/-- The existing native norm bound applies to the same literal representative. -/
theorem actualComplexConvolution_eLpNorm_toReal_le (hp : p ≠ ∞)
    (k : Test) (f : OneSpace) :
    (eLpNorm (fun x : Space => ∫ y, f y * k (x - y)) p volume).toReal ≤
      ‖k.toLp p volume‖ * ‖f‖ := by
  calc
    _ = ‖youngCLM hp (k.toLp p volume) f‖ := by
      rw [Lp.norm_def, eLpNorm_congr_ae (young_schwartz_coe_ae hp k f)]
    _ ≤ _ := youngValue_norm _ _

/-- Different finite exponent outputs have the same actual function a.e. -/
theorem young_schwartz_coe_ae_cross {r : ℝ≥0∞} [Fact (1 ≤ r)]
    (hp : p ≠ ∞) (hr : r ≠ ∞) (k : Test) (f : OneSpace) :
    (youngCLM hp (k.toLp p volume) f : Space → ℂ) =ᵐ[volume]
      (youngCLM hr (k.toLp r volume) f : Space → ℂ) :=
  (young_schwartz_coe_ae hp k f).trans (young_schwartz_coe_ae hr k f).symm

/-- The canonical p = 1 output itself has the extra Lp domain. -/
theorem youngOne_memLp (hp : p ≠ ∞) (k : Test) (f : OneSpace) :
    MemLp (youngCLM (by simp : (1 : ℝ≥0∞) ≠ ∞) (k.toLp 1 volume) f : Space → ℂ)
      p volume :=
  (Lp.memLp (youngCLM hp (k.toLp p volume) f)).ae_eq
    (young_schwartz_coe_ae_cross (p := p) (r := 1) hp (by simp) k f)

/-- Its conversion to Lp is exactly the already constructed Young value. -/
theorem youngOne_toLp_eq (hp : p ≠ ∞) (k : Test) (f : OneSpace) :
    (youngOne_memLp hp k f).toLp
        (youngCLM (by simp : (1 : ℝ≥0∞) ≠ ∞) (k.toLp 1 volume) f : Space → ℂ) =
      youngCLM hp (k.toLp p volume) f := by
  apply Lp.ext
  exact (youngOne_memLp hp k f).coeFn_toLp.trans
    (young_schwartz_coe_ae_cross (p := 1) (r := p) (by simp) hp k f)

end HartreeF.ComplexYoungRepresentative
