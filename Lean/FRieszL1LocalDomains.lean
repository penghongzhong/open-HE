import FRieszNearFarKernel
import FActualL1LpConvolution
import FRieszGradientConvolutionDomain

/-!
F-only static proof candidate. NOT COMPILED.
The literal Riesz potential of any real L1 density belongs locally to L2,
and its literal gradient convolution belongs locally to L6/5, for 2 ≤ α < 3.
This includes α=2 only as a LOCAL domain assertion; no strong endpoint HLS is used.
All spaces, kernels, coordinates and literal integral representatives are inherited.
-/
noncomputable section
set_option autoImplicit false
open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace HartreeF.RieszL1LocalDomains
open ForcingDomain RieszWeakDerivative RieszKernelDerivative RieszConvolutionDerivative
open SobolevStretch

variable {E : Type*} [NormedAddCommGroup E]

/-- Local radial-power calculation, expressed directly as membership of the cut kernel. -/
theorem nearPart_memLp_of_norm_rpow {k : Space → E} {C β p : ℝ}
    (hk : AEStronglyMeasurable k volume) (hC : 0 ≤ C) (hp : 0 < p)
    (hpow : -3 < β * p) (hnorm : ∀ z, ‖k z‖ = C * ‖z‖ ^ β) :
    MemLp (nearPart k) (ENNReal.ofReal p) volume := by
  rw [nearPart, memLp_indicator_iff_restrict measurableSet_ball.nullMeasurableSet]
  apply (integrable_norm_rpow_iff hk.restrict (by positivity) (by simp)).mp
  have hint : IntegrableOn (fun z : Space => ‖k z‖ ^ p) (Metric.ball 0 1) volume := by
    apply integrableOn_ball_of_norm_le_rpow
      (C := C ^ p) (α := -(β * p)) (by simp [Space])
      (by simp only [Space, finrank_euclideanSpace_fin, Nat.cast_ofNat]; linarith)
    · filter_upwards [] with z
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _),
        hnorm, Real.mul_rpow hC (Real.rpow_nonneg (norm_nonneg z) β),
        ← Real.rpow_mul (norm_nonneg z)]
      simp only [neg_neg, le_refl]
    · exact (hk.norm.aemeasurable.pow_const p).aestronglyMeasurable
  simpa only [IntegrableOn, ENNReal.toReal_ofReal hp.le] using hint

theorem near_rieszKernel_memLp_two {α c : ℝ} (hα2 : 2 ≤ α) (hc : 0 < c) :
    MemLp (nearPart (rieszKernel α c)) 2 volume := by
  have h := nearPart_memLp_of_norm_rpow
    (rieszKernel_measurable α c).aestronglyMeasurable hc.le
    (by norm_num : (0 : ℝ) < 2) (by nlinarith : -3 < (α - 3) * 2)
    (rieszKernel_norm hc)
  simpa only [ENNReal.ofReal_ofNat] using h

theorem near_rieszKernelGradient_memLp_six_fifths {α c : ℝ}
    (hα2 : 2 ≤ α) (hα3 : α < 3) (hc : 0 < c) :
    MemLp (nearPart (rieszKernelGradient α c)) (ENNReal.ofReal (6 / 5 : ℝ)) volume := by
  exact nearPart_memLp_of_norm_rpow
    (rieszKernelGradient_measurable α c).aestronglyMeasurable
    (mul_nonneg hc.le (by linarith)) (by norm_num)
    (by nlinarith : -3 < (α - 4) * (6 / 5 : ℝ))
    (rieszKernelGradient_norm hα3 hc)

section LocalYoung
variable [NormedSpace ℝ E]

/-- Bounded kernels have literal convolution integrals at every spatial point. -/
theorem actualConvolution_integrable_of_bound {h : Space → ℝ} {k : Space → E} {C : ℝ}
    (hh : Integrable h volume) (hk : AEStronglyMeasurable k volume)
    (hC : ∀ z, ‖k z‖ ≤ C) (x : Space) :
    Integrable (fun y => h y • k (x - y)) volume := by
  apply (hh.norm.mul_const C).mono'
    (hh.aestronglyMeasurable.smul
      (hk.comp_measurePreserving (volume.measurePreserving_sub_left x)))
  filter_upwards [] with y
  change ‖h y • k (x-y)‖ ≤ ‖h y‖ * C
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_left (hC (x - y)) (norm_nonneg _)

theorem actualConvolution_norm_le_of_bound {h : Space → ℝ} {k : Space → E} {C : ℝ}
    (hh : Integrable h volume) (hC : ∀ z, ‖k z‖ ≤ C) (x : Space) :
    ‖actualConvolution h k x‖ ≤ C * ∫ y, ‖h y‖ := by
  calc
    _ ≤ ∫ y, ‖h y‖ * C := by
      apply norm_integral_le_of_norm_le (hh.norm.mul_const C)
      filter_upwards [] with y
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_left (hC (x - y)) (norm_nonneg _)
    _ = _ := by rw [integral_mul_const, mul_comm]

/-- The same literal convolution splits a.e. into its two actual integrals. -/
theorem actualConvolution_near_far_ae {h : Space → ℝ} {k : Space → E} {C : ℝ}
    (hh : Integrable h volume) (hnear : Integrable (nearPart k) volume)
    (hfar : AEStronglyMeasurable (farPart k) volume)
    (hC : ∀ z, ‖farPart k z‖ ≤ C) :
    actualConvolution h k =ᵐ[volume]
      fun x => actualConvolution h (nearPart k) x + actualConvolution h (farPart k) x := by
  have hn : ∀ᵐ x ∂volume, Integrable (fun y => h y • nearPart k (x - y)) volume :=
    hh.ae_convolution_exists (ContinuousLinearMap.lsmul ℝ ℝ) hnear
  filter_upwards [hn] with x hx
  have hf := actualConvolution_integrable_of_bound hh hfar hC x
  unfold actualConvolution
  rw [← integral_add hx hf]
  apply integral_congr_ae
  filter_upwards [] with y
  rw [← smul_add, nearPart_add_farPart]

variable [CompleteSpace E]
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate q p]

include q in
/-- A proved near Lp kernel plus a bounded far tail gives the local Lp domain.
The conclusion is on every finite-measure set, and uses one actual representative. -/
theorem actualConvolution_memLp_restrict_of_near_far (hp : p ≠ ∞)
    {h : Space → ℝ} {k : Space → E} {C : ℝ}
    (hh : Integrable h volume) (hnear1 : Integrable (nearPart k) volume)
    (hnearp : MemLp (nearPart k) p volume)
    (hfar : AEStronglyMeasurable (farPart k) volume)
    (hC : ∀ z, ‖farPart k z‖ ≤ C)
    (s : Set Space) (hμs : volume s < ∞) :
    MemLp (actualConvolution h k) p (volume.restrict s) := by
  let : Fact (volume s < ∞) := ⟨hμs⟩
  have hn := actualConvolution_memLp (q := q) hp hh hnear1 hnearp
  have hmf : AEStronglyMeasurable (actualConvolution h (farPart k)) volume :=
    hh.aestronglyMeasurable.convolution (ContinuousLinearMap.lsmul ℝ ℝ) hfar
  have hf : MemLp (actualConvolution h (farPart k)) p (volume.restrict s) :=
    MemLp.of_bound hmf.restrict (C * ∫ y, ‖h y‖)
      (ae_restrict_of_ae (Eventually.of_forall (actualConvolution_norm_le_of_bound hh hC)))
  exact ((hn.restrict s).add hf).ae_eq
    (ae_restrict_of_ae (actualConvolution_near_far_ae hh hnear1 hfar hC).symm)
end LocalYoung

/-- Potential orientation is identified exactly, with no replacement of the kernel. -/
theorem rieszConvolution_eq_actualConvolution (α c : ℝ) (h : Space → ℝ) :
    rieszConvolution α c h = actualConvolution h (rieszKernel α c) := by
  funext x
  unfold rieszConvolution actualConvolution
  apply integral_congr_ae
  filter_upwards [] with y
  simp only [smul_eq_mul, mul_comm]

/-- Local L2 domain of the actual Riesz potential of a real L1 forcing density. -/
theorem rieszConvolution_memLp_two_restrict {α c : ℝ} {h : Space → ℝ}
    (hα2 : 2 ≤ α) (hα3 : α < 3) (hc : 0 < c) (hh : Integrable h volume)
    (s : Set Space) (hμs : volume s < ∞) :
    MemLp (rieszConvolution α c h) 2 (volume.restrict s) := by
  rw [rieszConvolution_eq_actualConvolution]
  exact actualConvolution_memLp_restrict_of_near_far (p := 2) (q := 2) (by norm_num)
    hh (near_rieszKernel_integrable (by linarith)) (near_rieszKernel_memLp_two hα2 hc)
    (farPart_aestronglyMeasurable (rieszKernel_measurable α c).aestronglyMeasurable)
    (far_rieszKernel_norm_le hα3 hc) s hμs

/-- Local L6/5 domain of the frozen literal vector gradient integral. -/
theorem gradientConvolution_memLp_six_fifths_restrict {α c : ℝ} {h : Space → ℝ}
    (hα2 : 2 ≤ α) (hα3 : α < 3) (hc : 0 < c) (hh : Integrable h volume)
    (s : Set Space) (hμs : volume s < ∞) :
    MemLp (gradientConvolution α c h) (ENNReal.ofReal (6 / 5 : ℝ)) (volume.restrict s) := by
  let : Fact ((1 : ℝ≥0∞) ≤ 6) := ⟨by norm_num⟩
  let : Fact (1 ≤ ENNReal.ofReal (6 / 5 : ℝ)) := ⟨by norm_num⟩
  let : ENNReal.HolderConjugate 6 (ENNReal.ofReal (6 / 5 : ℝ)) := by
    have hh : Real.HolderConjugate 6 (6 / 5) := by constructor <;> norm_num
    simpa only [ENNReal.ofReal_ofNat] using hh.ennrealOfReal
  change MemLp (actualConvolution h (rieszKernelGradient α c)) _ _
  exact actualConvolution_memLp_restrict_of_near_far
    (p := ENNReal.ofReal (6 / 5 : ℝ)) (q := 6) (by simp)
    hh (near_rieszKernelGradient_integrable (by linarith) hα3 hc)
    (near_rieszKernelGradient_memLp_six_fifths hα2 hα3 hc)
    (farPart_aestronglyMeasurable (rieszKernelGradient_measurable α c).aestronglyMeasurable)
    (far_rieszKernelGradient_norm_le hα3 hc) s hμs

/-- Joint local-domain producer for the actual potential and actual gradient.
No weak-derivative assertion is hidden here; that is the separate compact-test transfer. -/
theorem actual_riesz_local_domains {α c : ℝ} {h : Space → ℝ}
    (hα2 : 2 ≤ α) (hα3 : α < 3) (hc : 0 < c) (hh : Integrable h volume)
    (s : Set Space) (hμs : volume s < ∞) :
    MemLp (rieszConvolution α c h) 2 (volume.restrict s) ∧
    MemLp (gradientConvolution α c h) (ENNReal.ofReal (6 / 5 : ℝ)) (volume.restrict s) :=
  ⟨rieszConvolution_memLp_two_restrict hα2 hα3 hc hh s hμs,
    gradientConvolution_memLp_six_fifths_restrict hα2 hα3 hc hh s hμs⟩

end HartreeF.RieszL1LocalDomains
