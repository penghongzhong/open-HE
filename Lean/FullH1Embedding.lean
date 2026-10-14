import H1AESmoothApproximation
import H1SmoothTestApproximation
import SharpOrdinaryInterfaces

/-!
Ordinary real H1 embeds into L6 on the actual F Euclidean space.
The input function has only L2 membership and a genuine L2 weak gradient.
Ordinary H1 density supplies a compact smooth sequence. Its strong gradient
L2 convergence yields an eventual uniform L6 bound by ordinary Sobolev.
An actual almost-everywhere subsequence and native Lp Fatou then produce the
original function's L6 membership. No target L6 membership is a premise.
-/
noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Set
open scoped RealInnerProductSpace ENNReal Topology
namespace HartreeF.FullH1Embedding
open SobolevStretch StationarySelfTest ModulusGradient WeakCutoffLp

/-- Strong L2 gradient convergence bounds the sixth norms of the actual
compactly supported smooth approximants. -/
theorem smooth_approximation_eventually_L6_bounded {K : ℝ}
    (hSob : OrdinarySobolev K) {u : Space → ℝ} {V : Space → Space}
    (hV : MemLp V 2 volume) (a : H1AESmoothApproximation u V) :
    ∃ C : ℝ≥0∞, C < ∞ ∧ ∀ᶠ n in atTop, eLpNorm (a.seq n) 6 volume ≤ C := by
  have hLp := (Lp.tendsto_Lp_iff_tendsto_eLpNorm''
    (fun n => gradient (a.seq n)) a.gradient_L2 V hV).2 a.gradient_tendsto
  have hb : ∀ᶠ n in atTop,
      ‖(a.gradient_L2 n).toLp (gradient (a.seq n))‖ ≤ ‖hV.toLp V‖ + 1 :=
    hLp.norm.eventually (ge_mem_nhds (by linarith : ‖hV.toLp V‖ < ‖hV.toLp V‖ + 1))
  let B : ℝ := K * ((‖hV.toLp V‖ + 1)^2)^3
  refine ⟨ENNReal.ofReal (B ^ (6 : ℝ)⁻¹), ENNReal.ofReal_lt_top, ?_⟩
  filter_upwards [hb] with n hn
  have hn6 : MemLp (a.seq n) 6 volume :=
    cutoff_memLp (a.smooth n).continuous (a.compact n) _
  have he : (∫ x, ‖gradient (a.seq n) x‖^2) ≤ (‖hV.toLp V‖ + 1)^2 := by
    rw [norm_moment_eq_eLpNorm (by decide : (2 : ℕ) ≠ 0) (a.gradient_L2 n)]
    rw [← Lp.norm_toLp]
    exact pow_le_pow_left₀ (norm_nonneg _) hn 2
  have h6 : (∫ x, ‖a.seq n x‖^6) ≤ B := by
    apply (real_sobolev_integral_bound hSob hn6 (a.gradient_L2 n) (a.weak n)).trans
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (integral_nonneg fun x => sq_nonneg _) he 3) hSob.nonneg
  rw [MemLp.eLpNorm_eq_integral_rpow_norm (by norm_num : (6 : ℝ≥0∞) ≠ 0)
    (by norm_num : (6 : ℝ≥0∞) ≠ ∞) hn6]
  norm_num only [ENNReal.toReal_ofNat, Real.rpow_ofNat]
  apply ENNReal.ofReal_le_ofReal
  exact Real.rpow_le_rpow (integral_nonneg fun x => pow_nonneg (norm_nonneg _) _) h6
    (by positivity)

/-- Genuine H1-to-L6 production by the ordinary approximation and Fatou
argument. The original function's L6 membership is not assumed. -/
theorem h1_memLp_six (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) {u : Space → ℝ} {V : Space → Space}
    (hu : MemLp u 2 volume) (hV : MemLp V 2 volume)
    (hw : HasWeakGradient u V) : MemLp u 6 volume := by
  obtain ⟨a⟩ := ordinary_h1_ae_smooth_approximation hDensity hu hV hw
  obtain ⟨C, hC, hb⟩ := smooth_approximation_eventually_L6_bounded hSob hV a
  exact (Lp.eLpNorm_le_of_ae_tendsto hb (fun n => (a.function_L2 n).aestronglyMeasurable)
    hu.aestronglyMeasurable a.ae_tendsto).trans_lt hC

/-- The ordinary inequality now applies to every real H1 datum, at the
unchanged constant, after the function's missing L6 domain is produced. -/
theorem h1_sobolev_bound (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) {u : Space → ℝ} {V : Space → Space}
    (hu : MemLp u 2 volume) (hV : MemLp V 2 volume)
    (hw : HasWeakGradient u V) :
    MemLp u 6 volume ∧ (∫ x, ‖u x‖^6) ≤ K * (∫ x, ‖V x‖^2)^3 := by
  have hu6 := h1_memLp_six hDensity hSob hu hV hw
  exact ⟨hu6, real_sobolev_integral_bound hSob hu6 hV hw⟩

/-- Exact sharp specialization from F's already scoped ordinary sharp
Sobolev interface. It still assumes no L6 membership of the H1 datum. -/
theorem h1_sharp_sobolev_bound (hDensity : OrdinaryH1Density)
    (hSharp : SharpOrdinary.SharpOrdinarySobolev)
    {u : Space → ℝ} {V : Space → Space}
    (hu : MemLp u 2 volume) (hV : MemLp V 2 volume)
    (hw : HasWeakGradient u V) :
    MemLp u 6 volume ∧ (∫ x, ‖u x‖^6) ≤
      SharpOrdinary.sharpSobolevSixth * (∫ x, ‖V x‖^2)^3 :=
  h1_sobolev_bound hDensity hSharp.ordinary hu hV hw

/-- One and the same ordinary H1 approximating sequence converges in L2,
L6, and gradient L2. This is a producer for subsequent polynomial moments. -/
theorem h1_full_smooth_approximation (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) {u : Space → ℝ} {V : Space → Space}
    (hu : MemLp u 2 volume) (hV : MemLp V 2 volume)
    (hw : HasWeakGradient u V) :
    ∃ φ : ℕ → Space → ℝ,
      (∀ n, ContDiff ℝ (⊤ : ℕ∞) (φ n) ∧ HasCompactSupport (φ n)) ∧
      (∀ n, MemLp (φ n) 2 volume ∧ MemLp (φ n) 6 volume ∧
        MemLp (gradient (φ n)) 2 volume ∧ HasWeakGradient (φ n) (gradient (φ n))) ∧
      Tendsto (fun n => eLpNorm (φ n - u) 2 volume) atTop (𝓝 0) ∧
      Tendsto (fun n => eLpNorm (φ n - u) 6 volume) atTop (𝓝 0) ∧
      Tendsto (fun n => eLpNorm (gradient (φ n) - V) 2 volume) atTop (𝓝 0) := by
  have hu6 := h1_memLp_six hDensity hSob hu hV hw
  obtain ⟨φ, hφ, h2, hgrad⟩ := hDensity.approximate u V hu hV hw
  have hm (n : ℕ) : MemLp (φ n) 2 volume ∧ MemLp (φ n) 6 volume ∧
      MemLp (gradient (φ n)) 2 volume ∧ HasWeakGradient (φ n) (gradient (φ n)) :=
    ⟨cutoff_memLp (hφ n).1.continuous (hφ n).2 _,
      cutoff_memLp (hφ n).1.continuous (hφ n).2 _,
      cutoff_gradient_memLp (hφ n).1 (hφ n).2 _, smooth_hasWeakGradient (hφ n).1⟩
  refine ⟨φ, hφ, hm, h2, ?_, hgrad⟩
  exact sobolev_eLpNorm_tendsto_zero hSob
    (fun n => (hm n).2.1.sub hu6) (fun n => (hm n).2.2.1.sub hV)
    (fun n => weakGradient_sub (hm n).2.2.2 hw) hgrad

#print axioms smooth_approximation_eventually_L6_bounded
#print axioms h1_memLp_six
#print axioms h1_sobolev_bound
#print axioms h1_sharp_sobolev_bound
#print axioms h1_full_smooth_approximation
end HartreeF.FullH1Embedding
