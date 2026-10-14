import StationaryH1Extension
import CutoffConvergence

/-!
Actual self-testing from the original compact smooth distribution equation.
The proof first localizes with explicitly scaled cutoffs, which creates true
H1 tests even when the original function is not L2; uses ordinary H1 density
and the internally proved Sobolev/Holder limits; then removes the cutoff using
the actual L6 and full product-gradient L2 approximation producers.
-/
noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Set
open scoped RealInnerProductSpace ENNReal Topology
namespace HartreeF.StationarySelfTest
open SobolevStretch ForcingDomain WeakCutoffLp CutoffApproximation

/-- Produced extension to the full real homogeneous Sobolev test domain.
Only the literal compact smooth test equation is a hypothesis. -/
theorem weak_equation_extend_dotH1 (hDensity : OrdinaryH1Density)
    {K : ℝ} (hSob : OrdinarySobolev K) {G : Space → Space} {f : Space → ℝ}
    (hG : MemLp G 2 volume) (hf : MemLp f (ENNReal.ofReal (6 / 5 : ℝ)) volume)
    (heq : ∀ φ : Space → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      (∫ x, ⟪G x, gradient φ x⟫) = ∫ x, f x * φ x)
    {v : Space → ℝ} {V : Space → Space}
    (hv6 : MemLp v 6 volume) (hV : MemLp V 2 volume) (hw : HasWeakGradient v V) :
    (∫ x, ⟪G x, V x⟫) = ∫ x, f x * v x := by
  let vn : ℕ → Space → ℝ := fun n x => cutoff n x * v x
  let Vn : ℕ → Space → Space := fun n x =>
    cutoff n x • V x + v x • gradient (cutoff n) x
  have hvn2 (n : ℕ) : MemLp (vn n) 2 volume :=
    cutoff_smul_memLp_two (cutoff_smooth n).continuous (cutoff_compact n) hv6
  have hvn6 (n : ℕ) : MemLp (vn n) 6 volume :=
    cutoff_smul_memLp (cutoff_smooth n).continuous (cutoff_compact n) hv6
  have hVn (n : ℕ) : MemLp (Vn n) 2 volume :=
    (cutoff_gradient_field_memLp_two (cutoff_smooth n).continuous (cutoff_compact n) hV).add
      (function_smul_cutoff_gradient_memLp_two (cutoff_smooth n) (cutoff_compact n) hv6)
  have hwn (n : ℕ) : HasWeakGradient (vn n) (Vn n) := hw.mul_smooth (cutoff_smooth n)
  have hid : (fun n => ∫ x, ⟪G x, Vn n x⟫) = (fun n => ∫ x, f x * vn n x) := by
    funext n
    exact weak_equation_extend_h1 hDensity hSob hG hf heq (hvn2 n) (hvn6 n) (hVn n) (hwn n)
  have hleft := inner_pairing_tendsto hG hV hVn (cutoff_full_gradient_tendsto_zero hv6 hV)
  have ht6 : Tendsto (fun n => eLpNorm (fun x => vn n x - v x) 6 volume) atTop (𝓝 0) :=
    cutoff_eLpNorm_tendsto_zero hv6 (by norm_num) (by norm_num)
  have hright := forcing_pairing_tendsto hf hv6 hvn6 ht6
  rw [← hid] at hright
  exact tendsto_nhds_unique hleft hright

theorem WeakStationary.real_self_test {α c : ℝ} {u : Space → ℂ}
    {GRe GIm : Space → Space} (h : WeakStationary α c u GRe GIm)
    (hHLS : OrdinaryHLS α c) (hDensity : OrdinaryH1Density)
    {K : ℝ} (hSob : OrdinarySobolev K) :
    (∫ x, ‖GRe x‖ ^ 2) = ∫ x, (forcing α c u x).re * (u x).re := by
  obtain ⟨C, hC⟩ := forcing_energy_domain_bound hHLS
  have ht := weak_equation_extend_dotH1 hDensity hSob h.sobolev.real_gradient_L2
    ((hC u h.sobolev.function_L6).1.continuousLinearMap_comp Complex.reCLM)
    h.real_equation (h.sobolev.function_L6.continuousLinearMap_comp Complex.reCLM)
    h.sobolev.real_gradient_L2 h.sobolev.real_weak
  simpa only [real_inner_self_eq_norm_sq, Complex.reCLM_apply, Complex.imCLM_apply] using ht

theorem WeakStationary.imag_self_test {α c : ℝ} {u : Space → ℂ}
    {GRe GIm : Space → Space} (h : WeakStationary α c u GRe GIm)
    (hHLS : OrdinaryHLS α c) (hDensity : OrdinaryH1Density)
    {K : ℝ} (hSob : OrdinarySobolev K) :
    (∫ x, ‖GIm x‖ ^ 2) = ∫ x, (forcing α c u x).im * (u x).im := by
  obtain ⟨C, hC⟩ := forcing_energy_domain_bound hHLS
  have ht := weak_equation_extend_dotH1 hDensity hSob h.sobolev.imag_gradient_L2
    ((hC u h.sobolev.function_L6).1.continuousLinearMap_comp Complex.imCLM)
    h.imag_equation (h.sobolev.function_L6.continuousLinearMap_comp Complex.imCLM)
    h.sobolev.imag_gradient_L2 h.sobolev.imag_weak
  simpa only [real_inner_self_eq_norm_sq, Complex.reCLM_apply, Complex.imCLM_apply] using ht

/-- Genuine Nehari identity for every actual weak stationary solution. No
stationary-specific approximation, self-testing, or Nehari premise is used. -/
theorem WeakStationary.kinetic_eq_hartree {α c : ℝ} {u : Space → ℂ}
    {GRe GIm : Space → Space} (h : WeakStationary α c u GRe GIm)
    (hHLS : OrdinaryHLS α c) (hDensity : OrdinaryH1Density)
    {K : ℝ} (hSob : OrdinarySobolev K) :
    kinetic GRe GIm = ∫ x, potential α c u x * powerDensity α u x := by
  obtain ⟨C, hC⟩ := forcing_energy_domain_bound hHLS
  have hf := (hC u h.sobolev.function_L6).1
  have hr := forcing_pairing_integrable (hf.continuousLinearMap_comp Complex.reCLM)
    (h.sobolev.function_L6.continuousLinearMap_comp Complex.reCLM)
  have hi := forcing_pairing_integrable (hf.continuousLinearMap_comp Complex.imCLM)
    (h.sobolev.function_L6.continuousLinearMap_comp Complex.imCLM)
  simp only [Complex.reCLM_apply, Complex.imCLM_apply] at hr hi
  rw [kinetic_eq_sum h.sobolev.real_gradient_L2 h.sobolev.imag_gradient_L2,
    h.real_self_test hHLS hDensity hSob, h.imag_self_test hHLS hDensity hSob,
    ← integral_add hr hi]
  apply integral_congr_ae
  filter_upwards [] with x
  have hg := congrArg Complex.re (forcing_gauge_pair (c := c) hHLS.order_pos u x)
  simpa only [Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im,
    mul_neg, sub_neg_eq_add, Complex.ofReal_re] using hg

/-- The exact interaction definition used by the sharp-threshold chain. -/
theorem WeakStationary.kinetic_eq_interaction {α : ℝ} {u : Space → ℂ}
    {GRe GIm : Space → Space}
    (h : WeakStationary α (HeatRiesz.standardRieszConstant α) u GRe GIm)
    (hHLS : OrdinaryHLS α (HeatRiesz.standardRieszConstant α))
    (hDensity : OrdinaryH1Density) {K : ℝ} (hSob : OrdinarySobolev K) :
    kinetic GRe GIm = DirectionalCoercivity.interaction α u :=
  h.kinetic_eq_hartree hHLS hDensity hSob

/-- Exact stationary energy formula used to compare genuine stationary states. -/
theorem WeakStationary.energy_eq_thresholdEnergy {α : ℝ} {u : Space → ℂ}
    {GRe GIm : Space → Space}
    (h : WeakStationary α (HeatRiesz.standardRieszConstant α) u GRe GIm)
    (hHLS : OrdinaryHLS α (HeatRiesz.standardRieszConstant α))
    (hDensity : OrdinaryH1Density) {K : ℝ} (hSob : OrdinarySobolev K) :
    DirectionalCoercivity.energy α u GRe GIm =
      DirectionalCoercivity.thresholdEnergy α (kinetic GRe GIm) := by
  unfold DirectionalCoercivity.energy DirectionalCoercivity.thresholdEnergy
  rw [← h.kinetic_eq_interaction hHLS hDensity hSob]
  have hα : 3 + α ≠ 0 := ne_of_gt (by linarith [hHLS.order_pos])
  field_simp [hα]
  ring

#print axioms weak_equation_extend_dotH1
#print axioms WeakStationary.real_self_test
#print axioms WeakStationary.imag_self_test
#print axioms WeakStationary.kinetic_eq_hartree
#print axioms WeakStationary.kinetic_eq_interaction
#print axioms WeakStationary.energy_eq_thresholdEnergy
end HartreeF.StationarySelfTest
