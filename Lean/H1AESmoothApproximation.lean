import WeakGradientClosure
import RealSobolevApproximation

/-! Native strengthening of the sole external ordinary H1 density input.
The output supplies actual compact C-infinity functions, their literal gradients,
strong function/gradient L2 convergence, and almost-everywhere convergence.
It introduces no chain-rule premise. Apply independently to Re u and Im u. -/
noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Set
open scoped RealInnerProductSpace ENNReal Topology
namespace HartreeF.ModulusGradient
open SobolevStretch StationarySelfTest WeakCutoffLp

structure H1AESmoothApproximation (u : Space → ℝ) (G : Space → Space) where
  seq : ℕ → Space → ℝ
  smooth : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (seq n)
  compact : ∀ n, HasCompactSupport (seq n)
  function_L2 : ∀ n, MemLp (seq n) 2 volume
  gradient_L2 : ∀ n, MemLp (gradient (seq n)) 2 volume
  weak : ∀ n, HasWeakGradient (seq n) (gradient (seq n))
  function_tendsto : Tendsto (fun n => eLpNorm (seq n - u) 2 volume) atTop (𝓝 0)
  gradient_tendsto : Tendsto (fun n => eLpNorm (gradient (seq n) - G) 2 volume) atTop (𝓝 0)
  ae_tendsto : ∀ᵐ x ∂volume, Tendsto (fun n => seq n x) atTop (𝓝 (u x))

theorem ordinary_h1_ae_smooth_approximation (hDensity : OrdinaryH1Density)
    {u : Space → ℝ} {G : Space → Space}
    (hu : MemLp u 2 volume) (hG : MemLp G 2 volume)
    (hw : HasWeakGradient u G) : Nonempty (H1AESmoothApproximation u G) := by
  obtain ⟨φ, hφ, hf, hg⟩ := hDensity.approximate u G hu hG hw
  obtain ⟨ns, hns, hae⟩ := exists_ae_subsequence_of_strong_l2 hf
  exact ⟨{
    seq := fun n => φ (ns n)
    smooth := fun n => (hφ (ns n)).1
    compact := fun n => (hφ (ns n)).2
    function_L2 := fun n => cutoff_memLp (hφ (ns n)).1.continuous (hφ (ns n)).2 2
    gradient_L2 := fun n => cutoff_gradient_memLp (hφ (ns n)).1 (hφ (ns n)).2 2
    weak := fun n => smooth_hasWeakGradient (hφ (ns n)).1
    function_tendsto := hf.comp hns.tendsto_atTop
    gradient_tendsto := hg.comp hns.tendsto_atTop
    ae_tendsto := hae }⟩

/-- An actual complex H1 input produces two genuine real smooth approximations,
with all domains and a.e. limits, from ordinary density only. -/
theorem complex_h1_ae_smooth_approximation (hDensity : OrdinaryH1Density)
    {u : Space → ℂ} {GRe GIm : Space → Space}
    (hu : MemLp u 2 volume) (hs : InDotH1 u GRe GIm) :
    Nonempty (H1AESmoothApproximation (fun x => (u x).re) GRe ×
      H1AESmoothApproximation (fun x => (u x).im) GIm) := by
  obtain ⟨a⟩ := ordinary_h1_ae_smooth_approximation hDensity
    (hu.continuousLinearMap_comp Complex.reCLM) hs.real_gradient_L2 hs.real_weak
  obtain ⟨b⟩ := ordinary_h1_ae_smooth_approximation hDensity
    (hu.continuousLinearMap_comp Complex.imCLM) hs.imag_gradient_L2 hs.imag_weak
  exact ⟨(a, b)⟩

#print axioms H1AESmoothApproximation
#print axioms ordinary_h1_ae_smooth_approximation
#print axioms complex_h1_ae_smooth_approximation
end HartreeF.ModulusGradient
