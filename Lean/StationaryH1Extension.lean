import H1SmoothTestApproximation
import StationaryPairingLimits

/-! Extension of the literal compact C-infinity weak equation to actual H1
functions. Both pairings converge by native Holder/Bochner arguments. -/
noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Set
open scoped RealInnerProductSpace ENNReal Topology
namespace HartreeF.StationarySelfTest
open SobolevStretch ForcingDomain

theorem weak_equation_extend_h1 (hDensity : OrdinaryH1Density)
    {K : ℝ} (hSob : OrdinarySobolev K) {G : Space → Space} {f : Space → ℝ}
    (hG : MemLp G 2 volume) (hf : MemLp f (ENNReal.ofReal (6 / 5 : ℝ)) volume)
    (heq : ∀ φ : Space → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      (∫ x, ⟪G x, gradient φ x⟫) = ∫ x, f x * φ x)
    {v : Space → ℝ} {V : Space → Space} (hv2 : MemLp v 2 volume)
    (hv6 : MemLp v 6 volume) (hV : MemLp V 2 volume) (hw : HasWeakGradient v V) :
    (∫ x, ⟪G x, V x⟫) = ∫ x, f x * v x := by
  obtain ⟨φ, hφ, hm, ht6, ht2⟩ :=
    h1_smooth_test_approximation hDensity hSob hv2 hv6 hV hw
  have hleft := inner_pairing_tendsto hG hV (fun n => (hm n).2) ht2
  have hright := forcing_pairing_tendsto hf hv6 (fun n => (hm n).1) ht6
  have hid : (fun n => ∫ x, ⟪G x, gradient (φ n) x⟫) =
      (fun n => ∫ x, f x * φ n x) := by
    funext n
    exact heq (φ n) (hφ n).1 (hφ n).2
  rw [← hid] at hright
  exact tendsto_nhds_unique hleft hright

theorem WeakStationary.test_real_h1 {α c : ℝ} {u : Space → ℂ}
    {GRe GIm : Space → Space} (h : WeakStationary α c u GRe GIm)
    (hHLS : OrdinaryHLS α c) (hDensity : OrdinaryH1Density)
    {K : ℝ} (hSob : OrdinarySobolev K) {v : Space → ℝ} {V : Space → Space}
    (hv2 : MemLp v 2 volume) (hv6 : MemLp v 6 volume) (hV : MemLp V 2 volume)
    (hw : HasWeakGradient v V) :
    (∫ x, ⟪GRe x, V x⟫) = ∫ x, (forcing α c u x).re * v x := by
  obtain ⟨C, hC⟩ := forcing_energy_domain_bound hHLS
  exact weak_equation_extend_h1 hDensity hSob h.sobolev.real_gradient_L2
    ((hC u h.sobolev.function_L6).1.continuousLinearMap_comp Complex.reCLM)
    h.real_equation hv2 hv6 hV hw

theorem WeakStationary.test_imag_h1 {α c : ℝ} {u : Space → ℂ}
    {GRe GIm : Space → Space} (h : WeakStationary α c u GRe GIm)
    (hHLS : OrdinaryHLS α c) (hDensity : OrdinaryH1Density)
    {K : ℝ} (hSob : OrdinarySobolev K) {v : Space → ℝ} {V : Space → Space}
    (hv2 : MemLp v 2 volume) (hv6 : MemLp v 6 volume) (hV : MemLp V 2 volume)
    (hw : HasWeakGradient v V) :
    (∫ x, ⟪GIm x, V x⟫) = ∫ x, (forcing α c u x).im * v x := by
  obtain ⟨C, hC⟩ := forcing_energy_domain_bound hHLS
  exact weak_equation_extend_h1 hDensity hSob h.sobolev.imag_gradient_L2
    ((hC u h.sobolev.function_L6).1.continuousLinearMap_comp Complex.imCLM)
    h.imag_equation hv2 hv6 hV hw

#print axioms weak_equation_extend_h1
#print axioms WeakStationary.test_real_h1
#print axioms WeakStationary.test_imag_h1
end HartreeF.StationarySelfTest
