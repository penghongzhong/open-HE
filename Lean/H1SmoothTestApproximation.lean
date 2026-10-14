import RealSobolevApproximation

/-! Hunter's ordinary H1 density followed by a native Sobolev argument.
L6 convergence is a conclusion, and the interface is used only on true
inhomogeneous H1 inputs with their literal C11 weak gradients. -/
noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Set
open scoped RealInnerProductSpace ENNReal Topology
namespace HartreeF.StationarySelfTest
open SobolevStretch WeakCutoffLp

/-- Every actual real H1 function that is in L6 has genuine compact C-infinity
tests converging in both gradient L2 and function L6. The L6 approximation is
produced internally from ordinary Sobolev, not supplied by the density premise. -/
theorem h1_smooth_test_approximation (hDensity : OrdinaryH1Density)
    {K : ℝ} (hSob : OrdinarySobolev K) {v : Space → ℝ} {V : Space → Space}
    (hv2 : MemLp v 2 volume) (hv6 : MemLp v 6 volume) (hV : MemLp V 2 volume)
    (hw : HasWeakGradient v V) :
    ∃ φ : ℕ → Space → ℝ,
      (∀ n, ContDiff ℝ (⊤ : ℕ∞) (φ n) ∧ HasCompactSupport (φ n)) ∧
      (∀ n, MemLp (φ n) 6 volume ∧ MemLp (gradient (φ n)) 2 volume) ∧
      Tendsto (fun n => eLpNorm (fun x => φ n x - v x) 6 volume) atTop (𝓝 0) ∧
      Tendsto (fun n => eLpNorm (fun x => gradient (φ n) x - V x) 2 volume)
        atTop (𝓝 0) := by
  obtain ⟨φ, hφ, _, hgrad⟩ := hDensity.approximate v V hv2 hV hw
  have hm (n : ℕ) : MemLp (φ n) 6 volume ∧ MemLp (gradient (φ n)) 2 volume :=
    ⟨cutoff_memLp (hφ n).1.continuous (hφ n).2 _,
      cutoff_gradient_memLp (hφ n).1 (hφ n).2 _⟩
  refine ⟨φ, hφ, hm, ?_, hgrad⟩
  exact sobolev_eLpNorm_tendsto_zero hSob
    (fun n => (hm n).1.sub hv6) (fun n => (hm n).2.sub hV)
    (fun n => weakGradient_sub (smooth_hasWeakGradient (hφ n).1) hw) hgrad

#print axioms h1_smooth_test_approximation
end HartreeF.StationarySelfTest
