import WeakDirectionalStretch
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! Actual function-level continuity of the stationary test pairings.
Every L1 domain comes from the stated finite Lp domains; no integral continuity
or stationary self-test conclusion is an input. -/
noncomputable section
set_option autoImplicit false
open MeasureTheory Filter
open scoped Topology ENNReal RealInnerProductSpace
namespace HartreeF.StationaryPairing

theorem integral_inner_eq_toLp {G V : Space → Space}
    (hG : MemLp G 2 volume) (hV : MemLp V 2 volume) :
    (∫ x, ⟪G x, V x⟫ ∂volume) = ⟪hG.toLp G, hV.toLp V⟫ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hG.coeFn_toLp, hV.coeFn_toLp] with x hx hy
  rw [hx, hy]

theorem integral_inner_domain {G V : Space → Space}
    (hG : MemLp G 2 volume) (hV : MemLp V 2 volume) :
    Integrable (fun x => ⟪G x, V x⟫) volume := by
  apply (L2.integrable_inner (hG.toLp G) (hV.toLp V)).congr
  filter_upwards [hG.coeFn_toLp, hV.coeFn_toLp] with x hx hy
  rw [hx, hy]

theorem integral_inner_tendsto_of_eLpNorm {G V : Space → Space}
    {Vn : ℕ → Space → Space} (hG : MemLp G 2 volume)
    (hV : MemLp V 2 volume) (hn : ∀ n, MemLp (Vn n) 2 volume)
    (hconv : Tendsto (fun n => eLpNorm (Vn n - V) 2 volume) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, ⟪G x, Vn n x⟫ ∂volume) atTop
      (𝓝 (∫ x, ⟪G x, V x⟫ ∂volume)) := by
  have ht := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' Vn hn V hV).2 hconv
  have hc := ((innerSL ℝ (hG.toLp G)).continuous.tendsto (hV.toLp V)).comp ht
  change Tendsto (fun n => ⟪hG.toLp G, (hn n).toLp (Vn n)⟫) atTop
    (𝓝 ⟪hG.toLp G, hV.toLp V⟫) at hc
  have he : (fun n => ∫ x, ⟪G x, Vn n x⟫ ∂volume) =
      (fun n => ⟪hG.toLp G, (hn n).toLp (Vn n)⟫) := by
    funext n
    exact integral_inner_eq_toLp hG (hn n)
  rw [he, integral_inner_eq_toLp hG hV]
  exact hc

theorem integral_toLp_one_eq_actual {f : Space → ℝ} (hf : MemLp f 1 volume) :
    L1.integral (hf.toLp f) = ∫ x, f x ∂volume := by
  rw [L1.integral_eq_integral]
  exact integral_congr_ae hf.coeFn_toLp

/-- In particular use p=6/5 and q=6 for the actual Hartree forcing pairing. -/
theorem integral_mul_tendsto_of_eLpNorm {p q : ℝ≥0∞}
    [ENNReal.HolderTriple p q 1] {f v : Space → ℝ} {vn : ℕ → Space → ℝ}
    (hf : MemLp f p volume) (hv : MemLp v q volume)
    (hn : ∀ n, MemLp (vn n) q volume)
    (hconv : Tendsto (fun n => eLpNorm (vn n - v) q volume) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, f x * vn n x ∂volume) atTop
      (𝓝 (∫ x, f x * v x ∂volume)) := by
  have hm := ENNReal.Tendsto.const_mul (a := eLpNorm f p volume) hconv
    (Or.inr hf.eLpNorm_ne_top)
  simp only [mul_zero] at hm
  have hp : Tendsto (fun n => eLpNorm (fun x => f x * (vn n x - v x)) 1 volume)
      atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hm
      (fun _ => bot_le)
    intro n
    change eLpNorm (f • (vn n - v)) 1 volume ≤
      eLpNorm f p volume * eLpNorm (vn n - v) q volume
    exact eLpNorm_smul_le_mul_eLpNorm hf.aestronglyMeasurable
      ((hn n).sub hv).aestronglyMeasurable
  have hprod : MemLp (fun x => f x * v x) 1 volume := hf.mul hv
  have hprodn : ∀ n, MemLp (fun x => f x * vn n x) 1 volume := fun n => hf.mul (hn n)
  have he (n : ℕ) : ((fun x => f x * vn n x) - (fun x => f x * v x)) =
      (fun x => f x * (vn n x - v x)) := by
    funext x
    simp only [Pi.sub_apply]
    ring
  have hp' : Tendsto (fun n => eLpNorm ((fun x => f x * vn n x) -
      (fun x => f x * v x)) 1 volume) atTop (𝓝 0) := by simpa only [he] using hp
  have hLp := (Lp.tendsto_Lp_iff_tendsto_eLpNorm''
    (fun n x => f x * vn n x) hprodn (fun x => f x * v x) hprod).2 hp'
  have hc : Continuous (fun z : Lp ℝ 1 (volume : Measure Space) => L1.integral z) :=
    L1.continuous_integral
  have hi := (hc.tendsto (hprod.toLp (fun x => f x * v x))).comp hLp
  simpa only [Function.comp_def, integral_toLp_one_eq_actual] using hi

#print axioms integral_inner_eq_toLp
#print axioms integral_inner_domain
#print axioms integral_inner_tendsto_of_eLpNorm
#print axioms integral_toLp_one_eq_actual
#print axioms integral_mul_tendsto_of_eLpNorm
end HartreeF.StationaryPairing
