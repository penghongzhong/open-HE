import HartreeLocalFactorWeakEndpoint
import HartreeGradientSingle

/-! The actual density gradient has the paper's E6/S10 split HLS input domain.
This is separate from the weaker exponent used only to identify weak derivatives. -/
noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal RealInnerProductSpace
namespace HartreeF.WeakHartreeChain
open SobolevStretch GradientMajorants

theorem densityGradient_norm_bound {p : ℝ} (hp : 1 < p)
    (u : Space → ℂ) (U V : Space → Space) (x : Space) :
    ‖densityGradient p u U V x‖ ≤ p*(‖u x‖^(p-1)*(‖U x‖+‖V x‖)) := by
  have he (e : ℂ) (hne : ‖e‖ = 1) := densityDerivative_component_bound hp (u x) e hne
  calc
    _ ≤ ‖densityDerivative p (u x) 1 • U x‖+‖densityDerivative p (u x) Complex.I • V x‖ := norm_add_le _ _
    _ ≤ (p*‖u x‖^(p-1))*‖U x‖+(p*‖u x‖^(p-1))*‖V x‖ := by
      simp only [norm_smul]
      exact add_le_add (mul_le_mul_of_nonneg_right (he 1 (by simp)) (norm_nonneg _))
        (mul_le_mul_of_nonneg_right (he Complex.I (by simp)) (norm_nonneg _))
    _ = _ := by ring

theorem hartreeDensityGradient_split_memLp {α : ℝ} (hα : 0 < α) (hα3 : α < 3)
    {u : Space → ℂ} {U V : Space → Space} (hu6 : MemLp u 6 volume)
    (hu10 : MemLp u 10 volume)
    (hU : MemLp U (ENNReal.ofReal (30/13 : ℝ)) volume)
    (hV : MemLp V (ENNReal.ofReal (30/13 : ℝ)) volume) :
    MemLp (hartreeDensityGradient α u U V) (ENNReal.ofReal (1/reciprocalB α)) volume := by
  have hb := second_density_bound hα hα3 (fun x => norm_nonneg (u x)) hu6.norm hu10.norm (hU.norm.add hV.norm)
  apply (hb.memLp.const_mul (3+α)).of_le
    (hartreeDensityGradient_memLp hα hu10 hU hV).aestronglyMeasurable
  filter_upwards [] with x
  rw [hartreeDensityGradient_eq]
  have he : 3+α-1 = 2+α := by ring
  have hh := densityGradient_norm_bound (by linarith : 1 < 3+α) u U V x
  rw [he] at hh
  have hn : 0 ≤ (3+α)*(‖u x‖^(2+α)*(‖U x‖+‖V x‖)) := by positivity
  simpa only [Pi.add_apply,Real.norm_eq_abs,abs_of_nonneg hn] using hh

theorem hartree_density_directional_split_memLp {α : ℝ} (hα : 0 < α) (hα3 : α < 3)
    {u : Space → ℂ} {U V : Space → Space} (hu6 : MemLp u 6 volume)
    (hu10 : MemLp u 10 volume)
    (hU : MemLp U (ENNReal.ofReal (30/13 : ℝ)) volume)
    (hV : MemLp V (ENNReal.ofReal (30/13 : ℝ)) volume) (v : Space) :
    MemLp (fun x => ⟪hartreeDensityGradient α u U V x,v⟫)
      (ENNReal.ofReal (1/reciprocalB α)) volume := by
  have hm := (innerSL ℝ v).comp_memLp' (hartreeDensityGradient_split_memLp hα hα3 hu6 hu10 hU hV)
  simpa only [Function.comp_def,innerSL_apply_apply,real_inner_comm v] using hm

/-- Literal directional Riesz integrals of the actual density gradient have
strong-HLS domains. This does not identify them as derivatives of the potential. -/
theorem hartree_density_gradient_convolution_domain {α c : ℝ}
    (hH : ForcingDomain.OrdinaryHLS α c)
    {u : Space → ℂ} {U V : Space → Space} (hu6 : MemLp u 6 volume)
    (hu10 : MemLp u 10 volume)
    (hU : MemLp U (ENNReal.ofReal (30/13 : ℝ)) volume)
    (hV : MemLp V (ENNReal.ofReal (30/13 : ℝ)) volume) (v : Space) :
    RieszDomain α c (fun x => ⟪hartreeDensityGradient α u U V x,v⟫) ∧
    MemLp (ForcingDomain.rieszConvolution α c
      (fun x => ⟪hartreeDensityGradient α u U V x,v⟫))
      (ENNReal.ofReal (1/(reciprocalB α-α/3))) volume := by
  have hrs := gradient_hls_ranges hH.order_pos hH.order_lt_three
  obtain ⟨hr1,hrα,hrout,hrel⟩ := reciprocal_hls_range hH.order_pos hrs.2.2.1 hrs.2.2.2
  obtain ⟨C,hC⟩ := hH.strong_bound _ _ hr1 hrα hrout hrel
  have hd := hC _ (hartree_density_directional_split_memLp hH.order_pos hH.order_lt_three hu6 hu10 hU hV v)
  exact ⟨hd.1,hd.2.1⟩

#print axioms densityGradient_norm_bound
#print axioms hartreeDensityGradient_split_memLp
#print axioms hartree_density_directional_split_memLp
#print axioms hartree_density_gradient_convolution_domain
end HartreeF.WeakHartreeChain
