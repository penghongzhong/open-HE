import HartreeForcingDomain
import Mathlib.MeasureTheory.Integral.Prod

/-! Genuine absolute integrability of the physical two-point Hartree energy,
derived from the same ordinary HLS interface on L6 data. -/
noncomputable section
set_option autoImplicit false
open MeasureTheory
namespace HartreeF.PressureDomain

def rieszPairDensity (α c : ℝ) (f : Space → ℂ) (z : Space × Space) : ℝ :=
  rieszKernel α c (z.1-z.2) * powerDensity α f z.2 * powerDensity α f z.1

theorem rieszPairDensity_nonneg {α c : ℝ} (hc : 0 ≤ c) (f : Space → ℂ)
    (z : Space × Space) : 0 ≤ rieszPairDensity α c f z := by
  unfold rieszPairDensity rieszKernel powerDensity
  positivity

theorem rieszPairDensity_measurable {α c : ℝ} {f : Space → ℂ}
    (hf : AEStronglyMeasurable f volume) :
    AEStronglyMeasurable (rieszPairDensity α c f) (volume.prod volume) := by
  have hk : Measurable (fun z : Space × Space => rieszKernel α c (z.1-z.2)) := by
    exact measurable_const.mul
      (((continuous_fst.sub continuous_snd).norm.measurable).pow_const (α-3))
  have hb : AEStronglyMeasurable (powerDensity α f) volume :=
    (hf.norm.aemeasurable.pow_const (3+α)).aestronglyMeasurable
  exact (hk.aestronglyMeasurable.mul hb.comp_snd).mul hb.comp_fst

theorem rieszPairDensity_inner_integral (α c : ℝ) (f : Space → ℂ) (x : Space) :
    (∫ y, rieszPairDensity α c f (x,y)) =
      potential α c f x * powerDensity α f x := by
  unfold rieszPairDensity potential
  dsimp only
  rw [integral_mul_const]

theorem rieszPairDensity_integrable {α c : ℝ}
    (hHLS : ForcingDomain.OrdinaryHLS α c) {f : Space → ℂ}
    (hf : MemLp f 6 volume) :
    Integrable (rieszPairDensity α c f) (volume.prod volume) := by
  obtain ⟨C,hC⟩ := ForcingDomain.potential_domain_bound hHLS
  have hkernel := (hC f hf).1
  have hD := ForcingDomain.interaction_density_integrable hHLS hf
  apply (integrable_prod_iff (rieszPairDensity_measurable hf.aestronglyMeasurable)).mpr
  constructor
  · filter_upwards [hkernel] with x hx
    exact hx.mul_const (powerDensity α f x)
  · apply hD.congr
    filter_upwards [] with x
    have hn : ∀ y, ‖rieszPairDensity α c f (x,y)‖ = rieszPairDensity α c f (x,y) := by
      intro y
      rw [Real.norm_eq_abs, abs_of_nonneg
        (rieszPairDensity_nonneg hHLS.normalization_pos.le f (x,y))]
    simp_rw [hn]
    exact (rieszPairDensity_inner_integral α c f x).symm

theorem hartree_energy_pair_identity {α c : ℝ}
    (hHLS : ForcingDomain.OrdinaryHLS α c) {f : Space → ℂ}
    (hf : MemLp f 6 volume) :
    (∫ z, rieszPairDensity α c f z ∂volume.prod volume) =
      ∫ x, potential α c f x * powerDensity α f x := by
  rw [integral_prod _ (rieszPairDensity_integrable hHLS hf)]
  exact integral_congr_ae (Filter.Eventually.of_forall (rieszPairDensity_inner_integral α c f))

#print axioms rieszPairDensity_nonneg
#print axioms rieszPairDensity_measurable
#print axioms rieszPairDensity_inner_integral
#print axioms rieszPairDensity_integrable
#print axioms hartree_energy_pair_identity
end HartreeF.PressureDomain
