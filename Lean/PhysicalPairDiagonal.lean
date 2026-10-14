import HeatRieszPointwise
import Mathlib.MeasureTheory.Integral.Prod

/-! The spatial diagonal is product-volume null. Therefore the off-diagonal
heat representation supplies a genuine a.e. identity, never a false pointwise
identity at the divergent heat-time integral on the zero diagonal. -/
noncomputable section
set_option autoImplicit false
open MeasureTheory
namespace HartreeF.HeatRiesz

theorem physical_pair_diagonal_null :
    (volume.prod volume) {q : Space × Space | q.1=q.2} = 0 := by
  rw [Measure.prod_apply (measurableSet_eq_fun measurable_fst measurable_snd)]
  have h : ∀ x : Space, volume ((Prod.mk x) ⁻¹' {q : Space × Space | q.1=q.2}) = 0 := by
    intro x
    have he : ((Prod.mk x) ⁻¹' {q : Space × Space | q.1=q.2}) = {x} := by
      ext y
      simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_singleton_iff]
      exact eq_comm
    rw [he, measure_singleton]
  simp_rw [h]
  simp

theorem physical_pair_difference_ne_zero_ae :
    ∀ᵐ q : Space × Space ∂volume.prod volume, q.1-q.2 ≠ 0 := by
  rw [ae_iff]
  simpa only [not_not, sub_eq_zero] using physical_pair_diagonal_null

theorem heatMixture_pair_eq_riesz_ae {α : ℝ} (hα3 : α < 3) :
    (fun q : Space × Space => ∫ t in Set.Ioi 0, heatMixtureIntegrand α (q.1-q.2) t) =ᵐ[volume.prod volume]
      (fun q => rieszKernel α (standardRieszConstant α) (q.1-q.2)) := by
  filter_upwards [physical_pair_difference_ne_zero_ae] with q hq
  exact heatMixture_eq_riesz_nonzero hα3 hq

theorem heatMixture_pair_integrable_time_ae {α : ℝ} (hα3 : α < 3) :
    ∀ᵐ q : Space × Space ∂volume.prod volume,
      IntegrableOn (heatMixtureIntegrand α (q.1-q.2)) (Set.Ioi 0) := by
  filter_upwards [physical_pair_difference_ne_zero_ae] with q hq
  exact heatMixture_integrable_nonzero hα3 hq

#print axioms physical_pair_diagonal_null
#print axioms physical_pair_difference_ne_zero_ae
#print axioms heatMixture_pair_eq_riesz_ae
#print axioms heatMixture_pair_integrable_time_ae
end HartreeF.HeatRiesz
