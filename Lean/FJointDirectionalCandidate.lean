import FJointRieszMeasurability
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace HartreeF.TimeHolder
open MeasureTheory ForcingDomain WeakHartreeChain DerivativeMajorization
open scoped ENNReal NNReal

theorem density_action_measurable {X : Type*} [MeasurableSpace X]
    (mu : Measure X) (p : ℝ) {u h : X → ℂ}
    (hu : AEStronglyMeasurable u mu) (hh : AEStronglyMeasurable h mu) :
    AEStronglyMeasurable (fun x => densityDerivative p (u x) (h x)) mu := by
  simp_rw [densityDerivative_apply]
  have hure := Complex.continuous_re.comp_aestronglyMeasurable hu
  have huim := Complex.continuous_im.comp_aestronglyMeasurable hu
  have hhre := Complex.continuous_re.comp_aestronglyMeasurable hh
  have hhim := Complex.continuous_im.comp_aestronglyMeasurable hh
  exact (aestronglyMeasurable_const.mul
    (hu.norm.aemeasurable.pow_const _).aestronglyMeasurable).mul
    ((hure.mul hhre).add (huim.mul hhim))

theorem local_factor_action_measurable {X : Type*} [MeasurableSpace X]
    (mu : Measure X) (q : ℝ) {u h : X → ℂ}
    (hu : AEStronglyMeasurable u mu) (hh : AEStronglyMeasurable h mu) :
    AEStronglyMeasurable (fun x => localFactorDerivative q (u x) (h x)) mu := by
  have hdb := density_action_measurable mu q hu hh
  have ht := ((hu.norm.aemeasurable.pow_const q).aestronglyMeasurable.smul hh).add
    (hdb.smul hu)
  convert ht using 1
  funext x
  simp only [localFactorDerivative, add_apply, smul_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.smulRight_apply, Pi.add_apply, Pi.smul_apply']

theorem joint_directional_candidate_measurable {T : Type*} [MeasurableSpace T]
    (mu : Measure T) [SigmaFinite mu] (alpha c : ℝ) (u h : T → Space → ℂ)
    (hu : AEStronglyMeasurable (fun z : T × Space => u z.1 z.2) (mu.prod volume))
    (hh : AEStronglyMeasurable (fun z : T × Space => h z.1 z.2) (mu.prod volume)) :
    AEStronglyMeasurable (fun z : T × Space =>
      directionalCandidate alpha c (u z.1) (h z.1) z.2) (mu.prod volume) := by
  have hD := joint_riesz_measurable mu alpha c
    (fun t => directionalDensity alpha (u t) (h t))
    (density_action_measurable (mu.prod volume) (3+alpha) hu hh)
  have hB := joint_riesz_measurable mu alpha c (fun t x => ‖u t x‖^(3+alpha))
    ((hu.norm.aemeasurable.pow_const (3+alpha)).aestronglyMeasurable)
  exact (hD.smul ((hu.norm.aemeasurable.pow_const (1+alpha)).aestronglyMeasurable.smul hu)).add
    (hB.smul (local_factor_action_measurable (mu.prod volume) (1+alpha) hu hh))

end HartreeF.TimeHolder
