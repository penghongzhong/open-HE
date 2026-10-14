import DirectionalSixMajorants
import Mathlib.MeasureTheory.Integral.Prod
noncomputable section
set_option autoImplicit false
open MeasureTheory
namespace HartreeF.DerivativeMajorization
open ForcingDomain WeakHartreeChain

theorem rieszConvolution_aestronglyMeasurable (α c : ℝ)
    {f : Space → ℝ} (hf : AEStronglyMeasurable f volume) :
    AEStronglyMeasurable (rieszConvolution α c f) volume := by
  have hm : Measurable (fun p : Space × Space => rieszKernel α c (p.1-p.2)) :=
    measurable_const.mul ((measurable_fst.sub measurable_snd).norm.pow_const _)
  have hf2 : AEStronglyMeasurable (fun p : Space × Space => f p.2) (volume.prod volume) := hf.comp_snd
  exact (hm.aestronglyMeasurable.mul hf2).integral_prod_right'

theorem localFactorDerivative_action_measurable (q : ℝ)
    {u h : Space → ℂ} (hu : AEStronglyMeasurable u volume)
    (hh : AEStronglyMeasurable h volume) :
    AEStronglyMeasurable (fun x => localFactorDerivative q (u x) (h x)) volume := by
  have hdb := directionalDensity_measurable (q-3) hu hh
  change AEStronglyMeasurable (fun x => densityDerivative (3+(q-3)) (u x) (h x)) volume at hdb
  rw [show 3+(q-3)=q by ring] at hdb
  have ht := ((hu.norm.aemeasurable.pow_const q).aestronglyMeasurable.smul hh).add (hdb.smul hu)
  convert ht using 1
  funext x
  simp only [localFactorDerivative,add_apply,smul_apply,ContinuousLinearMap.id_apply,
    ContinuousLinearMap.smulRight_apply,Pi.add_apply,Pi.smul_apply']

theorem directionalCandidate_measurable (α c : ℝ)
    {u h : Space → ℂ} (hu : AEStronglyMeasurable u volume)
    (hh : AEStronglyMeasurable h volume) :
    AEStronglyMeasurable (directionalCandidate α c u h) volume := by
  have hD := rieszConvolution_aestronglyMeasurable α c (directionalDensity_measurable α hu hh)
  have hB := rieszConvolution_aestronglyMeasurable α c
    ((hu.norm.aemeasurable.pow_const (3+α)).aestronglyMeasurable)
  exact (hD.smul (ForcingDomain.localFactor_measurable α hu)).add
    (hB.smul (localFactorDerivative_action_measurable (1+α) hu hh))

#print axioms rieszConvolution_aestronglyMeasurable
#print axioms localFactorDerivative_action_measurable
#print axioms directionalCandidate_measurable
end HartreeF.DerivativeMajorization
