import FActualAffineSourceWeakGradients
import FEnergyCriticalTimeConsumer

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
open MeasureTheory
open scoped ENNReal RealInnerProductSpace
namespace HartreeF.AffineForcingIndependentReview
open CriticalAffine AffineForcing EnergySpace ForcingDomain SobolevStretch StationarySelfTest
open WeakHartreeProduct CriticalTimeSobolev LocalScalarSource

/-- The existing actual real forcing-gradient formula on this canonical state. -/
def canonicalForcingGradientRe (alpha c : ℝ) (u : EnergyState) : Space → Space :=
  forcingGradientRe alpha c (energyValue u) (energyProjectedGradient Complex.reCLM u)
    (energyProjectedGradient Complex.imCLM u)

/-- The existing actual imaginary forcing-gradient formula on this canonical state. -/
def canonicalForcingGradientIm (alpha c : ℝ) (u : EnergyState) : Space → Space :=
  forcingGradientIm alpha c (energyValue u) (energyProjectedGradient Complex.reCLM u)
    (energyProjectedGradient Complex.imCLM u)

/-- The same transformed canonical EnergyState has the pulled-back weak forcing
source, in genuine L6/5 scalar and vector domains. No source EnergyState or
scalar-time2 premise is introduced. -/
theorem affineState_canonical_weak_forcing (hDensity : OrdinaryH1Density)
    {K : ℝ} (hSob : OrdinarySobolev K) {alpha c : ℝ} (hH : OrdinaryHLS alpha c)
    (u : EnergyState) (hu10 : MemLp (energyValue u) 10 volume)
    (hU : MemLp (energyProjectedGradient Complex.reCLM u) (ENNReal.ofReal (30/13:ℝ)) volume)
    (hV : MemLp (energyProjectedGradient Complex.imCLM u) (ENNReal.ofReal (30/13:ℝ)) volume)
    {a : ℝ} (ha : 0<a) (b : Space) :
    (forcing alpha c (energyValue (affineState ha b u)) =ᵐ[volume]
      (fun x => a^(5/2:ℝ) • forcing alpha c (energyValue u) (affine a b x))) ∧
    HasWeakGradient (fun x => (forcing alpha c (energyValue (affineState ha b u)) x).re)
      (fun x => a^(7/2:ℝ) • canonicalForcingGradientRe alpha c u (affine a b x)) ∧
    HasWeakGradient (fun x => (forcing alpha c (energyValue (affineState ha b u)) x).im)
      (fun x => a^(7/2:ℝ) • canonicalForcingGradientIm alpha c u (affine a b x)) ∧
    MemLp (forcing alpha c (energyValue (affineState ha b u))) (ENNReal.ofReal (6/5:ℝ)) volume ∧
    MemLp (fun x => a^(7/2:ℝ) • canonicalForcingGradientRe alpha c u (affine a b x))
      (ENNReal.ofReal (6/5:ℝ)) volume ∧
    MemLp (fun x => a^(7/2:ℝ) • canonicalForcingGradientIm alpha c u (affine a b x))
      (ENNReal.ofReal (6/5:ℝ)) volume := by
  have hw := forcing_affine_weak_gradients hDensity hSob hH (energyState_inDotH1 u)
    hu10 hU hV ha b
  have hae := forcing_ae_of_ae (alpha := alpha) (c := c) (affineState_value_ae ha b u)
  refine ⟨affineState_forcing_ae alpha c ha b u, ?_, ?_, ?_, hw.2.2.2.1, hw.2.2.2.2⟩
  · exact weakGradient_congr_fields hw.1
      (hae.symm.mono (fun _ hx => congrArg Complex.re hx)) (Filter.EventuallyEq.rfl)
  · exact weakGradient_congr_fields hw.2.1
      (hae.symm.mono (fun _ hx => congrArg Complex.im hx)) (Filter.EventuallyEq.rfl)
  · exact (memLp_congr_ae hae.symm).mp hw.2.2.1

/-- Paper-length specialization on the same original and transformed canonical
states: scalar amplitude lambda^(-5/2), weak-gradient amplitude lambda^(-7/2). -/
theorem criticalAffineState_canonical_weak_forcing (hDensity : OrdinaryH1Density)
    {K : ℝ} (hSob : OrdinarySobolev K) {alpha c : ℝ} (hH : OrdinaryHLS alpha c)
    (u : EnergyState) (hu10 : MemLp (energyValue u) 10 volume)
    (hU : MemLp (energyProjectedGradient Complex.reCLM u) (ENNReal.ofReal (30/13:ℝ)) volume)
    (hV : MemLp (energyProjectedGradient Complex.imCLM u) (ENNReal.ofReal (30/13:ℝ)) volume)
    (lambda : ℝ) (hlambda : 0<lambda) (y : Space) :
    (forcing alpha c (energyValue (criticalAffineState lambda hlambda y u)) =ᵐ[volume]
      (fun x => lambda^(-(5/2:ℝ)) • forcing alpha c (energyValue u) (lambda⁻¹ • (x-y)))) ∧
    HasWeakGradient (fun x => (forcing alpha c (energyValue (criticalAffineState lambda hlambda y u)) x).re)
      (fun x => lambda^(-(7/2:ℝ)) • canonicalForcingGradientRe alpha c u (lambda⁻¹ • (x-y))) ∧
    HasWeakGradient (fun x => (forcing alpha c (energyValue (criticalAffineState lambda hlambda y u)) x).im)
      (fun x => lambda^(-(7/2:ℝ)) • canonicalForcingGradientIm alpha c u (lambda⁻¹ • (x-y))) ∧
    MemLp (forcing alpha c (energyValue (criticalAffineState lambda hlambda y u)))
      (ENNReal.ofReal (6/5:ℝ)) volume ∧
    MemLp (fun x => lambda^(-(7/2:ℝ)) • canonicalForcingGradientRe alpha c u (lambda⁻¹ • (x-y)))
      (ENNReal.ofReal (6/5:ℝ)) volume ∧
    MemLp (fun x => lambda^(-(7/2:ℝ)) • canonicalForcingGradientIm alpha c u (lambda⁻¹ • (x-y)))
      (ENNReal.ofReal (6/5:ℝ)) volume := by
  have h := affineState_canonical_weak_forcing hDensity hSob hH u hu10 hU hV
    (inv_pos.mpr hlambda) (-(lambda⁻¹ • y))
  have he : criticalAffineState lambda hlambda y u =
      affineState (inv_pos.mpr hlambda) (-(lambda⁻¹ • y)) u := rfl
  rw [he]
  simpa only [affine, Real.inv_rpow hlambda.le,
    Real.rpow_neg hlambda.le, sub_eq_add_neg, smul_add, smul_neg] using h

#print axioms canonicalForcingGradientRe
#print axioms canonicalForcingGradientIm
#print axioms affineState_canonical_weak_forcing
#print axioms criticalAffineState_canonical_weak_forcing
end HartreeF.AffineForcingIndependentReview
