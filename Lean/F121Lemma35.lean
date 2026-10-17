import FActualMaximalAffineCovariance
import FCriticalAffineEnergy
import FCriticalAffineMixedNorms

/-! Literal terminal wrapper for Lemma 3.5 of the 121-page manuscript.
It uses the paper's forward scale `r`: the state transform has amplitude
`r^(-1/2)`, time is pulled back by `(t-tau)/r^2`, and the transformed maximal
domain is exactly the forward image `tau+r^2 I`.  The same wrapper records
energy and all four displayed critical mixed-norm identities E, W, Z and S. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000
open MeasureTheory Set
open scoped ENNReal
namespace HartreeF.Paper121Lemma35
open EnergySpace TimeHolder SobolevStretch StationarySelfTest Retarded
open ActualStrichartz EndpointOutput ForcingDomain MaximalTrajectory
open CriticalAffine AffineMixed MaximalAffine StateEnergy

/-- The paper's state transform `T_(r,y)`, represented canonically in the
homogeneous energy space. -/
def paperAffineState {r : ℝ} (hr : 0 < r) (y : Space) (f : EnergyState) : EnergyState :=
  affineState (inv_pos.mpr hr) (-(r⁻¹) • y) f

theorem paperAffineState_value_ae {r : ℝ} (hr : 0 < r) (y : Space)
    (f : EnergyState) :
    (energyValue (paperAffineState hr y f) : Space → ℂ) =ᵐ[volume]
      fun x ↦ r^(-(1/2 : ℝ)) • energyValue f (r⁻¹ • (x-y)) := by
  refine (affineState_value_ae (inv_pos.mpr hr) (-(r⁻¹) • y) f).trans ?_
  filter_upwards with x
  unfold valuePullback
  have hx : affine r⁻¹ (-(r⁻¹) • y) x = r⁻¹ • (x-y) := by
    simp only [affine, smul_sub, neg_smul]
    abel
  rw [hx, Real.sqrt_eq_rpow, Real.inv_rpow hr.le, ← Real.rpow_neg hr.le]

theorem paperAffineState_gradient_ae {r : ℝ} (hr : 0 < r) (y : Space)
    (f : EnergyState) (j : Fin 3) :
    (energyGradient j (paperAffineState hr y f) : Space → ℂ) =ᵐ[volume]
      fun x ↦ r^(-(3/2 : ℝ)) • energyGradient j f (r⁻¹ • (x-y)) := by
  refine (affineState_gradient_ae (inv_pos.mpr hr) (-(r⁻¹) • y) f j).trans ?_
  filter_upwards with x
  unfold gradientPullback
  have hx : affine r⁻¹ (-(r⁻¹) • y) x = r⁻¹ • (x-y) := by
    simp only [affine, smul_sub, neg_smul]
    abel
  rw [hx]
  congr 1
  calc
    r⁻¹ * √r⁻¹ = (r⁻¹)^(1 : ℝ) * (r⁻¹)^(1/2 : ℝ) := by
      rw [Real.rpow_one, Real.sqrt_eq_rpow]
    _ = (r⁻¹)^(3/2 : ℝ) := by
      rw [← Real.rpow_add (inv_pos.mpr hr)]
      congr 1
      norm_num
    _ = r^(-(3/2 : ℝ)) := by
      rw [Real.inv_rpow hr.le, ← Real.rpow_neg hr.le]

/-- Pullback of the transformed time to the original trajectory. -/
def paperTimePullback (r tau t : ℝ) : ℝ :=
  timeAffine r⁻¹ (-tau / r^2) t

/-- Forward transport of the original lifespan. -/
def paperTimeForward (r tau t : ℝ) : ℝ := timeAffine r tau t

@[simp] theorem paperTimePullback_apply {r : ℝ} (hr : 0 < r) (tau t : ℝ) :
    paperTimePullback r tau t = (t-tau)/r^2 := by
  unfold paperTimePullback timeAffine
  field_simp [hr.ne']
  ring

@[simp] theorem paperTimeForward_apply (r tau t : ℝ) :
    paperTimeForward r tau t = tau+r^2*t := by
  unfold paperTimeForward timeAffine
  ring

theorem paperTimeForward_pullback {r : ℝ} (hr : 0 < r) (tau t : ℝ) :
    paperTimeForward r tau (paperTimePullback r tau t) = t := by
  rw [paperTimeForward_apply, paperTimePullback_apply hr]
  field_simp [hr.ne']
  ring

theorem paperTimePullback_forward {r : ℝ} (hr : 0 < r) (tau t : ℝ) :
    paperTimePullback r tau (paperTimeForward r tau t) = t := by
  rw [paperTimePullback_apply hr, paperTimeForward_apply]
  field_simp [hr.ne']
  ring

/-- The exact set identity behind `tau+r^2 I_max`. -/
theorem paperTimePullback_preimage_eq_forward_image {r : ℝ} (hr : 0 < r)
    (tau : ℝ) (S : Set ℝ) :
    (paperTimePullback r tau) ⁻¹' S = paperTimeForward r tau '' S := by
  ext t
  constructor
  · intro ht
    exact ⟨paperTimePullback r tau t, ht, paperTimeForward_pullback hr tau t⟩
  · rintro ⟨s, hs, rfl⟩
    change paperTimePullback r tau (paperTimeForward r tau s) ∈ S
    rw [paperTimePullback_forward hr]
    exact hs

/-- Literal simultaneous spacetime transform.  At `k=1/2` this is the value
field; at `k=3/2` it is the gradient field. -/
def paperParabolicField {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (r : ℝ) (y : Space) (tau k : ℝ) (f : ℝ → Space → E) : ℝ → Space → E :=
  parabolicField r⁻¹ (-(r⁻¹) • y) (-tau/r^2) k f

@[simp] theorem paperParabolicField_apply {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {r : ℝ} (hr : 0 < r) (y : Space) (tau k : ℝ)
    (f : ℝ → Space → E) (t : ℝ) (x : Space) :
    paperParabolicField r y tau k f t x =
      r^(-k) • f ((t-tau)/r^2) (r⁻¹ • (x-y)) := by
  unfold paperParabolicField parabolicField
  rw [show timeAffine r⁻¹ (-tau/r^2) t = (t-tau)/r^2 by
    exact paperTimePullback_apply hr tau t]
  have hx : affine r⁻¹ (-(r⁻¹) • y) x = r⁻¹ • (x-y) := by
    simp only [affine, smul_sub, neg_smul]
    abel
  rw [hx, Real.inv_rpow hr.le, ← Real.rpow_neg hr.le]

/-- The four norms in the manuscript, in the order E, W, Z and S. -/
def FourCriticalMixedNormsInvariant
    (r : ℝ) (y : Space) (tau : ℝ) (S : Set ℝ)
    (value : ℝ → Space → ℂ)
    (gradient : ℝ → Space → EuclideanSpace ℂ (Fin 3)) : Prop :=
  mixedNorm (volume.restrict ((paperTimePullback r tau) ⁻¹' S)) volume ∞ 2
      (paperParabolicField r y tau (3/2) gradient) =
      mixedNorm (volume.restrict S) volume ∞ 2 gradient ∧
  mixedNorm (volume.restrict ((paperTimePullback r tau) ⁻¹' S)) volume 10
      (ENNReal.ofReal (30/13 : ℝ)) (paperParabolicField r y tau (3/2) gradient) =
      mixedNorm (volume.restrict S) volume 10 (ENNReal.ofReal (30/13 : ℝ)) gradient ∧
  mixedNorm (volume.restrict ((paperTimePullback r tau) ⁻¹' S)) volume 2 6
      (paperParabolicField r y tau (3/2) gradient) =
      mixedNorm (volume.restrict S) volume 2 6 gradient ∧
  mixedNorm (volume.restrict ((paperTimePullback r tau) ⁻¹' S)) volume 10 10
      (paperParabolicField r y tau (1/2) value) =
      mixedNorm (volume.restrict S) volume 10 10 value

/-- The missing displayed Z identity is the same exact Jacobian computation
as E and W, with time exponent 2 and spatial exponent 6. -/
theorem parabolic_Z_invariant {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {a : ℝ} (ha : 0 < a) (b : Space) (c : ℝ) (S : Set ℝ)
    (f : ℝ → Space → E)
    (hf : AEStronglyMeasurable (fun z : ℝ × Space ↦ f z.1 z.2)
      ((volume.restrict S).prod volume)) :
    mixedNorm (volume.restrict ((timeAffine a c) ⁻¹' S)) volume 2 6
        (parabolicField a b c (3/2) f) =
      mixedNorm (volume.restrict S) volume 2 6 f := by
  have h := mixedNorm_parabolicField ha b c (3/2) S 2 6
    (by norm_num) (by norm_num) f hf
  norm_num [reciprocalExponent] at h
  exact h

theorem fourCriticalMixedNorms_invariant {r : ℝ} (hr : 0 < r)
    (y : Space) (tau : ℝ) (S : Set ℝ)
    (value : ℝ → Space → ℂ)
    (gradient : ℝ → Space → EuclideanSpace ℂ (Fin 3))
    (hv : AEStronglyMeasurable (fun z : ℝ × Space ↦ value z.1 z.2)
      ((volume.restrict S).prod volume))
    (hg : AEStronglyMeasurable (fun z : ℝ × Space ↦ gradient z.1 z.2)
      ((volume.restrict S).prod volume)) :
    FourCriticalMixedNormsInvariant r y tau S value gradient := by
  unfold FourCriticalMixedNormsInvariant paperParabolicField paperTimePullback
  let ha : 0 < r⁻¹ := inv_pos.mpr hr
  exact ⟨parabolic_energy_gradient_invariant ha (-(r⁻¹) • y) (-tau/r^2) S gradient hg,
    parabolic_W_invariant ha (-(r⁻¹) • y) (-tau/r^2) S gradient hg,
    parabolic_Z_invariant ha (-(r⁻¹) • y) (-tau/r^2) S gradient hg,
    parabolic_S_invariant ha (-(r⁻¹) • y) (-tau/r^2) S value hv⟩

theorem paperAffineState_totalEnergy {alpha r : ℝ}
    (hH : OrdinaryHLS alpha (HeatRiesz.standardRieszConstant alpha))
    (hr : 0 < r) (y : Space) (f : EnergyState) :
    totalEnergy alpha (paperAffineState hr y f) = totalEnergy alpha f := by
  exact affineState_totalEnergy hH (inv_pos.mpr hr) (-(r⁻¹) • y) f

/-- Full Lemma 3.5 in the paper's `(r,y,tau)` convention: exact maximal
trajectory and lifespan covariance, energy invariance, and E/W/Z/S invariance. -/
theorem lemma35_exact_affine_covariance
    (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr Che Cre alpha : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0)
    (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hefree : OrdinaryHomogeneousEndpointOutput Che)
    (heret : OrdinaryRetardedEndpointOutput h0 Cre)
    (hH : OrdinaryHLS alpha (HeatRiesz.standardRieszConstant alpha))
    {r : ℝ} (hr : 0 < r) (y : Space) (tau s0 : ℝ) (f : EnergyState) :
    let U := actualMaximalTrajectory hDensity hSob h0 hfree hret
      hefree heret hH s0 f
    let V := actualMaximalTrajectory hDensity hSob h0 hfree hret
      hefree heret hH (tau+r^2*s0) (paperAffineState hr y f)
    V.domain = paperTimeForward r tau '' U.domain ∧
    Set.EqOn V.state
      (fun t ↦ paperAffineState hr y (U.state (paperTimePullback r tau t))) V.domain ∧
    (∀ q : EnergyState,
      (energyValue (paperAffineState hr y q) : Space → ℂ) =ᵐ[volume]
          (fun x ↦ r^(-(1/2 : ℝ)) • energyValue q (r⁻¹ • (x-y))) ∧
      (∀ j : Fin 3,
        (energyGradient j (paperAffineState hr y q) : Space → ℂ) =ᵐ[volume]
          (fun x ↦ r^(-(3/2 : ℝ)) • energyGradient j q (r⁻¹ • (x-y)))) ∧
      totalEnergy alpha (paperAffineState hr y q) = totalEnergy alpha q) ∧
    ∀ (S : Set ℝ) (value : ℝ → Space → ℂ)
      (gradient : ℝ → Space → EuclideanSpace ℂ (Fin 3)),
      AEStronglyMeasurable (fun z : ℝ × Space ↦ value z.1 z.2)
          ((volume.restrict S).prod volume) →
      AEStronglyMeasurable (fun z : ℝ × Space ↦ gradient z.1 z.2)
          ((volume.restrict S).prod volume) →
      FourCriticalMixedNormsInvariant r y tau S value gradient := by
  dsimp only
  have hmark : (s0-(-tau/r^2))/(r⁻¹)^2 = tau+r^2*s0 := by
    field_simp [hr.ne']
    ring
  have hraw := actualMaximalTrajectory_affine hDensity hSob h0 hfree hret
    hefree heret hH (inv_pos.mpr hr) (-(r⁻¹) • y) (-tau/r^2) s0 f
  dsimp only at hraw
  rw [hmark] at hraw
  have hcov :
      (actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH
        (tau+r^2*s0) (paperAffineState hr y f)).domain =
          (paperTimePullback r tau) ⁻¹'
            (actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH s0 f).domain ∧
      Set.EqOn
        (actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH
          (tau+r^2*s0) (paperAffineState hr y f)).state
        (fun t ↦ paperAffineState hr y
          ((actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH s0 f).state
            (paperTimePullback r tau t)))
        (actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH
          (tau+r^2*s0) (paperAffineState hr y f)).domain := by
    rw [show paperTimePullback r tau = timeAffine r⁻¹ (-tau/r^2) from rfl]
    simpa only [paperAffineState] using hraw
  refine ⟨hcov.1.trans
      (paperTimePullback_preimage_eq_forward_image hr tau _), hcov.2, ?_, ?_⟩
  · intro q
    exact ⟨paperAffineState_value_ae hr y q,
      paperAffineState_gradient_ae hr y q,
      paperAffineState_totalEnergy hH hr y q⟩
  · intro S value gradient hv hg
    exact fourCriticalMixedNorms_invariant hr y tau S value gradient hv hg

end HartreeF.Paper121Lemma35
