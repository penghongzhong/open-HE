import FR2ActualGlobalX
import FFiniteProfileWeakGradient
import FCriticalAffineMixedNorms
import FStateFreeAffineCovariance

/-! Actual source-order profile frames, with their canonical EnergyState and
joint representatives kept separate. Static author source; UNCOMPILED. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2200000
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
namespace HartreeF.R2Frames
open EnergySpace SobolevStretch StationarySelfTest CriticalAffine AffineMixed TimeHolder
  ProfileApproximation ProfileSpatialSmoothing GeneralProfileCross CriticalTimeSobolev
  FiniteProfileWeakGradient ProfileEnergy R2Global FreeAffine CompactCross
local instance : SecondCountableTopologyEither ℝ EnergyState :=
  ⟨Or.inl inferInstance⟩

/-- The original positive-length frame, retaining its normalized time shift. -/
def stateFrame (g : ℝ → EnergyState) {a : ℝ} (ha : 0 < a)
    (y : Space) (s : ℝ) : ℝ → EnergyState :=
  fun t => criticalAffineState a ha y (g (timeAffine a⁻¹ s t))

theorem stateFrame_time (g : ℝ → EnergyState) {a : ℝ} (ha : 0 < a)
    (y : Space) (s t : ℝ) :
    stateFrame g ha y s t = criticalAffineState a ha y (g (s + t / a^2)) := by
  unfold stateFrame timeAffine
  congr 2
  rw [inv_pow, div_eq_mul_inv]
  ring

theorem stateFrame_continuous {g : ℝ → EnergyState} (hg : Continuous g)
    {a : ℝ} (ha : 0 < a) (y : Space) (s : ℝ) : Continuous (stateFrame g ha y s) := by
  exact (criticalAffineState a ha y).continuous.comp
    (hg.comp (by unfold timeAffine; fun_prop))

theorem stateFrame_sub (g h : ℝ → EnergyState) {a : ℝ} (ha : 0 < a)
    (y : Space) (s : ℝ) : stateFrame (g-h) ha y s = stateFrame g ha y s - stateFrame h ha y s := by
  funext t
  exact (criticalAffineState a ha y).map_sub _ _

private theorem derivative_weight {a : ℝ} (ha : 0 < a) :
    a⁻¹ * Real.sqrt a⁻¹ = (a⁻¹) ^ (3/2 : ℝ) := by
  rw [Real.sqrt_eq_rpow]
  calc
    _ = (a⁻¹) ^ (1 : ℝ) * (a⁻¹) ^ (1/2 : ℝ) := by rw [Real.rpow_one]
    _ = (a⁻¹) ^ ((1 : ℝ) + 1/2) := (Real.rpow_add (inv_pos.mpr ha) _ _).symm
    _ = _ := by norm_num

/-- Every time slice has the literal affine value and two genuine weak gradients. -/
theorem stateFrame_fields_ae (g : ℝ → EnergyState) {a : ℝ} (ha : 0 < a)
    (y : Space) (s t : ℝ) :
    (energyValue (stateFrame g ha y s t) : Space → ℂ) =ᵐ[volume] framedValue g a y s t ∧
    energyProjectedGradient Complex.reCLM (stateFrame g ha y s t) =ᵐ[volume]
      framedReal g a y s t ∧
    energyProjectedGradient Complex.imCLM (stateFrame g ha y s t) =ᵐ[volume]
      framedImag g a y s t := by
  let z := g (timeAffine a⁻¹ s t)
  let hz := inDotH1_affine_pullback (energyState_inDotH1 z)
    (inv_pos.mpr ha) (-(a⁻¹ • y))
  refine ⟨?_, ?_, ?_⟩
  · have he : valuePullback a⁻¹ (-(a⁻¹ • y)) (energyValue z) = framedValue g a y s t := by
      funext x
      change Real.sqrt a⁻¹ • (energyValue z : Space → ℂ) (affine a⁻¹ (-(a⁻¹ • y)) x) =
        (a⁻¹) ^ (1/2 : ℝ) • (energyValue z : Space → ℂ) (affine a⁻¹ (-(a⁻¹ • y)) x)
      rw [Real.sqrt_eq_rpow]
    rw [← he]
    exact inDotEnergyState_value_ae hz
  · have he : gradientPullback a⁻¹ (-(a⁻¹ • y)) (energyProjectedGradient Complex.reCLM z) =
        framedReal g a y s t := by
      funext x
      change (a⁻¹ * Real.sqrt a⁻¹) • energyProjectedGradient Complex.reCLM z
        (affine a⁻¹ (-(a⁻¹ • y)) x) =
        (a⁻¹) ^ (3/2 : ℝ) • energyProjectedGradient Complex.reCLM z
          (affine a⁻¹ (-(a⁻¹ • y)) x)
      rw [derivative_weight ha]
    rw [← he]
    exact inDotEnergyState_real_gradient_ae hz
  · have he : gradientPullback a⁻¹ (-(a⁻¹ • y)) (energyProjectedGradient Complex.imCLM z) =
        framedImag g a y s t := by
      funext x
      change (a⁻¹ * Real.sqrt a⁻¹) • energyProjectedGradient Complex.imCLM z
        (affine a⁻¹ (-(a⁻¹ • y)) x) =
        (a⁻¹) ^ (3/2 : ℝ) • energyProjectedGradient Complex.imCLM z
          (affine a⁻¹ (-(a⁻¹ • y)) x)
      rw [derivative_weight ha]
    rw [← he]
    exact inDotEnergyState_imag_gradient_ae hz

/-- An actual joint representative of the same framed curve; no joint
measurability is claimed for canonical quotient representatives. -/
def frameJointFields (g : ℝ → EnergyState) (r : EnergyJointFields volume g)
    {a : ℝ} (ha : 0 < a) (y : Space) (s : ℝ) :
    EnergyJointFields volume (stateFrame g ha y s) where
  u := framedJointValue r a y s
  U := framedJointReal r a y s
  V := framedJointImag r a y s
  joint_u := (framedJoint_joint_measurable r a y s).1
  joint_U := (framedJoint_joint_measurable r a y s).2.1
  joint_V := (framedJoint_joint_measurable r a y s).2.2
  slice_eq := by
    filter_upwards [framedJoint_nested_ae g r ha y s] with t ht
    have hs := stateFrame_fields_ae g ha y s t
    exact ⟨ht.1.symm.trans hs.1.symm, ht.2.1.symm.trans hs.2.1.symm,
      ht.2.2.symm.trans hs.2.2.symm⟩

theorem stateFrame_curveEnergy (g : ℝ → EnergyState) {a : ℝ} (ha : 0 < a)
    (y : Space) (s : ℝ) : curveEnergy (stateFrame g ha y s) = curveEnergy g := by
  unfold curveEnergy
  simp only [stateFrame, criticalAffineState_pureGradientNorm]
  have h := time_eLpNorm_affine (inv_pos.mpr ha) s Set.univ ∞
    (fun t => pureGradientNorm (g t))
  simpa [reciprocalExponent, Function.comp_def] using h

private theorem joint_value_norm (g : ℝ → EnergyState) (r : EnergyJointFields volume g) :
    mixedNorm volume volume 10 10 r.u = curveS g := by
  exact mixedNorm_congr_nested_ae volume volume 10 10 (r.slice_eq.mono fun _ ht => ht.1)

private theorem joint_gradient_norm (g : ℝ → EnergyState) (r : EnergyJointFields volume g) :
    mixedNorm volume volume 10 (ENNReal.ofReal (30/13 : ℝ))
      (fun t => complexGradient (r.U t) (r.V t)) = curveW g := by
  apply mixedNorm_congr_nested_ae
  filter_upwards [r.slice_eq] with t ht
  filter_upwards [ht.2.1, ht.2.2] with x hx hy
  exact congrArg₂ (fun U V : Space => complexGradient (fun _ => U) (fun _ => V) x) hx hy

theorem stateFrame_curveS {g : ℝ → EnergyState} (hg : Continuous g)
    {a : ℝ} (ha : 0 < a) (y : Space) (s : ℝ) :
    curveS (stateFrame g ha y s) = curveS g := by
  let r := energyJointFields volume g hg.aestronglyMeasurable
  let rf := frameJointFields g r ha y s
  rw [← joint_value_norm _ rf, ← joint_value_norm g r]
  exact seedFrame_S_invariant ha y s r.u r.joint_u.aestronglyMeasurable

theorem stateFrame_curveW {g : ℝ → EnergyState} (hg : Continuous g)
    {a : ℝ} (ha : 0 < a) (y : Space) (s : ℝ) :
    curveW (stateFrame g ha y s) = curveW g := by
  let r := energyJointFields volume g hg.aestronglyMeasurable
  let rf := frameJointFields g r ha y s
  rw [← joint_gradient_norm _ rf, ← joint_gradient_norm g r]
  change mixedNorm volume volume 10 (ENNReal.ofReal (30/13 : ℝ))
    (fun t => complexGradient (parabolicField a⁻¹ (-(a⁻¹ • y)) s (3/2) r.U t)
      (parabolicField a⁻¹ (-(a⁻¹ • y)) s (3/2) r.V t)) = _
  rw [← gradientFrame_is_packed]
  have h := parabolic_W_invariant (inv_pos.mpr ha) (-(a⁻¹ • y)) s Set.univ
    (fun t => complexGradient (r.U t) (r.V t))
    (by simpa only [Measure.restrict_univ] using
      (packedGradient_joint_measurable
        r.joint_U.aestronglyMeasurable r.joint_V.aestronglyMeasurable))
  simpa only [Set.preimage_univ, Measure.restrict_univ, gradientFrame] using h

theorem stateFrame_curveX {g : ℝ → EnergyState} (hg : Continuous g)
    {a : ℝ} (ha : 0 < a) (y : Space) (s : ℝ) :
    curveX (stateFrame g ha y s) = curveX g := by
  simp only [curveX, stateFrame_curveEnergy, stateFrame_curveS hg, stateFrame_curveW hg]

theorem CurveFinite.stateFrame {g : ℝ → EnergyState} (hg : CurveFinite g)
    {a : ℝ} (ha : 0 < a) (y : Space) (s : ℝ) : CurveFinite (stateFrame g ha y s) := by
  refine ⟨stateFrame_continuous hg.continuous ha y s, ?_, ?_, ?_⟩
  · rw [stateFrame_curveEnergy]
    exact hg.energy
  · rw [stateFrame_curveS hg.continuous]
    exact hg.value
  · rw [stateFrame_curveW hg.continuous]
    exact hg.gradient

theorem stateFrame_xNorm {g : ℝ → EnergyState} (hg : Continuous g)
    {a : ℝ} (ha : 0 < a) (y : Space) (s : ℝ) :
    xNorm (stateFrame g ha y s) = xNorm g := by
  exact congrArg ENNReal.toReal (stateFrame_curveX hg ha y s)

/-- The normalized free orbit is exactly the original physical profile atom. -/
theorem stateFrame_free (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) (φ : EnergyState) {a : ℝ} (ha : 0 < a)
    (y : Space) (s : ℝ) :
    stateFrame (fun t => freeEnergyState hDensity hSob t φ) ha y s =
      (fun t => freeEnergyState hDensity hSob t
        (linearProfileFrame hDensity hSob a ha y s φ)) := by
  funext t
  rw [linearProfileFrame_free_evolution, linearProfileFrame_apply, stateFrame_time]

/-- The source-order correction is an exact EnergyState difference. -/
theorem stateFrame_correction (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) (g : ℝ → EnergyState) (φ : EnergyState)
    {a : ℝ} (ha : 0 < a) (y : Space) (s : ℝ) :
    stateFrame (fun t => g t - freeEnergyState hDensity hSob t φ) ha y s =
      (fun t => stateFrame g ha y s t - freeEnergyState hDensity hSob t
        (linearProfileFrame hDensity hSob a ha y s φ)) := by
  rw [show (fun t => g t - freeEnergyState hDensity hSob t φ) =
    g - (fun t => freeEnergyState hDensity hSob t φ) from rfl,
    stateFrame_sub, stateFrame_free]
  rfl

end HartreeF.R2Frames
