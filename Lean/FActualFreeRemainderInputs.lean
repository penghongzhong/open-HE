import FOrdinaryLinearProfileInterface
import FOrdinaryHomogeneousStrichartz
import FStateFreeAffineCovariance
import FGeneralRepresentativeTransport

/-! Actual fixed-depth remainder data and its original-frame gradient.
Static candidate, UNCOMPILED. No scalar L2 requirement is imposed on an
EnergyState. All bounds below are at every original sequence index. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option warningAsError true
set_option maxHeartbeats 1500000
open MeasureTheory Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace HartreeF.FreeRemainderInputs
open EnergySpace SobolevStretch StationarySelfTest ProfileEnergy ActualStrichartz CriticalAffine
  GeneralProfileCross CompactCross AffineMixed TimeHolder

/-- A fixed-depth cap; no uniformity in J is asserted. -/
def headGradientCap (B : ℝ) (P : LinearProfileFamily) (J : ℕ) : ℝ :=
  B + ∑ j ∈ Finset.range J, pureGradientNorm (P.profile j)

def inverseFrameRemainder (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) (P : LinearProfileFamily) (u : ℕ → EnergyState)
    (J j n : ℕ) : EnergyState :=
  (linearProfileFrame hDensity hSob (P.scale j n) (P.scale_pos j n)
    (P.center j n) (P.time j n)).symm (profileRemainder hDensity hSob P u J n)

/-- The actual normalized free gradient coordinate, with a genuine joint representative. -/
def normalizedFreeGradient (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) (P : LinearProfileFamily) (u : ℕ → EnergyState)
    (J j : ℕ) (k : Fin 3) (n : ℕ) : ℝ → V → ℂ :=
  freeJoint (energyGradient k (inverseFrameRemainder hDensity hSob P u J j n))

theorem headGradientCap_nonneg {B : ℝ} (hB : 0 ≤ B) (P : LinearProfileFamily) (J : ℕ) :
    0 ≤ headGradientCap B P J :=
  add_nonneg hB (Finset.sum_nonneg (fun i _ => pureGradientNorm_nonneg (P.profile i)))

theorem inverseFrameRemainder_bound (hDensity : OrdinaryH1Density) {K B : ℝ}
    (hSob : OrdinarySobolev K) (P : LinearProfileFamily) (u : ℕ → EnergyState)
    (hB : ∀ n, pureGradientNorm (u n) ≤ B) (J j n : ℕ) :
    pureGradientNorm (inverseFrameRemainder hDensity hSob P u J j n) ≤
      headGradientCap B P J := by
  let A := linearProfileFrame hDensity hSob (P.scale j n) (P.scale_pos j n)
    (P.center j n) (P.time j n)
  have he := linearProfileFrame_pureGradientNorm hDensity hSob (P.scale j n)
    (P.scale_pos j n) (P.center j n) (P.time j n)
    (A.symm (profileRemainder hDensity hSob P u J n))
  change pureGradientNorm (A (A.symm (profileRemainder hDensity hSob P u J n))) =
    pureGradientNorm (A.symm (profileRemainder hDensity hSob P u J n)) at he
  rw [ContinuousLinearEquiv.apply_symm_apply] at he
  exact he.symm.trans_le (profileRemainder_pureGradient_bound hDensity hSob P u hB J n)

theorem inverseFrameRemainder_coordinate_bound (hDensity : OrdinaryH1Density) {K B : ℝ}
    (hSob : OrdinarySobolev K) (P : LinearProfileFamily) (u : ℕ → EnergyState)
    (hB : ∀ n, pureGradientNorm (u n) ≤ B) (J j n : ℕ) (k : Fin 3) :
    ‖energyGradient k (inverseFrameRemainder hDensity hSob P u J j n)‖ ≤
      headGradientCap B P J :=
  (energyGradient_le_pureGradient _ k).trans
    (inverseFrameRemainder_bound hDensity hSob P u hB J j n)

theorem inverseFrameRemainder_weak_zero (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) (P : LinearProfileFamily) (u : ℕ → EnergyState)
    (hp : LinearProfileProperties hDensity hSob u P) (J j : ℕ)
    (hj : j < J) (hJ : (J : WithTop ℕ) ≤ P.count) (k : Fin 3) (v : L2) :
    Tendsto (fun n => inner ℝ
      (energyGradient k (inverseFrameRemainder hDensity hSob P u J j n)) v)
      atTop (𝓝 0) := by
  simpa only [inverseFrameRemainder, map_zero, inner_zero_left] using
    hp.weak_remainder J j hj hJ k v

/-- Every time slice is a real L2 domain, before the temporal essential supremum. -/
theorem freeJoint_slice_eLpNorm (f : FreeFlow.L2) (t : ℝ) :
    eLpNorm (freeJoint f t) 2 volume = ENNReal.ofReal ‖f‖ := by
  rw [eLpNorm_congr_ae (freeJoint_slice f t), ← Lp.enorm_def, ← ofReal_norm,
    FreeFlow.freeL2_norm]

theorem freeJoint_E_bound (f : FreeFlow.L2) :
    mixedNorm volume volume ∞ 2 (freeJoint f) ≤ ENNReal.ofReal ‖f‖ := by
  change eLpNorm (fun t : ℝ => eLpNorm (freeJoint f t) 2 volume) ∞ volume ≤ _
  simp_rw [freeJoint_slice_eLpNorm]
  rw [eLpNorm_exponent_top aestronglyMeasurable_const]
  apply eLpNormEssSup_le_of_ae_enorm_bound
  exact Eventually.of_forall (fun _ => by rw [enorm_eq_self])

theorem normalizedFreeGradient_joint (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) (P : LinearProfileFamily) (u : ℕ → EnergyState)
    (J j : ℕ) (k : Fin 3) (n : ℕ) :
    StronglyMeasurable (fun z : ℝ × V =>
      normalizedFreeGradient hDensity hSob P u J j k n z.1 z.2) :=
  freeJoint_stronglyMeasurable _

/-- Both E and W caps concern the same field, at every n. -/
theorem normalizedFreeGradient_bounds (hDensity : OrdinaryH1Density) {K B C : ℝ}
    (hSob : OrdinarySobolev K) (hStr : OrdinaryHomogeneousStrichartz C)
    (P : LinearProfileFamily) (u : ℕ → EnergyState)
    (hB : ∀ n, pureGradientNorm (u n) ≤ B) (J j : ℕ) (k : Fin 3) (n : ℕ) :
    mixedNorm volume volume ∞ 2
      (normalizedFreeGradient hDensity hSob P u J j k n) ≤
      ENNReal.ofReal (headGradientCap B P J) ∧
    mixedNorm volume volume 10 (ENNReal.ofReal (30/13 : ℝ))
      (normalizedFreeGradient hDensity hSob P u J j k n) ≤
      ENNReal.ofReal (C * headGradientCap B P J) := by
  have hc := inverseFrameRemainder_coordinate_bound hDensity hSob P u hB J j n k
  exact ⟨(freeJoint_E_bound _).trans (ENNReal.ofReal_le_ofReal hc),
    (hStr.2 _).trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_left hc hStr.1))⟩

/-- Actual gradient covariance is an AE representative statement, never a
pointwise assertion about the chosen L2 representatives. -/
theorem free_gradient_frame_ae (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) (lambda : ℝ) (hlambda : 0 < lambda) (y : V) (s : ℝ)
    (v : EnergyState) (k : Fin 3) (t : ℝ) :
    freeJoint (energyGradient k (linearProfileFrame hDensity hSob lambda hlambda y s v)) t =ᵐ[volume]
      seedFrame lambda y s (3/2) (freeJoint (energyGradient k v)) t := by
  have ht : timeAffine lambda⁻¹ s t = s + t / lambda^2 := by
    simp only [timeAffine, inv_pow, div_eq_mul_inv]
    ring
  have ha : (lambda⁻¹) ^ (3/2 : ℝ) = lambda⁻¹ * (Real.sqrt lambda)⁻¹ := by
    rw [← Real.sqrt_inv, Real.sqrt_eq_rpow]
    calc
      (lambda⁻¹) ^ (3/2 : ℝ) = (lambda⁻¹) ^ ((1 : ℝ) + 1/2) := by norm_num
      _ = (lambda⁻¹) ^ (1 : ℝ) * (lambda⁻¹) ^ (1/2 : ℝ) :=
        Real.rpow_add (inv_pos.mpr hlambda) _ _
      _ = _ := by rw [Real.rpow_one]
  have hleft : freeJoint
      (energyGradient k (linearProfileFrame hDensity hSob lambda hlambda y s v)) t =ᵐ[volume]
      energyGradient k (freeEnergyState hDensity hSob t
        (linearProfileFrame hDensity hSob lambda hlambda y s v)) := by
    rw [freeEnergyState_gradient]
    exact freeJoint_slice _ t
  have hstate : freeEnergyState hDensity hSob t
      (linearProfileFrame hDensity hSob lambda hlambda y s v) =
      criticalAffineState lambda hlambda y (freeEnergyState hDensity hSob (s+t/lambda^2) v) := by
    rw [FreeAffine.linearProfileFrame_free_evolution, linearProfileFrame_apply]
  rw [hstate] at hleft
  have hright : freeJoint (energyGradient k v) (s+t/lambda^2) =ᵐ[volume]
      energyGradient k (freeEnergyState hDensity hSob (s+t/lambda^2) v) := by
    rw [freeEnergyState_gradient]
    exact freeJoint_slice _ _
  have hpull := affine_ae_pullback (inv_pos.mpr hlambda) (-(lambda⁻¹ • y)) hright
  filter_upwards [hleft, criticalAffineState_gradient_ae lambda hlambda y
    (freeEnergyState hDensity hSob (s+t/lambda^2) v) k, hpull] with x hl hx hr
  rw [hl, hx]
  simp only [seedFrame, parabolicField, ht, ha, paper_space_map] at hr ⊢
  exact congrArg (fun z : ℂ => (lambda⁻¹ * (Real.sqrt lambda)⁻¹) • z) hr.symm

/-- The physical free remainder is independent of the label used to view it. -/
theorem remainder_free_gradient_frame_ae (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) (P : LinearProfileFamily) (u : ℕ → EnergyState)
    (J j n : ℕ) (k : Fin 3) (t : ℝ) :
    freeJoint (energyGradient k (profileRemainder hDensity hSob P u J n)) t =ᵐ[volume]
      seedFrame (P.scale j n) (P.center j n) (P.time j n) (3/2)
        (normalizedFreeGradient hDensity hSob P u J j k n) t := by
  have h := free_gradient_frame_ae hDensity hSob (P.scale j n) (P.scale_pos j n)
    (P.center j n) (P.time j n) (inverseFrameRemainder hDensity hSob P u J j n) k t
  simpa only [inverseFrameRemainder, ContinuousLinearEquiv.apply_symm_apply,
    normalizedFreeGradient] using h

end HartreeF.FreeRemainderInputs
