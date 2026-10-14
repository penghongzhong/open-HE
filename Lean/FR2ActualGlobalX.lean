import FActualVectorGradientExhaustion
import FActualCoherentPathValueExhaustion
import FTwoSidedNestedLpAssembly
import FActualMollifiedFields
import FProfileEnergyBridge
import FCriticalHartreeSourceSmallness

/-! Actual global E+S+W. Static author source; no native validation is asserted.
All real conversions below require the extended norm's genuine finite domain. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology
namespace HartreeF.R2Global
open EnergySpace CriticalPathSpace SobolevStretch StationarySelfTest TimeHolder
  CriticalTimeSobolev ProfileApproximation ProfileSpatialSmoothing
  HomogeneousStability IntervalNormExhaustion CriticalSourceBounds EndpointOutput
attribute [local instance] FreeDataDependence.canonicalEnergyNormedSpace
  FreeDataDependence.canonicalPathNormedSpace
attribute [local irreducible] energySubmodule criticalPathSubmodule energyPath
local instance : SecondCountableTopologyEither ℝ EnergyState :=
  ⟨Or.inl inferInstance⟩

def curveGradient (g : ℝ → EnergyState) (t : ℝ) : Space → EuclideanSpace ℂ (Fin 3) :=
  complexGradient (stateRealGradientField g t) (stateImagGradientField g t)

def curveS (g : ℝ → EnergyState) : ℝ≥0∞ :=
  mixedNorm volume volume 10 10 (stateValueField g)

def curveW (g : ℝ → EnergyState) : ℝ≥0∞ :=
  mixedNorm volume volume 10 (ENNReal.ofReal (30/13 : ℝ)) (curveGradient g)

def curveX (g : ℝ → EnergyState) : ℝ≥0∞ := curveEnergy g + curveS g + curveW g

structure CurveFinite (g : ℝ → EnergyState) : Prop where
  continuous : Continuous g
  energy : curveEnergy g ≠ ∞
  value : curveS g ≠ ∞
  gradient : curveW g ≠ ∞

def xNorm (g : ℝ → EnergyState) : ℝ := (curveX g).toReal

theorem CurveFinite.x_ne_top {g : ℝ → EnergyState} (h : CurveFinite g) :
    curveX g ≠ ∞ := by
  exact ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨h.energy, h.value⟩, h.gradient⟩

theorem curveEnergy_le_curveX (g : ℝ → EnergyState) : curveEnergy g ≤ curveX g :=
  (le_add_of_nonneg_right bot_le).trans (le_add_of_nonneg_right bot_le)

theorem curveS_le_curveX (g : ℝ → EnergyState) : curveS g ≤ curveX g :=
  (le_add_of_nonneg_left bot_le).trans (le_add_of_nonneg_right bot_le)

theorem curveW_le_curveX (g : ℝ → EnergyState) : curveW g ≤ curveX g :=
  le_add_of_nonneg_left bot_le

theorem CurveFinite.of_le {g : ℝ → EnergyState} (hg : Continuous g) {R : ℝ}
    (h : curveX g ≤ ENNReal.ofReal R) : CurveFinite g := by
  have hx := ne_top_of_le_ne_top ENNReal.ofReal_ne_top h
  exact ⟨hg, ne_top_of_le_ne_top hx (curveEnergy_le_curveX g),
    ne_top_of_le_ne_top hx (curveS_le_curveX g),
    ne_top_of_le_ne_top hx (curveW_le_curveX g)⟩

theorem xNorm_nonneg (g : ℝ → EnergyState) : 0 ≤ xNorm g := ENNReal.toReal_nonneg

theorem ofReal_xNorm {g : ℝ → EnergyState} (h : CurveFinite g) :
    ENNReal.ofReal (xNorm g) = curveX g := ENNReal.ofReal_toReal h.x_ne_top

theorem xNorm_le {g : ℝ → EnergyState} {R : ℝ} (hR : 0 ≤ R)
    (h : curveX g ≤ ENNReal.ofReal R) : xNorm g ≤ R :=
  (ENNReal.toReal_mono ENNReal.ofReal_ne_top h).trans_eq (ENNReal.toReal_ofReal hR)

theorem curveX_le_of_component_caps (g : ℝ → EnergyState) {E S W : ℝ}
    (hE : 0 ≤ E) (hS : 0 ≤ S) (hW : 0 ≤ W)
    (he : curveEnergy g ≤ ENNReal.ofReal E)
    (hs : curveS g ≤ ENNReal.ofReal S) (hw : curveW g ≤ ENNReal.ofReal W) :
    curveX g ≤ ENNReal.ofReal (E+S+W) := by
  calc
    curveX g ≤ ENNReal.ofReal E + ENNReal.ofReal S + ENNReal.ofReal W :=
      add_le_add (add_le_add he hs) hw
    _ = _ := by rw [← ENNReal.ofReal_add hE hS, ← ENNReal.ofReal_add (add_nonneg hE hS) hW]

theorem curveGradient_eq_actual (g : ℝ → EnergyState) (t : ℝ) :
    curveGradient g t = energyComplexGradient (g t) := by
  funext x
  ext j
  exact (state_complexGradient_coordinate (g t) x j).trans
    (energyComplexGradient_coordinate (g t) x j).symm

theorem curveW_eq_actual (g : ℝ → EnergyState) :
    curveW g = mixedNorm volume volume 10 criticalExponent
      (fun t => energyComplexGradient (g t)) := by
  rfl

theorem curveEnergy_eq_actual (g : ℝ → EnergyState) (hg : Continuous g) :
    curveEnergy g = mixedNorm volume volume ∞ 2
      (fun t => energyComplexGradient (g t)) := by
  let r := energyJointFields volume g hg.aestronglyMeasurable
  apply (jointFields_energy_eq g r hg.aestronglyMeasurable).symm.trans
  apply eLpNorm_congr_ae
  filter_upwards [r.slice_eq] with t ht
  apply eLpNorm_congr_ae
  filter_upwards [ht.2.1, ht.2.2] with x hR hI
  have he : complexGradient (r.U t) (r.V t) x = curveGradient g t x := by
    simp only [curveGradient, stateRealGradientField, stateImagGradientField,
      complexGradient, hR, hI]
  exact he.trans (congrFun (curveGradient_eq_actual g t) x)

theorem joint_value_norm (g : ℝ → EnergyState) (r : EnergyJointFields volume g)
    (p q : ℝ≥0∞) :
    mixedNorm volume volume p q r.u = mixedNorm volume volume p q (stateValueField g) := by
  apply eLpNorm_congr_ae
  filter_upwards [r.slice_eq] with t ht
  exact eLpNorm_congr_ae ht.1

theorem joint_gradient_norm (g : ℝ → EnergyState) (r : EnergyJointFields volume g)
    (p q : ℝ≥0∞) :
    mixedNorm volume volume p q (fun t => complexGradient (r.U t) (r.V t)) =
      mixedNorm volume volume p q (curveGradient g) := by
  apply eLpNorm_congr_ae
  filter_upwards [r.slice_eq] with t ht
  apply eLpNorm_congr_ae
  filter_upwards [ht.2.1, ht.2.2] with x hR hI
  simp only [curveGradient, stateRealGradientField, stateImagGradientField,
    complexGradient, hR, hI]

theorem CurveFinite.value_slices {g : ℝ → EnergyState} (h : CurveFinite g) :
    ∀ᵐ t ∂volume, MemLp (stateValueField g t) 10 volume :=
  finite_mixedNorm_ae_slice_memLp volume volume 10 10 (by norm_num) (by norm_num) _ h.value

theorem CurveFinite.gradient_slices {g : ℝ → EnergyState} (h : CurveFinite g) :
    ∀ᵐ t ∂volume, MemLp (curveGradient g t) (ENNReal.ofReal (30/13 : ℝ)) volume :=
  finite_mixedNorm_ae_slice_memLp volume volume 10 _ (by norm_num) (by norm_num) _ h.gradient

/-- The actual spatial and time domains precede the real mixed norm. -/
theorem CurveFinite.value_time {g : ℝ → EnergyState} (h : CurveFinite g) :
    MemLp (fun t => eLpNorm (stateValueField g t) 10 volume) 10 volume :=
  lt_top_iff_ne_top.mpr h.value

theorem CurveFinite.gradient_time {g : ℝ → EnergyState} (h : CurveFinite g) :
    MemLp (fun t => eLpNorm (curveGradient g t) (ENNReal.ofReal (30/13 : ℝ)) volume)
      10 volume := lt_top_iff_ne_top.mpr h.gradient

/-- Real-valued time profiles are formed only after their slice domains. -/
theorem CurveFinite.value_real_time {g : ℝ → EnergyState} (h : CurveFinite g) :
    MemLp (fun t => (eLpNorm (stateValueField g t) 10 volume).toReal) 10 volume := by
  have he := finite_extended_norm_bridge volume 10
    (fun t => eLpNorm (stateValueField g t) 10 volume) h.value_time.aestronglyMeasurable
    (h.value_slices.mono fun _ ht => ht.ne)
  change eLpNorm (fun t => (eLpNorm (stateValueField g t) 10 volume).toReal) 10 volume < ∞
  rw [← he]
  exact h.value_time

theorem CurveFinite.gradient_real_time {g : ℝ → EnergyState} (h : CurveFinite g) :
    MemLp (fun t => (eLpNorm (curveGradient g t) (ENNReal.ofReal (30/13 : ℝ)) volume).toReal)
      10 volume := by
  have he := finite_extended_norm_bridge volume 10
    (fun t => eLpNorm (curveGradient g t) (ENNReal.ofReal (30/13 : ℝ)) volume)
    h.gradient_time.aestronglyMeasurable (h.gradient_slices.mono fun _ ht => ht.ne)
  change eLpNorm (fun t => (eLpNorm (curveGradient g t)
    (ENNReal.ofReal (30/13 : ℝ)) volume).toReal) 10 volume < ∞
  rw [← he]
  exact h.gradient_time

/-- The canonical packed gradients are additive only up to spatial AE. -/
theorem curveGradient_add_slice (g h : ℝ → EnergyState) (t : ℝ) :
    curveGradient (g+h) t =ᵐ[volume] fun x => curveGradient g t x + curveGradient h t x := by
  have hc (j : Fin 3) : (energyGradient j (g t+h t) : Space → ℂ) =ᵐ[volume]
      fun x => energyGradient j (g t) x + energyGradient j (h t) x := by
    rw [map_add]
    exact Lp.coeFn_add (energyGradient j (g t)) (energyGradient j (h t))
  filter_upwards [ae_all_iff.mpr hc] with x hx
  ext j
  simpa only [curveGradient, stateRealGradientField, stateImagGradientField,
    Pi.add_apply, PiLp.add_apply, state_complexGradient_coordinate] using hx j

theorem curveGradient_neg_slice (g : ℝ → EnergyState) (t : ℝ) :
    curveGradient (-g) t =ᵐ[volume] fun x => -curveGradient g t x := by
  have hc (j : Fin 3) : (energyGradient j (-g t) : Space → ℂ) =ᵐ[volume]
      fun x => -energyGradient j (g t) x := by
    rw [map_neg]
    exact Lp.coeFn_neg (energyGradient j (g t))
  filter_upwards [ae_all_iff.mpr hc] with x hx
  ext j
  simpa only [curveGradient, stateRealGradientField, stateImagGradientField,
    Pi.neg_apply, PiLp.neg_apply, state_complexGradient_coordinate] using hx j

private theorem value_add_le (g h : ℝ → EnergyState) (hg : Continuous g) (hh : Continuous h)
    {p q : ℝ≥0∞} (hp : 1 ≤ p) (hq : 1 ≤ q) (hqt : q ≠ ∞) :
    mixedNorm volume volume p q (stateValueField (g+h)) ≤
      mixedNorm volume volume p q (stateValueField g) +
      mixedNorm volume volume p q (stateValueField h) := by
  let r := energyJointFields volume g hg.aestronglyMeasurable
  let s := energyJointFields volume h hh.aestronglyMeasurable
  have he : mixedNorm volume volume p q (stateValueField (g+h)) =
      mixedNorm volume volume p q (fun t x => r.u t x+s.u t x) := by
    apply eLpNorm_congr_ae
    filter_upwards [r.slice_eq,s.slice_eq] with t hr hs
    apply eLpNorm_congr_ae
    filter_upwards [hr.1,hs.1,Lp.coeFn_add (energyValue (g t)) (energyValue (h t))]
      with x hrg hsh hadd
    simpa only [stateValueField,Pi.add_apply,map_add,hrg,hsh] using hadd
  rw [he]
  exact (mixed_add_le hp hq hqt _ _ r.joint_u.aestronglyMeasurable
    s.joint_u.aestronglyMeasurable).trans_eq
    (congrArg₂ (·+·) (joint_value_norm g r p q) (joint_value_norm h s p q))

private theorem gradient_add_le (g h : ℝ → EnergyState) (hg : Continuous g) (hh : Continuous h)
    {p q : ℝ≥0∞} (hp : 1 ≤ p) (hq : 1 ≤ q) (hqt : q ≠ ∞) :
    mixedNorm volume volume p q (curveGradient (g+h)) ≤
      mixedNorm volume volume p q (curveGradient g) +
      mixedNorm volume volume p q (curveGradient h) := by
  let r := energyJointFields volume g hg.aestronglyMeasurable
  let s := energyJointFields volume h hh.aestronglyMeasurable
  have he : mixedNorm volume volume p q (curveGradient (g+h)) =
      mixedNorm volume volume p q (fun t x => complexGradient (r.U t) (r.V t) x+
        complexGradient (s.U t) (s.V t) x) := by
    apply eLpNorm_congr_ae
    filter_upwards [r.slice_eq,s.slice_eq] with t hr hs
    apply eLpNorm_congr_ae
    filter_upwards [curveGradient_add_slice g h t,hr.2.1,hr.2.2,hs.2.1,hs.2.2]
      with x ha hru hrv hsu hsv
    simpa only [curveGradient,stateRealGradientField,stateImagGradientField,
      complexGradient,hru,hrv,hsu,hsv] using ha
  rw [he]
  exact (mixed_add_le hp hq hqt _ _
    (packedGradient_joint_measurable r.joint_U.aestronglyMeasurable r.joint_V.aestronglyMeasurable)
    (packedGradient_joint_measurable s.joint_U.aestronglyMeasurable s.joint_V.aestronglyMeasurable)).trans_eq
    (congrArg₂ (·+·) (joint_gradient_norm g r p q) (joint_gradient_norm h s p q))

theorem curveX_add_le (g h : ℝ → EnergyState) (hg : Continuous g) (hh : Continuous h) :
    curveX (g+h) ≤ curveX g+curveX h := by
  have he : curveEnergy (g+h) ≤ curveEnergy g+curveEnergy h := by
    simp_rw [curveEnergy_eq_actual _ (hg.add hh),curveEnergy_eq_actual g hg,
      curveEnergy_eq_actual h hh,← curveGradient_eq_actual]
    exact gradient_add_le g h hg hh (by simp) (by norm_num) (by norm_num)
  have hs : curveS (g+h) ≤ curveS g+curveS h :=
    value_add_le g h hg hh (by norm_num) (by norm_num) (by norm_num)
  have hw : curveW (g+h) ≤ curveW g+curveW h :=
    gradient_add_le g h hg hh (by norm_num) (by norm_num) ENNReal.ofReal_ne_top
  exact (add_le_add (add_le_add he hs) hw).trans_eq (by unfold curveX; ring)

theorem curveX_neg (g : ℝ → EnergyState) : curveX (-g) = curveX g := by
  have he : curveEnergy (-g)=curveEnergy g := by
    unfold curveEnergy
    congr 1
    funext t
    simp only [Pi.neg_apply,pureGradientNorm_eq_norm_gradientVector,map_neg,norm_neg]
  have hs : curveS (-g)=curveS g := by
    apply eLpNorm_congr_ae
    filter_upwards [] with t
    change eLpNorm (energyValue (-g t)) 10 volume = _
    rw [map_neg,eLpNorm_congr_ae (Lp.coeFn_neg _),eLpNorm_neg]
  have hw : curveW (-g)=curveW g := by
    apply eLpNorm_congr_ae
    filter_upwards [] with t
    rw [eLpNorm_congr_ae (curveGradient_neg_slice g t)]
    exact eLpNorm_neg _ _ _
  simp only [curveX,he,hs,hw]

theorem curveX_sub_le (g h : ℝ → EnergyState) (hg : Continuous g) (hh : Continuous h) :
    curveX (g-h) ≤ curveX g+curveX h := by
  simpa only [sub_eq_add_neg,curveX_neg] using curveX_add_le g (-h) hg hh.neg

theorem CurveFinite.add {g h : ℝ → EnergyState} (hg : CurveFinite g) (hh : CurveFinite h) :
    CurveFinite (g+h) := by
  apply CurveFinite.of_le (hg.continuous.add hh.continuous)
  exact (curveX_add_le g h hg.continuous hh.continuous).trans_eq (by
    rw [← ofReal_xNorm hg,← ofReal_xNorm hh,
      ← ENNReal.ofReal_add (xNorm_nonneg g) (xNorm_nonneg h)])

theorem CurveFinite.sub {g h : ℝ → EnergyState} (hg : CurveFinite g) (hh : CurveFinite h) :
    CurveFinite (g-h) := by
  apply CurveFinite.of_le (hg.continuous.sub hh.continuous)
  exact (curveX_sub_le g h hg.continuous hh.continuous).trans_eq (by
    rw [← ofReal_xNorm hg,← ofReal_xNorm hh,
      ← ENNReal.ofReal_add (xNorm_nonneg g) (xNorm_nonneg h)])

theorem xNorm_add_le {g h : ℝ → EnergyState} (hg : CurveFinite g) (hh : CurveFinite h) :
    xNorm (g+h) ≤ xNorm g+xNorm h := by
  apply xNorm_le (add_nonneg (xNorm_nonneg g) (xNorm_nonneg h))
  exact (curveX_add_le g h hg.continuous hh.continuous).trans_eq (by
    rw [← ofReal_xNorm hg,← ofReal_xNorm hh,
      ← ENNReal.ofReal_add (xNorm_nonneg g) (xNorm_nonneg h)])

theorem xNorm_sub_le {g h : ℝ → EnergyState} (hg : CurveFinite g) (hh : CurveFinite h) :
    xNorm (g-h) ≤ xNorm g+xNorm h := by
  apply xNorm_le (add_nonneg (xNorm_nonneg g) (xNorm_nonneg h))
  exact (curveX_sub_le g h hg.continuous hh.continuous).trans_eq (by
    rw [← ofReal_xNorm hg,← ofReal_xNorm hh,
      ← ENNReal.ofReal_add (xNorm_nonneg g) (xNorm_nonneg h)])

/-- Zero is handled through the actual Lp classes, never by a pointwise
assertion about a quotient-selected representative. -/
@[simp] theorem curveX_zero : curveX (0 : ℝ → EnergyState)=0 := by
  have he : curveEnergy (0 : ℝ → EnergyState)=0 := by
    simp [curveEnergy,pureGradientNorm_eq_norm_gradientVector]
  have hs : curveS (0 : ℝ → EnergyState)=0 := by
    unfold curveS mixedNorm
    have hslice (t : ℝ) : eLpNorm (stateValueField (0 : ℝ → EnergyState) t) 10 volume=0 := by
      change eLpNorm (energyValue (0 : EnergyState)) 10 volume=0
      rw [map_zero,eLpNorm_congr_ae (Lp.coeFn_zero ℂ 6 (volume : Measure Space)),eLpNorm_zero]
    simp only [hslice,eLpNorm_fun_zero]
  have hw : curveW (0 : ℝ → EnergyState)=0 := by
    have hslice (t : ℝ) : curveGradient (0 : ℝ → EnergyState) t =ᵐ[volume] 0 := by
      have hc (j : Fin 3) : (energyGradient j (0 : EnergyState) : Space → ℂ) =ᵐ[volume] 0 := by
        rw [map_zero]
        exact Lp.coeFn_zero ℂ 2 (volume : Measure Space)
      filter_upwards [ae_all_iff.mpr hc] with x hx
      ext j
      simpa only [curveGradient,stateRealGradientField,stateImagGradientField,Pi.zero_apply,
        state_complexGradient_coordinate, PiLp.zero_apply] using hx j
    unfold curveW mixedNorm
    have hn (t : ℝ) : eLpNorm (curveGradient (0 : ℝ → EnergyState) t)
        (ENNReal.ofReal (30/13 : ℝ)) volume=0 := by
      rw [eLpNorm_congr_ae (hslice t),eLpNorm_zero]
    simp only [hn,eLpNorm_fun_zero]
  simp only [curveX,he,hs,hw,zero_add]

@[simp] theorem xNorm_zero : xNorm (0 : ℝ → EnergyState)=0 := by
  simp only [xNorm,curveX_zero,ENNReal.toReal_zero]

theorem CurveFinite.zero : CurveFinite (0 : ℝ → EnergyState) := by
  apply CurveFinite.of_le (g := (0 : ℝ → EnergyState)) continuous_const (R := 0)
  rw [curveX_zero, ENNReal.ofReal_zero]

end HartreeF.R2Global
