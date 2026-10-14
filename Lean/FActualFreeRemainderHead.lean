import FActualFreeRemainderCompactness
import FActualFreeHeadApproximation
import FFreeHeadAffineSlots

/-! Fixed finite-head coefficient closure for the ACTUAL free remainder.
All profiles retain their explicit continuity/E/S/W hypotheses. The single
physical free field has no profile label. Every index has signed fibre domains
and genuine mixed domains before any limit or real-norm conversion.
Author-source candidate, UNCOMPILED. No nonlinear profile construction, infinite
tail conclusion, or small free-remainder assumption is made here. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
namespace HartreeF.ActualFreeRemainderHead
open EnergySpace SobolevStretch StationarySelfTest ProfileEnergy ActualStrichartz CriticalTimeSobolev
  TimeHolder ProfileApproximation GeneralProfileCross CompactCross LocalProfileProducts
  FreeRemainderInputs FreeHeadSlots FreeHeadFrames CriticalAffine ForcingDomain
  DerivativeMajorization ProfileSpatialSmoothing

/-- This is ONE physical field, independent of the profile label j. -/
def physicalFreeGradient (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) (P : LinearProfileFamily) (u : ℕ → EnergyState)
    (J : ℕ) (k : Fin 3) (n : ℕ) : ℝ → Space → ℂ :=
  freeJoint (energyGradient k (profileRemainder hDensity hSob P u J n))

def physicalProfileValue (P : LinearProfileFamily) (j : ℕ)
    (U : ℝ → Space → ℂ) (n : ℕ) : ℝ → Space → ℂ :=
  seedFrame (P.scale j n) (P.center j n) (P.time j n) (1/2) U

/-- For each time separately, only the countable n-family and finite label/
coordinate families are intersected. There is no uncountable AE intersection
and the left side remains the SAME physical field for every j. -/
theorem physicalFreeGradient_all_frame_ae (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) (P : LinearProfileFamily) (u : ℕ → EnergyState)
    (J : ℕ) (t : ℝ) :
    ∀ᵐ x ∂volume, ∀ (n : ℕ) (j : Fin J) (k : Fin 3),
      physicalFreeGradient hDensity hSob P u J k n t x =
        seedFrame (P.scale j.val n) (P.center j.val n) (P.time j.val n) (3/2)
          (normalizedFreeGradient hDensity hSob P u J j.val k n) t x := by
  apply ae_all_iff.mpr
  intro n
  apply ae_all_iff.mpr
  intro j
  apply ae_all_iff.mpr
  intro k
  exact remainder_free_gradient_frame_ae hDensity hSob P u J j.val n k t

/-- A literal forcing sequence, with its domain and limit kept together. -/
structure ForcingSequenceZero (F : ℕ → ℝ → Space → ℂ) : Prop where
  joint : ∀ n, AEStronglyMeasurable (Function.uncurry (F n)) (volume.prod volume)
  finite : ∀ n, forcingNorm (F n) ≠ ∞
  zero : Tendsto (fun n => forcingNorm (F n)) atTop (𝓝 0)

/-- Actual spatial membership and the actual outer time-domain follow at EVERY
index. No use is made of toReal on an unverified infinite slice. -/
theorem ForcingSequenceZero.domains {F : ℕ → ℝ → Space → ℂ}
    (hF : ForcingSequenceZero F) (n : ℕ) :
    (∀ᵐ t ∂volume, MemLp (F n t) (ENNReal.ofReal (6/5 : ℝ)) volume) ∧
    MemLp (fun t => eLpNorm (F n t) (ENNReal.ofReal (6/5 : ℝ)) volume) 2 volume := by
  exact ⟨finite_mixedNorm_ae_slice_memLp volume volume 2 _ (by norm_num)
    (by norm_num) (F n) (hF.finite n), lt_top_iff_ne_top.mpr (hF.finite n)⟩

theorem ForcingSequenceZero.real_zero {F : ℕ → ℝ → Space → ℂ}
    (hF : ForcingSequenceZero F) :
    Tendsto (fun n => (forcingNorm (F n)).toReal) atTop (𝓝 0) := by
  simpa only [Function.comp_def, ENNReal.toReal_zero] using
    (ENNReal.tendsto_toReal (by simp : (0 : ℝ≥0∞) ≠ ∞)).comp hF.zero

private theorem forcingSequenceZero_zero :
    ForcingSequenceZero (fun (_ : ℕ) (_ : ℝ) (_ : Space) => (0 : ℂ)) := by
  refine ⟨fun _ => aestronglyMeasurable_const, ?_, ?_⟩
  · intro n
    simp [forcingNorm, mixedNorm]
  · simpa only [forcingNorm, mixedNorm, eLpNorm_fun_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ≥0∞)) atTop (𝓝 0))

/-- The triangle step uses genuine joint measurability of both literal fields. -/
theorem ForcingSequenceZero.add {F G : ℕ → ℝ → Space → ℂ}
    (hF : ForcingSequenceZero F) (hG : ForcingSequenceZero G) :
    ForcingSequenceZero (fun n t x => F n t x + G n t x) := by
  have hb (n : ℕ) : forcingNorm (fun t x => F n t x + G n t x) ≤
      forcingNorm (F n) + forcingNorm (G n) :=
    mixed_add_le (by norm_num) (by norm_num) ENNReal.ofReal_ne_top
      (F n) (G n) (hF.joint n) (hG.joint n)
  refine ⟨fun n => (hF.joint n).add (hG.joint n), ?_, ?_⟩
  · intro n
    exact ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hF.finite n,hG.finite n⟩) (hb n)
  · apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (show Tendsto (fun n => forcingNorm (F n)+forcingNorm (G n)) atTop (𝓝 0) from
        by simpa only [zero_add] using hF.zero.add hG.zero)
      (fun _ => bot_le) hb

/-- A finite sum preserves the actual N domain and original-sequence limit.
This is deliberately a finite-set lemma, with no summability claim. -/
theorem ForcingSequenceZero.sum {ι : Type*} (s : Finset ι)
    (F : ι → ℕ → ℝ → Space → ℂ)
    (hF : ∀ j ∈ s, ForcingSequenceZero (F j)) :
    ForcingSequenceZero (fun n t x => ∑ j ∈ s, F j n t x) := by
  classical
  revert hF
  induction s using Finset.induction_on with
  | empty =>
      intro _hF
      simpa only [Finset.sum_empty] using forcingSequenceZero_zero
  | @insert j s hj ih =>
      intro hF
      have hs := ih (fun i hi => hF i (Finset.mem_insert_of_mem hi))
      have ha := (hF j (Finset.mem_insert_self j s)).add hs
      simpa only [Finset.sum_insert hj] using ha

/-- The per-profile endpoint includes independent signed fibre witnesses,
true Q/N mixed domains, all-index finiteness, and all three limits. -/
structure HeadSlotDecay (α c : ℝ) (U H : ℕ → ℝ → Space → ℂ) : Prop where
  fibres : ∀ n, SignedFibreDomains α c (U n) (H n)
  mixed : ∀ n, HeadMixedDomains α c (U n) (H n)
  Q_finite : ∀ n, localProductNorm (ENNReal.ofReal (15/8 : ℝ)) (U n) (H n) ≠ ∞
  Q_zero : Tendsto (fun n => localProductNorm (ENNReal.ofReal (15/8 : ℝ))
    (U n) (H n)) atTop (𝓝 0)
  inner : ForcingSequenceZero (fun n => innerCross α c (U n) (H n) (U n))
  outer : ForcingSequenceZero (fun n => outerCross α c (U n) (U n) (H n))

theorem HeadSlotDecay.Q_real_zero {α c : ℝ} {U H : ℕ → ℝ → Space → ℂ}
    (h : HeadSlotDecay α c U H) :
    Tendsto (fun n => (localProductNorm (ENNReal.ofReal (15/8 : ℝ))
      (U n) (H n)).toReal) atTop (𝓝 0) := by
  simpa only [Function.comp_def, ENNReal.toReal_zero] using
    (ENNReal.tendsto_toReal (by simp : (0 : ℝ≥0∞) ≠ ∞)).comp h.Q_zero

/-- Signed integrability is transported by actual spatial AE equality, before
any totalized integral or norm is used. -/
theorem signedFibreDomains_congr_nested_ae {α c : ℝ}
    {u U h H : ℝ → Space → ℂ} (hf : SignedFibreDomains α c u h)
    (hu : ∀ᵐ t ∂volume, u t =ᵐ[volume] U t)
    (hh : ∀ᵐ t ∂volume, h t =ᵐ[volume] H t) : SignedFibreDomains α c U H := by
  constructor
  · filter_upwards [hf.inner,hu,hh] with t ht hut hht
    filter_upwards [ht] with x hx
    apply hx.congr
    filter_upwards [hut,hht] with y huy hhy
    simp only [directionalDensity,huy,hhy]
  · filter_upwards [hf.outer,hu] with t ht hut
    filter_upwards [ht] with x hx
    apply hx.congr
    filter_upwards [hut] with y huy
    simp only [powerDensity,huy]

/-- Actual fixed eligible-depth, active-label theorem. The same inverse-frame
coordinate supplies the E/W caps, local L2 domain and original-sequence limit;
then its frame is identified with the one physical remainder free field. -/
theorem actual_physical_free_head_slots
    (hDensity : OrdinaryH1Density) {α c K B C : ℝ}
    (hHLS : OrdinaryHLS α c) (hSob : OrdinarySobolev K)
    (hStr : OrdinaryHomogeneousStrichartz C) (q : Highpass.Cutoff)
    (P : LinearProfileFamily) (u : ℕ → EnergyState)
    (hB : ∀ n, pureGradientNorm (u n) ≤ B)
    (hp : LinearProfileProperties hDensity hSob u P)
    (J j : ℕ) (hj : j < J) (hJ : (J : WithTop ℕ) ≤ P.count)
    (g : ℝ → EnergyState) (hg : Continuous g) (hgE : curveEnergy g ≠ ∞)
    (hgS : mixedNorm volume volume 10 10 (stateValueField g) ≠ ∞)
    (hgW : mixedNorm volume volume 10 (ENNReal.ofReal (30/13 : ℝ))
      (fun t => complexGradient (stateRealGradientField g t) (stateImagGradientField g t)) ≠ ∞)
    (r : EnergyJointFields volume g) (k : Fin 3) :
    HeadSlotDecay α c (physicalProfileValue P j r.u)
      (physicalFreeGradient hDensity hSob P u J k) := by
  let h := normalizedFreeGradient hDensity hSob P u J j k
  let bE : ℝ≥0 := (ENNReal.ofReal (headGradientCap B P J)).toNNReal
  let bW : ℝ≥0 := (ENNReal.ofReal (C*headGradientCap B P J)).toNNReal
  have hbE : (bE : ℝ≥0∞) = ENNReal.ofReal (headGradientCap B P J) :=
    ENNReal.coe_toNNReal ENNReal.ofReal_ne_top
  have hbW : (bW : ℝ≥0∞) = ENNReal.ofReal (C*headGradientCap B P J) :=
    ENNReal.coe_toNNReal ENNReal.ofReal_ne_top
  have hh (n : ℕ) : StronglyMeasurable (Function.uncurry (h n)) :=
    normalizedFreeGradient_joint hDensity hSob P u J j k n
  have hE (n : ℕ) : mixedNorm volume volume ∞ 2 (h n) ≤ bE := by
    rw [hbE]
    exact (normalizedFreeGradient_bounds hDensity hSob hStr P u hB J j k n).1
  have hW (n : ℕ) : mixedNorm volume volume 10 (ENNReal.ofReal (30/13 : ℝ)) (h n) ≤ bW := by
    rw [hbW]
    exact (normalizedFreeGradient_bounds hDensity hSob hStr P u hB J j k n).2
  have hlf (T R : ℝ) (z : Space) (_hT : 0 < T) (_hR : 0 < R) (n : ℕ) :
      cylinderL2 T R z (h n) ≠ ∞ :=
    normalizedFreeGradient_local_finite hDensity hSob P u J j k n T R z
  have hl0 (T R : ℝ) (z : Space) (hT : 0 < T) (hR : 0 < R) :
      Tendsto (fun n => cylinderL2 T R z (h n)) atTop (𝓝 0) :=
    normalizedFreeGradient_local_tendsto hDensity hSob q P u hB hp J j hj hJ k hT hR z
  have hs := actual_free_head_slots hHLS hSob g hg hgE hgS hgW r hh bE bW hE hW hlf hl0
  let U := physicalProfileValue P j r.u
  let H := physicalFreeGradient hDensity hSob P u J k
  let Hf (n : ℕ) := seedFrame (P.scale j n) (P.center j n) (P.time j n) (3/2) (h n)
  have hU (n : ℕ) : StronglyMeasurable (Function.uncurry (U n)) :=
    seedFrame_joint_stronglyMeasurable (P.scale j n) (P.center j n) (P.time j n)
      (1/2) r.u r.joint_u
  have hH (n : ℕ) : StronglyMeasurable (Function.uncurry (H n)) :=
    freeJoint_stronglyMeasurable _
  have he (n : ℕ) : ∀ᵐ t ∂volume, H n t =ᵐ[volume] Hf n t :=
    Eventually.of_forall (fun t => remainder_free_gradient_frame_ae
      hDensity hSob P u J j n k t)
  have hself (n : ℕ) : ∀ᵐ t ∂volume, U n t =ᵐ[volume] U n t :=
    Eventually.of_forall (fun _ => Filter.EventuallyEq.rfl)
  have hQeq (n : ℕ) : localProductNorm (ENNReal.ofReal (15/8 : ℝ)) (U n) (H n) =
      localProductNorm (ENNReal.ofReal (15/8 : ℝ)) r.u (h n) := by
    exact (localProductNorm_congr_nested_ae _ (hself n) (he n)).trans
      (seedFrame_Q (P.scale_pos j n) (P.center j n) (P.time j n) r.u (h n)
        r.joint_u.aestronglyMeasurable (hh n).aestronglyMeasurable)
  have hieq (n : ℕ) : forcingNorm (innerCross α c (U n) (H n) (U n)) =
      forcingNorm (innerCross α c r.u (h n) r.u) := by
    exact (innerCross_forcingNorm_congr_nested_ae α c (hself n) (he n) (hself n)).trans
      (seedFrame_inner_N α c (P.scale_pos j n) (P.center j n) (P.time j n) r.u (h n) r.u
        r.joint_u.aestronglyMeasurable (hh n).aestronglyMeasurable r.joint_u.aestronglyMeasurable)
  have hoeq (n : ℕ) : forcingNorm (outerCross α c (U n) (U n) (H n)) =
      forcingNorm (outerCross α c r.u r.u (h n)) := by
    exact (outerCross_forcingNorm_congr_nested_ae α c (hself n) (hself n) (he n)).trans
      (seedFrame_outer_N hHLS.order_pos c (P.scale_pos j n) (P.center j n) (P.time j n)
        r.u r.u (h n) r.joint_u.aestronglyMeasurable r.joint_u.aestronglyMeasurable
        (hh n).aestronglyMeasurable)
  have hQfin (n : ℕ) : localProductNorm (ENNReal.ofReal (15/8 : ℝ)) (U n) (H n) ≠ ∞ := by
    rw [hQeq n]
    exact (hs.1 n).2.1
  have hifin (n : ℕ) : forcingNorm (innerCross α c (U n) (H n) (U n)) ≠ ∞ := by
    rw [hieq n]
    exact (hs.1 n).2.2.1
  have hofin (n : ℕ) : forcingNorm (outerCross α c (U n) (U n) (H n)) ≠ ∞ := by
    rw [hoeq n]
    exact (hs.1 n).2.2.2
  refine ⟨?_,?_,hQfin,?_,?_,?_⟩
  · intro n
    have hframe : SignedFibreDomains α c (U n) (Hf n) := by
      exact ⟨directional_fibre_parabolic α c (inv_pos.mpr (P.scale_pos j n))
          (-((P.scale j n)⁻¹ • P.center j n)) (P.time j n) r.u (h n) (hs.1 n).1.inner,
        density_fibre_parabolic α c (inv_pos.mpr (P.scale_pos j n))
          (-((P.scale j n)⁻¹ • P.center j n)) (P.time j n) r.u (hs.1 n).1.outer⟩
    exact signedFibreDomains_congr_nested_ae hframe (hself n)
      ((he n).mono (fun _ ht => ht.symm))
  · intro n
    exact head_mixed_domains_of_finite (hU n).aestronglyMeasurable
      (hH n).aestronglyMeasurable (hQfin n) (hifin n) (hofin n)
  · have hnorm : (fun n => localProductNorm (ENNReal.ofReal (15/8 : ℝ)) (U n) (H n)) =
        (fun n => localProductNorm (ENNReal.ofReal (15/8 : ℝ)) r.u (h n)) := funext hQeq
    rw [hnorm]
    exact hs.2.1
  · refine ⟨fun n => innerCross_joint α c (hU n).aestronglyMeasurable
        (hH n).aestronglyMeasurable (hU n).aestronglyMeasurable, hifin, ?_⟩
    have hnorm : (fun n => forcingNorm (innerCross α c (U n) (H n) (U n))) =
        (fun n => forcingNorm (innerCross α c r.u (h n) r.u)) := funext hieq
    rw [hnorm]
    exact hs.2.2.1
  · refine ⟨fun n => outerCross_joint α c (hU n).aestronglyMeasurable
        (hU n).aestronglyMeasurable (hH n).aestronglyMeasurable, hofin, ?_⟩
    have hnorm : (fun n => forcingNorm (outerCross α c (U n) (U n) (H n))) =
        (fun n => forcingNorm (outerCross α c r.u r.u (h n))) := funext hoeq
    rw [hnorm]
    exact hs.2.2.2

/-- The canonical value field of g gives the SAME physical Q and the SAME
literal slots, by nested AE transport. No joint-measurability assertion about
pointwise canonical EnergyState representatives is required. -/
theorem canonical_physical_slot_norms (hDensity : OrdinaryH1Density) {α c K : ℝ}
    (hSob : OrdinarySobolev K) (P : LinearProfileFamily) (u : ℕ → EnergyState)
    (J j : ℕ) (g : ℝ → EnergyState) (r : EnergyJointFields volume g) (k : Fin 3) (n : ℕ) :
    let U := physicalProfileValue P j (stateValueField g) n
    let V := physicalProfileValue P j r.u n
    let H := physicalFreeGradient hDensity hSob P u J k n
    (∀ᵐ t ∂volume, U t =ᵐ[volume] V t) ∧
    localProductNorm (ENNReal.ofReal (15/8 : ℝ)) U H =
      localProductNorm (ENNReal.ofReal (15/8 : ℝ)) V H ∧
    forcingNorm (innerCross α c U H U) = forcingNorm (innerCross α c V H V) ∧
    forcingNorm (outerCross α c U U H) = forcingNorm (outerCross α c V V H) := by
  have hv := seedFrame_jointFields_value_nested_ae g r (P.scale_pos j n)
    (P.center j n) (P.time j n)
  have hh : ∀ᵐ t ∂volume, physicalFreeGradient hDensity hSob P u J k n t =ᵐ[volume]
      physicalFreeGradient hDensity hSob P u J k n t :=
    Eventually.of_forall (fun _ => Filter.EventuallyEq.rfl)
  exact ⟨hv,localProductNorm_congr_nested_ae _ hv hh,
    innerCross_forcingNorm_congr_nested_ae α c hv hh hv,
    outerCross_forcingNorm_congr_nested_ae α c hv hv hh⟩

/-- The fixed-head result covers every active j and all three coordinates.
Finite sums of the two literal placements, separately and together, use the
same physical free field. Fin 0 makes the zero-count case the empty sum. -/
theorem actual_fixed_head_free_slots
    (hDensity : OrdinaryH1Density) {α c K B C : ℝ}
    (hHLS : OrdinaryHLS α c) (hSob : OrdinarySobolev K)
    (hStr : OrdinaryHomogeneousStrichartz C) (q : Highpass.Cutoff)
    (P : LinearProfileFamily) (u : ℕ → EnergyState)
    (hB : ∀ n, pureGradientNorm (u n) ≤ B)
    (hp : LinearProfileProperties hDensity hSob u P)
    (J : ℕ) (hJ : (J : WithTop ℕ) ≤ P.count)
    (g : Fin J → ℝ → EnergyState) (hg : ∀ j, Continuous (g j))
    (hgE : ∀ j, curveEnergy (g j) ≠ ∞)
    (hgS : ∀ j, mixedNorm volume volume 10 10 (stateValueField (g j)) ≠ ∞)
    (hgW : ∀ j, mixedNorm volume volume 10 (ENNReal.ofReal (30/13 : ℝ))
      (fun t => complexGradient (stateRealGradientField (g j) t)
        (stateImagGradientField (g j) t)) ≠ ∞)
    (r : ∀ j, EnergyJointFields volume (g j)) :
    let U := fun j : Fin J => physicalProfileValue P j.val (r j).u
    let H := physicalFreeGradient hDensity hSob P u J
    (∀ (j : Fin J) (k : Fin 3), HeadSlotDecay α c (U j) (H k)) ∧
    ∀ k : Fin 3,
      ForcingSequenceZero (fun n t x => ∑ j : Fin J,
        innerCross α c (U j n) (H k n) (U j n) t x) ∧
      ForcingSequenceZero (fun n t x => ∑ j : Fin J,
        outerCross α c (U j n) (U j n) (H k n) t x) ∧
      ForcingSequenceZero (fun n t x => ∑ j : Fin J,
        (innerCross α c (U j n) (H k n) (U j n) t x +
          outerCross α c (U j n) (U j n) (H k n) t x)) := by
  dsimp only
  have hs (j : Fin J) (k : Fin 3) := actual_physical_free_head_slots hDensity hHLS hSob
    hStr q P u hB hp J j.val j.isLt hJ (g j) (hg j) (hgE j) (hgS j) (hgW j) (r j) k
  refine ⟨hs,?_⟩
  intro k
  exact ⟨ForcingSequenceZero.sum Finset.univ _ (fun j _ => (hs j k).inner),
    ForcingSequenceZero.sum Finset.univ _ (fun j _ => (hs j k).outer),
    ForcingSequenceZero.sum Finset.univ _ (fun j _ => (hs j k).inner.add (hs j k).outer)⟩

/-- Padded depths are reduced to the actual finite terminal count first.
No weak-zero or orthogonality premise is introduced for an inactive label. -/
theorem physicalFreeGradient_finite_padding (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) (P : LinearProfileFamily) (u : ℕ → EnergyState)
    (N J : ℕ) (hcount : P.count = (N : WithTop ℕ)) (hNJ : N ≤ J) (k : Fin 3) :
    physicalFreeGradient hDensity hSob P u J k =
      physicalFreeGradient hDensity hSob P u N k := by
  funext n
  unfold physicalFreeGradient
  rw [profileRemainder_finite_padding hDensity hSob P u N J n hcount hNJ]

end HartreeF.ActualFreeRemainderHead
