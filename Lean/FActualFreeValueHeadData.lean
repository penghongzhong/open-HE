import FActualFreeRemainderHead
import FFiniteProfileFrameData
import FFiniteProfileWeakGradient
import FFreeValueFullCandidate

/-! Actual finite-head fields for the selected free-value estimate.  The head
contains the labels below min(L,J), but every free remainder stays at depth J.
This is static author source, UNCOMPILED. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
namespace HartreeF.ActualFreeValueHeadData
open EnergySpace SobolevStretch CriticalTimeSobolev ProfileEnergy ActualStrichartz
  TimeHolder ProfileApproximation ProfileSpatialSmoothing GeneralProfileCross
  CompactCross LocalProfileProducts FiniteProfileMixedDefects FiniteProfileWeakGradient
  FiniteProfileFrameData ActualFreeRemainderHead FreeValueFullCandidate WeakHartreeProduct StationarySelfTest ForcingDomain

/-- Exactly the actual active prefix below both L and the retained depth J. -/
def headSet (L J : ℕ) : Finset (Fin L) := Finset.univ.filter (fun j => j.val < J)

@[simp] theorem mem_headSet {L J : ℕ} (j : Fin L) :
    j ∈ headSet L J ↔ j.val < J := by simp [headSet]

theorem headSet_min {L J : ℕ} (j : Fin L) :
    j ∈ headSet L J ↔ j.val < min J L := by
  rw [mem_headSet, lt_min_iff]
  exact ⟨fun h => ⟨h, j.isLt⟩, And.left⟩

variable {L : ℕ} {g : Fin L → ℝ → EnergyState}

def headValue (P : LinearProfileFamily) (r : ∀ j, EnergyJointFields volume (g j))
    (J n : ℕ) : ℝ → Space → ℂ := fun t x =>
  ∑ j ∈ headSet L J, framedJointValue (r j) (P.scale j.val n)
    (P.center j.val n) (P.time j.val n) t x

def headReal (P : LinearProfileFamily) (r : ∀ j, EnergyJointFields volume (g j))
    (J n : ℕ) : ℝ → Space → Space := fun t x =>
  ∑ j ∈ headSet L J, framedJointReal (r j) (P.scale j.val n)
    (P.center j.val n) (P.time j.val n) t x

def headImag (P : LinearProfileFamily) (r : ∀ j, EnergyJointFields volume (g j))
    (J n : ℕ) : ℝ → Space → Space := fun t x =>
  ∑ j ∈ headSet L J, framedJointImag (r j) (P.scale j.val n)
    (P.center j.val n) (P.time j.val n) t x

def headDirection (P : LinearProfileFamily) (r : ∀ j, EnergyJointFields volume (g j))
    (J : ℕ) (k : Fin 3) (n : ℕ) : ℝ → Space → ℂ := fun t x =>
  ∑ j ∈ headSet L J, seedFrame (P.scale j.val n) (P.center j.val n) (P.time j.val n)
    (3/2) (gradientCoordinate k (fun t => complexGradient ((r j).U t) ((r j).V t))) t x

theorem head_joint (P : LinearProfileFamily) (r : ∀ j, EnergyJointFields volume (g j))
    (J n : ℕ) :
    StronglyMeasurable (Function.uncurry (headValue P r J n)) ∧
    StronglyMeasurable (Function.uncurry (headReal P r J n)) ∧
    StronglyMeasurable (Function.uncurry (headImag P r J n)) := by
  refine ⟨?_, ?_, ?_⟩
  · exact Finset.stronglyMeasurable_fun_sum (headSet L J) (fun j _ =>
      (framedJoint_joint_measurable (r j) (P.scale j.val n)
        (P.center j.val n) (P.time j.val n)).1)
  · exact Finset.stronglyMeasurable_fun_sum (headSet L J) (fun j _ =>
      (framedJoint_joint_measurable (r j) (P.scale j.val n)
        (P.center j.val n) (P.time j.val n)).2.1)
  · exact Finset.stronglyMeasurable_fun_sum (headSet L J) (fun j _ =>
      (framedJoint_joint_measurable (r j) (P.scale j.val n)
        (P.center j.val n) (P.time j.val n)).2.2)

/-- The original canonical framed values, with exactly the same finite prefix. -/
def canonicalHeadValue (P : LinearProfileFamily) (g : Fin L → ℝ → EnergyState)
    (J n : ℕ) : ℝ → Space → ℂ := fun t x =>
  ∑ j ∈ headSet L J, framedValue (g j) (P.scale j.val n)
    (P.center j.val n) (P.time j.val n) t x

/-- Only the finite active family is intersected; no claim of joint measurability
for canonical quotient representatives is needed. -/
theorem head_canonical_nested_ae (P : LinearProfileFamily)
    (r : ∀ j, EnergyJointFields volume (g j)) (J n : ℕ) :
    ∀ᵐ t ∂volume, canonicalHeadValue P g J n t =ᵐ[volume] headValue P r J n t := by
  have he := (eventually_all_finset (headSet L J)).2 (fun j _ =>
    framedJoint_nested_ae (g j) (r j) (P.scale_pos j.val n)
      (P.center j.val n) (P.time j.val n))
  filter_upwards [he] with t ht
  have hx := (eventually_all_finset (headSet L J)).2 (fun j hj => (ht j hj).1)
  filter_upwards [hx] with x hxt
  exact Finset.sum_congr rfl (fun j hj => hxt j hj)

/-- The scalar direction is the true coordinate of the very same two real fields. -/
theorem head_directional (P : LinearProfileFamily)
    (r : ∀ j, EnergyJointFields volume (g j)) (J n : ℕ) (k : Fin 3) (t : ℝ) :
    directionalField (headReal P r J n t) (headImag P r J n t)
      (EuclideanSpace.basisFun (Fin 3) ℝ k) = headDirection P r J k n t := by
  change directionalField (fun x => ∑ j ∈ headSet L J,
    framedJointReal (r j) (P.scale j.val n) (P.center j.val n) (P.time j.val n) t x)
    (fun x => ∑ j ∈ headSet L J,
    framedJointImag (r j) (P.scale j.val n) (P.center j.val n) (P.time j.val n) t x) _ = _
  rw [directionalField_sum]
  funext x
  exact Finset.sum_congr rfl (fun j _ => congrFun
    (framedJoint_directionalField (r j) (P.scale j.val n)
      (P.center j.val n) (P.time j.val n) k t) x)

/-- Actual finite input domains alone; no target gradient or convergence hypothesis. -/
theorem profile_coordinate {K : ℝ} (hSob : OrdinarySobolev K)
    (hg : ∀ j, Continuous (g j)) (hE : ∀ j, curveEnergy (g j) ≠ ∞)
    (hS : ∀ j, mixedNorm volume volume 10 10 (stateValueField (g j)) ≠ ∞)
    (hW : ∀ j, mixedNorm volume volume 10 (ENNReal.ofReal (30/13 : ℝ))
      (fun t => complexGradient (stateRealGradientField (g j) t)
        (stateImagGradientField (g j) t)) ≠ ∞)
    (r : ∀ j, EnergyJointFields volume (g j)) (j : Fin L) (k : Fin 3) :
    ScalarProfile (r j).u
      (gradientCoordinate k (fun t => complexGradient ((r j).U t) ((r j).V t))) := by
  exact (Classical.choice (actual_coordinate_approximations hSob (g j) (hg j)
    (hE j) (hS j) (hW j) (r j)) k).profile

/-- Every prefix is a genuine scalar profile at every original index. -/
theorem head_profile {K : ℝ} (hSob : OrdinarySobolev K)
    (P : LinearProfileFamily) (hg : ∀ j, Continuous (g j))
    (hE : ∀ j, curveEnergy (g j) ≠ ∞)
    (hS : ∀ j, mixedNorm volume volume 10 10 (stateValueField (g j)) ≠ ∞)
    (hW : ∀ j, mixedNorm volume volume 10 (ENNReal.ofReal (30/13 : ℝ))
      (fun t => complexGradient (stateRealGradientField (g j) t)
        (stateImagGradientField (g j) t)) ≠ ∞)
    (r : ∀ j, EnergyJointFields volume (g j)) (J n : ℕ) (k : Fin 3) :
    ScalarProfile (headValue P r J n) (headDirection P r J k n) := by
  apply scalarProfile_sum
  intro j _
  exact (profile_coordinate hSob hg hE hS hW r j k).frame
    (P.scale_pos j.val n) (P.center j.val n) (P.time j.val n)

/-- Domain and weak-gradient transfer is from the original framed canonical fields. -/
theorem head_slices (P : LinearProfileFamily)
    (r : ∀ j, EnergyJointFields volume (g j))
    (hS : ∀ j, mixedNorm volume volume 10 10 (stateValueField (g j)) ≠ ∞)
    (hW : ∀ j, mixedNorm volume volume 10 (ENNReal.ofReal (30/13 : ℝ))
      (fun t => complexGradient (stateRealGradientField (g j) t)
        (stateImagGradientField (g j) t)) ≠ ∞) (J n : ℕ) :
    ∀ᵐ t ∂volume,
      InDotH1 (headValue P r J n t) (headReal P r J n t) (headImag P r J n t) ∧
      MemLp (headValue P r J n t) 10 volume ∧
      MemLp (headReal P r J n t) (ENNReal.ofReal (30/13 : ℝ)) volume ∧
      MemLp (headImag P r J n t) (ENNReal.ofReal (30/13 : ℝ)) volume := by
  have hc := (eventually_all_finset (headSet L J)).2 (fun j _ =>
    actual_frame_slices (g j) (P.scale_pos j.val n) (P.center j.val n)
      (P.time j.val n) (hS j) (hW j))
  have he := (eventually_all_finset (headSet L J)).2 (fun j _ =>
    framedJoint_nested_ae (g j) (r j) (P.scale_pos j.val n)
      (P.center j.val n) (P.time j.val n))
  filter_upwards [hc, he] with t ht het
  have hEach (j : Fin L) (hj : j ∈ headSet L J) := ht j hj
  refine ⟨inDotH1_sum (headSet L J) _ _ _ (fun j hj =>
    inDotH1_congr_fields (hEach j hj).1 (het j hj).1 (het j hj).2.1 (het j hj).2.2),
    memLp_finsetSum _ (fun j hj => (memLp_congr_ae (het j hj).1).mp (hEach j hj).2.1),
    memLp_finsetSum _ (fun j hj => (memLp_congr_ae (het j hj).2.1).mp (hEach j hj).2.2.1),
    memLp_finsetSum _ (fun j hj => (memLp_congr_ae (het j hj).2.2).mp (hEach j hj).2.2.2)⟩

/-- A single cap is fixed before J and n; it covers all prefixes and coordinates. -/
theorem head_uniform_cap {K : ℝ} (hSob : OrdinarySobolev K)
    (P : LinearProfileFamily) (hg : ∀ j, Continuous (g j))
    (hE : ∀ j, curveEnergy (g j) ≠ ∞)
    (hS : ∀ j, mixedNorm volume volume 10 10 (stateValueField (g j)) ≠ ∞)
    (hW : ∀ j, mixedNorm volume volume 10 (ENNReal.ofReal (30/13 : ℝ))
      (fun t => complexGradient (stateRealGradientField (g j) t)
        (stateImagGradientField (g j) t)) ≠ ∞)
    (r : ∀ j, EnergyJointFields volume (g j)) :
    ∃ b : ℝ≥0, ∀ J n k,
      mixedNorm volume volume ∞ 6 (headValue P r J n) ≤ b ∧
      mixedNorm volume volume 10 10 (headValue P r J n) ≤ b ∧
      mixedNorm volume volume 10 (ENNReal.ofReal (30/13 : ℝ))
        (headDirection P r J k n) ≤ b := by
  classical
  have hb (k : Fin 3) := finite_frame_uniform_bound (Finset.univ : Finset (Fin L))
    (fun j => (r j).u)
    (fun j => gradientCoordinate k (fun t => complexGradient ((r j).U t) ((r j).V t)))
    (fun j _ => profile_coordinate hSob hg hE hS hW r j k)
    (fun j n => P.scale j.val n) (fun j n => P.center j.val n)
    (fun j n => P.time j.val n) (fun j _ n => P.scale_pos j.val n)
  choose b hbound using hb
  refine ⟨∑ k : Fin 3, b k, fun J n k => ?_⟩
  have hk : (b k : ℝ≥0∞) ≤ ((∑ l : Fin 3, b l : ℝ≥0) : ℝ≥0∞) := by
    have hk0 : b k ≤ ∑ l : Fin 3, b l :=
      Finset.single_le_sum (fun l _ => (show (0 : ℝ≥0) ≤ b l from bot_le)) (Finset.mem_univ k)
    exact_mod_cast hk0
  have hsub (f : Fin L → ℝ≥0∞) : ∑ j ∈ headSet L J, f j ≤ ∑ j : Fin L, f j :=
    Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  refine ⟨?_, ?_, ?_⟩
  · exact (mixed_sum_le (headSet L J) (by simp) (by norm_num) (by norm_num) _
      (fun j _ => ((profile_coordinate hSob hg hE hS hW r j k).frame
        (P.scale_pos j.val n) (P.center j.val n) (P.time j.val n)).value_joint.aestronglyMeasurable)).trans
      ((hsub _).trans ((hbound k n).1.trans hk))
  · exact (mixed_sum_le (headSet L J) (by norm_num) (by norm_num) (by norm_num) _
      (fun j _ => ((profile_coordinate hSob hg hE hS hW r j k).frame
        (P.scale_pos j.val n) (P.center j.val n) (P.time j.val n)).value_joint.aestronglyMeasurable)).trans
      ((hsub _).trans ((hbound k n).2.1.trans hk))
  · exact (mixed_sum_le (headSet L J) (by norm_num) (by norm_num) (by norm_num) _
      (fun j _ => ((profile_coordinate hSob hg hE hS hW r j k).frame
        (P.scale_pos j.val n) (P.center j.val n) (P.time j.val n)).gradient_joint.aestronglyMeasurable)).trans
      ((hsub _).trans ((hbound k n).2.2.trans hk))

/-- Finite-head Q decay uses the retained remainder J, including when J<L. -/
theorem actual_head_Q_zero (hDensity : OrdinaryH1Density) {α c K B C : ℝ}
    (hH : OrdinaryHLS α c) (hSob : OrdinarySobolev K)
    (hStr : OrdinaryHomogeneousStrichartz C) (q : Highpass.Cutoff)
    (P : LinearProfileFamily) (u : ℕ → EnergyState)
    (hB : ∀ n, pureGradientNorm (u n) ≤ B)
    (hp : LinearProfileProperties hDensity hSob u P)
    (hg : ∀ j, Continuous (g j)) (hE : ∀ j, curveEnergy (g j) ≠ ∞)
    (hS : ∀ j, mixedNorm volume volume 10 10 (stateValueField (g j)) ≠ ∞)
    (hW : ∀ j, mixedNorm volume volume 10 (ENNReal.ofReal (30/13 : ℝ))
      (fun t => complexGradient (stateRealGradientField (g j) t)
        (stateImagGradientField (g j) t)) ≠ ∞)
    (r : ∀ j, EnergyJointFields volume (g j))
    (J : ℕ) (hJ : (J : WithTop ℕ) ≤ P.count) (k : Fin 3) :
    (∀ n, Q (headValue P r J n) (physicalFreeGradient hDensity hSob P u J k n) ≠ ∞) ∧
    Tendsto (fun n => Q (headValue P r J n)
      (physicalFreeGradient hDensity hSob P u J k n)) atTop (𝓝 0) := by
  have hi (j : Fin L) (hj : j ∈ headSet L J) := actual_physical_free_head_slots
    hDensity hH hSob hStr q P u hB hp J j.val ((mem_headSet j).mp hj) hJ
      (g j) (hg j) (hE j) (hS j) (hW j) (r j) k
  have hm (n : ℕ) : StronglyMeasurable (Function.uncurry
      (physicalFreeGradient hDensity hSob P u J k n)) := freeJoint_stronglyMeasurable _
  have hb (n : ℕ) := Q_sum_le (headSet L J)
    (fun j => physicalProfileValue P j.val (r j).u n)
    (physicalFreeGradient hDensity hSob P u J k n)
    (fun j _ => (seedFrame_joint_stronglyMeasurable _ _ _ _ (r j).u
      (r j).joint_u).aestronglyMeasurable) (hm n).aestronglyMeasurable
  have hz : Tendsto (fun n => ∑ j ∈ headSet L J,
      Q (physicalProfileValue P j.val (r j).u n)
        (physicalFreeGradient hDensity hSob P u J k n)) atTop (𝓝 0) := by
    simpa only [Finset.sum_const_zero] using
      tendsto_finsetSum (headSet L J) (fun j hj => (hi j hj).Q_zero)
  refine ⟨fun n => ne_top_of_le_ne_top
    (ENNReal.sum_ne_top.mpr (fun j hj => (hi j hj).Q_finite n)) (hb n), ?_⟩
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hz
    (fun _ => bot_le) hb

end HartreeF.ActualFreeValueHeadData
