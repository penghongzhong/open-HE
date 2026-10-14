import FActualNonlinearR2Tail
import FActualSelectedFreeValue
import FActualFiniteProfileGradientDefect
import FFullXGradientDifference
import FProfileInitialMatching

/-! Four-slot residual smallness at the original selected depth. All domains
are produced before numerical selection. No depth enlargement or second
extraction is made. Static author source; every declaration is UNCOMPILED. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3500000
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology
namespace HartreeF.FullResidual
open EnergySpace SobolevStretch StationarySelfTest ProfileEnergy TimeHolder
  CriticalTimeSobolev ProfileApproximation GeneralProfileCross ForcingDomain
  R2Global R2Frames R2SquareTail R2TailForcing R2FamilyTail ActualR2Tail
  FiniteProfileWeakGradient FiniteProfileFrameData ActualFiniteProfileGradientDefect
  ActualFreeValueHeadData FreeValueGradient ActualSelectedFreeValue
  CountableNonlinearProfiles Retarded ActualStrichartz EndpointOutput MaximalTrajectory

local instance : SecondCountableTopologyEither ℝ EnergyState :=
  ⟨Or.inl inferInstance⟩

variable {ι : Type*} [DecidableEq ι]

omit [DecidableEq ι] in
private theorem selected_finite_sum_ae {E : Type*} [AddCommMonoid E]
    (s : Finset ι) {f g : ι → Space → E}
    (h : ∀ i ∈ s, f i =ᵐ[volume] g i) :
    (fun x => ∑ i ∈ s, f i x) =ᵐ[volume] (fun x => ∑ i ∈ s, g i x) := by
  filter_upwards [(eventually_all_finset s).2 h] with x hx
  exact Finset.sum_congr rfl hx

omit [DecidableEq ι] in
private theorem selected_finite_joint_sum {E : Type*} [NormedAddCommGroup E]
    (s : Finset ι) (f : ι → ℝ → Space → E)
    (h : ∀ i ∈ s, AEStronglyMeasurable (fun z : ℝ × Space => f i z.1 z.2)
      (volume.prod volume)) :
    AEStronglyMeasurable (fun z : ℝ × Space => ∑ i ∈ s, f i z.1 z.2)
      (volume.prod volume) := by
  exact Finset.aestronglyMeasurable_fun_sum s h

omit [DecidableEq ι] in
private theorem lp_finset_sum_ae {p : ℝ≥0∞} (s : Finset ι)
    (f : ι → Lp ℂ p (volume : Measure Space)) :
    ((∑ j ∈ s, f j : Lp ℂ p volume) : Space → ℂ) =ᵐ[volume]
      (fun x => ∑ j ∈ s, f j x) :=
  Lp.coeFn_fun_finsetSum s f

/-- Canonical quotient representatives are added only modulo spatial AE. -/
omit [DecidableEq ι] in
private theorem energy_sum_fields_ae (s : Finset ι) (f : ι → EnergyState) :
    (energyValue (∑ j ∈ s, f j) : Space → ℂ) =ᵐ[volume]
      (fun x => ∑ j ∈ s, energyValue (f j) x) ∧
    energyProjectedGradient Complex.reCLM (∑ j ∈ s, f j) =ᵐ[volume]
      (fun x => ∑ j ∈ s, energyProjectedGradient Complex.reCLM (f j) x) ∧
    energyProjectedGradient Complex.imCLM (∑ j ∈ s, f j) =ᵐ[volume]
      (fun x => ∑ j ∈ s, energyProjectedGradient Complex.imCLM (f j) x) := by
  have hv : (energyValue (∑ j ∈ s, f j) : Space → ℂ) =ᵐ[volume]
      (fun x => ∑ j ∈ s, energyValue (f j) x) := by
    rw [map_sum]
    exact lp_finset_sum_ae s (fun j => energyValue (f j))
  have hd (k : Fin 3) : (energyGradient k (∑ j ∈ s, f j) : Space → ℂ) =ᵐ[volume]
      (fun x => ∑ j ∈ s, energyGradient k (f j) x) := by
    rw [map_sum]
    exact lp_finset_sum_ae s (fun j => energyGradient k (f j))
  have hp (L : ℂ →L[ℝ] ℝ) : energyProjectedGradient L (∑ j ∈ s, f j) =ᵐ[volume]
      (fun x => ∑ j ∈ s, energyProjectedGradient L (f j) x) := by
    filter_upwards [eventually_all.mpr hd] with x hx
    simp only [energyProjectedGradient]
    simp only [hx]
    simp only [map_sum, Finset.sum_smul]
    exact Finset.sum_comm
  exact ⟨hv, hp Complex.reCLM, hp Complex.imCLM⟩

/-- Literal finite joint fields; the canonical side is verified modulo AE. -/
def sumJointFields (s : Finset ι) {g : ι → ℝ → EnergyState}
    (r : ∀ j, EnergyJointFields volume (g j)) :
    EnergyJointFields volume (∑ j ∈ s, g j) where
  u := fun t x => ∑ j ∈ s, (r j).u t x
  U := fun t x => ∑ j ∈ s, (r j).U t x
  V := fun t x => ∑ j ∈ s, (r j).V t x
  joint_u := Finset.stronglyMeasurable_fun_sum s (fun j _ => (r j).joint_u)
  joint_U := Finset.stronglyMeasurable_fun_sum s (fun j _ => (r j).joint_U)
  joint_V := Finset.stronglyMeasurable_fun_sum s (fun j _ => (r j).joint_V)
  slice_eq := by
    filter_upwards [(eventually_all_finset s).2 (fun j _ => (r j).slice_eq)] with t ht
    have hc := energy_sum_fields_ae s (fun j => g j t)
    simp only [Finset.sum_apply]
    exact ⟨(selected_finite_sum_ae s (fun j hj => (ht j hj).1)).trans hc.1.symm,
      (selected_finite_sum_ae s (fun j hj => (ht j hj).2.1)).trans hc.2.1.symm,
      (selected_finite_sum_ae s (fun j hj => (ht j hj).2.2)).trans hc.2.2.symm⟩

private theorem energy_add_fields_ae (f g : EnergyState) :
    (energyValue (f+g) : Space → ℂ) =ᵐ[volume]
      (fun x => energyValue f x + energyValue g x) ∧
    energyProjectedGradient Complex.reCLM (f+g) =ᵐ[volume]
      (fun x => energyProjectedGradient Complex.reCLM f x + energyProjectedGradient Complex.reCLM g x) ∧
    energyProjectedGradient Complex.imCLM (f+g) =ᵐ[volume]
      (fun x => energyProjectedGradient Complex.imCLM f x + energyProjectedGradient Complex.imCLM g x) := by
  have hd (k : Fin 3) : (energyGradient k (f+g) : Space → ℂ) =ᵐ[volume]
      (fun x => energyGradient k f x + energyGradient k g x) := by
    rw [map_add]
    exact Lp.coeFn_add _ _
  have hp (L : ℂ →L[ℝ] ℝ) : energyProjectedGradient L (f+g) =ᵐ[volume]
      (fun x => energyProjectedGradient L f x + energyProjectedGradient L g x) := by
    filter_upwards [eventually_all.mpr hd] with x hx
    simp only [energyProjectedGradient]
    simp only [hx]
    simp only [map_add, add_smul, Finset.sum_add_distrib]
  refine ⟨?_, hp Complex.reCLM, hp Complex.imCLM⟩
  rw [map_add]
  exact Lp.coeFn_add _ _

def addJointFields {g h : ℝ → EnergyState}
    (r : EnergyJointFields volume g) (s : EnergyJointFields volume h) :
    EnergyJointFields volume (g+h) where
  u := r.u+s.u
  U := r.U+s.U
  V := r.V+s.V
  joint_u := r.joint_u.add s.joint_u
  joint_U := r.joint_U.add s.joint_U
  joint_V := r.joint_V.add s.joint_V
  slice_eq := by
    filter_upwards [r.slice_eq, s.slice_eq] with t hr hs
    have hc := energy_add_fields_ae (g t) (h t)
    exact ⟨(hr.1.add hs.1).trans hc.1.symm,
      (hr.2.1.add hs.2.1).trans hc.2.1.symm,
      (hr.2.2.add hs.2.2).trans hc.2.2.symm⟩

/-- Reindex the fixed Fin L head to exactly range(min J L). -/
theorem headSet_sum_eq_range {E : Type*} [AddCommMonoid E]
    (L J : ℕ) (f : ℕ → E) :
    (∑ j ∈ headSet L J, f j.val) = ∑ j ∈ Finset.range (min J L), f j := by
  apply Finset.sum_bij (fun j _ => j.val)
  · intro j hj
    exact Finset.mem_range.mpr ((headSet_min j).mp hj)
  · intro j hj k hk he
    exact Fin.ext he
  · intro j hj
    have h := Finset.mem_range.mp hj
    exact ⟨⟨j, (lt_min_iff.mp h).2⟩, (mem_headSet _).mpr (lt_min_iff.mp h).1, rfl⟩
  · intro j hj
    rfl

/-- The selected normalized fields are framed into the actual physical curves. -/
def selectedHeadFields (P : LinearProfileFamily) (g : ℕ → ℝ → EnergyState)
    {L : ℕ} (r : ∀ j : Fin L, EnergyJointFields volume (g j.val)) (J n : ℕ) :
    EnergyJointFields volume (∑ j ∈ headSet L J, nonlinearFrame P g j.val n) :=
  sumJointFields (headSet L J) (fun j : Fin L =>
    frameJointFields (g j.val) (r j) (P.scale_pos j.val n) (P.center j.val n) (P.time j.val n))

/-- All head labels are active: j<min(J,L)≤J≤count. -/
theorem selected_head_active (P : LinearProfileFamily) {L J : ℕ}
    (hJ : (J : WithTop ℕ) ≤ P.count) {j : Fin L} (hj : j ∈ headSet L J) :
    (j.val : WithTop ℕ) < P.count := by
  exact lt_of_lt_of_le (by exact_mod_cast (mem_headSet j).mp hj) hJ

/-- Complete finite-family gradient defect. The source theorem contains its
six-term candidate expansion; no succession of two-input bounds replaces it. -/
theorem selected_head_defect_tendsto (hDensity : OrdinaryH1Density) {K α c : ℝ}
    (hSob : OrdinarySobolev K) (hH : OrdinaryHLS α c)
    (P : LinearProfileFamily) (u : ℕ → EnergyState)
    (hp : LinearProfileProperties hDensity hSob u P)
    (g : ℕ → ℝ → EnergyState) (hg : ∀ j, CurveFinite (g j))
    {L : ℕ} (r : ∀ j : Fin L, EnergyJointFields volume (g j.val))
    (J : ℕ) (hJ : (J : WithTop ℕ) ≤ P.count) :
    Tendsto (fun n => vectorForcingNorm (fun t x =>
      sourceCandidate α c (selectedHeadFields P g r J n) t x -
        ∑ j ∈ headSet L J, sourceCandidate α c
          (frameJointFields (g j.val) (r j) (P.scale_pos j.val n)
            (P.center j.val n) (P.time j.val n)) t x)) atTop (𝓝 0) := by
  let a := fun j : Fin L => P.scale j.val
  let y := fun j : Fin L => P.center j.val
  let τ := fun j : Fin L => P.time j.val
  have horth : ∀ i ∈ headSet L J, ∀ j ∈ headSet L J, i ≠ j →
      Tendsto (frameSeparation a y τ i j) atTop atTop := by
    intro i hi j hj hij
    have hne : i.val ≠ j.val := fun he => hij (Fin.ext he)
    unfold frameSeparation
    simpa only [a, y, τ, mul_comm] using
      hp.orthogonal i.val j.val (selected_head_active P hJ hi)
        (selected_head_active P hJ hj) hne
  have hd := actual_finite_profile_gradient_defect hDensity hSob hH
    (headSet L J) (fun j : Fin L => g j.val)
    (fun j => (hg j.val).continuous) (fun j _ => (hg j.val).energy)
    (fun j _ => (hg j.val).value) (fun j _ => (hg j.val).gradient)
    a y τ (fun j _ n => P.scale_pos j.val n) horth
  have he (n : ℕ) := (actual_finite_framed_candidate_transfer hH
    (headSet L J) (fun j : Fin L => g j.val) r (fun j => a j n)
    (fun j => τ j n) (fun j => y j n) (fun j _ => P.scale_pos j.val n)
    (fun j _ => (hg j.val).value) (fun j _ => (hg j.val).gradient)).2
  apply hd.2.1.congr'
  apply Filter.Eventually.of_forall
  intro n
  have hn := mixedNorm_congr_nested_ae volume volume 2 (ENNReal.ofReal (6/5 : ℝ)) (he n)
  unfold jointCandidateDefect at hn
  simpa only [vectorForcingNorm, sourceCandidate_eq_full, selectedHeadFields,
    sumJointFields, frameJointFields, a, y, τ] using hn


def selectedHeadCurve (P : LinearProfileFamily) (g : ℕ → ℝ → EnergyState)
    (L J n : ℕ) : ℝ → EnergyState :=
  ∑ j ∈ headSet L J, nonlinearFrame P g j.val n

def selectedHeadFreeFields (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) (P : LinearProfileFamily) (u : ℕ → EnergyState)
    (g : ℕ → ℝ → EnergyState) {L : ℕ}
    (r : ∀ j : Fin L, EnergyJointFields volume (g j.val)) (J n : ℕ) :
    EnergyJointFields volume (selectedHeadCurve P g L J n +
      freeCurve hDensity hSob (profileRemainder hDensity hSob P u J n)) :=
  addJointFields (selectedHeadFields P g r J n)
    (ActualFreeValue.freeValueFields hDensity hSob (profileRemainder hDensity hSob P u J n))

/-- This exact curve identity uses H=min(J,L), so J<L gives the empty tail. -/
theorem selectedHeadFree_eq_sub_block (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) (P : LinearProfileFamily) (u : ℕ → EnergyState)
    (g : ℕ → ℝ → EnergyState) (L J n : ℕ) :
    selectedHeadCurve P g L J n + freeCurve hDensity hSob (profileRemainder hDensity hSob P u J n) =
      augmentedCurve hDensity hSob P u g J n - nonlinearBlock P g (min J L) J n := by
  have hp := Finset.sum_range_add_sum_Ico (fun j => nonlinearFrame P g j n) (min_le_left J L)
  rw [selectedHeadCurve, headSet_sum_eq_range L J (fun j => nonlinearFrame P g j n)]
  unfold augmentedCurve nonlinearBlock
  rw [← hp]
  abel

def headCandidate (P : LinearProfileFamily) (g : ℕ → ℝ → EnergyState)
    {L : ℕ} (α c : ℝ) (r : ∀ j : Fin L, EnergyJointFields volume (g j.val))
    (J n : ℕ) : ℝ → Space → CGradient := fun t x =>
  sourceCandidate α c (selectedHeadFields P g r J n) t x -
    ∑ j ∈ headSet L J, sourceCandidate α c
      (frameJointFields (g j.val) (r j) (P.scale_pos j.val n)
        (P.center j.val n) (P.time j.val n)) t x

/-- The head/free term is the candidate of the SAME source used by the
selected free-value producer, with its actual zero candidate already removed. -/
theorem headFree_candidate_eq (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) (P : LinearProfileFamily) (u : ℕ → EnergyState)
    (g : ℕ → ℝ → EnergyState) {L : ℕ} (α c : ℝ)
    (r : ∀ j : Fin L, EnergyJointFields volume (g j.val)) (J n : ℕ) :
    (fun t x => sourceCandidate α c (selectedHeadFreeFields hDensity hSob P u g r J n) t x -
      sourceCandidate α c (selectedHeadFields P g r J n) t x) =
      candidateGradient α c (headValue P r J n) (freeValue hDensity hSob P u J n)
        (headReal P r J n) (headImag P r J n)
        (freeReal hDensity hSob P u J n) (freeImag hDensity hSob P u J n) := by
  funext t x
  rw [sourceCandidate_eq_full, sourceCandidate_eq_full, candidateGradient_eq_candidates]
  rfl

/-- The literal scalar split has no derivative and no choice of a larger J.
The head and head-plus-free values are the canonical values of their actual
EnergyState sums; the full residual is independent of the auxiliary L. -/
theorem selected_four_slot_scalar (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) (P : LinearProfileFamily) (u : ℕ → EnergyState)
    (g : ℕ → ℝ → EnergyState) (L J n : ℕ) (α c : ℝ) (t : ℝ) (x : Space) :
    literalResidual (Finset.range J) α c
        (augmentedCurve hDensity hSob P u g J n) (fun j => nonlinearFrame P g j n) t x =
      (forcing α c (energyValue (augmentedCurve hDensity hSob P u g J n t)) x -
        forcing α c (energyValue ((selectedHeadCurve P g L J n +
          freeCurve hDensity hSob (profileRemainder hDensity hSob P u J n)) t)) x) +
      (forcing α c (energyValue ((selectedHeadCurve P g L J n +
          freeCurve hDensity hSob (profileRemainder hDensity hSob P u J n)) t)) x -
        forcing α c (energyValue (selectedHeadCurve P g L J n t)) x) +
      (forcing α c (energyValue (selectedHeadCurve P g L J n t)) x -
        ∑ j ∈ Finset.range (min J L), forcing α c (energyValue (nonlinearFrame P g j n t)) x) -
      ∑ j ∈ Finset.Ico (min J L) J, forcing α c (energyValue (nonlinearFrame P g j n t)) x := by
  have hsplit := Finset.sum_range_add_sum_Ico
    (fun j => forcing α c (energyValue (nonlinearFrame P g j n t)) x) (min_le_left J L)
  unfold literalResidual
  rw [← hsplit]
  abel

/-- Four genuine first-gradient slots, all on one common finite conull set.
The two different profile representative choices meet only via frameJointFields
and candidate congruence, never a raw actual-gradient congruence assertion. -/
theorem selected_four_slot_ae (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) (P : LinearProfileFamily) (u : ℕ → EnergyState)
    (g : ℕ → ℝ → EnergyState) {L : ℕ} (α c : ℝ)
    (r : ∀ j : Fin L, EnergyJointFields volume (g j.val)) (J n : ℕ)
    (rq : EnergyJointFields volume (augmentedCurve hDensity hSob P u g J n))
    (rp : ∀ j, EnergyJointFields volume (nonlinearFrame P g j n)) :
    ∀ᵐ t ∂volume, residualCandidate (Finset.range J) α c rq rp t =ᵐ[volume]
      (fun x =>
        (sourceCandidate α c rq t x -
          sourceCandidate α c (selectedHeadFreeFields hDensity hSob P u g r J n) t x) +
        (sourceCandidate α c (selectedHeadFreeFields hDensity hSob P u g r J n) t x -
          sourceCandidate α c (selectedHeadFields P g r J n) t x) +
        headCandidate P g α c r J n t x -
        ∑ j ∈ Finset.Ico (min J L) J, sourceCandidate α c (rp j) t x) := by
  have he (j : Fin L) := sourceCandidate_congr α c (rp j.val)
    (frameJointFields (g j.val) (r j) (P.scale_pos j.val n)
      (P.center j.val n) (P.time j.val n))
  filter_upwards [(eventually_all_finset (headSet L J)).2 (fun j _ => he j)] with t ht
  filter_upwards [(eventually_all_finset (headSet L J)).2 ht] with x hx
  have hsum : (∑ j ∈ headSet L J, sourceCandidate α c
      (frameJointFields (g j.val) (r j) (P.scale_pos j.val n)
        (P.center j.val n) (P.time j.val n)) t x) =
      ∑ j ∈ Finset.range (min J L), sourceCandidate α c (rp j) t x := by
    rw [← headSet_sum_eq_range L J]
    exact Finset.sum_congr rfl (fun j hj => (hx j hj).symm)
  have hsplit := Finset.sum_range_add_sum_Ico
    (fun j => sourceCandidate α c (rp j) t x) (min_le_left J L)
  unfold residualCandidate headCandidate
  rw [hsum, ← hsplit]
  abel

private theorem vectorForcingNorm_add_le (G H : ℝ → Space → CGradient)
    (hG : AEStronglyMeasurable (fun z : ℝ × Space => G z.1 z.2) (volume.prod volume))
    (hH : AEStronglyMeasurable (fun z : ℝ × Space => H z.1 z.2) (volume.prod volume)) :
    vectorForcingNorm (fun t x => G t x + H t x) ≤ vectorForcingNorm G + vectorForcingNorm H :=
  mixed_add_le (by norm_num) (by norm_num) ENNReal.ofReal_ne_top G H hG hH

/-- Numerical triangle after the genuine candidate identity. -/
theorem selected_four_slot_bound (hDensity : OrdinaryH1Density) {K Ch α c : ℝ}
    (hSob : OrdinarySobolev K) (hH : OrdinaryHLS α c)
    (hfree : OrdinaryHomogeneousStrichartz Ch)
    (P : LinearProfileFamily) (u : ℕ → EnergyState)
    (g : ℕ → ℝ → EnergyState) (hg : ∀ j, CurveFinite (g j)) {L : ℕ}
    (r : ∀ j : Fin L, EnergyJointFields volume (g j.val)) (J n : ℕ)
    (hq : CurveFinite (augmentedCurve hDensity hSob P u g J n))
    (rq : EnergyJointFields volume (augmentedCurve hDensity hSob P u g J n))
    (rp : ∀ j, EnergyJointFields volume (nonlinearFrame P g j n)) :
    vectorForcingNorm (residualCandidate (Finset.range J) α c rq rp) ≤
      vectorForcingNorm (fun t x => sourceCandidate α c rq t x -
        sourceCandidate α c (selectedHeadFreeFields hDensity hSob P u g r J n) t x) +
      vectorForcingNorm (ActualSelectedFreeValue.gradient hDensity hSob α c P u r J n) +
      vectorForcingNorm (headCandidate P g α c r J n) +
      vectorForcingNorm (fun t x => ∑ j ∈ Finset.Ico (min J L) J, sourceGradient α c (rp j) t x) := by
  let rA := selectedHeadFields P g r J n
  let rAz := selectedHeadFreeFields hDensity hSob P u g r J n
  have hpfin (j : ℕ) : CurveFinite (nonlinearFrame P g j n) :=
    R2Frames.CurveFinite.stateFrame (hg j) (P.scale_pos j n) (P.center j n) (P.time j n)
  have hAfin : CurveFinite (selectedHeadCurve P g L J n) :=
    curveFinite_sum (headSet L J) _ (fun j _ => hpfin j.val)
  have hTfin : CurveFinite (nonlinearBlock P g (min J L) J n) :=
    curveFinite_sum _ _ (fun j _ => hpfin j)
  have hAzfin : CurveFinite (selectedHeadCurve P g L J n +
      freeCurve hDensity hSob (profileRemainder hDensity hSob P u J n)) := by
    rw [selectedHeadFree_eq_sub_block]
    exact hq.sub hTfin
  let G1 := fun t x => sourceCandidate α c rq t x - sourceCandidate α c rAz t x
  let G2 := fun t x => sourceCandidate α c rAz t x - sourceCandidate α c rA t x
  let G3 := headCandidate P g α c r J n
  let G4 := fun t x => ∑ j ∈ Finset.Ico (min J L) J, sourceCandidate α c (rp j) t x
  have hqD := source_domains hDensity hSob hH hq rq
  have hAD := source_domains hDensity hSob hH hAfin rA
  have hAzD := source_domains hDensity hSob hH hAzfin rAz
  have h1 := hqD.candidate_joint.sub hAzD.candidate_joint
  have h2 := hAzD.candidate_joint.sub hAD.candidate_joint
  have h3 : AEStronglyMeasurable (fun z : ℝ × Space => G3 z.1 z.2) (volume.prod volume) :=
    hAD.candidate_joint.sub (selected_finite_joint_sum (headSet L J) _ (fun j _ =>
      (source_domains hDensity hSob hH (hpfin j.val)
        (frameJointFields (g j.val) (r j) (P.scale_pos j.val n)
          (P.center j.val n) (P.time j.val n))).candidate_joint))
  have h4 : AEStronglyMeasurable (fun z : ℝ × Space => G4 z.1 z.2) (volume.prod volume) :=
    selected_finite_joint_sum (Finset.Ico (min J L) J) _ (fun j _ =>
      (source_domains hDensity hSob hH (hpfin j) (rp j)).candidate_joint)
  have h2norm : vectorForcingNorm G2 =
      vectorForcingNorm (ActualSelectedFreeValue.gradient hDensity hSob α c P u r J n) := by
    have hd := actual_head_free_value_domains hDensity hH hSob hfree P u
      (fun j : Fin L => (hg j.val).continuous) (fun j => (hg j.val).energy)
      (fun j => (hg j.val).value) (fun j => (hg j.val).gradient) r J n
    change vectorForcingNorm (fun t x => sourceCandidate α c
      (selectedHeadFreeFields hDensity hSob P u g r J n) t x -
      sourceCandidate α c (selectedHeadFields P g r J n) t x) = _
    rw [headFree_candidate_eq]
    exact (mixedNorm_congr_nested_ae volume volume 2 (ENNReal.ofReal (6/5 : ℝ))
      hd.actual_ae_candidate).symm
  have h4norm : vectorForcingNorm G4 = vectorForcingNorm
      (fun t x => ∑ j ∈ Finset.Ico (min J L) J, sourceGradient α c (rp j) t x) := by
    apply mixedNorm_congr_nested_ae
    filter_upwards [(eventually_all_finset (Finset.Ico (min J L) J)).2 (fun j _ =>
      (source_domains hDensity hSob hH (hpfin j) (rp j)).actual_ae_candidate)] with t ht
    exact (selected_finite_sum_ae _ ht).symm
  have he := mixedNorm_congr_nested_ae volume volume 2 (ENNReal.ofReal (6/5 : ℝ))
    (selected_four_slot_ae hDensity hSob P u g α c r J n rq rp)
  calc
    _ = vectorForcingNorm (fun t x => G1 t x + G2 t x + G3 t x - G4 t x) := he
    _ ≤ vectorForcingNorm (fun t x => G1 t x + G2 t x + G3 t x) + vectorForcingNorm G4 :=
      vectorForcingNorm_sub_le _ _ ((h1.add h2).add h3) h4
    _ ≤ (vectorForcingNorm G1 + vectorForcingNorm G2 + vectorForcingNorm G3) +
        vectorForcingNorm G4 := add_le_add
      ((vectorForcingNorm_add_le _ _ (h1.add h2) h3).trans
        (add_le_add (vectorForcingNorm_add_le _ _ h1 h2) le_rfl)) le_rfl
    _ = _ := by rw [h2norm, h4norm]


/-- Same-depth residual selection. M and Ktail precede epsilon; d and eta
precede L; normalized Fin L fields and the free-value precision precede the
single original small_remainder selection of J. Only n is enlarged afterward. -/
theorem actual_selected_residual (hDensity : OrdinaryH1Density) {K Ch α c B : ℝ}
    (hSob : OrdinarySobolev K) (hH : OrdinaryHLS α c)
    (hfree : OrdinaryHomogeneousStrichartz Ch) (q : Highpass.Cutoff)
    (P : LinearProfileFamily) (u : ℕ → EnergyState)
    (hB : ∀ n, pureGradientNorm (u n) ≤ B)
    (hp : LinearProfileProperties hDensity hSob u P)
    (g : ℕ → ℝ → EnergyState) (δ Csd Ccorr Cforce Cf : ℝ) (L0 : ℕ) (M : ℝ)
    (_hCcorr : 0 ≤ Ccorr) (_hCforce : 0 ≤ Cforce) (hCf : 0 ≤ Cf)
    (r : ∀ j n, EnergyJointFields volume (nonlinearFrame P g j n))
    (hTail : TailBounds (α := α) (c := c) hDensity hSob P u g δ Csd Ccorr Cforce Cf L0 M r)
    (rq : ∀ J n, EnergyJointFields volume (augmentedCurve hDensity hSob P u g J n)) :
    ∀ ε : ℝ, 0 < ε → ∃ J N : ℕ,
      (P.count = ⊤ ∨ P.count = (J : WithTop ℕ)) ∧
      ∀ n ≥ N, vectorForcingNorm (residualCandidate (Finset.range J) α c
        (rq J n) (fun j => r j n)) ≤ ENNReal.ofReal ε := by
  classical
  obtain ⟨Ktail, hKtail, hdiff⟩ :=
    exists_full_x_gradient_difference_bound hDensity hSob hH M hTail.cap_one
  have ht := actualProfileTail_tendsto_zero hDensity hSob P u hp hB
  have hm : 0 < 5+2*α := by linarith [hH.order_pos]
  have htp : Tendsto (fun L => actualProfileTail P L^(5+2*α)) atTop (𝓝 0) :=
    ht.rpow_const_nhds_zero hm
  have htBlock : Tendsto (fun L => Cf*actualProfileTail P L +
      Ccorr*actualProfileTail P L^(5+2*α)) atTop (𝓝 0) := by
    simpa only [mul_zero, add_zero] using (ht.const_mul Cf).add (htp.const_mul Ccorr)
  have htForce : Tendsto (fun L => Cforce*actualProfileTail P L^(5+2*α)) atTop (𝓝 0) := by
    simpa only [mul_zero] using htp.const_mul Cforce
  intro ε hε
  let d : ℝ := min 1 (ε/(4*(Ktail+1)))
  have hd : 0 < d := lt_min (by norm_num) (div_pos hε (by positivity))
  have hd1 : d ≤ 1 := min_le_left _ _
  have hKd : Ktail*d ≤ ε/4 := by
    have hb : d*(4*(Ktail+1)) ≤ ε :=
      (le_div_iff₀ (by positivity)).mp (min_le_right _ _)
    nlinarith
  let η : ℝ := d/(2*(Cf+1))
  have hη : 0 < η := div_pos hd (by positivity)
  have hCη : Cf*η ≤ d/2 := by
    have hb : η*(2*(Cf+1)) = d := div_mul_cancel₀ d (by positivity)
    nlinarith
  obtain ⟨L, hL0, hLB, hLF⟩ :=
    ((eventually_ge_atTop L0).and
      ((htBlock.eventually (gt_mem_nhds (by positivity : 0 < d/2))).and
        (htForce.eventually (gt_mem_nhds (by positivity : 0 < ε/4))))).exists
  let rN (j : Fin L) : EnergyJointFields volume (g j.val) :=
    energyJointFields volume (g j.val) (hTail.curve_finite j.val).continuous.aestronglyMeasurable
  -- The retained theorem internally uses cutoffScale for extraction and
  -- smoothingPrecision for the free-value norm; those parameters are distinct.
  obtain ⟨J, Nz, hcount, hz⟩ := (actual_selected_head_free_value hDensity hH hSob hfree q
    P u hB hp (fun j : Fin L => (hTail.curve_finite j.val).continuous)
    (fun j => (hTail.curve_finite j.val).energy)
    (fun j => (hTail.curve_finite j.val).value)
    (fun j => (hTail.curve_finite j.val).gradient) rN).2 (ε/4) (by positivity)
  have hJ : (J : WithTop ℕ) ≤ P.count := by
    rcases hcount with ht | ht
    · simp only [ht, le_top]
    · simp only [ht, le_refl]
  let H := min J L
  have hTfin (n : ℕ) : CurveFinite (nonlinearBlock P g H J n) :=
    curveFinite_sum _ _ (fun j _ =>
      R2Frames.CurveFinite.stateFrame (hTail.curve_finite j) (P.scale_pos j n) (P.center j n) (P.time j n))
  have hTsmall : ∃ Nt : ℕ, ∀ n ≥ Nt, xNorm (nonlinearBlock P g H J n) ≤ d := by
    by_cases hLJ : L ≤ J
    · obtain ⟨Nt, hNt⟩ := hTail.block L hL0 J hLJ hJ η hη
      refine ⟨Nt, fun n hn => ?_⟩
      have hh : H = L := min_eq_right hLJ
      rw [hh]
      exact (hNt n hn).2.trans (by nlinarith [hLB.le, hCη])
    · have hJL : J ≤ L := (Nat.lt_of_not_ge hLJ).le
      refine ⟨0, fun n _ => ?_⟩
      have hh : H = J := min_eq_left hJL
      simp only [hh, nonlinearBlock, Finset.Ico_self, Finset.sum_empty, xNorm_zero]
      exact hd.le
  have hTailForce (n : ℕ) : vectorForcingNorm
      (fun t x => ∑ j ∈ Finset.Ico H J, sourceGradient α c (r j n) t x) ≤
      ENNReal.ofReal (ε/4) := by
    by_cases hLJ : L ≤ J
    · have hh : H = L := min_eq_right hLJ
      rw [hh]
      exact (hTail.source_tail L hL0 J n).2.trans (ENNReal.ofReal_le_ofReal hLF.le)
    · have hJL : J ≤ L := (Nat.lt_of_not_ge hLJ).le
      have hh : H = J := min_eq_left hJL
      simp only [hh, Finset.Ico_self, Finset.sum_empty]
      simp [vectorForcingNorm, mixedNorm]
  have hHead : Tendsto (fun n => vectorForcingNorm (headCandidate P g α c rN J n))
      atTop (𝓝 0) := selected_head_defect_tendsto hDensity hSob hH P u hp g
        hTail.curve_finite rN J hJ
  obtain ⟨Nh, hNh⟩ := eventually_atTop.mp ((ENNReal.tendsto_nhds_zero.mp hHead)
    _ (ENNReal.ofReal_pos.mpr (by positivity : 0 < ε/4)))
  obtain ⟨Nt, hNt⟩ := hTsmall
  refine ⟨J, max Nz (max Nh Nt), hcount, fun n hn => ?_⟩
  have hnz : Nz ≤ n := (le_max_left _ _).trans hn
  have hnh : Nh ≤ n := (le_max_left Nh Nt).trans ((le_max_right _ _).trans hn)
  have hnt : Nt ≤ n := (le_max_right Nh Nt).trans ((le_max_right _ _).trans hn)
  let rT := energyJointFields volume (nonlinearBlock P g H J n)
    (hTfin n).continuous.aestronglyMeasurable
  let rm := differenceJointFields (rq J n) rT
  let rAz := selectedHeadFreeFields hDensity hSob P u g rN J n
  have hmAz : ∀ᵐ t ∂volume, sourceCandidate α c rm t =ᵐ[volume]
      sourceCandidate α c rAz t := sourceCandidate_congr_curve α c rm rAz
        (selectedHeadFree_eq_sub_block hDensity hSob P u g L J n).symm
  have hDiff : vectorForcingNorm (fun t x => sourceCandidate α c (rq J n) t x -
      sourceCandidate α c rAz t x) ≤ ENNReal.ofReal (ε/4) := by
    have hb := hdiff (augmentedCurve hDensity hSob P u g J n) (nonlinearBlock P g H J n)
      (hTail.augmented J n).1 (hTfin n) (rq J n) rm d hd.le hd1
      (hTail.augmented J n).2 (hNt n hnt)
    have he : vectorForcingNorm (fun t x => sourceCandidate α c (rq J n) t x -
        sourceCandidate α c rm t x) =
        vectorForcingNorm (fun t x => sourceCandidate α c (rq J n) t x -
          sourceCandidate α c rAz t x) := by
      apply mixedNorm_congr_nested_ae
      exact hmAz.mono (fun _ ht => Filter.EventuallyEq.rfl.sub ht)
    rw [he] at hb
    exact hb.trans (ENNReal.ofReal_le_ofReal hKd)
  calc
    _ ≤ vectorForcingNorm (fun t x => sourceCandidate α c (rq J n) t x -
        sourceCandidate α c rAz t x) +
        vectorForcingNorm (ActualSelectedFreeValue.gradient hDensity hSob α c P u rN J n) +
        vectorForcingNorm (headCandidate P g α c rN J n) +
        vectorForcingNorm (fun t x => ∑ j ∈ Finset.Ico H J, sourceGradient α c (r j n) t x) :=
      selected_four_slot_bound hDensity hSob hH hfree P u g hTail.curve_finite rN J n
        (hTail.augmented J n).1 (rq J n) (fun j => r j n)
    _ ≤ ENNReal.ofReal (ε/4) + ENNReal.ofReal (ε/4) +
        ENNReal.ofReal (ε/4) + ENNReal.ofReal (ε/4) :=
      add_le_add (add_le_add (add_le_add hDiff (hz n hnz)) (hNh n hnh)) (hTailForce n)
    _ = ENNReal.ofReal ε := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring

abbrev actualMatchingFamily (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr Che Cre α c : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hefree : OrdinaryHomogeneousEndpointOutput Che)
    (heret : OrdinaryRetardedEndpointOutput h0 Cre) (hH : OrdinaryHLS α c)
    (T : ℕ → ℝ) (f : ℕ → EnergyState) : ℕ → ℝ → EnergyState :=
  fun j => (actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH (T j) (f j)).state

/-- The same original J handles the actual full residual and initial matching.
Every field belongs to the same marked canonical nonlinear family. -/
theorem actual_selected_full_residual (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr Che Cre α c B : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hefree : OrdinaryHomogeneousEndpointOutput Che)
    (heret : OrdinaryRetardedEndpointOutput h0 Cre) (hH : OrdinaryHLS α c)
    (q : Highpass.Cutoff) (P : LinearProfileFamily) (u : ℕ → EnergyState)
    (hB : ∀ n, pureGradientNorm (u n) ≤ B)
    (hp : LinearProfileProperties hDensity hSob u P)
    (T : ℕ → ℝ) (f : ℕ → EnergyState)
    (hmatch : ActualProfileFamilyApproximation hDensity hSob h0 hfree hret hefree heret hH P T f)
    (δ Csd Ccorr Cforce Cf : ℝ) (L0 : ℕ) (M : ℝ)
    (hCcorr : 0 ≤ Ccorr) (hCforce : 0 ≤ Cforce) (hCf : 0 ≤ Cf)
    (r : ∀ j n, EnergyJointFields volume (nonlinearFrame P
      (actualMatchingFamily hDensity hSob h0 hfree hret hefree heret hH T f) j n))
    (hTail : TailBounds (α := α) (c := c) hDensity hSob P u
      (actualMatchingFamily hDensity hSob h0 hfree hret hefree heret hH T f)
      δ Csd Ccorr Cforce Cf L0 M r)
    (rq : ∀ J n, EnergyJointFields volume (augmentedCurve hDensity hSob P u
      (actualMatchingFamily hDensity hSob h0 hfree hret hefree heret hH T f) J n)) :
    ∀ ε : ℝ, 0 < ε → ∃ J N : ℕ,
      (P.count = ⊤ ∨ P.count = (J : WithTop ℕ)) ∧
      ∀ n ≥ N,
        vectorForcingNorm (residualCandidate (Finset.range J) α c (rq J n) (fun j => r j n)) ≤
          ENNReal.ofReal ε ∧
        pureGradientNorm (u n - augmentedCurve hDensity hSob P u
          (actualMatchingFamily hDensity hSob h0 hfree hret hefree heret hH T f) J n 0) ≤ ε := by
  intro ε hε
  obtain ⟨J, Nr, hJ, hNr⟩ := actual_selected_residual hDensity hSob hH hfree q P u hB hp
    (actualMatchingFamily hDensity hSob h0 hfree hret hefree heret hH T f)
    δ Csd Ccorr Cforce Cf L0 M hCcorr hCforce hCf r hTail rq ε hε
  obtain ⟨Ni, hNi⟩ := ProfileInitialMatching.actual_initial_matching_eventually
    hDensity hSob h0 hfree hret hefree heret hH P u T f hmatch J hε
  exact ⟨J, max Nr Ni, hJ, fun n hn =>
    ⟨hNr n ((le_max_left _ _).trans hn), hNi n ((le_max_right _ _).trans hn)⟩⟩

end HartreeF.FullResidual
