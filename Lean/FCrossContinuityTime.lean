import FCrossContinuitySpatial
import FTimeThreeWeightBudget
import FJointDirectionalCandidate

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000
open MeasureTheory
open scoped ENNReal NNReal
namespace HartreeF.CrossContinuity
open ForcingDomain WeakHartreeChain DerivativeMajorization GradientMajorants TimeHolder CompactCross

/-- These are separate spatial memberships, not an equation or an inferred
Sobolev property of a nonnegative envelope. -/
structure SliceInputs (u U h H v V k K : Space → ℂ) : Prop where
  u6 : MemLp u 6 volume
  U6 : MemLp U 6 volume
  v6 : MemLp v 6 volume
  V6 : MemLp V 6 volume
  u10 : MemLp u 10 volume
  U10 : MemLp U 10 volume
  v10 : MemLp v 10 volume
  V10 : MemLp V 10 volume
  hW : MemLp h (ENNReal.ofReal (30/13 : ℝ)) volume
  HW : MemLp H (ENNReal.ofReal (30/13 : ℝ)) volume
  kW : MemLp k (ENNReal.ofReal (30/13 : ℝ)) volume
  KW : MemLp K (ENNReal.ofReal (30/13 : ℝ)) volume

structure JointInputs (u U h H v V k K : ℝ → Space → ℂ) : Prop where
  uM : AEStronglyMeasurable (fun z : ℝ × Space => u z.1 z.2) (volume.prod volume)
  UM : AEStronglyMeasurable (fun z : ℝ × Space => U z.1 z.2) (volume.prod volume)
  hM : AEStronglyMeasurable (fun z : ℝ × Space => h z.1 z.2) (volume.prod volume)
  HM : AEStronglyMeasurable (fun z : ℝ × Space => H z.1 z.2) (volume.prod volume)
  vM : AEStronglyMeasurable (fun z : ℝ × Space => v z.1 z.2) (volume.prod volume)
  VM : AEStronglyMeasurable (fun z : ℝ × Space => V z.1 z.2) (volume.prod volume)
  kM : AEStronglyMeasurable (fun z : ℝ × Space => k z.1 z.2) (volume.prod volume)
  KM : AEStronglyMeasurable (fun z : ℝ × Space => K z.1 z.2) (volume.prod volume)

def crossBudget (α : ℝ) (u U h H v V k K : ℝ → Space → ℂ) : ℝ≥0∞ :=
  threeWeightBudget α volume (fun t => valueEnvelope (u t) (U t) (v t) (V t))
    (fun t => differenceEnvelope (u t) (U t) (v t) (V t))
    (fun t => referenceEnvelope (H t) (K t))
    (fun t => directionEnvelope (h t) (H t) (k t) (K t))

theorem inner_joint_measurable (α c : ℝ) {u h v : ℝ → Space → ℂ}
    (hu : AEStronglyMeasurable (fun z : ℝ × Space => u z.1 z.2) (volume.prod volume))
    (hh : AEStronglyMeasurable (fun z : ℝ × Space => h z.1 z.2) (volume.prod volume))
    (hv : AEStronglyMeasurable (fun z : ℝ × Space => v z.1 z.2) (volume.prod volume)) :
    AEStronglyMeasurable (fun z : ℝ × Space => innerCross α c u h v z.1 z.2) (volume.prod volume) :=
  (joint_riesz_measurable volume α c (fun t => directionalDensity α (u t) (h t))
    (density_action_measurable (volume.prod volume) (3+α) hu hh)).smul
      ((hv.norm.aemeasurable.pow_const (1+α)).aestronglyMeasurable.smul hv)

theorem outer_joint_measurable (α c : ℝ) {u v k : ℝ → Space → ℂ}
    (hu : AEStronglyMeasurable (fun z : ℝ × Space => u z.1 z.2) (volume.prod volume))
    (hv : AEStronglyMeasurable (fun z : ℝ × Space => v z.1 z.2) (volume.prod volume))
    (hk : AEStronglyMeasurable (fun z : ℝ × Space => k z.1 z.2) (volume.prod volume)) :
    AEStronglyMeasurable (fun z : ℝ × Space => outerCross α c u v k z.1 z.2) (volume.prod volume) :=
  (joint_riesz_measurable volume α c (fun t x => ‖u t x‖^(3+α))
    (hu.norm.aemeasurable.pow_const (3+α)).aestronglyMeasurable).smul
      (local_factor_action_measurable (volume.prod volume) (1+α) hv hk)

/-- One uniform constant controls each separate mixed-label derivative placement
in the actual L²_t L^(6/5)_x norm. The same-field signed forcing estimate is unused. -/
theorem cross_pair_mixed_difference_budget {α c : ℝ} (hHLS : OrdinaryHLS α c) :
    ∃ C : ℝ≥0, ∀ (u U h H v V k K : ℝ → Space → ℂ),
      JointInputs u U h H v V k K →
      (∀ᵐ t ∂(volume : Measure ℝ), SliceInputs (u t) (U t) (h t) (H t) (v t) (V t) (k t) (K t)) →
      forcingNorm (innerCross α c u h v-innerCross α c U H V) ≤
        (C : ℝ≥0∞)*crossBudget α u U h H v V k K ∧
      forcingNorm (outerCross α c u v k-outerCross α c U V K) ≤
        (C : ℝ≥0∞)*crossBudget α u U h H v V k K := by
  obtain ⟨C,hC⟩ := cross_pair_spatial_bound hHLS
  refine ⟨C,?_⟩
  intro u U h H v V k K hJ hSlices
  let A := fun t => valueEnvelope (u t) (U t) (v t) (V t)
  let B := fun t => differenceEnvelope (u t) (U t) (v t) (V t)
  let Y := fun t => referenceEnvelope (H t) (K t)
  let Z := fun t => directionEnvelope (h t) (H t) (k t) (K t)
  have hA : AEStronglyMeasurable (fun z : ℝ × Space => A z.1 z.2) (volume.prod volume) :=
    (hJ.uM.norm.add hJ.UM.norm).add (hJ.vM.norm.add hJ.VM.norm)
  have hB : AEStronglyMeasurable (fun z : ℝ × Space => B z.1 z.2) (volume.prod volume) :=
    (hJ.uM.sub hJ.UM).norm.add (hJ.vM.sub hJ.VM).norm
  have hY : AEStronglyMeasurable (fun z : ℝ × Space => Y z.1 z.2) (volume.prod volume) :=
    hJ.HM.norm.add hJ.KM.norm
  have hZ : AEStronglyMeasurable (fun z : ℝ × Space => Z z.1 z.2) (volume.prod volume) :=
    (hJ.hM.sub hJ.HM).norm.add (hJ.kM.sub hJ.KM).norm
  have hs := hSlices.mono fun t ht => hC (u t) (U t) (h t) (H t) (v t) (V t) (k t) (K t)
    ht.u6 ht.U6 ht.v6 ht.V6 ht.u10 ht.U10 ht.v10 ht.V10 ht.hW ht.HW ht.kW ht.KW
  have him := (inner_joint_measurable α c hJ.uM hJ.hM hJ.vM).sub
    (inner_joint_measurable α c hJ.UM hJ.HM hJ.VM)
  have hom := (outer_joint_measurable α c hJ.uM hJ.vM hJ.kM).sub
    (outer_joint_measurable α c hJ.UM hJ.VM hJ.KM)
  have hinorm := spatial_lp_time_measurable volume volume (ENNReal.ofReal (6/5 : ℝ))
    (by norm_num) ENNReal.ofReal_ne_top (innerCross α c u h v-innerCross α c U H V) him
  have honorm := spatial_lp_time_measurable volume volume (ENNReal.ofReal (6/5 : ℝ))
    (by norm_num) ENNReal.ofReal_ne_top (outerCross α c u v k-outerCross α c U V K) hom
  have hiFin : ∀ᵐ t ∂(volume : Measure ℝ),
      eLpNorm ((innerCross α c u h v-innerCross α c U H V) t) (ENNReal.ofReal (6/5 : ℝ)) volume ≠ ∞ :=
    hs.mono fun _ ht => ht.1.1.eLpNorm_ne_top
  have hoFin : ∀ᵐ t ∂(volume : Measure ℝ),
      eLpNorm ((outerCross α c u v k-outerCross α c U V K) t) (ENNReal.ofReal (6/5 : ℝ)) volume ≠ ∞ :=
    hs.mono fun _ ht => ht.2.1.eLpNorm_ne_top
  exact ⟨finite_dominated_three_weights hHLS.order_pos hHLS.order_lt_three volume C _ A B Y Z
    hinorm hiFin hA hB hY hZ (hs.mono fun _ ht => ht.1.2),
    finite_dominated_three_weights hHLS.order_pos hHLS.order_lt_three volume C _ A B Y Z
    honorm hoFin hA hB hY hZ (hs.mono fun _ ht => ht.2.2)⟩

#print axioms inner_joint_measurable
#print axioms outer_joint_measurable
#print axioms cross_pair_mixed_difference_budget
end HartreeF.CrossContinuity
