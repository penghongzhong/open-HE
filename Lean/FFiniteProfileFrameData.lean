import FActualFourCrossOrthogonality
import FGeneralLocalProducts
import FLocalProductRepresentatives
import FFiniteProfileCrossDomains

/-! Internal finite-family framed-input data for the actual gradient defect.
Author source, UNCOMPILED. One supplied EnergyJointFields family is used in every
coordinate, every local product, every pure cross and every canonical bridge.
Only active labels need continuity, finite E/S/W, positive frames or separation.
-/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1500000
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
namespace HartreeF.FiniteProfileFrameData
open TimeHolder ProfileApproximation ProfileSpatialSmoothing SobolevStretch CompactCross
  EnergySpace CriticalTimeSobolev ForcingDomain GeneralProfileCross LocalProfileProducts

variable {ι ν : Type*} [DecidableEq ι]

/-- The literal jointly measurable framed value, on the original index. -/
def jointValue (g : ι → ℝ → EnergyState) (r : ∀ i, EnergyJointFields volume (g i))
    (a : ι → ν → ℝ) (y : ι → ν → Space) (τ : ι → ν → ℝ)
    (n : ν) (i : ι) : ℝ → Space → ℂ :=
  seedFrame (a i n) (y i n) (τ i n) (1/2) (r i).u

/-- Its true derivative coordinate uses the same representative family. -/
def jointDirection (g : ι → ℝ → EnergyState) (r : ∀ i, EnergyJointFields volume (g i))
    (a : ι → ν → ℝ) (y : ι → ν → Space) (τ : ι → ν → ℝ)
    (k : Fin 3) (n : ν) (i : ι) : ℝ → Space → ℂ :=
  seedFrame (a i n) (y i n) (τ i n) (3/2)
    (gradientCoordinate k (fun t => complexGradient ((r i).U t) ((r i).V t)))

def canonicalValue (g : ι → ℝ → EnergyState)
    (a : ι → ν → ℝ) (y : ι → ν → Space) (τ : ι → ν → ℝ)
    (n : ν) (i : ι) : ℝ → Space → ℂ :=
  seedFrame (a i n) (y i n) (τ i n) (1/2) (stateValueField (g i))

def canonicalDirection (g : ι → ℝ → EnergyState)
    (a : ι → ν → ℝ) (y : ι → ν → Space) (τ : ι → ν → ℝ)
    (k : Fin 3) (n : ν) (i : ι) : ℝ → Space → ℂ :=
  seedFrame (a i n) (y i n) (τ i n) (3/2)
    (fun t => (energyGradient k (g i t) : Space → ℂ))

/-- Source-order physical separation. It has no subsequence or transformed shift. -/
def frameSeparation (a : ι → ν → ℝ) (y : ι → ν → Space) (τ : ι → ν → ℝ)
    (i j : ι) (n : ν) : ℝ :=
  a i n / a j n + a j n / a i n + ‖y i n - y j n‖^2 / (a i n * a j n) +
    |(a i n)^2 * τ i n - (a j n)^2 * τ j n| / (a i n * a j n)

/-- Genuine input domains and orthogonality conclusions, rather than a new
analytic interface. The producer below fills every field from actual profiles. -/
structure FramedInputPacket (s : Finset ι) (l : Filter ν) (α c : ℝ)
    (u h : ν → ι → ℝ → Space → ℂ) : Prop where
  profile : ∀ n i, i ∈ s → ScalarProfile (u n i) (h n i)
  uniform_bound : ∃ M : ℝ≥0, ∀ n,
    (∑ i ∈ s, mixedNorm volume volume ∞ 6 (u n i)) ≤ (M : ℝ≥0∞) ∧
    (∑ i ∈ s, mixedNorm volume volume 10 10 (u n i)) ≤ (M : ℝ≥0∞) ∧
    (∑ i ∈ s, mixedNorm volume volume 10 (ENNReal.ofReal (30/13 : ℝ)) (h n i)) ≤
      (M : ℝ≥0∞)
  local_finite : ∀ n i, i ∈ s → ∀ j, j ∈ s →
    localProductNorm 5 (u n i) (u n j) ≠ ∞ ∧
    localProductNorm (ENNReal.ofReal (15/8 : ℝ)) (u n i) (h n j) ≠ ∞ ∧
    localProductNorm (ENNReal.ofReal (15/8 : ℝ)) (u n j) (h n i) ≠ ∞
  local_zero : ∀ i, i ∈ s → ∀ j, j ∈ s → i ≠ j →
    Tendsto (fun n => localProductNorm 5 (u n i) (u n j)) l (𝓝 0) ∧
    Tendsto (fun n => localProductNorm (ENNReal.ofReal (15/8 : ℝ))
      (u n i) (h n j)) l (𝓝 0) ∧
    Tendsto (fun n => localProductNorm (ENNReal.ofReal (15/8 : ℝ))
      (u n j) (h n i)) l (𝓝 0)
  cross_finite : ∀ n i, i ∈ s → ∀ j, j ∈ s →
    forcingNorm (innerCross α c (u n i) (h n i) (u n j)) ≠ ∞ ∧
    forcingNorm (outerCross α c (u n i) (u n j) (h n j)) ≠ ∞ ∧
    forcingNorm (innerCross α c (u n j) (h n j) (u n i)) ≠ ∞ ∧
    forcingNorm (outerCross α c (u n j) (u n i) (h n i)) ≠ ∞
  cross_zero : ∀ i, i ∈ s → ∀ j, j ∈ s → i ≠ j →
    Tendsto (fun n => forcingNorm (innerCross α c (u n i) (h n i) (u n j))) l (𝓝 0) ∧
    Tendsto (fun n => forcingNorm (outerCross α c (u n i) (u n j) (h n j))) l (𝓝 0) ∧
    Tendsto (fun n => forcingNorm (innerCross α c (u n j) (h n j) (u n i))) l (𝓝 0) ∧
    Tendsto (fun n => forcingNorm (outerCross α c (u n j) (u n i) (h n i))) l (𝓝 0)

omit [DecidableEq ι] in
/-- A finite, index-independent cap comes from the true input V/S/W norms.
It bounds each of the three finite sums and also handles the empty family. -/
theorem finite_frame_uniform_bound (s : Finset ι) (u h : ι → ℝ → Space → ℂ)
    (hp : ∀ i, i ∈ s → ScalarProfile (u i) (h i))
    (a : ι → ν → ℝ) (y : ι → ν → Space) (τ : ι → ν → ℝ)
    (ha : ∀ i, i ∈ s → ∀ n, 0 < a i n) :
    ∃ M : ℝ≥0, ∀ n,
      (∑ i ∈ s, mixedNorm volume volume ∞ 6
        (seedFrame (a i n) (y i n) (τ i n) (1/2) (u i))) ≤ (M : ℝ≥0∞) ∧
      (∑ i ∈ s, mixedNorm volume volume 10 10
        (seedFrame (a i n) (y i n) (τ i n) (1/2) (u i))) ≤ (M : ℝ≥0∞) ∧
      (∑ i ∈ s, mixedNorm volume volume 10 (ENNReal.ofReal (30/13 : ℝ))
        (seedFrame (a i n) (y i n) (τ i n) (3/2) (h i))) ≤ (M : ℝ≥0∞) := by
  let B : ℝ≥0∞ := ∑ i ∈ s,
    (mixedNorm volume volume ∞ 6 (u i) + mixedNorm volume volume 10 10 (u i) +
      mixedNorm volume volume 10 (ENNReal.ofReal (30/13 : ℝ)) (h i))
  have hB : B ≠ ∞ := ENNReal.sum_ne_top.mpr (fun i hi =>
    ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr
      ⟨(hp i hi).value_V, (hp i hi).value_S⟩, (hp i hi).gradient_W⟩)
  refine ⟨B.toNNReal, fun n => ?_⟩
  simp only [ENNReal.coe_toNNReal hB]
  refine ⟨?_, ?_, ?_⟩
  · calc
      (∑ i ∈ s, mixedNorm volume volume ∞ 6
          (seedFrame (a i n) (y i n) (τ i n) (1/2) (u i))) =
          ∑ i ∈ s, mixedNorm volume volume ∞ 6 (u i) :=
        Finset.sum_congr rfl (fun i hi => seedFrame_V_invariant (ha i hi n)
          (y i n) (τ i n) (u i) (hp i hi).value_joint.aestronglyMeasurable)
      _ ≤ B := Finset.sum_le_sum (fun _ _ =>
        (le_add_right le_rfl).trans (le_add_right le_rfl))
  · calc
      (∑ i ∈ s, mixedNorm volume volume 10 10
          (seedFrame (a i n) (y i n) (τ i n) (1/2) (u i))) =
          ∑ i ∈ s, mixedNorm volume volume 10 10 (u i) :=
        Finset.sum_congr rfl (fun i hi => seedFrame_S_invariant (ha i hi n)
          (y i n) (τ i n) (u i) (hp i hi).value_joint.aestronglyMeasurable)
      _ ≤ B := Finset.sum_le_sum (fun _ _ =>
        (le_add_left le_rfl).trans (le_add_right le_rfl))
  · calc
      (∑ i ∈ s, mixedNorm volume volume 10 (ENNReal.ofReal (30/13 : ℝ))
          (seedFrame (a i n) (y i n) (τ i n) (3/2) (h i))) =
          ∑ i ∈ s, mixedNorm volume volume 10 (ENNReal.ofReal (30/13 : ℝ)) (h i) :=
        Finset.sum_congr rfl (fun i hi => seedFrame_W_invariant (ha i hi n)
          (y i n) (τ i n) (h i) (hp i hi).gradient_joint.aestronglyMeasurable)
      _ ≤ B := Finset.sum_le_sum (fun _ _ => le_add_left le_rfl)

omit [DecidableEq ι] in
/-- Actual finite-family specialization. Every analytic hypothesis is an
ordinary pre-existing one, or a true finite input norm. All pair limits are
produced, not assumed, and finiteness is independently proved at every index. -/
theorem actual_framed_input_packet {l : Filter ν} {α c K : ℝ}
    (hSob : OrdinarySobolev K) (hH : OrdinaryHLS α c)
    (s : Finset ι) (g : ι → ℝ → EnergyState)
    (hg : ∀ i, i ∈ s → Continuous (g i))
    (hE : ∀ i, i ∈ s → curveEnergy (g i) ≠ ∞)
    (hS : ∀ i, i ∈ s → mixedNorm volume volume 10 10 (stateValueField (g i)) ≠ ∞)
    (hW : ∀ i, i ∈ s → mixedNorm volume volume 10 (ENNReal.ofReal (30/13 : ℝ))
      (fun t => complexGradient (stateRealGradientField (g i) t)
        (stateImagGradientField (g i) t)) ≠ ∞)
    (r : ∀ i, EnergyJointFields volume (g i))
    (a : ι → ν → ℝ) (y : ι → ν → Space) (τ : ι → ν → ℝ)
    (ha : ∀ i, i ∈ s → ∀ n, 0 < a i n)
    (horth : ∀ i, i ∈ s → ∀ j, j ∈ s → i ≠ j →
      Tendsto (frameSeparation a y τ i j) l atTop)
    (k : Fin 3) :
    FramedInputPacket s l α c (jointValue g r a y τ) (jointDirection g r a y τ k) := by
  classical
  let A (i : {i : ι // i ∈ s}) : ∀ k : Fin 3, ScalarCompactApproximation (r i.1).u
      (gradientCoordinate k (fun t => complexGradient ((r i.1).U t) ((r i.1).V t))) :=
    Classical.choice (actual_coordinate_approximations hSob (g i.1) (hg i.1 i.2)
      (hE i.1 i.2) (hS i.1 i.2) (hW i.1 i.2) (r i.1))
  have hp (i : ι) (hi : i ∈ s) : ScalarProfile (r i).u
      (gradientCoordinate k (fun t => complexGradient ((r i).U t) ((r i).V t))) :=
    (A ⟨i, hi⟩ k).profile
  have hf (n : ν) (i : ι) (hi : i ∈ s) :
      ScalarProfile (jointValue g r a y τ n i) (jointDirection g r a y τ k n i) :=
    (hp i hi).frame (ha i hi n) (y i n) (τ i n)
  refine ⟨hf, ?_, ?_, ?_, ?_, ?_⟩
  · exact finite_frame_uniform_bound s (fun i => (r i).u)
      (fun i => gradientCoordinate k (fun t => complexGradient ((r i).U t) ((r i).V t)))
      hp a y τ ha
  · intro n i hi j hj
    exact scalar_frame_PQQ_finite (hp i hi) (hp j hj) (ha i hi n) (ha j hj n)
      (y i n) (y j n) (τ i n) (τ j n)
  · intro i hi j hj hij
    exact scalar_PQQ_orthogonality (A ⟨i, hi⟩ k) (A ⟨j, hj⟩ k)
      (ha i hi) (ha j hj) (horth i hi j hj hij)
  · intro n i hi j hj
    have hij := FiniteProfileCrossDomains.scalar_cross_finite hH (hf n i hi) (hf n j hj)
    have hji := FiniteProfileCrossDomains.scalar_cross_finite hH (hf n j hj) (hf n i hi)
    exact ⟨hij.1, hij.2, hji.1, hji.2⟩
  · intro i hi j hj hij
    exact scalar_four_cross_orthogonality hH (A ⟨i, hi⟩ k) (A ⟨j, hj⟩ k)
      (ha i hi) (ha j hj) (horth i hi j hj hij)

omit [DecidableEq ι] in
/-- The canonical quotient value is transported by nested AE equality; no
joint measurability of canonical representatives is asserted. -/
theorem canonical_joint_value_nested_ae (g : ι → ℝ → EnergyState)
    (r : ∀ i, EnergyJointFields volume (g i))
    (a : ι → ν → ℝ) (y : ι → ν → Space) (τ : ι → ν → ℝ)
    (n : ν) (i : ι) (ha : 0 < a i n) :
    ∀ᵐ t ∂volume, canonicalValue g a y τ n i t =ᵐ[volume] jointValue g r a y τ n i t :=
  seedFrame_jointFields_value_nested_ae (g i) (r i) ha (y i n) (τ i n)

omit [DecidableEq ι] in
/-- The canonical true energy derivative has its own nested AE bridge. -/
theorem canonical_joint_direction_nested_ae (g : ι → ℝ → EnergyState)
    (r : ∀ i, EnergyJointFields volume (g i))
    (a : ι → ν → ℝ) (y : ι → ν → Space) (τ : ι → ν → ℝ)
    (k : Fin 3) (n : ν) (i : ι) (ha : 0 < a i n) :
    ∀ᵐ t ∂volume, canonicalDirection g a y τ k n i t =ᵐ[volume]
      jointDirection g r a y τ k n i t :=
  seedFrame_jointFields_gradient_nested_ae (g i) (r i) k ha (y i n) (τ i n)

omit [DecidableEq ι] in
/-- All labels and all three coordinates can be used on the same conull time set. -/
theorem canonical_joint_common_nested_ae (s : Finset ι) (g : ι → ℝ → EnergyState)
    (r : ∀ i, EnergyJointFields volume (g i))
    (a : ι → ν → ℝ) (y : ι → ν → Space) (τ : ι → ν → ℝ)
    (n : ν) (ha : ∀ i, i ∈ s → 0 < a i n) :
    ∀ᵐ t ∂volume, ∀ i ∈ s,
      canonicalValue g a y τ n i t =ᵐ[volume] jointValue g r a y τ n i t ∧
      ∀ k : Fin 3, canonicalDirection g a y τ k n i t =ᵐ[volume]
        jointDirection g r a y τ k n i t := by
  apply (eventually_all_finset s).2
  intro i hi
  filter_upwards [canonical_joint_value_nested_ae g r a y τ n i (ha i hi),
    eventually_all.mpr (fun k : Fin 3 =>
      canonical_joint_direction_nested_ae g r a y τ k n i (ha i hi))] with t hv hh
  exact ⟨hv, hh⟩

end HartreeF.FiniteProfileFrameData
