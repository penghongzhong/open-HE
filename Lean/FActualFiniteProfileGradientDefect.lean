import FFiniteProfileCandidateLimit
import FFiniteProfileWeakGradient
import FGeneralVectorReassembly

/-! One actual finite-profile producer: every-index genuine Euclidean N domain,
the original-filter zero limit, and the real/imaginary weak gradient of the SAME
literal forcing error. This is a fixed finite active family, not an infinite-tail
or nonlinear critical-element theorem. Author source, UNCOMPILED. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
namespace HartreeF.ActualFiniteProfileGradientDefect
open TimeHolder EnergySpace CriticalTimeSobolev SobolevStretch ForcingDomain
open StationarySelfTest ProfileSpatialSmoothing
open GeneralProfileCross ProfileApproximation FiniteProfileFrameData
open FiniteCandidateExpansion FiniteProfileCandidateLimit FiniteProfileWeakGradient

/-- All labels are continuous actual profiles; analytic domains and frame
orthogonality are required only for the finite active set. Inactive zero padding
therefore imposes no fictitious orthogonality condition. No scalar L2, variance,
target residual norm, or new nonlinear ordinary interface is an input. -/
theorem actual_finite_profile_gradient_defect
    {ι ν : Type*} [DecidableEq ι] {l : Filter ν}
    (hDensity : OrdinaryH1Density) {K : ℝ} (hSob : OrdinarySobolev K)
    {α c : ℝ} (hH : OrdinaryHLS α c)
    (s : Finset ι) (g : ι → ℝ → EnergyState)
    (hg : ∀ i, Continuous (g i))
    (hE : ∀ i ∈ s, curveEnergy (g i) ≠ ∞)
    (hS : ∀ i ∈ s, mixedNorm volume volume 10 10 (stateValueField (g i)) ≠ ∞)
    (hW : ∀ i ∈ s, mixedNorm volume volume 10 (ENNReal.ofReal (30/13 : ℝ))
      (fun t => complexGradient (stateRealGradientField (g i) t)
        (stateImagGradientField (g i) t)) ≠ ∞)
    (a : ι → ν → ℝ) (y : ι → ν → Space) (τ : ι → ν → ℝ)
    (ha : ∀ i ∈ s, ∀ n, 0 < a i n)
    (horth : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      Tendsto (frameSeparation a y τ i j) l atTop) :
    let u := fun n i => framedValue (g i) (a i n) (y i n) (τ i n)
    let U := fun n i => framedReal (g i) (a i n) (y i n) (τ i n)
    let V := fun n i => framedImag (g i) (a i n) (y i n) (τ i n)
    let E := fun n t => literalDefect s α c (fun i => u n i t)
    let D := fun n t => gradientDefect s α c (fun i => u n i t)
      (fun i => U n i t) (fun i => V n i t)
    (∀ n, vectorForcingNorm (D n) ≠ ∞) ∧
    Tendsto (fun n => vectorForcingNorm (D n)) l (𝓝 0) ∧
    (∀ n, ∀ᵐ t ∂volume,
      HasWeakGradient (fun x => (E n t x).re) (fun x => gradientReal (D n t x)) ∧
      HasWeakGradient (fun x => (E n t x).im) (fun x => gradientImag (D n t x)) ∧
      CoordinateTests (E n t) (D n t)) := by
  classical
  let : SecondCountableTopologyEither ℝ EnergyState := ⟨Or.inl inferInstance⟩
  dsimp only
  let r : ∀ i, EnergyJointFields volume (g i) :=
    fun i => energyJointFields volume (g i) (hg i).aestronglyMeasurable
  let u := jointValue g r a y τ
  let h := jointDirection g r a y τ
  let P := fun n i => framedJointReal (r i) (a i n) (y i n) (τ i n)
  let Q := fun n i => framedJointImag (r i) (a i n) (y i n) (τ i n)
  let G : ν → ℝ → Space → EuclideanSpace ℂ (Fin 3) := fun n t =>
    jointCandidateDefect s α c (fun i => u n i t) (fun i => P n i t) (fun i => Q n i t)
  have hInput (k : Fin 3) : FramedInputPacket s l α c u (h k) :=
    actual_framed_input_packet hSob hH s g (fun i _ => hg i) hE hS hW r a y τ ha horth k
  have hScalar (k : Fin 3) := candidate_defect_finite_tendsto hH s u (h k) (hInput k)
  have hTransfer (n : ν) := actual_finite_framed_candidate_transfer hH s g r
    (fun i => a i n) (fun i => τ i n) (fun i => y i n)
    (fun i hi => ha i hi n) hS hW
  have hG (n : ν) : AEStronglyMeasurable
      (fun z : ℝ × Space => G n z.1 z.2) (volume.prod volume) :=
    (hTransfer n).1
  have hCoord (n : ν) (k : Fin 3) :
      (fun t x => G n t x k) =
        (fun t x => candidateDefect α c s (fun i => u n i t) (fun i => h k n i t) x) := by
    funext t x
    change jointCandidateDefect s α c (fun i => u n i t)
      (fun i => P n i t) (fun i => Q n i t) x k = _
    rw [jointCandidateDefect_coordinate]
    congr 1
    funext i
    exact framedJoint_directionalField (r i) (a i n) (y i n) (τ i n) k t
  have hCoordFinite (n : ν) (k : Fin 3) :
      CompactCross.forcingNorm (fun t x => G n t x k) ≠ ∞ := by
    rw [hCoord n k]
    exact (hScalar k).1 n
  have hFinite (n : ν) : vectorForcingNorm (G n) ≠ ∞ :=
    ne_top_of_le_ne_top
      (ENNReal.sum_ne_top.mpr (fun k _ => hCoordFinite n k))
      (vectorForcingNorm_le_sum_of_joint (G n) (hG n))
  have hLimit : Tendsto (fun n => vectorForcingNorm (G n)) l (𝓝 0) := by
    apply vectorForcingNorm_tendsto_zero_of_joint G hG
    intro k
    simpa only [hCoord] using (hScalar k).2
  have hNorm (n : ν) :
      vectorForcingNorm (fun t => gradientDefect s α c
        (fun i => framedValue (g i) (a i n) (y i n) (τ i n) t)
        (fun i => framedReal (g i) (a i n) (y i n) (τ i n) t)
        (fun i => framedImag (g i) (a i n) (y i n) (τ i n) t)) =
      vectorForcingNorm (G n) := by
    apply eLpNorm_congr_ae
    filter_upwards [(hTransfer n).2] with t ht
    exact eLpNorm_congr_ae ht
  refine ⟨fun n => ?_, ?_, ?_⟩
  · rw [hNorm n]
    exact hFinite n
  · exact hLimit.congr' (Filter.Eventually.of_forall fun n => (hNorm n).symm)
  · intro n
    exact (actual_finite_framed_weak_gradients hDensity hSob hH s g
      (fun i => a i n) (fun i => τ i n) (fun i => y i n)
      (fun i hi => ha i hi n) hS hW).mono
        (fun _ ht => ⟨ht.1, ht.2.1, ht.2.2.1⟩)

#print axioms actual_finite_profile_gradient_defect
end HartreeF.ActualFiniteProfileGradientDefect
