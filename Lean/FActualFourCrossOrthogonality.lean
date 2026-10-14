import FGeneralPackedCrossOrthogonality
import FGeneralPackedCoupling
import FActualCoupledApproximationAdapter

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
namespace HartreeF.GeneralProfileCross
open TimeHolder ProfileApproximation ProfileSpatialSmoothing SobolevStretch CompactCross
  EnergySpace CriticalTimeSobolev ForcingDomain
attribute [local instance 101] secondCountableTopologyEither_of_left
attribute [local irreducible] energySubmodule

/-- A convenience projection of the native common coupled family, retaining the
same actual value/real-gradient/imaginary-gradient construction for every coordinate. -/
theorem actual_coordinate_approximations {K : ℝ} (hSob : OrdinarySobolev K)
    (g : ℝ → EnergyState) (hg : Continuous g) (hE : curveEnergy g ≠ ∞)
    (hS : mixedNorm volume volume 10 10 (stateValueField g) ≠ ∞)
    (hW : mixedNorm volume volume 10 (ENNReal.ofReal (30/13 : ℝ))
      (fun t => complexGradient (stateRealGradientField g t) (stateImagGradientField g t)) ≠ ∞)
    (r : EnergyJointFields volume g) :
    Nonempty (∀ j : Fin 3, ScalarCompactApproximation r.u
      (gradientCoordinate j (fun t => complexGradient (r.U t) (r.V t)))) := by
  classical
  obtain ⟨_,_,_,_,h⟩ := exists_actual_coupled_scalar_compact_approximation hSob g hg hE hS hW r
  exact ⟨fun j => Classical.choose (h j)⟩

/-- Each of the four literal directional cross terms tends to zero for the original
canonical EnergyState value and its actual weak derivative, along the entire filter. -/
theorem actual_four_scalar_cross_orthogonality {ι : Type*} {l : Filter ι}
    {α c K : ℝ} (hSob : OrdinarySobolev K) (hHLS : OrdinaryHLS α c)
    (g₁ g₂ : ℝ → EnergyState) (hg₁ : Continuous g₁) (hg₂ : Continuous g₂)
    (hE₁ : curveEnergy g₁ ≠ ∞) (hE₂ : curveEnergy g₂ ≠ ∞)
    (hS₁ : mixedNorm volume volume 10 10 (stateValueField g₁) ≠ ∞)
    (hS₂ : mixedNorm volume volume 10 10 (stateValueField g₂) ≠ ∞)
    (hW₁ : mixedNorm volume volume 10 (ENNReal.ofReal (30/13 : ℝ))
      (fun t => complexGradient (stateRealGradientField g₁ t) (stateImagGradientField g₁ t)) ≠ ∞)
    (hW₂ : mixedNorm volume volume 10 (ENNReal.ofReal (30/13 : ℝ))
      (fun t => complexGradient (stateRealGradientField g₂ t) (stateImagGradientField g₂ t)) ≠ ∞)
    (j : Fin 3) {a b s r : ι → ℝ} {y z : ι → Space}
    (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (horth : Tendsto (fun i => a i/b i+b i/a i+‖y i-z i‖^2/(a i*b i)+
      |a i^2*s i-b i^2*r i|/(a i*b i)) l atTop) :
    let u₁ := fun i => seedFrame (a i) (y i) (s i) (1/2) (stateValueField g₁)
    let u₂ := fun i => seedFrame (b i) (z i) (r i) (1/2) (stateValueField g₂)
    let h₁ := fun i => seedFrame (a i) (y i) (s i) (3/2) (fun t => (energyGradient j (g₁ t) : Space → ℂ))
    let h₂ := fun i => seedFrame (b i) (z i) (r i) (3/2) (fun t => (energyGradient j (g₂ t) : Space → ℂ))
    Tendsto (fun i => forcingNorm (innerCross α c (u₁ i) (h₁ i) (u₂ i))) l (𝓝 0) ∧
    Tendsto (fun i => forcingNorm (outerCross α c (u₁ i) (u₂ i) (h₂ i))) l (𝓝 0) ∧
    Tendsto (fun i => forcingNorm (innerCross α c (u₂ i) (h₂ i) (u₁ i))) l (𝓝 0) ∧
    Tendsto (fun i => forcingNorm (outerCross α c (u₂ i) (u₁ i) (h₁ i))) l (𝓝 0) := by
  let r₁ := energyJointFields volume g₁ hg₁.aestronglyMeasurable
  let r₂ := energyJointFields volume g₂ hg₂.aestronglyMeasurable
  obtain ⟨A⟩ := actual_coordinate_approximations hSob g₁ hg₁ hE₁ hS₁ hW₁ r₁
  obtain ⟨B⟩ := actual_coordinate_approximations hSob g₂ hg₂ hE₂ hS₂ hW₂ r₂
  have ht := scalar_four_cross_orthogonality hHLS (A j) (B j) ha hb horth
  have he (i : ι) := framed_jointFields_four_forcingNorm_eq α c g₁ g₂ r₁ r₂ j
    (ha i) (hb i) (y i) (z i) (s i) (r i)
  exact ⟨ht.1.congr' (Filter.Eventually.of_forall fun i => (he i).1.symm),
    ht.2.1.congr' (Filter.Eventually.of_forall fun i => (he i).2.1.symm),
    ht.2.2.1.congr' (Filter.Eventually.of_forall fun i => (he i).2.2.1.symm),
    ht.2.2.2.congr' (Filter.Eventually.of_forall fun i => (he i).2.2.2.symm)⟩

/-- Four separate genuine Euclidean-gradient forcing norms vanish for two actual
continuous homogeneous-energy profiles with finite E/S/W and orthogonal physical frames.
No scalar L2, variance, profile-density interface, or subsequence premise appears. -/
theorem actual_four_vector_cross_orthogonality {ι : Type*} {l : Filter ι}
    {α c K : ℝ} (hSob : OrdinarySobolev K) (hHLS : OrdinaryHLS α c)
    (g₁ g₂ : ℝ → EnergyState) (hg₁ : Continuous g₁) (hg₂ : Continuous g₂)
    (hE₁ : curveEnergy g₁ ≠ ∞) (hE₂ : curveEnergy g₂ ≠ ∞)
    (hS₁ : mixedNorm volume volume 10 10 (stateValueField g₁) ≠ ∞)
    (hS₂ : mixedNorm volume volume 10 10 (stateValueField g₂) ≠ ∞)
    (hW₁ : mixedNorm volume volume 10 (ENNReal.ofReal (30/13 : ℝ))
      (fun t => complexGradient (stateRealGradientField g₁ t) (stateImagGradientField g₁ t)) ≠ ∞)
    (hW₂ : mixedNorm volume volume 10 (ENNReal.ofReal (30/13 : ℝ))
      (fun t => complexGradient (stateRealGradientField g₂ t) (stateImagGradientField g₂ t)) ≠ ∞)
    {a b s r : ι → ℝ} {y z : ι → Space}
    (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (horth : Tendsto (fun i => a i/b i+b i/a i+‖y i-z i‖^2/(a i*b i)+
      |a i^2*s i-b i^2*r i|/(a i*b i)) l atTop) :
    let u₁ := fun i => seedFrame (a i) (y i) (s i) (1/2) (stateValueField g₁)
    let u₂ := fun i => seedFrame (b i) (z i) (r i) (1/2) (stateValueField g₂)
    let h₁ := fun i => gradientFrame (a i) (y i) (s i)
      (fun t => complexGradient (stateRealGradientField g₁ t) (stateImagGradientField g₁ t))
    let h₂ := fun i => gradientFrame (b i) (z i) (r i)
      (fun t => complexGradient (stateRealGradientField g₂ t) (stateImagGradientField g₂ t))
    Tendsto (fun i => vectorForcingNorm (packedInnerCross α c (u₁ i) (h₁ i) (u₂ i))) l (𝓝 0) ∧
    Tendsto (fun i => vectorForcingNorm (packedOuterCross α c (u₁ i) (u₂ i) (h₂ i))) l (𝓝 0) ∧
    Tendsto (fun i => vectorForcingNorm (packedInnerCross α c (u₂ i) (h₂ i) (u₁ i))) l (𝓝 0) ∧
    Tendsto (fun i => vectorForcingNorm (packedOuterCross α c (u₂ i) (u₁ i) (h₁ i))) l (𝓝 0) := by
  let r₁ := energyJointFields volume g₁ hg₁.aestronglyMeasurable
  let r₂ := energyJointFields volume g₂ hg₂.aestronglyMeasurable
  obtain ⟨A⟩ := actual_coordinate_approximations hSob g₁ hg₁ hE₁ hS₁ hW₁ r₁
  obtain ⟨B⟩ := actual_coordinate_approximations hSob g₂ hg₂ hE₂ hS₂ hW₂ r₂
  have ht := packed_four_cross_orthogonality hHLS
    (packedGradient_joint_stronglyMeasurable r₁.joint_U r₁.joint_V)
    (packedGradient_joint_stronglyMeasurable r₂.joint_U r₂.joint_V) A B ha hb horth
  have he (i : ι) := framed_jointFields_four_vectorNorm_eq α c g₁ g₂ r₁ r₂
    (ha i) (hb i) (y i) (z i) (s i) (r i)
  exact ⟨ht.1.congr' (Filter.Eventually.of_forall fun i => (he i).1.symm),
    ht.2.1.congr' (Filter.Eventually.of_forall fun i => (he i).2.1.symm),
    ht.2.2.1.congr' (Filter.Eventually.of_forall fun i => (he i).2.2.1.symm),
    ht.2.2.2.congr' (Filter.Eventually.of_forall fun i => (he i).2.2.2.symm)⟩

#print axioms actual_coordinate_approximations
#print axioms actual_four_scalar_cross_orthogonality
#print axioms actual_four_vector_cross_orthogonality
end HartreeF.GeneralProfileCross
