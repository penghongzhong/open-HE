import SobolevHartreeStretch
import PhysicalDirectionalTangent
import DirectionalThresholdBridge

/-!
Conditional actual-function variational threshold consumers. The universal
normalized Hartree-Sobolev bound on every complex function with its actual weak
gradients is an explicit internal mathematical premise, not an accepted external
standard interface. A separate native composition producer must supply it. It does not assume any particular
stretch, directional pressure bound, or DC conclusion. Its threshold G is
explicit: existence, optimality, and identification with a ground state are
not asserted by this interface or by this module.
-/
noncomputable section
set_option autoImplicit false
open MeasureTheory Set
namespace HartreeF.DirectionalCoercivity
open SobolevStretch PhysicalStretch PhysicalSpectral HeatRiesz ForcingDomain

def interaction (α : ℝ) (u : Space → ℂ) : ℝ :=
  ∫ x, potential α (standardRieszConstant α) u x * powerDensity α u x

def energy (α : ℝ) (u : Space → ℂ) (GRe GIm : Space → Space) : ℝ :=
  kinetic GRe GIm / 2 - interaction α u / (2*(3+α))

def thresholdEnergy (α G : ℝ) : ℝ := (2+α)/(2*(3+α))*G

def directionalPressure (α : ℝ) (ω : Space) (u : Space → ℂ) : ℝ :=
  (((1+α)/2)*interaction α u + ((3-α)/2)*
    directionalPhysicalMoment α (standardRieszConstant α) ω (powerDensity α u)) / (3+α)

/-- Internal universal unweighted normalized Hartree-Sobolev proposition on the
full actual complex homogeneous Sobolev domain. Its existence and optimality are
not assumed silently and it is not classified as an external standard interface. -/
structure NormalizedHartreeSobolev (α G : ℝ) : Prop where
  threshold_pos : 0 < G
  bound : ∀ {u : Space → ℂ} {GRe GIm : Space → Space}, InDotH1 u GRe GIm →
    interaction α u ≤ G^(1-(3+α)) * (kinetic GRe GIm)^(3+α)

def thresholdScale (G : ℝ) (ω : Space) (GRe GIm : Space → Space) : ℝ :=
  1 + (G-kinetic GRe GIm)/directionalKinetic ω GRe GIm

theorem directionalPressure_mul {α : ℝ} (hα : 0 < α) (ω : Space) (u : Space → ℂ) :
    (3+α)*directionalPressure α ω u =
      ((1+α)/2)*interaction α u + ((3-α)/2)*
        directionalPhysicalMoment α (standardRieszConstant α) ω (powerDensity α u) := by
  unfold directionalPressure
  exact mul_div_cancel₀ _ (by linarith : 3+α ≠ 0)

theorem thresholdScale_gt_one {G : ℝ} {ω : Space} {GRe GIm : Space → Space}
    (hgap : kinetic GRe GIm < G) (hdir : 0 < directionalKinetic ω GRe GIm) :
    1 < thresholdScale G ω GRe GIm := by
  unfold thresholdScale
  have h := div_pos (sub_pos.mpr hgap) hdir
  linarith

/-- The actual stretched weak Sobolev function reaches kinetic energy G. -/
theorem thresholdScale_kinetic {u : Space → ℂ} {GRe GIm : Space → Space}
    (hu : InDotH1 u GRe GIm) {ω : Space} (hω : ‖ω‖ = 1) {G : ℝ}
    (hgap : kinetic GRe GIm < G) (hdir : 0 < directionalKinetic ω GRe GIm) :
    kinetic (stretchedGradient ω (Real.sqrt (thresholdScale G ω GRe GIm)) GRe)
      (stretchedGradient ω (Real.sqrt (thresholdScale G ω GRe GIm)) GIm) = G := by
  have hs : 0 < thresholdScale G ω GRe GIm := lt_trans zero_lt_one (thresholdScale_gt_one hgap hdir)
  rw [kinetic_stretch hu hω (Real.sqrt_pos.2 hs), Real.sq_sqrt hs.le]
  unfold perpendicularKinetic thresholdScale
  have hd := div_mul_cancel₀ (G-kinetic GRe GIm) hdir.ne'
  nlinarith

/-- The universal inequality is applied to the actual threshold-reaching
Sobolev function; the specialized interaction bound is produced here. -/
theorem thresholdScale_interaction_le_of_normalized_bound {α G : ℝ} (hHS : NormalizedHartreeSobolev α G)
    {u : Space → ℂ} {GRe GIm : Space → Space} (hu : InDotH1 u GRe GIm)
    {ω : Space} (hω : ‖ω‖ = 1) (hgap : kinetic GRe GIm < G)
    (hdir : 0 < directionalKinetic ω GRe GIm) :
    interaction α (stretchedFunction ω (Real.sqrt (thresholdScale G ω GRe GIm)) u) ≤ G := by
  have hs : 0 < thresholdScale G ω GRe GIm := lt_trans zero_lt_one (thresholdScale_gt_one hgap hdir)
  have h := hHS.bound (hu.stretch hω (Real.sqrt_pos.2 hs))
  rw [thresholdScale_kinetic hu hω hgap hdir, ← Real.rpow_add hHS.threshold_pos,
    sub_add_cancel, Real.rpow_one] at h
  exact h

/-- C10's genuine physical tangent transported to the actual complex stretched
function by the C11 density and pair change-of-variables identity. -/
theorem interaction_stretch_tangent {α : ℝ}
    (hHLS : OrdinaryHLS α (standardRieszConstant α)) {ω : Space} (hω : ‖ω‖ = 1)
    {u : Space → ℂ} (hu : MemLp u 6 volume) {s : ℝ} (hs : 1 ≤ s) :
    interaction α u + (s-1)*((3+α)*directionalPressure α ω u) ≤
      interaction α (stretchedFunction ω (Real.sqrt s) u) := by
  have hs0 : 0 < s := lt_of_lt_of_le zero_lt_one hs
  have ht := hartree_physicalStretch_tangent hHLS hω hu hs
  have he := (hartree_stretch_domain_and_energy hHLS hω (Real.sqrt_pos.2 hs0) hu).2.2.2
  rw [Real.sq_sqrt hs0.le] at he
  change interaction α (stretchedFunction ω (Real.sqrt s) u) = _ at he
  rw [directionalPressure_mul hHLS.order_pos, he]
  exact ht

#print axioms directionalPressure_mul
#print axioms thresholdScale_gt_one
#print axioms thresholdScale_kinetic
#print axioms thresholdScale_interaction_le_of_normalized_bound
#print axioms interaction_stretch_tangent
end HartreeF.DirectionalCoercivity
