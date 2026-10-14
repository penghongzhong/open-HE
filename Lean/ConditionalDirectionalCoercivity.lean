import DirectionalKineticPositive
import VariationalHartreeThreshold

/-!
Conditional variational consumers on actual complex homogeneous Sobolev data.
The full-function NormalizedHartreeSobolev premise remains explicit and is an
internal mathematical obligation. The special threshold stretch, its kinetic
and Hartree energies, and its directional tangent are produced natively.
This module alone does not close the combined Hartree-Sobolev bound or identify
its normalization with an optimal/ground-state threshold.
-/
noncomputable section
set_option autoImplicit false
open MeasureTheory
namespace HartreeF.DirectionalCoercivity
open SobolevStretch PhysicalStretch HeatRiesz ForcingDomain PressureDomain

def directionalDefect (α : ℝ) (ω : Space) (u : Space → ℂ) (GRe GIm : Space → Space) : ℝ :=
  directionalKinetic ω GRe GIm - directionalPressure α ω u

/-- Conditional DC on the true weak-function domain. No special stretched
energy inequality or target directional inequality is an input. -/
theorem directional_coercivity_of_normalized_bound {α G K : ℝ}
    (hHLS : OrdinaryHLS α (standardRieszConstant α)) (hSob : OrdinarySobolev K)
    (hHS : NormalizedHartreeSobolev α G) {u : Space → ℂ} {GRe GIm : Space → Space}
    (hu : InDotH1 u GRe GIm) (hnonzero : ¬ u =ᵐ[volume] 0)
    {ω : Space} (hω : ‖ω‖ = 1) (hgap : kinetic GRe GIm < G) :
    2*(thresholdEnergy α G-energy α u GRe GIm)*directionalKinetic ω GRe GIm /
      (G-kinetic GRe GIm) ≤ directionalDefect α ω u GRe GIm := by
  have hd := directionalKinetic_pos hSob hu hnonzero hω
  have hs := thresholdScale_gt_one hgap hd
  have hsharp := thresholdScale_interaction_le_of_normalized_bound hHS hu hω hgap hd
  have ht := interaction_stretch_tangent hHLS hω hu.function_L6 hs.le
  have ht' : interaction α u + ((G-kinetic GRe GIm)/directionalKinetic ω GRe GIm)*
      (3+α)*directionalPressure α ω u ≤
      interaction α (stretchedFunction ω (Real.sqrt (thresholdScale G ω GRe GIm)) u) := by
    simpa only [thresholdScale, add_sub_cancel_left, mul_assoc] using ht
  have hb := threshold_tangent_coercivity (by linarith [hHLS.order_pos] : 0 < 3+α)
    hgap hd hsharp ht'
  simpa only [thresholdEnergy, energy, directionalDefect,
    show 3+α-1 = 2+α by ring] using hb

theorem directional_coercivity_positive_of_normalized_bound {α G K : ℝ}
    (hHLS : OrdinaryHLS α (standardRieszConstant α)) (hSob : OrdinarySobolev K)
    (hHS : NormalizedHartreeSobolev α G) {u : Space → ℂ} {GRe GIm : Space → Space}
    (hu : InDotH1 u GRe GIm) (hnonzero : ¬ u =ᵐ[volume] 0)
    {ω : Space} (hω : ‖ω‖ = 1) (hgap : kinetic GRe GIm < G)
    (henergy : energy α u GRe GIm < thresholdEnergy α G) :
    0 < directionalDefect α ω u GRe GIm := by
  have hd := directionalKinetic_pos hSob hu hnonzero hω
  have h := directional_coercivity_of_normalized_bound hHLS hSob hHS hu hnonzero hω hgap
  have hp : 0 < 2*(thresholdEnergy α G-energy α u GRe GIm)*directionalKinetic ω GRe GIm /
      (G-kinetic GRe GIm) := by
    exact div_pos (mul_pos (mul_pos (by norm_num) (sub_pos.mpr henergy)) hd) (sub_pos.mpr hgap)
  exact lt_of_lt_of_le hp h

/-- Every physical density entering the conditional coercivity statement is
in its actual integral domain, including the anisotropic pair moment. -/
theorem directional_coercivity_domains {α : ℝ}
    (hHLS : OrdinaryHLS α (standardRieszConstant α)) {u : Space → ℂ} {GRe GIm : Space → Space}
    (hu : InDotH1 u GRe GIm) {ω : Space} (hω : ‖ω‖ = 1) :
    Integrable (fun x => ‖complexGradient GRe GIm x‖^2) volume ∧
    Integrable (fun x => ‖complexDirectionalGradient ω GRe GIm x‖^2) volume ∧
    Integrable (fun x => potential α (standardRieszConstant α) u x * powerDensity α u x) volume ∧
    Integrable (rieszPairDensity α (standardRieszConstant α) u) (volume.prod volume) ∧
    Integrable (directionalPhysicalPair α (standardRieszConstant α) ω (powerDensity α u))
      (volume.prod volume) := by
  obtain ⟨C,hC⟩ := interaction_density_domain_bound hHLS
  have hp := rieszPairDensity_integrable hHLS hu.function_L6
  exact ⟨kinetic_density_integrable hu.real_gradient_L2 hu.imag_gradient_L2,
    directionalKinetic_density_integrable hu.real_gradient_L2 hu.imag_gradient_L2 ω,
    (hC _ hu.function_L6).1, hp,
    directionalPhysicalPair_integrable hHLS.normalization_pos.le hω
      (fun x => Real.rpow_nonneg (norm_nonneg _) _) hp⟩

#print axioms directional_coercivity_of_normalized_bound
#print axioms directional_coercivity_positive_of_normalized_bound
#print axioms directional_coercivity_domains
end HartreeF.DirectionalCoercivity
