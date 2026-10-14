import SobolevKineticStretch
import DirectionalPairChange
import RieszPairIntegrability

/-!
Identification of the actual complex Sobolev dilation density with the C9
real density, followed by the produced physical pair change of variables.
This closes D(S_l u)=F_{|u|^(3+alpha)}(l^2), with actual L6, single-energy and
pair-energy domains supplied. The only analytic interface is ordinary HLS.
-/
noncomputable section
set_option autoImplicit false
open MeasureTheory Set
open scoped RealInnerProductSpace ENNReal
namespace HartreeF.SobolevStretch
open DirectionalStretch PhysicalStretch PhysicalDensity ForcingDomain PressureDomain

theorem stretchedFunction_powerDensity (α : ℝ) (ω : Space) {l : ℝ} (hl : 0 < l)
    (u : Space → ℂ) :
    powerDensity α (stretchedFunction ω l u) = stretchedDensity α ω l (powerDensity α u) := by
  funext x
  simp only [powerDensity, stretchedFunction, stretchedDensity, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg l)]
  rw [Real.mul_rpow (Real.sqrt_nonneg l) (norm_nonneg _), Real.sqrt_eq_rpow,
    ← Real.rpow_mul hl.le]
  congr 2
  ring

/-- Genuine Sobolev-function Hartree energy scaling. The transformed pair and
single convolution energy are both integrable before their integrals are identified. -/
theorem hartree_stretch_domain_and_energy {α c : ℝ} (hHLS : OrdinaryHLS α c)
    {ω : Space} (hω : ‖ω‖ = 1) {l : ℝ} (hl : 0 < l)
    {u : Space → ℂ} (hu : MemLp u 6 volume) :
    MemLp (stretchedFunction ω l u) 6 volume ∧
    Integrable (rieszPairDensity α c (stretchedFunction ω l u)) (volume.prod volume) ∧
    Integrable (fun x => potential α c (stretchedFunction ω l u) x *
      powerDensity α (stretchedFunction ω l u) x) volume ∧
    (∫ x, potential α c (stretchedFunction ω l u) x *
      powerDensity α (stretchedFunction ω l u) x) =
      physicalStretchEnergy α c ω (powerDensity α u) (l^2) := by
  have hs := stretchedFunction_memLp hω hl (by norm_num) (by norm_num) hu
  have hp := stretchedDensity_riesz_domain_and_energy hHLS.order_lt_three hHLS.normalization_pos.le
    hω hl (hu.aestronglyMeasurable.norm.aemeasurable.pow_const (3+α)).aestronglyMeasurable
    (fun x => Real.rpow_nonneg (norm_nonneg (u x)) (3+α)) (rieszPairDensity_integrable hHLS hu)
  have he := hartree_energy_pair_identity hHLS hs
  have hid : rieszPairDensity α c (stretchedFunction ω l u) =
      pairDensity (fun q => rieszKernel α c (q.1-q.2))
        (stretchedDensity α ω l (powerDensity α u)) := by
    unfold rieszPairDensity pairDensity
    rw [stretchedFunction_powerDensity α ω hl u]
  refine ⟨hs, rieszPairDensity_integrable hHLS hs, ?_, ?_⟩
  · obtain ⟨C, hC⟩ := interaction_density_domain_bound hHLS
    exact (hC _ hs).1
  · rw [← he, hid]
    exact hp.2

#print axioms stretchedFunction_powerDensity
#print axioms hartree_stretch_domain_and_energy
end HartreeF.SobolevStretch
