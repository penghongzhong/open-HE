import PhysicalStretchConvexity
import PhysicalStretchDifferentiation

/-!
The actual physical directional tangent is obtained from the newly produced
physical convexity and the C5 HasDerivAt theorem for the actual double integral.
No spectral derivative or general non-L1 Fourier domain is assumed. The Hartree
specialization uses only the explicit ordinary HLS at the standard normalization.
-/
noncomputable section
set_option autoImplicit false
open MeasureTheory Set
namespace HartreeF.PhysicalSpectral
open PhysicalStretch PhysicalDensity HeatRiesz ForcingDomain PressureDomain

theorem physicalStretchEnergy_one_eq_standardRiesz (α : ℝ) (ω : Space) (b : Space → ℝ) :
    physicalStretchEnergy α (standardRieszConstant α) ω b 1 =
      ∫ q, standardRieszPair α b q ∂volume.prod volume := by
  unfold physicalStretchEnergy standardRieszPair
  simp only [physicalStretchPair_one]

/-- The exact physical finite-energy tangent for every s>=1. -/
theorem physicalStretch_tangent {α : ℝ} (hα : 0 < α) (hα3 : α < 3)
    {ω : Space} (hω : ‖ω‖ = 1) {b : Space → ℝ} (hb : AEStronglyMeasurable b volume)
    (hb0 : ∀ x, 0 ≤ b x) (hpair : Integrable (standardRieszPair α b) (volume.prod volume))
    {s : ℝ} (hs : 1 ≤ s) :
    (∫ q, standardRieszPair α b q ∂volume.prod volume) +
      (s-1) * (((1+α)/2) * (∫ q, standardRieszPair α b q ∂volume.prod volume) +
        ((3-α)/2) * directionalPhysicalMoment α (standardRieszConstant α) ω b) ≤
      physicalStretchEnergy α (standardRieszConstant α) ω b s := by
  rcases eq_or_lt_of_le hs with hs | hs
  · subst s
    rw [physicalStretchEnergy_one_eq_standardRiesz]
    simp only [sub_self, zero_mul, add_zero, le_refl]
  have hc := physicalStretch_convex hα hα3 hω hb hb0 hpair
  have hd := physicalStretchEnergy_hasDerivAt_one hα3
    (standardRieszConstant_pos hα hα3).le hω hb hb0 hpair
  have h := hc.le_slope_of_hasDerivAt
    (by norm_num : (1:ℝ) ∈ Ioi 0) (show s ∈ Ioi 0 by change 0<s; linarith) hs hd
  rw [slope_def_field, physicalStretchEnergy_one_eq_standardRiesz] at h
  have hm := (le_div_iff₀ (sub_pos.mpr hs)).mp h
  change (((1+α)/2) * (∫ q, standardRieszPair α b q ∂volume.prod volume) +
      ((3-α)/2) * directionalPhysicalMoment α (standardRieszConstant α) ω b) * (s-1) ≤ _ at hm
  nlinarith

/-- General L6 Hartree density: convexity is obtained through its actual L1 cutoffs. -/
theorem hartree_physicalStretch_convex {α : ℝ}
    (hHLS : OrdinaryHLS α (standardRieszConstant α)) {ω : Space} (hω : ‖ω‖ = 1)
    {f : Space → ℂ} (hf : MemLp f 6 volume) :
    ConvexOn ℝ (Ioi 0)
      (physicalStretchEnergy α (standardRieszConstant α) ω (powerDensity α f)) := by
  apply physicalStretch_convex hHLS.order_pos hHLS.order_lt_three hω
  · exact (hf.aestronglyMeasurable.norm.aemeasurable.pow_const (3+α)).aestronglyMeasurable
  · intro x
    exact Real.rpow_nonneg (norm_nonneg _) _
  · exact rieszPairDensity_integrable hHLS hf

/-- Actual Hartree physical tangent, with the pressure coefficients from the genuine
C5 derivative. No mass, L1 density, Fourier-transform, or Sobolev-gradient premise is added. -/
theorem hartree_physicalStretch_tangent {α : ℝ}
    (hHLS : OrdinaryHLS α (standardRieszConstant α)) {ω : Space} (hω : ‖ω‖ = 1)
    {f : Space → ℂ} (hf : MemLp f 6 volume) {s : ℝ} (hs : 1 ≤ s) :
    (∫ x, potential α (standardRieszConstant α) f x * powerDensity α f x) +
      (s-1) * (((1+α)/2) *
        (∫ x, potential α (standardRieszConstant α) f x * powerDensity α f x) +
        ((3-α)/2) * directionalPhysicalMoment α (standardRieszConstant α) ω (powerDensity α f)) ≤
      physicalStretchEnergy α (standardRieszConstant α) ω (powerDensity α f) s := by
  have hb : AEStronglyMeasurable (powerDensity α f) volume :=
    (hf.aestronglyMeasurable.norm.aemeasurable.pow_const (3+α)).aestronglyMeasurable
  have hb0 : ∀ x, 0 ≤ powerDensity α f x := fun x => Real.rpow_nonneg (norm_nonneg _) _
  have hp : Integrable (standardRieszPair α (powerDensity α f)) (volume.prod volume) :=
    rieszPairDensity_integrable hHLS hf
  have h := physicalStretch_tangent hHLS.order_pos hHLS.order_lt_three hω hb hb0 hp hs
  have he : (∫ q, standardRieszPair α (powerDensity α f) q ∂volume.prod volume) =
      ∫ x, potential α (standardRieszConstant α) f x * powerDensity α f x :=
    hartree_energy_pair_identity hHLS hf
  rwa [he] at h

#print axioms physicalStretchEnergy_one_eq_standardRiesz
#print axioms physicalStretch_tangent
#print axioms hartree_physicalStretch_convex
#print axioms hartree_physicalStretch_tangent
end HartreeF.PhysicalSpectral
