import DirectionalDensityFourier
import PhysicalStretchDomain
import Mathlib.Topology.Algebra.Module.Equiv.Prod

/-!
The genuine two-point Jacobian and physical energy transformation of the actual
stretched density. The original Riesz pair domain supplies the K_s domain by C5;
the product linear isomorphism then produces the stretched-density pair domain.
No target determinant, Jacobian, energy identity or weak-gradient rule is assumed.
-/
noncomputable section
set_option autoImplicit false
open MeasureTheory Set
open scoped RealInnerProductSpace
namespace HartreeF.DirectionalStretch
open PhysicalStretch PhysicalDensity

def pairStretch (ω : Space) (l : ℝ) : (Space × Space) →L[ℝ] (Space × Space) :=
  (stretch ω l).prodMap (stretch ω l)

@[simp] theorem pairStretch_apply (ω : Space) (l : ℝ) (q : Space × Space) :
    pairStretch ω l q = (stretch ω l q.1, stretch ω l q.2) := rfl

def pairStretchEquiv (ω : Space) (hω : ‖ω‖ = 1) (l : ℝ) (hl : l ≠ 0) :
    (Space × Space) ≃L[ℝ] (Space × Space) :=
  (stretchEquiv ω hω l hl).prodCongr (stretchEquiv ω hω l hl)

theorem pairStretch_det {ω : Space} (hω : ‖ω‖ = 1) (l : ℝ) :
    (pairStretch ω l).det = l^2 := by
  change LinearMap.det ((stretch ω l).toLinearMap.prodMap (stretch ω l).toLinearMap) = _
  rw [LinearMap.det_prodMap]
  change (stretch ω l).det * (stretch ω l).det = _
  rw [stretch_det hω]
  ring

theorem pairStretch_integral {ω : Space} (hω : ‖ω‖ = 1) {l : ℝ} (hl : 0 < l)
    (f : Space × Space → ℝ) :
    l^2 * (∫ q, f (pairStretch ω l q) ∂volume.prod volume) =
      ∫ q, f q ∂volume.prod volume := by
  have hi : InjOn (pairStretch ω l) univ := (pairStretchEquiv ω hω l hl.ne').injective.injOn
  have hs : pairStretch ω l '' univ = univ :=
    image_univ_of_surjective (pairStretchEquiv ω hω l hl.ne').surjective
  have h := integral_image_eq_integral_abs_det_fderiv_smul (volume.prod volume)
    MeasurableSet.univ (fun q _ => (pairStretch ω l).hasFDerivAt.hasFDerivWithinAt) hi f
  rw [hs, setIntegral_univ, setIntegral_univ] at h
  simpa only [pairStretch_det hω, abs_of_pos (sq_pos_of_pos hl), smul_eq_mul, integral_const_mul] using h.symm

theorem pairStretch_integrable_iff {ω : Space} (hω : ‖ω‖ = 1) {l : ℝ} (hl : 0 < l)
    (f : Space × Space → ℝ) :
    Integrable (fun q => f (pairStretch ω l q)) (volume.prod volume) ↔
      Integrable f (volume.prod volume) := by
  have hi : InjOn (pairStretch ω l) univ := (pairStretchEquiv ω hω l hl.ne').injective.injOn
  have hs : pairStretch ω l '' univ = univ :=
    image_univ_of_surjective (pairStretchEquiv ω hω l hl.ne').surjective
  have h := integrableOn_image_iff_integrableOn_abs_det_fderiv_smul (volume.prod volume)
    MeasurableSet.univ (fun q _ => (pairStretch ω l).hasFDerivAt.hasFDerivWithinAt) hi f
  rw [hs, integrableOn_univ, integrableOn_univ] at h
  simp only [pairStretch_det hω, abs_of_pos (sq_pos_of_pos hl), smul_eq_mul] at h
  have hm : Integrable (fun q => l^2 * f (pairStretch ω l q)) (volume.prod volume) ↔
      Integrable (fun q => f (pairStretch ω l q)) (volume.prod volume) :=
    integrable_smul_iff (sq_pos_of_pos hl).ne' _
  exact hm.symm.trans h.symm

theorem longitudinalSq_stretch {ω : Space} (hω : ‖ω‖ = 1) (l : ℝ) (z : Space) :
    longitudinalSq ω (stretch ω l z) = l^2 * longitudinalSq ω z := by
  unfold longitudinalSq
  rw [stretch_inner hω]
  ring

theorem transverseSq_stretch {ω : Space} (hω : ‖ω‖ = 1) (l : ℝ) (z : Space) :
    transverseSq ω (stretch ω l z) = transverseSq ω z := by
  change ‖stretch ω l z‖^2 - longitudinalSq ω (stretch ω l z) = transverseSq ω z
  rw [stretch_norm_sq hω, longitudinalSq_stretch hω]
  ring

theorem stretchDenominator_stretch {ω : Space} (hω : ‖ω‖ = 1) (l : ℝ) (z : Space) :
    stretchDenominator ω (l^2) (stretch ω l z) = l^2 * ‖z‖^2 := by
  unfold stretchDenominator
  rw [longitudinalSq_stretch hω, transverseSq_stretch hω]
  rw [← mul_add, directional_square_decomposition]

/-- The literal K_(l^2) pullback identity, including the zero separation. -/
theorem physicalStretchKernel_stretch (α c : ℝ) {ω : Space} (hω : ‖ω‖ = 1)
    {l : ℝ} (hl : 0 < l) (z : Space) :
    physicalStretchKernel α c ω (l^2) (stretch ω l z) =
      l^(1+α) * rieszKernel α c z := by
  unfold physicalStretchKernel
  rw [stretchDenominator_stretch hω, Real.mul_rpow (sq_nonneg l) (sq_nonneg ‖z‖),
    norm_sq_rpow_half, ← Real.rpow_natCast_mul hl.le]
  have he : (2:ℝ)*((α-3)/2) = α-3 := by ring
  norm_num only [Nat.cast_ofNat] at *
  rw [he]
  have hp : l^4 * l^(α-3) = l^(1+α) := by
    rw [show l^4 = l^(4:ℝ) by simp, ← Real.rpow_add hl]
    congr 1
    ring
  unfold rieszKernel
  calc
    _ = (l^4 * l^(α-3)) * c * ‖z‖^(α-3) := by ring
    _ = _ := by rw [hp]; ring

theorem density_amplitude_square (α : ℝ) {l : ℝ} (hl : 0 < l) :
    (l^((3+α)/2))^2 = l^2 * l^(1+α) := by
  rw [← Real.rpow_mul_natCast hl.le, show l^2 = l^(2:ℝ) by simp, ← Real.rpow_add hl]
  congr 1
  push_cast
  ring

theorem stretchedDensity_pair_pullback (α c : ℝ) {ω : Space} (hω : ‖ω‖ = 1)
    {l : ℝ} (hl : 0 < l) (b : Space → ℝ) (q : Space × Space) :
    pairDensity (fun z => rieszKernel α c (z.1-z.2)) (stretchedDensity α ω l b) q =
      l^2 * physicalStretchPair α c ω (l^2) b (pairStretch ω l q) := by
  unfold physicalStretchPair pairDensity stretchedDensity
  simp only [pairStretch_apply]
  rw [← map_sub (stretch ω l), physicalStretchKernel_stretch α c hω hl]
  calc
    _ = (l^((3+α)/2))^2 * rieszKernel α c (q.1-q.2) *
        b (stretch ω l q.2) * b (stretch ω l q.1) := by ring
    _ = _ := by rw [density_amplitude_square α hl]; ring

/-- Finite-domain actual physical energy transformation. No original density L1
assumption is needed here; only measurability, positivity and the finite base pair. -/
theorem stretchedDensity_riesz_domain_and_energy {α c : ℝ} (hα3 : α < 3)
    (hc : 0 ≤ c) {ω : Space} (hω : ‖ω‖ = 1) {l : ℝ} (hl : 0 < l)
    {b : Space → ℝ} (hb : AEStronglyMeasurable b volume) (hb0 : ∀ x, 0 ≤ b x)
    (hpair : Integrable (pairDensity (fun q => rieszKernel α c (q.1-q.2)) b) (volume.prod volume)) :
    Integrable (pairDensity (fun q => rieszKernel α c (q.1-q.2)) (stretchedDensity α ω l b))
      (volume.prod volume) ∧
    (∫ q, pairDensity (fun z => rieszKernel α c (z.1-z.2)) (stretchedDensity α ω l b) q
      ∂volume.prod volume) = physicalStretchEnergy α c ω b (l^2) := by
  have hp := physicalStretchPair_integrable hα3 hc hω (sq_pos_of_pos hl) hb hb0 hpair
  have ht := (pairStretch_integrable_iff hω hl (physicalStretchPair α c ω (l^2) b)).2 hp
  constructor
  · apply (ht.const_mul (l^2)).congr
    exact Filter.Eventually.of_forall (fun q => (stretchedDensity_pair_pullback α c hω hl b q).symm)
  · have he : (fun q => pairDensity (fun z => rieszKernel α c (z.1-z.2))
        (stretchedDensity α ω l b) q) =
        (fun q => l^2 * physicalStretchPair α c ω (l^2) b (pairStretch ω l q)) :=
      funext (stretchedDensity_pair_pullback α c hω hl b)
    rw [he, integral_const_mul, pairStretch_integral hω hl]
    rfl

#print axioms pairStretch_apply
#print axioms pairStretch_det
#print axioms pairStretch_integral
#print axioms pairStretch_integrable_iff
#print axioms longitudinalSq_stretch
#print axioms transverseSq_stretch
#print axioms stretchDenominator_stretch
#print axioms physicalStretchKernel_stretch
#print axioms density_amplitude_square
#print axioms stretchedDensity_pair_pullback
#print axioms stretchedDensity_riesz_domain_and_energy
end HartreeF.DirectionalStretch
