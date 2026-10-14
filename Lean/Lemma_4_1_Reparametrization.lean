import Lemma_4_1_RegularizedClock

/-! Actual three-dimensional longitudinal change of coordinates and chain rule. -/
noncomputable section
set_option autoImplicit false
open MeasureTheory Set Filter
open scoped ContDiff Topology
namespace BWork.Kelvin

local instance : (volume : Measure Plane).IsAddHaarMeasure := by
  change ((volume : Measure ℝ).prod (volume : Measure ℝ)).IsAddHaarMeasure
  infer_instance
local instance : (volume : Measure Space).IsAddHaarMeasure := by
  change ((volume : Measure ℝ).prod (volume : Measure Plane)).IsAddHaarMeasure
  infer_instance

def clockLift (τ : ℝ ≃ₜ ℝ) : Space ≃ₜ Space := τ.prodCongr (Homeomorph.refl Plane)

theorem clockLift_apply (τ : ℝ ≃ₜ ℝ) (z : Space) : clockLift τ z = (τ z.1,z.2) := rfl

theorem clockLift_hasFDerivAt {τ : ℝ ≃ₜ ℝ} {z : Space} {q : ℝ}
    (hτ : HasDerivAt τ q z.1) : HasFDerivAt (clockLift τ) (dilation q) z := by
  have hd := (hτ.hasFDerivAt.comp z hasFDerivAt_fst).prodMk (hasFDerivAt_snd (𝕜 := ℝ))
  convert! hd using 1
  apply ContinuousLinearMap.ext
  intro e
  change (q*e.1,e.2) = (e.1*q,e.2)
  simp only [mul_comm]

theorem clockLift_contDiff {τ : ℝ ≃ₜ ℝ} (hτ : ContDiff ℝ ∞ τ) :
    ContDiff ℝ ∞ (clockLift τ) := (hτ.comp contDiff_fst).prodMk contDiff_snd

theorem clockLift_integral (τ : ℝ ≃ₜ ℝ) (q : ℝ → ℝ)
    (hq : ∀ s,0 < q s) (hτ : ∀ s,HasDerivAt τ (q s) s) (F : Space → ℝ) :
    (∫ z,F z) = ∫ z,q z.1*F (clockLift τ z) := by
  have hd (z : Space) (_ : z ∈ univ) := (clockLift_hasFDerivAt (hτ z.1)).hasFDerivWithinAt (s := univ)
  have hi : InjOn (clockLift τ) univ := (clockLift τ).injective.injOn
  have him : clockLift τ '' univ = univ := image_univ_of_surjective (clockLift τ).surjective
  have h := integral_image_eq_integral_abs_det_fderiv_smul (volume : Measure Space) MeasurableSet.univ hd hi F
  rw [him,setIntegral_univ,setIntegral_univ] at h
  simpa only [dilation_det,abs_of_pos (hq _),smul_eq_mul] using h

def reparametrized (τ : ℝ ≃ₜ ℝ) (a : ℝ → ℝ) (g : Space → ℝ) (z : Space) : ℝ :=
  a (τ.symm z.1)*g (τ.symm z.1,z.2)

theorem reparametrized_on_image (τ : ℝ ≃ₜ ℝ) (a : ℝ → ℝ) (g : Space → ℝ) (z : Space) :
    reparametrized τ a g (clockLift τ z) = a z.1*g z := by
  simp [reparametrized,clockLift_apply]

theorem reparametrized_contDiff {τ : ℝ ≃ₜ ℝ} (hτ : ContDiff ℝ ∞ τ.symm)
    {a : ℝ → ℝ} (ha : ContDiff ℝ ∞ a) {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (reparametrized τ a g) :=
  (ha.comp (hτ.comp contDiff_fst)).mul (hg.comp ((hτ.comp contDiff_fst).prodMk contDiff_snd))

theorem reparametrized_compact (τ : ℝ ≃ₜ ℝ) (a : ℝ → ℝ)
    {g : Space → ℝ} (hc : HasCompactSupport g) : HasCompactSupport (reparametrized τ a g) := by
  have hm : HasCompactSupport (fun z : Space => a z.1*g z) := hc.mul_left
  exact hm.comp_homeomorph (clockLift τ).symm

def amplitudeDerivative (a a' g : ℝ) (D : Space →L[ℝ] ℝ) : Space →L[ℝ] ℝ :=
  a • D + (a'*g) • ContinuousLinearMap.fst ℝ ℝ Plane

theorem amplitude_hasFDerivAt {a : ℝ → ℝ} {a' : ℝ} {g : Space → ℝ} {z : Space}
    (ha : HasDerivAt a a' z.1) (hg : DifferentiableAt ℝ g z) :
    HasFDerivAt (fun x : Space => a x.1*g x)
      (amplitudeDerivative (a z.1) a' (g z) (fderiv ℝ g z)) z := by
  have hd := (ha.hasFDerivAt.comp z hasFDerivAt_fst).mul hg.hasFDerivAt
  convert! hd using 1
  apply ContinuousLinearMap.ext
  intro e
  change a z.1*(fderiv ℝ g z) e+(a'*g z)*e.1 =
    a z.1*(fderiv ℝ g z) e+g z*(e.1*a')
  ring

theorem reparametrized_hasFDerivAt_image {τ : ℝ ≃ₜ ℝ} {q : ℝ} {z : Space}
    (hq : q ≠ 0) (hτ : HasDerivAt τ q z.1)
    {a : ℝ → ℝ} {a' : ℝ} (ha : HasDerivAt a a' z.1)
    {g : Space → ℝ} (hg : DifferentiableAt ℝ g z) :
    HasFDerivAt (reparametrized τ a g)
      ((amplitudeDerivative (a z.1) a' (g z) (fderiv ℝ g z)).comp (dilation q⁻¹))
      (clockLift τ z) := by
  have hi : HasDerivAt τ.symm q⁻¹ (τ z.1) := by
    apply HasDerivAt.of_local_left_inverse τ.symm.continuous.continuousAt
      (by simpa only [τ.symm_apply_apply] using hτ) hq
    exact Eventually.of_forall τ.apply_symm_apply
  have hi3 := clockLift_hasFDerivAt (z := clockLift τ z) hi
  have ha3 := amplitude_hasFDerivAt ha hg
  have ha3' : HasFDerivAt (fun x : Space => a x.1*g x)
      (amplitudeDerivative (a z.1) a' (g z) (fderiv ℝ g z)) (clockLift τ.symm (clockLift τ z)) := by
    simpa only [clockLift_apply,Homeomorph.symm_apply_apply] using ha3
  exact ha3'.comp (clockLift τ z) hi3

#print axioms clockLift_apply
#print axioms clockLift_hasFDerivAt
#print axioms clockLift_contDiff
#print axioms clockLift_integral
#print axioms reparametrized_on_image
#print axioms reparametrized_contDiff
#print axioms reparametrized_compact
#print axioms amplitude_hasFDerivAt
#print axioms reparametrized_hasFDerivAt_image
end BWork.Kelvin
