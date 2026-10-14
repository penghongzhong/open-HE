import Lemma_4_1_KelvinGlobalEnergy

/-! Actual longitudinal dilation and sharp anisotropic optimization. The only
new standard interfaces are isotropic sharp Sobolev and the weak chain rule
under an arbitrary invertible linear change of coordinates. The anisotropic
inequality itself is proved, not used as an interface. -/
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

def dilation (a : ℝ) : Space →L[ℝ] Space :=
  (a • ContinuousLinearMap.id ℝ ℝ).prodMap (ContinuousLinearMap.id ℝ Plane)

theorem dilation_apply (a : ℝ) (z : Space) : dilation a z = (a*z.1,z.2) := by
  rfl

theorem dilation_inverse {a : ℝ} (ha : a ≠ 0) (z : Space) :
    dilation a⁻¹ (dilation a z) = z := by
  simp [dilation_apply,ha]

def dilationEquiv (a : ℝ) (ha : a ≠ 0) : Space ≃L[ℝ] Space :=
  { dilation a with
    invFun := dilation a⁻¹
    left_inv := dilation_inverse ha
    right_inv := fun z => by simpa using dilation_inverse (inv_ne_zero ha) z
    continuous_invFun := (dilation a⁻¹).continuous }

theorem dilation_det (a : ℝ) : (dilation a).det = a := by
  change LinearMap.det ((a • LinearMap.id : ℝ →ₗ[ℝ] ℝ).prodMap
    (LinearMap.id : Plane →ₗ[ℝ] Plane)) = a
  rw [LinearMap.det_prodMap]
  simp

/-- Native Mathlib change of variables, with the actual determinant a. -/
theorem dilation_integral {a : ℝ} (ha : 0 < a) (F : Space → ℝ) :
    a * (∫ z, F (dilation a z)) = ∫ z, F z := by
  have hi : InjOn (dilation a) univ := (dilationEquiv a ha.ne').injective.injOn
  have hs : dilation a '' univ = univ :=
    image_univ_of_surjective (dilationEquiv a ha.ne').surjective
  have h := integral_image_eq_integral_abs_det_fderiv_smul (volume : Measure Space)
    MeasurableSet.univ (fun z _ => (dilation a).hasFDerivAt.hasFDerivWithinAt) hi F
  rw [hs,setIntegral_univ,setIntegral_univ] at h
  simpa only [dilation_det,abs_of_pos ha,smul_eq_mul,integral_const_mul] using h.symm

/-- Universal standard weak chain rule. No special scaling or energy bound
is an input. The output covector is exactly D(Lz) composed with L. -/
def LinearSobolevPullback : Prop :=
  ∀ (L : Space ≃L[ℝ] Space) (u : Space → ℝ) (D : Space → Space →L[ℝ] ℝ),
    InH1 u D → InH1 (fun z => u (L z))
      (fun z => (D (L z)).comp L.toContinuousLinearMap)

/-- Isotropic sharp Sobolev, written with the actual sum of coordinate-square
energies; this is equation (2), not equation (12) or a weighted estimate. -/
def SharpSobolev (G : ℝ) : Prop :=
  ∀ (u : Space → ℝ) (D : Space → Space →L[ℝ] ℝ), InH1 u D →
    Integrable (fun z => u z ^ 6) ∧
    (∫ z, u z ^ 6) * G^2 ≤
      ((∫ z, transverseDensity D z) + ∫ z, longitudinalDensity D z)^3

def scaledDerivative (a : ℝ) (D : Space → Space →L[ℝ] ℝ) (z : Space) :
    Space →L[ℝ] ℝ := (D (dilation a z)).comp (dilation a)

theorem scaled_transverse (a : ℝ) (D : Space → Space →L[ℝ] ℝ) (z : Space) :
    transverseDensity (scaledDerivative a D) z = transverseDensity D (dilation a z) := by
  simp [transverseDensity,transverseGradient,scaledDerivative,dilation_apply]

theorem scaled_longitudinal (a : ℝ) (D : Space → Space →L[ℝ] ℝ) (z : Space) :
    longitudinalDensity (scaledDerivative a D) z = a^2 * longitudinalDensity D (dilation a z) := by
  unfold longitudinalDensity scaledDerivative
  simp only [ContinuousLinearMap.comp_apply,dilation_apply,mul_one]
  have he : (a,(0 : Plane)) = a • ((1,0) : Space) := by simp
  rw [he,map_smul,smul_eq_mul,mul_pow]

theorem scaled_transverse_integral {a : ℝ} (ha : 0 < a)
    (D : Space → Space →L[ℝ] ℝ) :
    a * (∫ z, transverseDensity (scaledDerivative a D) z) =
      ∫ z, transverseDensity D z := by
  simp_rw [scaled_transverse]
  exact dilation_integral ha _

theorem scaled_longitudinal_integral {a : ℝ} (ha : 0 < a)
    (D : Space → Space →L[ℝ] ℝ) :
    a * (∫ z, longitudinalDensity (scaledDerivative a D) z) =
      a^2 * ∫ z, longitudinalDensity D z := by
  simp_rw [scaled_longitudinal]
  rw [integral_const_mul]
  have h := dilation_integral ha (longitudinalDensity D)
  have hm := congrArg (fun x : ℝ => a^2*x) h
  nlinarith [hm]

/-- The one-parameter inequality is derived from actual scaled H1 functions. -/
theorem anisotropic_parameter {G : ℝ} (sharp : SharpSobolev G)
    (pullback : LinearSobolevPullback) {u : Space → ℝ} {D : Space → Space →L[ℝ] ℝ}
    (hu : InH1 u D) {q : ℝ} (hq : 0 < q) :
    (∫ z, u z^6) * G^2 * q ≤
      ((∫ z, transverseDensity D z) + q * ∫ z, longitudinalDensity D z)^3 := by
  let a := Real.sqrt q
  have ha : 0 < a := Real.sqrt_pos.mpr hq
  have ha2 : a^2=q := Real.sq_sqrt hq.le
  have hscaled : InH1 (fun z => u (dilation a z)) (scaledDerivative a D) :=
    pullback (dilationEquiv a ha.ne') u D hu
  have hs := (sharp _ _ hscaled).2
  have hN := dilation_integral ha (fun z => u z^6)
  have hA := scaled_transverse_integral ha D
  have hB := scaled_longitudinal_integral ha D
  have hmul := mul_le_mul_of_nonneg_left hs (pow_nonneg ha.le 3)
  have heL : a^3 * ((∫ z, u (dilation a z)^6) * G^2) =
      (∫ z, u z^6) * G^2 * q := by rw [← ha2,← hN]; ring
  have heR : a^3 * ((∫ z, transverseDensity (scaledDerivative a D) z) +
      ∫ z, longitudinalDensity (scaledDerivative a D) z)^3 =
      ((∫ z, transverseDensity D z) + q * ∫ z, longitudinalDensity D z)^3 := by
    rw [← mul_pow,mul_add,hA,hB,ha2]
  rwa [heL,heR] at hmul


theorem optimize_anisotropic_positive {N G A B : ℝ} (hA : 0 < A) (hB : 0 < B)
    (h : ∀ q : ℝ, 0 < q → N*G^2*q ≤ (A+q*B)^3) :
    4*N*G^2 ≤ 27*A^2*B := by
  have hq : 0 < A/(2*B) := div_pos hA (by positivity)
  have he : A + A/(2*B)*B = 3/2*A := by field_simp; ring
  have hi := h _ hq
  rw [he] at hi
  have hm := mul_le_mul_of_nonneg_right hi (show 0 ≤ 2*B by positivity)
  have hleft : N*G^2*(A/(2*B))*(2*B) = N*G^2*A := by field_simp
  rw [hleft] at hm
  apply (mul_le_mul_iff_right₀ hA).mp
  nlinarith [hm]

/-- Includes zero directional energies by an actual one-sided limit. -/
theorem optimize_anisotropic {N G A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (h : ∀ q : ℝ, 0 < q → N*G^2*q ≤ (A+q*B)^3) :
    4*N*G^2 ≤ 27*A^2*B := by
  have heps : ∀ ε : ℝ, 0 < ε → 4*N*G^2 ≤ 27*(A+ε)^2*(B+ε) := by
    intro ε hε
    apply optimize_anisotropic_positive (by linarith : 0 < A+ε) (by linarith : 0 < B+ε)
    intro q hq
    apply (h q hq).trans
    apply pow_le_pow_left₀ (by positivity)
    nlinarith
  have ht : Tendsto (fun ε : ℝ => 27*(A+ε)^2*(B+ε)) (𝓝[>] (0 : ℝ)) (𝓝 (27*A^2*B)) := by
    have hc : Continuous (fun ε : ℝ => 27*(A+ε)^2*(B+ε)) := by fun_prop
    simpa only [add_zero] using (hc.tendsto (0 : ℝ)).mono_left (show (𝓝[>] (0 : ℝ)) ≤ 𝓝 0 from nhdsWithin_le_nhds)
  apply ge_of_tendsto ht
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact heps ε hε

/-- Equation (12), for the actual H1 function and its genuine weak derivative. -/
theorem anisotropic_sobolev {G : ℝ} (hG : 0 < G) (sharp : SharpSobolev G)
    (pullback : LinearSobolevPullback) {u : Space → ℝ} {D : Space → Space →L[ℝ] ℝ}
    (hu : InH1 u D) :
    (∫ z, u z^6) ≤ 27/(4*G^2) * (∫ z, transverseDensity D z)^2 *
      ∫ z, longitudinalDensity D z := by
  have hA : 0 ≤ ∫ z, transverseDensity D z :=
    integral_nonneg (fun z => by unfold transverseDensity s; positivity)
  have hB : 0 ≤ ∫ z, longitudinalDensity D z := integral_nonneg (fun z => sq_nonneg _)
  have hopt := optimize_anisotropic hA hB (fun q hq => anisotropic_parameter sharp pullback hu hq)
  calc
    (∫ z, u z^6) ≤
        (27*(∫ z, transverseDensity D z)^2*(∫ z, longitudinalDensity D z))/(4*G^2) := by
      apply (le_div_iff₀ (by positivity : 0 < 4*G^2)).mpr
      nlinarith [hopt]
    _ = _ := by ring


/-- The paper-specific exterior estimate, obtained from the constructed
Kelvin extension and the proved anisotropic inequality. -/
theorem exterior_anisotropic {G R : ℝ} (hG : 0 < G) (hR : 0 < R)
    (sharp : SharpSobolev G) (pullback : LinearSobolevPullback) (glue : SmoothInterfaceGluing)
    {f : Space → ℝ} (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    (∫ z in exteriorCylinder R, f z^6) ≤
      54/G^2 * (∫ z, transverseDensity (fderiv ℝ f) z)^2 *
        ∫ z in exteriorCylinder R, longitudinalDensity (fderiv ℝ f) z := by
  have hH := extension_inH1 glue hR hf hc
  have hsharp := anisotropic_sobolev hG sharp pullback hH
  have hE := global_transverse_energy glue hR hf hc
  have hL := global_longitudinal_bound glue hR hf hc
  have hmem := (sharp _ _ hH).1
  have hretain : (∫ z in exteriorCylinder R, f z^6) ≤ ∫ z, (extension R f z)^6 := by
    have heq : (∫ z in exteriorCylinder R, f z^6) =
        ∫ z in exteriorCylinder R, (extension R f z)^6 := by
      apply setIntegral_congr_fun (MeasurableSet.univ.prod (exteriorDisk_measurable R))
      intro z hz
      dsimp only
      rw [extension_exterior f hz.2.le]
    rw [heq]
    exact setIntegral_le_integral hmem (Eventually.of_forall (fun z => by positivity))
  have hA : 0 ≤ ∫ z in exteriorCylinder R, transverseDensity (fderiv ℝ f) z :=
    integral_nonneg (fun z => by unfold transverseDensity s; positivity)
  have hB : 0 ≤ ∫ z in exteriorCylinder R, longitudinalDensity (fderiv ℝ f) z :=
    integral_nonneg (fun z => sq_nonneg _)
  have hAall : (∫ z in exteriorCylinder R, transverseDensity (fderiv ℝ f) z) ≤
      ∫ z, transverseDensity (fderiv ℝ f) z := by
    apply setIntegral_le_integral (transverseDensity_integrable (compact_derivative_memLp hf hc))
    exact Eventually.of_forall (fun z => by unfold transverseDensity s; positivity)
  rw [hE] at hsharp
  have hbound := mul_le_mul_of_nonneg_left hL
    (show 0 ≤ 27/(4*G^2)*(2*(∫ z in exteriorCylinder R, transverseDensity (fderiv ℝ f) z))^2 by positivity)
  have hconstant : 27/(4*G^2)*(2*(∫ z in exteriorCylinder R, transverseDensity (fderiv ℝ f) z))^2 *
      (2*(∫ z in exteriorCylinder R, longitudinalDensity (fderiv ℝ f) z)) =
      54/G^2*(∫ z in exteriorCylinder R, transverseDensity (fderiv ℝ f) z)^2 *
      (∫ z in exteriorCylinder R, longitudinalDensity (fderiv ℝ f) z) := by ring
  rw [hconstant] at hbound
  apply (hretain.trans (hsharp.trans hbound)).trans
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hA hAall 2) (by positivity)) hB



#print axioms dilation_apply
#print axioms dilation_inverse
#print axioms dilation_det
#print axioms dilation_integral
#print axioms scaled_transverse
#print axioms scaled_longitudinal
#print axioms scaled_transverse_integral
#print axioms scaled_longitudinal_integral
#print axioms anisotropic_parameter
#print axioms optimize_anisotropic_positive
#print axioms optimize_anisotropic
#print axioms anisotropic_sobolev
#print axioms exterior_anisotropic
end BWork.Kelvin
