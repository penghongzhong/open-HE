import WeakDirectionalStretch

/-!
The actual complex weak-gradient kinetic integral and directional kinetic
integral. Their output domains and anisotropic scaling are consequences of
the weak-gradient producer and the C9 Jacobian, never input identities.
-/
noncomputable section
set_option autoImplicit false
open MeasureTheory Set
open scoped RealInnerProductSpace ENNReal
namespace HartreeF.SobolevStretch
open DirectionalStretch PhysicalStretch

def complexGradient (GRe GIm : Space → Space) (x : Space) : EuclideanSpace ℂ (Fin 3) :=
  WithLp.toLp 2 (fun i => (GRe x i : ℂ) + Complex.I * (GIm x i : ℂ))

def complexDirectionalGradient (ω : Space) (GRe GIm : Space → Space) (x : Space) : ℂ :=
  (⟪ω,GRe x⟫ : ℂ) + Complex.I * (⟪ω,GIm x⟫ : ℂ)

def kinetic (GRe GIm : Space → Space) : ℝ := ∫ x, ‖complexGradient GRe GIm x‖^2

def directionalKinetic (ω : Space) (GRe GIm : Space → Space) : ℝ :=
  ∫ x, ‖complexDirectionalGradient ω GRe GIm x‖^2

def perpendicularKinetic (ω : Space) (GRe GIm : Space → Space) : ℝ :=
  kinetic GRe GIm - directionalKinetic ω GRe GIm

theorem complexGradient_norm_sq (GRe GIm : Space → Space) (x : Space) :
    ‖complexGradient GRe GIm x‖^2 = ‖GRe x‖^2 + ‖GIm x‖^2 := by
  simp only [EuclideanSpace.norm_sq_eq, complexGradient]
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im,
    Complex.I_re, Complex.I_im, zero_mul, one_mul, sub_zero,
    add_zero, zero_add, Real.norm_eq_abs, sq_abs]
  rw [Finset.sum_add_distrib]
  simp only [pow_two]

theorem complexDirectionalGradient_norm_sq (ω : Space) (GRe GIm : Space → Space) (x : Space) :
    ‖complexDirectionalGradient ω GRe GIm x‖^2 = ⟪ω,GRe x⟫^2 + ⟪ω,GIm x⟫^2 := by
  rw [complexDirectionalGradient, Complex.sq_norm]
  simp [Complex.normSq_apply, pow_two]

theorem directional_sq_integrable {V : Space → Space} (hV : MemLp V 2 volume) (ω : Space) :
    Integrable (fun x => ⟪ω,V x⟫^2) volume := by
  have h := (hV.continuousLinearMap_comp (innerSL ℝ ω)).integrable_norm_pow
    (by decide : (2:ℕ) ≠ 0)
  change Integrable (fun x => ‖(⟪ω,V x⟫ : ℝ)‖^2) volume at h
  simpa only [Real.norm_eq_abs, sq_abs] using h

theorem kinetic_density_integrable {GRe GIm : Space → Space}
    (hR : MemLp GRe 2 volume) (hI : MemLp GIm 2 volume) :
    Integrable (fun x => ‖complexGradient GRe GIm x‖^2) volume := by
  apply ((hR.integrable_norm_pow (by decide : (2:ℕ) ≠ 0)).add
    (hI.integrable_norm_pow (by decide : (2:ℕ) ≠ 0))).congr
  exact Filter.Eventually.of_forall (fun x => (complexGradient_norm_sq GRe GIm x).symm)

theorem directionalKinetic_density_integrable {GRe GIm : Space → Space}
    (hR : MemLp GRe 2 volume) (hI : MemLp GIm 2 volume) (ω : Space) :
    Integrable (fun x => ‖complexDirectionalGradient ω GRe GIm x‖^2) volume := by
  apply ((directional_sq_integrable hR ω).add (directional_sq_integrable hI ω)).congr
  exact Filter.Eventually.of_forall
    (fun x => (complexDirectionalGradient_norm_sq ω GRe GIm x).symm)

theorem kinetic_eq_sum {GRe GIm : Space → Space}
    (hR : MemLp GRe 2 volume) (hI : MemLp GIm 2 volume) :
    kinetic GRe GIm = (∫ x, ‖GRe x‖^2) + ∫ x, ‖GIm x‖^2 := by
  simp only [kinetic, complexGradient_norm_sq]
  exact integral_add (hR.integrable_norm_pow (by decide : (2:ℕ) ≠ 0))
    (hI.integrable_norm_pow (by decide : (2:ℕ) ≠ 0))

theorem directionalKinetic_eq_sum {GRe GIm : Space → Space}
    (hR : MemLp GRe 2 volume) (hI : MemLp GIm 2 volume) (ω : Space) :
    directionalKinetic ω GRe GIm = (∫ x, ⟪ω,GRe x⟫^2) + ∫ x, ⟪ω,GIm x⟫^2 := by
  simp only [directionalKinetic, complexDirectionalGradient_norm_sq]
  exact integral_add (directional_sq_integrable hR ω) (directional_sq_integrable hI ω)

theorem stretchedGradient_norm_sq {ω : Space} (hω : ‖ω‖ = 1) {l : ℝ} (hl : 0 < l)
    (V : Space → Space) (x : Space) :
    ‖stretchedGradient ω l V x‖^2 =
      l * (‖V (stretch ω l x)‖^2 + (l^2-1)*⟪ω,V (stretch ω l x)⟫^2) := by
  rw [stretchedGradient, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
    Real.sq_sqrt hl.le, stretch_norm_sq hω]
  unfold transverseSq longitudinalSq
  ring

theorem real_gradient_energy_stretch {ω : Space} (hω : ‖ω‖ = 1) {l : ℝ} (hl : 0 < l)
    {V : Space → Space} (hV : MemLp V 2 volume) :
    (∫ x, ‖stretchedGradient ω l V x‖^2) =
      (∫ x, ‖V x‖^2) + (l^2-1)*(∫ x, ⟪ω,V x⟫^2) := by
  simp only [stretchedGradient_norm_sq hω hl]
  rw [integral_const_mul]
  have hj := stretch_integral hω hl (fun y => ‖V y‖^2 + (l^2-1)*⟪ω,V y⟫^2)
  rw [smul_eq_mul] at hj
  rw [hj, integral_add (hV.integrable_norm_pow (by decide : (2:ℕ) ≠ 0))
    ((directional_sq_integrable hV ω).const_mul _), integral_const_mul]

/-- A(S_l u)=A_perp(u)+l^2 A_omega(u), for the actual produced weak gradient. -/
theorem kinetic_stretch {u : Space → ℂ} {GRe GIm : Space → Space}
    (h : InDotH1 u GRe GIm) {ω : Space} (hω : ‖ω‖ = 1) {l : ℝ} (hl : 0 < l) :
    kinetic (stretchedGradient ω l GRe) (stretchedGradient ω l GIm) =
      perpendicularKinetic ω GRe GIm + l^2 * directionalKinetic ω GRe GIm := by
  rw [kinetic_eq_sum (stretchedGradient_memLp hω hl h.real_gradient_L2)
    (stretchedGradient_memLp hω hl h.imag_gradient_L2),
    real_gradient_energy_stretch hω hl h.real_gradient_L2,
    real_gradient_energy_stretch hω hl h.imag_gradient_L2]
  unfold perpendicularKinetic
  rw [kinetic_eq_sum h.real_gradient_L2 h.imag_gradient_L2,
    directionalKinetic_eq_sum h.real_gradient_L2 h.imag_gradient_L2]
  ring

theorem sixth_mass_stretch {ω : Space} (hω : ‖ω‖ = 1) {l : ℝ} (hl : 0 < l)
    (u : Space → ℂ) :
    (∫ x, ‖stretchedFunction ω l u x‖^6) = l^2 * (∫ x, ‖u x‖^6) := by
  have hp (x : Space) : ‖stretchedFunction ω l u x‖^6 = l^3 * ‖u (stretch ω l x)‖^6 := by
    rw [stretchedFunction, norm_smul, mul_pow, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg l)]
    rw [show (6:ℕ) = 2*3 by norm_num, pow_mul, Real.sq_sqrt hl.le]
  simp only [hp]
  rw [integral_const_mul]
  have hj : l * (∫ x, ‖u (stretch ω l x)‖^6) = ∫ x, ‖u x‖^6 :=
    stretch_integral hω hl (fun x => ‖u x‖^6)
  calc
    _ = l^2 * (l * ∫ x, ‖u (stretch ω l x)‖^6) := by ring
    _ = _ := by rw [hj]

/-- Joint domain and identity certificate for the paper's complex dotH1 dilation. -/
theorem sobolev_stretch_domain_and_kinetic {u : Space → ℂ} {GRe GIm : Space → Space}
    (h : InDotH1 u GRe GIm) {ω : Space} (hω : ‖ω‖ = 1) {l : ℝ} (hl : 0 < l) :
    InDotH1 (stretchedFunction ω l u) (stretchedGradient ω l GRe) (stretchedGradient ω l GIm) ∧
    Integrable (fun x => ‖complexGradient (stretchedGradient ω l GRe)
      (stretchedGradient ω l GIm) x‖^2) volume ∧
    Integrable (fun x => ‖stretchedFunction ω l u x‖^6) volume ∧
    kinetic (stretchedGradient ω l GRe) (stretchedGradient ω l GIm) =
      perpendicularKinetic ω GRe GIm + l^2 * directionalKinetic ω GRe GIm ∧
    (∫ x, ‖stretchedFunction ω l u x‖^6) = l^2 * (∫ x, ‖u x‖^6) := by
  have hs := h.stretch hω hl
  exact ⟨hs, kinetic_density_integrable hs.real_gradient_L2 hs.imag_gradient_L2,
    hs.function_L6.integrable_norm_pow (by decide : (6:ℕ) ≠ 0),
    kinetic_stretch h hω hl, sixth_mass_stretch hω hl u⟩

/-- The transverse kinetic quantity is itself a genuine nonnegative projection
integral, with its absolute domain produced from the two L2 weak gradients. -/
theorem perpendicularKinetic_domain_and_projection {GRe GIm : Space → Space}
    (hR : MemLp GRe 2 volume) (hI : MemLp GIm 2 volume)
    {ω : Space} (hω : ‖ω‖ = 1) :
    Integrable (fun x => ‖GRe x - ⟪ω,GRe x⟫ • ω‖^2 +
      ‖GIm x - ⟪ω,GIm x⟫ • ω‖^2) volume ∧
    perpendicularKinetic ω GRe GIm =
      ∫ x, ‖GRe x - ⟪ω,GRe x⟫ • ω‖^2 + ‖GIm x - ⟪ω,GIm x⟫ • ω‖^2 := by
  have he (x : Space) : ‖complexGradient GRe GIm x‖^2 -
      ‖complexDirectionalGradient ω GRe GIm x‖^2 =
      ‖GRe x - ⟪ω,GRe x⟫ • ω‖^2 + ‖GIm x - ⟪ω,GIm x⟫ • ω‖^2 := by
    rw [complexGradient_norm_sq, complexDirectionalGradient_norm_sq,
      ← transverseSq_eq_norm_projection hω, ← transverseSq_eq_norm_projection hω]
    unfold transverseSq longitudinalSq
    ring
  constructor
  · apply ((kinetic_density_integrable hR hI).sub
      (directionalKinetic_density_integrable hR hI ω)).congr
    exact Filter.Eventually.of_forall he
  · unfold perpendicularKinetic kinetic directionalKinetic
    rw [← integral_sub (kinetic_density_integrable hR hI)
      (directionalKinetic_density_integrable hR hI ω)]
    exact integral_congr_ae (Filter.Eventually.of_forall he)

theorem perpendicularKinetic_nonneg {GRe GIm : Space → Space}
    (hR : MemLp GRe 2 volume) (hI : MemLp GIm 2 volume)
    {ω : Space} (hω : ‖ω‖ = 1) : 0 ≤ perpendicularKinetic ω GRe GIm := by
  rw [(perpendicularKinetic_domain_and_projection hR hI hω).2]
  exact integral_nonneg (fun x => add_nonneg (sq_nonneg _) (sq_nonneg _))

theorem directionalKinetic_nonneg (ω : Space) (GRe GIm : Space → Space) :
    0 ≤ directionalKinetic ω GRe GIm :=
  integral_nonneg (fun _ => sq_nonneg _)

#print axioms complexGradient_norm_sq
#print axioms complexDirectionalGradient_norm_sq
#print axioms directional_sq_integrable
#print axioms kinetic_density_integrable
#print axioms directionalKinetic_density_integrable
#print axioms kinetic_eq_sum
#print axioms directionalKinetic_eq_sum
#print axioms stretchedGradient_norm_sq
#print axioms real_gradient_energy_stretch
#print axioms kinetic_stretch
#print axioms sixth_mass_stretch
#print axioms sobolev_stretch_domain_and_kinetic
#print axioms perpendicularKinetic_domain_and_projection
#print axioms perpendicularKinetic_nonneg
#print axioms directionalKinetic_nonneg
end HartreeF.SobolevStretch
