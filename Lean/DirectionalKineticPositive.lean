import SobolevKineticStretch

/-!
Strict positivity of every actual directional kinetic integral on the
nonzero complex homogeneous Sobolev class. The only analytic interface
added here is the ordinary, unweighted Sobolev inequality on its full
complex dotH1 domain. All anisotropic identities and output domains are
the already proved C11 producers.
-/
noncomputable section
set_option autoImplicit false
open MeasureTheory Set
open scoped RealInnerProductSpace ENNReal
namespace HartreeF.SobolevStretch
open DirectionalStretch

/-- The ordinary Sobolev inequality, universally quantified over the genuine
complex homogeneous Sobolev class and its two real weak gradients. -/
structure OrdinarySobolev (K : ℝ) : Prop where
  nonneg : 0 ≤ K
  bound : ∀ {u : Space → ℂ} {GRe GIm : Space → Space},
    InDotH1 u GRe GIm →
    (∫ x, ‖u x‖^6) ≤ K * (kinetic GRe GIm)^3

theorem kinetic_nonneg (GRe GIm : Space → Space) :
    0 ≤ kinetic GRe GIm :=
  integral_nonneg (fun _ => sq_nonneg _)

/-- Nonzero means a nonzero almost-everywhere class, with no selected
pointwise representative required. L6 supplies the actual finite integral. -/
theorem sixth_mass_pos {u : Space → ℂ} (hu : MemLp u 6 volume)
    (hnonzero : ¬ u =ᵐ[volume] 0) :
    0 < (∫ x, ‖u x‖^6) := by
  have hnonneg : 0 ≤ (∫ x, ‖u x‖^6) :=
    integral_nonneg (fun _ => pow_nonneg (norm_nonneg _) _)
  by_contra hnot
  have hzero : (∫ x, ‖u x‖^6) = 0 :=
    le_antisymm (le_of_not_gt hnot) hnonneg
  have hae := (integral_eq_zero_iff_of_nonneg
    (fun x => pow_nonneg (norm_nonneg (u x)) 6)
    (hu.integrable_norm_pow (by decide : (6 : ℕ) ≠ 0))).1 hzero
  apply hnonzero
  filter_upwards [hae] with x hx
  simpa only [Pi.zero_apply, pow_eq_zero_iff (by decide : (6 : ℕ) ≠ 0),
    norm_eq_zero] using hx

/-- If one genuine directional kinetic integral were zero, stretching would
leave the actual kinetic integral constant while its actual sixth mass
grew by l squared. Ordinary Sobolev on that produced stretched function
then contradicts positivity of the original sixth mass. -/
theorem directionalKinetic_pos {K : ℝ} (hSob : OrdinarySobolev K)
    {u : Space → ℂ} {GRe GIm : Space → Space} (h : InDotH1 u GRe GIm)
    (hnonzero : ¬ u =ᵐ[volume] 0) {ω : Space} (hω : ‖ω‖ = 1) :
    0 < directionalKinetic ω GRe GIm := by
  have hm := sixth_mass_pos h.function_L6 hnonzero
  have hA := kinetic_nonneg GRe GIm
  have hC : 0 ≤ K * (kinetic GRe GIm)^3 :=
    mul_nonneg hSob.nonneg (pow_nonneg hA _)
  by_contra hnot
  have hzero : directionalKinetic ω GRe GIm = 0 :=
    le_antisymm (le_of_not_gt hnot) (directionalKinetic_nonneg ω GRe GIm)
  let l : ℝ := Real.sqrt (K * (kinetic GRe GIm)^3 / (∫ x, ‖u x‖^6) + 1)
  have hratio : 0 ≤ K * (kinetic GRe GIm)^3 / (∫ x, ‖u x‖^6) :=
    div_nonneg hC hm.le
  have hl : 0 < l := Real.sqrt_pos.2 (by linarith)
  have hl_sq : l^2 = K * (kinetic GRe GIm)^3 / (∫ x, ‖u x‖^6) + 1 :=
    Real.sq_sqrt (by linarith)
  have henergy : kinetic (stretchedGradient ω l GRe)
      (stretchedGradient ω l GIm) = kinetic GRe GIm := by
    simpa only [perpendicularKinetic, hzero, sub_zero, mul_zero, add_zero]
      using kinetic_stretch h hω hl
  have hbound := hSob.bound (h.stretch hω hl)
  rw [sixth_mass_stretch hω hl u, henergy, hl_sq, add_mul,
    div_mul_cancel₀ _ hm.ne', one_mul] at hbound
  linarith

/-- Finite-domain positivity certificate: all three displayed integrals
have their genuine L1 domains, and the sixth mass and A_omega are positive. -/
theorem directionalKinetic_finite_domain_positive {K : ℝ} (hSob : OrdinarySobolev K)
    {u : Space → ℂ} {GRe GIm : Space → Space} (h : InDotH1 u GRe GIm)
    (hnonzero : ¬ u =ᵐ[volume] 0) {ω : Space} (hω : ‖ω‖ = 1) :
    Integrable (fun x => ‖u x‖^6) volume ∧
    Integrable (fun x => ‖complexGradient GRe GIm x‖^2) volume ∧
    Integrable (fun x => ‖complexDirectionalGradient ω GRe GIm x‖^2) volume ∧
    0 < (∫ x, ‖u x‖^6) ∧ 0 < directionalKinetic ω GRe GIm := by
  exact ⟨h.function_L6.integrable_norm_pow (by decide : (6 : ℕ) ≠ 0),
    kinetic_density_integrable h.real_gradient_L2 h.imag_gradient_L2,
    directionalKinetic_density_integrable h.real_gradient_L2 h.imag_gradient_L2 ω,
    sixth_mass_pos h.function_L6 hnonzero,
    directionalKinetic_pos hSob h hnonzero hω⟩

#print axioms OrdinarySobolev
#print axioms kinetic_nonneg
#print axioms sixth_mass_pos
#print axioms directionalKinetic_pos
#print axioms directionalKinetic_finite_domain_positive
end HartreeF.SobolevStretch
