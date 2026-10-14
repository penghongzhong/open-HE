import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Tactic

/-! F: actual scalar Fourier kernel for the 3D generalized Hartree directional
stretch.  This is a new native proof, not an assumed Hartree analytic interface.
Here gamma = alpha/2, a = xi_parallel^2, b = norm(xi_perp)^2. -/
noncomputable section
set_option autoImplicit false
namespace HartreeF

def stretchKernel (γ a b s : ℝ) : ℝ := s ^ (1 + γ) * (a*s+b) ^ (-γ)
def stretchKernelD1 (γ a b s : ℝ) : ℝ :=
  s ^ γ * (a*s+b) ^ (-γ-1) * (a*s+(1+γ)*b)
def stretchKernelD2 (γ a b s : ℝ) : ℝ :=
  γ*(1+γ)*b^2 * s^(γ-1) * (a*s+b)^(-γ-2)

theorem affine_positive {a b s : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : 0 < a+b) (hs : 0 < s) : 0 < a*s+b := by
  rcases lt_or_eq_of_le ha with ha | ha
  · positivity
  · have : a = 0 := ha.symm
    simpa [this] using hab

theorem rpow_add_one {x : ℝ} (hx : 0 < x) (r : ℝ) :
    x^(r+1) = x^r*x := by rw [Real.rpow_add hx]; simp

theorem hasDerivAt_stretchKernel {γ a b s : ℝ}
    (hs : 0 < s) (hL : 0 < a*s+b) :
    HasDerivAt (stretchKernel γ a b) (stretchKernelD1 γ a b s) s := by
  have h1 := Real.hasDerivAt_rpow_const (x := s) (p := 1+γ) (Or.inl hs.ne')
  have h2 := (((hasDerivAt_id s).const_mul a).add_const b).rpow_const
    (p := -γ) (Or.inl hL.ne')
  unfold stretchKernel
  convert h1.mul h2 using 1
  · rfl
  unfold stretchKernelD1
  have e1 : 1+γ-1 = γ := by ring
  have e2 : s^(1+γ) = s^γ*s := by
    rw [show 1+γ=γ+1 by ring, rpow_add_one hs]
  have e3 : (a*s+b)^(-γ) = (a*s+b)^(-γ-1)*(a*s+b) := by
    calc
      _ = (a*s+b)^((-γ-1)+1) := by congr 1; ring
      _ = _ := rpow_add_one hL (-γ-1)
  simp only [id_eq, e1, e2, e3]
  ring

theorem hasDerivAt_stretchKernelD1 {γ a b s : ℝ}
    (hs : 0 < s) (hL : 0 < a*s+b) :
    HasDerivAt (stretchKernelD1 γ a b) (stretchKernelD2 γ a b s) s := by
  have h1 := Real.hasDerivAt_rpow_const (x := s) (p := γ) (Or.inl hs.ne')
  have h2 := (((hasDerivAt_id s).const_mul a).add_const b).rpow_const
    (p := -γ-1) (Or.inl hL.ne')
  have h3 := ((hasDerivAt_id s).const_mul a).add_const ((1+γ)*b)
  unfold stretchKernelD1
  convert (h1.mul h2).mul h3 using 1
  · rfl
  unfold stretchKernelD2
  have e1 : -γ-1-1 = -γ-2 := by ring
  have e2 : s^γ = s^(γ-1)*s := by
    calc
      _ = s^((γ-1)+1) := by congr 1; ring
      _ = _ := rpow_add_one hs (γ-1)
  have e3 : (a*s+b)^(-γ-1) = (a*s+b)^(-γ-2)*(a*s+b) := by
    calc
      _ = (a*s+b)^((-γ-2)+1) := by congr 1; ring
      _ = _ := rpow_add_one hL (-γ-2)
  simp only [id_eq, Pi.mul_apply, e1, e2, e3]
  ring

theorem stretchKernelD2_nonneg {γ a b s : ℝ} (hγ : 0 ≤ γ)
    (hs : 0 < s) (hL : 0 < a*s+b) : 0 ≤ stretchKernelD2 γ a b s := by
  unfold stretchKernelD2
  positivity

theorem convexOn_stretchKernel {γ a b : ℝ} (hγ : 0 ≤ γ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : 0 < a+b) :
    ConvexOn ℝ (Set.Ioi 0) (stretchKernel γ a b) := by
  have hd : ∀ s ∈ Set.Ioi (0:ℝ),
      HasDerivAt (stretchKernel γ a b) (stretchKernelD1 γ a b s) s := by
    intro s hs
    exact hasDerivAt_stretchKernel hs (affine_positive ha hb hab hs)
  apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Ioi 0)
    (fun s hs => (hd s hs).continuousAt.continuousWithinAt)
  · intro s hs
    exact (hd s (Set.mem_of_mem_of_subset hs interior_subset)).hasDerivWithinAt
  · intro s hs
    have hs0 : 0 < s := Set.mem_of_mem_of_subset hs interior_subset
    exact (hasDerivAt_stretchKernelD1 hs0
      (affine_positive ha hb hab hs0)).hasDerivWithinAt
  · intro s hs
    have hs0 : 0 < s := Set.mem_of_mem_of_subset hs interior_subset
    exact stretchKernelD2_nonneg hγ hs0 (affine_positive ha hb hab hs0)

theorem stretchKernel_tangent {γ a b s : ℝ} (hγ : 0 ≤ γ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : 0 < a+b) (hs : 1 ≤ s) :
    stretchKernel γ a b 1 + (s-1)*stretchKernelD1 γ a b 1 ≤
      stretchKernel γ a b s := by
  rcases eq_or_lt_of_le hs with hs | hs
  · subst s; simp
  have h := (convexOn_stretchKernel hγ ha hb hab).le_slope_of_hasDerivAt
    (by norm_num : (1:ℝ) ∈ Set.Ioi 0) (by change 0<s; linarith) hs
    (hasDerivAt_stretchKernel (by norm_num) (by simpa using hab))
  rw [slope_def_field] at h
  have h' := (le_div_iff₀ (sub_pos.mpr hs)).mp h
  nlinarith

theorem stretchKernel_nonneg {γ a b s : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hs : 0 ≤ s) : 0 ≤ stretchKernel γ a b s := by
  unfold stretchKernel; positivity

theorem stretchKernel_large_bound {γ a b s : ℝ} (hγ : 0 ≤ γ)
    (ha : 0 ≤ a) (_hb : 0 ≤ b) (hab : 0 < a+b) (hs : 1 ≤ s) :
    stretchKernel γ a b s ≤ s^(1+γ)*stretchKernel γ a b 1 := by
  have hL : a+b ≤ a*s+b := by nlinarith
  have hp := Real.rpow_le_rpow_of_nonpos hab hL (neg_nonpos.mpr hγ)
  simpa only [stretchKernel, Real.one_rpow, mul_one, one_mul] using
    mul_le_mul_of_nonneg_left hp (Real.rpow_nonneg (by linarith) (1+γ))

theorem stretchKernelD1_bound {γ a b : ℝ} (hγ : 0 ≤ γ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : 0 < a+b) :
    0 ≤ stretchKernelD1 γ a b 1 ∧
    stretchKernelD1 γ a b 1 ≤ (1+γ)*stretchKernel γ a b 1 := by
  have hp : (a+b)^(-γ) = (a+b)^(-γ-1)*(a+b) := by
    calc
      _ = (a+b)^((-γ-1)+1) := by congr 1; ring
      _ = _ := rpow_add_one hab (-γ-1)
  simp only [stretchKernelD1, stretchKernel, Real.one_rpow, mul_one, one_mul]
  constructor
  · positivity
  · rw [hp]
    have hc : a+(1+γ)*b ≤ (1+γ)*(a+b) := by nlinarith
    have ht := mul_le_mul_of_nonneg_left hc (Real.rpow_nonneg hab.le (-γ-1))
    nlinarith

#print axioms affine_positive
#print axioms hasDerivAt_stretchKernel
#print axioms hasDerivAt_stretchKernelD1
#print axioms stretchKernelD2_nonneg
#print axioms convexOn_stretchKernel
#print axioms stretchKernel_tangent
#print axioms stretchKernel_large_bound
#print axioms stretchKernelD1_bound
end HartreeF
