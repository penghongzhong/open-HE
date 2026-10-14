import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic

/-! Local concrete calculus for manuscript B, Lemma 4.1.
No integral theorem or whole-paper acceptance is asserted here. -/
noncomputable section
namespace BWork.Kelvin

def s (x y : ℝ) : ℝ := x ^ 2 + y ^ 2

def kx (R x y : ℝ) : ℝ := R ^ 2 * x / s x y

def ky (R x y : ℝ) : ℝ := R ^ 2 * y / s x y

def j11 (R x y : ℝ) : ℝ := R ^ 2 * (y ^ 2 - x ^ 2) / (s x y) ^ 2

def j12 (R x y : ℝ) : ℝ := -(2 * R ^ 2 * x * y) / (s x y) ^ 2

def j22 (R x y : ℝ) : ℝ := R ^ 2 * (x ^ 2 - y ^ 2) / (s x y) ^ 2

theorem s_pos {x y : ℝ} (h : x ≠ 0 ∨ y ≠ 0) : 0 < s x y := by
  rcases h with hx | hy
  · have hx2 := sq_pos_of_ne_zero hx
    dsimp [s]
    nlinarith [sq_nonneg y]
  · have hy2 := sq_pos_of_ne_zero hy
    dsimp [s]
    nlinarith [sq_nonneg x]

theorem derivative_kx_x (R x y : ℝ) (h : s x y ≠ 0) :
    HasDerivAt (fun t : ℝ => kx R t y) (j11 R x y) x := by
  have hs : HasDerivAt (fun t : ℝ => t ^ 2 + y ^ 2) (2 * x) x := by
    simpa [mul_comm, add_comm] using ((hasDerivAt_id x).pow 2).add_const (y ^ 2)
  have hn : HasDerivAt (fun t : ℝ => R ^ 2 * t) (R ^ 2) x := by
    simpa using (hasDerivAt_id x).const_mul (R ^ 2)
  change HasDerivAt (fun t : ℝ => R ^ 2 * t / (t ^ 2 + y ^ 2)) _ x
  convert hn.div hs h using 1
  dsimp [j11, s]
  ring

theorem derivative_kx_y (R x y : ℝ) (h : s x y ≠ 0) :
    HasDerivAt (fun t : ℝ => kx R x t) (j12 R x y) y := by
  have hs : HasDerivAt (fun t : ℝ => x ^ 2 + t ^ 2) (2 * y) y := by
    simpa [mul_comm, add_comm] using ((hasDerivAt_id y).pow 2).const_add (x ^ 2)
  change HasDerivAt (fun t : ℝ => R ^ 2 * x / (x ^ 2 + t ^ 2)) _ y
  convert (hasDerivAt_const y (R ^ 2 * x)).div hs h using 1
  dsimp [j12, s]
  ring

theorem derivative_ky_x (R x y : ℝ) (h : s x y ≠ 0) :
    HasDerivAt (fun t : ℝ => ky R t y) (j12 R x y) x := by
  have hs : HasDerivAt (fun t : ℝ => t ^ 2 + y ^ 2) (2 * x) x := by
    simpa [mul_comm, add_comm] using ((hasDerivAt_id x).pow 2).add_const (y ^ 2)
  change HasDerivAt (fun t : ℝ => R ^ 2 * y / (t ^ 2 + y ^ 2)) _ x
  convert (hasDerivAt_const x (R ^ 2 * y)).div hs h using 1
  dsimp [j12, s]
  ring

theorem derivative_ky_y (R x y : ℝ) (h : s x y ≠ 0) :
    HasDerivAt (fun t : ℝ => ky R x t) (j22 R x y) y := by
  have hs : HasDerivAt (fun t : ℝ => x ^ 2 + t ^ 2) (2 * y) y := by
    simpa [mul_comm, add_comm] using ((hasDerivAt_id y).pow 2).const_add (x ^ 2)
  have hn : HasDerivAt (fun t : ℝ => R ^ 2 * t) (R ^ 2) y := by
    simpa using (hasDerivAt_id y).const_mul (R ^ 2)
  change HasDerivAt (fun t : ℝ => R ^ 2 * t / (x ^ 2 + t ^ 2)) _ y
  convert hn.div hs h using 1
  dsimp [j22, s]
  ring

theorem differential_norm (R x y a b : ℝ) (h : s x y ≠ 0) :
    (j11 R x y * a + j12 R x y * b) ^ 2 +
      (j12 R x y * a + j22 R x y * b) ^ 2 =
      R ^ 4 / (s x y) ^ 2 * (a ^ 2 + b ^ 2) := by
  dsimp [j11, j12, j22, s] at *
  field_simp
  ring

theorem determinant (R x y : ℝ) (h : s x y ≠ 0) :
    j11 R x y * j22 R x y - (j12 R x y) ^ 2 =
      -(R ^ 4 / (s x y) ^ 2) := by
  dsimp [j11, j12, j22, s] at *
  field_simp
  ring

theorem absolute_jacobian (R x y : ℝ) (h : s x y ≠ 0) :
    |j11 R x y * j22 R x y - (j12 R x y) ^ 2| =
      R ^ 4 / (s x y) ^ 2 := by
  rw [determinant R x y h, abs_neg, abs_of_nonneg]
  exact div_nonneg (by positivity) (sq_nonneg _)

theorem image_norm_sq (R x y : ℝ) (h : s x y ≠ 0) :
    s (kx R x y) (ky R x y) = R ^ 4 / s x y := by
  dsimp [s, kx, ky] at *
  field_simp

theorem involution_x (R x y : ℝ) (hR : R ≠ 0) (h : s x y ≠ 0) :
    kx R (kx R x y) (ky R x y) = x := by
  unfold kx
  change R ^ 2 * (R ^ 2 * x / s x y) /
    s (kx R x y) (ky R x y) = x
  rw [image_norm_sq R x y h]
  field_simp

theorem involution_y (R x y : ℝ) (hR : R ≠ 0) (h : s x y ≠ 0) :
    ky R (kx R x y) (ky R x y) = y := by
  unfold ky
  change R ^ 2 * (R ^ 2 * y / s x y) /
    s (kx R x y) (ky R x y) = y
  rw [image_norm_sq R x y h]
  field_simp

#print axioms s_pos
#print axioms derivative_kx_x
#print axioms derivative_kx_y
#print axioms derivative_ky_x
#print axioms derivative_ky_y
#print axioms differential_norm
#print axioms determinant
#print axioms absolute_jacobian
#print axioms image_norm_sq
#print axioms involution_x
#print axioms involution_y
end BWork.Kelvin
