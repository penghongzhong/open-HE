import DirectionalSixMajorants
noncomputable section
set_option autoImplicit false
namespace HartreeF.DerivativeMajorization
open GradientMajorants

theorem weightedMajorantSum_le {α c : ℝ} (ha : 0<α) (hc : 0≤c)
    {V W Y Z : Space → ℝ} (hV : ∀ x, 0≤V x) (hW : ∀ x, 0≤W x)
    (hY : ∀ x, 0≤Y x) (hZ : ∀ x, 0≤Z x) (x : Space) :
    weightedMajorantSum α c V W Y Z x ≤ (6+α)^2*majorantSum α c V W Y Z x := by
  have hp (a : ℝ) (y : Space) : 0≤V y^a := Real.rpow_nonneg (hV y) a
  have hp1 := rieszConvolution_nonneg (α := α) hc (fun y => hp (3+α) y) x
  have hp2 := rieszConvolution_nonneg (α := α) hc (fun y => mul_nonneg (hp (2+α) y) (hW y)) x
  have hp4 := rieszConvolution_nonneg (α := α) hc (fun y => mul_nonneg (hp (2+α) y) (hZ y)) x
  have hp5 := rieszConvolution_nonneg (α := α) hc
    (fun y => mul_nonneg (mul_nonneg (hp (1+α) y) (hW y)) (hY y)) x
  have hp6 := rieszConvolution_nonneg (α := α) hc (fun y => mul_nonneg (hp (2+α) y) (hY y)) x
  have h1 : 0≤majorant1 α c V Z x := mul_nonneg (mul_nonneg hp1 (hp (1+α) x)) (hZ x)
  have h2 : 0≤majorant2 α c V W Y x := mul_nonneg (mul_nonneg hp2 (hp (1+α) x)) (hY x)
  have h3 : 0≤majorant3 α c V W Y x := mul_nonneg (mul_nonneg (mul_nonneg hp1 (hp α x)) (hW x)) (hY x)
  have h4 : 0≤majorant4 α c V Z x := mul_nonneg hp4 (hp (2+α) x)
  have h5 : 0≤majorant5 α c V W Y x := mul_nonneg hp5 (hp (2+α) x)
  have h6 : 0≤majorant6 α c V W Y x := mul_nonneg (mul_nonneg hp6 (hp (1+α) x)) (hW x)
  have hc1 : 2+α≤(6+α)^2 := by nlinarith [sq_nonneg α]
  have hc2 : (3+α)*(2+α)≤(6+α)^2 := by nlinarith
  have hc3 : (1+α)*(6+α)≤(6+α)^2 := by nlinarith
  have hc4 : 3+α≤(6+α)^2 := by nlinarith [sq_nonneg α]
  have hb := add_le_add (add_le_add (add_le_add (add_le_add (add_le_add
    (mul_le_mul_of_nonneg_right hc1 h1) (mul_le_mul_of_nonneg_right hc2 h2))
    (mul_le_mul_of_nonneg_right hc3 h3)) (mul_le_mul_of_nonneg_right hc4 h4))
    (mul_le_mul_of_nonneg_right hc2 h5)) (mul_le_mul_of_nonneg_right hc2 h6)
  convert hb using 1
  · rfl
  · dsimp [majorantSum]
    ring

#print axioms weightedMajorantSum_le
end HartreeF.DerivativeMajorization
