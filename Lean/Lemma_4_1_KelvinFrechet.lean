import Lemma_4_1_Kelvin
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Pow

noncomputable section
namespace BWork.Kelvin

abbrev Plane := ℝ × ℝ

def inversion (R : ℝ) (p : Plane) : Plane := (kx R p.1 p.2, ky R p.1 p.2)

def jacobian (R : ℝ) (p : Plane) : Plane →L[ℝ] Plane :=
  ((j11 R p.1 p.2 • ContinuousLinearMap.fst ℝ ℝ ℝ) +
    (j12 R p.1 p.2 • ContinuousLinearMap.snd ℝ ℝ ℝ)).prod
  ((j12 R p.1 p.2 • ContinuousLinearMap.fst ℝ ℝ ℝ) +
    (j22 R p.1 p.2 • ContinuousLinearMap.snd ℝ ℝ ℝ))

theorem derivative_inversion (R : ℝ) (p : Plane) (h : s p.1 p.2 ≠ 0) :
    HasFDerivAt (inversion R) (jacobian R p) p := by
  have hx : HasFDerivAt (fun z : Plane => z.1) (ContinuousLinearMap.fst ℝ ℝ ℝ) p :=
    hasFDerivAt_fst
  have hy : HasFDerivAt (fun z : Plane => z.2) (ContinuousLinearMap.snd ℝ ℝ ℝ) p :=
    hasFDerivAt_snd
  have hs := (hx.pow 2).add (hy.pow 2)
  have hi := (hasFDerivAt_inv h).comp p hs
  have h1 := (hx.const_mul (R ^ 2)).mul hi
  have h2 := (hy.const_mul (R ^ 2)).mul hi
  have hp := h1.prodMk h2
  convert hp using 1
  · funext z
    simp [inversion, kx, ky, s, div_eq_mul_inv]
  · ext <;> simp [jacobian, j11, j12, j22, s, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.prod_apply]
    all_goals field_simp
    all_goals ring

theorem jacobian_apply (R : ℝ) (p z : Plane) :
    jacobian R p z =
      (j11 R p.1 p.2 * z.1 + j12 R p.1 p.2 * z.2,
       j12 R p.1 p.2 * z.1 + j22 R p.1 p.2 * z.2) := by
  simp [jacobian]

theorem jacobian_energy (R : ℝ) (p z : Plane) (h : s p.1 p.2 ≠ 0) :
    s (jacobian R p z).1 (jacobian R p z).2 =
      R ^ 4 / (s p.1 p.2) ^ 2 * s z.1 z.2 := by
  rw [jacobian_apply]
  exact differential_norm R p.1 p.2 z.1 z.2 h

theorem inversion_involutive (R : ℝ) (p : Plane)
    (hR : R ≠ 0) (h : s p.1 p.2 ≠ 0) : inversion R (inversion R p) = p := by
  ext
  · exact involution_x R p.1 p.2 hR h
  · exact involution_y R p.1 p.2 hR h

#print axioms derivative_inversion
#print axioms jacobian_apply
#print axioms jacobian_energy
#print axioms inversion_involutive
end BWork.Kelvin
