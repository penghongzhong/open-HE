import ForcingLpMap

/-! The complete baseline Hartree environment, with its sum-norm power estimate.
The only analytic input is ordinary strong HLS for the actual Riesz convolution. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
namespace HartreeF.Paper121BaselineHartree
open ForcingDomain ForcingContinuity

theorem sum_power_bound {α x y : ℝ} (hα : 0 < α) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (3+α)*(x^(2+α)+y^(2+α))*x^(2+α) +
      y^(3+α)*(2+α)*(x^(1+α)+y^(1+α)) ≤
        (2*(5+2*α))*(x+y)^(2*(3+α)-2) := by
  have hR : 0 ≤ x+y := add_nonneg hx hy
  have hxR : x ≤ x+y := le_add_of_nonneg_right hy
  have hyR : y ≤ x+y := le_add_of_nonneg_left hx
  have ha1 : 0 ≤ 1+α := by linarith
  have ha2 : 0 ≤ 2+α := by linarith
  have ha3 : 0 ≤ 3+α := by linarith
  calc
    _ ≤ (3+α)*((x+y)^(2+α)+(x+y)^(2+α))*(x+y)^(2+α) +
        (x+y)^(3+α)*(2+α)*((x+y)^(1+α)+(x+y)^(1+α)) := by gcongr
    _ = 2*(3+α)*((x+y)^(2+α)*(x+y)^(2+α)) +
        2*(2+α)*((x+y)^(3+α)*(x+y)^(1+α)) := by ring
    _ = _ := by
      rw [← Real.rpow_add_of_nonneg hR ha2 ha2,
        ← Real.rpow_add_of_nonneg hR ha3 ha1]
      rw [show (2+α)+(2+α) = 2*(3+α)-2 by ring,
        show (3+α)+(1+α) = 2*(3+α)-2 by ring]
      ring

/-- The constant is selected before the inputs; the estimate holds on all L6. -/
theorem forcing_sum_norm_bound {α c : ℝ} (hH : OrdinaryHLS α c) :
    ∃ C : ℝ≥0, ∀ f g : Space → ℂ, MemLp f 6 volume → MemLp g 6 volume →
      (eLpNorm (forcing α c f-forcing α c g)
        (ENNReal.ofReal (6/5 : ℝ)) volume).toReal ≤
      (C : ℝ)*((eLpNorm f 6 volume).toReal+(eLpNorm g 6 volume).toReal)^(2*(3+α)-2)*
        (eLpNorm (f-g) 6 volume).toReal := by
  obtain ⟨C,hC⟩ := forcing_difference_bound hH
  let D : ℝ≥0 := ⟨(C : ℝ)*(2*(5+2*α)), by have hα := hH.order_pos; positivity⟩
  refine ⟨D,fun f g hf hg => ?_⟩
  have hb := sum_power_bound hH.order_pos
    (show 0 ≤ (eLpNorm f 6 volume).toReal from ENNReal.toReal_nonneg)
    (show 0 ≤ (eLpNorm g 6 volume).toReal from ENNReal.toReal_nonneg)
  exact (hC f g hf hg).trans
    ((mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hb C.coe_nonneg)
      ENNReal.toReal_nonneg).trans_eq (by dsimp [D]; ring))

/-- Every representative is literal; absolute convolution integrability is included. -/
theorem baseline_domains {α c : ℝ} (hH : OrdinaryHLS α c)
    {f : Space → ℂ} (hf : MemLp f 6 volume) :
    MemLp (powerDensity α f) (ENNReal.ofReal (6/(3+α))) volume ∧
    (∀ᵐ x ∂volume, Integrable
      (fun y => rieszKernel α c (x-y)*powerDensity α f y) volume) ∧
    MemLp (potential α c f) (ENNReal.ofReal (6/(3-α))) volume ∧
    MemLp (localFactor α f) (ENNReal.ofReal (6/(2+α))) volume ∧
    MemLp (forcing α c f) (ENNReal.ofReal (6/5 : ℝ)) volume := by
  obtain ⟨C,hC⟩ := potential_domain_bound hH
  exact ⟨powerDensity_memLp hH.order_pos hf, (hC f hf).1, (hC f hf).2.1,
    localFactor_memLp (p := 6) hH.order_pos (by simpa using hf), forcing_memLp hH hf⟩

/-- All clauses of the baseline environment, including exact exponents and continuity.
L6 is a stronger input domain than the homogeneous energy space in the manuscript. -/
theorem baseline_hartree_environment {α c : ℝ} (hH : OrdinaryHLS α c) :
    (1 < 6/(3+α) ∧ 6/(3+α) < 3/α ∧ 0 < 6/(3-α) ∧
      1/(6/(3-α)) = 1/(6/(3+α))-α/3) ∧
    1/(6/(3-α))+1/(6/(2+α)) = (5/6 : ℝ) ∧
    (∀ f : Space → ℂ, MemLp f 6 volume →
      MemLp (powerDensity α f) (ENNReal.ofReal (6/(3+α))) volume ∧
      (∀ᵐ x ∂volume, Integrable
        (fun y => rieszKernel α c (x-y)*powerDensity α f y) volume) ∧
      MemLp (potential α c f) (ENNReal.ofReal (6/(3-α))) volume ∧
      MemLp (localFactor α f) (ENNReal.ofReal (6/(2+α))) volume ∧
      MemLp (forcing α c f) (ENNReal.ofReal (6/5 : ℝ)) volume) ∧
    Continuous (forcingLp hH) ∧
    (∃ C : ℝ≥0, ∀ f g : Space → ℂ, MemLp f 6 volume → MemLp g 6 volume →
      (eLpNorm (forcing α c f-forcing α c g)
        (ENNReal.ofReal (6/5 : ℝ)) volume).toReal ≤
      (C : ℝ)*((eLpNorm f 6 volume).toReal+(eLpNorm g 6 volume).toReal)^(2*(3+α)-2)*
        (eLpNorm (f-g) 6 volume).toReal) := by
  refine ⟨energyHLS_range hH.order_pos hH.order_lt_three, ?_,
    fun _ hf => baseline_domains hH hf, forcingLp_continuous hH, forcing_sum_norm_bound hH⟩
  simp only [one_div, inv_div]
  ring

end HartreeF.Paper121BaselineHartree
