import DirectionalKineticPositive
import VariationalHartreeThreshold

/-!
Native production of a universal Hartree-Sobolev bound on the actual complex
homogeneous Sobolev domain from the ordinary HLS and ordinary Sobolev interfaces.
The produced positive threshold is not asserted to be sharp or to equal the
kinetic energy of a ground state.
-/
noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal NNReal
namespace HartreeF.DirectionalCoercivity
open SobolevStretch HeatRiesz ForcingDomain

/-- The HLS density bound controls the literal real interaction integral.
Its integrability is produced by the existing L6-to-L1 theorem. -/
theorem interaction_real_norm_bound {α : ℝ}
    (hHLS : OrdinaryHLS α (standardRieszConstant α)) :
    ∃ H : ℝ≥0, ∀ u : Space → ℂ, MemLp u 6 volume →
      interaction α u ≤ (H : ℝ) * (eLpNorm u 6 volume).toReal ^ (3+α) *
        (eLpNorm u 6 volume).toReal ^ (3+α) := by
  obtain ⟨H, hH⟩ := interaction_density_domain_bound hHLS
  refine ⟨H, fun u hu => ?_⟩
  obtain ⟨hi, hb⟩ := hH u hu
  have hn : (H : ℝ≥0∞) * eLpNorm u 6 volume ^ (3+α) *
      eLpNorm u 6 volume ^ (3+α) ≠ ∞ := by
    have hu' := hu.eLpNorm_ne_top
    have hp : 0 ≤ 3+α := by linarith [hHLS.order_pos]
    finiteness
  have hr := ENNReal.toReal_mono hn hb
  simp only [ENNReal.toReal_mul, ENNReal.coe_toReal, ← ENNReal.toReal_rpow] at hr
  have he : (eLpNorm (fun x => potential α (standardRieszConstant α) u x *
      powerDensity α u x) 1 volume).toReal =
      ∫ x, ‖potential α (standardRieszConstant α) u x * powerDensity α u x‖ := by
    rw [MemLp.eLpNorm_eq_integral_rpow_norm one_ne_zero ENNReal.one_ne_top
      (memLp_one_iff_integrable.mpr hi)]
    simp only [ENNReal.toReal_one, inv_one, Real.rpow_one]
    exact ENNReal.toReal_ofReal (integral_nonneg (fun _ => norm_nonneg _))
  calc
    interaction α u ≤ ‖interaction α u‖ := le_abs_self _
    _ ≤ ∫ x, ‖potential α (standardRieszConstant α) u x * powerDensity α u x‖ :=
      norm_integral_le_integral_norm _
    _ ≤ _ := by rwa [he] at hr

/-- The sixth power of the finite L6 norm is the actual sixth-mass integral. -/
theorem sixth_norm_pow_eq_integral {u : Space → ℂ} (hu : MemLp u 6 volume) :
    (eLpNorm u 6 volume).toReal ^ (6 : ℝ) = ∫ x, ‖u x‖^6 := by
  have hm : 0 ≤ ∫ x, ‖u x‖^6 := integral_nonneg (fun _ => pow_nonneg (norm_nonneg _) _)
  rw [MemLp.eLpNorm_eq_integral_rpow_norm (by norm_num : (6 : ℝ≥0∞) ≠ 0)
    (by norm_num : (6 : ℝ≥0∞) ≠ ∞) hu]
  norm_num only [ENNReal.toReal_ofNat, Real.rpow_ofNat]
  rw [ENNReal.toReal_ofReal (Real.rpow_nonneg hm _)]
  simpa using Real.rpow_inv_natCast_pow hm (by decide : (6 : ℕ) ≠ 0)

/-- The complete combined inequality is produced here from ordinary HLS and
ordinary Sobolev. The coefficient is positive and uniform over every actual
complex weak-Sobolev function and both of its real weak gradients. -/
theorem exists_hartree_sobolev_constant {α K : ℝ}
    (hHLS : OrdinaryHLS α (standardRieszConstant α)) (hSob : OrdinarySobolev K) :
    ∃ C : ℝ, 0 < C ∧ ∀ {u : Space → ℂ} {GRe GIm : Space → Space},
      InDotH1 u GRe GIm →
      interaction α u ≤ C * (kinetic GRe GIm)^(3+α) := by
  obtain ⟨H, hH⟩ := interaction_real_norm_bound hHLS
  let C : ℝ := (H : ℝ) * K^((3+α)/3) + 1
  have hcoeff : 0 ≤ (H : ℝ) * K^((3+α)/3) :=
    mul_nonneg H.coe_nonneg (Real.rpow_nonneg hSob.nonneg _)
  refine ⟨C, by dsimp [C]; linarith, fun {u GRe GIm} hu => ?_⟩
  have hn : 0 ≤ (eLpNorm u 6 volume).toReal := ENNReal.toReal_nonneg
  have hA := kinetic_nonneg GRe GIm
  have hp : 0 < 3+α := by linarith [hHLS.order_pos]
  have hm : 0 ≤ ∫ x, ‖u x‖^6 := integral_nonneg (fun _ => pow_nonneg (norm_nonneg _) _)
  have hpow := Real.rpow_le_rpow hm (hSob.bound hu) (show 0 ≤ (3+α)/3 by positivity)
  have hnorm : (eLpNorm u 6 volume).toReal ^ (3+α) *
      (eLpNorm u 6 volume).toReal ^ (3+α) = (∫ x, ‖u x‖^6)^((3+α)/3) := by
    rw [← sixth_norm_pow_eq_integral hu.function_L6, ← Real.rpow_mul hn,
      ← Real.rpow_add' hn (by linarith : (3+α)+(3+α) ≠ 0)]
    congr 1
    ring
  have hkin : (K * (kinetic GRe GIm)^3)^((3+α)/3) =
      K^((3+α)/3) * (kinetic GRe GIm)^(3+α) := by
    rw [Real.mul_rpow hSob.nonneg (pow_nonneg hA _), ← Real.rpow_natCast,
      ← Real.rpow_mul hA]
    congr 2
    ring
  calc
    interaction α u ≤ (H : ℝ) * (eLpNorm u 6 volume).toReal ^ (3+α) *
        (eLpNorm u 6 volume).toReal ^ (3+α) := hH u hu.function_L6
    _ = (H : ℝ) * (∫ x, ‖u x‖^6)^((3+α)/3) := by rw [mul_assoc, hnorm]
    _ ≤ (H : ℝ) * (K * (kinetic GRe GIm)^3)^((3+α)/3) :=
      mul_le_mul_of_nonneg_left hpow H.coe_nonneg
    _ = ((H : ℝ) * K^((3+α)/3)) * (kinetic GRe GIm)^(3+α) := by rw [hkin, mul_assoc]
    _ ≤ C * (kinetic GRe GIm)^(3+α) := by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hA _)
      dsimp [C]
      linarith

/-- An explicit positive normalization converts the produced coefficient into
a universal threshold. This existence result carries no optimality assertion. -/
theorem exists_normalized_hartree_sobolev {α K : ℝ}
    (hHLS : OrdinaryHLS α (standardRieszConstant α)) (hSob : OrdinarySobolev K) :
    ∃ G : ℝ, NormalizedHartreeSobolev α G := by
  obtain ⟨C, hC, hbound⟩ := exists_hartree_sobolev_constant hHLS hSob
  let G : ℝ := C^((1-(3+α))⁻¹)
  have he : 1-(3+α) ≠ 0 := by linarith [hHLS.order_pos]
  have hG : 0 < G := Real.rpow_pos_of_pos hC _
  refine ⟨G, hG, fun hu => ?_⟩
  have hnorm : G^(1-(3+α)) = C := by
    dsimp [G]
    rw [← Real.rpow_mul hC.le, inv_mul_cancel₀ he, Real.rpow_one]
  rw [hnorm]
  exact hbound hu

#print axioms interaction_real_norm_bound
#print axioms sixth_norm_pow_eq_integral
#print axioms exists_hartree_sobolev_constant
#print axioms exists_normalized_hartree_sobolev
end HartreeF.DirectionalCoercivity
