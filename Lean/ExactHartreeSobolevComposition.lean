import SharpOrdinaryInterfaces
import ConditionalDirectionalCoercivity

/-!
Native composition of the exact ordinary HLS and squared Sobolev constants.
The universal Hartree-Sobolev bound is produced on the actual weak-function
domain. The resulting explicit threshold is used in the existing actual DC
consumer. Attainment, sharpness of the combined inequality, and identification
with any weak ground state remain separate obligations.
-/
noncomputable section
set_option autoImplicit false
open MeasureTheory
namespace HartreeF.SharpOrdinary
open HeatRiesz ForcingDomain SobolevStretch DirectionalCoercivity

def standardCombinedConstant (α : ℝ) : ℝ :=
  sharpHLSConstant α * sharpSobolevConstant^(3+α)

def standardCombinedThreshold (α : ℝ) : ℝ :=
  (standardCombinedConstant α)^((1-(3+α))⁻¹)

theorem standardCombinedConstant_pos {α : ℝ} (hα : 0 < α) (hα3 : α < 3) :
    0 < standardCombinedConstant α :=
  mul_pos (sharpHLSConstant_pos hα hα3) (Real.rpow_pos_of_pos sharpSobolevConstant_pos _)

theorem standardCombinedThreshold_pos {α : ℝ} (hα : 0 < α) (hα3 : α < 3) :
    0 < standardCombinedThreshold α :=
  Real.rpow_pos_of_pos (standardCombinedConstant_pos hα hα3) _

/-- The exact product H_alpha S^(3+alpha), with no added slack, controls the
actual interaction for every complex weak-Sobolev function. -/
theorem exact_combined_hartree_sobolev {α : ℝ}
    (hOrd : OrdinaryHLS α (standardRieszConstant α)) (hH : SharpOrdinaryHLS α)
    (hS : SharpOrdinarySobolev) {u : Space → ℂ} {GRe GIm : Space → Space}
    (hu : InDotH1 u GRe GIm) :
    interaction α u ≤ standardCombinedConstant α * (kinetic GRe GIm)^(3+α) := by
  have hn : 0 ≤ (eLpNorm u 6 volume).toReal := ENNReal.toReal_nonneg
  have hp : 0 < 3+α := by linarith [hH.order_pos]
  have hA := kinetic_nonneg GRe GIm
  have hpow := Real.rpow_le_rpow (sq_nonneg ((eLpNorm u 6 volume).toReal)) (hS.bound hu) hp.le
  have hnorm : (eLpNorm u 6 volume).toReal^(3+α) * (eLpNorm u 6 volume).toReal^(3+α) =
      ((eLpNorm u 6 volume).toReal^2)^(3+α) := by
    rw [← Real.rpow_add' hn (by linarith : (3+α)+(3+α) ≠ 0),
      ← Real.rpow_natCast, ← Real.rpow_mul hn]
    congr 1
    ring
  calc
    interaction α u ≤ sharpHLSConstant α * (eLpNorm u 6 volume).toReal^(3+α) *
        (eLpNorm u 6 volume).toReal^(3+α) := sharp_interaction_norm_bound hOrd hH hu.function_L6
    _ = sharpHLSConstant α * ((eLpNorm u 6 volume).toReal^2)^(3+α) := by
      rw [mul_assoc, hnorm]
    _ ≤ sharpHLSConstant α * (sharpSobolevConstant * kinetic GRe GIm)^(3+α) :=
      mul_le_mul_of_nonneg_left hpow (sharpHLSConstant_pos hH.order_pos hH.order_lt_three).le
    _ = standardCombinedConstant α * (kinetic GRe GIm)^(3+α) := by
      rw [Real.mul_rpow sharpSobolevConstant_pos.le hA]
      simp only [standardCombinedConstant, mul_assoc]

/-- The internal normalized Hartree inequality is produced from the two
precisely scoped ordinary inequalities; it is not an external input. -/
theorem exact_normalized_hartree_sobolev {α : ℝ}
    (hOrd : OrdinaryHLS α (standardRieszConstant α)) (hH : SharpOrdinaryHLS α)
    (hS : SharpOrdinarySobolev) :
    NormalizedHartreeSobolev α (standardCombinedThreshold α) := by
  have hc := standardCombinedConstant_pos hH.order_pos hH.order_lt_three
  have he : 1-(3+α) ≠ 0 := by linarith [hH.order_pos]
  refine ⟨standardCombinedThreshold_pos hH.order_pos hH.order_lt_three, fun hu => ?_⟩
  have hn : (standardCombinedThreshold α)^(1-(3+α)) = standardCombinedConstant α := by
    unfold standardCombinedThreshold
    rw [← Real.rpow_mul hc.le, inv_mul_cancel₀ he, Real.rpow_one]
  rw [hn]
  exact exact_combined_hartree_sobolev hOrd hH hS hu

/-- Actual physical directional coercivity at the explicit product-constant
threshold. No optimizer or ground-state identification is claimed. -/
theorem directional_coercivity_at_standard_threshold {α : ℝ}
    (hOrd : OrdinaryHLS α (standardRieszConstant α)) (hH : SharpOrdinaryHLS α)
    (hS : SharpOrdinarySobolev) {u : Space → ℂ} {GRe GIm : Space → Space}
    (hu : InDotH1 u GRe GIm) (hnonzero : ¬ u =ᵐ[volume] 0)
    {ω : Space} (hω : ‖ω‖ = 1) (hgap : kinetic GRe GIm < standardCombinedThreshold α) :
    0 < directionalKinetic ω GRe GIm ∧
    2*(thresholdEnergy α (standardCombinedThreshold α)-energy α u GRe GIm)*
      directionalKinetic ω GRe GIm / (standardCombinedThreshold α-kinetic GRe GIm) ≤
      directionalDefect α ω u GRe GIm ∧
    (energy α u GRe GIm < thresholdEnergy α (standardCombinedThreshold α) →
      0 < directionalDefect α ω u GRe GIm) := by
  have hHS := exact_normalized_hartree_sobolev hOrd hH hS
  exact ⟨directionalKinetic_pos hS.ordinary hu hnonzero hω,
    directional_coercivity_of_normalized_bound hOrd hS.ordinary hHS hu hnonzero hω hgap,
    fun hE => directional_coercivity_positive_of_normalized_bound hOrd hS.ordinary hHS
      hu hnonzero hω hgap hE⟩

#print axioms standardCombinedConstant_pos
#print axioms standardCombinedThreshold_pos
#print axioms exact_combined_hartree_sobolev
#print axioms exact_normalized_hartree_sobolev
#print axioms directional_coercivity_at_standard_threshold
end HartreeF.SharpOrdinary
