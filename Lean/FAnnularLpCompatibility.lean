import FComplexYoungRepresentative
import FEnlargedAnnularL1

/-!
F-only static proof candidate. NOT COMPILED.
Finite sums preserve the common actual representative proved in
FComplexYoungRepresentative. In particular the existing canonical annular
and enlarged-annular OneSpace outputs themselves belong to L6/5.
No domain assumption on the original distribution, HLS assertion, or new
Young estimate is postulated.
-/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory Filter
open scoped ENNReal Topology SchwartzMap

namespace HartreeF.AnnularL1
open EnergySpace EnergySpace.Highpass YoungSource MassRecovery ComplexYoungRepresentative

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The same finite inverse-gradient construction in any finite Lp space. -/
def inverseGradientLp (hp : p ≠ ∞) (k : Fin 3 → Test) (H : Fin 3 → OneSpace) :
    Lp ℂ p (volume : Measure V) :=
  ∑ j : Fin 3, youngCLM hp ((k j).toLp p volume) (H j)

/-- Finite-sum a.e. compatibility for the canonical L1 and actual Lp values. -/
theorem inverseGradientL1_coe_ae_lp (hp : p ≠ ∞)
    (k : Fin 3 → Test) (H : Fin 3 → OneSpace) :
    (inverseGradientL1 k H : V → ℂ) =ᵐ[volume]
      (inverseGradientLp hp k H : V → ℂ) := by
  unfold inverseGradientL1 inverseGradientLp
  exact ((Lp.coeFn_finsetSum Finset.univ _).trans
    (eventuallyEq_sum fun j _ =>
      young_schwartz_coe_ae_cross (p := 1) (r := p)
        (by simp : (1 : ℝ≥0∞) ≠ ∞) hp (k j) (H j))).trans
    (Lp.coeFn_finsetSum Finset.univ _).symm

theorem inverseGradientL1_memLp (hp : p ≠ ∞)
    (k : Fin 3 → Test) (H : Fin 3 → OneSpace) :
    MemLp (inverseGradientL1 k H : V → ℂ) p volume :=
  (Lp.memLp (inverseGradientLp hp k H)).ae_eq
    (inverseGradientL1_coe_ae_lp hp k H).symm

theorem inverseGradientL1_toLp_eq (hp : p ≠ ∞)
    (k : Fin 3 → Test) (H : Fin 3 → OneSpace) :
    (inverseGradientL1_memLp hp k H).toLp (inverseGradientL1 k H : V → ℂ) =
      inverseGradientLp hp k H := by
  apply Lp.ext
  exact (inverseGradientL1_memLp hp k H).coeFn_toLp.trans
    (inverseGradientL1_coe_ae_lp hp k H)

/-- Quantitative control is inherited from the actual native Young norm bound. -/
theorem inverseGradientLp_norm (hp : p ≠ ∞)
    (k : Fin 3 → Test) (H : Fin 3 → OneSpace) :
    ‖inverseGradientLp hp k H‖ ≤ ∑ j : Fin 3, ‖(k j).toLp p volume‖ * ‖H j‖ := by
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => youngValue_norm _ _)

/-- The bound concerns the Lp realization of the same canonical L1 function. -/
theorem inverseGradientL1_toLp_norm (hp : p ≠ ∞)
    (k : Fin 3 → Test) (H : Fin 3 → OneSpace) :
    ‖(inverseGradientL1_memLp hp k H).toLp (inverseGradientL1 k H : V → ℂ)‖ ≤
      ∑ j : Fin 3, ‖(k j).toLp p volume‖ * ‖H j‖ := by
  rw [inverseGradientL1_toLp_eq]
  exact inverseGradientLp_norm hp k H

/-- Actual annular inverse-gradient OneSpace belongs to every finite Lp, p ≥ 1. -/
theorem annularL1Value_memLp (hp : p ≠ ∞) (q : Cutoff) {L : ℝ} (hL : 0 < L)
    (H : Fin 3 → OneSpace) :
    MemLp (annularL1Value q hL H : V → ℂ) p volume :=
  inverseGradientL1_memLp hp (inverseKernel q hL) H

/-- Actual enlarged-annular OneSpace has the same additional finite-p domain. -/
theorem enlargedAnnularL1Value_memLp (hp : p ≠ ∞) (q : Cutoff) {L : ℝ} (hL : 0 < L)
    (H : Fin 3 → OneSpace) :
    MemLp (enlargedAnnularL1Value q hL H : V → ℂ) p volume := by
  let A := annularL1Value q (by positivity : 0 < 2 * L) H
  let B := annularL1Value q hL H
  let C := annularL1Value q (by positivity : 0 < L / 2) H
  have hA : MemLp (A : V → ℂ) p volume := annularL1Value_memLp hp q _ H
  have hB : MemLp (B : V → ℂ) p volume := annularL1Value_memLp hp q _ H
  have hC : MemLp (C : V → ℂ) p volume := annularL1Value_memLp hp q _ H
  have hAB : MemLp ((A + B : OneSpace) : V → ℂ) p volume :=
    (hA.add hB).ae_eq (Lp.coeFn_add A B).symm
  exact (hAB.add hC).ae_eq (Lp.coeFn_add (A + B) C).symm

/-- Explicit 6/5 specialization for subsequent Hartree highpass estimates. -/
theorem annularL1Value_memLp_six_fifths (q : Cutoff) {L : ℝ} (hL : 0 < L)
    (H : Fin 3 → OneSpace) :
    MemLp (annularL1Value q hL H : V → ℂ) sourceExponent volume :=
  annularL1Value_memLp (by simp [sourceExponent]) q hL H

/-- The enlarged canonical L1 value itself, not a replacement distribution. -/
theorem enlargedAnnularL1Value_memLp_six_fifths (q : Cutoff) {L : ℝ} (hL : 0 < L)
    (H : Fin 3 → OneSpace) :
    MemLp (enlargedAnnularL1Value q hL H : V → ℂ) sourceExponent volume :=
  enlargedAnnularL1Value_memLp (by simp [sourceExponent]) q hL H

end HartreeF.AnnularL1
