import StationarySelfTesting
import ExactHartreeSobolevComposition

/-!
Lower bounds for every actual nonzero weak stationary state, derived from the
native self-test and native exact ordinary HLS/Sobolev composition. No optimizer
existence, sharp attainment, ground-state identification, or target lower bound
is an input. The explicit threshold is calibrated with W by a separate caller.
-/
noncomputable section
set_option autoImplicit false
open MeasureTheory
namespace HartreeF.StationarySelfTest
open SobolevStretch ForcingDomain HeatRiesz SharpOrdinary DirectionalCoercivity

/-- The normalized power bound and the actual positive Nehari value force the
kinetic value to be at least the normalization threshold. -/
theorem normalized_nehari_lower_bound {A G p : ℝ} (hA : 0 < A) (hG : 0 < G)
    (hp : 1 < p) (hbound : A ≤ G^(1-p) * A^p) : G ≤ A := by
  by_contra hnot
  have hlt : A < G := lt_of_not_ge hnot
  have hpow : A^(p-1) < G^(p-1) :=
    Real.rpow_lt_rpow hA.le hlt (by linarith)
  have hcancel : G^(1-p) * G^(p-1) = 1 := by
    rw [← Real.rpow_add hG]
    ring_nf
    rw [Real.rpow_zero]
  have hsplit : A^p = A * A^(p-1) := by
    calc
      A^p = A^((p-1)+1) := by congr 1; ring
      _ = A^(p-1) * A := Real.rpow_add_one hA.ne' _
      _ = A * A^(p-1) := mul_comm _ _
  have hstrict : G^(1-p) * A^p < A := by
    rw [hsplit]
    calc
      G^(1-p) * (A * A^(p-1)) = A * (G^(1-p) * A^(p-1)) := by ring
      _ < A * (G^(1-p) * G^(p-1)) :=
        mul_lt_mul_of_pos_left (mul_lt_mul_of_pos_left hpow
          (Real.rpow_pos_of_pos hG _)) hA
      _ = A := by rw [hcancel, mul_one]
  exact (not_lt_of_ge hbound) hstrict

/-- Almost-everywhere nontriviality and ordinary Sobolev produce positive
actual kinetic energy; a representative's isolated nonzero point is not used. -/
theorem WeakStationary.kinetic_pos {α c K : ℝ} {u : Space → ℂ}
    {GRe GIm : Space → Space} (h : WeakStationary α c u GRe GIm)
    (hSob : OrdinarySobolev K) (hnonzero : ¬ u =ᵐ[volume] 0) :
    0 < kinetic GRe GIm := by
  have hm := sixth_mass_pos h.sobolev.function_L6 hnonzero
  have hb := hSob.bound h.sobolev
  by_contra hn
  have hz : kinetic GRe GIm = 0 :=
    le_antisymm (le_of_not_gt hn) (kinetic_nonneg GRe GIm)
  rw [hz] at hb
  norm_num at hb
  linarith

/-- Actual weak stationary solutions satisfy A >= G, with the original exact
standard combined threshold; the self-test identity is produced internally. -/
theorem WeakStationary.kinetic_ge_standard_threshold {α : ℝ} {u : Space → ℂ}
    {GRe GIm : Space → Space}
    (h : WeakStationary α (standardRieszConstant α) u GRe GIm)
    (hOrd : OrdinaryHLS α (standardRieszConstant α))
    (hH : SharpOrdinaryHLS α) (hS : SharpOrdinarySobolev)
    (hDensity : OrdinaryH1Density) (hnonzero : ¬ u =ᵐ[volume] 0) :
    standardCombinedThreshold α ≤ kinetic GRe GIm := by
  have hHS := exact_normalized_hartree_sobolev hOrd hH hS
  have hb := hHS.bound h.sobolev
  rw [← h.kinetic_eq_interaction hOrd hDensity hS.ordinary] at hb
  exact normalized_nehari_lower_bound (h.kinetic_pos hS.ordinary hnonzero)
    hHS.threshold_pos (by linarith [hH.order_pos]) hb

/-- Every actual nonzero weak stationary solution has energy at least E_G.
This statement does not assume that a minimizer exists or realizes E_G. -/
theorem WeakStationary.energy_ge_standard_threshold {α : ℝ} {u : Space → ℂ}
    {GRe GIm : Space → Space}
    (h : WeakStationary α (standardRieszConstant α) u GRe GIm)
    (hOrd : OrdinaryHLS α (standardRieszConstant α))
    (hH : SharpOrdinaryHLS α) (hS : SharpOrdinarySobolev)
    (hDensity : OrdinaryH1Density) (hnonzero : ¬ u =ᵐ[volume] 0) :
    thresholdEnergy α (standardCombinedThreshold α) ≤ energy α u GRe GIm := by
  rw [h.energy_eq_thresholdEnergy hOrd hDensity hS.ordinary]
  unfold thresholdEnergy
  exact mul_le_mul_of_nonneg_left
    (h.kinetic_ge_standard_threshold hOrd hH hS hDensity hnonzero)
    (div_nonneg (by linarith [hH.order_pos]) (by linarith [hH.order_pos]))

#print axioms normalized_nehari_lower_bound
#print axioms WeakStationary.kinetic_pos
#print axioms WeakStationary.kinetic_ge_standard_threshold
#print axioms WeakStationary.energy_ge_standard_threshold
end HartreeF.StationarySelfTest
