import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
namespace HartreeF.EnergyTrapping
open Set

/-- Scalar consequence of the normalized sharp inequality. This is an
internal algebra lemma, not an external Hartree analytical interface. -/
theorem interaction_le_kinetic {p G A D : ℝ} (hp : 1 < p) (hG : 0 < G)
    (hA : 0 ≤ A) (hAG : A ≤ G) (hD : D ≤ G^(1-p) * A^p) : D ≤ A := by
  by_cases hz : A = 0
  · simpa [hz, Real.zero_rpow (by linarith : p ≠ 0)] using hD
  have hAp : 0 < A := lt_of_le_of_ne hA (Ne.symm hz)
  have hpow : A^p = A * A^(p-1) := by
    calc
      A^p = A^(1+(p-1)) := by congr 1; ring
      _ = A^1 * A^(p-1) := Real.rpow_add hAp _ _
      _ = A * A^(p-1) := by rw [Real.rpow_one]
  have hcancel : G^(1-p) * G^(p-1) = 1 := by
    rw [← Real.rpow_add hG]
    ring_nf
    exact Real.rpow_zero G
  calc
    D ≤ G^(1-p) * A^p := hD
    _ = A * (G^(1-p) * A^(p-1)) := by rw [hpow]; ring
    _ ≤ A * (G^(1-p) * G^(p-1)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow hA hAG (by linarith)) (Real.rpow_nonneg hG.le _)) hA
    _ = A := by rw [hcancel, mul_one]

/-- Below the sharp kinetic level, the conserved energy controls the kinetic
quantity with the exact factor 2p/(p-1), without dividing by A. -/
theorem kinetic_le_energy {p G A D E : ℝ} (hp : 1 < p) (hG : 0 < G)
    (hA : 0 ≤ A) (hAG : A ≤ G) (hD : D ≤ G^(1-p) * A^p)
    (hE : E = A/2 - D/(2*p)) : A ≤ (2*p/(p-1))*E := by
  have hDA := interaction_le_kinetic hp hG hA hAG hD
  have hpp : 0 < p := by linarith
  have he : (p-1)*A ≤ 2*p*E := by
    have hid : (2*p)*E = p*A-D := by rw [hE]; field_simp
    nlinarith
  have hdiv : A ≤ (2*p*E)/(p-1) :=
    (le_div_iff₀ (by linarith : 0 < p-1)).mpr (by nlinarith [he])
  calc
    A ≤ (2*p*E)/(p-1) := hdiv
    _ = (2*p/(p-1))*E := by ring

/-- A continuous scalar quantity on a connected interval cannot cross a
forbidden level from a strict initial inequality. -/
theorem below_of_no_level {I : Set ℝ} (hI : OrdConnected I) {A : ℝ → ℝ}
    (hA : ContinuousOn A I) {s t G : ℝ} (hs : s ∈ I) (ht : t ∈ I)
    (hinit : A s < G) (hlevel : ∀ r ∈ I, A r ≠ G) : A t < G := by
  by_contra hnot
  have hGt : G ≤ A t := le_of_not_gt hnot
  rcases le_total s t with hst | hts
  · have hsub : Icc s t ⊆ I := hI.out' hs ht
    obtain ⟨r, hr, he⟩ := intermediate_value_Icc hst (hA.mono hsub) ⟨hinit.le, hGt⟩
    exact hlevel r (hsub hr) he
  · have hsub : Icc t s ⊆ I := hI.out' ht hs
    obtain ⟨r, hr, he⟩ := intermediate_value_Icc' hts (hA.mono hsub) ⟨hinit.le, hGt⟩
    exact hlevel r (hsub hr) he

/-- Quantitative trapping from continuity, the normalized sharp bound, and
one conserved real energy. All three are internal inputs to this scalar
consumer and must later be produced for the actual Hartree trajectory. -/
theorem sharp_energy_trapping {I : Set ℝ} (hI : OrdConnected I)
    {A D : ℝ → ℝ} (hcont : ContinuousOn A I) {p G E s : ℝ}
    (hp : 1 < p) (hG : 0 < G) (hs : s ∈ I) (hinit : A s < G)
    (hA : ∀ t ∈ I, 0 ≤ A t)
    (hD : ∀ t ∈ I, D t ≤ G^(1-p) * (A t)^p)
    (hE : ∀ t ∈ I, E = A t/2 - D t/(2*p))
    (hgap : E < ((p-1)/(2*p))*G) :
    ∀ t ∈ I, A t ≤ (2*p/(p-1))*E ∧ (2*p/(p-1))*E < G := by
  have hpp : 0 < p := by linarith
  have hfactor : (2*p/(p-1))*E < G := by
    have hmul := (lt_div_iff₀ (by positivity : 0 < 2*p)).mp
      (show E < ((p-1)*G)/(2*p) by simpa only [div_mul_eq_mul_div] using hgap)
    rw [div_mul_eq_mul_div]
    apply (div_lt_iff₀ (by linarith : 0 < p-1)).mpr
    nlinarith
  have hlevel : ∀ t ∈ I, A t ≠ G := by
    intro t ht heq
    have h := kinetic_le_energy hp hG (hA t ht) heq.le (hD t ht) (hE t ht)
    rw [heq] at h
    exact (not_lt_of_ge h) hfactor
  intro t ht
  exact ⟨kinetic_le_energy hp hG (hA t ht)
    (below_of_no_level hI hcont hs ht hinit hlevel).le (hD t ht) (hE t ht), hfactor⟩

#print axioms interaction_le_kinetic
#print axioms kinetic_le_energy
#print axioms below_of_no_level
#print axioms sharp_energy_trapping
end HartreeF.EnergyTrapping
