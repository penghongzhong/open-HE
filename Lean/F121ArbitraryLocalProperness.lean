import F121AffineCompactParameters
import F121CriticalKineticBounds

/-! R8.4 Lemma 5.6, local properness for arbitrary pointwise normalizers.
The weak-disappearance assertions are not claimed by this module. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000
open Filter Set
open scoped Topology
namespace HartreeF.Paper121LocalProperness
open EnergySpace CriticalAffine StateEnergy StateSharpThreshold ForcingDomain
  HeatRiesz Paper121AffineProperness

theorem arbitrary_normalizers_bounded_on_compact_time
    {alpha Ec : ℝ} (hOrd : OrdinaryHLS alpha (standardRieszConstant alpha))
    (hEc : 0 < Ec) {J : Set ℝ} (hJ : IsCompact J)
    (u : ℝ → EnergyState) (hu : ContinuousOn u J)
    (hE : ∀ t ∈ J, totalEnergy alpha (u t) = Ec)
    (r : ℝ → ℝ) (hr : ∀ t, 0 < r t) (y : ℝ → Space)
    {Q : Set EnergyState} (hQ : IsCompact Q)
    (hnormalized : ∀ t ∈ J, (criticalAffineState (r t) (hr t) (y t)).symm (u t) ∈ Q) :
    ∃ a A X : ℝ, 0 < a ∧ 0 < A ∧ 0 ≤ X ∧
      ∀ t ∈ J, a ≤ r t ∧ r t ≤ A ∧ ‖y t‖ ≤ X := by
  have hzero : totalEnergy alpha (0 : EnergyState) = 0 := by
    simp [totalEnergy, gradientSquared, FreeTimeDecay.interactionLp_zero hOrd.order_pos]
  have hAzero : (0 : EnergyState) ∉ u '' J := by
    rintro ⟨t, ht, he⟩
    have h := hE t ht
    rw [he, hzero] at h
    exact hEc.ne h
  let B : Set EnergyState := Q ∩ {q | totalEnergy alpha q = Ec}
  have hB : IsCompact B := hQ.inter_right
    (isClosed_eq (totalEnergy_contDiff hOrd).continuous continuous_const)
  have hBzero : (0 : EnergyState) ∉ B := by
    intro hz
    have h := hz.2
    change totalEnergy alpha (0 : EnergyState) = Ec at h
    rw [hzero] at h
    exact hEc.ne h
  have hmem (t : ℝ) (ht : t ∈ J) :
      (criticalAffineState (r t) (hr t) (y t)).symm (u t) ∈ B := by
    refine ⟨hnormalized t ht, ?_⟩
    change totalEnergy alpha ((criticalAffineState (r t) (hr t) (y t)).symm (u t)) = Ec
    rw [criticalAffineState_symm_eq_affineState, affineState_totalEnergy hOrd]
    exact hE t ht
  obtain ⟨C, D, hC, hD, hbox⟩ := compact_carriers_parameter_box
    (hJ.image_of_continuousOn hu) hAzero hB hBzero
  refine ⟨1 / C, C, D, one_div_pos.mpr hC, hC, hD, ?_⟩
  intro t ht
  exact hbox (u t) ⟨t, ht, rfl⟩ (r t) (hr t) (y t) (hmem t ht)

end HartreeF.Paper121LocalProperness
