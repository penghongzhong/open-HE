import F121PointwiseNormalization

/-! Exact relative frames used by Theorem 5.8. All identities concern the
actual homogeneous energy state, with physical scale r/a. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
open Set
namespace HartreeF.Paper121RelativeNormalization
open EnergySpace CriticalAffine Paper121AffineClosed

theorem normalize_rescaled_state {a r : ℝ} (ha : 0 < a) (hr : 0 < r)
    (y x : Space) (u : EnergyState) :
    (criticalAffineState (r/a) (div_pos hr ha) (a⁻¹ • (x-y))).symm
      ((criticalAffineState a ha y).symm u) =
        (criticalAffineState r hr x).symm u := by
  rw [criticalAffineState_symm_eq_affineState,
    criticalAffineState_symm_eq_affineState,
    criticalAffineState_symm_eq_affineState, affineState_comp]
  have hs : a * (r/a) = r := by field_simp
  have hx : a • (a⁻¹ • (x-y)) + y = x := by
    rw [smul_smul, mul_inv_cancel₀ ha.ne', one_smul]
    abel
  simp only [hs, hx]

theorem rescaled_state_mem_bounded_carrier {a r B : ℝ}
    (ha : 0 < a) (hr : 0 < r) (y x : Space) (u : EnergyState)
    {K : Set EnergyState}
    (hu : (criticalAffineState r hr x).symm u ∈ K) (hB : r/a ≤ B) :
    (criticalAffineState a ha y).symm u ∈ boundedAffineCarrier K B := by
  refine ⟨(criticalAffineState r hr x).symm u, hu, r/a, div_pos hr ha,
    a⁻¹ • (x-y), hB, ?_⟩
  apply (criticalAffineState (r/a) (div_pos hr ha) (a⁻¹ • (x-y))).symm.injective
  rw [LinearIsometryEquiv.symm_apply_apply]
  exact normalize_rescaled_state ha hr y x u

theorem rescaled_compact_normalization
    (v : ℝ → EnergyState) (r : ℝ → ℝ) (hr : ∀ t, 0 < r t)
    (x : ℝ → Space) {Q : Set EnergyState} (hQ : IsCompact Q)
    (hn : ∀ t, (criticalAffineState (r t) (hr t) (x t)).symm (v t) ∈ Q)
    {a : ℝ} (ha : 0 < a) :
    let w := fun t => (criticalAffineState a ha 0).symm (v (a^2*t))
    IsCompact (closure {q : EnergyState | ∃ t : ℝ,
      q = (criticalAffineState (r (a^2*t)/a) (div_pos (hr _) ha)
        (a⁻¹ • x (a^2*t))).symm (w t)}) := by
  intro w
  apply hQ.of_isClosed_subset isClosed_closure
  apply closure_minimal _ hQ.isClosed
  rintro q ⟨t, rfl⟩
  have he := normalize_rescaled_state ha (hr (a^2*t)) 0 (x (a^2*t)) (v (a^2*t))
  simpa only [sub_zero] using he.symm ▸ hn (a^2*t)

end HartreeF.Paper121RelativeNormalization
