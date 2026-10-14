import FEnergySmoothApproximation

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000
open MeasureTheory Filter Set
open scoped ENNReal RealInnerProductSpace Topology
namespace HartreeF.EnergySpace
open SobolevStretch StationarySelfTest CutoffApproximation

/-- The actual weak cutoff state; its value is not required to have been L2. -/
def cutoffEnergyState (u : EnergyState) (n : ℕ) : EnergyState :=
  inDotEnergyState ((inDotH1_cutoff_approximation (energyState_inDotH1 u)).1 n).2

theorem cutoffEnergyState_tendsto {K : ℝ} (hSob : OrdinarySobolev K) (u : EnergyState) :
    Tendsto (cutoffEnergyState u) atTop (𝓝 u) := by
  have h := inDotH1_cutoff_approximation (energyState_inDotH1 u)
  have ht := inDotEnergyState_tendsto hSob (energyState_inDotH1 u)
    (fun n => (h.1 n).2) h.2.2.1 h.2.2.2
  rw [inDotEnergyState_roundtrip] at ht
  exact ht

/-- Each cutoff can be approximated by genuine smooth states using only ordinary H1 density. -/
theorem cutoffEnergyState_smooth_approximation (hDensity : OrdinaryH1Density)
    {K : ℝ} (hSob : OrdinarySobolev K) (u : EnergyState) (n : ℕ) :
    ∃ φ : ℕ → CompactSmoothReal × CompactSmoothReal,
      Tendsto (fun m => compactSmoothState (φ m)) atTop (𝓝 (cutoffEnergyState u n)) := by
  have h := (inDotH1_cutoff_approximation (energyState_inDotH1 u)).1 n
  exact h1_compactSmoothState_approximation hDensity hSob h.2 h.1

/-- A true diagonal choice in the graph metric. One index selects the whole state,
so its value and both weak gradients always use the same approximant. -/
theorem compactSmoothState_diagonal (hDensity : OrdinaryH1Density)
    {K : ℝ} (hSob : OrdinarySobolev K) (u : EnergyState) :
    ∃ φ : ℕ → ℕ → CompactSmoothReal × CompactSmoothReal, ∃ d : ℕ → ℕ,
      (∀ n, Tendsto (fun m => compactSmoothState (φ n m)) atTop
        (𝓝 (cutoffEnergyState u n))) ∧
      (∀ n, dist (compactSmoothState (φ n (d n))) (cutoffEnergyState u n) <
        1 / ((n : ℝ) + 1)) ∧
      Tendsto (fun n => compactSmoothState (φ n (d n))) atTop (𝓝 u) := by
  choose φ hφ using cutoffEnergyState_smooth_approximation hDensity hSob u
  have he (n : ℕ) : ∃ m : ℕ,
      dist (compactSmoothState (φ n m)) (cutoffEnergyState u n) < 1 / ((n : ℝ) + 1) := by
    have ht := (Metric.tendsto_nhds.mp (hφ n)) (1 / ((n : ℝ) + 1)) (by positivity)
    exact ht.exists
  choose d hd using he
  refine ⟨φ, d, hφ, hd, ?_⟩
  apply tendsto_iff_dist_tendsto_zero.mpr
  have hc := tendsto_iff_dist_tendsto_zero.mp (cutoffEnergyState_tendsto hSob u)
  have hb : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1) + dist (cutoffEnergyState u n) u)
      atTop (𝓝 0) := by
    simpa only [zero_add] using tendsto_one_div_add_atTop_nhds_zero_nat.add hc
  exact squeeze_zero (fun n => dist_nonneg)
    (fun n => (dist_triangle _ _ _).trans (add_le_add (hd n).le le_rfl)) hb

/-- Native homogeneous smooth approximation in the actual C43 Banach topology. -/
theorem compactSmoothState_approximation (hDensity : OrdinaryH1Density)
    {K : ℝ} (hSob : OrdinarySobolev K) (u : EnergyState) :
    ∃ φ : ℕ → CompactSmoothReal × CompactSmoothReal,
      Tendsto (fun n => compactSmoothState (φ n)) atTop (𝓝 u) := by
  obtain ⟨φ, d, _, _, ht⟩ := compactSmoothState_diagonal hDensity hSob u
  exact ⟨fun n => φ n (d n), ht⟩

/-- The smooth-state constructor has genuinely dense range in C43, not a density premise. -/
theorem compactSmoothState_denseRange (hDensity : OrdinaryH1Density)
    {K : ℝ} (hSob : OrdinarySobolev K) : DenseRange compactSmoothState := by
  intro u
  obtain ⟨φ, hφ⟩ := compactSmoothState_approximation hDensity hSob u
  exact mem_closure_of_tendsto hφ (Eventually.of_forall (fun n => mem_range_self (φ n)))

end HartreeF.EnergySpace
