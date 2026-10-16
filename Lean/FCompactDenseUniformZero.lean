import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 600000
open Filter Set
open scoped Topology
namespace HartreeF.CompactOrbitTerminal

/-- A finite net from the specified dense family gives uniform zero on any actual
compact carrier for a uniformly Lipschitz family. No moving-test limit is assumed. -/
theorem compact_dense_uniform_zero
    {ι A E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    {l : Filter ι} {d : A → E} (hd : DenseRange d)
    (P : ι → E → F) {C : ℝ} (hC : 0 ≤ C)
    (hLip : ∀ i x y, ‖P i x - P i y‖ ≤ C * ‖x-y‖)
    (hz : ∀ a, Tendsto (fun i => P i (d a)) l (𝓝 0))
    {K : Set E} (hK : IsCompact K) (u : ι → E)
    (hu : ∀ᶠ i in l, u i ∈ K) :
    Tendsto (fun i => P i (u i)) l (𝓝 0) := by
  classical
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let δ : ℝ := ε / (2*(C+1))
  have hCp : 0 < C+1 := by linarith
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδeq : (C+1)*δ = ε/2 := by
    dsimp [δ]
    field_simp
  have hCd : C*δ < ε/2 := by nlinarith
  have hcover : K ⊆ ⋃ a : A, Metric.ball (d a) δ := by
    intro x _
    obtain ⟨a, ha⟩ := hd.exists_dist_lt x hδ
    exact mem_iUnion.mpr ⟨a, ha⟩
  obtain ⟨net, hnet⟩ := hK.elim_finite_subcover
    (fun a : A => Metric.ball (d a) δ) (fun _ => Metric.isOpen_ball) hcover
  have hsmall : ∀ a ∈ net, ∀ᶠ i in l, ‖P i (d a)‖ < ε/2 := by
    intro a _
    simpa only [dist_zero_right] using
      Metric.tendsto_nhds.mp (hz a) (ε/2) (by positivity)
  have hall : ∀ᶠ i in l, ∀ a ∈ net, ‖P i (d a)‖ < ε/2 :=
    (Filter.eventually_all_finset net).mpr hsmall
  filter_upwards [hu, hall] with i hui hi
  obtain ⟨a, ha, hua⟩ := mem_iUnion₂.mp (hnet hui)
  have hdist : ‖u i - d a‖ < δ := by simpa only [Metric.mem_ball, dist_eq_norm] using hua
  have he : ‖P i (u i) - P i (d a)‖ < ε/2 :=
    (hLip i (u i) (d a)).trans_lt
      ((mul_le_mul_of_nonneg_left hdist.le hC).trans_lt hCd)
  rw [dist_zero_right]
  calc
    ‖P i (u i)‖ = ‖(P i (u i)-P i (d a))+P i (d a)‖ := by rw [sub_add_cancel]
    _ ≤ ‖P i (u i)-P i (d a)‖+‖P i (d a)‖ := norm_add_le _ _
    _ < ε/2+ε/2 := add_lt_add he (hi a ha)
    _ = ε := by ring

/-- The fixed-point dense-extension consequence uses the same proved finite-net lemma. -/
theorem dense_uniform_lipschitz_zero
    {ι A E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    {l : Filter ι} {d : A → E} (hd : DenseRange d)
    (P : ι → E → F) {C : ℝ} (hC : 0 ≤ C)
    (hLip : ∀ i x y, ‖P i x - P i y‖ ≤ C * ‖x-y‖)
    (hz : ∀ a, Tendsto (fun i => P i (d a)) l (𝓝 0)) (x : E) :
    Tendsto (fun i => P i x) l (𝓝 0) :=
  compact_dense_uniform_zero hd P hC hLip hz isCompact_singleton
    (fun _ => x) (Filter.Eventually.of_forall (fun _ => mem_singleton x))

end HartreeF.CompactOrbitTerminal
