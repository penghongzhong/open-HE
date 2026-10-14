import FCompactCrossSeeds

noncomputable section
set_option autoImplicit false
set_option warningAsError true
open MeasureTheory Set
namespace HartreeF.CompactCross

/-- Actual compact spacetime support is enclosed in a finite centered cylinder. -/
theorem compact_seed_cylinder {f : ℝ → Space → ℂ}
    (hc : HasCompactSupport (fun q : ℝ × Space => f q.1 q.2)) :
    ∃ R T : ℝ, 1 ≤ R ∧ 1 ≤ T ∧
      (∀ t x, x ∉ Metric.closedBall 0 R → f t x = 0) ∧
      (∀ t, t ∉ Icc (-T) T → ∀ x, f t x = 0) := by
  have hc' : IsCompact (tsupport (fun q : ℝ × Space => f q.1 q.2)) := hc
  obtain ⟨R,hR,hRS⟩ := (hc'.image continuous_snd).isBounded.subset_closedBall_lt 1 0
  obtain ⟨T,hT,hTI⟩ := (hc'.image continuous_fst).isBounded.subset_closedBall_lt 1 0
  refine ⟨R,T,hR.le,hT.le,?_,?_⟩
  · intro t x hx
    apply image_eq_zero_of_notMem_tsupport (f := fun q : ℝ × Space => f q.1 q.2) (x := (t,x))
    intro htx
    exact hx (hRS ⟨(t,x),htx,rfl⟩)
  · intro t ht x
    apply image_eq_zero_of_notMem_tsupport (f := fun q : ℝ × Space => f q.1 q.2) (x := (t,x))
    intro htx
    apply ht
    have hmem := hTI ⟨(t,x),htx,rfl⟩
    simpa only [Metric.mem_closedBall,Real.dist_eq,sub_zero,abs_le,mem_Icc] using hmem

/-- Two compact seeds share one fixed cylinder; no scale-dependent enclosure. -/
theorem compact_pair_cylinder {u v : ℝ → Space → ℂ}
    (hu : HasCompactSupport (fun q : ℝ × Space => u q.1 q.2))
    (hv : HasCompactSupport (fun q : ℝ × Space => v q.1 q.2)) :
    ∃ R T : ℝ, 1 ≤ R ∧ 1 ≤ T ∧
      (∀ t x, x ∉ Metric.closedBall 0 R → u t x = 0) ∧
      (∀ t x, x ∉ Metric.closedBall 0 R → v t x = 0) ∧
      (∀ t, t ∉ Icc (-T) T → ∀ x, u t x = 0) ∧
      (∀ t, t ∉ Icc (-T) T → ∀ x, v t x = 0) := by
  obtain ⟨R,T,hR,hT,huS,huI⟩ := compact_seed_cylinder hu
  obtain ⟨R',T',hR',hT',hvS,hvI⟩ := compact_seed_cylinder hv
  refine ⟨max R R',max T T',hR.trans (le_max_left _ _),hT.trans (le_max_left _ _),?_,?_,?_,?_⟩
  · intro t x hx
    exact huS t x (fun hs => hx (Metric.closedBall_subset_closedBall (le_max_left _ _) hs))
  · intro t x hx
    exact hvS t x (fun hs => hx (Metric.closedBall_subset_closedBall (le_max_right _ _) hs))
  · intro t ht
    apply huI t
    intro hs
    exact ht ⟨(neg_le_neg (le_max_left T T')).trans hs.1,hs.2.trans (le_max_left _ _)⟩
  · intro t ht
    apply hvI t
    intro hs
    exact ht ⟨(neg_le_neg (le_max_right T T')).trans hs.1,hs.2.trans (le_max_right _ _)⟩

#print axioms compact_seed_cylinder
#print axioms compact_pair_cylinder
end HartreeF.CompactCross
