import FCompactCrossEpsilon

/-! Compact spacetime seeds supply the pointwise data internally.
Only joint continuity and actual compact support are required. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
open MeasureTheory Set
open scoped ENNReal NNReal
namespace HartreeF.CompactCross
open ForcingDomain TimeHolder AffineMixed

theorem compact_seed_amplitude {f : ℝ → Space → ℂ}
    (hf : Continuous (fun z : ℝ × Space => f z.1 z.2))
    (hc : HasCompactSupport (fun z : ℝ × Space => f z.1 z.2)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t x, ‖f t x‖ ≤ M := by
  obtain ⟨M,hM⟩ := hf.norm.bddAbove_range_of_hasCompactSupport hc.norm
  refine ⟨max 0 M,le_max_left _ _,fun t x => ?_⟩
  exact (hM (mem_range_self (t,x))).trans (le_max_right _ _)

theorem compact_seed_supports {f : ℝ → Space → ℂ}
    (hc : HasCompactSupport (fun z : ℝ × Space => f z.1 z.2)) :
    ∃ (S : Set Space) (I : Set ℝ),
      MeasurableSet S ∧ MeasurableSet I ∧ volume S ≠ ∞ ∧ volume I ≠ ∞ ∧
      (∀ t x, x ∉ S → f t x = 0) ∧ (∀ t, t ∉ I → ∀ x, f t x = 0) := by
  have hc' : IsCompact (tsupport (fun z : ℝ × Space => f z.1 z.2)) := hc
  have hs := hc'.image continuous_snd
  have hi := hc'.image continuous_fst
  refine ⟨Prod.snd '' tsupport (fun z : ℝ × Space => f z.1 z.2),
    Prod.fst '' tsupport (fun z : ℝ × Space => f z.1 z.2),
    hs.measurableSet,hi.measurableSet,hs.measure_lt_top.ne,hi.measure_lt_top.ne,?_,?_⟩
  · intro t x hx
    apply image_eq_zero_of_notMem_tsupport (f := fun z : ℝ × Space => f z.1 z.2) (x := (t,x))
    intro htx
    exact hx ⟨(t,x),htx,rfl⟩
  · intro t ht x
    apply image_eq_zero_of_notMem_tsupport (f := fun z : ℝ × Space => f z.1 z.2) (x := (t,x))
    intro htx
    exact ht ⟨(t,x),htx,rfl⟩

/-- Native compact-seed scale-separated pure-cross estimate for every 0<alpha<3.
The constant is finite and independent of epsilon and both relative centers.
The directional fields may be the actual derivatives of smooth compact seeds,
but no derivative relation is needed for this stronger four-field theorem. -/
theorem compact_pure_cross_epsilon_decay {α c : ℝ} (hHLS : OrdinaryHLS α c)
    {u h v k : ℝ → Space → ℂ}
    (hu : Continuous (fun z : ℝ × Space => u z.1 z.2))
    (hh : Continuous (fun z : ℝ × Space => h z.1 z.2))
    (hv : Continuous (fun z : ℝ × Space => v z.1 z.2))
    (hk : Continuous (fun z : ℝ × Space => k z.1 z.2))
    (huC : HasCompactSupport (fun z : ℝ × Space => u z.1 z.2))
    (hhC : HasCompactSupport (fun z : ℝ × Space => h z.1 z.2))
    (hvC : HasCompactSupport (fun z : ℝ × Space => v z.1 z.2))
    (hkC : HasCompactSupport (fun z : ℝ × Space => k z.1 z.2)) :
    ∃ C : ℝ≥0, ∀ (ε : ℝ), 0 < ε → ε ≤ 1 → ∀ (b : Space) (d : ℝ),
      forcingNorm (innerCross α c (parabolicField ε⁻¹ b d (1/2) u)
        (parabolicField ε⁻¹ b d (3/2) h) v) ≤ (C : ℝ≥0∞) * ENNReal.ofReal (ε^((3-α)/4)) ∧
      forcingNorm (outerCross α c (parabolicField ε⁻¹ b d (1/2) u) v k) ≤
        (C : ℝ≥0∞) * ENNReal.ofReal (ε^((3-α)/4)) ∧
      forcingNorm (innerCross α c v k (parabolicField ε⁻¹ b d (1/2) u)) ≤
        (C : ℝ≥0∞) * ENNReal.ofReal (ε^((3-α)/4)) ∧
      forcingNorm (outerCross α c v (parabolicField ε⁻¹ b d (1/2) u)
        (parabolicField ε⁻¹ b d (3/2) h)) ≤ (C : ℝ≥0∞) * ENNReal.ofReal (ε^((3-α)/4)) := by
  obtain ⟨U,hU,huB⟩ := compact_seed_amplitude hu huC
  obtain ⟨H,hH,hhB⟩ := compact_seed_amplitude hh hhC
  obtain ⟨V,hV,hvB⟩ := compact_seed_amplitude hv hvC
  obtain ⟨K,hK,hkB⟩ := compact_seed_amplitude hk hkC
  obtain ⟨S,I,hS,hI,hSf,hIf,huS,huI⟩ := compact_seed_supports huC
  obtain ⟨T,_,hT,_,hTf,_,hvT,_⟩ := compact_seed_supports hvC
  exact box_pure_cross_epsilon_decay hHLS hS hT hI hSf hTf hIf hU hH hV hK
    hu hh hv hk huB hhB hvB hkB huS hvT huI

#print axioms compact_seed_amplitude
#print axioms compact_seed_supports
#print axioms compact_pure_cross_epsilon_decay
end HartreeF.CompactCross
