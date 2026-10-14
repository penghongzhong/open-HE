import FCompactCrossFrameSeparation
import FCompactCrossCylinder
import FOrthogonalityScaleCutoff

/-! Literal compact-seed cross potentials vanish along the whole orthogonal family.
All analytic norm bounds are derived here from the existing OrdinaryHLS interface,
compact support, and continuity; the imported scalar theorem only assembles them. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2500000
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace HartreeF.CompactCross
open ForcingDomain

theorem compact_frameCrossNorm_orthogonality {ι : Type*} {l : Filter ι}
    {α c : ℝ} (hHLS : OrdinaryHLS α c)
    {u h v k : ℝ → Space → ℂ}
    (hu : Continuous (fun q : ℝ × Space => u q.1 q.2))
    (hh : Continuous (fun q : ℝ × Space => h q.1 q.2))
    (hv : Continuous (fun q : ℝ × Space => v q.1 q.2))
    (hk : Continuous (fun q : ℝ × Space => k q.1 q.2))
    (huC : HasCompactSupport (fun q : ℝ × Space => u q.1 q.2))
    (hhC : HasCompactSupport (fun q : ℝ × Space => h q.1 q.2))
    (hvC : HasCompactSupport (fun q : ℝ × Space => v q.1 q.2))
    (hkC : HasCompactSupport (fun q : ℝ × Space => k q.1 q.2))
    {a b s r : ι → ℝ} {y z : ι → Space}
    (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (horth : Tendsto (fun i => a i/b i+b i/a i+‖y i-z i‖^2/(a i*b i)+
      |a i^2*s i-b i^2*r i|/(a i*b i)) l atTop) :
    Tendsto (fun i => frameCrossNorm α c u h v k (a i) (b i) (y i) (z i) (s i) (r i)) l (𝓝 0) := by
  obtain ⟨U,hU,huB⟩ := compact_seed_amplitude hu huC
  obtain ⟨H,hH,hhB⟩ := compact_seed_amplitude hh hhC
  obtain ⟨V,hV,hvB⟩ := compact_seed_amplitude hv hvC
  obtain ⟨K,hK,hkB⟩ := compact_seed_amplitude hk hkC
  obtain ⟨R,T,hR,hT,huS,hvS,huI,hvI⟩ := compact_pair_cylinder huC hvC
  have hSm : MeasurableSet (Metric.closedBall (0:Space) R) :=
    (isCompact_closedBall (0:Space) R).measurableSet
  have hSf : volume (Metric.closedBall (0:Space) R) ≠ ∞ :=
    (isCompact_closedBall (0:Space) R).measure_lt_top.ne
  have hIf : volume (Icc (-T) T) ≠ ∞ := isCompact_Icc.measure_lt_top.ne
  obtain ⟨Cs,hCs⟩ := box_frameCrossNorm_scale hHLS hSm hSm measurableSet_Icc measurableSet_Icc
    hSf hSf hIf hIf hU hH hV hK hu hh hv hk huB hhB hvB hkB huS hvS huI hvI
  obtain ⟨Cx,hCx⟩ := cylinder_frameCrossNorm_space hHLS (by linarith : 0 ≤ R)
    hU hH hV hK hu hh hv hk huB hhB hvB hkB huS hvS huI hvI
  apply OrthogonalityCutoff.tendsto_zero_of_scales_spatial_temporal ha hb Cs Cx
    (δ := (3-α)/4) (γ := (3-α)/2) (K := 4*R^2) (L := T)
    (by linarith [hHLS.order_lt_three]) (by linarith [hHLS.order_lt_three])
    (by positivity) (by linarith) horth
  · exact fun i => hCs (a i) (b i) (ha i) (hb i) (y i) (z i) (s i) (r i)
  · intro i hsep
    simpa only [neg_div] using hCx (a i) (b i) (ha i) (hb i) (y i) (z i) (s i) (r i) hsep
  · intro i hgap
    exact cylinder_frameCrossNorm_time hHLS.order_pos u h v k huI hvI (ha i) (hb i)
      (y i) (z i) (s i) (r i) hgap

#print axioms compact_frameCrossNorm_orthogonality
end HartreeF.CompactCross
