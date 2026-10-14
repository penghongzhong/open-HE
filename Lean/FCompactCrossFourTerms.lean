import FCompactCrossOrthogonality

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace HartreeF.CompactCross
open ForcingDomain

theorem tendsto_terms_of_frameCrossNorm {ι : Type*} {l : Filter ι} {α c : ℝ}
    {u h v k : ℝ → Space → ℂ} {a b s r : ι → ℝ} {y z : ι → Space}
    (hN : Tendsto (fun i => frameCrossNorm α c u h v k (a i) (b i) (y i) (z i) (s i) (r i)) l (𝓝 0)) :
    Tendsto (fun i => forcingNorm (innerCross α c (seedFrame (a i) (y i) (s i) (1/2) u)
      (seedFrame (a i) (y i) (s i) (3/2) h) (seedFrame (b i) (z i) (r i) (1/2) v))) l (𝓝 0) ∧
    Tendsto (fun i => forcingNorm (outerCross α c (seedFrame (a i) (y i) (s i) (1/2) u)
      (seedFrame (b i) (z i) (r i) (1/2) v) (seedFrame (b i) (z i) (r i) (3/2) k))) l (𝓝 0) := by
  constructor
  · exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hN
      (fun _ => bot_le) (fun _ => le_max_left _ _)
  · exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hN
      (fun _ => bot_le) (fun _ => le_max_right _ _)

/-- Four separate literal ENNReal L^2_t L^(6/5)_x forcing-norm limits for
orthogonal compact spacetime seeds, with both derivative placements and both
ordered pairs. The entire filter converges, without profile subsequences. -/
theorem compact_four_pure_cross_orthogonality {ι : Type*} {l : Filter ι}
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
    Tendsto (fun i => forcingNorm (innerCross α c (seedFrame (a i) (y i) (s i) (1/2) u)
      (seedFrame (a i) (y i) (s i) (3/2) h) (seedFrame (b i) (z i) (r i) (1/2) v))) l (𝓝 0) ∧
    Tendsto (fun i => forcingNorm (outerCross α c (seedFrame (a i) (y i) (s i) (1/2) u)
      (seedFrame (b i) (z i) (r i) (1/2) v) (seedFrame (b i) (z i) (r i) (3/2) k))) l (𝓝 0) ∧
    Tendsto (fun i => forcingNorm (innerCross α c (seedFrame (b i) (z i) (r i) (1/2) v)
      (seedFrame (b i) (z i) (r i) (3/2) k) (seedFrame (a i) (y i) (s i) (1/2) u))) l (𝓝 0) ∧
    Tendsto (fun i => forcingNorm (outerCross α c (seedFrame (b i) (z i) (r i) (1/2) v)
      (seedFrame (a i) (y i) (s i) (1/2) u) (seedFrame (a i) (y i) (s i) (3/2) h))) l (𝓝 0) := by
  have h1 := tendsto_terms_of_frameCrossNorm
    (compact_frameCrossNorm_orthogonality hHLS hu hh hv hk huC hhC hvC hkC ha hb horth)
  have horth' : Tendsto (fun i => b i/a i+a i/b i+‖z i-y i‖^2/(b i*a i)+
      |b i^2*r i-a i^2*s i|/(b i*a i)) l atTop := by
    have he : (fun i => b i/a i+a i/b i+‖z i-y i‖^2/(b i*a i)+
        |b i^2*r i-a i^2*s i|/(b i*a i)) =
        (fun i => a i/b i+b i/a i+‖y i-z i‖^2/(a i*b i)+
        |a i^2*s i-b i^2*r i|/(a i*b i)) := by
      funext i
      rw [norm_sub_rev (z i) (y i),abs_sub_comm (b i^2*r i) (a i^2*s i)]
      ring
    rw [he]
    exact horth
  have h2 := tendsto_terms_of_frameCrossNorm
    (compact_frameCrossNorm_orthogonality hHLS hv hk hu hh hvC hkC huC hhC hb ha horth')
  exact ⟨h1.1,h1.2,h2.1,h2.2⟩

#print axioms tendsto_terms_of_frameCrossNorm
#print axioms compact_four_pure_cross_orthogonality
end HartreeF.CompactCross
