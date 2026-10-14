import FWeakGradientEnergyDual
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.Topology.MetricSpace.Cauchy

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1500000
open MeasureTheory Filter Set
open scoped ENNReal Topology RealInnerProductSpace
namespace HartreeF.LocalRellich
open EnergySpace SobolevStretch

/-- Ordinary scalar Rellich compactness on a positive-radius three-dimensional
ball. This is the H1(B_R) -> L2(B_R) specialization of Brezis (2011), Theorem
9.16, p.285, and Hunter (1996), Theorem 3.7(a), p.44. The globally defined weak
gradient is a stronger hypothesis than the textbook local weak gradient.
The conclusion is only sequential precompactness in the scalar ball L2 norm.
It contains no named limit, EnergyState, a.e. extraction, or Hartree statement. -/
structure OrdinaryRellichBall : Prop where
  compact : ∀ (R : ℝ), 0 < R → ∀ (v : ℕ → Space → ℝ) (G : ℕ → Space → Space),
    (∀ n, HasWeakGradient (v n) (G n)) →
    ∀ (hv : ∀ n, MemLp (v n) 2 (volume.restrict (Metric.ball 0 R))),
    (∀ n, MemLp (G n) 2 (volume.restrict (Metric.ball 0 R))) →
    (∃ B : ℝ, ∀ n,
      (eLpNorm (v n) 2 (volume.restrict (Metric.ball 0 R))).toReal +
      (eLpNorm (G n) 2 (volume.restrict (Metric.ball 0 R))).toReal ≤ B) →
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ CauchySeq (fun n => (hv (σ n)).toLp (v (σ n)))

/-- Native support localization: the ordinary ball conclusion controls the
full-space scalar L2 sequence when its literal support lies in that ball. -/
theorem rellich_supported_cauchy (hRel : OrdinaryRellichBall)
    {R : ℝ} (hR : 0 < R) {v : ℕ → Space → ℝ} {G : ℕ → Space → Space}
    (hw : ∀ n, HasWeakGradient (v n) (G n))
    (hv : ∀ n, MemLp (v n) 2 volume) (hG : ∀ n, MemLp (G n) 2 volume)
    (hs : ∀ n, Function.support (v n) ⊆ Metric.ball 0 R)
    (hb : ∃ B : ℝ, ∀ n, (eLpNorm (v n) 2 volume).toReal +
      (eLpNorm (G n) 2 volume).toReal ≤ B) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ CauchySeq (fun n => (hv (σ n)).toLp (v (σ n))) := by
  have hv' (n) := (hv n).restrict (Metric.ball 0 R)
  have hG' (n) := (hG n).restrict (Metric.ball 0 R)
  have hb' : ∃ B : ℝ, ∀ n,
      (eLpNorm (v n) 2 (volume.restrict (Metric.ball 0 R))).toReal +
      (eLpNorm (G n) 2 (volume.restrict (Metric.ball 0 R))).toReal ≤ B := by
    obtain ⟨B,hB⟩ := hb
    refine ⟨B, fun n => (add_le_add ?_ ?_).trans (hB n)⟩
    · exact ENNReal.toReal_mono (hv n).eLpNorm_ne_top (eLpNorm_restrict_le _ _ _ _)
    · exact ENNReal.toReal_mono (hG n).eLpNorm_ne_top (eLpNorm_restrict_le _ _ _ _)
  obtain ⟨σ,hσ,hc⟩ := hRel.compact R hR v G hw hv' hG' hb'
  refine ⟨σ,hσ, Metric.cauchySeq_iff.mpr ?_⟩
  intro ε hε
  obtain ⟨N,hN⟩ := Metric.cauchySeq_iff.mp hc ε hε
  refine ⟨N, fun m hm n hn => ?_⟩
  have he : eLpNorm (v (σ m) - v (σ n)) 2 (volume.restrict (Metric.ball 0 R)) =
      eLpNorm (v (σ m) - v (σ n)) 2 volume := by
    apply eLpNorm_restrict_eq_of_support_subset ((hv (σ m)).sub (hv (σ n))).aestronglyMeasurable
    exact (Function.support_sub _ _).trans (union_subset (hs _) (hs _))
  have hd := hN m hm n hn
  simp only [dist_eq_norm, ← MemLp.toLp_sub, Lp.norm_toLp] at hd ⊢
  rwa [he] at hd

#print axioms OrdinaryRellichBall
#print axioms rellich_supported_cauchy
end HartreeF.LocalRellich
