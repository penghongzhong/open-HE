import FCompactLpExhaustion
import FPaperStabilitySumNorm

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory Filter Set
open scoped ENNReal Topology
namespace HartreeF.IntervalNormExhaustion
open EnergySpace CriticalPathSpace IntervalTimeTransport CriticalJointSources
open CriticalSourceBounds TimeHolder EndpointOutput HomogeneousStability
attribute [local irreducible] energySubmodule criticalPathSubmodule energyPath
  jointComplexGradient CriticalJointSources.jointFields

/-- One actual global Euclidean-gradient field is constructed from the same
compact paths. The statement is used at (p,r)=(10,30/13) and (2,6), sharing one
proof and preserving the exact bound rather than converting via coordinates. -/
theorem exists_actual_global_vector_gradient_of_compact_with_slices
    (p r : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ r)] [Fact (r ≠ ∞)]
    {C : ℝ} (hC : 0 ≤ C)
    (a b : ℕ → ℝ) (ha : Antitone a) (hb : Monotone b) (hab : ∀ n, a n ≤ b n)
    (q : ℝ → EnergyState) (Q : ∀ n, CriticalPath (intervalMeasure (a n) (b n)))
    (hQ : ∀ n (t : Icc (a n) (b n)), energyPath _ (Q n) t=q t)
    (hcap : ∀ n, mixedNorm (intervalMeasure (a n) (b n)) volume p r
      (fun t => energyComplexGradient (energyPath _ (Q n) t)) ≤ ENNReal.ofReal C)
    (hactualSlices : ∀ n, ∀ᵐ t ∂intervalMeasure (a n) (b n),
      MemLp (energyComplexGradient (energyPath _ (Q n) t)) r volume) :
    ∃ F : Lp (Lp (EuclideanSpace ℂ (Fin 3)) r (volume : Measure Space)) p (volume : Measure ℝ),
      ‖F‖ ≤ C ∧
      (∀ᵐ t ∂volume.restrict (⋃ n, Icc (a n) (b n)),
        (F t : Space → EuclideanSpace ℂ (Fin 3)) =ᵐ[volume] energyComplexGradient (q t)) ∧
      (∀ᵐ t ∂volume, t ∉ ⋃ n, Icc (a n) (b n) → F t=0) := by
  have heq (n : ℕ) : mixedNorm (intervalMeasure (a n) (b n)) volume p r
      (jointComplexGradient (Q n)) = mixedNorm (intervalMeasure (a n) (b n)) volume p r
        (fun t => energyComplexGradient (energyPath _ (Q n) t)) := by
    apply eLpNorm_congr_ae
    filter_upwards [jointComplexGradient_slice_eq (Q n)] with t ht
    exact eLpNorm_congr_ae ht
  have hfinite (n : ℕ) : mixedNorm (intervalMeasure (a n) (b n)) volume p r
      (jointComplexGradient (Q n)) ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top ((heq n).le.trans (hcap n))
  have hslices (n : ℕ) : ∀ᵐ t ∂intervalMeasure (a n) (b n),
      MemLp (jointComplexGradient (Q n) t) r volume := by
    filter_upwards [hactualSlices n,jointComplexGradient_slice_eq (Q n)] with t ht he
    exact (memLp_congr_ae he).mpr ht
  let field (n : ℕ) := jointLpRealization (intervalMeasure (a n) (b n)) volume p r
    (fun z => jointComplexGradient (Q n) z.1 z.2) (jointComplexGradient_joint (Q n))
    (hslices n) (hfinite n)
  let localField (n : ℕ) := toLocalLp (hab n) p (field n)
  have hnorm (n : ℕ) : ‖localField n‖ ≤ C := by
    rw [show ‖localField n‖=‖field n‖ from toLocalLp_norm (hab n) p (field n)]
    change ‖jointLpRealization _ _ _ _ _ _ _ _‖ ≤ C
    rw [jointLpRealization_norm]
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top
      ((heq n).le.trans (hcap n))).trans_eq (ENNReal.toReal_ofReal hC)
  have hactual (n : ℕ) : ∀ᵐ t ∂localMeasure (a n) (b n),
      (localField n t : Space → EuclideanSpace ℂ (Fin 3)) =ᵐ[volume]
        energyComplexGradient (q t) := by
    have hrep : ∀ᵐ t ∂intervalMeasure (a n) (b n),
        (field n t : Space → EuclideanSpace ℂ (Fin 3)) =ᵐ[volume]
          jointComplexGradient (Q n) t := jointLpRealization_coeFn (intervalMeasure (a n) (b n)) volume p r
      (fun z => jointComplexGradient (Q n) z.1 z.2) (jointComplexGradient_joint (Q n))
      (hslices n) (hfinite n)
    filter_upwards [toLocalLp_nested_coeFn (hab n) p r volume (field n),
      ae_clamp (hab n) hrep,ae_clamp (hab n) (jointComplexGradient_slice_eq (Q n)),
      ae_restrict_mem measurableSet_Icc] with t hl hj he ht
    have hstate : energyPath _ (Q n) (Set.projIcc (a n) (b n) (hab n) t)=q t :=
      (hQ n _).trans (congrArg (fun v : Icc (a n) (b n) => q v)
        (Set.projIcc_of_mem (hab n) ht))
    filter_upwards [hl,hj,he] with x hx hy hz
    exact hx.trans (hy.trans (hz.trans
      (congrArg (fun z : EnergyState => energyComplexGradient z x) hstate)))
  exact exists_global_nestedLp_of_actual_compact volume p r a b ha hb localField
    (fun t => energyComplexGradient (q t)) C hnorm hactual

/-- Finite-time-exponent W and endpoint instantiations produce their slice
domains from the same numerical mixed norm bounds. -/
theorem exists_actual_global_vector_gradient_of_compact
    (p r : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ r)] [Fact (r ≠ ∞)]
    (hptop : p ≠ ∞) {C : ℝ} (hC : 0 ≤ C)
    (a b : ℕ → ℝ) (ha : Antitone a) (hb : Monotone b) (hab : ∀ n, a n ≤ b n)
    (q : ℝ → EnergyState) (Q : ∀ n, CriticalPath (intervalMeasure (a n) (b n)))
    (hQ : ∀ n (t : Icc (a n) (b n)), energyPath _ (Q n) t=q t)
    (hcap : ∀ n, mixedNorm (intervalMeasure (a n) (b n)) volume p r
      (fun t => energyComplexGradient (energyPath _ (Q n) t)) ≤ ENNReal.ofReal C) :
    ∃ F : Lp (Lp (EuclideanSpace ℂ (Fin 3)) r (volume : Measure Space)) p (volume : Measure ℝ),
      ‖F‖ ≤ C ∧
      (∀ᵐ t ∂volume.restrict (⋃ n, Icc (a n) (b n)),
        (F t : Space → EuclideanSpace ℂ (Fin 3)) =ᵐ[volume] energyComplexGradient (q t)) ∧
      (∀ᵐ t ∂volume, t ∉ ⋃ n, Icc (a n) (b n) → F t=0) := by
  apply exists_actual_global_vector_gradient_of_compact_with_slices p r hC a b ha hb hab q Q hQ hcap
  intro n
  exact finite_mixedNorm_ae_slice_memLp _ volume p r
    (ne_of_gt (lt_of_lt_of_le zero_lt_one (Fact.out : 1 ≤ p))) hptop _
    (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hcap n))

/-- The essential energy component uses its actual spatial L2 domain, so the
same exhaustion construction works at the infinite time exponent as well. -/
theorem exists_actual_global_energy_gradient_of_compact
    {C : ℝ} (hC : 0 ≤ C)
    (a b : ℕ → ℝ) (ha : Antitone a) (hb : Monotone b) (hab : ∀ n, a n ≤ b n)
    (q : ℝ → EnergyState) (Q : ∀ n, CriticalPath (intervalMeasure (a n) (b n)))
    (hQ : ∀ n (t : Icc (a n) (b n)), energyPath _ (Q n) t=q t)
    (hcap : ∀ n, mixedNorm (intervalMeasure (a n) (b n)) volume ∞ 2
      (fun t => energyComplexGradient (energyPath _ (Q n) t)) ≤ ENNReal.ofReal C) :
    ∃ F : Lp (Lp (EuclideanSpace ℂ (Fin 3)) 2 (volume : Measure Space)) ∞ (volume : Measure ℝ),
      ‖F‖ ≤ C ∧
      (∀ᵐ t ∂volume.restrict (⋃ n, Icc (a n) (b n)),
        (F t : Space → EuclideanSpace ℂ (Fin 3)) =ᵐ[volume] energyComplexGradient (q t)) ∧
      (∀ᵐ t ∂volume, t ∉ ⋃ n, Icc (a n) (b n) → F t=0) := by
  let : Fact ((1 : ℝ≥0∞) ≤ ∞) := ⟨le_top⟩
  let : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  apply exists_actual_global_vector_gradient_of_compact_with_slices ∞ 2 hC a b ha hb hab q Q hQ hcap
  intro n
  exact Eventually.of_forall fun t => energyComplexGradient_memLp_two (energyPath _ (Q n) t)

#print axioms exists_actual_global_vector_gradient_of_compact_with_slices
#print axioms exists_actual_global_vector_gradient_of_compact
#print axioms exists_actual_global_energy_gradient_of_compact
end HartreeF.IntervalNormExhaustion
