import CompactLpTails

noncomputable section
set_option autoImplicit false
open MeasureTheory Set Filter Metric
open scoped ENNReal Topology
namespace HartreeF.ComplexIMS
open CutoffApproximation SobolevStretch

instance fact_one_le_six : Fact (1 ≤ (6 : ℝ≥0∞)) := ⟨by norm_num⟩
instance fact_one_le_two : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩

/-- A genuine complex field and its distributional real and imaginary weak gradients. -/
structure HomogeneousData where
  u : Space → ℂ
  realGradient : Space → Space
  imagGradient : Space → Space
  domain : InDotH1 u realGradient imagGradient

/-- The actual L6 × L2 × L2 realization; compactness here is stated explicitly. -/
def HomogeneousData.lpData (f : HomogeneousData) :
    Lp ℂ 6 (volume : Measure Space) ×
      (Lp Space 2 (volume : Measure Space) × Lp Space 2 (volume : Measure Space)) :=
  ⟨f.domain.function_L6.toLp f.u,
    f.domain.real_gradient_L2.toLp f.realGradient,
    f.domain.imag_gradient_L2.toLp f.imagGradient⟩

/-- Lp quotient restriction norms equal the integrals of the supplied actual field. -/
theorem exteriorLp_toLp_norm {E : Type*} [NormedAddCommGroup E] {p : ℝ≥0∞}
    {f : Space → E} (hf : MemLp f p volume) (n : ℕ) :
    ‖exteriorLp n (hf.toLp f)‖ = (eLpNorm (exteriorTail n f) p volume).toReal := by
  rw [exteriorLp_norm]
  congr 1
  apply eLpNorm_congr_ae
  filter_upwards [hf.coeFn_toLp] with x hx
  unfold exteriorTail
  by_cases hs : (n : ℝ) < ‖x‖ <;> simp [Set.indicator, hs, hx]

/-- A single radius controls all three literal tails uniformly near a compact family.
The input is explicitly compactness of actual L6 × L2 × L2 data, not an assumed tail bound. -/
theorem compact_homogeneous_uniform_tails {K : Set HomogeneousData}
    (hK : IsCompact (HomogeneousData.lpData '' K)) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ f ∈ K, ∀ g : HomogeneousData,
      dist g.lpData f.lpData < ε / 4 →
      (eLpNorm (exteriorTail n g.u) 6 volume).toReal < ε ∧
      (eLpNorm (exteriorTail n g.realGradient) 2 volume).toReal < ε ∧
      (eLpNorm (exteriorTail n g.imagGradient) 2 volume).toReal < ε := by
  have h0 := hK.image continuous_fst
  have h1 := hK.image (continuous_fst.comp continuous_snd)
  have h2 := hK.image (continuous_snd.comp continuous_snd)
  obtain ⟨N0, hN0⟩ := compact_exteriorLp_uniform_neighborhood (by norm_num : (6 : ℝ≥0∞) ≠ ∞) h0 hε
  obtain ⟨N1, hN1⟩ := compact_exteriorLp_uniform_neighborhood (by norm_num : (2 : ℝ≥0∞) ≠ ∞) h1 hε
  obtain ⟨N2, hN2⟩ := compact_exteriorLp_uniform_neighborhood (by norm_num : (2 : ℝ≥0∞) ≠ ∞) h2 hε
  refine ⟨max N0 (max N1 N2), ?_⟩
  intro n hn f hf g hgf
  have hn0 : N0 ≤ n := (le_max_left _ _).trans hn
  have hn1 : N1 ≤ n := (le_max_left _ _).trans ((le_max_right _ _).trans hn)
  have hn2 : N2 ≤ n := (le_max_right _ _).trans ((le_max_right _ _).trans hn)
  simp only [Prod.dist_eq, max_lt_iff] at hgf
  have hd0 : dist g.lpData.1 f.lpData.1 < ε / 4 := hgf.1
  have hd1 : dist g.lpData.2.1 f.lpData.2.1 < ε / 4 := hgf.2.1
  have hd2 : dist g.lpData.2.2 f.lpData.2.2 < ε / 4 := hgf.2.2
  have hmem : f.lpData ∈ HomogeneousData.lpData '' K := mem_image_of_mem _ hf
  have hh0 := hN0 n hn0 f.lpData.1 (mem_image_of_mem _ hmem) g.lpData.1 hd0
  have hh1 := hN1 n hn1 f.lpData.2.1 (mem_image_of_mem _ hmem) g.lpData.2.1 hd1
  have hh2 := hN2 n hn2 f.lpData.2.2 (mem_image_of_mem _ hmem) g.lpData.2.2 hd2
  exact ⟨by simpa only [HomogeneousData.lpData, exteriorLp_toLp_norm] using hh0,
    by simpa only [HomogeneousData.lpData, exteriorLp_toLp_norm] using hh1,
    by simpa only [HomogeneousData.lpData, exteriorLp_toLp_norm] using hh2⟩

#print axioms exteriorLp_toLp_norm
#print axioms compact_homogeneous_uniform_tails
end HartreeF.ComplexIMS
