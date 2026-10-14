import WeakLeibnizH1Factor

noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal
namespace HartreeF.WeakHartreeProduct
open SobolevStretch WeakCutoffLp ForcingDomain GradientMajorants RieszWeakDerivative

theorem compact_smul_memLp_lower {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {s t : ℝ} (hs : 0 < s) (hst : s < t)
    {χ : Space → ℝ} (hχ : Continuous χ) (hc : HasCompactSupport χ)
    {f : Space → E} (hf : MemLp f (ENNReal.ofReal (1/s)) volume) :
    MemLp (fun x => χ x • f x) (ENNReal.ofReal (1/t)) volume := by
  have hh : Real.HolderTriple (1/(t-s)) (1/s) (1/t) := by
    constructor
    · simp
    · exact div_pos (by norm_num) (by linarith)
    · positivity
  let := hh.ennrealOfReal
  exact (hχ.memLp_of_hasCompactSupport (p := ENNReal.ofReal (1/(t-s))) hc).smul hf

theorem smul_compact_memLp_lower {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {s t : ℝ} (hs : 0 < s) (hst : s < t)
    {χ : Space → E} (hχ : Continuous χ) (hc : HasCompactSupport χ)
    {f : Space → ℝ} (hf : MemLp f (ENNReal.ofReal (1/s)) volume) :
    MemLp (fun x => f x • χ x) (ENNReal.ofReal (1/t)) volume := by
  have hh : Real.HolderTriple (1/s) (1/(t-s)) (1/t) := by
    constructor
    · simp
    · positivity
    · exact div_pos (by norm_num) (by linarith)
  let := hh.ennrealOfReal
  exact hf.smul (hχ.memLp_of_hasCompactSupport (p := ENNReal.ofReal (1/(t-s))) hc)

theorem hartreePotential_memLp_split {α c : ℝ} (hH : OrdinaryHLS α c)
    {u : Space → ℂ} (hu6 : MemLp u 6 volume) (hu10 : MemLp u 10 volume) :
    MemLp (potential α c u) (ENNReal.ofReal (1/(reciprocalA α-α/3))) volume := by
  have hr := gradient_hls_ranges hH.order_pos hH.order_lt_three
  obtain ⟨C,hC⟩ := convolution_bound hH hr.1 hr.2.1
  have hb := first_density_bound hH.order_pos hH.order_lt_three (fun x => norm_nonneg (u x)) hu6.norm hu10.norm
  exact (hC _ _ hb).2.memLp

theorem potential_reciprocal_bounds {α c : ℝ} (hH : OrdinaryHLS α c) :
    0 < reciprocalA α-α/3 ∧ reciprocalA α-α/3 < 1/2 ∧
    0 < reciprocalB α-α/3 ∧ reciprocalB α-α/3 < 5/6 := by
  have hα := hH.order_pos
  have hα3 := hH.order_lt_three
  dsimp [reciprocalA,reciprocalB]
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

theorem cutoff_potential_domains {α c : ℝ} (hH : OrdinaryHLS α c)
    {u : Space → ℂ} {U V : Space → Space}
    (hu6 : MemLp u 6 volume) (hu10 : MemLp u 10 volume)
    (hU : MemLp U (ENNReal.ofReal (30/13 : ℝ)) volume)
    (hV : MemLp V (ENNReal.ofReal (30/13 : ℝ)) volume)
    {χ : Space → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ) :
    MemLp (fun x => χ x*potential α c u x) 2 volume ∧
    MemLp (fun x => χ x • hartreePotentialGradient α c u U V x+potential α c u x • gradient χ x)
      (ENNReal.ofReal (6/5 : ℝ)) volume := by
  have hp := hartreePotential_memLp_split hH hu6 hu10
  have hg := (hartreePotentialGradient_domain hH hu6 hu10 hU hV).2
  have hr := potential_reciprocal_bounds hH
  have hf2 := compact_smul_memLp_lower hr.1 hr.2.1 hχ.continuous hc hp
  have hg1 := compact_smul_memLp_lower hr.2.2.1 hr.2.2.2 hχ.continuous hc hg
  have hg2 := smul_compact_memLp_lower hr.1 (by linarith [hr.2.1] : reciprocalA α-α/3 < 5/6)
    (cutoff_gradient_continuous hχ) (cutoff_gradient_hasCompactSupport hc) hp
  constructor
  · simpa using hf2
  · convert hg1.add hg2 using 1
    norm_num

#print axioms compact_smul_memLp_lower
#print axioms smul_compact_memLp_lower
#print axioms hartreePotential_memLp_split
#print axioms potential_reciprocal_bounds
#print axioms cutoff_potential_domains
end HartreeF.WeakHartreeProduct
