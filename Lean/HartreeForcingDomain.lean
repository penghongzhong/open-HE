import HartreePhase
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.Basic.Real.ConjExponents
import Mathlib.Tactic

/-!
Actual-function spatial forcing domain for the 3D critical generalized Hartree equation.
The only external analytic premise is `OrdinaryHLS`: the standard strong HLS theorem,
Moroz--Van Schaftingen, arXiv:1606.02158, Appendix A.1--A.2, (A.2), printed pp. 26--27.
It concerns all real input functions, the actual Riesz kernel and Lebesgue/Bochner integral.
The positive normalization c is identical in this premise and in the Hartree potential.
It can be specialized to the standard positive constant A_alpha from that source.
No HLS axiom is declared and no Hartree-specific estimate is assumed.
-/
noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal NNReal
namespace HartreeF.ForcingDomain

def rieszConvolution (α c : ℝ) (g : Space → ℝ) (x : Space) : ℝ :=
  ∫ y, rieszKernel α c (x - y) * g y

/-- External ordinary-analysis interface, including actual-integral domain and finite norms.
`C : NNReal` is finite. The endpoint q=1 and q=3/alpha are excluded. -/
structure OrdinaryHLS (α c : ℝ) : Prop where
  order_pos : 0 < α
  order_lt_three : α < 3
  normalization_pos : 0 < c
  strong_bound : ∀ q r : ℝ, 1 < q → q < 3 / α → 0 < r →
    1 / r = 1 / q - α / 3 → ∃ C : ℝ≥0, ∀ g : Space → ℝ,
      MemLp g (ENNReal.ofReal q) volume →
      (∀ᵐ x ∂volume, Integrable (fun y => rieszKernel α c (x-y) * g y) volume) ∧
      MemLp (rieszConvolution α c g) (ENNReal.ofReal r) volume ∧
      eLpNorm (rieszConvolution α c g) (ENNReal.ofReal r) volume ≤
        (C : ℝ≥0∞) * eLpNorm g (ENNReal.ofReal q) volume

def localFactor (α : ℝ) (f : Space → ℂ) (x : Space) : ℂ :=
  ‖f x‖ ^ (1 + α) • f x

/-- This is exactly (I_alpha * |f|^(3+alpha)) |f|^(1+alpha) f. -/
def forcing (α c : ℝ) (f : Space → ℂ) : Space → ℂ :=
  potential α c f • localFactor α f

def densityExponent (α : ℝ) : ℝ := 6 / (3 + α)
def potentialExponent (α : ℝ) : ℝ := 6 / (3 - α)
def energyOuterExponent (α : ℝ) : ℝ := 6 / (2 + α)
def criticalExponent (α : ℝ) : ℝ := 6 * (α + 2) / (α + 3)

theorem forcing_apply (α c : ℝ) (f : Space → ℂ) (x : Space) :
    forcing α c f x = ((potential α c f x : ℂ) * ((‖f x‖ ^ (1 + α) : ℝ) : ℂ)) * f x := by
  simp [forcing, localFactor, mul_assoc]

theorem potential_eq_convolution (α c : ℝ) (f : Space → ℂ) :
    potential α c f = rieszConvolution α c (powerDensity α f) := rfl

theorem norm_localFactor {α : ℝ} (hα : 0 < α) (f : Space → ℂ) (x : Space) :
    ‖localFactor α f x‖ = ‖f x‖ ^ (2 + α) := by
  rw [localFactor, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
  have h := Real.rpow_add_one' (norm_nonneg (f x)) (show 1 + α + 1 ≠ 0 by linarith)
  convert h.symm using 1
  congr 1
  ring

theorem localFactor_measurable (α : ℝ) {f : Space → ℂ}
    (hf : AEStronglyMeasurable f volume) :
    AEStronglyMeasurable (localFactor α f) volume := by
  exact (hf.norm.aemeasurable.pow_const (1 + α)).aestronglyMeasurable.smul hf

theorem norm_power_memLp {p s : ℝ} (hs : 0 < s) {f : Space → ℂ}
    (hf : MemLp f (ENNReal.ofReal p) volume) :
    MemLp (fun x => ‖f x‖ ^ s) (ENNReal.ofReal (p / s)) volume := by
  simpa only [ENNReal.toReal_ofReal hs.le, ENNReal.ofReal_div_of_pos hs] using
    hf.norm_rpow_div (ENNReal.ofReal s)

theorem norm_power_eLpNorm {p s : ℝ} (hs : 0 < s) {f : Space → ℂ}
    (hf : AEStronglyMeasurable f volume) :
    eLpNorm (fun x => ‖f x‖ ^ s) (ENNReal.ofReal (p / s)) volume =
      eLpNorm f (ENNReal.ofReal p) volume ^ s := by
  rw [eLpNorm_norm_rpow f hf hs, ENNReal.ofReal_div_of_pos hs,
    ENNReal.div_mul_cancel (by simpa using hs) ENNReal.ofReal_ne_top]

theorem localFactor_memLp {α p : ℝ} (hα : 0 < α) {f : Space → ℂ}
    (hf : MemLp f (ENNReal.ofReal p) volume) :
    MemLp (localFactor α f) (ENNReal.ofReal (p / (2 + α))) volume := by
  apply (norm_power_memLp (show 0 < 2 + α by linarith) hf).of_le
    (localFactor_measurable α hf.aestronglyMeasurable)
  filter_upwards [] with x
  simp only [norm_localFactor hα, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _), le_refl]

theorem localFactor_eLpNorm {α p : ℝ} (hα : 0 < α) {f : Space → ℂ}
    (hf : AEStronglyMeasurable f volume) :
    eLpNorm (localFactor α f) (ENNReal.ofReal (p / (2 + α))) volume =
      eLpNorm f (ENNReal.ofReal p) volume ^ (2 + α) := by
  rw [← norm_power_eLpNorm (show 0 < 2 + α by linarith) hf]
  apply eLpNorm_congr_norm_ae (localFactor_measurable α hf)
    ((hf.norm.aemeasurable.pow_const _).aestronglyMeasurable)
  filter_upwards [] with x
  simp only [norm_localFactor hα, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]

theorem energyHLS_range {α : ℝ} (hα : 0 < α) (hα3 : α < 3) :
    1 < densityExponent α ∧ densityExponent α < 3 / α ∧
    0 < potentialExponent α ∧
    1 / potentialExponent α = 1 / densityExponent α - α / 3 := by
  dsimp [densityExponent, potentialExponent]
  have hp : 0 < 3 + α := by linarith
  have hm : 0 < 3 - α := by linarith
  refine ⟨(lt_div_iff₀ hp).2 (by linarith), ?_, div_pos (by norm_num) hm, ?_⟩
  · exact (div_lt_div_iff₀ hp hα).2 (by nlinarith)
  · field_simp
    ring

theorem powerDensity_memLp {α : ℝ} (hα : 0 < α) {f : Space → ℂ}
    (hf : MemLp f 6 volume) :
    MemLp (powerDensity α f) (ENNReal.ofReal (densityExponent α)) volume := by
  exact norm_power_memLp (show 0 < 3 + α by linarith) (by simpa using hf)

theorem powerDensity_eLpNorm {α : ℝ} (hα : 0 < α) {f : Space → ℂ}
    (hf : AEStronglyMeasurable f volume) :
    eLpNorm (powerDensity α f) (ENNReal.ofReal (densityExponent α)) volume =
      eLpNorm f 6 volume ^ (3 + α) := by
  change eLpNorm (fun x => ‖f x‖ ^ (3 + α)) (ENNReal.ofReal (6 / (3 + α))) volume = _
  simpa only [ENNReal.ofReal_ofNat] using
    norm_power_eLpNorm (p := 6) (show 0 < 3 + α by linarith) hf

theorem potential_domain_bound {α c : ℝ} (hHLS : OrdinaryHLS α c) :
    ∃ C : ℝ≥0, ∀ f : Space → ℂ, MemLp f 6 volume →
      (∀ᵐ x ∂volume, Integrable
        (fun y => rieszKernel α c (x-y) * powerDensity α f y) volume) ∧
      MemLp (potential α c f) (ENNReal.ofReal (potentialExponent α)) volume ∧
      eLpNorm (potential α c f) (ENNReal.ofReal (potentialExponent α)) volume ≤
        (C : ℝ≥0∞) * eLpNorm f 6 volume ^ (3 + α) := by
  obtain ⟨hq1, hqα, hr, hrel⟩ := energyHLS_range hHLS.order_pos hHLS.order_lt_three
  obtain ⟨C, hC⟩ := hHLS.strong_bound _ _ hq1 hqα hr hrel
  refine ⟨C, fun f hf => ?_⟩
  obtain ⟨hi, hm, hb⟩ := hC (powerDensity α f) (powerDensity_memLp hHLS.order_pos hf)
  rw [powerDensity_eLpNorm hHLS.order_pos hf.aestronglyMeasurable] at hb
  exact ⟨hi, hm, hb⟩


theorem energy_holder {α : ℝ} (hα : 0 < α) (hα3 : α < 3) :
    Real.HolderTriple (potentialExponent α) (energyOuterExponent α) (6 / 5) := by
  constructor
  · simp only [potentialExponent, energyOuterExponent, inv_div]
    ring
  · exact div_pos (by norm_num) (by linarith)
  · exact div_pos (by norm_num) (by linarith)

theorem critical_outer_exponent {α : ℝ} (hα : 0 < α) :
    criticalExponent α / (2 + α) = densityExponent α := by
  dsimp [criticalExponent, densityExponent]
  field_simp
  ring

theorem critical_holder {α : ℝ} (hα : 0 < α) (hα3 : α < 3) :
    Real.HolderTriple (potentialExponent α) (densityExponent α) 1 := by
  constructor
  · simp only [potentialExponent, densityExponent, inv_div, inv_one]
    ring
  · exact div_pos (by norm_num) (by linarith)
  · exact div_pos (by norm_num) (by linarith)

theorem critical_exponent_range {α : ℝ} (hα : 0 < α) (hα3 : α < 3) :
    4 < criticalExponent α ∧ criticalExponent α < 5 := by
  dsimp [criticalExponent]
  have hd : 0 < α + 3 := by linarith
  constructor
  · exact (lt_div_iff₀ hd).2 (by nlinarith)
  · exact (div_lt_iff₀ hd).2 (by nlinarith)

/-- Actual complex forcing has finite L^(6/5) norm from L6 alone. -/
theorem forcing_energy_domain_bound {α c : ℝ} (hHLS : OrdinaryHLS α c) :
    ∃ C : ℝ≥0, ∀ f : Space → ℂ, MemLp f 6 volume →
      MemLp (forcing α c f) (ENNReal.ofReal (6 / 5 : ℝ)) volume ∧
      eLpNorm (forcing α c f) (ENNReal.ofReal (6 / 5 : ℝ)) volume ≤
        (C : ℝ≥0∞) * eLpNorm f 6 volume ^ (3 + α) * eLpNorm f 6 volume ^ (2 + α) := by
  obtain ⟨C, hC⟩ := potential_domain_bound hHLS
  refine ⟨C, fun f hf => ?_⟩
  obtain ⟨_, hp, hb⟩ := hC f hf
  have hl : MemLp (localFactor α f) (ENNReal.ofReal (energyOuterExponent α)) volume :=
    localFactor_memLp hHLS.order_pos (by simpa using hf)
  let := (energy_holder hHLS.order_pos hHLS.order_lt_three).ennrealOfReal
  refine ⟨hp.smul hl, ?_⟩
  calc
    _ ≤ eLpNorm (potential α c f) (ENNReal.ofReal (potentialExponent α)) volume *
        eLpNorm (localFactor α f) (ENNReal.ofReal (energyOuterExponent α)) volume :=
      eLpNorm_smul_le_mul_eLpNorm hp.aestronglyMeasurable hl.aestronglyMeasurable
    _ = eLpNorm (potential α c f) (ENNReal.ofReal (potentialExponent α)) volume *
        eLpNorm f 6 volume ^ (2 + α) := by
      congr 1
      simpa only [energyOuterExponent, ENNReal.ofReal_ofNat] using
        localFactor_eLpNorm (p := 6) hHLS.order_pos hf.aestronglyMeasurable
    _ ≤ _ := by gcongr

/-- Additional L^rcrit input gives a genuine Bochner-integrable forcing and finite L1 bound.
No input L2 membership appears. -/
theorem forcing_critical_domain_bound {α c : ℝ} (hHLS : OrdinaryHLS α c) :
    ∃ C : ℝ≥0, ∀ f : Space → ℂ, MemLp f 6 volume →
      MemLp f (ENNReal.ofReal (criticalExponent α)) volume →
      Integrable (forcing α c f) volume ∧
      eLpNorm (forcing α c f) 1 volume ≤
        (C : ℝ≥0∞) * eLpNorm f 6 volume ^ (3 + α) *
          eLpNorm f (ENNReal.ofReal (criticalExponent α)) volume ^ (2 + α) := by
  obtain ⟨C, hC⟩ := potential_domain_bound hHLS
  refine ⟨C, fun f hf hcrit => ?_⟩
  obtain ⟨_, hp, hb⟩ := hC f hf
  have hl : MemLp (localFactor α f) (ENNReal.ofReal (densityExponent α)) volume := by
    simpa only [critical_outer_exponent hHLS.order_pos] using
      localFactor_memLp hHLS.order_pos hcrit
  let : ENNReal.HolderTriple (ENNReal.ofReal (potentialExponent α))
      (ENNReal.ofReal (densityExponent α)) 1 := by
    simpa only [ENNReal.ofReal_one] using
      (critical_holder hHLS.order_pos hHLS.order_lt_three).ennrealOfReal
  refine ⟨memLp_one_iff_integrable.mp (hp.smul hl), ?_⟩
  calc
    _ ≤ eLpNorm (potential α c f) (ENNReal.ofReal (potentialExponent α)) volume *
        eLpNorm (localFactor α f) (ENNReal.ofReal (densityExponent α)) volume :=
      eLpNorm_smul_le_mul_eLpNorm hp.aestronglyMeasurable hl.aestronglyMeasurable
    _ = eLpNorm (potential α c f) (ENNReal.ofReal (potentialExponent α)) volume *
        eLpNorm f (ENNReal.ofReal (criticalExponent α)) volume ^ (2 + α) := by
      congr 1
      simpa only [critical_outer_exponent hHLS.order_pos] using
        localFactor_eLpNorm (p := criticalExponent α) hHLS.order_pos hcrit.aestronglyMeasurable
    _ ≤ _ := by gcongr


/-- The literal Hartree interaction energy density is integrable from L6 alone. -/
theorem interaction_density_domain_bound {α c : ℝ} (hHLS : OrdinaryHLS α c) :
    ∃ C : ℝ≥0, ∀ f : Space → ℂ, MemLp f 6 volume →
      Integrable (fun x => potential α c f x * powerDensity α f x) volume ∧
      eLpNorm (fun x => potential α c f x * powerDensity α f x) 1 volume ≤
        (C : ℝ≥0∞) * eLpNorm f 6 volume ^ (3 + α) * eLpNorm f 6 volume ^ (3 + α) := by
  obtain ⟨C, hC⟩ := potential_domain_bound hHLS
  refine ⟨C, fun f hf => ?_⟩
  obtain ⟨_, hp, hb⟩ := hC f hf
  have hd := powerDensity_memLp hHLS.order_pos hf
  let : ENNReal.HolderTriple (ENNReal.ofReal (potentialExponent α))
      (ENNReal.ofReal (densityExponent α)) 1 := by
    simpa only [ENNReal.ofReal_one] using
      (critical_holder hHLS.order_pos hHLS.order_lt_three).ennrealOfReal
  refine ⟨memLp_one_iff_integrable.mp (hp.fun_mul hd), ?_⟩
  calc
    _ ≤ eLpNorm (potential α c f) (ENNReal.ofReal (potentialExponent α)) volume *
        eLpNorm (powerDensity α f) (ENNReal.ofReal (densityExponent α)) volume :=
      eLpNorm_smul_le_mul_eLpNorm hp.aestronglyMeasurable hd.aestronglyMeasurable
    _ = eLpNorm (potential α c f) (ENNReal.ofReal (potentialExponent α)) volume *
        eLpNorm f 6 volume ^ (3 + α) := by
      rw [powerDensity_eLpNorm hHLS.order_pos hf.aestronglyMeasurable]
    _ ≤ _ := by gcongr

theorem interaction_density_integrable {α c : ℝ} (hHLS : OrdinaryHLS α c)
    {f : Space → ℂ} (hf : MemLp f 6 volume) :
    Integrable (fun x => potential α c f x * powerDensity α f x) volume := by
  obtain ⟨C, hC⟩ := interaction_density_domain_bound hHLS
  exact (hC f hf).1

/-- Real-valued L1 norm bound. All input and output norms are finite. -/
theorem forcing_critical_real_norm_bound {α c : ℝ} (hHLS : OrdinaryHLS α c) :
    ∃ C : ℝ≥0, ∀ f : Space → ℂ, MemLp f 6 volume →
      MemLp f (ENNReal.ofReal (criticalExponent α)) volume →
      (eLpNorm (forcing α c f) 1 volume).toReal ≤
        (C : ℝ) * (eLpNorm f 6 volume).toReal ^ (3 + α) *
          (eLpNorm f (ENNReal.ofReal (criticalExponent α)) volume).toReal ^ (2 + α) := by
  obtain ⟨C, hC⟩ := forcing_critical_domain_bound hHLS
  refine ⟨C, fun f hf hcrit => ?_⟩
  have h6 := hf.eLpNorm_ne_top
  have hcritf := hcrit.eLpNorm_ne_top
  have hp : 0 ≤ 3 + α := by linarith [hHLS.order_pos]
  have hq : 0 ≤ 2 + α := by linarith [hHLS.order_pos]
  have hn : (C : ℝ≥0∞) * eLpNorm f 6 volume ^ (3 + α) *
      eLpNorm f (ENNReal.ofReal (criticalExponent α)) volume ^ (2 + α) ≠ ∞ := by
    finiteness
  have hb := ENNReal.toReal_mono hn (hC f hf hcrit).2
  simpa only [ENNReal.toReal_mul, ENNReal.coe_toReal, ENNReal.toReal_rpow] using hb

#print axioms forcing_apply
#print axioms potential_eq_convolution
#print axioms norm_localFactor
#print axioms localFactor_measurable
#print axioms norm_power_memLp
#print axioms norm_power_eLpNorm
#print axioms localFactor_memLp
#print axioms localFactor_eLpNorm
#print axioms energyHLS_range
#print axioms powerDensity_memLp
#print axioms powerDensity_eLpNorm
#print axioms potential_domain_bound
#print axioms energy_holder
#print axioms critical_outer_exponent
#print axioms critical_holder
#print axioms critical_exponent_range
#print axioms forcing_energy_domain_bound
#print axioms forcing_critical_domain_bound
#print axioms interaction_density_domain_bound
#print axioms interaction_density_integrable
#print axioms forcing_critical_real_norm_bound
end HartreeF.ForcingDomain
