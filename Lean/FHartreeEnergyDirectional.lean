import HartreeBilinearDifference
import HartreePowerCalculus
import ForcingLpMap
import DirectionalPotentialEnvelopes
import Mathlib.Analysis.Calculus.ParametricIntegral

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Set
open scoped ENNReal Topology
namespace HartreeF.EnergyVariation
open ForcingDomain SharpOrdinary EnergyContinuity

/-- Symmetry of the actual Riesz bilinear integral follows from its even kernel. -/
theorem actual_bilinear_symmetry (α : ℝ) (f g : Space → ℝ) :
    (∫ q, bilinearRieszPair α f g q ∂volume.prod volume) =
      ∫ q, bilinearRieszPair α g f q ∂volume.prod volume := by
  rw [← integral_prod_swap (bilinearRieszPair α g f)]
  apply integral_congr_ae
  filter_upwards [] with q
  simp only [bilinearRieszPair, Prod.swap, rieszKernel,
    norm_sub_rev q.2 q.1]
  ring

def affinePath (u h : Space → ℂ) (t : ℝ) : Space → ℂ := u + t • h

def densityVariation (α : ℝ) (u h : Space → ℂ) (x : Space) : ℝ :=
  WeakHartreeChain.densityDerivative (3+α) (u x) (h x)

theorem densityVariation_formula (α : ℝ) (u h : Space → ℂ) (x : Space) :
    densityVariation α u h x = (3+α)*‖u x‖^(1+α)*
      (star (u x) * h x).re := by
  rw [densityVariation, WeakHartreeChain.densityDerivative_apply]
  simp only [Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im]
  rw [show 3+α-2=1+α by ring]
  ring

theorem density_along_path_hasDerivAt {α : ℝ} (hα : 0 < α)
    (u h : Space → ℂ) (x : Space) (t : ℝ) :
    HasDerivAt (fun s => powerDensity α (affinePath u h s) x)
      (densityVariation α (affinePath u h t) h x) t := by
  have hp : 1 < 3+α := by linarith
  have ha : HasDerivAt (fun s : ℝ => u x + s • h x) (h x) t := by
    simpa using ((hasDerivAt_id t).smul_const (h x)).const_add (u x)
  exact (WeakHartreeChain.density_hasFDerivAt hp _).comp_hasDerivAt t ha

def envelope (u h : Space → ℂ) (x : Space) : ℂ := (‖u x‖+‖h x‖ : ℝ)

theorem envelope_memLp {u h : Space → ℂ} (hu : MemLp u 6 volume)
    (hh : MemLp h 6 volume) : MemLp (envelope u h) 6 volume :=
  (hu.norm.add hh.norm).ofReal

theorem norm_envelope (u h : Space → ℂ) (x : Space) :
    ‖envelope u h x‖=‖u x‖+‖h x‖ := by
  change ‖((‖u x‖+‖h x‖ : ℝ) : ℂ)‖=‖u x‖+‖h x‖
  rw [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]

theorem norm_affinePath_le_envelope (u h : Space → ℂ) (x : Space)
    {t : ℝ} (ht : |t| ≤ 1) : ‖affinePath u h t x‖ ≤ ‖envelope u h x‖ := by
  rw [norm_envelope]
  exact (norm_add_le (u x) (t • h x)).trans (by
    rw [norm_smul, Real.norm_eq_abs]
    exact add_le_add le_rfl (mul_le_of_le_one_left (norm_nonneg (h x)) ht))

theorem densityVariation_bound {α : ℝ} (hα : 0 < α)
    (u h : Space → ℂ) (x : Space) {t : ℝ} (ht : |t| ≤ 1) :
    ‖densityVariation α (affinePath u h t) h x‖ ≤
      (3+α)*powerDensity α (envelope u h) x := by
  have hp : 1 < 3+α := by linarith
  have hn := norm_affinePath_le_envelope u h x ht
  have hh : ‖h x‖ ≤ ‖envelope u h x‖ := by
    rw [norm_envelope]
    exact le_add_of_nonneg_left (norm_nonneg _)
  calc
    _ ≤ ‖WeakHartreeChain.densityDerivative (3+α) (affinePath u h t x)‖ * ‖h x‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ = (3+α)*‖affinePath u h t x‖^(3+α-1)*‖h x‖ := by
      rw [WeakHartreeChain.densityDerivative_norm hp]
    _ ≤ (3+α)*‖envelope u h x‖^(3+α-1)*‖envelope u h x‖ := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (norm_nonneg _) hn (by linarith)) (by linarith)
      · exact hh
      · exact norm_nonneg _
      · positivity
    _ = _ := by
      rw [mul_assoc, ← Real.rpow_add_one' (norm_nonneg _) (by linarith : 3+α-1+1≠0)]
      simp only [sub_add_cancel, powerDensity]

theorem densityVariation_measurable (α : ℝ) {u h : Space → ℂ}
    (hu : AEStronglyMeasurable u volume) (hh : AEStronglyMeasurable h volume) :
    AEStronglyMeasurable (densityVariation α u h) volume :=
  DerivativeMajorization.directionalDensity_measurable α hu hh

theorem powerDensity_path_bound {α : ℝ} (hα : 0 < α)
    (u h : Space → ℂ) (x : Space) {t : ℝ} (ht : |t| ≤ 1) :
    ‖powerDensity α (affinePath u h t) x‖ ≤ powerDensity α (envelope u h) x := by
  rw [powerDensity, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
  exact Real.rpow_le_rpow (norm_nonneg _)
    (norm_affinePath_le_envelope u h x ht) (by linarith)

def pairVariation (α c : ℝ) (u h : Space → ℂ) (q : Space × Space) : ℝ :=
  rieszKernel α c (q.1-q.2) *
    (densityVariation α u h q.2 * powerDensity α u q.1 +
      powerDensity α u q.2 * densityVariation α u h q.1)

theorem pair_along_path_hasDerivAt {α c : ℝ} (hα : 0 < α)
    (u h : Space → ℂ) (q : Space × Space) (t : ℝ) :
    HasDerivAt (fun s => PressureDomain.rieszPairDensity α c (affinePath u h s) q)
      (pairVariation α c (affinePath u h t) h q) t := by
  convert ((density_along_path_hasDerivAt hα u h q.2 t).mul
    (density_along_path_hasDerivAt hα u h q.1 t)).const_mul
      (rieszKernel α c (q.1-q.2)) using 1
  · funext s
    simp only [PressureDomain.rieszPairDensity, Pi.mul_apply]
    ring
  · simp only [pairVariation]

theorem pairVariation_measurable (α c : ℝ) {u h : Space → ℂ}
    (hu : AEStronglyMeasurable u volume) (hh : AEStronglyMeasurable h volume) :
    AEStronglyMeasurable (pairVariation α c u h) (volume.prod volume) := by
  have hk : Measurable (fun q : Space × Space => rieszKernel α c (q.1-q.2)) :=
    measurable_const.mul (((measurable_fst.sub measurable_snd).norm).pow_const _)
  have hd : AEStronglyMeasurable (powerDensity α u) volume :=
    (hu.norm.aemeasurable.pow_const _).aestronglyMeasurable
  have hv := densityVariation_measurable α hu hh
  exact hk.aestronglyMeasurable.mul
    ((hv.comp_snd.mul hd.comp_fst).add (hd.comp_snd.mul hv.comp_fst))

theorem pairVariation_bound {α c : ℝ} (hα : 0 < α) (hc : 0 ≤ c)
    (u h : Space → ℂ) (q : Space × Space) {t : ℝ} (ht : |t| ≤ 1) :
    ‖pairVariation α c (affinePath u h t) h q‖ ≤
      (2*(3+α))*PressureDomain.rieszPairDensity α c (envelope u h) q := by
  have hk : 0 ≤ rieszKernel α c (q.1-q.2) := by unfold rieszKernel; positivity
  calc
    _ ≤ rieszKernel α c (q.1-q.2) *
        (‖densityVariation α (affinePath u h t) h q.2‖ *
            ‖powerDensity α (affinePath u h t) q.1‖ +
          ‖powerDensity α (affinePath u h t) q.2‖ *
            ‖densityVariation α (affinePath u h t) h q.1‖) := by
      rw [pairVariation, norm_mul, Real.norm_of_nonneg hk]
      apply mul_le_mul_of_nonneg_left _ hk
      simpa only [norm_mul] using norm_add_le
        (densityVariation α (affinePath u h t) h q.2 * powerDensity α (affinePath u h t) q.1)
        (powerDensity α (affinePath u h t) q.2 * densityVariation α (affinePath u h t) h q.1)
    _ ≤ rieszKernel α c (q.1-q.2) *
        ((3+α)*powerDensity α (envelope u h) q.2 * powerDensity α (envelope u h) q.1 +
          powerDensity α (envelope u h) q.2 * ((3+α)*powerDensity α (envelope u h) q.1)) := by
      apply mul_le_mul_of_nonneg_left _ hk
      apply add_le_add
      · exact mul_le_mul (densityVariation_bound hα u h q.2 ht)
          (powerDensity_path_bound hα u h q.1 ht) (norm_nonneg _) (by unfold powerDensity; positivity)
      · exact mul_le_mul (powerDensity_path_bound hα u h q.2 ht)
          (densityVariation_bound hα u h q.1 ht) (norm_nonneg _) (by unfold powerDensity; positivity)
    _ = _ := by unfold PressureDomain.rieszPairDensity; ring

/-- Differentiation under the literal double integral, with an HLS-produced majorant. -/
theorem actual_pair_energy_hasDerivAt {α c : ℝ} (hH : OrdinaryHLS α c)
    {u h : Space → ℂ} (hu : MemLp u 6 volume) (hh : MemLp h 6 volume) :
    Integrable (pairVariation α c u h) (volume.prod volume) ∧
    HasDerivAt (fun t => ∫ q, PressureDomain.rieszPairDensity α c (affinePath u h t) q
      ∂volume.prod volume) (∫ q, pairVariation α c u h q ∂volume.prod volume) 0 := by
  have hpath (t : ℝ) : MemLp (affinePath u h t) 6 volume := hu.add (hh.const_smul t)
  have henv := PressureDomain.rieszPairDensity_integrable hH (envelope_memLp hu hh)
  have hz : affinePath u h 0 = u := by simp [affinePath]
  simpa only [hz] using
    (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := fun t q => PressureDomain.rieszPairDensity α c (affinePath u h t) q)
      (F' := fun t q => pairVariation α c (affinePath u h t) h q)
      (bound := fun q => (2*(3+α))*PressureDomain.rieszPairDensity α c (envelope u h) q)
      (s := Metric.ball 0 1) (x₀ := (0 : ℝ))
      (Metric.ball_mem_nhds 0 (by norm_num))
      (Eventually.of_forall (fun t => PressureDomain.rieszPairDensity_measurable
        (hpath t).aestronglyMeasurable))
      (PressureDomain.rieszPairDensity_integrable hH (hpath 0))
      (pairVariation_measurable α c (hpath 0).aestronglyMeasurable hh.aestronglyMeasurable)
      (Eventually.of_forall (fun q t ht => pairVariation_bound hH.order_pos
        hH.normalization_pos.le u h q (by simpa [Real.dist_eq] using (Metric.mem_ball.mp ht).le)))
      (henv.const_mul (2*(3+α)))
      (Eventually.of_forall (fun q t _ => pair_along_path_hasDerivAt hH.order_pos u h q t)))

def pairHalf (α c : ℝ) (u h : Space → ℂ) (q : Space × Space) : ℝ :=
  rieszKernel α c (q.1-q.2) * powerDensity α u q.2 * densityVariation α u h q.1

theorem pairHalf_measurable (α c : ℝ) {u h : Space → ℂ}
    (hu : AEStronglyMeasurable u volume) (hh : AEStronglyMeasurable h volume) :
    AEStronglyMeasurable (pairHalf α c u h) (volume.prod volume) := by
  have hk : Measurable (fun q : Space × Space => rieszKernel α c (q.1-q.2)) :=
    measurable_const.mul (((measurable_fst.sub measurable_snd).norm).pow_const _)
  have hd : AEStronglyMeasurable (powerDensity α u) volume :=
    (hu.norm.aemeasurable.pow_const _).aestronglyMeasurable
  exact (hk.aestronglyMeasurable.mul hd.comp_snd).mul
    (densityVariation_measurable α hu hh).comp_fst

theorem pairHalf_bound {α c : ℝ} (hα : 0 < α) (hc : 0 ≤ c)
    (u h : Space → ℂ) (q : Space × Space) :
    ‖pairHalf α c u h q‖ ≤
      (3+α)*PressureDomain.rieszPairDensity α c (envelope u h) q := by
  have hk : 0 ≤ rieszKernel α c (q.1-q.2) := by unfold rieszKernel; positivity
  have hz : affinePath u h 0 = u := by simp [affinePath]
  have hd := powerDensity_path_bound hα u h q.2 (t := 0) (by norm_num)
  have hv := densityVariation_bound hα u h q.1 (t := 0) (by norm_num)
  rw [hz] at hd hv
  calc
    _ = rieszKernel α c (q.1-q.2) * ‖powerDensity α u q.2‖ *
        ‖densityVariation α u h q.1‖ := by
      rw [pairHalf, norm_mul, norm_mul, Real.norm_of_nonneg hk]
    _ ≤ rieszKernel α c (q.1-q.2) * powerDensity α (envelope u h) q.2 *
        ((3+α)*powerDensity α (envelope u h) q.1) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hd hk) hv (norm_nonneg _)
        (mul_nonneg hk (Real.rpow_nonneg (norm_nonneg _) _))
    _ = _ := by unfold PressureDomain.rieszPairDensity; ring

theorem pairHalf_integrable {α c : ℝ} (hH : OrdinaryHLS α c)
    {u h : Space → ℂ} (hu : MemLp u 6 volume) (hh : MemLp h 6 volume) :
    Integrable (pairHalf α c u h) (volume.prod volume) := by
  apply ((PressureDomain.rieszPairDensity_integrable hH
    (envelope_memLp hu hh)).const_mul (3+α)).mono'
    (pairHalf_measurable α c hu.aestronglyMeasurable hh.aestronglyMeasurable)
  exact Eventually.of_forall (pairHalf_bound hH.order_pos hH.normalization_pos.le u h)

theorem pairVariation_eq_halves (α c : ℝ) (u h : Space → ℂ) (q : Space × Space) :
    pairVariation α c u h q = pairHalf α c u h q + pairHalf α c u h q.swap := by
  simp only [pairVariation, pairHalf, Prod.swap, rieszKernel, norm_sub_rev q.2 q.1]
  ring

/-- The two real kernel terms coincide by even-kernel symmetry and absolute Fubini. -/
theorem pairVariation_integral_eq {α c : ℝ} (hH : OrdinaryHLS α c)
    {u h : Space → ℂ} (hu : MemLp u 6 volume) (hh : MemLp h 6 volume) :
    (∫ q, pairVariation α c u h q ∂volume.prod volume) =
      2 * ∫ x, potential α c u x * densityVariation α u h x := by
  have hi := pairHalf_integrable hH hu hh
  have his : Integrable (fun q => pairHalf α c u h q.swap) (volume.prod volume) := hi.swap
  simp_rw [pairVariation_eq_halves]
  rw [integral_add hi his, integral_prod_swap]
  have hp : (∫ q, pairHalf α c u h q ∂volume.prod volume) =
      ∫ x, potential α c u x * densityVariation α u h x := by
    rw [integral_prod _ hi]
    apply integral_congr_ae
    filter_upwards [] with x
    simp only [pairHalf, potential, integral_mul_const]
  rw [hp]
  ring

theorem potential_densityVariation_eq (α c : ℝ) (u h : Space → ℂ) (x : Space) :
    potential α c u x * densityVariation α u h x =
      (3+α) * (star (forcing α c u x) * h x).re := by
  rw [densityVariation_formula, forcing_apply]
  simp only [Complex.star_def, map_mul, Complex.conj_ofReal, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, Complex.conj_re,
    Complex.conj_im, Complex.mul_im, zero_mul, add_zero]
  ring

theorem forcing_pairing_integrable {α c : ℝ} (hH : OrdinaryHLS α c)
    {u h : Space → ℂ} (hu : MemLp u 6 volume) (hh : MemLp h 6 volume) :
    Integrable (fun x => star (forcing α c u x) * h x) volume := by
  let : ENNReal.HolderTriple (ENNReal.ofReal (6/5 : ℝ)) 6 1 := by
    have h : Real.HolderTriple (6/5) 6 1 := by constructor <;> norm_num
    simpa only [ENNReal.ofReal_ofNat, ENNReal.ofReal_one] using h.ennrealOfReal
  exact memLp_one_iff_integrable.mp ((ForcingContinuity.forcing_memLp hH hu).star.fun_mul hh)

/-- Actual real directional derivative of the Hartree interaction, from L6 alone. -/
theorem actual_hartree_energy_hasDerivAt {α c : ℝ} (hH : OrdinaryHLS α c)
    {u h : Space → ℂ} (hu : MemLp u 6 volume) (hh : MemLp h 6 volume) :
    HasDerivAt (fun t => ∫ x, potential α c (affinePath u h t) x *
        powerDensity α (affinePath u h t) x)
      ((2*(3+α)) * (∫ x, star (forcing α c u x) * h x).re) 0 := by
  have he := (actual_pair_energy_hasDerivAt hH hu hh).2
  have hformula : (∫ q, pairVariation α c u h q ∂volume.prod volume) =
      (2*(3+α)) * (∫ x, star (forcing α c u x) * h x).re := by
    rw [pairVariation_integral_eq hH hu hh]
    simp_rw [potential_densityVariation_eq]
    have hre : (∫ x, (star (forcing α c u x) * h x).re) =
        (∫ x, star (forcing α c u x) * h x).re :=
      integral_re (forcing_pairing_integrable hH hu hh)
    rw [integral_const_mul, hre]
    ring
  rw [hformula] at he
  have hfun : (fun t => ∫ x, potential α c (affinePath u h t) x *
      powerDensity α (affinePath u h t) x) =
      (fun t => ∫ q, PressureDomain.rieszPairDensity α c (affinePath u h t) q
        ∂volume.prod volume) := by
    funext t
    exact (PressureDomain.hartree_energy_pair_identity hH (hu.add (hh.const_smul t))).symm
  rw [hfun]
  exact he

/-- The paper's original B, with precisely its standard Riesz normalization and p=3+α. -/
theorem interaction_hasDerivAt {α : ℝ}
    (hH : OrdinaryHLS α (HeatRiesz.standardRieszConstant α))
    {u h : Space → ℂ} (hu : MemLp u 6 volume) (hh : MemLp h 6 volume) :
    HasDerivAt (fun t => DirectionalCoercivity.interaction α (affinePath u h t))
      ((2*(3+α)) * (∫ x, star (forcing α (HeatRiesz.standardRieszConstant α) u x) * h x).re) 0 :=
  actual_hartree_energy_hasDerivAt hH hu hh

#print axioms actual_bilinear_symmetry
#print axioms densityVariation_formula
#print axioms density_along_path_hasDerivAt
#print axioms envelope_memLp
#print axioms norm_envelope
#print axioms norm_affinePath_le_envelope
#print axioms densityVariation_bound
#print axioms densityVariation_measurable
#print axioms powerDensity_path_bound
#print axioms pair_along_path_hasDerivAt
#print axioms pairVariation_measurable
#print axioms pairVariation_bound
#print axioms actual_pair_energy_hasDerivAt
#print axioms pairHalf_bound
#print axioms pairHalf_integrable
#print axioms pairVariation_eq_halves
#print axioms pairVariation_integral_eq
#print axioms potential_densityVariation_eq
#print axioms forcing_pairing_integrable
#print axioms actual_hartree_energy_hasDerivAt
#print axioms interaction_hasDerivAt
end HartreeF.EnergyVariation
