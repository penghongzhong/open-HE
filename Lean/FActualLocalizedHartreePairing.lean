import FActualCutoffH1Localization
import GaugeReality
import ForcingLpMap

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 600000
open MeasureTheory Filter Set
open scoped ENNReal Topology
namespace HartreeF.LocalChargeBridge
open EnergySpace ForcingDomain ForcingContinuity WeakCutoffLp
attribute [local irreducible] energySubmodule

/-- The literal original Hartree pairing with a real spatial coefficient. -/
def localizedHartreePair (α c : ℝ) (χ : V → ℝ) (u : EnergyState) : ℂ :=
  ∫ x : V, (χ x : ℂ) * forcing α c (energyValue u) x * star (energyValue u x)

theorem localizedHartreePair_integrable {α c : ℝ} (hH : OrdinaryHLS α c)
    {χ : V → ℝ} (hχ : Continuous χ) (hc : HasCompactSupport χ) (u : EnergyState) :
    Integrable (fun x : V => (χ x : ℂ) * forcing α c (energyValue u) x *
      star (energyValue u x)) volume := by
  have hi := forcing_mass_pairing_integrable hH (Lp.memLp (energyValue u))
  have hm := cutoff_smul_memLp hχ hc (memLp_one_iff_integrable.mpr hi)
  apply (memLp_one_iff_integrable.mp hm).congr
  filter_upwards [] with x
  simp only [Complex.real_smul, mul_assoc]

theorem localizedHartreePair_real {α c : ℝ} (hα : 0 < α)
    (χ : V → ℝ) (u : EnergyState) :
    localizedHartreePair α c χ u =
      ((∫ x : V, χ x * (potential α c (energyValue u) x * powerDensity α (energyValue u) x) : ℝ) : ℂ) := by
  unfold localizedHartreePair
  calc
    _ = ∫ x : V, ((χ x * (potential α c (energyValue u) x * powerDensity α (energyValue u) x) : ℝ) : ℂ) := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [mul_assoc, forcing_gauge_pair hα]
      push_cast
      rfl
    _ = _ := integral_complex_ofReal

/-- Cancellation comes together with its genuine spatial integrability proof. -/
theorem actual_localized_hartree_cancellation {α c : ℝ} (hH : OrdinaryHLS α c)
    {χ : V → ℝ} (hχ : Continuous χ) (hc : HasCompactSupport χ) (u : EnergyState) :
    Integrable (fun x : V => (χ x : ℂ) * forcing α c (energyValue u) x *
      star (energyValue u x)) volume ∧
    (localizedHartreePair α c χ u).im = 0 ∧
    (Complex.I * localizedHartreePair α c χ u).re = 0 := by
  refine ⟨localizedHartreePair_integrable hH hχ hc u, ?_, ?_⟩ <;>
    rw [localizedHartreePair_real hH.order_pos] <;> simp

/-- The L6 localized value used in the actual dual pairing. -/
def cutoffL6L6 {χ : V → ℝ} (hχ : Continuous χ) (hc : HasCompactSupport χ) : L6 →L[ℂ] L6 :=
  (ContinuousLinearMap.mul ℂ ℂ).holderL volume ∞ 6 6 (coefficientLp hχ hc ∞)

theorem cutoffL6L6_ae {χ : V → ℝ} (hχ : Continuous χ) (hc : HasCompactSupport χ)
    (u : L6) : (cutoffL6L6 hχ hc u : V → ℂ) =ᵐ[volume] fun x => χ x • u x := by
  filter_upwards [(ContinuousLinearMap.mul ℂ ℂ).coeFn_holder
    (r := 6) (coefficientLp hχ hc ∞) u, coefficientLp_ae hχ hc ∞] with x hx hcχ
  exact hx.trans (by rw [hcχ]; rfl)

local instance source_ge_one : Fact (1 ≤ ENNReal.ofReal (6/5 : ℝ)) := ⟨by norm_num⟩
local instance source_holder : ENNReal.HolderConjugate (ENNReal.ofReal (6/5 : ℝ)) 6 := by
  constructor
  apply (ENNReal.toReal_eq_toReal_iff' (by simp) (by simp)).mp
  rw [ENNReal.toReal_add (by simp) (by simp)]
  norm_num

/-- Native continuity of the actual finite Hartree pairing, before any imaginary-part cancellation. -/
theorem localizedHartreePair_continuous {α c : ℝ} (hH : OrdinaryHLS α c)
    {χ : V → ℝ} (hχ : Continuous χ) (hc : HasCompactSupport χ) :
    Continuous (localizedHartreePair α c χ) := by
  let conjMap := (Complex.conjCLE : ℂ →L[ℝ] ℂ).compLpL 6 (volume : Measure V)
  let pair := (ContinuousLinearMap.mul ℝ ℂ).lpPairing (volume : Measure V) (ENNReal.ofReal (6/5 : ℝ)) 6
  have he (u : EnergyState) : localizedHartreePair α c χ u =
      pair (forcingLp hH (energyValue u)) (conjMap (cutoffL6L6 hχ hc (energyValue u))) := by
    rw [ContinuousLinearMap.lpPairing_eq_integral]
    apply integral_congr_ae
    filter_upwards [(ForcingContinuity.forcing_memLp hH (Lp.memLp (energyValue u))).coeFn_toLp,
      (Complex.conjCLE : ℂ →L[ℝ] ℂ).coeFn_compLpL (cutoffL6L6 hχ hc (energyValue u)),
      cutoffL6L6_ae hχ hc (energyValue u)] with x hf hconj hcut
    change (χ x : ℂ) * forcing α c (energyValue u) x * star (energyValue u x) =
      forcingLp hH (energyValue u) x * conjMap (cutoffL6L6 hχ hc (energyValue u)) x
    rw [show forcingLp hH (energyValue u) x = forcing α c (energyValue u) x from hf,
      show conjMap (cutoffL6L6 hχ hc (energyValue u)) x = _ from hconj, hcut]
    change (χ x : ℂ) * forcing α c (energyValue u) x * star (energyValue u x) =
      forcing α c (energyValue u) x * star (χ x • energyValue u x)
    apply Complex.ext <;> simp [Complex.real_smul, Complex.mul_re, Complex.mul_im] <;> ring
  change Continuous (fun u => localizedHartreePair α c χ u)
  simp_rw [he]
  exact (pair.continuous.comp ((forcingLp_continuous hH).comp energyValue.continuous)).clm_apply
    (conjMap.continuous.comp ((cutoffL6L6 hχ hc).continuous.comp energyValue.continuous))

theorem localizedHartreePair_time_integrable {α c : ℝ} (hH : OrdinaryHLS α c)
    {χ : V → ℝ} (hχ : Continuous χ) (hc : HasCompactSupport χ)
    {u : ℝ → EnergyState} {a b : ℝ} (hu : ContinuousOn u (Icc a b)) :
    IntegrableOn (fun t => localizedHartreePair α c χ (u t)) (Icc a b) volume :=
  ((localizedHartreePair_continuous hH hχ hc).comp_continuousOn hu).integrableOn_Icc

end HartreeF.LocalChargeBridge
