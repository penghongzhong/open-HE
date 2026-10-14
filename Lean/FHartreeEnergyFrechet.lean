import FHartreeEnergyDirectional
import FRealDirectionalFrechet
import Mathlib.MeasureTheory.Function.Holder

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Set
open scoped ENNReal Topology
namespace HartreeF.EnergyVariation
open ForcingDomain ForcingContinuity

local instance : Fact (1 ≤ ENNReal.ofReal (6/5 : ℝ)) := ⟨by norm_num⟩
local instance : ENNReal.HolderConjugate (ENNReal.ofReal (6/5 : ℝ)) 6 := by
  have h : Real.HolderTriple (6/5) 6 1 := by constructor <;> norm_num
  simpa only [ENNReal.ofReal_ofNat, ENNReal.ofReal_one] using h.ennrealOfReal

abbrev EnergyL6 := Lp ℂ 6 (volume : Measure Space)

/-- The same literal Hartree interaction evaluated on the L6 representative. -/
def interactionLp (α : ℝ) (u : EnergyL6) : ℝ := DirectionalCoercivity.interaction α u

theorem potential_congr_ae (α c : ℝ) {u v : Space → ℂ} (h : u =ᵐ[volume] v) :
    potential α c u = potential α c v := by
  funext x
  apply integral_congr_ae
  filter_upwards [h] with y hy
  simp only [powerDensity, hy]

theorem interaction_congr_ae (α : ℝ) {u v : Space → ℂ} (h : u =ᵐ[volume] v) :
    DirectionalCoercivity.interaction α u = DirectionalCoercivity.interaction α v := by
  unfold DirectionalCoercivity.interaction
  rw [potential_congr_ae α (HeatRiesz.standardRieszConstant α) h]
  apply integral_congr_ae
  filter_upwards [h] with x hx
  simp only [powerDensity, hx]

/-- The real dual vector is represented by the actual L^(6/5) Hartree forcing. -/
def hartreeDerivative {α : ℝ}
    (hH : OrdinaryHLS α (HeatRiesz.standardRieszConstant α))
    (u : EnergyL6) : EnergyL6 →L[ℝ] ℝ :=
  (2*(3+α)) • ((innerSL ℝ (E := ℂ)).lpPairing volume
    (ENNReal.ofReal (6/5 : ℝ)) 6 (forcingLp hH u))

theorem hartreeDerivative_apply {α : ℝ}
    (hH : OrdinaryHLS α (HeatRiesz.standardRieszConstant α))
    (u h : EnergyL6) :
    hartreeDerivative hH u h = (2*(3+α)) *
      (∫ x, star (forcing α (HeatRiesz.standardRieszConstant α) u x) * h x).re := by
  change (2*(3+α)) * ((innerSL ℝ (E := ℂ)).lpPairing volume
    (ENNReal.ofReal (6/5 : ℝ)) 6 (forcingLp hH u) h) = _
  rw [ContinuousLinearMap.lpPairing_eq_integral]
  congr 1
  have hrep : forcingLp hH u =ᵐ[volume]
      forcing α (HeatRiesz.standardRieszConstant α) u :=
    (forcing_memLp hH (Lp.memLp u)).coeFn_toLp
  calc
    _ = ∫ x, (star (forcing α (HeatRiesz.standardRieszConstant α) u x) * h x).re := by
      apply integral_congr_ae
      filter_upwards [hrep] with x hx
      change inner ℝ (forcingLp hH u x) (h x) = _
      rw [hx, Complex.inner]
      simp only [Complex.star_def, mul_comm]
    _ = _ := integral_re (forcing_pairing_integrable hH (Lp.memLp u) (Lp.memLp h))

theorem hartreeDerivative_continuous {α : ℝ}
    (hH : OrdinaryHLS α (HeatRiesz.standardRieszConstant α)) :
    Continuous (hartreeDerivative hH) := by
  unfold hartreeDerivative
  exact ((((innerSL ℝ (E := ℂ)).lpPairing volume
    (ENNReal.ofReal (6/5 : ℝ)) 6).continuous.comp
    (forcingLp_continuous hH))).const_smul (2*(3+α))

theorem affinePath_coe_ae (u h : EnergyL6) (t : ℝ) :
    (⇑(u+t • h)) =ᵐ[volume] affinePath u h t := by
  filter_upwards [Lp.coeFn_add u (t • h), Lp.coeFn_smul t h] with x hx hy
  simpa only [affinePath, Pi.add_apply, Pi.smul_apply, hy] using hx

theorem interactionLp_line_hasDerivAt {α : ℝ}
    (hH : OrdinaryHLS α (HeatRiesz.standardRieszConstant α))
    (u h : EnergyL6) :
    HasDerivAt (fun t : ℝ => interactionLp α (u+t • h)) (hartreeDerivative hH u h) 0 := by
  rw [hartreeDerivative_apply]
  apply (interaction_hasDerivAt hH (Lp.memLp u) (Lp.memLp h)).congr_of_eventuallyEq
  exact Eventually.of_forall (fun t => interaction_congr_ae α (affinePath_coe_ae u h t))

/-- Actual C1 Hartree energy calculus on L6, with no mass, variance, or derivative premise. -/
theorem interactionLp_hasFDerivAt {α : ℝ}
    (hH : OrdinaryHLS α (HeatRiesz.standardRieszConstant α)) (u : EnergyL6) :
    HasFDerivAt (interactionLp α) (hartreeDerivative hH u) u :=
  hasFDerivAt_of_continuous_directional (interactionLp_line_hasDerivAt hH) u
    (hartreeDerivative_continuous hH).continuousAt

theorem interactionLp_contDiff_one {α : ℝ}
    (hH : OrdinaryHLS α (HeatRiesz.standardRieszConstant α)) :
    ContDiff ℝ 1 (interactionLp α) :=
  contDiff_one_iff_hasFDerivAt.mpr
    ⟨hartreeDerivative hH, hartreeDerivative_continuous hH, interactionLp_hasFDerivAt hH⟩

/-- Chain rule for every actual real differentiable L6 curve. -/
theorem interactionLp_curve_hasDerivAt {α : ℝ}
    (hH : OrdinaryHLS α (HeatRiesz.standardRieszConstant α))
    {u : ℝ → EnergyL6} {du : EnergyL6} {t : ℝ} (hu : HasDerivAt u du t) :
    HasDerivAt (fun s => interactionLp α (u s))
      ((2*(3+α)) * (∫ x, star (forcing α (HeatRiesz.standardRieszConstant α) (u t) x) * du x).re) t := by
  rw [← hartreeDerivative_apply]
  exact (interactionLp_hasFDerivAt hH (u t)).comp_hasDerivAt t hu

/-- The paper's 1/(2p) normalization cancels exactly in the actual curve derivative. -/
theorem normalizedInteractionLp_curve_hasDerivAt {α : ℝ}
    (hH : OrdinaryHLS α (HeatRiesz.standardRieszConstant α))
    {u : ℝ → EnergyL6} {du : EnergyL6} {t : ℝ} (hu : HasDerivAt u du t) :
    HasDerivAt (fun s => interactionLp α (u s)/(2*(3+α)))
      (∫ x, star (forcing α (HeatRiesz.standardRieszConstant α) (u t) x) * du x).re t := by
  have hp : 2*(3+α) ≠ 0 := by nlinarith [hH.order_pos]
  convert (interactionLp_curve_hasDerivAt hH hu).div_const (2*(3+α)) using 1
  exact (mul_div_cancel_left₀ _ hp).symm

/-- Actual Hartree derivative after any bounded real linear regularizer into L6. -/
theorem regularizedInteraction_hasFDerivAt {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {α : ℝ}
    (hH : OrdinaryHLS α (HeatRiesz.standardRieszConstant α))
    (P : E →L[ℝ] EnergyL6) (v : E) :
    HasFDerivAt (fun w => interactionLp α (P w))
      ((hartreeDerivative hH (P v)).comp P) v :=
  (interactionLp_hasFDerivAt hH (P v)).comp v P.hasFDerivAt

#print axioms potential_congr_ae
#print axioms interaction_congr_ae
#print axioms hartreeDerivative_apply
#print axioms hartreeDerivative_continuous
#print axioms affinePath_coe_ae
#print axioms interactionLp_line_hasDerivAt
#print axioms interactionLp_hasFDerivAt
#print axioms interactionLp_contDiff_one
#print axioms interactionLp_curve_hasDerivAt
#print axioms normalizedInteractionLp_curve_hasDerivAt
#print axioms regularizedInteraction_hasFDerivAt
end HartreeF.EnergyVariation
