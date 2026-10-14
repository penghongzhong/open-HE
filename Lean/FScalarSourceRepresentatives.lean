import FContinuousScalarSource
import FJointLpRepresentatives

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory
open scoped ENNReal
namespace HartreeF.LocalScalarSource
open EnergySpace ForcingDomain ForcingContinuity TimeHolder

theorem potential_eq_of_ae {alpha c : ℝ} {f g : Space → ℂ}
    (hfg : f =ᵐ[volume] g) : potential alpha c f = potential alpha c g := by
  funext x
  apply integral_congr_ae
  filter_upwards [hfg] with y hy
  simp only [powerDensity, hy]

theorem forcing_ae_of_ae {alpha c : ℝ} {f g : Space → ℂ}
    (hfg : f =ᵐ[volume] g) : forcing alpha c f =ᵐ[volume] forcing alpha c g := by
  have hp := potential_eq_of_ae (alpha := alpha) (c := c) hfg
  filter_upwards [hfg] with x hx
  change potential alpha c f x • (‖f x‖ ^ (1 + alpha) • f x) =
    potential alpha c g x • (‖g x‖ ^ (1 + alpha) • g x)
  rw [hp, hx]

variable {T : Type*} [TopologicalSpace T] [CompactSpace T]
    [MeasurableSpace T] [BorelSpace T] [SecondCountableTopology T]
    (mu : Measure T) [IsFiniteMeasure mu]

/-- Finite scalar forcing norm transfers to every actual representative of the path. -/
theorem represented_forcing_mixedNorm {alpha c : ℝ} (hH : OrdinaryHLS alpha c)
    (u : C(T, EnergyState)) (f : T → Space → ℂ)
    (hf : ∀ᵐ t ∂mu, f t =ᵐ[volume] energyValue (u t)) :
    mixedNorm mu volume 2 (ENNReal.ofReal (6/5 : ℝ))
      (fun t => forcing alpha c (f t)) = ‖scalarSource mu hH u‖ₑ := by
  rw [← forcing_mixedNorm_eq mu hH u]
  apply eLpNorm_congr_ae
  filter_upwards [hf] with t ht
  exact eLpNorm_congr_ae (forcing_ae_of_ae ht)

theorem represented_forcing_mixedNorm_ne_top {alpha c : ℝ} (hH : OrdinaryHLS alpha c)
    (u : C(T, EnergyState)) (f : T → Space → ℂ)
    (hf : ∀ᵐ t ∂mu, f t =ᵐ[volume] energyValue (u t)) :
    mixedNorm mu volume 2 (ENNReal.ofReal (6/5 : ℝ))
      (fun t => forcing alpha c (f t)) ≠ ∞ := by
  rw [represented_forcing_mixedNorm mu hH u f hf]
  exact enorm_ne_top

theorem represented_scalarSource_coeFn {alpha c : ℝ} (hH : OrdinaryHLS alpha c)
    (u : C(T, EnergyState)) (f : T → Space → ℂ)
    (hf : ∀ᵐ t ∂mu, f t =ᵐ[volume] energyValue (u t)) :
    ∀ᵐ t ∂mu, scalarSource mu hH u t =ᵐ[volume] forcing alpha c (f t) := by
  filter_upwards [scalarSource_coeFn mu hH u, hf] with t hsrc hval
  exact Filter.EventuallyEq.trans hsrc
    (forcing_ae_of_ae (alpha := alpha) (c := c) hval).symm

/-- This source producer constructs its own jointly measurable value representative. -/
theorem exists_joint_value_and_scalar_source {alpha c : ℝ} (hH : OrdinaryHLS alpha c)
    (u : C(T, EnergyState)) :
    ∃ f : T × Space → ℂ,
      StronglyMeasurable f ∧
      (∀ᵐ t ∂mu, (fun x => f (t,x)) =ᵐ[volume] energyValue (u t)) ∧
      (∀ᵐ t ∂mu, scalarSource mu hH u t =ᵐ[volume]
        forcing alpha c (fun x => f (t,x))) ∧
      mixedNorm mu volume 2 (ENNReal.ofReal (6/5 : ℝ))
        (fun t => forcing alpha c (fun x => f (t,x))) ≠ ∞ := by
  have hg : AEStronglyMeasurable (fun t => energyValue (u t)) mu :=
    (energyValue.continuous.comp u.continuous).aestronglyMeasurable
  let f := aeJointLpRepresentative mu volume 6 (fun t => energyValue (u t)) hg
  have hf : ∀ᵐ t ∂mu, (fun x => f (t,x)) =ᵐ[volume] energyValue (u t) :=
    aeJointLpRepresentative_slice mu volume 6 (fun t => energyValue (u t)) hg
  exact ⟨f, aeJointLpRepresentative_stronglyMeasurable mu volume 6 _ hg, hf,
    represented_scalarSource_coeFn mu hH u (fun t x => f (t,x)) hf,
    represented_forcing_mixedNorm_ne_top mu hH u (fun t x => f (t,x)) hf⟩

end HartreeF.LocalScalarSource
