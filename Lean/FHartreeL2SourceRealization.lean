import FHartreeL2Time

noncomputable section
set_option autoImplicit false
set_option warningAsError true
open MeasureTheory
open scoped ENNReal NNReal
namespace HartreeF.ForcingL2
open ForcingDomain TimeHolder
attribute [local instance] l2FiniteExponent

variable {T : Type*} [MeasurableSpace T]
    (mu : Measure T) [SigmaFinite mu] {alpha c : ℝ} (hH : OrdinaryHLS alpha c)
    (u : T → Space → ℂ)
    (hu : AEStronglyMeasurable (fun z : T × Space => u z.1 z.2) (mu.prod volume))
    (hs : ∀ᵐ t ∂mu, MemLp (u t) 6 volume ∧ MemLp (u t) 10 volume)
    (hE : mixedNorm mu volume ∞ 6 u ≠ ∞) (hS : mixedNorm mu volume 10 10 u ≠ ∞)

/-- The constructed L²_t(L²_x) class represents the literal nonlinearity. -/
theorem l2Source_coeFn :
    ∀ᵐ t ∂mu, ∀ᵐ x ∂volume, l2Source mu hH u hu hs hE hS t x = forcing alpha c (u t) x :=
  jointLpRealization_coeFn mu volume 2 2
    (fun z : T × Space => forcing alpha c (u z.1) z.2)
    (joint_forcing_measurable mu alpha c u hu)
    (hs.mono fun t ht => forcing_l2_memLp (u := u t) hH ht.1 ht.2)
    (forcing_l2_mixed_finite mu hH u hu hs hE hS)

/-- Its genuine Bochner norm is exactly the literal extended mixed norm. -/
theorem l2Source_enorm :
    ‖l2Source mu hH u hu hs hE hS‖ₑ =
      mixedNorm mu volume 2 2 (fun t => forcing alpha c (u t)) :=
  jointLpRealization_enorm mu volume 2 2
    (fun z : T × Space => forcing alpha c (u z.1) z.2)
    (joint_forcing_measurable mu alpha c u hu)
    (hs.mono fun t ht => forcing_l2_memLp (u := u t) hH ht.1 ht.2)
    (forcing_l2_mixed_finite mu hH u hu hs hE hS)

#print axioms l2Source_coeFn
#print axioms l2Source_enorm
end HartreeF.ForcingL2
