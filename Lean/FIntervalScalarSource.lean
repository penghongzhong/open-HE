import FIntervalTimeTransport
import FScalarDifferenceSource
import FEndpointTimeExtension

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory Filter
open scoped ENNReal Topology
namespace HartreeF.ActualDuhamelPath
open CriticalPathSpace IntervalTimeTransport EnergySpace LocalScalarSource ForcingDomain TimeHolder

/-- The source on real restricted time is constructed from the actual CriticalPath. -/
def intervalScalarSource {a b alpha c : ℝ} (hab : a ≤ b)
    (hH : OrdinaryHLS alpha c) (u : CriticalPath (intervalMeasure a b)) :
    Retarded.LocalEndpointSource (Set.Icc a b) :=
  toLocalLp hab 2 (scalarSource (intervalMeasure a b) hH (energyPath _ u))

theorem intervalScalarSource_norm {a b alpha c : ℝ} (hab : a ≤ b)
    (hH : OrdinaryHLS alpha c) (u : CriticalPath (intervalMeasure a b)) :
    ‖intervalScalarSource hab hH u‖ =
      ‖scalarSource (intervalMeasure a b) hH (energyPath _ u)‖ :=
  toLocalLp_norm hab 2 _

theorem intervalScalarSource_coeFn {a b alpha c : ℝ} (hab : a ≤ b)
    (hH : OrdinaryHLS alpha c) (u : CriticalPath (intervalMeasure a b)) :
    ∀ᵐ t ∂localMeasure a b, ∀ᵐ x ∂(volume : Measure Space),
      intervalScalarSource hab hH u t x =
        forcing alpha c (energyValue (extendEnergyPath hab (energyPath _ u) t)) x := by
  filter_upwards [toLocalLp_coeFn hab 2 (scalarSource (intervalMeasure a b) hH (energyPath _ u)),
    ae_clamp hab (scalarSource_coeFn (intervalMeasure a b) hH (energyPath _ u))] with t ht hs
  change ∀ᵐ x ∂(volume : Measure Space),
    toLocalLp hab 2 (scalarSource (intervalMeasure a b) hH (energyPath _ u)) t x = _
  rw [ht]
  exact hs

/-- Any jointly selected value field for this very path uses this same scalar source. -/
theorem intervalScalarSource_representative {a b alpha c : ℝ} (hab : a ≤ b)
    (hH : OrdinaryHLS alpha c) (u : CriticalPath (intervalMeasure a b))
    (f : Set.Icc a b → Space → ℂ)
    (hf : ∀ᵐ t ∂intervalMeasure a b, f t =ᵐ[volume] energyValue (energyPath _ u t)) :
    ∀ᵐ t ∂localMeasure a b, intervalScalarSource hab hH u t =ᵐ[volume]
      forcing alpha c (f (Set.projIcc a b hab t)) := by
  filter_upwards [intervalScalarSource_coeFn hab hH u, ae_clamp hab hf] with t hs ht
  exact Filter.EventuallyEq.trans hs (forcing_ae_of_ae (alpha := alpha) (c := c) ht).symm

/-- Finiteness of the literal local forcing comes from compact-time continuity,
not from a source-norm premise. -/
theorem interval_forcing_mixedNorm_finite {a b alpha c : ℝ} (hab : a ≤ b)
    (hH : OrdinaryHLS alpha c) (u : CriticalPath (intervalMeasure a b))
    (f : Set.Icc a b → Space → ℂ)
    (hf : ∀ᵐ t ∂intervalMeasure a b, f t =ᵐ[volume] energyValue (energyPath _ u t)) :
    mixedNorm (localMeasure a b) volume 2 (ENNReal.ofReal (6/5 : ℝ))
      (fun t => forcing alpha c (f (Set.projIcc a b hab t))) ≠ ∞ := by
  change eLpNorm (fun t => eLpNorm
    (forcing alpha c (f (Set.projIcc a b hab t))) (ENNReal.ofReal (6/5 : ℝ)) volume)
    2 (localMeasure a b) ≠ ∞
  rw [eLpNorm_clamp hab 2 (fun t => eLpNorm (forcing alpha c (f t))
    (ENNReal.ofReal (6/5 : ℝ)) volume)]
  exact represented_forcing_mixedNorm_ne_top (intervalMeasure a b) hH (energyPath _ u) f hf

/-- The scalar difference source is produced before any retarded target is constructed. -/
theorem intervalScalarDifferenceSource_coeFn {a b alpha c : ℝ} (hab : a ≤ b)
    (hH : OrdinaryHLS alpha c) (u v : CriticalPath (intervalMeasure a b))
    (f g : Set.Icc a b → Space → ℂ)
    (hf : ∀ᵐ t ∂intervalMeasure a b, f t =ᵐ[volume] energyValue (energyPath _ u t))
    (hg : ∀ᵐ t ∂intervalMeasure a b, g t =ᵐ[volume] energyValue (energyPath _ v t)) :
    ∀ᵐ t ∂localMeasure a b, ∀ᵐ x ∂(volume : Measure Space),
      (intervalScalarSource hab hH u - intervalScalarSource hab hH v) t x =
        forcing alpha c (f (Set.projIcc a b hab t)) x -
          forcing alpha c (g (Set.projIcc a b hab t)) x := by
  filter_upwards [Lp.coeFn_sub (intervalScalarSource hab hH u) (intervalScalarSource hab hH v),
    intervalScalarSource_representative hab hH u f hf,
    intervalScalarSource_representative hab hH v g hg] with t ht hu hv
  rw [ht]
  filter_upwards [Lp.coeFn_sub (intervalScalarSource hab hH u t)
    (intervalScalarSource hab hH v t), hu, hv] with x hx hux hvx
  simpa only [Pi.sub_apply, hux, hvx] using hx

end HartreeF.ActualDuhamelPath
