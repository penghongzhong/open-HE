import DotH1GradientTopology

noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal
namespace HartreeF.EnergyContinuity
open ForcingDomain SharpOrdinary DirectionalCoercivity

/-- The literal quadratic double integral in the ordinary sharp HLS interface. -/
def rieszQuadratic (α : ℝ) (f : Space → ℝ) : ℝ :=
  ∫ q, bilinearRieszPair α f f q ∂volume.prod volume

/-- Polarization of the actual double integral, after producing both mixed domains. -/
theorem rieszQuadratic_sub {α : ℝ} (hH : SharpOrdinaryHLS α)
    {f g : Space → ℝ}
    (hf : MemLp f (ENNReal.ofReal (densityExponent α)) volume)
    (hg : MemLp g (ENNReal.ofReal (densityExponent α)) volume) :
    rieszQuadratic α f-rieszQuadratic α g =
      (∫ q, bilinearRieszPair α (f-g) f q ∂volume.prod volume) +
      (∫ q, bilinearRieszPair α g (f-g) q ∂volume.prod volume) := by
  have hff := (hH.bound f f hf hf).1
  have hgg := (hH.bound g g hg hg).1
  have hdf := (hH.bound (f-g) f (hf.sub hg) hf).1
  have hgd := (hH.bound g (f-g) hg (hf.sub hg)).1
  rw [rieszQuadratic, rieszQuadratic, ← integral_sub hff hgg, ← integral_add hdf hgd]
  apply integral_congr_ae
  filter_upwards [] with q
  simp only [bilinearRieszPair, Pi.sub_apply]
  ring

/-- Quantitative actual double-integral continuity with no assumed target bound. -/
theorem rieszQuadratic_difference_bound {α : ℝ} (hH : SharpOrdinaryHLS α)
    {f g : Space → ℝ}
    (hf : MemLp f (ENNReal.ofReal (densityExponent α)) volume)
    (hg : MemLp g (ENNReal.ofReal (densityExponent α)) volume) :
    |rieszQuadratic α f-rieszQuadratic α g| ≤
      sharpHLSConstant α * (eLpNorm (f-g) (ENNReal.ofReal (densityExponent α)) volume).toReal *
        ((eLpNorm f (ENNReal.ofReal (densityExponent α)) volume).toReal +
          (eLpNorm g (ENNReal.ofReal (densityExponent α)) volume).toReal) := by
  rw [rieszQuadratic_sub hH hf hg]
  refine (abs_add_le _ _).trans ?_
  have h1 := (hH.bound (f-g) f (hf.sub hg) hf).2
  have h2 := (hH.bound g (f-g) hg (hf.sub hg)).2
  calc
    _ ≤ _ := add_le_add h1 h2
    _ = _ := by ring

/-- The physical iterated interaction agrees with the actual quadratic pair integral. -/
theorem interaction_eq_rieszQuadratic {α : ℝ}
    (hOrd : OrdinaryHLS α (HeatRiesz.standardRieszConstant α))
    {u : Space → ℂ} (hu : MemLp u 6 volume) :
    interaction α u = rieszQuadratic α (powerDensity α u) := by
  unfold interaction rieszQuadratic
  rw [← PressureDomain.hartree_energy_pair_identity hOrd hu]
  apply integral_congr_ae
  filter_upwards [] with q
  unfold bilinearRieszPair PressureDomain.rieszPairDensity
  ring

#print axioms rieszQuadratic_sub
#print axioms rieszQuadratic_difference_bound
#print axioms interaction_eq_rieszQuadratic
end HartreeF.EnergyContinuity
