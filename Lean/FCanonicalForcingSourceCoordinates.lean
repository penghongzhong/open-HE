import FCanonicalPathCriticalSlices
import FActualHartreeDuhamelMap

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
open MeasureTheory Filter Set LineDeriv
open scoped ENNReal RealInnerProductSpace
namespace HartreeF.NonlinearAffine
open EnergySpace CriticalPathSpace CriticalTimeSobolev SobolevStretch StationarySelfTest
open WeakHartreeProduct ForcingDomain TimeHolder Retarded ActualDuhamelPath IntervalTimeTransport
open AffineForcingIndependentReview
attribute [local irreducible] energySubmodule criticalPathSubmodule energyPath criticalPathIntervalSource
local instance : Fact (1 ≤ ENNReal.ofReal (6/5:ℝ)) := ⟨by norm_num⟩

/-- The literal canonical complex forcing-gradient coordinate. -/
def canonicalForcingCoordinate (alpha kernel : ℝ) (v : EnergyState) (j : Fin 3) : Space → ℂ :=
  directionalField (canonicalForcingGradientRe alpha kernel v)
    (canonicalForcingGradientIm alpha kernel v) (coordinate j)

theorem canonicalForcingCoordinate_actual (alpha kernel : ℝ) (v : EnergyState)
    (j : Fin 3) (x : Space) :
    canonicalForcingCoordinate alpha kernel v j x =
      actualFullGradient alpha kernel (energyValue v)
        (energyProjectedGradient Complex.reCLM v) (energyProjectedGradient Complex.imCLM v) x j := by
  simp only [canonicalForcingCoordinate,directionalField,canonicalForcingGradientRe,
    canonicalForcingGradientIm,coordinate,← EuclideanSpace.basisFun_apply,
    EuclideanSpace.inner_basisFun_real,actualFullGradient_coordinate]

/-- Existing scalar-class compatibility and genuine weak derivatives identify
the actual gradient class. The representative equality is a conclusion. -/
theorem source_coordinate_ae_of_weakGradients
    (f g : SourceSpace) (w : Space → ℂ) (U V : Space → Space)
    (hf : (f : Space → ℂ) =ᵐ[volume] w)
    (hU : MemLp U (ENNReal.ofReal (6/5:ℝ)) volume)
    (hV : MemLp V (ENNReal.ofReal (6/5:ℝ)) volume)
    (hR : HasWeakGradient (fun x => (w x).re) U)
    (hI : HasWeakGradient (fun x => (w x).im) V)
    (j : Fin 3)
    (hder : ∂_{coordinate j} (Lp.toTemperedDistribution f)=Lp.toTemperedDistribution g) :
    (g : Space → ℂ) =ᵐ[volume] directionalField U V (coordinate j) := by
  have hw : MemLp w (ENNReal.ofReal (6/5:ℝ)) volume := (Lp.memLp f).ae_eq hf
  have he : hw.toLp w=f := Lp.ext (hw.coeFn_toLp.trans hf.symm)
  have hd := weak_gradient_tempered_derivative hw hU hV hR hI (coordinate j)
  rw [he] at hd
  exact (spatial_ae_eq_of_distribution_eq g _ (hder.symm.trans hd)).trans
    (directionalField_memLp hU hV (coordinate j)).coeFn_toLp

/-- The actual nonlinear source built from a CriticalPath has the canonical
forcing-gradient coordinates. All critical slice domains are produced. -/
theorem canonical_path_source_gradient_ae (hDensity : OrdinaryH1Density)
    {K alpha kernel A B : ℝ} (hSob : OrdinarySobolev K) (hH : OrdinaryHLS alpha kernel)
    (hAB : A≤B) (u : CriticalPath (intervalMeasure A B)) :
    ∀ᵐ t ∂localMeasure A B, ∀ j : Fin 3,
      ((criticalPathIntervalSource hDensity hSob hH hAB u 0).gradient j t : Space → ℂ) =ᵐ[volume]
        canonicalForcingCoordinate alpha kernel (extendEnergyPath hAB (energyPath _ u) t) j := by
  filter_upwards [canonical_local_critical_slices hDensity hSob hAB u,
    criticalPathIntervalSource_single_coeFn hDensity hSob hH hAB u,
    (criticalPathIntervalSource hDensity hSob hH hAB u 0).derivative] with t hs hf hd
  intro j
  have hw := hartree_forcing_weak_gradients hDensity hSob hH
    (energyState_inDotH1 (extendEnergyPath hAB (energyPath _ u) t)) hs.1 hs.2.1 hs.2.2
  have hm := hartree_forcing_gradient_domains hH (Lp.memLp _) hs.1 hs.2.1 hs.2.2
  exact source_coordinate_ae_of_weakGradients _ _ _ _ _ hf hm.1 hm.2 hw.1 hw.2 j (hd j)

#print axioms canonicalForcingCoordinate
#print axioms canonicalForcingCoordinate_actual
#print axioms source_coordinate_ae_of_weakGradients
#print axioms canonical_path_source_gradient_ae
end HartreeF.NonlinearAffine
