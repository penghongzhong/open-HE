import FCanonicalForcingSourceCoordinates
import FActualAffineCriticalPath

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2200000
open MeasureTheory Filter Set LineDeriv
open scoped ENNReal RealInnerProductSpace
namespace HartreeF.NonlinearAffine
open EnergySpace CriticalPathSpace CriticalTimeSobolev SobolevStretch StationarySelfTest
open WeakHartreeProduct ForcingDomain TimeHolder Retarded ActualDuhamelPath IntervalTimeTransport
open AffineForcingIndependentReview AffineForcing AffinePath AffineMixed AffineL1Source CriticalAffine
attribute [local irreducible] energySubmodule criticalPathSubmodule energyPath criticalPathIntervalSource
  affineCriticalPath

/-- Convert the measure identity before applying it to large canonical slice predicates. -/
theorem timeAffine_local_quasiMeasurePreserving {a : ℝ} (ha : 0<a) (c A B : ℝ) :
    Measure.QuasiMeasurePreserving (timeAffine a c) (localMeasure A B)
      (localMeasure (timeAffine a c A) (timeAffine a c B)) := by
  simpa only [timeAffine_preimage_Icc ha c A B] using
    timeAffine_quasiMeasurePreserving ha c (Icc (timeAffine a c A) (timeAffine a c B))

/-- Canonical extended states agree on the actual target interval, including
its endpoints. No outside-interval representative assertion is needed. -/
theorem affine_extended_path {a : ℝ} (ha : 0<a) (b : Space) (c A B : ℝ) (hAB : A≤B)
    (u : CriticalPath (intervalMeasure (timeAffine a c A) (timeAffine a c B)))
    (s : ℝ) (hs : s∈Icc A B) :
    extendEnergyPath hAB (energyPath _ (affineCriticalPath ha b c A B hAB u)) s=
      affineState ha b (extendEnergyPath (timeAffine_monotone ha c hAB) (energyPath _ u)
        (timeAffine a c s)) := by
  let t : Icc A B := ⟨s,hs⟩
  exact (extendEnergyPath_val hAB _ t).trans
    ((affineCriticalPath_energy_apply ha b c A B hAB u t).trans
      (congrArg (affineState ha b)
        (extendEnergyPath_val (timeAffine_monotone ha c hAB) _
          (intervalAffineHomeomorph ha c A B t)).symm))

theorem directionalField_real_pullback (k : ℝ) (U V : Space → Space)
    (d : Space → Space) (v x : Space) :
    directionalField (fun y => k • U (d y)) (fun y => k • V (d y)) v x=
      k • directionalField U V v (d x) := by
  simp only [directionalField,real_inner_smul_left]
  exact map_smul Complex.equivRealProdCLM.symm k (inner ℝ (U (d x)) v,inner ℝ (V (d x)) v)

variable (hDensity : OrdinaryH1Density) {K alpha kernel : ℝ} (hSob : OrdinarySobolev K)
  (hH : OrdinaryHLS alpha kernel) {a : ℝ} (ha : 0<a) (b : Space) (c A B : ℝ)
  (hAB : A≤B) (u : CriticalPath (intervalMeasure (timeAffine a c A) (timeAffine a c B)))

/-- Literal canonical Hartree forcing on the transformed path. -/
theorem affine_path_forcing_ae : ∀ᵐ s ∂localMeasure A B,
    forcing alpha kernel (energyValue
      (extendEnergyPath hAB (energyPath _ (affineCriticalPath ha b c A B hAB u)) s)) =ᵐ[volume]
      (fun x => a^(5/2:ℝ) • forcing alpha kernel (energyValue
        (extendEnergyPath (timeAffine_monotone ha c hAB) (energyPath _ u) (timeAffine a c s)))
        (affine a b x)) := by
  filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
  rw [affine_extended_path ha b c A B hAB u s hs]
  exact affineState_forcing_ae alpha kernel ha b _

include hDensity hSob hH in
/-- Pointwise identification before substituting the actual path and source classes. -/
theorem affine_source_coordinate_ae (v w : EnergyState)
    (he : w=affineState ha b v)
    (hv10 : MemLp (energyValue v) 10 volume)
    (hU : MemLp (energyProjectedGradient Complex.reCLM v) criticalExponent volume)
    (hV : MemLp (energyProjectedGradient Complex.imCLM v) criticalExponent volume)
    (f g : SourceSpace)
    (hf : (f : Space → ℂ) =ᵐ[volume] forcing alpha kernel (energyValue w))
    (j : Fin 3)
    (hd : ∂_{coordinate j} (Lp.toTemperedDistribution f)=Lp.toTemperedDistribution g) :
    (g : Space → ℂ) =ᵐ[volume]
      (fun x => a^(7/2:ℝ) • canonicalForcingCoordinate alpha kernel v j (affine a b x)) := by
  have hf' : (f : Space → ℂ) =ᵐ[volume] forcing alpha kernel (energyValue (affineState ha b v)) := by
    simpa only [he] using hf
  have hw := affineState_canonical_weak_forcing hDensity hSob hH v hv10 hU hV ha b
  have hg := source_coordinate_ae_of_weakGradients _ _ _ _ _ hf'
    hw.2.2.2.2.1 hw.2.2.2.2.2 hw.2.1 hw.2.2.1 j hd
  exact hg.mono (fun x hx => hx.trans (directionalField_real_pullback _ _ _ _ _ x))

/-- The transformed source's actual constructed gradient is identified with
pulled canonical forcing gradients using native weak-gradient uniqueness.
No transformed-gradient equality is supplied as a premise. -/
theorem affine_path_source_canonical_gradient_ae : ∀ᵐ s ∂localMeasure A B, ∀ j : Fin 3,
    ((criticalPathIntervalSource hDensity hSob hH hAB
      (affineCriticalPath ha b c A B hAB u) 0).gradient j s : Space → ℂ) =ᵐ[volume]
    (fun x => a^(7/2:ℝ) • canonicalForcingCoordinate alpha kernel
      (extendEnergyPath (timeAffine_monotone ha c hAB) (energyPath _ u) (timeAffine a c s)) j
      (affine a b x)) := by
  have hs := (timeAffine_local_quasiMeasurePreserving ha c A B).ae
    (canonical_local_critical_slices hDensity hSob (timeAffine_monotone ha c hAB) u)
  filter_upwards [hs,
    criticalPathIntervalSource_single_coeFn hDensity hSob hH hAB
      (affineCriticalPath ha b c A B hAB u),
    (criticalPathIntervalSource hDensity hSob hH hAB
      (affineCriticalPath ha b c A B hAB u) 0).derivative,
    ae_restrict_mem measurableSet_Icc] with s hs hf hd hmem
  intro j
  have he := affine_extended_path ha b c A B hAB u s hmem
  exact affine_source_coordinate_ae hDensity hSob hH ha b
    (extendEnergyPath (timeAffine_monotone ha c hAB) (energyPath _ u) (timeAffine a c s))
    (extendEnergyPath hAB (energyPath _ (affineCriticalPath ha b c A B hAB u)) s) he
    hs.1 hs.2.1 hs.2.2 _ _ hf j (hd j)


#print axioms timeAffine_local_quasiMeasurePreserving
#print axioms affine_extended_path
#print axioms directionalField_real_pullback
#print axioms affine_path_forcing_ae
#print axioms affine_source_coordinate_ae
#print axioms affine_path_source_canonical_gradient_ae
end HartreeF.NonlinearAffine
