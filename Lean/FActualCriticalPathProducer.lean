import FIntervalTimeTransport
import FOrdinaryHomogeneousStrichartz
import FOrdinaryRetardedStrichartz

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory Filter
open scoped ENNReal Topology
namespace HartreeF.ActualDuhamelPath
open CriticalPathSpace IntervalTimeTransport EnergySpace TimeHolder ActualStrichartz
open SobolevStretch StationarySelfTest Retarded LineDeriv

instance criticalExponent_ne_top : Fact (criticalExponent ≠ ∞) := ⟨ENNReal.ofReal_ne_top⟩

theorem interval_mixedNorm_le_global (a b : ℝ) (p q : ℝ≥0∞) (f : ℝ → Space → ℂ) :
    mixedNorm (intervalMeasure a b) volume p q (fun t => f (t : ℝ)) ≤
      mixedNorm volume volume p q f := by
  have he := (MeasurableEmbedding.subtype_coe (show MeasurableSet (Set.Icc a b) from
    measurableSet_Icc)).eLpNorm_map_measure
    (g := fun t => eLpNorm (f t) q volume) (p := p) (μ := intervalMeasure a b)
  rw [(inclusion_measurePreserving a b).map_eq] at he
  change eLpNorm ((fun t => eLpNorm (f t) q volume) ∘ Subtype.val) p
    (intervalMeasure a b) ≤ _
  rw [← he]
  exact eLpNorm_mono_measure _ Measure.restrict_le_self

/-- Packaging lemma: actual joint fields with proved finite critical norms
produce the graph coordinates, with no output compatibility assumption. -/
def criticalPathOfGlobalFields (a b : ℝ) (g : ℝ → EnergyState) (hg : Continuous g)
    (d : Fin 3 → ℝ → Space → ℂ)
    (hdm : ∀ j, StronglyMeasurable (fun z : ℝ × Space => d j z.1 z.2))
    (hdf : ∀ j, mixedNorm volume volume 10 criticalExponent (d j) ≠ ∞)
    (hd : ∀ j, ∀ᵐ t ∂(volume : Measure ℝ),
      d j t =ᵐ[volume] energyGradient j (g t)) : CriticalPath (intervalMeasure a b) := by
  let f (j : Fin 3) : Set.Icc a b × Space → ℂ := fun z => d j z.1 z.2
  have hm (j : Fin 3) : AEStronglyMeasurable (f j) ((intervalMeasure a b).prod volume) :=
    ((hdm j).comp_measurable (measurable_subtype_coe.comp measurable_fst |>.prodMk
      measurable_snd)).aestronglyMeasurable
  have hf (j : Fin 3) : mixedNorm (intervalMeasure a b) volume 10 criticalExponent
      (fun t x => f j (t,x)) ≠ ∞ :=
    ne_top_of_le_ne_top (hdf j) (interval_mixedNorm_le_global a b 10 criticalExponent (d j))
  have hs (j : Fin 3) : ∀ᵐ t ∂intervalMeasure a b,
      MemLp (fun x => f j (t,x)) criticalExponent volume :=
    finite_mixedNorm_ae_slice_memLp (intervalMeasure a b) volume 10 criticalExponent
      (by norm_num) (by norm_num) (fun t x => f j (t,x)) (hf j)
  let D (j : Fin 3) : CriticalGradient (intervalMeasure a b) :=
    jointLpRealization (intervalMeasure a b) volume 10 criticalExponent (f j) (hm j) (hs j) (hf j)
  refine ofRepresentativeAgreement (intervalMeasure a b)
    ⟨fun t => g t, hg.comp continuous_subtype_val⟩ D ?_
  intro j
  have hdi := (inclusion_measurePreserving a b).quasiMeasurePreserving.ae (ae_restrict_of_ae (hd j))
  filter_upwards [hdi, jointLpRealization_coeFn (intervalMeasure a b) volume 10 criticalExponent
    (f j) (hm j) (hs j) (hf j)] with t hdt hDt
  exact Filter.EventuallyEq.trans (Filter.EventuallyEq.symm hdt) (Filter.EventuallyEq.symm hDt)

@[simp] theorem criticalPathOfGlobalFields_energy (a b : ℝ) (g : ℝ → EnergyState)
    (hg : Continuous g) (d : Fin 3 → ℝ → Space → ℂ)
    (hdm : ∀ j, StronglyMeasurable (fun z : ℝ × Space => d j z.1 z.2))
    (hdf : ∀ j, mixedNorm volume volume 10 criticalExponent (d j) ≠ ∞)
    (hd : ∀ j, ∀ᵐ t ∂(volume : Measure ℝ), d j t =ᵐ[volume] energyGradient j (g t))
    (t : Set.Icc a b) :
    energyPath _ (criticalPathOfGlobalFields a b g hg d hdm hdf hd) t = g t := rfl

/-- The literal Fourier free evolution of every homogeneous-energy datum lies
in the actual complete path space, using only the numerical KT(5) premise. -/
def freeCriticalPath (hDensity : OrdinaryH1Density) {K C : ℝ}
    (hSob : OrdinarySobolev K) (h : OrdinaryHomogeneousStrichartz C)
    (a b : ℝ) (u : EnergyState) : CriticalPath (intervalMeasure a b) :=
  criticalPathOfGlobalFields a b (fun t => freeEnergyState hDensity hSob t u)
    (freeEnergyState_time_continuous hDensity hSob u)
    (fun j => freeJoint (energyGradient j u))
    (fun j => freeJoint_stronglyMeasurable (energyGradient j u))
    (fun j => freeJoint_mixedNorm_finite h (energyGradient j u))
    (freeJoint_energyGradient hDensity hSob u)

@[simp] theorem freeCriticalPath_energy (hDensity : OrdinaryH1Density) {K C : ℝ}
    (hSob : OrdinarySobolev K) (h : OrdinaryHomogeneousStrichartz C)
    (a b : ℝ) (u : EnergyState) (t : Set.Icc a b) :
    energyPath _ (freeCriticalPath hDensity hSob h a b u) t =
      freeEnergyState hDensity hSob t u := rfl

/-- The already constructed retarded energy state belongs to the graph.
The input spatial derivative relation is the only compatibility premise;
KT(7) supplies only its numeric bound, and all output coordinates are produced. -/
def retardedCriticalPath (hDensity : OrdinaryH1Density) {K C0 C : ℝ}
    (hSob : OrdinarySobolev K) (h0 : OrdinaryEndpointBound C0)
    (h : OrdinaryRetardedStrichartz h0 C) (a b : ℝ)
    (F : EndpointSource) (G : Fin 3 → EndpointSource)
    (hFG : ∀ j : Fin 3, ∀ᵐ s ∂volume,
      ∂_{coordinate j} (Lp.toTemperedDistribution (F s)) = Lp.toTemperedDistribution (G j s)) :
    CriticalPath (intervalMeasure a b) :=
  criticalPathOfGlobalFields a b (retardedEnergyState hDensity hSob h0 F G hFG)
    (retardedEnergyState_time_continuous hDensity hSob h0 F G hFG)
    (fun j => retardedJoint h0 (G j))
    (fun j => retardedJoint_stronglyMeasurable h0 (G j))
    (fun j => retardedJoint_mixedNorm_finite h0 h (G j))
    (retardedJoint_energyGradient hDensity hSob h0 F G hFG)

@[simp] theorem retardedCriticalPath_energy (hDensity : OrdinaryH1Density) {K C0 C : ℝ}
    (hSob : OrdinarySobolev K) (h0 : OrdinaryEndpointBound C0)
    (h : OrdinaryRetardedStrichartz h0 C) (a b : ℝ)
    (F : EndpointSource) (G : Fin 3 → EndpointSource)
    (hFG : ∀ j : Fin 3, ∀ᵐ s ∂volume,
      ∂_{coordinate j} (Lp.toTemperedDistribution (F s)) = Lp.toTemperedDistribution (G j s))
    (t : Set.Icc a b) :
    energyPath _ (retardedCriticalPath hDensity hSob h0 h a b F G hFG) t =
      retardedEnergyState hDensity hSob h0 F G hFG t := rfl

end HartreeF.ActualDuhamelPath
