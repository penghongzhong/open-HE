import FCoherentLpExhaustion
import FIntervalRetardedRestart
import FIntervalLpRestriction

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory Filter LineDeriv
open scoped ENNReal Topology

namespace HartreeF.ActualDuhamelPath
open EnergySpace CriticalPathSpace IntervalTimeTransport CriticalPathRestriction
open SobolevStretch StationarySelfTest Retarded ForcingDomain

/-- Coherent, uniformly L²-bounded compatible sources exhaust a finite time
interval. Spatial derivative compatibility is inherited on the countable
cover; the missing terminal time is Lebesgue null. -/
theorem exists_compatibleIntervalSource_exhaustion
    {a T : ℝ} (b : ℕ → ℝ) (hbt : ∀ n, b n < T)
    (hcover : ∀ t ∈ Set.Ico a T, ∃ n, t ≤ b n)
    (F : (n : ℕ) → CompatibleIntervalSource a (b n)) (C : ℝ)
    (hvbound : ∀ n, ‖sourceGlobalValue (F n)‖ ≤ C)
    (hgbound : ∀ n j, ‖sourceGlobalGradient (F n) j‖ ≤ C)
    (hcoherent : ∀ n m, n ≤ m → ∀ᵐ t ∂localMeasure a (b n),
      sourceGlobalValue (F n) t = sourceGlobalValue (F m) t ∧
        ∀ j : Fin 3, sourceGlobalGradient (F n) j t = sourceGlobalGradient (F m) j t) :
    ∃ G : CompatibleIntervalSource a T, ‖G.value‖ ≤ C ∧
      (∀ j, ‖G.gradient j‖ ≤ C) ∧
      ∀ n, ∀ᵐ t ∂localMeasure a (b n), G.value t = (F n).value t ∧
        ∀ j : Fin 3, G.gradient j t = (F n).gradient j t := by
  have hvsupport (n : ℕ) : ∀ᵐ t ∂volume,
      t ∉ Set.Icc a (b n) → sourceGlobalValue (F n) t = 0 := by
    filter_upwards [extendEndpointSource_coeFn (Set.Icc a (b n))
      measurableSet_Icc (F n).value] with t ht
    intro htn
    simpa only [sourceGlobalValue, Set.indicator_of_notMem htn] using ht
  have hgsupport (j : Fin 3) (n : ℕ) : ∀ᵐ t ∂volume,
      t ∉ Set.Icc a (b n) → sourceGlobalGradient (F n) j t = 0 := by
    filter_upwards [extendEndpointSource_coeFn (Set.Icc a (b n))
      measurableSet_Icc ((F n).gradient j)] with t ht
    intro htn
    simpa only [sourceGlobalGradient, Set.indicator_of_notMem htn] using ht
  have hvcoherent (n m : ℕ) (hnm : n ≤ m) : ∀ᵐ t ∂volume,
      t ∈ Set.Icc a (b n) → sourceGlobalValue (F m) t = sourceGlobalValue (F n) t := by
    filter_upwards [(ae_restrict_iff' measurableSet_Icc).mp (hcoherent n m hnm)] with t ht
    exact fun htn => (ht htn).1.symm
  have hgcoherent (j : Fin 3) (n m : ℕ) (hnm : n ≤ m) : ∀ᵐ t ∂volume,
      t ∈ Set.Icc a (b n) → sourceGlobalGradient (F m) j t = sourceGlobalGradient (F n) j t := by
    filter_upwards [(ae_restrict_iff' measurableSet_Icc).mp (hcoherent n m hnm)] with t ht
    exact fun htn => ((ht htn).2 j).symm
  obtain ⟨v, hvb, hvl, _⟩ := FEndpoint.exists_coherent_L2_exhaustion
    (fun n => Set.Icc a (b n)) (fun n => sourceGlobalValue (F n)) C
    hvbound hvsupport hvcoherent
  have hge (j : Fin 3) := FEndpoint.exists_coherent_L2_exhaustion
    (fun n => Set.Icc a (b n)) (fun n => sourceGlobalGradient (F n) j) C
    (fun n => hgbound n j) (hgsupport j) (hgcoherent j)
  choose g hgb hgl _ using hge
  let v' : LocalEndpointSource (Set.Icc a T) :=
    shrinkLp 2 (Measure.restrict_le_self : localMeasure a T ≤ volume) v
  let g' : Fin 3 → LocalEndpointSource (Set.Icc a T) := fun j =>
    shrinkLp 2 (Measure.restrict_le_self : localMeasure a T ≤ volume) (g j)
  have hv' : ∀ᵐ t ∂localMeasure a T, v' t = v t := shrinkLp_coeFn 2 _ v
  have hg' : ∀ᵐ t ∂localMeasure a T, ∀ j, g' j t = g j t :=
    ae_all_iff.mpr fun j => shrinkLp_coeFn 2 _ (g j)
  have hvl' : ∀ᵐ t ∂volume, ∀ n,
      t ∈ Set.Icc a (b n) → v t = sourceGlobalValue (F n) t := ae_all_iff.mpr hvl
  have hgl' : ∀ᵐ t ∂volume, ∀ n j,
      t ∈ Set.Icc a (b n) → g j t = sourceGlobalGradient (F n) j t :=
    ae_all_iff.mpr fun n => ae_all_iff.mpr fun j => hgl j n
  have hd' : ∀ᵐ t ∂volume, ∀ n j,
      ∂_{coordinate j} (Lp.toTemperedDistribution (sourceGlobalValue (F n) t)) =
        Lp.toTemperedDistribution (sourceGlobalGradient (F n) j t) :=
    ae_all_iff.mpr fun n => ae_all_iff.mpr fun j => sourceGlobalDerivative (F n) j
  have hd : ∀ᵐ t ∂localMeasure a T, ∀ j,
      ∂_{coordinate j} (Lp.toTemperedDistribution (v' t)) =
        Lp.toTemperedDistribution (g' j t) := by
    filter_upwards [hv', hg', ae_restrict_of_ae hvl', ae_restrict_of_ae hgl',
      ae_restrict_of_ae hd', ae_restrict_of_ae (volume.ae_ne T),
      ae_restrict_mem measurableSet_Icc] with t htv htg htlv htlg htd htne htmem
    obtain ⟨n, htn⟩ := hcover t ⟨htmem.1, lt_of_le_of_ne htmem.2 htne⟩
    intro j
    rw [htv, htg j, htlv n ⟨htmem.1, htn⟩, htlg n j ⟨htmem.1, htn⟩]
    exact htd n j
  let G : CompatibleIntervalSource a T := ⟨v', g', hd⟩
  refine ⟨G, (shrinkLp_norm_le 2
    (Measure.restrict_le_self : localMeasure a T ≤ volume) v).trans hvb,
    (fun j => (shrinkLp_norm_le 2
      (Measure.restrict_le_self : localMeasure a T ≤ volume) (g j)).trans (hgb j)), ?_⟩
  intro n
  have hmu : localMeasure a (b n) ≤ localMeasure a T :=
    localMeasure_mono (a := a) le_rfl (hbt n).le
  have hlocalv := extendEndpointSource_restrict_coeFn (Set.Icc a (b n))
    measurableSet_Icc (F n).value
  have hlocalg : ∀ᵐ t ∂localMeasure a (b n), ∀ j,
      sourceGlobalGradient (F n) j t = (F n).gradient j t :=
    ae_all_iff.mpr fun j => extendEndpointSource_restrict_coeFn
      (Set.Icc a (b n)) measurableSet_Icc ((F n).gradient j)
  filter_upwards [ae_mono hmu hv', ae_mono hmu hg', ae_restrict_of_ae hvl',
    ae_restrict_of_ae hgl', hlocalv, hlocalg, ae_restrict_mem measurableSet_Icc]
    with t htv htg htlv htlg hvn hgn htmem
  exact ⟨htv.trans ((htlv n htmem).trans hvn),
    fun j => (htg j).trans ((htlg n j htmem).trans (hgn j))⟩

end HartreeF.ActualDuhamelPath

#print axioms HartreeF.ActualDuhamelPath.exists_compatibleIntervalSource_exhaustion
