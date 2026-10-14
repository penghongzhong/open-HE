import FIntervalRetardedPath

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory Filter LineDeriv
open scoped ENNReal Topology
namespace HartreeF.ActualDuhamelPath
open CriticalPathSpace IntervalTimeTransport EnergySpace TimeHolder ActualStrichartz
open SobolevStretch StationarySelfTest Retarded

/-- Exact graph-coordinate norm control inherited from the true global joint field. -/
theorem criticalPathOfGlobalFields_gradient_bound (a b : ℝ) (g : ℝ → EnergyState)
    (hg : Continuous g) (d : Fin 3 → ℝ → Space → ℂ)
    (hdm : ∀ j, StronglyMeasurable (fun z : ℝ × Space => d j z.1 z.2))
    (hdf : ∀ j, mixedNorm volume volume 10 criticalExponent (d j) ≠ ∞)
    (hd : ∀ j, ∀ᵐ t ∂(volume : Measure ℝ), d j t =ᵐ[volume] energyGradient j (g t))
    (j : Fin 3) :
    ‖criticalGradient _ j (criticalPathOfGlobalFields a b g hg d hdm hdf hd)‖ₑ ≤
      mixedNorm volume volume 10 criticalExponent (d j) := by
  rw [← criticalGradient_eLpNorm]
  apply le_trans _ (interval_mixedNorm_le_global a b 10 criticalExponent (d j))
  apply le_of_eq
  apply eLpNorm_congr_ae
  have hdi := (inclusion_measurePreserving a b).quasiMeasurePreserving.ae
    (ae_restrict_of_ae (hd j))
  filter_upwards [hdi] with t ht
  rw [criticalPathOfGlobalFields_energy]
  exact (eLpNorm_congr_ae ht).symm

/-- The constructed free graph coordinates satisfy the exact retained KT(5) bound. -/
theorem freeCriticalPath_gradient_bound (hDensity : OrdinaryH1Density) {K C : ℝ}
    (hSob : OrdinarySobolev K) (h : OrdinaryHomogeneousStrichartz C)
    (a b : ℝ) (u : EnergyState) (j : Fin 3) :
    ‖criticalGradient _ j (freeCriticalPath hDensity hSob h a b u)‖ₑ ≤
      ENNReal.ofReal (C * ‖energyGradient j u‖) :=
  (criticalPathOfGlobalFields_gradient_bound a b _ _ _ _ _ _ j).trans (h.2 _)

/-- The constructed retarded graph coordinates satisfy the exact retained KT(7) bound. -/
theorem retardedCriticalPath_gradient_bound (hDensity : OrdinaryH1Density) {K C0 C : ℝ}
    (hSob : OrdinarySobolev K) (h0 : OrdinaryEndpointBound C0)
    (h : OrdinaryRetardedStrichartz h0 C) (a b : ℝ)
    (F : EndpointSource) (G : Fin 3 → EndpointSource)
    (hFG : ∀ j : Fin 3, ∀ᵐ s ∂volume,
      ∂_{coordinate j} (Lp.toTemperedDistribution (F s)) = Lp.toTemperedDistribution (G j s))
    (j : Fin 3) :
    ‖criticalGradient _ j (retardedCriticalPath hDensity hSob h0 h a b F G hFG)‖ₑ ≤
      ENNReal.ofReal (C * ‖G j‖) :=
  (criticalPathOfGlobalFields_gradient_bound a b _ _ _ _ _ _ j).trans (h.2 _)

/-- Zero extension introduces no extra constant into the local critical estimate. -/
theorem intervalRetardedCriticalPath_gradient_bound (hDensity : OrdinaryH1Density)
    {K C0 C a b : ℝ} (hSob : OrdinarySobolev K) (h0 : OrdinaryEndpointBound C0)
    (h : OrdinaryRetardedStrichartz h0 C) (F : CompatibleIntervalSource a b) (j : Fin 3) :
    ‖criticalGradient _ j (intervalRetardedCriticalPath hDensity hSob h0 h F)‖ₑ ≤
      ENNReal.ofReal (C * ‖F.gradient j‖) := by
  unfold intervalRetardedCriticalPath
  simpa only [extendEndpointSource_norm] using
    retardedCriticalPath_gradient_bound hDensity hSob h0 h a b
      (extendEndpointSource (Set.Icc a b) measurableSet_Icc F.value)
      (fun k => extendEndpointSource (Set.Icc a b) measurableSet_Icc (F.gradient k))
      (ae_all_iff.mp (extendEndpointSource_coordinate_derivatives (Set.Icc a b)
        measurableSet_Icc F.value F.gradient F.derivative)) j

end HartreeF.ActualDuhamelPath
