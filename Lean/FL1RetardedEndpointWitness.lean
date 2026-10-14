import FL1RetardedCriticalPath
import FEndpointHartreeDuhamelOutput

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory Filter
open scoped ENNReal Topology
namespace HartreeF.EndpointOutput
open CriticalPathSpace IntervalTimeTransport EnergySpace ForcingDomain ActualDuhamelPath
open SobolevStretch StationarySelfTest Retarded ActualStrichartz TimeHolder
attribute [local instance] FreeDataDependence.canonicalEnergyNormedSpace
  FreeDataDependence.canonicalPathNormedSpace
attribute [local irreducible] energyPath energyGradient intervalRetardedCriticalPath
  CompatibleL1IntervalSource.retardedCriticalPath

/-- The original L2 source output has precisely the literal retarded gradient. -/
theorem intervalRetardedCriticalPath_actual_gradient (hDensity : OrdinaryH1Density)
    {K C0 C a b : ℝ} (hSob : OrdinarySobolev K) (h0 : OrdinaryEndpointBound C0)
    (h : OrdinaryRetardedStrichartz h0 C) (F : CompatibleIntervalSource a b)
    (t : Set.Icc a b) (j : Fin 3) :
    energyGradient j (energyPath _ (intervalRetardedCriticalPath hDensity hSob h0 h F) t) =
      retardedL2 h0 (extendEndpointSource (Set.Icc a b) measurableSet_Icc (F.gradient j)) t := by
  unfold intervalRetardedCriticalPath
  rw [retardedCriticalPath_energy, retardedEnergyState_gradient]

/-- Isometric zero extension is continuous in the original gradient norm. -/
theorem extendEndpointSource_tendsto {a b : ℝ}
    {F : ℕ → LocalEndpointSource (Set.Icc a b)} {G : LocalEndpointSource (Set.Icc a b)}
    (hF : Tendsto F atTop (𝓝 G)) :
    Tendsto (fun n => extendEndpointSource (Set.Icc a b) measurableSet_Icc (F n))
      atTop (𝓝 (extendEndpointSource (Set.Icc a b) measurableSet_Icc G)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have he : (fun n => ‖extendEndpointSource (Set.Icc a b) measurableSet_Icc (F n) -
      extendEndpointSource (Set.Icc a b) measurableSet_Icc G‖) = fun n => ‖F n - G‖ := by
    funext n
    rw [← extendEndpointSource_sub, extendEndpointSource_norm]
  rw [he]
  exact tendsto_iff_norm_sub_tendsto_zero.mp hF

attribute [local irreducible] restrictedL2CLM extendEndpointSource retardedL2

/-- Pointwise L2 identification of the existing E+W limit. No scalar L2 premise is used. -/
theorem l1RetardedCriticalPath_actual_gradient (hDensity : OrdinaryH1Density)
    {K C0 C a b : ℝ} (hSob : OrdinarySobolev K) (h0 : OrdinaryEndpointBound C0)
    (h : OrdinaryRetardedStrichartz h0 C) (E : CompatibleL1IntervalSource a b)
    (t : Set.Icc a b) (j : Fin 3) :
    energyGradient j (energyPath _ (E.retardedCriticalPath hDensity hSob h0 h) t) =
      retardedL2 h0 (extendEndpointSource (Set.Icc a b) measurableSet_Icc (E.gradient j)) t := by
  have hg : Tendsto (fun n => energyGradient j (energyPath _
      (intervalRetardedCriticalPath hDensity hSob h0 h (E.approximation n)) t)) atTop
      (𝓝 (energyGradient j (energyPath _ (E.retardedCriticalPath hDensity hSob h0 h) t))) :=
    (energyGradient j).continuous.tendsto _ |>.comp
      (E.retarded_approximation_energy_tendsto hDensity hSob h0 h t)
  have hs : Tendsto (fun n => (E.approximation n).gradient j) atTop (𝓝 (E.gradient j)) :=
    (continuous_apply j).tendsto E.gradient |>.comp E.approximation_gradient_tendsto
  have hr := (restrictedL2CLM h0 (Set.Iio (t : ℝ)) measurableSet_Iio t).continuous.tendsto _
    |>.comp (extendEndpointSource_tendsto hs)
  simp only [intervalRetardedCriticalPath_actual_gradient] at hg
  apply tendsto_nhds_unique hg
  simpa only [Function.comp_def, retardedL2, restrictedL2CLM_apply] using hr

/-- The L2_t L6_x field of the literal retarded scalar operator on a local gradient source. -/
def localRetardedEndpointField {C0 Ce a b : ℝ} (h0 : OrdinaryEndpointBound C0)
    (he : OrdinaryRetardedEndpointOutput h0 Ce) (G : LocalEndpointSource (Set.Icc a b)) :
    EndpointGradient (intervalMeasure a b) :=
  intervalEndpointField a b
    (retardedJoint h0 (extendEndpointSource (Set.Icc a b) measurableSet_Icc G))
    (retardedJoint_stronglyMeasurable h0 _)
    (retardedJoint_endpoint_finite h0 he _)

theorem localRetardedEndpointField_agrees {C0 Ce a b : ℝ} (h0 : OrdinaryEndpointBound C0)
    (he : OrdinaryRetardedEndpointOutput h0 Ce) (G : LocalEndpointSource (Set.Icc a b)) :
    ∀ᵐ t ∂intervalMeasure a b, (localRetardedEndpointField h0 he G t : Space → ℂ) =ᵐ[volume]
      retardedL2 h0 (extendEndpointSource (Set.Icc a b) measurableSet_Icc G) t := by
  filter_upwards [intervalEndpointField_agrees a b
    (retardedJoint h0 (extendEndpointSource (Set.Icc a b) measurableSet_Icc G))
    (retardedJoint_stronglyMeasurable h0 _) (retardedJoint_endpoint_finite h0 he _)] with t ht
  exact ht.trans (retardedJoint_slice h0 _ t)

theorem localRetardedEndpointField_enorm_le {C0 Ce a b : ℝ} (h0 : OrdinaryEndpointBound C0)
    (he : OrdinaryRetardedEndpointOutput h0 Ce) (G : LocalEndpointSource (Set.Icc a b)) :
    ‖localRetardedEndpointField h0 he G‖ₑ ≤ ENNReal.ofReal (Ce * ‖G‖) := by
  have hb := (intervalEndpointField_enorm_le a b
    (retardedJoint h0 (extendEndpointSource (Set.Icc a b) measurableSet_Icc G))
    (retardedJoint_stronglyMeasurable h0 _) (retardedJoint_endpoint_finite h0 he _)).trans (he.2 _)
  unfold localRetardedEndpointField
  simpa only [extendEndpointSource_norm] using hb

/-- Constructed endpoint witness for the very same accepted CriticalPath limit. -/
def l1RetardedCriticalPath_endpointWitness (hDensity : OrdinaryH1Density)
    {K C0 C Ce a b : ℝ} (hSob : OrdinarySobolev K) (h0 : OrdinaryEndpointBound C0)
    (h : OrdinaryRetardedStrichartz h0 C) (he : OrdinaryRetardedEndpointOutput h0 Ce)
    (E : CompatibleL1IntervalSource a b) :
    EndpointGradientWitness (intervalMeasure a b)
      (energyPath _ (E.retardedCriticalPath hDensity hSob h0 h)) where
  field j := localRetardedEndpointField h0 he (E.gradient j)
  agrees j := by
    filter_upwards [localRetardedEndpointField_agrees h0 he (E.gradient j)] with t ht
    rw [l1RetardedCriticalPath_actual_gradient hDensity hSob h0 h E t j]
    exact ht

theorem l1RetardedCriticalPath_endpoint_bound (hDensity : OrdinaryH1Density)
    {K C0 C Ce a b : ℝ} (hSob : OrdinarySobolev K) (h0 : OrdinaryEndpointBound C0)
    (h : OrdinaryRetardedStrichartz h0 C) (he : OrdinaryRetardedEndpointOutput h0 Ce)
    (E : CompatibleL1IntervalSource a b) (j : Fin 3) :
    mixedNorm (intervalMeasure a b) volume 2 6
      (fun t => energyGradient j (energyPath _ (E.retardedCriticalPath hDensity hSob h0 h) t)) ≤
      ENNReal.ofReal (Ce * ‖E.gradient j‖) := by
  rw [(l1RetardedCriticalPath_endpointWitness hDensity hSob h0 h he E).mixedNorm_eq]
  exact localRetardedEndpointField_enorm_le h0 he (E.gradient j)

theorem l1RetardedCriticalPath_fullZ (hDensity : OrdinaryH1Density)
    {K C0 C Ce a b : ℝ} (hSob : OrdinarySobolev K) (h0 : OrdinaryEndpointBound C0)
    (h : OrdinaryRetardedStrichartz h0 C) (he : OrdinaryRetardedEndpointOutput h0 Ce)
    (E : CompatibleL1IntervalSource a b) : FullZPath (E.retardedCriticalPath hDensity hSob h0 h) :=
  ⟨l1RetardedCriticalPath_endpointWitness hDensity hSob h0 h he E⟩

end HartreeF.EndpointOutput
