import FActualEnergyErrorBound
import FActualCommutatorRepresentatives
import FRegularizedEnergyResidualAlgebra

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory Filter LineDeriv
open scoped ENNReal Topology
namespace HartreeF.Regularization.Actual
open EnergySpace EnergyRegularizer SobolevStretch StationarySelfTest
open CriticalPathSpace IntervalTimeTransport ForcingDomain ForcingContinuity ForcingL2
open RegularizedEnergyPairing ActualDuhamelPath CriticalUniqueness StateEnergy
attribute [local instance] sourceEnergyNormedSpace sourcePathNormedSpace
attribute [local irreducible] energySubmodule criticalPathSubmodule energyPath energyValue
  criticalL2Source regularizeCriticalPath actualL2Commutator actualGradientCommutator

/-- The constructed L2 class is the actual Hartree nonlinearity at J_n u. -/
theorem actualRegularizedNonlinearityLocal_coeFn (hDensity : OrdinaryH1Density)
    {K alpha c a b : ℝ} (hSob : OrdinarySobolev K) (hH : OrdinaryHLS alpha c)
    (hab : a ≤ b) (Bw : OrdinaryBesselLp criticalExponent) (n : ℕ)
    (u : CriticalPath (intervalMeasure a b)) :
    ∀ᵐ t ∂localMeasure a b,
      (actualRegularizedNonlinearityLocal hDensity hSob hH hab Bw n u t : V → ℂ) =ᵐ[volume]
        forcing alpha c (energyValue
          (J hDensity hSob n (extendEnergyPath hab (energyPath _ u) t))) := by
  let v := regularizeCriticalPath (intervalMeasure a b) hDensity hSob Bw n u
  let F := criticalL2Source (intervalMeasure a b) hDensity hSob hH v
  have he (t : ℝ) : energyPath _ v (Set.projIcc a b hab t) =
      J hDensity hSob n (extendEnergyPath hab (energyPath _ u) t) :=
    regularizeCriticalPath_energy (intervalMeasure a b) hDensity hSob Bw n u _
  have hFt : ∀ᵐ t ∂localMeasure a b,
      (F (Set.projIcc a b hab t) : V → ℂ) =ᵐ[volume]
        forcing alpha c (energyValue (energyPath _ v (Set.projIcc a b hab t))) :=
    ae_clamp hab (criticalL2Source_coeFn (intervalMeasure a b) hDensity hSob hH v)
  filter_upwards [toLocalLp_coeFn hab 2 F, hFt] with t ht hF
  change ((toLocalLp hab 2 F) t : V → ℂ) =ᵐ[volume] _
  rw [ht]
  exact hF.trans (Eventually.of_forall (fun x => congrArg
    (fun z : EnergyState => forcing alpha c (energyValue z) x) (he t)))


theorem actualGradientCommutator_eq_terms (hDensity : OrdinaryH1Density)
    {K alpha c a b : ℝ} (hSob : OrdinarySobolev K) (hH : OrdinaryHLS alpha c)
    (hab : a ≤ b) (Bw : OrdinaryBesselLp criticalExponent)
    (Bs : OrdinaryBesselLp sourceExponent) (n : ℕ) (u : CriticalPath (intervalMeasure a b)) :
    ∀ᵐ t ∂localMeasure a b, ∀ j : Fin 3,
      actualGradientCommutator hDensity hSob hH hab Bw Bs n u j t =
        Bs.cutoffLp n ((criticalPathIntervalSource hDensity hSob hH hab u 0).gradient j t) -
        (criticalPathIntervalSource hDensity hSob hH hab
          (regularizeCriticalPath (intervalMeasure a b) hDensity hSob Bw n u) 0).gradient j t := by
  apply ae_all_iff.mpr
  intro j
  let F := criticalPathIntervalSource hDensity hSob hH hab u 0
  let G := criticalPathIntervalSource hDensity hSob hH hab
    (regularizeCriticalPath (intervalMeasure a b) hDensity hSob Bw n u) 0
  filter_upwards [Lp.coeFn_sub ((Bs.cutoffLp n).compLp (F.gradient j)) (G.gradient j),
    (Bs.cutoffLp n).coeFn_compLp (F.gradient j)] with t hs hc
  unfold actualGradientCommutator
  change (((Bs.cutoffLp n).compLp (F.gradient j)-G.gradient j) t) =
    Bs.cutoffLp n (F.gradient j t)-G.gradient j t
  exact hs.trans (by simp only [Pi.sub_apply, hc])

/-- A small spatial identity, with no path-level unfolding during addition
of the two actual L2 representatives. -/
theorem residual_sum_representative_at (hDensity : OrdinaryH1Density)
    {K alpha c : ℝ} (hSob : OrdinarySobolev K) (S : OrdinaryBesselSmoothing)
    (Bs : OrdinaryBesselLp sourceExponent) (hH : OrdinaryHLS alpha c)
    (n : ℕ) (z : EnergyState) (N R : EnergySpace.L2)
    (hN : (N : V → ℂ) =ᵐ[volume] forcing alpha c (energyValue (J hDensity hSob n z)))
    (hR : (R : V → ℂ) =ᵐ[volume] literalHartreeResidual hDensity hSob S Bs hH n z) :
    (energyValue (S.sourceJ Bs n (forcingLp hH (energyValue z))) : V → ℂ) =ᵐ[volume]
      (R+N : EnergySpace.L2) := by
  filter_upwards [hR, hN, Lp.coeFn_add R N] with x hRx hNx hsum
  dsimp only [literalHartreeResidual] at hRx
  have he : energyValue (S.sourceJ Bs n (forcingLp hH (energyValue z))) x = R x+N x := by
    calc
      _ = (energyValue (S.sourceJ Bs n (forcingLp hH (energyValue z))) x -
          forcing alpha c (energyValue (J hDensity hSob n z)) x) +
          forcing alpha c (energyValue (J hDensity hSob n z)) x := (sub_add_cancel _ _).symm
      _ = R x+N x := congrArg₂ (fun y w : ℂ => y+w) hRx.symm hNx.symm
  exact he.trans hsum.symm

/-- The native C1 energy rate is precisely the literal Hartree commutator
error. Every nonlinear value and weak derivative in the algebra lemma is
supplied here by the actual CriticalPath producers. -/
theorem actual_regularizedEnergyRate_error_ae (hDensity : OrdinaryH1Density)
    {K alpha a b : ℝ} (hSob : OrdinarySobolev K) (S : OrdinaryBesselSmoothing)
    (hH : OrdinaryHLS alpha (HeatRiesz.standardRieszConstant alpha))
    (hab : a ≤ b) (Bw : OrdinaryBesselLp criticalExponent)
    (Bs : OrdinaryBesselLp sourceExponent) (n : ℕ) (u : CriticalPath (intervalMeasure a b)) :
    ∀ᵐ t ∂localMeasure a b,
      regularizedEnergyRate hDensity hSob S Bs hH n (extendEnergyPath hab (energyPath _ u) t) =
        actualRegularizedEnergyError hDensity hSob hH hab Bw Bs n u t := by
  let v := regularizeCriticalPath (intervalMeasure a b) hDensity hSob Bw n u
  let G := criticalPathIntervalSource hDensity hSob hH hab v 0
  let N := actualRegularizedNonlinearityLocal hDensity hSob hH hab Bw n u
  let R := actualRegularizedResidualLocal hDensity hSob hH hab Bw n u
  let A := fun j => actualGradientCommutator hDensity hSob hH hab Bw Bs n u j
  have he (t : ℝ) : extendEnergyPath hab (energyPath _ v) t =
      J hDensity hSob n (extendEnergyPath hab (energyPath _ u) t) :=
    regularizeCriticalPath_energy (intervalMeasure a b) hDensity hSob Bw n u _
  have hv : ∀ᵐ t ∂localMeasure a b, ∀ j : Fin 3,
      regularizedGradientLp hDensity hSob hab n u j t =
        energyValue ((firstCutoff n j).energyCLM hDensity hSob
          (extendEnergyPath hab (energyPath _ u) t)) :=
    ae_all_iff.mpr (fun j => regularizedGradientLp_coeFn hDensity hSob hab n u j)
  have hNt : ∀ᵐ t ∂localMeasure a b,
      (N t : V → ℂ) =ᵐ[volume] forcing alpha (HeatRiesz.standardRieszConstant alpha)
        (energyValue (J hDensity hSob n (extendEnergyPath hab (energyPath _ u) t))) :=
    actualRegularizedNonlinearityLocal_coeFn hDensity hSob hH hab Bw n u
  have hRt : ∀ᵐ t ∂localMeasure a b,
      (R t : V → ℂ) =ᵐ[volume] literalHartreeResidual hDensity hSob S Bs hH n
        (extendEnergyPath hab (energyPath _ u) t) :=
    actualL2Commutator_literal hDensity hSob S Bs Bw hH hab n u
  have hAt : ∀ᵐ t ∂localMeasure a b, ∀ j : Fin 3,
      A j t = Bs.cutoffLp n ((criticalPathIntervalSource hDensity hSob hH hab u 0).gradient j t) -
        G.gradient j t :=
    actualGradientCommutator_eq_terms hDensity hSob hH hab Bw Bs n u
  have hGvalt : ∀ᵐ t ∂localMeasure a b,
      G.value t = forcingLp hH (energyValue (extendEnergyPath hab (energyPath _ v) t)) :=
    critical_source_value_eq_forcingLp hDensity hSob hH hab v
  filter_upwards [hNt, hRt, G.derivative, hGvalt,
    actual_sourceJ_gradient_ae hDensity hSob S Bs hH hab n u, hAt, hv]
    with t hN hR hG hGval hQG hA hV
  have hQ : (energyValue (S.sourceJ Bs n (forcingLp hH
      (energyValue (extendEnergyPath hab (energyPath _ u) t)))) : V → ℂ) =ᵐ[volume]
        (R t + N t : EnergySpace.L2) :=
    residual_sum_representative_at hDensity hSob S Bs hH n
      (extendEnergyPath hab (energyPath _ u) t) (N t) (R t) hN hR
  have hGN (j : Fin 3) : ∂_{coordinate j} (Lp.toTemperedDistribution
      (forcingLp hH (energyValue (J hDensity hSob n
        (extendEnergyPath hab (energyPath _ u) t))))) =
      Lp.toTemperedDistribution (G.gradient j t) := by
    have heq : G.value t = forcingLp hH (energyValue (J hDensity hSob n
        (extendEnergyPath hab (energyPath _ u) t))) :=
      hGval.trans (congrArg (fun z : EnergyState => forcingLp hH (energyValue z)) (he t))
    exact (congrArg (fun f : SourceLp => ∂_{coordinate j} (Lp.toTemperedDistribution f))
      heq).symm.trans (hG j)
  have hAG (j : Fin 3) : (A j t + G.gradient j t : SourceLp) =
      Bs.cutoffLp n ((criticalPathIntervalSource hDensity hSob hH hab u 0).gradient j t) := by
    exact (congrArg (fun x : SourceLp => x+G.gradient j t) (hA j)).trans (sub_add_cancel _ _)
  have hgrad (j : Fin 3) : (A j t + G.gradient j t : SourceLp) =ᵐ[volume]
      energyGradient j (S.sourceJ Bs n (forcingLp hH
        (energyValue (extendEnergyPath hab (energyPath _ u) t)))) := by
    exact Filter.EventuallyEq.trans
      (Eventually.of_forall (fun x : V => congrArg (fun f : SourceLp => f x) (hAG j)))
      (hQG j).symm
  have h := regularizedEnergyRate_residual_algebra hDensity hSob S Bs hH n
    (extendEnergyPath hab (energyPath _ u) t) (N t) (R t + N t)
    (fun j => G.gradient j t) (fun j => A j t + G.gradient j t)
    (Filter.EventuallyEq.symm hN) hQ hGN hgrad
  simpa only [add_sub_cancel_right, actualRegularizedEnergyError, hV, N, R, A] using h

/-- AE interior derivative identity for the actual mild solution. -/
theorem actual_mild_energy_error_hasDerivAt_ae (hDensity : OrdinaryH1Density)
    {K alpha a b : ℝ} (hSob : OrdinarySobolev K) (S : OrdinaryBesselSmoothing)
    (hH : OrdinaryHLS alpha (HeatRiesz.standardRieszConstant alpha))
    (hab : a ≤ b) (Bw : OrdinaryBesselLp criticalExponent)
    (Bs : OrdinaryBesselLp sourceExponent) (u0 : EnergyState)
    (u : CriticalPath (intervalMeasure a b))
    (hmild : IsMildHartreePath hab alpha (HeatRiesz.standardRieszConstant alpha) u0 u) (n : ℕ) :
    ∀ᵐ t ∂localMeasure a b,
      HasDerivAt (fun s => totalEnergy alpha
        (J hDensity hSob n (extendEnergyPath hab (energyPath _ u) s)))
      (actualRegularizedEnergyError hDensity hSob hH hab Bw Bs n u t) t := by
  filter_upwards [actual_regularizedEnergyRate_error_ae hDensity hSob S hH hab Bw Bs n u,
    ae_restrict_mem measurableSet_Icc, (localMeasure a b).ae_ne a,
    (localMeasure a b).ae_ne b] with t he ht ha hb
  rw [← he]
  exact actual_mild_regularized_energy_hasDerivAt hDensity hSob S Bs hH hab u0 u hmild n
    ⟨lt_of_le_of_ne ht.1 ha.symm, lt_of_le_of_ne ht.2 hb⟩

/-- Exact finite-interval identity with the actual, Bochner-integrable
nonlinear commutator error. -/
theorem actual_mild_energy_error_increment (hDensity : OrdinaryH1Density)
    {K alpha a b : ℝ} (hSob : OrdinarySobolev K) (S : OrdinaryBesselSmoothing)
    (hH : OrdinaryHLS alpha (HeatRiesz.standardRieszConstant alpha))
    (hab : a ≤ b) (Bw : OrdinaryBesselLp criticalExponent)
    (Bs : OrdinaryBesselLp sourceExponent) (u0 : EnergyState)
    (u : CriticalPath (intervalMeasure a b))
    (hmild : IsMildHartreePath hab alpha (HeatRiesz.standardRieszConstant alpha) u0 u) (n : ℕ) :
    totalEnergy alpha (J hDensity hSob n (extendEnergyPath hab (energyPath _ u) b)) -
      totalEnergy alpha (J hDensity hSob n (extendEnergyPath hab (energyPath _ u) a)) =
      ∫ t, actualRegularizedEnergyError hDensity hSob hH hab Bw Bs n u t ∂localMeasure a b := by
  rw [actual_mild_regularized_energy_increment hDensity hSob S Bs hH hab u0 u hmild n]
  rw [intervalIntegral.integral_of_le hab]
  change (∫ t in Set.Ioc a b, _) = ∫ t in Set.Icc a b, _
  rw [← integral_Icc_eq_integral_Ioc]
  exact integral_congr_ae (actual_regularizedEnergyRate_error_ae hDensity hSob S hH hab Bw Bs n u)

#check @residual_sum_representative_at
#print axioms residual_sum_representative_at
#print axioms actualRegularizedNonlinearityLocal_coeFn
#print axioms actualGradientCommutator_eq_terms
#print axioms actual_regularizedEnergyRate_error_ae
#print axioms actual_mild_energy_error_hasDerivAt_ae
#print axioms actual_mild_energy_error_increment
end HartreeF.Regularization.Actual
