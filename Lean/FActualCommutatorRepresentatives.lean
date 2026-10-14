import FRegularizedSourceRepresentatives

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000
open MeasureTheory Filter LineDeriv
open scoped ENNReal Topology SchwartzMap
namespace HartreeF.Regularization.Actual
open EnergySpace EnergyRegularizer SobolevStretch StationarySelfTest
open CriticalPathSpace IntervalTimeTransport ForcingDomain ForcingContinuity ForcingL2
open ActualDuhamelPath
attribute [local instance] sourceEnergyNormedSpace sourcePathNormedSpace
attribute [local irreducible] energySubmodule criticalPathSubmodule criticalPathIntervalSource
  regularizeCriticalPath criticalL2Source energyPath energyValue
  actualL2Commutator actualGradientCommutator

/-- A named temporal representative identity for genuine L2-valued classes. -/
theorem localL2_comp_sub_representative {a b : ℝ} (hab : a ≤ b)
    (L : EnergySpace.L2 →L[ℂ] EnergySpace.L2)
    (F G : Lp EnergySpace.L2 2 (intervalMeasure a b)) :
    ∀ᵐ t ∂localMeasure a b,
      toLocalLp hab 2 (L.compLp F-G) t =
        L (F (Set.projIcc a b hab t)) - G (Set.projIcc a b hab t) := by
  filter_upwards [toLocalLp_coeFn hab 2 (L.compLp F-G),
    ae_clamp hab (Lp.coeFn_sub (L.compLp F) G),
    ae_clamp hab (L.coeFn_compLp F)] with t ht hs hc
  exact ht.trans (hs.trans (congrArg (fun z : EnergySpace.L2 =>
    z-G (Set.projIcc a b hab t)) hc))

/-- Pure spatial realization, separated from the large actual path type. -/
theorem l2_residual_representative_at (hDensity : OrdinaryH1Density)
    {K alpha c : ℝ} (hSob : OrdinarySobolev K) (S : OrdinaryBesselSmoothing)
    (Bs : OrdinaryBesselLp sourceExponent) (hH : OrdinaryHLS alpha c)
    (n : ℕ) (z : EnergyState) (F G : EnergySpace.L2)
    (hF : (F : V → ℂ) =ᵐ[volume] forcing alpha c (energyValue z))
    (hG : (G : V → ℂ) =ᵐ[volume]
      forcing alpha c (energyValue (J hDensity hSob n z))) :
    (((cutoff n).l2 F-G : EnergySpace.L2) : V → ℂ) =ᵐ[volume]
      literalHartreeResidual hDensity hSob S Bs hH n z := by
  have hJF := sourceJ_value_ae_L2 S Bs n (forcingLp hH (energyValue z)) F
    ((forcingLp_coeFn hH (energyValue z)).trans hF.symm)
  filter_upwards [Lp.coeFn_sub ((cutoff n).l2 F) G, hJF, hG] with x hx hJ hN
  exact hx.trans (by simp only [Pi.sub_apply, ← hJ, hN]; rfl)

/-- Explicit alignment between the source distribution and its CLM form. -/
theorem cutoffLp_derivative_representative (Bs : OrdinaryBesselLp sourceExponent)
    (n : ℕ) (f g : SourceLp) (j : Fin 3)
    (hfg : ∂_{coordinate j} (Lp.toTemperedDistribution f) = Lp.toTemperedDistribution g) :
    ∂_{coordinate j} (Lp.toTemperedDistribution (Bs.cutoffLp n f)) =
      Lp.toTemperedDistribution (Bs.cutoffLp n g) := by
  rw [Bs.cutoffLp_distribution, BoundedSymbol.derivative_distribution, hfg]
  exact (Bs.cutoffLp_distribution n g).symm

/-- Exact scalar commutator realization in L2_t L2_x. Both its terms are
produced from the actual CriticalPath; the residual is a literal function. -/
theorem actualL2Commutator_literal (hDensity : OrdinaryH1Density) {K alpha c a b : ℝ}
    (hSob : OrdinarySobolev K) (S : OrdinaryBesselSmoothing)
    (Bs : OrdinaryBesselLp sourceExponent) (Bw : OrdinaryBesselLp criticalExponent)
    (hH : OrdinaryHLS alpha c) (hab : a ≤ b) (n : ℕ)
    (u : CriticalPath (intervalMeasure a b)) :
    ∀ᵐ t ∂localMeasure a b,
      (toLocalLp hab 2 (actualL2Commutator (intervalMeasure a b)
        hDensity hSob hH Bw n u) t : V → ℂ) =ᵐ[volume]
      literalHartreeResidual hDensity hSob S Bs hH n
        (extendEnergyPath hab (energyPath _ u) t) := by
  let v := regularizeCriticalPath (intervalMeasure a b) hDensity hSob Bw n u
  let F := criticalL2Source (intervalMeasure a b) hDensity hSob hH u
  let G := criticalL2Source (intervalMeasure a b) hDensity hSob hH v
  have he (t : ℝ) : energyPath _ v (Set.projIcc a b hab t) =
      J hDensity hSob n (extendEnergyPath hab (energyPath _ u) t) :=
    regularizeCriticalPath_energy (intervalMeasure a b) hDensity hSob Bw n u _
  have hc : ∀ᵐ t ∂localMeasure a b,
      toLocalLp hab 2 (actualL2Commutator (intervalMeasure a b)
        hDensity hSob hH Bw n u) t =
          (cutoff n).l2 (F (Set.projIcc a b hab t))-G (Set.projIcc a b hab t) := by
    unfold actualL2Commutator
    change ∀ᵐ t ∂localMeasure a b,
      toLocalLp hab 2 ((cutoff n).l2.compLp F-G) t =
        (cutoff n).l2 (F (Set.projIcc a b hab t))-G (Set.projIcc a b hab t)
    exact localL2_comp_sub_representative hab (cutoff n).l2 F G
  have hFt : ∀ᵐ t ∂localMeasure a b,
      (F (Set.projIcc a b hab t) : V → ℂ) =ᵐ[volume]
        forcing alpha c (energyValue (extendEnergyPath hab (energyPath _ u) t)) :=
    ae_clamp hab (criticalL2Source_coeFn (intervalMeasure a b) hDensity hSob hH u)
  have hGt : ∀ᵐ t ∂localMeasure a b,
      (G (Set.projIcc a b hab t) : V → ℂ) =ᵐ[volume]
        forcing alpha c (energyValue (energyPath _ v (Set.projIcc a b hab t))) :=
    ae_clamp hab (criticalL2Source_coeFn (intervalMeasure a b) hDensity hSob hH v)
  filter_upwards [hc, hFt, hGt]
      with t ht hF hG
  have hG' : (G (Set.projIcc a b hab t) : V → ℂ) =ᵐ[volume]
      forcing alpha c (energyValue (J hDensity hSob n
        (extendEnergyPath hab (energyPath _ u) t))) :=
    Filter.EventuallyEq.trans hG (Eventually.of_forall (fun x => congrArg
      (fun z : EnergyState => forcing alpha c (energyValue z) x) (he t)))
  rw [ht]
  exact l2_residual_representative_at hDensity hSob S Bs hH n
    (extendEnergyPath hab (energyPath _ u) t)
    (F (Set.projIcc a b hab t)) (G (Set.projIcc a b hab t)) hF hG'



/-- Exact gradient class of J_n N(u)-N(J_n u), tied to the derivative of
its literal L^(6/5) realization. This is produced from the canonical two
Hartree weak derivatives and the regularizer's distribution identity. -/
theorem actualGradientCommutator_derivative (hDensity : OrdinaryH1Density)
    {K alpha c a b : ℝ} (hSob : OrdinarySobolev K)
    (Bw : OrdinaryBesselLp criticalExponent) (Bs : OrdinaryBesselLp sourceExponent)
    (hH : OrdinaryHLS alpha c) (hab : a ≤ b) (n : ℕ)
    (u : CriticalPath (intervalMeasure a b)) :
    ∀ᵐ t ∂localMeasure a b, ∀ j : Fin 3,
      ∂_{coordinate j} (Lp.toTemperedDistribution
        (literalHartreeResidualLp hDensity hSob Bs hH n
          (extendEnergyPath hab (energyPath _ u) t))) =
      Lp.toTemperedDistribution (actualGradientCommutator hDensity hSob hH hab Bw Bs n u j t) := by
  let v := regularizeCriticalPath (intervalMeasure a b) hDensity hSob Bw n u
  let F := criticalPathIntervalSource hDensity hSob hH hab u 0
  let G := criticalPathIntervalSource hDensity hSob hH hab v 0
  have he (t : ℝ) : extendEnergyPath hab (energyPath _ v) t =
      J hDensity hSob n (extendEnergyPath hab (energyPath _ u) t) :=
    regularizeCriticalPath_energy (intervalMeasure a b) hDensity hSob Bw n u _
  have hc : ∀ᵐ t ∂localMeasure a b, ∀ j : Fin 3,
      actualGradientCommutator hDensity hSob hH hab Bw Bs n u j t =
        Bs.cutoffLp n (F.gradient j t) - G.gradient j t := by
    apply ae_all_iff.mpr
    intro j
    filter_upwards [Lp.coeFn_sub ((Bs.cutoffLp n).compLp (F.gradient j)) (G.gradient j),
      (Bs.cutoffLp n).coeFn_compLp (F.gradient j)] with t hsub hcomp
    unfold actualGradientCommutator
    change (((Bs.cutoffLp n).compLp (F.gradient j) - G.gradient j) t) = _
    exact hsub.trans (by simp only [Pi.sub_apply, hcomp])
  filter_upwards [F.derivative, G.derivative,
    critical_source_value_eq_forcingLp hDensity hSob hH hab u,
    critical_source_value_eq_forcingLp hDensity hSob hH hab v, hc]
    with t hF hG hfv hgv hc
  intro j
  have hres : literalHartreeResidualLp hDensity hSob Bs hH n
      (extendEnergyPath hab (energyPath _ u) t) = Bs.cutoffLp n (F.value t) - G.value t := by
    have hvv : G.value t = forcingLp hH (energyValue
        (J hDensity hSob n (extendEnergyPath hab (energyPath _ u) t))) :=
      hgv.trans (congrArg (fun z : EnergyState => forcingLp hH (energyValue z)) (he t))
    exact congrArg₂ (fun f g : SourceLp => Bs.cutoffLp n f - g) hfv.symm hvv.symm
  rw [hres, hc j]
  let D : SourceLp →L[ℂ] TD := Lp.toTemperedDistributionCLM ℂ volume sourceExponent
  let L : TD →L[ℂ] TD := lineDerivOpCLM ℂ TD (coordinate j)
  have hcut := cutoffLp_derivative_representative Bs n (F.value t) (F.gradient j t) j (hF j)
  have hsub := congrArg L (D.map_sub (Bs.cutoffLp n (F.value t)) (G.value t))
  have hlin := L.map_sub (D (Bs.cutoffLp n (F.value t))) (D (G.value t))
  have htarget := D.map_sub (Bs.cutoffLp n (F.gradient j t)) (G.gradient j t)
  exact hsub.trans (hlin.trans ((congrArg₂ (fun x y : TD => x-y) hcut (hG j)).trans htarget.symm))



#check @localL2_comp_sub_representative
#print axioms localL2_comp_sub_representative
#check @l2_residual_representative_at
#print axioms l2_residual_representative_at
#check @cutoffLp_derivative_representative
#print axioms cutoffLp_derivative_representative
#check @actualL2Commutator_literal
#print axioms actualL2Commutator_literal
#check @actualGradientCommutator_derivative
#print axioms actualGradientCommutator_derivative
end HartreeF.Regularization.Actual
