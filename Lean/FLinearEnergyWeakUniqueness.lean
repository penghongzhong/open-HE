import FLinearWeakEquation

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000
open MeasureTheory LineDeriv
open scoped ENNReal Topology SchwartzMap

namespace HartreeF.LinearWeakEquation
open EnergySpace SobolevStretch

/-- Ordinary homogeneous L2 uniqueness, retained as an explicit analytic theorem interface.
Source: Le Coz, Definition 2.3.1, p.16 and Proposition 2.3.2, p.17, only at F=0.
The compact-interval, tensor-test specialization and complex-linear sign convention
are documented in SOURCE_INTERFACE_MAP.md. The value is a genuine L2 class here;
the interface is used below exclusively on actual gradient coordinates. -/
structure OrdinaryL2HomogeneousUniqueness : Prop where
  zero : ∀ (a b t₀ : ℝ), t₀ ∈ Set.Icc a b → ∀ z : ℝ → L2,
    ContinuousOn z (Set.Icc a b) →
    WeakEquation a b (fun t => Lp.toTemperedDistribution (z t)) (fun _ => 0) →
    z t₀ = 0 → ∀ t ∈ Set.Icc a b, z t = 0

/-- The existing Sobolev estimate removes the kernel of the actual energy gradient. -/
theorem energyState_eq_zero_of_gradients {K : ℝ} (hSob : OrdinarySobolev K)
    (u : EnergyState) (hu : ∀ j : Fin 3, energyGradient j u = 0) : u = 0 := by
  apply (pureGradientNorm_eq_zero_iff hSob u).mp
  simp only [pureGradientNorm, gradientSquared, hu, norm_zero, zero_pow (by decide : 2 ≠ 0),
    Finset.sum_const_zero, Real.sqrt_zero]

/-- The distributional compatibility of the closed energy graph is sufficient to
place every true coordinate gradient in the homogeneous L2 uniqueness theorem. -/
theorem homogeneous_energy_gradients_zero
    (hUnique : OrdinaryL2HomogeneousUniqueness)
    {a b t₀ : ℝ} (ht₀ : t₀ ∈ Set.Icc a b) (u : ℝ → EnergyState)
    (hcont : ContinuousOn u (Set.Icc a b))
    (hPDE : WeakEquation a b (fun t => energyDistribution (u t)) (fun _ => 0))
    (hinit : u t₀ = 0) (j : Fin 3) :
    ∀ t ∈ Set.Icc a b, energyGradient j (u t) = 0 := by
  apply hUnique.zero a b t₀ ht₀ (fun t => energyGradient j (u t))
  · exact (energyGradient j).continuous.comp_continuousOn hcont
  · simpa only [lineDerivOp_zero] using energy_gradient_weakEquation hPDE j
  · simp only [hinit, map_zero]

/-- Homogeneous uniqueness for the canonical L6/dot-H1 realization, without
requiring the original scalar value to lie in L2. -/
theorem homogeneous_energy_zero (hUnique : OrdinaryL2HomogeneousUniqueness)
    {K a b t₀ : ℝ} (hSob : OrdinarySobolev K) (ht₀ : t₀ ∈ Set.Icc a b)
    (u : ℝ → EnergyState) (hcont : ContinuousOn u (Set.Icc a b))
    (hPDE : WeakEquation a b (fun t => energyDistribution (u t)) (fun _ => 0))
    (hinit : u t₀ = 0) : ∀ t ∈ Set.Icc a b, u t = 0 := by
  intro t ht
  exact energyState_eq_zero_of_gradients hSob (u t)
    (fun j => homogeneous_energy_gradients_zero hUnique ht₀ u hcont hPDE hinit j t ht)

/-- Two genuine energy paths satisfying the same distributional equation and
the same datum agree. Neither path is assumed to have a mild representation. -/
theorem energy_weak_uniqueness (hUnique : OrdinaryL2HomogeneousUniqueness)
    {K a b t₀ : ℝ} (hSob : OrdinarySobolev K) (ht₀ : t₀ ∈ Set.Icc a b)
    (u v : ℝ → EnergyState) (F : ℝ → TD)
    (hucont : ContinuousOn u (Set.Icc a b)) (hvcont : ContinuousOn v (Set.Icc a b))
    (hu : WeakEquation a b (fun t => energyDistribution (u t)) F)
    (hv : WeakEquation a b (fun t => energyDistribution (v t)) F)
    (hinit : u t₀ = v t₀) : ∀ t ∈ Set.Icc a b, u t = v t := by
  have hp : WeakEquation a b (fun t => energyDistribution (u t - v t)) (fun _ => 0) := by
    simpa only [map_sub] using hu.sub_same_source hv
  have hz := homogeneous_energy_zero hUnique hSob ht₀ (fun t => u t - v t)
    (hucont.sub hvcont) hp (sub_eq_zero.mpr hinit)
  exact fun t ht => sub_eq_zero.mp (hz t ht)

/-- The actual L6 representatives agree as Lp classes, so no nonzero spatial
constant can remain after gradient uniqueness. -/
theorem energy_value_weak_uniqueness (hUnique : OrdinaryL2HomogeneousUniqueness)
    {K a b t₀ : ℝ} (hSob : OrdinarySobolev K) (ht₀ : t₀ ∈ Set.Icc a b)
    (u v : ℝ → EnergyState) (F : ℝ → TD)
    (hucont : ContinuousOn u (Set.Icc a b)) (hvcont : ContinuousOn v (Set.Icc a b))
    (hu : WeakEquation a b (fun t => energyDistribution (u t)) F)
    (hv : WeakEquation a b (fun t => energyDistribution (v t)) F)
    (hinit : u t₀ = v t₀) :
    ∀ t ∈ Set.Icc a b, energyValue (u t) = energyValue (v t) := by
  intro t ht
  rw [energy_weak_uniqueness hUnique hSob ht₀ u v F hucont hvcont hu hv hinit t ht]

end HartreeF.LinearWeakEquation
