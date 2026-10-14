import FStrongOperatorsOnCompactPaths
import FStrongOperatorsOnBochnerLp
import FRegularizerLpConsumers

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory Filter
open scoped ENNReal Topology NNReal
namespace HartreeF.Regularization.Actual
open EnergySpace CriticalPathSpace EnergyRegularizer SobolevStretch StationarySelfTest
open StrongOperatorPaths

attribute [local irreducible] energySubmodule criticalPathSubmodule

def uniformEnergyBound (K : ℝ) : ℝ≥0 :=
  ⟨max (K^((6:ℝ)⁻¹)) 1 * Real.sqrt 3,
    mul_nonneg ((show (0:ℝ) ≤ 1 by norm_num).trans (le_max_right _ _))
      (Real.sqrt_nonneg _)⟩

theorem J_opNorm_uniform (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) (n : ℕ) :
    ‖J hDensity hSob n‖ ≤ uniformEnergyBound K :=
  (J hDensity hSob n).opNorm_le_bound (uniformEnergyBound K).property
    (J_uniform_bound hDensity hSob n)

section Paths
variable {T : Type*} [TopologicalSpace T] [CompactSpace T] [MeasurableSpace T]
variable (μ : Measure T)

omit [MeasurableSpace T] in
/-- Uniform energy convergence on the whole actual continuous trajectory. -/
theorem J_continuousPath_tendsto (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) (u : C(T,EnergyState)) :
    Tendsto (fun n => mapPath (J hDensity hSob n) u) atTop (𝓝 u) :=
  mapPath_tendsto (J hDensity hSob) (uniformEnergyBound K)
    (J_opNorm_uniform hDensity hSob) (J_strong hDensity hSob) u

/-- The existing critical graph is preserved by the actual scalar multiplier.
Compatibility is proved from the two literal Fourier distribution identities. -/
def regularizeCriticalPath (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) (B : OrdinaryBesselLp criticalExponent)
    (n : ℕ) (u : CriticalPath μ) : CriticalPath μ :=
  ofRepresentativeAgreement μ (mapPath (J hDensity hSob n) (energyPath μ u))
    (fun j => (B.cutoffLp n).compLp (criticalGradient μ j u)) (by
    intro j
    filter_upwards [criticalGradient_distribution_derivative μ u j,
      (B.cutoffLp n).coeFn_compLp (criticalGradient μ j u)]
      with t ht hrep
    change (energyGradient j (J hDensity hSob n (energyPath μ u t)) : V → ℂ) =ᵐ[volume]
      ((B.cutoffLp n).compLp (criticalGradient μ j u) t : V → ℂ)
    rw [hrep]
    exact J_Lp_gradient_ae B hDensity hSob n (energyPath μ u t) j
      (criticalGradient μ j u t)
      (ht.symm.trans (energyDistribution_derivative (energyPath μ u t) j)))

omit [CompactSpace T] in
theorem regularizeCriticalPath_energy (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) (B : OrdinaryBesselLp criticalExponent)
    (n : ℕ) (u : CriticalPath μ) (t : T) :
    energyPath μ (regularizeCriticalPath μ hDensity hSob B n u) t =
      J hDensity hSob n (energyPath μ u t) := rfl

omit [CompactSpace T] in
theorem regularizeCriticalPath_gradient (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) (B : OrdinaryBesselLp criticalExponent)
    (n : ℕ) (u : CriticalPath μ) (j : Fin 3) :
    criticalGradient μ j (regularizeCriticalPath μ hDensity hSob B n u) =
      (B.cutoffLp n).compLp (criticalGradient μ j u) := rfl

/-- Strong approximation in the actual complete E+W graph, with both
the time-uniform energy component and the true Bochner gradient component. -/
theorem regularizeCriticalPath_tendsto (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) (B : OrdinaryBesselLp criticalExponent)
    (u : CriticalPath μ) :
    Tendsto (fun n => regularizeCriticalPath μ hDensity hSob B n u) atTop (𝓝 u) := by
  have he := J_continuousPath_tendsto hDensity hSob (energyPath μ u)
  have hg (j : Fin 3) : Tendsto
      (fun n => (B.cutoffLp n).compLp (criticalGradient μ j u)) atTop
      (𝓝 (criticalGradient μ j u)) := by
    let : Fact ((1 : ℝ≥0∞) ≤ (10 : ℕ)) := ⟨by norm_num⟩
    have hb (n : ℕ) : ‖B.cutoffLp n‖ ≤ (2 : ℝ≥0) :=
      (B.cutoffLp n).opNorm_le_bound (by norm_num) (B.cutoffLp_bound n)
    exact compLp_tendsto μ (q := 10) (by decide) (B.cutoffLp) 2 hb
      B.cutoffLp_strong (criticalGradient μ j u)
  have hgp := tendsto_pi_nhds.mpr hg
  apply tendsto_subtype_rng.mpr
  change Tendsto (fun n =>
    (mapPath (J hDensity hSob n) (energyPath μ u),
      fun j => (B.cutoffLp n).compLp (criticalGradient μ j u))) atTop
      (𝓝 (energyPath μ u, fun j => criticalGradient μ j u))
  exact he.prodMk_nhds hgp

end Paths
#print axioms J_opNorm_uniform
#print axioms J_continuousPath_tendsto
#print axioms regularizeCriticalPath
#print axioms regularizeCriticalPath_energy
#print axioms regularizeCriticalPath_gradient
#print axioms regularizeCriticalPath_tendsto
end HartreeF.Regularization.Actual
