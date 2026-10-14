import FRetardedLinearity
import FEndpointSourceWeakDerivative
import FL2EnergyConstruction

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory LineDeriv
open scoped ENNReal SchwartzMap
namespace HartreeF.Retarded
open FreeFlow EnergySpace TimeHolder SobolevStretch StationarySelfTest
open ForcingDomain GradientMajorants WeakHartreeProduct

/-- Generic constructor from a compatible endpoint source. Only the source
relation is supplied: the output relation and target L6 class are produced. -/
def restrictedEnergyState (hDensity : OrdinaryH1Density) {K C : ℝ}
    (hSob : OrdinarySobolev K) (h : OrdinaryEndpointBound C)
    (F : EndpointSource) (G : Fin 3 → EndpointSource)
    (hFG : ∀ j : Fin 3, ∀ᵐ s ∂volume,
      ∂_{coordinate j} (Lp.toTemperedDistribution (F s)) = Lp.toTemperedDistribution (G j s))
    (J : Set ℝ) (hJ : MeasurableSet J) (t : ℝ) : EnergyState :=
  l2EnergyState hDensity hSob (restrictedL2 h J hJ t F)
    (fun j => restrictedL2 h J hJ t (G j))
    (fun j => restrictedL2_derivative h J hJ t F (G j) (coordinate j)
      (ae_restrict_of_ae (hFG j)))

theorem restrictedEnergyState_scalar (hDensity : OrdinaryH1Density) {K C : ℝ}
    (hSob : OrdinarySobolev K) (h : OrdinaryEndpointBound C)
    (F : EndpointSource) (G : Fin 3 → EndpointSource)
    (hFG : ∀ j : Fin 3, ∀ᵐ s ∂volume,
      ∂_{coordinate j} (Lp.toTemperedDistribution (F s)) = Lp.toTemperedDistribution (G j s))
    (J : Set ℝ) (hJ : MeasurableSet J) (t : ℝ) (φ : FreeFlow.Test) :
    energyDistribution (restrictedEnergyState hDensity hSob h F G hFG J hJ t) φ =
      ∫ s in J, scalarIntegrand t F φ s := by
  rw [restrictedEnergyState, l2EnergyState_distribution, restrictedL2_scalar]

theorem restrictedEnergyState_gradient (hDensity : OrdinaryH1Density) {K C : ℝ}
    (hSob : OrdinarySobolev K) (h : OrdinaryEndpointBound C)
    (F : EndpointSource) (G : Fin 3 → EndpointSource)
    (hFG : ∀ j : Fin 3, ∀ᵐ s ∂volume,
      ∂_{coordinate j} (Lp.toTemperedDistribution (F s)) = Lp.toTemperedDistribution (G j s))
    (J : Set ℝ) (hJ : MeasurableSet J) (t : ℝ) (j : Fin 3) :
    energyGradient j (restrictedEnergyState hDensity hSob h F G hFG J hJ t) =
      restrictedL2 h J hJ t (G j) := rfl

/-- Actual Hartree forcing difference produces an actual EnergyState. C41 and
the source-representative identities produce compatibility inside this proof.
Neither target EnergyState, L6 membership, nor output gradient relation is assumed. -/
theorem exists_actual_restrictedEnergyState (hDensity : OrdinaryH1Density)
    {K C alpha c : ℝ} (hSob : OrdinarySobolev K) (h : OrdinaryEndpointBound C)
    (hH : OrdinaryHLS alpha c)
    (u v : ℝ → Space → ℂ) (U V P Q : ℝ → Space → Space)
    (hSlices : ∀ᵐ s ∂(volume : Measure ℝ),
      InDotH1 (u s) (U s) (V s) ∧ InDotH1 (v s) (P s) (Q s) ∧
      MemLp (u s) 10 volume ∧ MemLp (v s) 10 volume ∧
      MemLp (U s) (ENNReal.ofReal (30/13 : ℝ)) volume ∧
      MemLp (V s) (ENNReal.ofReal (30/13 : ℝ)) volume ∧
      MemLp (P s) (ENNReal.ofReal (30/13 : ℝ)) volume ∧
      MemLp (Q s) (ENNReal.ofReal (30/13 : ℝ)) volume)
    (F : EndpointSource)
    (G : Lp (Lp (EuclideanSpace ℂ (Fin 3)) (ENNReal.ofReal (6/5 : ℝ))
      (volume : Measure Space)) 2 (volume : Measure ℝ))
    (hF : ∀ᵐ s ∂(volume : Measure ℝ), ∀ᵐ x ∂(volume : Measure Space),
      F s x = forcing alpha c (u s) x - forcing alpha c (v s) x)
    (hG : ∀ᵐ s ∂(volume : Measure ℝ), ∀ᵐ x ∂(volume : Measure Space),
      G s x = actualFullGradient alpha c (u s) (U s) (V s) x -
        actualFullGradient alpha c (v s) (P s) (Q s) x)
    (J : Set ℝ) (hJ : MeasurableSet J) (t : ℝ) :
    ∃ w : EnergyState,
      (∀ φ : FreeFlow.Test, energyDistribution w φ = ∫ s in J, scalarIntegrand t F φ s) ∧
      (∀ j : Fin 3, energyGradient j w =
        restrictedL2 h J hJ t (endpointGradientCoordinateSource volume j G)) ∧
      (energyValue w : Space → ℂ) =ᵐ[volume] restrictedL2 h J hJ t F := by
  have hd := actual_endpointSource_tempered_derivatives hDensity hSob hH
    volume u v U V P Q hSlices F G hF hG
  have hcoord (j : Fin 3) : ∀ᵐ s ∂(volume : Measure ℝ),
      ∂_{coordinate j} (Lp.toTemperedDistribution (F s)) =
        Lp.toTemperedDistribution (endpointGradientCoordinateSource volume j G s) := by
    filter_upwards [hd] with s hs
    exact hs j
  refine ⟨restrictedEnergyState hDensity hSob h F
    (fun j => endpointGradientCoordinateSource volume j G) hcoord J hJ t, ?_, ?_, ?_⟩
  · exact fun φ => restrictedEnergyState_scalar hDensity hSob h F _ hcoord J hJ t φ
  · exact fun j => restrictedEnergyState_gradient hDensity hSob h F _ hcoord J hJ t j
  · exact l2EnergyState_value_ae _ _ _ _ _

end HartreeF.Retarded
