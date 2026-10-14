import FActualGradientWeakTests
import FEnergyWeakGradientTemperedDerivative

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory LineDeriv
open scoped ENNReal RealInnerProductSpace
namespace HartreeF.TimeHolder
open SobolevStretch WeakHartreeProduct EnergySpace ForcingDomain StationarySelfTest

local instance endpointSourceExponent_one_le : Fact (1 ≤ ENNReal.ofReal (6/5 : ℝ)) :=
  ⟨by norm_num⟩

/-- The spatial coordinate map on the actual endpoint gradient class. -/
def endpointGradientCoordinate (j : Fin 3) :
    Lp (EuclideanSpace ℂ (Fin 3)) (ENNReal.ofReal (6/5 : ℝ)) (volume : Measure Space) →L[ℂ]
      Lp ℂ (ENNReal.ofReal (6/5 : ℝ)) (volume : Measure Space) :=
  (EuclideanSpace.proj (𝕜 := ℂ) j).compLpL (ENNReal.ofReal (6/5 : ℝ)) volume

theorem endpointGradientCoordinate_coeFn (j : Fin 3)
    (g : Lp (EuclideanSpace ℂ (Fin 3)) (ENNReal.ofReal (6/5 : ℝ))
      (volume : Measure Space)) :
    ∀ᵐ x ∂(volume : Measure Space), endpointGradientCoordinate j g x = g x j :=
  (EuclideanSpace.proj (𝕜 := ℂ) j).coeFn_compLpL g

/-- Projecting the Bochner source produces an actual scalar endpoint source. -/
def endpointGradientCoordinateSource {T : Type*} [MeasurableSpace T]
    (mu : Measure T) (j : Fin 3)
    (G : Lp (Lp (EuclideanSpace ℂ (Fin 3)) (ENNReal.ofReal (6/5 : ℝ))
      (volume : Measure Space)) 2 mu) :
    Lp (Lp ℂ (ENNReal.ofReal (6/5 : ℝ)) (volume : Measure Space)) 2 mu :=
  (endpointGradientCoordinate j).compLp G

theorem endpointGradientCoordinateSource_coeFn {T : Type*} [MeasurableSpace T]
    (mu : Measure T) (j : Fin 3)
    (G : Lp (Lp (EuclideanSpace ℂ (Fin 3)) (ENNReal.ofReal (6/5 : ℝ))
      (volume : Measure Space)) 2 mu) :
    ∀ᵐ t ∂mu, endpointGradientCoordinateSource mu j G t =
      endpointGradientCoordinate j (G t) :=
  (endpointGradientCoordinate j).coeFn_compLp G

theorem gradientReal_memLp {p : ℝ≥0∞} {g : Space → EuclideanSpace ℂ (Fin 3)}
    (hg : MemLp g p volume) : MemLp (fun x => gradientReal (g x)) p volume := by
  have heq : (fun x => gradientReal (g x)) =
      (fun x => ∑ j : Fin 3, (g x j).re • coordinate j) := by
    funext x
    exact (coordinate_reconstruct (gradientReal (g x))).symm
  rw [heq]
  apply memLp_finsetSum
  intro j _
  exact (((EuclideanSpace.proj (𝕜 := ℂ) j).comp_memLp' hg).continuousLinearMap_comp
    Complex.reCLM).continuousLinearMap_comp
      (ContinuousLinearMap.toSpanSingleton ℝ (coordinate j))

theorem gradientImag_memLp {p : ℝ≥0∞} {g : Space → EuclideanSpace ℂ (Fin 3)}
    (hg : MemLp g p volume) : MemLp (fun x => gradientImag (g x)) p volume := by
  have heq : (fun x => gradientImag (g x)) =
      (fun x => ∑ j : Fin 3, (g x j).im • coordinate j) := by
    funext x
    exact (coordinate_reconstruct (gradientImag (g x))).symm
  rw [heq]
  apply memLp_finsetSum
  intro j _
  exact (((EuclideanSpace.proj (𝕜 := ℂ) j).comp_memLp' hg).continuousLinearMap_comp
    Complex.imCLM).continuousLinearMap_comp
      (ContinuousLinearMap.toSpanSingleton ℝ (coordinate j))

theorem gradient_directionalField_coordinate
    (g : Space → EuclideanSpace ℂ (Fin 3)) (j : Fin 3) :
    directionalField (fun x => gradientReal (g x)) (fun x => gradientImag (g x))
      (coordinate j) = fun x => g x j := by
  funext x
  apply Complex.ext <;>
    simp [directionalField, coordinate, ← EuclideanSpace.basisFun_apply,
      EuclideanSpace.inner_basisFun_real, gradientReal, gradientImag]

/-- A genuine compact-test weak gradient of an endpoint representative gives
the distributional derivative of its Lp class. Compatibility is a conclusion. -/
theorem endpointSource_weakDerivative_of_weakGradients
    (f : Lp ℂ (ENNReal.ofReal (6/5 : ℝ)) (volume : Measure Space))
    (g : Lp (EuclideanSpace ℂ (Fin 3)) (ENNReal.ofReal (6/5 : ℝ))
      (volume : Measure Space))
    (w : Space → ℂ) (hrep : f =ᵐ[volume] w)
    (hR : HasWeakGradient (fun x => (w x).re) (fun x => gradientReal (g x)))
    (hI : HasWeakGradient (fun x => (w x).im) (fun x => gradientImag (g x)))
    (j : Fin 3) :
    ∂_{coordinate j} (Lp.toTemperedDistribution f) =
      Lp.toTemperedDistribution (endpointGradientCoordinate j g) := by
  have hw : MemLp w (ENNReal.ofReal (6/5 : ℝ)) volume := (Lp.memLp f).ae_eq hrep
  have hU := gradientReal_memLp (Lp.memLp g)
  have hV := gradientImag_memLp (Lp.memLp g)
  have hd := weak_gradient_tempered_derivative hw hU hV hR hI (coordinate j)
  have hf : hw.toLp w = f := Lp.ext (hw.coeFn_toLp.trans hrep.symm)
  have hg : (directionalField_memLp hU hV (coordinate j)).toLp
      (directionalField (fun x => gradientReal (g x)) (fun x => gradientImag (g x))
        (coordinate j)) = endpointGradientCoordinate j g := by
    apply Lp.ext
    filter_upwards [(directionalField_memLp hU hV (coordinate j)).coeFn_toLp,
      endpointGradientCoordinate_coeFn j g] with x hx hy
    rw [hx, gradient_directionalField_coordinate, hy]
  simpa only [hf, hg] using hd

/-- C41's actual compact-test identities imply native distribution compatibility
for the scalar Hartree-difference source and its actual Bochner gradient. The
scalar and vector assumptions are only their nested AE representative equalities. -/
theorem actual_endpointSource_tempered_derivatives (hDensity : OrdinaryH1Density)
    {K : ℝ} (hSob : OrdinarySobolev K) {alpha c : ℝ} (hH : OrdinaryHLS alpha c)
    {T : Type*} [MeasurableSpace T] (mu : Measure T)
    (u v : T → Space → ℂ) (U V P Q : T → Space → Space)
    (hSlices : ∀ᵐ t ∂mu,
      InDotH1 (u t) (U t) (V t) ∧ InDotH1 (v t) (P t) (Q t) ∧
      MemLp (u t) 10 volume ∧ MemLp (v t) 10 volume ∧
      MemLp (U t) (ENNReal.ofReal (30/13 : ℝ)) volume ∧
      MemLp (V t) (ENNReal.ofReal (30/13 : ℝ)) volume ∧
      MemLp (P t) (ENNReal.ofReal (30/13 : ℝ)) volume ∧
      MemLp (Q t) (ENNReal.ofReal (30/13 : ℝ)) volume)
    (f : Lp (Lp ℂ (ENNReal.ofReal (6/5 : ℝ)) (volume : Measure Space)) 2 mu)
    (G : Lp (Lp (EuclideanSpace ℂ (Fin 3)) (ENNReal.ofReal (6/5 : ℝ))
      (volume : Measure Space)) 2 mu)
    (hf : ∀ᵐ t ∂mu, ∀ᵐ x ∂(volume : Measure Space),
      f t x = forcing alpha c (u t) x - forcing alpha c (v t) x)
    (hG : ∀ᵐ t ∂mu, ∀ᵐ x ∂(volume : Measure Space),
      G t x = actualFullGradient alpha c (u t) (U t) (V t) x -
        actualFullGradient alpha c (v t) (P t) (Q t) x) :
    ∀ᵐ t ∂mu, ∀ j : Fin 3,
      ∂_{coordinate j} (Lp.toTemperedDistribution (f t)) =
        Lp.toTemperedDistribution (endpointGradientCoordinateSource mu j G t) := by
  have hw := actual_gradient_bochnerSource_hasWeakGradients hDensity hSob hH
    mu u v U V P Q hSlices G hG
  have hc : ∀ᵐ t ∂mu, ∀ j : Fin 3,
      endpointGradientCoordinateSource mu j G t = endpointGradientCoordinate j (G t) :=
    (ae_all_iff).mpr (fun j => endpointGradientCoordinateSource_coeFn mu j G)
  filter_upwards [hw, hf, hc] with t ht hft hct
  intro j
  rw [hct j]
  exact endpointSource_weakDerivative_of_weakGradients (f t) (G t)
    (fun x => forcing alpha c (u t) x - forcing alpha c (v t) x) hft ht.1 ht.2 j

end HartreeF.TimeHolder
