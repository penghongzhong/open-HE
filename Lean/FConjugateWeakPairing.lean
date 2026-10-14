import FEnergyRegularizerConsumer
import FActualHartreePairingLimit

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory Filter LineDeriv
open scoped ENNReal Topology SchwartzMap
namespace HartreeF.WeakSourcePairing
open EnergySpace Regularization.Actual SobolevStretch StationarySelfTest

local instance : Fact (1 ≤ ENNReal.ofReal (6/5 : ℝ)) := ⟨by norm_num⟩
local instance : ENNReal.HolderConjugate (ENNReal.ofReal (6/5 : ℝ)) 6 := by
  have h : Real.HolderTriple (6/5) 6 1 := by constructor <;> norm_num
  simpa only [ENNReal.ofReal_ofNat, ENNReal.ofReal_one] using h.ennrealOfReal

def conjugateTest (φ : Test) : Test :=
  φ.postcompCLM Complex.conjCLE.toContinuousLinearMap

def conjugateL6 : L6 →L[ℝ] L6 :=
  Complex.conjCLE.toContinuousLinearMap.compLpL 6 volume

theorem conjugateTest_derivative (φ : Test) (v : V) :
    ∂_{v} (conjugateTest φ) = conjugateTest (∂_{v} φ) := by
  ext x
  have h := (Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp x
    (φ.hasFDerivAt x)).fderiv
  exact congrArg (fun L : V →L[ℝ] ℂ => L v) h

theorem conjugateTest_toLp (φ : Test) :
    (conjugateTest φ).toLp 6 volume = conjugateL6 (φ.toLp 6 volume) := by
  apply Lp.ext
  filter_upwards [(conjugateTest φ).coeFn_toLp 6 volume,
    Complex.conjCLE.toContinuousLinearMap.coeFn_compLp (φ.toLp 6 volume),
    φ.coeFn_toLp 6 volume] with x hx hy hz
  change (SchwartzMap.toLp (conjugateTest φ) 6 volume : V → ℂ) x =
    (Complex.conjCLE.toContinuousLinearMap.compLp (φ.toLp 6 volume) : V → ℂ) x
  rw [hx, hy, hz]
  rfl

theorem conjugateL6_coeFn (h : L6) :
    (conjugateL6 h : V → ℂ) =ᵐ[volume] fun x => star (h x) :=
  Complex.conjCLE.toContinuousLinearMap.coeFn_compLp h

/-- The bilinear weak derivative pairing becomes the required sesquilinear
pairing by conjugating the same actual Schwartz approximants. -/
theorem conjugate_source_integration_by_parts_of_schwartz_limit
    (f g : Source) (v : V)
    (hfg : ∂_{v} (Lp.toTemperedDistribution f) = Lp.toTemperedDistribution g)
    (φ : ℕ → Test) {h dh : L6}
    (hφ : Tendsto (fun n => (φ n).toLp 6 volume) atTop (𝓝 h))
    (hdφ : Tendsto (fun n => (∂_{v} (φ n)).toLp 6 volume) atTop (𝓝 dh)) :
    (∫ x, f x * star (dh x)) = -(∫ x, g x * star (h x)) := by
  have hv := conjugateL6.continuous.tendsto h |>.comp hφ
  have hd := conjugateL6.continuous.tendsto dh |>.comp hdφ
  have hi := source_integration_by_parts_of_schwartz_limit f g v hfg
    (fun n => conjugateTest (φ n))
    (by simpa only [conjugateTest_toLp, Function.comp_def] using hv)
    (by simpa only [conjugateTest_derivative, conjugateTest_toLp, Function.comp_def] using hd)
  calc
    _ = ∫ x, f x * conjugateL6 dh x := by
      apply integral_congr_ae
      filter_upwards [conjugateL6_coeFn dh] with x hx
      rw [hx]
    _ = -(∫ x, g x * conjugateL6 h x) := hi
    _ = _ := by
      congr 1
      apply integral_congr_ae
      filter_upwards [conjugateL6_coeFn h] with x hx
      rw [hx]

/-- The exact first/second regularizer pair supplies the conjugate test
limit; no H1 assumption on f, no abstract integration-by-parts field. -/
theorem regularized_conjugate_source_integration_by_parts
    (hDensity : OrdinaryH1Density) {K : ℝ} (hSob : OrdinarySobolev K)
    (n : ℕ) (u : EnergyState) (j k : Fin 3) (f g : Source)
    (hfg : ∂_{coordinate k} (Lp.toTemperedDistribution f) = Lp.toTemperedDistribution g) :
    (∫ x, f x * star (energyValue
      ((secondCutoff n k j).energyCLM hDensity hSob u) x)) =
      -(∫ x, g x * star (energyValue
        ((firstCutoff n j).energyCLM hDensity hSob u) x)) := by
  obtain ⟨φ,hφ,hdφ⟩ := derivative_schwartz_L6_limits hDensity hSob n u j k
  exact conjugate_source_integration_by_parts_of_schwartz_limit f g (coordinate k)
    hfg φ hφ hdφ

#print axioms conjugateTest_derivative
#print axioms conjugateTest_toLp
#print axioms conjugate_source_integration_by_parts_of_schwartz_limit
#print axioms regularized_conjugate_source_integration_by_parts
end HartreeF.WeakSourcePairing
