import DensityWeakGradient
import DensityDerivativeDifference

/-! Actual density-side Hartree weak chain rule for every 0 < alpha < 3.
This proves no Riesz convolution differentiation or weak product identity for F. -/
noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal
namespace HartreeF.WeakHartreeChain
open SobolevStretch StationarySelfTest

def hartreeDensityGradient (α : ℝ) (u : Space → ℂ) (U V : Space → Space) : Space → Space :=
  fun x => ((3+α)*‖u x‖^(1+α)) • ((u x).re • U x+(u x).im • V x)

theorem hartreeDensityGradient_eq (α : ℝ) (u : Space → ℂ) (U V : Space → Space) :
    hartreeDensityGradient α u U V = densityGradient (3+α) u U V := by
  funext x
  rw [densityGradient_formula]
  simp only [hartreeDensityGradient,show 3+α-2 = 1+α by ring]

theorem hartree_density_hasWeakGradient (hDensity : OrdinaryH1Density)
    {α : ℝ} (hα : 0 < α) (hα3 : α < 3)
    {u : Space → ℂ} {U V : Space → Space} (hu : InDotH1 u U V)
    (hu10 : MemLp u 10 volume)
    (hU : MemLp U (ENNReal.ofReal (30/13 : ℝ)) volume)
    (hV : MemLp V (ENNReal.ofReal (30/13 : ℝ)) volume) :
    HasWeakGradient (powerDensity α u) (hartreeDensityGradient α u U V) := by
  rw [hartreeDensityGradient_eq]
  exact density_hasWeakGradient hDensity (by linarith) (by linarith) hu hu10 hU hV

theorem hartree_density_memLp {α : ℝ} (hα : 0 < α)
    {u : Space → ℂ} {U V : Space → Space} (hu : InDotH1 u U V) :
    MemLp (powerDensity α u) (ENNReal.ofReal (6/(3+α))) volume :=
  density_Lp (by linarith : 0 < 3+α) (by simpa using hu.function_L6)

theorem hartreeDensityGradient_memLp {α : ℝ} (hα : 0 < α)
    {u : Space → ℂ} {U V : Space → Space} (hu10 : MemLp u 10 volume)
    (hU : MemLp U (ENNReal.ofReal (30/13 : ℝ)) volume)
    (hV : MemLp V (ENNReal.ofReal (30/13 : ℝ)) volume) :
    MemLp (hartreeDensityGradient α u U V) (ENNReal.ofReal (30/(19+3*α))) volume := by
  rw [hartreeDensityGradient_eq]
  convert densityGradient_memLp (by linarith : 1 < 3+α) hu10 hU hV using 1
  congr 2
  ring

#print axioms hartreeDensityGradient_eq
#print axioms hartree_density_hasWeakGradient
#print axioms hartree_density_memLp
#print axioms hartreeDensityGradient_memLp
end HartreeF.WeakHartreeChain
