import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Topology.UniformSpace.Ascoli
import Mathlib.Topology.MetricSpace.UniformConvergence
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Analysis.Complex.Basic

noncomputable section
set_option autoImplicit false
set_option warningAsError true
open Filter
open scoped Topology NNReal
namespace HartreeF.StrongOperatorPaths

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {T : Type*} [TopologicalSpace T] [CompactSpace T]

def mapPath (P : E →L[ℂ] E) (u : C(T,E)) : C(T,E) :=
  ⟨fun t => P (u t), P.continuous.comp u.continuous⟩

/-- Strong convergence of a uniformly bounded family is uniform on each
actual compact continuous trajectory. Pointwise convergence alone is not
used as uniform convergence. -/
theorem mapPath_tendsto (P : ℕ → E →L[ℂ] E) (C : ℝ≥0)
    (hbound : ∀ n, ‖P n‖ ≤ C)
    (hstrong : ∀ x, Tendsto (fun n => P n x) atTop (𝓝 x))
    (u : C(T,E)) : Tendsto (fun n => mapPath (P n) u) atTop (𝓝 u) := by
  have hL : ∀ n, LipschitzWith C (P n) := fun n =>
    ContinuousLinearMap.lipschitzWith_of_opNorm_le (hbound n)
  have hEq : Equicontinuous (fun n x => P n x) :=
    (LipschitzWith.uniformEquicontinuous (fun n x => P n x) C hL).equicontinuous
  have hComp : Equicontinuous (fun n t => P n (u t)) := by
    rw [equicontinuous_iff_continuous] at hEq ⊢
    exact hEq.comp u.continuous
  have hp : Tendsto (fun n t => P n (u t)) atTop (𝓝 (fun t => u t)) :=
    tendsto_pi_nhds.mpr (fun t => hstrong (u t))
  have hu := (hComp.tendsto_uniformFun_iff_pi atTop (fun t => u t)).mpr hp
  apply ContinuousMap.tendsto_iff_tendstoUniformly.mpr
  exact UniformFun.tendsto_iff_tendstoUniformly.mp hu

#print axioms mapPath
#print axioms mapPath_tendsto
end HartreeF.StrongOperatorPaths
