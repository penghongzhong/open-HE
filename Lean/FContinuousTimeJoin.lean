import Mathlib.Topology.Piecewise
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Instances.Real.Lemmas

noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace HartreeF.CriticalPathGluing

/-- Joining two actual continuous maps at an equal real-time value. -/
def joinContinuous {E : Type*} [TopologicalSpace E] (c : ℝ)
    (f g : C(ℝ, E)) (h : f c = g c) : C(ℝ, E) where
  toFun := (Set.Iic c).piecewise f g
  continuous_toFun := by
    apply Continuous.piecewise _ f.continuous g.continuous
    intro t ht
    have ht' : t = c := by simpa only [frontier_Iic, Set.mem_singleton_iff] using ht
    exact ht' ▸ h

end HartreeF.CriticalPathGluing
