import FRetardedLinearity
import FFreeFlowContinuity

noncomputable section
set_option autoImplicit false
set_option warningAsError true
open MeasureTheory Filter
open scoped ENNReal Topology SchwartzMap
namespace HartreeF.Retarded
open FreeFlow

/-- Exact time transport under the already constructed actual Fourier group. -/
theorem scalarIntegrand_transport (r t s : ℝ) (F : EndpointSource) (φ : Test) :
    scalarIntegrand t F (freeTest r φ) s = scalarIntegrand (r+t) F φ s := by
  have he := congrArg (fun T : TD => T φ)
    (free_add r (t-s) (Lp.toTemperedDistribution (F s)))
  simpa only [free_apply, scalarIntegrand, add_sub_assoc] using he.symm

/-- The pure integral has no additional phase factor or forcing-sign coefficient. -/
theorem restrictedL2_transport {C : ℝ} (h : OrdinaryEndpointBound C)
    (J : Set ℝ) (hJ : MeasurableSet J) (r t : ℝ) (F : EndpointSource) :
    freeL2 r (restrictedL2 h J hJ t F) = restrictedL2 h J hJ (r+t) F := by
  apply l2_distribution_injective
  ext φ
  rw [freeL2_distribution, free_apply, restrictedL2_scalar, restrictedL2_scalar]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun s => scalarIntegrand_transport r t s F φ)

theorem restrictedL2_transport_from_zero {C : ℝ} (h : OrdinaryEndpointBound C)
    (J : Set ℝ) (hJ : MeasurableSet J) (t : ℝ) (F : EndpointSource) :
    restrictedL2 h J hJ t F = freeL2 t (restrictedL2 h J hJ 0 F) := by
  simpa only [add_zero] using (restrictedL2_transport h J hJ t 0 F).symm

/-- Uniform norm preservation permits simultaneously changing time and input. -/
theorem freeL2_joint_continuous : Continuous (fun z : ℝ × L2 => freeL2 z.1 z.2) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hvar : Tendsto (fun w : ℝ × L2 => ‖w.2 - z.2‖) (𝓝 z) (𝓝 0) := by
    simpa only [Function.comp_def, sub_self, norm_zero] using
      ((continuous_snd.tendsto z).sub (tendsto_const_nhds (x := z.2))).norm
  have htime : Tendsto (fun w : ℝ × L2 => ‖freeL2 w.1 z.2 - freeL2 z.1 z.2‖)
      (𝓝 z) (𝓝 0) := by
    simpa only [Function.comp_def, sub_self, norm_zero] using
      ((((freeL2_time_continuous z.2).comp continuous_fst).tendsto z).sub
        (tendsto_const_nhds (x := freeL2 z.1 z.2))).norm
  apply squeeze_zero (fun _ => norm_nonneg _) _ (by simpa using hvar.add htime)
  intro w
  calc
    _ = ‖(freeL2 w.1 w.2 - freeL2 w.1 z.2) +
        (freeL2 w.1 z.2 - freeL2 z.1 z.2)‖ := by congr 1; abel
    _ ≤ ‖freeL2 w.1 w.2 - freeL2 w.1 z.2‖ +
        ‖freeL2 w.1 z.2 - freeL2 z.1 z.2‖ := norm_add_le _ _
    _ = _ := by rw [← map_sub, freeL2_norm]

end HartreeF.Retarded
