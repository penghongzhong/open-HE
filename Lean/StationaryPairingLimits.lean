import StationaryWeakEquation
import ActualPairingContinuity

/-! Specialization of the independently produced actual integral-continuity
lemmas to the exact exponents used by the Hartree stationary equation. -/
noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Set
open scoped RealInnerProductSpace ENNReal Topology
namespace HartreeF.StationarySelfTest

theorem inner_pairing_integrable {G V : Space → Space}
    (hG : MemLp G 2 volume) (hV : MemLp V 2 volume) :
    Integrable (fun x => ⟪G x, V x⟫) volume :=
  StationaryPairing.integral_inner_domain hG hV

theorem inner_pairing_tendsto {G V : Space → Space} {Vn : ℕ → Space → Space}
    (hG : MemLp G 2 volume) (hV : MemLp V 2 volume)
    (hVn : ∀ n, MemLp (Vn n) 2 volume)
    (ht : Tendsto (fun n => eLpNorm (fun x => Vn n x - V x) 2 volume) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, ⟪G x, Vn n x⟫) atTop (𝓝 (∫ x, ⟪G x, V x⟫)) :=
  StationaryPairing.integral_inner_tendsto_of_eLpNorm hG hV hVn ht

theorem holder_six_fifths_six : ENNReal.HolderTriple (ENNReal.ofReal (6 / 5 : ℝ)) 6 1 := by
  have h : Real.HolderTriple (6 / 5) 6 1 := by constructor <;> norm_num
  simpa only [ENNReal.ofReal_ofNat, ENNReal.ofReal_one] using h.ennrealOfReal

theorem forcing_pairing_integrable {f v : Space → ℝ}
    (hf : MemLp f (ENNReal.ofReal (6 / 5 : ℝ)) volume) (hv : MemLp v 6 volume) :
    Integrable (fun x => f x * v x) volume := by
  let := holder_six_fifths_six
  exact memLp_one_iff_integrable.mp (hf.fun_mul hv)

theorem forcing_pairing_tendsto {f v : Space → ℝ} {vn : ℕ → Space → ℝ}
    (hf : MemLp f (ENNReal.ofReal (6 / 5 : ℝ)) volume) (hv : MemLp v 6 volume)
    (hvn : ∀ n, MemLp (vn n) 6 volume)
    (ht : Tendsto (fun n => eLpNorm (fun x => vn n x - v x) 6 volume) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, f x * vn n x) atTop (𝓝 (∫ x, f x * v x)) := by
  let := holder_six_fifths_six
  exact StationaryPairing.integral_mul_tendsto_of_eLpNorm hf hv hvn ht

#print axioms inner_pairing_integrable
#print axioms inner_pairing_tendsto
#print axioms holder_six_fifths_six
#print axioms forcing_pairing_integrable
#print axioms forcing_pairing_tendsto
end HartreeF.StationarySelfTest
