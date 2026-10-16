import F121GeneralAnnularL1
import F121ComplexGradientL1

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory LineDeriv
open scoped ENNReal
namespace HartreeF.GeneralAnnular
open EnergySpace EnergySpace.Highpass MassRecovery SobolevStretch WeakHartreeProduct
  StationarySelfTest ForcingDomain BoundedHartreeGradient YoungSource

/-- The actual real and imaginary weak derivatives produce the general annular
L1 representative and its quantitative inverse-gradient estimate. -/
theorem actual_weak_gradient_annular {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {f : V → ℂ} {U W : V → V} (hf : MemLp f p volume)
    (hU : MemLp U 1 volume) (hW : MemLp W 1 volume)
    (hwR : HasWeakGradient (fun x => (f x).re) U)
    (hwI : HasWeakGradient (fun x => (f x).im) W)
    (q : Symbol) {L : ℝ} (hL : 0 < L) :
    Lp.toTemperedDistribution (annularL1Value q hL (AnnularL1.weakGradientOne hU hW)) =
      annular q L (Lp.toTemperedDistribution (hf.toLp f)) ∧
    ‖annularL1Value q hL (AnnularL1.weakGradientOne hU hW)‖ ≤
      (annularConstant q / L) * ∑ j : Fin 3, ‖AnnularL1.weakGradientOne hU hW j‖ := by
  refine ⟨annularL1Value_distribution q hL _ _ ?_, annularL1Value_norm q hL _⟩
  intro j
  exact weak_gradient_tempered_derivative hf hU hW hwR hwI (coordinate j)

/-- The general annular source of the same actual lowpass Hartree state has a
constructed L1 representative. No global forcing-L1 assumption is used. -/
theorem lowEnergyState_general_annular_L1
    (hD : OrdinaryH1Density) {K α c : ℝ} (hSob : OrdinarySobolev K)
    (hH : OrdinaryHLS α c)
    (hUpper : 1 < α → ∃ c' : ℝ, OrdinaryHLS (α - 1) c')
    (qLow : Cutoff) (qAnn : Symbol) {M L : ℝ}
    (hM : 0 < M) (hL : 0 < L) (u : EnergyState) :
    let v := lowEnergyState hD hSob qLow hM u
    ∃ (hf : MemLp (forcing α c (energyValue v)) sourceExponent volume)
      (g : OneSpace),
      Integrable (g : V → ℂ) volume ∧
      Lp.toTemperedDistribution g = annular qAnn L
        (Lp.toTemperedDistribution (hf.toLp (forcing α c (energyValue v)))) := by
  let v := lowEnergyState hD hSob qLow hM u
  obtain ⟨C, hC⟩ := forcing_energy_domain_bound hH
  have hf : MemLp (forcing α c (energyValue v)) sourceExponent volume :=
    (hC (energyValue v) (Lp.memLp _)).1
  have hG := lowEnergyState_forcing_L1_weakGradients_allOrders hD hSob hH hUpper qLow hM u
  have h := actual_weak_gradient_annular hf hG.2.2.1 hG.2.2.2 hG.1 hG.2.1 qAnn hL
  exact ⟨hf, _, memLp_one_iff_integrable.mp (Lp.memLp _), h.1⟩

end HartreeF.GeneralAnnular
