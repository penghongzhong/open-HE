import F121GradientSameStateSmallOrder
import F121GradientSameStateUpperOrder
import FLowEnergyHartreeAllOrders
import F121PureLowAnnularBridge

/-! Lemma 6.6 component: actual lowpass Hartree weak derivatives with the
lowpass state's OWN gradient norm. Ordinary analytic interfaces stay explicit. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory
open scoped ENNReal
namespace HartreeF.BoundedHartreeGradient
open EnergySpace EnergySpace.Highpass PhysicalLowpass SobolevStretch StationarySelfTest
  ForcingDomain WeakHartreeProduct WeakHartreeChain GradientMajorants YoungSource

/-- All orders from OrdinaryHLS: 0 < alpha < 3. The extra ordinary interface is
consumed only when 1 < alpha. The constant is chosen before q, M, original u, A. -/
theorem lowEnergyState_forcing_L1_gradient_sameState_allOrders
    (hDensity : OrdinaryH1Density) {K α c : ℝ} (hSob : OrdinarySobolev K)
    (hH : OrdinaryHLS α c)
    (hUpper : 1 < α → ∃ c' : ℝ, OrdinaryHLS (α - 1) c') :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : Cutoff) (M : ℝ) (hM : 0 < M) (u : EnergyState)
      (A : ℝ), 0 ≤ A →
      (∀ᵐ x ∂volume, ‖energyValue (lowEnergyState hDensity hSob q hM u) x‖ ≤ A) →
      let v := lowEnergyState hDensity hSob q hM u
      let U := energyProjectedGradient Complex.reCLM v
      let V := energyProjectedGradient Complex.imCLM v
      (eLpNorm (forcingGradientRe α c (energyValue v) U V) 1 volume).toReal +
        (eLpNorm (forcingGradientIm α c (energyValue v) U V) 1 volume).toReal ≤
        C * A * pureGradientNorm v ^ (4 + 2 * α) := by
  by_cases hα1 : α ≤ 1
  · exact lowEnergyState_forcing_L1_gradient_sameState_smallOrder hDensity hSob hH hα1
  · obtain ⟨c', hLowerHLS⟩ := hUpper (lt_of_not_ge hα1)
    exact lowEnergyState_forcing_L1_gradient_sameState_upperOrder hDensity hSob hH hLowerHLS

/-- The full same-state producer interface: two actual weak-gradient identities,
two genuine L1 memberships, and their quantitative sum with the arbitrary value
bound A. A future D_L-to-value estimate may instantiate A without changing the
Hartree producer or the original pure-gradient factor. -/
theorem lowEnergyState_forcing_L1_sameState_allOrders
    (hDensity : OrdinaryH1Density) {K α c : ℝ} (hSob : OrdinarySobolev K)
    (hH : OrdinaryHLS α c)
    (hUpper : 1 < α → ∃ c' : ℝ, OrdinaryHLS (α - 1) c') :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : Cutoff) (M : ℝ) (hM : 0 < M) (u : EnergyState)
      (A : ℝ), 0 ≤ A →
      (∀ᵐ x ∂volume, ‖energyValue (lowEnergyState hDensity hSob q hM u) x‖ ≤ A) →
      let v := lowEnergyState hDensity hSob q hM u
      let U := energyProjectedGradient Complex.reCLM v
      let V := energyProjectedGradient Complex.imCLM v
      HasWeakGradient (fun x => (forcing α c (energyValue v) x).re)
        (forcingGradientRe α c (energyValue v) U V) ∧
      HasWeakGradient (fun x => (forcing α c (energyValue v) x).im)
        (forcingGradientIm α c (energyValue v) U V) ∧
      MemLp (forcingGradientRe α c (energyValue v) U V) 1 volume ∧
      MemLp (forcingGradientIm α c (energyValue v) U V) 1 volume ∧
      (eLpNorm (forcingGradientRe α c (energyValue v) U V) 1 volume).toReal +
        (eLpNorm (forcingGradientIm α c (energyValue v) U V) 1 volume).toReal ≤
        C * A * pureGradientNorm v ^ (4 + 2 * α) := by
  obtain ⟨C, hC0, hC⟩ :=
    lowEnergyState_forcing_L1_gradient_sameState_allOrders hDensity hSob hH hUpper
  refine ⟨C, hC0, ?_⟩
  intro q M hM u A hA0 hA
  have hw := lowEnergyState_forcing_L1_weakGradients_allOrders hDensity hSob hH hUpper q hM u
  exact ⟨hw.1, hw.2.1, hw.2.2.1, hw.2.2.2, hC q M hM u A hA0 hA⟩

/-- The endpoint alpha=1 uses only OrdinaryHLS 1 c, and has exponent 6.
The actual weak gradients and L1 memberships come from the lower-order producer;
there is no order-zero HLS hypothesis or invocation. -/
theorem lowEnergyState_forcing_L1_sameState_orderOne
    (hDensity : OrdinaryH1Density) {K c : ℝ} (hSob : OrdinarySobolev K)
    (hH : OrdinaryHLS 1 c) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : Cutoff) (M : ℝ) (hM : 0 < M) (u : EnergyState)
      (A : ℝ), 0 ≤ A →
      (∀ᵐ x ∂volume, ‖energyValue (lowEnergyState hDensity hSob q hM u) x‖ ≤ A) →
      let v := lowEnergyState hDensity hSob q hM u
      let U := energyProjectedGradient Complex.reCLM v
      let V := energyProjectedGradient Complex.imCLM v
      HasWeakGradient (fun x => (forcing 1 c (energyValue v) x).re)
        (forcingGradientRe 1 c (energyValue v) U V) ∧
      HasWeakGradient (fun x => (forcing 1 c (energyValue v) x).im)
        (forcingGradientIm 1 c (energyValue v) U V) ∧
      MemLp (forcingGradientRe 1 c (energyValue v) U V) 1 volume ∧
      MemLp (forcingGradientIm 1 c (energyValue v) U V) 1 volume ∧
      (eLpNorm (forcingGradientRe 1 c (energyValue v) U V) 1 volume).toReal +
        (eLpNorm (forcingGradientIm 1 c (energyValue v) U V) 1 volume).toReal ≤
        C * A * pureGradientNorm v ^ (6 : ℝ) := by
  obtain ⟨C, hC0, hC⟩ :=
    lowEnergyState_forcing_L1_gradient_sameState_smallOrder hDensity hSob hH (by norm_num)
  refine ⟨C, hC0, ?_⟩
  intro q M hM u A hA0 hA
  have hw := lowEnergyState_forcing_L1_weakGradients_smallOrder
    hDensity hSob hH (by norm_num) q hM u
  refine ⟨hw.1, hw.2.1, hw.2.2.1, hw.2.2.2, ?_⟩
  simpa only [mul_one, show (4 : ℝ) + 2 = 6 by norm_num] using hC q M hM u A hA0 hA



/-- The previously conditional annular representative is now instantiated with
this same actual Hartree forcing; its L1 weak derivatives are produced here. -/
theorem lowEnergyState_actual_annular_domains
    (hD : OrdinaryH1Density) {K α c : ℝ} (hSob : OrdinarySobolev K)
    (hH : OrdinaryHLS α c)
    (hUpper : 1 < α → ∃ c' : ℝ, OrdinaryHLS (α - 1) c')
    (qLow qAnn : Cutoff) {M L : ℝ} (hM : 0 < M) (hL : 0 < L) (u : EnergyState) :
    let v := lowEnergyState hD hSob qLow hM u
    ∃ (hf : MemLp (forcing α c (energyValue v)) sourceExponent volume)
      (g : MassRecovery.OneSpace),
      Integrable (g : V → ℂ) volume ∧
      MemLp (g : V → ℂ) sourceExponent volume ∧
      Lp.toTemperedDistribution g = AnnularL1.annular qAnn L
        (Lp.toTemperedDistribution (hf.toLp (forcing α c (energyValue v)))) := by
  let v := lowEnergyState hD hSob qLow hM u
  obtain ⟨C, hC⟩ := forcing_energy_domain_bound hH
  have hf : MemLp (forcing α c (energyValue v)) sourceExponent volume :=
    (hC (energyValue v) (Lp.memLp _)).1
  have hG := lowEnergyState_forcing_L1_weakGradients_allOrders hD hSob hH hUpper qLow hM u
  have h := Paper121PureLow.actual_annular_common_representative hf
    hG.2.2.1 hG.2.2.2 hG.1 hG.2.1 qAnn hL
  exact ⟨hf, _, h.1, h.2.1, h.2.2.1⟩

end HartreeF.BoundedHartreeGradient
