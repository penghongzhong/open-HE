import FHighpassSchwartzBound
import FL2EnergyConstruction

/-! Genuine highpass L2 realization obtained by completion of the dense Schwartz
energy graph. Ordinary H1 density and Sobolev are retained exactly as in F.
No highpass realization, finite original mass, or critical-orbit assumption is input. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 900000
open MeasureTheory FourierTransform Filter LineDeriv
open scoped ENNReal Topology SchwartzMap
namespace HartreeF.EnergySpace.Highpass
open HartreeF.EnergySpace SobolevStretch StationarySelfTest

theorem schwartzEnergyState_sub (φ ψ : Test) :
    schwartzEnergyState (φ - ψ) = schwartzEnergyState φ - schwartzEnergyState ψ := by
  apply energyValue_injective
  change (SchwartzMap.toLpCLM ℂ ℂ 6 volume) (φ - ψ) = _
  rw [map_sub]
  rfl

theorem highSchwartz_l2_difference_bound (q : Cutoff) {L : ℝ} (hL : 0 < L)
    (φ ψ : Test) :
    ‖(highSchwartz q L φ).toLp 2 volume - (highSchwartz q L ψ).toLp 2 volume‖ ≤
      (L⁻¹ * Real.sqrt 3) * ‖schwartzEnergyState φ - schwartzEnergyState ψ‖ := by
  have hs : (highSchwartz q L (φ - ψ)).toLp 2 volume =
      (highSchwartz q L φ).toLp 2 volume - (highSchwartz q L ψ).toLp 2 volume := by
    change (SchwartzMap.toLpCLM ℂ ℂ 2 volume) (highSchwartz q L (φ - ψ)) = _
    rw [map_sub, map_sub]
    rfl
  rw [← hs]
  calc
    _ ≤ L⁻¹ * pureGradientNorm (schwartzEnergyState (φ - ψ)) := highSchwartz_l2_bound q hL _
    _ ≤ L⁻¹ * (Real.sqrt 3 * ‖schwartzEnergyState (φ - ψ)‖) :=
      mul_le_mul_of_nonneg_left (pureGradient_le_sqrt_three_energyState _)
        (inv_nonneg.mpr hL.le)
    _ = _ := by rw [schwartzEnergyState_sub, mul_assoc]

theorem highSchwartz_l2_cauchy (q : Cutoff) {L : ℝ} (hL : 0 < L)
    (φ : ℕ → Test) (hφ : CauchySeq (fun n => schwartzEnergyState (φ n))) :
    CauchySeq (fun n => (highSchwartz q L (φ n)).toLp 2 volume) := by
  let C : ℝ := L⁻¹ * Real.sqrt 3
  have hC : 0 < C := mul_pos (inv_pos.mpr hL) (Real.sqrt_pos.mpr (by norm_num))
  apply Metric.cauchySeq_iff.mpr
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hφ (ε / C) (div_pos hε hC)
  refine ⟨N, fun m hm n hn => ?_⟩
  rw [dist_eq_norm]
  calc
    _ ≤ C * ‖schwartzEnergyState (φ m) - schwartzEnergyState (φ n)‖ :=
      highSchwartz_l2_difference_bound q hL _ _
    _ < C * (ε / C) := mul_lt_mul_of_pos_left
      (by simpa only [dist_eq_norm] using hN m hm n hn) hC
    _ = ε := by field_simp

/-- The actual L2 class is constructed, not postulated as a Bernstein interface. -/
theorem exists_highpass_l2 (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) (q : Cutoff) {L : ℝ} (hL : 0 < L) (u : EnergyState) :
    ∃ f : L2, Lp.toTemperedDistribution f = high q L (energyDistribution u) ∧
      ‖f‖ ≤ L⁻¹ * pureGradientNorm u := by
  obtain ⟨φ, hφ⟩ := schwartzEnergyState_approximation hDensity hSob u
  obtain ⟨f, hf⟩ := cauchySeq_tendsto_of_complete
    (highSchwartz_l2_cauchy q hL φ hφ.cauchySeq)
  refine ⟨f, ?_, ?_⟩
  · have hl := (Lp.toTemperedDistributionCLM ℂ (volume : Measure V) 2).continuous.tendsto f |>.comp hf
    have hr := (high q L).continuous.tendsto (energyDistribution u) |>.comp
      (energyDistribution.continuous.tendsto u |>.comp hφ)
    apply tendsto_nhds_unique hl
    convert hr using 1
    funext n
    simpa only [Function.comp_def, Lp.toTemperedDistributionCLM_apply,
      Lp.toTemperedDistribution_toLp_eq, schwartzEnergyState_distribution] using
        highSchwartz_distribution q hL (φ n)
  · exact le_of_tendsto_of_tendsto hf.norm
      ((pureGradientNorm_tendsto (gradientTendsto_of_tendsto hφ)).const_mul L⁻¹)
      (Eventually.of_forall (fun n => highSchwartz_l2_bound q hL (φ n)))

def highValueL2 (hDensity : OrdinaryH1Density) {K : ℝ} (hSob : OrdinarySobolev K)
    (q : Cutoff) {L : ℝ} (hL : 0 < L) (u : EnergyState) : L2 :=
  (exists_highpass_l2 hDensity hSob q hL u).choose

theorem highValueL2_distribution (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) (q : Cutoff) {L : ℝ} (hL : 0 < L) (u : EnergyState) :
    Lp.toTemperedDistribution (highValueL2 hDensity hSob q hL u) = high q L (energyDistribution u) :=
  (exists_highpass_l2 hDensity hSob q hL u).choose_spec.1

/-- The constructed L2 realization is uniquely fixed by the literal highpass distribution. -/
theorem highValueL2_unique (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) (q : Cutoff) {L : ℝ} (hL : 0 < L)
    (u : EnergyState) (f : L2)
    (hf : Lp.toTemperedDistribution f = high q L (energyDistribution u)) :
    f = highValueL2 hDensity hSob q hL u := by
  apply FreeFlow.l2_distribution_injective
  rw [hf, highValueL2_distribution]

theorem highValueL2_bound (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) (q : Cutoff) {L : ℝ} (hL : 0 < L) (u : EnergyState) :
    ‖highValueL2 hDensity hSob q hL u‖ ≤ L⁻¹ * pureGradientNorm u :=
  (exists_highpass_l2 hDensity hSob q hL u).choose_spec.2

theorem highValueL2_derivative (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) (q : Cutoff) {L : ℝ} (hL : 0 < L)
    (u : EnergyState) (j : Fin 3) :
    ∂_{coordinate j} (Lp.toTemperedDistribution (highValueL2 hDensity hSob q hL u)) =
      Lp.toTemperedDistribution (highL2 q L (energyGradient j u)) := by
  rw [highValueL2_distribution, derivative_high q hL, energyDistribution_derivative,
    highL2_distribution q hL]
  rfl

def highEnergyState (hDensity : OrdinaryH1Density) {K : ℝ} (hSob : OrdinarySobolev K)
    (q : Cutoff) {L : ℝ} (hL : 0 < L) (u : EnergyState) : EnergyState :=
  l2EnergyState hDensity hSob (highValueL2 hDensity hSob q hL u)
    (fun j => highL2 q L (energyGradient j u))
    (highValueL2_derivative hDensity hSob q hL u)

theorem highEnergyState_value_ae (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) (q : Cutoff) {L : ℝ} (hL : 0 < L) (u : EnergyState) :
    (energyValue (highEnergyState hDensity hSob q hL u) : V → ℂ) =ᵐ[volume]
      highValueL2 hDensity hSob q hL u :=
  l2EnergyState_value_ae hDensity hSob _ _ _

theorem highEnergyState_distribution (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) (q : Cutoff) {L : ℝ} (hL : 0 < L) (u : EnergyState) :
    energyDistribution (highEnergyState hDensity hSob q hL u) = high q L (energyDistribution u) := by
  rw [highEnergyState, l2EnergyState_distribution, highValueL2_distribution]

/-- The constructed homogeneous state is the unique actual L6/gradient realization. -/
theorem highEnergyState_unique (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) (q : Cutoff) {L : ℝ} (hL : 0 < L)
    (u v : EnergyState) (hv : energyDistribution v = high q L (energyDistribution u)) :
    v = highEnergyState hDensity hSob q hL u := by
  apply energyDistribution_injective
  rw [hv, highEnergyState_distribution]

theorem highEnergyState_gradient (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) (q : Cutoff) {L : ℝ} (hL : 0 < L)
    (u : EnergyState) (j : Fin 3) :
    energyGradient j (highEnergyState hDensity hSob q hL u) = highL2 q L (energyGradient j u) := rfl

theorem highEnergyState_memLp_two (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) (q : Cutoff) {L : ℝ} (hL : 0 < L) (u : EnergyState) :
    MemLp (energyValue (highEnergyState hDensity hSob q hL u) : V → ℂ) 2 volume :=
  (memLp_congr_ae (highEnergyState_value_ae hDensity hSob q hL u)).mpr
    (Lp.memLp (highValueL2 hDensity hSob q hL u))

/-- The exact L6 representative has the same finite L2 norm and pure-gradient bound. -/
theorem highEnergyState_l2_bound (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) (q : Cutoff) {L : ℝ} (hL : 0 < L) (u : EnergyState) :
    (eLpNorm (energyValue (highEnergyState hDensity hSob q hL u) : V → ℂ) 2 volume).toReal ≤
      L⁻¹ * pureGradientNorm u := by
  rw [eLpNorm_congr_ae (highEnergyState_value_ae hDensity hSob q hL u), ← Lp.norm_def]
  exact highValueL2_bound hDensity hSob q hL u

/-- Actual integration-by-parts for the L2 representative, in every real projection. -/
theorem highValueL2_actual_weak_gradient (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) (q : Cutoff) {L : ℝ} (hL : 0 < L)
    (u : EnergyState) (A : ℂ →L[ℝ] ℝ) :
    HasWeakGradient (fun x => A (highValueL2 hDensity hSob q hL u x))
      (energyProjectedGradient A (highEnergyState hDensity hSob q hL u)) :=
  l2_hasWeakGradient _ _ (highValueL2_derivative hDensity hSob q hL u) A

theorem highEnergyState_actual_weak_gradient (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) (q : Cutoff) {L : ℝ} (hL : 0 < L) (u : EnergyState) :
    InDotH1 (energyValue (highEnergyState hDensity hSob q hL u))
      (energyProjectedGradient Complex.reCLM (highEnergyState hDensity hSob q hL u))
      (energyProjectedGradient Complex.imCLM (highEnergyState hDensity hSob q hL u)) :=
  energyState_inDotH1 _

end HartreeF.EnergySpace.Highpass
