import FEnergySmoothDensity

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000
open MeasureTheory Filter Set LineDeriv
open scoped ENNReal Topology SchwartzMap
namespace HartreeF.EnergySpace
open SobolevStretch StationarySelfTest

/-- The canonical Schwartz inclusion into the actual value/weak-gradient graph. -/
def schwartzEnergyState (φ : Test) : EnergyState :=
  ⟨(φ.toLp 6 volume, fun j => (∂_{coordinate j} φ).toLp 2 volume), by
    apply (mem_energySubmodule _).mpr
    intro j
    simp only [Lp.toTemperedDistribution_toLp_eq]
    exact TemperedDistribution.lineDerivOp_toTemperedDistributionCLM_eq φ (coordinate j)⟩

theorem schwartzEnergyState_value (φ : Test) :
    energyValue (schwartzEnergyState φ) = φ.toLp 6 volume := rfl

theorem schwartzEnergyState_gradient (φ : Test) (j : Fin 3) :
    energyGradient j (schwartzEnergyState φ) = (∂_{coordinate j} φ).toLp 2 volume := rfl

theorem schwartzEnergyState_value_ae (φ : Test) :
    (energyValue (schwartzEnergyState φ) : Space → ℂ) =ᵐ[volume] φ := φ.coeFn_toLp 6 volume

theorem energyValue_injective : Function.Injective energyValue := by
  intro u v huv
  apply Subtype.ext
  apply Prod.ext huv
  funext j
  have hinj : Function.Injective (Lp.toTemperedDistribution : L2 → TD) :=
    LinearMap.ker_eq_bot.mp (Lp.ker_toTemperedDistributionCLM_eq_bot
      (F := ℂ) (μ := (volume : Measure Space)) (p := 2))
  apply hinj
  change Lp.toTemperedDistribution (u.val.2 j) = Lp.toTemperedDistribution (v.val.2 j)
  rw [← (mem_energySubmodule u.val).mp u.property j,
    ← (mem_energySubmodule v.val).mp v.property j]
  exact congrArg (fun f : L6 => ∂_{coordinate j} (Lp.toTemperedDistribution f)) huv

/-- Standard Mathlib compact-smooth to Schwartz construction, without a new assumption. -/
def compactSmoothSchwartz (φ : CompactSmoothReal × CompactSmoothReal) : Test :=
  (compactSmoothFunction_support φ).toSchwartzMap (compactSmoothFunction_contDiff φ)

theorem compactSmoothSchwartz_energy (φ : CompactSmoothReal × CompactSmoothReal) :
    schwartzEnergyState (compactSmoothSchwartz φ) = compactSmoothState φ := by
  apply energyValue_injective
  apply Lp.ext
  exact (schwartzEnergyState_value_ae (compactSmoothSchwartz φ)).trans
    (compactSmoothState_value_ae φ).symm

/-- The literal Schwartz inclusion has dense range in the actual homogeneous energy space. -/
theorem schwartzEnergyState_denseRange (hDensity : OrdinaryH1Density)
    {K : ℝ} (hSob : OrdinarySobolev K) : DenseRange schwartzEnergyState := by
  apply (compactSmoothState_denseRange hDensity hSob).mono
  rintro _ ⟨φ, rfl⟩
  exact ⟨compactSmoothSchwartz φ, compactSmoothSchwartz_energy φ⟩

/-- Actual Schwartz states approximate every C43 state, with the target explicitly given. -/
theorem schwartzEnergyState_approximation (hDensity : OrdinaryH1Density)
    {K : ℝ} (hSob : OrdinarySobolev K) (u : EnergyState) :
    ∃ φ : ℕ → Test,
      Tendsto (fun n => schwartzEnergyState (φ n)) atTop (𝓝 u) := by
  obtain ⟨φ, hφ⟩ := compactSmoothState_approximation hDensity hSob u
  exact ⟨fun n => compactSmoothSchwartz (φ n), by simpa only [compactSmoothSchwartz_energy] using hφ⟩

end HartreeF.EnergySpace
