import F121PureLowExactLinf
import FCoordinateGradientPack

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory
open scoped ENNReal
namespace HartreeF.BoundedHartreeGradient
open EnergySpace EnergySpace.Highpass PhysicalLowpass SobolevStretch StationarySelfTest
  ForcingDomain WeakHartreeProduct GradientMajorants TimeHolder

/-- Pointwise Euclidean complex gradient, with no dimension loss. -/
theorem complexGradient_norm_le_sum (U W : Space → Space) (x : Space) :
    ‖complexGradient U W x‖ ≤ ‖U x‖ + ‖W x‖ := by
  have h := complexGradient_norm_sq U W x
  have h0 := norm_nonneg (complexGradient U W x)
  have hU := norm_nonneg (U x)
  have hW := norm_nonneg (W x)
  nlinarith [mul_nonneg hU hW]

/-- The pre-existing actualFullGradient is precisely the complex vector formed
from the actual real and imaginary forcing gradients. -/
theorem actualFullGradient_eq_complex (α c : ℝ) (u : Space → ℂ)
    (U W : Space → Space) :
    actualFullGradient α c u U W =
      complexGradient (forcingGradientRe α c u U W) (forcingGradientIm α c u U W) := by
  funext x
  apply PiLp.ext
  intro j
  rw [actualFullGradient_coordinate]
  apply Complex.ext <;> simp [complexGradient]

/-- L1 membership is produced from the two actual weak-gradient domains. -/
theorem complexGradient_integrable {U W : Space → Space}
    (hU : MemLp U 1 volume) (hW : MemLp W 1 volume) :
    Integrable (complexGradient U W) volume := by
  have hc (j : Fin 3) : MemLp (fun x => complexGradient U W x j) 1 volume := by
    have hr := (hU.continuousLinearMap_comp
      (EuclideanSpace.proj j : Space →L[ℝ] ℝ)).continuousLinearMap_comp Complex.ofRealCLM
    have hi := (hW.continuousLinearMap_comp
      (EuclideanSpace.proj j : Space →L[ℝ] ℝ)).continuousLinearMap_comp Complex.ofRealCLM
    exact hr.add (hi.const_mul Complex.I)
  have he : complexGradient U W = fun x => packGradient
      (complexGradient U W x 0) (complexGradient U W x 1) (complexGradient U W x 2) := by
    funext x
    apply PiLp.ext
    intro j
    fin_cases j <;> simp [packGradient_coordinate]
  have hm : AEStronglyMeasurable (complexGradient U W) volume := by
    rw [he]
    exact (((hc 0).aestronglyMeasurable.smul_const _).add
      ((hc 1).aestronglyMeasurable.smul_const _)).add
      ((hc 2).aestronglyMeasurable.smul_const _)
  apply (((memLp_one_iff_integrable.mp hU).norm).add
    ((memLp_one_iff_integrable.mp hW).norm)).mono' hm
  exact Filter.Eventually.of_forall (complexGradient_norm_le_sum U W)

/-- The L1 norm of the Euclidean complex gradient is bounded by the sum
already estimated by the Hartree producer. -/
theorem complexGradient_L1_norm_le {U W : Space → Space}
    (hU : MemLp U 1 volume) (hW : MemLp W 1 volume) :
    (eLpNorm (complexGradient U W) 1 volume).toReal ≤
      (eLpNorm U 1 volume).toReal + (eLpNorm W 1 volume).toReal := by
  have hg := complexGradient_integrable hU hW
  have hu := memLp_one_iff_integrable.mp hU
  have hw := memLp_one_iff_integrable.mp hW
  have hn {E : Type*} [NormedAddCommGroup E] {f : Space → E}
      (hf : Integrable f volume) :
      (eLpNorm f 1 volume).toReal = ∫ x, ‖f x‖ := by
    rw [eLpNorm_one_eq_lintegral_enorm hf.aestronglyMeasurable]
    exact (integral_norm_eq_lintegral_enorm hf.aestronglyMeasurable).symm
  rw [hn hg, hn hu, hn hw, ← integral_add hu.norm hw.norm]
  exact integral_mono hg.norm (hu.norm.add hw.norm) (complexGradient_norm_le_sum U W)

/-- Lemma 6.6's first estimate in the full complex Euclidean gradient norm,
for the same actual Hartree forcing, with its L1 domain as a conclusion. -/
theorem lowEnergyState_actualFullGradient_exact_linf
    (hD : OrdinaryH1Density) {K α c : ℝ} (hSob : OrdinarySobolev K)
    (hH : OrdinaryHLS α c)
    (hUpper : 1 < α → ∃ c' : ℝ, OrdinaryHLS (α - 1) c') :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : Cutoff) (M : ℝ) (hM : 0 < M) (u : EnergyState),
      let v := lowEnergyState hD hSob q hM u
      let U := energyProjectedGradient Complex.reCLM v
      let W := energyProjectedGradient Complex.imCLM v
      Integrable (actualFullGradient α c (energyValue v) U W) volume ∧
      (eLpNorm (actualFullGradient α c (energyValue v) U W) 1 volume).toReal ≤
        C * (eLpNorm (fun x => energyValue v x) ∞ volume).toReal *
          pureGradientNorm v ^ (4 + 2 * α) := by
  obtain ⟨C, hC0, hC⟩ := lowEnergyState_forcing_L1_exact_linf_allOrders hD hSob hH hUpper
  refine ⟨C, hC0, ?_⟩
  intro q M hM u
  have h := hC q M hM u
  dsimp only at h ⊢
  rw [actualFullGradient_eq_complex]
  exact ⟨complexGradient_integrable h.2.2.1 h.2.2.2.1,
    (complexGradient_L1_norm_le h.2.2.1 h.2.2.2.1).trans h.2.2.2.2⟩

end HartreeF.BoundedHartreeGradient
