import FNonlocalBrezisLieb
import FStateEnergyCalculus

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1500000
open MeasureTheory Filter
open scoped ENNReal Topology RealInnerProductSpace
namespace HartreeF.NonlocalBL
open EnergySpace EnergyVariation StateEnergy ForcingDomain SharpOrdinary

/-- The kinetic split from ordinary weak convergence of the actual coordinate L2 gradients. -/
theorem gradientSquared_split_weak {g : ℕ → EnergyState} (u : EnergyState)
    (hweak : ∀ j : Fin 3, ∀ v : L2,
      Tendsto (fun n => inner ℝ (energyGradient j (g n)) v) atTop (𝓝 0)) :
    Tendsto (fun n => gradientSquared (g n+u)-gradientSquared (g n)-gradientSquared u)
      atTop (𝓝 0) := by
  have hid (n : ℕ) : gradientSquared (g n+u)-gradientSquared (g n)-gradientSquared u =
      ∑ j : Fin 3, 2*inner ℝ (energyGradient j (g n)) (energyGradient j u) := by
    simp only [gradientSquared, map_add, norm_add_sq_real, Finset.sum_add_distrib]
    ring
  have ht := tendsto_finsetSum Finset.univ (fun j _ => (hweak j (energyGradient j u)).const_mul 2)
  simpa only [hid, mul_zero, Finset.sum_const_zero] using ht

/-- The nonlinear interaction split is transferred to actual L6 quotient representatives. -/
theorem interactionLp_brezis_lieb_remainder {alpha B : ℝ}
    (hH : SharpOrdinaryHLS alpha)
    (hOrd : OrdinaryHLS alpha (HeatRiesz.standardRieszConstant alpha))
    {g : ℕ → EnergyState} (u : EnergyState)
    (hbound : ∀ n, ‖energyValue (g n)‖ ≤ B)
    (hlim : ∀ᵐ x ∂volume, Tendsto (fun n => energyValue (g n) x) atTop (𝓝 0)) :
    Tendsto (fun n => interactionLp alpha (energyValue (g n+u))-
      interactionLp alpha (energyValue (g n))-interactionLp alpha (energyValue u)) atTop (𝓝 0) := by
  have ht := interaction_brezis_lieb_remainder hH hOrd
    (fun n => Lp.memLp (energyValue (g n))) (Lp.memLp (energyValue u)) hbound hlim
  have he (n : ℕ) : interactionLp alpha (energyValue (g n+u)) =
      DirectionalCoercivity.interaction alpha ((energyValue (g n) : Space → ℂ)+energyValue u) := by
    unfold interactionLp
    rw [map_add]
    exact interaction_congr_ae alpha (Lp.coeFn_add _ _)
  simp_rw [he]
  exact ht

/-- One fixed profile plus weak/a.e.-vanishing remainder: genuine total-energy decoupling. -/
theorem totalEnergy_split_remainder {alpha B : ℝ}
    (hH : SharpOrdinaryHLS alpha)
    (hOrd : OrdinaryHLS alpha (HeatRiesz.standardRieszConstant alpha))
    {g : ℕ → EnergyState} (u : EnergyState)
    (hbound : ∀ n, ‖energyValue (g n)‖ ≤ B)
    (hlim : ∀ᵐ x ∂volume, Tendsto (fun n => energyValue (g n) x) atTop (𝓝 0))
    (hweak : ∀ j : Fin 3, ∀ v : L2,
      Tendsto (fun n => inner ℝ (energyGradient j (g n)) v) atTop (𝓝 0)) :
    Tendsto (fun n => totalEnergy alpha (g n+u)-totalEnergy alpha (g n)-totalEnergy alpha u)
      atTop (𝓝 0) := by
  have ht := ((gradientSquared_split_weak u hweak).div_const 2).sub
    ((interactionLp_brezis_lieb_remainder hH hOrd u hbound hlim).div_const (2*(3+alpha)))
  have he (n : ℕ) : totalEnergy alpha (g n+u)-totalEnergy alpha (g n)-totalEnergy alpha u =
      (gradientSquared (g n+u)-gradientSquared (g n)-gradientSquared u)/2-
      (interactionLp alpha (energyValue (g n+u))-interactionLp alpha (energyValue (g n))-
        interactionLp alpha (energyValue u))/(2*(3+alpha)) := by
    unfold totalEnergy
    ring
  simpa only [he, zero_div, sub_zero] using ht

/-- Actual one-profile energy splitting. The extraction of this weak/a.e. subsequence
is deliberately not asserted here. No initial scalar L2 or strong L6 hypothesis occurs. -/
theorem totalEnergy_split_one_profile {alpha B : ℝ}
    (hH : SharpOrdinaryHLS alpha)
    (hOrd : OrdinaryHLS alpha (HeatRiesz.standardRieszConstant alpha))
    {u : ℕ → EnergyState} (f : EnergyState)
    (hbound : ∀ n, ‖energyValue (u n)‖ ≤ B)
    (hlim : ∀ᵐ x ∂volume, Tendsto (fun n => energyValue (u n) x) atTop (𝓝 (energyValue f x)))
    (hweak : ∀ j : Fin 3, ∀ v : L2,
      Tendsto (fun n => inner ℝ (energyGradient j (u n)) v) atTop
        (𝓝 (inner ℝ (energyGradient j f) v))) :
    Tendsto (fun n => totalEnergy alpha (u n)-totalEnergy alpha (u n-f)-totalEnergy alpha f)
      atTop (𝓝 0) := by
  have hb (n : ℕ) : ‖energyValue (u n-f)‖ ≤ B+‖energyValue f‖ := by
    rw [map_sub]
    exact (norm_sub_le _ _).trans (add_le_add (hbound n) le_rfl)
  have hae (n : ℕ) : (energyValue (u n-f) : Space → ℂ) =ᵐ[volume]
      (fun x => energyValue (u n) x-energyValue f x) := by
    rw [map_sub]
    exact Lp.coeFn_sub _ _
  have hz : ∀ᵐ x ∂volume, Tendsto (fun n => energyValue (u n-f) x) atTop (𝓝 0) := by
    filter_upwards [hlim, ae_all_iff.mpr hae] with x hx he
    have ht := hx.sub_const (energyValue f x)
    simpa only [he, sub_self] using ht
  have hw (j : Fin 3) (v : L2) :
      Tendsto (fun n => inner ℝ (energyGradient j (u n-f)) v) atTop (𝓝 0) := by
    simpa only [map_sub, inner_sub_left, sub_self] using (hweak j v).sub_const
      (inner ℝ (energyGradient j f) v)
  simpa only [sub_add_cancel] using totalEnergy_split_remainder hH hOrd f hb hz hw

#print axioms gradientSquared_split_weak
#print axioms interactionLp_brezis_lieb_remainder
#print axioms totalEnergy_split_remainder
#print axioms totalEnergy_split_one_profile
end HartreeF.NonlocalBL
