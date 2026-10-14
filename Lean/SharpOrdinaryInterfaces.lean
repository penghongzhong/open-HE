import SharpOrdinaryConstants
import HartreeSobolevProducer

/-!
Precisely scoped external ordinary inequalities. Frank--Lieb,
arXiv:1010.5821v3 (3 May2012), https://arxiv.org/pdf/1010.5821,
Eq(1.1)/Theorem2.1 with N=3, lambda=3-alpha gives the real bilinear
L^(6/(3+alpha)) HLS interface below after multiplication by c_alpha.
Eq(1.4), Theorem3.1 and AppendixA give the complex Sobolev squared-norm
interface. Both quantify over their full actual ordinary function domains.
No Hartree combined bound, special stretched function, optimizer, directional
coercivity or ground-state identity is included in either premise.
-/
noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal
namespace HartreeF.SharpOrdinary
open HeatRiesz ForcingDomain SobolevStretch DirectionalCoercivity

def bilinearRieszPair (α : ℝ) (f g : Space → ℝ) (q : Space × Space) : ℝ :=
  rieszKernel α (standardRieszConstant α) (q.1-q.2) * f q.1 * g q.2

/-- Standard sharp bilinear HLS, including its genuine absolute pair domain.
The actual Riesz kernel has the already justified zero diagonal extension. -/
structure SharpOrdinaryHLS (α : ℝ) : Prop where
  order_pos : 0 < α
  order_lt_three : α < 3
  bound : ∀ (f g : Space → ℝ),
    MemLp f (ENNReal.ofReal (densityExponent α)) volume →
    MemLp g (ENNReal.ofReal (densityExponent α)) volume →
    Integrable (bilinearRieszPair α f g) (volume.prod volume) ∧
    |∫ q, bilinearRieszPair α f g q ∂volume.prod volume| ≤
      sharpHLSConstant α * (eLpNorm f (ENNReal.ofReal (densityExponent α)) volume).toReal *
        (eLpNorm g (ENNReal.ofReal (densityExponent α)) volume).toReal

/-- Standard sharp complex homogeneous Sobolev inequality, in its actual L6
and distributional-gradient domain. The assertion has no chosen datum. -/
structure SharpOrdinarySobolev : Prop where
  bound : ∀ {u : Space → ℂ} {GRe GIm : Space → Space}, InDotH1 u GRe GIm →
    (eLpNorm u 6 volume).toReal ^ 2 ≤ sharpSobolevConstant * kinetic GRe GIm

/-- Native conversion from the squared standard Sobolev inequality to the
ordinary sixth-integral interface used to prove strict directional positivity. -/
theorem SharpOrdinarySobolev.ordinary (hS : SharpOrdinarySobolev) :
    OrdinarySobolev sharpSobolevSixth := by
  refine ⟨sharpSobolevSixth_pos.le, fun hu => ?_⟩
  have hpow := pow_le_pow_left₀ (sq_nonneg ((eLpNorm _ 6 volume).toReal)) (hS.bound hu) 3
  rw [mul_pow, sharpSobolevConstant_cube, ← pow_mul] at hpow
  have he := sixth_norm_pow_eq_integral hu.function_L6
  norm_num only [Real.rpow_ofNat] at he
  norm_num only at hpow
  rwa [he] at hpow

/-- The external sharp HLS is applied only to the actual density. C2 supplies
the exact Lq density domain and its norm, and the physical pair identity is
used to identify the actual interaction integral. -/
theorem sharp_interaction_norm_bound {α : ℝ}
    (hOrd : OrdinaryHLS α (standardRieszConstant α)) (hH : SharpOrdinaryHLS α)
    {u : Space → ℂ} (hu : MemLp u 6 volume) :
    interaction α u ≤ sharpHLSConstant α * (eLpNorm u 6 volume).toReal^(3+α) *
      (eLpNorm u 6 volume).toReal^(3+α) := by
  have hd := powerDensity_memLp hH.order_pos hu
  have hb := (hH.bound (powerDensity α u) (powerDensity α u) hd hd).2
  have he : (∫ q, bilinearRieszPair α (powerDensity α u) (powerDensity α u) q
      ∂volume.prod volume) = interaction α u := by
    unfold interaction
    rw [← PressureDomain.hartree_energy_pair_identity hOrd hu]
    apply integral_congr_ae
    filter_upwards [] with q
    unfold bilinearRieszPair PressureDomain.rieszPairDensity
    ring
  rw [he, powerDensity_eLpNorm hH.order_pos hu.aestronglyMeasurable,
    ← ENNReal.toReal_rpow] at hb
  exact (le_abs_self _).trans hb

#print axioms SharpOrdinarySobolev.ordinary
#print axioms sharp_interaction_norm_bound
end HartreeF.SharpOrdinary
