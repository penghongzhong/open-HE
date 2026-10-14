import FScalarFiniteEndpointEstimate

/-! Reverse finite-segment scalar calculus at a finite left endpoint. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
open Set Filter
open scoped Topology
namespace HartreeF.FiniteEndpointCalculus

/-- Apply the mean-value inequality on the original finite segment [b,a],
then send b to the finite left endpoint. This uses no time reflection. -/
theorem abs_le_left_endpoint_of_hasDerivAt_bound
    {S : Set ℝ} (hord : OrdConnected S) {T a D : ℝ}
    (hT : T ∈ closure S) (ha : a ∈ S) (hTa : T < a)
    {q q' : ℝ → ℝ}
    (hd : ∀ t ∈ S, HasDerivAt q (q' t) t)
    (hb : ∀ t ∈ S, t ≤ a → |q' t| ≤ D)
    (hl : Tendsto q (𝓝[S] T) (𝓝 0)) :
    |q a| ≤ D * (a - T) := by
  let : NeBot (𝓝[S] T) := mem_closure_iff_nhdsWithin_neBot.mp hT
  have hId : Tendsto (fun b : ℝ => b) (𝓝[S] T) (𝓝 T) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hleft : Tendsto (fun b => |q a - q b|) (𝓝[S] T) (𝓝 |q a|) := by
    simpa only [sub_zero] using (tendsto_const_nhds.sub hl).abs
  have hright : Tendsto (fun b => D * (a - b)) (𝓝[S] T) (𝓝 (D * (a - T))) :=
    (tendsto_const_nhds.sub hId).const_mul D
  apply le_of_tendsto_of_tendsto hleft hright
  filter_upwards [self_mem_nhdsWithin, hId.eventually (eventually_lt_nhds hTa)]
    with b hbS hba
  have hseg : Icc b a ⊆ S := hord.out hbS ha
  have hm := norm_image_sub_le_of_norm_deriv_le_segment'
    (fun t ht => (hd t (hseg ht)).hasDerivWithinAt)
    (fun t ht => by
      simpa only [Real.norm_eq_abs] using hb t (hseg (Ico_subset_Icc_self ht)) ht.2.le)
    a (show a ∈ Icc b a from ⟨hba.le, le_rfl⟩)
  simpa only [Real.norm_eq_abs] using hm

end HartreeF.FiniteEndpointCalculus
