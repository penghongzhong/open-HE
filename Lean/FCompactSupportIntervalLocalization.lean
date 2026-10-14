import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.Real.Lemmas

set_option autoImplicit false
set_option warningAsError true
open Set
open scoped Topology
namespace HartreeF.HartreeMildPDEProducer

/-- Every actual compact subset of a nonempty open real interval has a finite
closed interval inside the domain whose STRICT interior contains that subset.
The extra point handles the empty compact set without an unstated nonempty premise. -/
theorem compact_subset_exists_closed_interval
    {S K : Set ℝ} (hS : IsOpen S) (hconn : OrdConnected S)
    (hne : S.Nonempty) (hK : IsCompact K) (hKS : K ⊆ S) :
    ∃ a b : ℝ, a < b ∧ Icc a b ⊆ S ∧ K ⊆ Ioo a b := by
  obtain ⟨s, hs⟩ := hne
  let T : Set ℝ := K ∪ {s}
  have hT : IsCompact T := hK.union isCompact_singleton
  have hsT : s ∈ T := Or.inr (mem_singleton s)
  have hTS : T ⊆ S := union_subset hKS (singleton_subset_iff.mpr hs)
  obtain ⟨m, hm⟩ := hT.exists_isLeast ⟨s, hsT⟩
  obtain ⟨M, hM⟩ := hT.exists_isGreatest ⟨s, hsT⟩
  obtain ⟨l, r, hml, hlr⟩ := mem_nhds_iff_exists_Ioo_subset.mp (hS.mem_nhds (hTS hm.1))
  obtain ⟨l', r', hMr, hlr'⟩ := mem_nhds_iff_exists_Ioo_subset.mp (hS.mem_nhds (hTS hM.1))
  obtain ⟨a, hla, ham⟩ := exists_between hml.1
  obtain ⟨b, hMb, hbr⟩ := exists_between hMr.2
  have ha : a ∈ S := hlr ⟨hla, ham.trans hml.2⟩
  have hb : b ∈ S := hlr' ⟨hMr.1.trans hMb, hbr⟩
  refine ⟨a, b, ham.trans_le (hm.2 hM.1) |>.trans hMb, hconn.out' ha hb, ?_⟩
  intro t ht
  exact ⟨ham.trans_le (hm.2 (Or.inl ht)), (hM.2 (Or.inl ht)).trans_lt hMb⟩

end HartreeF.HartreeMildPDEProducer
