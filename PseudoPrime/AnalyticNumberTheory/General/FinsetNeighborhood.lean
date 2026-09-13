import Mathlib.Order.Filter.Finite
import Mathlib.Topology.Instances.Complex

/-! A finite set avoids any point outside it on a neighborhood of that point. -/

namespace PseudoPrime.AnalyticNumberTheory.General

theorem eventually_not_mem_finset_nhds_of_not_mem {S : Finset ℂ} {s : ℂ} (hs : s ∉ S) :
    ∀ᶠ z in nhds s, z ∉ S := by
  have hne : ∀ ρ ∈ S, ∀ᶠ z in nhds s, z ≠ ρ := by
    intro ρ hρ
    exact isOpen_compl_singleton.mem_nhds (fun h => hs (h ▸ hρ))
  have hall : ∀ᶠ z in nhds s, ∀ ρ ∈ S, z ≠ ρ := (Filter.eventually_all_finset S).mpr hne
  filter_upwards [hall] with z hz hmem
  exact hz z hmem rfl

end PseudoPrime.AnalyticNumberTheory.General
