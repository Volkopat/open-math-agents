import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Topology.MetricSpace.Holder
import Mathlib.Topology.Path

namespace OMA.S_mo_45322

abbrev Hilbert := ↥(lp (fun _ : ℕ => ℝ) 2)

/-- Each pair of points can be joined inside the subgroup by a path
with the prescribed Hölder exponent. -/
def holderConnected (exponent : NNReal) (G : AddSubgroup Hilbert) : Prop :=
  ∀ a ∈ G, ∀ b ∈ G,
    ∃ path : Path a b, (∀ t, path t ∈ G) ∧
      ∃ constant : NNReal, HolderWith constant exponent path

theorem main :
    ∀ α : NNReal, 0 < α → α < 1 / 2 →
      ∃ G : AddSubgroup Hilbert,
        IsClosed (G : Set Hilbert) ∧ holderConnected α G ∧
          ∀ β : NNReal, α < β → ¬ holderConnected β G := by
  sorry

end OMA.S_mo_45322
