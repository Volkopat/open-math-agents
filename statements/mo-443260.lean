import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Disjoint
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Total orders on subsets

Source: https://mathoverflow.net/questions/443260

The finite representability question: does every total order on the subsets
of a finite set, compatible with the specified comparisons of disjoint unions,
arise from sums of real weights on the elements?

Every finite ground set can be labelled by `Fin n`, and its subsets are
represented by `Finset (Fin n)`. The order `r` is explicit: the disjointness
and union operations retain their usual set-theoretic meanings.
The source's separate request for terminology and its question about infinite
ground sets are not part of this finite representability assertion.
-/

namespace OMA.S_mo_443260

open scoped BigOperators

theorem main : ∀ (n : ℕ) (r : LinearOrder (Finset (Fin n))),
    (∀ A A' B B' : Finset (Fin n),
      r.lt A A' → r.le B B' → Disjoint A B → Disjoint A' B' →
        r.lt (A ∪ B) (A' ∪ B')) →
    ∃ f : Fin n → ℝ, ∀ A B : Finset (Fin n),
      r.lt A B ↔ (∑ i ∈ A, f i) < ∑ i ∈ B, f i := by
  sorry

end OMA.S_mo_443260
