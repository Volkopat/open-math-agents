import Mathlib

/-!
# Sets with distinct subset sums

Source: https://www.openproblemgarden.org/op/sets_with_distinct_subset_sums
Credit: @ihateSAS

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.

The source: a set `S` of integers has **distinct subset sums** if distinct subsets of `S` have
distinct sums.  Erdős conjectured that there is a fixed constant `c` with `|S| <= log_2 n + c`
whenever `S` is contained in `1, 2, ..., n` and has distinct subset sums.  Erdős valued this
problem at 500 dollars.

So the proposition formalized below is: there is a real constant `c` such that every finite set of
natural numbers contained in `1, ..., n` with distinct subset sums has at most
`log (n) / log 2 + c` elements.
-/

namespace OMA.S_opg_sets_with_distinct_subset_sums

-- definitions the statement needs (no sorry, no axiom)

/-- `S` has **distinct subset sums**: subsets of `S` with the same sum are equal. -/
def HasDistinctSubsetSums (S : Finset ℕ) : Prop :=
  ∀ A B : Finset ℕ, A ⊆ S → B ⊆ S → A.sum id = B.sum id → A = B

/-- Erdős conjecture on sets with distinct subset sums. -/
theorem main : ∃ c : ℝ, ∀ (n : ℕ) (S : Finset ℕ),
    S ⊆ Finset.Icc 1 n → HasDistinctSubsetSums S →
      (S.card : ℝ) ≤ Real.log (n : ℝ) / Real.log 2 + c := by
  sorry

end OMA.S_opg_sets_with_distinct_subset_sums
