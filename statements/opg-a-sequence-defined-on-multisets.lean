import Mathlib

/-!
# A sequence defined on multisets

Source: https://www.openproblemgarden.org/op/a_sequence_defined_on_multisets
Credit: @shc261392

Conjecture (Erickson): start from a `2 × n` array of positive integers whose first row consists
of distinct positive integers in increasing order and whose second row consists of any positive
integers. Form a new array whose first row lists, in increasing order, all integers occurring in
the array (in either row), and whose second row lists their multiplicities. Repeating this
process always ends in a loop of 1, 2 or 3 arrays.

Reading used here: an array is encoded by the finitely supported function `f : ℕ →₀ ℕ` sending
each first-row entry `a` to the entry below it (so the support is the first row and every value
is positive). The multiset of all entries of the array is `f.support.val + f.support.val.map f`,
and the next array is the multiplicity function of that multiset. The initial array has positive
first-row entries, i.e. `0 ∉ f.support`; it must be nonempty. Ending in a loop of `1`, `2` or `3`
arrays means that from some point on the sequence is periodic with period `1`, `2` or `3`
(a loop of 1 or 2 arrays is also periodic with period 2 or 3 respectively, so this is the
same as the eventual minimal period being at most 3).
-/

namespace OMA.S_opg_a_sequence_defined_on_multisets

/-- One step of the process: count the multiplicities of all entries of the array. -/
noncomputable def step (f : ℕ →₀ ℕ) : ℕ →₀ ℕ :=
  Multiset.toFinsupp (f.support.val + f.support.val.map f)

theorem main : ∀ f : ℕ →₀ ℕ, f ≠ 0 → 0 ∉ f.support →
    ∃ N : ℕ, ∃ q ∈ ({1, 2, 3} : Finset ℕ), step^[N + q] f = step^[N] f := by
  sorry

end OMA.S_opg_a_sequence_defined_on_multisets
