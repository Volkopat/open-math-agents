import Mathlib

/-!
# Sums of powers of consecutive bases 2, 3, ..., c + 2

Source: https://mathoverflow.net/questions/471586
Asked by MathOverflow user look at me.

The question asks whether every positive integer can eventually be expressed in the form
`a = ∑_{k=0}^{c} (k+2)^{s_k}` with `c ≥ 0` and all exponents `s_k ≥ 1`. The asker found the
eight exceptions `1, 3, 6, 10, 12, 18, 24, 30` and checked that there are no others up to
`400000`.

Translation choices.
* Eventually is read as: all sufficiently large positive integers have such a
  representation, i.e. there is a bound `N` such that every `a ≥ N` can be written in this
  form.
* The exponents are given by a function `s : ℕ → ℕ`, of which only the values `s 0, ..., s c`
  are used, and these are required to be at least `1`.
-/

namespace OMA.S_mo_471586

theorem main :
    ∃ N : ℕ, ∀ a : ℕ, N ≤ a →
      ∃ c : ℕ, ∃ s : ℕ → ℕ, (∀ k ≤ c, 1 ≤ s k) ∧
        a = ∑ k ∈ Finset.range (c + 1), (k + 2) ^ s k := by
  sorry

end OMA.S_mo_471586
