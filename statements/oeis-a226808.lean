import Mathlib

/-!
# A226808: sums of numbers 2^a + 5^b with no one dividing another

Source: https://oeis.org/A226808

A226808 (offset 1): the numbers of the form `2^j + 5^k`, for `j` and `k ≥ 0`:
2, 3, 5, 6, 7, 9, 13, 17, 21, 26, 27, 29, 33, …

Conjecture (Zhi-Wei Sun, Apr 14 2023): each integer `n > 4` can be written as `a_1 + … + a_k`,
where `a_1, …, a_k` are numbers of the form `2^a + 5^b` (`a, b ≥ 0`) (i.e., terms of the current
sequence) with no one dividing another. The entry notes that this has been verified for
`n = 5..1200`.

Conventions:
- A representation is a nonempty finite set `s` of terms of the sequence with sum `n` such that
  no element of `s` divides a different element of `s`. Since a number divides itself, a
  representation with no summand dividing another cannot repeat a summand, so a `Finset` loses
  nothing; the condition is stated as: `x ∣ y` with `x, y ∈ s` forces `x = y`.
- A single term (for example `5 = 2^2 + 5^0`) is an allowed representation, with `k = 1`.
- Everything is in `ℕ`; the exponents may be `0`.
-/

namespace OMA.S_oeis_a226808

theorem main :
    ∀ n : ℕ, 4 < n →
      ∃ s : Finset ℕ, (∀ x ∈ s, ∃ a b : ℕ, x = 2 ^ a + 5 ^ b) ∧ ∑ x ∈ s, x = n ∧
        ∀ x ∈ s, ∀ y ∈ s, x ∣ y → x = y := by
  sorry

end OMA.S_oeis_a226808
