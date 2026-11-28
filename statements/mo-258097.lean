import Mathlib

/-!
# Harmonic numbers with small fractional part

Source: https://mathoverflow.net/questions/258097/there-exist-infinite-many-n-in-mathbbn-such-that-s-n-s-n-frac1n2
Credit: @shc261392

Question. Let `S_n = 1 + 1/2 + ... + 1/n`. Is the set of natural numbers `n` with
`S_n - ⌊S_n⌋ < 1/n^2` infinite?

Reading used here: the affirmative answer, stated as the set of such `n` being infinite.
-/

namespace OMA.S_mo_258097

theorem main :
    {n : ℕ | 0 < n ∧ Int.fract (∑ i ∈ Finset.Icc 1 n, (1 : ℚ) / i) < 1 / (n : ℚ) ^ 2}.Infinite := by
  sorry

end OMA.S_mo_258097
