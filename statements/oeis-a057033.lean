import Mathlib

/-!
# The limits of successive cyclic block permutations

A057033 and A057063 start with 1, 2, 3, ... . At each stage m ≥ 2, rotate
every block of length m one place to the left past a fixed prefix. The
entries describe this as reverse-cyclic permutation; the stage examples
and the RotateLeft program specify its direction. A057033 fixes m−1
entries and A057063 fixes m. Block positions below are zero-based.

For an OEIS index n ≥ 1, stage count n suffices because all subsequent
prefixes already contain position n−1. Mikhail Kurkov conjectured the
one-index relation between the two limits.
Sources: https://oeis.org/A057033 and https://oeis.org/A057063
Formalization: @KoaOkano
-/

namespace OMA.S_oeis_a057033

def sourcePosition (m fixed i : ℕ) : ℕ :=
  if i < fixed then i else
    fixed + m * ((i - fixed) / m) + ((i - fixed) % m + 1) % m

def afterStages (extra : ℕ) : ℕ → ℕ → ℕ
  | 0, i => i + 1
  | r + 1, i => afterStages extra r (sourcePosition (r + 2) (r + 1 + extra) i)

def term (extra n : ℕ) : ℕ := afterStages extra n (n - 1)

theorem main : ∀ n : ℕ, 0 < n → term 0 n = term 1 (n + 1) - 1 := by
  sorry

end OMA.S_oeis_a057033
