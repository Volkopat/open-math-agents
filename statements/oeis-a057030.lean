import Mathlib

/-!
# The two limits of successive block reversals

Start with 1, 2, 3, ... . At stage m = 2, 3, ... reverse consecutive
blocks of length m after an initial fixed prefix. For A057030 the prefix
has m-1 entries and for A007062 it has m entries. Positions passed to
the functions below are zero-based, whereas both OEIS sequences start at 1.

After n stages all later prefixes contain position n-1, so its value
already equals the pointwise limit. The conjecture is Mikhail Kurkov's.
Sources: https://oeis.org/A057030 and https://oeis.org/A007062
Formalization: @KoaOkano
-/

namespace OMA.S_oeis_a057030

def sourcePosition (m fixed i : ℕ) : ℕ :=
  if i < fixed then i else
    fixed + m * ((i - fixed) / m) + (m - 1 - (i - fixed) % m)

def afterStages (extra : ℕ) : ℕ → ℕ → ℕ
  | 0, i => i + 1
  | r + 1, i =>
    afterStages extra r (sourcePosition (r + 2) (r + 1 + extra) i)

def term (extra n : ℕ) : ℕ := afterStages extra n (n - 1)

theorem main : ∀ n : ℕ, 0 < n → term 0 n = term 1 (n + 1) - 1 := by
  sorry

end OMA.S_oeis_a057030
