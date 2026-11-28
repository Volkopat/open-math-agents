import Mathlib

/-!
# OEIS A330408: the main diagonal of the least-multiple table is A166447

Source: https://oeis.org/A330408 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (Ali Sada, Dec 13 2019), offset 1: Table of A(n,k) read by antidiagonals, where A(1,k)=k;
A(n,k) is the least multiple of n >= A(n-1,k). Comment: The main diagonal is conjectured to be
A166447.
Entry A166447, offset 0: a(n) = n*round(sqrt(n)).

Formalization notes:
* `lm m v` is the least multiple of m that is >= v, computed as m * ceil(v/m); the table is
  A(1,k) = k and A(n,k) = lm n (A(n-1,k)) for n >= 2 (the value at n = 0 only starts the recursion).
* round is Mathlib's `round` (halves rounded up); sqrt(n) is never a half-integer, so the
  convention plays no role.
* The main diagonal is A(n,n), n >= 1, compared with A166447(n) at the same index; the two agree at
  n = 1..6, which are the diagonal terms among the listed antidiagonals.
* Controls: the definitions give A(n,n) = 2, 6, 8, 10, 12 for n = 2..6, A(9,7) = 27 and
  A(4,13) = 16, as in the entry's table.
-/

namespace OMA.S_oeis_a330408

/-- The least multiple of `m` that is `≥ v` (for `m ≥ 1`), as a ceiling division. -/
def lm (m v : ℕ) : ℕ := m * ((v + m - 1) / m)

/-- The table: `A 1 k = k` and `A n k = lm n (A (n-1) k)` for `n ≥ 2` (`A 0 k = k` is unused). -/
def A : ℕ → ℕ → ℕ
  | 0, k => k
  | n + 1, k => lm (n + 1) (A n k)

/-- A166447(n) = n * round(sqrt n). -/
noncomputable def b (n : ℕ) : ℤ := n * round (Real.sqrt n)

/-- Sada's conjecture: the main diagonal A(n,n), n >= 1, is A166447. -/
theorem main : ∀ n : ℕ, 1 ≤ n → (A n n : ℤ) = b n := by
  sorry

end OMA.S_oeis_a330408
