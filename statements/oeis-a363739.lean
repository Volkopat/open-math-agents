import Mathlib

/-!
# A363739: lengths of the runs of identical terms of A349509

Source: https://oeis.org/A363739 (OEIS Foundation, CC BY-SA 4.0).
Credit: @schulzee (agent: Claude Code, model claude-fable-5-2)

Entry A363739 (Stefano Spezia, Jun 19 2023), offset 1: a(n) is the length of the n-th run of
identical terms of A349509. Data 2, 1, 5, 1, 17, 1, 2, 1, 5, 1, 17, 1, 26, 1, 2, 1, 23, 1, ...

Formula section: Conjectures: a(2*n) = 1.
a(2*n+1) = A349929(n) - A349929(n-1) - 1, with A349929(0) = 0.

Related entries.
* A349509 (offset 1): a(n) is the denominator of binomial(n^3 + 6*n^2 - 6*n + 2, n^3 - 1)/n^3.
  Data 1, 1, 3, 1, 1, 1, 1, 1, 3, 1, ...
* A349929 (offset 1): numbers k such that A349509(k) = 3. Data 3, 9, 27, 30, 36, 54, 81, ...

Formalization notes.
* `b k` is A349509(k), the denominator of the rational number
  binomial(k^3 + 6 k^2 - 6 k + 2, k^3 - 1) / k^3 (the subtraction of natural numbers is exact
  for k >= 1; the value at k = 0 is not used by the runs, which start at index 1).
* `start n` is the first index of run number n + 1: `start 0 = 1`, and `start (n + 1)` is the
  least index k > start n with b(k) different from b(start n) (`sInf`).
* `a n = start n - start (n - 1)` is the length of the n-th run (n >= 1), that is A363739(n).
* `T n` is A349929(n) with A349929(0) = 0: for n >= 1 it is the n-th index k with b(k) = 3
  (`Nat.nth` counts from 0).
* The second formula has an index shift in the OEIS: as written it gives
  a(3) = A349929(1) - A349929(0) - 1 = 2, but a(3) = 5 = A349929(2) - A349929(1) - 1, and the
  case n = 0 uses A349929(-1). The formula that agrees with the data and with the convention
  A349929(0) = 0 is a(2*n-1) = A349929(n) - A349929(n-1) - 1 for n >= 1 (for example
  a(1) = 3 - 0 - 1 = 2, a(3) = 9 - 3 - 1 = 5, a(5) = 27 - 9 - 1 = 17, a(7) = 30 - 27 - 1 = 2).
  This is the form in `main`.
* `main` is the conjunction of both conjectures for each n >= 1. It implies that A349509 has
  infinitely many runs.
-/

namespace OMA.S_oeis_a363739

/-- A349509: the denominator of binomial(k^3 + 6 k^2 - 6 k + 2, k^3 - 1) / k^3. -/
def b (k : ℕ) : ℕ :=
  ((Nat.choose (k ^ 3 + 6 * k ^ 2 - 6 * k + 2) (k ^ 3 - 1) : ℚ) / (k : ℚ) ^ 3).den

/-- `start n` is the first index of run number `n + 1` of A349509. -/
noncomputable def start : ℕ → ℕ
  | 0 => 1
  | (n + 1) => sInf {k : ℕ | start n < k ∧ b k ≠ b (start n)}

/-- A363739: the length of the n-th run of identical terms of A349509. -/
noncomputable def a (n : ℕ) : ℕ := start n - start (n - 1)

/-- A349929 with the convention A349929(0) = 0. -/
noncomputable def T (n : ℕ) : ℕ :=
  if n = 0 then 0 else Nat.nth (fun k => b k = 3) (n - 1)

/-- Conjectures of Spezia: a(2n) = 1 and a(2n-1) = A349929(n) - A349929(n-1) - 1 for n >= 1. -/
theorem main : ∀ n : ℕ, 1 ≤ n → a (2 * n) = 1 ∧ a (2 * n - 1) = T n - T (n - 1) - 1 := by
  sorry

end OMA.S_oeis_a363739
