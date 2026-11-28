import Mathlib

/-!
# A215486: n - 1 mod phi(n), where phi(n) is Euler's totient function.

Source: https://oeis.org/A215486
Credit: @azmiozgen

Conjecture (Lehmer's totient problem, from the entry): a(n) = 0 only when n is 1 or prime.

Formalization notes:
* a(n) = (n - 1) mod phi(n), offset 1.
* Stated as a characterization for every n ≥ 1: a(n) = 0 if and only if n = 1 or n is prime
  (the converse direction holds since phi(p) = p - 1).
* Controls (computed): a(1..33) = 0, 0, 0, 1, 0, 1, 0, 3, 2, 1, 0, 3, 0, 1, 6, 7, 0, 5, 0, 3, 8, 1,
  0, 7, 4, 1, 8, 3, 0, 5, 0, 15, 12, as in the entry; no composite n < 100000 has a(n) = 0.
-/

namespace OMA.S_oeis_a215486

/-- A215486(n) = (n - 1) mod φ(n). -/
def a (n : ℕ) : ℕ := (n - 1) % Nat.totient n

/-- Lehmer's conjecture: `a(n) = 0` only for `n = 1` or `n` prime. -/
theorem main : ∀ n : ℕ, 1 ≤ n → (a n = 0 ↔ n = 1 ∨ n.Prime) := by
  sorry

end OMA.S_oeis_a215486
