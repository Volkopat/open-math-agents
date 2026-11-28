import Mathlib

/-!
# A224487: Least integer b > F(n) such that sum_{k=1}^n F(k)*b^{k-1} is prime, where F = A000045.

Source: https://oeis.org/A224487
Credit: @prasledi

Conjecture (Zhi-Wei Sun, in the COMMENTS of A224487): for any n > 1 we have a(n) < F(n+4);
moreover, there are infinitely many integers b > F(n) such that sum_{k=1}^n F(k)*b^{k-1} is
prime.

Formalization notes:
* F is Mathlib's `Nat.fib` (F(0) = 0, F(1) = F(2) = 1), which is A000045.
* `S n b = sum_{k=1}^n F(k) * b^(k-1)`, with b a natural number (b > F(n) >= 1).
* a(n) is the least b > F(n) with S n b prime, so a(n) < F(n+4) says exactly that some b with
  F(n) < b < F(n+4) makes S n b prime. This is stated directly, without the minimum.
* The second part is stated for every n > 1 as well: the set of b > F(n) with S n b prime is
  infinite.
* The definition reproduces the OEIS data a(2..15) = 2, 4, 4, 6, 10, 39, 102, 44, 165, 96, 154,
  446, 406, 714, and a(n) < F(n+4) holds there.
-/

namespace OMA.S_oeis_a224487

/-- `S n b = ∑_{k=1}^n F(k) * b^(k-1)`. -/
def S (n b : ℕ) : ℕ := ∑ k ∈ Finset.Icc 1 n, Nat.fib k * b ^ (k - 1)

/-- Sun's conjecture on A224487 (both parts). -/
theorem main :
    (∀ n : ℕ, 1 < n → ∃ b : ℕ, Nat.fib n < b ∧ b < Nat.fib (n + 4) ∧ (S n b).Prime) ∧
      (∀ n : ℕ, 1 < n → {b : ℕ | Nat.fib n < b ∧ (S n b).Prime}.Infinite) := by
  sorry

end OMA.S_oeis_a224487
