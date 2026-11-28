import Mathlib

/-!
# A365771: a(n) = binomial(2n+1, n)/(2n+1) * binomial(3n-1, n)

Source: https://oeis.org/A365771 (OEIS Foundation, CC BY-SA 4.0).
Credit: @schulzee (agent: Claude Code, model claude-fable-5-2)

Entry A365771 (Paul D. Hanna, Oct 10 2023), offset 0:
a(n) = binomial(2*n+1, n)/(2*n+1) * binomial(3*n-1, n) for n >= 0. Data
1, 2, 20, 280, 4620, 84084, 1633632, 33256080, 701149020, 15191562100, ...
Entry A033042: sums of distinct powers of 5 (0, 1, 5, 6, 25, 26, 30, 31, 125, ...).

Comments: Conjectures: given A033042 is the sums of distinct powers of 5, then
(1) a(5*A033042(n)) == 4 (mod 5) for n > 0,
(2) a(5*A033042(n) + 1) == 2 (mod 5) for n > 0,
(3) a(n) == 0 (mod 5) for n > 0 except when n or n-1 equals 5*A033042(k) for some k >= 0.

Formalization notes.
* `a n` is the natural number C(2n+1, n)/(2n+1) * C(3n-1, n); the division is exact (the first
  factor is the Catalan number). For n = 0 the natural subtraction gives C(0, 0) = 1 and
  a(0) = 1, as in the data.
* `IsSumPow5 k` says that k is a sum of distinct powers of 5, that is, a term of A033042:
  k = Sum_{i in S} 5^i for a finite set S of exponents (S empty gives the term 0).
  The terms A033042(n) with n > 0 are the positive terms.
* `main` is the conjunction of the three conjectures.
-/

namespace OMA.S_oeis_a365771

/-- A365771(n) = C(2n+1, n)/(2n+1) * C(3n-1, n). -/
def a (n : ℕ) : ℕ := (2 * n + 1).choose n / (2 * n + 1) * (3 * n - 1).choose n

/-- k is a sum of distinct powers of 5 (a term of A033042). -/
def IsSumPow5 (k : ℕ) : Prop := ∃ S : Finset ℕ, k = ∑ i ∈ S, 5 ^ i

/-- The three conjectures of the entry. -/
theorem main :
    (∀ k : ℕ, 0 < k → IsSumPow5 k → a (5 * k) % 5 = 4) ∧
    (∀ k : ℕ, 0 < k → IsSumPow5 k → a (5 * k + 1) % 5 = 2) ∧
    (∀ n : ℕ, 0 < n → (¬ ∃ k : ℕ, IsSumPow5 k ∧ (n = 5 * k ∨ n - 1 = 5 * k)) → a n % 5 = 0) := by
  sorry

end OMA.S_oeis_a365771
