import Mathlib

/-!
# A089587: Smallest k in (0, n) maximizing descents of k^m mod n

Source: https://oeis.org/A089587
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

a(n) is the smallest integer k, 0 < k < n, that most often satisfies the
condition k^m > k^(m+1) (modulo n) as m varies from 1 to n - 1.
Conjectures:
1. a(n) = 2 iff n is a Fermat number 2^(2^j) + 1 (for n >= 2).
2. a(2^n - 1) = 2^(n - 1) for n >= 2.
3. a(4^n - 2) = 4^(n - 1) for n >= 1.
-/

namespace OMA.S_oeis_a089587

/-- Number of m in {1, ..., n - 1} such that (k^m mod n) > (k^(m+1) mod n). -/
def descCount (n k : ℕ) : ℕ :=
  ((Finset.Icc 1 (n - 1)).filter (fun m => k ^ (m + 1) % n < k ^ m % n)).card

/-- a(n) = smallest k with 0 < k < n maximizing descCount n k. -/
noncomputable def a (n : ℕ) : ℕ :=
  sInf {k : ℕ | 0 < k ∧ k < n ∧ ∀ j : ℕ, 0 < j → j < n → descCount n j ≤ descCount n k}

theorem main :
    (∀ n : ℕ, 2 ≤ n → (a n = 2 ↔ ∃ j : ℕ, n = 2 ^ (2 ^ j) + 1)) ∧
    (∀ n : ℕ, 2 ≤ n → a (2 ^ n - 1) = 2 ^ (n - 1)) ∧
    (∀ n : ℕ, 1 ≤ n → a (4 ^ n - 2) = 4 ^ (n - 1)) := by
  sorry

end OMA.S_oeis_a089587
