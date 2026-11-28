import Mathlib

/-!
# A316111: a(n) is the smallest k > 1 such that gcd(k, n^k - n) = 1, for n > 1

Source: https://oeis.org/A316111 (OEIS Foundation, CC BY-SA 4.0).
Credit: @schulzee (agent: Claude Code, model claude-fable-5-2)

Entry A316111 (Thomas Ordowski, Aug 13 2018), offset 2: a(n) is the smallest k > 1 such that
gcd(k, n^k - n) = 1, for n > 1. Data
35, 35, 77, 77, 143, 55, 55, 77, 119, 119, 35, 55, 187, 143, 77, 35, 35, 77, 143, 247, ...
Entry A121707: numbers n > 1 such that n^3 divides Sum_{k=1..n-1} k^n = A121706(n). Data
35, 55, 77, 95, 115, 119, 143, 155, 161, 187, 203, 209, 215, 221, 235, 247, 253, 275, ...

Comments of A316111: Conjecture: all the terms are in A121707. If k is a term, then k is an
"anti-Carmichael number": p-1 does not divide k-1 for every prime p dividing k.

Formalization notes.
* For n > 1, the number k is the term a(n) when k is the least element of the set of all k > 1
  with `Nat.gcd k (n ^ k - n) = 1` (`IsLeast`). The natural subtraction is exact, because
  n ^ k >= n. The statement does not assume that such a k exists for each n.
* A term of A121707 is a natural number k > 1 such that k^3 divides Sum_{j=1..k-1} j^k. The sum is
  over `Finset.Icc 1 (k - 1)`.
* `main` says, for each n > 1 and each term k = a(n): k is a term of A121707, and p - 1 does not
  divide k - 1 for every prime p that divides k.
-/

namespace OMA.S_oeis_a316111

/-- Each term k = a(n) of A316111 is a term of A121707 and is an anti-Carmichael number. -/
theorem main : ∀ n k : ℕ, 1 < n → IsLeast {k : ℕ | 1 < k ∧ Nat.gcd k (n ^ k - n) = 1} k →
    (1 < k ∧ k ^ 3 ∣ ∑ j ∈ Finset.Icc 1 (k - 1), j ^ k) ∧
    ∀ p : ℕ, p.Prime → p ∣ k → ¬ (p - 1 ∣ k - 1) := by
  sorry

end OMA.S_oeis_a316111
