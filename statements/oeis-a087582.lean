import Mathlib

/-!
# A087582: Primes such that successive differences are distinct palindromes

Source: https://oeis.org/A087582
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Beginning with 2, greedily choose the smallest prime p > prev such that p - prev
is a base-10 palindrome not already appearing as a previous difference.
Conjecture: The sequence is infinite and every even positive palindrome occurs
as a successive difference.
-/

namespace OMA.S_oeis_a087582

/-- A positive natural number is a base-10 palindrome. -/
def IsPalindrome10 (n : ℕ) : Prop :=
  0 < n ∧ (Nat.digits 10 n).reverse = Nat.digits 10 n

/-- Successive differences of a list of natural numbers. -/
def diffs : List ℕ → List ℕ
  | a :: b :: rest => (b - a) :: diffs (b :: rest)
  | _ => []

/-- The first `m` terms of A087582 (starting at `a(1) = 2`). -/
noncomputable def seqList : ℕ → List ℕ
  | 0 => []
  | 1 => [2]
  | n + 2 =>
      let prev := seqList (n + 1)
      let last := prev.getLastD 2
      let used := diffs prev
      let next := sInf {p : ℕ | last < p ∧ p.Prime ∧ IsPalindrome10 (p - last) ∧ (p - last) ∉ used}
      prev ++ [next]

/-- The `m`-th term `a(m)` of A087582 (1-indexed). -/
noncomputable def a (m : ℕ) : ℕ :=
  (seqList m).getLastD 0

theorem main :
    (∀ m : ℕ, 1 ≤ m →
      ∃ p : ℕ, a m < p ∧ p.Prime ∧ IsPalindrome10 (p - a m) ∧ (p - a m) ∉ diffs (seqList m)) ∧
    (∀ d : ℕ, Even d → IsPalindrome10 d → ∃ m : ℕ, 1 ≤ m ∧ a (m + 1) - a m = d) := by
  sorry

end OMA.S_oeis_a087582
