import Mathlib

/-!
# A182508: a(0)=0, a(1)=1, a(n) = (a(n-2)+a(n-1)+n) AND n.

Source: https://oeis.org/A182508
Credit: @rickmanelius

Conjecture: sequence contains infinitely many zeros and ones, but no terms of the form 2^k-1,
k>1. (David Radcliffe, Jun 05 2025: This conjecture is true. In fact, the sequence contains no
terms of the form 4*k+3.)

Formalization notes:
* Offset 0, with `a 0 = 0`, `a 1 = 1` and `a (n + 2) = (a n + a (n + 1) + (n + 2)) &&& (n + 2)`,
  where `&&&` is bitwise AND on natural numbers (`Nat.land`), the AND of the entry. The data
  begin 0, 1, 2, 2, 0, 5, 2, 6, 0, 9, 2, 2, 0, 13, 10, 6, ..., matching the entry.
* Infinitely many zeros and ones is read as two claims: infinitely many indices n with
  a(n) = 0, and infinitely many indices n with a(n) = 1.
* No terms of the form 2^k-1, k>1: a(n) ≠ 2^k - 1 for every index n and every k ≥ 2. Since
  2^k ≥ 1, the natural-number subtraction 2^k - 1 is the usual one.
* The stronger remark about terms of the form 4*k+3 is not part of the conjecture and is not
  stated.
-/

namespace OMA.S_oeis_a182508

/-- a(0) = 0, a(1) = 1, a(n) = (a(n-2) + a(n-1) + n) AND n for n ≥ 2. -/
def a : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | (n + 2) => (a n + a (n + 1) + (n + 2)) &&& (n + 2)

theorem main :
    {n : ℕ | a n = 0}.Infinite ∧ {n : ℕ | a n = 1}.Infinite ∧
      ∀ n k : ℕ, 1 < k → a n ≠ 2 ^ k - 1 := by
  sorry

end OMA.S_oeis_a182508
