import Mathlib

/-!
# A269427: a(1) = 1, a(n) counts m < n for which n == a(m) (mod m).

Source: https://oeis.org/A269427
Credit: @agchua

Comment of A269427 (unsigned; the conjecture, verbatim):
  I conjecture that this sequence is unbounded.
The rest of that comment is the author's numerical evidence (counts of the values among the
first k terms); it ends: Thus the sequence appears to be unbounded.

The sequence has offset 1. In the count, m runs over 1 <= m < n (the value a(0) does not
occur), and n == a(m) (mod m) means n % m = a(m) % m. `IsA269427 a` is the defining recursion;
it determines a(n) for every n >= 1 by strong induction, and the statement also says that a
solution exists, so the claim is not vacuous. Unbounded: for every bound B some term exceeds B.
-/

namespace OMA.S_oeis_a269427

/-- The definition of A269427: a(1) = 1 and, for n >= 2, a(n) is the number of m with
1 <= m < n and n == a(m) (mod m). -/
def IsA269427 (a : ℕ → ℕ) : Prop :=
  a 1 = 1 ∧ ∀ n, 2 ≤ n → a n = ((Finset.Ico 1 n).filter (fun m => n % m = a m % m)).card

/-- The conjecture: the sequence is unbounded. -/
theorem main : (∃ a : ℕ → ℕ, IsA269427 a) ∧
    ∀ a : ℕ → ℕ, IsA269427 a → ∀ B : ℕ, ∃ n, 1 ≤ n ∧ B < a n := by
  sorry

end OMA.S_oeis_a269427
