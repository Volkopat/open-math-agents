import Mathlib

/-!
# A026488: Least positive integer > a(n-1) not of the form a(i)*a(j) - a(k)

Source: https://oeis.org/A026488
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Conjecture:
Define a(1) = 1, and for n >= 2 let a(n) be the least positive integer > a(n-1) that is not
equal to a(i) * a(j) - a(k) for any 1 <= i <= j <= k <= n.
Then a is the increasing sequence of positive integers congruent to 1 (mod 3), with 3 inserted:
a(1) = 1, a(2) = 3, and a(n) = 3 * n - 5 for all n >= 3.
-/

namespace OMA.S_oeis_a026488

/-- Characterization of A026488 on indices n >= 1. -/
def IsA026488 (a : ℕ → ℕ) : Prop :=
  a 1 = 1 ∧
  ∀ n : ℕ, 1 ≤ n →
    a (n + 1) = sInf {x : ℕ | a n < x ∧
      ∀ i j k : ℕ, 1 ≤ i → i ≤ j → j ≤ k → k ≤ n + 1 →
        let v : ℕ → ℕ := fun m => if m = n + 1 then x else a m
        (v i * v j : ℤ) - (v k : ℤ) ≠ (x : ℤ)}

/-- Conjecture: a(2) = 3 and a(n) = 3*n - 5 for all n >= 3. -/
theorem main :
    ∀ a : ℕ → ℕ, IsA026488 a → a 2 = 3 ∧ ∀ n : ℕ, 3 ≤ n → a n = 3 * n - 5 := by
  sorry

end OMA.S_oeis_a026488
