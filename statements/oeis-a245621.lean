import Mathlib

/-!
# OEIS A245621 — greedy distinct terms with cube averages

Source: https://oeis.org/A245621
Credit: @jacklarmer

The offset is one. Each term is the least unused natural number that makes the
running average a cube, including zero. The permissible set is nonempty since
a sufficiently large cube gives a candidate greater than every earlier term.
-/

namespace OMA.S_oeis_a245621

/-- Choose the next term by expressing the cube-average condition on the sum. -/
noncomputable def nextTerm (previous : List ℕ) : ℕ :=
  sInf {m : ℕ | m ∉ previous ∧ ∃ k : ℕ, previous.sum + m = (previous.length + 1) * k ^ 3}

/-- The first `n` terms in reverse order. -/
noncomputable def history : ℕ → List ℕ
  | 0 => []
  | n + 1 => let previous := history n; nextTerm previous :: previous

/-- The `n`th term for positive `n`. -/
noncomputable def a (n : ℕ) : ℕ := (history n).headD 0

/-- The odd and even formulas and Barker's recurrence, with signed arithmetic. -/
theorem main :
    (∀ n : ℕ, a (2 * n + 1) = n ^ 3) ∧
    (∀ n : ℕ, 0 < n → (a (2 * n) : ℤ) = 7 * (n : ℤ) ^ 3 - 9 * (n : ℤ) ^ 2 + 5 * (n : ℤ) - 1) ∧
    (∀ n : ℕ, 8 < n → (a n : ℤ) =
      4 * (a (n - 2) : ℤ) - 6 * (a (n - 4) : ℤ) + 4 * (a (n - 6) : ℤ) - (a (n - 8) : ℤ)) := by
  sorry

end OMA.S_oeis_a245621
