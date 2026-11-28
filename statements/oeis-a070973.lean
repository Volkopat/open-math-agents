import Mathlib

/-!
# A070973: Growth bounds and surjectivity for smallest k with n | floor((3/2)^k)

Source: https://oeis.org/A070973
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Title: A070973: Smallest integer k such that n divides floor((3/2)^k).

Statement:
Conjectures:
(i) log(n) < a(n) < n * log(n)^2 for n > 6.
(ii) The equation a(x) = n always has a solution.

Conventions:
- `floor((3/2)^k)` equals `3^k / 2^k` in `ℕ`.
- For `(ii)`, every `n : ℕ` (with `n >= 1`, and `a(1) = 0`) occurs as `a(x)` for some `x >= 1`.
-/

namespace OMA.S_oeis_a070973

/-- `A070973(n)`: smallest `k` such that `n` divides `floor((3/2)^k) = 3^k / 2^k`. -/
noncomputable def a (n : ℕ) : ℕ :=
  sInf {k : ℕ | n ∣ 3 ^ k / 2 ^ k}

theorem main :
    (∀ n : ℕ, 6 < n →
      Real.log (n : ℝ) < (a n : ℝ) ∧ (a n : ℝ) < (n : ℝ) * (Real.log (n : ℝ)) ^ 2) ∧
    (∀ n : ℕ, ∃ x : ℕ, 1 ≤ x ∧ a x = n) := by
  sorry

end OMA.S_oeis_a070973
