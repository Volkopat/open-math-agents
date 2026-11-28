import Mathlib

/-!
# A248006: Least positive integer m such that m + n divides phi(m * n)

Source: https://oeis.org/A248006
Credit: @AkiRA-COM-FP

Formalizes Zhi-Wei Sun's OEIS A248006 conjecture: for every `n > 2`, `a(n)` exists and
satisfies `a(n) <= n`, where `a(n)` is the least positive integer `m` such that `m + n`
divides `phi(m * n)`.
-/

namespace OMA.S_oeis_a248006

/-- The OEIS sequence A248006: least positive integer `m` such that `m + n` divides `phi(m * n)`. -/
noncomputable def a (n : ℕ) : ℕ :=
  sInf {m : ℕ | 0 < m ∧ (m + n) ∣ Nat.totient (m * n)}

/-- For every `n > 2`, `a(n)` exists and `a(n) <= n`. -/
theorem main :
    ∀ n : ℕ, 2 < n →
      ({m : ℕ | 0 < m ∧ (m + n) ∣ Nat.totient (m * n)}.Nonempty ∧ a n ≤ n) := by
  sorry

end OMA.S_oeis_a248006
