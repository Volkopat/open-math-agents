import Mathlib

/-!
# Infinitely many linked runs of three semiprimes

Sources: https://oeis.org/A398403 and https://oeis.org/A179502
(OEIS Foundation, CC BY-SA 4.0).
Formalization: @sturdy4days.

A run begins at n² and includes n² + 1 and n² + 2. For a prime r,
the two linked runs begin at r² and at the square of (r² + 2) / 3.
-/

namespace OMA.S_oeis_a398403

def IsSemiprime (n : ℕ) : Prop :=
  ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ n = p * q

def BeginsSemiprimeRun (n : ℕ) : Prop :=
  IsSemiprime (n ^ 2) ∧ IsSemiprime (n ^ 2 + 1) ∧ IsSemiprime (n ^ 2 + 2)

theorem main : ∀ bound : ℕ, ∃ r s : ℕ,
    bound < r ∧ r.Prime ∧ 3 * s = r ^ 2 + 2 ∧
    BeginsSemiprimeRun r ∧ BeginsSemiprimeRun s := by
  sorry

end OMA.S_oeis_a398403
