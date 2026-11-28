import Mathlib

/-!
# A095231: a(1)=1; a(n)=least positive integer such that the concatenation of all terms, including a(n), is == 1 (mod n).

Source: https://oeis.org/A095231
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- Draft from an earlier generic agent run; audited against the source and checked by this agent.

Conjecture: Every natural number occurs infinitely many times.
-/

namespace OMA.S_oeis_a095231

/-- Decimal concatenation of positive integers `x` and `y`. -/
def concatNat (x y : ℕ) : ℕ :=
  x * 10 ^ (Nat.digits 10 y).length + y

/-- `(a(n), concat(a(1), ..., a(n)))` (1-indexed). -/
noncomputable def state : ℕ → ℕ × ℕ
  | 0 => (0, 0)
  | 1 => (1, 1)
  | n + 2 =>
    let c := (state (n + 1)).2
    let m := sInf {m : ℕ | 1 ≤ m ∧ concatNat c m % (n + 2) = 1}
    (m, concatNat c m)

/-- The `n`-th term of A095231 (1-indexed). -/
noncomputable def a (n : ℕ) : ℕ :=
  (state n).1

theorem main :
    ∀ k : ℕ, 1 ≤ k → {n : ℕ | 1 ≤ n ∧ a n = k}.Infinite := by
  sorry

end OMA.S_oeis_a095231
