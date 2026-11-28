import Mathlib

/-!
# A023192: Infinitely-recurring prime patterns on 3 consecutive integers

Source: https://oeis.org/A023192
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Conjecture:
There are exactly five prime/composite patterns of length 3 that occur infinitely often on
three consecutive integers `(k, k + 1, k + 2)`, namely `ccc`, `ccp`, `cpc`, `pcc`, and `pcp`.

Conventions:
- `pattern3 k` is the triple `(Nat.Prime k, Nat.Prime (k + 1), Nat.Prime (k + 2))` of booleans
  (with `true` for prime `p` and `false` for nonprime `c`).
- For `k ≥ 4`, nonprime coincides with composite, which does not affect infinitude.
-/

namespace OMA.S_oeis_a023192

noncomputable def pattern3 (k : ℕ) : Bool × Bool × Bool :=
  (decide (Nat.Prime k), decide (Nat.Prime (k + 1)), decide (Nat.Prime (k + 2)))

theorem main :
    {pat : Bool × Bool × Bool | Set.Infinite {k : ℕ | pattern3 k = pat}} =
      {(false, false, false), (false, false, true), (false, true, false),
       (true, false, false), (true, false, true)} := by
  sorry

end OMA.S_oeis_a023192
