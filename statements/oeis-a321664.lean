import Mathlib.Data.Nat.Basic
import Mathlib.Data.Multiset.Basic

namespace OMA.S_oeis_a321664

/-- Predicate that for 4 natural numbers `(w, x, y, z)`, when sorted into `a ≤ b ≤ c ≤ d`,
the maximum equals the sum of the two smallest terms (`d = a + b`). -/
def FourWindowMaxEqSumTwoMin (w x y z : ℕ) : Prop :=
  ∃ (a b c d : ℕ), a ≤ b ∧ b ≤ c ∧ c ≤ d ∧ d = a + b ∧
    ({w, x, y, z} : Multiset ℕ) = {a, b, c, d}

/-- OEIS A321664 (Padovan 4-window conjecture, formerly in A000931):
Conjecture that every unbounded sequence `a : ℕ → ℕ` of positive integers satisfying
`FourWindowMaxEqSumTwoMin (a n) (a (n+1)) (a (n+2)) (a (n+3))` for all `n` must eventually
satisfy the Padovan recurrence `a (n + 3) = a (n + 1) + a n` (i.e. merge with a multiple
of the Padovan sequence A000931). -/
theorem main :
    ∀ (a : ℕ → ℕ),
      (∀ n, 0 < a n) →
      (∀ M, ∃ n, M < a n) →
      (∀ n, FourWindowMaxEqSumTwoMin (a n) (a (n + 1)) (a (n + 2)) (a (n + 3))) →
      ∃ N, ∀ n ≥ N, a (n + 3) = a (n + 1) + a n := by
  sorry

end OMA.S_oeis_a321664
