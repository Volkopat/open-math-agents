import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Ring.Periodic
import Mathlib.Data.Nat.Prime.Defs

/-!
# A340881: pure periodicity modulo primes

Source: https://oeis.org/A340881
Left to Solve: https://lefttosolve.com/p/oeis-a340881
Credit: @houyaji

This states the first conjecture. The positive OEIS index is `m + 1`,
so periodicity on `m : ℕ` starts at the first term.
-/

namespace OMA.S_oeis_a340881

open scoped BigOperators

/-- The finite sum for the OEIS term at positive index `n`. -/
def a (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range n,
    2 ^ (k * (k + 1) / 2) *
      ∏ j ∈ Finset.Ico (k + 1) n, (2 ^ j - 1)

theorem main :
    ∀ p : ℕ, p.Prime →
      ∃ T : ℕ, 0 < T ∧
        Function.Periodic (fun m : ℕ => a (m + 1) % p) T ∧
        (∀ U : ℕ, 0 < U →
          Function.Periodic (fun m : ℕ => a (m + 1) % p) U → T ≤ U) ∧
        T ∣ 2 * (p - 1) := by
  sorry

end OMA.S_oeis_a340881
