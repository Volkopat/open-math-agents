import Mathlib.Data.Nat.Basic
import Mathlib.Logic.Equiv.Defs

/-!
# Representations by `x*y+x+y`

Alex Ratushnyak defines A253975 at positive indices. Its `n`th term is
the least natural number `k` with exactly `n` representations as `x*y+x+y`
with `x ≥ y > 1`. The value is `-1` if there is no such `k`.
The conjecture that `-1` never occurs is equivalent to existence of a
witness at every positive index, by well-ordering of the natural numbers.

Source: https://oeis.org/A253975. Formalization by @anmolspace.
-/

namespace OMA.S_oeis_a253975

/-- The ordering convention counts each pair of factors only once. -/
def Representations (k : ℕ) :=
  {p : ℕ × ℕ // 1 < p.2 ∧ p.2 ≤ p.1 ∧ p.1 * p.2 + p.1 + p.2 = k}

/-- Each positive `n` occurs as the exact number of representations of some `k`. -/
theorem main : ∀ n : ℕ, 0 < n → ∃ k : ℕ, Nonempty (Fin n ≃ Representations k) := by
  sorry

end OMA.S_oeis_a253975
