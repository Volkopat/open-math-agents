import OMAStatements.S_oeis_a067129
import Mathlib

/-! A067129 split along the parity of `σ(2k)`.

An even term `k` has odd neighbours `k ± 3`. For odd `n`, `σ(n)` is odd exactly when `n` is a
square (pair each divisor `d` with `n / d`), and `σ(2^a u^2)` is odd for odd `u`. So when `k` is
an even square or twice a square (`k ≠ 4`), `σ(2k)` is odd while `k ± 3` are odd non-squares
(residues mod 8) with even `σ`: the equation fails by parity. That is `H1`, a classical parity
argument, not progress on the conjecture.

`H2` is the open rest: even `k` that is neither a square nor twice a square, where both sides
of the equation are even.
-/

namespace OMA.R_oeis_a067129_R1

open OMA.S_oeis_a067129

/-- Even squares and even twice-squares are never terms (parity of `σ`). -/
def H1 : Prop := ∀ k m : ℕ, Even k → (k = m ^ 2 ∨ k = 2 * m ^ 2) → ¬ IsTerm k

/-- The open rest: even `k` that is neither a square nor twice a square. -/
def H2 : Prop := ∀ k : ℕ, Even k → (∀ m : ℕ, k ≠ m ^ 2 ∧ k ≠ 2 * m ^ 2) → ¬ IsTerm k

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a067129.main := by
  intro h1 h2 k hk
  by_contra hodd
  have he : Even k := Nat.not_odd_iff_even.mp hodd
  by_cases hs : ∃ m : ℕ, k = m ^ 2 ∨ k = 2 * m ^ 2
  · obtain ⟨m, hm⟩ := hs
    exact h1 k m he hm hk
  · push_neg at hs
    exact h2 k he hs hk

end OMA.R_oeis_a067129_R1
