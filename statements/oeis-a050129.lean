import Mathlib

/-!
# First occurrence in Kimberling's halving-or-reset sequence

Source: https://oeis.org/A050129 (conjecture by Robert Israel, 2020).
The forward sequence is https://oeis.org/A050128.
Credit: @frido22
-/

namespace OMA.S_oeis_a050129

/-- The latest term and the set of all previous values, including the sentinel zero. -/
structure History where
  last : ℕ
  seen : Finset ℕ

def state : ℕ → History
  | 0 => ⟨0, {0}⟩
  | 1 => ⟨1, {0, 1}⟩
  | t + 2 =>
    let s := state (t + 1)
    let v := if s.last / 2 ∈ s.seen then 2 * (t + 2) else s.last / 2
    ⟨v, insert v s.seen⟩

def value (t : ℕ) : ℕ := (state t).last

/-- The first positive index of `n` lies at one of the six positions. The first
alternative is written without division so it applies only to even `n`. -/
theorem main : ∀ n : ℕ, 1 < n → ∃ k : ℕ,
    0 < k ∧ value k = n ∧ (∀ j, 0 < j → value j = n → k ≤ j) ∧
    (2*k = n ∨ k = n+1 ∨ k = 2*n+2 ∨ k = 2*n+3 ∨ k = 4*n+3 ∨ k = 4*n+5) := by
  sorry

end OMA.S_oeis_a050129
