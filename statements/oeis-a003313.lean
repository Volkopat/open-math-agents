import Mathlib

/-!
# A003313: Length of shortest addition chain for n.

Source: https://oeis.org/A003313
Credit: @mattdorman

The source states: it is conjectured by D. E. Knuth, K. Stolarsky et al. that for all `n`,
`⌊log₂ n⌋ + ⌈log₂ v(n)⌉ ≤ a(n)`, where `v(n)` (A000120) is the number of `1`s in the binary
expansion of `n` and `a(n)` is the length of a shortest addition chain for `n`.

Reading used here: `n ≥ 1`. An addition chain for `n` of length `r` is a sequence
`c 0 = 1, c 1, …, c r = n` in which every term after the first is the sum of two earlier terms
(possibly the same term twice). Since `a(n)` is the least such `r`, the inequality says every
addition chain for `n` has length at least `⌊log₂ n⌋ + ⌈log₂ v(n)⌉`, and it is stated in that
form; `⌊log₂⌋` and `⌈log₂⌉` are `Nat.log 2` and `Nat.clog 2`.
-/

namespace OMA.S_oeis_a003313

/-- `c 0, …, c r` is an addition chain for `n`. -/
def IsAdditionChain (n r : ℕ) (c : ℕ → ℕ) : Prop :=
  c 0 = 1 ∧ c r = n ∧ ∀ i, 1 ≤ i → i ≤ r → ∃ j < i, ∃ k < i, c i = c j + c k

/-- `v(n)`: the number of `1`s in the binary expansion of `n`. -/
def binaryWeight (n : ℕ) : ℕ := (Nat.digits 2 n).sum

theorem main :
    ∀ n : ℕ, 1 ≤ n → ∀ (r : ℕ) (c : ℕ → ℕ), IsAdditionChain n r c →
      Nat.log 2 n + Nat.clog 2 (binaryWeight n) ≤ r := by
  sorry

end OMA.S_oeis_a003313
