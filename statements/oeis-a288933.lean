import Mathlib

/-!
# Zero positions in A288932

A288933 records the one-based positions of zeros in A288932. Dekking proved that,
after its leading one, A288932 is the fixed point starting with zero of the morphism
`0 ↦ 0101`, `1 ↦ 1` (A308185). Each iterate is a prefix of the next, and stage `n`
contains `2^n` zeros, so it determines the n-th zero for every positive `n`.

Source: https://oeis.org/A288933
Source: https://oeis.org/A288932/a288932.pdf
Credit: @connoranderson
-/

namespace OMA.S_oeis_a288933

/-- Apply the A308185 morphism to each letter, with `false` representing zero. -/
def expand (w : List Bool) : List Bool :=
  w.flatMap fun b => if b then [true] else [false, true, false, true]

def word : ℕ → List Bool
  | 0 => [false]
  | n + 1 => expand (word n)

/-- The zero-based index of the `(k+1)`-st zero of a word when that zero exists. -/
def zeroAt : List Bool → ℕ → ℕ
  | [], _ => 0
  | true :: w, k => 1 + zeroAt w k
  | false :: _, 0 => 0
  | false :: w, k + 1 => 1 + zeroAt w k

/-- One unit accounts for the leading `1` of A288932 and one for one-based indexing. -/
def a (n : ℕ) : ℕ := 2 + zeroAt (word n) (n-1)

/-- The limit and strict bounds in Kimberling's comment, and Koloskov's binary digit-sum formula. -/
theorem main :
    Filter.Tendsto (fun n : ℕ => (a n : ℝ) / (n : ℝ)) Filter.atTop (nhds 3) ∧
    (∀ n : ℕ, 1 ≤ n → 0 < 3 - (a n : ℝ) / n ∧ 3 - (a n : ℝ) / n < 1) ∧
    (∀ n : ℕ, 1 ≤ n → (a n : ℤ) = 3*(n : ℤ)-1-((Nat.digits 2 (n-1)).sum : ℤ)) := by
  sorry

end OMA.S_oeis_a288933
