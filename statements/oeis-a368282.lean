import Mathlib.Data.Nat.Basic

/-!
# A368282: a Hofstadter-type recurrence as a prefix count

Source: https://oeis.org/A368282 and https://oeis.org/A368281.
Each replacement block has d ones, with a trailing zero exactly for
a source one. The indexed block predicate expresses the fixed point.
The theorem states the OEIS conjecture for every positive divisor d.
-/

namespace OMA.S_oeis_a368282

/-- Count the ones in the first k letters of an infinite binary word. -/
def ones (w : Nat → Bool) : Nat → Nat
  | 0 => 0
  | k+1 => ones w k + (w k).toNat

/-- Starting index of the image of source letter i under
0 ↦ 1^d and 1 ↦ 1^d 0. -/
def offset (w : Nat → Bool) (d i : Nat) : Nat := d*i + ones w i

/-- Exactly the block-by-block assertion that w is fixed by the substitution. -/
def Fixed (w : Nat → Bool) (d : Nat) : Prop :=
  (∀ i j : Nat, j < d → w (offset w d i + j) = true) ∧
  (∀ i : Nat, w i = true → w (offset w d i + d) = false)

theorem main : ∀ (d : Nat), 0 < d → ∀ (w : Nat → Bool), Fixed w d →
    ones w 0 = 0 ∧ ∀ k : Nat, ones w (k+1) = (k+1) - ones w (ones w k / d) := by
  sorry

end OMA.S_oeis_a368282
