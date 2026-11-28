import Mathlib

/-!
# A321580: Numbers k such that it is possible to reverse a deck of k cards by a sequence of
perfect Faro shuffles with cut.

Source: https://oeis.org/A321580
Credit: @esracummings31-blip

Conjecture (Jules Beauchamp, Oct 25 2026): a(n) = A014657(n+1) - 1, where A014657 lists the
numbers m that divide 2^k + 1 for some nonnegative k.

Conventions (following the OEIS programs and examples).
* A deck of k cards is a function `d : ℕ → ℕ` read at positions 0, ..., k-1; it starts as
  `fun i => i + 1` (cards 1..k) and the reversed deck has card `k - i` at position i.
* One shuffle puts the cards at (0-based) odd positions first, then those at even positions,
  each in order (Python: `shuffled[1::2] + shuffled[0::2]`): the new card at position i is the old
  card at position 2i+1 when i < k/2 (floor), and at position 2(i - k/2) otherwise.
* "Possible by a sequence of shuffles" means after some number j >= 1 of shuffles.
* Both sequences have offset 1 and are listed in increasing order (`Nat.nth`).
-/

namespace OMA.S_oeis_a321580

/-- One perfect Faro shuffle with cut of a deck of k cards. -/
def shuffle (k : ℕ) (d : ℕ → ℕ) : ℕ → ℕ :=
  fun i => if i < k / 2 then d (2 * i + 1) else d (2 * (i - k / 2))

/-- k is a term of A321580. -/
def InSeq (k : ℕ) : Prop :=
  1 ≤ k ∧ ∃ j : ℕ, 1 ≤ j ∧ ∀ i < k, (shuffle k)^[j] (fun i => i + 1) i = k - i

/-- A321580(n), offset 1. -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth InSeq (n - 1)

/-- m divides 2^k + 1 for some nonnegative k. -/
def DividesTwoPowAddOne (m : ℕ) : Prop := ∃ k : ℕ, m ∣ 2 ^ k + 1

/-- A014657(n), offset 1. -/
noncomputable def A014657 (n : ℕ) : ℕ := Nat.nth DividesTwoPowAddOne (n - 1)

theorem main : ∀ n : ℕ, 1 ≤ n → a n = A014657 (n + 1) - 1 := by
  sorry

end OMA.S_oeis_a321580
