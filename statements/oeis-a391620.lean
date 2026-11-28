import Mathlib

/-!
# A391620: Number of integer partitions of n > 0 that are not the first sums of any composition
with all parts > 1.

Source: https://oeis.org/A391620
Credit: @esracummings31-blip

Conjecture (Gus Wiseman): these are the integer partitions of n whose least part is < 4.

Conventions.
* The first sums of a nonempty sequence (a, b, c, d, ...) are (a+b, b+c, c+d, ...); for a list
  `c` this is `List.zipWith (· + ·) c c.tail`.
* An integer partition is written as its nonincreasing list of parts (as in the entry's
  example: (5,4) is the first sums of (3,2,2)).
* A composition with all parts > 1 is a nonempty finite sequence of integers each >= 2.
* The conjecture says: for every n >= 1 and every partition y of n, y is NOT the first sums of
  any composition with all parts > 1 if and only if y has a part < 4 (i.e. its least part is
  < 4). Consequently a(n) counts the partitions of n with least part < 4.
-/

namespace OMA.S_oeis_a391620

/-- First sums of a sequence. -/
def firstSums (c : List ℕ) : List ℕ := List.zipWith (· + ·) c c.tail

/-- The parts of a partition in nonincreasing order. -/
def partsDesc {n : ℕ} (y : Nat.Partition n) : List ℕ := y.parts.sort (· ≥ ·)

/-- `y` is the first sums of some composition with all parts > 1. -/
def IsFirstSumsOfBig {n : ℕ} (y : Nat.Partition n) : Prop :=
  ∃ c : List ℕ, c ≠ [] ∧ (∀ x ∈ c, 1 < x) ∧ firstSums c = partsDesc y

theorem main : ∀ n : ℕ, 1 ≤ n → ∀ y : Nat.Partition n,
    ¬ IsFirstSumsOfBig y ↔ ∃ x ∈ y.parts, x < 4 := by
  sorry

end OMA.S_oeis_a391620
