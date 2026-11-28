import Mathlib

/-!
# Tolunsky's recursive sequence and Neretin's run lengths

Sources: https://oeis.org/A359807 and https://oeis.org/A272729.
Both sequences here use index zero for the first displayed term.
Credit: @frido22
-/

namespace OMA.S_oeis_a359807

/-- The term at original index n+1. Its defining maximum ranges over earlier indices.
The supremum of the empty set of naturals gives the prescribed initial zero. -/
def term (n : ℕ) : ℕ :=
  (Finset.univ : Finset (Fin n)).sup fun i =>
    let b := term i + (i : ℕ) + 1
    if b ≤ n then b else 0
termination_by n

/-- Neretin's substitution sends each letter k to k-1 ones followed by k+1. -/
def substLetter (k : ℕ) : List ℕ := List.replicate (k-1) 1 ++ [k+1]

/-- Reading the successive substitution generations from left to right.
After reading a letter, append its image behind the remaining unread letters. -/
def unread : ℕ → List ℕ
  | 0 => [1]
  | n+1 => match unread n with
    | [] => []
    | k :: rest => rest ++ substLetter k

/-- The n-th letter of A272729, starting at zero. -/
def runLength (n : ℕ) : ℕ := (unread n).headD 0

/-- Sum of the first i letters, including the empty sum. -/
def start (i : ℕ) : ℕ := ∑ j ∈ Finset.range i, runLength j

/-- The i-th run has length A272729(i+1), and its value is the sum of the
preceding run lengths. The range consists of exactly these partial sums. -/
theorem main :
    (∀ i : ℕ, 0 < runLength i ∧
      ∀ n : ℕ, term n = start i ↔ start i ≤ n ∧ n < start (i+1)) ∧
    Set.range term = Set.range start := by
  sorry

end OMA.S_oeis_a359807
