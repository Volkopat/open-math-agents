import Mathlib

/-!
# A121878: a(1)=1. a(n) = the smallest positive integer not occurring earlier in the sequence such that a(n-1)+a(n) is squarefree.

Source: https://oeis.org/A121878
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A121878 (Leroy Quet, Aug 31 2006): the sequence is a
permutation of the natural numbers (conjectured by Derek Orr, Jun 01 2015).

Conventions:
* The sequence has offset 1 (data 1, 2, 3, 4, 6, 5, 8, 7, 10, 9, 12, 11, ...).
* The sequence is determined by a(1) = 1 and the greedy rule: for n >= 2, a(n) is the least
  positive integer m that does not occur among a(1), ..., a(n-1) and such that a(n-1) + m is
  squarefree (Mathlib `Squarefree`). The predicate `IsSeq a` states exactly this for a function a
  on the natural numbers (the value a 0 is unused). Such a sequence exists (there are always
  admissible m) and its values at n >= 1 are uniquely determined, so the statement about every `a`
  with `IsSeq a` is a statement about the OEIS sequence.
* The natural numbers here are the positive integers. The terms are distinct by construction, so
  `permutation of the natural numbers` is the statement that every positive integer occurs as a(n)
  for some n >= 1.
-/

namespace OMA.S_oeis_a121878

/-- `a` is the sequence A121878 (on the indices n >= 1). -/
def IsSeq (a : ℕ → ℕ) : Prop :=
  a 1 = 1 ∧ ∀ n : ℕ, 2 ≤ n →
    IsLeast {m : ℕ | 0 < m ∧ (∀ i : ℕ, 1 ≤ i → i < n → a i ≠ m) ∧ Squarefree (a (n - 1) + m)} (a n)

/-- The conjecture recorded in A121878: every positive integer occurs in the sequence. -/
theorem main : ∀ a : ℕ → ℕ, IsSeq a → ∀ m : ℕ, 0 < m → ∃ n : ℕ, 1 ≤ n ∧ a n = m := by
  sorry

end OMA.S_oeis_a121878
