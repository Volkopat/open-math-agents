import Mathlib

/-!
# A225389: Prime powers (A025475) representable as (p+q)/2, where p and q are distinct prime powers, in two or more ways.

Source: https://oeis.org/A225389
Credit: @luciusacarr

The entry records one conjecture: the sequence is infinite. Its terms begin 781370209,
59015782001929, ... (the first 12 terms are squares of primes).

Reading of the source:
* "Prime powers" are the terms of A025475, as in the title: `1` and the numbers `p^m` with `p`
  prime and `m ≥ 2` (primes themselves are excluded). The summands `p, q` are read as A025475
  terms too: if primes were allowed, small numbers such as 9 = (7 + 11)/2 = (5 + 13)/2 would be
  terms, contradicting the data. With this reading the least term is 781370209, as listed.
* Following the entry's comment, `n` is a term if there are `x ≠ y`, both positive, such that
  `n + x`, `n - x`, `n + y`, `n - y` are (four distinct) A025475 terms; each `x` gives one way
  `n = ((n - x) + (n + x)) / 2` with distinct summands, and different `x` give different ways.
-/

namespace OMA.S_oeis_a225389

/-- `n` is in A025475: `n = 1` or `n = p^m` with `p` prime and `m ≥ 2`. -/
def IsA025475 (n : ℕ) : Prop := n = 1 ∨ ∃ p m : ℕ, p.Prime ∧ 2 ≤ m ∧ n = p ^ m

/-- `n` is a term of A225389. -/
def IsTerm (n : ℕ) : Prop :=
  IsA025475 n ∧ ∃ x y : ℕ, 0 < x ∧ 0 < y ∧ x ≠ y ∧ x < n ∧ y < n ∧
    IsA025475 (n - x) ∧ IsA025475 (n + x) ∧ IsA025475 (n - y) ∧ IsA025475 (n + y)

theorem main : {n : ℕ | IsTerm n}.Infinite := by
  sorry

end OMA.S_oeis_a225389
