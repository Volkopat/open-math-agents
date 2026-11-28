import Mathlib

/-!
# A236043: Number of triangular numbers <= 10^n.

Source: https://oeis.org/A236043
Credit: @rickmanelius

Comment in the entry (unsigned; the entry is by Derek Orr, Jan 18 2014): Except for 5, all numbers
begin with either a 4 or a 1. If strictly less than, the 5 would become a 4, satisfying this
conjecture.

Robert G. Wilson v, Jan 11 2015: This is not a conjecture, it is a fact and it is the result from
the square root of 2 and 20 times powers of ten.

Formalization notes:
* Triangular numbers are m(m+1)/2 for m ≥ 0, so 0 counts, as in A000217. `triLe N` is the set of
  triangular numbers ≤ N and a(n) is the number of its elements for N = 10^n. The set is finite,
  so `Set.ncard` is its true size (never the junk value 0 of an infinite set). This reproduces the
  27 listed terms 2, 5, 14, 45, 141, ..., 14142135623731 (checked by computer).
* The two comments date from 2014 and 2015, when the data began with a(1) = 5 (offset 1). The
  term a(0) = 2 (the triangular numbers 0 and 1) was added in December 2024 together with the
  present offset 0 (revision 35 of the entry history), so it is outside the scope of the comment,
  which speaks of the terms a(1) = 5, a(2) = 14, a(3) = 45, ...; the statement is for n ≥ 1.
* A number x begins with the digit d when d is its most significant decimal digit, the last
  entry of the little-endian digit list `Nat.digits 10 x` (`beginsWith x d`).
* Except for 5 is read as: every term a(n), n ≥ 1, other than the value 5 begins with 4 or 1.
* If strictly less than: b(n) is the number of triangular numbers < 10^n. The comment says that
  the term 5 = a(1) becomes b(1) = 4 and that then every term b(n), n ≥ 1, begins with 4 or 1.
-/

namespace OMA.S_oeis_a236043

/-- The triangular numbers m(m+1)/2 (m ≥ 0) that are at most N. -/
def triLe (N : ℕ) : Set ℕ := {t | t ≤ N ∧ ∃ m : ℕ, t = m * (m + 1) / 2}

/-- The triangular numbers m(m+1)/2 (m ≥ 0) that are strictly less than N. -/
def triLt (N : ℕ) : Set ℕ := {t | t < N ∧ ∃ m : ℕ, t = m * (m + 1) / 2}

/-- A236043(n): the number of triangular numbers ≤ 10^n. -/
noncomputable def a (n : ℕ) : ℕ := (triLe (10 ^ n)).ncard

/-- The strict variant of the comment: the number of triangular numbers < 10^n. -/
noncomputable def b (n : ℕ) : ℕ := (triLt (10 ^ n)).ncard

/-- x begins with the decimal digit d: d is the most significant digit of x, the last entry of
the little-endian digit list `Nat.digits 10 x`. -/
def beginsWith (x d : ℕ) : Prop := (Nat.digits 10 x).getLast? = some d

/-- The comment: for n ≥ 1 every term a(n) except 5 begins with 4 or 1; with strict inequality
the term 5 = a(1) becomes b(1) = 4, and every b(n), n ≥ 1, begins with 4 or 1. -/
theorem main :
    (∀ n : ℕ, 1 ≤ n → a n ≠ 5 → beginsWith (a n) 4 ∨ beginsWith (a n) 1) ∧
    (a 1 = 5 ∧ b 1 = 4) ∧
    (∀ n : ℕ, 1 ≤ n → beginsWith (b n) 4 ∨ beginsWith (b n) 1) := by
  sorry

end OMA.S_oeis_a236043
