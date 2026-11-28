import Mathlib

/-!
# A383250: Nonnegative integers not ending with the digit 1 such that every odd digit except the rightmost is immediately followed by a smaller digit

Source: https://oeis.org/A383250 and https://oeis.org/A342045
Credit: @xor2k

Formalizes the OEIS A383250 conjecture: these are the terms of A342045, sorted.

The statement adapts the accepted statement of the sibling entry A383246 (same pipeline,
round 4) to the rule of A342045.

A342045 (When a digit d is odd, the next digit is < d) starts with a(1) = 0 and is then
extended with the smallest positive integer not yet present that does not lead to a
contradiction, where the rule applies to the digit stream of the whole sequence, including
the boundary between consecutive terms. A term ending in the digit 1 would block the sequence
(the next digit would have to be 0, but no term other than the already used 0 starts with 0),
and a term with an internal violation is impossible. Conversely, after any other admissible
term the sequence can always be continued, for instance by a fresh repdigit 22...2 (it starts
with 2, smaller than every odd digit other than 1, and its even last digit imposes nothing on
the next term). Hence the terms that do not lead to a contradiction are exactly the positive
`admissible` values below that obey the boundary rule `follows`, and `a` is the greedy
sequence with this test.

Conventions: `a` is indexed from zero, with `a 0 = 0` representing the source's first term
a(1) = 0. Digits are `Nat.digits 10` read from most to least significant (the reversed list);
the number 0 has the empty digit list, its last digit is taken to be 0, and it is admissible.
The conjecture says that the range of `a` is precisely the defining set of A383250;
injectivity records that the terms of A342045 are distinct, so that sorting them gives
exactly that set.
-/

namespace OMA.S_oeis_a383250

/-- The digit rule: if the digit `d` is odd, the next digit `e` is smaller than `d`. -/
def digitStep (d e : ℕ) : Prop := d % 2 = 1 → e < d

/-- The defining property of A383250: not ending with the digit 1, and every odd digit except
the rightmost is immediately followed by a smaller digit. -/
def admissible (n : ℕ) : Prop :=
  n % 10 ≠ 1 ∧ ((Nat.digits 10 n).reverse).IsChain digitStep

/-- The leading decimal digit (0 for the number 0). -/
def firstDigit (n : ℕ) : ℕ := (Nat.digits 10 n).reverse.headD 0

/-- The last decimal digit (0 for the number 0). -/
def lastDigit (n : ℕ) : ℕ := (Nat.digits 10 n).headD 0

/-- The digit rule across the boundary between the term `n` and the next term `m`. -/
def follows (n m : ℕ) : Prop := digitStep (lastDigit n) (firstDigit m)

/-- The least positive unused admissible value that may follow `previous`. -/
noncomputable def next (used : Finset ℕ) (previous : ℕ) : ℕ :=
  sInf {m : ℕ | 0 < m ∧ admissible m ∧ m ∉ used ∧ follows previous m}

/-- The set of used terms and the latest term after `n + 1` terms. -/
noncomputable def state : ℕ → Finset ℕ × ℕ
  | 0 => ({0}, 0)
  | n + 1 =>
    let m := next (state n).1 (state n).2
    (insert m (state n).1, m)

/-- A342045, indexed from zero: `a 0 = 0` and each later term is the greedy choice. -/
noncomputable def a (n : ℕ) : ℕ := (state n).2

/-- The terms of A342045 are distinct and, as a set, are exactly the terms of A383250. -/
theorem main : Function.Injective a ∧
    ∀ m : ℕ, (∃ n : ℕ, a n = m) ↔ admissible m := by
  sorry

end OMA.S_oeis_a383250
