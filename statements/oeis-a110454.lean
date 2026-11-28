import Mathlib

/-!
# A110454: Largest composite number obtained by concatenation of parts of a distinct partition of n, or 0 if no such number exist.

Source: https://oeis.org/A110454
Credit: @agchua

Comment line of A110454, verbatim:
  Conjecture a(n) = 0 only for n = 1, 2 and 4.
Offset 1, so the statement is for n >= 1.
Definition used below: the candidates are the numbers cat(L), where L is a list of distinct
positive integers with sum n and at least two entries (the parts of a partition of n into at
least two distinct parts, in any order), and cat(L) is the decimal concatenation of the entries
of L from left to right; a(n) is the largest composite candidate (composite: greater than 1 and
not prime), and 0 if there is none (sSup of the empty set of natural numbers is 0).
At least two parts, because the data has a(4) = 0 although 4 itself is composite. (The Maple
program of the entry uses all distinct partitions, one-part ones included, and the test m > 4
and not isprime(m); both readings give the same sequence: the listed data is recomputed by both,
and for n = 3 and n >= 5 the candidate (n-2)*10+2 from the parts n-2, 2 exceeds n.)
-/

namespace OMA.S_oeis_a110454

/-- Decimal concatenation of the entries of a list, from left to right. -/
def cat (L : List ℕ) : ℕ := L.foldl (fun acc x => acc * 10 ^ (Nat.digits 10 x).length + x) 0

/-- The composite numbers obtained by concatenating, in some order, the parts of a partition of
n into at least two distinct parts. -/
def comps (n : ℕ) : Set ℕ :=
  {m | ∃ L : List ℕ, L.Nodup ∧ (∀ x ∈ L, 0 < x) ∧ L.sum = n ∧ 2 ≤ L.length ∧ cat L = m ∧
    1 < m ∧ ¬ m.Prime}

/-- A110454: the largest such composite number, or 0 if there is none. -/
noncomputable def a (n : ℕ) : ℕ := sSup (comps n)

/-- a(n) = 0 only for n = 1, 2 and 4. -/
theorem main : ∀ n : ℕ, 1 ≤ n → (a n = 0 ↔ n = 1 ∨ n = 2 ∨ n = 4) := by
  sorry

end OMA.S_oeis_a110454
