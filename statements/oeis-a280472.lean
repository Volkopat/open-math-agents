import Mathlib

/-!
# A280472: Number of ways to write n as the sum of an octagonal number (A000567), a second octagonal number (A045944), and a strict partition number (A000009).

Source: https://oeis.org/A280472
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A280472 (Zhi-Wei Sun, Jan 04 2017), part (i): a(n) > 0
for all n > 0.

Conventions:
* The sequence has offset 1 (data 1, 2, 2, 2, 2, 3, 3, 3, 4, 4, 4, 3, ...). `a n` is the number of
  triples (x, y, v) of natural numbers with v a strict partition number (a value of A000009) and n
  = x*(3x-2) + y*(3y+2) + v, i.e. the number of ways to write n as the sum of an octagonal number
  x*(3x-2) (A000567), a second octagonal number y*(3y+2) (A045944) and a strict partition number,
  as in the OEIS name.
* q(.) is the strict partition function A000009: q(m) is the number of partitions of m into
  distinct parts, the cardinality of the Mathlib finset `Nat.Partition.distincts m` (helper `q`).
* The octagonal numbers are x*(3x-2) and the second octagonal numbers are y*(3y+2) with x, y = 0,
  1, 2, ...; distinct parameters give distinct values. The strict partition numbers repeat (q(0) =
  q(1) = q(2) = 1, q(3) = q(4) = 2), and a way is counted by the value v of the strict partition
  number, not by its index; this is what the Mathematica program in the entry does and it
  reproduces the OEIS data.
* At x = 0 the truncated natural subtraction 3x - 2 is multiplied by 0; for x >= 1 it is exact.
* Only part (i) of the conjecture is formalized; part (ii) is an asymptotic statement.
* The set of such tuples is finite for every n, so `Set.ncard` is its number of elements.
-/

namespace OMA.S_oeis_a280472

/-- q(m), the number of partitions of m into distinct parts (A000009). -/
def q (m : ℕ) : ℕ := (Nat.Partition.distincts m).card

/-- The condition in the name of A280472 on a tuple, for a given n. -/
def P (n : ℕ) (x y v : ℕ) : Prop :=
  (∃ m : ℕ, q m = v) ∧ x * (3 * x - 2) + y * (3 * y + 2) + v = n

/-- A280472: the number of representations of n described in the OEIS name. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {t : ℕ × ℕ × ℕ | P n t.1 t.2.1 t.2.2}

/-- The conjecture recorded in A280472. -/
theorem main : ∀ n : ℕ, 0 < n → 0 < a n := by
  sorry

end OMA.S_oeis_a280472
