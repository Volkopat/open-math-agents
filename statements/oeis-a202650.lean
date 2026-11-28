import Mathlib

/-!
# A202650: Number of ways to write n = p + p(k) + p(m) with 0 < k <= m, where p is a prime and p(.) is the partition function (A000041).

Source: https://oeis.org/A202650
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A202650 (Zhi-Wei Sun, Nov 24 2013), part (i): a(n) > 0
for all n > 3.

Conventions:
* The sequence has offset 1 (data 0, 0, 0, 1, 2, 3, 4, 4, 6, 5, 7, 5, ...). `a n` is the number of
  triples (r, k, m) with r a prime, 0 < k <= m and n = r + p(k) + p(m), exactly as in the OEIS
  name (the prime, called p in the OEIS name, is called r here to avoid a clash with the partition
  function p).
* p(.) is the partition function A000041: p(z) is the cardinality of the Mathlib type
  `Nat.Partition z` (helper `p`).
* Only part (i) of the conjecture is formalized; the other parts are different statements.
* The set of such tuples is finite for every n, so `Set.ncard` is its number of elements.
-/

namespace OMA.S_oeis_a202650

/-- p(n), the number of partitions of n. -/
def p (n : ℕ) : ℕ := Fintype.card (Nat.Partition n)

/-- The condition in the name of A202650 on a tuple, for a given n. -/
def P (n : ℕ) (r k m : ℕ) : Prop :=
  r.Prime ∧ 0 < k ∧ k ≤ m ∧ r + p k + p m = n

/-- A202650: the number of representations of n described in the OEIS name. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {t : ℕ × ℕ × ℕ | P n t.1 t.2.1 t.2.2}

/-- The conjecture recorded in A202650. -/
theorem main : ∀ n : ℕ, 3 < n → 0 < a n := by
  sorry

end OMA.S_oeis_a202650
