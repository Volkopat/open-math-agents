import Mathlib

/-!
# A349945: Number of ways to write n as a^4 + b^2 + (c^4 + d^2)/5 with a,b,c,d nonnegative integers.

Source: https://oeis.org/A349945
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A349945 (Zhi-Wei Sun, Dec 06 2021), Conjecture 1: a(n)
> 0 for all n >= 0, and a(n) = 1 only for n = 0, 2^(4*k+3) (k = 0,1,2,...).

Conventions:
* The sequence has offset 0 (data 1, 3, 4, 3, 3, 6, 7, 3, 1, 4, 5, 4, ...). `a n` is the number of
  quadruples (a, b, c, d) of natural numbers with n = a^4 + b^2 + (c^4 + d^2)/5, exactly as in the
  OEIS name.
* The quotient (c^4 + d^2)/5 is required to be an integer: the divisibility by 5 is a separate
  conjunct, and the natural-number division is then exact.
* Only Conjecture 1 of the entry is formalized.
* The set of such tuples is finite for every n, so `Set.ncard` is its number of elements.
* The `a(n) = 1 only for` part is rendered literally as an only-if: a(n) = 1 implies that n is one
  of the listed values.
-/

namespace OMA.S_oeis_a349945

/-- The condition in the name of A349945 on a tuple, for a given n. -/
def P (n : ℕ) (a b c d : ℕ) : Prop :=
  5 ∣ c ^ 4 + d ^ 2 ∧ a ^ 4 + b ^ 2 + (c ^ 4 + d ^ 2) / 5 = n

/-- A349945: the number of representations of n described in the OEIS name. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {t : ℕ × ℕ × ℕ × ℕ | P n t.1 t.2.1 t.2.2.1 t.2.2.2}

/-- The conjecture recorded in A349945. -/
theorem main : ∀ n : ℕ, 0 < a n ∧ (a n = 1 → n = 0 ∨ ∃ k : ℕ, n = 2 ^ (4 * k + 3)) := by
  sorry

end OMA.S_oeis_a349945
