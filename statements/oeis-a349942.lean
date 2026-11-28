import Mathlib

/-!
# A349942: Number of ways to write n as a^4 + b^2 + (c^4 + d^2)/25 with a,b,c,d nonnegative integers.

Source: https://oeis.org/A349942
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A349942 (Zhi-Wei Sun, Dec 05 2021): a(n) > 0 for all n
>= 0, and a(n) = 1 only for n = 0, 16^k*m (k = 0,1,2,... and m = 7, 8, 23, 44, 47).

Conventions:
* The sequence has offset 0 (data 1, 4, 6, 4, 3, 5, 4, 1, 1, 4, 8, 7, ...). `a n` is the number of
  quadruples (a, b, c, d) of natural numbers with n = a^4 + b^2 + (c^4 + d^2)/25, exactly as in
  the OEIS name.
* The quotient (c^4 + d^2)/25 is required to be an integer: the divisibility by 25 is a separate
  conjunct, and the natural-number division is then exact.
* The set of such tuples is finite for every n, so `Set.ncard` is its number of elements.
* The `a(n) = 1 only for` part is rendered literally as an only-if: a(n) = 1 implies that n is one
  of the listed values.
-/

namespace OMA.S_oeis_a349942

/-- The condition in the name of A349942 on a tuple, for a given n. -/
def P (n : ℕ) (a b c d : ℕ) : Prop :=
  25 ∣ c ^ 4 + d ^ 2 ∧ a ^ 4 + b ^ 2 + (c ^ 4 + d ^ 2) / 25 = n

/-- A349942: the number of representations of n described in the OEIS name. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {t : ℕ × ℕ × ℕ × ℕ | P n t.1 t.2.1 t.2.2.1 t.2.2.2}

/-- The conjecture recorded in A349942. -/
theorem main : ∀ n : ℕ, 0 < a n ∧ (a n = 1 →
      n = 0 ∨
      (∃ k m : ℕ, m ∈ ({7, 8, 23, 44, 47} : Finset ℕ) ∧ n = 16 ^ k * m)) := by
  sorry

end OMA.S_oeis_a349942
