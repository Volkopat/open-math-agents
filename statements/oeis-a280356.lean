import Mathlib

/-!
# A280356: Number of ways to write n as x^4 + y^3 + z^2 + 2^k, where x,y,z are nonnegative integers and k is a positive integer.

Source: https://oeis.org/A280356
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A280356 (Zhi-Wei Sun, Jan 01 2017), part (i): a(n) > 0
for all n > 1, and a(n) = 1 only for n = 2, 23, 1135, 6415, 6471.

Conventions:
* The sequence has offset 1 (data 0, 1, 3, 4, 4, 4, 3, 3, 5, 5, 4, 5, ...). `a n` is the number of
  quadruples (x, y, z, k) of natural numbers with k > 0 and n = x^4 + y^3 + z^2 + 2^k, exactly as
  in the OEIS name.
* The positivity part is stated for n > 1 and the only-if part for every n >= 1 (the offset).
* Only part (i) of the conjecture is formalized; part (ii) concerns other polynomials.
* The set of such tuples is finite for every n, so `Set.ncard` is its number of elements.
* The `a(n) = 1 only for` part is rendered literally as an only-if: a(n) = 1 implies that n is one
  of the listed values.
-/

namespace OMA.S_oeis_a280356

/-- The condition in the name of A280356 on a tuple, for a given n. -/
def P (n : ℕ) (x y z k : ℕ) : Prop :=
  0 < k ∧ x ^ 4 + y ^ 3 + z ^ 2 + 2 ^ k = n

/-- A280356: the number of representations of n described in the OEIS name. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {t : ℕ × ℕ × ℕ × ℕ | P n t.1 t.2.1 t.2.2.1 t.2.2.2}

/-- The conjecture recorded in A280356. -/
theorem main : ∀ n : ℕ, 0 < n → ((1 < n → 0 < a n) ∧ (a n = 1 →
      n ∈ ({2, 23, 1135, 6415, 6471} : Finset ℕ))) := by
  sorry

end OMA.S_oeis_a280356
