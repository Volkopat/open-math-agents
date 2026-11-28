import Mathlib

/-!
# A271169: Number of ordered ways to write n as s^5 + t^5 + 2*u^5 + 3*v^5 + 4*w^5 + 5*x^5 + 7*y^5 + 14*z^5, where s,t,u,v,w,x,y,z are nonnegative integers with s <= t.

Source: https://oeis.org/A271169
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A271169 (Zhi-Wei Sun, Mar 31 2016): a(n) > 0 for all n
= 0,1,2,..., and a(n) = 1 only for n = 0, 1, 2602.

Conventions:
* The sequence has offset 0 (data 1, 1, 2, 2, 3, 4, 4, 6, 5, 7, 6, 7, ...). `a n` is the number of
  8-tuples (s, t, u, v, w, x, y, z) of natural numbers with s <= t and n = s^5 + t^5 + 2*u^5 +
  3*v^5 + 4*w^5 + 5*x^5 + 7*y^5 + 14*z^5, exactly as in the OEIS name.
* The set of such tuples is finite for every n, so `Set.ncard` is its number of elements.
* The `a(n) = 1 only for` part is rendered literally as an only-if: a(n) = 1 implies that n is one
  of the listed values.
-/

namespace OMA.S_oeis_a271169

/-- The condition in the name of A271169 on a tuple, for a given n. -/
def P (n : ℕ) (s t u v w x y z : ℕ) : Prop :=
  s ≤ t ∧ s ^ 5 + t ^ 5 + 2 * u ^ 5 + 3 * v ^ 5 + 4 * w ^ 5 + 5 * x ^ 5 + 7 * y ^ 5 + 14 * z ^ 5 = n

/-- A271169: the number of representations of n described in the OEIS name. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {t : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ |
    P n t.1 t.2.1 t.2.2.1 t.2.2.2.1
    t.2.2.2.2.1 t.2.2.2.2.2.1 t.2.2.2.2.2.2.1 t.2.2.2.2.2.2.2}

/-- The conjecture recorded in A271169. -/
theorem main : ∀ n : ℕ, 0 < a n ∧ (a n = 1 → n ∈ ({0, 1, 2602} : Finset ℕ)) := by
  sorry

end OMA.S_oeis_a271169
