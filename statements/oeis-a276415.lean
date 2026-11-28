import Mathlib

/-!
# A276415: Number of ways to write n as p + x^3 + y^4, where p is a prime, and x and y are nonnegative integers.

Source: https://oeis.org/A276415
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A276415 (Zhi-Wei Sun, Sep 27 2016), part (i): a(n) > 0
for all n > 1, and a(n) = 1 only for n = 2, 9, 10, 16, 17, 36, 52, 502.

Conventions:
* The sequence has offset 1 (data 0, 1, 3, 3, 2, 2, 2, 2, 1, 1, 3, 3, ...). `a n` is the number of
  triples (p, x, y) of natural numbers with p prime and n = p + x^3 + y^4, exactly as in the OEIS
  name.
* The positivity part is stated for n > 1 and the only-if part for every n >= 1 (the offset).
* Only part (i) of the conjecture is formalized; parts (ii)-(iv) are different statements.
* The set of such tuples is finite for every n, so `Set.ncard` is its number of elements.
* The `a(n) = 1 only for` part is rendered literally as an only-if: a(n) = 1 implies that n is one
  of the listed values.
-/

namespace OMA.S_oeis_a276415

/-- The condition in the name of A276415 on a tuple, for a given n. -/
def P (n : ℕ) (p x y : ℕ) : Prop :=
  p.Prime ∧ p + x ^ 3 + y ^ 4 = n

/-- A276415: the number of representations of n described in the OEIS name. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {t : ℕ × ℕ × ℕ | P n t.1 t.2.1 t.2.2}

/-- The conjecture recorded in A276415. -/
theorem main : ∀ n : ℕ, 0 < n → ((1 < n → 0 < a n) ∧ (a n = 1 →
      n ∈ ({2, 9, 10, 16, 17, 36, 52, 502} : Finset ℕ))) := by
  sorry

end OMA.S_oeis_a276415
