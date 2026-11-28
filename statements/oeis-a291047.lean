import Mathlib

/-!
# A291047: Number of ways to write 4*n+1 as p^2 + q^2 + 8*r^2, where p is prime, and q and r are nonnegative integers.

Source: https://oeis.org/A291047
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A291047 (Zhi-Wei Sun, Aug 16 2017), part (i): a(n) > 0
for all n > 0, and the only values of n >= 1000 with a(n) = 1 are 1000, 1052, 1472, 1675, 1967,
4787, 4822, 11962.

Conventions:
* The sequence has offset 1 (data 1, 1, 3, 1, 2, 2, 2, 2, 3, 2, 3, 2, ...). `a n` is the number of
  triples (p, q, r) with p prime, q and r natural numbers and 4*n+1 = p^2 + q^2 + 8*r^2, exactly
  as in the OEIS name.
* `The only values of n >= 1000 with a(n) = 1 are ...` is rendered as an equivalence for n >=
  1000: a(n) = 1 if and only if n is one of the eight listed values (the listed values do satisfy
  a(n) = 1).
* Only part (i) of the conjecture is formalized; the other parts are different statements.
* The set of such tuples is finite for every n, so `Set.ncard` is its number of elements.
-/

namespace OMA.S_oeis_a291047

/-- The condition in the name of A291047 on a tuple, for a given n. -/
def P (n : ℕ) (p q r : ℕ) : Prop :=
  p.Prime ∧ p ^ 2 + q ^ 2 + 8 * r ^ 2 = 4 * n + 1

/-- A291047: the number of representations of n described in the OEIS name. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {t : ℕ × ℕ × ℕ | P n t.1 t.2.1 t.2.2}

/-- The conjecture recorded in A291047. -/
theorem main : (∀ n : ℕ, 0 < n → 0 < a n) ∧
    (∀ n : ℕ, 1000 ≤ n → (a n = 1 ↔
      n ∈ ({1000, 1052, 1472, 1675, 1967, 4787, 4822, 11962} : Finset ℕ))) := by
  sorry

end OMA.S_oeis_a291047
