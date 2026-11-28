import Mathlib

/-!
# A349778: Number of ways to write n as x^2 + y^k + 2*z^m, where x,y,z are nonnegative integers with x >= y, and k and m belong to the set {2,3}.

Source: https://oeis.org/A349778
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A349778 (Zhi-Wei Sun, Nov 29 2021), Conjecture 1: a(n)
> 0 for all n >= 0, and a(n) = 1 only for n = 30, 120, 142.

Conventions:
* The sequence has offset 0 (data 4, 4, 8, 4, 8, 4, 4, 4, 4, 6, 8, 4, ...). `a n` is the number of
  quintuples (x, y, z, k, m) with x, y, z natural numbers, x >= y, k and m in the set {2, 3}, and
  n = x^2 + y^k + 2*z^m, exactly as in the OEIS name.
* A way is a choice of (x, y, z, k, m); different exponents count as different ways even when the
  powers coincide, as in the OEIS example a(3) = 4 (3 = 1^2 + 0^2 + 2*1^2 = 1^2 + 0^2 + 2*1^3 =
  1^2 + 0^3 + 2*1^2 = 1^2 + 0^3 + 2*1^3).
* Only Conjecture 1 is formalized; Conjectures 2 and 3 are different statements.
* The set of such tuples is finite for every n, so `Set.ncard` is its number of elements.
* The `a(n) = 1 only for` part is rendered literally as an only-if: a(n) = 1 implies that n is one
  of the listed values.
-/

namespace OMA.S_oeis_a349778

/-- The condition in the name of A349778 on a tuple, for a given n. -/
def P (n : ℕ) (x y z k m : ℕ) : Prop :=
  (k = 2 ∨ k = 3) ∧ (m = 2 ∨ m = 3) ∧ y ≤ x ∧ x ^ 2 + y ^ k + 2 * z ^ m = n

/-- A349778: the number of representations of n described in the OEIS name. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {t : ℕ × ℕ × ℕ × ℕ × ℕ | P n t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2}

/-- The conjecture recorded in A349778. -/
theorem main : ∀ n : ℕ, 0 < a n ∧ (a n = 1 →
      n ∈ ({30, 120, 142} : Finset ℕ)) := by
  sorry

end OMA.S_oeis_a349778
