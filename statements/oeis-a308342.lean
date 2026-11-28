import Mathlib

/-!
# A308342: Number of ways to write 2*n as phi(x^2) + phi(y^2) + phi(z^2), where x,y,z are positive integers with x <= y <= z, and phi(.) is Euler's totient function (A000010).

Source: https://oeis.org/A308342
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A308342 (Zhi-Wei Sun, May 20 2019), Conjecture 1: a(n)
> 0 for all n > 1. In other words, the set {phi(x^2) + phi(y^2) + phi(z^2): x,y,z = 1,2,3,...}
contains all even numbers greater than two.

Conventions:
* The sequence has offset 1 (data 0, 1, 1, 1, 2, 1, 2, 2, 2, 2, 3, 3, ...). `a n` is the number of
  triples (x, y, z) of positive integers with x <= y <= z and 2*n = phi(x^2) + phi(y^2) +
  phi(z^2), exactly as in the OEIS name.
* phi is `Nat.totient`.
* Only Conjecture 1 of the entry is formalized; Conjecture 2 is a different statement.
* The set of such tuples is finite for every n, so `Set.ncard` is its number of elements.
-/

namespace OMA.S_oeis_a308342

/-- The condition in the name of A308342 on a tuple, for a given n. -/
def P (n : ℕ) (x y z : ℕ) : Prop :=
  0 < x ∧ x ≤ y ∧ y ≤ z ∧ Nat.totient (x ^ 2) + Nat.totient (y ^ 2) + Nat.totient (z ^ 2) = 2 * n

/-- A308342: the number of representations of n described in the OEIS name. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {t : ℕ × ℕ × ℕ | P n t.1 t.2.1 t.2.2}

/-- The conjecture recorded in A308342. -/
theorem main : ∀ n : ℕ, 1 < n → 0 < a n := by
  sorry

end OMA.S_oeis_a308342
