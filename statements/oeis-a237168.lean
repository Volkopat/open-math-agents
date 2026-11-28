import Mathlib

/-!
# A237168: Number of ways to write 2*n - 1 = 2*p + q with p, q, phi(p+1) - 1 and phi(p+1) + 1 all prime, where phi(.) is Euler's totient function.

Source: https://oeis.org/A237168
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A237168 (Zhi-Wei Sun, Feb 04 2014), part (i): a(n) > 0
for all n > 12.

Conventions:
* The sequence has offset 1 (data 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, ...). `a n` is the number of
  pairs (p, q) with 2*n - 1 = 2*p + q and p, q, phi(p+1) - 1, phi(p+1) + 1 all prime, exactly as
  in the OEIS name.
* phi is the Euler totient function `Nat.totient`.
* The equation 2*n - 1 = 2*p + q is written without subtraction as 2*p + q + 1 = 2*n. phi(p+1) - 1
  is an exact subtraction since phi(p+1) >= 1.
* Only part (i) of the conjecture is formalized; the other parts are different statements.
* The set of such tuples is finite for every n, so `Set.ncard` is its number of elements.
-/

namespace OMA.S_oeis_a237168

/-- The condition in the name of A237168 on a tuple, for a given n. -/
def P (n : ℕ) (p q : ℕ) : Prop :=
  2 * p + q + 1 = 2 * n ∧ p.Prime ∧ q.Prime ∧ (Nat.totient (p + 1) - 1).Prime ∧
  (Nat.totient (p + 1) + 1).Prime

/-- A237168: the number of representations of n described in the OEIS name. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {t : ℕ × ℕ | P n t.1 t.2}

/-- The conjecture recorded in A237168. -/
theorem main : ∀ n : ℕ, 12 < n → 0 < a n := by
  sorry

end OMA.S_oeis_a237168
