import Mathlib

/-!
# A238165: Number of pairs {j, k} with 0 < j < k <= n such that pi(j*n) divides pi(k*n), where pi(.) is given by A000720.

Source: https://oeis.org/A238165
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A238165 (Zhi-Wei Sun, Feb 19 2014), part (i): a(n) > 0
for all n > 1.

Conventions:
* The sequence has offset 1 (data 0, 1, 1, 2, 3, 2, 1, 5, 5, 5, 3, 5, ...). `a n` is the number of
  pairs (j, k) with 0 < j < k <= n such that pi(j*n) divides pi(k*n), exactly as in the OEIS name.
* pi(x) is `Nat.primeCounting x`, the number of primes not exceeding x.
* An unordered pair {j, k} with j < k is counted once, as the ordered pair (j, k) with j < k.
* Divisibility is `∣` on natural numbers; for n > 1 every pi(j*n) with j >= 1 is positive, so the
  convention about 0 never matters there.
* Only part (i) of the conjecture is formalized; the other parts are different statements.
* The set of such tuples is finite for every n, so `Set.ncard` is its number of elements.
-/

namespace OMA.S_oeis_a238165

/-- The condition in the name of A238165 on a tuple, for a given n. -/
def P (n : ℕ) (j k : ℕ) : Prop :=
  0 < j ∧ j < k ∧ k ≤ n ∧ Nat.primeCounting (j * n) ∣ Nat.primeCounting (k * n)

/-- A238165: the number of representations of n described in the OEIS name. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {t : ℕ × ℕ | P n t.1 t.2}

/-- The conjecture recorded in A238165. -/
theorem main : ∀ n : ℕ, 1 < n → 0 < a n := by
  sorry

end OMA.S_oeis_a238165
