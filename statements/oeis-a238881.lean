import Mathlib

/-!
# A238881: Number of odd primes p < 2*n with  prime(n*(p+1)/2) + n*(p+1)/2 prime.

Source: https://oeis.org/A238881
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A238881 (Zhi-Wei Sun, Mar 06 2014), part (i), first
sentence: (i) a(n) > 0 for all n > 5, and a(n) = 1 only for n = 2, 3, 7, 9, 23.

Conventions:
* The sequence has offset 1 (data 0, 1, 1, 0, 0, 2, 1, 3, 1, 2, 2, 5, ...). `a n` is the number of
  odd primes p < 2*n with prime(n*(p+1)/2) + n*(p+1)/2 prime, exactly as in the OEIS name.
* prime(k) is the k-th prime with prime(1) = 2; since `Nat.nth Nat.Prime` is 0-indexed (`Nat.nth
  Nat.Prime 0 = 2`), prime(k) is `Nat.nth Nat.Prime (k - 1)` for k >= 1. The helper `pr k` below
  is prime(k).
* For odd p the natural-number division n*(p+1)/2 is exact.
* Only the first sentence of part (i) is formalized; the `Moreover` sentence of part (i) and part
  (ii) are different statements.
* The set of such tuples is finite for every n, so `Set.ncard` is its number of elements.
* The `a(n) = 1 only for` part is rendered literally as an only-if: a(n) = 1 implies that n is one
  of the listed values.
-/

namespace OMA.S_oeis_a238881

/-- prime(k), the k-th prime with prime(1) = 2 (for k >= 1). -/
noncomputable def pr (k : ℕ) : ℕ := Nat.nth Nat.Prime (k - 1)

/-- The condition in the name of A238881 on a tuple, for a given n. -/
def P (n : ℕ) (p : ℕ) : Prop :=
  p.Prime ∧ Odd p ∧ p < 2 * n ∧ (pr (n * (p + 1) / 2) + n * (p + 1) / 2).Prime

/-- A238881: the number of representations of n described in the OEIS name. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {t : ℕ | P n t}

/-- The conjecture recorded in A238881. -/
theorem main : ∀ n : ℕ, 0 < n → ((5 < n → 0 < a n) ∧ (a n = 1 →
      n ∈ ({2, 3, 7, 9, 23} : Finset ℕ))) := by
  sorry

end OMA.S_oeis_a238881
