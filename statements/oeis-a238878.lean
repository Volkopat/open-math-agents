import Mathlib

/-!
# A238878: a(n) = |{0 < k <= n: prime(prime(k)) - prime(k) + 1 and prime(prime(k*n)) - prime(k*n) + 1 are both prime}|.

Source: https://oeis.org/A238878
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A238878 (Zhi-Wei Sun, Mar 06 2014), part (i): a(n) > 0
for all n > 0, and a(n) = 1 only for n = 1, 4, 5, 19, 77.

Conventions:
* The sequence has offset 1 (data 1, 2, 3, 1, 1, 4, 3, 2, 5, 5, 3, 4, ...). `a n` is the number of
  integers k with 0 < k <= n such that prime(prime(k)) - prime(k) + 1 and prime(prime(k*n)) -
  prime(k*n) + 1 are both prime, exactly as in the OEIS name.
* prime(k) is the k-th prime with prime(1) = 2; since `Nat.nth Nat.Prime` is 0-indexed (`Nat.nth
  Nat.Prime 0 = 2`), prime(k) is `Nat.nth Nat.Prime (k - 1)` for k >= 1. The helper `pr k` below
  is prime(k).
* The subtractions are exact since prime(j) >= j for j >= 1.
* Only part (i) of the conjecture is formalized; the other parts are different statements.
* The set of such tuples is finite for every n, so `Set.ncard` is its number of elements.
* The `a(n) = 1 only for` part is rendered literally as an only-if: a(n) = 1 implies that n is one
  of the listed values.
-/

namespace OMA.S_oeis_a238878

/-- prime(k), the k-th prime with prime(1) = 2 (for k >= 1). -/
noncomputable def pr (k : ℕ) : ℕ := Nat.nth Nat.Prime (k - 1)

/-- The condition in the name of A238878 on a tuple, for a given n. -/
def P (n : ℕ) (k : ℕ) : Prop :=
  0 < k ∧ k ≤ n ∧ (pr (pr k) - pr k + 1).Prime ∧ (pr (pr (k * n)) - pr (k * n) + 1).Prime

/-- A238878: the number of representations of n described in the OEIS name. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {t : ℕ | P n t}

/-- The conjecture recorded in A238878. -/
theorem main : ∀ n : ℕ, 0 < n → ((0 < n → 0 < a n) ∧ (a n = 1 →
      n ∈ ({1, 4, 5, 19, 77} : Finset ℕ))) := by
  sorry

end OMA.S_oeis_a238878
