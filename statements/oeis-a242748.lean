import Mathlib

/-!
# A242748: Number of ordered ways to write n = k + m with 0 < k <= m such that k is a primitive root modulo prime(k) and m is a primitive root modulo prime(m).

Source: https://oeis.org/A242748
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A242748 (Zhi-Wei Sun, May 21 2014): a(n) > 0 for all n
> 1.

Conventions:
* The sequence has offset 1 (data 0, 1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 3, ...). `a n` is the number of
  pairs (k, m) with 0 < k <= m, n = k + m, k a primitive root modulo prime(k) and m a primitive
  root modulo prime(m), exactly as in the OEIS name.
* prime(k) is the k-th prime with prime(1) = 2; since `Nat.nth Nat.Prime` is 0-indexed (`Nat.nth
  Nat.Prime 0 = 2`), prime(k) is `Nat.nth Nat.Prime (k - 1)` for k >= 1. The helper `pr k` below
  is prime(k).
* An integer g is a primitive root modulo a prime q when its multiplicative order modulo q equals
  q - 1; this is `orderOf (g : ZMod q) = q - 1` (if q divides g then the residue 0 has `orderOf`
  equal to 0, which is not q - 1). In particular 1 is a primitive root modulo prime(1) = 2, as in
  the OEIS example for a(7).
* The set of such tuples is finite for every n, so `Set.ncard` is its number of elements.
-/

namespace OMA.S_oeis_a242748

/-- prime(k), the k-th prime with prime(1) = 2 (for k >= 1). -/
noncomputable def pr (k : ℕ) : ℕ := Nat.nth Nat.Prime (k - 1)

/-- The condition in the name of A242748 on a tuple, for a given n. -/
def P (n : ℕ) (k m : ℕ) : Prop :=
  0 < k ∧ k ≤ m ∧ k + m = n ∧ orderOf (k : ZMod (pr k)) = pr k - 1 ∧
  orderOf (m : ZMod (pr m)) = pr m - 1

/-- A242748: the number of representations of n described in the OEIS name. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {t : ℕ × ℕ | P n t.1 t.2}

/-- The conjecture recorded in A242748. -/
theorem main : ∀ n : ℕ, 1 < n → 0 < a n := by
  sorry

end OMA.S_oeis_a242748
