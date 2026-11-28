import Mathlib

/-!
# A235330: Number of ways to write 2*n = p + q with p, q, prime(p) - p + 1 and prime(q) + q + 1 all prime.

Source: https://oeis.org/A235330
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A235330 (Zhi-Wei Sun, Jan 05 2014), part (i): a(n) > 0
for all n >= 2480.

Conventions:
* The sequence has offset 1 (data 0, 0, 0, 1, 1, 1, 1, 1, 2, 0, 1, 1, ...). `a n` is the number of
  pairs (p, q) with 2*n = p + q and p, q, prime(p) - p + 1, prime(q) + q + 1 all prime, exactly as
  in the OEIS name.
* prime(k) is the k-th prime with prime(1) = 2; since `Nat.nth Nat.Prime` is 0-indexed (`Nat.nth
  Nat.Prime 0 = 2`), prime(k) is `Nat.nth Nat.Prime (k - 1)` for k >= 1. The helper `pr k` below
  is prime(k).
* Since prime(p) > p the subtraction prime(p) - p is exact.
* Only part (i) of the conjecture is formalized; the other parts are different statements.
* The set of such tuples is finite for every n, so `Set.ncard` is its number of elements.
-/

namespace OMA.S_oeis_a235330

/-- prime(k), the k-th prime with prime(1) = 2 (for k >= 1). -/
noncomputable def pr (k : ℕ) : ℕ := Nat.nth Nat.Prime (k - 1)

/-- The condition in the name of A235330 on a tuple, for a given n. -/
def P (n : ℕ) (p q : ℕ) : Prop :=
  p + q = 2 * n ∧ p.Prime ∧ q.Prime ∧ (pr p - p + 1).Prime ∧ (pr q + q + 1).Prime

/-- A235330: the number of representations of n described in the OEIS name. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {t : ℕ × ℕ | P n t.1 t.2}

/-- The conjecture recorded in A235330. -/
theorem main : ∀ n : ℕ, 2480 ≤ n → 0 < a n := by
  sorry

end OMA.S_oeis_a235330
