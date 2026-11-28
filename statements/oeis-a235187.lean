import Mathlib

/-!
# A235187: Number of ordered ways to write 2*n = p + q with p, q and prime(p) + q - 1 all prime.

Source: https://oeis.org/A235187
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A235187 (Zhi-Wei Sun, Jan 04 2014), part (i): a(n) > 0
for all n > 2.

Conventions:
* The sequence has offset 1 (data 0, 0, 1, 1, 2, 1, 1, 2, 2, 3, 2, 3, ...). `a n` is the number of
  ordered pairs (p, q) of natural numbers with 2*n = p + q and p, q and prime(p) + q - 1 all
  prime, exactly as in the OEIS name.
* prime(k) is the k-th prime with prime(1) = 2; since `Nat.nth Nat.Prime` is 0-indexed (`Nat.nth
  Nat.Prime 0 = 2`), prime(k) is `Nat.nth Nat.Prime (k - 1)` for k >= 1. The helper `pr k` below
  is prime(k).
* The natural-number subtraction of 1 is exact since prime(p) + q >= 1.
* Only part (i) of the conjecture is formalized; part (ii) is a different statement.
* The set of such tuples is finite for every n, so `Set.ncard` is its number of elements.
-/

namespace OMA.S_oeis_a235187

/-- prime(k), the k-th prime with prime(1) = 2 (for k >= 1). -/
noncomputable def pr (k : ℕ) : ℕ := Nat.nth Nat.Prime (k - 1)

/-- The condition in the name of A235187 on a tuple, for a given n. -/
def P (n : ℕ) (p q : ℕ) : Prop :=
  p + q = 2 * n ∧ p.Prime ∧ q.Prime ∧ (pr p + q - 1).Prime

/-- A235187: the number of representations of n described in the OEIS name. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {t : ℕ × ℕ | P n t.1 t.2}

/-- The conjecture recorded in A235187. -/
theorem main : ∀ n : ℕ, 2 < n → 0 < a n := by
  sorry

end OMA.S_oeis_a235187
