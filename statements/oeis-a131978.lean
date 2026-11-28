import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Order.Lattice.Nat

namespace OMA.S_oeis_a131978

/-- The primorial `n#`: product of all primes `≤ n`. -/
def primorial (n : ℕ) : ℕ :=
  ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, p

/-- `A049614(n) = n! / n#`. -/
def A049614 (n : ℕ) : ℕ :=
  Nat.factorial n / primorial n

/-- `P(n, i) = ∏_{k=1}^n (i^k + k)`. -/
def polyProd (n i : ℕ) : ℕ :=
  ∏ k ∈ Finset.Icc 1 n, (i ^ k + k)

/-- `A131685(n)`: the smallest positive integer `m` such that `n! ∣ m * ∏_{k=1}^n (i^k + k)`
for all `i ≥ 0`. -/
noncomputable def A131685 (n : ℕ) : ℕ :=
  sInf {m : ℕ | 0 < m ∧ ∀ i : ℕ, Nat.factorial n ∣ m * polyProd n i}

/-- Conjecture (OEIS A131978): `A049614(n) / A131685(n)` is always an integer, i.e.,
`A131685(n) ∣ A049614(n)` for all `n ≥ 1`. -/
theorem main : ∀ n : ℕ, 1 ≤ n → A131685 n ∣ A049614 n := by
  sorry

end OMA.S_oeis_a131978
