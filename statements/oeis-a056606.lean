import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Prime.Basic

namespace OMA.S_oeis_a056606

/-- The squarefree kernel (radical) of a natural number `m`: the product of its distinct
prime factors. -/
def rad (m : ℕ) : ℕ :=
  ∏ p ∈ m.primeFactors, p

/-- `a(n)` (OEIS A056606): the squarefree kernel of `lcm(C(n, 0), ..., C(n, n))`. -/
def a (n : ℕ) : ℕ :=
  rad ((Finset.range (n + 1)).lcm (fun k => Nat.choose n k))

/-- Odd primorials (OEIS A070826): `∏_{p prime, 2 < p ≤ m} p`. -/
def IsOddPrimorial (x : ℕ) : Prop :=
  ∃ m : ℕ, x = ∏ p ∈ (Finset.range (m + 1)).filter (fun p => p.Prime ∧ 2 < p), p

/-- Conjecture (OEIS A056606): every odd term `a(n)` belongs to A070826 (odd primorials). -/
theorem main : ∀ n : ℕ, Odd (a n) → IsOddPrimorial (a n) := by
  sorry

end OMA.S_oeis_a056606
