import Mathlib

/-!
# A238766: Number of ordered ways to write n = k + m (k > 0 and m > 0) such that prime(prime(k)) - prime(k) + 1, prime(prime(2*k+1)) - prime(2*k+1) + 1 and prime(prime(m)) - prime(m) + 1 are all prime.

Source: https://oeis.org/A238766
Credit: @eltociear

Let `f(j) = prime(prime(j)) - prime(j) + 1`. `a(n)` (offset 1) counts the ordered ways to write
`n = k + m` with `k, m > 0` such that `f(k)`, `f(2k + 1)` and `f(m)` are all prime. The entry
conjectures (Zhi-Wei Sun):

  a(n) > 0 for all n > 1, and a(n) = 1 only for n = 2, 3, 11, 44, 55, 149, 371.

`main` is the conjunction of the two parts. `prime(k)` is the `k`-th prime, `Nat.nth Nat.Prime (k - 1)`. Since `prime(prime(j)) ≥ prime(j)`, the
subtraction in `f` is exact.
-/

namespace OMA.S_oeis_a238766

/-- `prime n` is the `n`-th prime, 1-indexed (`prime 1 = 2`). -/
noncomputable def prime (n : ℕ) : ℕ := Nat.nth Nat.Prime (n - 1)

/-- `f(j) = prime(prime(j)) - prime(j) + 1`. -/
noncomputable def f (j : ℕ) : ℕ := prime (prime j) - prime j + 1

/-- OEIS A238766: the number of `k ∈ [1, n - 1]` with `f(k)`, `f(2k + 1)`, `f(n - k)` prime. -/
noncomputable def a (n : ℕ) : ℕ :=
  ((Finset.Ioo 0 n).filter (fun k => (f k).Prime ∧ (f (2 * k + 1)).Prime ∧ (f (n - k)).Prime)).card

/-- The conjecture in OEIS A238766. -/
theorem main : (∀ n : ℕ, 1 < n → 0 < a n) ∧
    (∀ n : ℕ, 1 < n → a n = 1 → n ∈ ({2, 3, 11, 44, 55, 149, 371} : Finset ℕ)) := by
  sorry

end OMA.S_oeis_a238766
