import Mathlib

namespace OMA.S_oeis_a187772

/-- The `n × n` tridiagonal base matrix `T_{2n+1}` from L. E. Jeffery's definition of Danzer
matrices (for odd index `m = 2 * n + 1`): 1 on the superdiagonal, 1 on the subdiagonal,
1 at the bottom-right corner `(n - 1, n - 1)`, and 0 elsewhere. -/
def danzerBase (n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  fun i j =>
    if i.val + 1 = j.val ∨ j.val + 1 = i.val ∨ (i.val + 1 = n ∧ j.val + 1 = n) then 1 else 0

/-- Chebyshev S-polynomial recurrence `S_0(X) = 1`, `S_1(X) = X`,
`S_{r+2}(X) = X * S_{r+1}(X) - S_r(X)` evaluated on an `n × n` integer matrix. -/
def chebSMat {n : ℕ} : ℕ → Matrix (Fin n) (Fin n) ℤ → Matrix (Fin n) (Fin n) ℤ
  | 0, _ => 1
  | 1, X => X
  | r + 2, X => X * chebSMat (r + 1) X - chebSMat r X

/-- The `N`-th Danzer matrix `D_N = S_N(T_{2n+1})` in the `(2n + 1)`-th Danzer basis. -/
def danzerMatrix (n N : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  chebSMat N (danzerBase n)

/-- Reduction of an integer matrix modulo `k`. -/
def matMod {n : ℕ} (k : ℕ) (A : Matrix (Fin n) (Fin n) ℤ) : Matrix (Fin n) (Fin n) (ZMod k) :=
  A.map (Int.castRingHom (ZMod k))

/-- OEIS A220555: maximal multiplicative order of a Danzer matrix from the `(2n + 1)`-th
Danzer basis over `ℤ/kℤ`. -/
noncomputable def a220555 (n k : ℕ) : ℕ :=
  Finset.sup (Finset.univ : Finset (Fin n)) (fun N => orderOf (matMod k (danzerMatrix n N.val)))

/-- OEIS A187772: `T(n, k) = (n - 1) * A220555(n, k)` for `n, k ≥ 2`. -/
noncomputable def a187772 (n k : ℕ) : ℕ :=
  (n - 1) * a220555 n k

/-- OEIS A001175 (Pisano period `π(k)`): the smallest positive integer `p` such that
`Nat.fib (r + p) ≡ Nat.fib r [MOD k]` for all `r : ℕ`. -/
noncomputable def pisanoPeriod (k : ℕ) : ℕ :=
  sInf { p : ℕ | 0 < p ∧ ∀ r : ℕ, Nat.fib (r + p) % k = Nat.fib r % k }

/-- Conjecture in OEIS A187772: `T(2, k) = A001175(k)` (the Pisano period of `k`)
for all `k ≥ 2`. -/
theorem main : ∀ k : ℕ, 2 ≤ k → a187772 2 k = pisanoPeriod k := by sorry

end OMA.S_oeis_a187772
