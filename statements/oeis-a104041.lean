import Mathlib

namespace OMA.S_oeis_a104041

/-- Stirling numbers of the second kind `S2(n, k)` (`S2(0, 0) = 1`, `S2(n+1, k+1) = (k+1)*S2(n, k+1) + S2(n, k)`). -/
def stirling2 : ℕ → ℕ → ℤ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 0
  | n + 1, k + 1 => ((k + 1 : ℕ) : ℤ) * stirling2 n (k + 1) + stirling2 n k

/-- Signed Stirling numbers of the first kind `s1(n, k)` (`s1(0, 0) = 1`, `s1(n+1, k+1) = s1(n, k) - n*s1(n, k+1)`). -/
def stirling1 : ℕ → ℕ → ℤ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 0
  | n + 1, k + 1 => stirling1 n k - (n : ℤ) * stirling1 n (k + 1)

/-- Peter Bala's conjectured closed-form triangle (OEIS A104041, May 25 2023):
- Even rows: `T(2n, k) = C(n, k - n) * (-2)^(2n - k)` for `n ≤ k ≤ 2n`, else `0`.
- Odd rows: `T(2n + 1, k) = ∑_{i=0}^n S2(n, i) * s1(i + 2, k + 1 - n)` for `n ≤ k ≤ 2n + 1`, else `0`. -/
def balaT (r k : ℕ) : ℤ :=
  if r % 2 = 0 then
    let n := r / 2
    if n ≤ k ∧ k ≤ 2 * n then
      ((Nat.choose n (k - n) : ℕ) : ℤ) * (-2 : ℤ) ^ (2 * n - k)
    else 0
  else
    let n := r / 2
    if n ≤ k ∧ k ≤ 2 * n + 1 then
      ∑ i ∈ Finset.range (n + 1), stirling2 n i * stirling1 (i + 2) (k + 1 - n)
    else 0

/-- Candidate inverse triangle `U` built from the columns of `|T|` as specified by OEIS A104041:
row `m` of `U = T⁻¹` equals (in reverse) column `m - 1` of `|T|` for `m ≥ 1`, with `U(0, 0) = 1`. -/
def invFromCols (T : ℕ → ℕ → ℤ) (m c : ℕ) : ℤ :=
  if c ≤ m then
    if m = 0 then 1
    else |T (2 * m - 1 - c) (m - 1)|
  else 0

/-- Peter Bala's conjectures (OEIS A104041, May 25 2023):
For ANY unit lower-triangular integer matrix `T` (`T(r, r) = 1`, `T(r, k) = 0` for `k > r`)
whose inverse `T⁻¹` has non-negative entries satisfying the OEIS A104041 column/row duality
`T⁻¹(m, c) = |T(2m - 1 - c, m - 1)|` for `1 ≤ m`, `0 ≤ c ≤ m` and `T(r, k) = 0` for `r > 2k + 1`
(with alternating sign `(-1)^(r - k) * T(r, k) ≥ 0`), `T` is given uniquely by Peter Bala's formulas:
1. `T(2n, k) = C(n, k - n) * (-2)^(2n - k)` for `n ≤ k ≤ 2n` (and `0` for `k < n` or `k > 2n`),
2. `T(2n + 1, k) = ∑_{i=0}^n S2(n, i) * s1(i + 2, k + 1 - n)` for `n ≤ k ≤ 2n + 1` (and `0` otherwise);
and conversely, `balaT` itself is a unit lower-triangular matrix whose exact matrix inverse is
`invFromCols balaT`. -/
theorem main :
    (∀ r : ℕ, balaT r r = 1) ∧
    (∀ n : ℕ, balaT (n + 1) n = -((n + 1 : ℕ) : ℤ)) ∧
    (∀ r k : ℕ, r < k → balaT r k = 0) ∧
    (∀ r k : ℕ, 2 * k + 1 < r → balaT r k = 0) ∧
    (∀ r c : ℕ,
      (∑ m ∈ Finset.range (r + 1), balaT r m * invFromCols balaT m c) = if r = c then 1 else 0) ∧
    (∀ (T : ℕ → ℕ → ℤ),
      (∀ r : ℕ, T r r = 1) →
      (∀ n : ℕ, T (n + 1) n = -((n + 1 : ℕ) : ℤ)) →
      (∀ r k : ℕ, r < k → T r k = 0) →
      (∀ r k : ℕ, 2 * k + 1 < r → T r k = 0) →
      (∀ r k : ℕ, k ≤ r → 0 ≤ (-1 : ℤ) ^ (r - k) * T r k) →
      (∀ r c : ℕ,
        (∑ m ∈ Finset.range (r + 1), T r m * invFromCols T m c) = if r = c then 1 else 0) →
      ∀ r k : ℕ, T r k = balaT r k) := by
  sorry

end OMA.S_oeis_a104041
