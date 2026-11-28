import Mathlib

/-!
# A112283: the first occurrence of 1 after the first column of the array A109626

Source: https://oeis.org/A112283
Credit: @avivorly

Definition (A112283, verbatim): Consider the array T(n, m) where the n-th row is the sequence of integer
coefficients of A(x), where 1<=a(n)<=n, such that A(x)^(1/n) consists entirely of integer coefficients and
where m is the (m+1)-th coefficient. This sequence is the first occurrence of 1 after the first column.
Comment (verbatim): The degree >0 of the polynomial above whose coefficient is 1.

Conjecture (in the entry, verbatim): a(n)=n if n is 1, a prime or the square of the odd primes.

Conventions:
- Row `n` of the array (the rows of A109626; the Hanna sequences `H_n` of Heninger, Rains and Sloane,
  On the integrality of n-th roots of generating functions, J. Combin. Theory A 113 (2006), Section 6) is a
  sequence `a : ℕ → ℤ` with `a 0 = 1` (the first column), `1 ≤ a k ≤ n` for every `k ≥ 1`, such that
  `A(x) = ∑ a k * x ^ k` is the `n`-th power of a power series with integer coefficients (`IsRow n a`).
  This is the same as asking that `A(x)^(1/n)`, the `n`-th root with constant term `1`, has integer
  coefficients: if `B ^ n = A` with `B` integral, then `(B 0) ^ n = 1`, so `B 0 = 1` or `B 0 = -1`, and the
  one of `B`, `-B` with constant term `1` is that root (when `B 0 = -1`, `n` is even).
- `T n m` is the coefficient of `x ^ m` (the `(m+1)`-th coefficient), so the first column is `m = 0`.
- For every `n ≥ 1` the row exists and is unique (HRS, Theorem 17: `[x ^ k] B ^ n = n * B k + Φ`, where `Φ`
  depends only on `B 1, ..., B (k-1)`, so exactly one value of `a k` in `[1, n]` keeps the root integral);
  it is the row computed by the Mathematica and Maple programs of A109626 and A112283. `T n` is that row,
  picked by `Classical.choose` (the zero sequence when there is no row, which happens only for `n = 0`).
  The accompanying proof constructs a row for every `n ≥ 1` and proves the claim for every row, so it does
  not depend on which row is picked.
- `A112283 n` is the least `m ≥ 1` with `T n m = 1` (`sInf`, which would be `0` if there were none).
  The entry has offset 1; the conjecture concerns `n ≥ 1` only.
- The square of the odd primes is read as `n = p ^ 2` with `p` a prime, `p ≠ 2`. The claim is the
  implication as printed (if), not its converse (the data already has `a(27) = 27`).
-/

namespace OMA.S_oeis_a112283

/-- `a` is row `n` of the array: `a 0 = 1`, `1 ≤ a k ≤ n` for `k ≥ 1`, and `∑ a k * x ^ k` is the `n`-th
power of a power series with integer coefficients. -/
def IsRow (n : ℕ) (a : ℕ → ℤ) : Prop :=
  a 0 = 1 ∧ (∀ k : ℕ, 1 ≤ k → 1 ≤ a k ∧ a k ≤ n) ∧ ∃ B : PowerSeries ℤ, B ^ n = PowerSeries.mk a

open Classical in
/-- The array `T(n, m)`: `T n` is row `n` (picked by choice; the zero sequence if there is no row). -/
noncomputable def T (n : ℕ) : ℕ → ℤ :=
  if h : ∃ a : ℕ → ℤ, IsRow n a then h.choose else fun _ => 0

/-- `A112283 n`: the least column `m ≥ 1` with `T n m = 1`. -/
noncomputable def A112283 (n : ℕ) : ℕ :=
  sInf {m : ℕ | 1 ≤ m ∧ T n m = 1}

theorem main :
    ∀ n : ℕ, (n = 1 ∨ n.Prime ∨ ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ n = p ^ 2) → A112283 n = n := by
  sorry

end OMA.S_oeis_a112283
