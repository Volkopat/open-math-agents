import Mathlib

/-!
# A007655: Standard deviation of A007654.

Source: https://oeis.org/A007655
Credit: @luciusacarr

The entry records the following formula lines, labelled as conjectures (Creighton Dement,
Nov 02 2004), where `a = A007655`:
* `4*a(n+1) + A046184(n) = A055793(n+2) + A098301(n+1)`,
* `4*a(n+1) + A098301(n+1) + A055793(n+2) = A046184(n+1)`,
* `(4*a(n+1))^2 = A098301(2n+1)`.

Reading of the source (all offsets are the current OEIS offsets):
* A007654 (offset 1, data 0, 3, 48, 675, ...): numbers `k` such that the standard deviation of
  `1, ..., k` is an integer. The (sample) standard deviation of `1, ..., k` is
  `sqrt(k*(k+1)/12)`, so `k` is a term iff `k*(k+1)/12` is the square of an integer, i.e.
  `12 ∣ k*(k+1)` and `k*(k+1)/12` is a perfect square. `A007654(n)` is the `n`-th such `k`
  (1-indexed), i.e. `Nat.nth _ (n - 1)`.
* A007655 (offset 1, data 0, 1, 14, 195, ...): `a(n) = sqrt(A007654(n)*(A007654(n)+1)/12)`.
* A046184 (offset 1, data 1, 9, 121, ...): indices `m ≥ 1` such that the octagonal number
  `m*(3m-2)` is a perfect square; `A046184(n)` is the `n`-th such index.
* A055793 (offset 1, data 0, 1, 4, 49, ...): numbers `k` such that `k` and `floor(k/3)` are both
  squares; `A055793(n)` is the `n`-th such `k`.
* A098301 (offset 0, data 0, 1, 16, 225, ...): member `r = 16` of the Chebyshev family `S_r` of
  A092184, `S_r(n) = 2*(T(n,(r-2)/2) - 1)/(r-4)`, i.e. `A098301(n) = (T(n,7) - 1)/6` with `T`
  the Chebyshev polynomial of the first kind.
* The three identities are asserted for every `n ≥ 1` (for `n = 0` the term `A046184(0)` does
  not exist). The statement is the conjunction of the three identities, over the integers.
-/

namespace OMA.S_oeis_a007655

/-- `k` is a term of A007654: the standard deviation `sqrt(k*(k+1)/12)` of `1, ..., k` is an
integer. -/
def IsA007654 (k : ℕ) : Prop := 12 ∣ k * (k + 1) ∧ IsSquare (k * (k + 1) / 12)

/-- A007654, 1-indexed. -/
noncomputable def A007654 (n : ℕ) : ℕ := Nat.nth IsA007654 (n - 1)

/-- A007655: the standard deviation of `1, ..., A007654(n)`. -/
noncomputable def A007655 (n : ℕ) : ℕ := Nat.sqrt (A007654 n * (A007654 n + 1) / 12)

/-- `m` is a term of A046184: `m ≥ 1` and the octagonal number `m*(3m-2)` is a square. -/
def IsA046184 (m : ℕ) : Prop := 1 ≤ m ∧ IsSquare (m * (3 * m - 2))

/-- A046184, 1-indexed. -/
noncomputable def A046184 (n : ℕ) : ℕ := Nat.nth IsA046184 (n - 1)

/-- `k` is a term of A055793: `k` and `floor(k/3)` are both squares. -/
def IsA055793 (k : ℕ) : Prop := IsSquare k ∧ IsSquare (k / 3)

/-- A055793, 1-indexed. -/
noncomputable def A055793 (n : ℕ) : ℕ := Nat.nth IsA055793 (n - 1)

/-- A098301 (offset 0): `(T(n,7) - 1)/6`. -/
noncomputable def A098301 (n : ℕ) : ℤ :=
  ((Polynomial.Chebyshev.T ℤ (n : ℤ)).eval 7 - 1) / 6

theorem main :
    ∀ n : ℕ, 1 ≤ n →
      (4 * (A007655 (n + 1) : ℤ) + A046184 n = A055793 (n + 2) + A098301 (n + 1)) ∧
      (4 * (A007655 (n + 1) : ℤ) + A098301 (n + 1) + A055793 (n + 2) = A046184 (n + 1)) ∧
      ((4 * (A007655 (n + 1) : ℤ)) ^ 2 = A098301 (2 * n + 1)) := by
  sorry

end OMA.S_oeis_a007655
