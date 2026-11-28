import Mathlib

/-!
# A098301: Member r=16 of the family of Chebyshev sequences S_r(n) defined in A092184.

Source: https://oeis.org/A098301
Credit: @luciusacarr

The entry records the formula line labelled as a conjecture (Creighton Dement, Nov 01 2004):
`4*A007655(n+1) + A046184(n) = A055793(n+2) + a(n+1)`, where `a = A098301`.

Reading of the source (all offsets are the current OEIS offsets):
* A098301 (offset 0, data 0, 1, 16, 225, 3136, ...): the member `r = 16` of the Chebyshev family
  `S_r(n) = 2*(T(n,(r-2)/2) - 1)/(r-4)` of A092184, i.e. `a(n) = (T(n,7) - 1)/6` with `T` the
  Chebyshev polynomial of the first kind (as stated in the entry).
* A007654 (offset 1, data 0, 3, 48, 675, ...): numbers `k` such that the standard deviation
  `sqrt(k*(k+1)/12)` of `1, ..., k` is an integer, i.e. `12 ∣ k*(k+1)` and `k*(k+1)/12` is a
  perfect square; `A007654(n)` is the `n`-th such `k` (1-indexed).
* A007655 (offset 1, data 0, 1, 14, 195, ...): `A007655(n) = sqrt(A007654(n)*(A007654(n)+1)/12)`,
  the standard deviation of A007654.
* A046184 (offset 1, data 1, 9, 121, ...): indices `m ≥ 1` of octagonal numbers `m*(3m-2)` that
  are squares; `A046184(n)` is the `n`-th such index.
* A055793 (offset 1, data 0, 1, 4, 49, ...): numbers `k` such that `k` and `floor(k/3)` are both
  squares; `A055793(n)` is the `n`-th such `k`.
* The identity is asserted for every `n ≥ 1` (`A046184(0)` does not exist), over the integers.
-/

namespace OMA.S_oeis_a098301

/-- A098301 (offset 0): `a(n) = (T(n,7) - 1)/6`. -/
noncomputable def a (n : ℕ) : ℤ :=
  ((Polynomial.Chebyshev.T ℤ (n : ℤ)).eval 7 - 1) / 6

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

theorem main :
    ∀ n : ℕ, 1 ≤ n →
      4 * (A007655 (n + 1) : ℤ) + A046184 n = A055793 (n + 2) + a (n + 1) := by
  sorry

end OMA.S_oeis_a098301
