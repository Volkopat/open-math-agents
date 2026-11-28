import Mathlib

/-!
# A136097: a(n) = A135951(n) /[(2^(n+1)-1) * 2^(n*(n-1)/2)].

Source: https://oeis.org/A136097
Credit: @luciusacarr

A135951 is the sequence of central terms of A135950, the matrix inverse of A022166, the triangle of
Gaussian binomial coefficients [n,k] for q = 2. The entry records one conjecture (formula section):
the n-th central term of the matrix inverse of the triangle of Gaussian binomial coefficients in q
is divisible by [(q^(n+1)-1)/(q-1) * q^(n*(n-1)/2)] for n >= 0 and integer q > 1.

Reading of the source:
* The triangle of Gaussian binomial coefficients in `q` is the infinite lower-triangular matrix
  `T = ([i, j]_q)_{i, j ≥ 0}`. Here `[i, j]_q` is defined by the q-Pascal rule
  `[0, 0] = 1`, `[0, j + 1] = 0`, `[i + 1, 0] = 1`, `[i + 1, j + 1] = [i, j] + q^(j + 1) [i, j + 1]`,
  which gives the usual `[i, j]_q = prod_{t=1..j} (1 - q^(i-j+t)) / (1 - q^t)` (0 for `j > i`),
  the formula used in the entry's PARI program.
* `T` has ones on the diagonal, so it is invertible over the integers, and since it is lower
  triangular, the entries of its inverse in rows and columns `0..m-1` are the entries of the
  inverse of the `m × m` leading block `T_m`. The `n`-th central term of the inverse is its entry
  in row `2n`, column `n` (0-indexed), i.e. the entry `(2n, n)` of `(T_{2n+1})⁻¹` (exactly what
  the PARI program computes, with 1-indexed `A[2*n+1, n+1]`).
* `(q^(n+1) - 1)/(q - 1)` is an exact integer quotient (`= 1 + q + ... + q^n`), and
  `n*(n-1)/2` is also exact.
* The conjecture: for every integer `q > 1` and every `n ≥ 0`, the integer
  `(q^(n+1) - 1)/(q - 1) * q^(n(n-1)/2)` divides the entry `(2n, n)` of `(T_{2n+1})⁻¹`.
-/

namespace OMA.S_oeis_a136097

/-- The Gaussian binomial coefficient `[i, j]_q`, by the q-Pascal rule. -/
def gauss (q : ℤ) : ℕ → ℕ → ℤ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 1
  | i + 1, j + 1 => gauss q i j + q ^ (j + 1) * gauss q i (j + 1)

/-- The `m × m` leading block of the triangle of Gaussian binomial coefficients in `q`. -/
def gaussMatrix (q : ℤ) (m : ℕ) : Matrix (Fin m) (Fin m) ℤ :=
  fun i j => gauss q i j

theorem main :
    ∀ q : ℤ, 1 < q → ∀ n : ℕ,
      (q ^ (n + 1) - 1) / (q - 1) * q ^ (n * (n - 1) / 2) ∣
        (gaussMatrix q (2 * n + 1))⁻¹ ⟨2 * n, by omega⟩ ⟨n, by omega⟩ := by
  sorry

end OMA.S_oeis_a136097
