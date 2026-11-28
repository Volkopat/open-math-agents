import Mathlib

/-!
# A066933: Determinant of n X n matrix whose rows are cyclic permutations of 2..prime(n).

Source: https://oeis.org/A066933
Credit: @maaaakks

Conjecture (Benedict W. J. Irwin, Dec 07 2016):
"a(n) = (-1)^(n+floor(n/2))*Res(f(n), x^n - 1), where Res is the resultant, and
f(n)=Sum_{k=1..n} prime(k)*x^k."
(OEIS later notes: "Irwin's conjecture is true (see Fried link). - Sela Fried, Jan 26 2026".)

## Matrix convention

The sign of the determinant depends on the direction of the cyclic shifts. We follow the
OEIS programs (Maple/PARI: entry `(i, j) ↦ prime(1 + ((i + j - 2) mod n))` for 1-based
`i, j`; Mathematica: row `k` is `RotateLeft[{2, 3, 5, ..., prime(n)}, k]`) and the example
`a(3) = det [(2,3,5), (3,5,2), (5,2,3)] = -70`. With 0-based indices `i j : Fin n` and
`Nat.nth Nat.Prime 0 = 2`, the entry is `Nat.nth Nat.Prime ((i + j) % n)`: row `i` is the
list `2, 3, ..., prime(n)` rotated left by `i`. (Right rotations give the opposite sign
when `n ≡ 3, 0 (mod 4)`.) This reproduces the data `1, 2, -5, -70, 1275, 97748, ...`
for `n = 0..12` (checked numerically). The offset is 0 and `a 0 = 1` (empty determinant),
in agreement with the OEIS entry.

## Resultant convention

`Polynomial.resultant f g` is Mathlib's resultant: the determinant of the Sylvester matrix
with the default size arguments `f.natDegree` and `g.natDegree`; it agrees with the classical
`Res(f, g) = lc(f)^(deg g) * ∏_{f(α)=0} g(α)`. The argument order is that of the conjecture,
`Res(f(n), x^n - 1)` (swapping arguments multiplies by `(-1)^(n*n)`, which matters for odd `n`).
Here `f n = ∑_{k=1}^{n} prime(k) X^k` with `prime(k) = Nat.nth Nat.Prime (k - 1)`.

## Indexing / range

The statement is for all `n : ℕ`, including `n = 0`: then the matrix is empty (det 1),
`f 0 = 0` and `X^0 - 1 = 0`, both of natDegree 0, so the Sylvester matrix is `0 × 0` and the
resultant is `1`; the formula gives `1`, consistent with `a(0) = 1`. Numerically, the
identity holds for `n = 0..12` with exactly these conventions.
-/

namespace OMA.S_oeis_a066933

open Polynomial

/-- `a n`: determinant of the `n × n` matrix whose row `i` is `2, 3, 5, ..., prime(n)`
rotated left by `i`, i.e. entry `(i, j)` is `prime(1 + ((i + j) mod n))` (0-based). -/
noncomputable def a (n : ℕ) : ℤ :=
  (Matrix.of fun i j : Fin n => ((Nat.nth Nat.Prime ((i.val + j.val) % n) : ℕ) : ℤ)).det

/-- `f n = ∑_{k=1}^{n} prime(k) * X^k`, where `prime(k) = Nat.nth Nat.Prime (k - 1)`. -/
noncomputable def f (n : ℕ) : ℤ[X] :=
  ∑ k ∈ Finset.Icc 1 n, C ((Nat.nth Nat.Prime (k - 1) : ℕ) : ℤ) * X ^ k

theorem main : ∀ n : ℕ,
    a n = (-1) ^ (n + n / 2) * Polynomial.resultant (f n) (X ^ n - 1) := by
  sorry

end OMA.S_oeis_a066933
