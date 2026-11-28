import Mathlib

/-!
# A352082: a(n) = Sum_{k=0..floor(n/2)} (n-2*k)^n.

Source: https://oeis.org/A352082 (OEIS Foundation, CC BY-SA 4.0)
Credit: @bmendonca3

[Lean proof of this statement](https://github.com/bmendonca3/open-math-agents/blob/8a441ac1cf53e0d33983f8d8bc269e5abcf9cf2d/proofs/oeis-a352082.lean)

Conjecture (Velin Yanev, Mar 25 2024, formula section of A352082):
`a(n) = (1 - 2^n)*zeta(-n) - (2^n)*zeta(-n, n/2 + 1)` for `n > 0`, where the bivariate zeta
function is the Hurwitz zeta function.

## Reading of the statement

* `a n` is the sequence itself, `∑_{k=0}^{⌊n/2⌋} (n - 2k)^n`, with offset 0. For every `k` in
  the range we have `2 * k ≤ n`, so the subtraction in `ℕ` never truncates.
* `zeta(-n)` is the Riemann zeta function, Mathlib's `riemannZeta`, at the integer `-n`.
* `zeta(s, q)` is the classical Hurwitz zeta function: for real `q > 0` it is the analytic
  continuation in `s` (to `ℂ` minus the point `1`) of `∑_{j ≥ 0} (j + q)^(-s)`, `1 < re s`.
* `n/2 + 1` is the exact real number `n/2 + 1` (a half-integer when `n` is odd), not a floor.
* The two sides are compared in `ℂ`, where Mathlib's zeta functions take their values.
* The range is `n > 0`, as in the source. (At `n = 0` the right side is `1/2` and `a(0) = 1`.)

## Why the Hurwitz zeta function is defined here

Mathlib's `HurwitzZeta.hurwitzZeta a s` takes `a : UnitAddCircle`. It is periodic in `a`, and it
is the continuation of `∑_{j ≥ 0} (j + a)^(-s)` only for a representative `a ∈ [0, 1]`
(`HurwitzZeta.hasSum_hurwitzZeta_of_one_lt_re`). So it is not `zeta(s, q)` for `q > 1`, and the
second argument `n/2 + 1` of the conjecture is always greater than `1`.

`hurwitzZetaClassical s q` restores the classical function for every real `q > 0`. Put
`M = ⌈q⌉ - 1`, so that `M` is a natural number and `q - M ∈ (0, 1]`. Then

  `zeta(s, q) = zeta(s, q - M) - ∑_{k=1}^{M} (q - k)^(-s)`.

For `1 < re s` this is the series `∑_{j ≥ 0} (j + q - M)^(-s)` with its first `M` terms removed
(the term `j` is `(q - k)^(-s)` with `k = M - j`), which is `∑_{j ≥ 0} (j + q)^(-s)`. The first
term on the right is Mathlib's `hurwitzZeta (q : UnitAddCircle) s`, because `q` and `q - M` are
the same point of the circle and `q - M ∈ (0, 1]`. Every base `q - k` in the finite sum is a
positive real, so each `(q - k)^(-s)` is the principal power and is entire in `s`. Hence the
right side is analytic for `s ≠ 1` and is the analytic continuation: it is the classical
`zeta(s, q)`. For `q ≤ 0` the value has no meaning; the conjecture uses only `q = n/2 + 1 > 1`.
-/

namespace OMA.S_oeis_a352082

/-- OEIS A352082: `a(n) = ∑_{k=0}^{⌊n/2⌋} (n - 2k)^n`. The subtraction never truncates because
`2 * k ≤ n` for every `k ≤ n / 2`. -/
def a (n : ℕ) : ℕ := ∑ k ∈ Finset.range (n / 2 + 1), (n - 2 * k) ^ n

/-- The classical Hurwitz zeta function `ζ(s, q)` for real `q > 0` and `s ≠ 1`: the analytic
continuation in `s` of `∑_{j ≥ 0} (j + q)^(-s)`. With `M = ⌈q⌉ - 1` we have `q - M ∈ (0, 1]` and
`ζ(s, q) = ζ(s, q - M) - ∑_{k=1}^{M} (q - k)^(-s)`, where `ζ(s, q - M)` is Mathlib's periodic
`HurwitzZeta.hurwitzZeta` at the class of `q` in `ℝ / ℤ`. See the file header. -/
noncomputable def hurwitzZetaClassical (s : ℂ) (q : ℝ) : ℂ :=
  HurwitzZeta.hurwitzZeta (q : UnitAddCircle) s
    - ∑ k ∈ Finset.Icc 1 (⌈q⌉₊ - 1), ((q - (k : ℝ) : ℝ) : ℂ) ^ (-s)

/-- Conjecture (Velin Yanev, OEIS A352082): for `n > 0`,
`a(n) = (1 - 2^n) * ζ(-n) - 2^n * ζ(-n, n/2 + 1)`. -/
theorem main : ∀ n : ℕ, 0 < n →
    (a n : ℂ) = (1 - 2 ^ n) * riemannZeta (-(n : ℂ))
      - 2 ^ n * hurwitzZetaClassical (-(n : ℂ)) ((n : ℝ) / 2 + 1) := by
  sorry

end OMA.S_oeis_a352082
