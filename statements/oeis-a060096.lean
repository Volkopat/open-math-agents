import Mathlib

/-!
# A060096: Numerator of coefficients of Euler polynomials (rising powers).

Source: https://oeis.org/A060096
Credit: @theodorebennahum-hue (agent: Claude Code, model claude-opus-5-5)

The triangle `E(n, m)` (numerators A060096, denominators A060097) lists the coefficients of the
Euler polynomials, `E(n, x) = ∑_{m=0}^{n} E(n, m) x^m`, with e.g.f. `2 exp(x z) / (exp z + 1)`.
Conjecture (Wolfdieter Lang, OEIS, Jun 15 2015): the first (`m = 0`) column of the rational
triangle is `E(n, 0) = (-1)^n * A198631(n) / A006519(n + 1)`, for every `n ≥ 0`.

## Encoding

* `eulerConst n = E(n, 0)`, the `n`-th coefficient times `n!` of the e.g.f. `2 / (exp z + 1)`.
  Multiplying `(exp z + 1) * ∑ e_n z^n / n! = 2` out gives `e_0 = 1` and
  `e_n = -(1/2) ∑_{k<n} C(n, k) e_k` for `n ≥ 1`, the recursion used below.
* `eulerCoeff n m = C(n, m) * eulerConst (n - m)`: the e.g.f. is the product of
  `2 / (exp z + 1)` and `exp (x z)`, so `E(n, x)` is an Appell sequence. Only `m = 0` is used.
* `r n`, the rational sequence of A198631: the `n`-th coefficient times `n!` of the e.g.f.
  `2 / (1 + exp (-z))`. Multiplying out gives `r_0 = 1` and
  `r_n = -(1/2) ∑_{k<n} C(n, k) (-1)^(n-k) r_k` for `n ≥ 1`.
  The OEIS name says e.g.f. `1 / (1 + exp (-x))`, but its formula section and data use
  `2 / (1 + exp (-x))` (`a(0) = 1` with `A006519(1) = 1`). Both give the same numerators.
* `A198631 n` is the numerator of `r n` in lowest terms (`Rat.num`, sign included).
* `A006519 m = 2 ^ v₂(m)`, the highest power of `2` dividing `m` (offset 1; used at `n + 1`).
-/

namespace OMA.S_oeis_a060096

/-- `E(n, 0)`: the constant term of the `n`-th Euler polynomial, i.e. `n!` times the `n`-th
coefficient of `2 / (exp z + 1)`. -/
def eulerConst : ℕ → ℚ :=
  WellFounded.fix Nat.lt_wfRel.wf fun n e =>
    if n = 0 then 1 else -(1 / 2) * ∑ k : Fin n, (n.choose k : ℚ) * e k k.2

/-- `E(n, m)`: the coefficient of `x ^ m` in the `n`-th Euler polynomial
(A060096(n, m) / A060097(n, m)). -/
def eulerCoeff (n m : ℕ) : ℚ := (n.choose m : ℚ) * eulerConst (n - m)

/-- The rational sequence of A198631: `n!` times the `n`-th coefficient of
`2 / (1 + exp (-z))`. -/
def r : ℕ → ℚ :=
  WellFounded.fix Nat.lt_wfRel.wf fun n s =>
    if n = 0 then 1
    else -(1 / 2) * ∑ k : Fin n, (n.choose k : ℚ) * (-1) ^ (n - (k : ℕ)) * s k k.2

/-- A198631: the numerator of `r n` (in lowest terms, sign included). -/
def A198631 (n : ℕ) : ℤ := (r n).num

/-- A006519: the highest power of `2` dividing `m`. -/
def A006519 (m : ℕ) : ℕ := 2 ^ padicValNat 2 m

theorem main :
    ∀ n : ℕ, eulerCoeff n 0 = (-1 : ℚ) ^ n * (A198631 n : ℚ) / (A006519 (n + 1) : ℚ) := by
  sorry

end OMA.S_oeis_a060096
