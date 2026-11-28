import Mathlib

/-!
# A131137: the e.g.f. denominators of log((2*x/3-1)/(x-1)) and polylog(-n,1/4)/4

Source: https://oeis.org/A131137
Credit: @avivorly

A131137 (offset 0): Denominator of (exponential) expansion of `log((2*x/3-1)/(x-1))`.
So `a(n)` is the reduced denominator of `n! * [x^n] log((2*x/3-1)/(x-1))`.
Data: 1, 3, 9, 27, 27, 81, 243, 243, 729, 2187, 729, ...

Conjecture (Wouter Meeussen, Feb 13 2014, in the entry): starting at third term, also equals the denominator of
`polylog(-n,1/4)/4`.

Conventions:
- `log((2*x/3-1)/(x-1)) = log((1 - 2*x/3)/(1 - x)) = -log(1 - x) + log(1 - 2*x/3)`, and its Taylor series at `0` is
  `Sum_{m ≥ 1} (1 - (2/3)^m) x^m / m`. `negLogOneSub c` is the series `-log(1 - c*x) = Sum_{m ≥ 1} c^m x^m / m` over
  `ℚ`, and `logSeries = negLogOneSub 1 - negLogOneSub (2/3)` is the Taylor series above. `A131137 n` is the reduced
  denominator `Rat.den` of `n! * [x^n] logSeries` (so `A131137 0 = 1`, the denominator of `0`).
- `polylog(-n, z) = Li_{-n}(z) = Sum_{k ≥ 1} k^n z^k` for `|z| < 1`. At `z = 1/4` it is the real series
  `∑' k : ℕ, (k : ℝ) ^ n * (1/4 : ℝ) ^ k`; its `k = 0` term is `0` for `n ≥ 1`.
- Indexing: the third term is `a(2)`, and term `a(n+1)` is paired with `polylog(-n,1/4)/4` for `n ≥ 1`, as in
  Meeussen's own Mathematica program in the entry, `Join[{1, 3}, Table[Denominator[PolyLog[-n, 1/4]/4], {n, 31}]]`,
  and in Greathouse's PARI program, `a(n) = denominator(polylog(1-n,1/4)/4)` for `n ≥ 4`. For example
  `polylog(-1,1/4)/4 = 1/9` and `a(2) = 9`. (Pairing `a(n)` with `polylog(-n,1/4)/4` instead fails at once:
  `polylog(-2,1/4)/4 = 5/27` but `a(2) = 9`.)
- The value is not assumed rational: `main` asks for a rational `q` equal to `polylog(-n,1/4)/4` whose reduced
  denominator `q.den` is `a(n+1)`.
-/

namespace OMA.S_oeis_a131137

/-- `-log(1 - c*x) = Sum_{m ≥ 1} c^m x^m / m`, as a formal power series over `ℚ` (constant term `0`). -/
noncomputable def negLogOneSub (c : ℚ) : PowerSeries ℚ :=
  PowerSeries.mk fun m => if m = 0 then 0 else c ^ m / m

/-- The Taylor series at `0` of `log((2*x/3-1)/(x-1)) = -log(1 - x) - (-log(1 - (2/3)*x))`,
that is `Sum_{m ≥ 1} (1 - (2/3)^m) x^m / m`. -/
noncomputable def logSeries : PowerSeries ℚ :=
  negLogOneSub 1 - negLogOneSub (2 / 3)

/-- A131137: `a(n)` is the denominator of the `n`-th coefficient of the exponential expansion of
`log((2*x/3-1)/(x-1))`, i.e. of `n! * [x^n] logSeries`. -/
noncomputable def A131137 (n : ℕ) : ℕ :=
  ((n.factorial : ℚ) * PowerSeries.coeff n logSeries).den

theorem main :
    ∀ n : ℕ, 1 ≤ n → ∃ q : ℚ,
      (q : ℝ) = (∑' k : ℕ, (k : ℝ) ^ n * (1 / 4 : ℝ) ^ k) / 4 ∧ q.den = A131137 (n + 1) := by
  sorry

end OMA.S_oeis_a131137
