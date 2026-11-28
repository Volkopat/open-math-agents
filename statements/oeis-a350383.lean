import Mathlib

/-!
# A350383: a(n) = [x^n] 1/(1 + x + x^2)^n

Source: https://oeis.org/A350383

`a(n) = [x^n] 1/(1 + x + x^2)^n`, offset 0 (data 1, -1, 1, 2, -15, 49, -98, 48, 561, ...).

From Peter Bala, Apr 15 2023 (the hypergeometric formula there is stated as a fact, not a target):
1. Conjecture: the supercongruence `a(n*p^r) == a(n*p^(r-1)) (mod p^(2*r))` holds for positive
   integers `n` and `r` and all primes `p >= 5`.
2. More generally, let `k` be a positive integer, `m` an integer and `f(x) = g(x)/h(x)` with `g`, `h`
   finite products of cyclotomic polynomials. Then the same supercongruences hold, except for a finite
   number of primes `p` depending on `f`, for `a_(k,m,f)(n) = [x^(k*n)] f(x)^(m*n)`.

Formalized:
- `a n` is the coefficient of `x^n` of `(1 + X + X^2)^(-1)` raised to `n`, in `PowerSeries ℤ`; the inverse
  is `PowerSeries.invOfUnit` with constant coefficient `1` (the true inverse, as `1 + X + X^2` has
  constant coefficient `1`). The congruence is divisibility of the difference in `ℤ`.
- For claim 2, `g` and `h` are given by multisets `G`, `H` of positive indices `d` (with multiplicity), the
  product of `Polynomial.cyclotomic d`. Since every cyclotomic polynomial has constant coefficient `1` or
  `-1`, `f = g/h` is invertible in `PowerSeries ℚ`, computed there with the field inverse. `f^(e)` for an
  integer `e` is `f^e` for `e >= 0` and `(f⁻¹)^(-e)` for `e < 0`. The coefficients are integers, and the
  congruence mod `p^(2r)` is written as: the difference equals `p^(2r)` times an integer.
- 'Except for a finite number of primes' is written as: there is a bound `B` such that the congruences
  hold for every prime `p > B` (for all positive `n`, `r`).
-/

namespace OMA.S_oeis_a350383

open PowerSeries

/-- A350383: `a(n) = [x^n] (1 + x + x^2)^(-n)`. -/
noncomputable def a (n : ℕ) : ℤ :=
  PowerSeries.coeff n ((PowerSeries.invOfUnit (1 + X + X ^ 2 : PowerSeries ℤ) 1) ^ n)

/-- The cyclotomic polynomial `Φ_d` as a rational power series. -/
noncomputable def cyc (d : ℕ) : PowerSeries ℚ :=
  ((Polynomial.cyclotomic d ℚ : Polynomial ℚ) : PowerSeries ℚ)

/-- `f = (∏_{d ∈ G} Φ_d) / (∏_{d ∈ H} Φ_d)` as a rational power series. -/
noncomputable def f (G H : Multiset ℕ) : PowerSeries ℚ :=
  (G.map cyc).prod * ((H.map cyc).prod)⁻¹

/-- `f^e` for an integer exponent `e`. -/
noncomputable def fpow (G H : Multiset ℕ) (e : ℤ) : PowerSeries ℚ :=
  if 0 ≤ e then f G H ^ e.toNat else (f G H)⁻¹ ^ (-e).toNat

/-- `a_(k,m,f)(n) = [x^(k*n)] f(x)^(m*n)`. -/
noncomputable def gen (k : ℕ) (m : ℤ) (G H : Multiset ℕ) (n : ℕ) : ℚ :=
  PowerSeries.coeff (k * n) (fpow G H (m * n))

theorem main :
    (∀ p : ℕ, p.Prime → 5 ≤ p → ∀ n r : ℕ, 0 < n → 0 < r →
      ((p : ℤ) ^ (2 * r)) ∣ (a (n * p ^ r) - a (n * p ^ (r - 1)))) ∧
    (∀ k : ℕ, 0 < k → ∀ m : ℤ, ∀ G H : Multiset ℕ, (∀ d ∈ G, 0 < d) → (∀ d ∈ H, 0 < d) →
      ∃ B : ℕ, ∀ p : ℕ, p.Prime → B < p → ∀ n r : ℕ, 0 < n → 0 < r →
        ∃ z : ℤ, gen k m G H (n * p ^ r) - gen k m G H (n * p ^ (r - 1)) =
          ((p : ℚ) ^ (2 * r)) * z) := by
  sorry

end OMA.S_oeis_a350383
