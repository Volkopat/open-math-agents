import Mathlib

/-!
# Two conjectural congruences for Franel numbers

Source: https://mathoverflow.net/questions/343847 (Zhi-Wei Sun, CC BY-SA 4.0).

The Franel numbers are `f_n = ∑_{k=0}^{n} binom(n, k)^3`.
Conjecture (Sun). For each odd prime `p`,
1. `∑_{k=1}^{p-1} f_{k-1} / (k 8^{k-1}) ≡ -p² B_{p-3} (mod p³)`, and
2. `∑_{k=1}^{p-1} f_k / (k 8^k) ≡ 3 q_p(2) - (3/2) p q_p(2)² + p² q_p(2)³ (mod p³)`,
where `B_{p-3}` is the `(p-3)`-th Bernoulli number and `q_p(2) = (2^{p-1} - 1)/p` is the Fermat
quotient. (Both are known modulo `p`, by Remark 1.1 of Sun's 2013 paper on Franel numbers.)

Formalization notes:
* Both sides are rational numbers whose denominators are prime to `p` (`k < p`, `8` and `2` are
  prime to the odd prime `p`, and `B_{p-3}` is `p`-integral by von Staudt–Clausen). A congruence
  `x ≡ y (mod p³)` between such rationals is written `0 ≤ padicValRat p ((x - y) / p ^ 3)`, i.e.
  `(x - y) / p³` is a `p`-adic integer; this also covers `x = y`, since `padicValRat p 0 = 0`.
  This is the convention of `FormalConjectures/OEIS/208425.lean`.
* `B_{p-3}` is Mathlib's `bernoulli (p - 3)`; the index is `0` for `p = 3` and even otherwise, so
  the choice of sign convention for `B_1` plays no role.
* `q_p(2)` is the rational `(2^{p-1} - 1)/p` (an integer by Fermat's little theorem).
* Checked numerically: both congruences hold for every odd prime `p < 110`.
-/

namespace OMA.S_mo_343847

/-- The Franel numbers `f_n = ∑_{k=0}^{n} binom(n, k)^3`. -/
def franel (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), (n.choose k) ^ 3

/-- The Fermat quotient `q_p(2) = (2^{p-1} - 1)/p`, as a rational number. -/
def fermatQuotient (p : ℕ) : ℚ :=
  ((2 : ℚ) ^ (p - 1) - 1) / p

/-- Sun's two conjectural congruences for Franel numbers modulo `p³`, for every odd prime `p`. -/
theorem main : ∀ p : ℕ, p.Prime → Odd p →
    (0 ≤ padicValRat p
        ((∑ k ∈ Finset.Icc 1 (p - 1), (franel (k - 1) : ℚ) / (k * 8 ^ (k - 1))
          - (-(p : ℚ) ^ 2 * bernoulli (p - 3))) / (p : ℚ) ^ 3)) ∧
    (0 ≤ padicValRat p
        ((∑ k ∈ Finset.Icc 1 (p - 1), (franel k : ℚ) / (k * 8 ^ k)
          - (3 * fermatQuotient p - 3 / 2 * p * fermatQuotient p ^ 2
              + (p : ℚ) ^ 2 * fermatQuotient p ^ 3)) / (p : ℚ) ^ 3)) := by
  sorry

end OMA.S_mo_343847
