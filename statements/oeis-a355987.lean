import Mathlib

/-!
# A355987: a(n) = n! * Sum_{k=1..n} 1/floor(n/k)!.

Source: https://oeis.org/A355987
Credit: @bmendonca3

[Lean proof of this statement](https://github.com/bmendonca3/open-math-agents/blob/fc99e76f3f41da57cf134f0c1c843e7f40ab493f/proofs/oeis-a355987.lean)

Entry A355987 (Seiichi Manyama, Jul 22 2022), offset 1, data 1, 3, 13, 61, 421, 2641, 23521, ...
Formula section:
a(n) ~ c * n! * n, where c = 0.59962032... - Vaclav Kotesovec, Aug 03 2022
Conjecture: c = Sum_{k>=1} 1/((k+1)!*k) = 2 - exp(1) - A001620 + A091725. - Vaclav Kotesovec, Sep 24 2023

A001620 is Euler's constant gamma. A091725 is Ei(1), the exponential integral at 1.

The conjecture has two equalities, and `main` is their conjunction:
1. the constant c of the asymptotic formula is S = Sum_{k>=1} 1/((k+1)!*k), that is
   a(n) ~ S * n! * n as n tends to infinity;
2. S = 2 - e - gamma + Ei(1).

Formalization notes:
* `a n` is the formula of the entry, read in the rationals (floor(n/k) is the division of
  naturals `n / k`). All its values are integers.
* The constant of an asymptotic formula a(n) ~ c * n! * n is unique when it exists: it is the limit
  of a(n) / (n! * n). So the first equality is the claim that the asymptotic formula holds with
  c = S. The relation ~ is Mathlib's `Asymptotics.IsEquivalent` along `Filter.atTop`.
* Sum_{k>=1} f(k) is written as the sum over all naturals k of f(k + 1).
* Mathlib has no exponential integral. Ei(1) is stated by its definition as a Cauchy principal
  value (DLMF 6.2.5): Ei(x) = PV Integral_{t <= x} e^t / t dt for x > 0. The principal value at
  x = 1 is the limit, as eps tends to 0 from above, of
  Integral_{t <= -eps} e^t / t dt + Integral_{eps <= t <= 1} e^t / t dt (`EiOneCut eps`).
  `main` says that this limit exists and that its value satisfies the second equality. No series
  for Ei is used in the statement.
* gamma is Mathlib's `Real.eulerMascheroniConstant`.
-/

namespace OMA.S_oeis_a355987

open Filter Asymptotics Topology
open scoped Nat

/-- A355987: `a(n) = n! * Sum_{k=1..n} 1/floor(n/k)!`. -/
def a (n : ℕ) : ℚ :=
  (n ! : ℚ) * ∑ k ∈ Finset.Icc 1 n, 1 / ((n / k)! : ℚ)

/-- The series `Sum_{k>=1} 1/((k+1)!*k)`, with the index `k` written as `k + 1`. -/
noncomputable def S : ℝ :=
  ∑' k : ℕ, 1 / ((((k + 1) + 1)! : ℝ) * ((k + 1 : ℕ) : ℝ))

/-- The integral of `e^t / t` over `t ≤ 1` with the interval `(-ε, ε)` around the pole removed.
Its limit as `ε` tends to `0` from above is the principal value `Ei(1)`. -/
noncomputable def EiOneCut (ε : ℝ) : ℝ :=
  (∫ t in Set.Iic (-ε), Real.exp t / t) + ∫ t in ε..1, Real.exp t / t

/-- Kotesovec's conjecture: `a(n) ~ S * n! * n`, and `S = 2 - e - gamma + Ei(1)`. -/
theorem main :
    (fun n : ℕ => (a n : ℝ)) ~[atTop] (fun n : ℕ => S * (n ! : ℝ) * (n : ℝ)) ∧
    ∃ Ei1 : ℝ, Tendsto EiOneCut (𝓝[>] 0) (𝓝 Ei1) ∧
      S = 2 - Real.exp 1 - Real.eulerMascheroniConstant + Ei1 := by
  sorry

end OMA.S_oeis_a355987
