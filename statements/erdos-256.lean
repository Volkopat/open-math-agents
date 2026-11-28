import Mathlib

/-!
# Erdős Problem 256

Source: https://www.erdosproblems.com/256
Credit: @graydeveloper01

Source text: let n ≥ 1 and let f(n) be maximal such that for any integers 1 ≤ a_1 ≤ ⋯ ≤ a_n we have
max_{|z|=1} |∏_i (1 - z^{a_i})| ≥ f(n). Estimate f(n); in particular, is it true that there exists
some constant c > 0 such that log f(n) ≫ n^c?

STATUS WARNING. `main` is the affirmative answer to the specific question, stated as posed. The source
page itself records that the answer to this specific question is NO: Belov and Konyagin [BeKo96]
proved log f(n) ≪ (log n)^4, which contradicts log f(n) ≫ n^c for every c > 0. So `main` is
expected to be FALSE, and the mathematically correct resolution is a proof of `¬ main` (a
formalisation of the Belov-Konyagin bound, or of any bound log f(n) = o(n^c) for all c > 0). The
problem is presumably still listed as open because of the open-ended part, Estimate f(n). Known
bounds: the source page records f(n) > √(2n), attributed to Erdős and Szekeres (its comments note
a gap in the original argument, repaired by Billsborough et al.), and the comments report
f(n) ≥ 2 √n (Tang 2025); the upper bound is f(n) ≤ exp (C (log n)^4) by [BeKo96].

The page also discusses a different quantity f*(n), with strictly increasing exponents
(Bourgain, Chang); it is not the quantity formalised here.

Modelling choices.

* `supNorm a` is max_{|z|=1} |∏_i (1 - z^{a_i})|, written as a supremum over the subtype of the unit
  circle `Metric.sphere (0 : ℂ) 1`. The circle is nonempty and compact and the function is
  continuous, so the supremum is attained (it is the max of the source), and it is bounded above by
  2 ^ n, so the real `⨆` is not a junk value.
* `f n` is the infimum of `supNorm a` over all admissible tuples, which is exactly the maximal real
  number that is a lower bound for every `supNorm a`. Admissible tuples are `a : Fin n → ℕ` with
  `1 ≤ a i` for all i and `Monotone a`, i.e. 1 ≤ a_1 ≤ ⋯ ≤ a_n literally as in the source (equal
  exponents allowed). The product does not depend on the order, so dropping `Monotone` would give
  the same value; it is kept only to stay literal. The index set is nonempty (constant tuple 1) and
  the values are ≥ 0, so the real `⨅` is not a junk value.
* The exponents are natural numbers and `z ^ a i` is the monoid power in ℂ; there is no natural
  subtraction anywhere (`1 - z ^ a i` is subtraction in ℂ).
* `log f(n) ≫ n^c` (Vinogradov notation) is read as: there is a constant C > 0 such that
  C * n ^ c ≤ log (f n) for all sufficiently large n (`∀ᶠ n in atTop`). Here `(n : ℝ) ^ c` is the
  real power with real exponent c, and `Real.log` is the natural logarithm. Since the right side is
  positive for n ≥ 1, the inequality forces log (f n) > 0, hence (as f n ≥ 0) f n > 1, so the
  convention `Real.log 0 = 0` and the values of `Real.log` on nonpositive reals cannot make the
  statement true by accident; it is equivalent to exp (C * n ^ c) ≤ f n eventually. (In fact
  f n > √(2n) > 0, see the known bounds above, but the statement does not rely on this.)
* Eventually versus all n ≥ 1: for this statement the two readings are equivalent up to changing
  C exactly when f n > 1 for every n ≥ 1, which is true (f(n) > √(2n) ≥ 1); the eventual form is
  the standard meaning of ≫ and is used here.
* n = 0 (excluded by the source) is irrelevant because of `∀ᶠ n in atTop`; there `f 0 = 1`.
-/

namespace OMA.S_erdos_256

/-- max over the unit circle of |∏_i (1 - z^{a_i})|. -/
noncomputable def supNorm {n : ℕ} (a : Fin n → ℕ) : ℝ :=
  ⨆ z : Metric.sphere (0 : ℂ) 1, ‖∏ i : Fin n, (1 - (z : ℂ) ^ a i)‖

/-- f(n): the largest real number that is at most `supNorm a` for all integers
1 ≤ a_1 ≤ ⋯ ≤ a_n, i.e. the infimum of `supNorm a` over all such tuples. -/
noncomputable def f (n : ℕ) : ℝ :=
  ⨅ a : {a : Fin n → ℕ // (∀ i, 1 ≤ a i) ∧ Monotone a}, supNorm a.1

theorem main :
    ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 < C ∧
      ∀ᶠ n : ℕ in Filter.atTop, C * (n : ℝ) ^ c ≤ Real.log (f n) := by
  sorry

end OMA.S_erdos_256
