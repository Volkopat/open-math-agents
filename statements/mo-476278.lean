import Mathlib

/-!
# An inequality involving a concave monotonic function

Source: https://mathoverflow.net/questions/476278
Credit: @koolkao

Question (Alireza Bakhtiari, MathOverflow 476278, 2024; CC BY-SA 4.0). Assume that
`f : ℝ → ℝ₊` is a concave, non-decreasing and positive function. Let `𝕏` be a finite set
consisting of `0 ≤ x₁ ≤ x₂ ≤ x₃ ≤ … ≤ xₙ`. Further, let `X` be a random variable supported on `𝕏`.
I am interested in the following inequality:
`(f(xₙ) - E[f(X)]) / √(E[(f(X) - E[f(X)])²]) ≤ (xₙ - E[X]) / √(E[(X - E[X])²])`.
Is this inequality always true under the given conditions? If so, can you provide a proof or some
intuition behind why this inequality holds? If not, can you provide a counterexample or conditions
under which it might fail?

`main` states that the inequality always holds; a disproof is a counterexample.

Translation choices:
* the points are `x : Fin (n + 1) → ℝ` with `0 ≤ x i` and `x` monotone (so `x₁ ≤ … ≤ xₙ`, and
  `xₙ` is `x (Fin.last n)`); ties are allowed, as in the source. Indexing from `0` and writing the
  number of points as `n + 1` only relabels them;
* a random variable supported on `𝕏` is given by its law: weights `p i ≥ 0` with `∑ p i = 1`
  (`p i` is the probability of the point `x i`). Points of weight `0` are allowed, since a support
  condition only restricts where the mass lies; `E[g(X)] = ∑ p i * g (x i)`;
* a concave function on all of `ℝ` that is bounded below is constant, and then the left-hand side
  is `0 / 0`; so the source's hypotheses are read on `[0, ∞)`, where `X` takes its values:
  `f : ℝ → ℝ` is concave and non-decreasing on `Set.Ici 0` and `f t ≥ 0` for `t ≥ 0` (`ℝ₊` read as
  `[0, ∞)`; requiring `f t > 0` instead would only weaken the statement). Values of `f` on
  `(-∞, 0)` play no role;
* the two standard deviations are `Real.sqrt` of the variances, and both variances are assumed
  positive, as the source implicitly does when it divides by them;
* not stated: the requests for intuition and for conditions under which the inequality might fail.

Status: MathOverflow 476278 had no answers or comments in November 2026.
-/

namespace OMA.S_mo_476278

/-- The inequality of MathOverflow 476278 holds for every concave, non-decreasing, non-negative
`f` on `[0, ∞)` and every law on finitely many points `0 ≤ x₁ ≤ … ≤ xₙ`. -/
theorem main :
    ∀ (n : ℕ) (x : Fin (n + 1) → ℝ), (∀ i, 0 ≤ x i) → Monotone x →
      ∀ (p : Fin (n + 1) → ℝ), (∀ i, 0 ≤ p i) → ∑ i, p i = 1 →
      ∀ f : ℝ → ℝ, ConcaveOn ℝ (Set.Ici 0) f → MonotoneOn f (Set.Ici 0) →
        (∀ t, 0 ≤ t → 0 ≤ f t) →
        0 < ∑ i, p i * (x i - ∑ j, p j * x j) ^ 2 →
        0 < ∑ i, p i * (f (x i) - ∑ j, p j * f (x j)) ^ 2 →
        (f (x (Fin.last n)) - ∑ i, p i * f (x i)) /
            Real.sqrt (∑ i, p i * (f (x i) - ∑ j, p j * f (x j)) ^ 2) ≤
          (x (Fin.last n) - ∑ i, p i * x i) /
            Real.sqrt (∑ i, p i * (x i - ∑ j, p j * x j) ^ 2) := by
  sorry

end OMA.S_mo_476278
