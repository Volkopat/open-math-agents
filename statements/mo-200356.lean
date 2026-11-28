import Mathlib

/-!
# Is the total variation distance of product distributions determined by that of the factors?

Source: https://mathoverflow.net/questions/200356
Credit: @koolkao

Question (Jesse Uber, MathOverflow 200356, 2015; CC BY-SA 3.0). Given two discrete distributions
`P` and `Q`, with computable total variation distance `d_TV(P, Q) = ‖P - Q‖₁`, is there a precise
bound for `d_TV(Pⁿ, Qⁿ) = ‖Pⁿ - Qⁿ‖₁`, as needed to estimate the power of an optimal test for
multiple samples? Moreover, is it possible to exactly compute `d_TV(Pⁿ, Qⁿ)` without enumerating
all combinations?

We state the exact-computation question in the reading "is `d_TV(Pⁿ, Qⁿ)` a function of
`d_TV(P, Q)` alone": `main` states that there is a function `φ`, allowed to depend on the
alphabet size `k` and the number of samples `n`, with `d_TV(Pⁿ, Qⁿ) = φ k n (d_TV(P, Q))` for all
distributions `P`, `Q` on `Fin k`. A disproof is two pairs of distributions with the same total
variation distance whose `n`-fold products have different total variation distances.

Translation choices:
* a discrete distribution on a `k`-letter alphabet is a vector `P : Fin k → ℝ` with nonnegative
  entries summing to `1` (`IsDist`);
* `Pⁿ` is the law of `n` independent samples, the vector `x ↦ ∏ i, P (x i)` on `Fin n → Fin k`;
* the total variation distance is `(∑ x, |P x - Q x|) / 2`; the source's `‖P - Q‖₁` is twice
  this, which changes `φ` only by a factor;
* "exactly compute without enumerating" is read as "is a function of `k`, `n` and `d_TV(P, Q)`";
  the "precise bound" part of the question is not stated.
-/

namespace OMA.S_mo_200356

/-- `P` is a probability vector on `Fin k`. -/
def IsDist {k : ℕ} (P : Fin k → ℝ) : Prop := (∀ i, 0 ≤ P i) ∧ ∑ i, P i = 1

/-- Total variation distance `(∑ x, |P x - Q x|) / 2` of two vectors on a finite type. -/
noncomputable def tv {α : Type*} [Fintype α] (P Q : α → ℝ) : ℝ := (∑ x, |P x - Q x|) / 2

/-- The law `Pⁿ` of `n` independent samples from `P`. -/
def prodDist {k : ℕ} (n : ℕ) (P : Fin k → ℝ) : (Fin n → Fin k) → ℝ := fun x => ∏ i, P (x i)

/-- The total variation distance of `n`-fold products is a function of `k`, `n` and the total
variation distance of the factors. -/
theorem main :
    ∃ φ : ℕ → ℕ → ℝ → ℝ, ∀ (k n : ℕ) (P Q : Fin k → ℝ), IsDist P → IsDist Q →
      tv (prodDist n P) (prodDist n Q) = φ k n (tv P Q) := by
  sorry

end OMA.S_mo_200356
