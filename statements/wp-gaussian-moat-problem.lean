import Mathlib

/-!
# Gaussian moat problem

Source: https://en.wikipedia.org/wiki/Gaussian_moat
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Source statement (Gordon, 1962): the Gaussian moat problem asks whether it is possible to find an
infinite sequence of distinct Gaussian prime numbers such that the difference between
consecutive numbers in the sequence is bounded (more colourfully: can one walk from the origin to
infinity using the Gaussian primes as stepping stones, with steps of bounded size?).

The question is yes/no. `main` is the proposition asked about (that such a sequence exists), so
the problem is settled either by proving `main` or by proving `¬ main`. The source reports a
claimed (OpenAI, 2026) proof that no such walk exists, which would be a proof of `¬ main`.

Conventions:
* Gaussian integers are Mathlib's `GaussianInt` (`ℤ[i]`) and a Gaussian prime is a prime
  element (`Prime z`); since `ℤ[i]` is a principal ideal domain this is the same as an
  irreducible element;
* the infinite sequence is `f : ℕ → GaussianInt`; distinct means `f` is injective;
* bounded differences: some real `B` bounds the complex absolute value `‖f (n + 1) - f n‖` of
  every step, computed in `ℂ` through Mathlib's coercion `GaussianInt → ℂ`;
* starting at the origin is not imposed: a walk with bounded steps starting anywhere can be
  joined to a Gaussian prime near the origin by one extra finite step, so the two readings are
  equivalent, and the source's first (precise) sentence does not impose it.
-/

namespace OMA.S_wp_gaussian_moat_problem

theorem main : ∃ (f : ℕ → GaussianInt) (B : ℝ), Function.Injective f ∧
    (∀ n, Prime (f n)) ∧ ∀ n, ‖((f (n + 1) : ℂ) - (f n : ℂ))‖ ≤ B := by
  sorry

end OMA.S_wp_gaussian_moat_problem
