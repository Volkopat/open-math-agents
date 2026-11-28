import Mathlib

/-!
# Is the variance of an eigenfunction along a Markov chain nondecreasing?

Source: https://mathoverflow.net/questions/58241
Credit: @koolkao

Question (John Jiang, MathOverflow 58241, 2011; CC BY-SA 3.0). Given a function
`f : Ω → ℝ`, where `Ω` is the state space of an ergodic finite state Markov chain, let the chain
start at a single state `x ∈ Ω`. Assume `f` is an eigenfunction of the chain. Is it true that
`𝔼_t (f - 𝔼_t f)²` is nondecreasing in `t`? Here `𝔼_t f` denotes `𝔼 P_t f`, where `P_t` is
the Markov transition kernel from time `0` to time `t`.

`main` states that the answer is yes. A disproof is an ergodic finite chain, a real
eigenfunction `f`, a starting state `x` and a time `t` at which the variance of `f` at time
`t + 1` is smaller than at time `t`.

Translation choices:
* the state space is `Fin n` and the chain is its transition matrix `P`: nonnegative entries and
  row sums `1`; the time-`t` kernel is the matrix power `P ^ t`;
* "ergodic" (irreducible and aperiodic) is stated in the equivalent form for finite chains that
  `P` is primitive: some power `P ^ m` has all entries positive;
* "eigenfunction" means a nonzero real `f` with `P f = μ f` for some real `μ`, where
  `(P f)(x) = ∑_y P(x, y) f(y)` is `P *ᵥ f`;
* starting at `x`, `𝔼_t g = (P ^ t *ᵥ g) x`, so the variance at time `t` is
  `(P ^ t *ᵥ (f * f)) x - ((P ^ t *ᵥ f) x) ^ 2` (`f * f` is the pointwise square);
* "nondecreasing in `t`" is stated for consecutive times `t` and `t + 1`, `t : ℕ`.
-/

namespace OMA.S_mo_58241

open Matrix

/-- For an ergodic finite Markov chain started at a single state, the variance of a real
eigenfunction is nondecreasing in time. -/
theorem main :
    ∀ (n : ℕ) (P : Matrix (Fin n) (Fin n) ℝ), (∀ i j, 0 ≤ P i j) → (∀ i, ∑ j, P i j = 1) →
      (∃ m : ℕ, ∀ i j, 0 < (P ^ m) i j) →
      ∀ (μ : ℝ) (f : Fin n → ℝ), f ≠ 0 → P *ᵥ f = μ • f →
      ∀ (x : Fin n) (t : ℕ),
        (P ^ t *ᵥ (f * f)) x - ((P ^ t *ᵥ f) x) ^ 2 ≤
          (P ^ (t + 1) *ᵥ (f * f)) x - ((P ^ (t + 1) *ᵥ f) x) ^ 2 := by
  sorry

end OMA.S_mo_58241
