import Mathlib

/-!
# Friedgut–Kalai entropy–influence conjecture

Source: https://en.wikipedia.org/wiki/Entropy_influence_conjecture
Credit: @mgv27

There is an absolute constant C such that every Boolean function f : {−1,1}ⁿ → {−1,1}
satisfies H(f̂²) ≤ C · I(f), where H(f̂²) = Σ_S f̂(S)² log₂(1/f̂(S)²) is the entropy of its
Fourier spectrum and I(f) = Σ_S |S| f̂(S)² is its total influence.

Formalization notes:
* The cube `{−1,1}ⁿ` is modelled as `Fin n → Bool`, with `sgn b = if b then -1 else 1`;
  a Boolean function is `f : (Fin n → Bool) → Bool`, read as `±1`-valued via `sgn`.
* `f̂(S) = 2^{-n} Σ_x f(x) ∏_{i ∈ S} x_i` (uniform measure).
* Terms with `f̂(S) = 0` contribute `0` to the entropy (Mathlib's `Real.log 0 = 0`
  makes `0 · log₂(1/0) = 0`, the usual convention).
* `C` is a single real constant independent of `n` and `f`.
-/

namespace OMA.S_wpc_entropy_influence_conjecture

/-- The `±1` value of a bit: `true ↦ -1`, `false ↦ 1`. -/
def sgn (b : Bool) : ℝ := if b then -1 else 1

/-- The Fourier coefficient `f̂(S)` of `f : {−1,1}ⁿ → {−1,1}`. -/
noncomputable def fourier {n : ℕ} (f : (Fin n → Bool) → Bool) (S : Finset (Fin n)) : ℝ :=
  (1 / (2 : ℝ) ^ n) * ∑ x : Fin n → Bool, sgn (f x) * ∏ i ∈ S, sgn (x i)

/-- The spectral entropy `H(f̂²) = Σ_S f̂(S)² log₂(1/f̂(S)²)`. -/
noncomputable def spectralEntropy {n : ℕ} (f : (Fin n → Bool) → Bool) : ℝ :=
  ∑ S : Finset (Fin n), fourier f S ^ 2 * Real.logb 2 (1 / fourier f S ^ 2)

/-- The total influence `I(f) = Σ_S |S| f̂(S)²`. -/
noncomputable def totalInfluence {n : ℕ} (f : (Fin n → Bool) → Bool) : ℝ :=
  ∑ S : Finset (Fin n), (S.card : ℝ) * fourier f S ^ 2

/-- The entropy–influence conjecture. -/
theorem main : ∃ C : ℝ, ∀ n : ℕ, ∀ f : (Fin n → Bool) → Bool,
    spectralEntropy f ≤ C * totalInfluence f := by
  sorry

end OMA.S_wpc_entropy_influence_conjecture
