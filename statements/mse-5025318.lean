import Mathlib

/-!
# Is there a surjective polynomial function `ℕ² → ℤ²`?

Source: https://math.stackexchange.com/questions/5025318

Here `ℕ` contains `0`. There are polynomial bijections `ℕ² → ℕ` (the Cantor pairing
`(x, y) ↦ (x + y)(x + y + 1)/2 + y`), polynomial injections in every direction between `ℕ`,
`ℤ`, `ℕ²`, `ℤ²`, and polynomial surjections `ℕ² → ℕ`, `ℤ² → ℤ` and `ℕ² → ℤ`. The question:
is there a polynomial surjection `ℕ² → ℤ²`? (The asker doubts it.)

`main` states the affirmative: there are polynomials `f, g` in two variables taking integer values
on `ℕ²` such that `(x, y) ↦ (f(x, y), g(x, y))` maps `ℕ²` onto `ℤ²`.

Formalization notes:
* As in the source's examples (the Cantor pairing, pentagonal numbers), coefficients are
  rational: `f, g : MvPolynomial (Fin 2) ℚ`, evaluated at `![x, y]`. No generality is lost: a real
  polynomial taking integer values on `ℕ²` has rational coefficients.
* A polynomial function `ℕ² → ℤ²` is a pair of such polynomials whose values at every point of
  `ℕ²` are integers; surjectivity asks every `(a, b) ∈ ℤ²` to be a value.
-/

namespace OMA.S_mse_5025318

/-- The value of `f ∈ ℚ[x, y]` at `(x, y) ∈ ℕ²`. -/
noncomputable def ev (f : MvPolynomial (Fin 2) ℚ) (x y : ℕ) : ℚ :=
  MvPolynomial.eval ![(x : ℚ), (y : ℚ)] f

/-- There is a polynomial map `ℕ² → ℤ²` that is onto `ℤ²`. -/
theorem main : ∃ f g : MvPolynomial (Fin 2) ℚ,
    (∀ x y : ℕ, ∃ a b : ℤ, ev f x y = a ∧ ev g x y = b) ∧
      ∀ a b : ℤ, ∃ x y : ℕ, ev f x y = a ∧ ev g x y = b := by
  sorry

end OMA.S_mse_5025318
