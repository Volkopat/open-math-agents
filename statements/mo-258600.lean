import Mathlib

/-!
# Inducing surjections on GL_n

Source: https://mathoverflow.net/questions/258600
Credit: @dwilfand-sys (agent: Claude Code, model claude-fable-5-2)

Question: suppose `A`, `B` are (possibly noncommutative) rings and `f : A → B` is a surjective
ring homomorphism. Does it necessarily follow that the induced map `GL_n(A) → GL_n(B)` is
surjective for `n > 1`? `main` states the affirmative answer.

Conventions.
* Rings are unital and are not assumed commutative; `f` is a unital ring homomorphism.
* `GL_n(R)` is the group of invertible `n × n` matrices over `R`, that is, the group of units of
  the matrix ring `Matrix (Fin n) (Fin n) R`. This needs no commutativity.
* `glMap f n` is the induced group homomorphism: it applies `f` to every entry.
-/

namespace OMA.S_mo_258600

/-- The homomorphism `GL_n(A) → GL_n(B)` induced by a ring homomorphism `f : A → B`. -/
def glMap {A B : Type} [Ring A] [Ring B] (f : A →+* B) (n : ℕ) :
    (Matrix (Fin n) (Fin n) A)ˣ →* (Matrix (Fin n) (Fin n) B)ˣ :=
  Units.map (RingHom.mapMatrix f).toMonoidHom

/-- Affirmative answer: for a surjective ring homomorphism `f` and `n > 1`, the induced map
`GL_n(A) → GL_n(B)` is surjective. -/
theorem main : ∀ (A B : Type) [Ring A] [Ring B] (f : A →+* B), Function.Surjective f →
    ∀ n : ℕ, 1 < n → Function.Surjective (glMap f n) := by
  sorry

end OMA.S_mo_258600
