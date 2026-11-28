import Mathlib

/-!
# Generalized star-height problem

Source: https://en.wikipedia.org/wiki/Generalized_star-height_problem
Credit: @my-other-github-account

The source asks whether all regular languages can be expressed using generalized
regular expressions (regular expressions with a built-in complement operator) with
a limited nesting depth of Kleene stars. We read "limited" as one uniform bound `n`
for all regular languages over all finite alphabets.

Attribution: `Expression`, `Expression.language`, `Expression.height` and
`HasHeightAtMost` are adapted from OpenAI's `openai/math` repository (Apache-2.0),
https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/GeneralizedStarHeight.lean
whose `OAI.GeneralizedStarHeight.main` states the bound `3`.
-/

namespace OMA.S_wp_generalized_star_height_problem

universe u

/-- Generalized regular expressions: the empty language, the empty word, letters,
union, concatenation, complement and Kleene star. -/
inductive Expression (Alphabet : Type u) : Type u
  | zero : Expression Alphabet
  | one : Expression Alphabet
  | letter : Alphabet → Expression Alphabet
  | union : Expression Alphabet → Expression Alphabet → Expression Alphabet
  | concat : Expression Alphabet → Expression Alphabet → Expression Alphabet
  | compl : Expression Alphabet → Expression Alphabet
  | star : Expression Alphabet → Expression Alphabet

namespace Expression

open scoped Computability

/-- The language denoted by a generalized regular expression. -/
def language {Alphabet : Type u} : Expression Alphabet → Language Alphabet
  | .zero => 0
  | .one => 1
  | .letter a => {[a]}
  | .union P Q => P.language + Q.language
  | .concat P Q => P.language * Q.language
  | .compl P => P.languageᶜ
  | .star P => P.language∗

/-- Nesting depth of Kleene stars; complement does not increase it. -/
def height {Alphabet : Type u} : Expression Alphabet → ℕ
  | .zero | .one | .letter _ => 0
  | .union P Q | .concat P Q => max P.height Q.height
  | .compl P => P.height
  | .star P => 1 + P.height

end Expression

/-- `L` has generalized star height at most `n`. -/
def HasHeightAtMost {Alphabet : Type u} (L : Language Alphabet) (n : ℕ) : Prop :=
  ∃ P : Expression Alphabet, P.language = L ∧ P.height ≤ n

/-- There is a uniform bound on the generalized star height of all regular languages
over finite alphabets. -/
theorem main : ∃ n : ℕ, ∀ (Alphabet : Type u) [Finite Alphabet] (L : Language Alphabet),
    L.IsRegular → HasHeightAtMost L n := by
  sorry

end OMA.S_wp_generalized_star_height_problem
