import Mathlib

/-!
# A function whose second iterate is computable but whose third iterate is not

Source: https://mathoverflow.net/questions/441173
Asked by MathOverflow user Numa Grinberg.

The question asks for a function `f : ℕ → ℕ` such that `x ↦ f(f(x))` is computable but
`x ↦ f(f(f(x)))` is not computable.

Translation choices.
* Computability is Mathlib's `Computable` (partial recursive functions, via `Primcodable`).
* `main` asserts that such a function exists.
-/

namespace OMA.S_mo_441173

theorem main :
    ∃ f : ℕ → ℕ, Computable (fun x => f (f x)) ∧ ¬ Computable (fun x => f (f (f x))) := by
  sorry

end OMA.S_mo_441173
