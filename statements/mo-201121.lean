import Mathlib

/-!
# Choice functions on the n-subsets that differ on adjacent subsets

Source: https://mathoverflow.net/questions/201121
Asked by MathOverflow user Paul.

Let `Ω` be a set with `|Ω| = N` and let `𝓕` be the family of all `n`-element subsets of `Ω`.
The question considers functions `f : 𝓕 → Ω` such that
* `f(A) ∈ A` for every `A ∈ 𝓕`, and
* `f(A₁) ≠ f(A₂)` whenever `|A₁ ∩ A₂| = n - 1`,
and asks when such functions exist. The asker shows that for `n = N - 2` they exist iff `N`
is odd, and states the conjecture that such functions do not exist when `n < N - 2`.

This file formalizes that conjecture.

Translation choices.
* `Ω = Fin N`; a function on `𝓕` is a function `f : Finset (Fin N) → Fin N` of which only
  the values on `n`-element subsets matter (`GoodChoice N n f`).
* The conjecture is stated for `n ≥ 2`: for `n = 1` the function `f {a} = a` always has the
  two properties, so the conjecture is only meaningful for `n ≥ 2`. The inequality
  `n < N - 2` uses natural-number subtraction, which is harmless since `n ≥ 2`.
* `main` is the conjecture: for `2 ≤ n < N - 2` no such function exists.
-/

namespace OMA.S_mo_201121

/-- `f` picks an element of every `n`-subset, with different values on any two `n`-subsets
meeting in `n - 1` elements. -/
def GoodChoice (N n : ℕ) (f : Finset (Fin N) → Fin N) : Prop :=
  (∀ A : Finset (Fin N), A.card = n → f A ∈ A) ∧
    (∀ A B : Finset (Fin N), A.card = n → B.card = n → (A ∩ B).card = n - 1 → f A ≠ f B)

theorem main : ∀ N n : ℕ, 2 ≤ n → n < N - 2 → ¬ ∃ f, GoodChoice N n f := by
  sorry

end OMA.S_mo_201121
