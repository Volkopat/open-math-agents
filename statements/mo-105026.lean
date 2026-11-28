import Mathlib

/-!
# Semirings whose prime ideals are subtractive

Source: https://mathoverflow.net/questions/105026
Credit: @koolkao

Question (Peyman Nasehpour, MathOverflow 105026, 2012; CC BY-SA 3.0). Let `S` be a commutative
semiring with identity such that each prime ideal of `S` is subtractive. Does this imply all
ideals of `S` to be subtractive?

The source's definitions: `(S, +)` is a commutative monoid with identity element `0`; `(S, ·)`
is a commutative monoid with identity element `1 ≠ 0`; multiplication distributes over addition;
`0` is absorbing for multiplication. A nonempty subset `I` is an ideal if `a + b ∈ I` for all
`a, b ∈ I` and `s a ∈ I` for all `s ∈ S`, `a ∈ I`. A prime ideal is an ideal `P ≠ S` such that
`a b ∈ P` implies `a ∈ P` or `b ∈ P`. An ideal `I` is subtractive if `a + b ∈ I` and `a ∈ I`
imply `b ∈ I`.

`main` states that the answer is yes. A disproof is a commutative semiring with `1 ≠ 0` all of
whose prime ideals are subtractive, together with an ideal that is not.

Translation choices:
* a commutative semiring with identity, as defined in the source, is a `CommSemiring` (Mathlib's
  structure has exactly these axioms; its extra `nsmul`/`natCast`/`npow` fields are determined
  by them) together with `Nontrivial S` for `1 ≠ 0`; `S` lives in `Type`;
* the source's ideals are exactly Mathlib's `Ideal S` (a nonempty subset closed under
  multiplication by `S` contains `0 = 0 · a`); prime ideals are `Ideal.IsPrime` (proper, and
  `a b ∈ P → a ∈ P ∨ b ∈ P`);
* subtractive is `IsSubtractive I`, defined below exactly as in the source.
-/

namespace OMA.S_mo_105026

/-- An ideal `I` is subtractive if `a + b ∈ I` and `a ∈ I` imply `b ∈ I`. -/
def IsSubtractive {S : Type} [CommSemiring S] (I : Ideal S) : Prop :=
  ∀ a b : S, a + b ∈ I → a ∈ I → b ∈ I

/-- If every prime ideal of `S` is subtractive, then every ideal of `S` is subtractive. -/
theorem main :
    ∀ (S : Type) [CommSemiring S] [Nontrivial S],
      (∀ P : Ideal S, P.IsPrime → IsSubtractive P) → ∀ I : Ideal S, IsSubtractive I := by
  sorry

end OMA.S_mo_105026
