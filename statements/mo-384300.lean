import Mathlib

/-!
# A common partner completing primitive vectors of `ℤ^{n+1}` to bases

Source: https://mathoverflow.net/questions/384300
Asked by MathOverflow user PR_ (Extending finitely many primitive elements of Z^{n+1} to bases
with non-trivial intersection).

Given finitely many primitive elements `v_1, ..., v_k ∈ ℤ^{n+1}` (the gcd of the entries of
each `v_i` is `±1`), is it always possible to find `v ∈ ℤ^{n+1}` such that each of the sets
`{v_i, v}` can be extended to a basis of `ℤ^{n+1}`? (The asker notes a counterexample for
`n = 1` and asks in particular about `n ≥ 2`.)

Translation choices.
* `ℤ^{n+1}` is `Fin (n + 1) → ℤ`. A vector is primitive when every common divisor of its
  entries is a unit (`IsPrimitive`).
* The set `{u, w}` can be extended to a basis when it is contained in the range of some
  `ℤ`-basis of `ℤ^{n+1}` (`ExtendsToBasis`).
* `main` is the affirmative answer, for all `n` and all finite families (indexed by `Fin k`,
  repetitions allowed). It is stated for every `n`, including the cases `n ≥ 2`.
-/

namespace OMA.S_mo_384300

/-- Every common divisor of the entries of `v` is `±1`. -/
def IsPrimitive {m : ℕ} (v : Fin m → ℤ) : Prop :=
  ∀ d : ℤ, (∀ j, d ∣ v j) → IsUnit d

/-- The set `{u, w}` is contained in some basis of `ℤ^m`. -/
def ExtendsToBasis {m : ℕ} (u w : Fin m → ℤ) : Prop :=
  ∃ b : Module.Basis (Fin m) ℤ (Fin m → ℤ), ({u, w} : Set (Fin m → ℤ)) ⊆ Set.range b

theorem main :
    ∀ n k : ℕ, ∀ v : Fin k → Fin (n + 1) → ℤ, (∀ i, IsPrimitive (v i)) →
      ∃ w : Fin (n + 1) → ℤ, ∀ i, ExtendsToBasis (v i) w := by
  sorry

end OMA.S_mo_384300
