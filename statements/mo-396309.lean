import Mathlib

/-!
# Number of isotropic vectors of a perfect pairing over `ℤ/p^nℤ`

Source: https://mathoverflow.net/questions/396309
Asked by MathOverflow user Ted Mao (Number of solutions of quadratic equation from a perfect
pairing over Z/p^nZ).

Let `p > 2` be prime and `V = (ℤ/p^nℤ)^{2k+1}`. Let `B : V × V → ℤ/p^nℤ` be a bilinear
form which is a perfect pairing, i.e. `x ↦ B(x, -)` is an isomorphism `V ≅ V^*`. The
question (in its edited form, for the equation `B(x, x) = 0`) asks whether the number of
solutions of `B(x, x) = 0` is independent of `B`.

Translation choices.
* A bilinear form on `V = Fin (2k+1) → ZMod (p^n)` is given by its matrix `M`, with
  `B(x, y) = dotProduct x (M.mulVec y)`. The form is not required to be symmetric (the example in the
  question is not symmetric). It is a perfect pairing exactly when `M` is invertible, i.e.
  when `det M` is a unit.
* We take `n ≥ 1`; the number of solutions is a `Nat.card`. `main` says that any two perfect pairings have the same number of
  solutions of `B(x, x) = 0`.
* The other parts of the question (intuition, the original version with `B(x, x) = c`,
  general rings) are not formalized.
-/

namespace OMA.S_mo_396309

/-- The number of `x` with `B(x, x) = 0`, for the bilinear form with matrix `M`. -/
noncomputable def isoCount {R : Type} [CommRing R] {m : ℕ} (M : Matrix (Fin m) (Fin m) R) : ℕ :=
  Nat.card {x : Fin m → R // dotProduct x (M.mulVec x) = 0}

theorem main :
    ∀ p : ℕ, p.Prime → 2 < p → ∀ n : ℕ, 1 ≤ n → ∀ k : ℕ,
      ∀ M₁ M₂ : Matrix (Fin (2 * k + 1)) (Fin (2 * k + 1)) (ZMod (p ^ n)),
        IsUnit M₁.det → IsUnit M₂.det → isoCount M₁ = isoCount M₂ := by
  sorry

end OMA.S_mo_396309
