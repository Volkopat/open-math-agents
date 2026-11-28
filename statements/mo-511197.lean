import Mathlib

/-!
# Behavior of quadratic homogeneous mapping in the image

Source: https://mathoverflow.net/questions/511197
Credit: @eltociear

Let `Q : ℝ⁴ → ℝ³` be a homogeneous quadratic mapping (each coordinate is a quadratic form, i.e.
`Q x = B(x, x)` for a symmetric bilinear `B`), and suppose `Q` is surjective. The question asks to
show that the multivalued right inverse `y ↦ {x | Q x = y}` admits a bounded selection:
a map `s : ℝ³ → ℝ⁴` with `Q (s y) = y` for every `y`.

Reading of "bounded". Taken literally, the source's condition `‖Q⁻¹(y)‖ < ∞ for all y` holds for
every selection (a vector in `ℝ⁴` always has finite norm), so it says nothing beyond surjectivity.
The argument sketched in the source (fix `y`, take `y_n → y`, pick preimages `x_n`, extract a
convergent subsequence of minimum-norm preimages) aims at local boundedness: preimages of a
bounded set of values can be chosen in a bounded set. This file states that standard reading:
the selection maps bounded sets to bounded sets. Since `Q (c • x) = c ^ 2 • Q x`, this is
equivalent to the usual estimate `∃ C, ∀ y, ∃ x, Q x = y ∧ ‖x‖ ≤ C * √‖y‖`.

`ℝ⁴` and `ℝ³` are `EuclideanSpace ℝ (Fin 4)` and `EuclideanSpace ℝ (Fin 3)`. Boundedness does
not depend on the choice of norm.
-/

namespace OMA.S_mo_511197

theorem main :
    ∀ Q : QuadraticMap ℝ (EuclideanSpace ℝ (Fin 4)) (EuclideanSpace ℝ (Fin 3)),
      Function.Surjective Q →
      ∃ s : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 4),
        (∀ y, Q (s y) = y) ∧
        ∀ B : Set (EuclideanSpace ℝ (Fin 3)), Bornology.IsBounded B →
          Bornology.IsBounded (s '' B) := by
  sorry

end OMA.S_mo_511197
