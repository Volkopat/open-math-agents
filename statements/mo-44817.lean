import Mathlib

/-!
# Three-dimensional arrays with recurrences in two directions of planes

Source: https://mathoverflow.net/questions/44817 (Peter Shor, CC BY-SA 4.0).
Credit: @connoranderson

We use finite homogeneous linear shift recurrences with rational polynomial coefficients in
all three coordinates. In a family of parallel coordinate planes the first coordinate is held
fixed; the same coefficient polynomials apply throughout the family. A finite set of forward
shifts fits inside a square stencil. A relation with backward shifts can be translated forward.
-/

namespace OMA.S_mo_44817

/-- The three polynomial variables correspond to the fixed coordinate and the two shifted ones. -/
abbrev Coefficient := Polynomial (Polynomial (Polynomial ℚ))

noncomputable def value (P : Coefficient) (t x y : ℕ) : ℚ :=
  ((P.eval (t : Polynomial (Polynomial ℚ))).eval (x : Polynomial ℚ)).eval (y : ℚ)

/-- A nonzero polynomial-coefficient relation between finitely many shifts in each plane. -/
def HasPlanarRecurrence (A : ℕ → ℕ → ℕ → ℕ) : Prop :=
  ∃ d : ℕ, ∃ c : Fin d → Fin d → Coefficient,
    (∃ a b, c a b ≠ 0) ∧ ∀ t x y : ℕ,
      (∑ a : Fin d, ∑ b : Fin d, value (c a b) t x y * (A t (x+a.val) (y+b.val) : ℚ)) = 0

theorem main : ∃ A : ℕ → ℕ → ℕ → ℕ,
    HasPlanarRecurrence (fun k i j => A i j k) ∧
    HasPlanarRecurrence (fun j i k => A i j k) ∧
    ¬ HasPlanarRecurrence A := by
  sorry

end OMA.S_mo_44817
