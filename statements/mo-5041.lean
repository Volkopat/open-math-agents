import Mathlib

/-!
# Pencils with many completely decomposable fibers

Source: https://mathoverflow.net/questions/5041
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Question (MathOverflow): for a non-constant rational function `F = G/H : ℙ⁴ ⇢ ℙ¹` (`G, H`
homogeneous of the same degree), the poser and Yuzvinsky proved that either (a) after a linear
change of coordinates `F ∈ ℂ(x₀, x₁, x₂, x₃)`, or (b) `F` has at most three completely
decomposable fibers. Is there an example not satisfying (a) but with three completely
decomposable fibers?

Conventions:
* `G, H ∈ ℂ[x₀, …, x₄]` homogeneous of the same degree, not proportional (so `F` is
  non-constant). The fiber over `(λ : μ)` is completely decomposable if `μG - λH` is a nonzero
  product of linear forms (times a constant).
* (a) fails: for no invertible linear change of coordinates `A` do both `G ∘ A` and `H ∘ A`
  avoid the variable `x₄`.
* Three fibers: three pairwise non-proportional points `(λᵢ, μᵢ) ≠ (0, 0)`.
* The source asks for an example; `main` states that one exists, and a disproof would show none
  does.
-/

namespace OMA.S_mo_5041

open MvPolynomial

/-- `P` is a nonzero constant times a product of linear forms. -/
def IsProdLinear (P : MvPolynomial (Fin 5) ℂ) : Prop :=
  P ≠ 0 ∧ ∃ (c : ℂ) (L : List (MvPolynomial (Fin 5) ℂ)),
    (∀ l ∈ L, l.IsHomogeneous 1) ∧ P = C c * L.prod

/-- Linear change of coordinates by an invertible matrix. -/
noncomputable def linSubst (A : Matrix (Fin 5) (Fin 5) ℂ) (P : MvPolynomial (Fin 5) ℂ) :
    MvPolynomial (Fin 5) ℂ :=
  aeval (fun i => ∑ j, C (A i j) * X j) P

theorem main :
    ∃ (G H : MvPolynomial (Fin 5) ℂ) (d : ℕ) (pt : Fin 3 → ℂ × ℂ),
      G.IsHomogeneous d ∧ H.IsHomogeneous d ∧
      (∀ a b : ℂ, a • G = b • H → a = 0 ∧ b = 0) ∧
      (∀ A : Matrix (Fin 5) (Fin 5) ℂ, IsUnit A.det →
        ¬ (4 ∉ (linSubst A G).vars ∧ 4 ∉ (linSubst A H).vars)) ∧
      (∀ i, pt i ≠ 0) ∧ (∀ i j, i ≠ j → (pt i).1 * (pt j).2 ≠ (pt j).1 * (pt i).2) ∧
      ∀ i, IsProdLinear (C (pt i).2 * G - C (pt i).1 * H) := by
  sorry

end OMA.S_mo_5041
