import Mathlib

/-!
# Counting integral multipliers with all singular values in a fixed annulus

Source: MichaelGaudreau, https://mathoverflow.net/questions/339727 (CC BY-SA 4.0).
Credit: @connoranderson.

For an integral basis b, regular b a is the real matrix of multiplication
by a in that basis. Its squared singular values are the eigenvalues of its
transpose times itself. For positive R, shell b R therefore consists exactly
of the elements for which every singular value belongs to (R,2R].

The count is bounded above and below by positive constant multiples of R^n;
the constants may depend on the basis. The result holds for every finite free positive-rank
commutative ring over the integers and in particular for the ring of integers
of a number field with its given integral basis.
-/
namespace OMA.S_mo_339727
open Matrix Filter
abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℝ
noncomputable def regular {O : Type*} [CommRing O] {n : ℕ} (b : Module.Basis (Fin n) ℤ O)
    (a : O) : Mat n := (Algebra.leftMulMatrix b a).map (Int.castRingHom ℝ)
def shell {O : Type*} [CommRing O] {n : ℕ} (b : Module.Basis (Fin n) ℤ O) (R : ℝ) : Set O :=
  {a | ∀ z ∈ spectrum ℝ ((regular b a)ᵀ * regular b a), R^2 < z ∧ z ≤ (2*R)^2}

theorem main : ∀ (O : Type*) [CommRing O] (n : ℕ) (b : Module.Basis (Fin n) ℤ O), 0 < n →
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ᶠ R : ℝ in atTop, (shell b R).Finite ∧
      c*R^n ≤ ((shell b R).ncard:ℝ) ∧ ((shell b R).ncard:ℝ) ≤ C*R^n := by
  sorry
end OMA.S_mo_339727
