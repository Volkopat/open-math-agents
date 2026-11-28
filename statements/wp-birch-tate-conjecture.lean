import Mathlib

/-!
# Birch–Tate conjecture

Source: https://en.wikipedia.org/wiki/Birch%E2%80%93Tate_conjecture
Credit: @VestigeClub

The stable Steinberg presentation and its center are described in Weibel,
The K-book, III.5.1–5.2.1. The Birch–Tate formula is VI.8.6.
-/

namespace OMA.S_wp_birch_tate_conjecture

open scoped commutatorElement

/-- The stable elementary generators use off-diagonal pairs of natural numbers. -/
structure Generator (R : Type*) where
  row : ℕ
  col : ℕ
  different : row ≠ col
  entry : R

def x {R : Type*} (i j : ℕ) (h : i ≠ j) (a : R) : FreeGroup (Generator R) :=
  FreeGroup.of ⟨i, j, h, a⟩

/-- Additivity in a root subgroup, commutation of unrelated roots, and the
Steinberg commutator for three distinct indices. -/
def steinbergRelators (R : Type*) [Ring R] : Set (FreeGroup (Generator R)) :=
  { w |
    (∃ (i j : ℕ) (h : i ≠ j) (a b : R),
      w = x i j h a * x i j h b * (x i j h (a + b))⁻¹) ∨
    (∃ (i j k l : ℕ) (hij : i ≠ j) (hkl : k ≠ l) (a b : R),
      i ≠ l ∧ j ≠ k ∧ w = ⁅x i j hij a, x k l hkl b⁆) ∨
    (∃ (i j k : ℕ) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (a b : R),
      w = ⁅x i j hij a, x j k hjk b⁆ * (x i k hik (a * b))⁻¹) }

/-- The underlying type of the center of the stable Steinberg group. -/
abbrev KTwo (R : Type*) [Ring R] := ↥(Subgroup.center (PresentedGroup (steinbergRelators R)))

/-- The positive levels for which the cyclotomic Galois group has exponent
dividing two. A finite group of exponent dividing two is elementary abelian. -/
def cyclotomicLevels (F : Type*) [Field F] : Set ℕ+ :=
  { n | ∀ σ : CyclotomicField (n : ℕ) F ≃ₐ[F] CyclotomicField (n : ℕ) F, σ ^ 2 = 1 }

/-- The special value of the holomorphic continuation off the pole at 1.
Mathlib's Dirichlet series specifies the function on its half-plane of convergence. -/
def IsDedekindValueAtMinusOne (F : Type*) [Field F] [NumberField F] (z : ℂ) : Prop :=
  ∃ Z : ℂ → ℂ, DifferentiableOn ℂ Z ({1} : Set ℂ)ᶜ ∧
    (∀ s : ℂ, 1 < s.re → Z s = NumberField.dedekindZeta F s) ∧ Z (-1) = z

theorem main : ∀ (F : Type*) [Field F] [NumberField F] [NumberField.IsTotallyReal F],
    ∃ (N : ℕ+) (z : ℂ), IsGreatest (cyclotomicLevels F) N ∧
      IsDedekindValueAtMinusOne F z ∧ Finite (KTwo (NumberField.RingOfIntegers F)) ∧
      (Nat.card (KTwo (NumberField.RingOfIntegers F)) : ℝ) = ‖((N : ℕ) : ℂ) * z‖ := by
  sorry

end OMA.S_wp_birch_tate_conjecture
