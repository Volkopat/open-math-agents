import Mathlib

/-!
# A circular matrix of consecutive products

Source: lntk, https://mathoverflow.net/questions/467005 (CC BY-SA 4.0).
Fred Hucht gave the determinant and Vladimir Dotsenko suggested row subtraction.
Credit: @connoranderson.

The size is `n+1`, and the empty walk on the diagonal has product one.
The weighted cyclic shift gives a two-term formula for the inverse.
-/

namespace OMA.S_mo_467005
open scoped Fin.NatCast

def path {R : Type*} [CommRing R] {n : ℕ} (x : Fin (n+1) → R) (i : Fin (n+1))
    (k : ℕ) : R := ∏ t ∈ Finset.range k, x (i + (t : Fin (n+1)))

def circular {R : Type*} [CommRing R] {n : ℕ} (x : Fin (n+1) → R) :
    Matrix (Fin (n+1)) (Fin (n+1)) R := Matrix.of fun i j => path x i (j-i).val

def shift {R : Type*} [CommRing R] {n : ℕ} (x : Fin (n+1) → R) :
    Matrix (Fin (n+1)) (Fin (n+1)) R := Matrix.of fun i j => if i+1=j then x i else 0

theorem main : ∀ (n : ℕ) (x : Fin (n+1) → ℝ), (∀ i, x i ∈ Set.Icc (0:ℝ) 1) →
    (circular x).det = (1-∏ i, x i)^n ∧
    ((∏ i, x i) ≠ 1 → (circular x)⁻¹ = (1-∏ i, x i)⁻¹ • (1-shift x)) := by
  sorry
end OMA.S_mo_467005
