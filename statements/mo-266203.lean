import Mathlib

/-!
# Matrices with only two different entries and maximal determinant

Source: https://mathoverflow.net/questions/266203 (Wolfgang, CC BY-SA 3.0).
Credit: @connoranderson

A true entry is x, a false entry is 1. Absolute determinants implement the allowed
row swaps that normalize the leading sign. In every order with a Hadamard matrix
of order n+1, the normalized Hadamard cores are exactly the eventual maximizers,
and the second coefficient of the linear remainder is (n−1)/(n+1) times its first.
An explicit order-15 maximizer has no symmetric row/column rearrangement.
-/

namespace OMA.S_mo_266203
open Matrix
def border {n : ℕ} (u : ℝ) (N : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Unit ⊕ Fin n) (Unit ⊕ Fin n) ℝ :=
  Matrix.fromBlocks (fun _ _ => u) (fun _ _ => 1) (fun _ _ => 1) N
def signCore {n : ℕ} (a : Matrix (Fin n) (Fin n) Bool) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => if a i j then -1 else 1
def value {n : ℕ} (x : ℝ) (a : Matrix (Fin n) (Fin n) Bool) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => if a i j then x else 1
def extremalGram {n : ℕ} (a : Matrix (Fin n) (Fin n) Bool) : Prop :=
  let H := border 1 (signCore a)
  H*Hᵀ = ((n+1 : ℕ):ℝ) • 1
def symmetrizable {n : ℕ} (a : Matrix (Fin n) (Fin n) Bool) : Prop :=
  ∃ p q : Equiv.Perm (Fin n), ∀ i j, a (p i) (q j) = a (p j) (q i)
end OMA.S_mo_266203

namespace OMA.S_mo_266203
open Matrix Filter
theorem main :
    (∀ (n : ℕ), 0 < n → ∀ a : Matrix (Fin n) (Fin n) Bool, extremalGram a →
      (∀ x : ℝ, 1 < x → |(value x a).det| =
        |(border 1 (signCore a)).det|/2^n * (x-1)^(n-1) * (x+((n:ℝ)-1)/(n+1))) ∧
      ∀ᶠ x : ℝ in atTop, ∀ b : Matrix (Fin n) (Fin n) Bool,
        |(value x b).det| ≤ |(value x a).det| ∧
          (|(value x b).det| = |(value x a).det| ↔ extremalGram b)) ∧
    ∃ a : Matrix (Fin 15) (Fin 15) Bool, extremalGram a ∧ ¬ symmetrizable a ∧
      ∀ x : ℝ, 1 < x → |(value x a).det|=(x-1)^14*(131072*x+114688) := by
  sorry
end OMA.S_mo_266203
