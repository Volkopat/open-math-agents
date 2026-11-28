import Mathlib

/-!
# GCD determinants for Lucas sequences and Jordan totients

Source: T. Amdeberhan, https://mathoverflow.net/questions/309133 (CC BY-SA 4.0).
Credit: @connoranderson. The divisor-incidence factorization is the Smith
determinant argument. Darij Grinberg and Max Alekseyev identified its
application to the first equality in the source discussion.

We take the parameters to be positive as clarified in the question. The
Lucas factorial is the product of the first n positive-index Lucas terms.
The Möbius expression equals the determinant. The proposed prime-product
expression is strictly smaller at n=3 for every admissible parameter choice.
-/
namespace OMA.S_mo_309133
open Finset Matrix

def lucas (s t : ℕ) : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n+2 => s*lucas s t (n+1) + t*lucas s t n

def entries (n s t ℓ : ℕ) : Matrix (Fin n) (Fin n) ℚ :=
  fun i j => (Nat.gcd (lucas s t (i.val+1)) (lucas s t (j.val+1)) : ℚ)^ℓ

noncomputable def jordan (s t ℓ k : ℕ) : ℚ :=
  ∑ d ∈ k.divisors, (lucas s t d : ℚ)^ℓ * (ArithmeticFunction.moebius (k/d) : ℤ)

noncomputable def primeProduct (n s t ℓ : ℕ) : ℚ :=
  (∏ i : Fin n, (lucas s t (i.val+1) : ℚ))^ℓ *
    ∏ i : Fin n, ∏ p ∈ (i.val+1).primeFactors, (1-1/(p:ℚ)^ℓ)

theorem main : ∀ (s t ℓ : ℕ), 0 < s → 0 < t → 0 < ℓ → s ≠ 1 → s.Coprime t →
    (∀ n : ℕ, 0 < n → (entries n s t ℓ).det = ∏ i : Fin n, jordan s t ℓ (i.val+1)) ∧
    primeProduct 3 s t ℓ < (entries 3 s t ℓ).det := by
  sorry
end OMA.S_mo_309133
