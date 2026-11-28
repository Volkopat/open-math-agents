import Mathlib

/-!
# Positivity of the prime-base transform in MathOverflow 409517

Source: https://mathoverflow.net/questions/409517
Credit: @Mapika

The author explicitly asks for a proof of either of two conjectures. This
statement formalizes the first conjecture for every prime and every index.
The second conjecture, concerning composite bases, is a separate question.
The product unfolds the source recurrence for a by peeling digits from the
least significant end. Parity of the integer difference gives the signed factor.
-/

namespace OMA.S_mo_409517
open Finset

def weight (p n : ℕ) := (p.digits n).sum

def digitProduct : List ℕ → ℤ
  | [] => 1
  | i :: xs => (1 + (i + xs.sum : ℕ)) * digitProduct xs

def a (p n : ℕ) := digitProduct (p.digits n)

/-- The exponent of -1 is the signed integer difference of digit sums. -/
def b (p n : ℕ) : ℤ := ∑ k ∈ range (n+1),
  if p ∣ n.choose k then 0 else
    (if Even ((weight p n : ℤ) - weight p k) then 1 else -1) * a p k

theorem main : ∀ (p n : ℕ), p.Prime → 0 < b p n := by
  sorry

end OMA.S_mo_409517
