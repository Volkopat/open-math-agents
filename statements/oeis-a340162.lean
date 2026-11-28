import Mathlib

/-!
# The greedy sequence of binary weight three (OEIS A340162)

The first term is 7. Each subsequent term is the least unused number with
three set bits whose product with the preceding term also has three set bits.
The value at index zero is set to zero for coefficient extraction.
Source: https://oeis.org/A340162
Credit: Robert Leshner (@rleshner)
-/
namespace OMA.S_oeis_a340162

def allowed (p x : ℕ) : Prop :=
  x.bitIndices.length = 3 ∧ (p*x).bitIndices.length = 3

noncomputable def step (s : Set ℕ × ℕ) : Set ℕ × ℕ :=
  let x := sInf {x : ℕ | x ∉ s.1 ∧ allowed s.2 x}
  (insert x s.1, x)

noncomputable def state : ℕ → Set ℕ × ℕ
  | 0 => ({7}, 7)
  | n+1 => step (state n)

noncomputable def a : ℕ → ℕ
  | 0 => 0
  | n+1 => (state n).2

/-- The coefficients of the numerator of Wu's conjectured generating function. -/
def numerator : ℕ → ℤ
  | 1 => 7 | 2 => 14 | 3 => 5 | 5 => -15 | 6 => -28 | 7 => -46 | _ => 0

/-- Coefficient identity for (1-2x²)(1-2x⁴) times the ordinary generating
function. For n > 7 it is exactly the conjectured homogeneous recurrence. -/
theorem main : ∀ n : ℕ, (a n : ℤ) - 2*(a (n-2) : ℤ) - 2*(a (n-4) : ℤ)
    + 4*(a (n-6) : ℤ) = numerator n := by
  sorry

end OMA.S_oeis_a340162
