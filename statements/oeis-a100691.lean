import Mathlib

/-!
# A100691 versus A193641

For the triangular strip Z × {0,1}, A100691 gives the independent exact
recurrence for the walk count below. It is also obtained from the entry's
generating function (1+z²)(1+z+z²)/((1-z)(1-2z-z³)).
For A193641 we count words directly. A zero covers itself. Each nonzero
letter must have its opposite immediately to the left or right. If the last
letter still needs a partner, the next letter must supply it.
Starting with a fictitious zero places no restriction on the first letter.

Source: https://oeis.org/A100691 and https://oeis.org/A193641
Conjecture: R. J. Mathar, July 22, 2022.
Formalization: @KoaOkano
-/

namespace OMA.S_oeis_a100691

def walks : ℕ → ℕ
  | 0 => 1
  | 1 => 4
  | 2 => 12
  | 3 => 30
  | n+4 => 2*walks (n+3) + walks (n+1) + 6

def tails : ℕ → ℤ → Bool → ℕ
  | 0, _, pending => if pending then 0 else 1
  | n+1, last, pending =>
    (([-1,0,1] : List ℤ).map fun x =>
      if pending = true ∧ last + x ≠ 0 then 0
      else tails n x (decide (x ≠ 0 ∧ last + x ≠ 0))).sum

def words (n : ℕ) : ℕ := tails n 0 false

theorem main : ∀ m : ℕ, walks (m+1) + 3 = words (m+3) := by
  sorry

end OMA.S_oeis_a100691
