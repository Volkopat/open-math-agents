import Mathlib

/-!
# Reversed A373183 rows and unsigned Stirling numbers

Source: Mikhail Kurkov, https://mathoverflow.net/questions/473119
Credit: @connoranderson.

For a positive row index, removing its highest power of two removes the
leading binary one. The first zero-run then has length log₂(n) if no
bits remain, and log₂(n)−log₂(remainder)−1 otherwise. This is precisely
the source's convention that the logarithm of zero in the gap formula is −1.
-/
namespace OMA.S_mo_473119
open Polynomial

def remHigh (n : ℕ) : ℕ := n - 2^n.log2

def gap (n : ℕ) : ℕ :=
  if remHigh n=0 then n.log2 else n.log2 - (remHigh n).log2 - 1

/-- Zero-run lengths after successive one bits, listed from the least significant end. -/
def runs (n : ℕ) : List ℕ :=
  if n=0 then [] else runs (remHigh n) ++ [gap n]
termination_by n
decreasing_by
  unfold remHigh
  exact Nat.sub_lt (by omega) (by positivity)

def reverseEntry : List ℕ → ℕ → ℕ → ℤ
  | [],m,k => if 0 < k ∧ k ≤ m then Nat.stirlingFirst m (m-k+1) else 0
  | f::r,m,k => if k=0 then 0 else
      (m+1:ℤ)^f * reverseEntry r (m+1) k - (m:ℤ)^(f+1) * reverseEntry r m (k-1)

def b (n m k : ℕ) : ℤ := reverseEntry (runs n).reverse m k

noncomputable def row : ℕ → ℤ[X] :=
  Nat.binaryRec (motive := fun _ => ℤ[X]) X
    (fun d _ P => if d then X*P else X*(P.comp (X+1)-P))

theorem main : ∀ (n k : ℕ), 0 < k → k ≤ n.bits.count true + 1 →
    (row n).coeff k = b n 1 (n.bits.count true+2-k) := by
  sorry
end OMA.S_mo_473119
