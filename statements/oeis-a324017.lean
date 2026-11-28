import Mathlib.Data.Nat.ModEq

/-!
# Three tetration assertions in A324017

Source: https://oeis.org/A324017
Credit: @blakestone-x

Tetration is a right-associated tower, with height zero giving one. The
array uses least nonnegative residues. Both array indices start at one.
-/

namespace OMA.S_oeis_a324017

def tower (b : ℕ) : ℕ → ℕ
  | 0 => 1
  | h+1 => b ^ tower b h

def a (m n : ℕ) : ℕ := tower (2*n-1) m % (2*n)^m

theorem main : (∀ m n k : ℕ, 1 < m → 1 < n → 1 < k →
      tower (2*n-1) m ≡ k [MOD (2*n)^m] → (2*n-1)^k ≡ k [MOD (2*n)^m]) ∧
    (∀ m n : ℕ, 1 < n → 2 ≤ m →
      tower (2*n-1) m / (2*n) ≡ 2*(n-1) [MOD 2*n]) ∧
    (∀ m n j : ℕ, 1 < m → 0 < n →
      tower (2*n-1) m ≡ j [MOD (2*n)^(m+1)] → a (m+1) n = j) := by
  sorry

end OMA.S_oeis_a324017
