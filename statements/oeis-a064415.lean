import Mathlib

namespace OMA.S_oeis_a064415

def iterPhi : ℕ → ℕ
  | 0 => 0
  | 1 => 0
  | n + 2 => 1 + iterPhi (Nat.totient (n + 2))
termination_by n => n
decreasing_by
  exact Nat.totient_lt (n + 2) (by omega)

def a064415 (n : ℕ) : ℕ :=
  if n % 2 = 0 then iterPhi n else iterPhi n - 1

theorem main :
    (a064415 1 = 0 ∧ a064415 2 = 1) ∧
    (∀ m n : ℕ, 1 ≤ m → 1 ≤ n → a064415 (m * n) = a064415 m + a064415 n) ∧
    (∀ p : ℕ, Nat.Prime p → 3 ≤ p → a064415 p = 1 + a064415 ((p - 1) / 2)) ∧
    (∀ k : ℕ, a064415 (2 ^ k) = k ∧ a064415 (3 ^ k) = k) := by
  sorry

end OMA.S_oeis_a064415
