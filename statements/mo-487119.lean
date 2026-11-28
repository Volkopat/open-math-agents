import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Prime.Defs

/-! Source: https://mathoverflow.net/questions/487119 -/

namespace OMA.S_mo_487119

/-- The final second coordinate after simultaneous updates from 1 through n - 1. -/
def finalB (n : ℕ) : ℕ :=
  ((List.range (n - 1)).foldl
    (fun s j =>
      let i := j + 1
      (s.1 + Nat.gcd (s.1 + s.2) (s.1 - n + i),
       s.2 + Nat.gcd (s.1 + n - i) (s.2 + i - 1)))
    (n, 1)).2

theorem main :
    ∀ k : ℕ, k % 2 = 1 →
      ((k.Prime ∧ (2 * k - 1).Prime ∧ (3 * k - 2).Prime) ↔
        k ≠ 1 ∧ k ≠ 5 ∧ finalB k = k) := by
  sorry

end OMA.S_mo_487119
