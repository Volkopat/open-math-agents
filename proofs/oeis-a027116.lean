import OMAStatements.S_oeis_a027116
import Mathlib

/-!
Column k of the triangle only depends on columns k-3, k-2, k-1 of the row above, so for n >= 1
and k <= n+1 the entry T(n,k) is the tribonacci number t(k) (t = 1, 1, 2, 4, 7, ...).
Hence the diagonals D2(n) = T(n,n+2) and a(n) = T(n,n+3) satisfy, for n large enough,
D2(n+1) = t(n) + t(n+1) + D2(n) and a(n+1) = t(n+1) + D2(n) + a(n). Eliminating D2 with the
tribonacci recurrence gives a(n) = 3a(n-1) - 2a(n-2) - a(n-4) + a(n-5).
-/

namespace R027116
open OMA.S_oeis_a027116

/-- Tribonacci numbers 1, 1, 2, 4, 7, 13, ... -/
def t : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | 2 => 2
  | n + 3 => t n + t (n + 1) + t (n + 2)

/-- The diagonal `T(n, n+2)`. -/
def D (n : ℕ) : ℕ := T n (n + 2)

theorem t3 (j : ℕ) : t (j + 3) = t j + t (j + 1) + t (j + 2) := rfl

theorem T_mid (n k : ℕ) (h3 : 3 ≤ k) (hk : k ≤ 2 * n + 1) :
    T (n + 1) k = T n (k - 3) + T n (k - 2) + T n (k - 1) := by
  have c0 : ¬ (k = 0) := by omega
  have c1 : ¬ (k = 1) := by omega
  have c2 : ¬ (k = 2) := by omega
  have c3 : k ≤ 2 * (n + 1) - 1 := by omega
  rw [T, if_neg c0, if_neg c1, if_neg c2, if_pos c3]

theorem L1 (n : ℕ) (hn : 1 ≤ n) (k : ℕ) (hk : k ≤ n + 1) : T n k = t k := by
  induction n generalizing k with
  | zero => omega
  | succ n ih =>
    rcases Nat.lt_or_ge k 3 with h | h
    · interval_cases k <;> simp [T, t]
    · obtain ⟨j, rfl⟩ : ∃ j, k = j + 3 := ⟨k - 3, by omega⟩
      rcases Nat.eq_zero_or_pos n with h0 | hn1
      · omega
      · rw [T_mid n (j + 3) (by omega) (by omega), show j + 3 - 3 = j by omega,
          show j + 3 - 2 = j + 1 by omega, show j + 3 - 1 = j + 2 by omega,
          ih hn1 j (by omega), ih hn1 (j + 1) (by omega), ih hn1 (j + 2) (by omega), t3]

theorem L2 (n : ℕ) (hn : 2 ≤ n) : D (n + 1) = t n + t (n + 1) + D n := by
  show T (n + 1) (n + 1 + 2) = t n + t (n + 1) + T n (n + 2)
  rw [T_mid n (n + 1 + 2) (by omega) (by omega), show n + 1 + 2 - 3 = n by omega,
    show n + 1 + 2 - 2 = n + 1 by omega, show n + 1 + 2 - 1 = n + 2 by omega,
    L1 n (by omega) n (by omega), L1 n (by omega) (n + 1) (by omega)]

theorem L3 (n : ℕ) (hn : 3 ≤ n) : a (n + 1) = t (n + 1) + D n + a n := by
  show T (n + 1) (n + 1 + 3) = t (n + 1) + T n (n + 2) + T n (n + 3)
  rw [T_mid n (n + 1 + 3) (by omega) (by omega), show n + 1 + 3 - 3 = n + 1 by omega,
    show n + 1 + 3 - 2 = n + 2 by omega, show n + 1 + 3 - 1 = n + 3 by omega,
    L1 n (by omega) (n + 1) (by omega)]

theorem solve : ∀ n : ℕ, 8 ≤ n →
    (a n : ℤ) = 3 * a (n - 1) - 2 * a (n - 2) - a (n - 4) + a (n - 5) := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 8 := ⟨n - 8, by omega⟩
  rw [show m + 8 - 1 = m + 7 by omega, show m + 8 - 2 = m + 6 by omega,
    show m + 8 - 4 = m + 4 by omega, show m + 8 - 5 = m + 3 by omega]
  have A8 : a (m + 8) = t (m + 8) + D (m + 7) + a (m + 7) := L3 (m + 7) (by omega)
  have A7 : a (m + 7) = t (m + 7) + D (m + 6) + a (m + 6) := L3 (m + 6) (by omega)
  have A4 : a (m + 4) = t (m + 4) + D (m + 3) + a (m + 3) := L3 (m + 3) (by omega)
  have D7 : D (m + 7) = t (m + 6) + t (m + 7) + D (m + 6) := L2 (m + 6) (by omega)
  have D6 : D (m + 6) = t (m + 5) + t (m + 6) + D (m + 5) := L2 (m + 5) (by omega)
  have D5 : D (m + 5) = t (m + 4) + t (m + 5) + D (m + 4) := L2 (m + 4) (by omega)
  have D4 : D (m + 4) = t (m + 3) + t (m + 4) + D (m + 3) := L2 (m + 3) (by omega)
  have T8 : t (m + 8) = t (m + 5) + t (m + 6) + t (m + 7) := t3 (m + 5)
  have T6 : t (m + 6) = t (m + 3) + t (m + 4) + t (m + 5) := t3 (m + 3)
  omega

end R027116

theorem OMA.solution : type_of% @OMA.S_oeis_a027116.main := R027116.solve
