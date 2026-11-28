import OMAStatements.S_oeis_a221018
import Mathlib

namespace A221018

private theorem rank_dvd (b d k : ℕ) (hb : 0 < b) (hdb : d ∣ Nat.fib b)
    (small : ∀ g : Fin (b + 1), (g : ℕ) ∣ b → d ∣ Nat.fib g → (g : ℕ) = b)
    (h : d ∣ Nat.fib k) : b ∣ k := by
  have h₁ : Nat.gcd b k ∣ b := Nat.gcd_dvd_left b k
  have h₂ : d ∣ Nat.fib (Nat.gcd b k) := by
    rw [Nat.fib_gcd]
    exact Nat.dvd_gcd hdb h
  have h₃ : Nat.gcd b k < b + 1 := Nat.lt_succ_of_le (Nat.gcd_le_left k hb)
  have e : Nat.gcd b k = b := small ⟨Nat.gcd b k, h₃⟩ h₁ h₂
  rw [← e]
  exact Nat.gcd_dvd_right b k

end A221018

theorem OMA.solution : type_of% @OMA.S_oeis_a221018.main := by
  rintro k ⟨hk, _, hplus, hminus⟩
  have transfer (p : ℕ) (h : p ∣ k + 1 ∨ p ∣ k - 1) : p ∣ Nat.fib k :=
    h.elim (fun hp => hp.trans hplus) (fun hp => hp.trans hminus)
  have even : 2 ∣ k := by
    by_contra h
    by_cases h₃ : 3 ∣ k
    · have h₄ : 4 ∣ k + 1 ∨ 4 ∣ k - 1 := by omega
      have h₆ := A221018.rank_dvd 6 4 k (by decide) (by decide) (by decide) (transfer 4 h₄)
      omega
    · have h₄ : 3 ∣ k + 1 ∨ 3 ∣ k - 1 := by
        have hr : k % 3 = 1 ∨ k % 3 = 2 := by omega
        rcases hr with hr | hr
        · exact Or.inr ⟨k / 3, by omega⟩
        · exact Or.inl ⟨k / 3 + 1, by omega⟩
      have h₆ := A221018.rank_dvd 4 3 k (by decide) (by decide) (by decide) (transfer 3 h₄)
      omega
  by_contra h
  have hr : k % 10 = 4 ∨ k % 10 = 6 := by omega
  have h₅ : 5 ∣ k + 1 ∨ 5 ∣ k - 1 := by
    rcases hr with hr | hr
    · exact Or.inl ⟨2 * (k / 10) + 1, by omega⟩
    · exact Or.inr ⟨2 * (k / 10) + 1, by omega⟩
  obtain ⟨q, hq⟩ :=
    A221018.rank_dvd 5 5 k (by decide) (by decide) (by decide) (transfer 5 h₅)
  omega