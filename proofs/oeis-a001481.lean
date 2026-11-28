import OMAStatements.S_oeis_a001481
import Mathlib.Tactic

open OMA.S_oeis_a001481 in
theorem OMA.solution : type_of% @OMA.S_oeis_a001481.main := by
  have sq4 : ∀ x : ℕ, x ^ 2 % 4 = 0 ∨ x ^ 2 % 4 = 1 := by
    intro x
    rcases Nat.even_or_odd x with ⟨r, hr⟩ | ⟨r, hr⟩ <;> subst hr <;> ring_nf <;> omega
  have odd_mod : ∀ n, SumTwoSquares n → n % 2 = 1 → n % 4 = 1 := by
    rintro n ⟨x, y, rfl⟩ h
    rcases sq4 x with hx | hx <;> rcases sq4 y with hy | hy <;> omega
  have half : ∀ n, SumTwoSquares n → n % 2 = 0 → SumTwoSquares (n / 2) := by
    rintro n ⟨x, y, rfl⟩ h
    unfold SumTwoSquares
    have hxy : x % 2 = y % 2 := by
      rcases Nat.even_or_odd x with ⟨r, rfl⟩ | ⟨r, rfl⟩ <;>
        rcases Nat.even_or_odd y with ⟨s, rfl⟩ | ⟨s, rfl⟩ <;> ring_nf at h ⊢ <;> omega
    rcases le_total y x with hle | hle
    · obtain ⟨d, rfl⟩ : ∃ d, x = y + 2 * d := ⟨(x - y) / 2, by omega⟩
      refine ⟨y + d, d, ?_⟩
      rw [show (y + 2 * d) ^ 2 + y ^ 2 = 2 * ((y + d) ^ 2 + d ^ 2) by ring,
        Nat.mul_div_cancel_left _ (by norm_num)]
    · obtain ⟨d, rfl⟩ : ∃ d, y = x + 2 * d := ⟨(y - x) / 2, by omega⟩
      refine ⟨x + d, d, ?_⟩
      rw [show x ^ 2 + (x + 2 * d) ^ 2 = 2 * ((x + d) ^ 2 + d ^ 2) by ring,
        Nat.mul_div_cancel_left _ (by norm_num)]
  have key : ∀ k a b, a ≠ b → SumTwoSquares a → SumTwoSquares b → a + b = 2 ^ (k + 1) →
      a = 0 ∨ b = 0 := by
    intro k
    induction k with
    | zero =>
      intro a b hab _ _ h
      norm_num at h
      omega
    | succ k ih =>
      intro a b hab ha hb h
      have h4 : 4 ∣ 2 ^ (k + 1 + 1) := ⟨2 ^ k, by ring⟩
      have h2 : 2 ^ (k + 1 + 1) = 2 * 2 ^ (k + 1) := by ring
      by_cases ha2 : a % 2 = 1 <;> by_cases hb2 : b % 2 = 1
      · have := odd_mod a ha ha2
        have := odd_mod b hb hb2
        omega
      · omega
      · omega
      · have := ih (a / 2) (b / 2) (by omega) (half a ha (by omega)) (half b hb (by omega))
          (by omega)
        omega
  intro a b k hk hab ha hb h
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  exact key j a b hab ha hb h
