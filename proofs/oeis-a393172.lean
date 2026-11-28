import OMAStatements.S_oeis_a393172
import Mathlib

/-!
Strong induction modulo 4: for m ≥ 2, a(m) ≡ 2 if m is a power of 2 and a(m) ≡ 0 otherwise.
In the recurrence for a(n + 2) with n ≥ 1, the convolution is 2·a(1)·a(n + 1) plus products of
two even terms, hence 0 mod 4. In the binomial sum, the k = 0 term vanishes, the terms with
k + 1 not a power of 2 vanish, and a term with k + 1 = 2^j is 2·C(2^j, n + 1 - k) mod 4, where the
binomial is odd only for n + 1 - k = 2^j (Lucas), that is n + 2 = 2^(j+1). So the sum is 2 exactly
when n + 2 is a power of 2.
-/

namespace R393172
open OMA.S_oeis_a393172

theorem a_rec (n : ℕ) : a (n + 2) =
    (∑ j : Fin (n + 1), a (j.1 + 1) * a (n + 1 - j.1)) -
      ∑ k : Fin (n + 1),
        (-1 : ℤ) ^ (n + 1 - k.1) * (Nat.choose (k.1 + 1) (n + 1 - k.1) : ℤ) * a (k.1 + 1) := by
  rw [a]

theorem a_one : a 1 = 1 := by rw [a]

theorem hneg (e : ℕ) : (-1 : ZMod 4) ^ e * 2 = 2 := by
  rcases neg_one_pow_eq_or (ZMod 4) e with h | h <;> rw [h] <;> decide

open Classical in
theorem key : ∀ m, 2 ≤ m → (a m : ZMod 4) = if ∃ k : ℕ, m = 2 ^ k then 2 else 0 := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro hm
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 2 := ⟨m - 2, by omega⟩
  have hev : ∀ i, 2 ≤ i → i < n + 2 → 2 * (a i : ZMod 4) = 0 := by
    intro i hi hlt
    rw [ih i hlt hi]
    split_ifs <;> decide
  have hsq : ∀ i i', 2 ≤ i → i < n + 2 → 2 ≤ i' → i' < n + 2 →
      (a i : ZMod 4) * (a i' : ZMod 4) = 0 := by
    intro i i' hi hlt hi' hlt'
    rw [ih i hlt hi, ih i' hlt' hi']
    split_ifs <;> decide
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have h2 : a 2 = 2 := by
      simpa [a_one, Fin.sum_univ_succ, Fin.sum_univ_zero] using a_rec 0
    rw [if_pos ⟨1, rfl⟩]
    show ((a 2 : ℤ) : ZMod 4) = 2
    rw [h2]
    norm_num
  have h : (a (n + 2) : ZMod 4) =
      (∑ j : Fin (n + 1), (a (j.1 + 1) : ZMod 4) * (a (n + 1 - j.1) : ZMod 4)) -
        ∑ k : Fin (n + 1), (-1 : ZMod 4) ^ (n + 1 - k.1) *
          ((Nat.choose (k.1 + 1) (n + 1 - k.1) : ℕ) : ZMod 4) * (a (k.1 + 1) : ZMod 4) := by
    rw [a_rec n]
    push_cast
    try ring
  have hconv : ∑ j : Fin (n + 1), (a (j.1 + 1) : ZMod 4) * (a (n + 1 - j.1) : ZMod 4) = 0 := by
    rw [Fintype.sum_eq_add (0 : Fin (n + 1)) (Fin.last n)]
    · simp only [Fin.val_zero, Fin.val_last, Nat.sub_zero, Nat.zero_add, Nat.add_sub_cancel_left,
        a_one, Int.cast_one, one_mul, mul_one]
      rw [← two_mul]
      exact hev (n + 1) (by omega) (by omega)
    · intro h0
      have := congrArg Fin.val h0
      simp only [Fin.val_zero, Fin.val_last] at this
      omega
    · rintro c ⟨hc0, hcl⟩
      have h1 : c.1 ≠ 0 := fun h' => hc0 (Fin.ext (by simp [h']))
      have h2 : c.1 ≠ n := fun h' => hcl (Fin.ext (by simp [h']))
      have h3 := c.2
      exact hsq _ _ (by omega) (by omega) (by omega) (by omega)
  have term_zero : ∀ k : Fin (n + 1), ¬ (2 * (k.1 + 1) = n + 2 ∧ ∃ j, k.1 + 1 = 2 ^ j) →
      (-1 : ZMod 4) ^ (n + 1 - k.1) * ((Nat.choose (k.1 + 1) (n + 1 - k.1) : ℕ) : ZMod 4) *
        (a (k.1 + 1) : ZMod 4) = 0 := by
    intro k hk
    have hk2 := k.2
    rcases Nat.eq_zero_or_pos k.1 with h0 | h0
    · rw [h0, Nat.choose_eq_zero_of_lt (by omega : 0 + 1 < n + 1 - 0)]
      simp
    · rw [ih (k.1 + 1) (by omega) (by omega)]
      split_ifs with hp
      · obtain ⟨j, hj⟩ := hp
        have hne : n + 1 - k.1 ≠ 2 ^ j := fun h' => hk ⟨by omega, j, hj⟩
        obtain ⟨c, hc⟩ : 2 ∣ Nat.choose (k.1 + 1) (n + 1 - k.1) := by
          rw [hj]
          exact Nat.Prime.dvd_choose_pow Nat.prime_two (by omega) hne
        rw [hc]
        have h4 : (2 : ZMod 4) * 2 = 0 := by decide
        calc (-1 : ZMod 4) ^ (n + 1 - k.1) * ((2 * c : ℕ) : ZMod 4) * 2
            = (-1) ^ (n + 1 - k.1) * c * (2 * 2) := by push_cast; ring
          _ = 0 := by rw [h4, mul_zero]
      · simp
  rw [h, hconv, zero_sub]
  split_ifs with hP
  · obtain ⟨e, he⟩ := hP
    have he0 : e ≠ 0 := by
      rintro rfl
      rw [pow_zero] at he
      omega
    obtain ⟨i, rfl⟩ : ∃ i, e = i + 1 := ⟨e - 1, by omega⟩
    have h2i : 2 ^ (i + 1) = 2 ^ i * 2 := pow_succ 2 i
    have hi : 1 ≤ i := by
      rcases Nat.eq_zero_or_pos i with rfl | hi
      · norm_num at he
        omega
      · exact hi
    have hpos : 2 ≤ 2 ^ i := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) hi
    rw [Finset.sum_eq_single (⟨2 ^ i - 1, by omega⟩ : Fin (n + 1))]
    · show -((-1 : ZMod 4) ^ (n + 1 - (2 ^ i - 1)) *
          ((Nat.choose (2 ^ i - 1 + 1) (n + 1 - (2 ^ i - 1)) : ℕ) : ZMod 4) *
          (a (2 ^ i - 1 + 1) : ZMod 4)) = 2
      rw [show 2 ^ i - 1 + 1 = 2 ^ i by omega, show n + 1 - (2 ^ i - 1) = 2 ^ i by omega,
        Nat.choose_self, ih (2 ^ i) (by omega) hpos, if_pos ⟨i, rfl⟩, Nat.cast_one, mul_one, hneg]
      decide
    · intro b _ hb
      exact term_zero b (fun ⟨h1, j, hj⟩ => hb (Fin.ext (by show b.1 = 2 ^ i - 1; omega)))
    · exact fun h' => absurd (Finset.mem_univ _) h'
  · rw [Finset.sum_eq_zero (fun k _ => term_zero k
      (fun ⟨h1, j, hj⟩ => hP ⟨j + 1, by rw [pow_succ]; omega⟩)), neg_zero]

end R393172

theorem OMA.solution : type_of% @OMA.S_oeis_a393172.main := by
  intro n hn
  have hk := R393172.key n hn
  refine ⟨fun hp => ?_, fun hp => ?_⟩
  · rw [if_pos hp] at hk
    have := (ZMod.intCast_eq_intCast_iff (OMA.S_oeis_a393172.a n) 2 4).mp (by push_cast; exact hk)
    exact_mod_cast this
  · rw [if_neg hp] at hk
    have := (ZMod.intCast_eq_intCast_iff (OMA.S_oeis_a393172.a n) 0 4).mp (by push_cast; exact hk)
    exact_mod_cast this
