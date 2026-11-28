import OMAStatements.S_oeis_a093348
import Mathlib
open OMA.S_oeis_a093348

def Pa093348.G (m N : ℕ) : ℕ := ∑ k ∈ Finset.range N, 4 * 5 ^ k * ((m / 5 ^ (k + 1)) % 2)

theorem Pa093348.G_stable (m N M : ℕ) (hm : m < 5 ^ (N + 1)) (hNM : N ≤ M) :
    Pa093348.G m M = Pa093348.G m N := by
  induction M, hNM using Nat.le_induction with
  | base => rfl
  | succ M hNM ih =>
    unfold Pa093348.G at ih ⊢
    rw [Finset.sum_range_succ, ih]
    have h1 : 5 ^ (N + 1) ≤ 5 ^ (M + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have : m / 5 ^ (M + 1) = 0 := Nat.div_eq_of_lt (by omega)
    simp [this]

theorem Pa093348.flip (m' j k : ℕ) (hk : k < j) :
    (m' + 5 ^ j) / 5 ^ (k + 1) % 2 + m' / 5 ^ (k + 1) % 2 = 1 := by
  have hp : 5 ^ j = 5 ^ (k + 1) * 5 ^ (j - (k + 1)) := by
    rw [← pow_add]; congr 1; omega
  have hodd : Odd (5 ^ (j - (k + 1))) := Odd.pow (by decide)
  rw [hp, Nat.add_mul_div_left _ _ (by positivity)]
  have := Nat.odd_iff.mp hodd
  omega

theorem Pa093348.geom (j : ℕ) : ∑ k ∈ Finset.range j, 4 * 5 ^ k + 1 = 5 ^ j := by
  induction j with
  | zero => simp
  | succ j ih => rw [Finset.sum_range_succ, pow_succ]; omega

theorem Pa093348.key (m' j : ℕ) :
    Pa093348.G (m' + 5 ^ j) j + Pa093348.G m' j + 1 = 5 ^ j := by
  unfold Pa093348.G
  rw [← Finset.sum_add_distrib]
  conv_rhs => rw [← Pa093348.geom j]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mem_range] at hk
  have := Pa093348.flip m' j k hk
  rw [← mul_add, this, mul_one]

theorem Pa093348.unfold (n : ℕ) (hn : 1 ≤ n) :
    a (n + 1) = 5 ^ Nat.log 5 n - a (n - 5 ^ Nat.log 5 n + 1) := by
  rw [a, dif_neg (by omega), show n + 1 - 1 = n by omega]
  congr 2
  have := Nat.pow_log_le_self 5 (show n ≠ 0 by omega)
  omega

theorem OMA.solution : type_of% @OMA.S_oeis_a093348.main := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0
      rw [a, dif_pos (by norm_num)]
      simp
    · set j := Nat.log 5 n with hj
      have hle : 5 ^ j ≤ n := Nat.pow_log_le_self 5 (by omega)
      have hlt : n < 5 ^ (j + 1) := Nat.lt_pow_succ_log_self (by norm_num) n
      have hjn : j ≤ n := le_trans (Nat.lt_pow_self (by norm_num : 1 < 5)).le hle
      obtain ⟨m', hm'⟩ : ∃ m', n = m' + 5 ^ j := ⟨n - 5 ^ j, by omega⟩
      have hm'lt : m' < n := by have := Nat.one_le_pow j 5 (by norm_num); omega
      rw [Pa093348.unfold n hpos, ← hj, show n - 5 ^ j = m' by omega, ih m' hm'lt]
      have e1 : Pa093348.G n (n + 1) = Pa093348.G n j :=
        Pa093348.G_stable n j (n + 1) hlt (by omega)
      have e2 : Pa093348.G m' (m' + 1) = Pa093348.G m' j := by
        rcases le_total j (m' + 1) with h | h
        · exact Pa093348.G_stable m' j (m' + 1) (by omega) h
        · have h5 : m' < 5 ^ (m' + 1 + 1) := by
            have := Nat.lt_pow_self (show 1 < 5 by norm_num) (n := m' + 1 + 1); omega
          exact (Pa093348.G_stable m' (m' + 1) j h5 h).symm
      have hk := Pa093348.key m' j
      have hpar : n % 2 + m' % 2 = 1 := by
        have hodd : Odd (5 ^ j) := Odd.pow (by decide)
        have := Nat.odd_iff.mp hodd
        omega
      change 5 ^ j - ((m' % 2 + Pa093348.G m' (m' + 1) : ℕ) : ℤ) =
        ((n % 2 + Pa093348.G n (n + 1) : ℕ) : ℤ)
      rw [e1, e2, ← hm'] at *
      rw [← hm'] at hk
      have : (n % 2 + Pa093348.G n j) + (m' % 2 + Pa093348.G m' j) = 5 ^ j := by omega
      have h' : ((n % 2 + Pa093348.G n j : ℕ) : ℤ) + ((m' % 2 + Pa093348.G m' j : ℕ) : ℤ)
          = (5 : ℤ) ^ j := by exact_mod_cast this
      linarith
