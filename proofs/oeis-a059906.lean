import OMAStatements.S_oeis_a059906
import Mathlib

namespace OMA.A059906Proof

open OMA.S_oeis_a059906

def c (k : ℕ) : ℤ := (-1 : ℤ) ^ k * 2 ^ (k / 2)

def H (n : ℕ) : ℤ := ∑ k ∈ Finset.Icc 1 n, c k * ((n / 2 ^ k : ℕ) : ℤ)

def E (v : ℕ) : ℤ := if v % 2 = 0 then 2 ^ (v / 2) else 0

theorem c_odd (i : ℕ) : c (2 * i + 1) = -2 ^ i := by
  unfold c
  rw [Odd.neg_one_pow ⟨i, rfl⟩, show (2 * i + 1) / 2 = i by omega]
  ring

theorem c_even (i : ℕ) : c (2 * i + 2) = 2 ^ (i + 1) := by
  unfold c
  rw [Even.neg_one_pow ⟨i + 1, by ring⟩, show (2 * i + 2) / 2 = i + 1 by omega]
  ring

theorem csum (i : ℕ) :
    (1 + ∑ k ∈ Finset.Icc 1 (2 * i), c k = 2 ^ i) ∧
    (1 + ∑ k ∈ Finset.Icc 1 (2 * i + 1), c k = 0) := by
  induction i with
  | zero =>
    refine ⟨by simp, ?_⟩
    rw [show 2 * 0 + 1 = 1 from rfl, Finset.Icc_self, Finset.sum_singleton]
    have := c_odd 0
    rw [show 2 * 0 + 1 = 1 from rfl] at this
    rw [this]; norm_num
  | succ i ih =>
    have e1 : 1 + ∑ k ∈ Finset.Icc 1 (2 * (i + 1)), c k = 2 ^ (i + 1) := by
      rw [show 2 * (i + 1) = (2 * i + 1) + 1 from by ring,
        Finset.sum_Icc_succ_top (by omega), show 2 * i + 1 + 1 = 2 * i + 2 from rfl, c_even]
      linarith [ih.2]
    refine ⟨e1, ?_⟩
    rw [Finset.sum_Icc_succ_top (by omega), c_odd]
    linarith [e1]

theorem csum_E (v : ℕ) : 1 + ∑ k ∈ Finset.Icc 1 v, c k = E v := by
  obtain ⟨i, rfl | rfl⟩ : ∃ i, v = 2 * i ∨ v = 2 * i + 1 := ⟨v / 2, by omega⟩
  · rw [(csum i).1]; unfold E
    rw [if_pos (by omega), show 2 * i / 2 = i by omega]
  · rw [(csum i).2]; unfold E
    rw [if_neg (by omega)]

theorem H_succ (n : ℕ) :
    H (n + 1) = H n + ∑ k ∈ Finset.Icc 1 (padicValNat 2 (n + 1)), c k := by
  unfold H
  have hsplit : ∀ k ∈ Finset.Icc 1 (n + 1),
      c k * (((n + 1) / 2 ^ k : ℕ) : ℤ) =
        c k * ((n / 2 ^ k : ℕ) : ℤ) + (if 2 ^ k ∣ n + 1 then c k else 0) := by
    intro k _
    rw [Nat.succ_div]
    split_ifs <;> push_cast <;> ring
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib,
    Finset.sum_Icc_succ_top (by omega)]
  have hz : (n / 2 ^ (n + 1) : ℕ) = 0 :=
    Nat.div_eq_of_lt (lt_trans (Nat.lt_succ_self n) Nat.lt_two_pow_self)
  rw [hz, ← Finset.sum_filter]
  have hf : (Finset.Icc 1 (n + 1)).filter (fun k => 2 ^ k ∣ n + 1) =
      Finset.Icc 1 (padicValNat 2 (n + 1)) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_Icc]
    rw [padicValNat_dvd_iff_le (Nat.succ_ne_zero n)]
    constructor
    · rintro ⟨⟨h1, _⟩, h3⟩
      exact ⟨h1, h3⟩
    · rintro ⟨h1, h2⟩
      refine ⟨⟨h1, ?_⟩, h2⟩
      have hd : 2 ^ k ∣ n + 1 := (padicValNat_dvd_iff_le (Nat.succ_ne_zero n)).mpr h2
      have := Nat.le_of_dvd (Nat.succ_pos n) hd
      have := @Nat.lt_two_pow_self k
      omega
  rw [hf]
  push_cast
  ring

theorem G_eq (n : ℕ) : ∑ k ∈ Finset.Icc 1 n, E (padicValNat 2 k) = n + H n := by
  induction n with
  | zero => simp [H]
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih, H_succ, ← csum_E]
    push_cast
    ring

theorem pairs (n N : ℕ) :
    ∑ k ∈ Finset.Icc 1 (2 * N), c k * ((n / 2 ^ k : ℕ) : ℤ) =
      -∑ j ∈ Finset.range N, (((n / 2 ^ (2 * j + 1) % 2 : ℕ) : ℤ)) * 2 ^ j := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [show 2 * (N + 1) = (2 * N + 1) + 1 from by ring,
      Finset.sum_Icc_succ_top (by omega), Finset.sum_Icc_succ_top (by omega), ih,
      Finset.sum_range_succ, show 2 * N + 1 + 1 = 2 * N + 2 from rfl, c_odd, c_even]
    have hq : n / 2 ^ (2 * N + 2) = n / 2 ^ (2 * N + 1) / 2 := by
      rw [Nat.div_div_eq_div_mul, ← pow_succ]
    rw [hq]
    have hm := Nat.mod_add_div (n / 2 ^ (2 * N + 1)) 2
    have hm' : (((n / 2 ^ (2 * N + 1) % 2 : ℕ) : ℤ)) +
        2 * (((n / 2 ^ (2 * N + 1) / 2 : ℕ) : ℤ)) = ((n / 2 ^ (2 * N + 1) : ℕ) : ℤ) := by
      exact_mod_cast hm
    rw [← hm']
    ring

theorem H_eq (n : ℕ) : H n = -(a n : ℤ) := by
  have hsub : Finset.Icc 1 n ⊆ Finset.Icc 1 (2 * n) := by
    intro k hk
    rw [Finset.mem_Icc] at hk ⊢
    omega
  unfold H
  rw [Finset.sum_subset hsub, pairs]
  · unfold a
    push_cast
    rfl
  · intro k hk hk'
    rw [Finset.mem_Icc] at hk hk'
    have hlt : n < 2 ^ k :=
      lt_of_lt_of_le Nat.lt_two_pow_self (Nat.pow_le_pow_right (by norm_num) (by omega))
    rw [Nat.div_eq_of_lt hlt]
    simp

theorem sqrt_pow (v : ℕ) :
    (1 / 2 : ℝ) * (Real.sqrt 2 ^ v + (-Real.sqrt 2) ^ v) = ((E v : ℤ) : ℝ) := by
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  obtain ⟨i, rfl | rfl⟩ : ∃ i, v = 2 * i ∨ v = 2 * i + 1 := ⟨v / 2, by omega⟩
  · unfold E
    rw [if_pos (by omega), show 2 * i / 2 = i by omega, pow_mul, pow_mul, neg_sq, hs]
    push_cast
    ring
  · unfold E
    rw [if_neg (by omega), Odd.neg_pow ⟨i, rfl⟩]
    push_cast
    ring

end OMA.A059906Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a059906.main := by
  intro n
  have h2 : ((OMA.S_oeis_a059906.a n : ℕ) : ℤ) = -OMA.A059906Proof.H n := by
    rw [OMA.A059906Proof.H_eq]; ring
  refine ⟨?_, ?_⟩
  · rw [Finset.mul_sum, Finset.sum_congr rfl (fun k _ => OMA.A059906Proof.sqrt_pow _),
      ← Int.cast_sum, OMA.A059906Proof.G_eq, OMA.A059906Proof.H_eq]
    push_cast
    ring
  · rw [h2]
    rfl
