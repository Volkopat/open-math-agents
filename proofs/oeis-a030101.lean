import OMAStatements.S_oeis_a030101
import Mathlib

open OMA.S_oeis_a030101

lemma digits_even (j : ℕ) (hj : 0 < j) : Nat.digits 2 (2 * j) = 0 :: Nat.digits 2 j := by
  rw [Nat.digits_def' (by norm_num) (by omega)]
  congr 1
  · omega
  · congr 1; omega

lemma digits_odd (j : ℕ) : Nat.digits 2 (2 * j + 1) = 1 :: Nat.digits 2 j := by
  rw [Nat.digits_def' (by norm_num) (by omega)]
  congr 1
  · omega
  · congr 1; omega

lemma sum_range_even_odd (f : ℕ → ℕ) (k : ℕ) :
    ∑ m ∈ Finset.range (2 * k + 1), f m
      = ∑ j ∈ Finset.range (k + 1), f (2 * j) + ∑ j ∈ Finset.range k, f (2 * j + 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show 2 * (k + 1) + 1 = 2 * k + 1 + 1 + 1 by ring, Finset.sum_range_succ,
      Finset.sum_range_succ, ih, Finset.sum_range_succ (fun j => f (2 * j)) (k + 1),
      Finset.sum_range_succ (fun j => f (2 * j + 1)) k]
    rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring]
    ring

lemma w_eq (n : ℕ) : w n = ∑ m ∈ Finset.range (n + 1),
    if Nat.digits 2 m < Nat.digits 2 n then 1 else 0 := by
  unfold w
  rw [Finset.card_filter]

lemma w_zero : w 0 = 0 := by decide

lemma ind_even (j : ℕ) (L : List ℕ) (hL : L ≠ []) :
    (Nat.digits 2 (2 * j) < 0 :: L) ↔ (Nat.digits 2 j < L) := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp only [mul_zero, Nat.digits_zero, List.nil_lt_cons, true_iff]
    obtain ⟨x, l, rfl⟩ := List.exists_cons_of_ne_nil hL
    exact List.nil_lt_cons x l
  · rw [digits_even j hj, List.cons_lt_cons_self]

lemma w_even (k : ℕ) : w (2 * k) = w k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rfl
  rw [w_eq, w_eq, sum_range_even_odd, digits_even k hk]
  have hL : Nat.digits 2 k ≠ [] := Nat.digits_ne_nil_iff_ne_zero.mpr (by omega)
  have h2 : ∑ j ∈ Finset.range k,
      (if Nat.digits 2 (2 * j + 1) < 0 :: Nat.digits 2 k then 1 else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    rw [digits_odd, if_neg]
    rw [List.cons_lt_cons_iff]; simp
  rw [h2, add_zero]
  apply Finset.sum_congr rfl
  intro j _
  exact if_congr (ind_even j _ hL) rfl rfl

lemma w_odd (k : ℕ) : w (2 * k + 1) = w k + k + 1 := by
  rw [w_eq, w_eq, show 2 * k + 1 + 1 = 2 * (k + 1) by ring]
  rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring, Finset.sum_range_succ, sum_range_even_odd,
    digits_odd k]
  have h1 : ∑ j ∈ Finset.range (k + 1),
      (if Nat.digits 2 (2 * j) < 1 :: Nat.digits 2 k then 1 else 0) = k + 1 := by
    rw [Finset.sum_eq_card_nsmul (b := 1)]
    · simp
    intro j _
    rw [if_pos]
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · simp
    · rw [digits_even j hj, List.cons_lt_cons_iff]; simp
  have h2 : ∀ j, (if Nat.digits 2 (2 * j + 1) < 1 :: Nat.digits 2 k then 1 else 0)
      = (if Nat.digits 2 j < Nat.digits 2 k then 1 else 0) := by
    intro j
    rw [digits_odd]
    exact if_congr List.cons_lt_cons_self rfl rfl
  have h3 : (if 1 :: Nat.digits 2 k < 1 :: Nat.digits 2 k then 1 else 0) = 0 :=
    if_neg (List.lt_irrefl _)
  rw [h1, Finset.sum_congr rfl (fun j _ => h2 j), h3]
  have h4 : (if Nat.digits 2 k < Nat.digits 2 k then 1 else 0) = 0 := if_neg (List.lt_irrefl _)
  rw [Finset.sum_range_succ, h4]
  ring

lemma a_even (k : ℕ) (hk : 0 < k) : a (2 * k) = a k := by
  unfold a
  rw [digits_even k hk, List.reverse_cons, Nat.ofDigits_append_zero]

lemma a_odd (k : ℕ) : a (2 * k + 1) = a k + 2 ^ (Nat.digits 2 k).length := by
  unfold a
  rw [digits_odd k, List.reverse_cons, Nat.ofDigits_append, List.length_reverse,
    Nat.ofDigits_singleton]
  ring

lemma log_two_mul (k : ℕ) (hk : 0 < k) (r : ℕ) (hr : r < 2) :
    Nat.log 2 (2 * k + r) = Nat.log 2 k + 1 := by
  have h1 := Nat.log_div_base 2 (2 * k + r)
  rw [show (2 * k + r) / 2 = k by omega] at h1
  have h2 : 0 < Nat.log 2 (2 * k + r) := Nat.log_pos (by norm_num) (by omega)
  omega

lemma b_even (k : ℕ) (hk : 0 < k) : A053645 (2 * k) = 2 * A053645 k := by
  unfold A053645
  have := log_two_mul k hk 0 (by norm_num)
  rw [add_zero] at this
  rw [this, pow_succ]
  have : 2 ^ Nat.log 2 k ≤ k := Nat.pow_log_le_self 2 (by omega)
  omega

lemma b_odd (k : ℕ) (hk : 0 < k) : A053645 (2 * k + 1) = 2 * A053645 k + 1 := by
  unfold A053645
  rw [log_two_mul k hk 1 (by norm_num), pow_succ]
  have : 2 ^ Nat.log 2 k ≤ k := Nat.pow_log_le_self 2 (by omega)
  omega

theorem OMA.solution : type_of% @OMA.S_oeis_a030101.main := by
  intro n hn
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    obtain ⟨k, r, hr, rfl⟩ : ∃ k r, r < 2 ∧ n = 2 * k + r := ⟨n / 2, n % 2, Nat.mod_lt _ (by norm_num), by omega⟩
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · -- n = 1
      have : r = 1 := by omega
      subst this
      decide
    have ihk := ih k (by omega) hk
    interval_cases r
    · rw [add_zero, a_even k hk, w_even, b_even k hk, w_even]
      exact ihk
    · rw [a_odd, w_odd, b_odd k hk, w_odd, Nat.length_digits 2 k (by norm_num) (by omega)]
      have hb : A053645 k + 2 ^ Nat.log 2 k = k := by
        unfold A053645
        have : 2 ^ Nat.log 2 k ≤ k := Nat.pow_log_le_self 2 (by omega)
        omega
      push_cast
      rw [ihk, pow_succ]
      have hb' : ((A053645 k : ℕ) : ℤ) + 2 ^ Nat.log 2 k = k := by exact_mod_cast hb
      linear_combination (2 : ℤ) * hb'
