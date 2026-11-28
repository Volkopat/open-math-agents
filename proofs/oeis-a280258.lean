import OMAStatements.S_oeis_a280258
import Mathlib

open OMA.S_oeis_a280258


theorem pxi_mod (m : ℕ) (hm : 1 ≤ m) : pxi m % 2 = if m % 2 = 0 ∨ m = 1 then 1 else 0 := by
  by_cases h : m % 2 = 0 ∨ m = 1
  · rw [if_pos h]
    have hodd : Odd (pxi m) := by
      unfold pxi
      apply Finset.prod_induction _ Odd (fun a b ha hb => ha.mul hb) odd_one
      intro k hk
      simp only [Finset.mem_filter, Finset.mem_Icc] at hk
      rcases h with h | rfl
      · rw [Nat.odd_iff]
        by_contra hc
        have h2k : 2 ∣ k := by omega
        have h2m : 2 ∣ m := by omega
        have := Nat.dvd_gcd h2k h2m
        rw [hk.2] at this
        norm_num at this
      · have : k = 1 := by omega
        subst this; exact odd_one
    exact Nat.odd_iff.1 hodd
  · rw [if_neg h]
    simp only [not_or] at h
    have hmem : 2 ∈ (Finset.Icc 1 m).filter (fun k => Nat.Coprime k m) := by
      simp only [Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨by norm_num, by omega⟩, ?_⟩
      exact Nat.coprime_two_left.2 (Nat.odd_iff.2 (by omega))
    exact Nat.mod_eq_zero_of_dvd (Finset.dvd_prod_of_mem _ hmem)

theorem a_mod (n : ℕ) : a n % 2 = ((n.divisors).filter (fun d => d % 2 = 0 ∨ d = 1)).card % 2 := by
  unfold a
  rw [Finset.sum_nat_mod, Finset.card_filter]
  congr 1
  apply Finset.sum_congr rfl
  intro d hd
  have hd1 : 1 ≤ d := Nat.pos_of_mem_divisors hd
  rw [pxi_mod d hd1]

theorem card_split (n : ℕ) (hn : 1 ≤ n) :
    ((n.divisors).filter (fun d => d % 2 = 0 ∨ d = 1)).card =
      1 + ((n.divisors).filter (fun d => d % 2 = 0)).card := by
  have : (n.divisors).filter (fun d => d % 2 = 0 ∨ d = 1) =
      insert 1 ((n.divisors).filter (fun d => d % 2 = 0)) := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_insert, Nat.mem_divisors]
    constructor
    · rintro ⟨h1, h2 | h2⟩
      · right; exact ⟨h1, h2⟩
      · left; exact h2
    · rintro (rfl | ⟨h1, h2⟩)
      · exact ⟨⟨one_dvd n, by omega⟩, Or.inr rfl⟩
      · exact ⟨h1, Or.inl h2⟩
  rw [this, Finset.card_insert_of_notMem (by simp), add_comm]

theorem even_div_odd (n : ℕ) (hn : n % 2 = 1) : ((n.divisors).filter (fun d => d % 2 = 0)).card = 0 := by
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro d hd h
  have := Nat.dvd_of_mem_divisors hd
  have h2 : 2 ∣ d := by omega
  have := h2.trans this
  omega

theorem even_div_even (m : ℕ) (hm : 1 ≤ m) :
    (((2 * m).divisors).filter (fun d => d % 2 = 0)).card = (m.divisors).card := by
  have : ((2 * m).divisors).filter (fun d => d % 2 = 0) = (m.divisors).image (fun e => 2 * e) := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_image, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨hd, -⟩, h2⟩
      obtain ⟨e, rfl⟩ : ∃ e, d = 2 * e := ⟨d / 2, by omega⟩
      exact ⟨e, ⟨Nat.dvd_of_mul_dvd_mul_left (by norm_num) hd, by omega⟩, rfl⟩
    · rintro ⟨e, ⟨he, -⟩, rfl⟩
      exact ⟨⟨Nat.mul_dvd_mul_left 2 he, by omega⟩, by omega⟩
  rw [this, Finset.card_image_of_injective _ (fun x y h => by simpa using h)]

theorem tau_odd (m : ℕ) (hm : 1 ≤ m) : (m.divisors).card % 2 = 1 ↔ ∃ k, m = k ^ 2 := by
  set D := m.divisors
  have hsplit : D.card = (D.filter (fun d => d * d < m)).card + (D.filter (fun d => m < d * d)).card +
      (D.filter (fun d => d * d = m)).card := by
    have h1 := Finset.card_filter_add_card_filter_not (s := D) (p := fun d => d * d < m)
    have h2 := Finset.card_filter_add_card_filter_not (s := D.filter (fun d => ¬ d * d < m))
      (p := fun d => m < d * d)
    rw [Finset.filter_filter, Finset.filter_filter] at h2
    have e1 : D.filter (fun d => ¬ d * d < m ∧ m < d * d) = D.filter (fun d => m < d * d) := by
      apply Finset.filter_congr; intro d _; constructor
      · rintro ⟨-, h⟩; exact h
      · intro h; exact ⟨by omega, h⟩
    have e2 : D.filter (fun d => ¬ d * d < m ∧ ¬ m < d * d) = D.filter (fun d => d * d = m) := by
      apply Finset.filter_congr; intro d _; constructor
      · rintro ⟨h1, h2⟩; omega
      · intro h; exact ⟨by omega, by omega⟩
    rw [e1, e2] at h2
    omega
  have hAB : (D.filter (fun d => d * d < m)).card = (D.filter (fun d => m < d * d)).card := by
    apply Finset.card_bij (fun d _ => m / d)
    · intro d hd
      simp only [Finset.mem_filter, Nat.mem_divisors, D] at hd ⊢
      obtain ⟨⟨hdm, -⟩, hlt⟩ := hd
      obtain ⟨c, hc⟩ := hdm
      have hd0 : 0 < d := by rcases Nat.eq_zero_or_pos d with h | h <;> [simp [h] at hc; exact h] <;> omega
      rw [hc, Nat.mul_div_cancel_left _ hd0]
      refine ⟨⟨⟨d, by ring⟩, by omega⟩, ?_⟩
      have : d < c := by nlinarith
      nlinarith
    · intro d1 hd1 d2 hd2 h
      simp only [Finset.mem_filter, Nat.mem_divisors, D] at hd1 hd2
      rw [← Nat.div_div_self hd1.1.1 (by omega), h, Nat.div_div_self hd2.1.1 (by omega)]
    · intro e he
      simp only [Finset.mem_filter, Nat.mem_divisors, D] at he
      obtain ⟨⟨hem, -⟩, hlt⟩ := he
      obtain ⟨c, hc⟩ := hem
      have he0 : 0 < e := by rcases Nat.eq_zero_or_pos e with h | h <;> [simp [h] at hc; exact h] <;> omega
      refine ⟨c, ?_, ?_⟩
      · simp only [Finset.mem_filter, Nat.mem_divisors, D]
        refine ⟨⟨⟨e, by rw [hc]; ring⟩, by omega⟩, ?_⟩
        have : c < e := by nlinarith
        nlinarith
      · rw [hc, Nat.mul_div_cancel _ (by
          rcases Nat.eq_zero_or_pos c with h | h
          · subst h; simp at hc; omega
          · exact h)]
  have hC : (D.filter (fun d => d * d = m)).card ≤ 1 := by
    apply Finset.card_le_one.2
    intro x hx y hy
    simp only [Finset.mem_filter] at hx hy
    have : x * x = y * y := by rw [hx.2, hy.2]
    nlinarith [Nat.mul_self_le_mul_self_iff (m := x) (n := y), Nat.mul_self_lt_mul_self_iff (m := x) (n := y)]
  constructor
  · intro hodd
    have : (D.filter (fun d => d * d = m)).card = 1 := by omega
    obtain ⟨k, hk⟩ := Finset.card_eq_one.1 this
    have hkmem : k ∈ D.filter (fun d => d * d = m) := by rw [hk]; exact Finset.mem_singleton_self k
    simp only [Finset.mem_filter] at hkmem
    exact ⟨k, by rw [sq]; exact hkmem.2.symm⟩
  · rintro ⟨k, hk⟩
    have hmem : k ∈ D.filter (fun d => d * d = m) := by
      simp only [Finset.mem_filter, Nat.mem_divisors, D]
      exact ⟨⟨⟨k, by rw [hk]; ring⟩, by omega⟩, by rw [hk]; ring⟩
    have : (D.filter (fun d => d * d = m)).card = 1 := by
      have := Finset.card_pos.2 ⟨k, hmem⟩
      omega
    omega

theorem OMA.solution : type_of% @OMA.S_oeis_a280258.main := by
  intro n hn
  have key : a n % 2 = 1 ↔ ¬ ∃ k : ℕ, n = 2 * k ^ 2 := by
    rw [a_mod, card_split n hn]
    rcases Nat.even_or_odd n with ⟨m, hm⟩ | hodd
    · have hm2 : n = 2 * m := by omega
      have hm1 : 1 ≤ m := by omega
      rw [hm2, even_div_even m hm1]
      have ht := tau_odd m hm1
      constructor
      · intro h hk
        obtain ⟨k, hk⟩ := hk
        have : m = k ^ 2 := by omega
        have := ht.2 ⟨k, this⟩
        omega
      · intro h
        by_contra hc
        have : (m.divisors).card % 2 = 1 := by omega
        obtain ⟨k, hk⟩ := ht.1 this
        exact h ⟨k, by omega⟩
    · have hn1 : n % 2 = 1 := Nat.odd_iff.1 hodd
      rw [even_div_odd n hn1]
      constructor
      · intro _ hk
        obtain ⟨k, hk⟩ := hk
        omega
      · intro _; norm_num
  refine ⟨fun h => Nat.odd_iff.2 (key.2 h), fun h => ?_⟩
  rw [Nat.even_iff]
  have := mt key.1 (not_not.2 h)
  omega
