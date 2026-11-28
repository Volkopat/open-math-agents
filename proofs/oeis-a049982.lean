import OMAStatements.S_oeis_a049982

namespace OMA.S_oeis_a049982.Proof
open Finset

/-- pairs `(a, d)` for a fixed length `k` -/
def G (n k : ℕ) : Finset (ℕ × ℕ) :=
  (Icc 1 n ×ˢ Icc 1 n).filter (fun p => 2 * k * p.1 + p.2 * k * (k - 1) = 2 * n)

lemma odd_q (h q : ℕ) (hh : 1 ≤ h) (hq : 1 ≤ q) :
    (G ((2 * h + 1) * q) (2 * h + 1)).card = (q - 1) / h := by
  set n := (2 * h + 1) * q with hn
  have hqn : q ≤ n := by rw [hn]; nlinarith
  have key : ∀ a d : ℕ, (2 * (2 * h + 1) * a + d * (2 * h + 1) * (2 * h + 1 - 1) = 2 * n ↔
      a + d * h = q) := by
    intro a d
    have e1 : 2 * (2 * h + 1) * a + d * (2 * h + 1) * (2 * h + 1 - 1)
        = (2 * (2 * h + 1)) * (a + d * h) := by
      rw [show 2 * h + 1 - 1 = 2 * h by omega]; ring
    have e2 : 2 * n = (2 * (2 * h + 1)) * q := by rw [hn]; ring
    rw [e1, e2]
    exact Nat.mul_right_inj (by omega)
  have hc : (Icc 1 ((q - 1) / h)).card = (q - 1) / h := by simp
  rw [← hc]
  refine Finset.card_bij' (fun p _ => p.2) (fun d _ => (q - d * h, d)) ?_ ?_ ?_ ?_
  · intro p hp
    simp only [G, mem_filter, mem_product, mem_Icc] at hp
    obtain ⟨⟨⟨h1, _⟩, h3, _⟩, h5⟩ := hp
    rw [key] at h5
    simp only [mem_Icc]
    refine ⟨h3, ?_⟩
    rw [Nat.le_div_iff_mul_le hh]; omega
  · intro d hd
    simp only [mem_Icc] at hd
    have := (Nat.le_div_iff_mul_le hh).1 hd.2
    have hdh : d ≤ d * h := Nat.le_mul_of_pos_right d hh
    simp only [G, mem_filter, mem_product, mem_Icc]
    refine ⟨⟨⟨by omega, by omega⟩, hd.1, by omega⟩, ?_⟩
    rw [key]; omega
  · intro p hp
    simp only [G, mem_filter, mem_product, mem_Icc] at hp
    obtain ⟨_, h5⟩ := hp
    rw [key] at h5
    ext <;> simp; omega
  · intro d _; rfl

lemma odd_k (n k : ℕ) (hk : Odd k) (h2 : 2 ≤ k) (hn : 1 ≤ n) :
    (G n k).card = if k ∣ n then 2 * (n - k) / (k * (k - 1)) else 0 := by
  obtain ⟨h, rfl⟩ := hk
  have hh : 1 ≤ h := by omega
  split_ifs with hd
  · obtain ⟨q, rfl⟩ := hd
    have hq : 1 ≤ q := by
      rcases Nat.eq_zero_or_pos q with h0 | h0
      · subst h0; simp at hn
      · exact h0
    rw [odd_q h q hh hq]
    have e1 : 2 * ((2 * h + 1) * q - (2 * h + 1)) = (2 * (2 * h + 1)) * (q - 1) := by
      rw [Nat.mul_sub, Nat.mul_sub]; ring_nf
    have e2 : (2 * h + 1) * (2 * h + 1 - 1) = (2 * (2 * h + 1)) * h := by
      rw [show 2 * h + 1 - 1 = 2 * h by omega]; ring
    rw [e1, e2, Nat.mul_div_mul_left _ _ (by omega)]
  · rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro p hp
    simp only [G, mem_filter] at hp
    apply hd
    have e1 : 2 * (2 * h + 1) * p.1 + p.2 * (2 * h + 1) * (2 * h + 1 - 1)
        = 2 * ((2 * h + 1) * (p.1 + p.2 * h)) := by
      rw [show 2 * h + 1 - 1 = 2 * h by omega]; ring
    rw [e1] at hp
    exact ⟨_, (Nat.mul_left_cancel (by norm_num) hp.2).symm⟩

lemma even_key (j q a d : ℕ) :
    (2 * (2 * (j + 1)) * a + d * (2 * (j + 1)) * (2 * (j + 1) - 1) = 2 * ((j + 1) * q) ↔
      2 * a + 2 * (d * j) + d = q) := by
  have e1 : 2 * (2 * (j + 1)) * a + d * (2 * (j + 1)) * (2 * (j + 1) - 1)
      = (2 * (j + 1)) * (2 * a + 2 * (d * j) + d) := by
    rw [show 2 * (j + 1) - 1 = 2 * j + 1 by omega]; ring
  rw [e1, show 2 * ((j + 1) * q) = (2 * (j + 1)) * q by ring]
  exact Nat.mul_right_inj (by omega)

lemma even_r (j r : ℕ) (hr : 1 ≤ r) :
    (G ((j + 1) * (2 * r)) (2 * (j + 1))).card = (r - 1) / (2 * j + 1) := by
  have hc : (Icc 1 ((r - 1) / (2 * j + 1))).card = (r - 1) / (2 * j + 1) := by simp
  have hrn : 2 * r ≤ (j + 1) * (2 * r) := by nlinarith
  have h1 : 1 ≤ 2 * j + 1 := by omega
  rw [← hc]
  refine Finset.card_bij' (fun p _ => p.2 / 2) (fun e _ => (r - e * (2 * j + 1), 2 * e)) ?_ ?_ ?_ ?_
  · intro p hp
    simp only [G, mem_filter, mem_product, mem_Icc] at hp
    obtain ⟨⟨⟨h1', _⟩, h3, _⟩, h5⟩ := hp
    rw [even_key] at h5
    simp only [mem_Icc]
    obtain ⟨e, he⟩ : ∃ e, p.2 = 2 * e := ⟨p.2 / 2, by omega⟩
    rw [he] at h5 ⊢
    have : 2 * e * j = 2 * (e * j) := by ring
    rw [show 2 * e / 2 = e by omega]
    refine ⟨by omega, ?_⟩
    rw [Nat.le_div_iff_mul_le h1]
    have : e * (2 * j + 1) = 2 * (e * j) + e := by ring
    omega
  · intro e he
    simp only [mem_Icc] at he
    have := (Nat.le_div_iff_mul_le h1).1 he.2
    have h6 : e * (2 * j + 1) = 2 * (e * j) + e := by ring
    have h7 : 2 * e * j = 2 * (e * j) := by ring
    simp only [G, mem_filter, mem_product, mem_Icc]
    refine ⟨⟨⟨by omega, by omega⟩, by omega, by omega⟩, ?_⟩
    rw [even_key]; omega
  · rintro ⟨a, d⟩ hp
    simp only [G, mem_filter, mem_product, mem_Icc] at hp
    obtain ⟨_, h5⟩ := hp
    rw [even_key] at h5
    obtain ⟨e, rfl⟩ : ∃ e, d = 2 * e := ⟨d / 2, by omega⟩
    have h6 : e * (2 * j + 1) = 2 * (e * j) + e := by ring
    have h7 : 2 * e * j = 2 * (e * j) := by ring
    rw [show 2 * e / 2 = e by omega]
    ext
    · simp only; omega
    · simp only
  · intro e _; simp

lemma even_r1 (j r : ℕ) :
    (G ((j + 1) * (2 * r + 1)) (2 * (j + 1))).card = (r + j) / (2 * j + 1) := by
  have hc : (range ((r + j) / (2 * j + 1))).card = (r + j) / (2 * j + 1) := by simp
  have hrn : 2 * r + 1 ≤ (j + 1) * (2 * r + 1) := by nlinarith
  have h1 : 0 < 2 * j + 1 := by omega
  rw [← hc]
  refine Finset.card_bij' (fun p _ => p.2 / 2) (fun e _ => (r - j - e * (2 * j + 1), 2 * e + 1)) ?_ ?_ ?_ ?_
  · intro p hp
    simp only [G, mem_filter, mem_product, mem_Icc] at hp
    obtain ⟨⟨⟨h1', _⟩, h3, _⟩, h5⟩ := hp
    rw [even_key] at h5
    simp only [mem_range]
    obtain ⟨e, he⟩ : ∃ e, p.2 = 2 * e + 1 := ⟨p.2 / 2, by omega⟩
    rw [he] at h5 ⊢
    have : (2 * e + 1) * j = 2 * (e * j) + j := by ring
    rw [Nat.lt_iff_add_one_le, Nat.le_div_iff_mul_le h1]
    have : (2 * e + 1) / 2 = e := by omega
    rw [this]
    have : (e + 1) * (2 * j + 1) = 2 * (e * j) + e + 2 * j + 1 := by ring
    omega
  · intro e he
    simp only [mem_range] at he
    rw [Nat.lt_iff_add_one_le, Nat.le_div_iff_mul_le h1] at he
    have h6 : (e + 1) * (2 * j + 1) = 2 * (e * j) + e + 2 * j + 1 := by ring
    have h8 : e * (2 * j + 1) = 2 * (e * j) + e := by ring
    have h7 : (2 * e + 1) * j = 2 * (e * j) + j := by ring
    simp only [G, mem_filter, mem_product, mem_Icc]
    refine ⟨⟨⟨by omega, by omega⟩, by omega, by omega⟩, ?_⟩
    rw [even_key]; omega
  · rintro ⟨a, d⟩ hp
    simp only [G, mem_filter, mem_product, mem_Icc] at hp
    obtain ⟨_, h5⟩ := hp
    rw [even_key] at h5
    obtain ⟨e, rfl⟩ : ∃ e, d = 2 * e + 1 := ⟨d / 2, by omega⟩
    have h8 : e * (2 * j + 1) = 2 * (e * j) + e := by ring
    have h7 : (2 * e + 1) * j = 2 * (e * j) + j := by ring
    rw [show (2 * e + 1) / 2 = e by omega]
    ext
    · simp only; omega
    · simp only
  · intro e _; simp only; omega

def F1 (n m : ℕ) : ℕ := 2 * (n - m) / (m * (m - 1))

def F2 (n m : ℕ) : ℕ :=
  if Even (n / m) then (n - 2 * m) / (2 * m * (2 * m - 1))
  else (n + 2 * m * m - 3 * m) / (2 * m * (2 * m - 1))

lemma even_k (n m : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) :
    (G n (2 * m)).card = if m ∣ n then F2 n m else 0 := by
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
  split_ifs with hd
  · obtain ⟨q, rfl⟩ := hd
    have hq : 1 ≤ q := by
      rcases Nat.eq_zero_or_pos q with h0 | h0
      · subst h0; simp at hn
      · exact h0
    have hdiv : (j + 1) * q / (j + 1) = q := Nat.mul_div_cancel_left q (by omega)
    have hden : 2 * (j + 1) * (2 * (j + 1) - 1) = (2 * (j + 1)) * (2 * j + 1) := by
      rw [show 2 * (j + 1) - 1 = 2 * j + 1 by omega]
    rcases Nat.even_or_odd' q with ⟨r, rfl | rfl⟩
    · have hr : 1 ≤ r := by omega
      rw [even_r j r hr, F2, hdiv, if_pos (even_two_mul r), hden]
      have : (j + 1) * (2 * r) - 2 * (j + 1) = (2 * (j + 1)) * (r - 1) := by
        rw [Nat.mul_sub]; ring_nf
      rw [this, Nat.mul_div_mul_left _ _ (by omega)]
    · rw [even_r1 j r, F2, hdiv, if_neg (by rw [Nat.not_even_iff_odd]; exact odd_two_mul_add_one r),
        hden]
      have : (j + 1) * (2 * r + 1) + 2 * (j + 1) * (j + 1) - 3 * (j + 1)
          = (2 * (j + 1)) * (r + j) := by
        have : (j + 1) * (2 * r + 1) + 2 * (j + 1) * (j + 1)
            = (2 * (j + 1)) * (r + j) + 3 * (j + 1) := by ring
        rw [this, Nat.add_sub_cancel]
      rw [this, Nat.mul_div_mul_left _ _ (by omega)]
  · rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro p hp
    simp only [G, mem_filter] at hp
    apply hd
    have e1 : 2 * (2 * (j + 1)) * p.1 + p.2 * (2 * (j + 1)) * (2 * (j + 1) - 1)
        = 2 * ((j + 1) * (2 * p.1 + p.2 * (2 * j + 1))) := by
      rw [show 2 * (j + 1) - 1 = 2 * j + 1 by omega]; ring
    rw [e1] at hp
    exact ⟨_, (Nat.mul_left_cancel (by norm_num) hp.2).symm⟩

lemma floor_nat (x y : ℕ) : Int.floor ((x : ℚ) / (y : ℚ)) = ((x / y : ℕ) : ℤ) := by
  rw [Rat.floor_natCast_div_natCast]; exact (Int.natCast_div x y).symm

lemma floor1 (n m : ℕ) (hm : m ∈ n.divisors.filter (fun m => Odd m ∧ 1 < m)) :
    Int.floor ((2 * ((n : ℚ) - (m : ℚ))) / ((m : ℚ) * ((m : ℚ) - 1))) = (F1 n m : ℤ) := by
  simp only [mem_filter, Nat.mem_divisors] at hm
  have hle : m ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hm.1.2) hm.1.1
  have e1 : (2 * ((n : ℚ) - (m : ℚ))) = ((2 * (n - m) : ℕ) : ℚ) := by
    push_cast [hle]; ring
  have e2 : ((m : ℚ) * ((m : ℚ) - 1)) = ((m * (m - 1) : ℕ) : ℚ) := by
    push_cast [show 1 ≤ m by omega]; ring
  rw [e1, e2, floor_nat]; rfl

lemma floor2 (n m : ℕ) (hm : m ∈ n.divisors) :
    Int.floor
      (((n : ℚ) - (m : ℚ) * (5 - (-1 : ℚ) ^ (n / m)) / 2 +
          (m : ℚ) ^ 2 * (1 - (-1 : ℚ) ^ (n / m))) /
        (2 * (m : ℚ) * (2 * (m : ℚ) - 1))) = (F2 n m : ℤ) := by
  rw [Nat.mem_divisors] at hm
  obtain ⟨⟨q, hq⟩, hn0⟩ := hm
  have hm1 : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · subst h0; simp at hq; omega
    · exact h0
  have hq1 : 1 ≤ q := by
    rcases Nat.eq_zero_or_pos q with h0 | h0
    · subst h0; simp at hq; omega
    · exact h0
  have hdiv : n / m = q := by rw [hq]; exact Nat.mul_div_cancel_left q (by omega)
  have e2 : (2 * (m : ℚ) * (2 * (m : ℚ) - 1)) = ((2 * m * (2 * m - 1) : ℕ) : ℚ) := by
    push_cast [show 1 ≤ 2 * m by omega]; ring
  rw [hdiv, e2, F2, hdiv]
  rcases Nat.even_or_odd q with he | ho
  · rw [if_pos he, he.neg_one_pow]
    have h2 : 2 * m ≤ n := by
      obtain ⟨r, rfl⟩ := he
      have : 1 ≤ r := by omega
      rw [hq]; nlinarith
    have e1 : ((n : ℚ) - (m : ℚ) * (5 - 1) / 2 + (m : ℚ) ^ 2 * (1 - 1))
        = ((n - 2 * m : ℕ) : ℚ) := by push_cast [h2]; ring
    rw [e1, floor_nat]
  · rw [if_neg (Nat.not_even_iff_odd.2 ho), ho.neg_one_pow]
    have h2 : 3 * m ≤ n + 2 * m * m := by rw [hq]; nlinarith
    have e1 : ((n : ℚ) - (m : ℚ) * (5 - -1) / 2 + (m : ℚ) ^ 2 * (1 - -1))
        = ((n + 2 * m * m - 3 * m : ℕ) : ℚ) := by push_cast [h2]; ring
    rw [e1, floor_nat]

lemma a_eq (n : ℕ) : a n = ∑ k ∈ Icc 2 (2 * n), (G n k).card := by
  set T : Finset (ℕ × ℕ × ℕ) := (Icc 1 n ×ˢ (Icc 1 n ×ˢ Icc 2 (2 * n))).filter
    (fun t => 2 * t.2.2 * t.1 + t.2.1 * t.2.2 * (t.2.2 - 1) = 2 * n) with hT
  have hS : {t : ℕ × ℕ × ℕ | 1 ≤ t.1 ∧ 1 ≤ t.2.1 ∧ 2 ≤ t.2.2 ∧
      2 * t.2.2 * t.1 + t.2.1 * t.2.2 * (t.2.2 - 1) = 2 * n} = ↑T := by
    ext ⟨x, d, k⟩
    simp only [Set.mem_ofPred_eq, hT, coe_filter, mem_product, mem_Icc]
    constructor
    · rintro ⟨h1, h2, h3, h4⟩
      have i1 : d * 2 * 1 ≤ d * k * (k - 1) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ h3) (by omega)
      have i2 : 2 * 2 * x ≤ 2 * k * x := Nat.mul_le_mul (Nat.mul_le_mul_left _ h3) le_rfl
      have i3 : 2 * k * 1 ≤ 2 * k * x := Nat.mul_le_mul_left _ h1
      refine ⟨⟨⟨h1, by omega⟩, ⟨h2, by omega⟩, ⟨h3, by omega⟩⟩, h4⟩
    · rintro ⟨⟨⟨h1, _⟩, ⟨h2, _⟩, ⟨h3, _⟩⟩, h4⟩
      exact ⟨h1, h2, h3, h4⟩
  rw [a, hS, Set.ncard_coe_finset, ← Finset.card_sigma]
  refine Finset.card_bij' (fun t _ => ⟨t.2.2, (t.1, t.2.1)⟩) (fun s _ => (s.2.1, s.2.2, s.1))
    ?_ ?_ ?_ ?_
  · rintro ⟨x, d, k⟩ ht
    simp only [hT, mem_filter, mem_product, mem_Icc] at ht
    simp only [mem_sigma, G, mem_filter, mem_product, mem_Icc]
    exact ⟨ht.1.2.2, ⟨ht.1.1, ht.1.2.1⟩, ht.2⟩
  · rintro ⟨k, x, d⟩ hs
    simp only [mem_sigma, G, mem_filter, mem_product, mem_Icc] at hs
    simp only [hT, mem_filter, mem_product, mem_Icc]
    exact ⟨⟨hs.2.1.1, hs.2.1.2, hs.1⟩, hs.2.2⟩
  · intro t _; rfl
  · intro s _; rfl

theorem solution_main : type_of% @OMA.S_oeis_a049982.main := by
  intro n hn
  rw [a_eq n]
  push_cast
  rw [← Finset.sum_filter_add_sum_filter_not (Icc 2 (2 * n)) Odd,
    Finset.sum_congr rfl (fun m hm => floor1 n m hm),
    Finset.sum_congr rfl (fun m hm => floor2 n m hm)]
  congr 1
  · rw [Finset.sum_congr rfl (fun k hk => by
      simp only [mem_filter, mem_Icc] at hk
      rw [odd_k n k hk.2 hk.1.1 hn])]
    push_cast
    rw [← Finset.sum_filter, Finset.filter_filter]
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext k
    simp only [mem_filter, mem_Icc, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩
      exact ⟨⟨h4, by omega⟩, h3, by omega⟩
    · rintro ⟨⟨h4, _⟩, h3, h1⟩
      have := Nat.le_of_dvd (by omega) h4
      exact ⟨⟨by omega, by omega⟩, h3, h4⟩
  · have himg : (Icc 2 (2 * n)).filter (fun k => ¬ Odd k) = (Icc 1 n).image (fun m => 2 * m) := by
      ext k
      simp only [mem_filter, mem_Icc, mem_image, Nat.not_odd_iff_even]
      constructor
      · rintro ⟨⟨h1, h2⟩, ⟨m, rfl⟩⟩
        exact ⟨m, ⟨by omega, by omega⟩, by ring⟩
      · rintro ⟨m, ⟨h1, h2⟩, rfl⟩
        exact ⟨⟨by omega, by omega⟩, ⟨m, by ring⟩⟩
    rw [himg, Finset.sum_image (fun x _ y _ h => by simpa using h)]
    rw [Finset.sum_congr rfl (fun m hm => by
      simp only [mem_Icc] at hm
      rw [even_k n m hm.1 hn])]
    push_cast
    rw [← Finset.sum_filter]
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext m
    simp only [mem_filter, mem_Icc, Nat.mem_divisors]
    constructor
    · rintro ⟨_, h3⟩
      exact ⟨h3, by omega⟩
    · rintro ⟨h3, _⟩
      have := Nat.le_of_dvd (by omega) h3
      have : 0 < m := Nat.pos_of_dvd_of_pos h3 (by omega)
      exact ⟨⟨by omega, by omega⟩, h3⟩

end OMA.S_oeis_a049982.Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a049982.main := OMA.S_oeis_a049982.Proof.solution_main
