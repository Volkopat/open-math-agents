import OMAStatements.S_oeis_a285956

namespace OMA.S_oeis_a285956

open PowerSeries


instance (n x y u v : ℕ) : Decidable (good n x y u v) := by
  unfold good
  infer_instance


/-- The coordinate c avoids the diagonal points of the lines x and y. -/
def avoid (n x y c : ℕ) : Prop := x ≠ c ∧ y ≠ c ∧ x + c + 1 ≠ n ∧ y + c + 1 ≠ n

instance (n x y c : ℕ) : Decidable (avoid n x y c) := by
  unfold avoid
  infer_instance

theorem card_lt_pairs (S : Finset ℕ) :
    ((S ×ˢ S).filter (fun q => q.1 < q.2)).card = S.card.choose 2 := by
  have h1 : S.offDiag = (S ×ˢ S).filter (fun q => q.1 < q.2) ∪ (S ×ˢ S).filter (fun q => q.2 < q.1) := by
    ext ⟨p, q⟩
    simp only [Finset.mem_offDiag, Finset.mem_union, Finset.mem_filter, Finset.mem_product]
    constructor
    · rintro ⟨hp, hq, hpq⟩
      rcases Nat.lt_or_gt_of_ne hpq with h | h
      · exact Or.inl ⟨⟨hp, hq⟩, h⟩
      · exact Or.inr ⟨⟨hp, hq⟩, h⟩
    · rintro (⟨⟨hp, hq⟩, h⟩ | ⟨⟨hp, hq⟩, h⟩)
      · exact ⟨hp, hq, by omega⟩
      · exact ⟨hp, hq, by omega⟩
  have h2 : Disjoint ((S ×ˢ S).filter (fun q => q.1 < q.2)) ((S ×ˢ S).filter (fun q => q.2 < q.1)) := by
    rw [Finset.disjoint_filter]
    intro q _ h h'
    omega
  have h3 : ((S ×ˢ S).filter (fun q => q.2 < q.1)).card =
      ((S ×ˢ S).filter (fun q => q.1 < q.2)).card := by
    apply Finset.card_bij (fun q _ => (q.2, q.1))
    · intro q hq
      simp only [Finset.mem_filter, Finset.mem_product] at hq ⊢
      exact ⟨⟨hq.1.2, hq.1.1⟩, hq.2⟩
    · intro q₁ _ q₂ _ h
      simp only [Prod.mk.injEq] at h
      exact Prod.ext h.2 h.1
    · intro q hq
      refine ⟨(q.2, q.1), ?_, rfl⟩
      simp only [Finset.mem_filter, Finset.mem_product] at hq ⊢
      exact ⟨⟨hq.1.2, hq.1.1⟩, hq.2⟩
  have h4 := Finset.offDiag_card S
  rw [h1, Finset.card_union_of_disjoint h2, h3] at h4
  rw [Nat.choose_two_right, Nat.mul_sub_one, ← h4]
  omega

theorem a_sum (n : ℕ) : a n = ∑ x ∈ Finset.range n, ∑ y ∈ Finset.range n,
    ∑ u ∈ Finset.range n, ∑ v ∈ Finset.range n, if good n x y u v then 1 else 0 := by
  unfold a
  rw [Finset.card_filter]
  simp only [Finset.sum_product]

theorem good_iff {n x y u v : ℕ} (hxy : x < y) :
    good n x y u v ↔ avoid n x y u ∧ avoid n x y v ∧ u < v := by
  unfold good avoid
  constructor
  · rintro ⟨-, huv, h1, h2, h3, h4, h5, h6, h7, h8⟩
    exact ⟨⟨h1, h3, h5, h7⟩, ⟨h2, h4, h6, h8⟩, huv⟩
  · rintro ⟨⟨h1, h3, h5, h7⟩, ⟨h2, h4, h6, h8⟩, huv⟩
    exact ⟨hxy, huv, h1, h2, h3, h4, h5, h6, h7, h8⟩

/-- For x < y the rectangles with these x-coordinates are the pairs u < v of coordinates that
avoid T = {x, y, n-1-x, n-1-y}. -/
theorem inner_eq (n x y : ℕ) :
    (∑ u ∈ Finset.range n, ∑ v ∈ Finset.range n, if good n x y u v then 1 else 0) =
      if x < y then ((Finset.range n).filter (fun c => avoid n x y c)).card.choose 2 else 0 := by
  split_ifs with hxy
  · rw [← card_lt_pairs, Finset.card_filter, Finset.sum_product, Finset.sum_filter]
    refine Finset.sum_congr rfl (fun u _ => ?_)
    rw [Finset.sum_filter]
    split_ifs with hu
    · refine Finset.sum_congr rfl (fun v _ => ?_)
      by_cases hv : avoid n x y v <;> by_cases huv : u < v <;> simp [good_iff hxy, hu, hv, huv]
    · refine Finset.sum_eq_zero (fun v _ => ?_)
      simp [good_iff hxy, hu]
  · refine Finset.sum_eq_zero (fun u _ => Finset.sum_eq_zero (fun v _ => ?_))
    simp only [good, hxy, false_and, if_false]

/-- The number of coordinates avoiding T, by the coincidences in T. -/
theorem card_S (n x y : ℕ) (hxy : x < y) (hy : y < n) :
    ((Finset.range n).filter (fun c => avoid n x y c)).card + 4 = n + 2 * (if x + y + 1 = n then 1 else 0) +
      (if 2 * x + 1 = n then 1 else 0) + (if 2 * y + 1 = n then 1 else 0) := by
  have hs := Finset.card_filter_add_card_filter_not (s := Finset.range n) (fun c => avoid n x y c)
  rw [Finset.card_range] at hs
  by_cases h1 : x + y + 1 = n
  · have hT : (Finset.range n).filter (fun c => ¬ avoid n x y c) = {x, y} := by
      ext c
      rw [Finset.mem_filter, Finset.mem_range]
      simp only [avoid, Finset.mem_insert, Finset.mem_singleton]
      omega
    rw [hT, Finset.card_pair (by omega)] at hs
    simp only [h1, if_true, show ¬ 2 * x + 1 = n by omega, show ¬ 2 * y + 1 = n by omega, if_false]
    omega
  · by_cases h2 : 2 * x + 1 = n
    · have hT : (Finset.range n).filter (fun c => ¬ avoid n x y c) = {x, y, n - 1 - y} := by
        ext c
        rw [Finset.mem_filter, Finset.mem_range]
        simp only [avoid, Finset.mem_insert, Finset.mem_singleton]
        omega
      rw [hT, Finset.card_insert_of_notMem (by simp only [Finset.mem_insert, Finset.mem_singleton]; omega),
        Finset.card_pair (by omega)] at hs
      simp only [h1, h2, if_true, show ¬ 2 * y + 1 = n by omega, if_false]
      omega
    · by_cases h3 : 2 * y + 1 = n
      · have hT : (Finset.range n).filter (fun c => ¬ avoid n x y c) = {x, y, n - 1 - x} := by
          ext c
          rw [Finset.mem_filter, Finset.mem_range]
          simp only [avoid, Finset.mem_insert, Finset.mem_singleton]
          omega
        rw [hT, Finset.card_insert_of_notMem (by simp only [Finset.mem_insert, Finset.mem_singleton]; omega),
          Finset.card_pair (by omega)] at hs
        simp only [h1, h2, h3, if_true, if_false]
        omega
      · have hT : (Finset.range n).filter (fun c => ¬ avoid n x y c) = {x, y, n - 1 - x, n - 1 - y} := by
          ext c
          rw [Finset.mem_filter, Finset.mem_range]
          simp only [avoid, Finset.mem_insert, Finset.mem_singleton]
          omega
        rw [hT, Finset.card_insert_of_notMem (by simp only [Finset.mem_insert, Finset.mem_singleton]; omega),
          Finset.card_insert_of_notMem (by simp only [Finset.mem_insert, Finset.mem_singleton]; omega),
          Finset.card_pair (by omega)] at hs
        simp only [h1, h2, h3, if_false]
        omega

/-- The count of one pair x < y, as a polynomial in n and the indicators of the coincidences. -/
theorem pair_val (n x y : ℕ) (hxy : x < y) (hy : y < n) (hn : 4 ≤ n) :
    ((((Finset.range n).filter (fun c => avoid n x y c)).card.choose 2 : ℕ) : ℚ) =
      ((n : ℚ) - 4) * (n - 5) / 2 + (2 * n - 7) * (if x + y + 1 = n then 1 else 0) +
        (n - 4) * ((if 2 * x + 1 = n then 1 else 0) + (if 2 * y + 1 = n then 1 else 0)) := by
  have hc := card_S n x y hxy hy
  rw [Nat.cast_choose_two]
  by_cases h1 : x + y + 1 = n
  · have h2 : ¬ 2 * x + 1 = n := by omega
    have h3 : ¬ 2 * y + 1 = n := by omega
    simp only [h1, h2, h3, if_true, if_false] at hc ⊢
    have : ((Finset.range n).filter (fun c => avoid n x y c)).card = n - 2 := by omega
    rw [this, Nat.cast_sub (by omega)]
    push_cast
    ring
  · by_cases h2 : 2 * x + 1 = n
    · have h3 : ¬ 2 * y + 1 = n := by omega
      simp only [h1, h2, h3, if_true, if_false] at hc ⊢
      have : ((Finset.range n).filter (fun c => avoid n x y c)).card = n - 3 := by omega
      rw [this, Nat.cast_sub (by omega)]
      push_cast
      ring
    · by_cases h3 : 2 * y + 1 = n
      · simp only [h1, h2, h3, if_true, if_false] at hc ⊢
        have : ((Finset.range n).filter (fun c => avoid n x y c)).card = n - 3 := by omega
        rw [this, Nat.cast_sub (by omega)]
        push_cast
        ring
      · simp only [h1, h2, h3, if_false] at hc ⊢
        have : ((Finset.range n).filter (fun c => avoid n x y c)).card = n - 4 := by omega
        rw [this, Nat.cast_sub (by omega)]
        push_cast
        ring

theorem P1 (n : ℕ) :
    (∑ x ∈ Finset.range n, ∑ y ∈ Finset.range n, if x < y then 1 else 0) = n.choose 2 := by
  have h := card_lt_pairs (Finset.range n)
  rw [Finset.card_range] at h
  rw [← h, Finset.card_filter, Finset.sum_product]

theorem P2 (n : ℕ) :
    (∑ x ∈ Finset.range n, ∑ y ∈ Finset.range n, if x < y ∧ x + y + 1 = n then 1 else 0) = n / 2 := by
  have h : ∀ x ∈ Finset.range n, (∑ y ∈ Finset.range n, if x < y ∧ x + y + 1 = n then 1 else 0) =
      if 2 * x + 2 ≤ n then 1 else 0 := by
    intro x hx
    rw [Finset.mem_range] at hx
    rw [Finset.sum_eq_single (n - 1 - x)]
    · split_ifs <;> omega
    · intro y _ hy
      rw [if_neg]
      omega
    · intro h
      exact absurd (Finset.mem_range.2 (by omega)) h
  rw [Finset.sum_congr rfl h, Finset.sum_boole, Nat.cast_id]
  have : (Finset.range n).filter (fun x => 2 * x + 2 ≤ n) = Finset.range (n / 2) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [this, Finset.card_range]

theorem P3 (n : ℕ) :
    (∑ x ∈ Finset.range n, ∑ y ∈ Finset.range n, if x < y ∧ 2 * x + 1 = n then 1 else 0) =
      if n % 2 = 1 then n - 1 - n / 2 else 0 := by
  have h : ∀ x ∈ Finset.range n, (∑ y ∈ Finset.range n, if x < y ∧ 2 * x + 1 = n then 1 else 0) =
      if 2 * x + 1 = n then n - 1 - x else 0 := by
    intro x hx
    rw [Finset.mem_range] at hx
    split_ifs with hx1
    · simp only [hx1, and_true]
      rw [Finset.sum_boole, Nat.cast_id]
      have : (Finset.range n).filter (fun y => x < y) = Finset.Ioo x n := by
        ext y
        simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ioo]
        omega
      rw [this, Nat.card_Ioo]
      omega
    · refine Finset.sum_eq_zero (fun y _ => ?_)
      rw [if_neg]
      tauto
  rw [Finset.sum_congr rfl h]
  split_ifs with hn
  · rw [Finset.sum_eq_single (n / 2)]
    · rw [if_pos (by omega)]
    · intro x _ hx
      rw [if_neg]
      omega
    · intro h
      exact absurd (Finset.mem_range.2 (by omega)) h
  · refine Finset.sum_eq_zero (fun x _ => ?_)
    rw [if_neg]
    omega

theorem P4 (n : ℕ) :
    (∑ x ∈ Finset.range n, ∑ y ∈ Finset.range n, if x < y ∧ 2 * y + 1 = n then 1 else 0) =
      if n % 2 = 1 then n / 2 else 0 := by
  rw [Finset.sum_comm]
  have h : ∀ y ∈ Finset.range n, (∑ x ∈ Finset.range n, if x < y ∧ 2 * y + 1 = n then 1 else 0) =
      if 2 * y + 1 = n then y else 0 := by
    intro y hy
    rw [Finset.mem_range] at hy
    split_ifs with hy1
    · simp only [hy1, and_true]
      rw [Finset.sum_boole, Nat.cast_id]
      have : (Finset.range n).filter (fun x => x < y) = Finset.range y := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_range]
        omega
      rw [this, Finset.card_range]
    · refine Finset.sum_eq_zero (fun x _ => ?_)
      rw [if_neg]
      tauto
  rw [Finset.sum_congr rfl h]
  split_ifs with hn
  · rw [Finset.sum_eq_single (n / 2)]
    · rw [if_pos (by omega)]
    · intro x _ hx
      rw [if_neg]
      omega
    · intro h
      exact absurd (Finset.mem_range.2 (by omega)) h
  · refine Finset.sum_eq_zero (fun x _ => ?_)
    rw [if_neg]
    omega

/-- The count for n >= 4, by the kinds of pairs x < y. -/
theorem a_formula (n : ℕ) (hn : 4 ≤ n) :
    (a n : ℚ) = ((n.choose 2 : ℕ) : ℚ) * (((n : ℚ) - 4) * (n - 5) / 2) +
      (2 * n - 7) * ((n / 2 : ℕ) : ℚ) +
      (n - 4) * ((if n % 2 = 1 then n - 1 - n / 2 else 0 : ℕ) : ℚ) +
      (n - 4) * ((if n % 2 = 1 then n / 2 else 0 : ℕ) : ℚ) := by
  have q1 : ((n.choose 2 : ℕ) : ℚ) =
      ∑ x ∈ Finset.range n, ∑ y ∈ Finset.range n, if x < y then (1 : ℚ) else 0 := by
    exact_mod_cast (P1 n).symm
  have q2 : ((n / 2 : ℕ) : ℚ) =
      ∑ x ∈ Finset.range n, ∑ y ∈ Finset.range n, if x < y ∧ x + y + 1 = n then (1 : ℚ) else 0 := by
    exact_mod_cast (P2 n).symm
  have q3 : ((if n % 2 = 1 then n - 1 - n / 2 else 0 : ℕ) : ℚ) =
      ∑ x ∈ Finset.range n, ∑ y ∈ Finset.range n, if x < y ∧ 2 * x + 1 = n then (1 : ℚ) else 0 := by
    exact_mod_cast (P3 n).symm
  have q4 : ((if n % 2 = 1 then n / 2 else 0 : ℕ) : ℚ) =
      ∑ x ∈ Finset.range n, ∑ y ∈ Finset.range n, if x < y ∧ 2 * y + 1 = n then (1 : ℚ) else 0 := by
    exact_mod_cast (P4 n).symm
  rw [q1, q2, q3, q4, a_sum]
  simp only [inner_eq, Nat.cast_sum, Nat.cast_ite, Nat.cast_zero]
  simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun x hx => Finset.sum_congr rfl (fun y hy => ?_))
  rw [Finset.mem_range] at hx hy
  by_cases hxy : x < y
  · rw [if_pos hxy, pair_val n x y hxy hy hn]
    simp only [hxy, true_and, if_true]
    split_ifs <;> ring
  · simp only [hxy, false_and, if_false]
    ring

theorem small (n : ℕ) (hn : n < 4) : a n = 0 := by
  interval_cases n <;> decide

/-- Barker's formula for even n. -/
theorem even_form (m : ℕ) : (a (2 * m) : ℚ) = (((2 * m : ℕ) : ℚ) ^ 4 - 10 * ((2 * m : ℕ) : ℚ) ^ 3 +
    33 * ((2 * m : ℕ) : ℚ) ^ 2 - 34 * ((2 * m : ℕ) : ℚ)) / 4 := by
  rcases Nat.lt_or_ge m 2 with hm | hm
  · interval_cases m
    · rw [small 0 (by norm_num)]
      norm_num
    · rw [small 2 (by norm_num)]
      norm_num
  · rw [a_formula _ (by omega), Nat.cast_choose_two]
    have h1 : 2 * m / 2 = m := by omega
    have h2 : ¬ (2 * m) % 2 = 1 := by omega
    rw [h1]
    simp only [h2, if_false]
    push_cast
    ring

/-- Barker's formula for odd n. -/
theorem odd_form (m : ℕ) : (a (2 * m + 1) : ℚ) = (((2 * m + 1 : ℕ) : ℚ) ^ 4 -
    10 * ((2 * m + 1 : ℕ) : ℚ) ^ 3 + 37 * ((2 * m + 1 : ℕ) : ℚ) ^ 2 - 58 * ((2 * m + 1 : ℕ) : ℚ) + 30) / 4 := by
  rcases Nat.lt_or_ge m 2 with hm | hm
  · interval_cases m
    · rw [small 1 (by norm_num)]
      norm_num
    · rw [small 3 (by norm_num)]
      norm_num
  · rw [a_formula _ (by omega), Nat.cast_choose_two]
    have h1 : (2 * m + 1) / 2 = m := by omega
    have h2 : (2 * m + 1) % 2 = 1 := by omega
    have h3 : 2 * m + 1 - 1 - m = m := by omega
    rw [h1]
    simp only [h2, if_true, h3]
    push_cast
    ring

theorem even_q (n : ℕ) (h : Even n) :
    (a n : ℚ) = ((n : ℚ) ^ 4 - 10 * n ^ 3 + 33 * n ^ 2 - 34 * n) / 4 := by
  obtain ⟨m, rfl⟩ := h
  rw [show m + m = 2 * m by ring]
  exact even_form m

theorem odd_q (n : ℕ) (h : Odd n) :
    (a n : ℚ) = ((n : ℚ) ^ 4 - 10 * n ^ 3 + 37 * n ^ 2 - 58 * n + 30) / 4 := by
  obtain ⟨m, rfl⟩ := h
  exact odd_form m

/-- Barker's recurrence, for n > 7. -/
theorem recurrence (n : ℕ) (hn : 7 < n) :
    (a n : ℤ) = 2 * a (n - 1) + 2 * a (n - 2) - 6 * a (n - 3) + 6 * a (n - 5) - 2 * a (n - 6) -
      2 * a (n - 7) + a (n - 8) := by
  have key : (a n : ℚ) = 2 * a (n - 1) + 2 * a (n - 2) - 6 * a (n - 3) + 6 * a (n - 5) - 2 * a (n - 6) -
      2 * a (n - 7) + a (n - 8) := by
    rcases Nat.even_or_odd' n with ⟨m, rfl | rfl⟩
    · obtain ⟨j, rfl⟩ : ∃ j, m = j + 4 := ⟨m - 4, by omega⟩
      rw [show 2 * (j + 4) - 1 = 2 * (j + 3) + 1 by omega, show 2 * (j + 4) - 2 = 2 * (j + 3) by omega,
        show 2 * (j + 4) - 3 = 2 * (j + 2) + 1 by omega, show 2 * (j + 4) - 5 = 2 * (j + 1) + 1 by omega,
        show 2 * (j + 4) - 6 = 2 * (j + 1) by omega, show 2 * (j + 4) - 7 = 2 * j + 1 by omega,
        show 2 * (j + 4) - 8 = 2 * j by omega]
      simp only [even_form, odd_form]
      push_cast
      ring
    · obtain ⟨j, rfl⟩ : ∃ j, m = j + 4 := ⟨m - 4, by omega⟩
      rw [show 2 * (j + 4) + 1 - 1 = 2 * (j + 4) by omega,
        show 2 * (j + 4) + 1 - 2 = 2 * (j + 3) + 1 by omega,
        show 2 * (j + 4) + 1 - 3 = 2 * (j + 3) by omega, show 2 * (j + 4) + 1 - 5 = 2 * (j + 2) by omega,
        show 2 * (j + 4) + 1 - 6 = 2 * (j + 1) + 1 by omega, show 2 * (j + 4) + 1 - 7 = 2 * (j + 1) by omega,
        show 2 * (j + 4) + 1 - 8 = 2 * j + 1 by omega]
      simp only [even_form, odd_form]
      push_cast
      ring
  exact_mod_cast key

lemma values : a 4 = 2 ∧ a 5 = 10 ∧ a 6 = 30 ∧ a 7 = 102 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h := even_form 2
    norm_num at h
    exact_mod_cast h
  · have h := odd_form 2
    norm_num at h
    exact_mod_cast h
  · have h := even_form 3
    norm_num at h
    exact_mod_cast h
  · have h := odd_form 3
    norm_num at h
    exact_mod_cast h

/-- Barker's g.f., as A(x) (1 - x)^5 (1 + x)^3 = 2x^4 (1 + 3x + 3x^2 + 17x^3) in Z[[x]]. -/
theorem gf : PowerSeries.mk (fun n => (a n : ℤ)) * ((1 - X) ^ 5 * (1 + X) ^ 3) =
    2 * X ^ 4 * (1 + 3 * X + 3 * X ^ 2 + 17 * X ^ 3) := by
  set A : ℤ⟦X⟧ := PowerSeries.mk (fun n => (a n : ℤ)) with hA
  have e1 : A * ((1 - X) ^ 5 * (1 + X) ^ 3) = A - C 2 * (A * X ^ 1) - C 2 * (A * X ^ 2) +
      C 6 * (A * X ^ 3) - C 6 * (A * X ^ 5) + C 2 * (A * X ^ 6) + C 2 * (A * X ^ 7) - A * X ^ 8 := by
    simp only [map_ofNat]; ring
  have e2 : (2 * X ^ 4 * (1 + 3 * X + 3 * X ^ 2 + 17 * X ^ 3) : ℤ⟦X⟧) =
      X ^ 4 * C 2 + X ^ 5 * C 6 + X ^ 6 * C 6 + X ^ 7 * C 34 := by
    simp only [map_ofNat]; ring
  rw [e1, e2]
  ext n
  have hc : ∀ k, coeff k A = (a k : ℤ) := fun k => by rw [hA, coeff_mk]
  simp only [map_add, map_sub, coeff_C_mul, coeff_mul_C, coeff_X_pow, coeff_mul_X_pow', hc]
  obtain ⟨v4, v5, v6, v7⟩ := values
  have v0 := small 0 (by norm_num)
  have v1 := small 1 (by norm_num)
  have v2 := small 2 (by norm_num)
  have v3 := small 3 (by norm_num)
  rcases Nat.lt_or_ge n 8 with hn | hn
  · interval_cases n <;> simp [v0, v1, v2, v3, v4, v5, v6, v7]
  · obtain ⟨q, rfl⟩ : ∃ q, n = q + 8 := ⟨n - 8, by omega⟩
    have h := recurrence (q + 8) (by omega)
    simp only [show q + 8 - 1 = q + 7 by omega, show q + 8 - 2 = q + 6 by omega,
      show q + 8 - 3 = q + 5 by omega, show q + 8 - 5 = q + 3 by omega, show q + 8 - 6 = q + 2 by omega,
      show q + 8 - 7 = q + 1 by omega, show q + 8 - 8 = q by omega] at h ⊢
    simp only [show 1 ≤ q + 8 by omega, show 2 ≤ q + 8 by omega, show 3 ≤ q + 8 by omega,
      show 5 ≤ q + 8 by omega, show 6 ≤ q + 8 by omega, show 7 ≤ q + 8 by omega,
      show 8 ≤ q + 8 by omega, show ¬ q + 8 = 4 by omega, show ¬ q + 8 = 5 by omega,
      show ¬ q + 8 = 6 by omega, show ¬ q + 8 = 7 by omega, if_true, if_false]
    rw [h]
    ring

theorem e (m v : ℕ) (h : (((2 * m : ℕ) : ℚ) ^ 4 - 10 * ((2 * m : ℕ) : ℚ) ^ 3 + 33 * ((2 * m : ℕ) : ℚ) ^ 2 -
    34 * ((2 * m : ℕ) : ℚ)) / 4 = v) : a (2 * m) = v := by
  have := even_form m
  rw [h] at this
  exact_mod_cast this

theorem o (m v : ℕ) (h : (((2 * m + 1 : ℕ) : ℚ) ^ 4 - 10 * ((2 * m + 1 : ℕ) : ℚ) ^ 3 +
    37 * ((2 * m + 1 : ℕ) : ℚ) ^ 2 - 58 * ((2 * m + 1 : ℕ) : ℚ) + 30) / 4 = v) : a (2 * m + 1) = v := by
  have := odd_form m
  rw [h] at this
  exact_mod_cast this

/-- Controls: the entry's data a(0..44). -/
theorem controls : a 0 = 0 ∧ a 1 = 0 ∧ a 2 = 0 ∧ a 3 = 0 ∧ a 4 = 2 ∧ a 5 = 10 ∧ a 6 = 30 ∧
    a 7 = 102 ∧ a 8 = 204 ∧ a 9 = 444 ∧ a 10 = 740 ∧ a 11 = 1300 ∧ a 12 = 1950 ∧ a 13 = 3030 ∧
    a 14 = 4242 ∧ a 15 = 6090 ∧ a 16 = 8120 ∧ a 17 = 11032 ∧ a 18 = 14184 ∧ a 19 = 18504 ∧
    a 20 = 23130 ∧ a 21 = 29250 ∧ a 22 = 35750 ∧ a 23 = 44110 ∧ a 24 = 52932 ∧ a 25 = 64020 ∧
    a 26 = 75660 ∧ a 27 = 90012 ∧ a 28 = 105014 ∧ a 29 = 123214 ∧ a 30 = 142170 ∧ a 31 = 164850 ∧
    a 32 = 188400 ∧ a 33 = 216240 ∧ a 34 = 245072 ∧ a 35 = 278800 ∧ a 36 = 313650 ∧ a 37 = 354042 ∧
    a 38 = 395694 ∧ a 39 = 443574 ∧ a 40 = 492860 ∧ a 41 = 549100 ∧ a 42 = 606900 ∧ a 43 = 672420 ∧
    a 44 = 739662 :=
  ⟨small 0 (by norm_num), small 1 (by norm_num), small 2 (by norm_num), small 3 (by norm_num),
    e 2 2 (by norm_num), o 2 10 (by norm_num), e 3 30 (by norm_num), o 3 102 (by norm_num),
    e 4 204 (by norm_num), o 4 444 (by norm_num), e 5 740 (by norm_num), o 5 1300 (by norm_num),
    e 6 1950 (by norm_num), o 6 3030 (by norm_num), e 7 4242 (by norm_num), o 7 6090 (by norm_num),
    e 8 8120 (by norm_num), o 8 11032 (by norm_num), e 9 14184 (by norm_num),
    o 9 18504 (by norm_num), e 10 23130 (by norm_num), o 10 29250 (by norm_num),
    e 11 35750 (by norm_num), o 11 44110 (by norm_num), e 12 52932 (by norm_num),
    o 12 64020 (by norm_num), e 13 75660 (by norm_num), o 13 90012 (by norm_num),
    e 14 105014 (by norm_num), o 14 123214 (by norm_num), e 15 142170 (by norm_num),
    o 15 164850 (by norm_num), e 16 188400 (by norm_num), o 16 216240 (by norm_num),
    e 17 245072 (by norm_num), o 17 278800 (by norm_num), e 18 313650 (by norm_num),
    o 18 354042 (by norm_num), e 19 395694 (by norm_num), o 19 443574 (by norm_num),
    e 20 492860 (by norm_num), o 20 549100 (by norm_num), e 21 606900 (by norm_num),
    o 21 672420 (by norm_num), e 22 739662 (by norm_num)⟩

/-- All of Barker's conjectures. -/
theorem conjecture :
    PowerSeries.mk (fun n => (a n : ℤ)) * ((1 - X) ^ 5 * (1 + X) ^ 3) =
      2 * X ^ 4 * (1 + 3 * X + 3 * X ^ 2 + 17 * X ^ 3) ∧
    (∀ n : ℕ, Even n → (a n : ℚ) = ((n : ℚ) ^ 4 - 10 * n ^ 3 + 33 * n ^ 2 - 34 * n) / 4) ∧
    (∀ n : ℕ, Odd n → (a n : ℚ) = ((n : ℚ) ^ 4 - 10 * n ^ 3 + 37 * n ^ 2 - 58 * n + 30) / 4) ∧
    ∀ n : ℕ, 7 < n → (a n : ℤ) = 2 * a (n - 1) + 2 * a (n - 2) - 6 * a (n - 3) + 6 * a (n - 5) -
      2 * a (n - 6) - 2 * a (n - 7) + a (n - 8) :=
  ⟨gf, even_q, odd_q, recurrence⟩

end OMA.S_oeis_a285956

theorem OMA.solution : type_of% @OMA.S_oeis_a285956.main :=
  OMA.S_oeis_a285956.conjecture
