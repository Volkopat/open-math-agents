import OMAStatements.S_oeis_a215191

namespace OMA.S_oeis_a215191

open PowerSeries Finset




theorem good_iff (x : Fin 4 → ℕ) : good x ↔
    x 1 ≠ x 2 ∧ (x 0 ≠ x 1 ∧ x 3 ≠ x 2 ∧ x 0 + x 1 ≠ x 2 + x 3) := by
  constructor
  · intro h
    have h1 := h 0 1 (by norm_num) (by norm_num)
    have h2 := h 1 1 (by norm_num) (by norm_num)
    have h3 := h 2 1 (by norm_num) (by norm_num)
    have h4 := h 0 2 (by norm_num) (by norm_num)
    simp [get, Finset.sum_range_succ] at h1 h2 h3 h4
    exact ⟨h2, h1, fun e => h3 e.symm, h4⟩
  · rintro ⟨h2, h1, h3, h4⟩ i k hk hik
    rcases (show (i = 0 ∧ k = 1) ∨ (i = 1 ∧ k = 1) ∨ (i = 2 ∧ k = 1) ∨ (i = 0 ∧ k = 2) by omega) with
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp [get, Finset.sum_range_succ] <;> omega

/-- The middle pair (x1, x2) and the arms (x0, x3) of a good array with values in 0..n. -/
def T (n : ℕ) : Finset ((ℕ × ℕ) × (ℕ × ℕ)) :=
  ((range (n + 1) ×ˢ range (n + 1)) ×ˢ (range (n + 1) ×ˢ range (n + 1))).filter fun t =>
    t.1.1 ≠ t.1.2 ∧ (t.2.1 ≠ t.1.1 ∧ t.2.2 ≠ t.1.2 ∧ t.2.1 + t.1.1 ≠ t.1.2 + t.2.2)

/-- The array of a tuple of T. -/
def ψ (t : (ℕ × ℕ) × (ℕ × ℕ)) : Fin 4 → ℕ := ![t.2.1, t.1.1, t.1.2, t.2.2]

theorem ψ_inj : Function.Injective ψ := by
  rintro ⟨⟨a1, a2⟩, ⟨a0, a3⟩⟩ ⟨⟨b1, b2⟩, ⟨b0, b3⟩⟩ h
  have e0 := congrFun h 0
  have e1 := congrFun h 1
  have e2 := congrFun h 2
  have e3 := congrFun h 3
  simp only [ψ, Matrix.cons_val] at e0 e1 e2 e3
  subst e0 e1 e2 e3
  rfl

theorem set_eq (n : ℕ) : {x : Fin 4 → ℕ | (∀ i, x i ≤ n) ∧ good x} = ψ '' (T n : Set _) := by
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_image, Finset.mem_coe, T, Finset.mem_filter,
    Finset.mem_product, Finset.mem_range]
  constructor
  · rintro ⟨hb, hg⟩
    rw [good_iff] at hg
    refine ⟨((x 1, x 2), (x 0, x 3)), ⟨⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩, hg⟩, ?_⟩
    · exact Nat.lt_succ_of_le (hb 1)
    · exact Nat.lt_succ_of_le (hb 2)
    · exact Nat.lt_succ_of_le (hb 0)
    · exact Nat.lt_succ_of_le (hb 3)
    · funext i
      fin_cases i <;> rfl
  · rintro ⟨⟨⟨x1, x2⟩, ⟨x0, x3⟩⟩, ⟨⟨⟨h1, h2⟩, ⟨h0, h3⟩⟩, hc⟩, rfl⟩
    dsimp only at h0 h1 h2 h3
    refine ⟨fun i => ?_, ?_⟩
    · fin_cases i <;> simp [ψ] <;> omega
    · rw [good_iff]
      exact hc

theorem a_eq (n : ℕ) : a n = (T n).card := by
  unfold a
  rw [set_eq, Set.ncard_image_of_injective _ ψ_inj, Set.ncard_coe_finset]

/-- The completions (x0, x3) of a middle pair (x1, x2). -/
def N (n x1 x2 : ℕ) : ℕ :=
  ((range (n + 1) ×ˢ range (n + 1)).filter fun l => l.1 ≠ x1 ∧ l.2 ≠ x2 ∧ l.1 + x1 ≠ x2 + l.2).card

theorem card_T (n : ℕ) : (T n).card = ∑ m ∈ range (n + 1) ×ˢ range (n + 1),
    if m.1 ≠ m.2 then N n m.1 m.2 else 0 := by
  unfold T N
  rw [card_filter, sum_product]
  refine sum_congr rfl (fun m _ => ?_)
  by_cases hP : m.1 ≠ m.2
  · rw [if_pos hP, card_filter]
    refine sum_congr rfl (fun l _ => ?_)
    simp only [hP, ne_eq, not_false_eq_true, true_and]
  · rw [if_neg hP]
    simp [hP]

/-- The values x0 in 0..n with x2 ≤ x0 + x1 ≤ n + x2 (those with a partner x3 = x0 + x1 - x2). -/
theorem card_window (n x1 x2 : ℕ) (h1 : x1 ≤ n) (h2 : x2 ≤ n) :
    (((range (n + 1)).filter fun x0 => x2 ≤ x0 + x1 ∧ x0 + x1 ≤ n + x2).card : ℤ) =
      n + 1 - |(x1 : ℤ) - x2| := by
  have e : (range (n + 1)).filter (fun x0 => x2 ≤ x0 + x1 ∧ x0 + x1 ≤ n + x2) =
      Finset.Icc (x2 - x1) (n - (x1 - x2)) := by
    ext x0
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
    omega
  rw [e, Nat.card_Icc]
  rcases le_total x1 x2 with h | h
  · rw [abs_of_nonpos (by omega)]
    omega
  · rw [abs_of_nonneg (by omega)]
    omega

theorem N_val (n x1 x2 : ℕ) (h1 : x1 ≤ n) (h2 : x2 ≤ n) (h12 : x1 ≠ x2) :
    (N n x1 x2 : ℤ) = n ^ 2 - (n + 1 - |(x1 : ℤ) - x2|) +
      (if x2 ≤ 2 * x1 ∧ 2 * x1 ≤ n + x2 then 1 else 0) +
      (if x1 ≤ 2 * x2 ∧ 2 * x2 ≤ n + x1 then 1 else 0) := by
  -- count per x0: x3 avoids x2 and the partner x0 + x1 - x2
  have inner : ∀ x0 ∈ range (n + 1), x0 ≠ x1 →
      (((range (n + 1)).filter fun x3 => x3 ≠ x2 ∧ x0 + x1 ≠ x2 + x3).card : ℤ) =
        n - (if x2 ≤ x0 + x1 ∧ x0 + x1 ≤ n + x2 ∧ x0 + x1 ≠ 2 * x2 then 1 else 0) := by
    intro x0 hx0 _
    rw [mem_range] at hx0
    by_cases hw : x2 ≤ x0 + x1 ∧ x0 + x1 ≤ n + x2 ∧ x0 + x1 ≠ 2 * x2
    · rw [if_pos hw]
      have e : (range (n + 1)).filter (fun x3 => x3 ≠ x2 ∧ x0 + x1 ≠ x2 + x3) =
          ((range (n + 1)).erase x2).erase (x0 + x1 - x2) := by
        ext x3
        simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_erase]
        omega
      rw [e, Finset.card_erase_of_mem, Finset.card_erase_of_mem, Finset.card_range]
      · omega
      · rw [mem_range]; omega
      · rw [mem_erase, mem_range]; omega
    · rw [if_neg hw]
      have e : (range (n + 1)).filter (fun x3 => x3 ≠ x2 ∧ x0 + x1 ≠ x2 + x3) =
          (range (n + 1)).erase x2 := by
        ext x3
        simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_erase]
        omega
      rw [e, Finset.card_erase_of_mem (by rw [mem_range]; omega), Finset.card_range]
      push_cast
      ring
  have hN : (N n x1 x2 : ℤ) = ∑ x0 ∈ range (n + 1),
      if x0 ≠ x1 then (n - (if x2 ≤ x0 + x1 ∧ x0 + x1 ≤ n + x2 ∧ x0 + x1 ≠ 2 * x2 then 1 else 0) : ℤ)
      else 0 := by
    unfold N
    rw [card_filter, sum_product]
    push_cast
    refine sum_congr rfl (fun x0 hx0 => ?_)
    by_cases h0 : x0 ≠ x1
    · rw [if_pos h0, ← inner x0 hx0 h0, card_filter]
      push_cast
      refine sum_congr rfl (fun x3 _ => ?_)
      simp only [h0, ne_eq, not_false_eq_true, true_and]
    · rw [if_neg h0]
      refine sum_eq_zero (fun x3 _ => ?_)
      simp only [ne_eq, not_not] at h0
      simp [h0]
  -- split the sum: n for each x0 ≠ x1, minus the window count without x1 and 2 x2 - x1
  have hsplit : ∀ x0, (if x0 ≠ x1 then (n - (if x2 ≤ x0 + x1 ∧ x0 + x1 ≤ n + x2 ∧
      x0 + x1 ≠ 2 * x2 then 1 else 0) : ℤ) else 0) =
      (n : ℤ) - (if x0 = x1 then (n : ℤ) else 0) -
        (if x2 ≤ x0 + x1 ∧ x0 + x1 ≤ n + x2 then 1 else 0) +
        (if x0 = x1 ∧ x2 ≤ x0 + x1 ∧ x0 + x1 ≤ n + x2 then 1 else 0) +
        (if x0 + x1 = 2 * x2 ∧ x2 ≤ x0 + x1 ∧ x0 + x1 ≤ n + x2 then 1 else 0) := by
    intro x0
    by_cases ha : x0 = x1
    · subst ha
      have : ¬ (x0 + x0 = 2 * x2) := by omega
      by_cases hb : x2 ≤ x0 + x0 ∧ x0 + x0 ≤ n + x2 <;> simp [hb, this]
    · by_cases hb : x2 ≤ x0 + x1 ∧ x0 + x1 ≤ n + x2 <;> by_cases hc : x0 + x1 = 2 * x2 <;>
        simp [ha, hb, hc]
  rw [hN, sum_congr rfl (fun x0 _ => hsplit x0)]
  simp only [sum_add_distrib, sum_sub_distrib, sum_const, card_range, nsmul_eq_mul]
  rw [sum_ite_eq' (range (n + 1)) x1 (fun _ => (n : ℤ)), if_pos (mem_range.2 (by omega))]
  have w := card_window n x1 x2 h1 h2
  rw [Finset.card_filter] at w
  push_cast at w
  rw [w]
  have p1 : ∑ x0 ∈ range (n + 1), (if x0 = x1 ∧ x2 ≤ x0 + x1 ∧ x0 + x1 ≤ n + x2 then (1 : ℤ) else 0) =
      if x2 ≤ 2 * x1 ∧ 2 * x1 ≤ n + x2 then 1 else 0 := by
    rw [sum_eq_single x1]
    · simp only [true_and, two_mul]
    · intro b _ hb
      simp [hb]
    · intro h
      exact absurd (mem_range.2 (by omega)) h
  have p2 : ∑ x0 ∈ range (n + 1),
      (if x0 + x1 = 2 * x2 ∧ x2 ≤ x0 + x1 ∧ x0 + x1 ≤ n + x2 then (1 : ℤ) else 0) =
      if x1 ≤ 2 * x2 ∧ 2 * x2 ≤ n + x1 then 1 else 0 := by
    by_cases hc : x1 ≤ 2 * x2 ∧ 2 * x2 ≤ n + x1
    · rw [if_pos hc, sum_eq_single (2 * x2 - x1)]
      · rw [if_pos (by omega)]
      · intro b _ hb
        rw [if_neg (by omega)]
      · intro h
        exact absurd (mem_range.2 (by omega)) h
    · rw [if_neg hc]
      refine sum_eq_zero (fun b hb => ?_)
      rw [mem_range] at hb
      rw [if_neg (by omega)]
  rw [p1, p2]
  push_cast
  ring

/-- The summand of a(n) over the middle pairs, split into four parts. -/
theorem pt (n : ℕ) : ∀ m ∈ range (n + 1) ×ˢ range (n + 1),
    (if m.1 ≠ m.2 then (N n m.1 m.2 : ℤ) else 0) =
      (if m.1 ≠ m.2 then ((n : ℤ) ^ 2 - n - 1) else 0) + |(m.1 : ℤ) - m.2| +
      (if m.1 ≠ m.2 ∧ (m.2 ≤ 2 * m.1 ∧ 2 * m.1 ≤ n + m.2) then 1 else 0) +
      (if m.1 ≠ m.2 ∧ (m.1 ≤ 2 * m.2 ∧ 2 * m.2 ≤ n + m.1) then 1 else 0) := by
  rintro ⟨x1, x2⟩ hm
  simp only [mem_product, mem_range] at hm
  dsimp only
  by_cases h : x1 = x2
  · subst h
    simp
  · have hN := N_val n x1 x2 (by omega) (by omega) h
    simp only [ne_eq, h, not_false_eq_true, true_and, ↓reduceIte]
    rw [hN]
    ring

theorem S1_val (n : ℕ) (c : ℤ) :
    ∑ m ∈ range (n + 1) ×ˢ range (n + 1), (if m.1 ≠ m.2 then c else 0) = c * (((n : ℤ) + 1) * n) := by
  simp only [sum_product]
  have row : ∀ x1 ∈ range (n + 1), ∑ x2 ∈ range (n + 1), (if x1 ≠ x2 then c else 0) = c * n := by
    intro x1 hx1
    have e : ∀ x2, (if x1 ≠ x2 then c else 0) = c - if x1 = x2 then c else 0 := by
      intro x2
      by_cases h : x1 = x2 <;> simp [h]
    simp only [e, sum_sub_distrib, sum_const, card_range, sum_ite_eq, hx1, ↓reduceIte, nsmul_eq_mul]
    push_cast
    ring
  rw [sum_congr rfl row, sum_const, card_range, nsmul_eq_mul]
  push_cast
  ring

theorem gauss (n : ℕ) : 2 * ∑ x ∈ range (n + 1), ((n : ℤ) + 1 - x) = (n + 1) * (n + 2) := by
  have h : ∀ m : ℕ, 2 * ∑ x ∈ range m, (x : ℤ) = m * (m - 1) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [sum_range_succ, mul_add, ih]
      push_cast
      ring
  rw [sum_sub_distrib, sum_const, card_range, nsmul_eq_mul, mul_sub, h]
  push_cast
  ring

theorem D_val (n : ℕ) : 3 * ∑ m ∈ range (n + 1) ×ˢ range (n + 1), |(m.1 : ℤ) - m.2| =
    n * (n + 1) * (n + 2) := by
  simp only [sum_product]
  induction n with
  | zero => simp
  | succ n ih =>
    have inner : ∀ x1 : ℕ, ∑ x2 ∈ range (n + 1 + 1), |(x1 : ℤ) - x2| =
        ∑ x2 ∈ range (n + 1), |(x1 : ℤ) - x2| + |(x1 : ℤ) - ((n + 1 : ℕ) : ℤ)| :=
      fun x1 => sum_range_succ _ _
    have g1 : ∑ x1 ∈ range (n + 1), |(x1 : ℤ) - ((n + 1 : ℕ) : ℤ)| =
        ∑ x ∈ range (n + 1), ((n : ℤ) + 1 - x) := by
      refine sum_congr rfl (fun x hx => ?_)
      rw [mem_range] at hx
      rw [abs_of_nonpos (by push_cast; omega)]
      push_cast
      ring
    have g2 : ∑ x2 ∈ range (n + 1 + 1), |((n + 1 : ℕ) : ℤ) - x2| =
        ∑ x ∈ range (n + 1), ((n : ℤ) + 1 - x) := by
      rw [sum_range_succ, sub_self, abs_zero, add_zero]
      refine sum_congr rfl (fun x hx => ?_)
      rw [mem_range] at hx
      rw [abs_of_nonneg (by push_cast; omega)]
      push_cast
      ring
    rw [sum_range_succ, sum_congr rfl (fun x1 _ => inner x1), sum_add_distrib, g1, g2]
    have hg := gauss n
    push_cast
    linear_combination ih + 3 * hg

/-- The number of x2 in 0..n with x2 ≠ x1 and x2 ≤ 2 x1 ≤ n + x2. -/
def tf (n x : ℕ) : ℕ := if 2 * x ≤ n then 2 * x else 2 * n - 2 * x

theorem tent (n : ℕ) : 2 * ∑ x ∈ range (n + 1), tf n x + n % 2 = n ^ 2 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | _ | n
    · simp [tf]
    · simp [tf, sum_range_succ]
    · have h := ih n (by omega)
      have mid : ∀ x ∈ range (n + 1), tf (n + 1 + 1) (x + 1) = tf n x + 2 := by
        intro x hx
        rw [mem_range] at hx
        unfold tf
        split_ifs <;> omega
      have e0 : tf (n + 1 + 1) 0 = 0 := by simp [tf]
      have e1 : tf (n + 1 + 1) (n + 1 + 1) = 0 := by unfold tf; split_ifs <;> omega
      rw [sum_range_succ, sum_range_succ', sum_congr rfl mid, sum_add_distrib, sum_const,
        card_range, smul_eq_mul, e0, e1]
      have e2 : (n + 1 + 1) ^ 2 = n ^ 2 + 4 * n + 4 := by ring
      rw [e2]
      omega

theorem I3_val (n : ℕ) : 2 * ∑ m ∈ range (n + 1) ×ˢ range (n + 1),
    (if m.1 ≠ m.2 ∧ (m.2 ≤ 2 * m.1 ∧ 2 * m.1 ≤ n + m.2) then (1 : ℤ) else 0) =
      (n : ℤ) ^ 2 - ((n % 2 : ℕ) : ℤ) := by
  simp only [sum_product]
  have row : ∀ x1 ∈ range (n + 1), ∑ x2 ∈ range (n + 1),
      (if x1 ≠ x2 ∧ (x2 ≤ 2 * x1 ∧ 2 * x1 ≤ n + x2) then (1 : ℤ) else 0) = (tf n x1 : ℤ) := by
    intro x1 hx1
    rw [mem_range] at hx1
    rw [sum_boole, Nat.cast_inj]
    unfold tf
    by_cases h : 2 * x1 ≤ n
    · rw [if_pos h]
      have e : (range (n + 1)).filter (fun x2 => x1 ≠ x2 ∧ (x2 ≤ 2 * x1 ∧ 2 * x1 ≤ n + x2)) =
          (range (2 * x1 + 1)).erase x1 := by
        ext x2
        simp only [mem_filter, mem_range, mem_erase]
        omega
      rw [e, card_erase_of_mem (by rw [mem_range]; omega), card_range]
      omega
    · rw [if_neg h]
      have e : (range (n + 1)).filter (fun x2 => x1 ≠ x2 ∧ (x2 ≤ 2 * x1 ∧ 2 * x1 ≤ n + x2)) =
          (Icc (2 * x1 - n) n).erase x1 := by
        ext x2
        simp only [mem_filter, mem_range, mem_erase, mem_Icc]
        omega
      rw [e, card_erase_of_mem (by rw [mem_Icc]; omega), Nat.card_Icc]
      omega
  rw [sum_congr rfl row, ← Nat.cast_sum]
  have h' : 2 * ((∑ x ∈ range (n + 1), tf n x : ℕ) : ℤ) + ((n % 2 : ℕ) : ℤ) = (n : ℤ) ^ 2 := by
    exact_mod_cast tent n
  linarith

theorem I4_eq (n : ℕ) : ∑ m ∈ range (n + 1) ×ˢ range (n + 1),
    (if m.1 ≠ m.2 ∧ (m.1 ≤ 2 * m.2 ∧ 2 * m.2 ≤ n + m.1) then (1 : ℤ) else 0) =
    ∑ m ∈ range (n + 1) ×ˢ range (n + 1),
    (if m.1 ≠ m.2 ∧ (m.2 ≤ 2 * m.1 ∧ 2 * m.1 ≤ n + m.2) then (1 : ℤ) else 0) := by
  simp only [sum_product]
  rw [sum_comm]
  refine sum_congr rfl (fun x1 _ => sum_congr rfl (fun x2 _ => ?_))
  by_cases h : x1 = x2
  · subst h
    simp
  · have h' : x2 ≠ x1 := fun e => h e.symm
    simp only [ne_eq, h, h', not_false_eq_true, true_and]

/-- The closed form: 3 a(n) = 3n^4 + n^3 - n - 3 [n odd]. -/
theorem a_closed (n : ℕ) :
    3 * (a n : ℤ) = 3 * (n : ℤ) ^ 4 + (n : ℤ) ^ 3 - n - 3 * ((n % 2 : ℕ) : ℤ) := by
  have h0 : (a n : ℤ) = ∑ m ∈ range (n + 1) ×ˢ range (n + 1),
      (if m.1 ≠ m.2 then (N n m.1 m.2 : ℤ) else 0) := by
    simp only [a_eq, card_T, Nat.cast_sum, Nat.cast_ite, Nat.cast_zero]
  rw [h0, sum_congr rfl (pt n), sum_add_distrib, sum_add_distrib, sum_add_distrib, S1_val, I4_eq]
  have hD := D_val n
  have hI := I3_val n
  linear_combination hD + 3 * hI

theorem val (n v : ℕ) (h : 3 * (n : ℤ) ^ 4 + (n : ℤ) ^ 3 - n - 3 * ((n % 2 : ℕ) : ℤ) = 3 * v) :
    a n = v := by
  have := a_closed n
  rw [h] at this
  omega

theorem a_zero : a 0 = 0 := val 0 0 (by norm_num)

/-- The order-6 recurrence a(n) = 4a(n-1) - 5a(n-2) + 5a(n-4) - 4a(n-5) + a(n-6). -/
theorem rec6 (q : ℕ) : (a (q + 6) : ℤ) =
    4 * a (q + 5) - 5 * a (q + 4) + 5 * a (q + 2) - 4 * a (q + 1) + a q := by
  have h6 := a_closed (q + 6)
  have h5 := a_closed (q + 5)
  have h4 := a_closed (q + 4)
  have h2 := a_closed (q + 2)
  have h1 := a_closed (q + 1)
  have h0 := a_closed q
  rw [show (q + 6) % 2 = q % 2 by omega] at h6
  rw [show (q + 5) % 2 = (q + 1) % 2 by omega] at h5
  rw [show (q + 4) % 2 = q % 2 by omega] at h4
  rw [show (q + 2) % 2 = q % 2 by omega] at h2
  push_cast at h6 h5 h4 h2 h1 h0
  have key : 3 * (a (q + 6) : ℤ) =
      3 * (4 * a (q + 5) - 5 * a (q + 4) + 5 * a (q + 2) - 4 * a (q + 1) + a q) := by
    linear_combination h6 - 4 * h5 + 5 * h4 - 5 * h2 + 4 * h1 - h0
  linarith

/-- Barker's g.f. 2x^2 (9 + 8x + 7x^2) / ((1 - x)^5 (1 + x)), as A(x) (1 - x)^5 (1 + x) =
2x^2 (9 + 8x + 7x^2) in Q[[x]], with A(x) = Sum_{n >= 1} a(n) x^n. -/
theorem gf : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * ((1 - X) ^ 5 * (1 + X)) =
    2 * X ^ 2 * (9 + 8 * X + 7 * X ^ 2) := by
  set A : ℚ⟦X⟧ := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) with hA
  have e1 : A * ((1 - X) ^ 5 * (1 + X)) = A - C 4 * (A * X ^ 1) + C 5 * (A * X ^ 2) -
      C 5 * (A * X ^ 4) + C 4 * (A * X ^ 5) - A * X ^ 6 := by
    simp only [map_ofNat]; ring
  have e2 : (2 * X ^ 2 * (9 + 8 * X + 7 * X ^ 2) : ℚ⟦X⟧) =
      X ^ 2 * C 18 + X ^ 3 * C 16 + X ^ 4 * C 14 := by
    simp only [map_ofNat]; ring
  rw [e1, e2]
  ext n
  have hc : ∀ k, coeff k A = (a k : ℚ) := fun k => by
    rw [hA, coeff_mk]
    split_ifs with h
    · subst h
      rw [a_zero]
      simp
    · rfl
  simp only [map_add, map_sub, coeff_C_mul, coeff_mul_C, coeff_X_pow, coeff_mul_X_pow', hc]
  have v1 : a 1 = 0 := val 1 0 (by norm_num)
  have v2 : a 2 = 18 := val 2 18 (by norm_num)
  have v3 : a 3 = 88 := val 3 88 (by norm_num)
  have v4 : a 4 = 276 := val 4 276 (by norm_num)
  have v5 : a 5 = 664 := val 5 664 (by norm_num)
  rcases Nat.lt_or_ge n 6 with hn | hn
  · interval_cases n <;> simp [v1, v2, v3, v4, v5, a_zero] <;> norm_num
  · obtain ⟨q, rfl⟩ : ∃ q, n = q + 6 := ⟨n - 6, by omega⟩
    have hq : (a (q + 6) : ℚ) =
        4 * a (q + 5) - 5 * a (q + 4) + 5 * a (q + 2) - 4 * a (q + 1) + a q := by
      have h := congrArg (Int.cast : ℤ → ℚ) (rec6 q)
      push_cast at h
      linarith
    simp only [show q + 6 - 1 = q + 5 by omega, show q + 6 - 2 = q + 4 by omega,
      show q + 6 - 4 = q + 2 by omega, show q + 6 - 5 = q + 1 by omega,
      show q + 6 - 6 = q by omega, show 1 ≤ q + 6 by omega, show 2 ≤ q + 6 by omega,
      show 4 ≤ q + 6 by omega, show 5 ≤ q + 6 by omega, show 6 ≤ q + 6 by omega,
      show ¬ q + 6 = 2 by omega, show ¬ q + 6 = 3 by omega, show ¬ q + 6 = 4 by omega,
      if_true, if_false]
    rw [hq]
    ring

theorem even_form (n : ℕ) (hn : n % 2 = 0) : (a n : ℚ) = n * (3 * n ^ 3 + n ^ 2 - 1) / 3 := by
  have h := a_closed n
  rw [hn] at h
  have h' := congrArg (Int.cast : ℤ → ℚ) h
  push_cast at h'
  rw [eq_div_iff (by norm_num : (3 : ℚ) ≠ 0)]
  linear_combination h'

theorem odd_form (n : ℕ) (hn : n % 2 = 1) : (a n : ℚ) = (3 * n ^ 4 + n ^ 3 - n - 3) / 3 := by
  have h := a_closed n
  rw [hn] at h
  have h' := congrArg (Int.cast : ℤ → ℚ) h
  push_cast at h'
  rw [eq_div_iff (by norm_num : (3 : ℚ) ≠ 0)]
  linear_combination h'

/-- Controls: the entry's data a(1..34). -/
theorem controls : a 1 = 0 ∧ a 2 = 18 ∧ a 3 = 88 ∧ a 4 = 276 ∧ a 5 = 664 ∧ a 6 = 1366 ∧
    a 7 = 2512 ∧ a 8 = 4264 ∧ a 9 = 6800 ∧ a 10 = 10330 ∧ a 11 = 15080 ∧ a 12 = 21308 ∧
    a 13 = 29288 ∧ a 14 = 39326 ∧ a 15 = 51744 ∧ a 16 = 66896 ∧ a 17 = 85152 ∧ a 18 = 106914 ∧
    a 19 = 132600 ∧ a 20 = 162660 ∧ a 21 = 197560 ∧ a 22 = 237798 ∧ a 23 = 283888 ∧
    a 24 = 336376 ∧ a 25 = 395824 ∧ a 26 = 462826 ∧ a 27 = 537992 ∧ a 28 = 621964 ∧
    a 29 = 715400 ∧ a 30 = 818990 ∧ a 31 = 933440 ∧ a 32 = 1059488 ∧ a 33 = 1197888 ∧
    a 34 = 1349426 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> exact val _ _ (by norm_num)

/-- Barker's three conjectures. -/
theorem conjecture :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * ((1 - X) ^ 5 * (1 + X)) =
      2 * X ^ 2 * (9 + 8 * X + 7 * X ^ 2) ∧
    (∀ n : ℕ, 1 ≤ n → n % 2 = 0 → (a n : ℚ) = n * (3 * n ^ 3 + n ^ 2 - 1) / 3) ∧
    (∀ n : ℕ, n % 2 = 1 → (a n : ℚ) = (3 * n ^ 4 + n ^ 3 - n - 3) / 3) :=
  ⟨gf, fun n _ hn => even_form n hn, odd_form⟩

end OMA.S_oeis_a215191

theorem OMA.solution : type_of% @OMA.S_oeis_a215191.main :=
  OMA.S_oeis_a215191.conjecture
