import OMAStatements.S_oeis_a266590

namespace OMA.S_oeis_a266590


/-- Rule 37 as a local map: the new state of a cell from (left, center, right). -/
def rule (l c r : Bool) : Bool := (37 : ℕ).testBit ((cond l 4 0) + (cond c 2 0) + (cond r 1 0))

/-- The configuration at time `t`, started from the single ON cell at 0. -/
def cstate : ℕ → ℤ → Bool
  | 0, i => decide (i = 0)
  | t + 1, i => rule (cstate t (i - 1)) (cstate t i) (cstate t (i + 1))


/-- A266590(n): row `n`, cells `-n..n` (leftmost first), read as a binary number. -/
def ca (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (2 * n + 1), if cstate n ((k : ℤ) - n) then 2 ^ (2 * n - k) else 0


/-! ## A finite certificate: rows `0..4` on the window `[-4, 4]` -/

/-- The background (the state of every cell far from the origin). -/
def bg : ℕ → Bool
  | 0 => false
  | t + 1 => rule (bg t) (bg t) (bg t)

lemma light_cone (t : ℕ) : ∀ i : ℤ, ((t : ℤ) < i ∨ (t : ℤ) < -i) → cstate t i = bg t := by
  induction t with
  | zero => intro i hi; simp only [cstate, bg, decide_eq_false_iff_not]; omega
  | succ t ih =>
    intro i hi
    push_cast at hi
    show rule (cstate t (i - 1)) (cstate t i) (cstate t (i + 1)) = rule (bg t) (bg t) (bg t)
    rw [ih (i - 1) (by omega), ih i (by omega), ih (i + 1) (by omega)]

def W : ℕ := 4

/-- A row: the background bit and the cells `-W..W` as a bitset (bit `i + W` is cell `i`). -/
def decode (s : Bool × ℕ) (i : ℤ) : Bool :=
  if -(W : ℤ) ≤ i ∧ i ≤ W then s.2.testBit (i + W).toNat else s.1

def stepOK (s s' : Bool × ℕ) : Bool :=
  (s'.1 == rule s.1 s.1 s.1) && (List.range (2 * W + 1)).all fun j =>
    decode s' ((j : ℤ) - W) ==
      rule (decode s ((j : ℤ) - W - 1)) (decode s ((j : ℤ) - W)) (decode s ((j : ℤ) - W + 1))

def initOK (s : Bool × ℕ) : Bool :=
  (s.1 == false) && (List.range (2 * W + 1)).all fun j =>
    decode s ((j : ℤ) - W) == decide ((j : ℤ) - W = 0)

lemma in_window (i : ℤ) (h : -(W : ℤ) ≤ i ∧ i ≤ W) : ∃ j < 2 * W + 1, i = (j : ℤ) - W :=
  ⟨(i + W).toNat, by omega, by omega⟩

lemma init_ok (s : Bool × ℕ) (h : initOK s = true) : ∀ i, cstate 0 i = decode s i := by
  simp only [initOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨hbg, hcells⟩ := h
  intro i
  by_cases hw : -(W : ℤ) ≤ i ∧ i ≤ W
  · obtain ⟨j, hj, rfl⟩ := in_window i hw
    rw [hcells j hj]
    rfl
  · unfold decode
    rw [if_neg hw, hbg]
    show decide (i = 0) = false
    simp only [decide_eq_false_iff_not]
    omega

lemma step_ok (t : ℕ) (s s' : Bool × ℕ) (ht : t + 1 ≤ W) (hs : ∀ i, cstate t i = decode s i)
    (hb : s.1 = bg t) (hok : stepOK s s' = true) : ∀ i, cstate (t + 1) i = decode s' i := by
  simp only [stepOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at hok
  obtain ⟨hbg, hcells⟩ := hok
  intro i
  by_cases hw : -(W : ℤ) ≤ i ∧ i ≤ W
  · obtain ⟨j, hj, rfl⟩ := in_window i hw
    rw [hcells j hj]
    show rule (cstate t ((j : ℤ) - W - 1)) (cstate t ((j : ℤ) - W)) (cstate t ((j : ℤ) - W + 1)) = _
    rw [hs, hs, hs]
  · rw [light_cone (t + 1) i (by push_cast; omega)]
    unfold decode
    rw [if_neg hw, hbg, hb]
    rfl

/-- The rows `0..4`, computed outside Lean and checked cell by cell below. -/
def stages : List (Bool × ℕ) :=
  [(false, 16),
    (true, 471),
    (false, 56),
    (true, 387),
    (false, 56)]



/-! ## The periodic regime: the window border shows the background -/

def borderOK (s : Bool × ℕ) : Bool := (decode s (-(W : ℤ)) == s.1) && (decode s (W : ℤ) == s.1)

lemma step_border (t : ℕ) (s s' : Bool × ℕ) (hs : ∀ i, cstate t i = decode s i)
    (hbd : borderOK s = true) (hok : stepOK s s' = true) : ∀ i, cstate (t + 1) i = decode s' i := by
  simp only [stepOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at hok
  simp only [borderOK, Bool.and_eq_true, beq_iff_eq] at hbd
  obtain ⟨hbg, hcells⟩ := hok
  intro i
  by_cases hw : -(W : ℤ) ≤ i ∧ i ≤ W
  · obtain ⟨j, hj, rfl⟩ := in_window i hw
    rw [hcells j hj]
    show rule (cstate t ((j : ℤ) - W - 1)) (cstate t ((j : ℤ) - W)) (cstate t ((j : ℤ) - W + 1)) = _
    rw [hs, hs, hs]
  · have hout : ∀ k : ℤ, (k = i - 1 ∨ k = i ∨ k = i + 1) → decode s k = s.1 := by
      intro k hk
      by_cases hkw : -(W : ℤ) ≤ k ∧ k ≤ W
      · have hk2 : k = -(W : ℤ) ∨ k = (W : ℤ) := by omega
        rcases hk2 with rfl | rfl
        · exact hbd.1
        · exact hbd.2
      · unfold decode; rw [if_neg hkw]
    show rule (cstate t (i - 1)) (cstate t i) (cstate t (i + 1)) = decode s' i
    rw [hs, hs, hs, hout _ (Or.inl rfl), hout _ (Or.inr (Or.inl rfl)), hout _ (Or.inr (Or.inr rfl))]
    unfold decode
    rw [if_neg hw, hbg]


lemma stages_ok : initOK (stages.getD 0 default) = true ∧
    (∀ t < 4, stepOK (stages.getD t default) (stages.getD (t + 1) default) = true) ∧
    (∀ r < 2, borderOK (stages.getD (2 + r) default) = true) ∧
    stages.getD 4 default = stages.getD 2 default := by
  decide +kernel

lemma certified (t : ℕ) (ht : t ≤ 4) :
    (stages.getD t default).1 = bg t ∧ ∀ i, cstate t i = decode (stages.getD t default) i := by
  induction t with
  | zero =>
    have h := stages_ok.1
    refine ⟨?_, init_ok _ h⟩
    simp only [initOK, Bool.and_eq_true, beq_iff_eq] at h
    exact h.1
  | succ t ih =>
    obtain ⟨hb, hs⟩ := ih (by omega)
    have hok := stages_ok.2.1 t (by omega)
    refine ⟨?_, step_ok t _ _ (by unfold W; omega) hs hb hok⟩
    simp only [stepOK, Bool.and_eq_true, beq_iff_eq] at hok
    rw [hok.1, hb]
    rfl

lemma periodic_all (m : ℕ) :
    ∀ i, cstate (2 + m) i = decode (stages.getD (2 + m % 2) default) i := by
  induction m with
  | zero => simpa using (certified 2 (by norm_num)).2
  | succ m ih =>
    have hr : m % 2 < 2 := Nat.mod_lt _ (by norm_num)
    have hb := stages_ok.2.2.1 (m % 2) hr
    have hok := stages_ok.2.1 (2 + m % 2) (by omega)
    rcases (by omega : m % 2 + 1 < 2 ∨ m % 2 + 1 = 2) with h | h
    · rw [show (m + 1) % 2 = m % 2 + 1 by omega]
      exact step_border (2 + m) _ _ ih hb hok
    · rw [show (m + 1) % 2 = 0 by omega, Nat.add_zero, ← stages_ok.2.2.2]
      rw [show 4 = 2 + m % 2 + 1 by omega]
      exact step_border (2 + m) _ _ ih hb hok

/-- The row shown at time `t`. -/
def stageOf (t : ℕ) : Bool × ℕ :=
  if t < 2 then stages.getD t default else stages.getD (2 + (t - 2) % 2) default

def sim (t : ℕ) : ℤ → Bool := decode (stageOf t)

lemma state_eq (t : ℕ) : cstate t = sim t := by
  funext i
  unfold sim stageOf
  split_ifs with h
  · exact (certified t (by omega)).2 i
  · obtain ⟨m, rfl⟩ : ∃ m, t = 2 + m := ⟨t - 2, by omega⟩
    rw [periodic_all m i, Nat.add_sub_cancel_left]

lemma period (t : ℕ) (ht : 2 ≤ t) : cstate (t + 2) = cstate t := by
  rw [state_eq, state_eq]
  unfold sim stageOf
  rw [if_neg (by omega), if_neg (by omega), show (t + 2 - 2) % 2 = (t - 2) % 2 by omega]

/-- The background bit shown at time `t ≥ 2`. -/
def bgOf (t : ℕ) : Bool := (stages.getD (2 + (t - 2) % 2) default).1

lemma outside (t : ℕ) (ht : 2 ≤ t) (i : ℤ) (hi : ¬ (-(W : ℤ) ≤ i ∧ i ≤ W)) :
    cstate t i = bgOf t := by
  rw [state_eq]
  unfold sim stageOf decode bgOf
  rw [if_neg hi, if_neg (show ¬ (t < 2) by omega)]

def aSim (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (2 * n + 1), if sim n ((k : ℤ) - n) then 2 ^ (2 * n - k) else 0

lemma a_eq (n : ℕ) : ca n = aSim n := by
  unfold ca aSim
  simp only [state_eq]

/-- The values a(0..23); the listed terms are among them (control). -/
lemma vals : ∀ n ≤ 23, ca n = ([1, 2, 14, 65, 56, 1799, 224, 31775, 896, 520319, 3584, 8372735, 14336, 134154239, 57344, 2147229695, 229376, 34358722559, 917504, 549751750655, 3670016, 8796076769279, 14680064, 140737423343615] : List ℕ).getD n 0 := by
  intro n hn
  rw [a_eq n]
  revert n
  decide +kernel

lemma v0 : ca 0 = 1 := vals 0 (by norm_num)
lemma v1 : ca 1 = 2 := vals 1 (by norm_num)
lemma v2 : ca 2 = 14 := vals 2 (by norm_num)
lemma v3 : ca 3 = 65 := vals 3 (by norm_num)
lemma v4 : ca 4 = 56 := vals 4 (by norm_num)
lemma v5 : ca 5 = 1799 := vals 5 (by norm_num)
lemma v6 : ca 6 = 224 := vals 6 (by norm_num)
lemma v7 : ca 7 = 31775 := vals 7 (by norm_num)
lemma v8 : ca 8 = 896 := vals 8 (by norm_num)
lemma v9 : ca 9 = 520319 := vals 9 (by norm_num)
lemma v10 : ca 10 = 3584 := vals 10 (by norm_num)
lemma v11 : ca 11 = 8372735 := vals 11 (by norm_num)
lemma v12 : ca 12 = 14336 := vals 12 (by norm_num)
lemma v13 : ca 13 = 134154239 := vals 13 (by norm_num)
lemma v14 : ca 14 = 57344 := vals 14 (by norm_num)
lemma v15 : ca 15 = 2147229695 := vals 15 (by norm_num)
lemma v16 : ca 16 = 229376 := vals 16 (by norm_num)
lemma v17 : ca 17 = 34358722559 := vals 17 (by norm_num)
lemma v18 : ca 18 = 917504 := vals 18 (by norm_num)
lemma v19 : ca 19 = 549751750655 := vals 19 (by norm_num)
lemma v20 : ca 20 = 3670016 := vals 20 (by norm_num)
lemma v21 : ca 21 = 8796076769279 := vals 21 (by norm_num)
lemma v22 : ca 22 = 14680064 := vals 22 (by norm_num)
lemma v23 : ca 23 = 140737423343615 := vals 23 (by norm_num)

lemma rel (n : ℕ) (hn : 4 ≤ n) :
    ca (n + 2) = (if bgOf n then ∑ k ∈ Finset.range 2, 2 ^ (2 * n + (2 * 2 - k)) else 0) +
      2 ^ 2 * ca n + (if bgOf n then ∑ j ∈ Finset.range 2, 2 ^ (2 - 1 - j) else 0) := by
  unfold ca
  rw [show 2 * (n + 2) + 1 = 2 + (2 * n + 1) + 2 by ring, Finset.sum_range_add,
    Finset.sum_range_add, period n (by omega), Finset.mul_sum]
  congr 1
  congr 1
  · have h : ∀ k ∈ Finset.range 2, (if cstate n ((k : ℤ) - ((n + 2 : ℕ) : ℤ)) then
        2 ^ (2 * (n + 2) - k) else 0) = if bgOf n then 2 ^ (2 * n + (2 * 2 - k)) else 0 := by
      intro k hk
      have hk' := Finset.mem_range.mp hk
      rw [outside n (by omega) _ (by unfold W; push_cast; omega),
        show 2 * (n + 2) - k = 2 * n + (2 * 2 - k) by omega]
    rw [Finset.sum_congr rfl h]
    cases bgOf n <;> simp
  · refine Finset.sum_congr rfl fun k hk => ?_
    have hk' := Finset.mem_range.mp hk
    rw [show (((2 + k : ℕ) : ℤ) - ((n + 2 : ℕ) : ℤ)) = (k : ℤ) - n by push_cast; ring]
    split_ifs
    · rw [← pow_add]; congr 1; omega
    · simp
  · have h : ∀ j ∈ Finset.range 2, (if cstate n ((((2 + (2 * n + 1) + j) : ℕ) : ℤ) -
        ((n + 2 : ℕ) : ℤ)) then 2 ^ (2 * (n + 2) - (2 + (2 * n + 1) + j)) else 0) =
        if bgOf n then 2 ^ (2 - 1 - j) else 0 := by
      intro j hj
      have hj' := Finset.mem_range.mp hj
      rw [outside n (by omega) _ (by unfold W; push_cast; omega),
        show 2 * (n + 2) - (2 + (2 * n + 1) + j) = 2 - 1 - j by omega]
    rw [Finset.sum_congr rfl h]
    cases bgOf n <;> simp


lemma cf0 (m : ℕ) : (2 : ℚ) ^ 4 * (((2 : ℚ) - 1) * (ca (4 + 2 * m) : ℚ) -
    0 * (2 : ℚ) ^ (2 * (4 + 2 * m) + 1) + 0) = (56 : ℚ) * (2 : ℚ) ^ (4 + 2 * m) := by
  have hb : ∀ m, bgOf (4 + 2 * m) = false := by
    intro m
    unfold bgOf
    rw [show (4 + 2 * m - 2) % 2 = 0 by omega]
    rfl
  induction m with
  | zero =>
    rw [show 4 + 2 * 0 = 4 by ring, v4]
    norm_num
  | succ m ih =>
    rw [show 4 + 2 * (m + 1) = (4 + 2 * m) + 2 by ring, rel _ (by omega), hb m, if_neg (by decide), if_neg (by decide)]
    push_cast
    try simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceSub, Nat.reduceMul, Nat.reduceAdd]
    linear_combination (2 : ℚ) ^ 2 * ih

lemma cfn0 (n : ℕ) (h1 : 4 ≤ n) (h2 : n % 2 = 0) :
    (2 : ℚ) ^ 4 * (((2 : ℚ) - 1) * (ca n : ℚ) - 0 * (2 : ℚ) ^ (2 * n + 1) + 0) =
      (56 : ℚ) * (2 : ℚ) ^ n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = 4 + 2 * m := ⟨(n - 4) / 2, by omega⟩
  exact cf0 m


lemma cf1 (m : ℕ) : (2 : ℚ) ^ 5 * (((2 : ℚ) - 1) * (ca (5 + 2 * m) : ℚ) -
    1 * (2 : ℚ) ^ (2 * (5 + 2 * m) + 1) + 1) = (-248 : ℚ) * (2 : ℚ) ^ (5 + 2 * m) := by
  have hb : ∀ m, bgOf (5 + 2 * m) = true := by
    intro m
    unfold bgOf
    rw [show (5 + 2 * m - 2) % 2 = 1 by omega]
    rfl
  induction m with
  | zero =>
    rw [show 5 + 2 * 0 = 5 by ring, v5]
    norm_num
  | succ m ih =>
    rw [show 5 + 2 * (m + 1) = (5 + 2 * m) + 2 by ring, rel _ (by omega), hb m, if_pos rfl, if_pos rfl]
    push_cast
    try simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceSub, Nat.reduceMul, Nat.reduceAdd]
    linear_combination (2 : ℚ) ^ 2 * ih

lemma cfn1 (n : ℕ) (h1 : 4 ≤ n) (h2 : n % 2 = 1) :
    (2 : ℚ) ^ 5 * (((2 : ℚ) - 1) * (ca n : ℚ) - 1 * (2 : ℚ) ^ (2 * n + 1) + 1) =
      (-248 : ℚ) * (2 : ℚ) ^ n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = 5 + 2 * m := ⟨(n - 5) / 2, by omega⟩
  exact cf1 m


/-- a(n) = 21*a(n-2)-84*a(n-4)+64*a(n-6) for n>7 -/
theorem recurrence0 (n : ℕ) (hn : 8 ≤ n) : (ca n : ℤ) = ((((21 : ℤ) * (ca (n - 2) : ℤ)) - ((84 : ℤ) * (ca (n - 4) : ℤ))) + ((64 : ℤ) * (ca (n - 6) : ℤ))) := by
  rcases Nat.lt_or_ge n 10 with hlt | hge
  · interval_cases n <;> norm_num [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10] at *
  · suffices hq : (ca n : ℚ) = ((((21 : ℚ) * (ca (n - 2) : ℚ)) - ((84 : ℚ) * (ca (n - 4) : ℚ))) + ((64 : ℚ) * (ca (n - 6) : ℚ))) by exact_mod_cast hq
    rcases (by omega : n % 2 = 0 ∨ n % 2 = 1) with hpar | hpar
    · obtain ⟨q, rfl⟩ : ∃ q, n = 10 + 2 * q := ⟨(n - 10) / 2, by omega⟩
      have c0 := cfn0 (10 + 2 * q) (by omega) (by omega)
      rw [show 10 + 2 * q - 2 = 8 + 2 * q by omega]
      have c2 := cfn0 (8 + 2 * q) (by omega) (by omega)
      rw [show 10 + 2 * q - 4 = 6 + 2 * q by omega]
      have c4 := cfn0 (6 + 2 * q) (by omega) (by omega)
      rw [show 10 + 2 * q - 6 = 4 + 2 * q by omega]
      have c6 := cfn0 (4 + 2 * q) (by omega) (by omega)
      try simp only [pow_add, pow_mul, neg_one_sq, one_pow, mul_one, one_mul, show ((-1 : ℚ)) ^ 4 = 1 by norm_num, show ((-1 : ℚ)) ^ 6 = 1 by norm_num, show ((-1 : ℚ)) ^ 12 = 1 by norm_num] at c0 c2 c4 c6 ⊢
      push_cast at c0 c2 c4 c6 ⊢
      linear_combination (1 / ((2 : ℚ) ^ 4 * ((2 : ℚ) - 1))) * c0 + (-((21 : ℚ)) / ((2 : ℚ) ^ 4 * ((2 : ℚ) - 1))) * c2 + (-((-84 : ℚ)) / ((2 : ℚ) ^ 4 * ((2 : ℚ) - 1))) * c4 + (-((64 : ℚ)) / ((2 : ℚ) ^ 4 * ((2 : ℚ) - 1))) * c6
    · obtain ⟨q, rfl⟩ : ∃ q, n = 11 + 2 * q := ⟨(n - 11) / 2, by omega⟩
      have c0 := cfn1 (11 + 2 * q) (by omega) (by omega)
      rw [show 11 + 2 * q - 2 = 9 + 2 * q by omega]
      have c2 := cfn1 (9 + 2 * q) (by omega) (by omega)
      rw [show 11 + 2 * q - 4 = 7 + 2 * q by omega]
      have c4 := cfn1 (7 + 2 * q) (by omega) (by omega)
      rw [show 11 + 2 * q - 6 = 5 + 2 * q by omega]
      have c6 := cfn1 (5 + 2 * q) (by omega) (by omega)
      try simp only [pow_add, pow_mul, neg_one_sq, one_pow, mul_one, one_mul, show ((-1 : ℚ)) ^ 4 = 1 by norm_num, show ((-1 : ℚ)) ^ 6 = 1 by norm_num, show ((-1 : ℚ)) ^ 12 = 1 by norm_num] at c0 c2 c4 c6 ⊢
      push_cast at c0 c2 c4 c6 ⊢
      linear_combination (1 / ((2 : ℚ) ^ 5 * ((2 : ℚ) - 1))) * c0 + (-((21 : ℚ)) / ((2 : ℚ) ^ 5 * ((2 : ℚ) - 1))) * c2 + (-((-84 : ℚ)) / ((2 : ℚ) ^ 5 * ((2 : ℚ) - 1))) * c4 + (-((64 : ℚ)) / ((2 : ℚ) ^ 5 * ((2 : ℚ) - 1))) * c6


lemma gfrec1 (n : ℕ) (hn : 8 ≤ n) : (ca n : ℚ) = ((21 : ℚ)) * (ca (n - 2) : ℚ) + ((-84 : ℚ)) * (ca (n - 4) : ℚ) + ((64 : ℚ)) * (ca (n - 6) : ℚ) := by
  rcases Nat.lt_or_ge n 10 with hlt | hge
  · interval_cases n <;> norm_num [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10] at *
  · rcases (by omega : n % 2 = 0 ∨ n % 2 = 1) with hpar | hpar
    · obtain ⟨q, rfl⟩ : ∃ q, n = 10 + 2 * q := ⟨(n - 10) / 2, by omega⟩
      have c0 := cfn0 (10 + 2 * q) (by omega) (by omega)
      rw [show 10 + 2 * q - 2 = 8 + 2 * q by omega]
      have c2 := cfn0 (8 + 2 * q) (by omega) (by omega)
      rw [show 10 + 2 * q - 4 = 6 + 2 * q by omega]
      have c4 := cfn0 (6 + 2 * q) (by omega) (by omega)
      rw [show 10 + 2 * q - 6 = 4 + 2 * q by omega]
      have c6 := cfn0 (4 + 2 * q) (by omega) (by omega)
      try simp only [pow_add, pow_mul, neg_one_sq, one_pow, mul_one, one_mul, show ((-1 : ℚ)) ^ 4 = 1 by norm_num, show ((-1 : ℚ)) ^ 6 = 1 by norm_num, show ((-1 : ℚ)) ^ 12 = 1 by norm_num] at c0 c2 c4 c6 ⊢
      push_cast at c0 c2 c4 c6 ⊢
      linear_combination (1 / ((2 : ℚ) ^ 4 * ((2 : ℚ) - 1))) * c0 + (-((21 : ℚ)) / ((2 : ℚ) ^ 4 * ((2 : ℚ) - 1))) * c2 + (-((-84 : ℚ)) / ((2 : ℚ) ^ 4 * ((2 : ℚ) - 1))) * c4 + (-((64 : ℚ)) / ((2 : ℚ) ^ 4 * ((2 : ℚ) - 1))) * c6
    · obtain ⟨q, rfl⟩ : ∃ q, n = 11 + 2 * q := ⟨(n - 11) / 2, by omega⟩
      have c0 := cfn1 (11 + 2 * q) (by omega) (by omega)
      rw [show 11 + 2 * q - 2 = 9 + 2 * q by omega]
      have c2 := cfn1 (9 + 2 * q) (by omega) (by omega)
      rw [show 11 + 2 * q - 4 = 7 + 2 * q by omega]
      have c4 := cfn1 (7 + 2 * q) (by omega) (by omega)
      rw [show 11 + 2 * q - 6 = 5 + 2 * q by omega]
      have c6 := cfn1 (5 + 2 * q) (by omega) (by omega)
      try simp only [pow_add, pow_mul, neg_one_sq, one_pow, mul_one, one_mul, show ((-1 : ℚ)) ^ 4 = 1 by norm_num, show ((-1 : ℚ)) ^ 6 = 1 by norm_num, show ((-1 : ℚ)) ^ 12 = 1 by norm_num] at c0 c2 c4 c6 ⊢
      push_cast at c0 c2 c4 c6 ⊢
      linear_combination (1 / ((2 : ℚ) ^ 5 * ((2 : ℚ) - 1))) * c0 + (-((21 : ℚ)) / ((2 : ℚ) ^ 5 * ((2 : ℚ) - 1))) * c2 + (-((-84 : ℚ)) / ((2 : ℚ) ^ 5 * ((2 : ℚ) - 1))) * c4 + (-((64 : ℚ)) / ((2 : ℚ) ^ 5 * ((2 : ℚ) - 1))) * c6

open PowerSeries in
/-- G.f.: (1+2*x-7*x^2+23*x^3-154*x^4+602*x^5+160*x^6-672*x^7) / ((1-x)*(1+x)*(1-2*x)*(1+2*x)*(1-4*x)*(1+4*x)) -/
theorem gf1 : PowerSeries.mk (fun n => (ca n : ℚ)) = ((1+2*X-7*X ^ 2+23*X ^ 3-154*X ^ 4+602*X ^ 5+160*X ^ 6-672*X ^ 7)) * (((1-X)*(1+X)*(1-2*X)*(1+2*X)*(1-4*X)*(1+4*X)))⁻¹ := by
  set G : ℚ⟦X⟧ := PowerSeries.mk (fun n => (ca n : ℚ))
  have hden : constantCoeff ((((1-X)*(1+X)*(1-2*X)*(1+2*X)*(1-4*X)*(1+4*X))) : ℚ⟦X⟧) ≠ 0 := by simp
  have eQ : G * (((1-X)*(1+X)*(1-2*X)*(1+2*X)*(1-4*X)*(1+4*X))) = C ((1 : ℚ)) * G + C ((-21 : ℚ)) * (G * X ^ 2) + C ((84 : ℚ)) * (G * X ^ 4) + C ((-64 : ℚ)) * (G * X ^ 6) := by
    (try simp only [map_neg, map_ofNat, map_one, map_div₀, map_natCast]) <;> ring
  have eP : (((1+2*X-7*X ^ 2+23*X ^ 3-154*X ^ 4+602*X ^ 5+160*X ^ 6-672*X ^ 7)) : ℚ⟦X⟧) = C ((1 : ℚ)) + C ((2 : ℚ)) * X ^ 1 + C ((-7 : ℚ)) * X ^ 2 + C ((23 : ℚ)) * X ^ 3 + C ((-154 : ℚ)) * X ^ 4 + C ((602 : ℚ)) * X ^ 5 + C ((160 : ℚ)) * X ^ 6 + C ((-672 : ℚ)) * X ^ 7 := by
    (try simp only [map_neg, map_ofNat, map_one, map_div₀, map_natCast]) <;> ring
  have key : G * (((1-X)*(1+X)*(1-2*X)*(1+2*X)*(1-4*X)*(1+4*X))) = (1+2*X-7*X ^ 2+23*X ^ 3-154*X ^ 4+602*X ^ 5+160*X ^ 6-672*X ^ 7) := by
    rw [eQ, eP]
    ext n
    simp only [map_add, map_sub, coeff_C_mul, coeff_mul_X_pow', coeff_X_pow, G, coeff_mk, coeff_C]
    rcases Nat.lt_or_ge n 8 with hn | hn
    · interval_cases n <;> norm_num [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10]
    · simp only [show 1 ≤ n by omega, show 2 ≤ n by omega, show 3 ≤ n by omega, show 4 ≤ n by omega, show 5 ≤ n by omega, show 6 ≤ n by omega, show 7 ≤ n by omega, show n ≠ 0 by omega, show n ≠ 1 by omega, show n ≠ 2 by omega, show n ≠ 3 by omega, show n ≠ 4 by omega, show n ≠ 5 by omega, show n ≠ 6 by omega, show n ≠ 7 by omega, show n - 1 ≠ 0 by omega, show n - 2 ≠ 0 by omega, show n - 3 ≠ 0 by omega, show n - 4 ≠ 0 by omega, show n - 5 ≠ 0 by omega, show n - 6 ≠ 0 by omega, show n - 7 ≠ 0 by omega, if_true, if_false, ↓reduceIte, ne_eq, not_false_eq_true]
      have hr := gfrec1 n hn
      linear_combination ((1 : ℚ)) * hr
  rw [← key, mul_assoc, PowerSeries.mul_inv_cancel _ hden, mul_one]


/-- a(n) = 2*4^n - 31*2^(n-2) - 1 for odd n > 1 -/
theorem closed2 (n : ℕ) (hn : 2 ≤ n) (hp : n % 2 = 1) : (ca n : ℚ) = ((((2 : ℚ) * ((4 : ℚ) ^ n)) - ((31 : ℚ) * ((2 : ℚ) ^ (n - 2)))) - (1 : ℚ)) := by
  rcases Nat.lt_or_ge n 6 with hlt | hge
  · interval_cases n <;> norm_num [v0, v1, v2, v3, v4, v5, v6] at *
  · rcases (by omega : n % 2 = 0 ∨ n % 2 = 1) with hpar | hpar
    · omega
    · obtain ⟨q, rfl⟩ : ∃ q, n = 7 + 2 * q := ⟨(n - 7) / 2, by omega⟩
      have c0 := cfn1 (7 + 2 * q) (by omega) (by omega)
      try rw [show 7 + 2 * q - 2 = 5 + 2 * q by omega]
      try simp only [pow_add, pow_mul, neg_one_sq, one_pow, mul_one, one_mul, show ((-1 : ℚ)) ^ 4 = 1 by norm_num, show ((-1 : ℚ)) ^ 6 = 1 by norm_num, show ((-1 : ℚ)) ^ 12 = 1 by norm_num] at c0 ⊢
      try rw [show (4 : ℚ) = 2 ^ 2 by norm_num] at c0
      try rw [show (4 : ℚ) = 2 ^ 2 by norm_num]
      try simp only [mul_pow, ← pow_mul] at c0 ⊢
      push_cast at c0 ⊢
      linear_combination (1 / ((2 : ℚ) ^ 5 * ((2 : ℚ) - 1))) * c0


/-- a(n) = 7*2^(n-1) for even n > 1 -/
theorem closed3 (n : ℕ) (hn : 2 ≤ n) (hp : n % 2 = 0) : (ca n : ℚ) = ((7 : ℚ) * ((2 : ℚ) ^ (n - 1))) := by
  rcases Nat.lt_or_ge n 5 with hlt | hge
  · interval_cases n <;> norm_num [v0, v1, v2, v3, v4, v5] at *
  · rcases (by omega : n % 2 = 0 ∨ n % 2 = 1) with hpar | hpar
    · obtain ⟨q, rfl⟩ : ∃ q, n = 6 + 2 * q := ⟨(n - 6) / 2, by omega⟩
      have c0 := cfn0 (6 + 2 * q) (by omega) (by omega)
      try rw [show 6 + 2 * q - 1 = 5 + 2 * q by omega]
      try simp only [pow_add, pow_mul, neg_one_sq, one_pow, mul_one, one_mul, show ((-1 : ℚ)) ^ 4 = 1 by norm_num, show ((-1 : ℚ)) ^ 6 = 1 by norm_num, show ((-1 : ℚ)) ^ 12 = 1 by norm_num] at c0 ⊢
      push_cast at c0 ⊢
      linear_combination (1 / ((2 : ℚ) ^ 4 * ((2 : ℚ) - 1))) * c0
    · omega


open PowerSeries in
/-- All the proved formula lines of the entry, together. -/
theorem formulas :
    (∀ n : ℕ, 8 ≤ n → (ca n : ℤ) = ((((21 : ℤ) * (ca (n - 2) : ℤ)) - ((84 : ℤ) * (ca (n - 4) : ℤ))) + ((64 : ℤ) * (ca (n - 6) : ℤ)))) ∧
    (PowerSeries.mk (fun n => (ca n : ℚ)) = ((1+2*X-7*X ^ 2+23*X ^ 3-154*X ^ 4+602*X ^ 5+160*X ^ 6-672*X ^ 7)) * (((1-X)*(1+X)*(1-2*X)*(1+2*X)*(1-4*X)*(1+4*X)))⁻¹) ∧
    (∀ n : ℕ, 2 ≤ n → n % 2 = 1 → (ca n : ℚ) = ((((2 : ℚ) * ((4 : ℚ) ^ n)) - ((31 : ℚ) * ((2 : ℚ) ^ (n - 2)))) - (1 : ℚ))) ∧
    (∀ n : ℕ, 2 ≤ n → n % 2 = 0 → (ca n : ℚ) = ((7 : ℚ) * ((2 : ℚ) ^ (n - 1)))) :=
  ⟨recurrence0, gf1, closed2, closed3⟩


/-! ## The statement's definitions and the bridge -/

open PowerSeries






theorem rule_eq (l c r : Bool) :
    rule l c r = Nat.testBit 37 (4 * l.toNat + 2 * c.toNat + r.toNat) := by
  cases l <;> cases c <;> cases r <;> rfl

theorem cstate_eq (t : ℕ) : cstate t = state 37 t := by
  induction t with
  | zero => funext i; rfl
  | succ t ih =>
    funext i
    show rule (cstate t (i - 1)) (cstate t i) (cstate t (i + 1)) = step 37 (state 37 t) i
    rw [ih, rule_eq]
    rfl

theorem row_eq (n : ℕ) :
    rowValue (state 37 n) n = ∑ k ∈ Finset.range (2 * n + 1), if cstate n ((k : ℤ) - n) then 2 ^ (2 * n - k) else 0 := by
  rw [rowValue, ← cstate_eq]
  conv_lhs => rw [← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' := Finset.mem_range.mp hk
  rw [show ((n : ℤ) - ((2 * n + 1 - 1 - k : ℕ) : ℤ)) = (k : ℤ) - n by omega,
    show 2 * n + 1 - 1 - k = 2 * n - k by omega]
  cases cstate n ((k : ℤ) - n) <;> simp

theorem a_eq_ca : a = ca := by
  funext n
  rw [a, ca, row_eq]

theorem controls : ∀ n ≤ 23, a n = ([1, 2, 14, 65, 56, 1799, 224, 31775, 896, 520319, 3584, 8372735, 14336, 134154239, 57344, 2147229695, 229376, 34358722559, 917504, 549751750655, 3670016, 8796076769279, 14680064, 140737423343615] : List ℕ).getD n 0 := by
  rw [a_eq_ca]
  exact vals

/-- The site's problem, as stated in `main`. -/
theorem conj :
    (∀ n : ℕ, 7 < n → (a n : ℤ) = 21 * a (n - 2) - 84 * a (n - 4) + 64 * a (n - 6)) ∧
    A = (1 + 2 * X - 7 * X ^ 2 + 23 * X ^ 3 - 154 * X ^ 4 + 602 * X ^ 5 + 160 * X ^ 6 - 672 * X ^ 7) *
      ((1 - X) * (1 + X) * (1 - 2 * X) * (1 + 2 * X) * (1 - 4 * X) * (1 + 4 * X))⁻¹ ∧
    (∀ n : ℕ, 1 < n → Odd n → (a n : ℚ) = 2 * 4 ^ n - 31 * 2 ^ (n - 2) - 1) ∧
    (∀ n : ℕ, 1 < n → Even n → (a n : ℚ) = 7 * 2 ^ (n - 1)) := by
  rw [show A = PowerSeries.mk (fun n => (a n : ℚ)) from rfl, a_eq_ca]
  exact ⟨fun n hn => (recurrence0 n (by omega)).trans (by ring),
    gf1,
    fun n hn hp => (closed2 n (by omega) (Nat.odd_iff.mp hp)).trans (by ring),
    fun n hn hp => (closed3 n (by omega) (Nat.even_iff.mp hp)).trans (by ring)⟩

end OMA.S_oeis_a266590

theorem OMA.solution : type_of% @OMA.S_oeis_a266590.main :=
  OMA.S_oeis_a266590.conj
