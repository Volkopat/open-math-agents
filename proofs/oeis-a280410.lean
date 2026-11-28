import OMAStatements.S_oeis_a280410

namespace OMA.S_oeis_a280410








/-! ## A finite certificate: stages `0..2` on the window `[-2, 2]²` -/

/-- The background (the state of every cell far from the origin). -/
def bg : ℕ → Bool
  | 0 => false
  | t + 1 => rule (bg t) (cond (bg t) 4 0)

lemma countP_const (p : ℤ × ℤ) (f : ℤ × ℤ → Bool) (b : Bool) (h : ∀ q ∈ nbrs p, f q = b) :
    (nbrs p).countP f = cond b 4 0 := by
  have h1 := h (p.1 + 1, p.2) (by simp [nbrs])
  have h2 := h (p.1 - 1, p.2) (by simp [nbrs])
  have h3 := h (p.1, p.2 + 1) (by simp [nbrs])
  have h4 := h (p.1, p.2 - 1) (by simp [nbrs])
  cases b <;> simp [nbrs, h1, h2, h3, h4]

/-- `p` lies outside the light cone of the origin at time `t`: `t < |x| + |y|`. -/
def far (t : ℕ) (p : ℤ × ℤ) : Prop :=
  (t : ℤ) < p.1 + p.2 ∨ (t : ℤ) < p.1 - p.2 ∨ (t : ℤ) < -p.1 + p.2 ∨ (t : ℤ) < -p.1 - p.2

lemma light_cone (t : ℕ) : ∀ p, far t p → state t p = bg t := by
  induction t with
  | zero =>
    intro p hp
    simp only [state, bg, decide_eq_false_iff_not]
    rintro rfl
    simp [far] at hp
  | succ t ih =>
    intro p hp
    have hp' : far t p := by unfold far at *; push_cast at hp; omega
    show rule (state t p) _ = rule (bg t) _
    rw [ih p hp', countP_const p _ (bg t) (fun q hq => ih q ?_)]
    simp only [nbrs, List.mem_cons, List.mem_nil_iff, or_false] at hq
    unfold far at *
    push_cast at hp
    rcases hq with rfl | rfl | rfl | rfl <;> simp only <;> omega

def W : ℕ := 2

/-- A stage: the background bit and the rows `y = -W..W` as bitsets (bit `x + W` of row
`y + W` is the cell `(x, y)`). -/
def decode (s : Bool × List ℕ) (p : ℤ × ℤ) : Bool :=
  if -(W : ℤ) ≤ p.1 ∧ p.1 ≤ W ∧ -(W : ℤ) ≤ p.2 ∧ p.2 ≤ W then
    (s.2.getD (p.2 + W).toNat 0).testBit (p.1 + W).toNat
  else s.1

def cell (i j : ℕ) : ℤ × ℤ := ((i : ℤ) - W, (j : ℤ) - W)

/-- One step, checked on every window cell, and the background update. -/
def stepOK (s s' : Bool × List ℕ) : Bool :=
  (s'.1 == rule s.1 (cond s.1 4 0)) &&
  (List.range (2 * W + 1)).all fun i => (List.range (2 * W + 1)).all fun j =>
    decode s' (cell i j) == rule (decode s (cell i j)) ((nbrs (cell i j)).countP (decode s))

def initOK (s : Bool × List ℕ) : Bool :=
  (s.1 == false) && (List.range (2 * W + 1)).all fun i => (List.range (2 * W + 1)).all fun j =>
    decode s (cell i j) == decide (cell i j = (0, 0))

lemma in_window (p : ℤ × ℤ) (h : -(W : ℤ) ≤ p.1 ∧ p.1 ≤ W ∧ -(W : ℤ) ≤ p.2 ∧ p.2 ≤ W) :
    ∃ i < 2 * W + 1, ∃ j < 2 * W + 1, p = cell i j := by
  obtain ⟨x, y⟩ := p
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨(x + W).toNat, by omega, (y + W).toNat, by omega, ?_⟩
  simp only [cell, Prod.mk.injEq]
  constructor <;> omega

lemma init_ok (s : Bool × List ℕ) (h : initOK s = true) : ∀ p, state 0 p = decode s p := by
  simp only [initOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨hbg, hcells⟩ := h
  intro p
  by_cases hw : -(W : ℤ) ≤ p.1 ∧ p.1 ≤ W ∧ -(W : ℤ) ≤ p.2 ∧ p.2 ≤ W
  · obtain ⟨i, hi, j, hj, rfl⟩ := in_window p hw
    rw [hcells i hi j hj]
    rfl
  · unfold decode
    rw [if_neg hw, hbg]
    show decide (p = (0, 0)) = false
    simp only [decide_eq_false_iff_not]
    rintro rfl
    exact hw ⟨by simp, by simp, by simp, by simp⟩

lemma step_ok (t : ℕ) (s s' : Bool × List ℕ) (ht : t + 1 ≤ W) (hs : ∀ p, state t p = decode s p)
    (hb : s.1 = bg t) (hok : stepOK s s' = true) : ∀ p, state (t + 1) p = decode s' p := by
  simp only [stepOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at hok
  obtain ⟨hbg, hcells⟩ := hok
  intro p
  by_cases hw : -(W : ℤ) ≤ p.1 ∧ p.1 ≤ W ∧ -(W : ℤ) ≤ p.2 ∧ p.2 ≤ W
  · obtain ⟨i, hi, j, hj, rfl⟩ := in_window p hw
    rw [hcells i hi j hj]
    show rule (state t (cell i j)) ((nbrs (cell i j)).countP (fun q => state t q)) = _
    rw [hs, show (fun q => state t q) = decode s from funext hs]
  · have hfar : far (t + 1) p := by unfold far; push_cast; omega
    rw [light_cone (t + 1) p hfar]
    unfold decode
    rw [if_neg hw, hbg, hb]
    rfl

/-- The stages `0..2`, computed outside Lean and checked cell by cell below. -/
def stages : List (Bool × List ℕ) :=
  [(false, [0, 0, 4, 0, 0]),
    (true, [31, 31, 27, 31, 31]),
    (false, [0, 0, 4, 0, 0])]



/-! ## The periodic regime: the window border shows the background -/

def borderOK (s : Bool × List ℕ) : Bool :=
  (List.range (2 * W + 1)).all fun i => (List.range (2 * W + 1)).all fun j =>
    !(i == 0 || i == 2 * W || j == 0 || j == 2 * W) || (decode s (cell i j) == s.1)

lemma border_nbr (p q : ℤ × ℤ) (hp : ¬ (-(W : ℤ) ≤ p.1 ∧ p.1 ≤ W ∧ -(W : ℤ) ≤ p.2 ∧ p.2 ≤ W))
    (hq : q ∈ nbrs p) (hw : -(W : ℤ) ≤ q.1 ∧ q.1 ≤ W ∧ -(W : ℤ) ≤ q.2 ∧ q.2 ≤ W) :
    ∃ i < 2 * W + 1, ∃ j < 2 * W + 1, q = cell i j ∧ (i = 0 ∨ i = 2 * W ∨ j = 0 ∨ j = 2 * W) := by
  obtain ⟨i, hi, j, hj, rfl⟩ := in_window q hw
  refine ⟨i, hi, j, hj, rfl, ?_⟩
  obtain ⟨x, y⟩ := p
  simp only [nbrs, cell, List.mem_cons, Prod.mk.injEq, List.mem_nil_iff, or_false] at hq hp
  omega

lemma step_border (t : ℕ) (s s' : Bool × List ℕ) (hs : ∀ p, state t p = decode s p)
    (hbd : borderOK s = true) (hok : stepOK s s' = true) : ∀ p, state (t + 1) p = decode s' p := by
  simp only [stepOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at hok
  obtain ⟨hbg, hcells⟩ := hok
  intro p
  by_cases hw : -(W : ℤ) ≤ p.1 ∧ p.1 ≤ W ∧ -(W : ℤ) ≤ p.2 ∧ p.2 ≤ W
  · obtain ⟨i, hi, j, hj, rfl⟩ := in_window p hw
    rw [hcells i hi j hj]
    show rule (state t (cell i j)) ((nbrs (cell i j)).countP (fun q => state t q)) = _
    rw [hs, show (fun q => state t q) = decode s from funext hs]
  · have hp : decode s p = s.1 := by unfold decode; rw [if_neg hw]
    have hn : ∀ q ∈ nbrs p, decode s q = s.1 := by
      intro q hq
      by_cases hqw : -(W : ℤ) ≤ q.1 ∧ q.1 ≤ W ∧ -(W : ℤ) ≤ q.2 ∧ q.2 ≤ W
      · obtain ⟨i, hi, j, hj, rfl, hb⟩ := border_nbr p q hw hq hqw
        have := (List.all_eq_true.mp ((List.all_eq_true.mp hbd) i (List.mem_range.mpr hi)))
          j (List.mem_range.mpr hj)
        rcases hb with rfl | rfl | rfl | rfl <;> simpa using this
      · unfold decode; rw [if_neg hqw]
    show rule (state t p) ((nbrs p).countP (fun q => state t q)) = decode s' p
    rw [hs, show (fun q => state t q) = decode s from funext hs, hp, countP_const p _ s.1 hn]
    unfold decode
    rw [if_neg hw, hbg]


lemma stages_ok : initOK (stages.getD 0 default) = true ∧
    (∀ t < 2, stepOK (stages.getD t default) (stages.getD (t + 1) default) = true) ∧
    (∀ r < 2, borderOK (stages.getD (0 + r) default) = true) ∧
    stages.getD 2 default = stages.getD 0 default := by
  decide +kernel

lemma certified (t : ℕ) (ht : t ≤ 2) :
    (stages.getD t default).1 = bg t ∧ ∀ p, state t p = decode (stages.getD t default) p := by
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
    ∀ p, state (0 + m) p = decode (stages.getD (0 + m % 2) default) p := by
  induction m with
  | zero => simpa using (certified 0 (by norm_num)).2
  | succ m ih =>
    have hr : m % 2 < 2 := Nat.mod_lt _ (by norm_num)
    have hb := stages_ok.2.2.1 (m % 2) hr
    have hok := stages_ok.2.1 (0 + m % 2) (by omega)
    rcases (by omega : m % 2 + 1 < 2 ∨ m % 2 + 1 = 2) with h | h
    · rw [show (m + 1) % 2 = m % 2 + 1 by omega]
      exact step_border (0 + m) _ _ ih hb hok
    · rw [show (m + 1) % 2 = 0 by omega, Nat.add_zero, ← stages_ok.2.2.2]
      rw [show 2 = 0 + m % 2 + 1 by omega]
      exact step_border (0 + m) _ _ ih hb hok

/-- The stage shown at time `t`. -/
def stageOf (t : ℕ) : Bool × List ℕ :=
  if t < 0 then stages.getD t default else stages.getD (0 + (t - 0) % 2) default

def sim (t : ℕ) : ℤ × ℤ → Bool := decode (stageOf t)

lemma state_eq (t : ℕ) : state t = sim t := by
  funext p
  unfold sim stageOf
  split_ifs with h
  · exact (certified t (by omega)).2 p
  · obtain ⟨m, rfl⟩ : ∃ m, t = 0 + m := ⟨t - 0, by omega⟩
    rw [periodic_all m p, Nat.add_sub_cancel_left]

lemma period (t : ℕ) (ht : 0 ≤ t) : state (t + 2) = state t := by
  rw [state_eq, state_eq]
  unfold sim stageOf
  rw [if_neg (by omega), if_neg (by omega), show (t + 2 - 0) % 2 = (t - 0) % 2 by omega]

/-- The background bit shown at time `t ≥ 0`. -/
def bgOf (t : ℕ) : Bool := (stages.getD (0 + (t - 0) % 2) default).1

lemma outside (t : ℕ) (ht : 0 ≤ t) (p : ℤ × ℤ)
    (hp : ¬ (-(W : ℤ) ≤ p.1 ∧ p.1 ≤ W ∧ -(W : ℤ) ≤ p.2 ∧ p.2 ≤ W)) : state t p = bgOf t := by
  rw [state_eq]
  unfold sim stageOf decode bgOf
  rw [if_neg hp, if_neg (show ¬ (t < 0) by omega)]

def aSim (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), if sim n ((k : ℤ) - n, 0) then 10 ^ (n - k) else 0

lemma a_eq (n : ℕ) : a n = aSim n := by
  unfold a aSim
  rw [state_eq n]

/-- The values a(0..16); the listed terms are among them (control). -/
lemma vals : ∀ n ≤ 16, a n = ([1, 10, 1, 1110, 1, 111110, 1, 11111110, 1, 1111111110, 1, 111111111110, 1, 11111111111110, 1, 1111111111111110, 1] : List ℕ).getD n 0 := by
  intro n hn
  rw [a_eq n]
  revert n
  decide +kernel

lemma v0 : a 0 = 1 := vals 0 (by norm_num)
lemma v1 : a 1 = 10 := vals 1 (by norm_num)
lemma v2 : a 2 = 1 := vals 2 (by norm_num)
lemma v3 : a 3 = 1110 := vals 3 (by norm_num)
lemma v4 : a 4 = 1 := vals 4 (by norm_num)
lemma v5 : a 5 = 111110 := vals 5 (by norm_num)
lemma v6 : a 6 = 1 := vals 6 (by norm_num)
lemma v7 : a 7 = 11111110 := vals 7 (by norm_num)
lemma v8 : a 8 = 1 := vals 8 (by norm_num)
lemma v9 : a 9 = 1111111110 := vals 9 (by norm_num)
lemma v10 : a 10 = 1 := vals 10 (by norm_num)
lemma v11 : a 11 = 111111111110 := vals 11 (by norm_num)
lemma v12 : a 12 = 1 := vals 12 (by norm_num)
lemma v13 : a 13 = 11111111111110 := vals 13 (by norm_num)
lemma v14 : a 14 = 1 := vals 14 (by norm_num)
lemma v15 : a 15 = 1111111111111110 := vals 15 (by norm_num)
lemma v16 : a 16 = 1 := vals 16 (by norm_num)

lemma low_form (n : ℕ) :
    a n = ∑ d ∈ Finset.range (n + 1), if state n (-(d : ℤ), 0) then 10 ^ d else 0 := by
  unfold a
  rw [← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hd' : d < n + 1 := Finset.mem_range.mp hd
  rw [show n + 1 - 1 - d = n - d by omega, show n - (n - d) = d by omega]
  congr 2
  push_cast [show d ≤ n by omega]
  ring


lemma rel (n : ℕ) (hn : 2 ≤ n) :
    a (n + 2) = a n + (if bgOf n then ∑ j ∈ Finset.range 2, 10 ^ (n + 1 + j) else 0) := by
  rw [low_form, low_form, show n + 2 + 1 = (n + 1) + 2 by ring, Finset.sum_range_add,
    period n (by omega)]
  congr 1
  have h : ∀ j ∈ Finset.range 2,
      (if state n (-((n + 1 + j : ℕ) : ℤ), 0) then 10 ^ (n + 1 + j) else 0) =
      if bgOf n then 10 ^ (n + 1 + j) else 0 := by
    intro j _
    rw [outside n (by omega) _ (by unfold W; push_cast; omega)]
  rw [Finset.sum_congr rfl h]
  cases bgOf n <;> simp


lemma cf0 (m : ℕ) : ((10 : ℚ) - 1) * (a (2 + 2 * m) : ℚ) = 0 * (10 : ℚ) ^ (2 + 2 * m + 1) + (9 : ℚ) := by
  have hb : ∀ m, bgOf (2 + 2 * m) = false := by
    intro m
    unfold bgOf
    rw [show (2 + 2 * m - 0) % 2 = 0 by omega]
    rfl
  induction m with
  | zero =>
    rw [show 2 + 2 * 0 = 2 by ring, v2]
    norm_num
  | succ m ih =>
    rw [show 2 + 2 * (m + 1) = (2 + 2 * m) + 2 by ring, rel _ (by omega), hb m, if_neg (by decide)]
    push_cast
    try simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceSub, Nat.reduceAdd]
    linear_combination ih

lemma cfn0 (n : ℕ) (h1 : 2 ≤ n) (h2 : n % 2 = 0) : ((10 : ℚ) - 1) * (a n : ℚ) = 0 * (10 : ℚ) ^ (n + 1) + (9 : ℚ) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = 2 + 2 * m := ⟨(n - 2) / 2, by omega⟩
  exact cf0 m


lemma cf1 (m : ℕ) : ((10 : ℚ) - 1) * (a (3 + 2 * m) : ℚ) = 1 * (10 : ℚ) ^ (3 + 2 * m + 1) + (-10 : ℚ) := by
  have hb : ∀ m, bgOf (3 + 2 * m) = true := by
    intro m
    unfold bgOf
    rw [show (3 + 2 * m - 0) % 2 = 1 by omega]
    rfl
  induction m with
  | zero =>
    rw [show 3 + 2 * 0 = 3 by ring, v3]
    norm_num
  | succ m ih =>
    rw [show 3 + 2 * (m + 1) = (3 + 2 * m) + 2 by ring, rel _ (by omega), hb m, if_pos rfl]
    push_cast
    try simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceSub, Nat.reduceAdd]
    linear_combination ih

lemma cfn1 (n : ℕ) (h1 : 2 ≤ n) (h2 : n % 2 = 1) : ((10 : ℚ) - 1) * (a n : ℚ) = 1 * (10 : ℚ) ^ (n + 1) + (-10 : ℚ) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = 3 + 2 * m := ⟨(n - 3) / 2, by omega⟩
  exact cf1 m


/-- a(n) = 1 for n even -/
theorem closed0 (n : ℕ) (hp : n % 2 = 0) : (a n : ℚ) = (1 : ℚ) := by
  rcases Nat.lt_or_ge n 2 with hlt | hge
  · interval_cases n <;> norm_num [v0, v1, v2] at *
  · rcases Nat.mod_two_eq_zero_or_one n with hpar | hpar
    · obtain ⟨q, rfl⟩ : ∃ q, n = 2 + 2 * q := ⟨(n - 2) / 2, by omega⟩
      have c0 := cfn0 (2 + 2 * q) (by omega) (by omega)
      simp only [pow_add, pow_mul, neg_one_sq, one_pow, mul_one, one_mul] at c0 ⊢
      push_cast at c0 ⊢
      linear_combination (1 / ((10 : ℚ) - 1)) * c0
    · omega


/-- a(n) = 10*(10^n - 1)/9 for n odd -/
theorem closed1 (n : ℕ) (hp : n % 2 = 1) : (a n : ℚ) = (((10 : ℚ) * (((10 : ℚ) ^ n) - (1 : ℚ))) / (9 : ℚ)) := by
  rcases Nat.lt_or_ge n 2 with hlt | hge
  · interval_cases n <;> norm_num [v0, v1, v2] at *
  · rcases Nat.mod_two_eq_zero_or_one n with hpar | hpar
    · omega
    · obtain ⟨q, rfl⟩ : ∃ q, n = 3 + 2 * q := ⟨(n - 3) / 2, by omega⟩
      have c0 := cfn1 (3 + 2 * q) (by omega) (by omega)
      simp only [pow_add, pow_mul, neg_one_sq, one_pow, mul_one, one_mul] at c0 ⊢
      push_cast at c0 ⊢
      linear_combination (1 / ((10 : ℚ) - 1)) * c0


/-- a(n) = 101*a(n-2) - 100*a(n-4) for n>3 -/
theorem recurrence2 (n : ℕ) (hn : 4 ≤ n) : (a n : ℤ) = (((101 : ℤ) * (a (n - 2) : ℤ)) - ((100 : ℤ) * (a (n - 4) : ℤ))) := by
  rcases Nat.lt_or_ge n 6 with hlt | hge
  · interval_cases n <;> norm_num [v0, v1, v2, v3, v4, v5, v6] at *
  · suffices hq : (a n : ℚ) = (((101 : ℚ) * (a (n - 2) : ℚ)) - ((100 : ℚ) * (a (n - 4) : ℚ))) by exact_mod_cast hq
    rcases Nat.mod_two_eq_zero_or_one n with hpar | hpar
    · obtain ⟨q, rfl⟩ : ∃ q, n = 6 + 2 * q := ⟨(n - 6) / 2, by omega⟩
      have c0 := cfn0 (6 + 2 * q) (by omega) (by omega)
      rw [show 6 + 2 * q - 2 = 4 + 2 * q by omega]
      have c2 := cfn0 (4 + 2 * q) (by omega) (by omega)
      rw [show 6 + 2 * q - 4 = 2 + 2 * q by omega]
      have c4 := cfn0 (2 + 2 * q) (by omega) (by omega)
      simp only [pow_add, pow_mul, neg_one_sq, one_pow, mul_one, one_mul] at c0 c2 c4 ⊢
      push_cast at c0 c2 c4 ⊢
      linear_combination (1 / ((10 : ℚ) - 1)) * c0 + (-((101 : ℚ)) / ((10 : ℚ) - 1)) * c2 + (-((-100 : ℚ)) / ((10 : ℚ) - 1)) * c4
    · obtain ⟨q, rfl⟩ : ∃ q, n = 7 + 2 * q := ⟨(n - 7) / 2, by omega⟩
      have c0 := cfn1 (7 + 2 * q) (by omega) (by omega)
      rw [show 7 + 2 * q - 2 = 5 + 2 * q by omega]
      have c2 := cfn1 (5 + 2 * q) (by omega) (by omega)
      rw [show 7 + 2 * q - 4 = 3 + 2 * q by omega]
      have c4 := cfn1 (3 + 2 * q) (by omega) (by omega)
      simp only [pow_add, pow_mul, neg_one_sq, one_pow, mul_one, one_mul] at c0 c2 c4 ⊢
      push_cast at c0 c2 c4 ⊢
      linear_combination (1 / ((10 : ℚ) - 1)) * c0 + (-((101 : ℚ)) / ((10 : ℚ) - 1)) * c2 + (-((-100 : ℚ)) / ((10 : ℚ) - 1)) * c4


lemma gfrec3 (n : ℕ) (hn : 4 ≤ n) : (a n : ℚ) = ((101 : ℚ)) * (a (n - 2) : ℚ) + ((-100 : ℚ)) * (a (n - 4) : ℚ) := by
  rcases Nat.lt_or_ge n 6 with hlt | hge
  · interval_cases n <;> norm_num [v0, v1, v2, v3, v4, v5, v6] at *
  · rcases Nat.mod_two_eq_zero_or_one n with hpar | hpar
    · obtain ⟨q, rfl⟩ : ∃ q, n = 6 + 2 * q := ⟨(n - 6) / 2, by omega⟩
      have c0 := cfn0 (6 + 2 * q) (by omega) (by omega)
      rw [show 6 + 2 * q - 2 = 4 + 2 * q by omega]
      have c2 := cfn0 (4 + 2 * q) (by omega) (by omega)
      rw [show 6 + 2 * q - 4 = 2 + 2 * q by omega]
      have c4 := cfn0 (2 + 2 * q) (by omega) (by omega)
      simp only [pow_add, pow_mul, neg_one_sq, one_pow, mul_one, one_mul] at c0 c2 c4 ⊢
      push_cast at c0 c2 c4 ⊢
      linear_combination (1 / ((10 : ℚ) - 1)) * c0 + (-((101 : ℚ)) / ((10 : ℚ) - 1)) * c2 + (-((-100 : ℚ)) / ((10 : ℚ) - 1)) * c4
    · obtain ⟨q, rfl⟩ : ∃ q, n = 7 + 2 * q := ⟨(n - 7) / 2, by omega⟩
      have c0 := cfn1 (7 + 2 * q) (by omega) (by omega)
      rw [show 7 + 2 * q - 2 = 5 + 2 * q by omega]
      have c2 := cfn1 (5 + 2 * q) (by omega) (by omega)
      rw [show 7 + 2 * q - 4 = 3 + 2 * q by omega]
      have c4 := cfn1 (3 + 2 * q) (by omega) (by omega)
      simp only [pow_add, pow_mul, neg_one_sq, one_pow, mul_one, one_mul] at c0 c2 c4 ⊢
      push_cast at c0 c2 c4 ⊢
      linear_combination (1 / ((10 : ℚ) - 1)) * c0 + (-((101 : ℚ)) / ((10 : ℚ) - 1)) * c2 + (-((-100 : ℚ)) / ((10 : ℚ) - 1)) * c4

open PowerSeries in
/-- G.f.: (1 + 10*x - 100*x^2 + 100*x^3) / ((1 - x)*(1 + x)*(1 - 10*x)*(1 + 10*x)) -/
theorem gf3 : PowerSeries.mk (fun n => (a n : ℚ)) = ((1 + 10*X - 100*X ^ 2 + 100*X ^ 3)) * (((1 - X)*(1 + X)*(1 - 10*X)*(1 + 10*X)))⁻¹ := by
  set G : ℚ⟦X⟧ := PowerSeries.mk (fun n => (a n : ℚ))
  have hden : constantCoeff ((((1 - X)*(1 + X)*(1 - 10*X)*(1 + 10*X))) : ℚ⟦X⟧) ≠ 0 := by simp
  have eQ : G * (((1 - X)*(1 + X)*(1 - 10*X)*(1 + 10*X))) = C ((1 : ℚ)) * G + C ((-101 : ℚ)) * (G * X ^ 2) + C ((100 : ℚ)) * (G * X ^ 4) := by
    simp only [map_neg, map_ofNat, map_one, map_div₀, map_natCast]; ring
  have eP : (((1 + 10*X - 100*X ^ 2 + 100*X ^ 3)) : ℚ⟦X⟧) = C ((1 : ℚ)) + C ((10 : ℚ)) * X ^ 1 + C ((-100 : ℚ)) * X ^ 2 + C ((100 : ℚ)) * X ^ 3 := by
    simp only [map_neg, map_ofNat, map_one, map_div₀, map_natCast]; ring
  have key : G * (((1 - X)*(1 + X)*(1 - 10*X)*(1 + 10*X))) = (1 + 10*X - 100*X ^ 2 + 100*X ^ 3) := by
    rw [eQ, eP]
    ext n
    simp only [map_add, map_sub, coeff_C_mul, coeff_mul_X_pow', coeff_X_pow, G, coeff_mk, coeff_C]
    rcases Nat.lt_or_ge n 4 with hn | hn
    · interval_cases n <;> norm_num [v0, v1, v2, v3, v4, v5, v6]
    · simp only [show 1 ≤ n by omega, show 2 ≤ n by omega, show 3 ≤ n by omega, show 4 ≤ n by omega, show n ≠ 0 by omega, show n ≠ 1 by omega, show n ≠ 2 by omega, show n ≠ 3 by omega, show n - 1 ≠ 0 by omega, show n - 2 ≠ 0 by omega, show n - 3 ≠ 0 by omega, if_true, if_false, ↓reduceIte, ne_eq, not_false_eq_true]
      have hr := gfrec3 n hn
      linear_combination ((1 : ℚ)) * hr
  rw [← key, mul_assoc, PowerSeries.mul_inv_cancel _ hden, mul_one]


open PowerSeries in
/-- All the proved formula lines of the entry, together. -/
theorem formulas :
    (∀ n : ℕ, n % 2 = 0 → (a n : ℚ) = (1 : ℚ)) ∧
    (∀ n : ℕ, n % 2 = 1 → (a n : ℚ) = (((10 : ℚ) * (((10 : ℚ) ^ n) - (1 : ℚ))) / (9 : ℚ))) ∧
    (∀ n : ℕ, 4 ≤ n → (a n : ℤ) = (((101 : ℤ) * (a (n - 2) : ℤ)) - ((100 : ℤ) * (a (n - 4) : ℤ)))) ∧
    (PowerSeries.mk (fun n => (a n : ℚ)) = ((1 + 10*X - 100*X ^ 2 + 100*X ^ 3)) * (((1 - X)*(1 + X)*(1 - 10*X)*(1 + 10*X)))⁻¹) :=
  ⟨closed0, closed1, recurrence2, gf3⟩


/-! ## The statement's definitions and the bridge -/

open PowerSeries


/-- The site's problem, as stated in `main`. -/
theorem conj :
    (∀ n : ℕ, Even n → (a n : ℚ) = 1) ∧
    (∀ n : ℕ, Odd n → (a n : ℚ) = 10 * (10 ^ n - 1) / 9) ∧
    (∀ n : ℕ, 3 < n → (a n : ℤ) = 101 * a (n - 2) - 100 * a (n - 4)) ∧
    A = (1 + 10 * X - 100 * X ^ 2 + 100 * X ^ 3) *
      ((1 - X) * (1 + X) * (1 - 10 * X) * (1 + 10 * X))⁻¹ := by
  rw [show A = PowerSeries.mk (fun n => (a n : ℚ)) from rfl]
  exact ⟨fun n hp => (closed0 n (Nat.even_iff.mp hp)).trans (by ring),
    fun n hp => (closed1 n (Nat.odd_iff.mp hp)).trans (by ring),
    fun n hn => (recurrence2 n (by omega)).trans (by ring),
    gf3⟩

end OMA.S_oeis_a280410

theorem OMA.solution : type_of% @OMA.S_oeis_a280410.main :=
  OMA.S_oeis_a280410.conj
