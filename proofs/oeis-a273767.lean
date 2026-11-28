import OMAStatements.S_oeis_a273767

namespace OeisA273767_R921


/-- Rule 921: new state from the cell's state `c` and its number `k` of ON neighbors
(Wolfram's outer totalistic code: bit `2k + c` of 921). -/
def ruleR (c : Bool) (k : ℕ) : Bool := (921 : ℕ).testBit (2 * k + cond c 1 0)

/-- The four von Neumann neighbors. -/
def nbrsR (p : ℤ × ℤ) : List (ℤ × ℤ) :=
  [(p.1 + 1, p.2), (p.1 - 1, p.2), (p.1, p.2 + 1), (p.1, p.2 - 1)]

/-- The automaton on `ℤ × ℤ`, started from the single ON cell at the origin. -/
def stateR : ℕ → ℤ × ℤ → Bool
  | 0, p => decide (p = (0, 0))
  | t + 1, p => ruleR (stateR t p) ((nbrsR p).countP (fun q => stateR t q))


/-- A273767(n): the number of ON cells of stage `2^n - 1` in the square `[-(2^n-1), 2^n-1]²`. -/
def aR (n : ℕ) : ℕ :=
  ∑ x ∈ Finset.range (2 * (2 ^ n - 1) + 1), ∑ y ∈ Finset.range (2 * (2 ^ n - 1) + 1), if stateR (2 ^ n - 1) ((x : ℤ) - (2 ^ n - 1 : ℕ), (y : ℤ) - (2 ^ n - 1 : ℕ)) then 1 else 0


/-! ## A finite certificate: stages `0..5` on the window `[-5, 5]²` -/

/-- The background (the state of every cell far from the origin). -/
def bg : ℕ → Bool
  | 0 => false
  | t + 1 => ruleR (bg t) (cond (bg t) 4 0)

lemma countP_const (p : ℤ × ℤ) (f : ℤ × ℤ → Bool) (b : Bool) (h : ∀ q ∈ nbrsR p, f q = b) :
    (nbrsR p).countP f = cond b 4 0 := by
  have h1 := h (p.1 + 1, p.2) (by simp [nbrsR])
  have h2 := h (p.1 - 1, p.2) (by simp [nbrsR])
  have h3 := h (p.1, p.2 + 1) (by simp [nbrsR])
  have h4 := h (p.1, p.2 - 1) (by simp [nbrsR])
  cases b <;> simp [nbrsR, h1, h2, h3, h4]

/-- `p` lies outside the light cone of the origin at time `t`: `t < |x| + |y|`. -/
def far (t : ℕ) (p : ℤ × ℤ) : Prop :=
  (t : ℤ) < p.1 + p.2 ∨ (t : ℤ) < p.1 - p.2 ∨ (t : ℤ) < -p.1 + p.2 ∨ (t : ℤ) < -p.1 - p.2

lemma light_cone (t : ℕ) : ∀ p, far t p → stateR t p = bg t := by
  induction t with
  | zero =>
    intro p hp
    simp only [stateR, bg, decide_eq_false_iff_not]
    rintro rfl
    simp [far] at hp
  | succ t ih =>
    intro p hp
    have hp' : far t p := by unfold far at *; push_cast at hp; omega
    show ruleR (stateR t p) _ = ruleR (bg t) _
    rw [ih p hp', countP_const p _ (bg t) (fun q hq => ih q ?_)]
    simp only [nbrsR, List.mem_cons, List.mem_nil_iff, or_false] at hq
    unfold far at *
    push_cast at hp
    rcases hq with rfl | rfl | rfl | rfl <;> simp only <;> omega

def W : ℕ := 5

/-- A stage: the background bit and the rows `y = -W..W` as bitsets (bit `x + W` of row
`y + W` is the cell `(x, y)`). -/
def decode (s : Bool × List ℕ) (p : ℤ × ℤ) : Bool :=
  if -(W : ℤ) ≤ p.1 ∧ p.1 ≤ W ∧ -(W : ℤ) ≤ p.2 ∧ p.2 ≤ W then
    (s.2.getD (p.2 + W).toNat 0).testBit (p.1 + W).toNat
  else s.1

def cell (i j : ℕ) : ℤ × ℤ := ((i : ℤ) - W, (j : ℤ) - W)

/-- One step, checked on every window cell, and the background update. -/
def stepOK (s s' : Bool × List ℕ) : Bool :=
  (s'.1 == ruleR s.1 (cond s.1 4 0)) &&
  (List.range (2 * W + 1)).all fun i => (List.range (2 * W + 1)).all fun j =>
    decode s' (cell i j) == ruleR (decode s (cell i j)) ((nbrsR (cell i j)).countP (decode s))

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

lemma init_ok (s : Bool × List ℕ) (h : initOK s = true) : ∀ p, stateR 0 p = decode s p := by
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

lemma step_ok (t : ℕ) (s s' : Bool × List ℕ) (ht : t + 1 ≤ W) (hs : ∀ p, stateR t p = decode s p)
    (hb : s.1 = bg t) (hok : stepOK s s' = true) : ∀ p, stateR (t + 1) p = decode s' p := by
  simp only [stepOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at hok
  obtain ⟨hbg, hcells⟩ := hok
  intro p
  by_cases hw : -(W : ℤ) ≤ p.1 ∧ p.1 ≤ W ∧ -(W : ℤ) ≤ p.2 ∧ p.2 ≤ W
  · obtain ⟨i, hi, j, hj, rfl⟩ := in_window p hw
    rw [hcells i hi j hj]
    show ruleR (stateR t (cell i j)) ((nbrsR (cell i j)).countP (fun q => stateR t q)) = _
    rw [hs, show (fun q => stateR t q) = decode s from funext hs]
  · have hfar : far (t + 1) p := by unfold far; push_cast; omega
    rw [light_cone (t + 1) p hfar]
    unfold decode
    rw [if_neg hw, hbg, hb]
    rfl

/-- The stages `0..5`, computed outside Lean and checked cell by cell below. -/
def stages : List (Bool × List ℕ) :=
  [(false, [0, 0, 0, 0, 0, 32, 0, 0, 0, 0, 0]),
    (true, [2047, 2047, 2047, 2047, 2015, 1935, 2015, 2047, 2047, 2047, 2047]),
    (true, [2047, 2047, 2047, 2047, 1935, 1967, 1935, 2047, 2047, 2047, 2047]),
    (true, [2047, 2047, 2047, 2047, 2047, 2015, 2047, 2047, 2047, 2047, 2047]),
    (true, [2047, 2047, 2047, 2047, 2047, 2047, 2047, 2047, 2047, 2047, 2047]),
    (true, [2047, 2047, 2047, 2047, 2047, 2047, 2047, 2047, 2047, 2047, 2047])]



/-! ## The periodic regime: the window border shows the background -/

def borderOK (s : Bool × List ℕ) : Bool :=
  (List.range (2 * W + 1)).all fun i => (List.range (2 * W + 1)).all fun j =>
    !(i == 0 || i == 2 * W || j == 0 || j == 2 * W) || (decode s (cell i j) == s.1)

lemma border_nbr (p q : ℤ × ℤ) (hp : ¬ (-(W : ℤ) ≤ p.1 ∧ p.1 ≤ W ∧ -(W : ℤ) ≤ p.2 ∧ p.2 ≤ W))
    (hq : q ∈ nbrsR p) (hw : -(W : ℤ) ≤ q.1 ∧ q.1 ≤ W ∧ -(W : ℤ) ≤ q.2 ∧ q.2 ≤ W) :
    ∃ i < 2 * W + 1, ∃ j < 2 * W + 1, q = cell i j ∧ (i = 0 ∨ i = 2 * W ∨ j = 0 ∨ j = 2 * W) := by
  obtain ⟨i, hi, j, hj, rfl⟩ := in_window q hw
  refine ⟨i, hi, j, hj, rfl, ?_⟩
  obtain ⟨x, y⟩ := p
  simp only [nbrsR, cell, List.mem_cons, Prod.mk.injEq, List.mem_nil_iff, or_false] at hq hp
  omega

lemma step_border (t : ℕ) (s s' : Bool × List ℕ) (hs : ∀ p, stateR t p = decode s p)
    (hbd : borderOK s = true) (hok : stepOK s s' = true) : ∀ p, stateR (t + 1) p = decode s' p := by
  simp only [stepOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at hok
  obtain ⟨hbg, hcells⟩ := hok
  intro p
  by_cases hw : -(W : ℤ) ≤ p.1 ∧ p.1 ≤ W ∧ -(W : ℤ) ≤ p.2 ∧ p.2 ≤ W
  · obtain ⟨i, hi, j, hj, rfl⟩ := in_window p hw
    rw [hcells i hi j hj]
    show ruleR (stateR t (cell i j)) ((nbrsR (cell i j)).countP (fun q => stateR t q)) = _
    rw [hs, show (fun q => stateR t q) = decode s from funext hs]
  · have hp : decode s p = s.1 := by unfold decode; rw [if_neg hw]
    have hn : ∀ q ∈ nbrsR p, decode s q = s.1 := by
      intro q hq
      by_cases hqw : -(W : ℤ) ≤ q.1 ∧ q.1 ≤ W ∧ -(W : ℤ) ≤ q.2 ∧ q.2 ≤ W
      · obtain ⟨i, hi, j, hj, rfl, hb⟩ := border_nbr p q hw hq hqw
        have := (List.all_eq_true.mp ((List.all_eq_true.mp hbd) i (List.mem_range.mpr hi)))
          j (List.mem_range.mpr hj)
        rcases hb with rfl | rfl | rfl | rfl <;> simpa using this
      · unfold decode; rw [if_neg hqw]
    show ruleR (stateR t p) ((nbrsR p).countP (fun q => stateR t q)) = decode s' p
    rw [hs, show (fun q => stateR t q) = decode s from funext hs, hp, countP_const p _ s.1 hn]
    unfold decode
    rw [if_neg hw, hbg]


lemma stages_ok : initOK (stages.getD 0 default) = true ∧
    (∀ t < 5, stepOK (stages.getD t default) (stages.getD (t + 1) default) = true) ∧
    (∀ r < 1, borderOK (stages.getD (4 + r) default) = true) ∧
    stages.getD 5 default = stages.getD 4 default := by
  decide +kernel

lemma certified (t : ℕ) (ht : t ≤ 5) :
    (stages.getD t default).1 = bg t ∧ ∀ p, stateR t p = decode (stages.getD t default) p := by
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
    ∀ p, stateR (4 + m) p = decode (stages.getD (4 + m % 1) default) p := by
  induction m with
  | zero => simpa using (certified 4 (by norm_num)).2
  | succ m ih =>
    have hr : m % 1 < 1 := Nat.mod_lt _ (by norm_num)
    have hb := stages_ok.2.2.1 (m % 1) hr
    have hok := stages_ok.2.1 (4 + m % 1) (by omega)
    rcases (by omega : m % 1 + 1 < 1 ∨ m % 1 + 1 = 1) with h | h
    · rw [show (m + 1) % 1 = m % 1 + 1 by omega]
      exact step_border (4 + m) _ _ ih hb hok
    · rw [show (m + 1) % 1 = 0 by omega, Nat.add_zero, ← stages_ok.2.2.2]
      rw [show 5 = 4 + m % 1 + 1 by omega]
      exact step_border (4 + m) _ _ ih hb hok

/-- The stage shown at time `t`. -/
def stageOf (t : ℕ) : Bool × List ℕ :=
  if t < 4 then stages.getD t default else stages.getD (4 + (t - 4) % 1) default

def sim (t : ℕ) : ℤ × ℤ → Bool := decode (stageOf t)

lemma state_eq (t : ℕ) : stateR t = sim t := by
  funext p
  unfold sim stageOf
  split_ifs with h
  · exact (certified t (by omega)).2 p
  · obtain ⟨m, rfl⟩ : ∃ m, t = 4 + m := ⟨t - 4, by omega⟩
    rw [periodic_all m p, Nat.add_sub_cancel_left]

lemma period (t : ℕ) (ht : 4 ≤ t) : stateR (t + 1) = stateR t := by
  rw [state_eq, state_eq]
  unfold sim stageOf
  rw [if_neg (by omega), if_neg (by omega), show (t + 1 - 4) % 1 = (t - 4) % 1 by omega]

/-- The background bit shown at time `t ≥ 4`. -/
def bgOf (t : ℕ) : Bool := (stages.getD (4 + (t - 4) % 1) default).1

lemma outside (t : ℕ) (ht : 4 ≤ t) (p : ℤ × ℤ)
    (hp : ¬ (-(W : ℤ) ≤ p.1 ∧ p.1 ≤ W ∧ -(W : ℤ) ≤ p.2 ∧ p.2 ≤ W)) : stateR t p = bgOf t := by
  rw [state_eq]
  unfold sim stageOf decode bgOf
  rw [if_neg hp, if_neg (show ¬ (t < 4) by omega)]

def aSim (n : ℕ) : ℕ :=
  ∑ x ∈ Finset.range (2 * (2 ^ n - 1) + 1), ∑ y ∈ Finset.range (2 * (2 ^ n - 1) + 1), if sim (2 ^ n - 1) ((x : ℤ) - (2 ^ n - 1 : ℕ), (y : ℤ) - (2 ^ n - 1 : ℕ)) then 1 else 0

lemma a_eq (n : ℕ) : aR n = aSim n := by
  unfold aR aSim
  simp only [state_eq]

/-- The values a(0..2); the listed terms are among them (control). -/
lemma vals : ∀ n ≤ 2, aR n = ([1, 4, 48] : List ℕ).getD n 0 := by
  intro n hn
  rw [a_eq n]
  revert n
  decide +kernel

lemma v0 : aR 0 = 1 := vals 0 (by norm_num)
lemma v1 : aR 1 = 4 := vals 1 (by norm_num)
lemma v2 : aR 2 = 48 := vals 2 (by norm_num)

/-! ## Counting ON cells: outside the window every cell shows the background -/

/-- The number of ON cells of stage `n` in the square `[-n, n]²`. -/
def cnt (n : ℕ) : ℕ :=
  ∑ x ∈ Finset.range (2 * n + 1), ∑ y ∈ Finset.range (2 * n + 1),
    if stateR n ((x : ℤ) - n, (y : ℤ) - n) then 1 else 0

lemma sum_window (g : ℤ → ℤ) (hg : ∀ z : ℤ, (W : ℤ) < z ∨ z < -(W : ℤ) → g z = 0) (n : ℕ)
    (hn : W ≤ n) :
    ∑ x ∈ Finset.range (2 * n + 1), g ((x : ℤ) - n) =
      ∑ i ∈ Finset.range (2 * W + 1), g ((i : ℤ) - W) := by
  induction n, hn using Nat.le_induction with
  | base => rfl
  | succ n hn ih =>
    rw [show 2 * (n + 1) + 1 = 2 * n + 1 + 1 + 1 by ring, Finset.sum_range_succ,
      Finset.sum_range_succ', hg _ (by push_cast; omega), hg _ (by push_cast; omega), add_zero,
      add_zero, ← ih]
    refine Finset.sum_congr rfl fun x _ => ?_
    congr 1
    push_cast
    ring

lemma sum_window2 (g : ℤ → ℤ → ℤ)
    (hg : ∀ x y : ℤ, (W : ℤ) < x ∨ x < -(W : ℤ) ∨ (W : ℤ) < y ∨ y < -(W : ℤ) → g x y = 0) (n : ℕ)
    (hn : W ≤ n) :
    ∑ x ∈ Finset.range (2 * n + 1), ∑ y ∈ Finset.range (2 * n + 1), g ((x : ℤ) - n) ((y : ℤ) - n) =
      ∑ i ∈ Finset.range (2 * W + 1), ∑ j ∈ Finset.range (2 * W + 1), g ((i : ℤ) - W) ((j : ℤ) - W) := by
  have h1 : ∀ x ∈ Finset.range (2 * n + 1),
      ∑ y ∈ Finset.range (2 * n + 1), g ((x : ℤ) - n) ((y : ℤ) - n) =
        ∑ j ∈ Finset.range (2 * W + 1), g ((x : ℤ) - n) ((j : ℤ) - W) :=
    fun x _ => sum_window (g ((x : ℤ) - n)) (fun z hz => hg _ _ (by omega)) n hn
  rw [Finset.sum_congr rfl h1]
  exact sum_window (fun z => ∑ j ∈ Finset.range (2 * W + 1), g z ((j : ℤ) - W))
    (fun z hz => Finset.sum_eq_zero fun j _ => hg _ _ (by omega)) n hn

/-- A cell minus the background, as an integer. -/
def dl (n : ℕ) (x y : ℤ) : ℤ := (if stateR n (x, y) then 1 else 0) - (if bgOf n then 1 else 0)

lemma dl_out (n : ℕ) (hn : 4 ≤ n) (x y : ℤ)
    (h : (W : ℤ) < x ∨ x < -(W : ℤ) ∨ (W : ℤ) < y ∨ y < -(W : ℤ)) : dl n x y = 0 := by
  unfold dl
  rw [outside n hn (x, y) (by simp only; omega)]
  simp

lemma cnt_eq (n : ℕ) (hn : 5 ≤ n) :
    (cnt n : ℤ) = (if bgOf n then 1 else 0) * (2 * (n : ℤ) + 1) ^ 2 +
      ∑ i ∈ Finset.range (2 * W + 1), ∑ j ∈ Finset.range (2 * W + 1),
        dl n ((i : ℤ) - W) ((j : ℤ) - W) := by
  have e : ∀ x y : ℤ, (if stateR n (x, y) then (1 : ℤ) else 0) = (if bgOf n then 1 else 0) + dl n x y := by
    intro x y; unfold dl; ring
  have hW : W ≤ n := by unfold W; omega
  unfold cnt
  push_cast
  simp only [e]
  rw [Finset.sum_congr rfl (fun x _ => Finset.sum_add_distrib), Finset.sum_add_distrib,
    sum_window2 (dl n) (fun x y h => dl_out n (by omega) x y h) n hW]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  push_cast
  ring


lemma cntn0 (n : ℕ) (h1 : 5 ≤ n) (h2 : n % 1 = 0) :
    (cnt n : ℚ) = 1 * (2 * (n : ℚ) + 1) ^ 2 + (0 : ℚ) := by
  have hk : 4 + (n - 4) % 1 = 4 := by omega
  have hb : bgOf n = true := by unfold bgOf; rw [hk]; rfl
  have hd : ∑ i ∈ Finset.range (2 * W + 1), ∑ j ∈ Finset.range (2 * W + 1),
      dl n ((i : ℤ) - W) ((j : ℤ) - W) = 0 := by
    unfold dl
    rw [state_eq n, hb]
    unfold sim stageOf
    rw [if_neg (by omega), hk]
    decide +kernel
  have h := cnt_eq n h1
  rw [hb, hd, if_pos rfl] at h
  have hc : (cnt n : ℚ) = ((cnt n : ℤ) : ℚ) := by norm_cast
  rw [hc, h]
  push_cast
  ring


lemma cfn0 (n : ℕ) (h1 : 3 ≤ n) (h2 : n % 1 = 0) :
    (aR n : ℚ) = 1 * (2 * (2 : ℚ) ^ n - 1) ^ 2 + (0 : ℚ) := by
  have hp : 2 ^ 3 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h1
  have hs : 5 ≤ 2 ^ n - 1 := by norm_num at hp; omega
  have hr : (2 ^ n - 1) % 1 = 0 := by
    omega
  have h := cntn0 (2 ^ n - 1) hs hr
  have hc : ((2 ^ n - 1 : ℕ) : ℚ) = (2 : ℚ) ^ n - 1 := by
    rw [Nat.cast_sub Nat.one_le_two_pow]; push_cast; ring
  show (cnt (2 ^ n - 1) : ℚ) = _
  rw [h, hc]
  ring

lemma v3 : aR 3 = 225 := by
  have h := cfn0 3 (by norm_num) (by norm_num)
  have h' : (aR 3 : ℚ) = 225 := by rw [h]; norm_num
  exact_mod_cast h'
lemma v4 : aR 4 = 961 := by
  have h := cfn0 4 (by norm_num) (by norm_num)
  have h' : (aR 4 : ℚ) = 961 := by rw [h]; norm_num
  exact_mod_cast h'
lemma v5 : aR 5 = 3969 := by
  have h := cfn0 5 (by norm_num) (by norm_num)
  have h' : (aR 5 : ℚ) = 3969 := by rw [h]; norm_num
  exact_mod_cast h'
lemma v6 : aR 6 = 16129 := by
  have h := cfn0 6 (by norm_num) (by norm_num)
  have h' : (aR 6 : ℚ) = 16129 := by rw [h]; norm_num
  exact_mod_cast h'
lemma v7 : aR 7 = 65025 := by
  have h := cfn0 7 (by norm_num) (by norm_num)
  have h' : (aR 7 : ℚ) = 65025 := by rw [h]; norm_num
  exact_mod_cast h'
lemma v8 : aR 8 = 261121 := by
  have h := cfn0 8 (by norm_num) (by norm_num)
  have h' : (aR 8 : ℚ) = 261121 := by rw [h]; norm_num
  exact_mod_cast h'
lemma v9 : aR 9 = 1046529 := by
  have h := cfn0 9 (by norm_num) (by norm_num)
  have h' : (aR 9 : ℚ) = 1046529 := by rw [h]; norm_num
  exact_mod_cast h'
lemma v10 : aR 10 = 4190209 := by
  have h := cfn0 10 (by norm_num) (by norm_num)
  have h' : (aR 10 : ℚ) = 4190209 := by rw [h]; norm_num
  exact_mod_cast h'
lemma v11 : aR 11 = 16769025 := by
  have h := cfn0 11 (by norm_num) (by norm_num)
  have h' : (aR 11 : ℚ) = 16769025 := by rw [h]; norm_num
  exact_mod_cast h'

end OeisA273767_R921

namespace OeisA273767_R929


/-- Rule 929: new state from the cell's state `c` and its number `k` of ON neighbors
(Wolfram's outer totalistic code: bit `2k + c` of 929). -/
def ruleR (c : Bool) (k : ℕ) : Bool := (929 : ℕ).testBit (2 * k + cond c 1 0)

/-- The four von Neumann neighbors. -/
def nbrsR (p : ℤ × ℤ) : List (ℤ × ℤ) :=
  [(p.1 + 1, p.2), (p.1 - 1, p.2), (p.1, p.2 + 1), (p.1, p.2 - 1)]

/-- The automaton on `ℤ × ℤ`, started from the single ON cell at the origin. -/
def stateR : ℕ → ℤ × ℤ → Bool
  | 0, p => decide (p = (0, 0))
  | t + 1, p => ruleR (stateR t p) ((nbrsR p).countP (fun q => stateR t q))


/-- A273767(n): the number of ON cells of stage `2^n - 1` in the square `[-(2^n-1), 2^n-1]²`. -/
def aR (n : ℕ) : ℕ :=
  ∑ x ∈ Finset.range (2 * (2 ^ n - 1) + 1), ∑ y ∈ Finset.range (2 * (2 ^ n - 1) + 1), if stateR (2 ^ n - 1) ((x : ℤ) - (2 ^ n - 1 : ℕ), (y : ℤ) - (2 ^ n - 1 : ℕ)) then 1 else 0


/-! ## A finite certificate: stages `0..5` on the window `[-5, 5]²` -/

/-- The background (the state of every cell far from the origin). -/
def bg : ℕ → Bool
  | 0 => false
  | t + 1 => ruleR (bg t) (cond (bg t) 4 0)

lemma countP_const (p : ℤ × ℤ) (f : ℤ × ℤ → Bool) (b : Bool) (h : ∀ q ∈ nbrsR p, f q = b) :
    (nbrsR p).countP f = cond b 4 0 := by
  have h1 := h (p.1 + 1, p.2) (by simp [nbrsR])
  have h2 := h (p.1 - 1, p.2) (by simp [nbrsR])
  have h3 := h (p.1, p.2 + 1) (by simp [nbrsR])
  have h4 := h (p.1, p.2 - 1) (by simp [nbrsR])
  cases b <;> simp [nbrsR, h1, h2, h3, h4]

/-- `p` lies outside the light cone of the origin at time `t`: `t < |x| + |y|`. -/
def far (t : ℕ) (p : ℤ × ℤ) : Prop :=
  (t : ℤ) < p.1 + p.2 ∨ (t : ℤ) < p.1 - p.2 ∨ (t : ℤ) < -p.1 + p.2 ∨ (t : ℤ) < -p.1 - p.2

lemma light_cone (t : ℕ) : ∀ p, far t p → stateR t p = bg t := by
  induction t with
  | zero =>
    intro p hp
    simp only [stateR, bg, decide_eq_false_iff_not]
    rintro rfl
    simp [far] at hp
  | succ t ih =>
    intro p hp
    have hp' : far t p := by unfold far at *; push_cast at hp; omega
    show ruleR (stateR t p) _ = ruleR (bg t) _
    rw [ih p hp', countP_const p _ (bg t) (fun q hq => ih q ?_)]
    simp only [nbrsR, List.mem_cons, List.mem_nil_iff, or_false] at hq
    unfold far at *
    push_cast at hp
    rcases hq with rfl | rfl | rfl | rfl <;> simp only <;> omega

def W : ℕ := 5

/-- A stage: the background bit and the rows `y = -W..W` as bitsets (bit `x + W` of row
`y + W` is the cell `(x, y)`). -/
def decode (s : Bool × List ℕ) (p : ℤ × ℤ) : Bool :=
  if -(W : ℤ) ≤ p.1 ∧ p.1 ≤ W ∧ -(W : ℤ) ≤ p.2 ∧ p.2 ≤ W then
    (s.2.getD (p.2 + W).toNat 0).testBit (p.1 + W).toNat
  else s.1

def cell (i j : ℕ) : ℤ × ℤ := ((i : ℤ) - W, (j : ℤ) - W)

/-- One step, checked on every window cell, and the background update. -/
def stepOK (s s' : Bool × List ℕ) : Bool :=
  (s'.1 == ruleR s.1 (cond s.1 4 0)) &&
  (List.range (2 * W + 1)).all fun i => (List.range (2 * W + 1)).all fun j =>
    decode s' (cell i j) == ruleR (decode s (cell i j)) ((nbrsR (cell i j)).countP (decode s))

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

lemma init_ok (s : Bool × List ℕ) (h : initOK s = true) : ∀ p, stateR 0 p = decode s p := by
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

lemma step_ok (t : ℕ) (s s' : Bool × List ℕ) (ht : t + 1 ≤ W) (hs : ∀ p, stateR t p = decode s p)
    (hb : s.1 = bg t) (hok : stepOK s s' = true) : ∀ p, stateR (t + 1) p = decode s' p := by
  simp only [stepOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at hok
  obtain ⟨hbg, hcells⟩ := hok
  intro p
  by_cases hw : -(W : ℤ) ≤ p.1 ∧ p.1 ≤ W ∧ -(W : ℤ) ≤ p.2 ∧ p.2 ≤ W
  · obtain ⟨i, hi, j, hj, rfl⟩ := in_window p hw
    rw [hcells i hi j hj]
    show ruleR (stateR t (cell i j)) ((nbrsR (cell i j)).countP (fun q => stateR t q)) = _
    rw [hs, show (fun q => stateR t q) = decode s from funext hs]
  · have hfar : far (t + 1) p := by unfold far; push_cast; omega
    rw [light_cone (t + 1) p hfar]
    unfold decode
    rw [if_neg hw, hbg, hb]
    rfl

/-- The stages `0..5`, computed outside Lean and checked cell by cell below. -/
def stages : List (Bool × List ℕ) :=
  [(false, [0, 0, 0, 0, 0, 32, 0, 0, 0, 0, 0]),
    (true, [2047, 2047, 2047, 2047, 2015, 1935, 2015, 2047, 2047, 2047, 2047]),
    (true, [2047, 2047, 2047, 2047, 2015, 1967, 2015, 2047, 2047, 2047, 2047]),
    (true, [2047, 2047, 2047, 2047, 2047, 2015, 2047, 2047, 2047, 2047, 2047]),
    (true, [2047, 2047, 2047, 2047, 2047, 2047, 2047, 2047, 2047, 2047, 2047]),
    (true, [2047, 2047, 2047, 2047, 2047, 2047, 2047, 2047, 2047, 2047, 2047])]



/-! ## The periodic regime: the window border shows the background -/

def borderOK (s : Bool × List ℕ) : Bool :=
  (List.range (2 * W + 1)).all fun i => (List.range (2 * W + 1)).all fun j =>
    !(i == 0 || i == 2 * W || j == 0 || j == 2 * W) || (decode s (cell i j) == s.1)

lemma border_nbr (p q : ℤ × ℤ) (hp : ¬ (-(W : ℤ) ≤ p.1 ∧ p.1 ≤ W ∧ -(W : ℤ) ≤ p.2 ∧ p.2 ≤ W))
    (hq : q ∈ nbrsR p) (hw : -(W : ℤ) ≤ q.1 ∧ q.1 ≤ W ∧ -(W : ℤ) ≤ q.2 ∧ q.2 ≤ W) :
    ∃ i < 2 * W + 1, ∃ j < 2 * W + 1, q = cell i j ∧ (i = 0 ∨ i = 2 * W ∨ j = 0 ∨ j = 2 * W) := by
  obtain ⟨i, hi, j, hj, rfl⟩ := in_window q hw
  refine ⟨i, hi, j, hj, rfl, ?_⟩
  obtain ⟨x, y⟩ := p
  simp only [nbrsR, cell, List.mem_cons, Prod.mk.injEq, List.mem_nil_iff, or_false] at hq hp
  omega

lemma step_border (t : ℕ) (s s' : Bool × List ℕ) (hs : ∀ p, stateR t p = decode s p)
    (hbd : borderOK s = true) (hok : stepOK s s' = true) : ∀ p, stateR (t + 1) p = decode s' p := by
  simp only [stepOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at hok
  obtain ⟨hbg, hcells⟩ := hok
  intro p
  by_cases hw : -(W : ℤ) ≤ p.1 ∧ p.1 ≤ W ∧ -(W : ℤ) ≤ p.2 ∧ p.2 ≤ W
  · obtain ⟨i, hi, j, hj, rfl⟩ := in_window p hw
    rw [hcells i hi j hj]
    show ruleR (stateR t (cell i j)) ((nbrsR (cell i j)).countP (fun q => stateR t q)) = _
    rw [hs, show (fun q => stateR t q) = decode s from funext hs]
  · have hp : decode s p = s.1 := by unfold decode; rw [if_neg hw]
    have hn : ∀ q ∈ nbrsR p, decode s q = s.1 := by
      intro q hq
      by_cases hqw : -(W : ℤ) ≤ q.1 ∧ q.1 ≤ W ∧ -(W : ℤ) ≤ q.2 ∧ q.2 ≤ W
      · obtain ⟨i, hi, j, hj, rfl, hb⟩ := border_nbr p q hw hq hqw
        have := (List.all_eq_true.mp ((List.all_eq_true.mp hbd) i (List.mem_range.mpr hi)))
          j (List.mem_range.mpr hj)
        rcases hb with rfl | rfl | rfl | rfl <;> simpa using this
      · unfold decode; rw [if_neg hqw]
    show ruleR (stateR t p) ((nbrsR p).countP (fun q => stateR t q)) = decode s' p
    rw [hs, show (fun q => stateR t q) = decode s from funext hs, hp, countP_const p _ s.1 hn]
    unfold decode
    rw [if_neg hw, hbg]


lemma stages_ok : initOK (stages.getD 0 default) = true ∧
    (∀ t < 5, stepOK (stages.getD t default) (stages.getD (t + 1) default) = true) ∧
    (∀ r < 1, borderOK (stages.getD (4 + r) default) = true) ∧
    stages.getD 5 default = stages.getD 4 default := by
  decide +kernel

lemma certified (t : ℕ) (ht : t ≤ 5) :
    (stages.getD t default).1 = bg t ∧ ∀ p, stateR t p = decode (stages.getD t default) p := by
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
    ∀ p, stateR (4 + m) p = decode (stages.getD (4 + m % 1) default) p := by
  induction m with
  | zero => simpa using (certified 4 (by norm_num)).2
  | succ m ih =>
    have hr : m % 1 < 1 := Nat.mod_lt _ (by norm_num)
    have hb := stages_ok.2.2.1 (m % 1) hr
    have hok := stages_ok.2.1 (4 + m % 1) (by omega)
    rcases (by omega : m % 1 + 1 < 1 ∨ m % 1 + 1 = 1) with h | h
    · rw [show (m + 1) % 1 = m % 1 + 1 by omega]
      exact step_border (4 + m) _ _ ih hb hok
    · rw [show (m + 1) % 1 = 0 by omega, Nat.add_zero, ← stages_ok.2.2.2]
      rw [show 5 = 4 + m % 1 + 1 by omega]
      exact step_border (4 + m) _ _ ih hb hok

/-- The stage shown at time `t`. -/
def stageOf (t : ℕ) : Bool × List ℕ :=
  if t < 4 then stages.getD t default else stages.getD (4 + (t - 4) % 1) default

def sim (t : ℕ) : ℤ × ℤ → Bool := decode (stageOf t)

lemma state_eq (t : ℕ) : stateR t = sim t := by
  funext p
  unfold sim stageOf
  split_ifs with h
  · exact (certified t (by omega)).2 p
  · obtain ⟨m, rfl⟩ : ∃ m, t = 4 + m := ⟨t - 4, by omega⟩
    rw [periodic_all m p, Nat.add_sub_cancel_left]

lemma period (t : ℕ) (ht : 4 ≤ t) : stateR (t + 1) = stateR t := by
  rw [state_eq, state_eq]
  unfold sim stageOf
  rw [if_neg (by omega), if_neg (by omega), show (t + 1 - 4) % 1 = (t - 4) % 1 by omega]

/-- The background bit shown at time `t ≥ 4`. -/
def bgOf (t : ℕ) : Bool := (stages.getD (4 + (t - 4) % 1) default).1

lemma outside (t : ℕ) (ht : 4 ≤ t) (p : ℤ × ℤ)
    (hp : ¬ (-(W : ℤ) ≤ p.1 ∧ p.1 ≤ W ∧ -(W : ℤ) ≤ p.2 ∧ p.2 ≤ W)) : stateR t p = bgOf t := by
  rw [state_eq]
  unfold sim stageOf decode bgOf
  rw [if_neg hp, if_neg (show ¬ (t < 4) by omega)]

def aSim (n : ℕ) : ℕ :=
  ∑ x ∈ Finset.range (2 * (2 ^ n - 1) + 1), ∑ y ∈ Finset.range (2 * (2 ^ n - 1) + 1), if sim (2 ^ n - 1) ((x : ℤ) - (2 ^ n - 1 : ℕ), (y : ℤ) - (2 ^ n - 1 : ℕ)) then 1 else 0

lemma a_eq (n : ℕ) : aR n = aSim n := by
  unfold aR aSim
  simp only [state_eq]

/-- The values a(0..2); the listed terms are among them (control). -/
lemma vals : ∀ n ≤ 2, aR n = ([1, 4, 48] : List ℕ).getD n 0 := by
  intro n hn
  rw [a_eq n]
  revert n
  decide +kernel

lemma v0 : aR 0 = 1 := vals 0 (by norm_num)
lemma v1 : aR 1 = 4 := vals 1 (by norm_num)
lemma v2 : aR 2 = 48 := vals 2 (by norm_num)

/-! ## Counting ON cells: outside the window every cell shows the background -/

/-- The number of ON cells of stage `n` in the square `[-n, n]²`. -/
def cnt (n : ℕ) : ℕ :=
  ∑ x ∈ Finset.range (2 * n + 1), ∑ y ∈ Finset.range (2 * n + 1),
    if stateR n ((x : ℤ) - n, (y : ℤ) - n) then 1 else 0

lemma sum_window (g : ℤ → ℤ) (hg : ∀ z : ℤ, (W : ℤ) < z ∨ z < -(W : ℤ) → g z = 0) (n : ℕ)
    (hn : W ≤ n) :
    ∑ x ∈ Finset.range (2 * n + 1), g ((x : ℤ) - n) =
      ∑ i ∈ Finset.range (2 * W + 1), g ((i : ℤ) - W) := by
  induction n, hn using Nat.le_induction with
  | base => rfl
  | succ n hn ih =>
    rw [show 2 * (n + 1) + 1 = 2 * n + 1 + 1 + 1 by ring, Finset.sum_range_succ,
      Finset.sum_range_succ', hg _ (by push_cast; omega), hg _ (by push_cast; omega), add_zero,
      add_zero, ← ih]
    refine Finset.sum_congr rfl fun x _ => ?_
    congr 1
    push_cast
    ring

lemma sum_window2 (g : ℤ → ℤ → ℤ)
    (hg : ∀ x y : ℤ, (W : ℤ) < x ∨ x < -(W : ℤ) ∨ (W : ℤ) < y ∨ y < -(W : ℤ) → g x y = 0) (n : ℕ)
    (hn : W ≤ n) :
    ∑ x ∈ Finset.range (2 * n + 1), ∑ y ∈ Finset.range (2 * n + 1), g ((x : ℤ) - n) ((y : ℤ) - n) =
      ∑ i ∈ Finset.range (2 * W + 1), ∑ j ∈ Finset.range (2 * W + 1), g ((i : ℤ) - W) ((j : ℤ) - W) := by
  have h1 : ∀ x ∈ Finset.range (2 * n + 1),
      ∑ y ∈ Finset.range (2 * n + 1), g ((x : ℤ) - n) ((y : ℤ) - n) =
        ∑ j ∈ Finset.range (2 * W + 1), g ((x : ℤ) - n) ((j : ℤ) - W) :=
    fun x _ => sum_window (g ((x : ℤ) - n)) (fun z hz => hg _ _ (by omega)) n hn
  rw [Finset.sum_congr rfl h1]
  exact sum_window (fun z => ∑ j ∈ Finset.range (2 * W + 1), g z ((j : ℤ) - W))
    (fun z hz => Finset.sum_eq_zero fun j _ => hg _ _ (by omega)) n hn

/-- A cell minus the background, as an integer. -/
def dl (n : ℕ) (x y : ℤ) : ℤ := (if stateR n (x, y) then 1 else 0) - (if bgOf n then 1 else 0)

lemma dl_out (n : ℕ) (hn : 4 ≤ n) (x y : ℤ)
    (h : (W : ℤ) < x ∨ x < -(W : ℤ) ∨ (W : ℤ) < y ∨ y < -(W : ℤ)) : dl n x y = 0 := by
  unfold dl
  rw [outside n hn (x, y) (by simp only; omega)]
  simp

lemma cnt_eq (n : ℕ) (hn : 5 ≤ n) :
    (cnt n : ℤ) = (if bgOf n then 1 else 0) * (2 * (n : ℤ) + 1) ^ 2 +
      ∑ i ∈ Finset.range (2 * W + 1), ∑ j ∈ Finset.range (2 * W + 1),
        dl n ((i : ℤ) - W) ((j : ℤ) - W) := by
  have e : ∀ x y : ℤ, (if stateR n (x, y) then (1 : ℤ) else 0) = (if bgOf n then 1 else 0) + dl n x y := by
    intro x y; unfold dl; ring
  have hW : W ≤ n := by unfold W; omega
  unfold cnt
  push_cast
  simp only [e]
  rw [Finset.sum_congr rfl (fun x _ => Finset.sum_add_distrib), Finset.sum_add_distrib,
    sum_window2 (dl n) (fun x y h => dl_out n (by omega) x y h) n hW]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  push_cast
  ring


lemma cntn0 (n : ℕ) (h1 : 5 ≤ n) (h2 : n % 1 = 0) :
    (cnt n : ℚ) = 1 * (2 * (n : ℚ) + 1) ^ 2 + (0 : ℚ) := by
  have hk : 4 + (n - 4) % 1 = 4 := by omega
  have hb : bgOf n = true := by unfold bgOf; rw [hk]; rfl
  have hd : ∑ i ∈ Finset.range (2 * W + 1), ∑ j ∈ Finset.range (2 * W + 1),
      dl n ((i : ℤ) - W) ((j : ℤ) - W) = 0 := by
    unfold dl
    rw [state_eq n, hb]
    unfold sim stageOf
    rw [if_neg (by omega), hk]
    decide +kernel
  have h := cnt_eq n h1
  rw [hb, hd, if_pos rfl] at h
  have hc : (cnt n : ℚ) = ((cnt n : ℤ) : ℚ) := by norm_cast
  rw [hc, h]
  push_cast
  ring


lemma cfn0 (n : ℕ) (h1 : 3 ≤ n) (h2 : n % 1 = 0) :
    (aR n : ℚ) = 1 * (2 * (2 : ℚ) ^ n - 1) ^ 2 + (0 : ℚ) := by
  have hp : 2 ^ 3 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h1
  have hs : 5 ≤ 2 ^ n - 1 := by norm_num at hp; omega
  have hr : (2 ^ n - 1) % 1 = 0 := by
    omega
  have h := cntn0 (2 ^ n - 1) hs hr
  have hc : ((2 ^ n - 1 : ℕ) : ℚ) = (2 : ℚ) ^ n - 1 := by
    rw [Nat.cast_sub Nat.one_le_two_pow]; push_cast; ring
  show (cnt (2 ^ n - 1) : ℚ) = _
  rw [h, hc]
  ring

lemma v3 : aR 3 = 225 := by
  have h := cfn0 3 (by norm_num) (by norm_num)
  have h' : (aR 3 : ℚ) = 225 := by rw [h]; norm_num
  exact_mod_cast h'
lemma v4 : aR 4 = 961 := by
  have h := cfn0 4 (by norm_num) (by norm_num)
  have h' : (aR 4 : ℚ) = 961 := by rw [h]; norm_num
  exact_mod_cast h'
lemma v5 : aR 5 = 3969 := by
  have h := cfn0 5 (by norm_num) (by norm_num)
  have h' : (aR 5 : ℚ) = 3969 := by rw [h]; norm_num
  exact_mod_cast h'
lemma v6 : aR 6 = 16129 := by
  have h := cfn0 6 (by norm_num) (by norm_num)
  have h' : (aR 6 : ℚ) = 16129 := by rw [h]; norm_num
  exact_mod_cast h'
lemma v7 : aR 7 = 65025 := by
  have h := cfn0 7 (by norm_num) (by norm_num)
  have h' : (aR 7 : ℚ) = 65025 := by rw [h]; norm_num
  exact_mod_cast h'
lemma v8 : aR 8 = 261121 := by
  have h := cfn0 8 (by norm_num) (by norm_num)
  have h' : (aR 8 : ℚ) = 261121 := by rw [h]; norm_num
  exact_mod_cast h'
lemma v9 : aR 9 = 1046529 := by
  have h := cfn0 9 (by norm_num) (by norm_num)
  have h' : (aR 9 : ℚ) = 1046529 := by rw [h]; norm_num
  exact_mod_cast h'
lemma v10 : aR 10 = 4190209 := by
  have h := cfn0 10 (by norm_num) (by norm_num)
  have h' : (aR 10 : ℚ) = 4190209 := by rw [h]; norm_num
  exact_mod_cast h'
lemma v11 : aR 11 = 16769025 := by
  have h := cfn0 11 (by norm_num) (by norm_num)
  have h' : (aR 11 : ℚ) = 16769025 := by rw [h]; norm_num
  exact_mod_cast h'

end OeisA273767_R929

namespace OeisA273767_R937


/-- Rule 937: new state from the cell's state `c` and its number `k` of ON neighbors
(Wolfram's outer totalistic code: bit `2k + c` of 937). -/
def ruleR (c : Bool) (k : ℕ) : Bool := (937 : ℕ).testBit (2 * k + cond c 1 0)

/-- The four von Neumann neighbors. -/
def nbrsR (p : ℤ × ℤ) : List (ℤ × ℤ) :=
  [(p.1 + 1, p.2), (p.1 - 1, p.2), (p.1, p.2 + 1), (p.1, p.2 - 1)]

/-- The automaton on `ℤ × ℤ`, started from the single ON cell at the origin. -/
def stateR : ℕ → ℤ × ℤ → Bool
  | 0, p => decide (p = (0, 0))
  | t + 1, p => ruleR (stateR t p) ((nbrsR p).countP (fun q => stateR t q))


/-- A273767(n): the number of ON cells of stage `2^n - 1` in the square `[-(2^n-1), 2^n-1]²`. -/
def aR (n : ℕ) : ℕ :=
  ∑ x ∈ Finset.range (2 * (2 ^ n - 1) + 1), ∑ y ∈ Finset.range (2 * (2 ^ n - 1) + 1), if stateR (2 ^ n - 1) ((x : ℤ) - (2 ^ n - 1 : ℕ), (y : ℤ) - (2 ^ n - 1 : ℕ)) then 1 else 0


/-! ## A finite certificate: stages `0..5` on the window `[-5, 5]²` -/

/-- The background (the state of every cell far from the origin). -/
def bg : ℕ → Bool
  | 0 => false
  | t + 1 => ruleR (bg t) (cond (bg t) 4 0)

lemma countP_const (p : ℤ × ℤ) (f : ℤ × ℤ → Bool) (b : Bool) (h : ∀ q ∈ nbrsR p, f q = b) :
    (nbrsR p).countP f = cond b 4 0 := by
  have h1 := h (p.1 + 1, p.2) (by simp [nbrsR])
  have h2 := h (p.1 - 1, p.2) (by simp [nbrsR])
  have h3 := h (p.1, p.2 + 1) (by simp [nbrsR])
  have h4 := h (p.1, p.2 - 1) (by simp [nbrsR])
  cases b <;> simp [nbrsR, h1, h2, h3, h4]

/-- `p` lies outside the light cone of the origin at time `t`: `t < |x| + |y|`. -/
def far (t : ℕ) (p : ℤ × ℤ) : Prop :=
  (t : ℤ) < p.1 + p.2 ∨ (t : ℤ) < p.1 - p.2 ∨ (t : ℤ) < -p.1 + p.2 ∨ (t : ℤ) < -p.1 - p.2

lemma light_cone (t : ℕ) : ∀ p, far t p → stateR t p = bg t := by
  induction t with
  | zero =>
    intro p hp
    simp only [stateR, bg, decide_eq_false_iff_not]
    rintro rfl
    simp [far] at hp
  | succ t ih =>
    intro p hp
    have hp' : far t p := by unfold far at *; push_cast at hp; omega
    show ruleR (stateR t p) _ = ruleR (bg t) _
    rw [ih p hp', countP_const p _ (bg t) (fun q hq => ih q ?_)]
    simp only [nbrsR, List.mem_cons, List.mem_nil_iff, or_false] at hq
    unfold far at *
    push_cast at hp
    rcases hq with rfl | rfl | rfl | rfl <;> simp only <;> omega

def W : ℕ := 5

/-- A stage: the background bit and the rows `y = -W..W` as bitsets (bit `x + W` of row
`y + W` is the cell `(x, y)`). -/
def decode (s : Bool × List ℕ) (p : ℤ × ℤ) : Bool :=
  if -(W : ℤ) ≤ p.1 ∧ p.1 ≤ W ∧ -(W : ℤ) ≤ p.2 ∧ p.2 ≤ W then
    (s.2.getD (p.2 + W).toNat 0).testBit (p.1 + W).toNat
  else s.1

def cell (i j : ℕ) : ℤ × ℤ := ((i : ℤ) - W, (j : ℤ) - W)

/-- One step, checked on every window cell, and the background update. -/
def stepOK (s s' : Bool × List ℕ) : Bool :=
  (s'.1 == ruleR s.1 (cond s.1 4 0)) &&
  (List.range (2 * W + 1)).all fun i => (List.range (2 * W + 1)).all fun j =>
    decode s' (cell i j) == ruleR (decode s (cell i j)) ((nbrsR (cell i j)).countP (decode s))

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

lemma init_ok (s : Bool × List ℕ) (h : initOK s = true) : ∀ p, stateR 0 p = decode s p := by
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

lemma step_ok (t : ℕ) (s s' : Bool × List ℕ) (ht : t + 1 ≤ W) (hs : ∀ p, stateR t p = decode s p)
    (hb : s.1 = bg t) (hok : stepOK s s' = true) : ∀ p, stateR (t + 1) p = decode s' p := by
  simp only [stepOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at hok
  obtain ⟨hbg, hcells⟩ := hok
  intro p
  by_cases hw : -(W : ℤ) ≤ p.1 ∧ p.1 ≤ W ∧ -(W : ℤ) ≤ p.2 ∧ p.2 ≤ W
  · obtain ⟨i, hi, j, hj, rfl⟩ := in_window p hw
    rw [hcells i hi j hj]
    show ruleR (stateR t (cell i j)) ((nbrsR (cell i j)).countP (fun q => stateR t q)) = _
    rw [hs, show (fun q => stateR t q) = decode s from funext hs]
  · have hfar : far (t + 1) p := by unfold far; push_cast; omega
    rw [light_cone (t + 1) p hfar]
    unfold decode
    rw [if_neg hw, hbg, hb]
    rfl

/-- The stages `0..5`, computed outside Lean and checked cell by cell below. -/
def stages : List (Bool × List ℕ) :=
  [(false, [0, 0, 0, 0, 0, 32, 0, 0, 0, 0, 0]),
    (true, [2047, 2047, 2047, 2047, 2015, 1935, 2015, 2047, 2047, 2047, 2047]),
    (true, [2047, 2047, 2047, 2047, 2015, 1967, 2015, 2047, 2047, 2047, 2047]),
    (true, [2047, 2047, 2047, 2047, 2047, 2015, 2047, 2047, 2047, 2047, 2047]),
    (true, [2047, 2047, 2047, 2047, 2047, 2047, 2047, 2047, 2047, 2047, 2047]),
    (true, [2047, 2047, 2047, 2047, 2047, 2047, 2047, 2047, 2047, 2047, 2047])]



/-! ## The periodic regime: the window border shows the background -/

def borderOK (s : Bool × List ℕ) : Bool :=
  (List.range (2 * W + 1)).all fun i => (List.range (2 * W + 1)).all fun j =>
    !(i == 0 || i == 2 * W || j == 0 || j == 2 * W) || (decode s (cell i j) == s.1)

lemma border_nbr (p q : ℤ × ℤ) (hp : ¬ (-(W : ℤ) ≤ p.1 ∧ p.1 ≤ W ∧ -(W : ℤ) ≤ p.2 ∧ p.2 ≤ W))
    (hq : q ∈ nbrsR p) (hw : -(W : ℤ) ≤ q.1 ∧ q.1 ≤ W ∧ -(W : ℤ) ≤ q.2 ∧ q.2 ≤ W) :
    ∃ i < 2 * W + 1, ∃ j < 2 * W + 1, q = cell i j ∧ (i = 0 ∨ i = 2 * W ∨ j = 0 ∨ j = 2 * W) := by
  obtain ⟨i, hi, j, hj, rfl⟩ := in_window q hw
  refine ⟨i, hi, j, hj, rfl, ?_⟩
  obtain ⟨x, y⟩ := p
  simp only [nbrsR, cell, List.mem_cons, Prod.mk.injEq, List.mem_nil_iff, or_false] at hq hp
  omega

lemma step_border (t : ℕ) (s s' : Bool × List ℕ) (hs : ∀ p, stateR t p = decode s p)
    (hbd : borderOK s = true) (hok : stepOK s s' = true) : ∀ p, stateR (t + 1) p = decode s' p := by
  simp only [stepOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at hok
  obtain ⟨hbg, hcells⟩ := hok
  intro p
  by_cases hw : -(W : ℤ) ≤ p.1 ∧ p.1 ≤ W ∧ -(W : ℤ) ≤ p.2 ∧ p.2 ≤ W
  · obtain ⟨i, hi, j, hj, rfl⟩ := in_window p hw
    rw [hcells i hi j hj]
    show ruleR (stateR t (cell i j)) ((nbrsR (cell i j)).countP (fun q => stateR t q)) = _
    rw [hs, show (fun q => stateR t q) = decode s from funext hs]
  · have hp : decode s p = s.1 := by unfold decode; rw [if_neg hw]
    have hn : ∀ q ∈ nbrsR p, decode s q = s.1 := by
      intro q hq
      by_cases hqw : -(W : ℤ) ≤ q.1 ∧ q.1 ≤ W ∧ -(W : ℤ) ≤ q.2 ∧ q.2 ≤ W
      · obtain ⟨i, hi, j, hj, rfl, hb⟩ := border_nbr p q hw hq hqw
        have := (List.all_eq_true.mp ((List.all_eq_true.mp hbd) i (List.mem_range.mpr hi)))
          j (List.mem_range.mpr hj)
        rcases hb with rfl | rfl | rfl | rfl <;> simpa using this
      · unfold decode; rw [if_neg hqw]
    show ruleR (stateR t p) ((nbrsR p).countP (fun q => stateR t q)) = decode s' p
    rw [hs, show (fun q => stateR t q) = decode s from funext hs, hp, countP_const p _ s.1 hn]
    unfold decode
    rw [if_neg hw, hbg]


lemma stages_ok : initOK (stages.getD 0 default) = true ∧
    (∀ t < 5, stepOK (stages.getD t default) (stages.getD (t + 1) default) = true) ∧
    (∀ r < 1, borderOK (stages.getD (4 + r) default) = true) ∧
    stages.getD 5 default = stages.getD 4 default := by
  decide +kernel

lemma certified (t : ℕ) (ht : t ≤ 5) :
    (stages.getD t default).1 = bg t ∧ ∀ p, stateR t p = decode (stages.getD t default) p := by
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
    ∀ p, stateR (4 + m) p = decode (stages.getD (4 + m % 1) default) p := by
  induction m with
  | zero => simpa using (certified 4 (by norm_num)).2
  | succ m ih =>
    have hr : m % 1 < 1 := Nat.mod_lt _ (by norm_num)
    have hb := stages_ok.2.2.1 (m % 1) hr
    have hok := stages_ok.2.1 (4 + m % 1) (by omega)
    rcases (by omega : m % 1 + 1 < 1 ∨ m % 1 + 1 = 1) with h | h
    · rw [show (m + 1) % 1 = m % 1 + 1 by omega]
      exact step_border (4 + m) _ _ ih hb hok
    · rw [show (m + 1) % 1 = 0 by omega, Nat.add_zero, ← stages_ok.2.2.2]
      rw [show 5 = 4 + m % 1 + 1 by omega]
      exact step_border (4 + m) _ _ ih hb hok

/-- The stage shown at time `t`. -/
def stageOf (t : ℕ) : Bool × List ℕ :=
  if t < 4 then stages.getD t default else stages.getD (4 + (t - 4) % 1) default

def sim (t : ℕ) : ℤ × ℤ → Bool := decode (stageOf t)

lemma state_eq (t : ℕ) : stateR t = sim t := by
  funext p
  unfold sim stageOf
  split_ifs with h
  · exact (certified t (by omega)).2 p
  · obtain ⟨m, rfl⟩ : ∃ m, t = 4 + m := ⟨t - 4, by omega⟩
    rw [periodic_all m p, Nat.add_sub_cancel_left]

lemma period (t : ℕ) (ht : 4 ≤ t) : stateR (t + 1) = stateR t := by
  rw [state_eq, state_eq]
  unfold sim stageOf
  rw [if_neg (by omega), if_neg (by omega), show (t + 1 - 4) % 1 = (t - 4) % 1 by omega]

/-- The background bit shown at time `t ≥ 4`. -/
def bgOf (t : ℕ) : Bool := (stages.getD (4 + (t - 4) % 1) default).1

lemma outside (t : ℕ) (ht : 4 ≤ t) (p : ℤ × ℤ)
    (hp : ¬ (-(W : ℤ) ≤ p.1 ∧ p.1 ≤ W ∧ -(W : ℤ) ≤ p.2 ∧ p.2 ≤ W)) : stateR t p = bgOf t := by
  rw [state_eq]
  unfold sim stageOf decode bgOf
  rw [if_neg hp, if_neg (show ¬ (t < 4) by omega)]

def aSim (n : ℕ) : ℕ :=
  ∑ x ∈ Finset.range (2 * (2 ^ n - 1) + 1), ∑ y ∈ Finset.range (2 * (2 ^ n - 1) + 1), if sim (2 ^ n - 1) ((x : ℤ) - (2 ^ n - 1 : ℕ), (y : ℤ) - (2 ^ n - 1 : ℕ)) then 1 else 0

lemma a_eq (n : ℕ) : aR n = aSim n := by
  unfold aR aSim
  simp only [state_eq]

/-- The values a(0..2); the listed terms are among them (control). -/
lemma vals : ∀ n ≤ 2, aR n = ([1, 4, 48] : List ℕ).getD n 0 := by
  intro n hn
  rw [a_eq n]
  revert n
  decide +kernel

lemma v0 : aR 0 = 1 := vals 0 (by norm_num)
lemma v1 : aR 1 = 4 := vals 1 (by norm_num)
lemma v2 : aR 2 = 48 := vals 2 (by norm_num)

/-! ## Counting ON cells: outside the window every cell shows the background -/

/-- The number of ON cells of stage `n` in the square `[-n, n]²`. -/
def cnt (n : ℕ) : ℕ :=
  ∑ x ∈ Finset.range (2 * n + 1), ∑ y ∈ Finset.range (2 * n + 1),
    if stateR n ((x : ℤ) - n, (y : ℤ) - n) then 1 else 0

lemma sum_window (g : ℤ → ℤ) (hg : ∀ z : ℤ, (W : ℤ) < z ∨ z < -(W : ℤ) → g z = 0) (n : ℕ)
    (hn : W ≤ n) :
    ∑ x ∈ Finset.range (2 * n + 1), g ((x : ℤ) - n) =
      ∑ i ∈ Finset.range (2 * W + 1), g ((i : ℤ) - W) := by
  induction n, hn using Nat.le_induction with
  | base => rfl
  | succ n hn ih =>
    rw [show 2 * (n + 1) + 1 = 2 * n + 1 + 1 + 1 by ring, Finset.sum_range_succ,
      Finset.sum_range_succ', hg _ (by push_cast; omega), hg _ (by push_cast; omega), add_zero,
      add_zero, ← ih]
    refine Finset.sum_congr rfl fun x _ => ?_
    congr 1
    push_cast
    ring

lemma sum_window2 (g : ℤ → ℤ → ℤ)
    (hg : ∀ x y : ℤ, (W : ℤ) < x ∨ x < -(W : ℤ) ∨ (W : ℤ) < y ∨ y < -(W : ℤ) → g x y = 0) (n : ℕ)
    (hn : W ≤ n) :
    ∑ x ∈ Finset.range (2 * n + 1), ∑ y ∈ Finset.range (2 * n + 1), g ((x : ℤ) - n) ((y : ℤ) - n) =
      ∑ i ∈ Finset.range (2 * W + 1), ∑ j ∈ Finset.range (2 * W + 1), g ((i : ℤ) - W) ((j : ℤ) - W) := by
  have h1 : ∀ x ∈ Finset.range (2 * n + 1),
      ∑ y ∈ Finset.range (2 * n + 1), g ((x : ℤ) - n) ((y : ℤ) - n) =
        ∑ j ∈ Finset.range (2 * W + 1), g ((x : ℤ) - n) ((j : ℤ) - W) :=
    fun x _ => sum_window (g ((x : ℤ) - n)) (fun z hz => hg _ _ (by omega)) n hn
  rw [Finset.sum_congr rfl h1]
  exact sum_window (fun z => ∑ j ∈ Finset.range (2 * W + 1), g z ((j : ℤ) - W))
    (fun z hz => Finset.sum_eq_zero fun j _ => hg _ _ (by omega)) n hn

/-- A cell minus the background, as an integer. -/
def dl (n : ℕ) (x y : ℤ) : ℤ := (if stateR n (x, y) then 1 else 0) - (if bgOf n then 1 else 0)

lemma dl_out (n : ℕ) (hn : 4 ≤ n) (x y : ℤ)
    (h : (W : ℤ) < x ∨ x < -(W : ℤ) ∨ (W : ℤ) < y ∨ y < -(W : ℤ)) : dl n x y = 0 := by
  unfold dl
  rw [outside n hn (x, y) (by simp only; omega)]
  simp

lemma cnt_eq (n : ℕ) (hn : 5 ≤ n) :
    (cnt n : ℤ) = (if bgOf n then 1 else 0) * (2 * (n : ℤ) + 1) ^ 2 +
      ∑ i ∈ Finset.range (2 * W + 1), ∑ j ∈ Finset.range (2 * W + 1),
        dl n ((i : ℤ) - W) ((j : ℤ) - W) := by
  have e : ∀ x y : ℤ, (if stateR n (x, y) then (1 : ℤ) else 0) = (if bgOf n then 1 else 0) + dl n x y := by
    intro x y; unfold dl; ring
  have hW : W ≤ n := by unfold W; omega
  unfold cnt
  push_cast
  simp only [e]
  rw [Finset.sum_congr rfl (fun x _ => Finset.sum_add_distrib), Finset.sum_add_distrib,
    sum_window2 (dl n) (fun x y h => dl_out n (by omega) x y h) n hW]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  push_cast
  ring


lemma cntn0 (n : ℕ) (h1 : 5 ≤ n) (h2 : n % 1 = 0) :
    (cnt n : ℚ) = 1 * (2 * (n : ℚ) + 1) ^ 2 + (0 : ℚ) := by
  have hk : 4 + (n - 4) % 1 = 4 := by omega
  have hb : bgOf n = true := by unfold bgOf; rw [hk]; rfl
  have hd : ∑ i ∈ Finset.range (2 * W + 1), ∑ j ∈ Finset.range (2 * W + 1),
      dl n ((i : ℤ) - W) ((j : ℤ) - W) = 0 := by
    unfold dl
    rw [state_eq n, hb]
    unfold sim stageOf
    rw [if_neg (by omega), hk]
    decide +kernel
  have h := cnt_eq n h1
  rw [hb, hd, if_pos rfl] at h
  have hc : (cnt n : ℚ) = ((cnt n : ℤ) : ℚ) := by norm_cast
  rw [hc, h]
  push_cast
  ring


lemma cfn0 (n : ℕ) (h1 : 3 ≤ n) (h2 : n % 1 = 0) :
    (aR n : ℚ) = 1 * (2 * (2 : ℚ) ^ n - 1) ^ 2 + (0 : ℚ) := by
  have hp : 2 ^ 3 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h1
  have hs : 5 ≤ 2 ^ n - 1 := by norm_num at hp; omega
  have hr : (2 ^ n - 1) % 1 = 0 := by
    omega
  have h := cntn0 (2 ^ n - 1) hs hr
  have hc : ((2 ^ n - 1 : ℕ) : ℚ) = (2 : ℚ) ^ n - 1 := by
    rw [Nat.cast_sub Nat.one_le_two_pow]; push_cast; ring
  show (cnt (2 ^ n - 1) : ℚ) = _
  rw [h, hc]
  ring

lemma v3 : aR 3 = 225 := by
  have h := cfn0 3 (by norm_num) (by norm_num)
  have h' : (aR 3 : ℚ) = 225 := by rw [h]; norm_num
  exact_mod_cast h'
lemma v4 : aR 4 = 961 := by
  have h := cfn0 4 (by norm_num) (by norm_num)
  have h' : (aR 4 : ℚ) = 961 := by rw [h]; norm_num
  exact_mod_cast h'
lemma v5 : aR 5 = 3969 := by
  have h := cfn0 5 (by norm_num) (by norm_num)
  have h' : (aR 5 : ℚ) = 3969 := by rw [h]; norm_num
  exact_mod_cast h'
lemma v6 : aR 6 = 16129 := by
  have h := cfn0 6 (by norm_num) (by norm_num)
  have h' : (aR 6 : ℚ) = 16129 := by rw [h]; norm_num
  exact_mod_cast h'
lemma v7 : aR 7 = 65025 := by
  have h := cfn0 7 (by norm_num) (by norm_num)
  have h' : (aR 7 : ℚ) = 65025 := by rw [h]; norm_num
  exact_mod_cast h'
lemma v8 : aR 8 = 261121 := by
  have h := cfn0 8 (by norm_num) (by norm_num)
  have h' : (aR 8 : ℚ) = 261121 := by rw [h]; norm_num
  exact_mod_cast h'
lemma v9 : aR 9 = 1046529 := by
  have h := cfn0 9 (by norm_num) (by norm_num)
  have h' : (aR 9 : ℚ) = 1046529 := by rw [h]; norm_num
  exact_mod_cast h'
lemma v10 : aR 10 = 4190209 := by
  have h := cfn0 10 (by norm_num) (by norm_num)
  have h' : (aR 10 : ℚ) = 4190209 := by rw [h]; norm_num
  exact_mod_cast h'
lemma v11 : aR 11 = 16769025 := by
  have h := cfn0 11 (by norm_num) (by norm_num)
  have h' : (aR 11 : ℚ) = 16769025 := by rw [h]; norm_num
  exact_mod_cast h'

end OeisA273767_R937

namespace OeisA273767_R945


/-- Rule 945: new state from the cell's state `c` and its number `k` of ON neighbors
(Wolfram's outer totalistic code: bit `2k + c` of 945). -/
def ruleR (c : Bool) (k : ℕ) : Bool := (945 : ℕ).testBit (2 * k + cond c 1 0)

/-- The four von Neumann neighbors. -/
def nbrsR (p : ℤ × ℤ) : List (ℤ × ℤ) :=
  [(p.1 + 1, p.2), (p.1 - 1, p.2), (p.1, p.2 + 1), (p.1, p.2 - 1)]

/-- The automaton on `ℤ × ℤ`, started from the single ON cell at the origin. -/
def stateR : ℕ → ℤ × ℤ → Bool
  | 0, p => decide (p = (0, 0))
  | t + 1, p => ruleR (stateR t p) ((nbrsR p).countP (fun q => stateR t q))


/-- A273767(n): the number of ON cells of stage `2^n - 1` in the square `[-(2^n-1), 2^n-1]²`. -/
def aR (n : ℕ) : ℕ :=
  ∑ x ∈ Finset.range (2 * (2 ^ n - 1) + 1), ∑ y ∈ Finset.range (2 * (2 ^ n - 1) + 1), if stateR (2 ^ n - 1) ((x : ℤ) - (2 ^ n - 1 : ℕ), (y : ℤ) - (2 ^ n - 1 : ℕ)) then 1 else 0


/-! ## A finite certificate: stages `0..5` on the window `[-5, 5]²` -/

/-- The background (the state of every cell far from the origin). -/
def bg : ℕ → Bool
  | 0 => false
  | t + 1 => ruleR (bg t) (cond (bg t) 4 0)

lemma countP_const (p : ℤ × ℤ) (f : ℤ × ℤ → Bool) (b : Bool) (h : ∀ q ∈ nbrsR p, f q = b) :
    (nbrsR p).countP f = cond b 4 0 := by
  have h1 := h (p.1 + 1, p.2) (by simp [nbrsR])
  have h2 := h (p.1 - 1, p.2) (by simp [nbrsR])
  have h3 := h (p.1, p.2 + 1) (by simp [nbrsR])
  have h4 := h (p.1, p.2 - 1) (by simp [nbrsR])
  cases b <;> simp [nbrsR, h1, h2, h3, h4]

/-- `p` lies outside the light cone of the origin at time `t`: `t < |x| + |y|`. -/
def far (t : ℕ) (p : ℤ × ℤ) : Prop :=
  (t : ℤ) < p.1 + p.2 ∨ (t : ℤ) < p.1 - p.2 ∨ (t : ℤ) < -p.1 + p.2 ∨ (t : ℤ) < -p.1 - p.2

lemma light_cone (t : ℕ) : ∀ p, far t p → stateR t p = bg t := by
  induction t with
  | zero =>
    intro p hp
    simp only [stateR, bg, decide_eq_false_iff_not]
    rintro rfl
    simp [far] at hp
  | succ t ih =>
    intro p hp
    have hp' : far t p := by unfold far at *; push_cast at hp; omega
    show ruleR (stateR t p) _ = ruleR (bg t) _
    rw [ih p hp', countP_const p _ (bg t) (fun q hq => ih q ?_)]
    simp only [nbrsR, List.mem_cons, List.mem_nil_iff, or_false] at hq
    unfold far at *
    push_cast at hp
    rcases hq with rfl | rfl | rfl | rfl <;> simp only <;> omega

def W : ℕ := 5

/-- A stage: the background bit and the rows `y = -W..W` as bitsets (bit `x + W` of row
`y + W` is the cell `(x, y)`). -/
def decode (s : Bool × List ℕ) (p : ℤ × ℤ) : Bool :=
  if -(W : ℤ) ≤ p.1 ∧ p.1 ≤ W ∧ -(W : ℤ) ≤ p.2 ∧ p.2 ≤ W then
    (s.2.getD (p.2 + W).toNat 0).testBit (p.1 + W).toNat
  else s.1

def cell (i j : ℕ) : ℤ × ℤ := ((i : ℤ) - W, (j : ℤ) - W)

/-- One step, checked on every window cell, and the background update. -/
def stepOK (s s' : Bool × List ℕ) : Bool :=
  (s'.1 == ruleR s.1 (cond s.1 4 0)) &&
  (List.range (2 * W + 1)).all fun i => (List.range (2 * W + 1)).all fun j =>
    decode s' (cell i j) == ruleR (decode s (cell i j)) ((nbrsR (cell i j)).countP (decode s))

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

lemma init_ok (s : Bool × List ℕ) (h : initOK s = true) : ∀ p, stateR 0 p = decode s p := by
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

lemma step_ok (t : ℕ) (s s' : Bool × List ℕ) (ht : t + 1 ≤ W) (hs : ∀ p, stateR t p = decode s p)
    (hb : s.1 = bg t) (hok : stepOK s s' = true) : ∀ p, stateR (t + 1) p = decode s' p := by
  simp only [stepOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at hok
  obtain ⟨hbg, hcells⟩ := hok
  intro p
  by_cases hw : -(W : ℤ) ≤ p.1 ∧ p.1 ≤ W ∧ -(W : ℤ) ≤ p.2 ∧ p.2 ≤ W
  · obtain ⟨i, hi, j, hj, rfl⟩ := in_window p hw
    rw [hcells i hi j hj]
    show ruleR (stateR t (cell i j)) ((nbrsR (cell i j)).countP (fun q => stateR t q)) = _
    rw [hs, show (fun q => stateR t q) = decode s from funext hs]
  · have hfar : far (t + 1) p := by unfold far; push_cast; omega
    rw [light_cone (t + 1) p hfar]
    unfold decode
    rw [if_neg hw, hbg, hb]
    rfl

/-- The stages `0..5`, computed outside Lean and checked cell by cell below. -/
def stages : List (Bool × List ℕ) :=
  [(false, [0, 0, 0, 0, 0, 32, 0, 0, 0, 0, 0]),
    (true, [2047, 2047, 2047, 2047, 2015, 1935, 2015, 2047, 2047, 2047, 2047]),
    (true, [2047, 2047, 2047, 2047, 2015, 1967, 2015, 2047, 2047, 2047, 2047]),
    (true, [2047, 2047, 2047, 2047, 2047, 2015, 2047, 2047, 2047, 2047, 2047]),
    (true, [2047, 2047, 2047, 2047, 2047, 2047, 2047, 2047, 2047, 2047, 2047]),
    (true, [2047, 2047, 2047, 2047, 2047, 2047, 2047, 2047, 2047, 2047, 2047])]



/-! ## The periodic regime: the window border shows the background -/

def borderOK (s : Bool × List ℕ) : Bool :=
  (List.range (2 * W + 1)).all fun i => (List.range (2 * W + 1)).all fun j =>
    !(i == 0 || i == 2 * W || j == 0 || j == 2 * W) || (decode s (cell i j) == s.1)

lemma border_nbr (p q : ℤ × ℤ) (hp : ¬ (-(W : ℤ) ≤ p.1 ∧ p.1 ≤ W ∧ -(W : ℤ) ≤ p.2 ∧ p.2 ≤ W))
    (hq : q ∈ nbrsR p) (hw : -(W : ℤ) ≤ q.1 ∧ q.1 ≤ W ∧ -(W : ℤ) ≤ q.2 ∧ q.2 ≤ W) :
    ∃ i < 2 * W + 1, ∃ j < 2 * W + 1, q = cell i j ∧ (i = 0 ∨ i = 2 * W ∨ j = 0 ∨ j = 2 * W) := by
  obtain ⟨i, hi, j, hj, rfl⟩ := in_window q hw
  refine ⟨i, hi, j, hj, rfl, ?_⟩
  obtain ⟨x, y⟩ := p
  simp only [nbrsR, cell, List.mem_cons, Prod.mk.injEq, List.mem_nil_iff, or_false] at hq hp
  omega

lemma step_border (t : ℕ) (s s' : Bool × List ℕ) (hs : ∀ p, stateR t p = decode s p)
    (hbd : borderOK s = true) (hok : stepOK s s' = true) : ∀ p, stateR (t + 1) p = decode s' p := by
  simp only [stepOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at hok
  obtain ⟨hbg, hcells⟩ := hok
  intro p
  by_cases hw : -(W : ℤ) ≤ p.1 ∧ p.1 ≤ W ∧ -(W : ℤ) ≤ p.2 ∧ p.2 ≤ W
  · obtain ⟨i, hi, j, hj, rfl⟩ := in_window p hw
    rw [hcells i hi j hj]
    show ruleR (stateR t (cell i j)) ((nbrsR (cell i j)).countP (fun q => stateR t q)) = _
    rw [hs, show (fun q => stateR t q) = decode s from funext hs]
  · have hp : decode s p = s.1 := by unfold decode; rw [if_neg hw]
    have hn : ∀ q ∈ nbrsR p, decode s q = s.1 := by
      intro q hq
      by_cases hqw : -(W : ℤ) ≤ q.1 ∧ q.1 ≤ W ∧ -(W : ℤ) ≤ q.2 ∧ q.2 ≤ W
      · obtain ⟨i, hi, j, hj, rfl, hb⟩ := border_nbr p q hw hq hqw
        have := (List.all_eq_true.mp ((List.all_eq_true.mp hbd) i (List.mem_range.mpr hi)))
          j (List.mem_range.mpr hj)
        rcases hb with rfl | rfl | rfl | rfl <;> simpa using this
      · unfold decode; rw [if_neg hqw]
    show ruleR (stateR t p) ((nbrsR p).countP (fun q => stateR t q)) = decode s' p
    rw [hs, show (fun q => stateR t q) = decode s from funext hs, hp, countP_const p _ s.1 hn]
    unfold decode
    rw [if_neg hw, hbg]


lemma stages_ok : initOK (stages.getD 0 default) = true ∧
    (∀ t < 5, stepOK (stages.getD t default) (stages.getD (t + 1) default) = true) ∧
    (∀ r < 1, borderOK (stages.getD (4 + r) default) = true) ∧
    stages.getD 5 default = stages.getD 4 default := by
  decide +kernel

lemma certified (t : ℕ) (ht : t ≤ 5) :
    (stages.getD t default).1 = bg t ∧ ∀ p, stateR t p = decode (stages.getD t default) p := by
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
    ∀ p, stateR (4 + m) p = decode (stages.getD (4 + m % 1) default) p := by
  induction m with
  | zero => simpa using (certified 4 (by norm_num)).2
  | succ m ih =>
    have hr : m % 1 < 1 := Nat.mod_lt _ (by norm_num)
    have hb := stages_ok.2.2.1 (m % 1) hr
    have hok := stages_ok.2.1 (4 + m % 1) (by omega)
    rcases (by omega : m % 1 + 1 < 1 ∨ m % 1 + 1 = 1) with h | h
    · rw [show (m + 1) % 1 = m % 1 + 1 by omega]
      exact step_border (4 + m) _ _ ih hb hok
    · rw [show (m + 1) % 1 = 0 by omega, Nat.add_zero, ← stages_ok.2.2.2]
      rw [show 5 = 4 + m % 1 + 1 by omega]
      exact step_border (4 + m) _ _ ih hb hok

/-- The stage shown at time `t`. -/
def stageOf (t : ℕ) : Bool × List ℕ :=
  if t < 4 then stages.getD t default else stages.getD (4 + (t - 4) % 1) default

def sim (t : ℕ) : ℤ × ℤ → Bool := decode (stageOf t)

lemma state_eq (t : ℕ) : stateR t = sim t := by
  funext p
  unfold sim stageOf
  split_ifs with h
  · exact (certified t (by omega)).2 p
  · obtain ⟨m, rfl⟩ : ∃ m, t = 4 + m := ⟨t - 4, by omega⟩
    rw [periodic_all m p, Nat.add_sub_cancel_left]

lemma period (t : ℕ) (ht : 4 ≤ t) : stateR (t + 1) = stateR t := by
  rw [state_eq, state_eq]
  unfold sim stageOf
  rw [if_neg (by omega), if_neg (by omega), show (t + 1 - 4) % 1 = (t - 4) % 1 by omega]

/-- The background bit shown at time `t ≥ 4`. -/
def bgOf (t : ℕ) : Bool := (stages.getD (4 + (t - 4) % 1) default).1

lemma outside (t : ℕ) (ht : 4 ≤ t) (p : ℤ × ℤ)
    (hp : ¬ (-(W : ℤ) ≤ p.1 ∧ p.1 ≤ W ∧ -(W : ℤ) ≤ p.2 ∧ p.2 ≤ W)) : stateR t p = bgOf t := by
  rw [state_eq]
  unfold sim stageOf decode bgOf
  rw [if_neg hp, if_neg (show ¬ (t < 4) by omega)]

def aSim (n : ℕ) : ℕ :=
  ∑ x ∈ Finset.range (2 * (2 ^ n - 1) + 1), ∑ y ∈ Finset.range (2 * (2 ^ n - 1) + 1), if sim (2 ^ n - 1) ((x : ℤ) - (2 ^ n - 1 : ℕ), (y : ℤ) - (2 ^ n - 1 : ℕ)) then 1 else 0

lemma a_eq (n : ℕ) : aR n = aSim n := by
  unfold aR aSim
  simp only [state_eq]

/-- The values a(0..2); the listed terms are among them (control). -/
lemma vals : ∀ n ≤ 2, aR n = ([1, 4, 48] : List ℕ).getD n 0 := by
  intro n hn
  rw [a_eq n]
  revert n
  decide +kernel

lemma v0 : aR 0 = 1 := vals 0 (by norm_num)
lemma v1 : aR 1 = 4 := vals 1 (by norm_num)
lemma v2 : aR 2 = 48 := vals 2 (by norm_num)

/-! ## Counting ON cells: outside the window every cell shows the background -/

/-- The number of ON cells of stage `n` in the square `[-n, n]²`. -/
def cnt (n : ℕ) : ℕ :=
  ∑ x ∈ Finset.range (2 * n + 1), ∑ y ∈ Finset.range (2 * n + 1),
    if stateR n ((x : ℤ) - n, (y : ℤ) - n) then 1 else 0

lemma sum_window (g : ℤ → ℤ) (hg : ∀ z : ℤ, (W : ℤ) < z ∨ z < -(W : ℤ) → g z = 0) (n : ℕ)
    (hn : W ≤ n) :
    ∑ x ∈ Finset.range (2 * n + 1), g ((x : ℤ) - n) =
      ∑ i ∈ Finset.range (2 * W + 1), g ((i : ℤ) - W) := by
  induction n, hn using Nat.le_induction with
  | base => rfl
  | succ n hn ih =>
    rw [show 2 * (n + 1) + 1 = 2 * n + 1 + 1 + 1 by ring, Finset.sum_range_succ,
      Finset.sum_range_succ', hg _ (by push_cast; omega), hg _ (by push_cast; omega), add_zero,
      add_zero, ← ih]
    refine Finset.sum_congr rfl fun x _ => ?_
    congr 1
    push_cast
    ring

lemma sum_window2 (g : ℤ → ℤ → ℤ)
    (hg : ∀ x y : ℤ, (W : ℤ) < x ∨ x < -(W : ℤ) ∨ (W : ℤ) < y ∨ y < -(W : ℤ) → g x y = 0) (n : ℕ)
    (hn : W ≤ n) :
    ∑ x ∈ Finset.range (2 * n + 1), ∑ y ∈ Finset.range (2 * n + 1), g ((x : ℤ) - n) ((y : ℤ) - n) =
      ∑ i ∈ Finset.range (2 * W + 1), ∑ j ∈ Finset.range (2 * W + 1), g ((i : ℤ) - W) ((j : ℤ) - W) := by
  have h1 : ∀ x ∈ Finset.range (2 * n + 1),
      ∑ y ∈ Finset.range (2 * n + 1), g ((x : ℤ) - n) ((y : ℤ) - n) =
        ∑ j ∈ Finset.range (2 * W + 1), g ((x : ℤ) - n) ((j : ℤ) - W) :=
    fun x _ => sum_window (g ((x : ℤ) - n)) (fun z hz => hg _ _ (by omega)) n hn
  rw [Finset.sum_congr rfl h1]
  exact sum_window (fun z => ∑ j ∈ Finset.range (2 * W + 1), g z ((j : ℤ) - W))
    (fun z hz => Finset.sum_eq_zero fun j _ => hg _ _ (by omega)) n hn

/-- A cell minus the background, as an integer. -/
def dl (n : ℕ) (x y : ℤ) : ℤ := (if stateR n (x, y) then 1 else 0) - (if bgOf n then 1 else 0)

lemma dl_out (n : ℕ) (hn : 4 ≤ n) (x y : ℤ)
    (h : (W : ℤ) < x ∨ x < -(W : ℤ) ∨ (W : ℤ) < y ∨ y < -(W : ℤ)) : dl n x y = 0 := by
  unfold dl
  rw [outside n hn (x, y) (by simp only; omega)]
  simp

lemma cnt_eq (n : ℕ) (hn : 5 ≤ n) :
    (cnt n : ℤ) = (if bgOf n then 1 else 0) * (2 * (n : ℤ) + 1) ^ 2 +
      ∑ i ∈ Finset.range (2 * W + 1), ∑ j ∈ Finset.range (2 * W + 1),
        dl n ((i : ℤ) - W) ((j : ℤ) - W) := by
  have e : ∀ x y : ℤ, (if stateR n (x, y) then (1 : ℤ) else 0) = (if bgOf n then 1 else 0) + dl n x y := by
    intro x y; unfold dl; ring
  have hW : W ≤ n := by unfold W; omega
  unfold cnt
  push_cast
  simp only [e]
  rw [Finset.sum_congr rfl (fun x _ => Finset.sum_add_distrib), Finset.sum_add_distrib,
    sum_window2 (dl n) (fun x y h => dl_out n (by omega) x y h) n hW]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  push_cast
  ring


lemma cntn0 (n : ℕ) (h1 : 5 ≤ n) (h2 : n % 1 = 0) :
    (cnt n : ℚ) = 1 * (2 * (n : ℚ) + 1) ^ 2 + (0 : ℚ) := by
  have hk : 4 + (n - 4) % 1 = 4 := by omega
  have hb : bgOf n = true := by unfold bgOf; rw [hk]; rfl
  have hd : ∑ i ∈ Finset.range (2 * W + 1), ∑ j ∈ Finset.range (2 * W + 1),
      dl n ((i : ℤ) - W) ((j : ℤ) - W) = 0 := by
    unfold dl
    rw [state_eq n, hb]
    unfold sim stageOf
    rw [if_neg (by omega), hk]
    decide +kernel
  have h := cnt_eq n h1
  rw [hb, hd, if_pos rfl] at h
  have hc : (cnt n : ℚ) = ((cnt n : ℤ) : ℚ) := by norm_cast
  rw [hc, h]
  push_cast
  ring


lemma cfn0 (n : ℕ) (h1 : 3 ≤ n) (h2 : n % 1 = 0) :
    (aR n : ℚ) = 1 * (2 * (2 : ℚ) ^ n - 1) ^ 2 + (0 : ℚ) := by
  have hp : 2 ^ 3 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h1
  have hs : 5 ≤ 2 ^ n - 1 := by norm_num at hp; omega
  have hr : (2 ^ n - 1) % 1 = 0 := by
    omega
  have h := cntn0 (2 ^ n - 1) hs hr
  have hc : ((2 ^ n - 1 : ℕ) : ℚ) = (2 : ℚ) ^ n - 1 := by
    rw [Nat.cast_sub Nat.one_le_two_pow]; push_cast; ring
  show (cnt (2 ^ n - 1) : ℚ) = _
  rw [h, hc]
  ring

lemma v3 : aR 3 = 225 := by
  have h := cfn0 3 (by norm_num) (by norm_num)
  have h' : (aR 3 : ℚ) = 225 := by rw [h]; norm_num
  exact_mod_cast h'
lemma v4 : aR 4 = 961 := by
  have h := cfn0 4 (by norm_num) (by norm_num)
  have h' : (aR 4 : ℚ) = 961 := by rw [h]; norm_num
  exact_mod_cast h'
lemma v5 : aR 5 = 3969 := by
  have h := cfn0 5 (by norm_num) (by norm_num)
  have h' : (aR 5 : ℚ) = 3969 := by rw [h]; norm_num
  exact_mod_cast h'
lemma v6 : aR 6 = 16129 := by
  have h := cfn0 6 (by norm_num) (by norm_num)
  have h' : (aR 6 : ℚ) = 16129 := by rw [h]; norm_num
  exact_mod_cast h'
lemma v7 : aR 7 = 65025 := by
  have h := cfn0 7 (by norm_num) (by norm_num)
  have h' : (aR 7 : ℚ) = 65025 := by rw [h]; norm_num
  exact_mod_cast h'
lemma v8 : aR 8 = 261121 := by
  have h := cfn0 8 (by norm_num) (by norm_num)
  have h' : (aR 8 : ℚ) = 261121 := by rw [h]; norm_num
  exact_mod_cast h'
lemma v9 : aR 9 = 1046529 := by
  have h := cfn0 9 (by norm_num) (by norm_num)
  have h' : (aR 9 : ℚ) = 1046529 := by rw [h]; norm_num
  exact_mod_cast h'
lemma v10 : aR 10 = 4190209 := by
  have h := cfn0 10 (by norm_num) (by norm_num)
  have h' : (aR 10 : ℚ) = 4190209 := by rw [h]; norm_num
  exact_mod_cast h'
lemma v11 : aR 11 = 16769025 := by
  have h := cfn0 11 (by norm_num) (by norm_num)
  have h' : (aR 11 : ℚ) = 16769025 := by rw [h]; norm_num
  exact_mod_cast h'

end OeisA273767_R945

namespace OeisA273767_R953


/-- Rule 953: new state from the cell's state `c` and its number `k` of ON neighbors
(Wolfram's outer totalistic code: bit `2k + c` of 953). -/
def ruleR (c : Bool) (k : ℕ) : Bool := (953 : ℕ).testBit (2 * k + cond c 1 0)

/-- The four von Neumann neighbors. -/
def nbrsR (p : ℤ × ℤ) : List (ℤ × ℤ) :=
  [(p.1 + 1, p.2), (p.1 - 1, p.2), (p.1, p.2 + 1), (p.1, p.2 - 1)]

/-- The automaton on `ℤ × ℤ`, started from the single ON cell at the origin. -/
def stateR : ℕ → ℤ × ℤ → Bool
  | 0, p => decide (p = (0, 0))
  | t + 1, p => ruleR (stateR t p) ((nbrsR p).countP (fun q => stateR t q))


/-- A273767(n): the number of ON cells of stage `2^n - 1` in the square `[-(2^n-1), 2^n-1]²`. -/
def aR (n : ℕ) : ℕ :=
  ∑ x ∈ Finset.range (2 * (2 ^ n - 1) + 1), ∑ y ∈ Finset.range (2 * (2 ^ n - 1) + 1), if stateR (2 ^ n - 1) ((x : ℤ) - (2 ^ n - 1 : ℕ), (y : ℤ) - (2 ^ n - 1 : ℕ)) then 1 else 0


/-! ## A finite certificate: stages `0..5` on the window `[-5, 5]²` -/

/-- The background (the state of every cell far from the origin). -/
def bg : ℕ → Bool
  | 0 => false
  | t + 1 => ruleR (bg t) (cond (bg t) 4 0)

lemma countP_const (p : ℤ × ℤ) (f : ℤ × ℤ → Bool) (b : Bool) (h : ∀ q ∈ nbrsR p, f q = b) :
    (nbrsR p).countP f = cond b 4 0 := by
  have h1 := h (p.1 + 1, p.2) (by simp [nbrsR])
  have h2 := h (p.1 - 1, p.2) (by simp [nbrsR])
  have h3 := h (p.1, p.2 + 1) (by simp [nbrsR])
  have h4 := h (p.1, p.2 - 1) (by simp [nbrsR])
  cases b <;> simp [nbrsR, h1, h2, h3, h4]

/-- `p` lies outside the light cone of the origin at time `t`: `t < |x| + |y|`. -/
def far (t : ℕ) (p : ℤ × ℤ) : Prop :=
  (t : ℤ) < p.1 + p.2 ∨ (t : ℤ) < p.1 - p.2 ∨ (t : ℤ) < -p.1 + p.2 ∨ (t : ℤ) < -p.1 - p.2

lemma light_cone (t : ℕ) : ∀ p, far t p → stateR t p = bg t := by
  induction t with
  | zero =>
    intro p hp
    simp only [stateR, bg, decide_eq_false_iff_not]
    rintro rfl
    simp [far] at hp
  | succ t ih =>
    intro p hp
    have hp' : far t p := by unfold far at *; push_cast at hp; omega
    show ruleR (stateR t p) _ = ruleR (bg t) _
    rw [ih p hp', countP_const p _ (bg t) (fun q hq => ih q ?_)]
    simp only [nbrsR, List.mem_cons, List.mem_nil_iff, or_false] at hq
    unfold far at *
    push_cast at hp
    rcases hq with rfl | rfl | rfl | rfl <;> simp only <;> omega

def W : ℕ := 5

/-- A stage: the background bit and the rows `y = -W..W` as bitsets (bit `x + W` of row
`y + W` is the cell `(x, y)`). -/
def decode (s : Bool × List ℕ) (p : ℤ × ℤ) : Bool :=
  if -(W : ℤ) ≤ p.1 ∧ p.1 ≤ W ∧ -(W : ℤ) ≤ p.2 ∧ p.2 ≤ W then
    (s.2.getD (p.2 + W).toNat 0).testBit (p.1 + W).toNat
  else s.1

def cell (i j : ℕ) : ℤ × ℤ := ((i : ℤ) - W, (j : ℤ) - W)

/-- One step, checked on every window cell, and the background update. -/
def stepOK (s s' : Bool × List ℕ) : Bool :=
  (s'.1 == ruleR s.1 (cond s.1 4 0)) &&
  (List.range (2 * W + 1)).all fun i => (List.range (2 * W + 1)).all fun j =>
    decode s' (cell i j) == ruleR (decode s (cell i j)) ((nbrsR (cell i j)).countP (decode s))

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

lemma init_ok (s : Bool × List ℕ) (h : initOK s = true) : ∀ p, stateR 0 p = decode s p := by
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

lemma step_ok (t : ℕ) (s s' : Bool × List ℕ) (ht : t + 1 ≤ W) (hs : ∀ p, stateR t p = decode s p)
    (hb : s.1 = bg t) (hok : stepOK s s' = true) : ∀ p, stateR (t + 1) p = decode s' p := by
  simp only [stepOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at hok
  obtain ⟨hbg, hcells⟩ := hok
  intro p
  by_cases hw : -(W : ℤ) ≤ p.1 ∧ p.1 ≤ W ∧ -(W : ℤ) ≤ p.2 ∧ p.2 ≤ W
  · obtain ⟨i, hi, j, hj, rfl⟩ := in_window p hw
    rw [hcells i hi j hj]
    show ruleR (stateR t (cell i j)) ((nbrsR (cell i j)).countP (fun q => stateR t q)) = _
    rw [hs, show (fun q => stateR t q) = decode s from funext hs]
  · have hfar : far (t + 1) p := by unfold far; push_cast; omega
    rw [light_cone (t + 1) p hfar]
    unfold decode
    rw [if_neg hw, hbg, hb]
    rfl

/-- The stages `0..5`, computed outside Lean and checked cell by cell below. -/
def stages : List (Bool × List ℕ) :=
  [(false, [0, 0, 0, 0, 0, 32, 0, 0, 0, 0, 0]),
    (true, [2047, 2047, 2047, 2047, 2015, 1935, 2015, 2047, 2047, 2047, 2047]),
    (true, [2047, 2047, 2047, 2047, 2015, 1967, 2015, 2047, 2047, 2047, 2047]),
    (true, [2047, 2047, 2047, 2047, 2047, 2015, 2047, 2047, 2047, 2047, 2047]),
    (true, [2047, 2047, 2047, 2047, 2047, 2047, 2047, 2047, 2047, 2047, 2047]),
    (true, [2047, 2047, 2047, 2047, 2047, 2047, 2047, 2047, 2047, 2047, 2047])]



/-! ## The periodic regime: the window border shows the background -/

def borderOK (s : Bool × List ℕ) : Bool :=
  (List.range (2 * W + 1)).all fun i => (List.range (2 * W + 1)).all fun j =>
    !(i == 0 || i == 2 * W || j == 0 || j == 2 * W) || (decode s (cell i j) == s.1)

lemma border_nbr (p q : ℤ × ℤ) (hp : ¬ (-(W : ℤ) ≤ p.1 ∧ p.1 ≤ W ∧ -(W : ℤ) ≤ p.2 ∧ p.2 ≤ W))
    (hq : q ∈ nbrsR p) (hw : -(W : ℤ) ≤ q.1 ∧ q.1 ≤ W ∧ -(W : ℤ) ≤ q.2 ∧ q.2 ≤ W) :
    ∃ i < 2 * W + 1, ∃ j < 2 * W + 1, q = cell i j ∧ (i = 0 ∨ i = 2 * W ∨ j = 0 ∨ j = 2 * W) := by
  obtain ⟨i, hi, j, hj, rfl⟩ := in_window q hw
  refine ⟨i, hi, j, hj, rfl, ?_⟩
  obtain ⟨x, y⟩ := p
  simp only [nbrsR, cell, List.mem_cons, Prod.mk.injEq, List.mem_nil_iff, or_false] at hq hp
  omega

lemma step_border (t : ℕ) (s s' : Bool × List ℕ) (hs : ∀ p, stateR t p = decode s p)
    (hbd : borderOK s = true) (hok : stepOK s s' = true) : ∀ p, stateR (t + 1) p = decode s' p := by
  simp only [stepOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at hok
  obtain ⟨hbg, hcells⟩ := hok
  intro p
  by_cases hw : -(W : ℤ) ≤ p.1 ∧ p.1 ≤ W ∧ -(W : ℤ) ≤ p.2 ∧ p.2 ≤ W
  · obtain ⟨i, hi, j, hj, rfl⟩ := in_window p hw
    rw [hcells i hi j hj]
    show ruleR (stateR t (cell i j)) ((nbrsR (cell i j)).countP (fun q => stateR t q)) = _
    rw [hs, show (fun q => stateR t q) = decode s from funext hs]
  · have hp : decode s p = s.1 := by unfold decode; rw [if_neg hw]
    have hn : ∀ q ∈ nbrsR p, decode s q = s.1 := by
      intro q hq
      by_cases hqw : -(W : ℤ) ≤ q.1 ∧ q.1 ≤ W ∧ -(W : ℤ) ≤ q.2 ∧ q.2 ≤ W
      · obtain ⟨i, hi, j, hj, rfl, hb⟩ := border_nbr p q hw hq hqw
        have := (List.all_eq_true.mp ((List.all_eq_true.mp hbd) i (List.mem_range.mpr hi)))
          j (List.mem_range.mpr hj)
        rcases hb with rfl | rfl | rfl | rfl <;> simpa using this
      · unfold decode; rw [if_neg hqw]
    show ruleR (stateR t p) ((nbrsR p).countP (fun q => stateR t q)) = decode s' p
    rw [hs, show (fun q => stateR t q) = decode s from funext hs, hp, countP_const p _ s.1 hn]
    unfold decode
    rw [if_neg hw, hbg]


lemma stages_ok : initOK (stages.getD 0 default) = true ∧
    (∀ t < 5, stepOK (stages.getD t default) (stages.getD (t + 1) default) = true) ∧
    (∀ r < 1, borderOK (stages.getD (4 + r) default) = true) ∧
    stages.getD 5 default = stages.getD 4 default := by
  decide +kernel

lemma certified (t : ℕ) (ht : t ≤ 5) :
    (stages.getD t default).1 = bg t ∧ ∀ p, stateR t p = decode (stages.getD t default) p := by
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
    ∀ p, stateR (4 + m) p = decode (stages.getD (4 + m % 1) default) p := by
  induction m with
  | zero => simpa using (certified 4 (by norm_num)).2
  | succ m ih =>
    have hr : m % 1 < 1 := Nat.mod_lt _ (by norm_num)
    have hb := stages_ok.2.2.1 (m % 1) hr
    have hok := stages_ok.2.1 (4 + m % 1) (by omega)
    rcases (by omega : m % 1 + 1 < 1 ∨ m % 1 + 1 = 1) with h | h
    · rw [show (m + 1) % 1 = m % 1 + 1 by omega]
      exact step_border (4 + m) _ _ ih hb hok
    · rw [show (m + 1) % 1 = 0 by omega, Nat.add_zero, ← stages_ok.2.2.2]
      rw [show 5 = 4 + m % 1 + 1 by omega]
      exact step_border (4 + m) _ _ ih hb hok

/-- The stage shown at time `t`. -/
def stageOf (t : ℕ) : Bool × List ℕ :=
  if t < 4 then stages.getD t default else stages.getD (4 + (t - 4) % 1) default

def sim (t : ℕ) : ℤ × ℤ → Bool := decode (stageOf t)

lemma state_eq (t : ℕ) : stateR t = sim t := by
  funext p
  unfold sim stageOf
  split_ifs with h
  · exact (certified t (by omega)).2 p
  · obtain ⟨m, rfl⟩ : ∃ m, t = 4 + m := ⟨t - 4, by omega⟩
    rw [periodic_all m p, Nat.add_sub_cancel_left]

lemma period (t : ℕ) (ht : 4 ≤ t) : stateR (t + 1) = stateR t := by
  rw [state_eq, state_eq]
  unfold sim stageOf
  rw [if_neg (by omega), if_neg (by omega), show (t + 1 - 4) % 1 = (t - 4) % 1 by omega]

/-- The background bit shown at time `t ≥ 4`. -/
def bgOf (t : ℕ) : Bool := (stages.getD (4 + (t - 4) % 1) default).1

lemma outside (t : ℕ) (ht : 4 ≤ t) (p : ℤ × ℤ)
    (hp : ¬ (-(W : ℤ) ≤ p.1 ∧ p.1 ≤ W ∧ -(W : ℤ) ≤ p.2 ∧ p.2 ≤ W)) : stateR t p = bgOf t := by
  rw [state_eq]
  unfold sim stageOf decode bgOf
  rw [if_neg hp, if_neg (show ¬ (t < 4) by omega)]

def aSim (n : ℕ) : ℕ :=
  ∑ x ∈ Finset.range (2 * (2 ^ n - 1) + 1), ∑ y ∈ Finset.range (2 * (2 ^ n - 1) + 1), if sim (2 ^ n - 1) ((x : ℤ) - (2 ^ n - 1 : ℕ), (y : ℤ) - (2 ^ n - 1 : ℕ)) then 1 else 0

lemma a_eq (n : ℕ) : aR n = aSim n := by
  unfold aR aSim
  simp only [state_eq]

/-- The values a(0..2); the listed terms are among them (control). -/
lemma vals : ∀ n ≤ 2, aR n = ([1, 4, 48] : List ℕ).getD n 0 := by
  intro n hn
  rw [a_eq n]
  revert n
  decide +kernel

lemma v0 : aR 0 = 1 := vals 0 (by norm_num)
lemma v1 : aR 1 = 4 := vals 1 (by norm_num)
lemma v2 : aR 2 = 48 := vals 2 (by norm_num)

/-! ## Counting ON cells: outside the window every cell shows the background -/

/-- The number of ON cells of stage `n` in the square `[-n, n]²`. -/
def cnt (n : ℕ) : ℕ :=
  ∑ x ∈ Finset.range (2 * n + 1), ∑ y ∈ Finset.range (2 * n + 1),
    if stateR n ((x : ℤ) - n, (y : ℤ) - n) then 1 else 0

lemma sum_window (g : ℤ → ℤ) (hg : ∀ z : ℤ, (W : ℤ) < z ∨ z < -(W : ℤ) → g z = 0) (n : ℕ)
    (hn : W ≤ n) :
    ∑ x ∈ Finset.range (2 * n + 1), g ((x : ℤ) - n) =
      ∑ i ∈ Finset.range (2 * W + 1), g ((i : ℤ) - W) := by
  induction n, hn using Nat.le_induction with
  | base => rfl
  | succ n hn ih =>
    rw [show 2 * (n + 1) + 1 = 2 * n + 1 + 1 + 1 by ring, Finset.sum_range_succ,
      Finset.sum_range_succ', hg _ (by push_cast; omega), hg _ (by push_cast; omega), add_zero,
      add_zero, ← ih]
    refine Finset.sum_congr rfl fun x _ => ?_
    congr 1
    push_cast
    ring

lemma sum_window2 (g : ℤ → ℤ → ℤ)
    (hg : ∀ x y : ℤ, (W : ℤ) < x ∨ x < -(W : ℤ) ∨ (W : ℤ) < y ∨ y < -(W : ℤ) → g x y = 0) (n : ℕ)
    (hn : W ≤ n) :
    ∑ x ∈ Finset.range (2 * n + 1), ∑ y ∈ Finset.range (2 * n + 1), g ((x : ℤ) - n) ((y : ℤ) - n) =
      ∑ i ∈ Finset.range (2 * W + 1), ∑ j ∈ Finset.range (2 * W + 1), g ((i : ℤ) - W) ((j : ℤ) - W) := by
  have h1 : ∀ x ∈ Finset.range (2 * n + 1),
      ∑ y ∈ Finset.range (2 * n + 1), g ((x : ℤ) - n) ((y : ℤ) - n) =
        ∑ j ∈ Finset.range (2 * W + 1), g ((x : ℤ) - n) ((j : ℤ) - W) :=
    fun x _ => sum_window (g ((x : ℤ) - n)) (fun z hz => hg _ _ (by omega)) n hn
  rw [Finset.sum_congr rfl h1]
  exact sum_window (fun z => ∑ j ∈ Finset.range (2 * W + 1), g z ((j : ℤ) - W))
    (fun z hz => Finset.sum_eq_zero fun j _ => hg _ _ (by omega)) n hn

/-- A cell minus the background, as an integer. -/
def dl (n : ℕ) (x y : ℤ) : ℤ := (if stateR n (x, y) then 1 else 0) - (if bgOf n then 1 else 0)

lemma dl_out (n : ℕ) (hn : 4 ≤ n) (x y : ℤ)
    (h : (W : ℤ) < x ∨ x < -(W : ℤ) ∨ (W : ℤ) < y ∨ y < -(W : ℤ)) : dl n x y = 0 := by
  unfold dl
  rw [outside n hn (x, y) (by simp only; omega)]
  simp

lemma cnt_eq (n : ℕ) (hn : 5 ≤ n) :
    (cnt n : ℤ) = (if bgOf n then 1 else 0) * (2 * (n : ℤ) + 1) ^ 2 +
      ∑ i ∈ Finset.range (2 * W + 1), ∑ j ∈ Finset.range (2 * W + 1),
        dl n ((i : ℤ) - W) ((j : ℤ) - W) := by
  have e : ∀ x y : ℤ, (if stateR n (x, y) then (1 : ℤ) else 0) = (if bgOf n then 1 else 0) + dl n x y := by
    intro x y; unfold dl; ring
  have hW : W ≤ n := by unfold W; omega
  unfold cnt
  push_cast
  simp only [e]
  rw [Finset.sum_congr rfl (fun x _ => Finset.sum_add_distrib), Finset.sum_add_distrib,
    sum_window2 (dl n) (fun x y h => dl_out n (by omega) x y h) n hW]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  push_cast
  ring


lemma cntn0 (n : ℕ) (h1 : 5 ≤ n) (h2 : n % 1 = 0) :
    (cnt n : ℚ) = 1 * (2 * (n : ℚ) + 1) ^ 2 + (0 : ℚ) := by
  have hk : 4 + (n - 4) % 1 = 4 := by omega
  have hb : bgOf n = true := by unfold bgOf; rw [hk]; rfl
  have hd : ∑ i ∈ Finset.range (2 * W + 1), ∑ j ∈ Finset.range (2 * W + 1),
      dl n ((i : ℤ) - W) ((j : ℤ) - W) = 0 := by
    unfold dl
    rw [state_eq n, hb]
    unfold sim stageOf
    rw [if_neg (by omega), hk]
    decide +kernel
  have h := cnt_eq n h1
  rw [hb, hd, if_pos rfl] at h
  have hc : (cnt n : ℚ) = ((cnt n : ℤ) : ℚ) := by norm_cast
  rw [hc, h]
  push_cast
  ring


lemma cfn0 (n : ℕ) (h1 : 3 ≤ n) (h2 : n % 1 = 0) :
    (aR n : ℚ) = 1 * (2 * (2 : ℚ) ^ n - 1) ^ 2 + (0 : ℚ) := by
  have hp : 2 ^ 3 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h1
  have hs : 5 ≤ 2 ^ n - 1 := by norm_num at hp; omega
  have hr : (2 ^ n - 1) % 1 = 0 := by
    omega
  have h := cntn0 (2 ^ n - 1) hs hr
  have hc : ((2 ^ n - 1 : ℕ) : ℚ) = (2 : ℚ) ^ n - 1 := by
    rw [Nat.cast_sub Nat.one_le_two_pow]; push_cast; ring
  show (cnt (2 ^ n - 1) : ℚ) = _
  rw [h, hc]
  ring

lemma v3 : aR 3 = 225 := by
  have h := cfn0 3 (by norm_num) (by norm_num)
  have h' : (aR 3 : ℚ) = 225 := by rw [h]; norm_num
  exact_mod_cast h'
lemma v4 : aR 4 = 961 := by
  have h := cfn0 4 (by norm_num) (by norm_num)
  have h' : (aR 4 : ℚ) = 961 := by rw [h]; norm_num
  exact_mod_cast h'
lemma v5 : aR 5 = 3969 := by
  have h := cfn0 5 (by norm_num) (by norm_num)
  have h' : (aR 5 : ℚ) = 3969 := by rw [h]; norm_num
  exact_mod_cast h'
lemma v6 : aR 6 = 16129 := by
  have h := cfn0 6 (by norm_num) (by norm_num)
  have h' : (aR 6 : ℚ) = 16129 := by rw [h]; norm_num
  exact_mod_cast h'
lemma v7 : aR 7 = 65025 := by
  have h := cfn0 7 (by norm_num) (by norm_num)
  have h' : (aR 7 : ℚ) = 65025 := by rw [h]; norm_num
  exact_mod_cast h'
lemma v8 : aR 8 = 261121 := by
  have h := cfn0 8 (by norm_num) (by norm_num)
  have h' : (aR 8 : ℚ) = 261121 := by rw [h]; norm_num
  exact_mod_cast h'
lemma v9 : aR 9 = 1046529 := by
  have h := cfn0 9 (by norm_num) (by norm_num)
  have h' : (aR 9 : ℚ) = 1046529 := by rw [h]; norm_num
  exact_mod_cast h'
lemma v10 : aR 10 = 4190209 := by
  have h := cfn0 10 (by norm_num) (by norm_num)
  have h' : (aR 10 : ℚ) = 4190209 := by rw [h]; norm_num
  exact_mod_cast h'
lemma v11 : aR 11 = 16769025 := by
  have h := cfn0 11 (by norm_num) (by norm_num)
  have h' : (aR 11 : ℚ) = 16769025 := by rw [h]; norm_num
  exact_mod_cast h'

end OeisA273767_R953

namespace OMA.S_oeis_a273767








/-! ## A finite certificate: stages `0..5` on the window `[-5, 5]²` -/

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

def W : ℕ := 5

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

/-- The stages `0..5`, computed outside Lean and checked cell by cell below. -/
def stages : List (Bool × List ℕ) :=
  [(false, [0, 0, 0, 0, 0, 32, 0, 0, 0, 0, 0]),
    (true, [2047, 2047, 2047, 2047, 2015, 1935, 2015, 2047, 2047, 2047, 2047]),
    (true, [2047, 2047, 2047, 2047, 1935, 1967, 1935, 2047, 2047, 2047, 2047]),
    (true, [2047, 2047, 2047, 2047, 2047, 2015, 2047, 2047, 2047, 2047, 2047]),
    (true, [2047, 2047, 2047, 2047, 2047, 2047, 2047, 2047, 2047, 2047, 2047]),
    (true, [2047, 2047, 2047, 2047, 2047, 2047, 2047, 2047, 2047, 2047, 2047])]



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
    (∀ t < 5, stepOK (stages.getD t default) (stages.getD (t + 1) default) = true) ∧
    (∀ r < 1, borderOK (stages.getD (4 + r) default) = true) ∧
    stages.getD 5 default = stages.getD 4 default := by
  decide +kernel

lemma certified (t : ℕ) (ht : t ≤ 5) :
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
    ∀ p, state (4 + m) p = decode (stages.getD (4 + m % 1) default) p := by
  induction m with
  | zero => simpa using (certified 4 (by norm_num)).2
  | succ m ih =>
    have hr : m % 1 < 1 := Nat.mod_lt _ (by norm_num)
    have hb := stages_ok.2.2.1 (m % 1) hr
    have hok := stages_ok.2.1 (4 + m % 1) (by omega)
    rcases (by omega : m % 1 + 1 < 1 ∨ m % 1 + 1 = 1) with h | h
    · rw [show (m + 1) % 1 = m % 1 + 1 by omega]
      exact step_border (4 + m) _ _ ih hb hok
    · rw [show (m + 1) % 1 = 0 by omega, Nat.add_zero, ← stages_ok.2.2.2]
      rw [show 5 = 4 + m % 1 + 1 by omega]
      exact step_border (4 + m) _ _ ih hb hok

/-- The stage shown at time `t`. -/
def stageOf (t : ℕ) : Bool × List ℕ :=
  if t < 4 then stages.getD t default else stages.getD (4 + (t - 4) % 1) default

def sim (t : ℕ) : ℤ × ℤ → Bool := decode (stageOf t)

lemma state_eq (t : ℕ) : state t = sim t := by
  funext p
  unfold sim stageOf
  split_ifs with h
  · exact (certified t (by omega)).2 p
  · obtain ⟨m, rfl⟩ : ∃ m, t = 4 + m := ⟨t - 4, by omega⟩
    rw [periodic_all m p, Nat.add_sub_cancel_left]

lemma period (t : ℕ) (ht : 4 ≤ t) : state (t + 1) = state t := by
  rw [state_eq, state_eq]
  unfold sim stageOf
  rw [if_neg (by omega), if_neg (by omega), show (t + 1 - 4) % 1 = (t - 4) % 1 by omega]

/-- The background bit shown at time `t ≥ 4`. -/
def bgOf (t : ℕ) : Bool := (stages.getD (4 + (t - 4) % 1) default).1

lemma outside (t : ℕ) (ht : 4 ≤ t) (p : ℤ × ℤ)
    (hp : ¬ (-(W : ℤ) ≤ p.1 ∧ p.1 ≤ W ∧ -(W : ℤ) ≤ p.2 ∧ p.2 ≤ W)) : state t p = bgOf t := by
  rw [state_eq]
  unfold sim stageOf decode bgOf
  rw [if_neg hp, if_neg (show ¬ (t < 4) by omega)]

def aSim (n : ℕ) : ℕ :=
  ∑ x ∈ Finset.range (2 * (2 ^ n - 1) + 1), ∑ y ∈ Finset.range (2 * (2 ^ n - 1) + 1), if sim (2 ^ n - 1) ((x : ℤ) - (2 ^ n - 1 : ℕ), (y : ℤ) - (2 ^ n - 1 : ℕ)) then 1 else 0

lemma a_eq (n : ℕ) : a n = aSim n := by
  unfold a aSim
  simp only [state_eq]

/-- The values a(0..2); the listed terms are among them (control). -/
lemma vals : ∀ n ≤ 2, a n = ([1, 4, 48] : List ℕ).getD n 0 := by
  intro n hn
  rw [a_eq n]
  revert n
  decide +kernel

lemma v0 : a 0 = 1 := vals 0 (by norm_num)
lemma v1 : a 1 = 4 := vals 1 (by norm_num)
lemma v2 : a 2 = 48 := vals 2 (by norm_num)

/-! ## Counting ON cells: outside the window every cell shows the background -/

/-- The number of ON cells of stage `n` in the square `[-n, n]²`. -/
def cnt (n : ℕ) : ℕ :=
  ∑ x ∈ Finset.range (2 * n + 1), ∑ y ∈ Finset.range (2 * n + 1),
    if state n ((x : ℤ) - n, (y : ℤ) - n) then 1 else 0

lemma sum_window (g : ℤ → ℤ) (hg : ∀ z : ℤ, (W : ℤ) < z ∨ z < -(W : ℤ) → g z = 0) (n : ℕ)
    (hn : W ≤ n) :
    ∑ x ∈ Finset.range (2 * n + 1), g ((x : ℤ) - n) =
      ∑ i ∈ Finset.range (2 * W + 1), g ((i : ℤ) - W) := by
  induction n, hn using Nat.le_induction with
  | base => rfl
  | succ n hn ih =>
    rw [show 2 * (n + 1) + 1 = 2 * n + 1 + 1 + 1 by ring, Finset.sum_range_succ,
      Finset.sum_range_succ', hg _ (by push_cast; omega), hg _ (by push_cast; omega), add_zero,
      add_zero, ← ih]
    refine Finset.sum_congr rfl fun x _ => ?_
    congr 1
    push_cast
    ring

lemma sum_window2 (g : ℤ → ℤ → ℤ)
    (hg : ∀ x y : ℤ, (W : ℤ) < x ∨ x < -(W : ℤ) ∨ (W : ℤ) < y ∨ y < -(W : ℤ) → g x y = 0) (n : ℕ)
    (hn : W ≤ n) :
    ∑ x ∈ Finset.range (2 * n + 1), ∑ y ∈ Finset.range (2 * n + 1), g ((x : ℤ) - n) ((y : ℤ) - n) =
      ∑ i ∈ Finset.range (2 * W + 1), ∑ j ∈ Finset.range (2 * W + 1), g ((i : ℤ) - W) ((j : ℤ) - W) := by
  have h1 : ∀ x ∈ Finset.range (2 * n + 1),
      ∑ y ∈ Finset.range (2 * n + 1), g ((x : ℤ) - n) ((y : ℤ) - n) =
        ∑ j ∈ Finset.range (2 * W + 1), g ((x : ℤ) - n) ((j : ℤ) - W) :=
    fun x _ => sum_window (g ((x : ℤ) - n)) (fun z hz => hg _ _ (by omega)) n hn
  rw [Finset.sum_congr rfl h1]
  exact sum_window (fun z => ∑ j ∈ Finset.range (2 * W + 1), g z ((j : ℤ) - W))
    (fun z hz => Finset.sum_eq_zero fun j _ => hg _ _ (by omega)) n hn

/-- A cell minus the background, as an integer. -/
def dl (n : ℕ) (x y : ℤ) : ℤ := (if state n (x, y) then 1 else 0) - (if bgOf n then 1 else 0)

lemma dl_out (n : ℕ) (hn : 4 ≤ n) (x y : ℤ)
    (h : (W : ℤ) < x ∨ x < -(W : ℤ) ∨ (W : ℤ) < y ∨ y < -(W : ℤ)) : dl n x y = 0 := by
  unfold dl
  rw [outside n hn (x, y) (by simp only; omega)]
  simp

lemma cnt_eq (n : ℕ) (hn : 5 ≤ n) :
    (cnt n : ℤ) = (if bgOf n then 1 else 0) * (2 * (n : ℤ) + 1) ^ 2 +
      ∑ i ∈ Finset.range (2 * W + 1), ∑ j ∈ Finset.range (2 * W + 1),
        dl n ((i : ℤ) - W) ((j : ℤ) - W) := by
  have e : ∀ x y : ℤ, (if state n (x, y) then (1 : ℤ) else 0) = (if bgOf n then 1 else 0) + dl n x y := by
    intro x y; unfold dl; ring
  have hW : W ≤ n := by unfold W; omega
  unfold cnt
  push_cast
  simp only [e]
  rw [Finset.sum_congr rfl (fun x _ => Finset.sum_add_distrib), Finset.sum_add_distrib,
    sum_window2 (dl n) (fun x y h => dl_out n (by omega) x y h) n hW]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  push_cast
  ring


lemma cntn0 (n : ℕ) (h1 : 5 ≤ n) (h2 : n % 1 = 0) :
    (cnt n : ℚ) = 1 * (2 * (n : ℚ) + 1) ^ 2 + (0 : ℚ) := by
  have hk : 4 + (n - 4) % 1 = 4 := by omega
  have hb : bgOf n = true := by unfold bgOf; rw [hk]; rfl
  have hd : ∑ i ∈ Finset.range (2 * W + 1), ∑ j ∈ Finset.range (2 * W + 1),
      dl n ((i : ℤ) - W) ((j : ℤ) - W) = 0 := by
    unfold dl
    rw [state_eq n, hb]
    unfold sim stageOf
    rw [if_neg (by omega), hk]
    decide +kernel
  have h := cnt_eq n h1
  rw [hb, hd, if_pos rfl] at h
  have hc : (cnt n : ℚ) = ((cnt n : ℤ) : ℚ) := by norm_cast
  rw [hc, h]
  push_cast
  ring


lemma cfn0 (n : ℕ) (h1 : 3 ≤ n) (h2 : n % 1 = 0) :
    (a n : ℚ) = 1 * (2 * (2 : ℚ) ^ n - 1) ^ 2 + (0 : ℚ) := by
  have hp : 2 ^ 3 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h1
  have hs : 5 ≤ 2 ^ n - 1 := by norm_num at hp; omega
  have hr : (2 ^ n - 1) % 1 = 0 := by
    omega
  have h := cntn0 (2 ^ n - 1) hs hr
  have hc : ((2 ^ n - 1 : ℕ) : ℚ) = (2 : ℚ) ^ n - 1 := by
    rw [Nat.cast_sub Nat.one_le_two_pow]; push_cast; ring
  show (cnt (2 ^ n - 1) : ℚ) = _
  rw [h, hc]
  ring

lemma v3 : a 3 = 225 := by
  have h := cfn0 3 (by norm_num) (by norm_num)
  have h' : (a 3 : ℚ) = 225 := by rw [h]; norm_num
  exact_mod_cast h'
lemma v4 : a 4 = 961 := by
  have h := cfn0 4 (by norm_num) (by norm_num)
  have h' : (a 4 : ℚ) = 961 := by rw [h]; norm_num
  exact_mod_cast h'
lemma v5 : a 5 = 3969 := by
  have h := cfn0 5 (by norm_num) (by norm_num)
  have h' : (a 5 : ℚ) = 3969 := by rw [h]; norm_num
  exact_mod_cast h'
lemma v6 : a 6 = 16129 := by
  have h := cfn0 6 (by norm_num) (by norm_num)
  have h' : (a 6 : ℚ) = 16129 := by rw [h]; norm_num
  exact_mod_cast h'
lemma v7 : a 7 = 65025 := by
  have h := cfn0 7 (by norm_num) (by norm_num)
  have h' : (a 7 : ℚ) = 65025 := by rw [h]; norm_num
  exact_mod_cast h'
lemma v8 : a 8 = 261121 := by
  have h := cfn0 8 (by norm_num) (by norm_num)
  have h' : (a 8 : ℚ) = 261121 := by rw [h]; norm_num
  exact_mod_cast h'
lemma v9 : a 9 = 1046529 := by
  have h := cfn0 9 (by norm_num) (by norm_num)
  have h' : (a 9 : ℚ) = 1046529 := by rw [h]; norm_num
  exact_mod_cast h'
lemma v10 : a 10 = 4190209 := by
  have h := cfn0 10 (by norm_num) (by norm_num)
  have h' : (a 10 : ℚ) = 4190209 := by rw [h]; norm_num
  exact_mod_cast h'
lemma v11 : a 11 = 16769025 := by
  have h := cfn0 11 (by norm_num) (by norm_num)
  have h' : (a 11 : ℚ) = 16769025 := by rw [h]; norm_num
  exact_mod_cast h'
lemma v12 : a 12 = 67092481 := by
  have h := cfn0 12 (by norm_num) (by norm_num)
  have h' : (a 12 : ℚ) = 67092481 := by rw [h]; norm_num
  exact_mod_cast h'
lemma v13 : a 13 = 268402689 := by
  have h := cfn0 13 (by norm_num) (by norm_num)
  have h' : (a 13 : ℚ) = 268402689 := by rw [h]; norm_num
  exact_mod_cast h'
lemma v14 : a 14 = 1073676289 := by
  have h := cfn0 14 (by norm_num) (by norm_num)
  have h' : (a 14 : ℚ) = 1073676289 := by rw [h]; norm_num
  exact_mod_cast h'
lemma v15 : a 15 = 4294836225 := by
  have h := cfn0 15 (by norm_num) (by norm_num)
  have h' : (a 15 : ℚ) = 4294836225 := by rw [h]; norm_num
  exact_mod_cast h'
lemma v16 : a 16 = 17179607041 := by
  have h := cfn0 16 (by norm_num) (by norm_num)
  have h' : (a 16 : ℚ) = 17179607041 := by rw [h]; norm_num
  exact_mod_cast h'
lemma v17 : a 17 = 68718952449 := by
  have h := cfn0 17 (by norm_num) (by norm_num)
  have h' : (a 17 : ℚ) = 68718952449 := by rw [h]; norm_num
  exact_mod_cast h'

/-- a(n) = (2^(n+1) - 1)^2, n>2 -/
theorem closed0 (n : ℕ) (hn : 3 ≤ n) : (a n : ℚ) = ((((2 : ℚ) ^ (n + 1)) - (1 : ℚ)) ^ 2) := by
  rcases Nat.lt_or_ge n 3 with hlt | hge
  · interval_cases n <;> norm_num [v0, v1, v2, v3] at *
  · obtain ⟨q, rfl⟩ : ∃ q, n = 3 + q := ⟨n - 3, by omega⟩
    have c0 := cfn0 (3 + q) (by omega) (by omega)
    try simp only [pow_add, pow_mul, neg_one_sq, one_pow, mul_one, one_mul] at c0 ⊢
    push_cast at c0 ⊢
    linear_combination (1 / (1 : ℚ)) * c0


/-- a(n) = 7*a(n-1)-14*a(n-2)+8*a(n-3) for n>5 -/
theorem recurrence1 (n : ℕ) (hn : 6 ≤ n) : (a n : ℤ) = ((((7 : ℤ) * (a (n - 1) : ℤ)) - ((14 : ℤ) * (a (n - 2) : ℤ))) + ((8 : ℤ) * (a (n - 3) : ℤ))) := by
  rcases Nat.lt_or_ge n 6 with hlt | hge
  · interval_cases n <;> norm_num [v0, v1, v2, v3, v4, v5, v6] at *
  · suffices hq : (a n : ℚ) = ((((7 : ℚ) * (a (n - 1) : ℚ)) - ((14 : ℚ) * (a (n - 2) : ℚ))) + ((8 : ℚ) * (a (n - 3) : ℚ))) by exact_mod_cast hq
    obtain ⟨q, rfl⟩ : ∃ q, n = 6 + q := ⟨n - 6, by omega⟩
    have c0 := cfn0 (6 + q) (by omega) (by omega)
    rw [show 6 + q - 1 = 5 + q by omega]
    have c1 := cfn0 (5 + q) (by omega) (by omega)
    rw [show 6 + q - 2 = 4 + q by omega]
    have c2 := cfn0 (4 + q) (by omega) (by omega)
    rw [show 6 + q - 3 = 3 + q by omega]
    have c3 := cfn0 (3 + q) (by omega) (by omega)
    try simp only [pow_add, pow_mul, neg_one_sq, one_pow, mul_one, one_mul] at c0 c1 c2 c3 ⊢
    push_cast at c0 c1 c2 c3 ⊢
    linear_combination (1 / (1 : ℚ)) * c0 + (-((7 : ℚ)) / (1 : ℚ)) * c1 + (-((-14 : ℚ)) / (1 : ℚ)) * c2 + (-((8 : ℚ)) / (1 : ℚ)) * c3


lemma gfrec2 (n : ℕ) (hn : 6 ≤ n) : (a n : ℚ) = ((7 : ℚ)) * (a (n - 1) : ℚ) + ((-14 : ℚ)) * (a (n - 2) : ℚ) + ((8 : ℚ)) * (a (n - 3) : ℚ) := by
  rcases Nat.lt_or_ge n 6 with hlt | hge
  · interval_cases n <;> norm_num [v0, v1, v2, v3, v4, v5, v6] at *
  · obtain ⟨q, rfl⟩ : ∃ q, n = 6 + q := ⟨n - 6, by omega⟩
    have c0 := cfn0 (6 + q) (by omega) (by omega)
    rw [show 6 + q - 1 = 5 + q by omega]
    have c1 := cfn0 (5 + q) (by omega) (by omega)
    rw [show 6 + q - 2 = 4 + q by omega]
    have c2 := cfn0 (4 + q) (by omega) (by omega)
    rw [show 6 + q - 3 = 3 + q by omega]
    have c3 := cfn0 (3 + q) (by omega) (by omega)
    try simp only [pow_add, pow_mul, neg_one_sq, one_pow, mul_one, one_mul] at c0 c1 c2 c3 ⊢
    push_cast at c0 c1 c2 c3 ⊢
    linear_combination (1 / (1 : ℚ)) * c0 + (-((7 : ℚ)) / (1 : ℚ)) * c1 + (-((-14 : ℚ)) / (1 : ℚ)) * c2 + (-((8 : ℚ)) / (1 : ℚ)) * c3

open PowerSeries in
/-- G.f.: (1-3*x+34*x^2-63*x^3+26*x^4+8*x^5) / ((1-x)*(1-2*x)*(1-4*x)) -/
theorem gf2 : PowerSeries.mk (fun n => (a n : ℚ)) = ((1-3*X+34*X ^ 2-63*X ^ 3+26*X ^ 4+8*X ^ 5)) * (((1-X)*(1-2*X)*(1-4*X)))⁻¹ := by
  set G : ℚ⟦X⟧ := PowerSeries.mk (fun n => (a n : ℚ))
  have hden : constantCoeff ((((1-X)*(1-2*X)*(1-4*X))) : ℚ⟦X⟧) ≠ 0 := by simp
  have eQ : G * (((1-X)*(1-2*X)*(1-4*X))) = C ((1 : ℚ)) * G + C ((-7 : ℚ)) * (G * X ^ 1) + C ((14 : ℚ)) * (G * X ^ 2) + C ((-8 : ℚ)) * (G * X ^ 3) := by
    (try simp only [map_neg, map_ofNat, map_one, map_div₀, map_natCast]) <;> ring
  have eP : (((1-3*X+34*X ^ 2-63*X ^ 3+26*X ^ 4+8*X ^ 5)) : ℚ⟦X⟧) = C ((1 : ℚ)) + C ((-3 : ℚ)) * X ^ 1 + C ((34 : ℚ)) * X ^ 2 + C ((-63 : ℚ)) * X ^ 3 + C ((26 : ℚ)) * X ^ 4 + C ((8 : ℚ)) * X ^ 5 := by
    (try simp only [map_neg, map_ofNat, map_one, map_div₀, map_natCast]) <;> ring
  have key : G * (((1-X)*(1-2*X)*(1-4*X))) = (1-3*X+34*X ^ 2-63*X ^ 3+26*X ^ 4+8*X ^ 5) := by
    rw [eQ, eP]
    ext n
    simp only [map_add, map_sub, coeff_C_mul, coeff_mul_X_pow', coeff_X_pow, G, coeff_mk, coeff_C]
    rcases Nat.lt_or_ge n 6 with hn | hn
    · interval_cases n <;> norm_num [v0, v1, v2, v3, v4, v5, v6]
    · simp only [show 1 ≤ n by omega, show 2 ≤ n by omega, show 3 ≤ n by omega, show 4 ≤ n by omega, show 5 ≤ n by omega, show n ≠ 0 by omega, show n ≠ 1 by omega, show n ≠ 2 by omega, show n ≠ 3 by omega, show n ≠ 4 by omega, show n ≠ 5 by omega, show n - 1 ≠ 0 by omega, show n - 2 ≠ 0 by omega, show n - 3 ≠ 0 by omega, show n - 4 ≠ 0 by omega, show n - 5 ≠ 0 by omega, if_true, if_false, ↓reduceIte, ne_eq, not_false_eq_true]
      have hr := gfrec2 n hn
      linear_combination ((1 : ℚ)) * hr
  rw [← key, mul_assoc, PowerSeries.mul_inv_cancel _ hden, mul_one]


open PowerSeries in
/-- All the proved formula lines of the entry, together. -/
theorem formulas :
    (∀ n : ℕ, 3 ≤ n → (a n : ℚ) = ((((2 : ℚ) ^ (n + 1)) - (1 : ℚ)) ^ 2)) ∧
    (∀ n : ℕ, 6 ≤ n → (a n : ℤ) = ((((7 : ℤ) * (a (n - 1) : ℤ)) - ((14 : ℤ) * (a (n - 2) : ℤ))) + ((8 : ℤ) * (a (n - 3) : ℤ)))) ∧
    (PowerSeries.mk (fun n => (a n : ℚ)) = ((1-3*X+34*X ^ 2-63*X ^ 3+26*X ^ 4+8*X ^ 5)) * (((1-X)*(1-2*X)*(1-4*X)))⁻¹) :=
  ⟨closed0, recurrence1, gf2⟩


/-- Rule 921 also generates this sequence: Rule 921's count of ON cells at stage `2^n - 1` (in the
square `[-(2^n-1), 2^n-1]²`) equals a(n) for every n. -/
theorem rule921 (n : ℕ) : OeisA273767_R921.aR n = a n := by
  rcases Nat.lt_or_ge n 5 with h | h
  · interval_cases n <;> simp only [v0, v1, v2, v3, v4, OeisA273767_R921.v0, OeisA273767_R921.v1, OeisA273767_R921.v2, OeisA273767_R921.v3, OeisA273767_R921.v4]
  · have h1 := cfn0 n (by omega) (by omega)
    have h2 := OeisA273767_R921.cfn0 n (by omega) (by omega)
    exact_mod_cast h2.trans h1.symm

/-- Rule 929 also generates this sequence: Rule 929's count of ON cells at stage `2^n - 1` (in the
square `[-(2^n-1), 2^n-1]²`) equals a(n) for every n. -/
theorem rule929 (n : ℕ) : OeisA273767_R929.aR n = a n := by
  rcases Nat.lt_or_ge n 5 with h | h
  · interval_cases n <;> simp only [v0, v1, v2, v3, v4, OeisA273767_R929.v0, OeisA273767_R929.v1, OeisA273767_R929.v2, OeisA273767_R929.v3, OeisA273767_R929.v4]
  · have h1 := cfn0 n (by omega) (by omega)
    have h2 := OeisA273767_R929.cfn0 n (by omega) (by omega)
    exact_mod_cast h2.trans h1.symm

/-- Rule 937 also generates this sequence: Rule 937's count of ON cells at stage `2^n - 1` (in the
square `[-(2^n-1), 2^n-1]²`) equals a(n) for every n. -/
theorem rule937 (n : ℕ) : OeisA273767_R937.aR n = a n := by
  rcases Nat.lt_or_ge n 5 with h | h
  · interval_cases n <;> simp only [v0, v1, v2, v3, v4, OeisA273767_R937.v0, OeisA273767_R937.v1, OeisA273767_R937.v2, OeisA273767_R937.v3, OeisA273767_R937.v4]
  · have h1 := cfn0 n (by omega) (by omega)
    have h2 := OeisA273767_R937.cfn0 n (by omega) (by omega)
    exact_mod_cast h2.trans h1.symm

/-- Rule 945 also generates this sequence: Rule 945's count of ON cells at stage `2^n - 1` (in the
square `[-(2^n-1), 2^n-1]²`) equals a(n) for every n. -/
theorem rule945 (n : ℕ) : OeisA273767_R945.aR n = a n := by
  rcases Nat.lt_or_ge n 5 with h | h
  · interval_cases n <;> simp only [v0, v1, v2, v3, v4, OeisA273767_R945.v0, OeisA273767_R945.v1, OeisA273767_R945.v2, OeisA273767_R945.v3, OeisA273767_R945.v4]
  · have h1 := cfn0 n (by omega) (by omega)
    have h2 := OeisA273767_R945.cfn0 n (by omega) (by omega)
    exact_mod_cast h2.trans h1.symm

/-- Rule 953 also generates this sequence: Rule 953's count of ON cells at stage `2^n - 1` (in the
square `[-(2^n-1), 2^n-1]²`) equals a(n) for every n. -/
theorem rule953 (n : ℕ) : OeisA273767_R953.aR n = a n := by
  rcases Nat.lt_or_ge n 5 with h | h
  · interval_cases n <;> simp only [v0, v1, v2, v3, v4, OeisA273767_R953.v0, OeisA273767_R953.v1, OeisA273767_R953.v2, OeisA273767_R953.v3, OeisA273767_R953.v4]
  · have h1 := cfn0 n (by omega) (by omega)
    have h2 := OeisA273767_R953.cfn0 n (by omega) (by omega)
    exact_mod_cast h2.trans h1.symm

/-- Every rule named in the entry's comment generates the sequence. -/
theorem other_rules :
    (∀ n : ℕ, OeisA273767_R921.aR n = a n) ∧
    (∀ n : ℕ, OeisA273767_R929.aR n = a n) ∧
    (∀ n : ℕ, OeisA273767_R937.aR n = a n) ∧
    (∀ n : ℕ, OeisA273767_R945.aR n = a n) ∧
    (∀ n : ℕ, OeisA273767_R953.aR n = a n) :=
  ⟨rule921, rule929, rule937, rule945, rule953⟩


/-! ## The statement's definitions and the bridge -/

open PowerSeries





theorem stateOf_R921 (t : ℕ) : OeisA273767_R921.stateR t = stateOf 921 t := by
  induction t with
  | zero => funext p; rfl
  | succ t ih =>
    funext p
    show OeisA273767_R921.ruleR (OeisA273767_R921.stateR t p)
        ((OeisA273767_R921.nbrsR p).countP (fun q => OeisA273767_R921.stateR t q)) =
      ruleOf 921 (stateOf 921 t p) ((nbrs p).countP (fun q => stateOf 921 t q))
    rw [ih]
    rfl

theorem aOf_R921 (n : ℕ) : OeisA273767_R921.aR n = aOf 921 n := by
  rw [OeisA273767_R921.aR, aOf]
  simp only [stateOf_R921]

theorem stateOf_R929 (t : ℕ) : OeisA273767_R929.stateR t = stateOf 929 t := by
  induction t with
  | zero => funext p; rfl
  | succ t ih =>
    funext p
    show OeisA273767_R929.ruleR (OeisA273767_R929.stateR t p)
        ((OeisA273767_R929.nbrsR p).countP (fun q => OeisA273767_R929.stateR t q)) =
      ruleOf 929 (stateOf 929 t p) ((nbrs p).countP (fun q => stateOf 929 t q))
    rw [ih]
    rfl

theorem aOf_R929 (n : ℕ) : OeisA273767_R929.aR n = aOf 929 n := by
  rw [OeisA273767_R929.aR, aOf]
  simp only [stateOf_R929]

theorem stateOf_R937 (t : ℕ) : OeisA273767_R937.stateR t = stateOf 937 t := by
  induction t with
  | zero => funext p; rfl
  | succ t ih =>
    funext p
    show OeisA273767_R937.ruleR (OeisA273767_R937.stateR t p)
        ((OeisA273767_R937.nbrsR p).countP (fun q => OeisA273767_R937.stateR t q)) =
      ruleOf 937 (stateOf 937 t p) ((nbrs p).countP (fun q => stateOf 937 t q))
    rw [ih]
    rfl

theorem aOf_R937 (n : ℕ) : OeisA273767_R937.aR n = aOf 937 n := by
  rw [OeisA273767_R937.aR, aOf]
  simp only [stateOf_R937]

theorem stateOf_R945 (t : ℕ) : OeisA273767_R945.stateR t = stateOf 945 t := by
  induction t with
  | zero => funext p; rfl
  | succ t ih =>
    funext p
    show OeisA273767_R945.ruleR (OeisA273767_R945.stateR t p)
        ((OeisA273767_R945.nbrsR p).countP (fun q => OeisA273767_R945.stateR t q)) =
      ruleOf 945 (stateOf 945 t p) ((nbrs p).countP (fun q => stateOf 945 t q))
    rw [ih]
    rfl

theorem aOf_R945 (n : ℕ) : OeisA273767_R945.aR n = aOf 945 n := by
  rw [OeisA273767_R945.aR, aOf]
  simp only [stateOf_R945]

theorem stateOf_R953 (t : ℕ) : OeisA273767_R953.stateR t = stateOf 953 t := by
  induction t with
  | zero => funext p; rfl
  | succ t ih =>
    funext p
    show OeisA273767_R953.ruleR (OeisA273767_R953.stateR t p)
        ((OeisA273767_R953.nbrsR p).countP (fun q => OeisA273767_R953.stateR t q)) =
      ruleOf 953 (stateOf 953 t p) ((nbrs p).countP (fun q => stateOf 953 t q))
    rw [ih]
    rfl

theorem aOf_R953 (n : ℕ) : OeisA273767_R953.aR n = aOf 953 n := by
  rw [OeisA273767_R953.aR, aOf]
  simp only [stateOf_R953]

/-- The site's problem, as stated in `main`. -/
theorem conj :
    (∀ n : ℕ, aOf 921 n = a n) ∧
    (∀ n : ℕ, aOf 929 n = a n) ∧
    (∀ n : ℕ, aOf 937 n = a n) ∧
    (∀ n : ℕ, aOf 945 n = a n) ∧
    (∀ n : ℕ, aOf 953 n = a n) ∧
    (∀ n : ℕ, 2 < n → (a n : ℚ) = (2 ^ (n + 1) - 1) ^ 2) ∧
    (∀ n : ℕ, 5 < n → (a n : ℤ) = 7 * a (n - 1) - 14 * a (n - 2) + 8 * a (n - 3)) ∧
    A = (1 - 3 * X + 34 * X ^ 2 - 63 * X ^ 3 + 26 * X ^ 4 + 8 * X ^ 5) *
      ((1 - X) * (1 - 2 * X) * (1 - 4 * X))⁻¹ := by
  rw [show A = PowerSeries.mk (fun n => (a n : ℚ)) from rfl]
  exact ⟨fun n => (aOf_R921 n).symm.trans (rule921 n),
    fun n => (aOf_R929 n).symm.trans (rule929 n),
    fun n => (aOf_R937 n).symm.trans (rule937 n),
    fun n => (aOf_R945 n).symm.trans (rule945 n),
    fun n => (aOf_R953 n).symm.trans (rule953 n),
    fun n hn => (closed0 n (by omega)).trans (by ring),
    fun n hn => (recurrence1 n (by omega)).trans (by ring),
    gf2⟩

end OMA.S_oeis_a273767

theorem OMA.solution : type_of% @OMA.S_oeis_a273767.main :=
  OMA.S_oeis_a273767.conj
