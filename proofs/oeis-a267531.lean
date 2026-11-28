import OMAStatements.S_oeis_a267531

namespace OMA.S_oeis_a267531







/-! ## A finite certificate: rows `0..5` on the window `[-6, 6]` -/

/-- The background (the state of every cell far from the origin). -/
def bg : ℕ → Bool
  | 0 => false
  | t + 1 => rule (bg t) (bg t) (bg t)

lemma light_cone (t : ℕ) : ∀ i : ℤ, ((t : ℤ) < i ∨ (t : ℤ) < -i) → state t i = bg t := by
  induction t with
  | zero => intro i hi; simp only [state, bg, decide_eq_false_iff_not]; omega
  | succ t ih =>
    intro i hi
    push_cast at hi
    show rule (state t (i - 1)) (state t i) (state t (i + 1)) = rule (bg t) (bg t) (bg t)
    rw [ih (i - 1) (by omega), ih i (by omega), ih (i + 1) (by omega)]

def W : ℕ := 6

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

lemma init_ok (s : Bool × ℕ) (h : initOK s = true) : ∀ i, state 0 i = decode s i := by
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

lemma step_ok (t : ℕ) (s s' : Bool × ℕ) (ht : t + 1 ≤ W) (hs : ∀ i, state t i = decode s i)
    (hb : s.1 = bg t) (hok : stepOK s s' = true) : ∀ i, state (t + 1) i = decode s' i := by
  simp only [stepOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at hok
  obtain ⟨hbg, hcells⟩ := hok
  intro i
  by_cases hw : -(W : ℤ) ≤ i ∧ i ≤ W
  · obtain ⟨j, hj, rfl⟩ := in_window i hw
    rw [hcells j hj]
    show rule (state t ((j : ℤ) - W - 1)) (state t ((j : ℤ) - W)) (state t ((j : ℤ) - W + 1)) = _
    rw [hs, hs, hs]
  · rw [light_cone (t + 1) i (by push_cast; omega)]
    unfold decode
    rw [if_neg hw, hbg, hb]
    rfl

/-- The rows `0..5`, computed outside Lean and checked cell by cell below. -/
def stages : List (Bool × ℕ) :=
  [(false, 64),
    (true, 8031),
    (true, 8015),
    (true, 8007),
    (true, 8019),
    (true, 8017)]

lemma stages_ok : initOK (stages.getD 0 default) = true ∧
    ∀ t < 5, stepOK (stages.getD t default) (stages.getD (t + 1) default) = true := by
  decide +kernel

lemma cert_rows (t : ℕ) (ht : t ≤ 5) :
    (stages.getD t default).1 = bg t ∧ ∀ i, state t i = decode (stages.getD t default) i := by
  induction t with
  | zero =>
    have h := stages_ok.1
    refine ⟨?_, init_ok _ h⟩
    simp only [initOK, Bool.and_eq_true, beq_iff_eq] at h
    exact h.1
  | succ t ih =>
    obtain ⟨hb, hs⟩ := ih (by omega)
    have hok := stages_ok.2 t (by omega)
    refine ⟨?_, step_ok t _ _ (by unfold W; omega) hs hb hok⟩
    simp only [stepOK, Bool.and_eq_true, beq_iff_eq] at hok
    rw [hok.1, hb]
    rfl


def sim (t : ℕ) : ℤ → Bool := decode (stages.getD t default)

/-! ## The regime from row 5 on -/

def bgT : List Bool := [true, true]
/-- Bit `j` of the left edge block: cell `-t + j`. -/
def elT : List ℕ := [0, 0]
/-- Bit `j` of the right edge block: cell `t - j`. -/
def erT : List ℕ := [3, 3]
/-- Bit `m` of the center block: cell `m - 1`. -/
def coT : List ℕ := [2, 2]
/-- Bit `s` of the left flank: cells `i` with `(i + t) % 2 = s`. -/
def flLT : List ℕ := [2, 1]
/-- Bit `s` of the right flank: cells `i` with `(t - i) % 2 = s`. -/
def flRT : List ℕ := [3, 3]

def V (t : ℕ) (i : ℤ) : Bool :=
  if i < -(t : ℤ) ∨ (t : ℤ) < i then bgT.getD ((t - 5) % 2) false
  else if i + t ≤ 1 then (elT.getD ((t - 5) % 2) 0).testBit (i + t).toNat
  else if (t : ℤ) - i ≤ 1 then (erT.getD ((t - 5) % 2) 0).testBit ((t : ℤ) - i).toNat
  else if -(1 : ℤ) ≤ i ∧ i ≤ 1 then (coT.getD ((t - 5) % 2) 0).testBit (i + 1).toNat
  else if i < 0 then (flLT.getD ((t - 5) % 2) 0).testBit ((i + t) % 2).toNat
  else (flRT.getD ((t - 5) % 2) 0).testBit (((t : ℤ) - i) % 2).toNat

lemma V_out (t : ℕ) (i : ℤ) (h : i < -(t : ℤ) ∨ (t : ℤ) < i) :
    V t i = bgT.getD ((t - 5) % 2) false := by
  unfold V; rw [if_pos h]

lemma V_el (t : ℕ) (ht : 5 ≤ t) (i : ℤ) (j : ℕ) (hj : i + t = j) (hjA : j ≤ 1) :
    V t i = (elT.getD ((t - 5) % 2) 0).testBit j := by
  unfold V
  rw [if_neg (by omega), if_pos (by omega)]
  congr 1
  omega

lemma V_er (t : ℕ) (ht : 5 ≤ t) (i : ℤ) (j : ℕ) (hj : (t : ℤ) - i = j) (hjA : j ≤ 1) :
    V t i = (erT.getD ((t - 5) % 2) 0).testBit j := by
  unfold V
  rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)]
  congr 1
  omega

lemma V_co (t : ℕ) (ht : 5 ≤ t) (i : ℤ) (m : ℕ) (hm : i + 1 = m) (hmK : m ≤ 2 * 1) :
    V t i = (coT.getD ((t - 5) % 2) 0).testBit m := by
  unfold V
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]
  congr 1
  omega

lemma V_fll (t : ℕ) (ht : 5 ≤ t) (i : ℤ) (s : ℕ) (hs : (i + t) % 2 = s)
    (h1 : (1 : ℤ) < i + t) (h3 : i < -(1 : ℤ)) :
    V t i = (flLT.getD ((t - 5) % 2) 0).testBit s := by
  unfold V
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]
  congr 1
  omega

lemma V_flr (t : ℕ) (ht : 5 ≤ t) (i : ℤ) (s : ℕ) (hs : ((t : ℤ) - i) % 2 = s)
    (h2 : (1 : ℤ) < (t : ℤ) - i) (h3 : (1 : ℤ) < i) :
    V t i = (flRT.getD ((t - 5) % 2) 0).testBit s := by
  unfold V
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  congr 1
  omega


set_option maxHeartbeats 8000000 in
lemma stepV (t : ℕ) (ht : 5 ≤ t) (i : ℤ) :
    rule (V t (i - 1)) (V t i) (V t (i + 1)) = V (t + 1) i := by
  obtain ⟨q, hq, hqq⟩ : ∃ q, q < 2 ∧ (t - 5) % 2 = q := ⟨_, Nat.mod_lt _ (by norm_num), rfl⟩
  have hq1 : (t + 1 - 5) % 2 = (q + 1) % 2 := by omega
  interval_cases q
  · rcases (by omega : (i ≤ -(t : ℤ) - 3) ∨ (i = -(t : ℤ) - 2) ∨ (i + t + 1 = 0) ∨ (i + t + 1 = 1) ∨ (i + t + 1 = 2) ∨ (i + t + 1 = 3) ∨ (3 < i + t + 1 ∧ i < -1 - 1 ∧ (i + t + 1) % 2 = 0) ∨ (3 < i + t + 1 ∧ i < -1 - 1 ∧ (i + t + 1) % 2 = 1) ∨ (i = -2) ∨ (i = -1) ∨ (i = 0) ∨ (i = 1) ∨ (i = 2) ∨ (1 + 1 < i ∧ 3 < (t : ℤ) + 1 - i ∧ ((t : ℤ) + 1 - i) % 2 = 0) ∨ (1 + 1 < i ∧ 3 < (t : ℤ) + 1 - i ∧ ((t : ℤ) + 1 - i) % 2 = 1) ∨ ((t : ℤ) + 1 - i = 3) ∨ ((t : ℤ) + 1 - i = 2) ∨ ((t : ℤ) + 1 - i = 1) ∨ ((t : ℤ) + 1 - i = 0) ∨ (i = (t : ℤ) + 2) ∨ ((t : ℤ) + 3 ≤ i)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · rw [V_out t (i - 1) (by push_cast; omega), V_out t i (by push_cast; omega), V_out t (i + 1) (by push_cast; omega), V_out (t + 1) i (by push_cast; omega), hqq, hq1]
      decide
    · rw [V_out t (i - 1) (by push_cast; omega), V_out t i (by push_cast; omega), V_out t (i + 1) (by push_cast; omega), V_out (t + 1) i (by push_cast; omega), hqq, hq1]
      decide
    · rw [V_out t (i - 1) (by push_cast; omega), V_out t i (by push_cast; omega), V_el t ht (i + 1) 0 (by omega) (by norm_num), V_el (t + 1) (by omega) i 0 (by push_cast; omega) (by norm_num), hqq, hq1]
      decide
    · rw [V_out t (i - 1) (by push_cast; omega), V_el t ht i 0 (by omega) (by norm_num), V_el t ht (i + 1) 1 (by omega) (by norm_num), V_el (t + 1) (by omega) i 1 (by push_cast; omega) (by norm_num), hqq, hq1]
      decide
    · rw [V_el t ht (i - 1) 0 (by omega) (by norm_num), V_el t ht i 1 (by omega) (by norm_num), V_fll t ht (i + 1) 0 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 0 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
      decide
    · rw [V_el t ht (i - 1) 1 (by omega) (by norm_num), V_fll t ht i 0 (by omega) (by omega) (by omega), V_fll t ht (i + 1) 1 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 1 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
      decide
    · rw [V_fll t ht (i - 1) 0 (by omega) (by omega) (by omega), V_fll t ht i 1 (by omega) (by omega) (by omega), V_fll t ht (i + 1) 0 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 0 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
      decide
    · rw [V_fll t ht (i - 1) 1 (by omega) (by omega) (by omega), V_fll t ht i 0 (by omega) (by omega) (by omega), V_fll t ht (i + 1) 1 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 1 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
      decide
    · rw [V_fll t ht (i - 1) 0 (by omega) (by omega) (by omega), V_fll t ht i 1 (by omega) (by omega) (by omega), V_co t ht (i + 1) 0 (by omega) (by norm_num), V_fll (t + 1) (by omega) i 0 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
      decide
    · rw [V_fll t ht (i - 1) 1 (by omega) (by omega) (by omega), V_co t ht i 0 (by omega) (by norm_num), V_co t ht (i + 1) 1 (by omega) (by norm_num), V_co (t + 1) (by omega) i 0 (by omega) (by norm_num), hqq, hq1]
      decide
    · rw [V_co t ht (i - 1) 0 (by omega) (by norm_num), V_co t ht i 1 (by omega) (by norm_num), V_co t ht (i + 1) 2 (by omega) (by norm_num), V_co (t + 1) (by omega) i 1 (by omega) (by norm_num), hqq, hq1]
      decide
    · rw [V_co t ht (i - 1) 1 (by omega) (by norm_num), V_co t ht i 2 (by omega) (by norm_num), V_flr t ht (i + 1) 1 (by omega) (by omega) (by omega), V_co (t + 1) (by omega) i 2 (by omega) (by norm_num), hqq, hq1]
      decide
    · rw [V_co t ht (i - 1) 2 (by omega) (by norm_num), V_flr t ht i 1 (by omega) (by omega) (by omega), V_flr t ht (i + 1) 0 (by omega) (by omega) (by omega), V_flr (t + 1) (by omega) i 0 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
      decide
    · rw [V_flr t ht (i - 1) 0 (by omega) (by omega) (by omega), V_flr t ht i 1 (by omega) (by omega) (by omega), V_flr t ht (i + 1) 0 (by omega) (by omega) (by omega), V_flr (t + 1) (by omega) i 0 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
      decide
    · rw [V_flr t ht (i - 1) 1 (by omega) (by omega) (by omega), V_flr t ht i 0 (by omega) (by omega) (by omega), V_flr t ht (i + 1) 1 (by omega) (by omega) (by omega), V_flr (t + 1) (by omega) i 1 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
      decide
    · rw [V_flr t ht (i - 1) 1 (by omega) (by omega) (by omega), V_flr t ht i 0 (by omega) (by omega) (by omega), V_er t ht (i + 1) 1 (by omega) (by norm_num), V_flr (t + 1) (by omega) i 1 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
      decide
    · rw [V_flr t ht (i - 1) 0 (by omega) (by omega) (by omega), V_er t ht i 1 (by omega) (by norm_num), V_er t ht (i + 1) 0 (by omega) (by norm_num), V_flr (t + 1) (by omega) i 0 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
      decide
    · rw [V_er t ht (i - 1) 1 (by omega) (by norm_num), V_er t ht i 0 (by omega) (by norm_num), V_out t (i + 1) (by push_cast; omega), V_er (t + 1) (by omega) i 1 (by push_cast; omega) (by norm_num), hqq, hq1]
      decide
    · rw [V_er t ht (i - 1) 0 (by omega) (by norm_num), V_out t i (by push_cast; omega), V_out t (i + 1) (by push_cast; omega), V_er (t + 1) (by omega) i 0 (by push_cast; omega) (by norm_num), hqq, hq1]
      decide
    · rw [V_out t (i - 1) (by push_cast; omega), V_out t i (by push_cast; omega), V_out t (i + 1) (by push_cast; omega), V_out (t + 1) i (by push_cast; omega), hqq, hq1]
      decide
    · rw [V_out t (i - 1) (by push_cast; omega), V_out t i (by push_cast; omega), V_out t (i + 1) (by push_cast; omega), V_out (t + 1) i (by push_cast; omega), hqq, hq1]
      decide
  · rcases (by omega : (i ≤ -(t : ℤ) - 3) ∨ (i = -(t : ℤ) - 2) ∨ (i + t + 1 = 0) ∨ (i + t + 1 = 1) ∨ (i + t + 1 = 2) ∨ (i + t + 1 = 3) ∨ (3 < i + t + 1 ∧ i < -1 - 1 ∧ (i + t + 1) % 2 = 0) ∨ (3 < i + t + 1 ∧ i < -1 - 1 ∧ (i + t + 1) % 2 = 1) ∨ (i = -2) ∨ (i = -1) ∨ (i = 0) ∨ (i = 1) ∨ (i = 2) ∨ (1 + 1 < i ∧ 3 < (t : ℤ) + 1 - i ∧ ((t : ℤ) + 1 - i) % 2 = 0) ∨ (1 + 1 < i ∧ 3 < (t : ℤ) + 1 - i ∧ ((t : ℤ) + 1 - i) % 2 = 1) ∨ ((t : ℤ) + 1 - i = 3) ∨ ((t : ℤ) + 1 - i = 2) ∨ ((t : ℤ) + 1 - i = 1) ∨ ((t : ℤ) + 1 - i = 0) ∨ (i = (t : ℤ) + 2) ∨ ((t : ℤ) + 3 ≤ i)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · rw [V_out t (i - 1) (by push_cast; omega), V_out t i (by push_cast; omega), V_out t (i + 1) (by push_cast; omega), V_out (t + 1) i (by push_cast; omega), hqq, hq1]
      decide
    · rw [V_out t (i - 1) (by push_cast; omega), V_out t i (by push_cast; omega), V_out t (i + 1) (by push_cast; omega), V_out (t + 1) i (by push_cast; omega), hqq, hq1]
      decide
    · rw [V_out t (i - 1) (by push_cast; omega), V_out t i (by push_cast; omega), V_el t ht (i + 1) 0 (by omega) (by norm_num), V_el (t + 1) (by omega) i 0 (by push_cast; omega) (by norm_num), hqq, hq1]
      decide
    · rw [V_out t (i - 1) (by push_cast; omega), V_el t ht i 0 (by omega) (by norm_num), V_el t ht (i + 1) 1 (by omega) (by norm_num), V_el (t + 1) (by omega) i 1 (by push_cast; omega) (by norm_num), hqq, hq1]
      decide
    · rw [V_el t ht (i - 1) 0 (by omega) (by norm_num), V_el t ht i 1 (by omega) (by norm_num), V_fll t ht (i + 1) 0 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 0 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
      decide
    · rw [V_el t ht (i - 1) 1 (by omega) (by norm_num), V_fll t ht i 0 (by omega) (by omega) (by omega), V_fll t ht (i + 1) 1 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 1 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
      decide
    · rw [V_fll t ht (i - 1) 0 (by omega) (by omega) (by omega), V_fll t ht i 1 (by omega) (by omega) (by omega), V_fll t ht (i + 1) 0 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 0 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
      decide
    · rw [V_fll t ht (i - 1) 1 (by omega) (by omega) (by omega), V_fll t ht i 0 (by omega) (by omega) (by omega), V_fll t ht (i + 1) 1 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 1 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
      decide
    · rw [V_fll t ht (i - 1) 1 (by omega) (by omega) (by omega), V_fll t ht i 0 (by omega) (by omega) (by omega), V_co t ht (i + 1) 0 (by omega) (by norm_num), V_fll (t + 1) (by omega) i 1 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
      decide
    · rw [V_fll t ht (i - 1) 0 (by omega) (by omega) (by omega), V_co t ht i 0 (by omega) (by norm_num), V_co t ht (i + 1) 1 (by omega) (by norm_num), V_co (t + 1) (by omega) i 0 (by omega) (by norm_num), hqq, hq1]
      decide
    · rw [V_co t ht (i - 1) 0 (by omega) (by norm_num), V_co t ht i 1 (by omega) (by norm_num), V_co t ht (i + 1) 2 (by omega) (by norm_num), V_co (t + 1) (by omega) i 1 (by omega) (by norm_num), hqq, hq1]
      decide
    · rw [V_co t ht (i - 1) 1 (by omega) (by norm_num), V_co t ht i 2 (by omega) (by norm_num), V_flr t ht (i + 1) 0 (by omega) (by omega) (by omega), V_co (t + 1) (by omega) i 2 (by omega) (by norm_num), hqq, hq1]
      decide
    · rw [V_co t ht (i - 1) 2 (by omega) (by norm_num), V_flr t ht i 0 (by omega) (by omega) (by omega), V_flr t ht (i + 1) 1 (by omega) (by omega) (by omega), V_flr (t + 1) (by omega) i 1 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
      decide
    · rw [V_flr t ht (i - 1) 0 (by omega) (by omega) (by omega), V_flr t ht i 1 (by omega) (by omega) (by omega), V_flr t ht (i + 1) 0 (by omega) (by omega) (by omega), V_flr (t + 1) (by omega) i 0 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
      decide
    · rw [V_flr t ht (i - 1) 1 (by omega) (by omega) (by omega), V_flr t ht i 0 (by omega) (by omega) (by omega), V_flr t ht (i + 1) 1 (by omega) (by omega) (by omega), V_flr (t + 1) (by omega) i 1 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
      decide
    · rw [V_flr t ht (i - 1) 1 (by omega) (by omega) (by omega), V_flr t ht i 0 (by omega) (by omega) (by omega), V_er t ht (i + 1) 1 (by omega) (by norm_num), V_flr (t + 1) (by omega) i 1 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
      decide
    · rw [V_flr t ht (i - 1) 0 (by omega) (by omega) (by omega), V_er t ht i 1 (by omega) (by norm_num), V_er t ht (i + 1) 0 (by omega) (by norm_num), V_flr (t + 1) (by omega) i 0 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
      decide
    · rw [V_er t ht (i - 1) 1 (by omega) (by norm_num), V_er t ht i 0 (by omega) (by norm_num), V_out t (i + 1) (by push_cast; omega), V_er (t + 1) (by omega) i 1 (by push_cast; omega) (by norm_num), hqq, hq1]
      decide
    · rw [V_er t ht (i - 1) 0 (by omega) (by norm_num), V_out t i (by push_cast; omega), V_out t (i + 1) (by push_cast; omega), V_er (t + 1) (by omega) i 0 (by push_cast; omega) (by norm_num), hqq, hq1]
      decide
    · rw [V_out t (i - 1) (by push_cast; omega), V_out t i (by push_cast; omega), V_out t (i + 1) (by push_cast; omega), V_out (t + 1) i (by push_cast; omega), hqq, hq1]
      decide
    · rw [V_out t (i - 1) (by push_cast; omega), V_out t i (by push_cast; omega), V_out t (i + 1) (by push_cast; omega), V_out (t + 1) i (by push_cast; omega), hqq, hq1]
      decide

lemma base_ok : (∀ j < 2 * W + 1, decode (stages.getD 5 default) ((j : ℤ) - W) = V 5 ((j : ℤ) - W)) ∧
    (stages.getD 5 default).1 = bgT.getD 0 false := by
  decide +kernel

lemma pattern (t : ℕ) (ht : 5 ≤ t) : ∀ i, state t i = V t i := by
  induction t, ht using Nat.le_induction with
  | base =>
    intro i
    rw [(cert_rows 5 le_rfl).2 i]
    by_cases hw : -(W : ℤ) ≤ i ∧ i ≤ W
    · obtain ⟨j, hj, rfl⟩ := in_window i hw
      exact base_ok.1 j hj
    · unfold decode
      rw [if_neg hw, base_ok.2, V_out 5 i (by unfold W at hw; omega)]
  | succ t ht ih =>
    intro i
    show rule (state t (i - 1)) (state t i) (state t (i + 1)) = _
    rw [ih, ih, ih, stepV t ht i]

lemma sim_V (t : ℕ) (ht : t ≤ 5) : sim t = state t := funext fun i => ((cert_rows t ht).2 i).symm

lemma state_eq_V (t : ℕ) (ht : 5 ≤ t) : state t = V t := funext (pattern t ht)

def rowOf (t : ℕ) : ℤ → Bool := if t ≤ 5 then sim t else V t

lemma state_eq (t : ℕ) : state t = rowOf t := by
  unfold rowOf
  split_ifs with h
  · exact (sim_V t h).symm
  · exact state_eq_V t (by omega)

/-- The number of OFF cells among `-n..n` in row `n`. -/
def cnt1 (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (2 * n + 1), if state n ((k : ℤ) - n) then 0 else 1

lemma alt_even (f : ℕ → ℕ) (c m : ℕ) :
    ∑ k ∈ Finset.range (2 * m), f ((c + k) % 2) = m * (f (c % 2) + f ((c + 1) % 2)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ, ih,
      show (c + (2 * m + 1)) % 2 = (c + 1) % 2 by omega, show (c + 2 * m) % 2 = c % 2 by omega]
    ring

lemma alt_odd (f : ℕ → ℕ) (c m : ℕ) :
    ∑ k ∈ Finset.range (2 * m + 1), f ((c + k) % 2) = m * (f (c % 2) + f ((c + 1) % 2)) + f (c % 2) := by
  rw [Finset.sum_range_succ, alt_even, show (c + 2 * m) % 2 = c % 2 by omega]

set_option maxHeartbeats 4000000 in
lemma cnt_split (n : ℕ) (hn : 5 ≤ n) :
    cnt1 n = (∑ k ∈ Finset.range 2, (if (elT.getD ((n - 5) % 2) 0).testBit k then 0 else 1)) +
      (∑ k ∈ Finset.range (n - 3), (if (flLT.getD ((n - 5) % 2) 0).testBit ((2 + k) % 2) then 0 else 1)) +
      (∑ k ∈ Finset.range 3, (if (coT.getD ((n - 5) % 2) 0).testBit k then 0 else 1)) +
      (∑ k ∈ Finset.range (n - 3), (if (flRT.getD ((n - 5) % 2) 0).testBit ((2 + k) % 2) then 0 else 1)) +
      (∑ k ∈ Finset.range 2, (if (erT.getD ((n - 5) % 2) 0).testBit (1 - k) then 0 else 1)) := by
  unfold cnt1
  rw [state_eq_V n hn]
  rw [show 2 * n + 1 = 2 + (n - 3) + 3 + (n - 3) + 2 by omega]
  rw [Finset.sum_range_add, Finset.sum_range_add, Finset.sum_range_add, Finset.sum_range_add]
  congr 1
  congr 1
  congr 1
  congr 1
  · refine Finset.sum_congr rfl fun k hk => ?_
    have hk' := Finset.mem_range.mp hk
    rw [V_el n hn _ k (by omega) (by omega)]
  · refine Finset.sum_congr rfl fun k hk => ?_
    have hk' := Finset.mem_range.mp hk
    rw [V_fll n hn _ ((2 + k) % 2) (by push_cast; omega) (by push_cast; omega) (by push_cast; omega)]
  · refine Finset.sum_congr rfl fun k hk => ?_
    have hk' := Finset.mem_range.mp hk
    rw [V_co n hn _ k (by push_cast; omega) (by omega)]
  · rw [← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' := Finset.mem_range.mp hk
    rw [V_flr n hn _ ((2 + k) % 2) (by push_cast; omega) (by push_cast; omega) (by push_cast; omega)]
  · refine Finset.sum_congr rfl fun k hk => ?_
    have hk' := Finset.mem_range.mp hk
    rw [V_er n hn _ (1 - k) (by push_cast; omega) (by omega)]


lemma cntn0 (n : ℕ) (h1 : 5 ≤ n) (h2 : n % 2 = 0) :
    (cnt1 n : ℚ) = ((1 : ℚ) / 2) * (n : ℚ) + (2 : ℚ) := by
  rw [cnt_split n h1, show (n - 5) % 2 = 1 by omega]
  have e1 : (∑ k ∈ Finset.range 2, (if (elT.getD 1 0).testBit k then 0 else 1)) = 2 := by decide
  have e3 : (∑ k ∈ Finset.range 3, (if (coT.getD 1 0).testBit k then 0 else 1)) = 2 := by decide
  have e5 : (∑ k ∈ Finset.range 2, (if (erT.getD 1 0).testBit (1 - k) then 0 else 1)) = 0 := by decide
  rw [e1, e3, e5]
  obtain ⟨m, rfl⟩ : ∃ m, n = 3 + (2 * m + 1) := ⟨(n - 3) / 2, by omega⟩
  rw [show 3 + (2 * m + 1) - 3 = 2 * m + 1 by omega]
  have hl := alt_odd (fun s => if (flLT.getD 1 0).testBit s then 0 else 1) 2 m
  have hr := alt_odd (fun s => if (flRT.getD 1 0).testBit s then 0 else 1) 2 m
  try simp only at hl hr
  rw [hl, hr]
  have g1 : (if (flLT.getD 1 0).testBit (2 % 2) then 0 else 1 : ℕ) = 0 := by decide
  have g2 : (if (flLT.getD 1 0).testBit ((2 + 1) % 2) then 0 else 1 : ℕ) = 1 := by decide
  have g3 : (if (flRT.getD 1 0).testBit (2 % 2) then 0 else 1 : ℕ) = 0 := by decide
  have g4 : (if (flRT.getD 1 0).testBit ((2 + 1) % 2) then 0 else 1 : ℕ) = 0 := by decide
  rw [g1, g2, g3, g4]
  push_cast
  ring


lemma cntn1 (n : ℕ) (h1 : 5 ≤ n) (h2 : n % 2 = 1) :
    (cnt1 n : ℚ) = ((1 : ℚ) / 2) * (n : ℚ) + ((5 : ℚ) / 2) := by
  rw [cnt_split n h1, show (n - 5) % 2 = 0 by omega]
  have e1 : (∑ k ∈ Finset.range 2, (if (elT.getD 0 0).testBit k then 0 else 1)) = 2 := by decide
  have e3 : (∑ k ∈ Finset.range 3, (if (coT.getD 0 0).testBit k then 0 else 1)) = 2 := by decide
  have e5 : (∑ k ∈ Finset.range 2, (if (erT.getD 0 0).testBit (1 - k) then 0 else 1)) = 0 := by decide
  rw [e1, e3, e5]
  obtain ⟨m, rfl⟩ : ∃ m, n = 3 + (2 * m) := ⟨(n - 3) / 2, by omega⟩
  rw [show 3 + (2 * m) - 3 = 2 * m by omega]
  have hl := alt_even (fun s => if (flLT.getD 0 0).testBit s then 0 else 1) 2 m
  have hr := alt_even (fun s => if (flRT.getD 0 0).testBit s then 0 else 1) 2 m
  try simp only at hl hr
  rw [hl, hr]
  have g1 : (if (flLT.getD 0 0).testBit (2 % 2) then 0 else 1 : ℕ) = 1 := by decide
  have g2 : (if (flLT.getD 0 0).testBit ((2 + 1) % 2) then 0 else 1 : ℕ) = 0 := by decide
  have g3 : (if (flRT.getD 0 0).testBit (2 % 2) then 0 else 1 : ℕ) = 0 := by decide
  have g4 : (if (flRT.getD 0 0).testBit ((2 + 1) % 2) then 0 else 1 : ℕ) = 0 := by decide
  rw [g1, g2, g3, g4]
  push_cast
  ring



/-- The row counts read off the certified rows (`rowOf`). -/
def cSim (n : ℕ) : ℕ := ∑ k ∈ Finset.range (2 * n + 1), if rowOf n ((k : ℤ) - n) then 0 else 1

lemma cnt1_eq_sim (n : ℕ) : cnt1 n = cSim n := by
  unfold cnt1 cSim
  simp only [state_eq]

lemma cvals : ∀ n ≤ 5, cnt1 n = ([0, 2, 3, 4, 4, 5] : List ℕ).getD n 0 := by
  intro n hn
  rw [cnt1_eq_sim n]
  revert n
  decide +kernel

/-- The OFF count of row t is floor((t + 5)/2) for t >= 2. -/
lemma off_eq (t : ℕ) (ht : 2 ≤ t) : cnt1 t = (t + 5) / 2 := by
  rcases Nat.lt_or_ge t 5 with h | h
  · interval_cases t
    · rw [cvals 2 (by norm_num)]; decide
    · rw [cvals 3 (by norm_num)]; decide
    · rw [cvals 4 (by norm_num)]; decide
  · rcases Nat.even_or_odd t with ⟨s, hs⟩ | ⟨s, hs⟩
    · have hq := cntn0 t h (by omega)
      have : (cnt1 t : ℚ) = (((t + 5) / 2 : ℕ) : ℚ) := by
        rw [hq, show (t + 5) / 2 = s + 2 by omega, hs]; push_cast; ring
      exact_mod_cast this
    · have hq := cntn1 t h (by omega)
      have : (cnt1 t : ℚ) = (((t + 5) / 2 : ℕ) : ℚ) := by
        rw [hq, show (t + 5) / 2 = s + 3 by omega, hs]; push_cast; ring
      exact_mod_cast this

lemma a_zero : a 0 = cnt1 0 := by
  unfold a cnt1
  rw [Finset.sum_range_one]

lemma a_succ (n : ℕ) : a (n + 1) = a n + cnt1 (n + 1) := by
  unfold a cnt1
  rw [Finset.sum_range_succ]

/-- Stauduhar's conjecture: a(n) = a(n-1) + A004526(n+5) for n > 1, A004526(m) = floor(m/2). -/
theorem stauduhar (n : ℕ) (hn : 1 < n) : a n = a (n - 1) + (n + 5) / 2 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [a_succ, off_eq (m + 1) (by omega), show m + 1 - 1 = m by omega]

/-- Barker's recurrence, for n > 4. -/
theorem recurrence (n : ℕ) (hn : 4 < n) :
    (a n : ℤ) = 2 * a (n - 1) - 2 * a (n - 3) + a (n - 4) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
  have h5 := stauduhar (m + 5) (by omega)
  have h4 := stauduhar (m + 4) (by omega)
  have h3 := stauduhar (m + 3) (by omega)
  have h2 := stauduhar (m + 2) (by omega)
  rw [show m + 5 - 1 = m + 4 by omega] at h5
  rw [show m + 4 - 1 = m + 3 by omega] at h4
  rw [show m + 3 - 1 = m + 2 by omega] at h3
  rw [show m + 2 - 1 = m + 1 by omega] at h2
  rw [show m + 5 - 1 = m + 4 by omega, show m + 5 - 3 = m + 2 by omega,
    show m + 5 - 4 = m + 1 by omega]
  omega

lemma values : a 0 = 0 ∧ a 1 = 2 ∧ a 2 = 5 ∧ a 3 = 9 ∧ a 4 = 13 := by
  have h0 : a 0 = 0 := by rw [a_zero, cvals 0 (by norm_num)]; rfl
  have h1 : a 1 = 2 := by rw [a_succ, h0, cvals 1 (by norm_num)]; rfl
  have h2 : a 2 = 5 := by rw [stauduhar 2 (by norm_num), h1]
  have h3 : a 3 = 9 := by rw [stauduhar 3 (by norm_num), h2]
  have h4 : a 4 = 13 := by rw [stauduhar 4 (by norm_num), h3]
  exact ⟨h0, h1, h2, h3, h4⟩

open PowerSeries in
/-- Barker's g.f., as an identity in Q[[x]]. -/
theorem gf : PowerSeries.mk (fun n => (a n : ℚ)) =
    X * (2 + X - X ^ 2 - X ^ 3) * ((1 - X) ^ 3 * (1 + X))⁻¹ := by
  set A : ℚ⟦X⟧ := PowerSeries.mk (fun n => (a n : ℚ)) with hA
  have hden : constantCoeff ((1 - X) ^ 3 * (1 + X) : ℚ⟦X⟧) ≠ 0 := by simp
  have key : A * ((1 - X) ^ 3 * (1 + X)) = X * (2 + X - X ^ 2 - X ^ 3) := by
    have e1 : A * ((1 - X) ^ 3 * (1 + X)) =
        A - C 2 * (A * X ^ 1) + C 2 * (A * X ^ 3) - A * X ^ 4 := by
      simp only [map_ofNat]; ring
    have e2 : (X * (2 + X - X ^ 2 - X ^ 3) : ℚ⟦X⟧) = X ^ 1 * C 2 + X ^ 2 - X ^ 3 - X ^ 4 := by
      simp only [map_ofNat]; ring
    rw [e1, e2]
    ext n
    simp only [map_sub, map_add, coeff_C_mul, coeff_mul_C, coeff_mul_X_pow', coeff_X_pow, hA,
      coeff_mk]
    obtain ⟨v0, v1, v2, v3, v4⟩ := values
    rcases Nat.lt_or_ge n 5 with hn | hn
    · interval_cases n <;> simp [v0, v1, v2, v3, v4] <;> norm_num
    · rw [if_pos (by omega), if_pos (by omega), if_pos (by omega)]
      simp only [show n ≠ 1 by omega, show n ≠ 2 by omega, show n ≠ 3 by omega,
        show n ≠ 4 by omega, if_false]
      have hr := recurrence n (by omega)
      have : (a n : ℚ) = 2 * a (n - 1) - 2 * a (n - 3) + a (n - 4) := by exact_mod_cast hr
      rw [this]; ring
  rw [← key, mul_assoc, PowerSeries.mul_inv_cancel _ hden, mul_one]

/-- The closed form on odd indices: a(2k + 1) = k^2 + 6k + 2. -/
lemma cf_odd (k : ℕ) : a (2 * k + 1) = k ^ 2 + 6 * k + 2 := by
  induction k with
  | zero => exact values.2.1
  | succ k ih =>
    have e1 := stauduhar (2 * k + 3) (by omega)
    have e2 := stauduhar (2 * k + 2) (by omega)
    rw [show 2 * k + 3 - 1 = 2 * k + 2 by omega] at e1
    rw [show 2 * k + 2 - 1 = 2 * k + 1 by omega, ih] at e2
    rw [show 2 * (k + 1) + 1 = 2 * k + 3 by ring, e1, e2,
      show (2 * k + 3 + 5) / 2 = k + 4 by omega, show (2 * k + 2 + 5) / 2 = k + 3 by omega]
    ring

/-- The closed form on even indices: a(2k + 2) = k^2 + 7k + 5. -/
lemma cf_even (k : ℕ) : a (2 * k + 2) = k ^ 2 + 7 * k + 5 := by
  have e := stauduhar (2 * k + 2) (by omega)
  rw [show 2 * k + 2 - 1 = 2 * k + 1 by omega, cf_odd k,
    show (2 * k + 2 + 5) / 2 = k + 3 by omega] at e
  rw [e]
  ring

/-- Controls: the entry's data a(0..21). -/
theorem controls : a 0 = 0 ∧ a 1 = 2 ∧ a 2 = 5 ∧ a 3 = 9 ∧ a 4 = 13 ∧ a 5 = 18 ∧ a 6 = 23 ∧
    a 7 = 29 ∧ a 8 = 35 ∧ a 9 = 42 ∧ a 10 = 49 ∧ a 11 = 57 ∧ a 12 = 65 ∧ a 13 = 74 ∧
    a 14 = 83 ∧ a 15 = 93 ∧ a 16 = 103 ∧ a 17 = 114 ∧ a 18 = 125 ∧ a 19 = 137 ∧ a 20 = 149 ∧
    a 21 = 162 := by
  have o : ∀ k v, k ^ 2 + 6 * k + 2 = v → a (2 * k + 1) = v := fun k v h => (cf_odd k).trans h
  have e : ∀ k v, k ^ 2 + 7 * k + 5 = v → a (2 * k + 2) = v := fun k v h => (cf_even k).trans h
  exact ⟨values.1, o 0 2 rfl, e 0 5 rfl, o 1 9 rfl, e 1 13 rfl, o 2 18 rfl, e 2 23 rfl,
    o 3 29 rfl, e 3 35 rfl, o 4 42 rfl, e 4 49 rfl, o 5 57 rfl, e 5 65 rfl, o 6 74 rfl,
    e 6 83 rfl, o 7 93 rfl, e 7 103 rfl, o 8 114 rfl, e 8 125 rfl, o 9 137 rfl, e 9 149 rfl,
    o 10 162 rfl⟩

open PowerSeries in
/-- Barker's two conjectures and Stauduhar's. -/
theorem conjecture :
    (∀ n : ℕ, 4 < n → (a n : ℤ) = 2 * a (n - 1) - 2 * a (n - 3) + a (n - 4)) ∧
    PowerSeries.mk (fun n => (a n : ℚ)) =
      X * (2 + X - X ^ 2 - X ^ 3) * ((1 - X) ^ 3 * (1 + X))⁻¹ ∧
    (∀ n : ℕ, 1 < n → a n = a (n - 1) + (n + 5) / 2) :=
  ⟨recurrence, gf, stauduhar⟩

end OMA.S_oeis_a267531

theorem OMA.solution : type_of% @OMA.S_oeis_a267531.main :=
  OMA.S_oeis_a267531.conjecture
