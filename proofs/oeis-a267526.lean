import OMAStatements.S_oeis_a267526

namespace OMA.S_oeis_a267526


/-- Rule 141 as a local map: the new state of a cell from (left, center, right). -/
def rule (l c r : Bool) : Bool := (141 : ℕ).testBit ((cond l 4 0) + (cond c 2 0) + (cond r 1 0))

/-- The configuration at time `t`, started from the single ON cell at 0. -/
def cstate : ℕ → ℤ → Bool
  | 0, i => decide (i = 0)
  | t + 1, i => rule (cstate t (i - 1)) (cstate t i) (cstate t (i + 1))


/-- A267526(n): row `n`, cells `-n..n` (leftmost first), as binary digits read in base 10. -/
def ca (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (2 * n + 1), if cstate n ((k : ℤ) - n) then 10 ^ (2 * n - k) else 0


/-! ## A finite certificate: rows `0..5` on the window `[-6, 6]` -/

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

lemma certified (t : ℕ) (ht : t ≤ 5) :
    (stages.getD t default).1 = bg t ∧ ∀ i, cstate t i = decode (stages.getD t default) i := by
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

lemma pattern (t : ℕ) (ht : 5 ≤ t) : ∀ i, cstate t i = V t i := by
  induction t, ht using Nat.le_induction with
  | base =>
    intro i
    rw [(certified 5 le_rfl).2 i]
    by_cases hw : -(W : ℤ) ≤ i ∧ i ≤ W
    · obtain ⟨j, hj, rfl⟩ := in_window i hw
      exact base_ok.1 j hj
    · unfold decode
      rw [if_neg hw, base_ok.2, V_out 5 i (by unfold W at hw; omega)]
  | succ t ht ih =>
    intro i
    show rule (cstate t (i - 1)) (cstate t i) (cstate t (i + 1)) = _
    rw [ih, ih, ih, stepV t ht i]

lemma sim_V (t : ℕ) (ht : t ≤ 5) : sim t = cstate t := funext fun i => ((certified t ht).2 i).symm

lemma state_eq_V (t : ℕ) (ht : 5 ≤ t) : cstate t = V t := funext (pattern t ht)

def rowOf (t : ℕ) : ℤ → Bool := if t ≤ 5 then sim t else V t

lemma state_eq (t : ℕ) : cstate t = rowOf t := by
  unfold rowOf
  split_ifs with h
  · exact (sim_V t h).symm
  · exact state_eq_V t (by omega)

def aSim (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (2 * n + 1), if rowOf n ((k : ℤ) - n) then 10 ^ (2 * n - k) else 0

lemma a_eq (n : ℕ) : ca n = aSim n := by
  unfold ca aSim
  simp only [state_eq]

/-- The values a(0..20); the listed terms are among them (control). -/
lemma vals : ∀ n ≤ 20, ca n = ([1, 10, 101, 1011, 1010111, 10101111, 10101011111, 101010111111, 101010101111111, 1010101011111111, 1010101010111111111, 10101010101111111111, 10101010101011111111111, 101010101010111111111111, 101010101010101111111111111, 1010101010101011111111111111, 1010101010101010111111111111111, 10101010101010101111111111111111, 10101010101010101011111111111111111, 101010101010101010111111111111111111, 101010101010101010101111111111111111111] : List ℕ).getD n 0 := by
  intro n hn
  rw [a_eq n]
  revert n
  decide +kernel

lemma v0 : ca 0 = 1 := vals 0 (by norm_num)
lemma v1 : ca 1 = 10 := vals 1 (by norm_num)
lemma v2 : ca 2 = 101 := vals 2 (by norm_num)
lemma v3 : ca 3 = 1011 := vals 3 (by norm_num)
lemma v4 : ca 4 = 1010111 := vals 4 (by norm_num)
lemma v5 : ca 5 = 10101111 := vals 5 (by norm_num)
lemma v6 : ca 6 = 10101011111 := vals 6 (by norm_num)
lemma v7 : ca 7 = 101010111111 := vals 7 (by norm_num)
lemma v8 : ca 8 = 101010101111111 := vals 8 (by norm_num)
lemma v9 : ca 9 = 1010101011111111 := vals 9 (by norm_num)
lemma v10 : ca 10 = 1010101010111111111 := vals 10 (by norm_num)
lemma v11 : ca 11 = 10101010101111111111 := vals 11 (by norm_num)
lemma v12 : ca 12 = 10101010101011111111111 := vals 12 (by norm_num)
lemma v13 : ca 13 = 101010101010111111111111 := vals 13 (by norm_num)
lemma v14 : ca 14 = 101010101010101111111111111 := vals 14 (by norm_num)
lemma v15 : ca 15 = 1010101010101011111111111111 := vals 15 (by norm_num)
lemma v16 : ca 16 = 1010101010101010111111111111111 := vals 16 (by norm_num)
lemma v17 : ca 17 = 10101010101010101111111111111111 := vals 17 (by norm_num)
lemma v18 : ca 18 = 10101010101010101011111111111111111 := vals 18 (by norm_num)
lemma v19 : ca 19 = 101010101010101010111111111111111111 := vals 19 (by norm_num)
lemma v20 : ca 20 = 101010101010101010101111111111111111111 := vals 20 (by norm_num)

lemma altgeo (x c d m : ℕ) :
    (((10 : ℚ)) ^ 2 - 1) * ∑ k ∈ Finset.range (2 * m), (if x.testBit ((d + k) % 2) then (10 : ℚ) ^ (c + k) else 0) =
      ((if x.testBit (d % 2) then (10 : ℚ) ^ c else 0) + (if x.testBit ((d + 1) % 2) then (10 : ℚ) ^ (c + 1) else 0)) *
        ((10 : ℚ) ^ (2 * m) - 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ, mul_add, mul_add, ih,
      show (d + (2 * m + 1)) % 2 = (d + 1) % 2 by omega, show (d + 2 * m) % 2 = d % 2 by omega]
    split_ifs <;> ring

set_option maxHeartbeats 4000000 in
lemma row_split (n : ℕ) (hn : 5 ≤ n) :
    ca n = (∑ k ∈ Finset.range 2, if (elT.getD ((n - 5) % 2) 0).testBit k then 10 ^ (2 * n - k) else 0) +
      (∑ k ∈ Finset.range (n - 3), if (flLT.getD ((n - 5) % 2) 0).testBit ((n + 1 + 1 + k) % 2) then 10 ^ (n + 1 + 1 + k) else 0) +
      (∑ m ∈ Finset.range 3, if (coT.getD ((n - 5) % 2) 0).testBit m then 10 ^ (n + 1 - m) else 0) +
      (∑ k ∈ Finset.range (n - 3), if (flRT.getD ((n - 5) % 2) 0).testBit ((2 + k) % 2) then 10 ^ (2 + k) else 0) +
      (∑ k ∈ Finset.range 2, if (erT.getD ((n - 5) % 2) 0).testBit (1 - k) then 10 ^ (1 - k) else 0) := by
  unfold ca
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
  · rw [← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' := Finset.mem_range.mp hk
    rw [V_fll n hn _ ((n + 1 + 1 + k) % 2) (by push_cast; omega) (by push_cast; omega) (by push_cast; omega),
      show 2 * n - (2 + (n - 3 - 1 - k)) = n + 1 + 1 + k by omega]
  · refine Finset.sum_congr rfl fun m hm => ?_
    have hm' := Finset.mem_range.mp hm
    rw [V_co n hn _ m (by push_cast; omega) (by omega),
      show 2 * n - (2 + (n - 3) + m) = n + 1 - m by omega]
  · rw [← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' := Finset.mem_range.mp hk
    rw [V_flr n hn _ ((2 + k) % 2) (by push_cast; omega) (by push_cast; omega) (by push_cast; omega),
      show 2 * n - (2 + (n - 3) + 3 + (n - 3 - 1 - k)) = 2 + k by omega]
  · refine Finset.sum_congr rfl fun k hk => ?_
    have hk' := Finset.mem_range.mp hk
    rw [V_er n hn _ (1 - k) (by push_cast; omega) (by omega),
      show 2 * n - (2 + (n - 3) + 3 + (n - 3) + k) = 1 - k by omega]

def Esum (r : ℕ) : ℕ := ∑ k ∈ Finset.range 2, if (elT.getD r 0).testBit k then 10 ^ (1 - k) else 0
def Csum (r : ℕ) : ℕ := ∑ m ∈ Finset.range 3, if (coT.getD r 0).testBit m then 10 ^ (2 * 1 - m) else 0
def Rsum (r : ℕ) : ℕ := ∑ k ∈ Finset.range 2, if (erT.getD r 0).testBit (1 - k) then 10 ^ (1 - k) else 0

lemma piece1 (n : ℕ) (hn : 5 ≤ n) (r : ℕ) :
    (∑ k ∈ Finset.range 2, if (elT.getD r 0).testBit k then 10 ^ (2 * n - k) else 0) =
      10 ^ (2 * n - 1) * Esum r := by
  unfold Esum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' := Finset.mem_range.mp hk
  split_ifs
  · rw [← pow_add]; congr 1; omega
  · simp

lemma piece3 (n : ℕ) (hn : 5 ≤ n) (r : ℕ) :
    (∑ m ∈ Finset.range 3, if (coT.getD r 0).testBit m then 10 ^ (n + 1 - m) else 0) =
      10 ^ (n - 1) * Csum r := by
  unfold Csum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hm' := Finset.mem_range.mp hm
  split_ifs
  · rw [← pow_add]; congr 1; omega
  · simp


lemma cfn0 (n : ℕ) (h1 : 5 ≤ n) (h2 : n % 2 = 0) :
    (10 : ℚ) ^ 6 * (((10 : ℚ) ^ 2 - 1) * (ca n : ℚ)) =
      (1000000 : ℚ) * (10 : ℚ) ^ (2 * n) + (100000 : ℚ) * (10 : ℚ) ^ n + (-11000000 : ℚ) := by
  rw [row_split n h1, piece1 n h1, piece3 n h1, show (n - 5) % 2 = 1 by omega,
    show Esum 1 = 0 by decide, show Csum 1 = 10 by decide,
    show (∑ k ∈ Finset.range 2, if (erT.getD 1 0).testBit (1 - k) then 10 ^ (1 - k) else 0) = 11 by decide]
  obtain ⟨m, rfl⟩ : ∃ m, n = 3 + 2 * m + 1 := ⟨(n - 3) / 2, by omega⟩
  rw [show 3 + 2 * m + 1 - 3 = 2 * m + 1 by omega, show 2 * (3 + 2 * m + 1) - 1 = 7 + 4 * m by omega,
    show 3 + 2 * m + 1 - 1 = 3 + 2 * m by omega]
  rw [Finset.sum_range_succ, Finset.sum_range_succ]
  have g2 := altgeo (flLT.getD 1 0) (3 + 2 * m + 1 + 1 + 1) (3 + 2 * m + 1 + 1 + 1) m
  have g4 := altgeo (flRT.getD 1 0) 2 2 m
  push_cast at g2 g4 ⊢
  have b0 : (3 + 2 * m + 1 + 1 + 1) % 2 = 0 := by omega
  have b1 : ((3 + 2 * m + 1 + 1 + 1) + 1) % 2 = 1 := by omega
  have b2 : ((3 + 2 * m + 1 + 1 + 1) + 2 * m) % 2 = 0 := by omega
  have b3 : (2 + 2 * m) % 2 = 0 := by omega
  rw [b0, b1] at g2
  try simp only [b2, b3, show 2 % 2 = 0 from rfl, show (2 + 1) % 2 = 1 from rfl] at g2 g4 ⊢
  simp only [show (flLT.getD 1 0).testBit 0 = true from by decide,
    show (flLT.getD 1 0).testBit 1 = false from by decide,
    show (flRT.getD 1 0).testBit 0 = true from by decide,
    show (flRT.getD 1 0).testBit 1 = true from by decide,
    ↓reduceIte, Bool.false_eq_true] at g2 g4 ⊢
  linear_combination ((10 : ℚ) ^ 6) * g2 + ((10 : ℚ) ^ 6) * g4


lemma cfn1 (n : ℕ) (h1 : 5 ≤ n) (h2 : n % 2 = 1) :
    (10 : ℚ) ^ 5 * (((10 : ℚ) ^ 2 - 1) * (ca n : ℚ)) =
      (10000 : ℚ) * (10 : ℚ) ^ (2 * n) + (10000 : ℚ) * (10 : ℚ) ^ n + (-1100000 : ℚ) := by
  rw [row_split n h1, piece1 n h1, piece3 n h1, show (n - 5) % 2 = 0 by omega,
    show Esum 0 = 0 by decide, show Csum 0 = 10 by decide,
    show (∑ k ∈ Finset.range 2, if (erT.getD 0 0).testBit (1 - k) then 10 ^ (1 - k) else 0) = 11 by decide]
  obtain ⟨m, rfl⟩ : ∃ m, n = 3 + 2 * m := ⟨(n - 3) / 2, by omega⟩
  rw [show 3 + 2 * m - 3 = 2 * m by omega, show 2 * (3 + 2 * m) - 1 = 5 + 4 * m by omega,
    show 3 + 2 * m - 1 = 2 + 2 * m by omega]
  have g2 := altgeo (flLT.getD 0 0) (3 + 2 * m + 1 + 1) (3 + 2 * m + 1 + 1) m
  have g4 := altgeo (flRT.getD 0 0) 2 2 m
  push_cast at g2 g4 ⊢
  have b0 : (3 + 2 * m + 1 + 1) % 2 = 1 := by omega
  have b1 : ((3 + 2 * m + 1 + 1) + 1) % 2 = 0 := by omega
  have b2 : ((3 + 2 * m + 1 + 1) + 2 * m) % 2 = 1 := by omega
  have b3 : (2 + 2 * m) % 2 = 0 := by omega
  rw [b0, b1] at g2
  try simp only [b2, b3, show 2 % 2 = 0 from rfl, show (2 + 1) % 2 = 1 from rfl] at g2 g4 ⊢
  simp only [show (flLT.getD 0 0).testBit 1 = true from by decide,
    show (flLT.getD 0 0).testBit 0 = false from by decide,
    show (flRT.getD 0 0).testBit 0 = true from by decide,
    show (flRT.getD 0 0).testBit 1 = true from by decide,
    ↓reduceIte, Bool.false_eq_true] at g2 g4 ⊢
  linear_combination ((10 : ℚ) ^ 5) * g2 + ((10 : ℚ) ^ 5) * g4


/-- a(n) = 11*a(n-1) + 9990*a(n-2) - 110000*a(n-3) + 100000*a(n-4) for n > 5 -/
theorem recurrence0 (n : ℕ) (hn : 6 ≤ n) : (ca n : ℤ) = (((((11 : ℤ) * (ca (n - 1) : ℤ)) + ((9990 : ℤ) * (ca (n - 2) : ℤ))) - ((110000 : ℤ) * (ca (n - 3) : ℤ))) + ((100000 : ℤ) * (ca (n - 4) : ℤ))) := by
  rcases Nat.lt_or_ge n 9 with hlt | hge
  · interval_cases n <;> norm_num [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9] at *
  · suffices hq : (ca n : ℚ) = (((((11 : ℚ) * (ca (n - 1) : ℚ)) + ((9990 : ℚ) * (ca (n - 2) : ℚ))) - ((110000 : ℚ) * (ca (n - 3) : ℚ))) + ((100000 : ℚ) * (ca (n - 4) : ℚ))) by exact_mod_cast hq
    rcases (by omega : n % 2 = 0 ∨ n % 2 = 1) with hpar | hpar
    · obtain ⟨q, rfl⟩ : ∃ q, n = 10 + 2 * q := ⟨(n - 10) / 2, by omega⟩
      have c0 := cfn0 (10 + 2 * q) (by omega) (by omega)
      rw [show 10 + 2 * q - 1 = 9 + 2 * q by omega]
      have c1 := cfn1 (9 + 2 * q) (by omega) (by omega)
      rw [show 10 + 2 * q - 2 = 8 + 2 * q by omega]
      have c2 := cfn0 (8 + 2 * q) (by omega) (by omega)
      rw [show 10 + 2 * q - 3 = 7 + 2 * q by omega]
      have c3 := cfn1 (7 + 2 * q) (by omega) (by omega)
      rw [show 10 + 2 * q - 4 = 6 + 2 * q by omega]
      have c4 := cfn0 (6 + 2 * q) (by omega) (by omega)
      try simp only [pow_add, pow_mul, neg_one_sq, one_pow, mul_one, one_mul, show ((-1 : ℚ)) ^ 4 = 1 by norm_num, show ((-1 : ℚ)) ^ 6 = 1 by norm_num, show ((-1 : ℚ)) ^ 12 = 1 by norm_num] at c0 c1 c2 c3 c4 ⊢
      push_cast at c0 c1 c2 c3 c4 ⊢
      linear_combination (1 / ((10 : ℚ) ^ 6 * ((10 : ℚ) ^ 2 - 1))) * c0 + (-((11 : ℚ)) / ((10 : ℚ) ^ 5 * ((10 : ℚ) ^ 2 - 1))) * c1 + (-((9990 : ℚ)) / ((10 : ℚ) ^ 6 * ((10 : ℚ) ^ 2 - 1))) * c2 + (-((-110000 : ℚ)) / ((10 : ℚ) ^ 5 * ((10 : ℚ) ^ 2 - 1))) * c3 + (-((100000 : ℚ)) / ((10 : ℚ) ^ 6 * ((10 : ℚ) ^ 2 - 1))) * c4
    · obtain ⟨q, rfl⟩ : ∃ q, n = 9 + 2 * q := ⟨(n - 9) / 2, by omega⟩
      have c0 := cfn1 (9 + 2 * q) (by omega) (by omega)
      rw [show 9 + 2 * q - 1 = 8 + 2 * q by omega]
      have c1 := cfn0 (8 + 2 * q) (by omega) (by omega)
      rw [show 9 + 2 * q - 2 = 7 + 2 * q by omega]
      have c2 := cfn1 (7 + 2 * q) (by omega) (by omega)
      rw [show 9 + 2 * q - 3 = 6 + 2 * q by omega]
      have c3 := cfn0 (6 + 2 * q) (by omega) (by omega)
      rw [show 9 + 2 * q - 4 = 5 + 2 * q by omega]
      have c4 := cfn1 (5 + 2 * q) (by omega) (by omega)
      try simp only [pow_add, pow_mul, neg_one_sq, one_pow, mul_one, one_mul, show ((-1 : ℚ)) ^ 4 = 1 by norm_num, show ((-1 : ℚ)) ^ 6 = 1 by norm_num, show ((-1 : ℚ)) ^ 12 = 1 by norm_num] at c0 c1 c2 c3 c4 ⊢
      push_cast at c0 c1 c2 c3 c4 ⊢
      linear_combination (1 / ((10 : ℚ) ^ 5 * ((10 : ℚ) ^ 2 - 1))) * c0 + (-((11 : ℚ)) / ((10 : ℚ) ^ 6 * ((10 : ℚ) ^ 2 - 1))) * c1 + (-((9990 : ℚ)) / ((10 : ℚ) ^ 5 * ((10 : ℚ) ^ 2 - 1))) * c2 + (-((-110000 : ℚ)) / ((10 : ℚ) ^ 6 * ((10 : ℚ) ^ 2 - 1))) * c3 + (-((100000 : ℚ)) / ((10 : ℚ) ^ 5 * ((10 : ℚ) ^ 2 - 1))) * c4


lemma gfrec1 (n : ℕ) (hn : 6 ≤ n) : (ca n : ℚ) = ((11 : ℚ)) * (ca (n - 1) : ℚ) + ((9990 : ℚ)) * (ca (n - 2) : ℚ) + ((-110000 : ℚ)) * (ca (n - 3) : ℚ) + ((100000 : ℚ)) * (ca (n - 4) : ℚ) := by
  rcases Nat.lt_or_ge n 9 with hlt | hge
  · interval_cases n <;> norm_num [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9] at *
  · rcases (by omega : n % 2 = 0 ∨ n % 2 = 1) with hpar | hpar
    · obtain ⟨q, rfl⟩ : ∃ q, n = 10 + 2 * q := ⟨(n - 10) / 2, by omega⟩
      have c0 := cfn0 (10 + 2 * q) (by omega) (by omega)
      rw [show 10 + 2 * q - 1 = 9 + 2 * q by omega]
      have c1 := cfn1 (9 + 2 * q) (by omega) (by omega)
      rw [show 10 + 2 * q - 2 = 8 + 2 * q by omega]
      have c2 := cfn0 (8 + 2 * q) (by omega) (by omega)
      rw [show 10 + 2 * q - 3 = 7 + 2 * q by omega]
      have c3 := cfn1 (7 + 2 * q) (by omega) (by omega)
      rw [show 10 + 2 * q - 4 = 6 + 2 * q by omega]
      have c4 := cfn0 (6 + 2 * q) (by omega) (by omega)
      try simp only [pow_add, pow_mul, neg_one_sq, one_pow, mul_one, one_mul, show ((-1 : ℚ)) ^ 4 = 1 by norm_num, show ((-1 : ℚ)) ^ 6 = 1 by norm_num, show ((-1 : ℚ)) ^ 12 = 1 by norm_num] at c0 c1 c2 c3 c4 ⊢
      push_cast at c0 c1 c2 c3 c4 ⊢
      linear_combination (1 / ((10 : ℚ) ^ 6 * ((10 : ℚ) ^ 2 - 1))) * c0 + (-((11 : ℚ)) / ((10 : ℚ) ^ 5 * ((10 : ℚ) ^ 2 - 1))) * c1 + (-((9990 : ℚ)) / ((10 : ℚ) ^ 6 * ((10 : ℚ) ^ 2 - 1))) * c2 + (-((-110000 : ℚ)) / ((10 : ℚ) ^ 5 * ((10 : ℚ) ^ 2 - 1))) * c3 + (-((100000 : ℚ)) / ((10 : ℚ) ^ 6 * ((10 : ℚ) ^ 2 - 1))) * c4
    · obtain ⟨q, rfl⟩ : ∃ q, n = 9 + 2 * q := ⟨(n - 9) / 2, by omega⟩
      have c0 := cfn1 (9 + 2 * q) (by omega) (by omega)
      rw [show 9 + 2 * q - 1 = 8 + 2 * q by omega]
      have c1 := cfn0 (8 + 2 * q) (by omega) (by omega)
      rw [show 9 + 2 * q - 2 = 7 + 2 * q by omega]
      have c2 := cfn1 (7 + 2 * q) (by omega) (by omega)
      rw [show 9 + 2 * q - 3 = 6 + 2 * q by omega]
      have c3 := cfn0 (6 + 2 * q) (by omega) (by omega)
      rw [show 9 + 2 * q - 4 = 5 + 2 * q by omega]
      have c4 := cfn1 (5 + 2 * q) (by omega) (by omega)
      try simp only [pow_add, pow_mul, neg_one_sq, one_pow, mul_one, one_mul, show ((-1 : ℚ)) ^ 4 = 1 by norm_num, show ((-1 : ℚ)) ^ 6 = 1 by norm_num, show ((-1 : ℚ)) ^ 12 = 1 by norm_num] at c0 c1 c2 c3 c4 ⊢
      push_cast at c0 c1 c2 c3 c4 ⊢
      linear_combination (1 / ((10 : ℚ) ^ 5 * ((10 : ℚ) ^ 2 - 1))) * c0 + (-((11 : ℚ)) / ((10 : ℚ) ^ 6 * ((10 : ℚ) ^ 2 - 1))) * c1 + (-((9990 : ℚ)) / ((10 : ℚ) ^ 5 * ((10 : ℚ) ^ 2 - 1))) * c2 + (-((-110000 : ℚ)) / ((10 : ℚ) ^ 6 * ((10 : ℚ) ^ 2 - 1))) * c3 + (-((100000 : ℚ)) / ((10 : ℚ) ^ 5 * ((10 : ℚ) ^ 2 - 1))) * c4

open PowerSeries in
/-- G.f.: (1 - x - 9999*x^2 + 10000*x^3 + 990000*x^4 - 1000000*x^5) / ((1-x)*(1-10*x)*(1-100*x)*(1+100*x)) -/
theorem gf1 : PowerSeries.mk (fun n => (ca n : ℚ)) = ((1 - X - 9999*X ^ 2 + 10000*X ^ 3 + 990000*X ^ 4 - 1000000*X ^ 5)) * (((1-X)*(1-10*X)*(1-100*X)*(1+100*X)))⁻¹ := by
  set G : ℚ⟦X⟧ := PowerSeries.mk (fun n => (ca n : ℚ))
  have hden : constantCoeff ((((1-X)*(1-10*X)*(1-100*X)*(1+100*X))) : ℚ⟦X⟧) ≠ 0 := by simp
  have eQ : G * (((1-X)*(1-10*X)*(1-100*X)*(1+100*X))) = C ((1 : ℚ)) * G + C ((-11 : ℚ)) * (G * X ^ 1) + C ((-9990 : ℚ)) * (G * X ^ 2) + C ((110000 : ℚ)) * (G * X ^ 3) + C ((-100000 : ℚ)) * (G * X ^ 4) := by
    (try simp only [map_neg, map_ofNat, map_one, map_div₀, map_natCast]) <;> ring
  have eP : (((1 - X - 9999*X ^ 2 + 10000*X ^ 3 + 990000*X ^ 4 - 1000000*X ^ 5)) : ℚ⟦X⟧) = C ((1 : ℚ)) + C ((-1 : ℚ)) * X ^ 1 + C ((-9999 : ℚ)) * X ^ 2 + C ((10000 : ℚ)) * X ^ 3 + C ((990000 : ℚ)) * X ^ 4 + C ((-1000000 : ℚ)) * X ^ 5 := by
    (try simp only [map_neg, map_ofNat, map_one, map_div₀, map_natCast]) <;> ring
  have key : G * (((1-X)*(1-10*X)*(1-100*X)*(1+100*X))) = (1 - X - 9999*X ^ 2 + 10000*X ^ 3 + 990000*X ^ 4 - 1000000*X ^ 5) := by
    rw [eQ, eP]
    ext n
    simp only [map_add, map_sub, coeff_C_mul, coeff_mul_X_pow', coeff_X_pow, G, coeff_mk, coeff_C]
    rcases Nat.lt_or_ge n 6 with hn | hn
    · interval_cases n <;> norm_num [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9]
    · simp only [show 1 ≤ n by omega, show 2 ≤ n by omega, show 3 ≤ n by omega, show 4 ≤ n by omega, show 5 ≤ n by omega, show n ≠ 0 by omega, show n ≠ 1 by omega, show n ≠ 2 by omega, show n ≠ 3 by omega, show n ≠ 4 by omega, show n ≠ 5 by omega, show n - 1 ≠ 0 by omega, show n - 2 ≠ 0 by omega, show n - 3 ≠ 0 by omega, show n - 4 ≠ 0 by omega, show n - 5 ≠ 0 by omega, if_true, if_false, ↓reduceIte, ne_eq, not_false_eq_true]
      have hr := gfrec1 n hn
      linear_combination ((1 : ℚ)) * hr
  rw [← key, mul_assoc, PowerSeries.mul_inv_cancel _ hden, mul_one]


open PowerSeries in
/-- All the proved formula lines of the entry, together. -/
theorem formulas :
    (∀ n : ℕ, 6 ≤ n → (ca n : ℤ) = (((((11 : ℤ) * (ca (n - 1) : ℤ)) + ((9990 : ℤ) * (ca (n - 2) : ℤ))) - ((110000 : ℤ) * (ca (n - 3) : ℤ))) + ((100000 : ℤ) * (ca (n - 4) : ℤ)))) ∧
    (PowerSeries.mk (fun n => (ca n : ℚ)) = ((1 - X - 9999*X ^ 2 + 10000*X ^ 3 + 990000*X ^ 4 - 1000000*X ^ 5)) * (((1-X)*(1-10*X)*(1-100*X)*(1+100*X)))⁻¹) :=
  ⟨recurrence0, gf1⟩



/-- a(n) = 10^n*(100^floor(n/2) - 1)/99 + (10^(n-1) - 1)/9 for n > 1 -/
theorem keller_n (n : ℕ) (hn : 2 ≤ n) : (ca n : ℚ) = 10 ^ n * (100 ^ (n / 2) - 1) / 99 + (10 ^ (n - 1) - 1) / 9 := by
  rcases Nat.lt_or_ge n 5 with hlt | hge
  · interval_cases n <;> norm_num [v2, v3, v4]
  · rcases Nat.even_or_odd' n with ⟨j, hj | hj⟩
    · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
      subst hj
      have c := cfn0 (2 * (i + 1)) (by omega) (by omega)
      rw [show 2 * (i + 1) / 2 = i + 1 by omega, show 2 * (i + 1) - 1 = 2 * i + 1 by omega,
        show (100 : ℚ) = 10 ^ 2 by norm_num, ← pow_mul]
      linear_combination (1 / ((10 : ℚ) ^ 6 * ((10 : ℚ) ^ 2 - 1))) * c
    · subst hj
      have c := cfn1 (2 * j + 1) (by omega) (by omega)
      rw [show (2 * j + 1) / 2 = j by omega, show 2 * j + 1 - 1 = 2 * j by omega,
        show (100 : ℚ) = 10 ^ 2 by norm_num, ← pow_mul]
      linear_combination (1 / ((10 : ℚ) ^ 5 * ((10 : ℚ) ^ 2 - 1))) * c


/-! ## The statement's definitions and the bridge -/

open PowerSeries






theorem rule_eq (l c r : Bool) :
    rule l c r = Nat.testBit 141 (4 * l.toNat + 2 * c.toNat + r.toNat) := by
  cases l <;> cases c <;> cases r <;> rfl

theorem cstate_eq (t : ℕ) : cstate t = state 141 t := by
  induction t with
  | zero => funext i; rfl
  | succ t ih =>
    funext i
    show rule (cstate t (i - 1)) (cstate t i) (cstate t (i + 1)) = step 141 (state 141 t) i
    rw [ih, rule_eq]
    rfl

theorem row_eq (n : ℕ) :
    rowDigits (state 141 n) n = ∑ k ∈ Finset.range (2 * n + 1), if cstate n ((k : ℤ) - n) then 10 ^ (2 * n - k) else 0 := by
  rw [rowDigits, ← cstate_eq]
  conv_lhs => rw [← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' := Finset.mem_range.mp hk
  rw [show ((n : ℤ) - ((2 * n + 1 - 1 - k : ℕ) : ℤ)) = (k : ℤ) - n by omega,
    show 2 * n + 1 - 1 - k = 2 * n - k by omega]
  cases cstate n ((k : ℤ) - n) <;> simp

theorem a_eq_ca : a = ca := by
  funext n
  rw [a, ca, row_eq]

theorem controls : ∀ n ≤ 20, a n = ([1, 10, 101, 1011, 1010111, 10101111, 10101011111, 101010111111, 101010101111111, 1010101011111111, 1010101010111111111, 10101010101111111111, 10101010101011111111111, 101010101010111111111111, 101010101010101111111111111, 1010101010101011111111111111, 1010101010101010111111111111111, 10101010101010101111111111111111, 10101010101010101011111111111111111, 101010101010101010111111111111111111, 101010101010101010101111111111111111111] : List ℕ).getD n 0 := by
  rw [a_eq_ca]
  exact vals

/-- The site's problem, as stated in `main`. -/
theorem conj :
    (∀ n : ℕ, 5 < n →
      (a n : ℤ) = 11 * a (n - 1) + 9990 * a (n - 2) - 110000 * a (n - 3) + 100000 * a (n - 4)) ∧
    A = (1 - X - 9999 * X ^ 2 + 10000 * X ^ 3 + 990000 * X ^ 4 - 1000000 * X ^ 5) *
      ((1 - X) * (1 - 10 * X) * (1 - 100 * X) * (1 + 100 * X))⁻¹ ∧
    (∀ n : ℕ, 1 < n → (a n : ℚ) = 10 ^ n * (100 ^ (n / 2) - 1) / 99 + (10 ^ (n - 1) - 1) / 9) := by
  rw [show A = PowerSeries.mk (fun n => (a n : ℚ)) from rfl, a_eq_ca]
  exact ⟨fun n hn => (recurrence0 n (by omega)).trans (by ring),
    gf1,
    fun n hn => (keller_n n (by omega)).trans (by ring)⟩

end OMA.S_oeis_a267526

theorem OMA.solution : type_of% @OMA.S_oeis_a267526.main :=
  OMA.S_oeis_a267526.conj
