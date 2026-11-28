import OMAStatements.S_oeis_a267158

namespace OMA.S_oeis_a267158


/-- Rule 107 as a local map: the new state of a cell from (left, center, right). -/
def rule (l c r : Bool) : Bool := (107 : ℕ).testBit ((cond l 4 0) + (cond c 2 0) + (cond r 1 0))

/-- The configuration at time `t`, started from the single ON cell at 0. -/
def cstate : ℕ → ℤ → Bool
  | 0, i => decide (i = 0)
  | t + 1, i => rule (cstate t (i - 1)) (cstate t i) (cstate t (i + 1))


/-- A267158(n): the number of ON cells among `-n..n` in row `n`. -/
def ca (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (2 * n + 1), if cstate n ((k : ℤ) - n) then 1 else 0


/-! ## A finite certificate: rows `0..15` on the window `[-16, 16]` -/

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

def W : ℕ := 16

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

/-- The rows `0..15`, computed outside Lean and checked cell by cell below. -/
def stages : List (Bool × ℕ) :=
  [(false, 65536),
    (true, 8589737983),
    (false, 425984),
    (true, 8589377535),
    (false, 1949696),
    (true, 8587280383),
    (false, 7192576),
    (true, 8581513215),
    (false, 29474816),
    (true, 8547827711),
    (false, 113688576),
    (true, 8455192575),
    (false, 471597056),
    (true, 7916224511),
    (false, 1819017216),
    (true, 6434062335)]

lemma stages_ok : initOK (stages.getD 0 default) = true ∧
    ∀ t < 15, stepOK (stages.getD t default) (stages.getD (t + 1) default) = true := by
  decide +kernel

lemma certified (t : ℕ) (ht : t ≤ 15) :
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

/-! ## The regime from row 15 on -/

def bgT : List Bool := [true, false, true, false]
def flT : List Bool := [true, false, true, false]
/-- Bit `j` of the left edge block: cell `-t + j`. -/
def elT : List ℕ := [8191, 0, 8191, 0]
/-- Bit `j` of the right edge block: cell `t - j`. -/
def erT : List ℕ := [7934, 1799, 6906, 6939]
/-- Bit `m` of the center block: cell `m - 0`. -/
def coT : List ℕ := [1, 0, 1, 0]

def V (t : ℕ) (i : ℤ) : Bool :=
  if i < -(t : ℤ) ∨ (t : ℤ) < i then bgT.getD ((t - 15) % 4) false
  else if i + t ≤ 12 then (elT.getD ((t - 15) % 4) 0).testBit (i + t).toNat
  else if (t : ℤ) - i ≤ 12 then (erT.getD ((t - 15) % 4) 0).testBit ((t : ℤ) - i).toNat
  else if -(0 : ℤ) ≤ i ∧ i ≤ 0 then (coT.getD ((t - 15) % 4) 0).testBit (i + 0).toNat
  else flT.getD ((t - 15) % 4) false

lemma V_out (t : ℕ) (i : ℤ) (h : i < -(t : ℤ) ∨ (t : ℤ) < i) :
    V t i = bgT.getD ((t - 15) % 4) false := by
  unfold V; rw [if_pos h]

lemma V_el (t : ℕ) (ht : 15 ≤ t) (i : ℤ) (j : ℕ) (hj : i + t = j) (hjA : j ≤ 12) :
    V t i = (elT.getD ((t - 15) % 4) 0).testBit j := by
  unfold V
  rw [if_neg (by omega), if_pos (by omega)]
  congr 1
  omega

lemma V_er (t : ℕ) (ht : 15 ≤ t) (i : ℤ) (j : ℕ) (hj : (t : ℤ) - i = j) (hjA : j ≤ 12) :
    V t i = (erT.getD ((t - 15) % 4) 0).testBit j := by
  unfold V
  rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)]
  congr 1
  omega

lemma V_co (t : ℕ) (ht : 15 ≤ t) (i : ℤ) (m : ℕ) (hm : i + 0 = m) (hmK : m ≤ 2 * 0) :
    V t i = (coT.getD ((t - 15) % 4) 0).testBit m := by
  unfold V
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]
  congr 1
  omega

lemma V_fl (t : ℕ) (ht : 15 ≤ t) (i : ℤ) (h1 : (12 : ℤ) < i + t) (h2 : (12 : ℤ) < (t : ℤ) - i)
    (h3 : i < -(0 : ℤ) ∨ (0 : ℤ) < i) : V t i = flT.getD ((t - 15) % 4) false := by
  unfold V
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]


set_option maxHeartbeats 4000000 in
lemma stepV (t : ℕ) (ht : 15 ≤ t) (i : ℤ) :
    rule (V t (i - 1)) (V t i) (V t (i + 1)) = V (t + 1) i := by
  rcases (by omega : (i ≤ -(t : ℤ) - 3) ∨ (i = -(t : ℤ) - 2) ∨ (i + t + 1 = 0) ∨ (i + t + 1 = 1) ∨ (i + t + 1 = 2) ∨ (i + t + 1 = 3) ∨ (i + t + 1 = 4) ∨ (i + t + 1 = 5) ∨ (i + t + 1 = 6) ∨ (i + t + 1 = 7) ∨ (i + t + 1 = 8) ∨ (i + t + 1 = 9) ∨ (i + t + 1 = 10) ∨ (i + t + 1 = 11) ∨ (i + t + 1 = 12) ∨ (i + t + 1 = 13) ∨ (i + t + 1 = 14) ∨ (14 < i + t + 1 ∧ i < -0 - 1) ∨ (i = -1) ∨ (i = 0) ∨ (i = 1) ∨ (0 + 1 < i ∧ 14 < (t : ℤ) + 1 - i) ∨ ((t : ℤ) + 1 - i = 14) ∨ ((t : ℤ) + 1 - i = 13) ∨ ((t : ℤ) + 1 - i = 12) ∨ ((t : ℤ) + 1 - i = 11) ∨ ((t : ℤ) + 1 - i = 10) ∨ ((t : ℤ) + 1 - i = 9) ∨ ((t : ℤ) + 1 - i = 8) ∨ ((t : ℤ) + 1 - i = 7) ∨ ((t : ℤ) + 1 - i = 6) ∨ ((t : ℤ) + 1 - i = 5) ∨ ((t : ℤ) + 1 - i = 4) ∨ ((t : ℤ) + 1 - i = 3) ∨ ((t : ℤ) + 1 - i = 2) ∨ ((t : ℤ) + 1 - i = 1) ∨ ((t : ℤ) + 1 - i = 0) ∨ (i = (t : ℤ) + 2) ∨ ((t : ℤ) + 3 ≤ i)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · rw [V_out t (i - 1) (by push_cast; omega), V_out t i (by push_cast; omega), V_out t (i + 1) (by push_cast; omega), V_out (t + 1) i (by push_cast; omega)]
    obtain ⟨q, hq, hqq⟩ : ∃ q, q < 4 ∧ (t - 15) % 4 = q := ⟨_, Nat.mod_lt _ (by norm_num), rfl⟩
    rw [show (t + 1 - 15) % 4 = (q + 1) % 4 by omega, hqq]
    interval_cases q <;> decide
  · rw [V_out t (i - 1) (by push_cast; omega), V_out t i (by push_cast; omega), V_out t (i + 1) (by push_cast; omega), V_out (t + 1) i (by push_cast; omega)]
    obtain ⟨q, hq, hqq⟩ : ∃ q, q < 4 ∧ (t - 15) % 4 = q := ⟨_, Nat.mod_lt _ (by norm_num), rfl⟩
    rw [show (t + 1 - 15) % 4 = (q + 1) % 4 by omega, hqq]
    interval_cases q <;> decide
  · rw [V_out t (i - 1) (by push_cast; omega), V_out t i (by push_cast; omega), V_el t ht (i + 1) 0 (by omega) (by norm_num), V_el (t + 1) (by omega) i 0 (by push_cast; omega) (by norm_num)]
    obtain ⟨q, hq, hqq⟩ : ∃ q, q < 4 ∧ (t - 15) % 4 = q := ⟨_, Nat.mod_lt _ (by norm_num), rfl⟩
    rw [show (t + 1 - 15) % 4 = (q + 1) % 4 by omega, hqq]
    interval_cases q <;> decide
  · rw [V_out t (i - 1) (by push_cast; omega), V_el t ht i 0 (by omega) (by norm_num), V_el t ht (i + 1) 1 (by omega) (by norm_num), V_el (t + 1) (by omega) i 1 (by push_cast; omega) (by norm_num)]
    obtain ⟨q, hq, hqq⟩ : ∃ q, q < 4 ∧ (t - 15) % 4 = q := ⟨_, Nat.mod_lt _ (by norm_num), rfl⟩
    rw [show (t + 1 - 15) % 4 = (q + 1) % 4 by omega, hqq]
    interval_cases q <;> decide
  · rw [V_el t ht (i - 1) 0 (by omega) (by norm_num), V_el t ht i 1 (by omega) (by norm_num), V_el t ht (i + 1) 2 (by omega) (by norm_num), V_el (t + 1) (by omega) i 2 (by push_cast; omega) (by norm_num)]
    obtain ⟨q, hq, hqq⟩ : ∃ q, q < 4 ∧ (t - 15) % 4 = q := ⟨_, Nat.mod_lt _ (by norm_num), rfl⟩
    rw [show (t + 1 - 15) % 4 = (q + 1) % 4 by omega, hqq]
    interval_cases q <;> decide
  · rw [V_el t ht (i - 1) 1 (by omega) (by norm_num), V_el t ht i 2 (by omega) (by norm_num), V_el t ht (i + 1) 3 (by omega) (by norm_num), V_el (t + 1) (by omega) i 3 (by push_cast; omega) (by norm_num)]
    obtain ⟨q, hq, hqq⟩ : ∃ q, q < 4 ∧ (t - 15) % 4 = q := ⟨_, Nat.mod_lt _ (by norm_num), rfl⟩
    rw [show (t + 1 - 15) % 4 = (q + 1) % 4 by omega, hqq]
    interval_cases q <;> decide
  · rw [V_el t ht (i - 1) 2 (by omega) (by norm_num), V_el t ht i 3 (by omega) (by norm_num), V_el t ht (i + 1) 4 (by omega) (by norm_num), V_el (t + 1) (by omega) i 4 (by push_cast; omega) (by norm_num)]
    obtain ⟨q, hq, hqq⟩ : ∃ q, q < 4 ∧ (t - 15) % 4 = q := ⟨_, Nat.mod_lt _ (by norm_num), rfl⟩
    rw [show (t + 1 - 15) % 4 = (q + 1) % 4 by omega, hqq]
    interval_cases q <;> decide
  · rw [V_el t ht (i - 1) 3 (by omega) (by norm_num), V_el t ht i 4 (by omega) (by norm_num), V_el t ht (i + 1) 5 (by omega) (by norm_num), V_el (t + 1) (by omega) i 5 (by push_cast; omega) (by norm_num)]
    obtain ⟨q, hq, hqq⟩ : ∃ q, q < 4 ∧ (t - 15) % 4 = q := ⟨_, Nat.mod_lt _ (by norm_num), rfl⟩
    rw [show (t + 1 - 15) % 4 = (q + 1) % 4 by omega, hqq]
    interval_cases q <;> decide
  · rw [V_el t ht (i - 1) 4 (by omega) (by norm_num), V_el t ht i 5 (by omega) (by norm_num), V_el t ht (i + 1) 6 (by omega) (by norm_num), V_el (t + 1) (by omega) i 6 (by push_cast; omega) (by norm_num)]
    obtain ⟨q, hq, hqq⟩ : ∃ q, q < 4 ∧ (t - 15) % 4 = q := ⟨_, Nat.mod_lt _ (by norm_num), rfl⟩
    rw [show (t + 1 - 15) % 4 = (q + 1) % 4 by omega, hqq]
    interval_cases q <;> decide
  · rw [V_el t ht (i - 1) 5 (by omega) (by norm_num), V_el t ht i 6 (by omega) (by norm_num), V_el t ht (i + 1) 7 (by omega) (by norm_num), V_el (t + 1) (by omega) i 7 (by push_cast; omega) (by norm_num)]
    obtain ⟨q, hq, hqq⟩ : ∃ q, q < 4 ∧ (t - 15) % 4 = q := ⟨_, Nat.mod_lt _ (by norm_num), rfl⟩
    rw [show (t + 1 - 15) % 4 = (q + 1) % 4 by omega, hqq]
    interval_cases q <;> decide
  · rw [V_el t ht (i - 1) 6 (by omega) (by norm_num), V_el t ht i 7 (by omega) (by norm_num), V_el t ht (i + 1) 8 (by omega) (by norm_num), V_el (t + 1) (by omega) i 8 (by push_cast; omega) (by norm_num)]
    obtain ⟨q, hq, hqq⟩ : ∃ q, q < 4 ∧ (t - 15) % 4 = q := ⟨_, Nat.mod_lt _ (by norm_num), rfl⟩
    rw [show (t + 1 - 15) % 4 = (q + 1) % 4 by omega, hqq]
    interval_cases q <;> decide
  · rw [V_el t ht (i - 1) 7 (by omega) (by norm_num), V_el t ht i 8 (by omega) (by norm_num), V_el t ht (i + 1) 9 (by omega) (by norm_num), V_el (t + 1) (by omega) i 9 (by push_cast; omega) (by norm_num)]
    obtain ⟨q, hq, hqq⟩ : ∃ q, q < 4 ∧ (t - 15) % 4 = q := ⟨_, Nat.mod_lt _ (by norm_num), rfl⟩
    rw [show (t + 1 - 15) % 4 = (q + 1) % 4 by omega, hqq]
    interval_cases q <;> decide
  · rw [V_el t ht (i - 1) 8 (by omega) (by norm_num), V_el t ht i 9 (by omega) (by norm_num), V_el t ht (i + 1) 10 (by omega) (by norm_num), V_el (t + 1) (by omega) i 10 (by push_cast; omega) (by norm_num)]
    obtain ⟨q, hq, hqq⟩ : ∃ q, q < 4 ∧ (t - 15) % 4 = q := ⟨_, Nat.mod_lt _ (by norm_num), rfl⟩
    rw [show (t + 1 - 15) % 4 = (q + 1) % 4 by omega, hqq]
    interval_cases q <;> decide
  · rw [V_el t ht (i - 1) 9 (by omega) (by norm_num), V_el t ht i 10 (by omega) (by norm_num), V_el t ht (i + 1) 11 (by omega) (by norm_num), V_el (t + 1) (by omega) i 11 (by push_cast; omega) (by norm_num)]
    obtain ⟨q, hq, hqq⟩ : ∃ q, q < 4 ∧ (t - 15) % 4 = q := ⟨_, Nat.mod_lt _ (by norm_num), rfl⟩
    rw [show (t + 1 - 15) % 4 = (q + 1) % 4 by omega, hqq]
    interval_cases q <;> decide
  · rw [V_el t ht (i - 1) 10 (by omega) (by norm_num), V_el t ht i 11 (by omega) (by norm_num), V_el t ht (i + 1) 12 (by omega) (by norm_num), V_el (t + 1) (by omega) i 12 (by push_cast; omega) (by norm_num)]
    obtain ⟨q, hq, hqq⟩ : ∃ q, q < 4 ∧ (t - 15) % 4 = q := ⟨_, Nat.mod_lt _ (by norm_num), rfl⟩
    rw [show (t + 1 - 15) % 4 = (q + 1) % 4 by omega, hqq]
    interval_cases q <;> decide
  · rw [V_el t ht (i - 1) 11 (by omega) (by norm_num), V_el t ht i 12 (by omega) (by norm_num), V_fl t ht (i + 1) (by omega) (by omega) (by omega), V_fl (t + 1) (by omega) i (by push_cast; omega) (by push_cast; omega) (by omega)]
    obtain ⟨q, hq, hqq⟩ : ∃ q, q < 4 ∧ (t - 15) % 4 = q := ⟨_, Nat.mod_lt _ (by norm_num), rfl⟩
    rw [show (t + 1 - 15) % 4 = (q + 1) % 4 by omega, hqq]
    interval_cases q <;> decide
  · rw [V_el t ht (i - 1) 12 (by omega) (by norm_num), V_fl t ht i (by omega) (by omega) (by omega), V_fl t ht (i + 1) (by omega) (by omega) (by omega), V_fl (t + 1) (by omega) i (by push_cast; omega) (by push_cast; omega) (by omega)]
    obtain ⟨q, hq, hqq⟩ : ∃ q, q < 4 ∧ (t - 15) % 4 = q := ⟨_, Nat.mod_lt _ (by norm_num), rfl⟩
    rw [show (t + 1 - 15) % 4 = (q + 1) % 4 by omega, hqq]
    interval_cases q <;> decide
  · rw [V_fl t ht (i - 1) (by omega) (by omega) (by omega), V_fl t ht i (by omega) (by omega) (by omega), V_fl t ht (i + 1) (by omega) (by omega) (by omega), V_fl (t + 1) (by omega) i (by push_cast; omega) (by push_cast; omega) (by omega)]
    obtain ⟨q, hq, hqq⟩ : ∃ q, q < 4 ∧ (t - 15) % 4 = q := ⟨_, Nat.mod_lt _ (by norm_num), rfl⟩
    rw [show (t + 1 - 15) % 4 = (q + 1) % 4 by omega, hqq]
    interval_cases q <;> decide
  · rw [V_fl t ht (i - 1) (by omega) (by omega) (by omega), V_fl t ht i (by omega) (by omega) (by omega), V_co t ht (i + 1) 0 (by omega) (by norm_num), V_fl (t + 1) (by omega) i (by push_cast; omega) (by push_cast; omega) (by omega)]
    obtain ⟨q, hq, hqq⟩ : ∃ q, q < 4 ∧ (t - 15) % 4 = q := ⟨_, Nat.mod_lt _ (by norm_num), rfl⟩
    rw [show (t + 1 - 15) % 4 = (q + 1) % 4 by omega, hqq]
    interval_cases q <;> decide
  · rw [V_fl t ht (i - 1) (by omega) (by omega) (by omega), V_co t ht i 0 (by omega) (by norm_num), V_fl t ht (i + 1) (by omega) (by omega) (by omega), V_co (t + 1) (by omega) i 0 (by omega) (by norm_num)]
    obtain ⟨q, hq, hqq⟩ : ∃ q, q < 4 ∧ (t - 15) % 4 = q := ⟨_, Nat.mod_lt _ (by norm_num), rfl⟩
    rw [show (t + 1 - 15) % 4 = (q + 1) % 4 by omega, hqq]
    interval_cases q <;> decide
  · rw [V_co t ht (i - 1) 0 (by omega) (by norm_num), V_fl t ht i (by omega) (by omega) (by omega), V_fl t ht (i + 1) (by omega) (by omega) (by omega), V_fl (t + 1) (by omega) i (by push_cast; omega) (by push_cast; omega) (by omega)]
    obtain ⟨q, hq, hqq⟩ : ∃ q, q < 4 ∧ (t - 15) % 4 = q := ⟨_, Nat.mod_lt _ (by norm_num), rfl⟩
    rw [show (t + 1 - 15) % 4 = (q + 1) % 4 by omega, hqq]
    interval_cases q <;> decide
  · rw [V_fl t ht (i - 1) (by omega) (by omega) (by omega), V_fl t ht i (by omega) (by omega) (by omega), V_fl t ht (i + 1) (by omega) (by omega) (by omega), V_fl (t + 1) (by omega) i (by push_cast; omega) (by push_cast; omega) (by omega)]
    obtain ⟨q, hq, hqq⟩ : ∃ q, q < 4 ∧ (t - 15) % 4 = q := ⟨_, Nat.mod_lt _ (by norm_num), rfl⟩
    rw [show (t + 1 - 15) % 4 = (q + 1) % 4 by omega, hqq]
    interval_cases q <;> decide
  · rw [V_fl t ht (i - 1) (by omega) (by omega) (by omega), V_fl t ht i (by omega) (by omega) (by omega), V_er t ht (i + 1) 12 (by omega) (by norm_num), V_fl (t + 1) (by omega) i (by push_cast; omega) (by push_cast; omega) (by omega)]
    obtain ⟨q, hq, hqq⟩ : ∃ q, q < 4 ∧ (t - 15) % 4 = q := ⟨_, Nat.mod_lt _ (by norm_num), rfl⟩
    rw [show (t + 1 - 15) % 4 = (q + 1) % 4 by omega, hqq]
    interval_cases q <;> decide
  · rw [V_fl t ht (i - 1) (by omega) (by omega) (by omega), V_er t ht i 12 (by omega) (by norm_num), V_er t ht (i + 1) 11 (by omega) (by norm_num), V_fl (t + 1) (by omega) i (by push_cast; omega) (by push_cast; omega) (by omega)]
    obtain ⟨q, hq, hqq⟩ : ∃ q, q < 4 ∧ (t - 15) % 4 = q := ⟨_, Nat.mod_lt _ (by norm_num), rfl⟩
    rw [show (t + 1 - 15) % 4 = (q + 1) % 4 by omega, hqq]
    interval_cases q <;> decide
  · rw [V_er t ht (i - 1) 12 (by omega) (by norm_num), V_er t ht i 11 (by omega) (by norm_num), V_er t ht (i + 1) 10 (by omega) (by norm_num), V_er (t + 1) (by omega) i 12 (by push_cast; omega) (by norm_num)]
    obtain ⟨q, hq, hqq⟩ : ∃ q, q < 4 ∧ (t - 15) % 4 = q := ⟨_, Nat.mod_lt _ (by norm_num), rfl⟩
    rw [show (t + 1 - 15) % 4 = (q + 1) % 4 by omega, hqq]
    interval_cases q <;> decide
  · rw [V_er t ht (i - 1) 11 (by omega) (by norm_num), V_er t ht i 10 (by omega) (by norm_num), V_er t ht (i + 1) 9 (by omega) (by norm_num), V_er (t + 1) (by omega) i 11 (by push_cast; omega) (by norm_num)]
    obtain ⟨q, hq, hqq⟩ : ∃ q, q < 4 ∧ (t - 15) % 4 = q := ⟨_, Nat.mod_lt _ (by norm_num), rfl⟩
    rw [show (t + 1 - 15) % 4 = (q + 1) % 4 by omega, hqq]
    interval_cases q <;> decide
  · rw [V_er t ht (i - 1) 10 (by omega) (by norm_num), V_er t ht i 9 (by omega) (by norm_num), V_er t ht (i + 1) 8 (by omega) (by norm_num), V_er (t + 1) (by omega) i 10 (by push_cast; omega) (by norm_num)]
    obtain ⟨q, hq, hqq⟩ : ∃ q, q < 4 ∧ (t - 15) % 4 = q := ⟨_, Nat.mod_lt _ (by norm_num), rfl⟩
    rw [show (t + 1 - 15) % 4 = (q + 1) % 4 by omega, hqq]
    interval_cases q <;> decide
  · rw [V_er t ht (i - 1) 9 (by omega) (by norm_num), V_er t ht i 8 (by omega) (by norm_num), V_er t ht (i + 1) 7 (by omega) (by norm_num), V_er (t + 1) (by omega) i 9 (by push_cast; omega) (by norm_num)]
    obtain ⟨q, hq, hqq⟩ : ∃ q, q < 4 ∧ (t - 15) % 4 = q := ⟨_, Nat.mod_lt _ (by norm_num), rfl⟩
    rw [show (t + 1 - 15) % 4 = (q + 1) % 4 by omega, hqq]
    interval_cases q <;> decide
  · rw [V_er t ht (i - 1) 8 (by omega) (by norm_num), V_er t ht i 7 (by omega) (by norm_num), V_er t ht (i + 1) 6 (by omega) (by norm_num), V_er (t + 1) (by omega) i 8 (by push_cast; omega) (by norm_num)]
    obtain ⟨q, hq, hqq⟩ : ∃ q, q < 4 ∧ (t - 15) % 4 = q := ⟨_, Nat.mod_lt _ (by norm_num), rfl⟩
    rw [show (t + 1 - 15) % 4 = (q + 1) % 4 by omega, hqq]
    interval_cases q <;> decide
  · rw [V_er t ht (i - 1) 7 (by omega) (by norm_num), V_er t ht i 6 (by omega) (by norm_num), V_er t ht (i + 1) 5 (by omega) (by norm_num), V_er (t + 1) (by omega) i 7 (by push_cast; omega) (by norm_num)]
    obtain ⟨q, hq, hqq⟩ : ∃ q, q < 4 ∧ (t - 15) % 4 = q := ⟨_, Nat.mod_lt _ (by norm_num), rfl⟩
    rw [show (t + 1 - 15) % 4 = (q + 1) % 4 by omega, hqq]
    interval_cases q <;> decide
  · rw [V_er t ht (i - 1) 6 (by omega) (by norm_num), V_er t ht i 5 (by omega) (by norm_num), V_er t ht (i + 1) 4 (by omega) (by norm_num), V_er (t + 1) (by omega) i 6 (by push_cast; omega) (by norm_num)]
    obtain ⟨q, hq, hqq⟩ : ∃ q, q < 4 ∧ (t - 15) % 4 = q := ⟨_, Nat.mod_lt _ (by norm_num), rfl⟩
    rw [show (t + 1 - 15) % 4 = (q + 1) % 4 by omega, hqq]
    interval_cases q <;> decide
  · rw [V_er t ht (i - 1) 5 (by omega) (by norm_num), V_er t ht i 4 (by omega) (by norm_num), V_er t ht (i + 1) 3 (by omega) (by norm_num), V_er (t + 1) (by omega) i 5 (by push_cast; omega) (by norm_num)]
    obtain ⟨q, hq, hqq⟩ : ∃ q, q < 4 ∧ (t - 15) % 4 = q := ⟨_, Nat.mod_lt _ (by norm_num), rfl⟩
    rw [show (t + 1 - 15) % 4 = (q + 1) % 4 by omega, hqq]
    interval_cases q <;> decide
  · rw [V_er t ht (i - 1) 4 (by omega) (by norm_num), V_er t ht i 3 (by omega) (by norm_num), V_er t ht (i + 1) 2 (by omega) (by norm_num), V_er (t + 1) (by omega) i 4 (by push_cast; omega) (by norm_num)]
    obtain ⟨q, hq, hqq⟩ : ∃ q, q < 4 ∧ (t - 15) % 4 = q := ⟨_, Nat.mod_lt _ (by norm_num), rfl⟩
    rw [show (t + 1 - 15) % 4 = (q + 1) % 4 by omega, hqq]
    interval_cases q <;> decide
  · rw [V_er t ht (i - 1) 3 (by omega) (by norm_num), V_er t ht i 2 (by omega) (by norm_num), V_er t ht (i + 1) 1 (by omega) (by norm_num), V_er (t + 1) (by omega) i 3 (by push_cast; omega) (by norm_num)]
    obtain ⟨q, hq, hqq⟩ : ∃ q, q < 4 ∧ (t - 15) % 4 = q := ⟨_, Nat.mod_lt _ (by norm_num), rfl⟩
    rw [show (t + 1 - 15) % 4 = (q + 1) % 4 by omega, hqq]
    interval_cases q <;> decide
  · rw [V_er t ht (i - 1) 2 (by omega) (by norm_num), V_er t ht i 1 (by omega) (by norm_num), V_er t ht (i + 1) 0 (by omega) (by norm_num), V_er (t + 1) (by omega) i 2 (by push_cast; omega) (by norm_num)]
    obtain ⟨q, hq, hqq⟩ : ∃ q, q < 4 ∧ (t - 15) % 4 = q := ⟨_, Nat.mod_lt _ (by norm_num), rfl⟩
    rw [show (t + 1 - 15) % 4 = (q + 1) % 4 by omega, hqq]
    interval_cases q <;> decide
  · rw [V_er t ht (i - 1) 1 (by omega) (by norm_num), V_er t ht i 0 (by omega) (by norm_num), V_out t (i + 1) (by push_cast; omega), V_er (t + 1) (by omega) i 1 (by push_cast; omega) (by norm_num)]
    obtain ⟨q, hq, hqq⟩ : ∃ q, q < 4 ∧ (t - 15) % 4 = q := ⟨_, Nat.mod_lt _ (by norm_num), rfl⟩
    rw [show (t + 1 - 15) % 4 = (q + 1) % 4 by omega, hqq]
    interval_cases q <;> decide
  · rw [V_er t ht (i - 1) 0 (by omega) (by norm_num), V_out t i (by push_cast; omega), V_out t (i + 1) (by push_cast; omega), V_er (t + 1) (by omega) i 0 (by push_cast; omega) (by norm_num)]
    obtain ⟨q, hq, hqq⟩ : ∃ q, q < 4 ∧ (t - 15) % 4 = q := ⟨_, Nat.mod_lt _ (by norm_num), rfl⟩
    rw [show (t + 1 - 15) % 4 = (q + 1) % 4 by omega, hqq]
    interval_cases q <;> decide
  · rw [V_out t (i - 1) (by push_cast; omega), V_out t i (by push_cast; omega), V_out t (i + 1) (by push_cast; omega), V_out (t + 1) i (by push_cast; omega)]
    obtain ⟨q, hq, hqq⟩ : ∃ q, q < 4 ∧ (t - 15) % 4 = q := ⟨_, Nat.mod_lt _ (by norm_num), rfl⟩
    rw [show (t + 1 - 15) % 4 = (q + 1) % 4 by omega, hqq]
    interval_cases q <;> decide
  · rw [V_out t (i - 1) (by push_cast; omega), V_out t i (by push_cast; omega), V_out t (i + 1) (by push_cast; omega), V_out (t + 1) i (by push_cast; omega)]
    obtain ⟨q, hq, hqq⟩ : ∃ q, q < 4 ∧ (t - 15) % 4 = q := ⟨_, Nat.mod_lt _ (by norm_num), rfl⟩
    rw [show (t + 1 - 15) % 4 = (q + 1) % 4 by omega, hqq]
    interval_cases q <;> decide

lemma base_ok : (∀ j < 2 * W + 1, decode (stages.getD 15 default) ((j : ℤ) - W) = V 15 ((j : ℤ) - W)) ∧
    (stages.getD 15 default).1 = bgT.getD 0 false := by
  decide +kernel

lemma pattern (t : ℕ) (ht : 15 ≤ t) : ∀ i, cstate t i = V t i := by
  induction t, ht using Nat.le_induction with
  | base =>
    intro i
    rw [(certified 15 le_rfl).2 i]
    by_cases hw : -(W : ℤ) ≤ i ∧ i ≤ W
    · obtain ⟨j, hj, rfl⟩ := in_window i hw
      exact base_ok.1 j hj
    · unfold decode
      rw [if_neg hw, base_ok.2, V_out 15 i (by unfold W at hw; omega)]
  | succ t ht ih =>
    intro i
    show rule (cstate t (i - 1)) (cstate t i) (cstate t (i + 1)) = _
    rw [ih, ih, ih, stepV t ht i]

lemma sim_V (t : ℕ) (ht : t ≤ 15) : sim t = cstate t := funext fun i => ((certified t ht).2 i).symm


lemma state_eq_V (t : ℕ) (ht : 15 ≤ t) : cstate t = V t := funext (pattern t ht)

/-- The rows as computed: the certificate up to row 15, then `V`. -/
def rowOf (t : ℕ) : ℤ → Bool := if t ≤ 15 then sim t else V t

lemma state_eq (t : ℕ) : cstate t = rowOf t := by
  unfold rowOf
  split_ifs with h
  · exact (sim_V t h).symm
  · exact state_eq_V t (by omega)

def aSim (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (2 * n + 1), if rowOf n ((k : ℤ) - n) then 1 else 0

lemma a_eq (n : ℕ) : ca n = aSim n := by
  unfold ca aSim
  simp only [state_eq]

/-- The values a(0..39); the listed terms are among them (control). -/
lemma vals : ∀ n ≤ 39, ca n = ([1, 1, 3, 5, 6, 8, 7, 13, 6, 15, 8, 21, 6, 23, 8, 29, 6, 31, 8, 37, 6, 39, 8, 45, 6, 47, 8, 53, 6, 55, 8, 61, 6, 63, 8, 69, 6, 71, 8, 77] : List ℕ).getD n 0 := by
  intro n hn
  rw [a_eq n]
  revert n
  decide +kernel

lemma v0 : ca 0 = 1 := vals 0 (by norm_num)
lemma v1 : ca 1 = 1 := vals 1 (by norm_num)
lemma v2 : ca 2 = 3 := vals 2 (by norm_num)
lemma v3 : ca 3 = 5 := vals 3 (by norm_num)
lemma v4 : ca 4 = 6 := vals 4 (by norm_num)
lemma v5 : ca 5 = 8 := vals 5 (by norm_num)
lemma v6 : ca 6 = 7 := vals 6 (by norm_num)
lemma v7 : ca 7 = 13 := vals 7 (by norm_num)
lemma v8 : ca 8 = 6 := vals 8 (by norm_num)
lemma v9 : ca 9 = 15 := vals 9 (by norm_num)
lemma v10 : ca 10 = 8 := vals 10 (by norm_num)
lemma v11 : ca 11 = 21 := vals 11 (by norm_num)
lemma v12 : ca 12 = 6 := vals 12 (by norm_num)
lemma v13 : ca 13 = 23 := vals 13 (by norm_num)
lemma v14 : ca 14 = 8 := vals 14 (by norm_num)
lemma v15 : ca 15 = 29 := vals 15 (by norm_num)
lemma v16 : ca 16 = 6 := vals 16 (by norm_num)
lemma v17 : ca 17 = 31 := vals 17 (by norm_num)
lemma v18 : ca 18 = 8 := vals 18 (by norm_num)
lemma v19 : ca 19 = 37 := vals 19 (by norm_num)
lemma v20 : ca 20 = 6 := vals 20 (by norm_num)
lemma v21 : ca 21 = 39 := vals 21 (by norm_num)
lemma v22 : ca 22 = 8 := vals 22 (by norm_num)
lemma v23 : ca 23 = 45 := vals 23 (by norm_num)
lemma v24 : ca 24 = 6 := vals 24 (by norm_num)
lemma v25 : ca 25 = 47 := vals 25 (by norm_num)
lemma v26 : ca 26 = 8 := vals 26 (by norm_num)
lemma v27 : ca 27 = 53 := vals 27 (by norm_num)
lemma v28 : ca 28 = 6 := vals 28 (by norm_num)
lemma v29 : ca 29 = 55 := vals 29 (by norm_num)
lemma v30 : ca 30 = 8 := vals 30 (by norm_num)
lemma v31 : ca 31 = 61 := vals 31 (by norm_num)
lemma v32 : ca 32 = 6 := vals 32 (by norm_num)
lemma v33 : ca 33 = 63 := vals 33 (by norm_num)
lemma v34 : ca 34 = 8 := vals 34 (by norm_num)
lemma v35 : ca 35 = 69 := vals 35 (by norm_num)
lemma v36 : ca 36 = 6 := vals 36 (by norm_num)
lemma v37 : ca 37 = 71 := vals 37 (by norm_num)
lemma v38 : ca 38 = 8 := vals 38 (by norm_num)
lemma v39 : ca 39 = 77 := vals 39 (by norm_num)

/-- The number of ON cells among `-n..n` in row `n`. -/
def cnt1 (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (2 * n + 1), if cstate n ((k : ℤ) - n) then 1 else 0

set_option maxHeartbeats 4000000 in
lemma cnt_split (n : ℕ) (hn : 15 ≤ n) :
    cnt1 n = (∑ k ∈ Finset.range 13, if (elT.getD ((n - 15) % 4) 0).testBit k then 1 else 0) +
      (n - 13) * (if flT.getD ((n - 15) % 4) false then 1 else 0) +
      (∑ k ∈ Finset.range 1, if (coT.getD ((n - 15) % 4) 0).testBit k then 1 else 0) +
      (n - 13) * (if flT.getD ((n - 15) % 4) false then 1 else 0) +
      (∑ k ∈ Finset.range 13, if (erT.getD ((n - 15) % 4) 0).testBit (12 - k) then 1 else 0) := by
  unfold cnt1
  rw [state_eq_V n hn]
  rw [show 2 * n + 1 = 13 + (n - 13) + 1 + (n - 13) + 13 by omega]
  rw [Finset.sum_range_add, Finset.sum_range_add, Finset.sum_range_add, Finset.sum_range_add]
  congr 1
  congr 1
  congr 1
  congr 1
  · refine Finset.sum_congr rfl fun k hk => ?_
    have hk' := Finset.mem_range.mp hk
    rw [V_el n hn _ k (by omega) (by omega)]
  · rw [Finset.sum_congr rfl fun k hk => by
      rw [V_fl n hn _ (by have := Finset.mem_range.mp hk; push_cast; omega)
        (by have := Finset.mem_range.mp hk; push_cast; omega)
        (by have := Finset.mem_range.mp hk; push_cast; omega)]]
    simp
  · refine Finset.sum_congr rfl fun k hk => ?_
    have hk' := Finset.mem_range.mp hk
    rw [V_co n hn _ k (by push_cast; omega) (by omega)]
  · rw [Finset.sum_congr rfl fun k hk => by
      rw [V_fl n hn _ (by have := Finset.mem_range.mp hk; push_cast; omega)
        (by have := Finset.mem_range.mp hk; push_cast; omega)
        (by have := Finset.mem_range.mp hk; push_cast; omega)]]
    simp
  · refine Finset.sum_congr rfl fun k hk => ?_
    have hk' := Finset.mem_range.mp hk
    rw [V_er n hn _ (12 - k) (by push_cast; omega) (by omega)]


lemma cntn0 (n : ℕ) (h1 : 15 ≤ n) (h2 : n % 4 = 0) :
    (cnt1 n : ℚ) = 0 * (n : ℚ) + (6 : ℚ) := by
  rw [cnt_split n h1, show (n - 15) % 4 = 1 by omega]
  have e1 : ∑ k ∈ Finset.range 13, (if (elT.getD 1 0).testBit k then 1 else 0 : ℕ) = 0 := by decide
  have e2 : (if flT.getD 1 false then 1 else 0 : ℕ) = 0 := by decide
  have e3 : ∑ k ∈ Finset.range 1, (if (coT.getD 1 0).testBit k then 1 else 0 : ℕ) = 0 := by decide
  have e5 : ∑ k ∈ Finset.range 13, (if (erT.getD 1 0).testBit (12 - k) then 1 else 0 : ℕ) = 6 := by decide
  rw [e1, e2, e3, e5]
  push_cast [Nat.cast_sub (show 13 ≤ n by omega)]
  ring


lemma cfn0 (n : ℕ) (h1 : 15 ≤ n) (h2 : n % 4 = 0) :
    (ca n : ℚ) = 0 * (n : ℚ) + (6 : ℚ) := cntn0 n h1 h2


lemma cntn1 (n : ℕ) (h1 : 15 ≤ n) (h2 : n % 4 = 1) :
    (cnt1 n : ℚ) = 2 * (n : ℚ) + (-3 : ℚ) := by
  rw [cnt_split n h1, show (n - 15) % 4 = 2 by omega]
  have e1 : ∑ k ∈ Finset.range 13, (if (elT.getD 2 0).testBit k then 1 else 0 : ℕ) = 13 := by decide
  have e2 : (if flT.getD 2 false then 1 else 0 : ℕ) = 1 := by decide
  have e3 : ∑ k ∈ Finset.range 1, (if (coT.getD 2 0).testBit k then 1 else 0 : ℕ) = 1 := by decide
  have e5 : ∑ k ∈ Finset.range 13, (if (erT.getD 2 0).testBit (12 - k) then 1 else 0 : ℕ) = 9 := by decide
  rw [e1, e2, e3, e5]
  push_cast [Nat.cast_sub (show 13 ≤ n by omega)]
  ring


lemma cfn1 (n : ℕ) (h1 : 15 ≤ n) (h2 : n % 4 = 1) :
    (ca n : ℚ) = 2 * (n : ℚ) + (-3 : ℚ) := cntn1 n h1 h2


lemma cntn2 (n : ℕ) (h1 : 15 ≤ n) (h2 : n % 4 = 2) :
    (cnt1 n : ℚ) = 0 * (n : ℚ) + (8 : ℚ) := by
  rw [cnt_split n h1, show (n - 15) % 4 = 3 by omega]
  have e1 : ∑ k ∈ Finset.range 13, (if (elT.getD 3 0).testBit k then 1 else 0 : ℕ) = 0 := by decide
  have e2 : (if flT.getD 3 false then 1 else 0 : ℕ) = 0 := by decide
  have e3 : ∑ k ∈ Finset.range 1, (if (coT.getD 3 0).testBit k then 1 else 0 : ℕ) = 0 := by decide
  have e5 : ∑ k ∈ Finset.range 13, (if (erT.getD 3 0).testBit (12 - k) then 1 else 0 : ℕ) = 8 := by decide
  rw [e1, e2, e3, e5]
  push_cast [Nat.cast_sub (show 13 ≤ n by omega)]
  ring


lemma cfn2 (n : ℕ) (h1 : 15 ≤ n) (h2 : n % 4 = 2) :
    (ca n : ℚ) = 0 * (n : ℚ) + (8 : ℚ) := cntn2 n h1 h2


lemma cntn3 (n : ℕ) (h1 : 15 ≤ n) (h2 : n % 4 = 3) :
    (cnt1 n : ℚ) = 2 * (n : ℚ) + (-1 : ℚ) := by
  rw [cnt_split n h1, show (n - 15) % 4 = 0 by omega]
  have e1 : ∑ k ∈ Finset.range 13, (if (elT.getD 0 0).testBit k then 1 else 0 : ℕ) = 13 := by decide
  have e2 : (if flT.getD 0 false then 1 else 0 : ℕ) = 1 := by decide
  have e3 : ∑ k ∈ Finset.range 1, (if (coT.getD 0 0).testBit k then 1 else 0 : ℕ) = 1 := by decide
  have e5 : ∑ k ∈ Finset.range 13, (if (erT.getD 0 0).testBit (12 - k) then 1 else 0 : ℕ) = 11 := by decide
  rw [e1, e2, e3, e5]
  push_cast [Nat.cast_sub (show 13 ≤ n by omega)]
  ring


lemma cfn3 (n : ℕ) (h1 : 15 ≤ n) (h2 : n % 4 = 3) :
    (ca n : ℚ) = 2 * (n : ℚ) + (-1 : ℚ) := cntn3 n h1 h2


/-- a(n) = a(n-2)+a(n-4)-a(n-6) for n>12 -/
theorem recurrence0 (n : ℕ) (hn : 13 ≤ n) : (ca n : ℤ) = (((ca (n - 2) : ℤ) + (ca (n - 4) : ℤ)) - (ca (n - 6) : ℤ)) := by
  rcases Nat.lt_or_ge n 21 with hlt | hge
  · interval_cases n <;> norm_num [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16, v17, v18, v19, v20, v21] at *
  · suffices hq : (ca n : ℚ) = (((ca (n - 2) : ℚ) + (ca (n - 4) : ℚ)) - (ca (n - 6) : ℚ)) by exact_mod_cast hq
    rcases (by omega : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3) with hpar | hpar | hpar | hpar
    · obtain ⟨q, rfl⟩ : ∃ q, n = 24 + 4 * q := ⟨(n - 24) / 4, by omega⟩
      have c0 := cfn0 (24 + 4 * q) (by omega) (by omega)
      rw [show 24 + 4 * q - 2 = 22 + 4 * q by omega]
      have c2 := cfn2 (22 + 4 * q) (by omega) (by omega)
      rw [show 24 + 4 * q - 4 = 20 + 4 * q by omega]
      have c4 := cfn0 (20 + 4 * q) (by omega) (by omega)
      rw [show 24 + 4 * q - 6 = 18 + 4 * q by omega]
      have c6 := cfn2 (18 + 4 * q) (by omega) (by omega)
      try simp only [pow_add, pow_mul, neg_one_sq, one_pow, mul_one, one_mul, show ((-1 : ℚ)) ^ 4 = 1 by norm_num, show ((-1 : ℚ)) ^ 6 = 1 by norm_num, show ((-1 : ℚ)) ^ 12 = 1 by norm_num] at c0 c2 c4 c6 ⊢
      push_cast at c0 c2 c4 c6 ⊢
      linear_combination (1 / (1 : ℚ)) * c0 + (-((1 : ℚ)) / (1 : ℚ)) * c2 + (-((1 : ℚ)) / (1 : ℚ)) * c4 + (-((-1 : ℚ)) / (1 : ℚ)) * c6
    · obtain ⟨q, rfl⟩ : ∃ q, n = 21 + 4 * q := ⟨(n - 21) / 4, by omega⟩
      have c0 := cfn1 (21 + 4 * q) (by omega) (by omega)
      rw [show 21 + 4 * q - 2 = 19 + 4 * q by omega]
      have c2 := cfn3 (19 + 4 * q) (by omega) (by omega)
      rw [show 21 + 4 * q - 4 = 17 + 4 * q by omega]
      have c4 := cfn1 (17 + 4 * q) (by omega) (by omega)
      rw [show 21 + 4 * q - 6 = 15 + 4 * q by omega]
      have c6 := cfn3 (15 + 4 * q) (by omega) (by omega)
      try simp only [pow_add, pow_mul, neg_one_sq, one_pow, mul_one, one_mul, show ((-1 : ℚ)) ^ 4 = 1 by norm_num, show ((-1 : ℚ)) ^ 6 = 1 by norm_num, show ((-1 : ℚ)) ^ 12 = 1 by norm_num] at c0 c2 c4 c6 ⊢
      push_cast at c0 c2 c4 c6 ⊢
      linear_combination (1 / (1 : ℚ)) * c0 + (-((1 : ℚ)) / (1 : ℚ)) * c2 + (-((1 : ℚ)) / (1 : ℚ)) * c4 + (-((-1 : ℚ)) / (1 : ℚ)) * c6
    · obtain ⟨q, rfl⟩ : ∃ q, n = 22 + 4 * q := ⟨(n - 22) / 4, by omega⟩
      have c0 := cfn2 (22 + 4 * q) (by omega) (by omega)
      rw [show 22 + 4 * q - 2 = 20 + 4 * q by omega]
      have c2 := cfn0 (20 + 4 * q) (by omega) (by omega)
      rw [show 22 + 4 * q - 4 = 18 + 4 * q by omega]
      have c4 := cfn2 (18 + 4 * q) (by omega) (by omega)
      rw [show 22 + 4 * q - 6 = 16 + 4 * q by omega]
      have c6 := cfn0 (16 + 4 * q) (by omega) (by omega)
      try simp only [pow_add, pow_mul, neg_one_sq, one_pow, mul_one, one_mul, show ((-1 : ℚ)) ^ 4 = 1 by norm_num, show ((-1 : ℚ)) ^ 6 = 1 by norm_num, show ((-1 : ℚ)) ^ 12 = 1 by norm_num] at c0 c2 c4 c6 ⊢
      push_cast at c0 c2 c4 c6 ⊢
      linear_combination (1 / (1 : ℚ)) * c0 + (-((1 : ℚ)) / (1 : ℚ)) * c2 + (-((1 : ℚ)) / (1 : ℚ)) * c4 + (-((-1 : ℚ)) / (1 : ℚ)) * c6
    · obtain ⟨q, rfl⟩ : ∃ q, n = 23 + 4 * q := ⟨(n - 23) / 4, by omega⟩
      have c0 := cfn3 (23 + 4 * q) (by omega) (by omega)
      rw [show 23 + 4 * q - 2 = 21 + 4 * q by omega]
      have c2 := cfn1 (21 + 4 * q) (by omega) (by omega)
      rw [show 23 + 4 * q - 4 = 19 + 4 * q by omega]
      have c4 := cfn3 (19 + 4 * q) (by omega) (by omega)
      rw [show 23 + 4 * q - 6 = 17 + 4 * q by omega]
      have c6 := cfn1 (17 + 4 * q) (by omega) (by omega)
      try simp only [pow_add, pow_mul, neg_one_sq, one_pow, mul_one, one_mul, show ((-1 : ℚ)) ^ 4 = 1 by norm_num, show ((-1 : ℚ)) ^ 6 = 1 by norm_num, show ((-1 : ℚ)) ^ 12 = 1 by norm_num] at c0 c2 c4 c6 ⊢
      push_cast at c0 c2 c4 c6 ⊢
      linear_combination (1 / (1 : ℚ)) * c0 + (-((1 : ℚ)) / (1 : ℚ)) * c2 + (-((1 : ℚ)) / (1 : ℚ)) * c4 + (-((-1 : ℚ)) / (1 : ℚ)) * c6


lemma gfrec1 (n : ℕ) (hn : 13 ≤ n) : (ca n : ℚ) = ((1 : ℚ)) * (ca (n - 2) : ℚ) + ((1 : ℚ)) * (ca (n - 4) : ℚ) + ((-1 : ℚ)) * (ca (n - 6) : ℚ) := by
  rcases Nat.lt_or_ge n 21 with hlt | hge
  · interval_cases n <;> norm_num [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16, v17, v18, v19, v20, v21] at *
  · rcases (by omega : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3) with hpar | hpar | hpar | hpar
    · obtain ⟨q, rfl⟩ : ∃ q, n = 24 + 4 * q := ⟨(n - 24) / 4, by omega⟩
      have c0 := cfn0 (24 + 4 * q) (by omega) (by omega)
      rw [show 24 + 4 * q - 2 = 22 + 4 * q by omega]
      have c2 := cfn2 (22 + 4 * q) (by omega) (by omega)
      rw [show 24 + 4 * q - 4 = 20 + 4 * q by omega]
      have c4 := cfn0 (20 + 4 * q) (by omega) (by omega)
      rw [show 24 + 4 * q - 6 = 18 + 4 * q by omega]
      have c6 := cfn2 (18 + 4 * q) (by omega) (by omega)
      try simp only [pow_add, pow_mul, neg_one_sq, one_pow, mul_one, one_mul, show ((-1 : ℚ)) ^ 4 = 1 by norm_num, show ((-1 : ℚ)) ^ 6 = 1 by norm_num, show ((-1 : ℚ)) ^ 12 = 1 by norm_num] at c0 c2 c4 c6 ⊢
      push_cast at c0 c2 c4 c6 ⊢
      linear_combination (1 / (1 : ℚ)) * c0 + (-((1 : ℚ)) / (1 : ℚ)) * c2 + (-((1 : ℚ)) / (1 : ℚ)) * c4 + (-((-1 : ℚ)) / (1 : ℚ)) * c6
    · obtain ⟨q, rfl⟩ : ∃ q, n = 21 + 4 * q := ⟨(n - 21) / 4, by omega⟩
      have c0 := cfn1 (21 + 4 * q) (by omega) (by omega)
      rw [show 21 + 4 * q - 2 = 19 + 4 * q by omega]
      have c2 := cfn3 (19 + 4 * q) (by omega) (by omega)
      rw [show 21 + 4 * q - 4 = 17 + 4 * q by omega]
      have c4 := cfn1 (17 + 4 * q) (by omega) (by omega)
      rw [show 21 + 4 * q - 6 = 15 + 4 * q by omega]
      have c6 := cfn3 (15 + 4 * q) (by omega) (by omega)
      try simp only [pow_add, pow_mul, neg_one_sq, one_pow, mul_one, one_mul, show ((-1 : ℚ)) ^ 4 = 1 by norm_num, show ((-1 : ℚ)) ^ 6 = 1 by norm_num, show ((-1 : ℚ)) ^ 12 = 1 by norm_num] at c0 c2 c4 c6 ⊢
      push_cast at c0 c2 c4 c6 ⊢
      linear_combination (1 / (1 : ℚ)) * c0 + (-((1 : ℚ)) / (1 : ℚ)) * c2 + (-((1 : ℚ)) / (1 : ℚ)) * c4 + (-((-1 : ℚ)) / (1 : ℚ)) * c6
    · obtain ⟨q, rfl⟩ : ∃ q, n = 22 + 4 * q := ⟨(n - 22) / 4, by omega⟩
      have c0 := cfn2 (22 + 4 * q) (by omega) (by omega)
      rw [show 22 + 4 * q - 2 = 20 + 4 * q by omega]
      have c2 := cfn0 (20 + 4 * q) (by omega) (by omega)
      rw [show 22 + 4 * q - 4 = 18 + 4 * q by omega]
      have c4 := cfn2 (18 + 4 * q) (by omega) (by omega)
      rw [show 22 + 4 * q - 6 = 16 + 4 * q by omega]
      have c6 := cfn0 (16 + 4 * q) (by omega) (by omega)
      try simp only [pow_add, pow_mul, neg_one_sq, one_pow, mul_one, one_mul, show ((-1 : ℚ)) ^ 4 = 1 by norm_num, show ((-1 : ℚ)) ^ 6 = 1 by norm_num, show ((-1 : ℚ)) ^ 12 = 1 by norm_num] at c0 c2 c4 c6 ⊢
      push_cast at c0 c2 c4 c6 ⊢
      linear_combination (1 / (1 : ℚ)) * c0 + (-((1 : ℚ)) / (1 : ℚ)) * c2 + (-((1 : ℚ)) / (1 : ℚ)) * c4 + (-((-1 : ℚ)) / (1 : ℚ)) * c6
    · obtain ⟨q, rfl⟩ : ∃ q, n = 23 + 4 * q := ⟨(n - 23) / 4, by omega⟩
      have c0 := cfn3 (23 + 4 * q) (by omega) (by omega)
      rw [show 23 + 4 * q - 2 = 21 + 4 * q by omega]
      have c2 := cfn1 (21 + 4 * q) (by omega) (by omega)
      rw [show 23 + 4 * q - 4 = 19 + 4 * q by omega]
      have c4 := cfn3 (19 + 4 * q) (by omega) (by omega)
      rw [show 23 + 4 * q - 6 = 17 + 4 * q by omega]
      have c6 := cfn1 (17 + 4 * q) (by omega) (by omega)
      try simp only [pow_add, pow_mul, neg_one_sq, one_pow, mul_one, one_mul, show ((-1 : ℚ)) ^ 4 = 1 by norm_num, show ((-1 : ℚ)) ^ 6 = 1 by norm_num, show ((-1 : ℚ)) ^ 12 = 1 by norm_num] at c0 c2 c4 c6 ⊢
      push_cast at c0 c2 c4 c6 ⊢
      linear_combination (1 / (1 : ℚ)) * c0 + (-((1 : ℚ)) / (1 : ℚ)) * c2 + (-((1 : ℚ)) / (1 : ℚ)) * c4 + (-((-1 : ℚ)) / (1 : ℚ)) * c6

open PowerSeries in
/-- G.f.: (1+x+2*x^2+4*x^3+2*x^4+2*x^5-x^6+x^7-4*x^8-x^9+x^10+x^11-x^12) / ((1-x)^2*(1+x)^2*(1+x^2)) -/
theorem gf1 : PowerSeries.mk (fun n => (ca n : ℚ)) = ((1+X+2*X ^ 2+4*X ^ 3+2*X ^ 4+2*X ^ 5-X ^ 6+X ^ 7-4*X ^ 8-X ^ 9+X ^ 10+X ^ 11-X ^ 12)) * (((1-X) ^ 2*(1+X) ^ 2*(1+X ^ 2)))⁻¹ := by
  set G : ℚ⟦X⟧ := PowerSeries.mk (fun n => (ca n : ℚ))
  have hden : constantCoeff ((((1-X) ^ 2*(1+X) ^ 2*(1+X ^ 2))) : ℚ⟦X⟧) ≠ 0 := by simp
  have eQ : G * (((1-X) ^ 2*(1+X) ^ 2*(1+X ^ 2))) = C ((1 : ℚ)) * G + C ((-1 : ℚ)) * (G * X ^ 2) + C ((-1 : ℚ)) * (G * X ^ 4) + C ((1 : ℚ)) * (G * X ^ 6) := by
    (try simp only [map_neg, map_ofNat, map_one, map_div₀, map_natCast]) <;> ring
  have eP : (((1+X+2*X ^ 2+4*X ^ 3+2*X ^ 4+2*X ^ 5-X ^ 6+X ^ 7-4*X ^ 8-X ^ 9+X ^ 10+X ^ 11-X ^ 12)) : ℚ⟦X⟧) = C ((1 : ℚ)) + C ((1 : ℚ)) * X ^ 1 + C ((2 : ℚ)) * X ^ 2 + C ((4 : ℚ)) * X ^ 3 + C ((2 : ℚ)) * X ^ 4 + C ((2 : ℚ)) * X ^ 5 + C ((-1 : ℚ)) * X ^ 6 + C ((1 : ℚ)) * X ^ 7 + C ((-4 : ℚ)) * X ^ 8 + C ((-1 : ℚ)) * X ^ 9 + C ((1 : ℚ)) * X ^ 10 + C ((1 : ℚ)) * X ^ 11 + C ((-1 : ℚ)) * X ^ 12 := by
    (try simp only [map_neg, map_ofNat, map_one, map_div₀, map_natCast]) <;> ring
  have key : G * (((1-X) ^ 2*(1+X) ^ 2*(1+X ^ 2))) = (1+X+2*X ^ 2+4*X ^ 3+2*X ^ 4+2*X ^ 5-X ^ 6+X ^ 7-4*X ^ 8-X ^ 9+X ^ 10+X ^ 11-X ^ 12) := by
    rw [eQ, eP]
    ext n
    simp only [map_add, map_sub, coeff_C_mul, coeff_mul_X_pow', coeff_X_pow, G, coeff_mk, coeff_C]
    rcases Nat.lt_or_ge n 13 with hn | hn
    · interval_cases n <;> norm_num [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16, v17, v18, v19, v20, v21]
    · simp only [show 1 ≤ n by omega, show 2 ≤ n by omega, show 3 ≤ n by omega, show 4 ≤ n by omega, show 5 ≤ n by omega, show 6 ≤ n by omega, show 7 ≤ n by omega, show 8 ≤ n by omega, show 9 ≤ n by omega, show 10 ≤ n by omega, show 11 ≤ n by omega, show 12 ≤ n by omega, show n ≠ 0 by omega, show n ≠ 1 by omega, show n ≠ 2 by omega, show n ≠ 3 by omega, show n ≠ 4 by omega, show n ≠ 5 by omega, show n ≠ 6 by omega, show n ≠ 7 by omega, show n ≠ 8 by omega, show n ≠ 9 by omega, show n ≠ 10 by omega, show n ≠ 11 by omega, show n ≠ 12 by omega, show n - 1 ≠ 0 by omega, show n - 2 ≠ 0 by omega, show n - 3 ≠ 0 by omega, show n - 4 ≠ 0 by omega, show n - 5 ≠ 0 by omega, show n - 6 ≠ 0 by omega, show n - 7 ≠ 0 by omega, show n - 8 ≠ 0 by omega, show n - 9 ≠ 0 by omega, show n - 10 ≠ 0 by omega, show n - 11 ≠ 0 by omega, show n - 12 ≠ 0 by omega, if_true, if_false, ↓reduceIte, ne_eq, not_false_eq_true]
      have hr := gfrec1 n hn
      linear_combination ((1 : ℚ)) * hr
  rw [← key, mul_assoc, PowerSeries.mul_inv_cancel _ hden, mul_one]


open PowerSeries in
/-- All the proved formula lines of the entry, together. -/
theorem formulas :
    (∀ n : ℕ, 13 ≤ n → (ca n : ℤ) = (((ca (n - 2) : ℤ) + (ca (n - 4) : ℤ)) - (ca (n - 6) : ℤ))) ∧
    (PowerSeries.mk (fun n => (ca n : ℚ)) = ((1+X+2*X ^ 2+4*X ^ 3+2*X ^ 4+2*X ^ 5-X ^ 6+X ^ 7-4*X ^ 8-X ^ 9+X ^ 10+X ^ 11-X ^ 12)) * (((1-X) ^ 2*(1+X) ^ 2*(1+X ^ 2)))⁻¹) :=
  ⟨recurrence0, gf1⟩


/-! ## The statement's definitions and the bridge -/

open PowerSeries






theorem rule_eq (l c r : Bool) :
    rule l c r = Nat.testBit 107 (4 * l.toNat + 2 * c.toNat + r.toNat) := by
  cases l <;> cases c <;> cases r <;> rfl

theorem cstate_eq (t : ℕ) : cstate t = state 107 t := by
  induction t with
  | zero => funext i; rfl
  | succ t ih =>
    funext i
    show rule (cstate t (i - 1)) (cstate t i) (cstate t (i + 1)) = step 107 (state 107 t) i
    rw [ih, rule_eq]
    rfl

theorem row_eq (n : ℕ) :
    onCount (state 107 n) n = ∑ k ∈ Finset.range (2 * n + 1), if cstate n ((k : ℤ) - n) then 1 else 0 := by
  rw [onCount, ← cstate_eq]
  conv_lhs => rw [← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' := Finset.mem_range.mp hk
  rw [show ((n : ℤ) - ((2 * n + 1 - 1 - k : ℕ) : ℤ)) = (k : ℤ) - n by omega]
  cases cstate n ((k : ℤ) - n) <;> simp

theorem a_eq_ca : a = ca := by
  funext n
  rw [a, ca, row_eq]

theorem controls : ∀ n ≤ 39, a n = ([1, 1, 3, 5, 6, 8, 7, 13, 6, 15, 8, 21, 6, 23, 8, 29, 6, 31, 8, 37, 6, 39, 8, 45, 6, 47, 8, 53, 6, 55, 8, 61, 6, 63, 8, 69, 6, 71, 8, 77] : List ℕ).getD n 0 := by
  rw [a_eq_ca]
  exact vals

/-- The site's problem, as stated in `main`. -/
theorem conj :
    (∀ n : ℕ, 12 < n → (a n : ℤ) = a (n - 2) + a (n - 4) - a (n - 6)) ∧
    A = (1 + X + 2 * X ^ 2 + 4 * X ^ 3 + 2 * X ^ 4 + 2 * X ^ 5 - X ^ 6 + X ^ 7 - 4 * X ^ 8 - X ^ 9 + X ^ 10 + X ^ 11 - X ^ 12) *
      ((1 - X) ^ 2 * (1 + X) ^ 2 * (1 + X ^ 2))⁻¹ := by
  rw [show A = PowerSeries.mk (fun n => (a n : ℚ)) from rfl, a_eq_ca]
  exact ⟨fun n hn => (recurrence0 n (by omega)).trans (by ring),
    gf1⟩

end OMA.S_oeis_a267158

theorem OMA.solution : type_of% @OMA.S_oeis_a267158.main :=
  OMA.S_oeis_a267158.conj
