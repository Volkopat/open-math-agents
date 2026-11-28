import OMAStatements.S_oeis_a267360

namespace OMA.S_oeis_a267360


/-- Rule 125 as a local map: the new state of a cell from (left, center, right). -/
def rule (l c r : Bool) : Bool := (125 : ℕ).testBit ((cond l 4 0) + (cond c 2 0) + (cond r 1 0))

/-- The configuration at time `t`, started from the single ON cell at 0. -/
def cstate : ℕ → ℤ → Bool
  | 0, i => decide (i = 0)
  | t + 1, i => rule (cstate t (i - 1)) (cstate t i) (cstate t (i + 1))


/-- A267360(n): row `n`, cells `-n..n` (leftmost first), read as a binary number. -/
def ca (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (2 * n + 1), if cstate n ((k : ℤ) - n) then 2 ^ (2 * n - k) else 0


/-! ## A finite certificate: rows `0..9` on the window `[-10, 10]` -/

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

def W : ℕ := 10

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

/-- The rows `0..9`, computed outside Lean and checked cell by cell below. -/
def stages : List (Bool × ℕ) :=
  [(false, 1024),
    (true, 2096639),
    (false, 1792),
    (true, 2096511),
    (false, 1984),
    (true, 2096223),
    (false, 1520),
    (true, 2096919),
    (false, 380),
    (true, 2097093)]

lemma stages_ok : initOK (stages.getD 0 default) = true ∧
    ∀ t < 9, stepOK (stages.getD t default) (stages.getD (t + 1) default) = true := by
  decide +kernel

lemma certified (t : ℕ) (ht : t ≤ 9) :
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

/-! ## The regime from row 9 on -/

def bgT : List Bool := [true, false]
def flT : List Bool := [true, false]
/-- Bit `j` of the left edge block: cell `-t + j`. -/
def elT : List ℕ := [98, 95]
/-- Bit `j` of the right edge block: cell `t - j`. -/
def erT : List ℕ := [127, 0]
/-- Bit `m` of the center block: cell `m - 0`. -/
def coT : List ℕ := [1, 0]

def V (t : ℕ) (i : ℤ) : Bool :=
  if i < -(t : ℤ) ∨ (t : ℤ) < i then bgT.getD ((t - 9) % 2) false
  else if i + t ≤ 6 then (elT.getD ((t - 9) % 2) 0).testBit (i + t).toNat
  else if (t : ℤ) - i ≤ 6 then (erT.getD ((t - 9) % 2) 0).testBit ((t : ℤ) - i).toNat
  else if -(0 : ℤ) ≤ i ∧ i ≤ 0 then (coT.getD ((t - 9) % 2) 0).testBit (i + 0).toNat
  else flT.getD ((t - 9) % 2) false

lemma V_out (t : ℕ) (i : ℤ) (h : i < -(t : ℤ) ∨ (t : ℤ) < i) :
    V t i = bgT.getD ((t - 9) % 2) false := by
  unfold V; rw [if_pos h]

lemma V_el (t : ℕ) (ht : 9 ≤ t) (i : ℤ) (j : ℕ) (hj : i + t = j) (hjA : j ≤ 6) :
    V t i = (elT.getD ((t - 9) % 2) 0).testBit j := by
  unfold V
  rw [if_neg (by omega), if_pos (by omega)]
  congr 1
  omega

lemma V_er (t : ℕ) (ht : 9 ≤ t) (i : ℤ) (j : ℕ) (hj : (t : ℤ) - i = j) (hjA : j ≤ 6) :
    V t i = (erT.getD ((t - 9) % 2) 0).testBit j := by
  unfold V
  rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)]
  congr 1
  omega

lemma V_co (t : ℕ) (ht : 9 ≤ t) (i : ℤ) (m : ℕ) (hm : i + 0 = m) (hmK : m ≤ 2 * 0) :
    V t i = (coT.getD ((t - 9) % 2) 0).testBit m := by
  unfold V
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]
  congr 1
  omega

lemma V_fl (t : ℕ) (ht : 9 ≤ t) (i : ℤ) (h1 : (6 : ℤ) < i + t) (h2 : (6 : ℤ) < (t : ℤ) - i)
    (h3 : i < -(0 : ℤ) ∨ (0 : ℤ) < i) : V t i = flT.getD ((t - 9) % 2) false := by
  unfold V
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]


set_option maxHeartbeats 4000000 in
lemma stepV (t : ℕ) (ht : 9 ≤ t) (i : ℤ) :
    rule (V t (i - 1)) (V t i) (V t (i + 1)) = V (t + 1) i := by
  rcases (by omega : (i ≤ -(t : ℤ) - 3) ∨ (i = -(t : ℤ) - 2) ∨ (i + t + 1 = 0) ∨ (i + t + 1 = 1) ∨ (i + t + 1 = 2) ∨ (i + t + 1 = 3) ∨ (i + t + 1 = 4) ∨ (i + t + 1 = 5) ∨ (i + t + 1 = 6) ∨ (i + t + 1 = 7) ∨ (i + t + 1 = 8) ∨ (8 < i + t + 1 ∧ i < -0 - 1) ∨ (i = -1) ∨ (i = 0) ∨ (i = 1) ∨ (0 + 1 < i ∧ 8 < (t : ℤ) + 1 - i) ∨ ((t : ℤ) + 1 - i = 8) ∨ ((t : ℤ) + 1 - i = 7) ∨ ((t : ℤ) + 1 - i = 6) ∨ ((t : ℤ) + 1 - i = 5) ∨ ((t : ℤ) + 1 - i = 4) ∨ ((t : ℤ) + 1 - i = 3) ∨ ((t : ℤ) + 1 - i = 2) ∨ ((t : ℤ) + 1 - i = 1) ∨ ((t : ℤ) + 1 - i = 0) ∨ (i = (t : ℤ) + 2) ∨ ((t : ℤ) + 3 ≤ i)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · rw [V_out t (i - 1) (by push_cast; omega), V_out t i (by push_cast; omega), V_out t (i + 1) (by push_cast; omega), V_out (t + 1) i (by push_cast; omega)]
    obtain ⟨q, hq, hqq⟩ : ∃ q, q < 2 ∧ (t - 9) % 2 = q := ⟨_, Nat.mod_lt _ (by norm_num), rfl⟩
    rw [show (t + 1 - 9) % 2 = (q + 1) % 2 by omega, hqq]
    interval_cases q <;> decide
  · rw [V_out t (i - 1) (by push_cast; omega), V_out t i (by push_cast; omega), V_out t (i + 1) (by push_cast; omega), V_out (t + 1) i (by push_cast; omega)]
    obtain ⟨q, hq, hqq⟩ : ∃ q, q < 2 ∧ (t - 9) % 2 = q := ⟨_, Nat.mod_lt _ (by norm_num), rfl⟩
    rw [show (t + 1 - 9) % 2 = (q + 1) % 2 by omega, hqq]
    interval_cases q <;> decide
  · rw [V_out t (i - 1) (by push_cast; omega), V_out t i (by push_cast; omega), V_el t ht (i + 1) 0 (by omega) (by norm_num), V_el (t + 1) (by omega) i 0 (by push_cast; omega) (by norm_num)]
    obtain ⟨q, hq, hqq⟩ : ∃ q, q < 2 ∧ (t - 9) % 2 = q := ⟨_, Nat.mod_lt _ (by norm_num), rfl⟩
    rw [show (t + 1 - 9) % 2 = (q + 1) % 2 by omega, hqq]
    interval_cases q <;> decide
  · rw [V_out t (i - 1) (by push_cast; omega), V_el t ht i 0 (by omega) (by norm_num), V_el t ht (i + 1) 1 (by omega) (by norm_num), V_el (t + 1) (by omega) i 1 (by push_cast; omega) (by norm_num)]
    obtain ⟨q, hq, hqq⟩ : ∃ q, q < 2 ∧ (t - 9) % 2 = q := ⟨_, Nat.mod_lt _ (by norm_num), rfl⟩
    rw [show (t + 1 - 9) % 2 = (q + 1) % 2 by omega, hqq]
    interval_cases q <;> decide
  · rw [V_el t ht (i - 1) 0 (by omega) (by norm_num), V_el t ht i 1 (by omega) (by norm_num), V_el t ht (i + 1) 2 (by omega) (by norm_num), V_el (t + 1) (by omega) i 2 (by push_cast; omega) (by norm_num)]
    obtain ⟨q, hq, hqq⟩ : ∃ q, q < 2 ∧ (t - 9) % 2 = q := ⟨_, Nat.mod_lt _ (by norm_num), rfl⟩
    rw [show (t + 1 - 9) % 2 = (q + 1) % 2 by omega, hqq]
    interval_cases q <;> decide
  · rw [V_el t ht (i - 1) 1 (by omega) (by norm_num), V_el t ht i 2 (by omega) (by norm_num), V_el t ht (i + 1) 3 (by omega) (by norm_num), V_el (t + 1) (by omega) i 3 (by push_cast; omega) (by norm_num)]
    obtain ⟨q, hq, hqq⟩ : ∃ q, q < 2 ∧ (t - 9) % 2 = q := ⟨_, Nat.mod_lt _ (by norm_num), rfl⟩
    rw [show (t + 1 - 9) % 2 = (q + 1) % 2 by omega, hqq]
    interval_cases q <;> decide
  · rw [V_el t ht (i - 1) 2 (by omega) (by norm_num), V_el t ht i 3 (by omega) (by norm_num), V_el t ht (i + 1) 4 (by omega) (by norm_num), V_el (t + 1) (by omega) i 4 (by push_cast; omega) (by norm_num)]
    obtain ⟨q, hq, hqq⟩ : ∃ q, q < 2 ∧ (t - 9) % 2 = q := ⟨_, Nat.mod_lt _ (by norm_num), rfl⟩
    rw [show (t + 1 - 9) % 2 = (q + 1) % 2 by omega, hqq]
    interval_cases q <;> decide
  · rw [V_el t ht (i - 1) 3 (by omega) (by norm_num), V_el t ht i 4 (by omega) (by norm_num), V_el t ht (i + 1) 5 (by omega) (by norm_num), V_el (t + 1) (by omega) i 5 (by push_cast; omega) (by norm_num)]
    obtain ⟨q, hq, hqq⟩ : ∃ q, q < 2 ∧ (t - 9) % 2 = q := ⟨_, Nat.mod_lt _ (by norm_num), rfl⟩
    rw [show (t + 1 - 9) % 2 = (q + 1) % 2 by omega, hqq]
    interval_cases q <;> decide
  · rw [V_el t ht (i - 1) 4 (by omega) (by norm_num), V_el t ht i 5 (by omega) (by norm_num), V_el t ht (i + 1) 6 (by omega) (by norm_num), V_el (t + 1) (by omega) i 6 (by push_cast; omega) (by norm_num)]
    obtain ⟨q, hq, hqq⟩ : ∃ q, q < 2 ∧ (t - 9) % 2 = q := ⟨_, Nat.mod_lt _ (by norm_num), rfl⟩
    rw [show (t + 1 - 9) % 2 = (q + 1) % 2 by omega, hqq]
    interval_cases q <;> decide
  · rw [V_el t ht (i - 1) 5 (by omega) (by norm_num), V_el t ht i 6 (by omega) (by norm_num), V_fl t ht (i + 1) (by omega) (by omega) (by omega), V_fl (t + 1) (by omega) i (by push_cast; omega) (by push_cast; omega) (by omega)]
    obtain ⟨q, hq, hqq⟩ : ∃ q, q < 2 ∧ (t - 9) % 2 = q := ⟨_, Nat.mod_lt _ (by norm_num), rfl⟩
    rw [show (t + 1 - 9) % 2 = (q + 1) % 2 by omega, hqq]
    interval_cases q <;> decide
  · rw [V_el t ht (i - 1) 6 (by omega) (by norm_num), V_fl t ht i (by omega) (by omega) (by omega), V_fl t ht (i + 1) (by omega) (by omega) (by omega), V_fl (t + 1) (by omega) i (by push_cast; omega) (by push_cast; omega) (by omega)]
    obtain ⟨q, hq, hqq⟩ : ∃ q, q < 2 ∧ (t - 9) % 2 = q := ⟨_, Nat.mod_lt _ (by norm_num), rfl⟩
    rw [show (t + 1 - 9) % 2 = (q + 1) % 2 by omega, hqq]
    interval_cases q <;> decide
  · rw [V_fl t ht (i - 1) (by omega) (by omega) (by omega), V_fl t ht i (by omega) (by omega) (by omega), V_fl t ht (i + 1) (by omega) (by omega) (by omega), V_fl (t + 1) (by omega) i (by push_cast; omega) (by push_cast; omega) (by omega)]
    obtain ⟨q, hq, hqq⟩ : ∃ q, q < 2 ∧ (t - 9) % 2 = q := ⟨_, Nat.mod_lt _ (by norm_num), rfl⟩
    rw [show (t + 1 - 9) % 2 = (q + 1) % 2 by omega, hqq]
    interval_cases q <;> decide
  · rw [V_fl t ht (i - 1) (by omega) (by omega) (by omega), V_fl t ht i (by omega) (by omega) (by omega), V_co t ht (i + 1) 0 (by omega) (by norm_num), V_fl (t + 1) (by omega) i (by push_cast; omega) (by push_cast; omega) (by omega)]
    obtain ⟨q, hq, hqq⟩ : ∃ q, q < 2 ∧ (t - 9) % 2 = q := ⟨_, Nat.mod_lt _ (by norm_num), rfl⟩
    rw [show (t + 1 - 9) % 2 = (q + 1) % 2 by omega, hqq]
    interval_cases q <;> decide
  · rw [V_fl t ht (i - 1) (by omega) (by omega) (by omega), V_co t ht i 0 (by omega) (by norm_num), V_fl t ht (i + 1) (by omega) (by omega) (by omega), V_co (t + 1) (by omega) i 0 (by omega) (by norm_num)]
    obtain ⟨q, hq, hqq⟩ : ∃ q, q < 2 ∧ (t - 9) % 2 = q := ⟨_, Nat.mod_lt _ (by norm_num), rfl⟩
    rw [show (t + 1 - 9) % 2 = (q + 1) % 2 by omega, hqq]
    interval_cases q <;> decide
  · rw [V_co t ht (i - 1) 0 (by omega) (by norm_num), V_fl t ht i (by omega) (by omega) (by omega), V_fl t ht (i + 1) (by omega) (by omega) (by omega), V_fl (t + 1) (by omega) i (by push_cast; omega) (by push_cast; omega) (by omega)]
    obtain ⟨q, hq, hqq⟩ : ∃ q, q < 2 ∧ (t - 9) % 2 = q := ⟨_, Nat.mod_lt _ (by norm_num), rfl⟩
    rw [show (t + 1 - 9) % 2 = (q + 1) % 2 by omega, hqq]
    interval_cases q <;> decide
  · rw [V_fl t ht (i - 1) (by omega) (by omega) (by omega), V_fl t ht i (by omega) (by omega) (by omega), V_fl t ht (i + 1) (by omega) (by omega) (by omega), V_fl (t + 1) (by omega) i (by push_cast; omega) (by push_cast; omega) (by omega)]
    obtain ⟨q, hq, hqq⟩ : ∃ q, q < 2 ∧ (t - 9) % 2 = q := ⟨_, Nat.mod_lt _ (by norm_num), rfl⟩
    rw [show (t + 1 - 9) % 2 = (q + 1) % 2 by omega, hqq]
    interval_cases q <;> decide
  · rw [V_fl t ht (i - 1) (by omega) (by omega) (by omega), V_fl t ht i (by omega) (by omega) (by omega), V_er t ht (i + 1) 6 (by omega) (by norm_num), V_fl (t + 1) (by omega) i (by push_cast; omega) (by push_cast; omega) (by omega)]
    obtain ⟨q, hq, hqq⟩ : ∃ q, q < 2 ∧ (t - 9) % 2 = q := ⟨_, Nat.mod_lt _ (by norm_num), rfl⟩
    rw [show (t + 1 - 9) % 2 = (q + 1) % 2 by omega, hqq]
    interval_cases q <;> decide
  · rw [V_fl t ht (i - 1) (by omega) (by omega) (by omega), V_er t ht i 6 (by omega) (by norm_num), V_er t ht (i + 1) 5 (by omega) (by norm_num), V_fl (t + 1) (by omega) i (by push_cast; omega) (by push_cast; omega) (by omega)]
    obtain ⟨q, hq, hqq⟩ : ∃ q, q < 2 ∧ (t - 9) % 2 = q := ⟨_, Nat.mod_lt _ (by norm_num), rfl⟩
    rw [show (t + 1 - 9) % 2 = (q + 1) % 2 by omega, hqq]
    interval_cases q <;> decide
  · rw [V_er t ht (i - 1) 6 (by omega) (by norm_num), V_er t ht i 5 (by omega) (by norm_num), V_er t ht (i + 1) 4 (by omega) (by norm_num), V_er (t + 1) (by omega) i 6 (by push_cast; omega) (by norm_num)]
    obtain ⟨q, hq, hqq⟩ : ∃ q, q < 2 ∧ (t - 9) % 2 = q := ⟨_, Nat.mod_lt _ (by norm_num), rfl⟩
    rw [show (t + 1 - 9) % 2 = (q + 1) % 2 by omega, hqq]
    interval_cases q <;> decide
  · rw [V_er t ht (i - 1) 5 (by omega) (by norm_num), V_er t ht i 4 (by omega) (by norm_num), V_er t ht (i + 1) 3 (by omega) (by norm_num), V_er (t + 1) (by omega) i 5 (by push_cast; omega) (by norm_num)]
    obtain ⟨q, hq, hqq⟩ : ∃ q, q < 2 ∧ (t - 9) % 2 = q := ⟨_, Nat.mod_lt _ (by norm_num), rfl⟩
    rw [show (t + 1 - 9) % 2 = (q + 1) % 2 by omega, hqq]
    interval_cases q <;> decide
  · rw [V_er t ht (i - 1) 4 (by omega) (by norm_num), V_er t ht i 3 (by omega) (by norm_num), V_er t ht (i + 1) 2 (by omega) (by norm_num), V_er (t + 1) (by omega) i 4 (by push_cast; omega) (by norm_num)]
    obtain ⟨q, hq, hqq⟩ : ∃ q, q < 2 ∧ (t - 9) % 2 = q := ⟨_, Nat.mod_lt _ (by norm_num), rfl⟩
    rw [show (t + 1 - 9) % 2 = (q + 1) % 2 by omega, hqq]
    interval_cases q <;> decide
  · rw [V_er t ht (i - 1) 3 (by omega) (by norm_num), V_er t ht i 2 (by omega) (by norm_num), V_er t ht (i + 1) 1 (by omega) (by norm_num), V_er (t + 1) (by omega) i 3 (by push_cast; omega) (by norm_num)]
    obtain ⟨q, hq, hqq⟩ : ∃ q, q < 2 ∧ (t - 9) % 2 = q := ⟨_, Nat.mod_lt _ (by norm_num), rfl⟩
    rw [show (t + 1 - 9) % 2 = (q + 1) % 2 by omega, hqq]
    interval_cases q <;> decide
  · rw [V_er t ht (i - 1) 2 (by omega) (by norm_num), V_er t ht i 1 (by omega) (by norm_num), V_er t ht (i + 1) 0 (by omega) (by norm_num), V_er (t + 1) (by omega) i 2 (by push_cast; omega) (by norm_num)]
    obtain ⟨q, hq, hqq⟩ : ∃ q, q < 2 ∧ (t - 9) % 2 = q := ⟨_, Nat.mod_lt _ (by norm_num), rfl⟩
    rw [show (t + 1 - 9) % 2 = (q + 1) % 2 by omega, hqq]
    interval_cases q <;> decide
  · rw [V_er t ht (i - 1) 1 (by omega) (by norm_num), V_er t ht i 0 (by omega) (by norm_num), V_out t (i + 1) (by push_cast; omega), V_er (t + 1) (by omega) i 1 (by push_cast; omega) (by norm_num)]
    obtain ⟨q, hq, hqq⟩ : ∃ q, q < 2 ∧ (t - 9) % 2 = q := ⟨_, Nat.mod_lt _ (by norm_num), rfl⟩
    rw [show (t + 1 - 9) % 2 = (q + 1) % 2 by omega, hqq]
    interval_cases q <;> decide
  · rw [V_er t ht (i - 1) 0 (by omega) (by norm_num), V_out t i (by push_cast; omega), V_out t (i + 1) (by push_cast; omega), V_er (t + 1) (by omega) i 0 (by push_cast; omega) (by norm_num)]
    obtain ⟨q, hq, hqq⟩ : ∃ q, q < 2 ∧ (t - 9) % 2 = q := ⟨_, Nat.mod_lt _ (by norm_num), rfl⟩
    rw [show (t + 1 - 9) % 2 = (q + 1) % 2 by omega, hqq]
    interval_cases q <;> decide
  · rw [V_out t (i - 1) (by push_cast; omega), V_out t i (by push_cast; omega), V_out t (i + 1) (by push_cast; omega), V_out (t + 1) i (by push_cast; omega)]
    obtain ⟨q, hq, hqq⟩ : ∃ q, q < 2 ∧ (t - 9) % 2 = q := ⟨_, Nat.mod_lt _ (by norm_num), rfl⟩
    rw [show (t + 1 - 9) % 2 = (q + 1) % 2 by omega, hqq]
    interval_cases q <;> decide
  · rw [V_out t (i - 1) (by push_cast; omega), V_out t i (by push_cast; omega), V_out t (i + 1) (by push_cast; omega), V_out (t + 1) i (by push_cast; omega)]
    obtain ⟨q, hq, hqq⟩ : ∃ q, q < 2 ∧ (t - 9) % 2 = q := ⟨_, Nat.mod_lt _ (by norm_num), rfl⟩
    rw [show (t + 1 - 9) % 2 = (q + 1) % 2 by omega, hqq]
    interval_cases q <;> decide

lemma base_ok : (∀ j < 2 * W + 1, decode (stages.getD 9 default) ((j : ℤ) - W) = V 9 ((j : ℤ) - W)) ∧
    (stages.getD 9 default).1 = bgT.getD 0 false := by
  decide +kernel

lemma pattern (t : ℕ) (ht : 9 ≤ t) : ∀ i, cstate t i = V t i := by
  induction t, ht using Nat.le_induction with
  | base =>
    intro i
    rw [(certified 9 le_rfl).2 i]
    by_cases hw : -(W : ℤ) ≤ i ∧ i ≤ W
    · obtain ⟨j, hj, rfl⟩ := in_window i hw
      exact base_ok.1 j hj
    · unfold decode
      rw [if_neg hw, base_ok.2, V_out 9 i (by unfold W at hw; omega)]
  | succ t ht ih =>
    intro i
    show rule (cstate t (i - 1)) (cstate t i) (cstate t (i + 1)) = _
    rw [ih, ih, ih, stepV t ht i]

lemma sim_V (t : ℕ) (ht : t ≤ 9) : sim t = cstate t := funext fun i => ((certified t ht).2 i).symm


lemma state_eq_V (t : ℕ) (ht : 9 ≤ t) : cstate t = V t := funext (pattern t ht)

/-- The rows as computed: the certificate up to row 9, then `V`. -/
def rowOf (t : ℕ) : ℤ → Bool := if t ≤ 9 then sim t else V t

lemma state_eq (t : ℕ) : cstate t = rowOf t := by
  unfold rowOf
  split_ifs with h
  · exact (sim_V t h).symm
  · exact state_eq_V t (by omega)

def aSim (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (2 * n + 1), if rowOf n ((k : ℤ) - n) then 2 ^ (2 * n - k) else 0

lemma a_eq (n : ℕ) : ca n = aSim n := by
  unfold ca aSim
  simp only [state_eq]

/-- The values a(0..27); the listed terms are among them (control). -/
lemma vals : ∀ n ≤ 27, ca n = ([1, 3, 28, 47, 496, 575, 8000, 9215, 128000, 147455, 2048000, 2359295, 32768000, 37748735, 524288000, 603979775, 8388608000, 9663676415, 134217728000, 154618822655, 2147483648000, 2473901162495, 34359738368000, 39582418599935, 549755813888000, 633318697598975, 8796093022208000, 10133099161583615] : List ℕ).getD n 0 := by
  intro n hn
  rw [a_eq n]
  revert n
  decide +kernel

lemma v0 : ca 0 = 1 := vals 0 (by norm_num)
lemma v1 : ca 1 = 3 := vals 1 (by norm_num)
lemma v2 : ca 2 = 28 := vals 2 (by norm_num)
lemma v3 : ca 3 = 47 := vals 3 (by norm_num)
lemma v4 : ca 4 = 496 := vals 4 (by norm_num)
lemma v5 : ca 5 = 575 := vals 5 (by norm_num)
lemma v6 : ca 6 = 8000 := vals 6 (by norm_num)
lemma v7 : ca 7 = 9215 := vals 7 (by norm_num)
lemma v8 : ca 8 = 128000 := vals 8 (by norm_num)
lemma v9 : ca 9 = 147455 := vals 9 (by norm_num)
lemma v10 : ca 10 = 2048000 := vals 10 (by norm_num)
lemma v11 : ca 11 = 2359295 := vals 11 (by norm_num)
lemma v12 : ca 12 = 32768000 := vals 12 (by norm_num)
lemma v13 : ca 13 = 37748735 := vals 13 (by norm_num)
lemma v14 : ca 14 = 524288000 := vals 14 (by norm_num)
lemma v15 : ca 15 = 603979775 := vals 15 (by norm_num)
lemma v16 : ca 16 = 8388608000 := vals 16 (by norm_num)
lemma v17 : ca 17 = 9663676415 := vals 17 (by norm_num)
lemma v18 : ca 18 = 134217728000 := vals 18 (by norm_num)
lemma v19 : ca 19 = 154618822655 := vals 19 (by norm_num)
lemma v20 : ca 20 = 2147483648000 := vals 20 (by norm_num)
lemma v21 : ca 21 = 2473901162495 := vals 21 (by norm_num)
lemma v22 : ca 22 = 34359738368000 := vals 22 (by norm_num)
lemma v23 : ca 23 = 39582418599935 := vals 23 (by norm_num)
lemma v24 : ca 24 = 549755813888000 := vals 24 (by norm_num)
lemma v25 : ca 25 = 633318697598975 := vals 25 (by norm_num)
lemma v26 : ca 26 = 8796093022208000 := vals 26 (by norm_num)
lemma v27 : ca 27 = 10133099161583615 := vals 27 (by norm_num)

lemma geo (c L : ℕ) : ((2 : ℚ) - 1) * ∑ k ∈ Finset.range L, (2 : ℚ) ^ (c + k) =
    (2 : ℚ) ^ (c + L) - (2 : ℚ) ^ c := by
  induction L with
  | zero => simp
  | succ L ih => rw [Finset.sum_range_succ, mul_add, ih]; ring

set_option maxHeartbeats 4000000 in
lemma row_split (n : ℕ) (hn : 9 ≤ n) :
    ca n = (∑ k ∈ Finset.range 7, if (elT.getD ((n - 9) % 2) 0).testBit k then 2 ^ (2 * n - k) else 0) +
      (if flT.getD ((n - 9) % 2) false then ∑ k ∈ Finset.range (n - 7), 2 ^ (2 * n - (7 + k)) else 0) +
      (∑ m ∈ Finset.range 1, if (coT.getD ((n - 9) % 2) 0).testBit m then 2 ^ (n + 0 - m) else 0) +
      (if flT.getD ((n - 9) % 2) false then ∑ k ∈ Finset.range (n - 7), 2 ^ (n - 0 - 1 - k) else 0) +
      (∑ k ∈ Finset.range 7, if (erT.getD ((n - 9) % 2) 0).testBit (6 - k) then 2 ^ (6 - k) else 0) := by
  unfold ca
  rw [state_eq_V n hn]
  rw [show 2 * n + 1 = 7 + (n - 7) + 1 + (n - 7) + 7 by omega]
  rw [Finset.sum_range_add, Finset.sum_range_add, Finset.sum_range_add, Finset.sum_range_add]
  congr 1
  congr 1
  congr 1
  congr 1
  · refine Finset.sum_congr rfl fun k hk => ?_
    have hk' := Finset.mem_range.mp hk
    rw [V_el n hn _ k (by omega) (by omega)]
  · have h : ∀ k ∈ Finset.range (n - 7), (if V n (((7 + k : ℕ) : ℤ) - n) then
        2 ^ (2 * n - (7 + k)) else 0) = if flT.getD ((n - 9) % 2) false then 2 ^ (2 * n - (7 + k)) else 0 := by
      intro k hk
      have hk' := Finset.mem_range.mp hk
      rw [V_fl n hn _ (by push_cast; omega) (by push_cast; omega) (by push_cast; omega)]
    rw [Finset.sum_congr rfl h]
    cases flT.getD ((n - 9) % 2) false <;> simp
  · refine Finset.sum_congr rfl fun m hm => ?_
    have hm' := Finset.mem_range.mp hm
    rw [V_co n hn _ m (by push_cast; omega) (by omega),
      show 2 * n - (7 + (n - 7) + m) = n + 0 - m by omega]
  · have h : ∀ k ∈ Finset.range (n - 7), (if V n (((7 + (n - 7) + 1 + k : ℕ) : ℤ) - n) then
        2 ^ (2 * n - (7 + (n - 7) + 1 + k)) else 0) =
        if flT.getD ((n - 9) % 2) false then 2 ^ (n - 0 - 1 - k) else 0 := by
      intro k hk
      have hk' := Finset.mem_range.mp hk
      rw [V_fl n hn _ (by push_cast; omega) (by push_cast; omega) (by push_cast; omega),
        show 2 * n - (7 + (n - 7) + 1 + k) = n - 0 - 1 - k by omega]
    rw [Finset.sum_congr rfl h]
    cases flT.getD ((n - 9) % 2) false <;> simp
  · refine Finset.sum_congr rfl fun k hk => ?_
    have hk' := Finset.mem_range.mp hk
    rw [V_er n hn _ (6 - k) (by push_cast; omega) (by omega),
      show 2 * n - (7 + (n - 7) + 1 + (n - 7) + k) = 6 - k by omega]

def Esum (r : ℕ) : ℕ := ∑ k ∈ Finset.range 7, if (elT.getD r 0).testBit k then 2 ^ (6 - k) else 0
def Csum (r : ℕ) : ℕ := ∑ m ∈ Finset.range 1, if (coT.getD r 0).testBit m then 2 ^ (2 * 0 - m) else 0
def Rsum (r : ℕ) : ℕ := ∑ k ∈ Finset.range 7, if (erT.getD r 0).testBit (6 - k) then 2 ^ (6 - k) else 0
def fl (r : ℕ) : ℕ := if flT.getD r false then 1 else 0

set_option maxHeartbeats 4000000 in
lemma row_closed (n : ℕ) (hn : 9 ≤ n) :
    ca n = 2 ^ (2 * n - 6) * Esum ((n - 9) % 2) + fl ((n - 9) % 2) * ∑ k ∈ Finset.range (n - 7), 2 ^ (n + 0 + 1 + k) +
      2 ^ (n - 0) * Csum ((n - 9) % 2) + fl ((n - 9) % 2) * ∑ k ∈ Finset.range (n - 7), 2 ^ (6 + 1 + k) +
      Rsum ((n - 9) % 2) := by
  rw [row_split n hn]
  congr 1
  congr 1
  congr 1
  congr 1
  · unfold Esum
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' := Finset.mem_range.mp hk
    split_ifs
    · rw [← pow_add]; congr 1; omega
    · simp
  · unfold fl
    split_ifs <;> simp only [one_mul, zero_mul]
    rw [← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' := Finset.mem_range.mp hk
    congr 1
    omega
  · unfold Csum
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun m hm => ?_
    have hm' := Finset.mem_range.mp hm
    split_ifs
    · rw [← pow_add]; congr 1; omega
    · simp
  · unfold fl
    split_ifs <;> simp only [one_mul, zero_mul]
    rw [← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' := Finset.mem_range.mp hk
    congr 1
    omega


lemma cfn0 (n : ℕ) (h1 : 9 ≤ n) (h2 : n % 2 = 0) :
    (2 : ℚ) ^ 6 * (((2 : ℚ) - 1) * (ca n : ℚ)) =
      (125 : ℚ) * (2 : ℚ) ^ (2 * n) + (0 : ℚ) * (2 : ℚ) ^ n + (0 : ℚ) := by
  rw [row_closed n h1, show (n - 9) % 2 = 1 by omega, show Esum 1 = 125 by decide,
    show Csum 1 = 0 by decide, show Rsum 1 = 0 by decide, show fl 1 = 0 by decide]
  obtain ⟨L, rfl⟩ : ∃ L, n = 7 + L := ⟨n - 7, by omega⟩
  rw [show 7 + L - 7 = L by omega, show 2 * (7 + L) - 6 = 8 + 2 * L by omega,
    show 7 + L - 0 = 7 + L by omega]
  have g1 := geo (7 + L + 0 + 1) L
  have g2 := geo (6 + 1) L
  push_cast
  linear_combination (0 * (2 : ℚ) ^ 6) * g1 + (0 * (2 : ℚ) ^ 6) * g2


lemma cfn1 (n : ℕ) (h1 : 9 ≤ n) (h2 : n % 2 = 1) :
    (2 : ℚ) ^ 6 * (((2 : ℚ) - 1) * (ca n : ℚ)) =
      (36 : ℚ) * (2 : ℚ) ^ (2 * n) + (0 : ℚ) * (2 : ℚ) ^ n + (-64 : ℚ) := by
  rw [row_closed n h1, show (n - 9) % 2 = 0 by omega, show Esum 0 = 35 by decide,
    show Csum 0 = 1 by decide, show Rsum 0 = 127 by decide, show fl 0 = 1 by decide]
  obtain ⟨L, rfl⟩ : ∃ L, n = 7 + L := ⟨n - 7, by omega⟩
  rw [show 7 + L - 7 = L by omega, show 2 * (7 + L) - 6 = 8 + 2 * L by omega,
    show 7 + L - 0 = 7 + L by omega]
  have g1 := geo (7 + L + 0 + 1) L
  have g2 := geo (6 + 1) L
  push_cast
  linear_combination (1 * (2 : ℚ) ^ 6) * g1 + (1 * (2 : ℚ) ^ 6) * g2


/-- a(n) = 17*a(n-2)-16*a(n-4) for n>8 -/
theorem recurrence0 (n : ℕ) (hn : 9 ≤ n) : (ca n : ℤ) = (((17 : ℤ) * (ca (n - 2) : ℤ)) - ((16 : ℤ) * (ca (n - 4) : ℤ))) := by
  rcases Nat.lt_or_ge n 13 with hlt | hge
  · interval_cases n <;> norm_num [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13] at *
  · suffices hq : (ca n : ℚ) = (((17 : ℚ) * (ca (n - 2) : ℚ)) - ((16 : ℚ) * (ca (n - 4) : ℚ))) by exact_mod_cast hq
    rcases (by omega : n % 2 = 0 ∨ n % 2 = 1) with hpar | hpar
    · obtain ⟨q, rfl⟩ : ∃ q, n = 14 + 2 * q := ⟨(n - 14) / 2, by omega⟩
      have c0 := cfn0 (14 + 2 * q) (by omega) (by omega)
      rw [show 14 + 2 * q - 2 = 12 + 2 * q by omega]
      have c2 := cfn0 (12 + 2 * q) (by omega) (by omega)
      rw [show 14 + 2 * q - 4 = 10 + 2 * q by omega]
      have c4 := cfn0 (10 + 2 * q) (by omega) (by omega)
      try simp only [pow_add, pow_mul, neg_one_sq, one_pow, mul_one, one_mul, show ((-1 : ℚ)) ^ 4 = 1 by norm_num, show ((-1 : ℚ)) ^ 6 = 1 by norm_num, show ((-1 : ℚ)) ^ 12 = 1 by norm_num] at c0 c2 c4 ⊢
      push_cast at c0 c2 c4 ⊢
      linear_combination (1 / ((2 : ℚ) ^ 6 * ((2 : ℚ) - 1))) * c0 + (-((17 : ℚ)) / ((2 : ℚ) ^ 6 * ((2 : ℚ) - 1))) * c2 + (-((-16 : ℚ)) / ((2 : ℚ) ^ 6 * ((2 : ℚ) - 1))) * c4
    · obtain ⟨q, rfl⟩ : ∃ q, n = 13 + 2 * q := ⟨(n - 13) / 2, by omega⟩
      have c0 := cfn1 (13 + 2 * q) (by omega) (by omega)
      rw [show 13 + 2 * q - 2 = 11 + 2 * q by omega]
      have c2 := cfn1 (11 + 2 * q) (by omega) (by omega)
      rw [show 13 + 2 * q - 4 = 9 + 2 * q by omega]
      have c4 := cfn1 (9 + 2 * q) (by omega) (by omega)
      try simp only [pow_add, pow_mul, neg_one_sq, one_pow, mul_one, one_mul, show ((-1 : ℚ)) ^ 4 = 1 by norm_num, show ((-1 : ℚ)) ^ 6 = 1 by norm_num, show ((-1 : ℚ)) ^ 12 = 1 by norm_num] at c0 c2 c4 ⊢
      push_cast at c0 c2 c4 ⊢
      linear_combination (1 / ((2 : ℚ) ^ 6 * ((2 : ℚ) - 1))) * c0 + (-((17 : ℚ)) / ((2 : ℚ) ^ 6 * ((2 : ℚ) - 1))) * c2 + (-((-16 : ℚ)) / ((2 : ℚ) ^ 6 * ((2 : ℚ) - 1))) * c4


lemma gfrec1 (n : ℕ) (hn : 9 ≤ n) : (ca n : ℚ) = ((17 : ℚ)) * (ca (n - 2) : ℚ) + ((-16 : ℚ)) * (ca (n - 4) : ℚ) := by
  rcases Nat.lt_or_ge n 13 with hlt | hge
  · interval_cases n <;> norm_num [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13] at *
  · rcases (by omega : n % 2 = 0 ∨ n % 2 = 1) with hpar | hpar
    · obtain ⟨q, rfl⟩ : ∃ q, n = 14 + 2 * q := ⟨(n - 14) / 2, by omega⟩
      have c0 := cfn0 (14 + 2 * q) (by omega) (by omega)
      rw [show 14 + 2 * q - 2 = 12 + 2 * q by omega]
      have c2 := cfn0 (12 + 2 * q) (by omega) (by omega)
      rw [show 14 + 2 * q - 4 = 10 + 2 * q by omega]
      have c4 := cfn0 (10 + 2 * q) (by omega) (by omega)
      try simp only [pow_add, pow_mul, neg_one_sq, one_pow, mul_one, one_mul, show ((-1 : ℚ)) ^ 4 = 1 by norm_num, show ((-1 : ℚ)) ^ 6 = 1 by norm_num, show ((-1 : ℚ)) ^ 12 = 1 by norm_num] at c0 c2 c4 ⊢
      push_cast at c0 c2 c4 ⊢
      linear_combination (1 / ((2 : ℚ) ^ 6 * ((2 : ℚ) - 1))) * c0 + (-((17 : ℚ)) / ((2 : ℚ) ^ 6 * ((2 : ℚ) - 1))) * c2 + (-((-16 : ℚ)) / ((2 : ℚ) ^ 6 * ((2 : ℚ) - 1))) * c4
    · obtain ⟨q, rfl⟩ : ∃ q, n = 13 + 2 * q := ⟨(n - 13) / 2, by omega⟩
      have c0 := cfn1 (13 + 2 * q) (by omega) (by omega)
      rw [show 13 + 2 * q - 2 = 11 + 2 * q by omega]
      have c2 := cfn1 (11 + 2 * q) (by omega) (by omega)
      rw [show 13 + 2 * q - 4 = 9 + 2 * q by omega]
      have c4 := cfn1 (9 + 2 * q) (by omega) (by omega)
      try simp only [pow_add, pow_mul, neg_one_sq, one_pow, mul_one, one_mul, show ((-1 : ℚ)) ^ 4 = 1 by norm_num, show ((-1 : ℚ)) ^ 6 = 1 by norm_num, show ((-1 : ℚ)) ^ 12 = 1 by norm_num] at c0 c2 c4 ⊢
      push_cast at c0 c2 c4 ⊢
      linear_combination (1 / ((2 : ℚ) ^ 6 * ((2 : ℚ) - 1))) * c0 + (-((17 : ℚ)) / ((2 : ℚ) ^ 6 * ((2 : ℚ) - 1))) * c2 + (-((-16 : ℚ)) / ((2 : ℚ) ^ 6 * ((2 : ℚ) - 1))) * c4

open PowerSeries in
/-- G.f.: (1+3*x+11*x^2-4*x^3+36*x^4-176*x^5+16*x^6+192*x^7-64*x^8) / ((1-x)*(1+x)*(1-4*x)*(1+4*x)) -/
theorem gf1 : PowerSeries.mk (fun n => (ca n : ℚ)) = ((1+3*X+11*X ^ 2-4*X ^ 3+36*X ^ 4-176*X ^ 5+16*X ^ 6+192*X ^ 7-64*X ^ 8)) * (((1-X)*(1+X)*(1-4*X)*(1+4*X)))⁻¹ := by
  set G : ℚ⟦X⟧ := PowerSeries.mk (fun n => (ca n : ℚ))
  have hden : constantCoeff ((((1-X)*(1+X)*(1-4*X)*(1+4*X))) : ℚ⟦X⟧) ≠ 0 := by simp
  have eQ : G * (((1-X)*(1+X)*(1-4*X)*(1+4*X))) = C ((1 : ℚ)) * G + C ((-17 : ℚ)) * (G * X ^ 2) + C ((16 : ℚ)) * (G * X ^ 4) := by
    (try simp only [map_neg, map_ofNat, map_one, map_div₀, map_natCast]) <;> ring
  have eP : (((1+3*X+11*X ^ 2-4*X ^ 3+36*X ^ 4-176*X ^ 5+16*X ^ 6+192*X ^ 7-64*X ^ 8)) : ℚ⟦X⟧) = C ((1 : ℚ)) + C ((3 : ℚ)) * X ^ 1 + C ((11 : ℚ)) * X ^ 2 + C ((-4 : ℚ)) * X ^ 3 + C ((36 : ℚ)) * X ^ 4 + C ((-176 : ℚ)) * X ^ 5 + C ((16 : ℚ)) * X ^ 6 + C ((192 : ℚ)) * X ^ 7 + C ((-64 : ℚ)) * X ^ 8 := by
    (try simp only [map_neg, map_ofNat, map_one, map_div₀, map_natCast]) <;> ring
  have key : G * (((1-X)*(1+X)*(1-4*X)*(1+4*X))) = (1+3*X+11*X ^ 2-4*X ^ 3+36*X ^ 4-176*X ^ 5+16*X ^ 6+192*X ^ 7-64*X ^ 8) := by
    rw [eQ, eP]
    ext n
    simp only [map_add, map_sub, coeff_C_mul, coeff_mul_X_pow', coeff_X_pow, G, coeff_mk, coeff_C]
    rcases Nat.lt_or_ge n 9 with hn | hn
    · interval_cases n <;> norm_num [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13]
    · simp only [show 1 ≤ n by omega, show 2 ≤ n by omega, show 3 ≤ n by omega, show 4 ≤ n by omega, show 5 ≤ n by omega, show 6 ≤ n by omega, show 7 ≤ n by omega, show 8 ≤ n by omega, show n ≠ 0 by omega, show n ≠ 1 by omega, show n ≠ 2 by omega, show n ≠ 3 by omega, show n ≠ 4 by omega, show n ≠ 5 by omega, show n ≠ 6 by omega, show n ≠ 7 by omega, show n ≠ 8 by omega, show n - 1 ≠ 0 by omega, show n - 2 ≠ 0 by omega, show n - 3 ≠ 0 by omega, show n - 4 ≠ 0 by omega, show n - 5 ≠ 0 by omega, show n - 6 ≠ 0 by omega, show n - 7 ≠ 0 by omega, show n - 8 ≠ 0 by omega, if_true, if_false, ↓reduceIte, ne_eq, not_false_eq_true]
      have hr := gfrec1 n hn
      linear_combination ((1 : ℚ)) * hr
  rw [← key, mul_assoc, PowerSeries.mul_inv_cancel _ hden, mul_one]


open PowerSeries in
/-- All the proved formula lines of the entry, together. -/
theorem formulas :
    (∀ n : ℕ, 9 ≤ n → (ca n : ℤ) = (((17 : ℤ) * (ca (n - 2) : ℤ)) - ((16 : ℤ) * (ca (n - 4) : ℤ)))) ∧
    (PowerSeries.mk (fun n => (ca n : ℚ)) = ((1+3*X+11*X ^ 2-4*X ^ 3+36*X ^ 4-176*X ^ 5+16*X ^ 6+192*X ^ 7-64*X ^ 8)) * (((1-X)*(1+X)*(1-4*X)*(1+4*X)))⁻¹) :=
  ⟨recurrence0, gf1⟩


/-! ## The statement's definitions and the bridge -/

open PowerSeries






theorem rule_eq (l c r : Bool) :
    rule l c r = Nat.testBit 125 (4 * l.toNat + 2 * c.toNat + r.toNat) := by
  cases l <;> cases c <;> cases r <;> rfl

theorem cstate_eq (t : ℕ) : cstate t = state 125 t := by
  induction t with
  | zero => funext i; rfl
  | succ t ih =>
    funext i
    show rule (cstate t (i - 1)) (cstate t i) (cstate t (i + 1)) = step 125 (state 125 t) i
    rw [ih, rule_eq]
    rfl

theorem row_eq (n : ℕ) :
    rowValue (state 125 n) n = ∑ k ∈ Finset.range (2 * n + 1), if cstate n ((k : ℤ) - n) then 2 ^ (2 * n - k) else 0 := by
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

theorem controls : ∀ n ≤ 27, a n = ([1, 3, 28, 47, 496, 575, 8000, 9215, 128000, 147455, 2048000, 2359295, 32768000, 37748735, 524288000, 603979775, 8388608000, 9663676415, 134217728000, 154618822655, 2147483648000, 2473901162495, 34359738368000, 39582418599935, 549755813888000, 633318697598975, 8796093022208000, 10133099161583615] : List ℕ).getD n 0 := by
  rw [a_eq_ca]
  exact vals

/-- The site's problem, as stated in `main`. -/
theorem conj :
    (∀ n : ℕ, 8 < n → (a n : ℤ) = 17 * a (n - 2) - 16 * a (n - 4)) ∧
    A = (1 + 3 * X + 11 * X ^ 2 - 4 * X ^ 3 + 36 * X ^ 4 - 176 * X ^ 5 + 16 * X ^ 6 + 192 * X ^ 7 - 64 * X ^ 8) *
      ((1 - X) * (1 + X) * (1 - 4 * X) * (1 + 4 * X))⁻¹ := by
  rw [show A = PowerSeries.mk (fun n => (a n : ℚ)) from rfl, a_eq_ca]
  exact ⟨fun n hn => (recurrence0 n (by omega)).trans (by ring),
    gf1⟩

end OMA.S_oeis_a267360

theorem OMA.solution : type_of% @OMA.S_oeis_a267360.main :=
  OMA.S_oeis_a267360.conj
