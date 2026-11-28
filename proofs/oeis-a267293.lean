import OMAStatements.S_oeis_a267293

namespace OMA.S_oeis_a267293


/-- Rule 121 as a local map: the new state of a cell from (left, center, right). -/
def rule (l c r : Bool) : Bool := (121 : ℕ).testBit ((cond l 4 0) + (cond c 2 0) + (cond r 1 0))

/-- The configuration at time `t`, started from the single ON cell at 0. -/
def cstate : ℕ → ℤ → Bool
  | 0, i => decide (i = 0)
  | t + 1, i => rule (cstate t (i - 1)) (cstate t i) (cstate t (i + 1))


/-- A267293(n): row `n`, cells `-n..n` (leftmost first), as binary digits read in base 10. -/
def ca (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (2 * n + 1), if cstate n ((k : ℤ) - n) then 10 ^ (2 * n - k) else 0


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
    (true, 8589836287),
    (false, 180224),
    (true, 8589795327),
    (false, 487424),
    (true, 8589793279),
    (false, 486400),
    (true, 8589803007),
    (false, 460544),
    (true, 8589770111),
    (false, 444096),
    (true, 8589926367),
    (false, 28784),
    (true, 8589924311),
    (false, 27756),
    (true, 8589934077)]

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
def elT : List ℕ := [7934, 1799, 6906, 6939]
/-- Bit `j` of the right edge block: cell `t - j`. -/
def erT : List ℕ := [8191, 0, 8191, 0]
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
  ∑ k ∈ Finset.range (2 * n + 1), if rowOf n ((k : ℤ) - n) then 10 ^ (2 * n - k) else 0

lemma a_eq (n : ℕ) : ca n = aSim n := by
  unfold ca aSim
  simp only [state_eq]

/-- The values a(0..39); the listed terms are among them (control). -/
lemma vals : ∀ n ≤ 39, ca n = ([1, 1, 11010, 111011, 111011100, 1011101111, 1101101110000, 11111110111111, 11100000111000000, 101111101011111111, 110110001101100000000, 1111111011111111111111, 1110000011100000000000000, 10111110101111111111111111, 11011000110110000000000000000, 111111101111111111111111111111, 111000001110000000000000000000000, 1011111010111111111111111111111111, 1101100011011000000000000000000000000, 11111110111111111111111111111111111111, 11100000111000000000000000000000000000000, 101111101011111111111111111111111111111111, 110110001101100000000000000000000000000000000, 1111111011111111111111111111111111111111111111, 1110000011100000000000000000000000000000000000000, 10111110101111111111111111111111111111111111111111, 11011000110110000000000000000000000000000000000000000, 111111101111111111111111111111111111111111111111111111, 111000001110000000000000000000000000000000000000000000000, 1011111010111111111111111111111111111111111111111111111111, 1101100011011000000000000000000000000000000000000000000000000, 11111110111111111111111111111111111111111111111111111111111111, 11100000111000000000000000000000000000000000000000000000000000000, 101111101011111111111111111111111111111111111111111111111111111111, 110110001101100000000000000000000000000000000000000000000000000000000, 1111111011111111111111111111111111111111111111111111111111111111111111, 1110000011100000000000000000000000000000000000000000000000000000000000000, 10111110101111111111111111111111111111111111111111111111111111111111111111, 11011000110110000000000000000000000000000000000000000000000000000000000000000, 111111101111111111111111111111111111111111111111111111111111111111111111111111] : List ℕ).getD n 0 := by
  intro n hn
  rw [a_eq n]
  revert n
  decide +kernel

lemma v0 : ca 0 = 1 := vals 0 (by norm_num)
lemma v1 : ca 1 = 1 := vals 1 (by norm_num)
lemma v2 : ca 2 = 11010 := vals 2 (by norm_num)
lemma v3 : ca 3 = 111011 := vals 3 (by norm_num)
lemma v4 : ca 4 = 111011100 := vals 4 (by norm_num)
lemma v5 : ca 5 = 1011101111 := vals 5 (by norm_num)
lemma v6 : ca 6 = 1101101110000 := vals 6 (by norm_num)
lemma v7 : ca 7 = 11111110111111 := vals 7 (by norm_num)
lemma v8 : ca 8 = 11100000111000000 := vals 8 (by norm_num)
lemma v9 : ca 9 = 101111101011111111 := vals 9 (by norm_num)
lemma v10 : ca 10 = 110110001101100000000 := vals 10 (by norm_num)
lemma v11 : ca 11 = 1111111011111111111111 := vals 11 (by norm_num)
lemma v12 : ca 12 = 1110000011100000000000000 := vals 12 (by norm_num)
lemma v13 : ca 13 = 10111110101111111111111111 := vals 13 (by norm_num)
lemma v14 : ca 14 = 11011000110110000000000000000 := vals 14 (by norm_num)
lemma v15 : ca 15 = 111111101111111111111111111111 := vals 15 (by norm_num)
lemma v16 : ca 16 = 111000001110000000000000000000000 := vals 16 (by norm_num)
lemma v17 : ca 17 = 1011111010111111111111111111111111 := vals 17 (by norm_num)
lemma v18 : ca 18 = 1101100011011000000000000000000000000 := vals 18 (by norm_num)
lemma v19 : ca 19 = 11111110111111111111111111111111111111 := vals 19 (by norm_num)
lemma v20 : ca 20 = 11100000111000000000000000000000000000000 := vals 20 (by norm_num)
lemma v21 : ca 21 = 101111101011111111111111111111111111111111 := vals 21 (by norm_num)
lemma v22 : ca 22 = 110110001101100000000000000000000000000000000 := vals 22 (by norm_num)
lemma v23 : ca 23 = 1111111011111111111111111111111111111111111111 := vals 23 (by norm_num)
lemma v24 : ca 24 = 1110000011100000000000000000000000000000000000000 := vals 24 (by norm_num)
lemma v25 : ca 25 = 10111110101111111111111111111111111111111111111111 := vals 25 (by norm_num)
lemma v26 : ca 26 = 11011000110110000000000000000000000000000000000000000 := vals 26 (by norm_num)
lemma v27 : ca 27 = 111111101111111111111111111111111111111111111111111111 := vals 27 (by norm_num)
lemma v28 : ca 28 = 111000001110000000000000000000000000000000000000000000000 := vals 28 (by norm_num)
lemma v29 : ca 29 = 1011111010111111111111111111111111111111111111111111111111 := vals 29 (by norm_num)
lemma v30 : ca 30 = 1101100011011000000000000000000000000000000000000000000000000 := vals 30 (by norm_num)
lemma v31 : ca 31 = 11111110111111111111111111111111111111111111111111111111111111 := vals 31 (by norm_num)
lemma v32 : ca 32 = 11100000111000000000000000000000000000000000000000000000000000000 := vals 32 (by norm_num)
lemma v33 : ca 33 = 101111101011111111111111111111111111111111111111111111111111111111 := vals 33 (by norm_num)
lemma v34 : ca 34 = 110110001101100000000000000000000000000000000000000000000000000000000 := vals 34 (by norm_num)
lemma v35 : ca 35 = 1111111011111111111111111111111111111111111111111111111111111111111111 := vals 35 (by norm_num)
lemma v36 : ca 36 = 1110000011100000000000000000000000000000000000000000000000000000000000000 := vals 36 (by norm_num)
lemma v37 : ca 37 = 10111110101111111111111111111111111111111111111111111111111111111111111111 := vals 37 (by norm_num)
lemma v38 : ca 38 = 11011000110110000000000000000000000000000000000000000000000000000000000000000 := vals 38 (by norm_num)
lemma v39 : ca 39 = 111111101111111111111111111111111111111111111111111111111111111111111111111111 := vals 39 (by norm_num)

lemma geo (c L : ℕ) : ((10 : ℚ) - 1) * ∑ k ∈ Finset.range L, (10 : ℚ) ^ (c + k) =
    (10 : ℚ) ^ (c + L) - (10 : ℚ) ^ c := by
  induction L with
  | zero => simp
  | succ L ih => rw [Finset.sum_range_succ, mul_add, ih]; ring

set_option maxHeartbeats 4000000 in
lemma row_split (n : ℕ) (hn : 15 ≤ n) :
    ca n = (∑ k ∈ Finset.range 13, if (elT.getD ((n - 15) % 4) 0).testBit k then 10 ^ (2 * n - k) else 0) +
      (if flT.getD ((n - 15) % 4) false then ∑ k ∈ Finset.range (n - 13), 10 ^ (2 * n - (13 + k)) else 0) +
      (∑ m ∈ Finset.range 1, if (coT.getD ((n - 15) % 4) 0).testBit m then 10 ^ (n + 0 - m) else 0) +
      (if flT.getD ((n - 15) % 4) false then ∑ k ∈ Finset.range (n - 13), 10 ^ (n - 0 - 1 - k) else 0) +
      (∑ k ∈ Finset.range 13, if (erT.getD ((n - 15) % 4) 0).testBit (12 - k) then 10 ^ (12 - k) else 0) := by
  unfold ca
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
  · have h : ∀ k ∈ Finset.range (n - 13), (if V n (((13 + k : ℕ) : ℤ) - n) then
        10 ^ (2 * n - (13 + k)) else 0) = if flT.getD ((n - 15) % 4) false then 10 ^ (2 * n - (13 + k)) else 0 := by
      intro k hk
      have hk' := Finset.mem_range.mp hk
      rw [V_fl n hn _ (by push_cast; omega) (by push_cast; omega) (by push_cast; omega)]
    rw [Finset.sum_congr rfl h]
    cases flT.getD ((n - 15) % 4) false <;> simp
  · refine Finset.sum_congr rfl fun m hm => ?_
    have hm' := Finset.mem_range.mp hm
    rw [V_co n hn _ m (by push_cast; omega) (by omega),
      show 2 * n - (13 + (n - 13) + m) = n + 0 - m by omega]
  · have h : ∀ k ∈ Finset.range (n - 13), (if V n (((13 + (n - 13) + 1 + k : ℕ) : ℤ) - n) then
        10 ^ (2 * n - (13 + (n - 13) + 1 + k)) else 0) =
        if flT.getD ((n - 15) % 4) false then 10 ^ (n - 0 - 1 - k) else 0 := by
      intro k hk
      have hk' := Finset.mem_range.mp hk
      rw [V_fl n hn _ (by push_cast; omega) (by push_cast; omega) (by push_cast; omega),
        show 2 * n - (13 + (n - 13) + 1 + k) = n - 0 - 1 - k by omega]
    rw [Finset.sum_congr rfl h]
    cases flT.getD ((n - 15) % 4) false <;> simp
  · refine Finset.sum_congr rfl fun k hk => ?_
    have hk' := Finset.mem_range.mp hk
    rw [V_er n hn _ (12 - k) (by push_cast; omega) (by omega),
      show 2 * n - (13 + (n - 13) + 1 + (n - 13) + k) = 12 - k by omega]

def Esum (r : ℕ) : ℕ := ∑ k ∈ Finset.range 13, if (elT.getD r 0).testBit k then 10 ^ (12 - k) else 0
def Csum (r : ℕ) : ℕ := ∑ m ∈ Finset.range 1, if (coT.getD r 0).testBit m then 10 ^ (2 * 0 - m) else 0
def Rsum (r : ℕ) : ℕ := ∑ k ∈ Finset.range 13, if (erT.getD r 0).testBit (12 - k) then 10 ^ (12 - k) else 0
def fl (r : ℕ) : ℕ := if flT.getD r false then 1 else 0

set_option maxHeartbeats 4000000 in
lemma row_closed (n : ℕ) (hn : 15 ≤ n) :
    ca n = 10 ^ (2 * n - 12) * Esum ((n - 15) % 4) + fl ((n - 15) % 4) * ∑ k ∈ Finset.range (n - 13), 10 ^ (n + 0 + 1 + k) +
      10 ^ (n - 0) * Csum ((n - 15) % 4) + fl ((n - 15) % 4) * ∑ k ∈ Finset.range (n - 13), 10 ^ (12 + 1 + k) +
      Rsum ((n - 15) % 4) := by
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


lemma cfn0 (n : ℕ) (h1 : 15 ≤ n) (h2 : n % 4 = 0) :
    (10 : ℚ) ^ 12 * (((10 : ℚ) - 1) * (ca n : ℚ)) =
      (9990000099900 : ℚ) * (10 : ℚ) ^ (2 * n) + (0 : ℚ) * (10 : ℚ) ^ n + (0 : ℚ) := by
  rw [row_closed n h1, show (n - 15) % 4 = 1 by omega, show Esum 1 = 1110000011100 by decide,
    show Csum 1 = 0 by decide, show Rsum 1 = 0 by decide, show fl 1 = 0 by decide]
  obtain ⟨L, rfl⟩ : ∃ L, n = 13 + L := ⟨n - 13, by omega⟩
  rw [show 13 + L - 13 = L by omega, show 2 * (13 + L) - 12 = 14 + 2 * L by omega,
    show 13 + L - 0 = 13 + L by omega]
  have g1 := geo (13 + L + 0 + 1) L
  have g2 := geo (12 + 1) L
  push_cast
  linear_combination (0 * (10 : ℚ) ^ 12) * g1 + (0 * (10 : ℚ) ^ 12) * g2


lemma cfn1 (n : ℕ) (h1 : 15 ≤ n) (h2 : n % 4 = 1) :
    (10 : ℚ) ^ 12 * (((10 : ℚ) - 1) * (ca n : ℚ)) =
      (909999909100 : ℚ) * (10 : ℚ) ^ (2 * n) + (0 : ℚ) * (10 : ℚ) ^ n + (-1000000000000 : ℚ) := by
  rw [row_closed n h1, show (n - 15) % 4 = 2 by omega, show Esum 2 = 101111101011 by decide,
    show Csum 2 = 1 by decide, show Rsum 2 = 1111111111111 by decide, show fl 2 = 1 by decide]
  obtain ⟨L, rfl⟩ : ∃ L, n = 13 + L := ⟨n - 13, by omega⟩
  rw [show 13 + L - 13 = L by omega, show 2 * (13 + L) - 12 = 14 + 2 * L by omega,
    show 13 + L - 0 = 13 + L by omega]
  have g1 := geo (13 + L + 0 + 1) L
  have g2 := geo (12 + 1) L
  push_cast
  linear_combination (1 * (10 : ℚ) ^ 12) * g1 + (1 * (10 : ℚ) ^ 12) * g2


lemma cfn2 (n : ℕ) (h1 : 15 ≤ n) (h2 : n % 4 = 2) :
    (10 : ℚ) ^ 12 * (((10 : ℚ) - 1) * (ca n : ℚ)) =
      (9909900099099 : ℚ) * (10 : ℚ) ^ (2 * n) + (0 : ℚ) * (10 : ℚ) ^ n + (0 : ℚ) := by
  rw [row_closed n h1, show (n - 15) % 4 = 3 by omega, show Esum 3 = 1101100011011 by decide,
    show Csum 3 = 0 by decide, show Rsum 3 = 0 by decide, show fl 3 = 0 by decide]
  obtain ⟨L, rfl⟩ : ∃ L, n = 13 + L := ⟨n - 13, by omega⟩
  rw [show 13 + L - 13 = L by omega, show 2 * (13 + L) - 12 = 14 + 2 * L by omega,
    show 13 + L - 0 = 13 + L by omega]
  have g1 := geo (13 + L + 0 + 1) L
  have g2 := geo (12 + 1) L
  push_cast
  linear_combination (0 * (10 : ℚ) ^ 12) * g1 + (0 * (10 : ℚ) ^ 12) * g2


lemma cfn3 (n : ℕ) (h1 : 15 ≤ n) (h2 : n % 4 = 3) :
    (10 : ℚ) ^ 12 * (((10 : ℚ) - 1) * (ca n : ℚ)) =
      (999999910000 : ℚ) * (10 : ℚ) ^ (2 * n) + (0 : ℚ) * (10 : ℚ) ^ n + (-1000000000000 : ℚ) := by
  rw [row_closed n h1, show (n - 15) % 4 = 0 by omega, show Esum 0 = 111111101111 by decide,
    show Csum 0 = 1 by decide, show Rsum 0 = 1111111111111 by decide, show fl 0 = 1 by decide]
  obtain ⟨L, rfl⟩ : ∃ L, n = 13 + L := ⟨n - 13, by omega⟩
  rw [show 13 + L - 13 = L by omega, show 2 * (13 + L) - 12 = 14 + 2 * L by omega,
    show 13 + L - 0 = 13 + L by omega]
  have g1 := geo (13 + L + 0 + 1) L
  have g2 := geo (12 + 1) L
  push_cast
  linear_combination (1 * (10 : ℚ) ^ 12) * g1 + (1 * (10 : ℚ) ^ 12) * g2


/-- a(n) = a(n-2)+100000000*a(n-4)-100000000*a(n-6) for n>12 -/
theorem recurrence0 (n : ℕ) (hn : 13 ≤ n) : (ca n : ℤ) = (((ca (n - 2) : ℤ) + ((100000000 : ℤ) * (ca (n - 4) : ℤ))) - ((100000000 : ℤ) * (ca (n - 6) : ℤ))) := by
  rcases Nat.lt_or_ge n 21 with hlt | hge
  · interval_cases n <;> norm_num [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16, v17, v18, v19, v20, v21] at *
  · suffices hq : (ca n : ℚ) = (((ca (n - 2) : ℚ) + ((100000000 : ℚ) * (ca (n - 4) : ℚ))) - ((100000000 : ℚ) * (ca (n - 6) : ℚ))) by exact_mod_cast hq
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
      linear_combination (1 / ((10 : ℚ) ^ 12 * ((10 : ℚ) - 1))) * c0 + (-((1 : ℚ)) / ((10 : ℚ) ^ 12 * ((10 : ℚ) - 1))) * c2 + (-((100000000 : ℚ)) / ((10 : ℚ) ^ 12 * ((10 : ℚ) - 1))) * c4 + (-((-100000000 : ℚ)) / ((10 : ℚ) ^ 12 * ((10 : ℚ) - 1))) * c6
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
      linear_combination (1 / ((10 : ℚ) ^ 12 * ((10 : ℚ) - 1))) * c0 + (-((1 : ℚ)) / ((10 : ℚ) ^ 12 * ((10 : ℚ) - 1))) * c2 + (-((100000000 : ℚ)) / ((10 : ℚ) ^ 12 * ((10 : ℚ) - 1))) * c4 + (-((-100000000 : ℚ)) / ((10 : ℚ) ^ 12 * ((10 : ℚ) - 1))) * c6
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
      linear_combination (1 / ((10 : ℚ) ^ 12 * ((10 : ℚ) - 1))) * c0 + (-((1 : ℚ)) / ((10 : ℚ) ^ 12 * ((10 : ℚ) - 1))) * c2 + (-((100000000 : ℚ)) / ((10 : ℚ) ^ 12 * ((10 : ℚ) - 1))) * c4 + (-((-100000000 : ℚ)) / ((10 : ℚ) ^ 12 * ((10 : ℚ) - 1))) * c6
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
      linear_combination (1 / ((10 : ℚ) ^ 12 * ((10 : ℚ) - 1))) * c0 + (-((1 : ℚ)) / ((10 : ℚ) ^ 12 * ((10 : ℚ) - 1))) * c2 + (-((100000000 : ℚ)) / ((10 : ℚ) ^ 12 * ((10 : ℚ) - 1))) * c4 + (-((-100000000 : ℚ)) / ((10 : ℚ) ^ 12 * ((10 : ℚ) - 1))) * c6


lemma gfrec1 (n : ℕ) (hn : 13 ≤ n) : (ca n : ℚ) = ((1 : ℚ)) * (ca (n - 2) : ℚ) + ((100000000 : ℚ)) * (ca (n - 4) : ℚ) + ((-100000000 : ℚ)) * (ca (n - 6) : ℚ) := by
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
      linear_combination (1 / ((10 : ℚ) ^ 12 * ((10 : ℚ) - 1))) * c0 + (-((1 : ℚ)) / ((10 : ℚ) ^ 12 * ((10 : ℚ) - 1))) * c2 + (-((100000000 : ℚ)) / ((10 : ℚ) ^ 12 * ((10 : ℚ) - 1))) * c4 + (-((-100000000 : ℚ)) / ((10 : ℚ) ^ 12 * ((10 : ℚ) - 1))) * c6
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
      linear_combination (1 / ((10 : ℚ) ^ 12 * ((10 : ℚ) - 1))) * c0 + (-((1 : ℚ)) / ((10 : ℚ) ^ 12 * ((10 : ℚ) - 1))) * c2 + (-((100000000 : ℚ)) / ((10 : ℚ) ^ 12 * ((10 : ℚ) - 1))) * c4 + (-((-100000000 : ℚ)) / ((10 : ℚ) ^ 12 * ((10 : ℚ) - 1))) * c6
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
      linear_combination (1 / ((10 : ℚ) ^ 12 * ((10 : ℚ) - 1))) * c0 + (-((1 : ℚ)) / ((10 : ℚ) ^ 12 * ((10 : ℚ) - 1))) * c2 + (-((100000000 : ℚ)) / ((10 : ℚ) ^ 12 * ((10 : ℚ) - 1))) * c4 + (-((-100000000 : ℚ)) / ((10 : ℚ) ^ 12 * ((10 : ℚ) - 1))) * c6
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
      linear_combination (1 / ((10 : ℚ) ^ 12 * ((10 : ℚ) - 1))) * c0 + (-((1 : ℚ)) / ((10 : ℚ) ^ 12 * ((10 : ℚ) - 1))) * c2 + (-((100000000 : ℚ)) / ((10 : ℚ) ^ 12 * ((10 : ℚ) - 1))) * c4 + (-((-100000000 : ℚ)) / ((10 : ℚ) ^ 12 * ((10 : ℚ) - 1))) * c6

open PowerSeries in
/-- G.f.: (1 +x +11009*x^2 +111010*x^3 +11000090*x^4 +910990100*x^5 +90098900*x^6 +9099010000*x^7 -1109990110000*x^8 +979901000000*x^9 -108789011000000*x^10 -989900000000*x^11 +109898900000000*x^12) / ((1 -x)*(1 +x)*(1 -100*x)*(1 +100*x)*(1 +10000*x^2)) -/
theorem gf1 : PowerSeries.mk (fun n => (ca n : ℚ)) = ((1 +X +11009*X ^ 2 +111010*X ^ 3 +11000090*X ^ 4 +910990100*X ^ 5 +90098900*X ^ 6 +9099010000*X ^ 7 -1109990110000*X ^ 8 +979901000000*X ^ 9 -108789011000000*X ^ 10 -989900000000*X ^ 11 +109898900000000*X ^ 12)) * (((1 -X)*(1 +X)*(1 -100*X)*(1 +100*X)*(1 +10000*X ^ 2)))⁻¹ := by
  set G : ℚ⟦X⟧ := PowerSeries.mk (fun n => (ca n : ℚ))
  have hden : constantCoeff ((((1 -X)*(1 +X)*(1 -100*X)*(1 +100*X)*(1 +10000*X ^ 2))) : ℚ⟦X⟧) ≠ 0 := by simp
  have eQ : G * (((1 -X)*(1 +X)*(1 -100*X)*(1 +100*X)*(1 +10000*X ^ 2))) = C ((1 : ℚ)) * G + C ((-1 : ℚ)) * (G * X ^ 2) + C ((-100000000 : ℚ)) * (G * X ^ 4) + C ((100000000 : ℚ)) * (G * X ^ 6) := by
    (try simp only [map_neg, map_ofNat, map_one, map_div₀, map_natCast]) <;> ring
  have eP : (((1 +X +11009*X ^ 2 +111010*X ^ 3 +11000090*X ^ 4 +910990100*X ^ 5 +90098900*X ^ 6 +9099010000*X ^ 7 -1109990110000*X ^ 8 +979901000000*X ^ 9 -108789011000000*X ^ 10 -989900000000*X ^ 11 +109898900000000*X ^ 12)) : ℚ⟦X⟧) = C ((1 : ℚ)) + C ((1 : ℚ)) * X ^ 1 + C ((11009 : ℚ)) * X ^ 2 + C ((111010 : ℚ)) * X ^ 3 + C ((11000090 : ℚ)) * X ^ 4 + C ((910990100 : ℚ)) * X ^ 5 + C ((90098900 : ℚ)) * X ^ 6 + C ((9099010000 : ℚ)) * X ^ 7 + C ((-1109990110000 : ℚ)) * X ^ 8 + C ((979901000000 : ℚ)) * X ^ 9 + C ((-108789011000000 : ℚ)) * X ^ 10 + C ((-989900000000 : ℚ)) * X ^ 11 + C ((109898900000000 : ℚ)) * X ^ 12 := by
    (try simp only [map_neg, map_ofNat, map_one, map_div₀, map_natCast]) <;> ring
  have key : G * (((1 -X)*(1 +X)*(1 -100*X)*(1 +100*X)*(1 +10000*X ^ 2))) = (1 +X +11009*X ^ 2 +111010*X ^ 3 +11000090*X ^ 4 +910990100*X ^ 5 +90098900*X ^ 6 +9099010000*X ^ 7 -1109990110000*X ^ 8 +979901000000*X ^ 9 -108789011000000*X ^ 10 -989900000000*X ^ 11 +109898900000000*X ^ 12) := by
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
    (∀ n : ℕ, 13 ≤ n → (ca n : ℤ) = (((ca (n - 2) : ℤ) + ((100000000 : ℤ) * (ca (n - 4) : ℤ))) - ((100000000 : ℤ) * (ca (n - 6) : ℤ)))) ∧
    (PowerSeries.mk (fun n => (ca n : ℚ)) = ((1 +X +11009*X ^ 2 +111010*X ^ 3 +11000090*X ^ 4 +910990100*X ^ 5 +90098900*X ^ 6 +9099010000*X ^ 7 -1109990110000*X ^ 8 +979901000000*X ^ 9 -108789011000000*X ^ 10 -989900000000*X ^ 11 +109898900000000*X ^ 12)) * (((1 -X)*(1 +X)*(1 -100*X)*(1 +100*X)*(1 +10000*X ^ 2)))⁻¹) :=
  ⟨recurrence0, gf1⟩


/-! ## The statement's definitions and the bridge -/

open PowerSeries






theorem rule_eq (l c r : Bool) :
    rule l c r = Nat.testBit 121 (4 * l.toNat + 2 * c.toNat + r.toNat) := by
  cases l <;> cases c <;> cases r <;> rfl

theorem cstate_eq (t : ℕ) : cstate t = state 121 t := by
  induction t with
  | zero => funext i; rfl
  | succ t ih =>
    funext i
    show rule (cstate t (i - 1)) (cstate t i) (cstate t (i + 1)) = step 121 (state 121 t) i
    rw [ih, rule_eq]
    rfl

theorem row_eq (n : ℕ) :
    rowDigits (state 121 n) n = ∑ k ∈ Finset.range (2 * n + 1), if cstate n ((k : ℤ) - n) then 10 ^ (2 * n - k) else 0 := by
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

theorem controls : ∀ n ≤ 39, a n = ([1, 1, 11010, 111011, 111011100, 1011101111, 1101101110000, 11111110111111, 11100000111000000, 101111101011111111, 110110001101100000000, 1111111011111111111111, 1110000011100000000000000, 10111110101111111111111111, 11011000110110000000000000000, 111111101111111111111111111111, 111000001110000000000000000000000, 1011111010111111111111111111111111, 1101100011011000000000000000000000000, 11111110111111111111111111111111111111, 11100000111000000000000000000000000000000, 101111101011111111111111111111111111111111, 110110001101100000000000000000000000000000000, 1111111011111111111111111111111111111111111111, 1110000011100000000000000000000000000000000000000, 10111110101111111111111111111111111111111111111111, 11011000110110000000000000000000000000000000000000000, 111111101111111111111111111111111111111111111111111111, 111000001110000000000000000000000000000000000000000000000, 1011111010111111111111111111111111111111111111111111111111, 1101100011011000000000000000000000000000000000000000000000000, 11111110111111111111111111111111111111111111111111111111111111, 11100000111000000000000000000000000000000000000000000000000000000, 101111101011111111111111111111111111111111111111111111111111111111, 110110001101100000000000000000000000000000000000000000000000000000000, 1111111011111111111111111111111111111111111111111111111111111111111111, 1110000011100000000000000000000000000000000000000000000000000000000000000, 10111110101111111111111111111111111111111111111111111111111111111111111111, 11011000110110000000000000000000000000000000000000000000000000000000000000000, 111111101111111111111111111111111111111111111111111111111111111111111111111111] : List ℕ).getD n 0 := by
  rw [a_eq_ca]
  exact vals

/-- The site's problem, as stated in `main`. -/
theorem conj :
    (∀ n : ℕ, 12 < n → (a n : ℤ) = a (n - 2) + 100000000 * a (n - 4) - 100000000 * a (n - 6)) ∧
    A = (1 + X + 11009 * X ^ 2 + 111010 * X ^ 3 + 11000090 * X ^ 4 + 910990100 * X ^ 5 + 90098900 * X ^ 6 + 9099010000 * X ^ 7 - 1109990110000 * X ^ 8 + 979901000000 * X ^ 9 - 108789011000000 * X ^ 10 - 989900000000 * X ^ 11 + 109898900000000 * X ^ 12) *
      ((1 - X) * (1 + X) * (1 - 100 * X) * (1 + 100 * X) * (1 + 10000 * X ^ 2))⁻¹ := by
  rw [show A = PowerSeries.mk (fun n => (a n : ℚ)) from rfl, a_eq_ca]
  exact ⟨fun n hn => (recurrence0 n (by omega)).trans (by ring),
    gf1⟩

end OMA.S_oeis_a267293

theorem OMA.solution : type_of% @OMA.S_oeis_a267293.main :=
  OMA.S_oeis_a267293.conj
