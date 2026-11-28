import OMAStatements.S_oeis_a265431

namespace OMA.S_oeis_a265431


/-- Rule 188 as a local map: the new state of a cell from (left, center, right). -/
def rule (l c r : Bool) : Bool := (188 : ℕ).testBit ((cond l 4 0) + (cond c 2 0) + (cond r 1 0))

/-- The configuration at time `t`, started from the single ON cell at 0. -/
def cstate : ℕ → ℤ → Bool
  | 0, i => decide (i = 0)
  | t + 1, i => rule (cstate t (i - 1)) (cstate t i) (cstate t (i + 1))


/-- A265431(n): the number of OFF cells among `-t..t` in rows `t = 0..n`, summed. -/
def ca (n : ℕ) : ℕ :=
  ∑ t ∈ Finset.range (n + 1), ∑ k ∈ Finset.range (2 * t + 1), if cstate t ((k : ℤ) - t) then 0 else 1


/-! ## A finite certificate: rows `0..10` on the window `[-11, 11]` -/

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

def W : ℕ := 11

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

/-- The rows `0..10`, computed outside Lean and checked cell by cell below. -/
def stages : List (Bool × ℕ) :=
  [(false, 2048),
    (false, 6144),
    (false, 10240),
    (false, 30720),
    (false, 47104),
    (false, 120832),
    (false, 190464),
    (false, 489472),
    (false, 768000),
    (false, 1955840),
    (false, 3074048)]

lemma stages_ok : initOK (stages.getD 0 default) = true ∧
    ∀ t < 10, stepOK (stages.getD t default) (stages.getD (t + 1) default) = true := by
  decide +kernel

lemma certified (t : ℕ) (ht : t ≤ 10) :
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

/-! ## The regime from row 10 on -/

def bgT : List Bool := [false, false, false, false]
def elT : List ℕ := [0, 0, 0, 0]
def erT : List ℕ := [1, 1, 1, 1]
def coT : List ℕ := [1, 1, 1, 1]
def flLT : List ℕ := [0, 0, 0, 0]
def flRT : List ℕ := [13, 7, 13, 7]

def V (t : ℕ) (i : ℤ) : Bool :=
  if i < -(t : ℤ) ∨ (t : ℤ) < i then bgT.getD ((t - 10) % 4) false
  else if i + t ≤ 0 then (elT.getD ((t - 10) % 4) 0).testBit (i + t).toNat
  else if (t : ℤ) - i ≤ 0 then (erT.getD ((t - 10) % 4) 0).testBit ((t : ℤ) - i).toNat
  else if -(0 : ℤ) ≤ i ∧ i ≤ 0 then (coT.getD ((t - 10) % 4) 0).testBit (i + 0).toNat
  else if i < 0 then (flLT.getD ((t - 10) % 4) 0).testBit ((i + t) % 4).toNat
  else (flRT.getD ((t - 10) % 4) 0).testBit (((t : ℤ) - i) % 4).toNat

lemma V_out (t : ℕ) (i : ℤ) (h : i < -(t : ℤ) ∨ (t : ℤ) < i) :
    V t i = bgT.getD ((t - 10) % 4) false := by
  unfold V; rw [if_pos h]

lemma V_el (t : ℕ) (ht : 10 ≤ t) (i : ℤ) (j : ℕ) (hj : i + t = j) (hjA : j ≤ 0) :
    V t i = (elT.getD ((t - 10) % 4) 0).testBit j := by
  unfold V
  rw [if_neg (by omega), if_pos (by omega)]
  congr 1
  omega

lemma V_er (t : ℕ) (ht : 10 ≤ t) (i : ℤ) (j : ℕ) (hj : (t : ℤ) - i = j) (hjA : j ≤ 0) :
    V t i = (erT.getD ((t - 10) % 4) 0).testBit j := by
  unfold V
  rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)]
  congr 1
  omega

lemma V_co (t : ℕ) (ht : 10 ≤ t) (i : ℤ) (m : ℕ) (hm : i + 0 = m) (hmK : m ≤ 2 * 0) :
    V t i = (coT.getD ((t - 10) % 4) 0).testBit m := by
  unfold V
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]
  congr 1
  omega

lemma V_fll (t : ℕ) (ht : 10 ≤ t) (i : ℤ) (s : ℕ) (hs : (i + t) % 4 = s)
    (h1 : (0 : ℤ) < i + t) (h3 : i < -(0 : ℤ)) :
    V t i = (flLT.getD ((t - 10) % 4) 0).testBit s := by
  unfold V
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]
  congr 1
  omega

lemma V_flr (t : ℕ) (ht : 10 ≤ t) (i : ℤ) (s : ℕ) (hs : ((t : ℤ) - i) % 4 = s)
    (h2 : (0 : ℤ) < (t : ℤ) - i) (h3 : (0 : ℤ) < i) :
    V t i = (flRT.getD ((t - 10) % 4) 0).testBit s := by
  unfold V
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  congr 1
  omega


set_option maxHeartbeats 16000000 in
lemma stepV (t : ℕ) (ht : 10 ≤ t) (i : ℤ) :
    rule (V t (i - 1)) (V t i) (V t (i + 1)) = V (t + 1) i := by
  obtain ⟨q, hq, hqq⟩ : ∃ q, q < 4 ∧ (t - 10) % 4 = q := ⟨_, Nat.mod_lt _ (by norm_num), rfl⟩
  have hq1 : (t + 1 - 10) % 4 = (q + 1) % 4 := by omega
  interval_cases q
  · rcases (by omega : (i ≤ -(t : ℤ) - 3) ∨ (i = -(t : ℤ) - 2) ∨ (i + t + 1 = 0) ∨ (i + t + 1 = 1) ∨ (i + t + 1 = 2) ∨ (2 < i + t + 1 ∧ i < -0 - 1) ∨ (i = -1) ∨ (i = 0) ∨ (i = 1) ∨ (0 + 1 < i ∧ 2 < (t : ℤ) + 1 - i) ∨ ((t : ℤ) + 1 - i = 2) ∨ ((t : ℤ) + 1 - i = 1) ∨ ((t : ℤ) + 1 - i = 0) ∨ (i = (t : ℤ) + 2) ∨ ((t : ℤ) + 3 ≤ i)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · rw [V_out t (i - 1) (by push_cast; omega), V_out t i (by push_cast; omega), V_out t (i + 1) (by push_cast; omega), V_out (t + 1) i (by push_cast; omega), hqq, hq1]
      decide
    · rw [V_out t (i - 1) (by push_cast; omega), V_out t i (by push_cast; omega), V_out t (i + 1) (by push_cast; omega), V_out (t + 1) i (by push_cast; omega), hqq, hq1]
      decide
    · rw [V_out t (i - 1) (by push_cast; omega), V_out t i (by push_cast; omega), V_el t ht (i + 1) 0 (by omega) (by norm_num), V_el (t + 1) (by omega) i 0 (by push_cast; omega) (by norm_num), hqq, hq1]
      decide
    · rw [V_out t (i - 1) (by push_cast; omega), V_el t ht i 0 (by omega) (by norm_num), V_fll t ht (i + 1) 1 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 1 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
      decide
    · rw [V_el t ht (i - 1) 0 (by omega) (by norm_num), V_fll t ht i 1 (by omega) (by omega) (by omega), V_fll t ht (i + 1) 2 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 2 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
      decide
    · obtain ⟨e, he0, he1, hee⟩ : ∃ e : ℤ, 0 ≤ e ∧ e < 4 ∧ (i + t + 1) % 4 = e :=
        ⟨_, by omega, by omega, rfl⟩
      interval_cases e
      · rw [V_fll t ht (i - 1) 2 (by omega) (by omega) (by omega), V_fll t ht i 3 (by omega) (by omega) (by omega), V_fll t ht (i + 1) 0 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 0 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_fll t ht (i - 1) 3 (by omega) (by omega) (by omega), V_fll t ht i 0 (by omega) (by omega) (by omega), V_fll t ht (i + 1) 1 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 1 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_fll t ht (i - 1) 0 (by omega) (by omega) (by omega), V_fll t ht i 1 (by omega) (by omega) (by omega), V_fll t ht (i + 1) 2 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 2 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_fll t ht (i - 1) 1 (by omega) (by omega) (by omega), V_fll t ht i 2 (by omega) (by omega) (by omega), V_fll t ht (i + 1) 3 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 3 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
    · rw [V_fll t ht (i - 1) 0 (by omega) (by omega) (by omega), V_fll t ht i 1 (by omega) (by omega) (by omega), V_co t ht (i + 1) 0 (by omega) (by norm_num), V_fll (t + 1) (by omega) i 2 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
      decide
    · rw [V_fll t ht (i - 1) 1 (by omega) (by omega) (by omega), V_co t ht i 0 (by omega) (by norm_num), V_flr t ht (i + 1) 1 (by omega) (by omega) (by omega), V_co (t + 1) (by omega) i 0 (by omega) (by norm_num), hqq, hq1]
      decide
    · rw [V_co t ht (i - 1) 0 (by omega) (by norm_num), V_flr t ht i 1 (by omega) (by omega) (by omega), V_flr t ht (i + 1) 0 (by omega) (by omega) (by omega), V_flr (t + 1) (by omega) i 2 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
      decide
    · obtain ⟨e, he0, he1, hee⟩ : ∃ e : ℤ, 0 ≤ e ∧ e < 4 ∧ ((t : ℤ) + 1 - i) % 4 = e :=
        ⟨_, by omega, by omega, rfl⟩
      interval_cases e
      · rw [V_flr t ht (i - 1) 0 (by omega) (by omega) (by omega), V_flr t ht i 3 (by omega) (by omega) (by omega), V_flr t ht (i + 1) 2 (by omega) (by omega) (by omega), V_flr (t + 1) (by omega) i 0 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_flr t ht (i - 1) 1 (by omega) (by omega) (by omega), V_flr t ht i 0 (by omega) (by omega) (by omega), V_flr t ht (i + 1) 3 (by omega) (by omega) (by omega), V_flr (t + 1) (by omega) i 1 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_flr t ht (i - 1) 2 (by omega) (by omega) (by omega), V_flr t ht i 1 (by omega) (by omega) (by omega), V_flr t ht (i + 1) 0 (by omega) (by omega) (by omega), V_flr (t + 1) (by omega) i 2 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_flr t ht (i - 1) 3 (by omega) (by omega) (by omega), V_flr t ht i 2 (by omega) (by omega) (by omega), V_flr t ht (i + 1) 1 (by omega) (by omega) (by omega), V_flr (t + 1) (by omega) i 3 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
    · rw [V_flr t ht (i - 1) 2 (by omega) (by omega) (by omega), V_flr t ht i 1 (by omega) (by omega) (by omega), V_er t ht (i + 1) 0 (by omega) (by norm_num), V_flr (t + 1) (by omega) i 2 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
      decide
    · rw [V_flr t ht (i - 1) 1 (by omega) (by omega) (by omega), V_er t ht i 0 (by omega) (by norm_num), V_out t (i + 1) (by push_cast; omega), V_flr (t + 1) (by omega) i 1 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
      decide
    · rw [V_er t ht (i - 1) 0 (by omega) (by norm_num), V_out t i (by push_cast; omega), V_out t (i + 1) (by push_cast; omega), V_er (t + 1) (by omega) i 0 (by push_cast; omega) (by norm_num), hqq, hq1]
      decide
    · rw [V_out t (i - 1) (by push_cast; omega), V_out t i (by push_cast; omega), V_out t (i + 1) (by push_cast; omega), V_out (t + 1) i (by push_cast; omega), hqq, hq1]
      decide
    · rw [V_out t (i - 1) (by push_cast; omega), V_out t i (by push_cast; omega), V_out t (i + 1) (by push_cast; omega), V_out (t + 1) i (by push_cast; omega), hqq, hq1]
      decide
  · rcases (by omega : (i ≤ -(t : ℤ) - 3) ∨ (i = -(t : ℤ) - 2) ∨ (i + t + 1 = 0) ∨ (i + t + 1 = 1) ∨ (i + t + 1 = 2) ∨ (2 < i + t + 1 ∧ i < -0 - 1) ∨ (i = -1) ∨ (i = 0) ∨ (i = 1) ∨ (0 + 1 < i ∧ 2 < (t : ℤ) + 1 - i) ∨ ((t : ℤ) + 1 - i = 2) ∨ ((t : ℤ) + 1 - i = 1) ∨ ((t : ℤ) + 1 - i = 0) ∨ (i = (t : ℤ) + 2) ∨ ((t : ℤ) + 3 ≤ i)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · rw [V_out t (i - 1) (by push_cast; omega), V_out t i (by push_cast; omega), V_out t (i + 1) (by push_cast; omega), V_out (t + 1) i (by push_cast; omega), hqq, hq1]
      decide
    · rw [V_out t (i - 1) (by push_cast; omega), V_out t i (by push_cast; omega), V_out t (i + 1) (by push_cast; omega), V_out (t + 1) i (by push_cast; omega), hqq, hq1]
      decide
    · rw [V_out t (i - 1) (by push_cast; omega), V_out t i (by push_cast; omega), V_el t ht (i + 1) 0 (by omega) (by norm_num), V_el (t + 1) (by omega) i 0 (by push_cast; omega) (by norm_num), hqq, hq1]
      decide
    · rw [V_out t (i - 1) (by push_cast; omega), V_el t ht i 0 (by omega) (by norm_num), V_fll t ht (i + 1) 1 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 1 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
      decide
    · rw [V_el t ht (i - 1) 0 (by omega) (by norm_num), V_fll t ht i 1 (by omega) (by omega) (by omega), V_fll t ht (i + 1) 2 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 2 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
      decide
    · obtain ⟨e, he0, he1, hee⟩ : ∃ e : ℤ, 0 ≤ e ∧ e < 4 ∧ (i + t + 1) % 4 = e :=
        ⟨_, by omega, by omega, rfl⟩
      interval_cases e
      · rw [V_fll t ht (i - 1) 2 (by omega) (by omega) (by omega), V_fll t ht i 3 (by omega) (by omega) (by omega), V_fll t ht (i + 1) 0 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 0 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_fll t ht (i - 1) 3 (by omega) (by omega) (by omega), V_fll t ht i 0 (by omega) (by omega) (by omega), V_fll t ht (i + 1) 1 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 1 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_fll t ht (i - 1) 0 (by omega) (by omega) (by omega), V_fll t ht i 1 (by omega) (by omega) (by omega), V_fll t ht (i + 1) 2 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 2 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_fll t ht (i - 1) 1 (by omega) (by omega) (by omega), V_fll t ht i 2 (by omega) (by omega) (by omega), V_fll t ht (i + 1) 3 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 3 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
    · rw [V_fll t ht (i - 1) 1 (by omega) (by omega) (by omega), V_fll t ht i 2 (by omega) (by omega) (by omega), V_co t ht (i + 1) 0 (by omega) (by norm_num), V_fll (t + 1) (by omega) i 3 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
      decide
    · rw [V_fll t ht (i - 1) 2 (by omega) (by omega) (by omega), V_co t ht i 0 (by omega) (by norm_num), V_flr t ht (i + 1) 2 (by omega) (by omega) (by omega), V_co (t + 1) (by omega) i 0 (by omega) (by norm_num), hqq, hq1]
      decide
    · rw [V_co t ht (i - 1) 0 (by omega) (by norm_num), V_flr t ht i 2 (by omega) (by omega) (by omega), V_flr t ht (i + 1) 1 (by omega) (by omega) (by omega), V_flr (t + 1) (by omega) i 3 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
      decide
    · obtain ⟨e, he0, he1, hee⟩ : ∃ e : ℤ, 0 ≤ e ∧ e < 4 ∧ ((t : ℤ) + 1 - i) % 4 = e :=
        ⟨_, by omega, by omega, rfl⟩
      interval_cases e
      · rw [V_flr t ht (i - 1) 0 (by omega) (by omega) (by omega), V_flr t ht i 3 (by omega) (by omega) (by omega), V_flr t ht (i + 1) 2 (by omega) (by omega) (by omega), V_flr (t + 1) (by omega) i 0 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_flr t ht (i - 1) 1 (by omega) (by omega) (by omega), V_flr t ht i 0 (by omega) (by omega) (by omega), V_flr t ht (i + 1) 3 (by omega) (by omega) (by omega), V_flr (t + 1) (by omega) i 1 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_flr t ht (i - 1) 2 (by omega) (by omega) (by omega), V_flr t ht i 1 (by omega) (by omega) (by omega), V_flr t ht (i + 1) 0 (by omega) (by omega) (by omega), V_flr (t + 1) (by omega) i 2 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_flr t ht (i - 1) 3 (by omega) (by omega) (by omega), V_flr t ht i 2 (by omega) (by omega) (by omega), V_flr t ht (i + 1) 1 (by omega) (by omega) (by omega), V_flr (t + 1) (by omega) i 3 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
    · rw [V_flr t ht (i - 1) 2 (by omega) (by omega) (by omega), V_flr t ht i 1 (by omega) (by omega) (by omega), V_er t ht (i + 1) 0 (by omega) (by norm_num), V_flr (t + 1) (by omega) i 2 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
      decide
    · rw [V_flr t ht (i - 1) 1 (by omega) (by omega) (by omega), V_er t ht i 0 (by omega) (by norm_num), V_out t (i + 1) (by push_cast; omega), V_flr (t + 1) (by omega) i 1 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
      decide
    · rw [V_er t ht (i - 1) 0 (by omega) (by norm_num), V_out t i (by push_cast; omega), V_out t (i + 1) (by push_cast; omega), V_er (t + 1) (by omega) i 0 (by push_cast; omega) (by norm_num), hqq, hq1]
      decide
    · rw [V_out t (i - 1) (by push_cast; omega), V_out t i (by push_cast; omega), V_out t (i + 1) (by push_cast; omega), V_out (t + 1) i (by push_cast; omega), hqq, hq1]
      decide
    · rw [V_out t (i - 1) (by push_cast; omega), V_out t i (by push_cast; omega), V_out t (i + 1) (by push_cast; omega), V_out (t + 1) i (by push_cast; omega), hqq, hq1]
      decide
  · rcases (by omega : (i ≤ -(t : ℤ) - 3) ∨ (i = -(t : ℤ) - 2) ∨ (i + t + 1 = 0) ∨ (i + t + 1 = 1) ∨ (i + t + 1 = 2) ∨ (2 < i + t + 1 ∧ i < -0 - 1) ∨ (i = -1) ∨ (i = 0) ∨ (i = 1) ∨ (0 + 1 < i ∧ 2 < (t : ℤ) + 1 - i) ∨ ((t : ℤ) + 1 - i = 2) ∨ ((t : ℤ) + 1 - i = 1) ∨ ((t : ℤ) + 1 - i = 0) ∨ (i = (t : ℤ) + 2) ∨ ((t : ℤ) + 3 ≤ i)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · rw [V_out t (i - 1) (by push_cast; omega), V_out t i (by push_cast; omega), V_out t (i + 1) (by push_cast; omega), V_out (t + 1) i (by push_cast; omega), hqq, hq1]
      decide
    · rw [V_out t (i - 1) (by push_cast; omega), V_out t i (by push_cast; omega), V_out t (i + 1) (by push_cast; omega), V_out (t + 1) i (by push_cast; omega), hqq, hq1]
      decide
    · rw [V_out t (i - 1) (by push_cast; omega), V_out t i (by push_cast; omega), V_el t ht (i + 1) 0 (by omega) (by norm_num), V_el (t + 1) (by omega) i 0 (by push_cast; omega) (by norm_num), hqq, hq1]
      decide
    · rw [V_out t (i - 1) (by push_cast; omega), V_el t ht i 0 (by omega) (by norm_num), V_fll t ht (i + 1) 1 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 1 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
      decide
    · rw [V_el t ht (i - 1) 0 (by omega) (by norm_num), V_fll t ht i 1 (by omega) (by omega) (by omega), V_fll t ht (i + 1) 2 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 2 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
      decide
    · obtain ⟨e, he0, he1, hee⟩ : ∃ e : ℤ, 0 ≤ e ∧ e < 4 ∧ (i + t + 1) % 4 = e :=
        ⟨_, by omega, by omega, rfl⟩
      interval_cases e
      · rw [V_fll t ht (i - 1) 2 (by omega) (by omega) (by omega), V_fll t ht i 3 (by omega) (by omega) (by omega), V_fll t ht (i + 1) 0 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 0 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_fll t ht (i - 1) 3 (by omega) (by omega) (by omega), V_fll t ht i 0 (by omega) (by omega) (by omega), V_fll t ht (i + 1) 1 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 1 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_fll t ht (i - 1) 0 (by omega) (by omega) (by omega), V_fll t ht i 1 (by omega) (by omega) (by omega), V_fll t ht (i + 1) 2 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 2 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_fll t ht (i - 1) 1 (by omega) (by omega) (by omega), V_fll t ht i 2 (by omega) (by omega) (by omega), V_fll t ht (i + 1) 3 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 3 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
    · rw [V_fll t ht (i - 1) 2 (by omega) (by omega) (by omega), V_fll t ht i 3 (by omega) (by omega) (by omega), V_co t ht (i + 1) 0 (by omega) (by norm_num), V_fll (t + 1) (by omega) i 0 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
      decide
    · rw [V_fll t ht (i - 1) 3 (by omega) (by omega) (by omega), V_co t ht i 0 (by omega) (by norm_num), V_flr t ht (i + 1) 3 (by omega) (by omega) (by omega), V_co (t + 1) (by omega) i 0 (by omega) (by norm_num), hqq, hq1]
      decide
    · rw [V_co t ht (i - 1) 0 (by omega) (by norm_num), V_flr t ht i 3 (by omega) (by omega) (by omega), V_flr t ht (i + 1) 2 (by omega) (by omega) (by omega), V_flr (t + 1) (by omega) i 0 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
      decide
    · obtain ⟨e, he0, he1, hee⟩ : ∃ e : ℤ, 0 ≤ e ∧ e < 4 ∧ ((t : ℤ) + 1 - i) % 4 = e :=
        ⟨_, by omega, by omega, rfl⟩
      interval_cases e
      · rw [V_flr t ht (i - 1) 0 (by omega) (by omega) (by omega), V_flr t ht i 3 (by omega) (by omega) (by omega), V_flr t ht (i + 1) 2 (by omega) (by omega) (by omega), V_flr (t + 1) (by omega) i 0 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_flr t ht (i - 1) 1 (by omega) (by omega) (by omega), V_flr t ht i 0 (by omega) (by omega) (by omega), V_flr t ht (i + 1) 3 (by omega) (by omega) (by omega), V_flr (t + 1) (by omega) i 1 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_flr t ht (i - 1) 2 (by omega) (by omega) (by omega), V_flr t ht i 1 (by omega) (by omega) (by omega), V_flr t ht (i + 1) 0 (by omega) (by omega) (by omega), V_flr (t + 1) (by omega) i 2 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_flr t ht (i - 1) 3 (by omega) (by omega) (by omega), V_flr t ht i 2 (by omega) (by omega) (by omega), V_flr t ht (i + 1) 1 (by omega) (by omega) (by omega), V_flr (t + 1) (by omega) i 3 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
    · rw [V_flr t ht (i - 1) 2 (by omega) (by omega) (by omega), V_flr t ht i 1 (by omega) (by omega) (by omega), V_er t ht (i + 1) 0 (by omega) (by norm_num), V_flr (t + 1) (by omega) i 2 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
      decide
    · rw [V_flr t ht (i - 1) 1 (by omega) (by omega) (by omega), V_er t ht i 0 (by omega) (by norm_num), V_out t (i + 1) (by push_cast; omega), V_flr (t + 1) (by omega) i 1 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
      decide
    · rw [V_er t ht (i - 1) 0 (by omega) (by norm_num), V_out t i (by push_cast; omega), V_out t (i + 1) (by push_cast; omega), V_er (t + 1) (by omega) i 0 (by push_cast; omega) (by norm_num), hqq, hq1]
      decide
    · rw [V_out t (i - 1) (by push_cast; omega), V_out t i (by push_cast; omega), V_out t (i + 1) (by push_cast; omega), V_out (t + 1) i (by push_cast; omega), hqq, hq1]
      decide
    · rw [V_out t (i - 1) (by push_cast; omega), V_out t i (by push_cast; omega), V_out t (i + 1) (by push_cast; omega), V_out (t + 1) i (by push_cast; omega), hqq, hq1]
      decide
  · rcases (by omega : (i ≤ -(t : ℤ) - 3) ∨ (i = -(t : ℤ) - 2) ∨ (i + t + 1 = 0) ∨ (i + t + 1 = 1) ∨ (i + t + 1 = 2) ∨ (2 < i + t + 1 ∧ i < -0 - 1) ∨ (i = -1) ∨ (i = 0) ∨ (i = 1) ∨ (0 + 1 < i ∧ 2 < (t : ℤ) + 1 - i) ∨ ((t : ℤ) + 1 - i = 2) ∨ ((t : ℤ) + 1 - i = 1) ∨ ((t : ℤ) + 1 - i = 0) ∨ (i = (t : ℤ) + 2) ∨ ((t : ℤ) + 3 ≤ i)) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · rw [V_out t (i - 1) (by push_cast; omega), V_out t i (by push_cast; omega), V_out t (i + 1) (by push_cast; omega), V_out (t + 1) i (by push_cast; omega), hqq, hq1]
      decide
    · rw [V_out t (i - 1) (by push_cast; omega), V_out t i (by push_cast; omega), V_out t (i + 1) (by push_cast; omega), V_out (t + 1) i (by push_cast; omega), hqq, hq1]
      decide
    · rw [V_out t (i - 1) (by push_cast; omega), V_out t i (by push_cast; omega), V_el t ht (i + 1) 0 (by omega) (by norm_num), V_el (t + 1) (by omega) i 0 (by push_cast; omega) (by norm_num), hqq, hq1]
      decide
    · rw [V_out t (i - 1) (by push_cast; omega), V_el t ht i 0 (by omega) (by norm_num), V_fll t ht (i + 1) 1 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 1 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
      decide
    · rw [V_el t ht (i - 1) 0 (by omega) (by norm_num), V_fll t ht i 1 (by omega) (by omega) (by omega), V_fll t ht (i + 1) 2 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 2 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
      decide
    · obtain ⟨e, he0, he1, hee⟩ : ∃ e : ℤ, 0 ≤ e ∧ e < 4 ∧ (i + t + 1) % 4 = e :=
        ⟨_, by omega, by omega, rfl⟩
      interval_cases e
      · rw [V_fll t ht (i - 1) 2 (by omega) (by omega) (by omega), V_fll t ht i 3 (by omega) (by omega) (by omega), V_fll t ht (i + 1) 0 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 0 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_fll t ht (i - 1) 3 (by omega) (by omega) (by omega), V_fll t ht i 0 (by omega) (by omega) (by omega), V_fll t ht (i + 1) 1 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 1 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_fll t ht (i - 1) 0 (by omega) (by omega) (by omega), V_fll t ht i 1 (by omega) (by omega) (by omega), V_fll t ht (i + 1) 2 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 2 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_fll t ht (i - 1) 1 (by omega) (by omega) (by omega), V_fll t ht i 2 (by omega) (by omega) (by omega), V_fll t ht (i + 1) 3 (by omega) (by omega) (by omega), V_fll (t + 1) (by omega) i 3 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
    · rw [V_fll t ht (i - 1) 3 (by omega) (by omega) (by omega), V_fll t ht i 0 (by omega) (by omega) (by omega), V_co t ht (i + 1) 0 (by omega) (by norm_num), V_fll (t + 1) (by omega) i 1 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
      decide
    · rw [V_fll t ht (i - 1) 0 (by omega) (by omega) (by omega), V_co t ht i 0 (by omega) (by norm_num), V_flr t ht (i + 1) 0 (by omega) (by omega) (by omega), V_co (t + 1) (by omega) i 0 (by omega) (by norm_num), hqq, hq1]
      decide
    · rw [V_co t ht (i - 1) 0 (by omega) (by norm_num), V_flr t ht i 0 (by omega) (by omega) (by omega), V_flr t ht (i + 1) 3 (by omega) (by omega) (by omega), V_flr (t + 1) (by omega) i 1 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
      decide
    · obtain ⟨e, he0, he1, hee⟩ : ∃ e : ℤ, 0 ≤ e ∧ e < 4 ∧ ((t : ℤ) + 1 - i) % 4 = e :=
        ⟨_, by omega, by omega, rfl⟩
      interval_cases e
      · rw [V_flr t ht (i - 1) 0 (by omega) (by omega) (by omega), V_flr t ht i 3 (by omega) (by omega) (by omega), V_flr t ht (i + 1) 2 (by omega) (by omega) (by omega), V_flr (t + 1) (by omega) i 0 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_flr t ht (i - 1) 1 (by omega) (by omega) (by omega), V_flr t ht i 0 (by omega) (by omega) (by omega), V_flr t ht (i + 1) 3 (by omega) (by omega) (by omega), V_flr (t + 1) (by omega) i 1 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_flr t ht (i - 1) 2 (by omega) (by omega) (by omega), V_flr t ht i 1 (by omega) (by omega) (by omega), V_flr t ht (i + 1) 0 (by omega) (by omega) (by omega), V_flr (t + 1) (by omega) i 2 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
      · rw [V_flr t ht (i - 1) 3 (by omega) (by omega) (by omega), V_flr t ht i 2 (by omega) (by omega) (by omega), V_flr t ht (i + 1) 1 (by omega) (by omega) (by omega), V_flr (t + 1) (by omega) i 3 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
        decide
    · rw [V_flr t ht (i - 1) 2 (by omega) (by omega) (by omega), V_flr t ht i 1 (by omega) (by omega) (by omega), V_er t ht (i + 1) 0 (by omega) (by norm_num), V_flr (t + 1) (by omega) i 2 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
      decide
    · rw [V_flr t ht (i - 1) 1 (by omega) (by omega) (by omega), V_er t ht i 0 (by omega) (by norm_num), V_out t (i + 1) (by push_cast; omega), V_flr (t + 1) (by omega) i 1 (by push_cast; omega) (by push_cast; omega) (by omega), hqq, hq1]
      decide
    · rw [V_er t ht (i - 1) 0 (by omega) (by norm_num), V_out t i (by push_cast; omega), V_out t (i + 1) (by push_cast; omega), V_er (t + 1) (by omega) i 0 (by push_cast; omega) (by norm_num), hqq, hq1]
      decide
    · rw [V_out t (i - 1) (by push_cast; omega), V_out t i (by push_cast; omega), V_out t (i + 1) (by push_cast; omega), V_out (t + 1) i (by push_cast; omega), hqq, hq1]
      decide
    · rw [V_out t (i - 1) (by push_cast; omega), V_out t i (by push_cast; omega), V_out t (i + 1) (by push_cast; omega), V_out (t + 1) i (by push_cast; omega), hqq, hq1]
      decide

lemma base_ok : (∀ j < 2 * W + 1, decode (stages.getD 10 default) ((j : ℤ) - W) = V 10 ((j : ℤ) - W)) ∧
    (stages.getD 10 default).1 = bgT.getD 0 false := by
  decide +kernel

lemma pattern (t : ℕ) (ht : 10 ≤ t) : ∀ i, cstate t i = V t i := by
  induction t, ht using Nat.le_induction with
  | base =>
    intro i
    rw [(certified 10 le_rfl).2 i]
    by_cases hw : -(W : ℤ) ≤ i ∧ i ≤ W
    · obtain ⟨j, hj, rfl⟩ := in_window i hw
      exact base_ok.1 j hj
    · unfold decode
      rw [if_neg hw, base_ok.2, V_out 10 i (by unfold W at hw; omega)]
  | succ t ht ih =>
    intro i
    show rule (cstate t (i - 1)) (cstate t i) (cstate t (i + 1)) = _
    rw [ih, ih, ih, stepV t ht i]

lemma sim_V (t : ℕ) (ht : t ≤ 10) : sim t = cstate t := funext fun i => ((certified t ht).2 i).symm

lemma state_eq_V (t : ℕ) (ht : 10 ≤ t) : cstate t = V t := funext (pattern t ht)

def rowOf (t : ℕ) : ℤ → Bool := if t ≤ 10 then sim t else V t

lemma state_eq (t : ℕ) : cstate t = rowOf t := by
  unfold rowOf
  split_ifs with h
  · exact (sim_V t h).symm
  · exact state_eq_V t (by omega)

def aSim (n : ℕ) : ℕ :=
  ∑ t ∈ Finset.range (n + 1), ∑ k ∈ Finset.range (2 * t + 1), if rowOf t ((k : ℤ) - t) then 0 else 1

lemma a_eq (n : ℕ) : ca n = aSim n := by
  unfold ca aSim
  simp only [state_eq]

/-- The values a(0..26); the listed terms are among them (control). -/
lemma vals : ∀ n ≤ 26, ca n = ([0, 1, 4, 7, 12, 18, 26, 34, 44, 55, 68, 81, 96, 112, 130, 148, 168, 189, 212, 235, 260, 286, 314, 342, 372, 403, 436] : List ℕ).getD n 0 := by
  intro n hn
  rw [a_eq n]
  revert n
  decide +kernel

lemma v0 : ca 0 = 0 := vals 0 (by norm_num)
lemma v1 : ca 1 = 1 := vals 1 (by norm_num)
lemma v2 : ca 2 = 4 := vals 2 (by norm_num)
lemma v3 : ca 3 = 7 := vals 3 (by norm_num)
lemma v4 : ca 4 = 12 := vals 4 (by norm_num)
lemma v5 : ca 5 = 18 := vals 5 (by norm_num)
lemma v6 : ca 6 = 26 := vals 6 (by norm_num)
lemma v7 : ca 7 = 34 := vals 7 (by norm_num)
lemma v8 : ca 8 = 44 := vals 8 (by norm_num)
lemma v9 : ca 9 = 55 := vals 9 (by norm_num)
lemma v10 : ca 10 = 68 := vals 10 (by norm_num)
lemma v11 : ca 11 = 81 := vals 11 (by norm_num)
lemma v12 : ca 12 = 96 := vals 12 (by norm_num)
lemma v13 : ca 13 = 112 := vals 13 (by norm_num)
lemma v14 : ca 14 = 130 := vals 14 (by norm_num)
lemma v15 : ca 15 = 148 := vals 15 (by norm_num)
lemma v16 : ca 16 = 168 := vals 16 (by norm_num)
lemma v17 : ca 17 = 189 := vals 17 (by norm_num)
lemma v18 : ca 18 = 212 := vals 18 (by norm_num)
lemma v19 : ca 19 = 235 := vals 19 (by norm_num)
lemma v20 : ca 20 = 260 := vals 20 (by norm_num)
lemma v21 : ca 21 = 286 := vals 21 (by norm_num)
lemma v22 : ca 22 = 314 := vals 22 (by norm_num)
lemma v23 : ca 23 = 342 := vals 23 (by norm_num)
lemma v24 : ca 24 = 372 := vals 24 (by norm_num)
lemma v25 : ca 25 = 403 := vals 25 (by norm_num)
lemma v26 : ca 26 = 436 := vals 26 (by norm_num)

/-- The number of OFF cells among `-n..n` in row `n`. -/
def cnt1 (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (2 * n + 1), if cstate n ((k : ℤ) - n) then 0 else 1


lemma per_sum (f : ℕ → ℕ) (c m : ℕ) :
    ∑ k ∈ Finset.range (4 * m), f ((c + k) % 4) = m * ∑ j ∈ Finset.range 4, f ((c + j) % 4) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 4 * (m + 1) = 4 * m + 4 by ring, Finset.sum_range_add, ih]
    have h : ∀ j ∈ Finset.range 4, f ((c + (4 * m + j)) % 4) = f ((c + j) % 4) := by
      intro j _; congr 1; omega
    rw [Finset.sum_congr rfl h]
    ring


set_option maxHeartbeats 4000000 in
lemma cnt_split (n : ℕ) (hn : 10 ≤ n) :
    cnt1 n = (∑ k ∈ Finset.range 1, (if (elT.getD ((n - 10) % 4) 0).testBit k then 0 else 1)) +
      (∑ k ∈ Finset.range (n - 1), (if (flLT.getD ((n - 10) % 4) 0).testBit ((1 + k) % 4) then 0 else 1)) +
      (∑ k ∈ Finset.range 1, (if (coT.getD ((n - 10) % 4) 0).testBit k then 0 else 1)) +
      (∑ k ∈ Finset.range (n - 1), (if (flRT.getD ((n - 10) % 4) 0).testBit ((1 + k) % 4) then 0 else 1)) +
      (∑ k ∈ Finset.range 1, (if (erT.getD ((n - 10) % 4) 0).testBit (0 - k) then 0 else 1)) := by
  unfold cnt1
  rw [state_eq_V n hn]
  rw [show 2 * n + 1 = 1 + (n - 1) + 1 + (n - 1) + 1 by omega]
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
    rw [V_fll n hn _ ((1 + k) % 4) (by push_cast; omega) (by push_cast; omega) (by push_cast; omega)]
  · refine Finset.sum_congr rfl fun k hk => ?_
    have hk' := Finset.mem_range.mp hk
    rw [V_co n hn _ k (by push_cast; omega) (by omega)]
  · rw [← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' := Finset.mem_range.mp hk
    rw [V_flr n hn _ ((1 + k) % 4) (by push_cast; omega) (by push_cast; omega) (by push_cast; omega)]
  · refine Finset.sum_congr rfl fun k hk => ?_
    have hk' := Finset.mem_range.mp hk
    rw [V_er n hn _ (0 - k) (by push_cast; omega) (by omega)]


lemma cntn0 (n : ℕ) (h1 : 10 ≤ n) (h2 : n % 4 = 0) :
    (cnt1 n : ℚ) = ((5 : ℚ) / 4) * (n : ℚ) + (0 : ℚ) := by
  rw [cnt_split n h1, show (n - 10) % 4 = 2 by omega]
  have e1 : (∑ k ∈ Finset.range 1, (if (elT.getD 2 0).testBit k then 0 else 1)) = 1 := by decide
  have e3 : (∑ k ∈ Finset.range 1, (if (coT.getD 2 0).testBit k then 0 else 1)) = 0 := by decide
  have e5 : (∑ k ∈ Finset.range 1, (if (erT.getD 2 0).testBit (0 - k) then 0 else 1)) = 0 := by decide
  rw [e1, e3, e5]
  obtain ⟨m, rfl⟩ : ∃ m, n = 1 + (4 * m + 3) := ⟨(n - 1) / 4, by omega⟩
  rw [show 1 + (4 * m + 3) - 1 = 4 * m + 3 by omega, Finset.sum_range_add, Finset.sum_range_add]
  have hl := per_sum (fun s => if (flLT.getD 2 0).testBit s then 0 else 1) 1 m
  have hr := per_sum (fun s => if (flRT.getD 2 0).testBit s then 0 else 1) 1 m
  try simp only at hl hr
  rw [hl, hr]
  have gl : (∑ j ∈ Finset.range 4, (if (flLT.getD 2 0).testBit ((1 + j) % 4) then 0 else 1 : ℕ)) = 4 := by decide
  have gr : (∑ j ∈ Finset.range 4, (if (flRT.getD 2 0).testBit ((1 + j) % 4) then 0 else 1 : ℕ)) = 1 := by decide
  have tl : (∑ x ∈ Finset.range 3, (if (flLT.getD 2 0).testBit ((1 + (4 * m + x)) % 4) then 0 else 1 : ℕ)) = 3 := by
    rw [Finset.sum_congr rfl fun x _ => by rw [show (1 + (4 * m + x)) % 4 = (1 + x) % 4 by omega]]
    decide
  have tr : (∑ x ∈ Finset.range 3, (if (flRT.getD 2 0).testBit ((1 + (4 * m + x)) % 4) then 0 else 1 : ℕ)) = 1 := by
    rw [Finset.sum_congr rfl fun x _ => by rw [show (1 + (4 * m + x)) % 4 = (1 + x) % 4 by omega]]
    decide
  rw [gl, gr, tl, tr]
  push_cast
  ring


lemma cntn1 (n : ℕ) (h1 : 10 ≤ n) (h2 : n % 4 = 1) :
    (cnt1 n : ℚ) = ((5 : ℚ) / 4) * (n : ℚ) + ((-1 : ℚ) / 4) := by
  rw [cnt_split n h1, show (n - 10) % 4 = 3 by omega]
  have e1 : (∑ k ∈ Finset.range 1, (if (elT.getD 3 0).testBit k then 0 else 1)) = 1 := by decide
  have e3 : (∑ k ∈ Finset.range 1, (if (coT.getD 3 0).testBit k then 0 else 1)) = 0 := by decide
  have e5 : (∑ k ∈ Finset.range 1, (if (erT.getD 3 0).testBit (0 - k) then 0 else 1)) = 0 := by decide
  rw [e1, e3, e5]
  obtain ⟨m, rfl⟩ : ∃ m, n = 1 + (4 * m + 0) := ⟨(n - 1) / 4, by omega⟩
  rw [show 1 + (4 * m + 0) - 1 = 4 * m + 0 by omega, Finset.sum_range_add, Finset.sum_range_add]
  have hl := per_sum (fun s => if (flLT.getD 3 0).testBit s then 0 else 1) 1 m
  have hr := per_sum (fun s => if (flRT.getD 3 0).testBit s then 0 else 1) 1 m
  try simp only at hl hr
  rw [hl, hr]
  have gl : (∑ j ∈ Finset.range 4, (if (flLT.getD 3 0).testBit ((1 + j) % 4) then 0 else 1 : ℕ)) = 4 := by decide
  have gr : (∑ j ∈ Finset.range 4, (if (flRT.getD 3 0).testBit ((1 + j) % 4) then 0 else 1 : ℕ)) = 1 := by decide
  have tl : (∑ x ∈ Finset.range 0, (if (flLT.getD 3 0).testBit ((1 + (4 * m + x)) % 4) then 0 else 1 : ℕ)) = 0 := by
    rw [Finset.sum_congr rfl fun x _ => by rw [show (1 + (4 * m + x)) % 4 = (1 + x) % 4 by omega]]
    decide
  have tr : (∑ x ∈ Finset.range 0, (if (flRT.getD 3 0).testBit ((1 + (4 * m + x)) % 4) then 0 else 1 : ℕ)) = 0 := by
    rw [Finset.sum_congr rfl fun x _ => by rw [show (1 + (4 * m + x)) % 4 = (1 + x) % 4 by omega]]
    decide
  rw [gl, gr, tl, tr]
  push_cast
  ring


lemma cntn2 (n : ℕ) (h1 : 10 ≤ n) (h2 : n % 4 = 2) :
    (cnt1 n : ℚ) = ((5 : ℚ) / 4) * (n : ℚ) + ((1 : ℚ) / 2) := by
  rw [cnt_split n h1, show (n - 10) % 4 = 0 by omega]
  have e1 : (∑ k ∈ Finset.range 1, (if (elT.getD 0 0).testBit k then 0 else 1)) = 1 := by decide
  have e3 : (∑ k ∈ Finset.range 1, (if (coT.getD 0 0).testBit k then 0 else 1)) = 0 := by decide
  have e5 : (∑ k ∈ Finset.range 1, (if (erT.getD 0 0).testBit (0 - k) then 0 else 1)) = 0 := by decide
  rw [e1, e3, e5]
  obtain ⟨m, rfl⟩ : ∃ m, n = 1 + (4 * m + 1) := ⟨(n - 1) / 4, by omega⟩
  rw [show 1 + (4 * m + 1) - 1 = 4 * m + 1 by omega, Finset.sum_range_add, Finset.sum_range_add]
  have hl := per_sum (fun s => if (flLT.getD 0 0).testBit s then 0 else 1) 1 m
  have hr := per_sum (fun s => if (flRT.getD 0 0).testBit s then 0 else 1) 1 m
  try simp only at hl hr
  rw [hl, hr]
  have gl : (∑ j ∈ Finset.range 4, (if (flLT.getD 0 0).testBit ((1 + j) % 4) then 0 else 1 : ℕ)) = 4 := by decide
  have gr : (∑ j ∈ Finset.range 4, (if (flRT.getD 0 0).testBit ((1 + j) % 4) then 0 else 1 : ℕ)) = 1 := by decide
  have tl : (∑ x ∈ Finset.range 1, (if (flLT.getD 0 0).testBit ((1 + (4 * m + x)) % 4) then 0 else 1 : ℕ)) = 1 := by
    rw [Finset.sum_congr rfl fun x _ => by rw [show (1 + (4 * m + x)) % 4 = (1 + x) % 4 by omega]]
    decide
  have tr : (∑ x ∈ Finset.range 1, (if (flRT.getD 0 0).testBit ((1 + (4 * m + x)) % 4) then 0 else 1 : ℕ)) = 1 := by
    rw [Finset.sum_congr rfl fun x _ => by rw [show (1 + (4 * m + x)) % 4 = (1 + x) % 4 by omega]]
    decide
  rw [gl, gr, tl, tr]
  push_cast
  ring


lemma cntn3 (n : ℕ) (h1 : 10 ≤ n) (h2 : n % 4 = 3) :
    (cnt1 n : ℚ) = ((5 : ℚ) / 4) * (n : ℚ) + ((-3 : ℚ) / 4) := by
  rw [cnt_split n h1, show (n - 10) % 4 = 1 by omega]
  have e1 : (∑ k ∈ Finset.range 1, (if (elT.getD 1 0).testBit k then 0 else 1)) = 1 := by decide
  have e3 : (∑ k ∈ Finset.range 1, (if (coT.getD 1 0).testBit k then 0 else 1)) = 0 := by decide
  have e5 : (∑ k ∈ Finset.range 1, (if (erT.getD 1 0).testBit (0 - k) then 0 else 1)) = 0 := by decide
  rw [e1, e3, e5]
  obtain ⟨m, rfl⟩ : ∃ m, n = 1 + (4 * m + 2) := ⟨(n - 1) / 4, by omega⟩
  rw [show 1 + (4 * m + 2) - 1 = 4 * m + 2 by omega, Finset.sum_range_add, Finset.sum_range_add]
  have hl := per_sum (fun s => if (flLT.getD 1 0).testBit s then 0 else 1) 1 m
  have hr := per_sum (fun s => if (flRT.getD 1 0).testBit s then 0 else 1) 1 m
  try simp only at hl hr
  rw [hl, hr]
  have gl : (∑ j ∈ Finset.range 4, (if (flLT.getD 1 0).testBit ((1 + j) % 4) then 0 else 1 : ℕ)) = 4 := by decide
  have gr : (∑ j ∈ Finset.range 4, (if (flRT.getD 1 0).testBit ((1 + j) % 4) then 0 else 1 : ℕ)) = 1 := by decide
  have tl : (∑ x ∈ Finset.range 2, (if (flLT.getD 1 0).testBit ((1 + (4 * m + x)) % 4) then 0 else 1 : ℕ)) = 2 := by
    rw [Finset.sum_congr rfl fun x _ => by rw [show (1 + (4 * m + x)) % 4 = (1 + x) % 4 by omega]]
    decide
  have tr : (∑ x ∈ Finset.range 2, (if (flRT.getD 1 0).testBit ((1 + (4 * m + x)) % 4) then 0 else 1 : ℕ)) = 0 := by
    rw [Finset.sum_congr rfl fun x _ => by rw [show (1 + (4 * m + x)) % 4 = (1 + x) % 4 by omega]]
    decide
  rw [gl, gr, tl, tr]
  push_cast
  ring


lemma tstep (n : ℕ) : (ca (n + 4) : ℚ) = (ca n : ℚ) + ∑ j ∈ Finset.range 4, (cnt1 (n + 1 + j) : ℚ) := by
  show ((∑ t ∈ Finset.range (n + 4 + 1), cnt1 t : ℕ) : ℚ) =
    ((∑ t ∈ Finset.range (n + 1), cnt1 t : ℕ) : ℚ) + _
  rw [show n + 4 + 1 = (n + 1) + 4 by ring, Finset.sum_range_add]
  push_cast
  rfl


lemma cf0 (m : ℕ) : (ca (12 + 4 * m) : ℚ) = (0 : ℚ) * ((12 + 4 * m : ℕ) : ℚ) ^ 0 + ((1 : ℚ) / 2) * ((12 + 4 * m : ℕ) : ℚ) ^ 1 + ((5 : ℚ) / 8) * ((12 + 4 * m : ℕ) : ℚ) ^ 2 := by
  induction m with
  | zero =>
    rw [show 12 + 4 * 0 = 12 by ring, v12]
    norm_num
  | succ m ih =>
    rw [show 12 + 4 * (m + 1) = (12 + 4 * m) + 4 by ring, tstep]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    have e0 := cntn1 (12 + 4 * m + 1 + 0) (by omega) (by omega)
    have e1 := cntn2 (12 + 4 * m + 1 + 1) (by omega) (by omega)
    have e2 := cntn3 (12 + 4 * m + 1 + 2) (by omega) (by omega)
    have e3 := cntn0 (12 + 4 * m + 1 + 3) (by omega) (by omega)
    rw [ih, e0, e1, e2, e3]
    push_cast
    ring

lemma cfn0 (n : ℕ) (h1 : 10 ≤ n) (h2 : n % 4 = 0) : (ca n : ℚ) = (0 : ℚ) * (n : ℚ) ^ 0 + ((1 : ℚ) / 2) * (n : ℚ) ^ 1 + ((5 : ℚ) / 8) * (n : ℚ) ^ 2 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = 12 + 4 * m := ⟨(n - 12) / 4, by omega⟩
  exact cf0 m


lemma cf1 (m : ℕ) : (ca (13 + 4 * m) : ℚ) = ((-1 : ℚ) / 8) * ((13 + 4 * m : ℕ) : ℚ) ^ 0 + ((1 : ℚ) / 2) * ((13 + 4 * m : ℕ) : ℚ) ^ 1 + ((5 : ℚ) / 8) * ((13 + 4 * m : ℕ) : ℚ) ^ 2 := by
  induction m with
  | zero =>
    rw [show 13 + 4 * 0 = 13 by ring, v13]
    norm_num
  | succ m ih =>
    rw [show 13 + 4 * (m + 1) = (13 + 4 * m) + 4 by ring, tstep]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    have e0 := cntn2 (13 + 4 * m + 1 + 0) (by omega) (by omega)
    have e1 := cntn3 (13 + 4 * m + 1 + 1) (by omega) (by omega)
    have e2 := cntn0 (13 + 4 * m + 1 + 2) (by omega) (by omega)
    have e3 := cntn1 (13 + 4 * m + 1 + 3) (by omega) (by omega)
    rw [ih, e0, e1, e2, e3]
    push_cast
    ring

lemma cfn1 (n : ℕ) (h1 : 10 ≤ n) (h2 : n % 4 = 1) : (ca n : ℚ) = ((-1 : ℚ) / 8) * (n : ℚ) ^ 0 + ((1 : ℚ) / 2) * (n : ℚ) ^ 1 + ((5 : ℚ) / 8) * (n : ℚ) ^ 2 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = 13 + 4 * m := ⟨(n - 13) / 4, by omega⟩
  exact cf1 m


lemma cf2 (m : ℕ) : (ca (10 + 4 * m) : ℚ) = ((1 : ℚ) / 2) * ((10 + 4 * m : ℕ) : ℚ) ^ 0 + ((1 : ℚ) / 2) * ((10 + 4 * m : ℕ) : ℚ) ^ 1 + ((5 : ℚ) / 8) * ((10 + 4 * m : ℕ) : ℚ) ^ 2 := by
  induction m with
  | zero =>
    rw [show 10 + 4 * 0 = 10 by ring, v10]
    norm_num
  | succ m ih =>
    rw [show 10 + 4 * (m + 1) = (10 + 4 * m) + 4 by ring, tstep]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    have e0 := cntn3 (10 + 4 * m + 1 + 0) (by omega) (by omega)
    have e1 := cntn0 (10 + 4 * m + 1 + 1) (by omega) (by omega)
    have e2 := cntn1 (10 + 4 * m + 1 + 2) (by omega) (by omega)
    have e3 := cntn2 (10 + 4 * m + 1 + 3) (by omega) (by omega)
    rw [ih, e0, e1, e2, e3]
    push_cast
    ring

lemma cfn2 (n : ℕ) (h1 : 10 ≤ n) (h2 : n % 4 = 2) : (ca n : ℚ) = ((1 : ℚ) / 2) * (n : ℚ) ^ 0 + ((1 : ℚ) / 2) * (n : ℚ) ^ 1 + ((5 : ℚ) / 8) * (n : ℚ) ^ 2 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = 10 + 4 * m := ⟨(n - 10) / 4, by omega⟩
  exact cf2 m


lemma cf3 (m : ℕ) : (ca (11 + 4 * m) : ℚ) = ((-1 : ℚ) / 8) * ((11 + 4 * m : ℕ) : ℚ) ^ 0 + ((1 : ℚ) / 2) * ((11 + 4 * m : ℕ) : ℚ) ^ 1 + ((5 : ℚ) / 8) * ((11 + 4 * m : ℕ) : ℚ) ^ 2 := by
  induction m with
  | zero =>
    rw [show 11 + 4 * 0 = 11 by ring, v11]
    norm_num
  | succ m ih =>
    rw [show 11 + 4 * (m + 1) = (11 + 4 * m) + 4 by ring, tstep]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    have e0 := cntn0 (11 + 4 * m + 1 + 0) (by omega) (by omega)
    have e1 := cntn1 (11 + 4 * m + 1 + 1) (by omega) (by omega)
    have e2 := cntn2 (11 + 4 * m + 1 + 2) (by omega) (by omega)
    have e3 := cntn3 (11 + 4 * m + 1 + 3) (by omega) (by omega)
    rw [ih, e0, e1, e2, e3]
    push_cast
    ring

lemma cfn3 (n : ℕ) (h1 : 10 ≤ n) (h2 : n % 4 = 3) : (ca n : ℚ) = ((-1 : ℚ) / 8) * (n : ℚ) ^ 0 + ((1 : ℚ) / 2) * (n : ℚ) ^ 1 + ((5 : ℚ) / 8) * (n : ℚ) ^ 2 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = 11 + 4 * m := ⟨(n - 11) / 4, by omega⟩
  exact cf3 m


lemma gfrec0 (n : ℕ) (hn : 6 ≤ n) : (ca n : ℚ) = ((2 : ℚ)) * (ca (n - 1) : ℚ) + ((-1 : ℚ)) * (ca (n - 2) : ℚ) + ((1 : ℚ)) * (ca (n - 4) : ℚ) + ((-2 : ℚ)) * (ca (n - 5) : ℚ) + ((1 : ℚ)) * (ca (n - 6) : ℚ) := by
  rcases Nat.lt_or_ge n 16 with hlt | hge
  · interval_cases n <;> norm_num [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16] at *
  · rcases (by omega : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3) with hpar | hpar | hpar | hpar
    · obtain ⟨q, rfl⟩ : ∃ q, n = 16 + 4 * q := ⟨(n - 16) / 4, by omega⟩
      have c0 := cfn0 (16 + 4 * q) (by omega) (by omega)
      rw [show 16 + 4 * q - 1 = 15 + 4 * q by omega]
      have c1 := cfn3 (15 + 4 * q) (by omega) (by omega)
      rw [show 16 + 4 * q - 2 = 14 + 4 * q by omega]
      have c2 := cfn2 (14 + 4 * q) (by omega) (by omega)
      rw [show 16 + 4 * q - 4 = 12 + 4 * q by omega]
      have c4 := cfn0 (12 + 4 * q) (by omega) (by omega)
      rw [show 16 + 4 * q - 5 = 11 + 4 * q by omega]
      have c5 := cfn3 (11 + 4 * q) (by omega) (by omega)
      rw [show 16 + 4 * q - 6 = 10 + 4 * q by omega]
      have c6 := cfn2 (10 + 4 * q) (by omega) (by omega)
      try simp only [pow_add, mul_one, one_mul, show ∀ q : ℕ, ((-1 : ℚ)) ^ (4 * q) = 1 from fun q => by rw [pow_mul]; norm_num] at c0 c1 c2 c4 c5 c6 ⊢
      push_cast at c0 c1 c2 c4 c5 c6 ⊢
      linear_combination (1 / (1 : ℚ)) * c0 + (-((2 : ℚ)) / (1 : ℚ)) * c1 + (-((-1 : ℚ)) / (1 : ℚ)) * c2 + (-((1 : ℚ)) / (1 : ℚ)) * c4 + (-((-2 : ℚ)) / (1 : ℚ)) * c5 + (-((1 : ℚ)) / (1 : ℚ)) * c6
    · obtain ⟨q, rfl⟩ : ∃ q, n = 17 + 4 * q := ⟨(n - 17) / 4, by omega⟩
      have c0 := cfn1 (17 + 4 * q) (by omega) (by omega)
      rw [show 17 + 4 * q - 1 = 16 + 4 * q by omega]
      have c1 := cfn0 (16 + 4 * q) (by omega) (by omega)
      rw [show 17 + 4 * q - 2 = 15 + 4 * q by omega]
      have c2 := cfn3 (15 + 4 * q) (by omega) (by omega)
      rw [show 17 + 4 * q - 4 = 13 + 4 * q by omega]
      have c4 := cfn1 (13 + 4 * q) (by omega) (by omega)
      rw [show 17 + 4 * q - 5 = 12 + 4 * q by omega]
      have c5 := cfn0 (12 + 4 * q) (by omega) (by omega)
      rw [show 17 + 4 * q - 6 = 11 + 4 * q by omega]
      have c6 := cfn3 (11 + 4 * q) (by omega) (by omega)
      try simp only [pow_add, mul_one, one_mul, show ∀ q : ℕ, ((-1 : ℚ)) ^ (4 * q) = 1 from fun q => by rw [pow_mul]; norm_num] at c0 c1 c2 c4 c5 c6 ⊢
      push_cast at c0 c1 c2 c4 c5 c6 ⊢
      linear_combination (1 / (1 : ℚ)) * c0 + (-((2 : ℚ)) / (1 : ℚ)) * c1 + (-((-1 : ℚ)) / (1 : ℚ)) * c2 + (-((1 : ℚ)) / (1 : ℚ)) * c4 + (-((-2 : ℚ)) / (1 : ℚ)) * c5 + (-((1 : ℚ)) / (1 : ℚ)) * c6
    · obtain ⟨q, rfl⟩ : ∃ q, n = 18 + 4 * q := ⟨(n - 18) / 4, by omega⟩
      have c0 := cfn2 (18 + 4 * q) (by omega) (by omega)
      rw [show 18 + 4 * q - 1 = 17 + 4 * q by omega]
      have c1 := cfn1 (17 + 4 * q) (by omega) (by omega)
      rw [show 18 + 4 * q - 2 = 16 + 4 * q by omega]
      have c2 := cfn0 (16 + 4 * q) (by omega) (by omega)
      rw [show 18 + 4 * q - 4 = 14 + 4 * q by omega]
      have c4 := cfn2 (14 + 4 * q) (by omega) (by omega)
      rw [show 18 + 4 * q - 5 = 13 + 4 * q by omega]
      have c5 := cfn1 (13 + 4 * q) (by omega) (by omega)
      rw [show 18 + 4 * q - 6 = 12 + 4 * q by omega]
      have c6 := cfn0 (12 + 4 * q) (by omega) (by omega)
      try simp only [pow_add, mul_one, one_mul, show ∀ q : ℕ, ((-1 : ℚ)) ^ (4 * q) = 1 from fun q => by rw [pow_mul]; norm_num] at c0 c1 c2 c4 c5 c6 ⊢
      push_cast at c0 c1 c2 c4 c5 c6 ⊢
      linear_combination (1 / (1 : ℚ)) * c0 + (-((2 : ℚ)) / (1 : ℚ)) * c1 + (-((-1 : ℚ)) / (1 : ℚ)) * c2 + (-((1 : ℚ)) / (1 : ℚ)) * c4 + (-((-2 : ℚ)) / (1 : ℚ)) * c5 + (-((1 : ℚ)) / (1 : ℚ)) * c6
    · obtain ⟨q, rfl⟩ : ∃ q, n = 19 + 4 * q := ⟨(n - 19) / 4, by omega⟩
      have c0 := cfn3 (19 + 4 * q) (by omega) (by omega)
      rw [show 19 + 4 * q - 1 = 18 + 4 * q by omega]
      have c1 := cfn2 (18 + 4 * q) (by omega) (by omega)
      rw [show 19 + 4 * q - 2 = 17 + 4 * q by omega]
      have c2 := cfn1 (17 + 4 * q) (by omega) (by omega)
      rw [show 19 + 4 * q - 4 = 15 + 4 * q by omega]
      have c4 := cfn3 (15 + 4 * q) (by omega) (by omega)
      rw [show 19 + 4 * q - 5 = 14 + 4 * q by omega]
      have c5 := cfn2 (14 + 4 * q) (by omega) (by omega)
      rw [show 19 + 4 * q - 6 = 13 + 4 * q by omega]
      have c6 := cfn1 (13 + 4 * q) (by omega) (by omega)
      try simp only [pow_add, mul_one, one_mul, show ∀ q : ℕ, ((-1 : ℚ)) ^ (4 * q) = 1 from fun q => by rw [pow_mul]; norm_num] at c0 c1 c2 c4 c5 c6 ⊢
      push_cast at c0 c1 c2 c4 c5 c6 ⊢
      linear_combination (1 / (1 : ℚ)) * c0 + (-((2 : ℚ)) / (1 : ℚ)) * c1 + (-((-1 : ℚ)) / (1 : ℚ)) * c2 + (-((1 : ℚ)) / (1 : ℚ)) * c4 + (-((-2 : ℚ)) / (1 : ℚ)) * c5 + (-((1 : ℚ)) / (1 : ℚ)) * c6

open PowerSeries in
/-- G.f.: x*(1+2*x+2*x^3) / ((1-x)^3*(1+x)*(1+x^2)) -/
theorem gf0 : PowerSeries.mk (fun n => (ca n : ℚ)) = (X*(1+2*X+2*X ^ 3)) * (((1-X) ^ 3*(1+X)*(1+X ^ 2)))⁻¹ := by
  set G : ℚ⟦X⟧ := PowerSeries.mk (fun n => (ca n : ℚ))
  have hden : constantCoeff ((((1-X) ^ 3*(1+X)*(1+X ^ 2))) : ℚ⟦X⟧) ≠ 0 := by simp
  have eQ : G * (((1-X) ^ 3*(1+X)*(1+X ^ 2))) = C ((1 : ℚ)) * G + C ((-2 : ℚ)) * (G * X ^ 1) + C ((1 : ℚ)) * (G * X ^ 2) + C ((-1 : ℚ)) * (G * X ^ 4) + C ((2 : ℚ)) * (G * X ^ 5) + C ((-1 : ℚ)) * (G * X ^ 6) := by
    (try simp only [map_neg, map_ofNat, map_one, map_div₀, map_natCast]) <;> ring
  have eP : ((X*(1+2*X+2*X ^ 3)) : ℚ⟦X⟧) = C ((1 : ℚ)) * X ^ 1 + C ((2 : ℚ)) * X ^ 2 + C ((2 : ℚ)) * X ^ 4 := by
    (try simp only [map_neg, map_ofNat, map_one, map_div₀, map_natCast]) <;> ring
  have key : G * (((1-X) ^ 3*(1+X)*(1+X ^ 2))) = X*(1+2*X+2*X ^ 3) := by
    rw [eQ, eP]
    ext n
    simp only [map_add, map_sub, coeff_C_mul, coeff_mul_X_pow', coeff_X_pow, G, coeff_mk, coeff_C]
    rcases Nat.lt_or_ge n 6 with hn | hn
    · interval_cases n <;> norm_num [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16]
    · simp only [show 1 ≤ n by omega, show 2 ≤ n by omega, show 3 ≤ n by omega, show 4 ≤ n by omega, show 5 ≤ n by omega, show 6 ≤ n by omega, show n ≠ 0 by omega, show n ≠ 1 by omega, show n ≠ 2 by omega, show n ≠ 3 by omega, show n ≠ 4 by omega, show n - 1 ≠ 0 by omega, show n - 2 ≠ 0 by omega, show n - 3 ≠ 0 by omega, show n - 4 ≠ 0 by omega, if_true, if_false, ↓reduceIte, ne_eq, not_false_eq_true]
      have hr := gfrec0 n hn
      linear_combination ((1 : ℚ)) * hr
  rw [← key, mul_assoc, PowerSeries.mul_inv_cancel _ hden, mul_one]


/-- a(n) = 1/16*(10*n^2+8*n+3*(-1)^n-2*(-i)^n-2*i^n+1) where i = sqrt(-1) -/
theorem closedI0 : ∀ n : ℕ, (ca n : ℂ) = 1/16*(10*(n : ℂ)^2+8*(n : ℂ)+3*(-1)^n-2*(-Complex.I)^n-2*Complex.I^n+1) := by
  intro n
  have h4 : ∀ z : ℂ, z ^ 4 = 1 → z ^ n = z ^ (n % 4) := fun z hz => by
    conv_lhs => rw [← Nat.mod_add_div n 4, pow_add, pow_mul, hz, one_pow, mul_one]
  rw [h4 (-1) (by norm_num), h4 (-Complex.I) (by rw [neg_pow, Complex.I_pow_four]; norm_num),
    h4 Complex.I Complex.I_pow_four, show (ca n : ℂ) = ((ca n : ℚ) : ℂ) from (Rat.cast_natCast _).symm]
  rcases Nat.lt_or_ge n 10 with h | h
  · interval_cases n <;> simp only [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9] <;> push_cast <;> (try simp only [neg_sq, Complex.I_sq]) <;> ring
  · rcases (by omega : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3) with hr | hr | hr | hr
    · rw [cfn0 n h hr, show n % 4 = 0 by omega]
      push_cast
      (try simp only [neg_sq, Complex.I_sq])
      ring
    · rw [cfn1 n h hr, show n % 4 = 1 by omega]
      push_cast
      (try simp only [neg_sq, Complex.I_sq])
      ring
    · rw [cfn2 n h hr, show n % 4 = 2 by omega]
      push_cast
      (try simp only [neg_sq, Complex.I_sq])
      ring
    · rw [cfn3 n h hr, show n % 4 = 3 by omega]
      push_cast
      (try simp only [neg_sq, Complex.I_sq])
      ring


open PowerSeries in
/-- All the proved formula lines of the entry, together. -/
theorem formulas :
    (PowerSeries.mk (fun n => (ca n : ℚ)) = (X*(1+2*X+2*X ^ 3)) * (((1-X) ^ 3*(1+X)*(1+X ^ 2)))⁻¹) ∧
    (∀ n : ℕ, (ca n : ℂ) = 1/16*(10*(n : ℂ)^2+8*(n : ℂ)+3*(-1)^n-2*(-Complex.I)^n-2*Complex.I^n+1)) :=
  ⟨gf0, closedI0⟩


/-! ## The statement's definitions and the bridge -/

open PowerSeries






theorem rule_eq (l c r : Bool) :
    rule l c r = Nat.testBit 188 (4 * l.toNat + 2 * c.toNat + r.toNat) := by
  cases l <;> cases c <;> cases r <;> rfl

theorem cstate_eq (t : ℕ) : cstate t = state 188 t := by
  induction t with
  | zero => funext i; rfl
  | succ t ih =>
    funext i
    show rule (cstate t (i - 1)) (cstate t i) (cstate t (i + 1)) = step 188 (state 188 t) i
    rw [ih, rule_eq]
    rfl

theorem row_eq (n : ℕ) :
    offCount (state 188 n) n = ∑ k ∈ Finset.range (2 * n + 1), if cstate n ((k : ℤ) - n) then 0 else 1 := by
  rw [offCount, ← cstate_eq]
  conv_lhs => rw [← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' := Finset.mem_range.mp hk
  rw [show ((n : ℤ) - ((2 * n + 1 - 1 - k : ℕ) : ℤ)) = (k : ℤ) - n by omega]
  cases cstate n ((k : ℤ) - n) <;> simp

theorem a_eq_ca : a = ca := by
  funext n
  rw [a, ca]
  exact Finset.sum_congr rfl fun t _ => row_eq t

theorem controls : ∀ n ≤ 26, a n = ([0, 1, 4, 7, 12, 18, 26, 34, 44, 55, 68, 81, 96, 112, 130, 148, 168, 189, 212, 235, 260, 286, 314, 342, 372, 403, 436] : List ℕ).getD n 0 := by
  rw [a_eq_ca]
  exact vals

/-- The site's problem, as stated in `main`. -/
theorem conj :
    (∀ n : ℕ, (a n : ℂ) = 1/16*(10*(n : ℂ)^2+8*(n : ℂ)+3*(-1)^n-2*(-Complex.I)^n-2*Complex.I^n+1)) ∧
    A = (X * (1 + 2 * X + 2 * X ^ 3)) * ((1 - X) ^ 3 * (1 + X) * (1 + X ^ 2))⁻¹ := by
  rw [show A = PowerSeries.mk (fun n => (a n : ℚ)) from rfl, a_eq_ca]
  exact ⟨closedI0,
    gf0⟩

end OMA.S_oeis_a265431

theorem OMA.solution : type_of% @OMA.S_oeis_a265431.main :=
  OMA.S_oeis_a265431.conj
