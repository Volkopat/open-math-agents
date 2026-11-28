import OMAStatements.S_oeis_a265428

namespace OMA.S_oeis_a265428







/-! ## A finite certificate: rows `0..10` on the window `[-11, 11]` -/

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

lemma cert_rows (t : ℕ) (ht : t ≤ 10) :
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

lemma pattern (t : ℕ) (ht : 10 ≤ t) : ∀ i, state t i = V t i := by
  induction t, ht using Nat.le_induction with
  | base =>
    intro i
    rw [(cert_rows 10 le_rfl).2 i]
    by_cases hw : -(W : ℤ) ≤ i ∧ i ≤ W
    · obtain ⟨j, hj, rfl⟩ := in_window i hw
      exact base_ok.1 j hj
    · unfold decode
      rw [if_neg hw, base_ok.2, V_out 10 i (by unfold W at hw; omega)]
  | succ t ht ih =>
    intro i
    show rule (state t (i - 1)) (state t i) (state t (i + 1)) = _
    rw [ih, ih, ih, stepV t ht i]

lemma sim_V (t : ℕ) (ht : t ≤ 10) : sim t = state t := funext fun i => ((cert_rows t ht).2 i).symm

lemma state_eq_V (t : ℕ) (ht : 10 ≤ t) : state t = V t := funext (pattern t ht)

def rowOf (t : ℕ) : ℤ → Bool := if t ≤ 10 then sim t else V t

lemma state_eq (t : ℕ) : state t = rowOf t := by
  unfold rowOf
  split_ifs with h
  · exact (sim_V t h).symm
  · exact state_eq_V t (by omega)

/-- The number of ON cells among `-n..n` in row `n`. -/
def cnt1 (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (2 * n + 1), if state n ((k : ℤ) - n) then 1 else 0


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
    cnt1 n = (∑ k ∈ Finset.range 1, (if (elT.getD ((n - 10) % 4) 0).testBit k then 1 else 0)) +
      (∑ k ∈ Finset.range (n - 1), (if (flLT.getD ((n - 10) % 4) 0).testBit ((1 + k) % 4) then 1 else 0)) +
      (∑ k ∈ Finset.range 1, (if (coT.getD ((n - 10) % 4) 0).testBit k then 1 else 0)) +
      (∑ k ∈ Finset.range (n - 1), (if (flRT.getD ((n - 10) % 4) 0).testBit ((1 + k) % 4) then 1 else 0)) +
      (∑ k ∈ Finset.range 1, (if (erT.getD ((n - 10) % 4) 0).testBit (0 - k) then 1 else 0)) := by
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
    (cnt1 n : ℚ) = ((3 : ℚ) / 4) * (n : ℚ) + (1 : ℚ) := by
  rw [cnt_split n h1, show (n - 10) % 4 = 2 by omega]
  have e1 : (∑ k ∈ Finset.range 1, (if (elT.getD 2 0).testBit k then 1 else 0)) = 0 := by decide
  have e3 : (∑ k ∈ Finset.range 1, (if (coT.getD 2 0).testBit k then 1 else 0)) = 1 := by decide
  have e5 : (∑ k ∈ Finset.range 1, (if (erT.getD 2 0).testBit (0 - k) then 1 else 0)) = 1 := by decide
  rw [e1, e3, e5]
  obtain ⟨m, rfl⟩ : ∃ m, n = 1 + (4 * m + 3) := ⟨(n - 1) / 4, by omega⟩
  rw [show 1 + (4 * m + 3) - 1 = 4 * m + 3 by omega, Finset.sum_range_add, Finset.sum_range_add]
  have hl := per_sum (fun s => if (flLT.getD 2 0).testBit s then 1 else 0) 1 m
  have hr := per_sum (fun s => if (flRT.getD 2 0).testBit s then 1 else 0) 1 m
  try simp only at hl hr
  rw [hl, hr]
  have gl : (∑ j ∈ Finset.range 4, (if (flLT.getD 2 0).testBit ((1 + j) % 4) then 1 else 0 : ℕ)) = 0 := by decide
  have gr : (∑ j ∈ Finset.range 4, (if (flRT.getD 2 0).testBit ((1 + j) % 4) then 1 else 0 : ℕ)) = 3 := by decide
  have tl : (∑ x ∈ Finset.range 3, (if (flLT.getD 2 0).testBit ((1 + (4 * m + x)) % 4) then 1 else 0 : ℕ)) = 0 := by
    rw [Finset.sum_congr rfl fun x _ => by rw [show (1 + (4 * m + x)) % 4 = (1 + x) % 4 by omega]]
    decide
  have tr : (∑ x ∈ Finset.range 3, (if (flRT.getD 2 0).testBit ((1 + (4 * m + x)) % 4) then 1 else 0 : ℕ)) = 2 := by
    rw [Finset.sum_congr rfl fun x _ => by rw [show (1 + (4 * m + x)) % 4 = (1 + x) % 4 by omega]]
    decide
  rw [gl, gr, tl, tr]
  push_cast
  ring


lemma cntn1 (n : ℕ) (h1 : 10 ≤ n) (h2 : n % 4 = 1) :
    (cnt1 n : ℚ) = ((3 : ℚ) / 4) * (n : ℚ) + ((5 : ℚ) / 4) := by
  rw [cnt_split n h1, show (n - 10) % 4 = 3 by omega]
  have e1 : (∑ k ∈ Finset.range 1, (if (elT.getD 3 0).testBit k then 1 else 0)) = 0 := by decide
  have e3 : (∑ k ∈ Finset.range 1, (if (coT.getD 3 0).testBit k then 1 else 0)) = 1 := by decide
  have e5 : (∑ k ∈ Finset.range 1, (if (erT.getD 3 0).testBit (0 - k) then 1 else 0)) = 1 := by decide
  rw [e1, e3, e5]
  obtain ⟨m, rfl⟩ : ∃ m, n = 1 + (4 * m + 0) := ⟨(n - 1) / 4, by omega⟩
  rw [show 1 + (4 * m + 0) - 1 = 4 * m + 0 by omega, Finset.sum_range_add, Finset.sum_range_add]
  have hl := per_sum (fun s => if (flLT.getD 3 0).testBit s then 1 else 0) 1 m
  have hr := per_sum (fun s => if (flRT.getD 3 0).testBit s then 1 else 0) 1 m
  try simp only at hl hr
  rw [hl, hr]
  have gl : (∑ j ∈ Finset.range 4, (if (flLT.getD 3 0).testBit ((1 + j) % 4) then 1 else 0 : ℕ)) = 0 := by decide
  have gr : (∑ j ∈ Finset.range 4, (if (flRT.getD 3 0).testBit ((1 + j) % 4) then 1 else 0 : ℕ)) = 3 := by decide
  have tl : (∑ x ∈ Finset.range 0, (if (flLT.getD 3 0).testBit ((1 + (4 * m + x)) % 4) then 1 else 0 : ℕ)) = 0 := by
    rw [Finset.sum_congr rfl fun x _ => by rw [show (1 + (4 * m + x)) % 4 = (1 + x) % 4 by omega]]
    decide
  have tr : (∑ x ∈ Finset.range 0, (if (flRT.getD 3 0).testBit ((1 + (4 * m + x)) % 4) then 1 else 0 : ℕ)) = 0 := by
    rw [Finset.sum_congr rfl fun x _ => by rw [show (1 + (4 * m + x)) % 4 = (1 + x) % 4 by omega]]
    decide
  rw [gl, gr, tl, tr]
  push_cast
  ring


lemma cntn2 (n : ℕ) (h1 : 10 ≤ n) (h2 : n % 4 = 2) :
    (cnt1 n : ℚ) = ((3 : ℚ) / 4) * (n : ℚ) + ((1 : ℚ) / 2) := by
  rw [cnt_split n h1, show (n - 10) % 4 = 0 by omega]
  have e1 : (∑ k ∈ Finset.range 1, (if (elT.getD 0 0).testBit k then 1 else 0)) = 0 := by decide
  have e3 : (∑ k ∈ Finset.range 1, (if (coT.getD 0 0).testBit k then 1 else 0)) = 1 := by decide
  have e5 : (∑ k ∈ Finset.range 1, (if (erT.getD 0 0).testBit (0 - k) then 1 else 0)) = 1 := by decide
  rw [e1, e3, e5]
  obtain ⟨m, rfl⟩ : ∃ m, n = 1 + (4 * m + 1) := ⟨(n - 1) / 4, by omega⟩
  rw [show 1 + (4 * m + 1) - 1 = 4 * m + 1 by omega, Finset.sum_range_add, Finset.sum_range_add]
  have hl := per_sum (fun s => if (flLT.getD 0 0).testBit s then 1 else 0) 1 m
  have hr := per_sum (fun s => if (flRT.getD 0 0).testBit s then 1 else 0) 1 m
  try simp only at hl hr
  rw [hl, hr]
  have gl : (∑ j ∈ Finset.range 4, (if (flLT.getD 0 0).testBit ((1 + j) % 4) then 1 else 0 : ℕ)) = 0 := by decide
  have gr : (∑ j ∈ Finset.range 4, (if (flRT.getD 0 0).testBit ((1 + j) % 4) then 1 else 0 : ℕ)) = 3 := by decide
  have tl : (∑ x ∈ Finset.range 1, (if (flLT.getD 0 0).testBit ((1 + (4 * m + x)) % 4) then 1 else 0 : ℕ)) = 0 := by
    rw [Finset.sum_congr rfl fun x _ => by rw [show (1 + (4 * m + x)) % 4 = (1 + x) % 4 by omega]]
    decide
  have tr : (∑ x ∈ Finset.range 1, (if (flRT.getD 0 0).testBit ((1 + (4 * m + x)) % 4) then 1 else 0 : ℕ)) = 0 := by
    rw [Finset.sum_congr rfl fun x _ => by rw [show (1 + (4 * m + x)) % 4 = (1 + x) % 4 by omega]]
    decide
  rw [gl, gr, tl, tr]
  push_cast
  ring


lemma cntn3 (n : ℕ) (h1 : 10 ≤ n) (h2 : n % 4 = 3) :
    (cnt1 n : ℚ) = ((3 : ℚ) / 4) * (n : ℚ) + ((7 : ℚ) / 4) := by
  rw [cnt_split n h1, show (n - 10) % 4 = 1 by omega]
  have e1 : (∑ k ∈ Finset.range 1, (if (elT.getD 1 0).testBit k then 1 else 0)) = 0 := by decide
  have e3 : (∑ k ∈ Finset.range 1, (if (coT.getD 1 0).testBit k then 1 else 0)) = 1 := by decide
  have e5 : (∑ k ∈ Finset.range 1, (if (erT.getD 1 0).testBit (0 - k) then 1 else 0)) = 1 := by decide
  rw [e1, e3, e5]
  obtain ⟨m, rfl⟩ : ∃ m, n = 1 + (4 * m + 2) := ⟨(n - 1) / 4, by omega⟩
  rw [show 1 + (4 * m + 2) - 1 = 4 * m + 2 by omega, Finset.sum_range_add, Finset.sum_range_add]
  have hl := per_sum (fun s => if (flLT.getD 1 0).testBit s then 1 else 0) 1 m
  have hr := per_sum (fun s => if (flRT.getD 1 0).testBit s then 1 else 0) 1 m
  try simp only at hl hr
  rw [hl, hr]
  have gl : (∑ j ∈ Finset.range 4, (if (flLT.getD 1 0).testBit ((1 + j) % 4) then 1 else 0 : ℕ)) = 0 := by decide
  have gr : (∑ j ∈ Finset.range 4, (if (flRT.getD 1 0).testBit ((1 + j) % 4) then 1 else 0 : ℕ)) = 3 := by decide
  have tl : (∑ x ∈ Finset.range 2, (if (flLT.getD 1 0).testBit ((1 + (4 * m + x)) % 4) then 1 else 0 : ℕ)) = 0 := by
    rw [Finset.sum_congr rfl fun x _ => by rw [show (1 + (4 * m + x)) % 4 = (1 + x) % 4 by omega]]
    decide
  have tr : (∑ x ∈ Finset.range 2, (if (flRT.getD 1 0).testBit ((1 + (4 * m + x)) % 4) then 1 else 0 : ℕ)) = 2 := by
    rw [Finset.sum_congr rfl fun x _ => by rw [show (1 + (4 * m + x)) % 4 = (1 + x) % 4 by omega]]
    decide
  rw [gl, gr, tl, tr]
  push_cast
  ring



lemma a_eq_cnt1 (n : ℕ) : a n = cnt1 n := rfl

/-- The row counts read off the certified rows (`rowOf`). -/
def cSim (n : ℕ) : ℕ := ∑ k ∈ Finset.range (2 * n + 1), if rowOf n ((k : ℤ) - n) then 1 else 0

lemma a_eq_sim (n : ℕ) : a n = cSim n := by
  unfold a cSim
  simp only [state_eq]

lemma cvals : ∀ n ≤ 10, a n = ([1, 2, 2, 4, 4, 5, 5, 7, 7, 8, 8] : List ℕ).getD n 0 := by
  intro n hn
  rw [a_eq_sim n]
  revert n
  decide +kernel

/-- The closed form on every residue class, from row 10 on. -/
noncomputable def c (r : ℕ) : ℚ := if r = 0 then 1 else if r = 1 then 5 / 4 else if r = 2 then 1 / 2 else 7 / 4

lemma cfq (n : ℕ) (h : 10 ≤ n) : (a n : ℚ) = 3 / 4 * n + c (n % 4) := by
  rw [a_eq_cnt1]
  rcases (by omega : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3) with hr | hr | hr | hr
  · rw [cntn0 n h hr, hr]; simp [c]
  · rw [cntn1 n h hr, hr]; simp [c]
  · rw [cntn2 n h hr, hr]; simp [c]
  · rw [cntn3 n h hr, hr]; simp [c]

lemma values : a 0 = 1 ∧ a 1 = 2 ∧ a 2 = 2 ∧ a 3 = 4 ∧ a 4 = 4 ∧ a 5 = 5 ∧ a 6 = 5 ∧ a 7 = 7 ∧
    a 8 = 7 ∧ a 9 = 8 ∧ a 10 = 8 ∧ a 11 = 10 ∧ a 12 = 10 ∧ a 13 = 11 ∧ a 14 = 11 := by
  have q : ∀ n : ℕ, 10 ≤ n → ∀ v : ℕ, (3 / 4 * (n : ℚ) + c (n % 4) = (v : ℚ)) → a n = v := by
    intro n hn v hv
    have := cfq n hn
    rw [hv] at this
    exact_mod_cast this
  refine ⟨cvals 0 (by norm_num), cvals 1 (by norm_num), cvals 2 (by norm_num),
    cvals 3 (by norm_num), cvals 4 (by norm_num), cvals 5 (by norm_num), cvals 6 (by norm_num),
    cvals 7 (by norm_num), cvals 8 (by norm_num), cvals 9 (by norm_num), cvals 10 (by norm_num),
    q 11 (by norm_num) 10 (by norm_num [c]), q 12 (by norm_num) 10 (by norm_num [c]),
    q 13 (by norm_num) 11 (by norm_num [c]), q 14 (by norm_num) 11 (by norm_num [c])⟩

/-- Barker's closed form, with i = sqrt(-1), for every n. -/
theorem closed_form : ∀ n : ℕ, (a n : ℂ) = (1 / 8) * (6 * (n : ℂ) - 3 * (-1) ^ n +
    (1 - Complex.I) * (-Complex.I) ^ n + (1 + Complex.I) * Complex.I ^ n + 9) := by
  intro n
  have h4 : ∀ z : ℂ, z ^ 4 = 1 → z ^ n = z ^ (n % 4) := fun z hz => by
    conv_lhs => rw [← Nat.mod_add_div n 4, pow_add, pow_mul, hz, one_pow, mul_one]
  rw [h4 (-1) (by norm_num), h4 (-Complex.I) (by rw [neg_pow, Complex.I_pow_four]; norm_num),
    h4 Complex.I Complex.I_pow_four, show (a n : ℂ) = ((a n : ℚ) : ℂ) from (Rat.cast_natCast _).symm]
  obtain ⟨v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, -⟩ := values
  rcases Nat.lt_or_ge n 10 with h | h
  · interval_cases n <;> simp only [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9] <;>
      apply Complex.ext <;> simp [pow_succ] <;> norm_num
  · rw [cfq n h]
    rcases (by omega : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3) with hr | hr | hr | hr <;>
      rw [hr] <;> apply Complex.ext <;> simp [c, pow_succ] <;> ring

/-- Barker's recurrence, for n > 4. -/
theorem recurrence (n : ℕ) (hn : 4 < n) : (a n : ℤ) = a (n - 1) + a (n - 4) - a (n - 5) := by
  rcases Nat.lt_or_ge n 15 with hlt | hge
  · obtain ⟨v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14⟩ := values
    interval_cases n <;> simp [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14]
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 15 := ⟨n - 15, by omega⟩
    have key : (a (m + 15) : ℚ) = a (m + 14) + a (m + 11) - a (m + 10) := by
      rw [cfq (m + 15) (by omega), cfq (m + 14) (by omega), cfq (m + 11) (by omega),
        cfq (m + 10) (by omega), show (m + 11) % 4 = (m + 15) % 4 by omega,
        show (m + 10) % 4 = (m + 14) % 4 by omega]
      push_cast
      ring
    rw [show m + 15 - 1 = m + 14 by omega, show m + 15 - 4 = m + 11 by omega,
      show m + 15 - 5 = m + 10 by omega]
    exact_mod_cast key

open PowerSeries in
/-- Barker's g.f., as an identity in Q[[x]]. -/
theorem gf : PowerSeries.mk (fun n => (a n : ℚ)) =
    (1 + X + 2 * X ^ 3 - X ^ 4) * ((1 - X) ^ 2 * (1 + X) * (1 + X ^ 2))⁻¹ := by
  set A : ℚ⟦X⟧ := PowerSeries.mk (fun n => (a n : ℚ)) with hA
  have hden : constantCoeff ((1 - X) ^ 2 * (1 + X) * (1 + X ^ 2) : ℚ⟦X⟧) ≠ 0 := by simp
  have key : A * ((1 - X) ^ 2 * (1 + X) * (1 + X ^ 2)) = 1 + X + 2 * X ^ 3 - X ^ 4 := by
    have e1 : A * ((1 - X) ^ 2 * (1 + X) * (1 + X ^ 2)) =
        A - A * X ^ 1 - A * X ^ 4 + A * X ^ 5 := by ring
    have e2 : (1 + X + 2 * X ^ 3 - X ^ 4 : ℚ⟦X⟧) = 1 + X ^ 1 + X ^ 3 * C 2 - X ^ 4 := by
      simp only [map_ofNat]; ring
    rw [e1, e2]
    ext n
    simp only [map_sub, map_add, coeff_mul_C, coeff_mul_X_pow', coeff_one, coeff_X_pow, hA,
      coeff_mk]
    obtain ⟨v0, v1, v2, v3, v4, -⟩ := values
    rcases Nat.lt_or_ge n 5 with hn | hn
    · interval_cases n <;> simp [v0, v1, v2, v3, v4] <;> norm_num
    · rw [if_pos (by omega), if_pos (by omega), if_pos (by omega)]
      simp only [show n ≠ 0 by omega, show n ≠ 1 by omega, show n ≠ 3 by omega,
        show n ≠ 4 by omega, if_false]
      have hr := recurrence n (by omega)
      have : (a n : ℚ) = a (n - 1) + a (n - 4) - a (n - 5) := by exact_mod_cast hr
      rw [this]; ring
  rw [← key, mul_assoc, PowerSeries.mul_inv_cancel _ hden, mul_one]

/-- Controls: the entry's data a(0..25). -/
theorem controls : (List.range 26).map (fun n => (a n : ℚ)) =
    [1, 2, 2, 4, 4, 5, 5, 7, 7, 8, 8, 10, 10, 11, 11, 13, 13, 14, 14, 16, 16, 17, 17, 19, 19,
      20] := by
  obtain ⟨v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, -⟩ := values
  simp only [List.range_succ, List.range_zero, List.nil_append, List.map_cons, List.map_nil,
    List.cons_append]
  rw [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9]
  simp only [List.cons.injEq, and_true]
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num,
    by norm_num, by norm_num, by norm_num, by norm_num, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    rw [cfq _ (by norm_num)] <;> norm_num [c]

open PowerSeries in
/-- All three of Barker's conjectures. -/
theorem conjecture :
    (∀ n : ℕ, (a n : ℂ) = (1 / 8) * (6 * (n : ℂ) - 3 * (-1) ^ n +
      (1 - Complex.I) * (-Complex.I) ^ n + (1 + Complex.I) * Complex.I ^ n + 9)) ∧
    (∀ n : ℕ, 4 < n → (a n : ℤ) = a (n - 1) + a (n - 4) - a (n - 5)) ∧
    PowerSeries.mk (fun n => (a n : ℚ)) =
      (1 + X + 2 * X ^ 3 - X ^ 4) * ((1 - X) ^ 2 * (1 + X) * (1 + X ^ 2))⁻¹ :=
  ⟨closed_form, recurrence, gf⟩

end OMA.S_oeis_a265428

theorem OMA.solution : type_of% @OMA.S_oeis_a265428.main :=
  OMA.S_oeis_a265428.conjecture
