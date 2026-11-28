import OMAStatements.S_oeis_a282681

namespace OMA.S_oeis_a282681




/-! ### The grid

The cell `(x, y)` with `|x|, |y| ≤ 41` is bit `(y + 41) * 84 + (x + 41)` of a natural number `D`
whose set bits are the cells that differ from the background. Up to stage 40 these cells lie in
`|x|, |y| ≤ 40` (`Supp`), so column 83 and the rows from 82 on stay clear and the shifted copies
of `D` never mix two rows. -/

/-- The box `|x|, |y| ≤ 41`. -/
def InBox (p : ℤ × ℤ) : Prop := -41 ≤ p.1 ∧ p.1 ≤ 41 ∧ -41 ≤ p.2 ∧ p.2 ≤ 41

instance : DecidablePred InBox := fun p => by unfold InBox; infer_instance

/-- Bit index of a box cell. -/
def idx (p : ℤ × ℤ) : ℕ := ((p.2 + 41) * 84 + (p.1 + 41)).toNat

/-- The configuration that differs from the background `bg` exactly at the box cells whose bit
is set in `D`. -/
def rep (bg : Bool) (D : ℕ) (p : ℤ × ℤ) : Bool :=
  (if InBox p then D.testBit (idx p) else false) ^^ bg

/-- Every set bit of `D` lies in the window `|x|, |y| ≤ n`. -/
def Supp (n D : ℕ) : Prop :=
  ∀ k, D.testBit k = true → 41 - n ≤ k % 84 ∧ k % 84 ≤ 41 + n ∧ 41 - n ≤ k / 84 ∧ k / 84 ≤ 41 + n

/-- The new background. -/
def bgstep (rule : ℕ) (bg : Bool) : Bool :=
  Nat.testBit rule (bg.toNat + 2 * (bg.toNat + bg.toNat + bg.toNat + bg.toNat))

/-- Whether a cell that differs from the background `bg` exactly when `c` holds, and has `j`
neighbors that differ from it, differs from the new background after one step. -/
def coef (rule : ℕ) (bg c : Bool) (j : ℕ) : Bool :=
  Nat.testBit rule ((c ^^ bg).toNat + 2 * (if bg then 4 - j else j)) ^^ bgstep rule bg

/-- `X` when `b` holds, else `0`. -/
def sel (b : Bool) (X : ℕ) : ℕ := if b then X else 0

/-- One step on the grid. `L R U V` are the left, right, lower and upper neighbors of every cell,
`s0 + 2 * s1 + 4 * s2` is the number of neighbors that differ from the background, `e j` marks the
cells where that number is `j`, and each class of cells (own bit, number) gets its value from
`coef`. The class of a background cell with background neighbors is never selected, so the
result has no set bit far from the set bits of `D`. -/
def fstep (rule : ℕ) (bg : Bool) (D : ℕ) : ℕ :=
  let L := D <<< 1
  let R := D >>> 1
  let U := D <<< 84
  let V := D >>> 84
  let s0 := (L ^^^ R) ^^^ (U ^^^ V)
  let s1 := (((L ^^^ R) &&& (U ^^^ V)) ^^^ (L &&& R)) ^^^ (U &&& V)
  let s2 := (L &&& R) &&& (U &&& V)
  let e1 := s0 ^^^ (s0 &&& (s1 ||| s2))
  let e2 := s1 ^^^ (s1 &&& (s0 ||| s2))
  let e3 := s0 &&& s1
  sel (coef rule bg true 0) (D ^^^ (D &&& (((L ||| R) ||| U) ||| V))) ^^^
    sel (coef rule bg false 1) (e1 ^^^ (D &&& e1)) ^^^ sel (coef rule bg true 1) (D &&& e1) ^^^
    sel (coef rule bg false 2) (e2 ^^^ (D &&& e2)) ^^^ sel (coef rule bg true 2) (D &&& e2) ^^^
    sel (coef rule bg false 3) (e3 ^^^ (D &&& e3)) ^^^ sel (coef rule bg true 3) (D &&& e3) ^^^
    sel (coef rule bg false 4) (s2 ^^^ (D &&& s2)) ^^^ sel (coef rule bg true 4) (D &&& s2)

/-- The circuit of `fstep` on one cell `c` with neighbors `l r u d`. -/
def cellF (rule : ℕ) (bg c l r u d : Bool) : Bool :=
  let s0 := (l ^^ r) ^^ (u ^^ d)
  let s1 := (((l ^^ r) && (u ^^ d)) ^^ (l && r)) ^^ (u && d)
  let s2 := (l && r) && (u && d)
  let e1 := s0 ^^ (s0 && (s1 || s2))
  let e2 := s1 ^^ (s1 && (s0 || s2))
  let e3 := s0 && s1
  (coef rule bg true 0 && (c ^^ (c && (((l || r) || u) || d)))) ^^
    (coef rule bg false 1 && (e1 ^^ (c && e1))) ^^ (coef rule bg true 1 && (c && e1)) ^^
    (coef rule bg false 2 && (e2 ^^ (c && e2))) ^^ (coef rule bg true 2 && (c && e2)) ^^
    (coef rule bg false 3 && (e3 ^^ (c && e3))) ^^ (coef rule bg true 3 && (c && e3)) ^^
    (coef rule bg false 4 && (s2 ^^ (c && s2))) ^^ (coef rule bg true 4 && (c && s2))

/-- The circuit computes the rule on one cell, relative to the background. -/
def RuleOK (rule : ℕ) : Prop :=
  ∀ bg c l r u d : Bool, (cellF rule bg c l r u d ^^ bgstep rule bg) =
    Nat.testBit rule ((c ^^ bg).toNat + 2 * ((l ^^ bg).toNat + (r ^^ bg).toNat + (u ^^ bg).toNat +
      (d ^^ bg).toNat))

/-- Background of stage `n`. -/
def bgs (rule : ℕ) : ℕ → Bool
  | 0 => false
  | n + 1 => bgstep rule (bgs rule n)

/-- Grid of stage `n`: the origin is bit `41 * 84 + 41 = 3485`. -/
def grid (rule : ℕ) : ℕ → ℕ
  | 0 => 1 <<< 3485
  | n + 1 => fstep rule (bgs rule n) (grid rule n)

/-- The x-axis of stage `n` read from the grid. -/
def xgrid (rule n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (n + 1), (rep (bgs rule n) (grid rule n) ((i : ℤ), 0)).toNat * 2 ^ (n - i)

theorem ruleOK_497 : RuleOK 497 := by
  unfold RuleOK
  decide +kernel

theorem ruleOK_499 : RuleOK 499 := by
  unfold RuleOK
  decide +kernel

theorem testBit_sel (b : Bool) (X k : ℕ) : (sel b X).testBit k = (b && X.testBit k) := by
  cases b <;> simp [sel]

theorem testBit_fstep (rule : ℕ) (bg : Bool) (D k : ℕ) :
    (fstep rule bg D).testBit k = cellF rule bg (D.testBit k) (decide (k ≥ 1) && D.testBit (k - 1))
      (D.testBit (1 + k)) (decide (k ≥ 84) && D.testBit (k - 84)) (D.testBit (84 + k)) := by
  simp only [fstep, cellF, testBit_sel, Nat.testBit_xor, Nat.testBit_and, Nat.testBit_or,
    Nat.testBit_shiftLeft, Nat.testBit_shiftRight]

theorem cellF_inputs {rule : ℕ} {bg c l r u d : Bool} (h : cellF rule bg c l r u d = true) :
    c = true ∨ l = true ∨ r = true ∨ u = true ∨ d = true := by
  cases c <;> cases l <;> cases r <;> cases u <;> cases d <;> simp_all [cellF]

theorem idx_cast {x y : ℤ} (h : InBox (x, y)) : (idx (x, y) : ℤ) = (y + 41) * 84 + (x + 41) := by
  unfold InBox at h
  simp only at h
  unfold idx
  exact Int.toNat_of_nonneg (by omega)

theorem bit_out {n D : ℕ} (hD : Supp n D) {j : ℕ}
    (hj : ¬ (41 - n ≤ j % 84 ∧ j % 84 ≤ 41 + n ∧ 41 - n ≤ j / 84 ∧ j / 84 ≤ 41 + n)) :
    D.testBit j = false := by
  cases h : D.testBit j
  · rfl
  · exact absurd (hD j h) hj

theorem and_bit {n D : ℕ} (hD : Supp n D) (hn : n ≤ 40) (k m : ℕ) :
    (decide (k ≥ m) && D.testBit (k - m)) = D.testBit (k - m) := by
  by_cases h : k ≥ m
  · simp [h]
  · rw [show k - m = 0 by omega, bit_out hD (j := 0) (by omega)]
    simp

/-- A cell read at index `j`: either the cell is in the box with index `j`, or `j` is outside the
window. -/
theorem rep_at {n D : ℕ} (hD : Supp n D) (bg : Bool) (q : ℤ × ℤ) (j : ℕ)
    (h : (InBox q ∧ idx q = j) ∨
      (¬ InBox q ∧ ¬ (41 - n ≤ j % 84 ∧ j % 84 ≤ 41 + n ∧ 41 - n ≤ j / 84 ∧ j / 84 ≤ 41 + n))) :
    rep bg D q = (D.testBit j ^^ bg) := by
  rcases h with ⟨hq, rfl⟩ | ⟨hq, hj⟩
  · rw [rep, if_pos hq]
  · rw [rep, if_neg hq, bit_out hD hj]

/-- Next to a cell outside the box, every cell has the background value. -/
theorem rep_near {n D : ℕ} (hD : Supp n D) (hn : n ≤ 40) (bg : Bool) {x y a b : ℤ}
    (hp : ¬ InBox (x, y)) (ha : x - 1 ≤ a ∧ a ≤ x + 1) (hb : y - 1 ≤ b ∧ b ≤ y + 1) :
    rep bg D (a, b) = bg := by
  by_cases hq : InBox (a, b)
  · have hj : D.testBit (idx (a, b)) = false := by
      apply bit_out hD
      have hk := idx_cast hq
      unfold InBox at hp hq
      simp only at hp hq
      omega
    rw [rep, if_pos hq, hj, Bool.false_xor]
  · rw [rep, if_neg hq, Bool.false_xor]

/-- One grid step is one step of the automaton. -/
theorem step_rep (rule : ℕ) (hR : RuleOK rule) {n D : ℕ} (hn : n ≤ 40) (hD : Supp n D)
    (bg : Bool) : step rule (rep bg D) = rep (bgstep rule bg) (fstep rule bg D) := by
  unfold RuleOK at hR
  funext p
  obtain ⟨x, y⟩ := p
  by_cases hp : InBox (x, y)
  · have hk := idx_cast hp
    have hb := hp
    unfold InBox at hb
    simp only at hb
    have e0 : rep bg D (x, y) = (D.testBit (idx (x, y)) ^^ bg) := rep_at hD bg _ _ (Or.inl ⟨hp, rfl⟩)
    have e1 : rep bg D (x - 1, y) = (D.testBit (idx (x, y) - 1) ^^ bg) := by
      apply rep_at hD
      by_cases h' : InBox (x - 1, y)
      · have := idx_cast h'
        exact Or.inl ⟨h', by omega⟩
      · refine Or.inr ⟨h', ?_⟩
        unfold InBox at h'
        simp only at h'
        omega
    have e2 : rep bg D (x + 1, y) = (D.testBit (1 + idx (x, y)) ^^ bg) := by
      apply rep_at hD
      by_cases h' : InBox (x + 1, y)
      · have := idx_cast h'
        exact Or.inl ⟨h', by omega⟩
      · refine Or.inr ⟨h', ?_⟩
        unfold InBox at h'
        simp only at h'
        omega
    have e3 : rep bg D (x, y - 1) = (D.testBit (idx (x, y) - 84) ^^ bg) := by
      apply rep_at hD
      by_cases h' : InBox (x, y - 1)
      · have := idx_cast h'
        exact Or.inl ⟨h', by omega⟩
      · refine Or.inr ⟨h', ?_⟩
        unfold InBox at h'
        simp only at h'
        omega
    have e4 : rep bg D (x, y + 1) = (D.testBit (84 + idx (x, y)) ^^ bg) := by
      apply rep_at hD
      by_cases h' : InBox (x, y + 1)
      · have := idx_cast h'
        exact Or.inl ⟨h', by omega⟩
      · refine Or.inr ⟨h', ?_⟩
        unfold InBox at h'
        simp only at h'
        omega
    simp only [step]
    rw [e0, e1, e2, e3, e4, rep, if_pos hp, testBit_fstep, and_bit hD hn, and_bit hD hn, hR]
  · have e0 := rep_near hD hn bg hp (a := x) (b := y) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
    have e1 := rep_near hD hn bg hp (a := x - 1) (b := y) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
    have e2 := rep_near hD hn bg hp (a := x + 1) (b := y) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
    have e3 := rep_near hD hn bg hp (a := x) (b := y - 1) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
    have e4 := rep_near hD hn bg hp (a := x) (b := y + 1) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
    simp only [step]
    rw [e0, e1, e2, e3, e4, rep, if_neg hp, Bool.false_xor]
    rfl

theorem supp_fstep (rule : ℕ) {n D : ℕ} (hn : n ≤ 40) (hD : Supp n D) (bg : Bool) :
    Supp (n + 1) (fstep rule bg D) := by
  intro k hk
  rw [testBit_fstep] at hk
  rcases cellF_inputs hk with h | h | h | h | h
  · have := hD k h
    omega
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    have := hD (k - 1) h.2
    omega
  · have := hD (1 + k) h
    omega
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    have := hD (k - 84) h.2
    omega
  · have := hD (84 + k) h
    omega

/-- The grid of stage `n` is the automaton at stage `n`. -/
theorem state_eq (rule : ℕ) (hR : RuleOK rule) (n : ℕ) (hn : n ≤ 41) :
    state rule n = rep (bgs rule n) (grid rule n) ∧ Supp n (grid rule n) := by
  induction n with
  | zero =>
    refine ⟨?_, ?_⟩
    · funext p
      obtain ⟨x, y⟩ := p
      show decide (x = 0 ∧ y = 0) =
        ((if InBox (x, y) then (1 <<< 3485 : ℕ).testBit (idx (x, y)) else false) ^^ false)
      rw [Bool.xor_false]
      by_cases hb : InBox (x, y)
      · have hk := idx_cast hb
        rw [if_pos hb, Nat.testBit_shiftLeft, Bool.eq_iff_iff]
        simp only [decide_eq_true_eq, Bool.and_eq_true, Nat.testBit_one_eq_true_iff_self_eq_zero]
        unfold InBox at hb
        simp only at hb
        constructor
        · rintro ⟨rfl, rfl⟩
          omega
        · intro h
          omega
      · rw [if_neg hb, decide_eq_false_iff_not]
        rintro ⟨rfl, rfl⟩
        exact hb (by unfold InBox; simp only; omega)
    · intro k hk
      change (1 <<< 3485 : ℕ).testBit k = true at hk
      rw [Nat.testBit_shiftLeft] at hk
      simp only [Bool.and_eq_true, decide_eq_true_eq, Nat.testBit_one_eq_true_iff_self_eq_zero] at hk
      omega
  | succ n ih =>
    obtain ⟨h1, h2⟩ := ih (by omega)
    refine ⟨?_, supp_fstep rule (by omega) h2 _⟩
    rw [show state rule (n + 1) = step rule (state rule n) from rfl, h1,
      step_rep rule hR (by omega) h2]
    rfl

theorem xaxis_eq (rule : ℕ) (hR : RuleOK rule) (n : ℕ) (hn : n ≤ 41) :
    xaxis rule n = xgrid rule n := by
  rw [xaxis, xgrid, (state_eq rule hR n hn).1]

/-- Controls: the listed terms `a(1)`, `a(13)` and `a(15)` of both entries. -/
theorem controls : xaxis 499 1 = 2 ∧ xaxis 497 1 = 0 ∧ xaxis 497 13 = 768 ∧ xaxis 499 13 = 768 ∧
    xaxis 497 15 = 16128 ∧ xaxis 499 15 = 16128 := by
  rw [xaxis_eq 499 ruleOK_499 1 (by norm_num), xaxis_eq 497 ruleOK_497 1 (by norm_num),
    xaxis_eq 497 ruleOK_497 13 (by norm_num), xaxis_eq 499 ruleOK_499 13 (by norm_num),
    xaxis_eq 497 ruleOK_497 15 (by norm_num), xaxis_eq 499 ruleOK_499 15 (by norm_num)]
  decide +kernel

theorem value_497 : xgrid 497 39 = 193525710848 := by
  decide +kernel

theorem value_499 : xgrid 499 39 = 202115645440 := by
  decide +kernel

/-- Mathar's conjecture (A282681(n) = A282677(n) for n >= 2) fails at n = 39. -/
theorem disproof : ¬ ∀ n : ℕ, 2 ≤ n → xaxis 499 n = xaxis 497 n := by
  intro h
  have := h 39 (by norm_num)
  rw [xaxis_eq 499 ruleOK_499 39 (by norm_num), xaxis_eq 497 ruleOK_497 39 (by norm_num),
    value_497, value_499] at this
  norm_num at this

end OMA.S_oeis_a282681

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a282681.main) :=
  OMA.S_oeis_a282681.disproof
