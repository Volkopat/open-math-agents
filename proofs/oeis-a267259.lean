import OMAStatements.S_oeis_a267259
import Mathlib

namespace A267259Aux

def p0 (i : ℤ) : Bool :=
  decide (i = 0)

lemma far0 (i : ℤ) (h : i < -0 ∨ 0 < i) : p0 i = false := by
  simp only [p0, decide_eq_false_iff_not]
  omega
def p1 (i : ℤ) : Bool :=
  decide (¬(i = 1))

lemma far1 (i : ℤ) (h : i < -1 ∨ 1 < i) : p1 i = true := by
  simp only [p1, decide_eq_true_eq]
  omega
def p2 (i : ℤ) : Bool :=
  decide ((0 ≤ i ∧ i ≤ 2))

lemma far2 (i : ℤ) (h : i < -2 ∨ 2 < i) : p2 i = false := by
  simp only [p2, decide_eq_false_iff_not]
  omega
def p3 (i : ℤ) : Bool :=
  decide (¬(i = 1 ∨ i = 3))

lemma far3 (i : ℤ) (h : i < -3 ∨ 3 < i) : p3 i = true := by
  simp only [p3, decide_eq_true_eq]
  omega
def p4 (i : ℤ) : Bool :=
  decide ((0 ≤ i ∧ i ≤ 4))

lemma far4 (i : ℤ) (h : i < -4 ∨ 4 < i) : p4 i = false := by
  simp only [p4, decide_eq_false_iff_not]
  omega
def p5 (i : ℤ) : Bool :=
  decide (¬((1 ≤ i ∧ i ≤ 3) ∨ i = 5))

lemma far5 (i : ℤ) (h : i < -5 ∨ 5 < i) : p5 i = true := by
  simp only [p5, decide_eq_true_eq]
  omega
def p6 (i : ℤ) : Bool :=
  decide (i = 0 ∨ (2 ≤ i ∧ i ≤ 6))

lemma far6 (i : ℤ) (h : i < -6 ∨ 6 < i) : p6 i = false := by
  simp only [p6, decide_eq_false_iff_not]
  omega
def p7 (i : ℤ) : Bool :=
  decide (¬((3 ≤ i ∧ i ≤ 5) ∨ i = 7))

lemma far7 (i : ℤ) (h : i < -7 ∨ 7 < i) : p7 i = true := by
  simp only [p7, decide_eq_true_eq]
  omega
def p8 (i : ℤ) : Bool :=
  decide (i = 2 ∨ (4 ≤ i ∧ i ≤ 8))

lemma far8 (i : ℤ) (h : i < -8 ∨ 8 < i) : p8 i = false := by
  simp only [p8, decide_eq_false_iff_not]
  omega

def box1 : List ℤ := [-1, 0, 1]

lemma mem_box1 (x : ℤ) (h1 : -1 ≤ x) (h2 : x ≤ 1) : x ∈ box1 := by
  unfold box1
  simp
  omega

lemma trbox0 : ∀ i ∈ box1, p1 i = Nat.testBit 111 (4 * (p0 (i - 1)).toNat + 2 * (p0 i).toNat + (p0 (i + 1)).toNat) := by
  decide

lemma tr0 (i : ℤ) : p1 i = Nat.testBit 111 (4 * (p0 (i - 1)).toNat + 2 * (p0 i).toNat + (p0 (i + 1)).toNat) := by
  by_cases h : -1 ≤ i ∧ i ≤ 1
  · exact trbox0 i (mem_box1 i h.1 h.2)
  · rw [far1 i (by omega), far0 (i - 1) (by omega), far0 i (by omega), far0 (i + 1) (by omega)]
    decide

def box2 : List ℤ := [-2, -1, 0, 1, 2]

lemma mem_box2 (x : ℤ) (h1 : -2 ≤ x) (h2 : x ≤ 2) : x ∈ box2 := by
  unfold box2
  simp
  omega

lemma trbox1 : ∀ i ∈ box2, p2 i = Nat.testBit 111 (4 * (p1 (i - 1)).toNat + 2 * (p1 i).toNat + (p1 (i + 1)).toNat) := by
  decide

lemma tr1 (i : ℤ) : p2 i = Nat.testBit 111 (4 * (p1 (i - 1)).toNat + 2 * (p1 i).toNat + (p1 (i + 1)).toNat) := by
  by_cases h : -2 ≤ i ∧ i ≤ 2
  · exact trbox1 i (mem_box2 i h.1 h.2)
  · rw [far2 i (by omega), far1 (i - 1) (by omega), far1 i (by omega), far1 (i + 1) (by omega)]
    decide

def box3 : List ℤ := [-3, -2, -1, 0, 1, 2, 3]

lemma mem_box3 (x : ℤ) (h1 : -3 ≤ x) (h2 : x ≤ 3) : x ∈ box3 := by
  unfold box3
  simp
  omega

lemma trbox2 : ∀ i ∈ box3, p3 i = Nat.testBit 111 (4 * (p2 (i - 1)).toNat + 2 * (p2 i).toNat + (p2 (i + 1)).toNat) := by
  decide

lemma tr2 (i : ℤ) : p3 i = Nat.testBit 111 (4 * (p2 (i - 1)).toNat + 2 * (p2 i).toNat + (p2 (i + 1)).toNat) := by
  by_cases h : -3 ≤ i ∧ i ≤ 3
  · exact trbox2 i (mem_box3 i h.1 h.2)
  · rw [far3 i (by omega), far2 (i - 1) (by omega), far2 i (by omega), far2 (i + 1) (by omega)]
    decide

def box4 : List ℤ := [-4, -3, -2, -1, 0, 1, 2, 3, 4]

lemma mem_box4 (x : ℤ) (h1 : -4 ≤ x) (h2 : x ≤ 4) : x ∈ box4 := by
  unfold box4
  simp
  omega

lemma trbox3 : ∀ i ∈ box4, p4 i = Nat.testBit 111 (4 * (p3 (i - 1)).toNat + 2 * (p3 i).toNat + (p3 (i + 1)).toNat) := by
  decide

lemma tr3 (i : ℤ) : p4 i = Nat.testBit 111 (4 * (p3 (i - 1)).toNat + 2 * (p3 i).toNat + (p3 (i + 1)).toNat) := by
  by_cases h : -4 ≤ i ∧ i ≤ 4
  · exact trbox3 i (mem_box4 i h.1 h.2)
  · rw [far4 i (by omega), far3 (i - 1) (by omega), far3 i (by omega), far3 (i + 1) (by omega)]
    decide

def box5 : List ℤ := [-5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5]

lemma mem_box5 (x : ℤ) (h1 : -5 ≤ x) (h2 : x ≤ 5) : x ∈ box5 := by
  unfold box5
  simp
  omega

lemma trbox4 : ∀ i ∈ box5, p5 i = Nat.testBit 111 (4 * (p4 (i - 1)).toNat + 2 * (p4 i).toNat + (p4 (i + 1)).toNat) := by
  decide

lemma tr4 (i : ℤ) : p5 i = Nat.testBit 111 (4 * (p4 (i - 1)).toNat + 2 * (p4 i).toNat + (p4 (i + 1)).toNat) := by
  by_cases h : -5 ≤ i ∧ i ≤ 5
  · exact trbox4 i (mem_box5 i h.1 h.2)
  · rw [far5 i (by omega), far4 (i - 1) (by omega), far4 i (by omega), far4 (i + 1) (by omega)]
    decide

def box6 : List ℤ := [-6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6]

lemma mem_box6 (x : ℤ) (h1 : -6 ≤ x) (h2 : x ≤ 6) : x ∈ box6 := by
  unfold box6
  simp
  omega

lemma trbox5 : ∀ i ∈ box6, p6 i = Nat.testBit 111 (4 * (p5 (i - 1)).toNat + 2 * (p5 i).toNat + (p5 (i + 1)).toNat) := by
  decide

lemma tr5 (i : ℤ) : p6 i = Nat.testBit 111 (4 * (p5 (i - 1)).toNat + 2 * (p5 i).toNat + (p5 (i + 1)).toNat) := by
  by_cases h : -6 ≤ i ∧ i ≤ 6
  · exact trbox5 i (mem_box6 i h.1 h.2)
  · rw [far6 i (by omega), far5 (i - 1) (by omega), far5 i (by omega), far5 (i + 1) (by omega)]
    decide

def box7 : List ℤ := [-7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7]

lemma mem_box7 (x : ℤ) (h1 : -7 ≤ x) (h2 : x ≤ 7) : x ∈ box7 := by
  unfold box7
  simp
  omega

lemma trbox6 : ∀ i ∈ box7, p7 i = Nat.testBit 111 (4 * (p6 (i - 1)).toNat + 2 * (p6 i).toNat + (p6 (i + 1)).toNat) := by
  decide

lemma tr6 (i : ℤ) : p7 i = Nat.testBit 111 (4 * (p6 (i - 1)).toNat + 2 * (p6 i).toNat + (p6 (i + 1)).toNat) := by
  by_cases h : -7 ≤ i ∧ i ≤ 7
  · exact trbox6 i (mem_box7 i h.1 h.2)
  · rw [far7 i (by omega), far6 (i - 1) (by omega), far6 i (by omega), far6 (i + 1) (by omega)]
    decide

def box8 : List ℤ := [-8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8]

lemma mem_box8 (x : ℤ) (h1 : -8 ≤ x) (h2 : x ≤ 8) : x ∈ box8 := by
  unfold box8
  simp
  omega

lemma trbox7 : ∀ i ∈ box8, p8 i = Nat.testBit 111 (4 * (p7 (i - 1)).toNat + 2 * (p7 i).toNat + (p7 (i + 1)).toNat) := by
  decide

lemma tr7 (i : ℤ) : p8 i = Nat.testBit 111 (4 * (p7 (i - 1)).toNat + 2 * (p7 i).toNat + (p7 (i + 1)).toNat) := by
  by_cases h : -8 ≤ i ∧ i ≤ 8
  · exact trbox7 i (mem_box8 i h.1 h.2)
  · rw [far8 i (by omega), far7 (i - 1) (by omega), far7 i (by omega), far7 (i + 1) (by omega)]
    decide

open OMA.S_oeis_a267259 in
lemma c0 : ∀ i, cell 111 0 i = p0 i := by
  intro i
  rfl

open OMA.S_oeis_a267259 in
lemma c1 : ∀ i, cell 111 1 i = p1 i := by
  intro i
  show ruleOut 111 (cell 111 0 (i - 1)) (cell 111 0 i) (cell 111 0 (i + 1)) = p1 i
  rw [c0, c0, c0]
  exact (tr0 i).symm

open OMA.S_oeis_a267259 in
lemma c2 : ∀ i, cell 111 2 i = p2 i := by
  intro i
  show ruleOut 111 (cell 111 1 (i - 1)) (cell 111 1 i) (cell 111 1 (i + 1)) = p2 i
  rw [c1, c1, c1]
  exact (tr1 i).symm

open OMA.S_oeis_a267259 in
lemma c3 : ∀ i, cell 111 3 i = p3 i := by
  intro i
  show ruleOut 111 (cell 111 2 (i - 1)) (cell 111 2 i) (cell 111 2 (i + 1)) = p3 i
  rw [c2, c2, c2]
  exact (tr2 i).symm

open OMA.S_oeis_a267259 in
lemma c4 : ∀ i, cell 111 4 i = p4 i := by
  intro i
  show ruleOut 111 (cell 111 3 (i - 1)) (cell 111 3 i) (cell 111 3 (i + 1)) = p4 i
  rw [c3, c3, c3]
  exact (tr3 i).symm

open OMA.S_oeis_a267259 in
lemma c5 : ∀ i, cell 111 5 i = p5 i := by
  intro i
  show ruleOut 111 (cell 111 4 (i - 1)) (cell 111 4 i) (cell 111 4 (i + 1)) = p5 i
  rw [c4, c4, c4]
  exact (tr4 i).symm

open OMA.S_oeis_a267259 in
lemma c6 : ∀ i, cell 111 6 i = p6 i := by
  intro i
  show ruleOut 111 (cell 111 5 (i - 1)) (cell 111 5 i) (cell 111 5 (i + 1)) = p6 i
  rw [c5, c5, c5]
  exact (tr5 i).symm

open OMA.S_oeis_a267259 in
lemma c7 : ∀ i, cell 111 7 i = p7 i := by
  intro i
  show ruleOut 111 (cell 111 6 (i - 1)) (cell 111 6 i) (cell 111 6 (i + 1)) = p7 i
  rw [c6, c6, c6]
  exact (tr6 i).symm

open OMA.S_oeis_a267259 in
lemma c8 : ∀ i, cell 111 8 i = p8 i := by
  intro i
  show ruleOut 111 (cell 111 7 (i - 1)) (cell 111 7 i) (cell 111 7 (i + 1)) = p8 i
  rw [c7, c7, c7]
  exact (tr7 i).symm

/-- for `t ≥ 5`: at even `t` exactly the cells `t - 6` and `t - 4 .. t` are ON, at odd `t` exactly the cells `t - 4, t - 3, t - 2, t` are OFF -/
def p (t : ℕ) (i : ℤ) : Bool :=
  decide ((t % 2 = 0 ∧ (i = (t : ℤ) - 6 ∨ ((t : ℤ) - 4 ≤ i ∧ i ≤ t))) ∨
    (t % 2 = 1 ∧ i ≠ (t : ℤ) - 4 ∧ i ≠ (t : ℤ) - 3 ∧ i ≠ (t : ℤ) - 2 ∧ i ≠ t))

set_option maxHeartbeats 4000000 in
lemma tr (t : ℕ) (ht : 5 ≤ t) (i : ℤ) (l c r : Bool) (hl : p t (i - 1) = l) (hc : p t i = c)
    (hr : p t (i + 1) = r) :
    p (t + 1) i = Nat.testBit 111 (4 * l.toNat + 2 * c.toNat + r.toNat) := by
  cases l <;> cases c <;> cases r <;>
    simp only [p, decide_eq_true_eq, decide_eq_false_iff_not, Bool.toNat_true, Bool.toNat_false,
      Nat.testBit_eq_decide_div_mod_eq] at hl hc hr ⊢ <;>
    norm_num <;> push_cast <;> omega

lemma pbase (i : ℤ) : p5 i = p 5 i := by
  unfold p5 p
  apply decide_eq_decide.mpr
  constructor <;> intro h <;> omega

open OMA.S_oeis_a267259 in
lemma cellP (t : ℕ) (ht : 5 ≤ t) : ∀ i, cell 111 t i = p t i := by
  induction t, ht using Nat.le_induction with
  | base =>
    intro i
    rw [c5, pbase]
  | succ k hk ih =>
    intro i
    show ruleOut 111 (cell 111 k (i - 1)) (cell 111 k i) (cell 111 k (i + 1)) = p (k + 1) i
    rw [ih, ih, ih]
    exact (tr k hk i _ _ _ rfl rfl rfl).symm

open OMA.S_oeis_a267259 in
lemma on_even (n : ℕ) (hn : 5 ≤ n) (h : n % 2 = 0) : onCount 111 n = 6 := by
  unfold onCount
  rw [show 2 * n + 1 = (2 * n - 6) + 7 by omega, Finset.sum_range_add]
  have hhead : ∀ j ∈ Finset.range (2 * n - 6),
      (if cell 111 n ((j : ℤ) - (n : ℤ)) then 1 else 0) = 0 := by
    intro j hj
    have hj' := Finset.mem_range.mp hj
    rw [cellP n hn]
    have e : p n ((j : ℤ) - (n : ℤ)) = false := by
      unfold p
      rw [decide_eq_false_iff_not]
      omega
    rw [e]
    rfl
  have htail : ∀ x ∈ Finset.range 7,
      (if cell 111 n (((2 * n - 6 + x : ℕ) : ℤ) - (n : ℤ)) then 1 else 0) =
      (if x = 0 ∨ 2 ≤ x then 1 else 0) := by
    intro x hx
    have hx' := Finset.mem_range.mp hx
    rw [cellP n hn]
    have e : p n (((2 * n - 6 + x : ℕ) : ℤ) - (n : ℤ)) = decide (x = 0 ∨ 2 ≤ x) := by
      unfold p
      apply decide_eq_decide.mpr
      constructor <;> intro h' <;> omega
    rw [e]
    by_cases hT : x = 0 ∨ 2 ≤ x <;> simp [hT]
  rw [Finset.sum_congr rfl hhead, Finset.sum_congr rfl htail,
    show ∑ x ∈ Finset.range 7, (if x = 0 ∨ 2 ≤ x then 1 else 0) = 6 from by decide]
  simp

open OMA.S_oeis_a267259 in
lemma on_odd (n : ℕ) (hn : 5 ≤ n) (h : n % 2 = 1) : onCount 111 n = 2 * n - 3 := by
  unfold onCount
  rw [show 2 * n + 1 = (2 * n - 6) + 7 by omega, Finset.sum_range_add]
  have hhead : ∀ j ∈ Finset.range (2 * n - 6),
      (if cell 111 n ((j : ℤ) - (n : ℤ)) then 1 else 0) = 1 := by
    intro j hj
    have hj' := Finset.mem_range.mp hj
    rw [cellP n hn]
    have e : p n ((j : ℤ) - (n : ℤ)) = true := by
      unfold p
      rw [decide_eq_true_eq]
      omega
    rw [e]
    rfl
  have htail : ∀ x ∈ Finset.range 7,
      (if cell 111 n (((2 * n - 6 + x : ℕ) : ℤ) - (n : ℤ)) then 1 else 0) =
      (if x = 0 ∨ x = 1 ∨ x = 5 then 1 else 0) := by
    intro x hx
    have hx' := Finset.mem_range.mp hx
    rw [cellP n hn]
    have e : p n (((2 * n - 6 + x : ℕ) : ℤ) - (n : ℤ)) = decide (x = 0 ∨ x = 1 ∨ x = 5) := by
      unfold p
      apply decide_eq_decide.mpr
      constructor <;> intro h' <;> omega
    rw [e]
    by_cases hT : x = 0 ∨ x = 1 ∨ x = 5 <;> simp [hT]
  rw [Finset.sum_congr rfl hhead, Finset.sum_congr rfl htail,
    show ∑ x ∈ Finset.range 7, (if x = 0 ∨ x = 1 ∨ x = 5 then 1 else 0) = 3 from by decide]
  simp
  omega

open OMA.S_oeis_a267259 in
lemma aQ (n : ℕ) (hn : 5 ≤ n) : (a n : ℚ) = (-2 * (-1 : ℚ) ^ n * (n : ℚ) + 2 * (n : ℚ) + 9 * (-1 : ℚ) ^ n + 3) / 2 := by
  unfold a
  push_cast
  rcases Nat.even_or_odd n with he | ho
  · rw [on_even n hn (Nat.even_iff.mp he), he.neg_one_pow]
    push_cast
    ring
  · have h := on_odd n hn (Nat.odd_iff.mp ho)
    have h2 : onCount 111 n + 3 = 2 * n := by omega
    have h3 : (onCount 111 n : ℚ) + 3 = 2 * (n : ℚ) := by exact_mod_cast h2
    rw [ho.neg_one_pow]
    linarith

open OMA.S_oeis_a267259 in
lemma e0 : (a 0 : ℚ) = 1 := by
  have h : onCount 111 0 = 1 := by
    unfold onCount
    simp only [c0]
    decide
  unfold a
  rw [h]
  norm_num

open OMA.S_oeis_a267259 in
lemma e1 : (a 1 : ℚ) = 2 := by
  have h : onCount 111 1 = 2 := by
    unfold onCount
    simp only [c1]
    decide
  unfold a
  rw [h]
  norm_num

open OMA.S_oeis_a267259 in
lemma e2 : (a 2 : ℚ) = 3 := by
  have h : onCount 111 2 = 3 := by
    unfold onCount
    simp only [c2]
    decide
  unfold a
  rw [h]
  norm_num

open OMA.S_oeis_a267259 in
lemma e3 : (a 3 : ℚ) = 5 := by
  have h : onCount 111 3 = 5 := by
    unfold onCount
    simp only [c3]
    decide
  unfold a
  rw [h]
  norm_num

open OMA.S_oeis_a267259 in
lemma e4 : (a 4 : ℚ) = 5 := by
  have h : onCount 111 4 = 5 := by
    unfold onCount
    simp only [c4]
    decide
  unfold a
  rw [h]
  norm_num

open OMA.S_oeis_a267259 in
lemma e5 : (a 5 : ℚ) = 7 := by
  have h : onCount 111 5 = 7 := by
    unfold onCount
    simp only [c5]
    decide
  unfold a
  rw [h]
  norm_num

open OMA.S_oeis_a267259 in
lemma e6 : (a 6 : ℚ) = 6 := by
  have h : onCount 111 6 = 6 := by
    unfold onCount
    simp only [c6]
    decide
  unfold a
  rw [h]
  norm_num

open OMA.S_oeis_a267259 in
lemma e7 : (a 7 : ℚ) = 11 := by
  have h : onCount 111 7 = 11 := by
    unfold onCount
    simp only [c7]
    decide
  unfold a
  rw [h]
  norm_num

open OMA.S_oeis_a267259 in
lemma e8 : (a 8 : ℚ) = 6 := by
  have h : onCount 111 8 = 6 := by
    unfold onCount
    simp only [c8]
    decide
  unfold a
  rw [h]
  norm_num

open PowerSeries in
lemma coeff_term (f : ℕ → ℚ) (c : ℚ) (k n : ℕ) :
    coeff n (mk f * (C c * X ^ k)) = if k ≤ n then c * f (n - k) else 0 := by
  rw [← mul_assoc, mul_comm (mk f) (C c), mul_assoc, coeff_C_mul, coeff_mul_X_pow']
  split_ifs <;> simp [coeff_mk]

end A267259Aux

set_option maxHeartbeats 1600000 in
open OMA.S_oeis_a267259 A267259Aux PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a267259.main := by
  refine ⟨?_, ?_⟩
  · intro n hn
    rw [aQ n (by omega)]
    first | done | ring
  · have hD : ((1 - X) ^ 2 * (1 + X) ^ 2 : PowerSeries ℚ) =
        PowerSeries.C 1 * PowerSeries.X ^ 0 + PowerSeries.C (-2) * PowerSeries.X ^ 2 + PowerSeries.C 1 * PowerSeries.X ^ 4 := by
      simp only [map_one, map_ofNat, map_neg]; ring
    have hN : (1 + 2 * X + X ^ 2 + X ^ 3 - X ^ 5 - X ^ 6 + 2 * X ^ 7 - X ^ 8 : PowerSeries ℚ) =
        PowerSeries.C 1 * PowerSeries.X ^ 0 + PowerSeries.C 2 * PowerSeries.X ^ 1 + PowerSeries.C 1 * PowerSeries.X ^ 2 + PowerSeries.C 1 * PowerSeries.X ^ 3 + PowerSeries.C (-1) * PowerSeries.X ^ 5 + PowerSeries.C (-1) * PowerSeries.X ^ 6 + PowerSeries.C 2 * PowerSeries.X ^ 7 + PowerSeries.C (-1) * PowerSeries.X ^ 8 := by
      simp only [map_one, map_ofNat, map_neg]; ring
    rw [hD, hN]
    ext n
    simp only [mul_add, map_add, coeff_term, PowerSeries.coeff_C_mul_X_pow]
    rcases n with _ | _ | _ | _ | _ | _ | _ | _ | _ | n
    · norm_num [e0]
    · norm_num [e1]
    · norm_num [e0, e2]
    · norm_num [e1, e3]
    · norm_num [e0, e2, e4]
    · norm_num [e1, e3, e5]
    · norm_num [e2, e4, e6]
    · norm_num [e3, e5, e7]
    · norm_num [e4, e6, e8]
    · have f5 := aQ (n + 5) (by omega)
      have f7 := aQ (n + 7) (by omega)
      have f9 := aQ (n + 9) (by omega)
      simp [show n + 9 - 2 = n + 7 by omega, show n + 9 - 4 = n + 5 by omega, f5, f7, f9]
      ring
