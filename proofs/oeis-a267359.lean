import OMAStatements.S_oeis_a267359
import Mathlib

namespace A267359Aux

def p0 (i : ℤ) : Bool :=
  decide (i = 0)

lemma far0 (i : ℤ) (h : i < -0 ∨ 0 < i) : p0 i = false := by
  simp only [p0, decide_eq_false_iff_not]
  omega
def p1 (i : ℤ) : Bool :=
  decide (¬(i = -1))

lemma far1 (i : ℤ) (h : i < -1 ∨ 1 < i) : p1 i = true := by
  simp only [p1, decide_eq_true_eq]
  omega
def p2 (i : ℤ) : Bool :=
  decide ((-2 ≤ i ∧ i ≤ 0))

lemma far2 (i : ℤ) (h : i < -2 ∨ 2 < i) : p2 i = false := by
  simp only [p2, decide_eq_false_iff_not]
  omega
def p3 (i : ℤ) : Bool :=
  decide (¬(i = -3 ∨ i = -1))

lemma far3 (i : ℤ) (h : i < -3 ∨ 3 < i) : p3 i = true := by
  simp only [p3, decide_eq_true_eq]
  omega
def p4 (i : ℤ) : Bool :=
  decide ((-4 ≤ i ∧ i ≤ 0))

lemma far4 (i : ℤ) (h : i < -4 ∨ 4 < i) : p4 i = false := by
  simp only [p4, decide_eq_false_iff_not]
  omega
def p5 (i : ℤ) : Bool :=
  decide (¬(i = -5 ∨ (-3 ≤ i ∧ i ≤ -1)))

lemma far5 (i : ℤ) (h : i < -5 ∨ 5 < i) : p5 i = true := by
  simp only [p5, decide_eq_true_eq]
  omega
def p6 (i : ℤ) : Bool :=
  decide ((-6 ≤ i ∧ i ≤ -2) ∨ i = 0)

lemma far6 (i : ℤ) (h : i < -6 ∨ 6 < i) : p6 i = false := by
  simp only [p6, decide_eq_false_iff_not]
  omega

def box1 : List ℤ := [-1, 0, 1]

lemma mem_box1 (x : ℤ) (h1 : -1 ≤ x) (h2 : x ≤ 1) : x ∈ box1 := by
  unfold box1
  simp
  omega

lemma trbox0 : ∀ i ∈ box1, p1 i = Nat.testBit 125 (4 * (p0 (i - 1)).toNat + 2 * (p0 i).toNat + (p0 (i + 1)).toNat) := by
  decide

lemma tr0 (i : ℤ) : p1 i = Nat.testBit 125 (4 * (p0 (i - 1)).toNat + 2 * (p0 i).toNat + (p0 (i + 1)).toNat) := by
  by_cases h : -1 ≤ i ∧ i ≤ 1
  · exact trbox0 i (mem_box1 i h.1 h.2)
  · rw [far1 i (by omega), far0 (i - 1) (by omega), far0 i (by omega), far0 (i + 1) (by omega)]
    decide

def box2 : List ℤ := [-2, -1, 0, 1, 2]

lemma mem_box2 (x : ℤ) (h1 : -2 ≤ x) (h2 : x ≤ 2) : x ∈ box2 := by
  unfold box2
  simp
  omega

lemma trbox1 : ∀ i ∈ box2, p2 i = Nat.testBit 125 (4 * (p1 (i - 1)).toNat + 2 * (p1 i).toNat + (p1 (i + 1)).toNat) := by
  decide

lemma tr1 (i : ℤ) : p2 i = Nat.testBit 125 (4 * (p1 (i - 1)).toNat + 2 * (p1 i).toNat + (p1 (i + 1)).toNat) := by
  by_cases h : -2 ≤ i ∧ i ≤ 2
  · exact trbox1 i (mem_box2 i h.1 h.2)
  · rw [far2 i (by omega), far1 (i - 1) (by omega), far1 i (by omega), far1 (i + 1) (by omega)]
    decide

def box3 : List ℤ := [-3, -2, -1, 0, 1, 2, 3]

lemma mem_box3 (x : ℤ) (h1 : -3 ≤ x) (h2 : x ≤ 3) : x ∈ box3 := by
  unfold box3
  simp
  omega

lemma trbox2 : ∀ i ∈ box3, p3 i = Nat.testBit 125 (4 * (p2 (i - 1)).toNat + 2 * (p2 i).toNat + (p2 (i + 1)).toNat) := by
  decide

lemma tr2 (i : ℤ) : p3 i = Nat.testBit 125 (4 * (p2 (i - 1)).toNat + 2 * (p2 i).toNat + (p2 (i + 1)).toNat) := by
  by_cases h : -3 ≤ i ∧ i ≤ 3
  · exact trbox2 i (mem_box3 i h.1 h.2)
  · rw [far3 i (by omega), far2 (i - 1) (by omega), far2 i (by omega), far2 (i + 1) (by omega)]
    decide

def box4 : List ℤ := [-4, -3, -2, -1, 0, 1, 2, 3, 4]

lemma mem_box4 (x : ℤ) (h1 : -4 ≤ x) (h2 : x ≤ 4) : x ∈ box4 := by
  unfold box4
  simp
  omega

lemma trbox3 : ∀ i ∈ box4, p4 i = Nat.testBit 125 (4 * (p3 (i - 1)).toNat + 2 * (p3 i).toNat + (p3 (i + 1)).toNat) := by
  decide

lemma tr3 (i : ℤ) : p4 i = Nat.testBit 125 (4 * (p3 (i - 1)).toNat + 2 * (p3 i).toNat + (p3 (i + 1)).toNat) := by
  by_cases h : -4 ≤ i ∧ i ≤ 4
  · exact trbox3 i (mem_box4 i h.1 h.2)
  · rw [far4 i (by omega), far3 (i - 1) (by omega), far3 i (by omega), far3 (i + 1) (by omega)]
    decide

def box5 : List ℤ := [-5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5]

lemma mem_box5 (x : ℤ) (h1 : -5 ≤ x) (h2 : x ≤ 5) : x ∈ box5 := by
  unfold box5
  simp
  omega

lemma trbox4 : ∀ i ∈ box5, p5 i = Nat.testBit 125 (4 * (p4 (i - 1)).toNat + 2 * (p4 i).toNat + (p4 (i + 1)).toNat) := by
  decide

lemma tr4 (i : ℤ) : p5 i = Nat.testBit 125 (4 * (p4 (i - 1)).toNat + 2 * (p4 i).toNat + (p4 (i + 1)).toNat) := by
  by_cases h : -5 ≤ i ∧ i ≤ 5
  · exact trbox4 i (mem_box5 i h.1 h.2)
  · rw [far5 i (by omega), far4 (i - 1) (by omega), far4 i (by omega), far4 (i + 1) (by omega)]
    decide

def box6 : List ℤ := [-6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6]

lemma mem_box6 (x : ℤ) (h1 : -6 ≤ x) (h2 : x ≤ 6) : x ∈ box6 := by
  unfold box6
  simp
  omega

lemma trbox5 : ∀ i ∈ box6, p6 i = Nat.testBit 125 (4 * (p5 (i - 1)).toNat + 2 * (p5 i).toNat + (p5 (i + 1)).toNat) := by
  decide

lemma tr5 (i : ℤ) : p6 i = Nat.testBit 125 (4 * (p5 (i - 1)).toNat + 2 * (p5 i).toNat + (p5 (i + 1)).toNat) := by
  by_cases h : -6 ≤ i ∧ i ≤ 6
  · exact trbox5 i (mem_box6 i h.1 h.2)
  · rw [far6 i (by omega), far5 (i - 1) (by omega), far5 i (by omega), far5 (i + 1) (by omega)]
    decide

open OMA.S_oeis_a267359 in
lemma c0 : ∀ i, cell 125 0 i = p0 i := by
  intro i
  rfl

open OMA.S_oeis_a267359 in
lemma c1 : ∀ i, cell 125 1 i = p1 i := by
  intro i
  show ruleOut 125 (cell 125 0 (i - 1)) (cell 125 0 i) (cell 125 0 (i + 1)) = p1 i
  rw [c0, c0, c0]
  exact (tr0 i).symm

open OMA.S_oeis_a267359 in
lemma c2 : ∀ i, cell 125 2 i = p2 i := by
  intro i
  show ruleOut 125 (cell 125 1 (i - 1)) (cell 125 1 i) (cell 125 1 (i + 1)) = p2 i
  rw [c1, c1, c1]
  exact (tr1 i).symm

open OMA.S_oeis_a267359 in
lemma c3 : ∀ i, cell 125 3 i = p3 i := by
  intro i
  show ruleOut 125 (cell 125 2 (i - 1)) (cell 125 2 i) (cell 125 2 (i + 1)) = p3 i
  rw [c2, c2, c2]
  exact (tr2 i).symm

open OMA.S_oeis_a267359 in
lemma c4 : ∀ i, cell 125 4 i = p4 i := by
  intro i
  show ruleOut 125 (cell 125 3 (i - 1)) (cell 125 3 i) (cell 125 3 (i + 1)) = p4 i
  rw [c3, c3, c3]
  exact (tr3 i).symm

open OMA.S_oeis_a267359 in
lemma c5 : ∀ i, cell 125 5 i = p5 i := by
  intro i
  show ruleOut 125 (cell 125 4 (i - 1)) (cell 125 4 i) (cell 125 4 (i + 1)) = p5 i
  rw [c4, c4, c4]
  exact (tr4 i).symm

open OMA.S_oeis_a267359 in
lemma c6 : ∀ i, cell 125 6 i = p6 i := by
  intro i
  show ruleOut 125 (cell 125 5 (i - 1)) (cell 125 5 i) (cell 125 5 (i + 1)) = p6 i
  rw [c5, c5, c5]
  exact (tr5 i).symm

/-- for `t ≥ 5`, with `x = i + t` the distance from the left end: at even `t` exactly the cells `x = 0..4` and `x = 6` are ON, at odd `t` exactly the cells `x = 0, 2, 3, 4` of the row are OFF -/
def p (t : ℕ) (i : ℤ) : Bool :=
  decide ((t % 2 = 0 ∧ ((0 ≤ i + t ∧ i + t ≤ 4) ∨ i + t = 6)) ∨
    (t % 2 = 1 ∧ (i + t < 0 ∨ i + t = 1 ∨ 5 ≤ i + t)))

lemma tr (t : ℕ) (ht : 5 ≤ t) (i : ℤ) (l c r : Bool) (hl : p t (i - 1) = l) (hc : p t i = c)
    (hr : p t (i + 1) = r) :
    p (t + 1) i = Nat.testBit 125 (4 * l.toNat + 2 * c.toNat + r.toNat) := by
  cases l <;> cases c <;> cases r <;>
    simp only [p, decide_eq_true_eq, decide_eq_false_iff_not, Bool.toNat_true, Bool.toNat_false,
      Nat.testBit_eq_decide_div_mod_eq] at hl hc hr ⊢ <;>
    norm_num <;> push_cast <;> omega

lemma pbase (i : ℤ) : p5 i = p 5 i := by
  unfold p5 p
  apply decide_eq_decide.mpr
  constructor <;> intro h <;> omega

open OMA.S_oeis_a267359 in
lemma cellP (t : ℕ) (ht : 5 ≤ t) : ∀ i, cell 125 t i = p t i := by
  induction t, ht using Nat.le_induction with
  | base =>
    intro i
    rw [c5, pbase]
  | succ k hk ih =>
    intro i
    show ruleOut 125 (cell 125 k (i - 1)) (cell 125 k i) (cell 125 k (i + 1)) = p (k + 1) i
    rw [ih, ih, ih]
    exact (tr k hk i _ _ _ rfl rfl rfl).symm

/-- the digit contributed by cell `j - n` of row `n` -/
def w (n j : ℕ) : ℤ :=
  if OMA.S_oeis_a267359.cell 125 n ((j : ℤ) - (n : ℤ)) then (10 : ℤ) ^ (2 * n - j) else 0

open OMA.S_oeis_a267359 in
lemma a_w (n : ℕ) : a n = ∑ j ∈ Finset.range (2 * n + 1), w n j := rfl

lemma main_even (n : ℕ) (hn : 5 ≤ n) (h : n % 2 = 0) :
    ∑ j ∈ Finset.range (2 * n + 1), w (n + 2) j = 10000 * ∑ j ∈ Finset.range (2 * n + 1), w n j := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  have hj' := Finset.mem_range.mp hj
  unfold w
  rw [cellP (n + 2) (by omega), cellP n (by omega)]
  have e : p (n + 2) ((j : ℤ) - ((n + 2 : ℕ) : ℤ)) = p n ((j : ℤ) - (n : ℤ)) := by
    unfold p
    apply decide_eq_decide.mpr
    push_cast
    constructor <;> intro h' <;> first | omega | trivial | exact h'.elim
  rw [e, show 2 * (n + 2) - j = (2 * n - j) + 4 by omega, pow_add]
  split_ifs <;> ring

lemma tail2_even (n : ℕ) (hn : 5 ≤ n) (h : n % 2 = 0) :
    ∑ x ∈ Finset.range 4, w (n + 2) (2 * n + 1 + x) = 0 := by
  have hv : ∀ x ∈ Finset.range 4, w (n + 2) (2 * n + 1 + x) =
      (if False then (10 : ℤ) ^ (3 - x) else 0) := by
    intro x hx
    have hx' := Finset.mem_range.mp hx
    unfold w
    rw [cellP (n + 2) (by omega)]
    have e : p (n + 2) (((2 * n + 1 + x : ℕ) : ℤ) - ((n + 2 : ℕ) : ℤ)) = decide (False) := by
      unfold p
      apply decide_eq_decide.mpr
      push_cast
      constructor <;> intro h' <;> first | omega | trivial | exact h'.elim
    rw [e, show 2 * (n + 2) - (2 * n + 1 + x) = 3 - x by omega]
    simp
  rw [Finset.sum_congr rfl hv]
  decide

open OMA.S_oeis_a267359 in
lemma a_step_even (n : ℕ) (hn : 5 ≤ n) (h : n % 2 = 0) : a (n + 2) = 10000 * a n + (0) := by
  rw [a_w, a_w, show 2 * (n + 2) + 1 = 2 * n + 1 + 4 by ring, Finset.sum_range_add,
    main_even n hn h, tail2_even n hn h]

lemma main_odd (n : ℕ) (hn : 5 ≤ n) (h : n % 2 = 1) :
    ∑ j ∈ Finset.range (2 * n + 1), w (n + 2) j = 10000 * ∑ j ∈ Finset.range (2 * n + 1), w n j := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  have hj' := Finset.mem_range.mp hj
  unfold w
  rw [cellP (n + 2) (by omega), cellP n (by omega)]
  have e : p (n + 2) ((j : ℤ) - ((n + 2 : ℕ) : ℤ)) = p n ((j : ℤ) - (n : ℤ)) := by
    unfold p
    apply decide_eq_decide.mpr
    push_cast
    constructor <;> intro h' <;> first | omega | trivial | exact h'.elim
  rw [e, show 2 * (n + 2) - j = (2 * n - j) + 4 by omega, pow_add]
  split_ifs <;> ring

lemma tail2_odd (n : ℕ) (hn : 5 ≤ n) (h : n % 2 = 1) :
    ∑ x ∈ Finset.range 4, w (n + 2) (2 * n + 1 + x) = 1111 := by
  have hv : ∀ x ∈ Finset.range 4, w (n + 2) (2 * n + 1 + x) =
      (if True then (10 : ℤ) ^ (3 - x) else 0) := by
    intro x hx
    have hx' := Finset.mem_range.mp hx
    unfold w
    rw [cellP (n + 2) (by omega)]
    have e : p (n + 2) (((2 * n + 1 + x : ℕ) : ℤ) - ((n + 2 : ℕ) : ℤ)) = decide (True) := by
      unfold p
      apply decide_eq_decide.mpr
      push_cast
      constructor <;> intro h' <;> first | omega | trivial | exact h'.elim
    rw [e, show 2 * (n + 2) - (2 * n + 1 + x) = 3 - x by omega]
    simp
  rw [Finset.sum_congr rfl hv]
  decide

open OMA.S_oeis_a267359 in
lemma a_step_odd (n : ℕ) (hn : 5 ≤ n) (h : n % 2 = 1) : a (n + 2) = 10000 * a n + (1111) := by
  rw [a_w, a_w, show 2 * (n + 2) + 1 = 2 * n + 1 + 4 by ring, Finset.sum_range_add,
    main_odd n hn h, tail2_odd n hn h]

open OMA.S_oeis_a267359 in
lemma recQ (m : ℕ) : (a (m + 9) : ℚ) = 10001 * a (m + 7) - 10000 * a (m + 5) := by
  rcases Nat.mod_two_eq_zero_or_one m with h | h
  · have h1 := a_step_odd (m + 7) (by omega) (by omega)
    have h2 := a_step_odd (m + 5) (by omega) (by omega)
    rw [show m + 7 + 2 = m + 9 by ring] at h1
    rw [show m + 5 + 2 = m + 7 by ring] at h2
    rw [h1, h2]
    push_cast
    ring
  · have h1 := a_step_even (m + 7) (by omega) (by omega)
    have h2 := a_step_even (m + 5) (by omega) (by omega)
    rw [show m + 7 + 2 = m + 9 by ring] at h1
    rw [show m + 5 + 2 = m + 7 by ring] at h2
    rw [h1, h2]
    push_cast
    ring

open OMA.S_oeis_a267359 in
lemma e0 : (a 0 : ℚ) = 1 := by
  have h : a 0 = 1 := by
    unfold a
    simp only [c0]
    decide
  rw [h]; norm_num

open OMA.S_oeis_a267359 in
lemma e1 : (a 1 : ℚ) = 11 := by
  have h : a 1 = 11 := by
    unfold a
    simp only [c1]
    decide
  rw [h]; norm_num

open OMA.S_oeis_a267359 in
lemma e2 : (a 2 : ℚ) = 11100 := by
  have h : a 2 = 11100 := by
    unfold a
    simp only [c2]
    decide
  rw [h]; norm_num

open OMA.S_oeis_a267359 in
lemma e3 : (a 3 : ℚ) = 101111 := by
  have h : a 3 = 101111 := by
    unfold a
    simp only [c3]
    decide
  rw [h]; norm_num

open OMA.S_oeis_a267359 in
lemma e4 : (a 4 : ℚ) = 111110000 := by
  have h : a 4 = 111110000 := by
    unfold a
    simp only [c4]
    decide
  rw [h]; norm_num

open OMA.S_oeis_a267359 in
lemma e5 : (a 5 : ℚ) = 1000111111 := by
  have h : a 5 = 1000111111 := by
    unfold a
    simp only [c5]
    decide
  rw [h]; norm_num

open OMA.S_oeis_a267359 in
lemma e6 : (a 6 : ℚ) = 1111101000000 := by
  have h : a 6 = 1111101000000 := by
    unfold a
    simp only [c6]
    decide
  rw [h]; norm_num

open OMA.S_oeis_a267359 in
lemma e7 : (a 7 : ℚ) = 10001111111111 := by
  rw [a_step_odd 5 (by norm_num) (by norm_num)]
  push_cast
  rw [e5]
  norm_num

open OMA.S_oeis_a267359 in
lemma e8 : (a 8 : ℚ) = 11111010000000000 := by
  rw [a_step_even 6 (by norm_num) (by norm_num)]
  push_cast
  rw [e6]
  norm_num

open PowerSeries in
lemma coeff_term (f : ℕ → ℚ) (c : ℚ) (k n : ℕ) :
    coeff n (mk f * (C c * X ^ k)) = if k ≤ n then c * f (n - k) else 0 := by
  rw [← mul_assoc, mul_comm (mk f) (C c), mul_assoc, coeff_C_mul, coeff_mul_X_pow']
  split_ifs <;> simp [coeff_mk]

end A267359Aux

set_option maxHeartbeats 1600000 in
open OMA.S_oeis_a267359 A267359Aux PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a267359.main := by
  refine ⟨?_, ?_⟩
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 9 := ⟨n - 9, by omega⟩
    simp only [show m + 9 - 2 = m + 7 by omega, show m + 9 - 4 = m + 5 by omega]
    linarith [recQ m]
  · have hD : ((1 - X) * (1 + X) * (1 - 100 * X) * (1 + 100 * X) : PowerSeries ℚ) =
        PowerSeries.C 1 * PowerSeries.X ^ 0 + PowerSeries.C (-10001) * PowerSeries.X ^ 2 + PowerSeries.C 10000 * PowerSeries.X ^ 4 := by
      simp only [map_one, map_ofNat, map_neg]; ring
    have hN : (1 + 11 * X + 1099 * X ^ 2 - 8900 * X ^ 3 + 108900 * X ^ 4 - 10990000 * X ^ 5 + 890000 * X ^ 6 + 11000000 * X ^ 7 - 1000000 * X ^ 8 : PowerSeries ℚ) =
        PowerSeries.C 1 * PowerSeries.X ^ 0 + PowerSeries.C 11 * PowerSeries.X ^ 1 + PowerSeries.C 1099 * PowerSeries.X ^ 2 + PowerSeries.C (-8900) * PowerSeries.X ^ 3 + PowerSeries.C 108900 * PowerSeries.X ^ 4 + PowerSeries.C (-10990000) * PowerSeries.X ^ 5 + PowerSeries.C 890000 * PowerSeries.X ^ 6 + PowerSeries.C 11000000 * PowerSeries.X ^ 7 + PowerSeries.C (-1000000) * PowerSeries.X ^ 8 := by
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
    · have hr := recQ (n)
      simp [show n + 9 - 2 = n + 7 by omega, show n + 9 - 4 = n + 5 by omega]
      linarith
