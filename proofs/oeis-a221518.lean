import OMAStatements.S_oeis_a221518

namespace OMA.S_oeis_a221518

open PowerSeries Finset



/-- The values u and v differ by at most 1. -/
def cl (u v : ℕ) : Prop := u ≤ v + 1 ∧ v ≤ u + 1

instance (u v : ℕ) : Decidable (cl u v) := by unfold cl; infer_instance

theorem cl_comm (u v : ℕ) : cl u v ↔ cl v u := by unfold cl; omega

theorem good_iff (x : Fin 7 → ℕ) : good x ↔
    ¬ (cl (x 2) (x 3) ∧ cl (x 3) (x 4)) ∧
    (¬ (cl (x 1) (x 2) ∧ cl (x 2) (x 3)) ∧ ¬ cl (x 0) (x 1)) ∧
    (¬ (cl (x 3) (x 4) ∧ cl (x 4) (x 5)) ∧ ¬ cl (x 5) (x 6)) := by
  unfold good cl
  constructor
  · intro h
    have e0 : ¬ (x 0 ≤ x 1 + 1 ∧ x 1 ≤ x 0 + 1) := by
      obtain ⟨j, hj, h1⟩ := h 0
      have hv : j.val = 1 := by simp at hj; omega
      have : j = 1 := Fin.ext hv
      subst this; omega
    have e6 : ¬ (x 5 ≤ x 6 + 1 ∧ x 6 ≤ x 5 + 1) := by
      obtain ⟨j, hj, h1⟩ := h 6
      have hv : j.val = 5 := by simp at hj; omega
      have : j = 5 := Fin.ext hv
      subst this; omega
    have e2 : ¬ ((x 1 ≤ x 2 + 1 ∧ x 2 ≤ x 1 + 1) ∧ (x 2 ≤ x 3 + 1 ∧ x 3 ≤ x 2 + 1)) := by
      obtain ⟨j, hj, h1⟩ := h 2
      have hv : j.val = 3 ∨ j.val = 1 := by simp at hj; omega
      rcases hv with hv | hv
      · have : j = 3 := Fin.ext hv
        subst this; omega
      · have : j = 1 := Fin.ext hv
        subst this; omega
    have e3 : ¬ ((x 2 ≤ x 3 + 1 ∧ x 3 ≤ x 2 + 1) ∧ (x 3 ≤ x 4 + 1 ∧ x 4 ≤ x 3 + 1)) := by
      obtain ⟨j, hj, h1⟩ := h 3
      have hv : j.val = 4 ∨ j.val = 2 := by simp at hj; omega
      rcases hv with hv | hv
      · have : j = 4 := Fin.ext hv
        subst this; omega
      · have : j = 2 := Fin.ext hv
        subst this; omega
    have e4 : ¬ ((x 3 ≤ x 4 + 1 ∧ x 4 ≤ x 3 + 1) ∧ (x 4 ≤ x 5 + 1 ∧ x 5 ≤ x 4 + 1)) := by
      obtain ⟨j, hj, h1⟩ := h 4
      have hv : j.val = 5 ∨ j.val = 3 := by simp at hj; omega
      rcases hv with hv | hv
      · have : j = 5 := Fin.ext hv
        subst this; omega
      · have : j = 3 := Fin.ext hv
        subst this; omega
    exact ⟨e3, ⟨e2, e0⟩, ⟨e4, e6⟩⟩
  · rintro ⟨h23, ⟨h12, h01⟩, ⟨h34, h56⟩⟩ i
    fin_cases i
    · exact ⟨1, by decide, show x 0 + 2 ≤ x 1 ∨ x 1 + 2 ≤ x 0 by omega⟩
    · exact ⟨0, by decide, show x 1 + 2 ≤ x 0 ∨ x 0 + 2 ≤ x 1 by omega⟩
    · by_cases hc : x 1 ≤ x 2 + 1 ∧ x 2 ≤ x 1 + 1
      · exact ⟨3, by decide, show x 2 + 2 ≤ x 3 ∨ x 3 + 2 ≤ x 2 by omega⟩
      · exact ⟨1, by decide, show x 2 + 2 ≤ x 1 ∨ x 1 + 2 ≤ x 2 by omega⟩
    · by_cases hc : x 2 ≤ x 3 + 1 ∧ x 3 ≤ x 2 + 1
      · exact ⟨4, by decide, show x 3 + 2 ≤ x 4 ∨ x 4 + 2 ≤ x 3 by omega⟩
      · exact ⟨2, by decide, show x 3 + 2 ≤ x 2 ∨ x 2 + 2 ≤ x 3 by omega⟩
    · by_cases hc : x 3 ≤ x 4 + 1 ∧ x 4 ≤ x 3 + 1
      · exact ⟨5, by decide, show x 4 + 2 ≤ x 5 ∨ x 5 + 2 ≤ x 4 by omega⟩
      · exact ⟨3, by decide, show x 4 + 2 ≤ x 3 ∨ x 3 + 2 ≤ x 4 by omega⟩
    · exact ⟨6, by decide, show x 5 + 2 ≤ x 6 ∨ x 6 + 2 ≤ x 5 by omega⟩
    · exact ⟨5, by decide, show x 6 + 2 ≤ x 5 ∨ x 5 + 2 ≤ x 6 by omega⟩

/-- The triple (x2, x3, x4), the value x1 and the pair (x5, x6) of a good array starting with 0
with values in 0..n. -/
def T (n : ℕ) : Finset ((ℕ × ℕ × ℕ) × ℕ × (ℕ × ℕ)) :=
  ((range (n + 1) ×ˢ range (n + 1) ×ˢ range (n + 1)) ×ˢ range (n + 1) ×ˢ
    (range (n + 1) ×ˢ range (n + 1))).filter fun t =>
      ¬ (cl t.1.1 t.1.2.1 ∧ cl t.1.2.1 t.1.2.2) ∧
      (¬ (cl t.2.1 t.1.1 ∧ cl t.1.1 t.1.2.1) ∧ ¬ cl 0 t.2.1) ∧
      (¬ (cl t.1.2.1 t.1.2.2 ∧ cl t.1.2.2 t.2.2.1) ∧ ¬ cl t.2.2.1 t.2.2.2)

/-- The array of a tuple of T. -/
def ψ (t : (ℕ × ℕ × ℕ) × ℕ × (ℕ × ℕ)) : Fin 7 → ℕ :=
  ![0, t.2.1, t.1.1, t.1.2.1, t.1.2.2, t.2.2.1, t.2.2.2]

theorem ψ_inj : Function.Injective ψ := by
  rintro ⟨⟨a2, a3, a4⟩, a1, ⟨a5, a6⟩⟩ ⟨⟨b2, b3, b4⟩, b1, ⟨b5, b6⟩⟩ h
  have e1 := congrFun h 1
  have e2 := congrFun h 2
  have e3 := congrFun h 3
  have e4 := congrFun h 4
  have e5 := congrFun h 5
  have e6 := congrFun h 6
  simp only [ψ, Matrix.cons_val] at e1 e2 e3 e4 e5 e6
  subst e1 e2 e3 e4 e5 e6
  rfl

theorem set_eq (n : ℕ) :
    {x : Fin 7 → ℕ | x 0 = 0 ∧ (∀ i, x i ≤ n) ∧ good x} = ψ '' (T n : Set _) := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_image, Finset.mem_coe, T, Finset.mem_filter,
    Finset.mem_product, Finset.mem_range]
  constructor
  · rintro ⟨h0, hb, hg⟩
    rw [good_iff, h0] at hg
    refine ⟨((x 2, x 3, x 4), x 1, (x 5, x 6)), ⟨⟨⟨?_, ?_, ?_⟩, ?_, ⟨?_, ?_⟩⟩, hg⟩, ?_⟩
    · exact Nat.lt_succ_of_le (hb 2)
    · exact Nat.lt_succ_of_le (hb 3)
    · exact Nat.lt_succ_of_le (hb 4)
    · exact Nat.lt_succ_of_le (hb 1)
    · exact Nat.lt_succ_of_le (hb 5)
    · exact Nat.lt_succ_of_le (hb 6)
    · funext i
      fin_cases i
      · exact h0.symm
      all_goals rfl
  · rintro ⟨⟨⟨x2, x3, x4⟩, x1, ⟨x5, x6⟩⟩, ⟨⟨⟨h2, h3, h4⟩, h1, ⟨h5, h6⟩⟩, hc⟩, rfl⟩
    dsimp only at h1 h2 h3 h4 h5 h6
    refine ⟨rfl, fun i => ?_, ?_⟩
    · fin_cases i <;> simp [ψ] <;> omega
    · rw [good_iff]
      exact hc

theorem a_eq (n : ℕ) : a n = (T n).card := by
  unfold a
  rw [set_eq, Set.ncard_image_of_injective _ ψ_inj, Set.ncard_coe_finset]

/-- The number of values in 0..n not close to y. -/
def fc (n y : ℕ) : ℕ := ((range (n + 1)).filter fun w => ¬ cl w y).card

/-- The completions x1 of (x2, x3) on the left (x0 = 0). -/
def Lc (n x2 x3 : ℕ) : ℕ :=
  ((range (n + 1)).filter fun x1 => ¬ (cl x1 x2 ∧ cl x2 x3) ∧ ¬ cl 0 x1).card

/-- The completions (x5, x6) of (x3, x4) on the right. -/
def Rc (n x3 x4 : ℕ) : ℕ :=
  ((range (n + 1) ×ˢ range (n + 1)).filter fun r => ¬ (cl x3 x4 ∧ cl x4 r.1) ∧ ¬ cl r.1 r.2).card

theorem card_T (n : ℕ) : (T n).card = ∑ m ∈ range (n + 1) ×ˢ range (n + 1) ×ˢ range (n + 1),
    if ¬ (cl m.1 m.2.1 ∧ cl m.2.1 m.2.2) then Lc n m.1 m.2.1 * Rc n m.2.1 m.2.2 else 0 := by
  unfold T
  rw [card_filter, sum_product]
  refine sum_congr rfl (fun m _ => ?_)
  by_cases hP : ¬ (cl m.1 m.2.1 ∧ cl m.2.1 m.2.2)
  · rw [if_pos hP]
    unfold Lc Rc
    rw [card_filter, card_filter, sum_mul_sum, sum_product]
    refine sum_congr rfl (fun l _ => sum_congr rfl (fun r _ => ?_))
    simp only [hP, true_and]
    split_ifs <;> simp_all
  · rw [if_neg hP]
    simp [hP]

theorem Rc_eq (n x3 x4 : ℕ) :
    Rc n x3 x4 = ∑ x5 ∈ range (n + 1), if ¬ (cl x3 x4 ∧ cl x4 x5) then fc n x5 else 0 := by
  unfold Rc fc
  rw [card_filter, sum_product]
  refine sum_congr rfl (fun x5 _ => ?_)
  by_cases h : ¬ (cl x3 x4 ∧ cl x4 x5)
  · rw [if_pos h, card_filter]
    refine sum_congr rfl (fun x6 _ => ?_)
    simp only [h, not_false_eq_true, true_and, cl_comm x5 x6]
  · rw [if_neg h]
    simp [h]

/-- The indicator of the values not close to 0, that is, of the values >= 2. -/
def gz (y : ℕ) : ℤ := if ¬ cl 0 y then 1 else 0

/-- G = the number of values in 0..n not close to 0. -/
def G (n : ℕ) : ℤ := ∑ y ∈ range (n + 1), gz y

/-- E(y) = the number of values in 0..n close to y and not close to 0. -/
def E (n y : ℕ) : ℤ := ∑ w ∈ range (n + 1), if cl w y then gz w else 0

/-- F = the sum of fc over 0..n. -/
def F (n : ℕ) : ℤ := ∑ y ∈ range (n + 1), (fc n y : ℤ)

/-- D(y) = the sum of fc over the values close to y. -/
def D (n y : ℕ) : ℤ := ∑ w ∈ range (n + 1), if cl w y then (fc n w : ℤ) else 0

theorem Lc_int (n x2 x3 : ℕ) : (Lc n x2 x3 : ℤ) = G n - if cl x2 x3 then E n x2 else 0 := by
  unfold Lc G E gz
  rw [card_filter]
  push_cast
  by_cases h : cl x2 x3
  · rw [if_pos h, ← sum_sub_distrib]
    refine sum_congr rfl (fun x1 _ => ?_)
    by_cases h1 : cl x1 x2 <;> by_cases h0 : cl 0 x1 <;> simp [h, h1, h0]
  · rw [if_neg h, sub_zero]
    refine sum_congr rfl (fun x1 _ => ?_)
    simp [h]

theorem Rc_int (n x3 x4 : ℕ) : (Rc n x3 x4 : ℤ) = F n - if cl x3 x4 then D n x4 else 0 := by
  rw [Rc_eq]
  push_cast
  unfold F D
  by_cases h : cl x3 x4
  · rw [if_pos h, ← sum_sub_distrib]
    refine sum_congr rfl (fun x5 _ => ?_)
    by_cases h1 : cl x4 x5 <;> simp [h, h1, cl_comm x5 x4]
  · rw [if_neg h, sub_zero]
    refine sum_congr rfl (fun x5 _ => ?_)
    simp [h]

def PL (n z : ℕ) : ℤ := ∑ y ∈ range (n + 1), (G n - if cl y z then E n y else 0)

def QL (n z : ℕ) : ℤ := ∑ y ∈ range (n + 1), if cl y z then G n - E n y else 0

def PR (n z : ℕ) : ℤ := ∑ y ∈ range (n + 1), (F n - if cl y z then D n y else 0)

def QR (n z : ℕ) : ℤ := ∑ y ∈ range (n + 1), if cl y z then F n - D n y else 0

theorem a_sum (n : ℕ) :
    (a n : ℤ) = ∑ z ∈ range (n + 1), (PL n z * PR n z - QL n z * QR n z) := by
  rw [a_eq, card_T]
  push_cast
  simp only [Lc_int, Rc_int]
  rw [sum_product]
  simp only [sum_product]
  rw [sum_comm]
  refine sum_congr rfl (fun z _ => ?_)
  have hpt : ∀ y w : ℕ, (if ¬ (cl y z ∧ cl z w) then
      (G n - if cl y z then E n y else 0) * (F n - if cl z w then D n w else 0) else 0) =
      (G n - if cl y z then E n y else 0) * (F n - if cl w z then D n w else 0) -
      (if cl y z then G n - E n y else 0) * (if cl w z then F n - D n w else 0) := by
    intro y w
    have hc : cl w z ↔ cl z w := cl_comm w z
    by_cases hA : cl y z <;> by_cases hB : cl z w <;> simp [hA, hB, hc]
  simp only [hpt, sum_sub_distrib]
  rw [← sum_mul_sum, ← sum_mul_sum]
  rfl

theorem csum (n : ℕ) (g : ℕ → ℤ) (z : ℕ) (hz : z ≤ n) :
    ∑ y ∈ range (n + 1), (if cl y z then g y else 0) =
      (if 0 < z then g (z - 1) else 0) + g z + (if z < n then g (z + 1) else 0) := by
  have h1 : ∀ y, (if cl y z then g y else 0) = (if y = z - 1 ∧ 0 < z then g y else 0) +
      (if y = z then g y else 0) + (if y = z + 1 then g y else 0) := by
    intro y
    by_cases ha : y = z + 1
    · have hb : ¬ (y = z - 1 ∧ 0 < z) := by omega
      have hb' : ¬ y = z := by omega
      have hc : cl y z := by unfold cl; omega
      rw [if_pos hc, if_neg hb, if_neg hb', if_pos ha, zero_add, zero_add]
    · by_cases hb : y = z - 1 ∧ 0 < z
      · have hb' : ¬ y = z := by omega
        have hc : cl y z := by unfold cl; omega
        rw [if_pos hc, if_pos hb, if_neg hb', if_neg ha, add_zero, add_zero]
      · by_cases hb' : y = z
        · have hc : cl y z := by unfold cl; omega
          rw [if_pos hc, if_neg hb, if_pos hb', if_neg ha, zero_add, add_zero]
        · have hc : ¬ cl y z := by unfold cl; omega
          rw [if_neg hc, if_neg hb, if_neg hb', if_neg ha, add_zero, add_zero]
  rw [sum_congr rfl (fun y _ => h1 y), sum_add_distrib, sum_add_distrib]
  congr 1
  congr 1
  · by_cases hz0 : 0 < z
    · rw [if_pos hz0]
      have : ∀ y, (if y = z - 1 ∧ 0 < z then g y else 0) = (if y = z - 1 then g y else 0) := by
        intro y
        simp only [hz0, and_true]
      rw [sum_congr rfl (fun y _ => this y), sum_ite_eq', if_pos (mem_range.2 (by omega))]
    · rw [if_neg hz0]
      refine sum_eq_zero (fun y _ => ?_)
      rw [if_neg (by omega)]
  · rw [sum_ite_eq', if_pos (mem_range.2 (by omega))]
  · rw [sum_ite_eq']
    by_cases h : z < n
    · rw [if_pos (mem_range.2 (by omega)), if_pos h]
    · rw [if_neg (by rw [mem_range]; omega), if_neg h]

theorem gz_val (y : ℕ) : gz y = if 2 ≤ y then 1 else 0 := by
  unfold gz cl
  by_cases h : 2 ≤ y
  · rw [if_pos h, if_pos (by omega)]
  · rw [if_neg h, if_neg (by omega)]

theorem G_val (n : ℕ) (hn : 1 ≤ n) : G n = n - 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  unfold G
  rw [sum_range_succ', sum_range_succ']
  simp only [gz_val]
  rw [sum_congr rfl (fun i _ => if_pos (by omega)), if_neg (by omega), if_neg (by omega)]
  simp

theorem E_val (n y : ℕ) (hy : y ≤ n) :
    E n y = (if 0 < y then gz (y - 1) else 0) + gz y + (if y < n then gz (y + 1) else 0) :=
  csum n gz y hy

theorem fc_val (n y : ℕ) (hy : y ≤ n) :
    (fc n y : ℤ) = n - (if 0 < y then 1 else 0) - (if y < n then 1 else 0) := by
  have h := csum n (fun _ => 1) y hy
  unfold fc
  rw [card_filter]
  push_cast
  have : ∀ w, (if ¬ cl w y then (1 : ℤ) else 0) = 1 - (if cl w y then 1 else 0) := by
    intro w
    by_cases hw : cl w y <;> simp [hw]
  rw [sum_congr rfl (fun w _ => this w), sum_sub_distrib, h, sum_const, card_range, nsmul_eq_mul,
    mul_one]
  push_cast
  ring

theorem F_val (n : ℕ) : F n = n ^ 2 - n := by
  unfold F
  rw [sum_congr rfl (fun y hy => fc_val n y (Nat.lt_succ_iff.1 (mem_range.1 hy))),
    sum_sub_distrib, sum_sub_distrib]
  have h1 : ∑ y ∈ range (n + 1), (if 0 < y then (1 : ℤ) else 0) = n := by
    rw [sum_range_succ']
    simp
  have h2 : ∑ y ∈ range (n + 1), (if y < n then (1 : ℤ) else 0) = n := by
    rw [sum_range_succ, if_neg (lt_irrefl n), add_zero,
      sum_congr rfl (fun y hy => if_pos (mem_range.1 hy))]
    simp
  rw [h1, h2, sum_const, card_range, nsmul_eq_mul]
  push_cast
  ring

theorem D_val (n y : ℕ) (hy : y ≤ n) :
    D n y = (if 0 < y then (fc n (y - 1) : ℤ) else 0) + (fc n y : ℤ) +
      (if y < n then (fc n (y + 1) : ℤ) else 0) :=
  csum n (fun w => (fc n w : ℤ)) y hy

theorem PL_val (n z : ℕ) (hz : z ≤ n) : PL n z = (n + 1) * G n -
    ((if 0 < z then E n (z - 1) else 0) + E n z + (if z < n then E n (z + 1) else 0)) := by
  unfold PL
  rw [sum_sub_distrib, csum n (E n) z hz, sum_const, card_range, nsmul_eq_mul]
  push_cast
  ring

theorem QL_val (n z : ℕ) (hz : z ≤ n) : QL n z = (if 0 < z then G n - E n (z - 1) else 0) +
    (G n - E n z) + (if z < n then G n - E n (z + 1) else 0) :=
  csum n (fun y => G n - E n y) z hz

theorem PR_val (n z : ℕ) (hz : z ≤ n) : PR n z = (n + 1) * F n -
    ((if 0 < z then D n (z - 1) else 0) + D n z + (if z < n then D n (z + 1) else 0)) := by
  unfold PR
  rw [sum_sub_distrib, csum n (D n) z hz, sum_const, card_range, nsmul_eq_mul]
  push_cast
  ring

theorem QR_val (n z : ℕ) (hz : z ≤ n) : QR n z = (if 0 < z then F n - D n (z - 1) else 0) +
    (F n - D n z) + (if z < n then F n - D n (z + 1) else 0) :=
  csum n (fun y => F n - D n y) z hz

theorem mid (m z : ℕ) (h1 : 4 ≤ z) (h2 : z ≤ m + 4) :
    PL (m + 7) z * PR (m + 7) z - QL (m + 7) z * QR (m + 7) z =
      ((m + 8) * (m + 6) - 9) * ((m + 8) * ((m + 7) ^ 2 - (m + 7)) - 9 * (m + 5)) -
      3 * (m + 3) * (3 * (((m + 7) ^ 2 - (m + 7)) - 3 * (m + 5))) := by
  simp (disch := omega) only [PL_val, QL_val, PR_val, QR_val, E_val, gz_val, G_val, D_val, fc_val,
    F_val, if_pos, if_neg]
  push_cast
  ring

/-- The closed form for n >= 7. -/
theorem a_big (m : ℕ) : (a (m + 7) : ℤ) = ((m + 7 : ℕ) : ℤ) ^ 6 + ((m + 7 : ℕ) : ℤ) ^ 5 -
    29 * ((m + 7 : ℕ) : ℤ) ^ 4 + 104 * ((m + 7 : ℕ) : ℤ) ^ 3 - 173 * ((m + 7 : ℕ) : ℤ) ^ 2 +
    136 * ((m + 7 : ℕ) : ℤ) - 40 := by
  rw [a_sum, sum_range_succ, sum_range_succ, sum_range_succ, sum_range_succ', sum_range_succ',
    sum_range_succ', sum_range_succ']
  have hmid : ∀ i ∈ range (m + 1),
      PL (m + 7) (i + 1 + 1 + 1 + 1) * PR (m + 7) (i + 1 + 1 + 1 + 1) -
      QL (m + 7) (i + 1 + 1 + 1 + 1) * QR (m + 7) (i + 1 + 1 + 1 + 1) =
      ((m + 8) * (m + 6) - 9) * ((m + 8) * ((m + 7) ^ 2 - (m + 7)) - 9 * (m + 5)) -
      3 * (m + 3) * (3 * (((m + 7) ^ 2 - (m + 7)) - 3 * (m + 5))) := by
    intro i hi
    rw [mem_range] at hi
    exact mid m (i + 1 + 1 + 1 + 1) (by omega) (by omega)
  rw [sum_congr rfl hmid, sum_const, card_range, nsmul_eq_mul]
  simp (disch := omega) only [PL_val, QL_val, PR_val, QR_val, E_val, gz_val, G_val, D_val, fc_val,
    F_val, if_pos, if_neg]
  push_cast
  ring

theorem small : (a 1 : ℤ) = 0 ∧ (a 2 : ℤ) = 8 ∧ (a 3 : ℤ) = 248 ∧ (a 4 : ℤ) = 2088 ∧
    (a 5 : ℤ) = 9940 ∧ (a 6 : ℤ) = 33860 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [a_sum] <;> simp only [sum_range_succ, sum_range_zero] <;>
    simp (disch := omega) only [PL_val, QL_val, PR_val, QR_val, E_val, gz_val, G_val, D_val,
      fc_val, F_val, if_pos, if_neg] <;> norm_num

/-- The closed form for n >= 4 (Hardin's empirical polynomial). -/
theorem a_poly (n : ℕ) (hn : 4 ≤ n) : (a n : ℤ) = (n : ℤ) ^ 6 + (n : ℤ) ^ 5 - 29 * (n : ℤ) ^ 4 +
    104 * (n : ℤ) ^ 3 - 173 * (n : ℤ) ^ 2 + 136 * (n : ℤ) - 40 := by
  rcases (show n = 4 ∨ n = 5 ∨ n = 6 ∨ 7 ≤ n by omega) with rfl | rfl | rfl | h
  · rw [small.2.2.2.1]; norm_num
  · rw [small.2.2.2.2.1]; norm_num
  · rw [small.2.2.2.2.2]; norm_num
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 7 := ⟨n - 7, by omega⟩
    exact a_big m

/-- Barker's recurrence, for n > 10. -/
theorem recurrence (n : ℕ) (hn : 10 < n) :
    (a n : ℤ) = 7 * a (n - 1) - 21 * a (n - 2) + 35 * a (n - 3) - 35 * a (n - 4) +
      21 * a (n - 5) - 7 * a (n - 6) + a (n - 7) := by
  obtain ⟨q, rfl⟩ : ∃ q, n = q + 11 := ⟨n - 11, by omega⟩
  simp only [show q + 11 - 1 = q + 10 by omega, show q + 11 - 2 = q + 9 by omega,
    show q + 11 - 3 = q + 8 by omega, show q + 11 - 4 = q + 7 by omega,
    show q + 11 - 5 = q + 6 by omega, show q + 11 - 6 = q + 5 by omega,
    show q + 11 - 7 = q + 4 by omega]
  rw [a_poly (q + 11) (by omega), a_poly (q + 10) (by omega), a_poly (q + 9) (by omega),
    a_poly (q + 8) (by omega), a_poly (q + 7) (by omega), a_poly (q + 6) (by omega),
    a_poly (q + 5) (by omega), a_poly (q + 4) (by omega)]
  push_cast
  ring

theorem val (n v : ℕ) (hn : 4 ≤ n) (h : (n : ℤ) ^ 6 + (n : ℤ) ^ 5 - 29 * (n : ℤ) ^ 4 +
    104 * (n : ℤ) ^ 3 - 173 * (n : ℤ) ^ 2 + 136 * (n : ℤ) - 40 = v) : a n = v := by
  have := a_poly n hn
  rw [h] at this
  exact_mod_cast this

/-- Barker's g.f., as A(x) (1 - x)^7 = 2x^2 (4 + 96x + ... - 3x^8) in Z[[x]], with
A(x) = Sum_{n >= 1} a(n) x^n. -/
theorem gf : PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * (1 - X) ^ 7 =
    2 * X ^ 2 * (4 + 96 * X + 260 * X ^ 2 + 126 * X ^ 3 - 136 * X ^ 4 + 43 * X ^ 5 - 49 * X ^ 6 +
      19 * X ^ 7 - 3 * X ^ 8) := by
  set A : ℤ⟦X⟧ := PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) with hA
  have e1 : A * (1 - X) ^ 7 = A - C 7 * (A * X ^ 1) + C 21 * (A * X ^ 2) - C 35 * (A * X ^ 3) +
      C 35 * (A * X ^ 4) - C 21 * (A * X ^ 5) + C 7 * (A * X ^ 6) - A * X ^ 7 := by
    simp only [map_ofNat]; ring
  have e2 : (2 * X ^ 2 * (4 + 96 * X + 260 * X ^ 2 + 126 * X ^ 3 - 136 * X ^ 4 + 43 * X ^ 5 -
      49 * X ^ 6 + 19 * X ^ 7 - 3 * X ^ 8) : ℤ⟦X⟧) =
      X ^ 2 * C 8 + X ^ 3 * C 192 + X ^ 4 * C 520 + X ^ 5 * C 252 - X ^ 6 * C 272 +
      X ^ 7 * C 86 - X ^ 8 * C 98 + X ^ 9 * C 38 - X ^ 10 * C 6 := by
    simp only [map_ofNat]; ring
  rw [e1, e2]
  ext n
  have hc : ∀ k, coeff k A = if k = 0 then (0 : ℤ) else a k := fun k => by rw [hA, coeff_mk]
  simp only [map_add, map_sub, coeff_C_mul, coeff_mul_C, coeff_X_pow, coeff_mul_X_pow', hc]
  obtain ⟨v1, v2, v3, v4, v5, v6⟩ := small
  have v7 : a 7 = 92934 := val 7 _ (by norm_num) (by norm_num)
  have v8 : a 8 = 219352 := val 8 _ (by norm_num) (by norm_num)
  have v9 : a 9 = 463208 := val 9 _ (by norm_num) (by norm_num)
  have v10 : a 10 = 898020 := val 10 _ (by norm_num) (by norm_num)
  rcases Nat.lt_or_ge n 11 with hn | hn
  · interval_cases n <;> simp [v1, v2, v3, v4, v5, v6, v7, v8, v9, v10]
  · obtain ⟨q, rfl⟩ : ∃ q, n = q + 11 := ⟨n - 11, by omega⟩
    have h := recurrence (q + 11) (by omega)
    simp only [show q + 11 - 1 = q + 10 by omega, show q + 11 - 2 = q + 9 by omega,
      show q + 11 - 3 = q + 8 by omega, show q + 11 - 4 = q + 7 by omega,
      show q + 11 - 5 = q + 6 by omega, show q + 11 - 6 = q + 5 by omega,
      show q + 11 - 7 = q + 4 by omega] at h ⊢
    simp only [show ¬ q + 11 = 0 by omega, show ¬ q + 10 = 0 by omega, show ¬ q + 9 = 0 by omega,
      show ¬ q + 8 = 0 by omega, show ¬ q + 7 = 0 by omega, show ¬ q + 6 = 0 by omega,
      show ¬ q + 5 = 0 by omega, show ¬ q + 4 = 0 by omega,
      show 1 ≤ q + 11 by omega, show 2 ≤ q + 11 by omega, show 3 ≤ q + 11 by omega,
      show 4 ≤ q + 11 by omega, show 5 ≤ q + 11 by omega, show 6 ≤ q + 11 by omega,
      show 7 ≤ q + 11 by omega, show ¬ q + 11 = 2 by omega, show ¬ q + 11 = 3 by omega,
      show ¬ q + 11 = 4 by omega, show ¬ q + 11 = 5 by omega, show ¬ q + 11 = 6 by omega,
      show ¬ q + 11 = 7 by omega, show ¬ q + 11 = 8 by omega, show ¬ q + 11 = 9 by omega,
      show ¬ q + 11 = 10 by omega, if_true, if_false]
    rw [h]
    ring

/-- Controls: the entry's data a(1..27). -/
theorem controls : a 1 = 0 ∧ a 2 = 8 ∧ a 3 = 248 ∧ a 4 = 2088 ∧ a 5 = 9940 ∧ a 6 = 33860 ∧
    a 7 = 92934 ∧ a 8 = 219352 ∧ a 9 = 463208 ∧ a 10 = 898020 ∧ a 11 = 1626970 ∧
    a 12 = 2789864 ∧ a 13 = 4570812 ∧ a 14 = 7206628 ∧ a 15 = 10995950 ∧ a 16 = 16309080 ∧
    a 17 = 23598544 ∧ a 18 = 33410372 ∧ a 19 = 46396098 ∧ a 20 = 63325480 ∧ a 21 = 85099940 ∧
    a 22 = 112766724 ∧ a 23 = 147533782 ∧ a 24 = 190785368 ∧ a 25 = 244098360 ∧
    a 26 = 309259300 ∧ a 27 = 388282154 := by
  obtain ⟨v1, v2, v3, v4, v5, v6⟩ := small
  exact ⟨by exact_mod_cast v1, by exact_mod_cast v2, by exact_mod_cast v3, by exact_mod_cast v4,
    by exact_mod_cast v5, by exact_mod_cast v6, val 7 _ (by norm_num) (by norm_num),
    val 8 _ (by norm_num) (by norm_num), val 9 _ (by norm_num) (by norm_num),
    val 10 _ (by norm_num) (by norm_num), val 11 _ (by norm_num) (by norm_num),
    val 12 _ (by norm_num) (by norm_num), val 13 _ (by norm_num) (by norm_num),
    val 14 _ (by norm_num) (by norm_num), val 15 _ (by norm_num) (by norm_num),
    val 16 _ (by norm_num) (by norm_num), val 17 _ (by norm_num) (by norm_num),
    val 18 _ (by norm_num) (by norm_num), val 19 _ (by norm_num) (by norm_num),
    val 20 _ (by norm_num) (by norm_num), val 21 _ (by norm_num) (by norm_num),
    val 22 _ (by norm_num) (by norm_num), val 23 _ (by norm_num) (by norm_num),
    val 24 _ (by norm_num) (by norm_num), val 25 _ (by norm_num) (by norm_num),
    val 26 _ (by norm_num) (by norm_num), val 27 _ (by norm_num) (by norm_num)⟩

/-- Both of Barker's conjectures. -/
theorem conjecture :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * (1 - X) ^ 7 =
      2 * X ^ 2 * (4 + 96 * X + 260 * X ^ 2 + 126 * X ^ 3 - 136 * X ^ 4 + 43 * X ^ 5 -
        49 * X ^ 6 + 19 * X ^ 7 - 3 * X ^ 8) ∧
    ∀ n : ℕ, 10 < n → (a n : ℤ) = 7 * a (n - 1) - 21 * a (n - 2) + 35 * a (n - 3) -
      35 * a (n - 4) + 21 * a (n - 5) - 7 * a (n - 6) + a (n - 7) :=
  ⟨gf, recurrence⟩

end OMA.S_oeis_a221518

theorem OMA.solution : type_of% @OMA.S_oeis_a221518.main :=
  OMA.S_oeis_a221518.conjecture
