import OMAStatements.S_oeis_a208556
import Mathlib
-- Credit: @ptc-prover-bot

/-!
Proof idea. The vertical rule (no 0?1 in a column) says: in each column, a 0 in row `i`
forces a 0 in row `i + 2`. The horizontal rule (no 000, no 001) says: in each row, positions
`j, j + 1` are not both 0 whenever `j + 2 < n`. Both rules only couple row 0 with row 2 and
row 1 with row 3, so the count is `T n ^ 2`, where `T n` counts length-`n` words over the
three column states `(0,0), (1,0), (1,1)` of a pair of rows. A first-letter recursion gives
`T (k+1) = 3 J (k+2)` with `J` the Jacobsthal numbers, and `3 J m = 2^m - (-1)^m`.
-/

namespace A208556Proof

open OMA.S_oeis_a208556 PowerSeries Finset

open scoped Classical

abbrev St := Fin 2 × Fin 2

/-- Column state of a pair of rows `(i, i+2)`: a top 0 forces a bottom 0. -/
def Sok (s : St) : Prop := s.1.val = 0 → s.2.val = 0

/-- Consecutive column states: neither row has two consecutive zeros. -/
def ok (s t : St) : Prop := ¬ (s.1.val = 0 ∧ t.1.val = 0) ∧ ¬ (s.2.val = 0 ∧ t.2.val = 0)

/-- A word of column states; the adjacency rule is only imposed when `j + 2 < k`. -/
def Valid {k : ℕ} (v : Fin k → St) : Prop :=
  (∀ j, Sok (v j)) ∧ ∀ j : ℕ, ∀ h : j + 2 < k, ok (v ⟨j, by omega⟩) (v ⟨j + 1, by omega⟩)

lemma cons_mk_zero {k : ℕ} (s : St) (v : Fin (k + 1) → St) (h : 0 < k + 2) :
    (Fin.cons s v : Fin (k + 2) → St) ⟨0, h⟩ = s := by
  rw [show (⟨0, h⟩ : Fin (k + 2)) = 0 from rfl, Fin.cons_zero]

lemma cons_mk_succ {k : ℕ} (s : St) (v : Fin (k + 1) → St) (j : ℕ) (h : j + 1 < k + 2) :
    (Fin.cons s v : Fin (k + 2) → St) ⟨j + 1, h⟩ = v ⟨j, by omega⟩ := by
  rw [show (⟨j + 1, h⟩ : Fin (k + 2)) = Fin.succ ⟨j, by omega⟩ from rfl, Fin.cons_succ]

lemma valid_cons {k : ℕ} (s : St) (v : Fin (k + 1) → St) :
    Valid (Fin.cons s v : Fin (k + 2) → St) ↔ Sok s ∧ (1 ≤ k → ok s (v 0)) ∧ Valid v := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨by simpa using h1 0, fun hk => ?_, fun j => by simpa using h1 j.succ,
      fun j hj => ?_⟩
    · have := h2 0 (by omega)
      rw [cons_mk_zero, cons_mk_succ] at this
      exact this
    · have := h2 (j + 1) (by omega)
      rw [cons_mk_succ, cons_mk_succ] at this
      exact this
  · rintro ⟨hs, h0, hv1, hv2⟩
    refine ⟨fun j => ?_, fun j hj => ?_⟩
    · refine Fin.cases ?_ (fun i => ?_) j
      · simpa using hs
      · simpa using hv1 i
    · rcases j with _ | j
      · rw [cons_mk_zero, cons_mk_succ]
        exact h0 (by omega)
      · rw [cons_mk_succ, cons_mk_succ]
        exact hv2 j (by omega)

/-- Number of valid words of length `k`. -/
noncomputable def T (k : ℕ) : ℕ := (univ.filter (fun v : Fin k → St => Valid v)).card

/-- Number of valid words of length `k + 1` with first letter `s`. -/
noncomputable def E (k : ℕ) (s : St) : ℕ :=
  (univ.filter (fun v : Fin k → St => Valid (Fin.cons s v : Fin (k + 1) → St))).card

lemma T_succ (k : ℕ) : T (k + 1) = ∑ s, E k s := by
  unfold T E
  simp only [card_filter]
  rw [← Fintype.sum_equiv (Fin.consEquiv fun _ => St)
    (fun p => if Valid (Fin.cons p.1 p.2 : Fin (k + 1) → St) then 1 else 0)
    (fun w => if Valid w then 1 else 0) (fun p => rfl), Fintype.sum_prod_type]

lemma E_zero (s : St) : E 0 s = if Sok s then 1 else 0 := by
  have h : ∀ v : Fin 0 → St, Valid (Fin.cons s v : Fin 1 → St) ↔ Sok s := fun v =>
    ⟨fun h => by simpa using h.1 0,
     fun h => ⟨fun j => by fin_cases j; simpa using h, fun j hj => by omega⟩⟩
  simp only [E, card_filter, Fintype.sum_unique, h]

lemma E_succ (k : ℕ) (s : St) :
    E (k + 1) s = ∑ t, if Sok s ∧ (1 ≤ k → ok s t) then E k t else 0 := by
  unfold E
  rw [card_filter]
  rw [← Fintype.sum_equiv (Fin.consEquiv fun _ => St)
    (fun p => if Valid (Fin.cons s (Fin.cons p.1 p.2 : Fin (k + 1) → St) : Fin (k + 2) → St)
      then 1 else 0)
    (fun w => if Valid (Fin.cons s w : Fin (k + 2) → St) then 1 else 0) (fun p => rfl),
    Fintype.sum_prod_type]
  refine sum_congr rfl fun t _ => ?_
  rcases Classical.em (Sok s ∧ (1 ≤ k → ok s t)) with h | h
  · rw [if_pos h, card_filter]
    refine sum_congr rfl fun w _ => ?_
    dsimp only
    rw [valid_cons, Fin.cons_zero]
    split_ifs with h1 h2 h2
    · rfl
    · exact absurd h1.2.2 h2
    · exact absurd ⟨h.1, h.2, h2⟩ h1
    · rfl
  · rw [if_neg h]
    refine sum_eq_zero fun w _ => ?_
    dsimp only
    rw [valid_cons, Fin.cons_zero, if_neg]
    exact fun hh => h ⟨hh.1, hh.2.1⟩

/-- Jacobsthal numbers. -/
def jac : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => jac (n + 1) + 2 * jac n

def jw (k : ℕ) (s : St) : ℕ := if s = (1, 1) then jac (k + 1) else jac k

lemma E_closed (k : ℕ) (s : St) : E (k + 1) s = if Sok s then 3 * jw (k + 1) s else 0 := by
  induction k generalizing s with
  | zero =>
    rw [E_succ]
    simp only [E_zero, Fintype.sum_prod_type, Fin.sum_univ_two]
    fin_cases s <;> simp [Sok, jw, jac]
  | succ k ih =>
    rw [E_succ]
    simp only [ih]
    fin_cases s <;> simp [Fintype.sum_prod_type, Fin.sum_univ_two, Sok, ok, jw, jac]
    all_goals ring

lemma T_closed (k : ℕ) : T (k + 1) = 3 * jac (k + 2) := by
  rw [T_succ]
  rcases k with _ | k
  · simp only [E_zero, Fintype.sum_prod_type, Fin.sum_univ_two]
    simp [Sok, jac]
  · simp only [E_closed, Fintype.sum_prod_type, Fin.sum_univ_two]
    simp [Sok, jw, jac]
    ring

/-! Splitting an array into the two row pairs. -/

section split

variable {n : ℕ}

def pr (x : Fin 4 → Fin n → Fin 2) (a b : Fin 4) : Fin n → St := fun j => (x a j, x b j)

lemma get_val (x : Fin 4 → Fin n → Fin 2) (i : ℕ) (hi : i < 4) (j : ℕ) (hj : j < n) :
    OMA.S_oeis_a208556.get x i j = (x ⟨i, hi⟩ ⟨j, hj⟩).val := by
  unfold OMA.S_oeis_a208556.get
  rw [dif_pos ⟨hi, hj⟩]

lemma get_le (x : Fin 4 → Fin n → Fin 2) (i j : ℕ) : OMA.S_oeis_a208556.get x i j ≤ 1 := by
  unfold OMA.S_oeis_a208556.get
  split
  · rename_i h
    have := (x ⟨i, h.1⟩ ⟨j, h.2⟩).isLt
    omega
  · omega

lemma tri_bad (c : ℕ) (hc : c ≤ 1) : ¬ ((0, 0, c) ≠ ((0 : ℕ), (0 : ℕ), (0 : ℕ)) ∧
    (0, 0, c) ≠ ((0 : ℕ), (0 : ℕ), (1 : ℕ))) := by
  interval_cases c <;> simp

lemma tri_good (a b c : ℕ) (h : ¬ (a = 0 ∧ b = 0)) :
    (a, b, c) ≠ ((0 : ℕ), (0 : ℕ), (0 : ℕ)) ∧ (a, b, c) ≠ ((0 : ℕ), (0 : ℕ), (1 : ℕ)) := by
  constructor <;> intro e <;> simp only [Prod.mk.injEq] at e <;> omega

lemma vert_bad (b c : ℕ) (hb : b ≤ 1) (hc : c ≤ 1)
    (h : (0, b, c) ≠ ((0 : ℕ), (0 : ℕ), (1 : ℕ)) ∧ (0, b, c) ≠ ((0 : ℕ), (1 : ℕ), (1 : ℕ))) :
    c = 0 := by
  interval_cases b <;> interval_cases c <;> simp_all

lemma vert_good (a b c : ℕ) (h : a = 0 → c = 0) :
    (a, b, c) ≠ ((0 : ℕ), (0 : ℕ), (1 : ℕ)) ∧ (a, b, c) ≠ ((0 : ℕ), (1 : ℕ), (1 : ℕ)) := by
  constructor <;> intro e <;> simp only [Prod.mk.injEq] at e <;> omega

lemma key (x : Fin 4 → Fin n → Fin 2) :
    avoids x = true ↔ Valid (pr x 0 2) ∧ Valid (pr x 1 3) := by
  simp only [avoids, decide_eq_true_eq]
  constructor
  · rintro ⟨H, V⟩
    have hH : ∀ i (hi : i < 4) j (hj : j + 2 < n),
        ¬ ((x ⟨i, hi⟩ ⟨j, by omega⟩).val = 0 ∧ (x ⟨i, hi⟩ ⟨j + 1, by omega⟩).val = 0) := by
      intro i hi j hj ⟨h1, h2⟩
      have := H i hi j (by omega)
      rw [get_val x i hi j (by omega), get_val x i hi (j + 1) (by omega), h1, h2] at this
      exact tri_bad _ (get_le x i (j + 2)) this
    have hV : ∀ i (hi : i < 2) j (hj : j < n),
        (x ⟨i, by omega⟩ ⟨j, hj⟩).val = 0 → (x ⟨i + 2, by omega⟩ ⟨j, hj⟩).val = 0 := by
      intro i hi j hj h1
      have := V i hi j hj
      rw [get_val x i (by omega) j hj, get_val x (i + 2) (by omega) j hj, h1] at this
      exact vert_bad _ _ (get_le x (i + 1) j) (by have := (x ⟨i + 2, by omega⟩ ⟨j, hj⟩).isLt; omega)
        this
    exact ⟨⟨fun j h => hV 0 (by norm_num) j j.isLt h, fun j hj => ⟨hH 0 (by norm_num) j hj,
        hH 2 (by norm_num) j hj⟩⟩,
      ⟨fun j h => hV 1 (by norm_num) j j.isLt h, fun j hj => ⟨hH 1 (by norm_num) j hj,
        hH 3 (by norm_num) j hj⟩⟩⟩
  · rintro ⟨⟨S1, O1⟩, ⟨S2, O2⟩⟩
    refine ⟨fun i hi j hj => ?_, fun i hi j hj => ?_⟩
    · have hj2 : j + 2 < n := by omega
      rw [get_val x i hi j (by omega), get_val x i hi (j + 1) (by omega)]
      apply tri_good
      interval_cases i
      · exact (O1 j hj2).1
      · exact (O2 j hj2).1
      · exact (O1 j hj2).2
      · exact (O2 j hj2).2
    · rw [get_val x i (by omega) j hj, get_val x (i + 2) (by omega) j hj]
      apply vert_good
      interval_cases i
      · exact S1 ⟨j, hj⟩
      · exact S2 ⟨j, hj⟩

def splitEquiv (n : ℕ) : (Fin 4 → Fin n → Fin 2) ≃ (Fin n → St) × (Fin n → St) where
  toFun x := (pr x 0 2, pr x 1 3)
  invFun p := ![fun j => (p.1 j).1, fun j => (p.2 j).1, fun j => (p.1 j).2, fun j => (p.2 j).2]
  left_inv x := by
    funext i
    fin_cases i <;> rfl
  right_inv p := rfl

lemma card_split (n : ℕ) :
    ((univ : Finset (Fin 4 → Fin n → Fin 2)).filter (fun x => avoids x)).card = T n ^ 2 := by
  rw [card_equiv (splitEquiv n)
    (t := (univ.filter fun v : Fin n → St => Valid v) ×ˢ (univ.filter fun v : Fin n → St => Valid v))]
  · rw [card_product, T, sq]
  · intro x
    simp only [mem_filter, mem_univ, true_and, mem_product, key]
    exact Iff.rfl

end split

lemma jac_closed : ∀ m : ℕ, 3 * (jac m : ℚ) = 2 ^ m - (-1) ^ m
  | 0 => by simp [jac]
  | 1 => by norm_num [jac]
  | m + 2 => by
    have h1 := jac_closed (m + 1)
    have h0 := jac_closed m
    rw [jac]
    push_cast
    linear_combination h1 + 2 * h0

lemma a_val (n : ℕ) (hn : 1 ≤ n) : (a n : ℚ) = (2 ^ (n + 1) - (-1) ^ (n + 1)) ^ 2 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [a, card_split, T_closed]
  push_cast
  rw [jac_closed]

lemma a_val' (m : ℕ) : (a (m + 1) : ℚ) = 4 * 4 ^ (m + 1) + 4 * (-2) ^ (m + 1) + 1 := by
  rw [a_val (m + 1) (by omega), neg_pow (2 : ℚ) (m + 1),
    show (4 : ℚ) ^ (m + 1) = (2 ^ (m + 1)) ^ 2 by rw [← pow_mul, mul_comm, pow_mul]; norm_num]
  have h1 : ((-1 : ℚ) ^ (m + 1)) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  linear_combination h1

lemma geom (r : ℚ) : mk (fun n => r ^ n) * (1 - C r * X) = 1 := by
  ext n
  rw [mul_sub, mul_one, ← mul_assoc, map_sub]
  rcases n with _ | n
  · simp
  · rw [coeff_succ_mul_X, mul_comm, coeff_C_mul]
    simp [pow_succ, coeff_one]
    ring

lemma gf : PowerSeries.mk (fun n => if n < 1 then 0 else (a n : ℚ)) *
    ((1 - X) * (1 + 2 * X) * (1 - 4 * X) : PowerSeries ℚ) = 9 * X * (1 + 6 * X - 8 * X ^ 2) := by
  have hA : mk (fun n => (4 : ℚ) ^ n) * (1 - 4 * X) = 1 := by
    have := geom 4
    rwa [show (C (4 : ℚ) : PowerSeries ℚ) = 4 from map_ofNat C 4] at this
  have hB : mk (fun n => (-2 : ℚ) ^ n) * (1 + 2 * X) = 1 := by
    have := geom (-2)
    rwa [map_neg, show (C (2 : ℚ) : PowerSeries ℚ) = 2 from map_ofNat C 2, neg_mul,
      sub_neg_eq_add] at this
  have hG : mk (fun n => (1 : ℚ) ^ n) * (1 - X) = 1 := by
    have := geom 1
    rwa [map_one, one_mul] at this
  have hF : PowerSeries.mk (fun n => if n < 1 then 0 else (a n : ℚ)) =
      4 * mk (fun n => (4 : ℚ) ^ n) + 4 * mk (fun n => (-2 : ℚ) ^ n) +
        mk (fun n => (1 : ℚ) ^ n) - 9 := by
    rw [show (4 : PowerSeries ℚ) = C 4 from (map_ofNat C 4).symm,
      show (9 : PowerSeries ℚ) = C 9 from (map_ofNat C 9).symm]
    ext n
    simp only [map_add, map_sub, coeff_C_mul, coeff_mk, coeff_C]
    rcases n with _ | m
    · norm_num
    · simp only [show ¬ (m + 1 < 1) by omega, if_false, a_val', one_pow, Nat.add_one_ne_zero]
      ring
  rw [hF]
  linear_combination (4 * (1 - X) * (1 + 2 * X)) * hA + (4 * (1 - X) * (1 - 4 * X)) * hB +
    ((1 + 2 * X) * (1 - 4 * X)) * hG

theorem main' :
    (PowerSeries.mk (fun n => if n < 1 then 0 else (a n : ℚ)) *
      ((1 - X) * (1 + 2 * X) * (1 - 4 * X) : PowerSeries ℚ) = 9 * X * (1 + 6 * X - 8 * X ^ 2)) ∧
    (∀ n : ℕ, 1 ≤ n → Even n → (a n : ℚ) = ((2 : ℚ) ^ (n + 1) + 1) ^ 2) ∧
    (∀ n : ℕ, 1 ≤ n → Odd n → (a n : ℚ) = ((2 : ℚ) ^ (n + 1) - 1) ^ 2) := by
  refine ⟨gf, fun n hn he => ?_, fun n hn ho => ?_⟩
  · rw [a_val n hn, Odd.neg_one_pow he.add_one]
    ring
  · rw [a_val n hn, Even.neg_one_pow ho.add_one]

end A208556Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a208556.main := A208556Proof.main'

