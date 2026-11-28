import OMAStatements.S_oeis_a267161
import Mathlib

/-!
Rule 107 from a single ON cell settles, from step 7 on, into a pattern of period 4 that moves right
at speed one. With `u = t - i` (the distance of cell `i` from the right edge of the light cone) the
row at time `t ≥ 7` depends only on `t mod 4` and `u`:

* `t ≡ 0`: ON exactly at `u ∈ {0,1,2,8,9,10}`;
* `t ≡ 1`: OFF exactly at `u ∈ {0,2,8,10}`;
* `t ≡ 2`: ON exactly at `u ∈ {0,1,3,4,8,9,11,12}`;
* `t ≡ 3`: OFF exactly at `u ∈ {0,8}`.

So the number of OFF cells in row `t ≥ 7` is `2t-5, 4, 2t-7, 2` for `t ≡ 0,1,2,3 (mod 4)`, which
gives the recurrence; the generating function follows by comparing coefficients.
-/

namespace OMA.A267161Proof

open OMA.S_oeis_a267161 PowerSeries

/-- Rule 107 as a truth table. -/
theorem rule107 (l c r : Bool) :
    ruleOut 107 l c r = ((!l && !c) || (!l && r) || (l && !c && r) || (l && c && !r)) := by
  cases l <;> cases c <;> cases r <;> decide

/-- Outside the light cone every cell is the background, which is ON exactly at odd times. -/
theorem cone : ∀ (t : ℕ) (i : ℤ), (i < -(t : ℤ) ∨ (t : ℤ) < i) →
    cell 107 t i = decide (t % 2 = 1) := by
  intro t
  induction t with
  | zero =>
    intro i hi
    have h0 : i ≠ 0 := by omega
    simp [cell, h0]
  | succ t ih =>
    intro i hi
    have h1 := ih (i - 1) (by omega)
    have h2 := ih i (by omega)
    have h3 := ih (i + 1) (by omega)
    show ruleOut 107 (cell 107 t (i - 1)) (cell 107 t i) (cell 107 t (i + 1)) = _
    rw [h1, h2, h3, rule107]
    rcases Nat.mod_two_eq_zero_or_one t with h | h
    · have h' : (t + 1) % 2 = 1 := by omega
      simp [h, h']
    · have h' : (t + 1) % 2 = 0 := by omega
      simp [h, h']

def g0 (u : ℤ) : Bool := decide (u = 0 ∨ u = 1 ∨ u = 2 ∨ u = 8 ∨ u = 9 ∨ u = 10)
def g1 (u : ℤ) : Bool := !decide (u = 0 ∨ u = 2 ∨ u = 8 ∨ u = 10)
def g2 (u : ℤ) : Bool :=
  decide (u = 0 ∨ u = 1 ∨ u = 3 ∨ u = 4 ∨ u = 8 ∨ u = 9 ∨ u = 11 ∨ u = 12)
def g3 (u : ℤ) : Bool := !decide (u = 0 ∨ u = 8)

/-- The row at a time congruent to `r` modulo 4, as a function of `u = t - i`. -/
def G : ℕ → ℤ → Bool
  | 0 => g0
  | 1 => g1
  | 2 => g2
  | _ => g3

theorem G0 : G 0 = g0 := rfl
theorem G1 : G 1 = g1 := rfl
theorem G2 : G 2 = g2 := rfl
theorem G3 : G 3 = g3 := rfl

theorem g0_far (u : ℤ) (h : u < 0 ∨ 10 < u) : g0 u = false := by
  simp [g0]; omega
theorem g1_far (u : ℤ) (h : u < 0 ∨ 10 < u) : g1 u = true := by
  simp [g1]; omega
theorem g2_far (u : ℤ) (h : u < 0 ∨ 12 < u) : g2 u = false := by
  simp [g2]; omega
theorem g3_far (u : ℤ) (h : u < 0 ∨ 8 < u) : g3 u = true := by
  simp [g3]; omega

theorem step01 (u : ℤ) : ruleOut 107 (g0 u) (g0 (u - 1)) (g0 (u - 2)) = g1 u := by
  rcases lt_or_ge u 0 with h | h
  · rw [g0_far u (by omega), g0_far (u - 1) (by omega), g0_far (u - 2) (by omega),
      g1_far u (by omega)]
    decide
  · rcases lt_or_ge u 15 with h2 | h2
    · interval_cases u <;> decide
    · rw [g0_far u (by omega), g0_far (u - 1) (by omega), g0_far (u - 2) (by omega),
        g1_far u (by omega)]
      decide

theorem step12 (u : ℤ) : ruleOut 107 (g1 u) (g1 (u - 1)) (g1 (u - 2)) = g2 u := by
  rcases lt_or_ge u 0 with h | h
  · rw [g1_far u (by omega), g1_far (u - 1) (by omega), g1_far (u - 2) (by omega),
      g2_far u (by omega)]
    decide
  · rcases lt_or_ge u 15 with h2 | h2
    · interval_cases u <;> decide
    · rw [g1_far u (by omega), g1_far (u - 1) (by omega), g1_far (u - 2) (by omega),
        g2_far u (by omega)]
      decide

theorem step23 (u : ℤ) : ruleOut 107 (g2 u) (g2 (u - 1)) (g2 (u - 2)) = g3 u := by
  rcases lt_or_ge u 0 with h | h
  · rw [g2_far u (by omega), g2_far (u - 1) (by omega), g2_far (u - 2) (by omega),
      g3_far u (by omega)]
    decide
  · rcases lt_or_ge u 15 with h2 | h2
    · interval_cases u <;> decide
    · rw [g2_far u (by omega), g2_far (u - 1) (by omega), g2_far (u - 2) (by omega),
        g3_far u (by omega)]
      decide

theorem step30 (u : ℤ) : ruleOut 107 (g3 u) (g3 (u - 1)) (g3 (u - 2)) = g0 u := by
  rcases lt_or_ge u 0 with h | h
  · rw [g3_far u (by omega), g3_far (u - 1) (by omega), g3_far (u - 2) (by omega),
      g0_far u (by omega)]
    decide
  · rcases lt_or_ge u 15 with h2 | h2
    · interval_cases u <;> decide
    · rw [g3_far u (by omega), g3_far (u - 1) (by omega), g3_far (u - 2) (by omega),
        g0_far u (by omega)]
      decide

/-- The row at time 7. -/
theorem base7 (i : ℤ) : cell 107 7 i = g3 (7 - i) := by
  by_cases h : i < -7 ∨ 7 < i
  · rw [cone 7 i (by omega), g3_far (7 - i) (by omega)]
    decide
  · have h1 : -7 ≤ i := by omega
    have h2 : i ≤ 7 := by omega
    interval_cases i <;> decide +kernel

/-- The row at every time `t ≥ 7`. -/
theorem cell_eq : ∀ t : ℕ, 7 ≤ t → ∀ i : ℤ, cell 107 t i = G (t % 4) ((t : ℤ) - i) := by
  intro t ht
  induction t, ht using Nat.le_induction with
  | base =>
    intro i
    rw [base7]
    simp [G]
  | succ t ht ih =>
    intro i
    show ruleOut 107 (cell 107 t (i - 1)) (cell 107 t i) (cell 107 t (i + 1)) = _
    rw [ih (i - 1), ih i, ih (i + 1)]
    have e1 : (t : ℤ) - (i - 1) = ((t + 1 : ℕ) : ℤ) - i := by push_cast; ring
    have e2 : (t : ℤ) - i = ((t + 1 : ℕ) : ℤ) - i - 1 := by push_cast; ring
    have e3 : (t : ℤ) - (i + 1) = ((t + 1 : ℕ) : ℤ) - i - 2 := by push_cast; ring
    rw [e1, e2, e3]
    have hr : t % 4 < 4 := Nat.mod_lt _ (by norm_num)
    have hs : (t + 1) % 4 = (t % 4 + 1) % 4 := by omega
    rw [hs]
    generalize ((t + 1 : ℕ) : ℤ) - i = u
    generalize t % 4 = r at hr ⊢
    interval_cases r
    · exact step01 u
    · exact step12 u
    · exact step23 u
    · exact step30 u

theorem onCount_eq (t : ℕ) (ht : 7 ≤ t) :
    onCount 107 t = ∑ u ∈ Finset.range (2 * t + 1), (if G (t % 4) (u : ℤ) then 1 else 0) := by
  unfold onCount
  rw [← Finset.sum_range_reflect (fun u : ℕ => if G (t % 4) (u : ℤ) then 1 else 0) (2 * t + 1)]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mem_range] at hj
  rw [cell_eq t ht]
  have e : (t : ℤ) - ((j : ℤ) - t) = ((2 * t + 1 - 1 - j : ℕ) : ℤ) := by omega
  rw [e]

theorem sum_split (f : ℕ → ℕ) (t : ℕ) (ht : 7 ≤ t) :
    ∑ u ∈ Finset.range (2 * t + 1), f u
      = ∑ u ∈ Finset.range 15, f u + ∑ x ∈ Finset.range (2 * t - 14), f (15 + x) := by
  rw [← Finset.sum_range_add]
  congr 2
  omega

theorem head0 : ∑ u ∈ Finset.range 15, (if G 0 (u : ℤ) then 1 else 0) = 6 := by decide +kernel
theorem head1 : ∑ u ∈ Finset.range 15, (if G 1 (u : ℤ) then 1 else 0) = 11 := by decide +kernel
theorem head2 : ∑ u ∈ Finset.range 15, (if G 2 (u : ℤ) then 1 else 0) = 8 := by decide +kernel
theorem head3 : ∑ u ∈ Finset.range 15, (if G 3 (u : ℤ) then 1 else 0) = 13 := by decide +kernel

theorem tail0 (m : ℕ) :
    ∑ x ∈ Finset.range m, (if G 0 ((15 + x : ℕ) : ℤ) then 1 else 0) = 0 := by
  apply Finset.sum_eq_zero
  intro x _
  have h : g0 ((15 + x : ℕ) : ℤ) = false := g0_far _ (by omega)
  exact if_neg (by rw [G0, h]; simp)

theorem tail2 (m : ℕ) :
    ∑ x ∈ Finset.range m, (if G 2 ((15 + x : ℕ) : ℤ) then 1 else 0) = 0 := by
  apply Finset.sum_eq_zero
  intro x _
  have h : g2 ((15 + x : ℕ) : ℤ) = false := g2_far _ (by omega)
  exact if_neg (by rw [G2, h]; simp)

theorem tail1 (m : ℕ) :
    ∑ x ∈ Finset.range m, (if G 1 ((15 + x : ℕ) : ℤ) then 1 else 0) = m := by
  have key : ∀ x ∈ Finset.range m, (if G 1 ((15 + x : ℕ) : ℤ) then 1 else 0) = 1 := by
    intro x _
    have h : g1 ((15 + x : ℕ) : ℤ) = true := g1_far _ (by omega)
    exact if_pos (by rw [G1, h])
  rw [Finset.sum_congr rfl key]
  simp

theorem tail3 (m : ℕ) :
    ∑ x ∈ Finset.range m, (if G 3 ((15 + x : ℕ) : ℤ) then 1 else 0) = m := by
  have key : ∀ x ∈ Finset.range m, (if G 3 ((15 + x : ℕ) : ℤ) then 1 else 0) = 1 := by
    intro x _
    have h : g3 ((15 + x : ℕ) : ℤ) = true := g3_far _ (by omega)
    exact if_pos (by rw [G3, h])
  rw [Finset.sum_congr rfl key]
  simp

/-- The number of OFF cells in row `t`. -/
def off (t : ℕ) : ℤ := (2 * t + 1 : ℤ) - onCount 107 t

theorem off0 (t : ℕ) (ht : 7 ≤ t) (h : t % 4 = 0) : off t = 2 * (t : ℤ) - 5 := by
  unfold off
  rw [onCount_eq t ht, h, sum_split _ t ht, head0, tail0]
  omega

theorem off1 (t : ℕ) (ht : 7 ≤ t) (h : t % 4 = 1) : off t = 4 := by
  unfold off
  rw [onCount_eq t ht, h, sum_split _ t ht, head1, tail1]
  omega

theorem off2 (t : ℕ) (ht : 7 ≤ t) (h : t % 4 = 2) : off t = 2 * (t : ℤ) - 7 := by
  unfold off
  rw [onCount_eq t ht, h, sum_split _ t ht, head2, tail2]
  omega

theorem off3 (t : ℕ) (ht : 7 ≤ t) (h : t % 4 = 3) : off t = 2 := by
  unfold off
  rw [onCount_eq t ht, h, sum_split _ t ht, head3, tail3]
  omega

theorem off_rec (m : ℕ) (hm : 6 ≤ m) :
    off (m + 7) = off (m + 5) + off (m + 3) - off (m + 1) := by
  rcases (by omega : m % 4 = 0 ∨ m % 4 = 1 ∨ m % 4 = 2 ∨ m % 4 = 3) with h | h | h | h
  · rw [off3 (m + 7) (by omega) (by omega), off1 (m + 5) (by omega) (by omega),
      off3 (m + 3) (by omega) (by omega), off1 (m + 1) (by omega) (by omega)]
    norm_num
  · rw [off0 (m + 7) (by omega) (by omega), off2 (m + 5) (by omega) (by omega),
      off0 (m + 3) (by omega) (by omega), off2 (m + 1) (by omega) (by omega)]
    push_cast
    ring
  · rw [off1 (m + 7) (by omega) (by omega), off3 (m + 5) (by omega) (by omega),
      off1 (m + 3) (by omega) (by omega), off3 (m + 1) (by omega) (by omega)]
    norm_num
  · rw [off2 (m + 7) (by omega) (by omega), off0 (m + 5) (by omega) (by omega),
      off2 (m + 3) (by omega) (by omega), off0 (m + 1) (by omega) (by omega)]
    push_cast
    ring

theorem a_succ (n : ℕ) : a (n + 1) = a n + off (n + 1) := by
  unfold a off
  rw [Finset.sum_range_succ]

theorem rec_int (m : ℕ) (hm : 6 ≤ m) :
    a (m + 7) = a (m + 6) + a (m + 5) - a (m + 4) + a (m + 3) - a (m + 2) - a (m + 1) + a m := by
  have h7 : a (m + 7) = a (m + 6) + off (m + 7) := a_succ (m + 6)
  have h5 : a (m + 5) = a (m + 4) + off (m + 5) := a_succ (m + 4)
  have h3 : a (m + 3) = a (m + 2) + off (m + 3) := a_succ (m + 2)
  have h1 : a (m + 1) = a m + off (m + 1) := a_succ m
  have h := off_rec m hm
  linarith

theorem rec_main (n : ℕ) (hn : 13 ≤ n) :
    (a n : ℚ) = a (n - 1) + a (n - 2) - a (n - 3) + a (n - 4) - a (n - 5) - a (n - 6)
      + a (n - 7) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 7 := ⟨n - 7, by omega⟩
  have h := rec_int m (by omega)
  have e1 : m + 7 - 1 = m + 6 := by omega
  have e2 : m + 7 - 2 = m + 5 := by omega
  have e3 : m + 7 - 3 = m + 4 := by omega
  have e4 : m + 7 - 4 = m + 3 := by omega
  have e5 : m + 7 - 5 = m + 2 := by omega
  have e6 : m + 7 - 6 = m + 1 := by omega
  have e7 : m + 7 - 7 = m := by omega
  rw [e1, e2, e3, e4, e5, e6, e7, h]
  push_cast
  ring

theorem on_0 : onCount 107 0 = 1 := by decide +kernel
theorem on_1 : onCount 107 1 = 1 := by decide +kernel
theorem on_2 : onCount 107 2 = 3 := by decide +kernel
theorem on_3 : onCount 107 3 = 5 := by decide +kernel
theorem on_4 : onCount 107 4 = 6 := by decide +kernel
theorem on_5 : onCount 107 5 = 8 := by decide +kernel
theorem on_6 : onCount 107 6 = 7 := by decide +kernel

theorem off_1 : off 1 = 2 := by unfold off; rw [on_1]; norm_num
theorem off_2 : off 2 = 2 := by unfold off; rw [on_2]; norm_num
theorem off_3 : off 3 = 2 := by unfold off; rw [on_3]; norm_num
theorem off_4 : off 4 = 3 := by unfold off; rw [on_4]; norm_num
theorem off_5 : off 5 = 3 := by unfold off; rw [on_5]; norm_num
theorem off_6 : off 6 = 6 := by unfold off; rw [on_6]; norm_num
theorem off_7 : off 7 = 2 := off3 7 (by norm_num) (by norm_num)
theorem off_8 : off 8 = 11 := by rw [off0 8 (by norm_num) (by norm_num)]; norm_num
theorem off_9 : off 9 = 4 := off1 9 (by norm_num) (by norm_num)
theorem off_10 : off 10 = 13 := by rw [off2 10 (by norm_num) (by norm_num)]; norm_num
theorem off_11 : off 11 = 2 := off3 11 (by norm_num) (by norm_num)
theorem off_12 : off 12 = 19 := by rw [off0 12 (by norm_num) (by norm_num)]; norm_num

theorem a_0 : a 0 = 0 := by simp [a, on_0]
theorem a_1 : a 1 = 2 := by
  have h : a 1 = a 0 + off 1 := a_succ 0
  rw [h, a_0, off_1]; norm_num
theorem a_2 : a 2 = 4 := by
  have h : a 2 = a 1 + off 2 := a_succ 1
  rw [h, a_1, off_2]; norm_num
theorem a_3 : a 3 = 6 := by
  have h : a 3 = a 2 + off 3 := a_succ 2
  rw [h, a_2, off_3]; norm_num
theorem a_4 : a 4 = 9 := by
  have h : a 4 = a 3 + off 4 := a_succ 3
  rw [h, a_3, off_4]; norm_num
theorem a_5 : a 5 = 12 := by
  have h : a 5 = a 4 + off 5 := a_succ 4
  rw [h, a_4, off_5]; norm_num
theorem a_6 : a 6 = 18 := by
  have h : a 6 = a 5 + off 6 := a_succ 5
  rw [h, a_5, off_6]; norm_num
theorem a_7 : a 7 = 20 := by
  have h : a 7 = a 6 + off 7 := a_succ 6
  rw [h, a_6, off_7]; norm_num
theorem a_8 : a 8 = 31 := by
  have h : a 8 = a 7 + off 8 := a_succ 7
  rw [h, a_7, off_8]; norm_num
theorem a_9 : a 9 = 35 := by
  have h : a 9 = a 8 + off 9 := a_succ 8
  rw [h, a_8, off_9]; norm_num
theorem a_10 : a 10 = 48 := by
  have h : a 10 = a 9 + off 10 := a_succ 9
  rw [h, a_9, off_10]; norm_num
theorem a_11 : a 11 = 50 := by
  have h : a 11 = a 10 + off 11 := a_succ 10
  rw [h, a_10, off_11]; norm_num
theorem a_12 : a 12 = 69 := by
  have h : a 12 = a 11 + off 12 := a_succ 11
  rw [h, a_11, off_12]; norm_num

theorem gf :
    (PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) ^ 3 * (1 + X) ^ 2 * (1 + X ^ 2) : PowerSeries ℚ)
      = X * (2 + 2 * X + X ^ 3 - X ^ 4 + X ^ 5 - X ^ 6 + 4 * X ^ 7 + X ^ 8 - X ^ 9 - X ^ 10
        + X ^ 11)) := by
  have hD : ((1 - X) ^ 3 * (1 + X) ^ 2 * (1 + X ^ 2) : PowerSeries ℚ)
      = 1 - X ^ 1 - X ^ 2 + X ^ 3 - X ^ 4 + X ^ 5 + X ^ 6 - X ^ 7 := by ring
  have hN : (X * (2 + 2 * X + X ^ 3 - X ^ 4 + X ^ 5 - X ^ 6 + 4 * X ^ 7 + X ^ 8 - X ^ 9 - X ^ 10
      + X ^ 11) : PowerSeries ℚ)
      = X ^ 1 + X ^ 1 + (X ^ 2 + X ^ 2) + X ^ 4 - X ^ 5 + X ^ 6 - X ^ 7
        + (X ^ 8 + X ^ 8 + X ^ 8 + X ^ 8) + X ^ 9 - X ^ 10 - X ^ 11 + X ^ 12 := by ring
  rw [hD, hN]
  ext n
  simp only [mul_sub, mul_add, mul_one, map_sub, map_add, coeff_mul_X_pow', coeff_X_pow, coeff_mk]
  rcases lt_or_ge n 13 with h | h
  · interval_cases n <;>
      norm_num [a_0, a_1, a_2, a_3, a_4, a_5, a_6, a_7, a_8, a_9, a_10, a_11, a_12]
  · have hr := rec_main n h
    rw [if_pos (by omega : 1 ≤ n), if_pos (by omega : 2 ≤ n), if_pos (by omega : 3 ≤ n),
      if_pos (by omega : 4 ≤ n), if_pos (by omega : 5 ≤ n), if_pos (by omega : 6 ≤ n),
      if_pos (by omega : 7 ≤ n), if_neg (by omega : ¬ n = 1), if_neg (by omega : ¬ n = 2),
      if_neg (by omega : ¬ n = 4), if_neg (by omega : ¬ n = 5), if_neg (by omega : ¬ n = 6),
      if_neg (by omega : ¬ n = 7), if_neg (by omega : ¬ n = 8), if_neg (by omega : ¬ n = 9),
      if_neg (by omega : ¬ n = 10), if_neg (by omega : ¬ n = 11), if_neg (by omega : ¬ n = 12)]
    rw [hr]
    ring

end OMA.A267161Proof

open OMA.A267161Proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a267161.main :=
  ⟨rec_main, gf⟩
