import OMAStatements.S_oeis_a284350
import Mathlib.Data.List.FinRange
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

-- Credit: @CubeJerry. Agent: codex. Model: gpt-6.2-astra.
-- New three-valued invariant for Rule873, retaining axis reflection correlations.
-- Source: https://oeis.org/A284350. Generic infrastructure adapted from our Rule998 proof.

/- Module A284350Core -/

namespace A284350

open OMA.S_oeis_a284350

lemma cell_swap (code n : ℕ) (x y : ℤ) : cell code n x y = cell code n y x := by
  induction n generalizing x y with
  | zero => simp [cell, and_comm]
  | succ n ih =>
    simp only [cell, ih x y, ih (x + 1) y, ih (x - 1) y,
      ih x (y + 1), ih x (y - 1)]
    congr 1
    omega

lemma cell_neg_left (code n : ℕ) (x y : ℤ) : cell code n (-x) y = cell code n x y := by
  induction n generalizing x y with
  | zero => simp [cell]
  | succ n ih =>
    simp only [cell]
    rw [show -x + 1 = -(x - 1) by omega,
      show -x - 1 = -(x + 1) by omega, ih, ih, ih, ih, ih]
    congr 1
    omega

def prevN (x : ℕ) : ℕ := if x = 0 then 1 else x - 1

def quad (n x y : ℕ) : Bool := cell 873 n x y

def rule (c e w u d : Bool) : Bool :=
  (873 : ℕ).testBit (c.toNat + 2 * (e.toNat + w.toNat + u.toNat + d.toNat))

lemma quad_swap (n x y : ℕ) : quad n x y = quad n y x := cell_swap 873 n x y

lemma left_prev (n x y : ℕ) : cell 873 n ((x : ℤ) - 1) y = quad n (prevN x) y := by
  by_cases h : x = 0
  · subst x
    simpa [prevN, quad] using cell_neg_left 873 n 1 y
  · congr 2
    simp only [prevN, h, if_false]
    omega

lemma down_prev (n x y : ℕ) : cell 873 n x ((y : ℤ) - 1) = quad n x (prevN y) := by
  rw [cell_swap, left_prev, quad_swap]

lemma quad_succ (n x y : ℕ) : quad (n + 1) x y =
    rule (quad n x y) (quad n (x + 1) y) (quad n (prevN x) y)
      (quad n x (y + 1)) (quad n x (prevN y)) := by
  simp only [quad, cell, rule, Nat.cast_add, Nat.cast_one, left_prev, down_prev]

lemma quad_outside (n x y : ℕ) (h : n < x + y) : quad n x y = decide (0 < n) := by
  induction n generalizing x y with
  | zero => simp [quad, cell]; omega
  | succ n ih =>
    have hx : n < prevN x + y := by unfold prevN; split <;> omega
    have hy : n < x + prevN y := by unfold prevN; split <;> omega
    rw [quad_succ, ih x y (by omega), ih (x + 1) y (by omega),
      ih (prevN x) y hx, ih x (y + 1) (by omega), ih x (prevN y) hy]
    cases n <;> norm_num [rule] <;> decide

/-- Values zero and one assert a cell value; two leaves it unspecified. -/
def Agrees (v : ℕ) (b : Bool) : Prop := v = 2 ∨ v = b.toNat

instance (v : ℕ) (b : Bool) : Decidable (Agrees v b) := by
  unfold Agrees
  infer_instance

def ones (v : ℕ) : ℕ := if v = 1 then 1 else 0
def possible (v : ℕ) : ℕ := if v = 0 then 0 else 1

def triNext (c e w u d : ℕ) : ℕ :=
  let lo := ones e + ones w + ones u + ones d
  let hi := possible e + possible w + possible u + possible d
  if (if c = 0 then hi = 0 ∨ 3 ≤ lo
      else if c = 1 then (1 ≤ lo ∧ hi ≤ 2) ∨ 4 ≤ lo else 4 ≤ lo) then 1
  else if (if c = 0 then 1 ≤ lo ∧ hi ≤ 2
      else if c = 1 then hi = 0 ∨ (lo = 3 ∧ hi = 3) else False) then 0
  else 2

def triAxis (c e w u : ℕ) : ℕ :=
  if c = 1 ∧ e = 1 ∧ w = 1 then 1 else triNext c e w u u

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def triNext_sound : ∀ c e w u d : Fin 3, ∀ bc be bw bu bd : Bool,
    Agrees c bc → Agrees e be → Agrees w bw → Agrees u bu → Agrees d bd →
      Agrees (triNext c e w u d) (rule bc be bw bu bd) := by
  decide

def compatible (v c e w u d : ℕ) : Bool :=
  v == 2 || v == triNext c e w u d

lemma compatible_sound {v c e w u d : ℕ}
    (hc : c < 3) (he : e < 3) (hw : w < 3) (hu : u < 3) (hd : d < 3)
    (h : compatible v c e w u d = true)
    {bc be bw bu bd : Bool}
    (hbc : Agrees c bc) (hbe : Agrees e be) (hbw : Agrees w bw)
    (hbu : Agrees u bu) (hbd : Agrees d bd) : Agrees v (rule bc be bw bu bd) := by
  simp only [compatible, Bool.or_eq_true, beq_iff_eq] at h
  rcases h with h | h
  · exact Or.inl h
  · rw [h]
    exact triNext_sound ⟨c, hc⟩ ⟨e, he⟩ ⟨w, hw⟩ ⟨u, hu⟩ ⟨d, hd⟩
      bc be bw bu bd hbc hbe hbw hbu hbd

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def triAxis_sound : ∀ c e w u : Fin 3, ∀ bc be bw bu : Bool,
    Agrees c bc → Agrees e be → Agrees w bw → Agrees u bu →
      Agrees (triAxis c e w u) (rule bc be bw bu bu) := by
  decide

def compatibleAxis (v c e w u : ℕ) : Bool :=
  v == 2 || v == triAxis c e w u

lemma compatibleAxis_sound {v c e w u : ℕ}
    (hc : c < 3) (he : e < 3) (hw : w < 3) (hu : u < 3)
    (h : compatibleAxis v c e w u = true)
    {bc be bw bu : Bool}
    (hbc : Agrees c bc) (hbe : Agrees e be) (hbw : Agrees w bw)
    (hbu : Agrees u bu) : Agrees v (rule bc be bw bu bu) := by
  simp only [compatibleAxis, Bool.or_eq_true, beq_iff_eq] at h
  rcases h with h | h
  · exact Or.inl h
  · rw [h]
    exact triAxis_sound ⟨c, hc⟩ ⟨e, he⟩ ⟨w, hw⟩ ⟨u, hu⟩
      bc be bw bu hbc hbe hbw hbu

end A284350

/- Module A284350Data -/

namespace A284350

def tipRow (p y : ℕ) : ℕ :=
  ([87108, 87381, 148821, 169301, 173397, 83284, 69905, 148821, 169301, 173397, 87380, 70997, 152645, 169301, 173397, 87364, 69905, 148805, 168213, 173397, 87364, 87317, 152917, 169301, 173141, 87380, 86353, 152661, 168277, 173141, 87380, 70933, 152645, 169301, 173141, 87364, 70993, 148805, 169237, 173141] : List ℕ)[p * 5 + y]?.getD 0

def tip (p d y : ℕ) : ℕ := tipRow p y / 4 ^ d % 4

set_option maxRecDepth 10000 in
def tip_lt_three : ∀ p : Fin 8, ∀ d : Fin 9, ∀ y : Fin 5, tip p d y < 3 := by
  decide

end A284350

/- Module A284350Template -/

namespace A284350

def pattern (n x y : ℕ) : ℕ :=
  let a := max x y
  let b := min x y
  if n < a + b then 1
  else if 4 < b then 2
  else if a + 8 < n then if b = 0 then 1 else 2
  else tip (n % 8) (n - a) b

lemma pattern_swap (n x y : ℕ) : pattern n x y = pattern n y x := by
  simp only [pattern, max_comm x y, min_comm x y]

lemma pattern_lt (n x y : ℕ) : pattern n x y < 3 := by
  unfold pattern
  dsimp
  split_ifs with h1 h2 h3 h4
  all_goals try omega
  exact tip_lt_three ⟨n % 8, Nat.mod_lt _ (by decide)⟩
    ⟨n - max x y, by omega⟩ ⟨min x y, by omega⟩

lemma pattern_small {n m x y : ℕ} (hn : 32 ≤ n) (hm : 32 ≤ m)
    (hx : x ≤ 9) (hy : y ≤ 7) : pattern n x y = pattern m x y := by
  have ha : max x y ≤ 9 := by omega
  have hb : min x y ≤ 7 := by omega
  simp only [pattern, if_neg (show ¬ n < max x y + min x y by omega),
    if_neg (show ¬ m < max x y + min x y by omega),
    if_pos (show max x y + 8 < n by omega),
    if_pos (show max x y + 8 < m by omega)]

lemma pattern_translate {n m x z y : ℕ} (hy : y ≤ 7)
    (hx : 8 ≤ x) (hz : 8 ≤ z) (he : x + m = z + n) (hr : n % 8 = m % 8) :
    pattern n x y = pattern m z y := by
  have hxy : y ≤ x := by omega
  have hzy : y ≤ z := by omega
  have hcone : n < x + y ↔ m < z + y := by omega
  have hinterior : x + 8 < n ↔ z + 8 < m := by omega
  have hdepth : n - x = m - z := by omega
  simp only [pattern, max_eq_left hxy, min_eq_right hxy,
    max_eq_left hzy, min_eq_right hzy,
    hcone, hinterior, hdepth, hr]

lemma pattern_middle {n m x z y : ℕ} (hy : y ≤ 7)
    (hx : 8 ≤ x) (hz : 8 ≤ z) (hn : x + 8 < n) (hm : z + 8 < m) :
    pattern n x y = pattern m z y := by
  have hxy : y ≤ x := by omega
  have hzy : y ≤ z := by omega
  simp only [pattern, max_eq_left hxy, min_eq_right hxy,
    max_eq_left hzy, min_eq_right hzy,
    if_neg (show ¬ n < x + y by omega), if_neg (show ¬ m < z + y by omega),
    if_pos hn, if_pos hm]

def localCheck (n x y : ℕ) : Bool :=
  if y = 0 then
    compatibleAxis (pattern (n + 1) x y) (pattern n x y)
      (pattern n (x + 1) y) (pattern n (prevN x) y) (pattern n x (y + 1))
  else
    compatible (pattern (n + 1) x y) (pattern n x y)
      (pattern n (x + 1) y) (pattern n (prevN x) y)
      (pattern n x (y + 1)) (pattern n x (prevN y))

end A284350

/- Module A284350Local -/

namespace A284350

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
def local_certificate :
    ((List.range 25).all fun t =>
      (List.range 42).all fun x =>
        (List.range 6).all fun y => if y ≤ x then localCheck (t + 15) x y else true) = true := by
  decide

lemma localCheck_finite (n x y : ℕ) (hn : 15 ≤ n) (hn' : n < 40)
    (hx : x < 42) (hy : y < 6) (hyx : y ≤ x) : localCheck n x y = true := by
  have h := (List.all_eq_true.mp local_certificate) (n - 15) (by simp; omega)
  have h := (List.all_eq_true.mp h) x (by simpa)
  have h := (List.all_eq_true.mp h) y (by simpa)
  simpa only [Nat.sub_add_cancel hn, if_pos hyx] using h

lemma prevN_le (x : ℕ) : prevN x ≤ x + 1 := by
  unfold prevN
  split <;> omega

lemma localCheck_small {n m x y : ℕ} (hn : 32 ≤ n) (hm : 32 ≤ m)
    (hx : x ≤ 8) (hy : y ≤ 4) : localCheck n x y = localCheck m x y := by
  have hpx : prevN x ≤ 9 := by have := prevN_le x; omega
  have hpy : prevN y ≤ 7 := by have := prevN_le y; omega
  by_cases hy0 : y = 0
  all_goals simp only [localCheck, hy0, if_true, if_false]
  all_goals congr 1 <;> apply pattern_small <;> omega

lemma localCheck_middle {n m x z y : ℕ} (hy : y ≤ 4)
    (hx : 9 ≤ x) (hz : 9 ≤ z) (hn : x + 10 ≤ n) (hm : z + 10 ≤ m) :
    localCheck n x y = localCheck m z y := by
  have hpx : prevN x = x - 1 := if_neg (by omega)
  have hpz : prevN z = z - 1 := if_neg (by omega)
  have hpy : prevN y ≤ 7 := by have := prevN_le y; omega
  by_cases hy0 : y = 0
  all_goals simp only [localCheck, hy0, if_true, if_false, hpx, hpz]
  all_goals congr 1 <;> apply pattern_middle <;> omega

lemma localCheck_translate {n m x z y : ℕ} (hy : y ≤ 4)
    (hx : 9 ≤ x) (hz : 9 ≤ z) (he : x + m = z + n) (hr : n % 8 = m % 8) :
    localCheck n x y = localCheck m z y := by
  have hpx : prevN x = x - 1 := if_neg (by omega)
  have hpz : prevN z = z - 1 := if_neg (by omega)
  have hpy : prevN y ≤ 7 := by have := prevN_le y; omega
  by_cases hy0 : y = 0
  all_goals simp only [localCheck, hy0, if_true, if_false, hpx, hpz]
  all_goals congr 1 <;> apply pattern_translate <;> omega

lemma localCheck_all (n x y : ℕ) (hn : 15 ≤ n) (hx : x ≤ n + 1) (hy : y ≤ 4) (hyx : y ≤ x) :
    localCheck n x y = true := by
  by_cases hsmall : n < 32
  · exact localCheck_finite n x y hn (by omega) (by omega) (by omega) hyx
  let m := 32 + n % 8
  have hm : 32 ≤ m := by dsimp [m]; omega
  have hm' : m < 40 := by dsimp [m]; omega
  have hr : n % 8 = m % 8 := by dsimp [m]; omega
  by_cases hleft : x ≤ 8
  · rw [localCheck_small (m := m) (by omega) (by omega) hleft hy]
    exact localCheck_finite m x y (by omega) hm' (by omega) (by omega) hyx
  by_cases hmiddle : x + 10 ≤ n
  · rw [localCheck_middle (m := m) (z := 16) hy (by omega) (by omega) hmiddle (by omega)]
    exact localCheck_finite m 16 y (by omega) hm' (by omega) (by omega) (by omega)
  let z := x + m - n
  have hz : 9 ≤ z := by dsimp [z]; omega
  have he : x + m = z + n := by dsimp [z]; omega
  have hz' : z < 42 := by dsimp [z]; omega
  rw [localCheck_translate (m := m) (z := z) hy (by omega) hz he hr]
  exact localCheck_finite m z y (by omega) hm' hz' (by omega) (by omega)

lemma step_sound (n : ℕ) (hn : 15 ≤ n)
    (ih : ∀ x y, Agrees (pattern n x y) (quad n x y)) :
    ∀ x y, Agrees (pattern (n + 1) x y) (quad (n + 1) x y) := by
  have wedge : ∀ x y, y ≤ x →
      Agrees (pattern (n + 1) x y) (quad (n + 1) x y) := by
    intro x y hyx
    by_cases hout : n + 1 < x + y
    · rw [quad_outside (n + 1) x y hout]
      right
      simp only [pattern, max_eq_left hyx, min_eq_right hyx, if_pos hout,
        decide_eq_true (by omega : 0 < n + 1), Bool.toNat_true]
    by_cases hhigh : 4 < y
    · left
      simp only [pattern, max_eq_left hyx, min_eq_right hyx, if_neg hout,
        if_pos hhigh]
    have hc := localCheck_all n x y hn (by omega) (by omega) hyx
    rw [quad_succ]
    by_cases hy0 : y = 0
    · subst y
      apply compatibleAxis_sound (pattern_lt _ _ _) (pattern_lt _ _ _)
        (pattern_lt _ _ _) (pattern_lt _ _ _)
      · simpa [localCheck] using hc
      all_goals exact ih _ _
    · apply compatible_sound (pattern_lt _ _ _) (pattern_lt _ _ _)
        (pattern_lt _ _ _) (pattern_lt _ _ _) (pattern_lt _ _ _)
      · simpa only [localCheck, if_neg hy0] using hc
      all_goals exact ih _ _

  intro x y
  by_cases h : y ≤ x
  · exact wedge x y h
  · rw [pattern_swap (n + 1) x y, quad_swap (n + 1) x y]
    exact wedge y x (by omega)

end A284350

/- Module A284350Algebra -/

namespace A284350Algebra

open OMA.S_oeis_a284350 PowerSeries

def tipOff (n d : ℕ) : Bool :=
  match n % 8 with
  | 0 => decide (d = 4 ∨ d = 2 ∨ d = 0)
  | 1 => decide (d = 6 ∨ d = 0)
  | 2 => decide (d = 0)
  | 3 => decide (d = 2 ∨ d = 0)
  | 4 => decide (d = 2 ∨ d = 0)
  | 5 => decide (d = 0)
  | 6 => decide (d = 0)
  | _ => decide (d = 2 ∨ d = 0)

def Axis : Prop := ∀ n k : ℕ, 15 ≤ n → k ≤ n →
  cell 873 n k 0 = !tipOff n (n - k)

def initialValues : List ℤ :=
  [1, 0, 6, 10, 10, 46, 46, 250, 490, 958, 1790, 2810, 3066, 12286, 16382]

def Initial : Prop := ∀ n : ℕ, n < 15 → a n = initialValues[n]?.getD 0

def correction (n : ℕ) : ℚ :=
  ∑ d ∈ Finset.range 7, if tipOff n d then (2 : ℚ) ^ d else 0

lemma tipOff_large (n d : ℕ) (hd : 7 ≤ d) : tipOff n d = false := by
  have hn : n % 8 < 8 := Nat.mod_lt n (by decide)
  unfold tipOff
  interval_cases h : n % 8 <;> simp <;> omega

lemma correction_period {n m : ℕ} (h : n % 8 = m % 8) :
    correction n = correction m := by
  simp only [correction, tipOff, h]
  rfl

lemma geom (m : ℕ) :
    (∑ d ∈ Finset.range m, (2 : ℚ) ^ d) = 2 ^ m - 1 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, pow_succ]
    linarith

lemma a_cast (n : ℕ) :
    (a n : ℚ) = ∑ k ∈ Finset.range (n + 1),
      if cell 873 n k 0 then (2 : ℚ) ^ (n - k) else 0 := by
  simp [a]

lemma formula (haxis : Axis) (n : ℕ) (hn : 15 ≤ n) :
    (a n : ℚ) = 2 ^ (n + 1) - 1 - correction n := by
  have htip : (∑ d ∈ Finset.range (n + 1),
      if tipOff n d then (2 : ℚ) ^ d else 0) = correction n := by
    symm
    apply Finset.sum_subset (Finset.range_mono (by omega))
    intro d hd hnot
    have hlarge : 7 ≤ d := by simpa using hnot
    rw [tipOff_large n d hlarge]
    rfl
  rw [a_cast, ← Finset.sum_range_reflect]
  have hsum : (∑ d ∈ Finset.range (n + 1),
      if cell 873 n ((n + 1 - 1 - d : ℕ) : ℤ) 0 then
        (2 : ℚ) ^ (n - (n + 1 - 1 - d)) else 0) =
      ∑ d ∈ Finset.range (n + 1), ((2 : ℚ) ^ d -
        (if tipOff n d then (2 : ℚ) ^ d else 0)) := by
    apply Finset.sum_congr rfl
    intro d hd
    have hdn : d ≤ n := by simpa using hd
    have he : n + 1 - 1 - d = n - d := by omega
    rw [he, haxis n (n - d) hn (by omega)]
    rw [Nat.sub_sub_self hdn]
    cases ht : tipOff n d <;> simp [ht]
  rw [hsum, Finset.sum_sub_distrib, htip, geom]

lemma recurrence (haxis : Axis) (n : ℕ) (hn : 24 ≤ n) :
    (a n : ℚ) = 2 * a (n - 1) + a (n - 8) - 2 * a (n - 9) := by
  have h0 := formula haxis n (by omega)
  have h1 := formula haxis (n - 1) (by omega)
  have h8 := formula haxis (n - 8) (by omega)
  have h9 := formula haxis (n - 9) (by omega)
  rw [correction_period (show (n - 8) % 8 = n % 8 by omega)] at h8
  rw [correction_period (show (n - 9) % 8 = (n - 1) % 8 by omega)] at h9
  have hp0 : (2 : ℚ) ^ (n + 1) = 2 ^ (n - 8) * 2 ^ 9 := by
    rw [← pow_add]; congr 1; omega
  have hp1 : (2 : ℚ) ^ (n - 1 + 1) = 2 ^ (n - 8) * 2 ^ 8 := by
    rw [← pow_add]; congr 1; omega
  have hp8 : (2 : ℚ) ^ (n - 8 + 1) = 2 ^ (n - 8) * 2 := by rw [pow_succ]
  have hp9 : n - 9 + 1 = n - 8 := by omega
  rw [hp0] at h0
  rw [hp1] at h1
  rw [hp8] at h8
  rw [hp9] at h9
  norm_num at h0 h1
  linarith

def value (n : ℕ) : ℚ :=
  if n < 15 then (initialValues[n]?.getD 0 : ℤ)
  else (2 : ℚ) ^ (n + 1) - 1 - correction n

lemma a_value (haxis : Axis) (hi : Initial) (n : ℕ) : (a n : ℚ) = value n := by
  unfold value
  split_ifs with h
  · rw [hi n h]
  · exact formula haxis n (by omega)

lemma coeff_mk_mul_monomial (f : ℕ → ℚ) (c : ℚ) (k n : ℕ) :
    coeff n (mk f * (C c * X ^ k)) = if k ≤ n then f (n - k) * c else 0 := by
  rw [← mul_assoc, coeff_mul_X_pow']
  split_ifs with h
  · rw [coeff_mul_C, coeff_mk]
  · rfl

set_option maxHeartbeats 3000000 in
lemma generating_function (haxis : Axis) (hi : Initial) :
    PowerSeries.mk (fun n => (a n : ℚ)) * (2 * X ^ 9 - X ^ 8 - 2 * X + 1 : PowerSeries ℚ) =
      -32768 * X ^ 23 + 8192 * X ^ 22 - 6144 * X ^ 21 + 2560 * X ^ 20 + 768 * X ^ 19 + 256 * X ^ 18 + 32608 * X ^ 15 - 8144 * X ^ 14 + 6128 * X ^ 13 - 2544 * X ^ 12 - 768 * X ^ 11 - 132 * X ^ 10 - 20 * X ^ 9 - 11 * X ^ 8 + 158 * X ^ 7 - 46 * X ^ 6 + 26 * X ^ 5 - 10 * X ^ 4 - 2 * X ^ 3 + 6 * X ^ 2 - 2 * X + 1 := by
  have hd : (2 * X ^ 9 - X ^ 8 - 2 * X + 1 : PowerSeries ℚ) =
      C 1 * X ^ 0 + C (-2) * X ^ 1 + C (-1) * X ^ 8 + C 2 * X ^ 9 := by
    simp only [map_one, map_neg, map_ofNat]; ring
  have hn : (-32768 * X ^ 23 + 8192 * X ^ 22 - 6144 * X ^ 21 + 2560 * X ^ 20 + 768 * X ^ 19 + 256 * X ^ 18 + 32608 * X ^ 15 - 8144 * X ^ 14 + 6128 * X ^ 13 - 2544 * X ^ 12 - 768 * X ^ 11 - 132 * X ^ 10 - 20 * X ^ 9 - 11 * X ^ 8 + 158 * X ^ 7 - 46 * X ^ 6 + 26 * X ^ 5 - 10 * X ^ 4 - 2 * X ^ 3 + 6 * X ^ 2 - 2 * X + 1 : PowerSeries ℚ) =
      C 1 * X ^ 0 +
      C (-2) * X ^ 1 +
      C 6 * X ^ 2 +
      C (-2) * X ^ 3 +
      C (-10) * X ^ 4 +
      C 26 * X ^ 5 +
      C (-46) * X ^ 6 +
      C 158 * X ^ 7 +
      C (-11) * X ^ 8 +
      C (-20) * X ^ 9 +
      C (-132) * X ^ 10 +
      C (-768) * X ^ 11 +
      C (-2544) * X ^ 12 +
      C 6128 * X ^ 13 +
      C (-8144) * X ^ 14 +
      C 32608 * X ^ 15 +
      C 256 * X ^ 18 +
      C 768 * X ^ 19 +
      C 2560 * X ^ 20 +
      C (-6144) * X ^ 21 +
      C 8192 * X ^ 22 +
      C (-32768) * X ^ 23 := by
    simp only [map_one, map_neg, map_ofNat]; ring
  rw [hd, hn]
  ext n
  simp only [mul_add, map_add, coeff_mk_mul_monomial, coeff_C_mul_X_pow]
  by_cases h : 24 ≤ n
  · have hr := recurrence haxis n h
    simp (disch := omega) only [if_pos, if_neg, Nat.sub_zero]
    linarith
  · simp_rw [a_value haxis hi]
    interval_cases n <;> norm_num [value, initialValues, correction, tipOff, Finset.sum_range_succ]

theorem solution_of_axis (haxis : Axis) (hi : Initial) :
    type_of% @OMA.S_oeis_a284350.main := by
  exact ⟨recurrence haxis, generating_function haxis hi⟩

end A284350Algebra

/- Module A284350Initial -/

namespace A284350Initial

open A284350 OMA.S_oeis_a284350

def rows : List (List ℕ) :=
  [[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [3, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [5, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [10, 13, 6, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [29, 14, 15, 7, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [58, 55, 14, 13, 3, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [95, 63, 31, 15, 7, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [175, 255, 127, 63, 30, 15, 6, 3, 0, 0, 0, 0, 0, 0, 0, 0],
   [503, 175, 255, 126, 61, 31, 13, 7, 1, 0, 0, 0, 0, 0, 0, 0],
   [1019, 1023, 174, 255, 123, 63, 27, 15, 3, 3, 0, 0, 0, 0, 0, 0],
   [1525, 682, 501, 170, 245, 127, 53, 31, 5, 2, 1, 0, 0, 0, 0, 0],
   [3066, 3573, 2042, 1013, 191, 255, 111, 63, 15, 13, 6, 3, 0, 0, 0, 0],
   [8189, 3818, 3581, 1711, 469, 175, 215, 127, 21, 11, 15, 7, 1, 0, 0, 0],
   [16382, 14173, 3007, 4095, 1007, 989, 251, 253, 63, 63, 11, 13, 3, 3, 0, 0],
   [24575, 16107, 7677, 4015, 1525, 703, 343, 191, 93, 43, 31, 15, 7, 2, 1, 0]]

def grid (n x y : ℕ) : Bool :=
  if x + y ≤ n then ((rows[n]?.getD [])[y]?.getD 0).testBit x else decide (0 < n)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 6000000 in
lemma grid_step : ∀ n : Fin 15, ∀ x y : Fin 16,
    grid (n + 1) x y =
      rule (grid n x y) (grid n (x + 1) y) (grid n (prevN x) y)
        (grid n x (y + 1)) (grid n x (prevN y)) := by
  decide +kernel

lemma quad_eq_grid (n : ℕ) (hn : n ≤ 15) (x y : ℕ) :
    quad n x y = grid n x y := by
  induction n generalizing x y with
  | zero =>
    by_cases h : x + y ≤ 0
    · have hx : x = 0 := by omega
      have hy : y = 0 := by omega
      subst x; subst y
      rfl
    · rw [quad_outside 0 x y (by omega)]
      simp [grid, h]
  | succ n ih =>
    by_cases h : x + y ≤ n + 1
    · have hx : x < 16 := by omega
      have hy : y < 16 := by omega
      rw [quad_succ]
      simp only [ih (by omega)]
      exact (grid_step ⟨n, by omega⟩ ⟨x, hx⟩ ⟨y, hy⟩).symm
    · rw [quad_outside (n + 1) x y (by omega)]
      simp [grid, h]

theorem cell_eq_grid (n x y : ℕ) (hn : n ≤ 15) (hx : x ≤ 15) (hy : y ≤ 15) :
    cell 873 n x y = grid n x y := quad_eq_grid n hn x y

lemma a_grid (n : ℕ) (hn : n ≤ 15) :
    a n = ∑ k ∈ Finset.range (n + 1),
      if grid n k 0 then (2 : ℤ) ^ (n - k) else 0 := by
  unfold a
  apply Finset.sum_congr rfl
  intro k hk
  rw [show cell 873 n k 0 = grid n k 0 from quad_eq_grid n hn k 0]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
lemma initial : A284350Algebra.Initial := by
  intro n hn
  rw [a_grid n (by omega)]
  interval_cases n <;> decide +kernel

end A284350Initial

/- Module A284350Invariant -/

namespace A284350

set_option maxRecDepth 10000 in
def initial_pattern : ∀ x y : Fin 16,
    Agrees (pattern 15 x y) (A284350Initial.grid 15 x y) := by
  decide

lemma base_sound (x y : ℕ) : Agrees (pattern 15 x y) (quad 15 x y) := by
  rw [A284350Initial.quad_eq_grid 15 (by omega)]
  by_cases h : x + y ≤ 15
  · exact initial_pattern ⟨x, by omega⟩ ⟨y, by omega⟩
  · right
    have he : max x y + min x y = x + y := max_add_min x y
    simp only [pattern, if_pos (show 15 < max x y + min x y by omega),
      A284350Initial.grid, if_neg h, decide_eq_true (by decide : 0 < 15), Bool.toNat_true]

theorem pattern_sound (n : ℕ) (hn : 15 ≤ n) :
    ∀ x y, Agrees (pattern n x y) (quad n x y) := by
  induction n, hn using Nat.le_induction with
  | base => exact base_sound
  | succ n hn ih => exact step_sound n hn ih

end A284350

/- Module A284350Axis -/

namespace A284350

open A284350Algebra

set_option maxRecDepth 10000 in
def axis_table : ∀ p : Fin 8, ∀ d : Fin 9,
    tip p d 0 = (!tipOff p d).toNat := by
  decide

lemma pattern_axis (n k : ℕ) (hn : 15 ≤ n) (hk : k ≤ n) :
    pattern n k 0 = (!tipOff n (n - k)).toNat := by
  have hcone : ¬ n < k + 0 := by omega
  simp only [pattern, max_eq_left (Nat.zero_le k), min_eq_right (Nat.zero_le k),
    if_neg hcone, show ¬ 4 < 0 by omega, if_false, if_pos rfl]
  by_cases hinterior : k + 8 < n
  · rw [if_pos hinterior, tipOff_large n (n - k) (by omega)]
    rfl
  · rw [if_neg hinterior]
    have h := axis_table ⟨n % 8, Nat.mod_lt _ (by decide)⟩ ⟨n - k, by omega⟩
    simpa only [tipOff, Nat.mod_mod] using h

lemma axis_of_sound
    (hs : ∀ n : ℕ, 15 ≤ n → ∀ x y, Agrees (pattern n x y) (quad n x y)) : Axis := by
  intro n k hn hk
  have h := hs n hn k 0
  rw [pattern_axis n k hn hk] at h
  change Agrees _ (OMA.S_oeis_a284350.cell 873 n k 0) at h
  cases hc : OMA.S_oeis_a284350.cell 873 n k 0 <;>
    cases hv : !tipOff n (n - k) <;> simp_all [Agrees]

end A284350

/- Module A284350Finish -/

theorem OMA.solution : type_of% @OMA.S_oeis_a284350.main :=
  A284350Algebra.solution_of_axis
    (A284350.axis_of_sound A284350.pattern_sound)
    A284350Initial.initial

