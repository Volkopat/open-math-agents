import OMAStatements.S_oeis_a284545
import Mathlib.Data.List.FinRange
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

-- Credit: @CubeJerry. Agent: ChatGPT. Model: gpt-6-astra.
-- New finite partial-plane invariant for Rule998, followed by the exact axis readout.
-- Source: https://oeis.org/A284545. No previously completed Rule998 proof is used.

/- Module A284545Core -/

namespace A284545

open OMA.S_oeis_a284545

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

def quad (n x y : ℕ) : Bool := cell 998 n x y

def rule (c e w u d : Bool) : Bool :=
  (998 : ℕ).testBit (c.toNat + 2 * (e.toNat + w.toNat + u.toNat + d.toNat))

lemma quad_swap (n x y : ℕ) : quad n x y = quad n y x := cell_swap 998 n x y

lemma left_prev (n x y : ℕ) : cell 998 n ((x : ℤ) - 1) y = quad n (prevN x) y := by
  by_cases h : x = 0
  · subst x
    simpa [prevN, quad] using cell_neg_left 998 n 1 y
  · congr 2
    simp only [prevN, h, if_false]
    omega

lemma down_prev (n x y : ℕ) : cell 998 n x ((y : ℤ) - 1) = quad n x (prevN y) := by
  rw [cell_swap, left_prev, quad_swap]

lemma quad_succ (n x y : ℕ) : quad (n + 1) x y =
    rule (quad n x y) (quad n (x + 1) y) (quad n (prevN x) y)
      (quad n x (y + 1)) (quad n x (prevN y)) := by
  simp only [quad, cell, rule, Nat.cast_add, Nat.cast_one, left_prev, down_prev]

lemma quad_outside (n x y : ℕ) (h : n < x + y) : quad n x y = false := by
  induction n generalizing x y with
  | zero => simp [quad, cell]; omega
  | succ n ih =>
    have hx : n < prevN x + y := by unfold prevN; split <;> omega
    have hy : n < x + prevN y := by unfold prevN; split <;> omega
    rw [quad_succ, ih x y (by omega), ih (x + 1) y (by omega),
      ih (prevN x) y hx, ih x (y + 1) (by omega), ih x (prevN y) hy]
    rfl

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
  if (if c = 0 then (lo = 1 ∧ hi = 1) ∨ 3 ≤ lo
      else if c = 1 then hi = 0 ∨ 2 ≤ lo else 3 ≤ lo) then 1
  else if (if c = 0 then hi = 0 ∨ (lo = 2 ∧ hi = 2)
      else if c = 1 then lo = 1 ∧ hi = 1 else False) then 0
  else 2

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

end A284545
/- Module A284545Data -/

namespace A284545

/-- Two-bit encodings of the finite tip template, with two denoting an unspecified cell. -/
def tipRow : ℕ → ℕ → ℕ
  | 0, 0 => 5725557009
  | 0, 1 => 5726601216
  | 0, 2 => 5726617856
  | 0, 3 => 5726606336
  | 0, 4 => 5726605312
  | 0, 5 => 11453153280
  | 0, 6 => 11453202432
  | 1, 0 => 5726553157
  | 1, 1 => 5726552132
  | 1, 2 => 5726536960
  | 1, 3 => 5726617600
  | 1, 4 => 5726601216
  | 1, 5 => 11452809216
  | 1, 6 => 11453202432
  | 2, 0 => 5726343441
  | 2, 1 => 5726289920
  | 2, 2 => 5726289936
  | 2, 3 => 5726557184
  | 2, 4 => 5726535680
  | 2, 5 => 11453071360
  | 2, 6 => 11453202432
  | 3, 0 => 5725570117
  | 3, 1 => 5726274564
  | 3, 2 => 5725557072
  | 3, 3 => 5726356544
  | 3, 4 => 5726621696
  | 3, 5 => 11453071360
  | 3, 6 => 11453202432
  | 4, 0 => 5725491473
  | 4, 1 => 5722144768
  | 4, 2 => 5725573376
  | 4, 3 => 5726622720
  | 4, 4 => 5726601472
  | 4, 5 => 11453153280
  | 4, 6 => 11453202432
  | 5, 0 => 5709841477
  | 5, 1 => 5726273604
  | 5, 2 => 5726622976
  | 5, 3 => 5726618624
  | 5, 4 => 5726618880
  | 5, 5 => 11452826624
  | 5, 6 => 11453202432
  | 6, 0 => 5726540049
  | 6, 1 => 5726289920
  | 6, 2 => 5726621712
  | 6, 3 => 5726622720
  | 6, 4 => 5726605568
  | 6, 5 => 11452809216
  | 6, 6 => 11453206528
  | 7, 0 => 5725570117
  | 7, 1 => 5726290948
  | 7, 2 => 5726617936
  | 7, 3 => 5726617664
  | 7, 4 => 5726606592
  | 7, 5 => 11453072384
  | 7, 6 => 11453222912
  | _, _ => 0

def tip (p d y : ℕ) : ℕ := tipRow p y / 4 ^ d % 4

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def tip_lt_three : ∀ p : Fin 8, ∀ d : Fin 17, ∀ y : Fin 7, tip p d y < 3 := by
  decide

end A284545
/- Module A284545Template -/

namespace A284545

def pattern (n x y : ℕ) : ℕ :=
  let a := max x y
  let b := min x y
  if n < a + b then 0
  else if a ≤ 1 then if a = 0 then 1 else 0
  else if 6 < b then 2
  else if a + 16 < n then if b ≤ 1 then 1 else 2
  else tip (n % 8) (n - a) b

lemma pattern_swap (n x y : ℕ) : pattern n x y = pattern n y x := by
  simp only [pattern, max_comm x y, min_comm x y]

lemma pattern_lt (n x y : ℕ) : pattern n x y < 3 := by
  unfold pattern
  dsimp
  split_ifs with h1 h2 h3 h4 h5 h6
  all_goals try omega
  exact tip_lt_three ⟨n % 8, Nat.mod_lt _ (by decide)⟩
    ⟨n - max x y, by omega⟩ ⟨min x y, by omega⟩

lemma pattern_small {n m x y : ℕ} (hn : 32 ≤ n) (hm : 32 ≤ m)
    (hx : x ≤ 9) (hy : y ≤ 7) : pattern n x y = pattern m x y := by
  have ha : max x y ≤ 9 := by omega
  have hb : min x y ≤ 7 := by omega
  simp only [pattern, if_neg (show ¬ n < max x y + min x y by omega),
    if_neg (show ¬ m < max x y + min x y by omega),
    if_pos (show max x y + 16 < n by omega),
    if_pos (show max x y + 16 < m by omega)]

lemma pattern_translate {n m x z y : ℕ} (hy : y ≤ 7)
    (hx : 8 ≤ x) (hz : 8 ≤ z) (he : x + m = z + n) (hr : n % 8 = m % 8) :
    pattern n x y = pattern m z y := by
  have hxy : y ≤ x := by omega
  have hzy : y ≤ z := by omega
  have hcone : n < x + y ↔ m < z + y := by omega
  have hinterior : x + 16 < n ↔ z + 16 < m := by omega
  have hdepth : n - x = m - z := by omega
  simp only [pattern, max_eq_left hxy, min_eq_right hxy,
    max_eq_left hzy, min_eq_right hzy,
    if_neg (show ¬ x ≤ 1 by omega), if_neg (show ¬ z ≤ 1 by omega),
    hcone, hinterior, hdepth, hr]

lemma pattern_middle {n m x z y : ℕ} (hy : y ≤ 7)
    (hx : 8 ≤ x) (hz : 8 ≤ z) (hn : x + 16 < n) (hm : z + 16 < m) :
    pattern n x y = pattern m z y := by
  have hxy : y ≤ x := by omega
  have hzy : y ≤ z := by omega
  simp only [pattern, max_eq_left hxy, min_eq_right hxy,
    max_eq_left hzy, min_eq_right hzy,
    if_neg (show ¬ n < x + y by omega), if_neg (show ¬ m < z + y by omega),
    if_neg (show ¬ x ≤ 1 by omega), if_neg (show ¬ z ≤ 1 by omega),
    if_pos hn, if_pos hm]

def localCheck (n x y : ℕ) : Bool :=
  compatible (pattern (n + 1) x y) (pattern n x y)
    (pattern n (x + 1) y) (pattern n (prevN x) y)
    (pattern n x (y + 1)) (pattern n x (prevN y))

end A284545
/- Module A284545Local -/

namespace A284545

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
def local_certificate :
    ((List.range 39).all fun t =>
      (List.range 58).all fun x =>
        (List.range 8).all fun y => localCheck (t + 17) x y) = true := by
  decide

lemma localCheck_finite (n x y : ℕ) (hn : 17 ≤ n) (hn' : n < 56)
    (hx : x < 58) (hy : y < 8) : localCheck n x y = true := by
  have h := (List.all_eq_true.mp local_certificate) (n - 17) (by simp; omega)
  have h := (List.all_eq_true.mp h) x (by simpa)
  have h := (List.all_eq_true.mp h) y (by simpa)
  simpa only [Nat.sub_add_cancel hn] using h

lemma prevN_le (x : ℕ) : prevN x ≤ x + 1 := by
  unfold prevN
  split <;> omega

lemma localCheck_small {n m x y : ℕ} (hn : 32 ≤ n) (hm : 32 ≤ m)
    (hx : x ≤ 8) (hy : y ≤ 6) : localCheck n x y = localCheck m x y := by
  have hpx : prevN x ≤ 9 := by have := prevN_le x; omega
  have hpy : prevN y ≤ 7 := by have := prevN_le y; omega
  unfold localCheck
  rw [pattern_small (n := n + 1) (m := m + 1) (by omega) (by omega) (by omega) (by omega),
    pattern_small hn hm (by omega) (by omega),
    pattern_small hn hm (show x + 1 ≤ 9 by omega) (by omega),
    pattern_small hn hm hpx (by omega),
    pattern_small hn hm (show x ≤ 9 by omega) (show y + 1 ≤ 7 by omega),
    pattern_small hn hm (show x ≤ 9 by omega) hpy]

lemma localCheck_middle {n m x z y : ℕ} (hy : y ≤ 6)
    (hx : 9 ≤ x) (hz : 9 ≤ z) (hn : x + 18 ≤ n) (hm : z + 18 ≤ m) :
    localCheck n x y = localCheck m z y := by
  have hpx : prevN x = x - 1 := if_neg (by omega)
  have hpz : prevN z = z - 1 := if_neg (by omega)
  have hpy : prevN y ≤ 7 := by have := prevN_le y; omega
  unfold localCheck
  rw [hpx, hpz]
  congr 1 <;> apply pattern_middle <;> omega

lemma localCheck_translate {n m x z y : ℕ} (hy : y ≤ 6)
    (hx : 9 ≤ x) (hz : 9 ≤ z) (he : x + m = z + n) (hr : n % 8 = m % 8) :
    localCheck n x y = localCheck m z y := by
  have hpx : prevN x = x - 1 := if_neg (by omega)
  have hpz : prevN z = z - 1 := if_neg (by omega)
  have hpy : prevN y ≤ 7 := by have := prevN_le y; omega
  unfold localCheck
  rw [hpx, hpz]
  congr 1 <;> apply pattern_translate <;> omega

lemma localCheck_all (n x y : ℕ) (hn : 17 ≤ n) (hx : x ≤ n + 1) (hy : y ≤ 6) :
    localCheck n x y = true := by
  by_cases hsmall : n < 48
  · exact localCheck_finite n x y hn (by omega) (by omega) (by omega)
  let m := 48 + n % 8
  have hm : 48 ≤ m := by dsimp [m]; omega
  have hm' : m < 56 := by dsimp [m]; omega
  have hr : n % 8 = m % 8 := by dsimp [m]; omega
  by_cases hleft : x ≤ 8
  · rw [localCheck_small (m := m) (by omega) (by omega) hleft hy]
    exact localCheck_finite m x y (by omega) hm' (by omega) (by omega)
  by_cases hmiddle : x + 18 ≤ n
  · rw [localCheck_middle (m := m) (z := 16) hy (by omega) (by omega) hmiddle (by omega)]
    exact localCheck_finite m 16 y (by omega) hm' (by omega) (by omega)
  let z := x + m - n
  have hz : 9 ≤ z := by dsimp [z]; omega
  have he : x + m = z + n := by dsimp [z]; omega
  have hz' : z < 58 := by dsimp [z]; omega
  rw [localCheck_translate (m := m) (z := z) hy (by omega) hz he hr]
  exact localCheck_finite m z y (by omega) hm' hz' (by omega)

lemma step_sound (n : ℕ) (hn : 17 ≤ n)
    (ih : ∀ x y, Agrees (pattern n x y) (quad n x y)) :
    ∀ x y, Agrees (pattern (n + 1) x y) (quad (n + 1) x y) := by
  have wedge : ∀ x y, y ≤ x →
      Agrees (pattern (n + 1) x y) (quad (n + 1) x y) := by
    intro x y hyx
    by_cases hout : n + 1 < x + y
    · rw [quad_outside (n + 1) x y hout]
      right
      simp only [pattern, max_eq_left hyx, min_eq_right hyx, if_pos hout, Bool.toNat_false]
    by_cases hhigh : 6 < y
    · left
      simp only [pattern, max_eq_left hyx, min_eq_right hyx, if_neg hout,
        if_neg (show ¬ x ≤ 1 by omega), if_pos hhigh]
    have hc := localCheck_all n x y hn (by omega) (by omega)
    rw [quad_succ]
    exact compatible_sound (pattern_lt _ _ _) (pattern_lt _ _ _)
      (pattern_lt _ _ _) (pattern_lt _ _ _) (pattern_lt _ _ _) hc
      (ih _ _) (ih _ _) (ih _ _) (ih _ _) (ih _ _)
  intro x y
  by_cases h : y ≤ x
  · exact wedge x y h
  · rw [pattern_swap (n + 1) x y, quad_swap (n + 1) x y]
    exact wedge y x (by omega)

end A284545
/- Module A284545Algebra -/

namespace A284545Algebra

open OMA.S_oeis_a284545 PowerSeries

def tipOff (n d : ℕ) : Bool :=
  match n % 8 with
  | 0 => decide (d = 10 ∨ d = 7 ∨ d = 5 ∨ d = 3 ∨ d = 1)
  | 1 => decide (d = 8 ∨ d = 6 ∨ d = 4 ∨ d = 2)
  | 2 => decide (d = 9 ∨ d = 7 ∨ d = 5 ∨ d = 3 ∨ d = 1)
  | 3 => decide (d = 10 ∨ d = 6 ∨ d = 4 ∨ d = 2)
  | 4 => decide (d = 10 ∨ d = 8 ∨ d = 7 ∨ d = 5 ∨ d = 3 ∨ d = 1)
  | 5 => decide (d = 12 ∨ d = 6 ∨ d = 4 ∨ d = 2)
  | 6 => decide (d = 8 ∨ d = 7 ∨ d = 5 ∨ d = 3 ∨ d = 1)
  | _ => decide (d = 10 ∨ d = 6 ∨ d = 4 ∨ d = 2)

def Axis : Prop := ∀ n k : ℕ, 17 ≤ n → k ≤ n →
  cell 998 n k 0 = !(decide (k = 1) || tipOff n (n - k))

def initialValues : List ℤ :=
  [1, 11, 101, 1011, 10101, 101011, 1010101, 10101011, 101010101,
    1010101011, 10101010101, 101110101011, 1011101010101, 10110010101011,
    101111101010101, 1011110110101011, 10111110101010101]

def Initial : Prop := ∀ n : ℕ, n < 17 → a n = initialValues[n]?.getD 0

def correction (n : ℕ) : ℚ :=
  ∑ d ∈ Finset.range 13, if tipOff n d then (10 : ℚ) ^ d else 0

lemma tipOff_large (n d : ℕ) (hd : 13 ≤ d) : tipOff n d = false := by
  have hn : n % 8 < 8 := Nat.mod_lt n (by decide)
  unfold tipOff
  interval_cases h : n % 8 <;> simp <;> omega

lemma correction_period {n m : ℕ} (h : n % 8 = m % 8) :
    correction n = correction m := by
  simp only [correction, tipOff, h]
  rfl

lemma geom_scaled (m : ℕ) :
    9 * (∑ d ∈ Finset.range m, (10 : ℚ) ^ d) = 10 ^ m - 1 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, pow_succ]
    linarith

lemma a_cast (n : ℕ) :
    (a n : ℚ) = ∑ k ∈ Finset.range (n + 1),
      if cell 998 n k 0 then (10 : ℚ) ^ (n - k) else 0 := by
  simp [a]

lemma a_from_axis (haxis : Axis) (n : ℕ) (hn : 17 ≤ n) :
    (a n : ℚ) = (∑ d ∈ Finset.range (n + 1), (10 : ℚ) ^ d) -
      10 ^ (n - 1) - correction n := by
  have htip : (∑ d ∈ Finset.range (n + 1),
      if tipOff n d then (10 : ℚ) ^ d else 0) = correction n := by
    symm
    apply Finset.sum_subset (Finset.range_mono (by omega))
    intro d hd hnot
    have hlarge : 13 ≤ d := by simpa using hnot
    rw [tipOff_large n d hlarge]
    rfl
  rw [a_cast, ← Finset.sum_range_reflect]
  have hsum : (∑ d ∈ Finset.range (n + 1),
      if cell 998 n ((n + 1 - 1 - d : ℕ) : ℤ) 0 then
        (10 : ℚ) ^ (n - (n + 1 - 1 - d)) else 0) =
      ∑ d ∈ Finset.range (n + 1), ((10 : ℚ) ^ d -
        (if d = n - 1 then (10 : ℚ) ^ d else 0) -
        (if tipOff n d then (10 : ℚ) ^ d else 0)) := by
    apply Finset.sum_congr rfl
    intro d hd
    have hdn : d ≤ n := by simpa using hd
    have he : n + 1 - 1 - d = n - d := by omega
    rw [he, haxis n (n - d) hn (by omega)]
    rw [Nat.sub_sub_self hdn]
    have hi : n - d = 1 ↔ d = n - 1 := by omega
    simp only [hi]
    by_cases hd1 : d = n - 1
    · have hlarge : 13 ≤ d := by omega
      rw [tipOff_large n d hlarge]
      simp [hd1]
    · cases ht : tipOff n d <;> simp [hd1, ht]
  rw [hsum, Finset.sum_sub_distrib, Finset.sum_sub_distrib, htip]
  simp [Finset.mem_range, show n - 1 < n + 1 by omega]

lemma scaled_formula (haxis : Axis) (n : ℕ) (hn : 17 ≤ n) :
    9 * (a n : ℚ) = 91 * (10 : ℚ) ^ (n - 1) - 1 - 9 * correction n := by
  rw [a_from_axis haxis n hn]
  have h := geom_scaled (n + 1)
  have hp : (10 : ℚ) ^ (n + 1) = 100 * 10 ^ (n - 1) := by
    rw [show n + 1 = (n - 1) + 2 by omega, pow_add]
    ring
  rw [hp] at h
  linarith

lemma recurrence (haxis : Axis) (n : ℕ) (hn : 26 ≤ n) :
    (a n : ℚ) = 10 * a (n - 1) + a (n - 8) - 10 * a (n - 9) := by
  have h0 := scaled_formula haxis n (by omega)
  have h1 := scaled_formula haxis (n - 1) (by omega)
  have h8 := scaled_formula haxis (n - 8) (by omega)
  have h9 := scaled_formula haxis (n - 9) (by omega)
  rw [correction_period (show (n - 8) % 8 = n % 8 by omega)] at h8
  rw [correction_period (show (n - 9) % 8 = (n - 1) % 8 by omega)] at h9
  have hp0 : (10 : ℚ) ^ (n - 1) = 10 ^ (n - 10) * 10 ^ 9 := by
    rw [← pow_add]; congr 1; omega
  have hp1 : (10 : ℚ) ^ (n - 1 - 1) = 10 ^ (n - 10) * 10 ^ 8 := by
    rw [← pow_add]; congr 1; omega
  have hp8 : (10 : ℚ) ^ (n - 8 - 1) = 10 ^ (n - 10) * 10 := by
    rw [← pow_succ]; congr 1; omega
  have hp9 : n - 9 - 1 = n - 10 := by omega
  rw [hp0] at h0
  rw [hp1] at h1
  rw [hp8] at h8
  rw [hp9] at h9
  norm_num at h0 h1
  linarith

def value (n : ℕ) : ℚ :=
  if n < 17 then (initialValues[n]?.getD 0 : ℤ)
  else (91 * (10 : ℚ) ^ (n - 1) - 1 - 9 * correction n) / 9

lemma a_value (haxis : Axis) (hi : Initial) (n : ℕ) : (a n : ℚ) = value n := by
  unfold value
  split_ifs with h
  · rw [hi n h]
  · have hs := scaled_formula haxis n (by omega)
    linarith

lemma coeff_mk_mul_monomial (f : ℕ → ℚ) (c : ℚ) (k n : ℕ) :
    coeff n (mk f * (C c * X ^ k)) = if k ≤ n then f (n - k) * c else 0 := by
  rw [← mul_assoc, coeff_mul_X_pow']
  split_ifs with h
  · rw [coeff_mul_C, coeff_mk]
  · rfl

set_option maxHeartbeats 3000000 in
lemma generating_function (haxis : Axis) (hi : Initial) :
    PowerSeries.mk (fun n => (a n : ℚ)) * (10 * X ^ 9 - X ^ 8 - 10 * X + 1 : PowerSeries ℚ) =
      90000000000 * X ^ 25 + 81000000000 * X ^ 24 - 8000000000 * X ^ 23 +
      9988900000000 * X ^ 22 - 897900000000 * X ^ 21 + 89900000000 * X ^ 20 +
      10000000000 * X ^ 17 + 9000000000 * X ^ 16 - 900000000 * X ^ 15 +
      11000000000 * X ^ 14 - 1000000000 * X ^ 13 + 100000000 * X ^ 11 -
      10 * X ^ 8 + X ^ 7 - 9 * X ^ 6 + X ^ 5 - 9 * X ^ 4 + X ^ 3 -
      9 * X ^ 2 + X + 1 := by
  have hd : (10 * X ^ 9 - X ^ 8 - 10 * X + 1 : PowerSeries ℚ) =
      C 1 * X ^ 0 + C (-10) * X ^ 1 + C (-1) * X ^ 8 + C 10 * X ^ 9 := by
    simp only [map_one, map_neg, map_ofNat]; ring
  have hn : (90000000000 * X ^ 25 + 81000000000 * X ^ 24 - 8000000000 * X ^ 23 +
      9988900000000 * X ^ 22 - 897900000000 * X ^ 21 + 89900000000 * X ^ 20 +
      10000000000 * X ^ 17 + 9000000000 * X ^ 16 - 900000000 * X ^ 15 +
      11000000000 * X ^ 14 - 1000000000 * X ^ 13 + 100000000 * X ^ 11 -
      10 * X ^ 8 + X ^ 7 - 9 * X ^ 6 + X ^ 5 - 9 * X ^ 4 + X ^ 3 -
      9 * X ^ 2 + X + 1 : PowerSeries ℚ) =
      C 1 * X ^ 0 + C 1 * X ^ 1 + C (-9) * X ^ 2 + C 1 * X ^ 3 +
      C (-9) * X ^ 4 + C 1 * X ^ 5 + C (-9) * X ^ 6 + C 1 * X ^ 7 +
      C (-10) * X ^ 8 + C 100000000 * X ^ 11 + C (-1000000000) * X ^ 13 +
      C 11000000000 * X ^ 14 + C (-900000000) * X ^ 15 + C 9000000000 * X ^ 16 +
      C 10000000000 * X ^ 17 + C 89900000000 * X ^ 20 + C (-897900000000) * X ^ 21 +
      C 9988900000000 * X ^ 22 + C (-8000000000) * X ^ 23 + C 81000000000 * X ^ 24 +
      C 90000000000 * X ^ 25 := by
    simp only [map_one, map_neg, map_ofNat]; ring
  rw [hd, hn]
  ext n
  simp only [mul_add, map_add, coeff_mk_mul_monomial, coeff_C_mul_X_pow]
  by_cases h : 26 ≤ n
  · have hr := recurrence haxis n h
    simp (disch := omega) only [if_pos, if_neg, Nat.sub_zero]
    linarith
  · simp_rw [a_value haxis hi]
    interval_cases n <;> norm_num [value, initialValues, correction, tipOff, Finset.sum_range_succ]

theorem solution_of_axis (haxis : Axis) (hi : Initial) :
    type_of% @OMA.S_oeis_a284545.main := by
  exact ⟨recurrence haxis, generating_function haxis hi⟩

end A284545Algebra
/- Module A284545Initial -/

namespace A284545Initial

open A284545 OMA.S_oeis_a284545

def rows : List (List ℕ) :=
  [[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [5, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [13, 4, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [21, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [53, 20, 3, 0, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [85, 0, 17, 0, 5, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [213, 68, 59, 20, 13, 4, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [341, 0, 21, 8, 5, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [853, 320, 61, 12, 5, 4, 3, 0, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0],
   [1365, 8, 285, 46, 5, 8, 1, 0, 5, 0, 1, 0, 0, 0, 0, 0, 0, 0],
   [3421, 1108, 911, 381, 43, 24, 11, 4, 13, 4, 3, 1, 0, 0, 0, 0, 0, 0],
   [5469, 12, 383, 191, 285, 12, 5, 8, 21, 0, 1, 0, 1, 0, 0, 0, 0, 0],
   [13645, 5180, 959, 511, 798, 270, 9, 12, 61, 20, 3, 0, 3, 1, 0, 0, 0, 0],
   [21885, 188, 4607, 1023, 1375, 143, 285, 46, 93, 8, 17, 0, 5, 0, 1, 0, 0, 0],
   [54717, 17788, 14847, 4607, 3775, 1439, 782, 317, 239, 80, 51, 20, 13, 4, 3, 1, 0, 0],
   [87421, 508, 5119, 3583, 1535, 991, 319, 62, 127, 36, 25, 8, 5, 0, 1, 0, 1, 0],
   [218621, 83452, 12799, 2047, 1023, 511, 63, 319, 191, 24, 11, 0, 5, 4, 3, 0, 3, 1]]

def grid (n x y : ℕ) : Bool :=
  if x + y ≤ n then ((rows[n]?.getD [])[y]?.getD 0).testBit x else false

set_option maxRecDepth 20000 in
set_option maxHeartbeats 6000000 in
lemma grid_step : ∀ n : Fin 17, ∀ x y : Fin 18,
    grid (n + 1) x y =
      rule (grid n x y) (grid n (x + 1) y) (grid n (prevN x) y)
        (grid n x (y + 1)) (grid n x (prevN y)) := by
  decide +kernel

lemma quad_eq_grid (n : ℕ) (hn : n ≤ 17) (x y : ℕ) :
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
    · have hx : x < 18 := by omega
      have hy : y < 18 := by omega
      rw [quad_succ]
      simp only [ih (by omega)]
      exact (grid_step ⟨n, by omega⟩ ⟨x, hx⟩ ⟨y, hy⟩).symm
    · rw [quad_outside (n + 1) x y (by omega)]
      simp [grid, h]

theorem cell_eq_grid (n x y : ℕ) (hn : n ≤ 17) (hx : x ≤ 17) (hy : y ≤ 17) :
    cell 998 n x y = grid n x y := quad_eq_grid n hn x y

lemma a_grid (n : ℕ) (hn : n ≤ 17) :
    a n = ∑ k ∈ Finset.range (n + 1),
      if grid n k 0 then (10 : ℤ) ^ (n - k) else 0 := by
  unfold a
  apply Finset.sum_congr rfl
  intro k hk
  rw [show cell 998 n k 0 = grid n k 0 from quad_eq_grid n hn k 0]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
lemma initial : A284545Algebra.Initial := by
  intro n hn
  rw [a_grid n (by omega)]
  interval_cases n <;> decide +kernel

end A284545Initial
/- Module A284545Invariant -/

namespace A284545

set_option maxRecDepth 10000 in
def initial_pattern : ∀ x y : Fin 18,
    Agrees (pattern 17 x y) (A284545Initial.grid 17 x y) := by
  decide

lemma base_sound (x y : ℕ) : Agrees (pattern 17 x y) (quad 17 x y) := by
  rw [A284545Initial.quad_eq_grid 17 (by omega)]
  by_cases h : x + y ≤ 17
  · exact initial_pattern ⟨x, by omega⟩ ⟨y, by omega⟩
  · right
    have he : max x y + min x y = x + y := max_add_min x y
    simp only [pattern, if_pos (show 17 < max x y + min x y by omega),
      A284545Initial.grid, if_neg h, Bool.toNat_false]

theorem pattern_sound (n : ℕ) (hn : 17 ≤ n) :
    ∀ x y, Agrees (pattern n x y) (quad n x y) := by
  induction n, hn using Nat.le_induction with
  | base => exact base_sound
  | succ n hn ih => exact step_sound n hn ih

end A284545
/- Module A284545Axis -/

namespace A284545

open A284545Algebra

set_option maxRecDepth 10000 in
def axis_table : ∀ p : Fin 8, ∀ d : Fin 17,
    tip p d 0 = (!tipOff p d).toNat := by
  decide

lemma pattern_axis (n k : ℕ) (hn : 17 ≤ n) (hk : k ≤ n) :
    pattern n k 0 = (!(decide (k = 1) || tipOff n (n - k))).toNat := by
  by_cases hsmall : k ≤ 1
  · have hl : 13 ≤ n - k := by omega
    rw [tipOff_large n (n - k) hl]
    interval_cases k <;> simp [pattern, show ¬ n < 1 by omega]
  have hcone : ¬ n < k + 0 := by omega
  have hk1 : k ≠ 1 := by omega
  simp only [pattern, max_eq_left (Nat.zero_le k), min_eq_right (Nat.zero_le k),
    if_neg hcone, if_neg hsmall, show ¬ 6 < 0 by omega, if_false, zero_le,
    if_true, hk1, decide_false, Bool.false_or]
  by_cases hinterior : k + 16 < n
  · rw [if_pos hinterior, tipOff_large n (n - k) (by omega)]
    rfl
  · rw [if_neg hinterior]
    have h := axis_table ⟨n % 8, Nat.mod_lt _ (by decide)⟩
      ⟨n - k, by omega⟩
    simpa only [tipOff, Nat.mod_mod] using h

lemma axis_of_sound
    (hs : ∀ n : ℕ, 17 ≤ n → ∀ x y, Agrees (pattern n x y) (quad n x y)) : Axis := by
  intro n k hn hk
  have h := hs n hn k 0
  rw [pattern_axis n k hn hk] at h
  change Agrees _ (OMA.S_oeis_a284545.cell 998 n k 0) at h
  cases hc : OMA.S_oeis_a284545.cell 998 n k 0 <;>
    cases hv : !(decide (k = 1) || tipOff n (n - k)) <;>
    simp_all [Agrees]

end A284545
/- Module A284545Finish -/

theorem OMA.solution : type_of% @OMA.S_oeis_a284545.main :=
  A284545Algebra.solution_of_axis (A284545.axis_of_sound A284545.pattern_sound)
    A284545Initial.initial
