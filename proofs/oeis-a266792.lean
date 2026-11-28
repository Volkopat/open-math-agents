import OMAStatements.S_oeis_a266792
import Mathlib

namespace A266792Aux

def st (b : Bool) (L : List ℤ) : ℤ → Bool := fun x => xor b (decide (x ∈ L))

open OMA.S_oeis_a266792 in
def stp (rule : ℕ) (g : ℤ → Bool) : ℤ → Bool := fun i =>
  ruleOut rule (g (i - 1)) (g i) (g (i + 1))

def inBox (lo hi : ℤ) (L : List ℤ) : Prop := ∀ p ∈ L, lo ≤ p ∧ p ≤ hi

def rng (lo hi : ℤ) : List ℤ :=
  (List.range (hi - lo + 3).toNat).map (fun k : ℕ => (k : ℤ) + (lo - 1))

lemma mem_rng (lo hi x : ℤ) (h1 : lo - 1 ≤ x) (h2 : x ≤ hi + 1) : x ∈ rng lo hi := by
  unfold rng
  rw [List.mem_map]
  refine ⟨(x - (lo - 1)).toNat, ?_, ?_⟩
  · rw [List.mem_range]
    omega
  · have h : (((x - (lo - 1)).toNat : ℕ) : ℤ) = x - (lo - 1) := Int.toNat_of_nonneg (by omega)
    omega

lemma st_far (b : Bool) (lo hi : ℤ) (L : List ℤ) (hL : inBox lo hi L) (u : ℤ)
    (h : ¬(lo ≤ u ∧ u ≤ hi)) : st b L u = b := by
  unfold st
  have hm : u ∉ L := fun hm => h (hL _ hm)
  simp [hm]

open OMA.S_oeis_a266792 in
lemma step_st (rule : ℕ) (lo hi : ℤ) (b b' : Bool) (L L' : List ℤ)
    (hL : inBox lo hi L) (hL' : inBox lo hi L')
    (hr : ruleOut rule b b b = b')
    (hbox : ∀ x ∈ rng lo hi, stp rule (st b L) x = st b' L' x) :
    stp rule (st b L) = st b' L' := by
  funext x
  by_cases h : lo - 1 ≤ x ∧ x ≤ hi + 1
  · exact hbox x (mem_rng lo hi x h.1 h.2)
  · rw [st_far b' lo hi L' hL' x (by omega)]
    unfold stp
    rw [st_far b lo hi L hL x (by omega), st_far b lo hi L hL (x - 1) (by omega),
      st_far b lo hi L hL (x + 1) (by omega)]
    exact hr

open OMA.S_oeis_a266792 in
lemma stp_shift (rule : ℕ) (g : ℤ → Bool) (c : ℤ) :
    stp rule (fun i => g (i - c)) = fun i => stp rule g (i - c) := by
  funext i
  show ruleOut rule (g (i - 1 - c)) (g (i - c)) (g (i + 1 - c)) =
    ruleOut rule (g (i - c - 1)) (g (i - c)) (g (i - c + 1))
  rw [show i - 1 - c = i - c - 1 from by ring, show i + 1 - c = i - c + 1 from by ring]

lemma st_map (b : Bool) (L : List ℤ) (d : ℤ) :
    st b (L.map (fun x => x + d)) = fun i => st b L (i - d) := by
  funext i
  show xor b (decide (i ∈ L.map (fun x => x + d))) = xor b (decide (i - d ∈ L))
  have h : (i ∈ L.map (fun x => x + d)) ↔ (i - d ∈ L) := by
    rw [List.mem_map]
    constructor
    · rintro ⟨a, ha, rfl⟩
      simpa using ha
    · intro h
      exact ⟨i - d, h, by ring⟩
  rw [decide_eq_decide.mpr h]

lemma count_one (t : ℕ) (c p : ℤ) (hp : -(t : ℤ) ≤ p + c ∧ p + c ≤ t) :
    (∑ j ∈ Finset.range (2 * t + 1), if ((j : ℤ) - t - c = p) then (1 : ℤ) else 0) = 1 := by
  have h1 : (((p + c + t).toNat : ℕ) : ℤ) = p + c + t := Int.toNat_of_nonneg (by omega)
  rw [Finset.sum_eq_single (p + c + t).toNat]
  · rw [if_pos]
    omega
  · intro j _ hj
    rw [if_neg]
    intro h
    apply hj
    omega
  · intro h
    exfalso
    apply h
    rw [Finset.mem_range]
    omega

lemma count_fin (t : ℕ) (c : ℤ) (L : List ℤ) (hnd : L.Nodup)
    (hbox : ∀ p ∈ L, -(t : ℤ) ≤ p + c ∧ p + c ≤ t) :
    (∑ j ∈ Finset.range (2 * t + 1), if ((j : ℤ) - t - c ∈ L) then (1 : ℤ) else 0) = L.length := by
  induction L with
  | nil => simp
  | cons p L ih =>
    have hp : p ∉ L := (List.nodup_cons.mp hnd).1
    have h1 := ih (List.nodup_cons.mp hnd).2 (fun q hq => hbox q (List.mem_cons_of_mem _ hq))
    have h2 := count_one t c p (hbox p List.mem_cons_self)
    have hsplit : (∑ j ∈ Finset.range (2 * t + 1),
        if ((j : ℤ) - t - c ∈ p :: L) then (1 : ℤ) else 0) =
        (∑ j ∈ Finset.range (2 * t + 1), if ((j : ℤ) - t - c = p) then (1 : ℤ) else 0) +
        (∑ j ∈ Finset.range (2 * t + 1), if ((j : ℤ) - t - c ∈ L) then (1 : ℤ) else 0) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      by_cases hq : (j : ℤ) - t - c = p
      · have hq' : (j : ℤ) - t - c ∉ L := hq ▸ hp
        rw [if_pos (hq ▸ List.mem_cons_self), if_neg hq', if_pos hq]
        norm_num
      · by_cases hm : (j : ℤ) - t - c ∈ L
        · rw [if_pos (List.mem_cons_of_mem _ hm), if_pos hm, if_neg hq]
          norm_num
        · have hm' : (j : ℤ) - t - c ∉ p :: L := by
            intro h
            rcases List.mem_cons.mp h with h | h
            · exact hq h
            · exact hm h
          rw [if_neg hm', if_neg hm, if_neg hq]
          norm_num
    rw [hsplit, h1, h2, List.length_cons]
    push_cast
    ring

lemma count_st (t : ℕ) (b : Bool) (c : ℤ) (L : List ℤ) (hnd : L.Nodup)
    (hbox : ∀ p ∈ L, -(t : ℤ) ≤ p + c ∧ p + c ≤ t) :
    ((∑ j ∈ Finset.range (2 * t + 1), if st b L ((j : ℤ) - t - c) then 1 else 0 : ℕ) : ℤ) =
      if b then (2 * (t : ℤ) + 1) - (L.length : ℤ) else (L.length : ℤ) := by
  have hc := count_fin t c L hnd hbox
  have key : ∀ j : ℕ, (if st b L ((j : ℤ) - t - c) then (1 : ℤ) else 0) =
      if b then 1 - (if ((j : ℤ) - t - c ∈ L) then (1 : ℤ) else 0)
      else (if ((j : ℤ) - t - c ∈ L) then (1 : ℤ) else 0) := by
    intro j
    unfold st
    by_cases h : ((j : ℤ) - t - c ∈ L) <;> cases b <;> simp [h]
  push_cast
  simp only [key]
  cases b
  · simpa using hc
  · simp only [if_true, Finset.sum_sub_distrib, hc]
    simp

open OMA.S_oeis_a266792 in
lemma cell_zero (rule : ℕ) : cell rule 0 = st false [0] := by
  funext i
  simp [cell, st]

open OMA.S_oeis_a266792 in
lemma cell_succ (rule t : ℕ) : cell rule (t + 1) = stp rule (cell rule t) := rfl

open OMA.S_oeis_a266792 in
lemma on_of_state (rule t : ℕ) (b : Bool) (c : ℤ) (L : List ℤ)
    (hs : cell rule t = fun i => st b L (i - c)) (hnd : L.Nodup)
    (hbox : ∀ p ∈ L, -(t : ℤ) ≤ p + c ∧ p + c ≤ t) :
    (onCount rule t : ℤ) = if b then (2 * (t : ℤ) + 1) - (L.length : ℤ) else (L.length : ℤ) := by
  unfold onCount
  rw [hs]
  exact count_st t b c L hnd hbox

open OMA.S_oeis_a266792 in
lemma on_of_state0 (rule t : ℕ) (b : Bool) (L : List ℤ)
    (hs : cell rule t = st b L) (hnd : L.Nodup)
    (hbox : ∀ p ∈ L, -(t : ℤ) ≤ p ∧ p ≤ t) :
    (onCount rule t : ℤ) = if b then (2 * (t : ℤ) + 1) - (L.length : ℤ) else (L.length : ℤ) := by
  refine on_of_state rule t b 0 L ?_ hnd ?_
  · rw [hs]
    funext i
    simp
  · intro p hp
    have := hbox p hp
    omega


open OMA.S_oeis_a266792 in
lemma step0 : stp 61 (st false [0]) = st true [-1] :=
  step_st 61 (-1) (0) false true _ _ (by unfold inBox; decide) (by unfold inBox; decide) (by decide) (by decide)

open OMA.S_oeis_a266792 in
lemma step1 : stp 61 (st true [-1]) = st false [-1, 0] :=
  step_st 61 (-1) (0) true false _ _ (by unfold inBox; decide) (by unfold inBox; decide) (by decide) (by decide)

open OMA.S_oeis_a266792 in
lemma step2 : stp 61 (st false [-1, 0]) = st true [-2, 0] :=
  step_st 61 (-2) (0) false true _ _ (by unfold inBox; decide) (by unfold inBox; decide) (by decide) (by decide)

open OMA.S_oeis_a266792 in
lemma step3 : stp 61 (st true [-2, 0]) = st false [-2, -1, 0, 1] :=
  step_st 61 (-2) (1) true false _ _ (by unfold inBox; decide) (by unfold inBox; decide) (by decide) (by decide)

open OMA.S_oeis_a266792 in
lemma step4 : stp 61 (st false [-2, -1, 0, 1]) = st true [-3, -1, 0, 1] :=
  step_st 61 (-3) (1) false true _ _ (by unfold inBox; decide) (by unfold inBox; decide) (by decide) (by decide)

open OMA.S_oeis_a266792 in
lemma stepP0 : stp 61 (st true [-3, -1, 0, 1]) = st false [-3, -2, -1, 0, 2] :=
  step_st 61 (-3) (2) true false _ _ (by unfold inBox; decide) (by unfold inBox; decide) (by decide) (by decide)

open OMA.S_oeis_a266792 in
lemma stepPlast : stp 61 (st false [-3, -2, -1, 0, 2]) = st true (([-3, -1, 0, 1] : List ℤ).map (fun x => x + (-1))) := by
  have e : (([-3, -1, 0, 1] : List ℤ).map (fun x => x + (-1)) : List ℤ) = ([-4, -2, -1, 0] : List ℤ) := by decide
  rw [e]
  exact step_st 61 (-4) (2) false true _ _ (by unfold inBox; decide) (by unfold inBox; decide) (by decide) (by decide)

open OMA.S_oeis_a266792 in
lemma s0 : cell 61 0 = st false [0] := cell_zero 61

open OMA.S_oeis_a266792 in
lemma s1 : cell 61 1 = st true [-1] := by
  rw [cell_succ, s0]
  exact step0

open OMA.S_oeis_a266792 in
lemma s2 : cell 61 2 = st false [-1, 0] := by
  rw [cell_succ, s1]
  exact step1

open OMA.S_oeis_a266792 in
lemma s3 : cell 61 3 = st true [-2, 0] := by
  rw [cell_succ, s2]
  exact step2

open OMA.S_oeis_a266792 in
lemma s4 : cell 61 4 = st false [-2, -1, 0, 1] := by
  rw [cell_succ, s3]
  exact step3

open OMA.S_oeis_a266792 in
lemma s5 : cell 61 5 = st true [-3, -1, 0, 1] := by
  rw [cell_succ, s4]
  exact step4

open OMA.S_oeis_a266792 in
lemma s6 : cell 61 6 = st false [-3, -2, -1, 0, 2] := by
  rw [cell_succ, s5]
  exact stepP0

open OMA.S_oeis_a266792 in
lemma per (m : ℕ) : (cell 61 (5 + 2 * m) = fun i => st true [-3, -1, 0, 1] (i - (-1) * (m : ℤ))) ∧
    (cell 61 (5 + 2 * m + 1) = fun i => st false [-3, -2, -1, 0, 2] (i - (-1) * (m : ℤ))) := by
  induction m with
  | zero =>
    refine ⟨?_, ?_⟩
    · rw [show 5 + 2 * 0 = 5 from rfl, s5]
      funext i
      simp
    · rw [show 5 + 2 * 0 + 1 = 6 from rfl, s6]
      funext i
      simp
  | succ k ih =>
    obtain ⟨ih0, ih1⟩ := ih
    have h0 : (cell 61 (5 + 2 * (k + 1)) = fun i => st true [-3, -1, 0, 1] (i - (-1) * ((k + 1 : ℕ) : ℤ))) := by
      rw [show 5 + 2 * (k + 1) = (5 + 2 * k + 1) + 1 from by ring, cell_succ, ih1, stp_shift, stepPlast, st_map]
      funext i
      show st true [-3, -1, 0, 1] (i - (-1) * (k : ℤ) - (-1)) = st true [-3, -1, 0, 1] (i - (-1) * ((k + 1 : ℕ) : ℤ))
      congr 1
      push_cast
      ring
    have h1 : (cell 61 (5 + 2 * (k + 1) + 1) = fun i => st false [-3, -2, -1, 0, 2] (i - (-1) * ((k + 1 : ℕ) : ℤ))) := by
      rw [cell_succ, h0, stp_shift, stepP0]
    exact ⟨h0, h1⟩

open OMA.S_oeis_a266792 in
lemma onC1 (t : ℕ) (h0 : 5 ≤ t) (hp : t % 2 = 1) : (onCount 61 t : ℤ) = 2 * (t : ℤ) + 1 - 4 := by
  obtain ⟨m, rfl⟩ : ∃ m, t = 5 + 2 * m := ⟨(t - 5) / 2, by omega⟩
  rw [on_of_state 61 (5 + 2 * m) true ((-1) * (m : ℤ)) [-3, -1, 0, 1] (per m).1 (by decide) (by
    intro q hq
    have hq' := (show inBox (-3) (1) [-3, -1, 0, 1] by unfold inBox; decide) q hq
    constructor <;> omega)]
  simp

open OMA.S_oeis_a266792 in
lemma onC0 (t : ℕ) (h0 : 6 ≤ t) (hp : t % 2 = 0) : (onCount 61 t : ℤ) = 5 := by
  obtain ⟨m, rfl⟩ : ∃ m, t = 5 + 2 * m + 1 := ⟨(t - 6) / 2, by omega⟩
  rw [on_of_state 61 (5 + 2 * m + 1) false ((-1) * (m : ℤ)) [-3, -2, -1, 0, 2] (per m).2 (by decide) (by
    intro q hq
    have hq' := (show inBox (-3) (2) [-3, -2, -1, 0, 2] by unfold inBox; decide) q hq
    constructor <;> omega)]
  simp

open OMA.S_oeis_a266792 in
lemma ov0 : (onCount 61 0 : ℤ) = 1 := by
  rw [on_of_state0 61 0 false [0] s0 (by decide) (by decide)]
  simp

open OMA.S_oeis_a266792 in
lemma ov1 : (onCount 61 1 : ℤ) = 2 := by
  rw [on_of_state0 61 1 true [-1] s1 (by decide) (by decide)]
  simp

open OMA.S_oeis_a266792 in
lemma ov2 : (onCount 61 2 : ℤ) = 2 := by
  rw [on_of_state0 61 2 false [-1, 0] s2 (by decide) (by decide)]
  simp

open OMA.S_oeis_a266792 in
lemma ov3 : (onCount 61 3 : ℤ) = 5 := by
  rw [on_of_state0 61 3 true [-2, 0] s3 (by decide) (by decide)]
  simp

open OMA.S_oeis_a266792 in
lemma ov4 : (onCount 61 4 : ℤ) = 4 := by
  rw [on_of_state0 61 4 false [-2, -1, 0, 1] s4 (by decide) (by decide)]
  simp

open OMA.S_oeis_a266792 in
lemma ov5 : (onCount 61 5 : ℤ) = 7 :=
  (onC1 5 (by norm_num) (by norm_num)).trans (by norm_num)

open OMA.S_oeis_a266792 in
lemma ov6 : (onCount 61 6 : ℤ) = 5 :=
  (onC0 6 (by norm_num) (by norm_num)).trans (by norm_num)

open OMA.S_oeis_a266792 in
lemma ov7 : (onCount 61 7 : ℤ) = 11 :=
  (onC1 7 (by norm_num) (by norm_num)).trans (by norm_num)

open OMA.S_oeis_a266792 in
lemma ov8 : (onCount 61 8 : ℤ) = 5 :=
  (onC0 8 (by norm_num) (by norm_num)).trans (by norm_num)

open OMA.S_oeis_a266792 in
lemma ov9 : (onCount 61 9 : ℤ) = 15 :=
  (onC1 9 (by norm_num) (by norm_num)).trans (by norm_num)

open OMA.S_oeis_a266792 in
lemma ov10 : (onCount 61 10 : ℤ) = 5 :=
  (onC0 10 (by norm_num) (by norm_num)).trans (by norm_num)

open OMA.S_oeis_a266792 in
lemma aC0 (n : ℕ) (h0 : 6 ≤ n) (hp : n % 2 = 0) : (a n : ℚ) = (0 : ℚ) * (n : ℚ) ^ 3 + (0 : ℚ) * (n : ℚ) ^ 2 + (0 : ℚ) * (n : ℚ) + (5 : ℚ) := by
  unfold a
  rw [onC0 n (by omega) (by omega)]
  push_cast
  ring

open OMA.S_oeis_a266792 in
lemma aC1 (n : ℕ) (h0 : 5 ≤ n) (hp : n % 2 = 1) : (a n : ℚ) = (0 : ℚ) * (n : ℚ) ^ 3 + (0 : ℚ) * (n : ℚ) ^ 2 + (2 : ℚ) * (n : ℚ) + (-3 : ℚ) := by
  unfold a
  rw [onC1 n (by omega) (by omega)]
  push_cast
  ring

open OMA.S_oeis_a266792 in
lemma av0 : (a 0 : ℚ) = 1 := by
  unfold a
  rw [ov0]
  norm_num

open OMA.S_oeis_a266792 in
lemma av1 : (a 1 : ℚ) = 2 := by
  unfold a
  rw [ov1]
  norm_num

open OMA.S_oeis_a266792 in
lemma av2 : (a 2 : ℚ) = 2 := by
  unfold a
  rw [ov2]
  norm_num

open OMA.S_oeis_a266792 in
lemma av3 : (a 3 : ℚ) = 5 := by
  unfold a
  rw [ov3]
  norm_num

open OMA.S_oeis_a266792 in
lemma av4 : (a 4 : ℚ) = 4 := by
  unfold a
  rw [ov4]
  norm_num

open OMA.S_oeis_a266792 in
lemma av5 : (a 5 : ℚ) = 7 := by
  unfold a
  rw [ov5]
  norm_num

open OMA.S_oeis_a266792 in
lemma av6 : (a 6 : ℚ) = 5 := by
  unfold a
  rw [ov6]
  norm_num

open OMA.S_oeis_a266792 in
lemma av7 : (a 7 : ℚ) = 11 := by
  unfold a
  rw [ov7]
  norm_num

open OMA.S_oeis_a266792 in
lemma av8 : (a 8 : ℚ) = 5 := by
  unfold a
  rw [ov8]
  norm_num

open OMA.S_oeis_a266792 in
lemma av9 : (a 9 : ℚ) = 15 := by
  unfold a
  rw [ov9]
  norm_num

open OMA.S_oeis_a266792 in
lemma rec_gen (m : ℕ) : (1 : ℚ) * (a (m + 10) : ℚ) + (-2 : ℚ) * (a (m + 8) : ℚ) + (1 : ℚ) * (a (m + 6) : ℚ) = 0 := by
  rcases (show m % 2 = 0 ∨ m % 2 = 1 by omega) with h | h
  · rw [aC0 (m + 10) (by omega) (by omega),
      aC0 (m + 8) (by omega) (by omega),
      aC0 (m + 6) (by omega) (by omega)]
    push_cast
    ring
  · rw [aC1 (m + 10) (by omega) (by omega),
      aC1 (m + 8) (by omega) (by omega),
      aC1 (m + 6) (by omega) (by omega)]
    push_cast
    ring

open PowerSeries in
lemma coeff_term (f : ℕ → ℚ) (c : ℚ) (k n : ℕ) :
    coeff n (mk f * (C c * X ^ k)) = if k ≤ n then c * f (n - k) else 0 := by
  rw [← mul_assoc, mul_comm (mk f) (C c), mul_assoc, coeff_C_mul, coeff_mul_X_pow']
  split_ifs <;> simp [coeff_mk]

end A266792Aux

set_option maxHeartbeats 1600000 in
open OMA.S_oeis_a266792 A266792Aux PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a266792.main := by
  refine ⟨?_, ?_, ?_⟩
  · intro n hn
    rcases Nat.lt_or_ge n 6 with hs | hs
    · interval_cases n <;> norm_num [av0, av1, av2, av3, av4, av5, av6, av7, av8, av9]
    · rcases (show n % 2 = 0 ∨ n % 2 = 1 by omega) with h | h
      · have h1 : (-1 : ℚ) ^ n = 1 := Even.neg_one_pow (by rw [Nat.even_iff]; omega)
        rw [aC0 n (by omega) h]
        rw [h1]
        ring
      · have h1 : (-1 : ℚ) ^ n = -1 := Odd.neg_one_pow (by rw [Nat.odd_iff]; omega)
        rw [aC1 n (by omega) h]
        rw [h1]
        ring
  · intro n hn
    rcases Nat.lt_or_ge n 10 with hs | hs
    · interval_cases n <;> norm_num [av0, av1, av2, av3, av4, av5, av6, av7, av8, av9]
    · obtain ⟨j, rfl⟩ : ∃ j, n = j + 4 := ⟨n - 4, by omega⟩
      rw [show j + 4 - 2 = j + 2 from by omega, show j + 4 - 4 = j from by omega]
      rcases (show j % 2 = 0 ∨ j % 2 = 1 by omega) with h | h
      · rw [aC0 (j + 4) (by omega) (by omega), aC0 (j + 2) (by omega) (by omega), aC0 (j) (by omega) (by omega)]
        push_cast
        ring
      · rw [aC1 (j + 4) (by omega) (by omega), aC1 (j + 2) (by omega) (by omega), aC1 (j) (by omega) (by omega)]
        push_cast
        ring
  · have hD : (((1 - X) ^ 2 * (1 + X) ^ 2 : PowerSeries ℚ)) = C (1 : ℚ) * X ^ 0 + C (-2 : ℚ) * X ^ 2 + C (1 : ℚ) * X ^ 4 := by
      simp only [map_one, map_ofNat, map_neg]
      ring
    have hN : (1 + 2 * X + X ^ 3 + X ^ 4 - X ^ 5 - X ^ 6 + 2 * X ^ 7 - X ^ 8 : PowerSeries ℚ) = C (1 : ℚ) * X ^ 0 + C (2 : ℚ) * X ^ 1 + C (1 : ℚ) * X ^ 3 + C (1 : ℚ) * X ^ 4 + C (-1 : ℚ) * X ^ 5 + C (-1 : ℚ) * X ^ 6 + C (2 : ℚ) * X ^ 7 + C (-1 : ℚ) * X ^ 8 := by
      simp only [map_one, map_ofNat, map_neg]
      ring
    rw [hD, hN]
    ext n
    simp only [mul_add, map_add, coeff_term, PowerSeries.coeff_C_mul_X_pow]
    rcases Nat.lt_or_ge n 10 with hs | hs
    · interval_cases n <;> norm_num [av0, av1, av2, av3, av4, av5, av6, av7, av8, av9]
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 10 := ⟨n - 10, by omega⟩
      rw [if_pos (show 0 ≤ m + 10 by omega),
        if_pos (show 2 ≤ m + 10 by omega),
        if_pos (show 4 ≤ m + 10 by omega),
        if_neg (show ¬ (m + 10 = 0) by omega),
        if_neg (show ¬ (m + 10 = 1) by omega),
        if_neg (show ¬ (m + 10 = 3) by omega),
        if_neg (show ¬ (m + 10 = 4) by omega),
        if_neg (show ¬ (m + 10 = 5) by omega),
        if_neg (show ¬ (m + 10 = 6) by omega),
        if_neg (show ¬ (m + 10 = 7) by omega),
        if_neg (show ¬ (m + 10 = 8) by omega)]
      rw [show m + 10 - 2 = m + 8 from by omega,
        show m + 10 - 4 = m + 6 from by omega]
      rw [show m + 10 - 0 = m + 10 from by omega]
      have hrec := rec_gen m
      linarith
