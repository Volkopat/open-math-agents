import OMAStatements.S_oeis_a267802
import Mathlib

namespace A267802Aux

def st (b : Bool) (L : List ℤ) : ℤ → Bool := fun x => xor b (decide (x ∈ L))

open OMA.S_oeis_a267802 in
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

open OMA.S_oeis_a267802 in
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

open OMA.S_oeis_a267802 in
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

open OMA.S_oeis_a267802 in
lemma cell_zero (rule : ℕ) : cell rule 0 = st false [0] := by
  funext i
  simp [cell, st]

open OMA.S_oeis_a267802 in
lemma cell_succ (rule t : ℕ) : cell rule (t + 1) = stp rule (cell rule t) := rfl

open OMA.S_oeis_a267802 in
lemma on_of_state (rule t : ℕ) (b : Bool) (c : ℤ) (L : List ℤ)
    (hs : cell rule t = fun i => st b L (i - c)) (hnd : L.Nodup)
    (hbox : ∀ p ∈ L, -(t : ℤ) ≤ p + c ∧ p + c ≤ t) :
    (onCount rule t : ℤ) = if b then (2 * (t : ℤ) + 1) - (L.length : ℤ) else (L.length : ℤ) := by
  unfold onCount
  rw [hs]
  exact count_st t b c L hnd hbox

open OMA.S_oeis_a267802 in
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


open OMA.S_oeis_a267802 in
lemma step0 : stp 213 (st false [0]) = st true [-1] :=
  step_st 213 (-1) (0) false true _ _ (by unfold inBox; decide) (by unfold inBox; decide) (by decide) (by decide)

open OMA.S_oeis_a267802 in
lemma step1 : stp 213 (st true [-1]) = st true [-1, 0] :=
  step_st 213 (-1) (0) true true _ _ (by unfold inBox; decide) (by unfold inBox; decide) (by decide) (by decide)

open OMA.S_oeis_a267802 in
lemma stepPlast : stp 213 (st true [-1, 0]) = st true (([-1, 0] : List ℤ).map (fun x => x + (1))) := by
  have e : (([-1, 0] : List ℤ).map (fun x => x + (1)) : List ℤ) = ([0, 1] : List ℤ) := by decide
  rw [e]
  exact step_st 213 (-1) (1) true true _ _ (by unfold inBox; decide) (by unfold inBox; decide) (by decide) (by decide)

open OMA.S_oeis_a267802 in
lemma s0 : cell 213 0 = st false [0] := cell_zero 213

open OMA.S_oeis_a267802 in
lemma s1 : cell 213 1 = st true [-1] := by
  rw [cell_succ, s0]
  exact step0

open OMA.S_oeis_a267802 in
lemma s2 : cell 213 2 = st true [-1, 0] := by
  rw [cell_succ, s1]
  exact step1

open OMA.S_oeis_a267802 in
lemma per (m : ℕ) : cell 213 (2 + m) = fun i => st true [-1, 0] (i - (m : ℤ)) := by
  induction m with
  | zero =>
    rw [show 2 + 0 = 2 from rfl, s2]
    funext i
    simp
  | succ k ih =>
    rw [show 2 + (k + 1) = (2 + k) + 1 from by ring, cell_succ, ih, stp_shift, stepPlast, st_map]
    funext i
    show st true [-1, 0] (i - (k : ℤ) - (1)) = st true [-1, 0] (i - ((k + 1 : ℕ) : ℤ))
    congr 1
    push_cast
    ring

lemma w_one (t : ℕ) (B c p : ℤ) (hp : -(t : ℤ) ≤ p + c ∧ p + c ≤ t) :
    (∑ j ∈ Finset.range (2 * t + 1), if ((j : ℤ) - t - c = p) then B ^ (2 * t - j) else 0) =
      B ^ ((t : ℤ) - (p + c)).toNat := by
  have h1 : (((p + c + t).toNat : ℕ) : ℤ) = p + c + t := Int.toNat_of_nonneg (by omega)
  rw [Finset.sum_eq_single (p + c + t).toNat]
  · rw [if_pos (by omega)]
    congr 1
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

lemma w_fin (t : ℕ) (B c : ℤ) (L : List ℤ) (hnd : L.Nodup)
    (hbox : ∀ p ∈ L, -(t : ℤ) ≤ p + c ∧ p + c ≤ t) :
    (∑ j ∈ Finset.range (2 * t + 1), if ((j : ℤ) - t - c ∈ L) then B ^ (2 * t - j) else 0) =
      (L.map (fun p => B ^ ((t : ℤ) - (p + c)).toNat)).sum := by
  induction L with
  | nil => simp
  | cons p L ih =>
    have hp : p ∉ L := (List.nodup_cons.mp hnd).1
    have h1 := ih (List.nodup_cons.mp hnd).2 (fun q hq => hbox q (List.mem_cons_of_mem _ hq))
    have h2 := w_one t B c p (hbox p List.mem_cons_self)
    have hsplit : (∑ j ∈ Finset.range (2 * t + 1),
        if ((j : ℤ) - t - c ∈ p :: L) then B ^ (2 * t - j) else 0) =
        (∑ j ∈ Finset.range (2 * t + 1), if ((j : ℤ) - t - c = p) then B ^ (2 * t - j) else 0) +
        (∑ j ∈ Finset.range (2 * t + 1), if ((j : ℤ) - t - c ∈ L) then B ^ (2 * t - j) else 0) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      by_cases hq : (j : ℤ) - t - c = p
      · have hq' : (j : ℤ) - t - c ∉ L := hq ▸ hp
        rw [if_pos (hq ▸ List.mem_cons_self), if_neg hq', if_pos hq]
        ring
      · by_cases hm : (j : ℤ) - t - c ∈ L
        · rw [if_pos (List.mem_cons_of_mem _ hm), if_pos hm, if_neg hq]
          ring
        · have hm' : (j : ℤ) - t - c ∉ p :: L := by
            intro h
            rcases List.mem_cons.mp h with h | h
            · exact hq h
            · exact hm h
          rw [if_neg hm', if_neg hm, if_neg hq]
          ring
    rw [hsplit, h1, h2, List.map_cons, List.sum_cons]

lemma w_st (t : ℕ) (B : ℤ) (b : Bool) (c : ℤ) (L : List ℤ) (hnd : L.Nodup)
    (hbox : ∀ p ∈ L, -(t : ℤ) ≤ p + c ∧ p + c ≤ t) :
    (∑ j ∈ Finset.range (2 * t + 1), if st b L ((j : ℤ) - t - c) then B ^ (2 * t - j) else 0) =
      if b then (∑ j ∈ Finset.range (2 * t + 1), B ^ (2 * t - j)) -
        (L.map (fun p => B ^ ((t : ℤ) - (p + c)).toNat)).sum
      else (L.map (fun p => B ^ ((t : ℤ) - (p + c)).toNat)).sum := by
  have hc := w_fin t B c L hnd hbox
  have key : ∀ j : ℕ, (if st b L ((j : ℤ) - t - c) then B ^ (2 * t - j) else 0) =
      if b then B ^ (2 * t - j) - (if ((j : ℤ) - t - c ∈ L) then B ^ (2 * t - j) else 0)
      else (if ((j : ℤ) - t - c ∈ L) then B ^ (2 * t - j) else 0) := by
    intro j
    unfold st
    by_cases h : ((j : ℤ) - t - c ∈ L) <;> cases b <;> simp [h]
  simp only [key]
  cases b
  · simpa using hc
  · simp only [if_true, Finset.sum_sub_distrib, hc]

lemma geom (B : ℤ) (n : ℕ) :
    (∑ j ∈ Finset.range (2 * n + 1), B ^ (2 * n - j)) * (B - 1) = B ^ (2 * n + 1) - 1 := by
  have h : ∑ j ∈ Finset.range (2 * n + 1), B ^ (2 * n - j) =
      ∑ j ∈ Finset.range (2 * n + 1), B ^ j :=
    Finset.sum_range_reflect (fun j => B ^ j) (2 * n + 1)
  rw [h, geom_sum_mul]


open OMA.S_oeis_a267802 in
lemma aC (n : ℕ) (h : 2 ≤ n) : 1 * a n = 2 ^ (2 * n + 1) - 13 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = 2 + m := ⟨n - 2, by omega⟩
  have hw := w_st (2 + m) 2 true (m : ℤ) [-1, 0] (by decide) (by
    intro q hq
    have hq' := (show inBox (-1) (0) [-1, 0] by unfold inBox; decide) q hq
    constructor <;> omega)
  have key : a (2 + m) = (∑ j ∈ Finset.range (2 * (2 + m) + 1), (2 : ℤ) ^ (2 * (2 + m) - j)) -
      ([-1, 0].map (fun p => (2 : ℤ) ^ (((2 + m : ℕ) : ℤ) - (p + (m : ℤ))).toNat)).sum := by
    unfold a
    rw [per m]
    exact hw
  have e0 : (((2 + m : ℕ) : ℤ) - (-1 + (m : ℤ))).toNat = 3 := by omega
  have e1 : (((2 + m : ℕ) : ℤ) - (0 + (m : ℤ))).toNat = 2 := by omega
  have hg := geom 2 (2 + m)
  rw [key]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  rw [e0, e1]
  linear_combination hg

open OMA.S_oeis_a267802 in
lemma aQ (n : ℕ) (h : 2 ≤ n) : (1 : ℚ) * (a n : ℚ) = (2 : ℚ) ^ (2 * n + 1) - 13 := by
  exact_mod_cast aC n h

open OMA.S_oeis_a267802 in
lemma av0 : (a 0 : ℚ) = 1 := by
  have h : a 0 = 1 := by decide
  rw [h]
  norm_num

open OMA.S_oeis_a267802 in
lemma av1 : (a 1 : ℚ) = 3 := by
  have h : a 1 = 3 := by decide
  rw [h]
  norm_num

open OMA.S_oeis_a267802 in
lemma av2 : (a 2 : ℚ) = 19 := by
  have h := aQ 2 (by norm_num)
  norm_num at h
  linarith

open OMA.S_oeis_a267802 in
lemma av3 : (a 3 : ℚ) = 115 := by
  have h := aQ 3 (by norm_num)
  norm_num at h
  linarith

open OMA.S_oeis_a267802 in
lemma arec (j : ℕ) : (a (j + 4) : ℚ) = 5 * (a (j + 3) : ℚ) - 4 * (a (j + 2) : ℚ) := by
  have h4 := aQ (j + 4) (by omega)
  have h3 := aQ (j + 3) (by omega)
  have h2 := aQ (j + 2) (by omega)
  linear_combination (1 / 1 : ℚ) * h4 - (5 / 1 : ℚ) * h3 + (4 / 1 : ℚ) * h2

open PowerSeries in
lemma coeff_term (f : ℕ → ℚ) (c : ℚ) (k n : ℕ) :
    coeff n (mk f * (C c * X ^ k)) = if k ≤ n then c * f (n - k) else 0 := by
  rw [← mul_assoc, mul_comm (mk f) (C c), mul_assoc, coeff_C_mul, coeff_mul_X_pow']
  split_ifs <;> simp [coeff_mk]

end A267802Aux

set_option maxHeartbeats 1600000 in
open OMA.S_oeis_a267802 A267802Aux PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a267802.main := by
  refine ⟨?_, ?_, ?_⟩
  · intro n hn
    obtain ⟨j, rfl⟩ : ∃ j, n = j + 4 := ⟨n - 4, by omega⟩
    rw [show j + 4 - 1 = j + 3 from by omega, show j + 4 - 2 = j + 2 from by omega]
    exact arec j
  · have hD : (((1 - X) * (1 - 4 * X) : PowerSeries ℚ)) = C (1 : ℚ) * X ^ 0 + C (-5 : ℚ) * X ^ 1 + C (4 : ℚ) * X ^ 2 := by
      simp only [map_one, map_ofNat, map_neg]
      ring
    have hN : ((1 + 2 * X) * (1 - 4 * X + 16 * X ^ 2) : PowerSeries ℚ) = C (1 : ℚ) * X ^ 0 + C (-2 : ℚ) * X ^ 1 + C (8 : ℚ) * X ^ 2 + C (32 : ℚ) * X ^ 3 := by
      simp only [map_one, map_ofNat, map_neg]
      ring
    rw [hD, hN]
    ext n
    simp only [mul_add, map_add, coeff_term, PowerSeries.coeff_C_mul_X_pow]
    rcases Nat.lt_or_ge n 4 with hs | hs
    · interval_cases n <;> norm_num [av0, av1, av2, av3]
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
      rw [if_pos (show 0 ≤ m + 4 by omega),
        if_pos (show 1 ≤ m + 4 by omega),
        if_pos (show 2 ≤ m + 4 by omega),
        if_neg (show ¬ (m + 4 = 0) by omega),
        if_neg (show ¬ (m + 4 = 1) by omega),
        if_neg (show ¬ (m + 4 = 2) by omega),
        if_neg (show ¬ (m + 4 = 3) by omega)]
      rw [show m + 4 - 1 = m + 3 from by omega, show m + 4 - 2 = m + 2 from by omega,
        show m + 4 - 0 = m + 4 from by omega]
      have hrec := arec m
      linarith
  · intro n hn
    have h := aQ n hn
    linarith
