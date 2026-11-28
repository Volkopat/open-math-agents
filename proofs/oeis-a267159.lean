import OMAStatements.S_oeis_a267159
import Mathlib

namespace A267159Aux

def st (b : Bool) (L : List ℤ) : ℤ → Bool := fun x => xor b (decide (x ∈ L))

open OMA.S_oeis_a267159 in
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

open OMA.S_oeis_a267159 in
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

open OMA.S_oeis_a267159 in
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

open OMA.S_oeis_a267159 in
lemma cell_zero (rule : ℕ) : cell rule 0 = st false [0] := by
  funext i
  simp [cell, st]

open OMA.S_oeis_a267159 in
lemma cell_succ (rule t : ℕ) : cell rule (t + 1) = stp rule (cell rule t) := rfl

open OMA.S_oeis_a267159 in
lemma on_of_state (rule t : ℕ) (b : Bool) (c : ℤ) (L : List ℤ)
    (hs : cell rule t = fun i => st b L (i - c)) (hnd : L.Nodup)
    (hbox : ∀ p ∈ L, -(t : ℤ) ≤ p + c ∧ p + c ≤ t) :
    (onCount rule t : ℤ) = if b then (2 * (t : ℤ) + 1) - (L.length : ℤ) else (L.length : ℤ) := by
  unfold onCount
  rw [hs]
  exact count_st t b c L hnd hbox

open OMA.S_oeis_a267159 in
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


open OMA.S_oeis_a267159 in
lemma step0 : stp 107 (st false [0]) = st true [0, 1] :=
  step_st 107 (0) (1) false true _ _ (by unfold inBox; decide) (by unfold inBox; decide) (by decide) (by decide)

open OMA.S_oeis_a267159 in
lemma step1 : stp 107 (st true [0, 1]) = st false [-1, 1, 2] :=
  step_st 107 (-1) (2) true false _ _ (by unfold inBox; decide) (by unfold inBox; decide) (by decide) (by decide)

open OMA.S_oeis_a267159 in
lemma step2 : stp 107 (st false [-1, 1, 2]) = st true [-1, 3] :=
  step_st 107 (-1) (3) false true _ _ (by unfold inBox; decide) (by unfold inBox; decide) (by decide) (by decide)

open OMA.S_oeis_a267159 in
lemma step3 : stp 107 (st true [-1, 3]) = st false [-2, -1, 0, 2, 3, 4] :=
  step_st 107 (-2) (4) true false _ _ (by unfold inBox; decide) (by unfold inBox; decide) (by decide) (by decide)

open OMA.S_oeis_a267159 in
lemma step4 : stp 107 (st false [-2, -1, 0, 2, 3, 4]) = st true [-1, 3, 5] :=
  step_st 107 (-2) (5) false true _ _ (by unfold inBox; decide) (by unfold inBox; decide) (by decide) (by decide)

open OMA.S_oeis_a267159 in
lemma step5 : stp 107 (st true [-1, 3, 5]) = st false [-2, -1, 0, 2, 3, 5, 6] :=
  step_st 107 (-2) (6) true false _ _ (by unfold inBox; decide) (by unfold inBox; decide) (by decide) (by decide)

open OMA.S_oeis_a267159 in
lemma step6 : stp 107 (st false [-2, -1, 0, 2, 3, 5, 6]) = st true [-1, 7] :=
  step_st 107 (-2) (7) false true _ _ (by unfold inBox; decide) (by unfold inBox; decide) (by decide) (by decide)

open OMA.S_oeis_a267159 in
lemma stepP0 : stp 107 (st true [-1, 7]) = st false [-2, -1, 0, 6, 7, 8] :=
  step_st 107 (-2) (8) true false _ _ (by unfold inBox; decide) (by unfold inBox; decide) (by decide) (by decide)

open OMA.S_oeis_a267159 in
lemma stepP1 : stp 107 (st false [-2, -1, 0, 6, 7, 8]) = st true [-1, 1, 7, 9] :=
  step_st 107 (-2) (9) false true _ _ (by unfold inBox; decide) (by unfold inBox; decide) (by decide) (by decide)

open OMA.S_oeis_a267159 in
lemma stepP2 : stp 107 (st true [-1, 1, 7, 9]) = st false [-2, -1, 1, 2, 6, 7, 9, 10] :=
  step_st 107 (-2) (10) true false _ _ (by unfold inBox; decide) (by unfold inBox; decide) (by decide) (by decide)

open OMA.S_oeis_a267159 in
lemma stepPlast : stp 107 (st false [-2, -1, 1, 2, 6, 7, 9, 10]) = st true (([-1, 7] : List ℤ).map (fun x => x + (4))) := by
  have e : (([-1, 7] : List ℤ).map (fun x => x + (4)) : List ℤ) = ([3, 11] : List ℤ) := by decide
  rw [e]
  exact step_st 107 (-2) (11) false true _ _ (by unfold inBox; decide) (by unfold inBox; decide) (by decide) (by decide)

open OMA.S_oeis_a267159 in
lemma s0 : cell 107 0 = st false [0] := cell_zero 107

open OMA.S_oeis_a267159 in
lemma s1 : cell 107 1 = st true [0, 1] := by
  rw [cell_succ, s0]
  exact step0

open OMA.S_oeis_a267159 in
lemma s2 : cell 107 2 = st false [-1, 1, 2] := by
  rw [cell_succ, s1]
  exact step1

open OMA.S_oeis_a267159 in
lemma s3 : cell 107 3 = st true [-1, 3] := by
  rw [cell_succ, s2]
  exact step2

open OMA.S_oeis_a267159 in
lemma s4 : cell 107 4 = st false [-2, -1, 0, 2, 3, 4] := by
  rw [cell_succ, s3]
  exact step3

open OMA.S_oeis_a267159 in
lemma s5 : cell 107 5 = st true [-1, 3, 5] := by
  rw [cell_succ, s4]
  exact step4

open OMA.S_oeis_a267159 in
lemma s6 : cell 107 6 = st false [-2, -1, 0, 2, 3, 5, 6] := by
  rw [cell_succ, s5]
  exact step5

open OMA.S_oeis_a267159 in
lemma s7 : cell 107 7 = st true [-1, 7] := by
  rw [cell_succ, s6]
  exact step6

open OMA.S_oeis_a267159 in
lemma s8 : cell 107 8 = st false [-2, -1, 0, 6, 7, 8] := by
  rw [cell_succ, s7]
  exact stepP0

open OMA.S_oeis_a267159 in
lemma s9 : cell 107 9 = st true [-1, 1, 7, 9] := by
  rw [cell_succ, s8]
  exact stepP1

open OMA.S_oeis_a267159 in
lemma s10 : cell 107 10 = st false [-2, -1, 1, 2, 6, 7, 9, 10] := by
  rw [cell_succ, s9]
  exact stepP2

open OMA.S_oeis_a267159 in
lemma per (m : ℕ) : (cell 107 (7 + 4 * m) = fun i => st true [-1, 7] (i - (4) * (m : ℤ))) ∧
    (cell 107 (7 + 4 * m + 1) = fun i => st false [-2, -1, 0, 6, 7, 8] (i - (4) * (m : ℤ))) ∧
    (cell 107 (7 + 4 * m + 2) = fun i => st true [-1, 1, 7, 9] (i - (4) * (m : ℤ))) ∧
    (cell 107 (7 + 4 * m + 3) = fun i => st false [-2, -1, 1, 2, 6, 7, 9, 10] (i - (4) * (m : ℤ))) := by
  induction m with
  | zero =>
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [show 7 + 4 * 0 = 7 from rfl, s7]
      funext i
      simp
    · rw [show 7 + 4 * 0 + 1 = 8 from rfl, s8]
      funext i
      simp
    · rw [show 7 + 4 * 0 + 2 = 9 from rfl, s9]
      funext i
      simp
    · rw [show 7 + 4 * 0 + 3 = 10 from rfl, s10]
      funext i
      simp
  | succ k ih =>
    obtain ⟨ih0, ih1, ih2, ih3⟩ := ih
    have h0 : (cell 107 (7 + 4 * (k + 1)) = fun i => st true [-1, 7] (i - (4) * ((k + 1 : ℕ) : ℤ))) := by
      rw [show 7 + 4 * (k + 1) = (7 + 4 * k + 3) + 1 from by ring, cell_succ, ih3, stp_shift, stepPlast, st_map]
      funext i
      show st true [-1, 7] (i - (4) * (k : ℤ) - (4)) = st true [-1, 7] (i - (4) * ((k + 1 : ℕ) : ℤ))
      congr 1
      push_cast
      ring
    have h1 : (cell 107 (7 + 4 * (k + 1) + 1) = fun i => st false [-2, -1, 0, 6, 7, 8] (i - (4) * ((k + 1 : ℕ) : ℤ))) := by
      rw [cell_succ, h0, stp_shift, stepP0]
    have h2 : (cell 107 (7 + 4 * (k + 1) + 2) = fun i => st true [-1, 1, 7, 9] (i - (4) * ((k + 1 : ℕ) : ℤ))) := by
      rw [cell_succ, h1, stp_shift, stepP1]
    have h3 : (cell 107 (7 + 4 * (k + 1) + 3) = fun i => st false [-2, -1, 1, 2, 6, 7, 9, 10] (i - (4) * ((k + 1 : ℕ) : ℤ))) := by
      rw [cell_succ, h2, stp_shift, stepP2]
    exact ⟨h0, h1, h2, h3⟩

open OMA.S_oeis_a267159 in
lemma onC3 (t : ℕ) (h0 : 7 ≤ t) (hp : t % 4 = 3) : (onCount 107 t : ℤ) = 2 * (t : ℤ) + 1 - 2 := by
  obtain ⟨m, rfl⟩ : ∃ m, t = 7 + 4 * m := ⟨(t - 7) / 4, by omega⟩
  rw [on_of_state 107 (7 + 4 * m) true ((4) * (m : ℤ)) [-1, 7] (per m).1 (by decide) (by
    intro q hq
    have hq' := (show inBox (-1) (7) [-1, 7] by unfold inBox; decide) q hq
    constructor <;> omega)]
  simp

open OMA.S_oeis_a267159 in
lemma onC0 (t : ℕ) (h0 : 8 ≤ t) (hp : t % 4 = 0) : (onCount 107 t : ℤ) = 6 := by
  obtain ⟨m, rfl⟩ : ∃ m, t = 7 + 4 * m + 1 := ⟨(t - 8) / 4, by omega⟩
  rw [on_of_state 107 (7 + 4 * m + 1) false ((4) * (m : ℤ)) [-2, -1, 0, 6, 7, 8] (per m).2.1 (by decide) (by
    intro q hq
    have hq' := (show inBox (-2) (8) [-2, -1, 0, 6, 7, 8] by unfold inBox; decide) q hq
    constructor <;> omega)]
  simp

open OMA.S_oeis_a267159 in
lemma onC1 (t : ℕ) (h0 : 9 ≤ t) (hp : t % 4 = 1) : (onCount 107 t : ℤ) = 2 * (t : ℤ) + 1 - 4 := by
  obtain ⟨m, rfl⟩ : ∃ m, t = 7 + 4 * m + 2 := ⟨(t - 9) / 4, by omega⟩
  rw [on_of_state 107 (7 + 4 * m + 2) true ((4) * (m : ℤ)) [-1, 1, 7, 9] (per m).2.2.1 (by decide) (by
    intro q hq
    have hq' := (show inBox (-1) (9) [-1, 1, 7, 9] by unfold inBox; decide) q hq
    constructor <;> omega)]
  simp

open OMA.S_oeis_a267159 in
lemma onC2 (t : ℕ) (h0 : 10 ≤ t) (hp : t % 4 = 2) : (onCount 107 t : ℤ) = 8 := by
  obtain ⟨m, rfl⟩ : ∃ m, t = 7 + 4 * m + 3 := ⟨(t - 10) / 4, by omega⟩
  rw [on_of_state 107 (7 + 4 * m + 3) false ((4) * (m : ℤ)) [-2, -1, 1, 2, 6, 7, 9, 10] (per m).2.2.2 (by decide) (by
    intro q hq
    have hq' := (show inBox (-2) (10) [-2, -1, 1, 2, 6, 7, 9, 10] by unfold inBox; decide) q hq
    constructor <;> omega)]
  simp

open OMA.S_oeis_a267159 in
lemma ov0 : (onCount 107 0 : ℤ) = 1 := by
  rw [on_of_state0 107 0 false [0] s0 (by decide) (by decide)]
  simp

open OMA.S_oeis_a267159 in
lemma ov1 : (onCount 107 1 : ℤ) = 1 := by
  rw [on_of_state0 107 1 true [0, 1] s1 (by decide) (by decide)]
  simp

open OMA.S_oeis_a267159 in
lemma ov2 : (onCount 107 2 : ℤ) = 3 := by
  rw [on_of_state0 107 2 false [-1, 1, 2] s2 (by decide) (by decide)]
  simp

open OMA.S_oeis_a267159 in
lemma ov3 : (onCount 107 3 : ℤ) = 5 := by
  rw [on_of_state0 107 3 true [-1, 3] s3 (by decide) (by decide)]
  simp

open OMA.S_oeis_a267159 in
lemma ov4 : (onCount 107 4 : ℤ) = 6 := by
  rw [on_of_state0 107 4 false [-2, -1, 0, 2, 3, 4] s4 (by decide) (by decide)]
  simp

open OMA.S_oeis_a267159 in
lemma ov5 : (onCount 107 5 : ℤ) = 8 := by
  rw [on_of_state0 107 5 true [-1, 3, 5] s5 (by decide) (by decide)]
  simp

open OMA.S_oeis_a267159 in
lemma ov6 : (onCount 107 6 : ℤ) = 7 := by
  rw [on_of_state0 107 6 false [-2, -1, 0, 2, 3, 5, 6] s6 (by decide) (by decide)]
  simp

open OMA.S_oeis_a267159 in
lemma ov7 : (onCount 107 7 : ℤ) = 13 :=
  (onC3 7 (by norm_num) (by norm_num)).trans (by norm_num)

open OMA.S_oeis_a267159 in
lemma ov8 : (onCount 107 8 : ℤ) = 6 :=
  (onC0 8 (by norm_num) (by norm_num)).trans (by norm_num)

open OMA.S_oeis_a267159 in
lemma ov9 : (onCount 107 9 : ℤ) = 15 :=
  (onC1 9 (by norm_num) (by norm_num)).trans (by norm_num)

open OMA.S_oeis_a267159 in
lemma ov10 : (onCount 107 10 : ℤ) = 8 :=
  (onC2 10 (by norm_num) (by norm_num)).trans (by norm_num)

open OMA.S_oeis_a267159 in
lemma ov11 : (onCount 107 11 : ℤ) = 21 :=
  (onC3 11 (by norm_num) (by norm_num)).trans (by norm_num)

open OMA.S_oeis_a267159 in
lemma ov12 : (onCount 107 12 : ℤ) = 6 :=
  (onC0 12 (by norm_num) (by norm_num)).trans (by norm_num)

open OMA.S_oeis_a267159 in
lemma ov13 : (onCount 107 13 : ℤ) = 23 :=
  (onC1 13 (by norm_num) (by norm_num)).trans (by norm_num)

open OMA.S_oeis_a267159 in
lemma ov14 : (onCount 107 14 : ℤ) = 8 :=
  (onC2 14 (by norm_num) (by norm_num)).trans (by norm_num)

open OMA.S_oeis_a267159 in
lemma a_succ (n : ℕ) : a (n + 1) = a n + (onCount 107 (n + 1) : ℤ) := by
  unfold a
  rw [Finset.sum_range_succ]

open OMA.S_oeis_a267159 in
lemma av0 : (a 0 : ℚ) = 1 := by
  unfold a
  rw [Finset.sum_range_one, ov0]
  norm_num

open OMA.S_oeis_a267159 in
lemma av1 : (a 1 : ℚ) = 2 := by
  rw [a_succ, Int.cast_add, av0, ov1]
  norm_num

open OMA.S_oeis_a267159 in
lemma av2 : (a 2 : ℚ) = 5 := by
  rw [a_succ, Int.cast_add, av1, ov2]
  norm_num

open OMA.S_oeis_a267159 in
lemma av3 : (a 3 : ℚ) = 10 := by
  rw [a_succ, Int.cast_add, av2, ov3]
  norm_num

open OMA.S_oeis_a267159 in
lemma av4 : (a 4 : ℚ) = 16 := by
  rw [a_succ, Int.cast_add, av3, ov4]
  norm_num

open OMA.S_oeis_a267159 in
lemma av5 : (a 5 : ℚ) = 24 := by
  rw [a_succ, Int.cast_add, av4, ov5]
  norm_num

open OMA.S_oeis_a267159 in
lemma av6 : (a 6 : ℚ) = 31 := by
  rw [a_succ, Int.cast_add, av5, ov6]
  norm_num

open OMA.S_oeis_a267159 in
lemma av7 : (a 7 : ℚ) = 44 := by
  rw [a_succ, Int.cast_add, av6, ov7]
  norm_num

open OMA.S_oeis_a267159 in
lemma av8 : (a 8 : ℚ) = 50 := by
  rw [a_succ, Int.cast_add, av7, ov8]
  norm_num

open OMA.S_oeis_a267159 in
lemma av9 : (a 9 : ℚ) = 65 := by
  rw [a_succ, Int.cast_add, av8, ov9]
  norm_num

open OMA.S_oeis_a267159 in
lemma av10 : (a 10 : ℚ) = 73 := by
  rw [a_succ, Int.cast_add, av9, ov10]
  norm_num

open OMA.S_oeis_a267159 in
lemma av11 : (a 11 : ℚ) = 94 := by
  rw [a_succ, Int.cast_add, av10, ov11]
  norm_num

open OMA.S_oeis_a267159 in
lemma av12 : (a 12 : ℚ) = 100 := by
  rw [a_succ, Int.cast_add, av11, ov12]
  norm_num

open OMA.S_oeis_a267159 in
lemma av13 : (a 13 : ℚ) = 123 := by
  rw [a_succ, Int.cast_add, av12, ov13]
  norm_num

open OMA.S_oeis_a267159 in
lemma a_closed (n : ℕ) (hn : 7 ≤ n) :
    (n % 4 = 0 → (a n : ℚ) = (0 : ℚ) * (n : ℚ) ^ 3 + (1 / 2 : ℚ) * (n : ℚ) ^ 2 + (5 / 2 : ℚ) * (n : ℚ) + (-2 : ℚ)) ∧
    (n % 4 = 1 → (a n : ℚ) = (0 : ℚ) * (n : ℚ) ^ 3 + (1 / 2 : ℚ) * (n : ℚ) ^ 2 + (7 / 2 : ℚ) * (n : ℚ) + (-7 : ℚ)) ∧
    (n % 4 = 2 → (a n : ℚ) = (0 : ℚ) * (n : ℚ) ^ 3 + (1 / 2 : ℚ) * (n : ℚ) ^ 2 + (5 / 2 : ℚ) * (n : ℚ) + (-2 : ℚ)) ∧
    (n % 4 = 3 → (a n : ℚ) = (0 : ℚ) * (n : ℚ) ^ 3 + (1 / 2 : ℚ) * (n : ℚ) ^ 2 + (7 / 2 : ℚ) * (n : ℚ) + (-5 : ℚ)) := by
  induction n, hn using Nat.le_induction with
  | base =>
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro h
      exfalso
      omega
    · intro h
      exfalso
      omega
    · intro h
      exfalso
      omega
    · intro h
      rw [av7]
      norm_num
  | succ n hn ih =>
    obtain ⟨ih0, ih1, ih2, ih3⟩ := ih
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro h
      have h' : n % 4 = 3 := by omega
      rw [a_succ, Int.cast_add, ih3 h', onC0 (n + 1) (by omega) (by omega)]
      push_cast
      ring
    · intro h
      have h' : n % 4 = 0 := by omega
      rw [a_succ, Int.cast_add, ih0 h', onC1 (n + 1) (by omega) (by omega)]
      push_cast
      ring
    · intro h
      have h' : n % 4 = 1 := by omega
      rw [a_succ, Int.cast_add, ih1 h', onC2 (n + 1) (by omega) (by omega)]
      push_cast
      ring
    · intro h
      have h' : n % 4 = 2 := by omega
      rw [a_succ, Int.cast_add, ih2 h', onC3 (n + 1) (by omega) (by omega)]
      push_cast
      ring

open OMA.S_oeis_a267159 in
lemma aC0 (n : ℕ) (h0 : 7 ≤ n) (hp : n % 4 = 0) : (a n : ℚ) = (0 : ℚ) * (n : ℚ) ^ 3 + (1 / 2 : ℚ) * (n : ℚ) ^ 2 + (5 / 2 : ℚ) * (n : ℚ) + (-2 : ℚ) :=
  (a_closed n h0).1 hp

open OMA.S_oeis_a267159 in
lemma aC1 (n : ℕ) (h0 : 7 ≤ n) (hp : n % 4 = 1) : (a n : ℚ) = (0 : ℚ) * (n : ℚ) ^ 3 + (1 / 2 : ℚ) * (n : ℚ) ^ 2 + (7 / 2 : ℚ) * (n : ℚ) + (-7 : ℚ) :=
  (a_closed n h0).2.1 hp

open OMA.S_oeis_a267159 in
lemma aC2 (n : ℕ) (h0 : 7 ≤ n) (hp : n % 4 = 2) : (a n : ℚ) = (0 : ℚ) * (n : ℚ) ^ 3 + (1 / 2 : ℚ) * (n : ℚ) ^ 2 + (5 / 2 : ℚ) * (n : ℚ) + (-2 : ℚ) :=
  (a_closed n h0).2.2.1 hp

open OMA.S_oeis_a267159 in
lemma aC3 (n : ℕ) (h0 : 7 ≤ n) (hp : n % 4 = 3) : (a n : ℚ) = (0 : ℚ) * (n : ℚ) ^ 3 + (1 / 2 : ℚ) * (n : ℚ) ^ 2 + (7 / 2 : ℚ) * (n : ℚ) + (-5 : ℚ) :=
  (a_closed n h0).2.2.2 hp

open OMA.S_oeis_a267159 in
lemma rec_gen (m : ℕ) : (1 : ℚ) * (a (m + 14) : ℚ) + (-1 : ℚ) * (a (m + 13) : ℚ) + (-1 : ℚ) * (a (m + 12) : ℚ) + (1 : ℚ) * (a (m + 11) : ℚ) + (-1 : ℚ) * (a (m + 10) : ℚ) + (1 : ℚ) * (a (m + 9) : ℚ) + (1 : ℚ) * (a (m + 8) : ℚ) + (-1 : ℚ) * (a (m + 7) : ℚ) = 0 := by
  rcases (show m % 4 = 0 ∨ m % 4 = 1 ∨ m % 4 = 2 ∨ m % 4 = 3 by omega) with h | h | h | h
  · rw [aC2 (m + 14) (by omega) (by omega),
      aC1 (m + 13) (by omega) (by omega),
      aC0 (m + 12) (by omega) (by omega),
      aC3 (m + 11) (by omega) (by omega),
      aC2 (m + 10) (by omega) (by omega),
      aC1 (m + 9) (by omega) (by omega),
      aC0 (m + 8) (by omega) (by omega),
      aC3 (m + 7) (by omega) (by omega)]
    push_cast
    ring
  · rw [aC3 (m + 14) (by omega) (by omega),
      aC2 (m + 13) (by omega) (by omega),
      aC1 (m + 12) (by omega) (by omega),
      aC0 (m + 11) (by omega) (by omega),
      aC3 (m + 10) (by omega) (by omega),
      aC2 (m + 9) (by omega) (by omega),
      aC1 (m + 8) (by omega) (by omega),
      aC0 (m + 7) (by omega) (by omega)]
    push_cast
    ring
  · rw [aC0 (m + 14) (by omega) (by omega),
      aC3 (m + 13) (by omega) (by omega),
      aC2 (m + 12) (by omega) (by omega),
      aC1 (m + 11) (by omega) (by omega),
      aC0 (m + 10) (by omega) (by omega),
      aC3 (m + 9) (by omega) (by omega),
      aC2 (m + 8) (by omega) (by omega),
      aC1 (m + 7) (by omega) (by omega)]
    push_cast
    ring
  · rw [aC1 (m + 14) (by omega) (by omega),
      aC0 (m + 13) (by omega) (by omega),
      aC3 (m + 12) (by omega) (by omega),
      aC2 (m + 11) (by omega) (by omega),
      aC1 (m + 10) (by omega) (by omega),
      aC0 (m + 9) (by omega) (by omega),
      aC3 (m + 8) (by omega) (by omega),
      aC2 (m + 7) (by omega) (by omega)]
    push_cast
    ring

open PowerSeries in
lemma coeff_term (f : ℕ → ℚ) (c : ℚ) (k n : ℕ) :
    coeff n (mk f * (C c * X ^ k)) = if k ≤ n then c * f (n - k) else 0 := by
  rw [← mul_assoc, mul_comm (mk f) (C c), mul_assoc, coeff_C_mul, coeff_mul_X_pow']
  split_ifs <;> simp [coeff_mk]

end A267159Aux

set_option maxHeartbeats 1600000 in
open OMA.S_oeis_a267159 A267159Aux PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a267159.main := by
  refine ⟨?_, ?_⟩
  · intro n hn
    rcases Nat.lt_or_ge n 14 with hs | hs
    · interval_cases n <;> norm_num [av0, av1, av2, av3, av4, av5, av6, av7, av8, av9, av10, av11, av12, av13]
    · obtain ⟨j, rfl⟩ : ∃ j, n = j + 7 := ⟨n - 7, by omega⟩
      rw [show j + 7 - 1 = j + 6 from by omega, show j + 7 - 2 = j + 5 from by omega, show j + 7 - 3 = j + 4 from by omega, show j + 7 - 4 = j + 3 from by omega, show j + 7 - 5 = j + 2 from by omega, show j + 7 - 6 = j + 1 from by omega, show j + 7 - 7 = j from by omega]
      rcases (show j % 4 = 0 ∨ j % 4 = 1 ∨ j % 4 = 2 ∨ j % 4 = 3 by omega) with h | h | h | h
      · rw [aC3 (j + 7) (by omega) (by omega), aC2 (j + 6) (by omega) (by omega), aC1 (j + 5) (by omega) (by omega), aC0 (j + 4) (by omega) (by omega), aC3 (j + 3) (by omega) (by omega), aC2 (j + 2) (by omega) (by omega), aC1 (j + 1) (by omega) (by omega), aC0 (j) (by omega) (by omega)]
        push_cast
        ring
      · rw [aC0 (j + 7) (by omega) (by omega), aC3 (j + 6) (by omega) (by omega), aC2 (j + 5) (by omega) (by omega), aC1 (j + 4) (by omega) (by omega), aC0 (j + 3) (by omega) (by omega), aC3 (j + 2) (by omega) (by omega), aC2 (j + 1) (by omega) (by omega), aC1 (j) (by omega) (by omega)]
        push_cast
        ring
      · rw [aC1 (j + 7) (by omega) (by omega), aC0 (j + 6) (by omega) (by omega), aC3 (j + 5) (by omega) (by omega), aC2 (j + 4) (by omega) (by omega), aC1 (j + 3) (by omega) (by omega), aC0 (j + 2) (by omega) (by omega), aC3 (j + 1) (by omega) (by omega), aC2 (j) (by omega) (by omega)]
        push_cast
        ring
      · rw [aC2 (j + 7) (by omega) (by omega), aC1 (j + 6) (by omega) (by omega), aC0 (j + 5) (by omega) (by omega), aC3 (j + 4) (by omega) (by omega), aC2 (j + 3) (by omega) (by omega), aC1 (j + 2) (by omega) (by omega), aC0 (j + 1) (by omega) (by omega), aC3 (j) (by omega) (by omega)]
        push_cast
        ring
  · have hD : (((1 - X) ^ 3 * (1 + X) ^ 2 * (1 + X ^ 2) : PowerSeries ℚ)) = C (1 : ℚ) * X ^ 0 + C (-1 : ℚ) * X ^ 1 + C (-1 : ℚ) * X ^ 2 + C (1 : ℚ) * X ^ 3 + C (-1 : ℚ) * X ^ 4 + C (1 : ℚ) * X ^ 5 + C (1 : ℚ) * X ^ 6 + C (-1 : ℚ) * X ^ 7 := by
      simp only [map_one, map_ofNat, map_neg]
      ring
    have hN : (1 + X + 2 * X ^ 2 + 4 * X ^ 3 + 2 * X ^ 4 + 2 * X ^ 5 - X ^ 6 + X ^ 7 - 4 * X ^ 8 - X ^ 9 + X ^ 10 + X ^ 11 - X ^ 12 : PowerSeries ℚ) = C (1 : ℚ) * X ^ 0 + C (1 : ℚ) * X ^ 1 + C (2 : ℚ) * X ^ 2 + C (4 : ℚ) * X ^ 3 + C (2 : ℚ) * X ^ 4 + C (2 : ℚ) * X ^ 5 + C (-1 : ℚ) * X ^ 6 + C (1 : ℚ) * X ^ 7 + C (-4 : ℚ) * X ^ 8 + C (-1 : ℚ) * X ^ 9 + C (1 : ℚ) * X ^ 10 + C (1 : ℚ) * X ^ 11 + C (-1 : ℚ) * X ^ 12 := by
      simp only [map_one, map_ofNat, map_neg]
      ring
    rw [hD, hN]
    ext n
    simp only [mul_add, map_add, coeff_term, PowerSeries.coeff_C_mul_X_pow]
    rcases Nat.lt_or_ge n 14 with hs | hs
    · interval_cases n <;> norm_num [av0, av1, av2, av3, av4, av5, av6, av7, av8, av9, av10, av11, av12, av13]
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 14 := ⟨n - 14, by omega⟩
      rw [if_pos (show 0 ≤ m + 14 by omega),
        if_pos (show 1 ≤ m + 14 by omega),
        if_pos (show 2 ≤ m + 14 by omega),
        if_pos (show 3 ≤ m + 14 by omega),
        if_pos (show 4 ≤ m + 14 by omega),
        if_pos (show 5 ≤ m + 14 by omega),
        if_pos (show 6 ≤ m + 14 by omega),
        if_pos (show 7 ≤ m + 14 by omega),
        if_neg (show ¬ (m + 14 = 0) by omega),
        if_neg (show ¬ (m + 14 = 1) by omega),
        if_neg (show ¬ (m + 14 = 2) by omega),
        if_neg (show ¬ (m + 14 = 3) by omega),
        if_neg (show ¬ (m + 14 = 4) by omega),
        if_neg (show ¬ (m + 14 = 5) by omega),
        if_neg (show ¬ (m + 14 = 6) by omega),
        if_neg (show ¬ (m + 14 = 7) by omega),
        if_neg (show ¬ (m + 14 = 8) by omega),
        if_neg (show ¬ (m + 14 = 9) by omega),
        if_neg (show ¬ (m + 14 = 10) by omega),
        if_neg (show ¬ (m + 14 = 11) by omega),
        if_neg (show ¬ (m + 14 = 12) by omega)]
      rw [show m + 14 - 1 = m + 13 from by omega,
        show m + 14 - 2 = m + 12 from by omega,
        show m + 14 - 3 = m + 11 from by omega,
        show m + 14 - 4 = m + 10 from by omega,
        show m + 14 - 5 = m + 9 from by omega,
        show m + 14 - 6 = m + 8 from by omega,
        show m + 14 - 7 = m + 7 from by omega]
      rw [show m + 14 - 0 = m + 14 from by omega]
      have hrec := rec_gen m
      linarith
