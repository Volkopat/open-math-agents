import OMAStatements.S_oeis_a270934
import Mathlib

namespace A270934Aux

def step (code : ℕ) (g : ℤ → ℤ → Bool) : ℤ → ℤ → Bool := fun i j =>
  code.testBit ((g i j).toNat + 2 * ((g (i + 1) j).toNat +
      (g (i - 1) j).toNat + (g i (j + 1)).toNat + (g i (j - 1)).toNat))

open OMA.S_oeis_a270934 in
lemma cell_succ (code t : ℕ) : cell code (t + 1) = step code (cell code t) := by
  funext i j
  rw [cell]
  rfl

def pat (s : Bool) (L : List (ℤ × ℤ)) : ℤ → ℤ → Bool :=
  fun x y => if (x, y) ∈ L then !s else s

def inBox (L : List (ℤ × ℤ)) : Prop := ∀ p ∈ L, -2 ≤ p.1 ∧ p.1 ≤ 2 ∧ -2 ≤ p.2 ∧ p.2 ≤ 2

lemma pat_far (s : Bool) (L : List (ℤ × ℤ)) (hL : inBox L) (u v : ℤ)
    (h : ¬(-2 ≤ u ∧ u ≤ 2 ∧ -2 ≤ v ∧ v ≤ 2)) : pat s L u v = s := by
  unfold pat
  have hm : (u, v) ∉ L := fun hm => h (hL _ hm)
  simp [hm]

def five : List ℤ := [-3, -2, -1, 0, 1, 2, 3]

lemma mem_five (x : ℤ) (h1 : -3 ≤ x) (h2 : x ≤ 3) : x ∈ five := by
  unfold five
  simp
  omega

lemma step_pat (code : ℕ) (s s' : Bool) (L L' : List (ℤ × ℤ)) (hL : inBox L) (hL' : inBox L')
    (hr : code.testBit (s.toNat + 2 * (s.toNat + s.toNat + s.toNat + s.toNat)) = s')
    (hbox : ∀ x ∈ five, ∀ y ∈ five, step code (pat s L) x y = pat s' L' x y) :
    step code (pat s L) = pat s' L' := by
  funext x y
  by_cases h : (-3 ≤ x ∧ x ≤ 3) ∧ (-3 ≤ y ∧ y ≤ 3)
  · exact hbox x (mem_five x h.1.1 h.1.2) y (mem_five y h.2.1 h.2.2)
  · rw [pat_far s' L' hL' x y (by omega)]
    unfold step
    rw [pat_far s L hL x y (by omega), pat_far s L hL (x + 1) y (by omega),
      pat_far s L hL (x - 1) y (by omega), pat_far s L hL x (y + 1) (by omega),
      pat_far s L hL x (y - 1) (by omega)]
    exact hr

open OMA.S_oeis_a270934 in
lemma cell_zero (code : ℕ) : cell code 0 = pat false [(0, 0)] := by
  funext i j
  rw [cell]
  unfold pat
  by_cases h : i = 0 ∧ j = 0
  · obtain ⟨rfl, rfl⟩ := h
    simp
  · have : (i, j) ∉ [((0 : ℤ), (0 : ℤ))] := by
      simp only [List.mem_singleton, Prod.mk.injEq]
      exact h
    simp [h]

lemma single_count (p : ℤ × ℤ) (t : ℕ)
    (hp : -(t : ℤ) ≤ p.1 ∧ p.1 ≤ t ∧ -(t : ℤ) ≤ p.2 ∧ p.2 ≤ t) :
    (∑ i ∈ Finset.range (2 * t + 1), ∑ j ∈ Finset.range (2 * t + 1),
      if (((i : ℤ) - t, (j : ℤ) - t) = p) then (1 : ℤ) else 0) = 1 := by
  obtain ⟨a, b⟩ := p
  simp only at hp
  have hi0 : (a + t).toNat < 2 * t + 1 := by omega
  have hj0 : (b + t).toNat < 2 * t + 1 := by omega
  have h1 : ∀ i ∈ Finset.range (2 * t + 1), (∑ j ∈ Finset.range (2 * t + 1),
      if (((i : ℤ) - t, (j : ℤ) - t) = (a, b)) then (1 : ℤ) else 0) =
      if i = (a + t).toNat then 1 else 0 := by
    intro i _
    have h2 : ∀ j : ℕ, (((i : ℤ) - t, (j : ℤ) - t) = (a, b)) ↔
        (j = (b + t).toNat ∧ i = (a + t).toNat) := by
      intro j
      simp only [Prod.mk.injEq]
      omega
    simp only [h2]
    by_cases hi : i = (a + t).toNat
    · simp [hi, hj0]
    · simp [hi]
  rw [Finset.sum_congr rfl h1]
  simp [hi0]

def memCount (L : List (ℤ × ℤ)) (t : ℕ) : ℤ :=
  ∑ i ∈ Finset.range (2 * t + 1), ∑ j ∈ Finset.range (2 * t + 1),
    if (((i : ℤ) - t, (j : ℤ) - t) ∈ L) then (1 : ℤ) else 0

lemma memCount_eq (t : ℕ) (ht : 2 ≤ t) (L : List (ℤ × ℤ)) (hnd : L.Nodup) (hin : inBox L) :
    memCount L t = L.length := by
  induction L with
  | nil => simp [memCount]
  | cons p L ih =>
    have hp : p ∉ L := (List.nodup_cons.mp hnd).1
    have hin' : inBox L := fun q hq => hin q (List.mem_cons_of_mem _ hq)
    have hpb := hin p List.mem_cons_self
    have key : ∀ i j : ℕ, (if (((i : ℤ) - t, (j : ℤ) - t) ∈ p :: L) then (1 : ℤ) else 0) =
        (if (((i : ℤ) - t, (j : ℤ) - t) = p) then (1 : ℤ) else 0) +
        (if (((i : ℤ) - t, (j : ℤ) - t) ∈ L) then (1 : ℤ) else 0) := by
      intro i j
      by_cases h1 : ((i : ℤ) - t, (j : ℤ) - t) = p
      · have h2 : ((i : ℤ) - t, (j : ℤ) - t) ∉ L := by rw [h1]; exact hp
        simp [h1, hp]
      · simp [h1]
    have e : memCount (p :: L) t = 1 + memCount L t := by
      unfold memCount
      simp only [key, Finset.sum_add_distrib]
      rw [single_count p t (by omega)]
    rw [e, ih (List.nodup_cons.mp hnd).2 hin']
    simp
    ring

open OMA.S_oeis_a270934 in
lemma count_true (code t : ℕ) (ht : 2 ≤ t) (L : List (ℤ × ℤ)) (hnd : L.Nodup) (hin : inBox L)
    (h : cell code t = pat true L) :
    ((onCount code t : ℕ) : ℤ) = (2 * (t : ℤ) + 1) ^ 2 - L.length := by
  unfold onCount
  rw [h, ← memCount_eq t ht L hnd hin]
  unfold memCount
  push_cast
  have key : ∀ i j : ℕ, (if pat true L ((i : ℤ) - t) ((j : ℤ) - t) = true then (1 : ℤ) else 0) =
      1 - (if (((i : ℤ) - t, (j : ℤ) - t) ∈ L) then (1 : ℤ) else 0) := by
    intro i j
    unfold pat
    by_cases h1 : ((i : ℤ) - t, (j : ℤ) - t) ∈ L
    · simp [h1]
    · simp [h1]
  simp only [key, Finset.sum_sub_distrib]
  simp
  ring

open OMA.S_oeis_a270934 in
lemma count_false (code t : ℕ) (ht : 2 ≤ t) (L : List (ℤ × ℤ)) (hnd : L.Nodup) (hin : inBox L)
    (h : cell code t = pat false L) :
    ((onCount code t : ℕ) : ℤ) = L.length := by
  unfold onCount
  rw [h, ← memCount_eq t ht L hnd hin]
  unfold memCount
  push_cast
  have key : ∀ i j : ℕ, (if pat false L ((i : ℤ) - t) ((j : ℤ) - t) = true then (1 : ℤ) else 0) =
      (if (((i : ℤ) - t, (j : ℤ) - t) ∈ L) then (1 : ℤ) else 0) := by
    intro i j
    unfold pat
    by_cases h1 : ((i : ℤ) - t, (j : ℤ) - t) ∈ L
    · simp [h1]
    · simp [h1]
  simp only [key]


open OMA.S_oeis_a270934 in
lemma s0 : cell 221 0 = pat false [(0, 0)] := cell_zero 221

open OMA.S_oeis_a270934 in
lemma s1 : cell 221 1 = pat true [(0, 0)] := by
  rw [show (1 : ℕ) = 0 + 1 from rfl, cell_succ, s0]
  exact step_pat 221 false true _ _ (by unfold inBox; decide) (by unfold inBox; decide) (by decide) (by decide)

open OMA.S_oeis_a270934 in
lemma s2 : cell 221 2 = pat false [(-1, 0), (0, -1), (0, 1), (1, 0)] := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, cell_succ, s1]
  exact step_pat 221 true false _ _ (by unfold inBox; decide) (by unfold inBox; decide) (by decide) (by decide)

open OMA.S_oeis_a270934 in
lemma s3 : cell 221 3 = pat true [(-1, 0), (0, -1), (0, 0), (0, 1), (1, 0)] := by
  rw [show (3 : ℕ) = 2 + 1 from rfl, cell_succ, s2]
  exact step_pat 221 false true _ _ (by unfold inBox; decide) (by unfold inBox; decide) (by decide) (by decide)

open OMA.S_oeis_a270934 in
lemma s4 : cell 221 4 = pat false [(-2, 0), (-1, 0), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, 0), (2, 0)] := by
  rw [show (4 : ℕ) = 3 + 1 from rfl, cell_succ, s3]
  exact step_pat 221 true false _ _ (by unfold inBox; decide) (by unfold inBox; decide) (by decide) (by decide)

open OMA.S_oeis_a270934 in
lemma sper (k : ℕ) : cell 221 (2 * k + 3) = pat true [(-1, 0), (0, -1), (0, 0), (0, 1), (1, 0)] ∧
    cell 221 (2 * k + 4) = pat false [(-2, 0), (-1, 0), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, 0), (2, 0)] := by
  induction k with
  | zero => exact ⟨s3, s4⟩
  | succ k ih =>
    have h1 : cell 221 (2 * (k + 1) + 3) = pat true [(-1, 0), (0, -1), (0, 0), (0, 1), (1, 0)] := by
      rw [show 2 * (k + 1) + 3 = (2 * k + 4) + 1 by ring, cell_succ, ih.2]
      exact step_pat 221 false true _ _ (by unfold inBox; decide) (by unfold inBox; decide) (by decide) (by decide)
    refine ⟨h1, ?_⟩
    rw [show 2 * (k + 1) + 4 = (2 * (k + 1) + 3) + 1 by ring, cell_succ, h1]
    exact step_pat 221 true false _ _ (by unfold inBox; decide) (by unfold inBox; decide) (by decide) (by decide)

open OMA.S_oeis_a270934 in
lemma on_big (n : ℕ) (hn : 3 ≤ n) :
    ((onCount 221 n : ℕ) : ℚ) = ((1 / 2 : ℚ) + ((-1) / 2 : ℚ) * (-1 : ℚ) ^ n) * (2 * (n : ℚ) + 1) ^ 2
      + ((2 / 1 : ℚ) + (7 / 1 : ℚ) * (-1 : ℚ) ^ n) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' m
  · have h := count_true 221 (2 * k + 3) (by omega) _ (by decide) (by unfold inBox; decide) (sper k).1
    have h' : ((onCount 221 (2 * k + 3) : ℕ) : ℚ) = (2 * ((2 * k + 3 : ℕ) : ℚ) + 1) ^ 2 - 5 := by
      have h2 : ((onCount 221 (2 * k + 3) : ℕ) : ℤ) = (2 * ((2 * k + 3 : ℕ) : ℤ) + 1) ^ 2 - 5 := by
        rw [h]; norm_num
      exact_mod_cast h2
    have e : (-1 : ℚ) ^ (2 * k + 3) = -1 := by rw [pow_add, pow_mul]; norm_num
    rw [h', e]
    push_cast
    ring
  · rw [show 2 * k + 1 + 3 = 2 * k + 4 by ring]
    have h := count_false 221 (2 * k + 4) (by omega) _ (by decide) (by unfold inBox; decide) (sper k).2
    have h' : ((onCount 221 (2 * k + 4) : ℕ) : ℚ) = 9 := by
      have h2 : ((onCount 221 (2 * k + 4) : ℕ) : ℤ) = 9 := by
        rw [h]; norm_num
      exact_mod_cast h2
    have e : (-1 : ℚ) ^ (2 * k + 4) = 1 := by rw [pow_add, pow_mul]; norm_num
    rw [h', e]
    push_cast
    ring

open OMA.S_oeis_a270934 in
lemma on_0 : ((onCount 221 0 : ℕ) : ℚ) = 1 := by
  have h : onCount 221 0 = 1 := by decide
  rw [h]; norm_num

open OMA.S_oeis_a270934 in
lemma on_1 : ((onCount 221 1 : ℕ) : ℚ) = 8 := by
  have h : onCount 221 1 = 8 := by decide
  rw [h]; norm_num

open OMA.S_oeis_a270934 in
lemma on_2 : ((onCount 221 2 : ℕ) : ℚ) = 4 := by
  have h2 : ((onCount 221 2 : ℕ) : ℤ) = 4 := by
    rw [count_false 221 2 (by norm_num) _ (by decide) (by unfold inBox; decide) s2]; norm_num
  exact_mod_cast h2

open OMA.S_oeis_a270934 in
lemma on_3 : ((onCount 221 3 : ℕ) : ℚ) = 44 := by
  rw [on_big 3 (by norm_num)]; norm_num

open OMA.S_oeis_a270934 in
lemma on_4 : ((onCount 221 4 : ℕ) : ℚ) = 9 := by
  rw [on_big 4 (by norm_num)]; norm_num

open OMA.S_oeis_a270934 in
lemma on_5 : ((onCount 221 5 : ℕ) : ℚ) = 116 := by
  rw [on_big 5 (by norm_num)]; norm_num

open OMA.S_oeis_a270934 in
lemma on_6 : ((onCount 221 6 : ℕ) : ℚ) = 9 := by
  rw [on_big 6 (by norm_num)]; norm_num

open OMA.S_oeis_a270934 in
lemma on_7 : ((onCount 221 7 : ℕ) : ℚ) = 220 := by
  rw [on_big 7 (by norm_num)]; norm_num

open OMA.S_oeis_a270934 in
lemma on_8 : ((onCount 221 8 : ℕ) : ℚ) = 9 := by
  rw [on_big 8 (by norm_num)]; norm_num

open OMA.S_oeis_a270934 in
lemma on_9 : ((onCount 221 9 : ℕ) : ℚ) = 356 := by
  rw [on_big 9 (by norm_num)]; norm_num

open OMA.S_oeis_a270934 in
lemma on_10 : ((onCount 221 10 : ℕ) : ℚ) = 9 := by
  rw [on_big 10 (by norm_num)]; norm_num

open OMA.S_oeis_a270934 in
lemma a_q (n : ℕ) : (a n : ℚ) = ((onCount 221 n : ℕ) : ℚ) := by
  unfold a
  push_cast
  rfl

open OMA.S_oeis_a270934 in
lemma a_0 : (a 0 : ℚ) = 1 := by
  rw [a_q, on_0]

open OMA.S_oeis_a270934 in
lemma a_1 : (a 1 : ℚ) = 8 := by
  rw [a_q, on_1]

open OMA.S_oeis_a270934 in
lemma a_2 : (a 2 : ℚ) = 4 := by
  rw [a_q, on_2]

open OMA.S_oeis_a270934 in
lemma a_3 : (a 3 : ℚ) = 44 := by
  rw [a_q, on_3]

open OMA.S_oeis_a270934 in
lemma a_4 : (a 4 : ℚ) = 9 := by
  rw [a_q, on_4]

open OMA.S_oeis_a270934 in
lemma a_5 : (a 5 : ℚ) = 116 := by
  rw [a_q, on_5]

open OMA.S_oeis_a270934 in
lemma a_6 : (a 6 : ℚ) = 9 := by
  rw [a_q, on_6]

open OMA.S_oeis_a270934 in
lemma a_7 : (a 7 : ℚ) = 220 := by
  rw [a_q, on_7]

open OMA.S_oeis_a270934 in
lemma a_8 : (a 8 : ℚ) = 9 := by
  rw [a_q, on_8]

open OMA.S_oeis_a270934 in
lemma a_9 : (a 9 : ℚ) = 356 := by
  rw [a_q, on_9]

open OMA.S_oeis_a270934 in
lemma a_cl (n : ℕ) (hn : 3 ≤ n) : (a n : ℚ) = (5 + 13 * (-1 : ℚ) ^ n - 4 * (-1 + (-1 : ℚ) ^ n) * (n : ℚ) - 4 * (-1 + (-1 : ℚ) ^ n) * (n : ℚ) ^ 2) / 2 := by
  have hge : 3 ≤ n := hn
  rw [a_q, on_big n (by omega)]
  ring

open PowerSeries in
lemma coeff_term (f : ℕ → ℚ) (c : ℚ) (k n : ℕ) :
    coeff n (mk f * (C c * X ^ k)) = if k ≤ n then c * f (n - k) else 0 := by
  rw [← mul_assoc, mul_comm (mk f) (C c), mul_assoc, coeff_C_mul, coeff_mul_X_pow']
  split_ifs <;> simp [coeff_mk]

end A270934Aux

set_option maxHeartbeats 1600000 in
open OMA.S_oeis_a270934 A270934Aux in
theorem OMA.solution : type_of% @OMA.S_oeis_a270934.main := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro n hn
    refine (a_cl n (by omega)).trans ?_
    ring
  · intro n hn hp
    refine (a_cl n (by omega)).trans ?_
    try rw [Even.neg_one_pow hp]
    ring
  · intro n hn hp
    refine (a_cl n (by omega)).trans ?_
    try rw [Odd.neg_one_pow hp]
    ring
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 9 := ⟨n - 9, by omega⟩
    simp only [show m + 9 - 2 = m + 7 by omega, show m + 9 - 4 = m + 5 by omega, show m + 9 - 6 = m + 3 by omega]
    rw [a_cl (m + 9) (by omega), a_cl (m + 7) (by omega), a_cl (m + 5) (by omega), a_cl (m + 3) (by omega)]
    push_cast
    ring
  · have hD : ((1 - PowerSeries.X) ^ 3 * (1 + PowerSeries.X) ^ 3 : PowerSeries ℚ) =
        PowerSeries.C 1 * PowerSeries.X ^ 0 + PowerSeries.C (-3) * PowerSeries.X ^ 2 + PowerSeries.C 3 * PowerSeries.X ^ 4 + PowerSeries.C (-1) * PowerSeries.X ^ 6 := by
      simp only [map_one, map_ofNat, map_neg]; ring
    have hN : (1 + 8 * PowerSeries.X + PowerSeries.X ^ 2 + 20 * PowerSeries.X ^ 3 + 8 * PowerSeries.X ^ 5 - 7 * PowerSeries.X ^ 6 - 4 * PowerSeries.X ^ 7 + 5 * PowerSeries.X ^ 8 : PowerSeries ℚ) =
        PowerSeries.C 1 * PowerSeries.X ^ 0 + PowerSeries.C 8 * PowerSeries.X ^ 1 + PowerSeries.C 1 * PowerSeries.X ^ 2 + PowerSeries.C 20 * PowerSeries.X ^ 3 + PowerSeries.C 8 * PowerSeries.X ^ 5 + PowerSeries.C (-7) * PowerSeries.X ^ 6 + PowerSeries.C (-4) * PowerSeries.X ^ 7 + PowerSeries.C 5 * PowerSeries.X ^ 8 := by
      simp only [map_one, map_ofNat, map_neg]; ring
    rw [hD, hN]
    ext n
    simp only [mul_add, map_add, coeff_term, PowerSeries.coeff_C_mul_X_pow]
    rcases n with _ | _ | _ | _ | _ | _ | _ | _ | _ | n
    · simp [a_0] <;> norm_num
    · simp [a_0, a_1] <;> norm_num
    · simp [a_0, a_1, a_2] <;> norm_num
    · simp [a_0, a_1, a_2, a_3] <;> norm_num
    · simp [a_0, a_1, a_2, a_3, a_4] <;> norm_num
    · simp [a_0, a_1, a_2, a_3, a_4, a_5] <;> norm_num
    · simp [a_0, a_1, a_2, a_3, a_4, a_5, a_6] <;> norm_num
    · simp [a_1, a_2, a_3, a_4, a_5, a_6, a_7] <;> norm_num
    · simp [a_2, a_3, a_4, a_5, a_6, a_7, a_8] <;> norm_num
    · have f0 := a_cl (n + 9) (by omega)
      have f2 := a_cl (n + 7) (by omega)
      have f4 := a_cl (n + 5) (by omega)
      have f6 := a_cl (n + 3) (by omega)
      simp [f0, f2, f4, f6]
      ring
