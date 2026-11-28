import OMAStatements.S_oeis_a267352
import Mathlib

namespace CAOEISA267352Aux


def pat (b : Bool) (L : List ℤ) : ℤ → Bool := fun i => if i ∈ L then !b else b

def inBox (L : List ℤ) : Prop := ∀ p ∈ L, -2 ≤ p ∧ p ≤ 2

lemma pat_far (b : Bool) (L : List ℤ) (hL : inBox L) (u : ℤ)
    (h : ¬(-2 ≤ u ∧ u ≤ 2)) : pat b L u = b := by
  unfold pat
  have hm : u ∉ L := fun hm => h (hL _ hm)
  simp [hm]

def seven : List ℤ := [-3, -2, -1, 0, 1, 2, 3]

lemma mem_seven (x : ℤ) (h1 : -3 ≤ x) (h2 : x ≤ 3) : x ∈ seven := by
  unfold seven
  simp
  omega

open OMA.S_oeis_a267352 in
def nxt (code : ℕ) (g : ℤ → Bool) : ℤ → Bool := fun i =>
  ruleOut code (g (i - 1)) (g i) (g (i + 1))

open OMA.S_oeis_a267352 in
lemma cell_succ (code t : ℕ) : cell code (t + 1) = nxt code (cell code t) := by
  funext i
  rw [cell]
  rfl

open OMA.S_oeis_a267352 in
lemma cell_zero (code : ℕ) : cell code 0 = pat false [0] := by
  funext i
  unfold pat
  rw [cell]
  by_cases h : i = 0
  · simp [h]
  · simp [h]

open OMA.S_oeis_a267352 in
lemma step_pat (code : ℕ) (b b' : Bool) (L L' : List ℤ) (hL : inBox L) (hL' : inBox L')
    (hr : ruleOut code b b b = b')
    (hbox : ∀ x ∈ seven, nxt code (pat b L) x = pat b' L' x) :
    nxt code (pat b L) = pat b' L' := by
  funext x
  by_cases h : (-3 ≤ x ∧ x ≤ 3)
  · exact hbox x (mem_seven x h.1 h.2)
  · rw [pat_far b' L' hL' x (by omega)]
    unfold nxt
    rw [pat_far b L hL x (by omega), pat_far b L hL (x + 1) (by omega),
      pat_far b L hL (x - 1) (by omega)]
    exact hr

lemma count_single (t : ℕ) (p : ℤ) (h : -(t : ℤ) ≤ p ∧ p ≤ t) :
    ∑ i ∈ Finset.range (2 * t + 1), (if ((i : ℤ) - t = p) then 1 else 0) = 1 := by
  have e1 : (((p + t).toNat : ℕ) : ℤ) = p + t := Int.toNat_of_nonneg (by omega)
  rw [Finset.sum_eq_single (p + t).toNat]
  · rw [if_pos]
    rw [e1]
    ring
  · intro i _ hi
    rw [if_neg]
    intro heq
    apply hi
    omega
  · intro hn
    exfalso
    apply hn
    rw [Finset.mem_range]
    omega

lemma count_mem (t : ℕ) (L : List ℤ) (hn : L.Nodup)
    (hb : ∀ p ∈ L, -(t : ℤ) ≤ p ∧ p ≤ t) :
    ∑ i ∈ Finset.range (2 * t + 1), (if ((i : ℤ) - t ∈ L) then 1 else 0) = L.length := by
  induction L with
  | nil => simp
  | cons p L ih =>
    have hp : p ∉ L := (List.nodup_cons.mp hn).1
    have hn' : L.Nodup := (List.nodup_cons.mp hn).2
    have e : ∀ i : ℕ, (if ((i : ℤ) - t ∈ p :: L) then 1 else 0) =
        (if ((i : ℤ) - t = p) then 1 else 0) + (if ((i : ℤ) - t ∈ L) then 1 else 0) := by
      intro i
      by_cases h1 : (i : ℤ) - t = p
      · have h2 : (i : ℤ) - t ∉ L := by rw [h1]; exact hp
        rw [if_pos (by rw [h1]; exact List.mem_cons_self), if_pos h1, if_neg h2]
      · by_cases h3 : (i : ℤ) - t ∈ L
        · rw [if_pos (List.mem_cons_of_mem _ h3), if_neg h1, if_pos h3]
        · rw [if_neg (by
            intro hm
            rcases List.mem_cons.mp hm with h4 | h4
            · exact h1 h4
            · exact h3 h4), if_neg h1, if_neg h3]
    simp only [e, Finset.sum_add_distrib]
    rw [count_single t p (hb p List.mem_cons_self),
      ih hn' (fun q hq => hb q (List.mem_cons_of_mem _ hq))]
    simp [add_comm]

open OMA.S_oeis_a267352 in
lemma onCount_false (code t : ℕ) (L : List ℤ) (c : ℕ) (hc : L.length = c) (hn : L.Nodup)
    (hb : ∀ p ∈ L, -(t : ℤ) ≤ p ∧ p ≤ t)
    (h : cell code t = pat false L) : onCount code t = c := by
  unfold onCount
  rw [h, ← hc, ← count_mem t L hn hb]
  apply Finset.sum_congr rfl
  intro i _
  unfold pat
  by_cases hm : (i : ℤ) - t ∈ L <;> simp [hm]

open OMA.S_oeis_a267352 in
lemma onCount_true (code t : ℕ) (L : List ℤ) (c : ℕ) (hc : L.length = c) (hn : L.Nodup)
    (hb : ∀ p ∈ L, -(t : ℤ) ≤ p ∧ p ≤ t)
    (h : cell code t = pat true L) : onCount code t + c = 2 * t + 1 := by
  unfold onCount
  rw [h, ← hc, ← count_mem t L hn hb, ← Finset.sum_add_distrib]
  have e2 : ∀ i ∈ Finset.range (2 * t + 1),
      ((if pat true L ((i : ℤ) - t) = true then 1 else 0)
        + (if ((i : ℤ) - t ∈ L) then 1 else 0) : ℕ) = 1 := by
    intro i _
    unfold pat
    by_cases hm : (i : ℤ) - t ∈ L <;> simp [hm]
  rw [Finset.sum_congr rfl e2]
  simp


open PowerSeries in
lemma coeff_term (f : ℕ → ℚ) (c : ℚ) (k n : ℕ) :
    coeff n (mk f * (C c * X ^ k)) = if k ≤ n then c * f (n - k) else 0 := by
  rw [← mul_assoc, mul_comm (mk f) (C c), mul_assoc, coeff_C_mul, coeff_mul_X_pow']
  split_ifs <;> simp [coeff_mk]

open OMA.S_oeis_a267352 in
lemma st0 : cell 123 0 = pat false [0] := cell_zero 123

open OMA.S_oeis_a267352 in
lemma st1 : cell 123 1 = pat true [0] := by
  rw [show (1 : ℕ) = 0 + 1 from rfl, cell_succ, st0]
  exact step_pat 123 false true [0] [0] (by unfold inBox; decide) (by unfold inBox; decide) (by decide) (by decide)

open OMA.S_oeis_a267352 in
lemma st2 : cell 123 2 = pat false [-1, 0, 1] := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, cell_succ, st1]
  exact step_pat 123 true false [0] [-1, 0, 1] (by unfold inBox; decide) (by unfold inBox; decide) (by decide) (by decide)

open OMA.S_oeis_a267352 in
lemma st3 : cell 123 3 = pat true [0] := by
  rw [show (3 : ℕ) = 2 + 1 from rfl, cell_succ, st2]
  exact step_pat 123 false true [-1, 0, 1] [0] (by unfold inBox; decide) (by unfold inBox; decide) (by decide) (by decide)

lemma stepAB : nxt 123 (pat false [-1, 0, 1]) = pat true [0] :=
  step_pat 123 false true [-1, 0, 1] [0] (by unfold inBox; decide) (by unfold inBox; decide) (by decide) (by decide)

lemma stepBA : nxt 123 (pat true [0]) = pat false [-1, 0, 1] :=
  step_pat 123 true false [0] [-1, 0, 1] (by unfold inBox; decide) (by unfold inBox; decide) (by decide) (by decide)

open OMA.S_oeis_a267352 in
lemma stP (m : ℕ) : cell 123 (2 + 2 * m) = pat false [-1, 0, 1] ∧
    cell 123 (2 + 2 * m + 1) = pat true [0] := by
  induction m with
  | zero => exact ⟨st2, st3⟩
  | succ k ih =>
    have h1 : cell 123 (2 + 2 * (k + 1)) = pat false [-1, 0, 1] := by
      rw [show 2 + 2 * (k + 1) = (2 + 2 * k + 1) + 1 from by ring, cell_succ, ih.2]
      exact stepBA
    refine ⟨h1, ?_⟩
    rw [cell_succ, h1]
    exact stepAB

open OMA.S_oeis_a267352 in
lemma oc0 : onCount 123 0 = 1 :=
  onCount_false 123 0 _ 1 rfl (by decide) (by decide) st0

open OMA.S_oeis_a267352 in
lemma oc1 : onCount 123 1 = 2 := by
  have h := onCount_true 123 1 _ 1 rfl (by decide) (by decide) st1
  omega

open OMA.S_oeis_a267352 in
lemma oc2 : onCount 123 2 = 3 :=
  onCount_false 123 2 _ 3 rfl (by decide) (by decide) st2

open OMA.S_oeis_a267352 in
lemma oc3 : onCount 123 3 = 6 := by
  have h := onCount_true 123 3 _ 1 rfl (by decide) (by decide) st3
  omega

lemma hLE : inBox [-1, 0, 1] := by unfold inBox; decide

open OMA.S_oeis_a267352 in
lemma ocE (m : ℕ) : (onCount 123 (2 + 2 * m) : ℤ) = 3 := by
  have h := onCount_false 123 (2 + 2 * m) _ 3 rfl (by decide) (fun p hp => by have h := hLE p hp; omega) (stP m).1
  rw [h]
  norm_num

lemma hLO : inBox [0] := by unfold inBox; decide

open OMA.S_oeis_a267352 in
lemma ocO (m : ℕ) : (onCount 123 (2 + 2 * m + 1) : ℤ) = (2 * (2 + 2 * (m : ℤ) + 1) + 1) - 1 := by
  have h := onCount_true 123 (2 + 2 * m + 1) _ 1 rfl (by decide) (fun p hp => by have h := hLO p hp; omega) (stP m).2
  have h' : ((onCount 123 (2 + 2 * m + 1) : ℕ) : ℤ) + 1 = (2 * (2 + 2 * (m : ℤ) + 1) + 1) := by exact_mod_cast h
  linarith

open OMA.S_oeis_a267352 in
lemma oc_eq (n : ℕ) (hn : 2 ≤ n) : (onCount 123 n : ℚ) = (((3 : ℚ) / 2) + (1 : ℚ) * (n : ℚ)) + (-1 : ℚ) ^ n * (((3 : ℚ) / 2) + (-1 : ℚ) * (n : ℚ)) := by
  obtain ⟨m, rfl | rfl⟩ : ∃ m, n = 2 + 2 * m ∨ n = 2 + 2 * m + 1 := ⟨(n - 2) / 2, by omega⟩
  · have hs : (-1 : ℚ) ^ (2 + 2 * m) = 1 := Even.neg_one_pow ⟨1 + m, by ring⟩
    have h := ocE m
    have h' : ((onCount 123 (2 + 2 * m) : ℕ) : ℚ) = (((onCount 123 (2 + 2 * m) : ℕ) : ℤ) : ℚ) := by norm_cast
    rw [h', h, hs]
    push_cast
    ring
  · have hs : (-1 : ℚ) ^ (2 + 2 * m + 1) = -1 := Odd.neg_one_pow ⟨1 + m, by ring⟩
    have h := ocO m
    have h' : ((onCount 123 (2 + 2 * m + 1) : ℕ) : ℚ) = (((onCount 123 (2 + 2 * m + 1) : ℕ) : ℤ) : ℚ) := by norm_cast
    rw [h', h, hs]
    push_cast
    ring

open OMA.S_oeis_a267352 in
lemma a_eq (n : ℕ) (hn : 2 ≤ n) : (a n : ℚ) = (((3 : ℚ) / 2) + (1 : ℚ) * (n : ℚ)) + (-1 : ℚ) ^ n * (((3 : ℚ) / 2) + (-1 : ℚ) * (n : ℚ)) := by
  unfold a
  push_cast
  rw [oc_eq n hn]
  try ring

open OMA.S_oeis_a267352 in
lemma av0 : (a 0 : ℚ) = 1 := by
  norm_num [a, Finset.sum_range_succ, oc0, oc1, oc2, oc3]

open OMA.S_oeis_a267352 in
lemma av1 : (a 1 : ℚ) = 2 := by
  norm_num [a, Finset.sum_range_succ, oc0, oc1, oc2, oc3]

open OMA.S_oeis_a267352 in
lemma av2 : (a 2 : ℚ) = 3 := by
  rw [a_eq 2 (by norm_num)]
  norm_num

open OMA.S_oeis_a267352 in
lemma av3 : (a 3 : ℚ) = 6 := by
  rw [a_eq 3 (by norm_num)]
  norm_num

open OMA.S_oeis_a267352 in
lemma av4 : (a 4 : ℚ) = 3 := by
  rw [a_eq 4 (by norm_num)]
  norm_num

open OMA.S_oeis_a267352 in
lemma av5 : (a 5 : ℚ) = 10 := by
  rw [a_eq 5 (by norm_num)]
  norm_num

open OMA.S_oeis_a267352 in
lemma av6 : (a 6 : ℚ) = 3 := by
  rw [a_eq 6 (by norm_num)]
  norm_num

end CAOEISA267352Aux

set_option maxHeartbeats 1600000 in
open OMA.S_oeis_a267352 CAOEISA267352Aux in
theorem OMA.solution : type_of% @OMA.S_oeis_a267352.main := by
  refine ⟨?_, ?_, ?_⟩
  · intro n hn
    rcases Nat.lt_or_ge n 2 with h | h
    · interval_cases n
      · rw [av1]
        norm_num
    · rw [a_eq n h]
      ring
  · intro n hn
    rcases Nat.lt_or_ge n 6 with h | h
    · interval_cases n
      · norm_num [av1, av3, av5]
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 6 := ⟨n - 6, by omega⟩
      rw [show m + 6 - 2 = m + 4 from by omega, show m + 6 - 4 = m + 2 from by omega]
      rw [a_eq (m + 6) (by omega), a_eq (m + 4) (by omega), a_eq (m + 2) (by omega)]
      push_cast
      ring
  · have hD : (((1 - PowerSeries.X) ^ 2 * (1 + PowerSeries.X) ^ 2) : PowerSeries ℚ) =
        PowerSeries.C 1 * PowerSeries.X ^ 0 + PowerSeries.C (-2) * PowerSeries.X ^ 2 + PowerSeries.C 1 * PowerSeries.X ^ 4 := by
      simp only [map_one, map_ofNat, map_neg]
      ring
    have hN : ((1 + 2 * PowerSeries.X + PowerSeries.X ^ 2 + 2 * PowerSeries.X ^ 3 - 2 * PowerSeries.X ^ 4) : PowerSeries ℚ) =
        PowerSeries.C 1 * PowerSeries.X ^ 0 + PowerSeries.C 2 * PowerSeries.X ^ 1 + PowerSeries.C 1 * PowerSeries.X ^ 2 + PowerSeries.C 2 * PowerSeries.X ^ 3 + PowerSeries.C (-2) * PowerSeries.X ^ 4 := by
      simp only [map_one, map_ofNat, map_neg]
      ring
    rw [hD, hN]
    ext n
    simp only [mul_add, map_add, coeff_term, PowerSeries.coeff_C_mul_X_pow]
    rcases Nat.lt_or_ge n 6 with h | h
    · interval_cases n
      · norm_num [av0]
      · norm_num [av1]
      · norm_num [av0, av2]
      · norm_num [av1, av3]
      · norm_num [av0, av2, av4]
      · norm_num [av1, av3, av5]
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 6 := ⟨n - 6, by omega⟩
      rw [if_pos (show 0 ≤ m + 6 from by omega), if_pos (show 2 ≤ m + 6 from by omega), if_pos (show 4 ≤ m + 6 from by omega)]
      rw [if_neg (show ¬ (m + 6 = 0) from by omega), if_neg (show ¬ (m + 6 = 1) from by omega), if_neg (show ¬ (m + 6 = 2) from by omega), if_neg (show ¬ (m + 6 = 3) from by omega), if_neg (show ¬ (m + 6 = 4) from by omega)]
      rw [show m + 6 - 0 = m + 6 from by omega, show m + 6 - 2 = m + 4 from by omega, show m + 6 - 4 = m + 2 from by omega]
      rw [a_eq (m + 6) (by omega), a_eq (m + 4) (by omega), a_eq (m + 2) (by omega)]
      push_cast
      ring
