import OMAStatements.S_oeis_a269907
import Mathlib

namespace CAOEISA269907Aux


def pat (b : Bool) (L : List (ℤ × ℤ)) : ℤ → ℤ → Bool := fun i j => if (i, j) ∈ L then !b else b

def inBox (L : List (ℤ × ℤ)) : Prop := ∀ p ∈ L, -2 ≤ p.1 ∧ p.1 ≤ 2 ∧ -2 ≤ p.2 ∧ p.2 ≤ 2

lemma pat_far (b : Bool) (L : List (ℤ × ℤ)) (hL : inBox L) (u v : ℤ)
    (h : ¬(-2 ≤ u ∧ u ≤ 2 ∧ -2 ≤ v ∧ v ≤ 2)) : pat b L u v = b := by
  unfold pat
  have hm : (u, v) ∉ L := fun hm => h (hL _ hm)
  simp [hm]

def seven : List ℤ := [-3, -2, -1, 0, 1, 2, 3]

lemma mem_seven (x : ℤ) (h1 : -3 ≤ x) (h2 : x ≤ 3) : x ∈ seven := by
  unfold seven
  simp
  omega

def nxt (code : ℕ) (g : ℤ → ℤ → Bool) : ℤ → ℤ → Bool := fun i j =>
  code.testBit ((g i j).toNat + 2 * ((g (i + 1) j).toNat + (g (i - 1) j).toNat +
    (g i (j + 1)).toNat + (g i (j - 1)).toNat))

open OMA.S_oeis_a269907 in
lemma cell_succ (code t : ℕ) : cell code (t + 1) = nxt code (cell code t) := by
  funext i j
  rw [cell]
  rfl

open OMA.S_oeis_a269907 in
lemma cell_zero (code : ℕ) : cell code 0 = pat false [(0, 0)] := by
  funext i j
  unfold pat
  rw [cell]
  by_cases h : i = 0 ∧ j = 0
  · simp [h]
  · have h' : ¬ ((i, j) = ((0 : ℤ), (0 : ℤ))) := fun e => h (Prod.mk.injEq _ _ _ _ |>.mp e)
    simp [h, h']

lemma step_pat (code : ℕ) (b b' : Bool) (L L' : List (ℤ × ℤ)) (hL : inBox L) (hL' : inBox L')
    (hr : code.testBit (b.toNat + 2 * (b.toNat + b.toNat + b.toNat + b.toNat)) = b')
    (hbox : ∀ x ∈ seven, ∀ y ∈ seven, nxt code (pat b L) x y = pat b' L' x y) :
    nxt code (pat b L) = pat b' L' := by
  funext x y
  by_cases h : (-3 ≤ x ∧ x ≤ 3) ∧ (-3 ≤ y ∧ y ≤ 3)
  · exact hbox x (mem_seven x h.1.1 h.1.2) y (mem_seven y h.2.1 h.2.2)
  · rw [pat_far b' L' hL' x y (by omega)]
    unfold nxt
    rw [pat_far b L hL x y (by omega), pat_far b L hL (x + 1) y (by omega),
      pat_far b L hL (x - 1) y (by omega), pat_far b L hL x (y + 1) (by omega),
      pat_far b L hL x (y - 1) (by omega)]
    exact hr

lemma count_single (t : ℕ) (p : ℤ × ℤ)
    (h : -(t : ℤ) ≤ p.1 ∧ p.1 ≤ t ∧ -(t : ℤ) ≤ p.2 ∧ p.2 ≤ t) :
    ∑ i ∈ Finset.range (2 * t + 1), ∑ j ∈ Finset.range (2 * t + 1),
      (if (((i : ℤ) - t, (j : ℤ) - t) = p) then 1 else 0) = 1 := by
  obtain ⟨p1, p2⟩ := p
  simp only at h
  have e1 : (((p1 + t).toNat : ℕ) : ℤ) = p1 + t := Int.toNat_of_nonneg (by omega)
  have e2 : (((p2 + t).toNat : ℕ) : ℤ) = p2 + t := Int.toNat_of_nonneg (by omega)
  rw [Finset.sum_eq_single (p1 + t).toNat]
  · rw [Finset.sum_eq_single (p2 + t).toNat]
    · rw [if_pos]
      rw [e1, e2]
      simp
    · intro j _ hj
      rw [if_neg]
      intro heq
      apply hj
      have h2 := (Prod.mk.injEq _ _ _ _ |>.mp heq).2
      omega
    · intro hn
      exfalso
      apply hn
      rw [Finset.mem_range]
      omega
  · intro i _ hi
    apply Finset.sum_eq_zero
    intro j _
    rw [if_neg]
    intro heq
    apply hi
    have h1 := (Prod.mk.injEq _ _ _ _ |>.mp heq).1
    omega
  · intro hn
    exfalso
    apply hn
    rw [Finset.mem_range]
    omega

lemma count_mem (t : ℕ) (L : List (ℤ × ℤ)) (hn : L.Nodup)
    (hb : ∀ p ∈ L, -(t : ℤ) ≤ p.1 ∧ p.1 ≤ t ∧ -(t : ℤ) ≤ p.2 ∧ p.2 ≤ t) :
    ∑ i ∈ Finset.range (2 * t + 1), ∑ j ∈ Finset.range (2 * t + 1),
      (if (((i : ℤ) - t, (j : ℤ) - t) ∈ L) then 1 else 0) = L.length := by
  induction L with
  | nil => simp
  | cons p L ih =>
    have hp : p ∉ L := (List.nodup_cons.mp hn).1
    have hn' : L.Nodup := (List.nodup_cons.mp hn).2
    have e : ∀ i j : ℕ, (if (((i : ℤ) - t, (j : ℤ) - t) ∈ p :: L) then 1 else 0) =
        (if (((i : ℤ) - t, (j : ℤ) - t) = p) then 1 else 0) +
        (if (((i : ℤ) - t, (j : ℤ) - t) ∈ L) then 1 else 0) := by
      intro i j
      by_cases h1 : ((i : ℤ) - t, (j : ℤ) - t) = p
      · have h2 : ((i : ℤ) - t, (j : ℤ) - t) ∉ L := by rw [h1]; exact hp
        rw [if_pos (by rw [h1]; exact List.mem_cons_self), if_pos h1, if_neg h2]
      · by_cases h3 : ((i : ℤ) - t, (j : ℤ) - t) ∈ L
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

open OMA.S_oeis_a269907 in
lemma onCount_false (code t : ℕ) (L : List (ℤ × ℤ)) (c : ℕ) (hc : L.length = c) (hn : L.Nodup)
    (hb : ∀ p ∈ L, -(t : ℤ) ≤ p.1 ∧ p.1 ≤ t ∧ -(t : ℤ) ≤ p.2 ∧ p.2 ≤ t)
    (h : cell code t = pat false L) : onCount code t = c := by
  unfold onCount
  rw [h, ← hc, ← count_mem t L hn hb]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  unfold pat
  by_cases hm : ((i : ℤ) - t, (j : ℤ) - t) ∈ L <;> simp [hm]

open OMA.S_oeis_a269907 in
lemma onCount_true (code t : ℕ) (L : List (ℤ × ℤ)) (c : ℕ) (hc : L.length = c) (hn : L.Nodup)
    (hb : ∀ p ∈ L, -(t : ℤ) ≤ p.1 ∧ p.1 ≤ t ∧ -(t : ℤ) ≤ p.2 ∧ p.2 ≤ t)
    (h : cell code t = pat true L) : onCount code t + c = (2 * t + 1) ^ 2 := by
  unfold onCount
  rw [h, ← hc, ← count_mem t L hn hb, ← Finset.sum_add_distrib]
  have e : ∀ i ∈ Finset.range (2 * t + 1),
      (∑ j ∈ Finset.range (2 * t + 1), (if pat true L ((i : ℤ) - t) ((j : ℤ) - t) = true then 1 else 0)
        + ∑ j ∈ Finset.range (2 * t + 1), (if (((i : ℤ) - t, (j : ℤ) - t) ∈ L) then 1 else 0))
      = 2 * t + 1 := by
    intro i _
    rw [← Finset.sum_add_distrib]
    have e2 : ∀ j ∈ Finset.range (2 * t + 1),
        ((if pat true L ((i : ℤ) - t) ((j : ℤ) - t) = true then 1 else 0)
          + (if (((i : ℤ) - t, (j : ℤ) - t) ∈ L) then 1 else 0) : ℕ) = 1 := by
      intro j _
      unfold pat
      by_cases hm : ((i : ℤ) - t, (j : ℤ) - t) ∈ L <;> simp [hm]
    rw [Finset.sum_congr rfl e2]
    simp
  rw [Finset.sum_congr rfl e]
  simp
  ring


open PowerSeries in
lemma coeff_term (f : ℕ → ℚ) (c : ℚ) (k n : ℕ) :
    coeff n (mk f * (C c * X ^ k)) = if k ≤ n then c * f (n - k) else 0 := by
  rw [← mul_assoc, mul_comm (mk f) (C c), mul_assoc, coeff_C_mul, coeff_mul_X_pow']
  split_ifs <;> simp [coeff_mk]

open OMA.S_oeis_a269907 in
lemma st0 : cell 1 0 = pat false [(0, 0)] := cell_zero 1

open OMA.S_oeis_a269907 in
lemma st1 : cell 1 1 = pat true [(-1, 0), (0, -1), (0, 0), (0, 1), (1, 0)] := by
  rw [show (1 : ℕ) = 0 + 1 from rfl, cell_succ, st0]
  exact step_pat 1 false true [(0, 0)] [(-1, 0), (0, -1), (0, 0), (0, 1), (1, 0)] (by unfold inBox; decide) (by unfold inBox; decide) (by decide) (by decide)

open OMA.S_oeis_a269907 in
lemma st2 : cell 1 2 = pat false [(0, 0)] := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, cell_succ, st1]
  exact step_pat 1 true false [(-1, 0), (0, -1), (0, 0), (0, 1), (1, 0)] [(0, 0)] (by unfold inBox; decide) (by unfold inBox; decide) (by decide) (by decide)

open OMA.S_oeis_a269907 in
lemma st3 : cell 1 3 = pat true [(-1, 0), (0, -1), (0, 0), (0, 1), (1, 0)] := by
  rw [show (3 : ℕ) = 2 + 1 from rfl, cell_succ, st2]
  exact step_pat 1 false true [(0, 0)] [(-1, 0), (0, -1), (0, 0), (0, 1), (1, 0)] (by unfold inBox; decide) (by unfold inBox; decide) (by decide) (by decide)

lemma stepAB : nxt 1 (pat false [(0, 0)]) = pat true [(-1, 0), (0, -1), (0, 0), (0, 1), (1, 0)] :=
  step_pat 1 false true [(0, 0)] [(-1, 0), (0, -1), (0, 0), (0, 1), (1, 0)] (by unfold inBox; decide) (by unfold inBox; decide) (by decide) (by decide)

lemma stepBA : nxt 1 (pat true [(-1, 0), (0, -1), (0, 0), (0, 1), (1, 0)]) = pat false [(0, 0)] :=
  step_pat 1 true false [(-1, 0), (0, -1), (0, 0), (0, 1), (1, 0)] [(0, 0)] (by unfold inBox; decide) (by unfold inBox; decide) (by decide) (by decide)

open OMA.S_oeis_a269907 in
lemma stP (m : ℕ) : cell 1 (2 + 2 * m) = pat false [(0, 0)] ∧
    cell 1 (2 + 2 * m + 1) = pat true [(-1, 0), (0, -1), (0, 0), (0, 1), (1, 0)] := by
  induction m with
  | zero => exact ⟨st2, st3⟩
  | succ k ih =>
    have h1 : cell 1 (2 + 2 * (k + 1)) = pat false [(0, 0)] := by
      rw [show 2 + 2 * (k + 1) = (2 + 2 * k + 1) + 1 from by ring, cell_succ, ih.2]
      exact stepBA
    refine ⟨h1, ?_⟩
    rw [cell_succ, h1]
    exact stepAB

open OMA.S_oeis_a269907 in
lemma oc0 : onCount 1 0 = 1 :=
  onCount_false 1 0 _ 1 rfl (by decide) (by decide) st0

open OMA.S_oeis_a269907 in
lemma oc1 : onCount 1 1 = 4 := by
  have h := onCount_true 1 1 _ 5 rfl (by decide) (by decide) st1
  omega

open OMA.S_oeis_a269907 in
lemma oc2 : onCount 1 2 = 1 :=
  onCount_false 1 2 _ 1 rfl (by decide) (by decide) st2

open OMA.S_oeis_a269907 in
lemma oc3 : onCount 1 3 = 44 := by
  have h := onCount_true 1 3 _ 5 rfl (by decide) (by decide) st3
  omega

lemma hLE : inBox [(0, 0)] := by unfold inBox; decide

open OMA.S_oeis_a269907 in
lemma ocE (m : ℕ) : (onCount 1 (2 + 2 * m) : ℤ) = 1 := by
  have h := onCount_false 1 (2 + 2 * m) _ 1 rfl (by decide) (fun p hp => by have h := hLE p hp; omega) (stP m).1
  rw [h]
  norm_num

lemma hLO : inBox [(-1, 0), (0, -1), (0, 0), (0, 1), (1, 0)] := by unfold inBox; decide

open OMA.S_oeis_a269907 in
lemma ocO (m : ℕ) : (onCount 1 (2 + 2 * m + 1) : ℤ) = (2 * (2 + 2 * (m : ℤ) + 1) + 1) ^ 2 - 5 := by
  have h := onCount_true 1 (2 + 2 * m + 1) _ 5 rfl (by decide) (fun p hp => by have h := hLO p hp; omega) (stP m).2
  have h' : ((onCount 1 (2 + 2 * m + 1) : ℕ) : ℤ) + 5 = (2 * (2 + 2 * (m : ℤ) + 1) + 1) ^ 2 := by exact_mod_cast h
  linarith

open OMA.S_oeis_a269907 in
lemma oc_eq (n : ℕ) (hn : 2 ≤ n) : (onCount 1 n : ℚ) = ((-(3 : ℚ) / 2) + (2 : ℚ) * (n : ℚ) + (2 : ℚ) * (n : ℚ) ^ 2) + (-1 : ℚ) ^ n * (((5 : ℚ) / 2) + (-2 : ℚ) * (n : ℚ) + (-2 : ℚ) * (n : ℚ) ^ 2) := by
  obtain ⟨m, rfl | rfl⟩ : ∃ m, n = 2 + 2 * m ∨ n = 2 + 2 * m + 1 := ⟨(n - 2) / 2, by omega⟩
  · have hs : (-1 : ℚ) ^ (2 + 2 * m) = 1 := Even.neg_one_pow ⟨1 + m, by ring⟩
    have h := ocE m
    have h' : ((onCount 1 (2 + 2 * m) : ℕ) : ℚ) = (((onCount 1 (2 + 2 * m) : ℕ) : ℤ) : ℚ) := by norm_cast
    rw [h', h, hs]
    push_cast
    ring
  · have hs : (-1 : ℚ) ^ (2 + 2 * m + 1) = -1 := Odd.neg_one_pow ⟨1 + m, by ring⟩
    have h := ocO m
    have h' : ((onCount 1 (2 + 2 * m + 1) : ℕ) : ℚ) = (((onCount 1 (2 + 2 * m + 1) : ℕ) : ℤ) : ℚ) := by norm_cast
    rw [h', h, hs]
    push_cast
    ring

open OMA.S_oeis_a269907 in
lemma a0 : (a 0 : ℚ) = 1 := by
  norm_num [a, oc0]

open OMA.S_oeis_a269907 in
lemma a1 : (a 1 : ℚ) = 4 := by
  norm_num [a, oc1]

open OMA.S_oeis_a269907 in
lemma a_big (m : ℕ) : (a (m + 2) : ℚ) = 4 * ((4 : ℚ) ^ (m + 2) - (2 : ℚ) ^ (m + 2) - 1) := by
  have h1 : 2 ≤ 2 ^ (m + 1) := by
    have : 1 ≤ 2 ^ m := Nat.one_le_two_pow
    have e : 2 ^ (m + 1) = 2 * 2 ^ m := by ring
    omega
  have h2 : 2 ^ (m + 2) - 1 = 2 + 2 * (2 ^ (m + 1) - 2) + 1 := by
    have e : 2 ^ (m + 2) = 2 * 2 ^ (m + 1) := by ring
    omega
  have e4 : (4 : ℚ) ^ (m + 2) = 16 * ((2 : ℚ) ^ m) ^ 2 := by
    rw [show (4 : ℚ) = 2 ^ 2 from by norm_num, ← pow_mul]
    ring
  unfold a
  rw [h2, ocO]
  push_cast [Nat.cast_sub h1]
  rw [e4]
  ring

open OMA.S_oeis_a269907 in
lemma a_cl (n : ℕ) (hn : 1 ≤ n) : (a n : ℚ) = 4 * ((4 : ℚ) ^ n - (2 : ℚ) ^ n - 1) := by
  rcases Nat.lt_or_ge n 2 with h | h
  · interval_cases n
    rw [a1]
    norm_num
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    exact a_big m

end CAOEISA269907Aux

open OMA.S_oeis_a269907 CAOEISA269907Aux in
theorem OMA.solution : type_of% @OMA.S_oeis_a269907.main := by
  refine ⟨?_, ?_, ?_⟩
  · intro n hn
    exact a_cl n hn
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
    rw [show m + 4 - 1 = m + 3 from by omega, show m + 4 - 2 = m + 2 from by omega,
      show m + 4 - 3 = m + 1 from by omega]
    rw [a_cl (m + 4) (by omega), a_cl (m + 3) (by omega), a_cl (m + 2) (by omega),
      a_cl (m + 1) (by omega)]
    ring
  · have hD : (((1 - PowerSeries.X) * (1 - 2 * PowerSeries.X) * (1 - 4 * PowerSeries.X)) : PowerSeries ℚ) =
        PowerSeries.C 1 * PowerSeries.X ^ 0 + PowerSeries.C (-7) * PowerSeries.X ^ 1 + PowerSeries.C 14 * PowerSeries.X ^ 2 + PowerSeries.C (-8) * PowerSeries.X ^ 3 := by
      simp only [map_one, map_ofNat, map_neg]
      ring
    have hN : ((1 - 3 * PowerSeries.X + 30 * PowerSeries.X ^ 2 - 40 * PowerSeries.X ^ 3) : PowerSeries ℚ) =
        PowerSeries.C 1 * PowerSeries.X ^ 0 + PowerSeries.C (-3) * PowerSeries.X ^ 1 + PowerSeries.C 30 * PowerSeries.X ^ 2 + PowerSeries.C (-40) * PowerSeries.X ^ 3 := by
      simp only [map_one, map_ofNat, map_neg]
      ring
    rw [hD, hN]
    ext n
    simp only [mul_add, map_add, coeff_term, PowerSeries.coeff_C_mul_X_pow]
    have v2 := a_cl 2 (by norm_num)
    have v3 := a_cl 3 (by norm_num)
    norm_num at v2 v3
    rcases Nat.lt_or_ge n 4 with h | h
    · interval_cases n
      · norm_num [a0]
      · norm_num [a0, a1]
      · norm_num [a0, a1, v2]
      · norm_num [a0, a1, v2, v3]
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
      rw [if_pos (show 0 ≤ m + 4 from by omega), if_pos (show 1 ≤ m + 4 from by omega), if_pos (show 2 ≤ m + 4 from by omega), if_pos (show 3 ≤ m + 4 from by omega)]
      rw [if_neg (show ¬ (m + 4 = 0) from by omega), if_neg (show ¬ (m + 4 = 1) from by omega), if_neg (show ¬ (m + 4 = 2) from by omega), if_neg (show ¬ (m + 4 = 3) from by omega)]
      rw [show m + 4 - 0 = m + 4 from by omega, show m + 4 - 1 = m + 3 from by omega, show m + 4 - 2 = m + 2 from by omega, show m + 4 - 3 = m + 1 from by omega]
      rw [a_cl (m + 4) (by omega), a_cl (m + 3) (by omega), a_cl (m + 2) (by omega), a_cl (m + 1) (by omega)]
      ring
