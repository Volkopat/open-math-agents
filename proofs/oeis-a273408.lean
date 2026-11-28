import OMAStatements.S_oeis_a273408
import Mathlib

namespace CAA273408Aux

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


open OMA.S_oeis_a273408 in
lemma state_zero : state 0 = pat false [(0, 0)] := by
  funext i j
  show initial i j = _
  unfold pat initial
  by_cases h : i = 0 ∧ j = 0
  · simp [h]
  · have h' : ¬ ((i, j) = ((0 : ℤ), (0 : ℤ))) := fun e => h (Prod.mk.injEq _ _ _ _ |>.mp e)
    simp [h, h']

open OMA.S_oeis_a273408 in
lemma step_pat (b b' : Bool) (L L' : List (ℤ × ℤ)) (hL : inBox L) (hL' : inBox L')
    (hr : rule b (bit b + bit b + bit b + bit b) = b')
    (hbox : ∀ x ∈ seven, ∀ y ∈ seven, step (pat b L) x y = pat b' L' x y) :
    step (pat b L) = pat b' L' := by
  funext x y
  by_cases h : (-3 ≤ x ∧ x ≤ 3) ∧ (-3 ≤ y ∧ y ≤ 3)
  · exact hbox x (mem_seven x h.1.1 h.1.2) y (mem_seven y h.2.1 h.2.2)
  · rw [pat_far b' L' hL' x y (by omega)]
    unfold step neighbors
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


open OMA.S_oeis_a273408 in
lemma onCount_true (t : ℕ) (L : List (ℤ × ℤ)) (c : ℕ) (hc : L.length = c) (hn : L.Nodup)
    (hb : ∀ p ∈ L, -(t : ℤ) ≤ p.1 ∧ p.1 ≤ t ∧ -(t : ℤ) ≤ p.2 ∧ p.2 ≤ t)
    (h : state t = pat true L) : onCount t + c = (2 * t + 1) ^ 2 := by
  unfold onCount
  rw [h, ← hc, ← count_mem t L hn hb, ← Finset.sum_add_distrib]
  have e : ∀ i ∈ Finset.range (2 * t + 1),
      (∑ j ∈ Finset.range (2 * t + 1), bit (pat true L ((i : ℤ) - t) ((j : ℤ) - t))
        + ∑ j ∈ Finset.range (2 * t + 1), (if (((i : ℤ) - t, (j : ℤ) - t) ∈ L) then 1 else 0))
      = 2 * t + 1 := by
    intro i _
    rw [← Finset.sum_add_distrib]
    have e2 : ∀ j ∈ Finset.range (2 * t + 1),
        (bit (pat true L ((i : ℤ) - t) ((j : ℤ) - t))
          + (if (((i : ℤ) - t, (j : ℤ) - t) ∈ L) then 1 else 0) : ℕ) = 1 := by
      intro j _
      unfold pat bit
      by_cases hm : ((i : ℤ) - t, (j : ℤ) - t) ∈ L <;> simp [hm]
    rw [Finset.sum_congr rfl e2]
    simp
  rw [Finset.sum_congr rfl e]
  simp
  ring

open OMA.S_oeis_a273408 in
lemma st1 : state 1 = pat true [(-1, 0), (0, -1), (0, 1), (1, 0)] := by
  show step (state 0) = _
  rw [state_zero]
  exact step_pat false true _ _ (by unfold inBox; decide) (by unfold inBox; decide) (by decide) (by decide)

open OMA.S_oeis_a273408 in
lemma stN (n : ℕ) : state (n + 1) = pat true [(-1, 0), (0, -1), (0, 1), (1, 0)] := by
  induction n with
  | zero => exact st1
  | succ k ih =>
    show step (state (k + 1)) = _
    rw [ih]
    exact step_pat true true _ _ (by unfold inBox; decide) (by unfold inBox; decide) (by decide) (by decide)

open OMA.S_oeis_a273408 in
lemma oc0 : onCount 0 = 1 := by decide

open OMA.S_oeis_a273408 in
lemma ocN (n : ℕ) : (onCount (n + 1) : ℤ) = (2 * ((n : ℤ) + 1) + 1) ^ 2 - 4 := by
  have h := onCount_true (n + 1) _ 4 rfl (by decide)
    (fun p hp => by
      have hL : ∀ q ∈ [((-1 : ℤ), (0 : ℤ)), (0, -1), (0, 1), (1, 0)],
          -1 ≤ q.1 ∧ q.1 ≤ 1 ∧ -1 ≤ q.2 ∧ q.2 ≤ 1 := by decide
      have h := hL p hp
      omega) (stN n)
  have h' : ((onCount (n + 1) : ℕ) : ℤ) + 4 = (2 * ((n : ℤ) + 1) + 1) ^ 2 := by exact_mod_cast h
  linarith

open OMA.S_oeis_a273408 in
lemma a_succ (n : ℕ) : a (n + 1) = a n + onCount (n + 1) := by
  unfold a
  rw [Finset.sum_range_succ]

open OMA.S_oeis_a273408 in
lemma a_cl (n : ℕ) : 3 * (a n : ℤ) = 4 * (n : ℤ) ^ 3 + 12 * (n : ℤ) ^ 2 - (n : ℤ) + 3 := by
  induction n with
  | zero =>
    have : a 0 = 1 := by
      unfold a
      simp [oc0]
    rw [this]
    norm_num
  | succ k ih =>
    rw [a_succ]
    push_cast
    rw [ocN]
    linarith [ih]

open PowerSeries in
lemma coeff_termZ (f : ℕ → ℤ) (c : ℤ) (k n : ℕ) :
    coeff n (mk f * (C c * X ^ k)) = if k ≤ n then c * f (n - k) else 0 := by
  rw [← mul_assoc, mul_comm (mk f) (C c), mul_assoc, coeff_C_mul, coeff_mul_X_pow']
  split_ifs <;> simp [coeff_mk]

end CAA273408Aux

open OMA.S_oeis_a273408 CAA273408Aux in
theorem OMA.solution : type_of% @OMA.S_oeis_a273408.main := by
  refine ⟨?_, ?_, ?_⟩
  · intro n
    have h := a_cl n
    have h' : 3 * (a n : ℚ) = 4 * (n : ℚ) ^ 3 + 12 * (n : ℚ) ^ 2 - (n : ℚ) + 3 := by exact_mod_cast h
    linarith
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
    rw [show m + 4 - 1 = m + 3 from by omega, show m + 4 - 2 = m + 2 from by omega,
      show m + 4 - 3 = m + 1 from by omega, show m + 4 - 4 = m from by omega]
    have h4 := a_cl (m + 4)
    have h3 := a_cl (m + 3)
    have h2 := a_cl (m + 2)
    have h1 := a_cl (m + 1)
    have h0 := a_cl m
    push_cast at h4 h3 h2 h1 h0
    linarith
  · have hD : ((1 : PowerSeries ℤ) - PowerSeries.X) ^ 4 =
        PowerSeries.C 1 * PowerSeries.X ^ 0 + PowerSeries.C (-4) * PowerSeries.X ^ 1 + PowerSeries.C 6 * PowerSeries.X ^ 2 + PowerSeries.C (-4) * PowerSeries.X ^ 3 + PowerSeries.C 1 * PowerSeries.X ^ 4 := by
      simp only [map_one, map_ofNat, map_neg]
      ring
    have hN : (1 + 2 * PowerSeries.X + 9 * PowerSeries.X ^ 2 - 4 * PowerSeries.X ^ 3 : PowerSeries ℤ) =
        PowerSeries.C 1 * PowerSeries.X ^ 0 + PowerSeries.C 2 * PowerSeries.X ^ 1 + PowerSeries.C 9 * PowerSeries.X ^ 2 + PowerSeries.C (-4) * PowerSeries.X ^ 3 := by
      simp only [map_one, map_ofNat, map_neg]
      ring
    rw [hD, hN]
    ext n
    simp only [mul_add, map_add, coeff_termZ, PowerSeries.coeff_C_mul_X_pow]
    have v0 := a_cl 0
    have v1 := a_cl 1
    have v2 := a_cl 2
    have v3 := a_cl 3
    norm_num at v0 v1 v2 v3
    rcases Nat.lt_or_ge n 4 with h | h
    · interval_cases n
      · norm_num
        omega
      · norm_num
        omega
      · norm_num
        omega
      · norm_num
        omega
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
      rw [if_pos (show 0 ≤ m + 4 from by omega), if_pos (show 1 ≤ m + 4 from by omega), if_pos (show 2 ≤ m + 4 from by omega), if_pos (show 3 ≤ m + 4 from by omega), if_pos (show 4 ≤ m + 4 from by omega)]
      rw [if_neg (show ¬ (m + 4 = 0) from by omega), if_neg (show ¬ (m + 4 = 1) from by omega), if_neg (show ¬ (m + 4 = 2) from by omega), if_neg (show ¬ (m + 4 = 3) from by omega)]
      rw [show m + 4 - 0 = m + 4 from by omega, show m + 4 - 1 = m + 3 from by omega, show m + 4 - 2 = m + 2 from by omega, show m + 4 - 3 = m + 1 from by omega, show m + 4 - 4 = m from by omega]
      have h4 := a_cl (m + 4)
      have h3 := a_cl (m + 3)
      have h2 := a_cl (m + 2)
      have h1 := a_cl (m + 1)
      have h0 := a_cl m
      push_cast at h4 h3 h2 h1 h0
      linarith
