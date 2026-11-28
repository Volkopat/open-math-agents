import OMAStatements.S_oeis_a283353
import Mathlib

-- Problem: A283353 (Rule 619 cellular automaton, x-axis from the origin to the right edge).
-- Credit: @buzzchain
-- Idea: (1) every cell outside the light cone is ON from step 1; (2) a verified list simulator computes
-- the automaton up to step 7 by kernel evaluation; (3) in coordinates moving with the right-hand front
-- the 3-deep tip is autonomous and has period 4 from step 4 (the axis argument starts at step 5); (4) behind the tip the axis stays ON,
-- because the cells above and below an axis cell are equal by mirror symmetry and an ON cell with ON
-- left and right neighbours stays ON with either 2 or 4 ON neighbours;
-- hence a(n) = 2^(n+1) - 2 for odd n and 2^(n+1) - 4 for even n >= 1.

namespace OMA.A
open OMA.S_oeis_a283353

def rule (c e w n s : Bool) : Bool :=
  (619 : ℕ).testBit (c.toNat + 2 * (e.toNat + w.toNat + n.toNat + s.toNat))

theorem cell_succ (t : ℕ) (i j : ℤ) : cell 619 (t+1) i j =
    rule (cell 619 t i j) (cell 619 t (i+1) j) (cell 619 t (i-1) j)
      (cell 619 t i (j+1)) (cell 619 t i (j-1)) := rfl

theorem cone0 (i j : ℤ) (h : 0 < i.natAbs + j.natAbs) : cell 619 0 i j = false := by
  simp only [cell, decide_eq_false_iff_not]
  omega

theorem cone1 (t : ℕ) : ∀ i j : ℤ, t + 1 < i.natAbs + j.natAbs → cell 619 (t+1) i j = true := by
  induction t with
  | zero =>
    intro i j h
    rw [cell_succ, cone0 i j (by omega), cone0 (i+1) j (by omega), cone0 (i-1) j (by omega),
      cone0 i (j+1) (by omega), cone0 i (j-1) (by omega)]
    decide
  | succ t ih =>
    intro i j h
    rw [cell_succ, ih i j (by omega), ih (i+1) j (by omega), ih (i-1) j (by omega),
      ih i (j+1) (by omega), ih i (j-1) (by omega)]
    decide

theorem cone (t : ℕ) (ht : 1 ≤ t) (i j : ℤ) (h : t < i.natAbs + j.natAbs) : cell 619 t i j = true := by
  obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
  exact cone1 s i j h

theorem sym (t : ℕ) : ∀ i j : ℤ, cell 619 t (-i) j = cell 619 t i j := by
  induction t with
  | zero =>
    intro i j
    simp [cell]
  | succ t ih =>
    intro i j
    have h1 : -i + 1 = -(i-1) := by ring
    have h2 : -i - 1 = -(i+1) := by ring
    rw [cell_succ, cell_succ, ih i j, ih i (j+1), ih i (j-1), h1, h2, ih, ih]
    unfold rule
    congr 2
    omega

theorem symj (t : ℕ) : ∀ i j : ℤ, cell 619 t i (-j) = cell 619 t i j := by
  induction t with
  | zero =>
    intro i j
    simp [cell]
  | succ t ih =>
    intro i j
    have h1 : -j + 1 = -(j-1) := by ring
    have h2 : -j - 1 = -(j+1) := by ring
    rw [cell_succ, cell_succ, ih i j, ih (i+1) j, ih (i-1) j, h1, h2, ih, ih]
    unfold rule
    congr 2
    omega

/-! simulator on the window [-7,7]^2; cells outside the window have the background value `d` -/
def tab (f : ℕ → ℕ → Bool) : List (List Bool) :=
  (List.range 15).map fun a => (List.range 15).map fun b => f a b

def lkN (d : Bool) (G : List (List Bool)) (a b : ℕ) : Bool := ((G[a]?).getD [])[b]?.getD d

def lkZ (d : Bool) (G : List (List Bool)) (i j : ℤ) : Bool :=
  if 0 ≤ i + 7 ∧ 0 ≤ j + 7 then lkN d G (i + 7).toNat (j + 7).toNat else d

theorem lkZ_tab (d : Bool) (f : ℕ → ℕ → Bool) (i j : ℤ) : lkZ d (tab f) i j =
    if 0 ≤ i + 7 ∧ i ≤ 7 ∧ 0 ≤ j + 7 ∧ j ≤ 7 then f (i + 7).toNat (j + 7).toNat else d := by
  unfold lkZ lkN tab
  by_cases h : 0 ≤ i + 7 ∧ i ≤ 7 ∧ 0 ≤ j + 7 ∧ j ≤ 7
  · have ha : (i + 7).toNat < 15 := by omega
    have hb : (j + 7).toNat < 15 := by omega
    simp [h, ha, hb]
  · rw [if_neg h]
    by_cases h0 : 0 ≤ i + 7 ∧ 0 ≤ j + 7
    · rw [if_pos h0]
      by_cases ha : (i + 7).toNat < 15
      · have hb : ¬ (j + 7).toNat < 15 := by omega
        simp [ha, hb]
      · simp [ha]
    · rw [if_neg h0]

def bg : ℕ → Bool
  | 0 => false
  | _ + 1 => true

def stp (d : Bool) (G : List (List Bool)) : List (List Bool) :=
  tab fun a b => rule (lkZ d G ((a:ℤ) - 7) ((b:ℤ) - 7)) (lkZ d G ((a:ℤ) - 7 + 1) ((b:ℤ) - 7))
    (lkZ d G ((a:ℤ) - 7 - 1) ((b:ℤ) - 7)) (lkZ d G ((a:ℤ) - 7) ((b:ℤ) - 7 + 1))
    (lkZ d G ((a:ℤ) - 7) ((b:ℤ) - 7 - 1))

def sim : ℕ → List (List Bool)
  | 0 => tab fun a b => a == 7 && b == 7
  | t + 1 => stp (bg t) (sim t)

theorem sim_ok (t : ℕ) : t ≤ 7 → ∀ i j : ℤ, cell 619 t i j = lkZ (bg t) (sim t) i j := by
  induction t with
  | zero =>
    intro _ i j
    simp only [cell, sim, lkZ_tab, bg]
    by_cases h : 0 ≤ i + 7 ∧ i ≤ 7 ∧ 0 ≤ j + 7 ∧ j ≤ 7
    · rw [if_pos h]
      by_cases h2 : i = 0 ∧ j = 0
      · obtain ⟨rfl, rfl⟩ := h2; decide
      · have : ¬ ((i + 7).toNat = 7 ∧ (j + 7).toNat = 7) := by omega
        simp [h2]
        omega
    · rw [if_neg h]
      have : ¬ (i = 0 ∧ j = 0) := by omega
      simp [this]
  | succ t ih =>
    intro ht i j
    have ih' := ih (by omega)
    simp only [sim, stp, lkZ_tab]
    by_cases h : 0 ≤ i + 7 ∧ i ≤ 7 ∧ 0 ≤ j + 7 ∧ j ≤ 7
    · rw [if_pos h, cell_succ]
      have e1 : (((i + 7).toNat : ℕ) : ℤ) - 7 = i := by omega
      have e2 : (((j + 7).toNat : ℕ) : ℤ) - 7 = j := by omega
      rw [e1, e2, ih', ih', ih', ih', ih']
    · rw [if_neg h]
      exact cone (t+1) (by omega) i j (by omega)

/-! the periodic tip -/
def tau (ph : ℕ) : ℕ := match ph with | 1 => 5 | 2 => 6 | 3 => 7 | _ => 4

theorem tau_bd (ph : ℕ) : 4 ≤ tau ph ∧ tau ph ≤ 7 := by
  unfold tau; split <;> omega

def L (ph : ℕ) (u y : ℤ) : Bool := lkZ (bg (tau ph)) (sim (tau ph)) ((tau ph : ℤ) - u) y

theorem L_eq (ph : ℕ) (u y : ℤ) : L ph u y = cell 619 (tau ph) ((tau ph : ℤ) - u) y :=
  (sim_ok _ (tau_bd ph).2 _ _).symm

set_option maxRecDepth 1000000 in
theorem FC : ∀ ph : Fin 4, ∀ k : Fin 4, ∀ m : Fin 7,
    rule (L ph.val ((k.val:ℤ) - 1) ((m.val:ℤ) - 3)) (L ph.val ((k.val:ℤ) - 2) ((m.val:ℤ) - 3))
      (L ph.val (k.val:ℤ) ((m.val:ℤ) - 3)) (L ph.val ((k.val:ℤ) - 1) ((m.val:ℤ) - 3 + 1))
      (L ph.val ((k.val:ℤ) - 1) ((m.val:ℤ) - 3 - 1)) = L ((ph.val + 1) % 4) (k.val:ℤ) ((m.val:ℤ) - 3) := by
  decide

set_option maxRecDepth 1000000 in
theorem FC2 : ∀ ph : Fin 4, ∀ x, rule true (L ph.val 3 0) true x x = true := by
  decide

set_option maxRecDepth 1000000 in
theorem FC3 : ∀ ph : Fin 4,
    rule (L ph.val 3 0) (L ph.val 2 0) true (L ph.val 3 (0 + 1)) (L ph.val 3 (0 - 1)) = true := by
  decide

set_option maxRecDepth 1000000 in
theorem FC4 : ∀ ph : Fin 4, ∀ k : Fin 4,
    L ph.val (k.val:ℤ) 0 = (decide (k.val ≠ 0) && (decide (k.val ≠ 1) || decide (ph.val % 2 = 1))) := by
  decide

theorem r0 : ∀ x, rule true true true x x = true := by decide

def Inv (t : ℕ) : Prop := ∀ u y : ℤ, u ≤ 3 → cell 619 t ((t:ℤ) - u) y = L (t % 4) u y
def Strip (t : ℕ) : Prop := ∀ i : ℤ, i.natAbs + 4 ≤ t → cell 619 t i 0 = true

theorem inv4 : Inv 4 := by
  intro u y _
  rw [L_eq]
  rfl

theorem strip5 : Strip 5 := by
  intro i hi
  have h : i = -1 ∨ i = 0 ∨ i = 1 := by omega
  rcases h with rfl | rfl | rfl <;> rw [sim_ok 5 (by norm_num)] <;> decide

theorem inv_step (t : ℕ) (ht : 4 ≤ t) (I : Inv t) : Inv (t + 1) := by
  intro u y hu
  by_cases hin : 0 ≤ u ∧ -3 ≤ y ∧ y ≤ 3
  · have h := FC ⟨t % 4, by omega⟩ ⟨u.toNat, by omega⟩ ⟨(y + 3).toNat, by omega⟩
    simp only [] at h
    have e1 : ((u.toNat : ℕ) : ℤ) = u := by omega
    have e2 : (((y + 3).toNat : ℕ) : ℤ) - 3 = y := by omega
    rw [e1, e2] at h
    have e3 : (t + 1) % 4 = (t % 4 + 1) % 4 := by omega
    rw [e3, ← h, cell_succ]
    have c1 : ((t + 1 : ℕ) : ℤ) - u = (t:ℤ) - (u - 1) := by push_cast; ring
    have c2 : ((t + 1 : ℕ) : ℤ) - u + 1 = (t:ℤ) - (u - 2) := by push_cast; ring
    have c3 : ((t + 1 : ℕ) : ℤ) - u - 1 = (t:ℤ) - u := by push_cast; ring
    rw [c2, c3, c1, I (u-1) y (by omega), I (u-2) y (by omega), I u y hu,
      I (u-1) (y+1) (by omega), I (u-1) (y-1) (by omega)]
  · have hb := tau_bd ((t + 1) % 4)
    rw [L_eq, cone (t+1) (by omega) _ _ (by omega), cone _ (by omega) _ _ (by omega)]

theorem strip_key (t : ℕ) (ht : 5 ≤ t) (I : Inv t) (S : Strip t) (i : ℤ) (h0 : 0 ≤ i)
    (hi : i + 4 ≤ (t:ℤ) + 1) : cell 619 (t + 1) i 0 = true := by
  have hm : cell 619 t i (0 - 1) = cell 619 t i (0 + 1) := by
    have := symj t i (0 + 1)
    simpa using this
  rw [cell_succ, hm]
  by_cases hA : i + 5 ≤ t
  · have hw : cell 619 t (i - 1) 0 = true := by
      by_cases hz : i = 0
      · subst hz
        have := sym t 1 0
        rw [show (0:ℤ) - 1 = -1 by norm_num, this]
        exact S 1 (by omega)
      · exact S (i - 1) (by omega)
    rw [S i (by omega), S (i+1) (by omega), hw]
    exact r0 _
  · by_cases hB : i + 4 = t
    · have e : i + 1 = (t:ℤ) - 3 := by omega
      rw [S i (by omega), S (i-1) (by omega), e, I 3 0 (by norm_num)]
      exact FC2 ⟨t % 4, by omega⟩ _
    · have e : i = (t:ℤ) - 3 := by omega
      have e1 : (t:ℤ) - 3 + 1 = (t:ℤ) - 2 := by ring
      subst e
      rw [e1, I 3 0 (by norm_num), I 2 0 (by norm_num), I 3 (0+1) (by norm_num),
        S ((t:ℤ) - 3 - 1) (by omega)]
      have h := FC3 ⟨t % 4, by omega⟩
      simp only [] at h
      have hm' : L (t % 4) 3 (0 - 1) = L (t % 4) 3 (0 + 1) := by
        rw [L_eq, L_eq]
        have := symj (tau (t % 4)) ((tau (t % 4) : ℤ) - 3) (0 + 1)
        simpa using this
      rw [hm'] at h
      exact h

theorem strip_step (t : ℕ) (ht : 5 ≤ t) (I : Inv t) (S : Strip t) : Strip (t + 1) := by
  intro i hi
  by_cases h0 : 0 ≤ i
  · exact strip_key t ht I S i h0 (by omega)
  · rw [← sym]
    exact strip_key t ht I S (-i) (by omega) (by omega)

theorem inv_all (t : ℕ) (ht : 5 ≤ t) : Inv t ∧ Strip t := by
  induction t, ht using Nat.le_induction with
  | base => exact ⟨inv_step 4 (by norm_num) inv4, strip5⟩
  | succ t ht ih => exact ⟨inv_step t (by omega) ih.1, strip_step t ht ih.1 ih.2⟩

theorem axis (t : ℕ) (ht : 5 ≤ t) (u : ℕ) (hu : u ≤ t) :
    cell 619 t ((t:ℤ) - u) 0 = (decide (u ≠ 0) && (decide (u ≠ 1) || decide (t % 2 = 1))) := by
  obtain ⟨I, S⟩ := inv_all t ht
  by_cases h3 : u ≤ 3
  · have h := FC4 ⟨t % 4, by omega⟩ ⟨u, by omega⟩
    simp only [] at h
    have e : t % 4 % 2 = t % 2 := by omega
    rw [e] at h
    rw [I u 0 (by omega), h]
  · rw [S _ (by omega)]
    have h1 : u ≠ 0 := by omega
    have h2 : u ≠ 1 := by omega
    simp [h1, h2]

def AL : List ℤ := [1, 2, 4, 14, 28]

set_option maxRecDepth 1000000 in
theorem aval_sim : ∀ n : Fin 5,
    (∑ k ∈ Finset.range (n.val + 1), if lkZ (bg n.val) (sim n.val) (k:ℤ) 0 then (2:ℤ) ^ (n.val - k) else 0)
      = AL.getD n.val 0 := by
  decide

theorem aval (n : ℕ) (hn : n < 5) : a n = AL.getD n 0 := by
  have h := aval_sim ⟨n, hn⟩
  simp only [] at h
  rw [← h]
  unfold a
  apply Finset.sum_congr rfl
  intro k _
  rw [sim_ok n (by omega)]

theorem sumA (n : ℕ) :
    ∑ u ∈ Finset.range (n + 1), (if u ≠ 0 then (2:ℤ) ^ u else 0) = 2 ^ (n + 1) - 2 := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih, if_pos (by omega)]; ring

theorem sumB (n : ℕ) (hn : 1 ≤ n) :
    ∑ u ∈ Finset.range (n + 1), (if u ≠ 0 ∧ u ≠ 1 then (2:ℤ) ^ u else 0) = 2 ^ (n + 1) - 4 := by
  induction n, hn using Nat.le_induction with
  | base => decide
  | succ n hn ih =>
    rw [Finset.sum_range_succ, ih, if_pos (by omega)]; ring

theorem closed (t : ℕ) (ht : 1 ≤ t) :
    a t = 2 ^ (t + 1) - (if t % 2 = 1 then 2 else 4) := by
  by_cases h4 : t < 5
  · rw [aval t h4]
    interval_cases t <;> decide
  have h : a t = ∑ u ∈ Finset.range (t + 1),
      (if (decide (u ≠ 0) && (decide (u ≠ 1) || decide (t % 2 = 1))) then (2:ℤ) ^ u else 0) := by
    unfold a
    rw [← Finset.sum_range_reflect]
    apply Finset.sum_congr rfl
    intro u hu
    have hu' : u ≤ t := by have := Finset.mem_range.mp hu; omega
    have e1 : ((t + 1 - 1 - u : ℕ) : ℤ) = (t:ℤ) - u := by omega
    have e2 : t - (t + 1 - 1 - u) = u := by omega
    rw [e1, e2, axis t (by omega) u hu']
  rw [h]
  by_cases hodd : t % 2 = 1
  · rw [if_pos hodd, ← sumA t]
    exact Finset.sum_congr rfl (fun u _ => by simp [hodd])
  · rw [if_neg hodd, ← sumB t ht]
    exact Finset.sum_congr rfl (fun u _ => by simp [hodd])

theorem rec (m : ℕ) (hm : 1 ≤ m) : a (m + 3) = 2 * a (m + 2) + a (m + 1) - 2 * a m := by
  rw [closed (m+3) (by omega), closed (m+2) (by omega), closed (m+1) (by omega), closed m hm]
  split_ifs <;> first | (exfalso; omega) | ring

open PowerSeries in
theorem coeffL (f : ℕ → ℚ) (n : ℕ) :
    coeff n (mk f * ((1 - X) * (1 + X) * (1 - 2 * X) : PowerSeries ℚ)) =
      f n - 2 * (if 1 ≤ n then f (n - 1) else 0) - (if 2 ≤ n then f (n - 2) else 0)
        + 2 * (if 3 ≤ n then f (n - 3) else 0) := by
  have hP : ((1 - X) * (1 + X) * (1 - 2 * X) : PowerSeries ℚ) = 1 - C 2 * X - X ^ 2 + C 2 * X ^ 3 := by
    have : (2 : PowerSeries ℚ) = C 2 := (map_ofNat C 2).symm
    rw [← this]; ring
  rw [hP]
  simp only [mul_sub, mul_add, mul_one, map_sub, map_add, coeff_mk, ← mul_assoc, mul_comm _ (C (2:ℚ))]
  simp only [mul_assoc, coeff_C_mul, coeff_mul_X_pow', coeff_mk]
  have h1 : mk f * X = mk f * X ^ 1 := by rw [pow_one]
  rw [h1, coeff_mul_X_pow', coeff_mk]

end OMA.A

open PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a283353.main := by
  open OMA.A OMA.S_oeis_a283353 in
  have hrec : ∀ m : ℕ, 1 ≤ m → (a (m + 3) : ℚ) = 2 * a (m + 2) + a (m + 1) - 2 * a m := by
    intro m hm
    have := rec m hm
    exact_mod_cast this
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hR : ((1 + 2 * X) * (1 - 2 * X + 3 * X ^ 2) : PowerSeries ℚ) = 1 - X ^ 2 + 6 * X ^ 3 := by ring
    rw [hR]
    ext n
    rw [coeffL]
    have hC (c : ℕ) [c.AtLeastTwo] : (OfNat.ofNat c : PowerSeries ℚ) = C (OfNat.ofNat c) :=
      (map_ofNat C c).symm
    by_cases hn : n < 4
    · interval_cases n <;> simp [hC, coeff_C_mul, coeff_X_pow, coeff_one, aval, AL] <;> norm_num
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
      have h := hrec (m + 1) (by omega)
      have e1 : m + 4 - 1 = m + 1 + 2 := by omega
      have e2 : m + 4 - 2 = m + 1 + 1 := by omega
      have e3 : m + 4 - 3 = m + 1 := by omega
      have e0 : m + 4 = m + 1 + 3 := by omega
      rw [if_pos (by omega), if_pos (by omega), if_pos (by omega), e1, e2, e3]
      simp only [hC, map_add, map_sub, coeff_C_mul, coeff_X_pow, coeff_one]
      rw [e0, h]
      simp
      ring
  · intro n hn he
    have h := closed n hn
    rw [if_neg (by have := Nat.even_iff.mp he; omega)] at h
    rw [h]
    push_cast
    ring
  · intro n ho
    have h := closed n (by have := Nat.odd_iff.mp ho; omega)
    rw [if_pos (Nat.odd_iff.mp ho)] at h
    rw [h]
    push_cast
    ring
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
    exact hrec m (by omega)
