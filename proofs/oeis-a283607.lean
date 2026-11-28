import OMAStatements.S_oeis_a283607
import Mathlib

-- Problem: A283607 (Rule 670 cellular automaton, x-axis from the origin to the right edge).
-- Credit: @buzzchain
-- Idea: (1) a verified list simulator computes the automaton up to step 18 by kernel evaluation;
-- (2) in coordinates moving with the right-hand front the 5-deep tip triangle is autonomous and
-- has period 4 from step 15; (3) rows -1, 0, 1 stay ON behind the tip, whatever happens above;
-- hence a(n) = 2^(n+1) - 1 for odd n >= 15 and 2^(n+1) - 9 for even n >= 15.

namespace OMA.A
open OMA.S_oeis_a283607

def rule (c e w n s : Bool) : Bool :=
  (670 : ℕ).testBit (c.toNat + 2 * (e.toNat + w.toNat + n.toNat + s.toNat))

theorem cell_succ (t : ℕ) (i j : ℤ) : cell 670 (t+1) i j =
    rule (cell 670 t i j) (cell 670 t (i+1) j) (cell 670 t (i-1) j)
      (cell 670 t i (j+1)) (cell 670 t i (j-1)) := rfl

theorem cone (t : ℕ) : ∀ i j : ℤ, t < i.natAbs + j.natAbs → cell 670 t i j = false := by
  induction t with
  | zero =>
    intro i j h
    simp only [cell, decide_eq_false_iff_not]
    omega
  | succ t ih =>
    intro i j h
    rw [cell_succ, ih i j (by omega), ih (i+1) j (by omega), ih (i-1) j (by omega),
      ih i (j+1) (by omega), ih i (j-1) (by omega)]
    decide

theorem sym (t : ℕ) : ∀ i j : ℤ, cell 670 t (-i) j = cell 670 t i j := by
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

/-! simulator on the window [-18,18]^2 -/
def tab (f : ℕ → ℕ → Bool) : List (List Bool) :=
  (List.range 37).map fun a => (List.range 37).map fun b => f a b

def lkN (G : List (List Bool)) (a b : ℕ) : Bool := ((G[a]?).getD [])[b]?.getD false

def lkZ (G : List (List Bool)) (i j : ℤ) : Bool :=
  if 0 ≤ i + 18 ∧ 0 ≤ j + 18 then lkN G (i + 18).toNat (j + 18).toNat else false

theorem lkZ_tab (f : ℕ → ℕ → Bool) (i j : ℤ) : lkZ (tab f) i j =
    if 0 ≤ i + 18 ∧ i ≤ 18 ∧ 0 ≤ j + 18 ∧ j ≤ 18 then f (i + 18).toNat (j + 18).toNat else false := by
  unfold lkZ lkN tab
  by_cases h : 0 ≤ i + 18 ∧ i ≤ 18 ∧ 0 ≤ j + 18 ∧ j ≤ 18
  · have ha : (i + 18).toNat < 37 := by omega
    have hb : (j + 18).toNat < 37 := by omega
    simp [h, ha, hb]
  · rw [if_neg h]
    by_cases h0 : 0 ≤ i + 18 ∧ 0 ≤ j + 18
    · rw [if_pos h0]
      by_cases ha : (i + 18).toNat < 37
      · have hb : ¬ (j + 18).toNat < 37 := by omega
        simp [ha, hb]
      · simp [ha]
    · rw [if_neg h0]

def stp (G : List (List Bool)) : List (List Bool) :=
  tab fun a b => rule (lkZ G ((a:ℤ) - 18) ((b:ℤ) - 18)) (lkZ G ((a:ℤ) - 18 + 1) ((b:ℤ) - 18))
    (lkZ G ((a:ℤ) - 18 - 1) ((b:ℤ) - 18)) (lkZ G ((a:ℤ) - 18) ((b:ℤ) - 18 + 1))
    (lkZ G ((a:ℤ) - 18) ((b:ℤ) - 18 - 1))

def sim : ℕ → List (List Bool)
  | 0 => tab fun a b => a == 18 && b == 18
  | t + 1 => stp (sim t)

theorem sim_ok (t : ℕ) : t ≤ 18 → ∀ i j : ℤ, cell 670 t i j = lkZ (sim t) i j := by
  induction t with
  | zero =>
    intro _ i j
    simp only [cell, sim, lkZ_tab]
    by_cases h : 0 ≤ i + 18 ∧ i ≤ 18 ∧ 0 ≤ j + 18 ∧ j ≤ 18
    · rw [if_pos h]
      by_cases h2 : i = 0 ∧ j = 0
      · obtain ⟨rfl, rfl⟩ := h2; decide
      · have : ¬ ((i + 18).toNat = 18 ∧ (j + 18).toNat = 18) := by omega
        simp [h2]
        omega
    · rw [if_neg h]
      have : ¬ (i = 0 ∧ j = 0) := by omega
      simp [this]
  | succ t ih =>
    intro ht i j
    have ih' := ih (by omega)
    simp only [sim, stp, lkZ_tab]
    by_cases h : 0 ≤ i + 18 ∧ i ≤ 18 ∧ 0 ≤ j + 18 ∧ j ≤ 18
    · rw [if_pos h, cell_succ]
      have e1 : (((i + 18).toNat : ℕ) : ℤ) - 18 = i := by omega
      have e2 : (((j + 18).toNat : ℕ) : ℤ) - 18 = j := by omega
      rw [e1, e2, ih', ih', ih', ih', ih']
    · rw [if_neg h]
      exact cone (t+1) i j (by omega)


/-! the periodic tip -/
def tau (ph : ℕ) : ℕ := match ph with | 0 => 16 | 1 => 17 | 2 => 18 | _ => 15

theorem tau_bd (ph : ℕ) : 15 ≤ tau ph ∧ tau ph ≤ 18 := by
  unfold tau; split <;> omega

def L (ph : ℕ) (u y : ℤ) : Bool := lkZ (sim (tau ph)) ((tau ph : ℤ) - u) y

theorem L_eq (ph : ℕ) (u y : ℤ) : L ph u y = cell 670 (tau ph) ((tau ph : ℤ) - u) y :=
  (sim_ok _ (tau_bd ph).2 _ _).symm

set_option maxRecDepth 1000000 in
theorem FC : ∀ ph : Fin 4, ∀ k : Fin 6, ∀ m : Fin 11,
    rule (L ph.val ((k.val:ℤ) - 1) ((m.val:ℤ) - 5)) (L ph.val ((k.val:ℤ) - 2) ((m.val:ℤ) - 5))
      (L ph.val (k.val:ℤ) ((m.val:ℤ) - 5)) (L ph.val ((k.val:ℤ) - 1) ((m.val:ℤ) - 5 + 1))
      (L ph.val ((k.val:ℤ) - 1) ((m.val:ℤ) - 5 - 1)) = L ((ph.val + 1) % 4) (k.val:ℤ) ((m.val:ℤ) - 5) := by
  decide

set_option maxRecDepth 1000000 in
theorem FC2 : ∀ ph : Fin 4, rule true (L ph.val 5 0) true true true = true ∧
    (∀ x, rule true (L ph.val 5 1) true x true = true) ∧
    (∀ x, rule true (L ph.val 5 (-1)) true true x = true) := by
  decide

set_option maxRecDepth 1000000 in
theorem FC3 : ∀ ph : Fin 4, ∀ b : Fin 3,
    rule (L ph.val 5 ((b.val:ℤ) - 1)) (L ph.val 4 ((b.val:ℤ) - 1)) true
      (L ph.val 5 ((b.val:ℤ) - 1 + 1)) (L ph.val 5 ((b.val:ℤ) - 1 - 1)) = true := by
  decide

set_option maxRecDepth 1000000 in
theorem FC4 : ∀ ph : Fin 4, ∀ k : Fin 6,
    L ph.val (k.val:ℤ) 0 = (decide (k.val ≠ 3) || decide (ph.val % 2 = 1)) := by
  decide

set_option maxRecDepth 1000000 in
theorem FC5 : ∀ a : Fin 19, ∀ b : Fin 3, lkZ (sim 15) ((a.val:ℤ) - 9) ((b.val:ℤ) - 1) = true := by
  decide

theorem r1 : ∀ x, rule true true true x true = true := by decide
theorem r2 : ∀ x, rule true true true true x = true := by decide
theorem r0 : rule true true true true true = true := by decide

def Inv (t : ℕ) : Prop := ∀ u y : ℤ, u ≤ 5 → cell 670 t ((t:ℤ) - u) y = L (t % 4) u y
def Strip (t : ℕ) : Prop := ∀ i j : ℤ, i.natAbs + 6 ≤ t → j.natAbs ≤ 1 → cell 670 t i j = true

theorem inv15 : Inv 15 := by
  intro u y _
  rw [L_eq]
  rfl

theorem strip15 : Strip 15 := by
  intro i j hi hj
  have h := FC5 ⟨(i + 9).toNat, by omega⟩ ⟨(j + 1).toNat, by omega⟩
  simp only [] at h
  have e1 : (((i + 9).toNat : ℕ) : ℤ) - 9 = i := by omega
  have e2 : (((j + 1).toNat : ℕ) : ℤ) - 1 = j := by omega
  rw [e1, e2] at h
  rw [sim_ok 15 (by norm_num)]
  exact h

theorem inv_step (t : ℕ) (ht : 15 ≤ t) (I : Inv t) : Inv (t + 1) := by
  intro u y hu
  by_cases hin : 0 ≤ u ∧ -5 ≤ y ∧ y ≤ 5
  · have h := FC ⟨t % 4, by omega⟩ ⟨u.toNat, by omega⟩ ⟨(y + 5).toNat, by omega⟩
    simp only [] at h
    have e1 : ((u.toNat : ℕ) : ℤ) = u := by omega
    have e2 : (((y + 5).toNat : ℕ) : ℤ) - 5 = y := by omega
    rw [e1, e2] at h
    have e3 : (t + 1) % 4 = (t % 4 + 1) % 4 := by omega
    rw [e3, ← h, cell_succ]
    have c1 : ((t + 1 : ℕ) : ℤ) - u = (t:ℤ) - (u - 1) := by push_cast; ring
    have c2 : ((t + 1 : ℕ) : ℤ) - u + 1 = (t:ℤ) - (u - 2) := by push_cast; ring
    have c3 : ((t + 1 : ℕ) : ℤ) - u - 1 = (t:ℤ) - u := by push_cast; ring
    rw [c2, c3, c1, I (u-1) y (by omega), I (u-2) y (by omega), I u y hu,
      I (u-1) (y+1) (by omega), I (u-1) (y-1) (by omega)]
  · have hb := tau_bd ((t + 1) % 4)
    rw [L_eq, cone (t+1) _ _ (by omega), cone _ _ _ (by omega)]

theorem strip_key (t : ℕ) (ht : 15 ≤ t) (I : Inv t) (S : Strip t) (i j : ℤ) (h0 : 0 ≤ i)
    (hi : i + 6 ≤ (t:ℤ) + 1) (hj : j.natAbs ≤ 1) : cell 670 (t + 1) i j = true := by
  have hj' : j = 0 ∨ j = 1 ∨ j = -1 := by omega
  rw [cell_succ]
  by_cases hA : i + 7 ≤ t
  · rw [S i j (by omega) hj, S (i+1) j (by omega) hj, S (i-1) j (by omega) hj]
    rcases hj' with rfl | rfl | rfl
    · rw [S i (0+1) (by omega) (by decide), S i (0-1) (by omega) (by decide)]; exact r0
    · rw [S i (1-1) (by omega) (by decide)]; exact r1 _
    · rw [S i (-1+1) (by omega) (by decide)]; exact r2 _
  · by_cases hB : i + 6 = t
    · have e : i + 1 = (t:ℤ) - 5 := by omega
      obtain ⟨f0, f1, f2⟩ := FC2 ⟨t % 4, by omega⟩
      simp only [] at f0 f1 f2
      rw [S i j (by omega) hj, S (i-1) j (by omega) hj, e, I 5 j (by norm_num)]
      rcases hj' with rfl | rfl | rfl
      · rw [S i (0+1) (by omega) (by decide), S i (0-1) (by omega) (by decide)]; exact f0
      · rw [S i (1-1) (by omega) (by decide)]; exact f1 _
      · rw [S i (-1+1) (by omega) (by decide)]; exact f2 _
    · have e : i = (t:ℤ) - 5 := by omega
      have e1 : (t:ℤ) - 5 + 1 = (t:ℤ) - 4 := by ring
      subst e
      rw [e1, I 5 j (by norm_num), I 4 j (by norm_num), I 5 (j+1) (by norm_num),
        I 5 (j-1) (by norm_num), S ((t:ℤ) - 5 - 1) j (by omega) hj]
      have h := FC3 ⟨t % 4, by omega⟩ ⟨(j + 1).toNat, by omega⟩
      simp only [] at h
      have e2 : (((j + 1).toNat : ℕ) : ℤ) - 1 = j := by omega
      rw [e2] at h
      exact h

theorem strip_step (t : ℕ) (ht : 15 ≤ t) (I : Inv t) (S : Strip t) : Strip (t + 1) := by
  intro i j hi hj
  by_cases h0 : 0 ≤ i
  · exact strip_key t ht I S i j h0 (by omega) hj
  · rw [← sym]
    exact strip_key t ht I S (-i) j (by omega) (by omega) hj

theorem inv_all (t : ℕ) (ht : 15 ≤ t) : Inv t ∧ Strip t := by
  induction t, ht using Nat.le_induction with
  | base => exact ⟨inv15, strip15⟩
  | succ t ht ih => exact ⟨inv_step t ht ih.1, strip_step t ht ih.1 ih.2⟩

theorem axis (t : ℕ) (ht : 15 ≤ t) (u : ℕ) (hu : u ≤ t) :
    cell 670 t ((t:ℤ) - u) 0 = (decide (u ≠ 3) || decide (t % 2 = 1)) := by
  obtain ⟨I, S⟩ := inv_all t ht
  by_cases h5 : u ≤ 5
  · have h := FC4 ⟨t % 4, by omega⟩ ⟨u, by omega⟩
    simp only [] at h
    have e : t % 4 % 2 = t % 2 := by omega
    rw [e] at h
    rw [I u 0 (by omega), h]
  · rw [S _ 0 (by omega) (by decide)]
    have : u ≠ 3 := by omega
    simp [this]


def AL : List ℤ := [1, 3, 7, 15, 23, 63, 119, 255, 375, 1023, 1783, 4095, 6647, 16383, 28663, 65535, 131063, 262143]

set_option maxRecDepth 1000000 in
theorem aval_sim : ∀ n : Fin 18,
    (∑ k ∈ Finset.range (n.val + 1), if lkZ (sim n.val) (k:ℤ) 0 then (2:ℤ) ^ (n.val - k) else 0)
      = AL.getD n.val 0 := by
  decide

theorem aval (n : ℕ) (hn : n < 18) : a n = AL.getD n 0 := by
  have h := aval_sim ⟨n, hn⟩
  simp only [] at h
  rw [← h]
  unfold a
  apply Finset.sum_congr rfl
  intro k _
  rw [sim_ok n (by omega)]

theorem sumA (n : ℕ) : ∑ u ∈ Finset.range (n + 1), (2:ℤ) ^ u = 2 ^ (n + 1) - 1 := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih]; ring

theorem sumB (n : ℕ) (hn : 3 ≤ n) :
    ∑ u ∈ Finset.range (n + 1), (if u ≠ 3 then (2:ℤ) ^ u else 0) = 2 ^ (n + 1) - 1 - 8 := by
  induction n, hn using Nat.le_induction with
  | base => decide
  | succ n hn ih =>
    rw [Finset.sum_range_succ, ih, if_pos (by omega)]; ring

theorem closed (t : ℕ) (ht : 15 ≤ t) :
    a t = 2 ^ (t + 1) - 1 - (if t % 2 = 1 then 0 else 8) := by
  have h : a t = ∑ u ∈ Finset.range (t + 1),
      (if (decide (u ≠ 3) || decide (t % 2 = 1)) then (2:ℤ) ^ u else 0) := by
    unfold a
    rw [← Finset.sum_range_reflect]
    apply Finset.sum_congr rfl
    intro u hu
    have hu' : u ≤ t := by have := Finset.mem_range.mp hu; omega
    have e1 : ((t + 1 - 1 - u : ℕ) : ℤ) = (t:ℤ) - u := by omega
    have e2 : t - (t + 1 - 1 - u) = u := by omega
    rw [e1, e2, axis t ht u hu']
  rw [h]
  by_cases hodd : t % 2 = 1
  · simp [hodd, sumA]
  · rw [if_neg hodd, ← sumB t (by omega)]
    exact Finset.sum_congr rfl (fun u _ => by simp [hodd])

theorem rec (m : ℕ) (hm : 15 ≤ m) : a (m + 3) = 2 * a (m + 2) + a (m + 1) - 2 * a m := by
  rw [closed (m+3) (by omega), closed (m+2) (by omega), closed (m+1) (by omega), closed m hm]
  split_ifs <;> first | (exfalso; omega) | ring

open PowerSeries in
theorem coeffL (f : ℕ → ℚ) (n : ℕ) :
    coeff n (mk f * ((X - 1) * (X + 1) * (2 * X - 1) : PowerSeries ℚ)) =
      f n - 2 * (if 1 ≤ n then f (n - 1) else 0) - (if 2 ≤ n then f (n - 2) else 0)
        + 2 * (if 3 ≤ n then f (n - 3) else 0) := by
  have hP : ((X - 1) * (X + 1) * (2 * X - 1) : PowerSeries ℚ) = 1 - C 2 * X - X ^ 2 + C 2 * X ^ 3 := by
    have : (2 : PowerSeries ℚ) = C 2 := (map_ofNat C 2).symm
    rw [← this]; ring
  rw [hP]
  simp only [mul_sub, mul_add, mul_one, map_sub, map_add, coeff_mk, ← mul_assoc, mul_comm _ (C (2:ℚ))]
  simp only [mul_assoc, coeff_C_mul, coeff_mul_X_pow', coeff_mk]
  have h1 : mk f * X = mk f * X ^ 1 := by rw [pow_one]
  rw [h1, coeff_mul_X_pow', coeff_mk]

end OMA.A

open PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a283607.main := by
  open OMA.A OMA.S_oeis_a283607 in
  have hrec : ∀ m : ℕ, 15 ≤ m → (a (m + 3) : ℚ) = 2 * a (m + 2) + a (m + 1) - 2 * a m := by
    intro m hm
    have := rec m hm
    exact_mod_cast this
  refine ⟨?_, ?_⟩
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
    exact hrec m (by omega)
  · ext n
    rw [coeffL]
    have hC (c : ℕ) [c.AtLeastTwo] : (OfNat.ofNat c : PowerSeries ℚ) = C (OfNat.ofNat c) :=
      (map_ofNat C c).symm
    by_cases hn : n < 18
    · interval_cases n <;> simp [hC, coeff_C_mul, coeff_X_pow, coeff_X, coeff_one, aval, AL] <;> norm_num
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 18 := ⟨n - 18, by omega⟩
      have h := hrec (m + 15) (by omega)
      have e1 : m + 18 - 1 = m + 15 + 2 := by omega
      have e2 : m + 18 - 2 = m + 15 + 1 := by omega
      have e3 : m + 18 - 3 = m + 15 := by omega
      have e0 : m + 18 = m + 15 + 3 := by omega
      rw [if_pos (by omega), if_pos (by omega), if_pos (by omega), e1, e2, e3]
      simp only [hC, map_add, map_sub, coeff_C_mul, coeff_X_pow, coeff_X, coeff_one]
      rw [e0, h]
      simp
      ring
