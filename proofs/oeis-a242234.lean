import OMAStatements.S_oeis_a242234
import Mathlib

namespace OMA.Helpers_a242234
open OMA.S_oeis_a242234

def Good {m : ℕ} (x : Fin m → Fin 4) : Prop := AllInWindows x ∧ NewInOrder x

instance {m : ℕ} (x : Fin m → Fin 4) : Decidable (Good x) := by unfold Good; infer_instance

def last4 {m : ℕ} (x : Fin (m + 4) → Fin 4) : Fin 4 → Fin 4 := fun i => x (Fin.natAdd m i)

def okw (s : Fin 4 → Fin 4) (y : Fin 4) : Prop := ∀ v : Fin 4, v = y ∨ ∃ i, s i = v

instance (s : Fin 4 → Fin 4) (y : Fin 4) : Decidable (okw s y) := by unfold okw; infer_instance

def shift (s : Fin 4 → Fin 4) (y : Fin 4) : Fin 4 → Fin 4 := ![s 1, s 2, s 3, y]

def cls (s : Fin 4 → Fin 4) : Fin 5 :=
  if (Finset.univ.image s).card = 4 then 0
  else if (Finset.univ.image s).card ≤ 2 then 4
  else if s 0 = s 1 ∨ s 0 = s 2 ∨ s 0 = s 3 then 1
  else if s 1 = s 2 ∨ s 1 = s 3 then 2 else 3

def Ntab : Fin 5 → Fin 5 → ℕ := ![![1, 1, 1, 1, 0], ![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0],
  ![0, 0, 1, 0, 0], ![0, 0, 0, 0, 0]]

theorem T1 : ∀ s : Fin 4 → Fin 4, cls s ≠ 4 → ∀ c : Fin 5,
    (Finset.univ.filter (fun y => okw s y ∧ cls (shift s y) = c)).card = Ntab (cls s) c := by
  decide +kernel

theorem T2 : ∀ (s : Fin 4 → Fin 4) (z : Fin 4), (∀ v : Fin 4, v = z ∨ ∃ i, s i = v) → cls s ≠ 4 := by
  decide +kernel

theorem snoc_good (m : ℕ) (hm : 1 ≤ m) (x : Fin (m + 4) → Fin 4) (y : Fin 4) :
    Good (Fin.snoc x y : Fin (m + 4 + 1) → Fin 4) ↔ Good x ∧ okw (last4 x) y := by
  constructor
  · rintro ⟨hA, hN⟩
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro i hi v
      obtain ⟨j, hj1, hj2, hj3⟩ := hA (Fin.castSucc i) (by simp; omega) v
      have hjl : j.val < m + 4 := by simp at hj2; omega
      obtain ⟨j', rfl⟩ : ∃ j' : Fin (m + 4), j = Fin.castSucc j' := ⟨⟨j.val, hjl⟩, rfl⟩
      rw [Fin.snoc_castSucc] at hj3
      exact ⟨j', by simpa using hj1, by simpa using hj2, hj3⟩
    · intro j w hw
      have := hN (Fin.castSucc j) w (by rw [Fin.snoc_castSucc]; exact hw)
      obtain ⟨k, hk1, hk2⟩ := this
      have hkl : k.val < m + 4 := by
        have := Fin.lt_def.mp hk1; simp at this; omega
      obtain ⟨k', rfl⟩ : ∃ k' : Fin (m + 4), k = Fin.castSucc k' := ⟨⟨k.val, hkl⟩, rfl⟩
      rw [Fin.snoc_castSucc] at hk2
      exact ⟨k', Fin.castSucc_lt_castSucc_iff.mp hk1, hk2⟩
    · intro v
      obtain ⟨j, hj1, hj2, hj3⟩ := hA ⟨m, by omega⟩ (by simp) v
      by_cases hl : j.val < m + 4
      · right
        obtain ⟨j', rfl⟩ : ∃ j' : Fin (m + 4), j = Fin.castSucc j' := ⟨⟨j.val, hl⟩, rfl⟩
        rw [Fin.snoc_castSucc] at hj3
        simp at hj1
        refine ⟨⟨j'.val - m, by omega⟩, ?_⟩
        rw [← hj3]; simp only [last4]
        congr 1; ext; simp; omega
      · left
        obtain rfl : j = Fin.last (m + 4) := Fin.ext (by simp at hj2 ⊢; omega)
        rw [Fin.snoc_last] at hj3; exact hj3.symm
  · rintro ⟨⟨hA, hN⟩, hw⟩
    refine ⟨?_, ?_⟩
    · intro i hi v
      by_cases h5 : i.val + 5 ≤ m + 4
      · obtain ⟨j, hj1, hj2, hj3⟩ := hA ⟨i.val, by omega⟩ h5 v
        refine ⟨Fin.castSucc j, by simpa using hj1, by simpa using hj2, ?_⟩
        rw [Fin.snoc_castSucc, hj3]
      · have hi' : i.val = m := by simp at hi; omega
        rcases hw v with h | ⟨k, hk⟩
        · refine ⟨Fin.last (m + 4), by simp; omega, by simp; omega, ?_⟩
          rw [Fin.snoc_last, h]
        · refine ⟨Fin.castSucc (Fin.natAdd m k), by simp; omega, by simp; omega, ?_⟩
          rw [Fin.snoc_castSucc]; exact hk
    · intro j w hwj
      refine Fin.lastCases ?_ (fun j' hwj' => ?_) j hwj
      · intro hlast
        rw [Fin.snoc_last] at hlast
        obtain ⟨k, hk1, hk2, hk3⟩ := hA ⟨0, by omega⟩ (by simp; omega) w
        refine ⟨Fin.castSucc k, Fin.castSucc_lt_last k, ?_⟩
        rw [Fin.snoc_castSucc, hk3]
      · rw [Fin.snoc_castSucc] at hwj'
        obtain ⟨k, hk1, hk2⟩ := hN j' w hwj'
        exact ⟨Fin.castSucc k, Fin.castSucc_lt_castSucc_iff.mpr hk1, by rw [Fin.snoc_castSucc, hk2]⟩

theorem last4_snoc (m : ℕ) (x : Fin (m + 4) → Fin 4) (y : Fin 4) :
    last4 (Fin.snoc x y : Fin (m + 1 + 4) → Fin 4) = shift (last4 x) y := by
  funext i
  fin_cases i
  · show (Fin.snoc x y : Fin (m + 4 + 1) → Fin 4) (Fin.castSucc (Fin.natAdd m 1)) = _
    rw [Fin.snoc_castSucc]; rfl
  · show (Fin.snoc x y : Fin (m + 4 + 1) → Fin 4) (Fin.castSucc (Fin.natAdd m 2)) = _
    rw [Fin.snoc_castSucc]; rfl
  · show (Fin.snoc x y : Fin (m + 4 + 1) → Fin 4) (Fin.castSucc (Fin.natAdd m 3)) = _
    rw [Fin.snoc_castSucc]; rfl
  · show (Fin.snoc x y : Fin (m + 4 + 1) → Fin 4) (Fin.last (m + 4)) = _
    rw [Fin.snoc_last]; rfl

theorem good_cls (m : ℕ) (hm : 1 ≤ m) (x : Fin (m + 4) → Fin 4) (h : Good x) : cls (last4 x) ≠ 4 := by
  apply T2 (last4 x) (x ⟨m - 1, by omega⟩)
  intro v
  obtain ⟨j, hj1, hj2, hj3⟩ := h.1 ⟨m - 1, by omega⟩ (by simp; omega) v
  by_cases hj : j.val = m - 1
  · left; rw [← hj3]; congr 1; ext; simp [hj]
  · right
    refine ⟨⟨j.val - m, by simp at hj1 hj2; omega⟩, ?_⟩
    rw [← hj3]; simp only [last4]; congr 1; ext; simp at hj1 hj2 ⊢; omega

def cnt (m : ℕ) (c : Fin 5) : ℕ :=
  ((Finset.univ : Finset (Fin (m + 4) → Fin 4)).filter (fun x => Good x ∧ cls (last4 x) = c)).card

theorem a_eq (m : ℕ) : a m = ∑ c : Fin 5, cnt m c := by
  unfold a cnt
  rw [Finset.card_eq_sum_card_fiberwise (f := fun x => cls (last4 x)) (t := Finset.univ) (by simp)]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  rw [Finset.filter_filter]; rfl

theorem cnt4 (m : ℕ) (hm : 1 ≤ m) : cnt m 4 = 0 := by
  unfold cnt
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro x _ ⟨hg, hc⟩
  exact good_cls m hm x hg hc

theorem step (m : ℕ) (hm : 1 ≤ m) (c' : Fin 5) : cnt (m + 1) c' = ∑ c : Fin 5, Ntab c c' * cnt m c := by
  have h1 : cnt (m + 1) c' = ∑ x' : Fin (m + 4 + 1) → Fin 4,
      if Good x' ∧ cls (last4 (x' : Fin (m + 1 + 4) → Fin 4)) = c' then 1 else 0 := by
    unfold cnt; rw [Finset.card_filter]
  rw [h1, ← Fintype.sum_equiv (Fin.snocEquiv fun _ => Fin 4) _ _ (fun p => rfl), Fintype.sum_prod_type,
    Finset.sum_comm]
  have h2 : ∀ x : Fin (m + 4) → Fin 4, (∑ y : Fin 4, (if Good (Fin.snoc x y : Fin (m + 4 + 1) → Fin 4) ∧
      cls (last4 (Fin.snoc x y : Fin (m + 1 + 4) → Fin 4)) = c' then 1 else 0)) =
      if Good x then Ntab (cls (last4 x)) c' else 0 := by
    intro x
    have e : ∀ y : Fin 4, (Good (Fin.snoc x y : Fin (m + 4 + 1) → Fin 4) ∧
        cls (last4 (Fin.snoc x y : Fin (m + 1 + 4) → Fin 4)) = c') ↔
        (Good x ∧ (okw (last4 x) y ∧ cls (shift (last4 x) y) = c')) := by
      intro y; rw [snoc_good m hm, last4_snoc]; tauto
    simp only [e]
    by_cases hg : Good x
    · simp only [hg, true_and, if_true]
      rw [← Finset.card_filter, T1 _ (good_cls m hm x hg)]
    · simp [hg]
  refine (Finset.sum_congr rfl (fun x _ => h2 x)).trans ?_
  rw [← Finset.sum_fiberwise Finset.univ (fun x => cls (last4 x))]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  unfold cnt
  rw [Finset.card_filter, Finset.mul_sum, Finset.sum_filter]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  by_cases h1 : cls (last4 x) = c <;> by_cases h2 : Good x <;> simp [h1, h2]

theorem base : cnt 1 0 = 4 ∧ cnt 1 1 = 3 ∧ cnt 1 2 = 2 ∧ cnt 1 3 = 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide +kernel

theorem rels (m : ℕ) (hm : 1 ≤ m) :
    (cnt (m + 1) 0 : ℤ) = cnt m 0 + cnt m 1 ∧ (cnt (m + 1) 1 : ℤ) = cnt m 0 + cnt m 2 ∧
    (cnt (m + 1) 2 : ℤ) = cnt m 0 + cnt m 3 ∧ (cnt (m + 1) 3 : ℤ) = cnt m 0 := by
  have h4 := cnt4 m hm
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · rw [step m hm]
    simp [Fin.sum_univ_five, Ntab, h4]
    try ring

theorem aZ (m : ℕ) (hm : 1 ≤ m) : (a m : ℤ) = cnt m 0 + cnt m 1 + cnt m 2 + cnt m 3 := by
  rw [a_eq, Fin.sum_univ_five, cnt4 m hm]; push_cast; ring

theorem rec (n : ℕ) (hn : 5 ≤ n) : (a n : ℤ) = a (n - 1) + a (n - 2) + a (n - 3) + a (n - 4) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
  rw [show m + 5 - 1 = m + 1 + 3 by omega, show m + 5 - 2 = m + 1 + 2 by omega,
    show m + 5 - 3 = m + 1 + 1 by omega, show m + 5 - 4 = m + 1 by omega, show m + 5 = m + 1 + 4 by omega]
  obtain ⟨d0, p0, q0, r0⟩ := rels (m + 1) (by omega)
  obtain ⟨d1, p1, q1, r1⟩ := rels (m + 1 + 1) (by omega)
  obtain ⟨d2, p2, q2, r2⟩ := rels (m + 1 + 2) (by omega)
  obtain ⟨d3, p3, q3, r3⟩ := rels (m + 1 + 3) (by omega)
  rw [aZ _ (by omega), aZ _ (by omega), aZ _ (by omega), aZ _ (by omega), aZ _ (by omega)]
  simp only [show m + 1 + 1 + 1 = m + 1 + 2 by omega, show m + 1 + 2 + 1 = m + 1 + 3 by omega,
    show m + 1 + 3 + 1 = m + 1 + 4 by omega] at *
  linear_combination d0 + p0 + q0 - 2 * r0 + 2 * d1 + 2 * p1 - q1 - r1 + 3 * d2 + d3 + p3 + q3 + r3

theorem vals : (a 1 : ℤ) = 10 ∧ (a 2 : ℤ) = 22 ∧ (a 3 : ℤ) = 43 ∧ (a 4 : ℤ) = 82 := by
  obtain ⟨b0, b1, b2, b3⟩ := base
  obtain ⟨d1, p1, q1, r1⟩ := rels 1 le_rfl
  obtain ⟨d2, p2, q2, r2⟩ := rels 2 (by norm_num)
  obtain ⟨d3, p3, q3, r3⟩ := rels 3 (by norm_num)
  rw [aZ 1 le_rfl, aZ 2 (by norm_num), aZ 3 (by norm_num), aZ 4 (by norm_num)]
  simp only [b0, b1, b2, b3] at *
  push_cast at *
  refine ⟨by norm_num, ?_, ?_, ?_⟩ <;> linarith

open PowerSeries in
theorem gf : PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else (a n : ℤ)) * (1 - X - X ^ 2 - X ^ 3 - X ^ 4) =
      X * (10 + 12 * X + 11 * X ^ 2 + 7 * X ^ 3) := by
  set A := PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else (a n : ℤ)) with hA
  have hD : A * (1 - X - X ^ 2 - X ^ 3 - X ^ 4 : PowerSeries ℤ) =
      A - A * X ^ 1 - A * X ^ 2 - A * X ^ 3 - A * X ^ 4 := by ring
  have hN : (X * (10 + 12 * X + 11 * X ^ 2 + 7 * X ^ 3) : PowerSeries ℤ) =
      C (10 : ℤ) * X ^ 1 + C (12 : ℤ) * X ^ 2 + C (11 : ℤ) * X ^ 3 + C (7 : ℤ) * X ^ 4 := by
    simp only [map_ofNat]; ring
  rw [hD, hN]
  ext k
  simp only [map_add, map_sub, coeff_mul_X_pow', hA, coeff_mk]
  obtain ⟨v1, v2, v3, v4⟩ := vals
  rcases Nat.lt_or_ge k 5 with h | h
  · interval_cases k <;> simp only [v1, v2, v3, v4, coeff_C, ↓reduceIte, Nat.reduceSub, Nat.reduceLeDiff, Nat.one_le_ofNat, OfNat.ofNat_ne_zero, one_ne_zero, le_refl] <;> norm_num
  · have r := rec k h
    simp only [show 1 ≤ k by omega, show 2 ≤ k by omega, show 3 ≤ k by omega, show 4 ≤ k by omega,
      if_true, show k ≠ 0 by omega, show k - 1 ≠ 0 by omega, show k - 2 ≠ 0 by omega,
      show k - 3 ≠ 0 by omega, show k - 4 ≠ 0 by omega,
      if_false, coeff_C]
    linear_combination r

end OMA.Helpers_a242234

theorem OMA.solution : type_of% @OMA.S_oeis_a242234.main :=
  ⟨OMA.Helpers_a242234.rec, OMA.Helpers_a242234.gf⟩
