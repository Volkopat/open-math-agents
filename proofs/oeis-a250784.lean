import OMAStatements.S_oeis_a250784
import Mathlib

open OMA.S_oeis_a250784

namespace P250784

abbrev Col := Fin 3 → Fin 2

def ok (c d : Col) : Prop := Blk (c 0) (d 0) (c 1) (d 1) ∧ Blk (c 1) (d 1) (c 2) (d 2)

instance (c d : Col) : Decidable (ok c d) := by unfold ok Blk; infer_instance

def V (m : ℕ) (f : Fin (m + 1) → Col) : Prop := ∀ j : Fin m, ok (f j.castSucc) (f j.succ)

instance (m : ℕ) (f : Fin (m + 1) → Col) : Decidable (V m f) := by unfold V; infer_instance

def e (n : ℕ) : {x : Fin 3 → Fin (n + 1) → Fin 2 // Good n x} ≃ {y : Fin (n + 1) → Col // V n y} :=
  Equiv.subtypeEquiv (Equiv.piComm _) (fun x => by
    constructor
    · intro h j
      exact ⟨h 0 j, h 1 j⟩
    · intro h i j
      fin_cases i
      · exact (h j).1
      · exact (h j).2)

theorem card_eq (n : ℕ) : a n = ∑ f : Fin (n + 1) → Col, if V n f then 1 else 0 := by
  rw [a, Nat.card_congr (e n), Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter]

theorem V_cons (m : ℕ) (r : Col) (y : Fin (m + 1) → Col) :
    V (m + 1) (Fin.cons r y : Fin (m + 2) → Col) ↔ ok r (y 0) ∧ V m y := by
  unfold V
  rw [Fin.forall_fin_succ]
  simp only [Fin.castSucc_zero, Fin.cons_zero, Fin.cons_succ, ← Fin.succ_castSucc]

theorem sum_cons {n : ℕ} (F : (Fin (n + 1) → Col) → ℕ) :
    ∑ f, F f = ∑ x : Col, ∑ g : Fin n → Col, F (Fin.cons x g) := by
  rw [← (Fin.consEquiv (fun _ => Col)).sum_comp, Fintype.sum_prod_type]
  rfl

def H (m : ℕ) (r : Col) : ℕ :=
  ∑ y : Fin m → Col, if V m (Fin.cons r y : Fin (m + 1) → Col) then 1 else 0

theorem H_succ (m : ℕ) (r : Col) :
    H (m + 1) r = ∑ s, if ok r s then H m s else 0 := by
  rw [H, sum_cons]
  refine Finset.sum_congr rfl fun s _ => ?_
  by_cases hs : ok r s
  · rw [if_pos hs, H]
    refine Finset.sum_congr rfl fun z _ => ?_
    simp only [V_cons, Fin.cons_zero, hs, true_and]
  · rw [if_neg hs]
    refine Finset.sum_eq_zero fun z _ => ?_
    simp [V_cons, Fin.cons_zero, hs]

theorem H0 (r : Col) : H 0 r = 1 := by
  rw [H, Fintype.sum_unique, if_pos]
  intro i
  exact i.elim0

theorem sumR2 (g : (Fin 2 → Fin 2) → ℕ) :
    ∑ s, g s = g ![0, 0] + g ![0, 1] + g ![1, 0] + g ![1, 1] := by
  have e : ∀ a b : Fin 2, (piFinTwoEquiv fun _ => Fin 2).symm (a, b) = ![a, b] := by
    intro a b
    funext i
    fin_cases i <;> rfl
  rw [← (piFinTwoEquiv fun _ => Fin 2).symm.sum_comp, Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two, e]
  ring

theorem sumC (g : Col → ℕ) : ∑ s, g s = g ![0, 0, 0] + g ![0, 0, 1] + g ![0, 1, 0] + g ![0, 1, 1] + g ![1, 0, 0] + g ![1, 0, 1] + g ![1, 1, 0] + g ![1, 1, 1] := by
  rw [← (Fin.consEquiv (fun _ => Fin 2)).sum_comp, Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two]
  rw [sumR2, sumR2]
  try simp only [Fin.consEquiv_apply]
  ring_nf
  rfl

theorem Hs (m : ℕ) :
    H (m + 1) ![0, 0, 0] = H m ![0, 0, 0] + H m ![0, 0, 1] + H m ![0, 1, 1] + H m ![1, 1, 1] ∧
    H (m + 1) ![0, 0, 1] = H m ![0, 0, 1] + H m ![0, 1, 0] + H m ![1, 1, 0] ∧
    H (m + 1) ![0, 1, 0] = H m ![1, 0, 1] ∧
    H (m + 1) ![0, 1, 1] = H m ![0, 1, 1] + H m ![1, 0, 0] + H m ![1, 0, 1] ∧
    H (m + 1) ![1, 0, 0] = H m ![0, 1, 1] ∧
    H (m + 1) ![1, 0, 1] = H m ![0, 1, 0] ∧
    H (m + 1) ![1, 1, 0] = H m ![0, 0, 1] ∧
    H (m + 1) ![1, 1, 1] = H m ![0, 0, 0] + H m ![0, 0, 1] + H m ![0, 1, 1] + H m ![1, 1, 1] := by
  have k0 : ok ![0, 0, 0] ![0, 0, 0] := by decide
  have k1 : ok ![0, 0, 0] ![0, 0, 1] := by decide
  have k2 : ¬ ok ![0, 0, 0] ![0, 1, 0] := by decide
  have k3 : ok ![0, 0, 0] ![0, 1, 1] := by decide
  have k4 : ¬ ok ![0, 0, 0] ![1, 0, 0] := by decide
  have k5 : ¬ ok ![0, 0, 0] ![1, 0, 1] := by decide
  have k6 : ¬ ok ![0, 0, 0] ![1, 1, 0] := by decide
  have k7 : ok ![0, 0, 0] ![1, 1, 1] := by decide
  have k8 : ¬ ok ![0, 0, 1] ![0, 0, 0] := by decide
  have k9 : ok ![0, 0, 1] ![0, 0, 1] := by decide
  have k10 : ok ![0, 0, 1] ![0, 1, 0] := by decide
  have k11 : ¬ ok ![0, 0, 1] ![0, 1, 1] := by decide
  have k12 : ¬ ok ![0, 0, 1] ![1, 0, 0] := by decide
  have k13 : ¬ ok ![0, 0, 1] ![1, 0, 1] := by decide
  have k14 : ok ![0, 0, 1] ![1, 1, 0] := by decide
  have k15 : ¬ ok ![0, 0, 1] ![1, 1, 1] := by decide
  have k16 : ¬ ok ![0, 1, 0] ![0, 0, 0] := by decide
  have k17 : ¬ ok ![0, 1, 0] ![0, 0, 1] := by decide
  have k18 : ¬ ok ![0, 1, 0] ![0, 1, 0] := by decide
  have k19 : ¬ ok ![0, 1, 0] ![0, 1, 1] := by decide
  have k20 : ¬ ok ![0, 1, 0] ![1, 0, 0] := by decide
  have k21 : ok ![0, 1, 0] ![1, 0, 1] := by decide
  have k22 : ¬ ok ![0, 1, 0] ![1, 1, 0] := by decide
  have k23 : ¬ ok ![0, 1, 0] ![1, 1, 1] := by decide
  have k24 : ¬ ok ![0, 1, 1] ![0, 0, 0] := by decide
  have k25 : ¬ ok ![0, 1, 1] ![0, 0, 1] := by decide
  have k26 : ¬ ok ![0, 1, 1] ![0, 1, 0] := by decide
  have k27 : ok ![0, 1, 1] ![0, 1, 1] := by decide
  have k28 : ok ![0, 1, 1] ![1, 0, 0] := by decide
  have k29 : ok ![0, 1, 1] ![1, 0, 1] := by decide
  have k30 : ¬ ok ![0, 1, 1] ![1, 1, 0] := by decide
  have k31 : ¬ ok ![0, 1, 1] ![1, 1, 1] := by decide
  have k32 : ¬ ok ![1, 0, 0] ![0, 0, 0] := by decide
  have k33 : ¬ ok ![1, 0, 0] ![0, 0, 1] := by decide
  have k34 : ¬ ok ![1, 0, 0] ![0, 1, 0] := by decide
  have k35 : ok ![1, 0, 0] ![0, 1, 1] := by decide
  have k36 : ¬ ok ![1, 0, 0] ![1, 0, 0] := by decide
  have k37 : ¬ ok ![1, 0, 0] ![1, 0, 1] := by decide
  have k38 : ¬ ok ![1, 0, 0] ![1, 1, 0] := by decide
  have k39 : ¬ ok ![1, 0, 0] ![1, 1, 1] := by decide
  have k40 : ¬ ok ![1, 0, 1] ![0, 0, 0] := by decide
  have k41 : ¬ ok ![1, 0, 1] ![0, 0, 1] := by decide
  have k42 : ok ![1, 0, 1] ![0, 1, 0] := by decide
  have k43 : ¬ ok ![1, 0, 1] ![0, 1, 1] := by decide
  have k44 : ¬ ok ![1, 0, 1] ![1, 0, 0] := by decide
  have k45 : ¬ ok ![1, 0, 1] ![1, 0, 1] := by decide
  have k46 : ¬ ok ![1, 0, 1] ![1, 1, 0] := by decide
  have k47 : ¬ ok ![1, 0, 1] ![1, 1, 1] := by decide
  have k48 : ¬ ok ![1, 1, 0] ![0, 0, 0] := by decide
  have k49 : ok ![1, 1, 0] ![0, 0, 1] := by decide
  have k50 : ¬ ok ![1, 1, 0] ![0, 1, 0] := by decide
  have k51 : ¬ ok ![1, 1, 0] ![0, 1, 1] := by decide
  have k52 : ¬ ok ![1, 1, 0] ![1, 0, 0] := by decide
  have k53 : ¬ ok ![1, 1, 0] ![1, 0, 1] := by decide
  have k54 : ¬ ok ![1, 1, 0] ![1, 1, 0] := by decide
  have k55 : ¬ ok ![1, 1, 0] ![1, 1, 1] := by decide
  have k56 : ok ![1, 1, 1] ![0, 0, 0] := by decide
  have k57 : ok ![1, 1, 1] ![0, 0, 1] := by decide
  have k58 : ¬ ok ![1, 1, 1] ![0, 1, 0] := by decide
  have k59 : ok ![1, 1, 1] ![0, 1, 1] := by decide
  have k60 : ¬ ok ![1, 1, 1] ![1, 0, 0] := by decide
  have k61 : ¬ ok ![1, 1, 1] ![1, 0, 1] := by decide
  have k62 : ¬ ok ![1, 1, 1] ![1, 1, 0] := by decide
  have k63 : ok ![1, 1, 1] ![1, 1, 1] := by decide
  simp only [H_succ, sumC, k0, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, k12, k13, k14, k15, k16, k17, k18, k19, k20, k21, k22, k23, k24, k25, k26, k27, k28, k29, k30, k31, k32, k33, k34, k35, k36, k37, k38, k39, k40, k41, k42, k43, k44, k45, k46, k47, k48, k49, k50, k51, k52, k53, k54, k55, k56, k57, k58, k59, k60, k61, k62, k63, if_true, if_false, add_zero, zero_add]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> trivial

def S (m : ℕ) : ℕ := H m ![0, 0, 0] + H m ![0, 0, 1] + H m ![0, 1, 0] + H m ![0, 1, 1] + H m ![1, 0, 0] + H m ![1, 0, 1] + H m ![1, 1, 0] + H m ![1, 1, 1]

theorem aS (n : ℕ) : a n = S n := by
  rw [card_eq, sum_cons, sumC]
  rfl

theorem Srec (m : ℕ) : (S (m + 4) : ℤ) = 4 * S (m + 3) - 4 * S (m + 2) - S (m + 1) + 2 * S m := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7⟩ := Hs m
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := Hs (m + 1)
  obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7⟩ := Hs (m + 2)
  obtain ⟨d0, d1, d2, d3, d4, d5, d6, d7⟩ := Hs (m + 3)
  simp only [show m + 1 + 1 = m + 2 from rfl, show m + 2 + 1 = m + 3 from rfl,
    show m + 3 + 1 = m + 4 from rfl] at *
  simp only [S]
  zify at *
  linear_combination (1 : ℤ) * d0 + (1 : ℤ) * d1 + (1 : ℤ) * d2 + (1 : ℤ) * d3 + (1 : ℤ) * d4 + (1 : ℤ) * d5 + (1 : ℤ) * d6 + (1 : ℤ) * d7 + (-2 : ℤ) * c0 + (-2 : ℤ) * c2 + (-3 : ℤ) * c4 + (-2 : ℤ) * c5 + (-3 : ℤ) * c6 + (-2 : ℤ) * c7 + (-3 : ℤ) * b1 + (2 : ℤ) * b2 + (-3 : ℤ) * b3 + (4 : ℤ) * b4 + (2 : ℤ) * b5 + (4 : ℤ) * b6 + (1 : ℤ) * a0 + (2 : ℤ) * a1 + (2 : ℤ) * a3 + (-2 : ℤ) * a4 + (-2 : ℤ) * a6 + (1 : ℤ) * a7

theorem S0 : S 0 = 8 := by simp [S, H0]

theorem S1 : S 1 = 18 := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7⟩ := Hs 0
  simp only [show (0 : ℕ) + 1 = 1 from rfl, show (1 : ℕ) + 1 = 2 from rfl,
    show (2 : ℕ) + 1 = 3 from rfl, H0] at *
  simp only [S]
  omega

theorem S2 : S 2 = 46 := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7⟩ := Hs 0
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := Hs 1
  simp only [show (0 : ℕ) + 1 = 1 from rfl, show (1 : ℕ) + 1 = 2 from rfl,
    show (2 : ℕ) + 1 = 3 from rfl, H0] at *
  simp only [S]
  omega

theorem S3 : S 3 = 106 := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7⟩ := Hs 0
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := Hs 1
  obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7⟩ := Hs 2
  simp only [show (0 : ℕ) + 1 = 1 from rfl, show (1 : ℕ) + 1 = 2 from rfl,
    show (2 : ℕ) + 1 = 3 from rfl, H0] at *
  simp only [S]
  omega

theorem S4 : S 4 = 238 := by
  have h := Srec 0
  simp only [show (0 : ℕ) + 4 = 4 from rfl, show (0 : ℕ) + 3 = 3 from rfl,
    show (0 : ℕ) + 2 = 2 from rfl, show (0 : ℕ) + 1 = 1 from rfl] at h
  rw [S3, S2, S1, S0] at h
  omega

end P250784

open P250784 in
theorem OMA.solution : type_of% @OMA.S_oeis_a250784.main := by
  refine ⟨by rw [aS, S1], by rw [aS, S2], by rw [aS, S3], by rw [aS, S4], ?_⟩
  intro n _
  simp only [aS]
  exact Srec n
