import OMAStatements.S_oeis_a250899
import Mathlib

open OMA.S_oeis_a250899 PowerSeries

namespace P250899

abbrev Col := Fin 2 → Fin 3

def ok (c d : Col) : Prop := CellOK ((c 0 : ℕ) : ℤ) ((d 0 : ℕ) : ℤ) ((c 1 : ℕ) : ℤ) ((d 1 : ℕ) : ℤ)

instance (c d : Col) : Decidable (ok c d) := by unfold ok CellOK; infer_instance

def V (m : ℕ) (f : Fin (m + 1) → Col) : Prop := ∀ j : Fin m, ok (f j.castSucc) (f j.succ)

instance (m : ℕ) (f : Fin (m + 1) → Col) : Decidable (V m f) := by unfold V; infer_instance

def e (n : ℕ) : {x : Fin 2 → Fin (n + 1) → Fin 3 // ∀ i : Fin 1, ∀ j : Fin n,
    CellOK ((x i.castSucc j.castSucc : ℕ) : ℤ) ((x i.castSucc j.succ : ℕ) : ℤ) ((x i.succ j.castSucc : ℕ) : ℤ) ((x i.succ j.succ : ℕ) : ℤ)} ≃
    {y : Fin (n + 1) → Col // V n y} :=
  Equiv.subtypeEquiv (Equiv.piComm _) (fun x => by
    constructor
    · intro h j
      exact h 0 j
    · intro h i j
      fin_cases i
      exact h j)

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

theorem sumC (g : Col → ℕ) : ∑ s, g s = g ![0, 0] + g ![0, 1] + g ![0, 2] + g ![1, 0] + g ![1, 1] + g ![1, 2] + g ![2, 0] + g ![2, 1] + g ![2, 2] := by
  have e : ∀ a b : Fin 3, (piFinTwoEquiv fun _ => Fin 3).symm (a, b) = ![a, b] := by
    intro a b; funext i; fin_cases i <;> rfl
  rw [← (piFinTwoEquiv fun _ => Fin 3).symm.sum_comp, Fintype.sum_prod_type]
  simp only [Fin.sum_univ_three, e]
  ring

theorem Hs (m : ℕ) :
    H (m + 1) ![0, 0] = H m ![0, 0] + H m ![0, 1] + H m ![0, 2] + H m ![1, 1] + H m ![1, 2] + H m ![2, 2] ∧
    H (m + 1) ![0, 1] = H m ![0, 1] + H m ![0, 2] + H m ![1, 2] ∧
    H (m + 1) ![0, 2] = H m ![0, 2] ∧
    H (m + 1) ![1, 0] = H m ![0, 1] + H m ![0, 2] + H m ![1, 0] + H m ![1, 2] + H m ![2, 1] ∧
    H (m + 1) ![1, 1] = H m ![0, 0] + H m ![0, 1] + H m ![0, 2] + H m ![1, 1] + H m ![1, 2] + H m ![2, 2] ∧
    H (m + 1) ![1, 2] = H m ![0, 1] + H m ![0, 2] + H m ![1, 2] ∧
    H (m + 1) ![2, 0] = H m ![0, 2] + H m ![2, 0] ∧
    H (m + 1) ![2, 1] = H m ![0, 1] + H m ![0, 2] + H m ![1, 0] + H m ![1, 2] + H m ![2, 1] ∧
    H (m + 1) ![2, 2] = H m ![0, 0] + H m ![0, 1] + H m ![0, 2] + H m ![1, 1] + H m ![1, 2] + H m ![2, 2] := by
  have k0 : ok ![0, 0] ![0, 0] := by decide
  have k1 : ok ![0, 0] ![0, 1] := by decide
  have k2 : ok ![0, 0] ![0, 2] := by decide
  have k3 : ¬ ok ![0, 0] ![1, 0] := by decide
  have k4 : ok ![0, 0] ![1, 1] := by decide
  have k5 : ok ![0, 0] ![1, 2] := by decide
  have k6 : ¬ ok ![0, 0] ![2, 0] := by decide
  have k7 : ¬ ok ![0, 0] ![2, 1] := by decide
  have k8 : ok ![0, 0] ![2, 2] := by decide
  have k9 : ¬ ok ![0, 1] ![0, 0] := by decide
  have k10 : ok ![0, 1] ![0, 1] := by decide
  have k11 : ok ![0, 1] ![0, 2] := by decide
  have k12 : ¬ ok ![0, 1] ![1, 0] := by decide
  have k13 : ¬ ok ![0, 1] ![1, 1] := by decide
  have k14 : ok ![0, 1] ![1, 2] := by decide
  have k15 : ¬ ok ![0, 1] ![2, 0] := by decide
  have k16 : ¬ ok ![0, 1] ![2, 1] := by decide
  have k17 : ¬ ok ![0, 1] ![2, 2] := by decide
  have k18 : ¬ ok ![0, 2] ![0, 0] := by decide
  have k19 : ¬ ok ![0, 2] ![0, 1] := by decide
  have k20 : ok ![0, 2] ![0, 2] := by decide
  have k21 : ¬ ok ![0, 2] ![1, 0] := by decide
  have k22 : ¬ ok ![0, 2] ![1, 1] := by decide
  have k23 : ¬ ok ![0, 2] ![1, 2] := by decide
  have k24 : ¬ ok ![0, 2] ![2, 0] := by decide
  have k25 : ¬ ok ![0, 2] ![2, 1] := by decide
  have k26 : ¬ ok ![0, 2] ![2, 2] := by decide
  have k27 : ¬ ok ![1, 0] ![0, 0] := by decide
  have k28 : ok ![1, 0] ![0, 1] := by decide
  have k29 : ok ![1, 0] ![0, 2] := by decide
  have k30 : ok ![1, 0] ![1, 0] := by decide
  have k31 : ¬ ok ![1, 0] ![1, 1] := by decide
  have k32 : ok ![1, 0] ![1, 2] := by decide
  have k33 : ¬ ok ![1, 0] ![2, 0] := by decide
  have k34 : ok ![1, 0] ![2, 1] := by decide
  have k35 : ¬ ok ![1, 0] ![2, 2] := by decide
  have k36 : ok ![1, 1] ![0, 0] := by decide
  have k37 : ok ![1, 1] ![0, 1] := by decide
  have k38 : ok ![1, 1] ![0, 2] := by decide
  have k39 : ¬ ok ![1, 1] ![1, 0] := by decide
  have k40 : ok ![1, 1] ![1, 1] := by decide
  have k41 : ok ![1, 1] ![1, 2] := by decide
  have k42 : ¬ ok ![1, 1] ![2, 0] := by decide
  have k43 : ¬ ok ![1, 1] ![2, 1] := by decide
  have k44 : ok ![1, 1] ![2, 2] := by decide
  have k45 : ¬ ok ![1, 2] ![0, 0] := by decide
  have k46 : ok ![1, 2] ![0, 1] := by decide
  have k47 : ok ![1, 2] ![0, 2] := by decide
  have k48 : ¬ ok ![1, 2] ![1, 0] := by decide
  have k49 : ¬ ok ![1, 2] ![1, 1] := by decide
  have k50 : ok ![1, 2] ![1, 2] := by decide
  have k51 : ¬ ok ![1, 2] ![2, 0] := by decide
  have k52 : ¬ ok ![1, 2] ![2, 1] := by decide
  have k53 : ¬ ok ![1, 2] ![2, 2] := by decide
  have k54 : ¬ ok ![2, 0] ![0, 0] := by decide
  have k55 : ¬ ok ![2, 0] ![0, 1] := by decide
  have k56 : ok ![2, 0] ![0, 2] := by decide
  have k57 : ¬ ok ![2, 0] ![1, 0] := by decide
  have k58 : ¬ ok ![2, 0] ![1, 1] := by decide
  have k59 : ¬ ok ![2, 0] ![1, 2] := by decide
  have k60 : ok ![2, 0] ![2, 0] := by decide
  have k61 : ¬ ok ![2, 0] ![2, 1] := by decide
  have k62 : ¬ ok ![2, 0] ![2, 2] := by decide
  have k63 : ¬ ok ![2, 1] ![0, 0] := by decide
  have k64 : ok ![2, 1] ![0, 1] := by decide
  have k65 : ok ![2, 1] ![0, 2] := by decide
  have k66 : ok ![2, 1] ![1, 0] := by decide
  have k67 : ¬ ok ![2, 1] ![1, 1] := by decide
  have k68 : ok ![2, 1] ![1, 2] := by decide
  have k69 : ¬ ok ![2, 1] ![2, 0] := by decide
  have k70 : ok ![2, 1] ![2, 1] := by decide
  have k71 : ¬ ok ![2, 1] ![2, 2] := by decide
  have k72 : ok ![2, 2] ![0, 0] := by decide
  have k73 : ok ![2, 2] ![0, 1] := by decide
  have k74 : ok ![2, 2] ![0, 2] := by decide
  have k75 : ¬ ok ![2, 2] ![1, 0] := by decide
  have k76 : ok ![2, 2] ![1, 1] := by decide
  have k77 : ok ![2, 2] ![1, 2] := by decide
  have k78 : ¬ ok ![2, 2] ![2, 0] := by decide
  have k79 : ¬ ok ![2, 2] ![2, 1] := by decide
  have k80 : ok ![2, 2] ![2, 2] := by decide
  simp only [H_succ, sumC, k0, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, k12, k13, k14, k15, k16, k17, k18, k19, k20, k21, k22, k23, k24, k25, k26, k27, k28, k29, k30, k31, k32, k33, k34, k35, k36, k37, k38, k39, k40, k41, k42, k43, k44, k45, k46, k47, k48, k49, k50, k51, k52, k53, k54, k55, k56, k57, k58, k59, k60, k61, k62, k63, k64, k65, k66, k67, k68, k69, k70, k71, k72, k73, k74, k75, k76, k77, k78, k79, k80, if_true, if_false, add_zero, zero_add]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> trivial

theorem Hf (m : ℕ) :
    (H m ![0, 0] : ℚ) = (1 / 2 : ℚ) + (-4 : ℚ) * (2 : ℚ) ^ m + (9 / 2 : ℚ) * (3 : ℚ) ^ m ∧
    (H m ![0, 1] : ℚ) = (-1 : ℚ) + (2 : ℚ) * (2 : ℚ) ^ m ∧
    (H m ![0, 2] : ℚ) = (1 : ℚ) ∧
    (H m ![1, 0] : ℚ) = (1 : ℚ) + (2 : ℚ) * (m : ℚ) ^ 1 * (2 : ℚ) ^ m ∧
    (H m ![1, 1] : ℚ) = (1 / 2 : ℚ) + (-4 : ℚ) * (2 : ℚ) ^ m + (9 / 2 : ℚ) * (3 : ℚ) ^ m ∧
    (H m ![1, 2] : ℚ) = (-1 : ℚ) + (2 : ℚ) * (2 : ℚ) ^ m ∧
    (H m ![2, 0] : ℚ) = (1 : ℚ) + (1 : ℚ) * (m : ℚ) ^ 1 ∧
    (H m ![2, 1] : ℚ) = (1 : ℚ) + (2 : ℚ) * (m : ℚ) ^ 1 * (2 : ℚ) ^ m ∧
    (H m ![2, 2] : ℚ) = (1 / 2 : ℚ) + (-4 : ℚ) * (2 : ℚ) ^ m + (9 / 2 : ℚ) * (3 : ℚ) ^ m := by
  induction m with
  | zero => simp only [H0]; norm_num
  | succ m ih =>
    obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩ := ih
    obtain ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8⟩ := Hs m
    rw [g0, g1, g2, g3, g4, g5, g6, g7, g8]
    push_cast
    rw [h0, h1, h2, h3, h4, h5, h6, h7, h8]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> ring

theorem aS (n : ℕ) : a n = H n ![0, 0] + H n ![0, 1] + H n ![0, 2] + H n ![1, 0] + H n ![1, 1] + H n ![1, 2] + H n ![2, 0] + H n ![2, 1] + H n ![2, 2] := by
  rw [card_eq, sum_cons, sumC]
  rfl

theorem aval (n : ℕ) : (a n : ℚ) = (7 - 2 ^ (4 + n) + 3 ^ (3 + n) + (2 + 2 ^ (3 + n)) * (n : ℚ)) / 2 := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩ := Hf n
  rw [aS]
  push_cast
  rw [h0, h1, h2, h3, h4, h5, h6, h7, h8]
  ring

end P250899

open P250899 in
theorem OMA.solution : type_of% @OMA.S_oeis_a250899.main := by
  refine ⟨?_, ?_, ?_⟩
  · intro n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 6 := ⟨n - 6, by omega⟩
    rw [show k + 6 - 1 = k + 5 by omega, show k + 6 - 2 = k + 4 by omega, show k + 6 - 3 = k + 3 by omega, show k + 6 - 4 = k + 2 by omega, show k + 6 - 5 = k + 1 by omega]
    apply Int.cast_injective (α := ℚ)
    push_cast
    simp only [aval]
    push_cast
    ring
  · have hm : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * ((1 - PowerSeries.X) ^ 2 * (1 - 2 * PowerSeries.X) ^ 2 * (1 - 3 * PowerSeries.X)) = PowerSeries.X * (37 - 206 * PowerSeries.X + 407 * PowerSeries.X ^ 2 - 348 * PowerSeries.X ^ 3 + 108 * PowerSeries.X ^ 4) := by
      have hq : ∀ F : PowerSeries ℚ, F * ((1 - PowerSeries.X) ^ 2 * (1 - 2 * PowerSeries.X) ^ 2 * (1 - 3 * PowerSeries.X)) = F - C (9 : ℚ) * (F * X ^ 1) + C (31 : ℚ) * (F * X ^ 2) - C (51 : ℚ) * (F * X ^ 3) + C (40 : ℚ) * (F * X ^ 4) - C (12 : ℚ) * (F * X ^ 5) := by
        intro F; simp only [map_ofNat, map_one, pow_one, map_neg]; ring
      have hr : (PowerSeries.X * (37 - 206 * PowerSeries.X + 407 * PowerSeries.X ^ 2 - 348 * PowerSeries.X ^ 3 + 108 * PowerSeries.X ^ 4) : PowerSeries ℚ) = C (37 : ℚ) * X ^ 1 - C (206 : ℚ) * X ^ 2 + C (407 : ℚ) * X ^ 3 - C (348 : ℚ) * X ^ 4 + C (108 : ℚ) * X ^ 5 := by
        simp only [map_ofNat, map_one, pow_one, map_neg]; ring
      rw [hq, hr]
      ext n
      simp only [map_add, map_sub, map_neg, coeff_mul_X_pow', coeff_C_mul, coeff_mk, coeff_C, coeff_X_pow, coeff_one]
      by_cases hn : n < 6
      · interval_cases n <;> simp [aval] <;> norm_num
      · obtain ⟨m, rfl⟩ : ∃ m, n = m + 6 := ⟨n - 6, by omega⟩
        simp only [show m + 6 - 1 = m + 5 by omega, show m + 6 - 2 = m + 4 by omega, show m + 6 - 3 = m + 3 by omega, show m + 6 - 4 = m + 2 by omega, show m + 6 - 5 = m + 1 by omega, show 1 ≤ m + 6 by omega, show 2 ≤ m + 6 by omega, show 3 ≤ m + 6 by omega, show 4 ≤ m + 6 by omega, show 5 ≤ m + 6 by omega, show m + 6 ≠ 0 by omega, show m + 6 ≠ 1 by omega, show m + 6 ≠ 2 by omega, show m + 6 ≠ 3 by omega, show m + 6 ≠ 4 by omega, show m + 6 ≠ 5 by omega, show m + 6 ≠ 0 by omega, show m + 5 ≠ 0 by omega, show m + 4 ≠ 0 by omega, show m + 3 ≠ 0 by omega, show m + 2 ≠ 0 by omega, show m + 1 ≠ 0 by omega, if_true, if_false, aval]
        push_cast
        ring
    have hd : constantCoeff ((1 - PowerSeries.X) ^ 2 * (1 - 2 * PowerSeries.X) ^ 2 * (1 - 3 * PowerSeries.X) : PowerSeries ℚ) ≠ 0 := by simp
    rw [G, ← hm, mul_assoc, PowerSeries.mul_inv_cancel _ hd, mul_one]
  · intro n _
    rw [aval]
