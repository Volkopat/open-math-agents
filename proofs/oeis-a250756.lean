import OMAStatements.S_oeis_a250756
import Mathlib

open OMA.S_oeis_a250756 PowerSeries

namespace P250756

abbrev Col := Fin 2 → Fin 3

def ok (c d : Col) : Prop := Blk (c 0) (d 0) (c 1) (d 1)

instance (c d : Col) : Decidable (ok c d) := by unfold ok Blk; infer_instance

def V (m : ℕ) (f : Fin (m + 1) → Col) : Prop := ∀ j : Fin m, ok (f j.castSucc) (f j.succ)

instance (m : ℕ) (f : Fin (m + 1) → Col) : Decidable (V m f) := by unfold V; infer_instance

def e (n : ℕ) : {x : Fin 2 → Fin (n + 1) → Fin 3 // ∀ i : Fin 1, ∀ j : Fin n,
      Blk (x i.castSucc j.castSucc) (x i.castSucc j.succ) (x i.succ j.castSucc) (x i.succ j.succ)} ≃
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
    H (m + 1) ![1, 0] = H m ![0, 1] + H m ![0, 2] + H m ![1, 0] + H m ![1, 1] + H m ![1, 2] + H m ![2, 1] + H m ![2, 2] ∧
    H (m + 1) ![1, 1] = H m ![0, 2] + H m ![1, 1] + H m ![1, 2] + H m ![2, 2] ∧
    H (m + 1) ![1, 2] = H m ![1, 2] ∧
    H (m + 1) ![2, 0] = H m ![0, 2] + H m ![1, 1] + H m ![1, 2] + H m ![2, 0] + H m ![2, 1] + H m ![2, 2] ∧
    H (m + 1) ![2, 1] = H m ![1, 2] + H m ![2, 1] + H m ![2, 2] ∧
    H (m + 1) ![2, 2] = H m ![2, 2] := by
  simp only [H_succ, sumC]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_num [ok, Blk]

theorem Hf (m : ℕ) :
    (H m ![0, 0] : ℚ) = (1 : ℚ) + (5 / 2 : ℚ) * (m : ℚ) ^ 1 + (5 / 2 : ℚ) * (m : ℚ) ^ 2 ∧
    (H m ![0, 1] : ℚ) = (1 : ℚ) + (2 : ℚ) * (m : ℚ) ^ 1 ∧
    (H m ![0, 2] : ℚ) = (1 : ℚ) ∧
    (H m ![1, 0] : ℚ) = (1 : ℚ) + (5 / 2 : ℚ) * (m : ℚ) ^ 1 + (7 / 2 : ℚ) * (m : ℚ) ^ 2 ∧
    (H m ![1, 1] : ℚ) = (1 : ℚ) + (3 : ℚ) * (m : ℚ) ^ 1 ∧
    (H m ![1, 2] : ℚ) = (1 : ℚ) ∧
    (H m ![2, 0] : ℚ) = (1 : ℚ) + (5 / 2 : ℚ) * (m : ℚ) ^ 1 + (5 / 2 : ℚ) * (m : ℚ) ^ 2 ∧
    (H m ![2, 1] : ℚ) = (1 : ℚ) + (2 : ℚ) * (m : ℚ) ^ 1 ∧
    (H m ![2, 2] : ℚ) = (1 : ℚ) := by
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

theorem aval (n : ℕ) : (a n : ℚ) = 17 / 2 * (n : ℚ) ^ 2 + 29 / 2 * (n : ℚ) + 9 := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩ := Hf n
  rw [aS]
  push_cast
  rw [h0, h1, h2, h3, h4, h5, h6, h7, h8]
  ring

end P250756

open P250756 in
theorem OMA.solution : type_of% @OMA.S_oeis_a250756.main := by
  refine ⟨fun n _ => aval n, ?_, ?_⟩
  · have hm : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 3 =
        X * (32 - 24 * X + 9 * X ^ 2) := by
      have hq : ∀ F : PowerSeries ℚ, F * (1 - X) ^ 3 = F - C (3 : ℚ) * (F * X ^ 1) + C (3 : ℚ) * (F * X ^ 2) - F * X ^ 3 := by
        intro F; simp only [map_ofNat]; ring
      have hr : (X * (32 - 24 * X + 9 * X ^ 2) : PowerSeries ℚ) = C (32 : ℚ) * X ^ 1 - C (24 : ℚ) * X ^ 2 + C (9 : ℚ) * X ^ 3 := by
        simp only [map_ofNat, pow_one]; ring
      rw [hq, hr]
      ext n
      simp only [map_add, map_sub, coeff_mul_X_pow', coeff_C_mul, coeff_mk, coeff_C, coeff_X_pow]
      by_cases hn : n < 4
      · interval_cases n <;> simp [aval] <;> norm_num
      · obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
        simp only [show m + 4 - 1 = m + 3 by omega, show m + 4 - 2 = m + 2 by omega, show m + 4 - 3 = m + 1 by omega,
          show 1 ≤ m + 4 by omega, show 2 ≤ m + 4 by omega, show 3 ≤ m + 4 by omega, show m + 4 ≠ 0 by omega,
          show m + 3 ≠ 0 by omega, show m + 2 ≠ 0 by omega, show m + 1 ≠ 0 by omega,
          show m + 4 ≠ 1 by omega, show m + 4 ≠ 2 by omega, show m + 4 ≠ 3 by omega, if_true, if_false, aval]
        push_cast
        ring
    have hd : constantCoeff ((1 - X) ^ 3 : PowerSeries ℚ) ≠ 0 := by simp
    rw [G, ← hm, mul_assoc, PowerSeries.mul_inv_cancel _ hd, mul_one]
  · intro n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
    rw [show k + 4 - 1 = k + 3 by omega, show k + 4 - 2 = k + 2 by omega, show k + 4 - 3 = k + 1 by omega]
    apply Int.cast_injective (α := ℚ)
    push_cast
    rw [aval, aval, aval, aval]
    push_cast
    ring
