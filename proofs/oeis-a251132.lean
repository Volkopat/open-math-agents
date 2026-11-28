import OMAStatements.S_oeis_a251132
import Mathlib

open OMA.S_oeis_a251132 PowerSeries

namespace P251132

abbrev Col := Fin 4 → Fin 3

def ok (r r' : Col) : Prop := ∀ j : Fin 3, Blk (r j.castSucc) (r j.succ) (r' j.castSucc) (r' j.succ)

instance (c d : Col) : Decidable (ok c d) := by unfold ok Blk; infer_instance

def V (m : ℕ) (f : Fin (m + 1) → Col) : Prop := ∀ j : Fin m, ok (f j.castSucc) (f j.succ)

instance (m : ℕ) (f : Fin (m + 1) → Col) : Decidable (V m f) := by unfold V; infer_instance

def e (n : ℕ) : {x : Fin (n + 1) → Fin 4 → Fin 3 // ∀ i : Fin n, ∀ j : Fin 3,
      Blk (x i.castSucc j.castSucc) (x i.castSucc j.succ) (x i.succ j.castSucc) (x i.succ j.succ)} ≃
    {y : Fin (n + 1) → Col // V n y} :=
  Equiv.subtypeEquiv (Equiv.refl _) (fun x => Iff.rfl)

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

def eC : (Fin 4 → Fin 3) ≃ Fin 3 × Fin 3 × Fin 3 × Fin 3 where
  toFun f := (f 0, f 1, f 2, f 3)
  invFun p := ![p.1, p.2.1, p.2.2.1, p.2.2.2]
  left_inv f := by funext i; fin_cases i <;> rfl
  right_inv p := rfl

theorem eCs (p : Fin 3 × Fin 3 × Fin 3 × Fin 3) : eC.symm p = ![p.1, p.2.1, p.2.2.1, p.2.2.2] := rfl

theorem sumC (g : Col → ℕ) : ∑ s, g s = g ![0, 0, 0, 0] + g ![0, 0, 0, 1] + g ![0, 0, 0, 2] + g ![0, 0, 1, 0] + g ![0, 0, 1, 1] + g ![0, 0, 1, 2] + g ![0, 0, 2, 0] + g ![0, 0, 2, 1] + g ![0, 0, 2, 2] + g ![0, 1, 0, 0] + g ![0, 1, 0, 1] + g ![0, 1, 0, 2] + g ![0, 1, 1, 0] + g ![0, 1, 1, 1] + g ![0, 1, 1, 2] + g ![0, 1, 2, 0] + g ![0, 1, 2, 1] + g ![0, 1, 2, 2] + g ![0, 2, 0, 0] + g ![0, 2, 0, 1] + g ![0, 2, 0, 2] + g ![0, 2, 1, 0] + g ![0, 2, 1, 1] + g ![0, 2, 1, 2] + g ![0, 2, 2, 0] + g ![0, 2, 2, 1] + g ![0, 2, 2, 2] + g ![1, 0, 0, 0] + g ![1, 0, 0, 1] + g ![1, 0, 0, 2] + g ![1, 0, 1, 0] + g ![1, 0, 1, 1] + g ![1, 0, 1, 2] + g ![1, 0, 2, 0] + g ![1, 0, 2, 1] + g ![1, 0, 2, 2] + g ![1, 1, 0, 0] + g ![1, 1, 0, 1] + g ![1, 1, 0, 2] + g ![1, 1, 1, 0] + g ![1, 1, 1, 1] + g ![1, 1, 1, 2] + g ![1, 1, 2, 0] + g ![1, 1, 2, 1] + g ![1, 1, 2, 2] + g ![1, 2, 0, 0] + g ![1, 2, 0, 1] + g ![1, 2, 0, 2] + g ![1, 2, 1, 0] + g ![1, 2, 1, 1] + g ![1, 2, 1, 2] + g ![1, 2, 2, 0] + g ![1, 2, 2, 1] + g ![1, 2, 2, 2] + g ![2, 0, 0, 0] + g ![2, 0, 0, 1] + g ![2, 0, 0, 2] + g ![2, 0, 1, 0] + g ![2, 0, 1, 1] + g ![2, 0, 1, 2] + g ![2, 0, 2, 0] + g ![2, 0, 2, 1] + g ![2, 0, 2, 2] + g ![2, 1, 0, 0] + g ![2, 1, 0, 1] + g ![2, 1, 0, 2] + g ![2, 1, 1, 0] + g ![2, 1, 1, 1] + g ![2, 1, 1, 2] + g ![2, 1, 2, 0] + g ![2, 1, 2, 1] + g ![2, 1, 2, 2] + g ![2, 2, 0, 0] + g ![2, 2, 0, 1] + g ![2, 2, 0, 2] + g ![2, 2, 1, 0] + g ![2, 2, 1, 1] + g ![2, 2, 1, 2] + g ![2, 2, 2, 0] + g ![2, 2, 2, 1] + g ![2, 2, 2, 2] := by
  rw [← eC.symm.sum_comp]
  simp only [Fintype.sum_prod_type, Fin.sum_univ_three, eCs]
  ring

theorem S0 (g : Col → ℕ) : ∑ s, (if ok ![0, 0, 0, 0] s then g s else 0) = g ![0, 0, 0, 0] + (g ![1, 0, 0, 0] + (g ![1, 1, 0, 0] + (g ![1, 1, 1, 0] + (g ![1, 1, 1, 1] + (g ![2, 0, 0, 0] + (g ![2, 1, 0, 0] + (g ![2, 1, 1, 0] + (g ![2, 1, 1, 1] + (g ![2, 2, 0, 0] + (g ![2, 2, 1, 0] + (g ![2, 2, 1, 1] + (g ![2, 2, 2, 0] + (g ![2, 2, 2, 1] + g ![2, 2, 2, 2]))))))))))))) := by
  have hf : Finset.univ.filter (fun s : Col => ok ![0, 0, 0, 0] s) = {![0, 0, 0, 0], ![1, 0, 0, 0], ![1, 1, 0, 0], ![1, 1, 1, 0], ![1, 1, 1, 1], ![2, 0, 0, 0], ![2, 1, 0, 0], ![2, 1, 1, 0], ![2, 1, 1, 1], ![2, 2, 0, 0], ![2, 2, 1, 0], ![2, 2, 1, 1], ![2, 2, 2, 0], ![2, 2, 2, 1], ![2, 2, 2, 2]} := by decide +kernel
  rw [← Finset.sum_filter, hf, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_singleton]
  all_goals decide +kernel

theorem S1 (g : Col → ℕ) : ∑ s, (if ok ![0, 0, 0, 1] s then g s else 0) = g ![0, 0, 0, 0] + (g ![0, 0, 0, 1] + (g ![1, 0, 0, 0] + (g ![1, 0, 0, 1] + (g ![1, 1, 0, 0] + (g ![1, 1, 0, 1] + (g ![1, 1, 1, 0] + (g ![1, 1, 1, 1] + (g ![2, 0, 0, 0] + (g ![2, 0, 0, 1] + (g ![2, 1, 0, 0] + (g ![2, 1, 0, 1] + (g ![2, 1, 1, 0] + (g ![2, 1, 1, 1] + (g ![2, 2, 0, 0] + (g ![2, 2, 0, 1] + (g ![2, 2, 1, 0] + (g ![2, 2, 1, 1] + (g ![2, 2, 2, 0] + (g ![2, 2, 2, 1] + g ![2, 2, 2, 2]))))))))))))))))))) := by
  have hf : Finset.univ.filter (fun s : Col => ok ![0, 0, 0, 1] s) = {![0, 0, 0, 0], ![0, 0, 0, 1], ![1, 0, 0, 0], ![1, 0, 0, 1], ![1, 1, 0, 0], ![1, 1, 0, 1], ![1, 1, 1, 0], ![1, 1, 1, 1], ![2, 0, 0, 0], ![2, 0, 0, 1], ![2, 1, 0, 0], ![2, 1, 0, 1], ![2, 1, 1, 0], ![2, 1, 1, 1], ![2, 2, 0, 0], ![2, 2, 0, 1], ![2, 2, 1, 0], ![2, 2, 1, 1], ![2, 2, 2, 0], ![2, 2, 2, 1], ![2, 2, 2, 2]} := by decide +kernel
  rw [← Finset.sum_filter, hf, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_singleton]
  all_goals decide +kernel

theorem S2 (g : Col → ℕ) : ∑ s, (if ok ![0, 0, 0, 2] s then g s else 0) = g ![0, 0, 0, 0] + (g ![0, 0, 0, 1] + (g ![0, 0, 0, 2] + (g ![1, 0, 0, 0] + (g ![1, 0, 0, 1] + (g ![1, 0, 0, 2] + (g ![1, 1, 0, 0] + (g ![1, 1, 0, 1] + (g ![1, 1, 0, 2] + (g ![1, 1, 1, 0] + (g ![1, 1, 1, 1] + (g ![1, 1, 1, 2] + (g ![2, 0, 0, 0] + (g ![2, 0, 0, 1] + (g ![2, 0, 0, 2] + (g ![2, 1, 0, 0] + (g ![2, 1, 0, 1] + (g ![2, 1, 0, 2] + (g ![2, 1, 1, 0] + (g ![2, 1, 1, 1] + (g ![2, 1, 1, 2] + (g ![2, 2, 0, 0] + (g ![2, 2, 0, 1] + (g ![2, 2, 0, 2] + (g ![2, 2, 1, 0] + (g ![2, 2, 1, 1] + (g ![2, 2, 1, 2] + (g ![2, 2, 2, 0] + (g ![2, 2, 2, 1] + g ![2, 2, 2, 2])))))))))))))))))))))))))))) := by
  have hf : Finset.univ.filter (fun s : Col => ok ![0, 0, 0, 2] s) = {![0, 0, 0, 0], ![0, 0, 0, 1], ![0, 0, 0, 2], ![1, 0, 0, 0], ![1, 0, 0, 1], ![1, 0, 0, 2], ![1, 1, 0, 0], ![1, 1, 0, 1], ![1, 1, 0, 2], ![1, 1, 1, 0], ![1, 1, 1, 1], ![1, 1, 1, 2], ![2, 0, 0, 0], ![2, 0, 0, 1], ![2, 0, 0, 2], ![2, 1, 0, 0], ![2, 1, 0, 1], ![2, 1, 0, 2], ![2, 1, 1, 0], ![2, 1, 1, 1], ![2, 1, 1, 2], ![2, 2, 0, 0], ![2, 2, 0, 1], ![2, 2, 0, 2], ![2, 2, 1, 0], ![2, 2, 1, 1], ![2, 2, 1, 2], ![2, 2, 2, 0], ![2, 2, 2, 1], ![2, 2, 2, 2]} := by decide +kernel
  rw [← Finset.sum_filter, hf, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_singleton]
  all_goals decide +kernel

theorem S3 (g : Col → ℕ) : ∑ s, (if ok ![0, 0, 1, 0] s then g s else 0) = g ![0, 0, 1, 0] + (g ![1, 0, 1, 0] + (g ![1, 1, 1, 0] + (g ![2, 0, 1, 0] + (g ![2, 1, 1, 0] + (g ![2, 2, 1, 0] + (g ![2, 2, 2, 0] + g ![2, 2, 2, 1])))))) := by
  have hf : Finset.univ.filter (fun s : Col => ok ![0, 0, 1, 0] s) = {![0, 0, 1, 0], ![1, 0, 1, 0], ![1, 1, 1, 0], ![2, 0, 1, 0], ![2, 1, 1, 0], ![2, 2, 1, 0], ![2, 2, 2, 0], ![2, 2, 2, 1]} := by decide +kernel
  rw [← Finset.sum_filter, hf, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_singleton]
  all_goals decide +kernel

theorem S4 (g : Col → ℕ) : ∑ s, (if ok ![0, 0, 1, 1] s then g s else 0) = g ![0, 0, 0, 0] + (g ![0, 0, 1, 0] + (g ![1, 0, 0, 0] + (g ![1, 0, 1, 0] + (g ![1, 1, 0, 0] + (g ![1, 1, 1, 0] + (g ![2, 0, 0, 0] + (g ![2, 0, 1, 0] + (g ![2, 1, 0, 0] + (g ![2, 1, 1, 0] + (g ![2, 2, 0, 0] + (g ![2, 2, 1, 0] + (g ![2, 2, 2, 0] + g ![2, 2, 2, 1])))))))))))) := by
  have hf : Finset.univ.filter (fun s : Col => ok ![0, 0, 1, 1] s) = {![0, 0, 0, 0], ![0, 0, 1, 0], ![1, 0, 0, 0], ![1, 0, 1, 0], ![1, 1, 0, 0], ![1, 1, 1, 0], ![2, 0, 0, 0], ![2, 0, 1, 0], ![2, 1, 0, 0], ![2, 1, 1, 0], ![2, 2, 0, 0], ![2, 2, 1, 0], ![2, 2, 2, 0], ![2, 2, 2, 1]} := by decide +kernel
  rw [← Finset.sum_filter, hf, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_singleton]
  all_goals decide +kernel

theorem S5 (g : Col → ℕ) : ∑ s, (if ok ![0, 0, 1, 2] s then g s else 0) = g ![0, 0, 0, 0] + (g ![0, 0, 0, 1] + (g ![0, 0, 1, 0] + (g ![0, 0, 1, 1] + (g ![1, 0, 0, 0] + (g ![1, 0, 0, 1] + (g ![1, 0, 1, 0] + (g ![1, 0, 1, 1] + (g ![1, 1, 0, 0] + (g ![1, 1, 0, 1] + (g ![1, 1, 1, 0] + (g ![1, 1, 1, 1] + (g ![2, 0, 0, 0] + (g ![2, 0, 0, 1] + (g ![2, 0, 1, 0] + (g ![2, 0, 1, 1] + (g ![2, 1, 0, 0] + (g ![2, 1, 0, 1] + (g ![2, 1, 1, 0] + (g ![2, 1, 1, 1] + (g ![2, 2, 0, 0] + (g ![2, 2, 0, 1] + (g ![2, 2, 1, 0] + (g ![2, 2, 1, 1] + (g ![2, 2, 2, 0] + g ![2, 2, 2, 1])))))))))))))))))))))))) := by
  have hf : Finset.univ.filter (fun s : Col => ok ![0, 0, 1, 2] s) = {![0, 0, 0, 0], ![0, 0, 0, 1], ![0, 0, 1, 0], ![0, 0, 1, 1], ![1, 0, 0, 0], ![1, 0, 0, 1], ![1, 0, 1, 0], ![1, 0, 1, 1], ![1, 1, 0, 0], ![1, 1, 0, 1], ![1, 1, 1, 0], ![1, 1, 1, 1], ![2, 0, 0, 0], ![2, 0, 0, 1], ![2, 0, 1, 0], ![2, 0, 1, 1], ![2, 1, 0, 0], ![2, 1, 0, 1], ![2, 1, 1, 0], ![2, 1, 1, 1], ![2, 2, 0, 0], ![2, 2, 0, 1], ![2, 2, 1, 0], ![2, 2, 1, 1], ![2, 2, 2, 0], ![2, 2, 2, 1]} := by decide +kernel
  rw [← Finset.sum_filter, hf, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_singleton]
  all_goals decide +kernel

theorem S6 (g : Col → ℕ) : ∑ s, (if ok ![0, 0, 2, 0] s then g s else 0) = g ![0, 0, 2, 0] + (g ![1, 0, 2, 0] + (g ![1, 1, 2, 0] + (g ![2, 0, 2, 0] + (g ![2, 1, 2, 0] + g ![2, 2, 2, 0])))) := by
  have hf : Finset.univ.filter (fun s : Col => ok ![0, 0, 2, 0] s) = {![0, 0, 2, 0], ![1, 0, 2, 0], ![1, 1, 2, 0], ![2, 0, 2, 0], ![2, 1, 2, 0], ![2, 2, 2, 0]} := by decide +kernel
  rw [← Finset.sum_filter, hf, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_singleton]
  all_goals decide +kernel

theorem S7 (g : Col → ℕ) : ∑ s, (if ok ![0, 0, 2, 1] s then g s else 0) = g ![0, 0, 2, 0] + (g ![1, 0, 2, 0] + (g ![1, 1, 2, 0] + (g ![2, 0, 2, 0] + (g ![2, 1, 2, 0] + g ![2, 2, 2, 0])))) := by
  have hf : Finset.univ.filter (fun s : Col => ok ![0, 0, 2, 1] s) = {![0, 0, 2, 0], ![1, 0, 2, 0], ![1, 1, 2, 0], ![2, 0, 2, 0], ![2, 1, 2, 0], ![2, 2, 2, 0]} := by decide +kernel
  rw [← Finset.sum_filter, hf, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_singleton]
  all_goals decide +kernel

theorem S8 (g : Col → ℕ) : ∑ s, (if ok ![0, 0, 2, 2] s then g s else 0) = g ![0, 0, 0, 0] + (g ![0, 0, 1, 0] + (g ![0, 0, 2, 0] + (g ![1, 0, 0, 0] + (g ![1, 0, 1, 0] + (g ![1, 0, 2, 0] + (g ![1, 1, 0, 0] + (g ![1, 1, 1, 0] + (g ![1, 1, 2, 0] + (g ![2, 0, 0, 0] + (g ![2, 0, 1, 0] + (g ![2, 0, 2, 0] + (g ![2, 1, 0, 0] + (g ![2, 1, 1, 0] + (g ![2, 1, 2, 0] + (g ![2, 2, 0, 0] + (g ![2, 2, 1, 0] + g ![2, 2, 2, 0])))))))))))))))) := by
  have hf : Finset.univ.filter (fun s : Col => ok ![0, 0, 2, 2] s) = {![0, 0, 0, 0], ![0, 0, 1, 0], ![0, 0, 2, 0], ![1, 0, 0, 0], ![1, 0, 1, 0], ![1, 0, 2, 0], ![1, 1, 0, 0], ![1, 1, 1, 0], ![1, 1, 2, 0], ![2, 0, 0, 0], ![2, 0, 1, 0], ![2, 0, 2, 0], ![2, 1, 0, 0], ![2, 1, 1, 0], ![2, 1, 2, 0], ![2, 2, 0, 0], ![2, 2, 1, 0], ![2, 2, 2, 0]} := by decide +kernel
  rw [← Finset.sum_filter, hf, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_singleton]
  all_goals decide +kernel

theorem S9 (g : Col → ℕ) : ∑ s, (if ok ![0, 1, 0, 0] s then g s else 0) = g ![0, 1, 0, 0] + (g ![1, 1, 0, 0] + (g ![2, 1, 0, 0] + (g ![2, 2, 0, 0] + (g ![2, 2, 1, 0] + g ![2, 2, 1, 1])))) := by
  have hf : Finset.univ.filter (fun s : Col => ok ![0, 1, 0, 0] s) = {![0, 1, 0, 0], ![1, 1, 0, 0], ![2, 1, 0, 0], ![2, 2, 0, 0], ![2, 2, 1, 0], ![2, 2, 1, 1]} := by decide +kernel
  rw [← Finset.sum_filter, hf, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_singleton]
  all_goals decide +kernel

theorem S10 (g : Col → ℕ) : ∑ s, (if ok ![0, 1, 0, 1] s then g s else 0) = g ![0, 1, 0, 0] + (g ![0, 1, 0, 1] + (g ![1, 1, 0, 0] + (g ![1, 1, 0, 1] + (g ![2, 1, 0, 0] + (g ![2, 1, 0, 1] + (g ![2, 2, 0, 0] + (g ![2, 2, 0, 1] + (g ![2, 2, 1, 0] + g ![2, 2, 1, 1])))))))) := by
  have hf : Finset.univ.filter (fun s : Col => ok ![0, 1, 0, 1] s) = {![0, 1, 0, 0], ![0, 1, 0, 1], ![1, 1, 0, 0], ![1, 1, 0, 1], ![2, 1, 0, 0], ![2, 1, 0, 1], ![2, 2, 0, 0], ![2, 2, 0, 1], ![2, 2, 1, 0], ![2, 2, 1, 1]} := by decide +kernel
  rw [← Finset.sum_filter, hf, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_singleton]
  all_goals decide +kernel

theorem S11 (g : Col → ℕ) : ∑ s, (if ok ![0, 1, 0, 2] s then g s else 0) = g ![0, 1, 0, 0] + (g ![0, 1, 0, 1] + (g ![0, 1, 0, 2] + (g ![1, 1, 0, 0] + (g ![1, 1, 0, 1] + (g ![1, 1, 0, 2] + (g ![2, 1, 0, 0] + (g ![2, 1, 0, 1] + (g ![2, 1, 0, 2] + (g ![2, 2, 0, 0] + (g ![2, 2, 0, 1] + (g ![2, 2, 0, 2] + (g ![2, 2, 1, 0] + (g ![2, 2, 1, 1] + g ![2, 2, 1, 2]))))))))))))) := by
  have hf : Finset.univ.filter (fun s : Col => ok ![0, 1, 0, 2] s) = {![0, 1, 0, 0], ![0, 1, 0, 1], ![0, 1, 0, 2], ![1, 1, 0, 0], ![1, 1, 0, 1], ![1, 1, 0, 2], ![2, 1, 0, 0], ![2, 1, 0, 1], ![2, 1, 0, 2], ![2, 2, 0, 0], ![2, 2, 0, 1], ![2, 2, 0, 2], ![2, 2, 1, 0], ![2, 2, 1, 1], ![2, 2, 1, 2]} := by decide +kernel
  rw [← Finset.sum_filter, hf, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_singleton]
  all_goals decide +kernel

theorem S12 (g : Col → ℕ) : ∑ s, (if ok ![0, 1, 1, 0] s then g s else 0) = g ![2, 2, 1, 0] := by
  have hf : Finset.univ.filter (fun s : Col => ok ![0, 1, 1, 0] s) = {![2, 2, 1, 0]} := by decide +kernel
  rw [← Finset.sum_filter, hf, Finset.sum_singleton]

theorem S13 (g : Col → ℕ) : ∑ s, (if ok ![0, 1, 1, 1] s then g s else 0) = g ![0, 0, 0, 0] + (g ![0, 1, 0, 0] + (g ![1, 0, 0, 0] + (g ![1, 1, 0, 0] + (g ![2, 0, 0, 0] + (g ![2, 1, 0, 0] + (g ![2, 2, 0, 0] + g ![2, 2, 1, 0])))))) := by
  have hf : Finset.univ.filter (fun s : Col => ok ![0, 1, 1, 1] s) = {![0, 0, 0, 0], ![0, 1, 0, 0], ![1, 0, 0, 0], ![1, 1, 0, 0], ![2, 0, 0, 0], ![2, 1, 0, 0], ![2, 2, 0, 0], ![2, 2, 1, 0]} := by decide +kernel
  rw [← Finset.sum_filter, hf, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_singleton]
  all_goals decide +kernel

theorem S14 (g : Col → ℕ) : ∑ s, (if ok ![0, 1, 1, 2] s then g s else 0) = g ![0, 0, 0, 0] + (g ![0, 0, 0, 1] + (g ![0, 1, 0, 0] + (g ![0, 1, 0, 1] + (g ![1, 0, 0, 0] + (g ![1, 0, 0, 1] + (g ![1, 1, 0, 0] + (g ![1, 1, 0, 1] + (g ![2, 0, 0, 0] + (g ![2, 0, 0, 1] + (g ![2, 1, 0, 0] + (g ![2, 1, 0, 1] + (g ![2, 2, 0, 0] + (g ![2, 2, 0, 1] + (g ![2, 2, 1, 0] + g ![2, 2, 1, 1])))))))))))))) := by
  have hf : Finset.univ.filter (fun s : Col => ok ![0, 1, 1, 2] s) = {![0, 0, 0, 0], ![0, 0, 0, 1], ![0, 1, 0, 0], ![0, 1, 0, 1], ![1, 0, 0, 0], ![1, 0, 0, 1], ![1, 1, 0, 0], ![1, 1, 0, 1], ![2, 0, 0, 0], ![2, 0, 0, 1], ![2, 1, 0, 0], ![2, 1, 0, 1], ![2, 2, 0, 0], ![2, 2, 0, 1], ![2, 2, 1, 0], ![2, 2, 1, 1]} := by decide +kernel
  rw [← Finset.sum_filter, hf, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_singleton]
  all_goals decide +kernel

theorem S15 (g : Col → ℕ) : ∑ s, (if ok ![0, 1, 2, 0] s then g s else 0) = 0 := by
  have hf : Finset.univ.filter (fun s : Col => ok ![0, 1, 2, 0] s) = ∅ := by decide +kernel
  rw [← Finset.sum_filter, hf, Finset.sum_empty]

theorem S16 (g : Col → ℕ) : ∑ s, (if ok ![0, 1, 2, 1] s then g s else 0) = 0 := by
  have hf : Finset.univ.filter (fun s : Col => ok ![0, 1, 2, 1] s) = ∅ := by decide +kernel
  rw [← Finset.sum_filter, hf, Finset.sum_empty]

theorem S17 (g : Col → ℕ) : ∑ s, (if ok ![0, 1, 2, 2] s then g s else 0) = g ![0, 0, 0, 0] + (g ![0, 0, 1, 0] + (g ![0, 1, 0, 0] + (g ![0, 1, 1, 0] + (g ![1, 0, 0, 0] + (g ![1, 0, 1, 0] + (g ![1, 1, 0, 0] + (g ![1, 1, 1, 0] + (g ![2, 0, 0, 0] + (g ![2, 0, 1, 0] + (g ![2, 1, 0, 0] + (g ![2, 1, 1, 0] + (g ![2, 2, 0, 0] + g ![2, 2, 1, 0])))))))))))) := by
  have hf : Finset.univ.filter (fun s : Col => ok ![0, 1, 2, 2] s) = {![0, 0, 0, 0], ![0, 0, 1, 0], ![0, 1, 0, 0], ![0, 1, 1, 0], ![1, 0, 0, 0], ![1, 0, 1, 0], ![1, 1, 0, 0], ![1, 1, 1, 0], ![2, 0, 0, 0], ![2, 0, 1, 0], ![2, 1, 0, 0], ![2, 1, 1, 0], ![2, 2, 0, 0], ![2, 2, 1, 0]} := by decide +kernel
  rw [← Finset.sum_filter, hf, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_singleton]
  all_goals decide +kernel

theorem S18 (g : Col → ℕ) : ∑ s, (if ok ![0, 2, 0, 0] s then g s else 0) = g ![0, 2, 0, 0] + (g ![1, 2, 0, 0] + g ![2, 2, 0, 0]) := by
  have hf : Finset.univ.filter (fun s : Col => ok ![0, 2, 0, 0] s) = {![0, 2, 0, 0], ![1, 2, 0, 0], ![2, 2, 0, 0]} := by decide +kernel
  rw [← Finset.sum_filter, hf, Finset.sum_insert, Finset.sum_insert, Finset.sum_singleton]
  all_goals decide +kernel

theorem S19 (g : Col → ℕ) : ∑ s, (if ok ![0, 2, 0, 1] s then g s else 0) = g ![0, 2, 0, 0] + (g ![0, 2, 0, 1] + (g ![1, 2, 0, 0] + (g ![1, 2, 0, 1] + (g ![2, 2, 0, 0] + g ![2, 2, 0, 1])))) := by
  have hf : Finset.univ.filter (fun s : Col => ok ![0, 2, 0, 1] s) = {![0, 2, 0, 0], ![0, 2, 0, 1], ![1, 2, 0, 0], ![1, 2, 0, 1], ![2, 2, 0, 0], ![2, 2, 0, 1]} := by decide +kernel
  rw [← Finset.sum_filter, hf, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_singleton]
  all_goals decide +kernel

theorem S20 (g : Col → ℕ) : ∑ s, (if ok ![0, 2, 0, 2] s then g s else 0) = g ![0, 2, 0, 0] + (g ![0, 2, 0, 1] + (g ![0, 2, 0, 2] + (g ![1, 2, 0, 0] + (g ![1, 2, 0, 1] + (g ![1, 2, 0, 2] + (g ![2, 2, 0, 0] + (g ![2, 2, 0, 1] + g ![2, 2, 0, 2]))))))) := by
  have hf : Finset.univ.filter (fun s : Col => ok ![0, 2, 0, 2] s) = {![0, 2, 0, 0], ![0, 2, 0, 1], ![0, 2, 0, 2], ![1, 2, 0, 0], ![1, 2, 0, 1], ![1, 2, 0, 2], ![2, 2, 0, 0], ![2, 2, 0, 1], ![2, 2, 0, 2]} := by decide +kernel
  rw [← Finset.sum_filter, hf, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_singleton]
  all_goals decide +kernel

theorem S21 (g : Col → ℕ) : ∑ s, (if ok ![0, 2, 1, 0] s then g s else 0) = 0 := by
  have hf : Finset.univ.filter (fun s : Col => ok ![0, 2, 1, 0] s) = ∅ := by decide +kernel
  rw [← Finset.sum_filter, hf, Finset.sum_empty]

theorem S22 (g : Col → ℕ) : ∑ s, (if ok ![0, 2, 1, 1] s then g s else 0) = g ![0, 2, 0, 0] + (g ![1, 2, 0, 0] + g ![2, 2, 0, 0]) := by
  have hf : Finset.univ.filter (fun s : Col => ok ![0, 2, 1, 1] s) = {![0, 2, 0, 0], ![1, 2, 0, 0], ![2, 2, 0, 0]} := by decide +kernel
  rw [← Finset.sum_filter, hf, Finset.sum_insert, Finset.sum_insert, Finset.sum_singleton]
  all_goals decide +kernel

theorem S23 (g : Col → ℕ) : ∑ s, (if ok ![0, 2, 1, 2] s then g s else 0) = g ![0, 2, 0, 0] + (g ![0, 2, 0, 1] + (g ![1, 2, 0, 0] + (g ![1, 2, 0, 1] + (g ![2, 2, 0, 0] + g ![2, 2, 0, 1])))) := by
  have hf : Finset.univ.filter (fun s : Col => ok ![0, 2, 1, 2] s) = {![0, 2, 0, 0], ![0, 2, 0, 1], ![1, 2, 0, 0], ![1, 2, 0, 1], ![2, 2, 0, 0], ![2, 2, 0, 1]} := by decide +kernel
  rw [← Finset.sum_filter, hf, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_singleton]
  all_goals decide +kernel

theorem S24 (g : Col → ℕ) : ∑ s, (if ok ![0, 2, 2, 0] s then g s else 0) = 0 := by
  have hf : Finset.univ.filter (fun s : Col => ok ![0, 2, 2, 0] s) = ∅ := by decide +kernel
  rw [← Finset.sum_filter, hf, Finset.sum_empty]

theorem S25 (g : Col → ℕ) : ∑ s, (if ok ![0, 2, 2, 1] s then g s else 0) = 0 := by
  have hf : Finset.univ.filter (fun s : Col => ok ![0, 2, 2, 1] s) = ∅ := by decide +kernel
  rw [← Finset.sum_filter, hf, Finset.sum_empty]

theorem S26 (g : Col → ℕ) : ∑ s, (if ok ![0, 2, 2, 2] s then g s else 0) = g ![0, 0, 0, 0] + (g ![0, 1, 0, 0] + (g ![0, 2, 0, 0] + (g ![1, 0, 0, 0] + (g ![1, 1, 0, 0] + (g ![1, 2, 0, 0] + (g ![2, 0, 0, 0] + (g ![2, 1, 0, 0] + g ![2, 2, 0, 0]))))))) := by
  have hf : Finset.univ.filter (fun s : Col => ok ![0, 2, 2, 2] s) = {![0, 0, 0, 0], ![0, 1, 0, 0], ![0, 2, 0, 0], ![1, 0, 0, 0], ![1, 1, 0, 0], ![1, 2, 0, 0], ![2, 0, 0, 0], ![2, 1, 0, 0], ![2, 2, 0, 0]} := by decide +kernel
  rw [← Finset.sum_filter, hf, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_singleton]
  all_goals decide +kernel

theorem S27 (g : Col → ℕ) : ∑ s, (if ok ![1, 0, 0, 0] s then g s else 0) = g ![1, 0, 0, 0] + (g ![2, 0, 0, 0] + (g ![2, 1, 0, 0] + (g ![2, 1, 1, 0] + g ![2, 1, 1, 1]))) := by
  have hf : Finset.univ.filter (fun s : Col => ok ![1, 0, 0, 0] s) = {![1, 0, 0, 0], ![2, 0, 0, 0], ![2, 1, 0, 0], ![2, 1, 1, 0], ![2, 1, 1, 1]} := by decide +kernel
  rw [← Finset.sum_filter, hf, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_singleton]
  all_goals decide +kernel

theorem S28 (g : Col → ℕ) : ∑ s, (if ok ![1, 0, 0, 1] s then g s else 0) = g ![1, 0, 0, 0] + (g ![1, 0, 0, 1] + (g ![2, 0, 0, 0] + (g ![2, 0, 0, 1] + (g ![2, 1, 0, 0] + (g ![2, 1, 0, 1] + (g ![2, 1, 1, 0] + g ![2, 1, 1, 1])))))) := by
  have hf : Finset.univ.filter (fun s : Col => ok ![1, 0, 0, 1] s) = {![1, 0, 0, 0], ![1, 0, 0, 1], ![2, 0, 0, 0], ![2, 0, 0, 1], ![2, 1, 0, 0], ![2, 1, 0, 1], ![2, 1, 1, 0], ![2, 1, 1, 1]} := by decide +kernel
  rw [← Finset.sum_filter, hf, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_singleton]
  all_goals decide +kernel

theorem S29 (g : Col → ℕ) : ∑ s, (if ok ![1, 0, 0, 2] s then g s else 0) = g ![1, 0, 0, 0] + (g ![1, 0, 0, 1] + (g ![1, 0, 0, 2] + (g ![2, 0, 0, 0] + (g ![2, 0, 0, 1] + (g ![2, 0, 0, 2] + (g ![2, 1, 0, 0] + (g ![2, 1, 0, 1] + (g ![2, 1, 0, 2] + (g ![2, 1, 1, 0] + (g ![2, 1, 1, 1] + g ![2, 1, 1, 2])))))))))) := by
  have hf : Finset.univ.filter (fun s : Col => ok ![1, 0, 0, 2] s) = {![1, 0, 0, 0], ![1, 0, 0, 1], ![1, 0, 0, 2], ![2, 0, 0, 0], ![2, 0, 0, 1], ![2, 0, 0, 2], ![2, 1, 0, 0], ![2, 1, 0, 1], ![2, 1, 0, 2], ![2, 1, 1, 0], ![2, 1, 1, 1], ![2, 1, 1, 2]} := by decide +kernel
  rw [← Finset.sum_filter, hf, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_singleton]
  all_goals decide +kernel

theorem S30 (g : Col → ℕ) : ∑ s, (if ok ![1, 0, 1, 0] s then g s else 0) = g ![1, 0, 1, 0] + (g ![2, 0, 1, 0] + g ![2, 1, 1, 0]) := by
  have hf : Finset.univ.filter (fun s : Col => ok ![1, 0, 1, 0] s) = {![1, 0, 1, 0], ![2, 0, 1, 0], ![2, 1, 1, 0]} := by decide +kernel
  rw [← Finset.sum_filter, hf, Finset.sum_insert, Finset.sum_insert, Finset.sum_singleton]
  all_goals decide +kernel

theorem S31 (g : Col → ℕ) : ∑ s, (if ok ![1, 0, 1, 1] s then g s else 0) = g ![1, 0, 0, 0] + (g ![1, 0, 1, 0] + (g ![2, 0, 0, 0] + (g ![2, 0, 1, 0] + (g ![2, 1, 0, 0] + g ![2, 1, 1, 0])))) := by
  have hf : Finset.univ.filter (fun s : Col => ok ![1, 0, 1, 1] s) = {![1, 0, 0, 0], ![1, 0, 1, 0], ![2, 0, 0, 0], ![2, 0, 1, 0], ![2, 1, 0, 0], ![2, 1, 1, 0]} := by decide +kernel
  rw [← Finset.sum_filter, hf, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_singleton]
  all_goals decide +kernel

theorem S32 (g : Col → ℕ) : ∑ s, (if ok ![1, 0, 1, 2] s then g s else 0) = g ![1, 0, 0, 0] + (g ![1, 0, 0, 1] + (g ![1, 0, 1, 0] + (g ![1, 0, 1, 1] + (g ![2, 0, 0, 0] + (g ![2, 0, 0, 1] + (g ![2, 0, 1, 0] + (g ![2, 0, 1, 1] + (g ![2, 1, 0, 0] + (g ![2, 1, 0, 1] + (g ![2, 1, 1, 0] + g ![2, 1, 1, 1])))))))))) := by
  have hf : Finset.univ.filter (fun s : Col => ok ![1, 0, 1, 2] s) = {![1, 0, 0, 0], ![1, 0, 0, 1], ![1, 0, 1, 0], ![1, 0, 1, 1], ![2, 0, 0, 0], ![2, 0, 0, 1], ![2, 0, 1, 0], ![2, 0, 1, 1], ![2, 1, 0, 0], ![2, 1, 0, 1], ![2, 1, 1, 0], ![2, 1, 1, 1]} := by decide +kernel
  rw [← Finset.sum_filter, hf, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_singleton]
  all_goals decide +kernel

theorem S33 (g : Col → ℕ) : ∑ s, (if ok ![1, 0, 2, 0] s then g s else 0) = g ![1, 0, 2, 0] + (g ![2, 0, 2, 0] + g ![2, 1, 2, 0]) := by
  have hf : Finset.univ.filter (fun s : Col => ok ![1, 0, 2, 0] s) = {![1, 0, 2, 0], ![2, 0, 2, 0], ![2, 1, 2, 0]} := by decide +kernel
  rw [← Finset.sum_filter, hf, Finset.sum_insert, Finset.sum_insert, Finset.sum_singleton]
  all_goals decide +kernel

theorem S34 (g : Col → ℕ) : ∑ s, (if ok ![1, 0, 2, 1] s then g s else 0) = g ![1, 0, 2, 0] + (g ![2, 0, 2, 0] + g ![2, 1, 2, 0]) := by
  have hf : Finset.univ.filter (fun s : Col => ok ![1, 0, 2, 1] s) = {![1, 0, 2, 0], ![2, 0, 2, 0], ![2, 1, 2, 0]} := by decide +kernel
  rw [← Finset.sum_filter, hf, Finset.sum_insert, Finset.sum_insert, Finset.sum_singleton]
  all_goals decide +kernel

theorem S35 (g : Col → ℕ) : ∑ s, (if ok ![1, 0, 2, 2] s then g s else 0) = g ![1, 0, 0, 0] + (g ![1, 0, 1, 0] + (g ![1, 0, 2, 0] + (g ![2, 0, 0, 0] + (g ![2, 0, 1, 0] + (g ![2, 0, 2, 0] + (g ![2, 1, 0, 0] + (g ![2, 1, 1, 0] + g ![2, 1, 2, 0]))))))) := by
  have hf : Finset.univ.filter (fun s : Col => ok ![1, 0, 2, 2] s) = {![1, 0, 0, 0], ![1, 0, 1, 0], ![1, 0, 2, 0], ![2, 0, 0, 0], ![2, 0, 1, 0], ![2, 0, 2, 0], ![2, 1, 0, 0], ![2, 1, 1, 0], ![2, 1, 2, 0]} := by decide +kernel
  rw [← Finset.sum_filter, hf, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_singleton]
  all_goals decide +kernel

theorem S36 (g : Col → ℕ) : ∑ s, (if ok ![1, 1, 0, 0] s then g s else 0) = g ![2, 1, 0, 0] := by
  have hf : Finset.univ.filter (fun s : Col => ok ![1, 1, 0, 0] s) = {![2, 1, 0, 0]} := by decide +kernel
  rw [← Finset.sum_filter, hf, Finset.sum_singleton]

theorem S37 (g : Col → ℕ) : ∑ s, (if ok ![1, 1, 0, 1] s then g s else 0) = g ![2, 1, 0, 0] + g ![2, 1, 0, 1] := by
  have hf : Finset.univ.filter (fun s : Col => ok ![1, 1, 0, 1] s) = {![2, 1, 0, 0], ![2, 1, 0, 1]} := by decide +kernel
  rw [← Finset.sum_filter, hf, Finset.sum_insert, Finset.sum_singleton]
  all_goals decide +kernel

theorem S38 (g : Col → ℕ) : ∑ s, (if ok ![1, 1, 0, 2] s then g s else 0) = g ![2, 1, 0, 0] + (g ![2, 1, 0, 1] + g ![2, 1, 0, 2]) := by
  have hf : Finset.univ.filter (fun s : Col => ok ![1, 1, 0, 2] s) = {![2, 1, 0, 0], ![2, 1, 0, 1], ![2, 1, 0, 2]} := by decide +kernel
  rw [← Finset.sum_filter, hf, Finset.sum_insert, Finset.sum_insert, Finset.sum_singleton]
  all_goals decide +kernel

theorem S39 (g : Col → ℕ) : ∑ s, (if ok ![1, 1, 1, 0] s then g s else 0) = 0 := by
  have hf : Finset.univ.filter (fun s : Col => ok ![1, 1, 1, 0] s) = ∅ := by decide +kernel
  rw [← Finset.sum_filter, hf, Finset.sum_empty]

theorem S40 (g : Col → ℕ) : ∑ s, (if ok ![1, 1, 1, 1] s then g s else 0) = g ![0, 0, 0, 0] + (g ![1, 0, 0, 0] + (g ![2, 0, 0, 0] + g ![2, 1, 0, 0])) := by
  have hf : Finset.univ.filter (fun s : Col => ok ![1, 1, 1, 1] s) = {![0, 0, 0, 0], ![1, 0, 0, 0], ![2, 0, 0, 0], ![2, 1, 0, 0]} := by decide +kernel
  rw [← Finset.sum_filter, hf, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_singleton]
  all_goals decide +kernel

theorem S41 (g : Col → ℕ) : ∑ s, (if ok ![1, 1, 1, 2] s then g s else 0) = g ![0, 0, 0, 0] + (g ![0, 0, 0, 1] + (g ![1, 0, 0, 0] + (g ![1, 0, 0, 1] + (g ![2, 0, 0, 0] + (g ![2, 0, 0, 1] + (g ![2, 1, 0, 0] + g ![2, 1, 0, 1])))))) := by
  have hf : Finset.univ.filter (fun s : Col => ok ![1, 1, 1, 2] s) = {![0, 0, 0, 0], ![0, 0, 0, 1], ![1, 0, 0, 0], ![1, 0, 0, 1], ![2, 0, 0, 0], ![2, 0, 0, 1], ![2, 1, 0, 0], ![2, 1, 0, 1]} := by decide +kernel
  rw [← Finset.sum_filter, hf, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_singleton]
  all_goals decide +kernel

theorem S42 (g : Col → ℕ) : ∑ s, (if ok ![1, 1, 2, 0] s then g s else 0) = 0 := by
  have hf : Finset.univ.filter (fun s : Col => ok ![1, 1, 2, 0] s) = ∅ := by decide +kernel
  rw [← Finset.sum_filter, hf, Finset.sum_empty]

theorem S43 (g : Col → ℕ) : ∑ s, (if ok ![1, 1, 2, 1] s then g s else 0) = 0 := by
  have hf : Finset.univ.filter (fun s : Col => ok ![1, 1, 2, 1] s) = ∅ := by decide +kernel
  rw [← Finset.sum_filter, hf, Finset.sum_empty]

theorem S44 (g : Col → ℕ) : ∑ s, (if ok ![1, 1, 2, 2] s then g s else 0) = g ![0, 0, 0, 0] + (g ![0, 0, 1, 0] + (g ![1, 0, 0, 0] + (g ![1, 0, 1, 0] + (g ![2, 0, 0, 0] + (g ![2, 0, 1, 0] + (g ![2, 1, 0, 0] + g ![2, 1, 1, 0])))))) := by
  have hf : Finset.univ.filter (fun s : Col => ok ![1, 1, 2, 2] s) = {![0, 0, 0, 0], ![0, 0, 1, 0], ![1, 0, 0, 0], ![1, 0, 1, 0], ![2, 0, 0, 0], ![2, 0, 1, 0], ![2, 1, 0, 0], ![2, 1, 1, 0]} := by decide +kernel
  rw [← Finset.sum_filter, hf, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_singleton]
  all_goals decide +kernel

theorem S45 (g : Col → ℕ) : ∑ s, (if ok ![1, 2, 0, 0] s then g s else 0) = 0 := by
  have hf : Finset.univ.filter (fun s : Col => ok ![1, 2, 0, 0] s) = ∅ := by decide +kernel
  rw [← Finset.sum_filter, hf, Finset.sum_empty]

theorem S46 (g : Col → ℕ) : ∑ s, (if ok ![1, 2, 0, 1] s then g s else 0) = 0 := by
  have hf : Finset.univ.filter (fun s : Col => ok ![1, 2, 0, 1] s) = ∅ := by decide +kernel
  rw [← Finset.sum_filter, hf, Finset.sum_empty]

theorem S47 (g : Col → ℕ) : ∑ s, (if ok ![1, 2, 0, 2] s then g s else 0) = 0 := by
  have hf : Finset.univ.filter (fun s : Col => ok ![1, 2, 0, 2] s) = ∅ := by decide +kernel
  rw [← Finset.sum_filter, hf, Finset.sum_empty]

theorem S48 (g : Col → ℕ) : ∑ s, (if ok ![1, 2, 1, 0] s then g s else 0) = 0 := by
  have hf : Finset.univ.filter (fun s : Col => ok ![1, 2, 1, 0] s) = ∅ := by decide +kernel
  rw [← Finset.sum_filter, hf, Finset.sum_empty]

theorem S49 (g : Col → ℕ) : ∑ s, (if ok ![1, 2, 1, 1] s then g s else 0) = 0 := by
  have hf : Finset.univ.filter (fun s : Col => ok ![1, 2, 1, 1] s) = ∅ := by decide +kernel
  rw [← Finset.sum_filter, hf, Finset.sum_empty]

theorem S50 (g : Col → ℕ) : ∑ s, (if ok ![1, 2, 1, 2] s then g s else 0) = 0 := by
  have hf : Finset.univ.filter (fun s : Col => ok ![1, 2, 1, 2] s) = ∅ := by decide +kernel
  rw [← Finset.sum_filter, hf, Finset.sum_empty]

theorem S51 (g : Col → ℕ) : ∑ s, (if ok ![1, 2, 2, 0] s then g s else 0) = 0 := by
  have hf : Finset.univ.filter (fun s : Col => ok ![1, 2, 2, 0] s) = ∅ := by decide +kernel
  rw [← Finset.sum_filter, hf, Finset.sum_empty]

theorem S52 (g : Col → ℕ) : ∑ s, (if ok ![1, 2, 2, 1] s then g s else 0) = 0 := by
  have hf : Finset.univ.filter (fun s : Col => ok ![1, 2, 2, 1] s) = ∅ := by decide +kernel
  rw [← Finset.sum_filter, hf, Finset.sum_empty]

theorem S53 (g : Col → ℕ) : ∑ s, (if ok ![1, 2, 2, 2] s then g s else 0) = g ![0, 0, 0, 0] + (g ![0, 1, 0, 0] + (g ![1, 0, 0, 0] + (g ![1, 1, 0, 0] + (g ![2, 0, 0, 0] + g ![2, 1, 0, 0])))) := by
  have hf : Finset.univ.filter (fun s : Col => ok ![1, 2, 2, 2] s) = {![0, 0, 0, 0], ![0, 1, 0, 0], ![1, 0, 0, 0], ![1, 1, 0, 0], ![2, 0, 0, 0], ![2, 1, 0, 0]} := by decide +kernel
  rw [← Finset.sum_filter, hf, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_singleton]
  all_goals decide +kernel

theorem S54 (g : Col → ℕ) : ∑ s, (if ok ![2, 0, 0, 0] s then g s else 0) = g ![2, 0, 0, 0] := by
  have hf : Finset.univ.filter (fun s : Col => ok ![2, 0, 0, 0] s) = {![2, 0, 0, 0]} := by decide +kernel
  rw [← Finset.sum_filter, hf, Finset.sum_singleton]

theorem S55 (g : Col → ℕ) : ∑ s, (if ok ![2, 0, 0, 1] s then g s else 0) = g ![2, 0, 0, 0] + g ![2, 0, 0, 1] := by
  have hf : Finset.univ.filter (fun s : Col => ok ![2, 0, 0, 1] s) = {![2, 0, 0, 0], ![2, 0, 0, 1]} := by decide +kernel
  rw [← Finset.sum_filter, hf, Finset.sum_insert, Finset.sum_singleton]
  all_goals decide +kernel

theorem S56 (g : Col → ℕ) : ∑ s, (if ok ![2, 0, 0, 2] s then g s else 0) = g ![2, 0, 0, 0] + (g ![2, 0, 0, 1] + g ![2, 0, 0, 2]) := by
  have hf : Finset.univ.filter (fun s : Col => ok ![2, 0, 0, 2] s) = {![2, 0, 0, 0], ![2, 0, 0, 1], ![2, 0, 0, 2]} := by decide +kernel
  rw [← Finset.sum_filter, hf, Finset.sum_insert, Finset.sum_insert, Finset.sum_singleton]
  all_goals decide +kernel

theorem S57 (g : Col → ℕ) : ∑ s, (if ok ![2, 0, 1, 0] s then g s else 0) = g ![2, 0, 1, 0] := by
  have hf : Finset.univ.filter (fun s : Col => ok ![2, 0, 1, 0] s) = {![2, 0, 1, 0]} := by decide +kernel
  rw [← Finset.sum_filter, hf, Finset.sum_singleton]

theorem S58 (g : Col → ℕ) : ∑ s, (if ok ![2, 0, 1, 1] s then g s else 0) = g ![2, 0, 0, 0] + g ![2, 0, 1, 0] := by
  have hf : Finset.univ.filter (fun s : Col => ok ![2, 0, 1, 1] s) = {![2, 0, 0, 0], ![2, 0, 1, 0]} := by decide +kernel
  rw [← Finset.sum_filter, hf, Finset.sum_insert, Finset.sum_singleton]
  all_goals decide +kernel

theorem S59 (g : Col → ℕ) : ∑ s, (if ok ![2, 0, 1, 2] s then g s else 0) = g ![2, 0, 0, 0] + (g ![2, 0, 0, 1] + (g ![2, 0, 1, 0] + g ![2, 0, 1, 1])) := by
  have hf : Finset.univ.filter (fun s : Col => ok ![2, 0, 1, 2] s) = {![2, 0, 0, 0], ![2, 0, 0, 1], ![2, 0, 1, 0], ![2, 0, 1, 1]} := by decide +kernel
  rw [← Finset.sum_filter, hf, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_singleton]
  all_goals decide +kernel

theorem S60 (g : Col → ℕ) : ∑ s, (if ok ![2, 0, 2, 0] s then g s else 0) = g ![2, 0, 2, 0] := by
  have hf : Finset.univ.filter (fun s : Col => ok ![2, 0, 2, 0] s) = {![2, 0, 2, 0]} := by decide +kernel
  rw [← Finset.sum_filter, hf, Finset.sum_singleton]

theorem S61 (g : Col → ℕ) : ∑ s, (if ok ![2, 0, 2, 1] s then g s else 0) = g ![2, 0, 2, 0] := by
  have hf : Finset.univ.filter (fun s : Col => ok ![2, 0, 2, 1] s) = {![2, 0, 2, 0]} := by decide +kernel
  rw [← Finset.sum_filter, hf, Finset.sum_singleton]

theorem S62 (g : Col → ℕ) : ∑ s, (if ok ![2, 0, 2, 2] s then g s else 0) = g ![2, 0, 0, 0] + (g ![2, 0, 1, 0] + g ![2, 0, 2, 0]) := by
  have hf : Finset.univ.filter (fun s : Col => ok ![2, 0, 2, 2] s) = {![2, 0, 0, 0], ![2, 0, 1, 0], ![2, 0, 2, 0]} := by decide +kernel
  rw [← Finset.sum_filter, hf, Finset.sum_insert, Finset.sum_insert, Finset.sum_singleton]
  all_goals decide +kernel

theorem S63 (g : Col → ℕ) : ∑ s, (if ok ![2, 1, 0, 0] s then g s else 0) = 0 := by
  have hf : Finset.univ.filter (fun s : Col => ok ![2, 1, 0, 0] s) = ∅ := by decide +kernel
  rw [← Finset.sum_filter, hf, Finset.sum_empty]

theorem S64 (g : Col → ℕ) : ∑ s, (if ok ![2, 1, 0, 1] s then g s else 0) = 0 := by
  have hf : Finset.univ.filter (fun s : Col => ok ![2, 1, 0, 1] s) = ∅ := by decide +kernel
  rw [← Finset.sum_filter, hf, Finset.sum_empty]

theorem S65 (g : Col → ℕ) : ∑ s, (if ok ![2, 1, 0, 2] s then g s else 0) = 0 := by
  have hf : Finset.univ.filter (fun s : Col => ok ![2, 1, 0, 2] s) = ∅ := by decide +kernel
  rw [← Finset.sum_filter, hf, Finset.sum_empty]

theorem S66 (g : Col → ℕ) : ∑ s, (if ok ![2, 1, 1, 0] s then g s else 0) = 0 := by
  have hf : Finset.univ.filter (fun s : Col => ok ![2, 1, 1, 0] s) = ∅ := by decide +kernel
  rw [← Finset.sum_filter, hf, Finset.sum_empty]

theorem S67 (g : Col → ℕ) : ∑ s, (if ok ![2, 1, 1, 1] s then g s else 0) = g ![2, 0, 0, 0] := by
  have hf : Finset.univ.filter (fun s : Col => ok ![2, 1, 1, 1] s) = {![2, 0, 0, 0]} := by decide +kernel
  rw [← Finset.sum_filter, hf, Finset.sum_singleton]

theorem S68 (g : Col → ℕ) : ∑ s, (if ok ![2, 1, 1, 2] s then g s else 0) = g ![2, 0, 0, 0] + g ![2, 0, 0, 1] := by
  have hf : Finset.univ.filter (fun s : Col => ok ![2, 1, 1, 2] s) = {![2, 0, 0, 0], ![2, 0, 0, 1]} := by decide +kernel
  rw [← Finset.sum_filter, hf, Finset.sum_insert, Finset.sum_singleton]
  all_goals decide +kernel

theorem S69 (g : Col → ℕ) : ∑ s, (if ok ![2, 1, 2, 0] s then g s else 0) = 0 := by
  have hf : Finset.univ.filter (fun s : Col => ok ![2, 1, 2, 0] s) = ∅ := by decide +kernel
  rw [← Finset.sum_filter, hf, Finset.sum_empty]

theorem S70 (g : Col → ℕ) : ∑ s, (if ok ![2, 1, 2, 1] s then g s else 0) = 0 := by
  have hf : Finset.univ.filter (fun s : Col => ok ![2, 1, 2, 1] s) = ∅ := by decide +kernel
  rw [← Finset.sum_filter, hf, Finset.sum_empty]

theorem S71 (g : Col → ℕ) : ∑ s, (if ok ![2, 1, 2, 2] s then g s else 0) = g ![2, 0, 0, 0] + g ![2, 0, 1, 0] := by
  have hf : Finset.univ.filter (fun s : Col => ok ![2, 1, 2, 2] s) = {![2, 0, 0, 0], ![2, 0, 1, 0]} := by decide +kernel
  rw [← Finset.sum_filter, hf, Finset.sum_insert, Finset.sum_singleton]
  all_goals decide +kernel

theorem S72 (g : Col → ℕ) : ∑ s, (if ok ![2, 2, 0, 0] s then g s else 0) = 0 := by
  have hf : Finset.univ.filter (fun s : Col => ok ![2, 2, 0, 0] s) = ∅ := by decide +kernel
  rw [← Finset.sum_filter, hf, Finset.sum_empty]

theorem S73 (g : Col → ℕ) : ∑ s, (if ok ![2, 2, 0, 1] s then g s else 0) = 0 := by
  have hf : Finset.univ.filter (fun s : Col => ok ![2, 2, 0, 1] s) = ∅ := by decide +kernel
  rw [← Finset.sum_filter, hf, Finset.sum_empty]

theorem S74 (g : Col → ℕ) : ∑ s, (if ok ![2, 2, 0, 2] s then g s else 0) = 0 := by
  have hf : Finset.univ.filter (fun s : Col => ok ![2, 2, 0, 2] s) = ∅ := by decide +kernel
  rw [← Finset.sum_filter, hf, Finset.sum_empty]

theorem S75 (g : Col → ℕ) : ∑ s, (if ok ![2, 2, 1, 0] s then g s else 0) = 0 := by
  have hf : Finset.univ.filter (fun s : Col => ok ![2, 2, 1, 0] s) = ∅ := by decide +kernel
  rw [← Finset.sum_filter, hf, Finset.sum_empty]

theorem S76 (g : Col → ℕ) : ∑ s, (if ok ![2, 2, 1, 1] s then g s else 0) = 0 := by
  have hf : Finset.univ.filter (fun s : Col => ok ![2, 2, 1, 1] s) = ∅ := by decide +kernel
  rw [← Finset.sum_filter, hf, Finset.sum_empty]

theorem S77 (g : Col → ℕ) : ∑ s, (if ok ![2, 2, 1, 2] s then g s else 0) = 0 := by
  have hf : Finset.univ.filter (fun s : Col => ok ![2, 2, 1, 2] s) = ∅ := by decide +kernel
  rw [← Finset.sum_filter, hf, Finset.sum_empty]

theorem S78 (g : Col → ℕ) : ∑ s, (if ok ![2, 2, 2, 0] s then g s else 0) = 0 := by
  have hf : Finset.univ.filter (fun s : Col => ok ![2, 2, 2, 0] s) = ∅ := by decide +kernel
  rw [← Finset.sum_filter, hf, Finset.sum_empty]

theorem S79 (g : Col → ℕ) : ∑ s, (if ok ![2, 2, 2, 1] s then g s else 0) = 0 := by
  have hf : Finset.univ.filter (fun s : Col => ok ![2, 2, 2, 1] s) = ∅ := by decide +kernel
  rw [← Finset.sum_filter, hf, Finset.sum_empty]

theorem S80 (g : Col → ℕ) : ∑ s, (if ok ![2, 2, 2, 2] s then g s else 0) = g ![0, 0, 0, 0] + (g ![1, 0, 0, 0] + g ![2, 0, 0, 0]) := by
  have hf : Finset.univ.filter (fun s : Col => ok ![2, 2, 2, 2] s) = {![0, 0, 0, 0], ![1, 0, 0, 0], ![2, 0, 0, 0]} := by decide +kernel
  rw [← Finset.sum_filter, hf, Finset.sum_insert, Finset.sum_insert, Finset.sum_singleton]
  all_goals decide +kernel

theorem Hs (m : ℕ) :
    H (m + 1) ![0, 0, 0, 0] = H m ![0, 0, 0, 0] + (H m ![1, 0, 0, 0] + (H m ![1, 1, 0, 0] + (H m ![1, 1, 1, 0] + (H m ![1, 1, 1, 1] + (H m ![2, 0, 0, 0] + (H m ![2, 1, 0, 0] + (H m ![2, 1, 1, 0] + (H m ![2, 1, 1, 1] + (H m ![2, 2, 0, 0] + (H m ![2, 2, 1, 0] + (H m ![2, 2, 1, 1] + (H m ![2, 2, 2, 0] + (H m ![2, 2, 2, 1] + H m ![2, 2, 2, 2]))))))))))))) ∧
    H (m + 1) ![0, 0, 0, 1] = H m ![0, 0, 0, 0] + (H m ![0, 0, 0, 1] + (H m ![1, 0, 0, 0] + (H m ![1, 0, 0, 1] + (H m ![1, 1, 0, 0] + (H m ![1, 1, 0, 1] + (H m ![1, 1, 1, 0] + (H m ![1, 1, 1, 1] + (H m ![2, 0, 0, 0] + (H m ![2, 0, 0, 1] + (H m ![2, 1, 0, 0] + (H m ![2, 1, 0, 1] + (H m ![2, 1, 1, 0] + (H m ![2, 1, 1, 1] + (H m ![2, 2, 0, 0] + (H m ![2, 2, 0, 1] + (H m ![2, 2, 1, 0] + (H m ![2, 2, 1, 1] + (H m ![2, 2, 2, 0] + (H m ![2, 2, 2, 1] + H m ![2, 2, 2, 2]))))))))))))))))))) ∧
    H (m + 1) ![0, 0, 0, 2] = H m ![0, 0, 0, 0] + (H m ![0, 0, 0, 1] + (H m ![0, 0, 0, 2] + (H m ![1, 0, 0, 0] + (H m ![1, 0, 0, 1] + (H m ![1, 0, 0, 2] + (H m ![1, 1, 0, 0] + (H m ![1, 1, 0, 1] + (H m ![1, 1, 0, 2] + (H m ![1, 1, 1, 0] + (H m ![1, 1, 1, 1] + (H m ![1, 1, 1, 2] + (H m ![2, 0, 0, 0] + (H m ![2, 0, 0, 1] + (H m ![2, 0, 0, 2] + (H m ![2, 1, 0, 0] + (H m ![2, 1, 0, 1] + (H m ![2, 1, 0, 2] + (H m ![2, 1, 1, 0] + (H m ![2, 1, 1, 1] + (H m ![2, 1, 1, 2] + (H m ![2, 2, 0, 0] + (H m ![2, 2, 0, 1] + (H m ![2, 2, 0, 2] + (H m ![2, 2, 1, 0] + (H m ![2, 2, 1, 1] + (H m ![2, 2, 1, 2] + (H m ![2, 2, 2, 0] + (H m ![2, 2, 2, 1] + H m ![2, 2, 2, 2])))))))))))))))))))))))))))) ∧
    H (m + 1) ![0, 0, 1, 0] = H m ![0, 0, 1, 0] + (H m ![1, 0, 1, 0] + (H m ![1, 1, 1, 0] + (H m ![2, 0, 1, 0] + (H m ![2, 1, 1, 0] + (H m ![2, 2, 1, 0] + (H m ![2, 2, 2, 0] + H m ![2, 2, 2, 1])))))) ∧
    H (m + 1) ![0, 0, 1, 1] = H m ![0, 0, 0, 0] + (H m ![0, 0, 1, 0] + (H m ![1, 0, 0, 0] + (H m ![1, 0, 1, 0] + (H m ![1, 1, 0, 0] + (H m ![1, 1, 1, 0] + (H m ![2, 0, 0, 0] + (H m ![2, 0, 1, 0] + (H m ![2, 1, 0, 0] + (H m ![2, 1, 1, 0] + (H m ![2, 2, 0, 0] + (H m ![2, 2, 1, 0] + (H m ![2, 2, 2, 0] + H m ![2, 2, 2, 1])))))))))))) ∧
    H (m + 1) ![0, 0, 1, 2] = H m ![0, 0, 0, 0] + (H m ![0, 0, 0, 1] + (H m ![0, 0, 1, 0] + (H m ![0, 0, 1, 1] + (H m ![1, 0, 0, 0] + (H m ![1, 0, 0, 1] + (H m ![1, 0, 1, 0] + (H m ![1, 0, 1, 1] + (H m ![1, 1, 0, 0] + (H m ![1, 1, 0, 1] + (H m ![1, 1, 1, 0] + (H m ![1, 1, 1, 1] + (H m ![2, 0, 0, 0] + (H m ![2, 0, 0, 1] + (H m ![2, 0, 1, 0] + (H m ![2, 0, 1, 1] + (H m ![2, 1, 0, 0] + (H m ![2, 1, 0, 1] + (H m ![2, 1, 1, 0] + (H m ![2, 1, 1, 1] + (H m ![2, 2, 0, 0] + (H m ![2, 2, 0, 1] + (H m ![2, 2, 1, 0] + (H m ![2, 2, 1, 1] + (H m ![2, 2, 2, 0] + H m ![2, 2, 2, 1])))))))))))))))))))))))) ∧
    H (m + 1) ![0, 0, 2, 0] = H m ![0, 0, 2, 0] + (H m ![1, 0, 2, 0] + (H m ![1, 1, 2, 0] + (H m ![2, 0, 2, 0] + (H m ![2, 1, 2, 0] + H m ![2, 2, 2, 0])))) ∧
    H (m + 1) ![0, 0, 2, 1] = H m ![0, 0, 2, 0] + (H m ![1, 0, 2, 0] + (H m ![1, 1, 2, 0] + (H m ![2, 0, 2, 0] + (H m ![2, 1, 2, 0] + H m ![2, 2, 2, 0])))) ∧
    H (m + 1) ![0, 0, 2, 2] = H m ![0, 0, 0, 0] + (H m ![0, 0, 1, 0] + (H m ![0, 0, 2, 0] + (H m ![1, 0, 0, 0] + (H m ![1, 0, 1, 0] + (H m ![1, 0, 2, 0] + (H m ![1, 1, 0, 0] + (H m ![1, 1, 1, 0] + (H m ![1, 1, 2, 0] + (H m ![2, 0, 0, 0] + (H m ![2, 0, 1, 0] + (H m ![2, 0, 2, 0] + (H m ![2, 1, 0, 0] + (H m ![2, 1, 1, 0] + (H m ![2, 1, 2, 0] + (H m ![2, 2, 0, 0] + (H m ![2, 2, 1, 0] + H m ![2, 2, 2, 0])))))))))))))))) ∧
    H (m + 1) ![0, 1, 0, 0] = H m ![0, 1, 0, 0] + (H m ![1, 1, 0, 0] + (H m ![2, 1, 0, 0] + (H m ![2, 2, 0, 0] + (H m ![2, 2, 1, 0] + H m ![2, 2, 1, 1])))) ∧
    H (m + 1) ![0, 1, 0, 1] = H m ![0, 1, 0, 0] + (H m ![0, 1, 0, 1] + (H m ![1, 1, 0, 0] + (H m ![1, 1, 0, 1] + (H m ![2, 1, 0, 0] + (H m ![2, 1, 0, 1] + (H m ![2, 2, 0, 0] + (H m ![2, 2, 0, 1] + (H m ![2, 2, 1, 0] + H m ![2, 2, 1, 1])))))))) ∧
    H (m + 1) ![0, 1, 0, 2] = H m ![0, 1, 0, 0] + (H m ![0, 1, 0, 1] + (H m ![0, 1, 0, 2] + (H m ![1, 1, 0, 0] + (H m ![1, 1, 0, 1] + (H m ![1, 1, 0, 2] + (H m ![2, 1, 0, 0] + (H m ![2, 1, 0, 1] + (H m ![2, 1, 0, 2] + (H m ![2, 2, 0, 0] + (H m ![2, 2, 0, 1] + (H m ![2, 2, 0, 2] + (H m ![2, 2, 1, 0] + (H m ![2, 2, 1, 1] + H m ![2, 2, 1, 2]))))))))))))) ∧
    H (m + 1) ![0, 1, 1, 0] = H m ![2, 2, 1, 0] ∧
    H (m + 1) ![0, 1, 1, 1] = H m ![0, 0, 0, 0] + (H m ![0, 1, 0, 0] + (H m ![1, 0, 0, 0] + (H m ![1, 1, 0, 0] + (H m ![2, 0, 0, 0] + (H m ![2, 1, 0, 0] + (H m ![2, 2, 0, 0] + H m ![2, 2, 1, 0])))))) ∧
    H (m + 1) ![0, 1, 1, 2] = H m ![0, 0, 0, 0] + (H m ![0, 0, 0, 1] + (H m ![0, 1, 0, 0] + (H m ![0, 1, 0, 1] + (H m ![1, 0, 0, 0] + (H m ![1, 0, 0, 1] + (H m ![1, 1, 0, 0] + (H m ![1, 1, 0, 1] + (H m ![2, 0, 0, 0] + (H m ![2, 0, 0, 1] + (H m ![2, 1, 0, 0] + (H m ![2, 1, 0, 1] + (H m ![2, 2, 0, 0] + (H m ![2, 2, 0, 1] + (H m ![2, 2, 1, 0] + H m ![2, 2, 1, 1])))))))))))))) ∧
    H (m + 1) ![0, 1, 2, 0] = 0 ∧
    H (m + 1) ![0, 1, 2, 1] = 0 ∧
    H (m + 1) ![0, 1, 2, 2] = H m ![0, 0, 0, 0] + (H m ![0, 0, 1, 0] + (H m ![0, 1, 0, 0] + (H m ![0, 1, 1, 0] + (H m ![1, 0, 0, 0] + (H m ![1, 0, 1, 0] + (H m ![1, 1, 0, 0] + (H m ![1, 1, 1, 0] + (H m ![2, 0, 0, 0] + (H m ![2, 0, 1, 0] + (H m ![2, 1, 0, 0] + (H m ![2, 1, 1, 0] + (H m ![2, 2, 0, 0] + H m ![2, 2, 1, 0])))))))))))) ∧
    H (m + 1) ![0, 2, 0, 0] = H m ![0, 2, 0, 0] + (H m ![1, 2, 0, 0] + H m ![2, 2, 0, 0]) ∧
    H (m + 1) ![0, 2, 0, 1] = H m ![0, 2, 0, 0] + (H m ![0, 2, 0, 1] + (H m ![1, 2, 0, 0] + (H m ![1, 2, 0, 1] + (H m ![2, 2, 0, 0] + H m ![2, 2, 0, 1])))) ∧
    H (m + 1) ![0, 2, 0, 2] = H m ![0, 2, 0, 0] + (H m ![0, 2, 0, 1] + (H m ![0, 2, 0, 2] + (H m ![1, 2, 0, 0] + (H m ![1, 2, 0, 1] + (H m ![1, 2, 0, 2] + (H m ![2, 2, 0, 0] + (H m ![2, 2, 0, 1] + H m ![2, 2, 0, 2]))))))) ∧
    H (m + 1) ![0, 2, 1, 0] = 0 ∧
    H (m + 1) ![0, 2, 1, 1] = H m ![0, 2, 0, 0] + (H m ![1, 2, 0, 0] + H m ![2, 2, 0, 0]) ∧
    H (m + 1) ![0, 2, 1, 2] = H m ![0, 2, 0, 0] + (H m ![0, 2, 0, 1] + (H m ![1, 2, 0, 0] + (H m ![1, 2, 0, 1] + (H m ![2, 2, 0, 0] + H m ![2, 2, 0, 1])))) ∧
    H (m + 1) ![0, 2, 2, 0] = 0 ∧
    H (m + 1) ![0, 2, 2, 1] = 0 ∧
    H (m + 1) ![0, 2, 2, 2] = H m ![0, 0, 0, 0] + (H m ![0, 1, 0, 0] + (H m ![0, 2, 0, 0] + (H m ![1, 0, 0, 0] + (H m ![1, 1, 0, 0] + (H m ![1, 2, 0, 0] + (H m ![2, 0, 0, 0] + (H m ![2, 1, 0, 0] + H m ![2, 2, 0, 0]))))))) ∧
    H (m + 1) ![1, 0, 0, 0] = H m ![1, 0, 0, 0] + (H m ![2, 0, 0, 0] + (H m ![2, 1, 0, 0] + (H m ![2, 1, 1, 0] + H m ![2, 1, 1, 1]))) ∧
    H (m + 1) ![1, 0, 0, 1] = H m ![1, 0, 0, 0] + (H m ![1, 0, 0, 1] + (H m ![2, 0, 0, 0] + (H m ![2, 0, 0, 1] + (H m ![2, 1, 0, 0] + (H m ![2, 1, 0, 1] + (H m ![2, 1, 1, 0] + H m ![2, 1, 1, 1])))))) ∧
    H (m + 1) ![1, 0, 0, 2] = H m ![1, 0, 0, 0] + (H m ![1, 0, 0, 1] + (H m ![1, 0, 0, 2] + (H m ![2, 0, 0, 0] + (H m ![2, 0, 0, 1] + (H m ![2, 0, 0, 2] + (H m ![2, 1, 0, 0] + (H m ![2, 1, 0, 1] + (H m ![2, 1, 0, 2] + (H m ![2, 1, 1, 0] + (H m ![2, 1, 1, 1] + H m ![2, 1, 1, 2])))))))))) ∧
    H (m + 1) ![1, 0, 1, 0] = H m ![1, 0, 1, 0] + (H m ![2, 0, 1, 0] + H m ![2, 1, 1, 0]) ∧
    H (m + 1) ![1, 0, 1, 1] = H m ![1, 0, 0, 0] + (H m ![1, 0, 1, 0] + (H m ![2, 0, 0, 0] + (H m ![2, 0, 1, 0] + (H m ![2, 1, 0, 0] + H m ![2, 1, 1, 0])))) ∧
    H (m + 1) ![1, 0, 1, 2] = H m ![1, 0, 0, 0] + (H m ![1, 0, 0, 1] + (H m ![1, 0, 1, 0] + (H m ![1, 0, 1, 1] + (H m ![2, 0, 0, 0] + (H m ![2, 0, 0, 1] + (H m ![2, 0, 1, 0] + (H m ![2, 0, 1, 1] + (H m ![2, 1, 0, 0] + (H m ![2, 1, 0, 1] + (H m ![2, 1, 1, 0] + H m ![2, 1, 1, 1])))))))))) ∧
    H (m + 1) ![1, 0, 2, 0] = H m ![1, 0, 2, 0] + (H m ![2, 0, 2, 0] + H m ![2, 1, 2, 0]) ∧
    H (m + 1) ![1, 0, 2, 1] = H m ![1, 0, 2, 0] + (H m ![2, 0, 2, 0] + H m ![2, 1, 2, 0]) ∧
    H (m + 1) ![1, 0, 2, 2] = H m ![1, 0, 0, 0] + (H m ![1, 0, 1, 0] + (H m ![1, 0, 2, 0] + (H m ![2, 0, 0, 0] + (H m ![2, 0, 1, 0] + (H m ![2, 0, 2, 0] + (H m ![2, 1, 0, 0] + (H m ![2, 1, 1, 0] + H m ![2, 1, 2, 0]))))))) ∧
    H (m + 1) ![1, 1, 0, 0] = H m ![2, 1, 0, 0] ∧
    H (m + 1) ![1, 1, 0, 1] = H m ![2, 1, 0, 0] + H m ![2, 1, 0, 1] ∧
    H (m + 1) ![1, 1, 0, 2] = H m ![2, 1, 0, 0] + (H m ![2, 1, 0, 1] + H m ![2, 1, 0, 2]) ∧
    H (m + 1) ![1, 1, 1, 0] = 0 ∧
    H (m + 1) ![1, 1, 1, 1] = H m ![0, 0, 0, 0] + (H m ![1, 0, 0, 0] + (H m ![2, 0, 0, 0] + H m ![2, 1, 0, 0])) ∧
    H (m + 1) ![1, 1, 1, 2] = H m ![0, 0, 0, 0] + (H m ![0, 0, 0, 1] + (H m ![1, 0, 0, 0] + (H m ![1, 0, 0, 1] + (H m ![2, 0, 0, 0] + (H m ![2, 0, 0, 1] + (H m ![2, 1, 0, 0] + H m ![2, 1, 0, 1])))))) ∧
    H (m + 1) ![1, 1, 2, 0] = 0 ∧
    H (m + 1) ![1, 1, 2, 1] = 0 ∧
    H (m + 1) ![1, 1, 2, 2] = H m ![0, 0, 0, 0] + (H m ![0, 0, 1, 0] + (H m ![1, 0, 0, 0] + (H m ![1, 0, 1, 0] + (H m ![2, 0, 0, 0] + (H m ![2, 0, 1, 0] + (H m ![2, 1, 0, 0] + H m ![2, 1, 1, 0])))))) ∧
    H (m + 1) ![1, 2, 0, 0] = 0 ∧
    H (m + 1) ![1, 2, 0, 1] = 0 ∧
    H (m + 1) ![1, 2, 0, 2] = 0 ∧
    H (m + 1) ![1, 2, 1, 0] = 0 ∧
    H (m + 1) ![1, 2, 1, 1] = 0 ∧
    H (m + 1) ![1, 2, 1, 2] = 0 ∧
    H (m + 1) ![1, 2, 2, 0] = 0 ∧
    H (m + 1) ![1, 2, 2, 1] = 0 ∧
    H (m + 1) ![1, 2, 2, 2] = H m ![0, 0, 0, 0] + (H m ![0, 1, 0, 0] + (H m ![1, 0, 0, 0] + (H m ![1, 1, 0, 0] + (H m ![2, 0, 0, 0] + H m ![2, 1, 0, 0])))) ∧
    H (m + 1) ![2, 0, 0, 0] = H m ![2, 0, 0, 0] ∧
    H (m + 1) ![2, 0, 0, 1] = H m ![2, 0, 0, 0] + H m ![2, 0, 0, 1] ∧
    H (m + 1) ![2, 0, 0, 2] = H m ![2, 0, 0, 0] + (H m ![2, 0, 0, 1] + H m ![2, 0, 0, 2]) ∧
    H (m + 1) ![2, 0, 1, 0] = H m ![2, 0, 1, 0] ∧
    H (m + 1) ![2, 0, 1, 1] = H m ![2, 0, 0, 0] + H m ![2, 0, 1, 0] ∧
    H (m + 1) ![2, 0, 1, 2] = H m ![2, 0, 0, 0] + (H m ![2, 0, 0, 1] + (H m ![2, 0, 1, 0] + H m ![2, 0, 1, 1])) ∧
    H (m + 1) ![2, 0, 2, 0] = H m ![2, 0, 2, 0] ∧
    H (m + 1) ![2, 0, 2, 1] = H m ![2, 0, 2, 0] ∧
    H (m + 1) ![2, 0, 2, 2] = H m ![2, 0, 0, 0] + (H m ![2, 0, 1, 0] + H m ![2, 0, 2, 0]) ∧
    H (m + 1) ![2, 1, 0, 0] = 0 ∧
    H (m + 1) ![2, 1, 0, 1] = 0 ∧
    H (m + 1) ![2, 1, 0, 2] = 0 ∧
    H (m + 1) ![2, 1, 1, 0] = 0 ∧
    H (m + 1) ![2, 1, 1, 1] = H m ![2, 0, 0, 0] ∧
    H (m + 1) ![2, 1, 1, 2] = H m ![2, 0, 0, 0] + H m ![2, 0, 0, 1] ∧
    H (m + 1) ![2, 1, 2, 0] = 0 ∧
    H (m + 1) ![2, 1, 2, 1] = 0 ∧
    H (m + 1) ![2, 1, 2, 2] = H m ![2, 0, 0, 0] + H m ![2, 0, 1, 0] ∧
    H (m + 1) ![2, 2, 0, 0] = 0 ∧
    H (m + 1) ![2, 2, 0, 1] = 0 ∧
    H (m + 1) ![2, 2, 0, 2] = 0 ∧
    H (m + 1) ![2, 2, 1, 0] = 0 ∧
    H (m + 1) ![2, 2, 1, 1] = 0 ∧
    H (m + 1) ![2, 2, 1, 2] = 0 ∧
    H (m + 1) ![2, 2, 2, 0] = 0 ∧
    H (m + 1) ![2, 2, 2, 1] = 0 ∧
    H (m + 1) ![2, 2, 2, 2] = H m ![0, 0, 0, 0] + (H m ![1, 0, 0, 0] + H m ![2, 0, 0, 0]) := by
  exact ⟨by rw [H_succ, S0], by rw [H_succ, S1], by rw [H_succ, S2], by rw [H_succ, S3], by rw [H_succ, S4], by rw [H_succ, S5], by rw [H_succ, S6], by rw [H_succ, S7], by rw [H_succ, S8], by rw [H_succ, S9], by rw [H_succ, S10], by rw [H_succ, S11], by rw [H_succ, S12], by rw [H_succ, S13], by rw [H_succ, S14], by rw [H_succ, S15], by rw [H_succ, S16], by rw [H_succ, S17], by rw [H_succ, S18], by rw [H_succ, S19], by rw [H_succ, S20], by rw [H_succ, S21], by rw [H_succ, S22], by rw [H_succ, S23], by rw [H_succ, S24], by rw [H_succ, S25], by rw [H_succ, S26], by rw [H_succ, S27], by rw [H_succ, S28], by rw [H_succ, S29], by rw [H_succ, S30], by rw [H_succ, S31], by rw [H_succ, S32], by rw [H_succ, S33], by rw [H_succ, S34], by rw [H_succ, S35], by rw [H_succ, S36], by rw [H_succ, S37], by rw [H_succ, S38], by rw [H_succ, S39], by rw [H_succ, S40], by rw [H_succ, S41], by rw [H_succ, S42], by rw [H_succ, S43], by rw [H_succ, S44], by rw [H_succ, S45], by rw [H_succ, S46], by rw [H_succ, S47], by rw [H_succ, S48], by rw [H_succ, S49], by rw [H_succ, S50], by rw [H_succ, S51], by rw [H_succ, S52], by rw [H_succ, S53], by rw [H_succ, S54], by rw [H_succ, S55], by rw [H_succ, S56], by rw [H_succ, S57], by rw [H_succ, S58], by rw [H_succ, S59], by rw [H_succ, S60], by rw [H_succ, S61], by rw [H_succ, S62], by rw [H_succ, S63], by rw [H_succ, S64], by rw [H_succ, S65], by rw [H_succ, S66], by rw [H_succ, S67], by rw [H_succ, S68], by rw [H_succ, S69], by rw [H_succ, S70], by rw [H_succ, S71], by rw [H_succ, S72], by rw [H_succ, S73], by rw [H_succ, S74], by rw [H_succ, S75], by rw [H_succ, S76], by rw [H_succ, S77], by rw [H_succ, S78], by rw [H_succ, S79], by rw [H_succ, S80]⟩

theorem B1 :
    H 1 ![0, 0, 0, 0] = 15 ∧
    H 1 ![0, 0, 0, 1] = 21 ∧
    H 1 ![0, 0, 0, 2] = 30 ∧
    H 1 ![0, 0, 1, 0] = 8 ∧
    H 1 ![0, 0, 1, 1] = 14 ∧
    H 1 ![0, 0, 1, 2] = 26 ∧
    H 1 ![0, 0, 2, 0] = 6 ∧
    H 1 ![0, 0, 2, 1] = 6 ∧
    H 1 ![0, 0, 2, 2] = 18 ∧
    H 1 ![0, 1, 0, 0] = 6 ∧
    H 1 ![0, 1, 0, 1] = 10 ∧
    H 1 ![0, 1, 0, 2] = 15 ∧
    H 1 ![0, 1, 1, 0] = 1 ∧
    H 1 ![0, 1, 1, 1] = 8 ∧
    H 1 ![0, 1, 1, 2] = 16 ∧
    H 1 ![0, 1, 2, 0] = 0 ∧
    H 1 ![0, 1, 2, 1] = 0 ∧
    H 1 ![0, 1, 2, 2] = 14 ∧
    H 1 ![0, 2, 0, 0] = 3 ∧
    H 1 ![0, 2, 0, 1] = 6 ∧
    H 1 ![0, 2, 0, 2] = 9 ∧
    H 1 ![0, 2, 1, 0] = 0 ∧
    H 1 ![0, 2, 1, 1] = 3 ∧
    H 1 ![0, 2, 1, 2] = 6 ∧
    H 1 ![0, 2, 2, 0] = 0 ∧
    H 1 ![0, 2, 2, 1] = 0 ∧
    H 1 ![0, 2, 2, 2] = 9 ∧
    H 1 ![1, 0, 0, 0] = 5 ∧
    H 1 ![1, 0, 0, 1] = 8 ∧
    H 1 ![1, 0, 0, 2] = 12 ∧
    H 1 ![1, 0, 1, 0] = 3 ∧
    H 1 ![1, 0, 1, 1] = 6 ∧
    H 1 ![1, 0, 1, 2] = 12 ∧
    H 1 ![1, 0, 2, 0] = 3 ∧
    H 1 ![1, 0, 2, 1] = 3 ∧
    H 1 ![1, 0, 2, 2] = 9 ∧
    H 1 ![1, 1, 0, 0] = 1 ∧
    H 1 ![1, 1, 0, 1] = 2 ∧
    H 1 ![1, 1, 0, 2] = 3 ∧
    H 1 ![1, 1, 1, 0] = 0 ∧
    H 1 ![1, 1, 1, 1] = 4 ∧
    H 1 ![1, 1, 1, 2] = 8 ∧
    H 1 ![1, 1, 2, 0] = 0 ∧
    H 1 ![1, 1, 2, 1] = 0 ∧
    H 1 ![1, 1, 2, 2] = 8 ∧
    H 1 ![1, 2, 0, 0] = 0 ∧
    H 1 ![1, 2, 0, 1] = 0 ∧
    H 1 ![1, 2, 0, 2] = 0 ∧
    H 1 ![1, 2, 1, 0] = 0 ∧
    H 1 ![1, 2, 1, 1] = 0 ∧
    H 1 ![1, 2, 1, 2] = 0 ∧
    H 1 ![1, 2, 2, 0] = 0 ∧
    H 1 ![1, 2, 2, 1] = 0 ∧
    H 1 ![1, 2, 2, 2] = 6 ∧
    H 1 ![2, 0, 0, 0] = 1 ∧
    H 1 ![2, 0, 0, 1] = 2 ∧
    H 1 ![2, 0, 0, 2] = 3 ∧
    H 1 ![2, 0, 1, 0] = 1 ∧
    H 1 ![2, 0, 1, 1] = 2 ∧
    H 1 ![2, 0, 1, 2] = 4 ∧
    H 1 ![2, 0, 2, 0] = 1 ∧
    H 1 ![2, 0, 2, 1] = 1 ∧
    H 1 ![2, 0, 2, 2] = 3 ∧
    H 1 ![2, 1, 0, 0] = 0 ∧
    H 1 ![2, 1, 0, 1] = 0 ∧
    H 1 ![2, 1, 0, 2] = 0 ∧
    H 1 ![2, 1, 1, 0] = 0 ∧
    H 1 ![2, 1, 1, 1] = 1 ∧
    H 1 ![2, 1, 1, 2] = 2 ∧
    H 1 ![2, 1, 2, 0] = 0 ∧
    H 1 ![2, 1, 2, 1] = 0 ∧
    H 1 ![2, 1, 2, 2] = 2 ∧
    H 1 ![2, 2, 0, 0] = 0 ∧
    H 1 ![2, 2, 0, 1] = 0 ∧
    H 1 ![2, 2, 0, 2] = 0 ∧
    H 1 ![2, 2, 1, 0] = 0 ∧
    H 1 ![2, 2, 1, 1] = 0 ∧
    H 1 ![2, 2, 1, 2] = 0 ∧
    H 1 ![2, 2, 2, 0] = 0 ∧
    H 1 ![2, 2, 2, 1] = 0 ∧
    H 1 ![2, 2, 2, 2] = 3 := by
  obtain ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, g25, g26, g27, g28, g29, g30, g31, g32, g33, g34, g35, g36, g37, g38, g39, g40, g41, g42, g43, g44, g45, g46, g47, g48, g49, g50, g51, g52, g53, g54, g55, g56, g57, g58, g59, g60, g61, g62, g63, g64, g65, g66, g67, g68, g69, g70, g71, g72, g73, g74, g75, g76, g77, g78, g79, g80⟩ := Hs 0
  
  simp only [Nat.reduceAdd, zero_add] at g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 g16 g17 g18 g19 g20 g21 g22 g23 g24 g25 g26 g27 g28 g29 g30 g31 g32 g33 g34 g35 g36 g37 g38 g39 g40 g41 g42 g43 g44 g45 g46 g47 g48 g49 g50 g51 g52 g53 g54 g55 g56 g57 g58 g59 g60 g61 g62 g63 g64 g65 g66 g67 g68 g69 g70 g71 g72 g73 g74 g75 g76 g77 g78 g79 g80
  simp only [g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, g25, g26, g27, g28, g29, g30, g31, g32, g33, g34, g35, g36, g37, g38, g39, g40, g41, g42, g43, g44, g45, g46, g47, g48, g49, g50, g51, g52, g53, g54, g55, g56, g57, g58, g59, g60, g61, g62, g63, g64, g65, g66, g67, g68, g69, g70, g71, g72, g73, g74, g75, g76, g77, g78, g79, g80, H0]
  norm_num

theorem B2 :
    H 2 ![0, 0, 0, 0] = 30 ∧
    H 2 ![0, 0, 0, 1] = 63 ∧
    H 2 ![0, 0, 0, 2] = 121 ∧
    H 2 ![0, 0, 1, 0] = 12 ∧
    H 2 ![0, 0, 1, 1] = 34 ∧
    H 2 ![0, 0, 1, 2] = 94 ∧
    H 2 ![0, 0, 2, 0] = 10 ∧
    H 2 ![0, 0, 2, 1] = 10 ∧
    H 2 ![0, 0, 2, 2] = 44 ∧
    H 2 ![0, 1, 0, 0] = 7 ∧
    H 2 ![0, 1, 0, 1] = 19 ∧
    H 2 ![0, 1, 0, 2] = 37 ∧
    H 2 ![0, 1, 1, 0] = 0 ∧
    H 2 ![0, 1, 1, 1] = 28 ∧
    H 2 ![0, 1, 1, 2] = 71 ∧
    H 2 ![0, 1, 2, 0] = 0 ∧
    H 2 ![0, 1, 2, 1] = 0 ∧
    H 2 ![0, 1, 2, 2] = 41 ∧
    H 2 ![0, 2, 0, 0] = 3 ∧
    H 2 ![0, 2, 0, 1] = 9 ∧
    H 2 ![0, 2, 0, 2] = 18 ∧
    H 2 ![0, 2, 1, 0] = 0 ∧
    H 2 ![0, 2, 1, 1] = 3 ∧
    H 2 ![0, 2, 1, 2] = 9 ∧
    H 2 ![0, 2, 2, 0] = 0 ∧
    H 2 ![0, 2, 2, 1] = 0 ∧
    H 2 ![0, 2, 2, 2] = 31 ∧
    H 2 ![1, 0, 0, 0] = 7 ∧
    H 2 ![1, 0, 0, 1] = 17 ∧
    H 2 ![1, 0, 0, 2] = 34 ∧
    H 2 ![1, 0, 1, 0] = 4 ∧
    H 2 ![1, 0, 1, 1] = 10 ∧
    H 2 ![1, 0, 1, 2] = 29 ∧
    H 2 ![1, 0, 2, 0] = 4 ∧
    H 2 ![1, 0, 2, 1] = 4 ∧
    H 2 ![1, 0, 2, 2] = 14 ∧
    H 2 ![1, 1, 0, 0] = 0 ∧
    H 2 ![1, 1, 0, 1] = 0 ∧
    H 2 ![1, 1, 0, 2] = 0 ∧
    H 2 ![1, 1, 1, 0] = 0 ∧
    H 2 ![1, 1, 1, 1] = 21 ∧
    H 2 ![1, 1, 1, 2] = 52 ∧
    H 2 ![1, 1, 2, 0] = 0 ∧
    H 2 ![1, 1, 2, 1] = 0 ∧
    H 2 ![1, 1, 2, 2] = 33 ∧
    H 2 ![1, 2, 0, 0] = 0 ∧
    H 2 ![1, 2, 0, 1] = 0 ∧
    H 2 ![1, 2, 0, 2] = 0 ∧
    H 2 ![1, 2, 1, 0] = 0 ∧
    H 2 ![1, 2, 1, 1] = 0 ∧
    H 2 ![1, 2, 1, 2] = 0 ∧
    H 2 ![1, 2, 2, 0] = 0 ∧
    H 2 ![1, 2, 2, 1] = 0 ∧
    H 2 ![1, 2, 2, 2] = 28 ∧
    H 2 ![2, 0, 0, 0] = 1 ∧
    H 2 ![2, 0, 0, 1] = 3 ∧
    H 2 ![2, 0, 0, 2] = 6 ∧
    H 2 ![2, 0, 1, 0] = 1 ∧
    H 2 ![2, 0, 1, 1] = 2 ∧
    H 2 ![2, 0, 1, 2] = 6 ∧
    H 2 ![2, 0, 2, 0] = 1 ∧
    H 2 ![2, 0, 2, 1] = 1 ∧
    H 2 ![2, 0, 2, 2] = 3 ∧
    H 2 ![2, 1, 0, 0] = 0 ∧
    H 2 ![2, 1, 0, 1] = 0 ∧
    H 2 ![2, 1, 0, 2] = 0 ∧
    H 2 ![2, 1, 1, 0] = 0 ∧
    H 2 ![2, 1, 1, 1] = 1 ∧
    H 2 ![2, 1, 1, 2] = 3 ∧
    H 2 ![2, 1, 2, 0] = 0 ∧
    H 2 ![2, 1, 2, 1] = 0 ∧
    H 2 ![2, 1, 2, 2] = 2 ∧
    H 2 ![2, 2, 0, 0] = 0 ∧
    H 2 ![2, 2, 0, 1] = 0 ∧
    H 2 ![2, 2, 0, 2] = 0 ∧
    H 2 ![2, 2, 1, 0] = 0 ∧
    H 2 ![2, 2, 1, 1] = 0 ∧
    H 2 ![2, 2, 1, 2] = 0 ∧
    H 2 ![2, 2, 2, 0] = 0 ∧
    H 2 ![2, 2, 2, 1] = 0 ∧
    H 2 ![2, 2, 2, 2] = 21 := by
  obtain ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, g25, g26, g27, g28, g29, g30, g31, g32, g33, g34, g35, g36, g37, g38, g39, g40, g41, g42, g43, g44, g45, g46, g47, g48, g49, g50, g51, g52, g53, g54, g55, g56, g57, g58, g59, g60, g61, g62, g63, g64, g65, g66, g67, g68, g69, g70, g71, g72, g73, g74, g75, g76, g77, g78, g79, g80⟩ := Hs 1
  obtain ⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30, w31, w32, w33, w34, w35, w36, w37, w38, w39, w40, w41, w42, w43, w44, w45, w46, w47, w48, w49, w50, w51, w52, w53, w54, w55, w56, w57, w58, w59, w60, w61, w62, w63, w64, w65, w66, w67, w68, w69, w70, w71, w72, w73, w74, w75, w76, w77, w78, w79, w80⟩ := B1
  simp only [Nat.reduceAdd] at g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 g16 g17 g18 g19 g20 g21 g22 g23 g24 g25 g26 g27 g28 g29 g30 g31 g32 g33 g34 g35 g36 g37 g38 g39 g40 g41 g42 g43 g44 g45 g46 g47 g48 g49 g50 g51 g52 g53 g54 g55 g56 g57 g58 g59 g60 g61 g62 g63 g64 g65 g66 g67 g68 g69 g70 g71 g72 g73 g74 g75 g76 g77 g78 g79 g80
  simp only [g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, g25, g26, g27, g28, g29, g30, g31, g32, g33, g34, g35, g36, g37, g38, g39, g40, g41, g42, g43, g44, g45, g46, g47, g48, g49, g50, g51, g52, g53, g54, g55, g56, g57, g58, g59, g60, g61, g62, g63, g64, g65, g66, g67, g68, g69, g70, g71, g72, g73, g74, g75, g76, g77, g78, g79, g80, w0, w1, w2, w3, w4, w6, w9, w10, w11, w12, w18, w19, w20, w27, w28, w29, w30, w31, w33, w36, w37, w38, w39, w40, w41, w42, w45, w46, w47, w54, w55, w56, w57, w58, w60, w63, w64, w65, w66, w67, w68, w69, w72, w73, w74, w75, w76, w77, w78, w79, w80]
  norm_num

theorem B3 :
    H 3 ![0, 0, 0, 0] = 81 ∧
    H 3 ![0, 0, 0, 1] = 164 ∧
    H 3 ![0, 0, 0, 2] = 380 ∧
    H 3 ![0, 0, 1, 0] = 17 ∧
    H 3 ![0, 0, 1, 1] = 55 ∧
    H 3 ![0, 0, 1, 2] = 206 ∧
    H 3 ![0, 0, 2, 0] = 15 ∧
    H 3 ![0, 0, 2, 1] = 15 ∧
    H 3 ![0, 0, 2, 2] = 70 ∧
    H 3 ![0, 1, 0, 0] = 7 ∧
    H 3 ![0, 1, 0, 1] = 26 ∧
    H 3 ![0, 1, 0, 2] = 63 ∧
    H 3 ![0, 1, 1, 0] = 0 ∧
    H 3 ![0, 1, 1, 1] = 45 ∧
    H 3 ![0, 1, 1, 2] = 147 ∧
    H 3 ![0, 1, 2, 0] = 0 ∧
    H 3 ![0, 1, 2, 1] = 0 ∧
    H 3 ![0, 1, 2, 2] = 62 ∧
    H 3 ![0, 2, 0, 0] = 3 ∧
    H 3 ![0, 2, 0, 1] = 12 ∧
    H 3 ![0, 2, 0, 2] = 30 ∧
    H 3 ![0, 2, 1, 0] = 0 ∧
    H 3 ![0, 2, 1, 1] = 3 ∧
    H 3 ![0, 2, 1, 2] = 12 ∧
    H 3 ![0, 2, 2, 0] = 0 ∧
    H 3 ![0, 2, 2, 1] = 0 ∧
    H 3 ![0, 2, 2, 2] = 48 ∧
    H 3 ![1, 0, 0, 0] = 9 ∧
    H 3 ![1, 0, 0, 1] = 29 ∧
    H 3 ![1, 0, 0, 2] = 72 ∧
    H 3 ![1, 0, 1, 0] = 5 ∧
    H 3 ![1, 0, 1, 1] = 13 ∧
    H 3 ![1, 0, 1, 2] = 46 ∧
    H 3 ![1, 0, 2, 0] = 5 ∧
    H 3 ![1, 0, 2, 1] = 5 ∧
    H 3 ![1, 0, 2, 2] = 18 ∧
    H 3 ![1, 1, 0, 0] = 0 ∧
    H 3 ![1, 1, 0, 1] = 0 ∧
    H 3 ![1, 1, 0, 2] = 0 ∧
    H 3 ![1, 1, 1, 0] = 0 ∧
    H 3 ![1, 1, 1, 1] = 38 ∧
    H 3 ![1, 1, 1, 2] = 121 ∧
    H 3 ![1, 1, 2, 0] = 0 ∧
    H 3 ![1, 1, 2, 1] = 0 ∧
    H 3 ![1, 1, 2, 2] = 55 ∧
    H 3 ![1, 2, 0, 0] = 0 ∧
    H 3 ![1, 2, 0, 1] = 0 ∧
    H 3 ![1, 2, 0, 2] = 0 ∧
    H 3 ![1, 2, 1, 0] = 0 ∧
    H 3 ![1, 2, 1, 1] = 0 ∧
    H 3 ![1, 2, 1, 2] = 0 ∧
    H 3 ![1, 2, 2, 0] = 0 ∧
    H 3 ![1, 2, 2, 1] = 0 ∧
    H 3 ![1, 2, 2, 2] = 45 ∧
    H 3 ![2, 0, 0, 0] = 1 ∧
    H 3 ![2, 0, 0, 1] = 4 ∧
    H 3 ![2, 0, 0, 2] = 10 ∧
    H 3 ![2, 0, 1, 0] = 1 ∧
    H 3 ![2, 0, 1, 1] = 2 ∧
    H 3 ![2, 0, 1, 2] = 7 ∧
    H 3 ![2, 0, 2, 0] = 1 ∧
    H 3 ![2, 0, 2, 1] = 1 ∧
    H 3 ![2, 0, 2, 2] = 3 ∧
    H 3 ![2, 1, 0, 0] = 0 ∧
    H 3 ![2, 1, 0, 1] = 0 ∧
    H 3 ![2, 1, 0, 2] = 0 ∧
    H 3 ![2, 1, 1, 0] = 0 ∧
    H 3 ![2, 1, 1, 1] = 1 ∧
    H 3 ![2, 1, 1, 2] = 4 ∧
    H 3 ![2, 1, 2, 0] = 0 ∧
    H 3 ![2, 1, 2, 1] = 0 ∧
    H 3 ![2, 1, 2, 2] = 2 ∧
    H 3 ![2, 2, 0, 0] = 0 ∧
    H 3 ![2, 2, 0, 1] = 0 ∧
    H 3 ![2, 2, 0, 2] = 0 ∧
    H 3 ![2, 2, 1, 0] = 0 ∧
    H 3 ![2, 2, 1, 1] = 0 ∧
    H 3 ![2, 2, 1, 2] = 0 ∧
    H 3 ![2, 2, 2, 0] = 0 ∧
    H 3 ![2, 2, 2, 1] = 0 ∧
    H 3 ![2, 2, 2, 2] = 38 := by
  obtain ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, g25, g26, g27, g28, g29, g30, g31, g32, g33, g34, g35, g36, g37, g38, g39, g40, g41, g42, g43, g44, g45, g46, g47, g48, g49, g50, g51, g52, g53, g54, g55, g56, g57, g58, g59, g60, g61, g62, g63, g64, g65, g66, g67, g68, g69, g70, g71, g72, g73, g74, g75, g76, g77, g78, g79, g80⟩ := Hs 2
  obtain ⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30, w31, w32, w33, w34, w35, w36, w37, w38, w39, w40, w41, w42, w43, w44, w45, w46, w47, w48, w49, w50, w51, w52, w53, w54, w55, w56, w57, w58, w59, w60, w61, w62, w63, w64, w65, w66, w67, w68, w69, w70, w71, w72, w73, w74, w75, w76, w77, w78, w79, w80⟩ := B2
  simp only [Nat.reduceAdd] at g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 g16 g17 g18 g19 g20 g21 g22 g23 g24 g25 g26 g27 g28 g29 g30 g31 g32 g33 g34 g35 g36 g37 g38 g39 g40 g41 g42 g43 g44 g45 g46 g47 g48 g49 g50 g51 g52 g53 g54 g55 g56 g57 g58 g59 g60 g61 g62 g63 g64 g65 g66 g67 g68 g69 g70 g71 g72 g73 g74 g75 g76 g77 g78 g79 g80
  simp only [g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, g25, g26, g27, g28, g29, g30, g31, g32, g33, g34, g35, g36, g37, g38, g39, g40, g41, g42, g43, g44, g45, g46, g47, g48, g49, g50, g51, g52, g53, g54, g55, g56, g57, g58, g59, g60, g61, g62, g63, g64, g65, g66, g67, g68, g69, g70, g71, g72, g73, g74, g75, g76, g77, g78, g79, g80, w0, w1, w2, w3, w4, w6, w9, w10, w11, w12, w18, w19, w20, w27, w28, w29, w30, w31, w33, w36, w37, w38, w39, w40, w41, w42, w45, w46, w47, w54, w55, w56, w57, w58, w60, w63, w64, w65, w66, w67, w68, w69, w72, w73, w74, w75, w76, w77, w78, w79, w80]
  norm_num

theorem B4 :
    H 4 ![0, 0, 0, 0] = 168 ∧
    H 4 ![0, 0, 0, 1] = 365 ∧
    H 4 ![0, 0, 0, 2] = 952 ∧
    H 4 ![0, 0, 1, 0] = 23 ∧
    H 4 ![0, 0, 1, 1] = 114 ∧
    H 4 ![0, 0, 1, 2] = 420 ∧
    H 4 ![0, 0, 2, 0] = 21 ∧
    H 4 ![0, 0, 2, 1] = 21 ∧
    H 4 ![0, 0, 2, 2] = 135 ∧
    H 4 ![0, 1, 0, 0] = 7 ∧
    H 4 ![0, 1, 0, 1] = 33 ∧
    H 4 ![0, 1, 0, 2] = 96 ∧
    H 4 ![0, 1, 1, 0] = 0 ∧
    H 4 ![0, 1, 1, 1] = 98 ∧
    H 4 ![0, 1, 1, 2] = 321 ∧
    H 4 ![0, 1, 2, 0] = 0 ∧
    H 4 ![0, 1, 2, 1] = 0 ∧
    H 4 ![0, 1, 2, 2] = 121 ∧
    H 4 ![0, 2, 0, 0] = 3 ∧
    H 4 ![0, 2, 0, 1] = 15 ∧
    H 4 ![0, 2, 0, 2] = 45 ∧
    H 4 ![0, 2, 1, 0] = 0 ∧
    H 4 ![0, 2, 1, 1] = 3 ∧
    H 4 ![0, 2, 1, 2] = 15 ∧
    H 4 ![0, 2, 2, 0] = 0 ∧
    H 4 ![0, 2, 2, 1] = 0 ∧
    H 4 ![0, 2, 2, 2] = 101 ∧
    H 4 ![1, 0, 0, 0] = 11 ∧
    H 4 ![1, 0, 0, 1] = 44 ∧
    H 4 ![1, 0, 0, 2] = 130 ∧
    H 4 ![1, 0, 1, 0] = 6 ∧
    H 4 ![1, 0, 1, 1] = 16 ∧
    H 4 ![1, 0, 1, 2] = 65 ∧
    H 4 ![1, 0, 2, 0] = 6 ∧
    H 4 ![1, 0, 2, 1] = 6 ∧
    H 4 ![1, 0, 2, 2] = 22 ∧
    H 4 ![1, 1, 0, 0] = 0 ∧
    H 4 ![1, 1, 0, 1] = 0 ∧
    H 4 ![1, 1, 0, 2] = 0 ∧
    H 4 ![1, 1, 1, 0] = 0 ∧
    H 4 ![1, 1, 1, 1] = 91 ∧
    H 4 ![1, 1, 1, 2] = 288 ∧
    H 4 ![1, 1, 2, 0] = 0 ∧
    H 4 ![1, 1, 2, 1] = 0 ∧
    H 4 ![1, 1, 2, 2] = 114 ∧
    H 4 ![1, 2, 0, 0] = 0 ∧
    H 4 ![1, 2, 0, 1] = 0 ∧
    H 4 ![1, 2, 0, 2] = 0 ∧
    H 4 ![1, 2, 1, 0] = 0 ∧
    H 4 ![1, 2, 1, 1] = 0 ∧
    H 4 ![1, 2, 1, 2] = 0 ∧
    H 4 ![1, 2, 2, 0] = 0 ∧
    H 4 ![1, 2, 2, 1] = 0 ∧
    H 4 ![1, 2, 2, 2] = 98 ∧
    H 4 ![2, 0, 0, 0] = 1 ∧
    H 4 ![2, 0, 0, 1] = 5 ∧
    H 4 ![2, 0, 0, 2] = 15 ∧
    H 4 ![2, 0, 1, 0] = 1 ∧
    H 4 ![2, 0, 1, 1] = 2 ∧
    H 4 ![2, 0, 1, 2] = 8 ∧
    H 4 ![2, 0, 2, 0] = 1 ∧
    H 4 ![2, 0, 2, 1] = 1 ∧
    H 4 ![2, 0, 2, 2] = 3 ∧
    H 4 ![2, 1, 0, 0] = 0 ∧
    H 4 ![2, 1, 0, 1] = 0 ∧
    H 4 ![2, 1, 0, 2] = 0 ∧
    H 4 ![2, 1, 1, 0] = 0 ∧
    H 4 ![2, 1, 1, 1] = 1 ∧
    H 4 ![2, 1, 1, 2] = 5 ∧
    H 4 ![2, 1, 2, 0] = 0 ∧
    H 4 ![2, 1, 2, 1] = 0 ∧
    H 4 ![2, 1, 2, 2] = 2 ∧
    H 4 ![2, 2, 0, 0] = 0 ∧
    H 4 ![2, 2, 0, 1] = 0 ∧
    H 4 ![2, 2, 0, 2] = 0 ∧
    H 4 ![2, 2, 1, 0] = 0 ∧
    H 4 ![2, 2, 1, 1] = 0 ∧
    H 4 ![2, 2, 1, 2] = 0 ∧
    H 4 ![2, 2, 2, 0] = 0 ∧
    H 4 ![2, 2, 2, 1] = 0 ∧
    H 4 ![2, 2, 2, 2] = 91 := by
  obtain ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, g25, g26, g27, g28, g29, g30, g31, g32, g33, g34, g35, g36, g37, g38, g39, g40, g41, g42, g43, g44, g45, g46, g47, g48, g49, g50, g51, g52, g53, g54, g55, g56, g57, g58, g59, g60, g61, g62, g63, g64, g65, g66, g67, g68, g69, g70, g71, g72, g73, g74, g75, g76, g77, g78, g79, g80⟩ := Hs 3
  obtain ⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30, w31, w32, w33, w34, w35, w36, w37, w38, w39, w40, w41, w42, w43, w44, w45, w46, w47, w48, w49, w50, w51, w52, w53, w54, w55, w56, w57, w58, w59, w60, w61, w62, w63, w64, w65, w66, w67, w68, w69, w70, w71, w72, w73, w74, w75, w76, w77, w78, w79, w80⟩ := B3
  simp only [Nat.reduceAdd] at g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 g16 g17 g18 g19 g20 g21 g22 g23 g24 g25 g26 g27 g28 g29 g30 g31 g32 g33 g34 g35 g36 g37 g38 g39 g40 g41 g42 g43 g44 g45 g46 g47 g48 g49 g50 g51 g52 g53 g54 g55 g56 g57 g58 g59 g60 g61 g62 g63 g64 g65 g66 g67 g68 g69 g70 g71 g72 g73 g74 g75 g76 g77 g78 g79 g80
  simp only [g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, g25, g26, g27, g28, g29, g30, g31, g32, g33, g34, g35, g36, g37, g38, g39, g40, g41, g42, g43, g44, g45, g46, g47, g48, g49, g50, g51, g52, g53, g54, g55, g56, g57, g58, g59, g60, g61, g62, g63, g64, g65, g66, g67, g68, g69, g70, g71, g72, g73, g74, g75, g76, g77, g78, g79, g80, w0, w1, w2, w3, w4, w6, w9, w10, w11, w12, w18, w19, w20, w27, w28, w29, w30, w31, w33, w36, w37, w38, w39, w40, w41, w42, w45, w46, w47, w54, w55, w56, w57, w58, w60, w63, w64, w65, w66, w67, w68, w69, w72, w73, w74, w75, w76, w77, w78, w79, w80]
  norm_num

theorem Hf (m : ℕ) (hm : 4 ≤ m) :
    (H m ![0, 0, 0, 0] : ℚ) = (-9 : ℚ) + (-3 : ℚ) * (m : ℚ) ^ 1 + (-3 : ℚ) * (-1 : ℚ) ^ m + (12 : ℚ) * (2 : ℚ) ^ m ∧
    (H m ![0, 0, 0, 1] : ℚ) = (-35 / 2 : ℚ) + (-10 : ℚ) * (m : ℚ) ^ 1 + (1 / 2 : ℚ) * (m : ℚ) ^ 2 + (1 / 2 : ℚ) * (m : ℚ) ^ 3 + (-3 / 2 : ℚ) * (-1 : ℚ) ^ m + (24 : ℚ) * (2 : ℚ) ^ m ∧
    (H m ![0, 0, 0, 2] : ℚ) = (-73 : ℚ) + (-30 : ℚ) * (m : ℚ) ^ 1 + (-83 / 12 : ℚ) * (m : ℚ) ^ 2 + (3 / 2 : ℚ) * (m : ℚ) ^ 3 + (5 / 12 : ℚ) * (m : ℚ) ^ 4 + (-3 : ℚ) * (-1 : ℚ) ^ m + (66 : ℚ) * (2 : ℚ) ^ m ∧
    (H m ![0, 0, 1, 0] : ℚ) = (5 : ℚ) + (5 / 2 : ℚ) * (m : ℚ) ^ 1 + (1 / 2 : ℚ) * (m : ℚ) ^ 2 ∧
    (H m ![0, 0, 1, 1] : ℚ) = (1 : ℚ) + (3 / 2 : ℚ) * (m : ℚ) ^ 1 + (1 / 2 : ℚ) * (m : ℚ) ^ 2 + (3 : ℚ) * (-1 : ℚ) ^ m + (6 : ℚ) * (2 : ℚ) ^ m ∧
    (H m ![0, 0, 1, 2] : ℚ) = (-13 / 2 : ℚ) + (-3 : ℚ) * (m : ℚ) ^ 1 + (3 / 2 : ℚ) * (m : ℚ) ^ 2 + (1 / 2 : ℚ) * (m : ℚ) ^ 3 + (-3 / 2 : ℚ) * (-1 : ℚ) ^ m + (24 : ℚ) * (2 : ℚ) ^ m ∧
    (H m ![0, 0, 2, 0] : ℚ) = (3 : ℚ) + (5 / 2 : ℚ) * (m : ℚ) ^ 1 + (1 / 2 : ℚ) * (m : ℚ) ^ 2 ∧
    (H m ![0, 0, 2, 1] : ℚ) = (3 : ℚ) + (5 / 2 : ℚ) * (m : ℚ) ^ 1 + (1 / 2 : ℚ) * (m : ℚ) ^ 2 ∧
    (H m ![0, 0, 2, 2] : ℚ) = (4 : ℚ) + (4 : ℚ) * (m : ℚ) ^ 1 + (1 : ℚ) * (m : ℚ) ^ 2 + (3 : ℚ) * (-1 : ℚ) ^ m + (6 : ℚ) * (2 : ℚ) ^ m ∧
    (H m ![0, 1, 0, 0] : ℚ) = (7 : ℚ) ∧
    (H m ![0, 1, 0, 1] : ℚ) = (5 : ℚ) + (7 : ℚ) * (m : ℚ) ^ 1 ∧
    (H m ![0, 1, 0, 2] : ℚ) = (6 : ℚ) + (17 / 2 : ℚ) * (m : ℚ) ^ 1 + (7 / 2 : ℚ) * (m : ℚ) ^ 2 ∧
    (H m ![0, 1, 1, 0] : ℚ) = 0 ∧
    (H m ![0, 1, 1, 1] : ℚ) = (3 : ℚ) + (-1 : ℚ) * (m : ℚ) ^ 1 + (3 : ℚ) * (-1 : ℚ) ^ m + (6 : ℚ) * (2 : ℚ) ^ m ∧
    (H m ![0, 1, 1, 2] : ℚ) = (-15 / 2 : ℚ) + (-1 : ℚ) * (m : ℚ) ^ 1 + (1 / 2 : ℚ) * (m : ℚ) ^ 2 + (1 / 2 : ℚ) * (m : ℚ) ^ 3 + (9 / 2 : ℚ) * (-1 : ℚ) ^ m + (18 : ℚ) * (2 : ℚ) ^ m ∧
    (H m ![0, 1, 2, 0] : ℚ) = 0 ∧
    (H m ![0, 1, 2, 1] : ℚ) = 0 ∧
    (H m ![0, 1, 2, 2] : ℚ) = (8 : ℚ) + (3 / 2 : ℚ) * (m : ℚ) ^ 1 + (1 / 2 : ℚ) * (m : ℚ) ^ 2 + (3 : ℚ) * (-1 : ℚ) ^ m + (6 : ℚ) * (2 : ℚ) ^ m ∧
    (H m ![0, 2, 0, 0] : ℚ) = (3 : ℚ) ∧
    (H m ![0, 2, 0, 1] : ℚ) = (3 : ℚ) + (3 : ℚ) * (m : ℚ) ^ 1 ∧
    (H m ![0, 2, 0, 2] : ℚ) = (3 : ℚ) + (9 / 2 : ℚ) * (m : ℚ) ^ 1 + (3 / 2 : ℚ) * (m : ℚ) ^ 2 ∧
    (H m ![0, 2, 1, 0] : ℚ) = 0 ∧
    (H m ![0, 2, 1, 1] : ℚ) = (3 : ℚ) ∧
    (H m ![0, 2, 1, 2] : ℚ) = (3 : ℚ) + (3 : ℚ) * (m : ℚ) ^ 1 ∧
    (H m ![0, 2, 2, 0] : ℚ) = 0 ∧
    (H m ![0, 2, 2, 1] : ℚ) = 0 ∧
    (H m ![0, 2, 2, 2] : ℚ) = (6 : ℚ) + (-1 : ℚ) * (m : ℚ) ^ 1 + (3 : ℚ) * (-1 : ℚ) ^ m + (6 : ℚ) * (2 : ℚ) ^ m ∧
    (H m ![1, 0, 0, 0] : ℚ) = (3 : ℚ) + (2 : ℚ) * (m : ℚ) ^ 1 ∧
    (H m ![1, 0, 0, 1] : ℚ) = (2 : ℚ) + (9 / 2 : ℚ) * (m : ℚ) ^ 1 + (3 / 2 : ℚ) * (m : ℚ) ^ 2 ∧
    (H m ![1, 0, 0, 2] : ℚ) = (2 : ℚ) + (16 / 3 : ℚ) * (m : ℚ) ^ 1 + (4 : ℚ) * (m : ℚ) ^ 2 + (2 / 3 : ℚ) * (m : ℚ) ^ 3 ∧
    (H m ![1, 0, 1, 0] : ℚ) = (2 : ℚ) + (1 : ℚ) * (m : ℚ) ^ 1 ∧
    (H m ![1, 0, 1, 1] : ℚ) = (4 : ℚ) + (3 : ℚ) * (m : ℚ) ^ 1 ∧
    (H m ![1, 0, 1, 2] : ℚ) = (7 : ℚ) + (17 / 2 : ℚ) * (m : ℚ) ^ 1 + (3 / 2 : ℚ) * (m : ℚ) ^ 2 ∧
    (H m ![1, 0, 2, 0] : ℚ) = (2 : ℚ) + (1 : ℚ) * (m : ℚ) ^ 1 ∧
    (H m ![1, 0, 2, 1] : ℚ) = (2 : ℚ) + (1 : ℚ) * (m : ℚ) ^ 1 ∧
    (H m ![1, 0, 2, 2] : ℚ) = (6 : ℚ) + (4 : ℚ) * (m : ℚ) ^ 1 ∧
    (H m ![1, 1, 0, 0] : ℚ) = 0 ∧
    (H m ![1, 1, 0, 1] : ℚ) = 0 ∧
    (H m ![1, 1, 0, 2] : ℚ) = 0 ∧
    (H m ![1, 1, 1, 0] : ℚ) = 0 ∧
    (H m ![1, 1, 1, 1] : ℚ) = (-4 : ℚ) + (-1 : ℚ) * (m : ℚ) ^ 1 + (3 : ℚ) * (-1 : ℚ) ^ m + (6 : ℚ) * (2 : ℚ) ^ m ∧
    (H m ![1, 1, 1, 2] : ℚ) = (-25 / 2 : ℚ) + (-8 : ℚ) * (m : ℚ) ^ 1 + (1 / 2 : ℚ) * (m : ℚ) ^ 2 + (1 / 2 : ℚ) * (m : ℚ) ^ 3 + (9 / 2 : ℚ) * (-1 : ℚ) ^ m + (18 : ℚ) * (2 : ℚ) ^ m ∧
    (H m ![1, 1, 2, 0] : ℚ) = 0 ∧
    (H m ![1, 1, 2, 1] : ℚ) = 0 ∧
    (H m ![1, 1, 2, 2] : ℚ) = (1 : ℚ) + (3 / 2 : ℚ) * (m : ℚ) ^ 1 + (1 / 2 : ℚ) * (m : ℚ) ^ 2 + (3 : ℚ) * (-1 : ℚ) ^ m + (6 : ℚ) * (2 : ℚ) ^ m ∧
    (H m ![1, 2, 0, 0] : ℚ) = 0 ∧
    (H m ![1, 2, 0, 1] : ℚ) = 0 ∧
    (H m ![1, 2, 0, 2] : ℚ) = 0 ∧
    (H m ![1, 2, 1, 0] : ℚ) = 0 ∧
    (H m ![1, 2, 1, 1] : ℚ) = 0 ∧
    (H m ![1, 2, 1, 2] : ℚ) = 0 ∧
    (H m ![1, 2, 2, 0] : ℚ) = 0 ∧
    (H m ![1, 2, 2, 1] : ℚ) = 0 ∧
    (H m ![1, 2, 2, 2] : ℚ) = (3 : ℚ) + (-1 : ℚ) * (m : ℚ) ^ 1 + (3 : ℚ) * (-1 : ℚ) ^ m + (6 : ℚ) * (2 : ℚ) ^ m ∧
    (H m ![2, 0, 0, 0] : ℚ) = (1 : ℚ) ∧
    (H m ![2, 0, 0, 1] : ℚ) = (1 : ℚ) + (1 : ℚ) * (m : ℚ) ^ 1 ∧
    (H m ![2, 0, 0, 2] : ℚ) = (1 : ℚ) + (3 / 2 : ℚ) * (m : ℚ) ^ 1 + (1 / 2 : ℚ) * (m : ℚ) ^ 2 ∧
    (H m ![2, 0, 1, 0] : ℚ) = (1 : ℚ) ∧
    (H m ![2, 0, 1, 1] : ℚ) = (2 : ℚ) ∧
    (H m ![2, 0, 1, 2] : ℚ) = (4 : ℚ) + (1 : ℚ) * (m : ℚ) ^ 1 ∧
    (H m ![2, 0, 2, 0] : ℚ) = (1 : ℚ) ∧
    (H m ![2, 0, 2, 1] : ℚ) = (1 : ℚ) ∧
    (H m ![2, 0, 2, 2] : ℚ) = (3 : ℚ) ∧
    (H m ![2, 1, 0, 0] : ℚ) = 0 ∧
    (H m ![2, 1, 0, 1] : ℚ) = 0 ∧
    (H m ![2, 1, 0, 2] : ℚ) = 0 ∧
    (H m ![2, 1, 1, 0] : ℚ) = 0 ∧
    (H m ![2, 1, 1, 1] : ℚ) = (1 : ℚ) ∧
    (H m ![2, 1, 1, 2] : ℚ) = (1 : ℚ) + (1 : ℚ) * (m : ℚ) ^ 1 ∧
    (H m ![2, 1, 2, 0] : ℚ) = 0 ∧
    (H m ![2, 1, 2, 1] : ℚ) = 0 ∧
    (H m ![2, 1, 2, 2] : ℚ) = (2 : ℚ) ∧
    (H m ![2, 2, 0, 0] : ℚ) = 0 ∧
    (H m ![2, 2, 0, 1] : ℚ) = 0 ∧
    (H m ![2, 2, 0, 2] : ℚ) = 0 ∧
    (H m ![2, 2, 1, 0] : ℚ) = 0 ∧
    (H m ![2, 2, 1, 1] : ℚ) = 0 ∧
    (H m ![2, 2, 1, 2] : ℚ) = 0 ∧
    (H m ![2, 2, 2, 0] : ℚ) = 0 ∧
    (H m ![2, 2, 2, 1] : ℚ) = 0 ∧
    (H m ![2, 2, 2, 2] : ℚ) = (-4 : ℚ) + (-1 : ℚ) * (m : ℚ) ^ 1 + (3 : ℚ) * (-1 : ℚ) ^ m + (6 : ℚ) * (2 : ℚ) ^ m := by
  induction m, hm using Nat.le_induction with
  | base =>
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32, b33, b34, b35, b36, b37, b38, b39, b40, b41, b42, b43, b44, b45, b46, b47, b48, b49, b50, b51, b52, b53, b54, b55, b56, b57, b58, b59, b60, b61, b62, b63, b64, b65, b66, b67, b68, b69, b70, b71, b72, b73, b74, b75, b76, b77, b78, b79, b80⟩ := B4
    rw [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32, b33, b34, b35, b36, b37, b38, b39, b40, b41, b42, b43, b44, b45, b46, b47, b48, b49, b50, b51, b52, b53, b54, b55, b56, b57, b58, b59, b60, b61, b62, b63, b64, b65, b66, b67, b68, b69, b70, b71, b72, b73, b74, b75, b76, b77, b78, b79, b80]
    norm_num
  | succ m hm ih =>
    obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36, h37, h38, h39, h40, h41, h42, h43, h44, h45, h46, h47, h48, h49, h50, h51, h52, h53, h54, h55, h56, h57, h58, h59, h60, h61, h62, h63, h64, h65, h66, h67, h68, h69, h70, h71, h72, h73, h74, h75, h76, h77, h78, h79, h80⟩ := ih
    obtain ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, g25, g26, g27, g28, g29, g30, g31, g32, g33, g34, g35, g36, g37, g38, g39, g40, g41, g42, g43, g44, g45, g46, g47, g48, g49, g50, g51, g52, g53, g54, g55, g56, g57, g58, g59, g60, g61, g62, g63, g64, g65, g66, g67, g68, g69, g70, g71, g72, g73, g74, g75, g76, g77, g78, g79, g80⟩ := Hs m
    rw [g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, g25, g26, g27, g28, g29, g30, g31, g32, g33, g34, g35, g36, g37, g38, g39, g40, g41, g42, g43, g44, g45, g46, g47, g48, g49, g50, g51, g52, g53, g54, g55, g56, g57, g58, g59, g60, g61, g62, g63, g64, g65, g66, g67, g68, g69, g70, g71, g72, g73, g74, g75, g76, g77, g78, g79, g80]
    push_cast
    simp only [h0, h1, h2, h3, h4, h6, h9, h10, h11, h12, h18, h19, h20, h27, h28, h29, h30, h31, h33, h36, h37, h38, h39, h40, h41, h42, h45, h46, h47, h54, h55, h56, h57, h58, h60, h63, h64, h65, h66, h67, h68, h69, h72, h73, h74, h75, h76, h77, h78, h79, h80]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> first | ring | trivial

theorem aS (n : ℕ) : a n = H n ![0, 0, 0, 0] + H n ![0, 0, 0, 1] + H n ![0, 0, 0, 2] + H n ![0, 0, 1, 0] + H n ![0, 0, 1, 1] + H n ![0, 0, 1, 2] + H n ![0, 0, 2, 0] + H n ![0, 0, 2, 1] + H n ![0, 0, 2, 2] + H n ![0, 1, 0, 0] + H n ![0, 1, 0, 1] + H n ![0, 1, 0, 2] + H n ![0, 1, 1, 0] + H n ![0, 1, 1, 1] + H n ![0, 1, 1, 2] + H n ![0, 1, 2, 0] + H n ![0, 1, 2, 1] + H n ![0, 1, 2, 2] + H n ![0, 2, 0, 0] + H n ![0, 2, 0, 1] + H n ![0, 2, 0, 2] + H n ![0, 2, 1, 0] + H n ![0, 2, 1, 1] + H n ![0, 2, 1, 2] + H n ![0, 2, 2, 0] + H n ![0, 2, 2, 1] + H n ![0, 2, 2, 2] + H n ![1, 0, 0, 0] + H n ![1, 0, 0, 1] + H n ![1, 0, 0, 2] + H n ![1, 0, 1, 0] + H n ![1, 0, 1, 1] + H n ![1, 0, 1, 2] + H n ![1, 0, 2, 0] + H n ![1, 0, 2, 1] + H n ![1, 0, 2, 2] + H n ![1, 1, 0, 0] + H n ![1, 1, 0, 1] + H n ![1, 1, 0, 2] + H n ![1, 1, 1, 0] + H n ![1, 1, 1, 1] + H n ![1, 1, 1, 2] + H n ![1, 1, 2, 0] + H n ![1, 1, 2, 1] + H n ![1, 1, 2, 2] + H n ![1, 2, 0, 0] + H n ![1, 2, 0, 1] + H n ![1, 2, 0, 2] + H n ![1, 2, 1, 0] + H n ![1, 2, 1, 1] + H n ![1, 2, 1, 2] + H n ![1, 2, 2, 0] + H n ![1, 2, 2, 1] + H n ![1, 2, 2, 2] + H n ![2, 0, 0, 0] + H n ![2, 0, 0, 1] + H n ![2, 0, 0, 2] + H n ![2, 0, 1, 0] + H n ![2, 0, 1, 1] + H n ![2, 0, 1, 2] + H n ![2, 0, 2, 0] + H n ![2, 0, 2, 1] + H n ![2, 0, 2, 2] + H n ![2, 1, 0, 0] + H n ![2, 1, 0, 1] + H n ![2, 1, 0, 2] + H n ![2, 1, 1, 0] + H n ![2, 1, 1, 1] + H n ![2, 1, 1, 2] + H n ![2, 1, 2, 0] + H n ![2, 1, 2, 1] + H n ![2, 1, 2, 2] + H n ![2, 2, 0, 0] + H n ![2, 2, 0, 1] + H n ![2, 2, 0, 2] + H n ![2, 2, 1, 0] + H n ![2, 2, 1, 1] + H n ![2, 2, 1, 2] + H n ![2, 2, 2, 0] + H n ![2, 2, 2, 1] + H n ![2, 2, 2, 2] := by
  rw [card_eq, sum_cons, sumC]
  rfl

theorem aval (n : ℕ) (hn : 4 ≤ n) : (a n : ℚ) = (36 * (-5 + 9 * (-1) ^ n + 9 * 2 ^ (3 + n)) + 202 * (n : ℚ) + 151 * (n : ℚ) ^ 2 + 50 * (n : ℚ) ^ 3 + 5 * (n : ℚ) ^ 4) / 12 := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36, h37, h38, h39, h40, h41, h42, h43, h44, h45, h46, h47, h48, h49, h50, h51, h52, h53, h54, h55, h56, h57, h58, h59, h60, h61, h62, h63, h64, h65, h66, h67, h68, h69, h70, h71, h72, h73, h74, h75, h76, h77, h78, h79, h80⟩ := Hf n hn
  rw [aS]
  push_cast
  rw [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36, h37, h38, h39, h40, h41, h42, h43, h44, h45, h46, h47, h48, h49, h50, h51, h52, h53, h54, h55, h56, h57, h58, h59, h60, h61, h62, h63, h64, h65, h66, h67, h68, h69, h70, h71, h72, h73, h74, h75, h76, h77, h78, h79, h80]
  ring

theorem a0 : (a 0 : ℚ) = 81 := by
  rw [aS]; simp only [H0]; norm_num

theorem a1 : (a 1 : ℚ) = 369 := by
  obtain ⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30, w31, w32, w33, w34, w35, w36, w37, w38, w39, w40, w41, w42, w43, w44, w45, w46, w47, w48, w49, w50, w51, w52, w53, w54, w55, w56, w57, w58, w59, w60, w61, w62, w63, w64, w65, w66, w67, w68, w69, w70, w71, w72, w73, w74, w75, w76, w77, w78, w79, w80⟩ := B1
  rw [aS]; simp only [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30, w31, w32, w33, w34, w35, w36, w37, w38, w39, w40, w41, w42, w43, w44, w45, w46, w47, w48, w49, w50, w51, w52, w53, w54, w55, w56, w57, w58, w59, w60, w61, w62, w63, w64, w65, w66, w67, w68, w69, w70, w71, w72, w73, w74, w75, w76, w77, w78, w79, w80]; norm_num

theorem a2 : (a 2 : ℚ) = 1002 := by
  obtain ⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30, w31, w32, w33, w34, w35, w36, w37, w38, w39, w40, w41, w42, w43, w44, w45, w46, w47, w48, w49, w50, w51, w52, w53, w54, w55, w56, w57, w58, w59, w60, w61, w62, w63, w64, w65, w66, w67, w68, w69, w70, w71, w72, w73, w74, w75, w76, w77, w78, w79, w80⟩ := B2
  rw [aS]; simp only [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30, w31, w32, w33, w34, w35, w36, w37, w38, w39, w40, w41, w42, w43, w44, w45, w46, w47, w48, w49, w50, w51, w52, w53, w54, w55, w56, w57, w58, w59, w60, w61, w62, w63, w64, w65, w66, w67, w68, w69, w70, w71, w72, w73, w74, w75, w76, w77, w78, w79, w80]; norm_num

theorem a3 : (a 3 : ℚ) = 1997 := by
  obtain ⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30, w31, w32, w33, w34, w35, w36, w37, w38, w39, w40, w41, w42, w43, w44, w45, w46, w47, w48, w49, w50, w51, w52, w53, w54, w55, w56, w57, w58, w59, w60, w61, w62, w63, w64, w65, w66, w67, w68, w69, w70, w71, w72, w73, w74, w75, w76, w77, w78, w79, w80⟩ := B3
  rw [aS]; simp only [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30, w31, w32, w33, w34, w35, w36, w37, w38, w39, w40, w41, w42, w43, w44, w45, w46, w47, w48, w49, w50, w51, w52, w53, w54, w55, w56, w57, w58, w59, w60, w61, w62, w63, w64, w65, w66, w67, w68, w69, w70, w71, w72, w73, w74, w75, w76, w77, w78, w79, w80]; norm_num

end P251132

open P251132 in
theorem OMA.solution : type_of% @OMA.S_oeis_a251132.main := by
  refine ⟨?_, ?_, ?_⟩
  · intro n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 11 := ⟨n - 11, by omega⟩
    rw [show k + 11 - 1 = k + 10 by omega, show k + 11 - 2 = k + 9 by omega, show k + 11 - 3 = k + 8 by omega, show k + 11 - 4 = k + 7 by omega, show k + 11 - 5 = k + 6 by omega, show k + 11 - 6 = k + 5 by omega, show k + 11 - 7 = k + 4 by omega]
    apply Int.cast_injective (α := ℚ)
    push_cast
    simp only [aval _ (show 4 ≤ k + 11 by omega), aval _ (show 4 ≤ k + 10 by omega), aval _ (show 4 ≤ k + 9 by omega), aval _ (show 4 ≤ k + 8 by omega), aval _ (show 4 ≤ k + 7 by omega), aval _ (show 4 ≤ k + 6 by omega), aval _ (show 4 ≤ k + 5 by omega), aval _ (show 4 ≤ k + 4 by omega)]
    push_cast
    ring
  · have hm : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * ((1 - PowerSeries.X) ^ 5 * (1 + PowerSeries.X) * (1 - 2 * PowerSeries.X)) = PowerSeries.X * (369 - 1212 * PowerSeries.X + 782 * PowerSeries.X ^ 2 + 1464 * PowerSeries.X ^ 3 - 2514 * PowerSeries.X ^ 4 + 1146 * PowerSeries.X ^ 5 + 62 * PowerSeries.X ^ 6 - 114 * PowerSeries.X ^ 7 - 5 * PowerSeries.X ^ 8 + 2 * PowerSeries.X ^ 9) := by
      have hq : ∀ F : PowerSeries ℚ, F * ((1 - PowerSeries.X) ^ 5 * (1 + PowerSeries.X) * (1 - 2 * PowerSeries.X)) = F - C (6 : ℚ) * (F * X ^ 1) + C (13 : ℚ) * (F * X ^ 2) - C (10 : ℚ) * (F * X ^ 3) - C (5 : ℚ) * (F * X ^ 4) + C (14 : ℚ) * (F * X ^ 5) - C (9 : ℚ) * (F * X ^ 6) + C (2 : ℚ) * (F * X ^ 7) := by
        intro F; simp only [map_ofNat, map_one, pow_one, map_neg]; ring
      have hr : (PowerSeries.X * (369 - 1212 * PowerSeries.X + 782 * PowerSeries.X ^ 2 + 1464 * PowerSeries.X ^ 3 - 2514 * PowerSeries.X ^ 4 + 1146 * PowerSeries.X ^ 5 + 62 * PowerSeries.X ^ 6 - 114 * PowerSeries.X ^ 7 - 5 * PowerSeries.X ^ 8 + 2 * PowerSeries.X ^ 9) : PowerSeries ℚ) = C (369 : ℚ) * X ^ 1 - C (1212 : ℚ) * X ^ 2 + C (782 : ℚ) * X ^ 3 + C (1464 : ℚ) * X ^ 4 - C (2514 : ℚ) * X ^ 5 + C (1146 : ℚ) * X ^ 6 + C (62 : ℚ) * X ^ 7 - C (114 : ℚ) * X ^ 8 - C (5 : ℚ) * X ^ 9 + C (2 : ℚ) * X ^ 10 := by
        simp only [map_ofNat, map_one, pow_one, map_neg]; ring
      rw [hq, hr]
      ext n
      simp only [map_add, map_sub, map_neg, coeff_mul_X_pow', coeff_C_mul, coeff_mk, coeff_C, coeff_X_pow, coeff_one]
      by_cases hn : n < 11
      · interval_cases n <;> simp [a0, a1, a2, a3, aval] <;> norm_num
      · obtain ⟨m, rfl⟩ : ∃ m, n = m + 11 := ⟨n - 11, by omega⟩
        simp only [show m + 11 - 1 = m + 10 by omega, show m + 11 - 2 = m + 9 by omega, show m + 11 - 3 = m + 8 by omega, show m + 11 - 4 = m + 7 by omega, show m + 11 - 5 = m + 6 by omega, show m + 11 - 6 = m + 5 by omega, show m + 11 - 7 = m + 4 by omega, show 1 ≤ m + 11 by omega, show 2 ≤ m + 11 by omega, show 3 ≤ m + 11 by omega, show 4 ≤ m + 11 by omega, show 5 ≤ m + 11 by omega, show 6 ≤ m + 11 by omega, show 7 ≤ m + 11 by omega, show m + 11 ≠ 0 by omega, show m + 11 ≠ 1 by omega, show m + 11 ≠ 2 by omega, show m + 11 ≠ 3 by omega, show m + 11 ≠ 4 by omega, show m + 11 ≠ 5 by omega, show m + 11 ≠ 6 by omega, show m + 11 ≠ 7 by omega, show m + 11 ≠ 8 by omega, show m + 11 ≠ 9 by omega, show m + 11 ≠ 10 by omega, show m + 11 ≠ 0 by omega, show m + 10 ≠ 0 by omega, show m + 9 ≠ 0 by omega, show m + 8 ≠ 0 by omega, show m + 7 ≠ 0 by omega, show m + 6 ≠ 0 by omega, show m + 5 ≠ 0 by omega, show m + 4 ≠ 0 by omega, if_true, if_false, aval _ (show 4 ≤ m + 4 by omega), aval _ (show 4 ≤ m + 5 by omega), aval _ (show 4 ≤ m + 6 by omega), aval _ (show 4 ≤ m + 7 by omega), aval _ (show 4 ≤ m + 8 by omega), aval _ (show 4 ≤ m + 9 by omega), aval _ (show 4 ≤ m + 10 by omega), aval _ (show 4 ≤ m + 11 by omega)]
        push_cast
        ring
    have hd : constantCoeff ((1 - PowerSeries.X) ^ 5 * (1 + PowerSeries.X) * (1 - 2 * PowerSeries.X) : PowerSeries ℚ) ≠ 0 := by simp
    rw [G, ← hm, mul_assoc, PowerSeries.mul_inv_cancel _ hd, mul_one]
  · intro n hn
    rw [aval n (by omega)]
