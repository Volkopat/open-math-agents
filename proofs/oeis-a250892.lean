import OMAStatements.S_oeis_a250892
import Mathlib

open OMA.S_oeis_a250892 PowerSeries

namespace P250892

abbrev Col := Fin 3 → Fin 3

def ok (r r' : Col) : Prop := ∀ j : Fin 2, Blk (r j.castSucc) (r j.succ) (r' j.castSucc) (r' j.succ)

instance (c d : Col) : Decidable (ok c d) := by unfold ok Blk; infer_instance

def V (m : ℕ) (f : Fin (m + 1) → Col) : Prop := ∀ j : Fin m, ok (f j.castSucc) (f j.succ)

instance (m : ℕ) (f : Fin (m + 1) → Col) : Decidable (V m f) := by unfold V; infer_instance

def e (n : ℕ) : {x : Fin (n + 1) → Fin 3 → Fin 3 // ∀ i : Fin n, ∀ j : Fin 2,
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

def eC : (Fin 3 → Fin 3) ≃ Fin 3 × Fin 3 × Fin 3 where
  toFun f := (f 0, f 1, f 2)
  invFun p := ![p.1, p.2.1, p.2.2]
  left_inv f := by funext i; fin_cases i <;> rfl
  right_inv p := rfl

theorem eCs (p : Fin 3 × Fin 3 × Fin 3) : eC.symm p = ![p.1, p.2.1, p.2.2] := rfl

theorem sumC (g : Col → ℕ) : ∑ s, g s = g ![0, 0, 0] + g ![0, 0, 1] + g ![0, 0, 2] + g ![0, 1, 0] + g ![0, 1, 1] + g ![0, 1, 2] + g ![0, 2, 0] + g ![0, 2, 1] + g ![0, 2, 2] + g ![1, 0, 0] + g ![1, 0, 1] + g ![1, 0, 2] + g ![1, 1, 0] + g ![1, 1, 1] + g ![1, 1, 2] + g ![1, 2, 0] + g ![1, 2, 1] + g ![1, 2, 2] + g ![2, 0, 0] + g ![2, 0, 1] + g ![2, 0, 2] + g ![2, 1, 0] + g ![2, 1, 1] + g ![2, 1, 2] + g ![2, 2, 0] + g ![2, 2, 1] + g ![2, 2, 2] := by
  rw [← eC.symm.sum_comp]
  simp only [Fintype.sum_prod_type, Fin.sum_univ_three, eCs]
  ring

set_option maxHeartbeats 4000000 in
theorem Hs (m : ℕ) :
    H (m + 1) ![0, 0, 0] = H m ![0, 0, 0] + H m ![0, 0, 1] + H m ![0, 0, 2] + H m ![0, 1, 1] + H m ![0, 1, 2] + H m ![0, 2, 2] + H m ![1, 1, 1] + H m ![1, 1, 2] + H m ![1, 2, 2] + H m ![2, 2, 2] ∧
    H (m + 1) ![0, 0, 1] = H m ![0, 0, 1] + H m ![0, 0, 2] + H m ![0, 1, 2] + H m ![1, 1, 2] ∧
    H (m + 1) ![0, 0, 2] = H m ![0, 0, 2] ∧
    H (m + 1) ![0, 1, 0] = H m ![0, 1, 0] + H m ![0, 1, 1] + H m ![0, 1, 2] + H m ![0, 2, 1] + H m ![0, 2, 2] + H m ![1, 2, 1] + H m ![1, 2, 2] ∧
    H (m + 1) ![0, 1, 1] = H m ![0, 1, 1] + H m ![0, 1, 2] + H m ![0, 2, 2] + H m ![1, 2, 2] ∧
    H (m + 1) ![0, 1, 2] = H m ![0, 1, 2] ∧
    H (m + 1) ![0, 2, 0] = H m ![0, 2, 0] + H m ![0, 2, 1] + H m ![0, 2, 2] ∧
    H (m + 1) ![0, 2, 1] = H m ![0, 2, 1] + H m ![0, 2, 2] ∧
    H (m + 1) ![0, 2, 2] = H m ![0, 2, 2] ∧
    H (m + 1) ![1, 0, 0] = H m ![0, 1, 1] + H m ![0, 1, 2] + H m ![0, 2, 2] + H m ![1, 0, 0] + H m ![1, 0, 1] + H m ![1, 0, 2] + H m ![1, 1, 1] + H m ![1, 1, 2] + H m ![1, 2, 2] + H m ![2, 1, 1] + H m ![2, 1, 2] + H m ![2, 2, 2] ∧
    H (m + 1) ![1, 0, 1] = H m ![0, 1, 2] + H m ![1, 0, 1] + H m ![1, 0, 2] + H m ![1, 1, 2] + H m ![2, 1, 2] ∧
    H (m + 1) ![1, 0, 2] = H m ![1, 0, 2] ∧
    H (m + 1) ![1, 1, 0] = H m ![0, 0, 1] + H m ![0, 0, 2] + H m ![0, 2, 1] + H m ![0, 2, 2] + H m ![1, 1, 0] + H m ![1, 1, 1] + H m ![1, 1, 2] + H m ![1, 2, 1] + H m ![1, 2, 2] + H m ![2, 2, 1] + H m ![2, 2, 2] ∧
    H (m + 1) ![1, 1, 1] = H m ![0, 0, 0] + H m ![0, 0, 2] + H m ![0, 2, 2] + H m ![1, 1, 1] + H m ![1, 1, 2] + H m ![1, 2, 2] + H m ![2, 2, 2] ∧
    H (m + 1) ![1, 1, 2] = H m ![0, 0, 1] + H m ![1, 1, 2] ∧
    H (m + 1) ![1, 2, 0] = H m ![0, 1, 1] + H m ![0, 1, 2] + H m ![1, 2, 0] + H m ![1, 2, 1] + H m ![1, 2, 2] ∧
    H (m + 1) ![1, 2, 1] = H m ![0, 1, 0] + H m ![0, 1, 2] + H m ![1, 2, 1] + H m ![1, 2, 2] ∧
    H (m + 1) ![1, 2, 2] = H m ![0, 1, 1] + H m ![1, 2, 2] ∧
    H (m + 1) ![2, 0, 0] = H m ![0, 2, 2] + H m ![1, 1, 1] + H m ![1, 1, 2] + H m ![1, 2, 2] + H m ![2, 0, 0] + H m ![2, 0, 1] + H m ![2, 0, 2] + H m ![2, 1, 1] + H m ![2, 1, 2] + H m ![2, 2, 2] ∧
    H (m + 1) ![2, 0, 1] = H m ![1, 1, 2] + H m ![2, 0, 1] + H m ![2, 0, 2] + H m ![2, 1, 2] ∧
    H (m + 1) ![2, 0, 2] = H m ![2, 0, 2] ∧
    H (m + 1) ![2, 1, 0] = H m ![1, 0, 1] + H m ![1, 0, 2] + H m ![1, 2, 1] + H m ![1, 2, 2] + H m ![2, 1, 0] + H m ![2, 1, 1] + H m ![2, 1, 2] + H m ![2, 2, 1] + H m ![2, 2, 2] ∧
    H (m + 1) ![2, 1, 1] = H m ![1, 0, 0] + H m ![1, 0, 2] + H m ![1, 2, 2] + H m ![2, 1, 1] + H m ![2, 1, 2] + H m ![2, 2, 2] ∧
    H (m + 1) ![2, 1, 2] = H m ![1, 0, 1] + H m ![2, 1, 2] ∧
    H (m + 1) ![2, 2, 0] = H m ![0, 0, 2] + H m ![1, 1, 1] + H m ![1, 1, 2] + H m ![2, 2, 0] + H m ![2, 2, 1] + H m ![2, 2, 2] ∧
    H (m + 1) ![2, 2, 1] = H m ![1, 1, 0] + H m ![1, 1, 2] + H m ![2, 2, 1] + H m ![2, 2, 2] ∧
    H (m + 1) ![2, 2, 2] = H m ![0, 0, 0] + H m ![1, 1, 1] + H m ![2, 2, 2] := by
  have k0 : ok ![0, 0, 0] ![0, 0, 0] := by decide
  have k1 : ok ![0, 0, 0] ![0, 0, 1] := by decide
  have k2 : ok ![0, 0, 0] ![0, 0, 2] := by decide
  have k3 : ¬ ok ![0, 0, 0] ![0, 1, 0] := by decide
  have k4 : ok ![0, 0, 0] ![0, 1, 1] := by decide
  have k5 : ok ![0, 0, 0] ![0, 1, 2] := by decide
  have k6 : ¬ ok ![0, 0, 0] ![0, 2, 0] := by decide
  have k7 : ¬ ok ![0, 0, 0] ![0, 2, 1] := by decide
  have k8 : ok ![0, 0, 0] ![0, 2, 2] := by decide
  have k9 : ¬ ok ![0, 0, 0] ![1, 0, 0] := by decide
  have k10 : ¬ ok ![0, 0, 0] ![1, 0, 1] := by decide
  have k11 : ¬ ok ![0, 0, 0] ![1, 0, 2] := by decide
  have k12 : ¬ ok ![0, 0, 0] ![1, 1, 0] := by decide
  have k13 : ok ![0, 0, 0] ![1, 1, 1] := by decide
  have k14 : ok ![0, 0, 0] ![1, 1, 2] := by decide
  have k15 : ¬ ok ![0, 0, 0] ![1, 2, 0] := by decide
  have k16 : ¬ ok ![0, 0, 0] ![1, 2, 1] := by decide
  have k17 : ok ![0, 0, 0] ![1, 2, 2] := by decide
  have k18 : ¬ ok ![0, 0, 0] ![2, 0, 0] := by decide
  have k19 : ¬ ok ![0, 0, 0] ![2, 0, 1] := by decide
  have k20 : ¬ ok ![0, 0, 0] ![2, 0, 2] := by decide
  have k21 : ¬ ok ![0, 0, 0] ![2, 1, 0] := by decide
  have k22 : ¬ ok ![0, 0, 0] ![2, 1, 1] := by decide
  have k23 : ¬ ok ![0, 0, 0] ![2, 1, 2] := by decide
  have k24 : ¬ ok ![0, 0, 0] ![2, 2, 0] := by decide
  have k25 : ¬ ok ![0, 0, 0] ![2, 2, 1] := by decide
  have k26 : ok ![0, 0, 0] ![2, 2, 2] := by decide
  have k27 : ¬ ok ![0, 0, 1] ![0, 0, 0] := by decide
  have k28 : ok ![0, 0, 1] ![0, 0, 1] := by decide
  have k29 : ok ![0, 0, 1] ![0, 0, 2] := by decide
  have k30 : ¬ ok ![0, 0, 1] ![0, 1, 0] := by decide
  have k31 : ¬ ok ![0, 0, 1] ![0, 1, 1] := by decide
  have k32 : ok ![0, 0, 1] ![0, 1, 2] := by decide
  have k33 : ¬ ok ![0, 0, 1] ![0, 2, 0] := by decide
  have k34 : ¬ ok ![0, 0, 1] ![0, 2, 1] := by decide
  have k35 : ¬ ok ![0, 0, 1] ![0, 2, 2] := by decide
  have k36 : ¬ ok ![0, 0, 1] ![1, 0, 0] := by decide
  have k37 : ¬ ok ![0, 0, 1] ![1, 0, 1] := by decide
  have k38 : ¬ ok ![0, 0, 1] ![1, 0, 2] := by decide
  have k39 : ¬ ok ![0, 0, 1] ![1, 1, 0] := by decide
  have k40 : ¬ ok ![0, 0, 1] ![1, 1, 1] := by decide
  have k41 : ok ![0, 0, 1] ![1, 1, 2] := by decide
  have k42 : ¬ ok ![0, 0, 1] ![1, 2, 0] := by decide
  have k43 : ¬ ok ![0, 0, 1] ![1, 2, 1] := by decide
  have k44 : ¬ ok ![0, 0, 1] ![1, 2, 2] := by decide
  have k45 : ¬ ok ![0, 0, 1] ![2, 0, 0] := by decide
  have k46 : ¬ ok ![0, 0, 1] ![2, 0, 1] := by decide
  have k47 : ¬ ok ![0, 0, 1] ![2, 0, 2] := by decide
  have k48 : ¬ ok ![0, 0, 1] ![2, 1, 0] := by decide
  have k49 : ¬ ok ![0, 0, 1] ![2, 1, 1] := by decide
  have k50 : ¬ ok ![0, 0, 1] ![2, 1, 2] := by decide
  have k51 : ¬ ok ![0, 0, 1] ![2, 2, 0] := by decide
  have k52 : ¬ ok ![0, 0, 1] ![2, 2, 1] := by decide
  have k53 : ¬ ok ![0, 0, 1] ![2, 2, 2] := by decide
  have k54 : ¬ ok ![0, 0, 2] ![0, 0, 0] := by decide
  have k55 : ¬ ok ![0, 0, 2] ![0, 0, 1] := by decide
  have k56 : ok ![0, 0, 2] ![0, 0, 2] := by decide
  have k57 : ¬ ok ![0, 0, 2] ![0, 1, 0] := by decide
  have k58 : ¬ ok ![0, 0, 2] ![0, 1, 1] := by decide
  have k59 : ¬ ok ![0, 0, 2] ![0, 1, 2] := by decide
  have k60 : ¬ ok ![0, 0, 2] ![0, 2, 0] := by decide
  have k61 : ¬ ok ![0, 0, 2] ![0, 2, 1] := by decide
  have k62 : ¬ ok ![0, 0, 2] ![0, 2, 2] := by decide
  have k63 : ¬ ok ![0, 0, 2] ![1, 0, 0] := by decide
  have k64 : ¬ ok ![0, 0, 2] ![1, 0, 1] := by decide
  have k65 : ¬ ok ![0, 0, 2] ![1, 0, 2] := by decide
  have k66 : ¬ ok ![0, 0, 2] ![1, 1, 0] := by decide
  have k67 : ¬ ok ![0, 0, 2] ![1, 1, 1] := by decide
  have k68 : ¬ ok ![0, 0, 2] ![1, 1, 2] := by decide
  have k69 : ¬ ok ![0, 0, 2] ![1, 2, 0] := by decide
  have k70 : ¬ ok ![0, 0, 2] ![1, 2, 1] := by decide
  have k71 : ¬ ok ![0, 0, 2] ![1, 2, 2] := by decide
  have k72 : ¬ ok ![0, 0, 2] ![2, 0, 0] := by decide
  have k73 : ¬ ok ![0, 0, 2] ![2, 0, 1] := by decide
  have k74 : ¬ ok ![0, 0, 2] ![2, 0, 2] := by decide
  have k75 : ¬ ok ![0, 0, 2] ![2, 1, 0] := by decide
  have k76 : ¬ ok ![0, 0, 2] ![2, 1, 1] := by decide
  have k77 : ¬ ok ![0, 0, 2] ![2, 1, 2] := by decide
  have k78 : ¬ ok ![0, 0, 2] ![2, 2, 0] := by decide
  have k79 : ¬ ok ![0, 0, 2] ![2, 2, 1] := by decide
  have k80 : ¬ ok ![0, 0, 2] ![2, 2, 2] := by decide
  have k81 : ¬ ok ![0, 1, 0] ![0, 0, 0] := by decide
  have k82 : ¬ ok ![0, 1, 0] ![0, 0, 1] := by decide
  have k83 : ¬ ok ![0, 1, 0] ![0, 0, 2] := by decide
  have k84 : ok ![0, 1, 0] ![0, 1, 0] := by decide
  have k85 : ok ![0, 1, 0] ![0, 1, 1] := by decide
  have k86 : ok ![0, 1, 0] ![0, 1, 2] := by decide
  have k87 : ¬ ok ![0, 1, 0] ![0, 2, 0] := by decide
  have k88 : ok ![0, 1, 0] ![0, 2, 1] := by decide
  have k89 : ok ![0, 1, 0] ![0, 2, 2] := by decide
  have k90 : ¬ ok ![0, 1, 0] ![1, 0, 0] := by decide
  have k91 : ¬ ok ![0, 1, 0] ![1, 0, 1] := by decide
  have k92 : ¬ ok ![0, 1, 0] ![1, 0, 2] := by decide
  have k93 : ¬ ok ![0, 1, 0] ![1, 1, 0] := by decide
  have k94 : ¬ ok ![0, 1, 0] ![1, 1, 1] := by decide
  have k95 : ¬ ok ![0, 1, 0] ![1, 1, 2] := by decide
  have k96 : ¬ ok ![0, 1, 0] ![1, 2, 0] := by decide
  have k97 : ok ![0, 1, 0] ![1, 2, 1] := by decide
  have k98 : ok ![0, 1, 0] ![1, 2, 2] := by decide
  have k99 : ¬ ok ![0, 1, 0] ![2, 0, 0] := by decide
  have k100 : ¬ ok ![0, 1, 0] ![2, 0, 1] := by decide
  have k101 : ¬ ok ![0, 1, 0] ![2, 0, 2] := by decide
  have k102 : ¬ ok ![0, 1, 0] ![2, 1, 0] := by decide
  have k103 : ¬ ok ![0, 1, 0] ![2, 1, 1] := by decide
  have k104 : ¬ ok ![0, 1, 0] ![2, 1, 2] := by decide
  have k105 : ¬ ok ![0, 1, 0] ![2, 2, 0] := by decide
  have k106 : ¬ ok ![0, 1, 0] ![2, 2, 1] := by decide
  have k107 : ¬ ok ![0, 1, 0] ![2, 2, 2] := by decide
  have k108 : ¬ ok ![0, 1, 1] ![0, 0, 0] := by decide
  have k109 : ¬ ok ![0, 1, 1] ![0, 0, 1] := by decide
  have k110 : ¬ ok ![0, 1, 1] ![0, 0, 2] := by decide
  have k111 : ¬ ok ![0, 1, 1] ![0, 1, 0] := by decide
  have k112 : ok ![0, 1, 1] ![0, 1, 1] := by decide
  have k113 : ok ![0, 1, 1] ![0, 1, 2] := by decide
  have k114 : ¬ ok ![0, 1, 1] ![0, 2, 0] := by decide
  have k115 : ¬ ok ![0, 1, 1] ![0, 2, 1] := by decide
  have k116 : ok ![0, 1, 1] ![0, 2, 2] := by decide
  have k117 : ¬ ok ![0, 1, 1] ![1, 0, 0] := by decide
  have k118 : ¬ ok ![0, 1, 1] ![1, 0, 1] := by decide
  have k119 : ¬ ok ![0, 1, 1] ![1, 0, 2] := by decide
  have k120 : ¬ ok ![0, 1, 1] ![1, 1, 0] := by decide
  have k121 : ¬ ok ![0, 1, 1] ![1, 1, 1] := by decide
  have k122 : ¬ ok ![0, 1, 1] ![1, 1, 2] := by decide
  have k123 : ¬ ok ![0, 1, 1] ![1, 2, 0] := by decide
  have k124 : ¬ ok ![0, 1, 1] ![1, 2, 1] := by decide
  have k125 : ok ![0, 1, 1] ![1, 2, 2] := by decide
  have k126 : ¬ ok ![0, 1, 1] ![2, 0, 0] := by decide
  have k127 : ¬ ok ![0, 1, 1] ![2, 0, 1] := by decide
  have k128 : ¬ ok ![0, 1, 1] ![2, 0, 2] := by decide
  have k129 : ¬ ok ![0, 1, 1] ![2, 1, 0] := by decide
  have k130 : ¬ ok ![0, 1, 1] ![2, 1, 1] := by decide
  have k131 : ¬ ok ![0, 1, 1] ![2, 1, 2] := by decide
  have k132 : ¬ ok ![0, 1, 1] ![2, 2, 0] := by decide
  have k133 : ¬ ok ![0, 1, 1] ![2, 2, 1] := by decide
  have k134 : ¬ ok ![0, 1, 1] ![2, 2, 2] := by decide
  have k135 : ¬ ok ![0, 1, 2] ![0, 0, 0] := by decide
  have k136 : ¬ ok ![0, 1, 2] ![0, 0, 1] := by decide
  have k137 : ¬ ok ![0, 1, 2] ![0, 0, 2] := by decide
  have k138 : ¬ ok ![0, 1, 2] ![0, 1, 0] := by decide
  have k139 : ¬ ok ![0, 1, 2] ![0, 1, 1] := by decide
  have k140 : ok ![0, 1, 2] ![0, 1, 2] := by decide
  have k141 : ¬ ok ![0, 1, 2] ![0, 2, 0] := by decide
  have k142 : ¬ ok ![0, 1, 2] ![0, 2, 1] := by decide
  have k143 : ¬ ok ![0, 1, 2] ![0, 2, 2] := by decide
  have k144 : ¬ ok ![0, 1, 2] ![1, 0, 0] := by decide
  have k145 : ¬ ok ![0, 1, 2] ![1, 0, 1] := by decide
  have k146 : ¬ ok ![0, 1, 2] ![1, 0, 2] := by decide
  have k147 : ¬ ok ![0, 1, 2] ![1, 1, 0] := by decide
  have k148 : ¬ ok ![0, 1, 2] ![1, 1, 1] := by decide
  have k149 : ¬ ok ![0, 1, 2] ![1, 1, 2] := by decide
  have k150 : ¬ ok ![0, 1, 2] ![1, 2, 0] := by decide
  have k151 : ¬ ok ![0, 1, 2] ![1, 2, 1] := by decide
  have k152 : ¬ ok ![0, 1, 2] ![1, 2, 2] := by decide
  have k153 : ¬ ok ![0, 1, 2] ![2, 0, 0] := by decide
  have k154 : ¬ ok ![0, 1, 2] ![2, 0, 1] := by decide
  have k155 : ¬ ok ![0, 1, 2] ![2, 0, 2] := by decide
  have k156 : ¬ ok ![0, 1, 2] ![2, 1, 0] := by decide
  have k157 : ¬ ok ![0, 1, 2] ![2, 1, 1] := by decide
  have k158 : ¬ ok ![0, 1, 2] ![2, 1, 2] := by decide
  have k159 : ¬ ok ![0, 1, 2] ![2, 2, 0] := by decide
  have k160 : ¬ ok ![0, 1, 2] ![2, 2, 1] := by decide
  have k161 : ¬ ok ![0, 1, 2] ![2, 2, 2] := by decide
  have k162 : ¬ ok ![0, 2, 0] ![0, 0, 0] := by decide
  have k163 : ¬ ok ![0, 2, 0] ![0, 0, 1] := by decide
  have k164 : ¬ ok ![0, 2, 0] ![0, 0, 2] := by decide
  have k165 : ¬ ok ![0, 2, 0] ![0, 1, 0] := by decide
  have k166 : ¬ ok ![0, 2, 0] ![0, 1, 1] := by decide
  have k167 : ¬ ok ![0, 2, 0] ![0, 1, 2] := by decide
  have k168 : ok ![0, 2, 0] ![0, 2, 0] := by decide
  have k169 : ok ![0, 2, 0] ![0, 2, 1] := by decide
  have k170 : ok ![0, 2, 0] ![0, 2, 2] := by decide
  have k171 : ¬ ok ![0, 2, 0] ![1, 0, 0] := by decide
  have k172 : ¬ ok ![0, 2, 0] ![1, 0, 1] := by decide
  have k173 : ¬ ok ![0, 2, 0] ![1, 0, 2] := by decide
  have k174 : ¬ ok ![0, 2, 0] ![1, 1, 0] := by decide
  have k175 : ¬ ok ![0, 2, 0] ![1, 1, 1] := by decide
  have k176 : ¬ ok ![0, 2, 0] ![1, 1, 2] := by decide
  have k177 : ¬ ok ![0, 2, 0] ![1, 2, 0] := by decide
  have k178 : ¬ ok ![0, 2, 0] ![1, 2, 1] := by decide
  have k179 : ¬ ok ![0, 2, 0] ![1, 2, 2] := by decide
  have k180 : ¬ ok ![0, 2, 0] ![2, 0, 0] := by decide
  have k181 : ¬ ok ![0, 2, 0] ![2, 0, 1] := by decide
  have k182 : ¬ ok ![0, 2, 0] ![2, 0, 2] := by decide
  have k183 : ¬ ok ![0, 2, 0] ![2, 1, 0] := by decide
  have k184 : ¬ ok ![0, 2, 0] ![2, 1, 1] := by decide
  have k185 : ¬ ok ![0, 2, 0] ![2, 1, 2] := by decide
  have k186 : ¬ ok ![0, 2, 0] ![2, 2, 0] := by decide
  have k187 : ¬ ok ![0, 2, 0] ![2, 2, 1] := by decide
  have k188 : ¬ ok ![0, 2, 0] ![2, 2, 2] := by decide
  have k189 : ¬ ok ![0, 2, 1] ![0, 0, 0] := by decide
  have k190 : ¬ ok ![0, 2, 1] ![0, 0, 1] := by decide
  have k191 : ¬ ok ![0, 2, 1] ![0, 0, 2] := by decide
  have k192 : ¬ ok ![0, 2, 1] ![0, 1, 0] := by decide
  have k193 : ¬ ok ![0, 2, 1] ![0, 1, 1] := by decide
  have k194 : ¬ ok ![0, 2, 1] ![0, 1, 2] := by decide
  have k195 : ¬ ok ![0, 2, 1] ![0, 2, 0] := by decide
  have k196 : ok ![0, 2, 1] ![0, 2, 1] := by decide
  have k197 : ok ![0, 2, 1] ![0, 2, 2] := by decide
  have k198 : ¬ ok ![0, 2, 1] ![1, 0, 0] := by decide
  have k199 : ¬ ok ![0, 2, 1] ![1, 0, 1] := by decide
  have k200 : ¬ ok ![0, 2, 1] ![1, 0, 2] := by decide
  have k201 : ¬ ok ![0, 2, 1] ![1, 1, 0] := by decide
  have k202 : ¬ ok ![0, 2, 1] ![1, 1, 1] := by decide
  have k203 : ¬ ok ![0, 2, 1] ![1, 1, 2] := by decide
  have k204 : ¬ ok ![0, 2, 1] ![1, 2, 0] := by decide
  have k205 : ¬ ok ![0, 2, 1] ![1, 2, 1] := by decide
  have k206 : ¬ ok ![0, 2, 1] ![1, 2, 2] := by decide
  have k207 : ¬ ok ![0, 2, 1] ![2, 0, 0] := by decide
  have k208 : ¬ ok ![0, 2, 1] ![2, 0, 1] := by decide
  have k209 : ¬ ok ![0, 2, 1] ![2, 0, 2] := by decide
  have k210 : ¬ ok ![0, 2, 1] ![2, 1, 0] := by decide
  have k211 : ¬ ok ![0, 2, 1] ![2, 1, 1] := by decide
  have k212 : ¬ ok ![0, 2, 1] ![2, 1, 2] := by decide
  have k213 : ¬ ok ![0, 2, 1] ![2, 2, 0] := by decide
  have k214 : ¬ ok ![0, 2, 1] ![2, 2, 1] := by decide
  have k215 : ¬ ok ![0, 2, 1] ![2, 2, 2] := by decide
  have k216 : ¬ ok ![0, 2, 2] ![0, 0, 0] := by decide
  have k217 : ¬ ok ![0, 2, 2] ![0, 0, 1] := by decide
  have k218 : ¬ ok ![0, 2, 2] ![0, 0, 2] := by decide
  have k219 : ¬ ok ![0, 2, 2] ![0, 1, 0] := by decide
  have k220 : ¬ ok ![0, 2, 2] ![0, 1, 1] := by decide
  have k221 : ¬ ok ![0, 2, 2] ![0, 1, 2] := by decide
  have k222 : ¬ ok ![0, 2, 2] ![0, 2, 0] := by decide
  have k223 : ¬ ok ![0, 2, 2] ![0, 2, 1] := by decide
  have k224 : ok ![0, 2, 2] ![0, 2, 2] := by decide
  have k225 : ¬ ok ![0, 2, 2] ![1, 0, 0] := by decide
  have k226 : ¬ ok ![0, 2, 2] ![1, 0, 1] := by decide
  have k227 : ¬ ok ![0, 2, 2] ![1, 0, 2] := by decide
  have k228 : ¬ ok ![0, 2, 2] ![1, 1, 0] := by decide
  have k229 : ¬ ok ![0, 2, 2] ![1, 1, 1] := by decide
  have k230 : ¬ ok ![0, 2, 2] ![1, 1, 2] := by decide
  have k231 : ¬ ok ![0, 2, 2] ![1, 2, 0] := by decide
  have k232 : ¬ ok ![0, 2, 2] ![1, 2, 1] := by decide
  have k233 : ¬ ok ![0, 2, 2] ![1, 2, 2] := by decide
  have k234 : ¬ ok ![0, 2, 2] ![2, 0, 0] := by decide
  have k235 : ¬ ok ![0, 2, 2] ![2, 0, 1] := by decide
  have k236 : ¬ ok ![0, 2, 2] ![2, 0, 2] := by decide
  have k237 : ¬ ok ![0, 2, 2] ![2, 1, 0] := by decide
  have k238 : ¬ ok ![0, 2, 2] ![2, 1, 1] := by decide
  have k239 : ¬ ok ![0, 2, 2] ![2, 1, 2] := by decide
  have k240 : ¬ ok ![0, 2, 2] ![2, 2, 0] := by decide
  have k241 : ¬ ok ![0, 2, 2] ![2, 2, 1] := by decide
  have k242 : ¬ ok ![0, 2, 2] ![2, 2, 2] := by decide
  have k243 : ¬ ok ![1, 0, 0] ![0, 0, 0] := by decide
  have k244 : ¬ ok ![1, 0, 0] ![0, 0, 1] := by decide
  have k245 : ¬ ok ![1, 0, 0] ![0, 0, 2] := by decide
  have k246 : ¬ ok ![1, 0, 0] ![0, 1, 0] := by decide
  have k247 : ok ![1, 0, 0] ![0, 1, 1] := by decide
  have k248 : ok ![1, 0, 0] ![0, 1, 2] := by decide
  have k249 : ¬ ok ![1, 0, 0] ![0, 2, 0] := by decide
  have k250 : ¬ ok ![1, 0, 0] ![0, 2, 1] := by decide
  have k251 : ok ![1, 0, 0] ![0, 2, 2] := by decide
  have k252 : ok ![1, 0, 0] ![1, 0, 0] := by decide
  have k253 : ok ![1, 0, 0] ![1, 0, 1] := by decide
  have k254 : ok ![1, 0, 0] ![1, 0, 2] := by decide
  have k255 : ¬ ok ![1, 0, 0] ![1, 1, 0] := by decide
  have k256 : ok ![1, 0, 0] ![1, 1, 1] := by decide
  have k257 : ok ![1, 0, 0] ![1, 1, 2] := by decide
  have k258 : ¬ ok ![1, 0, 0] ![1, 2, 0] := by decide
  have k259 : ¬ ok ![1, 0, 0] ![1, 2, 1] := by decide
  have k260 : ok ![1, 0, 0] ![1, 2, 2] := by decide
  have k261 : ¬ ok ![1, 0, 0] ![2, 0, 0] := by decide
  have k262 : ¬ ok ![1, 0, 0] ![2, 0, 1] := by decide
  have k263 : ¬ ok ![1, 0, 0] ![2, 0, 2] := by decide
  have k264 : ¬ ok ![1, 0, 0] ![2, 1, 0] := by decide
  have k265 : ok ![1, 0, 0] ![2, 1, 1] := by decide
  have k266 : ok ![1, 0, 0] ![2, 1, 2] := by decide
  have k267 : ¬ ok ![1, 0, 0] ![2, 2, 0] := by decide
  have k268 : ¬ ok ![1, 0, 0] ![2, 2, 1] := by decide
  have k269 : ok ![1, 0, 0] ![2, 2, 2] := by decide
  have k270 : ¬ ok ![1, 0, 1] ![0, 0, 0] := by decide
  have k271 : ¬ ok ![1, 0, 1] ![0, 0, 1] := by decide
  have k272 : ¬ ok ![1, 0, 1] ![0, 0, 2] := by decide
  have k273 : ¬ ok ![1, 0, 1] ![0, 1, 0] := by decide
  have k274 : ¬ ok ![1, 0, 1] ![0, 1, 1] := by decide
  have k275 : ok ![1, 0, 1] ![0, 1, 2] := by decide
  have k276 : ¬ ok ![1, 0, 1] ![0, 2, 0] := by decide
  have k277 : ¬ ok ![1, 0, 1] ![0, 2, 1] := by decide
  have k278 : ¬ ok ![1, 0, 1] ![0, 2, 2] := by decide
  have k279 : ¬ ok ![1, 0, 1] ![1, 0, 0] := by decide
  have k280 : ok ![1, 0, 1] ![1, 0, 1] := by decide
  have k281 : ok ![1, 0, 1] ![1, 0, 2] := by decide
  have k282 : ¬ ok ![1, 0, 1] ![1, 1, 0] := by decide
  have k283 : ¬ ok ![1, 0, 1] ![1, 1, 1] := by decide
  have k284 : ok ![1, 0, 1] ![1, 1, 2] := by decide
  have k285 : ¬ ok ![1, 0, 1] ![1, 2, 0] := by decide
  have k286 : ¬ ok ![1, 0, 1] ![1, 2, 1] := by decide
  have k287 : ¬ ok ![1, 0, 1] ![1, 2, 2] := by decide
  have k288 : ¬ ok ![1, 0, 1] ![2, 0, 0] := by decide
  have k289 : ¬ ok ![1, 0, 1] ![2, 0, 1] := by decide
  have k290 : ¬ ok ![1, 0, 1] ![2, 0, 2] := by decide
  have k291 : ¬ ok ![1, 0, 1] ![2, 1, 0] := by decide
  have k292 : ¬ ok ![1, 0, 1] ![2, 1, 1] := by decide
  have k293 : ok ![1, 0, 1] ![2, 1, 2] := by decide
  have k294 : ¬ ok ![1, 0, 1] ![2, 2, 0] := by decide
  have k295 : ¬ ok ![1, 0, 1] ![2, 2, 1] := by decide
  have k296 : ¬ ok ![1, 0, 1] ![2, 2, 2] := by decide
  have k297 : ¬ ok ![1, 0, 2] ![0, 0, 0] := by decide
  have k298 : ¬ ok ![1, 0, 2] ![0, 0, 1] := by decide
  have k299 : ¬ ok ![1, 0, 2] ![0, 0, 2] := by decide
  have k300 : ¬ ok ![1, 0, 2] ![0, 1, 0] := by decide
  have k301 : ¬ ok ![1, 0, 2] ![0, 1, 1] := by decide
  have k302 : ¬ ok ![1, 0, 2] ![0, 1, 2] := by decide
  have k303 : ¬ ok ![1, 0, 2] ![0, 2, 0] := by decide
  have k304 : ¬ ok ![1, 0, 2] ![0, 2, 1] := by decide
  have k305 : ¬ ok ![1, 0, 2] ![0, 2, 2] := by decide
  have k306 : ¬ ok ![1, 0, 2] ![1, 0, 0] := by decide
  have k307 : ¬ ok ![1, 0, 2] ![1, 0, 1] := by decide
  have k308 : ok ![1, 0, 2] ![1, 0, 2] := by decide
  have k309 : ¬ ok ![1, 0, 2] ![1, 1, 0] := by decide
  have k310 : ¬ ok ![1, 0, 2] ![1, 1, 1] := by decide
  have k311 : ¬ ok ![1, 0, 2] ![1, 1, 2] := by decide
  have k312 : ¬ ok ![1, 0, 2] ![1, 2, 0] := by decide
  have k313 : ¬ ok ![1, 0, 2] ![1, 2, 1] := by decide
  have k314 : ¬ ok ![1, 0, 2] ![1, 2, 2] := by decide
  have k315 : ¬ ok ![1, 0, 2] ![2, 0, 0] := by decide
  have k316 : ¬ ok ![1, 0, 2] ![2, 0, 1] := by decide
  have k317 : ¬ ok ![1, 0, 2] ![2, 0, 2] := by decide
  have k318 : ¬ ok ![1, 0, 2] ![2, 1, 0] := by decide
  have k319 : ¬ ok ![1, 0, 2] ![2, 1, 1] := by decide
  have k320 : ¬ ok ![1, 0, 2] ![2, 1, 2] := by decide
  have k321 : ¬ ok ![1, 0, 2] ![2, 2, 0] := by decide
  have k322 : ¬ ok ![1, 0, 2] ![2, 2, 1] := by decide
  have k323 : ¬ ok ![1, 0, 2] ![2, 2, 2] := by decide
  have k324 : ¬ ok ![1, 1, 0] ![0, 0, 0] := by decide
  have k325 : ok ![1, 1, 0] ![0, 0, 1] := by decide
  have k326 : ok ![1, 1, 0] ![0, 0, 2] := by decide
  have k327 : ¬ ok ![1, 1, 0] ![0, 1, 0] := by decide
  have k328 : ¬ ok ![1, 1, 0] ![0, 1, 1] := by decide
  have k329 : ¬ ok ![1, 1, 0] ![0, 1, 2] := by decide
  have k330 : ¬ ok ![1, 1, 0] ![0, 2, 0] := by decide
  have k331 : ok ![1, 1, 0] ![0, 2, 1] := by decide
  have k332 : ok ![1, 1, 0] ![0, 2, 2] := by decide
  have k333 : ¬ ok ![1, 1, 0] ![1, 0, 0] := by decide
  have k334 : ¬ ok ![1, 1, 0] ![1, 0, 1] := by decide
  have k335 : ¬ ok ![1, 1, 0] ![1, 0, 2] := by decide
  have k336 : ok ![1, 1, 0] ![1, 1, 0] := by decide
  have k337 : ok ![1, 1, 0] ![1, 1, 1] := by decide
  have k338 : ok ![1, 1, 0] ![1, 1, 2] := by decide
  have k339 : ¬ ok ![1, 1, 0] ![1, 2, 0] := by decide
  have k340 : ok ![1, 1, 0] ![1, 2, 1] := by decide
  have k341 : ok ![1, 1, 0] ![1, 2, 2] := by decide
  have k342 : ¬ ok ![1, 1, 0] ![2, 0, 0] := by decide
  have k343 : ¬ ok ![1, 1, 0] ![2, 0, 1] := by decide
  have k344 : ¬ ok ![1, 1, 0] ![2, 0, 2] := by decide
  have k345 : ¬ ok ![1, 1, 0] ![2, 1, 0] := by decide
  have k346 : ¬ ok ![1, 1, 0] ![2, 1, 1] := by decide
  have k347 : ¬ ok ![1, 1, 0] ![2, 1, 2] := by decide
  have k348 : ¬ ok ![1, 1, 0] ![2, 2, 0] := by decide
  have k349 : ok ![1, 1, 0] ![2, 2, 1] := by decide
  have k350 : ok ![1, 1, 0] ![2, 2, 2] := by decide
  have k351 : ok ![1, 1, 1] ![0, 0, 0] := by decide
  have k352 : ¬ ok ![1, 1, 1] ![0, 0, 1] := by decide
  have k353 : ok ![1, 1, 1] ![0, 0, 2] := by decide
  have k354 : ¬ ok ![1, 1, 1] ![0, 1, 0] := by decide
  have k355 : ¬ ok ![1, 1, 1] ![0, 1, 1] := by decide
  have k356 : ¬ ok ![1, 1, 1] ![0, 1, 2] := by decide
  have k357 : ¬ ok ![1, 1, 1] ![0, 2, 0] := by decide
  have k358 : ¬ ok ![1, 1, 1] ![0, 2, 1] := by decide
  have k359 : ok ![1, 1, 1] ![0, 2, 2] := by decide
  have k360 : ¬ ok ![1, 1, 1] ![1, 0, 0] := by decide
  have k361 : ¬ ok ![1, 1, 1] ![1, 0, 1] := by decide
  have k362 : ¬ ok ![1, 1, 1] ![1, 0, 2] := by decide
  have k363 : ¬ ok ![1, 1, 1] ![1, 1, 0] := by decide
  have k364 : ok ![1, 1, 1] ![1, 1, 1] := by decide
  have k365 : ok ![1, 1, 1] ![1, 1, 2] := by decide
  have k366 : ¬ ok ![1, 1, 1] ![1, 2, 0] := by decide
  have k367 : ¬ ok ![1, 1, 1] ![1, 2, 1] := by decide
  have k368 : ok ![1, 1, 1] ![1, 2, 2] := by decide
  have k369 : ¬ ok ![1, 1, 1] ![2, 0, 0] := by decide
  have k370 : ¬ ok ![1, 1, 1] ![2, 0, 1] := by decide
  have k371 : ¬ ok ![1, 1, 1] ![2, 0, 2] := by decide
  have k372 : ¬ ok ![1, 1, 1] ![2, 1, 0] := by decide
  have k373 : ¬ ok ![1, 1, 1] ![2, 1, 1] := by decide
  have k374 : ¬ ok ![1, 1, 1] ![2, 1, 2] := by decide
  have k375 : ¬ ok ![1, 1, 1] ![2, 2, 0] := by decide
  have k376 : ¬ ok ![1, 1, 1] ![2, 2, 1] := by decide
  have k377 : ok ![1, 1, 1] ![2, 2, 2] := by decide
  have k378 : ¬ ok ![1, 1, 2] ![0, 0, 0] := by decide
  have k379 : ok ![1, 1, 2] ![0, 0, 1] := by decide
  have k380 : ¬ ok ![1, 1, 2] ![0, 0, 2] := by decide
  have k381 : ¬ ok ![1, 1, 2] ![0, 1, 0] := by decide
  have k382 : ¬ ok ![1, 1, 2] ![0, 1, 1] := by decide
  have k383 : ¬ ok ![1, 1, 2] ![0, 1, 2] := by decide
  have k384 : ¬ ok ![1, 1, 2] ![0, 2, 0] := by decide
  have k385 : ¬ ok ![1, 1, 2] ![0, 2, 1] := by decide
  have k386 : ¬ ok ![1, 1, 2] ![0, 2, 2] := by decide
  have k387 : ¬ ok ![1, 1, 2] ![1, 0, 0] := by decide
  have k388 : ¬ ok ![1, 1, 2] ![1, 0, 1] := by decide
  have k389 : ¬ ok ![1, 1, 2] ![1, 0, 2] := by decide
  have k390 : ¬ ok ![1, 1, 2] ![1, 1, 0] := by decide
  have k391 : ¬ ok ![1, 1, 2] ![1, 1, 1] := by decide
  have k392 : ok ![1, 1, 2] ![1, 1, 2] := by decide
  have k393 : ¬ ok ![1, 1, 2] ![1, 2, 0] := by decide
  have k394 : ¬ ok ![1, 1, 2] ![1, 2, 1] := by decide
  have k395 : ¬ ok ![1, 1, 2] ![1, 2, 2] := by decide
  have k396 : ¬ ok ![1, 1, 2] ![2, 0, 0] := by decide
  have k397 : ¬ ok ![1, 1, 2] ![2, 0, 1] := by decide
  have k398 : ¬ ok ![1, 1, 2] ![2, 0, 2] := by decide
  have k399 : ¬ ok ![1, 1, 2] ![2, 1, 0] := by decide
  have k400 : ¬ ok ![1, 1, 2] ![2, 1, 1] := by decide
  have k401 : ¬ ok ![1, 1, 2] ![2, 1, 2] := by decide
  have k402 : ¬ ok ![1, 1, 2] ![2, 2, 0] := by decide
  have k403 : ¬ ok ![1, 1, 2] ![2, 2, 1] := by decide
  have k404 : ¬ ok ![1, 1, 2] ![2, 2, 2] := by decide
  have k405 : ¬ ok ![1, 2, 0] ![0, 0, 0] := by decide
  have k406 : ¬ ok ![1, 2, 0] ![0, 0, 1] := by decide
  have k407 : ¬ ok ![1, 2, 0] ![0, 0, 2] := by decide
  have k408 : ¬ ok ![1, 2, 0] ![0, 1, 0] := by decide
  have k409 : ok ![1, 2, 0] ![0, 1, 1] := by decide
  have k410 : ok ![1, 2, 0] ![0, 1, 2] := by decide
  have k411 : ¬ ok ![1, 2, 0] ![0, 2, 0] := by decide
  have k412 : ¬ ok ![1, 2, 0] ![0, 2, 1] := by decide
  have k413 : ¬ ok ![1, 2, 0] ![0, 2, 2] := by decide
  have k414 : ¬ ok ![1, 2, 0] ![1, 0, 0] := by decide
  have k415 : ¬ ok ![1, 2, 0] ![1, 0, 1] := by decide
  have k416 : ¬ ok ![1, 2, 0] ![1, 0, 2] := by decide
  have k417 : ¬ ok ![1, 2, 0] ![1, 1, 0] := by decide
  have k418 : ¬ ok ![1, 2, 0] ![1, 1, 1] := by decide
  have k419 : ¬ ok ![1, 2, 0] ![1, 1, 2] := by decide
  have k420 : ok ![1, 2, 0] ![1, 2, 0] := by decide
  have k421 : ok ![1, 2, 0] ![1, 2, 1] := by decide
  have k422 : ok ![1, 2, 0] ![1, 2, 2] := by decide
  have k423 : ¬ ok ![1, 2, 0] ![2, 0, 0] := by decide
  have k424 : ¬ ok ![1, 2, 0] ![2, 0, 1] := by decide
  have k425 : ¬ ok ![1, 2, 0] ![2, 0, 2] := by decide
  have k426 : ¬ ok ![1, 2, 0] ![2, 1, 0] := by decide
  have k427 : ¬ ok ![1, 2, 0] ![2, 1, 1] := by decide
  have k428 : ¬ ok ![1, 2, 0] ![2, 1, 2] := by decide
  have k429 : ¬ ok ![1, 2, 0] ![2, 2, 0] := by decide
  have k430 : ¬ ok ![1, 2, 0] ![2, 2, 1] := by decide
  have k431 : ¬ ok ![1, 2, 0] ![2, 2, 2] := by decide
  have k432 : ¬ ok ![1, 2, 1] ![0, 0, 0] := by decide
  have k433 : ¬ ok ![1, 2, 1] ![0, 0, 1] := by decide
  have k434 : ¬ ok ![1, 2, 1] ![0, 0, 2] := by decide
  have k435 : ok ![1, 2, 1] ![0, 1, 0] := by decide
  have k436 : ¬ ok ![1, 2, 1] ![0, 1, 1] := by decide
  have k437 : ok ![1, 2, 1] ![0, 1, 2] := by decide
  have k438 : ¬ ok ![1, 2, 1] ![0, 2, 0] := by decide
  have k439 : ¬ ok ![1, 2, 1] ![0, 2, 1] := by decide
  have k440 : ¬ ok ![1, 2, 1] ![0, 2, 2] := by decide
  have k441 : ¬ ok ![1, 2, 1] ![1, 0, 0] := by decide
  have k442 : ¬ ok ![1, 2, 1] ![1, 0, 1] := by decide
  have k443 : ¬ ok ![1, 2, 1] ![1, 0, 2] := by decide
  have k444 : ¬ ok ![1, 2, 1] ![1, 1, 0] := by decide
  have k445 : ¬ ok ![1, 2, 1] ![1, 1, 1] := by decide
  have k446 : ¬ ok ![1, 2, 1] ![1, 1, 2] := by decide
  have k447 : ¬ ok ![1, 2, 1] ![1, 2, 0] := by decide
  have k448 : ok ![1, 2, 1] ![1, 2, 1] := by decide
  have k449 : ok ![1, 2, 1] ![1, 2, 2] := by decide
  have k450 : ¬ ok ![1, 2, 1] ![2, 0, 0] := by decide
  have k451 : ¬ ok ![1, 2, 1] ![2, 0, 1] := by decide
  have k452 : ¬ ok ![1, 2, 1] ![2, 0, 2] := by decide
  have k453 : ¬ ok ![1, 2, 1] ![2, 1, 0] := by decide
  have k454 : ¬ ok ![1, 2, 1] ![2, 1, 1] := by decide
  have k455 : ¬ ok ![1, 2, 1] ![2, 1, 2] := by decide
  have k456 : ¬ ok ![1, 2, 1] ![2, 2, 0] := by decide
  have k457 : ¬ ok ![1, 2, 1] ![2, 2, 1] := by decide
  have k458 : ¬ ok ![1, 2, 1] ![2, 2, 2] := by decide
  have k459 : ¬ ok ![1, 2, 2] ![0, 0, 0] := by decide
  have k460 : ¬ ok ![1, 2, 2] ![0, 0, 1] := by decide
  have k461 : ¬ ok ![1, 2, 2] ![0, 0, 2] := by decide
  have k462 : ¬ ok ![1, 2, 2] ![0, 1, 0] := by decide
  have k463 : ok ![1, 2, 2] ![0, 1, 1] := by decide
  have k464 : ¬ ok ![1, 2, 2] ![0, 1, 2] := by decide
  have k465 : ¬ ok ![1, 2, 2] ![0, 2, 0] := by decide
  have k466 : ¬ ok ![1, 2, 2] ![0, 2, 1] := by decide
  have k467 : ¬ ok ![1, 2, 2] ![0, 2, 2] := by decide
  have k468 : ¬ ok ![1, 2, 2] ![1, 0, 0] := by decide
  have k469 : ¬ ok ![1, 2, 2] ![1, 0, 1] := by decide
  have k470 : ¬ ok ![1, 2, 2] ![1, 0, 2] := by decide
  have k471 : ¬ ok ![1, 2, 2] ![1, 1, 0] := by decide
  have k472 : ¬ ok ![1, 2, 2] ![1, 1, 1] := by decide
  have k473 : ¬ ok ![1, 2, 2] ![1, 1, 2] := by decide
  have k474 : ¬ ok ![1, 2, 2] ![1, 2, 0] := by decide
  have k475 : ¬ ok ![1, 2, 2] ![1, 2, 1] := by decide
  have k476 : ok ![1, 2, 2] ![1, 2, 2] := by decide
  have k477 : ¬ ok ![1, 2, 2] ![2, 0, 0] := by decide
  have k478 : ¬ ok ![1, 2, 2] ![2, 0, 1] := by decide
  have k479 : ¬ ok ![1, 2, 2] ![2, 0, 2] := by decide
  have k480 : ¬ ok ![1, 2, 2] ![2, 1, 0] := by decide
  have k481 : ¬ ok ![1, 2, 2] ![2, 1, 1] := by decide
  have k482 : ¬ ok ![1, 2, 2] ![2, 1, 2] := by decide
  have k483 : ¬ ok ![1, 2, 2] ![2, 2, 0] := by decide
  have k484 : ¬ ok ![1, 2, 2] ![2, 2, 1] := by decide
  have k485 : ¬ ok ![1, 2, 2] ![2, 2, 2] := by decide
  have k486 : ¬ ok ![2, 0, 0] ![0, 0, 0] := by decide
  have k487 : ¬ ok ![2, 0, 0] ![0, 0, 1] := by decide
  have k488 : ¬ ok ![2, 0, 0] ![0, 0, 2] := by decide
  have k489 : ¬ ok ![2, 0, 0] ![0, 1, 0] := by decide
  have k490 : ¬ ok ![2, 0, 0] ![0, 1, 1] := by decide
  have k491 : ¬ ok ![2, 0, 0] ![0, 1, 2] := by decide
  have k492 : ¬ ok ![2, 0, 0] ![0, 2, 0] := by decide
  have k493 : ¬ ok ![2, 0, 0] ![0, 2, 1] := by decide
  have k494 : ok ![2, 0, 0] ![0, 2, 2] := by decide
  have k495 : ¬ ok ![2, 0, 0] ![1, 0, 0] := by decide
  have k496 : ¬ ok ![2, 0, 0] ![1, 0, 1] := by decide
  have k497 : ¬ ok ![2, 0, 0] ![1, 0, 2] := by decide
  have k498 : ¬ ok ![2, 0, 0] ![1, 1, 0] := by decide
  have k499 : ok ![2, 0, 0] ![1, 1, 1] := by decide
  have k500 : ok ![2, 0, 0] ![1, 1, 2] := by decide
  have k501 : ¬ ok ![2, 0, 0] ![1, 2, 0] := by decide
  have k502 : ¬ ok ![2, 0, 0] ![1, 2, 1] := by decide
  have k503 : ok ![2, 0, 0] ![1, 2, 2] := by decide
  have k504 : ok ![2, 0, 0] ![2, 0, 0] := by decide
  have k505 : ok ![2, 0, 0] ![2, 0, 1] := by decide
  have k506 : ok ![2, 0, 0] ![2, 0, 2] := by decide
  have k507 : ¬ ok ![2, 0, 0] ![2, 1, 0] := by decide
  have k508 : ok ![2, 0, 0] ![2, 1, 1] := by decide
  have k509 : ok ![2, 0, 0] ![2, 1, 2] := by decide
  have k510 : ¬ ok ![2, 0, 0] ![2, 2, 0] := by decide
  have k511 : ¬ ok ![2, 0, 0] ![2, 2, 1] := by decide
  have k512 : ok ![2, 0, 0] ![2, 2, 2] := by decide
  have k513 : ¬ ok ![2, 0, 1] ![0, 0, 0] := by decide
  have k514 : ¬ ok ![2, 0, 1] ![0, 0, 1] := by decide
  have k515 : ¬ ok ![2, 0, 1] ![0, 0, 2] := by decide
  have k516 : ¬ ok ![2, 0, 1] ![0, 1, 0] := by decide
  have k517 : ¬ ok ![2, 0, 1] ![0, 1, 1] := by decide
  have k518 : ¬ ok ![2, 0, 1] ![0, 1, 2] := by decide
  have k519 : ¬ ok ![2, 0, 1] ![0, 2, 0] := by decide
  have k520 : ¬ ok ![2, 0, 1] ![0, 2, 1] := by decide
  have k521 : ¬ ok ![2, 0, 1] ![0, 2, 2] := by decide
  have k522 : ¬ ok ![2, 0, 1] ![1, 0, 0] := by decide
  have k523 : ¬ ok ![2, 0, 1] ![1, 0, 1] := by decide
  have k524 : ¬ ok ![2, 0, 1] ![1, 0, 2] := by decide
  have k525 : ¬ ok ![2, 0, 1] ![1, 1, 0] := by decide
  have k526 : ¬ ok ![2, 0, 1] ![1, 1, 1] := by decide
  have k527 : ok ![2, 0, 1] ![1, 1, 2] := by decide
  have k528 : ¬ ok ![2, 0, 1] ![1, 2, 0] := by decide
  have k529 : ¬ ok ![2, 0, 1] ![1, 2, 1] := by decide
  have k530 : ¬ ok ![2, 0, 1] ![1, 2, 2] := by decide
  have k531 : ¬ ok ![2, 0, 1] ![2, 0, 0] := by decide
  have k532 : ok ![2, 0, 1] ![2, 0, 1] := by decide
  have k533 : ok ![2, 0, 1] ![2, 0, 2] := by decide
  have k534 : ¬ ok ![2, 0, 1] ![2, 1, 0] := by decide
  have k535 : ¬ ok ![2, 0, 1] ![2, 1, 1] := by decide
  have k536 : ok ![2, 0, 1] ![2, 1, 2] := by decide
  have k537 : ¬ ok ![2, 0, 1] ![2, 2, 0] := by decide
  have k538 : ¬ ok ![2, 0, 1] ![2, 2, 1] := by decide
  have k539 : ¬ ok ![2, 0, 1] ![2, 2, 2] := by decide
  have k540 : ¬ ok ![2, 0, 2] ![0, 0, 0] := by decide
  have k541 : ¬ ok ![2, 0, 2] ![0, 0, 1] := by decide
  have k542 : ¬ ok ![2, 0, 2] ![0, 0, 2] := by decide
  have k543 : ¬ ok ![2, 0, 2] ![0, 1, 0] := by decide
  have k544 : ¬ ok ![2, 0, 2] ![0, 1, 1] := by decide
  have k545 : ¬ ok ![2, 0, 2] ![0, 1, 2] := by decide
  have k546 : ¬ ok ![2, 0, 2] ![0, 2, 0] := by decide
  have k547 : ¬ ok ![2, 0, 2] ![0, 2, 1] := by decide
  have k548 : ¬ ok ![2, 0, 2] ![0, 2, 2] := by decide
  have k549 : ¬ ok ![2, 0, 2] ![1, 0, 0] := by decide
  have k550 : ¬ ok ![2, 0, 2] ![1, 0, 1] := by decide
  have k551 : ¬ ok ![2, 0, 2] ![1, 0, 2] := by decide
  have k552 : ¬ ok ![2, 0, 2] ![1, 1, 0] := by decide
  have k553 : ¬ ok ![2, 0, 2] ![1, 1, 1] := by decide
  have k554 : ¬ ok ![2, 0, 2] ![1, 1, 2] := by decide
  have k555 : ¬ ok ![2, 0, 2] ![1, 2, 0] := by decide
  have k556 : ¬ ok ![2, 0, 2] ![1, 2, 1] := by decide
  have k557 : ¬ ok ![2, 0, 2] ![1, 2, 2] := by decide
  have k558 : ¬ ok ![2, 0, 2] ![2, 0, 0] := by decide
  have k559 : ¬ ok ![2, 0, 2] ![2, 0, 1] := by decide
  have k560 : ok ![2, 0, 2] ![2, 0, 2] := by decide
  have k561 : ¬ ok ![2, 0, 2] ![2, 1, 0] := by decide
  have k562 : ¬ ok ![2, 0, 2] ![2, 1, 1] := by decide
  have k563 : ¬ ok ![2, 0, 2] ![2, 1, 2] := by decide
  have k564 : ¬ ok ![2, 0, 2] ![2, 2, 0] := by decide
  have k565 : ¬ ok ![2, 0, 2] ![2, 2, 1] := by decide
  have k566 : ¬ ok ![2, 0, 2] ![2, 2, 2] := by decide
  have k567 : ¬ ok ![2, 1, 0] ![0, 0, 0] := by decide
  have k568 : ¬ ok ![2, 1, 0] ![0, 0, 1] := by decide
  have k569 : ¬ ok ![2, 1, 0] ![0, 0, 2] := by decide
  have k570 : ¬ ok ![2, 1, 0] ![0, 1, 0] := by decide
  have k571 : ¬ ok ![2, 1, 0] ![0, 1, 1] := by decide
  have k572 : ¬ ok ![2, 1, 0] ![0, 1, 2] := by decide
  have k573 : ¬ ok ![2, 1, 0] ![0, 2, 0] := by decide
  have k574 : ¬ ok ![2, 1, 0] ![0, 2, 1] := by decide
  have k575 : ¬ ok ![2, 1, 0] ![0, 2, 2] := by decide
  have k576 : ¬ ok ![2, 1, 0] ![1, 0, 0] := by decide
  have k577 : ok ![2, 1, 0] ![1, 0, 1] := by decide
  have k578 : ok ![2, 1, 0] ![1, 0, 2] := by decide
  have k579 : ¬ ok ![2, 1, 0] ![1, 1, 0] := by decide
  have k580 : ¬ ok ![2, 1, 0] ![1, 1, 1] := by decide
  have k581 : ¬ ok ![2, 1, 0] ![1, 1, 2] := by decide
  have k582 : ¬ ok ![2, 1, 0] ![1, 2, 0] := by decide
  have k583 : ok ![2, 1, 0] ![1, 2, 1] := by decide
  have k584 : ok ![2, 1, 0] ![1, 2, 2] := by decide
  have k585 : ¬ ok ![2, 1, 0] ![2, 0, 0] := by decide
  have k586 : ¬ ok ![2, 1, 0] ![2, 0, 1] := by decide
  have k587 : ¬ ok ![2, 1, 0] ![2, 0, 2] := by decide
  have k588 : ok ![2, 1, 0] ![2, 1, 0] := by decide
  have k589 : ok ![2, 1, 0] ![2, 1, 1] := by decide
  have k590 : ok ![2, 1, 0] ![2, 1, 2] := by decide
  have k591 : ¬ ok ![2, 1, 0] ![2, 2, 0] := by decide
  have k592 : ok ![2, 1, 0] ![2, 2, 1] := by decide
  have k593 : ok ![2, 1, 0] ![2, 2, 2] := by decide
  have k594 : ¬ ok ![2, 1, 1] ![0, 0, 0] := by decide
  have k595 : ¬ ok ![2, 1, 1] ![0, 0, 1] := by decide
  have k596 : ¬ ok ![2, 1, 1] ![0, 0, 2] := by decide
  have k597 : ¬ ok ![2, 1, 1] ![0, 1, 0] := by decide
  have k598 : ¬ ok ![2, 1, 1] ![0, 1, 1] := by decide
  have k599 : ¬ ok ![2, 1, 1] ![0, 1, 2] := by decide
  have k600 : ¬ ok ![2, 1, 1] ![0, 2, 0] := by decide
  have k601 : ¬ ok ![2, 1, 1] ![0, 2, 1] := by decide
  have k602 : ¬ ok ![2, 1, 1] ![0, 2, 2] := by decide
  have k603 : ok ![2, 1, 1] ![1, 0, 0] := by decide
  have k604 : ¬ ok ![2, 1, 1] ![1, 0, 1] := by decide
  have k605 : ok ![2, 1, 1] ![1, 0, 2] := by decide
  have k606 : ¬ ok ![2, 1, 1] ![1, 1, 0] := by decide
  have k607 : ¬ ok ![2, 1, 1] ![1, 1, 1] := by decide
  have k608 : ¬ ok ![2, 1, 1] ![1, 1, 2] := by decide
  have k609 : ¬ ok ![2, 1, 1] ![1, 2, 0] := by decide
  have k610 : ¬ ok ![2, 1, 1] ![1, 2, 1] := by decide
  have k611 : ok ![2, 1, 1] ![1, 2, 2] := by decide
  have k612 : ¬ ok ![2, 1, 1] ![2, 0, 0] := by decide
  have k613 : ¬ ok ![2, 1, 1] ![2, 0, 1] := by decide
  have k614 : ¬ ok ![2, 1, 1] ![2, 0, 2] := by decide
  have k615 : ¬ ok ![2, 1, 1] ![2, 1, 0] := by decide
  have k616 : ok ![2, 1, 1] ![2, 1, 1] := by decide
  have k617 : ok ![2, 1, 1] ![2, 1, 2] := by decide
  have k618 : ¬ ok ![2, 1, 1] ![2, 2, 0] := by decide
  have k619 : ¬ ok ![2, 1, 1] ![2, 2, 1] := by decide
  have k620 : ok ![2, 1, 1] ![2, 2, 2] := by decide
  have k621 : ¬ ok ![2, 1, 2] ![0, 0, 0] := by decide
  have k622 : ¬ ok ![2, 1, 2] ![0, 0, 1] := by decide
  have k623 : ¬ ok ![2, 1, 2] ![0, 0, 2] := by decide
  have k624 : ¬ ok ![2, 1, 2] ![0, 1, 0] := by decide
  have k625 : ¬ ok ![2, 1, 2] ![0, 1, 1] := by decide
  have k626 : ¬ ok ![2, 1, 2] ![0, 1, 2] := by decide
  have k627 : ¬ ok ![2, 1, 2] ![0, 2, 0] := by decide
  have k628 : ¬ ok ![2, 1, 2] ![0, 2, 1] := by decide
  have k629 : ¬ ok ![2, 1, 2] ![0, 2, 2] := by decide
  have k630 : ¬ ok ![2, 1, 2] ![1, 0, 0] := by decide
  have k631 : ok ![2, 1, 2] ![1, 0, 1] := by decide
  have k632 : ¬ ok ![2, 1, 2] ![1, 0, 2] := by decide
  have k633 : ¬ ok ![2, 1, 2] ![1, 1, 0] := by decide
  have k634 : ¬ ok ![2, 1, 2] ![1, 1, 1] := by decide
  have k635 : ¬ ok ![2, 1, 2] ![1, 1, 2] := by decide
  have k636 : ¬ ok ![2, 1, 2] ![1, 2, 0] := by decide
  have k637 : ¬ ok ![2, 1, 2] ![1, 2, 1] := by decide
  have k638 : ¬ ok ![2, 1, 2] ![1, 2, 2] := by decide
  have k639 : ¬ ok ![2, 1, 2] ![2, 0, 0] := by decide
  have k640 : ¬ ok ![2, 1, 2] ![2, 0, 1] := by decide
  have k641 : ¬ ok ![2, 1, 2] ![2, 0, 2] := by decide
  have k642 : ¬ ok ![2, 1, 2] ![2, 1, 0] := by decide
  have k643 : ¬ ok ![2, 1, 2] ![2, 1, 1] := by decide
  have k644 : ok ![2, 1, 2] ![2, 1, 2] := by decide
  have k645 : ¬ ok ![2, 1, 2] ![2, 2, 0] := by decide
  have k646 : ¬ ok ![2, 1, 2] ![2, 2, 1] := by decide
  have k647 : ¬ ok ![2, 1, 2] ![2, 2, 2] := by decide
  have k648 : ¬ ok ![2, 2, 0] ![0, 0, 0] := by decide
  have k649 : ¬ ok ![2, 2, 0] ![0, 0, 1] := by decide
  have k650 : ok ![2, 2, 0] ![0, 0, 2] := by decide
  have k651 : ¬ ok ![2, 2, 0] ![0, 1, 0] := by decide
  have k652 : ¬ ok ![2, 2, 0] ![0, 1, 1] := by decide
  have k653 : ¬ ok ![2, 2, 0] ![0, 1, 2] := by decide
  have k654 : ¬ ok ![2, 2, 0] ![0, 2, 0] := by decide
  have k655 : ¬ ok ![2, 2, 0] ![0, 2, 1] := by decide
  have k656 : ¬ ok ![2, 2, 0] ![0, 2, 2] := by decide
  have k657 : ¬ ok ![2, 2, 0] ![1, 0, 0] := by decide
  have k658 : ¬ ok ![2, 2, 0] ![1, 0, 1] := by decide
  have k659 : ¬ ok ![2, 2, 0] ![1, 0, 2] := by decide
  have k660 : ¬ ok ![2, 2, 0] ![1, 1, 0] := by decide
  have k661 : ok ![2, 2, 0] ![1, 1, 1] := by decide
  have k662 : ok ![2, 2, 0] ![1, 1, 2] := by decide
  have k663 : ¬ ok ![2, 2, 0] ![1, 2, 0] := by decide
  have k664 : ¬ ok ![2, 2, 0] ![1, 2, 1] := by decide
  have k665 : ¬ ok ![2, 2, 0] ![1, 2, 2] := by decide
  have k666 : ¬ ok ![2, 2, 0] ![2, 0, 0] := by decide
  have k667 : ¬ ok ![2, 2, 0] ![2, 0, 1] := by decide
  have k668 : ¬ ok ![2, 2, 0] ![2, 0, 2] := by decide
  have k669 : ¬ ok ![2, 2, 0] ![2, 1, 0] := by decide
  have k670 : ¬ ok ![2, 2, 0] ![2, 1, 1] := by decide
  have k671 : ¬ ok ![2, 2, 0] ![2, 1, 2] := by decide
  have k672 : ok ![2, 2, 0] ![2, 2, 0] := by decide
  have k673 : ok ![2, 2, 0] ![2, 2, 1] := by decide
  have k674 : ok ![2, 2, 0] ![2, 2, 2] := by decide
  have k675 : ¬ ok ![2, 2, 1] ![0, 0, 0] := by decide
  have k676 : ¬ ok ![2, 2, 1] ![0, 0, 1] := by decide
  have k677 : ¬ ok ![2, 2, 1] ![0, 0, 2] := by decide
  have k678 : ¬ ok ![2, 2, 1] ![0, 1, 0] := by decide
  have k679 : ¬ ok ![2, 2, 1] ![0, 1, 1] := by decide
  have k680 : ¬ ok ![2, 2, 1] ![0, 1, 2] := by decide
  have k681 : ¬ ok ![2, 2, 1] ![0, 2, 0] := by decide
  have k682 : ¬ ok ![2, 2, 1] ![0, 2, 1] := by decide
  have k683 : ¬ ok ![2, 2, 1] ![0, 2, 2] := by decide
  have k684 : ¬ ok ![2, 2, 1] ![1, 0, 0] := by decide
  have k685 : ¬ ok ![2, 2, 1] ![1, 0, 1] := by decide
  have k686 : ¬ ok ![2, 2, 1] ![1, 0, 2] := by decide
  have k687 : ok ![2, 2, 1] ![1, 1, 0] := by decide
  have k688 : ¬ ok ![2, 2, 1] ![1, 1, 1] := by decide
  have k689 : ok ![2, 2, 1] ![1, 1, 2] := by decide
  have k690 : ¬ ok ![2, 2, 1] ![1, 2, 0] := by decide
  have k691 : ¬ ok ![2, 2, 1] ![1, 2, 1] := by decide
  have k692 : ¬ ok ![2, 2, 1] ![1, 2, 2] := by decide
  have k693 : ¬ ok ![2, 2, 1] ![2, 0, 0] := by decide
  have k694 : ¬ ok ![2, 2, 1] ![2, 0, 1] := by decide
  have k695 : ¬ ok ![2, 2, 1] ![2, 0, 2] := by decide
  have k696 : ¬ ok ![2, 2, 1] ![2, 1, 0] := by decide
  have k697 : ¬ ok ![2, 2, 1] ![2, 1, 1] := by decide
  have k698 : ¬ ok ![2, 2, 1] ![2, 1, 2] := by decide
  have k699 : ¬ ok ![2, 2, 1] ![2, 2, 0] := by decide
  have k700 : ok ![2, 2, 1] ![2, 2, 1] := by decide
  have k701 : ok ![2, 2, 1] ![2, 2, 2] := by decide
  have k702 : ok ![2, 2, 2] ![0, 0, 0] := by decide
  have k703 : ¬ ok ![2, 2, 2] ![0, 0, 1] := by decide
  have k704 : ¬ ok ![2, 2, 2] ![0, 0, 2] := by decide
  have k705 : ¬ ok ![2, 2, 2] ![0, 1, 0] := by decide
  have k706 : ¬ ok ![2, 2, 2] ![0, 1, 1] := by decide
  have k707 : ¬ ok ![2, 2, 2] ![0, 1, 2] := by decide
  have k708 : ¬ ok ![2, 2, 2] ![0, 2, 0] := by decide
  have k709 : ¬ ok ![2, 2, 2] ![0, 2, 1] := by decide
  have k710 : ¬ ok ![2, 2, 2] ![0, 2, 2] := by decide
  have k711 : ¬ ok ![2, 2, 2] ![1, 0, 0] := by decide
  have k712 : ¬ ok ![2, 2, 2] ![1, 0, 1] := by decide
  have k713 : ¬ ok ![2, 2, 2] ![1, 0, 2] := by decide
  have k714 : ¬ ok ![2, 2, 2] ![1, 1, 0] := by decide
  have k715 : ok ![2, 2, 2] ![1, 1, 1] := by decide
  have k716 : ¬ ok ![2, 2, 2] ![1, 1, 2] := by decide
  have k717 : ¬ ok ![2, 2, 2] ![1, 2, 0] := by decide
  have k718 : ¬ ok ![2, 2, 2] ![1, 2, 1] := by decide
  have k719 : ¬ ok ![2, 2, 2] ![1, 2, 2] := by decide
  have k720 : ¬ ok ![2, 2, 2] ![2, 0, 0] := by decide
  have k721 : ¬ ok ![2, 2, 2] ![2, 0, 1] := by decide
  have k722 : ¬ ok ![2, 2, 2] ![2, 0, 2] := by decide
  have k723 : ¬ ok ![2, 2, 2] ![2, 1, 0] := by decide
  have k724 : ¬ ok ![2, 2, 2] ![2, 1, 1] := by decide
  have k725 : ¬ ok ![2, 2, 2] ![2, 1, 2] := by decide
  have k726 : ¬ ok ![2, 2, 2] ![2, 2, 0] := by decide
  have k727 : ¬ ok ![2, 2, 2] ![2, 2, 1] := by decide
  have k728 : ok ![2, 2, 2] ![2, 2, 2] := by decide
  simp only [H_succ, sumC, k0, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, k12, k13, k14, k15, k16, k17, k18, k19, k20, k21, k22, k23, k24, k25, k26, k27, k28, k29, k30, k31, k32, k33, k34, k35, k36, k37, k38, k39, k40, k41, k42, k43, k44, k45, k46, k47, k48, k49, k50, k51, k52, k53, k54, k55, k56, k57, k58, k59, k60, k61, k62, k63, k64, k65, k66, k67, k68, k69, k70, k71, k72, k73, k74, k75, k76, k77, k78, k79, k80, k81, k82, k83, k84, k85, k86, k87, k88, k89, k90, k91, k92, k93, k94, k95, k96, k97, k98, k99, k100, k101, k102, k103, k104, k105, k106, k107, k108, k109, k110, k111, k112, k113, k114, k115, k116, k117, k118, k119, k120, k121, k122, k123, k124, k125, k126, k127, k128, k129, k130, k131, k132, k133, k134, k135, k136, k137, k138, k139, k140, k141, k142, k143, k144, k145, k146, k147, k148, k149, k150, k151, k152, k153, k154, k155, k156, k157, k158, k159, k160, k161, k162, k163, k164, k165, k166, k167, k168, k169, k170, k171, k172, k173, k174, k175, k176, k177, k178, k179, k180, k181, k182, k183, k184, k185, k186, k187, k188, k189, k190, k191, k192, k193, k194, k195, k196, k197, k198, k199, k200, k201, k202, k203, k204, k205, k206, k207, k208, k209, k210, k211, k212, k213, k214, k215, k216, k217, k218, k219, k220, k221, k222, k223, k224, k225, k226, k227, k228, k229, k230, k231, k232, k233, k234, k235, k236, k237, k238, k239, k240, k241, k242, k243, k244, k245, k246, k247, k248, k249, k250, k251, k252, k253, k254, k255, k256, k257, k258, k259, k260, k261, k262, k263, k264, k265, k266, k267, k268, k269, k270, k271, k272, k273, k274, k275, k276, k277, k278, k279, k280, k281, k282, k283, k284, k285, k286, k287, k288, k289, k290, k291, k292, k293, k294, k295, k296, k297, k298, k299, k300, k301, k302, k303, k304, k305, k306, k307, k308, k309, k310, k311, k312, k313, k314, k315, k316, k317, k318, k319, k320, k321, k322, k323, k324, k325, k326, k327, k328, k329, k330, k331, k332, k333, k334, k335, k336, k337, k338, k339, k340, k341, k342, k343, k344, k345, k346, k347, k348, k349, k350, k351, k352, k353, k354, k355, k356, k357, k358, k359, k360, k361, k362, k363, k364, k365, k366, k367, k368, k369, k370, k371, k372, k373, k374, k375, k376, k377, k378, k379, k380, k381, k382, k383, k384, k385, k386, k387, k388, k389, k390, k391, k392, k393, k394, k395, k396, k397, k398, k399, k400, k401, k402, k403, k404, k405, k406, k407, k408, k409, k410, k411, k412, k413, k414, k415, k416, k417, k418, k419, k420, k421, k422, k423, k424, k425, k426, k427, k428, k429, k430, k431, k432, k433, k434, k435, k436, k437, k438, k439, k440, k441, k442, k443, k444, k445, k446, k447, k448, k449, k450, k451, k452, k453, k454, k455, k456, k457, k458, k459, k460, k461, k462, k463, k464, k465, k466, k467, k468, k469, k470, k471, k472, k473, k474, k475, k476, k477, k478, k479, k480, k481, k482, k483, k484, k485, k486, k487, k488, k489, k490, k491, k492, k493, k494, k495, k496, k497, k498, k499, k500, k501, k502, k503, k504, k505, k506, k507, k508, k509, k510, k511, k512, k513, k514, k515, k516, k517, k518, k519, k520, k521, k522, k523, k524, k525, k526, k527, k528, k529, k530, k531, k532, k533, k534, k535, k536, k537, k538, k539, k540, k541, k542, k543, k544, k545, k546, k547, k548, k549, k550, k551, k552, k553, k554, k555, k556, k557, k558, k559, k560, k561, k562, k563, k564, k565, k566, k567, k568, k569, k570, k571, k572, k573, k574, k575, k576, k577, k578, k579, k580, k581, k582, k583, k584, k585, k586, k587, k588, k589, k590, k591, k592, k593, k594, k595, k596, k597, k598, k599, k600, k601, k602, k603, k604, k605, k606, k607, k608, k609, k610, k611, k612, k613, k614, k615, k616, k617, k618, k619, k620, k621, k622, k623, k624, k625, k626, k627, k628, k629, k630, k631, k632, k633, k634, k635, k636, k637, k638, k639, k640, k641, k642, k643, k644, k645, k646, k647, k648, k649, k650, k651, k652, k653, k654, k655, k656, k657, k658, k659, k660, k661, k662, k663, k664, k665, k666, k667, k668, k669, k670, k671, k672, k673, k674, k675, k676, k677, k678, k679, k680, k681, k682, k683, k684, k685, k686, k687, k688, k689, k690, k691, k692, k693, k694, k695, k696, k697, k698, k699, k700, k701, k702, k703, k704, k705, k706, k707, k708, k709, k710, k711, k712, k713, k714, k715, k716, k717, k718, k719, k720, k721, k722, k723, k724, k725, k726, k727, k728, if_true, if_false, add_zero, zero_add]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> trivial

theorem B1 :
    H 1 ![0, 0, 0] = 10 ∧
    H 1 ![0, 0, 1] = 4 ∧
    H 1 ![0, 0, 2] = 1 ∧
    H 1 ![0, 1, 0] = 7 ∧
    H 1 ![0, 1, 1] = 4 ∧
    H 1 ![0, 1, 2] = 1 ∧
    H 1 ![0, 2, 0] = 3 ∧
    H 1 ![0, 2, 1] = 2 ∧
    H 1 ![0, 2, 2] = 1 ∧
    H 1 ![1, 0, 0] = 12 ∧
    H 1 ![1, 0, 1] = 5 ∧
    H 1 ![1, 0, 2] = 1 ∧
    H 1 ![1, 1, 0] = 11 ∧
    H 1 ![1, 1, 1] = 7 ∧
    H 1 ![1, 1, 2] = 2 ∧
    H 1 ![1, 2, 0] = 5 ∧
    H 1 ![1, 2, 1] = 4 ∧
    H 1 ![1, 2, 2] = 2 ∧
    H 1 ![2, 0, 0] = 10 ∧
    H 1 ![2, 0, 1] = 4 ∧
    H 1 ![2, 0, 2] = 1 ∧
    H 1 ![2, 1, 0] = 9 ∧
    H 1 ![2, 1, 1] = 6 ∧
    H 1 ![2, 1, 2] = 2 ∧
    H 1 ![2, 2, 0] = 6 ∧
    H 1 ![2, 2, 1] = 4 ∧
    H 1 ![2, 2, 2] = 3 := by
  obtain ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, g25, g26⟩ := Hs 0
  
  simp only [Nat.reduceAdd, zero_add] at g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 g16 g17 g18 g19 g20 g21 g22 g23 g24 g25 g26
  simp only [g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, g25, g26, H0]
  norm_num

theorem B2 :
    H 2 ![0, 0, 0] = 35 ∧
    H 2 ![0, 0, 1] = 8 ∧
    H 2 ![0, 0, 2] = 1 ∧
    H 2 ![0, 1, 0] = 21 ∧
    H 2 ![0, 1, 1] = 8 ∧
    H 2 ![0, 1, 2] = 1 ∧
    H 2 ![0, 2, 0] = 6 ∧
    H 2 ![0, 2, 1] = 3 ∧
    H 2 ![0, 2, 2] = 1 ∧
    H 2 ![1, 0, 0] = 46 ∧
    H 2 ![1, 0, 1] = 11 ∧
    H 2 ![1, 0, 2] = 1 ∧
    H 2 ![1, 1, 0] = 41 ∧
    H 2 ![1, 1, 1] = 26 ∧
    H 2 ![1, 1, 2] = 6 ∧
    H 2 ![1, 2, 0] = 16 ∧
    H 2 ![1, 2, 1] = 14 ∧
    H 2 ![1, 2, 2] = 6 ∧
    H 2 ![2, 0, 0] = 38 ∧
    H 2 ![2, 0, 1] = 9 ∧
    H 2 ![2, 0, 2] = 1 ∧
    H 2 ![2, 1, 0] = 36 ∧
    H 2 ![2, 1, 1] = 26 ∧
    H 2 ![2, 1, 2] = 7 ∧
    H 2 ![2, 2, 0] = 23 ∧
    H 2 ![2, 2, 1] = 20 ∧
    H 2 ![2, 2, 2] = 20 := by
  obtain ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, g25, g26⟩ := Hs 1
  obtain ⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26⟩ := B1
  simp only [Nat.reduceAdd] at g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 g16 g17 g18 g19 g20 g21 g22 g23 g24 g25 g26
  simp only [g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, g25, g26, w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26]
  norm_num

theorem B3 :
    H 3 ![0, 0, 0] = 112 ∧
    H 3 ![0, 0, 1] = 16 ∧
    H 3 ![0, 0, 2] = 1 ∧
    H 3 ![0, 1, 0] = 54 ∧
    H 3 ![0, 1, 1] = 16 ∧
    H 3 ![0, 1, 2] = 1 ∧
    H 3 ![0, 2, 0] = 10 ∧
    H 3 ![0, 2, 1] = 4 ∧
    H 3 ![0, 2, 2] = 1 ∧
    H 3 ![1, 0, 0] = 159 ∧
    H 3 ![1, 0, 1] = 26 ∧
    H 3 ![1, 0, 2] = 1 ∧
    H 3 ![1, 1, 0] = 146 ∧
    H 3 ![1, 1, 1] = 95 ∧
    H 3 ![1, 1, 2] = 14 ∧
    H 3 ![1, 2, 0] = 45 ∧
    H 3 ![1, 2, 1] = 42 ∧
    H 3 ![1, 2, 2] = 14 ∧
    H 3 ![2, 0, 0] = 140 ∧
    H 3 ![2, 0, 1] = 23 ∧
    H 3 ![2, 0, 2] = 1 ∧
    H 3 ![2, 1, 0] = 141 ∧
    H 3 ![2, 1, 1] = 106 ∧
    H 3 ![2, 1, 2] = 18 ∧
    H 3 ![2, 2, 0] = 96 ∧
    H 3 ![2, 2, 1] = 87 ∧
    H 3 ![2, 2, 2] = 81 := by
  obtain ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, g25, g26⟩ := Hs 2
  obtain ⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26⟩ := B2
  simp only [Nat.reduceAdd] at g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 g16 g17 g18 g19 g20 g21 g22 g23 g24 g25 g26
  simp only [g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, g25, g26, w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26]
  norm_num

theorem Hf (m : ℕ) (hm : 3 ≤ m) :
    (H m ![0, 0, 0] : ℚ) = (1 / 2 : ℚ) + (-2 : ℚ) * (2 : ℚ) ^ m + (85 / 18 : ℚ) * (3 : ℚ) ^ m ∧
    (H m ![0, 0, 1] : ℚ) = (2 : ℚ) * (2 : ℚ) ^ m ∧
    (H m ![0, 0, 2] : ℚ) = (1 : ℚ) ∧
    (H m ![0, 1, 0] : ℚ) = (9 / 4 : ℚ) * (2 : ℚ) ^ m + (3 / 2 : ℚ) * (m : ℚ) ^ 1 * (2 : ℚ) ^ m ∧
    (H m ![0, 1, 1] : ℚ) = (2 : ℚ) * (2 : ℚ) ^ m ∧
    (H m ![0, 1, 2] : ℚ) = (1 : ℚ) ∧
    (H m ![0, 2, 0] : ℚ) = (1 : ℚ) + (3 / 2 : ℚ) * (m : ℚ) ^ 1 + (1 / 2 : ℚ) * (m : ℚ) ^ 2 ∧
    (H m ![0, 2, 1] : ℚ) = (1 : ℚ) + (1 : ℚ) * (m : ℚ) ^ 1 ∧
    (H m ![0, 2, 2] : ℚ) = (1 : ℚ) ∧
    (H m ![1, 0, 0] : ℚ) = (-1 / 2 : ℚ) + (-73 / 16 : ℚ) * (2 : ℚ) ^ m + (-5 / 4 : ℚ) * (m : ℚ) ^ 1 * (2 : ℚ) ^ m + (3 / 16 : ℚ) * (m : ℚ) ^ 2 * (2 : ℚ) ^ m + (425 / 54 : ℚ) * (3 : ℚ) ^ m ∧
    (H m ![1, 0, 1] : ℚ) = (7 / 4 : ℚ) * (2 : ℚ) ^ m + (1 / 2 : ℚ) * (m : ℚ) ^ 1 * (2 : ℚ) ^ m ∧
    (H m ![1, 0, 2] : ℚ) = (1 : ℚ) ∧
    (H m ![1, 1, 0] : ℚ) = (1 / 2 : ℚ) + (-89 / 16 : ℚ) * (2 : ℚ) ^ m + (-3 / 2 : ℚ) * (m : ℚ) ^ 1 * (2 : ℚ) ^ m + (3 / 16 : ℚ) * (m : ℚ) ^ 2 * (2 : ℚ) ^ m + (425 / 54 : ℚ) * (3 : ℚ) ^ m ∧
    (H m ![1, 1, 1] : ℚ) = (-1 / 2 : ℚ) + (-4 : ℚ) * (2 : ℚ) ^ m + (85 / 18 : ℚ) * (3 : ℚ) ^ m ∧
    (H m ![1, 1, 2] : ℚ) = (-2 : ℚ) + (2 : ℚ) * (2 : ℚ) ^ m ∧
    (H m ![1, 2, 0] : ℚ) = (-3 / 2 : ℚ) * (m : ℚ) ^ 1 + (-1 / 2 : ℚ) * (m : ℚ) ^ 2 + (9 / 4 : ℚ) * (2 : ℚ) ^ m + (3 / 2 : ℚ) * (m : ℚ) ^ 1 * (2 : ℚ) ^ m ∧
    (H m ![1, 2, 1] : ℚ) = (-1 : ℚ) + (-1 : ℚ) * (m : ℚ) ^ 1 + (5 / 4 : ℚ) * (2 : ℚ) ^ m + (3 / 2 : ℚ) * (m : ℚ) ^ 1 * (2 : ℚ) ^ m ∧
    (H m ![1, 2, 2] : ℚ) = (-2 : ℚ) + (2 : ℚ) * (2 : ℚ) ^ m ∧
    (H m ![2, 0, 0] : ℚ) = (5 / 2 : ℚ) + (-1 / 2 : ℚ) * (m : ℚ) ^ 1 + (-1 / 2 : ℚ) * (m : ℚ) ^ 2 + (-105 / 16 : ℚ) * (2 : ℚ) ^ m + (-5 / 4 : ℚ) * (m : ℚ) ^ 1 * (2 : ℚ) ^ m + (3 / 16 : ℚ) * (m : ℚ) ^ 2 * (2 : ℚ) ^ m + (425 / 54 : ℚ) * (3 : ℚ) ^ m ∧
    (H m ![2, 0, 1] : ℚ) = (-1 : ℚ) * (m : ℚ) ^ 1 + (7 / 4 : ℚ) * (2 : ℚ) ^ m + (1 / 2 : ℚ) * (m : ℚ) ^ 1 * (2 : ℚ) ^ m ∧
    (H m ![2, 0, 2] : ℚ) = (1 : ℚ) ∧
    (H m ![2, 1, 0] : ℚ) = (-13 / 4 : ℚ) + (1 : ℚ) * (m : ℚ) ^ 1 + (-1 / 2 : ℚ) * (m : ℚ) ^ 2 + (-49 / 8 : ℚ) * (2 : ℚ) ^ m + (-11 / 4 : ℚ) * (m : ℚ) ^ 1 * (2 : ℚ) ^ m + (3 / 8 : ℚ) * (m : ℚ) ^ 2 * (2 : ℚ) ^ m + (935 / 108 : ℚ) * (3 : ℚ) ^ m ∧
    (H m ![2, 1, 1] : ℚ) = (-83 / 16 : ℚ) * (2 : ℚ) ^ m + (-3 / 2 : ℚ) * (m : ℚ) ^ 1 * (2 : ℚ) ^ m + (3 / 16 : ℚ) * (m : ℚ) ^ 2 * (2 : ℚ) ^ m + (170 / 27 : ℚ) * (3 : ℚ) ^ m ∧
    (H m ![2, 1, 2] : ℚ) = (3 / 4 : ℚ) * (2 : ℚ) ^ m + (1 / 2 : ℚ) * (m : ℚ) ^ 1 * (2 : ℚ) ^ m ∧
    (H m ![2, 2, 0] : ℚ) = (3 / 2 : ℚ) + (1 : ℚ) * (m : ℚ) ^ 1 + (-125 / 16 : ℚ) * (2 : ℚ) ^ m + (-3 : ℚ) * (m : ℚ) ^ 1 * (2 : ℚ) ^ m + (3 / 16 : ℚ) * (m : ℚ) ^ 2 * (2 : ℚ) ^ m + (425 / 54 : ℚ) * (3 : ℚ) ^ m ∧
    (H m ![2, 2, 1] : ℚ) = (1 : ℚ) + (-87 / 16 : ℚ) * (2 : ℚ) ^ m + (-9 / 4 : ℚ) * (m : ℚ) ^ 1 * (2 : ℚ) ^ m + (3 / 16 : ℚ) * (m : ℚ) ^ 2 * (2 : ℚ) ^ m + (170 / 27 : ℚ) * (3 : ℚ) ^ m ∧
    (H m ![2, 2, 2] : ℚ) = (3 / 2 : ℚ) + (-6 : ℚ) * (2 : ℚ) ^ m + (85 / 18 : ℚ) * (3 : ℚ) ^ m := by
  induction m, hm using Nat.le_induction with
  | base =>
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26⟩ := B3
    rw [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26]
    norm_num
  | succ m hm ih =>
    obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26⟩ := ih
    obtain ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, g25, g26⟩ := Hs m
    rw [g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, g25, g26]
    push_cast
    rw [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> ring

theorem aS (n : ℕ) : a n = H n ![0, 0, 0] + H n ![0, 0, 1] + H n ![0, 0, 2] + H n ![0, 1, 0] + H n ![0, 1, 1] + H n ![0, 1, 2] + H n ![0, 2, 0] + H n ![0, 2, 1] + H n ![0, 2, 2] + H n ![1, 0, 0] + H n ![1, 0, 1] + H n ![1, 0, 2] + H n ![1, 1, 0] + H n ![1, 1, 1] + H n ![1, 1, 2] + H n ![1, 2, 0] + H n ![1, 2, 1] + H n ![1, 2, 2] + H n ![2, 0, 0] + H n ![2, 0, 1] + H n ![2, 0, 2] + H n ![2, 1, 0] + H n ![2, 1, 1] + H n ![2, 1, 2] + H n ![2, 2, 0] + H n ![2, 2, 1] + H n ![2, 2, 2] := by
  rw [card_eq, sum_cons, sumC]
  rfl

theorem aval (n : ℕ) (hn : 3 ≤ n) : (a n : ℚ) = (567 - 3807 * 2 ^ n + 7225 * 3 ^ n - 54 * (-1 + 15 * 2 ^ n) * (n : ℚ) + 54 * (-2 + 3 * 2 ^ n) * (n : ℚ) ^ 2) / 108 := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26⟩ := Hf n hn
  rw [aS]
  push_cast
  rw [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26]
  ring

theorem a0 : (a 0 : ℚ) = 27 := by
  rw [aS]; simp only [H0]; norm_num

theorem a1 : (a 1 : ℚ) = 127 := by
  obtain ⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26⟩ := B1
  rw [aS]; simp only [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26]; norm_num

theorem a2 : (a 2 : ℚ) = 431 := by
  obtain ⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26⟩ := B2
  rw [aS]; simp only [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26]; norm_num

end P250892

open P250892 in
theorem OMA.solution : type_of% @OMA.S_oeis_a250892.main := by
  refine ⟨?_, ?_, ?_⟩
  · intro n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 10 := ⟨n - 10, by omega⟩
    rw [show k + 10 - 1 = k + 9 by omega, show k + 10 - 2 = k + 8 by omega, show k + 10 - 3 = k + 7 by omega, show k + 10 - 4 = k + 6 by omega, show k + 10 - 5 = k + 5 by omega, show k + 10 - 6 = k + 4 by omega, show k + 10 - 7 = k + 3 by omega]
    apply Int.cast_injective (α := ℚ)
    push_cast
    simp only [aval _ (show 3 ≤ k + 10 by omega), aval _ (show 3 ≤ k + 9 by omega), aval _ (show 3 ≤ k + 8 by omega), aval _ (show 3 ≤ k + 7 by omega), aval _ (show 3 ≤ k + 6 by omega), aval _ (show 3 ≤ k + 5 by omega), aval _ (show 3 ≤ k + 4 by omega), aval _ (show 3 ≤ k + 3 by omega)]
    push_cast
    ring
  · have hm : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * ((1 - PowerSeries.X) ^ 3 * (1 - 2 * PowerSeries.X) ^ 3 * (1 - 3 * PowerSeries.X)) = PowerSeries.X * (127 - 1093 * PowerSeries.X + 3898 * PowerSeries.X ^ 2 - 7364 * PowerSeries.X ^ 3 + 7674 * PowerSeries.X ^ 4 - 3984 * PowerSeries.X ^ 5 + 498 * PowerSeries.X ^ 6 + 328 * PowerSeries.X ^ 7 - 88 * PowerSeries.X ^ 8) := by
      have hq : ∀ F : PowerSeries ℚ, F * ((1 - PowerSeries.X) ^ 3 * (1 - 2 * PowerSeries.X) ^ 3 * (1 - 3 * PowerSeries.X)) = F - C (12 : ℚ) * (F * X ^ 1) + C (60 : ℚ) * (F * X ^ 2) - C (162 : ℚ) * (F * X ^ 3) + C (255 : ℚ) * (F * X ^ 4) - C (234 : ℚ) * (F * X ^ 5) + C (116 : ℚ) * (F * X ^ 6) - C (24 : ℚ) * (F * X ^ 7) := by
        intro F; simp only [map_ofNat, map_one, pow_one, map_neg]; ring
      have hr : (PowerSeries.X * (127 - 1093 * PowerSeries.X + 3898 * PowerSeries.X ^ 2 - 7364 * PowerSeries.X ^ 3 + 7674 * PowerSeries.X ^ 4 - 3984 * PowerSeries.X ^ 5 + 498 * PowerSeries.X ^ 6 + 328 * PowerSeries.X ^ 7 - 88 * PowerSeries.X ^ 8) : PowerSeries ℚ) = C (127 : ℚ) * X ^ 1 - C (1093 : ℚ) * X ^ 2 + C (3898 : ℚ) * X ^ 3 - C (7364 : ℚ) * X ^ 4 + C (7674 : ℚ) * X ^ 5 - C (3984 : ℚ) * X ^ 6 + C (498 : ℚ) * X ^ 7 + C (328 : ℚ) * X ^ 8 - C (88 : ℚ) * X ^ 9 := by
        simp only [map_ofNat, map_one, pow_one, map_neg]; ring
      rw [hq, hr]
      ext n
      simp only [map_add, map_sub, map_neg, coeff_mul_X_pow', coeff_C_mul, coeff_mk, coeff_C, coeff_X_pow, coeff_one]
      by_cases hn : n < 10
      · interval_cases n <;> simp [a0, a1, a2, aval] <;> norm_num
      · obtain ⟨m, rfl⟩ : ∃ m, n = m + 10 := ⟨n - 10, by omega⟩
        simp only [show m + 10 - 1 = m + 9 by omega, show m + 10 - 2 = m + 8 by omega, show m + 10 - 3 = m + 7 by omega, show m + 10 - 4 = m + 6 by omega, show m + 10 - 5 = m + 5 by omega, show m + 10 - 6 = m + 4 by omega, show m + 10 - 7 = m + 3 by omega, show 1 ≤ m + 10 by omega, show 2 ≤ m + 10 by omega, show 3 ≤ m + 10 by omega, show 4 ≤ m + 10 by omega, show 5 ≤ m + 10 by omega, show 6 ≤ m + 10 by omega, show 7 ≤ m + 10 by omega, show m + 10 ≠ 0 by omega, show m + 10 ≠ 1 by omega, show m + 10 ≠ 2 by omega, show m + 10 ≠ 3 by omega, show m + 10 ≠ 4 by omega, show m + 10 ≠ 5 by omega, show m + 10 ≠ 6 by omega, show m + 10 ≠ 7 by omega, show m + 10 ≠ 8 by omega, show m + 10 ≠ 9 by omega, show m + 10 ≠ 0 by omega, show m + 9 ≠ 0 by omega, show m + 8 ≠ 0 by omega, show m + 7 ≠ 0 by omega, show m + 6 ≠ 0 by omega, show m + 5 ≠ 0 by omega, show m + 4 ≠ 0 by omega, show m + 3 ≠ 0 by omega, if_true, if_false, aval _ (show 3 ≤ m + 3 by omega), aval _ (show 3 ≤ m + 4 by omega), aval _ (show 3 ≤ m + 5 by omega), aval _ (show 3 ≤ m + 6 by omega), aval _ (show 3 ≤ m + 7 by omega), aval _ (show 3 ≤ m + 8 by omega), aval _ (show 3 ≤ m + 9 by omega), aval _ (show 3 ≤ m + 10 by omega)]
        push_cast
        ring
    have hd : constantCoeff ((1 - PowerSeries.X) ^ 3 * (1 - 2 * PowerSeries.X) ^ 3 * (1 - 3 * PowerSeries.X) : PowerSeries ℚ) ≠ 0 := by simp
    rw [G, ← hm, mul_assoc, PowerSeries.mul_inv_cancel _ hd, mul_one]
  · intro n hn
    rw [aval n (by omega)]
