import OMAStatements.S_oeis_a250878
import Mathlib

open OMA.S_oeis_a250878 PowerSeries

namespace P250878

abbrev Col := Fin 2 → Fin 4

def ok (c d : Col) : Prop := Blk (c 0) (d 0) (c 1) (d 1)

instance (c d : Col) : Decidable (ok c d) := by unfold ok Blk; infer_instance

def V (m : ℕ) (f : Fin (m + 1) → Col) : Prop := ∀ j : Fin m, ok (f j.castSucc) (f j.succ)

instance (m : ℕ) (f : Fin (m + 1) → Col) : Decidable (V m f) := by unfold V; infer_instance

def e (n : ℕ) : {x : Fin 2 → Fin (n + 1) → Fin 4 // Good n x} ≃ {y : Fin (n + 1) → Col // V n y} :=
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

theorem sumC (g : Col → ℕ) : ∑ s, g s = g ![0, 0] + g ![0, 1] + g ![0, 2] + g ![0, 3] + g ![1, 0] + g ![1, 1] + g ![1, 2] + g ![1, 3] + g ![2, 0] + g ![2, 1] + g ![2, 2] + g ![2, 3] + g ![3, 0] + g ![3, 1] + g ![3, 2] + g ![3, 3] := by
  have e : ∀ a b : Fin 4, (piFinTwoEquiv fun _ => Fin 4).symm (a, b) = ![a, b] := by
    intro a b; funext i; fin_cases i <;> rfl
  rw [← (piFinTwoEquiv fun _ => Fin 4).symm.sum_comp, Fintype.sum_prod_type]
  simp only [Fin.sum_univ_four, e]
  ring

theorem Hs (m : ℕ) :
    H (m + 1) ![0, 0] = H m ![0, 0] + H m ![0, 1] + H m ![0, 2] + H m ![0, 3] + H m ![1, 1] + H m ![1, 2] + H m ![1, 3] + H m ![2, 2] + H m ![2, 3] + H m ![3, 3] ∧
    H (m + 1) ![0, 1] = H m ![0, 1] + H m ![0, 2] + H m ![0, 3] + H m ![1, 2] + H m ![1, 3] + H m ![2, 3] ∧
    H (m + 1) ![0, 2] = H m ![0, 2] + H m ![0, 3] + H m ![1, 3] ∧
    H (m + 1) ![0, 3] = H m ![0, 3] ∧
    H (m + 1) ![1, 0] = H m ![0, 1] + H m ![0, 2] + H m ![0, 3] + H m ![1, 0] + H m ![1, 1] + H m ![1, 2] + H m ![1, 3] + H m ![2, 1] + H m ![2, 2] + H m ![2, 3] + H m ![3, 2] + H m ![3, 3] ∧
    H (m + 1) ![1, 1] = H m ![0, 2] + H m ![0, 3] + H m ![1, 1] + H m ![1, 2] + H m ![1, 3] + H m ![2, 2] + H m ![2, 3] + H m ![3, 3] ∧
    H (m + 1) ![1, 2] = H m ![0, 3] + H m ![1, 2] + H m ![1, 3] + H m ![2, 3] ∧
    H (m + 1) ![1, 3] = H m ![1, 3] ∧
    H (m + 1) ![2, 0] = H m ![0, 2] + H m ![0, 3] + H m ![1, 1] + H m ![1, 2] + H m ![1, 3] + H m ![2, 0] + H m ![2, 1] + H m ![2, 2] + H m ![2, 3] + H m ![3, 1] + H m ![3, 2] + H m ![3, 3] ∧
    H (m + 1) ![2, 1] = H m ![0, 3] + H m ![1, 2] + H m ![1, 3] + H m ![2, 1] + H m ![2, 2] + H m ![2, 3] + H m ![3, 2] + H m ![3, 3] ∧
    H (m + 1) ![2, 2] = H m ![1, 3] + H m ![2, 2] + H m ![2, 3] + H m ![3, 3] ∧
    H (m + 1) ![2, 3] = H m ![2, 3] ∧
    H (m + 1) ![3, 0] = H m ![0, 3] + H m ![1, 2] + H m ![1, 3] + H m ![2, 1] + H m ![2, 2] + H m ![2, 3] + H m ![3, 0] + H m ![3, 1] + H m ![3, 2] + H m ![3, 3] ∧
    H (m + 1) ![3, 1] = H m ![1, 3] + H m ![2, 2] + H m ![2, 3] + H m ![3, 1] + H m ![3, 2] + H m ![3, 3] ∧
    H (m + 1) ![3, 2] = H m ![2, 3] + H m ![3, 2] + H m ![3, 3] ∧
    H (m + 1) ![3, 3] = H m ![3, 3] := by
  have k0 : ok ![0, 0] ![0, 0] := by decide
  have k1 : ok ![0, 0] ![0, 1] := by decide
  have k2 : ok ![0, 0] ![0, 2] := by decide
  have k3 : ok ![0, 0] ![0, 3] := by decide
  have k4 : ¬ ok ![0, 0] ![1, 0] := by decide
  have k5 : ok ![0, 0] ![1, 1] := by decide
  have k6 : ok ![0, 0] ![1, 2] := by decide
  have k7 : ok ![0, 0] ![1, 3] := by decide
  have k8 : ¬ ok ![0, 0] ![2, 0] := by decide
  have k9 : ¬ ok ![0, 0] ![2, 1] := by decide
  have k10 : ok ![0, 0] ![2, 2] := by decide
  have k11 : ok ![0, 0] ![2, 3] := by decide
  have k12 : ¬ ok ![0, 0] ![3, 0] := by decide
  have k13 : ¬ ok ![0, 0] ![3, 1] := by decide
  have k14 : ¬ ok ![0, 0] ![3, 2] := by decide
  have k15 : ok ![0, 0] ![3, 3] := by decide
  have k16 : ¬ ok ![0, 1] ![0, 0] := by decide
  have k17 : ok ![0, 1] ![0, 1] := by decide
  have k18 : ok ![0, 1] ![0, 2] := by decide
  have k19 : ok ![0, 1] ![0, 3] := by decide
  have k20 : ¬ ok ![0, 1] ![1, 0] := by decide
  have k21 : ¬ ok ![0, 1] ![1, 1] := by decide
  have k22 : ok ![0, 1] ![1, 2] := by decide
  have k23 : ok ![0, 1] ![1, 3] := by decide
  have k24 : ¬ ok ![0, 1] ![2, 0] := by decide
  have k25 : ¬ ok ![0, 1] ![2, 1] := by decide
  have k26 : ¬ ok ![0, 1] ![2, 2] := by decide
  have k27 : ok ![0, 1] ![2, 3] := by decide
  have k28 : ¬ ok ![0, 1] ![3, 0] := by decide
  have k29 : ¬ ok ![0, 1] ![3, 1] := by decide
  have k30 : ¬ ok ![0, 1] ![3, 2] := by decide
  have k31 : ¬ ok ![0, 1] ![3, 3] := by decide
  have k32 : ¬ ok ![0, 2] ![0, 0] := by decide
  have k33 : ¬ ok ![0, 2] ![0, 1] := by decide
  have k34 : ok ![0, 2] ![0, 2] := by decide
  have k35 : ok ![0, 2] ![0, 3] := by decide
  have k36 : ¬ ok ![0, 2] ![1, 0] := by decide
  have k37 : ¬ ok ![0, 2] ![1, 1] := by decide
  have k38 : ¬ ok ![0, 2] ![1, 2] := by decide
  have k39 : ok ![0, 2] ![1, 3] := by decide
  have k40 : ¬ ok ![0, 2] ![2, 0] := by decide
  have k41 : ¬ ok ![0, 2] ![2, 1] := by decide
  have k42 : ¬ ok ![0, 2] ![2, 2] := by decide
  have k43 : ¬ ok ![0, 2] ![2, 3] := by decide
  have k44 : ¬ ok ![0, 2] ![3, 0] := by decide
  have k45 : ¬ ok ![0, 2] ![3, 1] := by decide
  have k46 : ¬ ok ![0, 2] ![3, 2] := by decide
  have k47 : ¬ ok ![0, 2] ![3, 3] := by decide
  have k48 : ¬ ok ![0, 3] ![0, 0] := by decide
  have k49 : ¬ ok ![0, 3] ![0, 1] := by decide
  have k50 : ¬ ok ![0, 3] ![0, 2] := by decide
  have k51 : ok ![0, 3] ![0, 3] := by decide
  have k52 : ¬ ok ![0, 3] ![1, 0] := by decide
  have k53 : ¬ ok ![0, 3] ![1, 1] := by decide
  have k54 : ¬ ok ![0, 3] ![1, 2] := by decide
  have k55 : ¬ ok ![0, 3] ![1, 3] := by decide
  have k56 : ¬ ok ![0, 3] ![2, 0] := by decide
  have k57 : ¬ ok ![0, 3] ![2, 1] := by decide
  have k58 : ¬ ok ![0, 3] ![2, 2] := by decide
  have k59 : ¬ ok ![0, 3] ![2, 3] := by decide
  have k60 : ¬ ok ![0, 3] ![3, 0] := by decide
  have k61 : ¬ ok ![0, 3] ![3, 1] := by decide
  have k62 : ¬ ok ![0, 3] ![3, 2] := by decide
  have k63 : ¬ ok ![0, 3] ![3, 3] := by decide
  have k64 : ¬ ok ![1, 0] ![0, 0] := by decide
  have k65 : ok ![1, 0] ![0, 1] := by decide
  have k66 : ok ![1, 0] ![0, 2] := by decide
  have k67 : ok ![1, 0] ![0, 3] := by decide
  have k68 : ok ![1, 0] ![1, 0] := by decide
  have k69 : ok ![1, 0] ![1, 1] := by decide
  have k70 : ok ![1, 0] ![1, 2] := by decide
  have k71 : ok ![1, 0] ![1, 3] := by decide
  have k72 : ¬ ok ![1, 0] ![2, 0] := by decide
  have k73 : ok ![1, 0] ![2, 1] := by decide
  have k74 : ok ![1, 0] ![2, 2] := by decide
  have k75 : ok ![1, 0] ![2, 3] := by decide
  have k76 : ¬ ok ![1, 0] ![3, 0] := by decide
  have k77 : ¬ ok ![1, 0] ![3, 1] := by decide
  have k78 : ok ![1, 0] ![3, 2] := by decide
  have k79 : ok ![1, 0] ![3, 3] := by decide
  have k80 : ¬ ok ![1, 1] ![0, 0] := by decide
  have k81 : ¬ ok ![1, 1] ![0, 1] := by decide
  have k82 : ok ![1, 1] ![0, 2] := by decide
  have k83 : ok ![1, 1] ![0, 3] := by decide
  have k84 : ¬ ok ![1, 1] ![1, 0] := by decide
  have k85 : ok ![1, 1] ![1, 1] := by decide
  have k86 : ok ![1, 1] ![1, 2] := by decide
  have k87 : ok ![1, 1] ![1, 3] := by decide
  have k88 : ¬ ok ![1, 1] ![2, 0] := by decide
  have k89 : ¬ ok ![1, 1] ![2, 1] := by decide
  have k90 : ok ![1, 1] ![2, 2] := by decide
  have k91 : ok ![1, 1] ![2, 3] := by decide
  have k92 : ¬ ok ![1, 1] ![3, 0] := by decide
  have k93 : ¬ ok ![1, 1] ![3, 1] := by decide
  have k94 : ¬ ok ![1, 1] ![3, 2] := by decide
  have k95 : ok ![1, 1] ![3, 3] := by decide
  have k96 : ¬ ok ![1, 2] ![0, 0] := by decide
  have k97 : ¬ ok ![1, 2] ![0, 1] := by decide
  have k98 : ¬ ok ![1, 2] ![0, 2] := by decide
  have k99 : ok ![1, 2] ![0, 3] := by decide
  have k100 : ¬ ok ![1, 2] ![1, 0] := by decide
  have k101 : ¬ ok ![1, 2] ![1, 1] := by decide
  have k102 : ok ![1, 2] ![1, 2] := by decide
  have k103 : ok ![1, 2] ![1, 3] := by decide
  have k104 : ¬ ok ![1, 2] ![2, 0] := by decide
  have k105 : ¬ ok ![1, 2] ![2, 1] := by decide
  have k106 : ¬ ok ![1, 2] ![2, 2] := by decide
  have k107 : ok ![1, 2] ![2, 3] := by decide
  have k108 : ¬ ok ![1, 2] ![3, 0] := by decide
  have k109 : ¬ ok ![1, 2] ![3, 1] := by decide
  have k110 : ¬ ok ![1, 2] ![3, 2] := by decide
  have k111 : ¬ ok ![1, 2] ![3, 3] := by decide
  have k112 : ¬ ok ![1, 3] ![0, 0] := by decide
  have k113 : ¬ ok ![1, 3] ![0, 1] := by decide
  have k114 : ¬ ok ![1, 3] ![0, 2] := by decide
  have k115 : ¬ ok ![1, 3] ![0, 3] := by decide
  have k116 : ¬ ok ![1, 3] ![1, 0] := by decide
  have k117 : ¬ ok ![1, 3] ![1, 1] := by decide
  have k118 : ¬ ok ![1, 3] ![1, 2] := by decide
  have k119 : ok ![1, 3] ![1, 3] := by decide
  have k120 : ¬ ok ![1, 3] ![2, 0] := by decide
  have k121 : ¬ ok ![1, 3] ![2, 1] := by decide
  have k122 : ¬ ok ![1, 3] ![2, 2] := by decide
  have k123 : ¬ ok ![1, 3] ![2, 3] := by decide
  have k124 : ¬ ok ![1, 3] ![3, 0] := by decide
  have k125 : ¬ ok ![1, 3] ![3, 1] := by decide
  have k126 : ¬ ok ![1, 3] ![3, 2] := by decide
  have k127 : ¬ ok ![1, 3] ![3, 3] := by decide
  have k128 : ¬ ok ![2, 0] ![0, 0] := by decide
  have k129 : ¬ ok ![2, 0] ![0, 1] := by decide
  have k130 : ok ![2, 0] ![0, 2] := by decide
  have k131 : ok ![2, 0] ![0, 3] := by decide
  have k132 : ¬ ok ![2, 0] ![1, 0] := by decide
  have k133 : ok ![2, 0] ![1, 1] := by decide
  have k134 : ok ![2, 0] ![1, 2] := by decide
  have k135 : ok ![2, 0] ![1, 3] := by decide
  have k136 : ok ![2, 0] ![2, 0] := by decide
  have k137 : ok ![2, 0] ![2, 1] := by decide
  have k138 : ok ![2, 0] ![2, 2] := by decide
  have k139 : ok ![2, 0] ![2, 3] := by decide
  have k140 : ¬ ok ![2, 0] ![3, 0] := by decide
  have k141 : ok ![2, 0] ![3, 1] := by decide
  have k142 : ok ![2, 0] ![3, 2] := by decide
  have k143 : ok ![2, 0] ![3, 3] := by decide
  have k144 : ¬ ok ![2, 1] ![0, 0] := by decide
  have k145 : ¬ ok ![2, 1] ![0, 1] := by decide
  have k146 : ¬ ok ![2, 1] ![0, 2] := by decide
  have k147 : ok ![2, 1] ![0, 3] := by decide
  have k148 : ¬ ok ![2, 1] ![1, 0] := by decide
  have k149 : ¬ ok ![2, 1] ![1, 1] := by decide
  have k150 : ok ![2, 1] ![1, 2] := by decide
  have k151 : ok ![2, 1] ![1, 3] := by decide
  have k152 : ¬ ok ![2, 1] ![2, 0] := by decide
  have k153 : ok ![2, 1] ![2, 1] := by decide
  have k154 : ok ![2, 1] ![2, 2] := by decide
  have k155 : ok ![2, 1] ![2, 3] := by decide
  have k156 : ¬ ok ![2, 1] ![3, 0] := by decide
  have k157 : ¬ ok ![2, 1] ![3, 1] := by decide
  have k158 : ok ![2, 1] ![3, 2] := by decide
  have k159 : ok ![2, 1] ![3, 3] := by decide
  have k160 : ¬ ok ![2, 2] ![0, 0] := by decide
  have k161 : ¬ ok ![2, 2] ![0, 1] := by decide
  have k162 : ¬ ok ![2, 2] ![0, 2] := by decide
  have k163 : ¬ ok ![2, 2] ![0, 3] := by decide
  have k164 : ¬ ok ![2, 2] ![1, 0] := by decide
  have k165 : ¬ ok ![2, 2] ![1, 1] := by decide
  have k166 : ¬ ok ![2, 2] ![1, 2] := by decide
  have k167 : ok ![2, 2] ![1, 3] := by decide
  have k168 : ¬ ok ![2, 2] ![2, 0] := by decide
  have k169 : ¬ ok ![2, 2] ![2, 1] := by decide
  have k170 : ok ![2, 2] ![2, 2] := by decide
  have k171 : ok ![2, 2] ![2, 3] := by decide
  have k172 : ¬ ok ![2, 2] ![3, 0] := by decide
  have k173 : ¬ ok ![2, 2] ![3, 1] := by decide
  have k174 : ¬ ok ![2, 2] ![3, 2] := by decide
  have k175 : ok ![2, 2] ![3, 3] := by decide
  have k176 : ¬ ok ![2, 3] ![0, 0] := by decide
  have k177 : ¬ ok ![2, 3] ![0, 1] := by decide
  have k178 : ¬ ok ![2, 3] ![0, 2] := by decide
  have k179 : ¬ ok ![2, 3] ![0, 3] := by decide
  have k180 : ¬ ok ![2, 3] ![1, 0] := by decide
  have k181 : ¬ ok ![2, 3] ![1, 1] := by decide
  have k182 : ¬ ok ![2, 3] ![1, 2] := by decide
  have k183 : ¬ ok ![2, 3] ![1, 3] := by decide
  have k184 : ¬ ok ![2, 3] ![2, 0] := by decide
  have k185 : ¬ ok ![2, 3] ![2, 1] := by decide
  have k186 : ¬ ok ![2, 3] ![2, 2] := by decide
  have k187 : ok ![2, 3] ![2, 3] := by decide
  have k188 : ¬ ok ![2, 3] ![3, 0] := by decide
  have k189 : ¬ ok ![2, 3] ![3, 1] := by decide
  have k190 : ¬ ok ![2, 3] ![3, 2] := by decide
  have k191 : ¬ ok ![2, 3] ![3, 3] := by decide
  have k192 : ¬ ok ![3, 0] ![0, 0] := by decide
  have k193 : ¬ ok ![3, 0] ![0, 1] := by decide
  have k194 : ¬ ok ![3, 0] ![0, 2] := by decide
  have k195 : ok ![3, 0] ![0, 3] := by decide
  have k196 : ¬ ok ![3, 0] ![1, 0] := by decide
  have k197 : ¬ ok ![3, 0] ![1, 1] := by decide
  have k198 : ok ![3, 0] ![1, 2] := by decide
  have k199 : ok ![3, 0] ![1, 3] := by decide
  have k200 : ¬ ok ![3, 0] ![2, 0] := by decide
  have k201 : ok ![3, 0] ![2, 1] := by decide
  have k202 : ok ![3, 0] ![2, 2] := by decide
  have k203 : ok ![3, 0] ![2, 3] := by decide
  have k204 : ok ![3, 0] ![3, 0] := by decide
  have k205 : ok ![3, 0] ![3, 1] := by decide
  have k206 : ok ![3, 0] ![3, 2] := by decide
  have k207 : ok ![3, 0] ![3, 3] := by decide
  have k208 : ¬ ok ![3, 1] ![0, 0] := by decide
  have k209 : ¬ ok ![3, 1] ![0, 1] := by decide
  have k210 : ¬ ok ![3, 1] ![0, 2] := by decide
  have k211 : ¬ ok ![3, 1] ![0, 3] := by decide
  have k212 : ¬ ok ![3, 1] ![1, 0] := by decide
  have k213 : ¬ ok ![3, 1] ![1, 1] := by decide
  have k214 : ¬ ok ![3, 1] ![1, 2] := by decide
  have k215 : ok ![3, 1] ![1, 3] := by decide
  have k216 : ¬ ok ![3, 1] ![2, 0] := by decide
  have k217 : ¬ ok ![3, 1] ![2, 1] := by decide
  have k218 : ok ![3, 1] ![2, 2] := by decide
  have k219 : ok ![3, 1] ![2, 3] := by decide
  have k220 : ¬ ok ![3, 1] ![3, 0] := by decide
  have k221 : ok ![3, 1] ![3, 1] := by decide
  have k222 : ok ![3, 1] ![3, 2] := by decide
  have k223 : ok ![3, 1] ![3, 3] := by decide
  have k224 : ¬ ok ![3, 2] ![0, 0] := by decide
  have k225 : ¬ ok ![3, 2] ![0, 1] := by decide
  have k226 : ¬ ok ![3, 2] ![0, 2] := by decide
  have k227 : ¬ ok ![3, 2] ![0, 3] := by decide
  have k228 : ¬ ok ![3, 2] ![1, 0] := by decide
  have k229 : ¬ ok ![3, 2] ![1, 1] := by decide
  have k230 : ¬ ok ![3, 2] ![1, 2] := by decide
  have k231 : ¬ ok ![3, 2] ![1, 3] := by decide
  have k232 : ¬ ok ![3, 2] ![2, 0] := by decide
  have k233 : ¬ ok ![3, 2] ![2, 1] := by decide
  have k234 : ¬ ok ![3, 2] ![2, 2] := by decide
  have k235 : ok ![3, 2] ![2, 3] := by decide
  have k236 : ¬ ok ![3, 2] ![3, 0] := by decide
  have k237 : ¬ ok ![3, 2] ![3, 1] := by decide
  have k238 : ok ![3, 2] ![3, 2] := by decide
  have k239 : ok ![3, 2] ![3, 3] := by decide
  have k240 : ¬ ok ![3, 3] ![0, 0] := by decide
  have k241 : ¬ ok ![3, 3] ![0, 1] := by decide
  have k242 : ¬ ok ![3, 3] ![0, 2] := by decide
  have k243 : ¬ ok ![3, 3] ![0, 3] := by decide
  have k244 : ¬ ok ![3, 3] ![1, 0] := by decide
  have k245 : ¬ ok ![3, 3] ![1, 1] := by decide
  have k246 : ¬ ok ![3, 3] ![1, 2] := by decide
  have k247 : ¬ ok ![3, 3] ![1, 3] := by decide
  have k248 : ¬ ok ![3, 3] ![2, 0] := by decide
  have k249 : ¬ ok ![3, 3] ![2, 1] := by decide
  have k250 : ¬ ok ![3, 3] ![2, 2] := by decide
  have k251 : ¬ ok ![3, 3] ![2, 3] := by decide
  have k252 : ¬ ok ![3, 3] ![3, 0] := by decide
  have k253 : ¬ ok ![3, 3] ![3, 1] := by decide
  have k254 : ¬ ok ![3, 3] ![3, 2] := by decide
  have k255 : ok ![3, 3] ![3, 3] := by decide
  simp only [H_succ, sumC, k0, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, k12, k13, k14, k15, k16, k17, k18, k19, k20, k21, k22, k23, k24, k25, k26, k27, k28, k29, k30, k31, k32, k33, k34, k35, k36, k37, k38, k39, k40, k41, k42, k43, k44, k45, k46, k47, k48, k49, k50, k51, k52, k53, k54, k55, k56, k57, k58, k59, k60, k61, k62, k63, k64, k65, k66, k67, k68, k69, k70, k71, k72, k73, k74, k75, k76, k77, k78, k79, k80, k81, k82, k83, k84, k85, k86, k87, k88, k89, k90, k91, k92, k93, k94, k95, k96, k97, k98, k99, k100, k101, k102, k103, k104, k105, k106, k107, k108, k109, k110, k111, k112, k113, k114, k115, k116, k117, k118, k119, k120, k121, k122, k123, k124, k125, k126, k127, k128, k129, k130, k131, k132, k133, k134, k135, k136, k137, k138, k139, k140, k141, k142, k143, k144, k145, k146, k147, k148, k149, k150, k151, k152, k153, k154, k155, k156, k157, k158, k159, k160, k161, k162, k163, k164, k165, k166, k167, k168, k169, k170, k171, k172, k173, k174, k175, k176, k177, k178, k179, k180, k181, k182, k183, k184, k185, k186, k187, k188, k189, k190, k191, k192, k193, k194, k195, k196, k197, k198, k199, k200, k201, k202, k203, k204, k205, k206, k207, k208, k209, k210, k211, k212, k213, k214, k215, k216, k217, k218, k219, k220, k221, k222, k223, k224, k225, k226, k227, k228, k229, k230, k231, k232, k233, k234, k235, k236, k237, k238, k239, k240, k241, k242, k243, k244, k245, k246, k247, k248, k249, k250, k251, k252, k253, k254, k255, if_true, if_false, add_zero, zero_add]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> trivial

theorem Hf (m : ℕ) :
    (H m ![0, 0] : ℚ) = (1 : ℚ) + (10 / 3 : ℚ) * (m : ℚ) ^ 1 + (7 / 2 : ℚ) * (m : ℚ) ^ 2 + (13 / 6 : ℚ) * (m : ℚ) ^ 3 ∧
    (H m ![0, 1] : ℚ) = (1 : ℚ) + (5 / 2 : ℚ) * (m : ℚ) ^ 1 + (5 / 2 : ℚ) * (m : ℚ) ^ 2 ∧
    (H m ![0, 2] : ℚ) = (1 : ℚ) + (2 : ℚ) * (m : ℚ) ^ 1 ∧
    (H m ![0, 3] : ℚ) = (1 : ℚ) ∧
    (H m ![1, 0] : ℚ) = (1 : ℚ) + (7 / 2 : ℚ) * (m : ℚ) ^ 1 + (4 : ℚ) * (m : ℚ) ^ 2 + (7 / 2 : ℚ) * (m : ℚ) ^ 3 ∧
    (H m ![1, 1] : ℚ) = (1 : ℚ) + (3 : ℚ) * (m : ℚ) ^ 1 + (4 : ℚ) * (m : ℚ) ^ 2 ∧
    (H m ![1, 2] : ℚ) = (1 : ℚ) + (3 : ℚ) * (m : ℚ) ^ 1 ∧
    (H m ![1, 3] : ℚ) = (1 : ℚ) ∧
    (H m ![2, 0] : ℚ) = (1 : ℚ) + (7 / 2 : ℚ) * (m : ℚ) ^ 1 + (4 : ℚ) * (m : ℚ) ^ 2 + (7 / 2 : ℚ) * (m : ℚ) ^ 3 ∧
    (H m ![2, 1] : ℚ) = (1 : ℚ) + (3 : ℚ) * (m : ℚ) ^ 1 + (4 : ℚ) * (m : ℚ) ^ 2 ∧
    (H m ![2, 2] : ℚ) = (1 : ℚ) + (3 : ℚ) * (m : ℚ) ^ 1 ∧
    (H m ![2, 3] : ℚ) = (1 : ℚ) ∧
    (H m ![3, 0] : ℚ) = (1 : ℚ) + (10 / 3 : ℚ) * (m : ℚ) ^ 1 + (7 / 2 : ℚ) * (m : ℚ) ^ 2 + (13 / 6 : ℚ) * (m : ℚ) ^ 3 ∧
    (H m ![3, 1] : ℚ) = (1 : ℚ) + (5 / 2 : ℚ) * (m : ℚ) ^ 1 + (5 / 2 : ℚ) * (m : ℚ) ^ 2 ∧
    (H m ![3, 2] : ℚ) = (1 : ℚ) + (2 : ℚ) * (m : ℚ) ^ 1 ∧
    (H m ![3, 3] : ℚ) = (1 : ℚ) := by
  induction m with
  | zero => simp only [H0]; norm_num
  | succ m ih =>
    obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ := ih
    obtain ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15⟩ := Hs m
    rw [g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15]
    push_cast
    rw [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> ring

theorem aS (n : ℕ) : a n = H n ![0, 0] + H n ![0, 1] + H n ![0, 2] + H n ![0, 3] + H n ![1, 0] + H n ![1, 1] + H n ![1, 2] + H n ![1, 3] + H n ![2, 0] + H n ![2, 1] + H n ![2, 2] + H n ![2, 3] + H n ![3, 0] + H n ![3, 1] + H n ![3, 2] + H n ![3, 3] := by
  rw [card_eq, sum_cons, sumC]
  rfl

theorem aval (n : ℕ) : (a n : ℚ) = (34 * (n : ℚ) ^ 3 + 84 * (n : ℚ) ^ 2 + 104 * (n : ℚ) + 48) / 3 := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ := Hf n
  rw [aS]
  push_cast
  rw [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15]
  ring

end P250878

open P250878 in
theorem OMA.solution : type_of% @OMA.S_oeis_a250878.main := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h := aval 1
    norm_num at h
    exact_mod_cast h
  · have h := aval 2
    norm_num at h
    exact_mod_cast h
  · have h := aval 3
    norm_num at h
    exact_mod_cast h
  · have h := aval 4
    norm_num at h
    exact_mod_cast h
  · intro n _
    apply Int.cast_injective (α := ℚ)
    push_cast
    simp only [aval]
    push_cast
    ring
  · intro n _
    apply Int.cast_injective (α := ℚ)
    push_cast
    rw [aval]
    ring
