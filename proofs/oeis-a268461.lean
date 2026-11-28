import OMAStatements.S_oeis_a268461
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace A268461Proof

open OMA.S_oeis_a268461

open scoped Classical

abbrev Word (n : ℕ) := Fin 7 → Fin (n + 1)

private def tuple {α : Type*} (a b c d e f g : α) (i : Fin 7) : α :=
  match i.val with
  | 0 => a
  | 1 => b
  | 2 => c
  | 3 => d
  | 4 => e
  | 5 => f
  | _ => g

@[simp] private theorem cast0 : (0 : Fin 6).castSucc = (0 : Fin 7) := rfl
@[simp] private theorem cast1 : (1 : Fin 6).castSucc = (1 : Fin 7) := rfl
@[simp] private theorem cast2 : (2 : Fin 6).castSucc = (2 : Fin 7) := rfl
@[simp] private theorem cast3 : (3 : Fin 6).castSucc = (3 : Fin 7) := rfl
@[simp] private theorem succ0 : (0 : Fin 6).succ = (1 : Fin 7) := rfl
@[simp] private theorem succ1 : (1 : Fin 6).succ = (2 : Fin 7) := rfl
@[simp] private theorem succ2 : (2 : Fin 6).succ = (3 : Fin 7) := rfl
@[simp] private theorem succ3 : (3 : Fin 6).succ = (4 : Fin 7) := rfl


private def valid {n : ℕ} (w : Word n) :=
  ∀ i j : Fin 6, i < j → ¬ reversed w i j

@[simp] private theorem cast4 : (4 : Fin 6).castSucc = (4 : Fin 7) := rfl
@[simp] private theorem succ4 : (4 : Fin 6).succ = (5 : Fin 7) := rfl
@[simp] private theorem cast5 : (5 : Fin 6).castSucc = (5 : Fin 7) := rfl
@[simp] private theorem succ5 : (5 : Fin 6).succ = (6 : Fin 7) := rfl

private theorem valid_iff {n : ℕ} (w : Word n) :
    valid w ↔ ¬ (reversed w 0 1 ∨ reversed w 0 2 ∨ reversed w 0 3 ∨
      reversed w 0 4 ∨ reversed w 0 5 ∨ reversed w 1 2 ∨
      reversed w 1 3 ∨ reversed w 1 4 ∨ reversed w 1 5 ∨
      reversed w 2 3 ∨ reversed w 2 4 ∨ reversed w 2 5 ∨
      reversed w 3 4 ∨ reversed w 3 5 ∨ reversed w 4 5) := by
  constructor
  · intro hv h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact hv 0 1 (by decide) h
    · exact hv 0 2 (by decide) h
    · exact hv 0 3 (by decide) h
    · exact hv 0 4 (by decide) h
    · exact hv 0 5 (by decide) h
    · exact hv 1 2 (by decide) h
    · exact hv 1 3 (by decide) h
    · exact hv 1 4 (by decide) h
    · exact hv 1 5 (by decide) h
    · exact hv 2 3 (by decide) h
    · exact hv 2 4 (by decide) h
    · exact hv 2 5 (by decide) h
    · exact hv 3 4 (by decide) h
    · exact hv 3 5 (by decide) h
    · exact hv 4 5 (by decide) h
  · intro h i j hij hr
    fin_cases i <;> fin_cases j <;> try (norm_num [Fin.lt_def] at hij)
    all_goals exact h (by tauto)

private theorem overlap_control {n : ℕ} (w : Word n) :
    (reversed w 0 1 ∧ reversed w 0 3 → reversed w 2 3) ∧
    (reversed w 0 1 ∧ reversed w 0 3 ∧ reversed w 0 5 → reversed w 2 5) ∧
    (reversed w 0 1 ∧ reversed w 0 3 ∧ reversed w 4 5 → reversed w 2 5) ∧
    (reversed w 0 1 ∧ reversed w 0 5 ∧ reversed w 2 3 → reversed w 2 5) ∧
    (reversed w 0 1 ∧ reversed w 0 5 ∧ reversed w 2 3 → reversed w 4 5) ∧
    (reversed w 0 1 ∧ reversed w 0 5 ∧ reversed w 3 4 → reversed w 2 5) ∧
    (reversed w 0 1 ∧ reversed w 2 3 → reversed w 0 3) ∧
    (reversed w 0 1 ∧ reversed w 2 3 ∧ reversed w 4 5 → reversed w 0 5) ∧
    (reversed w 0 1 ∧ reversed w 2 4 → reversed w 0 4) ∧
    (reversed w 0 1 ∧ reversed w 2 5 → reversed w 0 5) ∧
    (reversed w 0 1 ∧ reversed w 2 5 ∧ reversed w 4 5 → reversed w 0 3) ∧
    (reversed w 0 2 ∧ reversed w 0 4 → reversed w 3 4) ∧
    (reversed w 0 2 ∧ reversed w 3 4 → reversed w 0 4) ∧
    (reversed w 0 2 ∧ reversed w 3 5 → reversed w 0 5) ∧
    (reversed w 0 3 ∧ reversed w 0 5 → reversed w 4 5) ∧
    (reversed w 0 3 ∧ reversed w 0 5 ∧ reversed w 2 3 → reversed w 2 5) ∧
    (reversed w 0 3 ∧ reversed w 1 5 → reversed w 1 2) ∧
    (reversed w 0 3 ∧ reversed w 2 3 → reversed w 0 1) ∧
    (reversed w 0 3 ∧ reversed w 2 5 → reversed w 0 1) ∧
    (reversed w 0 3 ∧ reversed w 2 5 → reversed w 0 5) ∧
    (reversed w 0 3 ∧ reversed w 2 5 → reversed w 2 3) ∧
    (reversed w 0 3 ∧ reversed w 2 5 → reversed w 4 5) ∧
    (reversed w 0 3 ∧ reversed w 4 5 → reversed w 0 5) ∧
    (reversed w 0 4 ∧ reversed w 2 4 → reversed w 0 1) ∧
    (reversed w 0 4 ∧ reversed w 2 5 → reversed w 3 4) ∧
    (reversed w 0 5 ∧ reversed w 1 2 ∧ reversed w 4 5 → reversed w 0 3) ∧
    (reversed w 0 5 ∧ reversed w 2 3 ∧ reversed w 2 5 → reversed w 0 3) ∧
    (reversed w 0 5 ∧ reversed w 2 3 ∧ reversed w 4 5 → reversed w 0 1) ∧
    (reversed w 0 5 ∧ reversed w 2 3 ∧ reversed w 4 5 → reversed w 0 3) ∧
    (reversed w 0 5 ∧ reversed w 2 5 → reversed w 0 1) ∧
    (reversed w 0 5 ∧ reversed w 2 5 ∧ reversed w 4 5 → reversed w 0 3) ∧
    (reversed w 1 2 ∧ reversed w 1 4 → reversed w 3 4) ∧
    (reversed w 1 2 ∧ reversed w 3 4 → reversed w 1 4) ∧
    (reversed w 1 2 ∧ reversed w 3 5 → reversed w 1 5) ∧
    (reversed w 1 3 ∧ reversed w 1 5 → reversed w 4 5) ∧
    (reversed w 1 3 ∧ reversed w 4 5 → reversed w 1 5) ∧
    (reversed w 1 4 ∧ reversed w 3 4 → reversed w 1 2) ∧
    (reversed w 1 5 ∧ reversed w 3 5 → reversed w 1 2) ∧
    (reversed w 2 3 ∧ reversed w 2 5 → reversed w 4 5) ∧
    (reversed w 2 3 ∧ reversed w 4 5 → reversed w 2 5) ∧
    (reversed w 2 5 ∧ reversed w 4 5 → reversed w 2 3) ∧
    ¬ (reversed w 0 1 ∧ reversed w 0 2) ∧
    ¬ (reversed w 0 1 ∧ reversed w 0 4 ∧ reversed w 2 3) ∧
    ¬ (reversed w 0 1 ∧ reversed w 0 4 ∧ reversed w 2 5) ∧
    ¬ (reversed w 0 1 ∧ reversed w 0 5 ∧ reversed w 2 4) ∧
    ¬ (reversed w 0 1 ∧ reversed w 1 2) ∧
    ¬ (reversed w 0 1 ∧ reversed w 1 3) ∧
    ¬ (reversed w 0 1 ∧ reversed w 1 4) ∧
    ¬ (reversed w 0 1 ∧ reversed w 1 5) ∧
    ¬ (reversed w 0 2 ∧ reversed w 0 3) ∧
    ¬ (reversed w 0 2 ∧ reversed w 0 5 ∧ reversed w 3 4) ∧
    ¬ (reversed w 0 2 ∧ reversed w 1 2) ∧
    ¬ (reversed w 0 2 ∧ reversed w 1 3) ∧
    ¬ (reversed w 0 2 ∧ reversed w 1 4) ∧
    ¬ (reversed w 0 2 ∧ reversed w 1 5) ∧
    ¬ (reversed w 0 2 ∧ reversed w 2 3) ∧
    ¬ (reversed w 0 2 ∧ reversed w 2 4) ∧
    ¬ (reversed w 0 2 ∧ reversed w 2 5) ∧
    ¬ (reversed w 0 3 ∧ reversed w 0 4) ∧
    ¬ (reversed w 0 3 ∧ reversed w 1 3) ∧
    ¬ (reversed w 0 3 ∧ reversed w 1 4) ∧
    ¬ (reversed w 0 3 ∧ reversed w 1 5 ∧ reversed w 2 3) ∧
    ¬ (reversed w 0 3 ∧ reversed w 1 5 ∧ reversed w 4 5) ∧
    ¬ (reversed w 0 3 ∧ reversed w 2 4) ∧
    ¬ (reversed w 0 3 ∧ reversed w 3 4) ∧
    ¬ (reversed w 0 3 ∧ reversed w 3 5) ∧
    ¬ (reversed w 0 4 ∧ reversed w 0 5) ∧
    ¬ (reversed w 0 4 ∧ reversed w 1 2 ∧ reversed w 3 4) ∧
    ¬ (reversed w 0 4 ∧ reversed w 1 4) ∧
    ¬ (reversed w 0 4 ∧ reversed w 1 5) ∧
    ¬ (reversed w 0 4 ∧ reversed w 2 3 ∧ reversed w 2 5) ∧
    ¬ (reversed w 0 4 ∧ reversed w 3 5) ∧
    ¬ (reversed w 0 4 ∧ reversed w 4 5) ∧
    ¬ (reversed w 0 5 ∧ reversed w 1 2 ∧ reversed w 3 5) ∧
    ¬ (reversed w 0 5 ∧ reversed w 1 3 ∧ reversed w 4 5) ∧
    ¬ (reversed w 0 5 ∧ reversed w 1 5) ∧
    ¬ (reversed w 1 2 ∧ reversed w 1 3) ∧
    ¬ (reversed w 1 2 ∧ reversed w 1 5 ∧ reversed w 3 4) ∧
    ¬ (reversed w 1 2 ∧ reversed w 2 3) ∧
    ¬ (reversed w 1 2 ∧ reversed w 2 4) ∧
    ¬ (reversed w 1 2 ∧ reversed w 2 5) ∧
    ¬ (reversed w 1 3 ∧ reversed w 1 4) ∧
    ¬ (reversed w 1 3 ∧ reversed w 2 3) ∧
    ¬ (reversed w 1 3 ∧ reversed w 2 4) ∧
    ¬ (reversed w 1 3 ∧ reversed w 2 5) ∧
    ¬ (reversed w 1 3 ∧ reversed w 3 4) ∧
    ¬ (reversed w 1 3 ∧ reversed w 3 5) ∧
    ¬ (reversed w 1 4 ∧ reversed w 1 5) ∧
    ¬ (reversed w 1 4 ∧ reversed w 2 4) ∧
    ¬ (reversed w 1 4 ∧ reversed w 2 5) ∧
    ¬ (reversed w 1 4 ∧ reversed w 3 5) ∧
    ¬ (reversed w 1 4 ∧ reversed w 4 5) ∧
    ¬ (reversed w 1 5 ∧ reversed w 2 3 ∧ reversed w 4 5) ∧
    ¬ (reversed w 1 5 ∧ reversed w 2 5) ∧
    ¬ (reversed w 2 3 ∧ reversed w 2 4) ∧
    ¬ (reversed w 2 3 ∧ reversed w 3 4) ∧
    ¬ (reversed w 2 3 ∧ reversed w 3 5) ∧
    ¬ (reversed w 2 4 ∧ reversed w 2 5) ∧
    ¬ (reversed w 2 4 ∧ reversed w 3 4) ∧
    ¬ (reversed w 2 4 ∧ reversed w 3 5) ∧
    ¬ (reversed w 2 4 ∧ reversed w 4 5) ∧
    ¬ (reversed w 2 5 ∧ reversed w 3 5) ∧
    ¬ (reversed w 3 4 ∧ reversed w 3 5) ∧
    ¬ (reversed w 3 4 ∧ reversed w 4 5) ∧
    ¬ (reversed w 3 5 ∧ reversed w 4 5) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [reversed, Fin.ext_iff] <;> omega

private noncomputable def ind (p : Prop) : ℤ := if p then 1 else 0

set_option maxHeartbeats 9000000 in
private theorem indicators {n : ℕ} (w : Word n) :
    ind (valid w) = 1 -
      (ind (reversed w 0 1) + ind (reversed w 0 2) + ind (reversed w 0 3) +
       ind (reversed w 0 4) + ind (reversed w 0 5) + ind (reversed w 1 2) +
       ind (reversed w 1 3) + ind (reversed w 1 4) + ind (reversed w 1 5) +
       ind (reversed w 2 3) + ind (reversed w 2 4) + ind (reversed w 2 5) +
       ind (reversed w 3 4) + ind (reversed w 3 5) + ind (reversed w 4 5)) +
      ind (reversed w 0 1 ∧ reversed w 0 4) +
      ind (reversed w 0 1 ∧ reversed w 0 5) +
      ind (reversed w 0 1 ∧ reversed w 3 4) +
      ind (reversed w 0 1 ∧ reversed w 3 5) +
      ind (reversed w 0 1 ∧ reversed w 4 5) +
      ind (reversed w 0 2 ∧ reversed w 0 5) +
      ind (reversed w 0 2 ∧ reversed w 4 5) +
      ind (reversed w 0 3 ∧ reversed w 1 2) +
      ind (reversed w 0 4 ∧ reversed w 1 2) +
      ind (reversed w 0 4 ∧ reversed w 1 3) +
      ind (reversed w 0 4 ∧ reversed w 2 3) +
      ind (reversed w 0 4 ∧ reversed w 3 4) +
      ind (reversed w 0 5 ∧ reversed w 1 2) +
      ind (reversed w 0 5 ∧ reversed w 1 3) +
      ind (reversed w 0 5 ∧ reversed w 1 4) +
      ind (reversed w 0 5 ∧ reversed w 2 3) +
      ind (reversed w 0 5 ∧ reversed w 2 4) +
      ind (reversed w 0 5 ∧ reversed w 3 4) +
      ind (reversed w 0 5 ∧ reversed w 3 5) +
      ind (reversed w 0 5 ∧ reversed w 4 5) +
      ind (reversed w 1 2 ∧ reversed w 1 5) +
      ind (reversed w 1 2 ∧ reversed w 4 5) +
      ind (reversed w 1 4 ∧ reversed w 2 3) +
      ind (reversed w 1 5 ∧ reversed w 2 3) +
      ind (reversed w 1 5 ∧ reversed w 2 4) +
      ind (reversed w 1 5 ∧ reversed w 3 4) +
      ind (reversed w 1 5 ∧ reversed w 4 5) +
      ind (reversed w 2 5 ∧ reversed w 3 4) +
      2 * ind (reversed w 0 1 ∧ reversed w 0 3 ∧ reversed w 2 3) +
      ind (reversed w 0 1 ∧ reversed w 0 4 ∧ reversed w 2 4) -
      ind (reversed w 0 1 ∧ reversed w 0 4 ∧ reversed w 3 4) +
      ind (reversed w 0 1 ∧ reversed w 0 5 ∧ reversed w 2 5) -
      ind (reversed w 0 1 ∧ reversed w 0 5 ∧ reversed w 3 5) -
      ind (reversed w 0 1 ∧ reversed w 0 5 ∧ reversed w 4 5) +
      ind (reversed w 0 2 ∧ reversed w 0 4 ∧ reversed w 3 4) -
      ind (reversed w 0 2 ∧ reversed w 0 5 ∧ reversed w 4 5) +
      ind (reversed w 0 3 ∧ reversed w 0 5 ∧ reversed w 4 5) -
      ind (reversed w 0 5 ∧ reversed w 1 4 ∧ reversed w 2 3) +
      2 * ind (reversed w 1 2 ∧ reversed w 1 4 ∧ reversed w 3 4) +
      ind (reversed w 1 2 ∧ reversed w 1 5 ∧ reversed w 3 5) -
      ind (reversed w 1 2 ∧ reversed w 1 5 ∧ reversed w 4 5) +
      ind (reversed w 1 3 ∧ reversed w 1 5 ∧ reversed w 4 5) +
      2 * ind (reversed w 2 3 ∧ reversed w 2 5 ∧ reversed w 4 5) -
      2 * ind (reversed w 0 1 ∧ reversed w 0 5 ∧ reversed w 2 5 ∧ reversed w 3 4) -
      2 * ind (reversed w 0 3 ∧ reversed w 0 5 ∧ reversed w 1 2 ∧ reversed w 4 5) -
      2 * ind (reversed w 0 5 ∧ reversed w 1 2 ∧ reversed w 1 4 ∧ reversed w 3 4) -
      4 * ind (reversed w 0 1 ∧ reversed w 0 3 ∧ reversed w 0 5 ∧ reversed w 2 3 ∧ reversed w 2 5 ∧ reversed w 4 5) := by
  rcases overlap_control w with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36, h37, h38, h39, h40, h41, h42, h43, h44, h45, h46, h47, h48, h49, h50, h51, h52, h53, h54, h55, h56, h57, h58, h59, h60, h61, h62, h63, h64, h65, h66, h67, h68, h69, h70, h71, h72, h73, h74, h75, h76, h77, h78, h79, h80, h81, h82, h83, h84, h85, h86, h87, h88, h89, h90, h91, h92, h93, h94, h95, h96, h97, h98, h99, h100, h101, h102, h103, h104⟩
  simp only [ind, valid_iff]
  all_goals by_cases h01 : reversed w 0 1 <;> simp_all
  all_goals by_cases h02 : reversed w 0 2 <;> simp_all
  all_goals by_cases h03 : reversed w 0 3 <;> simp_all
  all_goals by_cases h04 : reversed w 0 4 <;> simp_all
  all_goals by_cases h05 : reversed w 0 5 <;> simp_all
  all_goals by_cases h12 : reversed w 1 2 <;> simp_all
  all_goals by_cases h13 : reversed w 1 3 <;> simp_all
  all_goals by_cases h14 : reversed w 1 4 <;> simp_all
  all_goals by_cases h15 : reversed w 1 5 <;> simp_all
  all_goals by_cases h23 : reversed w 2 3 <;> simp_all
  all_goals by_cases h24 : reversed w 2 4 <;> simp_all
  all_goals by_cases h25 : reversed w 2 5 <;> simp_all
  all_goals by_cases h34 : reversed w 3 4 <;> simp_all
  all_goals by_cases h35 : reversed w 3 5 <;> simp_all
  all_goals by_cases h45 : reversed w 4 5 <;> simp_all

private def translate {n width : ℕ} (x : Fin (n + 1 - width)) (offset : Fin (width + 1)) :
    Fin (n + 1) :=
  ⟨x.val + offset.val, by have hx := x.isLt; have ho := offset.isLt; omega⟩

private theorem count01 (n : ℕ) :
    Nat.card {w : Word n // reversed w 0 1} = n * (n + 1) * (n + 1) * (n + 1) * (n + 1) := by
  let word : Fin n × Fin (n + 1) × Fin (n + 1) × Fin (n + 1) × Fin (n + 1) → Word n := fun t => tuple (translate (width := 1) t.1 0) (translate (width := 1) t.1 1) (translate (width := 1) t.1 0) t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2
  let e : {w : Word n // reversed w 0 1} ≃ Fin n × Fin (n + 1) × Fin (n + 1) × Fin (n + 1) × Fin (n + 1) := {
    toFun := fun w => (⟨(w.1 0).val, by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      have hb := (w.1 1).isLt
      omega⟩, w.1 3, w.1 4, w.1 5, w.1 6)
    invFun := fun t => ⟨word t, by simp [word, tuple, translate, reversed]⟩
    left_inv := fun w => by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      apply Subtype.ext
      funext j
      fin_cases j <;> simp [word, tuple, translate, Fin.ext_iff] <;> omega
    right_inv := fun _ => rfl }
  simpa only [Nat.card_fin, Nat.card_prod, mul_assoc] using Nat.card_congr e

private theorem count02 (n : ℕ) :
    Nat.card {w : Word n // reversed w 0 2} = n * (n + 1) * (n + 1) * (n + 1) := by
  let word : Fin n × Fin (n + 1) × Fin (n + 1) × Fin (n + 1) → Word n := fun t => tuple (translate (width := 1) t.1 0) (translate (width := 1) t.1 1) (translate (width := 1) t.1 1) (translate (width := 1) t.1 0) t.2.1 t.2.2.1 t.2.2.2
  let e : {w : Word n // reversed w 0 2} ≃ Fin n × Fin (n + 1) × Fin (n + 1) × Fin (n + 1) := {
    toFun := fun w => (⟨(w.1 0).val, by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      have hb := (w.1 1).isLt
      omega⟩, w.1 4, w.1 5, w.1 6)
    invFun := fun t => ⟨word t, by simp [word, tuple, translate, reversed]⟩
    left_inv := fun w => by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      apply Subtype.ext
      funext j
      fin_cases j <;> simp [word, tuple, translate, Fin.ext_iff] <;> omega
    right_inv := fun _ => rfl }
  simpa only [Nat.card_fin, Nat.card_prod, mul_assoc] using Nat.card_congr e

private theorem count03 (n : ℕ) :
    Nat.card {w : Word n // reversed w 0 3} = n * (n + 1) * (n + 1) * (n + 1) := by
  let word : Fin n × Fin (n + 1) × Fin (n + 1) × Fin (n + 1) → Word n := fun t => tuple (translate (width := 1) t.1 0) (translate (width := 1) t.1 1) t.2.1 (translate (width := 1) t.1 1) (translate (width := 1) t.1 0) t.2.2.1 t.2.2.2
  let e : {w : Word n // reversed w 0 3} ≃ Fin n × Fin (n + 1) × Fin (n + 1) × Fin (n + 1) := {
    toFun := fun w => (⟨(w.1 0).val, by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      have hb := (w.1 1).isLt
      omega⟩, w.1 2, w.1 5, w.1 6)
    invFun := fun t => ⟨word t, by simp [word, tuple, translate, reversed]⟩
    left_inv := fun w => by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      apply Subtype.ext
      funext j
      fin_cases j <;> simp [word, tuple, translate, Fin.ext_iff] <;> omega
    right_inv := fun _ => rfl }
  simpa only [Nat.card_fin, Nat.card_prod, mul_assoc] using Nat.card_congr e

private theorem count04 (n : ℕ) :
    Nat.card {w : Word n // reversed w 0 4} = n * (n + 1) * (n + 1) * (n + 1) := by
  let word : Fin n × Fin (n + 1) × Fin (n + 1) × Fin (n + 1) → Word n := fun t => tuple (translate (width := 1) t.1 0) (translate (width := 1) t.1 1) t.2.1 t.2.2.1 (translate (width := 1) t.1 1) (translate (width := 1) t.1 0) t.2.2.2
  let e : {w : Word n // reversed w 0 4} ≃ Fin n × Fin (n + 1) × Fin (n + 1) × Fin (n + 1) := {
    toFun := fun w => (⟨(w.1 0).val, by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      have hb := (w.1 1).isLt
      omega⟩, w.1 2, w.1 3, w.1 6)
    invFun := fun t => ⟨word t, by simp [word, tuple, translate, reversed]⟩
    left_inv := fun w => by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      apply Subtype.ext
      funext j
      fin_cases j <;> simp [word, tuple, translate, Fin.ext_iff] <;> omega
    right_inv := fun _ => rfl }
  simpa only [Nat.card_fin, Nat.card_prod, mul_assoc] using Nat.card_congr e

private theorem count05 (n : ℕ) :
    Nat.card {w : Word n // reversed w 0 5} = n * (n + 1) * (n + 1) * (n + 1) := by
  let word : Fin n × Fin (n + 1) × Fin (n + 1) × Fin (n + 1) → Word n := fun t => tuple (translate (width := 1) t.1 0) (translate (width := 1) t.1 1) t.2.1 t.2.2.1 t.2.2.2 (translate (width := 1) t.1 1) (translate (width := 1) t.1 0)
  let e : {w : Word n // reversed w 0 5} ≃ Fin n × Fin (n + 1) × Fin (n + 1) × Fin (n + 1) := {
    toFun := fun w => (⟨(w.1 0).val, by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      have hb := (w.1 1).isLt
      omega⟩, w.1 2, w.1 3, w.1 4)
    invFun := fun t => ⟨word t, by simp [word, tuple, translate, reversed]⟩
    left_inv := fun w => by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      apply Subtype.ext
      funext j
      fin_cases j <;> simp [word, tuple, translate, Fin.ext_iff] <;> omega
    right_inv := fun _ => rfl }
  simpa only [Nat.card_fin, Nat.card_prod, mul_assoc] using Nat.card_congr e

private theorem count12 (n : ℕ) :
    Nat.card {w : Word n // reversed w 1 2} = n * (n + 1) * (n + 1) * (n + 1) * (n + 1) := by
  let word : Fin n × Fin (n + 1) × Fin (n + 1) × Fin (n + 1) × Fin (n + 1) → Word n := fun t => tuple t.2.1 (translate (width := 1) t.1 0) (translate (width := 1) t.1 1) (translate (width := 1) t.1 0) t.2.2.1 t.2.2.2.1 t.2.2.2.2
  let e : {w : Word n // reversed w 1 2} ≃ Fin n × Fin (n + 1) × Fin (n + 1) × Fin (n + 1) × Fin (n + 1) := {
    toFun := fun w => (⟨(w.1 1).val, by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      have hb := (w.1 2).isLt
      omega⟩, w.1 0, w.1 4, w.1 5, w.1 6)
    invFun := fun t => ⟨word t, by simp [word, tuple, translate, reversed]⟩
    left_inv := fun w => by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      apply Subtype.ext
      funext j
      fin_cases j <;> simp [word, tuple, translate, Fin.ext_iff] <;> omega
    right_inv := fun _ => rfl }
  simpa only [Nat.card_fin, Nat.card_prod, mul_assoc] using Nat.card_congr e

private theorem count13 (n : ℕ) :
    Nat.card {w : Word n // reversed w 1 3} = n * (n + 1) * (n + 1) * (n + 1) := by
  let word : Fin n × Fin (n + 1) × Fin (n + 1) × Fin (n + 1) → Word n := fun t => tuple t.2.1 (translate (width := 1) t.1 0) (translate (width := 1) t.1 1) (translate (width := 1) t.1 1) (translate (width := 1) t.1 0) t.2.2.1 t.2.2.2
  let e : {w : Word n // reversed w 1 3} ≃ Fin n × Fin (n + 1) × Fin (n + 1) × Fin (n + 1) := {
    toFun := fun w => (⟨(w.1 1).val, by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      have hb := (w.1 2).isLt
      omega⟩, w.1 0, w.1 5, w.1 6)
    invFun := fun t => ⟨word t, by simp [word, tuple, translate, reversed]⟩
    left_inv := fun w => by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      apply Subtype.ext
      funext j
      fin_cases j <;> simp [word, tuple, translate, Fin.ext_iff] <;> omega
    right_inv := fun _ => rfl }
  simpa only [Nat.card_fin, Nat.card_prod, mul_assoc] using Nat.card_congr e

private theorem count14 (n : ℕ) :
    Nat.card {w : Word n // reversed w 1 4} = n * (n + 1) * (n + 1) * (n + 1) := by
  let word : Fin n × Fin (n + 1) × Fin (n + 1) × Fin (n + 1) → Word n := fun t => tuple t.2.1 (translate (width := 1) t.1 0) (translate (width := 1) t.1 1) t.2.2.1 (translate (width := 1) t.1 1) (translate (width := 1) t.1 0) t.2.2.2
  let e : {w : Word n // reversed w 1 4} ≃ Fin n × Fin (n + 1) × Fin (n + 1) × Fin (n + 1) := {
    toFun := fun w => (⟨(w.1 1).val, by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      have hb := (w.1 2).isLt
      omega⟩, w.1 0, w.1 3, w.1 6)
    invFun := fun t => ⟨word t, by simp [word, tuple, translate, reversed]⟩
    left_inv := fun w => by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      apply Subtype.ext
      funext j
      fin_cases j <;> simp [word, tuple, translate, Fin.ext_iff] <;> omega
    right_inv := fun _ => rfl }
  simpa only [Nat.card_fin, Nat.card_prod, mul_assoc] using Nat.card_congr e

private theorem count15 (n : ℕ) :
    Nat.card {w : Word n // reversed w 1 5} = n * (n + 1) * (n + 1) * (n + 1) := by
  let word : Fin n × Fin (n + 1) × Fin (n + 1) × Fin (n + 1) → Word n := fun t => tuple t.2.1 (translate (width := 1) t.1 0) (translate (width := 1) t.1 1) t.2.2.1 t.2.2.2 (translate (width := 1) t.1 1) (translate (width := 1) t.1 0)
  let e : {w : Word n // reversed w 1 5} ≃ Fin n × Fin (n + 1) × Fin (n + 1) × Fin (n + 1) := {
    toFun := fun w => (⟨(w.1 1).val, by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      have hb := (w.1 2).isLt
      omega⟩, w.1 0, w.1 3, w.1 4)
    invFun := fun t => ⟨word t, by simp [word, tuple, translate, reversed]⟩
    left_inv := fun w => by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      apply Subtype.ext
      funext j
      fin_cases j <;> simp [word, tuple, translate, Fin.ext_iff] <;> omega
    right_inv := fun _ => rfl }
  simpa only [Nat.card_fin, Nat.card_prod, mul_assoc] using Nat.card_congr e

private theorem count23 (n : ℕ) :
    Nat.card {w : Word n // reversed w 2 3} = n * (n + 1) * (n + 1) * (n + 1) * (n + 1) := by
  let word : Fin n × Fin (n + 1) × Fin (n + 1) × Fin (n + 1) × Fin (n + 1) → Word n := fun t => tuple t.2.1 t.2.2.1 (translate (width := 1) t.1 0) (translate (width := 1) t.1 1) (translate (width := 1) t.1 0) t.2.2.2.1 t.2.2.2.2
  let e : {w : Word n // reversed w 2 3} ≃ Fin n × Fin (n + 1) × Fin (n + 1) × Fin (n + 1) × Fin (n + 1) := {
    toFun := fun w => (⟨(w.1 2).val, by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      have hb := (w.1 3).isLt
      omega⟩, w.1 0, w.1 1, w.1 5, w.1 6)
    invFun := fun t => ⟨word t, by simp [word, tuple, translate, reversed]⟩
    left_inv := fun w => by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      apply Subtype.ext
      funext j
      fin_cases j <;> simp [word, tuple, translate, Fin.ext_iff] <;> omega
    right_inv := fun _ => rfl }
  simpa only [Nat.card_fin, Nat.card_prod, mul_assoc] using Nat.card_congr e

private theorem count24 (n : ℕ) :
    Nat.card {w : Word n // reversed w 2 4} = n * (n + 1) * (n + 1) * (n + 1) := by
  let word : Fin n × Fin (n + 1) × Fin (n + 1) × Fin (n + 1) → Word n := fun t => tuple t.2.1 t.2.2.1 (translate (width := 1) t.1 0) (translate (width := 1) t.1 1) (translate (width := 1) t.1 1) (translate (width := 1) t.1 0) t.2.2.2
  let e : {w : Word n // reversed w 2 4} ≃ Fin n × Fin (n + 1) × Fin (n + 1) × Fin (n + 1) := {
    toFun := fun w => (⟨(w.1 2).val, by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      have hb := (w.1 3).isLt
      omega⟩, w.1 0, w.1 1, w.1 6)
    invFun := fun t => ⟨word t, by simp [word, tuple, translate, reversed]⟩
    left_inv := fun w => by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      apply Subtype.ext
      funext j
      fin_cases j <;> simp [word, tuple, translate, Fin.ext_iff] <;> omega
    right_inv := fun _ => rfl }
  simpa only [Nat.card_fin, Nat.card_prod, mul_assoc] using Nat.card_congr e

private theorem count25 (n : ℕ) :
    Nat.card {w : Word n // reversed w 2 5} = n * (n + 1) * (n + 1) * (n + 1) := by
  let word : Fin n × Fin (n + 1) × Fin (n + 1) × Fin (n + 1) → Word n := fun t => tuple t.2.1 t.2.2.1 (translate (width := 1) t.1 0) (translate (width := 1) t.1 1) t.2.2.2 (translate (width := 1) t.1 1) (translate (width := 1) t.1 0)
  let e : {w : Word n // reversed w 2 5} ≃ Fin n × Fin (n + 1) × Fin (n + 1) × Fin (n + 1) := {
    toFun := fun w => (⟨(w.1 2).val, by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      have hb := (w.1 3).isLt
      omega⟩, w.1 0, w.1 1, w.1 4)
    invFun := fun t => ⟨word t, by simp [word, tuple, translate, reversed]⟩
    left_inv := fun w => by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      apply Subtype.ext
      funext j
      fin_cases j <;> simp [word, tuple, translate, Fin.ext_iff] <;> omega
    right_inv := fun _ => rfl }
  simpa only [Nat.card_fin, Nat.card_prod, mul_assoc] using Nat.card_congr e

private theorem count34 (n : ℕ) :
    Nat.card {w : Word n // reversed w 3 4} = n * (n + 1) * (n + 1) * (n + 1) * (n + 1) := by
  let word : Fin n × Fin (n + 1) × Fin (n + 1) × Fin (n + 1) × Fin (n + 1) → Word n := fun t => tuple t.2.1 t.2.2.1 t.2.2.2.1 (translate (width := 1) t.1 0) (translate (width := 1) t.1 1) (translate (width := 1) t.1 0) t.2.2.2.2
  let e : {w : Word n // reversed w 3 4} ≃ Fin n × Fin (n + 1) × Fin (n + 1) × Fin (n + 1) × Fin (n + 1) := {
    toFun := fun w => (⟨(w.1 3).val, by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      have hb := (w.1 4).isLt
      omega⟩, w.1 0, w.1 1, w.1 2, w.1 6)
    invFun := fun t => ⟨word t, by simp [word, tuple, translate, reversed]⟩
    left_inv := fun w => by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      apply Subtype.ext
      funext j
      fin_cases j <;> simp [word, tuple, translate, Fin.ext_iff] <;> omega
    right_inv := fun _ => rfl }
  simpa only [Nat.card_fin, Nat.card_prod, mul_assoc] using Nat.card_congr e

private theorem count35 (n : ℕ) :
    Nat.card {w : Word n // reversed w 3 5} = n * (n + 1) * (n + 1) * (n + 1) := by
  let word : Fin n × Fin (n + 1) × Fin (n + 1) × Fin (n + 1) → Word n := fun t => tuple t.2.1 t.2.2.1 t.2.2.2 (translate (width := 1) t.1 0) (translate (width := 1) t.1 1) (translate (width := 1) t.1 1) (translate (width := 1) t.1 0)
  let e : {w : Word n // reversed w 3 5} ≃ Fin n × Fin (n + 1) × Fin (n + 1) × Fin (n + 1) := {
    toFun := fun w => (⟨(w.1 3).val, by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      have hb := (w.1 4).isLt
      omega⟩, w.1 0, w.1 1, w.1 2)
    invFun := fun t => ⟨word t, by simp [word, tuple, translate, reversed]⟩
    left_inv := fun w => by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      apply Subtype.ext
      funext j
      fin_cases j <;> simp [word, tuple, translate, Fin.ext_iff] <;> omega
    right_inv := fun _ => rfl }
  simpa only [Nat.card_fin, Nat.card_prod, mul_assoc] using Nat.card_congr e

private theorem count45 (n : ℕ) :
    Nat.card {w : Word n // reversed w 4 5} = n * (n + 1) * (n + 1) * (n + 1) * (n + 1) := by
  let word : Fin n × Fin (n + 1) × Fin (n + 1) × Fin (n + 1) × Fin (n + 1) → Word n := fun t => tuple t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2 (translate (width := 1) t.1 0) (translate (width := 1) t.1 1) (translate (width := 1) t.1 0)
  let e : {w : Word n // reversed w 4 5} ≃ Fin n × Fin (n + 1) × Fin (n + 1) × Fin (n + 1) × Fin (n + 1) := {
    toFun := fun w => (⟨(w.1 4).val, by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      have hb := (w.1 5).isLt
      omega⟩, w.1 0, w.1 1, w.1 2, w.1 3)
    invFun := fun t => ⟨word t, by simp [word, tuple, translate, reversed]⟩
    left_inv := fun w => by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      apply Subtype.ext
      funext j
      fin_cases j <;> simp [word, tuple, translate, Fin.ext_iff] <;> omega
    right_inv := fun _ => rfl }
  simpa only [Nat.card_fin, Nat.card_prod, mul_assoc] using Nat.card_congr e

private theorem count0104 (n : ℕ) :
    Nat.card {w : Word n // reversed w 0 1 ∧ reversed w 0 4} = n * (n + 1) * (n + 1) := by
  let word : Fin n × Fin (n + 1) × Fin (n + 1) → Word n := fun t => tuple (translate (width := 1) t.1 0) (translate (width := 1) t.1 1) (translate (width := 1) t.1 0) t.2.1 (translate (width := 1) t.1 1) (translate (width := 1) t.1 0) t.2.2
  let e : {w : Word n // reversed w 0 1 ∧ reversed w 0 4} ≃ Fin n × Fin (n + 1) × Fin (n + 1) := {
    toFun := fun w => (⟨(w.1 0).val, by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      have hb := (w.1 1).isLt
      omega⟩, w.1 3, w.1 6)
    invFun := fun t => ⟨word t, by simp [word, tuple, translate, reversed]⟩
    left_inv := fun w => by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      apply Subtype.ext
      funext j
      fin_cases j <;> simp [word, tuple, translate, Fin.ext_iff] <;> omega
    right_inv := fun _ => rfl }
  simpa only [Nat.card_fin, Nat.card_prod, mul_assoc] using Nat.card_congr e

private theorem count0105 (n : ℕ) :
    Nat.card {w : Word n // reversed w 0 1 ∧ reversed w 0 5} = n * (n + 1) * (n + 1) := by
  let word : Fin n × Fin (n + 1) × Fin (n + 1) → Word n := fun t => tuple (translate (width := 1) t.1 0) (translate (width := 1) t.1 1) (translate (width := 1) t.1 0) t.2.1 t.2.2 (translate (width := 1) t.1 1) (translate (width := 1) t.1 0)
  let e : {w : Word n // reversed w 0 1 ∧ reversed w 0 5} ≃ Fin n × Fin (n + 1) × Fin (n + 1) := {
    toFun := fun w => (⟨(w.1 0).val, by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      have hb := (w.1 1).isLt
      omega⟩, w.1 3, w.1 4)
    invFun := fun t => ⟨word t, by simp [word, tuple, translate, reversed]⟩
    left_inv := fun w => by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      apply Subtype.ext
      funext j
      fin_cases j <;> simp [word, tuple, translate, Fin.ext_iff] <;> omega
    right_inv := fun _ => rfl }
  simpa only [Nat.card_fin, Nat.card_prod, mul_assoc] using Nat.card_congr e

private theorem count0134 (n : ℕ) :
    Nat.card {w : Word n // reversed w 0 1 ∧ reversed w 3 4} = n * n * (n + 1) := by
  let word : Fin n × Fin n × Fin (n + 1) → Word n := fun t => tuple (translate (width := 1) t.1 0) (translate (width := 1) t.1 1) (translate (width := 1) t.1 0) (translate (width := 1) t.2.1 0) (translate (width := 1) t.2.1 1) (translate (width := 1) t.2.1 0) t.2.2
  let e : {w : Word n // reversed w 0 1 ∧ reversed w 3 4} ≃ Fin n × Fin n × Fin (n + 1) := {
    toFun := fun w => (⟨(w.1 0).val, by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      have hb := (w.1 1).isLt
      omega⟩, ⟨(w.1 3).val, by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      have hb := (w.1 4).isLt
      omega⟩, w.1 6)
    invFun := fun t => ⟨word t, by simp [word, tuple, translate, reversed]⟩
    left_inv := fun w => by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      apply Subtype.ext
      funext j
      fin_cases j <;> simp [word, tuple, translate, Fin.ext_iff] <;> omega
    right_inv := fun _ => rfl }
  simpa only [Nat.card_fin, Nat.card_prod, mul_assoc] using Nat.card_congr e

private theorem count0135 (n : ℕ) :
    Nat.card {w : Word n // reversed w 0 1 ∧ reversed w 3 5} = n * n := by
  let word : Fin n × Fin n → Word n := fun t => tuple (translate (width := 1) t.1 0) (translate (width := 1) t.1 1) (translate (width := 1) t.1 0) (translate (width := 1) t.2 0) (translate (width := 1) t.2 1) (translate (width := 1) t.2 1) (translate (width := 1) t.2 0)
  let e : {w : Word n // reversed w 0 1 ∧ reversed w 3 5} ≃ Fin n × Fin n := {
    toFun := fun w => (⟨(w.1 0).val, by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      have hb := (w.1 1).isLt
      omega⟩, ⟨(w.1 3).val, by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      have hb := (w.1 4).isLt
      omega⟩)
    invFun := fun t => ⟨word t, by simp [word, tuple, translate, reversed]⟩
    left_inv := fun w => by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      apply Subtype.ext
      funext j
      fin_cases j <;> simp [word, tuple, translate, Fin.ext_iff] <;> omega
    right_inv := fun _ => rfl }
  simpa only [Nat.card_fin, Nat.card_prod, mul_assoc] using Nat.card_congr e

private theorem count0145 (n : ℕ) :
    Nat.card {w : Word n // reversed w 0 1 ∧ reversed w 4 5} = n * n * (n + 1) := by
  let word : Fin n × Fin n × Fin (n + 1) → Word n := fun t => tuple (translate (width := 1) t.1 0) (translate (width := 1) t.1 1) (translate (width := 1) t.1 0) t.2.2 (translate (width := 1) t.2.1 0) (translate (width := 1) t.2.1 1) (translate (width := 1) t.2.1 0)
  let e : {w : Word n // reversed w 0 1 ∧ reversed w 4 5} ≃ Fin n × Fin n × Fin (n + 1) := {
    toFun := fun w => (⟨(w.1 0).val, by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      have hb := (w.1 1).isLt
      omega⟩, ⟨(w.1 4).val, by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      have hb := (w.1 5).isLt
      omega⟩, w.1 3)
    invFun := fun t => ⟨word t, by simp [word, tuple, translate, reversed]⟩
    left_inv := fun w => by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      apply Subtype.ext
      funext j
      fin_cases j <;> simp [word, tuple, translate, Fin.ext_iff] <;> omega
    right_inv := fun _ => rfl }
  simpa only [Nat.card_fin, Nat.card_prod, mul_assoc] using Nat.card_congr e

private theorem count0205 (n : ℕ) :
    Nat.card {w : Word n // reversed w 0 2 ∧ reversed w 0 5} = n * (n + 1) := by
  let word : Fin n × Fin (n + 1) → Word n := fun t => tuple (translate (width := 1) t.1 0) (translate (width := 1) t.1 1) (translate (width := 1) t.1 1) (translate (width := 1) t.1 0) t.2 (translate (width := 1) t.1 1) (translate (width := 1) t.1 0)
  let e : {w : Word n // reversed w 0 2 ∧ reversed w 0 5} ≃ Fin n × Fin (n + 1) := {
    toFun := fun w => (⟨(w.1 0).val, by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      have hb := (w.1 1).isLt
      omega⟩, w.1 4)
    invFun := fun t => ⟨word t, by simp [word, tuple, translate, reversed]⟩
    left_inv := fun w => by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      apply Subtype.ext
      funext j
      fin_cases j <;> simp [word, tuple, translate, Fin.ext_iff] <;> omega
    right_inv := fun _ => rfl }
  simpa only [Nat.card_fin, Nat.card_prod, mul_assoc] using Nat.card_congr e

private theorem count0245 (n : ℕ) :
    Nat.card {w : Word n // reversed w 0 2 ∧ reversed w 4 5} = n * n := by
  let word : Fin n × Fin n → Word n := fun t => tuple (translate (width := 1) t.1 0) (translate (width := 1) t.1 1) (translate (width := 1) t.1 1) (translate (width := 1) t.1 0) (translate (width := 1) t.2 0) (translate (width := 1) t.2 1) (translate (width := 1) t.2 0)
  let e : {w : Word n // reversed w 0 2 ∧ reversed w 4 5} ≃ Fin n × Fin n := {
    toFun := fun w => (⟨(w.1 0).val, by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      have hb := (w.1 1).isLt
      omega⟩, ⟨(w.1 4).val, by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      have hb := (w.1 5).isLt
      omega⟩)
    invFun := fun t => ⟨word t, by simp [word, tuple, translate, reversed]⟩
    left_inv := fun w => by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      apply Subtype.ext
      funext j
      fin_cases j <;> simp [word, tuple, translate, Fin.ext_iff] <;> omega
    right_inv := fun _ => rfl }
  simpa only [Nat.card_fin, Nat.card_prod, mul_assoc] using Nat.card_congr e

private theorem count0312 (n : ℕ) :
    Nat.card {w : Word n // reversed w 0 3 ∧ reversed w 1 2} = (n - 1) * (n + 1) * (n + 1) := by
  let word : Fin (n - 1) × Fin (n + 1) × Fin (n + 1) → Word n := fun t => tuple (translate (width := 2) t.1 0) (translate (width := 2) t.1 1) (translate (width := 2) t.1 2) (translate (width := 2) t.1 1) (translate (width := 2) t.1 0) t.2.1 t.2.2
  let e : {w : Word n // reversed w 0 3 ∧ reversed w 1 2} ≃ Fin (n - 1) × Fin (n + 1) × Fin (n + 1) := {
    toFun := fun w => (⟨(w.1 0).val, by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      have hb := (w.1 2).isLt
      omega⟩, w.1 5, w.1 6)
    invFun := fun t => ⟨word t, by simp [word, tuple, translate, reversed]⟩
    left_inv := fun w => by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      apply Subtype.ext
      funext j
      fin_cases j <;> simp [word, tuple, translate, Fin.ext_iff] <;> omega
    right_inv := fun _ => rfl }
  simpa only [Nat.card_fin, Nat.card_prod, mul_assoc] using Nat.card_congr e

private theorem count0412 (n : ℕ) :
    Nat.card {w : Word n // reversed w 0 4 ∧ reversed w 1 2} = (n - 1) * (n + 1) := by
  let word : Fin (n - 1) × Fin (n + 1) → Word n := fun t => tuple (translate (width := 2) t.1 0) (translate (width := 2) t.1 1) (translate (width := 2) t.1 2) (translate (width := 2) t.1 1) (translate (width := 2) t.1 1) (translate (width := 2) t.1 0) t.2
  let e : {w : Word n // reversed w 0 4 ∧ reversed w 1 2} ≃ Fin (n - 1) × Fin (n + 1) := {
    toFun := fun w => (⟨(w.1 0).val, by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      have hb := (w.1 2).isLt
      omega⟩, w.1 6)
    invFun := fun t => ⟨word t, by simp [word, tuple, translate, reversed]⟩
    left_inv := fun w => by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      apply Subtype.ext
      funext j
      fin_cases j <;> simp [word, tuple, translate, Fin.ext_iff] <;> omega
    right_inv := fun _ => rfl }
  simpa only [Nat.card_fin, Nat.card_prod, mul_assoc] using Nat.card_congr e

private theorem count0413 (n : ℕ) :
    Nat.card {w : Word n // reversed w 0 4 ∧ reversed w 1 3} = (n - 1) * (n + 1) := by
  let word : Fin (n - 1) × Fin (n + 1) → Word n := fun t => tuple (translate (width := 2) t.1 0) (translate (width := 2) t.1 1) (translate (width := 2) t.1 2) (translate (width := 2) t.1 2) (translate (width := 2) t.1 1) (translate (width := 2) t.1 0) t.2
  let e : {w : Word n // reversed w 0 4 ∧ reversed w 1 3} ≃ Fin (n - 1) × Fin (n + 1) := {
    toFun := fun w => (⟨(w.1 0).val, by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      have hb := (w.1 2).isLt
      omega⟩, w.1 6)
    invFun := fun t => ⟨word t, by simp [word, tuple, translate, reversed]⟩
    left_inv := fun w => by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      apply Subtype.ext
      funext j
      fin_cases j <;> simp [word, tuple, translate, Fin.ext_iff] <;> omega
    right_inv := fun _ => rfl }
  simpa only [Nat.card_fin, Nat.card_prod, mul_assoc] using Nat.card_congr e

private theorem count0423 (n : ℕ) :
    Nat.card {w : Word n // reversed w 0 4 ∧ reversed w 2 3} = (n - 1) * (n + 1) := by
  let word : Fin (n - 1) × Fin (n + 1) → Word n := fun t => tuple (translate (width := 2) t.1 0) (translate (width := 2) t.1 1) (translate (width := 2) t.1 1) (translate (width := 2) t.1 2) (translate (width := 2) t.1 1) (translate (width := 2) t.1 0) t.2
  let e : {w : Word n // reversed w 0 4 ∧ reversed w 2 3} ≃ Fin (n - 1) × Fin (n + 1) := {
    toFun := fun w => (⟨(w.1 0).val, by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      have hb := (w.1 3).isLt
      omega⟩, w.1 6)
    invFun := fun t => ⟨word t, by simp [word, tuple, translate, reversed]⟩
    left_inv := fun w => by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      apply Subtype.ext
      funext j
      fin_cases j <;> simp [word, tuple, translate, Fin.ext_iff] <;> omega
    right_inv := fun _ => rfl }
  simpa only [Nat.card_fin, Nat.card_prod, mul_assoc] using Nat.card_congr e

private theorem count0434 (n : ℕ) :
    Nat.card {w : Word n // reversed w 0 4 ∧ reversed w 3 4} = n * (n + 1) * (n + 1) := by
  let word : Fin n × Fin (n + 1) × Fin (n + 1) → Word n := fun t => tuple (translate (width := 1) t.1 0) (translate (width := 1) t.1 1) t.2.1 (translate (width := 1) t.1 0) (translate (width := 1) t.1 1) (translate (width := 1) t.1 0) t.2.2
  let e : {w : Word n // reversed w 0 4 ∧ reversed w 3 4} ≃ Fin n × Fin (n + 1) × Fin (n + 1) := {
    toFun := fun w => (⟨(w.1 0).val, by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      have hb := (w.1 1).isLt
      omega⟩, w.1 2, w.1 6)
    invFun := fun t => ⟨word t, by simp [word, tuple, translate, reversed]⟩
    left_inv := fun w => by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      apply Subtype.ext
      funext j
      fin_cases j <;> simp [word, tuple, translate, Fin.ext_iff] <;> omega
    right_inv := fun _ => rfl }
  simpa only [Nat.card_fin, Nat.card_prod, mul_assoc] using Nat.card_congr e

private theorem count0512 (n : ℕ) :
    Nat.card {w : Word n // reversed w 0 5 ∧ reversed w 1 2} = (n - 1) * (n + 1) := by
  let word : Fin (n - 1) × Fin (n + 1) → Word n := fun t => tuple (translate (width := 2) t.1 0) (translate (width := 2) t.1 1) (translate (width := 2) t.1 2) (translate (width := 2) t.1 1) t.2 (translate (width := 2) t.1 1) (translate (width := 2) t.1 0)
  let e : {w : Word n // reversed w 0 5 ∧ reversed w 1 2} ≃ Fin (n - 1) × Fin (n + 1) := {
    toFun := fun w => (⟨(w.1 0).val, by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      have hb := (w.1 2).isLt
      omega⟩, w.1 4)
    invFun := fun t => ⟨word t, by simp [word, tuple, translate, reversed]⟩
    left_inv := fun w => by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      apply Subtype.ext
      funext j
      fin_cases j <;> simp [word, tuple, translate, Fin.ext_iff] <;> omega
    right_inv := fun _ => rfl }
  simpa only [Nat.card_fin, Nat.card_prod, mul_assoc] using Nat.card_congr e

private theorem count0513 (n : ℕ) :
    Nat.card {w : Word n // reversed w 0 5 ∧ reversed w 1 3} = (n - 1) := by
  let word : Fin (n - 1) → Word n := fun t => tuple (translate (width := 2) t 0) (translate (width := 2) t 1) (translate (width := 2) t 2) (translate (width := 2) t 2) (translate (width := 2) t 1) (translate (width := 2) t 1) (translate (width := 2) t 0)
  let e : {w : Word n // reversed w 0 5 ∧ reversed w 1 3} ≃ Fin (n - 1) := {
    toFun := fun w => ⟨(w.1 0).val, by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      have hb := (w.1 2).isLt
      omega⟩
    invFun := fun t => ⟨word t, by simp [word, tuple, translate, reversed]⟩
    left_inv := fun w => by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      apply Subtype.ext
      funext j
      fin_cases j <;> simp [word, tuple, translate, Fin.ext_iff] <;> omega
    right_inv := fun _ => rfl }
  simpa only [Nat.card_fin] using Nat.card_congr e

private theorem count0514 (n : ℕ) :
    Nat.card {w : Word n // reversed w 0 5 ∧ reversed w 1 4} = (n - 1) * (n + 1) := by
  let word : Fin (n - 1) × Fin (n + 1) → Word n := fun t => tuple (translate (width := 2) t.1 0) (translate (width := 2) t.1 1) (translate (width := 2) t.1 2) t.2 (translate (width := 2) t.1 2) (translate (width := 2) t.1 1) (translate (width := 2) t.1 0)
  let e : {w : Word n // reversed w 0 5 ∧ reversed w 1 4} ≃ Fin (n - 1) × Fin (n + 1) := {
    toFun := fun w => (⟨(w.1 0).val, by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      have hb := (w.1 2).isLt
      omega⟩, w.1 3)
    invFun := fun t => ⟨word t, by simp [word, tuple, translate, reversed]⟩
    left_inv := fun w => by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      apply Subtype.ext
      funext j
      fin_cases j <;> simp [word, tuple, translate, Fin.ext_iff] <;> omega
    right_inv := fun _ => rfl }
  simpa only [Nat.card_fin, Nat.card_prod, mul_assoc] using Nat.card_congr e

private theorem count0523 (n : ℕ) :
    Nat.card {w : Word n // reversed w 0 5 ∧ reversed w 2 3} = n * n := by
  let word : Fin n × Fin n → Word n := fun t => tuple (translate (width := 1) t.1 0) (translate (width := 1) t.1 1) (translate (width := 1) t.2 0) (translate (width := 1) t.2 1) (translate (width := 1) t.2 0) (translate (width := 1) t.1 1) (translate (width := 1) t.1 0)
  let e : {w : Word n // reversed w 0 5 ∧ reversed w 2 3} ≃ Fin n × Fin n := {
    toFun := fun w => (⟨(w.1 0).val, by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      have hb := (w.1 1).isLt
      omega⟩, ⟨(w.1 2).val, by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      have hb := (w.1 3).isLt
      omega⟩)
    invFun := fun t => ⟨word t, by simp [word, tuple, translate, reversed]⟩
    left_inv := fun w => by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      apply Subtype.ext
      funext j
      fin_cases j <;> simp [word, tuple, translate, Fin.ext_iff] <;> omega
    right_inv := fun _ => rfl }
  simpa only [Nat.card_fin, Nat.card_prod, mul_assoc] using Nat.card_congr e

private theorem count0524 (n : ℕ) :
    Nat.card {w : Word n // reversed w 0 5 ∧ reversed w 2 4} = (n - 1) := by
  let word : Fin (n - 1) → Word n := fun t => tuple (translate (width := 2) t 0) (translate (width := 2) t 1) (translate (width := 2) t 1) (translate (width := 2) t 2) (translate (width := 2) t 2) (translate (width := 2) t 1) (translate (width := 2) t 0)
  let e : {w : Word n // reversed w 0 5 ∧ reversed w 2 4} ≃ Fin (n - 1) := {
    toFun := fun w => ⟨(w.1 0).val, by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      have hb := (w.1 3).isLt
      omega⟩
    invFun := fun t => ⟨word t, by simp [word, tuple, translate, reversed]⟩
    left_inv := fun w => by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      apply Subtype.ext
      funext j
      fin_cases j <;> simp [word, tuple, translate, Fin.ext_iff] <;> omega
    right_inv := fun _ => rfl }
  simpa only [Nat.card_fin] using Nat.card_congr e

private theorem count0534 (n : ℕ) :
    Nat.card {w : Word n // reversed w 0 5 ∧ reversed w 3 4} = (n - 1) * (n + 1) := by
  let word : Fin (n - 1) × Fin (n + 1) → Word n := fun t => tuple (translate (width := 2) t.1 0) (translate (width := 2) t.1 1) t.2 (translate (width := 2) t.1 1) (translate (width := 2) t.1 2) (translate (width := 2) t.1 1) (translate (width := 2) t.1 0)
  let e : {w : Word n // reversed w 0 5 ∧ reversed w 3 4} ≃ Fin (n - 1) × Fin (n + 1) := {
    toFun := fun w => (⟨(w.1 0).val, by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      have hb := (w.1 4).isLt
      omega⟩, w.1 2)
    invFun := fun t => ⟨word t, by simp [word, tuple, translate, reversed]⟩
    left_inv := fun w => by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      apply Subtype.ext
      funext j
      fin_cases j <;> simp [word, tuple, translate, Fin.ext_iff] <;> omega
    right_inv := fun _ => rfl }
  simpa only [Nat.card_fin, Nat.card_prod, mul_assoc] using Nat.card_congr e

private theorem count0535 (n : ℕ) :
    Nat.card {w : Word n // reversed w 0 5 ∧ reversed w 3 5} = n * (n + 1) := by
  let word : Fin n × Fin (n + 1) → Word n := fun t => tuple (translate (width := 1) t.1 0) (translate (width := 1) t.1 1) t.2 (translate (width := 1) t.1 0) (translate (width := 1) t.1 1) (translate (width := 1) t.1 1) (translate (width := 1) t.1 0)
  let e : {w : Word n // reversed w 0 5 ∧ reversed w 3 5} ≃ Fin n × Fin (n + 1) := {
    toFun := fun w => (⟨(w.1 0).val, by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      have hb := (w.1 1).isLt
      omega⟩, w.1 2)
    invFun := fun t => ⟨word t, by simp [word, tuple, translate, reversed]⟩
    left_inv := fun w => by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      apply Subtype.ext
      funext j
      fin_cases j <;> simp [word, tuple, translate, Fin.ext_iff] <;> omega
    right_inv := fun _ => rfl }
  simpa only [Nat.card_fin, Nat.card_prod, mul_assoc] using Nat.card_congr e

private theorem count0545 (n : ℕ) :
    Nat.card {w : Word n // reversed w 0 5 ∧ reversed w 4 5} = n * (n + 1) * (n + 1) := by
  let word : Fin n × Fin (n + 1) × Fin (n + 1) → Word n := fun t => tuple (translate (width := 1) t.1 0) (translate (width := 1) t.1 1) t.2.1 t.2.2 (translate (width := 1) t.1 0) (translate (width := 1) t.1 1) (translate (width := 1) t.1 0)
  let e : {w : Word n // reversed w 0 5 ∧ reversed w 4 5} ≃ Fin n × Fin (n + 1) × Fin (n + 1) := {
    toFun := fun w => (⟨(w.1 0).val, by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      have hb := (w.1 1).isLt
      omega⟩, w.1 2, w.1 3)
    invFun := fun t => ⟨word t, by simp [word, tuple, translate, reversed]⟩
    left_inv := fun w => by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      apply Subtype.ext
      funext j
      fin_cases j <;> simp [word, tuple, translate, Fin.ext_iff] <;> omega
    right_inv := fun _ => rfl }
  simpa only [Nat.card_fin, Nat.card_prod, mul_assoc] using Nat.card_congr e

private theorem count1215 (n : ℕ) :
    Nat.card {w : Word n // reversed w 1 2 ∧ reversed w 1 5} = n * (n + 1) * (n + 1) := by
  let word : Fin n × Fin (n + 1) × Fin (n + 1) → Word n := fun t => tuple t.2.1 (translate (width := 1) t.1 0) (translate (width := 1) t.1 1) (translate (width := 1) t.1 0) t.2.2 (translate (width := 1) t.1 1) (translate (width := 1) t.1 0)
  let e : {w : Word n // reversed w 1 2 ∧ reversed w 1 5} ≃ Fin n × Fin (n + 1) × Fin (n + 1) := {
    toFun := fun w => (⟨(w.1 1).val, by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      have hb := (w.1 2).isLt
      omega⟩, w.1 0, w.1 4)
    invFun := fun t => ⟨word t, by simp [word, tuple, translate, reversed]⟩
    left_inv := fun w => by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      apply Subtype.ext
      funext j
      fin_cases j <;> simp [word, tuple, translate, Fin.ext_iff] <;> omega
    right_inv := fun _ => rfl }
  simpa only [Nat.card_fin, Nat.card_prod, mul_assoc] using Nat.card_congr e

private theorem count1245 (n : ℕ) :
    Nat.card {w : Word n // reversed w 1 2 ∧ reversed w 4 5} = n * n * (n + 1) := by
  let word : Fin n × Fin n × Fin (n + 1) → Word n := fun t => tuple t.2.2 (translate (width := 1) t.1 0) (translate (width := 1) t.1 1) (translate (width := 1) t.1 0) (translate (width := 1) t.2.1 0) (translate (width := 1) t.2.1 1) (translate (width := 1) t.2.1 0)
  let e : {w : Word n // reversed w 1 2 ∧ reversed w 4 5} ≃ Fin n × Fin n × Fin (n + 1) := {
    toFun := fun w => (⟨(w.1 1).val, by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      have hb := (w.1 2).isLt
      omega⟩, ⟨(w.1 4).val, by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      have hb := (w.1 5).isLt
      omega⟩, w.1 0)
    invFun := fun t => ⟨word t, by simp [word, tuple, translate, reversed]⟩
    left_inv := fun w => by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      apply Subtype.ext
      funext j
      fin_cases j <;> simp [word, tuple, translate, Fin.ext_iff] <;> omega
    right_inv := fun _ => rfl }
  simpa only [Nat.card_fin, Nat.card_prod, mul_assoc] using Nat.card_congr e

private theorem count1423 (n : ℕ) :
    Nat.card {w : Word n // reversed w 1 4 ∧ reversed w 2 3} = (n - 1) * (n + 1) * (n + 1) := by
  let word : Fin (n - 1) × Fin (n + 1) × Fin (n + 1) → Word n := fun t => tuple t.2.1 (translate (width := 2) t.1 0) (translate (width := 2) t.1 1) (translate (width := 2) t.1 2) (translate (width := 2) t.1 1) (translate (width := 2) t.1 0) t.2.2
  let e : {w : Word n // reversed w 1 4 ∧ reversed w 2 3} ≃ Fin (n - 1) × Fin (n + 1) × Fin (n + 1) := {
    toFun := fun w => (⟨(w.1 1).val, by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      have hb := (w.1 3).isLt
      omega⟩, w.1 0, w.1 6)
    invFun := fun t => ⟨word t, by simp [word, tuple, translate, reversed]⟩
    left_inv := fun w => by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      apply Subtype.ext
      funext j
      fin_cases j <;> simp [word, tuple, translate, Fin.ext_iff] <;> omega
    right_inv := fun _ => rfl }
  simpa only [Nat.card_fin, Nat.card_prod, mul_assoc] using Nat.card_congr e

private theorem count1523 (n : ℕ) :
    Nat.card {w : Word n // reversed w 1 5 ∧ reversed w 2 3} = (n - 1) * (n + 1) := by
  let word : Fin (n - 1) × Fin (n + 1) → Word n := fun t => tuple t.2 (translate (width := 2) t.1 0) (translate (width := 2) t.1 1) (translate (width := 2) t.1 2) (translate (width := 2) t.1 1) (translate (width := 2) t.1 1) (translate (width := 2) t.1 0)
  let e : {w : Word n // reversed w 1 5 ∧ reversed w 2 3} ≃ Fin (n - 1) × Fin (n + 1) := {
    toFun := fun w => (⟨(w.1 1).val, by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      have hb := (w.1 3).isLt
      omega⟩, w.1 0)
    invFun := fun t => ⟨word t, by simp [word, tuple, translate, reversed]⟩
    left_inv := fun w => by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      apply Subtype.ext
      funext j
      fin_cases j <;> simp [word, tuple, translate, Fin.ext_iff] <;> omega
    right_inv := fun _ => rfl }
  simpa only [Nat.card_fin, Nat.card_prod, mul_assoc] using Nat.card_congr e

private theorem count1524 (n : ℕ) :
    Nat.card {w : Word n // reversed w 1 5 ∧ reversed w 2 4} = (n - 1) * (n + 1) := by
  let word : Fin (n - 1) × Fin (n + 1) → Word n := fun t => tuple t.2 (translate (width := 2) t.1 0) (translate (width := 2) t.1 1) (translate (width := 2) t.1 2) (translate (width := 2) t.1 2) (translate (width := 2) t.1 1) (translate (width := 2) t.1 0)
  let e : {w : Word n // reversed w 1 5 ∧ reversed w 2 4} ≃ Fin (n - 1) × Fin (n + 1) := {
    toFun := fun w => (⟨(w.1 1).val, by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      have hb := (w.1 3).isLt
      omega⟩, w.1 0)
    invFun := fun t => ⟨word t, by simp [word, tuple, translate, reversed]⟩
    left_inv := fun w => by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      apply Subtype.ext
      funext j
      fin_cases j <;> simp [word, tuple, translate, Fin.ext_iff] <;> omega
    right_inv := fun _ => rfl }
  simpa only [Nat.card_fin, Nat.card_prod, mul_assoc] using Nat.card_congr e

private theorem count1534 (n : ℕ) :
    Nat.card {w : Word n // reversed w 1 5 ∧ reversed w 3 4} = (n - 1) * (n + 1) := by
  let word : Fin (n - 1) × Fin (n + 1) → Word n := fun t => tuple t.2 (translate (width := 2) t.1 0) (translate (width := 2) t.1 1) (translate (width := 2) t.1 1) (translate (width := 2) t.1 2) (translate (width := 2) t.1 1) (translate (width := 2) t.1 0)
  let e : {w : Word n // reversed w 1 5 ∧ reversed w 3 4} ≃ Fin (n - 1) × Fin (n + 1) := {
    toFun := fun w => (⟨(w.1 1).val, by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      have hb := (w.1 4).isLt
      omega⟩, w.1 0)
    invFun := fun t => ⟨word t, by simp [word, tuple, translate, reversed]⟩
    left_inv := fun w => by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      apply Subtype.ext
      funext j
      fin_cases j <;> simp [word, tuple, translate, Fin.ext_iff] <;> omega
    right_inv := fun _ => rfl }
  simpa only [Nat.card_fin, Nat.card_prod, mul_assoc] using Nat.card_congr e

private theorem count1545 (n : ℕ) :
    Nat.card {w : Word n // reversed w 1 5 ∧ reversed w 4 5} = n * (n + 1) * (n + 1) := by
  let word : Fin n × Fin (n + 1) × Fin (n + 1) → Word n := fun t => tuple t.2.1 (translate (width := 1) t.1 0) (translate (width := 1) t.1 1) t.2.2 (translate (width := 1) t.1 0) (translate (width := 1) t.1 1) (translate (width := 1) t.1 0)
  let e : {w : Word n // reversed w 1 5 ∧ reversed w 4 5} ≃ Fin n × Fin (n + 1) × Fin (n + 1) := {
    toFun := fun w => (⟨(w.1 1).val, by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      have hb := (w.1 2).isLt
      omega⟩, w.1 0, w.1 3)
    invFun := fun t => ⟨word t, by simp [word, tuple, translate, reversed]⟩
    left_inv := fun w => by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      apply Subtype.ext
      funext j
      fin_cases j <;> simp [word, tuple, translate, Fin.ext_iff] <;> omega
    right_inv := fun _ => rfl }
  simpa only [Nat.card_fin, Nat.card_prod, mul_assoc] using Nat.card_congr e

private theorem count2534 (n : ℕ) :
    Nat.card {w : Word n // reversed w 2 5 ∧ reversed w 3 4} = (n - 1) * (n + 1) * (n + 1) := by
  let word : Fin (n - 1) × Fin (n + 1) × Fin (n + 1) → Word n := fun t => tuple t.2.1 t.2.2 (translate (width := 2) t.1 0) (translate (width := 2) t.1 1) (translate (width := 2) t.1 2) (translate (width := 2) t.1 1) (translate (width := 2) t.1 0)
  let e : {w : Word n // reversed w 2 5 ∧ reversed w 3 4} ≃ Fin (n - 1) × Fin (n + 1) × Fin (n + 1) := {
    toFun := fun w => (⟨(w.1 2).val, by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      have hb := (w.1 4).isLt
      omega⟩, w.1 0, w.1 1)
    invFun := fun t => ⟨word t, by simp [word, tuple, translate, reversed]⟩
    left_inv := fun w => by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      apply Subtype.ext
      funext j
      fin_cases j <;> simp [word, tuple, translate, Fin.ext_iff] <;> omega
    right_inv := fun _ => rfl }
  simpa only [Nat.card_fin, Nat.card_prod, mul_assoc] using Nat.card_congr e

private theorem count010323 (n : ℕ) :
    Nat.card {w : Word n // reversed w 0 1 ∧ reversed w 0 3 ∧ reversed w 2 3} = n * (n + 1) * (n + 1) := by
  let word : Fin n × Fin (n + 1) × Fin (n + 1) → Word n := fun t => tuple (translate (width := 1) t.1 0) (translate (width := 1) t.1 1) (translate (width := 1) t.1 0) (translate (width := 1) t.1 1) (translate (width := 1) t.1 0) t.2.1 t.2.2
  let e : {w : Word n // reversed w 0 1 ∧ reversed w 0 3 ∧ reversed w 2 3} ≃ Fin n × Fin (n + 1) × Fin (n + 1) := {
    toFun := fun w => (⟨(w.1 0).val, by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      have hb := (w.1 1).isLt
      omega⟩, w.1 5, w.1 6)
    invFun := fun t => ⟨word t, by simp [word, tuple, translate, reversed]⟩
    left_inv := fun w => by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      apply Subtype.ext
      funext j
      fin_cases j <;> simp [word, tuple, translate, Fin.ext_iff] <;> omega
    right_inv := fun _ => rfl }
  simpa only [Nat.card_fin, Nat.card_prod, mul_assoc] using Nat.card_congr e

private theorem count010424 (n : ℕ) :
    Nat.card {w : Word n // reversed w 0 1 ∧ reversed w 0 4 ∧ reversed w 2 4} = n * (n + 1) := by
  let word : Fin n × Fin (n + 1) → Word n := fun t => tuple (translate (width := 1) t.1 0) (translate (width := 1) t.1 1) (translate (width := 1) t.1 0) (translate (width := 1) t.1 1) (translate (width := 1) t.1 1) (translate (width := 1) t.1 0) t.2
  let e : {w : Word n // reversed w 0 1 ∧ reversed w 0 4 ∧ reversed w 2 4} ≃ Fin n × Fin (n + 1) := {
    toFun := fun w => (⟨(w.1 0).val, by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      have hb := (w.1 1).isLt
      omega⟩, w.1 6)
    invFun := fun t => ⟨word t, by simp [word, tuple, translate, reversed]⟩
    left_inv := fun w => by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      apply Subtype.ext
      funext j
      fin_cases j <;> simp [word, tuple, translate, Fin.ext_iff] <;> omega
    right_inv := fun _ => rfl }
  simpa only [Nat.card_fin, Nat.card_prod, mul_assoc] using Nat.card_congr e

private theorem count010434 (n : ℕ) :
    Nat.card {w : Word n // reversed w 0 1 ∧ reversed w 0 4 ∧ reversed w 3 4} = n * (n + 1) := by
  let word : Fin n × Fin (n + 1) → Word n := fun t => tuple (translate (width := 1) t.1 0) (translate (width := 1) t.1 1) (translate (width := 1) t.1 0) (translate (width := 1) t.1 0) (translate (width := 1) t.1 1) (translate (width := 1) t.1 0) t.2
  let e : {w : Word n // reversed w 0 1 ∧ reversed w 0 4 ∧ reversed w 3 4} ≃ Fin n × Fin (n + 1) := {
    toFun := fun w => (⟨(w.1 0).val, by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      have hb := (w.1 1).isLt
      omega⟩, w.1 6)
    invFun := fun t => ⟨word t, by simp [word, tuple, translate, reversed]⟩
    left_inv := fun w => by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      apply Subtype.ext
      funext j
      fin_cases j <;> simp [word, tuple, translate, Fin.ext_iff] <;> omega
    right_inv := fun _ => rfl }
  simpa only [Nat.card_fin, Nat.card_prod, mul_assoc] using Nat.card_congr e

private theorem count010525 (n : ℕ) :
    Nat.card {w : Word n // reversed w 0 1 ∧ reversed w 0 5 ∧ reversed w 2 5} = n * (n + 1) := by
  let word : Fin n × Fin (n + 1) → Word n := fun t => tuple (translate (width := 1) t.1 0) (translate (width := 1) t.1 1) (translate (width := 1) t.1 0) (translate (width := 1) t.1 1) t.2 (translate (width := 1) t.1 1) (translate (width := 1) t.1 0)
  let e : {w : Word n // reversed w 0 1 ∧ reversed w 0 5 ∧ reversed w 2 5} ≃ Fin n × Fin (n + 1) := {
    toFun := fun w => (⟨(w.1 0).val, by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      have hb := (w.1 1).isLt
      omega⟩, w.1 4)
    invFun := fun t => ⟨word t, by simp [word, tuple, translate, reversed]⟩
    left_inv := fun w => by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      apply Subtype.ext
      funext j
      fin_cases j <;> simp [word, tuple, translate, Fin.ext_iff] <;> omega
    right_inv := fun _ => rfl }
  simpa only [Nat.card_fin, Nat.card_prod, mul_assoc] using Nat.card_congr e

private theorem count010535 (n : ℕ) :
    Nat.card {w : Word n // reversed w 0 1 ∧ reversed w 0 5 ∧ reversed w 3 5} = n := by
  let word : Fin n → Word n := fun t => tuple (translate (width := 1) t 0) (translate (width := 1) t 1) (translate (width := 1) t 0) (translate (width := 1) t 0) (translate (width := 1) t 1) (translate (width := 1) t 1) (translate (width := 1) t 0)
  let e : {w : Word n // reversed w 0 1 ∧ reversed w 0 5 ∧ reversed w 3 5} ≃ Fin n := {
    toFun := fun w => ⟨(w.1 0).val, by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      have hb := (w.1 1).isLt
      omega⟩
    invFun := fun t => ⟨word t, by simp [word, tuple, translate, reversed]⟩
    left_inv := fun w => by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      apply Subtype.ext
      funext j
      fin_cases j <;> simp [word, tuple, translate, Fin.ext_iff] <;> omega
    right_inv := fun _ => rfl }
  simpa only [Nat.card_fin] using Nat.card_congr e

private theorem count010545 (n : ℕ) :
    Nat.card {w : Word n // reversed w 0 1 ∧ reversed w 0 5 ∧ reversed w 4 5} = n * (n + 1) := by
  let word : Fin n × Fin (n + 1) → Word n := fun t => tuple (translate (width := 1) t.1 0) (translate (width := 1) t.1 1) (translate (width := 1) t.1 0) t.2 (translate (width := 1) t.1 0) (translate (width := 1) t.1 1) (translate (width := 1) t.1 0)
  let e : {w : Word n // reversed w 0 1 ∧ reversed w 0 5 ∧ reversed w 4 5} ≃ Fin n × Fin (n + 1) := {
    toFun := fun w => (⟨(w.1 0).val, by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      have hb := (w.1 1).isLt
      omega⟩, w.1 3)
    invFun := fun t => ⟨word t, by simp [word, tuple, translate, reversed]⟩
    left_inv := fun w => by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      apply Subtype.ext
      funext j
      fin_cases j <;> simp [word, tuple, translate, Fin.ext_iff] <;> omega
    right_inv := fun _ => rfl }
  simpa only [Nat.card_fin, Nat.card_prod, mul_assoc] using Nat.card_congr e

private theorem count020434 (n : ℕ) :
    Nat.card {w : Word n // reversed w 0 2 ∧ reversed w 0 4 ∧ reversed w 3 4} = n * (n + 1) := by
  let word : Fin n × Fin (n + 1) → Word n := fun t => tuple (translate (width := 1) t.1 0) (translate (width := 1) t.1 1) (translate (width := 1) t.1 1) (translate (width := 1) t.1 0) (translate (width := 1) t.1 1) (translate (width := 1) t.1 0) t.2
  let e : {w : Word n // reversed w 0 2 ∧ reversed w 0 4 ∧ reversed w 3 4} ≃ Fin n × Fin (n + 1) := {
    toFun := fun w => (⟨(w.1 0).val, by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      have hb := (w.1 1).isLt
      omega⟩, w.1 6)
    invFun := fun t => ⟨word t, by simp [word, tuple, translate, reversed]⟩
    left_inv := fun w => by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      apply Subtype.ext
      funext j
      fin_cases j <;> simp [word, tuple, translate, Fin.ext_iff] <;> omega
    right_inv := fun _ => rfl }
  simpa only [Nat.card_fin, Nat.card_prod, mul_assoc] using Nat.card_congr e

private theorem count020545 (n : ℕ) :
    Nat.card {w : Word n // reversed w 0 2 ∧ reversed w 0 5 ∧ reversed w 4 5} = n := by
  let word : Fin n → Word n := fun t => tuple (translate (width := 1) t 0) (translate (width := 1) t 1) (translate (width := 1) t 1) (translate (width := 1) t 0) (translate (width := 1) t 0) (translate (width := 1) t 1) (translate (width := 1) t 0)
  let e : {w : Word n // reversed w 0 2 ∧ reversed w 0 5 ∧ reversed w 4 5} ≃ Fin n := {
    toFun := fun w => ⟨(w.1 0).val, by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      have hb := (w.1 1).isLt
      omega⟩
    invFun := fun t => ⟨word t, by simp [word, tuple, translate, reversed]⟩
    left_inv := fun w => by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      apply Subtype.ext
      funext j
      fin_cases j <;> simp [word, tuple, translate, Fin.ext_iff] <;> omega
    right_inv := fun _ => rfl }
  simpa only [Nat.card_fin] using Nat.card_congr e

private theorem count030545 (n : ℕ) :
    Nat.card {w : Word n // reversed w 0 3 ∧ reversed w 0 5 ∧ reversed w 4 5} = n * (n + 1) := by
  let word : Fin n × Fin (n + 1) → Word n := fun t => tuple (translate (width := 1) t.1 0) (translate (width := 1) t.1 1) t.2 (translate (width := 1) t.1 1) (translate (width := 1) t.1 0) (translate (width := 1) t.1 1) (translate (width := 1) t.1 0)
  let e : {w : Word n // reversed w 0 3 ∧ reversed w 0 5 ∧ reversed w 4 5} ≃ Fin n × Fin (n + 1) := {
    toFun := fun w => (⟨(w.1 0).val, by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      have hb := (w.1 1).isLt
      omega⟩, w.1 2)
    invFun := fun t => ⟨word t, by simp [word, tuple, translate, reversed]⟩
    left_inv := fun w => by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      apply Subtype.ext
      funext j
      fin_cases j <;> simp [word, tuple, translate, Fin.ext_iff] <;> omega
    right_inv := fun _ => rfl }
  simpa only [Nat.card_fin, Nat.card_prod, mul_assoc] using Nat.card_congr e

private theorem count051423 (n : ℕ) :
    Nat.card {w : Word n // reversed w 0 5 ∧ reversed w 1 4 ∧ reversed w 2 3} = (n - 2) := by
  let word : Fin (n - 2) → Word n := fun t => tuple (translate (width := 3) t 0) (translate (width := 3) t 1) (translate (width := 3) t 2) (translate (width := 3) t 3) (translate (width := 3) t 2) (translate (width := 3) t 1) (translate (width := 3) t 0)
  let e : {w : Word n // reversed w 0 5 ∧ reversed w 1 4 ∧ reversed w 2 3} ≃ Fin (n - 2) := {
    toFun := fun w => ⟨(w.1 0).val, by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      have hb := (w.1 3).isLt
      omega⟩
    invFun := fun t => ⟨word t, by simp [word, tuple, translate, reversed]⟩
    left_inv := fun w => by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      apply Subtype.ext
      funext j
      fin_cases j <;> simp [word, tuple, translate, Fin.ext_iff] <;> omega
    right_inv := fun _ => rfl }
  simpa only [Nat.card_fin] using Nat.card_congr e

private theorem count121434 (n : ℕ) :
    Nat.card {w : Word n // reversed w 1 2 ∧ reversed w 1 4 ∧ reversed w 3 4} = n * (n + 1) * (n + 1) := by
  let word : Fin n × Fin (n + 1) × Fin (n + 1) → Word n := fun t => tuple t.2.1 (translate (width := 1) t.1 0) (translate (width := 1) t.1 1) (translate (width := 1) t.1 0) (translate (width := 1) t.1 1) (translate (width := 1) t.1 0) t.2.2
  let e : {w : Word n // reversed w 1 2 ∧ reversed w 1 4 ∧ reversed w 3 4} ≃ Fin n × Fin (n + 1) × Fin (n + 1) := {
    toFun := fun w => (⟨(w.1 1).val, by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      have hb := (w.1 2).isLt
      omega⟩, w.1 0, w.1 6)
    invFun := fun t => ⟨word t, by simp [word, tuple, translate, reversed]⟩
    left_inv := fun w => by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      apply Subtype.ext
      funext j
      fin_cases j <;> simp [word, tuple, translate, Fin.ext_iff] <;> omega
    right_inv := fun _ => rfl }
  simpa only [Nat.card_fin, Nat.card_prod, mul_assoc] using Nat.card_congr e

private theorem count121535 (n : ℕ) :
    Nat.card {w : Word n // reversed w 1 2 ∧ reversed w 1 5 ∧ reversed w 3 5} = n * (n + 1) := by
  let word : Fin n × Fin (n + 1) → Word n := fun t => tuple t.2 (translate (width := 1) t.1 0) (translate (width := 1) t.1 1) (translate (width := 1) t.1 0) (translate (width := 1) t.1 1) (translate (width := 1) t.1 1) (translate (width := 1) t.1 0)
  let e : {w : Word n // reversed w 1 2 ∧ reversed w 1 5 ∧ reversed w 3 5} ≃ Fin n × Fin (n + 1) := {
    toFun := fun w => (⟨(w.1 1).val, by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      have hb := (w.1 2).isLt
      omega⟩, w.1 0)
    invFun := fun t => ⟨word t, by simp [word, tuple, translate, reversed]⟩
    left_inv := fun w => by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      apply Subtype.ext
      funext j
      fin_cases j <;> simp [word, tuple, translate, Fin.ext_iff] <;> omega
    right_inv := fun _ => rfl }
  simpa only [Nat.card_fin, Nat.card_prod, mul_assoc] using Nat.card_congr e

private theorem count121545 (n : ℕ) :
    Nat.card {w : Word n // reversed w 1 2 ∧ reversed w 1 5 ∧ reversed w 4 5} = n * (n + 1) := by
  let word : Fin n × Fin (n + 1) → Word n := fun t => tuple t.2 (translate (width := 1) t.1 0) (translate (width := 1) t.1 1) (translate (width := 1) t.1 0) (translate (width := 1) t.1 0) (translate (width := 1) t.1 1) (translate (width := 1) t.1 0)
  let e : {w : Word n // reversed w 1 2 ∧ reversed w 1 5 ∧ reversed w 4 5} ≃ Fin n × Fin (n + 1) := {
    toFun := fun w => (⟨(w.1 1).val, by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      have hb := (w.1 2).isLt
      omega⟩, w.1 0)
    invFun := fun t => ⟨word t, by simp [word, tuple, translate, reversed]⟩
    left_inv := fun w => by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      apply Subtype.ext
      funext j
      fin_cases j <;> simp [word, tuple, translate, Fin.ext_iff] <;> omega
    right_inv := fun _ => rfl }
  simpa only [Nat.card_fin, Nat.card_prod, mul_assoc] using Nat.card_congr e

private theorem count131545 (n : ℕ) :
    Nat.card {w : Word n // reversed w 1 3 ∧ reversed w 1 5 ∧ reversed w 4 5} = n * (n + 1) := by
  let word : Fin n × Fin (n + 1) → Word n := fun t => tuple t.2 (translate (width := 1) t.1 0) (translate (width := 1) t.1 1) (translate (width := 1) t.1 1) (translate (width := 1) t.1 0) (translate (width := 1) t.1 1) (translate (width := 1) t.1 0)
  let e : {w : Word n // reversed w 1 3 ∧ reversed w 1 5 ∧ reversed w 4 5} ≃ Fin n × Fin (n + 1) := {
    toFun := fun w => (⟨(w.1 1).val, by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      have hb := (w.1 2).isLt
      omega⟩, w.1 0)
    invFun := fun t => ⟨word t, by simp [word, tuple, translate, reversed]⟩
    left_inv := fun w => by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      apply Subtype.ext
      funext j
      fin_cases j <;> simp [word, tuple, translate, Fin.ext_iff] <;> omega
    right_inv := fun _ => rfl }
  simpa only [Nat.card_fin, Nat.card_prod, mul_assoc] using Nat.card_congr e

private theorem count232545 (n : ℕ) :
    Nat.card {w : Word n // reversed w 2 3 ∧ reversed w 2 5 ∧ reversed w 4 5} = n * (n + 1) * (n + 1) := by
  let word : Fin n × Fin (n + 1) × Fin (n + 1) → Word n := fun t => tuple t.2.1 t.2.2 (translate (width := 1) t.1 0) (translate (width := 1) t.1 1) (translate (width := 1) t.1 0) (translate (width := 1) t.1 1) (translate (width := 1) t.1 0)
  let e : {w : Word n // reversed w 2 3 ∧ reversed w 2 5 ∧ reversed w 4 5} ≃ Fin n × Fin (n + 1) × Fin (n + 1) := {
    toFun := fun w => (⟨(w.1 2).val, by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      have hb := (w.1 3).isLt
      omega⟩, w.1 0, w.1 1)
    invFun := fun t => ⟨word t, by simp [word, tuple, translate, reversed]⟩
    left_inv := fun w => by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      apply Subtype.ext
      funext j
      fin_cases j <;> simp [word, tuple, translate, Fin.ext_iff] <;> omega
    right_inv := fun _ => rfl }
  simpa only [Nat.card_fin, Nat.card_prod, mul_assoc] using Nat.card_congr e

private theorem count01052534 (n : ℕ) :
    Nat.card {w : Word n // reversed w 0 1 ∧ reversed w 0 5 ∧ reversed w 2 5 ∧ reversed w 3 4} = (n - 1) := by
  let word : Fin (n - 1) → Word n := fun t => tuple (translate (width := 2) t 0) (translate (width := 2) t 1) (translate (width := 2) t 0) (translate (width := 2) t 1) (translate (width := 2) t 2) (translate (width := 2) t 1) (translate (width := 2) t 0)
  let e : {w : Word n // reversed w 0 1 ∧ reversed w 0 5 ∧ reversed w 2 5 ∧ reversed w 3 4} ≃ Fin (n - 1) := {
    toFun := fun w => ⟨(w.1 0).val, by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      have hb := (w.1 4).isLt
      omega⟩
    invFun := fun t => ⟨word t, by simp [word, tuple, translate, reversed]⟩
    left_inv := fun w => by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      apply Subtype.ext
      funext j
      fin_cases j <;> simp [word, tuple, translate, Fin.ext_iff] <;> omega
    right_inv := fun _ => rfl }
  simpa only [Nat.card_fin] using Nat.card_congr e

private theorem count03051245 (n : ℕ) :
    Nat.card {w : Word n // reversed w 0 3 ∧ reversed w 0 5 ∧ reversed w 1 2 ∧ reversed w 4 5} = (n - 1) := by
  let word : Fin (n - 1) → Word n := fun t => tuple (translate (width := 2) t 0) (translate (width := 2) t 1) (translate (width := 2) t 2) (translate (width := 2) t 1) (translate (width := 2) t 0) (translate (width := 2) t 1) (translate (width := 2) t 0)
  let e : {w : Word n // reversed w 0 3 ∧ reversed w 0 5 ∧ reversed w 1 2 ∧ reversed w 4 5} ≃ Fin (n - 1) := {
    toFun := fun w => ⟨(w.1 0).val, by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      have hb := (w.1 2).isLt
      omega⟩
    invFun := fun t => ⟨word t, by simp [word, tuple, translate, reversed]⟩
    left_inv := fun w => by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      apply Subtype.ext
      funext j
      fin_cases j <;> simp [word, tuple, translate, Fin.ext_iff] <;> omega
    right_inv := fun _ => rfl }
  simpa only [Nat.card_fin] using Nat.card_congr e

private theorem count05121434 (n : ℕ) :
    Nat.card {w : Word n // reversed w 0 5 ∧ reversed w 1 2 ∧ reversed w 1 4 ∧ reversed w 3 4} = (n - 1) := by
  let word : Fin (n - 1) → Word n := fun t => tuple (translate (width := 2) t 0) (translate (width := 2) t 1) (translate (width := 2) t 2) (translate (width := 2) t 1) (translate (width := 2) t 2) (translate (width := 2) t 1) (translate (width := 2) t 0)
  let e : {w : Word n // reversed w 0 5 ∧ reversed w 1 2 ∧ reversed w 1 4 ∧ reversed w 3 4} ≃ Fin (n - 1) := {
    toFun := fun w => ⟨(w.1 0).val, by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      have hb := (w.1 2).isLt
      omega⟩
    invFun := fun t => ⟨word t, by simp [word, tuple, translate, reversed]⟩
    left_inv := fun w => by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      apply Subtype.ext
      funext j
      fin_cases j <;> simp [word, tuple, translate, Fin.ext_iff] <;> omega
    right_inv := fun _ => rfl }
  simpa only [Nat.card_fin] using Nat.card_congr e

private theorem count010305232545 (n : ℕ) :
    Nat.card {w : Word n // reversed w 0 1 ∧ reversed w 0 3 ∧ reversed w 0 5 ∧ reversed w 2 3 ∧ reversed w 2 5 ∧ reversed w 4 5} = n := by
  let word : Fin n → Word n := fun t => tuple (translate (width := 1) t 0) (translate (width := 1) t 1) (translate (width := 1) t 0) (translate (width := 1) t 1) (translate (width := 1) t 0) (translate (width := 1) t 1) (translate (width := 1) t 0)
  let e : {w : Word n // reversed w 0 1 ∧ reversed w 0 3 ∧ reversed w 0 5 ∧ reversed w 2 3 ∧ reversed w 2 5 ∧ reversed w 4 5} ≃ Fin n := {
    toFun := fun w => ⟨(w.1 0).val, by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      have hb := (w.1 1).isLt
      omega⟩
    invFun := fun t => ⟨word t, by simp [word, tuple, translate, reversed]⟩
    left_inv := fun w => by
      have h := w.2
      simp [reversed, Fin.ext_iff] at h
      apply Subtype.ext
      funext j
      fin_cases j <;> simp [word, tuple, translate, Fin.ext_iff] <;> omega
    right_inv := fun _ => rfl }
  simpa only [Nat.card_fin] using Nat.card_congr e

open scoped BigOperators

private theorem sum_ind {ι : Type*} [Fintype ι] (p : ι → Prop) :
    (∑ x, ind (p x)) = (Nat.card {x // p x} : ℤ) := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  exact Finset.sum_boole p _

private def poly (x : ℤ) : ℤ :=
  x ^ 7 + 7 * x ^ 6 + 16 * x ^ 5 + 5 * x ^ 4 - 7 * x ^ 3 + 18 * x ^ 2 - 5 * x - 5

set_option maxHeartbeats 2000000 in
private theorem a_at_all (n : ℕ) : a n = if n = 0 then 0 else if n = 1 then 29 else poly n := by
  by_cases hn : n = 0
  · simp [hn, a]
  simp only [if_neg hn]
  have h := Finset.sum_congr (s₁ := (Finset.univ : Finset (Word n))) rfl
    (fun w _ => indicators w)
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, sum_ind,
    count01, count02, count03, count04, count05, count12,
    count13, count14, count15, count23, count24, count25,
    count34, count35, count45, count0104, count0105, count0134,
    count0135, count0145, count0205, count0245, count0312, count0412,
    count0413, count0423, count0434, count0512, count0513, count0514,
    count0523, count0524, count0534, count0535, count0545, count1215,
    count1245, count1423, count1523, count1524, count1534, count1545,
    count2534, count010323, count010424, count010434, count010525, count010535,
    count010545, count020434, count020545, count030545, count051423, count121434,
    count121535, count121545, count131545, count232545, count01052534, count03051245,
    count05121434, count010305232545,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, Fintype.card_fun,
    Fintype.card_fin] at h
  rw [a, if_neg hn]
  change (Nat.card {w : Word n // valid w} : ℤ) = _
  rw [h]
  by_cases h1 : n = 1
  · subst n
    norm_num
  simp only [if_neg h1]
  push_cast [Int.ofNat_sub (show 1 ≤ n by omega), Int.ofNat_sub (show 2 ≤ n by omega)]
  unfold poly
  ring

private theorem a_poly (n : ℕ) (h : 2 ≤ n) : a n = poly n := by
  rw [a_at_all, if_neg (show n ≠ 0 by omega), if_neg (show n ≠ 1 by omega)]

private theorem recurrence (n : ℕ) (hn : 9 < n) :
    a n = 8 * a (n - 1) - 28 * a (n - 2) + 56 * a (n - 3) -
      70 * a (n - 4) + 56 * a (n - 5) - 28 * a (n - 6) + 8 * a (n - 7) - a (n - 8) := by
  rw [a_poly n (by omega), a_poly (n - 1) (by omega), a_poly (n - 2) (by omega),
    a_poly (n - 3) (by omega), a_poly (n - 4) (by omega), a_poly (n - 5) (by omega),
    a_poly (n - 6) (by omega), a_poly (n - 7) (by omega), a_poly (n - 8) (by omega)]
  simp only [Int.natCast_sub (show 1 ≤ n by omega),
    Int.natCast_sub (show 2 ≤ n by omega), Int.natCast_sub (show 3 ≤ n by omega),
    Int.natCast_sub (show 4 ≤ n by omega), Int.natCast_sub (show 5 ≤ n by omega),
    Int.natCast_sub (show 6 ≤ n by omega), Int.natCast_sub (show 7 ≤ n by omega),
    Int.natCast_sub (show 8 ≤ n by omega), Nat.cast_ofNat]
  unfold poly
  ring

open PowerSeries

private theorem generating_function :
    (1 - X) ^ 8 * mk a = X *
      (29 + 937 * X + 2996 * X ^ 2 + 1355 * X ^ 3 - 536 * X ^ 4 + 335 * X ^ 5 -
        88 * X ^ 6 + 13 * X ^ 7 - X ^ 8) := by
  have hd : ((1 - X) : PowerSeries ℤ) ^ 8 =
      1 - C 8 * X ^ 1 + C 28 * X ^ 2 - C 56 * X ^ 3 + C 70 * X ^ 4 -
        C 56 * X ^ 5 + C 28 * X ^ 6 - C 8 * X ^ 7 + X ^ 8 := by
    norm_num
    ring
  have hq : X *
      (29 + 937 * X + 2996 * X ^ 2 + 1355 * X ^ 3 - 536 * X ^ 4 + 335 * X ^ 5 -
        88 * X ^ 6 + 13 * X ^ 7 - X ^ 8) =
      (C 29 * X ^ 1 + C 937 * X ^ 2 + C 2996 * X ^ 3 + C 1355 * X ^ 4 -
        C 536 * X ^ 5 + C 335 * X ^ 6 - C 88 * X ^ 7 + C 13 * X ^ 8 - X ^ 9 :
        PowerSeries ℤ) := by
    norm_num
    ring
  rw [hd, hq]
  ext n
  simp only [sub_mul, add_mul, one_mul, mul_assoc, map_add, map_sub,
    coeff_C_mul, coeff_X_pow_mul', coeff_mk, coeff_X_pow]
  by_cases hn : n < 10
  · interval_cases n <;> norm_num [a_at_all, poly]
  · simp only [if_pos (show 1 ≤ n by omega), if_pos (show 2 ≤ n by omega),
      if_pos (show 3 ≤ n by omega), if_pos (show 4 ≤ n by omega),
      if_pos (show 5 ≤ n by omega), if_pos (show 6 ≤ n by omega),
      if_pos (show 7 ≤ n by omega), if_pos (show 8 ≤ n by omega),
      if_neg (show n ≠ 1 by omega), if_neg (show n ≠ 2 by omega),
      if_neg (show n ≠ 3 by omega), if_neg (show n ≠ 4 by omega),
      if_neg (show n ≠ 5 by omega), if_neg (show n ≠ 6 by omega),
      if_neg (show n ≠ 7 by omega), if_neg (show n ≠ 8 by omega),
      if_neg (show n ≠ 9 by omega), mul_zero, add_zero, sub_zero]
    have hr := recurrence n (by omega)
    omega

end A268461Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a268461.main :=
  ⟨A268461Proof.generating_function, A268461Proof.recurrence⟩
