import OMAStatements.S_mo_206961
import Mathlib

open OMA.S_mo_206961
open Equiv

abbrev MoA4 := ↥(alternatingGroup (Fin 4))

def mo206961_ord (g : MoA4) : ℕ := if g = 1 then 1 else if g ^ 2 = 1 then 2 else 3

def mo206961_prods' : List MoA4 → Multiset MoA4
  | [] => {1}
  | g :: L => (Multiset.range (mo206961_ord g)).bind
      (fun k => (mo206961_prods' L).map (fun y => g ^ k * y))

lemma mo206961_key : ∀ g : MoA4, g ^ 2 = 1 ∨ g ^ 3 = 1 := by decide

lemma mo206961_ord_eq (g : MoA4) : orderOf g = mo206961_ord g := by
  unfold mo206961_ord
  split_ifs with h1 h2
  · simp [h1]
  · exact orderOf_eq_prime h2 h1
  · have h3 : g ^ 3 = 1 := (mo206961_key g).resolve_left h2
    have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    exact orderOf_eq_prime h3 h1

lemma mo206961_prods_eq : ∀ L : List MoA4, prods L = mo206961_prods' L := by
  intro L
  induction L with
  | nil => rfl
  | cons g L ih => simp only [prods, mo206961_prods', ih, mo206961_ord_eq]

def mo206961_e (σ : Perm (Fin 4)) (h : σ ∈ alternatingGroup (Fin 4)) : MoA4 := ⟨σ, h⟩

def mo206961_l : List MoA4 :=
  [1,
   mo206961_e ⟨![0, 2, 3, 1], ![0, 3, 1, 2], by decide, by decide⟩ (Perm.mem_alternatingGroup.2 (by decide)),
   mo206961_e ⟨![0, 3, 1, 2], ![0, 2, 3, 1], by decide, by decide⟩ (Perm.mem_alternatingGroup.2 (by decide)),
   mo206961_e ⟨![1, 0, 3, 2], ![1, 0, 3, 2], by decide, by decide⟩ (Perm.mem_alternatingGroup.2 (by decide)),
   mo206961_e ⟨![1, 2, 0, 3], ![2, 0, 1, 3], by decide, by decide⟩ (Perm.mem_alternatingGroup.2 (by decide)),
   mo206961_e ⟨![1, 3, 2, 0], ![3, 0, 2, 1], by decide, by decide⟩ (Perm.mem_alternatingGroup.2 (by decide)),
   mo206961_e ⟨![2, 0, 1, 3], ![1, 2, 0, 3], by decide, by decide⟩ (Perm.mem_alternatingGroup.2 (by decide)),
   mo206961_e ⟨![2, 1, 3, 0], ![3, 1, 0, 2], by decide, by decide⟩ (Perm.mem_alternatingGroup.2 (by decide)),
   mo206961_e ⟨![2, 3, 0, 1], ![2, 3, 0, 1], by decide, by decide⟩ (Perm.mem_alternatingGroup.2 (by decide)),
   mo206961_e ⟨![3, 0, 2, 1], ![1, 3, 2, 0], by decide, by decide⟩ (Perm.mem_alternatingGroup.2 (by decide)),
   mo206961_e ⟨![3, 1, 0, 2], ![2, 1, 3, 0], by decide, by decide⟩ (Perm.mem_alternatingGroup.2 (by decide)),
   mo206961_e ⟨![3, 2, 1, 0], ![3, 2, 1, 0], by decide, by decide⟩ (Perm.mem_alternatingGroup.2 (by decide))]

lemma mo206961_nodup : mo206961_l.Nodup := by decide

lemma mo206961_all : ∀ g : MoA4, g ∈ mo206961_l := by decide

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_206961.main) := by
  intro h
  have := h MoA4 mo206961_l mo206961_nodup mo206961_all 1
    (mo206961_e ⟨![1, 0, 3, 2], ![1, 0, 3, 2], by decide, by decide⟩ (Perm.mem_alternatingGroup.2 (by decide)))
  rw [mo206961_prods_eq] at this
  revert this
  decide +kernel
