import OMAReductions.R_Erdos1162_erdos_1162_variants_roney_dougal_tracey_R1_H2_R2_H1_R1

/-!
Subgroups of a finite nilpotent group are determined by their intersections
with its Sylow subgroups. Faithful permutation actions on those factors
then give the required prime-local subgroup counts.

The degree budget is used in the proof of Theorem 3 of Roney-Dougal and
Tracey, *Subgroups of symmetric groups: enumeration and asymptotic
properties*, https://arxiv.org/html/2503.05416#S7.
-/

namespace OMA.R_Erdos1162_erdos_1162_variants_roney_dougal_tracey_R1_H2_R2_H1_R1_H2_R1

open Finset
open scoped BigOperators

/-- A subgroup of a finite nilpotent group is determined by its Sylow intersections. -/
def H1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Group.IsNilpotent G →
    ∀ P : (p : (Nat.card G).primeFactors) → Sylow p G,
    Function.Injective (fun H : Subgroup G => fun p => H.comap (P p).1.subtype)

/-- Faithful actions of the Sylow factors using at most the original degree in total. -/
def H2 : Prop :=
  ∀ n : ℕ, ∀ D : Subgroup (Equiv.Perm (Fin n)), Group.IsNilpotent D →
    ∀ P : (p : (Nat.card D).primeFactors) → Sylow p D, ∃ m : ℕ → ℕ,
      (∀ p ∈ (Nat.card D).primeFactors, p ≤ m p) ∧
      (∑ p ∈ (Nat.card D).primeFactors, m p) ≤ n ∧
      ∀ p, ∃ f : P p →* Equiv.Perm (Fin (m p)), Function.Injective f

theorem main : H1 → H2 →
    OMA.R_Erdos1162_erdos_1162_variants_roney_dougal_tracey_R1_H2_R2_H1_R1.H2 := by
  classical
  intro intersections degrees n D hD
  let S := (Nat.card D).primeFactors
  let P (p : S) : Sylow p D := default
  obtain ⟨m, hm, hSum, hActions⟩ := degrees n D hD P
  let act (p : S) := (hActions p).choose
  have hAct (p : S) : Function.Injective (act p) := (hActions p).choose_spec
  let T (p : ℕ) := {K : Subgroup (Equiv.Perm (Fin (m p))) // IsPGroup p K}
  let encode (H : Subgroup D) (p : S) : T p :=
    ⟨(H.comap (P p).1.subtype).map (act p),
      ((P p).isPGroup'.to_subgroup _).map (act p)⟩
  have hEncode : Function.Injective encode := by
    intro H K h
    apply intersections D hD P
    funext p
    apply Subgroup.map_injective (hAct p)
    exact congrArg Subtype.val (congrFun h p)
  refine ⟨S, m, fun p hp => ⟨Nat.prime_of_mem_primeFactors hp, hm p hp⟩, hSum, ?_⟩
  calc
    _ ≤ Nat.card (∀ p : S, T p) := Nat.card_le_card_of_injective encode hEncode
    _ = ∏ p : S, Nat.card (T p) := Nat.card_pi
    _ = _ := Finset.prod_finset_coe (fun p => Nat.card (T p)) S

end OMA.R_Erdos1162_erdos_1162_variants_roney_dougal_tracey_R1_H2_R2_H1_R1_H2_R1
