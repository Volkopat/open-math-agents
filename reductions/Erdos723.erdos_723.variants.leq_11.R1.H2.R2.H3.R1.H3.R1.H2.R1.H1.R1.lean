import OMAReductions.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2_H3_R1_H3_R1_H2_R1
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Bitwise

namespace OMA.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2_H3_R1_H3_R1_H2_R1_H1_R1

private def isPerfectMatching (L : Finset (Fin 111)) (M : Finset (Finset (Fin 111))) : Prop :=
  M.card = 3 ∧ (∀ e ∈ M, e ⊆ L ∧ e.card = 2) ∧
    ∀ l ∈ L, ∃! e, e ∈ M ∧ l ∈ e

private def isExteriorLabel (L : Finset (Fin 111)) (C : Finset (Finset (Finset (Fin 111)))) : Prop :=
  C.card = 2 ∧ (∀ M ∈ C, isPerfectMatching L M) ∧
    ∀ M ∈ C, ∀ N ∈ C, M ≠ N → Disjoint M N

private def HasStarCover : Prop :=
  ∃ L : Finset (Fin 111), L.card = 6 ∧
    ∃ stars : ↥(L.powersetCard 2) → Fin 6 → Finset (Finset (Finset (Finset (Fin 111)))),
      (∀ e i C, C ∈ stars e i → isExteriorLabel L C ∧ ∀ M ∈ C, e.val ∉ M) ∧
      (∀ e i M, isPerfectMatching L M → e.val ∉ M → ∃! C, C ∈ stars e i ∧ M ∈ C) ∧
      (∀ e C, isExteriorLabel L C → (∀ M ∈ C, e.val ∉ M) → ∃! i, C ∈ stars e i) ∧
      ∀ e f, e ≠ f → ∀ i j, (stars e i ∩ stars f j).card ≤ 1

private def PackedCover : Prop :=
  (
    let allowed (g : Fin 15) (p : Fin 60) := (0xfffc3ef80fafa00f3bbfb03bed00eeaeefc0bef00bdbdcf43b5efe00e7db781eef77db7007715f55fdd75f5f003c3740d75d7ddf5d5c1dd01e7d77fa4b5ea76c0beee5fa2a83ababebbbaf00cccf3cf3f3f3f033333cf3cfcfcffc003cf3cf3f3f3ffffc0000fcfcfcfffffffff000000:Nat).testBit (60 * g.val + p.val) = true
    let required (g m : Fin 15) := (0x1fedbef6efdbf6f77bf5bff76df7edf6fdf6df8fffe3fff8fffe3fff8:Nat).testBit (15 * g.val + m.val) = true
    let endpoint (p : Fin 60) (m : Fin 15) := (0x5000600220014008400880208011000a000c01040108011000a0202020401080110201020200840088005000604020404040804100220014200410081010082008400888008801040202040208011000a000c80044008401040201040108011000a400240042008201020202040108011:Nat).testBit (15 * p.val + m.val) = true
    ∃ s : Fin 15 → Fin 6 → Finset (Fin 60),
      (∀ g i p,p ∈ s g i → allowed g p) ∧
      (∀ g i m,required g m → ∃! p, p ∈ s g i ∧ endpoint p m) ∧
      (∀ g p,allowed g p → ∃! i, p ∈ s g i) ∧
      ∀ g h i j, g ≠ h → (s g i ∩ s h j).card ≤ 1)

private def allowed (g : Fin 15) (p : Fin 60) := (0xfffc3ef80fafa00f3bbfb03bed00eeaeefc0bef00bdbdcf43b5efe00e7db781eef77db7007715f55fdd75f5f003c3740d75d7ddf5d5c1dd01e7d77fa4b5ea76c0beee5fa2a83ababebbbaf00cccf3cf3f3f3f033333cf3cfcfcffc003cf3cf3f3f3ffffc0000fcfcfcfffffffff000000:Nat).testBit (60 * g.val + p.val) = true

private def required (g m : Fin 15) := (0x1fedbef6efdbf6f77bf5bff76df7edf6fdf6df8fffe3fff8fffe3fff8:Nat).testBit (15 * g.val + m.val) = true

private def endpoint (p : Fin 60) (m : Fin 15) := (0x5000600220014008400880208011000a000c01040108011000a0202020401080110201020200840088005000604020404040804100220014200410081010082008400888008801040202040208011000a000c80044008401040201040108011000a400240042008201020202040108011:Nat).testBit (15 * p.val + m.val) = true

private def catalogueBase : Finset (Fin 111) := ([0,1,2,3,4,5] : List (Fin 111)).toFinset

private def HasPackingCatalogue : Prop :=
  ∃ (medium : Fin 15 → Finset (Finset (Fin 111)))
    (exterior : Fin 60 → Finset (Finset (Finset (Fin 111))))
    (group : Fin 15 → ↥(catalogueBase.powersetCard 2)),
    Function.Injective group ∧ Function.Injective exterior ∧
    (∀ C, isExteriorLabel catalogueBase C → ∃ p, exterior p = C) ∧
    (∀ m, isPerfectMatching catalogueBase (medium m)) ∧
    (∀ p, isExteriorLabel catalogueBase (exterior p)) ∧
    (∀ g p, allowed g p ↔ ∀ m ∈ exterior p, (group g).val ∉ m) ∧
    (∀ g m, required g m ↔ (group g).val ∉ medium m) ∧
    (∀ p m, endpoint p m ↔ medium m ∈ exterior p)

def H1 : Prop := HasPackingCatalogue

def H2 : Prop := HasPackingCatalogue → HasStarCover → PackedCover

theorem main : H1 → H2 → OMA.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2_H3_R1_H3_R1_H2_R1.H1 := by
  intro catalogue transfer
  exact transfer catalogue

end OMA.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2_H3_R1_H3_R1_H2_R1_H1_R1
