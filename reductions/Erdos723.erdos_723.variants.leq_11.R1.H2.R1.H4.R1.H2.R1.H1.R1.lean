import OMAReductions.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R1_H4_R1_H2_R1
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.List.Basic

/-! Classify the pair-only intersections of the six five-secants. -/
-- Credit: @LordMike
-- Port of reductions/Erdos723.erdos_723.variants.leq_11.R1.H2.R2.H4.R1.H2.R1.H1.R1.lean by @avivorly (PR #3086) onto the identical hypothesis statement Erdos723.erdos_723.variants.leq_11.R1.H2.R1.H4.R1.H2.R1.H1.
namespace OMA.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R1_H4_R1_H2_R1_H1_R1

def H1 : Prop :=
  ∀ A : Fin 6 → Fin 19 → Bool,
    (∀ a, (Finset.univ.filter fun p => A a p = true).card = 5) →
    (∀ p, (Finset.univ.filter fun a => A a p = true).card ≤ 2) →
    (∀ p q, p ≠ q →
      ((Finset.univ.filter fun a => A a p = true) ∩ (Finset.univ.filter fun a => A a q = true)).card ≤ 1) →
    ∃ w < 2^15,
      let P : List (Fin 6 × Fin 6) := [(0,1), (0,2), (0,3), (0,4), (0,5), (1,2), (1,3), (1,4), (1,5), (2,3), (2,4), (2,5), (3,4), (3,5), (4,5)]
      (∀ i : Fin 15, w.testBit i.val = true ↔
        ∃ p, A (P[i.val]!).1 p = true ∧ A (P[i.val]!).2 p = true) ∧
      ∃ r ∈ ([0x7ff, 0xfdf, 0xfff, 0x16ff, 0x177f, 0x17fe, 0x17ff, 0x19ff, 0x1bbf, 0x1bfe, 0x1bff, 0x1fdd, 0x1fdf, 0x1fff, 0x3dfe, 0x3dff, 0x3fff, 0x7fff] : List Nat), ∃ m,
        let f (i : Nat) := ((m >>> (3*i)) &&& 7) % 6
        ((List.range 6).map f).Nodup ∧
        ((P.zipIdx.map fun ((a,b),i) =>
          if w.testBit i then
            let x := min (f a.val) (f b.val)
            let y := max (f a.val) (f b.val)
            2^(x*(11-x)/2 + (y-x-1))
          else 0).foldr Nat.lor 0) = r

def H2 : Prop :=
  let R := Fin 6 ⊕ (Fin 37 ⊕ Fin 68)
  let P := Fin 19 ⊕ Fin 92
  let A (M : R → P → Bool) (p : P) :=
    (Finset.univ.filter fun a : Fin 6 => M (.inl a) p = true).card
  let B (M : R → P → Bool) (p : P) :=
    (Finset.univ.filter fun b : Fin 37 => M (.inr (.inl b)) p = true).card
  ¬ ∃ M : R → P → Bool,
    (∀ l, (Finset.univ.filter fun p => M l p = true).card = 11) ∧
    (∀ p, (Finset.univ.filter fun l => M l p = true).card = 11) ∧
    (∀ l m, l ≠ m → ∃! p, M l p = true ∧ M m p = true) ∧
    (∀ p q, p ≠ q → ∃! l, M l p = true ∧ M l q = true) ∧
    (∀ a : Fin 6, (Finset.univ.filter fun p : Fin 19 => M (.inl a) (.inl p) = true).card = 5) ∧
    (∀ b : Fin 37, (Finset.univ.filter fun p : Fin 19 => M (.inr (.inl b)) (.inl p) = true).card = 3) ∧
    (∀ c : Fin 68, (Finset.univ.filter fun p : Fin 19 => M (.inr (.inr c)) (.inl p) = true).card = 1) ∧
    (∀ p : Fin 19, B M (.inl p) + 2*A M (.inl p) = 9) ∧
    (∀ p : Fin 92, B M (.inr p) + 2*A M (.inr p) = 4) ∧
    (∀ p : Fin 19, A M (.inl p) ≤ 2) ∧
    let A0 (a : Fin 6) (p : Fin 19) := M (.inl a) (.inl p)
    ∃ w < 2^15,
      let P : List (Fin 6 × Fin 6) := [(0,1), (0,2), (0,3), (0,4), (0,5), (1,2), (1,3), (1,4), (1,5), (2,3), (2,4), (2,5), (3,4), (3,5), (4,5)]
      (∀ i : Fin 15, w.testBit i.val = true ↔
        ∃ p, A0 (P[i.val]!).1 p = true ∧ A0 (P[i.val]!).2 p = true) ∧
      ∃ r ∈ ([0x7ff, 0xfdf, 0xfff, 0x16ff, 0x177f, 0x17fe, 0x17ff, 0x19ff, 0x1bbf, 0x1bfe, 0x1bff, 0x1fdd, 0x1fdf, 0x1fff, 0x3dfe, 0x3dff, 0x3fff, 0x7fff] : List Nat), ∃ m,
        let f (i : Nat) := ((m >>> (3*i)) &&& 7) % 6
        ((List.range 6).map f).Nodup ∧
        ((P.zipIdx.map fun ((a,b),i) =>
          if w.testBit i then
            let x := min (f a.val) (f b.val)
            let y := max (f a.val) (f b.val)
            2^(x*(11-x)/2 + (y-x-1))
          else 0).foldr Nat.lor 0) = r

theorem main : H1 → H2 → OMA.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R1_H4_R1_H2_R1.H1 := by
  intro classify impossible
  unfold OMA.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R1_H4_R1_H2_R1.H1
  dsimp only
  rintro ⟨M,rowSizes,colSizes,rowPairs,colPairs,aSizes,bSizes,cSizes,inside,outside,max_two⟩
  let A (a : Fin 6) (p : Fin 19) := M (.inl a) (.inl p)
  have overlaps (p q : Fin 19) (different : p ≠ q) :
      ((Finset.univ.filter fun a => A a p = true) ∩
        (Finset.univ.filter fun a => A a q = true)).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro a ha b hb
    have present (v : Fin 6)
        (hv : v ∈ (Finset.univ.filter fun a => A a p = true) ∩
          (Finset.univ.filter fun a => A a q = true)) : A v p = true ∧ A v q = true := by
      obtain ⟨hp,hq⟩ := Finset.mem_inter.mp hv
      exact ⟨(Finset.mem_filter.mp hp).2,(Finset.mem_filter.mp hq).2⟩
    obtain ⟨_,_,unique⟩ := colPairs (.inl p) (.inl q) (fun eq => different (Sum.inl.inj eq))
    exact Sum.inl.inj ((unique (.inl a) (present a ha)).trans (unique (.inl b) (present b hb)).symm)
  have found := classify A aSizes max_two overlaps
  exact impossible ⟨M,rowSizes,colSizes,rowPairs,colPairs,aSizes,bSizes,cSizes,inside,outside,max_two,found⟩

end OMA.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R1_H4_R1_H2_R1_H1_R1

