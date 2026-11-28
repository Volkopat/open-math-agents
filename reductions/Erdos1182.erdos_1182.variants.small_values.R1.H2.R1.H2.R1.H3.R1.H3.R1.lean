import OMAReductions.R_Erdos1182_erdos_1182_variants_small_values_R1_H2_R1_H2_R1_H3_R1
import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

-- Credit: @Ehdunhackme


namespace Problem14.DensitySplit
open SimpleGraph

/-- Independent obstruction families for an exhaustive set of base-density
    ranges can be concatenated, adding the fixed triangle-free base host. -/
theorem combine (n h k q : ℕ) (encode : ℕ → SimpleGraph (Fin h))
    (base : SimpleGraph (Fin h)) (baseMask : ℕ)
    (base_eq : encode baseMask = base) (base_triangle : base.CliqueFree 3)
    (P : Fin k → ℕ → Prop) (exhaustive : ∀ m, ∃ i, P i m)
    (children : ∀ i : Fin k, ∃ (r : ℕ) (masks : Fin r → ℕ),
      (∀ a, (encode (masks a)).CliqueFree 3) ∧
      ∀ (f0 : Fin n ↪ Fin h) (f : Fin r → Fin n ↪ Fin h),
        let B := baseᶜ.comap f0
        let D := B ⊓ ⨅ a, (encode (masks a))ᶜ.comap (f a)
        P i B.edgeSet.ncard → D.Connected → D.edgeSet.ncard ≤ q) :
    ∃ (r : ℕ) (masks : Fin r → ℕ),
      (∀ a, (encode (masks a)).CliqueFree 3) ∧
      ∀ f : Fin r → Fin n ↪ Fin h,
        let D := ⨅ a, (encode (masks a))ᶜ.comap (f a)
        D.Connected → D.edgeSet.ncard ≤ q := by
  classical
  choose r masks good using children
  let J := Unit ⊕ Σ i : Fin k, Fin (r i)
  let e : J ≃ Fin (Fintype.card J) := Fintype.equivFin J
  let M : J → ℕ := Sum.elim (fun _ => baseMask) (fun ij => masks ij.1 ij.2)
  refine ⟨Fintype.card J, M ∘ e.symm, ?_, ?_⟩
  · intro a
    change (encode (M (e.symm a))).CliqueFree 3
    cases he : e.symm a with
    | inl u => simpa only [he, M, Sum.elim_inl, base_eq] using base_triangle
    | inr ij => simpa only [he, M, Sum.elim_inr] using (good ij.1).1 ij.2
  · intro f
    let G := ⨅ a, (encode (M (e.symm a)))ᶜ.comap (f a)
    change G.Connected → G.edgeSet.ncard ≤ q
    intro hG
    let f0 := f (e (Sum.inl ()))
    let B := baseᶜ.comap f0
    have hGB : G ≤ B := by
      have hh := iInf_le (fun a => (encode (M (e.symm a)))ᶜ.comap (f a)) (e (Sum.inl ()))
      simpa only [G, B, f0, Equiv.symm_apply_apply, M, Sum.elim_inl, base_eq] using hh
    obtain ⟨i, hi⟩ := exhaustive B.edgeSet.ncard
    let fi : Fin (r i) → Fin n ↪ Fin h := fun j => f (e (Sum.inr ⟨i,j⟩))
    let Gi := B ⊓ ⨅ j, (encode (masks i j))ᶜ.comap (fi j)
    have hGGi : G ≤ Gi := by
      apply le_inf hGB
      apply le_iInf
      intro j
      have hh := iInf_le (fun a => (encode (M (e.symm a)))ᶜ.comap (f a))
        (e (Sum.inr ⟨i,j⟩))
      simpa only [G, fi, Equiv.symm_apply_apply, M, Sum.elim_inr] using hh
    have hb : Gi.edgeSet.ncard ≤ q :=
      (good i).2 f0 fi hi (SimpleGraph.Connected.mono hGGi hG)
    exact (Set.ncard_le_ncard (SimpleGraph.edgeSet_mono hGGi)).trans hb

theorem cycle5_blowup_triangleFree (h : ℕ) :
    ((cycleGraph 5).comap (fun v : Fin h =>
      (⟨v.val % 5, Nat.mod_lt _ (by decide)⟩ : Fin 5))).CliqueFree 3 := by
  have htf : ∀ i j k : Fin 5, (cycleGraph 5).Adj i j →
      (cycleGraph 5).Adj i k → ¬ (cycleGraph 5).Adj j k := by decide +kernel
  intro S hS
  obtain ⟨x,y,z,hxy,hxz,hyz,_⟩ := SimpleGraph.is3Clique_iff.mp hS
  exact htf _ _ _ hxy hxz hyz

end Problem14.DensitySplit
namespace OMA.R_Erdos1182_erdos_1182_variants_small_values_R1_H2_R1_H2_R1_H3_R1_H3_R1
open SimpleGraph

def H1 : Prop :=
  ∃ (r : ℕ) (masks : Fin r → ℕ),
    let C (a : Fin r) : SimpleGraph (Fin 23) :=
      { Adj := fun i j => i ≠ j ∧ (masks a).testBit ((min i j).val*23+(max i j).val) = true
        symm := ⟨fun i j v => ⟨v.1.symm,by simpa [min_comm j i,max_comm j i] using v.2⟩⟩
        loopless := ⟨by simp⟩ }
    (∀ a, (C a).CliqueFree 3) ∧
    ∀ (f0 : Fin 12 ↪ Fin 23) (f : Fin r → Fin 12 ↪ Fin 23),
      let B := ((SimpleGraph.cycleGraph 5).comap (fun v : Fin 23 => (⟨v.val % 5, Nat.mod_lt _ (by decide)⟩ : Fin 5)))ᶜ.comap f0
      let D := B ⊓ ⨅ a, (C a)ᶜ.comap (f a)
      (B.edgeSet.ncard ≤ 51) → D.Connected → D.edgeSet.ncard ≤ 49

def H2 : Prop :=
  ∃ (r : ℕ) (masks : Fin r → ℕ),
    let C (a : Fin r) : SimpleGraph (Fin 23) :=
      { Adj := fun i j => i ≠ j ∧ (masks a).testBit ((min i j).val*23+(max i j).val) = true
        symm := ⟨fun i j v => ⟨v.1.symm,by simpa [min_comm j i,max_comm j i] using v.2⟩⟩
        loopless := ⟨by simp⟩ }
    (∀ a, (C a).CliqueFree 3) ∧
    ∀ (f0 : Fin 12 ↪ Fin 23) (f : Fin r → Fin 12 ↪ Fin 23),
      let B := ((SimpleGraph.cycleGraph 5).comap (fun v : Fin 23 => (⟨v.val % 5, Nat.mod_lt _ (by decide)⟩ : Fin 5)))ᶜ.comap f0
      let D := B ⊓ ⨅ a, (C a)ᶜ.comap (f a)
      (52 ≤ B.edgeSet.ncard ∧ B.edgeSet.ncard ≤ 54) → D.Connected → D.edgeSet.ncard ≤ 49

def H3 : Prop :=
  ∃ (r : ℕ) (masks : Fin r → ℕ),
    let C (a : Fin r) : SimpleGraph (Fin 23) :=
      { Adj := fun i j => i ≠ j ∧ (masks a).testBit ((min i j).val*23+(max i j).val) = true
        symm := ⟨fun i j v => ⟨v.1.symm,by simpa [min_comm j i,max_comm j i] using v.2⟩⟩
        loopless := ⟨by simp⟩ }
    (∀ a, (C a).CliqueFree 3) ∧
    ∀ (f0 : Fin 12 ↪ Fin 23) (f : Fin r → Fin 12 ↪ Fin 23),
      let B := ((SimpleGraph.cycleGraph 5).comap (fun v : Fin 23 => (⟨v.val % 5, Nat.mod_lt _ (by decide)⟩ : Fin 5)))ᶜ.comap f0
      let D := B ⊓ ⨅ a, (C a)ᶜ.comap (f a)
      (B.edgeSet.ncard = 55) → D.Connected → D.edgeSet.ncard ≤ 49

def H4 : Prop :=
  ∃ (r : ℕ) (masks : Fin r → ℕ),
    let C (a : Fin r) : SimpleGraph (Fin 23) :=
      { Adj := fun i j => i ≠ j ∧ (masks a).testBit ((min i j).val*23+(max i j).val) = true
        symm := ⟨fun i j v => ⟨v.1.symm,by simpa [min_comm j i,max_comm j i] using v.2⟩⟩
        loopless := ⟨by simp⟩ }
    (∀ a, (C a).CliqueFree 3) ∧
    ∀ (f0 : Fin 12 ↪ Fin 23) (f : Fin r → Fin 12 ↪ Fin 23),
      let B := ((SimpleGraph.cycleGraph 5).comap (fun v : Fin 23 => (⟨v.val % 5, Nat.mod_lt _ (by decide)⟩ : Fin 5)))ᶜ.comap f0
      let D := B ⊓ ⨅ a, (C a)ᶜ.comap (f a)
      (56 ≤ B.edgeSet.ncard) → D.Connected → D.edgeSet.ncard ≤ 49

theorem main : H1 → H2 → H3 → H4 → OMA.R_Erdos1182_erdos_1182_variants_small_values_R1_H2_R1_H2_R1_H3_R1.H3 := by
  intro h1 h2 h3 h4
  let encode : ℕ → SimpleGraph (Fin 23) := fun mask =>
      { Adj := fun i j => i ≠ j ∧ (mask).testBit ((min i j).val*23+(max i j).val) = true
        symm := ⟨fun i j v => ⟨v.1.symm,by simpa [min_comm j i,max_comm j i] using v.2⟩⟩
        loopless := ⟨by simp⟩ }
  let base : SimpleGraph (Fin 23) := (SimpleGraph.cycleGraph 5).comap (fun v : Fin 23 => (⟨v.val % 5, Nat.mod_lt _ (by decide)⟩ : Fin 5))
  have heq : encode 104748505696174012614033004642281303050133616916139286786987393701035100998493430711500720089665727525596909321493949503782742040903767463089440213781074 = base := by
    have hf : ∀ i j : Fin 23,
        (i ≠ j ∧ (104748505696174012614033004642281303050133616916139286786987393701035100998493430711500720089665727525596909321493949503782742040903767463089440213781074 : ℕ).testBit ((min i j).val*23+(max i j).val) = true) ↔
        (SimpleGraph.cycleGraph 5).Adj
          (⟨i.val % 5, Nat.mod_lt _ (by decide)⟩ : Fin 5)
          (⟨j.val % 5, Nat.mod_lt _ (by decide)⟩ : Fin 5) := by decide +kernel
    ext i j
    exact hf i j
  apply Problem14.DensitySplit.combine 12 23 4 49 encode base 104748505696174012614033004642281303050133616916139286786987393701035100998493430711500720089665727525596909321493949503782742040903767463089440213781074 heq
    (Problem14.DensitySplit.cycle5_blowup_triangleFree 23) (![fun m => m ≤ 51,fun m => 52 ≤ m ∧ m ≤ 54,fun m => m = 55,fun m => 56 ≤ m])
  · intro m
    by_cases h : m ≤ 51
    · exact ⟨0,h⟩
    by_cases h' : m ≤ 54
    · exact ⟨1,by change 52 ≤ m ∧ m ≤ 54; omega⟩
    by_cases he : m = 55
    · exact ⟨2,he⟩
    exact ⟨3,by change 56 ≤ m; omega⟩
  · intro i
    fin_cases i
    · exact h1
    · exact h2
    · exact h3
    · exact h4

end OMA.R_Erdos1182_erdos_1182_variants_small_values_R1_H2_R1_H2_R1_H3_R1_H3_R1
