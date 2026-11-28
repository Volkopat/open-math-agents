import OMAStatements.S_erdos_278
import Mathlib

/-! Formalization of the minimum cover theorem for finite residue systems. A prime-power CRT product realizes the classes as boxes. Aligning their centers one coordinate at a time can only decrease the union. The minimum-density theorem of Rogers appears in Halberstam and Roth, Sequences (1966), Chapter V, Section 3. See also R. J. Simpson, Exact coverings of the integers by arithmetic progressions (1986), and Erdős problem 278. -/


namespace Deldor14.CongruenceBoxes
open Finset
open scoped BigOperators
private theorem nestedUnion {J X : Type*} [DecidableEq X] (I : Finset J)
    (L R : J → Finset X) (nested : ∀ a b, L a ⊆ L b ∨ L b ⊆ L a)
    (size : ∀ a, (L a).card=(R a).card) :
    (I.biUnion L).card ≤ (I.biUnion R).card := by
  classical
  obtain e|ne := I.eq_empty_or_nonempty
  · simp [e]
  obtain ⟨j,hj,top⟩ := I.exists_max_image (fun i => (L i).card) ne
  have le : I.biUnion L ⊆ L j := by
    intro x hx
    obtain ⟨i,hi,xi⟩ := mem_biUnion.mp hx
    rcases nested i j with h|h
    · exact h xi
    · exact (eq_of_subset_of_card_le h (top i hi)).symm ▸ xi
  exact (card_le_card le).trans ((size j).le.trans (card_le_card (subset_biUnion_of_mem R hj)))

noncomputable def count {J D : Type*} [Fintype D] {X : D → Type*} [∀ i,Fintype (X i)]
    (I : Finset J) (B : ∀ i, J → Finset (X i)) : ℕ := by
  classical
  exact (univ.filter (fun x : ∀ i, X i => ∃ j ∈ I, ∀ i, x i ∈ B i j)).card

open Classical in
private theorem slice {J D : Type*} [Fintype D] {X : D → Type*} [∀ i,Fintype (X i)]
    (I : Finset J) (B : ∀ i, J → Finset (X i)) (t : D) :
    count I B = ∑ y : (∀ i : {j : D // j≠t}, X i),
      ((I.filter (fun j => ∀ i : {v : D // v ≠ t}, y i ∈ B i j)).biUnion (B t)).card := by
  classical
  rw [count,card_filter]
  let E := Equiv.piSplitAt t X
  let V (w : X t × (∀ i : {j : D // j≠t}, X i)) : ℕ :=
    if w.1 ∈ (I.filter (fun j => ∀ i : {v : D // v ≠ t}, w.2 i ∈ B i j)).biUnion (B t) then 1 else 0
  calc
   _ = ∑ w, V w := by
     apply Fintype.sum_equiv E
     intro x
     dsimp [V,E,Equiv.piSplitAt]
     congr 1
     apply propext
     simp only [mem_biUnion,mem_filter]
     constructor
     · rintro ⟨j,hj,all⟩
       exact ⟨j,⟨hj,fun i => all i⟩,all t⟩
     · rintro ⟨j,⟨hj,sub⟩,ht⟩
       refine ⟨j,hj,fun i => ?_⟩
       by_cases e : i=t
       · subst i; exact ht
       · exact sub ⟨i,e⟩
   _ = _ := by
     rw [Fintype.sum_prod_type_right]
     apply sum_congr rfl
     intro y _
     dsimp [V]
     rw [← card_filter]
     congr 1
     ext x
     simp only [mem_filter,mem_univ,true_and]

theorem compression {J D : Type*} [Fintype D] {X : D → Type*} [∀ i,Fintype (X i)]
    (I : Finset J) (L R : ∀ i, J → Finset (X i))
    (nested : ∀ i a b, L i a ⊆ L i b ∨ L i b ⊆ L i a)
    (size : ∀ i a, (L i a).card=(R i a).card) : count I L ≤ count I R := by
  classical
  let B (T : Finset D) (i : D) := if i ∈ T then L i else R i
  have cmp (T : Finset D) : count I (B T) ≤ count I R := by
    induction T using Finset.induction_on with
    | empty => simp [B]
    | @insert t T ht ih =>
      refine le_trans ?_ ih
      rw [slice I _ t,slice I (B T) t]
      apply sum_le_sum
      intro y _
      have outside (j : J) (i : {i : D // i≠t}) : B (insert t T) i j = B T i j := by simp [B,i.property]
      simp only [outside]
      have a : B (insert t T) t=L t := by simp [B]
      have b : B T t=R t := by simp [B,ht]
      rw [a,b]
      apply nestedUnion _ _ _ (nested t) (size t)
  simpa [B] using cmp univ

end Deldor14.CongruenceBoxes

namespace Deldor14.CongruenceArithmetic
open Finset
open Deldor14.CongruenceBoxes

private noncomputable def box (q d : ℕ) [NeZero q] (h : d ∣ q) (a : ℤ) : Finset (ZMod q) := by
  classical
  exact univ.filter (fun x => ZMod.castHom h (ZMod d) x = (a:ZMod d))
private theorem inbox {q d : ℕ} [NeZero q] (h : d ∣ q) (a x : ℤ) :
    (x:ZMod q) ∈ box q d h a ↔ x ≡ a [ZMOD (d:ℤ)] := by
  classical
  simp only [box,mem_filter,mem_univ,true_and,map_intCast]
  exact ZMod.intCast_eq_intCast_iff ..
private theorem size {q d : ℕ} [NeZero q] (h : d ∣ q) (a b : ℤ) :
    (box q d h a).card=(box q d h b).card := by
  classical
  apply card_equiv (Equiv.addRight ((b-a:ℤ):ZMod q))
  intro x
  obtain ⟨v,rfl⟩ := ZMod.intCast_surjective x
  change (v:ZMod q) ∈ _ ↔ (v:ZMod q)+((b-a:ℤ):ZMod q) ∈ _
  rw [← Int.cast_add,inbox,inbox]
  simp only [Int.modEq_iff_dvd]
  ring_nf
private theorem subset {q d e : ℕ} [NeZero q] (hd : d ∣ q) (he : e ∣ q) (h : d ∣ e) (a : ℤ) :
    box q e he a ⊆ box q d hd a := by
  intro x hx
  obtain ⟨v,rfl⟩ := ZMod.intCast_surjective x
  exact (inbox hd a v).mpr (((inbox he a v).mp hx).of_dvd (by exact_mod_cast h))

private theorem local_iff {L n : ℕ} (hl : L≠0) (hn : n≠0) (dvd : n∣L) (x a : ℤ) :
    x ≡ a [ZMOD (n:ℤ)] ↔
      ∀ p : L.primeFactors, x ≡ a [ZMOD (((p:ℕ)^n.factorization p:ℕ):ℤ)] := by
  constructor
  · intro h p
    apply h.of_dvd
    exact_mod_cast Nat.ordProj_dvd n p.val
  · intro h
    apply (ZMod.intCast_eq_intCast_iff ..).mp
    apply (ZMod.equivPi n hn).injective
    funext p
    change (ZMod.equivPi n hn (x:ZMod n)) p = (ZMod.equivPi n hn (a:ZMod n)) p
    rw [map_intCast,map_intCast]
    exact (ZMod.intCast_eq_intCast_iff ..).mpr (h ⟨p.val,Nat.primeFactors_mono dvd hl p.property⟩)

private theorem finCast (n : ℕ) [NeZero n] (v : Fin n) : ZMod.finEquiv n v=(v.val:ZMod n) := by
  cases n with
  | zero => exact Fin.elim0 v
  | succ n => exact (ZMod.natCast_zmod_val (n:=n+1) v).symm

theorem result : type_of% @OMA.S_erdos_278.main := by
  classical
  intro A hn a c
  let L := A.lcm id
  have nz : L≠0 := Finset.lcm_ne_zero_iff.mpr (fun n h => (hn n h).ne')
  letI : NeZero L := ⟨nz⟩
  let D := {p : ℕ // p ∈ L.primeFactors}
  letI : DecidableEq D := Classical.decEq D
  letI (p : D) : NeZero (p.val) := ⟨(Nat.pos_of_mem_primeFactors p.property).ne'⟩
  let q (p : D) := p.val^L.factorization p
  letI (p : D) : NeZero (q p) := ⟨pow_ne_zero _ (NeZero.ne _)⟩
  let J := {n : ℕ // n ∈ A}
  have dvd (n : J) : n.val ∣ L := Finset.dvd_lcm (f:=id) n.property
  let d (p : D) (n : J) := p.val^n.val.factorization p
  have dh (p : D) (n : J) : d p n ∣ q p := Nat.ordProj_dvd_ordProj_of_dvd nz (dvd n) p.val
  let B (g : ℕ → ℤ) (p : D) (n : J) := box (q p) (d p n) (dh p n) (g n.val)
  let E : Fin L ≃ ((p : D) → ZMod (q p)) := (ZMod.finEquiv L).toEquiv.trans (ZMod.equivPi L nz).toEquiv
  have ec (v : Fin L) (p : D) : E v p=((v.val:ℤ):ZMod (q p)) := by
    have f : ZMod.finEquiv L v=(v.val:ZMod L) := finCast L v
    change (ZMod.equivPi L nz (ZMod.finEquiv L v)) p=_
    rw [f,map_natCast]
    simp
  have counting (g : ℕ → ℤ) :
      ((range L).filter (fun x : ℕ => ∃ n ∈ A, (x:ℤ) ≡ g n [ZMOD (n:ℤ)])).card =
        count (univ : Finset J) (B g) := by
    rw [count,card_filter,card_filter,← Fin.sum_univ_eq_sum_range]
    apply Fintype.sum_equiv E
    intro v
    congr 1
    apply propext
    simp only [mem_univ,true_and]
    constructor
    · rintro ⟨n,hn',hx⟩
      let j : J := ⟨n,hn'⟩
      refine ⟨j,fun p => ?_⟩
      rw [ec]
      exact (inbox (dh p j) _ _).mpr ((local_iff nz (hn n hn').ne' (dvd j) v.val (g n)).mp hx p)
    · rintro ⟨n,hx⟩
      refine ⟨n.val,n.property,(local_iff nz (hn n.val n.property).ne' (dvd n) v.val _).mpr ?_⟩
      intro p
      have hh := hx p
      rw [ec] at hh
      exact (inbox (dh p n) _ _).mp hh
  have cmp := compression (univ : Finset J) (B (fun _ => c)) (B a) (by
    intro p i j
    rcases le_total (i.val.factorization p) (j.val.factorization p) with h|h
    · exact Or.inr (subset _ _ (pow_dvd_pow _ h) c)
    · exact Or.inl (subset _ _ (pow_dvd_pow _ h) c)) (fun p j => size _ c (a j.val))
  rw [← counting (fun _ => c),← counting a] at cmp
  unfold OMA.S_erdos_278.coveredDensity
  exact div_le_div_of_nonneg_right (by exact_mod_cast cmp) (by positivity)
end Deldor14.CongruenceArithmetic

theorem OMA.solution : type_of% @OMA.S_erdos_278.main := Deldor14.CongruenceArithmetic.result
