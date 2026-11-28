import OMAReductions.R_Erdos723_erdos_723_variants_eq_12_R1_H1_R1
import Mathlib

/-! Extend the order-12 partial plane at each of the three stated sizes. -/

/- A size obstruction to alternating values and nontrivial closed classes of cliques. -/

open Finset

namespace PlaneCliqueCount

variable {V : Type} [DecidableEq V]

private theorem ten_from_intersections (K : Finset (Finset V)) (C : Finset V) (hC : 10 ≤ C.card)
    (h : ∀ x ∈ C, ∃ D ∈ K, C ∩ D = {x}) : 10 ≤ K.card := by
  classical
  choose D hD he using h
  let g := fun x : V => if hx : x ∈ C then D x hx else ∅
  refine hC.trans (card_le_card_of_injOn g ?_ ?_)
  · intro x hx
    change x ∈ C at hx
    rw [show g x = D x hx by simp [g,hx]]
    exact hD x hx
  · intro x hx y hy hxy
    change x ∈ C at hx
    change y ∈ C at hy
    simp only [g,dif_pos hx,dif_pos hy] at hxy
    have h := congrArg (fun E => C ∩ E) hxy
    rw [he x hx,he y hy] at h
    exact singleton_inj.mp h

private theorem large_disjoint_impossible {K K₁ K₂ : Finset (Finset V)} (hK : K.card ≤ 19)
    (h₁ : K₁ ⊆ K) (h₂ : K₂ ⊆ K) (hd : Disjoint K₁ K₂)
    (hc₁ : 10 ≤ K₁.card) (hc₂ : 10 ≤ K₂.card) : False := by
  have h := card_le_card (union_subset h₁ h₂)
  rw [card_union_of_disjoint hd] at h
  omega

theorem alternating_vanish (K : Finset (Finset V)) (hK : K.card ≤ 19)
    (hmin : ∀ C ∈ K, 10 ≤ C.card)
    (other : ∀ C ∈ K, ∀ x ∈ C, ∃ D ∈ K, D ≠ C ∧ x ∈ D ∧ C ∩ D = {x})
    (f : Finset V → ℤ)
    (halt : ∀ C ∈ K, ∀ D ∈ K, C ≠ D → ∀ x ∈ C, x ∈ D → f C + f D = 0) :
    ∀ C ∈ K, f C = 0 := by
  classical
  intro C hC
  by_contra hne
  obtain ⟨x,hx⟩ := card_pos.mp (by have := hmin C hC; omega : 0 < C.card)
  obtain ⟨D,hD,hdc,hxD,_⟩ := other C hC x hx
  have hh := halt C hC D hD hdc.symm x hx hxD
  have hp : ∃ E ∈ K, 0 < f E := by
    by_cases hf : 0 < f C
    · exact ⟨C,hC,hf⟩
    · exact ⟨D,hD,by omega⟩
  have hn : ∃ E ∈ K, f E < 0 := by
    by_cases hf : f C < 0
    · exact ⟨C,hC,hf⟩
    · exact ⟨D,hD,by omega⟩
  obtain ⟨P,hP,hfp⟩ := hp
  obtain ⟨N,hN,hfn⟩ := hn
  let Kp := K.filter (fun E => 0 < f E)
  let Kn := K.filter (fun E => f E < 0)
  have hkp : 10 ≤ Kp.card := by
    apply ten_from_intersections Kp N (hmin N hN)
    intro y hy
    obtain ⟨E,hE,hen,hyE,hint⟩ := other N hN y hy
    have h := halt N hN E hE hen.symm y hy hyE
    exact ⟨E,mem_filter.mpr ⟨hE,by omega⟩,hint⟩
  have hkn : 10 ≤ Kn.card := by
    apply ten_from_intersections Kn P (hmin P hP)
    intro y hy
    obtain ⟨E,hE,hep,hyE,hint⟩ := other P hP y hy
    have h := halt P hP E hE hep.symm y hy hyE
    exact ⟨E,mem_filter.mpr ⟨hE,by omega⟩,hint⟩
  exact large_disjoint_impossible hK (filter_subset _ _) (filter_subset _ _)
    (disjoint_left.mpr (fun E he hE => lt_asymm (mem_filter.mp he).2 (mem_filter.mp hE).2)) hkp hkn

theorem constant_predicate (K : Finset (Finset V)) (hK : K.card ≤ 19)
    (hmin : ∀ C ∈ K, 10 ≤ C.card)
    (other : ∀ C ∈ K, ∀ x ∈ C, ∃ D ∈ K, D ≠ C ∧ x ∈ D ∧ C ∩ D = {x})
    (P : Finset V → Prop)
    (hsame : ∀ C ∈ K, ∀ D ∈ K, C ≠ D → ∀ x ∈ C, x ∈ D → (P C ↔ P D)) :
    ∀ C ∈ K, ∀ D ∈ K, (P C ↔ P D) := by
  classical
  have forward (C : Finset V) (hC : C ∈ K) (hPC : P C)
      (D : Finset V) (hD : D ∈ K) : P D := by
    by_contra hPD
    let yes := K.filter P
    let no := K.filter (fun E => ¬P E)
    have hy : 10 ≤ yes.card := by
      apply ten_from_intersections yes C (hmin C hC)
      intro x hx
      obtain ⟨E,hE,hec,hxE,hint⟩ := other C hC x hx
      exact ⟨E,mem_filter.mpr ⟨hE,(hsame C hC E hE hec.symm x hx hxE).mp hPC⟩,hint⟩
    have hn : 10 ≤ no.card := by
      apply ten_from_intersections no D (hmin D hD)
      intro x hx
      obtain ⟨E,hE,hed,hxE,hint⟩ := other D hD x hx
      exact ⟨E,mem_filter.mpr ⟨hE,fun he => hPD ((hsame D hD E hE hed.symm x hx hxE).mpr he)⟩,hint⟩
    exact large_disjoint_impossible (K₁ := yes) (K₂ := no) hK (filter_subset _ _) (filter_subset _ _)
      (disjoint_left.mpr (fun E he hE => (show ¬ P E from (mem_filter.mp hE).2) (mem_filter.mp he).2)) hy hn
  intro C hC D hD
  exact ⟨fun hc => forward C hC hc D hD, fun hd => forward D hD hd C hC⟩

end PlaneCliqueCount


/- A bipartition lemma for a triangle-free graph of order 22 and minimum degree nine. -/

open Finset
open scoped BigOperators

namespace PlaneLocalGraph

variable {V : Type}
variable (r : V → V → Prop) [DecidableRel r]

private def nb (A : Finset V) (x : V) : Finset V := A.filter (r x)

private theorem nb_subset (A : Finset V) (x : V) : nb r A x ⊆ A := filter_subset _ _

private theorem mem_nb {A : Finset V} {x y : V} : y ∈ nb r A x ↔ y ∈ A ∧ r x y :=
  mem_filter

private theorem independent_cycle_five : ∀ f : Fin 5 → Bool,
    (∀ i, f i = true → f (i+1) = false) → ((univ.filter fun i => f i = true).card ≤ 2) := by
  decide +kernel

private theorem no_closed_five (A : Finset V) (hA : A.card = 22)
    (rs : ∀ ⦃x y⦄, r x y → r y x)
    (ht : ∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A, r x y → r y z → r z x → False)
    (hd : ∀ x ∈ A, 9 ≤ (nb r A x).card)
    (e : Fin 5 → V) (he : ∀ i, e i ∈ A) (hedge : ∀ i, r (e i) (e (i+1))) : False := by
  have hupper (x : V) (hx : x ∈ A) : ((univ.filter fun i : Fin 5 => r (e i) x).card ≤ 2) := by
    let f := fun i : Fin 5 => decide (r (e i) x)
    have hf (i : Fin 5) (hi : f i = true) : f (i+1) = false := by
      have h1 : r (e i) x := of_decide_eq_true hi
      apply decide_eq_false
      intro h2
      exact ht (e i) (he i) (e (i+1)) (he (i+1)) x hx (hedge i) h2 (rs h1)
    simpa [f] using independent_cycle_five f hf
  have hcount : (∑ i : Fin 5, (nb r A (e i)).card) =
      ∑ x ∈ A, (univ.filter fun i : Fin 5 => r (e i) x).card := by
    simp only [nb, card_filter]
    exact sum_comm
  have hlo : 45 ≤ ∑ i : Fin 5, (nb r A (e i)).card := by
    simpa using (Finset.sum_le_sum (s := (univ : Finset (Fin 5))) (fun i _ => hd (e i) (he i)))
  have hhi : (∑ x ∈ A, (univ.filter fun i : Fin 5 => r (e i) x).card) ≤ 44 := by
    simpa [hA] using (Finset.sum_le_sum (s := A) hupper)
  omega

variable [DecidableEq V]

private theorem nb_bound_erase (A : Finset V) (hr : ∀ x, ¬r x x) {x : V} (hx : x ∈ A) :
    (nb r A x).card + 1 ≤ A.card := by
  have h : nb r A x ⊆ A.erase x := by
    intro y hy
    have hh := (mem_nb r).mp hy
    exact mem_erase.mpr ⟨fun e => hr x (e ▸ hh.2), hh.1⟩
  exact (Nat.add_le_add_right (card_le_card h) 1).trans_eq (card_erase_add_one hx)

private theorem independent_extension (A C D X Y : Finset V)
    (rs : ∀ ⦃x y⦄, r x y → r y x) (ht : ∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A, r x y → r y z → r z x → False)
    (hD : D ⊆ A) (hX : X ⊆ A) (hY : Y ⊆ X)
    (hcard : C.card + D.card + X.card = 22) (hs : X.card ≤ 4) (hCcard : 9 ≤ C.card)
    (hbase : ∀ x ∈ C, ∀ y ∈ C, ¬r x y)
    (hnone : ∀ x ∈ Y, ∀ y ∈ C, ¬r x y)
    (hbig : ∀ x ∈ Y, 10 ≤ (nb r D x).card + X.card) :
    ∀ x ∈ C ∪ Y, ∀ y ∈ C ∪ Y, ¬r x y := by
  intro x hx y hy hxy
  rcases mem_union.mp hx with hx | hx
  · rcases mem_union.mp hy with hy | hy
    · exact hbase x hx y hy hxy
    · exact hnone y hy x hx (rs hxy)
  · rcases mem_union.mp hy with hy | hy
    · exact hnone x hx y hy hxy
    · have hdis : Disjoint (nb r D x) (nb r D y) := by
        apply disjoint_left.mpr
        intro z hz1 hz2
        obtain ⟨hzD, hxz⟩ := (mem_nb r).mp hz1
        obtain ⟨_, hyz⟩ := (mem_nb r).mp hz2
        exact ht x (hX (hY hx)) y (hX (hY hy)) z (hD hzD) hxy hyz (rs hxz)
      have hone := card_le_card (union_subset (nb_subset r D x) (nb_subset r D y))
      rw [card_union_of_disjoint hdis] at hone
      have := hbig x hx
      have := hbig y hy
      omega

theorem bipartition_twenty_two (A : Finset V) (hA : A.card = 22)
    (rs : ∀ ⦃x y⦄, r x y → r y x) (hr : ∀ x, ¬r x x)
    (ht : ∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A, r x y → r y z → r z x → False)
    (hd : ∀ x ∈ A, 9 ≤ (nb r A x).card) :
    ∃ L R : Finset V, L ∪ R = A ∧ Disjoint L R ∧
      (∀ x ∈ L, ∀ y ∈ L, ¬r x y) ∧ (∀ x ∈ R, ∀ y ∈ R, ¬r x y) ∧
      9 ≤ L.card ∧ 9 ≤ R.card := by
  classical
  obtain ⟨u, hu⟩ := card_pos.mp (show 0 < A.card by omega)
  obtain ⟨v, hv⟩ := card_pos.mp (show 0 < (nb r A u).card by have := hd u hu; omega)
  have huv := ((mem_nb r).mp hv).2
  have hvA := nb_subset r A u hv
  let C := nb r A u
  let D := nb r A v
  let X := A \ (C ∪ D)
  have hCa : C ⊆ A := nb_subset r A u
  have hDa : D ⊆ A := nb_subset r A v
  have hXa : X ⊆ A := sdiff_subset
  have hCd : Disjoint C D := disjoint_left.mpr fun z hzC hzD =>
    ht u hu v hvA z (hCa hzC) huv ((mem_nb r).mp hzD).2 (rs ((mem_nb r).mp hzC).2)
  have hC : 9 ≤ C.card := hd u hu
  have hD : 9 ≤ D.card := hd v hvA
  have hsum : C.card + D.card + X.card = 22 := by
    have h := card_sdiff_add_card_eq_card (union_subset hCa hDa)
    change X.card + (C ∪ D).card = A.card at h
    rw [card_union_of_disjoint hCd, hA] at h
    omega
  have hX : X.card ≤ 4 := by omega
  have hbase (s : V) (hs : s ∈ A) : ∀ x ∈ nb r A s, ∀ y ∈ nb r A s, ¬r x y := by
    intro x hx y hy hxy
    obtain ⟨hxA, hsx⟩ := (mem_nb r).mp hx
    obtain ⟨hyA, hsy⟩ := (mem_nb r).mp hy
    exact ht s hs x hxA y hyA hsx hxy (rs hsy)
  have hsplit (x : V) (hx : x ∈ X) :
      (nb r C x).card = 0 ∨ (nb r D x).card = 0 := by
    by_contra! h
    obtain ⟨a, ha⟩ := card_pos.mp (show 0 < (nb r C x).card by omega)
    obtain ⟨b, hb⟩ := card_pos.mp (show 0 < (nb r D x).card by omega)
    obtain ⟨haC, hxa⟩ := (mem_nb r).mp ha
    obtain ⟨hbD, hxb⟩ := (mem_nb r).mp hb
    let e : Fin 5 → V := ![u,v,b,x,a]
    have he (i : Fin 5) : e i ∈ A := by
      fin_cases i
      · simpa [e] using hu
      · simpa [e] using hvA
      · simpa [e] using hDa hbD
      · simpa [e] using hXa hx
      · simpa [e] using hCa haC
    have hedge (i : Fin 5) : r (e i) (e (i+1)) := by
      fin_cases i
      · simpa [e] using huv
      · simpa [e] using ((mem_nb r).mp hbD).2
      · simpa [e] using rs hxb
      · simpa [e] using hxa
      · simpa [e] using rs ((mem_nb r).mp haC).2
    exact no_closed_five r A hA rs ht hd e he hedge
  have hnbTotal (x : V) (hx : x ∈ X) :
      10 ≤ (nb r C x).card + (nb r D x).card + X.card := by
    have he : nb r A x = nb r C x ∪ nb r D x ∪ nb r X x := by
      ext y
      simp only [nb, mem_filter, mem_union, X, mem_sdiff]
      constructor
      · intro h
        by_cases hC : y ∈ C
        · exact Or.inl (Or.inl ⟨hC,h.2⟩)
        · by_cases hD : y ∈ D
          · exact Or.inl (Or.inr ⟨hD,h.2⟩)
          · exact Or.inr ⟨⟨h.1,not_or.mpr ⟨hC,hD⟩⟩,h.2⟩
      · rintro ((h | h) | h)
        · exact ⟨hCa h.1,h.2⟩
        · exact ⟨hDa h.1,h.2⟩
        · exact ⟨h.1.1,h.2⟩
    have hb := nb_bound_erase r X hr hx
    have h1 := hd x (hXa hx)
    have h2 := card_union_le (nb r C x ∪ nb r D x) (nb r X x)
    have h3 := card_union_le (nb r C x) (nb r D x)
    rw [he] at h1
    omega
  let Y := X.filter (fun x => (nb r C x).card = 0)
  let Z := X.filter (fun x => (nb r C x).card ≠ 0)
  have hY : Y ⊆ X := filter_subset _ _
  have hZ : Z ⊆ X := filter_subset _ _
  have hY0 (x : V) (hx : x ∈ Y) : (nb r C x).card = 0 := (mem_filter.mp hx).2
  have hZ0 (x : V) (hx : x ∈ Z) : (nb r D x).card = 0 :=
    (hsplit x (hZ hx)).resolve_left (mem_filter.mp hx).2
  have hYnone (x : V) (hx : x ∈ Y) (y : V) (hy : y ∈ C) : ¬r x y := by
    intro h
    have hc := card_pos.mpr ⟨y, (mem_nb r).mpr ⟨hy,h⟩⟩
    have hz := hY0 x hx
    omega
  have hZnone (x : V) (hx : x ∈ Z) (y : V) (hy : y ∈ D) : ¬r x y := by
    intro h
    have hc := card_pos.mpr ⟨y, (mem_nb r).mpr ⟨hy,h⟩⟩
    have hz := hZ0 x hx
    omega
  refine ⟨C ∪ Y, D ∪ Z, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext x
    simp only [mem_union, Y, Z, X, mem_filter, mem_sdiff]
    constructor
    · rintro ((h | h) | h | h)
      · exact hCa h
      · exact h.1.1
      · exact hDa h
      · exact h.1.1
    · intro h
      by_cases hC : x ∈ C
      · exact Or.inl (Or.inl hC)
      · by_cases hD : x ∈ D
        · exact Or.inr (Or.inl hD)
        · have hXmem : x ∈ A ∧ ¬ (x ∈ C ∨ x ∈ D) := ⟨h, not_or.mpr ⟨hC,hD⟩⟩
          by_cases hz : (nb r C x).card = 0
          · exact Or.inl (Or.inr ⟨hXmem,hz⟩)
          · exact Or.inr (Or.inr ⟨hXmem,hz⟩)
  · apply disjoint_left.mpr
    intro x hx hz
    rcases mem_union.mp hx with hx | hx
    · rcases mem_union.mp hz with hz | hz
      · exact disjoint_left.mp hCd hx hz
      · exact (mem_sdiff.mp (hZ hz)).2 (mem_union.mpr (Or.inl hx))
    · rcases mem_union.mp hz with hz | hz
      · exact (mem_sdiff.mp (hY hx)).2 (mem_union.mpr (Or.inr hz))
      · exact (mem_filter.mp hz).2 (hY0 x hx)
  · apply independent_extension r A C D X Y rs ht hDa hXa hY hsum hX hC (hbase u hu) hYnone
    intro x hx
    simpa [hY0 x hx] using hnbTotal x (hY hx)
  · have hs : D.card + C.card + X.card = 22 := by omega
    apply independent_extension r A D C X Z rs ht hCa hXa hZ hs hX hD (hbase v hvA) hZnone
    intro x hx
    simpa [hZ0 x hx] using hnbTotal x (hZ hx)
  · exact hC.trans (card_le_card subset_union_left)
  · exact hD.trans (card_le_card subset_union_left)


variable {V : Type} [DecidableEq V]
variable (r : V → V → Prop) [DecidableRel r]

private def Clique (A : Finset V) : Prop :=
  ∀ x ∈ A, ∀ y ∈ A, x ≠ y → r x y

private theorem no_three_large_sets (A B C U : Finset V) (hU : U.card = 22)
    (hA : A ⊆ U) (hB : B ⊆ U) (hC : C ⊆ U)
    (a : 11 ≤ A.card) (b : 11 ≤ B.card) (c : 11 ≤ C.card)
    (ab : (A ∩ B).card ≤ 3) (ac : (A ∩ C).card ≤ 3) (bc : (B ∩ C).card ≤ 3) : False := by
  have h1 := card_union_add_card_inter A B
  have h2 := card_union_add_card_inter (A ∪ B) C
  have h3 := card_le_card (union_subset (union_subset hA hB) hC)
  have he : (A ∪ B) ∩ C = (A ∩ C) ∪ (B ∩ C) := by
    ext x
    simp only [mem_inter,mem_union]
    tauto
  have h4 := card_union_le (A ∩ C) (B ∩ C)
  rw [he] at h2
  omega

private theorem two_local_cliques (A : Finset V)
    (rs : ∀ ⦃x y⦄, r x y → r y x) (hr : ∀ x, ¬r x x)
    (hd : ∀ x ∈ A, (nb r A x).card = 22)
    (hcommon : ∀ x ∈ A, ∀ y ∈ A, r x y →
      10 ≤ (nb r A x ∩ nb r A y).card ∧ (nb r A x ∩ nb r A y).card ≤ 12)
    (hapart : ∀ x ∈ A, ∀ y ∈ A, x ≠ y → ¬r x y → (nb r A x ∩ nb r A y).card ≤ 4)
    (x : V) (hx : x ∈ A) :
    ∃ L R : Finset V, L ∪ R = nb r A x ∧ Disjoint L R ∧ 9 ≤ L.card ∧ 9 ≤ R.card ∧
      Clique r (insert x L) ∧ Clique r (insert x R) ∧
      ∀ B ⊆ A, x ∈ B → 10 ≤ B.card → Clique r B →
        B ⊆ insert x L ∨ B ⊆ insert x R := by
  classical
  let N := nb r A x
  let comp : V → V → Prop := fun y z => y ≠ z ∧ ¬ r y z
  have hN : N.card = 22 := hd x hx
  have hNA : N ⊆ A := nb_subset r A x
  have xn : x ∉ N := fun h => hr x ((mem_nb r).mp h).2
  have cSymm : ∀ ⦃u v⦄, comp u v → comp v u := by
    intro u v h
    exact ⟨Ne.symm h.1, fun h' => h.2 (rs h')⟩
  have cIrrefl (u : V) : ¬ comp u u := fun h => h.1 rfl
  have loc (y : V) : nb r N y = N ∩ nb r A y := by
    ext z
    simp only [mem_nb, mem_inter]
    exact ⟨fun h => ⟨h.1,hNA h.1,h.2⟩, fun h => ⟨h.1,h.2.2⟩⟩
  have cdeg (y : V) (hy : y ∈ N) : 9 ≤ (nb comp N y).card := by
    have h := (hcommon x hx y (hNA hy) ((mem_nb r).mp hy).2).2
    change (N ∩ nb r A y).card ≤ 12 at h
    rw [← loc y] at h
    have hsub : nb r N y ⊆ N.erase y := by
      intro z hz
      obtain ⟨hzN, hyz⟩ := (mem_nb r).mp hz
      exact mem_erase.mpr ⟨fun e => hr y (e ▸ hyz),hzN⟩
    have he : nb comp N y = N.erase y \ nb r N y := by
      ext z
      simp only [mem_nb, comp, mem_sdiff, mem_erase]
      aesop
    rw [he, card_sdiff_of_subset hsub]
    have hcc := card_erase_add_one hy
    omega
  let K := fun y : V => insert y (nb r N y)
  have hKs (y : V) (hy : y ∈ N) : K y ⊆ N := by
    intro z hz
    rcases mem_insert.mp hz with rfl | h
    · exact hy
    · exact nb_subset r N y h
  have hKl (y : V) (hy : y ∈ N) : 11 ≤ (K y).card := by
    have h := (hcommon x hx y (hNA hy) ((mem_nb r).mp hy).2).1
    change 10 ≤ (N ∩ nb r A y).card at h
    rw [← loc y] at h
    change 11 ≤ (insert y (nb r N y)).card
    rw [card_insert_of_notMem (fun hy => hr y ((mem_nb r).mp hy).2)]
    omega
  have hKi (y : V) (hy : y ∈ N) (z : V) (hz : z ∈ N) (hyz : comp y z) :
      (K y ∩ K z).card ≤ 3 := by
    have hbound := hapart y (hNA hy) z (hNA hz) hyz.1 hyz.2
    let D := nb r A y ∩ nb r A z
    have hxD : x ∈ D := mem_inter.mpr ⟨(mem_nb r).mpr ⟨hx,rs ((mem_nb r).mp hy).2⟩,
      (mem_nb r).mpr ⟨hx,rs ((mem_nb r).mp hz).2⟩⟩
    have hsub : K y ∩ K z ⊆ D.erase x := by
      intro p hp
      have hpN := hKs y hy (mem_inter.mp hp).1
      have hs : p ∈ nb r N y ∧ p ∈ nb r N z := by
        obtain ⟨hp1,hp2⟩ := mem_inter.mp hp
        rcases mem_insert.mp hp1 with e | h
        · subst p
          rcases mem_insert.mp hp2 with e | h
          · exact (hyz.1 e).elim
          · exact (hyz.2 (rs ((mem_nb r).mp h).2)).elim
        · rcases mem_insert.mp hp2 with e | h'
          · subst p
            exact (hyz.2 ((mem_nb r).mp h).2).elim
          · exact ⟨h,h'⟩
      refine mem_erase.mpr ⟨fun e => xn (e ▸ hpN), mem_inter.mpr ?_⟩
      exact ⟨(mem_nb r).mpr ⟨hNA hpN,((mem_nb r).mp hs.1).2⟩,
        (mem_nb r).mpr ⟨hNA hpN,((mem_nb r).mp hs.2).2⟩⟩
    have h := card_le_card hsub
    have he := card_erase_add_one hxD
    change D.card ≤ 4 at hbound
    omega
  have ctri : ∀ a ∈ N, ∀ b ∈ N, ∀ c ∈ N, comp a b → comp b c → comp c a → False := by
    intro a ha b hb c hc hab hbc hca
    exact no_three_large_sets (K a) (K b) (K c) N hN
      (hKs a ha) (hKs b hb) (hKs c hc) (hKl a ha) (hKl b hb) (hKl c hc)
      (hKi a ha b hb hab) (hKi a ha c hc (cSymm hca)) (hKi b hb c hc hbc)
  obtain ⟨L, R, hLR, hdis, hL, hR, hL9, hR9⟩ :=
    bipartition_twenty_two comp N hN cSymm cIrrefl ctri cdeg
  have hLsub : L ⊆ N := fun _ h => hLR ▸ mem_union.mpr (Or.inl h)
  have hRsub : R ⊆ N := fun _ h => hLR ▸ mem_union.mpr (Or.inr h)
  have hcards : L.card + R.card = 22 := by rw [← card_union_of_disjoint hdis, hLR, hN]
  have hLc : L.card ≤ 13 := by omega
  have hRc : R.card ≤ 13 := by omega
  have grow (Y : Finset V) (hY : Y ⊆ N) (hn : ∀ u ∈ Y, ∀ v ∈ Y, ¬comp u v) :
      Clique r (insert x Y) := by
    intro u hu v hv hne
    rcases mem_insert.mp hu with he | huY
    · subst u
      rcases mem_insert.mp hv with he | hvY
      · exact (hne he.symm).elim
      · exact ((mem_nb r).mp (hY hvY)).2
    · rcases mem_insert.mp hv with he | hvY
      · subst v
        exact rs ((mem_nb r).mp (hY huY)).2
      · by_contra h
        exact hn u huY v hvY ⟨hne,h⟩
  refine ⟨L, R, hLR, hdis, hL9, hR9, grow L hLsub hL, grow R hRsub hR, ?_⟩
  intro B hBA hxB hB hBc
  let T := B.erase x
  have hT : T ⊆ N := by
    intro y hy
    obtain ⟨hyx,hyB⟩ := mem_erase.mp hy
    exact (mem_nb r).mpr ⟨hBA hyB, hBc x hxB y hyB hyx.symm⟩
  have bound_other (U W : Finset V) (hu : U ∪ W = N) (hUc : U.card ≤ 13)
      (hw : ∀ y ∈ W, ∀ z ∈ W, ¬comp y z) (z : V) (hz : z ∈ T ∩ W) :
      (T ∩ U).card ≤ 4 := by
    obtain ⟨hzT,hzW⟩ := mem_inter.mp hz
    have hn := cdeg z (hT hzT)
    have hsub : nb comp N z ⊆ U := by
      intro y hy
      obtain ⟨hyN,hzy⟩ := (mem_nb comp).mp hy
      rw [← hu] at hyN
      exact (mem_union.mp hyN).resolve_right (fun hyW => hw z hzW y hyW hzy)
    have hd : Disjoint (T ∩ U) (nb comp N z) := by
      apply disjoint_left.mpr
      intro y hy hnb
      have h := ((mem_nb comp).mp hnb).2
      exact h.2 (hBc z (mem_erase.mp hzT).2 y (mem_erase.mp (mem_inter.mp hy).1).2 h.1)
    have hs := card_le_card (union_subset (show T ∩ U ⊆ U from inter_subset_right) hsub)
    rw [card_union_of_disjoint hd] at hs
    omega
  by_cases hTL : (T ∩ L).Nonempty
  · by_cases hTR : (T ∩ R).Nonempty
    · obtain ⟨l,hl⟩ := hTL
      obtain ⟨q,hq⟩ := hTR
      have hlt := bound_other L R hLR hLc hR q hq
      have hrt := bound_other R L (by rw [union_comm,hLR]) hRc hL l hl
      have hTsum : (T ∩ L) ∪ (T ∩ R) = T := by
        ext y
        simp only [mem_union,mem_inter]
        exact ⟨fun h => h.elim And.left And.left, fun hy =>
          (mem_union.mp (show y ∈ L ∪ R from hLR.symm ▸ hT hy)).elim
            (fun h => Or.inl ⟨hy,h⟩) (fun h => Or.inr ⟨hy,h⟩)⟩
      have z := card_union_le (T ∩ L) (T ∩ R)
      rw [hTsum] at z
      have he : T.card + 1 = B.card := card_erase_add_one hxB
      omega
    · left
      intro y hy
      by_cases e : y = x
      · exact mem_insert.mpr (Or.inl e)
      · have hyT : y ∈ T := mem_erase.mpr ⟨e,hy⟩
        have h := mem_union.mp (show y ∈ L ∪ R from hLR.symm ▸ hT hyT)
        exact mem_insert.mpr (Or.inr (h.resolve_right (fun h => hTR ⟨y,mem_inter.mpr ⟨hyT,h⟩⟩)))
  · right
    intro y hy
    by_cases e : y = x
    · exact mem_insert.mpr (Or.inl e)
    · have hyT : y ∈ T := mem_erase.mpr ⟨e,hy⟩
      have h := mem_union.mp (show y ∈ L ∪ R from hLR.symm ▸ hT hyT)
      exact mem_insert.mpr (Or.inr (h.resolve_left (fun h => hTL ⟨y,mem_inter.mpr ⟨hyT,h⟩⟩)))

private noncomputable def bigCliques (A : Finset V) : Finset (Finset V) := by
  classical
  exact A.powerset.filter fun C => 10 ≤ C.card ∧ Clique r C ∧
    ∀ D ⊆ A, Clique r D → C ⊆ D → D = C

omit [DecidableRel r] in
private theorem mem_bigCliques {A C : Finset V} :
    C ∈ bigCliques r A ↔ C ⊆ A ∧ 10 ≤ C.card ∧ Clique r C ∧
      ∀ D ⊆ A, Clique r D → C ⊆ D → D = C := by
  classical
  simp only [bigCliques, mem_filter, mem_powerset]

private theorem clique_pair (A : Finset V)
    (rs : ∀ ⦃x y⦄, r x y → r y x) (hr : ∀ x, ¬r x x)
    (hd : ∀ x ∈ A, (nb r A x).card = 22)
    (hcommon : ∀ x ∈ A, ∀ y ∈ A, r x y →
      10 ≤ (nb r A x ∩ nb r A y).card ∧ (nb r A x ∩ nb r A y).card ≤ 12)
    (hapart : ∀ x ∈ A, ∀ y ∈ A, x ≠ y → ¬r x y → (nb r A x ∩ nb r A y).card ≤ 4)
    (x : V) (hx : x ∈ A) :
    ∃ C D, C ∈ bigCliques r A ∧ D ∈ bigCliques r A ∧ C ≠ D ∧ C ∩ D = {x} ∧
      C ∪ D = insert x (nb r A x) ∧
      ∀ E ∈ bigCliques r A, x ∈ E → E = C ∨ E = D := by
  classical
  obtain ⟨L, R, hLR, hdis, hL9, hR9, hclL, hclR, hclass⟩ :=
    two_local_cliques r A rs hr hd hcommon hapart x hx
  let C := insert x L
  let D := insert x R
  have hLsub : L ⊆ nb r A x := fun _ e => hLR ▸ mem_union.mpr (Or.inl e)
  have hRsub : R ⊆ nb r A x := fun _ e => hLR ▸ mem_union.mpr (Or.inr e)
  have hxn : x ∉ nb r A x := fun e => hr x ((mem_nb r).mp e).2
  have hunion : C ∪ D = insert x (nb r A x) := by
    ext y
    simp only [C,D,mem_insert,mem_union,← hLR]
    tauto
  have hinter : C ∩ D = {x} := by
    ext y
    simp only [C,D,mem_inter,mem_insert,mem_singleton]
    constructor
    · rintro ⟨e | ha,e' | hb⟩
      · exact e
      · exact e
      · exact e'
      · exact (disjoint_left.mp hdis ha hb).elim
    · exact fun e => ⟨Or.inl e,Or.inl e⟩
  have hsubset (U : Finset V) (hU : U ⊆ nb r A x) : insert x U ⊆ A := by
    intro y hy
    rcases mem_insert.mp hy with rfl | hy
    · exact hx
    · exact (nb_subset r A x) (hU hy)
  have hC : 10 ≤ C.card := by
    change 10 ≤ (insert x L).card
    rw [card_insert_of_notMem (fun e => hxn (hLsub e))]
    omega
  have hD : 10 ≤ D.card := by
    change 10 ≤ (insert x R).card
    rw [card_insert_of_notMem (fun e => hxn (hRsub e))]
    omega
  have hCD : ¬C ⊆ D := by
    intro e
    have he := card_le_card (show C ⊆ C ∩ D from fun _ h => mem_inter.mpr ⟨h,e h⟩)
    rw [hinter,card_singleton] at he
    omega
  have hDC : ¬D ⊆ C := by
    intro e
    have he := card_le_card (show D ⊆ C ∩ D from fun _ h => mem_inter.mpr ⟨e h,h⟩)
    rw [hinter,card_singleton] at he
    omega
  have hmC : C ∈ bigCliques r A := by
    refine (mem_bigCliques r).mpr ⟨hsubset L hLsub,hC,hclL,?_⟩
    intro E hEA hE hCE
    have hxE : x ∈ E := hCE (mem_insert_self _ _)
    rcases hclass E hEA hxE (hC.trans (card_le_card hCE)) hE with h | h
    · exact le_antisymm h hCE
    · exact False.elim (hCD (hCE.trans h))
  have hmD : D ∈ bigCliques r A := by
    refine (mem_bigCliques r).mpr ⟨hsubset R hRsub,hD,hclR,?_⟩
    intro E hEA hE hDE
    have hxE : x ∈ E := hDE (mem_insert_self _ _)
    rcases hclass E hEA hxE (hD.trans (card_le_card hDE)) hE with h | h
    · exact False.elim (hDC (hDE.trans h))
    · exact le_antisymm h hDE
  refine ⟨C,D,hmC,hmD,fun e => hCD (by rw [e]),hinter,hunion,?_⟩
  intro E hE hxE
  obtain ⟨hEA, hEcard, hEclique, hEmax⟩ := (mem_bigCliques r).mp hE
  rcases hclass E hEA hxE hEcard hEclique with h | h
  · exact Or.inl (hEmax C (hsubset L hLsub) hclL h).symm
  · exact Or.inr (hEmax D (hsubset R hRsub) hclR h).symm


private theorem star_cover (A : Finset V) (hA : A.card = 96)
    (rs : ∀ ⦃x y⦄, r x y → r y x) (hr : ∀ x, ¬r x x)
    (hd : ∀ x ∈ A, (nb r A x).card = 22)
    (hcommon : ∀ x ∈ A, ∀ y ∈ A, r x y →
      10 ≤ (nb r A x ∩ nb r A y).card ∧ (nb r A x ∩ nb r A y).card ≤ 12)
    (hapart : ∀ x ∈ A, ∀ y ∈ A, x ≠ y → ¬r x y → (nb r A x ∩ nb r A y).card ≤ 4) :
    ∃ K : Finset (Finset V), K.card = 16 ∧
      (∀ C ∈ K, C ⊆ A ∧ C.card = 12 ∧ Clique r C) ∧
      (∀ C ∈ K, ∀ x ∈ C, ∃ D ∈ K, D ≠ C ∧ x ∈ D ∧ C ∩ D = {x}) ∧
      (∀ C ∈ K, ∀ D ∈ K, C ≠ D → ∀ x ∈ C, x ∈ D →
        C ∪ D = insert x (nb r A x) ∧ C ∩ D = {x}) ∧
      ∀ B : Finset V, (∑ C ∈ K, ((C ∩ B).card : ℤ)) = 2 * ((A ∩ B).card : ℤ) := by
  classical
  let K := bigCliques r A
  have csub (C : Finset V) (hC : C ∈ K) : C ⊆ A := ((mem_bigCliques r).mp hC).1
  have cmin (C : Finset V) (hC : C ∈ K) : 10 ≤ C.card := ((mem_bigCliques r).mp hC).2.1
  have partner (C : Finset V) (hC : C ∈ K) (x : V) (hx : x ∈ C) :
      ∃ D ∈ K, D ≠ C ∧ x ∈ D ∧ C ∩ D = {x} := by
    obtain ⟨L,R,hL,hR,hne,hint,_,hall⟩ :=
      clique_pair r A rs hr hd hcommon hapart x (csub C hC hx)
    have hmem : x ∈ L ∩ R := by rw [hint]; exact mem_singleton_self _
    rcases hall C hC hx with e | e
    · subst C
      exact ⟨R,hR,hne.symm,(mem_inter.mp hmem).2,hint⟩
    · subst C
      exact ⟨L,hL,hne,(mem_inter.mp hmem).1,by rw [inter_comm,hint]⟩
  have paired (C : Finset V) (hC : C ∈ K) (D : Finset V) (hD : D ∈ K) (hne : C ≠ D)
      (x : V) (hx : x ∈ C) (hy : x ∈ D) :
      C ∪ D = insert x (nb r A x) ∧ C ∩ D = {x} := by
    obtain ⟨L,R,_,_,_,hint,hunion,hall⟩ :=
      clique_pair r A rs hr hd hcommon hapart x (csub C hC hx)
    rcases hall C hC hx with e | e
    · have f := (hall D hD hy).resolve_left (fun f => hne (e.trans f.symm))
      simpa only [e,f] using And.intro hunion hint
    · have f := (hall D hD hy).resolve_right (fun f => hne (e.trans f.symm))
      simp only [e,f]
      exact ⟨by rwa [union_comm],by rwa [inter_comm]⟩
  have twice (x : V) (hx : x ∈ A) : (K.filter (x ∈ ·)).card = 2 := by
    obtain ⟨L,R,hL,hR,hne,hin,_,hall⟩ := clique_pair r A rs hr hd hcommon hapart x hx
    have hh : x ∈ L ∩ R := by rw [hin]; exact mem_singleton_self _
    have he : K.filter (x ∈ ·) = {L,R} := by
      ext C
      simp only [mem_filter, mem_insert,mem_singleton]
      exact ⟨fun h => hall C h.1 h.2, fun h => h.elim
        (fun e => e.symm ▸ ⟨hL,(mem_inter.mp hh).1⟩)
        (fun e => e.symm ▸ ⟨hR,(mem_inter.mp hh).2⟩)⟩
    rw [he,card_pair hne]
  have count (B : Finset V) : (∑ C ∈ K, (C ∩ B).card) = 2 * (A ∩ B).card := by
    calc
      _ = ∑ C ∈ K, ∑ x ∈ A ∩ B, if x ∈ C then (1 : ℕ) else 0 := by
        apply sum_congr rfl
        intro C hC
        rw [← card_filter]
        congr 1
        ext x
        simp only [mem_inter,mem_filter]
        exact ⟨fun h => ⟨⟨csub C hC h.1,h.2⟩,h.1⟩,fun h => ⟨h.2,h.1.2⟩⟩
      _ = ∑ x ∈ A ∩ B, (K.filter (x ∈ ·)).card := by
        rw [sum_comm]
        simp only [card_filter]
      _ = _ := by
        have ht (x : V) (hx : x ∈ A ∩ B) : (K.filter (x ∈ ·)).card = 2 :=
          twice x (mem_inter.mp hx).1
        rw [sum_congr rfl ht,sum_const]
        simp [Nat.mul_comm]
  have total : (∑ C ∈ K, C.card) = 192 := by
    calc
      _ = ∑ C ∈ K, (C ∩ A).card := by
        apply sum_congr rfl
        intro C hC
        rw [inter_eq_left.mpr (csub C hC)]
      _ = _ := by simpa [hA] using count A
  have hK19 : K.card ≤ 19 := by
    have h := sum_le_sum cmin
    rw [sum_const,total] at h
    simp at h
    omega
  have hdeg : ∀ C ∈ K, C.card = 12 := by
    have h := PlaneCliqueCount.alternating_vanish K hK19 cmin partner
      (fun C => (C.card : ℤ) - 12) (by
        intro C hC D hD hne x hx hy
        obtain ⟨hu,hi⟩ := paired C hC D hD hne x hx hy
        have h := card_union_add_card_inter C D
        have hxN : x ∉ nb r A x := fun e => hr x ((mem_nb r).mp e).2
        rw [hu,hi,card_insert_of_notMem hxN,card_singleton,hd x (csub C hC hx)] at h
        omega)
    intro C hC
    have hc := h C hC
    omega
  have hK16 : K.card = 16 := by
    rw [sum_congr rfl hdeg,sum_const] at total
    simp at total
    omega
  exact ⟨K,hK16,fun C hc => ⟨csub C hc,hdeg C hc,((mem_bigCliques r).mp hc).2.2.1⟩,
    partner,paired,fun B => by exact_mod_cast count B⟩

end PlaneLocalGraph


/- Adding a line to a partial plane from a point of degree twelve. -/

open Finset
open scoped BigOperators

namespace PartialPlane12

abbrev Lines := Finset (Finset (Fin 157))

def Uniform (S : Lines) : Prop := ∀ b ∈ S, b.card = 13

def MeetsOnce (S : Lines) : Prop :=
  ∀ b ∈ S, ∀ c ∈ S, b ≠ c → ∃! y, y ∈ b ∧ y ∈ c

private def through (S : Lines) (x : Fin 157) : Lines := S.filter (x ∈ ·)

private theorem punctured_disjoint (S : Lines) (hmeet : MeetsOnce S) (x : Fin 157) :
    (↑(through S x) : Set (Finset (Fin 157))).PairwiseDisjoint (fun b => b.erase x) := by
  intro b hb c hc hne
  obtain ⟨hbS, hbx⟩ := mem_filter.mp hb
  obtain ⟨hcS, hcx⟩ := mem_filter.mp hc
  obtain ⟨p, _, hp⟩ := hmeet b hbS c hcS hne
  refine disjoint_left.mpr ?_
  intro y hyb hyc
  exact (mem_erase.mp hyb).1
    ((hp y ⟨(mem_erase.mp hyb).2, (mem_erase.mp hyc).2⟩).trans (hp x ⟨hbx, hcx⟩).symm)

private theorem card_covered (S : Lines) (hunif : Uniform S) (hmeet : MeetsOnce S) (x : Fin 157) :
    ((through S x).biUnion (fun b => b.erase x)).card = 12 * (through S x).card := by
  rw [card_biUnion (punctured_disjoint S hmeet x)]
  have h b (hb : b ∈ through S x) : (b.erase x).card = 12 := by
    obtain ⟨hbS, hbx⟩ := mem_filter.mp hb
    rw [card_erase_of_mem hbx, hunif b hbS]
  rw [sum_congr rfl h, sum_const]
  simp [Nat.mul_comm]

theorem degree_le_thirteen (S : Lines) (hunif : Uniform S) (hmeet : MeetsOnce S) (x : Fin 157) :
    (through S x).card ≤ 13 := by
  have h : ((through S x).biUnion (fun b => b.erase x)).card ≤ 157 := by
    simpa using card_le_univ ((through S x).biUnion (fun b => b.erase x))
  rw [card_covered S hunif hmeet x] at h
  omega

theorem extend_at_twelve (S : Lines) (hunif : Uniform S) (hmeet : MeetsOnce S) (x : Fin 157)
    (hxdeg : (S.filter (x ∈ ·)).card = 12) :
    ∃ T : Lines, S ⊆ T ∧ T.card = S.card + 1 ∧ Uniform T ∧ MeetsOnce T := by
  let P := through S x
  let U := P.biUnion (fun b => b.erase x)
  let B := univ \ U
  have hPx : P.card = 12 := hxdeg
  have hUc : U.card = 144 := by
    change ((through S x).biUnion (fun b => b.erase x)).card = 144
    rw [card_covered S hunif hmeet x]
    change 12 * P.card = 144
    rw [hPx]
  have hBc : (B : Finset (Fin 157)).card = 13 := by
    change (univ \ U).card = 13
    rw [card_sdiff_of_subset (subset_univ U), card_univ, Fintype.card_fin, hUc]
  have hxB : x ∈ B := by
    refine mem_sdiff.mpr ⟨mem_univ _, ?_⟩
    intro h
    obtain ⟨l, _, hl⟩ := mem_biUnion.mp h
    exact (mem_erase.mp hl).1 rfl
  have cross (b : Finset (Fin 157)) (hb : b ∈ S) : ∃! y, y ∈ B ∧ y ∈ b := by
    by_cases hbx : x ∈ b
    · refine ⟨x, ⟨hxB, hbx⟩, ?_⟩
      intro y hy
      by_contra hyx
      exact (mem_sdiff.mp hy.1).2
        (mem_biUnion.mpr ⟨b, mem_filter.mpr ⟨hb, hbx⟩, mem_erase.mpr ⟨hyx, hy.2⟩⟩)
    · have hbi : U ∩ b = P.biUnion (fun l => l.erase x ∩ b) := by
        ext y
        simp only [mem_inter, mem_biUnion, U]
        aesop
      have hdis : (↑P : Set (Finset (Fin 157))).PairwiseDisjoint (fun l => l.erase x ∩ b) := by
        intro l hl m hm hne
        have hd := punctured_disjoint S hmeet x hl hm hne
        exact hd.mono (by intro y hy; exact (mem_inter.mp hy).1)
          (by intro y hy; exact (mem_inter.mp hy).1)
      have hone (l : Finset (Fin 157)) (hl : l ∈ P) : (l.erase x ∩ b).card = 1 := by
        obtain ⟨hlS, hlx⟩ := mem_filter.mp hl
        have hne : l ≠ b := fun h => hbx (h ▸ hlx)
        obtain ⟨p, hp, huniq⟩ := hmeet l hlS b hb hne
        apply card_eq_one_iff_existsUnique.mpr
        refine ⟨p, mem_inter.mpr ⟨mem_erase.mpr ⟨?_, hp.1⟩, hp.2⟩, ?_⟩
        · intro h
          exact hbx (h ▸ hp.2)
        · intro y hy
          exact huniq y ⟨(mem_erase.mp (mem_inter.mp hy).1).2, (mem_inter.mp hy).2⟩
      have hint : (U ∩ b).card = 12 := by
        rw [hbi, card_biUnion hdis, sum_congr rfl hone, sum_const]
        simp [hPx]
      have hcard : (B ∩ b).card = 1 := by
        have hdiff : B ∩ b = b \ U := by ext y; simp [B, and_comm]
        rw [hdiff, card_sdiff, hunif b hb, hint]
      simpa only [mem_inter] using (card_eq_one_iff_existsUnique.mp hcard)
  have hB : B ∉ S := by
    intro hb
    have hone : (B ∩ B).card = 1 := card_eq_one_iff_existsUnique.mpr
      (by simpa only [mem_inter] using cross B hb)
    simp [hBc] at hone
  refine ⟨insert B S, subset_insert _ _, card_insert_of_notMem hB, ?_, ?_⟩
  · intro b hb
    rcases mem_insert.mp hb with rfl | hb
    · exact hBc
    · exact hunif b hb
  · intro b hb c hc hne
    rcases mem_insert.mp hb with rfl | hb
    · rcases mem_insert.mp hc with rfl | hc
      · exact False.elim (hne rfl)
      · exact cross c hc
    · rcases mem_insert.mp hc with rfl | hc
      · simpa only [and_comm] using cross b hb
      · exact hmeet b hb c hc hne

def defect (S : Lines) (x : Fin 157) : ℤ := 13 - (through S x).card

theorem defect_nonneg (S : Lines) (hunif : Uniform S) (hmeet : MeetsOnce S) (x : Fin 157) :
    0 ≤ defect S x := by
  unfold defect
  have h := degree_le_thirteen S hunif hmeet x
  exact sub_nonneg.mpr (by exact_mod_cast h)

private theorem degrees_on_line (S : Lines) (hunif : Uniform S) (hmeet : MeetsOnce S)
    (b : Finset (Fin 157)) (hb : b ∈ S) :
    (∑ x ∈ b, (through S x).card) = S.card + 12 := by
  classical
  have inter_count (l : Finset (Fin 157)) (hl : l ∈ S.erase b) : (b ∩ l).card = 1 := by
    obtain ⟨hlb, hlS⟩ := mem_erase.mp hl
    exact card_eq_one_iff_existsUnique.mpr (by simpa only [mem_inter] using hmeet b hb l hlS hlb.symm)
  calc
    _ = ∑ x ∈ b, ∑ l ∈ S, if x ∈ l then (1 : ℕ) else 0 := by
      simp only [through, card_filter]
    _ = ∑ l ∈ S, ∑ x ∈ b, if x ∈ l then (1 : ℕ) else 0 := sum_comm
    _ = ∑ l ∈ S, (b ∩ l).card := by
      apply sum_congr rfl
      intro l _
      rw [← card_filter]
      congr 1
    _ = _ := by
      rw [← sum_erase_add S (fun l => (b ∩ l).card) hb,
        sum_congr rfl inter_count, sum_const, inter_self, hunif b hb]
      simp [card_erase_add_one hb]

theorem defect_sum_on_line (S : Lines) (hunif : Uniform S) (hmeet : MeetsOnce S) :
    ∀ b ∈ S, (∑ x ∈ b, defect S x) = 157 - (S.card : ℤ) := by
  intro b hb
  have h := degrees_on_line S hunif hmeet b hb
  have h' : (∑ x ∈ b, ((through S x).card : ℤ)) = (S.card : ℤ) + 12 := by exact_mod_cast h
  simp only [defect, sum_sub_distrib, sum_const, nsmul_eq_mul, hunif b hb, h']
  norm_num
  ring

private theorem weighted_incidence (S : Lines) (f : Fin 157 → ℤ) :
    (∑ x, ((through S x).card : ℤ) * f x) = ∑ b ∈ S, ∑ x ∈ b, f x := by
  classical
  calc
    _ = ∑ x, ∑ b ∈ S, if x ∈ b then f x else 0 := by
      apply sum_congr rfl
      intro x _
      simp only [through, card_filter, Nat.cast_sum, sum_mul, Nat.cast_ite, Nat.cast_one,
        Nat.cast_zero, ite_mul, one_mul, zero_mul]
    _ = ∑ b ∈ S, ∑ x, if x ∈ b then f x else 0 := sum_comm
    _ = _ := by
      apply sum_congr rfl
      intro b _
      rw [← sum_filter]
      simp

theorem defect_moments (S : Lines) (hunif : Uniform S) (hmeet : MeetsOnce S) :
    let d : ℤ := 157 - S.card
    (∑ x, defect S x) = 13 * d ∧ (∑ x, (defect S x) ^ 2) = d * (d + 12) := by
  let d : ℤ := 157 - S.card
  have hi : (∑ x, ((through S x).card : ℤ)) = (S.card : ℤ) * 13 := by
    have hi0 := weighted_incidence S (fun _ => 1)
    simp only [mul_one] at hi0
    rw [hi0]
    trans ∑ _b ∈ S, (13 : ℤ)
    · apply sum_congr rfl
      intro b hb
      rw [sum_const, hunif b hb]
      norm_num
    · simp
  have hfirst : (∑ x, defect S x) = 13 * d := by
    rw [show (∑ x, defect S x) = (∑ _x : Fin 157, (13 : ℤ)) -
        (∑ x, ((through S x).card : ℤ)) by simp [defect, sum_sub_distrib], hi]
    simp [d]
    ring
  refine ⟨hfirst, ?_⟩
  have hw : (∑ x, ((through S x).card : ℤ) * defect S x) = (S.card : ℤ) * d := by
    rw [weighted_incidence]
    rw [sum_congr rfl (defect_sum_on_line S hunif hmeet), sum_const, nsmul_eq_mul]
  have hh : (∑ x, (defect S x) ^ 2) = 13 * (∑ x, defect S x) -
      (∑ x, ((through S x).card : ℤ) * defect S x) := by
    rw [mul_sum, ← sum_sub_distrib]
    apply sum_congr rfl
    intro x _
    simp only [defect]
    ring
  rw [hh, hfirst, hw]
  dsimp [d]
  ring

private theorem center_not_covered (S : Lines) (x : Fin 157) :
    x ∉ (through S x).biUnion (fun b => b.erase x) := by
  intro h
  obtain ⟨b, _, hb⟩ := mem_biUnion.mp h
  exact (mem_erase.mp hb).1 rfl

def uncovered (S : Lines) (x : Fin 157) : Finset (Fin 157) :=
  univ \ insert x ((through S x).biUnion (fun b => b.erase x))

theorem mem_uncovered {S : Lines} {x y : Fin 157} :
    y ∈ uncovered S x ↔ y ≠ x ∧ ¬ ∃ b ∈ S, x ∈ b ∧ y ∈ b := by
  simp only [uncovered, mem_sdiff, mem_univ, true_and, mem_insert, mem_biUnion,
    through, mem_filter, mem_erase]
  constructor
  · intro h
    have hxy : y ≠ x := fun hxy => h (Or.inl hxy)
    exact ⟨hxy, fun ⟨b, hb, hx, hy⟩ => h (Or.inr ⟨b, ⟨hb, hx⟩, ⟨hxy, hy⟩⟩)⟩
  · rintro ⟨hne, h⟩ (he | ⟨b, ⟨hb, hx⟩, _, hy⟩)
    · exact hne he
    · exact h ⟨b, hb, hx, hy⟩

theorem uncovered_count (S : Lines) (hunif : Uniform S) (hmeet : MeetsOnce S) (x : Fin 157) :
    ((uncovered S x).card : ℤ) = 12 * defect S x := by
  have hr := degree_le_thirteen S hunif hmeet x
  rw [uncovered, card_sdiff_of_subset (subset_univ _),
    card_insert_of_notMem (center_not_covered S x), card_covered S hunif hmeet x,
    card_univ, Fintype.card_fin]
  rw [Nat.cast_sub (by omega), Nat.cast_add, Nat.cast_one, Nat.cast_mul]
  norm_num [defect]
  ring

theorem defect_sum_uncovered (S : Lines) (hunif : Uniform S) (hmeet : MeetsOnce S) (x : Fin 157) :
    let d : ℤ := 157 - S.card
    (∑ y ∈ uncovered S x, defect S y) = defect S x * (d + 12 - defect S x) := by
  let d : ℤ := 157 - S.card
  let P := through S x
  let U := P.biUnion (fun b => b.erase x)
  have hline (b : Finset (Fin 157)) (hb : b ∈ P) :
      (∑ y ∈ b.erase x, defect S y) = d - defect S x := by
    obtain ⟨hbS, hbx⟩ := mem_filter.mp hb
    have h := defect_sum_on_line S hunif hmeet b hbS
    rw [← sum_erase_add b (defect S) hbx] at h
    change (∑ y ∈ b.erase x, defect S y) + defect S x = d at h
    linarith
  have hu : (∑ y ∈ U, defect S y) = (P.card : ℤ) * (d - defect S x) := by
    rw [sum_biUnion (punctured_disjoint S hmeet x), sum_congr rfl hline, sum_const, nsmul_eq_mul]
  have h := sum_sdiff (f := defect S) (subset_univ (insert x U))
  change (∑ y ∈ uncovered S x, defect S y) + (∑ y ∈ insert x U, defect S y) =
    ∑ y, defect S y at h
  rw [sum_insert (center_not_covered S x), hu, (defect_moments S hunif hmeet).1] at h
  have hp : (P.card : ℤ) = 13 - defect S x := by simp [P, defect]
  change (∑ y ∈ uncovered S x, defect S y) + (defect S x + ↑P.card * (d - defect S x)) =
    13 * d at h
  rw [hp] at h
  change (∑ y ∈ uncovered S x, defect S y) = defect S x * (d + 12 - defect S x)
  linear_combination h

theorem positive_defect_bounded (S : Lines) (hunif : Uniform S) (hmeet : MeetsOnce S)
    (hnone : ∀ x, defect S x ≠ 1) {x : Fin 157} (hx : 0 < defect S x) :
    defect S x ≤ 145 - (S.card : ℤ) := by
  have hdef (y : Fin 157) (hy : y ∈ uncovered S x) : 2 ≤ defect S y := by
    obtain ⟨hyx, hy⟩ := mem_uncovered.mp hy
    have hxy : x ∈ uncovered S y := mem_uncovered.mpr ⟨Ne.symm hyx,
      fun ⟨b, hb, hby, hbx⟩ => hy ⟨b, hb, hbx, hby⟩⟩
    have hpos : 0 < (uncovered S y).card := card_pos.mpr ⟨x, hxy⟩
    have hc := uncovered_count S hunif hmeet y
    have hpos' : 0 < ((uncovered S y).card : ℤ) := by exact_mod_cast hpos
    have hn := hnone y
    omega
  have hh : (∑ y ∈ uncovered S x, (2 : ℤ)) ≤ ∑ y ∈ uncovered S x, defect S y :=
    sum_le_sum hdef
  rw [sum_const, nsmul_eq_mul, uncovered_count S hunif hmeet x, defect_sum_uncovered S hunif hmeet x] at hh
  by_contra! hgt
  have hv : 157 - (S.card : ℤ) + 12 - defect S x < 24 := by linarith
  have hm := mul_lt_mul_of_pos_left hv hx
  nlinarith

theorem extend_142 (S : Lines) (hunif : Uniform S) (hmeet : MeetsOnce S)
    (h142 : S.card = 142) : ∃ T : Lines, S ⊆ T ∧ T.card = S.card + 1 ∧ Uniform T ∧ MeetsOnce T := by
  classical
  by_cases h1 : ∃ x, defect S x = 1
  · obtain ⟨x, hx⟩ := h1
    apply extend_at_twelve S hunif hmeet x
    unfold defect at hx
    change (through S x).card = 12
    omega
  push Not at h1
  let W := fun x : Fin 157 => if defect S x = 3 then (1 : ℤ) else 0
  have cases_defect (x : Fin 157) : defect S x = 0 ∨ defect S x = 2 ∨ defect S x = 3 := by
    have h0 := defect_nonneg S hunif hmeet x
    have hne := h1 x
    by_cases hz : defect S x = 0
    · exact Or.inl hz
    · have hpos : 0 < defect S x := by omega
      have hsmall := positive_defect_bounded S hunif hmeet h1 hpos
      norm_num [h142] at hsmall
      omega
  have hpoint (x : Fin 157) : (defect S x)^2 - 2 * defect S x = 3 * W x := by
    rcases cases_defect x with h | h | h <;> norm_num [W, h]
  have hW : (∑ x, W x) = 5 := by
    have h := Finset.sum_congr (s₁ := (univ : Finset (Fin 157))) rfl (fun x _ => hpoint x)
    rw [sum_sub_distrib, ← mul_sum, ← mul_sum, (defect_moments S hunif hmeet).1,
      (defect_moments S hunif hmeet).2] at h
    norm_num [h142] at h
    omega
  have hline (b : Finset (Fin 157)) (hb : b ∈ S) : 1 ≤ ∑ x ∈ b, W x := by
    have hsome : ∃ x ∈ b, defect S x = 3 := by
      by_contra! hnone
      have heven (x : Fin 157) (hx : x ∈ b) : defect S x = 2 * (defect S x / 2) := by
        rcases cases_defect x with h | h | h
        · norm_num [h]
        · norm_num [h]
        · exact (hnone x hx h).elim
      have h := Finset.sum_congr rfl heven
      rw [← mul_sum, defect_sum_on_line S hunif hmeet b hb] at h
      norm_num [h142] at h
      omega
    obtain ⟨x, hx, h3⟩ := hsome
    have hs : W x ≤ ∑ y ∈ b, W y := single_le_sum (fun y _ => by dsimp [W]; split <;> norm_num) hx
    simpa only [W, h3, if_true] using hs
  have hsmall : (∑ b ∈ S, ∑ x ∈ b, W x) = 50 := by
    rw [← weighted_incidence]
    calc
      _ = ∑ x, 10 * W x := by
        apply sum_congr rfl
        intro x _
        by_cases h : defect S x = 3
        · have hd : ((through S x).card : ℤ) = 10 := by unfold defect at h; omega
          rw [hd]
        · simp [W, h]
      _ = _ := by rw [← mul_sum, hW]; norm_num
  have hbig := Finset.sum_le_sum (s := S) hline
  rw [hsmall, sum_const, nsmul_eq_mul, mul_one, h142] at hbig
  norm_num at hbig

private def covered (S : Lines) (x : Fin 157) : Finset (Fin 157) :=
  insert x ((through S x).biUnion (fun b => b.erase x))

private theorem mem_covered {S : Lines} {x z : Fin 157} :
    z ∈ covered S x ↔ z = x ∨ ∃ l ∈ S, x ∈ l ∧ z ∈ l := by
  by_cases h : z = x
  · simp [covered, h]
  · simp only [covered, mem_insert, mem_biUnion, through, mem_filter, mem_erase, h, false_or]
    aesop

private theorem line_subset_covered {S : Lines} {x : Fin 157} {b : Finset (Fin 157)}
    (hb : b ∈ S) (hxb : x ∈ b) : b ⊆ covered S x :=
  fun _ hz => mem_covered.mpr (Or.inr ⟨b, hb, hxb, hz⟩)

private theorem covered_count (S : Lines) (hunif : Uniform S) (hmeet : MeetsOnce S) (x : Fin 157) :
    (covered S x).card = 12 * (through S x).card + 1 := by
  rw [covered, card_insert_of_notMem (center_not_covered S x), card_covered S hunif hmeet x]

private theorem pencil_inter_line (S : Lines) (hmeet : MeetsOnce S) (x : Fin 157)
    (b : Finset (Fin 157)) (hb : b ∈ S) (hx : x ∉ b) :
    (covered S x ∩ b).card = (through S x).card := by
  rw [covered, insert_inter_of_notMem hx, biUnion_inter]
  have hdis : (↑(through S x) : Set (Finset (Fin 157))).PairwiseDisjoint (fun l => l.erase x ∩ b) := by
    intro l hl m hm hne
    exact (punctured_disjoint S hmeet x hl hm hne).mono inter_subset_left inter_subset_left
  rw [card_biUnion hdis]
  have hterm (l : Finset (Fin 157)) (hl : l ∈ through S x) : (l.erase x ∩ b).card = 1 := by
    obtain ⟨hlS, hlx⟩ := mem_filter.mp hl
    have hne : l ≠ b := fun e => hx (e ▸ hlx)
    obtain ⟨z, hz, huniq⟩ := hmeet l hlS b hb hne
    apply card_eq_one_iff_existsUnique.mpr
    refine ⟨z, mem_inter.mpr ⟨mem_erase.mpr ⟨?_, hz.1⟩, hz.2⟩, ?_⟩
    · intro e
      exact hx (e ▸ hz.2)
    · intro y hy
      exact huniq y ⟨(mem_erase.mp (mem_inter.mp hy).1).2, (mem_inter.mp hy).2⟩
  rw [sum_congr rfl hterm, sum_const]
  simp

private theorem through_unique_line {S : Lines} (hmeet : MeetsOnce S) {x y : Fin 157}
    (hne : x ≠ y) {b c : Finset (Fin 157)} (hbS : b ∈ S) (hcS : c ∈ S)
    (hb : x ∈ b ∧ y ∈ b) (hc : x ∈ c ∧ y ∈ c) : b = c := by
  by_contra hd
  obtain ⟨z, _, hu⟩ := hmeet b hbS c hcS hd
  exact hne ((hu x ⟨hb.1,hc.1⟩).trans (hu y ⟨hb.2,hc.2⟩).symm)

private theorem intersect_pencil_sum (S : Lines) (hmeet : MeetsOnce S) (x y : Fin 157) :
    (covered S x ∩ covered S y).card =
      (∑ b ∈ through S y, (covered S x ∩ b.erase y).card) +
        if y ∈ covered S x then 1 else 0 := by
  let P := (through S y).biUnion (fun b => b.erase y)
  have hnot : y ∉ covered S x ∩ P := fun h => center_not_covered S y (mem_inter.mp h).2
  have hdis : (↑(through S y) : Set (Finset (Fin 157))).PairwiseDisjoint
      (fun b => covered S x ∩ b.erase y) := by
    intro b hb c hc hne
    exact (punctured_disjoint S hmeet y hb hc hne).mono inter_subset_right inter_subset_right
  have hsum : (covered S x ∩ P).card =
      ∑ b ∈ through S y, (covered S x ∩ b.erase y).card := by
    dsimp [P]
    rw [inter_biUnion, card_biUnion hdis]
  change (covered S x ∩ insert y P).card = _
  by_cases h : y ∈ covered S x
  · rw [inter_insert_of_mem h, card_insert_of_notMem hnot, hsum, if_pos h]
  · rw [inter_insert_of_notMem h, hsum, if_neg h, add_zero]

theorem uncovered_common (S : Lines) (hunif : Uniform S) (hmeet : MeetsOnce S)
    {x y : Fin 157} (hne : x ≠ y) :
    ((uncovered S x ∩ uncovered S y).card : ℤ) =
      defect S x * defect S y +
      if y ∈ uncovered S x then 12 - defect S x - defect S y else 0 := by
  have hcompl : uncovered S x ∩ uncovered S y = univ \ (covered S x ∪ covered S y) := by
    ext z
    simp [uncovered, covered]
    tauto
  have hwhole : ((uncovered S x ∩ uncovered S y).card : ℤ) =
      157 - ((covered S x).card : ℤ) - ((covered S y).card : ℤ) +
      ((covered S x ∩ covered S y).card : ℤ) := by
    have h := card_sdiff_add_card_eq_card (subset_univ (covered S x ∪ covered S y))
    have h1 : ((uncovered S x ∩ uncovered S y).card : ℤ) +
        ((covered S x ∪ covered S y).card : ℤ) = 157 := by
      rw [hcompl]
      exact_mod_cast (by simpa using h :
        (univ \ (covered S x ∪ covered S y)).card + (covered S x ∪ covered S y).card = 157)
    have h2 := Finset.cast_card_inter (R := ℤ) (s := covered S x) (t := covered S y)
    linarith
  rw [hwhole, covered_count S hunif hmeet x, covered_count S hunif hmeet y]
  by_cases h : y ∈ uncovered S x
  · rw [if_pos h]
    have hnot : y ∉ covered S x := (mem_sdiff.mp h).2
    have hterm (l : Finset (Fin 157)) (hl : l ∈ through S y) :
        (covered S x ∩ l.erase y).card = (through S x).card := by
      obtain ⟨hlS, hly⟩ := mem_filter.mp hl
      have hxl : x ∉ l := fun hx => hnot (mem_covered.mpr (Or.inr ⟨l, hlS, hx, hly⟩))
      have he : covered S x ∩ l.erase y = covered S x ∩ l := by
        ext z
        simp only [mem_inter, mem_erase]
        constructor
        · exact fun h => ⟨h.1, h.2.2⟩
        · exact fun h => ⟨h.1, fun e => hnot (e ▸ h.1), h.2⟩
      rw [he, pencil_inter_line S hmeet x l hlS hxl]
    rw [intersect_pencil_sum S hmeet x y, if_neg hnot, add_zero, sum_congr rfl hterm, sum_const]
    simp only [defect, nsmul_eq_mul, Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat, Nat.cast_id]
    ring
  · rw [if_neg h, add_zero]
    have hmem : y ∈ covered S x := by
      by_contra! hn
      exact h (mem_sdiff.mpr ⟨mem_univ _, hn⟩)
    obtain ⟨L, hLS, hxL, hyL⟩ := (mem_covered.mp hmem).resolve_left hne.symm
    have hLQ : L ∈ through S y := mem_filter.mpr ⟨hLS, hyL⟩
    have hQ : 1 ≤ (through S y).card := card_pos.mpr ⟨L,hLQ⟩
    have hP : 1 ≤ (through S x).card := card_pos.mpr ⟨L, mem_filter.mpr ⟨hLS,hxL⟩⟩
    have ha : (covered S x ∩ L.erase y).card = 12 := by
      rw [inter_eq_right.mpr (erase_subset _ _ |>.trans (line_subset_covered hLS hxL)),
        card_erase_of_mem hyL, hunif L hLS]
    have hterm (l : Finset (Fin 157)) (hl : l ∈ (through S y).erase L) :
        (covered S x ∩ l.erase y).card = (through S x).card - 1 := by
      obtain ⟨hneL, hlQ⟩ := mem_erase.mp hl
      obtain ⟨hlS, hly⟩ := mem_filter.mp hlQ
      have hxl : x ∉ l := fun hx => hneL (through_unique_line hmeet hne hlS hLS ⟨hx,hly⟩ ⟨hxL,hyL⟩)
      have he : covered S x ∩ l.erase y = (covered S x ∩ l).erase y := by
        rw [inter_comm,erase_inter,inter_comm]
      rw [he, card_erase_of_mem (mem_inter.mpr ⟨hmem,hly⟩), pencil_inter_line S hmeet x l hlS hxl]
    rw [intersect_pencil_sum S hmeet x y, if_pos hmem,
      ← sum_erase_add (through S y) (fun l => (covered S x ∩ l.erase y).card) hLQ,
      ha, sum_congr rfl hterm, sum_const, card_erase_of_mem hLQ]
    simp only [defect, nsmul_eq_mul, Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat, Nat.cast_id,
      Nat.cast_sub hP, Nat.cast_sub hQ]
    ring

theorem uncovered_on_line (S : Lines) (hunif : Uniform S) (hmeet : MeetsOnce S)
    (x : Fin 157) {b : Finset (Fin 157)} (hb : b ∈ S) :
    ((uncovered S x ∩ b).card : ℤ) = if x ∈ b then 0 else defect S x := by
  have he : uncovered S x ∩ b = b \ covered S x := by
    ext z
    simp [uncovered, covered, and_comm]
  rw [he]
  by_cases hx : x ∈ b
  · rw [if_pos hx, sdiff_eq_empty_iff_subset.mpr (line_subset_covered hb hx), card_empty, Nat.cast_zero]
  · rw [if_neg hx, card_sdiff, pencil_inter_line S hmeet x b hb hx, hunif b hb,
      Nat.cast_sub (degree_le_thirteen S hunif hmeet x), defect]
    norm_num

private def mark (S : Lines) (j : ℤ) (x : Fin 157) : ℤ :=
  if defect S x = j then 1 else 0

private theorem mark_nonneg (S : Lines) (j : ℤ) (x : Fin 157) : 0 ≤ mark S j x := by
  unfold mark
  split <;> norm_num

private def Tally (S : Lines) (j : ℤ) : ℤ := ∑ x, mark S j x

private theorem tally_nonneg (S : Lines) (j : ℤ) : 0 ≤ Tally S j :=
  sum_nonneg (fun x _ => mark_nonneg S j x)

private theorem mark_le_tally (S : Lines) (j : ℤ) (x : Fin 157) :
    mark S j x ≤ Tally S j := single_le_sum (fun y _ => mark_nonneg S j y) (mem_univ x)

private theorem defect_cases_five (S : Lines) (hunif : Uniform S) (hmeet : MeetsOnce S)
    (hlo : 140 ≤ S.card) (hnone : ∀ x, defect S x ≠ 1) (x : Fin 157) :
    defect S x = 0 ∨ defect S x = 2 ∨ defect S x = 3 ∨ defect S x = 4 ∨ defect S x = 5 := by
  have hz := defect_nonneg S hunif hmeet x
  by_cases hx : defect S x = 0
  · exact Or.inl hx
  · have hu := positive_defect_bounded S hunif hmeet hnone (show 0 < defect S x by omega)
    have h := hnone x
    omega

private theorem tally_moment (S : Lines) (hunif : Uniform S) (hmeet : MeetsOnce S)
    (hlo : 140 ≤ S.card) (hnone : ∀ x, defect S x ≠ 1) :
    3 * Tally S 3 + 8 * Tally S 4 + 15 * Tally S 5 =
      (157 - (S.card : ℤ)) * (143 - (S.card : ℤ)) := by
  have hp (x : Fin 157) :
      defect S x ^ 2 - 2 * defect S x =
        3 * mark S 3 x + 8 * mark S 4 x + 15 * mark S 5 x := by
    rcases defect_cases_five S hunif hmeet hlo hnone x with h | h | h | h | h <;> norm_num [mark,h]
  have h := Finset.sum_congr (s₁ := (univ : Finset (Fin 157))) rfl (fun x _ => hp x)
  simp only [sum_sub_distrib, sum_add_distrib, ← mul_sum] at h
  rw [(defect_moments S hunif hmeet).1, (defect_moments S hunif hmeet).2] at h
  change (157 - (S.card : ℤ)) * (157 - (S.card : ℤ) + 12) -
    2 * (13 * (157 - (S.card : ℤ))) = 3 * Tally S 3 + 8 * Tally S 4 + 15 * Tally S 5 at h
  rw [← h]
  ring

private theorem tally_incidence (S : Lines) (j : ℤ) :
    (∑ b ∈ S, ∑ x ∈ b, mark S j x) = (13 - j) * Tally S j := by
  rw [← weighted_incidence, Tally, mul_sum]
  apply sum_congr rfl
  intro x _
  by_cases hx : defect S x = j
  · unfold defect at hx
    have he : ((through S x).card : ℤ) = 13 - j := by omega
    rw [he]
  · simp [mark, hx]

private theorem odd_mark_count (S : Lines) (hunif : Uniform S) (hmeet : MeetsOnce S)
    (hlo : 140 ≤ S.card) (hnone : ∀ x, defect S x ≠ 1) {b : Finset (Fin 157)}
    (hb : b ∈ S) (hodd : (157 - (S.card : ℤ)) % 2 = 1) :
    1 ≤ (∑ x ∈ b, mark S 3 x) + (∑ x ∈ b, mark S 5 x) := by
  have hp (x : Fin 157) : defect S x =
      2 * (defect S x / 2) + mark S 3 x + mark S 5 x := by
    rcases defect_cases_five S hunif hmeet hlo hnone x with h | h | h | h | h <;> norm_num [mark,h]
  have h := sum_congr (s₁ := b) rfl (fun x _ => hp x)
  simp only [sum_add_distrib, ← mul_sum] at h
  rw [defect_sum_on_line S hunif hmeet b hb] at h
  have h3 : 0 ≤ ∑ x ∈ b, mark S 3 x := sum_nonneg (fun x _ => mark_nonneg S 3 x)
  have h5 : 0 ≤ ∑ x ∈ b, mark S 5 x := sum_nonneg (fun x _ => mark_nonneg S 5 x)
  omega

private theorem marks_140 (S : Lines) (hunif : Uniform S) (hmeet : MeetsOnce S)
    (h140 : S.card = 140) (hnone : ∀ x, defect S x ≠ 1) :
    Tally S 3 = 17 ∧ Tally S 4 = 0 ∧ Tally S 5 = 0 := by
  have hlo : 140 ≤ S.card := h140.ge
  have hmoment := tally_moment S hunif hmeet hlo hnone
  norm_num [h140] at hmoment
  have hin := Finset.sum_le_sum (s := S) (fun b hb =>
    odd_mark_count S hunif hmeet hlo hnone hb (by norm_num [h140]))
  rw [sum_add_distrib, tally_incidence S 3, tally_incidence S 5, sum_const, nsmul_eq_mul, mul_one] at hin
  norm_num [h140] at hin
  have ha := tally_nonneg S 3
  have hb := tally_nonneg S 4
  have hc := tally_nonneg S 5
  have hsmall : 80 * Tally S 4 + 126 * Tally S 5 ≤ 90 := by linarith
  have hc0 : Tally S 5 = 0 := by omega
  have hb0 : Tally S 4 = 0 := by
    by_contra hn
    have h1 : Tally S 4 = 1 := by omega
    omega
  omega

private theorem uncovered_defect_positive (S : Lines) (hunif : Uniform S) (hmeet : MeetsOnce S)
    {x y : Fin 157} (hy : y ∈ uncovered S x) : 0 < defect S y := by
  obtain ⟨hyx, hy⟩ := mem_uncovered.mp hy
  have hxy : x ∈ uncovered S y := mem_uncovered.mpr ⟨Ne.symm hyx,
    fun ⟨b, hb, hby, hbx⟩ => hy ⟨b, hb, hbx, hby⟩⟩
  have hpos : 0 < (uncovered S y).card := card_pos.mpr ⟨x, hxy⟩
  have hc := uncovered_count S hunif hmeet y
  have hpos' : 0 < ((uncovered S y).card : ℤ) := by exact_mod_cast hpos
  omega

private theorem incidence_comm (S : Lines) (f : Fin 157 → Finset (Fin 157) → ℤ) :
    (∑ b ∈ S, ∑ x ∈ b, f x b) = ∑ x, ∑ b ∈ through S x, f x b := by
  classical
  calc
    _ = ∑ b ∈ S, ∑ x : Fin 157, if x ∈ b then f x b else 0 := by
      apply sum_congr rfl
      intro b _
      rw [← sum_filter]
      simp
    _ = _ := by rw [sum_comm]; simp only [through, sum_filter]

private theorem pencil_weight (S : Lines) (hmeet : MeetsOnce S) (x : Fin 157) (f : Fin 157 → ℤ) :
    (∑ b ∈ through S x, ∑ y ∈ b, f y) =
      ((through S x).card : ℤ) * f x + (∑ y, f y) - f x - (∑ y ∈ uncovered S x, f y) := by
  let U := (through S x).biUnion (fun b => b.erase x)
  have h1 (b : Finset (Fin 157)) (hb : b ∈ through S x) :
      (∑ y ∈ b, f y) = (∑ y ∈ b.erase x, f y) + f x :=
    (sum_erase_add b f (mem_filter.mp hb).2).symm
  have h2 := Finset.sum_sdiff (f := f) (subset_univ (insert x U))
  change (∑ y ∈ uncovered S x, f y) + (∑ y ∈ insert x U, f y) = ∑ y, f y at h2
  rw [sum_insert (center_not_covered S x)] at h2
  rw [sum_congr rfl h1, sum_add_distrib, sum_const, nsmul_eq_mul]
  rw [← sum_biUnion (punctured_disjoint S hmeet x)]
  change (∑ y ∈ U, f y) + ((through S x).card : ℤ) * f x = _
  linarith

theorem extend_140 (S : Lines) (hunif : Uniform S) (hmeet : MeetsOnce S)
    (h140 : S.card = 140) : ∃ T : Lines, S ⊆ T ∧ T.card = S.card + 1 ∧ Uniform T ∧ MeetsOnce T := by
  classical
  by_cases h1 : ∃ x, defect S x = 1
  · obtain ⟨x, hx⟩ := h1
    apply extend_at_twelve S hunif hmeet x
    unfold defect at hx
    change (through S x).card = 12
    omega
  push Not at h1
  obtain ⟨h3, h4, h5⟩ := marks_140 S hunif hmeet h140 h1
  let W := mark S 3
  let M := fun b : Finset (Fin 157) => ∑ x ∈ b, W x
  have hnot4 (x : Fin 157) : defect S x ≠ 4 := by
    intro h
    have := mark_le_tally S 4 x
    simp [mark,h,h4] at this
  have hnot5 (x : Fin 157) : defect S x ≠ 5 := by
    intro h
    have := mark_le_tally S 5 x
    simp [mark,h,h5] at this
  have hd (x : Fin 157) : defect S x = 0 ∨ defect S x = 2 ∨ defect S x = 3 := by
    have h := defect_cases_five S hunif hmeet h140.ge h1 x
    have := hnot4 x
    have := hnot5 x
    omega
  have hun (x : Fin 157) (hx : defect S x = 3) : (∑ y ∈ uncovered S x, W y) = 6 := by
    have hh (y : Fin 157) (hy : y ∈ uncovered S x) : defect S y = 2 + W y := by
      have hp := uncovered_defect_positive S hunif hmeet hy
      rcases hd y with h | h | h
      · omega
      · norm_num [W,mark,h]
      · norm_num [W,mark,h]
    have h := Finset.sum_congr rfl hh
    rw [sum_add_distrib, sum_const, nsmul_eq_mul,
      defect_sum_uncovered S hunif hmeet x, uncovered_count S hunif hmeet x] at h
    norm_num [hx,h140] at h
    omega
  have hlower (b : Finset (Fin 157)) (hb : b ∈ S) : 1 ≤ M b := by
    have ho := odd_mark_count S hunif hmeet h140.ge h1 hb (by norm_num [h140])
    simpa [M,W,mark,hnot5] using ho
  have hupper (b : Finset (Fin 157)) (hb : b ∈ S) : M b ≤ 5 := by
    have hp (x : Fin 157) : 3 * W x ≤ defect S x := by
      rcases hd x with h | h | h <;> norm_num [W,mark,h]
    have he := sum_le_sum (s := b) (fun x _ => hp x)
    rw [← mul_sum, defect_sum_on_line S hunif hmeet b hb] at he
    change 3 * M b ≤ 157 - ↑S.card at he
    omega
  have hsum1 : (∑ b ∈ S, M b) = 170 := by
    change (∑ b ∈ S, ∑ x ∈ b, mark S 3 x) = 170
    rw [tally_incidence, h3]
    norm_num
  have hsum2 : (∑ b ∈ S, (M b)^2) = 340 := by
    calc
      _ = ∑ b ∈ S, ∑ x ∈ b, W x * M b := by
        apply sum_congr rfl
        intro b _
        rw [← sum_mul,pow_two]
      _ = ∑ x, ∑ b ∈ through S x, W x * M b := incidence_comm S _
      _ = ∑ x, 20 * W x := by
        apply sum_congr rfl
        intro x _
        rw [← mul_sum]
        by_cases hx : defect S x = 3
        · have hr : ((through S x).card : ℤ) = 10 := by unfold defect at hx; omega
          change W x * (∑ b ∈ through S x, ∑ y ∈ b, W y) = _
          have hW : (∑ y, W y) = 17 := h3
          rw [pencil_weight S hmeet x W, hr, hW, hun x hx]
          norm_num [W,mark,hx]
        · simp [W,mark,hx]
      _ = _ := by
        rw [← mul_sum]
        change 20 * Tally S 3 = 340
        rw [h3]
        norm_num
  have hp (b : Finset (Fin 157)) (hb : b ∈ S) :
      (M b)^2 - M b ≤ 5 * (M b - 1) := by
    have h := mul_nonneg (sub_nonneg.mpr (hlower b hb)) (sub_nonneg.mpr (hupper b hb))
    nlinarith
  have hh := sum_le_sum hp
  simp only [mul_sub, mul_one, sum_sub_distrib, ← mul_sum] at hh
  rw [hsum2, hsum1, sum_const, nsmul_eq_mul, h140] at hh
  norm_num at hh

private def level (S : Lines) (j : ℤ) : Finset (Fin 157) :=
  univ.filter (fun x => defect S x = j)

private theorem mem_level {S : Lines} {j : ℤ} {x : Fin 157} :
    x ∈ level S j ↔ defect S x = j := by simp [level]

private theorem sum_mark_eq_card (S : Lines) (j : ℤ) (A : Finset (Fin 157)) :
    (∑ x ∈ A, mark S j x) = ((A ∩ level S j).card : ℤ) := by
  have he : A ∩ level S j = A.filter (fun x => defect S x = j) := by ext x; simp [mem_level]
  rw [he, card_filter, Nat.cast_sum]
  apply sum_congr rfl
  intro x _
  by_cases h : defect S x = j <;> simp [mark, h]

private theorem tally_level (S : Lines) (j : ℤ) : Tally S j = ((level S j).card : ℤ) := by
  rw [Tally, sum_mark_eq_card, univ_inter]

private theorem classes_141 (S : Lines) (hunif : Uniform S) (hmeet : MeetsOnce S)
    (h141 : S.card = 141) (hnone : ∀ x, defect S x ≠ 1) :
    (∀ x, defect S x = 0 ∨ defect S x = 2 ∨ defect S x = 4) ∧
      (level S 2).card = 96 ∧ (level S 4).card = 4 := by
  have hlo : 140 ≤ S.card := by omega
  have hc (x : Fin 157) : defect S x = 0 ∨ defect S x = 2 ∨ defect S x = 3 ∨ defect S x = 4 := by
    by_cases hzero : defect S x = 0
    · exact Or.inl hzero
    · have hpos := defect_nonneg S hunif hmeet x
      have h := positive_defect_bounded S hunif hmeet hnone (by omega : 0 < defect S x)
      have h1 := hnone x
      omega
  have h5 (x : Fin 157) : defect S x ≠ 5 := by have := hc x; omega
  have hT5 : Tally S 5 = 0 := by simp [Tally, mark, h5]
  have hmoment := tally_moment S hunif hmeet hlo hnone
  norm_num [h141, hT5] at hmoment
  have hT3max : Tally S 3 ≤ 10 := by have := tally_nonneg S 4; omega
  have heven (b : Finset (Fin 157)) (hb : b ∈ S) : (∑ x ∈ b, mark S 3 x) % 2 = 0 := by
    have hf (x : Fin 157) : defect S x = 2 * (defect S x / 2) + mark S 3 x := by
      rcases hc x with h | h | h | h <;> norm_num [mark,h]
    have hv := sum_congr (s₁ := b) rfl (fun x _ => hf x)
    rw [defect_sum_on_line S hunif hmeet b hb, sum_add_distrib, ← mul_sum] at hv
    norm_num [h141] at hv
    omega
  have h3 (x : Fin 157) : defect S x ≠ 3 := by
    intro hx
    have hr : ((through S x).card : ℤ) = 10 := by unfold defect at hx; omega
    have hline (b : Finset (Fin 157)) (hb : b ∈ through S x) :
        2 ≤ ∑ y ∈ b, mark S 3 y := by
      obtain ⟨hbS, hxb⟩ := mem_filter.mp hb
      have hm := single_le_sum (s := b) (fun y _ => mark_nonneg S 3 y) hxb
      have hx1 : mark S 3 x = 1 := by simp [mark,hx]
      rw [hx1] at hm
      have he := heven b hbS
      omega
    have hlo : 20 ≤ ∑ b ∈ through S x, ∑ y ∈ b, mark S 3 y := by
      have h := sum_le_sum hline
      rw [sum_const,nsmul_eq_mul,hr] at h
      norm_num at h
      exact h
    have h := pencil_weight S hmeet x (mark S 3)
    change (∑ b ∈ through S x, ∑ y ∈ b, mark S 3 y) =
      ((through S x).card : ℤ) * mark S 3 x + Tally S 3 - mark S 3 x -
      ∑ y ∈ uncovered S x, mark S 3 y at h
    have hx1 : mark S 3 x = 1 := by simp [mark,hx]
    rw [hr,hx1] at h
    have hsum : 0 ≤ ∑ y ∈ uncovered S x, mark S 3 y := sum_nonneg (fun y _ => mark_nonneg S 3 y)
    linarith
  have ht3 : Tally S 3 = 0 := by simp [Tally, mark, h3]
  have hc' (x : Fin 157) : defect S x = 0 ∨ defect S x = 2 ∨ defect S x = 4 := by
    have := hc x
    have := h3 x
    omega
  have ht4 : Tally S 4 = 4 := by omega
  have ht2 : Tally S 2 = 96 := by
    have hf (x : Fin 157) : defect S x = 2 * mark S 2 x + 4 * mark S 4 x := by
      rcases hc' x with h | h | h <;> norm_num [mark,h]
    have hj := sum_congr (s₁ := (univ : Finset (Fin 157))) rfl (fun x _ => hf x)
    rw [sum_add_distrib, ← mul_sum, ← mul_sum, (defect_moments S hunif hmeet).1] at hj
    change 13 * (157 - (S.card : ℤ)) = 2 * Tally S 2 + 4 * Tally S 4 at hj
    norm_num [h141,ht4] at hj
    omega
  rw [tally_level] at ht2 ht4
  exact ⟨hc',by exact_mod_cast ht2,by exact_mod_cast ht4⟩

private theorem local_classes_141 (S : Lines) (hunif : Uniform S) (hmeet : MeetsOnce S)
    (h141 : S.card = 141) (hc : ∀ x, defect S x = 0 ∨ defect S x = 2 ∨ defect S x = 4)
    (x : Fin 157) :
    (defect S x = 2 → (uncovered S x ∩ level S 2).card = 22 ∧ (uncovered S x ∩ level S 4).card = 2) ∧
    (defect S x = 4 → (uncovered S x ∩ level S 2).card = 48 ∧ (uncovered S x ∩ level S 4).card = 0) := by
  have hsel (y : Fin 157) (hy : y ∈ uncovered S x) : defect S y = 2 ∨ defect S y = 4 := by
    have := hc y
    have := uncovered_defect_positive S hunif hmeet hy
    omega
  have hsum :
      ((uncovered S x).card : ℤ) =
        ((uncovered S x ∩ level S 2).card : ℤ) + ((uncovered S x ∩ level S 4).card : ℤ) := by
    have h (y : Fin 157) (hy : y ∈ uncovered S x) :
        (1 : ℤ) = mark S 2 y + mark S 4 y := by
      rcases hsel y hy with e | e <;> norm_num [mark,e]
    have he := sum_congr rfl h
    simpa only [sum_const, nsmul_eq_mul, mul_one, sum_add_distrib, sum_mark_eq_card] using he
  have hweighted :
      defect S x * (157 - (S.card : ℤ) + 12 - defect S x) =
        2 * ((uncovered S x ∩ level S 2).card : ℤ) + 4 * ((uncovered S x ∩ level S 4).card : ℤ) := by
    have h (y : Fin 157) (hy : y ∈ uncovered S x) :
        defect S y = 2 * mark S 2 y + 4 * mark S 4 y := by
      rcases hsel y hy with e | e <;> norm_num [mark,e]
    have he := sum_congr rfl h
    rw [sum_add_distrib, ← mul_sum, ← mul_sum, sum_mark_eq_card, sum_mark_eq_card,
      defect_sum_uncovered S hunif hmeet x] at he
    exact he
  rw [uncovered_count S hunif hmeet x] at hsum
  constructor <;> intro hx <;> norm_num [hx,h141] at hsum hweighted <;> omega

private theorem extend_with_thirteen (S : Lines) (hunif : Uniform S) (hmeet : MeetsOnce S)
    (B : Finset (Fin 157)) (hB : B.card = 13)
    (hpair : ∀ x ∈ B, ∀ y ∈ B, x ≠ y → y ∈ uncovered S x)
    (hdeg : (∑ x ∈ B, ((through S x).card : ℤ)) = (S.card : ℤ)) :
    ∃ T : Lines, S ⊆ T ∧ T.card = S.card + 1 ∧ Uniform T ∧ MeetsOnce T := by
  classical
  have hcard (b : Finset (Fin 157)) (hb : b ∈ S) : (b ∩ B).card ≤ 1 := by
    apply card_le_one.mpr
    intro x hx y hy
    by_contra hne
    obtain ⟨hxb,hxB⟩ := mem_inter.mp hx
    obtain ⟨hyb,hyB⟩ := mem_inter.mp hy
    exact (mem_uncovered.mp (hpair x hxB y hyB hne)).2 ⟨b,hb,hxb,hyb⟩
  let f := fun x : Fin 157 => if x ∈ B then (1 : ℤ) else 0
  have hsum : (∑ b ∈ S, ((b ∩ B).card : ℤ)) = (S.card : ℤ) := by
    calc
      _ = ∑ b ∈ S, ∑ x ∈ b, f x := by
        apply sum_congr rfl
        intro b _
        change ((b.filter (· ∈ B)).card : ℤ) = _
        rw [card_filter,Nat.cast_sum]
        apply sum_congr rfl
        intro x _
        by_cases hx : x ∈ B <;> simp [hx,f]
      _ = ∑ x, ((through S x).card : ℤ) * f x := (weighted_incidence S f).symm
      _ = _ := by
        simp only [f,mul_ite,mul_one,mul_zero, ← sum_filter]
        rw [show (univ.filter (· ∈ B)) = B by ext x; simp]
        exact hdeg
  have hcount (b : Finset (Fin 157)) (hb : b ∈ S) : (b ∩ B).card = 1 := by
    by_contra hn
    have hzero : (b ∩ B).card = 0 := by have := hcard b hb; omega
    have hse := sum_erase_add S (fun c => ((c ∩ B).card : ℤ)) hb
    rw [hsum,hzero] at hse
    have hrest := sum_le_sum (s := S.erase b) (fun c hc =>
      show ((c ∩ B).card : ℤ) ≤ 1 by exact_mod_cast hcard c (mem_erase.mp hc).2)
    rw [sum_const,nsmul_eq_mul,mul_one] at hrest
    have hc := card_erase_add_one hb
    omega
  have hnot : B ∉ S := by
    intro hb
    have h := hcard B hb
    rw [inter_self,hB] at h
    norm_num at h
  have cross (b : Finset (Fin 157)) (hb : b ∈ S) : ∃! x, x ∈ b ∧ x ∈ B :=
    by simpa only [mem_inter] using card_eq_one_iff_existsUnique.mp (hcount b hb)
  refine ⟨insert B S, subset_insert _ _, card_insert_of_notMem hnot, ?_, ?_⟩
  · intro b hb
    rcases mem_insert.mp hb with e | h
    · exact e.symm ▸ hB
    · exact hunif b h
  · intro b hb c hc hne
    rcases mem_insert.mp hb with e | h
    · subst b
      rcases mem_insert.mp hc with e | h
      · exact (hne e.symm).elim
      · simpa only [and_comm] using cross c h
    · rcases mem_insert.mp hc with e | h'
      · subst c
        exact cross b h
      · exact hmeet b h c h' hne

private def residueSign (a : ℤ) : ℤ :=
  if 0 < a % 8 ∧ a % 8 < 4 then 1 else if 4 < a % 8 then -1 else 0

private theorem residueSign_alt (a b : ℤ) (h : (a + b) % 8 = 0) :
    residueSign a + residueSign b = 0 := by
  have ha : 0 ≤ a % 8 := Int.emod_nonneg _ (by decide)
  have hb : 0 ≤ b % 8 := Int.emod_nonneg _ (by decide)
  have ha' : a % 8 < 8 := Int.emod_lt_of_pos _ (by decide)
  have hb' : b % 8 < 8 := Int.emod_lt_of_pos _ (by decide)
  have hsum : a % 8 + b % 8 = 0 ∨ a % 8 + b % 8 = 8 := by
    have hh : (a % 8 + b % 8) % 8 = 0 := by rwa [← Int.add_emod]
    omega
  unfold residueSign
  split_ifs <;> omega

private theorem residueSign_zero (a : ℤ) (h : residueSign a = 0) : a % 8 = 0 ∨ a % 8 = 4 := by
  have ha : 0 ≤ a % 8 := Int.emod_nonneg _ (by decide)
  unfold residueSign at h
  split_ifs at h <;> omega


private theorem extend_141 (S : Lines) (hunif : Uniform S) (hmeet : MeetsOnce S)
    (h141 : S.card = 141) : ∃ T : Lines, S ⊆ T ∧ T.card = S.card + 1 ∧ Uniform T ∧ MeetsOnce T := by
  classical
  by_cases h1 : ∃ x, defect S x = 1
  · obtain ⟨x,hx⟩ := h1
    apply extend_at_twelve S hunif hmeet x
    unfold defect at hx
    change (through S x).card = 12
    omega
  push Not at h1
  obtain ⟨hc,hA,hP⟩ := classes_141 S hunif hmeet h141 h1
  let A := level S 2
  let P := level S 4
  let r : Fin 157 → Fin 157 → Prop := fun x y => y ∈ uncovered S x
  have Ar (x : Fin 157) (hx : x ∈ A) : defect S x = 2 := mem_level.mp hx
  have Pr (x : Fin 157) (hx : x ∈ P) : defect S x = 4 := mem_level.mp hx
  have sym : ∀ ⦃x y⦄, r x y → r y x := by
    intro x y h
    obtain ⟨hn,h⟩ := mem_uncovered.mp h
    exact mem_uncovered.mpr ⟨Ne.symm hn, fun ⟨b,hb,hy,hx⟩ => h ⟨b,hb,hx,hy⟩⟩
  have irr (x : Fin 157) : ¬r x x := fun h => (mem_uncovered.mp h).1 rfl
  have nbEq (x : Fin 157) : PlaneLocalGraph.nb r A x = uncovered S x ∩ A := by
    ext y
    simp [PlaneLocalGraph.nb,r,and_comm]
  have nbCommon (x y : Fin 157) :
      PlaneLocalGraph.nb r A x ∩ PlaneLocalGraph.nb r A y =
        (uncovered S x ∩ uncovered S y) ∩ A := by
    ext z
    simp only [nbEq,mem_inter]
    tauto
  have split_card (x : Fin 157) (B : Finset (Fin 157)) (hB : B ⊆ uncovered S x) :
      (B.card : ℤ) = ((B ∩ A).card : ℤ) + ((B ∩ P).card : ℤ) := by
    have h (y : Fin 157) (hy : y ∈ B) : (1 : ℤ) = mark S 2 y + mark S 4 y := by
      have hp := uncovered_defect_positive S hunif hmeet (hB hy)
      rcases hc y with h | h | h
      · omega
      · norm_num [mark,h]
      · norm_num [mark,h]
    have hs := sum_congr rfl h
    simpa only [sum_const, nsmul_eq_mul, mul_one,sum_add_distrib,sum_mark_eq_card] using hs
  have hAd (x : Fin 157) (hx : x ∈ A) :
      (PlaneLocalGraph.nb r A x).card = 22 := by
    rw [nbEq]
    exact ((local_classes_141 S hunif hmeet h141 hc x).1 (Ar x hx)).1
  have happ (x : Fin 157) (hx : x ∈ A) (y : Fin 157) (hy : y ∈ A)
      (hxy : r x y) :
      10 ≤ (PlaneLocalGraph.nb r A x ∩ PlaneLocalGraph.nb r A y).card ∧
        (PlaneLocalGraph.nb r A x ∩ PlaneLocalGraph.nb r A y).card ≤ 12 := by
    have hn : x ≠ y := fun e => irr x (e.symm ▸ hxy)
    have hraw := uncovered_common S hunif hmeet hn
    change y ∈ uncovered S x at hxy
    norm_num [Ar x hx, Ar y hy,hxy] at hraw
    have hpart := split_card x (uncovered S x ∩ uncovered S y) inter_subset_left
    have hPbound : ((uncovered S x ∩ uncovered S y) ∩ P).card ≤ 2 := by
      have hsub : (uncovered S x ∩ uncovered S y) ∩ P ⊆ uncovered S x ∩ P := by
        intro z hz
        exact mem_inter.mpr ⟨(mem_inter.mp (mem_inter.mp hz).1).1,(mem_inter.mp hz).2⟩
      exact (card_le_card hsub).trans_eq ((local_classes_141 S hunif hmeet h141 hc x).1 (Ar x hx)).2
    rw [nbCommon]
    omega
  have hsep (x : Fin 157) (hx : x ∈ A) (y : Fin 157) (hy : y ∈ A)
      (hne : x ≠ y) (hn : ¬r x y) :
      (PlaneLocalGraph.nb r A x ∩ PlaneLocalGraph.nb r A y).card ≤ 4 := by
    change y ∉ uncovered S x at hn
    have hraw := uncovered_common S hunif hmeet hne
    norm_num [Ar x hx, Ar y hy,hn] at hraw
    rw [nbCommon]
    have h := card_le_card (show (uncovered S x ∩ uncovered S y) ∩ A ⊆ _ from inter_subset_left)
    omega
  obtain ⟨K,hK,cl,partner,pairOn,tot⟩ :=
    PlaneLocalGraph.star_cover r A hA sym irr hAd happ hsep
  have hK19 : K.card ≤ 19 := by omega
  have hmin (C : Finset (Fin 157)) (hC : C ∈ K) : 10 ≤ C.card := by have := (cl C hC).2.1; omega
  let a := fun s C => ((C ∩ uncovered S s).card : ℤ)
  have hPonly (s : Fin 157) (hs : s ∈ P) : uncovered S s ⊆ A := by
    intro z hz
    have hz0 := uncovered_defect_positive S hunif hmeet hz
    have hzClass := hc z
    apply mem_level.mpr
    by_contra hnot
    have hz4 : defect S z = 4 := by omega
    have he := ((local_classes_141 S hunif hmeet h141 hc s).2 (Pr s hs)).2
    change (uncovered S s ∩ P).card = 0 at he
    exact (not_lt_of_ge he.le)
      (card_pos.mpr ⟨z,mem_inter.mpr ⟨hz,mem_level.mpr hz4⟩⟩)
  have star_sum (B C D : Finset (Fin 157)) (hC : C ∈ K) (hD : D ∈ K) (hne : C ≠ D)
      (x : Fin 157) (hx : x ∈ C) (hy : x ∈ D) :
      ((C ∩ B).card : ℤ) + ((D ∩ B).card : ℤ) =
        (if x ∈ B then 2 else 0) + ((PlaneLocalGraph.nb r A x ∩ B).card : ℤ) := by
    obtain ⟨hunion,hint⟩ := pairOn C hC D hD hne x hx hy
    have heu : (C ∩ B) ∪ (D ∩ B) = (C ∪ D) ∩ B := by ext z; simp only [mem_union,mem_inter]; tauto
    have hei : (C ∩ B) ∩ (D ∩ B) = (C ∩ D) ∩ B := by ext z; simp only [mem_inter]; tauto
    have he := card_union_add_card_inter (C ∩ B) (D ∩ B)
    rw [heu,hei,hunion,hint] at he
    by_cases hxB : x ∈ B
    · have hsub : x ∉ PlaneLocalGraph.nb r A x ∩ B := fun h => irr x ((PlaneLocalGraph.mem_nb r).mp (mem_inter.mp h).1).2
      have hs : {x} ∩ B = {x} := inter_eq_left.mpr (singleton_subset_iff.mpr hxB)
      rw [insert_inter_of_mem hxB,card_insert_of_notMem hsub,hs,card_singleton] at he
      rw [if_pos hxB]
      omega
    · have hs : {x} ∩ B = ∅ := by
        ext z
        simp only [mem_inter,mem_singleton,notMem_empty,iff_false]
        rintro ⟨rfl,h⟩
        exact hxB h
      rw [insert_inter_of_notMem hxB,hs,card_empty] at he
      rw [if_neg hxB]
      omega
  have a_edge (s : Fin 157) (hs : s ∈ P) (C : Finset (Fin 157)) (hC : C ∈ K) (D : Finset (Fin 157))
      (hD : D ∈ K) (hne : C ≠ D) (x : Fin 157) (hx : x ∈ C) (hy : x ∈ D) :
      a s C + a s D = 8 + (if x ∈ uncovered S s then 8 else 0) := by
    have hxA := (cl C hC).1 hx
    have hxs : x ≠ s := by intro e; have h := Ar x hxA; rw [e,Pr s hs] at h; norm_num at h
    have hraw := uncovered_common S hunif hmeet hxs
    have h := star_sum (uncovered S s) C D hC hD hne x hx hy
    have he : PlaneLocalGraph.nb r A x ∩ uncovered S s = uncovered S x ∩ uncovered S s := by
      rw [nbEq]
      ext y
      simp only [mem_inter]
      exact ⟨fun h => ⟨h.1.1,h.2⟩,fun h => ⟨⟨h.1,hPonly s hs h.2⟩,h.2⟩⟩
    rw [he] at h
    change a s C + a s D = _ at h
    by_cases hsx : x ∈ uncovered S s
    · have hxs : s ∈ uncovered S x := sym hsx
      norm_num [Ar x hxA,Pr s hs,hxs,hsx] at hraw h ⊢
      omega
    · have hxs : s ∉ uncovered S x := fun e => hsx (sym e)
      norm_num [Ar x hxA,Pr s hs,hxs,hsx] at hraw h ⊢
      omega
  by_cases h12 : ∃ s ∈ P, ∃ C ∈ K, a s C = 12
  · obtain ⟨s,hs,C,hC,ha⟩ := h12
    obtain ⟨hCA,hC12,hClique⟩ := cl C hC
    have hsC : s ∉ C := by intro e; have h := Ar s (hCA e); rw [Pr s hs] at h; norm_num at h
    have hcard : (C ∩ uncovered S s).card = C.card := by
      change ((C ∩ uncovered S s).card : ℤ) = 12 at ha
      omega
    have he := eq_of_subset_of_card_le (show C ∩ uncovered S s ⊆ C from inter_subset_left) hcard.ge
    have hsub : C ⊆ uncovered S s := fun _ hx => (mem_inter.mp (he.symm ▸ hx)).2
    apply extend_with_thirteen S hunif hmeet (insert s C)
    · rw [card_insert_of_notMem hsC,hC12]
    · intro x hx y hy hne
      rcases mem_insert.mp hx with e | hxC
      · subst x
        rcases mem_insert.mp hy with e | hyC
        · exact (hne e.symm).elim
        · exact hsub hyC
      · rcases mem_insert.mp hy with e | hyC
        · subst y
          exact sym (hsub hxC)
        · exact hClique x hxC y hyC hne
    · have hs9 : ((through S s).card : ℤ) = 9 := by have h := Pr s hs; unfold defect at h; omega
      have hd (x : Fin 157) (hx : x ∈ C) : ((through S x).card : ℤ) = 11 := by
        have h := Ar x (hCA hx)
        unfold defect at h
        omega
      rw [sum_insert hsC,hs9,sum_congr rfl hd,sum_const,nsmul_eq_mul,hC12,h141]
      norm_num
  push Not at h12
  have hmod (s : Fin 157) (hs : s ∈ P) (C : Finset (Fin 157)) (hC : C ∈ K) (D : Finset (Fin 157))
      (hD : D ∈ K) (hne : C ≠ D) (x : Fin 157) (hx : x ∈ C) (hy : x ∈ D) :
      (a s C + a s D) % 8 = 0 := by
    rw [a_edge s hs C hC D hD hne x hx hy]
    split <;> decide
  have residues (s : Fin 157) (hs : s ∈ P) : ∀ C ∈ K, a s C % 8 = 0 := by
    have hv := PlaneCliqueCount.alternating_vanish K hK19 hmin partner
      (fun C => residueSign (a s C)) (fun C hC D hD hn x hx hy =>
        residueSign_alt _ _ (hmod s hs C hC D hD hn x hx hy))
    have hres (C : Finset (Fin 157)) (hC : C ∈ K) : a s C % 8 = 0 ∨ a s C % 8 = 4 :=
      residueSign_zero _ (hv C hC)
    intro C hC
    rcases hres C hC with h | h
    · exact h
    · have hsame : ∀ D ∈ K, a s D % 8 = 4 := by
        have aux := PlaneCliqueCount.constant_predicate K hK19 hmin partner
          (fun D => a s D % 8 = 4) (by
            intro X hX Y hY hn x hx hy
            have he := hmod s hs X hX Y hY hn x hx hy
            omega)
        intro D hD
        exact (aux C hC D hD).mp h
      have hsmall (D : Finset (Fin 157)) (hD : D ∈ K) : a s D = 4 := by
        have hul := card_le_card (show D ∩ uncovered S s ⊆ D from inter_subset_left)
        rw [(cl D hD).2.1] at hul
        have hzero : 0 ≤ a s D := by dsimp [a]; positivity
        have ht := hsame D hD
        have hnot := h12 s hs D hD
        dsimp [a] at hzero ht hnot ⊢
        omega
      have hsum := tot (uncovered S s)
      rw [inter_eq_right.mpr (hPonly s hs)] at hsum
      have hx := ((local_classes_141 S hunif hmeet h141 hc s).2 (Pr s hs)).1
      rw [inter_eq_left.mpr (hPonly s hs)] at hx
      change (∑ D ∈ K, a s D) = _ at hsum
      rw [sum_congr rfl hsmall,sum_const,nsmul_eq_mul,hK,hx] at hsum
      norm_num at hsum
  have lineEven (b : Finset (Fin 157)) (hb : b ∈ S) : ((P ∩ b).card : ℤ) % 2 = 0 := by
    let Q := P ∩ b
    let F := fun C : Finset (Fin 157) =>
      8 * ((C ∩ b).card : ℤ) + (∑ s ∈ Q, a s C) - 4 * (Q.card : ℤ) - 8
    have halt (C : Finset (Fin 157)) (hC : C ∈ K) (D : Finset (Fin 157)) (hD : D ∈ K)
        (hne : C ≠ D) (x : Fin 157) (hx : x ∈ C) (hy : x ∈ D) : F C + F D = 0 := by
      have hs := star_sum b C D hC hD hne x hx hy
      have hbCounts := uncovered_on_line S hunif hmeet x hb
      have hxA := (cl C hC).1 hx
      rw [Ar x hxA] at hbCounts
      have hsplit := split_card x (uncovered S x ∩ b) inter_subset_left
      have hcor : PlaneLocalGraph.nb r A x ∩ b = (uncovered S x ∩ b) ∩ A := by
        rw [nbEq]
        ext y
        simp only [mem_inter]
        tauto
      rw [hcor] at hs
      have hsQ :
          (∑ s ∈ Q, a s C) + (∑ s ∈ Q, a s D) =
            8 * (Q.card : ℤ) + 8 * (((uncovered S x ∩ b) ∩ P).card : ℤ) := by
        rw [← sum_add_distrib]
        have ht (s : Fin 157) (hs : s ∈ Q) :
            a s C + a s D = 8 + 8 * (if s ∈ uncovered S x then 1 else 0) := by
          rw [a_edge s (mem_inter.mp hs).1 C hC D hD hne x hx hy]
          by_cases h : s ∈ uncovered S x
          · have hs' : x ∈ uncovered S s := sym (x := x) (y := s) h
            simp [h,hs']
          · have hs' : x ∉ uncovered S s := fun he => h (sym (x := s) (y := x) he)
            simp [h,hs']
        rw [sum_congr rfl ht,sum_add_distrib,sum_const,nsmul_eq_mul,← mul_sum]
        have he : (((uncovered S x ∩ b) ∩ P).card : ℤ) =
            (∑ s ∈ Q, if s ∈ uncovered S x then (1 : ℤ) else 0) := by
          have he : (uncovered S x ∩ b) ∩ P = Q.filter (· ∈ uncovered S x) := by
            ext y
            simp only [Q,mem_inter,mem_filter]
            tauto
          rw [he,card_filter,Nat.cast_sum]
          apply sum_congr rfl
          intro y _
          split <;> norm_num
        rw [he,mul_comm (Q.card : ℤ) 8]
      dsimp only [F]
      by_cases hxB : x ∈ b
      · rw [if_pos hxB] at hs hbCounts
        linarith
      · rw [if_neg hxB] at hs hbCounts
        linarith
    have hF := PlaneCliqueCount.alternating_vanish K hK19 hmin partner F halt
    obtain ⟨C,hC⟩ := card_pos.mp (show 0 < K.card by omega)
    have h := hF C hC
    have hdvd : (8 : ℤ) ∣ ∑ s ∈ Q, a s C := by
      apply Finset.dvd_sum
      intro s hs
      exact Int.dvd_iff_emod_eq_zero.mpr (residues s (mem_inter.mp hs).1 C hC)
    dsimp only [F] at h
    change (Q.card : ℤ) % 2 = 0
    omega
  obtain ⟨s,hs⟩ := card_pos.mp (show 0 < P.card by rw [show P.card = 4 from hP]; decide)
  have hs9 : ((through S s).card : ℤ) = 9 := by have h := Pr s hs; unfold defect at h; omega
  have hmark (b : Finset (Fin 157)) (hb : b ∈ through S s) : 2 ≤ ∑ x ∈ b, mark S 4 x := by
    obtain ⟨hbS,hsb⟩ := mem_filter.mp hb
    rw [sum_mark_eq_card,inter_comm]
    change (2 : ℤ) ≤ ((P ∩ b).card : ℤ)
    have hp : 0 < (P ∩ b).card := card_pos.mpr ⟨s,mem_inter.mpr ⟨hs,hsb⟩⟩
    have he := lineEven b hbS
    omega
  have hlo := sum_le_sum hmark
  rw [sum_const,nsmul_eq_mul,hs9] at hlo
  have hup := pencil_weight S hmeet s (mark S 4)
  have hs1 : mark S 4 s = 1 := by simp [mark,Pr s hs]
  have ht : (∑ x, mark S 4 x) = 4 := by change Tally S 4 = 4; rw [tally_level]; exact_mod_cast hP
  rw [hs9,hs1,ht] at hup
  have hnonneg : 0 ≤ ∑ x ∈ uncovered S s, mark S 4 x := sum_nonneg (fun x _ => mark_nonneg S 4 x)
  linarith

end PartialPlane12

theorem OMA.solution : OMA.R_Erdos723_erdos_723_variants_eq_12_R1_H1_R1.H2 := by
  intro S hlo hhi hu hm
  have h : S.card = 140 ∨ S.card = 141 ∨ S.card = 142 := by omega
  rcases h with h | h | h
  · exact PartialPlane12.extend_140 S hu hm h
  · exact PartialPlane12.extend_141 S hu hm h
  · exact PartialPlane12.extend_142 S hu hm h