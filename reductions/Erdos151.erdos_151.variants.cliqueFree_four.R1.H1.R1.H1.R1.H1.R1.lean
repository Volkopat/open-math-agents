import OMAReductions.R_Erdos151_erdos_151_variants_cliqueFree_four_R1_H1_R1_H1_R1
import Mathlib

/-! Three-anchor induced-path overlap reduction closing H(n) = 11 (all n <= R(3,12)-1)
for K_4-free Erdos Problem 151, pushing the residual open core to H(n) >= 12. -/

open Finset SimpleGraph
open scoped Classical

namespace OMA.R_Erdos151_erdos_151_variants_cliqueFree_four_R1_H1_R1_H1_R1_H1_R1

/-- Residual open core at H(n) >= 12 (n >= R(3,12) >= 52). -/
def H1 : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)), G.CliqueFree 4 →
    12 ≤ Erdos151.H n →
    (∀ v, (univ.filter (G.Adj v)).card < Erdos151.H n) →
    (∃ S : Finset (Fin n), S.Nonempty ∧
      ∀ v ∈ S, 8 ≤ (S.filter (G.Adj v)).card) →
    cliqueTransversalNumber G ≤ n - Erdos151.H n

/-- Ramsey upper bound R(3,8) <= 28. -/
def H2 : Prop := 8 ≤ Erdos151.H 28

/-- Ramsey lower bound R(3,11) >= 47 (witnessed by Exoo 46-vertex graph). -/
def H3 : Prop := ∀ n, 11 ≤ Erdos151.H n → 47 ≤ n

/-- Bikov 7-vertex link-extension lemma. -/
def H4 : Prop :=
  ∀ (k : ℕ) (L : SimpleGraph (Fin k)), k ≤ 7 → L.CliqueFree 3 →
    ∀ c : Fin k → Fin k → Bool, (∀ x y, c x y = c y x) →
      ∃ d : Fin k → Bool, ∀ x y, L.Adj x y → ¬ (d x = c x y ∧ d y = c x y)

section Proof

-- === BEGIN HELPERS ===
private lemma transversal_le_of_free {n k : ℕ} (G : SimpleGraph (Fin n))
    (B : Finset (Fin n)) (hB : k ≤ B.card)
    (hfree : ∀ K : Finset (Fin n), G.IsBigMaximalClique K → ¬ (K ⊆ B)) :
    G.cliqueTransversalNumber ≤ n - k := by
  classical
  have hT : G.IsCliqueTransversal (Finset.univ \ B) := by
    intro K hK
    by_contra h
    apply hfree K hK
    intro x hx
    by_contra hxB
    exact h ⟨x, hx, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hxB⟩⟩
  have hm : (Finset.univ \ B).card ∈
      {j : ℕ | ∃ T : Finset (Fin n), G.IsCliqueTransversal T ∧ T.card = j} :=
    ⟨_, hT, rfl⟩
  have hs := Nat.sInf_le hm
  change G.cliqueTransversalNumber ≤ (Finset.univ \ B).card at hs
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ B)] at hs
  simp only [Finset.card_univ, Fintype.card_fin] at hs
  omega

private lemma free_of_coloring {n : ℕ} (G : SimpleGraph (Fin n))
    (c : Fin n → Fin n → Bool) (hs : ∀ x y, c x y = c y x)
    (hc : ∀ x y z, G.Adj x y → G.Adj x z → G.Adj y z →
      ¬ (c x y = c x z ∧ c x y = c y z)) :
    ∃ B : Finset (Fin n), Erdos151.H n ≤ B.card ∧
      ∀ K : Finset (Fin n), G.IsBigMaximalClique K → ¬ (K ⊆ B) := by
  classical
  let F : SimpleGraph (Fin n) := {
    Adj := fun x y => G.Adj x y ∧ (c x y = true ∨ ¬ ∃ w, G.Adj x w ∧ G.Adj y w)
    symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.elim (fun h => Or.inl ((hs _ _).trans h))
      (fun h => Or.inr (fun ⟨w, hw, hw'⟩ => h ⟨w, hw', hw⟩))⟩⟩
    loopless := ⟨fun _ h => G.irrefl h.1⟩ }
  have hF : F.CliqueFree 3 := by
    intro t h
    obtain ⟨x, y, z, hxy, hxz, hyz, -⟩ := is3Clique_iff.mp h
    have hxyt : c x y = true := hxy.2.resolve_right (fun h => h ⟨z, hxz.1, hyz.1⟩)
    have hxzt : c x z = true := hxz.2.resolve_right (fun h => h ⟨y, hxy.1, hyz.1.symm⟩)
    have hyzt : c y z = true := hyz.2.resolve_right (fun h => h ⟨x, hxy.1.symm, hxz.1.symm⟩)
    exact hc x y z hxy.1 hxz.1 hyz.1 ⟨hxyt.trans hxzt.symm, hxyt.trans hyzt.symm⟩
  have hAtt : ∃ s, F.IsNIndepSet (Erdos151.H n) s := by
    let sizes : Set ℕ :=
      {k | ∀ Q : SimpleGraph (Fin n), Q.CliqueFree 3 → ∃ s, Q.IsNIndepSet k s}
    have hnonempty : sizes.Nonempty := ⟨0, fun _ _ => ⟨∅, by simp [SimpleGraph.isNIndepSet_iff]⟩⟩
    have hfinite : sizes.Finite := (Set.finite_Iic n).subset fun k hk => by
      obtain ⟨s, hs⟩ := hk F hF
      simpa [hs.card_eq] using Finset.card_le_univ s
    exact hnonempty.csSup_mem hfinite F hF
  obtain ⟨I, hI⟩ := hAtt
  refine ⟨I, hI.card_eq.ge, ?_⟩
  intro t ht htI
  have hNo {x y : Fin n} (hx : x ∈ t) (hy : y ∈ t) (hxy : G.Adj x y) : c x y = false := by
    cases hb : c x y
    · rfl
    · exact (hI.isIndepSet (htI hx) (htI hy) hxy.ne ⟨hxy, Or.inl hb⟩).elim
  have hNotThree : t.card < 3 := by
    by_contra! hLarge
    obtain ⟨u, hu, huC⟩ := exists_subset_card_eq hLarge
    have hClique : G.IsNClique 3 u :=
      ⟨fun _ hx _ hy hxy => ht.1.1 (hu hx) (hu hy) hxy, huC⟩
    obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := is3Clique_iff.mp hClique
    have hx : x ∈ t := hu (by simp)
    have hy : y ∈ t := hu (by simp)
    have hz : z ∈ t := hu (by simp)
    have h1 := hNo hx hy hxy
    have h2 := hNo hx hz hxz
    have h3 := hNo hy hz hyz
    exact hc x y z hxy hxz hyz ⟨h1.trans h2.symm, h1.trans h3.symm⟩
  have hTwo : t.card = 2 := by have := ht.2; omega
  obtain ⟨x, y, hxy, htxy⟩ := card_eq_two.mp hTwo
  have hx : x ∈ t := by simp [htxy]
  have hy : y ∈ t := by simp [htxy]
  have hAdj := ht.1.1 hx hy hxy
  have hN : ¬ ∃ w, G.Adj x w ∧ G.Adj y w := by
    rintro ⟨w, hwx, hwy⟩
    have hSub : G.IsClique (↑(insert w t) : Set (Fin n)) := by
      rw [coe_insert]
      apply ht.1.1.insert
      intro u hu _
      have : u = x ∨ u = y := by simpa [htxy] using hu
      exact this.elim (fun h => h ▸ hwx.symm) (fun h => h ▸ hwy.symm)
    have hwMem : w ∈ t := ht.1.2 hSub (subset_insert _ _) (mem_insert_self _ _)
    have : w = x ∨ w = y := by simpa [htxy] using hwMem
    exact this.elim hwx.ne.symm hwy.ne.symm
  exact hI.isIndepSet (htI hx) (htI hy) hxy ⟨hAdj, Or.inr hN⟩

private lemma beta_of_coloring_28 (h2 : H2) (h4 : H4)
    {n : ℕ} (G : SimpleGraph (Fin n)) (hG : G.CliqueFree 4)
    (R : Finset (Fin n)) (hR : 28 ≤ R.card) :
    ∃ B : Finset (Fin n), B ⊆ R ∧ 8 ≤ B.card ∧
      ∀ K : Finset (Fin n), G.IsBigMaximalClique K → ¬ (K ⊆ B) := by
  classical
  obtain ⟨S, hSR, hS⟩ := Finset.exists_subset_card_eq hR
  let E : Fin 28 ≃ ↥S := (Fintype.equivFinOfCardEq (by simpa using hS)).symm
  let e : Fin 28 ↪ Fin n :=
    ⟨fun i => (E i).val, fun _ _ h => E.injective (Subtype.ext h)⟩
  let Q : SimpleGraph (Fin 28) := {
    Adj := fun i j => G.Adj (e i) (e j)
    symm := ⟨fun _ _ h => G.symm.symm _ _ h⟩
    loopless := ⟨fun _ h => G.irrefl h⟩ }
  have mapClique (U : Finset (Fin 28)) (hU : Q.IsClique (↑U : Set (Fin 28))) :
      G.IsClique (↑(U.map e) : Set (Fin n)) := by
    intro a ha b hb hab
    obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp (show a ∈ U.map e from ha)
    obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp (show b ∈ U.map e from hb)
    exact hU hi hj (fun h => hab (congrArg (fun k => e k) h))
  have hQ : Q.CliqueFree 4 := by
    intro U hU
    exact hG (U.map e) ⟨mapClique U hU.1, by simpa only [Finset.card_map] using hU.2⟩
  have noFour (w x y z : Fin 28) (hwx : Q.Adj w x) (hwy : Q.Adj w y)
      (hwz : Q.Adj w z) (hxy : Q.Adj x y) (hxz : Q.Adj x z) (hyz : Q.Adj y z) : False := by
    have hwN : w ∉ ({x, y, z} : Finset (Fin 28)) := by
      simp [hwx.ne, hwy.ne, hwz.ne]
    have hxN : x ∉ ({y, z} : Finset (Fin 28)) := by
      simp [hxy.ne, hxz.ne]
    have hyN : y ∉ ({z} : Finset (Fin 28)) := by simp [hyz.ne]
    apply hQ ({w, x, y, z} : Finset (Fin 28))
    constructor
    · intro a ha b hb hab
      simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at ha hb
      rcases ha with rfl | rfl | rfl | rfl <;>
        rcases hb with rfl | rfl | rfl | rfl <;>
        first | exact (hab rfl).elim | assumption | exact Q.symm.symm _ _ (by assumption)
    · rw [Finset.card_insert_of_notMem hwN, Finset.card_insert_of_notMem hxN,
        Finset.card_insert_of_notMem hyN]
      simp
  have hfree : ∃ B : Finset (Fin 28), 8 ≤ B.card ∧
      ∀ K : Finset (Fin 28), Q.IsBigMaximalClique K → ¬ (K ⊆ B) := by
    by_cases hlarge : ∃ w : Fin 28, 8 ≤ (Finset.univ.filter (Q.Adj w)).card
    · obtain ⟨w, hw⟩ := hlarge
      refine ⟨Finset.univ.filter (Q.Adj w), hw, ?_⟩
      intro K hK hKN
      have hc : Q.IsClique (↑(insert w K) : Set (Fin 28)) := by
        rw [Finset.coe_insert]
        apply hK.1.1.insert
        intro a ha _
        exact (Finset.mem_filter.mp (hKN ha)).2
      have hwK : w ∈ K := hK.1.2 hc (Finset.subset_insert _ _) (Finset.mem_insert_self _ _)
      exact Q.irrefl (Finset.mem_filter.mp (hKN hwK)).2
    · let Good (U : Finset (Fin 28)) (c : Fin 28 → Fin 28 → Bool) : Prop :=
        ∀ x y z, x ∈ U → y ∈ U → z ∈ U → Q.Adj x y → Q.Adj x z → Q.Adj y z →
          ¬ (c x y = c x z ∧ c x y = c y z)
      have build (U : Finset (Fin 28)) :
          ∃ c : Fin 28 → Fin 28 → Bool, (∀ x y, c x y = c y x) ∧ Good U c := by
        induction U using Finset.induction_on with
        | empty =>
          refine ⟨fun _ _ => false, fun _ _ => rfl, ?_⟩
          intro x y z hx
          simp at hx
        | @insert w U hw ih =>
          obtain ⟨c, hs, hc⟩ := ih
          let P := U.filter (Q.Adj w)
          have hp : P.card ≤ 7 := by
            have hsub : P ⊆ Finset.univ.filter (Q.Adj w) := by
              intro a ha
              exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp ha).2⟩
            have hle := Finset.card_le_card hsub
            have hlt : ¬ 8 ≤ (Finset.univ.filter (Q.Adj w)).card := fun h => hlarge ⟨w, h⟩
            omega
          let J : Fin P.card ≃ ↥P := (Fintype.equivFinOfCardEq (by simp)).symm
          let L : SimpleGraph (Fin P.card) := {
            Adj := fun i j => Q.Adj (J i).val (J j).val
            symm := ⟨fun _ _ h => Q.symm.symm _ _ h⟩
            loopless := ⟨fun _ h => Q.irrefl h⟩ }
          have hL : L.CliqueFree 3 := by
            intro T hT
            obtain ⟨x, y, z, hxy, hxz, hyz, -⟩ := is3Clique_iff.mp hT
            have hn (i : Fin P.card) : Q.Adj w (J i).val :=
              (Finset.mem_filter.mp (J i).property).2
            exact noFour w (J x).val (J y).val (J z).val (hn x) (hn y) (hn z) hxy hxz hyz
          obtain ⟨d, hd⟩ := h4 P.card L hp hL
            (fun i j => c (J i).val (J j).val) (fun i j => hs (J i).val (J j).val)
          let paint (a : Fin 28) : Bool := if ha : a ∈ P then d (J.symm ⟨a, ha⟩) else false
          have valid (a b : Fin 28) (ha : a ∈ P) (hb : b ∈ P) (hab : Q.Adj a b) :
              ¬ (paint a = c a b ∧ paint b = c a b) := by
            have he : L.Adj (J.symm ⟨a, ha⟩) (J.symm ⟨b, hb⟩) := by
              change Q.Adj (J (J.symm ⟨a, ha⟩)).val (J (J.symm ⟨b, hb⟩)).val
              simpa only [Equiv.apply_symm_apply] using hab
            simpa [paint, ha, hb] using hd _ _ he
          let c' (a b : Fin 28) : Bool :=
            if a = w then paint b else if b = w then paint a else c a b
          refine ⟨c', ?_, ?_⟩
          · intro a b
            by_cases ha : a = w
            · by_cases hb : b = w
              · subst a
                subst b
                rfl
              · simp [c', ha, hb]
            · by_cases hb : b = w
              · simp [c', ha, hb]
              · simpa [c', ha, hb] using hs a b
          · intro x y z hx hy hz hxy hxz hyz hm
            have old (a : Fin 28) (ha : a ∈ insert w U) (hna : a ≠ w) : a ∈ U :=
              (Finset.mem_insert.mp ha).resolve_left hna
            have near (a : Fin 28) (ha : a ∈ insert w U) (hna : a ≠ w)
                (hwa : Q.Adj w a) : a ∈ P := Finset.mem_filter.mpr ⟨old a ha hna, hwa⟩
            by_cases ex : x = w
            · subst x
              have ey : y ≠ w := hxy.ne.symm
              have ez : z ≠ w := hxz.ne.symm
              have hh : paint y = paint z ∧ paint y = c y z := by
                simpa [c', ey, ez] using hm
              exact valid y z (near y hy ey hxy) (near z hz ez hxz) hyz
                ⟨hh.2, hh.1.symm.trans hh.2⟩
            · by_cases ey : y = w
              · subst y
                have ez : z ≠ w := hyz.ne.symm
                have hh : paint x = c x z ∧ paint x = paint z := by
                  simpa [c', ex, ez] using hm
                exact valid x z (near x hx ex (Q.symm.symm _ _ hxy)) (near z hz ez hyz) hxz
                  ⟨hh.1, hh.2.symm.trans hh.1⟩
              · by_cases ez : z = w
                · subst z
                  have hh : c x y = paint x ∧ c x y = paint y := by
                    simpa [c', ex, ey] using hm
                  exact valid x y (near x hx ex (Q.symm.symm _ _ hxz))
                    (near y hy ey (Q.symm.symm _ _ hyz)) hxy ⟨hh.1.symm, hh.2.symm⟩
                · exact hc x y z (old x hx ex) (old y hy ey) (old z hz ez) hxy hxz hyz
                    (by simpa [c', ex, ey, ez] using hm)
      obtain ⟨c, hs, hc⟩ := build Finset.univ
      obtain ⟨B, hB, havoid⟩ := free_of_coloring Q c hs (fun x y z =>
        hc x y z (Finset.mem_univ _) (Finset.mem_univ _) (Finset.mem_univ _))
      have hH : 8 ≤ Erdos151.H 28 := h2
      exact ⟨B, hH.trans hB, havoid⟩
  obtain ⟨B, hB, havoid⟩ := hfree
  refine ⟨B.map e, ?_, by simpa only [Finset.card_map] using hB, ?_⟩
  · intro a ha
    obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp ha
    exact hSR (E i).property
  · intro K hK hKB
    let T := Finset.univ.filter (fun i : Fin 28 => e i ∈ K)
    have hmap : T.map e = K := by
      ext a
      constructor
      · intro ha
        obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp ha
        exact (Finset.mem_filter.mp hi).2
      · intro ha
        obtain ⟨i, _, hi⟩ := Finset.mem_map.mp (hKB ha)
        exact Finset.mem_map.mpr ⟨i, Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, by simpa only [hi] using ha⟩, hi⟩
    have hTB : T ⊆ B := by
      intro i hi
      have hiK : e i ∈ K := (Finset.mem_filter.mp hi).2
      obtain ⟨j, hj, he⟩ := Finset.mem_map.mp (hKB hiK)
      exact (e.injective he) ▸ hj
    apply havoid T ?_ hTB
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro i hi j hj hij
      exact hK.1.1 (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2
        (fun he => hij (e.injective he))
    · intro U hU hTU i hi
      have hKU : K ⊆ U.map e := by
        rw [← hmap]
        intro a ha
        obtain ⟨j, hj, he⟩ := Finset.mem_map.mp ha
        exact Finset.mem_map.mpr ⟨j, hTU hj, he⟩
      have hiK : e i ∈ K := hK.1.2 (mapClique U hU) hKU
        (Finset.mem_map.mpr ⟨i, hi, rfl⟩)
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hiK⟩
    · have hcard := congrArg Finset.card hmap
      rw [Finset.card_map] at hcard
      rw [hcard]
      exact hK.2

private lemma maximal_clique_link_obstruction {n : ℕ} (G : SimpleGraph (Fin n))
    (K : Finset (Fin n)) (hK : G.IsBigMaximalClique K) (w : Fin n) (hw : w ∈ K)
    (hlink : ∀ x ∈ K, G.Adj w x → ∃ z, G.Adj w z ∧ G.Adj x z) :
    ∃ x ∈ K, ∃ y ∈ K, G.Adj w x ∧ G.Adj w y ∧ G.Adj x y := by
  classical
  have hcard : 1 ≤ (K.erase w).card := by
    rw [Finset.card_erase_of_mem hw]
    have := hK.2
    omega
  by_cases h2 : 2 ≤ (K.erase w).card
  · obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp (by omega : 1 < (K.erase w).card)
    have hxK : x ∈ K := Finset.mem_of_mem_erase hx
    have hyK : y ∈ K := Finset.mem_of_mem_erase hy
    have hwx : w ≠ x := (Finset.ne_of_mem_erase hx).symm
    have hwy : w ≠ y := (Finset.ne_of_mem_erase hy).symm
    exact ⟨x, hxK, y, hyK, hK.1.1 hw hxK hwx, hK.1.1 hw hyK hwy, hK.1.1 hxK hyK hxy⟩
  · have h1 : (K.erase w).card = 1 := by omega
    obtain ⟨x, hx⟩ := Finset.card_eq_one.mp h1
    have hxE : x ∈ K.erase w := by simp [hx]
    have hxK : x ∈ K := Finset.mem_of_mem_erase hxE
    have hwx : w ≠ x := (Finset.ne_of_mem_erase hxE).symm
    have hadj : G.Adj w x := hK.1.1 hw hxK hwx
    obtain ⟨z, hwz, hxz⟩ := hlink x hxK hadj
    have hKeq : K = {w, x} := by
      ext u
      constructor
      · intro hu
        by_cases huw : u = w
        · simp [huw]
        · have : u ∈ K.erase w := Finset.mem_erase.mpr ⟨huw, hu⟩
          rw [hx, Finset.mem_singleton] at this
          simp [this]
      · intro hu
        simp only [Finset.mem_insert, Finset.mem_singleton] at hu
        rcases hu with rfl | rfl
        · exact hw
        · exact hxK
    have hSub : G.IsClique (↑(insert z K) : Set (Fin n)) := by
      rw [coe_insert]
      apply hK.1.1.insert
      intro u hu _
      have : u = w ∨ u = x := by simpa [hKeq] using hu
      exact this.elim (fun h => h ▸ hwz.symm) (fun h => h ▸ hxz.symm)
    have hzK : z ∈ K := hK.1.2 hSub (subset_insert _ _) (mem_insert_self _ _)
    have : z = w ∨ z = x := by simpa [hKeq] using hzK
    exact (this.elim hwz.ne.symm hxz.ne.symm).elim

private lemma free_set_deletion {n : ℕ} (G : SimpleGraph (Fin n))
    (A D B : Finset (Fin n)) (I : Fin n → Finset (Fin n))
    (hcover : ∀ w ∈ A, (Finset.univ.filter (G.Adj w)) \ I w ⊆ D)
    (hlink : ∀ w ∈ A, ∀ x ∈ I w, G.Adj w x ∧ ∃ z, G.Adj w z ∧ G.Adj x z)
    (hind : ∀ w ∈ A, ∀ x ∈ I w, ∀ y ∈ I w, ¬ G.Adj x y)
    (hanchors : ∀ w ∈ A, ∀ x ∈ A, G.Adj w x → x ∈ I w)
    (hBD : B ⊆ Finset.univ \ D)
    (hB : ∀ K : Finset (Fin n), G.IsBigMaximalClique K → ¬ (K ⊆ B)) :
    ∀ K : Finset (Fin n), G.IsBigMaximalClique K → ¬ (K ⊆ A ∪ B) := by
  classical
  intro K hK hKU
  by_cases hm : ∃ w ∈ K, w ∈ A
  · obtain ⟨w, hwK, hwA⟩ := hm
    have hKI : ∀ x ∈ K, G.Adj w x → x ∈ I w := by
      intro x hxK hwx
      rcases Finset.mem_union.mp (hKU hxK) with hxA | hxB
      · exact hanchors w hwA x hxA hwx
      · by_contra hxI
        have hxD : x ∈ D := hcover w hwA (Finset.mem_sdiff.mpr
          ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hwx⟩, hxI⟩)
        exact (Finset.mem_sdiff.mp (hBD hxB)).2 hxD
    obtain ⟨x, hxK, y, hyK, hwx, hwy, hxy⟩ :=
      maximal_clique_link_obstruction G K hK w hwK
        (fun x hxK hwx => (hlink w hwA x (hKI x hxK hwx)).2)
    exact hind w hwA x (hKI x hxK hwx) y (hKI y hyK hwy) hxy
  · apply hB K hK
    intro x hxK
    rcases Finset.mem_union.mp (hKU hxK) with hxA | hxB
    · exact (hm ⟨x, hxK, hxA⟩).elim
    · exact hxB

private lemma extend_from_28 (h2 : H2) (h4 : H4) {n k : ℕ}
    (G : SimpleGraph (Fin n)) (hG : G.CliqueFree 4)
    (A D : Finset (Fin n)) (I : Fin n → Finset (Fin n))
    (hk : k ≤ A.card + 8) (hbudget : D.card + 28 ≤ n) (hAD : A ⊆ D)
    (hcover : ∀ w ∈ A, (Finset.univ.filter (G.Adj w)) \ I w ⊆ D)
    (hlink : ∀ w ∈ A, ∀ x ∈ I w, G.Adj w x ∧ ∃ z, G.Adj w z ∧ G.Adj x z)
    (hind : ∀ w ∈ A, ∀ x ∈ I w, ∀ y ∈ I w, ¬ G.Adj x y)
    (hanchors : ∀ w ∈ A, ∀ x ∈ A, G.Adj w x → x ∈ I w) :
    G.cliqueTransversalNumber ≤ n - k := by
  classical
  have hR : 28 ≤ (Finset.univ \ D).card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ D)]
    simp only [Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨B, hBD, hBcard, hB⟩ := beta_of_coloring_28 h2 h4 G hG _ hR
  have hdisj : Disjoint A B := Finset.disjoint_left.mpr
    (fun _ hxA hxB => (Finset.mem_sdiff.mp (hBD hxB)).2 (hAD hxA))
  refine transversal_le_of_free G (A ∪ B) ?_ ?_
  · rw [Finset.card_union_of_disjoint hdisj]
    omega
  · exact free_set_deletion G A D B I hcover hlink hind hanchors hBD hB


private lemma r34_and_triple_in_8 {n : ℕ} (G : SimpleGraph (Fin n))
    (hG : G.CliqueFree 4) (w : Fin n) (P : Finset (Fin n))
    (hP : P ⊆ Finset.univ.filter (G.Adj w)) (h8 : 8 ≤ P.card)
    (halpha : ∀ I : Finset (Fin n), I ⊆ P →
      (∀ x ∈ I, ∀ y ∈ I, ¬ G.Adj x y) → I.card ≤ 3) :
    P.card = 8 ∧ ∀ v ∈ P, ∃ I : Finset (Fin n), I ⊆ P ∧
      (∀ x ∈ I, ∀ y ∈ I, ¬ G.Adj x y) ∧ I.card = 3 ∧ v ∈ I := by
  classical
  have noTri (x : Fin n) (hx : x ∈ P) (y : Fin n) (hy : y ∈ P)
      (z : Fin n) (hz : z ∈ P) (hxy : G.Adj x y) (hxz : G.Adj x z)
      (hyz : G.Adj y z) : False := by
    have hwx := (Finset.mem_filter.mp (hP hx)).2
    have hwy := (Finset.mem_filter.mp (hP hy)).2
    have hwz := (Finset.mem_filter.mp (hP hz)).2
    have hwN : w ∉ ({x, y, z} : Finset (Fin n)) := by
      simp [hwx.ne, hwy.ne, hwz.ne]
    have hxN : x ∉ ({y, z} : Finset (Fin n)) := by simp [hxy.ne, hxz.ne]
    have hyN : y ∉ ({z} : Finset (Fin n)) := by simp [hyz.ne]
    apply hG ({w, x, y, z} : Finset (Fin n))
    constructor
    · intro a ha b hb hab
      simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at ha hb
      rcases ha with rfl | rfl | rfl | rfl <;>
        rcases hb with rfl | rfl | rfl | rfl <;>
        first | exact (hab rfl).elim | assumption | exact G.symm.symm _ _ (by assumption)
    · rw [Finset.card_insert_of_notMem hwN, Finset.card_insert_of_notMem hxN,
        Finset.card_insert_of_notMem hyN]
      simp
  let N (S : Finset (Fin n)) (a : Fin n) := S.filter (G.Adj a)
  let M (S : Finset (Fin n)) (a : Fin n) := S.erase a \ N S a
  have memN (S : Finset (Fin n)) (a x : Fin n) :
      x ∈ N S a ↔ x ∈ S ∧ G.Adj a x := Finset.mem_filter
  have memM (S : Finset (Fin n)) (a x : Fin n) :
      x ∈ M S a ↔ x ∈ S ∧ x ≠ a ∧ ¬ G.Adj a x := by
    constructor
    · intro h
      obtain ⟨he, hn⟩ := Finset.mem_sdiff.mp h
      obtain ⟨hne, hs⟩ := Finset.mem_erase.mp he
      exact ⟨hs, hne, fun hadj => hn ((memN S a x).mpr ⟨hs, hadj⟩)⟩
    · rintro ⟨hs, hne, hn⟩
      exact Finset.mem_sdiff.mpr
        ⟨Finset.mem_erase.mpr ⟨hne, hs⟩, fun h => hn ((memN S a x).mp h).2⟩
  have cardM (S : Finset (Fin n)) (a : Fin n) (ha : a ∈ S) :
      (M S a).card = S.card - 1 - (N S a).card := by
    have hsub : N S a ⊆ S.erase a := by
      intro x hx
      obtain ⟨hxS, hax⟩ := (memN S a x).mp hx
      exact Finset.mem_erase.mpr ⟨hax.ne.symm, hxS⟩
    change (S.erase a \ N S a).card = _
    rw [Finset.card_sdiff_of_subset hsub, Finset.card_erase_of_mem ha]
  have indN (S : Finset (Fin n)) (hSP : S ⊆ P) (a : Fin n) (ha : a ∈ S) :
      ∀ x ∈ N S a, ∀ y ∈ N S a, ¬ G.Adj x y := by
    intro x hx y hy hxy
    obtain ⟨hxS, hax⟩ := (memN S a x).mp hx
    obtain ⟨hyS, hay⟩ := (memN S a y).mp hy
    exact noTri a (hSP ha) x (hSP hxS) y (hSP hyS) hax hay hxy
  have noEdge (S : Finset (Fin n)) (hSP : S ⊆ P) (h3 : 3 ≤ S.card) :
      ∃ x ∈ S, ∃ y ∈ S, x ≠ y ∧ ¬ G.Adj x y := by
    by_contra hn
    have adj (x : Fin n) (hx : x ∈ S) (y : Fin n) (hy : y ∈ S)
        (hxy : x ≠ y) : G.Adj x y := by
      by_contra h
      exact hn ⟨x, hx, y, hy, hxy, h⟩
    obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp (by omega : 1 < S.card)
    have hp : ({x, y} : Finset (Fin n)) ⊆ S := by
      intro u hu
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with rfl | rfl
      · exact hx
      · exact hy
    have hr : 0 < (S \ ({x, y} : Finset (Fin n))).card := by
      rw [Finset.card_sdiff_of_subset hp, Finset.card_pair hxy]
      omega
    obtain ⟨z, hz⟩ := Finset.card_pos.mp hr
    obtain ⟨hzS, hzN⟩ := Finset.mem_sdiff.mp hz
    have hzx : z ≠ x := fun h => hzN (by simp [h])
    have hzy : z ≠ y := fun h => hzN (by simp [h])
    exact noTri x (hSP hx) y (hSP hy) z (hSP hzS)
      (adj x hx y hy hxy) (adj x hx z hzS hzx.symm) (adj y hy z hzS hzy.symm)
  have triple (S : Finset (Fin n)) (hSP : S ⊆ P) (a : Fin n) (ha : a ∈ S)
      (hm : 3 ≤ (M S a).card) :
      ∃ I : Finset (Fin n), I ⊆ S ∧
        (∀ x ∈ I, ∀ y ∈ I, ¬ G.Adj x y) ∧ I.card = 3 ∧ a ∈ I := by
    have hMS : M S a ⊆ S := fun x hx => ((memM S a x).mp hx).1
    obtain ⟨x, hx, y, hy, hxy, hnot⟩ := noEdge (M S a) (fun u hu => hSP (hMS hu)) hm
    obtain ⟨hxS, hxa, hax⟩ := (memM S a x).mp hx
    obtain ⟨hyS, hya, hay⟩ := (memM S a y).mp hy
    have hxa' : ¬ G.Adj x a := fun h => hax h.symm
    have hya' : ¬ G.Adj y a := fun h => hay h.symm
    have hyx : ¬ G.Adj y x := fun h => hnot h.symm
    refine ⟨{a, x, y}, ?_, ?_, ?_, by simp⟩
    · intro u hu
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with rfl | rfl | rfl
      · exact ha
      · exact hxS
      · exact hyS
    · intro u hu v hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu hv
      rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl <;>
        first | assumption | exact (fun h => G.irrefl h)
    · have hn : a ∉ ({x, y} : Finset (Fin n)) := by simp [hxa.symm, hya.symm]
      rw [Finset.card_insert_of_notMem hn, Finset.card_pair hxy]
  have six (S : Finset (Fin n)) (hSP : S ⊆ P) (h6 : 6 ≤ S.card) :
      ∃ I : Finset (Fin n), I ⊆ S ∧
        (∀ x ∈ I, ∀ y ∈ I, ¬ G.Adj x y) ∧ I.card = 3 := by
    obtain ⟨a, ha⟩ := Finset.card_pos.mp (by omega : 0 < S.card)
    by_cases hn : 3 ≤ (N S a).card
    · obtain ⟨I, hIN, hIc⟩ := Finset.exists_subset_card_eq hn
      refine ⟨I, fun x hx => ((memN S a x).mp (hIN hx)).1, ?_, hIc⟩
      intro x hx y hy
      exact indN S hSP a ha x (hIN hx) y (hIN hy)
    · have hc := cardM S a ha
      obtain ⟨I, hi, hind, hic, _⟩ := triple S hSP a ha (by omega)
      exact ⟨I, hi, hind, hic⟩
  have sumConst (S : Finset (Fin n)) (j : ℕ) :
      Finset.sum S (fun _ => j) = S.card * j := by
    induction S using Finset.induction_on with
    | empty => simp
    | @insert a T ha ih =>
      rw [Finset.sum_insert ha, Finset.card_insert_of_notMem ha, ih,
        Nat.add_mul, Nat.one_mul, Nat.add_comm j]
  have parity (S : Finset (Fin n)) :
      ∃ k : ℕ, Finset.sum S (fun x => (N S x).card) = 2 * k := by
    induction S using Finset.induction_on with
    | empty => exact ⟨0, by simp⟩
    | @insert a T ha ih =>
      obtain ⟨k, hk⟩ := ih
      have step (x : Fin n) : (N (insert a T) x).card =
          (N T x).card + (if G.Adj a x then 1 else 0) := by
        have hn : a ∉ T.filter (G.Adj x) := fun h => ha (Finset.mem_filter.mp h).1
        change ((insert a T).filter (G.Adj x)).card = (T.filter (G.Adj x)).card + _
        by_cases hax : G.Adj a x
        · have hxa := hax.symm
          have he : (insert a T).filter (G.Adj x) = insert a (T.filter (G.Adj x)) := by
            simp [Finset.filter_insert, hxa]
          rw [he, Finset.card_insert_of_notMem hn, if_pos hax]
        · have hxa : ¬ G.Adj x a := fun h => hax h.symm
          simp [Finset.filter_insert, hxa, hax]
      have hself : (N (insert a T) a).card = (N T a).card := by
        have hna : ¬ G.Adj a a := fun h => G.irrefl h
        simpa [hna] using step a
      have hcount : Finset.sum T (fun x => if G.Adj a x then (1 : ℕ) else 0) =
          (N T a).card := by
        calc
          _ = Finset.sum (N T a) (fun _ => (1 : ℕ)) := by
            change _ = Finset.sum (T.filter (G.Adj a)) (fun _ => (1 : ℕ))
            rw [Finset.sum_filter]
          _ = _ := by rw [sumConst, Nat.mul_one]
      have hsum : Finset.sum T (fun x => (N (insert a T) x).card) =
          Finset.sum T (fun x => (N T x).card) + (N T a).card := by
        calc
          _ = Finset.sum T (fun x => (N T x).card + (if G.Adj a x then 1 else 0)) :=
            Finset.sum_congr rfl (fun x _ => step x)
          _ = _ := by rw [Finset.sum_add_distrib, hcount]
      refine ⟨k + (N T a).card, ?_⟩
      rw [Finset.sum_insert ha, hself, hsum, hk]
      omega
  have hcard : P.card = 8 := by
    by_contra hne
    obtain ⟨Q, hQP, hQ⟩ := Finset.exists_subset_card_eq (by omega : 9 ≤ P.card)
    have hdeg (a : Fin n) (ha : a ∈ Q) : (N Q a).card = 3 := by
      have hu : (N Q a).card ≤ 3 :=
        halpha (N Q a) (fun x hx => hQP ((memN Q a x).mp hx).1) (indN Q hQP a ha)
      by_contra hne'
      have hM := cardM Q a ha
      have hm : 6 ≤ (M Q a).card := by omega
      have hMP : M Q a ⊆ P := fun x hx => hQP ((memM Q a x).mp hx).1
      obtain ⟨I, hIM, hind, hIc⟩ := six (M Q a) hMP hm
      have hna : a ∉ I := fun h => ((memM Q a a).mp (hIM h)).2.1 rfl
      have hsub : insert a I ⊆ P := by
        intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx
        · exact hQP ha
        · exact hMP (hIM hx)
      have hIind : ∀ x ∈ insert a I, ∀ y ∈ insert a I, ¬ G.Adj x y := by
        intro x hx y hy hxy
        rcases Finset.mem_insert.mp hx with hx' | hx
        · rcases Finset.mem_insert.mp hy with hy' | hy
          · rw [hx', hy'] at hxy
            exact G.irrefl hxy
          · rw [hx'] at hxy
            exact ((memM Q a y).mp (hIM hy)).2.2 hxy
        · rcases Finset.mem_insert.mp hy with hy' | hy
          · rw [hy'] at hxy
            exact ((memM Q a x).mp (hIM hx)).2.2 hxy.symm
          · exact hind x hx y hy hxy
      have hb := halpha (insert a I) hsub hIind
      rw [Finset.card_insert_of_notMem hna, hIc] at hb
      omega
    have hsum : Finset.sum Q (fun x => (N Q x).card) = 27 := by
      calc
        _ = Finset.sum Q (fun _ => (3 : ℕ)) := Finset.sum_congr rfl hdeg
        _ = _ := by rw [sumConst, hQ]
    obtain ⟨k, hk⟩ := parity Q
    omega
  refine ⟨hcard, ?_⟩
  intro v hv
  have hu : (N P v).card ≤ 3 :=
    halpha (N P v) (fun x hx => ((memN P v x).mp hx).1)
      (indN P (fun _ hx => hx) v hv)
  have hm := cardM P v hv
  exact triple P (fun _ hx => hx) v hv (by omega)

private theorem minimal_uncolorable_subgraph {n : ℕ} (G : SimpleGraph (Fin n))
    (hc : ¬ ∃ c : Fin n → Fin n → Bool, (∀ x y, c x y = c y x) ∧
      (∀ x y z, G.Adj x y → G.Adj x z → G.Adj y z →
        ¬ (c x y = c x z ∧ c x y = c y z))) :
    ∃ Q : SimpleGraph (Fin n),
      (∀ x y, Q.Adj x y → G.Adj x y) ∧
      (¬ ∃ c : Fin n → Fin n → Bool, (∀ x y, c x y = c y x) ∧
        (∀ x y z, Q.Adj x y → Q.Adj x z → Q.Adj y z →
          ¬ (c x y = c x z ∧ c x y = c y z))) ∧
      (∀ R : SimpleGraph (Fin n), (∀ x y, R.Adj x y → Q.Adj x y) →
        (∃ x y, Q.Adj x y ∧ ¬ R.Adj x y) →
        ∃ c : Fin n → Fin n → Bool, (∀ x y, c x y = c y x) ∧
          (∀ x y z, R.Adj x y → R.Adj x z → R.Adj y z →
            ¬ (c x y = c x z ∧ c x y = c y z))) := by
  classical
  let Colorable (Q : SimpleGraph (Fin n)) : Prop :=
    ∃ c : Fin n → Fin n → Bool, (∀ x y, c x y = c y x) ∧
      (∀ x y z, Q.Adj x y → Q.Adj x z → Q.Adj y z →
        ¬ (c x y = c x z ∧ c x y = c y z))
  let E (Q : SimpleGraph (Fin n)) : Finset (Fin n × Fin n) :=
    Finset.univ.filter (fun p : Fin n × Fin n => Q.Adj p.1 p.2)
  let P (k : ℕ) : Prop := ∃ Q : SimpleGraph (Fin n),
    (∀ x y, Q.Adj x y → G.Adj x y) ∧ ¬ Colorable Q ∧ (E Q).card = k
  have hex : ∃ k, P k := ⟨(E G).card, G, fun _ _ h => h, hc, rfl⟩
  obtain ⟨Q, hQG, hQbad, hcard⟩ : P (Nat.find hex) := Nat.find_spec hex
  refine ⟨Q, hQG, hQbad, ?_⟩
  intro R hRQ hw
  change Colorable R
  by_contra hRbad
  have hsub : E R ⊆ E Q := by
    intro p hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hRQ _ _ (Finset.mem_filter.mp hp).2⟩
  have hnsub : ¬ E Q ⊆ E R := by
    intro h
    obtain ⟨x, y, hxy, hnxy⟩ := hw
    have hp : (x, y) ∈ E Q := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxy⟩
    exact hnxy (Finset.mem_filter.mp (h hp)).2
  have hlt : (E R).card < (E Q).card := by
    apply Finset.card_lt_card
    first
    | exact ⟨hsub, hnsub⟩
    | exact lt_of_le_not_ge hsub hnsub
    | exact Finset.ssubset_iff_subset_ne.mpr ⟨hsub, fun he => hnsub (he ▸ hsub)⟩
  have hp : P (E R).card := ⟨R, fun x y h => hQG x y (hRQ x y h), hRbad, rfl⟩
  have hle : Nat.find hex ≤ (E R).card := Nat.find_min' hex hp
  omega

private theorem restore_vertex_coloring (h4 : H4) {n : ℕ}
    (Q R : SimpleGraph (Fin n)) (hQ : Q.CliqueFree 4) (w : Fin n)
    (hw : (Finset.univ.filter (Q.Adj w)).card ≤ 7)
    (hR : ∀ x y, R.Adj x y ↔ Q.Adj x y ∧ x ≠ w ∧ y ≠ w)
    (hc : ∃ c : Fin n → Fin n → Bool, (∀ x y, c x y = c y x) ∧
      (∀ x y z, R.Adj x y → R.Adj x z → R.Adj y z →
        ¬ (c x y = c x z ∧ c x y = c y z))) :
    ∃ c : Fin n → Fin n → Bool, (∀ x y, c x y = c y x) ∧
      (∀ x y z, Q.Adj x y → Q.Adj x z → Q.Adj y z →
        ¬ (c x y = c x z ∧ c x y = c y z)) := by
  classical
  obtain ⟨c, hs, ht⟩ := hc
  let P : Finset (Fin n) := Finset.univ.filter (Q.Adj w)
  have hp : P.card ≤ 7 := by
    simpa [P] using hw
  let J : Fin P.card ≃ ↥P := (Fintype.equivFinOfCardEq (by simp)).symm
  let L : SimpleGraph (Fin P.card) := {
    Adj := fun i j => Q.Adj (J i).val (J j).val
    symm := ⟨fun _ _ h => Q.symm.symm _ _ h⟩
    loopless := ⟨fun _ h => Q.irrefl h⟩ }
  have noFour (a b q : Fin P.card)
      (hab : Q.Adj (J a).val (J b).val)
      (haq : Q.Adj (J a).val (J q).val)
      (hbq : Q.Adj (J b).val (J q).val)
      (hwa : Q.Adj w (J a).val)
      (hwb : Q.Adj w (J b).val)
      (hwq : Q.Adj w (J q).val) : False := by
    have hwN : w ∉ ({(J a).val, (J b).val, (J q).val} : Finset (Fin n)) := by
      simp [hwa.ne, hwb.ne, hwq.ne]
    have haN : (J a).val ∉ ({(J b).val, (J q).val} : Finset (Fin n)) := by
      simp [hab.ne, haq.ne]
    have hbN : (J b).val ∉ ({(J q).val} : Finset (Fin n)) := by
      simp [hbq.ne]
    apply hQ ({w, (J a).val, (J b).val, (J q).val} : Finset (Fin n))
    constructor
    · intro x hx y hy hxy
      simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hx hy
      rcases hx with rfl | rfl | rfl | rfl <;>
        rcases hy with rfl | rfl | rfl | rfl <;>
        first | exact (hxy rfl).elim | assumption | exact Q.symm.symm _ _ (by assumption)
    · rw [Finset.card_insert_of_notMem hwN, Finset.card_insert_of_notMem haN,
        Finset.card_insert_of_notMem hbN]
      simp
  have hL : L.CliqueFree 3 := by
    intro T hT
    obtain ⟨a, b, q, hab, haq, hbq, -⟩ := is3Clique_iff.mp hT
    have hn (i : Fin P.card) : Q.Adj w (J i).val :=
      (Finset.mem_filter.mp (J i).property).2
    exact noFour a b q hab haq hbq (hn a) (hn b) (hn q)
  obtain ⟨d, hd⟩ := h4 P.card L hp hL
    (fun i j => c (J i).val (J j).val) (fun i j => hs (J i).val (J j).val)
  let paint (a : Fin n) : Bool :=
    if ha : a ∈ P then d (J.symm ⟨a, ha⟩) else false
  have valid (a b : Fin n) (ha : a ∈ P) (hb : b ∈ P) (hab : Q.Adj a b) :
      ¬ (paint a = c a b ∧ paint b = c a b) := by
    have he : L.Adj (J.symm ⟨a, ha⟩) (J.symm ⟨b, hb⟩) := by
      change Q.Adj (J (J.symm ⟨a, ha⟩)).val (J (J.symm ⟨b, hb⟩)).val
      simpa only [Equiv.apply_symm_apply] using hab
    simpa [paint, ha, hb] using hd _ _ he
  let c' (a b : Fin n) : Bool :=
    if a = w then paint b else if b = w then paint a else c a b
  have hs' (a b : Fin n) : c' a b = c' b a := by
    by_cases ha : a = w
    · by_cases hb : b = w
      · subst a
        subst b
        rfl
      · simp [c', ha, hb]
    · by_cases hb : b = w
      · simp [c', ha, hb]
      · simpa [c', ha, hb] using hs a b
  refine ⟨c', hs', ?_⟩
  intro x y z hxy hxz hyz hm
  by_cases ex : x = w
  · subst x
    have ey : y ≠ w := hxy.ne.symm
    have ez : z ≠ w := hxz.ne.symm
    have hh : paint y = paint z ∧ paint y = c y z := by
      simpa [c', ey, ez] using hm
    exact valid y z (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxy⟩)
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxz⟩) hyz
      ⟨hh.2, hh.1.symm.trans hh.2⟩
  · by_cases ey : y = w
    · subst y
      have ez : z ≠ w := hyz.ne.symm
      have hh : paint x = c x z ∧ paint x = paint z := by
        simpa [c', ex, ez] using hm
      exact valid x z
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, Q.symm.symm _ _ hxy⟩)
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hyz⟩) hxz
        ⟨hh.1, hh.2.symm.trans hh.1⟩
    · by_cases ez : z = w
      · subst z
        have hh : c x y = paint x ∧ c x y = paint y := by
          simpa [c', ex, ey] using hm
        exact valid x y
          (Finset.mem_filter.mpr ⟨Finset.mem_univ _, Q.symm.symm _ _ hxz⟩)
          (Finset.mem_filter.mpr ⟨Finset.mem_univ _, Q.symm.symm _ _ hyz⟩) hxy
          ⟨hh.1.symm, hh.2.symm⟩
      · exact ht x y z
          ((hR x y).mpr ⟨hxy, ex, ey⟩)
          ((hR x z).mpr ⟨hxz, ex, ez⟩)
          ((hR y z).mpr ⟨hyz, ey, ez⟩)
          (by simpa [c', ex, ey, ez] using hm)

private theorem restore_edge_coloring {n : ℕ}
    (Q R : SimpleGraph (Fin n)) (u v : Fin n)
    (hR : ∀ x y, R.Adj x y ↔ Q.Adj x y ∧
      ¬ ((x = u ∧ y = v) ∨ (x = v ∧ y = u)))
    (hsmall : ¬ ∃ z t : Fin n, z ≠ t ∧ Q.Adj u z ∧ Q.Adj v z ∧ Q.Adj u t ∧ Q.Adj v t)
    (hc : ∃ c : Fin n → Fin n → Bool, (∀ x y, c x y = c y x) ∧
      (∀ x y z, R.Adj x y → R.Adj x z → R.Adj y z →
        ¬ (c x y = c x z ∧ c x y = c y z))) :
    ∃ c : Fin n → Fin n → Bool, (∀ x y, c x y = c y x) ∧
      (∀ x y z, Q.Adj x y → Q.Adj x z → Q.Adj y z →
        ¬ (c x y = c x z ∧ c x y = c y z)) := by
  classical
  obtain ⟨c, hs, ht⟩ := hc
  obtain ⟨b, hb⟩ : ∃ b : Bool, ∀ z, Q.Adj u z → Q.Adj v z → b ≠ c u z := by
    by_cases he : ∃ z, Q.Adj u z ∧ Q.Adj v z
    · obtain ⟨z, huz, hvz⟩ := he
      refine ⟨if c u z = true then false else true, ?_⟩
      intro t hut hvt
      have htz : t = z := by
        by_contra hne
        exact hsmall ⟨t, z, hne, hut, hvt, huz, hvz⟩
      subst t
      cases hcol : c u z <;> simp [hcol]
    · exact ⟨false, fun z huz hvz => (he ⟨z, huz, hvz⟩).elim⟩
  let E (x y : Fin n) : Prop := (x = u ∧ y = v) ∨ (x = v ∧ y = u)
  have rev (x y : Fin n) (h : E x y) : E y x := by
    rcases h with ⟨hx, hy⟩ | ⟨hx, hy⟩
    · exact Or.inr ⟨hy, hx⟩
    · exact Or.inl ⟨hy, hx⟩
  let d (x y : Fin n) : Bool := if E x y then b else c x y
  have ds (x y : Fin n) : d x y = d y x := by
    by_cases he : E x y
    · simp [d, he, rev x y he]
    · have hn : ¬ E y x := fun h => he (rev y x h)
      simpa [d, he, hn] using hs x y
  have avoid (x y z : Fin n) (he : E x y) (hxz : Q.Adj x z) (hyz : Q.Adj y z) :
      ¬ (d x y = d x z ∧ d x y = d y z) := by
    intro hm
    have hxy : d x y = b := if_pos he
    rcases he with ⟨hx, hy⟩ | ⟨hx, hy⟩
    · subst x
      subst y
      have hn : ¬ E u z := by
        rintro (⟨_, h⟩ | ⟨_, h⟩)
        · exact hyz.ne h.symm
        · exact hxz.ne h.symm
      have hside : d u z = c u z := if_neg hn
      exact hb z hxz hyz (hxy.symm.trans (hm.1.trans hside))
    · subst x
      subst y
      have hn : ¬ E u z := by
        rintro (⟨_, h⟩ | ⟨_, h⟩)
        · exact hxz.ne h.symm
        · exact hyz.ne h.symm
      have hside : d u z = c u z := if_neg hn
      exact hb z hyz hxz (hxy.symm.trans (hm.2.trans hside))
  refine ⟨d, ds, ?_⟩
  intro x y z hxy hxz hyz hm
  by_cases exy : E x y
  · exact avoid x y z exy hxz hyz hm
  by_cases exz : E x z
  · exact avoid x z y exz hxy hyz.symm
      ⟨hm.1.symm, hm.1.symm.trans (hm.2.trans (ds y z))⟩
  by_cases eyz : E y z
  · exact avoid y z x eyz hxy.symm hxz.symm
      ⟨hm.2.symm.trans (ds x y), hm.2.symm.trans (hm.1.trans (ds x z))⟩
  exact ht x y z ((hR x y).mpr ⟨hxy, exy⟩) ((hR x z).mpr ⟨hxz, exz⟩)
    ((hR y z).mpr ⟨hyz, eyz⟩) (by simpa [d, exy, exz, eyz] using hm)


private lemma oma151_core {n : ℕ} (G : SimpleGraph (Fin n))
    (hG : G.CliqueFree 4) (h11 : 11 ≤ Erdos151.H n)
    (extend : ∀ (k : ℕ) (L : SimpleGraph (Fin k)), k ≤ 7 → L.CliqueFree 3 →
      ∀ c : Fin k → Fin k → Bool, (∀ x y, c x y = c y x) →
        ∃ d : Fin k → Bool, ∀ x y, L.Adj x y → ¬ (d x = c x y ∧ d y = c x y)) :
    G.cliqueTransversalNumber ≤ n - 11 ∨
      ∃ F : SimpleGraph (Fin n), F ≤ G ∧ (∃ b x, F.Adj b x) ∧
        (∀ b x, F.Adj b x → 8 ≤ (Finset.univ.filter (F.Adj b)).card) ∧
        (∀ b x, F.Adj b x →
          2 ≤ (Finset.univ.filter (fun z => F.Adj b z ∧ F.Adj x z)).card) := by
  classical
  by_cases hcolor : ∃ c : Fin n → Fin n → Bool, (∀ x y, c x y = c y x) ∧
      (∀ x y z, G.Adj x y → G.Adj x z → G.Adj y z →
        ¬ (c x y = c x z ∧ c x y = c y z))
  · obtain ⟨c, hs, hc⟩ := hcolor
    obtain ⟨B, hB, hfree⟩ := free_of_coloring G c hs hc
    exact Or.inl (transversal_le_of_free G B (h11.trans hB) hfree)
  · have hbad := minimal_uncolorable_subgraph G hcolor
    obtain ⟨Q, hQG, hQbad, hmin⟩ := hbad
    have hQ : Q.CliqueFree 4 := by
      intro K hK
      apply hG K
      refine ⟨?_, hK.2⟩
      intro x hx y hy hxy
      exact hQG x y (hK.1 hx hy hxy)
    have hedge : ∃ b x, Q.Adj b x := by
      by_contra hn
      apply hQbad
      refine ⟨fun _ _ => false, ?_, ?_⟩
      · intro _ _
        rfl
      · intro x y z hxy _ _
        exact (hn ⟨x, y, hxy⟩).elim
    have hdegree : ∀ b x, Q.Adj b x →
        8 ≤ (Finset.univ.filter (Q.Adj b)).card := by
      intro b x hbx
      by_contra hnot
      have hsmall : (Finset.univ.filter (Q.Adj b)).card ≤ 7 := by omega
      let R : SimpleGraph (Fin n) := {
        Adj := fun y z => Q.Adj y z ∧ y ≠ b ∧ z ≠ b
        symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
        loopless := ⟨fun _ h => Q.irrefl h.1⟩ }
      have hR : ∀ y z, R.Adj y z ↔ Q.Adj y z ∧ y ≠ b ∧ z ≠ b := by
        intro y z
        rfl
      have hcR := hmin R (fun _ _ h => h.1)
        ⟨b, x, hbx, fun hr => hr.2.1 rfl⟩
      obtain ⟨d, hds, hdt⟩ :=
        restore_vertex_coloring extend Q R hQ b hsmall hR hcR
      exact hQbad ⟨d, hds, hdt⟩
    have hcommon : ∀ b x, Q.Adj b x →
        2 ≤ (Finset.univ.filter (fun z => Q.Adj b z ∧ Q.Adj x z)).card := by
      intro b x hbx
      by_contra hnot
      let C := Finset.univ.filter (fun z => Q.Adj b z ∧ Q.Adj x z)
      have hC : C.card ≤ 1 := by
        dsimp [C]
        omega
      have hsmall : ¬ ∃ z t : Fin n, z ≠ t ∧ Q.Adj b z ∧ Q.Adj x z ∧
          Q.Adj b t ∧ Q.Adj x t := by
        rintro ⟨z, t, hzt, hbz, hxz, hbt, hxt⟩
        have hz : z ∈ C := by simp [C, hbz, hxz]
        have ht : t ∈ C := by simp [C, hbt, hxt]
        have hlt : 1 < C.card :=
          Finset.one_lt_card.mpr ⟨z, hz, t, ht, hzt⟩
        omega
      let R : SimpleGraph (Fin n) := {
        Adj := fun y z => Q.Adj y z ∧
          ¬ ((y = b ∧ z = x) ∨ (y = x ∧ z = b))
        symm := ⟨fun y z h => by
          refine ⟨h.1.symm, ?_⟩
          intro he
          rcases he with ⟨hz, hy⟩ | ⟨hz, hy⟩
          · exact h.2 (Or.inr ⟨hy, hz⟩)
          · exact h.2 (Or.inl ⟨hy, hz⟩)⟩
        loopless := ⟨fun _ h => Q.irrefl h.1⟩ }
      have hR : ∀ y z, R.Adj y z ↔ Q.Adj y z ∧
          ¬ ((y = b ∧ z = x) ∨ (y = x ∧ z = b)) := by
        intro y z
        rfl
      have hcR := hmin R (fun _ _ h => h.1)
        ⟨b, x, hbx, fun hr => hr.2 (Or.inl ⟨rfl, rfl⟩)⟩
      obtain ⟨d, hds, hdt⟩ := restore_edge_coloring Q R b x hR hsmall hcR
      exact hQbad ⟨d, hds, hdt⟩
    exact Or.inr ⟨Q, hQG, hedge, hdegree, hcommon⟩

private lemma oma151_link_facts {n : ℕ} (G : SimpleGraph (Fin n))
    (hG : G.CliqueFree 4) (v : Fin n) :
    let P := (Finset.univ.filter (G.Adj v)).filter
      (fun x => ∃ z, G.Adj v z ∧ G.Adj x z)
    (∀ x ∈ P, (P.filter (G.Adj x)).card ≤ 3 → 8 ≤ P.card →
      ∃ I ⊆ P, I.card = 3 ∧ x ∈ I ∧ ∀ u ∈ I, ∀ w ∈ I, ¬ G.Adj u w) ∧
    ((∀ I ⊆ P, (∀ u ∈ I, ∀ w ∈ I, ¬ G.Adj u w) → I.card ≤ 3) →
      8 ≤ P.card →
      P.card = 8 ∧
      (∀ x ∈ P, ∃ I ⊆ P, I.card = 3 ∧ x ∈ I ∧
        ∀ u ∈ I, ∀ w ∈ I, ¬ G.Adj u w) ∧
      ((∀ x ∈ P, 2 ≤ (P.filter (G.Adj x)).card) →
        ∃ x ∈ P, 3 ≤ (P.filter (G.Adj x)).card)) := by
  classical
  intro P
  let N (S : Finset (Fin n)) (a : Fin n) := S.filter (G.Adj a)
  let M (S : Finset (Fin n)) (a : Fin n) := S.erase a \ N S a
  have hP : P ⊆ Finset.univ.filter (G.Adj v) := fun _ h => (Finset.mem_filter.mp h).1
  have memM (S : Finset (Fin n)) (a x : Fin n) :
      x ∈ M S a ↔ x ∈ S ∧ x ≠ a ∧ ¬ G.Adj a x := by
    change x ∈ S.erase a \ S.filter (G.Adj a) ↔ _
    constructor
    · intro h
      obtain ⟨he, hn⟩ := Finset.mem_sdiff.mp h
      obtain ⟨hne, hs⟩ := Finset.mem_erase.mp he
      exact ⟨hs, hne, fun ha => hn (Finset.mem_filter.mpr ⟨hs, ha⟩)⟩
    · rintro ⟨hs, hne, hn⟩
      exact Finset.mem_sdiff.mpr
        ⟨Finset.mem_erase.mpr ⟨hne, hs⟩, fun h => hn (Finset.mem_filter.mp h).2⟩
  have cardM (S : Finset (Fin n)) (a : Fin n) (ha : a ∈ S) :
      (M S a).card = S.card - 1 - (N S a).card := by
    have hsub : N S a ⊆ S.erase a := by
      intro y hy
      obtain ⟨hyS, hay⟩ := Finset.mem_filter.mp hy
      exact Finset.mem_erase.mpr ⟨hay.ne.symm, hyS⟩
    change (S.erase a \ N S a).card = _
    rw [Finset.card_sdiff_of_subset hsub, Finset.card_erase_of_mem ha]
  have noTri {a b c : Fin n} (ha : a ∈ P) (hb : b ∈ P) (hc : c ∈ P)
      (hab : G.Adj a b) (hac : G.Adj a c) (hbc : G.Adj b c) : False := by
    have hva := (Finset.mem_filter.mp (hP ha)).2
    have hvb := (Finset.mem_filter.mp (hP hb)).2
    have hvc := (Finset.mem_filter.mp (hP hc)).2
    have hvN : v ∉ ({a, b, c} : Finset (Fin n)) := by simp [hva.ne, hvb.ne, hvc.ne]
    have haN : a ∉ ({b, c} : Finset (Fin n)) := by simp [hab.ne, hac.ne]
    have hbN : b ∉ ({c} : Finset (Fin n)) := by simp [hbc.ne]
    apply hG ({v, a, b, c} : Finset (Fin n))
    constructor
    · intro u hu w hw huw
      simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hu hw
      rcases hu with rfl | rfl | rfl | rfl <;>
        rcases hw with rfl | rfl | rfl | rfl <;>
        first | exact (huw rfl).elim | assumption | exact G.symm.symm _ _ (by assumption)
    · rw [Finset.card_insert_of_notMem hvN, Finset.card_insert_of_notMem haN,
        Finset.card_insert_of_notMem hbN]
      simp
  have nonedge (S : Finset (Fin n)) (hSP : S ⊆ P) (h3 : 3 ≤ S.card) :
      ∃ x ∈ S, ∃ y ∈ S, x ≠ y ∧ ¬ G.Adj x y := by
    by_contra hn
    have adj (x : Fin n) (hx : x ∈ S) (y : Fin n) (hy : y ∈ S)
        (hxy : x ≠ y) : G.Adj x y := by
      by_contra h
      exact hn ⟨x, hx, y, hy, hxy, h⟩
    obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp (show 1 < S.card by omega)
    have hsub : ({x, y} : Finset (Fin n)) ⊆ S := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact hx
      · exact hy
    have hpos : 0 < (S \ ({x, y} : Finset (Fin n))).card := by
      rw [Finset.card_sdiff_of_subset hsub, Finset.card_pair hxy]
      omega
    obtain ⟨z, hz⟩ := Finset.card_pos.mp hpos
    obtain ⟨hzS, hzN⟩ := Finset.mem_sdiff.mp hz
    have hzx : z ≠ x := fun h => hzN (by simp [h])
    have hzy : z ≠ y := fun h => hzN (by simp [h])
    exact noTri (hSP hx) (hSP hy) (hSP hzS)
      (adj x hx y hy hxy) (adj x hx z hzS hzx.symm) (adj y hy z hzS hzy.symm)
  have addInd (I : Finset (Fin n)) (a : Fin n)
      (hi : ∀ u ∈ I, ∀ w ∈ I, ¬ G.Adj u w)
      (ha : ∀ u ∈ I, ¬ G.Adj a u) :
      ∀ u ∈ insert a I, ∀ w ∈ insert a I, ¬ G.Adj u w := by
    intro u hu w hw hadj
    rcases Finset.mem_insert.mp hu with e | hu
    · rcases Finset.mem_insert.mp hw with f | hw
      · rw [e, f] at hadj
        exact G.irrefl hadj
      · rw [e] at hadj
        exact ha w hw hadj
    · rcases Finset.mem_insert.mp hw with f | hw
      · rw [f] at hadj
        exact ha u hu hadj.symm
      · exact hi u hu w hw hadj
  have triple (S : Finset (Fin n)) (hSP : S ⊆ P) (a : Fin n) (ha : a ∈ S)
      (hm : 3 ≤ (M S a).card) :
      ∃ I ⊆ S, I.card = 3 ∧ a ∈ I ∧ ∀ u ∈ I, ∀ w ∈ I, ¬ G.Adj u w := by
    obtain ⟨x, hx, y, hy, hxy, hnot⟩ :=
      nonedge (M S a) (fun z hz => hSP ((memM S a z).mp hz).1) hm
    obtain ⟨hxS, hxa, hax⟩ := (memM S a x).mp hx
    obtain ⟨hyS, hya, hay⟩ := (memM S a y).mp hy
    refine ⟨{a, x, y}, ?_, ?_, by simp, ?_⟩
    · intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl | rfl
      · exact ha
      · exact hxS
      · exact hyS
    · have hn : a ∉ ({x, y} : Finset (Fin n)) := by simp [hxa.symm, hya.symm]
      rw [Finset.card_insert_of_notMem hn, Finset.card_pair hxy]
    · apply addInd ({x, y} : Finset (Fin n)) a
      · intro u hu w hw hadj
        simp only [Finset.mem_insert, Finset.mem_singleton] at hu hw
        rcases hu with rfl | rfl <;> rcases hw with rfl | rfl
        · exact G.irrefl hadj
        · exact hnot hadj
        · exact hnot hadj.symm
        · exact G.irrefl hadj
      · intro u hu
        simp only [Finset.mem_insert, Finset.mem_singleton] at hu
        rcases hu with rfl | rfl
        · exact hax
        · exact hay
  constructor
  · intro x hx hdeg h8
    change (N P x).card ≤ 3 at hdeg
    have hc := cardM P x hx
    exact triple P (fun _ h => h) x hx (by omega)
  · intro halpha h8
    obtain ⟨h8eq, htrip⟩ := r34_and_triple_in_8 G hG v P hP h8 halpha
    refine ⟨h8eq, ?_, ?_⟩
    · intro x hx
      obtain ⟨I, hI, hind, hcard, hxI⟩ := htrip x hx
      exact ⟨I, hI, hcard, hxI, hind⟩
    · intro hmin
      by_contra hnone
      have htwo (x : Fin n) (hx : x ∈ P) : (N P x).card = 2 := by
        have hl : 2 ≤ (N P x).card := hmin x hx
        have hu : ¬ 3 ≤ (N P x).card := fun h => hnone ⟨x, hx, h⟩
        omega
      obtain ⟨x, hx⟩ := Finset.card_pos.mp (show 0 < P.card by omega)
      let W := M P x
      have hW5 : W.card = 5 := by
        change (M P x).card = 5
        rw [cardM P x hx, h8eq, htwo x hx]
      have hWP : W ⊆ P := fun z hz => ((memM P x z).mp hz).1
      have hclosed (w : Fin n) (hw : w ∈ W) : N P w ⊆ W := by
        have hl : 2 ≤ (N W w).card := by
          by_contra hn
          have hc := cardM W w hw
          obtain ⟨I, hIW, hI3, _, hi⟩ := triple W hWP w hw (by omega)
          have hxI : x ∉ I := fun h => ((memM P x x).mp (hIW h)).2.1 rfl
          have hsub : insert x I ⊆ P := by
            intro u hu
            rcases Finset.mem_insert.mp hu with rfl | hu
            · exact hx
            · exact hWP (hIW hu)
          have hnon (u : Fin n) (hu : u ∈ I) : ¬ G.Adj x u :=
            ((memM P x u).mp (hIW hu)).2.2
          have hb := halpha (insert x I) hsub (addInd I x hi hnon)
          rw [Finset.card_insert_of_notMem hxI, hI3] at hb
          omega
        have hsub : N W w ⊆ N P w := by
          intro u hu
          obtain ⟨huW, hwu⟩ := Finset.mem_filter.mp hu
          exact Finset.mem_filter.mpr ⟨hWP huW, hwu⟩
        have he : N W w = N P w := Finset.eq_of_subset_of_card_le hsub (by
          rw [htwo w (hWP hw)]
          exact hl)
        intro u hu
        rw [← he] at hu
        exact (Finset.mem_filter.mp hu).1
      have hpos : 0 < (N P x).card := by rw [htwo x hx]; decide
      obtain ⟨y, hy⟩ := Finset.card_pos.mp hpos
      obtain ⟨hyP, hxy⟩ := Finset.mem_filter.mp hy
      have hsub : N P y ⊆ ({x} : Finset (Fin n)) := by
        intro z hz
        obtain ⟨hzP, hyz⟩ := Finset.mem_filter.mp hz
        apply Finset.mem_singleton.mpr
        by_contra hzx
        have hn : ¬ G.Adj x z := fun hxz => noTri hx hyP hzP hxy hxz hyz
        have hzW : z ∈ W := (memM P x z).mpr ⟨hzP, hzx, hn⟩
        have hyN : y ∈ N P z := Finset.mem_filter.mpr ⟨hyP, hyz.symm⟩
        exact ((memM P x y).mp (hclosed z hzW hyN)).2.2 hxy
      have hle : (N P y).card ≤ 1 := by
        simpa only [Finset.card_singleton] using Finset.card_le_card hsub
      have hy2 := htwo y hyP
      omega

private lemma oma151_anchors {n : ℕ} (G F : SimpleGraph (Fin n))
    (hG : G.CliqueFree 4) (hFG : F ≤ G)
    (he : ∃ b x, F.Adj b x)
    (hd : ∀ v, (Finset.univ.filter (G.Adj v)).card ≤ 10)
    (hf : ∀ b x, F.Adj b x → 8 ≤ (Finset.univ.filter (F.Adj b)).card)
    (ht : ∀ b x, F.Adj b x →
      2 ≤ (Finset.univ.filter (fun z => F.Adj b z ∧ F.Adj x z)).card) :
    let N := fun v => Finset.univ.filter (G.Adj v)
    let P := fun v => (N v).filter (fun x => ∃ z, G.Adj v z ∧ G.Adj x z)
    let s := fun u v => (N u ∩ N v).card
    ∃ (a b c : Fin n) (A B C : Finset (Fin n)),
      a ≠ c ∧ A ⊆ P a ∧ B ⊆ P b ∧ C ⊆ P c ∧
      b ∈ A ∧ a ∈ B ∧ c ∈ B ∧ b ∈ C ∧
      (∀ u ∈ A, ∀ w ∈ A, ¬ G.Adj u w) ∧
      (∀ u ∈ B, ∀ w ∈ B, ¬ G.Adj u w) ∧
      (∀ u ∈ C, ∀ w ∈ C, ¬ G.Adj u w) ∧
      14 ≤ A.card + B.card + C.card + s a b + s b c := by
  classical
  intro N P s
  let M := fun v : Fin n => Finset.univ.filter (F.Adj v)
  let Indep := fun I : Finset (Fin n) => ∀ u ∈ I, ∀ w ∈ I, ¬ G.Adj u w
  have hM (v : Fin n) : M v ⊆ P v := by
    intro x hx
    have hfx : F.Adj v x := (Finset.mem_filter.mp hx).2
    have hpos : 0 < (Finset.univ.filter (fun z => F.Adj v z ∧ F.Adj x z)).card :=
      lt_of_lt_of_le (by decide) (ht v x hfx)
    obtain ⟨z, hz⟩ := Finset.card_pos.mp hpos
    have hz' := (Finset.mem_filter.mp hz).2
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hFG hfx⟩, z, hFG hz'.1, hFG hz'.2⟩
  have hPN (v : Fin n) : P v ⊆ N v := fun _ hx => (Finset.mem_filter.mp hx).1
  have hPs (v : Fin n) : (P v).card ≤ 10 := (Finset.card_le_card (hPN v)).trans (hd v)
  have hP8 {v x : Fin n} (hvx : F.Adj v x) : 8 ≤ (P v).card :=
    (hf v x hvx).trans (Finset.card_le_card (hM v))
  have hs2 {v x : Fin n} (hvx : F.Adj v x) : 2 ≤ s v x := by
    apply (ht v x hvx).trans (Finset.card_le_card _)
    intro z hz
    have hz' := (Finset.mem_filter.mp hz).2
    exact Finset.mem_inter.mpr
      ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hFG hz'.1⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hFG hz'.2⟩⟩
  have hsym (v x : Fin n) : s v x = s x v := by simp [s, Finset.inter_comm]
  have hlink {v x : Fin n} (hvx : G.Adj v x) :
      (P v).filter (G.Adj x) = N v ∩ N x := by
    ext z
    simp only [P, N, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_inter]
    constructor
    · exact fun h => ⟨h.1.1, h.2⟩
    · exact fun h => ⟨⟨h.1, x, hvx, h.2.symm⟩, h.2⟩
  have hside {v x : Fin n} (hvx : F.Adj v x) :
      ∃ I ⊆ P v, x ∈ I ∧ Indep I ∧ 5 ≤ I.card + s v x := by
    have hx : x ∈ P v := hM v (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hvx⟩)
    by_cases hbig : 4 ≤ s v x
    · refine ⟨{x}, Finset.singleton_subset_iff.mpr hx, by simp, ?_, ?_⟩
      · intro u hu w hw
        have hu' := Finset.mem_singleton.mp hu
        have hw' := Finset.mem_singleton.mp hw
        subst u
        subst w
        intro hxx
        exact hxx.ne rfl
      · simp only [Finset.card_singleton]
        omega
    · have hle : ((P v).filter (G.Adj x)).card ≤ 3 := by
        rw [hlink (hFG hvx)]
        change s v x ≤ 3
        omega
      obtain ⟨I, hI, hcard, hxI, hi⟩ := (oma151_link_facts G hG v).1 x hx hle (hP8 hvx)
      exact ⟨I, hI, hxI, hi, by have := hs2 hvx; omega⟩
  by_cases hlarge : ∃ (b x : Fin n) (B : Finset (Fin n)),
      F.Adj b x ∧ B ⊆ P b ∧ B.card = 4 ∧ Indep B
  · obtain ⟨b, x, B, hbx, hB, hB4, hiB⟩ := hlarge
    have hinter : 1 < (B ∩ M b).card := by
      have hu : (B ∪ M b).card ≤ (P b).card :=
        Finset.card_le_card (Finset.union_subset hB (hM b))
      have hu' := Finset.card_union_add_card_inter B (M b)
      have hm : 8 ≤ (M b).card := hf b x hbx
      have hp := hPs b
      omega
    obtain ⟨a, ha, c, hc, hac⟩ := Finset.one_lt_card.mp hinter
    obtain ⟨haB, haM⟩ := Finset.mem_inter.mp ha
    obtain ⟨hcB, hcM⟩ := Finset.mem_inter.mp hc
    have hba : F.Adj b a := (Finset.mem_filter.mp haM).2
    have hbc : F.Adj b c := (Finset.mem_filter.mp hcM).2
    obtain ⟨A, hA, hbA, hiA, hcostA⟩ := hside hba.symm
    obtain ⟨C, hC, hbC, hiC, hcostC⟩ := hside hbc.symm
    rw [hsym c b] at hcostC
    exact ⟨a, b, c, A, B, C, hac, hA, hB, hC, hbA, haB, hcB, hbC,
      hiA, hiB, hiC, by omega⟩
  · have hsmall {v x : Fin n} (hvx : F.Adj v x) :
        ∀ I ⊆ P v, Indep I → I.card ≤ 3 := by
      intro I hI hi
      by_contra! hcard
      obtain ⟨J, hJI, hJ4⟩ := Finset.exists_subset_card_eq (show 4 ≤ I.card by omega)
      exact hlarge ⟨v, x, J, hvx, hJI.trans hI, hJ4,
        fun u hu w hw => hi u (hJI hu) w (hJI hw)⟩
    have hdata {v x : Fin n} (hvx : F.Adj v x) :=
      (oma151_link_facts G hG v).2 (hsmall hvx) (hP8 hvx)
    obtain ⟨b, x, hbx⟩ := he
    have hEq : M b = P b := by
      apply Finset.eq_of_subset_of_card_le (hM b)
      rw [(hdata hbx).1]
      exact hf b x hbx
    have hmin : ∀ y ∈ P b, 2 ≤ ((P b).filter (G.Adj y)).card := by
      intro y hy
      have hyM : y ∈ M b := hEq.symm ▸ hy
      have hby : F.Adj b y := (Finset.mem_filter.mp hyM).2
      rw [hlink (hFG hby)]
      exact hs2 hby
    obtain ⟨a, ha, ha3⟩ := (hdata hbx).2.2 hmin
    obtain ⟨B, hB, hB3, haB, hiB⟩ := (hdata hbx).2.1 a ha
    have hc_exists : ∃ c ∈ B, a ≠ c := by
      obtain ⟨u, hu, w, hw, huw⟩ := Finset.one_lt_card.mp (show 1 < B.card by omega)
      by_cases hua : u = a
      · exact ⟨w, hw, hua ▸ huw⟩
      · exact ⟨u, hu, Ne.symm hua⟩
    obtain ⟨c, hc, hac⟩ := hc_exists
    have haM : a ∈ M b := hEq.symm ▸ ha
    have hcM : c ∈ M b := hEq.symm ▸ hB hc
    have hba : F.Adj b a := (Finset.mem_filter.mp haM).2
    have hbc : F.Adj b c := (Finset.mem_filter.mp hcM).2
    have hab : F.Adj a b := hba.symm
    have hcb : F.Adj c b := hbc.symm
    obtain ⟨A, hA, hA3, hbA, hiA⟩ := (hdata hab).2.1 b
      (hM a (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hab⟩))
    obtain ⟨C, hC, hC3, hbC, hiC⟩ := (hdata hcb).2.1 b
      (hM c (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcb⟩))
    have hsa : 3 ≤ s a b := by
      change 3 ≤ ((P b).filter (G.Adj a)).card at ha3
      rw [hlink (hFG hba)] at ha3
      calc
        3 ≤ s b a := ha3
        _ = s a b := hsym b a
    have hsc := hs2 hbc
    exact ⟨a, b, c, A, B, C, hac, hA, hB, hC, hbA, haB, hc, hbC,
      hiA, hiB, hiC, by omega⟩


private lemma oma151_delete (h2 : H2) (h4 : H4) {n : ℕ} (G : SimpleGraph (Fin n))
    (hG : G.CliqueFree 4) (hn : 47 ≤ n)
    (hd : ∀ v, (Finset.univ.filter (G.Adj v)).card ≤ 10) :
    let N := fun v => Finset.univ.filter (G.Adj v)
    let P := fun v => (N v).filter (fun x => ∃ z, G.Adj v z ∧ G.Adj x z)
    let s := fun u v => (N u ∩ N v).card
    (∃ (a b c : Fin n) (A B C : Finset (Fin n)),
      a ≠ c ∧ A ⊆ P a ∧ B ⊆ P b ∧ C ⊆ P c ∧
      b ∈ A ∧ a ∈ B ∧ c ∈ B ∧ b ∈ C ∧
      (∀ u ∈ A, ∀ w ∈ A, ¬ G.Adj u w) ∧
      (∀ u ∈ B, ∀ w ∈ B, ¬ G.Adj u w) ∧
      (∀ u ∈ C, ∀ w ∈ C, ¬ G.Adj u w) ∧
      14 ≤ A.card + B.card + C.card + s a b + s b c) →
    G.cliqueTransversalNumber ≤ n - 11 := by
  classical
  intro N P s h
  obtain ⟨a, b, c, A, B, C, hac, hA, hB, hC, hbA, haB, hcB, hbC,
    hiA, hiB, hiC, hcost⟩ := h
  let Da := N a \ A
  let Db := N b \ B
  let Dc := N c \ C
  let Anch : Finset (Fin n) := {a, b, c}
  let D := Anch ∪ (Da ∪ Db ∪ Dc)
  have hPN (v : Fin n) : P v ⊆ N v := fun _ hx => (Finset.mem_filter.mp hx).1
  have hab_adj : G.Adj a b := (Finset.mem_filter.mp (hPN a (hA hbA))).2
  have hcb_adj : G.Adj c b := (Finset.mem_filter.mp (hPN c (hC hbC))).2
  have hab_ne : a ≠ b := hab_adj.ne
  have hbc_ne : b ≠ c := hcb_adj.ne.symm
  have hAnch_card : Anch.card = 3 := by
    have ha_not : a ∉ ({b, c} : Finset (Fin n)) := by simp [hab_ne, hac]
    have hb_not : b ∉ ({c} : Finset (Fin n)) := by simp [hbc_ne]
    dsimp [Anch]
    rw [Finset.card_insert_of_notMem ha_not, Finset.card_insert_of_notMem hb_not, Finset.card_singleton]
  have hcharge {u v : Fin n} {I J : Finset (Fin n)}
      (hvI : v ∈ I) (huJ : u ∈ J)
      (hi : ∀ x ∈ I, ∀ y ∈ I, ¬ G.Adj x y)
      (hj : ∀ x ∈ J, ∀ y ∈ J, ¬ G.Adj x y) :
      s u v ≤ ((N u \ I) ∩ (N v \ J)).card := by
    apply Finset.card_le_card
    intro z hz
    obtain ⟨hzu, hzv⟩ := Finset.mem_inter.mp hz
    exact Finset.mem_inter.mpr
      ⟨Finset.mem_sdiff.mpr ⟨hzu, fun hzI => hi v hvI z hzI (Finset.mem_filter.mp hzv).2⟩,
        Finset.mem_sdiff.mpr ⟨hzv, fun hzJ => hj u huJ z hzJ (Finset.mem_filter.mp hzu).2⟩⟩
  have hab := hcharge hbA haB hiA hiB
  have hbc := hcharge hcB hbC hiB hiC
  have hbc' : (Db ∩ Dc).card ≤ ((Da ∪ Db) ∩ Dc).card := by
    apply Finset.card_le_card
    intro z hz
    obtain ⟨hzB, hzC⟩ := Finset.mem_inter.mp hz
    exact Finset.mem_inter.mpr ⟨Finset.mem_union.mpr (Or.inr hzB), hzC⟩
  have hu1 := Finset.card_union_add_card_inter Da Db
  have hu2 := Finset.card_union_add_card_inter (Da ∪ Db) Dc
  have hda : Da.card + A.card = (N a).card := by
    change (N a \ A).card + A.card = (N a).card
    rw [Finset.card_sdiff_of_subset (hA.trans (hPN a))]
    have := Finset.card_le_card (hA.trans (hPN a))
    omega
  have hdb : Db.card + B.card = (N b).card := by
    change (N b \ B).card + B.card = (N b).card
    rw [Finset.card_sdiff_of_subset (hB.trans (hPN b))]
    have := Finset.card_le_card (hB.trans (hPN b))
    omega
  have hdc : Dc.card + C.card = (N c).card := by
    change (N c \ C).card + C.card = (N c).card
    rw [Finset.card_sdiff_of_subset (hC.trans (hPN c))]
    have := Finset.card_le_card (hC.trans (hPN c))
    omega
  have hD : D.card ≤ 19 := by
    change s a b ≤ (Da ∩ Db).card at hab
    change s b c ≤ (Db ∩ Dc).card at hbc
    have hU := Finset.card_union_le Anch (Da ∪ Db ∪ Dc)
    change D.card ≤ Anch.card + (Da ∪ Db ∪ Dc).card at hU
    have ha := hd a
    have hb := hd b
    have hc := hd c
    change (N a).card ≤ 10 at ha
    change (N b).card ≤ 10 at hb
    change (N c).card ≤ 10 at hc
    omega
  let I : Fin n → Finset (Fin n) := fun w => if w = a then A else if w = b then B else C
  have hcases : ∀ w ∈ Anch, w = a ∨ w = b ∨ w = c := by
    intro w hw; simpa [Anch] using hw
  have hmemP (v x : Fin n) (hx : x ∈ P v) : G.Adj v x ∧ ∃ z, G.Adj v z ∧ G.Adj x z := by
    have := Finset.mem_filter.mp hx
    exact ⟨(Finset.mem_filter.mp this.1).2, this.2⟩
  refine extend_from_28 h2 h4 G hG Anch D I (k := 11) (by omega) (by omega)
    (fun x hx => Finset.mem_union.mpr (Or.inl hx)) ?_ ?_ ?_ ?_
  · intro w hw x hx
    rcases hcases w hw with rfl | rfl | rfl
    · have hx' : x ∈ Da := by simpa [Da, I, N] using hx
      exact Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl hx')))))
    · have hx' : x ∈ Db := by simpa [Db, I, N, hab_ne.symm] using hx
      exact Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr hx')))))
    · have hx' : x ∈ Dc := by simpa [Dc, I, N, hac.symm, hbc_ne.symm] using hx
      exact Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inr hx')))
  · intro w hw x hx
    rcases hcases w hw with rfl | rfl | rfl
    · exact hmemP w x (hA (by simpa [I] using hx))
    · exact hmemP w x (hB (by simpa [I, hab_ne.symm] using hx))
    · exact hmemP w x (hC (by simpa [I, hac.symm, hbc_ne.symm] using hx))
  · intro w hw x hx y hy
    rcases hcases w hw with rfl | rfl | rfl
    · exact hiA x (by simpa [I] using hx) y (by simpa [I] using hy)
    · exact hiB x (by simpa [I, hab_ne.symm] using hx) y (by simpa [I, hab_ne.symm] using hy)
    · exact hiC x (by simpa [I, hac.symm, hbc_ne.symm] using hx) y (by simpa [I, hac.symm, hbc_ne.symm] using hy)
  · intro w hw x hx hadj
    rcases hcases w hw with rfl | rfl | rfl <;> rcases hcases x hx with rfl | rfl | rfl
    · exact (G.irrefl hadj).elim
    · simpa [I] using hbA
    · exact (hiB w haB x hcB hadj).elim
    · simpa [I, hab_ne.symm] using haB
    · exact (G.irrefl hadj).elim
    · simpa [I, hab_ne.symm] using hcB
    · exact (hiB w hcB x haB hadj).elim
    · simpa [I, hac.symm, hbc_ne.symm] using hbC
    · exact (G.irrefl hadj).elim
-- === END HELPERS ===

theorem main : H1 → H2 → H3 → H4 → OMA.R_Erdos151_erdos_151_variants_cliqueFree_four_R1_H1_R1_H1_R1.H1 := by
  classical
  intro h1 h2 h3 h4 n G hG h11 hdeg hS
  by_cases h12 : 12 ≤ Erdos151.H n
  · exact h1 n G hG h12 hdeg hS
  · have hH : Erdos151.H n = 11 := by omega
    have hn : 47 ≤ n := h3 n h11
    have hd (v : Fin n) : (Finset.univ.filter (G.Adj v)).card ≤ 10 := by
      have hv := hdeg v
      omega
    rw [hH]
    obtain hgood | ⟨F, hFG, he, hf, ht⟩ := oma151_core G hG h11 h4
    · exact hgood
    · exact oma151_delete h2 h4 G hG hn hd (oma151_anchors G F hG hFG he hd hf ht)

end Proof

end OMA.R_Erdos151_erdos_151_variants_cliqueFree_four_R1_H1_R1_H1_R1_H1_R1
