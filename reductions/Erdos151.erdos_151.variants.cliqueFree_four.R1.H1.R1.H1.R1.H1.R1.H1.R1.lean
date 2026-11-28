import OMAReductions.R_Erdos151_erdos_151_variants_cliqueFree_four_R1_H1_R1_H1_R1_H1_R1
import Mathlib

/-! Closing H(n) = 12 for all n >= 54 (all K_4-free graphs through n = 59 except
possibly n = 53) via a 4-anchor K_{1,3} star vs. Seymour-forced cubic-link C_4
square overlap deletion argument (deletion cost <= 26, leaving >= 28 vertices). -/

open Finset SimpleGraph
open scoped Classical

namespace OMA.R_Erdos151_erdos_151_variants_cliqueFree_four_R1_H1_R1_H1_R1_H1_R1_H1_R1

/-- Remaining open core: either (H n = 12 and n = 53) or 13 <= H n. -/
def H1 : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)), G.CliqueFree 4 →
    ((Erdos151.H n = 12 ∧ n = 53) ∨ 13 ≤ Erdos151.H n) →
    (∀ v, (univ.filter (G.Adj v)).card < Erdos151.H n) →
    (∃ S : Finset (Fin n), S.Nonempty ∧
      ∀ v ∈ S, 8 ≤ (S.filter (G.Adj v)).card) →
    cliqueTransversalNumber G ≤ n - Erdos151.H n

/-- Ramsey upper bound R(3,8) <= 28. -/
def H2 : Prop :=
  8 ≤ Erdos151.H 28

/-- Ramsey lower bound R(3,12) >= 53. -/
def H3 : Prop :=
  ∀ n, 12 ≤ Erdos151.H n → 53 ≤ n

/-- Bikov 7-vertex link-extension lemma and Seymour triangle-count bound T(F) >= |E(F)|
for subgraph-minimal (3,3)-arrowing graphs F. -/
def H4 : Prop :=
  (∀ (k : ℕ) (L : SimpleGraph (Fin k)), k ≤ 7 → L.CliqueFree 3 →
    ∀ c : Fin k → Fin k → Bool, (∀ x y, c x y = c y x) →
      ∃ d : Fin k → Bool, ∀ x y, L.Adj x y → ¬ (d x = c x y ∧ d y = c x y)) ∧
  (∀ (n : ℕ) (F : SimpleGraph (Fin n)),
    (¬ ∃ c : Fin n → Fin n → Bool, (∀ x y, c x y = c y x) ∧
      ∀ x y z, F.Adj x y → F.Adj x z → F.Adj y z → ¬ (c x y = c x z ∧ c x y = c y z)) →
    (∀ F' : SimpleGraph (Fin n), F' < F →
      ∃ c : Fin n → Fin n → Bool, (∀ x y, c x y = c y x) ∧
        ∀ x y z, F'.Adj x y → F'.Adj x z → F'.Adj y z → ¬ (c x y = c x z ∧ c x y = c y z)) →
    3 * (∑ v : Fin n, (univ.filter (F.Adj v)).card) ≤
      ∑ v : Fin n, ∑ u ∈ univ.filter (F.Adj v),
        (univ.filter (fun z => F.Adj v z ∧ F.Adj u z)).card)

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

private lemma beta_of_coloring_28 (h2 : H2) (h4 : (∀ (k : ℕ) (L : SimpleGraph (Fin k)), k ≤ 7 → L.CliqueFree 3 →
    ∀ c : Fin k → Fin k → Bool, (∀ x y, c x y = c y x) →
      ∃ d : Fin k → Bool, ∀ x y, L.Adj x y → ¬ (d x = c x y ∧ d y = c x y)))
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

private lemma extend_from_28 (h2 : H2) (h4 : (∀ (k : ℕ) (L : SimpleGraph (Fin k)), k ≤ 7 → L.CliqueFree 3 →
    ∀ c : Fin k → Fin k → Bool, (∀ x y, c x y = c y x) →
      ∃ d : Fin k → Bool, ∀ x y, L.Adj x y → ¬ (d x = c x y ∧ d y = c x y))) {n k : ℕ}
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

private theorem restore_vertex_coloring (h4 : (∀ (k : ℕ) (L : SimpleGraph (Fin k)), k ≤ 7 → L.CliqueFree 3 →
    ∀ c : Fin k → Fin k → Bool, (∀ x y, c x y = c y x) →
      ∃ d : Fin k → Bool, ∀ x y, L.Adj x y → ¬ (d x = c x y ∧ d y = c x y))) {n : ℕ}
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



private lemma oma151_h12_core {n : ℕ} (G : SimpleGraph (Fin n))
    (hG : G.CliqueFree 4) (h12 : 12 ≤ Erdos151.H n) (h4 : H4) :
    G.cliqueTransversalNumber ≤ n - 12 ∨
      ∃ F : SimpleGraph (Fin n), F ≤ G ∧ (∃ b x, F.Adj b x) ∧
        (∀ b x, F.Adj b x → 8 ≤ (Finset.univ.filter (F.Adj b)).card) ∧
        (∀ b x, F.Adj b x →
          2 ≤ (Finset.univ.filter (fun z => F.Adj b z ∧ F.Adj x z)).card) ∧
        3 * (∑ v : Fin n, (univ.filter (F.Adj v)).card) ≤
          ∑ v : Fin n, ∑ u ∈ univ.filter (F.Adj v),
            (univ.filter (fun z => F.Adj v z ∧ F.Adj u z)).card := by
  classical
  by_cases hcol : ∃ c : Fin n → Fin n → Bool,
      (∀ x y, c x y = c y x) ∧
        (∀ x y z, G.Adj x y → G.Adj x z → G.Adj y z →
          ¬ (c x y = c x z ∧ c x y = c y z))
  · obtain ⟨c, hs, hc⟩ := hcol
    obtain ⟨B, hB, havoid⟩ := free_of_coloring G c hs hc
    exact Or.inl (transversal_le_of_free G B (h12.trans hB) havoid)
  · obtain ⟨Q, hQG, hQbad, hmin⟩ := minimal_uncolorable_subgraph G hcol
    have hQ : Q.CliqueFree 4 := by
      intro K hK
      apply hG K
      refine ⟨?_, hK.2⟩
      intro a ha b hb hab
      exact hQG a b (hK.1 ha hb hab)
    have hedge : ∃ b x, Q.Adj b x := by
      by_contra hn
      apply hQbad
      refine ⟨fun _ _ => false, ?_, ?_⟩
      · intro x y
        rfl
      · intro x y z hxy hxz hyz hm
        exact (hn ⟨x, y, hxy⟩).elim
    have hminimal : ∀ R : SimpleGraph (Fin n), R < Q →
        ∃ c : Fin n → Fin n → Bool, (∀ x y, c x y = c y x) ∧
          ∀ x y z, R.Adj x y → R.Adj x z → R.Adj y z →
            ¬ (c x y = c x z ∧ c x y = c y z) := by
      intro R hlt
      have hRQ : R ≤ Q := le_of_lt hlt
      have hmiss : ∃ x y, Q.Adj x y ∧ ¬ R.Adj x y := by
        by_contra hn
        apply (not_le_of_gt hlt)
        intro x y hxy
        by_contra hnot
        exact hn ⟨x, y, hxy, hnot⟩
      exact hmin R hRQ hmiss
    have hdegQ : ∀ b x, Q.Adj b x →
        8 ≤ (Finset.univ.filter (Q.Adj b)).card := by
      intro b x hbx
      by_contra hlt
      have hle : (Finset.univ.filter (Q.Adj b)).card ≤ 7 := by omega
      let R : SimpleGraph (Fin n) := {
        Adj := fun a c => Q.Adj a c ∧ a ≠ b ∧ c ≠ b
        symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
        loopless := ⟨fun _ h => Q.irrefl h.1⟩ }
      have hRle : R ≤ Q := by
        intro a c hac
        exact hac.1
      have hmiss : ∃ a c, Q.Adj a c ∧ ¬ R.Adj a c :=
        ⟨b, x, hbx, by simp [R]⟩
      obtain ⟨c, hs, hc⟩ := hmin R hRle hmiss
      have hR : ∀ a c, R.Adj a c ↔ Q.Adj a c ∧ a ≠ b ∧ c ≠ b := by
        intro a c
        rfl
      obtain ⟨d, hds, hdc⟩ :=
        restore_vertex_coloring h4.1 Q R hQ b hle hR ⟨c, hs, hc⟩
      exact hQbad ⟨d, hds, hdc⟩
    have hcommon : ∀ b x, Q.Adj b x →
        2 ≤ (Finset.univ.filter (fun z => Q.Adj b z ∧ Q.Adj x z)).card := by
      intro b x hbx
      by_contra hlt
      have hle :
          (Finset.univ.filter (fun z => Q.Adj b z ∧ Q.Adj x z)).card ≤ 1 := by
        omega
      have hsmall :
          ¬ ∃ z t : Fin n, z ≠ t ∧ Q.Adj b z ∧ Q.Adj x z ∧
            Q.Adj b t ∧ Q.Adj x t := by
        rintro ⟨z, t, hzt, hbz, hxz, hbt, hxt⟩
        have hz : z ∈ Finset.univ.filter (fun z => Q.Adj b z ∧ Q.Adj x z) :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨hbz, hxz⟩⟩
        have ht : t ∈ Finset.univ.filter (fun z => Q.Adj b z ∧ Q.Adj x z) :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨hbt, hxt⟩⟩
        have hlt' := Finset.one_lt_card.mpr ⟨z, hz, t, ht, hzt⟩
        omega
      let R : SimpleGraph (Fin n) := {
        Adj := fun a c => Q.Adj a c ∧
          ¬ ((a = b ∧ c = x) ∨ (a = x ∧ c = b))
        symm := ⟨fun a c h => ⟨h.1.symm, by
          intro he
          apply h.2
          rcases he with ⟨ha, hc⟩ | ⟨ha, hc⟩
          · exact Or.inr ⟨hc, ha⟩
          · exact Or.inl ⟨hc, ha⟩⟩⟩
        loopless := ⟨fun _ h => Q.irrefl h.1⟩ }
      have hRle : R ≤ Q := by
        intro a c hac
        exact hac.1
      have hmiss : ∃ a c, Q.Adj a c ∧ ¬ R.Adj a c :=
        ⟨b, x, hbx, by simp [R]⟩
      obtain ⟨c, hs, hc⟩ := hmin R hRle hmiss
      have hR : ∀ a c, R.Adj a c ↔ Q.Adj a c ∧
          ¬ ((a = b ∧ c = x) ∨ (a = x ∧ c = b)) := by
        intro a c
        rfl
      obtain ⟨d, hds, hdc⟩ :=
        restore_edge_coloring Q R b x hR hsmall ⟨c, hs, hc⟩
      exact hQbad ⟨d, hds, hdc⟩
    have hsey := h4.2 n Q hQbad hminimal
    refine Or.inr ⟨Q, hQG, hedge, ?_, ?_, hsey⟩
    · intro b x hbx
      exact hdegQ b x hbx
    · intro b x hbx
      exact hcommon b x hbx

private theorem h12_positive_dense_link {n : ℕ} (F : SimpleGraph (Fin n))
    (he : ∃ b x, F.Adj b x)
    (hsey : 3 * (∑ v : Fin n, (univ.filter (F.Adj v)).card) ≤
      ∑ v : Fin n, ∑ u ∈ univ.filter (F.Adj v),
        (univ.filter (fun z => F.Adj v z ∧ F.Adj u z)).card) :
    ∃ b : Fin n, (∃ x, F.Adj b x) ∧
      3 * (univ.filter (F.Adj b)).card ≤
        ∑ u ∈ univ.filter (F.Adj b),
          (univ.filter (fun z => F.Adj b z ∧ F.Adj u z)).card := by
  classical
  let a (v : Fin n) := 3 * (univ.filter (F.Adj v)).card
  let c (v : Fin n) := ∑ u ∈ univ.filter (F.Adj v),
    (univ.filter (fun z => F.Adj v z ∧ F.Adj u z)).card
  by_contra hn
  have hlt (v : Fin n) (hv : ∃ x, F.Adj v x) : c v < a v := by
    have hnot : ¬ a v ≤ c v := fun h => hn ⟨v, hv, h⟩
    omega
  have hle (v : Fin n) : c v ≤ a v := by
    by_cases hv : ∃ x, F.Adj v x
    · exact (hlt v hv).le
    · have hz : univ.filter (F.Adj v) = (∅ : Finset (Fin n)) := by
        ext x
        have hx : ¬ F.Adj v x := fun h => hv ⟨x, h⟩
        simp [hx]
      simp [a, c, hz]
  obtain ⟨b, x, hbx⟩ := he
  have hs : (∑ v : Fin n, c v) < ∑ v : Fin n, a v :=
    Finset.sum_lt_sum (fun v _ => hle v) ⟨b, Finset.mem_univ b, hlt b ⟨x, hbx⟩⟩
  rw [Finset.mul_sum] at hsey
  exact (not_lt_of_ge (show (∑ v : Fin n, a v) ≤ ∑ v : Fin n, c v from hsey)) hs

private theorem h12_star_budget_certificate {n : ℕ} (G F : SimpleGraph (Fin n))
    (hG : G.CliqueFree 4) (hFG : F ≤ G)
    (hf : ∀ b x, F.Adj b x → 8 ≤ (univ.filter (F.Adj b)).card)
    (ht : ∀ b x, F.Adj b x →
      2 ≤ (univ.filter (fun z => F.Adj b z ∧ F.Adj x z)).card)
    (b : Fin n) (J L : Finset (Fin n))
    (hJ : J ⊆ univ.filter (F.Adj b)) (hL : L ⊆ J) (hLc : L.card = 3)
    (hJi : ∀ x ∈ J, ∀ y ∈ J, ¬ G.Adj x y)
    (hb : let d (x : Fin n) := (univ.filter (fun z => G.Adj b z ∧ G.Adj x z)).card
      let q (x : Fin n) := (univ.filter (G.Adj x)).card - 1 - d x -
        (if d x ≤ 4 then 2 else if d x ≤ 6 then 1 else 0)
      1 + ((univ.filter (G.Adj b)) \ (J \ L)).card + (∑ x ∈ L, q x) ≤ 26) :
    ∃ (A : Finset (Fin n)) (I : Fin n → Finset (Fin n)),
      A.card = 4 ∧
      ((A.biUnion (fun w => (univ.filter (G.Adj w)) \ I w)) \ A).card ≤ 22 ∧
      (∀ w ∈ A, ∀ x ∈ I w, G.Adj w x ∧ ∃ z, G.Adj w z ∧ G.Adj x z) ∧
      (∀ w ∈ A, ∀ x ∈ I w, ∀ y ∈ I w, ¬ G.Adj x y) ∧
      (∀ w ∈ A, ∀ x ∈ A, G.Adj w x → x ∈ I w) := by
  classical
  let N (x : Fin n) := univ.filter (G.Adj x)
  let U (x : Fin n) := univ.filter (F.Adj x)
  let C (x : Fin n) := univ.filter (fun z => G.Adj b z ∧ G.Adj x z)
  let T (x : Fin n) := insert b (C x)
  let X (x : Fin n) := U x \ T x
  let Y (x : Fin n) := N x \ T x
  let d (x : Fin n) := (C x).card
  let r (x : Fin n) : ℕ := if d x ≤ 4 then 2 else if d x ≤ 6 then 1 else 0
  let q (x : Fin n) := (N x).card - 1 - d x - r x
  change 1 + (N b \ (J \ L)).card + (∑ x ∈ L, q x) ≤ 26 at hb
  have tri (u v : Fin n) (huv : F.Adj u v) :
      G.Adj u v ∧ ∃ z, G.Adj u z ∧ G.Adj v z := by
    have hpos : 0 < (univ.filter (fun z => F.Adj u z ∧ F.Adj v z)).card :=
      lt_of_lt_of_le (by decide : 0 < 2) (ht u v huv)
    obtain ⟨z, hz⟩ := Finset.card_pos.mp hpos
    obtain ⟨huz, hvz⟩ := (Finset.mem_filter.mp hz).2
    exact ⟨hFG huv, z, hFG huz, hFG hvz⟩
  have hJF (x : Fin n) (hx : x ∈ J) : F.Adj b x := (Finset.mem_filter.mp (hJ hx)).2
  have hLF (x : Fin n) (hx : x ∈ L) : F.Adj x b := (hJF x (hL hx)).symm
  have hbL : b ∉ L := fun hx => F.irrefl (hLF b hx)
  have hJN : J ⊆ N b := fun x hx =>
    Finset.mem_filter.mpr ⟨Finset.mem_univ x, hFG (hJF x hx)⟩
  have hUN (x : Fin n) : U x ⊆ N x := fun z hz =>
    Finset.mem_filter.mpr ⟨Finset.mem_univ z, hFG (Finset.mem_filter.mp hz).2⟩
  have hTc (x : Fin n) : (T x).card = d x + 1 := by
    have hnot : b ∉ C x := fun hz => G.irrefl (Finset.mem_filter.mp hz).2.1
    exact Finset.card_insert_of_notMem hnot
  have hTN (x : Fin n) (hx : x ∈ L) : T x ⊆ N x := by
    intro z hz
    rcases Finset.mem_insert.mp hz with he | hc
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ z, he.symm ▸ hFG (hLF x hx)⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ z, (Finset.mem_filter.mp hc).2.2⟩
  have hXY (x : Fin n) : X x ⊆ Y x := fun z hz =>
    Finset.mem_sdiff.mpr ⟨hUN x (Finset.mem_sdiff.mp hz).1, (Finset.mem_sdiff.mp hz).2⟩
  have hXsize (x : Fin n) (hx : x ∈ L) : 8 ≤ (X x).card + (d x + 1) := by
    have hsub : U x ⊆ X x ∪ T x := by
      intro z hz
      by_cases hzT : z ∈ T x
      · exact Finset.mem_union.mpr (Or.inr hzT)
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_sdiff.mpr ⟨hz, hzT⟩))
    have hle := (Finset.card_le_card hsub).trans (Finset.card_union_le (X x) (T x))
    rw [hTc] at hle
    exact (hf x b (hLF x hx)).trans hle
  have hXout (x z : Fin n) (hz : z ∈ X x) : ¬ G.Adj b z := by
    intro hbz
    have hxz := hFG (Finset.mem_filter.mp (Finset.mem_sdiff.mp hz).1).2
    have hzC : z ∈ C x := Finset.mem_filter.mpr ⟨Finset.mem_univ z, hbz, hxz⟩
    exact (Finset.mem_sdiff.mp hz).2 (Finset.mem_insert.mpr (Or.inr hzC))
  have noTri (x y z t : Fin n) (hy : y ∈ X x) (hz : z ∈ X x) (ht' : t ∈ X x)
      (hyz : G.Adj y z) (hyt : G.Adj y t) (hzt : G.Adj z t) : False := by
    have hxy := hFG (Finset.mem_filter.mp (Finset.mem_sdiff.mp hy).1).2
    have hxz := hFG (Finset.mem_filter.mp (Finset.mem_sdiff.mp hz).1).2
    have hxt := hFG (Finset.mem_filter.mp (Finset.mem_sdiff.mp ht').1).2
    have hxN : x ∉ ({y, z, t} : Finset (Fin n)) := by simp [hxy.ne, hxz.ne, hxt.ne]
    have hyN : y ∉ ({z, t} : Finset (Fin n)) := by simp [hyz.ne, hyt.ne]
    have hzN : z ∉ ({t} : Finset (Fin n)) := by simp [hzt.ne]
    apply hG ({x, y, z, t} : Finset (Fin n))
    constructor
    · intro a ha c hc hac
      simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at ha hc
      rcases ha with rfl | rfl | rfl | rfl <;>
        rcases hc with rfl | rfl | rfl | rfl <;>
        first | exact (hac rfl).elim | assumption | exact G.symm.symm _ _ (by assumption)
    · rw [Finset.card_insert_of_notMem hxN, Finset.card_insert_of_notMem hyN,
        Finset.card_insert_of_notMem hzN] <;> simp
  have pair (x : Fin n) (hsize : 3 ≤ (X x).card) :
      ∃ y ∈ X x, ∃ z ∈ X x, y ≠ z ∧ ¬ G.Adj y z := by
    by_contra hn
    have adj (y z : Fin n) (hy : y ∈ X x) (hz : z ∈ X x) (hne : y ≠ z) : G.Adj y z := by
      by_contra ha
      exact hn ⟨y, hy, z, hz, hne, ha⟩
    obtain ⟨y, hy, z, hz, hyz⟩ := Finset.one_lt_card.mp (by omega : 1 < (X x).card)
    have hsub : ({y, z} : Finset (Fin n)) ⊆ X x := by
      intro t ht'
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht'
      exact ht'.elim (fun h => h.symm ▸ hy) (fun h => h.symm ▸ hz)
    have hpos : 0 < (X x \ ({y, z} : Finset (Fin n))).card := by
      rw [Finset.card_sdiff_of_subset hsub, Finset.card_pair hyz]
      omega
    obtain ⟨t, ht'⟩ := Finset.card_pos.mp hpos
    obtain ⟨htX, htN⟩ := Finset.mem_sdiff.mp ht'
    have hty : t ≠ y := fun h => htN (by simp [h])
    have htz : t ≠ z := fun h => htN (by simp [h])
    exact noTri x y z t hy hz htX (adj y z hy hz hyz)
      (adj y t hy htX hty.symm) (adj z t hz htX htz.symm)
  have hex (x : Fin n) (hx : x ∈ L) : ∃ E : Finset (Fin n), E ⊆ X x ∧
      (∀ y ∈ E, ∀ z ∈ E, ¬ G.Adj y z) ∧ E.card = r x := by
    have hsize := hXsize x hx
    by_cases h4 : d x ≤ 4
    · obtain ⟨y, hy, z, hz, hyz, hn⟩ := pair x (by omega)
      have hn' : ¬ G.Adj z y := fun h => hn h.symm
      refine ⟨{y, z}, ?_, ?_, ?_⟩
      · intro t ht'
        simp only [Finset.mem_insert, Finset.mem_singleton] at ht'
        exact ht'.elim (fun h => h.symm ▸ hy) (fun h => h.symm ▸ hz)
      · intro u hu v hv
        simp only [Finset.mem_insert, Finset.mem_singleton] at hu hv
        rcases hu with rfl | rfl <;> rcases hv with rfl | rfl <;>
          first | assumption | exact (fun h => G.irrefl h)
      · simp [r, h4, Finset.card_pair hyz]
    · by_cases h6 : d x ≤ 6
      · obtain ⟨y, hy⟩ := Finset.card_pos.mp (by omega : 0 < (X x).card)
        refine ⟨{y}, ?_, ?_, by simp [r, h4, h6]⟩
        · intro z hz
          have he := Finset.mem_singleton.mp hz
          exact he.symm ▸ hy
        · intro u hu v hv
          simp only [Finset.mem_singleton] at hu hv
          intro h
          rw [hu, hv] at h
          exact G.irrefl h
      · exact ⟨∅, by simp, by simp, by simp [r, h4, h6]⟩
  let E (x : Fin n) : Finset (Fin n) := if hx : x ∈ L then Classical.choose (hex x hx) else ∅
  have hE (x : Fin n) (hx : x ∈ L) : E x ⊆ X x ∧
      (∀ y ∈ E x, ∀ z ∈ E x, ¬ G.Adj y z) ∧ (E x).card = r x := by
    simpa only [E, dif_pos hx] using (Classical.choose_spec (hex x hx))
  have hEY (x : Fin n) (hx : x ∈ L) : E x ⊆ Y x :=
    fun z hz => hXY x ((hE x hx).1 hz)
  have hcharge (x : Fin n) (hx : x ∈ L) : (Y x \ E x).card = q x := by
    rw [Finset.card_sdiff_of_subset (hEY x hx)]
    change (N x \ T x).card - (E x).card = q x
    rw [Finset.card_sdiff_of_subset (hTN x hx), hTc, (hE x hx).2.2]
    change (N x).card - (d x + 1) - r x = (N x).card - 1 - d x - r x
    omega
  let A := insert b L
  let I (w : Fin n) := if w = b then J else insert b (E w)
  have hAc : A.card = 4 := by
    change (insert b L).card = 4
    rw [Finset.card_insert_of_notMem hbL, hLc]
  have hIb : I b = J := by simp [I]
  have hIx (w : Fin n) (hw : w ≠ b) : I w = insert b (E w) := by simp [I, hw]
  have leaf (w : Fin n) (hw : w ∈ A) (hne : w ≠ b) : w ∈ L :=
    (Finset.mem_insert.mp hw).resolve_left hne
  have hcover : ((A.biUnion (fun w => N w \ I w)) \ A) ⊆
      (N b \ J) ∪ L.biUnion (fun x => Y x \ E x) := by
    intro z hz
    obtain ⟨hzU, hzA⟩ := Finset.mem_sdiff.mp hz
    obtain ⟨w, hwA, hzw⟩ := Finset.mem_biUnion.mp hzU
    obtain ⟨hzN, hzI⟩ := Finset.mem_sdiff.mp hzw
    by_cases hwb : w = b
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_sdiff.mpr
        ⟨hwb ▸ hzN, fun hzJ => hzI (by simpa only [hwb, hIb] using hzJ)⟩))
    · have hwL := leaf w hwA hwb
      by_cases hzT : z ∈ T w
      · rcases Finset.mem_insert.mp hzT with hzb | hzC
        · exact (hzA (Finset.mem_insert.mpr (Or.inl hzb))).elim
        · obtain ⟨hbz, hwz⟩ := (Finset.mem_filter.mp hzC).2
          exact Finset.mem_union.mpr (Or.inl (Finset.mem_sdiff.mpr
            ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ z, hbz⟩,
              fun hzJ => hJi w (hL hwL) z hzJ hwz⟩))
      · have hzY : z ∈ Y w := Finset.mem_sdiff.mpr ⟨hzN, hzT⟩
        have hzE : z ∉ E w := fun he => hzI (by
          rw [hIx w hwb]
          exact Finset.mem_insert.mpr (Or.inr he))
        exact Finset.mem_union.mpr (Or.inr (Finset.mem_biUnion.mpr
          ⟨w, hwL, Finset.mem_sdiff.mpr ⟨hzY, hzE⟩⟩))
  have hbase : (N b \ (J \ L)).card = (N b \ J).card + 3 := by
    have hsub : J \ L ⊆ N b := fun z hz => hJN (Finset.mem_sdiff.mp hz).1
    have hle := Finset.card_le_card hJN
    have hle' := Finset.card_le_card hL
    rw [Finset.card_sdiff_of_subset hsub, Finset.card_sdiff_of_subset hJN,
      Finset.card_sdiff_of_subset hL, hLc]
    omega
  have hsum : (∑ x ∈ L, (Y x \ E x).card) = ∑ x ∈ L, q x :=
    Finset.sum_congr rfl hcharge
  refine ⟨A, I, hAc, ?_, ?_, ?_, ?_⟩
  · change ((A.biUnion (fun w => N w \ I w)) \ A).card ≤ 22
    calc
      _ ≤ ((N b \ J) ∪ L.biUnion (fun x => Y x \ E x)).card := Finset.card_le_card hcover
      _ ≤ (N b \ J).card + (L.biUnion (fun x => Y x \ E x)).card := Finset.card_union_le _ _
      _ ≤ (N b \ J).card + (∑ x ∈ L, (Y x \ E x).card) := by
        apply Nat.add_le_add_left
        first | exact Finset.card_biUnion_le | exact Finset.card_biUnion_le _ _
      _ ≤ 22 := by rw [hsum]; omega
  · intro w hw z hz
    by_cases hwb : w = b
    · rw [hwb, hIb] at hz
      rw [hwb]
      exact tri b z (hJF z hz)
    · have hwL := leaf w hw hwb
      rw [hIx w hwb] at hz
      rcases Finset.mem_insert.mp hz with hzb | hzE
      · rw [hzb]
        exact tri w b (hLF w hwL)
      · have hzX := (hE w hwL).1 hzE
        exact tri w z (Finset.mem_filter.mp (Finset.mem_sdiff.mp hzX).1).2
  · intro w hw y hy z hz
    by_cases hwb : w = b
    · rw [hwb, hIb] at hy hz
      exact hJi y hy z hz
    · have hwL := leaf w hw hwb
      rw [hIx w hwb] at hy hz
      rcases Finset.mem_insert.mp hy with hyb | hyE
      · rcases Finset.mem_insert.mp hz with hzb | hzE
        · intro h
          rw [hyb, hzb] at h
          exact G.irrefl h
        · rw [hyb]
          exact hXout w z ((hE w hwL).1 hzE)
      · rcases Finset.mem_insert.mp hz with hzb | hzE
        · intro h
          rw [hzb] at h
          exact hXout w y ((hE w hwL).1 hyE) h.symm
        · exact (hE w hwL).2.1 y hyE z hzE
  · intro w hw z hz hadj
    by_cases hwb : w = b
    · have hzb : z ≠ b := fun he => hadj.ne (hwb.trans he.symm)
      rw [hwb, hIb]
      exact hL (leaf z hz hzb)
    · rw [hIx w hwb]
      by_cases hzb : z = b
      · exact Finset.mem_insert.mpr (Or.inl hzb)
      · exact (hJi w (hL (leaf w hw hwb)) z (hL (leaf z hz hzb)) hadj).elim

private theorem h12_no_star_weight_bound {n : ℕ} (G F : SimpleGraph (Fin n))
    (hFG : F ≤ G)
    (hd : ∀ v, (univ.filter (G.Adj v)).card ≤ 11)
    (hf : ∀ b x, F.Adj b x → 8 ≤ (univ.filter (F.Adj b)).card)
    (ht : ∀ b x, F.Adj b x →
      2 ≤ (univ.filter (fun z => F.Adj b z ∧ F.Adj x z)).card)
    (hnostar : let d (b x : Fin n) := (univ.filter (fun z => G.Adj b z ∧ G.Adj x z)).card
      let q (b x : Fin n) := (univ.filter (G.Adj x)).card - 1 - d b x -
        (if d b x ≤ 4 then 2 else if d b x ≤ 6 then 1 else 0)
      ¬ ∃ (b : Fin n) (J L : Finset (Fin n)),
        J ⊆ univ.filter (F.Adj b) ∧ L ⊆ J ∧ L.card = 3 ∧
        (∀ x ∈ J, ∀ y ∈ J, ¬ G.Adj x y) ∧
        1 + ((univ.filter (G.Adj b)) \ (J \ L)).card + (∑ x ∈ L, q b x) ≤ 26) :
    let N (x : Fin n) := univ.filter (G.Adj x)
    let d (b x : Fin n) := (univ.filter (fun z => G.Adj b z ∧ G.Adj x z)).card
    let r (b x : Fin n) : ℕ := if d b x ≤ 4 then 2 else if d b x ≤ 6 then 1 else 0
    let w (b x : Fin n) := (11 - (N x).card) + (d b x + r b x - 4)
    ∀ (b : Fin n) (J L : Finset (Fin n)),
      J ⊆ univ.filter (F.Adj b) → L ⊆ J → L.card = 3 →
      (∀ x ∈ J, ∀ y ∈ J, ¬ G.Adj x y) →
      J.card + (11 - (N b).card) + (∑ x ∈ L, w b x) ≤ 6 := by
  classical
  intro N d r w b J L hJ hL hLc hJi
  let q (v x : Fin n) := (N x).card - 1 - d v x - r v x
  have hJb : J ⊆ N b := by
    intro x hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hFG (Finset.mem_filter.mp (hJ hx)).2⟩
  have hterm (x : Fin n) (hx : x ∈ L) : q b x + w b x = 6 := by
    have hbx : F.Adj b x := (Finset.mem_filter.mp (hJ (hL hx))).2
    have hlow : 8 ≤ (N x).card := by
      have hsub : univ.filter (F.Adj x) ⊆ N x := by
        intro z hz
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hFG (Finset.mem_filter.mp hz).2⟩
      exact (hf x b hbx.symm).trans (Finset.card_le_card hsub)
    have hu : (N x).card ≤ 11 := hd x
    have hmin : 2 ≤ d b x := by
      have hsub : (univ.filter (fun z => F.Adj b z ∧ F.Adj x z)) ⊆
          univ.filter (fun z => G.Adj b z ∧ G.Adj x z) := by
        intro z hz
        obtain ⟨hbz, hxz⟩ := (Finset.mem_filter.mp hz).2
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hFG hbz, hFG hxz⟩
      exact (ht b x hbx).trans (Finset.card_le_card hsub)
    have hmax : d b x ≤ (N x).card - 1 := by
      have hbN : b ∈ N x := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hFG hbx.symm⟩
      have hsub : (univ.filter (fun z => G.Adj b z ∧ G.Adj x z)) ⊆ (N x).erase b := by
        intro z hz
        obtain ⟨hbz, hxz⟩ := (Finset.mem_filter.mp hz).2
        exact Finset.mem_erase.mpr ⟨hbz.ne.symm, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxz⟩⟩
      have hc := Finset.card_le_card hsub
      rw [Finset.card_erase_of_mem hbN] at hc
      exact hc
    have hrange : 4 ≤ d b x + r b x ∧ 1 + d b x + r b x ≤ (N x).card := by
      by_cases h4 : d b x ≤ 4
      · have hr : r b x = 2 := if_pos h4
        rw [hr]
        omega
      · by_cases h6 : d b x ≤ 6
        · have hr : r b x = 1 := (if_neg h4).trans (if_pos h6)
          rw [hr]
          omega
        · have hr : r b x = 0 := (if_neg h4).trans (if_neg h6)
          rw [hr]
          omega
    change ((N x).card - 1 - d b x - r b x) +
      ((11 - (N x).card) + (d b x + r b x - 4)) = 6
    obtain ⟨hrlo, hrhi⟩ := hrange
    omega
  have hs : (∑ x ∈ L, q b x) + (∑ x ∈ L, w b x) = 18 := by
    rw [← Finset.sum_add_distrib]
    calc
      _ = ∑ _x ∈ L, (6 : ℕ) := Finset.sum_congr rfl hterm
      _ = 18 := by simp [hLc]
  have hsub : J \ L ⊆ N b := fun x hx => hJb (Finset.mem_sdiff.mp hx).1
  have hbase : (N b \ (J \ L)).card = (N b).card - (J.card - 3) := by
    rw [Finset.card_sdiff_of_subset hsub, Finset.card_sdiff_of_subset hL, hLc]
  have hfail : ¬ (1 + (N b \ (J \ L)).card + (∑ x ∈ L, q b x) ≤ 26) := by
    intro hb
    apply hnostar
    exact ⟨b, J, L, hJ, hL, hLc, hJi, hb⟩
  rw [hbase] at hfail
  have hJle := Finset.card_le_card hJb
  have hLle := Finset.card_le_card hL
  have hble : (N b).card ≤ 11 := hd b
  omega

private theorem h12_weighted_three_count {α : Type*} [DecidableEq α]
    (J : Finset α) (w : α → ℕ) (P : α → Prop) [DecidablePred P]
    (hJ : 4 ≤ J.card) (hpos : ∀ x ∈ J, P x → 1 ≤ w x)
    (hbound : ∀ L : Finset α, L ⊆ J → L.card = 3 → J.card + (∑ x ∈ L, w x) ≤ 6) :
    J.card + (J.filter P).card ≤ 6 := by
  classical
  let B := J.filter P
  have hBJ : B ⊆ J := fun _ hx => (Finset.mem_filter.mp hx).1
  have hmass (T : Finset α) (hTB : T ⊆ B) : T.card ≤ ∑ x ∈ T, w x := by
    calc
      T.card = ∑ _x ∈ T, (1 : ℕ) := by simp
      _ ≤ ∑ x ∈ T, w x := Finset.sum_le_sum (fun x hx =>
        hpos x (hBJ (hTB hx)) (Finset.mem_filter.mp (hTB hx)).2)
  have hBsmall : B.card < 3 := by
    by_contra hn
    obtain ⟨T, hTB, hTc⟩ := Finset.exists_subset_card_eq (by omega : 3 ≤ B.card)
    have h₁ := hbound T (fun x hx => hBJ (hTB hx)) hTc
    have h₂ := hmass T hTB
    omega
  have hspace : 3 - B.card ≤ (J \ B).card := by
    rw [Finset.card_sdiff_of_subset hBJ]
    omega
  obtain ⟨R, hR, hRc⟩ := Finset.exists_subset_card_eq hspace
  have hdisj : Disjoint B R := Finset.disjoint_left.mpr (fun _ hb hr =>
    (Finset.mem_sdiff.mp (hR hr)).2 hb)
  have hsub : B ∪ R ⊆ J := by
    intro x hx
    exact (Finset.mem_union.mp hx).elim (fun hb => hBJ hb)
      (fun hr => (Finset.mem_sdiff.mp (hR hr)).1)
  have hc : (B ∪ R).card = 3 := by
    rw [Finset.card_union_of_disjoint hdisj, hRc]
    omega
  have hsum : (∑ x ∈ B, w x) ≤ ∑ x ∈ B ∪ R, w x := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro x hx
      exact Finset.mem_union.mpr (Or.inl hx)
    · intro x hx hnx
      exact Nat.zero_le _
  have h₁ := hbound (B ∪ R) hsub hc
  have h₂ := hmass B (fun _ hx => hx)
  change J.card + B.card ≤ 6
  omega

private theorem h12_link_discharge {n : ℕ} (F : SimpleGraph (Fin n))
    (ht : ∀ b u, F.Adj b u →
      2 ≤ (univ.filter (fun z => F.Adj b z ∧ F.Adj u z)).card)
    (hlocal : let C (b u : Fin n) := univ.filter (fun z => F.Adj b z ∧ F.Adj u z)
      ∀ b u, F.Adj b u → 4 ≤ (C b u).card →
        (C b u).card + ((C b u).filter (fun z => 3 ≤ (C b z).card)).card ≤ 6) :
    let U (b : Fin n) := univ.filter (F.Adj b)
    let C (b u : Fin n) := univ.filter (fun z => F.Adj b z ∧ F.Adj u z)
    ∀ b, (∑ u ∈ U b, (C b u).card) ≤ 3 * (U b).card ∧
      ((∑ u ∈ U b, (C b u).card) = 3 * (U b).card →
        ∀ u ∈ U b,
          ((C b u).card = 2 → ∀ z ∈ C b u, 4 ≤ (C b z).card) ∧
          (4 ≤ (C b u).card →
            ((C b u).filter (fun z => (C b z).card = 2)).card = 2 * ((C b u).card - 3))) := by
  classical
  intro U C b
  let V := U b
  let K (u : Fin n) := C b u
  let d (u : Fin n) := (K u).card
  let L := V.filter (fun u => d u = 2)
  let H := V.filter (fun u => 4 ≤ d u)
  let q (u : Fin n) := ((K u).filter (fun z => d z = 2)).card
  let r (u : Fin n) := ((K u).filter (fun z => 3 ≤ d z)).card
  let g (z : Fin n) := ((K z).filter (fun u => u ∈ H)).card
  have hmem (u z : Fin n) : z ∈ K u ↔ F.Adj b z ∧ F.Adj u z := by
    constructor
    · intro hz
      exact (Finset.mem_filter.mp hz).2
    · intro hz
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hz⟩
  have hV (u : Fin n) (hu : u ∈ V) : F.Adj b u :=
    (Finset.mem_filter.mp hu).2
  have hKV (u : Fin n) : K u ⊆ V := by
    intro z hz
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ((hmem u z).mp hz).1⟩
  have hdeg (u : Fin n) (hu : u ∈ V) : 2 ≤ d u := ht b u (hV u hu)
  have hL (u : Fin n) (hu : u ∈ L) : u ∈ V ∧ d u = 2 := Finset.mem_filter.mp hu
  have hH (u : Fin n) (hu : u ∈ H) : u ∈ V ∧ 4 ≤ d u := Finset.mem_filter.mp hu
  have hsym (u z : Fin n) (hu : u ∈ V) (hz : z ∈ V) :
      z ∈ K u ↔ u ∈ K z := by
    constructor
    · intro hzK
      exact (hmem z u).mpr ⟨hV u hu, ((hmem u z).mp hzK).2.symm⟩
    · intro huK
      exact (hmem u z).mpr ⟨hV z hz, ((hmem z u).mp huK).2.symm⟩
  have hpart (u : Fin n) : q u + r u = d u := by
    let A := (K u).filter (fun z => d z = 2)
    let B := (K u).filter (fun z => 3 ≤ d z)
    have hdisj : Disjoint A B := Finset.disjoint_left.mpr (by
      intro z ha hb
      have ha' : d z = 2 := (Finset.mem_filter.mp ha).2
      have hb' : 3 ≤ d z := (Finset.mem_filter.mp hb).2
      omega)
    have hAB : A ∪ B = K u := by
      ext z
      constructor
      · intro hz
        rcases Finset.mem_union.mp hz with ha | hb
        · exact (Finset.mem_filter.mp ha).1
        · exact (Finset.mem_filter.mp hb).1
      · intro hz
        have hz2 := hdeg z (hKV u hz)
        by_cases he : d z = 2
        · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨hz, he⟩))
        · have hz3 : 3 ≤ d z := by omega
          exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨hz, hz3⟩))
    change A.card + B.card = (K u).card
    rw [← Finset.card_union_of_disjoint hdisj, hAB]
  have hqlo (u : Fin n) (hu : u ∈ H) : 2 * (d u - 3) ≤ q u := by
    obtain ⟨huV, hu4⟩ := hH u hu
    have hloc : d u + r u ≤ 6 := hlocal b u (hV u huV) hu4
    have hp := hpart u
    omega
  have hgle (z : Fin n) (hz : z ∈ L) : g z ≤ 2 := by
    have hle := Finset.card_le_card (Finset.filter_subset (fun u => u ∈ H) (K z))
    change g z ≤ d z at hle
    rw [(hL z hz).2] at hle
    exact hle
  have hrow (u : Fin n) : q u = (∑ z ∈ L, (if z ∈ K u then (1 : ℕ) else 0)) := by
    have he : (K u).filter (fun z => d z = 2) = L.filter (fun z => z ∈ K u) := by
      ext z
      constructor
      · intro hz
        obtain ⟨hzK, hz2⟩ := Finset.mem_filter.mp hz
        exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hKV u hzK, hz2⟩, hzK⟩
      · intro hz
        obtain ⟨hzL, hzK⟩ := Finset.mem_filter.mp hz
        exact Finset.mem_filter.mpr ⟨hzK, (hL z hzL).2⟩
    rw [← Finset.sum_filter]
    change ((K u).filter (fun z => d z = 2)).card =
      (∑ _z ∈ L.filter (fun z => z ∈ K u), (1 : ℕ))
    rw [he]
    simp
  have hcol (z : Fin n) (hz : z ∈ L) :
      (∑ u ∈ H, (if z ∈ K u then (1 : ℕ) else 0)) = g z := by
    have he : H.filter (fun u => z ∈ K u) = (K z).filter (fun u => u ∈ H) := by
      ext u
      constructor
      · intro hu
        obtain ⟨huH, hzK⟩ := Finset.mem_filter.mp hu
        exact Finset.mem_filter.mpr
          ⟨(hsym u z (hH u huH).1 (hL z hz).1).mp hzK, huH⟩
      · intro hu
        obtain ⟨huK, huH⟩ := Finset.mem_filter.mp hu
        exact Finset.mem_filter.mpr
          ⟨huH, (hsym u z (hH u huH).1 (hL z hz).1).mpr huK⟩
    rw [← Finset.sum_filter, he]
    change (∑ _u ∈ (K z).filter (fun u => u ∈ H), (1 : ℕ)) =
      ((K z).filter (fun u => u ∈ H)).card
    simp
  have hinc : (∑ u ∈ H, q u) = (∑ z ∈ L, g z) := by
    calc
      _ = ∑ u ∈ H, ∑ z ∈ L, (if z ∈ K u then (1 : ℕ) else 0) :=
        Finset.sum_congr rfl (fun u _ => hrow u)
      _ = ∑ z ∈ L, ∑ u ∈ H, (if z ∈ K u then (1 : ℕ) else 0) := by
        rw [Finset.sum_comm]
      _ = _ := Finset.sum_congr rfl hcol
  have hpoint (u : Fin n) (hu : u ∈ V) :
      d u + (if d u = 2 then 1 else 0) = 3 + (if 4 ≤ d u then d u - 3 else 0) := by
    have hmin := hdeg u hu
    by_cases h2 : d u = 2 <;> by_cases h4 : 4 ≤ d u <;> simp [h2, h4] <;> omega
  have hleft : (∑ u ∈ V, (if d u = 2 then (1 : ℕ) else 0)) = L.card := by
    rw [← Finset.sum_filter]
    change (∑ _u ∈ L, (1 : ℕ)) = L.card
    simp
  have hright : (∑ u ∈ V, (if 4 ≤ d u then d u - 3 else 0)) =
      (∑ u ∈ H, (d u - 3)) := by
    rw [← Finset.sum_filter]
  have hthree : (∑ _u ∈ V, (3 : ℕ)) = 3 * V.card := by
    simp [Nat.mul_comm]
  have htwo : (∑ _z ∈ L, (2 : ℕ)) = 2 * L.card := by
    simp [Nat.mul_comm]
  have hbalance : (∑ u ∈ V, d u) + L.card = 3 * V.card + (∑ u ∈ H, (d u - 3)) := by
    calc
      _ = ∑ u ∈ V, (d u + (if d u = 2 then 1 else 0)) := by
        rw [Finset.sum_add_distrib, hleft]
      _ = ∑ u ∈ V, (3 + (if 4 ≤ d u then d u - 3 else 0)) :=
        Finset.sum_congr rfl hpoint
      _ = _ := by rw [Finset.sum_add_distrib, hthree, hright]
  have hlo : 2 * (∑ u ∈ H, (d u - 3)) ≤ (∑ u ∈ H, q u) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum hqlo
  have hhi : (∑ u ∈ H, q u) ≤ 2 * L.card := by
    rw [hinc, ← htwo]
    exact Finset.sum_le_sum hgle
  constructor
  · change (∑ u ∈ V, d u) ≤ 3 * V.card
    omega
  · intro heq
    change (∑ u ∈ V, d u) = 3 * V.card at heq
    have hsumL : (∑ z ∈ L, g z) = (∑ _z ∈ L, (2 : ℕ)) := by
      rw [← hinc, htwo]
      omega
    have hsumH : (∑ u ∈ H, (2 * (d u - 3))) = (∑ u ∈ H, q u) := by
      rw [← Finset.mul_sum]
      omega
    have hg_eq (z : Fin n) (hz : z ∈ L) : g z = 2 := by
      by_contra hn
      have hlt : g z < 2 := lt_of_le_of_ne (hgle z hz) hn
      have hs : (∑ u ∈ L, g u) < (∑ _u ∈ L, (2 : ℕ)) :=
        Finset.sum_lt_sum hgle ⟨z, hz, hlt⟩
      exact (ne_of_lt hs) hsumL
    have hq_eq (u : Fin n) (hu : u ∈ H) : 2 * (d u - 3) = q u := by
      by_contra hn
      have hlt : 2 * (d u - 3) < q u := lt_of_le_of_ne (hqlo u hu) hn
      have hs : (∑ v ∈ H, (2 * (d v - 3))) < (∑ v ∈ H, q v) :=
        Finset.sum_lt_sum hqlo ⟨u, hu, hlt⟩
      exact (ne_of_lt hs) hsumH
    intro u hu
    change u ∈ V at hu
    constructor
    · intro hu2 z hz
      change d u = 2 at hu2
      change z ∈ K u at hz
      change 4 ≤ d z
      have huL : u ∈ L := Finset.mem_filter.mpr ⟨hu, hu2⟩
      have hgu := hg_eq u huL
      by_contra hn
      have hzH : z ∉ H := fun hh => hn (hH z hh).2
      have hsub : (K u).filter (fun v => v ∈ H) ⊆ (K u).erase z := by
        intro v hv
        obtain ⟨hvK, hvH⟩ := Finset.mem_filter.mp hv
        exact Finset.mem_erase.mpr ⟨fun he => hzH (he ▸ hvH), hvK⟩
      have hle := Finset.card_le_card hsub
      rw [Finset.card_erase_of_mem hz] at hle
      change g u ≤ d u - 1 at hle
      omega
    · intro hu4
      change 4 ≤ d u at hu4
      change q u = 2 * (d u - 3)
      exact (hq_eq u (Finset.mem_filter.mpr ⟨hu, hu4⟩)).symm

private theorem h12_tight_edge_codegrees {n : ℕ} (G F : SimpleGraph (Fin n))
    (hG : G.CliqueFree 4) (hFG : F ≤ G)
    (ht : ∀ b x, F.Adj b x →
      2 ≤ (univ.filter (fun z => F.Adj b z ∧ F.Adj x z)).card)
    (hwbound : let N (x : Fin n) := univ.filter (G.Adj x)
      let d (b x : Fin n) := (univ.filter (fun z => G.Adj b z ∧ G.Adj x z)).card
      let r (b x : Fin n) : ℕ := if d b x ≤ 4 then 2 else if d b x ≤ 6 then 1 else 0
      let w (b x : Fin n) := (11 - (N x).card) + (d b x + r b x - 4)
      ∀ (b : Fin n) (J L : Finset (Fin n)),
        J ⊆ univ.filter (F.Adj b) → L ⊆ J → L.card = 3 →
        (∀ x ∈ J, ∀ y ∈ J, ¬ G.Adj x y) →
        J.card + (11 - (N b).card) + (∑ x ∈ L, w b x) ≤ 6)
    (htight : let U (b : Fin n) := univ.filter (F.Adj b)
      let C (b u : Fin n) := univ.filter (fun z => F.Adj b z ∧ F.Adj u z)
      ∀ b, (∑ u ∈ U b, (C b u).card) = 3 * (U b).card ∧
        ∀ u ∈ U b,
          ((C b u).card = 2 → ∀ z ∈ C b u, 4 ≤ (C b z).card) ∧
          (4 ≤ (C b u).card →
            ((C b u).filter (fun z => (C b z).card = 2)).card = 2 * ((C b u).card - 3))) :
    ∀ b u, F.Adj b u →
      (univ.filter (fun z => F.Adj b z ∧ F.Adj u z)).card = 3 ∧
      (univ.filter (fun z => G.Adj b z ∧ G.Adj u z)).card = 3 := by
  classical
  let N (x : Fin n) := univ.filter (G.Adj x)
  let U (x : Fin n) := univ.filter (F.Adj x)
  let C (b u : Fin n) := univ.filter (fun z => F.Adj b z ∧ F.Adj u z)
  let D (b u : Fin n) := univ.filter (fun z => G.Adj b z ∧ G.Adj u z)
  let d (b u : Fin n) := (D b u).card
  let r (b x : Fin n) : ℕ := if d b x ≤ 4 then 2 else if d b x ≤ 6 then 1 else 0
  let w (b x : Fin n) := (11 - (N x).card) + (d b x + r b x - 4)
  change ∀ b J L, J ⊆ U b → L ⊆ J → L.card = 3 →
    (∀ x ∈ J, ∀ y ∈ J, ¬ G.Adj x y) →
    J.card + (11 - (N b).card) + (∑ x ∈ L, w b x) ≤ 6 at hwbound
  have cm (b u z : Fin n) : z ∈ C b u ↔ F.Adj b z ∧ F.Adj u z := by
    simp [C]
  have um (b u : Fin n) : u ∈ U b ↔ F.Adj b u := by simp [U]
  have cs (b u : Fin n) : C b u = C u b := by
    ext z
    rw [cm, cm, and_comm]
  have csub (b u : Fin n) : C b u ⊆ U b := fun z hz =>
    (um b z).mpr ((cm b u z).mp hz).1
  have cle (b u : Fin n) : (C b u).card ≤ d b u := by
    apply Finset.card_le_card
    intro z hz
    obtain ⟨hbz, huz⟩ := (cm b u z).mp hz
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hFG hbz, hFG huz⟩
  have ind (b u : Fin n) (hbu : F.Adj b u) :
      ∀ x ∈ C b u, ∀ y ∈ C b u, ¬ G.Adj x y := by
    intro x hx y hy hxy
    obtain ⟨hbx, hux⟩ := (cm b u x).mp hx
    obtain ⟨hby, huy⟩ := (cm b u y).mp hy
    have e₁ := hFG hbu
    have e₂ := hFG hbx
    have e₃ := hFG hby
    have e₄ := hFG hux
    have e₅ := hFG huy
    have hbn : b ∉ ({u, x, y} : Finset (Fin n)) := by simp [e₁.ne, e₂.ne, e₃.ne]
    have hun : u ∉ ({x, y} : Finset (Fin n)) := by simp [e₄.ne, e₅.ne]
    have hxn : x ∉ ({y} : Finset (Fin n)) := by simp [hxy.ne]
    apply hG ({b, u, x, y} : Finset (Fin n))
    constructor
    · intro i hi j hj hij
      simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hi hj
      rcases hi with rfl | rfl | rfl | rfl <;>
        rcases hj with rfl | rfl | rfl | rfl <;>
        first | exact (hij rfl).elim | assumption | exact G.symm.symm _ _ (by assumption)
    · rw [Finset.card_insert_of_notMem hbn, Finset.card_insert_of_notMem hun,
        Finset.card_insert_of_notMem hxn]
      simp
  have wrange (b x : Fin n) : (3 ≤ d b x → 1 ≤ w b x) ∧
      (4 ≤ d b x → 2 ≤ w b x) := by
    change (3 ≤ d b x → 1 ≤ (11 - (N x).card) + (d b x + r b x - 4)) ∧
      (4 ≤ d b x → 2 ≤ (11 - (N x).card) + (d b x + r b x - 4))
    by_cases h4 : d b x ≤ 4
    · simp only [r, if_pos h4]
      constructor <;> intro h <;> omega
    · by_cases h6 : d b x ≤ 6
      · simp only [r, if_neg h4, if_pos h6]
        constructor <;> intro h <;> omega
      · simp only [r, if_neg h4, if_neg h6]
        constructor <;> intro h <;> omega
  have low_forces (b u z : Fin n) (huz : F.Adj u z)
      (hz2 : (C u z).card = 2) (hb : b ∈ C u z) : 4 ≤ (C b z).card := by
    have hz2' : (C z u).card = 2 := by rw [cs z u]; exact hz2
    have hb' : b ∈ C z u := by rw [cs z u]; exact hb
    rw [cs b z]
    exact ((htight z).2 u ((um z u).mpr huz.symm)).1 hz2' b hb'
  have nohigh (b u : Fin n) (hbu : F.Adj b u) : ¬ 4 ≤ (C b u).card := by
    intro hh
    have hh' : 4 ≤ (C u b).card := by rw [cs u b]; exact hh
    let S := (C u b).filter (fun z => (C u z).card = 2)
    have hSc : S.card = 2 * ((C u b).card - 3) :=
      ((htight u).2 b ((um u b).mpr hbu.symm)).2 hh'
    obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp (by omega : 1 < S.card)
    have large (z : Fin n) (hz : z ∈ S) : z ∈ C b u ∧ 2 ≤ w b z := by
      obtain ⟨hzC, hz2⟩ := Finset.mem_filter.mp hz
      obtain ⟨huz, hbz⟩ := (cm u b z).mp hzC
      have hz4 := low_forces b u z huz hz2 ((cm u z b).mpr ⟨hbu.symm, hbz.symm⟩)
      exact ⟨(cm b u z).mpr ⟨hbz, huz⟩, (wrange b z).2 (hz4.trans (cle b z))⟩
    obtain ⟨hxJ, hxw⟩ := large x hx
    obtain ⟨hyJ, hyw⟩ := large y hy
    let J := C b u
    let P : Finset (Fin n) := {x, y}
    have hPJ : P ⊆ J := by
      intro v hv
      simp only [P, Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl
      · exact hxJ
      · exact hyJ
    have hPc : P.card = 2 := Finset.card_pair hxy
    have hJ4 : 4 ≤ J.card := hh
    obtain ⟨t, ht'⟩ := Finset.card_pos.mp (show 0 < (J \ P).card by
      rw [Finset.card_sdiff_of_subset hPJ, hPc]
      omega)
    obtain ⟨htJ, htP⟩ := Finset.mem_sdiff.mp ht'
    have hLJ : insert t P ⊆ J := by
      intro v hv
      exact (Finset.mem_insert.mp hv).elim (fun h => h.symm ▸ htJ) (fun h => hPJ h)
    have hLc : (insert t P).card = 3 := by
      rw [Finset.card_insert_of_notMem htP, hPc]
    have hbd := hwbound b J (insert t P) (csub b u) hLJ hLc (ind b u hbu)
    have hpw : (∑ z ∈ P, w b z) = w b x + w b y := by
      simp [P, Finset.sum_insert, hxy]
    rw [Finset.sum_insert htP, hpw] at hbd
    omega
  have cubic (b u : Fin n) (hbu : F.Adj b u) : (C b u).card = 3 := by
    have hmin : 2 ≤ (C b u).card := ht b u hbu
    have hn := nohigh b u hbu
    by_contra hne
    have hc2 : (C b u).card = 2 := by omega
    obtain ⟨z, hz⟩ := Finset.card_pos.mp (show 0 < (C b u).card by omega)
    have hz4 := ((htight b).2 u ((um b u).mpr hbu)).1 hc2 z hz
    exact nohigh b z ((cm b u z).mp hz).1 hz4
  have weight_one (b v : Fin n) (hbv : F.Adj b v) (x : Fin n) (hx : x ∈ C b v) :
      w b x ≤ 1 := by
    let J := C b v
    have hj : J.card = 3 := cubic b v hbv
    have hlo (z : Fin n) (hz : z ∈ J) : 1 ≤ w b z := by
      have hz3 := cubic b z ((cm b v z).mp hz).1
      exact (wrange b z).1 ((le_of_eq hz3.symm).trans (cle b z))
    have hbd := hwbound b J J (csub b v) (fun _ hz => hz) hj (ind b v hbv)
    by_contra hn
    have hlt : 1 < w b x := by omega
    have hs : (∑ _z ∈ J, (1 : ℕ)) < ∑ z ∈ J, w b z :=
      Finset.sum_lt_sum hlo ⟨x, hx, hlt⟩
    simp [hj] at hs
    omega
  intro b u hbu
  have hu3 := cubic b u hbu
  refine ⟨hu3, ?_⟩
  obtain ⟨v, hv⟩ := Finset.card_pos.mp (show 0 < (C b u).card by omega)
  obtain ⟨hbv, huv⟩ := (cm b u v).mp hv
  have hwu := weight_one b v hbv u ((cm b v u).mpr ⟨hbu, huv.symm⟩)
  have hlo := cle b u
  change d b u = 3
  by_contra hn
  have hh : 4 ≤ d b u := by omega
  have hw := (wrange b u).2 hh
  omega

private theorem h12_square_in_cubic_link {n : ℕ} (G F : SimpleGraph (Fin n))
    (hG : G.CliqueFree 4) (hFG : F ≤ G)
    (hf : ∀ b x, F.Adj b x → 8 ≤ (univ.filter (F.Adj b)).card)
    (p : Fin n) (hp : ∃ x, F.Adj p x)
    (hwbound : let N (x : Fin n) := univ.filter (G.Adj x)
      let d (b x : Fin n) := (univ.filter (fun z => G.Adj b z ∧ G.Adj x z)).card
      let r (b x : Fin n) : ℕ := if d b x ≤ 4 then 2 else if d b x ≤ 6 then 1 else 0
      let w (b x : Fin n) := (11 - (N x).card) + (d b x + r b x - 4)
      ∀ (b : Fin n) (J L : Finset (Fin n)),
        J ⊆ univ.filter (F.Adj b) → L ⊆ J → L.card = 3 →
        (∀ x ∈ J, ∀ y ∈ J, ¬ G.Adj x y) →
        J.card + (11 - (N b).card) + (∑ x ∈ L, w b x) ≤ 6)
    (hcodes : ∀ b u, F.Adj b u →
      (univ.filter (fun z => F.Adj b z ∧ F.Adj u z)).card = 3 ∧
      (univ.filter (fun z => G.Adj b z ∧ G.Adj u z)).card = 3) :
    ∃ a b c e : Fin n, F.Adj p a ∧ F.Adj p b ∧ F.Adj p c ∧ F.Adj p e ∧
      F.Adj a b ∧ F.Adj b c ∧ F.Adj c e ∧ F.Adj e a ∧ a ≠ c ∧ b ≠ e := by
  let U := univ.filter (F.Adj p)
  let K (x : Fin n) := univ.filter (fun z => F.Adj p z ∧ F.Adj x z)
  have um (x : Fin n) : x ∈ U ↔ F.Adj p x := by simp [U]
  have km (x z : Fin n) : z ∈ K x ↔ F.Adj p z ∧ F.Adj x z := by simp [K]
  have ksub (x : Fin n) : K x ⊆ U := fun z hz => (um z).mpr ((km x z).mp hz).1
  have kcard (x : Fin n) (hx : x ∈ U) : (K x).card = 3 :=
    (hcodes p x ((um x).mp hx)).1
  have h8 : 8 ≤ U.card := by
    obtain ⟨x, hx⟩ := hp
    exact hf p x hx
  have hsub : U ⊆ univ.filter (G.Adj p) := fun x hx =>
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hFG ((um x).mp hx)⟩
  have halpha (J : Finset (Fin n)) (hJ : J ⊆ U)
      (hind : ∀ x ∈ J, ∀ y ∈ J, ¬ G.Adj x y) : J.card ≤ 3 := by
    by_contra hn
    obtain ⟨L, hL, hLc⟩ := Finset.exists_subset_card_eq (by omega : 3 ≤ J.card)
    let N (x : Fin n) := univ.filter (G.Adj x)
    let d (b x : Fin n) := (univ.filter (fun z => G.Adj b z ∧ G.Adj x z)).card
    let r (b x : Fin n) : ℕ :=
      if d b x ≤ 4 then 2 else if d b x ≤ 6 then 1 else 0
    let w (b x : Fin n) := (11 - (N x).card) + (d b x + r b x - 4)
    have hbd := hwbound p J L hJ hL hLc hind
    change J.card + (11 - (N p).card) + (∑ x ∈ L, w p x) ≤ 6 at hbd
    have hwt (x : Fin n) (hx : x ∈ L) : 1 ≤ w p x := by
      have hx3 : d p x = 3 := (hcodes p x ((um x).mp (hJ (hL hx)))).2
      change 1 ≤ (11 - (N x).card) + (d p x + r p x - 4)
      simp [r, hx3]
    have hsum : (∑ _x ∈ L, (1 : ℕ)) ≤ ∑ x ∈ L, w p x := Finset.sum_le_sum hwt
    simp [hLc] at hsum
    omega
  have hUc : U.card = 8 := (r34_and_triple_in_8 G hG p U hsub h8 halpha).1
  have noTri (x y z : Fin n) (hx : x ∈ U) (hy : y ∈ U) (hz : z ∈ U)
      (hxy : F.Adj x y) (hxz : F.Adj x z) (hyz : F.Adj y z) : False := by
    have hpx : G.Adj p x := hFG ((um x).mp hx)
    have hpy : G.Adj p y := hFG ((um y).mp hy)
    have hpz : G.Adj p z := hFG ((um z).mp hz)
    have hxy' : G.Adj x y := hFG hxy
    have hxz' : G.Adj x z := hFG hxz
    have hyz' : G.Adj y z := hFG hyz
    have hpN : p ∉ ({x, y, z} : Finset (Fin n)) := by
      simp [hpx.ne, hpy.ne, hpz.ne]
    have hxN : x ∉ ({y, z} : Finset (Fin n)) := by
      simp [hxy'.ne, hxz'.ne]
    have hyN : y ∉ ({z} : Finset (Fin n)) := by
      simp [hyz'.ne]
    apply hG ({p, x, y, z} : Finset (Fin n))
    constructor
    · intro i hi j hj hij
      simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hi hj
      rcases hi with rfl | rfl | rfl | rfl <;>
        rcases hj with rfl | rfl | rfl | rfl <;>
        first | exact (hij rfl).elim | assumption | exact G.symm.symm _ _ (by assumption)
    · rw [Finset.card_insert_of_notMem hpN, Finset.card_insert_of_notMem hxN,
        Finset.card_insert_of_notMem hyN]
      simp
  obtain ⟨a, ha⟩ := Finset.card_pos.mp (by omega : 0 < U.card)
  let M (y : Fin n) := (K y).erase a
  let W := U \ insert a (K a)
  have hKaNot : a ∉ K a := by
    intro h
    exact F.irrefl ((km a a).mp h).2
  have hInsSub : insert a (K a) ⊆ U := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact ha
    · exact ksub a hx
  have hWcard : W.card = 4 := by
    dsimp [W]
    rw [Finset.card_sdiff_of_subset hInsSub,
      Finset.card_insert_of_notMem hKaNot, kcard a ha, hUc]
  have hMcard (y : Fin n) (hy : y ∈ K a) : (M y).card = 2 := by
    have hyU : y ∈ U := ksub a hy
    have hay : a ∈ K y := by
      apply (km y a).mpr
      exact ⟨(um a).mp ha, ((km a y).mp hy).2.symm⟩
    change ((K y).erase a).card = 2
    rw [Finset.card_erase_of_mem hay, kcard y hyU]
  have hMsub (y : Fin n) (hy : y ∈ K a) : M y ⊆ W := by
    intro t ht
    change t ∈ (K y).erase a at ht
    obtain ⟨hta, htKy⟩ := Finset.mem_erase.mp ht
    have htU : t ∈ U := ksub y htKy
    have hnot : t ∉ K a := by
      intro htKa
      have hay : F.Adj a y := ((km a y).mp hy).2
      have hat : F.Adj a t := ((km a t).mp htKa).2
      have hyt : F.Adj y t := ((km y t).mp htKy).2
      exact noTri a y t ha (ksub a hy) htU hay hat hyt
    exact Finset.mem_sdiff.mpr
      ⟨htU, fun htIns => by
        rcases Finset.mem_insert.mp htIns with hta' | htKa'
        · exact hta hta'
        · exact hnot htKa'⟩
  by_contra hnsq
  let V := (K a).biUnion M
  have hdisj (y : Fin n) (hy : y ∈ K a) (z : Fin n) (hz : z ∈ K a)
      (hyz : y ≠ z) : Disjoint (M y) (M z) := by
    apply Finset.disjoint_left.mpr
    intro t hty htz
    change t ∈ (K y).erase a at hty
    change t ∈ (K z).erase a at htz
    obtain ⟨hta, htKy⟩ := Finset.mem_erase.mp hty
    obtain ⟨_, htKz⟩ := Finset.mem_erase.mp htz
    have hpa : F.Adj p a := (um a).mp ha
    have hpy : F.Adj p y := ((km a y).mp hy).1
    have hpt : F.Adj p t := ((km y t).mp htKy).1
    have hpz : F.Adj p z := ((km a z).mp hz).1
    have hay : F.Adj a y := ((km a y).mp hy).2
    have hyt : F.Adj y t := ((km y t).mp htKy).2
    have htz' : F.Adj t z := ((km z t).mp htKz).2.symm
    have haz : F.Adj a z := ((km a z).mp hz).2
    exact hnsq ⟨a, y, t, z, hpa, hpy, hpt, hpz, hay, hyt, htz',
      haz.symm, hta.symm, hyz⟩
  have hbi : V.card = ∑ y ∈ K a, (M y).card := by
    dsimp [V]
    apply Finset.card_biUnion
    intro y hy z hz hyz
    exact hdisj y hy z hz hyz
  have sumConst (S : Finset (Fin n)) (j : ℕ) :
      Finset.sum S (fun _ => j) = S.card * j := by
    induction S using Finset.induction_on with
    | empty => simp
    | @insert x T hx ih =>
      rw [Finset.sum_insert hx, Finset.card_insert_of_notMem hx, ih,
        Nat.add_mul, Nat.one_mul]
      omega
  have hsum : ∑ y ∈ K a, (M y).card = 6 := by
    calc
      _ = ∑ y ∈ K a, (2 : ℕ) :=
        Finset.sum_congr rfl (fun y hy => hMcard y hy)
      _ = (K a).card * 2 := sumConst (K a) 2
      _ = 6 := by rw [kcard a ha]
  have hsubW : V ⊆ W := by
    intro t ht
    obtain ⟨y, hy, hty⟩ := Finset.mem_biUnion.mp ht
    exact hMsub y hy hty
  have hle := Finset.card_le_card hsubW
  rw [hbi, hsum, hWcard] at hle
  omega

private theorem h12_square_deletion {n : ℕ} (G F : SimpleGraph (Fin n))
    (hG : G.CliqueFree 4) (hFG : F ≤ G)
    (hd : ∀ v, (univ.filter (G.Adj v)).card ≤ 11)
    (hf : ∀ b x, F.Adj b x → 8 ≤ (univ.filter (F.Adj b)).card)
    (hwbound : let N (x : Fin n) := univ.filter (G.Adj x)
      let d (b x : Fin n) := (univ.filter (fun z => G.Adj b z ∧ G.Adj x z)).card
      let r (b x : Fin n) : ℕ := if d b x ≤ 4 then 2 else if d b x ≤ 6 then 1 else 0
      let w (b x : Fin n) := (11 - (N x).card) + (d b x + r b x - 4)
      ∀ (b : Fin n) (J L : Finset (Fin n)),
        J ⊆ univ.filter (F.Adj b) → L ⊆ J → L.card = 3 →
        (∀ x ∈ J, ∀ y ∈ J, ¬ G.Adj x y) →
        J.card + (11 - (N b).card) + (∑ x ∈ L, w b x) ≤ 6)
    (hcodes : ∀ b u, F.Adj b u →
      (univ.filter (fun z => F.Adj b z ∧ F.Adj u z)).card = 3 ∧
      (univ.filter (fun z => G.Adj b z ∧ G.Adj u z)).card = 3)
    (p a b c e : Fin n)
    (ha : F.Adj p a) (hb : F.Adj p b) (hc : F.Adj p c) (he : F.Adj p e)
    (hab : F.Adj a b) (hbc : F.Adj b c) (hce : F.Adj c e) (hea : F.Adj e a)
    (hac : a ≠ c) (hbe : b ≠ e) :
    ∃ (A : Finset (Fin n)) (I : Fin n → Finset (Fin n)),
      A.card = 4 ∧
      ((A.biUnion (fun w => (univ.filter (G.Adj w)) \ I w)) \ A).card ≤ 22 ∧
      (∀ w ∈ A, ∀ x ∈ I w, G.Adj w x ∧ ∃ z, G.Adj w z ∧ G.Adj x z) ∧
      (∀ w ∈ A, ∀ x ∈ I w, ∀ y ∈ I w, ¬ G.Adj x y) ∧
      (∀ w ∈ A, ∀ x ∈ A, G.Adj w x → x ∈ I w) := by
  classical
  let N (x : Fin n) := univ.filter (G.Adj x)
  let U (x : Fin n) := univ.filter (F.Adj x)
  let CF (x y : Fin n) := univ.filter (fun z => F.Adj x z ∧ F.Adj y z)
  let CG (x y : Fin n) := univ.filter (fun z => G.Adj x z ∧ G.Adj y z)
  have hnoK4 : ∀ w x y z : Fin n,
      G.Adj w x → G.Adj w y → G.Adj w z → G.Adj x y → G.Adj x z → ¬ G.Adj y z := by
    intro w x y z hwx hwy hwz hxy hxz hyz
    have h4 : G.IsNClique 4 ({w, x, y, z} : Finset (Fin n)) := by
      refine ⟨?_, ?_⟩
      · intro u hu v hv huv
        simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hu hv
        rcases hu with rfl | rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl | rfl
        all_goals first | exact (huv rfl).elim | exact hwx | exact hwx.symm | exact hwy | exact hwy.symm | exact hwz | exact hwz.symm | exact hxy | exact hxy.symm | exact hxz | exact hxz.symm | exact hyz | exact hyz.symm
      · rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
            Finset.card_insert_of_notMem, Finset.card_singleton]
        · simp [hyz.ne]
        · simp [hxy.ne, hxz.ne]
        · simp [hwx.ne, hwy.ne, hwz.ne]
    exact hG ({w, x, y, z} : Finset (Fin n)) h4
  have hCF_eq_CG : ∀ x y, F.Adj x y → CF x y = CG x y := by
    intro x y hxy
    apply Finset.eq_of_subset_of_card_le
    · intro z hz
      obtain ⟨hxz, hyz⟩ := (Finset.mem_filter.mp hz).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hFG hxz, hFG hyz⟩
    · rw [(hcodes x y hxy).1, (hcodes x y hxy).2]
  have halpha3 : ∀ v, ∀ J : Finset (Fin n),
      J ⊆ U v → (∀ x ∈ J, ∀ y ∈ J, ¬ G.Adj x y) → J.card ≤ 3 := by
    intro v J hJU hJind
    by_contra hgt
    have h4 : 4 ≤ J.card := by omega
    obtain ⟨L, hLJ, hLc⟩ := Finset.exists_subset_card_eq (show 3 ≤ J.card by omega)
    have hwb := hwbound v J L hJU hLJ hLc hJind
    dsimp only at hwb
    have hsum : 3 ≤ ∑ x ∈ L, ((11 - (N x).card) + ((CG v x).card +
        (if (CG v x).card ≤ 4 then 2 else if (CG v x).card ≤ 6 then 1 else 0) - 4)) := by
      calc 3 = ∑ _x ∈ L, (1 : ℕ) := by simp [hLc]
        _ ≤ _ := Finset.sum_le_sum fun x hx => by
            have hvx : F.Adj v x := (Finset.mem_filter.mp (hJU (hLJ hx))).2
            have hcg : (CG v x).card = 3 := (hcodes v x hvx).2
            simp [hcg]
    dsimp only [N, CG] at hsum
    omega
  have hU_card8 : ∀ v x, F.Adj v x → (U v).card = 8 := by
    intro v x hvx
    exact (r34_and_triple_in_8 G hG v (U v)
      (fun u hu => Finset.mem_filter.mpr ⟨Finset.mem_univ _, hFG (Finset.mem_filter.mp hu).2⟩)
      (hf v x hvx) (fun J hJ hJind => halpha3 v J hJ hJind)).1
  have htriple : ∀ v x y, F.Adj v x → F.Adj v y → x ≠ y → ¬ G.Adj x y →
      ∃ z ∈ U v, z ≠ x ∧ z ≠ y ∧ ¬ G.Adj x z ∧ ¬ G.Adj y z := by
    intro v x y hvx hvy hxy hna
    have h8 : (U v).card = 8 := hU_card8 v x hvx
    have hcx : (CF v x).card = 3 := (hcodes v x hvx).1
    have hcy : (CF v y).card = 3 := (hcodes v y hvy).1
    have hne_inter : (CF v x ∩ CF v y).Nonempty := by
      by_contra hempty
      rw [Finset.not_nonempty_iff_eq_empty] at hempty
      let J := insert x (CF v y)
      have hxnot : x ∉ CF v y := by
        intro hx
        exact hna (hFG (Finset.mem_filter.mp hx).2.2).symm
      have hJU : J ⊆ U v := by
        intro t ht
        rcases Finset.mem_insert.mp ht with rfl | ht
        · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hvx⟩
        · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp ht).2.1⟩
      have hJind : ∀ u ∈ J, ∀ w ∈ J, ¬ G.Adj u w := by
        intro u hu w hw huw
        rcases Finset.mem_insert.mp hu with hu' | hu <;>
        rcases Finset.mem_insert.mp hw with hw' | hw
        · rw [hu', hw'] at huw; exact G.irrefl huw
        · rw [hu'] at huw
          have hw' := Finset.mem_filter.mp hw
          have hmem_cg : w ∈ CG v x := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hFG hw'.2.1, huw⟩
          rw [← hCF_eq_CG v x hvx] at hmem_cg
          have : w ∈ CF v x ∩ CF v y := Finset.mem_inter.mpr ⟨hmem_cg, hw⟩
          rw [hempty] at this; exact Finset.notMem_empty _ this
        · rw [hw'] at huw
          have hu' := Finset.mem_filter.mp hu
          have hmem_cg : u ∈ CG v x := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hFG hu'.2.1, huw.symm⟩
          rw [← hCF_eq_CG v x hvx] at hmem_cg
          have : u ∈ CF v x ∩ CF v y := Finset.mem_inter.mpr ⟨hmem_cg, hu⟩
          rw [hempty] at this; exact Finset.notMem_empty _ this
        · have hu' := (Finset.mem_filter.mp hu).2
          have hw' := (Finset.mem_filter.mp hw).2
          exact hnoK4 v y u w (hFG hvy) (hFG hu'.1) (hFG hw'.1) (hFG hu'.2) (hFG hw'.2) huw
      have hJc : J.card = 4 := by rw [Finset.card_insert_of_notMem hxnot, hcy]
      have hle3 := halpha3 v J hJU hJind
      omega
    have hunion : (CF v x ∪ CF v y).card ≤ 5 := by
      have hi : 1 ≤ (CF v x ∩ CF v y).card := Finset.card_pos.mpr hne_inter
      have hu := Finset.card_union_add_card_inter (CF v x) (CF v y)
      omega
    let Bad := insert x (insert y (CF v x ∪ CF v y))
    have hBad : Bad.card ≤ 7 := by
      have h1 : Bad.card ≤ (insert y (CF v x ∪ CF v y)).card + 1 := Finset.card_insert_le _ _
      have h2 : (insert y (CF v x ∪ CF v y)).card ≤ (CF v x ∪ CF v y).card + 1 := Finset.card_insert_le _ _
      omega
    have hpos : 0 < (U v \ Bad).card := by
      have hsub := Finset.card_sdiff_add_card_inter (U v) Bad
      have hint : (U v ∩ Bad).card ≤ Bad.card := Finset.card_le_card Finset.inter_subset_right
      omega
    obtain ⟨z, hz⟩ := Finset.card_pos.mp hpos
    obtain ⟨hzU, hzBad⟩ := Finset.mem_sdiff.mp hz
    have hzx : z ≠ x := fun h => hzBad (Finset.mem_insert.mpr (Or.inl h))
    have hzy : z ≠ y := fun h => hzBad (Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inl h))))
    have hnxz : ¬ G.Adj x z := by
      intro hxz
      have hmem : z ∈ CG v x := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hFG (Finset.mem_filter.mp hzU).2, hxz⟩
      rw [← hCF_eq_CG v x hvx] at hmem
      exact hzBad (Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inr (Finset.mem_union.mpr (Or.inl hmem))))))
    have hnyz : ¬ G.Adj y z := by
      intro hyz
      have hmem : z ∈ CG v y := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hFG (Finset.mem_filter.mp hzU).2, hyz⟩
      rw [← hCF_eq_CG v y hvy] at hmem
      exact hzBad (Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inr (Finset.mem_union.mpr (Or.inr hmem))))))
    exact ⟨z, hzU, hzx, hzy, hnxz, hnyz⟩
  have hnac : ¬ G.Adj a c := fun h => hnoK4 p a b c (hFG ha) (hFG hb) (hFG hc) (hFG hab) h (hFG hbc)
  have hnbe : ¬ G.Adj b e := fun h => hnoK4 p a b e (hFG ha) (hFG hb) (hFG he) (hFG hab) (hFG hea.symm) h
  obtain ⟨za, hzaU, hzab, hzae, hnab_z, hnae_z⟩ := htriple a b e hab hea.symm hbe hnbe
  obtain ⟨zb, hzbU, hzba, hzbc, hnba_z, hnbc_z⟩ := htriple b a c hab.symm hbc hac hnac
  obtain ⟨zc, hzcU, hzcb, hzce, hncb_z, hnce_z⟩ := htriple c b e hbc.symm hce hbe hnbe
  obtain ⟨ze, hzeU, hzea, hzec, hnea_z, hnec_z⟩ := htriple e a c hea hce.symm hac hnac
  let A : Finset (Fin n) := {a, b, c, e}
  have hab_ne : a ≠ b := hab.ne
  have hbc_ne : b ≠ c := hbc.ne
  have hce_ne : c ≠ e := hce.ne
  have hea_ne : e ≠ a := hea.ne
  have hAc : A.card = 4 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
        Finset.card_insert_of_notMem, Finset.card_singleton]
    · simp [hce_ne]
    · simp [hbc_ne, hbe]
    · simp [hab_ne, hac, hea_ne.symm]
  let I : Fin n → Finset (Fin n) := fun w =>
    if w = a then {b, e, za}
    else if w = b then {a, c, zb}
    else if w = c then {b, e, zc}
    else if w = e then {a, c, ze}
    else ∅
  have hIa : I a = {b, e, za} := by simp [I]
  have hIb : I b = {a, c, zb} := by simp [I, hab_ne.symm]
  have hIc : I c = {b, e, zc} := by simp [I, hac.symm, hbc_ne.symm]
  have hIe : I e = {a, c, ze} := by simp [I, hea_ne, hbe.symm, hce_ne.symm]
  have hIa_c : (I a).card = 3 := by
    rw [hIa, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
    · simp [hzae.symm]
    · simp [hbe, hzab.symm]
  have hIb_c : (I b).card = 3 := by
    rw [hIb, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
    · simp [hzbc.symm]
    · simp [hac, hzba.symm]
  have hIc_c : (I c).card = 3 := by
    rw [hIc, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
    · simp [hzce.symm]
    · simp [hbe, hzcb.symm]
  have hIe_c : (I e).card = 3 := by
    rw [hIe, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
    · simp [hzec.symm]
    · simp [hac, hzea.symm]
  have hP : ∀ w ∈ A, ∀ x ∈ I w, G.Adj w x ∧ ∃ z, G.Adj w z ∧ G.Adj x z := by
    intro w hw x hx
    have htri (u v : Fin n) (huv : F.Adj u v) : G.Adj u v ∧ ∃ z, G.Adj u z ∧ G.Adj v z := by
      refine ⟨hFG huv, ?_⟩
      have hpos : 0 < (CF u v).card := by rw [(hcodes u v huv).1]; omega
      obtain ⟨z, hz⟩ := Finset.card_pos.mp hpos
      exact ⟨z, hFG (Finset.mem_filter.mp hz).2.1, hFG (Finset.mem_filter.mp hz).2.2⟩
    simp only [A, Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with hw | hw | hw | hw
    · rw [hw] at hx ⊢; rw [hIa] at hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with hx | hx | hx <;> rw [hx]
      · exact htri a b hab
      · exact htri a e hea.symm
      · exact htri a za (Finset.mem_filter.mp hzaU).2
    · rw [hw] at hx ⊢; rw [hIb] at hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with hx | hx | hx <;> rw [hx]
      · exact htri b a hab.symm
      · exact htri b c hbc
      · exact htri b zb (Finset.mem_filter.mp hzbU).2
    · rw [hw] at hx ⊢; rw [hIc] at hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with hx | hx | hx <;> rw [hx]
      · exact htri c b hbc.symm
      · exact htri c e hce
      · exact htri c zc (Finset.mem_filter.mp hzcU).2
    · rw [hw] at hx ⊢; rw [hIe] at hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with hx | hx | hx <;> rw [hx]
      · exact htri e a hea
      · exact htri e c hce.symm
      · exact htri e ze (Finset.mem_filter.mp hzeU).2
  have hind : ∀ w ∈ A, ∀ x ∈ I w, ∀ y ∈ I w, ¬ G.Adj x y := by
    intro w hw x hx y hy hxy
    simp only [A, Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with hw | hw | hw | hw
    · rw [hw, hIa] at hx hy; simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
      rcases hx with hx | hx | hx <;> rcases hy with hy | hy | hy <;> rw [hx, hy] at hxy
      all_goals first | exact G.irrefl hxy | exact hnbe hxy | exact hnbe hxy.symm | exact hnab_z hxy | exact hnab_z hxy.symm | exact hnae_z hxy | exact hnae_z hxy.symm
    · rw [hw, hIb] at hx hy; simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
      rcases hx with hx | hx | hx <;> rcases hy with hy | hy | hy <;> rw [hx, hy] at hxy
      all_goals first | exact G.irrefl hxy | exact hnac hxy | exact hnac hxy.symm | exact hnba_z hxy | exact hnba_z hxy.symm | exact hnbc_z hxy | exact hnbc_z hxy.symm
    · rw [hw, hIc] at hx hy; simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
      rcases hx with hx | hx | hx <;> rcases hy with hy | hy | hy <;> rw [hx, hy] at hxy
      all_goals first | exact G.irrefl hxy | exact hnbe hxy | exact hnbe hxy.symm | exact hncb_z hxy | exact hncb_z hxy.symm | exact hnce_z hxy | exact hnce_z hxy.symm
    · rw [hw, hIe] at hx hy; simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
      rcases hx with hx | hx | hx <;> rcases hy with hy | hy | hy <;> rw [hx, hy] at hxy
      all_goals first | exact G.irrefl hxy | exact hnac hxy | exact hnac hxy.symm | exact hnea_z hxy | exact hnea_z hxy.symm | exact hnec_z hxy | exact hnec_z hxy.symm
  have hself : ∀ w ∈ A, ∀ x ∈ A, G.Adj w x → x ∈ I w := by
    intro w hw x hx hwx
    simp only [A, Finset.mem_insert, Finset.mem_singleton] at hw hx
    rcases hw with hw | hw | hw | hw <;> rcases hx with hx | hx | hx | hx <;> rw [hw, hx] at hwx ⊢
    all_goals first | exact (G.irrefl hwx).elim | exact (hnac hwx).elim | exact (hnac hwx.symm).elim | exact (hnbe hwx).elim | exact (hnbe hwx.symm).elim | simp [hIa, hIb, hIc, hIe]
  let S (w : Fin n) := (N w) \ I w
  have hSc : ∀ w ∈ A, (S w).card ≤ 8 := by
    intro w hw
    have hsub : I w ⊆ N w := fun x hx => Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hP w hw x hx).1⟩
    have hsd := Finset.card_sdiff_of_subset hsub
    have hdw := hd w
    have hIc3 : (I w).card = 3 := by
      simp only [A, Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with hw | hw | hw | hw <;> rw [hw]
      · exact hIa_c
      · exact hIb_c
      · exact hIc_c
      · exact hIe_c
    change ((N w) \ I w).card ≤ 8
    dsimp only [N] at hsd ⊢
    omega
  have hCF_sub : ∀ x ∈ A, ∀ y ∈ A, F.Adj x y → CF x y ⊆ S x ∩ S y := by
    intro x hx y hy hxy z hz
    obtain ⟨hxz, hyz⟩ := (Finset.mem_filter.mp hz).2
    refine Finset.mem_inter.mpr ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hFG hxz⟩, ?_⟩,
      Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hFG hyz⟩, ?_⟩⟩
    · intro hzx
      exact hind x hx z hzx y (hself x hx y hy (hFG hxy)) (hFG hyz.symm)
    · intro hzy
      exact hind y hy z hzy x (hself y hy x hx (hFG hxy.symm)) (hFG hxz.symm)
  let M := S a ∩ S b ∩ S c ∩ S e
  have hM_le2 : M.card ≤ 2 := by
    by_contra hgt
    have hge3 : 3 ≤ M.card := by omega
    have hM_ab : M ⊆ CF a b := by
      intro z hz
      have hza : z ∈ S a := (Finset.mem_inter.mp (Finset.mem_inter.mp (Finset.mem_inter.mp hz).1).1).1
      have hzb : z ∈ S b := (Finset.mem_inter.mp (Finset.mem_inter.mp (Finset.mem_inter.mp hz).1).1).2
      have hmem : z ∈ CG a b := Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        (Finset.mem_filter.mp (Finset.mem_sdiff.mp hza).1).2,
        (Finset.mem_filter.mp (Finset.mem_sdiff.mp hzb).1).2⟩
      rwa [← hCF_eq_CG a b hab] at hmem
    have hM_ae : M ⊆ CF a e := by
      intro z hz
      have hza : z ∈ S a := (Finset.mem_inter.mp (Finset.mem_inter.mp (Finset.mem_inter.mp hz).1).1).1
      have hze : z ∈ S e := (Finset.mem_inter.mp hz).2
      have hmem : z ∈ CG a e := Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        (Finset.mem_filter.mp (Finset.mem_sdiff.mp hza).1).2,
        (Finset.mem_filter.mp (Finset.mem_sdiff.mp hze).1).2⟩
      rwa [← hCF_eq_CG a e hea.symm] at hmem
    have hM_eq_ab : M = CF a b := Finset.eq_of_subset_of_card_le hM_ab (by rw [(hcodes a b hab).1]; omega)
    have hM_eq_ae : M = CF a e := Finset.eq_of_subset_of_card_le hM_ae (by rw [(hcodes a e hea.symm).1]; omega)
    have hMc : M.card = 3 := by rw [hM_eq_ab, (hcodes a b hab).1]
    let R := (U a) \ (insert b (insert e M))
    have hRc : 3 ≤ R.card := by
      have h8 : (U a).card = 8 := hU_card8 a b hab
      have h1 : (insert b (insert e M)).card ≤ (insert e M).card + 1 := Finset.card_insert_le _ _
      have h2 : (insert e M).card ≤ M.card + 1 := Finset.card_insert_le _ _
      have hsd := Finset.card_sdiff_add_card_inter (U a) (insert b (insert e M))
      change R.card + (U a ∩ insert b (insert e M)).card = (U a).card at hsd
      have hint : (U a ∩ insert b (insert e M)).card ≤ (insert b (insert e M)).card :=
        Finset.card_le_card Finset.inter_subset_right
      omega
    obtain ⟨T, hTR, hTc⟩ := Finset.exists_subset_card_eq hRc
    obtain ⟨x, hxT, y, hyT, hxy_ne, hnxy⟩ : ∃ x ∈ T, ∃ y ∈ T, x ≠ y ∧ ¬ G.Adj x y := by
      obtain ⟨x, hxT⟩ := Finset.card_pos.mp (show 0 < T.card by omega)
      obtain ⟨y, hyT⟩ := Finset.card_pos.mp (show 0 < (T.erase x).card by rw [Finset.card_erase_of_mem hxT]; omega)
      have hyx : y ≠ x := (Finset.mem_erase.mp hyT).1
      have hyT' : y ∈ T := (Finset.mem_erase.mp hyT).2
      obtain ⟨z, hzT⟩ := Finset.card_pos.mp (show 0 < ((T.erase x).erase y).card by
        rw [Finset.card_erase_of_mem hyT, Finset.card_erase_of_mem hxT]; omega)
      have hzy : z ≠ y := (Finset.mem_erase.mp hzT).1
      have hzx : z ≠ x := (Finset.mem_erase.mp (Finset.mem_erase.mp hzT).2).1
      have hzT' : z ∈ T := (Finset.mem_erase.mp (Finset.mem_erase.mp hzT).2).2
      by_cases hxy : G.Adj x y
      · by_cases hxz : G.Adj x z
        · exact ⟨y, hyT', z, hzT', hzy.symm, hnoK4 a x y z
            (hFG (Finset.mem_filter.mp (Finset.mem_sdiff.mp (hTR hxT)).1).2)
            (hFG (Finset.mem_filter.mp (Finset.mem_sdiff.mp (hTR hyT')).1).2)
            (hFG (Finset.mem_filter.mp (Finset.mem_sdiff.mp (hTR hzT')).1).2) hxy hxz⟩
        · exact ⟨x, hxT, z, hzT', hzx.symm, hxz⟩
      · exact ⟨x, hxT, y, hyT', hyx.symm, hxy⟩
    have hxR := Finset.mem_sdiff.mp (hTR hxT)
    have hyR := Finset.mem_sdiff.mp (hTR hyT)
    have hnb : ∀ t ∈ R, ¬ G.Adj b t := by
      intro t ht hbt
      have htR := Finset.mem_sdiff.mp ht
      have hmem : t ∈ CG a b := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hFG (Finset.mem_filter.mp htR.1).2, hbt⟩
      rw [← hCF_eq_CG a b hab, ← hM_eq_ab] at hmem
      exact htR.2 (Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inr hmem))))
    have hne : ∀ t ∈ R, ¬ G.Adj e t := by
      intro t ht het
      have htR := Finset.mem_sdiff.mp ht
      have hmem : t ∈ CG a e := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hFG (Finset.mem_filter.mp htR.1).2, het⟩
      rw [← hCF_eq_CG a e hea.symm, ← hM_eq_ae] at hmem
      exact htR.2 (Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inr hmem))))
    let J : Finset (Fin n) := {b, e, x, y}
    have hJU : J ⊆ U a := by
      intro t ht
      simp only [J, Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl | rfl | rfl
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hab⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hea.symm⟩
      · exact hxR.1
      · exact hyR.1
    have hJind : ∀ u ∈ J, ∀ v ∈ J, ¬ G.Adj u v := by
      intro u hu v hv huv
      simp only [J, Finset.mem_insert, Finset.mem_singleton] at hu hv
      rcases hu with hu | hu | hu | hu <;> rcases hv with hv | hv | hv | hv <;> rw [hu, hv] at huv
      all_goals first | exact G.irrefl huv | exact hnbe huv | exact hnbe huv.symm | exact hnb x (hTR hxT) huv | exact hnb x (hTR hxT) huv.symm | exact hnb y (hTR hyT) huv | exact hnb y (hTR hyT) huv.symm | exact hne x (hTR hxT) huv | exact hne x (hTR hxT) huv.symm | exact hne y (hTR hyT) huv | exact hne y (hTR hyT) huv.symm | exact hnxy huv | exact hnxy huv.symm
    have hbx : b ≠ x := fun h => hxR.2 (Finset.mem_insert.mpr (Or.inl h.symm))
    have hby : b ≠ y := fun h => hyR.2 (Finset.mem_insert.mpr (Or.inl h.symm))
    have hex : e ≠ x := fun h => hxR.2 (Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inl h.symm))))
    have hey : e ≠ y := fun h => hyR.2 (Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inl h.symm))))
    have hJc : J.card = 4 := by
      rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
          Finset.card_insert_of_notMem, Finset.card_singleton]
      · simp [hxy_ne]
      · simp [hex, hey]
      · simp [hbe, hbx, hby]
    have hle3 := halpha3 a J hJU hJind
    omega
  let U4 := S a ∪ S b ∪ S c ∪ S e
  have hbi_sub : (A.biUnion (fun w => (univ.filter (G.Adj w)) \ I w)) \ A ⊆ U4 := by
    intro v hv
    obtain ⟨w, hwA, hvw⟩ := Finset.mem_biUnion.mp (Finset.mem_sdiff.mp hv).1
    simp only [A, Finset.mem_insert, Finset.mem_singleton] at hwA
    rcases hwA with rfl | rfl | rfl | rfl
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl hvw)))))
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr hvw)))))
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr hvw)))
    · exact Finset.mem_union.mpr (Or.inr hvw)
  have hind_sum : ∀ X : Finset (Fin n), X ⊆ U4 →
      X.card = ∑ v ∈ U4, (if v ∈ X then (1 : ℕ) else 0) := by
    intro X hX
    rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr hX]
    simp
  have hpt : ∀ v ∈ U4,
      1 + (if v ∈ S a ∩ S b then (1 : ℕ) else 0) + (if v ∈ S b ∩ S c then 1 else 0) +
          (if v ∈ S c ∩ S e then 1 else 0) + (if v ∈ S e ∩ S a then 1 else 0) ≤
      (if v ∈ S a then (1 : ℕ) else 0) + (if v ∈ S b then 1 else 0) +
          (if v ∈ S c then 1 else 0) + (if v ∈ S e then 1 else 0) +
          (if v ∈ M then 1 else 0) := by
    intro v hv
    have hmemU : v ∈ S a ∨ v ∈ S b ∨ v ∈ S c ∨ v ∈ S e := by
      simp only [U4, Finset.mem_union] at hv; tauto
    by_cases h1 : v ∈ S a <;> by_cases h2 : v ∈ S b <;> by_cases h3 : v ∈ S c <;> by_cases h4 : v ∈ S e
    all_goals simp [M, h1, h2, h3, h4] at hmemU ⊢
  have hsum_le := Finset.sum_le_sum hpt
  have hU4_c : U4.card + (S a ∩ S b).card + (S b ∩ S c).card + (S c ∩ S e).card + (S e ∩ S a).card ≤
      (S a).card + (S b).card + (S c).card + (S e).card + M.card := by
    have h1 : (∑ _v ∈ U4, (1 : ℕ)) = U4.card := by simp
    have hSa := hind_sum (S a) (fun v hv => Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl hv))))))
    have hSb := hind_sum (S b) (fun v hv => Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr hv))))))
    have hSc' := hind_sum (S c) (fun v hv => Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr hv))))
    have hSe := hind_sum (S e) (fun v hv => Finset.mem_union.mpr (Or.inr hv))
    have hSab := hind_sum (S a ∩ S b) (fun v hv => Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl (Finset.mem_inter.mp hv).1))))))
    have hSbc := hind_sum (S b ∩ S c) (fun v hv => Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr (Finset.mem_inter.mp hv).1))))))
    have hSce := hind_sum (S c ∩ S e) (fun v hv => Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr (Finset.mem_inter.mp hv).1))))
    have hSea := hind_sum (S e ∩ S a) (fun v hv => Finset.mem_union.mpr (Or.inr (Finset.mem_inter.mp hv).1))
    have hMsub := hind_sum M (fun v hv => Finset.mem_union.mpr (Or.inr (Finset.mem_inter.mp hv).2))
    simp only [Finset.sum_add_distrib] at hsum_le
    rw [h1, ← hSab, ← hSbc, ← hSce, ← hSea, ← hSa, ← hSb, ← hSc', ← hSe, ← hMsub] at hsum_le
    exact hsum_le
  have h1ab : 3 ≤ (S a ∩ S b).card := by
    rw [← (hcodes a b hab).1]
    exact Finset.card_le_card (hCF_sub a (by simp [A]) b (by simp [A]) hab)
  have h1bc : 3 ≤ (S b ∩ S c).card := by
    rw [← (hcodes b c hbc).1]
    exact Finset.card_le_card (hCF_sub b (by simp [A]) c (by simp [A]) hbc)
  have h1ce : 3 ≤ (S c ∩ S e).card := by
    rw [← (hcodes c e hce).1]
    exact Finset.card_le_card (hCF_sub c (by simp [A]) e (by simp [A]) hce)
  have h1ea : 3 ≤ (S e ∩ S a).card := by
    rw [← (hcodes e a hea).1]
    exact Finset.card_le_card (hCF_sub e (by simp [A]) a (by simp [A]) hea)
  have hSa8 := hSc a (by simp [A])
  have hSb8 := hSc b (by simp [A])
  have hSc8 := hSc c (by simp [A])
  have hSe8 := hSc e (by simp [A])
  have hU4_le22 : U4.card ≤ 22 := by omega
  exact ⟨A, I, hAc, (Finset.card_le_card hbi_sub).trans hU4_le22, hP, hind, hself⟩

private theorem h12_certificate_of_tight_links {n : ℕ} (G F : SimpleGraph (Fin n))
    (hG : G.CliqueFree 4) (hFG : F ≤ G)
    (hd : ∀ v, (univ.filter (G.Adj v)).card ≤ 11)
    (hf : ∀ b x, F.Adj b x → 8 ≤ (univ.filter (F.Adj b)).card)
    (ht : ∀ b x, F.Adj b x →
      2 ≤ (univ.filter (fun z => F.Adj b z ∧ F.Adj x z)).card)
    (p : Fin n) (hp : ∃ x, F.Adj p x)
    (hwbound : let N (x : Fin n) := univ.filter (G.Adj x)
      let d (b x : Fin n) := (univ.filter (fun z => G.Adj b z ∧ G.Adj x z)).card
      let r (b x : Fin n) : ℕ := if d b x ≤ 4 then 2 else if d b x ≤ 6 then 1 else 0
      let w (b x : Fin n) := (11 - (N x).card) + (d b x + r b x - 4)
      ∀ (b : Fin n) (J L : Finset (Fin n)),
        J ⊆ univ.filter (F.Adj b) → L ⊆ J → L.card = 3 →
        (∀ x ∈ J, ∀ y ∈ J, ¬ G.Adj x y) →
        J.card + (11 - (N b).card) + (∑ x ∈ L, w b x) ≤ 6)
    (htight : let U (b : Fin n) := univ.filter (F.Adj b)
      let C (b u : Fin n) := univ.filter (fun z => F.Adj b z ∧ F.Adj u z)
      ∀ b, (∑ u ∈ U b, (C b u).card) = 3 * (U b).card ∧
        ∀ u ∈ U b,
          ((C b u).card = 2 → ∀ z ∈ C b u, 4 ≤ (C b z).card) ∧
          (4 ≤ (C b u).card →
            ((C b u).filter (fun z => (C b z).card = 2)).card = 2 * ((C b u).card - 3))) :
    ∃ (A : Finset (Fin n)) (I : Fin n → Finset (Fin n)),
      A.card = 4 ∧
      ((A.biUnion (fun w => (univ.filter (G.Adj w)) \ I w)) \ A).card ≤ 22 ∧
      (∀ w ∈ A, ∀ x ∈ I w, G.Adj w x ∧ ∃ z, G.Adj w z ∧ G.Adj x z) ∧
      (∀ w ∈ A, ∀ x ∈ I w, ∀ y ∈ I w, ¬ G.Adj x y) ∧
      (∀ w ∈ A, ∀ x ∈ A, G.Adj w x → x ∈ I w) := by
  classical
  have hcodes := h12_tight_edge_codegrees G F hG hFG ht hwbound htight
  obtain ⟨a, b, c, e, ha, hb, hc, he, hab, hbc, hce, hea, hac, hbe⟩ :=
    h12_square_in_cubic_link G F hG hFG hf p hp hwbound hcodes
  exact h12_square_deletion G F hG hFG hd hf hwbound hcodes p a b c e
    ha hb hc he hab hbc hce hea hac hbe

private theorem h12_overlap_from_weight_bound {n : ℕ} (G F : SimpleGraph (Fin n))
    (hG : G.CliqueFree 4) (hFG : F ≤ G)
    (hd : ∀ v, (univ.filter (G.Adj v)).card ≤ 11)
    (hf : ∀ b x, F.Adj b x → 8 ≤ (univ.filter (F.Adj b)).card)
    (ht : ∀ b x, F.Adj b x →
      2 ≤ (univ.filter (fun z => F.Adj b z ∧ F.Adj x z)).card)
    (hsey : 3 * (∑ v : Fin n, (univ.filter (F.Adj v)).card) ≤
      ∑ v : Fin n, ∑ u ∈ univ.filter (F.Adj v),
        (univ.filter (fun z => F.Adj v z ∧ F.Adj u z)).card)
    (p : Fin n) (hp : ∃ x, F.Adj p x)
    (hpavg : 3 * (univ.filter (F.Adj p)).card ≤
      ∑ u ∈ univ.filter (F.Adj p),
        (univ.filter (fun z => F.Adj p z ∧ F.Adj u z)).card)
    (hwbound : let N (x : Fin n) := univ.filter (G.Adj x)
      let d (b x : Fin n) := (univ.filter (fun z => G.Adj b z ∧ G.Adj x z)).card
      let r (b x : Fin n) : ℕ := if d b x ≤ 4 then 2 else if d b x ≤ 6 then 1 else 0
      let w (b x : Fin n) := (11 - (N x).card) + (d b x + r b x - 4)
      ∀ (b : Fin n) (J L : Finset (Fin n)),
        J ⊆ univ.filter (F.Adj b) → L ⊆ J → L.card = 3 →
        (∀ x ∈ J, ∀ y ∈ J, ¬ G.Adj x y) →
        J.card + (11 - (N b).card) + (∑ x ∈ L, w b x) ≤ 6) :
    ∃ (A : Finset (Fin n)) (I : Fin n → Finset (Fin n)),
      A.card = 4 ∧
      ((A.biUnion (fun w => (univ.filter (G.Adj w)) \ I w)) \ A).card ≤ 22 ∧
      (∀ w ∈ A, ∀ x ∈ I w, G.Adj w x ∧ ∃ z, G.Adj w z ∧ G.Adj x z) ∧
      (∀ w ∈ A, ∀ x ∈ I w, ∀ y ∈ I w, ¬ G.Adj x y) ∧
      (∀ w ∈ A, ∀ x ∈ A, G.Adj w x → x ∈ I w) := by
  classical
  let N (x : Fin n) := univ.filter (G.Adj x)
  let U (x : Fin n) := univ.filter (F.Adj x)
  let C (b x : Fin n) := univ.filter (fun z => F.Adj b z ∧ F.Adj x z)
  let d (b x : Fin n) := (univ.filter (fun z => G.Adj b z ∧ G.Adj x z)).card
  let r (b x : Fin n) : ℕ := if d b x ≤ 4 then 2 else if d b x ≤ 6 then 1 else 0
  let w (b x : Fin n) := (11 - (N x).card) + (d b x + r b x - 4)
  change ∀ b J L, J ⊆ U b → L ⊆ J → L.card = 3 →
    (∀ x ∈ J, ∀ y ∈ J, ¬ G.Adj x y) →
    J.card + (11 - (N b).card) + (∑ x ∈ L, w b x) ≤ 6 at hwbound
  have hpos (b z : Fin n) (hz : 3 ≤ (C b z).card) : 1 ≤ w b z := by
    have hsub : C b z ⊆ univ.filter (fun t => G.Adj b t ∧ G.Adj z t) := by
      intro t ht'
      obtain ⟨hbt, hzt⟩ := (Finset.mem_filter.mp ht').2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hFG hbt, hFG hzt⟩
    have hlo : 3 ≤ d b z := hz.trans (Finset.card_le_card hsub)
    change 1 ≤ (11 - (N z).card) + (d b z + r b z - 4)
    by_cases h₄ : d b z ≤ 4
    · simp only [r, if_pos h₄]
      omega
    · by_cases h₆ : d b z ≤ 6
      · simp only [r, if_neg h₄, if_pos h₆]
        omega
      · simp only [r, if_neg h₄, if_neg h₆]
        omega
  have hlocal (b u : Fin n) (hbu : F.Adj b u) (hlarge : 4 ≤ (C b u).card) :
      (C b u).card + ((C b u).filter (fun z => 3 ≤ (C b z).card)).card ≤ 6 := by
    have hJ : C b u ⊆ U b := by
      intro z hz
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hz).2.1⟩
    have hind : ∀ z ∈ C b u, ∀ t ∈ C b u, ¬ G.Adj z t := by
      intro z hz t ht' hzt
      obtain ⟨hbz, huz⟩ := (Finset.mem_filter.mp hz).2
      obtain ⟨hbt, hut⟩ := (Finset.mem_filter.mp ht').2
      have e₁ := hFG hbu
      have e₂ := hFG hbz
      have e₃ := hFG hbt
      have e₄ := hFG huz
      have e₅ := hFG hut
      have hbN : b ∉ ({u, z, t} : Finset (Fin n)) := by simp [e₁.ne, e₂.ne, e₃.ne]
      have huN : u ∉ ({z, t} : Finset (Fin n)) := by simp [e₄.ne, e₅.ne]
      have hzN : z ∉ ({t} : Finset (Fin n)) := by simp [hzt.ne]
      apply hG ({b, u, z, t} : Finset (Fin n))
      constructor
      · intro a ha c hc hac
        simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at ha hc
        rcases ha with rfl | rfl | rfl | rfl <;>
          rcases hc with rfl | rfl | rfl | rfl <;>
          first | exact (hac rfl).elim | assumption | exact G.symm.symm _ _ (by assumption)
      · rw [Finset.card_insert_of_notMem hbN, Finset.card_insert_of_notMem huN,
          Finset.card_insert_of_notMem hzN]
        simp
    apply h12_weighted_three_count (C b u) (w b) (fun z => 3 ≤ (C b z).card) hlarge
    · intro z _ hz
      exact hpos b z hz
    · intro L hL hLc
      have h := hwbound b (C b u) L hJ hL hLc hind
      omega
  have hlinks := h12_link_discharge F ht hlocal
  have hupper (b : Fin n) : (∑ u ∈ U b, (C b u).card) ≤ 3 * (U b).card :=
    (hlinks b).1
  rw [Finset.mul_sum] at hsey
  change (∑ b : Fin n, 3 * (U b).card) ≤ ∑ b : Fin n, ∑ u ∈ U b, (C b u).card at hsey
  have htight (b : Fin n) : (∑ u ∈ U b, (C b u).card) = 3 * (U b).card := by
    apply Nat.le_antisymm (hupper b)
    by_contra hn
    have hlt : (∑ u ∈ U b, (C b u).card) < 3 * (U b).card := by omega
    have hs : (∑ v : Fin n, ∑ u ∈ U v, (C v u).card) <
        ∑ v : Fin n, 3 * (U v).card :=
      Finset.sum_lt_sum (fun v _ => hupper v) ⟨b, Finset.mem_univ _, hlt⟩
    exact (not_lt_of_ge hsey) hs
  exact h12_certificate_of_tight_links G F hG hFG hd hf ht p hp hwbound
    (fun b => ⟨htight b, (hlinks b).2 (htight b)⟩)

private theorem h12_residual_overlap_certificate {n : ℕ} (G F : SimpleGraph (Fin n))
    (hG : G.CliqueFree 4) (hFG : F ≤ G)
    (hd : ∀ v, (univ.filter (G.Adj v)).card ≤ 11)
    (hf : ∀ b x, F.Adj b x → 8 ≤ (univ.filter (F.Adj b)).card)
    (ht : ∀ b x, F.Adj b x →
      2 ≤ (univ.filter (fun z => F.Adj b z ∧ F.Adj x z)).card)
    (hsey : 3 * (∑ v : Fin n, (univ.filter (F.Adj v)).card) ≤
      ∑ v : Fin n, ∑ u ∈ univ.filter (F.Adj v),
        (univ.filter (fun z => F.Adj v z ∧ F.Adj u z)).card)
    (p : Fin n) (hp : ∃ x, F.Adj p x)
    (hpavg : 3 * (univ.filter (F.Adj p)).card ≤
      ∑ u ∈ univ.filter (F.Adj p),
        (univ.filter (fun z => F.Adj p z ∧ F.Adj u z)).card)
    (hnostar : let d (b x : Fin n) := (univ.filter (fun z => G.Adj b z ∧ G.Adj x z)).card
      let q (b x : Fin n) := (univ.filter (G.Adj x)).card - 1 - d b x -
        (if d b x ≤ 4 then 2 else if d b x ≤ 6 then 1 else 0)
      ¬ ∃ (b : Fin n) (J L : Finset (Fin n)),
        J ⊆ univ.filter (F.Adj b) ∧ L ⊆ J ∧ L.card = 3 ∧
        (∀ x ∈ J, ∀ y ∈ J, ¬ G.Adj x y) ∧
        1 + ((univ.filter (G.Adj b)) \ (J \ L)).card + (∑ x ∈ L, q b x) ≤ 26) :
    ∃ (A : Finset (Fin n)) (I : Fin n → Finset (Fin n)),
      A.card = 4 ∧
      ((A.biUnion (fun w => (univ.filter (G.Adj w)) \ I w)) \ A).card ≤ 22 ∧
      (∀ w ∈ A, ∀ x ∈ I w, G.Adj w x ∧ ∃ z, G.Adj w z ∧ G.Adj x z) ∧
      (∀ w ∈ A, ∀ x ∈ I w, ∀ y ∈ I w, ¬ G.Adj x y) ∧
      (∀ w ∈ A, ∀ x ∈ A, G.Adj w x → x ∈ I w) := by
  classical
  exact h12_overlap_from_weight_bound G F hG hFG hd hf ht hsey p hp hpavg
    (h12_no_star_weight_bound G F hFG hd hf ht hnostar)

private lemma oma151_h12_star_or_square {n : ℕ} (G F : SimpleGraph (Fin n))
    (hG : G.CliqueFree 4) (hFG : F ≤ G)
    (he : ∃ b x, F.Adj b x)
    (hd : ∀ v, (Finset.univ.filter (G.Adj v)).card ≤ 11)
    (hf : ∀ b x, F.Adj b x → 8 ≤ (Finset.univ.filter (F.Adj b)).card)
    (ht : ∀ b x, F.Adj b x →
      2 ≤ (Finset.univ.filter (fun z => F.Adj b z ∧ F.Adj x z)).card)
    (hsey : 3 * (∑ v : Fin n, (univ.filter (F.Adj v)).card) ≤
      ∑ v : Fin n, ∑ u ∈ univ.filter (F.Adj v),
        (univ.filter (fun z => F.Adj v z ∧ F.Adj u z)).card) :
    let N := fun v => Finset.univ.filter (G.Adj v)
    let P := fun v => (N v).filter (fun x => ∃ z, G.Adj v z ∧ G.Adj x z)
    ∃ (Anch D : Finset (Fin n)) (I : Fin n → Finset (Fin n)),
      Anch.card = 4 ∧ D.card ≤ 26 ∧ Anch ⊆ D ∧
      (∀ w ∈ Anch, ∀ x, G.Adj w x → x ∉ I w → x ∈ D) ∧
      (∀ w ∈ Anch, ∀ x ∈ I w, G.Adj w x ∧ ∃ z, G.Adj w z ∧ G.Adj x z) ∧
      (∀ w ∈ Anch, ∀ x ∈ I w, ∀ y ∈ I w, ¬ G.Adj x y) ∧
      (∀ w ∈ Anch, ∀ x ∈ Anch, G.Adj w x → x ∈ I w) := by
  classical
  intro N P
  let d (b x : Fin n) : ℕ := (univ.filter (fun z => G.Adj b z ∧ G.Adj x z)).card
  let q (b x : Fin n) : ℕ := (univ.filter (G.Adj x)).card - 1 - d b x -
    (if d b x ≤ 4 then 2 else if d b x ≤ 6 then 1 else 0)
  have cert : ∃ (A : Finset (Fin n)) (I : Fin n → Finset (Fin n)),
      A.card = 4 ∧
      ((A.biUnion (fun w => (univ.filter (G.Adj w)) \ I w)) \ A).card ≤ 22 ∧
      (∀ w ∈ A, ∀ x ∈ I w, G.Adj w x ∧ ∃ z, G.Adj w z ∧ G.Adj x z) ∧
      (∀ w ∈ A, ∀ x ∈ I w, ∀ y ∈ I w, ¬ G.Adj x y) ∧
      (∀ w ∈ A, ∀ x ∈ A, G.Adj w x → x ∈ I w) := by
    by_cases hs : ∃ (b : Fin n) (J L : Finset (Fin n)),
        J ⊆ univ.filter (F.Adj b) ∧ L ⊆ J ∧ L.card = 3 ∧
        (∀ x ∈ J, ∀ y ∈ J, ¬ G.Adj x y) ∧
        1 + ((univ.filter (G.Adj b)) \ (J \ L)).card + (∑ x ∈ L, q b x) ≤ 26
    · obtain ⟨b, J, L, hJ, hL, hLc, hJi, hb⟩ := hs
      exact h12_star_budget_certificate G F hG hFG hf ht b J L hJ hL hLc hJi hb
    · obtain ⟨b, hbe, hb⟩ := h12_positive_dense_link F he hsey
      exact h12_residual_overlap_certificate G F hG hFG hd hf ht hsey b hbe hb hs
  obtain ⟨A, I, hAc, hC, hlink, hind, hself⟩ := cert
  let C := (A.biUnion (fun w => (univ.filter (G.Adj w)) \ I w)) \ A
  have hCc : C.card ≤ 22 := hC
  have hdisj : Disjoint A C := Finset.disjoint_left.mpr (fun _ ha hc =>
    (Finset.mem_sdiff.mp hc).2 ha)
  refine ⟨A, A ∪ C, I, hAc, ?_, ?_, ?_, hlink, hind, hself⟩
  · rw [Finset.card_union_of_disjoint hdisj, hAc]
    omega
  · intro x hx
    exact Finset.mem_union.mpr (Or.inl hx)
  · intro w hw x hwx hxI
    by_cases hxA : x ∈ A
    · exact Finset.mem_union.mpr (Or.inl hxA)
    · have hxU : x ∈ A.biUnion (fun a => (univ.filter (G.Adj a)) \ I a) :=
        Finset.mem_biUnion.mpr ⟨w, hw, Finset.mem_sdiff.mpr
          ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hwx⟩, hxI⟩⟩
      exact Finset.mem_union.mpr (Or.inr (show x ∈ C from Finset.mem_sdiff.mpr ⟨hxU, hxA⟩))

-- === END HELPERS ===

theorem main : H1 → H2 → H3 → H4 → OMA.R_Erdos151_erdos_151_variants_cliqueFree_four_R1_H1_R1_H1_R1_H1_R1.H1 := by
  classical
  intro h1 h2 h3 h4 n G hG h12 hdeg hS
  by_cases h13 : 13 ≤ Erdos151.H n
  · exact h1 n G hG (Or.inr h13) hdeg hS
  · have hH : Erdos151.H n = 12 := by omega
    have hn53 : 53 ≤ n := h3 n h12
    by_cases hn_eq : n = 53
    · exact h1 n G hG (Or.inl ⟨hH, hn_eq⟩) hdeg hS
    · have hn54 : 54 ≤ n := by omega
      have hd (v : Fin n) : (Finset.univ.filter (G.Adj v)).card ≤ 11 := by
        have hv := hdeg v
        omega
      rw [hH]
      obtain hgood | ⟨F, hFG, he, hf, ht, hsey⟩ := oma151_h12_core G hG h12 h4
      · exact hgood
      · obtain ⟨Anch, D, I, hAc, hDc, hAD, hcov, hP, hind, hself⟩ :=
          oma151_h12_star_or_square G F hG hFG he hd hf ht hsey
        exact extend_from_28 h2 h4.1 G hG Anch D I (k := 12) (by omega) (by omega)
          hAD (fun w hw x hx => hcov w hw x (Finset.mem_filter.mp (Finset.mem_sdiff.mp hx).1).2 (Finset.mem_sdiff.mp hx).2)
          hP hind hself

end Proof

end OMA.R_Erdos151_erdos_151_variants_cliqueFree_four_R1_H1_R1_H1_R1_H1_R1_H1_R1
