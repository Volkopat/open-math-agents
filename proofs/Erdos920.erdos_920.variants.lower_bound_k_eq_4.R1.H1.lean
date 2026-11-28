import OMAReductions.R_Erdos920_erdos_920_variants_lower_bound_k_eq_4_R1
import Mathlib










open Finset

noncomputable section

namespace SimpleGraph

theorem IndepSetFree.comap {α β : Type*} {G : SimpleGraph α} {H : SimpleGraph β} {n : ℕ}
    (f : H ↪g G) : G.IndepSetFree n → H.IndepSetFree n := by
  intro h
  rw [← cliqueFree_compl] at h ⊢
  exact CliqueFree.comap
    (((Embedding.complEquiv (G := H) (H := G)).toFun f).isContained) h

def Iso.compl {α β : Type*} {G : SimpleGraph α} {H : SimpleGraph β}
    (e : G ≃g H) : Gᶜ ≃g Hᶜ where
  toEquiv := e.toEquiv
  map_rel_iff' := by
    intro v w
    by_cases hvw : v = w
    · subst hvw
      simp
    · simpa [compl_adj, hvw, e.injective.ne_iff] using
        not_congr (e.map_adj_iff (v := v) (w := w))

theorem Iso.cliqueFree_iff {α β : Type*} {G : SimpleGraph α} {H : SimpleGraph β} {n : ℕ}
    (e : G ≃g H) : G.CliqueFree n ↔ H.CliqueFree n := by
  constructor
  · intro h
    exact CliqueFree.comap e.symm.toEmbedding.isContained h
  · intro h
    exact CliqueFree.comap e.toEmbedding.isContained h

theorem Iso.indepSetFree_iff {α β : Type*} {G : SimpleGraph α} {H : SimpleGraph β} {n : ℕ}
    (e : G ≃g H) : G.IndepSetFree n ↔ H.IndepSetFree n := by
  simpa [indepSetFree_compl] using
    (Iso.cliqueFree_iff (n := n) (e := Iso.compl e))

end SimpleGraph

namespace Ramsey





def RamseyProperty (k l n : ℕ) : Prop :=
  ∀ G : SimpleGraph (Fin n), ¬ (G.CliqueFree k ∧ G.IndepSetFree l)

lemma ramseyProperty_of_card {k l n : ℕ} {α : Type*} [Fintype α]
    (hcard : Fintype.card α = n) (hprop : RamseyProperty k l n) :
    ∀ G : SimpleGraph α, ¬ (G.CliqueFree k ∧ G.IndepSetFree l) := by
  intro G hbad
  let H : SimpleGraph (Fin n) := G.overFin hcard
  let e : G ≃g H := SimpleGraph.overFinIso (G := G) hcard
  have hcf : H.CliqueFree k := hbad.1.comap e.symm.toEmbedding.isContained
  have hcfCompl : Hᶜ.CliqueFree l := by
    have hGCompl : Gᶜ.CliqueFree l := by
      simpa [SimpleGraph.cliqueFree_compl] using hbad.2
    exact hGCompl.comap
      (((SimpleGraph.Embedding.complEquiv (G := H) (H := G)).toFun e.symm.toEmbedding).isContained)
  have hif : H.IndepSetFree l := by
    simpa [SimpleGraph.cliqueFree_compl] using hcfCompl
  exact hprop H ⟨hcf, hif⟩

lemma ramseyProperty_mono {k l n m : ℕ} (hnm : n ≤ m) :
    RamseyProperty k l n → RamseyProperty k l m := by
  intro h G hbad
  let f : Fin n ↪ Fin m := Fin.castLEEmb hnm
  have hcf : (G.comap f).CliqueFree k :=
    hbad.1.comap (SimpleGraph.Embedding.comap f G).isContained
  have hif : (G.comap f).IndepSetFree l :=
    SimpleGraph.IndepSetFree.comap (SimpleGraph.Embedding.comap f G) hbad.2
  exact h (G.comap f) ⟨hcf, hif⟩


theorem ramseyProperty_exists (k l : ℕ) : ∃ n, RamseyProperty k l n := by
  revert l
  induction k with
  | zero =>
      intro l
      refine ⟨0, ?_⟩
      intro G hbad
      simpa using hbad.1
  | succ k ih =>
      intro l
      induction l with
      | zero =>
          refine ⟨0, ?_⟩
          intro G hbad
          exact hbad.2 ∅ (by simp [SimpleGraph.isNIndepSet_iff])
      | succ l ihl =>
          rcases ih (l + 1) with ⟨m, hm⟩
          rcases ihl with ⟨n, hn⟩
          refine ⟨m + n + 1, ?_⟩
          intro G hbad
          classical
          let v : Fin (m + n + 1) := 0
          by_cases hdeg : m ≤ G.degree v
          · let H : SimpleGraph (G.neighborSet v) := G.induce (G.neighborSet v)
            have hprop : RamseyProperty k (l + 1) (G.degree v) := ramseyProperty_mono hdeg hm
            have hcf : H.CliqueFree k := by
              intro t ht
              let t' : Finset (Fin (m + n + 1)) :=
                Finset.map ⟨Subtype.val, Subtype.val_injective⟩ t
              have htInd :
                  (((⊤ : SimpleGraph.Subgraph G).induce (G.neighborSet v)).coe).IsNClique k t := by
                rw [← SimpleGraph.induce_eq_coe_induce_top]
                exact ht
              have ht' : G.IsNClique k t' := by
                simpa [H, t'] using
                  (SimpleGraph.IsNClique.of_induce
                    (S := (⊤ : SimpleGraph.Subgraph G)) (F := G.neighborSet v) (cc := htInd))
              have hvt : ∀ b ∈ t', G.Adj v b := by
                intro b hb
                rcases Finset.mem_map.mp hb with ⟨x, hx, rfl⟩
                exact x.property
              exact hbad.1 _ (ht'.insert hvt)
            have hif : H.IndepSetFree (l + 1) := by
              exact SimpleGraph.IndepSetFree.comap
                (SimpleGraph.Embedding.induce (G := G) (s := G.neighborSet v)) hbad.2
            exact ramseyProperty_of_card (G.card_neighborSet_eq_degree v) hprop H ⟨hcf, hif⟩
          · let H : SimpleGraph (Gᶜ.neighborSet v) := G.induce (Gᶜ.neighborSet v)
            have hcompdeg : n ≤ Gᶜ.degree v := by
              rw [G.degree_compl (v := v), Fintype.card_fin]
              omega
            have hprop : RamseyProperty (k + 1) l (Gᶜ.degree v) :=
              ramseyProperty_mono hcompdeg hn
            have hcf : H.CliqueFree (k + 1) := by
              exact hbad.1.comap
                (SimpleGraph.Embedding.induce (G := G) (s := Gᶜ.neighborSet v)).isContained
            have hif : H.IndepSetFree l := by
              intro t ht
              let t' : Finset (Fin (m + n + 1)) :=
                Finset.map ⟨Subtype.val, Subtype.val_injective⟩ t
              have htInd :
                  (((⊤ : SimpleGraph.Subgraph G).induce
                    (Gᶜ.neighborSet v)).coe).IsNIndepSet l t := by
                rw [← SimpleGraph.induce_eq_coe_induce_top]
                exact ht
              have ht' : G.IsNIndepSet l t' := by
                simpa [H, t'] using
                  (SimpleGraph.isNIndepSet_induce
                    (G := G) (F := Gᶜ.neighborSet v) (s := t) (n := l)).1 htInd
              have ht'compl : Gᶜ.IsNClique l t' := by
                simpa using ht'
              have hvt : ∀ b ∈ t', Gᶜ.Adj v b := by
                intro b hb
                rcases Finset.mem_map.mp hb with ⟨x, hx, rfl⟩
                exact x.property
              have ht'' : G.IsNIndepSet (l + 1) (insert v t') := by
                simpa using ht'compl.insert hvt
              exact hbad.2 _ ht''
            exact ramseyProperty_of_card (Gᶜ.card_neighborSet_eq_degree v) hprop H ⟨hcf, hif⟩


def ramseyNumber (k l : ℕ) : ℕ :=
  by
    classical
    exact Nat.find (ramseyProperty_exists k l)

lemma ramseyNumber_spec (k l : ℕ) : RamseyProperty k l (ramseyNumber k l) :=
  by
    classical
    exact Nat.find_spec (ramseyProperty_exists k l)

lemma ramseyProperty_one_left (l : ℕ) : RamseyProperty 1 l 1 := by
  intro G hbad
  simpa [SimpleGraph.cliqueFree_one] using hbad.1

lemma ramseyProperty_mono_vertices {k l n m : ℕ} (hnm : n ≤ m) :
    RamseyProperty k l n → RamseyProperty k l m := by
  intro h G hbad
  let f : Fin n ↪ Fin m := Fin.castLEEmb hnm
  have hcf : (G.comap f).CliqueFree k :=
    hbad.1.comap (SimpleGraph.Embedding.comap f G).isContained
  have hif : (G.comap f).IndepSetFree l :=
    SimpleGraph.IndepSetFree.comap (SimpleGraph.Embedding.comap f G) hbad.2
  exact h (G.comap f) ⟨hcf, hif⟩

lemma ramseyNumber_le_of_property {k l n : ℕ} (hn : RamseyProperty k l n) :
    ramseyNumber k l ≤ n := by
  classical
  exact Nat.find_min' (ramseyProperty_exists k l) hn

lemma ramseyProperty_of_ramseyNumber_le {k l n : ℕ} (hn : ramseyNumber k l ≤ n) :
    RamseyProperty k l n :=
  ramseyProperty_mono_vertices hn (ramseyNumber_spec k l)

lemma ramseyProperty_zero_right (k : ℕ) : RamseyProperty k 0 0 := by
  intro G hbad
  have hnil : G.IsNIndepSet 0 (∅ : Finset (Fin 0)) := by
    simp [SimpleGraph.isNIndepSet_iff]
  exact hbad.2 _ hnil

lemma ramseyNumber_zero_right (k : ℕ) : ramseyNumber k 0 = 0 := by
  exact le_antisymm (ramseyNumber_le_of_property (ramseyProperty_zero_right k)) (Nat.zero_le _)

lemma ramseyNumber_pos {u m : ℕ} (hu : 1 ≤ u) (hm : 1 ≤ m) : 0 < ramseyNumber u m := by
  by_contra hpos
  have hz : ramseyNumber u m = 0 := Nat.eq_zero_of_not_pos hpos
  have hprop : RamseyProperty u m 0 := by
    simpa [hz] using ramseyNumber_spec u m
  let G : SimpleGraph (Fin 0) := ⊥
  have hcf : G.CliqueFree u := by
    have hcard : Fintype.card (Fin 0) < u := by
      simpa [Fintype.card_fin] using (Nat.succ_le_iff.mp hu)
    exact SimpleGraph.cliqueFree_of_card_lt (G := G) hcard
  have hif : G.IndepSetFree m := by
    rw [← SimpleGraph.cliqueFree_compl]
    have hcard : Fintype.card (Fin 0) < m := by
      simpa [Fintype.card_fin] using (Nat.succ_le_iff.mp hm)
    exact SimpleGraph.cliqueFree_of_card_lt (G := Gᶜ) hcard
  exact hprop G ⟨hcf, hif⟩

lemma ramseyProperty_one_right (k : ℕ) : RamseyProperty k 1 1 := by
  intro G hbad
  have hs : G.IsNIndepSet 1 (Finset.univ : Finset (Fin 1)) := by
    refine ⟨?_, by simp⟩
    simp [SimpleGraph.isIndepSet_iff]
  exact hbad.2 _ hs

lemma ramseyProperty_succ_succ_of_sum {k l m n : ℕ}
    (hm : RamseyProperty k (l + 1) m)
    (hn : RamseyProperty (k + 1) l n)
    (hpos : 0 < m + n) :
    RamseyProperty (k + 1) (l + 1) (m + n) := by
  intro G hbad
  classical
  let v : Fin (m + n) := ⟨0, hpos⟩
  by_cases hdeg : m ≤ G.degree v
  · let H : SimpleGraph (G.neighborSet v) := G.induce (G.neighborSet v)
    have hprop : RamseyProperty k (l + 1) (G.degree v) := ramseyProperty_mono hdeg hm
    have hcf : H.CliqueFree k := by
      intro t ht
      let t' : Finset (Fin (m + n)) := Finset.map ⟨Subtype.val, Subtype.val_injective⟩ t
      have htInd :
          (((⊤ : SimpleGraph.Subgraph G).induce (G.neighborSet v)).coe).IsNClique k t := by
        rw [← SimpleGraph.induce_eq_coe_induce_top]
        exact ht
      have ht' : G.IsNClique k t' := by
        simpa [H, t'] using
          (SimpleGraph.IsNClique.of_induce
            (S := (⊤ : SimpleGraph.Subgraph G)) (F := G.neighborSet v) (cc := htInd))
      have hvt : ∀ b ∈ t', G.Adj v b := by
        intro b hb
        rcases Finset.mem_map.mp hb with ⟨x, hx, rfl⟩
        exact x.property
      exact hbad.1 _ (ht'.insert hvt)
    have hif : H.IndepSetFree (l + 1) := by
      exact SimpleGraph.IndepSetFree.comap
        (SimpleGraph.Embedding.induce (G := G) (s := G.neighborSet v)) hbad.2
    exact ramseyProperty_of_card (G.card_neighborSet_eq_degree v) hprop H ⟨hcf, hif⟩
  · let H : SimpleGraph (Gᶜ.neighborSet v) := G.induce (Gᶜ.neighborSet v)
    have hcompdeg : n ≤ Gᶜ.degree v := by
      rw [G.degree_compl (v := v), Fintype.card_fin]
      omega
    have hprop : RamseyProperty (k + 1) l (Gᶜ.degree v) := ramseyProperty_mono hcompdeg hn
    have hcf : H.CliqueFree (k + 1) := by
      exact hbad.1.comap
        (SimpleGraph.Embedding.induce (G := G) (s := Gᶜ.neighborSet v)).isContained
    have hif : H.IndepSetFree l := by
      intro t ht
      let t' : Finset (Fin (m + n)) := Finset.map ⟨Subtype.val, Subtype.val_injective⟩ t
      have htInd :
          (((⊤ : SimpleGraph.Subgraph G).induce
            (Gᶜ.neighborSet v)).coe).IsNIndepSet l t := by
        rw [← SimpleGraph.induce_eq_coe_induce_top]
        exact ht
      have ht' : G.IsNIndepSet l t' := by
        simpa [H, t'] using
          (SimpleGraph.isNIndepSet_induce
            (G := G) (F := Gᶜ.neighborSet v) (s := t) (n := l)).1 htInd
      have ht'compl : Gᶜ.IsNClique l t' := by
        simpa using ht'
      have hvt : ∀ b ∈ t', Gᶜ.Adj v b := by
        intro b hb
        rcases Finset.mem_map.mp hb with ⟨x, hx, rfl⟩
        exact x.property
      have ht'' : G.IsNIndepSet (l + 1) (insert v t') := by
        simpa using ht'compl.insert hvt
      exact hbad.2 _ ht''
    exact ramseyProperty_of_card (Gᶜ.card_neighborSet_eq_degree v) hprop H ⟨hcf, hif⟩

lemma ramseyNumber_recurrence (u m : ℕ) (hu : 1 ≤ u) :
    ramseyNumber (u + 1) (m + 1) ≤ ramseyNumber u (m + 1) + ramseyNumber (u + 1) m := by
  apply ramseyNumber_le_of_property
  have hpos : 0 < ramseyNumber u (m + 1) + ramseyNumber (u + 1) m := by
    exact Nat.add_pos_left (ramseyNumber_pos hu (by omega)) _
  exact ramseyProperty_succ_succ_of_sum
    (ramseyNumber_spec u (m + 1))
    (ramseyNumber_spec (u + 1) m)
    hpos

lemma ramseyNumber_le_choose (u : ℕ) :
    ∀ m, ramseyNumber (u + 1) m ≤ Nat.choose (u + m - 1) u := by
  induction u with
  | zero =>
      intro m
      cases m with
      | zero =>
          simp [ramseyNumber_zero_right]
      | succ m =>
          have hle : ramseyNumber 1 (m + 1) ≤ 1 := by
            exact ramseyNumber_le_of_property (ramseyProperty_one_left (m + 1))
          simpa using hle
  | succ u ihu =>
      intro m
      induction m with
      | zero =>
          rw [ramseyNumber_zero_right]
          simp
      | succ m ihm =>
          have hrec : ramseyNumber (u + 2) (m + 1) ≤
              ramseyNumber (u + 1) (m + 1) + ramseyNumber (u + 2) m := by
            exact ramseyNumber_recurrence (u + 1) m (by omega)
          have hleft : ramseyNumber (u + 1) (m + 1) ≤ Nat.choose (u + m) u := by
            simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using ihu (m + 1)
          have hright : ramseyNumber (u + 2) m ≤ Nat.choose (u + m) (u + 1) := by
            simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using ihm
          calc
            ramseyNumber (u + 2) (m + 1)
                ≤ ramseyNumber (u + 1) (m + 1) + ramseyNumber (u + 2) m := hrec
            _ ≤ Nat.choose (u + m) u + Nat.choose (u + m) (u + 1) := by
              exact Nat.add_le_add hleft hright
            _ = Nat.choose (u + m + 1) (u + 1) := by
              rw [Nat.choose_succ_succ' (u + m) u]
            _ = Nat.choose (u + 1 + (m + 1) - 1) (u + 1) := by
              simp [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

end Ramsey

namespace Erdos202
namespace ParkPham

variable {α : Type*}

section
variable [DecidableEq α]

def upClosureIn (X : Finset α) (A : Finset (Finset α)) : Finset (Finset α) :=
  X.powerset.filter fun T => ∃ S ∈ A, S ⊆ T

@[simp]
lemma mem_upClosureIn {X : Finset α} {A : Finset (Finset α)} {T : Finset α} :
    T ∈ upClosureIn X A ↔ T ⊆ X ∧ ∃ S ∈ A, S ⊆ T := by
  simp [upClosureIn, mem_powerset]

noncomputable def bernoulliMass (X S : Finset α) (p : ℝ) : ℝ :=
  p ^ S.card * (1 - p) ^ (X.card - S.card)


noncomputable def muP (X : Finset α) (U : Finset (Finset α)) (p : ℝ) : ℝ :=
  ∑ S ∈ X.powerset.filter (· ∈ U), bernoulliMass X S p

omit [DecidableEq α] in
lemma bernoulliMass_nonneg {X S : Finset α} {p : ℝ}
    (h0 : 0 ≤ p) (h1 : p ≤ 1) : 0 ≤ bernoulliMass X S p := by
  unfold bernoulliMass
  have : 0 ≤ 1 - p := by linarith
  positivity


lemma muP_nonneg {X : Finset α} {U : Finset (Finset α)} {p : ℝ}
    (h0 : 0 ≤ p) (h1 : p ≤ 1) : 0 ≤ muP X U p := by
  refine Finset.sum_nonneg fun S _ => bernoulliMass_nonneg h0 h1


lemma muP_mono_family {X : Finset α} {U V : Finset (Finset α)} {p : ℝ}
    (h0 : 0 ≤ p) (h1 : p ≤ 1) (hUV : U ⊆ V) : muP X U p ≤ muP X V p := by
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
  · intro S hS
    rcases Finset.mem_filter.mp hS with ⟨hSX, hSU⟩
    exact Finset.mem_filter.mpr ⟨hSX, hUV hSU⟩
  · intros
    exact bernoulliMass_nonneg h0 h1


omit [DecidableEq α] in


lemma sum_bernoulliMass_eq_one (X : Finset α) {p : ℝ}
    (h : p + (1 - p) = 1) :
    (∑ S ∈ X.powerset, bernoulliMass X S p) = 1 := by
  classical
  
  have hsum :
      (∑ S ∈ X.powerset, p ^ S.card * (1 - p) ^ (X.card - S.card)) =
        ∑ k ∈ Finset.range (X.card + 1),
          (X.card.choose k : ℝ) * (p ^ k * (1 - p) ^ (X.card - k)) := by
    classical
    rw [Finset.sum_powerset_apply_card
      (f := fun k => p ^ k * (1 - p) ^ (X.card - k))]
    refine Finset.sum_congr rfl ?_
    intro k _
    rw [nsmul_eq_mul]
  unfold bernoulliMass
  rw [hsum]
  have hbinom : (p + (1 - p)) ^ X.card =
      ∑ k ∈ Finset.range (X.card + 1),
        p ^ k * (1 - p) ^ (X.card - k) * (X.card.choose k : ℝ) :=
    add_pow p (1 - p) X.card
  have : (p + (1 - p)) ^ X.card = 1 := by rw [h]; exact one_pow _
  rw [this] at hbinom
  
  have hreshape :
      (∑ k ∈ Finset.range (X.card + 1),
          (X.card.choose k : ℝ) * (p ^ k * (1 - p) ^ (X.card - k))) =
        (∑ k ∈ Finset.range (X.card + 1),
          p ^ k * (1 - p) ^ (X.card - k) * (X.card.choose k : ℝ)) := by
    refine Finset.sum_congr rfl ?_
    intro k _
    ring
  rw [hreshape, ← hbinom]




lemma upClosureIn_singleton (X T₀ : Finset α) (hT₀ : T₀ ⊆ X) :
    upClosureIn X {T₀} =
      X.powerset.filter (fun T => T₀ ⊆ T) := by
  classical
  ext T
  constructor
  · intro hT
    rcases mem_upClosureIn.mp hT with ⟨hTX, S, hS, hST⟩
    rcases Finset.mem_singleton.mp hS with rfl
    exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hTX, hST⟩
  · intro hT
    rcases Finset.mem_filter.mp hT with ⟨hTX, hT₀T⟩
    exact mem_upClosureIn.mpr ⟨Finset.mem_powerset.mp hTX, T₀,
      Finset.mem_singleton.mpr rfl, hT₀T⟩



theorem muP_upClosure_single (X T₀ : Finset α) (hT₀ : T₀ ⊆ X) {p : ℝ}
    (_h0 : 0 ≤ p) (_h1 : p ≤ 1) :
    muP X (upClosureIn X {T₀}) p = p ^ T₀.card := by
  classical
  
  
  
  set Y : Finset α := X \ T₀ with hY
  have hY_card : Y.card = X.card - T₀.card := by
    simp [hY, Finset.card_sdiff_of_subset hT₀]
  have hT₀_disj_Y : Disjoint T₀ Y := by
    simp [hY, Finset.disjoint_sdiff]
  
  let f : Finset α → Finset α := fun S' => T₀ ∪ S'
  have hf_inj : Set.InjOn f (↑Y.powerset) := by
    intro S' hS' R' hR' hfeq
    have hS'Y : S' ⊆ Y := Finset.mem_powerset.mp hS'
    have hR'Y : R' ⊆ Y := Finset.mem_powerset.mp hR'
    have hdisj_S' : Disjoint T₀ S' := Finset.disjoint_of_subset_right hS'Y hT₀_disj_Y
    have hdisj_R' : Disjoint T₀ R' := Finset.disjoint_of_subset_right hR'Y hT₀_disj_Y
    have heq : T₀ ∪ S' = T₀ ∪ R' := hfeq
    
    have hS'_eq : S' = (T₀ ∪ S') \ T₀ := by
      ext x
      constructor
      · intro hx
        refine Finset.mem_sdiff.mpr ⟨Finset.mem_union.mpr (Or.inr hx), ?_⟩
        exact fun hxT₀ => (Finset.disjoint_left.mp hdisj_S' hxT₀ hx).elim
      · intro hx
        rcases Finset.mem_sdiff.mp hx with ⟨hxun, hxnT₀⟩
        rcases Finset.mem_union.mp hxun with hxT₀ | hxS'
        · exact (hxnT₀ hxT₀).elim
        · exact hxS'
    have hR'_eq : R' = (T₀ ∪ R') \ T₀ := by
      ext x
      constructor
      · intro hx
        refine Finset.mem_sdiff.mpr ⟨Finset.mem_union.mpr (Or.inr hx), ?_⟩
        exact fun hxT₀ => (Finset.disjoint_left.mp hdisj_R' hxT₀ hx).elim
      · intro hx
        rcases Finset.mem_sdiff.mp hx with ⟨hxun, hxnT₀⟩
        rcases Finset.mem_union.mp hxun with hxT₀ | hxR'
        · exact (hxnT₀ hxT₀).elim
        · exact hxR'
    rw [hS'_eq, hR'_eq, heq]
  
  have him :
      Y.powerset.image f =
        X.powerset.filter (fun T => T ∈ upClosureIn X {T₀}) := by
    ext T
    simp only [Finset.mem_image, Finset.mem_powerset, Finset.mem_filter,
      mem_upClosureIn, Finset.mem_singleton]
    constructor
    · rintro ⟨S', hS'Y, rfl⟩
      have hS'X : S' ⊆ X := hS'Y.trans Finset.sdiff_subset
      have hfX : T₀ ∪ S' ⊆ X := Finset.union_subset hT₀ hS'X
      refine ⟨hfX, hfX, T₀, rfl, ?_⟩
      exact Finset.subset_union_left
    · rintro ⟨hTX, _, S₀, hS₀eq, hS₀T⟩
      refine ⟨T \ T₀, ?_, ?_⟩
      · intro x hx
        rcases Finset.mem_sdiff.mp hx with ⟨hxT, hxnT₀⟩
        exact Finset.mem_sdiff.mpr ⟨hTX hxT, hxnT₀⟩
      · 
        have hT₀T : T₀ ⊆ T := by
          have := hS₀T
          rw [hS₀eq] at this
          exact this
        change T₀ ∪ (T \ T₀) = T
        ext x
        constructor
        · intro hx
          rcases Finset.mem_union.mp hx with hxT₀ | hxd
          · exact hT₀T hxT₀
          · exact (Finset.mem_sdiff.mp hxd).1
        · intro hxT
          by_cases hxT₀ : x ∈ T₀
          · exact Finset.mem_union.mpr (Or.inl hxT₀)
          · exact Finset.mem_union.mpr (Or.inr (Finset.mem_sdiff.mpr ⟨hxT, hxT₀⟩))
  
  unfold muP
  rw [← him, Finset.sum_image hf_inj]
  
  
  
  have hkey :
      ∀ S' ∈ Y.powerset,
        bernoulliMass X (f S') p = p ^ T₀.card * bernoulliMass Y S' p := by
    intro S' hS'
    have hS'Y : S' ⊆ Y := Finset.mem_powerset.mp hS'
    have hdisj : Disjoint T₀ S' := Finset.disjoint_of_subset_right hS'Y hT₀_disj_Y
    have hcard : (T₀ ∪ S').card = T₀.card + S'.card :=
      Finset.card_union_of_disjoint hdisj
    have hsum_eq : X.card - (T₀.card + S'.card) = Y.card - S'.card := by
      rw [hY_card]; omega
    change p ^ (f S').card * (1 - p) ^ (X.card - (f S').card)
        = p ^ T₀.card * (p ^ S'.card * (1 - p) ^ (Y.card - S'.card))
    change p ^ (T₀ ∪ S').card * (1 - p) ^ (X.card - (T₀ ∪ S').card)
        = p ^ T₀.card * (p ^ S'.card * (1 - p) ^ (Y.card - S'.card))
    rw [hcard, hsum_eq, pow_add, mul_assoc]
  
  rw [Finset.sum_congr rfl hkey, ← Finset.mul_sum]
  have : (∑ S' ∈ Y.powerset, bernoulliMass Y S' p) = 1 :=
    sum_bernoulliMass_eq_one (α := α) Y (p := p) (by ring)
  rw [this, mul_one]


end

end ParkPham
end Erdos202














namespace Erdos920.Mixing

open scoped BigOperators

noncomputable section

variable {V : Type*} [Fintype V]


def restrictedDegree (R : V → V → Prop) [DecidableRel R]
    (B : Finset V) (x : V) : ℕ :=
  (B.filter (R x)).card



def orderedEdges (R : V → V → Prop) [DecidableRel R]
    (A B : Finset V) : ℕ :=
  ∑ x ∈ A, restrictedDegree R B x

lemma sum_restrictedDegree_univ
    (R : V → V → Prop) [DecidableRel R] (d : ℕ)
    (hsymm : ∀ ⦃x y⦄, R x y → R y x)
    (hdegree : ∀ x, (Finset.univ.filter (R x)).card = d)
    (B : Finset V) :
    ∑ x : V, restrictedDegree R B x = d * B.card := by
  classical
  simp_rw [restrictedDegree, Finset.card_filter]
  rw [Finset.sum_comm]
  calc
    (∑ y ∈ B, ∑ x : V, (if R x y then 1 else 0 : ℕ)) =
        ∑ y ∈ B, d := by
      apply Finset.sum_congr rfl
      intro y hy
      rw [← Finset.card_filter]
      have heq : (Finset.univ.filter fun x ↦ R x y) =
          Finset.univ.filter (R y) := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨(fun h ↦ hsymm h), (fun h ↦ hsymm h)⟩
      rw [heq, hdegree]
    _ = d * B.card := by simp [mul_comm]

lemma orderedEdges_univ_left
    (R : V → V → Prop) [DecidableRel R] (d : ℕ)
    (hsymm : ∀ ⦃x y⦄, R x y → R y x)
    (hdegree : ∀ x, (Finset.univ.filter (R x)).card = d)
    (B : Finset V) :
    orderedEdges R Finset.univ B = d * B.card := by
  simpa [orderedEdges] using sum_restrictedDegree_univ R d hsymm hdegree B

omit [Fintype V] in
lemma restrictedDegree_sq
    (R : V → V → Prop) [DecidableRel R] (B : Finset V) (x : V) :
    restrictedDegree R B x ^ 2 =
      ∑ y ∈ B, ∑ z ∈ B, if R x y ∧ R x z then 1 else 0 := by
  classical
  let C := B.filter (R x)
  calc
    restrictedDegree R B x ^ 2 = (C ×ˢ C).card := by
      simp [restrictedDegree, C, pow_two]
    _ = (((B ×ˢ B).filter fun yz ↦ R x yz.1 ∧ R x yz.2)).card := by
      congr 1
      ext yz
      simp only [Finset.mem_product, Finset.mem_filter, C]
      aesop
    _ = ∑ yz ∈ B ×ˢ B, if R x yz.1 ∧ R x yz.2 then 1 else 0 := by
      rw [Finset.card_filter]
    _ = ∑ y ∈ B, ∑ z ∈ B, if R x y ∧ R x z then 1 else 0 := by
      rw [Finset.sum_product]

omit [Fintype V] in
lemma sum_diagonal_offDiagonal [DecidableEq V] (B : Finset V) (d a : ℕ) :
    (∑ y ∈ B, ∑ z ∈ B, if y = z then d else a) =
      d * B.card + a * B.card * (B.card - 1) := by
  classical
  calc
    (∑ y ∈ B, ∑ z ∈ B, if y = z then d else a) =
        ∑ y ∈ B, (d + a * (B.card - 1)) := by
      apply Finset.sum_congr rfl
      intro y hy
      rw [← Finset.sum_erase_add _ _ hy]
      have hoff : (∑ z ∈ B.erase y, if y = z then d else a) =
          a * (B.card - 1) := by
        calc
          (∑ z ∈ B.erase y, if y = z then d else a) =
              ∑ _z ∈ B.erase y, a := by
            apply Finset.sum_congr rfl
            intro z hz
            rw [if_neg]
            exact Ne.symm (Finset.ne_of_mem_erase hz)
          _ = a * (B.card - 1) := by
            simp [Finset.card_erase_of_mem hy, mul_comm]
      rw [hoff, if_pos rfl, add_comm]
    _ = d * B.card + a * B.card * (B.card - 1) := by
      simp
      ring


lemma sum_restrictedDegree_sq
    (R : V → V → Prop) [DecidableRel R] (d a : ℕ)
    (hsymm : ∀ ⦃x y⦄, R x y → R y x)
    (hdegree : ∀ x, (Finset.univ.filter (R x)).card = d)
    (hcommon : ∀ x y, x ≠ y →
      (Finset.univ.filter fun z ↦ R x z ∧ R y z).card = a)
    (B : Finset V) :
    ∑ x : V, restrictedDegree R B x ^ 2 =
      d * B.card + a * B.card * (B.card - 1) := by
  classical
  simp_rw [restrictedDegree_sq]
  calc
    (∑ x : V, ∑ y ∈ B, ∑ z ∈ B,
        if R x y ∧ R x z then 1 else 0) =
        ∑ y ∈ B, ∑ z ∈ B, ∑ x : V,
          if R x y ∧ R x z then 1 else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro y hy
      rw [Finset.sum_comm]
    _ = ∑ y ∈ B, ∑ z ∈ B, if y = z then d else a := by
      apply Finset.sum_congr rfl
      intro y hy
      apply Finset.sum_congr rfl
      intro z hz
      rw [← Finset.card_filter]
      have heq : (Finset.univ.filter fun x ↦ R x y ∧ R x z) =
          Finset.univ.filter fun x ↦ R y x ∧ R z x := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact and_congr
          ⟨(fun h ↦ hsymm h), (fun h ↦ hsymm h)⟩
          ⟨(fun h ↦ hsymm h), (fun h ↦ hsymm h)⟩
      rw [heq]
      by_cases hyz : y = z
      · subst z
        simpa using hdegree y
      · simpa [hyz] using hcommon y z hyz
    _ = d * B.card + a * B.card * (B.card - 1) :=
      sum_diagonal_offDiagonal B d a




def scaledCenteredDegree (R : V → V → Prop) [DecidableRel R]
    (d : ℕ) (B : Finset V) (x : V) : ℝ :=
  (Fintype.card V : ℝ) * restrictedDegree R B x -
    (d : ℝ) * B.card



lemma sum_scaledCenteredDegree
    (R : V → V → Prop) [DecidableRel R] (d : ℕ) (A B : Finset V) :
    ∑ x ∈ A, scaledCenteredDegree R d B x =
      (Fintype.card V : ℝ) * orderedEdges R A B -
        (d : ℝ) * A.card * B.card := by
  classical
  simp only [scaledCenteredDegree, orderedEdges, Nat.cast_sum,
    Finset.sum_sub_distrib, Finset.mul_sum]
  simp
  ring



lemma orderedEdges_deviation_sq_le_card_mul_sum
    (R : V → V → Prop) [DecidableRel R] (d : ℕ) (A B : Finset V) :
    ((Fintype.card V : ℝ) * orderedEdges R A B -
        (d : ℝ) * A.card * B.card) ^ 2 ≤
      (A.card : ℝ) * ∑ x : V, (scaledCenteredDegree R d B x) ^ 2 := by
  classical
  have hc := sq_sum_le_card_mul_sum_sq
    (s := A) (f := fun x ↦ scaledCenteredDegree R d B x)
  have hsub :
      (∑ x ∈ A, (scaledCenteredDegree R d B x) ^ 2) ≤
        ∑ x : V, (scaledCenteredDegree R d B x) ^ 2 := by
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ A)
      (fun _ _ _ ↦ sq_nonneg _)
  rw [sum_scaledCenteredDegree] at hc
  exact hc.trans (mul_le_mul_of_nonneg_left hsub (Nat.cast_nonneg A.card))




lemma sum_scaledCenteredDegree_sq
    (R : V → V → Prop) [DecidableRel R] (d a : ℕ)
    (hsymm : ∀ ⦃x y⦄, R x y → R y x)
    (hdegree : ∀ x, (Finset.univ.filter (R x)).card = d)
    (hcommon : ∀ x y, x ≠ y →
      (Finset.univ.filter fun z ↦ R x z ∧ R y z).card = a)
    (B : Finset V) :
    ∑ x : V, (scaledCenteredDegree R d B x) ^ 2 =
      (Fintype.card V : ℝ) ^ 2 *
          (d * B.card + a * B.card * (B.card - 1) : ℕ) -
        (Fintype.card V : ℝ) * (d * B.card : ℕ) ^ 2 := by
  classical
  have hfirst :
      (∑ x : V, (restrictedDegree R B x : ℝ)) = (d * B.card : ℕ) := by
    exact_mod_cast sum_restrictedDegree_univ R d hsymm hdegree B
  have hsecond :
      (∑ x : V, (restrictedDegree R B x : ℝ) ^ 2) =
        (d * B.card + a * B.card * (B.card - 1) : ℕ) := by
    exact_mod_cast sum_restrictedDegree_sq R d a hsymm hdegree hcommon B
  calc
    (∑ x : V, (scaledCenteredDegree R d B x) ^ 2) =
        ∑ x : V,
          ((Fintype.card V : ℝ) ^ 2 * (restrictedDegree R B x : ℝ) ^ 2 -
            2 * (Fintype.card V : ℝ) * (d * B.card : ℕ) *
              restrictedDegree R B x +
            ((d * B.card : ℕ) : ℝ) ^ 2) := by
      apply Finset.sum_congr rfl
      intro x hx
      simp only [scaledCenteredDegree]
      push_cast
      ring
    _ = (Fintype.card V : ℝ) ^ 2 *
          (∑ x : V, (restrictedDegree R B x : ℝ) ^ 2) -
        2 * (Fintype.card V : ℝ) * (d * B.card : ℕ) *
          (∑ x : V, (restrictedDegree R B x : ℝ)) +
        (Fintype.card V : ℝ) * ((d * B.card : ℕ) : ℝ) ^ 2 := by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
        ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ = (Fintype.card V : ℝ) ^ 2 *
          (d * B.card + a * B.card * (B.card - 1) : ℕ) -
        (Fintype.card V : ℝ) * (d * B.card : ℕ) ^ 2 := by
      rw [hfirst, hsecond]
      push_cast
      ring



theorem orderedEdges_deviation_sq_le
    (R : V → V → Prop) [DecidableRel R] (d a : ℕ)
    (hsymm : ∀ ⦃x y⦄, R x y → R y x)
    (hdegree : ∀ x, (Finset.univ.filter (R x)).card = d)
    (hcommon : ∀ x y, x ≠ y →
      (Finset.univ.filter fun z ↦ R x z ∧ R y z).card = a)
    (A B : Finset V) :
    ((Fintype.card V : ℝ) * orderedEdges R A B -
        (d : ℝ) * A.card * B.card) ^ 2 ≤
      (A.card : ℝ) *
        ((Fintype.card V : ℝ) ^ 2 *
            (d * B.card + a * B.card * (B.card - 1) : ℕ) -
          (Fintype.card V : ℝ) * (d * B.card : ℕ) ^ 2) := by
  rw [← sum_scaledCenteredDegree_sq R d a hsymm hdegree hcommon B]
  exact orderedEdges_deviation_sq_le_card_mul_sum R d A B



lemma parameter_identity [Nonempty V]
    (R : V → V → Prop) [DecidableRel R] (d a : ℕ)
    (hsymm : ∀ ⦃x y⦄, R x y → R y x)
    (hdegree : ∀ x, (Finset.univ.filter (R x)).card = d)
    (hcommon : ∀ x y, x ≠ y →
      (Finset.univ.filter fun z ↦ R x z ∧ R y z).card = a) :
    d ^ 2 = d + a * (Fintype.card V - 1) := by
  have hm := sum_restrictedDegree_sq R d a hsymm hdegree hcommon
    (Finset.univ : Finset V)
  have hdres : ∀ x, restrictedDegree R (Finset.univ : Finset V) x = d := by
    intro x
    exact hdegree x
  simp_rw [hdres] at hm
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hm
  have hmul : Fintype.card V * d ^ 2 =
      Fintype.card V * (d + a * (Fintype.card V - 1)) := by
    nlinarith
  exact Nat.eq_of_mul_eq_mul_left Fintype.card_pos hmul



lemma sum_scaledCenteredDegree_sq_design [Nonempty V]
    (R : V → V → Prop) [DecidableRel R] (d a : ℕ)
    (hsymm : ∀ ⦃x y⦄, R x y → R y x)
    (hdegree : ∀ x, (Finset.univ.filter (R x)).card = d)
    (hcommon : ∀ x y, x ≠ y →
      (Finset.univ.filter fun z ↦ R x z ∧ R y z).card = a)
    (B : Finset V) :
    ∑ x : V, (scaledCenteredDegree R d B x) ^ 2 =
      (Fintype.card V : ℝ) * ((d : ℝ) - a) * B.card *
        ((Fintype.card V : ℝ) - B.card) := by
  rw [sum_scaledCenteredDegree_sq R d a hsymm hdegree hcommon B]
  have hp := parameter_identity R d a hsymm hdegree hcommon
  have hN : 1 ≤ Fintype.card V := Fintype.card_pos
  by_cases hB : B = ∅
  · simp [hB]
  · have hb : 1 ≤ B.card := (Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hB))
    have hpR : ((d ^ 2 : ℕ) : ℝ) =
        ((d + a * (Fintype.card V - 1) : ℕ) : ℝ) := congrArg _ hp
    push_cast [Nat.cast_sub hN, Nat.cast_sub hb] at hpR ⊢
    linear_combination -(Fintype.card V : ℝ) * (B.card : ℝ) ^ 2 * hpR



theorem scaled_orderedEdges_deviation_sq_le [Nonempty V]
    (R : V → V → Prop) [DecidableRel R] (d a : ℕ)
    (hsymm : ∀ ⦃x y⦄, R x y → R y x)
    (hdegree : ∀ x, (Finset.univ.filter (R x)).card = d)
    (hcommon : ∀ x y, x ≠ y →
      (Finset.univ.filter fun z ↦ R x z ∧ R y z).card = a)
    (ha : a ≤ d) (A B : Finset V) :
    ((Fintype.card V : ℝ) * orderedEdges R A B -
        (d : ℝ) * A.card * B.card) ^ 2 ≤
      (Fintype.card V : ℝ) ^ 2 * ((d : ℝ) - a) * A.card * B.card := by
  have hbase := orderedEdges_deviation_sq_le_card_mul_sum R d A B
  rw [sum_scaledCenteredDegree_sq_design R d a hsymm hdegree hcommon B] at hbase
  have hgap : (Fintype.card V : ℝ) - B.card ≤ Fintype.card V := by
    exact sub_le_self _ (Nat.cast_nonneg B.card)
  have haR : (a : ℝ) ≤ d := by exact_mod_cast ha
  have hcoef : 0 ≤
      (A.card : ℝ) * (Fintype.card V : ℝ) * ((d : ℝ) - a) * B.card := by
    positivity
  calc
    ((Fintype.card V : ℝ) * orderedEdges R A B -
        (d : ℝ) * A.card * B.card) ^ 2 ≤
        (A.card : ℝ) * ((Fintype.card V : ℝ) * ((d : ℝ) - a) *
          B.card * ((Fintype.card V : ℝ) - B.card)) := hbase
    _ ≤ (Fintype.card V : ℝ) ^ 2 * ((d : ℝ) - a) * A.card * B.card := by
      have := mul_le_mul_of_nonneg_left hgap hcoef
      nlinarith


theorem orderedEdges_normalized_deviation_sq_le [Nonempty V]
    (R : V → V → Prop) [DecidableRel R] (d a : ℕ)
    (hsymm : ∀ ⦃x y⦄, R x y → R y x)
    (hdegree : ∀ x, (Finset.univ.filter (R x)).card = d)
    (hcommon : ∀ x y, x ≠ y →
      (Finset.univ.filter fun z ↦ R x z ∧ R y z).card = a)
    (ha : a ≤ d) (A B : Finset V) :
    ((orderedEdges R A B : ℝ) -
        (d : ℝ) / Fintype.card V * A.card * B.card) ^ 2 ≤
      ((d : ℝ) - a) * A.card * B.card := by
  have hclear := scaled_orderedEdges_deviation_sq_le
    R d a hsymm hdegree hcommon ha A B
  have hN : (0 : ℝ) < Fintype.card V := by
    exact_mod_cast Fintype.card_pos
  let z : ℝ := (orderedEdges R A B : ℝ) -
    (d : ℝ) / Fintype.card V * A.card * B.card
  let C : ℝ := ((d : ℝ) - a) * A.card * B.card
  have hscale :
      (Fintype.card V : ℝ) * orderedEdges R A B -
          (d : ℝ) * A.card * B.card =
        (Fintype.card V : ℝ) * z := by
    dsimp [z]
    field_simp
  rw [hscale] at hclear
  have hscaled : (Fintype.card V : ℝ) ^ 2 * z ^ 2 ≤
      (Fintype.card V : ℝ) ^ 2 * C := by
    dsimp [C]
    convert hclear using 1 <;> ring
  have hz := le_of_mul_le_mul_left hscaled (sq_pos_of_pos hN)
  simpa [z, C] using hz



theorem abs_orderedEdges_sub_expected_le [Nonempty V]
    (R : V → V → Prop) [DecidableRel R] (d a : ℕ)
    (hsymm : ∀ ⦃x y⦄, R x y → R y x)
    (hdegree : ∀ x, (Finset.univ.filter (R x)).card = d)
    (hcommon : ∀ x y, x ≠ y →
      (Finset.univ.filter fun z ↦ R x z ∧ R y z).card = a)
    (ha : a ≤ d) (A B : Finset V) :
    |(orderedEdges R A B : ℝ) -
        (d : ℝ) / Fintype.card V * A.card * B.card| ≤
      Real.sqrt (((d : ℝ) - a) * A.card * B.card) := by
  apply Real.abs_le_sqrt
  exact orderedEdges_normalized_deviation_sq_le
    R d a hsymm hdegree hcommon ha A B

omit [Fintype V] in

lemma mul_orderedEdges_le_card_mul_of_pointwise
    (R : V → V → Prop) [DecidableRel R] (c : ℕ) (A B : Finset V)
    (h : ∀ x ∈ A, c * restrictedDegree R B x ≤ B.card) :
    c * orderedEdges R A B ≤ A.card * B.card := by
  classical
  rw [orderedEdges, Finset.mul_sum]
  calc
    (∑ x ∈ A, c * restrictedDegree R B x) ≤
        ∑ _x ∈ A, B.card := by
      exact Finset.sum_le_sum fun x hx ↦ h x hx
    _ = A.card * B.card := by simp





theorem card_mul_le_of_sparse_orderedEdges [Nonempty V]
    (R : V → V → Prop) [DecidableRel R] (d a : ℕ)
    (hsymm : ∀ ⦃x y⦄, R x y → R y x)
    (hdegree : ∀ x, (Finset.univ.filter (R x)).card = d)
    (hcommon : ∀ x y, x ≠ y →
      (Finset.univ.filter fun z ↦ R x z ∧ R y z).card = a)
    (ha : a ≤ d) (A B : Finset V) (Q L : ℝ)
    (hQ : 0 < Q) (hL : 0 ≤ L)
    (hNd : (Fintype.card V : ℝ) ≤ 2 * Q * d)
    (hvar : (d : ℝ) - a ≤ L)
    (hsparse : 8 * Q * orderedEdges R A B ≤
      (A.card : ℝ) * B.card) :
    (A.card : ℝ) * B.card ≤ 256 * Q ^ 2 * L := by
  have hN : (0 : ℝ) < Fintype.card V := by
    exact_mod_cast Fintype.card_pos
  let X : ℝ := (A.card : ℝ) * B.card
  let E : ℝ := orderedEdges R A B
  let D : ℝ := (d : ℝ) / Fintype.card V * A.card * B.card
  have hX : 0 ≤ X := by positivity
  have hdensity : (1 : ℝ) / (2 * Q) ≤ (d : ℝ) / Fintype.card V := by
    rw [div_le_div_iff₀ (mul_pos (by norm_num) hQ) hN]
    simpa [mul_assoc, mul_comm, mul_left_comm] using hNd
  have hExpected : X / (2 * Q) ≤ D := by
    dsimp [D, X]
    have := mul_le_mul_of_nonneg_right hdensity
      (mul_nonneg (Nat.cast_nonneg A.card) (Nat.cast_nonneg B.card))
    simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using this
  have hEdge : E ≤ X / (8 * Q) := by
    rw [le_div_iff₀ (mul_pos (by norm_num) hQ)]
    dsimp [E, X]
    nlinarith
  have hquarter : X / (4 * Q) ≤ D - E := by
    have htwo : X / (2 * Q) = 2 * (X / (4 * Q)) := by
      field_simp [ne_of_gt hQ]
      ring
    have height : X / (8 * Q) = (X / (4 * Q)) / 2 := by
      field_simp [ne_of_gt hQ]
      ring
    nlinarith [hExpected, hEdge]
  have hquarter_nonneg : 0 ≤ X / (4 * Q) := by positivity
  have hDE_nonneg : 0 ≤ D - E := hquarter_nonneg.trans hquarter
  have hsquare : (X / (4 * Q)) ^ 2 ≤ (E - D) ^ 2 := by
    have hs := (sq_le_sq₀ hquarter_nonneg hDE_nonneg).2 hquarter
    nlinarith
  have hmix := orderedEdges_normalized_deviation_sq_le
    R d a hsymm hdegree hcommon ha A B
  have hmix' : (E - D) ^ 2 ≤ L * X := by
    have hv := mul_le_mul_of_nonneg_right hvar hX
    dsimp [X] at hv
    dsimp [E, D, X]
    have hv' : ((d : ℝ) - a) * A.card * B.card ≤
        L * (A.card * B.card) := by
      simpa [mul_assoc] using hv
    exact hmix.trans hv'
  have hboth : (X / (4 * Q)) ^ 2 ≤ L * X := hsquare.trans hmix'
  by_cases hXzero : X = 0
  · change X ≤ 256 * Q ^ 2 * L
    rw [hXzero]
    positivity
  · have hXpos : 0 < X := lt_of_le_of_ne hX (Ne.symm hXzero)
    have hpoly : X * X ≤ X * (16 * Q ^ 2 * L) := by
      have hscale_nonneg : 0 ≤ (4 * Q) ^ 2 := sq_nonneg _
      have hs := mul_le_mul_of_nonneg_left hboth hscale_nonneg
      calc
        X * X = (4 * Q) ^ 2 * (X / (4 * Q)) ^ 2 := by
          field_simp [ne_of_gt hQ]
        _ ≤ (4 * Q) ^ 2 * (L * X) := hs
        _ = X * (16 * Q ^ 2 * L) := by ring
    have hsmall : X ≤ 16 * Q ^ 2 * L :=
      le_of_mul_le_mul_left hpoly hXpos
    calc
      X ≤ 16 * Q ^ 2 * L := hsmall
      _ ≤ 256 * Q ^ 2 * L := by
        have : 0 ≤ Q ^ 2 * L := mul_nonneg (sq_nonneg Q) hL
        nlinarith

end

end Erdos920.Mixing













namespace Erdos920.Projective

open scoped BigOperators LinearAlgebra.Projectivization

noncomputable section


theorem pow_pred_le_geomSum (q d : ℕ) (hd : 1 ≤ d) :
    q ^ (d - 1) ≤ ∑ i ∈ Finset.range d, q ^ i := by
  apply Finset.single_le_sum
  · intro i hi
    exact Nat.zero_le _
  · simp only [Finset.mem_range]
    omega



theorem geomSum_le_two_mul_pow_pred (q d : ℕ) (hq : 2 ≤ q) :
    (∑ i ∈ Finset.range d, q ^ i) ≤ 2 * q ^ (d - 1) := by
  induction d with
  | zero => simp
  | succ d ih =>
      cases d with
      | zero => simp
      | succ n =>
          rw [Finset.sum_range_succ]
          have hstep : 2 * q ^ n ≤ q ^ (n + 1) := by
            calc
              2 * q ^ n ≤ q * q ^ n := Nat.mul_le_mul_right (q ^ n) hq
              _ = q ^ (n + 1) := by rw [pow_succ, Nat.mul_comm]
          have ih' : (∑ i ∈ Finset.range (n + 1), q ^ i) ≤ 2 * q ^ n := by
            simpa using ih
          have hold : (∑ i ∈ Finset.range (n + 1), q ^ i) ≤ q ^ (n + 1) :=
            ih'.trans hstep
          simp only [Nat.add_sub_cancel]
          omega


theorem geomSum_mono (q : ℕ) {a b : ℕ} (hab : a ≤ b) :
    (∑ i ∈ Finset.range a, q ^ i) ≤ ∑ i ∈ Finset.range b, q ^ i :=
  Finset.sum_le_sum_of_subset (Finset.range_mono hab)


abbrev Point (F : Type*) [Field F] (d : ℕ) := ℙ F (Fin d → F)


abbrev Orthogonal {F : Type*} [Field F] {d : ℕ} :
    Point F d → Point F d → Prop :=
  Projectivization.orthogonal

lemma orthogonal_comm {F : Type*} [Field F] {d : ℕ} (x y : Point F d) :
    Orthogonal x y ↔ Orthogonal y x :=
  Projectivization.orthogonal_comm


instance pointFinite (F : Type*) [Field F] [Finite F] (d : ℕ) :
    Finite (Point F d) := inferInstance



theorem natCard_point (F : Type*) [Field F] [Finite F] (d : ℕ) :
    Nat.card (Point F d) = ∑ i ∈ Finset.range d, Nat.card F ^ i := by
  apply Projectivization.card_of_finrank
  exact Module.finrank_fin_fun F


theorem natCard_point_zmod (q d : ℕ) [Fact q.Prime] :
    Nat.card (Point (ZMod q) d) = ∑ i ∈ Finset.range d, q ^ i := by
  simpa [Nat.card_zmod] using natCard_point (ZMod q) d


theorem pow_pred_le_natCard_point_zmod (q d : ℕ) [Fact q.Prime]
    (hd : 1 ≤ d) :
    q ^ (d - 1) ≤ Nat.card (Point (ZMod q) d) := by
  rw [natCard_point_zmod]
  exact pow_pred_le_geomSum q d hd


theorem natCard_point_zmod_le_two_mul_pow_pred (q d : ℕ) [Fact q.Prime] :
    Nat.card (Point (ZMod q) d) ≤ 2 * q ^ (d - 1) := by
  rw [natCard_point_zmod]
  exact geomSum_le_two_mul_pow_pred q d (Fact.out : q.Prime).two_le



theorem point_zmod_bounds (q t : ℕ) [Fact q.Prime] :
    q ^ t ≤ Nat.card (Point (ZMod q) (t + 1)) ∧
      Nat.card (Point (ZMod q) (t + 1)) ≤ 2 * q ^ t := by
  constructor
  · simpa using pow_pred_le_natCard_point_zmod q (t + 1) (by omega)
  · simpa using natCard_point_zmod_le_two_mul_pow_pred q (t + 1)



def dotFunctional {F : Type*} [Field F] {d : ℕ} (x : Point F d) :
    (Fin d → F) →ₗ[F] F :=
  (dotProductBilin F F) x.rep

@[simp] lemma dotFunctional_apply {F : Type*} [Field F] {d : ℕ}
    (x : Point F d) (v : Fin d → F) :
    dotFunctional x v = x.rep ⬝ᵥ v := rfl


def orthSpace {F : Type*} [Field F] {d : ℕ} (x : Point F d) :
    Submodule F (Fin d → F) :=
  LinearMap.ker (dotFunctional x)

@[simp] lemma mem_orthSpace_iff {F : Type*} [Field F] {d : ℕ}
    (x : Point F d) (v : Fin d → F) :
    v ∈ orthSpace x ↔ x.rep ⬝ᵥ v = 0 := by
  rfl


theorem dotFunctional_ne_zero {F : Type*} [Field F] {d : ℕ} (x : Point F d) :
    dotFunctional x ≠ 0 := by
  intro h
  have hz : ∀ v : Fin d → F, x.rep ⬝ᵥ v = 0 := by
    intro v
    have := LinearMap.congr_fun h v
    simpa using this
  exact x.rep_nonzero (dotProduct_eq_zero x.rep hz)



theorem finrank_orthSpace_add_one {F : Type*} [Field F] {d : ℕ}
    (x : Point F d) :
    Module.finrank F (orthSpace x) + 1 = d := by
  calc
    Module.finrank F (orthSpace x) + 1 = Module.finrank F (Fin d → F) :=
      Module.Dual.finrank_ker_add_one_of_ne_zero (dotFunctional_ne_zero x)
    _ = d := Module.finrank_fin_fun F


theorem finrank_orthSpace {F : Type*} [Field F] {d : ℕ}
    (x : Point F d) :
    Module.finrank F (orthSpace x) = d - 1 := by
  have h := finrank_orthSpace_add_one x
  omega



theorem orthSpace_injective {F : Type*} [Field F] {d : ℕ} :
    Function.Injective (orthSpace : Point F d → Submodule F (Fin d → F)) := by
  intro x y hker
  obtain ⟨v, hfv⟩ : ∃ v : Fin d → F, dotFunctional x v ≠ 0 := by
    by_contra h
    push Not at h
    apply dotFunctional_ne_zero x
    apply LinearMap.ext
    intro w
    simpa using h w
  have hgv : dotFunctional y v ≠ 0 := by
    intro hzero
    have hvy : v ∈ orthSpace y := hzero
    have hvx : v ∈ orthSpace x := by rwa [hker]
    exact hfv hvx
  let c : F := dotFunctional x v / dotFunctional y v
  have hc : c ≠ 0 := div_ne_zero hfv hgv
  have hker' : LinearMap.ker (dotFunctional x) =
      LinearMap.ker (c • dotFunctional y) := by
    calc
      LinearMap.ker (dotFunctional x) = LinearMap.ker (dotFunctional y) := hker
      _ = LinearMap.ker (c • dotFunctional y) :=
        (LinearMap.ker_smul (dotFunctional y) c hc).symm
  have happ : dotFunctional x v = (c • dotFunctional y) v := by
    rw [LinearMap.smul_apply]
    change dotFunctional x v = c * dotFunctional y v
    exact (div_mul_cancel₀ (dotFunctional x v) hgv).symm
  have hfun : dotFunctional x = c • dotFunctional y :=
    Module.Dual.eq_of_ker_eq_of_apply_eq v hker' happ hfv
  have hrep : x.rep = c • y.rep := by
    apply dotProduct_eq
    intro w
    have hw := LinearMap.congr_fun hfun w
    simpa [dotFunctional, smul_dotProduct] using hw
  rw [← x.mk_rep, ← y.mk_rep, Projectivization.mk_eq_mk_iff']
  exact ⟨c, hrep.symm⟩



theorem orthogonal_iff_submodule_le {F : Type*} [Field F] {d : ℕ}
    (x y : Point F d) :
    Orthogonal x y ↔ y.submodule ≤ orthSpace x := by
  rw [Projectivization.submodule_eq, Submodule.span_singleton_le_iff_mem,
    mem_orthSpace_iff]
  conv_lhs =>
    rw [← x.mk_rep, ← y.mk_rep]
  exact Projectivization.orthogonal_mk x.rep_nonzero y.rep_nonzero

section ProjectivizeSubmodule

variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]



def projectivizeInclusion (S : Submodule F V) : ℙ F S → ℙ F V :=
  Projectivization.map S.subtype S.injective_subtype

theorem projectivizeInclusion_injective (S : Submodule F V) :
    Function.Injective (projectivizeInclusion S) :=
  Projectivization.map_injective S.subtype S.injective_subtype



theorem mem_range_projectivizeInclusion_iff (S : Submodule F V) (p : ℙ F V) :
    p ∈ Set.range (projectivizeInclusion S) ↔ p.submodule ≤ S := by
  constructor
  · rintro ⟨z, rfl⟩
    induction z using Projectivization.ind with
    | h v hv =>
        rw [projectivizeInclusion, Projectivization.map_mk,
          Projectivization.submodule_mk, Submodule.span_singleton_le_iff_mem]
        exact v.property
  · intro hp
    have hrep : p.rep ∈ S := by
      apply hp
      rw [Projectivization.submodule_eq]
      exact Submodule.mem_span_singleton_self p.rep
    let v : S := ⟨p.rep, hrep⟩
    have hv : v ≠ 0 := by
      intro h
      exact p.rep_nonzero (congr_arg Subtype.val h)
    refine ⟨Projectivization.mk F v hv, ?_⟩
    rw [projectivizeInclusion, Projectivization.map_mk]
    exact p.mk_rep



def pointsInEquiv (S : Submodule F V) :
    ℙ F S ≃ {p : ℙ F V // p.submodule ≤ S} :=
  (Equiv.ofInjective (projectivizeInclusion S)
      (projectivizeInclusion_injective S)).trans
    (Equiv.setCongr (Set.ext fun p ↦ mem_range_projectivizeInclusion_iff S p))



theorem natCard_pointsIn [Finite F] [Finite V] (S : Submodule F V) :
    Nat.card {p : ℙ F V // p.submodule ≤ S} =
      ∑ i ∈ Finset.range (Module.finrank F S), Nat.card F ^ i := by
  calc
    Nat.card {p : ℙ F V // p.submodule ≤ S} = Nat.card (ℙ F S) :=
      Nat.card_congr (pointsInEquiv S).symm
    _ = ∑ i ∈ Finset.range (Module.finrank F S), Nat.card F ^ i :=
      Projectivization.card_of_finrank F S rfl



theorem pow_pred_le_natCard_pointsIn_zmod
    {q : ℕ} [Fact q.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod q) V]
    [Finite V] (S : Submodule (ZMod q) V) (hS : 1 ≤ Module.finrank (ZMod q) S) :
    q ^ (Module.finrank (ZMod q) S - 1) ≤
      Nat.card {p : ℙ (ZMod q) V // p.submodule ≤ S} := by
  rw [natCard_pointsIn]
  simpa [Nat.card_zmod] using
    pow_pred_le_geomSum q (Module.finrank (ZMod q) S) hS



theorem natCard_pointsIn_zmod_le_two_mul_pow_pred
    {q : ℕ} [Fact q.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod q) V]
    [Finite V] (S : Submodule (ZMod q) V) :
    Nat.card {p : ℙ (ZMod q) V // p.submodule ≤ S} ≤
      2 * q ^ (Module.finrank (ZMod q) S - 1) := by
  rw [natCard_pointsIn]
  simpa [Nat.card_zmod] using geomSum_le_two_mul_pow_pred q
    (Module.finrank (ZMod q) S) (Fact.out : q.Prime).two_le


theorem natCard_pointsIn_eq_zero_of_finrank_eq_zero
    {F V : Type*} [Field F] [Finite F] [AddCommGroup V] [Module F V] [Finite V]
    (S : Submodule F V) (hS : Module.finrank F S = 0) :
    Nat.card {p : ℙ F V // p.submodule ≤ S} = 0 := by
  rw [natCard_pointsIn, hS]
  simp


theorem natCard_pointsIn_eq_one_of_finrank_eq_one
    {F V : Type*} [Field F] [Finite F] [AddCommGroup V] [Module F V] [Finite V]
    (S : Submodule F V) (hS : Module.finrank F S = 1) :
    Nat.card {p : ℙ F V // p.submodule ≤ S} = 1 := by
  rw [natCard_pointsIn, hS]
  simp

end ProjectivizeSubmodule




abbrev Neighbors {F : Type*} [Field F] {d : ℕ} (x : Point F d) :=
  {y : Point F d // Orthogonal x y}


def neighborsEquiv {F : Type*} [Field F] {d : ℕ} (x : Point F d) :
    ℙ F (orthSpace x) ≃ Neighbors x :=
  (pointsInEquiv (orthSpace x)).trans
    (Equiv.setCongr (Set.ext fun y ↦ (orthogonal_iff_submodule_le x y).symm))


theorem natCard_neighbors {F : Type*} [Field F] [Finite F] {d : ℕ}
    (x : Point F d) :
    Nat.card (Neighbors x) =
      ∑ i ∈ Finset.range (d - 1), Nat.card F ^ i := by
  calc
    Nat.card (Neighbors x) = Nat.card (ℙ F (orthSpace x)) :=
      Nat.card_congr (neighborsEquiv x).symm
    _ = ∑ i ∈ Finset.range (d - 1), Nat.card F ^ i := by
      apply Projectivization.card_of_finrank
      exact finrank_orthSpace x


theorem natCard_neighbors_zmod (q : ℕ) [Fact q.Prime] {d : ℕ}
    (x : Point (ZMod q) d) :
    Nat.card (Neighbors x) = ∑ i ∈ Finset.range (d - 1), q ^ i := by
  simpa [Nat.card_zmod] using natCard_neighbors x


theorem neighbor_zmod_bounds (q : ℕ) [Fact q.Prime] {t : ℕ} (ht : 1 ≤ t)
    (x : Point (ZMod q) (t + 1)) :
    q ^ (t - 1) ≤ Nat.card (Neighbors x) ∧
      Nat.card (Neighbors x) ≤ 2 * q ^ (t - 1) := by
  rw [natCard_neighbors_zmod]
  have hdim : t + 1 - 1 = t := by omega
  rw [hdim]
  exact ⟨pow_pred_le_geomSum q t ht,
    geomSum_le_two_mul_pow_pred q t (Fact.out : q.Prime).two_le⟩


def commonOrthSpace {F : Type*} [Field F] {d : ℕ} (x y : Point F d) :
    Submodule F (Fin d → F) :=
  orthSpace x ⊓ orthSpace y


abbrev CommonNeighbors {F : Type*} [Field F] {d : ℕ} (x y : Point F d) :=
  {z : Point F d // Orthogonal x z ∧ Orthogonal y z}



def commonNeighborsEquiv {F : Type*} [Field F] {d : ℕ} (x y : Point F d) :
    ℙ F (commonOrthSpace x y) ≃ CommonNeighbors x y :=
  (pointsInEquiv (commonOrthSpace x y)).trans
    (Equiv.setCongr (Set.ext fun z ↦ by
      change z.submodule ≤ orthSpace x ⊓ orthSpace y ↔
        Orthogonal x z ∧ Orthogonal y z
      rw [le_inf_iff, ← orthogonal_iff_submodule_le x z,
        ← orthogonal_iff_submodule_le y z]))


theorem sup_orthSpace_eq_top {F : Type*} [Field F] {d : ℕ}
    {x y : Point F d} (hxy : x ≠ y) :
    orthSpace x ⊔ orthSpace y = ⊤ := by
  have hne : orthSpace x ≠ orthSpace y := by
    intro h
    exact hxy (orthSpace_injective h)
  have hnotle : ¬ orthSpace y ≤ orthSpace x := by
    intro hle
    apply hne
    symm
    apply Submodule.eq_of_le_of_finrank_eq hle
    rw [finrank_orthSpace y, finrank_orthSpace x]
  have hlt : orthSpace x < orthSpace x ⊔ orthSpace y := by
    apply lt_of_le_of_ne le_sup_left
    intro heq
    apply hnotle
    rw [heq]
    exact le_sup_right
  have hrank_lt := Submodule.finrank_lt_finrank_of_lt hlt
  have hrank_le := Submodule.finrank_le (orthSpace x ⊔ orthSpace y)
  have hrank_eq : Module.finrank F ↑(orthSpace x ⊔ orthSpace y) = d := by
    rw [finrank_orthSpace x] at hrank_lt
    rw [Module.finrank_fin_fun] at hrank_le
    omega
  apply Submodule.eq_top_of_finrank_eq
  simpa [Module.finrank_fin_fun] using hrank_eq


theorem finrank_commonOrthSpace {F : Type*} [Field F] {d : ℕ}
    {x y : Point F d} (hxy : x ≠ y) :
    Module.finrank F (commonOrthSpace x y) = d - 2 := by
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq
    (orthSpace x) (orthSpace y)
  have htop : Module.finrank F (⊤ : Submodule F (Fin d → F)) = d := by
    rw [finrank_top, Module.finrank_fin_fun]
  rw [sup_orthSpace_eq_top hxy, htop,
    finrank_orthSpace x, finrank_orthSpace y] at hdim
  change Module.finrank F ↑(orthSpace x ⊓ orthSpace y) = d - 2
  omega



theorem natCard_commonNeighbors {F : Type*} [Field F] [Finite F] {d : ℕ}
    {x y : Point F d} (hxy : x ≠ y) :
    Nat.card (CommonNeighbors x y) =
      ∑ i ∈ Finset.range (d - 2), Nat.card F ^ i := by
  calc
    Nat.card (CommonNeighbors x y) = Nat.card (ℙ F (commonOrthSpace x y)) :=
      Nat.card_congr (commonNeighborsEquiv x y).symm
    _ = ∑ i ∈ Finset.range (d - 2), Nat.card F ^ i := by
      apply Projectivization.card_of_finrank
      exact finrank_commonOrthSpace hxy


theorem natCard_commonNeighbors_zmod (q : ℕ) [Fact q.Prime] {d : ℕ}
    {x y : Point (ZMod q) d} (hxy : x ≠ y) :
    Nat.card (CommonNeighbors x y) =
      ∑ i ∈ Finset.range (d - 2), q ^ i := by
  simpa [Nat.card_zmod] using natCard_commonNeighbors hxy


theorem commonNeighbor_zmod_bounds (q : ℕ) [Fact q.Prime] {t : ℕ}
    (ht : 2 ≤ t) {x y : Point (ZMod q) (t + 1)} (hxy : x ≠ y) :
    q ^ (t - 2) ≤ Nat.card (CommonNeighbors x y) ∧
      Nat.card (CommonNeighbors x y) ≤ 2 * q ^ (t - 2) := by
  rw [natCard_commonNeighbors_zmod q hxy]
  have hdim : t + 1 - 2 = t - 1 := by omega
  have hpred : t - 1 - 1 = t - 2 := by omega
  rw [hdim]
  constructor
  · simpa [hpred] using pow_pred_le_geomSum q (t - 1) (by omega)
  · simpa [hpred] using geomSum_le_two_mul_pow_pred q (t - 1)
      (Fact.out : q.Prime).two_le


theorem natCard_commonNeighbors_zmod_le (q : ℕ) [Fact q.Prime] {t : ℕ}
    {x y : Point (ZMod q) (t + 1)} (hxy : x ≠ y) :
    Nat.card (CommonNeighbors x y) ≤ 2 * q ^ (t - 2) := by
  rw [natCard_commonNeighbors_zmod q hxy]
  have hdim : t + 1 - 2 = t - 1 := by omega
  have hpred : t - 1 - 1 = t - 2 := by omega
  rw [hdim]
  simpa [hpred] using geomSum_le_two_mul_pow_pred q (t - 1)
    (Fact.out : q.Prime).two_le

section Mixing




theorem card_filter_univ_eq_natCard_subtype
    {X : Type*} [Fintype X] (p : X → Prop) [DecidablePred p] :
    (Finset.univ.filter p).card = Nat.card {x : X // p x} := by
  rw [Nat.card_eq_fintype_card]
  simp [Fintype.card_subtype]


theorem card_filter_orthogonal
    {F : Type*} [Field F] [Finite F] {d : ℕ}
    [Fintype (Point F d)] [DecidableRel (@Orthogonal F _ d)]
    (x : Point F d) :
    (Finset.univ.filter (Orthogonal x)).card =
      ∑ i ∈ Finset.range (d - 1), Nat.card F ^ i := by
  rw [card_filter_univ_eq_natCard_subtype]
  exact natCard_neighbors x


theorem card_filter_commonOrthogonal
    {F : Type*} [Field F] [Finite F] {d : ℕ}
    [Fintype (Point F d)] [DecidableRel (@Orthogonal F _ d)]
    {x y : Point F d} (hxy : x ≠ y) :
    (Finset.univ.filter fun z ↦ Orthogonal x z ∧ Orthogonal y z).card =
      ∑ i ∈ Finset.range (d - 2), Nat.card F ^ i := by
  rw [card_filter_univ_eq_natCard_subtype]
  exact natCard_commonNeighbors hxy





theorem orthogonal_orderedEdges_deviation_sq_le
    {F : Type*} [Field F] [Finite F] {d : ℕ}
    [Fintype (Point F d)] [DecidableRel (@Orthogonal F _ d)]
    (A B : Finset (Point F d)) :
    let D := ∑ i ∈ Finset.range (d - 1), Nat.card F ^ i
    let C := ∑ i ∈ Finset.range (d - 2), Nat.card F ^ i
    (((Fintype.card (Point F d) : ℝ) *
          Mixing.orderedEdges Orthogonal A B -
        (D : ℝ) * A.card * B.card) ^ 2 ≤
      (A.card : ℝ) *
        ((Fintype.card (Point F d) : ℝ) ^ 2 *
            (D * B.card + C * B.card * (B.card - 1) : ℕ) -
          (Fintype.card (Point F d) : ℝ) * (D * B.card : ℕ) ^ 2)) := by
  dsimp only
  apply Mixing.orderedEdges_deviation_sq_le Orthogonal
  · intro x y hxy
    exact (orthogonal_comm x y).mp hxy
  · exact card_filter_orthogonal
  · intro x y hxy
    exact card_filter_commonOrthogonal hxy




theorem orthogonal_scaled_mixing_sq_le
    {F : Type*} [Field F] [Finite F] {d : ℕ}
    [Fintype (Point F d)] [Nonempty (Point F d)]
    [DecidableRel (@Orthogonal F _ d)]
    (A B : Finset (Point F d)) :
    let D := ∑ i ∈ Finset.range (d - 1), Nat.card F ^ i
    let C := ∑ i ∈ Finset.range (d - 2), Nat.card F ^ i
    (((Fintype.card (Point F d) : ℝ) *
          Mixing.orderedEdges Orthogonal A B -
        (D : ℝ) * A.card * B.card) ^ 2 ≤
      (Fintype.card (Point F d) : ℝ) ^ 2 * ((D : ℝ) - C) *
        A.card * B.card) := by
  dsimp only
  apply Mixing.scaled_orderedEdges_deviation_sq_le Orthogonal
  · intro x y hxy
    exact (orthogonal_comm x y).mp hxy
  · exact card_filter_orthogonal
  · intro x y hxy
    exact card_filter_commonOrthogonal hxy
  · exact geomSum_mono (Nat.card F) (by omega)



theorem orthogonal_abs_orderedEdges_sub_expected_le
    {F : Type*} [Field F] [Finite F] {d : ℕ}
    [Fintype (Point F d)] [Nonempty (Point F d)]
    [DecidableRel (@Orthogonal F _ d)]
    (A B : Finset (Point F d)) :
    let D := ∑ i ∈ Finset.range (d - 1), Nat.card F ^ i
    let C := ∑ i ∈ Finset.range (d - 2), Nat.card F ^ i
    |(Mixing.orderedEdges Orthogonal A B : ℝ) -
        (D : ℝ) / Fintype.card (Point F d) * A.card * B.card| ≤
      Real.sqrt (((D : ℝ) - C) * A.card * B.card) := by
  dsimp only
  apply Mixing.abs_orderedEdges_sub_expected_le Orthogonal
  · intro x y hxy
    exact (orthogonal_comm x y).mp hxy
  · exact card_filter_orthogonal
  · intro x y hxy
    exact card_filter_commonOrthogonal hxy
  · exact geomSum_mono (Nat.card F) (by omega)

end Mixing

end

end Erdos920.Projective























open Matrix

namespace Erdos920
namespace DStar


abbrev Vec (K : Type*) (t : ℕ) := Fin (t + 1) → K


structure Vertex (K : Type*) (t : ℕ) [Field K] where
  left : Vec K t
  right : Vec K t
  left_ne_zero : left ≠ 0
  right_ne_zero : right ≠ 0
  orthogonal : left ⬝ᵥ right = 0


def Arc {K : Type*} {t : ℕ} [Field K] (u v : Vertex K t) : Prop :=
  u.left ⬝ᵥ v.right = 0 ∧ v.left ⬝ᵥ u.right ≠ 0


def HasTransitiveTournament (K : Type*) (t r : ℕ) [Field K] : Prop :=
  ∃ v : Fin r → Vertex K t, Function.Injective v ∧
    ∀ ⦃i j : Fin r⦄, i < j → Arc (v i) (v j)



theorem linearIndependent_of_upperTriangular_pairing
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {n : ℕ}
    (v : Fin n → V) (f : Fin n → V →ₗ[K] K)
    (hzero : ∀ ⦃i j : Fin n⦄, i < j → f i (v j) = 0)
    (hdiag : ∀ i : Fin n, f i (v i) ≠ 0) :
    LinearIndependent K v := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have hcoeff : ∀ k (hk : k < n), c ⟨k, hk⟩ = 0 := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
        intro hk
        let i : Fin n := ⟨k, hk⟩
        have hsum : ∑ j : Fin n, c j * f i (v j) = 0 := by
          calc
            ∑ j : Fin n, c j * f i (v j) =
                f i (∑ j : Fin n, c j • v j) := by
                  simp [map_sum, map_smul, smul_eq_mul]
            _ = 0 := by rw [hc]; simp
        have hsingle : c i * f i (v i) = 0 := by
          rw [← hsum]
          symm
          apply Finset.sum_eq_single i
          · intro j _ hji
            rcases lt_or_gt_of_ne hji with hji_lt | hij_lt
            · rw [ih j.val hji_lt j.isLt]
              simp
            · rw [hzero hij_lt]
              simp
          · simp
        exact (mul_eq_zero.mp hsingle).resolve_right (hdiag i)
  intro i
  exact hcoeff i.val i.isLt


def dotLeft {K : Type*} [Field K] {t : ℕ} (x : Vec K t) : Vec K t →ₗ[K] K where
  toFun y := x ⬝ᵥ y
  map_add' y z := dotProduct_add x y z
  map_smul' a y := by simp [dotProduct_smul]

@[simp]
theorem dotLeft_apply {K : Type*} [Field K] {t : ℕ} (x y : Vec K t) :
    dotLeft x y = x ⬝ᵥ y := rfl



theorem transitiveTournament_impossible
    {K : Type*} [Field K] {t : ℕ}
    (v : Fin (t + 1) → Vertex K t)
    (_hinjective : Function.Injective v)
    (harc : ∀ ⦃i j : Fin (t + 1)⦄, i < j → Arc (v i) (v j)) :
    False := by
  classical
  let x : Fin (t + 1) → Vec K t := fun i ↦ (v i).left
  let y : Fin (t + 1) → Vec K t := fun i ↦ (v i).right
  have hy_last : y (Fin.last t) ≠ 0 := (v (Fin.last t)).right_ne_zero
  have hnot_all : ¬ ∀ w : Vec K t, y (Fin.last t) ⬝ᵥ w = 0 := by
    intro h
    exact hy_last (dotProduct_eq_zero _ h)
  obtain ⟨w, hw⟩ := not_forall.mp hnot_all
  let z : Fin (t + 1) → Vec K t :=
    Fin.lastCases w (fun i : Fin t ↦ x i.succ)
  let f : Fin (t + 1) → Vec K t →ₗ[K] K := fun i ↦ dotLeft (z i)
  have hzero : ∀ ⦃i j : Fin (t + 1)⦄, i < j → f i (y j) = 0 := by
    intro i j hij
    have hi_last : i ≠ Fin.last t := by
      exact ne_of_lt (lt_of_lt_of_le hij (Fin.le_last j))
    obtain ⟨k, rfl⟩ := Fin.eq_castSucc_of_ne_last hi_last
    have hle : k.succ ≤ j := by
      exact (Fin.castSucc_lt_iff_succ_le.mp hij)
    rcases hle.eq_or_lt with heq | hlt
    · subst j
      simpa [f, z, x, y] using (v k.succ).orthogonal
    · simpa [f, z, x, y] using (harc hlt).1
  have hdiag : ∀ i : Fin (t + 1), f i (y i) ≠ 0 := by
    intro i
    refine Fin.lastCases ?_ (fun k : Fin t ↦ ?_) i
    · simpa [f, z, y, dotProduct_comm] using hw
    · simpa [f, z, x, y] using
        (harc (Fin.castSucc_lt_succ (i := k))).2
  have hy_independent : LinearIndependent K y :=
    linearIndependent_of_upperTriangular_pairing y f hzero hdiag
  have hy_span : Submodule.span K (Set.range y) = ⊤ := by
    apply hy_independent.span_eq_top_of_card_eq_finrank
    simp
  have hx_zero_on_generators : ∀ j : Fin (t + 1), x 0 ⬝ᵥ y j = 0 := by
    intro j
    by_cases hj : j = 0
    · subst j
      exact (v 0).orthogonal
    · exact (harc (Fin.pos_iff_ne_zero.mpr hj)).1
  have hx_zero_on_all : ∀ u : Vec K t, x 0 ⬝ᵥ u = 0 := by
    have hspan_le : Submodule.span K (Set.range y) ≤ (dotLeft (x 0)).ker := by
      rw [Submodule.span_le]
      rintro u ⟨j, rfl⟩
      exact LinearMap.mem_ker.mpr (hx_zero_on_generators j)
    intro u
    have hu : u ∈ Submodule.span K (Set.range y) := by
      rw [hy_span]
      trivial
    exact LinearMap.mem_ker.mp (hspan_le hu)
  have hx0 : x 0 = 0 := dotProduct_eq_zero _ hx_zero_on_all
  exact (v 0).left_ne_zero hx0


theorem no_transitiveTournament {K : Type*} [Field K] (t : ℕ) :
    ¬ HasTransitiveTournament K t (t + 1) := by
  rintro ⟨v, hinjective, harc⟩
  exact transitiveTournament_impossible v hinjective harc

end DStar
end Erdos920
















namespace Erdos920.PrimeScale

open Filter Asymptotics

private lemma eventually_log_sq_linear (C : ℝ) (hC : 0 < C) :
    ∀ᶠ m : ℕ in atTop,
      8 * C * Real.log (m : ℝ) ^ 2 ≤ (m : ℝ) := by
  have heps : 0 < (8 * C)⁻¹ := inv_pos.mpr (mul_pos (by norm_num) hC)
  have hreal := (Real.isLittleO_pow_log_id_atTop (n := 2)).bound heps
  have hnat := tendsto_natCast_atTop_atTop.eventually hreal
  filter_upwards [hnat] with m hm
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), id_eq,
    Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)] at hm
  calc
    8 * C * Real.log (m : ℝ) ^ 2
        ≤ 8 * C * ((8 * C)⁻¹ * (m : ℝ)) :=
      mul_le_mul_of_nonneg_left hm (mul_nonneg (by norm_num) hC.le)
    _ = (m : ℝ) := by
      field_simp

private lemma eventually_log_large (C : ℝ) (_hC : 0 < C) :
    ∀ᶠ m : ℕ in atTop,
      max 1 (1 / (2 * C)) ≤ Real.log (m : ℝ) := by
  exact (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
    (eventually_ge_atTop (max 1 (1 / (2 * C))))










theorem eventually_exists_prime_scale (C : ℝ) (hC : 0 < C) :
    ∀ᶠ m : ℕ in atTop, ∃ q : ℕ,
      q.Prime ∧
      2 ≤ q ∧
      q ≤ m ∧
      (m : ℝ) / (8 * C * Real.log (m : ℝ) ^ 2) ≤ (q : ℝ) ∧
      C * (q : ℝ) * Real.log (q : ℝ) ^ 2 ≤ (m : ℝ) := by
  filter_upwards [eventually_log_sq_linear C hC, eventually_log_large C hC]
    with m hlinear hlogLarge
  have hlogm : 0 < Real.log (m : ℝ) :=
    lt_of_lt_of_le (by norm_num) (le_trans (le_max_left _ _) hlogLarge)
  have hden4 : 0 < 4 * C * Real.log (m : ℝ) ^ 2 := by positivity
  have hden2 : 0 < 2 * C * Real.log (m : ℝ) ^ 2 := by positivity
  have hscale :
      2 ≤ (m : ℝ) / (4 * C * Real.log (m : ℝ) ^ 2) := by
    rw [le_div_iff₀ hden4]
    nlinarith
  let r : ℕ := ⌊(m : ℝ) / (4 * C * Real.log (m : ℝ) ^ 2)⌋₊
  have hfloor :
      (m : ℝ) / (8 * C * Real.log (m : ℝ) ^ 2) ≤ (r : ℝ) := by
    have hsub := Nat.sub_one_lt_floor
      ((m : ℝ) / (4 * C * Real.log (m : ℝ) ^ 2))
    change (m : ℝ) / (8 * C * Real.log (m : ℝ) ^ 2) ≤
      (⌊(m : ℝ) / (4 * C * Real.log (m : ℝ) ^ 2)⌋₊ : ℝ)
    have hhalf :
        (m : ℝ) / (8 * C * Real.log (m : ℝ) ^ 2) =
          ((m : ℝ) / (4 * C * Real.log (m : ℝ) ^ 2)) / 2 := by ring
    rw [hhalf]
    linarith
  have hr0 : r ≠ 0 := by
    intro hr
    have hone :
        (1 : ℝ) ≤ (m : ℝ) / (8 * C * Real.log (m : ℝ) ^ 2) := by
      have hhalf :
          (m : ℝ) / (8 * C * Real.log (m : ℝ) ^ 2) =
            ((m : ℝ) / (4 * C * Real.log (m : ℝ) ^ 2)) / 2 := by ring
      rw [hhalf]
      linarith
    have : (1 : ℝ) ≤ (r : ℝ) := hone.trans hfloor
    norm_num [hr] at this
  obtain ⟨q, hqprime, hrq, hq2r⟩ := Nat.bertrand r hr0
  have hq2 : 2 ≤ q := hqprime.two_le
  have hfloorUpper :
      (r : ℝ) ≤ (m : ℝ) / (4 * C * Real.log (m : ℝ) ^ 2) := by
    exact Nat.floor_le (by positivity)
  have hqUpper :
      (q : ℝ) ≤ (m : ℝ) / (2 * C * Real.log (m : ℝ) ^ 2) := by
    have hq2r' : (q : ℝ) ≤ 2 * (r : ℝ) := by exact_mod_cast hq2r
    calc
      (q : ℝ) ≤ 2 * (r : ℝ) := hq2r'
      _ ≤ 2 * ((m : ℝ) / (4 * C * Real.log (m : ℝ) ^ 2)) :=
        mul_le_mul_of_nonneg_left hfloorUpper (by norm_num)
      _ = (m : ℝ) / (2 * C * Real.log (m : ℝ) ^ 2) := by ring
  have hdenOne : 1 ≤ 2 * C * Real.log (m : ℝ) ^ 2 := by
    have hlogC : 1 / (2 * C) ≤ Real.log (m : ℝ) :=
      (le_max_right _ _).trans hlogLarge
    have honeC : 1 ≤ 2 * C * Real.log (m : ℝ) := by
      rw [div_le_iff₀ (mul_pos (by norm_num) hC)] at hlogC
      nlinarith
    calc
      1 ≤ 2 * C * Real.log (m : ℝ) := honeC
      _ ≤ (2 * C * Real.log (m : ℝ)) * Real.log (m : ℝ) := by
        exact le_mul_of_one_le_right (by positivity)
          ((le_max_left _ _).trans hlogLarge)
      _ = 2 * C * Real.log (m : ℝ) ^ 2 := by ring
  have hqlem : (q : ℝ) ≤ (m : ℝ) := by
    exact hqUpper.trans (div_le_self (Nat.cast_nonneg m) hdenOne)
  have hqm : q ≤ m := by exact_mod_cast hqlem
  have hlogq : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg (by
    exact_mod_cast (show 1 ≤ q from hq2.trans' (by omega)))
  have hlogqm : Real.log (q : ℝ) ≤ Real.log (m : ℝ) :=
    Real.log_le_log (by exact_mod_cast hqprime.pos) hqlem
  have hlogsq : Real.log (q : ℝ) ^ 2 ≤ Real.log (m : ℝ) ^ 2 := by
    nlinarith
  have hproduct :
      (q : ℝ) * Real.log (q : ℝ) ^ 2 ≤
        ((m : ℝ) / (2 * C * Real.log (m : ℝ) ^ 2)) *
          Real.log (m : ℝ) ^ 2 := by
    exact mul_le_mul hqUpper hlogsq (sq_nonneg _) (by positivity)
  refine ⟨q, hqprime, hq2, hqm, ?_, ?_⟩
  · exact hfloor.trans (by exact_mod_cast hrq.le)
  · calc
      C * (q : ℝ) * Real.log (q : ℝ) ^ 2
          = C * ((q : ℝ) * Real.log (q : ℝ) ^ 2) := by ring
      _ ≤ C * (((m : ℝ) / (2 * C * Real.log (m : ℝ) ^ 2)) *
          Real.log (m : ℝ) ^ 2) := mul_le_mul_of_nonneg_left hproduct hC.le
      _ = (m : ℝ) / 2 := by field_simp
      _ ≤ (m : ℝ) := div_le_self (Nat.cast_nonneg m) (by norm_num)


theorem eventually_exists_prime_scale_nat (C : ℕ) (hC : 0 < C) :
    ∀ᶠ m : ℕ in atTop, ∃ q : ℕ,
      q.Prime ∧
      2 ≤ q ∧
      q ≤ m ∧
      (m : ℝ) / (8 * (C : ℝ) * Real.log (m : ℝ) ^ 2) ≤ (q : ℝ) ∧
      (C : ℝ) * (q : ℝ) * Real.log (q : ℝ) ^ 2 ≤ (m : ℝ) := by
  exact eventually_exists_prime_scale (C : ℝ) (by exact_mod_cast hC)

end Erdos920.PrimeScale





















open Filter
open scoped BigOperators

namespace Erdos920.RamseyPackaging

noncomputable section





structure Digraph (V : Type*) where
  arc : V → V → Prop


def Digraph.HasTransitiveTournament {V : Type*} (D : Digraph V) (r : ℕ) : Prop :=
  ∃ v : Fin r → V, Function.Injective v ∧
    ∀ i j : Fin r, i < j → D.arc (v i) (v j)



def Digraph.IsForwardIndependent {V : Type*} (D : Digraph V) {m : ℕ}
    (v : Fin m → V) : Prop :=
  ∀ i j : Fin m, i < j → ¬ D.arc (v i) (v j)


def Digraph.forwardIndependentTupleCount {V : Type*} [Fintype V]
    (D : Digraph V) (m : ℕ) : ℕ := by
  classical
  exact ((Finset.univ : Finset (Fin m → V)).filter
    (fun v => D.IsForwardIndependent v)).card




structure DStarWitness (t m q : ℕ) (C : ℝ) where
  V : Type
  fintypeV : Fintype V
  D : Digraph V
  transitiveTournamentFree : ¬ D.HasTransitiveTournament (t + 1)
  vertex_lower : (q : ℝ) ^ (2 * t - 1) / 4 ≤ (@Fintype.card V fintypeV : ℝ)
  forward_bound :
    ((@Digraph.forwardIndependentTupleCount V fintypeV D m : ℕ) : ℝ) ≤
      (C * (q : ℝ) ^ t) ^ m

namespace DStarWitness

variable {t m q : ℕ} {C : ℝ}


def samplingDensity (_W : DStarWitness t m q C) : ℝ :=
  (m : ℝ) / (Real.exp 1 * C * (q : ℝ) ^ t)












def HasAveragingSamplingConclusion (W : DStarWitness t m q C) : Prop :=
  W.samplingDensity * (@Fintype.card W.V W.fintypeV : ℝ) - 1 <
    (Ramsey.ramseyNumber (t + 1) m : ℝ)


def SamplingSideConditions (W : DStarWitness t m q C) : Prop :=
  0 < W.samplingDensity ∧ W.samplingDensity ≤ 1

end DStarWitness








theorem ramsey_lower_of_dStarWitness {t m q : ℕ} {C : ℝ}
    (W : DStarWitness t m q C) (ht : 1 ≤ t) (hq : 1 ≤ q)
    (hC : 0 < C) (hm : 8 * Real.exp 1 * C ≤ (m : ℝ))
    (haverage : W.HasAveragingSamplingConclusion) :
    (m : ℝ) * (q : ℝ) ^ (t - 1) / (8 * Real.exp 1 * C) ≤
      (Ramsey.ramseyNumber (t + 1) m : ℝ) := by
  let E : ℝ := Real.exp 1
  have hE : 0 < E := Real.exp_pos 1
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hqpow : 0 < (q : ℝ) ^ t := pow_pos hq0 _
  have hden : 0 < E * C * (q : ℝ) ^ t := mul_pos (mul_pos hE hC) hqpow
  have hcard := W.vertex_lower
  have htwo : 2 * t - 1 = t + (t - 1) := by omega
  have hscale_nonneg :
      0 ≤ (m : ℝ) / (E * C * (q : ℝ) ^ t) :=
    div_nonneg (Nat.cast_nonneg _) hden.le
  have hsample_lower :
      (m : ℝ) * (q : ℝ) ^ (t - 1) / (4 * E * C) ≤
        W.samplingDensity * (@Fintype.card W.V W.fintypeV : ℝ) := by
    calc
      (m : ℝ) * (q : ℝ) ^ (t - 1) / (4 * E * C) =
          ((m : ℝ) / (E * C * (q : ℝ) ^ t)) *
            ((q : ℝ) ^ (2 * t - 1) / 4) := by
              rw [htwo, pow_add]
              field_simp
      _ ≤ ((m : ℝ) / (E * C * (q : ℝ) ^ t)) *
            (@Fintype.card W.V W.fintypeV : ℝ) :=
        mul_le_mul_of_nonneg_left hcard hscale_nonneg
      _ = W.samplingDensity * (@Fintype.card W.V W.fintypeV : ℝ) := by
        rfl
  have hhalf_ge_one :
      1 ≤ (m : ℝ) * (q : ℝ) ^ (t - 1) / (8 * E * C) := by
    have hqpow_one : (1 : ℝ) ≤ (q : ℝ) ^ (t - 1) := by
      exact one_le_pow₀ (by exact_mod_cast hq)
    have hm' : 8 * E * C ≤ (m : ℝ) * (q : ℝ) ^ (t - 1) := by
      calc
        8 * E * C ≤ (m : ℝ) := hm
        _ ≤ (m : ℝ) * (q : ℝ) ^ (t - 1) := by
          exact le_mul_of_one_le_right (Nat.cast_nonneg _) hqpow_one
    exact (le_div_iff₀ (mul_pos (mul_pos (by norm_num) hE) hC)).2 (by
      simpa [mul_assoc] using hm')
  have hsplit :
      (m : ℝ) * (q : ℝ) ^ (t - 1) / (4 * E * C) =
        2 * ((m : ℝ) * (q : ℝ) ^ (t - 1) / (8 * E * C)) := by
    field_simp
    ring
  have hminus_one :
      (m : ℝ) * (q : ℝ) ^ (t - 1) / (8 * E * C) ≤
        W.samplingDensity * (@Fintype.card W.V W.fintypeV : ℝ) - 1 := by
    rw [hsplit] at hsample_lower
    linarith
  exact hminus_one.trans haverage.le





def HasDStarAtScale (u m : ℕ) (C κ : ℝ) : Prop :=
  ∃ q : ℕ, q.Prime ∧
    κ * ((m : ℝ) / Real.log (m : ℝ) ^ 2) ≤ (q : ℝ) ∧
    ∃ W : DStarWitness (u + 1) m q C,
      W.SamplingSideConditions ∧ W.HasAveragingSamplingConclusion


lemma target_scale_eq (u m : ℕ) (κ C : ℝ) (hlog : Real.log (m : ℝ) ≠ 0)
    (hC : C ≠ 0) :
    κ ^ u / (8 * Real.exp 1 * C) * (m : ℝ) ^ (u + 1) /
        Real.log (m : ℝ) ^ (2 * u) =
      (m : ℝ) * (κ * ((m : ℝ) / Real.log (m : ℝ) ^ 2)) ^ u /
        (8 * Real.exp 1 * C) := by
  rw [pow_succ, mul_pow, div_pow, pow_mul]
  field_simp [hlog, hC]



theorem ramsey_lower_of_hasDStarAtScale {u m : ℕ} {C κ : ℝ}
    (hC : 0 < C) (hκ : 0 ≤ κ) (hm2 : 2 ≤ m)
    (hlarge : 8 * Real.exp 1 * C ≤ (m : ℝ))
    (hstar : HasDStarAtScale u m C κ) :
    κ ^ u / (8 * Real.exp 1 * C) * (m : ℝ) ^ (u + 1) /
        Real.log (m : ℝ) ^ (2 * u) ≤
      (Ramsey.ramseyNumber (u + 2) m : ℝ) := by
  rcases hstar with ⟨q, hqprime, hqscale, W, _hside, haverage⟩
  have hq1 : 1 ≤ q := (Nat.Prime.one_lt hqprime).le
  have hlogpos : 0 < Real.log (m : ℝ) := Real.log_pos (by exact_mod_cast hm2)
  have hscale_nonneg : 0 ≤ κ * ((m : ℝ) / Real.log (m : ℝ) ^ 2) :=
    mul_nonneg hκ (div_nonneg (Nat.cast_nonneg _) (sq_nonneg _))
  have hpow_scale :
      (κ * ((m : ℝ) / Real.log (m : ℝ) ^ 2)) ^ u ≤ (q : ℝ) ^ u :=
    pow_le_pow_left₀ hscale_nonneg hqscale _
  have hmul_scale :
      (m : ℝ) * (κ * ((m : ℝ) / Real.log (m : ℝ) ^ 2)) ^ u /
          (8 * Real.exp 1 * C) ≤
        (m : ℝ) * (q : ℝ) ^ u / (8 * Real.exp 1 * C) := by
    gcongr
  rw [target_scale_eq u m κ C hlogpos.ne' hC.ne']
  exact hmul_scale.trans
    (ramsey_lower_of_dStarWitness W (by omega) hq1 hC hlarge haverage)






structure DStarFamily (u : ℕ) where
  C : ℝ
  κ : ℝ
  C_pos : 0 < C
  κ_pos : 0 < κ
  exists_eventually : ∀ᶠ m : ℕ in atTop, HasDStarAtScale u m C κ




structure DStarConstruction (u : ℕ) where
  C : ℝ
  C_pos : 0 < C
  qThreshold : ℕ
  build : ∀ (m q : ℕ), q.Prime → qThreshold ≤ q → 2 ≤ q → q ≤ m →
    (m : ℝ) / (8 * C * Real.log (m : ℝ) ^ 2) ≤ (q : ℝ) →
    C * (q : ℝ) * Real.log (q : ℝ) ^ 2 ≤ (m : ℝ) →
      ∃ W : DStarWitness (u + 1) m q C,
        W.SamplingSideConditions ∧ W.HasAveragingSamplingConclusion


private lemma eventually_mul_log_sq_le (K : ℝ) (hK : 0 < K) :
    ∀ᶠ m : ℕ in atTop, K * Real.log (m : ℝ) ^ 2 ≤ (m : ℝ) := by
  have heps : 0 < K⁻¹ := inv_pos.mpr hK
  have hreal := (Real.isLittleO_pow_log_id_atTop (n := 2)).bound heps
  have hnat := tendsto_natCast_atTop_atTop.eventually hreal
  filter_upwards [hnat] with m hm
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), id_eq,
    Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)] at hm
  calc
    K * Real.log (m : ℝ) ^ 2 ≤ K * (K⁻¹ * (m : ℝ)) :=
      mul_le_mul_of_nonneg_left hm hK.le
    _ = (m : ℝ) := by field_simp



private lemma eventually_qThreshold_le_scale (C : ℝ) (hC : 0 < C) (Q : ℕ) :
    ∀ᶠ m : ℕ in atTop,
      (Q : ℝ) ≤ (m : ℝ) / (8 * C * Real.log (m : ℝ) ^ 2) := by
  have hK : 0 < 8 * C * ((Q : ℝ) + 1) := by positivity
  filter_upwards [eventually_mul_log_sq_le
      (8 * C * ((Q : ℝ) + 1)) hK,
      eventually_ge_atTop (2 : ℕ)] with m hm hm2
  have hlog : 0 < Real.log (m : ℝ) := Real.log_pos (by exact_mod_cast hm2)
  rw [le_div_iff₀ (by positivity)]
  calc
    (Q : ℝ) * (8 * C * Real.log (m : ℝ) ^ 2) ≤
        (8 * C * ((Q : ℝ) + 1)) * Real.log (m : ℝ) ^ 2 := by
      nlinarith [sq_nonneg (Real.log (m : ℝ))]
    _ ≤ (m : ℝ) := hm




def DStarConstruction.toFamily {u : ℕ} (B : DStarConstruction u) :
    DStarFamily u where
  C := B.C
  κ := 1 / (8 * B.C)
  C_pos := B.C_pos
  κ_pos := div_pos (by norm_num) (mul_pos (by norm_num) B.C_pos)
  exists_eventually := by
    filter_upwards [PrimeScale.eventually_exists_prime_scale B.C B.C_pos,
      eventually_qThreshold_le_scale B.C B.C_pos B.qThreshold] with
      m hprime hthreshold
    rcases hprime with ⟨q, hqprime, hq2, hqm, hqscale, hbudget⟩
    have hqthreshold : B.qThreshold ≤ q := by
      exact_mod_cast hthreshold.trans hqscale
    refine ⟨q, hqprime, ?_,
      B.build m q hqprime hqthreshold hq2 hqm hqscale hbudget⟩
    have hm2 : 2 ≤ m := hq2.trans hqm
    have hlog : Real.log (m : ℝ) ≠ 0 :=
      (Real.log_pos (by exact_mod_cast hm2)).ne'
    calc
      (1 / (8 * B.C)) * ((m : ℝ) / Real.log (m : ℝ) ^ 2) =
          (m : ℝ) / (8 * B.C * Real.log (m : ℝ) ^ 2) := by
            field_simp [B.C_pos.ne', hlog]
      _ ≤ (q : ℝ) := hqscale



theorem bradac_ramsey_lower_bound_eventually_of_dStarFamily (u : ℕ)
    (F : DStarFamily u) :
    ∃ A : ℝ, 0 < A ∧
      ∀ᶠ m : ℕ in atTop,
        A * (m : ℝ) ^ (u + 1) / Real.log (m : ℝ) ^ (2 * u) ≤
          (Ramsey.ramseyNumber (u + 2) m : ℝ) := by
  let A : ℝ := F.κ ^ u / (8 * Real.exp 1 * F.C)
  have hA : 0 < A := div_pos (pow_pos F.κ_pos _) <|
    mul_pos (mul_pos (by norm_num) (Real.exp_pos 1)) F.C_pos
  refine ⟨A, hA, ?_⟩
  filter_upwards [F.exists_eventually,
      (eventually_ge_atTop (2 : ℕ)),
      (tendsto_natCast_atTop_atTop.eventually
        (eventually_ge_atTop (8 * Real.exp 1 * F.C)))] with m hstar hm2 hlarge
  exact ramsey_lower_of_hasDStarAtScale F.C_pos F.κ_pos.le hm2 hlarge hstar



theorem bradac_ramsey_lower_bound_eventually_of_package (s : ℕ) (hs : 3 ≤ s)
    (F : DStarFamily (s - 2)) :
    ∃ A : ℝ, 0 < A ∧
      ∀ᶠ m : ℕ in atTop,
        A * (m : ℝ) ^ (s - 1) / Real.log (m : ℝ) ^ (2 * s - 4) ≤
          (Ramsey.ramseyNumber s m : ℝ) := by
  obtain ⟨A, hA, hbound⟩ :=
    bradac_ramsey_lower_bound_eventually_of_dStarFamily (s - 2) F
  refine ⟨A, hA, ?_⟩
  have hsu : s - 2 + 2 = s := by omega
  have hspow : s - 2 + 1 = s - 1 := by omega
  have hslog : 2 * (s - 2) = 2 * s - 4 := by omega
  simpa [hsu, hspow, hslog] using hbound




theorem bradac_ramsey_lower_bound_eventually_of_construction (s : ℕ)
    (hs : 3 ≤ s) (B : DStarConstruction (s - 2)) :
    ∃ A : ℝ, 0 < A ∧
      ∀ᶠ m : ℕ in atTop,
        A * (m : ℝ) ^ (s - 1) / Real.log (m : ℝ) ^ (2 * s - 4) ≤
          (Ramsey.ramseyNumber s m : ℝ) :=
  bradac_ramsey_lower_bound_eventually_of_package s hs B.toFamily

end

end Erdos920.RamseyPackaging













open scoped BigOperators LinearAlgebra.Projectivization

namespace Erdos920.ProjectiveDStar

noncomputable section

open Erdos920.Projective



abbrev Vertex (q t : ℕ) [Fact q.Prime] :=
  {p : Point (ZMod q) (t + 1) × Point (ZMod q) (t + 1) //
    Orthogonal p.1 p.2}

instance vertexFintype (q t : ℕ) [Fact q.Prime] : Fintype (Vertex q t) :=
  Fintype.ofFinite (Vertex q t)


def leftPoint {q t : ℕ} [Fact q.Prime] (u : Vertex q t) :
    Point (ZMod q) (t + 1) := u.1.1


def rightPoint {q t : ℕ} [Fact q.Prime] (u : Vertex q t) :
    Point (ZMod q) (t + 1) := u.1.2

@[simp] theorem incident {q t : ℕ} [Fact q.Prime] (u : Vertex q t) :
    Orthogonal (leftPoint u) (rightPoint u) := u.2



def vertexEquivSigma (q t : ℕ) [Fact q.Prime] :
    Vertex q t ≃ (Σ x : Point (ZMod q) (t + 1), Neighbors x) where
  toFun u := ⟨leftPoint u, ⟨rightPoint u, incident u⟩⟩
  invFun u := ⟨(u.1, u.2.1), u.2.2⟩
  left_inv u := by cases u; rfl
  right_inv u := by cases u with | mk x y => cases y; rfl


def Arc {q t : ℕ} [Fact q.Prime] (u v : Vertex q t) : Prop :=
  Orthogonal (leftPoint u) (rightPoint v) ∧
    ¬ Orthogonal (leftPoint v) (rightPoint u)

instance arcDecidable {q t : ℕ} [Fact q.Prime] : DecidableRel (@Arc q t _) :=
  Classical.decRel _



def toVectorVertex {q t : ℕ} [Fact q.Prime] (u : Vertex q t) :
    DStar.Vertex (ZMod q) t where
  left := (leftPoint u).rep
  right := (rightPoint u).rep
  left_ne_zero := (leftPoint u).rep_nonzero
  right_ne_zero := (rightPoint u).rep_nonzero
  orthogonal := by
    have h := incident u
    rw [← (leftPoint u).mk_rep, ← (rightPoint u).mk_rep] at h
    exact (Projectivization.orthogonal_mk
      (leftPoint u).rep_nonzero (rightPoint u).rep_nonzero).mp h


theorem arc_iff_vectorArc {q t : ℕ} [Fact q.Prime] (u v : Vertex q t) :
    Arc u v ↔ DStar.Arc (toVectorVertex u) (toVectorVertex v) := by
  constructor
  · rintro ⟨huv, hvu⟩
    constructor
    · rw [← (leftPoint u).mk_rep, ← (rightPoint v).mk_rep] at huv
      exact (Projectivization.orthogonal_mk
        (leftPoint u).rep_nonzero (rightPoint v).rep_nonzero).mp huv
    · intro hzero
      apply hvu
      rw [← (leftPoint v).mk_rep, ← (rightPoint u).mk_rep]
      exact (Projectivization.orthogonal_mk
        (leftPoint v).rep_nonzero (rightPoint u).rep_nonzero).mpr hzero
  · rintro ⟨huv, hvu⟩
    constructor
    · rw [← (leftPoint u).mk_rep, ← (rightPoint v).mk_rep]
      exact (Projectivization.orthogonal_mk
        (leftPoint u).rep_nonzero (rightPoint v).rep_nonzero).mpr huv
    · intro horth
      apply hvu
      rw [← (leftPoint v).mk_rep, ← (rightPoint u).mk_rep] at horth
      exact (Projectivization.orthogonal_mk
        (leftPoint v).rep_nonzero (rightPoint u).rep_nonzero).mp horth



theorem no_transitiveTournament (q t : ℕ) [Fact q.Prime] :
    ¬ ∃ v : Fin (t + 1) → Vertex q t, Function.Injective v ∧
      ∀ {i j : Fin (t + 1)}, i < j → Arc (v i) (v j) := by
  rintro ⟨v, hv, harc⟩
  apply DStar.no_transitiveTournament (K := ZMod q) t
  refine ⟨fun i ↦ toVectorVertex (v i), ?_, ?_⟩
  · intro i j hij
    apply hv
    
    have hleft : leftPoint (v i) = leftPoint (v j) := by
      rw [← (leftPoint (v i)).mk_rep, ← (leftPoint (v j)).mk_rep]
      exact congrArg (fun z : DStar.Vertex (ZMod q) t ↦
        Projectivization.mk (ZMod q) z.left z.left_ne_zero) hij
    have hright : rightPoint (v i) = rightPoint (v j) := by
      rw [← (rightPoint (v i)).mk_rep, ← (rightPoint (v j)).mk_rep]
      exact congrArg (fun z : DStar.Vertex (ZMod q) t ↦
        Projectivization.mk (ZMod q) z.right z.right_ne_zero) hij
    apply Subtype.ext
    exact Prod.ext hleft hright
  · intro i j hij
    exact (arc_iff_vectorArc (v i) (v j)).mp (harc hij)


def digraph (q t : ℕ) [Fact q.Prime] :
    RamseyPackaging.Digraph (Vertex q t) where
  arc := Arc

theorem digraph_transitiveTournamentFree (q t : ℕ) [Fact q.Prime] :
    ¬ (digraph q t).HasTransitiveTournament (t + 1) := by
  rintro ⟨v, hv, harc⟩
  exact no_transitiveTournament q t ⟨v, hv, fun {_ _} h ↦ harc _ _ h⟩


theorem card_vertex (q t : ℕ) [Fact q.Prime] :
    Fintype.card (Vertex q t) =
      (∑ i ∈ Finset.range (t + 1), q ^ i) *
        (∑ i ∈ Finset.range t, q ^ i) := by
  let : Fintype (Point (ZMod q) (t + 1)) := Fintype.ofFinite _
  let (x : Point (ZMod q) (t + 1)) : Fintype (Neighbors x) :=
    Fintype.ofFinite _
  rw [Fintype.card_congr (vertexEquivSigma q t), Fintype.card_sigma]
  have hneigh (x : Point (ZMod q) (t + 1)) :
      Fintype.card (Neighbors x) = ∑ i ∈ Finset.range t, q ^ i := by
    rw [← Nat.card_eq_fintype_card]
    simpa using natCard_neighbors_zmod q x
  have hpoint : Fintype.card (Point (ZMod q) (t + 1)) =
      ∑ i ∈ Finset.range (t + 1), q ^ i := by
    rw [← Nat.card_eq_fintype_card]
    exact natCard_point_zmod q (t + 1)
  simp_rw [hneigh]
  rw [Finset.sum_const, Finset.card_univ, hpoint, nsmul_eq_mul]
  norm_num


lemma pow_le_geometricSum (q d i : ℕ) (hi : i < d) :
    q ^ i ≤ ∑ j ∈ Finset.range d, q ^ j := by
  exact Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) (by simp [hi])



theorem pow_two_mul_sub_one_le_card_vertex (q t : ℕ) [Fact q.Prime]
    (ht : 1 ≤ t) :
    q ^ (2 * t - 1) ≤ Fintype.card (Vertex q t) := by
  rw [card_vertex]
  have h1 := pow_le_geometricSum q (t + 1) t (by omega)
  have h2 := pow_le_geometricSum q t (t - 1) (by omega)
  calc
    q ^ (2 * t - 1) = q ^ t * q ^ (t - 1) := by
      rw [← pow_add]
      congr 1
      omega
    _ ≤ (∑ i ∈ Finset.range (t + 1), q ^ i) *
        (∑ i ∈ Finset.range t, q ^ i) := Nat.mul_le_mul h1 h2



lemma geometricSum_le_two_mul_pow (q d : ℕ) (hq : 2 ≤ q) (hd : 1 ≤ d) :
    ∑ i ∈ Finset.range d, q ^ i ≤ 2 * q ^ (d - 1) := by
  rw [Nat.geomSum_eq hq]
  apply Nat.div_le_of_le_mul
  have hd_eq : d = (d - 1) + 1 := by omega
  have hqfactor : q ≤ 2 * (q - 1) := by omega
  calc
    q ^ d - 1 ≤ q ^ d := Nat.sub_le _ _
    _ = q ^ ((d - 1) + 1) := congrArg (fun n ↦ q ^ n) hd_eq
    _ = q ^ (d - 1) * q := by rw [pow_succ]
    _ ≤ q ^ (d - 1) * (2 * (q - 1)) :=
      Nat.mul_le_mul_left _ hqfactor
    _ = (q - 1) * (2 * q ^ (d - 1)) := by ring


theorem card_vertex_le_four_mul_pow (q t : ℕ) [Fact q.Prime]
    (ht : 1 ≤ t) :
    Fintype.card (Vertex q t) ≤ 4 * q ^ (2 * t - 1) := by
  have hq : 2 ≤ q := (Fact.out : q.Prime).two_le
  rw [card_vertex]
  have h1 := geometricSum_le_two_mul_pow q (t + 1) hq (by omega)
  have h2 := geometricSum_le_two_mul_pow q t hq ht
  calc
    (∑ i ∈ Finset.range (t + 1), q ^ i) *
        (∑ i ∈ Finset.range t, q ^ i)
        ≤ (2 * q ^ t) * (2 * q ^ (t - 1)) := Nat.mul_le_mul h1 h2
    _ = 4 * q ^ (2 * t - 1) := by
      rw [mul_mul_mul_comm, ← pow_add]
      congr 2
      omega


theorem vertex_lower_real (q t : ℕ) [Fact q.Prime] (ht : 1 ≤ t) :
    (q : ℝ) ^ (2 * t - 1) / 4 ≤ (Fintype.card (Vertex q t) : ℝ) := by
  have h := pow_two_mul_sub_one_le_card_vertex q t ht
  have hreal : (q : ℝ) ^ (2 * t - 1) ≤
      (Fintype.card (Vertex q t) : ℝ) := by exact_mod_cast h
  calc
    (q : ℝ) ^ (2 * t - 1) / 4 ≤ (q : ℝ) ^ (2 * t - 1) := by
      have hp : 0 ≤ (q : ℝ) ^ (2 * t - 1) :=
        pow_nonneg (Nat.cast_nonneg q) _
      linarith
    _ ≤ (Fintype.card (Vertex q t) : ℝ) := hreal

end

end Erdos920.ProjectiveDStar













namespace Erdos920.ConcreteWitness

open Erdos920.ProjectiveDStar
open Erdos920.RamseyPackaging

noncomputable section






def ofForwardBound (q t m : ℕ) [Fact q.Prime] (C : ℝ) (ht : 1 ≤ t)
    (hforward :
      ((@Digraph.forwardIndependentTupleCount
          (ProjectiveDStar.Vertex q t)
          (ProjectiveDStar.vertexFintype q t)
          (ProjectiveDStar.digraph q t) m : ℕ) : ℝ) ≤
        (C * (q : ℝ) ^ t) ^ m) :
    DStarWitness t m q C where
  V := ProjectiveDStar.Vertex q t
  fintypeV := ProjectiveDStar.vertexFintype q t
  D := ProjectiveDStar.digraph q t
  transitiveTournamentFree :=
    ProjectiveDStar.digraph_transitiveTournamentFree q t
  vertex_lower := ProjectiveDStar.vertex_lower_real q t ht
  forward_bound := hforward



@[simp] theorem ofForwardBound_vertexType (q t m : ℕ) [Fact q.Prime]
    (C : ℝ) (ht : 1 ≤ t) (hforward :
      ((@Digraph.forwardIndependentTupleCount
          (ProjectiveDStar.Vertex q t)
          (ProjectiveDStar.vertexFintype q t)
          (ProjectiveDStar.digraph q t) m : ℕ) : ℝ) ≤
        (C * (q : ℝ) ^ t) ^ m) :
    (ofForwardBound q t m C ht hforward).V =
      ProjectiveDStar.Vertex q t := rfl


@[simp] theorem ofForwardBound_digraph (q t m : ℕ) [Fact q.Prime]
    (C : ℝ) (ht : 1 ≤ t) (hforward :
      ((@Digraph.forwardIndependentTupleCount
          (ProjectiveDStar.Vertex q t)
          (ProjectiveDStar.vertexFintype q t)
          (ProjectiveDStar.digraph q t) m : ℕ) : ℝ) ≤
        (C * (q : ℝ) ^ t) ^ m) :
    (ofForwardBound q t m C ht hforward).D =
      ProjectiveDStar.digraph q t := rfl

end

end Erdos920.ConcreteWitness















namespace Erdos920.DensitySide

open Filter

private lemma eventually_log_four_growth (C : ℝ) (hC : 0 < C) :
    ∀ᶠ m : ℕ in atTop,
      64 * C * Real.log (m : ℝ) ^ 4 ≤ Real.exp 1 * (m : ℝ) := by
  have hK : 0 < 64 * C / Real.exp 1 := by positivity
  have heps : 0 < (64 * C / Real.exp 1)⁻¹ := inv_pos.mpr hK
  have hreal := (Real.isLittleO_pow_log_id_atTop (n := 4)).bound heps
  have hnat := tendsto_natCast_atTop_atTop.eventually hreal
  filter_upwards [hnat] with m hm
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ Real.log (m : ℝ) ^ 4),
    id_eq, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)] at hm
  have hscaled :
      (64 * C / Real.exp 1) * Real.log (m : ℝ) ^ 4 ≤ (m : ℝ) := by
    calc
      (64 * C / Real.exp 1) * Real.log (m : ℝ) ^ 4
          ≤ (64 * C / Real.exp 1) *
              ((64 * C / Real.exp 1)⁻¹ * (m : ℝ)) :=
        mul_le_mul_of_nonneg_left hm hK.le
      _ = (m : ℝ) := by field_simp
  have hexp : 0 < Real.exp 1 := Real.exp_pos 1
  calc
    64 * C * Real.log (m : ℝ) ^ 4 =
        Real.exp 1 * ((64 * C / Real.exp 1) *
          Real.log (m : ℝ) ^ 4) := by field_simp
    _ ≤ Real.exp 1 * (m : ℝ) :=
      mul_le_mul_of_nonneg_left hscaled hexp.le









theorem exists_threshold_sampling_density
    (C : ℝ) (hC : 0 < C) (u : ℕ) (hu : 1 ≤ u) :
    ∃ Q : ℕ, ∀ (m q : ℕ), Q ≤ q → q ≤ m →
      (m : ℝ) / (8 * C * Real.log (m : ℝ) ^ 2) ≤ (q : ℝ) →
        0 < (m : ℝ) / (Real.exp 1 * C * (q : ℝ) ^ (u + 1)) ∧
        (m : ℝ) / (Real.exp 1 * C * (q : ℝ) ^ (u + 1)) ≤ 1 := by
  obtain ⟨Q₀, hQ₀⟩ := Filter.eventually_atTop.mp
    (eventually_log_four_growth C hC)
  refine ⟨max 2 Q₀, ?_⟩
  intro m q hQq hqm hscale
  have hq2 : 2 ≤ q := (le_max_left 2 Q₀).trans hQq
  have hm2 : 2 ≤ m := hq2.trans hqm
  have hmQ₀ : Q₀ ≤ m := (le_max_right 2 Q₀).trans (hQq.trans hqm)
  have hgrowth :
      64 * C * Real.log (m : ℝ) ^ 4 ≤ Real.exp 1 * (m : ℝ) :=
    hQ₀ m hmQ₀
  have hmpos : 0 < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
  have hqone : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast (show 1 ≤ q by omega)
  have hlog : 0 < Real.log (m : ℝ) :=
    Real.log_pos (by exact_mod_cast hm2)
  have hscaleDen : 0 < 8 * C * Real.log (m : ℝ) ^ 2 := by positivity
  have hsmallLog : 8 * Real.log (m : ℝ) ^ 2 ≤ Real.exp 1 * (q : ℝ) := by
    calc
      8 * Real.log (m : ℝ) ^ 2 ≤
          (Real.exp 1 * (m : ℝ)) /
            (8 * C * Real.log (m : ℝ) ^ 2) := by
        apply (le_div_iff₀ hscaleDen).2
        calc
          8 * Real.log (m : ℝ) ^ 2 *
                (8 * C * Real.log (m : ℝ) ^ 2) =
              64 * C * Real.log (m : ℝ) ^ 4 := by ring
          _ ≤ Real.exp 1 * (m : ℝ) := hgrowth
      _ = Real.exp 1 *
          ((m : ℝ) / (8 * C * Real.log (m : ℝ) ^ 2)) := by ring
      _ ≤ Real.exp 1 * (q : ℝ) :=
        mul_le_mul_of_nonneg_left hscale (Real.exp_pos 1).le
  have hqpow : (q : ℝ) ≤ (q : ℝ) ^ u := by
    simpa only [pow_one] using pow_le_pow_right₀ hqone hu
  have hmUpper : (m : ℝ) ≤ Real.exp 1 * C * (q : ℝ) ^ (u + 1) := by
    have hmCleared :
        (m : ℝ) ≤ (q : ℝ) *
          (8 * C * Real.log (m : ℝ) ^ 2) :=
      (div_le_iff₀ hscaleDen).mp hscale
    calc
      (m : ℝ) ≤ (q : ℝ) *
          (8 * C * Real.log (m : ℝ) ^ 2) := hmCleared
      _ = C * (q : ℝ) * (8 * Real.log (m : ℝ) ^ 2) := by ring
      _ ≤ C * (q : ℝ) * (Real.exp 1 * (q : ℝ)) := by
        gcongr
      _ ≤ C * (q : ℝ) * (Real.exp 1 * (q : ℝ) ^ u) := by
        gcongr
      _ = Real.exp 1 * C * (q : ℝ) ^ (u + 1) := by
        rw [pow_succ]
        ring
  have hden : 0 < Real.exp 1 * C * (q : ℝ) ^ (u + 1) := by positivity
  exact ⟨div_pos hmpos hden, (div_le_one hden).2 hmUpper⟩

end Erdos920.DensitySide



















namespace Erdos920.MarkedTree

open Finset

section Definitions

variable {alpha : Type*} [DecidableEq alpha]


noncomputable def signatures : Nat -> Finset (List Bool)
  | 0 => {[]}
  | m + 1 => (signatures m).biUnion fun s => {false :: s, true :: s}







noncomputable def pathsOfSignature
    (children : List alpha -> Finset alpha)
    (marked : List alpha -> alpha -> Bool) : List Bool -> Finset (List alpha)
  | [] => {[]}
  | b :: bs =>
      (pathsOfSignature children marked bs).biUnion fun xs =>
        ((children xs).filter fun x => marked xs x = b).image fun x => x :: xs


def IsPath (children : List alpha -> Finset alpha) : List alpha -> Prop
  | [] => True
  | x :: xs => IsPath children xs /\ x ∈ children xs


def pathSignature (marked : List alpha -> alpha -> Bool) : List alpha -> List Bool
  | [] => []
  | x :: xs => marked xs x :: pathSignature marked xs






noncomputable def boundedPaths
    (children : List alpha -> Finset alpha)
    (marked : List alpha -> alpha -> Bool) (m w : Nat) : Finset (List alpha) :=
  (signatures m).filter (fun s => s.count false <= w) |>.biUnion
    (pathsOfSignature children marked)

end Definitions

section ElementaryProperties

variable {alpha : Type*}

@[simp] theorem mem_signatures_iff_length (s : List Bool) (m : Nat) :
    s ∈ signatures m <-> s.length = m := by
  induction m generalizing s with
  | zero => simp [signatures]
  | succ m ih =>
      cases s with
      | nil => simp [signatures]
      | cons b s =>
          cases b <;> simp [signatures, ih]

theorem card_signatures_le (m : Nat) :
    (signatures m).card <= 2 ^ m := by
  induction m with
  | zero => simp [signatures]
  | succ m ih =>
      calc
        (signatures (m + 1)).card <=
            ∑ s ∈ signatures m, ({false :: s, true :: s} : Finset (List Bool)).card := by
          simpa [signatures] using
            (Finset.card_biUnion_le
              (s := signatures m)
              (t := fun s => ({false :: s, true :: s} : Finset (List Bool))))
        _ = (signatures m).card * 2 := by simp
        _ <= 2 ^ m * 2 := Nat.mul_le_mul_right 2 ih
        _ = 2 ^ (m + 1) := by rw [pow_succ]

@[simp] theorem pathSignature_length
    (marked : List alpha -> alpha -> Bool) (xs : List alpha) :
    (pathSignature marked xs).length = xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [pathSignature, ih]

variable [DecidableEq alpha]

@[simp] theorem mem_pathsOfSignature_iff
    (children : List alpha -> Finset alpha)
    (marked : List alpha -> alpha -> Bool)
    (xs : List alpha) (s : List Bool) :
    xs ∈ pathsOfSignature children marked s <->
      IsPath children xs /\ pathSignature marked xs = s := by
  classical
  induction s generalizing xs with
  | nil =>
      cases xs <;> simp [pathsOfSignature, IsPath, pathSignature]
  | cons b bs ih =>
      cases xs with
      | nil => simp [pathsOfSignature, IsPath, pathSignature]
      | cons x xs =>
          simp [pathsOfSignature, IsPath, pathSignature, ih, and_assoc,
            and_left_comm, and_comm]

@[simp] theorem mem_boundedPaths_iff
    (children : List alpha -> Finset alpha)
    (marked : List alpha -> alpha -> Bool)
    (xs : List alpha) (m w : Nat) :
    xs ∈ boundedPaths children marked m w <->
      IsPath children xs /\ xs.length = m /\
        (pathSignature marked xs).count false <= w := by
  classical
  constructor
  · intro hxs
    simp only [boundedPaths] at hxs
    obtain ⟨s, hs, hpath⟩ := Finset.mem_biUnion.mp hxs
    have hs' := Finset.mem_filter.mp hs
    have hchar := (mem_pathsOfSignature_iff children marked xs s).mp hpath
    refine ⟨hchar.1, ?_, ?_⟩
    · rw [← pathSignature_length marked xs, hchar.2]
      exact (mem_signatures_iff_length s m).mp hs'.1
    · simpa [hchar.2] using hs'.2
  · rintro ⟨hpath, hlen, hunmarked⟩
    simp only [boundedPaths]
    apply Finset.mem_biUnion.mpr
    refine ⟨pathSignature marked xs, ?_, ?_⟩
    · apply Finset.mem_filter.mpr
      exact ⟨(mem_signatures_iff_length _ _).mpr (by simpa using hlen), hunmarked⟩
    · exact (mem_pathsOfSignature_iff children marked xs _).mpr ⟨hpath, rfl⟩

end ElementaryProperties

section Counting

variable {alpha : Type*} [DecidableEq alpha]



private theorem pow_mul_pow_le_pow_mul_pow
    {h Delta j w m : Nat} (hhDelta : h <= Delta) (hjw : j <= w) (hwm : w <= m) :
    Delta ^ j * h ^ (m - j) <= Delta ^ w * h ^ (m - w) := by
  have hmj : m - j = (m - w) + (w - j) := by omega
  calc
    Delta ^ j * h ^ (m - j) =
        (Delta ^ j * h ^ (m - w)) * h ^ (w - j) := by
          rw [hmj, pow_add]
          ac_rfl
    _ <= (Delta ^ j * h ^ (m - w)) * Delta ^ (w - j) :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hhDelta _)
    _ = Delta ^ (j + (w - j)) * h ^ (m - w) := by
      rw [pow_add]
      ac_rfl
    _ = Delta ^ w * h ^ (m - w) := by
      rw [Nat.add_sub_of_le hjw]


theorem card_pathsOfSignature_le
    (children : List alpha -> Finset alpha)
    (marked : List alpha -> alpha -> Bool)
    {Delta h : Nat}
    (hchildren : ∀ xs, (children xs).card <= Delta)
    (hmarked : ∀ xs,
      ((children xs).filter fun x => marked xs x = true).card <= h)
    (s : List Bool) :
    (pathsOfSignature children marked s).card <=
      Delta ^ s.count false * h ^ s.count true := by
  classical
  induction s with
  | nil => simp [pathsOfSignature]
  | cons b bs ih =>
      let stepBound := if b then h else Delta
      have hone (xs : List alpha) :
          (((children xs).filter fun x => marked xs x = b).image fun x => x :: xs).card <=
            stepBound := by
        refine Finset.card_image_le.trans ?_
        cases b with
        | false =>
            exact (Finset.card_filter_le _ _).trans (hchildren xs)
        | true =>
            simpa [stepBound] using hmarked xs
      calc
        (pathsOfSignature children marked (b :: bs)).card <=
            ∑ xs ∈ pathsOfSignature children marked bs,
              ((((children xs).filter fun x => marked xs x = b).image
                fun x => x :: xs).card) := by
          simpa [pathsOfSignature] using
            (Finset.card_biUnion_le
              (s := pathsOfSignature children marked bs)
              (t := fun xs =>
                ((children xs).filter fun x => marked xs x = b).image fun x => x :: xs))
        _ <= ∑ _xs ∈ pathsOfSignature children marked bs, stepBound := by
          exact Finset.sum_le_sum fun xs _ => hone xs
        _ = (pathsOfSignature children marked bs).card * stepBound := by simp
        _ <= (Delta ^ bs.count false * h ^ bs.count true) * stepBound :=
          Nat.mul_le_mul_right stepBound ih
        _ = Delta ^ (b :: bs).count false * h ^ (b :: bs).count true := by
          cases b <;> simp [stepBound, pow_succ] <;> ac_rfl







theorem card_boundedPaths_le
    (children : List alpha -> Finset alpha)
    (marked : List alpha -> alpha -> Bool)
    {Delta h m w : Nat}
    (hchildren : ∀ xs, (children xs).card <= Delta)
    (hmarked : ∀ xs,
      ((children xs).filter fun x => marked xs x = true).card <= h)
    (hhDelta : h <= Delta) (hwm : w <= m) :
    (boundedPaths children marked m w).card <=
      2 ^ m * Delta ^ w * h ^ (m - w) := by
  classical
  let S := (signatures m).filter fun s => s.count false <= w
  let B := Delta ^ w * h ^ (m - w)
  have hper (s : List Bool) (hs : s ∈ S) :
      (pathsOfSignature children marked s).card <= B := by
    have hs' := Finset.mem_filter.mp hs
    have hlen : s.length = m := (mem_signatures_iff_length s m).mp hs'.1
    have htrue : s.count true = m - s.count false := by
      have hcounts := List.count_false_add_count_true s
      omega
    calc
      (pathsOfSignature children marked s).card <=
          Delta ^ s.count false * h ^ s.count true :=
        card_pathsOfSignature_le children marked hchildren hmarked s
      _ = Delta ^ s.count false * h ^ (m - s.count false) := by rw [htrue]
      _ <= Delta ^ w * h ^ (m - w) :=
        pow_mul_pow_le_pow_mul_pow hhDelta hs'.2 hwm
      _ = B := rfl
  have hScard : S.card <= 2 ^ m := by
    exact (Finset.card_filter_le _ _).trans (card_signatures_le m)
  calc
    (boundedPaths children marked m w).card <=
        ∑ s ∈ S, (pathsOfSignature children marked s).card := by
      simpa [boundedPaths, S] using
        (Finset.card_biUnion_le
          (s := S) (t := pathsOfSignature children marked))
    _ <= ∑ _s ∈ S, B := Finset.sum_le_sum fun s hs => hper s hs
    _ = S.card * B := by simp
    _ <= 2 ^ m * B := Nat.mul_le_mul_right B hScard
    _ = 2 ^ m * Delta ^ w * h ^ (m - w) := by
      simp only [B, Nat.mul_assoc]

end Counting

end Erdos920.MarkedTree
















namespace Erdos920.Container

open scoped BigOperators

variable {P : Type*} [DecidableEq P]




structure RankClosure (P : Type*) [DecidableEq P] where
  rank : Finset P → ℕ
  Cl : P → Finset P → Prop
  decidable_cl : ∀ x S, Decidable (Cl x S)
  rank_mono_insert : ∀ (S : Finset P) (x : P), rank S ≤ rank (insert x S)
  rank_insert_le : ∀ (S : Finset P) (x : P), rank (insert x S) ≤ rank S + 1
  rank_insert_of_not_cl : ∀ (S : Finset P) (x : P), ¬ Cl x S → rank (insert x S) = rank S + 1

instance instRankClosureDecidableCl {P : Type*} [DecidableEq P] (C : RankClosure P)
    (x : P) (S : Finset P) : Decidable (C.Cl x S) :=
  C.decidable_cl x S



def generators (R : P → P → Prop) [DecidableRel R]
    (σ : List (P × P)) (y : P) : Finset P :=
  ((σ.toFinset.filter fun p => R p.1 y).image Prod.snd)

@[simp] lemma generators_nil (R : P → P → Prop) [DecidableRel R] (y : P) :
    generators R [] y = ∅ := by
  simp [generators]

@[simp] lemma generators_cons (R : P → P → Prop) [DecidableRel R]
    (p : P × P) (σ : List (P × P)) (y : P) :
    generators R (p :: σ) y = if R p.1 y then insert p.2 (generators R σ y)
      else generators R σ y := by
  unfold generators
  rw [List.toFinset_cons, Finset.filter_insert]
  split
  · rw [Finset.image_insert]
  · rfl


def prefixRank (C : RankClosure P) (R : P → P → Prop) [DecidableRel R]
    (σ : List (P × P)) (y : P) : ℕ :=
  C.rank (generators R σ y)


def U (points : Finset P) (C : RankClosure P) (R : P → P → Prop)
    [DecidableRel R] (σ : List (P × P)) (j : ℕ) : Finset P :=
  points.filter fun y => prefixRank C R σ y ≤ j


def Z (points : Finset P) (C : RankClosure P) (R : P → P → Prop)
    [DecidableRel R] (σ : List (P × P)) (j : ℕ) : Finset P :=
  points.filter fun y => prefixRank C R σ y = j

lemma Z_subset_U (points : Finset P) (C : RankClosure P) (R : P → P → Prop)
    [DecidableRel R] (σ : List (P × P)) (j : ℕ) :
    Z points C R σ j ⊆ U points C R σ j := by
  intro y hy
  simp only [Z, Finset.mem_filter] at hy
  simp [U, hy.1, hy.2.le]

lemma U_mono_cons (points : Finset P) (C : RankClosure P) (R : P → P → Prop)
    [DecidableRel R] (p : P × P) (σ : List (P × P)) (j : ℕ) :
    U points C R (p :: σ) j ⊆ U points C R σ j := by
  intro y hy
  rcases Finset.mem_filter.mp hy with ⟨hypoints, hrank⟩
  apply Finset.mem_filter.mpr
  refine ⟨hypoints, ?_⟩
  simp only [prefixRank, generators_cons] at hrank ⊢
  split at hrank
  · exact (C.rank_mono_insert _ _).trans hrank
  · exact hrank



def CanExtend (R : P → P → Prop) (p : P × P) (σ : List (P × P)) : Prop :=
  R p.1 p.2 ∧ ∀ old ∈ σ, R old.1 p.2 → R p.1 old.2

noncomputable instance instDecidableCanExtend (R : P → P → Prop)
    (p : P × P) (σ : List (P × P)) : Decidable (CanExtend R p σ) :=
  Classical.propDecidable _



def Consistent (R : P → P → Prop) : List (P × P) → Prop
  | [] => True
  | p :: σ => Consistent R σ ∧ CanExtend R p σ

omit [DecidableEq P] in
@[simp] lemma consistent_nil (R : P → P → Prop) : Consistent R [] := trivial

omit [DecidableEq P] in
@[simp] lemma consistent_cons_iff (R : P → P → Prop) (p : P × P)
    (σ : List (P × P)) :
    Consistent R (p :: σ) ↔ Consistent R σ ∧ CanExtend R p σ := Iff.rfl



noncomputable def relationPairs (points : Finset P) (R : P → P → Prop)
    [DecidableRel R] : Finset (P × P) :=
  points.biUnion fun a => (points.filter fun b => R a b).image fun b => (a, b)

@[simp] theorem mem_relationPairs_iff (points : Finset P) (R : P → P → Prop)
    [DecidableRel R] (p : P × P) :
    p ∈ relationPairs points R ↔ p.1 ∈ points ∧ p.2 ∈ points ∧ R p.1 p.2 := by
  classical
  constructor
  · intro hp
    obtain ⟨a, ha, hpimg⟩ := Finset.mem_biUnion.mp hp
    obtain ⟨b, hb, hab⟩ := Finset.mem_image.mp hpimg
    have hab' := Finset.mem_filter.mp hb
    cases hab
    exact ⟨ha, hab'.1, hab'.2⟩
  · rintro ⟨ha, hb, hR⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨p.1, ha, ?_⟩
    apply Finset.mem_image.mpr
    exact ⟨p.2, Finset.mem_filter.mpr ⟨hb, hR⟩, Prod.ext rfl rfl⟩



noncomputable def extensionChildren (points : Finset P) (R : P → P → Prop)
    [DecidableRel R] (σ : List (P × P)) : Finset (P × P) :=
  (relationPairs points R).filter fun p => CanExtend R p σ

lemma extensionChildren_subset_relationPairs
    (points : Finset P) (R : P → P → Prop) [DecidableRel R]
    (σ : List (P × P)) : extensionChildren points R σ ⊆ relationPairs points R :=
  by
    classical
    simp [extensionChildren]



theorem relationPairs_card_le (points : Finset P) (R : P → P → Prop)
    [DecidableRel R] (d : ℕ)
    (hdegree : ∀ a ∈ points, (points.filter fun b => R a b).card ≤ d) :
    (relationPairs points R).card ≤ points.card * d := by
  classical
  calc
    (relationPairs points R).card ≤
        ∑ a ∈ points, ((points.filter fun b => R a b).image fun b => (a, b)).card := by
      exact Finset.card_biUnion_le
    _ ≤ ∑ _a ∈ points, d := by
      exact Finset.sum_le_sum fun a ha => Finset.card_image_le.trans (hdegree a ha)
    _ = points.card * d := by simp

theorem extensionChildren_card_le (points : Finset P) (R : P → P → Prop)
    [DecidableRel R] (d : ℕ)
    (hdegree : ∀ a ∈ points, (points.filter fun b => R a b).card ≤ d)
    (σ : List (P × P)) :
    (extensionChildren points R σ).card ≤ points.card * d :=
  (Finset.card_le_card (extensionChildren_subset_relationPairs points R σ)).trans
    (relationPairs_card_le points R d hdegree)

theorem isPath_extensionChildren_consistent
    (points : Finset P) (R : P → P → Prop) [DecidableRel R]
    {xs : List (P × P)}
    (hpath : Erdos920.MarkedTree.IsPath (extensionChildren points R) xs) :
    Consistent R xs := by
  induction xs with
  | nil => trivial
  | cons x xs ih =>
      rcases hpath with ⟨hpath, hx⟩
      have hx' : x ∈ (relationPairs points R).filter fun p => CanExtend R p xs := by
        simpa [extensionChildren] using hx
      exact ⟨ih hpath, (Finset.mem_filter.mp hx').2⟩




def neighborsInStratum (points : Finset P) (C : RankClosure P)
    (R : P → P → Prop) [DecidableRel R] (σ : List (P × P)) (ℓ : ℕ) (a : P) :
    Finset P :=
  (Z points C R σ ℓ).filter fun y => R a y


def closureInStratum (points : Finset P) (C : RankClosure P)
    (R : P → P → Prop) [DecidableRel R] (σ : List (P × P)) (ℓ : ℕ) (b : P) :
    Finset P :=
  (Z points C R σ ℓ).filter fun y => C.Cl b (generators R σ y)



def Poor (points : Finset P) (C : RankClosure P) (R : P → P → Prop)
    [DecidableRel R] (σ : List (P × P)) (ℓ cut : ℕ) (a : P) : Prop :=
  (neighborsInStratum points C R σ ℓ a).card < 2 * cut

instance instDecidablePoor (points : Finset P) (C : RankClosure P)
    (R : P → P → Prop) [DecidableRel R] (σ : List (P × P)) (ℓ cut : ℕ)
    (a : P) : Decidable (Poor points C R σ ℓ cut a) := by
  unfold Poor
  exact Nat.decLt _ _



def Popular (points : Finset P) (C : RankClosure P) (R : P → P → Prop)
    [DecidableRel R] (σ : List (P × P)) (ℓ cut : ℕ) (b : P) : Prop :=
  cut ≤ (closureInStratum points C R σ ℓ b).card

instance instDecidablePopular (points : Finset P) (C : RankClosure P)
    (R : P → P → Prop) [DecidableRel R] (σ : List (P × P)) (ℓ cut : ℕ)
    (b : P) : Decidable (Popular points C R σ ℓ cut b) := by
  unfold Popular
  exact Nat.decLe _ _



def rankRaisingSet (points : Finset P) (C : RankClosure P)
    (R : P → P → Prop) [DecidableRel R] (σ : List (P × P)) (ℓ : ℕ)
    (a b : P) : Finset P :=
  (Z points C R σ ℓ).filter fun y => R a y ∧ ¬ C.Cl b (generators R σ y)



noncomputable def markedByPoorOrPopular {L : Type*}
    (points : Finset P) (C : RankClosure P) (R : P → P → Prop)
    [DecidableRel R] (level : List (P × P) → (P × P) → L)
    (levelNat : L → ℕ) (cut : List (P × P) → (P × P) → ℕ)
    (σ : List (P × P)) (p : P × P) : Bool :=
  decide (Poor points C R σ (levelNat (level σ p)) (cut σ p) p.1 ∨
    Popular points C R σ (levelNat (level σ p)) (cut σ p) p.2)

theorem markedByPoorOrPopular_eq_false_iff {L : Type*}
    (points : Finset P) (C : RankClosure P) (R : P → P → Prop)
    [DecidableRel R] (level : List (P × P) → (P × P) → L)
    (levelNat : L → ℕ) (cut : List (P × P) → (P × P) → ℕ)
    (σ : List (P × P)) (p : P × P) :
    markedByPoorOrPopular points C R level levelNat cut σ p = false ↔
      ¬ Poor points C R σ (levelNat (level σ p)) (cut σ p) p.1 ∧
      ¬ Popular points C R σ (levelNat (level σ p)) (cut σ p) p.2 := by
  classical
  simp [markedByPoorOrPopular]


theorem markedChildren_card_le {L : Type*}
    (points : Finset P) (C : RankClosure P) (R : P → P → Prop)
    [DecidableRel R] (level : List (P × P) → (P × P) → L)
    (levelNat : L → ℕ) (cut : List (P × P) → (P × P) → ℕ)
    (σ : List (P × P)) (hp hq : ℕ)
    (hpoor : ((extensionChildren points R σ).filter fun p =>
      Poor points C R σ (levelNat (level σ p)) (cut σ p) p.1).card ≤ hp)
    (hpopular : ((extensionChildren points R σ).filter fun p =>
      Popular points C R σ (levelNat (level σ p)) (cut σ p) p.2).card ≤ hq) :
    ((extensionChildren points R σ).filter fun p =>
      markedByPoorOrPopular points C R level levelNat cut σ p = true).card ≤ hp + hq := by
  classical
  let poorChildren := (extensionChildren points R σ).filter fun p =>
    Poor points C R σ (levelNat (level σ p)) (cut σ p) p.1
  let popularChildren := (extensionChildren points R σ).filter fun p =>
    Popular points C R σ (levelNat (level σ p)) (cut σ p) p.2
  have hsubset :
      (extensionChildren points R σ).filter (fun p =>
        markedByPoorOrPopular points C R level levelNat cut σ p = true) ⊆
        poorChildren ∪ popularChildren := by
    intro p hpmark
    have hp' := Finset.mem_filter.mp hpmark
    have hor : Poor points C R σ (levelNat (level σ p)) (cut σ p) p.1 ∨
        Popular points C R σ (levelNat (level σ p)) (cut σ p) p.2 := by
      simpa [markedByPoorOrPopular] using hp'.2
    rcases hor with hor | hor
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hp'.1, hor⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hp'.1, hor⟩)
  calc
    ((extensionChildren points R σ).filter fun p =>
      markedByPoorOrPopular points C R level levelNat cut σ p = true).card ≤
        (poorChildren ∪ popularChildren).card := Finset.card_le_card hsubset
    _ ≤ poorChildren.card + popularChildren.card :=
      Finset.card_union_le poorChildren popularChildren
    _ ≤ hp + hq := Nat.add_le_add hpoor hpopular

omit [DecidableEq P] in

lemma card_filter_and_not_ge {s : Finset P} {A B : P → Prop}
    [DecidablePred A] [DecidablePred B] {cut : ℕ}
    (hA : 2 * cut ≤ (s.filter A).card) (hB : (s.filter B).card ≤ cut) :
    cut ≤ (s.filter fun x => A x ∧ ¬ B x).card := by
  classical
  let a := s.filter A
  let b := s.filter B
  have hdiff : a \ b = s.filter fun x => A x ∧ ¬ B x := by
    ext x
    by_cases hx : x ∈ s <;> simp [a, b, hx]
  have hinter : (a ∩ b).card ≤ b.card :=
    Finset.card_le_card (by intro x hx; exact Finset.mem_of_mem_inter_right hx)
  have hsplit := Finset.card_sdiff_add_card_inter a b
  rw [hdiff] at hsplit
  dsimp [a, b] at hinter hsplit
  omega

lemma rankRaisingSet_card_ge_of_not_poor_not_popular
    (points : Finset P) (C : RankClosure P) (R : P → P → Prop)
    [DecidableRel R] (σ : List (P × P)) (ℓ cut : ℕ) (a b : P)
    (ha : ¬ Poor points C R σ ℓ cut a)
    (hb : ¬ Popular points C R σ ℓ cut b) :
    cut ≤ (rankRaisingSet points C R σ ℓ a b).card := by
  apply card_filter_and_not_ge
  · simpa [Poor, neighborsInStratum] using (Nat.le_of_not_gt ha)
  · simpa [Popular, closureInStratum] using (Nat.le_of_lt (Nat.lt_of_not_ge hb))

lemma rankRaisingSet_subset_U_diff
    (points : Finset P) (C : RankClosure P) (R : P → P → Prop)
    [DecidableRel R] (σ : List (P × P)) (ℓ : ℕ) (a b : P) :
    rankRaisingSet points C R σ ℓ a b ⊆
      U points C R σ ℓ \ U points C R ((a, b) :: σ) ℓ := by
  intro y hy
  simp only [rankRaisingSet, Finset.mem_filter, Z] at hy
  have hyOld : prefixRank C R σ y = ℓ := hy.1.2
  have hyNew : prefixRank C R ((a, b) :: σ) y = ℓ + 1 := by
    simp only [prefixRank, generators_cons, hy.2.1, if_true]
    rw [C.rank_insert_of_not_cl _ _ hy.2.2]
    exact congrArg (fun n => n + 1) hyOld
  apply Finset.mem_sdiff.mpr
  refine ⟨?_, ?_⟩
  · exact Finset.mem_filter.mpr ⟨hy.1.1, hyOld.le⟩
  · intro h
    have hle : prefixRank C R ((a, b) :: σ) y ≤ ℓ := (Finset.mem_filter.mp h).2
    rw [hyNew] at hle
    omega




theorem U_card_add_cut_le_of_not_poor_not_popular
    (points : Finset P) (C : RankClosure P) (R : P → P → Prop)
    [DecidableRel R] (σ : List (P × P)) (ℓ cut : ℕ) (a b : P)
    (ha : ¬ Poor points C R σ ℓ cut a)
    (hb : ¬ Popular points C R σ ℓ cut b) :
    (U points C R ((a, b) :: σ) ℓ).card + cut ≤
      (U points C R σ ℓ).card := by
  have hmono := U_mono_cons points C R (a, b) σ ℓ
  have hraise := rankRaisingSet_subset_U_diff points C R σ ℓ a b
  have hcard := rankRaisingSet_card_ge_of_not_poor_not_popular
    points C R σ ℓ cut a b ha hb
  have hdisj : Disjoint (U points C R ((a, b) :: σ) ℓ)
      (rankRaisingSet points C R σ ℓ a b) := by
    apply Finset.disjoint_left.mpr
    intro y hyNew hyRaise
    exact (Finset.mem_sdiff.mp (hraise hyRaise)).2 hyNew
  have hunion :
      U points C R ((a, b) :: σ) ℓ ∪ rankRaisingSet points C R σ ℓ a b ⊆
        U points C R σ ℓ := by
    intro y hy
    rcases Finset.mem_union.mp hy with hy | hy
    · exact hmono hy
    · exact (Finset.mem_sdiff.mp (hraise hy)).1
  have hsum :
      (U points C R ((a, b) :: σ) ℓ).card +
          (rankRaisingSet points C R σ ℓ a b).card ≤
        (U points C R σ ℓ).card := by
    rw [← Finset.card_union_of_disjoint hdisj]
    exact Finset.card_le_card hunion
  omega




theorem U_card_multiplicative_shrink
    (points : Finset P) (C : RankClosure P) (R : P → P → Prop)
    [DecidableRel R] (σ : List (P × P)) (ℓ cut K : ℕ) (a b : P)
    (hK : 1 ≤ K) (hcut : (U points C R σ ℓ).card ≤ K * cut)
    (ha : ¬ Poor points C R σ ℓ cut a)
    (hb : ¬ Popular points C R σ ℓ cut b) :
    K * (U points C R ((a, b) :: σ) ℓ).card ≤
      (K - 1) * (U points C R σ ℓ).card := by
  have hshrink := U_card_add_cut_le_of_not_poor_not_popular
    points C R σ ℓ cut a b ha hb
  have hKm : K - 1 + 1 = K := Nat.sub_add_cancel hK
  nlinarith



omit [DecidableEq P] in

lemma sum_card_filter_eq_sum_card_filter (s t : Finset P) (I : P → P → Prop)
    [DecidableRel I] :
    ∑ x ∈ s, (t.filter fun y => I x y).card =
      ∑ y ∈ t, (s.filter fun x => I x y).card := by
  calc
    ∑ x ∈ s, (t.filter fun y => I x y).card =
        ∑ x ∈ s, ∑ y ∈ t, if I x y then 1 else 0 := by
          congr 1 with x
          exact Finset.card_filter _ _
    _ = ∑ y ∈ t, ∑ x ∈ s, if I x y then 1 else 0 := Finset.sum_comm
    _ = ∑ y ∈ t, (s.filter fun x => I x y).card := by
          congr 1 with y
          exact (Finset.card_filter _ _).symm

omit [DecidableEq P] in



theorem popular_card_mul_cut_le (s t : Finset P) (I : P → P → Prop)
    [DecidableRel I] (cut cap : ℕ)
    (hfibre : ∀ y ∈ t, (s.filter fun x => I x y).card ≤ cap) :
    ((s.filter fun x => cut ≤ (t.filter fun y => I x y).card).card) * cut ≤
      t.card * cap := by
  let pop := s.filter fun x => cut ≤ (t.filter fun y => I x y).card
  have hleft : pop.card * cut ≤ ∑ x ∈ pop, (t.filter fun y => I x y).card := by
    rw [Finset.card_eq_sum_ones, Finset.sum_mul]
    exact Finset.sum_le_sum fun x hx => by
      simpa [pop] using (Finset.mem_filter.mp hx).2
  have hsub :
      ∑ x ∈ pop, (t.filter fun y => I x y).card ≤
        ∑ x ∈ s, (t.filter fun y => I x y).card := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro x hx
      exact (Finset.mem_filter.mp hx).1
    · intro i hi _
      exact Nat.zero_le _
  have hright : ∑ y ∈ t, (s.filter fun x => I x y).card ≤ t.card * cap := by
    rw [Finset.card_eq_sum_ones, Finset.sum_mul]
    exact Finset.sum_le_sum fun y hy => by simpa using hfibre y hy
  dsimp [pop] at hleft ⊢
  exact hleft.trans (hsub.trans ((sum_card_filter_eq_sum_card_filter s t I).le.trans hright))

theorem popularInStratum_card_mul_cut_le
    (points : Finset P) (C : RankClosure P) (R : P → P → Prop)
    [DecidableRel R] (σ : List (P × P)) (ℓ cut cap : ℕ)
    (hfibre : ∀ y ∈ Z points C R σ ℓ,
      (points.filter fun b => C.Cl b (generators R σ y)).card ≤ cap) :
    ((points.filter fun b => Popular points C R σ ℓ cut b).card) * cut ≤
      (Z points C R σ ℓ).card * cap := by
  classical
  change
    ((points.filter fun b => cut ≤
      ((Z points C R σ ℓ).filter fun y => C.Cl b (generators R σ y)).card).card) * cut ≤
        (Z points C R σ ℓ).card * cap
  exact popular_card_mul_cut_le points (Z points C R σ ℓ)
    (fun b y => C.Cl b (generators R σ y)) cut cap hfibre





theorem pow_count_mul_last_le
    {m K : ℕ} (V : Fin (m + 1) → ℕ) (contract : Fin m → Bool)
    (hmono : ∀ i : Fin m, V i.succ ≤ V i.castSucc)
    (hcontract : ∀ i : Fin m, contract i = true →
      K * V i.succ ≤ (K - 1) * V i.castSucc) :
    K ^ (List.ofFn contract).count true * V (Fin.last m) ≤
      (K - 1) ^ (List.ofFn contract).count true * V 0 := by
  induction m with
  | zero => simp
  | succ m ih =>
      let V' : Fin (m + 1) → ℕ := fun i => V i.succ
      let contract' : Fin m → Bool := fun i => contract i.succ
      have hmono' : ∀ i : Fin m, V' i.succ ≤ V' i.castSucc := by
        intro i
        exact hmono i.succ
      have hcontract' : ∀ i : Fin m, contract' i = true →
          K * V' i.succ ≤ (K - 1) * V' i.castSucc := by
        intro i hi
        exact hcontract i.succ hi
      have hi := ih V' contract' hmono' hcontract'
      rw [List.ofFn_succ]
      change
        K ^ ((contract 0 :: List.ofFn contract').count true) * V (Fin.last (m + 1)) ≤
          (K - 1) ^ ((contract 0 :: List.ofFn contract').count true) * V 0
      have hlast : V' (Fin.last m) = V (Fin.last (m + 1)) := rfl
      rw [← hlast]
      cases h0 : contract 0 with
      | false =>
          simp only [List.count_cons]
          exact hi.trans (Nat.mul_le_mul_left _ (hmono 0))
      | true =>
          simp only [List.count_cons, beq_self_eq_true, if_true, pow_succ]
          calc
            (K ^ (List.ofFn contract').count true * K) * V' (Fin.last m) =
                K * (K ^ (List.ofFn contract').count true * V' (Fin.last m)) := by
                  ac_rfl
            _ ≤ K * ((K - 1) ^ (List.ofFn contract').count true * V' 0) :=
              Nat.mul_le_mul_left K hi
            _ = (K - 1) ^ (List.ofFn contract').count true * (K * V' 0) := by
              ac_rfl
            _ ≤ (K - 1) ^ (List.ofFn contract').count true * ((K - 1) * V 0) :=
              Nat.mul_le_mul_left _ (hcontract 0 h0)
            _ = ((K - 1) ^ (List.ofFn contract').count true * (K - 1)) * V 0 := by
              ac_rfl




lemma shifted_contraction {K A B : ℕ} (hK : 1 ≤ K) (hB : 1 ≤ B)
    (h : K * A ≤ (K - 1) * B) :
    (2 * K) * (A + 1) ≤ (2 * K - 1) * (B + 1) := by
  have hKm : K - 1 + 1 = K := Nat.sub_add_cancel hK
  have htwok : 2 * K - 1 + 1 = 2 * K := Nat.sub_add_cancel (by omega : 1 ≤ 2 * K)
  nlinarith



theorem power_stopping_of_at_succ {K N w : ℕ} (hK : 1 ≤ K)
    (hstop : (2 * K - 1) ^ (w + 1) * (N + 1) < (2 * K) ^ (w + 1)) :
    ∀ c : ℕ, w < c → (2 * K - 1) ^ c * (N + 1) < (2 * K) ^ c := by
  intro c hc
  obtain ⟨r, hr⟩ := Nat.exists_eq_add_of_le (show w + 1 ≤ c by omega)
  rw [hr, pow_add (2 * K - 1) (w + 1) r, pow_add (2 * K) (w + 1) r]
  have hbase : 0 < 2 * K - 1 := by omega
  calc
    ((2 * K - 1) ^ (w + 1) * (2 * K - 1) ^ r) * (N + 1) =
        (2 * K - 1) ^ r * ((2 * K - 1) ^ (w + 1) * (N + 1)) := by ac_rfl
    _ < (2 * K - 1) ^ r * (2 * K) ^ (w + 1) :=
      Nat.mul_lt_mul_of_pos_left hstop (Nat.pow_pos hbase)
    _ ≤ (2 * K) ^ r * (2 * K) ^ (w + 1) :=
      Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (by omega : 2 * K - 1 ≤ 2 * K) r)
    _ = (2 * K) ^ (w + 1) * (2 * K) ^ r := by ac_rfl




theorem count_contract_le_of_potential
    {m K N w : ℕ} (V : Fin (m + 1) → ℕ) (contract : Fin m → Bool)
    (hK : 1 ≤ K) (hV0 : V 0 ≤ N)
    (hmono : ∀ i : Fin m, V i.succ ≤ V i.castSucc)
    (hpositive : ∀ i : Fin m, contract i = true → 1 ≤ V i.castSucc)
    (hcontract : ∀ i : Fin m, contract i = true →
      K * V i.succ ≤ (K - 1) * V i.castSucc)
    (hpow : ∀ c : ℕ, w < c →
      (2 * K - 1) ^ c * (N + 1) < (2 * K) ^ c) :
    (List.ofFn contract).count true ≤ w := by
  let V' : Fin (m + 1) → ℕ := fun i => V i + 1
  have hmono' : ∀ i : Fin m, V' i.succ ≤ V' i.castSucc := by
    intro i
    exact Nat.add_le_add_right (hmono i) 1
  have hcontract' : ∀ i : Fin m, contract i = true →
      (2 * K) * V' i.succ ≤ (2 * K - 1) * V' i.castSucc := by
    intro i hi
    exact shifted_contraction hK (hpositive i hi) (hcontract i hi)
  have hprod := pow_count_mul_last_le V' contract hmono' hcontract'
  by_contra hc
  have hwc : w < (List.ofFn contract).count true := Nat.lt_of_not_ge hc
  have hstrict := hpow _ hwc
  have hfinal : 1 ≤ V' (Fin.last m) := by simp [V']
  have hstart : V' 0 ≤ N + 1 := Nat.add_le_add_right hV0 1
  have hbad :
      (2 * K) ^ (List.ofFn contract).count true ≤
        (2 * K - 1) ^ (List.ofFn contract).count true * (N + 1) := by
    have hbad' := (Nat.mul_le_mul_left _ hfinal).trans
      (hprod.trans (Nat.mul_le_mul_left _ hstart))
    simpa only [Nat.mul_one] using hbad'
  omega


lemma card_eq_sum_card_fibers {I L : Type*} [Fintype L]
    [DecidableEq L] (s : Finset I) (label : I → L) :
    s.card = ∑ ℓ : L, (s.filter fun i => label i = ℓ).card := by
  classical
  rw [Finset.card_eq_sum_ones]
  calc
    ∑ _i ∈ s, 1 = ∑ i ∈ s, ∑ ℓ : L, if label i = ℓ then 1 else 0 := by simp
    _ = ∑ ℓ : L, ∑ i ∈ s, if label i = ℓ then 1 else 0 := Finset.sum_comm
    _ = ∑ ℓ : L, (s.filter fun i => label i = ℓ).card := by
      apply Finset.sum_congr rfl
      intro ℓ _
      exact (Finset.card_filter _ _).symm



theorem card_le_levels_mul_of_fibers_le {I L : Type*}
    [Fintype L] [DecidableEq L] (s : Finset I) (label : I → L) (r : ℕ)
    (hfibre : ∀ ℓ : L, (s.filter fun i => label i = ℓ).card ≤ r) :
    s.card ≤ Fintype.card L * r := by
  rw [card_eq_sum_card_fibers s label]
  calc
    ∑ ℓ : L, (s.filter fun i => label i = ℓ).card ≤ ∑ _ℓ : L, r :=
      Finset.sum_le_sum fun ℓ _ => hfibre ℓ
    _ = Fintype.card L * r := by simp




def unmarkedCount {A : Type*} (marked : List A → A → Bool) : List A → ℕ
  | [] => 0
  | x :: xs => unmarkedCount marked xs + if marked xs x = false then 1 else 0


def selectedCount {A L : Type*} [DecidableEq L]
    (marked : List A → A → Bool) (level : List A → A → L) (ℓ : L) : List A → ℕ
  | [] => 0
  | x :: xs => selectedCount marked level ℓ xs +
      if marked xs x = false ∧ level xs x = ℓ then 1 else 0

@[simp] lemma unmarkedCount_eq_count_false {A : Type*}
    (marked : List A → A → Bool) (xs : List A) :
    unmarkedCount marked xs =
      (Erdos920.MarkedTree.pathSignature marked xs).count false := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [unmarkedCount, Erdos920.MarkedTree.pathSignature, List.count_cons, ih]
      cases marked xs x <;> simp

lemma unmarkedCount_eq_sum_selectedCount {A L : Type*} [Fintype L] [DecidableEq L]
    (marked : List A → A → Bool) (level : List A → A → L) (xs : List A) :
    unmarkedCount marked xs = ∑ ℓ : L, selectedCount marked level ℓ xs := by
  classical
  induction xs with
  | nil => simp [unmarkedCount, selectedCount]
  | cons x xs ih =>
      rw [unmarkedCount, ih]
      simp only [selectedCount, Finset.sum_add_distrib]
      by_cases hm : marked xs x = false <;> simp [hm]



structure PathShrinkCertificate {A L : Type*} [DecidableEq A] [Fintype L]
    (children : List A → Finset A) (marked : List A → A → Bool)
    (K N : ℕ) where
  potential : L → List A → ℕ
  level : List A → A → L
  initial_le : ∀ ℓ, potential ℓ [] ≤ N
  mono : ∀ ℓ σ x, x ∈ children σ → potential ℓ (x :: σ) ≤ potential ℓ σ
  positive : ∀ σ x, x ∈ children σ → marked σ x = false →
    1 ≤ potential (level σ x) σ
  contract : ∀ σ x, x ∈ children σ → marked σ x = false →
    K * potential (level σ x) (x :: σ) ≤
      (K - 1) * potential (level σ x) σ





noncomputable def rankPathShrinkCertificate {L : Type*} [Fintype L] [DecidableEq L]
    (points : Finset P) (C : RankClosure P) (R : P → P → Prop)
    [DecidableRel R] (level : List (P × P) → (P × P) → L)
    (levelNat : L → ℕ) (cut : List (P × P) → (P × P) → ℕ)
    (K : ℕ) (hK : 1 ≤ K)
    (hpivot : ∀ σ p, p ∈ extensionChildren points R σ →
      (Z points C R σ (levelNat (level σ p))).Nonempty)
    (hcut : ∀ σ p, p ∈ extensionChildren points R σ →
      (U points C R σ (levelNat (level σ p))).card ≤ K * cut σ p) :
    PathShrinkCertificate (L := L) (extensionChildren points R)
      (markedByPoorOrPopular points C R level levelNat cut) K points.card where
  potential ℓ σ := (U points C R σ (levelNat ℓ)).card
  level := level
  initial_le ℓ := Finset.card_filter_le _ _
  mono ℓ σ p _ := Finset.card_le_card (U_mono_cons points C R p σ (levelNat ℓ))
  positive σ p hp _ := by
    obtain ⟨y, hy⟩ := hpivot σ p hp
    exact (Finset.card_pos.mpr ⟨y, Z_subset_U points C R σ _ hy⟩)
  contract σ p hp hmark := by
    have hn := (markedByPoorOrPopular_eq_false_iff
      points C R level levelNat cut σ p).mp hmark
    exact U_card_multiplicative_shrink points C R σ
      (levelNat (level σ p)) (cut σ p) K p.1 p.2 hK (hcut σ p hp) hn.1 hn.2



theorem pow_selectedCount_mul_potential_le
    {A L : Type*} [DecidableEq A] [Fintype L] [DecidableEq L]
    {children : List A → Finset A} {marked : List A → A → Bool}
    {K N : ℕ} (cert : PathShrinkCertificate (L := L) children marked K N)
    (hK : 1 ≤ K) (xs : List A) (hpath : Erdos920.MarkedTree.IsPath children xs)
    (ℓ : L) :
    (2 * K) ^ selectedCount marked cert.level ℓ xs * (cert.potential ℓ xs + 1) ≤
      (2 * K - 1) ^ selectedCount marked cert.level ℓ xs *
        (cert.potential ℓ [] + 1) := by
  induction xs with
  | nil => simp [selectedCount]
  | cons x xs ih =>
      rcases hpath with ⟨hpath, hx⟩
      have ih' := ih hpath
      have hmono := cert.mono ℓ xs x hx
      by_cases hs : marked xs x = false ∧ cert.level xs x = ℓ
      · have hpos : 1 ≤ cert.potential (cert.level xs x) xs :=
          cert.positive xs x hx hs.1
        have hcontract := shifted_contraction hK hpos (cert.contract xs x hx hs.1)
        rw [hs.2] at hcontract
        simp only [selectedCount, hs]
        calc
          ((2 * K) ^ selectedCount marked cert.level ℓ xs * (2 * K)) *
                (cert.potential ℓ (x :: xs) + 1) =
              (2 * K) ^ selectedCount marked cert.level ℓ xs *
                ((2 * K) * (cert.potential ℓ (x :: xs) + 1)) := by ac_rfl
          _ ≤ (2 * K) ^ selectedCount marked cert.level ℓ xs *
                ((2 * K - 1) * (cert.potential ℓ xs + 1)) :=
              Nat.mul_le_mul_left _ hcontract
          _ = (2 * K - 1) *
                ((2 * K) ^ selectedCount marked cert.level ℓ xs *
                  (cert.potential ℓ xs + 1)) := by ac_rfl
          _ ≤ (2 * K - 1) *
                ((2 * K - 1) ^ selectedCount marked cert.level ℓ xs *
                  (cert.potential ℓ [] + 1)) := Nat.mul_le_mul_left _ ih'
          _ = ((2 * K - 1) ^ selectedCount marked cert.level ℓ xs * (2 * K - 1)) *
                (cert.potential ℓ [] + 1) := by ac_rfl
      · simp only [selectedCount, hs, if_false]
        exact (Nat.mul_le_mul_left _ (Nat.add_le_add_right hmono 1)).trans ih'



theorem selectedCount_le_of_certificate
    {A L : Type*} [DecidableEq A] [Fintype L] [DecidableEq L]
    {children : List A → Finset A} {marked : List A → A → Bool}
    {K N w : ℕ} (cert : PathShrinkCertificate (L := L) children marked K N)
    (hK : 1 ≤ K)
    (hpow : ∀ c : ℕ, w < c → (2 * K - 1) ^ c * (N + 1) < (2 * K) ^ c)
    (xs : List A) (hpath : Erdos920.MarkedTree.IsPath children xs) (ℓ : L) :
    selectedCount marked cert.level ℓ xs ≤ w := by
  by_contra h
  have hwc : w < selectedCount marked cert.level ℓ xs := Nat.lt_of_not_ge h
  have hprod := pow_selectedCount_mul_potential_le cert hK xs hpath ℓ
  have hfinal : 1 ≤ cert.potential ℓ xs + 1 := by omega
  have hinitial : cert.potential ℓ [] + 1 ≤ N + 1 :=
    Nat.add_le_add_right (cert.initial_le ℓ) 1
  have hbad : (2 * K) ^ selectedCount marked cert.level ℓ xs ≤
      (2 * K - 1) ^ selectedCount marked cert.level ℓ xs * (N + 1) := by
    have hbad' := (Nat.mul_le_mul_left _ hfinal).trans
      (hprod.trans (Nat.mul_le_mul_left _ hinitial))
    simpa only [Nat.mul_one] using hbad'
  exact (Nat.not_lt_of_ge hbad) (hpow _ hwc)



theorem unmarkedCount_le_of_certificate
    {A L : Type*} [DecidableEq A] [Fintype L]
    {children : List A → Finset A} {marked : List A → A → Bool}
    {K N w : ℕ} (cert : PathShrinkCertificate (L := L) children marked K N)
    (hK : 1 ≤ K)
    (hpow : ∀ c : ℕ, w < c → (2 * K - 1) ^ c * (N + 1) < (2 * K) ^ c)
    (xs : List A) (hpath : Erdos920.MarkedTree.IsPath children xs) :
    (Erdos920.MarkedTree.pathSignature marked xs).count false ≤ Fintype.card L * w := by
  classical
  rw [← unmarkedCount_eq_count_false,
    unmarkedCount_eq_sum_selectedCount (L := L)]
  calc
    ∑ ℓ : L, selectedCount marked cert.level ℓ xs ≤ ∑ _ℓ : L, w :=
      Finset.sum_le_sum fun ℓ _ =>
        selectedCount_le_of_certificate (L := L) cert hK hpow xs hpath ℓ
    _ = Fintype.card L * w := by simp






noncomputable def allPaths {A : Type*} [DecidableEq A]
    (children : List A → Finset A) (marked : List A → A → Bool) (m : ℕ) :
    Finset (List A) :=
  Erdos920.MarkedTree.boundedPaths children marked m m

@[simp] theorem mem_allPaths_iff {A : Type*} [DecidableEq A]
    (children : List A → Finset A) (marked : List A → A → Bool)
    (xs : List A) (m : ℕ) :
    xs ∈ allPaths children marked m ↔
      Erdos920.MarkedTree.IsPath children xs ∧ xs.length = m := by
  rw [allPaths, Erdos920.MarkedTree.mem_boundedPaths_iff]
  constructor
  · exact fun h => ⟨h.1, h.2.1⟩
  · rintro ⟨hpath, hlen⟩
    refine ⟨hpath, hlen, ?_⟩
    rw [← hlen, ← Erdos920.MarkedTree.pathSignature_length marked xs]
    exact List.count_le_length




theorem card_allPaths_le {A : Type*} [DecidableEq A]
    (children : List A → Finset A) (marked : List A → A → Bool)
    {Delta h m w : ℕ}
    (hchildren : ∀ xs, (children xs).card ≤ Delta)
    (hmarked : ∀ xs, ((children xs).filter fun x => marked xs x = true).card ≤ h)
    (hunmarked : ∀ xs, Erdos920.MarkedTree.IsPath children xs → xs.length = m →
      (Erdos920.MarkedTree.pathSignature marked xs).count false ≤ w)
    (hhDelta : h ≤ Delta) (hwm : w ≤ m) :
    (allPaths children marked m).card ≤ 2 ^ m * Delta ^ w * h ^ (m - w) := by
  classical
  have hsubset : allPaths children marked m ⊆
      Erdos920.MarkedTree.boundedPaths children marked m w := by
    intro xs hxs
    have hx := (mem_allPaths_iff children marked xs m).mp hxs
    exact (Erdos920.MarkedTree.mem_boundedPaths_iff children marked xs m w).mpr
      ⟨hx.1, hx.2, hunmarked xs hx.1 hx.2⟩
  exact (Finset.card_le_card hsubset).trans
    (Erdos920.MarkedTree.card_boundedPaths_le children marked
      hchildren hmarked hhDelta hwm)






theorem rankContainer_count {L : Type*} [Fintype L]
    (points : Finset P) (C : RankClosure P) (R : P → P → Prop)
    [DecidableRel R] (level : List (P × P) → (P × P) → L)
    (levelNat : L → ℕ) (cut : List (P × P) → (P × P) → ℕ)
    {d hp hq K w m : ℕ}
    (hdegree : ∀ a ∈ points, (points.filter fun b => R a b).card ≤ d)
    (hpoor : ∀ σ, ((extensionChildren points R σ).filter fun p =>
      Poor points C R σ (levelNat (level σ p)) (cut σ p) p.1).card ≤ hp)
    (hpopular : ∀ σ, ((extensionChildren points R σ).filter fun p =>
      Popular points C R σ (levelNat (level σ p)) (cut σ p) p.2).card ≤ hq)
    (hK : 1 ≤ K)
    (hpivot : ∀ σ p, p ∈ extensionChildren points R σ →
      (Z points C R σ (levelNat (level σ p))).Nonempty)
    (hcut : ∀ σ p, p ∈ extensionChildren points R σ →
      (U points C R σ (levelNat (level σ p))).card ≤ K * cut σ p)
    (hpow : ∀ c : ℕ, w < c →
      (2 * K - 1) ^ c * (points.card + 1) < (2 * K) ^ c)
    (hmarkedTotal : hp + hq ≤ points.card * d)
    (hunmarkedLength : Fintype.card L * w ≤ m) :
    (allPaths (extensionChildren points R)
      (markedByPoorOrPopular points C R level levelNat cut) m).card ≤
      2 ^ m * (points.card * d) ^ (Fintype.card L * w) *
        (hp + hq) ^ (m - Fintype.card L * w) := by
  classical
  let marked := markedByPoorOrPopular points C R level levelNat cut
  let cert := rankPathShrinkCertificate points C R level levelNat cut K hK hpivot hcut
  apply card_allPaths_le (extensionChildren points R) marked
  · exact fun σ => extensionChildren_card_le points R d hdegree σ
  · intro σ
    exact markedChildren_card_le points C R level levelNat cut σ hp hq
      (hpoor σ) (hpopular σ)
  · intro xs hpath _
    exact unmarkedCount_le_of_certificate (L := L) cert hK hpow xs hpath
  · exact hmarkedTotal
  · exact hunmarkedLength

end Erdos920.Container



















namespace Erdos920.TupleBound

open Erdos920

noncomputable section





def tupleHistory {alpha : Type*} {m : ℕ} (x : Fin m → alpha) : List alpha :=
  (List.ofFn x).reverse

@[simp] theorem length_tupleHistory {alpha : Type*} {m : ℕ}
    (x : Fin m → alpha) : (tupleHistory x).length = m := by
  simp [tupleHistory]


theorem tupleHistory_injective {alpha : Type*} {m : ℕ} :
    Function.Injective (tupleHistory : (Fin m → alpha) → List alpha) := by
  intro x y hxy
  apply List.ofFn_injective
  have := congrArg List.reverse hxy
  simpa [tupleHistory] using this



variable {alpha : Type*}



theorem card_tuples_le_boundedPaths [DecidableEq alpha]
    {m w : ℕ}
    (tuples : Finset (Fin m → alpha))
    (children : List alpha → Finset alpha)
    (marked : List alpha → alpha → Bool)
    (hpath : ∀ x ∈ tuples,
      MarkedTree.IsPath children (tupleHistory x))
    (hunmarked : ∀ x ∈ tuples,
      (MarkedTree.pathSignature marked (tupleHistory x)).count false ≤ w) :
    tuples.card ≤ (MarkedTree.boundedPaths children marked m w).card := by
  classical
  refine Finset.card_le_card_of_injOn tupleHistory ?_ ?_
  · intro x hx
    exact (MarkedTree.mem_boundedPaths_iff children marked (tupleHistory x) m w).2
      ⟨hpath x hx, length_tupleHistory x, hunmarked x hx⟩
  · intro x _ y _ hxy
    exact tupleHistory_injective hxy



theorem card_tuples_le_of_markedTree
    {Delta h m w : ℕ}
    (tuples : Finset (Fin m → alpha))
    (children : List alpha → Finset alpha)
    (marked : List alpha → alpha → Bool)
    (hpath : ∀ x ∈ tuples,
      MarkedTree.IsPath children (tupleHistory x))
    (hunmarked : ∀ x ∈ tuples,
      (MarkedTree.pathSignature marked (tupleHistory x)).count false ≤ w)
    (hchildren : ∀ σ, (children σ).card ≤ Delta)
    (hmarked : ∀ σ,
      ((children σ).filter fun x ↦ marked σ x = true).card ≤ h)
    (hhDelta : h ≤ Delta) (hwm : w ≤ m) :
    tuples.card ≤ 2 ^ m * Delta ^ w * h ^ (m - w) := by
  classical
  exact (card_tuples_le_boundedPaths tuples children marked hpath hunmarked).trans
    (MarkedTree.card_boundedPaths_le children marked hchildren hmarked hhDelta hwm)



variable {P : Type*}





def consistentChildren (vertices : Finset (P × P))
    (R : P → P → Prop) [DecidableRel R]
    (σ : List (P × P)) : Finset (P × P) := by
  classical
  exact vertices.filter fun p ↦ Container.CanExtend R p σ

@[simp] theorem mem_consistentChildren_iff
    (vertices : Finset (P × P)) (R : P → P → Prop)
    [DecidableRel R] (p : P × P) (σ : List (P × P)) :
    p ∈ consistentChildren vertices R σ ↔
      p ∈ vertices ∧ Container.CanExtend R p σ := by
  classical
  simp [consistentChildren]




theorem isPath_consistentChildren_iff
    (vertices : Finset (P × P)) (R : P → P → Prop)
    [DecidableRel R] (σ : List (P × P)) :
    MarkedTree.IsPath (consistentChildren vertices R) σ ↔
      Container.Consistent R σ ∧ ∀ p ∈ σ, p ∈ vertices := by
  induction σ with
  | nil => simp [MarkedTree.IsPath]
  | cons p σ ih =>
      simp only [MarkedTree.IsPath, Container.consistent_cons_iff,
        mem_consistentChildren_iff, ih, List.mem_cons]
      aesop



theorem card_consistent_tuples_le_of_markedTree
    {Delta h m w : ℕ}
    (vertices : Finset (P × P)) (R : P → P → Prop)
    [DecidableRel R]
    (tuples : Finset (Fin m → (P × P)))
    (marked : List (P × P) → (P × P) → Bool)
    (hconsistent : ∀ x ∈ tuples, Container.Consistent R (tupleHistory x))
    (hmem : ∀ x ∈ tuples, ∀ i, x i ∈ vertices)
    (hunmarked : ∀ x ∈ tuples,
      (MarkedTree.pathSignature marked (tupleHistory x)).count false ≤ w)
    (hchildren : ∀ σ, (consistentChildren vertices R σ).card ≤ Delta)
    (hmarked : ∀ σ,
      ((consistentChildren vertices R σ).filter
        fun x ↦ marked σ x = true).card ≤ h)
    (hhDelta : h ≤ Delta) (hwm : w ≤ m) :
    tuples.card ≤ 2 ^ m * Delta ^ w * h ^ (m - w) := by
  apply card_tuples_le_of_markedTree tuples
    (consistentChildren vertices R) marked
  · intro x hx
    rw [isPath_consistentChildren_iff]
    refine ⟨hconsistent x hx, ?_⟩
    intro p hp
    have hp' : p ∈ List.ofFn x := by
      simpa [tupleHistory] using hp
    rcases List.mem_ofFn.mp hp' with ⟨i, rfl⟩
    exact hmem x hx i
  · exact hunmarked
  · exact hchildren
  · exact hmarked
  · exact hhDelta
  · exact hwm

end

end Erdos920.TupleBound













open scoped LinearAlgebra.Projectivization

namespace Erdos920.TupleHistory

noncomputable section

open Erdos920.Projective
open Erdos920.ProjectiveDStar
open Erdos920.RamseyPackaging

variable {q t m : ℕ} [Fact q.Prime]

abbrev P (q t : ℕ) [Fact q.Prime] :=
  Projective.Point (ZMod q) (t + 1)
abbrev V (q t : ℕ) [Fact q.Prime] := ProjectiveDStar.Vertex q t

local instance orthogonalDecidable :
    DecidableRel (@Projective.Orthogonal (ZMod q) _ (t + 1)) :=
  Classical.decRel _

noncomputable local instance pointFintype : Fintype (P q t) :=
  Fintype.ofFinite _

local instance pointDecidableEq : DecidableEq (P q t) :=
  Classical.decEq _


def incidentPairs : Finset (P q t × P q t) :=
  Finset.univ.filter fun p ↦ Projective.Orthogonal p.1 p.2

@[simp] theorem mem_incidentPairs_iff (p : P q t × P q t) :
    p ∈ (incidentPairs : Finset (P q t × P q t)) ↔
      Projective.Orthogonal p.1 p.2 := by
  simp [incidentPairs]


def vertexPair (u : V q t) : P q t × P q t :=
  (ProjectiveDStar.leftPoint u, ProjectiveDStar.rightPoint u)

@[simp] theorem vertexPair_fst (u : V q t) :
    (vertexPair u).1 = ProjectiveDStar.leftPoint u := rfl

@[simp] theorem vertexPair_snd (u : V q t) :
    (vertexPair u).2 = ProjectiveDStar.rightPoint u := rfl


def pairTuple (x : Fin m → V q t) : Fin m → P q t × P q t :=
  fun i ↦ vertexPair (x i)


def pairHistory (x : Fin m → V q t) : List (P q t × P q t) :=
  TupleBound.tupleHistory (pairTuple x)

@[simp] theorem length_pairHistory (x : Fin m → V q t) :
    (pairHistory x).length = m := by
  simp [pairHistory]

theorem vertexPair_injective :
    Function.Injective (@vertexPair q t _) := by
  intro u v huv
  exact Subtype.ext huv

theorem pairTuple_injective :
    Function.Injective
      (pairTuple : (Fin m → V q t) → (Fin m → P q t × P q t)) := by
  intro x y hxy
  funext i
  exact vertexPair_injective (congrFun hxy i)

theorem pairHistory_injective :
    Function.Injective
      (pairHistory : (Fin m → V q t) → List (P q t × P q t)) := by
  intro x y hxy
  apply pairTuple_injective
  exact TupleBound.tupleHistory_injective hxy

private theorem ofFn_get_cast {alpha : Type*} (xs : List alpha) {n : ℕ}
    (h : n = xs.length) :
    List.ofFn (fun i : Fin n ↦ xs.get (Fin.cast h i)) = xs := by
  subst n
  simp





theorem canExtend_vertexPair_iff (new : V q t) (old : List (V q t)) :
    Container.CanExtend Projective.Orthogonal
        (vertexPair new)
        (old.map vertexPair) ↔
      ∀ u ∈ old, ¬ ProjectiveDStar.Arc u new := by
  constructor
  · intro h u hu harc
    rcases h with ⟨_inc, hcompat⟩
    rcases harc with ⟨huv, hvu⟩
    apply hvu
    apply hcompat (vertexPair u)
    · exact List.mem_map.mpr ⟨u, hu, rfl⟩
    · exact huv
  · intro h
    refine ⟨ProjectiveDStar.incident new, ?_⟩
    intro p hp holdnew
    rcases List.mem_map.mp hp with ⟨u, hu, rfl⟩
    by_contra hnewold
    exact h u hu ⟨holdnew, hnewold⟩



theorem consistent_map_iff_pairwise_reverse (xs : List (V q t)) :
    Container.Consistent Projective.Orthogonal
        (xs.map vertexPair) ↔
      xs.reverse.Pairwise (fun old new ↦ ¬ ProjectiveDStar.Arc old new) := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      rw [List.map_cons, Container.consistent_cons_iff, ih,
        canExtend_vertexPair_iff]
      simp only [List.reverse_cons]
      rw [List.pairwise_append]
      simp



theorem isForwardIndependent_iff_consistent (x : Fin m → V q t) :
    (ProjectiveDStar.digraph q t).IsForwardIndependent x ↔
      Container.Consistent Projective.Orthogonal (pairHistory x) := by
  rw [pairHistory, TupleBound.tupleHistory]
  have hmap : List.ofFn (pairTuple x) =
      (List.ofFn x).map vertexPair := by
    rw [List.map_ofFn]
    rfl
  rw [hmap, ← List.map_reverse, consistent_map_iff_pairwise_reverse]
  simp only [List.reverse_reverse]
  rw [List.pairwise_ofFn]
  rfl


theorem pairHistory_mem_incidentPairs (x : Fin m → V q t) :
    ∀ p ∈ pairHistory x,
      p ∈ (incidentPairs : Finset (P q t × P q t)) := by
  intro p hp
  have hp' : p ∈ List.ofFn (pairTuple x) := by
    simpa [pairHistory, TupleBound.tupleHistory] using hp
  rcases List.mem_ofFn.mp hp' with ⟨i, rfl⟩
  exact (mem_incidentPairs_iff _).2 (ProjectiveDStar.incident (x i))


theorem isPath_pairHistory_iff (x : Fin m → V q t) :
    MarkedTree.IsPath
        (TupleBound.consistentChildren incidentPairs Projective.Orthogonal)
        (pairHistory x) ↔
      (ProjectiveDStar.digraph q t).IsForwardIndependent x := by
  rw [TupleBound.isPath_consistentChildren_iff,
    ← isForwardIndependent_iff_consistent]
  exact and_iff_left (pairHistory_mem_incidentPairs x)




def forwardIndependentTuples : Finset (Fin m → V q t) :=
  by
    classical
    exact Finset.univ.filter fun x ↦
      (ProjectiveDStar.digraph q t).IsForwardIndependent x

@[simp] theorem mem_forwardIndependentTuples_iff (x : Fin m → V q t) :
    x ∈ (forwardIndependentTuples : Finset (Fin m → V q t)) ↔
      (ProjectiveDStar.digraph q t).IsForwardIndependent x := by
  simp [forwardIndependentTuples]

theorem card_forwardIndependentTuples :
    (forwardIndependentTuples : Finset (Fin m → V q t)).card =
      @Digraph.forwardIndependentTupleCount (V q t)
        (ProjectiveDStar.vertexFintype q t) (ProjectiveDStar.digraph q t) m := by
  simp [forwardIndependentTuples, Digraph.forwardIndependentTupleCount]



def forwardHistories : Finset (List (P q t × P q t)) :=
  by
    classical
    exact (forwardIndependentTuples (q := q) (t := t) (m := m)).image pairHistory

theorem card_forwardHistories :
    (forwardHistories (q := q) (t := t) (m := m)).card =
      @Digraph.forwardIndependentTupleCount (V q t)
        (ProjectiveDStar.vertexFintype q t) (ProjectiveDStar.digraph q t) m := by
  rw [forwardHistories, Finset.card_image_iff.mpr]
  · exact card_forwardIndependentTuples
  · exact pairHistory_injective.injOn


theorem mem_forwardHistories_iff (xs : List (P q t × P q t)) :
    xs ∈ (forwardHistories (q := q) (t := t) (m := m) :
        Finset (List (P q t × P q t))) ↔
      Container.Consistent Projective.Orthogonal xs ∧
      xs.length = m ∧
      ∀ p ∈ xs, p ∈ (incidentPairs : Finset (P q t × P q t)) := by
  constructor
  · intro hxs
    rw [forwardHistories] at hxs
    rcases Finset.mem_image.mp hxs with ⟨x, hx, rfl⟩
    exact ⟨(isForwardIndependent_iff_consistent x).1
        ((mem_forwardIndependentTuples_iff x).1 hx),
      length_pairHistory x, pairHistory_mem_incidentPairs x⟩
  · rintro ⟨hconsistent, hlen, hinc⟩
    have hrev : m = xs.reverse.length := by
      calc
        m = xs.length := hlen.symm
        _ = xs.reverse.length := by simp
    let x : Fin m → V q t := fun i ↦
      ⟨xs.reverse.get (Fin.cast hrev i), (mem_incidentPairs_iff _).1
        (hinc _ (List.mem_reverse.mp
          (List.get_mem xs.reverse (Fin.cast hrev i))))⟩
    have hhistory : pairHistory x = xs := by
      apply List.reverse_injective
      simp only [pairHistory, TupleBound.tupleHistory, List.reverse_reverse]
      change List.ofFn (fun i : Fin m ↦
        xs.reverse.get (Fin.cast hrev i)) = xs.reverse
      exact ofFn_get_cast xs.reverse hrev
    rw [forwardHistories]
    apply Finset.mem_image.mpr
    refine ⟨x, ?_, hhistory⟩
    rw [mem_forwardIndependentTuples_iff,
      isForwardIndependent_iff_consistent, hhistory]
    exact hconsistent




theorem forwardHistories_eq_allPaths
    (marked : List (P q t × P q t) → (P q t × P q t) → Bool) :
    forwardHistories (q := q) (t := t) (m := m) = Container.allPaths
      (TupleBound.consistentChildren
        (incidentPairs (q := q) (t := t)) Projective.Orthogonal)
      marked m := by
  ext xs
  rw [mem_forwardHistories_iff, Container.mem_allPaths_iff,
    TupleBound.isPath_consistentChildren_iff]
  aesop



theorem forwardIndependentTupleCount_eq_card_allPaths
    (marked : List (P q t × P q t) → (P q t × P q t) → Bool) :
    @Digraph.forwardIndependentTupleCount (V q t)
        (ProjectiveDStar.vertexFintype q t) (ProjectiveDStar.digraph q t) m =
      (Container.allPaths
        (TupleBound.consistentChildren
          (incidentPairs (q := q) (t := t)) Projective.Orthogonal)
        marked m).card := by
  rw [← card_forwardHistories, forwardHistories_eq_allPaths marked]

end

end Erdos920.TupleHistory












open scoped BigOperators LinearAlgebra.Projectivization

namespace Erdos920.DesignAdapter

noncomputable section

open Erdos920.Projective
open Erdos920.Mixing


abbrev P (q t : ℕ) [Fact q.Prime] := Point (ZMod q) (t + 1)


abbrev Incidence (q t : ℕ) [Fact q.Prime] : P q t → P q t → Prop :=
  Orthogonal


def degree (q t : ℕ) : ℕ := ∑ i ∈ Finset.range t, q ^ i


def codegree (q t : ℕ) : ℕ := ∑ i ∈ Finset.range (t - 1), q ^ i

noncomputable local instance pointFintype (q t : ℕ) [Fact q.Prime] :
    Fintype (P q t) := Fintype.ofFinite _

local instance incidenceDecidable (q t : ℕ) [Fact q.Prime] :
    DecidableRel (Incidence q t) := Classical.decRel _


theorem card_points (q t : ℕ) [Fact q.Prime] :
    Fintype.card (P q t) = ∑ i ∈ Finset.range (t + 1), q ^ i := by
  rw [← Nat.card_eq_fintype_card]
  exact natCard_point_zmod q (t + 1)


theorem card_filter_orthogonal_zmod (q t : ℕ) [Fact q.Prime]
    (x : P q t) :
    (Finset.univ.filter (Incidence q t x)).card = degree q t := by
  classical
  simpa [degree] using (card_filter_orthogonal (x := x))


theorem card_filter_commonOrthogonal_zmod (q t : ℕ) [Fact q.Prime]
    {x y : P q t} (hxy : x ≠ y) :
    (Finset.univ.filter fun z ↦ Incidence q t x z ∧ Incidence q t y z).card =
      codegree q t := by
  classical
  simpa [codegree] using (card_filter_commonOrthogonal (x := x) (y := y) hxy)


theorem orthogonal_symm_zmod (q t : ℕ) [Fact q.Prime]
    {x y : P q t} (hxy : Incidence q t x y) : Incidence q t y x :=
  (orthogonal_comm x y).mp hxy


theorem design_parameter_bounds (q t : ℕ) [Fact q.Prime] (ht : 2 ≤ t) :
    q ^ t ≤ Fintype.card (P q t) ∧
      Fintype.card (P q t) ≤ 2 * q ^ t ∧
      q ^ (t - 1) ≤ degree q t ∧
      degree q t ≤ 2 * q ^ (t - 1) ∧
      codegree q t ≤ degree q t := by
  have hpoint := point_zmod_bounds q t
  have hdegree : q ^ (t - 1) ≤ degree q t ∧
      degree q t ≤ 2 * q ^ (t - 1) := by
    exact ⟨pow_pred_le_geomSum q t (by omega),
      geomSum_le_two_mul_pow_pred q t (Fact.out : q.Prime).two_le⟩
  have hcode : codegree q t ≤ degree q t := by
    unfold codegree degree
    apply Finset.sum_le_sum_of_subset
    exact Finset.range_mono (by omega)
  have hpoint' : q ^ t ≤ Fintype.card (P q t) ∧
      Fintype.card (P q t) ≤ 2 * q ^ t := by
    simpa only [Nat.card_eq_fintype_card] using hpoint
  exact ⟨hpoint'.1, hpoint'.2, hdegree.1, hdegree.2, hcode⟩



theorem card_points_le_two_mul_q_mul_degree
    (q t : ℕ) [Fact q.Prime] (ht : 2 ≤ t) :
    Fintype.card (P q t) ≤ 2 * q * degree q t := by
  have h := design_parameter_bounds q t ht
  have hpow : q ^ t = q ^ (t - 1) * q := by
    conv_lhs => rw [show t = (t - 1) + 1 by omega]
    rw [pow_succ]
  calc
    Fintype.card (P q t) ≤ 2 * q ^ t := h.2.1
    _ = 2 * q * q ^ (t - 1) := by
      rw [hpow]
      ring
    _ ≤ 2 * q * degree q t := Nat.mul_le_mul_left (2 * q) h.2.2.1



theorem orthogonal_normalized_deviation_sq_le
    (q t : ℕ) [Fact q.Prime] (ht : 2 ≤ t)
    (A B : Finset (P q t)) :
    (((orderedEdges (Incidence q t) A B : ℝ) -
        (degree q t : ℝ) / Fintype.card (P q t) * A.card * B.card) ^ 2 ≤
      2 * (q : ℝ) ^ (t - 1) * A.card * B.card) := by
  classical
  have hpar := design_parameter_bounds q t ht
  have hmix := orderedEdges_normalized_deviation_sq_le
    (Incidence q t) (degree q t) (codegree q t)
    (fun {_ _} h ↦ orthogonal_symm_zmod q t h)
    (card_filter_orthogonal_zmod q t)
    (fun _ _ hxy ↦ card_filter_commonOrthogonal_zmod q t hxy)
    hpar.2.2.2.2 A B
  have hgap : (degree q t : ℝ) - codegree q t ≤
      2 * (q : ℝ) ^ (t - 1) := by
    have hd : (degree q t : ℝ) ≤ 2 * (q : ℝ) ^ (t - 1) := by
      exact_mod_cast hpar.2.2.2.1
    have hc : (0 : ℝ) ≤ codegree q t := Nat.cast_nonneg _
    linarith
  calc
    (((orderedEdges (Incidence q t) A B : ℝ) -
        (degree q t : ℝ) / Fintype.card (P q t) * A.card * B.card) ^ 2) ≤
      ((degree q t : ℝ) - codegree q t) * A.card * B.card := hmix
    _ ≤ 2 * (q : ℝ) ^ (t - 1) * A.card * B.card := by
      have hAB : (0 : ℝ) ≤ (A.card : ℝ) * B.card := by positivity
      nlinarith


theorem abs_orthogonal_sub_expected_le
    (q t : ℕ) [Fact q.Prime] (ht : 2 ≤ t)
    (A B : Finset (P q t)) :
    |(orderedEdges (Incidence q t) A B : ℝ) -
        (degree q t : ℝ) / Fintype.card (P q t) * A.card * B.card| ≤
      Real.sqrt (2 * (q : ℝ) ^ (t - 1) * A.card * B.card) := by
  apply Real.abs_le_sqrt
  exact orthogonal_normalized_deviation_sq_le q t ht A B




theorem poor_product_le_real
    (q t : ℕ) [Fact q.Prime] (ht : 2 ≤ t)
    (A Z : Finset (P q t))
    (hpoor : ∀ a ∈ A,
      8 * q * (Z.filter (Incidence q t a)).card ≤ Z.card) :
    (A.card : ℝ) * Z.card ≤ 512 * (q : ℝ) ^ (t + 1) := by
  classical
  let d := degree q t
  let c := codegree q t
  have hpar := design_parameter_bounds q t ht
  have hsparseNat :
      8 * q * orderedEdges (Incidence q t) A Z ≤ A.card * Z.card := by
    simpa [Nat.mul_assoc] using
      (mul_orderedEdges_le_card_mul_of_pointwise (Incidence q t) (8 * q) A Z
        (by simpa [restrictedDegree] using hpoor))
  have hsparse :
      8 * (q : ℝ) * orderedEdges Orthogonal A Z ≤
        (A.card : ℝ) * Z.card := by
    exact_mod_cast hsparseNat
  have hNd : (Fintype.card (P q t) : ℝ) ≤
      2 * (q : ℝ) * d := by
    exact_mod_cast card_points_le_two_mul_q_mul_degree q t ht
  have hvar : (d : ℝ) - c ≤ 2 * (q : ℝ) ^ (t - 1) := by
    have hd : (d : ℝ) ≤ 2 * (q : ℝ) ^ (t - 1) := by
      exact_mod_cast hpar.2.2.2.1
    have hc : (0 : ℝ) ≤ c := Nat.cast_nonneg _
    linarith
  have hm := card_mul_le_of_sparse_orderedEdges
    (Incidence q t) d c (fun {_ _} h ↦ orthogonal_symm_zmod q t h)
    (card_filter_orthogonal_zmod q t)
    (fun _ _ hxy ↦ card_filter_commonOrthogonal_zmod q t hxy)
    hpar.2.2.2.2 A Z (q : ℝ) (2 * (q : ℝ) ^ (t - 1))
    (by exact_mod_cast (Fact.out : q.Prime).pos)
    (by positivity) hNd hvar hsparse
  calc
    (A.card : ℝ) * Z.card ≤
        256 * (q : ℝ) ^ 2 * (2 * (q : ℝ) ^ (t - 1)) := hm
    _ = 512 * (q : ℝ) ^ (t + 1) := by
      rw [show t + 1 = 2 + (t - 1) by omega, pow_add]
      ring


theorem poor_product_le
    (q t : ℕ) [Fact q.Prime] (ht : 2 ≤ t)
    (A Z : Finset (P q t))
    (hpoor : ∀ a ∈ A,
      8 * q * (Z.filter (Incidence q t a)).card ≤ Z.card) :
    A.card * Z.card ≤ 512 * q ^ (t + 1) := by
  exact_mod_cast poor_product_le_real q t ht A Z hpoor


def poorSet (q t : ℕ) [Fact q.Prime] (Z : Finset (P q t)) : Finset (P q t) :=
  Finset.univ.filter fun a ↦
    8 * q * (Z.filter (Incidence q t a)).card ≤ Z.card

@[simp] theorem mem_poorSet_iff
    (q t : ℕ) [Fact q.Prime] (Z : Finset (P q t)) (a : P q t) :
    a ∈ poorSet q t Z ↔
      8 * q * (Z.filter (Incidence q t a)).card ≤ Z.card := by
  simp [poorSet]


theorem poorSet_product_le
    (q t : ℕ) [Fact q.Prime] (ht : 2 ≤ t) (Z : Finset (P q t)) :
    (poorSet q t Z).card * Z.card ≤ 512 * q ^ (t + 1) := by
  apply poor_product_le q t ht
  intro a ha
  exact (mem_poorSet_iff q t Z a).mp ha




theorem poor_edges_le_real
    (q t : ℕ) [Fact q.Prime] (ht : 2 ≤ t)
    (A Z B : Finset (P q t))
    (hpoor : ∀ a ∈ A,
      8 * q * (Z.filter (Incidence q t a)).card ≤ Z.card)
    (hBZ : B.card ≤ Z.card) :
    (orderedEdges (Incidence q t) A B : ℝ) ≤
      2048 * (q : ℝ) ^ t := by
  classical
  let d := degree q t
  let c := codegree q t
  let N : ℝ := Fintype.card (P q t)
  let X : ℝ := (A.card : ℝ) * B.card
  have hpar := design_parameter_bounds q t ht
  have hqpos : (0 : ℝ) < q := by
    exact_mod_cast (Fact.out : q.Prime).pos
  have hNpos : 0 < N := by
    dsimp [N]
    exact_mod_cast Fintype.card_pos
  have hNlow : (q : ℝ) ^ t ≤ N := by
    dsimp [N]
    exact_mod_cast hpar.1
  have hd : (d : ℝ) ≤ 2 * (q : ℝ) ^ (t - 1) := by
    exact_mod_cast hpar.2.2.2.1
  have hc : (c : ℝ) ≤ d := by
    exact_mod_cast hpar.2.2.2.2
  have hgap : (d : ℝ) - c ≤ 2 * (q : ℝ) ^ (t - 1) := by
    have : (0 : ℝ) ≤ c := Nat.cast_nonneg _
    linarith
  have hgap0 : (0 : ℝ) ≤ (d : ℝ) - c := sub_nonneg.mpr hc
  have hX0 : 0 ≤ X := by
    dsimp [X]
    positivity
  have hX : X ≤ 512 * (q : ℝ) ^ (t + 1) := by
    dsimp [X]
    have hcast : (B.card : ℝ) ≤ Z.card := by exact_mod_cast hBZ
    calc
      (A.card : ℝ) * B.card ≤ (A.card : ℝ) * Z.card :=
        mul_le_mul_of_nonneg_left hcast (Nat.cast_nonneg _)
      _ ≤ 512 * (q : ℝ) ^ (t + 1) :=
        poor_product_le_real q t ht A Z hpoor
  have hpow : (q : ℝ) ^ t = (q : ℝ) ^ (t - 1) * q := by
    conv_lhs => rw [show t = (t - 1) + 1 by omega]
    rw [pow_succ]
  have hdensity : (d : ℝ) / N ≤ 2 / (q : ℝ) := by
    rw [div_le_div_iff₀ hNpos hqpos]
    calc
      (d : ℝ) * q ≤ (2 * (q : ℝ) ^ (t - 1)) * q :=
        mul_le_mul_of_nonneg_right hd hqpos.le
      _ = 2 * (q : ℝ) ^ t := by rw [hpow]; ring
      _ ≤ 2 * N := mul_le_mul_of_nonneg_left hNlow (by norm_num)
  have hdensity0 : 0 ≤ (d : ℝ) / N := by positivity
  have hexpected : (d : ℝ) / N * X ≤ 1024 * (q : ℝ) ^ t := by
    calc
      (d : ℝ) / N * X ≤ (2 / (q : ℝ)) * X :=
        mul_le_mul_of_nonneg_right hdensity hX0
      _ ≤ (2 / (q : ℝ)) *
          (512 * (q : ℝ) ^ (t + 1)) :=
        mul_le_mul_of_nonneg_left hX (by positivity)
      _ = 1024 * (q : ℝ) ^ t := by
        rw [pow_succ]
        field_simp
        ring
  have hvariance :
      ((d : ℝ) - c) * X ≤ 1024 * (q : ℝ) ^ (2 * t) := by
    calc
      ((d : ℝ) - c) * X ≤
          (2 * (q : ℝ) ^ (t - 1)) *
            (512 * (q : ℝ) ^ (t + 1)) :=
        mul_le_mul hgap hX hX0 (by positivity)
      _ = 1024 * (q : ℝ) ^ (2 * t) := by
        rw [show 2 * t = (t - 1) + (t + 1) by omega, pow_add]
        ring
  have hpowsq : ((q : ℝ) ^ t) ^ 2 = (q : ℝ) ^ (2 * t) := by
    rw [← pow_mul]
    congr 1
    omega
  have hsqrt :
      Real.sqrt (((d : ℝ) - c) * X) ≤ 1024 * (q : ℝ) ^ t := by
    rw [Real.sqrt_le_iff]
    constructor
    · positivity
    · calc
        ((d : ℝ) - c) * X ≤ 1024 * (q : ℝ) ^ (2 * t) := hvariance
        _ ≤ (1024 * (q : ℝ) ^ t) ^ 2 := by
          rw [mul_pow, hpowsq]
          have hpow0 : (0 : ℝ) ≤ (q : ℝ) ^ (2 * t) := by positivity
          nlinarith
  have hmix := abs_orderedEdges_sub_expected_le
    (Incidence q t) d c (fun {_ _} h ↦ orthogonal_symm_zmod q t h)
    (card_filter_orthogonal_zmod q t)
    (fun _ _ hxy ↦ card_filter_commonOrthogonal_zmod q t hxy)
    hpar.2.2.2.2 A B
  have hmix' :
      |(orderedEdges (Incidence q t) A B : ℝ) - (d : ℝ) / N * X| ≤
        Real.sqrt (((d : ℝ) - c) * X) := by
    dsimp [N, X]
    convert hmix using 1 <;> ring_nf
  have hupper :
      (orderedEdges (Incidence q t) A B : ℝ) - (d : ℝ) / N * X ≤
        Real.sqrt (((d : ℝ) - c) * X) := by
    have habs :
        (orderedEdges (Incidence q t) A B : ℝ) - (d : ℝ) / N * X ≤
          |(orderedEdges (Incidence q t) A B : ℝ) - (d : ℝ) / N * X| :=
      le_abs_self _
    exact habs.trans hmix'
  have hsum :
      (orderedEdges (Incidence q t) A B : ℝ) ≤
        (d : ℝ) / N * X + Real.sqrt (((d : ℝ) - c) * X) := by
    linarith
  calc
    (orderedEdges (Incidence q t) A B : ℝ) ≤
        (d : ℝ) / N * X + Real.sqrt (((d : ℝ) - c) * X) := hsum
    _ ≤ 1024 * (q : ℝ) ^ t + 1024 * (q : ℝ) ^ t :=
      add_le_add hexpected hsqrt
    _ = 2048 * (q : ℝ) ^ t := by ring


theorem poor_edges_le
    (q t : ℕ) [Fact q.Prime] (ht : 2 ≤ t)
    (A Z B : Finset (P q t))
    (hpoor : ∀ a ∈ A,
      8 * q * (Z.filter (Incidence q t a)).card ≤ Z.card)
    (hBZ : B.card ≤ Z.card) :
    orderedEdges (Incidence q t) A B ≤ 2048 * q ^ t := by
  exact_mod_cast poor_edges_le_real q t ht A Z B hpoor hBZ


theorem poorSet_edges_le
    (q t : ℕ) [Fact q.Prime] (ht : 2 ≤ t)
    (Z B : Finset (P q t)) (hBZ : B.card ≤ Z.card) :
    orderedEdges (Incidence q t) (poorSet q t Z) B ≤ 2048 * q ^ t := by
  apply poor_edges_le q t ht (poorSet q t Z) Z B
  · intro a ha
    exact (mem_poorSet_iff q t Z a).mp ha
  · exact hBZ

end

end Erdos920.DesignAdapter

















open scoped LinearAlgebra.Projectivization

namespace Erdos920.ProjectiveContainer

noncomputable section

open Erdos920.Projective

variable {F : Type*} [Field F] {d : ℕ}


def pointSpan (S : Finset (Point F d)) : Submodule F (Fin d → F) :=
  S.sup Projectivization.submodule

@[simp] theorem pointSpan_empty :
    pointSpan (∅ : Finset (Point F d)) = ⊥ := by
  simp [pointSpan]

@[simp] theorem pointSpan_insert [DecidableEq (Point F d)]
    (x : Point F d) (S : Finset (Point F d)) :
    pointSpan (insert x S) = x.submodule ⊔ pointSpan S := by
  exact Finset.sup_insert

theorem submodule_le_pointSpan_of_mem
    {x : Point F d} {S : Finset (Point F d)} (hx : x ∈ S) :
    x.submodule ≤ pointSpan S := by
  unfold pointSpan
  exact Finset.le_sup hx


def InClosure (x : Point F d) (S : Finset (Point F d)) : Prop :=
  x.submodule ≤ pointSpan S

theorem inClosure_iff_rep_mem (x : Point F d) (S : Finset (Point F d)) :
    InClosure x S ↔ x.rep ∈ pointSpan S := by
  rw [InClosure, Projectivization.submodule_eq,
    Submodule.span_singleton_le_iff_mem]

theorem pointSpan_insert_eq_of_inClosure [DecidableEq (Point F d)]
    {x : Point F d} {S : Finset (Point F d)} (hx : InClosure x S) :
    pointSpan (insert x S) = pointSpan S := by
  rw [pointSpan_insert, sup_eq_right]
  exact hx

theorem pointSpan_le_insert [DecidableEq (Point F d)]
    (x : Point F d) (S : Finset (Point F d)) :
    pointSpan S ≤ pointSpan (insert x S) := by
  rw [pointSpan_insert]
  exact le_sup_right



theorem finrank_pointSpan_insert_le [DecidableEq (Point F d)]
    (x : Point F d) (S : Finset (Point F d)) :
    Module.finrank F (pointSpan (insert x S)) ≤
      Module.finrank F (pointSpan S) + 1 := by
  rw [pointSpan_insert]
  have h := Submodule.finrank_add_le_finrank_add_finrank
    x.submodule (pointSpan S)
  rw [Projectivization.finrank_submodule] at h
  omega



theorem finrank_pointSpan_insert_of_not_inClosure
    [DecidableEq (Point F d)] (x : Point F d) (S : Finset (Point F d))
    (hx : ¬ InClosure x S) :
    Module.finrank F (pointSpan (insert x S)) =
      Module.finrank F (pointSpan S) + 1 := by
  rw [pointSpan_insert, sup_comm, Projectivization.submodule_eq]
  apply Submodule.finrank_sup_span_singleton
  simpa [inClosure_iff_rep_mem] using hx



def rankClosure [DecidableEq (Point F d)] :
    Container.RankClosure (Point F d) where
  rank S := Module.finrank F (pointSpan S)
  Cl x S := InClosure x S
  decidable_cl := fun _ _ ↦ Classical.dec _
  rank_mono_insert := fun S x ↦
    Submodule.finrank_mono (pointSpan_le_insert x S)
  rank_insert_le := fun S x ↦ finrank_pointSpan_insert_le x S
  rank_insert_of_not_cl := fun S x hx ↦
    finrank_pointSpan_insert_of_not_inClosure x S hx

@[simp] theorem rankClosure_rank [DecidableEq (Point F d)]
    (S : Finset (Point F d)) :
    (rankClosure (F := F) (d := d)).rank S = Module.finrank F (pointSpan S) := rfl

@[simp] theorem rankClosure_cl [DecidableEq (Point F d)]
    (x : Point F d) (S : Finset (Point F d)) :
    (rankClosure (F := F) (d := d)).Cl x S ↔ InClosure x S := Iff.rfl



section DStarHistory

variable {q t : ℕ} [Fact q.Prime]

abbrev P (q t : ℕ) [Fact q.Prime] := Point (ZMod q) (t + 1)

local instance : Fintype (P q t) := Fintype.ofFinite _
local instance : DecidableEq (P q t) := Classical.decEq _
local instance : DecidableRel (Orthogonal : P q t → P q t → Prop) :=
  Classical.decRel _



def projectiveRankClosure (q t : ℕ) [Fact q.Prime] :
    Container.RankClosure (P q t) :=
  rankClosure (F := ZMod q) (d := t + 1)

@[simp] theorem projectiveRankClosure_rank (S : Finset (P q t)) :
    (projectiveRankClosure q t).rank S =
      Module.finrank (ZMod q) (pointSpan S) := rfl

@[simp] theorem projectiveRankClosure_cl (x : P q t) (S : Finset (P q t)) :
    (projectiveRankClosure q t).Cl x S ↔
      x.submodule ≤ pointSpan S := Iff.rfl

@[simp] theorem projectiveRankClosure_rank_empty :
    (projectiveRankClosure q t).rank ∅ = 0 := by
  simp [projectiveRankClosure]

theorem projectiveRankClosure_rank_le_dim (S : Finset (P q t)) :
    (projectiveRankClosure q t).rank S ≤ t + 1 := by
  have h := Submodule.finrank_le (pointSpan S)
  simpa [Module.finrank_fin_fun] using h



theorem card_filter_projectiveRankClosure_cl_le (S : Finset (P q t)) :
    (Finset.univ.filter fun x ↦
      (projectiveRankClosure q t).Cl x S).card ≤
      2 * q ^ ((projectiveRankClosure q t).rank S - 1) := by
  rw [Projective.card_filter_univ_eq_natCard_subtype]
  simpa [projectiveRankClosure, rankClosure, InClosure] using
    (Projective.natCard_pointsIn_zmod_le_two_mul_pow_pred (pointSpan S))



def vertexPair (u : ProjectiveDStar.Vertex q t) : P q t × P q t :=
  (ProjectiveDStar.leftPoint u, ProjectiveDStar.rightPoint u)

@[simp] theorem vertexPair_fst (u : ProjectiveDStar.Vertex q t) :
    (vertexPair u).1 = ProjectiveDStar.leftPoint u := rfl

@[simp] theorem vertexPair_snd (u : ProjectiveDStar.Vertex q t) :
    (vertexPair u).2 = ProjectiveDStar.rightPoint u := rfl

@[simp] theorem vertexPair_incident (u : ProjectiveDStar.Vertex q t) :
    Orthogonal (vertexPair u).1 (vertexPair u).2 :=
  ProjectiveDStar.incident u




theorem compatible_vertexPair_of_not_arc
    (new : ProjectiveDStar.Vertex q t)
    (old : ProjectiveDStar.Vertex q t)
    (h : ¬ ProjectiveDStar.Arc old new) :
    Orthogonal (vertexPair old).1 (vertexPair new).2 →
      Orthogonal (vertexPair new).1 (vertexPair old).2 := by
  intro holdnew
  by_contra hnewold
  exact h ⟨holdnew, hnewold⟩



theorem canExtend_vertexPair_of_not_arc
    (new : ProjectiveDStar.Vertex q t)
    (old : List (ProjectiveDStar.Vertex q t))
    (h : ∀ u ∈ old, ¬ ProjectiveDStar.Arc u new) :
    Container.CanExtend Orthogonal (vertexPair new) (old.map vertexPair) := by
  refine ⟨vertexPair_incident new, ?_⟩
  intro p hp holdnew
  rcases List.mem_map.mp hp with ⟨u, hu, rfl⟩
  exact compatible_vertexPair_of_not_arc new u (h u hu) holdnew



theorem consistent_of_pairwise
    {Q : Type*}
    {R : Q → Q → Prop} (l : List (Q × Q))
    (hinc : ∀ p ∈ l, R p.1 p.2)
    (hpair : l.Pairwise fun new old ↦
      R old.1 new.2 → R new.1 old.2) :
    Container.Consistent R l := by
  induction l with
  | nil => exact Container.consistent_nil R
  | cons p l ih =>
      rw [Container.consistent_cons_iff]
      have hp := List.pairwise_cons.mp hpair
      refine ⟨ih (fun x hx ↦ hinc x (List.mem_cons_of_mem p hx)) hp.2, ?_⟩
      refine ⟨hinc p (by simp), ?_⟩
      intro old hold
      exact hp.1 old hold



theorem consistent_tupleHistory_of_forwardIndependent {m : ℕ}
    (v : Fin m → ProjectiveDStar.Vertex q t)
    (hforward : (ProjectiveDStar.digraph q t).IsForwardIndependent v) :
    Container.Consistent Orthogonal
      (TupleBound.tupleHistory (fun i ↦ vertexPair (v i))) := by
  classical
  apply consistent_of_pairwise
  · intro p hp
    rw [TupleBound.tupleHistory, List.mem_reverse] at hp
    rcases List.mem_ofFn.mp hp with ⟨i, rfl⟩
    exact vertexPair_incident (v i)
  · rw [TupleBound.tupleHistory, List.pairwise_reverse,
      List.pairwise_ofFn]
    intro i j hij
    exact compatible_vertexPair_of_not_arc (v j) (v i)
      (hforward i j hij)



def incidentPairs (q t : ℕ) [Fact q.Prime] :
    Finset (P q t × P q t) := by
  classical
  exact Finset.univ.filter fun p ↦ Orthogonal p.1 p.2

@[simp] theorem mem_incidentPairs_iff (p : P q t × P q t) :
    p ∈ incidentPairs q t ↔ Orthogonal p.1 p.2 := by
  classical
  simp [incidentPairs]

@[simp] theorem vertexPair_mem_incidentPairs
    (u : ProjectiveDStar.Vertex q t) :
    vertexPair u ∈ incidentPairs q t := by
  simp



theorem tupleHistory_isPath_consistentChildren {m : ℕ}
    (v : Fin m → ProjectiveDStar.Vertex q t)
    (hforward : (ProjectiveDStar.digraph q t).IsForwardIndependent v) :
    MarkedTree.IsPath
      (TupleBound.consistentChildren (incidentPairs q t) Orthogonal)
      (TupleBound.tupleHistory (fun i ↦ vertexPair (v i))) := by
  classical
  rw [TupleBound.isPath_consistentChildren_iff]
  refine ⟨consistent_tupleHistory_of_forwardIndependent v hforward, ?_⟩
  intro p hp
  rw [TupleBound.tupleHistory, List.mem_reverse] at hp
  rcases List.mem_ofFn.mp hp with ⟨i, rfl⟩
  exact vertexPair_mem_incidentPairs (v i)

end DStarHistory

end

end Erdos920.ProjectiveContainer

















namespace Erdos920.Pivot

open Erdos920.Container

noncomputable section

variable {P : Type*} [DecidableEq P]

section Strata

variable (points : Finset P) (C : RankClosure P) (R : P → P → Prop)
  [DecidableRel R] (σ : List (P × P))




def pivotLevel : ℕ → ℕ
  | 0 => 0
  | j + 1 =>
      if (Z points C R σ (pivotLevel j)).card <
          (Z points C R σ (j + 1)).card then j + 1
      else pivotLevel j

theorem pivotLevel_mem_range (j : ℕ) :
    pivotLevel points C R σ j < j + 1 := by
  induction j with
  | zero => simp [pivotLevel]
  | succ j ih =>
      rw [pivotLevel]
      split <;> omega

theorem pivotLevel_le (j : ℕ) :
    pivotLevel points C R σ j ≤ j :=
  Nat.le_of_lt_succ (pivotLevel_mem_range points C R σ j)


theorem Z_card_le_pivot {r j : ℕ} (hr : r ≤ j) :
    (Z points C R σ r).card ≤
      (Z points C R σ (pivotLevel points C R σ j)).card := by
  induction j with
  | zero =>
      have : r = 0 := by omega
      subst r
      simp [pivotLevel]
  | succ j ih =>
      rw [pivotLevel]
      split_ifs with hnew
      · by_cases hrnew : r = j + 1
        · subst r
          exact le_rfl
        · exact (ih (Nat.le_of_lt_succ (lt_of_le_of_ne hr hrnew))).trans hnew.le
      · by_cases hrnew : r = j + 1
        · subst r
          exact Nat.le_of_not_gt hnew
        · exact ih (Nat.le_of_lt_succ (lt_of_le_of_ne hr hrnew))


def pivotIndex (j : ℕ) : Fin (j + 1) :=
  ⟨pivotLevel points C R σ j, pivotLevel_mem_range points C R σ j⟩

@[simp] theorem pivotLevel_eq (j : ℕ) :
    pivotLevel points C R σ j = (pivotIndex points C R σ j : ℕ) := rfl

@[simp] theorem pivotIndex_le (j : ℕ) :
    (pivotIndex points C R σ j : ℕ) ≤ j :=
  pivotLevel_le points C R σ j


theorem card_Z_le_card_Z_pivot (j r : ℕ) (hr : r ≤ j) :
    (Z points C R σ r).card ≤
      (Z points C R σ (pivotIndex points C R σ j : ℕ)).card := by
  exact Z_card_le_pivot points C R σ hr



theorem mem_U_iff_exists_mem_Z (j : ℕ) (y : P) :
    y ∈ U points C R σ j ↔
      ∃ r ∈ Finset.range (j + 1), y ∈ Z points C R σ r := by
  constructor
  · intro hy
    have hy' := Finset.mem_filter.mp hy
    refine ⟨prefixRank C R σ y, Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hy'.2), ?_⟩
    exact Finset.mem_filter.mpr ⟨hy'.1, rfl⟩
  · rintro ⟨r, hr, hyr⟩
    have hyr' := Finset.mem_filter.mp hyr
    refine Finset.mem_filter.mpr ⟨hyr'.1, ?_⟩
    rw [hyr'.2]
    exact Nat.le_of_lt_succ (Finset.mem_range.mp hr)


theorem U_eq_biUnion_Z (j : ℕ) :
    U points C R σ j =
      (Finset.range (j + 1)).biUnion fun r ↦ Z points C R σ r := by
  ext y
  rw [mem_U_iff_exists_mem_Z points C R σ]
  simp only [Finset.mem_biUnion]



theorem card_U_le_mul_card_Z_pivot (j : ℕ) :
    (U points C R σ j).card ≤
      (j + 1) * (Z points C R σ (pivotIndex points C R σ j : ℕ)).card := by
  rw [U_eq_biUnion_Z points C R σ]
  calc
    ((Finset.range (j + 1)).biUnion fun r ↦ Z points C R σ r).card ≤
        ∑ r ∈ Finset.range (j + 1), (Z points C R σ r).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _r ∈ Finset.range (j + 1),
        (Z points C R σ (pivotIndex points C R σ j : ℕ)).card := by
      exact Finset.sum_le_sum fun r hr ↦
        card_Z_le_card_Z_pivot points C R σ j r
          (Nat.le_of_lt_succ (Finset.mem_range.mp hr))
    _ = (j + 1) *
        (Z points C R σ (pivotIndex points C R σ j : ℕ)).card := by
      simp


theorem U_card_le_succ_mul_Z_pivot (j : ℕ) :
    (U points C R σ j).card ≤
      (j + 1) * (Z points C R σ (pivotLevel points C R σ j)).card := by
  exact card_U_le_mul_card_Z_pivot points C R σ j




theorem card_U_le_two_mul_card_Z_pivot (j : ℕ) (hj : 0 < j) :
    (U points C R σ j).card ≤
      2 * j * (Z points C R σ (pivotIndex points C R σ j : ℕ)).card := by
  refine (card_U_le_mul_card_Z_pivot points C R σ j).trans ?_
  apply Nat.mul_le_mul_right
  omega

end Strata

section IntegerCut




def pivotCut (q z : ℕ) : ℕ :=
  max 1 (z ⌈/⌉ (32 * q))

@[simp] theorem pivotCut_pos (q z : ℕ) : 0 < pivotCut q z := by
  simp [pivotCut]

theorem ceilDiv_le_pivotCut (q z : ℕ) :
    z ⌈/⌉ (32 * q) ≤ pivotCut q z := by
  exact Nat.le_max_right _ _



theorem card_le_mul_pivotCut {q z : ℕ} (hq : 0 < q) :
    z ≤ (32 * q) * pivotCut q z := by
  exact (le_smul_ceilDiv (by positivity : 0 < 32 * q)).trans
    (Nat.mul_le_mul_left (32 * q) (ceilDiv_le_pivotCut q z))



theorem pivotCut_le_card {q z : ℕ} (hq : 0 < q) (hz : 0 < z) :
    pivotCut q z ≤ z := by
  rw [pivotCut, max_le_iff]
  refine ⟨hz, ?_⟩
  rw [ceilDiv_le_iff_le_mul (by positivity : 0 < 32 * q)]
  have hden : 1 ≤ 32 * q := by omega
  simpa using Nat.mul_le_mul_right z hden




theorem popular_count_le {q z cut pop cap : ℕ}
    (hcutpos : 0 < cut) (hzcut : z ≤ (32 * q) * cut)
    (hinc : pop * cut ≤ z * cap) :
    pop ≤ (32 * q) * cap := by
  apply Nat.le_of_mul_le_mul_right ?_ hcutpos
  calc
    pop * cut ≤ z * cap := hinc
    _ ≤ ((32 * q) * cut) * cap := Nat.mul_le_mul_right cap hzcut
    _ = ((32 * q) * cap) * cut := by ring


theorem popular_count_le_of_pivotCut {q z pop cap : ℕ} (hq : 0 < q)
    (hinc : pop * pivotCut q z ≤ z * cap) :
    pop ≤ (32 * q) * cap := by
  exact popular_count_le (pivotCut_pos q z) (card_le_mul_pivotCut hq) hinc





theorem pivotCut_le_filter_and_not_of_not_poor_not_popular
    {q z : ℕ} {S : Type*}
    (s : Finset S) (A B : S → Prop) [DecidablePred A] [DecidablePred B]
    (hnotPoor : ¬ (s.filter A).card < 2 * pivotCut q z)
    (hnotPopular : ¬ pivotCut q z ≤ (s.filter B).card) :
    pivotCut q z ≤ (s.filter fun x ↦ A x ∧ ¬ B x).card := by
  apply Container.card_filter_and_not_ge
  · exact Nat.le_of_not_gt hnotPoor
  · exact Nat.le_of_lt (Nat.lt_of_not_ge hnotPopular)

end IntegerCut

section ContainerCut

variable (points : Finset P) (C : RankClosure P) (R : P → P → Prop)
  [DecidableRel R] (σ : List (P × P))



theorem pivotCut_le_rankRaisingSet_of_not_poor_not_popular
    (q ℓ : ℕ) (a b : P)
    (ha : ¬ Poor points C R σ ℓ
      (pivotCut q (Z points C R σ ℓ).card) a)
    (hb : ¬ Popular points C R σ ℓ
      (pivotCut q (Z points C R σ ℓ).card) b) :
    pivotCut q (Z points C R σ ℓ).card ≤
      (rankRaisingSet points C R σ ℓ a b).card := by
  exact rankRaisingSet_card_ge_of_not_poor_not_popular
    points C R σ ℓ (pivotCut q (Z points C R σ ℓ).card) a b ha hb




theorem popularInStratum_card_le_of_pivotCut
    (q ℓ cap : ℕ) (hq : 0 < q)
    (hfibre : ∀ y ∈ Z points C R σ ℓ,
      (points.filter fun b ↦ C.Cl b (generators R σ y)).card ≤ cap) :
    (points.filter fun b ↦ Popular points C R σ ℓ
      (pivotCut q (Z points C R σ ℓ).card) b).card ≤
        (32 * q) * cap := by
  apply popular_count_le_of_pivotCut hq
  exact popularInStratum_card_mul_cut_le points C R σ ℓ
    (pivotCut q (Z points C R σ ℓ).card) cap hfibre

end ContainerCut

end

end Erdos920.Pivot












open scoped BigOperators LinearAlgebra.Projectivization

namespace Erdos920.MarkedChildren

noncomputable section

open Erdos920.Projective
open Erdos920.ProjectiveContainer
open Erdos920.Container
open Erdos920.Pivot

section Pivot

variable {P : Type*} [DecidableEq P]

theorem mem_Z_rank (points : Finset P) (C : RankClosure P)
    (R : P → P → Prop) [DecidableRel R]
    (sigma : List (P × P)) {b : P} (hb : b ∈ points) :
    b ∈ Z points C R sigma (prefixRank C R sigma b) := by
  simp [Z, hb]

theorem pivot_Z_nonempty_of_mem (points : Finset P) (C : RankClosure P)
    (R : P → P → Prop) [DecidableRel R]
    (sigma : List (P × P)) {b : P} (hb : b ∈ points) :
    (Z points C R sigma
      (pivotLevel points C R sigma (prefixRank C R sigma b))).Nonempty := by
  have hcard : 1 ≤ (Z points C R sigma (prefixRank C R sigma b)).card :=
    Finset.one_le_card.mpr ⟨b, mem_Z_rank points C R sigma hb⟩
  have hp := Z_card_le_pivot points C R sigma (le_refl (prefixRank C R sigma b))
  exact Finset.card_pos.mp (lt_of_lt_of_le (by omega) (hcard.trans hp))

end Pivot

section ClearedThresholds

variable {P : Type*} [DecidableEq P]


def PoorQ (points : Finset P) (C : RankClosure P) (R : P → P → Prop)
    [DecidableRel R] (q : ℕ) (sigma : List (P × P)) (l : ℕ) (a : P) : Prop :=
  8 * q * (neighborsInStratum points C R sigma l a).card ≤
    (Z points C R sigma l).card


def PopularQ (points : Finset P) (C : RankClosure P) (R : P → P → Prop)
    [DecidableRel R] (q : ℕ) (sigma : List (P × P)) (l : ℕ) (b : P) : Prop :=
  (Z points C R sigma l).card ≤
    16 * q * (closureInStratum points C R sigma l b).card



theorem pivot_card_lt_mul_rankRaising_of_not_poorQ_not_popularQ
    (points : Finset P) (C : RankClosure P) (R : P → P → Prop)
    [DecidableRel R] (q : ℕ) (sigma : List (P × P)) (l : ℕ) (a b : P)
    (ha : ¬ PoorQ points C R q sigma l a)
    (hb : ¬ PopularQ points C R q sigma l b) :
    (Z points C R sigma l).card <
      16 * q * (rankRaisingSet points C R sigma l a b).card := by
  classical
  let Z0 := Z points C R sigma l
  let A := Z0.filter fun y => R a y
  let B := Z0.filter fun y => C.Cl b (generators R sigma y)
  let E := Z0.filter fun y => R a y ∧ ¬ C.Cl b (generators R sigma y)
  have hpoor : Z0.card < 8 * q * A.card := Nat.lt_of_not_ge ha
  have hpopular : 16 * q * B.card < Z0.card := Nat.lt_of_not_ge hb
  have hE : E = A \ B := by
    ext y
    simp only [E, A, B, Finset.mem_filter, Finset.mem_sdiff]
    aesop
  have hinter : (A ∩ B).card ≤ B.card :=
    Finset.card_le_card Finset.inter_subset_right
  have hsplit := Finset.card_sdiff_add_card_inter A B
  rw [← hE] at hsplit
  have hmulE : 16 * q * E.card + 16 * q * (A ∩ B).card =
      2 * (8 * q * A.card) := by
    calc
      16 * q * E.card + 16 * q * (A ∩ B).card =
          16 * q * (E.card + (A ∩ B).card) := by ring
      _ = 16 * q * A.card := by rw [hsplit]
      _ = 2 * (8 * q * A.card) := by ring
  have hB : 16 * q * (A ∩ B).card < Z0.card :=
    (Nat.mul_le_mul_left (16 * q) hinter).trans_lt hpopular
  have htwice : 2 * Z0.card <
      16 * q * E.card + 16 * q * (A ∩ B).card := by
    rw [hmulE]
    omega
  have hz : Z0.card < 16 * q * E.card := by omega
  simpa [Z0, E, rankRaisingSet] using hz


theorem U_card_shrink_of_not_poorQ_not_popularQ
    (points : Finset P) (C : RankClosure P) (R : P → P → Prop)
    [DecidableRel R] (q t : ℕ) (sigma : List (P × P)) (l : ℕ) (a b : P)
    (hU : (U points C R sigma l).card ≤
      2 * t * (Z points C R sigma l).card)
    (ha : ¬ PoorQ points C R q sigma l a)
    (hb : ¬ PopularQ points C R q sigma l b) :
    (32 * t * q) * (U points C R ((a, b) :: sigma) l).card ≤
      (32 * t * q - 1) * (U points C R sigma l).card := by
  have hrank := pivot_card_lt_mul_rankRaising_of_not_poorQ_not_popularQ
    points C R q sigma l a b ha hb
  have hmono := U_mono_cons points C R (a, b) sigma l
  have hraise := rankRaisingSet_subset_U_diff points C R sigma l a b
  have hdisj : Disjoint (U points C R ((a, b) :: sigma) l)
      (rankRaisingSet points C R sigma l a b) := by
    apply Finset.disjoint_left.mpr
    intro y hyNew hyRaise
    exact (Finset.mem_sdiff.mp (hraise hyRaise)).2 hyNew
  have hunion : U points C R ((a, b) :: sigma) l ∪
      rankRaisingSet points C R sigma l a b ⊆ U points C R sigma l := by
    intro y hy
    rcases Finset.mem_union.mp hy with hy | hy
    · exact hmono hy
    · exact (Finset.mem_sdiff.mp (hraise hy)).1
  have hadd : (U points C R ((a, b) :: sigma) l).card +
      (rankRaisingSet points C R sigma l a b).card ≤
        (U points C R sigma l).card := by
    rw [← Finset.card_union_of_disjoint hdisj]
    exact Finset.card_le_card hunion
  have hcut : (U points C R sigma l).card ≤
      (32 * t * q) * (rankRaisingSet points C R sigma l a b).card := by
    calc
      (U points C R sigma l).card ≤
          2 * t * (Z points C R sigma l).card := hU
      _ ≤ 2 * t * (16 * q *
          (rankRaisingSet points C R sigma l a b).card) :=
        Nat.mul_le_mul_left (2 * t) hrank.le
      _ = (32 * t * q) *
          (rankRaisingSet points C R sigma l a b).card := by ring
  let K := 32 * t * q
  by_cases hK : K = 0
  · simp [K, hK]
  · have hKpos : 1 ≤ K := Nat.one_le_iff_ne_zero.mpr hK
    have hmuladd : K * (U points C R ((a, b) :: sigma) l).card +
          K * (rankRaisingSet points C R sigma l a b).card ≤
        K * (U points C R sigma l).card := by
      simpa [mul_add] using Nat.mul_le_mul_left K hadd
    have hwithU : K * (U points C R ((a, b) :: sigma) l).card +
          (U points C R sigma l).card ≤
        K * (U points C R sigma l).card :=
      (Nat.add_le_add_left hcut _).trans hmuladd
    have hrhs : (K - 1) * (U points C R sigma l).card +
          (U points C R sigma l).card = K * (U points C R sigma l).card := by
      calc
        (K - 1) * (U points C R sigma l).card +
              (U points C R sigma l).card =
            (K - 1) * (U points C R sigma l).card +
              1 * (U points C R sigma l).card := by simp
        _ = ((K - 1) + 1) * (U points C R sigma l).card := by rw [add_mul]
        _ = K * (U points C R sigma l).card := by rw [Nat.sub_add_cancel hKpos]
    apply Nat.le_of_add_le_add_right
    rw [hrhs]
    exact hwithU

end ClearedThresholds

section Marking

variable {P : Type*} [DecidableEq P]


def chosenPivot (points : Finset P) (C : RankClosure P)
    (R : P → P → Prop) [DecidableRel R]
    (sigma : List (P × P)) (p : P × P) : ℕ :=
  pivotLevel points C R sigma (prefixRank C R sigma p.2)



def SmallPivotQ (points : Finset P) (C : RankClosure P)
    (R : P → P → Prop) [DecidableRel R] (q : ℕ)
    (sigma : List (P × P)) (p : P × P) : Prop :=
  (Z points C R sigma (chosenPivot points C R sigma p)).card < 16 * q





def marked (points : Finset P) (C : RankClosure P)
    (R : P → P → Prop) [DecidableRel R] (q : ℕ)
    (sigma : List (P × P)) (p : P × P) : Bool :=
  by
    classical
    exact decide
      (PoorQ points C R q sigma (chosenPivot points C R sigma p) p.1 ∨
       PopularQ points C R q sigma (chosenPivot points C R sigma p) p.2)

theorem marked_eq_false_iff (points : Finset P) (C : RankClosure P)
    (R : P → P → Prop) [DecidableRel R] (q : ℕ)
    (sigma : List (P × P)) (p : P × P) :
    marked points C R q sigma p = false ↔
      ¬ PoorQ points C R q sigma (chosenPivot points C R sigma p) p.1 ∧
      ¬ PopularQ points C R q sigma (chosenPivot points C R sigma p) p.2 := by
  classical
  simp [marked]




def levelIndex (T : ℕ) (points : Finset P) (C : RankClosure P)
    (R : P → P → Prop) [DecidableRel R]
    (sigma : List (P × P)) (p : P × P) : Fin (T + 1) :=
  ⟨min (chosenPivot points C R sigma p) T, by omega⟩

theorem levelIndex_val_of_rank_le (T : ℕ) (points : Finset P)
    (C : RankClosure P) (R : P → P → Prop) [DecidableRel R]
    (sigma : List (P × P)) (p : P × P)
    (hrank : prefixRank C R sigma p.2 ≤ T) :
    (levelIndex T points C R sigma p : ℕ) =
      chosenPivot points C R sigma p := by
  change min (chosenPivot points C R sigma p) T =
    chosenPivot points C R sigma p
  exact Nat.min_eq_left ((pivotLevel_le points C R sigma _).trans hrank)



theorem chosen_U_card_le
    (points : Finset P) (C : RankClosure P) (R : P → P → Prop)
    [DecidableRel R] (T : ℕ) (sigma : List (P × P)) (p : P × P)
    (hrank : prefixRank C R sigma p.2 + 1 ≤ T) :
    (U points C R sigma (chosenPivot points C R sigma p)).card ≤
      T * (Z points C R sigma (chosenPivot points C R sigma p)).card := by
  have hU0 := U_card_le_succ_mul_Z_pivot points C R sigma
    (prefixRank C R sigma p.2)
  have hmonoU : U points C R sigma (chosenPivot points C R sigma p) ⊆
      U points C R sigma (prefixRank C R sigma p.2) := by
    intro y hy
    have hy' := Finset.mem_filter.mp hy
    exact Finset.mem_filter.mpr ⟨hy'.1,
      hy'.2.trans (pivotLevel_le points C R sigma _)⟩
  calc
    (U points C R sigma (chosenPivot points C R sigma p)).card ≤
        (U points C R sigma (prefixRank C R sigma p.2)).card :=
      Finset.card_le_card hmonoU
    _ ≤ (prefixRank C R sigma p.2 + 1) *
        (Z points C R sigma (chosenPivot points C R sigma p)).card := hU0
    _ ≤ T * (Z points C R sigma (chosenPivot points C R sigma p)).card :=
      Nat.mul_le_mul_right _ hrank



theorem chosen_U_shrink_of_not_poorQ_not_popularQ
    (points : Finset P) (C : RankClosure P) (R : P → P → Prop)
    [DecidableRel R] (q t : ℕ) (sigma : List (P × P)) (p : P × P)
    (hrank : prefixRank C R sigma p.2 + 1 ≤ 2 * t)
    (hpoor : ¬ PoorQ points C R q sigma
      (chosenPivot points C R sigma p) p.1)
    (hpopular : ¬ PopularQ points C R q sigma
      (chosenPivot points C R sigma p) p.2) :
    (32 * t * q) *
        (U points C R (p :: sigma) (chosenPivot points C R sigma p)).card ≤
      (32 * t * q - 1) *
        (U points C R sigma (chosenPivot points C R sigma p)).card := by
  exact U_card_shrink_of_not_poorQ_not_popularQ points C R q t sigma
    (chosenPivot points C R sigma p) p.1 p.2
    (chosen_U_card_le points C R (2 * t) sigma p hrank) hpoor hpopular



theorem chosen_U_shrink_of_unmarked
    (points : Finset P) (C : RankClosure P) (R : P → P → Prop)
    [DecidableRel R] (q t : ℕ) (sigma : List (P × P)) (p : P × P)
    (hrank : prefixRank C R sigma p.2 + 1 ≤ 2 * t)
    (hunmarked : marked points C R q sigma p = false) :
    (32 * t * q) *
        (U points C R (p :: sigma) (chosenPivot points C R sigma p)).card ≤
    (32 * t * q - 1) *
        (U points C R sigma (chosenPivot points C R sigma p)).card := by
  have hfalse := (marked_eq_false_iff points C R q sigma p).mp hunmarked
  exact chosen_U_shrink_of_not_poorQ_not_popularQ points C R q t sigma p
    hrank hfalse.1 hfalse.2



theorem chosen_U_positive_of_second_mem
    (points : Finset P) (C : RankClosure P) (R : P → P → Prop)
    [DecidableRel R] (sigma : List (P × P)) (p : P × P)
    (hb : p.2 ∈ points) :
    1 ≤ (U points C R sigma (chosenPivot points C R sigma p)).card := by
  have hpivot := pivot_Z_nonempty_of_mem points C R sigma hb
  apply Finset.one_le_card.mpr
  obtain ⟨y, hy⟩ := hpivot
  refine ⟨y, ?_⟩
  exact Z_subset_U points C R sigma _ hy

end Marking

section ProjectiveCertificate

open Erdos920.TupleBound

noncomputable local instance classicalDecidableProp (p : Prop) : Decidable p := Classical.propDecidable p
noncomputable local instance classicalDecidableEq (α : Type*) : DecidableEq α := Classical.decEq α


variable {q t : ℕ} [Fact q.Prime]

abbrev PointT (q t : ℕ) [Fact q.Prime] :=
  Projective.Point (ZMod q) (t + 1)

local instance pointFintype (q t : ℕ) [Fact q.Prime] :
    Fintype (PointT q t) := Fintype.ofFinite _

local instance orthogonalDecidable (q t : ℕ) [Fact q.Prime] :
    DecidableRel
      (@Projective.Orthogonal (ZMod q) _ (t + 1)) := Classical.decRel _


def projectiveVertices (q t : ℕ) [Fact q.Prime] : Finset (PointT q t × PointT q t) :=
  ProjectiveContainer.incidentPairs q t


def projectiveChildren (q t : ℕ) [Fact q.Prime]
    (sigma : List (PointT q t × PointT q t)) : Finset (PointT q t × PointT q t) :=
  consistentChildren (projectiveVertices q t) Projective.Orthogonal sigma

theorem projectiveChildren_eq_extensionChildren (q t : ℕ) [Fact q.Prime]
    (sigma : List (PointT q t × PointT q t)) :
    projectiveChildren q t sigma =
      extensionChildren (Finset.univ : Finset (PointT q t))
        Projective.Orthogonal sigma := by
  ext p
  simp [projectiveChildren, projectiveVertices, consistentChildren,
    extensionChildren]


def projectiveMarked (q t : ℕ) [Fact q.Prime]
    (sigma : List (PointT q t × PointT q t)) (p : PointT q t × PointT q t) : Bool :=
  marked (Finset.univ : Finset (PointT q t))
    (projectiveRankClosure q t) Projective.Orthogonal q sigma p



def projectiveLevel (q t : ℕ) [Fact q.Prime]
    (sigma : List (PointT q t × PointT q t))
    (p : PointT q t × PointT q t) : Fin (t + 2) :=
  levelIndex (t + 1) (Finset.univ : Finset (PointT q t))
    (projectiveRankClosure q t) Projective.Orthogonal sigma p



theorem projective_prefixRank_le (sigma : List (PointT q t × PointT q t))
    (b : PointT q t) :
    prefixRank (projectiveRankClosure q t) Projective.Orthogonal sigma b ≤ t + 1 := by
  exact projectiveRankClosure_rank_le_dim
    (generators Projective.Orthogonal sigma b)

theorem projectiveLevel_val (sigma : List (PointT q t × PointT q t))
    (p : PointT q t × PointT q t) :
    (projectiveLevel q t sigma p : ℕ) =
      chosenPivot (Finset.univ : Finset (PointT q t))
        (projectiveRankClosure q t) Projective.Orthogonal sigma p := by
  exact levelIndex_val_of_rank_le (t + 1)
    (Finset.univ : Finset (PointT q t)) (projectiveRankClosure q t)
    Projective.Orthogonal sigma p (projective_prefixRank_le sigma p.2)



def projectiveShrinkCertificate (q t : ℕ) [Fact q.Prime] (ht : 2 ≤ t) :
    PathShrinkCertificate (L := Fin (t + 2))
      (projectiveChildren q t) (projectiveMarked q t)
      (32 * t * q) (Fintype.card (PointT q t)) where
  potential l sigma :=
    (U (Finset.univ : Finset (PointT q t)) (projectiveRankClosure q t)
      Projective.Orthogonal sigma l.1).card
  level := projectiveLevel q t
  initial_le l := by
    exact Finset.card_le_card (Finset.filter_subset _ _)
  mono l sigma p hp := by
    exact Finset.card_le_card
      (U_mono_cons (Finset.univ : Finset (PointT q t))
        (projectiveRankClosure q t) Projective.Orthogonal p sigma l.1)
  positive sigma p hp hunmarked := by
    rw [projectiveLevel_val sigma p]
    exact chosen_U_positive_of_second_mem
      (Finset.univ : Finset (PointT q t)) (projectiveRankClosure q t)
      Projective.Orthogonal sigma p (Finset.mem_univ _)
  contract sigma p hp hunmarked := by
    have hrank : prefixRank (projectiveRankClosure q t)
        Projective.Orthogonal sigma p.2 + 1 ≤ 2 * t := by
      have hcap := projective_prefixRank_le sigma p.2
      omega
    rw [projectiveLevel_val sigma p]
    exact chosen_U_shrink_of_unmarked
      (Finset.univ : Finset (PointT q t)) (projectiveRankClosure q t)
      Projective.Orthogonal q t sigma p hrank hunmarked

end ProjectiveCertificate

end

end Erdos920.MarkedChildren














open scoped BigOperators LinearAlgebra.Projectivization

namespace Erdos920.PoorChildren

noncomputable section

open Erdos920.Container
open Erdos920.DesignAdapter
open Erdos920.MarkedChildren
open Erdos920.Mixing
open Erdos920.Pivot
open Erdos920.Projective
open Erdos920.ProjectiveContainer

noncomputable local instance classicalDecidableProp (p : Prop) : Decidable p := Classical.propDecidable p
noncomputable local instance classicalDecidableEq (α : Type*) : DecidableEq α := Classical.decEq α


variable {X : Type*} [DecidableEq X]




def edgePairs (R : X -> X -> Prop) [DecidableRel R]
    (A B : Finset X) : Finset (X × X) :=
  A.biUnion fun a => (B.filter (R a)).image fun b => (a, b)

@[simp] theorem mem_edgePairs_iff (R : X -> X -> Prop) [DecidableRel R]
    (A B : Finset X) (p : X × X) :
    p ∈ edgePairs R A B <-> p.1 ∈ A ∧ p.2 ∈ B ∧ R p.1 p.2 := by
  classical
  constructor
  · intro hp
    obtain ⟨a, ha, hp⟩ := Finset.mem_biUnion.mp hp
    obtain ⟨b, hb, hab⟩ := Finset.mem_image.mp hp
    have hb' := Finset.mem_filter.mp hb
    cases hab
    exact ⟨ha, hb'.1, hb'.2⟩
  · rintro ⟨ha, hb, hp⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨p.1, ha, ?_⟩
    apply Finset.mem_image.mpr
    exact ⟨p.2, Finset.mem_filter.mpr ⟨hb, hp⟩, Prod.ext rfl rfl⟩




theorem card_edgePairs_le_orderedEdges
    (R : X -> X -> Prop) [DecidableRel R] (A B : Finset X) :
    (edgePairs R A B).card ≤ orderedEdges R A B := by
  classical
  calc
    (edgePairs R A B).card ≤
        ∑ a ∈ A, ((B.filter (R a)).image fun b => (a, b)).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ a ∈ A, (B.filter (R a)).card := by
      exact Finset.sum_le_sum fun _ _ => Finset.card_image_le
    _ = orderedEdges R A B := by
      rfl

theorem card_le_orderedEdges_of_subset_edgePairs
    (R : X -> X -> Prop) [DecidableRel R] (A B : Finset X)
    (S : Finset (X × X)) (hS : S ⊆ edgePairs R A B) :
    S.card ≤ orderedEdges R A B :=
  (Finset.card_le_card hS).trans (card_edgePairs_le_orderedEdges R A B)



abbrev PointT (q t : ℕ) [Fact q.Prime] :=
  Point (ZMod q) (t + 1)

local instance pointFintype (q t : ℕ) [Fact q.Prime] :
    Fintype (PointT q t) := Fintype.ofFinite _

local instance orthogonalDecidable (q t : ℕ) [Fact q.Prime] :
    DecidableRel (@Orthogonal (ZMod q) _ (t + 1)) := Classical.decRel _



def poorChildrenAtRank (q t : ℕ) [Fact q.Prime]
    (sigma : List (PointT q t × PointT q t)) (j : ℕ) :
    Finset (PointT q t × PointT q t) :=
  let points : Finset (PointT q t) := Finset.univ
  let C := projectiveRankClosure q t
  (extensionChildren points Orthogonal sigma).filter fun p =>
    prefixRank C Orthogonal sigma p.2 = j ∧
      PoorQ points C Orthogonal q sigma
        (pivotLevel points C Orthogonal sigma j) p.1

@[simp] theorem mem_poorChildrenAtRank_iff
    (q t : ℕ) [Fact q.Prime]
    (sigma : List (PointT q t × PointT q t)) (j : ℕ)
    (p : PointT q t × PointT q t) :
    p ∈ poorChildrenAtRank q t sigma j <->
      p ∈ extensionChildren (Finset.univ : Finset (PointT q t))
        Orthogonal sigma ∧
      prefixRank (projectiveRankClosure q t) Orthogonal sigma p.2 = j ∧
      PoorQ (Finset.univ : Finset (PointT q t))
        (projectiveRankClosure q t) Orthogonal q sigma
        (pivotLevel (Finset.univ : Finset (PointT q t))
          (projectiveRankClosure q t) Orthogonal sigma j) p.1 := by
  rw [poorChildrenAtRank, Finset.mem_filter]



theorem poorChildrenAtRank_subset_edgePairs
    (q t : ℕ) [Fact q.Prime]
    (sigma : List (PointT q t × PointT q t)) (j : ℕ) :
    let points : Finset (PointT q t) := Finset.univ
    let C := projectiveRankClosure q t
    let l := pivotLevel points C Orthogonal sigma j
    poorChildrenAtRank q t sigma j ⊆
      edgePairs Orthogonal
        (poorSet q t (Z points C Orthogonal sigma l))
        (Z points C Orthogonal sigma j) := by
  classical
  dsimp only
  intro p hp
  have hp' := (mem_poorChildrenAtRank_iff q t sigma j p).mp hp
  have hrel := extensionChildren_subset_relationPairs
    (Finset.univ : Finset (PointT q t)) Orthogonal sigma hp'.1
  have hrel' := (mem_relationPairs_iff
    (Finset.univ : Finset (PointT q t)) Orthogonal p).mp hrel
  apply (mem_edgePairs_iff Orthogonal _ _ p).mpr
  refine ⟨?_, ?_, hrel'.2.2⟩
  · apply (mem_poorSet_iff q t _ p.1).mpr
    simpa [PoorQ, neighborsInStratum] using hp'.2.2
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp'.2.1⟩



theorem card_rankStratum_le_card_pivotStratum
    (q t : ℕ) [Fact q.Prime]
    (sigma : List (PointT q t × PointT q t)) (j : ℕ) :
    let points : Finset (PointT q t) := Finset.univ
    let C := projectiveRankClosure q t
    (Z points C Orthogonal sigma j).card ≤
      (Z points C Orthogonal sigma
        (pivotLevel points C Orthogonal sigma j)).card := by
  dsimp only
  exact Z_card_le_pivot (Finset.univ : Finset (PointT q t))
    (projectiveRankClosure q t) Orthogonal sigma (le_refl j)




theorem card_poorChildrenAtRank_le
    (q t : ℕ) [Fact q.Prime] (ht : 2 ≤ t)
    (sigma : List (PointT q t × PointT q t)) (j : ℕ) :
    (poorChildrenAtRank q t sigma j).card ≤ 2048 * q ^ t := by
  let points : Finset (PointT q t) := Finset.univ
  let C := projectiveRankClosure q t
  let l := pivotLevel points C Orthogonal sigma j
  let A := poorSet q t (Z points C Orthogonal sigma l)
  let B := Z points C Orthogonal sigma j
  calc
    (poorChildrenAtRank q t sigma j).card ≤
        orderedEdges Orthogonal A B := by
      apply card_le_orderedEdges_of_subset_edgePairs
      simpa [points, C, l, A, B] using
        poorChildrenAtRank_subset_edgePairs q t sigma j
    _ ≤ 2048 * q ^ t := by
      apply poorSet_edges_le q t ht
      simpa [points, C, l, B] using
        card_rankStratum_le_card_pivotStratum q t sigma j





theorem orthogonal_generators_of_canExtend
    (q t : ℕ) [Fact q.Prime]
    (sigma : List (PointT q t × PointT q t))
    (p : PointT q t × PointT q t)
    (hp : CanExtend Orthogonal p sigma) :
    ∀ z ∈ generators Orthogonal sigma p.2, Orthogonal p.1 z := by
  intro z hz
  rw [generators] at hz
  obtain ⟨old, hold, rfl⟩ := Finset.mem_image.mp hz
  have hold' := Finset.mem_filter.mp hold
  exact hp.2 old (by simpa using hold'.1) hold'.2



theorem prefixRank_second_le_of_canExtend
    (q t : ℕ) [Fact q.Prime]
    (sigma : List (PointT q t × PointT q t))
    (p : PointT q t × PointT q t)
    (hp : CanExtend Orthogonal p sigma) :
    prefixRank (projectiveRankClosure q t) Orthogonal sigma p.2 ≤ t := by
  let S := generators Orthogonal sigma p.2
  have hspan : pointSpan S ≤ orthSpace p.1 := by
    unfold pointSpan
    exact Finset.sup_le fun z hz =>
      (orthogonal_iff_submodule_le p.1 z).mp
        (orthogonal_generators_of_canExtend q t sigma p hp z hz)
  change Module.finrank (ZMod q) (pointSpan S) ≤ t
  calc
    Module.finrank (ZMod q) (pointSpan S) ≤
        Module.finrank (ZMod q) (orthSpace p.1) :=
      Submodule.finrank_mono hspan
    _ = t := by simpa using finrank_orthSpace p.1


theorem prefixRank_second_le_of_mem_extensionChildren
    (q t : ℕ) [Fact q.Prime]
    (sigma : List (PointT q t × PointT q t))
    (p : PointT q t × PointT q t)
    (hp : p ∈ extensionChildren
      (Finset.univ : Finset (PointT q t)) Orthogonal sigma) :
    prefixRank (projectiveRankClosure q t) Orthogonal sigma p.2 ≤ t := by
  have hp' := Finset.mem_filter.mp hp
  exact prefixRank_second_le_of_canExtend q t sigma p hp'.2



def poorChildren (q t : ℕ) [Fact q.Prime]
    (sigma : List (PointT q t × PointT q t)) :
    Finset (PointT q t × PointT q t) :=
  let points : Finset (PointT q t) := Finset.univ
  let C := projectiveRankClosure q t
  (extensionChildren points Orthogonal sigma).filter fun p =>
    PoorQ points C Orthogonal q sigma
      (pivotLevel points C Orthogonal sigma
        (prefixRank C Orthogonal sigma p.2)) p.1

@[simp] theorem mem_poorChildren_iff
    (q t : ℕ) [Fact q.Prime]
    (sigma : List (PointT q t × PointT q t))
    (p : PointT q t × PointT q t) :
    p ∈ poorChildren q t sigma <->
      p ∈ extensionChildren (Finset.univ : Finset (PointT q t))
        Orthogonal sigma ∧
      PoorQ (Finset.univ : Finset (PointT q t))
        (projectiveRankClosure q t) Orthogonal q sigma
        (pivotLevel (Finset.univ : Finset (PointT q t))
          (projectiveRankClosure q t) Orthogonal sigma
          (prefixRank (projectiveRankClosure q t) Orthogonal sigma p.2)) p.1 := by
  rw [poorChildren, Finset.mem_filter]


theorem poorChildren_subset_biUnion_rank
    (q t : ℕ) [Fact q.Prime]
    (sigma : List (PointT q t × PointT q t)) :
    poorChildren q t sigma ⊆
      (Finset.range (t + 1)).biUnion fun j =>
        poorChildrenAtRank q t sigma j := by
  intro p hp
  have hp' := (mem_poorChildren_iff q t sigma p).mp hp
  let j := prefixRank (projectiveRankClosure q t) Orthogonal sigma p.2
  apply Finset.mem_biUnion.mpr
  refine ⟨j, Finset.mem_range.mpr (Nat.lt_succ_iff.mpr ?_), ?_⟩
  · exact prefixRank_second_le_of_mem_extensionChildren q t sigma p hp'.1
  · apply (mem_poorChildrenAtRank_iff q t sigma j p).mpr
    exact ⟨hp'.1, rfl, hp'.2⟩



theorem card_poorChildren_le
    (q t : ℕ) [Fact q.Prime] (ht : 2 ≤ t)
    (sigma : List (PointT q t × PointT q t)) :
    (poorChildren q t sigma).card ≤
      2048 * (t + 1) * q ^ t := by
  calc
    (poorChildren q t sigma).card ≤
        ((Finset.range (t + 1)).biUnion fun j =>
          poorChildrenAtRank q t sigma j).card :=
      Finset.card_le_card (poorChildren_subset_biUnion_rank q t sigma)
    _ ≤ ∑ j ∈ Finset.range (t + 1),
        (poorChildrenAtRank q t sigma j).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _j ∈ Finset.range (t + 1), 2048 * q ^ t := by
      exact Finset.sum_le_sum fun j _ =>
        card_poorChildrenAtRank_le q t ht sigma j
    _ = 2048 * (t + 1) * q ^ t := by
      simp
      ring

end

end Erdos920.PoorChildren

















open scoped BigOperators LinearAlgebra.Projectivization

namespace Erdos920.SpanCounts

noncomputable section

open Erdos920.Projective
open Erdos920.ProjectiveContainer

noncomputable local instance classicalDecidableProp (p : Prop) : Decidable p := Classical.propDecidable p
noncomputable local instance classicalDecidableEq (α : Type*) : DecidableEq α := Classical.decEq α


local instance pointFintype (q d : ℕ) [Fact q.Prime] :
    Fintype (Point (ZMod q) d) := Fintype.ofFinite _

variable {q d t r : ℕ} [Fact q.Prime]




theorem card_filter_inClosure_eq_geomSum
    (S : Finset (Point (ZMod q) d)) :
    (Finset.univ.filter fun p ↦ InClosure p S).card =
      ∑ i ∈ Finset.range (Module.finrank (ZMod q) (pointSpan S)), q ^ i := by
  classical
  rw [card_filter_univ_eq_natCard_subtype]
  simpa [InClosure, Nat.card_zmod] using
    (natCard_pointsIn (pointSpan S))



theorem card_filter_inClosure_le_two_mul_pow_pred
    (S : Finset (Point (ZMod q) d))
    (hr : Module.finrank (ZMod q) (pointSpan S) = r) :
    (Finset.univ.filter fun p ↦ InClosure p S).card ≤ 2 * q ^ (r - 1) := by
  calc
    (Finset.univ.filter fun p ↦ InClosure p S).card =
        ∑ i ∈ Finset.range r, q ^ i := by
      simpa only [hr] using card_filter_inClosure_eq_geomSum S
    _ ≤ 2 * q ^ (r - 1) :=
      geomSum_le_two_mul_pow_pred q r (Fact.out : q.Prime).two_le


theorem card_filter_inClosure_eq_zero_of_rank_eq_zero
    (S : Finset (Point (ZMod q) d))
    (hr : Module.finrank (ZMod q) (pointSpan S) = 0) :
    (Finset.univ.filter fun p ↦ InClosure p S).card = 0 := by
  calc
    (Finset.univ.filter fun p ↦ InClosure p S).card =
        ∑ i ∈ Finset.range 0, q ^ i := by
      simpa only [hr] using card_filter_inClosure_eq_geomSum S
    _ = 0 := by simp


theorem card_filter_rankClosure_cl_le_two_mul_pow_pred
    (S : Finset (Point (ZMod q) d))
    (hr : (rankClosure (F := ZMod q) (d := d)).rank S = r) :
    (Finset.univ.filter fun p ↦
        (rankClosure (F := ZMod q) (d := d)).Cl p S).card ≤
      2 * q ^ (r - 1) := by
  exact card_filter_inClosure_le_two_mul_pow_pred S hr


theorem card_filter_rankClosure_cl_eq_zero_of_rank_eq_zero
    (S : Finset (Point (ZMod q) d))
    (hr : (rankClosure (F := ZMod q) (d := d)).rank S = 0) :
    (Finset.univ.filter fun p ↦
        (rankClosure (F := ZMod q) (d := d)).Cl p S).card = 0 := by
  exact card_filter_inClosure_eq_zero_of_rank_eq_zero S hr


theorem card_filter_rankClosure_cl_le_if
    (S : Finset (Point (ZMod q) d))
    (hr : (rankClosure (F := ZMod q) (d := d)).rank S = r) :
    (Finset.univ.filter fun p ↦
        (rankClosure (F := ZMod q) (d := d)).Cl p S).card ≤
      if r = 0 then 0 else 2 * q ^ (r - 1) := by
  split_ifs with hzero
  · exact (card_filter_rankClosure_cl_eq_zero_of_rank_eq_zero S
      (hr.trans hzero)).le
  · exact card_filter_rankClosure_cl_le_two_mul_pow_pred S hr



theorem finrank_pointSpan_le_ambient
    (S : Finset (Point (ZMod q) d)) :
    Module.finrank (ZMod q) (pointSpan S) ≤ d := by
  calc
    Module.finrank (ZMod q) (pointSpan S) ≤
        Module.finrank (ZMod q) (Fin d → ZMod q) := Submodule.finrank_le _
    _ = d := Module.finrank_fin_fun (ZMod q)





def spanOrthSpace (S : Finset (Point (ZMod q) d)) :
    Submodule (ZMod q) (Fin d → ZMod q) :=
  LinearMap.BilinForm.orthogonal
    (dotProductBilin (ZMod q) (ZMod q) :
      LinearMap.BilinForm (ZMod q) (Fin d → ZMod q))
    (pointSpan S)


theorem dotProductBilin_nondegenerate :
    (dotProductBilin (ZMod q) (ZMod q) :
      (Fin d → ZMod q) →ₗ[ZMod q] (Fin d → ZMod q) →ₗ[ZMod q] ZMod q).Nondegenerate := by
  constructor
  · intro x hx
    apply dotProduct_eq_zero x
    exact hx
  · intro y hy
    apply dotProduct_eq_zero y
    intro x
    rw [dotProduct_comm]
    exact hy x



theorem finrank_spanOrthSpace (S : Finset (Point (ZMod q) d)) :
    Module.finrank (ZMod q) (spanOrthSpace S) =
      d - Module.finrank (ZMod q) (pointSpan S) := by
  rw [spanOrthSpace,
    LinearMap.BilinForm.finrank_orthogonal dotProductBilin_nondegenerate,
    Module.finrank_fin_fun]



theorem submodule_le_spanOrthSpace_iff
    (a : Point (ZMod q) d) (S : Finset (Point (ZMod q) d)) :
    a.submodule ≤ spanOrthSpace S ↔
      ∀ p ∈ S, Orthogonal p a := by
  constructor
  · intro ha p hp
    rw [orthogonal_iff_submodule_le]
    intro v hv
    have hva : v ∈ spanOrthSpace S := ha hv
    exact hva p.rep (submodule_le_pointSpan_of_mem hp
      (by rw [Projectivization.submodule_eq]
          exact Submodule.mem_span_singleton_self p.rep))
  · intro ha
    rw [Projectivization.submodule_eq, Submodule.span_singleton_le_iff_mem]
    intro v hv
    have hspan : pointSpan S ≤
        LinearMap.ker
          ((dotProductBilin (ZMod q) (ZMod q) :
            LinearMap.BilinForm (ZMod q) (Fin d → ZMod q)).flip a.rep) := by
      unfold pointSpan
      apply Finset.sup_le
      intro p hp
      rw [Projectivization.submodule_eq, Submodule.span_singleton_le_iff_mem]
      change p.rep ⬝ᵥ a.rep = 0
      have hap := (orthogonal_iff_submodule_le p a).mp (ha p hp)
      exact hap (by
        rw [Projectivization.submodule_eq]
        exact Submodule.mem_span_singleton_self a.rep)
    exact hspan hv


theorem card_filter_orthogonal_to_span_eq_geomSum
    (S : Finset (Point (ZMod q) d)) :
    (Finset.univ.filter fun a ↦ ∀ p ∈ S, Orthogonal p a).card =
      ∑ i ∈ Finset.range
        (d - Module.finrank (ZMod q) (pointSpan S)), q ^ i := by
  classical
  rw [card_filter_univ_eq_natCard_subtype]
  have hequiv :
      {a : Point (ZMod q) d // ∀ p ∈ S, Orthogonal p a} ≃
        {a : Point (ZMod q) d // a.submodule ≤ spanOrthSpace S} :=
    Equiv.setCongr (Set.ext fun a ↦ (submodule_le_spanOrthSpace_iff a S).symm)
  calc
    Nat.card {a : Point (ZMod q) d // ∀ p ∈ S, Orthogonal p a} =
        Nat.card {a : Point (ZMod q) d // a.submodule ≤ spanOrthSpace S} :=
      Nat.card_congr hequiv
    _ = ∑ i ∈ Finset.range (Module.finrank (ZMod q) (spanOrthSpace S)), q ^ i := by
      simpa [Nat.card_zmod] using natCard_pointsIn (spanOrthSpace S)
    _ = ∑ i ∈ Finset.range
        (d - Module.finrank (ZMod q) (pointSpan S)), q ^ i := by
      rw [finrank_spanOrthSpace]


theorem card_filter_left_orthogonal_to_span_eq_geomSum
    (S : Finset (Point (ZMod q) d)) :
    (Finset.univ.filter fun a ↦ ∀ p ∈ S, Orthogonal a p).card =
      ∑ i ∈ Finset.range
        (d - Module.finrank (ZMod q) (pointSpan S)), q ^ i := by
  have heq :
      (Finset.univ.filter fun a : Point (ZMod q) d ↦
          ∀ p ∈ S, Orthogonal a p) =
        Finset.univ.filter fun a ↦ ∀ p ∈ S, Orthogonal p a := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor <;> intro h p hp
    · exact (orthogonal_comm p a).mpr (h p hp)
    · exact (orthogonal_comm a p).mpr (h p hp)
  rw [heq, card_filter_orthogonal_to_span_eq_geomSum]



theorem card_filter_orthogonal_to_span_le_two_mul_pow
    (S : Finset (Point (ZMod q) (t + 1)))
    (hr : Module.finrank (ZMod q) (pointSpan S) = r) :
    (Finset.univ.filter fun a ↦ ∀ p ∈ S, Orthogonal p a).card ≤
      2 * q ^ (t - r) := by
  have hpred : t + 1 - r - 1 = t - r := by omega
  calc
    (Finset.univ.filter fun a ↦ ∀ p ∈ S, Orthogonal p a).card =
        ∑ i ∈ Finset.range (t + 1 - r), q ^ i := by
      simpa only [hr] using card_filter_orthogonal_to_span_eq_geomSum S
    _ ≤ 2 * q ^ (t - r) := by
      simpa only [hpred] using geomSum_le_two_mul_pow_pred q (t + 1 - r)
        (Fact.out : q.Prime).two_le


theorem card_filter_orthogonal_to_rankClosure_le_two_mul_pow
    (S : Finset (Point (ZMod q) (t + 1)))
    (hr : (rankClosure (F := ZMod q) (d := t + 1)).rank S = r) :
    (Finset.univ.filter fun a ↦ ∀ p ∈ S, Orthogonal p a).card ≤
      2 * q ^ (t - r) := by
  exact card_filter_orthogonal_to_span_le_two_mul_pow S hr


theorem card_filter_left_orthogonal_to_span_le_two_mul_pow
    (S : Finset (Point (ZMod q) (t + 1)))
    (hr : Module.finrank (ZMod q) (pointSpan S) = r) :
    (Finset.univ.filter fun a ↦ ∀ p ∈ S, Orthogonal a p).card ≤
      2 * q ^ (t - r) := by
  rw [card_filter_left_orthogonal_to_span_eq_geomSum, hr]
  have hpred : t + 1 - r - 1 = t - r := by omega
  simpa only [hpred] using geomSum_le_two_mul_pow_pred q (t + 1 - r)
    (Fact.out : q.Prime).two_le



theorem card_filter_left_orthogonal_to_span_eq_zero_of_full_rank
    (S : Finset (Point (ZMod q) (t + 1)))
    (hr : Module.finrank (ZMod q) (pointSpan S) = t + 1) :
    (Finset.univ.filter fun a ↦ ∀ p ∈ S, Orthogonal a p).card = 0 := by
  rw [card_filter_left_orthogonal_to_span_eq_geomSum, hr]
  simp


theorem card_filter_left_orthogonal_to_span_le_if
    (S : Finset (Point (ZMod q) (t + 1)))
    (hr : Module.finrank (ZMod q) (pointSpan S) = r) :
    (Finset.univ.filter fun a ↦ ∀ p ∈ S, Orthogonal a p).card ≤
      if r = t + 1 then 0 else 2 * q ^ (t - r) := by
  split_ifs with hfull
  · exact (card_filter_left_orthogonal_to_span_eq_zero_of_full_rank S
      (hr.trans hfull)).le
  · exact card_filter_left_orthogonal_to_span_le_two_mul_pow S hr





theorem canExtend_orthogonal_generators
    (a b : Point (ZMod q) d)
    (sigma : List (Point (ZMod q) d × Point (ZMod q) d))
    (h : Container.CanExtend Orthogonal (a, b) sigma) :
    ∀ g ∈ Container.generators Orthogonal sigma b, Orthogonal a g := by
  intro g hg
  rw [Container.generators] at hg
  rcases Finset.mem_image.mp hg with ⟨old, hold, rfl⟩
  have hold' := Finset.mem_filter.mp hold
  exact h.2 old (by simpa using hold'.1) hold'.2



theorem card_filter_canExtend_le_if
    (b : Point (ZMod q) (t + 1))
    (sigma : List
      (Point (ZMod q) (t + 1) × Point (ZMod q) (t + 1)))
    (hr : (rankClosure (F := ZMod q) (d := t + 1)).rank
      (Container.generators Orthogonal sigma b) = r) :
    (Finset.univ.filter fun a ↦
        Container.CanExtend Orthogonal (a, b) sigma).card ≤
      if r = t + 1 then 0 else 2 * q ^ (t - r) := by
  let S := Container.generators Orthogonal sigma b
  have hsubset :
      (Finset.univ.filter fun a : Point (ZMod q) (t + 1) ↦
          Container.CanExtend Orthogonal (a, b) sigma) ⊆
        Finset.univ.filter fun a ↦ ∀ p ∈ S, Orthogonal a p := by
    intro a ha
    have ha' := (Finset.mem_filter.mp ha).2
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, canExtend_orthogonal_generators a b sigma ha'⟩
  exact (Finset.card_le_card hsubset).trans
    (card_filter_left_orthogonal_to_span_le_if S hr)



theorem card_filter_cl_generators_le_if
    (b : Point (ZMod q) d)
    (sigma : List (Point (ZMod q) d × Point (ZMod q) d))
    (ell : ℕ)
    (hr : Container.prefixRank
      (rankClosure (F := ZMod q) (d := d)) Orthogonal sigma b = ell) :
    (Finset.univ.filter fun x ↦
        (rankClosure (F := ZMod q) (d := d)).Cl x
          (Container.generators Orthogonal sigma b)).card ≤
      if ell = 0 then 0 else 2 * q ^ (ell - 1) := by
  apply card_filter_rankClosure_cl_le_if
  exact hr


theorem card_filter_canExtend_le_if_of_prefixRank
    (b : Point (ZMod q) (t + 1))
    (sigma : List
      (Point (ZMod q) (t + 1) × Point (ZMod q) (t + 1)))
    (hr : Container.prefixRank
      (rankClosure (F := ZMod q) (d := t + 1)) Orthogonal sigma b = r) :
    (Finset.univ.filter fun a ↦
        Container.CanExtend Orthogonal (a, b) sigma).card ≤
      if r = t + 1 then 0 else 2 * q ^ (t - r) := by
  apply card_filter_canExtend_le_if
  exact hr

end

end Erdos920.SpanCounts











open scoped BigOperators LinearAlgebra.Projectivization

namespace Erdos920.PopularChildren

noncomputable section

open Erdos920.Projective
open Erdos920.ProjectiveContainer
open Erdos920.Container
open Erdos920.MarkedChildren
open Erdos920.Pivot

noncomputable local instance classicalDecidableProp (p : Prop) : Decidable p := Classical.propDecidable p
noncomputable local instance classicalDecidableEq (α : Type*) : DecidableEq α := Classical.decEq α


section ClearedDoubleCount

variable {P : Type*} [DecidableEq P]




theorem popularQ_card_le_of_fibre
    (points : Finset P) (C : RankClosure P) (R : P → P → Prop)
    [DecidableRel R] (q : ℕ) (sigma : List (P × P)) (l cap : ℕ)
    (hz : 0 < (Z points C R sigma l).card)
    (hfibre : ∀ y ∈ Z points C R sigma l,
      (points.filter fun b ↦ C.Cl b (generators R sigma y)).card ≤ cap) :
    (points.filter fun b ↦ PopularQ points C R q sigma l b).card ≤
      16 * q * cap := by
  classical
  let Z0 := Z points C R sigma l
  let pop := points.filter fun b ↦ PopularQ points C R q sigma l b
  have hleft : pop.card * Z0.card ≤
      16 * q * ∑ b ∈ pop,
        (Z0.filter fun y ↦ C.Cl b (generators R sigma y)).card := by
    rw [Finset.card_eq_sum_ones, Finset.sum_mul]
    calc
      ∑ _b ∈ pop, 1 * Z0.card = ∑ _b ∈ pop, Z0.card := by simp
      _ ≤ ∑ b ∈ pop,
          16 * q * (Z0.filter fun y ↦ C.Cl b (generators R sigma y)).card := by
        apply Finset.sum_le_sum
        intro b hb
        exact (Finset.mem_filter.mp hb).2
      _ = 16 * q * ∑ b ∈ pop,
          (Z0.filter fun y ↦ C.Cl b (generators R sigma y)).card := by
        rw [Finset.mul_sum]
  have hsub :
      ∑ b ∈ pop, (Z0.filter fun y ↦ C.Cl b (generators R sigma y)).card ≤
        ∑ b ∈ points,
          (Z0.filter fun y ↦ C.Cl b (generators R sigma y)).card := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro b hb
      exact (Finset.mem_filter.mp hb).1
    · intro i hi _
      exact Nat.zero_le _
  have hswap :
      ∑ b ∈ points,
          (Z0.filter fun y ↦ C.Cl b (generators R sigma y)).card =
        ∑ y ∈ Z0,
          (points.filter fun b ↦ C.Cl b (generators R sigma y)).card := by
    exact sum_card_filter_eq_sum_card_filter points Z0
      (fun b y ↦ C.Cl b (generators R sigma y))
  have hright :
      ∑ y ∈ Z0,
          (points.filter fun b ↦ C.Cl b (generators R sigma y)).card ≤
        Z0.card * cap := by
    rw [Finset.card_eq_sum_ones, Finset.sum_mul]
    exact Finset.sum_le_sum fun y hy ↦ by
      simpa [Z0] using hfibre y hy
  have hmul : pop.card * Z0.card ≤ (16 * q * cap) * Z0.card := by
    calc
      pop.card * Z0.card ≤
          16 * q * ∑ b ∈ pop,
            (Z0.filter fun y ↦ C.Cl b (generators R sigma y)).card := hleft
      _ ≤ 16 * q * ∑ b ∈ points,
            (Z0.filter fun y ↦ C.Cl b (generators R sigma y)).card :=
        Nat.mul_le_mul_left (16 * q) hsub
      _ = 16 * q * ∑ y ∈ Z0,
            (points.filter fun b ↦ C.Cl b (generators R sigma y)).card := by
        rw [hswap]
      _ ≤ 16 * q * (Z0.card * cap) := Nat.mul_le_mul_left (16 * q) hright
      _ = (16 * q * cap) * Z0.card := by ring
  exact Nat.le_of_mul_le_mul_right hmul hz

end ClearedDoubleCount

section ProjectiveChildren

variable (q t : ℕ) [Fact q.Prime]

abbrev P := Projective.Point (ZMod q) (t + 1)

local instance pointFintype : Fintype (P q t) := Fintype.ofFinite _
local instance orthogonalDecidable :
    DecidableRel (@Orthogonal (ZMod q) _ (t + 1)) := Classical.decRel _



def childRank (sigma : List (P q t × P q t)) (p : P q t × P q t) : ℕ :=
  prefixRank (projectiveRankClosure q t) Orthogonal sigma p.2


def pivotForRank (sigma : List (P q t × P q t)) (j : ℕ) : ℕ :=
  pivotLevel (Finset.univ : Finset (P q t))
    (projectiveRankClosure q t) Orthogonal sigma j


def popularSecondsAtRank (sigma : List (P q t × P q t)) (j : ℕ) :
    Finset (P q t) :=
  Finset.univ.filter fun b ↦
    prefixRank (projectiveRankClosure q t) Orthogonal sigma b = j ∧
      PopularQ (Finset.univ : Finset (P q t)) (projectiveRankClosure q t)
        Orthogonal q sigma (pivotForRank q t sigma j) b



def popularChildrenAtRank (sigma : List (P q t × P q t)) (j : ℕ) :
    Finset (P q t × P q t) :=
  (TupleBound.consistentChildren (incidentPairs q t) Orthogonal sigma).filter fun p ↦
    childRank q t sigma p = j ∧
      PopularQ (Finset.univ : Finset (P q t)) (projectiveRankClosure q t)
        Orthogonal q sigma (pivotForRank q t sigma j) p.2




def compatibleFirsts (sigma : List (P q t × P q t)) (b : P q t) :
    Finset (P q t) :=
  Finset.univ.filter fun a ↦
    ∀ y ∈ generators Orthogonal sigma b, Orthogonal y a



theorem orthogonal_generators_of_canExtend
    (sigma : List (P q t × P q t)) (a b : P q t)
    (h : CanExtend Orthogonal (a, b) sigma) :
    ∀ y ∈ generators Orthogonal sigma b, Orthogonal y a := by
  intro y hy
  rcases Finset.mem_image.mp hy with ⟨old, hold, rfl⟩
  have hold' := Finset.mem_filter.mp hold
  have hoa : Orthogonal a old.2 :=
    h.2 old (List.mem_toFinset.mp hold'.1) hold'.2
  exact (orthogonal_comm a old.2).mp hoa



theorem compatibleFirsts_card_le
    (sigma : List (P q t × P q t)) (b : P q t) (j : ℕ)
    (hrank : prefixRank (projectiveRankClosure q t) Orthogonal sigma b = j) :
    (compatibleFirsts q t sigma b).card ≤ 2 * q ^ (t - j) := by
  have hrank' :
      (rankClosure (F := ZMod q) (d := t + 1)).rank
          (generators Orthogonal sigma b) = j := by
    simpa [prefixRank, projectiveRankClosure] using hrank
  simpa [compatibleFirsts] using
    (Erdos920.SpanCounts.card_filter_orthogonal_to_rankClosure_le_two_mul_pow
      (S := generators Orthogonal sigma b) hrank')




theorem childRank_le_t_of_mem_children
    (sigma : List (P q t × P q t)) (p : P q t × P q t)
    (hp : p ∈ TupleBound.consistentChildren (incidentPairs q t)
      Orthogonal sigma) :
    childRank q t sigma p ≤ t := by
  have hmem := (TupleBound.mem_consistentChildren_iff
    (incidentPairs q t) Orthogonal p sigma).mp hp
  have horth : ∀ y ∈ generators Orthogonal sigma p.2,
      Orthogonal y p.1 :=
    orthogonal_generators_of_canExtend q t sigma p.1 p.2 hmem.2
  have hpfirst : p.1 ∈ compatibleFirsts q t sigma p.2 := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, horth⟩
  let j := childRank q t sigma p
  have hjdim : j ≤ t + 1 := by
    exact (projectiveRankClosure_rank_le_dim
      (q := q) (t := t) (generators Orthogonal sigma p.2))
  by_contra hj
  have hjeq : j = t + 1 := by omega
  have hrank : Module.finrank (ZMod q)
      (pointSpan (generators Orthogonal sigma p.2)) = t + 1 := by
    simpa [j, childRank, prefixRank, projectiveRankClosure] using hjeq
  have hzero : (compatibleFirsts q t sigma p.2).card = 0 := by
    have hexact :=
      Erdos920.SpanCounts.card_filter_orthogonal_to_span_eq_geomSum
        (S := generators Orthogonal sigma p.2)
    rw [hrank] at hexact
    simpa [compatibleFirsts] using hexact
  have hpos : 0 < (compatibleFirsts q t sigma p.2).card :=
    Finset.card_pos.mpr ⟨p.1, hpfirst⟩
  omega



theorem pivot_nonempty_of_popularChildrenAtRank_nonempty
    (sigma : List (P q t × P q t)) (j : ℕ)
    (hne : (popularChildrenAtRank q t sigma j).Nonempty) :
    (Z (Finset.univ : Finset (P q t)) (projectiveRankClosure q t)
      Orthogonal sigma (pivotForRank q t sigma j)).Nonempty := by
  obtain ⟨p, hp⟩ := hne
  have hp' := Finset.mem_filter.mp hp
  have hrank : prefixRank (projectiveRankClosure q t) Orthogonal sigma p.2 = j :=
    hp'.2.1
  have hbZ : p.2 ∈ Z (Finset.univ : Finset (P q t))
      (projectiveRankClosure q t) Orthogonal sigma j := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hrank⟩
  have hone : 1 ≤ (Z (Finset.univ : Finset (P q t))
      (projectiveRankClosure q t) Orthogonal sigma j).card :=
    Finset.one_le_card.mpr ⟨p.2, hbZ⟩
  have hpivot := Z_card_le_pivot
    (Finset.univ : Finset (P q t)) (projectiveRankClosure q t)
      Orthogonal sigma (r := j) (le_refl j)
  exact Finset.card_pos.mp (lt_of_lt_of_le (by omega) (hone.trans hpivot))



theorem popularSecondsAtRank_card_le_of_pivot_pos
    (sigma : List (P q t × P q t)) (j : ℕ)
    (hz : 0 < (Z (Finset.univ : Finset (P q t))
      (projectiveRankClosure q t) Orthogonal sigma
        (pivotForRank q t sigma j)).card)
    (hl : 0 < pivotForRank q t sigma j) :
    (popularSecondsAtRank q t sigma j).card ≤
      32 * q ^ (pivotForRank q t sigma j) := by
  let l := pivotForRank q t sigma j
  have hfibre : ∀ y ∈ Z (Finset.univ : Finset (P q t))
      (projectiveRankClosure q t) Orthogonal sigma l,
      ((Finset.univ : Finset (P q t)).filter fun b ↦
        (projectiveRankClosure q t).Cl b
          (generators Orthogonal sigma y)).card ≤ 2 * q ^ (l - 1) := by
    intro y hy
    have hrank : (rankClosure (F := ZMod q) (d := t + 1)).rank
        (generators Orthogonal sigma y) = l := by
      simpa [prefixRank, projectiveRankClosure] using (Finset.mem_filter.mp hy).2
    exact Erdos920.SpanCounts.card_filter_rankClosure_cl_le_two_mul_pow_pred
      (S := generators Orthogonal sigma y) hrank
  have hall := popularQ_card_le_of_fibre
    (Finset.univ : Finset (P q t)) (projectiveRankClosure q t)
      Orthogonal q sigma l (2 * q ^ (l - 1)) hz hfibre
  have hsub : popularSecondsAtRank q t sigma j ⊆
      (Finset.univ : Finset (P q t)).filter fun b ↦
        PopularQ (Finset.univ : Finset (P q t)) (projectiveRankClosure q t)
          Orthogonal q sigma l b := by
    intro b hb
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hb).2.2⟩
  calc
    (popularSecondsAtRank q t sigma j).card ≤
        ((Finset.univ : Finset (P q t)).filter fun b ↦
          PopularQ (Finset.univ : Finset (P q t)) (projectiveRankClosure q t)
            Orthogonal q sigma l b).card := Finset.card_le_card hsub
    _ ≤ 16 * q * (2 * q ^ (l - 1)) := hall
    _ = 32 * q ^ l := by
      have hpow : q ^ (l - 1) * q = q ^ l := by
        rw [← pow_succ]
        congr 1
        omega
      calc
        16 * q * (2 * q ^ (l - 1)) = 32 * (q ^ (l - 1) * q) := by ring
        _ = 32 * q ^ l := by rw [hpow]



theorem popularSecondsAtRank_card_eq_zero_of_pivot_zero
    (sigma : List (P q t × P q t)) (j : ℕ)
    (hz : 0 < (Z (Finset.univ : Finset (P q t))
      (projectiveRankClosure q t) Orthogonal sigma
        (pivotForRank q t sigma j)).card)
    (hl : pivotForRank q t sigma j = 0) :
    (popularSecondsAtRank q t sigma j).card = 0 := by
  let l := pivotForRank q t sigma j
  have hfibre : ∀ y ∈ Z (Finset.univ : Finset (P q t))
      (projectiveRankClosure q t) Orthogonal sigma l,
      ((Finset.univ : Finset (P q t)).filter fun b ↦
        (projectiveRankClosure q t).Cl b
          (generators Orthogonal sigma y)).card ≤ 0 := by
    intro y hy
    have hy' : (projectiveRankClosure q t).rank
        (generators Orthogonal sigma y) = l :=
      (Finset.mem_filter.mp hy).2
    have hl0 : l = 0 := by simpa [l] using hl
    have hrank0 : (projectiveRankClosure q t).rank
        (generators Orthogonal sigma y) = 0 := by
      rw [← hl0]
      exact hy'
    have hrank : (rankClosure (F := ZMod q) (d := t + 1)).rank
        (generators Orthogonal sigma y) = 0 := by
      change (projectiveRankClosure q t).rank
        (generators Orthogonal sigma y) = 0
      exact hrank0
    exact (Erdos920.SpanCounts.card_filter_rankClosure_cl_eq_zero_of_rank_eq_zero
      (S := generators Orthogonal sigma y) hrank).le
  have hall := popularQ_card_le_of_fibre
    (Finset.univ : Finset (P q t)) (projectiveRankClosure q t)
      Orthogonal q sigma l 0 hz hfibre
  have hsub : popularSecondsAtRank q t sigma j ⊆
      (Finset.univ : Finset (P q t)).filter fun b ↦
        PopularQ (Finset.univ : Finset (P q t)) (projectiveRankClosure q t)
          Orthogonal q sigma l b := by
    intro b hb
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hb).2.2⟩
  have : (popularSecondsAtRank q t sigma j).card ≤ 0 :=
    (Finset.card_le_card hsub).trans (by simpa using hall)
  omega


theorem popularSecondsAtRank_card_le
    (sigma : List (P q t × P q t)) (j : ℕ)
    (hz : 0 < (Z (Finset.univ : Finset (P q t))
      (projectiveRankClosure q t) Orthogonal sigma
        (pivotForRank q t sigma j)).card) :
    (popularSecondsAtRank q t sigma j).card ≤
      32 * q ^ (pivotForRank q t sigma j) := by
  by_cases hl : pivotForRank q t sigma j = 0
  · rw [popularSecondsAtRank_card_eq_zero_of_pivot_zero q t sigma j hz hl]
    exact Nat.zero_le _
  · exact popularSecondsAtRank_card_le_of_pivot_pos q t sigma j hz
      (Nat.pos_of_ne_zero hl)



theorem popularChildrenAtRank_card_le_mul
    (sigma : List (P q t × P q t)) (j : ℕ) :
    (popularChildrenAtRank q t sigma j).card ≤
      (popularSecondsAtRank q t sigma j).card * (2 * q ^ (t - j)) := by
  let B := popularSecondsAtRank q t sigma j
  let A := fun b : P q t ↦ compatibleFirsts q t sigma b
  have hsub : popularChildrenAtRank q t sigma j ⊆
      B.biUnion fun b ↦ (A b).image fun a ↦ (a, b) := by
    intro p hp
    have hp' := Finset.mem_filter.mp hp
    have hchild := (TupleBound.mem_consistentChildren_iff
      (incidentPairs q t) Orthogonal p sigma).mp hp'.1
    have hb : p.2 ∈ B := by
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp'.2⟩
    have ha : p.1 ∈ A p.2 := by
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        orthogonal_generators_of_canExtend q t sigma p.1 p.2 hchild.2⟩
    exact Finset.mem_biUnion.mpr ⟨p.2, hb,
      Finset.mem_image.mpr ⟨p.1, ha, rfl⟩⟩
  calc
    (popularChildrenAtRank q t sigma j).card ≤
        (B.biUnion fun b ↦ (A b).image fun a ↦ (a, b)).card :=
      Finset.card_le_card hsub
    _ ≤ ∑ b ∈ B, ((A b).image fun a ↦ (a, b)).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _b ∈ B, 2 * q ^ (t - j) := by
      apply Finset.sum_le_sum
      intro b hb
      exact Finset.card_image_le.trans
        (compatibleFirsts_card_le q t sigma b j (Finset.mem_filter.mp hb).2.1)
    _ = B.card * (2 * q ^ (t - j)) := by simp



theorem popularChildrenAtRank_card_le
    (sigma : List (P q t × P q t)) (j : ℕ) (hj : j ≤ t) :
    (popularChildrenAtRank q t sigma j).card ≤ 64 * q ^ t := by
  by_cases hne : (popularChildrenAtRank q t sigma j).Nonempty
  · have hz := Finset.card_pos.mpr
      (pivot_nonempty_of_popularChildrenAtRank_nonempty q t sigma j hne)
    have hseconds := popularSecondsAtRank_card_le q t sigma j hz
    have hpivot : pivotForRank q t sigma j ≤ j := by
      exact pivotLevel_le
        (Finset.univ : Finset (P q t)) (projectiveRankClosure q t)
          Orthogonal sigma j
    calc
      (popularChildrenAtRank q t sigma j).card ≤
          (popularSecondsAtRank q t sigma j).card * (2 * q ^ (t - j)) :=
        popularChildrenAtRank_card_le_mul q t sigma j
      _ ≤ (32 * q ^ (pivotForRank q t sigma j)) * (2 * q ^ (t - j)) :=
        Nat.mul_le_mul_right _ hseconds
      _ = 64 * q ^ (pivotForRank q t sigma j + (t - j)) := by
        rw [pow_add]
        ring
      _ ≤ 64 * q ^ t := by
        exact Nat.mul_le_mul_left 64
          (Nat.pow_le_pow_right (Fact.out : q.Prime).pos (by omega))
  · simp only [Finset.not_nonempty_iff_eq_empty] at hne
    simp [hne]



def popularChildren (sigma : List (P q t × P q t)) :
    Finset (P q t × P q t) :=
  (TupleBound.consistentChildren (incidentPairs q t) Orthogonal sigma).filter fun p ↦
    PopularQ (Finset.univ : Finset (P q t)) (projectiveRankClosure q t)
      Orthogonal q sigma
        (pivotForRank q t sigma (childRank q t sigma p)) p.2




theorem popularChildren_eq_markedPopular
    (sigma : List (P q t × P q t)) :
    popularChildren q t sigma =
      (TupleBound.consistentChildren (incidentPairs q t) Orthogonal sigma).filter
        fun p ↦ PopularQ (Finset.univ : Finset (P q t))
          (projectiveRankClosure q t) Orthogonal q sigma
            (chosenPivot (Finset.univ : Finset (P q t))
              (projectiveRankClosure q t) Orthogonal sigma p) p.2 := by
  rfl



theorem popularChildren_card_le (sigma : List (P q t × P q t)) :
    (popularChildren q t sigma).card ≤ 64 * (t + 1) * q ^ t := by
  let S := popularChildren q t sigma
  let Sj := fun j : ℕ ↦ popularChildrenAtRank q t sigma j
  have hsub : S ⊆ (Finset.range (t + 1)).biUnion Sj := by
    intro p hp
    have hp' := Finset.mem_filter.mp hp
    have hj : childRank q t sigma p ≤ t :=
      childRank_le_t_of_mem_children q t sigma p hp'.1
    apply Finset.mem_biUnion.mpr
    refine ⟨childRank q t sigma p, Finset.mem_range.mpr (by omega), ?_⟩
    exact Finset.mem_filter.mpr ⟨hp'.1, rfl, hp'.2⟩
  calc
    (popularChildren q t sigma).card = S.card := rfl
    _ ≤ ((Finset.range (t + 1)).biUnion Sj).card := Finset.card_le_card hsub
    _ ≤ ∑ j ∈ Finset.range (t + 1), (Sj j).card := Finset.card_biUnion_le
    _ ≤ ∑ _j ∈ Finset.range (t + 1), 64 * q ^ t := by
      exact Finset.sum_le_sum fun j hj ↦
        popularChildrenAtRank_card_le q t sigma j
          (Nat.le_of_lt_succ (Finset.mem_range.mp hj))
    _ = 64 * (t + 1) * q ^ t := by
      simp
      ring

end ProjectiveChildren

end

end Erdos920.PopularChildren











open scoped LinearAlgebra.Projectivization

namespace Erdos920.MarkedChildrenBound

noncomputable section

open Erdos920.Container
open Erdos920.MarkedChildren
open Erdos920.PoorChildren
open Erdos920.PopularChildren
open Erdos920.Projective
open Erdos920.ProjectiveContainer

noncomputable local instance classicalDecidableProp (p : Prop) : Decidable p := Classical.propDecidable p
noncomputable local instance classicalDecidableEq (α : Type*) : DecidableEq α := Classical.decEq α


variable {q t : ℕ} [Fact q.Prime]

abbrev PT (q t : ℕ) [Fact q.Prime] := MarkedChildren.PointT q t

local instance pointFintype : Fintype (PT q t) := Fintype.ofFinite _
local instance orthogonalDecidable :
    DecidableRel (@Orthogonal (ZMod q) _ (t + 1)) := Classical.decRel _



def poorChildren (q t : ℕ) [Fact q.Prime]
    (sigma : List (PT q t × PT q t)) :
    Finset (PT q t × PT q t) :=
  (projectiveChildren q t sigma).filter fun p =>
    PoorQ (Finset.univ : Finset (PT q t)) (projectiveRankClosure q t)
      Orthogonal q sigma
        (chosenPivot (Finset.univ : Finset (PT q t))
          (projectiveRankClosure q t) Orthogonal sigma p) p.1


theorem poorChildren_card_le (ht : 2 ≤ t)
    (sigma : List (PT q t × PT q t)) :
    (poorChildren q t sigma).card ≤ 2048 * (t + 1) * q ^ t := by
  let S := poorChildren q t sigma
  let Sj := fun j : ℕ => PoorChildren.poorChildrenAtRank q t sigma j
  have hsub : S ⊆ (Finset.range (t + 1)).biUnion Sj := by
    intro p hp
    have hp' := Finset.mem_filter.mp hp
    have hj : PopularChildren.childRank q t sigma p ≤ t :=
      PopularChildren.childRank_le_t_of_mem_children q t sigma p hp'.1
    apply Finset.mem_biUnion.mpr
    refine ⟨PopularChildren.childRank q t sigma p,
      Finset.mem_range.mpr (by omega), ?_⟩
    apply (PoorChildren.mem_poorChildrenAtRank_iff q t sigma
      (PopularChildren.childRank q t sigma p) p).mpr
    refine ⟨?_, rfl, ?_⟩
    · simpa [projectiveChildren_eq_extensionChildren] using hp'.1
    · simpa [PopularChildren.childRank, PopularChildren.pivotForRank,
        chosenPivot] using hp'.2
  calc
    (poorChildren q t sigma).card = S.card := rfl
    _ ≤ ((Finset.range (t + 1)).biUnion Sj).card := Finset.card_le_card hsub
    _ ≤ ∑ j ∈ Finset.range (t + 1), (Sj j).card := Finset.card_biUnion_le
    _ ≤ ∑ _j ∈ Finset.range (t + 1), 2048 * q ^ t := by
      exact Finset.sum_le_sum fun j _ =>
        PoorChildren.card_poorChildrenAtRank_le q t ht sigma j
    _ = 2048 * (t + 1) * q ^ t := by simp; ring


def markedChildren (q t : ℕ) [Fact q.Prime]
    (sigma : List (PT q t × PT q t)) :
    Finset (PT q t × PT q t) :=
  (projectiveChildren q t sigma).filter fun p =>
    projectiveMarked q t sigma p = true


theorem markedChildren_card_le (ht : 2 ≤ t)
    (sigma : List (PT q t × PT q t)) :
    (markedChildren q t sigma).card ≤ 2112 * (t + 1) * q ^ t := by
  have hsub : markedChildren q t sigma ⊆
      poorChildren q t sigma ∪ PopularChildren.popularChildren q t sigma := by
    intro p hp
    have hp' := Finset.mem_filter.mp hp
    have hor :
        PoorQ (Finset.univ : Finset (PT q t)) (projectiveRankClosure q t)
            Orthogonal q sigma
              (chosenPivot (Finset.univ : Finset (PT q t))
                (projectiveRankClosure q t) Orthogonal sigma p) p.1 ∨
        PopularQ (Finset.univ : Finset (PT q t)) (projectiveRankClosure q t)
            Orthogonal q sigma
              (chosenPivot (Finset.univ : Finset (PT q t))
                (projectiveRankClosure q t) Orthogonal sigma p) p.2 := by
      simpa [projectiveMarked, marked] using hp'.2
    rcases hor with hpoor | hpopular
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hp'.1, hpoor⟩)
    · apply Finset.mem_union_right
      rw [PopularChildren.popularChildren_eq_markedPopular]
      exact Finset.mem_filter.mpr ⟨hp'.1, hpopular⟩
  calc
    (markedChildren q t sigma).card ≤
        (poorChildren q t sigma ∪ PopularChildren.popularChildren q t sigma).card :=
      Finset.card_le_card hsub
    _ ≤ (poorChildren q t sigma).card +
        (PopularChildren.popularChildren q t sigma).card :=
      Finset.card_union_le _ _
    _ ≤ 2048 * (t + 1) * q ^ t + 64 * (t + 1) * q ^ t :=
      Nat.add_le_add (poorChildren_card_le ht sigma)
        (PopularChildren.popularChildren_card_le q t sigma)
    _ = 2112 * (t + 1) * q ^ t := by ring

end

end Erdos920.MarkedChildrenBound












namespace Erdos920.ContainerNumeric

open Finset



def stoppingBlocks (t q : ℕ) : ℕ :=
  t * (Nat.log 2 q + 1) + 2



def contractionBudget (K t q : ℕ) : ℕ :=
  2 * K * stoppingBlocks t q



def projectiveBudgetConstant (t : ℕ) : ℕ :=
  320 * t * t * (t + 1)



theorem two_mul_pow_succ_le_succ_pow (a : ℕ) :
    2 * a ^ (a + 1) ≤ (a + 1) ^ (a + 1) := by
  rw [show a + 1 = a + 1 by rfl, show (a + 1 : ℕ) = a + 1 by rfl,
    add_pow]
  have hs : ({a, a + 1} : Finset ℕ) ⊆ Finset.range (a + 1 + 1) := by
    intro i hi
    simp only [mem_insert, mem_singleton] at hi
    rcases hi with rfl | rfl <;> simp
  calc
    2 * a ^ (a + 1) ≤
        ∑ m ∈ ({a, a + 1} : Finset ℕ),
          a ^ m * 1 ^ (a + 1 - m) * (a + 1).choose m := by
      simp only [one_pow, mul_one, mem_singleton, Nat.left_eq_add, one_ne_zero,
        not_false_eq_true, sum_insert, Nat.choose_succ_self_right, sum_singleton,
        Nat.choose_self]
      rw [Nat.mul_succ]
      rw [pow_succ]
      omega
    _ ≤ ∑ m ∈ Finset.range (a + 1 + 1),
          a ^ m * 1 ^ (a + 1 - m) * (a + 1).choose m := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hs (fun _ _ _ ↦ Nat.zero_le _)


theorem pow_two_mul_pow_pred_le_pow {B r : ℕ} (hB : 1 ≤ B) :
    2 ^ r * (B - 1) ^ (B * r) ≤ B ^ (B * r) := by
  have hblock : 2 * (B - 1) ^ B ≤ B ^ B := by
    obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le hB
    simpa [Nat.add_sub_cancel_left, Nat.add_comm] using two_mul_pow_succ_le_succ_pow a
  calc
    2 ^ r * (B - 1) ^ (B * r) =
        (2 * (B - 1) ^ B) ^ r := by rw [mul_pow, pow_mul]
    _ ≤ (B ^ B) ^ r := Nat.pow_le_pow_left hblock r
    _ = B ^ (B * r) := by rw [pow_mul]



theorem initial_lt_two_pow_stoppingBlocks {t q N : ℕ}
    (ht : 1 ≤ t) (_hq : 1 ≤ q) (hN : N ≤ 2 * q ^ t) :
    N + 1 < 2 ^ stoppingBlocks t q := by
  have hqpow : q < 2 ^ (Nat.log 2 q + 1) := by
    simpa only [Nat.succ_eq_add_one] using Nat.lt_pow_succ_log_self (by omega : 1 < 2) q
  have ht0 : t ≠ 0 := by omega
  have hpow : q ^ t < (2 ^ (Nat.log 2 q + 1)) ^ t :=
    Nat.pow_lt_pow_left hqpow ht0
  have hNlt : N < 2 ^ (t * (Nat.log 2 q + 1) + 1) := by
    calc
      N ≤ 2 * q ^ t := hN
      _ < 2 * (2 ^ (Nat.log 2 q + 1)) ^ t :=
        Nat.mul_lt_mul_of_pos_left hpow (by omega)
      _ = 2 ^ (t * (Nat.log 2 q + 1) + 1) := by
        rw [← pow_mul]
        simp [pow_succ', Nat.mul_comm]
  have hsucc : N + 1 ≤ 2 ^ (t * (Nat.log 2 q + 1) + 1) := hNlt
  calc
    N + 1 ≤ 2 ^ (t * (Nat.log 2 q + 1) + 1) := hsucc
    _ < 2 ^ stoppingBlocks t q := by
      unfold stoppingBlocks
      exact Nat.pow_lt_pow_right (by omega) (by omega)



theorem contraction_stopping {K t q N : ℕ}
    (hK : 1 ≤ K) (ht : 1 ≤ t) (hq : 1 ≤ q) (hN : N ≤ 2 * q ^ t) :
    ∀ c : ℕ, contractionBudget K t q < c →
      (2 * K - 1) ^ c * (N + 1) < (2 * K) ^ c := by
  intro c hc
  let B := 2 * K
  let r := stoppingBlocks t q
  have hB : 1 ≤ B := by simp [B]; omega
  have hinit : N + 1 < 2 ^ r := by
    simpa [r] using initial_lt_two_pow_stoppingBlocks ht hq hN
  have hbr : B * r ≤ c := by
    simpa [contractionBudget, B, r] using hc.le
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hbr
  have hapos : 0 < (B - 1) ^ (B * r) := pow_pos (by omega) _
  have htailpos : 0 < (B - 1) ^ d := pow_pos (by omega) _
  have htail : (B - 1) ^ d ≤ B ^ d :=
    Nat.pow_le_pow_left (Nat.sub_le B 1) d
  calc
    (2 * K - 1) ^ (B * r + d) * (N + 1) =
        ((B - 1) ^ (B * r) * (N + 1)) * (B - 1) ^ d := by
      simp only [B, pow_add]
      ac_rfl
    _ < ((B - 1) ^ (B * r) * 2 ^ r) * (B - 1) ^ d := by
      exact Nat.mul_lt_mul_of_pos_right
        (Nat.mul_lt_mul_of_pos_left hinit hapos) htailpos
    _ ≤ B ^ (B * r) * B ^ d := by
      have hblock := pow_two_mul_pow_pred_le_pow (B := B) (r := r) hB
      calc
        ((B - 1) ^ (B * r) * 2 ^ r) * (B - 1) ^ d =
            (2 ^ r * (B - 1) ^ (B * r)) * (B - 1) ^ d := by ac_rfl
        _ ≤ B ^ (B * r) * (B - 1) ^ d := Nat.mul_le_mul_right _ hblock
        _ ≤ B ^ (B * r) * B ^ d := Nat.mul_le_mul_left _ htail
    _ = (2 * K) ^ (B * r + d) := by
      simp only [B, ← pow_add]



theorem projective_contraction_stopping {t q N : ℕ}
    (ht : 1 ≤ t) (hq : 1 ≤ q) (hN : N ≤ 2 * q ^ t) :
    ∀ c : ℕ, contractionBudget (32 * t * q) t q < c →
      (2 * (32 * t * q) - 1) ^ c * (N + 1) <
        (2 * (32 * t * q)) ^ c := by
  have hK : 1 ≤ 32 * t * q := by
    have : 0 < 32 * t * q := Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega)
    omega
  exact contraction_stopping
    (K := 32 * t * q) (t := t) (q := q) (N := N)
    hK ht hq hN

end Erdos920.ContainerNumeric


















namespace Erdos920.NumericAbsorption

noncomputable section


def unmarkedBudget (A q : ℕ) : ℕ :=
  A * q * Nat.ceil (Real.log (q : ℝ))



def absorptionConstant (t A : ℕ) : ℕ :=
  8 * t * A


def absorptionThreshold : ℕ := 4

theorem absorptionConstant_pos {t A : ℕ} (ht : 1 ≤ t) (hA : 1 ≤ A) :
    0 < absorptionConstant t A := by
  exact Nat.mul_pos (Nat.mul_pos (by norm_num) (Nat.zero_lt_of_lt ht))
    (Nat.zero_lt_of_lt hA)

private theorem half_le_log_of_four_le {q : ℕ} (hq : 4 ≤ q) :
    (1 / 2 : ℝ) ≤ Real.log (q : ℝ) := by
  have hfour : (4 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hlog_mono : Real.log (4 : ℝ) ≤ Real.log (q : ℝ) :=
    Real.log_le_log (by norm_num) hfour
  have hhalf_two : (1 / 2 : ℝ) ≤ Real.log 2 :=
    Real.log_two_gt_d9.le.trans' (by norm_num)
  have hlog_four : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  rw [hlog_four] at hlog_mono
  linarith

private theorem one_le_log_of_four_le {q : ℕ} (hq : 4 ≤ q) :
    (1 : ℝ) ≤ Real.log (q : ℝ) := by
  have hfour : (4 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hlog_mono : Real.log (4 : ℝ) ≤ Real.log (q : ℝ) :=
    Real.log_le_log (by norm_num) hfour
  have hhalf_two : (1 / 2 : ℝ) ≤ Real.log 2 :=
    Real.log_two_gt_d9.le.trans' (by norm_num)
  have hlog_four : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  rw [hlog_four] at hlog_mono
  linarith


theorem unmarkedBudget_cast_le {A q : ℕ} (hq : 4 ≤ q) :
    (unmarkedBudget A q : ℝ) ≤
      2 * (A : ℝ) * (q : ℝ) * Real.log (q : ℝ) := by
  have hceil : (Nat.ceil (Real.log (q : ℝ)) : ℝ) ≤
      2 * Real.log (q : ℝ) := by
    exact Nat.ceil_le_two_mul (by
      simpa only [one_div] using half_le_log_of_four_le hq)
  simp only [unmarkedBudget, Nat.cast_mul]
  have hA0 : (0 : ℝ) ≤ A := by positivity
  have hq0 : (0 : ℝ) ≤ q := by positivity
  calc
    (A : ℝ) * q * Nat.ceil (Real.log (q : ℝ)) ≤
        (A : ℝ) * q * (2 * Real.log (q : ℝ)) := by gcongr
    _ = 2 * (A : ℝ) * q * Real.log (q : ℝ) := by ring



theorem unmarkedBudget_le {t A q m : ℕ}
    (ht : 1 ≤ t) (hA : 1 ≤ A) (hq : 4 ≤ q)
    (hm : (absorptionConstant t A : ℝ) * (q : ℝ) *
        Real.log (q : ℝ) ^ 2 ≤ (m : ℝ)) :
    unmarkedBudget A q ≤ m := by
  have hA0 : (0 : ℝ) ≤ A := by positivity
  have hq0 : (0 : ℝ) ≤ q := by positivity
  have hlog1 := one_le_log_of_four_le hq
  have hlog0 : 0 ≤ Real.log (q : ℝ) := zero_le_one.trans hlog1
  have hceil := unmarkedBudget_cast_le (A := A) hq
  have hconst : (2 : ℝ) * A ≤ absorptionConstant t A := by
    simp only [absorptionConstant, Nat.cast_mul, Nat.cast_ofNat]
    nlinarith [show (1 : ℝ) ≤ t by exact_mod_cast ht]
  have hsquare : Real.log (q : ℝ) ≤ Real.log (q : ℝ) ^ 2 := by
    nlinarith
  have hreal : (unmarkedBudget A q : ℝ) ≤ (m : ℝ) := by
    calc
      (unmarkedBudget A q : ℝ) ≤ 2 * A * q * Real.log (q : ℝ) := hceil
      _ ≤ (absorptionConstant t A : ℝ) * q * Real.log (q : ℝ) ^ 2 := by
        gcongr
      _ ≤ (m : ℝ) := hm
  exact_mod_cast hreal



theorem q_pow_unmarked_loss_le {t A q m : ℕ}
    (ht : 1 ≤ t) (hA : 1 ≤ A) (hq : 4 ≤ q)
    (hm : (absorptionConstant t A : ℝ) * (q : ℝ) *
        Real.log (q : ℝ) ^ 2 ≤ (m : ℝ)) :
    (q : ℝ) ^ (2 * t * unmarkedBudget A q) ≤ (2 : ℝ) ^ m := by
  have hA0 : (0 : ℝ) ≤ A := by
    exact_mod_cast (Nat.zero_lt_of_lt hA).le
  have hqpos : (0 : ℝ) < q := by positivity
  have hlog0 : 0 ≤ Real.log (q : ℝ) :=
    (zero_le_one.trans (one_le_log_of_four_le hq))
  have hw := unmarkedBudget_cast_le (A := A) hq
  have hlog_two_half : (1 / 2 : ℝ) ≤ Real.log 2 :=
    Real.log_two_gt_d9.le.trans' (by norm_num)
  have hexponent :
      ((2 * t * unmarkedBudget A q : ℕ) : ℝ) * Real.log (q : ℝ) ≤
        (m : ℝ) * Real.log 2 := by
    have hleft :
        ((2 * t * unmarkedBudget A q : ℕ) : ℝ) * Real.log (q : ℝ) ≤
          4 * (t : ℝ) * A * q * Real.log (q : ℝ) ^ 2 := by
      simp only [Nat.cast_mul, Nat.cast_ofNat]
      calc
        (2 * (t : ℝ) * (unmarkedBudget A q : ℝ)) * Real.log (q : ℝ) ≤
            (2 * (t : ℝ) * (2 * A * q * Real.log (q : ℝ))) *
              Real.log (q : ℝ) := by gcongr
        _ = 4 * (t : ℝ) * A * q * Real.log (q : ℝ) ^ 2 := by ring
    have hbudget :
        4 * (t : ℝ) * A * q * Real.log (q : ℝ) ^ 2 ≤ (m : ℝ) / 2 := by
      have hm' := hm
      simp only [absorptionConstant, Nat.cast_mul, Nat.cast_ofNat] at hm'
      linarith
    have hm0 : (0 : ℝ) ≤ m := by positivity
    calc
      ((2 * t * unmarkedBudget A q : ℕ) : ℝ) * Real.log (q : ℝ) ≤
          4 * (t : ℝ) * A * q * Real.log (q : ℝ) ^ 2 := hleft
      _ ≤ (m : ℝ) / 2 := hbudget
      _ ≤ (m : ℝ) * Real.log 2 := by nlinarith
  rw [← Real.log_le_log_iff (pow_pos hqpos _) (by positivity),
    Real.log_pow, Real.log_pow]
  simpa [mul_comm] using hexponent






theorem markedTree_numeric_absorption {t A q m : ℕ}
    (ht : 1 ≤ t) (hA : 1 ≤ A) (hq : 4 ≤ q)
    (hm : (absorptionConstant t A : ℝ) * (q : ℝ) *
        Real.log (q : ℝ) ^ 2 ≤ (m : ℝ)) :
    (2 : ℝ) ^ m *
          (4 * (q : ℝ) ^ (2 * t - 1)) ^ unmarkedBudget A q *
          ((A : ℝ) * (q : ℝ) ^ t) ^ (m - unmarkedBudget A q) ≤
      ((absorptionConstant t A : ℝ) * (q : ℝ) ^ t) ^ m := by
  let w := unmarkedBudget A q
  have hw : w ≤ m := unmarkedBudget_le ht hA hq hm
  have hq0 : (0 : ℝ) ≤ q := by positivity
  have hdelta :
      (4 : ℝ) * (q : ℝ) ^ (2 * t - 1) ≤ (q : ℝ) ^ (2 * t) := by
    calc
      (4 : ℝ) * (q : ℝ) ^ (2 * t - 1) ≤
          (q : ℝ) * (q : ℝ) ^ (2 * t - 1) := by
        gcongr
        exact_mod_cast hq
      _ = (q : ℝ) ^ (2 * t) := by
        rw [← pow_succ']
        congr 1
        omega
  have hdelta_pow :
      ((4 : ℝ) * (q : ℝ) ^ (2 * t - 1)) ^ w ≤ (2 : ℝ) ^ m := by
    calc
      ((4 : ℝ) * (q : ℝ) ^ (2 * t - 1)) ^ w ≤
          ((q : ℝ) ^ (2 * t)) ^ w := by gcongr
      _ = (q : ℝ) ^ (2 * t * w) := by rw [← pow_mul]
      _ ≤ (2 : ℝ) ^ m := q_pow_unmarked_loss_le ht hA hq hm
  have hbase : (1 : ℝ) ≤ (A : ℝ) * (q : ℝ) ^ t := by
    have hAreal : (1 : ℝ) ≤ A := by exact_mod_cast hA
    have hqreal : (1 : ℝ) ≤ q := by exact_mod_cast (le_trans (by omega : 1 ≤ 4) hq)
    nlinarith [show (1 : ℝ) ≤ (q : ℝ) ^ t from one_le_pow₀ hqreal]
  have hlast :
      ((A : ℝ) * (q : ℝ) ^ t) ^ (m - w) ≤
        ((A : ℝ) * (q : ℝ) ^ t) ^ m := by
    exact pow_le_pow_right₀ hbase (Nat.sub_le m w)
  have hCbase :
      (4 : ℝ) * ((A : ℝ) * (q : ℝ) ^ t) ≤
        (absorptionConstant t A : ℝ) * (q : ℝ) ^ t := by
    have htR : (1 : ℝ) ≤ t := by exact_mod_cast ht
    simp only [absorptionConstant, Nat.cast_mul, Nat.cast_ofNat]
    have hqt0 : (0 : ℝ) ≤ (q : ℝ) ^ t := by positivity
    nlinarith
  change (2 : ℝ) ^ m *
      (4 * (q : ℝ) ^ (2 * t - 1)) ^ w *
      ((A : ℝ) * (q : ℝ) ^ t) ^ (m - w) ≤ _
  calc
    (2 : ℝ) ^ m *
          (4 * (q : ℝ) ^ (2 * t - 1)) ^ w *
          ((A : ℝ) * (q : ℝ) ^ t) ^ (m - w) ≤
        (2 : ℝ) ^ m * (2 : ℝ) ^ m *
          ((A : ℝ) * (q : ℝ) ^ t) ^ m := by gcongr
    _ = ((4 : ℝ) * ((A : ℝ) * (q : ℝ) ^ t)) ^ m := by
      rw [← mul_pow, ← mul_pow]
      ring_nf
    _ ≤ ((absorptionConstant t A : ℝ) * (q : ℝ) ^ t) ^ m := by
      gcongr

end

end Erdos920.NumericAbsorption












namespace Erdos920.StoppingPower

open Erdos920.ContainerNumeric

noncomputable section


def stoppingCoefficient (t : ℕ) : ℕ :=
  320 * t * t * (t + 1)


def stoppingDepth (t q : ℕ) : ℕ :=
  stoppingCoefficient t * q * ⌈Real.log (q : ℝ)⌉₊


def branchFactor (t q : ℕ) : ℕ := 32 * t * q


def terminalBound (t q : ℕ) : ℕ := 2 * q ^ t




theorem le_four_pow_ceil_log {q : ℕ} (hq : 2 ≤ q) :
    q ≤ 4 ^ ⌈Real.log (q : ℝ)⌉₊ := by
  let z := ⌈Real.log (q : ℝ)⌉₊
  have hqR : (0 : ℝ) < q := by positivity
  have hlog : Real.log (q : ℝ) ≤ (z : ℝ) := by
    simpa [z] using Nat.le_ceil (Real.log (q : ℝ))
  have hexp : (q : ℝ) ≤ Real.exp (z : ℝ) := by
    rw [← Real.exp_log hqR]
    exact Real.exp_le_exp.mpr hlog
  have hbase : Real.exp 1 ≤ (4 : ℝ) :=
    Real.exp_one_lt_three.le.trans (by norm_num)
  have hpow : Real.exp 1 ^ z ≤ (4 : ℝ) ^ z := by
    exact pow_le_pow_left₀ (Real.exp_pos 1).le hbase z
  have hexp' : Real.exp (z : ℝ) = Real.exp 1 ^ z := by
    simp
  rw [hexp'] at hexp
  exact_mod_cast hexp.trans hpow



theorem natLogTwo_add_one_le_three_ceil_log {q : ℕ} (hq : 4 ≤ q) :
    Nat.log 2 q + 1 ≤ 3 * ⌈Real.log (q : ℝ)⌉₊ := by
  let L := Nat.log 2 q
  let z := ⌈Real.log (q : ℝ)⌉₊
  have hq0 : q ≠ 0 := by omega
  have hlow : 2 ^ L ≤ q := by
    simpa [L] using Nat.pow_log_le_self 2 hq0
  have hupp : q ≤ 2 ^ (2 * z) := by
    calc
      q ≤ 4 ^ z := by
        simpa [z] using le_four_pow_ceil_log (by omega : 2 ≤ q)
      _ = 2 ^ (2 * z) := by rw [show 4 = 2 ^ 2 by norm_num, pow_mul]
  have hpow : 2 ^ L ≤ 2 ^ (2 * z) := hlow.trans hupp
  have hLz : L ≤ 2 * z :=
    (Nat.pow_le_pow_iff_right (by omega : 1 < 2)).mp hpow
  have hz : 1 ≤ z := by
    have hlog : (0 : ℝ) < Real.log (q : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < q by omega))
    exact Nat.ceil_pos.mpr hlog
  calc
    Nat.log 2 q + 1 = L + 1 := by rfl
    _ ≤ 2 * z + z := Nat.add_le_add hLz hz
    _ = 3 * ⌈Real.log (q : ℝ)⌉₊ := by simp [z]; ring


theorem contractionBudget_le_stoppingDepth {t q : ℕ}
    (ht : 1 ≤ t) (hq : 4 ≤ q) :
    contractionBudget (branchFactor t q) t q ≤ stoppingDepth t q := by
  let z := ⌈Real.log (q : ℝ)⌉₊
  have hz : 1 ≤ z := by
    have hlog : (0 : ℝ) < Real.log (q : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < q by omega))
    exact Nat.ceil_pos.mpr hlog
  have hlog := natLogTwo_add_one_le_three_ceil_log hq
  have hblocks : stoppingBlocks t q ≤ 5 * t * z := by
    calc
      stoppingBlocks t q = t * (Nat.log 2 q + 1) + 2 := rfl
      _ ≤ t * (3 * z) + 2 * z := by
        apply Nat.add_le_add
        · exact Nat.mul_le_mul_left t (by simpa [z] using hlog)
        · omega
      _ = (3 * t + 2) * z := by ring
      _ ≤ (5 * t) * z := Nat.mul_le_mul_right z (by omega)
      _ = 5 * t * z := by ring
  calc
    contractionBudget (branchFactor t q) t q =
        64 * t * q * stoppingBlocks t q := by
      unfold contractionBudget branchFactor
      ring
    _ ≤ 64 * t * q * (5 * t * z) := Nat.mul_le_mul_left _ hblocks
    _ = 320 * t * t * q * z := by ring
    _ ≤ (320 * t * t * q * z) * (t + 1) :=
      by
        simpa using Nat.mul_le_mul_left (320 * t * t * q * z)
          (show 1 ≤ t + 1 by omega)
    _ = 320 * t * t * (t + 1) * q * z := by ring
    _ = stoppingDepth t q := by simp [stoppingDepth, stoppingCoefficient, z]



theorem stoppingCoefficient_pos {t : ℕ} (ht : 1 ≤ t) :
    1 ≤ stoppingCoefficient t := by
  have : 0 < stoppingCoefficient t := by
    simp only [stoppingCoefficient]
    positivity
  omega




theorem projective_stopping_power {t q c : ℕ}
    (ht : 2 ≤ t) (hq : 4 ≤ q) (hc : stoppingDepth t q < c) :
    (2 * branchFactor t q - 1) ^ c * (terminalBound t q + 1) <
      (2 * branchFactor t q) ^ c := by
  apply projective_contraction_stopping
      (t := t) (q := q) (N := terminalBound t q)
      (by omega) (by omega) (by simp [terminalBound]) c
  exact (contractionBudget_le_stoppingDepth (by omega) hq).trans_lt hc


theorem projective_stopping_power_expanded {t q c : ℕ}
    (ht : 2 ≤ t) (hq : 4 ≤ q)
    (hc : stoppingCoefficient t * q * ⌈Real.log (q : ℝ)⌉₊ < c) :
    (2 * (32 * t * q) - 1) ^ c * (2 * q ^ t + 1) <
      (2 * (32 * t * q)) ^ c := by
  exact projective_stopping_power ht hq hc



theorem exists_stopping_parameters (t : ℕ) (ht : 2 ≤ t) :
    ∃ Astop Q : ℕ, 1 ≤ Astop ∧ 2 ≤ Q ∧
      ∀ q c : ℕ, Q ≤ q →
        Astop * q * ⌈Real.log (q : ℝ)⌉₊ < c →
          (2 * (32 * t * q) - 1) ^ c * (2 * q ^ t + 1) <
            (2 * (32 * t * q)) ^ c := by
  refine ⟨stoppingCoefficient t, 4, stoppingCoefficient_pos (by omega),
    by omega, ?_⟩
  intro q c hq hc
  exact projective_stopping_power_expanded ht hq hc

end

end Erdos920.StoppingPower












open scoped LinearAlgebra.Projectivization

namespace Erdos920.ForwardBound

noncomputable section

open Erdos920.Projective
open Erdos920.ProjectiveDStar
open Erdos920.RamseyPackaging


def markedCoefficient (t : ℕ) : ℕ := 2112 * (t + 1)


def totalStoppingCoefficient (t : ℕ) : ℕ :=
  (t + 2) * StoppingPower.stoppingCoefficient t


def treeCoefficient (t : ℕ) : ℕ :=
  max (markedCoefficient t) (totalStoppingCoefficient t)



def forwardConstantNat (t : ℕ) : ℕ :=
  NumericAbsorption.absorptionConstant t (treeCoefficient t)


def forwardThreshold (t : ℕ) : ℕ := max 4 (treeCoefficient t)

theorem treeCoefficient_pos (t : ℕ) : 1 ≤ treeCoefficient t := by
  unfold treeCoefficient markedCoefficient
  omega

theorem forwardConstantNat_pos {t : ℕ} (ht : 2 ≤ t) :
    0 < forwardConstantNat t := by
  exact NumericAbsorption.absorptionConstant_pos (by omega)
    (treeCoefficient_pos t)

variable {q t m : ℕ} [Fact q.Prime]

abbrev PointT (q t : ℕ) [Fact q.Prime] :=
  Projective.Point (ZMod q) (t + 1)

local instance pointFintype : Fintype (PointT q t) := Fintype.ofFinite _
local instance pointDecidableEq : DecidableEq (PointT q t) := Classical.decEq _
local instance orthogonalDecidable :
    DecidableRel (@Projective.Orthogonal (ZMod q) _ (t + 1)) :=
  Classical.decRel _



theorem tupleChildren_eq_projectiveChildren :
    TupleBound.consistentChildren
        (TupleHistory.incidentPairs (q := q) (t := t))
        Projective.Orthogonal =
      MarkedChildren.projectiveChildren q t := by
  funext sigma
  ext p
  simp [TupleBound.consistentChildren, TupleHistory.incidentPairs,
    MarkedChildren.projectiveChildren, MarkedChildren.projectiveVertices,
    ProjectiveContainer.incidentPairs]



theorem projectiveChildren_card_le (ht : 1 ≤ t)
    (sigma : List (PointT q t × PointT q t)) :
    (MarkedChildren.projectiveChildren q t sigma).card ≤
      4 * q ^ (2 * t - 1) := by
  have hsub : MarkedChildren.projectiveChildren q t sigma ⊆
      MarkedChildren.projectiveVertices q t :=
    Finset.filter_subset _ _
  have hcard :
      (MarkedChildren.projectiveVertices q t).card =
        Fintype.card (ProjectiveDStar.Vertex q t) := by
    classical
    simpa [MarkedChildren.projectiveVertices,
      ProjectiveContainer.incidentPairs] using
      (Fintype.card_subtype
        (fun p : PointT q t × PointT q t ↦
          Projective.Orthogonal p.1 p.2)).symm
  calc
    (MarkedChildren.projectiveChildren q t sigma).card ≤
        (MarkedChildren.projectiveVertices q t).card :=
      Finset.card_le_card hsub
    _ = Fintype.card (ProjectiveDStar.Vertex q t) := hcard
    _ ≤ 4 * q ^ (2 * t - 1) :=
      ProjectiveDStar.card_vertex_le_four_mul_pow q t ht



theorem projective_unmarkedCount_le (ht : 2 ≤ t) (hq : 4 ≤ q)
    (xs : List (PointT q t × PointT q t))
    (hpath : MarkedTree.IsPath
      (MarkedChildren.projectiveChildren q t) xs) :
    (MarkedTree.pathSignature (MarkedChildren.projectiveMarked q t) xs).count false ≤
      NumericAbsorption.unmarkedBudget (treeCoefficient t) q := by
  let K : ℕ := 32 * t * q
  let N : ℕ := Fintype.card (PointT q t)
  let w : ℕ := StoppingPower.stoppingDepth t q
  let cert := MarkedChildren.projectiveShrinkCertificate q t ht
  have hK : 1 ≤ K := by
    dsimp [K]
    have h32t : 1 ≤ 32 * t :=
      Nat.mul_le_mul (by norm_num : 1 ≤ 32) (by omega : 1 ≤ t)
    simpa using Nat.mul_le_mul h32t (show 1 ≤ q by omega)
  have hN : N ≤ 2 * q ^ t := by
    dsimp [N]
    simpa only [Nat.card_eq_fintype_card] using
      (Projective.point_zmod_bounds q t).2
  have hpow : ∀ c : ℕ, w < c →
      (2 * K - 1) ^ c * (N + 1) < (2 * K) ^ c := by
    intro c hc
    have hstop := StoppingPower.projective_stopping_power ht hq hc
    have hterminal : N + 1 ≤ StoppingPower.terminalBound t q + 1 :=
      Nat.add_le_add_right hN 1
    exact (Nat.mul_le_mul_left ((2 * K - 1) ^ c) hterminal).trans_lt (by
      simpa [K, StoppingPower.branchFactor] using hstop)
  have hcount := Container.unmarkedCount_le_of_certificate
    (L := Fin (t + 2)) cert hK hpow xs hpath
  calc
    (MarkedTree.pathSignature (MarkedChildren.projectiveMarked q t) xs).count false
        ≤ (t + 2) * StoppingPower.stoppingDepth t q := by
      simpa [cert, K, N, w] using hcount
    _ ≤ NumericAbsorption.unmarkedBudget (treeCoefficient t) q := by
      simp only [StoppingPower.stoppingDepth,
        NumericAbsorption.unmarkedBudget]
      simpa [treeCoefficient, totalStoppingCoefficient, Nat.mul_assoc] using
        Nat.mul_le_mul_right
          (q * ⌈Real.log (q : ℝ)⌉₊)
          (Nat.le_max_right (markedCoefficient t)
            (totalStoppingCoefficient t))


theorem forwardIndependentTupleCount_le_tree
    (ht : 2 ≤ t) (hq : 4 ≤ q)
    (hAq : treeCoefficient t ≤ q)
    (hm : (forwardConstantNat t : ℝ) * (q : ℝ) *
      Real.log (q : ℝ) ^ 2 ≤ (m : ℝ)) :
    @Digraph.forwardIndependentTupleCount
        (ProjectiveDStar.Vertex q t)
        (ProjectiveDStar.vertexFintype q t)
        (ProjectiveDStar.digraph q t) m ≤
      2 ^ m * (4 * q ^ (2 * t - 1)) ^
          NumericAbsorption.unmarkedBudget (treeCoefficient t) q *
        (treeCoefficient t * q ^ t) ^
          (m - NumericAbsorption.unmarkedBudget (treeCoefficient t) q) := by
  let children := MarkedChildren.projectiveChildren q t
  let marked := MarkedChildren.projectiveMarked q t
  let Delta := 4 * q ^ (2 * t - 1)
  let h := treeCoefficient t * q ^ t
  let w := NumericAbsorption.unmarkedBudget (treeCoefficient t) q
  have hchildren : ∀ sigma, (children sigma).card ≤ Delta := by
    intro sigma
    exact projectiveChildren_card_le (q := q) (t := t) (by omega) sigma
  have hmarked : ∀ sigma,
      ((children sigma).filter fun p ↦ marked sigma p = true).card ≤ h := by
    intro sigma
    calc
      ((children sigma).filter fun p ↦ marked sigma p = true).card =
          (MarkedChildrenBound.markedChildren q t sigma).card := by
        rfl
      _ ≤ 2112 * (t + 1) * q ^ t :=
        MarkedChildrenBound.markedChildren_card_le ht sigma
      _ ≤ treeCoefficient t * q ^ t :=
        Nat.mul_le_mul_right (q ^ t)
          (Nat.le_max_left (markedCoefficient t)
            (totalStoppingCoefficient t))
  have hunmarked : ∀ xs, MarkedTree.IsPath children xs → xs.length = m →
      (MarkedTree.pathSignature marked xs).count false ≤ w := by
    intro xs hpath _hlen
    exact projective_unmarkedCount_le ht hq xs hpath
  have hhDelta : h ≤ Delta := by
    have hq1 : 1 ≤ q := by omega
    calc
      treeCoefficient t * q ^ t ≤ q * q ^ t :=
        Nat.mul_le_mul_right (q ^ t) hAq
      _ = q ^ (t + 1) := by rw [pow_succ']
      _ ≤ q ^ (2 * t - 1) := by
        exact Nat.pow_le_pow_right hq1 (by omega)
      _ ≤ 4 * q ^ (2 * t - 1) := by omega
  have hwm : w ≤ m :=
    NumericAbsorption.unmarkedBudget_le (by omega)
      (treeCoefficient_pos t) hq hm
  have htree := Container.card_allPaths_le children marked
    hchildren hmarked hunmarked hhDelta hwm
  rw [TupleHistory.forwardIndependentTupleCount_eq_card_allPaths marked,
    tupleChildren_eq_projectiveChildren] 
  simpa [children, marked, Delta, h, w] using htree


theorem forwardIndependentTupleCount_le
    (ht : 2 ≤ t) (hq : 4 ≤ q)
    (hAq : treeCoefficient t ≤ q)
    (hm : (forwardConstantNat t : ℝ) * (q : ℝ) *
      Real.log (q : ℝ) ^ 2 ≤ (m : ℝ)) :
    ((@Digraph.forwardIndependentTupleCount
        (ProjectiveDStar.Vertex q t)
        (ProjectiveDStar.vertexFintype q t)
        (ProjectiveDStar.digraph q t) m : ℕ) : ℝ) ≤
      ((forwardConstantNat t : ℝ) * (q : ℝ) ^ t) ^ m := by
  have hnat := forwardIndependentTupleCount_le_tree
    (q := q) (t := t) (m := m) ht hq hAq hm
  have hreal :
      ((@Digraph.forwardIndependentTupleCount
          (ProjectiveDStar.Vertex q t)
          (ProjectiveDStar.vertexFintype q t)
          (ProjectiveDStar.digraph q t) m : ℕ) : ℝ) ≤
        (2 : ℝ) ^ m *
          (4 * (q : ℝ) ^ (2 * t - 1)) ^
            NumericAbsorption.unmarkedBudget (treeCoefficient t) q *
          ((treeCoefficient t : ℝ) * (q : ℝ) ^ t) ^
            (m - NumericAbsorption.unmarkedBudget (treeCoefficient t) q) := by
    exact_mod_cast hnat
  exact hreal.trans
    (NumericAbsorption.markedTree_numeric_absorption
      (by omega) (treeCoefficient_pos t) hq hm)






theorem exists_forwardConstant (t : ℕ) (ht : 2 ≤ t) :
    ∃ C : ℝ, 0 < C ∧ ∃ Q : ℕ,
      ∀ (q m : ℕ), (hq : q.Prime) → Q ≤ q →
        C * (q : ℝ) * Real.log (q : ℝ) ^ 2 ≤ (m : ℝ) →
        letI : Fact q.Prime := ⟨hq⟩
        ((@Digraph.forwardIndependentTupleCount
            (ProjectiveDStar.Vertex q t)
            (ProjectiveDStar.vertexFintype q t)
            (ProjectiveDStar.digraph q t) m : ℕ) : ℝ) ≤
          (C * (q : ℝ) ^ t) ^ m := by
  refine ⟨(forwardConstantNat t : ℝ), ?_, forwardThreshold t, ?_⟩
  · exact_mod_cast forwardConstantNat_pos ht
  · intro q m hq hQ hm
    let : Fact q.Prime := ⟨hq⟩
    have hq4 : 4 ≤ q :=
      (Nat.le_max_left 4 (treeCoefficient t)).trans hQ
    have hAq : treeCoefficient t ≤ q :=
      (Nat.le_max_right 4 (treeCoefficient t)).trans hQ
    exact forwardIndependentTupleCount_le ht hq4 hAq hm

end

end Erdos920.ForwardBound






















open scoped BigOperators

namespace Erdos920

section OrderedDigraph

variable {V : Type*}



def ForwardIndependent (D : V → V → Prop) {k : ℕ} (x : Fin k → V) : Prop :=
  ∀ ⦃i j : Fin k⦄, i < j → ¬ D (x i) (x j)


noncomputable def forwardIndependentFinset [Fintype V] (D : V → V → Prop) (k : ℕ) :
    Finset (Fin k → V) := by
  classical
  exact Finset.univ.filter (ForwardIndependent D)

@[simp]
lemma mem_forwardIndependentFinset [Fintype V] {D : V → V → Prop} {k : ℕ} {x : Fin k → V} :
    x ∈ forwardIndependentFinset D k ↔ ForwardIndependent D x := by
  classical
  simp [forwardIndependentFinset]


def TransitiveTournamentFree (D : V → V → Prop) (s : ℕ) : Prop :=
  ∀ x : Fin s → V, Function.Injective x →
    ¬ ∀ ⦃i j : Fin s⦄, i < j → D (x i) (x j)

variable [LinearOrder V]



def forwardGraph (D : V → V → Prop) (π : Equiv.Perm V) :
    SimpleGraph V :=
  SimpleGraph.fromRel fun u v => π u < π v ∧ D u v



noncomputable instance instDecidableRelForwardGraph (D : V → V → Prop)
    (π : Equiv.Perm V) : DecidableRel (forwardGraph D π).Adj :=
  Classical.decRel _

lemma forwardGraph_adj_iff {D : V → V → Prop} {π : Equiv.Perm V} {u v : V} :
    (forwardGraph D π).Adj u v ↔
      u ≠ v ∧ ((π u < π v ∧ D u v) ∨ (π v < π u ∧ D v u)) :=
  Iff.rfl



noncomputable def orderedTuple (π : Equiv.Perm V) (S : Finset V) {k : ℕ}
    (hS : S.card = k) : Fin k → V :=
  fun i => π.symm ((S.map π.toEmbedding).orderEmbOfFin (by simpa using hS) i)

lemma orderedTuple_injective (π : Equiv.Perm V) (S : Finset V) {k : ℕ}
    (hS : S.card = k) : Function.Injective (orderedTuple π S hS) := by
  intro i j hij
  apply (S.map π.toEmbedding).orderEmbOfFin (by simpa using hS) |>.injective
  simpa [orderedTuple] using congrArg π hij

lemma orderedTuple_mem (π : Equiv.Perm V) (S : Finset V) {k : ℕ}
    (hS : S.card = k) (i : Fin k) : orderedTuple π S hS i ∈ S := by
  have hi := (S.map π.toEmbedding).orderEmbOfFin_mem (by simpa using hS) i
  simpa [orderedTuple] using hi

@[simp]
lemma range_orderedTuple (π : Equiv.Perm V) (S : Finset V) {k : ℕ}
    (hS : S.card = k) : Set.range (orderedTuple π S hS) = (S : Set V) := by
  ext v
  constructor
  · rintro ⟨i, rfl⟩
    exact orderedTuple_mem π S hS i
  · intro hv
    let y : S.map π.toEmbedding := ⟨π v, by simpa using hv⟩
    obtain ⟨i, hi⟩ :=
      ((S.map π.toEmbedding).orderIsoOfFin (by simpa using hS)).surjective y
    refine ⟨i, ?_⟩
    apply π.injective
    simpa [orderedTuple, y] using congrArg Subtype.val hi

lemma orderedTuple_strictMono_after (π : Equiv.Perm V) (S : Finset V) {k : ℕ}
    (hS : S.card = k) : StrictMono (fun i => π (orderedTuple π S hS i)) := by
  simpa [orderedTuple] using
    (S.map π.toEmbedding).orderEmbOfFin (by simpa using hS) |>.strictMono



lemma forwardGraph_cliqueFree {D : V → V → Prop} {s : ℕ}
    (hD : TransitiveTournamentFree D s) (π : Equiv.Perm V) :
    (forwardGraph D π).CliqueFree s := by
  intro C hC
  let x : Fin s → V := orderedTuple π C hC.card_eq
  have hxinj : Function.Injective x := orderedTuple_injective π C hC.card_eq
  apply hD x hxinj
  intro i j hij
  have hxi : x i ∈ C := orderedTuple_mem π C hC.card_eq i
  have hxj : x j ∈ C := orderedTuple_mem π C hC.card_eq j
  have hn : x i ≠ x j := fun h => hij.ne (hxinj h)
  have hadj : (forwardGraph D π).Adj (x i) (x j) :=
    hC.isClique hxi hxj hn
  rcases (forwardGraph_adj_iff.mp hadj).2 with h | h
  · exact h.2
  · have hlt := orderedTuple_strictMono_after π C hC.card_eq hij
    exact (lt_asymm hlt h.1).elim

lemma orderedTuple_forwardIndependent {D : V → V → Prop} (π : Equiv.Perm V)
    (S : Finset V) {k : ℕ} (hS : S.card = k)
    (hI : (forwardGraph D π).IsIndepSet (S : Set V)) :
    ForwardIndependent D (orderedTuple π S hS) := by
  intro i j hij hDij
  have hlt : π (orderedTuple π S hS i) < π (orderedTuple π S hS j) :=
    orderedTuple_strictMono_after π S hS hij
  have hn : orderedTuple π S hS i ≠ orderedTuple π S hS j :=
    fun h => hij.ne (orderedTuple_injective π S hS h)
  exact hI (orderedTuple_mem π S hS i) (orderedTuple_mem π S hS j)
    hn ((forwardGraph_adj_iff).2 ⟨hn, Or.inl ⟨hlt, hDij⟩⟩)




lemma indepSetFinset_card_forwardGraph_le [Fintype V] {D : V → V → Prop}
    (π : Equiv.Perm V)
    (k : ℕ) :
    ((forwardGraph D π).indepSetFinset k).card ≤
      (forwardIndependentFinset D k).card := by
  classical
  let A := (forwardGraph D π).indepSetFinset k
  let f : {S // S ∈ A} → (Fin k → V) := fun S =>
    orderedTuple π S.1 <| (SimpleGraph.mem_indepSetFinset_iff.mp S.2).card_eq
  rw [← Finset.card_attach (s := A)]
  refine Finset.card_le_card_of_injOn f ?_ ?_
  · intro S hS
    have hNS := SimpleGraph.mem_indepSetFinset_iff.mp S.2
    exact mem_forwardIndependentFinset.mpr
      (orderedTuple_forwardIndependent π S.1 hNS.card_eq hNS.isIndepSet)
  · intro S hS T hT hST
    apply Subtype.ext
    apply Finset.coe_injective
    rw [← range_orderedTuple π S.1
          (SimpleGraph.mem_indepSetFinset_iff.mp S.2).card_eq,
      ← range_orderedTuple π T.1
          (SimpleGraph.mem_indepSetFinset_iff.mp T.2).card_eq]
    exact congrArg Set.range hST

end OrderedDigraph

section Deletion

variable {V : Type*} [Fintype V] [DecidableEq V]


def survivingIndepSetFinset (G : SimpleGraph V) [DecidableRel G.Adj]
    (k : ℕ) (A : Finset V) : Finset (Finset V) :=
  (G.indepSetFinset k).filter (· ⊆ A)

@[simp]
lemma mem_survivingIndepSetFinset {G : SimpleGraph V} [DecidableRel G.Adj]
    {k : ℕ} {A T : Finset V} :
    T ∈ survivingIndepSetFinset G k A ↔ G.IsNIndepSet k T ∧ T ⊆ A := by
  simp [survivingIndepSetFinset, SimpleGraph.mem_indepSetFinset_iff]



lemma exists_induced_indepSetFree_subgraph_subset
    (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset V)
    {k : ℕ} (hk : 1 ≤ k) :
    ∃ U : Finset V, U ⊆ A ∧
      A.card - (survivingIndepSetFinset G k A).card ≤ U.card ∧
        (G.induce (U : Set V)).IndepSetFree k := by
  classical
  let B : Finset (Finset V) := survivingIndepSetFinset G k A
  let pick : {T // T ∈ B} → V := fun T =>
    Classical.choose <| by
      have hT : G.IsNIndepSet k T.1 :=
        (mem_survivingIndepSetFinset.mp (show T.1 ∈ B from T.2)).1
      exact Finset.card_pos.mp (hT.card_eq ▸ hk)
  have hpick_mem : ∀ T : {T // T ∈ B}, pick T ∈ T.1 := by
    intro T
    exact Classical.choose_spec <| by
      have hT : G.IsNIndepSet k T.1 :=
        (mem_survivingIndepSetFinset.mp (show T.1 ∈ B from T.2)).1
      exact Finset.card_pos.mp (hT.card_eq ▸ hk)
  let deleted : Finset V := B.attach.image pick
  let U : Finset V := A \ deleted
  have hdeletedA : deleted ⊆ A := by
    intro v hv
    rcases Finset.mem_image.mp hv with ⟨T, hT, rfl⟩
    have hTA : T.1 ⊆ A :=
      (mem_survivingIndepSetFinset.mp (show T.1 ∈ B from T.2)).2
    exact hTA (hpick_mem T)
  have hUsub : U ⊆ A := Finset.sdiff_subset
  have hUcard : A.card - B.card ≤ U.card := by
    have hd : deleted.card ≤ B.card := by
      simpa [deleted] using Finset.card_image_le (s := B.attach) (f := pick)
    calc
      A.card - B.card ≤ A.card - deleted.card := Nat.sub_le_sub_left hd _
      _ = U.card := by
        symm
        simpa [U] using Finset.card_sdiff_of_subset hdeletedA
  have hhit : ∀ {T : Finset V}, T ∈ B → T ⊆ U → False := by
    intro T hT hTU
    let TT : {T // T ∈ B} := ⟨T, hT⟩
    have hpdel : pick TT ∈ deleted :=
      Finset.mem_image.mpr ⟨TT, by simp, rfl⟩
    have hpU : pick TT ∈ U := hTU (hpick_mem TT)
    exact (Finset.mem_sdiff.mp hpU).2 hpdel
  have hfree : (G.induce (U : Set V)).IndepSetFree k := by
    intro T hT
    let T' : Finset V := T.map ⟨Subtype.val, Subtype.val_injective⟩
    have hT' : G.IsNIndepSet k T' := by
      have hTi :
          (((⊤ : SimpleGraph.Subgraph G).induce (U : Set V)).coe).IsNIndepSet k T := by
        rw [← SimpleGraph.induce_eq_coe_induce_top]
        exact hT
      simpa [T'] using
        (SimpleGraph.isNIndepSet_induce (G := G) (F := (U : Set V))
          (s := T) (n := k)).mp hTi
    have hT'U : T' ⊆ U := by
      intro v hv
      rcases Finset.mem_map.mp hv with ⟨x, hx, rfl⟩
      exact x.property
    have hT'A : T' ⊆ A := hT'U.trans hUsub
    exact hhit (by exact mem_survivingIndepSetFinset.mpr ⟨hT', hT'A⟩) hT'U
  exact ⟨U, hUsub, by simpa [B] using hUcard, hfree⟩




lemma exists_induced_indepSetFree_subgraph (G : SimpleGraph V) [DecidableRel G.Adj]
    {k : ℕ} (hk : 1 ≤ k) :
    ∃ U : Finset V,
      Fintype.card V - (G.indepSetFinset k).card ≤ U.card ∧
        (G.induce (U : Set V)).IndepSetFree k := by
  classical
  let B : Finset (Finset V) := G.indepSetFinset k
  let pick : {T // T ∈ B} → V := fun T =>
    Classical.choose <| by
      have hT : G.IsNIndepSet k T.1 := by
        simpa [B] using (SimpleGraph.mem_indepSetFinset_iff.mp T.2)
      exact Finset.card_pos.mp (hT.card_eq ▸ hk)
  have hpick_mem : ∀ T : {T // T ∈ B}, pick T ∈ T.1 := by
    intro T
    exact Classical.choose_spec <| by
      have hT : G.IsNIndepSet k T.1 := by
        simpa [B] using (SimpleGraph.mem_indepSetFinset_iff.mp T.2)
      exact Finset.card_pos.mp (hT.card_eq ▸ hk)
  let deleted : Finset V := B.attach.image pick
  let U : Finset V := Finset.univ \ deleted
  have hUcard : Fintype.card V - B.card ≤ U.card := by
    have hd : deleted.card ≤ B.card := by
      simpa [deleted] using Finset.card_image_le (s := B.attach) (f := pick)
    calc
      Fintype.card V - B.card ≤ Fintype.card V - deleted.card :=
        Nat.sub_le_sub_left hd _
      _ = U.card := by
        symm
        simp [U, Finset.card_sdiff_of_subset, Finset.subset_univ]
  have hhit : ∀ {T : Finset V}, T ∈ B → T ⊆ U → False := by
    intro T hT hTU
    let TT : {T // T ∈ B} := ⟨T, hT⟩
    have hpdel : pick TT ∈ deleted :=
      Finset.mem_image.mpr ⟨TT, by simp, rfl⟩
    have hpU : pick TT ∈ U := hTU (hpick_mem TT)
    have hpnot : pick TT ∉ deleted := by
      exact (show pick TT ∈ Finset.univ ∧ pick TT ∉ deleted by simpa [U] using hpU).2
    exact hpnot hpdel
  have hfree : (G.induce (U : Set V)).IndepSetFree k := by
    intro T hT
    let T' : Finset V := T.map ⟨Subtype.val, Subtype.val_injective⟩
    have hT' : G.IsNIndepSet k T' := by
      have hTi :
          (((⊤ : SimpleGraph.Subgraph G).induce (U : Set V)).coe).IsNIndepSet k T := by
        rw [← SimpleGraph.induce_eq_coe_induce_top]
        exact hT
      simpa [T'] using
        (SimpleGraph.isNIndepSet_induce (G := G) (F := (U : Set V))
          (s := T) (n := k)).mp hTi
    have hT'U : T' ⊆ U := by
      intro v hv
      rcases Finset.mem_map.mp hv with ⟨x, hx, rfl⟩
      exact x.property
    exact hhit (by simpa [B] using hT') hT'U
  exact ⟨U, by simpa [B] using hUcard, hfree⟩



lemma exists_ramsey_graph_of_indepSet_count
    (G : SimpleGraph V) [DecidableRel G.Adj] {s k : ℕ} (hk : 1 ≤ k)
    (hcf : G.CliqueFree s) :
    ∃ n : ℕ,
      Fintype.card V - (G.indepSetFinset k).card ≤ n ∧
        ∃ H : SimpleGraph (Fin n), H.CliqueFree s ∧ H.IndepSetFree k := by
  classical
  obtain ⟨U, hUcard, hUfree⟩ := exists_induced_indepSetFree_subgraph G hk
  let G' : SimpleGraph {x // x ∈ (U : Set V)} := G.induce (U : Set V)
  have hG'cf : G'.CliqueFree s :=
    hcf.comap (SimpleGraph.Embedding.induce (G := G) (s := (U : Set V))).isContained
  let n := U.card
  have hcard : Fintype.card {x // x ∈ (U : Set V)} = n := by simp [n]
  let H : SimpleGraph (Fin n) := G'.overFin hcard
  have hi : G' ≃g H := SimpleGraph.overFinIso (G := G') hcard
  refine ⟨n, hUcard, H, ?_, ?_⟩
  · exact (SimpleGraph.Iso.cliqueFree_iff (n := s) (e := hi)).mp hG'cf
  · exact (SimpleGraph.Iso.indepSetFree_iff (n := k) (e := hi)).mp hUfree

end Deletion

section Sampling

variable {V : Type*}

open Erdos202.ParkPham



lemma sum_bernoulliMass_indicator_superset [DecidableEq V] (X T : Finset V) (hTX : T ⊆ X)
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (∑ W ∈ X.powerset,
        bernoulliMass X W p * (if T ⊆ W then (1 : ℝ) else 0)) = p ^ T.card := by
  calc
    (∑ W ∈ X.powerset,
        bernoulliMass X W p * (if T ⊆ W then (1 : ℝ) else 0)) =
        muP X (upClosureIn X {T}) p := by
          rw [upClosureIn_singleton X T hTX]
          simp only [muP, Finset.mem_filter, Finset.mem_powerset]
          rw [Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro W hW
          simp [Finset.mem_powerset.mp hW]
    _ = p ^ T.card := muP_upClosure_single X T hTX hp0 hp1




lemma sum_bernoulliMass_contained_count [DecidableEq V] (X : Finset V) (A : Finset (Finset V))
    {k : ℕ} (hAX : ∀ T ∈ A, T ⊆ X) (hcard : ∀ T ∈ A, T.card = k)
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (∑ W ∈ X.powerset,
        bernoulliMass X W p * ((A.filter (· ⊆ W)).card : ℝ)) =
      p ^ k * A.card := by
  calc
    (∑ W ∈ X.powerset,
        bernoulliMass X W p * ((A.filter (· ⊆ W)).card : ℝ)) =
        ∑ W ∈ X.powerset,
          ∑ T ∈ A, bernoulliMass X W p * (if T ⊆ W then (1 : ℝ) else 0) := by
            apply Finset.sum_congr rfl
            intro W hW
            rw [← Finset.mul_sum, Finset.sum_boole]
    _ = ∑ T ∈ A,
          ∑ W ∈ X.powerset,
            bernoulliMass X W p * (if T ⊆ W then (1 : ℝ) else 0) := by
          rw [Finset.sum_comm]
    _ = ∑ T ∈ A, p ^ T.card := by
          apply Finset.sum_congr rfl
          intro T hT
          exact sum_bernoulliMass_indicator_superset X T (hAX T hT) hp0 hp1
    _ = p ^ k * A.card := by
          rw [Finset.sum_congr rfl (fun T hT => by rw [hcard T hT])]
          simp [mul_comm]


lemma sum_bernoulliMass_card (X : Finset V) {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (∑ W ∈ X.powerset, bernoulliMass X W p * (W.card : ℝ)) =
      p * X.card := by
  classical
  calc
    (∑ W ∈ X.powerset, bernoulliMass X W p * (W.card : ℝ)) =
        ∑ W ∈ X.powerset,
          ∑ v ∈ X, bernoulliMass X W p * (if v ∈ W then (1 : ℝ) else 0) := by
            apply Finset.sum_congr rfl
            intro W hW
            have hWX : W ⊆ X := Finset.mem_powerset.mp hW
            have hfilter : X.filter (· ∈ W) = W := by
              ext v
              simp only [Finset.mem_filter]
              constructor
              · exact And.right
              · intro hv
                exact ⟨hWX hv, hv⟩
            rw [show (W.card : ℝ) =
                ∑ v ∈ X, if v ∈ W then (1 : ℝ) else 0 by
              rw [Finset.sum_boole]
              rw [hfilter]]
            rw [Finset.mul_sum]
    _ = ∑ v ∈ X,
          ∑ W ∈ X.powerset,
            bernoulliMass X W p * (if ({v} : Finset V) ⊆ W then (1 : ℝ) else 0) := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro v hv
          apply Finset.sum_congr rfl
          intro W hW
          simp
    _ = ∑ _v ∈ X, p := by
          apply Finset.sum_congr rfl
          intro v hv
          simpa using sum_bernoulliMass_indicator_superset X ({v} : Finset V)
            (by simpa using hv) hp0 hp1
    _ = p * X.card := by simp [mul_comm]

end Sampling

end Erdos920














open scoped BigOperators

namespace Erdos920

section

variable {V : Type*} [LinearOrder V]




noncomputable def increasingForwardFinset [Fintype V] (D : V → V → Prop)
    (π : Equiv.Perm V) (k : ℕ) : Finset (Fin k → V) := by
  classical
  exact (forwardIndependentFinset D k).filter
    (fun x ↦ StrictMono (fun i ↦ π (x i)))

@[simp]
lemma mem_increasingForwardFinset [Fintype V] {D : V → V → Prop}
    {π : Equiv.Perm V} {k : ℕ} {x : Fin k → V} :
    x ∈ increasingForwardFinset D π k ↔
      ForwardIndependent D x ∧ StrictMono (fun i ↦ π (x i)) := by
  classical
  simp [increasingForwardFinset]

private lemma image_univ_card_of_strictMono {k : ℕ} {π : Equiv.Perm V}
    {x : Fin k → V} (hx : StrictMono (fun i ↦ π (x i))) :
    (Finset.univ.image x).card = k := by
  rw [Finset.card_image_iff.mpr]
  · simp
  · intro i hi j hj hij
    exact hx.injective (congrArg π hij)

private lemma image_univ_independent {D : V → V → Prop}
    {π : Equiv.Perm V} {k : ℕ} {x : Fin k → V}
    (hforward : ForwardIndependent D x)
    (hmono : StrictMono (fun i ↦ π (x i))) :
    (forwardGraph D π).IsIndepSet (Finset.univ.image x : Set V) := by
  intro u hu v hv huv hadj
  simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ,
    Set.mem_range] at hu hv
  obtain ⟨i, rfl⟩ := hu
  obtain ⟨j, rfl⟩ := hv
  rcases lt_trichotomy i j with hij | hij | hij
  · rcases (forwardGraph_adj_iff.mp hadj).2 with h | h
    · exact hforward hij h.2
    · exact (lt_asymm (hmono hij) h.1).elim
  · exact huv (congrArg x hij)
  · rcases (forwardGraph_adj_iff.mp hadj).2 with h | h
    · exact (lt_asymm (hmono hij) h.1).elim
    · exact hforward hij h.2

private lemma strictMono_eq_of_image_eq {k : ℕ} {x y : Fin k → V}
    (hx : StrictMono x) (hy : StrictMono y)
    (hxy : Finset.univ.image x = Finset.univ.image y) : x = y := by
  have hcard : (Finset.univ.image x).card = k := by
    rw [Finset.card_image_iff.mpr]
    · simp
    · intro i hi j hj hij
      exact hx.injective hij
  have hxeq : x = (Finset.univ.image x).orderEmbOfFin hcard :=
    Finset.orderEmbOfFin_unique hcard (by simp) hx
  have hyeq : y = (Finset.univ.image x).orderEmbOfFin hcard :=
    Finset.orderEmbOfFin_unique hcard (by simp [hxy]) hy
  exact hxeq.trans hyeq.symm

private lemma increasing_tuple_eq_of_image_eq {k : ℕ} {π : Equiv.Perm V}
    {x y : Fin k → V}
    (hx : StrictMono (fun i ↦ π (x i)))
    (hy : StrictMono (fun i ↦ π (y i)))
    (hxy : Finset.univ.image x = Finset.univ.image y) : x = y := by
  apply π.injective.comp_left
  apply strictMono_eq_of_image_eq hx hy
  ext v
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, rfl⟩
    have hi : x i ∈ Finset.univ.image y := by
      rw [← hxy]
      simp
    obtain ⟨j, hj, hji⟩ := Finset.mem_image.mp hi
    exact ⟨j, by simp [hji]⟩
  · rintro ⟨i, rfl⟩
    have hi : y i ∈ Finset.univ.image x := by
      rw [hxy]
      simp
    obtain ⟨j, hj, hji⟩ := Finset.mem_image.mp hi
    exact ⟨j, by simp [hji]⟩

variable [Fintype V]



lemma indepSetFinset_card_forwardGraph_eq_increasing
    (D : V → V → Prop) (π : Equiv.Perm V) (k : ℕ) :
    ((forwardGraph D π).indepSetFinset k).card =
      (increasingForwardFinset D π k).card := by
  classical
  let A := (forwardGraph D π).indepSetFinset k
  let B := increasingForwardFinset D π k
  apply Nat.le_antisymm
  · rw [← Finset.card_attach (s := A)]
    let f : {S // S ∈ A} → (Fin k → V) := fun S ↦
      orderedTuple π S.1 <| (SimpleGraph.mem_indepSetFinset_iff.mp S.2).card_eq
    exact Finset.card_le_card_of_injOn f (by
      intro S hS
      have hNS := SimpleGraph.mem_indepSetFinset_iff.mp S.2
      exact mem_increasingForwardFinset.mpr ⟨
        orderedTuple_forwardIndependent π S.1 hNS.card_eq hNS.isIndepSet,
        orderedTuple_strictMono_after π S.1 hNS.card_eq⟩) (by
      intro S hS T hT hST
      apply Subtype.ext
      apply Finset.coe_injective
      rw [← range_orderedTuple π S.1
            (SimpleGraph.mem_indepSetFinset_iff.mp S.2).card_eq,
        ← range_orderedTuple π T.1
            (SimpleGraph.mem_indepSetFinset_iff.mp T.2).card_eq]
      exact congrArg Set.range hST)
  · rw [← Finset.card_attach (s := B)]
    let g : {x // x ∈ B} → Finset V := fun x ↦ Finset.univ.image x.1
    exact Finset.card_le_card_of_injOn g (by
      intro x hx
      have hx' := mem_increasingForwardFinset.mp x.2
      exact SimpleGraph.mem_indepSetFinset_iff.mpr ⟨
        image_univ_independent hx'.1 hx'.2,
        image_univ_card_of_strictMono hx'.2⟩) (by
      intro x hx y hy hxy
      apply Subtype.ext
      exact increasing_tuple_eq_of_image_eq
        (mem_increasingForwardFinset.mp x.2).2
        (mem_increasingForwardFinset.mp y.2).2 hxy)


noncomputable def increasingPermFinset {k : ℕ} (x : Fin k → V) :
    Finset (Equiv.Perm V) := by
  classical
  exact Finset.univ.filter (fun π ↦ StrictMono (fun i ↦ π (x i)))

@[simp]
lemma mem_increasingPermFinset {k : ℕ} {x : Fin k → V}
    {π : Equiv.Perm V} :
    π ∈ increasingPermFinset x ↔ StrictMono (fun i ↦ π (x i)) := by
  classical
  simp [increasingPermFinset]





lemma increasingPermFinset_card_mul_factorial_le {k : ℕ}
    (x : Fin k → V) (hx : Function.Injective x) :
    (increasingPermFinset x).card * k.factorial ≤
      Fintype.card (Equiv.Perm V) := by
  classical
  let A : Finset (Equiv.Perm V) := increasingPermFinset x
  let e : Fin k ↪ V := ⟨x, hx⟩
  let twist : Equiv.Perm (Fin k) → Equiv.Perm V :=
    fun σ ↦ σ.viaFintypeEmbedding e
  let F : Equiv.Perm V × Equiv.Perm (Fin k) → Equiv.Perm V :=
    fun p ↦ (twist p.2).trans p.1
  have hF : Set.InjOn F
      (↑(A ×ˢ (Finset.univ : Finset (Equiv.Perm (Fin k)))) :
        Set (Equiv.Perm V × Equiv.Perm (Fin k))) := by
    rintro ⟨π, σ⟩ hp ⟨π', σ'⟩ hp' heq
    have hpA : π ∈ A := (Finset.mem_product.mp hp).1
    have hpA' : π' ∈ A := (Finset.mem_product.mp hp').1
    have hπ : StrictMono (fun i ↦ π (x i)) :=
      mem_increasingPermFinset.mp hpA
    have hπ' : StrictMono (fun i ↦ π' (x i)) :=
      mem_increasingPermFinset.mp hpA'
    have himage :
        Finset.univ.image (fun i ↦ π (x i)) =
          Finset.univ.image (fun i ↦ π' (x i)) := by
      ext v
      constructor
      · intro hv
        simp only [Finset.mem_image, Finset.mem_univ, true_and] at hv ⊢
        obtain ⟨i, rfl⟩ := hv
        refine ⟨σ' (σ.symm i), ?_⟩
        have happ := DFunLike.congr_fun heq (x (σ.symm i))
        dsimp only [F] at happ
        change π ((twist σ) (e (σ.symm i))) =
          π' ((twist σ') (e (σ.symm i))) at happ
        simp only [twist, Equiv.Perm.viaFintypeEmbedding_apply_image] at happ
        simpa [e] using happ.symm
      · intro hv
        simp only [Finset.mem_image, Finset.mem_univ, true_and] at hv ⊢
        obtain ⟨i, rfl⟩ := hv
        refine ⟨σ (σ'.symm i), ?_⟩
        have happ := DFunLike.congr_fun heq (x (σ'.symm i))
        dsimp only [F] at happ
        change π ((twist σ) (e (σ'.symm i))) =
          π' ((twist σ') (e (σ'.symm i))) at happ
        simp only [twist, Equiv.Perm.viaFintypeEmbedding_apply_image] at happ
        simpa [e] using happ
    have hordered : (fun i ↦ π (x i)) = (fun i ↦ π' (x i)) :=
      strictMono_eq_of_image_eq hπ hπ' himage
    have hσσ' : σ = σ' := by
      apply Equiv.ext
      intro i
      apply hπ.injective
      have happ := DFunLike.congr_fun heq (x i)
      dsimp only [F] at happ
      change π ((twist σ) (e i)) = π' ((twist σ') (e i)) at happ
      simp only [twist, Equiv.Perm.viaFintypeEmbedding_apply_image] at happ
      have hord := congrFun hordered (σ' i)
      exact happ.trans hord.symm
    subst σ'
    have hππ' : π = π' := by
      ext v
      have happ := DFunLike.congr_fun heq ((twist σ).symm v)
      simpa [F] using happ
    subst π'
    rfl
  calc
    (increasingPermFinset x).card * k.factorial =
        (A ×ˢ (Finset.univ : Finset (Equiv.Perm (Fin k)))).card := by
      rw [Finset.card_product, Finset.card_univ, Fintype.card_perm,
        Fintype.card_fin]
    _ ≤ (Finset.univ : Finset (Equiv.Perm V)).card :=
      Finset.card_le_card_of_injOn F (by simp) hF
    _ = Fintype.card (Equiv.Perm V) := Finset.card_univ



lemma sum_increasingForwardFinset_card (D : V → V → Prop) (k : ℕ) :
    (∑ π : Equiv.Perm V, (increasingForwardFinset D π k).card) =
      ∑ x ∈ forwardIndependentFinset D k, (increasingPermFinset x).card := by
  classical
  simp only [increasingForwardFinset, increasingPermFinset, Finset.card_filter]
  rw [Finset.sum_comm]



lemma sum_indepSetFinset_card_forwardGraph_mul_factorial_le
    (D : V → V → Prop) (k : ℕ) :
    (∑ π : Equiv.Perm V, ((forwardGraph D π).indepSetFinset k).card) *
        k.factorial ≤
      (forwardIndependentFinset D k).card *
        Fintype.card (Equiv.Perm V) := by
  classical
  rw [Finset.sum_congr rfl (fun π _ ↦
    indepSetFinset_card_forwardGraph_eq_increasing D π k)]
  rw [sum_increasingForwardFinset_card D k, Finset.sum_mul]
  calc
    ∑ x ∈ forwardIndependentFinset D k,
        (increasingPermFinset x).card * k.factorial ≤
        ∑ _x ∈ forwardIndependentFinset D k,
          Fintype.card (Equiv.Perm V) := by
      apply Finset.sum_le_sum
      intro x hx
      by_cases hinj : Function.Injective x
      · exact increasingPermFinset_card_mul_factorial_le x hinj
      · have hempty : increasingPermFinset x = ∅ := by
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro π hπ
          apply hinj
          intro i j hij
          apply (mem_increasingPermFinset.mp hπ).injective
          exact congrArg π hij
        simp [hempty]
    _ = (forwardIndependentFinset D k).card *
          Fintype.card (Equiv.Perm V) := by simp





theorem exists_forwardGraph_factorial_bound
    (D : V → V → Prop) (k : ℕ) :
    ∃ π : Equiv.Perm V,
      ((forwardGraph D π).indepSetFinset k).card * k.factorial ≤
        (forwardIndependentFinset D k).card := by
  classical
  by_contra! hbad
  have hstrict :
      (∑ _π : Equiv.Perm V, (forwardIndependentFinset D k).card) <
        ∑ π : Equiv.Perm V,
          ((forwardGraph D π).indepSetFinset k).card * k.factorial := by
    apply Finset.sum_lt_sum_of_nonempty (by simp)
    intro π hπ
    exact hbad π
  have htotal := sum_indepSetFinset_card_forwardGraph_mul_factorial_le D k
  rw [Finset.sum_mul] at htotal
  have :
      (∑ π : Equiv.Perm V,
          ((forwardGraph D π).indepSetFinset k).card * k.factorial) ≤
        ∑ _π : Equiv.Perm V, (forwardIndependentFinset D k).card := by
    simpa [Nat.mul_comm] using htotal
  exact (not_lt_of_ge this) hstrict



theorem exists_cliqueFree_forwardGraph_factorial_bound
    {D : V → V → Prop} {s : ℕ} (hD : TransitiveTournamentFree D s)
    (k : ℕ) :
    ∃ π : Equiv.Perm V, (forwardGraph D π).CliqueFree s ∧
      ((forwardGraph D π).indepSetFinset k).card * k.factorial ≤
        (forwardIndependentFinset D k).card := by
  obtain ⟨π, hπ⟩ := exists_forwardGraph_factorial_bound D k
  exact ⟨π, forwardGraph_cliqueFree hD π, hπ⟩

end

end Erdos920
















open scoped BigOperators

namespace Erdos920

open Erdos202.ParkPham

noncomputable section

variable {V : Type*}



lemma exists_ge_of_bernoulli_average_ge (X : Finset V) {p a : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (F : Finset V → ℝ)
    (havg : a ≤ ∑ W ∈ X.powerset, bernoulliMass X W p * F W) :
    ∃ W ∈ X.powerset, a ≤ F W := by
  by_contra hnone
  push Not at hnone
  have hsum_lt :
      (∑ W ∈ X.powerset, bernoulliMass X W p * F W) <
        ∑ W ∈ X.powerset, bernoulliMass X W p * a := by
    apply Finset.sum_lt_sum
    · intro W hW
      exact mul_le_mul_of_nonneg_left (le_of_lt (hnone W hW))
        (bernoulliMass_nonneg hp0 hp1)
    · have hone : (1 : ℝ) = ∑ W ∈ X.powerset, bernoulliMass X W p := by
        symm
        exact sum_bernoulliMass_eq_one X (by ring)
      have hposmass : ∃ W ∈ X.powerset, 0 < bernoulliMass X W p := by
        by_contra hz
        push Not at hz
        have hallzero : ∀ W ∈ X.powerset, bernoulliMass X W p = 0 := by
          intro W hW
          exact le_antisymm (hz W hW) (bernoulliMass_nonneg hp0 hp1)
        have : (1 : ℝ) = 0 := by
          calc
            (1 : ℝ) = ∑ W ∈ X.powerset, bernoulliMass X W p := hone
            _ = 0 := by
              apply Finset.sum_eq_zero
              intro W hW
              exact hallzero W hW
        norm_num at this
      rcases hposmass with ⟨W, hW, hmass⟩
      refine ⟨W, hW, ?_⟩
      exact mul_lt_mul_of_pos_left (hnone W hW) hmass
  have hconst :
      (∑ W ∈ X.powerset, bernoulliMass X W p * a) = a := by
    rw [← Finset.sum_mul, sum_bernoulliMass_eq_one X (by ring), one_mul]
  linarith

variable [Fintype V] [DecidableEq V]



lemma card_indepSetFinset_induce_le_surviving
    (G : SimpleGraph V) [DecidableRel G.Adj] (W : Finset V) (m : ℕ) :
    ((G.induce (W : Set V)).indepSetFinset m).card ≤
      ((G.indepSetFinset m).filter (fun T => T ⊆ W)).card := by
  classical
  let e : {x // x ∈ (W : Set V)} ↪ V := ⟨Subtype.val, Subtype.val_injective⟩
  let f : Finset {x // x ∈ (W : Set V)} → Finset V := fun T => T.map e
  apply Finset.card_le_card_of_injOn f
  · intro T hT
    have hTi : (G.induce (W : Set V)).IsNIndepSet m T :=
      SimpleGraph.mem_indepSetFinset_iff.mp hT
    have hmap : G.IsNIndepSet m (f T) := by
      have hTi' :
          (((⊤ : SimpleGraph.Subgraph G).induce (W : Set V)).coe).IsNIndepSet m T := by
        rw [← SimpleGraph.induce_eq_coe_induce_top]
        exact hTi
      simpa [f, e] using
        (SimpleGraph.isNIndepSet_induce (G := G) (F := (W : Set V))
          (s := T) (n := m)).mp hTi'
    have hsub : f T ⊆ W := by
      intro v hv
      rcases Finset.mem_map.mp hv with ⟨x, hx, rfl⟩
      exact x.property
    exact Finset.mem_filter.mpr
      ⟨SimpleGraph.mem_indepSetFinset_iff.mpr hmap, hsub⟩
  · exact (Finset.mapEmbedding e).injective.injOn



lemma card_lt_ramseyNumber_of_cliqueFree_indepSetFree
    {U : Type*} [Fintype U] (G : SimpleGraph U) {s m : ℕ}
    (hcf : G.CliqueFree s) (hif : G.IndepSetFree m) :
    Fintype.card U < Ramsey.ramseyNumber s m := by
  by_contra hn
  have hR : Ramsey.ramseyNumber s m ≤ Fintype.card U := Nat.le_of_not_gt hn
  have hprop : Ramsey.RamseyProperty s m (Fintype.card U) :=
    Ramsey.ramseyProperty_of_ramseyNumber_le hR
  exact Ramsey.ramseyProperty_of_card rfl hprop G ⟨hcf, hif⟩






theorem sampling_deletion_ramsey_lt
    (G : SimpleGraph V) [DecidableRel G.Adj] {s m : ℕ}
    (hm : 1 ≤ m) (hcf : G.CliqueFree s) {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hcount : p ^ m * (G.indepSetFinset m).card ≤ 1) :
    p * Fintype.card V - 1 < (Ramsey.ramseyNumber s m : ℝ) := by
  classical
  let X : Finset V := Finset.univ
  let A : Finset (Finset V) := G.indepSetFinset m
  let Y : Finset V → ℝ := fun W =>
    (W.card : ℝ) - ((A.filter (fun T => T ⊆ W)).card : ℝ)
  have hAX : ∀ T ∈ A, T ⊆ X := by
    intro T hT
    exact Finset.subset_univ T
  have hAcard : ∀ T ∈ A, T.card = m := by
    intro T hT
    exact (SimpleGraph.mem_indepSetFinset_iff.mp hT).card_eq
  have havg_eq :
      (∑ W ∈ X.powerset, bernoulliMass X W p * Y W) =
        p * Fintype.card V - p ^ m * A.card := by
    rw [show (∑ W ∈ X.powerset, bernoulliMass X W p * Y W) =
        (∑ W ∈ X.powerset, bernoulliMass X W p * (W.card : ℝ)) -
        ∑ W ∈ X.powerset,
          bernoulliMass X W p * ((A.filter (fun T => T ⊆ W)).card : ℝ) by
      simp only [Y, mul_sub, Finset.sum_sub_distrib]]
    rw [sum_bernoulliMass_card X hp0 hp1,
      sum_bernoulliMass_contained_count X A hAX hAcard hp0 hp1]
    simp [X]
  have havg :
      p * Fintype.card V - 1 ≤
        ∑ W ∈ X.powerset, bernoulliMass X W p * Y W := by
    rw [havg_eq]
    have : p ^ m * A.card ≤ 1 := by simpa [A] using hcount
    linarith
  obtain ⟨W, hWX, hWY⟩ :=
    exists_ge_of_bernoulli_average_ge X hp0 hp1 Y havg
  let GW : SimpleGraph {x // x ∈ (W : Set V)} := G.induce (W : Set V)
  have hGWcf : GW.CliqueFree s :=
    hcf.comap (SimpleGraph.Embedding.induce (G := G) (s := (W : Set V))).isContained
  obtain ⟨U, hUcard, hUfree⟩ :=
    exists_induced_indepSetFree_subgraph (G := GW) hm
  let GU : SimpleGraph {x // x ∈ (U : Set {x // x ∈ (W : Set V)})} :=
    GW.induce (U : Set {x // x ∈ (W : Set V)})
  have hGUcf : GU.CliqueFree s :=
    hGWcf.comap (SimpleGraph.Embedding.induce (G := GW)
      (s := (U : Set {x // x ∈ (W : Set V)}))).isContained
  have hUramsey : U.card < Ramsey.ramseyNumber s m := by
    have hcardU : Fintype.card {x // x ∈ (U : Set {x // x ∈ (W : Set V)})} = U.card := by
      simp
    rw [← hcardU]
    exact card_lt_ramseyNumber_of_cliqueFree_indepSetFree GU hGUcf hUfree
  have hinduce_le : (GW.indepSetFinset m).card ≤
      (A.filter (fun T => T ⊆ W)).card := by
    simpa [GW, A] using card_indepSetFinset_induce_le_surviving G W m
  have hnat : W.card - (A.filter (fun T => T ⊆ W)).card ≤ U.card := by
    have hUcard' : W.card - (GW.indepSetFinset m).card ≤ U.card := by
      simpa using hUcard
    exact (Nat.sub_le_sub_left hinduce_le W.card).trans hUcard'
  have hreal : Y W ≤ (U.card : ℝ) := by
    by_cases hsurv_le : (A.filter (fun T => T ⊆ W)).card ≤ W.card
    · rw [show Y W =
          ((W.card - (A.filter (fun T => T ⊆ W)).card : ℕ) : ℝ) by
        simp only [Y]
        exact (Nat.cast_sub hsurv_le).symm]
      exact_mod_cast hnat
    · have hYnonpos : Y W ≤ 0 := by
        simp only [Y]
        exact sub_nonpos.mpr (by exact_mod_cast (Nat.le_of_not_ge hsurv_le))
      exact hYnonpos.trans (Nat.cast_nonneg U.card)
  exact lt_of_le_of_lt (hWY.trans hreal) (by exact_mod_cast hUramsey)

end

end Erdos920





















open scoped BigOperators

namespace Erdos920

noncomputable section

open RamseyPackaging


lemma factorial_lower_bound (m : ℕ) :
    ((m : ℝ) / Real.exp 1) ^ m ≤ (m.factorial : ℝ) := by
  field_simp
  rw [div_pow, div_le_iff₀ (by positivity)]
  rw [← div_le_iff₀' (by positivity)]
  rw [← Real.exp_nat_mul, mul_comm, Real.exp_eq_exp_ℝ]
  rw [NormedSpace.exp_eq_tsum_div]
  exact
    (Summable.le_tsum
      (show Summable _ from Real.summable_pow_div_factorial _)
      m (fun _ _ ↦ by positivity)).trans (by norm_num)




lemma sampling_count_le_one_of_factorial_bound
    {m I F : ℕ} {B : ℝ} (hB : 0 < B)
    (horder : I * m.factorial ≤ F) (hforward : (F : ℝ) ≤ B ^ m) :
    ((m : ℝ) / (Real.exp 1 * B)) ^ m * (I : ℝ) ≤ 1 := by
  have hI : 0 ≤ (I : ℝ) := Nat.cast_nonneg I
  have hfactorial := factorial_lower_bound m
  have hcleared :
      (I : ℝ) * ((m : ℝ) / Real.exp 1) ^ m ≤ B ^ m := by
    calc
      (I : ℝ) * ((m : ℝ) / Real.exp 1) ^ m ≤
          (I : ℝ) * (m.factorial : ℝ) :=
        mul_le_mul_of_nonneg_left hfactorial hI
      _ ≤ (F : ℝ) := by exact_mod_cast horder
      _ ≤ B ^ m := hforward
  have hBpow : 0 < B ^ m := pow_pos hB _
  calc
    ((m : ℝ) / (Real.exp 1 * B)) ^ m * (I : ℝ) =
        ((I : ℝ) * ((m : ℝ) / Real.exp 1) ^ m) / B ^ m := by
      rw [div_pow, mul_pow, div_pow]
      field_simp [hB.ne']
    _ ≤ B ^ m / B ^ m := div_le_div_of_nonneg_right hcleared hBpow.le
    _ = 1 := div_self hBpow.ne'

namespace RamseyPackaging.DStarWitness









theorem hasAveragingSamplingConclusion_of_sideConditions
    {t m q : ℕ} {C : ℝ} (W : DStarWitness t m q C)
    (hm : 1 ≤ m) (hq : 1 ≤ q) (hC : 0 < C)
    (hside : W.SamplingSideConditions) :
    W.HasAveragingSamplingConclusion := by
  classical
  let : Fintype W.V := W.fintypeV
  let : LinearOrder W.V := LinearOrder.lift' (Fintype.equivFin W.V)
    (Fintype.equivFin W.V).injective
  let D : W.V → W.V → Prop := W.D.arc
  have htfree : TransitiveTournamentFree D (t + 1) := by
    intro v hv htv
    apply W.transitiveTournamentFree
    refine ⟨v, hv, ?_⟩
    intro i j hij
    exact htv hij
  obtain ⟨π, hclique, horder⟩ :=
    exists_cliqueFree_forwardGraph_factorial_bound (D := D) htfree m
  have hcount_eq :
      (forwardIndependentFinset D m).card =
        @Digraph.forwardIndependentTupleCount W.V W.fintypeV W.D m := by
    simp only [forwardIndependentFinset, Digraph.forwardIndependentTupleCount,
      Finset.card_filter, D]
    apply Finset.sum_congr rfl
    intro v hv
    congr 1
  let B : ℝ := C * (q : ℝ) ^ t
  have hB : 0 < B := by
    exact mul_pos hC (pow_pos (by exact_mod_cast (show 0 < q by omega)) _)
  have hforward : ((forwardIndependentFinset D m).card : ℝ) ≤ B ^ m := by
    rw [hcount_eq]
    exact W.forward_bound
  have hcount :
      W.samplingDensity ^ m *
          ((forwardGraph D π).indepSetFinset m).card ≤ 1 := by
    have h := sampling_count_le_one_of_factorial_bound hB horder hforward
    simpa [RamseyPackaging.DStarWitness.samplingDensity, B, mul_assoc] using h
  have hsamp := sampling_deletion_ramsey_lt
    (G := forwardGraph D π) hm hclique hside.1.le hside.2 hcount
  simpa [HasAveragingSamplingConclusion] using hsamp

end RamseyPackaging.DStarWitness

end

end Erdos920




















namespace Erdos920.Construction

open Erdos920.ProjectiveDStar
open Erdos920.RamseyPackaging

noncomputable section







def HasConcreteBuild (u m q : ℕ) (C : ℝ) (hq : q.Prime) : Prop :=
  letI : Fact q.Prime := ⟨hq⟩
  ∃ hforward :
      ((@Digraph.forwardIndependentTupleCount
          (ProjectiveDStar.Vertex q (u + 1))
          (ProjectiveDStar.vertexFintype q (u + 1))
          (ProjectiveDStar.digraph q (u + 1)) m : ℕ) : ℝ) ≤
        (C * (q : ℝ) ^ (u + 1)) ^ m,
    let W := ConcreteWitness.ofForwardBound q (u + 1) m C (by omega) hforward
    W.SamplingSideConditions ∧ W.HasAveragingSamplingConclusion








structure ProjectiveBuildTheorem (u : ℕ) where
  C : ℝ
  C_pos : 0 < C
  qThreshold : ℕ
  build : ∀ (m q : ℕ), (hq : q.Prime) → qThreshold ≤ q →
    2 ≤ q → q ≤ m →
    (m : ℝ) / (8 * C * Real.log (m : ℝ) ^ 2) ≤ (q : ℝ) →
    C * (q : ℝ) * Real.log (q : ℝ) ^ 2 ≤ (m : ℝ) →
      HasConcreteBuild u m q C hq








def projectiveBuildTheoremOfForwardBound (u : ℕ) (hu : 1 ≤ u)
    (C : ℝ) (hC : 0 < C) (Qforward : ℕ)
    (hforward : ∀ (q m : ℕ), (hq : q.Prime) → Qforward ≤ q →
      C * (q : ℝ) * Real.log (q : ℝ) ^ 2 ≤ (m : ℝ) →
      letI : Fact q.Prime := ⟨hq⟩
      ((@Digraph.forwardIndependentTupleCount
          (ProjectiveDStar.Vertex q (u + 1))
          (ProjectiveDStar.vertexFintype q (u + 1))
          (ProjectiveDStar.digraph q (u + 1)) m : ℕ) : ℝ) ≤
        (C * (q : ℝ) ^ (u + 1)) ^ m) :
    ProjectiveBuildTheorem u := by
  let Qdensity := Classical.choose
    (DensitySide.exists_threshold_sampling_density C hC u hu)
  have hdensity := Classical.choose_spec
    (DensitySide.exists_threshold_sampling_density C hC u hu)
  refine
    { C := C
      C_pos := hC
      qThreshold := max Qforward Qdensity
      build := ?_ }
  intro m q hq hqThreshold hq2 hqm hscale hbudget
  let : Fact q.Prime := ⟨hq⟩
  have hqForward : Qforward ≤ q :=
    (Nat.le_max_left Qforward Qdensity).trans hqThreshold
  have hqDensity : Qdensity ≤ q :=
    (Nat.le_max_right Qforward Qdensity).trans hqThreshold
  have htuple := hforward q m hq hqForward hbudget
  refine ⟨htuple, ?_⟩
  let W := ConcreteWitness.ofForwardBound q (u + 1) m C (by omega) htuple
  have hside : W.SamplingSideConditions := by
    exact hdensity m q hqDensity hqm hscale
  refine ⟨hside, ?_⟩
  exact W.hasAveragingSamplingConclusion_of_sideConditions
    (by omega) (by omega) hC hside



def projectiveBuildTheorem (u : ℕ) (hu : 1 ≤ u) :
    ProjectiveBuildTheorem u := by
  let E := ForwardBound.exists_forwardConstant (u + 1) (by omega)
  let C := Classical.choose E
  have hC_and := Classical.choose_spec E
  let Q := Classical.choose hC_and.2
  have hforward := Classical.choose_spec hC_and.2
  exact projectiveBuildTheoremOfForwardBound u hu C hC_and.1 Q hforward



def projectiveDStarConstruction (u : ℕ) (_hu : 1 ≤ u)
    (B : ProjectiveBuildTheorem u) : DStarConstruction u where
  C := B.C
  C_pos := B.C_pos
  qThreshold := B.qThreshold
  build := by
    intro m q hq hqThreshold hq2 hqm hscale hbudget
    let _ : Fact q.Prime := ⟨hq⟩
    rcases B.build m q hq hqThreshold hq2 hqm hscale hbudget with
      ⟨hforward, hside, haverage⟩
    exact ⟨ConcreteWitness.ofForwardBound q (u + 1) m B.C (by omega) hforward,
      hside, haverage⟩






def dStarFamilyOfBuild (u : ℕ) (hu : 1 ≤ u) (B : ProjectiveBuildTheorem u) :
    DStarFamily u :=
  (projectiveDStarConstruction u hu B).toFamily



def dStarFamily (u : ℕ) (hu : 1 ≤ u) : DStarFamily u :=
  dStarFamilyOfBuild u hu (projectiveBuildTheorem u hu)

@[simp] theorem dStarFamilyOfBuild_C (u : ℕ) (hu : 1 ≤ u)
    (B : ProjectiveBuildTheorem u) :
    (dStarFamilyOfBuild u hu B).C = B.C := rfl

@[simp] theorem dStarFamilyOfBuild_κ (u : ℕ) (hu : 1 ≤ u)
    (B : ProjectiveBuildTheorem u) :
    (dStarFamilyOfBuild u hu B).κ = 1 / (8 * B.C) := rfl


theorem bradacRamseyLowerBoundOfBuild (u : ℕ) (hu : 1 ≤ u)
    (B : ProjectiveBuildTheorem u) :
    ∃ A : ℝ, 0 < A ∧
      ∀ᶠ m : ℕ in Filter.atTop,
        A * (m : ℝ) ^ (u + 1) / Real.log (m : ℝ) ^ (2 * u) ≤
          (Ramsey.ramseyNumber (u + 2) m : ℝ) :=
  bradac_ramsey_lower_bound_eventually_of_dStarFamily u
    (dStarFamilyOfBuild u hu B)

end

end Erdos920.Construction


namespace Erdos920OMATransport

open Filter

/-- Clique/free formulation of the classical Ramsey property. -/
def IsGraphRamseyOMA (n k l : ℕ) : Prop :=
  ∀ G : SimpleGraph (Fin n), ¬ (G.CliqueFree k ∧ (Gᶜ).CliqueFree l)

lemma classicalRamsey_eq_sInf_oma (k l : ℕ) :
    SimpleGraph.classicalRamsey k l = sInf {n : ℕ | IsGraphRamseyOMA n k l} := by
  classical
  simp only [SimpleGraph.classicalRamsey, SimpleGraph.graphRamsey,
    IsGraphRamseyOMA, not_and_or, SimpleGraph.not_cliqueFree_iff_top_isContained]

lemma ramseyNumber_le_of_ramseyProperty {k l n : ℕ}
    (h : Ramsey.RamseyProperty k l n) : Ramsey.ramseyNumber k l ≤ n := by
  classical
  unfold Ramsey.ramseyNumber
  exact Nat.find_le h

lemma ramseyNumber_le_classicalRamsey (k l : ℕ) :
    Ramsey.ramseyNumber k l ≤ SimpleGraph.classicalRamsey k l := by
  classical
  rcases Ramsey.ramseyProperty_exists k l with ⟨n, hn⟩
  have hnI : IsGraphRamseyOMA n k l := by
    intro G hbad
    exact hn G ⟨hbad.1, (SimpleGraph.cliqueFree_compl (G := G) (n := l)).mp hbad.2⟩
  have hne : {n : ℕ | IsGraphRamseyOMA n k l}.Nonempty := ⟨n, hnI⟩
  have hmem := Nat.sInf_mem hne
  rw [← classicalRamsey_eq_sInf_oma k l] at hmem
  have hprop : Ramsey.RamseyProperty k l (SimpleGraph.classicalRamsey k l) := by
    intro G hbad
    exact hmem G ⟨hbad.1, (SimpleGraph.cliqueFree_compl (G := G) (n := l)).mpr hbad.2⟩
  exact ramseyNumber_le_of_ramseyProperty hprop

theorem external_ramsey_lower_bound_k4 :
    ∃ A : ℝ, 0 < A ∧
      ∀ᶠ m : ℕ in Filter.atTop,
        A * (m : ℝ) ^ 3 / Real.log (m : ℝ) ^ 4 ≤
          (Ramsey.ramseyNumber 4 m : ℝ) := by
  simpa using
    (Erdos920.Construction.bradacRamseyLowerBoundOfBuild 2 (by norm_num)
      (Erdos920.Construction.projectiveBuildTheorem 2 (by norm_num)))

theorem oma_ramsey_lower_bound_k4 :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ m : ℕ in Filter.atTop,
      (SimpleGraph.classicalRamsey 4 m : ℝ) ≥
        C * (m : ℝ) ^ 3 / Real.log (m : ℝ) ^ 4 := by
  rcases external_ramsey_lower_bound_k4 with ⟨A, hA, hev⟩
  refine ⟨A, hA, ?_⟩
  filter_upwards [hev] with m hm
  exact hm.trans (by exact_mod_cast ramseyNumber_le_classicalRamsey 4 m)

end Erdos920OMATransport

theorem OMA.solution : OMA.R_Erdos920_erdos_920_variants_lower_bound_k_eq_4_R1.H1 := by
  unfold OMA.R_Erdos920_erdos_920_variants_lower_bound_k_eq_4_R1.H1
  exact Erdos920OMATransport.oma_ramsey_lower_bound_k4
