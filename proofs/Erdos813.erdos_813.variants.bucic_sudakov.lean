import FormalConjectures.ErdosProblems.«813»

/-!
# Erdos Problem 813 - Bucic-Sudakov Lower Bound

Complete proof of `Erdos813.erdos_813.variants.bucic_sudakov`: for every $\varepsilon > 0$,
eventually $n^{5/12 - \varepsilon} \le h(n)$. The proof translates `EverySevenHasTriangle`
to the complement graph $G$ and follows Section 2.2 of Bucic and Sudakov (arXiv:2007.03667).
-/

open Asymptotics Finset
open scoped Topology

namespace E813BuSu

noncomputable section

section Helpers

variable {V : Type*} [DecidableEq V] [Fintype V]

private def neighbors (G : SimpleGraph V) (S : Finset V) (v : V) : Finset V := by
  classical
  exact S.filter (G.Adj v)

omit [DecidableEq V] [Fintype V] in
private lemma mem_neighbors {G : SimpleGraph V} {S : Finset V} {v w : V} :
    w ∈ neighbors G S v ↔ w ∈ S ∧ G.Adj v w := by
  classical
  simp [neighbors]

omit [DecidableEq V] [Fintype V] in
private lemma neighbors_subset {G : SimpleGraph V} {S : Finset V} {v : V} :
    neighbors G S v ⊆ S := by
  intro w hw
  exact (mem_neighbors.mp hw).1

omit [DecidableEq V] [Fintype V] in
private lemma neighbors_mono {G : SimpleGraph V} {S T : Finset V} (hST : S ⊆ T) (v : V) :
    neighbors G S v ⊆ neighbors G T v := by
  intro w hw
  obtain ⟨hwS, hadj⟩ := mem_neighbors.mp hw
  exact mem_neighbors.mpr ⟨hST hwS, hadj⟩

private def near (G : SimpleGraph V) (S A : Finset V) : Finset V :=
  A.biUnion (neighbors G S)

omit [Fintype V] in
private lemma mem_near {G : SimpleGraph V} {S A : Finset V} {w : V} :
    w ∈ near G S A ↔ w ∈ S ∧ ∃ v ∈ A, G.Adj v w := by
  simp only [near, mem_biUnion, mem_neighbors]
  aesop

private def edgesIn (G : SimpleGraph V) (S : Finset V) : Finset (Finset V) := by
  classical
  exact (S.powersetCard 2).filter (fun e => G.IsClique (e : Set V))

omit [Fintype V] in
private lemma mem_edgesIn {G : SimpleGraph V} {S e : Finset V} :
    e ∈ edgesIn G S ↔ e ⊆ S ∧ e.card = 2 ∧ G.IsClique (e : Set V) := by
  classical
  simp [edgesIn, mem_powersetCard, and_assoc]

omit [Fintype V] in
private lemma edgesIn_mono {G : SimpleGraph V} {S T : Finset V} (hST : S ⊆ T) :
    edgesIn G S ⊆ edgesIn G T := by
  intro e he
  obtain ⟨heS, hc, hcl⟩ := mem_edgesIn.mp he
  exact mem_edgesIn.mpr ⟨heS.trans hST, hc, hcl⟩

private def TriangleFree (G : SimpleGraph V) (S : Finset V) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, G.Adj x y → G.Adj y z → ¬ G.Adj x z

omit [DecidableEq V] [Fintype V] in
private lemma triangleFree_subset {G : SimpleGraph V} {S T : Finset V}
    (hT : TriangleFree G T) (hST : S ⊆ T) : TriangleFree G S :=
  fun x hx y hy z hz => hT x (hST hx) y (hST hy) z (hST hz)

omit [DecidableEq V] [Fintype V] in
private lemma triangleFree_neighbors_indep {G : SimpleGraph V} {S : Finset V}
    (hTF : TriangleFree G S) {v : V} (hv : v ∈ S) :
    G.IsIndepSet (neighbors G S v : Set V) := by
  rw [G.isIndepSet_iff]
  intro x hx y hy _ hadj
  obtain ⟨hxS, hvx⟩ := mem_neighbors.mp hx
  obtain ⟨hyS, hvy⟩ := mem_neighbors.mp hy
  exact hTF v hv x hxS y hyS hvx hadj hvy

omit [DecidableEq V] [Fintype V] in
private lemma indep_mono {G : SimpleGraph V} {S T : Finset V} (hST : S ⊆ T)
    (hT : G.IsIndepSet (T : Set V)) : G.IsIndepSet (S : Set V) := by
  rw [G.isIndepSet_iff] at hT ⊢
  intro a ha b hb hab
  exact hT (hST ha) (hST hb) hab

omit [DecidableEq V] [Fintype V] in
private lemma max_subset (S : Finset V) (P : Finset V → Prop) (h : P ∅) :
    ∃ A ⊆ S, P A ∧ ∀ B ⊆ S, P B → B.card ≤ A.card := by
  classical
  obtain ⟨A, hA, hmax⟩ := (S.powerset.filter P).exists_max_image card ⟨∅, by simp [h]⟩
  rw [mem_filter, mem_powerset] at hA
  exact ⟨A, hA.1, hA.2, fun B hBS hB => hmax B (by simp [hBS, hB])⟩

omit [Fintype V] in
private lemma card_erase_ge_sub_one {α : Type*} [DecidableEq α] (s : Finset α) (a : α) :
    s.card - 1 ≤ (s.erase a).card := by
  by_cases h : a ∈ s
  · rw [card_erase_of_mem h]
  · rw [erase_eq_self.mpr h]; omega

omit [Fintype V] in
private lemma cover_bound (G : SimpleGraph V) (S : Finset V) (a D : ℝ)
    (ha : ∀ I ⊆ S, G.IsIndepSet (I : Set V) → (I.card : ℝ) ≤ a)
    (hD : 0 ≤ D)
    (hdeg : ∀ v ∈ S, ((neighbors G S v).card : ℝ) ≤ D) :
    (S.card : ℝ) ≤ a * (D + 1) := by
  obtain ⟨A, hAS, hA, hmax⟩ := max_subset S (fun s => G.IsIndepSet (s : Set V)) (by simp)
  have hcover : S ⊆ A ∪ near G S A := by
    intro v hv
    by_contra hh
    have hvA : v ∉ A := fun hin => hh (mem_union_left _ hin)
    have hn : ∀ u ∈ A, ¬ G.Adj u v := fun u hu hadj =>
      hh (mem_union_right _ (mem_near.mpr ⟨hv, u, hu, hadj⟩))
    have hi : G.IsIndepSet (↑(insert v A) : Set V) := by
      rw [G.isIndepSet_iff]
      intro u hu w hw huw
      simp only [coe_insert, Set.mem_insert_iff, mem_coe] at hu hw
      rcases hu with rfl | hu <;> rcases hw with rfl | hw
      · exact False.elim (huw rfl)
      · exact fun hadj => hn w hw hadj.symm
      · exact hn u hu
      · exact (G.isIndepSet_iff.mp hA) hu hw huw
    have hm := hmax _ (insert_subset hv hAS) hi
    rw [card_insert_of_notMem hvA] at hm
    omega
  have hu := card_le_card hcover
  have hc := (card_union_le A (near G S A)).trans
    (Nat.add_le_add_left (card_biUnion_le (s := A) (t := neighbors G S)) _)
  have hh : (S.card : ℝ) ≤ A.card + ∑ v ∈ A, ((neighbors G S v).card : ℝ) := by
    exact_mod_cast hu.trans hc
  have hAa : (A.card : ℝ) ≤ a := ha A hAS hA
  have ha0 : 0 ≤ a := le_trans (by positivity) hAa
  calc
    (S.card : ℝ) ≤ A.card + ∑ v ∈ A, ((neighbors G S v).card : ℝ) := hh
    _ ≤ A.card + ∑ _v ∈ A, D := add_le_add le_rfl (sum_le_sum fun v hv => hdeg v (hAS hv))
    _ = (A.card : ℝ) * (D + 1) := by simp; ring
    _ ≤ a * (D + 1) := mul_le_mul_of_nonneg_right hAa (by positivity)

omit [Fintype V] in
private lemma card_triangle_free_subset (G : SimpleGraph V) (S : Finset V)
    (hTF : TriangleFree G S) :
    ∃ I ⊆ S, G.IsIndepSet (I : Set V) ∧ S.card ≤ 2 * I.card ^ 2 := by
  obtain ⟨I, hIS, hI, hmax⟩ := max_subset S (fun s => G.IsIndepSet (s : Set V)) (by simp)
  have hcover : S ⊆ I ∪ near G S I := by
    intro v hv
    by_contra hh
    have hvI : v ∉ I := fun hin => hh (mem_union_left _ hin)
    have hn : ∀ u ∈ I, ¬ G.Adj u v := fun u hu hadj =>
      hh (mem_union_right _ (mem_near.mpr ⟨hv, u, hu, hadj⟩))
    have hi : G.IsIndepSet (↑(insert v I) : Set V) := by
      rw [G.isIndepSet_iff]
      intro u hu w hw huw
      simp only [coe_insert, Set.mem_insert_iff, mem_coe] at hu hw
      rcases hu with rfl | hu <;> rcases hw with rfl | hw
      · exact False.elim (huw rfl)
      · exact fun hadj => hn w hw hadj.symm
      · exact hn u hu
      · exact (G.isIndepSet_iff.mp hI) hu hw huw
    have hm := hmax _ (insert_subset hv hIS) hi
    rw [card_insert_of_notMem hvI] at hm
    omega
  have h1 : S.card ≤ I.card + ∑ v ∈ I, (neighbors G S v).card :=
    (card_le_card hcover).trans ((card_union_le I (near G S I)).trans
      (Nat.add_le_add_left (card_biUnion_le (s := I) (t := neighbors G S)) _))
  have h2 : ∑ v ∈ I, (neighbors G S v).card ≤ I.card * I.card := by
    calc
      ∑ v ∈ I, (neighbors G S v).card ≤ ∑ _v ∈ I, I.card :=
        sum_le_sum fun v hv => hmax _ neighbors_subset (triangleFree_neighbors_indep hTF (hIS hv))
      _ = I.card * I.card := by simp
  have h3 : I.card + I.card * I.card ≤ 2 * I.card ^ 2 := by
    rcases Nat.eq_zero_or_pos I.card with h0 | hpos
    · simp [h0]
    · nlinarith
  exact ⟨I, hIS, hI, h1.trans ((Nat.add_le_add_left h2 _).trans h3)⟩

omit [Fintype V] in
private lemma handshaking_edgesIn (G : SimpleGraph V) (S : Finset V) :
    2 * (edgesIn G S).card = ∑ v ∈ S, (neighbors G S v).card := by
  classical
  have hL : 2 * (edgesIn G S).card =
      ∑ e ∈ edgesIn G S, ∑ v ∈ S, if v ∈ e then 1 else 0 := by
    have h1 : ∀ e ∈ edgesIn G S, (∑ v ∈ S, if v ∈ e then 1 else 0) = 2 := by
      intro e he
      obtain ⟨heS, hc, _⟩ := mem_edgesIn.mp he
      rw [sum_boole, Nat.cast_id]
      have hinter : S.filter (fun v => v ∈ e) = e := by
        ext v
        simp only [mem_filter]
        exact ⟨fun h => h.2, fun h => ⟨heS h, h⟩⟩
      rw [hinter, hc]
    rw [sum_congr rfl h1, sum_const, smul_eq_mul, mul_comm]
  have hR : ∑ v ∈ S, (neighbors G S v).card =
      ∑ v ∈ S, ∑ e ∈ edgesIn G S, if v ∈ e then 1 else 0 := by
    refine sum_congr rfl fun v hv => ?_
    rw [sum_boole, Nat.cast_id]
    refine card_bij (fun w _ => ({v, w} : Finset V)) ?_ ?_ ?_
    · intro w hw
      obtain ⟨hwS, hvw⟩ := mem_neighbors.mp hw
      have hne : v ≠ w := hvw.ne
      rw [mem_filter]
      refine ⟨mem_edgesIn.mpr ⟨?_, card_pair hne, ?_⟩, mem_insert_self v {w}⟩
      · intro z hz
        simp only [mem_insert, mem_singleton] at hz
        rcases hz with rfl | rfl <;> assumption
      · intro a ha b hb hab
        simp only [coe_insert, coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
        rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
        · exact False.elim (hab rfl)
        · exact hvw
        · exact hvw.symm
        · exact False.elim (hab rfl)
    · intro w₁ hw₁ w₂ hw₂ heq
      have hne₁ : v ≠ w₁ := (mem_neighbors.mp hw₁).2.ne
      have h1 : w₁ ∈ ({v, w₂} : Finset V) := heq ▸ (by simp)
      simp only [mem_insert, mem_singleton] at h1
      rcases h1 with rfl | rfl
      · exact False.elim (hne₁ rfl)
      · rfl
    · intro e he
      rw [mem_filter, mem_edgesIn] at he
      obtain ⟨⟨heS, hcard, hcl⟩, hve⟩ := he
      obtain ⟨a, b, hab, rfl⟩ := card_eq_two.mp hcard
      simp only [mem_insert, mem_singleton] at hve
      rcases hve with rfl | rfl
      · refine ⟨b, mem_neighbors.mpr ⟨heS (by simp), hcl (by simp) (by simp) hab⟩, rfl⟩
      · refine ⟨a, mem_neighbors.mpr ⟨heS (by simp), hcl (by simp) (by simp) hab.symm⟩, ?_⟩
        ext x
        simp only [mem_insert, mem_singleton]
        tauto
  rw [hL, hR, sum_comm]

omit [Fintype V] in
private lemma turan_indep (G : SimpleGraph V) :
    ∀ k : ℕ, 1 ≤ k → ∀ S : Finset V,
      (∀ I ⊆ S, G.IsIndepSet (I : Set V) → I.card ≤ k) →
      (S.card : ℝ) ^ 2 ≤ (k : ℝ) * ((S.card : ℝ) + ∑ v ∈ S, ((neighbors G S v).card : ℝ)) := by
  intro k hk
  induction k with
  | zero => omega
  | succ k ih =>
    intro S hS
    rcases eq_or_ne k 0 with rfl | hk0
    · by_cases hne : S.Nonempty
      · have hdeg : ∀ v ∈ S, (neighbors G S v).card = S.card - 1 := by
          intro v hv
          have heq : neighbors G S v = S.erase v := by
            ext w
            rw [mem_neighbors, mem_erase]
            constructor
            · rintro ⟨hwS, hvw⟩
              exact ⟨hvw.ne.symm, hwS⟩
            · rintro ⟨hwv, hwS⟩
              refine ⟨hwS, ?_⟩
              by_contra hnot
              have hind : G.IsIndepSet (↑({v, w} : Finset V) : Set V) := by
                rw [G.isIndepSet_iff]
                intro a ha b hb hab
                simp only [coe_insert, coe_singleton, Set.mem_insert_iff,
                  Set.mem_singleton_iff] at ha hb
                rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
                · exact False.elim (hab rfl)
                · exact hnot
                · exact fun hadj => hnot hadj.symm
                · exact False.elim (hab rfl)
              have hsub : ({v, w} : Finset V) ⊆ S := by
                intro z hz
                simp only [mem_insert, mem_singleton] at hz
                rcases hz with rfl | rfl <;> assumption
              have hle := hS _ hsub hind
              rw [card_pair hwv.symm] at hle
              omega
          rw [heq, card_erase_of_mem hv]
        have hsum : ∑ v ∈ S, ((neighbors G S v).card : ℝ) =
            (S.card : ℝ) * ((S.card : ℝ) - 1) := by
          have h1 : ∑ v ∈ S, ((neighbors G S v).card : ℝ) =
              ∑ _v ∈ S, ((S.card : ℝ) - 1) := by
            refine sum_congr rfl fun v hv => ?_
            rw [hdeg v hv, Nat.cast_sub (card_pos.mpr ⟨v, hv⟩)]
            norm_num
          rw [h1, sum_const, nsmul_eq_mul]
        rw [hsum]
        norm_num
        ring_nf
        exact le_rfl
      · rw [not_nonempty_iff_eq_empty.mp hne]
        simp
    · have hk1 : 1 ≤ k := Nat.pos_of_ne_zero hk0
      rcases S.eq_empty_or_nonempty with rfl | hne
      · simp
      obtain ⟨v, hvS, hvmin⟩ := S.exists_min_image (fun u => (neighbors G S u).card) hne
      let T : Finset V := insert v (neighbors G S v)
      let A : Finset V := S \ T
      have hTS : T ⊆ S := insert_subset hvS neighbors_subset
      have hAS : A ⊆ S := sdiff_subset
      have hdisj : Disjoint T A := disjoint_sdiff_self_right
      have hunion : T ∪ A = S := union_sdiff_of_subset hTS
      have hcardS : (S.card : ℝ) = (T.card : ℝ) + (A.card : ℝ) := by
        have hnat : S.card = T.card + A.card := by
          rw [← hunion, card_union_of_disjoint hdisj]
        exact_mod_cast hnat
      have hvnot : v ∉ neighbors G S v := fun h => G.loopless.irrefl v (mem_neighbors.mp h).2
      have hTcard : ((neighbors G S v).card : ℝ) = (T.card : ℝ) - 1 := by
        have hnat : T.card = (neighbors G S v).card + 1 := card_insert_of_notMem hvnot
        have : (T.card : ℝ) = ((neighbors G S v).card : ℝ) + 1 := by exact_mod_cast hnat
        linarith
      have hA_ind : ∀ I ⊆ A, G.IsIndepSet (I : Set V) → I.card ≤ k := by
        intro I hIA hI
        have hvI : v ∉ I := fun hv => (mem_sdiff.mp (hIA hv)).2 (mem_insert_self v _)
        have hI_ins : G.IsIndepSet (↑(insert v I) : Set V) := by
          rw [G.isIndepSet_iff]
          intro x hx y hy hxy
          simp only [coe_insert, Set.mem_insert_iff, mem_coe] at hx hy
          rcases hx with rfl | hx <;> rcases hy with rfl | hy
          · exact False.elim (hxy rfl)
          · intro hadj
            exact (mem_sdiff.mp (hIA hy)).2 (mem_insert_of_mem (mem_neighbors.mpr ⟨hAS (hIA hy), hadj⟩))
          · intro hadj
            exact (mem_sdiff.mp (hIA hx)).2 (mem_insert_of_mem (mem_neighbors.mpr ⟨hAS (hIA hx), hadj.symm⟩))
          · exact (G.isIndepSet_iff.mp hI) hx hy hxy
        have hle := hS (insert v I) (insert_subset hvS (hIA.trans hAS)) hI_ins
        rw [card_insert_of_notMem hvI] at hle
        omega
      have hIH := ih hk1 A hA_ind
      have hsumT : (T.card : ℝ) * ((T.card : ℝ) - 1) ≤
          ∑ w ∈ T, ((neighbors G S w).card : ℝ) := by
        rw [← hTcard]
        calc
          (T.card : ℝ) * ((neighbors G S v).card : ℝ)
            = ∑ _w ∈ T, ((neighbors G S v).card : ℝ) := by rw [sum_const, nsmul_eq_mul]
          _ ≤ ∑ w ∈ T, ((neighbors G S w).card : ℝ) :=
            sum_le_sum fun w hw => by exact_mod_cast hvmin w (hTS hw)
      have hsumA : ∑ w ∈ A, ((neighbors G A w).card : ℝ) ≤
          ∑ w ∈ A, ((neighbors G S w).card : ℝ) :=
        sum_le_sum fun w _ => by exact_mod_cast card_le_card (neighbors_mono hAS w)
      have hsumS : ∑ w ∈ S, ((neighbors G S w).card : ℝ) =
          ∑ w ∈ T, ((neighbors G S w).card : ℝ) + ∑ w ∈ A, ((neighbors G S w).card : ℝ) := by
        rw [← hunion, sum_union hdisj]
      have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk1
      have hcomb : (T.card : ℝ) ^ 2 + (A.card : ℝ) ^ 2 / (k : ℝ) ≤
          (S.card : ℝ) + ∑ w ∈ S, ((neighbors G S w).card : ℝ) := by
        have hAdiv : (A.card : ℝ) ^ 2 / (k : ℝ) ≤
            (A.card : ℝ) + ∑ w ∈ A, ((neighbors G A w).card : ℝ) := by
          rw [div_le_iff₀ hkpos]
          linarith
        linarith [hsumS, hsumT, hsumA, hcardS]
      have hsq : ((k : ℝ) * (T.card : ℝ) - (A.card : ℝ)) ^ 2 ≥ 0 := sq_nonneg _
      have hmul : (S.card : ℝ) ^ 2 ≤ ((k : ℝ) + 1) * ((T.card : ℝ) ^ 2 + (A.card : ℝ) ^ 2 / (k : ℝ)) := by
        rw [hcardS]
        have hclear : (k : ℝ) * ((T.card : ℝ) + (A.card : ℝ)) ^ 2 ≤
            (k : ℝ) * (((k : ℝ) + 1) * ((T.card : ℝ) ^ 2 + (A.card : ℝ) ^ 2 / (k : ℝ))) := by
          have hk0' : (k : ℝ) ≠ 0 := hkpos.ne'
          field_simp
          nlinarith [hsq]
        exact le_of_mul_le_mul_left hclear hkpos
      have hk_cast : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; rfl
      rw [hk_cast]
      exact hmul.trans (mul_le_mul_of_nonneg_left hcomb (by positivity))

omit [Fintype V] in
private lemma edgesIn_ge_of_indep_le (G : SimpleGraph V) (S : Finset V) (α : ℕ)
    (hα : 1 ≤ α)
    (hInd : ∀ I ⊆ S, G.IsIndepSet (I : Set V) → I.card ≤ α)
    (hS : 2 * α ≤ S.card) :
    (S.card : ℝ) ^ 2 ≤ 4 * (α : ℝ) * ((edgesIn G S).card : ℝ) := by
  have ht := turan_indep G α hα S hInd
  have hhs : (∑ v ∈ S, ((neighbors G S v).card : ℝ)) = 2 * ((edgesIn G S).card : ℝ) := by
    exact_mod_cast (handshaking_edgesIn G S).symm
  rw [hhs] at ht
  have h2a : (2 : ℝ) * (α : ℝ) ≤ (S.card : ℝ) := by exact_mod_cast hS
  have hS0 : (0 : ℝ) ≤ (S.card : ℝ) := by positivity
  have hal : (α : ℝ) * (S.card : ℝ) ≤ (S.card : ℝ) ^ 2 / 2 := by nlinarith
  nlinarith

private lemma cauchy_schwarz_finset {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    (∑ i ∈ s, f i) ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, (f i) ^ 2 := by
  simpa [mul_comm] using Finset.sum_mul_sq_le_sq_mul_sq s f (fun _ => (1 : ℝ))

omit [Fintype V] in
private lemma expanding_neighbors (G : SimpleGraph V) (S : Finset V) (a D : ℝ)
    (ha : ∀ I ⊆ S, G.IsIndepSet (I : Set V) → (I.card : ℝ) ≤ a) (hD : 0 ≤ D) :
    ∃ T ⊆ S, (S.card : ℝ) - a * (D + 1) ≤ (T.card : ℝ) ∧
      ∀ A ⊆ T, G.IsIndepSet (A : Set V) → D * (A.card : ℝ) ≤ ((near G T A).card : ℝ) := by
  obtain ⟨X, hXS, hX, hmax⟩ := max_subset S
    (fun X => G.IsIndepSet (X : Set V) ∧ ((near G S X).card : ℝ) ≤ D * (X.card : ℝ))
    (by simp [near])
  let W := X ∪ near G S X
  let T := S \ W
  have hs : S.card ≤ (S \ W).card + W.card := card_le_card_sdiff_add_card
  have hw : (W.card : ℝ) ≤ a * (D + 1) := by
    have ha1 : (W.card : ℝ) ≤ (X.card : ℝ) + ((near G S X).card : ℝ) := by
      exact_mod_cast card_union_le X (near G S X)
    have hx : (X.card : ℝ) ≤ a := ha X hXS hX.1
    nlinarith [hX.2]
  refine ⟨T, sdiff_subset, ?_, ?_⟩
  · have hs' : (S.card : ℝ) ≤ ((S \ W).card : ℝ) + (W.card : ℝ) := by exact_mod_cast hs
    change _ ≤ ((S \ W).card : ℝ)
    linarith
  intro A hAT hA
  by_contra! hsmall
  have hAX : Disjoint X A := by
    apply disjoint_left.mpr
    intro x hx hxa
    exact (mem_sdiff.mp (hAT hxa)).2 (mem_union_left _ hx)
  have hInd : G.IsIndepSet (↑(X ∪ A) : Set V) := by
    rw [G.isIndepSet_iff]
    intro x hx y hy hxy hadj
    simp only [coe_union, Set.mem_union, mem_coe] at hx hy
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · exact (G.isIndepSet_iff.mp hX.1) hx hy hxy hadj
    · obtain ⟨hys, hyw⟩ := mem_sdiff.mp (hAT hy)
      exact hyw (mem_union_right _ (mem_near.mpr ⟨hys, x, hx, hadj⟩))
    · obtain ⟨hxs, hxw⟩ := mem_sdiff.mp (hAT hx)
      exact hxw (mem_union_right _ (mem_near.mpr ⟨hxs, y, hy, hadj.symm⟩))
    · exact (G.isIndepSet_iff.mp hA) hx hy hxy hadj
  have hnears : near G S (X ∪ A) ⊆ near G S X ∪ near G T A := by
    intro w hw
    obtain ⟨hws, v, hv, hvw⟩ := mem_near.mp hw
    by_cases hvX : v ∈ X
    · exact mem_union_left _ (mem_near.mpr ⟨hws, v, hvX, hvw⟩)
    have hvA := (mem_union.mp hv).resolve_left hvX
    by_cases hwX : w ∈ near G S X
    · exact mem_union_left _ hwX
    have hwT : w ∈ T := by
      apply Finset.mem_sdiff.mpr
      refine ⟨hws, fun h => ?_⟩
      rcases mem_union.mp h with hx | hx
      · exact (Finset.mem_sdiff.mp (hAT hvA)).2 (mem_union_right _
          (mem_near.mpr ⟨(Finset.mem_sdiff.mp (hAT hvA)).1, w, hx, hvw.symm⟩))
      · exact hwX hx
    exact mem_union_right _ (mem_near.mpr ⟨hwT, v, hvA, hvw⟩)
  have hcard : ((near G S (X ∪ A)).card : ℝ) ≤
      ((near G S X).card : ℝ) + ((near G T A).card : ℝ) := by
    exact_mod_cast (card_le_card hnears).trans (card_union_le _ _)
  have hSmall : ((near G S (X ∪ A)).card : ℝ) ≤ D * ((X ∪ A).card : ℝ) := by
    rw [card_union_of_disjoint hAX, Nat.cast_add, mul_add]
    linarith [hX.2, hsmall]
  have hA_ne : A.Nonempty := by
    by_contra hAe
    rw [not_nonempty_iff_eq_empty.mp hAe] at hsmall
    simp [near] at hsmall
  have hm := hmax (X ∪ A) (union_subset hXS (hAT.trans sdiff_subset)) ⟨hInd, hSmall⟩
  rw [card_union_of_disjoint hAX] at hm
  have hpos : 0 < A.card := card_pos.mpr hA_ne
  omega

private lemma greedy_matching_of_directed (G : SimpleGraph V) (Nv : Finset V) (α : ℕ)
    (hTF : TriangleFree G Nv)
    (hInd : ∀ I ⊆ Nv, G.IsIndepSet (I : Set V) → I.card ≤ α)
    (M₀ : Finset (V × V))
    (hM₀ : ∀ p ∈ M₀, p.1 ∈ Nv ∧ p.2 ∈ Nv ∧ G.Adj p.1 p.2) :
    ∃ M' ⊆ M₀,
      (∀ p ∈ M', ∀ q ∈ M', p ≠ q → p.1 ≠ q.1 ∧ p.1 ≠ q.2 ∧ p.2 ≠ q.1 ∧ p.2 ≠ q.2) ∧
      M₀.card ≤ 4 * α * M'.card := by
  classical
  let IsMatching (M : Finset (V × V)) : Prop :=
    ∀ p ∈ M, ∀ q ∈ M, p ≠ q → p.1 ≠ q.1 ∧ p.1 ≠ q.2 ∧ p.2 ≠ q.1 ∧ p.2 ≠ q.2
  obtain ⟨M', hM', hmax⟩ := (M₀.powerset.filter IsMatching).exists_max_image card
    ⟨∅, by simp [IsMatching]⟩
  rw [mem_filter, mem_powerset] at hM'
  have hM'sub : M' ⊆ M₀ := hM'.1
  have hM'match : IsMatching M' := hM'.2
  have hmax' : ∀ B ⊆ M₀, IsMatching B → B.card ≤ M'.card := fun B hB1 hB2 =>
    hmax B (by simp [hB1, hB2])
  let U : Finset V := M'.biUnion (fun p => {p.1, p.2})
  have hUcard : U.card ≤ 2 * M'.card := by
    calc
      U.card ≤ ∑ _p ∈ M', 2 := card_biUnion_le.trans (sum_le_sum fun p _ => card_le_two)
      _ = 2 * M'.card := by simp [mul_comm]
  have hcover : ∀ p ∈ M₀, p.1 ∈ U ∨ p.2 ∈ U := by
    intro p hp
    by_contra hnot
    rw [not_or] at hnot
    have hpM' : p ∉ M' := fun h => hnot.1 (mem_biUnion.mpr ⟨p, h, by simp⟩)
    have hM'ins : IsMatching (insert p M') := by
      intro a ha b hb hab
      simp only [mem_insert] at ha hb
      rcases ha with rfl | ha <;> rcases hb with rfl | hb
      · exact False.elim (hab rfl)
      · have hb1 : b.1 ∈ U := mem_biUnion.mpr ⟨b, hb, by simp⟩
        have hb2 : b.2 ∈ U := mem_biUnion.mpr ⟨b, hb, by simp⟩
        exact ⟨fun h => hnot.1 (h ▸ hb1), fun h => hnot.1 (h ▸ hb2),
               fun h => hnot.2 (h ▸ hb1), fun h => hnot.2 (h ▸ hb2)⟩
      · have ha1 : a.1 ∈ U := mem_biUnion.mpr ⟨a, ha, by simp⟩
        have ha2 : a.2 ∈ U := mem_biUnion.mpr ⟨a, ha, by simp⟩
        exact ⟨fun h => hnot.1 (h.symm ▸ ha1), fun h => hnot.2 (h.symm ▸ ha1),
               fun h => hnot.1 (h.symm ▸ ha2), fun h => hnot.2 (h.symm ▸ ha2)⟩
      · exact hM'match a ha b hb hab
    have hm := hmax' (insert p M') (insert_subset hp hM'sub) hM'ins
    rw [card_insert_of_notMem hpM'] at hm
    omega
  have hM₀sub : M₀ ⊆ U.biUnion (fun z =>
      (M₀.filter (fun p => p.1 = z)) ∪ (M₀.filter (fun p => p.2 = z))) := by
    intro p hp
    rcases hcover p hp with h1 | h2
    · exact mem_biUnion.mpr ⟨p.1, h1, mem_union_left _ (mem_filter.mpr ⟨hp, rfl⟩)⟩
    · exact mem_biUnion.mpr ⟨p.2, h2, mem_union_right _ (mem_filter.mpr ⟨hp, rfl⟩)⟩
  have hfiber : ∀ z ∈ U,
      ((M₀.filter (fun p => p.1 = z)) ∪ (M₀.filter (fun p => p.2 = z))).card ≤ 2 * α := by
    intro z hz
    have hzNv : z ∈ Nv := by
      obtain ⟨p, hp, hzp⟩ := mem_biUnion.mp hz
      simp only [mem_insert, mem_singleton] at hzp
      rcases hzp with rfl | rfl
      · exact (hM₀ p (hM'sub hp)).1
      · exact (hM₀ p (hM'sub hp)).2.1
    have hNle : (neighbors G Nv z).card ≤ α :=
      hInd _ neighbors_subset (triangleFree_neighbors_indep hTF hzNv)
    have h1 : (M₀.filter (fun p => p.1 = z)).card ≤ (neighbors G Nv z).card := by
      refine card_le_card_of_injOn Prod.snd ?_ ?_
      · intro p hp
        obtain ⟨hpM, rfl⟩ := mem_filter.mp hp
        have h := hM₀ p hpM
        exact mem_neighbors.mpr ⟨h.2.1, h.2.2⟩
      · intro p₁ hp₁ p₂ hp₂ heq
        have e1 := (mem_filter.mp hp₁).2
        have e2 := (mem_filter.mp hp₂).2
        exact Prod.ext (e1.trans e2.symm) heq
    have h2 : (M₀.filter (fun p => p.2 = z)).card ≤ (neighbors G Nv z).card := by
      refine card_le_card_of_injOn Prod.fst ?_ ?_
      · intro p hp
        obtain ⟨hpM, rfl⟩ := mem_filter.mp hp
        have h := hM₀ p hpM
        exact mem_neighbors.mpr ⟨h.1, h.2.2.symm⟩
      · intro p₁ hp₁ p₂ hp₂ heq
        have e1 := (mem_filter.mp hp₁).2
        have e2 := (mem_filter.mp hp₂).2
        exact Prod.ext heq (e1.trans e2.symm)
    exact (card_union_le _ _).trans (by omega)
  have hM₀le : M₀.card ≤ U.card * (2 * α) := by
    calc
      M₀.card ≤ ∑ z ∈ U, ((M₀.filter (fun p => p.1 = z)) ∪ (M₀.filter (fun p => p.2 = z))).card :=
        (card_le_card hM₀sub).trans card_biUnion_le
      _ ≤ ∑ _z ∈ U, (2 * α) := sum_le_sum hfiber
      _ = U.card * (2 * α) := by simp
  refine ⟨M', hM'sub, hM'match, hM₀le.trans ?_⟩
  nlinarith [hUcard]

omit [Fintype V] in
private lemma bipartite_cut_exists (S : Finset V) (E : Finset (V × V))
    (hE : ∀ p ∈ E, p.1 ∈ S ∧ p.2 ∈ S ∧ p.1 ≠ p.2) :
    ∃ U₀ ⊆ S, E.card ≤ 4 * (E.filter (fun p => p.1 ∈ U₀ ∧ p.2 ∉ U₀)).card := by
  classical
  rcases E.eq_empty_or_nonempty with rfl | hne
  · exact ⟨∅, empty_subset S, by simp⟩
  obtain ⟨p₀, hp₀⟩ := hne
  have hS2 : 2 ≤ S.card := by
    have h1 := (hE p₀ hp₀).1
    have h2 := (hE p₀ hp₀).2.1
    have hne0 := (hE p₀ hp₀).2.2
    have hsub : ({p₀.1, p₀.2} : Finset V) ⊆ S := by
      intro z hz
      simp only [mem_insert, mem_singleton] at hz
      rcases hz with rfl | rfl <;> assumption
    exact (card_pair hne0).symm.trans_le (card_le_card hsub)
  let f : Finset V → V × V → ℕ := fun U₀ p => if p.1 ∈ U₀ ∧ p.2 ∉ U₀ then 1 else 0
  have hsum : ∑ U₀ ∈ S.powerset, (E.filter (fun p => p.1 ∈ U₀ ∧ p.2 ∉ U₀)).card =
      E.card * 2 ^ (S.card - 2) := by
    have h1 : ∀ U₀ ∈ S.powerset,
        (E.filter (fun p => p.1 ∈ U₀ ∧ p.2 ∉ U₀)).card = ∑ p ∈ E, f U₀ p := by
      intro U₀ _
      rw [sum_boole, Nat.cast_id]
    rw [sum_congr rfl h1, sum_comm]
    have h2 : ∀ p ∈ E, (∑ U₀ ∈ S.powerset, f U₀ p) = 2 ^ (S.card - 2) := by
      intro p hp
      obtain ⟨hp1, hp2, hne⟩ := hE p hp
      rw [sum_boole, Nat.cast_id]
      have hcard_bij : (S.powerset.filter (fun U₀ => p.1 ∈ U₀ ∧ p.2 ∉ U₀)).card =
          ((S \ {p.1, p.2}).powerset).card := by
        refine card_bij (fun U₀ _ => U₀.erase p.1) ?_ ?_ ?_
        · intro U₀ hU₀
          rw [mem_filter, mem_powerset] at hU₀
          rw [mem_powerset]
          intro z hz
          rw [mem_erase] at hz
          refine mem_sdiff.mpr ⟨hU₀.1 hz.2, ?_⟩
          simp only [mem_insert, mem_singleton, not_or]
          exact ⟨hz.1, fun h => hU₀.2.2 (h ▸ hz.2)⟩
        · intro U₁ hU₁ U₂ hU₂ heq
          have h1' := (mem_filter.mp hU₁).2.1
          have h2' := (mem_filter.mp hU₂).2.1
          rw [← insert_erase h1', ← insert_erase h2', heq]
        · intro T hT
          rw [mem_powerset] at hT
          refine ⟨insert p.1 T, mem_filter.mpr ⟨mem_powerset.mpr ?_, mem_insert_self _ _, ?_⟩, ?_⟩
          · exact insert_subset hp1 (hT.trans sdiff_subset)
          · simp only [mem_insert, not_or]
            refine ⟨hne.symm, fun h => ?_⟩
            exact (mem_sdiff.mp (hT h)).2 (by simp)
          · apply erase_insert
            intro h
            exact (mem_sdiff.mp (hT h)).2 (by simp)
      rw [hcard_bij, card_powerset, card_sdiff_of_subset (by
        intro z hz
        simp only [mem_insert, mem_singleton] at hz
        rcases hz with rfl | rfl <;> assumption), card_pair hne]
    rw [sum_congr rfl h2, sum_const, smul_eq_mul]
  have hpow : 4 * (E.card * 2 ^ (S.card - 2)) = S.powerset.card * E.card := by
    rw [card_powerset]
    have hexp : S.card = (S.card - 2) + 2 := (Nat.sub_add_cancel hS2).symm
    conv_rhs => rw [hexp, pow_add]
    ring
  by_contra! hlt
  have hbad : ∑ U₀ ∈ S.powerset, 4 * (E.filter (fun p => p.1 ∈ U₀ ∧ p.2 ∉ U₀)).card <
      ∑ _U₀ ∈ S.powerset, E.card := by
    refine sum_lt_sum (fun U₀ hU₀ => (hlt U₀ (mem_powerset.mp hU₀)).le) ?_
    refine ⟨∅, mem_powerset.mpr (empty_subset S), hlt ∅ (empty_subset S)⟩
  rw [← mul_sum, hsum, sum_const, smul_eq_mul, hpow] at hbad
  exact lt_irrefl _ hbad

private lemma dyadic_pigeonhole {α : Type*} (S_v : Finset α) (f : α → ℕ) (bound : ℕ)
    (hbound : ∀ e ∈ S_v, f e ≤ bound)
    (hpos : 0 < ∑ e ∈ S_v, (f e).choose 2) :
    ∃ j t : ℕ, 1 ≤ j ∧ j ≤ Nat.log 2 bound ∧ t = 2 ^ j ∧ t ≤ bound ∧
      let S := S_v.filter (fun e => t ≤ f e ∧ f e < 2 * t)
      S.Nonempty ∧ ∑ e ∈ S_v, (f e).choose 2 ≤ (Nat.log 2 bound + 1) * (2 * S.card * t ^ 2) := by
  classical
  let J := Finset.Ico 1 (Nat.log 2 bound + 1)
  have hpart : ∑ e ∈ S_v, (f e).choose 2 =
      ∑ j ∈ J, ∑ e ∈ S_v.filter (fun e => Nat.log 2 (f e) = j), (f e).choose 2 := by
    have hR : ∀ j ∈ J,
        ∑ e ∈ S_v.filter (fun e => Nat.log 2 (f e) = j), (f e).choose 2 =
          ∑ e ∈ S_v, if Nat.log 2 (f e) = j then (f e).choose 2 else 0 := by
      intro j _; rw [sum_filter]
    rw [sum_congr rfl hR, sum_comm]
    refine sum_congr rfl fun e he => ?_
    by_cases h2 : 2 ≤ f e
    · have hlog_in : Nat.log 2 (f e) ∈ J := by
        rw [mem_Ico]
        refine ⟨?_, Nat.lt_succ_of_le (Nat.log_mono_right (hbound e he))⟩
        have h1 : Nat.log 2 2 ≤ Nat.log 2 (f e) := Nat.log_mono_right h2
        have : Nat.log 2 2 = 1 := by decide
        omega
      have hf_eq : J.filter (fun j => Nat.log 2 (f e) = j) = {Nat.log 2 (f e)} := by
        ext j; simp only [mem_filter, mem_singleton]
        exact ⟨fun h => h.2.symm, fun h => ⟨h ▸ hlog_in, h.symm⟩⟩
      rw [← sum_filter, hf_eq, sum_singleton]
    · have hlt : f e < 2 := Nat.lt_of_not_le h2
      simp [Nat.choose_eq_zero_of_lt hlt]
  have hJne : J.Nonempty := by
    by_contra hJe
    rw [not_nonempty_iff_eq_empty.mp hJe, sum_empty] at hpart
    omega
  obtain ⟨j, hjJ, hmax⟩ := J.exists_max_image
    (fun j => ∑ e ∈ S_v.filter (fun e => Nat.log 2 (f e) = j), (f e).choose 2) hJne
  have hj1 : 1 ≤ j := (mem_Ico.mp hjJ).1
  have hjb : j ≤ Nat.log 2 bound := Nat.lt_succ_iff.mp (mem_Ico.mp hjJ).2
  let t := 2 ^ j
  let S := S_v.filter (fun e => t ≤ f e ∧ f e < 2 * t)
  have hsub : S_v.filter (fun e => Nat.log 2 (f e) = j) ⊆ S := by
    intro e he
    obtain ⟨heS, hlog⟩ := mem_filter.mp he
    have hfe0 : f e ≠ 0 := by
      intro hz
      rw [hz, Nat.log_zero_right] at hlog
      omega
    rw [mem_filter]
    refine ⟨heS, ?_, ?_⟩
    · change 2 ^ j ≤ f e
      rw [← hlog]
      exact Nat.pow_log_le_self 2 hfe0
    · change f e < 2 * 2 ^ j
      have hlt := Nat.lt_pow_succ_log_self (by decide : 1 < 2) (f e)
      rw [hlog, pow_succ, mul_comm] at hlt
      exact hlt
  have hsum_le : ∑ e ∈ S_v.filter (fun e => Nat.log 2 (f e) = j), (f e).choose 2 ≤
      2 * S.card * t ^ 2 := by
    calc
      ∑ e ∈ S_v.filter (fun e => Nat.log 2 (f e) = j), (f e).choose 2
        ≤ ∑ e ∈ S, (f e).choose 2 := sum_le_sum_of_subset hsub
      _ ≤ ∑ _e ∈ S, (2 * t ^ 2) := by
        refine sum_le_sum fun e he => ?_
        have hfe := (mem_filter.mp he).2.2
        rw [Nat.choose_two_right]
        have hmul : f e * (f e - 1) ≤ (2 * t) * (2 * t) :=
          Nat.mul_le_mul hfe.le ((Nat.sub_le _ _).trans hfe.le)
        have hdiv : f e * (f e - 1) / 2 ≤ 2 * t ^ 2 := by
          have : (2 * t) * (2 * t) / 2 = 2 * t ^ 2 := by
            rw [show (2 * t) * (2 * t) = 2 * (2 * t ^ 2) by ring, Nat.mul_div_cancel_left _ (by decide)]
          exact (Nat.div_le_div_right hmul).trans_eq this
        exact hdiv
      _ = 2 * S.card * t ^ 2 := by rw [sum_const, smul_eq_mul]; ring
  have htot : ∑ e ∈ S_v, (f e).choose 2 ≤ (Nat.log 2 bound + 1) * (2 * S.card * t ^ 2) := by
    rw [hpart]
    calc
      ∑ k ∈ J, ∑ e ∈ S_v.filter (fun e => Nat.log 2 (f e) = k), (f e).choose 2
        ≤ ∑ _k ∈ J, ∑ e ∈ S_v.filter (fun e => Nat.log 2 (f e) = j), (f e).choose 2 :=
          sum_le_sum fun k hk => hmax k hk
      _ = J.card * ∑ e ∈ S_v.filter (fun e => Nat.log 2 (f e) = j), (f e).choose 2 := by
          rw [sum_const, smul_eq_mul]
      _ ≤ (Nat.log 2 bound + 1) * (2 * S.card * t ^ 2) := by
          apply Nat.mul_le_mul _ hsum_le
          rw [Nat.card_Ico]
          omega
  have hSne : S.Nonempty := by
    by_contra hSe
    rw [not_nonempty_iff_eq_empty.mp hSe, card_empty] at htot
    omega
  have htb : t ≤ bound := by
    obtain ⟨e0, he0⟩ := hSne
    exact (mem_filter.mp he0).2.1.trans (hbound e0 (mem_filter.mp he0).1)
  exact ⟨j, t, hj1, hjb, rfl, htb, hSne, htot⟩

private lemma lt_of_rpow_poly {n L α : ℝ} (hn : 1 ≤ n) (hL : 1 ≤ L) (hα : 1 ≤ α)
    (hbad : (10 ^ 30 : ℝ) * L * α ^ 12 < n ^ 5)
    (p j q : ℕ) (hp : 1 ≤ p) (C : ℝ) (_hC0 : 0 ≤ C)
    (hpq : 5 * q ≤ 12 * p) (hjq : 12 * j ≤ q)
    (hC : C ^ 12 ≤ (10 ^ 30 : ℝ) ^ q) :
    C * L ^ j * α ^ q < n ^ p := by
  have hstrict : ((10 ^ 30 : ℝ) * L * α ^ 12) ^ q < (n ^ 5) ^ q ∨ q = 0 := by
    rcases eq_or_ne q 0 with rfl | hq0
    · exact Or.inr rfl
    · exact Or.inl (pow_lt_pow_left₀ hbad (by positivity) hq0)
  rcases hstrict with hlt_q | rfl
  · have hL12 : L ^ (12 * j) ≤ L ^ q := pow_le_pow_right₀ hL hjq
    have hn12 : n ^ (5 * q) ≤ n ^ (12 * p) := pow_le_pow_right₀ hn hpq
    have hpow : (C * L ^ j * α ^ q) ^ 12 < (n ^ p) ^ 12 := by
      calc
        (C * L ^ j * α ^ q) ^ 12 = C ^ 12 * L ^ (12 * j) * (α ^ 12) ^ q := by ring
        _ ≤ (10 ^ 30 : ℝ) ^ q * L ^ q * (α ^ 12) ^ q := by gcongr
        _ = ((10 ^ 30 : ℝ) * L * α ^ 12) ^ q := by ring
        _ < (n ^ 5) ^ q := hlt_q
        _ = n ^ (5 * q) := by ring
        _ ≤ n ^ (12 * p) := hn12
        _ = (n ^ p) ^ 12 := by ring
    exact lt_of_pow_lt_pow_left₀ 12 (by positivity) hpow
  · have hj0 : j = 0 := by omega
    subst hj0
    simp only [pow_zero, mul_one] at hC ⊢
    have hC1 : C ≤ 1 := by
      have hpow : C ^ 12 ≤ 1 ^ 12 := by simpa using hC
      exact le_of_pow_le_pow_left₀ (by decide) (by positivity) hpow
    have h1n : (1 : ℝ) < n := by
      by_contra hle
      have hn1 : n = 1 := le_antisymm (by linarith) hn
      rw [hn1, one_pow] at hbad
      have h10 : (10 ^ 30 : ℝ) ≤ (10 ^ 30 : ℝ) * L * α ^ 12 := by
        have h1la : 1 ≤ L * α ^ 12 := one_le_mul_of_one_le_of_one_le hL (one_le_pow₀ hα)
        linarith [mul_le_mul_of_nonneg_left h1la (by positivity : (0 : ℝ) ≤ 10 ^ 30)]
      linarith
    exact hC1.trans_lt (one_lt_pow₀ h1n (by omega))

end Helpers

section Forbidden

variable {V : Type*} [DecidableEq V] [Fintype V]

private def LocalIndep (G : SimpleGraph V) : Prop :=
  ∀ S : Finset V, S.card = 7 → ∃ I ⊆ S, I.card = 3 ∧ G.IsIndepSet (I : Set V)

private def Clique4Free (G : SimpleGraph V) : Prop :=
  ∀ K : Finset V, K.card = 4 → ¬ G.IsClique (K : Set V)

omit [Fintype V] in
private lemma card_inter_clique_le_one (G : SimpleGraph V) {I K : Finset V}
    (hI : G.IsIndepSet (I : Set V)) (hK : G.IsClique (K : Set V)) :
    (I ∩ K).card ≤ 1 := by
  by_contra! hgt
  obtain ⟨a, ha, b, hb, hab⟩ := one_lt_card.mp hgt
  rw [mem_inter] at ha hb
  exact (G.isIndepSet_iff.mp hI) ha.1 hb.1 hab (hK ha.2 hb.2 hab)

omit [Fintype V] in
private lemma card_inter_triangle_le_one (G : SimpleGraph V) {I : Finset V} {x y z : V}
    (hI : G.IsIndepSet (I : Set V)) (hxy : G.Adj x y) (hyz : G.Adj y z) (hxz : G.Adj x z) :
    (I ∩ ({x, y, z} : Finset V)).card ≤ 1 := by
  refine card_inter_clique_le_one G hI ?_
  intro a ha b hb hab
  simp only [coe_insert, coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
  · exact False.elim (hab rfl)
  · exact hxy
  · exact hxz
  · exact hxy.symm
  · exact False.elim (hab rfl)
  · exact hyz
  · exact hxz.symm
  · exact hyz.symm
  · exact False.elim (hab rfl)

private lemma k4_gives_triangle_free_rest (G : SimpleGraph V) (hLoc : LocalIndep G)
    {K : Finset V} (hKc : K.card = 4) (hK : G.IsClique (K : Set V)) :
    TriangleFree G (Finset.univ \ K) := by
  intro x hx y hy z hz hxy hyz hxz
  have hxK : x ∉ K := (mem_sdiff.mp hx).2
  have hyK : y ∉ K := (mem_sdiff.mp hy).2
  have hzK : z ∉ K := (mem_sdiff.mp hz).2
  have hxy' : x ≠ y := hxy.ne
  have hyz' : y ≠ z := hyz.ne
  have hxz' : x ≠ z := hxz.ne
  let T : Finset V := {x, y, z}
  have hTc : T.card = 3 := by
    rw [card_insert_of_notMem (by simp [hxy', hxz']), card_pair hyz']
  have hdisj : Disjoint K T := by
    rw [disjoint_right]
    intro w hw
    simp only [T, mem_insert, mem_singleton] at hw
    rcases hw with rfl | rfl | rfl <;> assumption
  have hSc : (K ∪ T).card = 7 := by
    rw [card_union_of_disjoint hdisj, hKc, hTc]
  obtain ⟨I, hIKT, hIc, hI⟩ := hLoc (K ∪ T) hSc
  have hI_sub : I ⊆ (I ∩ K) ∪ (I ∩ T) := by
    intro w hw
    rcases mem_union.mp (hIKT hw) with hwK | hwT
    · exact mem_union_left _ (mem_inter.mpr ⟨hw, hwK⟩)
    · exact mem_union_right _ (mem_inter.mpr ⟨hw, hwT⟩)
  have hle1 : (I ∩ K).card ≤ 1 := card_inter_clique_le_one G hI hK
  have hle2 : (I ∩ T).card ≤ 1 := card_inter_triangle_le_one G hI hxy hyz hxz
  have hcle := (card_le_card hI_sub).trans (card_union_le _ _)
  omega

omit [Fintype V] in
private lemma no_adj_extending_disjoint_edges (G : SimpleGraph V) (hLoc : LocalIndep G)
    {v a₁ a₂ b₁ b₂ u w : V}
    (hva₁ : G.Adj v a₁) (hva₂ : G.Adj v a₂) (ha₁₂ : G.Adj a₁ a₂)
    (hvb₁ : G.Adj v b₁) (hvb₂ : G.Adj v b₂) (hb₁₂ : G.Adj b₁ b₂)
    (hab₁₁ : a₁ ≠ b₁) (hab₁₂ : a₁ ≠ b₂) (hab₂₁ : a₂ ≠ b₁) (hab₂₂ : a₂ ≠ b₂)
    (huv : u ≠ v) (hnuv : ¬ G.Adj v u) (hua₁ : G.Adj u a₁) (hua₂ : G.Adj u a₂)
    (hwv : w ≠ v) (hnwv : ¬ G.Adj v w) (hwb₁ : G.Adj w b₁) (hwb₂ : G.Adj w b₂) :
    ¬ G.Adj u w := by
  intro huw
  have hne_uw : u ≠ w := huw.ne
  have hua₁' : u ≠ a₁ := hua₁.ne
  have hua₂' : u ≠ a₂ := hua₂.ne
  have hub₁ : u ≠ b₁ := fun h => hnuv (h ▸ hvb₁)
  have hub₂ : u ≠ b₂ := fun h => hnuv (h ▸ hvb₂)
  have hwa₁ : w ≠ a₁ := fun h => hnwv (h ▸ hva₁)
  have hwa₂ : w ≠ a₂ := fun h => hnwv (h ▸ hva₂)
  have hwb₁' : w ≠ b₁ := hwb₁.ne
  have hwb₂' : w ≠ b₂ := hwb₂.ne
  have hva₁' : v ≠ a₁ := hva₁.ne
  have hva₂' : v ≠ a₂ := hva₂.ne
  have hvb₁' : v ≠ b₁ := hvb₁.ne
  have hvb₂' : v ≠ b₂ := hvb₂.ne
  have ha₁₂' : a₁ ≠ a₂ := ha₁₂.ne
  have hb₁₂' : b₁ ≠ b₂ := hb₁₂.ne
  let S : Finset V := {v, a₁, a₂, b₁, b₂, u, w}
  have hSc : S.card = 7 := by
    rw [card_insert_of_notMem (by simp [hva₁', hva₂', hvb₁', hvb₂', huv.symm, hwv.symm])]
    rw [card_insert_of_notMem (by simp [ha₁₂', hab₁₁, hab₁₂, hua₁'.symm, hwa₁.symm])]
    rw [card_insert_of_notMem (by simp [hab₂₁, hab₂₂, hua₂'.symm, hwa₂.symm])]
    rw [card_insert_of_notMem (by simp [hb₁₂', hub₁.symm, hwb₁'.symm])]
    rw [card_insert_of_notMem (by simp [hub₂.symm, hwb₂'.symm])]
    rw [card_pair hne_uw]
  obtain ⟨I, hIS, hIc, hI⟩ := hLoc S hSc
  by_cases huI : u ∈ I
  · have hsub : I ⊆ insert u (I ∩ ({v, b₁, b₂} : Finset V)) := by
      intro z hz
      by_cases hzu : z = u
      · subst hzu; exact mem_insert_self _ _
      have hzS := hIS hz
      simp only [S, mem_insert, mem_singleton] at hzS
      have hn1 : z ≠ a₁ := fun h => (G.isIndepSet_iff.mp hI) huI hz (h ▸ hua₁') (h ▸ hua₁)
      have hn2 : z ≠ a₂ := fun h => (G.isIndepSet_iff.mp hI) huI hz (h ▸ hua₂') (h ▸ hua₂)
      have hnw : z ≠ w := fun h => (G.isIndepSet_iff.mp hI) huI hz (h ▸ hne_uw) (h ▸ huw)
      rcases hzS with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact mem_insert_of_mem (mem_inter.mpr ⟨hz, by simp⟩)
      · exact False.elim (hn1 rfl)
      · exact False.elim (hn2 rfl)
      · exact mem_insert_of_mem (mem_inter.mpr ⟨hz, by simp⟩)
      · exact mem_insert_of_mem (mem_inter.mpr ⟨hz, by simp⟩)
      · exact False.elim (hzu rfl)
      · exact False.elim (hnw rfl)
    have hle := card_inter_triangle_le_one G hI hvb₁ hb₁₂ hvb₂
    have hcle := (card_le_card hsub).trans (card_insert_le _ _)
    omega
  · have hsub : I ⊆ (I ∩ ({v, a₁, a₂} : Finset V)) ∪ (I ∩ ({w, b₁, b₂} : Finset V)) := by
      intro z hz
      have hzS := hIS hz
      simp only [S, mem_insert, mem_singleton] at hzS
      rcases hzS with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact mem_union_left _ (mem_inter.mpr ⟨hz, by simp⟩)
      · exact mem_union_left _ (mem_inter.mpr ⟨hz, by simp⟩)
      · exact mem_union_left _ (mem_inter.mpr ⟨hz, by simp⟩)
      · exact mem_union_right _ (mem_inter.mpr ⟨hz, by simp⟩)
      · exact mem_union_right _ (mem_inter.mpr ⟨hz, by simp⟩)
      · exact False.elim (huI hz)
      · exact mem_union_right _ (mem_inter.mpr ⟨hz, by simp⟩)
    have hle1 := card_inter_triangle_le_one G hI hva₁ ha₁₂ hva₂
    have hle2 := card_inter_triangle_le_one G hI hwb₁ hb₁₂ hwb₂
    have hcle := (card_le_card hsub).trans (card_union_le _ _)
    omega

end Forbidden

section PropertiesAndPartition

variable {V : Type*} [DecidableEq V] [Fintype V]

private def IsVExt (G : SimpleGraph V) (v w : V) : Prop :=
  w ≠ v ∧ ¬ G.Adj v w ∧
    ∃ e ∈ edgesIn G (neighbors G Finset.univ v), ∀ a ∈ e, G.Adj w a

private def N_tri (G : SimpleGraph V) (v : V) : Finset V := by
  classical
  exact Finset.univ.filter (IsVExt G v)

private def vTris (G : SimpleGraph V) (v w : V) : Finset (Finset V) := by
  classical
  exact (edgesIn G (neighbors G Finset.univ v)).filter (fun e => ∀ a ∈ e, G.Adj w a)

private lemma mem_N_tri {G : SimpleGraph V} {v w : V} :
    w ∈ N_tri G v ↔ IsVExt G v w := by
  classical
  simp [N_tri]

private lemma mem_vTris {G : SimpleGraph V} {v w : V} {e : Finset V} :
    e ∈ vTris G v w ↔ e ∈ edgesIn G (neighbors G Finset.univ v) ∧ ∀ a ∈ e, G.Adj w a := by
  classical
  simp [vTris]

private lemma no_adj_disjoint_vTris (G : SimpleGraph V) (hLoc : LocalIndep G) {v u w : V}
    (hu : u ∈ N_tri G v) (hw : w ∈ N_tri G v)
    {e₁ e₂ : Finset V} (he₁ : e₁ ∈ vTris G v u) (he₂ : e₂ ∈ vTris G v w)
    (hdisj : Disjoint e₁ e₂) : ¬ G.Adj u w := by
  obtain ⟨hu_ne, hnuv, _⟩ := mem_N_tri.mp hu
  obtain ⟨hw_ne, hnwv, _⟩ := mem_N_tri.mp hw
  obtain ⟨he₁_in, hu_adj⟩ := mem_vTris.mp he₁
  obtain ⟨he₂_in, hw_adj⟩ := mem_vTris.mp he₂
  obtain ⟨he₁_sub, he₁_c, he₁_cl⟩ := mem_edgesIn.mp he₁_in
  obtain ⟨he₂_sub, he₂_c, he₂_cl⟩ := mem_edgesIn.mp he₂_in
  obtain ⟨a₁, a₂, ha₁₂, rfl⟩ := card_eq_two.mp he₁_c
  obtain ⟨b₁, b₂, hb₁₂, rfl⟩ := card_eq_two.mp he₂_c
  have hva₁ := (mem_neighbors.mp (he₁_sub (mem_insert_self a₁ _))).2
  have hva₂ := (mem_neighbors.mp (he₁_sub (mem_insert_of_mem (mem_singleton_self a₂)))).2
  have hvb₁ := (mem_neighbors.mp (he₂_sub (mem_insert_self b₁ _))).2
  have hvb₂ := (mem_neighbors.mp (he₂_sub (mem_insert_of_mem (mem_singleton_self b₂)))).2
  have hadj_a := he₁_cl (by simp) (by simp) ha₁₂
  have hadj_b := he₂_cl (by simp) (by simp) hb₁₂
  have hd : ∀ x ∈ ({a₁, a₂} : Finset V), ∀ y ∈ ({b₁, b₂} : Finset V), x ≠ y := by
    intro x hx y hy hxy
    exact (disjoint_left.mp hdisj) hx (hxy ▸ hy)
  exact no_adj_extending_disjoint_edges G hLoc hva₁ hva₂ hadj_a hvb₁ hvb₂ hadj_b
    (hd a₁ (by simp) b₁ (by simp)) (hd a₁ (by simp) b₂ (by simp))
    (hd a₂ (by simp) b₁ (by simp)) (hd a₂ (by simp) b₂ (by simp))
    hu_ne hnuv (hu_adj a₁ (mem_insert_self a₁ _))
    (hu_adj a₂ (mem_insert_of_mem (mem_singleton_self a₂)))
    hw_ne hnwv (hw_adj b₁ (mem_insert_self b₁ _))
    (hw_adj b₂ (mem_insert_of_mem (mem_singleton_self b₂)))

private lemma N_tri_triangle_free (G : SimpleGraph V) (hK4 : Clique4Free G) (hLoc : LocalIndep G)
    (v : V) : TriangleFree G (N_tri G v) := by
  intro x hx y hy z hz hxy hyz hxz
  obtain ⟨_, _, e₁, he₁, hadj₁⟩ := mem_N_tri.mp hx
  obtain ⟨_, _, e₂, he₂, hadj₂⟩ := mem_N_tri.mp hy
  obtain ⟨_, _, e₃, he₃, hadj₃⟩ := mem_N_tri.mp hz
  have he₁' : e₁ ∈ vTris G v x := mem_vTris.mpr ⟨he₁, hadj₁⟩
  have he₂' : e₂ ∈ vTris G v y := mem_vTris.mpr ⟨he₂, hadj₂⟩
  have he₃' : e₃ ∈ vTris G v z := mem_vTris.mpr ⟨he₃, hadj₃⟩
  have hd₁₂ : ¬ Disjoint e₁ e₂ := fun hd => no_adj_disjoint_vTris G hLoc hx hy he₁' he₂' hd hxy
  have hd₂₃ : ¬ Disjoint e₂ e₃ := fun hd => no_adj_disjoint_vTris G hLoc hy hz he₂' he₃' hd hyz
  have hd₁₃ : ¬ Disjoint e₁ e₃ := fun hd => no_adj_disjoint_vTris G hLoc hx hz he₁' he₃' hd hxz
  rw [not_disjoint_iff] at hd₁₂ hd₂₃ hd₁₃
  obtain ⟨p₁, hp₁₁, hp₁₂⟩ := hd₁₂
  obtain ⟨p₂, hp₂₂, hp₂₃⟩ := hd₂₃
  obtain ⟨p₃, hp₃₁, hp₃₃⟩ := hd₁₃
  by_cases hcom : ∃ p, p ∈ e₁ ∧ p ∈ e₂ ∧ p ∈ e₃
  · obtain ⟨p, hp1, hp2, hp3⟩ := hcom
    have hpNv : p ∈ neighbors G Finset.univ v := (mem_edgesIn.mp he₁).1 hp1
    have hpx : p ≠ x := fun h => (mem_N_tri.mp hx).2.1 (h ▸ (mem_neighbors.mp hpNv).2)
    have hpy : p ≠ y := fun h => (mem_N_tri.mp hy).2.1 (h ▸ (mem_neighbors.mp hpNv).2)
    have hpz : p ≠ z := fun h => (mem_N_tri.mp hz).2.1 (h ▸ (mem_neighbors.mp hpNv).2)
    let K : Finset V := {p, x, y, z}
    have hKc : K.card = 4 := by
      rw [card_insert_of_notMem (by simp [hpx, hpy, hpz]),
          card_insert_of_notMem (by simp [hxy.ne, hxz.ne]), card_pair hyz.ne]
    refine hK4 K hKc ?_
    intro a ha b hb hab
    simp only [K, coe_insert, coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
    rcases ha with rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl
    · exact False.elim (hab rfl)
    · exact (hadj₁ _ hp1).symm
    · exact (hadj₂ _ hp2).symm
    · exact (hadj₃ _ hp3).symm
    · exact hadj₁ _ hp1
    · exact False.elim (hab rfl)
    · exact hxy
    · exact hxz
    · exact hadj₂ _ hp2
    · exact hxy.symm
    · exact False.elim (hab rfl)
    · exact hyz
    · exact hadj₃ _ hp3
    · exact hxz.symm
    · exact hyz.symm
    · exact False.elim (hab rfl)
  · push Not at hcom
    have hp₁₃ : p₁ ∉ e₃ := hcom p₁ hp₁₁ hp₁₂
    have hp₂₁ : p₂ ∉ e₁ := fun h => hcom p₂ h hp₂₂ hp₂₃
    have hp₃₂ : p₃ ∉ e₂ := fun h => hcom p₃ hp₃₁ h hp₃₃
    have h12 : p₁ ≠ p₂ := fun h => hp₂₁ (h ▸ hp₁₁)
    have h23 : p₂ ≠ p₃ := fun h => hp₃₂ (h ▸ hp₂₂)
    have h13 : p₁ ≠ p₃ := fun h => hp₁₃ (h ▸ hp₃₃)
    have hvp₁ : G.Adj v p₁ := (mem_neighbors.mp ((mem_edgesIn.mp he₁).1 hp₁₁)).2
    have hvp₂ : G.Adj v p₂ := (mem_neighbors.mp ((mem_edgesIn.mp he₂).1 hp₂₂)).2
    have hvp₃ : G.Adj v p₃ := (mem_neighbors.mp ((mem_edgesIn.mp he₃).1 hp₃₃)).2
    have hp₁₂_adj : G.Adj p₁ p₂ := (mem_edgesIn.mp he₂).2.2 hp₁₂ hp₂₂ h12
    have hp₂₃_adj : G.Adj p₂ p₃ := (mem_edgesIn.mp he₃).2.2 hp₂₃ hp₃₃ h23
    have hp₁₃_adj : G.Adj p₁ p₃ := (mem_edgesIn.mp he₁).2.2 hp₁₁ hp₃₁ h13
    let K : Finset V := {v, p₁, p₂, p₃}
    have hKc : K.card = 4 := by
      rw [card_insert_of_notMem (by simp [hvp₁.ne, hvp₂.ne, hvp₃.ne]),
          card_insert_of_notMem (by simp [h12, h13]), card_pair h23]
    refine hK4 K hKc ?_
    intro a ha b hb hab
    simp only [K, coe_insert, coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
    rcases ha with rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl
    · exact False.elim (hab rfl)
    · exact hvp₁
    · exact hvp₂
    · exact hvp₃
    · exact hvp₁.symm
    · exact False.elim (hab rfl)
    · exact hp₁₂_adj
    · exact hp₁₃_adj
    · exact hvp₂.symm
    · exact hp₁₂_adj.symm
    · exact False.elim (hab rfl)
    · exact hp₂₃_adj
    · exact hvp₃.symm
    · exact hp₁₃_adj.symm
    · exact hp₂₃_adj.symm
    · exact False.elim (hab rfl)

omit [Fintype V] in
private lemma at_most_four_intersecting_both {E : Finset (Finset V)} {e₁ e₂ : Finset V}
    (he₁ : e₁.card = 2) (he₂ : e₂.card = 2) (hdisj : Disjoint e₁ e₂)
    (hE : ∀ e ∈ E, e.card = 2 ∧ ¬ Disjoint e e₁ ∧ ¬ Disjoint e e₂) :
    E.card ≤ 4 := by
  have hsub : E ⊆ (e₁ ×ˢ e₂).image (fun p => ({p.1, p.2} : Finset V)) := by
    intro e he
    obtain ⟨hec, hd1, hd2⟩ := hE e he
    rw [not_disjoint_iff] at hd1 hd2
    obtain ⟨x, hxe, hxe1⟩ := hd1
    obtain ⟨y, hye, hye2⟩ := hd2
    have hxy : x ≠ y := fun h => (disjoint_left.mp hdisj) hxe1 (h ▸ hye2)
    have hpair : ({x, y} : Finset V) ⊆ e := by
      intro z hz
      simp only [mem_insert, mem_singleton] at hz
      rcases hz with rfl | rfl <;> assumption
    have heq : ({x, y} : Finset V) = e := eq_of_subset_of_card_le hpair (by rw [hec, card_pair hxy])
    exact mem_image.mpr ⟨(x, y), mem_product.mpr ⟨hxe1, hye2⟩, heq⟩
  calc
    E.card ≤ ((e₁ ×ˢ e₂).image (fun p => ({p.1, p.2} : Finset V))).card := card_le_card hsub
    _ ≤ (e₁ ×ˢ e₂).card := card_image_le
    _ = 4 := by rw [card_product, he₁, he₂]

private lemma intersecting_pairs_star {E : Finset (Finset V)}
    (hcard : ∀ e ∈ E, e.card = 2)
    (hinter : ∀ e₁ ∈ E, ∀ e₂ ∈ E, ¬ Disjoint e₁ e₂)
    (h4 : 4 ≤ E.card) :
    ∃! c : V, ∀ e ∈ E, c ∈ e := by
  have hEx : ∃ c : V, ∀ e ∈ E, c ∈ e := by
    obtain ⟨e₀, he₀⟩ := card_pos.mp (by omega : 0 < E.card)
    obtain ⟨a, b, hab, he₀_eq⟩ := card_eq_two.mp (hcard e₀ he₀)
    by_cases ha : ∀ e ∈ E, a ∈ e
    · exact ⟨a, ha⟩
    push Not at ha
    obtain ⟨e₁, he₁, hae₁⟩ := ha
    have hbe₁ : b ∈ e₁ := by
      have hd := hinter e₀ he₀ e₁ he₁
      rw [not_disjoint_iff] at hd
      obtain ⟨z, hz0, hz1⟩ := hd
      rw [he₀_eq] at hz0
      simp only [mem_insert, mem_singleton] at hz0
      rcases hz0 with rfl | rfl
      · exact False.elim (hae₁ hz1)
      · exact hz1
    obtain ⟨x, y, hxy, he₁_eq⟩ := card_eq_two.mp (hcard e₁ he₁)
    have hbx : b = x ∨ b = y := by
      rw [he₁_eq] at hbe₁
      simpa using hbe₁
    have h_other : ∃ d : V, d ≠ a ∧ d ≠ b ∧ e₁ = {b, d} := by
      rcases hbx with rfl | rfl
      · exact ⟨y, fun h => hae₁ (he₁_eq ▸ (by simp [h])), hxy.symm, he₁_eq⟩
      · refine ⟨x, fun h => hae₁ (he₁_eq ▸ (by simp [h])), hxy, ?_⟩
        rw [he₁_eq, pair_comm]
    obtain ⟨d, hda, hdb, he₁_eq'⟩ := h_other
    by_cases hb : ∀ e ∈ E, b ∈ e
    · exact ⟨b, hb⟩
    push Not at hb
    obtain ⟨e₂, he₂, hbe₂⟩ := hb
    have hae₂ : a ∈ e₂ := by
      have hd := hinter e₀ he₀ e₂ he₂
      rw [not_disjoint_iff] at hd
      obtain ⟨z, hz0, hz2⟩ := hd
      rw [he₀_eq] at hz0
      simp only [mem_insert, mem_singleton] at hz0
      rcases hz0 with rfl | rfl
      · exact hz2
      · exact False.elim (hbe₂ hz2)
    have hde₂ : d ∈ e₂ := by
      have hd := hinter e₁ he₁ e₂ he₂
      rw [not_disjoint_iff] at hd
      obtain ⟨z, hz1, hz2⟩ := hd
      rw [he₁_eq'] at hz1
      simp only [mem_insert, mem_singleton] at hz1
      rcases hz1 with rfl | rfl
      · exact False.elim (hbe₂ hz2)
      · exact hz2
    have he₂_eq : e₂ = {a, d} := by
      refine (eq_of_subset_of_card_le ?_ (by rw [hcard e₂ he₂, card_pair hda.symm])).symm
      intro z hz
      simp only [mem_insert, mem_singleton] at hz
      rcases hz with rfl | rfl <;> assumption
    have hsub3 : E ⊆ ({a, b, d} : Finset V).powersetCard 2 := by
      intro e he
      rw [mem_powersetCard]
      refine ⟨?_, hcard e he⟩
      intro z hz
      by_contra hnot
      obtain ⟨u, v, huv, he_eq⟩ := card_eq_two.mp (hcard e he)
      have hzuv : z = u ∨ z = v := by simpa [he_eq] using hz
      have h_other_mem : ∃ w : V, w ≠ z ∧ e = {z, w} := by
        rcases hzuv with rfl | rfl
        · exact ⟨v, huv.symm, he_eq⟩
        · exact ⟨u, huv, by rw [he_eq, pair_comm]⟩
      obtain ⟨w, hwz, he_eq'⟩ := h_other_mem
      have h_inter_mem : ∀ {S : Finset V}, ¬ Disjoint S e → ∃ t ∈ S, t ∈ e := by
        intro S hS
        rw [not_disjoint_iff] at hS
        exact hS
      have hw0 : w ∈ e₀ := by
        obtain ⟨t, ht0, hte⟩ := h_inter_mem (hinter e₀ he₀ e he)
        rw [he_eq'] at hte
        simp only [mem_insert, mem_singleton] at hte
        rcases hte with rfl | rfl
        · exact False.elim (hnot (by rw [he₀_eq] at ht0; simp only [mem_insert, mem_singleton] at ht0 ⊢; tauto))
        · exact ht0
      have hw1 : w ∈ e₁ := by
        obtain ⟨t, ht1, hte⟩ := h_inter_mem (hinter e₁ he₁ e he)
        rw [he_eq'] at hte
        simp only [mem_insert, mem_singleton] at hte
        rcases hte with rfl | rfl
        · exact False.elim (hnot (by rw [he₁_eq'] at ht1; simp only [mem_insert, mem_singleton] at ht1 ⊢; tauto))
        · exact ht1
      have hw2 : w ∈ e₂ := by
        obtain ⟨t, ht2, hte⟩ := h_inter_mem (hinter e₂ he₂ e he)
        rw [he_eq'] at hte
        simp only [mem_insert, mem_singleton] at hte
        rcases hte with rfl | rfl
        · exact False.elim (hnot (by rw [he₂_eq] at ht2; simp only [mem_insert, mem_singleton] at ht2 ⊢; tauto))
        · exact ht2
      rw [he₀_eq] at hw0
      rw [he₁_eq'] at hw1
      rw [he₂_eq] at hw2
      simp only [mem_insert, mem_singleton] at hw0 hw1 hw2
      rcases hw0 with rfl | rfl
      · rcases hw1 with h | h
        · exact absurd h hab
        · exact absurd h hda.symm
      · rcases hw2 with h | h
        · exact absurd h hab.symm
        · exact absurd h hdb.symm
    have hle3 : E.card ≤ 3 := by
      calc
        E.card ≤ (({a, b, d} : Finset V).powersetCard 2).card := card_le_card hsub3
        _ = ({a, b, d} : Finset V).card.choose 2 := card_powersetCard _ _
        _ ≤ 3 := by
          have hc3 : ({a, b, d} : Finset V).card ≤ 3 :=
            (card_insert_le _ _).trans (Nat.succ_le_succ card_le_two)
          have hch : ({a, b, d} : Finset V).card.choose 2 ≤ 3 :=
            (Nat.choose_le_choose 2 hc3).trans (by decide)
          exact hch
    omega
  obtain ⟨c, hc⟩ := hEx
  refine ⟨c, hc, fun c' hc' => ?_⟩
  by_contra hne
  have hsub1 : E ⊆ {{c, c'}} := by
    intro e he
    rw [mem_singleton]
    refine (eq_of_subset_of_card_le ?_ (by rw [hcard e he, card_pair (Ne.symm hne)])).symm
    intro z hz
    simp only [mem_insert, mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact hc e he
    · exact hc' e he
  have hle1 : E.card ≤ 1 := (card_le_card hsub1).trans (by simp)
  omega

private lemma vTris_star_of_adj (G : SimpleGraph V) (hLoc : LocalIndep G) {v u w : V}
    (hu : u ∈ N_tri G v) (hw : w ∈ N_tri G v) (huw : G.Adj u w)
    (h5u : 5 ≤ (vTris G v u).card) (h5w : 5 ≤ (vTris G v w).card) :
    ∃ cu ∈ neighbors G Finset.univ v,
      (∀ e ∈ vTris G v u, cu ∈ e) ∧ (∀ e ∈ vTris G v w, cu ∈ e) := by
  have hdisj_u : ∀ e₁ ∈ vTris G v u, ∀ e₂ ∈ vTris G v u, ¬ Disjoint e₁ e₂ := by
    intro e₁ he₁ e₂ he₂ hd
    have h4 : (vTris G v w).card ≤ 4 := by
      refine at_most_four_intersecting_both
        (mem_edgesIn.mp (mem_vTris.mp he₁).1).2.1
        (mem_edgesIn.mp (mem_vTris.mp he₂).1).2.1 hd fun e he => ?_
      refine ⟨(mem_edgesIn.mp (mem_vTris.mp he).1).2.1, ?_, ?_⟩
      · intro h; exact no_adj_disjoint_vTris G hLoc hu hw he₁ he h.symm huw
      · intro h; exact no_adj_disjoint_vTris G hLoc hu hw he₂ he h.symm huw
    omega
  have hdisj_w : ∀ e₁ ∈ vTris G v w, ∀ e₂ ∈ vTris G v w, ¬ Disjoint e₁ e₂ := by
    intro e₁ he₁ e₂ he₂ hd
    have h4 : (vTris G v u).card ≤ 4 := by
      refine at_most_four_intersecting_both
        (mem_edgesIn.mp (mem_vTris.mp he₁).1).2.1
        (mem_edgesIn.mp (mem_vTris.mp he₂).1).2.1 hd fun e he => ?_
      refine ⟨(mem_edgesIn.mp (mem_vTris.mp he).1).2.1, ?_, ?_⟩
      · intro h; exact no_adj_disjoint_vTris G hLoc hw hu he₁ he h.symm huw.symm
      · intro h; exact no_adj_disjoint_vTris G hLoc hw hu he₂ he h.symm huw.symm
    omega
  obtain ⟨cu, hcu, _⟩ := intersecting_pairs_star
    (fun e he => (mem_edgesIn.mp (mem_vTris.mp he).1).2.1) hdisj_u (by omega)
  obtain ⟨cw, hcw, _⟩ := intersecting_pairs_star
    (fun e he => (mem_edgesIn.mp (mem_vTris.mp he).1).2.1) hdisj_w (by omega)
  have hcu_nv : cu ∈ neighbors G Finset.univ v := by
    obtain ⟨e₀, he₀⟩ := card_pos.mp (by omega : 0 < (vTris G v u).card)
    exact (mem_edgesIn.mp (mem_vTris.mp he₀).1).1 (hcu e₀ he₀)
  have heq_c : cu = cw := by
    by_contra hne
    let Eu' := (vTris G v u).erase {cu, cw}
    let Ew' := (vTris G v w).erase {cu, cw}
    have hEu'_ne : Eu'.Nonempty := by
      rw [← card_pos]
      dsimp [Eu']
      have := card_erase_ge_sub_one (vTris G v u) {cu, cw}
      omega
    obtain ⟨eu, heu⟩ := hEu'_ne
    have heu_u : eu ∈ vTris G v u := mem_of_mem_erase heu
    have heu_ne : eu ≠ {cu, cw} := (mem_erase.mp heu).1
    have hcw_not_eu : cw ∉ eu := by
      intro hcw_in
      apply heu_ne
      refine (eq_of_subset_of_card_le ?_ (by
        rw [(mem_edgesIn.mp (mem_vTris.mp heu_u).1).2.1, card_pair hne])).symm
      intro z hz
      simp only [mem_insert, mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact hcu eu heu_u
      · exact hcw_in
    obtain ⟨x, hxu, hx_eq⟩ : ∃ x ≠ cu, eu = {cu, x} := by
      obtain ⟨a, b, hab, heq⟩ := card_eq_two.mp (mem_edgesIn.mp (mem_vTris.mp heu_u).1).2.1
      have hcu_in : cu ∈ eu := hcu eu heu_u
      rw [heq] at hcu_in
      simp only [mem_insert, mem_singleton] at hcu_in
      rcases hcu_in with rfl | rfl
      · exact ⟨b, hab.symm, heq⟩
      · exact ⟨a, hab, by rw [heq, pair_comm]⟩
    have hEw'_card : 2 ≤ (Ew'.erase {cw, x}).card := by
      have h1 := card_erase_ge_sub_one (vTris G v w) {cu, cw}
      have h2 := card_erase_ge_sub_one Ew' {cw, x}
      dsimp [Ew'] at h2 ⊢
      omega
    obtain ⟨ew, hew⟩ := card_pos.mp (by omega : 0 < (Ew'.erase {cw, x}).card)
    have hew_Ew' : ew ∈ Ew' := mem_of_mem_erase hew
    have hew_w : ew ∈ vTris G v w := mem_of_mem_erase hew_Ew'
    have hew_ne1 : ew ≠ {cu, cw} := (mem_erase.mp hew_Ew').1
    have hew_ne2 : ew ≠ {cw, x} := (mem_erase.mp hew).1
    have hcu_not_ew : cu ∉ ew := by
      intro hcu_in
      apply hew_ne1
      refine (eq_of_subset_of_card_le ?_ (by
        rw [(mem_edgesIn.mp (mem_vTris.mp hew_w).1).2.1, card_pair hne])).symm
      intro z hz
      simp only [mem_insert, mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact hcu_in
      · exact hcw ew hew_w
    have hx_not_ew : x ∉ ew := by
      intro hx_in
      apply hew_ne2
      have hx_cw : cw ≠ x := fun h => hcw_not_eu (hx_eq ▸ (by simp [h]))
      refine (eq_of_subset_of_card_le ?_ (by
        rw [(mem_edgesIn.mp (mem_vTris.mp hew_w).1).2.1, card_pair hx_cw])).symm
      intro z hz
      simp only [mem_insert, mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact hcw ew hew_w
      · exact hx_in
    have hdisj : Disjoint eu ew := by
      rw [hx_eq, disjoint_left]
      intro z hz
      simp only [mem_insert, mem_singleton] at hz
      rcases hz with rfl | rfl <;> assumption
    exact no_adj_disjoint_vTris G hLoc hu hw heu_u hew_w hdisj huw
  subst heq_c
  exact ⟨cu, hcu_nv, hcu, hcw⟩

private lemma partition_N_tri (G : SimpleGraph V) (hLoc : LocalIndep G) (v : V) :
    ∃ L_set I_set C_set : Finset V, ∃ C_part : V → Finset V,
      L_set ∪ I_set ∪ C_set = N_tri G v ∧
      Disjoint L_set I_set ∧ Disjoint L_set C_set ∧ Disjoint I_set C_set ∧
      (∀ w ∈ L_set, (vTris G v w).card ≤ 4) ∧
      G.IsIndepSet (I_set : Set V) ∧
      C_set = (neighbors G Finset.univ v).biUnion C_part ∧
      (∀ c₁ ∈ neighbors G Finset.univ v, ∀ c₂ ∈ neighbors G Finset.univ v, c₁ ≠ c₂ →
        Disjoint (C_part c₁) (C_part c₂) ∧
        ∀ x ∈ C_part c₁, ∀ y ∈ C_part c₂, ¬ G.Adj x y) ∧
      (∀ c ∈ neighbors G Finset.univ v, ∀ w ∈ C_part c, ∀ e ∈ vTris G v w, c ∈ e) := by
  classical
  let Nv := neighbors G Finset.univ v
  let Nt := N_tri G v
  let L_set := Nt.filter (fun w => (vTris G v w).card ≤ 4)
  let H := Nt \ L_set
  let I_set := H.filter (fun w => ∀ u ∈ H, ¬ G.Adj w u)
  let C_set := H \ I_set
  have hH5 : ∀ w ∈ H, 5 ≤ (vTris G v w).card := by
    intro w hw
    have hnot : ¬ (vTris G v w).card ≤ 4 := by
      intro hle
      exact (mem_sdiff.mp hw).2 (mem_filter.mpr ⟨(mem_sdiff.mp hw).1, hle⟩)
    omega
  let center (w : V) : V :=
    if hw : w ∈ C_set then
      have hwH : w ∈ H := (mem_sdiff.mp hw).1
      have hnbr : ∃ u ∈ H, G.Adj w u := by
        by_contra hnone
        push Not at hnone
        exact (mem_sdiff.mp hw).2 (mem_filter.mpr ⟨hwH, hnone⟩)
      let u := Classical.choose hnbr
      let hu := Classical.choose_spec hnbr
      Classical.choose (vTris_star_of_adj G hLoc (mem_sdiff.mp hwH).1
        (mem_sdiff.mp hu.1).1 hu.2 (hH5 w hwH) (hH5 u hu.1))
    else v
  have hcenter_prop : ∀ w ∈ C_set,
      center w ∈ Nv ∧ (∀ e ∈ vTris G v w, center w ∈ e) := by
    intro w hw
    simp only [center, dif_pos hw]
    generalize_proofs h1 h2
    have hsp := Classical.choose_spec h2
    exact ⟨hsp.1, hsp.2.1⟩
  let C_part (c : V) : Finset V := C_set.filter (fun w => center w = c)
  refine ⟨L_set, I_set, C_set, C_part, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext w
    simp only [mem_union, C_set, I_set, H, L_set, mem_sdiff, mem_filter]
    tauto
  · rw [disjoint_left]
    intro w hwL hwI
    exact (mem_sdiff.mp (mem_filter.mp hwI).1).2 hwL
  · rw [disjoint_left]
    intro w hwL hwC
    exact (mem_sdiff.mp (mem_sdiff.mp hwC).1).2 hwL
  · exact disjoint_sdiff_self_right
  · intro w hw
    exact (mem_filter.mp hw).2
  · rw [G.isIndepSet_iff]
    intro x hx y hy _ hadj
    exact (mem_filter.mp hx).2 y (mem_filter.mp hy).1 hadj
  · ext w
    simp only [mem_biUnion, C_part, mem_filter]
    constructor
    · intro hw
      exact ⟨center w, (hcenter_prop w hw).1, hw, rfl⟩
    · rintro ⟨c, _, hw, _⟩
      exact hw
  · intro c₁ _ c₂ _ hne
    refine ⟨?_, ?_⟩
    · rw [disjoint_left]
      intro w hw₁ hw₂
      exact hne ((mem_filter.mp hw₁).2.symm.trans (mem_filter.mp hw₂).2)
    · intro x hx y hy hxy
      have hxC : x ∈ C_set := (mem_filter.mp hx).1
      have hyC : y ∈ C_set := (mem_filter.mp hy).1
      have hxH : x ∈ H := (mem_sdiff.mp hxC).1
      have hyH : y ∈ H := (mem_sdiff.mp hyC).1
      obtain ⟨c, _, hcx, hcy⟩ := vTris_star_of_adj G hLoc
        (mem_sdiff.mp hxH).1 (mem_sdiff.mp hyH).1 hxy (hH5 x hxH) (hH5 y hyH)
      have hc1x : center x = c := by
        by_contra hneq
        have hsub1 : vTris G v x ⊆ {{center x, c}} := by
          intro e he
          rw [mem_singleton]
          refine (eq_of_subset_of_card_le ?_ (by
            rw [(mem_edgesIn.mp (mem_vTris.mp he).1).2.1, card_pair hneq])).symm
          intro z hz
          simp only [mem_insert, mem_singleton] at hz
          rcases hz with rfl | rfl
          · exact (hcenter_prop x hxC).2 e he
          · exact hcx e he
        have := (card_le_card hsub1).trans (by simp : ({{center x, c}} : Finset (Finset V)).card ≤ 1)
        have := hH5 x hxH
        omega
      have hc2y : center y = c := by
        by_contra hneq
        have hsub1 : vTris G v y ⊆ {{center y, c}} := by
          intro e he
          rw [mem_singleton]
          refine (eq_of_subset_of_card_le ?_ (by
            rw [(mem_edgesIn.mp (mem_vTris.mp he).1).2.1, card_pair hneq])).symm
          intro z hz
          simp only [mem_insert, mem_singleton] at hz
          rcases hz with rfl | rfl
          · exact (hcenter_prop y hyC).2 e he
          · exact hcy e he
        have := (card_le_card hsub1).trans (by simp : ({{center y, c}} : Finset (Finset V)).card ≤ 1)
        have := hH5 y hyH
        omega
      exact hne ((mem_filter.mp hx).2.symm.trans (hc1x.trans (hc2y.symm.trans (mem_filter.mp hy).2)))
  · intro c _ w hw e he
    rw [← (mem_filter.mp hw).2]
    exact (hcenter_prop w (mem_filter.mp hw).1).2 e he

end PropertiesAndPartition

section Pruning

variable {V : Type*} [DecidableEq V] [Fintype V]

private def touchingPairs (G : SimpleGraph V) (R : Finset V) : Finset (Finset V) := by
  classical
  exact (edgesIn G Finset.univ).filter (fun e => ∃ v ∈ R, v ∈ e)

private lemma prune_aux (G : SimpleGraph V) (hV : 1 ≤ Fintype.card V) (D₀ : ℝ) (_hD₀ : 0 ≤ D₀) :
    ∀ k : ℕ, ∀ S R : Finset V, S.card = k → Disjoint S R → S ∪ R = Finset.univ →
      ((touchingPairs G R).card : ℝ) ≤ D₀ * (R.card : ℝ) →
      (∃ R' : Finset V, R'.Nonempty ∧ Fintype.card V ≤ 2 * R'.card ∧
        ∑ u ∈ R', ((neighbors G R' u).card : ℝ) ≤ 2 * D₀ * (R'.card : ℝ)) ∨
      (∃ V' : Finset V, V'.Nonempty ∧ Fintype.card V ≤ 2 * V'.card ∧
        ∀ u ∈ V', D₀ < ((neighbors G V' u).card : ℝ)) := by
  classical
  intro k
  induction k with
  | zero =>
    intro S R hSk _ hunion htouch
    have hSe : S = ∅ := card_eq_zero.mp hSk
    rw [hSe, empty_union] at hunion
    have hRcard : R.card = Fintype.card V := by rw [hunion, card_univ]
    have hRn : R.Nonempty := card_pos.mp (by omega)
    have hsub : edgesIn G R ⊆ touchingPairs G R := by
      intro e he
      obtain ⟨heR, he2, hcl⟩ := mem_edgesIn.mp he
      obtain ⟨v, hv⟩ := card_pos.mp (by omega : 0 < e.card)
      exact mem_filter.mpr ⟨mem_edgesIn.mpr ⟨subset_univ e, he2, hcl⟩, v, heR hv, hv⟩
    have hsum : ∑ u ∈ R, ((neighbors G R u).card : ℝ) ≤ 2 * D₀ * (R.card : ℝ) := by
      have hhs : (∑ u ∈ R, ((neighbors G R u).card : ℝ)) = 2 * ((edgesIn G R).card : ℝ) := by
        exact_mod_cast (handshaking_edgesIn G R).symm
      have hle : ((edgesIn G R).card : ℝ) ≤ ((touchingPairs G R).card : ℝ) := by
        exact_mod_cast card_le_card hsub
      linarith
    exact Or.inl ⟨R, hRn, by omega, hsum⟩
  | succ k ih =>
    intro S R hSk hdisj hunion htouch
    by_cases hhalf : 2 * S.card < Fintype.card V
    · have hsum_card : S.card + R.card = Fintype.card V := by
        rw [← card_union_of_disjoint hdisj, hunion, card_univ]
      have hR2 : Fintype.card V ≤ 2 * R.card := by omega
      have hRn : R.Nonempty := card_pos.mp (by omega)
      have hsub : edgesIn G R ⊆ touchingPairs G R := by
        intro e he
        obtain ⟨heR, he2, hcl⟩ := mem_edgesIn.mp he
        obtain ⟨v, hv⟩ := card_pos.mp (by omega : 0 < e.card)
        exact mem_filter.mpr ⟨mem_edgesIn.mpr ⟨subset_univ e, he2, hcl⟩, v, heR hv, hv⟩
      have hsum : ∑ u ∈ R, ((neighbors G R u).card : ℝ) ≤ 2 * D₀ * (R.card : ℝ) := by
        have hhs : (∑ u ∈ R, ((neighbors G R u).card : ℝ)) = 2 * ((edgesIn G R).card : ℝ) := by
          exact_mod_cast (handshaking_edgesIn G R).symm
        have hle : ((edgesIn G R).card : ℝ) ≤ ((touchingPairs G R).card : ℝ) := by
          exact_mod_cast card_le_card hsub
        linarith
      exact Or.inl ⟨R, hRn, hR2, hsum⟩
    · have hS2 : Fintype.card V ≤ 2 * S.card := by omega
      have hSn : S.Nonempty := card_pos.mp (by omega)
      by_cases hdeg : ∀ u ∈ S, D₀ < ((neighbors G S u).card : ℝ)
      · exact Or.inr ⟨S, hSn, hS2, hdeg⟩
      push Not at hdeg
      obtain ⟨u, huS, hule⟩ := hdeg
      let S' := S.erase u
      let R' := insert u R
      have hS'k : S'.card = k := by rw [card_erase_of_mem huS, hSk]; rfl
      have huR : u ∉ R := (disjoint_left.mp hdisj) huS
      have hdisj' : Disjoint S' R' := by
        rw [disjoint_left]
        intro z hzS' hzR'
        rw [mem_erase] at hzS'
        rw [mem_insert] at hzR'
        rcases hzR' with rfl | hzR
        · exact hzS'.1 rfl
        · exact (disjoint_left.mp hdisj) hzS'.2 hzR
      have hunion' : S' ∪ R' = Finset.univ := by
        ext z
        simp only [S', R', mem_union, mem_erase, mem_insert, mem_univ, iff_true]
        by_cases hzu : z = u
        · right; left; exact hzu
        · have hz : z ∈ S ∪ R := hunion ▸ mem_univ z
          rcases mem_union.mp hz with hzS | hzR
          · left; exact ⟨hzu, hzS⟩
          · right; right; exact hzR
      have htouch_sub : touchingPairs G R' ⊆
          touchingPairs G R ∪ (neighbors G S u).image (fun w => ({u, w} : Finset V)) := by
        intro e he
        dsimp [touchingPairs] at he ⊢
        rw [mem_filter] at he
        obtain ⟨heE, v, hvR', hve⟩ := he
        by_cases hexR : ∃ v₀ ∈ R, v₀ ∈ e
        · exact mem_union_left _ (mem_filter.mpr ⟨heE, hexR⟩)
        push Not at hexR
        rw [mem_insert] at hvR'
        rcases hvR' with hvu | hvR
        · rw [hvu] at hve
          obtain ⟨_, he2, hcl⟩ := mem_edgesIn.mp heE
          obtain ⟨a, b, hab, he_eq⟩ := card_eq_two.mp he2
          rw [he_eq] at hve
          simp only [mem_insert, mem_singleton] at hve
          have h_other : ∃ w, w ≠ u ∧ e = {u, w} ∧ G.Adj u w := by
            rcases hve with rfl | rfl
            · exact ⟨b, hab.symm, he_eq, hcl (by rw [he_eq]; simp) (by rw [he_eq]; simp) hab⟩
            · exact ⟨a, hab, by rw [he_eq, pair_comm],
                hcl (by rw [he_eq]; simp) (by rw [he_eq]; simp) hab.symm⟩
          obtain ⟨w, _, heuw, hadj⟩ := h_other
          have hw_not_R : w ∉ R := fun hwR => hexR w hwR (heuw ▸ (by simp))
          have hwS : w ∈ S := by
            have := hunion ▸ mem_univ w
            exact (mem_union.mp this).resolve_right hw_not_R
          exact mem_union_right _ (mem_image.mpr ⟨w, mem_neighbors.mpr ⟨hwS, hadj⟩, heuw.symm⟩)
        · exact False.elim (hexR v hvR hve)
      have htouch' : ((touchingPairs G R').card : ℝ) ≤ D₀ * (R'.card : ℝ) := by
        have hc1 : (touchingPairs G R').card ≤ (touchingPairs G R).card + (neighbors G S u).card :=
          (card_le_card htouch_sub).trans ((card_union_le _ _).trans (Nat.add_le_add_left card_image_le _))
        have hc1' : ((touchingPairs G R').card : ℝ) ≤
            ((touchingPairs G R).card : ℝ) + ((neighbors G S u).card : ℝ) := by exact_mod_cast hc1
        have hR'c : (R'.card : ℝ) = (R.card : ℝ) + 1 := by
          have : R'.card = R.card + 1 := card_insert_of_notMem huR
          exact_mod_cast this
        rw [hR'c]
        nlinarith [htouch, hule]
      exact ih S' R' hS'k hdisj' hunion' htouch'

private lemma prune_min_deg (G : SimpleGraph V) (hV : 1 ≤ Fintype.card V) (α : ℕ) (hα : 1 ≤ α)
    (hInd : ∀ I : Finset V, G.IsIndepSet (I : Set V) → I.card ≤ α) :
    (Fintype.card V : ℝ) ≤ 4 * (α : ℝ) ∨
      ∃ V' : Finset V, V'.Nonempty ∧ Fintype.card V ≤ 2 * V'.card ∧
        ∀ u ∈ V', (Fintype.card V : ℝ) / (8 * (α : ℝ)) < ((neighbors G V' u).card : ℝ) := by
  let D₀ : ℝ := (Fintype.card V : ℝ) / (8 * (α : ℝ))
  have hD₀ : 0 ≤ D₀ := by positivity
  have h0 : ((touchingPairs G ∅).card : ℝ) ≤ D₀ * ((∅ : Finset V).card : ℝ) := by
    have he : touchingPairs G ∅ = ∅ := by
      ext e
      simp [touchingPairs]
    simp [he]
  rcases prune_aux G hV D₀ hD₀ (Fintype.card V) Finset.univ ∅ card_univ
      (disjoint_empty_right _) (union_empty _) h0 with
    ⟨R, hRn, hR2, hsum⟩ | ⟨V', hV'n, hV'2, hdeg⟩
  · left
    have ht := turan_indep G α hα R (fun I _ hI => hInd I hI)
    have hRpos : (0 : ℝ) < (R.card : ℝ) := by exact_mod_cast card_pos.mpr hRn
    have hRhalf : (Fintype.card V : ℝ) / 2 ≤ (R.card : ℝ) := by
      have : (Fintype.card V : ℝ) ≤ 2 * (R.card : ℝ) := by exact_mod_cast hR2
      linarith
    have h2D : 2 * (α : ℝ) * D₀ = (Fintype.card V : ℝ) / 4 := by
      dsimp [D₀]
      have hα0 : (α : ℝ) ≠ 0 := by positivity
      field_simp; ring
    have hRsq : (R.card : ℝ) ^ 2 ≤ (R.card : ℝ) * ((α : ℝ) + (Fintype.card V : ℝ) / 4) := by
      calc
        (R.card : ℝ) ^ 2 ≤ (α : ℝ) * ((R.card : ℝ) + ∑ u ∈ R, ((neighbors G R u).card : ℝ)) := ht
        _ ≤ (α : ℝ) * ((R.card : ℝ) + 2 * D₀ * (R.card : ℝ)) := by
          gcongr
        _ = (R.card : ℝ) * ((α : ℝ) + 2 * (α : ℝ) * D₀) := by ring
        _ = (R.card : ℝ) * ((α : ℝ) + (Fintype.card V : ℝ) / 4) := by rw [h2D]
    have hRle : (R.card : ℝ) ≤ (α : ℝ) + (Fintype.card V : ℝ) / 4 := by
      nlinarith [hRpos, hRsq]
    linarith
  · exact Or.inr ⟨V', hV'n, hV'2, hdeg⟩

end Pruning

section Claim1

variable {V : Type*} [DecidableEq V] [Fintype V]

private lemma ext_subset_N_tri (G : SimpleGraph V) (hK4 : Clique4Free G)
    (V' : Finset V) (outN : V → Finset V)
    (hout_sub : ∀ u ∈ V', outN u ⊆ neighbors G V' u)
    {v u w z : V} (huV' : u ∈ V') (hv_out : v ∈ outN u) (hw_out : w ∈ outN u) (hw_nv : G.Adj v w)
    (hz_out : z ∈ outN u) (hwz : G.Adj w z) (hzv : z ≠ v) :
    z ∈ N_tri G v := by
  have huv_adj : G.Adj u v := (mem_neighbors.mp (hout_sub u huV' hv_out)).2
  have huw_adj : G.Adj u w := (mem_neighbors.mp (hout_sub u huV' hw_out)).2
  have huz_adj : G.Adj u z := (mem_neighbors.mp (hout_sub u huV' hz_out)).2
  have hnvz : ¬ G.Adj v z := by
    intro hvz
    let K : Finset V := {v, u, w, z}
    have hKc : K.card = 4 := by
      rw [card_insert_of_notMem (by simp [huv_adj.ne.symm, hw_nv.ne, hzv.symm]),
          card_insert_of_notMem (by simp [huw_adj.ne, huz_adj.ne]),
          card_pair hwz.ne]
    refine hK4 K hKc ?_
    intro a ha b hb hab
    simp only [K, coe_insert, coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
    rcases ha with rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl
    · exact False.elim (hab rfl)
    · exact huv_adj.symm
    · exact hw_nv
    · exact hvz
    · exact huv_adj
    · exact False.elim (hab rfl)
    · exact huw_adj
    · exact huz_adj
    · exact hw_nv.symm
    · exact huw_adj.symm
    · exact False.elim (hab rfl)
    · exact hwz
    · exact hvz.symm
    · exact huz_adj.symm
    · exact hwz.symm
    · exact False.elim (hab rfl)
  refine mem_N_tri.mpr ⟨hzv, hnvz, ({u, w} : Finset V), ?_, ?_⟩
  · refine mem_edgesIn.mpr ⟨?_, card_pair huw_adj.ne, ?_⟩
    · intro a ha
      simp only [mem_insert, mem_singleton] at ha
      rcases ha with rfl | rfl
      · exact mem_neighbors.mpr ⟨mem_univ _, huv_adj.symm⟩
      · exact mem_neighbors.mpr ⟨mem_univ _, hw_nv⟩
    · intro a ha b hb hab
      simp only [coe_insert, coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
      · exact False.elim (hab rfl)
      · exact huw_adj
      · exact huw_adj.symm
      · exact False.elim (hab rfl)
  · intro a ha
    simp only [mem_insert, mem_singleton] at ha
    rcases ha with rfl | rfl
    · exact huz_adj.symm
    · exact hwz.symm

private lemma indep_of_disjoint_edge_exts (G : SimpleGraph V) (hK4 : Clique4Free G)
    (hLoc : LocalIndep G) (v : V) (M' : Finset (V × V))
    (hM'_nv : ∀ p ∈ M', p.1 ∈ neighbors G Finset.univ v ∧ p.2 ∈ neighbors G Finset.univ v ∧
      G.Adj p.1 p.2)
    (hM'_disj : ∀ p ∈ M', ∀ q ∈ M', p ≠ q →
      p.1 ≠ q.1 ∧ p.1 ≠ q.2 ∧ p.2 ≠ q.1 ∧ p.2 ≠ q.2)
    (N_e : V × V → Finset V)
    (hN_sub : ∀ p ∈ M', N_e p ⊆ N_tri G v ∧ ∀ z ∈ N_e p, G.Adj z p.1 ∧ G.Adj z p.2) :
    G.IsIndepSet (↑(M'.biUnion N_e) : Set V) := by
  rw [G.isIndepSet_iff]
  intro z₁ hz₁ z₂ hz₂ hne
  simp only [mem_coe, mem_biUnion] at hz₁ hz₂
  obtain ⟨p, hp, hzp⟩ := hz₁
  obtain ⟨q, hq, hzq⟩ := hz₂
  by_cases hpq : p = q
  · subst hpq
    intro hadj
    have hz1_adj := (hN_sub p hp).2 z₁ hzp
    have hz2_adj := (hN_sub p hp).2 z₂ hzq
    have hp12 := (hM'_nv p hp).2.2
    have hzp1 : z₁ ≠ p.1 := hz1_adj.1.ne
    have hzp2 : z₁ ≠ p.2 := hz1_adj.2.ne
    have hzq1 : z₂ ≠ p.1 := hz2_adj.1.ne
    have hzq2 : z₂ ≠ p.2 := hz2_adj.2.ne
    let K : Finset V := {p.1, p.2, z₁, z₂}
    have hKc : K.card = 4 := by
      rw [card_insert_of_notMem (by simp [hp12.ne, hzp1.symm, hzq1.symm]),
          card_insert_of_notMem (by simp [hzp2.symm, hzq2.symm]),
          card_pair hne]
    refine hK4 K hKc ?_
    intro a ha b hb hab
    simp only [K, coe_insert, coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
    rcases ha with rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl
    · exact False.elim (hab rfl)
    · exact hp12
    · exact hz1_adj.1.symm
    · exact hz2_adj.1.symm
    · exact hp12.symm
    · exact False.elim (hab rfl)
    · exact hz1_adj.2.symm
    · exact hz2_adj.2.symm
    · exact hz1_adj.1
    · exact hz1_adj.2
    · exact False.elim (hab rfl)
    · exact hadj
    · exact hz2_adj.1
    · exact hz2_adj.2
    · exact hadj.symm
    · exact False.elim (hab rfl)
  · have hd := hM'_disj p hp q hq hpq
    have he1 : ({p.1, p.2} : Finset V) ∈ vTris G v z₁ := by
      refine mem_vTris.mpr ⟨mem_edgesIn.mpr ⟨?_, card_pair (hM'_nv p hp).2.2.ne, ?_⟩, ?_⟩
      · intro a ha
        simp only [mem_insert, mem_singleton] at ha
        rcases ha with rfl | rfl
        · exact (hM'_nv p hp).1
        · exact (hM'_nv p hp).2.1
      · intro a ha b hb hab
        simp only [coe_insert, coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
        rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
        · exact False.elim (hab rfl)
        · exact (hM'_nv p hp).2.2
        · exact (hM'_nv p hp).2.2.symm
        · exact False.elim (hab rfl)
      · intro a ha
        simp only [mem_insert, mem_singleton] at ha
        rcases ha with rfl | rfl
        · exact (hN_sub p hp).2 z₁ hzp |>.1
        · exact (hN_sub p hp).2 z₁ hzp |>.2
    have he2 : ({q.1, q.2} : Finset V) ∈ vTris G v z₂ := by
      refine mem_vTris.mpr ⟨mem_edgesIn.mpr ⟨?_, card_pair (hM'_nv q hq).2.2.ne, ?_⟩, ?_⟩
      · intro a ha
        simp only [mem_insert, mem_singleton] at ha
        rcases ha with rfl | rfl
        · exact (hM'_nv q hq).1
        · exact (hM'_nv q hq).2.1
      · intro a ha b hb hab
        simp only [coe_insert, coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
        rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
        · exact False.elim (hab rfl)
        · exact (hM'_nv q hq).2.2
        · exact (hM'_nv q hq).2.2.symm
        · exact False.elim (hab rfl)
      · intro a ha
        simp only [mem_insert, mem_singleton] at ha
        rcases ha with rfl | rfl
        · exact (hN_sub q hq).2 z₂ hzq |>.1
        · exact (hN_sub q hq).2 z₂ hzq |>.2
    have hdisj : Disjoint ({p.1, p.2} : Finset V) ({q.1, q.2} : Finset V) := by
      rw [disjoint_left]
      intro a ha hb
      simp only [mem_insert, mem_singleton] at ha hb
      rcases ha with ha | ha <;> rcases hb with hb | hb
      · exact hd.1 (ha.symm.trans hb)
      · exact hd.2.1 (ha.symm.trans hb)
      · exact hd.2.2.1 (ha.symm.trans hb)
      · exact hd.2.2.2 (ha.symm.trans hb)
    exact no_adj_disjoint_vTris G hLoc ((hN_sub p hp).1 hzp) ((hN_sub q hq).1 hzq) he1 he2 hdisj

private lemma claim1_per_v (G : SimpleGraph V) (hK4 : Clique4Free G) (hLoc : LocalIndep G)
    (α : ℕ) (hα : 1 ≤ α)
    (hInd : ∀ I : Finset V, G.IsIndepSet (I : Set V) → I.card ≤ α)
    (V' : Finset V) (outN inN : V → Finset V) (commonOut : Finset V → Finset V)
    (hinN_def : ∀ w u, u ∈ inN w ↔ u ∈ V' ∧ w ∈ outN u)
    (hco_def : ∀ e z, z ∈ commonOut e ↔ z ∈ V' ∧ ∀ a ∈ e, z ∈ outN a)
    (hout_sub : ∀ u ∈ V', outN u ⊆ neighbors G V' u)
    (x : ℝ) (hx_pos : 0 < x)
    (hout_exp : ∀ u ∈ V', ∀ A ⊆ outN u, G.IsIndepSet (A : Set V) →
      x * (A.card : ℝ) ≤ ((near G (outN u) A).card : ℝ))
    (x_nat : ℕ) (hx_nat_le : (x_nat : ℝ) ≤ x - 1) (hx_nat_pos : 1 ≤ x_nat)
    (hx_nat_lb : (Fintype.card V : ℝ) / (64 * (α : ℝ) ^ 2) ≤ (x_nat : ℝ))
    (hN3_contra : 16 * 9 * 64 ^ 3 * (α : ℝ) ^ 7 < (Fintype.card V : ℝ) ^ 3)
    (v : V) (hvV' : v ∈ V')
    (hd_lb : (Fintype.card V : ℝ) / (64 * (α : ℝ)) ≤ ((inN v).card : ℝ)) :
    (((inN v).card : ℝ) * (x_nat : ℝ) ^ 2 / 18) ^ 2 / (4 * (α : ℝ) ^ 2) ≤
      ∑ e ∈ edgesIn G (inN v), (((commonOut e).erase v).card : ℝ) := by
  classical
  let n : ℝ := Fintype.card V
  have hn_pos : 0 < n := by
    have : (0 : ℝ) ≤ 16 * 9 * 64 ^ 3 * (α : ℝ) ^ 7 := by positivity
    have hn3 : 0 < n ^ 3 := lt_of_le_of_lt this hN3_contra
    by_contra! hle
    have : n ^ 3 ≤ 0 := by nlinarith [sq_nonneg n]
    linarith
  let Nv := neighbors G Finset.univ v
  have hNv_TF : TriangleFree G Nv := by
    intro a ha b hb c hc hab hbc hac
    let K : Finset V := {v, a, b, c}
    have hva := (mem_neighbors.mp ha).2
    have hvb := (mem_neighbors.mp hb).2
    have hvc := (mem_neighbors.mp hc).2
    have hKc : K.card = 4 := by
      rw [card_insert_of_notMem (by simp [hva.ne, hvb.ne, hvc.ne]),
          card_insert_of_notMem (by simp [hab.ne, hac.ne]), card_pair hbc.ne]
    refine hK4 K hKc ?_
    intro p hp q hq hpq
    simp only [K, coe_insert, coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at hp hq
    rcases hp with rfl | rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl | rfl
    · exact False.elim (hpq rfl)
    · exact hva
    · exact hvb
    · exact hvc
    · exact hva.symm
    · exact False.elim (hpq rfl)
    · exact hab
    · exact hac
    · exact hvb.symm
    · exact hab.symm
    · exact False.elim (hpq rfl)
    · exact hbc
    · exact hvc.symm
    · exact hac.symm
    · exact hbc.symm
    · exact False.elim (hpq rfl)
  let M : Finset (V × V) :=
    (inN v).biUnion (fun u => (neighbors G (outN u) v).image (fun w => (u, w)))
  have hM_mem : ∀ p ∈ M, p.1 ∈ inN v ∧ p.2 ∈ outN p.1 ∧ G.Adj v p.2 := by
    intro p hp
    obtain ⟨u, hu, hpw⟩ := mem_biUnion.mp hp
    obtain ⟨w, hw, rfl⟩ := mem_image.mp hpw
    obtain ⟨hw_out, hvw⟩ := mem_neighbors.mp hw
    exact ⟨hu, hw_out, hvw⟩
  have hM_card : ((inN v).card : ℝ) * (x_nat : ℝ) ≤ (M.card : ℝ) := by
    have hdisj : Set.PairwiseDisjoint (inN v : Set V)
        (fun u => (neighbors G (outN u) v).image (fun w => (u, w))) := by
      intro u₁ _ u₂ _ hne
      change Disjoint _ _
      rw [disjoint_left]
      intro p hp₁ hp₂
      obtain ⟨w₁, _, rfl⟩ := mem_image.mp hp₁
      obtain ⟨w₂, _, heq⟩ := mem_image.mp hp₂
      exact hne (congrArg Prod.fst heq).symm
    have heq_card : M.card = ∑ u ∈ inN v, (neighbors G (outN u) v).card := by
      rw [card_biUnion hdisj]
      refine sum_congr rfl fun u _ => card_image_of_injective _ (fun w₁ w₂ h => congrArg Prod.snd h)
    have heach : ∀ u ∈ inN v, (x_nat : ℝ) ≤ ((neighbors G (outN u) v).card : ℝ) := by
      intro u hu
      obtain ⟨huV', hv_out⟩ := (hinN_def v u).mp hu
      have hind_v : G.IsIndepSet (↑({v} : Finset V) : Set V) := by simp
      have hsub_v : ({v} : Finset V) ⊆ outN u := singleton_subset_iff.mpr hv_out
      have hexp := hout_exp u huV' {v} hsub_v hind_v
      have hnear : near G (outN u) {v} = neighbors G (outN u) v := by simp [near]
      rw [hnear, card_singleton, Nat.cast_one, mul_one] at hexp
      have hxnat_le_x : (x_nat : ℝ) ≤ x := by linarith only [hx_nat_le]
      linarith only [hexp, hxnat_le_x]
    have hsum_r : ((M.card : ℝ)) = ∑ u ∈ inN v, ((neighbors G (outN u) v).card : ℝ) := by
      exact_mod_cast heq_card
    rw [hsum_r]
    calc
      ((inN v).card : ℝ) * (x_nat : ℝ) = ∑ _u ∈ inN v, (x_nat : ℝ) := by
        rw [sum_const, nsmul_eq_mul]
      _ ≤ ∑ u ∈ inN v, ((neighbors G (outN u) v).card : ℝ) := sum_le_sum heach
  let ext₁ (p : V × V) : Finset V := (neighbors G (outN p.1) p.2).erase v
  have hext_card : ∀ p ∈ M, x_nat ≤ (ext₁ p).card := by
    intro p hp
    obtain ⟨hu_in, hw_out, _⟩ := hM_mem p hp
    have huV' : p.1 ∈ V' := ((hinN_def v p.1).mp hu_in).1
    have hind_w : G.IsIndepSet (↑({p.2} : Finset V) : Set V) := by simp
    have hexp := hout_exp p.1 huV' {p.2} (singleton_subset_iff.mpr hw_out) hind_w
    have hnear : near G (outN p.1) {p.2} = neighbors G (outN p.1) p.2 := by simp [near]
    rw [hnear, card_singleton, Nat.cast_one, mul_one] at hexp
    have hc : (x_nat : ℝ) ≤ ((ext₁ p).card : ℝ) := by
      have hsub_nat : (neighbors G (outN p.1) p.2).card - 1 ≤ (ext₁ p).card :=
        card_erase_ge_sub_one _ _
      have hsub : ((neighbors G (outN p.1) p.2).card : ℝ) - 1 ≤ ((ext₁ p).card : ℝ) := by
        by_cases h0 : (neighbors G (outN p.1) p.2).card = 0
        · rw [h0] at hexp; rw [Nat.cast_zero] at hexp; linarith only [hx_pos, hexp]
        · have h1 : 1 ≤ (neighbors G (outN p.1) p.2).card := Nat.pos_of_ne_zero h0
          have hcast : (((neighbors G (outN p.1) p.2).card - 1 : ℕ) : ℝ) =
              ((neighbors G (outN p.1) p.2).card : ℝ) - 1 := by
            rw [Nat.cast_sub h1]; norm_num
          rw [← hcast]
          exact_mod_cast hsub_nat
      linarith only [hx_nat_le, hexp, hsub]
    exact_mod_cast hc
  have hext_sub : ∀ p ∈ M, ext₁ p ⊆ N_tri G v := by
    intro p hp z hz
    obtain ⟨hu_in, hw_out, hvw⟩ := hM_mem p hp
    obtain ⟨huV', hv_out⟩ := (hinN_def v p.1).mp hu_in
    have hzv : z ≠ v := (mem_erase.mp hz).1
    obtain ⟨hz_out, hwz⟩ := mem_neighbors.mp (mem_of_mem_erase hz)
    exact ext_subset_N_tri G hK4 V' outN hout_sub huV' hv_out hw_out hvw hz_out hwz hzv
  obtain ⟨L_set, I_set, C_set, C_part, hUnion, hLI, hLC, hIC, hL4, hIind, hC_biU, hC_disj, hC_ctr⟩ :=
    partition_N_tri G hLoc v
  let M_C := M.filter (fun p => x_nat ≤ 3 * (ext₁ p ∩ C_set).card)
  let M_L := (M \ M_C).filter (fun p => x_nat ≤ 3 * (ext₁ p ∩ L_set).card)
  let M_I := (M \ M_C) \ M_L
  have hM_split : M.card = M_C.card + M_L.card + M_I.card := by
    have h1 : M.card = M_C.card + (M \ M_C).card :=
      (card_sdiff_add_card_inter M M_C).symm.trans (by
        rw [inter_eq_right.mpr (filter_subset _ _), add_comm])
    have h2 : (M \ M_C).card = M_L.card + M_I.card :=
      (card_sdiff_add_card_inter (M \ M_C) M_L).symm.trans (by
        rw [inter_eq_right.mpr (filter_subset _ _), add_comm])
    omega
  have hM_I_prop : ∀ p ∈ M_I, x_nat ≤ 3 * (ext₁ p ∩ I_set).card := by
    intro p hp
    have hp_not_L : ¬ x_nat ≤ 3 * (ext₁ p ∩ L_set).card := by
      intro hle
      exact (mem_sdiff.mp hp).2 (mem_filter.mpr ⟨(mem_sdiff.mp hp).1, hle⟩)
    have hp_not_C : ¬ x_nat ≤ 3 * (ext₁ p ∩ C_set).card := by
      intro hle
      exact (mem_sdiff.mp (mem_sdiff.mp hp).1).2
        (mem_filter.mpr ⟨(mem_sdiff.mp (mem_sdiff.mp hp).1).1, hle⟩)
    have hpM : p ∈ M := (mem_sdiff.mp (mem_sdiff.mp hp).1).1
    have hpart_ext : (ext₁ p).card =
        (ext₁ p ∩ L_set).card + (ext₁ p ∩ I_set).card + (ext₁ p ∩ C_set).card := by
      have hsub : ext₁ p ⊆ L_set ∪ I_set ∪ C_set := hUnion ▸ hext_sub p hpM
      have h_eq : ext₁ p = (ext₁ p ∩ L_set) ∪ (ext₁ p ∩ I_set) ∪ (ext₁ p ∩ C_set) := by
        ext z
        simp only [mem_union, mem_inter]
        constructor
        · intro hz
          have h1 := hsub hz
          simp only [mem_union] at h1
          tauto
        · intro h
          tauto
      have hd1 : Disjoint (ext₁ p ∩ L_set) (ext₁ p ∩ I_set) :=
        Disjoint.mono inter_subset_right inter_subset_right hLI
      have hd2 : Disjoint (ext₁ p ∩ L_set ∪ ext₁ p ∩ I_set) (ext₁ p ∩ C_set) :=
        Disjoint.mono
          (union_subset (inter_subset_right.trans subset_union_left)
            (inter_subset_right.trans subset_union_right))
          inter_subset_right (disjoint_union_left.mpr ⟨hLC, hIC⟩)
      exact (congrArg Finset.card h_eq).trans
        ((card_union_of_disjoint hd2).trans
          (congrArg (· + (ext₁ p ∩ C_set).card) (card_union_of_disjoint hd1)))
    have hge := hext_card p hpM
    omega
  have hcases : M.card ≤ 3 * M_C.card ∨ M.card ≤ 3 * M_L.card ∨ M.card ≤ 3 * M_I.card := by
    omega
  rcases hcases with hC_maj | hL_maj | hI_maj
  · -- Case 1: type C
    exfalso
    have hMC_nv : ∀ p ∈ M_C, p.1 ∈ Nv ∧ p.2 ∈ Nv ∧ G.Adj p.1 p.2 := by
      intro p hp
      obtain ⟨hu_in, hw_out, hvw⟩ := hM_mem p (filter_subset _ _ hp)
      obtain ⟨huV', hv_out⟩ := (hinN_def v p.1).mp hu_in
      have huv : G.Adj v p.1 := (mem_neighbors.mp (hout_sub p.1 huV' hv_out)).2.symm
      have huw : G.Adj p.1 p.2 := (mem_neighbors.mp (hout_sub p.1 huV' hw_out)).2
      exact ⟨mem_neighbors.mpr ⟨mem_univ _, huv⟩, mem_neighbors.mpr ⟨mem_univ _, hvw⟩, huw⟩
    obtain ⟨M', hM'sub, hM'disj, hM'card⟩ :=
      greedy_matching_of_directed G Nv α hNv_TF (fun I _ hI => hInd I hI) M_C hMC_nv
    let N_e (p : V × V) : Finset V := ext₁ p ∩ C_set
    have hN_sub : ∀ p ∈ M', N_e p ⊆ N_tri G v ∧ ∀ z ∈ N_e p, G.Adj z p.1 ∧ G.Adj z p.2 := by
      intro p hp
      have hpM : p ∈ M := filter_subset _ _ (hM'sub hp)
      refine ⟨inter_subset_left.trans (hext_sub p hpM), fun z hz => ?_⟩
      have hz' := mem_of_mem_erase (mem_inter.mp hz).1
      have huV' : p.1 ∈ V' := ((hinN_def v p.1).mp (hM_mem p hpM).1).1
      have huz : G.Adj p.1 z := (mem_neighbors.mp (hout_sub p.1 huV' (mem_neighbors.mp hz').1)).2
      have hwz : G.Adj p.2 z := (mem_neighbors.mp hz').2
      exact ⟨huz.symm, hwz.symm⟩
    have hind_U : G.IsIndepSet (↑(M'.biUnion N_e) : Set V) :=
      indep_of_disjoint_edge_exts G hK4 hLoc v M' (fun p hp => hMC_nv p (hM'sub hp))
        hM'disj N_e hN_sub
    have hdisj_N : Set.PairwiseDisjoint (M' : Set (V × V)) N_e := by
      intro p hp q hq hpq
      change Disjoint _ _
      rw [disjoint_left]
      intro z hzp hzq
      have hzC : z ∈ C_set := (mem_inter.mp hzp).2
      rw [hC_biU] at hzC
      obtain ⟨c, hcNv, hzc⟩ := mem_biUnion.mp hzC
      have hep : ({p.1, p.2} : Finset V) ∈ vTris G v z := by
        refine mem_vTris.mpr ⟨mem_edgesIn.mpr ⟨?_, card_pair (hMC_nv p (hM'sub hp)).2.2.ne, ?_⟩, ?_⟩
        · intro a ha; simp only [mem_insert, mem_singleton] at ha
          rcases ha with rfl | rfl; exact (hMC_nv p (hM'sub hp)).1; exact (hMC_nv p (hM'sub hp)).2.1
        · intro a ha b hb hab
          simp only [coe_insert, coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
          rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
          · exact False.elim (hab rfl)
          · exact (hMC_nv p (hM'sub hp)).2.2
          · exact (hMC_nv p (hM'sub hp)).2.2.symm
          · exact False.elim (hab rfl)
        · intro a ha; simp only [mem_insert, mem_singleton] at ha
          rcases ha with rfl | rfl; exact (hN_sub p hp).2 z hzp |>.1; exact (hN_sub p hp).2 z hzp |>.2
      have heq : ({q.1, q.2} : Finset V) ∈ vTris G v z := by
        refine mem_vTris.mpr ⟨mem_edgesIn.mpr ⟨?_, card_pair (hMC_nv q (hM'sub hq)).2.2.ne, ?_⟩, ?_⟩
        · intro a ha; simp only [mem_insert, mem_singleton] at ha
          rcases ha with rfl | rfl; exact (hMC_nv q (hM'sub hq)).1; exact (hMC_nv q (hM'sub hq)).2.1
        · intro a ha b hb hab
          simp only [coe_insert, coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
          rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
          · exact False.elim (hab rfl)
          · exact (hMC_nv q (hM'sub hq)).2.2
          · exact (hMC_nv q (hM'sub hq)).2.2.symm
          · exact False.elim (hab rfl)
        · intro a ha; simp only [mem_insert, mem_singleton] at ha
          rcases ha with rfl | rfl; exact (hN_sub q hq).2 z hzq |>.1; exact (hN_sub q hq).2 z hzq |>.2
      have hcp := hC_ctr c hcNv z hzc _ hep
      have hcq := hC_ctr c hcNv z hzc _ heq
      have hd := hM'disj p hp q hq hpq
      simp only [mem_insert, mem_singleton] at hcp hcq
      rcases hcp with hcp | hcp <;> rcases hcq with hcq | hcq
      · exact hd.1 (hcp.symm.trans hcq)
      · exact hd.2.1 (hcp.symm.trans hcq)
      · exact hd.2.2.1 (hcp.symm.trans hcq)
      · exact hd.2.2.2 (hcp.symm.trans hcq)
    have hU_le : ((M'.biUnion N_e).card : ℝ) ≤ (α : ℝ) := by
      exact_mod_cast hInd _ hind_U
    have hU_ge : (M'.card : ℝ) * (x_nat : ℝ) / 3 ≤ ((M'.biUnion N_e).card : ℝ) := by
      have hnat : (M'.biUnion N_e).card = ∑ p ∈ M', (N_e p).card := card_biUnion hdisj_N
      have hreal : ((M'.biUnion N_e).card : ℝ) = ∑ p ∈ M', ((N_e p).card : ℝ) := by exact_mod_cast hnat
      rw [hreal]
      calc
        (M'.card : ℝ) * (x_nat : ℝ) / 3 = ∑ _p ∈ M', ((x_nat : ℝ) / 3) := by
          rw [sum_const, nsmul_eq_mul]; ring
        _ ≤ ∑ p ∈ M', ((N_e p).card : ℝ) := by
          refine sum_le_sum fun p hp => ?_
          have h3 : (x_nat : ℝ) ≤ 3 * ((N_e p).card : ℝ) := by
            exact_mod_cast (mem_filter.mp (hM'sub hp)).2
          linarith only [h3]
    have hM_le : (M.card : ℝ) ≤ 12 * (α : ℝ) * (M'.card : ℝ) := by
      have h1 : (M.card : ℝ) ≤ 3 * (M_C.card : ℝ) := by exact_mod_cast hC_maj
      have h2 : (M_C.card : ℝ) ≤ 4 * (α : ℝ) * (M'.card : ℝ) := by exact_mod_cast hM'card
      nlinarith only [h1, h2, (by positivity : (0 : ℝ) ≤ (α : ℝ))]
    have hchain : n ^ 3 / (64 ^ 3 * (α : ℝ) ^ 5) ≤ (M.card : ℝ) * (x_nat : ℝ) := by
      have h1 : n / (64 * (α : ℝ)) * (x_nat : ℝ) ≤ (M.card : ℝ) :=
        le_trans (mul_le_mul_of_nonneg_right hd_lb (by positivity)) hM_card
      have h2 : n / (64 * (α : ℝ)) * (x_nat : ℝ) ^ 2 ≤ (M.card : ℝ) * (x_nat : ℝ) := by
        nlinarith only [h1, (by positivity : 0 ≤ (x_nat : ℝ))]
      have h3 : n / (64 * (α : ℝ)) * (n / (64 * (α : ℝ) ^ 2)) ^ 2 ≤
          n / (64 * (α : ℝ)) * (x_nat : ℝ) ^ 2 := by
        have hnl : n / (64 * (α : ℝ) ^ 2) ≤ (x_nat : ℝ) := hx_nat_lb
        gcongr
      calc
        n ^ 3 / (64 ^ 3 * (α : ℝ) ^ 5) = n / (64 * (α : ℝ)) * (n / (64 * (α : ℝ) ^ 2)) ^ 2 := by
          ring
        _ ≤ (M.card : ℝ) * (x_nat : ℝ) := h3.trans h2
    have hbad1 : (M.card : ℝ) * (x_nat : ℝ) ≤ 36 * (α : ℝ) ^ 2 := by
      have hα0 : 0 ≤ (α : ℝ) := by positivity
      have hx0 : 0 ≤ (x_nat : ℝ) := by positivity
      have hMx : (M'.card : ℝ) * (x_nat : ℝ) ≤ 3 * (α : ℝ) := by linarith only [hU_le, hU_ge]
      calc
        (M.card : ℝ) * (x_nat : ℝ) ≤ (12 * (α : ℝ) * (M'.card : ℝ)) * (x_nat : ℝ) :=
          mul_le_mul_of_nonneg_right hM_le hx0
        _ = 12 * (α : ℝ) * ((M'.card : ℝ) * (x_nat : ℝ)) := by ring
        _ ≤ 12 * (α : ℝ) * (3 * (α : ℝ)) := by gcongr
        _ = 36 * (α : ℝ) ^ 2 := by ring
    have hcontra : n ^ 3 ≤ 36 * 64 ^ 3 * (α : ℝ) ^ 7 := by
      have hdiv : n ^ 3 / (64 ^ 3 * (α : ℝ) ^ 5) ≤ 36 * (α : ℝ) ^ 2 := hchain.trans hbad1
      rw [div_le_iff₀ (by positivity)] at hdiv
      linarith only [hdiv, show (36 * (α : ℝ) ^ 2) * (64 ^ 3 * (α : ℝ) ^ 5) =
        36 * 64 ^ 3 * (α : ℝ) ^ 7 by ring]
    have hcmp : 36 * 64 ^ 3 * (α : ℝ) ^ 7 ≤ 16 * 9 * 64 ^ 3 * (α : ℝ) ^ 7 :=
      mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
    linarith only [hcontra, hN3_contra, hcmp]
  · -- Case 2: type L
    exfalso
    have hsum_L : ∑ p ∈ M_L, (ext₁ p ∩ L_set).card ≤ 8 * L_set.card := by
      have h1 : ∑ p ∈ M_L, (ext₁ p ∩ L_set).card =
          ∑ p ∈ M_L, ∑ z ∈ L_set, if z ∈ ext₁ p then 1 else 0 := by
        refine sum_congr rfl fun p _ => ?_
        rw [sum_boole, Nat.cast_id]
        congr 1
        ext z; rw [mem_filter, mem_inter]; tauto
      rw [h1, sum_comm]
      calc
        ∑ z ∈ L_set, ∑ p ∈ M_L, (if z ∈ ext₁ p then 1 else 0)
          = ∑ z ∈ L_set, (M_L.filter (fun p => z ∈ ext₁ p)).card := by
            refine sum_congr rfl fun z _ => ?_
            rw [sum_boole, Nat.cast_id]
        _ ≤ ∑ _z ∈ L_set, 8 := by
            refine sum_le_sum fun z hz => ?_
            let F := M_L.filter (fun p => z ∈ ext₁ p)
            have hF_map : F ⊆ (vTris G v z).biUnion (fun e =>
                (e ×ˢ e).filter (fun p => p.1 ≠ p.2)) := by
              intro p hp
              obtain ⟨hpML, hzp⟩ := mem_filter.mp hp
              have hpM : p ∈ M := (mem_sdiff.mp (mem_filter.mp hpML).1).1
              obtain ⟨hu_in, hw_out, hvw⟩ := hM_mem p hpM
              obtain ⟨huV', hv_out⟩ := (hinN_def v p.1).mp hu_in
              have huv : G.Adj v p.1 := (mem_neighbors.mp (hout_sub p.1 huV' hv_out)).2.symm
              have huw : G.Adj p.1 p.2 := (mem_neighbors.mp (hout_sub p.1 huV' hw_out)).2
              have hz' := mem_of_mem_erase hzp
              have huz : G.Adj p.1 z := (mem_neighbors.mp (hout_sub p.1 huV' (mem_neighbors.mp hz').1)).2
              have hwz : G.Adj p.2 z := (mem_neighbors.mp hz').2
              refine mem_biUnion.mpr ⟨{p.1, p.2}, ?_, ?_⟩
              · refine mem_vTris.mpr ⟨mem_edgesIn.mpr ⟨?_, card_pair huw.ne, ?_⟩, ?_⟩
                · intro a ha; simp only [mem_insert, mem_singleton] at ha
                  rcases ha with rfl | rfl
                  · exact mem_neighbors.mpr ⟨mem_univ _, huv⟩
                  · exact mem_neighbors.mpr ⟨mem_univ _, hvw⟩
                · intro a ha b hb hab
                  simp only [coe_insert, coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
                  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
                  · exact False.elim (hab rfl)
                  · exact huw
                  · exact huw.symm
                  · exact False.elim (hab rfl)
                · intro a ha; simp only [mem_insert, mem_singleton] at ha
                  rcases ha with rfl | rfl
                  · exact huz.symm
                  · exact hwz.symm
              · rw [mem_filter, mem_product]
                exact ⟨⟨by simp, by simp⟩, huw.ne⟩
            have hF_le : F.card ≤ ∑ e ∈ vTris G v z, ((e ×ˢ e).filter (fun p => p.1 ≠ p.2)).card :=
              (card_le_card hF_map).trans card_biUnion_le
            have heach : ∀ e ∈ vTris G v z, ((e ×ˢ e).filter (fun p => p.1 ≠ p.2)).card ≤ 2 := by
              intro e he
              obtain ⟨a, b, hab, rfl⟩ := card_eq_two.mp (mem_edgesIn.mp (mem_vTris.mp he).1).2.1
              have hsub : ({a, b} ×ˢ ({a, b} : Finset V)).filter (fun p => p.1 ≠ p.2) ⊆
                  {(a, b), (b, a)} := by
                intro p hp
                rw [mem_filter, mem_product] at hp
                simp only [mem_insert, mem_singleton] at hp ⊢
                rcases hp.1.1 with h1 | h1 <;> rcases hp.1.2 with h2 | h2
                · exact absurd (h1.trans h2.symm) hp.2
                · left; exact Prod.ext h1 h2
                · right; exact Prod.ext h1 h2
                · exact absurd (h1.trans h2.symm) hp.2
              exact (card_le_card hsub).trans card_le_two
            calc
              F.card ≤ ∑ _e ∈ vTris G v z, 2 := hF_le.trans (sum_le_sum heach)
              _ = (vTris G v z).card * 2 := by simp
              _ ≤ 4 * 2 := Nat.mul_le_mul_right 2 (hL4 z hz)
              _ = 8 := by decide
        _ = 8 * L_set.card := by rw [sum_const, smul_eq_mul]; ring
    have hL_TF : TriangleFree G L_set :=
      triangleFree_subset (N_tri_triangle_free G hK4 hLoc v)
        (fun w hw => (hUnion ▸ mem_union_left _ (mem_union_left _ hw) : w ∈ N_tri G v))
    obtain ⟨I_L, _, hI_L, hL_bound⟩ := card_triangle_free_subset G L_set hL_TF
    have hL_le2 : L_set.card ≤ 2 * α ^ 2 :=
      hL_bound.trans (Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left (hInd I_L hI_L) 2))
    have hML_bound : (M_L.card : ℝ) * (x_nat : ℝ) / 3 ≤ 8 * (L_set.card : ℝ) := by
      have h1 : (M_L.card : ℝ) * ((x_nat : ℝ) / 3) ≤
          ∑ p ∈ M_L, ((ext₁ p ∩ L_set).card : ℝ) := by
        rw [← nsmul_eq_mul, ← sum_const]
        refine sum_le_sum fun p hp => ?_
        have h3 : (x_nat : ℝ) ≤ 3 * ((ext₁ p ∩ L_set).card : ℝ) := by
          exact_mod_cast (mem_filter.mp hp).2
        linarith only [h3]
      have h2 : (∑ p ∈ M_L, ((ext₁ p ∩ L_set).card : ℝ)) ≤ 8 * (L_set.card : ℝ) := by
        exact_mod_cast hsum_L
      linarith only [h1, h2]
    have hchain : n ^ 3 / (64 ^ 3 * (α : ℝ) ^ 5) ≤ (M.card : ℝ) * (x_nat : ℝ) := by
      have h1 : n / (64 * (α : ℝ)) * (x_nat : ℝ) ≤ (M.card : ℝ) :=
        le_trans (mul_le_mul_of_nonneg_right hd_lb (by positivity)) hM_card
      have h2 : n / (64 * (α : ℝ)) * (x_nat : ℝ) ^ 2 ≤ (M.card : ℝ) * (x_nat : ℝ) := by
        nlinarith only [h1, (by positivity : 0 ≤ (x_nat : ℝ))]
      have h3 : n / (64 * (α : ℝ)) * (n / (64 * (α : ℝ) ^ 2)) ^ 2 ≤
          n / (64 * (α : ℝ)) * (x_nat : ℝ) ^ 2 := by
        have hnl : n / (64 * (α : ℝ) ^ 2) ≤ (x_nat : ℝ) := hx_nat_lb
        gcongr
      calc
        n ^ 3 / (64 ^ 3 * (α : ℝ) ^ 5) = n / (64 * (α : ℝ)) * (n / (64 * (α : ℝ) ^ 2)) ^ 2 := by
          ring
        _ ≤ (M.card : ℝ) * (x_nat : ℝ) := h3.trans h2
    have hM_le : (M.card : ℝ) * (x_nat : ℝ) ≤ 72 * (L_set.card : ℝ) := by
      have h3 : (M.card : ℝ) ≤ 3 * (M_L.card : ℝ) := by exact_mod_cast hL_maj
      nlinarith only [h3, hML_bound, (by positivity : 0 ≤ (x_nat : ℝ))]
    have hL_leR : (L_set.card : ℝ) ≤ 2 * (α : ℝ) ^ 2 := by exact_mod_cast hL_le2
    have hcontra : n ^ 3 ≤ 144 * 64 ^ 3 * (α : ℝ) ^ 7 := by
      have hdiv : n ^ 3 / (64 ^ 3 * (α : ℝ) ^ 5) ≤ 144 * (α : ℝ) ^ 2 := by
        linarith only [hchain, hM_le, hL_leR]
      rw [div_le_iff₀ (by positivity)] at hdiv
      linarith only [hdiv, show (144 * (α : ℝ) ^ 2) * (64 ^ 3 * (α : ℝ) ^ 5) =
        144 * 64 ^ 3 * (α : ℝ) ^ 7 by ring]
    have hcmp : 144 * 64 ^ 3 * (α : ℝ) ^ 7 = 16 * 9 * 64 ^ 3 * (α : ℝ) ^ 7 := by ring
    linarith only [hcontra, hN3_contra, hcmp]
  · -- Case 3: type I
    let T_u (u : V) : Finset V := (neighbors G (outN u) v).filter (fun w => (u, w) ∈ M_I)
    have hMI_sum : M_I.card = ∑ u ∈ inN v, (T_u u).card := by
      have hMI_sub : M_I ⊆ M := (sdiff_subset.trans sdiff_subset)
      have hdisj : Set.PairwiseDisjoint (inN v : Set V)
          (fun u => (T_u u).image (fun w => (u, w))) := by
        intro u₁ _ u₂ _ hne
        change Disjoint _ _
        rw [disjoint_left]
        intro p hp₁ hp₂
        obtain ⟨w₁, _, rfl⟩ := mem_image.mp hp₁
        obtain ⟨w₂, _, heq⟩ := mem_image.mp hp₂
        exact hne (congrArg Prod.fst heq).symm
      have heq : M_I = (inN v).biUnion (fun u => (T_u u).image (fun w => (u, w))) := by
        ext p
        rw [mem_biUnion]
        constructor
        · intro hp
          have hpM := hMI_sub hp
          obtain ⟨u, hu, hpw⟩ := mem_biUnion.mp hpM
          obtain ⟨w, hw, rfl⟩ := mem_image.mp hpw
          exact ⟨u, hu, mem_image.mpr ⟨w, mem_filter.mpr ⟨hw, hp⟩, rfl⟩⟩
        · rintro ⟨u, _, hpw⟩
          obtain ⟨w, hw, rfl⟩ := mem_image.mp hpw
          exact (mem_filter.mp hw).2
      rw [heq, card_biUnion hdisj]
      refine sum_congr rfl fun u _ => card_image_of_injective _ (fun w₁ w₂ h => congrArg Prod.snd h)
    let B_u (u : V) : Finset V := (near G (outN u) (T_u u)).erase v
    have hB_in_I : ∀ u ∈ inN v, ((T_u u).card : ℝ) * (x_nat : ℝ) / 3 ≤ ((B_u u ∩ I_set).card : ℝ) := by
      intro u hu
      rcases (T_u u).eq_empty_or_nonempty with hTe | hTne
      · rw [hTe, card_empty, Nat.cast_zero, zero_mul, zero_div]
        exact Nat.cast_nonneg _
      obtain ⟨huV', hv_out⟩ := (hinN_def v u).mp hu
      have hTu_ind : G.IsIndepSet (↑(T_u u) : Set V) := by
        have hsub : T_u u ⊆ neighbors G Nv u := by
          intro w hw
          have hw_nbr := (mem_filter.mp hw).1
          have hw_out := (mem_neighbors.mp hw_nbr).1
          have hw_v := (mem_neighbors.mp hw_nbr).2
          exact mem_neighbors.mpr ⟨mem_neighbors.mpr ⟨mem_univ _, hw_v⟩,
            (mem_neighbors.mp (hout_sub u huV' hw_out)).2⟩
        have hu_nv : u ∈ Nv := mem_neighbors.mpr ⟨mem_univ _, (mem_neighbors.mp (hout_sub u huV' hv_out)).2.symm⟩
        exact indep_mono hsub (triangleFree_neighbors_indep hNv_TF hu_nv)
      have hTu_sub : T_u u ⊆ outN u := fun w hw => (mem_neighbors.mp (mem_filter.mp hw).1).1
      have hexp := hout_exp u huV' (T_u u) hTu_sub hTu_ind
      have hBu_ge : ((T_u u).card : ℝ) * (x_nat : ℝ) ≤ ((B_u u).card : ℝ) := by
        have h1 : (near G (outN u) (T_u u)).card - 1 ≤ (B_u u).card :=
          card_erase_ge_sub_one _ _
        have hnear_pos : 1 ≤ (near G (outN u) (T_u u)).card := by
          have hT1 : (1 : ℝ) ≤ ((T_u u).card : ℝ) := by exact_mod_cast card_pos.mpr hTne
          have hx1 : (1 : ℝ) ≤ x := by linarith only [hx_nat_le, (by exact_mod_cast hx_nat_pos : (1 : ℝ) ≤ (x_nat : ℝ))]
          have : (1 : ℝ) ≤ ((near G (outN u) (T_u u)).card : ℝ) := by nlinarith only [hT1, hx1, hexp]
          exact_mod_cast this
        have hsub_r : ((near G (outN u) (T_u u)).card : ℝ) - 1 ≤ ((B_u u).card : ℝ) := by
          have hcast : (((near G (outN u) (T_u u)).card - 1 : ℕ) : ℝ) =
              ((near G (outN u) (T_u u)).card : ℝ) - 1 := by
            rw [Nat.cast_sub hnear_pos]; norm_num
          rw [← hcast]
          exact_mod_cast h1
        have hT1 : (1 : ℝ) ≤ ((T_u u).card : ℝ) := by exact_mod_cast card_pos.mpr hTne
        calc
          ((T_u u).card : ℝ) * (x_nat : ℝ) ≤ ((T_u u).card : ℝ) * (x - 1) :=
            mul_le_mul_of_nonneg_left hx_nat_le (Nat.cast_nonneg _)
          _ = x * ((T_u u).card : ℝ) - ((T_u u).card : ℝ) := by ring
          _ ≤ x * ((T_u u).card : ℝ) - 1 := by linarith only [hT1]
          _ ≤ ((near G (outN u) (T_u u)).card : ℝ) - 1 := by linarith only [hexp]
          _ ≤ ((B_u u).card : ℝ) := hsub_r
      have hBu_sdiff : B_u u \ I_set ⊆ (T_u u).biUnion (fun w => ext₁ (u, w) \ I_set) := by
        intro z hz
        obtain ⟨hzB, hzI⟩ := mem_sdiff.mp hz
        have hzv : z ≠ v := (mem_erase.mp hzB).1
        obtain ⟨hz_out, w, hwT, hwz⟩ := mem_near.mp (mem_of_mem_erase hzB)
        exact mem_biUnion.mpr ⟨w, hwT, mem_sdiff.mpr ⟨mem_erase.mpr ⟨hzv, mem_neighbors.mpr ⟨hz_out, hwz⟩⟩, hzI⟩⟩
      have h_nonI_le : ∀ w ∈ T_u u, ((ext₁ (u, w) \ I_set).card : ℝ) ≤ 2 * (x_nat : ℝ) / 3 := by
        intro w hwT
        have hw_MI : (u, w) ∈ M_I := (mem_filter.mp hwT).2
        have hw_M : (u, w) ∈ M := (sdiff_subset.trans sdiff_subset) hw_MI
        have hnotC : ¬ x_nat ≤ 3 * (ext₁ (u, w) ∩ C_set).card := by
          intro hle
          exact (mem_sdiff.mp (mem_sdiff.mp hw_MI).1).2
            (mem_filter.mpr ⟨(mem_sdiff.mp (mem_sdiff.mp hw_MI).1).1, hle⟩)
        have hnotL : ¬ x_nat ≤ 3 * (ext₁ (u, w) ∩ L_set).card := by
          intro hle
          exact (mem_sdiff.mp hw_MI).2 (mem_filter.mpr ⟨(mem_sdiff.mp hw_MI).1, hle⟩)
        have hsub_CL : ext₁ (u, w) \ I_set ⊆ (ext₁ (u, w) ∩ C_set) ∪ (ext₁ (u, w) ∩ L_set) := by
          intro z hz
          obtain ⟨hz1, hzI⟩ := mem_sdiff.mp hz
          have hzN : z ∈ N_tri G v := hext_sub (u, w) hw_M hz1
          rw [← hUnion] at hzN
          simp only [mem_union] at hzN
          rcases hzN with (hzL | hzI') | hzC
          · exact mem_union_right _ (mem_inter.mpr ⟨hz1, hzL⟩)
          · exact False.elim (hzI hzI')
          · exact mem_union_left _ (mem_inter.mpr ⟨hz1, hzC⟩)
        have hcle : (ext₁ (u, w) \ I_set).card ≤
            (ext₁ (u, w) ∩ C_set).card + (ext₁ (u, w) ∩ L_set).card :=
          (card_le_card hsub_CL).trans (card_union_le _ _)
        have hcleR : ((ext₁ (u, w) \ I_set).card : ℝ) ≤
            ((ext₁ (u, w) ∩ C_set).card : ℝ) + ((ext₁ (u, w) ∩ L_set).card : ℝ) := by
          exact_mod_cast hcle
        have hC_lt : 3 * ((ext₁ (u, w) ∩ C_set).card : ℝ) < (x_nat : ℝ) := by
          exact_mod_cast Nat.lt_of_not_le hnotC
        have hL_lt : 3 * ((ext₁ (u, w) ∩ L_set).card : ℝ) < (x_nat : ℝ) := by
          exact_mod_cast Nat.lt_of_not_le hnotL
        linarith only [hcleR, hC_lt, hL_lt]
      have hBu_sdiff_le : ((B_u u \ I_set).card : ℝ) ≤ ((T_u u).card : ℝ) * (2 * (x_nat : ℝ) / 3) := by
        have h1 : (B_u u \ I_set).card ≤ ∑ w ∈ T_u u, (ext₁ (u, w) \ I_set).card :=
          (card_le_card hBu_sdiff).trans card_biUnion_le
        have h1r : ((B_u u \ I_set).card : ℝ) ≤ ∑ w ∈ T_u u, ((ext₁ (u, w) \ I_set).card : ℝ) := by
          exact_mod_cast h1
        calc
          ((B_u u \ I_set).card : ℝ) ≤ ∑ w ∈ T_u u, ((ext₁ (u, w) \ I_set).card : ℝ) := h1r
          _ ≤ ∑ _w ∈ T_u u, (2 * (x_nat : ℝ) / 3) := sum_le_sum h_nonI_le
          _ = ((T_u u).card : ℝ) * (2 * (x_nat : ℝ) / 3) := by rw [sum_const, nsmul_eq_mul]
      have hpartB : ((B_u u).card : ℝ) =
          ((B_u u \ I_set).card : ℝ) + ((B_u u ∩ I_set).card : ℝ) := by
        exact_mod_cast (card_sdiff_add_card_inter (B_u u) I_set).symm
      linarith only [hBu_ge, hBu_sdiff_le, hpartB]
    have hsum_sz : ((inN v).card : ℝ) * (x_nat : ℝ) ^ 2 / 9 ≤
        ∑ z ∈ I_set, ((inN v ∩ inN z).card : ℝ) := by
      have hsub_in : ∀ u ∈ inN v, B_u u ∩ I_set ⊆ I_set.filter (fun z => u ∈ inN z) := by
        intro u hu z hz
        obtain ⟨hzB, hzI⟩ := mem_inter.mp hz
        have huV' : u ∈ V' := ((hinN_def v u).mp hu).1
        obtain ⟨hz_out, _⟩ := mem_near.mp (mem_of_mem_erase hzB)
        exact mem_filter.mpr ⟨hzI, (hinN_def z u).mpr ⟨huV', hz_out⟩⟩
      have h1 : ∑ u ∈ inN v, ((T_u u).card : ℝ) * (x_nat : ℝ) / 3 ≤
          ∑ u ∈ inN v, ((I_set.filter (fun z => u ∈ inN z)).card : ℝ) := by
        refine sum_le_sum fun u hu => (hB_in_I u hu).trans ?_
        exact_mod_cast card_le_card (hsub_in u hu)
      have h2 : (∑ u ∈ inN v, (I_set.filter (fun z => u ∈ inN z)).card) =
          ∑ z ∈ I_set, (inN v ∩ inN z).card := by
        have hL : ∀ u ∈ inN v, (I_set.filter (fun z => u ∈ inN z)).card =
            ∑ z ∈ I_set, if u ∈ inN z then 1 else 0 := by
          intro u _; rw [sum_boole, Nat.cast_id]
        have hR : ∀ z ∈ I_set, (inN v ∩ inN z).card =
            ∑ u ∈ inN v, if u ∈ inN z then 1 else 0 := by
          intro z _
          rw [sum_boole, Nat.cast_id, filter_mem_eq_inter]
        rw [sum_congr rfl hL, sum_comm, sum_congr rfl hR]
      have h2r : (∑ u ∈ inN v, ((I_set.filter (fun z => u ∈ inN z)).card : ℝ)) =
          ∑ z ∈ I_set, ((inN v ∩ inN z).card : ℝ) := by
        exact_mod_cast h2
      have h3 : ((inN v).card : ℝ) * (x_nat : ℝ) ^ 2 / 9 ≤
          ∑ u ∈ inN v, ((T_u u).card : ℝ) * (x_nat : ℝ) / 3 := by
        have hMI_r : (M_I.card : ℝ) = ∑ u ∈ inN v, ((T_u u).card : ℝ) := by exact_mod_cast hMI_sum
        have hM_le : (M.card : ℝ) ≤ 3 * (M_I.card : ℝ) := by exact_mod_cast hI_maj
        have hx0 : 0 ≤ (x_nat : ℝ) := by positivity
        calc
          ((inN v).card : ℝ) * (x_nat : ℝ) ^ 2 / 9
            = (((inN v).card : ℝ) * (x_nat : ℝ)) * (x_nat : ℝ) / 9 := by ring
          _ ≤ (M.card : ℝ) * (x_nat : ℝ) / 9 := by gcongr
          _ ≤ (3 * (M_I.card : ℝ)) * (x_nat : ℝ) / 9 := by gcongr
          _ = (M_I.card : ℝ) * (x_nat : ℝ) / 3 := by ring
          _ = (∑ u ∈ inN v, ((T_u u).card : ℝ)) * (x_nat : ℝ) / 3 := by rw [hMI_r]
          _ = ∑ u ∈ inN v, ((T_u u).card : ℝ) * (x_nat : ℝ) / 3 := by
              rw [sum_mul, sum_div]
      exact (h3.trans h1).trans_eq h2r
    let I' := I_set.filter (fun z => 2 * α ≤ (inN v ∩ inN z).card)
    have hI'_sum : ((inN v).card : ℝ) * (x_nat : ℝ) ^ 2 / 18 ≤
        ∑ z ∈ I', ((inN v ∩ inN z).card : ℝ) := by
      have hsplit : ∑ z ∈ I_set, ((inN v ∩ inN z).card : ℝ) =
          ∑ z ∈ I', ((inN v ∩ inN z).card : ℝ) +
            ∑ z ∈ I_set \ I', ((inN v ∩ inN z).card : ℝ) := by
        rw [← sum_union disjoint_sdiff_self_right, union_sdiff_of_subset (filter_subset _ _)]
      have hsmall : ∑ z ∈ I_set \ I', ((inN v ∩ inN z).card : ℝ) ≤ 2 * (α : ℝ) ^ 2 := by
        have hI_le : (I_set.card : ℝ) ≤ (α : ℝ) := by exact_mod_cast hInd I_set hIind
        have hs_le : ((I_set \ I').card : ℝ) ≤ (I_set.card : ℝ) := by
          exact_mod_cast card_le_card sdiff_subset
        calc
          ∑ z ∈ I_set \ I', ((inN v ∩ inN z).card : ℝ)
            ≤ ∑ _z ∈ I_set \ I', (2 * (α : ℝ)) := by
              refine sum_le_sum fun z hz => ?_
              have hnot : ¬ 2 * α ≤ (inN v ∩ inN z).card := by
                intro hle
                exact (mem_sdiff.mp hz).2 (mem_filter.mpr ⟨(mem_sdiff.mp hz).1, hle⟩)
              have hlt : (inN v ∩ inN z).card < 2 * α := Nat.lt_of_not_le hnot
              exact_mod_cast hlt.le
          _ = ((I_set \ I').card : ℝ) * (2 * (α : ℝ)) := by rw [sum_const, nsmul_eq_mul]
          _ ≤ (I_set.card : ℝ) * (2 * (α : ℝ)) := by gcongr
          _ ≤ (α : ℝ) * (2 * (α : ℝ)) := by gcongr
          _ = 2 * (α : ℝ) ^ 2 := by ring
      have h2a_le : 2 * (α : ℝ) ^ 2 ≤ ((inN v).card : ℝ) * (x_nat : ℝ) ^ 2 / 18 := by
        have hchain : n ^ 3 / (64 ^ 3 * (α : ℝ) ^ 5) ≤ ((inN v).card : ℝ) * (x_nat : ℝ) ^ 2 := by
          have h1 : n / (64 * (α : ℝ)) * (n / (64 * (α : ℝ) ^ 2)) ^ 2 ≤
              ((inN v).card : ℝ) * (x_nat : ℝ) ^ 2 := by
            have hdl : n / (64 * (α : ℝ)) ≤ ((inN v).card : ℝ) := hd_lb
            have hxl : n / (64 * (α : ℝ) ^ 2) ≤ (x_nat : ℝ) := hx_nat_lb
            gcongr
          calc
            n ^ 3 / (64 ^ 3 * (α : ℝ) ^ 5) = n / (64 * (α : ℝ)) * (n / (64 * (α : ℝ) ^ 2)) ^ 2 := by
              ring
            _ ≤ ((inN v).card : ℝ) * (x_nat : ℝ) ^ 2 := h1
        have hα_pos : (0 : ℝ) < (α : ℝ) := by positivity
        have h1 : 36 * (α : ℝ) ^ 2 ≤ n ^ 3 / (64 ^ 3 * (α : ℝ) ^ 5) := by
          rw [le_div_iff₀ (by positivity)]
          have hcmp : 36 * 64 ^ 3 * (α : ℝ) ^ 7 ≤ 16 * 9 * 64 ^ 3 * (α : ℝ) ^ 7 :=
            mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
          linarith only [hN3_contra, hcmp, show (36 * (α : ℝ) ^ 2) * (64 ^ 3 * (α : ℝ) ^ 5) =
            36 * 64 ^ 3 * (α : ℝ) ^ 7 by ring]
        linarith only [hchain, h1]
      linarith only [hsum_sz, hsplit, hsmall, h2a_le]
    have hI'_ne : I'.Nonempty := by
      by_contra hIe
      rw [not_nonempty_iff_eq_empty.mp hIe, sum_empty] at hI'_sum
      have hd_pos : 0 < ((inN v).card : ℝ) := lt_of_lt_of_le (by positivity) hd_lb
      have hx_pos' : 0 < (x_nat : ℝ) := by exact_mod_cast hx_nat_pos
      have h0 : 0 < ((inN v).card : ℝ) * (x_nat : ℝ) ^ 2 / 18 := by positivity
      linarith only [h0, hI'_sum]
    have hI'_card_pos : (0 : ℝ) < (I'.card : ℝ) := by exact_mod_cast card_pos.mpr hI'_ne
    have hI'_card_le : (I'.card : ℝ) ≤ (α : ℝ) := by
      have : I'.card ≤ I_set.card := card_le_card (filter_subset _ _)
      exact_mod_cast this.trans (hInd I_set hIind)
    have hsum_edges : (((inN v).card : ℝ) * (x_nat : ℝ) ^ 2 / 18) ^ 2 / (4 * (α : ℝ) ^ 2) ≤
        ∑ z ∈ I', ((edgesIn G (inN v ∩ inN z)).card : ℝ) := by
      have hCS := cauchy_schwarz_finset I' (fun z => ((inN v ∩ inN z).card : ℝ))
      have hCS1 : (∑ z ∈ I', ((inN v ∩ inN z).card : ℝ)) ^ 2 / (I'.card : ℝ) ≤
          ∑ z ∈ I', ((inN v ∩ inN z).card : ℝ) ^ 2 := by
        rw [div_le_iff₀ hI'_card_pos]; linarith only [hCS]
      have hTuran : ∑ z ∈ I', ((inN v ∩ inN z).card : ℝ) ^ 2 ≤
          4 * (α : ℝ) * ∑ z ∈ I', ((edgesIn G (inN v ∩ inN z)).card : ℝ) := by
        rw [mul_sum]
        refine sum_le_sum fun z hz => ?_
        exact edgesIn_ge_of_indep_le G (inN v ∩ inN z) α hα (fun I _ hI => hInd I hI)
          (mem_filter.mp hz).2
      have hα_pos' : (0 : ℝ) < (α : ℝ) := by exact_mod_cast hα
      have h4α_pos : (0 : ℝ) < 4 * (α : ℝ) := mul_pos (by norm_num) hα_pos'
      have hnum_nn : 0 ≤ ((inN v).card : ℝ) * (x_nat : ℝ) ^ 2 / 18 :=
        div_nonneg (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)) (by norm_num)
      have hnum : (((inN v).card : ℝ) * (x_nat : ℝ) ^ 2 / 18) ^ 2 ≤
          (∑ z ∈ I', ((inN v ∩ inN z).card : ℝ)) ^ 2 :=
        pow_le_pow_left₀ hnum_nn hI'_sum 2
      have h4ap : 4 * (α : ℝ) * (I'.card : ℝ) ≤ 4 * (α : ℝ) ^ 2 := by
        nlinarith only [hI'_card_le, hα_pos']
      have h4aI_pos : 0 < 4 * (α : ℝ) * (I'.card : ℝ) := mul_pos h4α_pos hI'_card_pos
      calc
        (((inN v).card : ℝ) * (x_nat : ℝ) ^ 2 / 18) ^ 2 / (4 * (α : ℝ) ^ 2)
          ≤ (∑ z ∈ I', ((inN v ∩ inN z).card : ℝ)) ^ 2 / (4 * (α : ℝ) * (I'.card : ℝ)) :=
            div_le_div₀ (sq_nonneg _) hnum h4aI_pos h4ap
        _ = ((∑ z ∈ I', ((inN v ∩ inN z).card : ℝ)) ^ 2 / (I'.card : ℝ)) / (4 * (α : ℝ)) := by
            ring
        _ ≤ (∑ z ∈ I', ((inN v ∩ inN z).card : ℝ) ^ 2) / (4 * (α : ℝ)) :=
            div_le_div_of_nonneg_right hCS1 h4α_pos.le
        _ ≤ ∑ z ∈ I', ((edgesIn G (inN v ∩ inN z)).card : ℝ) :=
            (div_le_iff₀ h4α_pos).mpr (by rw [mul_comm]; exact hTuran)
    have hcount_le : ∑ z ∈ I', (edgesIn G (inN v ∩ inN z)).card ≤
        ∑ e ∈ edgesIn G (inN v), ((commonOut e).erase v).card := by
      have hL : ∀ z ∈ I', (edgesIn G (inN v ∩ inN z)).card =
          ∑ e ∈ edgesIn G (inN v), if z ∈ (commonOut e).erase v then 1 else 0 := by
        intro z hz
        rw [sum_boole, Nat.cast_id]
        congr 1
        ext e
        rw [mem_filter, mem_edgesIn, mem_edgesIn]
        have hzI : z ∈ I_set := (filter_subset _ _) hz
        have hzN : z ∈ N_tri G v := hUnion ▸ mem_union_left _ (mem_union_right _ hzI)
        have hzv : z ≠ v := (mem_N_tri.mp hzN).1
        constructor
        · rintro ⟨he_sub, he2, hcl⟩
          refine ⟨⟨he_sub.trans inter_subset_left, he2, hcl⟩, mem_erase.mpr ⟨hzv, ?_⟩⟩
          have hzV' : z ∈ V' := by
            obtain ⟨a, ha⟩ := card_pos.mp (by omega : 0 < e.card)
            have ha_in : a ∈ inN z := inter_subset_right (he_sub ha)
            obtain ⟨haV', hza⟩ := (hinN_def z a).mp ha_in
            exact (mem_neighbors.mp (hout_sub a haV' hza)).1
          exact (hco_def e z).mpr ⟨hzV', fun a ha => ((hinN_def z a).mp (inter_subset_right (he_sub ha))).2⟩
        · rintro ⟨⟨he_sub, he2, hcl⟩, hze⟩
          refine ⟨fun a ha => mem_inter.mpr ⟨he_sub ha, ?_⟩, he2, hcl⟩
          have hz_co := ((hco_def e z).mp (mem_of_mem_erase hze)).2 a ha
          exact (hinN_def z a).mpr ⟨((hinN_def v a).mp (he_sub ha)).1, hz_co⟩
      have hR : ∀ e ∈ edgesIn G (inN v),
          (∑ z ∈ I', if z ∈ (commonOut e).erase v then 1 else 0) ≤
            ((commonOut e).erase v).card := by
        intro e _
        rw [sum_boole, Nat.cast_id]
        exact card_le_card (fun z hz => (mem_filter.mp hz).2)
      rw [sum_congr rfl hL, sum_comm]
      exact sum_le_sum hR
    have hcount_leR : (∑ z ∈ I', ((edgesIn G (inN v ∩ inN z)).card : ℝ)) ≤
        ∑ e ∈ edgesIn G (inN v), (((commonOut e).erase v).card : ℝ) := by
      simpa only [Nat.cast_sum] using (Nat.cast_le (α := ℝ)).mpr hcount_le
    exact hsum_edges.trans hcount_leR

private lemma claim1_T4_lower (G : SimpleGraph V) (hK4 : Clique4Free G) (hLoc : LocalIndep G)
    (α : ℕ) (hα : 1 ≤ α)
    (hInd : ∀ I : Finset V, G.IsIndepSet (I : Set V) → I.card ≤ α)
    (V' : Finset V) (outN : V → Finset V)
    (hout_sub : ∀ u ∈ V', outN u ⊆ neighbors G V' u)
    (x : ℝ) (hx_pos : 0 < x)
    (hout_exp : ∀ u ∈ V', ∀ A ⊆ outN u, G.IsIndepSet (A : Set V) →
      x * (A.card : ℝ) ≤ ((near G (outN u) A).card : ℝ))
    (x_nat : ℕ) (hx_nat_le : (x_nat : ℝ) ≤ x - 1) (hx_nat_pos : 1 ≤ x_nat)
    (hx_nat_lb : (Fintype.card V : ℝ) / (64 * (α : ℝ) ^ 2) ≤ (x_nat : ℝ))
    (hx_sum_lb : (Fintype.card V : ℝ) ^ 2 / (32 * (α : ℝ)) ≤
      ∑ u ∈ V', ((outN u).card : ℝ))
    (hN3_contra : 16 * 9 * 64 ^ 3 * (α : ℝ) ^ 7 < (Fintype.card V : ℝ) ^ 3) :
    (Fintype.card V : ℝ) ^ 7 ≤ 2592 * 64 ^ 6 * (α : ℝ) ^ 12 *
      ((∑ e ∈ edgesIn G V', (V'.filter (fun z => ∀ a ∈ e, z ∈ outN a)).card.choose 2 : ℕ) : ℝ) := by
  classical
  let inN : V → Finset V := fun v => V'.filter (fun u => v ∈ outN u)
  let commonOut : Finset V → Finset V := fun e => V'.filter (fun z => ∀ a ∈ e, z ∈ outN a)
  let T4 : ℕ := ∑ e ∈ edgesIn G V', (commonOut e).card.choose 2
  change (Fintype.card V : ℝ) ^ 7 ≤ 2592 * 64 ^ 6 * (α : ℝ) ^ 12 * (T4 : ℝ)
  let n : ℝ := Fintype.card V
  have hn_pos : 0 < n := by
    have : (0 : ℝ) ≤ 16 * 9 * 64 ^ 3 * (α : ℝ) ^ 7 := by positivity
    have hn3 : 0 < n ^ 3 := lt_of_le_of_lt this hN3_contra
    by_contra! hle
    have : n ^ 3 ≤ 0 := by nlinarith [sq_nonneg n]
    linarith
  have hsum_in : n ^ 2 / (32 * (α : ℝ)) ≤ ∑ v ∈ V', ((inN v).card : ℝ) := by
    have hswap : ∑ v ∈ V', (inN v).card = ∑ u ∈ V', (outN u).card := by
      have h1 : ∀ v ∈ V', (inN v).card = ∑ u ∈ V', if v ∈ outN u then 1 else 0 := by
        intro v _
        rw [sum_boole, Nat.cast_id]
      have h2 : ∀ u ∈ V', (outN u).card = ∑ v ∈ V', if v ∈ outN u then 1 else 0 := by
        intro u hu
        rw [sum_boole, Nat.cast_id]
        have heq : V'.filter (fun v => v ∈ outN u) = outN u := by
          ext v
          rw [mem_filter]
          exact ⟨fun h => h.2, fun h => ⟨(mem_neighbors.mp (hout_sub u hu h)).1, h⟩⟩
        rw [heq]
      rw [sum_congr rfl h1, sum_comm, sum_congr rfl h2]
    have hswapR : (∑ v ∈ V', ((inN v).card : ℝ)) = ∑ u ∈ V', ((outN u).card : ℝ) := by
      exact_mod_cast hswap
    linarith [hx_sum_lb]
  let V'_in := V'.filter (fun v => n / (64 * (α : ℝ)) ≤ ((inN v).card : ℝ))
  have hV'_in_sum : n ^ 2 / (64 * (α : ℝ)) ≤ ∑ v ∈ V'_in, ((inN v).card : ℝ) := by
    have hsplit : ∑ v ∈ V', ((inN v).card : ℝ) =
        ∑ v ∈ V'_in, ((inN v).card : ℝ) + ∑ v ∈ V' \ V'_in, ((inN v).card : ℝ) := by
      rw [← sum_union disjoint_sdiff_self_right, union_sdiff_of_subset (filter_subset _ _)]
    have hlow : ∑ v ∈ V' \ V'_in, ((inN v).card : ℝ) ≤ n ^ 2 / (64 * (α : ℝ)) := by
      calc
        ∑ v ∈ V' \ V'_in, ((inN v).card : ℝ)
          ≤ ∑ _v ∈ V' \ V'_in, (n / (64 * (α : ℝ))) := by
            refine sum_le_sum fun v hv => ?_
            have hnot : ¬ n / (64 * (α : ℝ)) ≤ ((inN v).card : ℝ) := by
              intro hle
              exact (mem_sdiff.mp hv).2 (mem_filter.mpr ⟨(mem_sdiff.mp hv).1, hle⟩)
            linarith
        _ = ((V' \ V'_in).card : ℝ) * (n / (64 * (α : ℝ))) := by rw [sum_const, nsmul_eq_mul]
        _ ≤ n * (n / (64 * (α : ℝ))) := by
            have hle : ((V' \ V'_in).card : ℝ) ≤ n := by
              dsimp [n]
              exact_mod_cast (card_le_univ (V' \ V'_in))
            gcongr
        _ = n ^ 2 / (64 * (α : ℝ)) := by ring
    linarith only [hsum_in, hsplit, hlow,
      show n ^ 2 / (32 * (α : ℝ)) = 2 * (n ^ 2 / (64 * (α : ℝ))) by ring]
  have hper_v : ∀ v ∈ V'_in,
      (((inN v).card : ℝ) * (x_nat : ℝ) ^ 2 / 18) ^ 2 / (4 * (α : ℝ) ^ 2) ≤
        ∑ e ∈ edgesIn G (inN v), (((commonOut e).erase v).card : ℝ) := by
    intro v hv_in
    exact claim1_per_v G hK4 hLoc α hα hInd V' outN inN commonOut
      (fun w u => by simp [inN]) (fun e z => by simp [commonOut])
      hout_sub x hx_pos hout_exp x_nat hx_nat_le hx_nat_pos hx_nat_lb hN3_contra
      v ((filter_subset _ _) hv_in) (mem_filter.mp hv_in).2
  -- Sum hper_v over V'_in and relate to 2 * T4
  have h2T4 : 2 * T4 = ∑ v ∈ V', ∑ e ∈ edgesIn G (inN v), ((commonOut e).erase v).card := by
    have hL : 2 * T4 = ∑ e ∈ edgesIn G V', (commonOut e).card * ((commonOut e).card - 1) := by
      dsimp [T4]
      rw [mul_sum]
      refine sum_congr rfl fun e _ => ?_
      rw [Nat.choose_two_right]
      have h2 : 2 ∣ (commonOut e).card * ((commonOut e).card - 1) := by
        rcases Nat.even_or_odd (commonOut e).card with ⟨k, hk⟩ | ⟨k, hk⟩
        · exact ⟨k * ((commonOut e).card - 1), by rw [hk]; ring⟩
        · have h1 : (commonOut e).card - 1 = 2 * k := by omega
          exact ⟨(commonOut e).card * k, by rw [h1]; ring⟩
      exact Nat.mul_div_cancel' h2
    have hR : ∑ v ∈ V', ∑ e ∈ edgesIn G (inN v), ((commonOut e).erase v).card =
        ∑ e ∈ edgesIn G V', (commonOut e).card * ((commonOut e).card - 1) := by
      have hsub_in : ∀ v ∈ V', edgesIn G (inN v) =
          (edgesIn G V').filter (fun e => v ∈ commonOut e) := by
        intro v _
        ext e
        rw [mem_filter, mem_edgesIn, mem_edgesIn]
        constructor
        · rintro ⟨he_in, he2, hcl⟩
          refine ⟨⟨he_in.trans (filter_subset _ _), he2, hcl⟩, mem_filter.mpr ⟨?_, ?_⟩⟩
          · assumption
          · intro a ha; exact (mem_filter.mp (he_in ha)).2
        · rintro ⟨⟨heV', he2, hcl⟩, hv_co⟩
          refine ⟨fun a ha => mem_filter.mpr ⟨heV' ha, (mem_filter.mp hv_co).2 a ha⟩, he2, hcl⟩
      have h1 : ∀ v ∈ V', (∑ e ∈ edgesIn G (inN v), ((commonOut e).erase v).card) =
          ∑ e ∈ edgesIn G V', if v ∈ commonOut e then (commonOut e).card - 1 else 0 := by
        intro v hv
        rw [hsub_in v hv, sum_filter]
        refine sum_congr rfl fun e _ => ?_
        split_ifs with hve
        · rw [card_erase_of_mem hve]
        · rfl
      rw [sum_congr rfl h1, sum_comm]
      refine sum_congr rfl fun e _ => ?_
      have hco_sub : commonOut e ⊆ V' := filter_subset _ _
      rw [← sum_filter, filter_mem_eq_inter, inter_eq_right.mpr hco_sub, sum_const, smul_eq_mul]
    rw [hL, hR]
  have hV'_in_ne : V'_in.Nonempty := by
    by_contra hVe
    rw [not_nonempty_iff_eq_empty.mp hVe, sum_empty] at hV'_in_sum
    have : 0 < n ^ 2 / (64 * (α : ℝ)) := by positivity
    linarith
  have hV'_in_pos : (0 : ℝ) < (V'_in.card : ℝ) := by exact_mod_cast card_pos.mpr hV'_in_ne
  have hV'_in_le : (V'_in.card : ℝ) ≤ n := by
    dsimp [n]
    exact_mod_cast (card_le_univ V'_in)
  have hsum_2T4 : ∑ v ∈ V'_in,
      (((inN v).card : ℝ) * (x_nat : ℝ) ^ 2 / 18) ^ 2 / (4 * (α : ℝ) ^ 2) ≤ 2 * (T4 : ℝ) := by
    have h1 : ∑ v ∈ V'_in,
        (((inN v).card : ℝ) * (x_nat : ℝ) ^ 2 / 18) ^ 2 / (4 * (α : ℝ) ^ 2) ≤
        ∑ v ∈ V'_in, (∑ e ∈ edgesIn G (inN v), (((commonOut e).erase v).card : ℝ)) :=
      sum_le_sum hper_v
    have h2 : ∑ v ∈ V'_in, (∑ e ∈ edgesIn G (inN v), ((commonOut e).erase v).card) ≤
        ∑ v ∈ V', (∑ e ∈ edgesIn G (inN v), ((commonOut e).erase v).card) :=
      sum_le_sum_of_subset (filter_subset _ _)
    have h2r : ∑ v ∈ V'_in, (∑ e ∈ edgesIn G (inN v), (((commonOut e).erase v).card : ℝ)) ≤
        2 * (T4 : ℝ) := by
      have h2' : (∑ v ∈ V'_in, (∑ e ∈ edgesIn G (inN v), (((commonOut e).erase v).card : ℝ))) ≤
          (∑ v ∈ V', (∑ e ∈ edgesIn G (inN v), (((commonOut e).erase v).card : ℝ))) := by
        exact_mod_cast h2
      have h2T4r : (2 : ℝ) * (T4 : ℝ) =
          ∑ v ∈ V', ∑ e ∈ edgesIn G (inN v), (((commonOut e).erase v).card : ℝ) := by
        exact_mod_cast h2T4
      linarith
    exact h1.trans h2r
  have hCS_v := cauchy_schwarz_finset V'_in (fun v => ((inN v).card : ℝ))
  have hLHS : n ^ 7 / (1296 * 64 ^ 6 * (α : ℝ) ^ 12) ≤
      ∑ v ∈ V'_in, (((inN v).card : ℝ) * (x_nat : ℝ) ^ 2 / 18) ^ 2 / (4 * (α : ℝ) ^ 2) := by
    have hfactor : ∑ v ∈ V'_in, (((inN v).card : ℝ) * (x_nat : ℝ) ^ 2 / 18) ^ 2 / (4 * (α : ℝ) ^ 2) =
        ((x_nat : ℝ) ^ 4 / (1296 * (α : ℝ) ^ 2)) * ∑ v ∈ V'_in, ((inN v).card : ℝ) ^ 2 := by
      rw [mul_sum]
      refine sum_congr rfl fun v _ => ?_
      ring
    rw [hfactor]
    have hα_pos' : (0 : ℝ) < (α : ℝ) := by exact_mod_cast hα
    have h64a_pos : (0 : ℝ) < 64 * (α : ℝ) := mul_pos (by norm_num) hα_pos'
    have h64a2_pos : (0 : ℝ) < 64 * (α : ℝ) ^ 2 := mul_pos (by norm_num) (pow_pos hα_pos' 2)
    have h1296a2_pos : (0 : ℝ) < 1296 * (α : ℝ) ^ 2 := mul_pos (by norm_num) (pow_pos hα_pos' 2)
    have hsum_sq : n ^ 3 / (64 ^ 2 * (α : ℝ) ^ 2) ≤ ∑ v ∈ V'_in, ((inN v).card : ℝ) ^ 2 := by
      have h1 : (n ^ 2 / (64 * (α : ℝ))) ^ 2 ≤ (∑ v ∈ V'_in, ((inN v).card : ℝ)) ^ 2 :=
        pow_le_pow_left₀ (div_nonneg (pow_nonneg hn_pos.le 2) h64a_pos.le) hV'_in_sum 2
      have heqn3 : n ^ 3 / (64 ^ 2 * (α : ℝ) ^ 2) = (n ^ 2 / (64 * (α : ℝ))) ^ 2 / n := by
        have hn0 : n ≠ 0 := hn_pos.ne'
        field_simp
      calc
        n ^ 3 / (64 ^ 2 * (α : ℝ) ^ 2) = (n ^ 2 / (64 * (α : ℝ))) ^ 2 / n := heqn3
        _ ≤ (∑ v ∈ V'_in, ((inN v).card : ℝ)) ^ 2 / (V'_in.card : ℝ) :=
            div_le_div₀ (sq_nonneg _) h1 hV'_in_pos hV'_in_le
        _ ≤ ∑ v ∈ V'_in, ((inN v).card : ℝ) ^ 2 := by
            rw [div_le_iff₀ hV'_in_pos, mul_comm]; exact hCS_v
    have hx4 : n ^ 4 / (64 ^ 4 * (α : ℝ) ^ 8) ≤ (x_nat : ℝ) ^ 4 := by
      have : (n / (64 * (α : ℝ) ^ 2)) ^ 4 ≤ (x_nat : ℝ) ^ 4 :=
        pow_le_pow_left₀ (div_nonneg hn_pos.le h64a2_pos.le) hx_nat_lb 4
      calc
        n ^ 4 / (64 ^ 4 * (α : ℝ) ^ 8) = (n / (64 * (α : ℝ) ^ 2)) ^ 4 := by ring
        _ ≤ (x_nat : ℝ) ^ 4 := this
    calc
      n ^ 7 / (1296 * 64 ^ 6 * (α : ℝ) ^ 12)
        = (n ^ 4 / (64 ^ 4 * (α : ℝ) ^ 8) / (1296 * (α : ℝ) ^ 2)) * (n ^ 3 / (64 ^ 2 * (α : ℝ) ^ 2)) := by
          ring
      _ ≤ ((x_nat : ℝ) ^ 4 / (1296 * (α : ℝ) ^ 2)) * ∑ v ∈ V'_in, ((inN v).card : ℝ) ^ 2 :=
          mul_le_mul (div_le_div_of_nonneg_right hx4 h1296a2_pos.le) hsum_sq
            (div_nonneg (pow_nonneg hn_pos.le 3) (mul_nonneg (by norm_num) (sq_nonneg _)))
            (div_nonneg (pow_nonneg (Nat.cast_nonneg _) 4) h1296a2_pos.le)
  have hfinal : n ^ 7 / (1296 * 64 ^ 6 * (α : ℝ) ^ 12) ≤ 2 * (T4 : ℝ) := hLHS.trans hsum_2T4
  have hden_pos : (0 : ℝ) < 1296 * 64 ^ 6 * (α : ℝ) ^ 12 :=
    mul_pos (by norm_num) (pow_pos (by exact_mod_cast hα) 12)
  rw [div_le_iff₀ hden_pos] at hfinal
  linarith only [hfinal, show (2 * (T4 : ℝ)) * (1296 * 64 ^ 6 * (α : ℝ) ^ 12) =
    2592 * 64 ^ 6 * (α : ℝ) ^ 12 * (T4 : ℝ) by ring]

end Claim1

section GridLemma

private lemma floor_half_add_one_le {r : ℝ} (hr : 1 ≤ r) :
    Nat.floor (r / 2) + 1 ≤ Nat.floor r := by
  have hm1 : 1 ≤ Nat.floor r := (Nat.one_le_floor_iff r).mpr hr
  have hmr : r < (Nat.floor r : ℝ) + 1 := Nat.lt_floor_add_one r
  have hm1R : (1 : ℝ) ≤ (Nat.floor r : ℝ) := by exact_mod_cast hm1
  exact (Nat.floor_lt (by linarith)).mpr (by linarith)

private abbrev gridGraph {ι κ V : Type*} (G : SimpleGraph V) :
    SimpleGraph ((ι × κ) × V) where
  Adj p q := p ≠ q ∧ G.Adj p.2 q.2
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

private lemma grid_clean {ι κ V : Type*} [DecidableEq ι] [DecidableEq κ] [DecidableEq V]
    (G : SimpleGraph V) (α' : ℕ) (hα'pos : 1 ≤ α')
    (I_rows : Finset ι) (J_cols : Finset κ)
    (U_grid : Finset ((ι × κ) × V)) (cell : ι → κ → Finset ((ι × κ) × V))
    (hcell_U : ∀ i j, cell i j ⊆ U_grid)
    (hcell_fst : ∀ i j p, p ∈ cell i j → p.1.1 = i ∧ p.1.2 = j)
    (hG_ind : ∀ S ⊆ U_grid, (gridGraph G).IsIndepSet (S : Set ((ι × κ) × V)) → S.card ≤ α')
    (hG_cross : ∀ p ∈ U_grid, ∀ q ∈ U_grid,
      p.1.1 ≠ q.1.1 → p.1.2 ≠ q.1.2 → ¬ (gridGraph G).Adj p q)
    (T : ℝ) (hT_pos : 0 < T) (hs₀_pos : 1 ≤ I_rows.card) :
    let s₀ := I_rows.card
    let k_col := Nat.floor (T / (s₀ : ℝ))
    ∃ I_cur ⊆ I_rows, ∃ J_cur ⊆ J_cols,
      s₀ < 2 * I_cur.card ∧
      ((J_cols \ J_cur).card : ℝ) ≤ ((s₀ - I_cur.card : ℕ) : ℝ) * (T / (s₀ : ℝ)) ∧
      (∀ i ∈ I_cur, ∀ J₀ ⊆ J_cur, J₀.card ≤ k_col →
        ∀ S ⊆ J₀.biUnion (cell i), (gridGraph G).IsIndepSet (S : Set ((ι × κ) × V)) →
          (S.card : ℝ) ≤ 2 * (α' : ℝ) / (s₀ : ℝ)) := by
  classical
  intro s₀ k_col
  have hStep : ∀ m : ℕ, ∀ I_cur J_cur : Finset _, ∀ I_acc : Finset ((ι × κ) × V),
      I_cur.card = m → I_cur ⊆ I_rows → J_cur ⊆ J_cols → I_acc ⊆ U_grid →
      (gridGraph G).IsIndepSet (I_acc : Set ((ι × κ) × V)) →
      (∀ p ∈ I_acc, p.1.1 ∉ I_cur ∧ p.1.2 ∉ J_cur) →
      (I_cur = I_rows ∨ ((s₀ - I_cur.card : ℕ) : ℝ) * (2 * (α' : ℝ) / (s₀ : ℝ)) < (I_acc.card : ℝ)) →
      ((J_cols \ J_cur).card : ℝ) ≤ ((s₀ - I_cur.card : ℕ) : ℝ) * (T / (s₀ : ℝ)) →
      ∃ I_out ⊆ I_rows, ∃ J_out ⊆ J_cols,
        s₀ < 2 * I_out.card ∧
        ((J_cols \ J_out).card : ℝ) ≤ ((s₀ - I_out.card : ℕ) : ℝ) * (T / (s₀ : ℝ)) ∧
        (∀ i ∈ I_out, ∀ J₀ ⊆ J_out, J₀.card ≤ k_col →
          ∀ S ⊆ J₀.biUnion (cell i), (gridGraph G).IsIndepSet (S : Set ((ι × κ) × V)) →
            (S.card : ℝ) ≤ 2 * (α' : ℝ) / (s₀ : ℝ)) := by
    intro m
    induction m with
    | zero =>
      intro I_cur J_cur I_acc hm hIsub hJsub hAccU hAccInd hAccAvoid hInv _
      exfalso
      have hI0 : I_cur.card = 0 := hm
      rcases hInv with hIeq | hlt
      · rw [hIeq] at hI0; dsimp [s₀] at *; omega
      · have hle : (I_acc.card : ℝ) ≤ (α' : ℝ) := by exact_mod_cast hG_ind I_acc hAccU hAccInd
        rw [hI0, Nat.sub_zero] at hlt
        have hs₀r : (0 : ℝ) < (s₀ : ℝ) := by exact_mod_cast hs₀_pos
        have h1 : (s₀ : ℝ) * (2 * (α' : ℝ) / (s₀ : ℝ)) = 2 * (α' : ℝ) := by field_simp
        linarith [show (α' : ℝ) ≥ 1 by exact_mod_cast hα'pos]
    | succ m ih =>
      intro I_cur J_cur I_acc hm hIsub hJsub hAccU hAccInd hAccAvoid hInv hDel
      by_cases hdone : ∀ i ∈ I_cur, ∀ J₀ ⊆ J_cur, J₀.card ≤ k_col →
          ∀ S ⊆ J₀.biUnion (cell i), (gridGraph G).IsIndepSet (S : Set ((ι × κ) × V)) →
            (S.card : ℝ) ≤ 2 * (α' : ℝ) / (s₀ : ℝ)
      · have hs1_2 : s₀ < 2 * I_cur.card := by
          rcases hInv with hIeq | hlt
          · rw [hIeq]; dsimp [s₀]; omega
          · have hle : (I_acc.card : ℝ) ≤ (α' : ℝ) := by exact_mod_cast hG_ind I_acc hAccU hAccInd
            have hsub_le : I_cur.card ≤ s₀ := card_le_card hIsub
            have hs₀r : (0 : ℝ) < (s₀ : ℝ) := by exact_mod_cast hs₀_pos
            have hα'r : (0 : ℝ) < (α' : ℝ) := by exact_mod_cast hα'pos
            have h1 : ((s₀ - I_cur.card : ℕ) : ℝ) * (2 * (α' : ℝ) / (s₀ : ℝ)) < (α' : ℝ) := by
              linarith
            have h2 : 2 * ((s₀ - I_cur.card : ℕ) : ℝ) < (s₀ : ℝ) := by
              have : (2 * ((s₀ - I_cur.card : ℕ) : ℝ) - (s₀ : ℝ)) * ((α' : ℝ) / (s₀ : ℝ)) < 0 := by
                nlinarith [h1, show 2 * ((s₀ - I_cur.card : ℕ) : ℝ) * ((α' : ℝ) / (s₀ : ℝ)) =
                  ((s₀ - I_cur.card : ℕ) : ℝ) * (2 * (α' : ℝ) / (s₀ : ℝ)) by ring,
                  show (s₀ : ℝ) * ((α' : ℝ) / (s₀ : ℝ)) = (α' : ℝ) by field_simp]
              have hpos : 0 < (α' : ℝ) / (s₀ : ℝ) := div_pos hα'r hs₀r
              nlinarith
            have h3 : 2 * (s₀ - I_cur.card) < s₀ := by exact_mod_cast h2
            omega
        exact ⟨I_cur, hIsub, J_cur, hJsub, hs1_2, hDel, hdone⟩
      push Not at hdone
      obtain ⟨i, hi, J₀, hJ₀, hJ₀k, I_bad, hIbad_sub, hIbad_ind, hIbad_gt⟩ := hdone
      let I_cur' := I_cur.erase i
      let J_cur' := J_cur \ J₀
      let I_acc' := I_acc ∪ I_bad
      have hm' : I_cur'.card = m := by rw [card_erase_of_mem hi, hm]; rfl
      have hIbad_U : I_bad ⊆ U_grid := by
        intro p hp
        obtain ⟨j, _, hpcell⟩ := mem_biUnion.mp (hIbad_sub hp)
        exact hcell_U i j hpcell
      have hdisj_acc : Disjoint I_acc I_bad := by
        rw [disjoint_left]
        intro p hpA hpB
        obtain ⟨j, _, hpcell⟩ := mem_biUnion.mp (hIbad_sub hpB)
        have hpi : p.1.1 = i := (hcell_fst i j p hpcell).1
        exact (hAccAvoid p hpA).1 (hpi ▸ hi)
      have hAccInd' : (gridGraph G).IsIndepSet (I_acc' : Set ((ι × κ) × V)) := by
        rw [(gridGraph G).isIndepSet_iff]
        intro p hp q hq hpq
        simp only [I_acc', coe_union, Set.mem_union, mem_coe] at hp hq
        rcases hp with hp | hp <;> rcases hq with hq | hq
        · exact ((gridGraph G).isIndepSet_iff.mp hAccInd) hp hq hpq
        · obtain ⟨j, hjJ₀, hqcell⟩ := mem_biUnion.mp (hIbad_sub hq)
          have hq12 := hcell_fst i j q hqcell
          have hp_av := hAccAvoid p hp
          exact hG_cross p (hAccU hp) q (hIbad_U hq)
            (fun h => hp_av.1 (h ▸ hq12.1 ▸ hi)) (fun h => hp_av.2 (h ▸ hq12.2 ▸ hJ₀ hjJ₀))
        · obtain ⟨j, hjJ₀, hpcell⟩ := mem_biUnion.mp (hIbad_sub hp)
          have hp12 := hcell_fst i j p hpcell
          have hq_av := hAccAvoid q hq
          exact hG_cross p (hIbad_U hp) q (hAccU hq)
            (fun h => hq_av.1 (h.symm ▸ hp12.1 ▸ hi)) (fun h => hq_av.2 (h.symm ▸ hp12.2 ▸ hJ₀ hjJ₀))
        · exact ((gridGraph G).isIndepSet_iff.mp hIbad_ind) hp hq hpq
      have hAccAvoid' : ∀ p ∈ I_acc', p.1.1 ∉ I_cur' ∧ p.1.2 ∉ J_cur' := by
        intro p hp
        rcases mem_union.mp hp with hpA | hpB
        · have h := hAccAvoid p hpA
          exact ⟨fun h1 => h.1 (erase_subset _ _ h1), fun h2 => h.2 (sdiff_subset h2)⟩
        · obtain ⟨j, hjJ₀, hpcell⟩ := mem_biUnion.mp (hIbad_sub hpB)
          have hp12 := hcell_fst i j p hpcell
          exact ⟨fun h => (mem_erase.mp h).1 hp12.1, fun h => (mem_sdiff.mp h).2 (hp12.2 ▸ hjJ₀)⟩
      have hI_cur_le : I_cur.card ≤ s₀ := card_le_card hIsub
      have hI_cur'_le : I_cur'.card < s₀ := by rw [hm']; omega
      have hdiff_succ : s₀ - I_cur'.card = (s₀ - I_cur.card) + 1 := by omega
      have hInv' : I_cur' = I_rows ∨
          ((s₀ - I_cur'.card : ℕ) : ℝ) * (2 * (α' : ℝ) / (s₀ : ℝ)) < (I_acc'.card : ℝ) := by
        right
        rw [hdiff_succ, Nat.cast_add, Nat.cast_one, add_mul, one_mul]
        have hcard_acc : (I_acc'.card : ℝ) = (I_acc.card : ℝ) + (I_bad.card : ℝ) := by
          exact_mod_cast card_union_of_disjoint hdisj_acc
        rw [hcard_acc]
        have hle_prev : ((s₀ - I_cur.card : ℕ) : ℝ) * (2 * (α' : ℝ) / (s₀ : ℝ)) ≤ (I_acc.card : ℝ) := by
          rcases hInv with hIeq | hlt
          · rw [hIeq]; dsimp [s₀]; simp
          · exact hlt.le
        linarith
      have hDel' : ((J_cols \ J_cur').card : ℝ) ≤ ((s₀ - I_cur'.card : ℕ) : ℝ) * (T / (s₀ : ℝ)) := by
        have hsub_del : J_cols \ J_cur' ⊆ (J_cols \ J_cur) ∪ J₀ := by
          intro j hj
          rw [mem_sdiff] at hj
          rw [mem_union, mem_sdiff]
          by_cases hj_cur : j ∈ J_cur
          · right
            by_contra hj0
            exact hj.2 (mem_sdiff.mpr ⟨hj_cur, hj0⟩)
          · left
            exact ⟨hj.1, hj_cur⟩
        have hc_del : (J_cols \ J_cur').card ≤ (J_cols \ J_cur).card + J₀.card :=
          (card_le_card hsub_del).trans (card_union_le _ _)
        have hc_delR : ((J_cols \ J_cur').card : ℝ) ≤
            ((J_cols \ J_cur).card : ℝ) + (J₀.card : ℝ) := by exact_mod_cast hc_del
        have hJ₀_le : (J₀.card : ℝ) ≤ T / (s₀ : ℝ) := by
          have hfl : (k_col : ℝ) ≤ T / (s₀ : ℝ) :=
            Nat.floor_le (div_nonneg hT_pos.le (Nat.cast_nonneg _))
          exact (by exact_mod_cast hJ₀k : (J₀.card : ℝ) ≤ (k_col : ℝ)).trans hfl
        rw [hdiff_succ, Nat.cast_add, Nat.cast_one, add_mul, one_mul]
        linarith
      exact ih I_cur' J_cur' I_acc' hm' (erase_subset _ _ |>.trans hIsub)
        (sdiff_subset.trans hJsub) (union_subset hAccU hIbad_U) hAccInd' hAccAvoid' hInv' hDel'
  exact hStep s₀ I_rows J_cols ∅ rfl (Subset.refl _) (Subset.refl _) (empty_subset _)
    (by simp) (fun _ h => by simp at h) (Or.inl rfl) (by dsimp [s₀]; simp)

private lemma grid_row_case {ι κ V : Type*} [DecidableEq ι] [DecidableEq κ] [DecidableEq V]
    (G : SimpleGraph V) (α_orig α' : ℕ) (hα'eq : (α' : ℝ) = 4 * (α_orig : ℝ)) (hα'pos : 1 ≤ α')
    (I_rows : Finset ι) (_J_cols : Finset κ)
    (U_grid : Finset ((ι × κ) × V)) (cell : ι → κ → Finset ((ι × κ) × V))
    (hcell_fst : ∀ i j p, p ∈ cell i j → p.1.1 = i ∧ p.1.2 = j)
    (hG_ind : ∀ S ⊆ U_grid, (gridGraph G).IsIndepSet (S : Set ((ι × κ) × V)) → S.card ≤ α')
    (hG_TF : TriangleFree (gridGraph G) U_grid)
    (hG_cross : ∀ p ∈ U_grid, ∀ q ∈ U_grid,
      p.1.1 ≠ q.1.1 → p.1.2 ≠ q.1.2 → ¬ (gridGraph G).Adj p q)
    (X M₀ : ℕ) (T : ℝ) (hT_pos : 0 < T) (hT_ge : (I_rows.card : ℝ) ≤ T) (hs₀_pos : 1 ≤ I_rows.card)
    (I_cur : Finset ι) (J_cur : Finset κ)
    (hs1_2 : I_rows.card < 2 * I_cur.card)
    (hNoBad : ∀ i ∈ I_cur, ∀ J₀ ⊆ J_cur, J₀.card ≤ Nat.floor (T / (I_rows.card : ℝ)) →
      ∀ S ⊆ J₀.biUnion (cell i), (gridGraph G).IsIndepSet (S : Set ((ι × κ) × V)) →
        (S.card : ℝ) ≤ 2 * (α' : ℝ) / (I_rows.card : ℝ))
    (R_row : ι → Finset ((ι × κ) × V))
    (hR_sub' : ∀ i ∈ I_cur, R_row i ⊆ J_cur.biUnion (cell i))
    (hR_card' : ∀ i ∈ I_cur, (R_row i).card = M₀)
    (hR_disj : Set.PairwiseDisjoint (I_cur : Set ι) R_row)
    (U_trim : Finset ((ι × κ) × V)) (hU_trim_eq : U_trim = I_cur.biUnion R_row)
    (hU_trim_sub : U_trim ⊆ U_grid)
    (N_grid : ℝ) (hN_grid_eq : N_grid = (I_cur.card : ℝ) * (M₀ : ℝ))
    (hN_grid_ge : (I_rows.card : ℝ) * T * (X : ℝ) / 6 ≤ N_grid)
    (hN_4a : 4 * (α' : ℝ) ≤ N_grid)
    (C_col : κ → Finset ((ι × κ) × V))
    (hC_col_def : ∀ j, C_col j = U_trim.filter (fun p => p.1.2 = j))
    (High_row : Finset ((ι × κ) × V)) (hHigh_row_sub : High_row ⊆ U_trim)
    (hHigh_row_deg : ∀ p ∈ High_row, N_grid / (8 * (α' : ℝ)) ≤ ((neighbors (gridGraph G) (R_row p.1.1) p).card : ℝ))
    (hRow_case : N_grid / 4 ≤ (High_row.card : ℝ)) :
    ((I_rows.card : ℝ) ^ 2 * T * (X : ℝ) ≤ 3072 * (α_orig : ℝ) ^ 2) ∨
    ((I_rows.card : ℝ) ^ 3 * T ^ 3 * (X : ℝ) ^ 2 ≤ 9663676416 * (α_orig : ℝ) ^ 5) := by
  classical
  let s₀ : ℕ := I_rows.card
  let s₁ : ℕ := I_cur.card
  have hs₁_pos : 1 ≤ s₁ := by omega
  let k_col : ℕ := Nat.floor (T / (s₀ : ℝ))
  have hN_nn : 0 ≤ N_grid := le_trans (by positivity) hN_4a
  have hM₀_rpos : (0 : ℝ) < (M₀ : ℝ) := by
    have hNpos : 0 < N_grid := lt_of_lt_of_le (by positivity) hN_4a
    rw [hN_grid_eq] at hNpos
    have hs1r : (0 : ℝ) < (s₁ : ℝ) := by exact_mod_cast hs₁_pos
    exact pos_of_mul_pos_right hNpos hs1r.le
  let I_good := I_cur.filter (fun i => (R_row i ∩ High_row).Nonempty)
  have hI_good_sub : High_row ⊆ I_good.biUnion R_row := by
    intro p hp
    have hpU : p ∈ U_trim := hHigh_row_sub hp
    rw [hU_trim_eq] at hpU
    obtain ⟨i, hi, hpR⟩ := mem_biUnion.mp hpU
    refine mem_biUnion.mpr ⟨i, mem_filter.mpr ⟨hi, ⟨p, mem_inter.mpr ⟨hpR, hp⟩⟩⟩, hpR⟩
  have hI_good_ge : (s₁ : ℝ) / 4 ≤ (I_good.card : ℝ) := by
    have hc : N_grid / 4 ≤ (I_good.card : ℝ) * (M₀ : ℝ) := by
      calc
        N_grid / 4 ≤ (High_row.card : ℝ) := hRow_case
        _ ≤ ∑ i ∈ I_good, ((R_row i).card : ℝ) := by exact_mod_cast (card_le_card hI_good_sub).trans card_biUnion_le
        _ = ∑ _i ∈ I_good, (M₀ : ℝ) := sum_congr rfl fun i hi => by
            exact_mod_cast hR_card' i (filter_subset _ _ hi)
        _ = (I_good.card : ℝ) * (M₀ : ℝ) := by rw [sum_const, nsmul_eq_mul]
    rw [hN_grid_eq] at hc
    exact le_of_mul_le_mul_right (by linarith [hc]) hM₀_rpos
  have hexists_I_row : ∀ i : ι, ∃ I_i ⊆ R_row i,
      i ∈ I_good → (gridGraph G).IsIndepSet (I_i : Set ((ι × κ) × V)) ∧ N_grid / (8 * (α' : ℝ)) ≤ (I_i.card : ℝ) := by
    intro i
    by_cases hi : i ∈ I_good
    · obtain ⟨p, hp⟩ := (mem_filter.mp hi).2
      have hp_hr : p ∈ High_row := (mem_inter.mp hp).2
      have hpi : p.1.1 = i := by
        obtain ⟨j', _, hqcell⟩ := mem_biUnion.mp (hR_sub' i (filter_subset _ _ hi) (mem_inter.mp hp).1)
        exact (hcell_fst i j' p hqcell).1
      refine ⟨neighbors (gridGraph G) (R_row i) p, neighbors_subset, fun _ => ⟨?_, ?_⟩⟩
      · refine triangleFree_neighbors_indep ?_ (mem_inter.mp hp).1
        exact triangleFree_subset hG_TF (fun q hq => hU_trim_sub (hU_trim_eq ▸ mem_biUnion.mpr ⟨i, filter_subset _ _ hi, hq⟩))
      · rw [← hpi]
        exact hHigh_row_deg p hp_hr
    · exact ⟨∅, empty_subset _, fun hi' => absurd hi' hi⟩
  choose I_row hI_row_sub hI_row_prop using hexists_I_row
  have hI_row_sub' : ∀ i ∈ I_good, I_row i ⊆ R_row i := fun i _ => hI_row_sub i
  have hI_row_ind' : ∀ i ∈ I_good, (gridGraph G).IsIndepSet (I_row i : Set ((ι × κ) × V)) :=
    fun i hi => (hI_row_prop i hi).1
  have hI_row_ge' : ∀ i ∈ I_good, N_grid / (8 * (α' : ℝ)) ≤ ((I_row i).card : ℝ) :=
    fun i hi => (hI_row_prop i hi).2
  let J_full (i : ι) : Finset κ :=
    J_cur.filter (fun j => 4 * (α' : ℝ) / T ≤ ((I_row i ∩ cell i j).card : ℝ))
  have hJ_full_le : ∀ i ∈ I_good, (J_full i).card ≤ k_col := by
    intro i hi
    have hi_cur : i ∈ I_cur := (filter_subset _ _) hi
    by_contra! hgt
    have h1 : 1 ≤ T / (s₀ : ℝ) := (le_div_iff₀ (by exact_mod_cast hs₀_pos)).mpr (by linarith)
    have hfl : Nat.floor ((T / (s₀ : ℝ)) / 2) + 1 ≤ k_col := floor_half_add_one_le h1
    have hle_full : Nat.floor ((T / (s₀ : ℝ)) / 2) + 1 ≤ (J_full i).card := by omega
    obtain ⟨J₀, hJ₀_sub, hJ₀_card⟩ := exists_subset_card_eq hle_full
    have hJ₀_le_k : J₀.card ≤ k_col := by omega
    have hJ₀_cur : J₀ ⊆ J_cur := hJ₀_sub.trans (filter_subset _ _)
    let S_bad := I_row i ∩ J₀.biUnion (cell i)
    have hS_bad_ind : (gridGraph G).IsIndepSet (S_bad : Set ((ι × κ) × V)) :=
      indep_mono inter_subset_left (hI_row_ind' i hi)
    have hS_bad_le := hNoBad i hi_cur J₀ hJ₀_cur hJ₀_le_k S_bad inter_subset_right hS_bad_ind
    have hdisj_cells : Set.PairwiseDisjoint (J₀ : Set κ) (fun j => I_row i ∩ cell i j) := by
      intro j₁ _ j₂ _ hne
      change Disjoint _ _
      rw [disjoint_left]
      intro p hp1 hp2
      exact hne ((hcell_fst i j₁ p (mem_inter.mp hp1).2).2.symm.trans
        (hcell_fst i j₂ p (mem_inter.mp hp2).2).2)
    have hS_eq : S_bad = J₀.biUnion (fun j => I_row i ∩ cell i j) := by
      ext p
      rw [mem_inter, mem_biUnion, mem_biUnion]
      constructor
      · rintro ⟨hpI, j, hj, hpc⟩
        exact ⟨j, hj, mem_inter.mpr ⟨hpI, hpc⟩⟩
      · rintro ⟨j, hj, hp⟩
        rw [mem_inter] at hp
        exact ⟨hp.1, j, hj, hp.2⟩
    have hS_bad_gt : 2 * (α' : ℝ) / (s₀ : ℝ) < (S_bad.card : ℝ) := by
      have h1' : (S_bad.card : ℝ) = ∑ j ∈ J₀, ((I_row i ∩ cell i j).card : ℝ) := by
        have : S_bad.card = ∑ j ∈ J₀, (I_row i ∩ cell i j).card := by
          rw [hS_eq, card_biUnion hdisj_cells]
        exact_mod_cast this
      have h2' : (J₀.card : ℝ) * (4 * (α' : ℝ) / T) ≤ (S_bad.card : ℝ) := by
        rw [h1', ← nsmul_eq_mul, ← sum_const]
        exact sum_le_sum fun j hj => (mem_filter.mp (hJ₀_sub hj)).2
      have hlt_half : (T / (s₀ : ℝ)) / 2 < (J₀.card : ℝ) := by
        rw [hJ₀_card]
        push_cast
        exact Nat.lt_floor_add_one _
      have hpos_coef : 0 < 4 * (α' : ℝ) / T := by positivity
      have h3' : ((T / (s₀ : ℝ)) / 2) * (4 * (α' : ℝ) / T) < (J₀.card : ℝ) * (4 * (α' : ℝ) / T) := by
        gcongr
      have heq_coef : ((T / (s₀ : ℝ)) / 2) * (4 * (α' : ℝ) / T) = 2 * (α' : ℝ) / (s₀ : ℝ) := by
        have hT0 : T ≠ 0 := hT_pos.ne'
        field_simp; ring
      linarith
    linarith
  have hFull_verts_le : ∀ i ∈ I_good,
      (((I_row i ∩ (J_full i).biUnion (cell i)).card : ℝ)) ≤ 2 * (α' : ℝ) / (s₀ : ℝ) := by
    intro i hi
    refine hNoBad i (filter_subset _ _ hi) (J_full i) (filter_subset _ _) (hJ_full_le i hi)
      (I_row i ∩ (J_full i).biUnion (cell i)) inter_subset_right
      (indep_mono inter_subset_left (hI_row_ind' i hi))
  by_cases hFull_big : N_grid / (16 * (α' : ℝ)) ≤ 2 * (α' : ℝ) / (s₀ : ℝ)
  · left
    have h1 : (s₀ : ℝ) * N_grid ≤ 32 * (α' : ℝ) ^ 2 := by
      have hs₀r : (0 : ℝ) < (s₀ : ℝ) := by exact_mod_cast hs₀_pos
      have hα'r : (0 : ℝ) < (α' : ℝ) := by exact_mod_cast hα'pos
      have hmul : (s₀ : ℝ) * N_grid / (16 * (α' : ℝ)) ≤ 2 * (α' : ℝ) := by
        calc
          (s₀ : ℝ) * N_grid / (16 * (α' : ℝ)) = (s₀ : ℝ) * (N_grid / (16 * (α' : ℝ))) := by ring
          _ ≤ (s₀ : ℝ) * (2 * (α' : ℝ) / (s₀ : ℝ)) := by gcongr
          _ = 2 * (α' : ℝ) := by field_simp
      rw [div_le_iff₀ (by positivity)] at hmul
      linarith
    have h2 : (s₀ : ℝ) * ((s₀ : ℝ) * T * (X : ℝ) / 6) ≤ 32 * (α' : ℝ) ^ 2 :=
      (mul_le_mul_of_nonneg_left hN_grid_ge (by positivity)).trans h1
    rw [hα'eq] at h2
    have heq : (s₀ : ℝ) * ((s₀ : ℝ) * T * (X : ℝ) / 6) = ((s₀ : ℝ) ^ 2 * T * (X : ℝ)) / 6 := by ring
    have heq2 : 32 * (4 * (α_orig : ℝ)) ^ 2 = 512 * (α_orig : ℝ) ^ 2 := by ring
    dsimp [s₀] at h2 heq
    linarith only [h2, heq, heq2]
  · right
    have hFull_small : 2 * (α' : ℝ) / (s₀ : ℝ) < N_grid / (16 * (α' : ℝ)) := lt_of_not_ge hFull_big
    let I'_row (i : ι) : Finset ((ι × κ) × V) := I_row i \ (J_full i).biUnion (cell i)
    have hI'_row_sub : ∀ i ∈ I_good, I'_row i ⊆ R_row i := fun i hi =>
      sdiff_subset.trans (hI_row_sub' i hi)
    have hI'_row_ind : ∀ i ∈ I_good, (gridGraph G).IsIndepSet (I'_row i : Set ((ι × κ) × V)) :=
      fun i hi => indep_mono sdiff_subset (hI_row_ind' i hi)
    have hI'_row_ge : ∀ i ∈ I_good, N_grid / (16 * (α' : ℝ)) ≤ ((I'_row i).card : ℝ) := by
      intro i hi
      have h1 : (I_row i).card ≤ (I'_row i).card + (I_row i ∩ (J_full i).biUnion (cell i)).card := by
        have := (card_sdiff_add_card_inter (I_row i) ((J_full i).biUnion (cell i))).symm
        dsimp [I'_row]
        omega
      have h1r : ((I_row i).card : ℝ) ≤
          ((I'_row i).card : ℝ) + ((I_row i ∩ (J_full i).biUnion (cell i)).card : ℝ) := by
        exact_mod_cast h1
      linarith only [hI_row_ge' i hi, hFull_verts_le i hi, hFull_small, h1r,
        show N_grid / (8 * (α' : ℝ)) = 2 * (N_grid / (16 * (α' : ℝ))) by ring]
    let U' : Finset ((ι × κ) × V) := I_good.biUnion I'_row
    have hU'_disj : Set.PairwiseDisjoint (I_good : Set ι) I'_row := by
      intro i₁ hi₁ i₂ hi₂ hne
      change Disjoint _ _
      rw [disjoint_left]
      intro p hp1 hp2
      exact (disjoint_left.mp (hR_disj (filter_subset _ _ hi₁) (filter_subset _ _ hi₂) hne))
        (hI'_row_sub i₁ hi₁ hp1) (hI'_row_sub i₂ hi₂ hp2)
    have hU'_card : (s₁ : ℝ) * N_grid / (64 * (α' : ℝ)) ≤ (U'.card : ℝ) := by
      have h1 : (U'.card : ℝ) = ∑ i ∈ I_good, ((I'_row i).card : ℝ) := by
        exact_mod_cast card_biUnion hU'_disj
      rw [h1]
      calc
        (s₁ : ℝ) * N_grid / (64 * (α' : ℝ)) = ((s₁ : ℝ) / 4) * (N_grid / (16 * (α' : ℝ))) := by ring
        _ ≤ (I_good.card : ℝ) * (N_grid / (16 * (α' : ℝ))) :=
            mul_le_mul_of_nonneg_right hI_good_ge (div_nonneg hN_nn (by positivity))
        _ = ∑ _i ∈ I_good, (N_grid / (16 * (α' : ℝ))) := by rw [sum_const, nsmul_eq_mul]
        _ ≤ ∑ i ∈ I_good, ((I'_row i).card : ℝ) := sum_le_sum hI'_row_ge
    have hb_le : ∀ j ∈ J_cur, ((U' ∩ C_col j).card : ℝ) ≤ 4 * (s₁ : ℝ) * (α' : ℝ) / T := by
      intro j hj
      have hsub : U' ∩ C_col j ⊆ I_good.biUnion (fun i => I'_row i ∩ cell i j) := by
        intro p hp
        obtain ⟨hpU', hpC⟩ := mem_inter.mp hp
        obtain ⟨i, hi, hpI'⟩ := mem_biUnion.mp hpU'
        have hpR := hI'_row_sub i hi hpI'
        obtain ⟨j', _, hpcell⟩ := mem_biUnion.mp (hR_sub' i (filter_subset _ _ hi) hpR)
        rw [hC_col_def] at hpC
        have hj' : j' = j := (hcell_fst i j' p hpcell).2.symm.trans (mem_filter.mp hpC).2
        exact mem_biUnion.mpr ⟨i, hi, mem_inter.mpr ⟨hpI', hj' ▸ hpcell⟩⟩
      have h1 : (U' ∩ C_col j).card ≤ ∑ i ∈ I_good, (I'_row i ∩ cell i j).card :=
        (card_le_card hsub).trans card_biUnion_le
      have h1r : ((U' ∩ C_col j).card : ℝ) ≤ ∑ i ∈ I_good, ((I'_row i ∩ cell i j).card : ℝ) := by
        exact_mod_cast h1
      have heach : ∀ i ∈ I_good, ((I'_row i ∩ cell i j).card : ℝ) ≤ 4 * (α' : ℝ) / T := by
        intro i hi
        by_cases hjf : j ∈ J_full i
        · have hEmpty : I'_row i ∩ cell i j = ∅ := by
            rw [eq_empty_iff_forall_notMem]
            intro p hp
            obtain ⟨hpI', hpcell⟩ := mem_inter.mp hp
            exact (mem_sdiff.mp hpI').2 (mem_biUnion.mpr ⟨j, hjf, hpcell⟩)
          rw [hEmpty, card_empty, Nat.cast_zero]
          positivity
        · have hlt : ((I_row i ∩ cell i j).card : ℝ) < 4 * (α' : ℝ) / T := by
            by_contra! hge
            exact hjf (mem_filter.mpr ⟨hj, hge⟩)
          have hsub_i : I'_row i ∩ cell i j ⊆ I_row i ∩ cell i j :=
            inter_subset_inter sdiff_subset Subset.rfl
          have hc : ((I'_row i ∩ cell i j).card : ℝ) ≤ ((I_row i ∩ cell i j).card : ℝ) := by
            exact_mod_cast card_le_card hsub_i
          exact hc.trans hlt.le
      have hIgood_le : (I_good.card : ℝ) ≤ (s₁ : ℝ) := by exact_mod_cast card_le_card (filter_subset _ _)
      calc
        ((U' ∩ C_col j).card : ℝ) ≤ ∑ i ∈ I_good, ((I'_row i ∩ cell i j).card : ℝ) := h1r
        _ ≤ ∑ _i ∈ I_good, (4 * (α' : ℝ) / T) := sum_le_sum heach
        _ = (I_good.card : ℝ) * (4 * (α' : ℝ) / T) := by rw [sum_const, nsmul_eq_mul]
        _ ≤ (s₁ : ℝ) * (4 * (α' : ℝ) / T) := by gcongr
        _ = 4 * (s₁ : ℝ) * (α' : ℝ) / T := by ring
    have hK_col : ∀ j : κ, ∃ K_j ⊆ U' ∩ C_col j,
        j ∈ J_cur → (gridGraph G).IsIndepSet (K_j : Set ((ι × κ) × V)) ∧ (U' ∩ C_col j).card ≤ 2 * K_j.card ^ 2 := by
      intro j
      by_cases hj : j ∈ J_cur
      · obtain ⟨K_j, h1, h2, h3⟩ := card_triangle_free_subset (gridGraph G) (U' ∩ C_col j)
          (triangleFree_subset hG_TF (inter_subset_right.trans (by
            rw [hC_col_def]; exact (filter_subset _ _).trans hU_trim_sub)))
        exact ⟨K_j, h1, fun _ => ⟨h2, h3⟩⟩
      · exact ⟨∅, empty_subset _, fun hj' => absurd hj' hj⟩
    choose K_col hK_sub hK_prop using hK_col
    have hK_sub' : ∀ j ∈ J_cur, K_col j ⊆ U' ∩ C_col j := fun j _ => hK_sub j
    have hK_ind' : ∀ j ∈ J_cur, (gridGraph G).IsIndepSet (K_col j : Set ((ι × κ) × V)) :=
      fun j hj => (hK_prop j hj).1
    have hK_sq' : ∀ j ∈ J_cur, (U' ∩ C_col j).card ≤ 2 * (K_col j).card ^ 2 :=
      fun j hj => (hK_prop j hj).2
    let K_all := J_cur.biUnion K_col
    have hK_all_ind : (gridGraph G).IsIndepSet (K_all : Set ((ι × κ) × V)) := by
      rw [(gridGraph G).isIndepSet_iff]
      intro p hp q hq hpq hadj
      simp only [K_all, mem_coe, mem_biUnion] at hp hq
      obtain ⟨j₁, hj₁, hpK⟩ := hp
      obtain ⟨j₂, hj₂, hqK⟩ := hq
      by_cases hj : j₁ = j₂
      · subst hj
        exact ((gridGraph G).isIndepSet_iff.mp (hK_ind' j₁ hj₁)) hpK hqK hpq hadj
      · have hpC := hK_sub' j₁ hj₁ hpK
        have hqC := hK_sub' j₂ hj₂ hqK
        have hp_col : p.1.2 = j₁ := by rw [hC_col_def] at hpC; exact (mem_filter.mp (mem_inter.mp hpC).2).2
        have hq_col : q.1.2 = j₂ := by rw [hC_col_def] at hqC; exact (mem_filter.mp (mem_inter.mp hqC).2).2
        have hp_U' : p ∈ U' := (mem_inter.mp hpC).1
        have hq_U' : q ∈ U' := (mem_inter.mp hqC).1
        obtain ⟨i₁, hi₁, hpI'⟩ := mem_biUnion.mp hp_U'
        obtain ⟨i₂, hi₂, hqI'⟩ := mem_biUnion.mp hq_U'
        have hpi₁ : p.1.1 = i₁ := by
          obtain ⟨j', _, hpcell⟩ := mem_biUnion.mp (hR_sub' i₁ (filter_subset _ _ hi₁) (hI'_row_sub i₁ hi₁ hpI'))
          exact (hcell_fst i₁ j' p hpcell).1
        have hqi₂ : q.1.1 = i₂ := by
          obtain ⟨j', _, hqcell⟩ := mem_biUnion.mp (hR_sub' i₂ (filter_subset _ _ hi₂) (hI'_row_sub i₂ hi₂ hqI'))
          exact (hcell_fst i₂ j' q hqcell).1
        have hi_eq : i₁ = i₂ := by
          by_contra hni
          exact hG_cross p (hU_trim_sub (hU_trim_eq ▸ mem_biUnion.mpr ⟨i₁, filter_subset _ _ hi₁, hI'_row_sub i₁ hi₁ hpI'⟩))
            q (hU_trim_sub (hU_trim_eq ▸ mem_biUnion.mpr ⟨i₂, filter_subset _ _ hi₂, hI'_row_sub i₂ hi₂ hqI'⟩))
            (by rw [hpi₁, hqi₂]; exact hni) (by rw [hp_col, hq_col]; exact hj) hadj
        subst hi_eq
        exact ((gridGraph G).isIndepSet_iff.mp (hI'_row_ind i₁ hi₁)) hpI' hqI' hpq hadj
    have hK_disj : Set.PairwiseDisjoint (J_cur : Set κ) K_col := by
      intro j₁ hj₁ j₂ hj₂ hne
      change Disjoint _ _
      rw [disjoint_left]
      intro p hp1 hp2
      have h1 := (mem_inter.mp (hK_sub' j₁ hj₁ hp1)).2
      have h2 := (mem_inter.mp (hK_sub' j₂ hj₂ hp2)).2
      rw [hC_col_def] at h1 h2
      exact hne ((mem_filter.mp h1).2.symm.trans (mem_filter.mp h2).2)
    have hK_sum_le : ∑ j ∈ J_cur, ((K_col j).card : ℝ) ≤ (α' : ℝ) := by
      have h1 : K_all.card = ∑ j ∈ J_cur, (K_col j).card := card_biUnion hK_disj
      have hK_all_U : K_all ⊆ U_grid := by
        intro p hp
        obtain ⟨j, hj, hpK⟩ := mem_biUnion.mp hp
        have hC := (mem_inter.mp (hK_sub' j hj hpK)).2
        rw [hC_col_def] at hC
        exact hU_trim_sub (filter_subset _ _ hC)
      have h2 : K_all.card ≤ α' := hG_ind K_all hK_all_U hK_all_ind
      exact_mod_cast h1 ▸ h2
    have hU'_part : U'.card = ∑ j ∈ J_cur, (U' ∩ C_col j).card := by
      have hdisj_c : Set.PairwiseDisjoint (J_cur : Set κ) (fun j => U' ∩ C_col j) := by
        intro j₁ _ j₂ _ hne
        change Disjoint _ _
        rw [disjoint_left]
        intro p hp1 hp2
        have h1 := (mem_inter.mp hp1).2
        have h2 := (mem_inter.mp hp2).2
        rw [hC_col_def] at h1 h2
        exact hne ((mem_filter.mp h1).2.symm.trans (mem_filter.mp h2).2)
      have heq : U' = J_cur.biUnion (fun j => U' ∩ C_col j) := by
        ext p
        dsimp [U']
        rw [mem_biUnion, mem_biUnion]
        constructor
        · rintro ⟨i, hi, hpI'⟩
          have hpR := hI'_row_sub i hi hpI'
          obtain ⟨j, hj, hpcell⟩ := mem_biUnion.mp (hR_sub' i (filter_subset _ _ hi) hpR)
          have hpU : p ∈ U_trim := hU_trim_eq ▸ mem_biUnion.mpr ⟨i, filter_subset _ _ hi, hpR⟩
          refine ⟨j, hj, mem_inter.mpr ⟨mem_biUnion.mpr ⟨i, hi, hpI'⟩, ?_⟩⟩
          rw [hC_col_def]
          exact mem_filter.mpr ⟨hpU, (hcell_fst i j p hpcell).2⟩
        · rintro ⟨_, _, hp⟩
          exact mem_biUnion.mp (mem_inter.mp hp).1
      conv_lhs => rw [heq]
      exact card_biUnion hdisj_c
    let M_col : ℝ := 4 * (s₁ : ℝ) * (α' : ℝ) / T
    have hM_col_nn : 0 ≤ M_col := div_nonneg (by positivity) hT_pos.le
    have hU'_le_sqrt : (U'.card : ℝ) ≤ Real.sqrt (2 * M_col) * (α' : ℝ) := by
      have hU'_r : (U'.card : ℝ) = ∑ j ∈ J_cur, ((U' ∩ C_col j).card : ℝ) := by exact_mod_cast hU'_part
      rw [hU'_r]
      have hterm : ∀ j ∈ J_cur, ((U' ∩ C_col j).card : ℝ) ≤
          Real.sqrt (2 * M_col) * ((K_col j).card : ℝ) := by
        intro j hj
        have hb1 : ((U' ∩ C_col j).card : ℝ) ≤ M_col := hb_le j hj
        have hb2 : ((U' ∩ C_col j).card : ℝ) ≤ 2 * ((K_col j).card : ℝ) ^ 2 := by
          exact_mod_cast hK_sq' j hj
        have hsq : ((U' ∩ C_col j).card : ℝ) ^ 2 ≤
            (Real.sqrt (2 * M_col) * ((K_col j).card : ℝ)) ^ 2 := by
          rw [mul_pow, Real.sq_sqrt (mul_nonneg (by norm_num) hM_col_nn)]
          calc
            ((U' ∩ C_col j).card : ℝ) ^ 2
              = ((U' ∩ C_col j).card : ℝ) * ((U' ∩ C_col j).card : ℝ) := by ring
            _ ≤ M_col * (2 * ((K_col j).card : ℝ) ^ 2) :=
                mul_le_mul hb1 hb2 (by positivity) hM_col_nn
            _ = 2 * M_col * ((K_col j).card : ℝ) ^ 2 := by ring
        exact le_of_pow_le_pow_left₀ (by decide) (by positivity) hsq
      calc
        ∑ j ∈ J_cur, ((U' ∩ C_col j).card : ℝ)
          ≤ ∑ j ∈ J_cur, Real.sqrt (2 * M_col) * ((K_col j).card : ℝ) := sum_le_sum hterm
        _ = Real.sqrt (2 * M_col) * ∑ j ∈ J_cur, ((K_col j).card : ℝ) := by rw [mul_sum]
        _ ≤ Real.sqrt (2 * M_col) * (α' : ℝ) := mul_le_mul_of_nonneg_left hK_sum_le (Real.sqrt_nonneg _)
    have hU'_sq : (U'.card : ℝ) ^ 2 ≤ 2 * M_col * (α' : ℝ) ^ 2 := by
      have hsq := pow_le_pow_left₀ (by positivity) hU'_le_sqrt 2
      rw [mul_pow, Real.sq_sqrt (mul_nonneg (by norm_num) hM_col_nn)] at hsq
      exact hsq
    have hs1_ge : (s₀ : ℝ) / 2 ≤ (s₁ : ℝ) := by
      have : (s₀ : ℝ) ≤ 2 * (s₁ : ℝ) := by exact_mod_cast hs1_2.le
      linarith
    have hs1_posR : (0 : ℝ) < (s₁ : ℝ) := by exact_mod_cast hs₁_pos
    have hmain_r : (s₁ : ℝ) * T * N_grid ^ 2 ≤ 8 * 64 ^ 2 * (α' : ℝ) ^ 5 := by
      have h1 : ((s₁ : ℝ) * N_grid / (64 * (α' : ℝ))) ^ 2 ≤ 8 * (s₁ : ℝ) * (α' : ℝ) ^ 3 / T := by
        have hsq := pow_le_pow_left₀ (by positivity) hU'_card 2
        have h2M : 2 * M_col * (α' : ℝ) ^ 2 = 8 * (s₁ : ℝ) * (α' : ℝ) ^ 3 / T := by
          dsimp [M_col]; ring
        linarith
      have h2 : (s₁ : ℝ) ^ 2 * N_grid ^ 2 * T ≤ 8 * 64 ^ 2 * (s₁ : ℝ) * (α' : ℝ) ^ 5 := by
        have heq1 : ((s₁ : ℝ) * N_grid / (64 * (α' : ℝ))) ^ 2 =
            ((s₁ : ℝ) ^ 2 * N_grid ^ 2) / (64 ^ 2 * (α' : ℝ) ^ 2) := by ring
        rw [heq1, div_le_div_iff₀ (by positivity) hT_pos] at h1
        linarith [show (8 * (s₁ : ℝ) * (α' : ℝ) ^ 3) * (64 ^ 2 * (α' : ℝ) ^ 2) =
          8 * 64 ^ 2 * (s₁ : ℝ) * (α' : ℝ) ^ 5 by ring]
      exact le_of_mul_le_mul_left (by linarith [h2]) hs1_posR
    have hfinal_r : ((s₀ : ℝ) / 2) * T * ((s₀ : ℝ) * T * (X : ℝ) / 6) ^ 2 ≤
        8 * 64 ^ 2 * (α' : ℝ) ^ 5 := by
      calc
        ((s₀ : ℝ) / 2) * T * ((s₀ : ℝ) * T * (X : ℝ) / 6) ^ 2
          ≤ (s₁ : ℝ) * T * N_grid ^ 2 :=
            mul_le_mul (mul_le_mul_of_nonneg_right hs1_ge hT_pos.le)
              (pow_le_pow_left₀
                (div_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg s₀) hT_pos.le) (Nat.cast_nonneg X)) (by norm_num))
                hN_grid_ge 2)
              (sq_nonneg _) (mul_nonneg (Nat.cast_nonneg s₁) hT_pos.le)
        _ ≤ 8 * 64 ^ 2 * (α' : ℝ) ^ 5 := hmain_r
    rw [hα'eq] at hfinal_r
    have heq1 : ((s₀ : ℝ) / 2) * T * ((s₀ : ℝ) * T * (X : ℝ) / 6) ^ 2 =
        ((s₀ : ℝ) ^ 3 * T ^ 3 * (X : ℝ) ^ 2) / 72 := by ring
    have heq2 : 8 * 64 ^ 2 * (4 * (α_orig : ℝ)) ^ 5 = 33554432 * (α_orig : ℝ) ^ 5 := by ring
    have hα5 : (0 : ℝ) ≤ (α_orig : ℝ) ^ 5 := by positivity
    dsimp [s₀] at hfinal_r heq1
    linarith only [hfinal_r, heq1, heq2, hα5]

private lemma grid_col_case {ι κ V : Type*} [DecidableEq ι] [DecidableEq κ] [DecidableEq V]
    (G : SimpleGraph V) (α_orig α' : ℕ) (hα'eq : (α' : ℝ) = 4 * (α_orig : ℝ)) (hα'pos : 1 ≤ α')
    (I_rows : Finset ι) (_J_cols : Finset κ)
    (U_grid : Finset ((ι × κ) × V)) (cell : ι → κ → Finset ((ι × κ) × V))
    (hcell_fst : ∀ i j p, p ∈ cell i j → p.1.1 = i ∧ p.1.2 = j)
    (hG_ind : ∀ S ⊆ U_grid, (gridGraph G).IsIndepSet (S : Set ((ι × κ) × V)) → S.card ≤ α')
    (hG_TF : TriangleFree (gridGraph G) U_grid)
    (hG_cross : ∀ p ∈ U_grid, ∀ q ∈ U_grid,
      p.1.1 ≠ q.1.1 → p.1.2 ≠ q.1.2 → ¬ (gridGraph G).Adj p q)
    (X M₀ : ℕ) (hX_pos : 1 ≤ X) (T : ℝ) (hTX6 : 6 ≤ T * (X : ℝ))
    (I_cur : Finset ι) (J_cur : Finset κ) (hs1_2 : I_rows.card < 2 * I_cur.card)
    (R_row : ι → Finset ((ι × κ) × V))
    (hR_sub' : ∀ i ∈ I_cur, R_row i ⊆ J_cur.biUnion (cell i))
    (hR_card' : ∀ i ∈ I_cur, (R_row i).card = M₀)
    (hR_disj : Set.PairwiseDisjoint (I_cur : Set ι) R_row)
    (hM₀_ge : T * (X : ℝ) / 3 ≤ (M₀ : ℝ)) (hM₀_pos : 1 ≤ M₀)
    (U_trim : Finset ((ι × κ) × V)) (hU_trim_eq : U_trim = I_cur.biUnion R_row)
    (hU_trim_sub : U_trim ⊆ U_grid)
    (N_grid : ℝ) (hN_grid_eq : N_grid = (I_cur.card : ℝ) * (M₀ : ℝ))
    (C_col : κ → Finset ((ι × κ) × V))
    (hC_col_def : ∀ j, C_col j = U_trim.filter (fun p => p.1.2 = j))
    (hC_col_le : ∀ j : κ, (C_col j).card ≤ I_cur.card * X)
    (High_col : Finset ((ι × κ) × V)) (hHigh_col_sub : High_col ⊆ U_trim)
    (hHigh_col_deg : ∀ p ∈ High_col, N_grid / (8 * (α' : ℝ)) ≤ ((neighbors (gridGraph G) (C_col p.1.2) p).card : ℝ))
    (hCol_case : N_grid / 4 ≤ (High_col.card : ℝ)) :
    (I_rows.card : ℝ) ^ 2 * T ^ 3 * (X : ℝ) ≤ 56623104 * (α_orig : ℝ) ^ 4 := by
  classical
  let s₀ : ℕ := I_rows.card
  let s₁ : ℕ := I_cur.card
  have hs₁_pos : 1 ≤ s₁ := by omega
  have hN_nn : 0 ≤ N_grid := by rw [hN_grid_eq]; positivity
  let J_good := J_cur.filter (fun j => (C_col j ∩ High_col).Nonempty)
  have hHigh_col_sub_U : High_col ⊆ J_good.biUnion C_col := by
    intro p hp
    have hpU : p ∈ U_trim := hHigh_col_sub hp
    have hpU' : p ∈ I_cur.biUnion R_row := hU_trim_eq ▸ hpU
    obtain ⟨i, hi, hpR⟩ := mem_biUnion.mp hpU'
    obtain ⟨j, hj, hpcell⟩ := mem_biUnion.mp (hR_sub' i hi hpR)
    have hpj : p.1.2 = j := (hcell_fst i j p hpcell).2
    have hpC : p ∈ C_col j := by rw [hC_col_def]; exact mem_filter.mpr ⟨hpU, hpj⟩
    exact mem_biUnion.mpr ⟨j, mem_filter.mpr ⟨hj, ⟨p, mem_inter.mpr ⟨hpC, hp⟩⟩⟩, hpC⟩
  have hJ_good_ge : N_grid / (4 * (s₁ : ℝ) * (X : ℝ)) ≤ (J_good.card : ℝ) := by
    have hc : N_grid / 4 ≤ (J_good.card : ℝ) * ((s₁ : ℝ) * (X : ℝ)) := by
      calc
        N_grid / 4 ≤ (High_col.card : ℝ) := hCol_case
        _ ≤ ∑ j ∈ J_good, ((C_col j).card : ℝ) := by
            exact_mod_cast (card_le_card hHigh_col_sub_U).trans card_biUnion_le
        _ ≤ ∑ _j ∈ J_good, ((s₁ : ℝ) * (X : ℝ)) :=
            sum_le_sum fun j _ => by exact_mod_cast hC_col_le j
        _ = (J_good.card : ℝ) * ((s₁ : ℝ) * (X : ℝ)) := by rw [sum_const, nsmul_eq_mul]
    rw [div_le_iff₀ (by
      have hs1r : (0 : ℝ) < (s₁ : ℝ) := by exact_mod_cast hs₁_pos
      have hXr : (0 : ℝ) < (X : ℝ) := by exact_mod_cast hX_pos
      positivity)]
    linarith
  have hexists_I_col : ∀ j : κ, ∃ I_j ⊆ C_col j,
      j ∈ J_good → (gridGraph G).IsIndepSet (I_j : Set ((ι × κ) × V)) ∧ N_grid / (8 * (α' : ℝ)) ≤ (I_j.card : ℝ) := by
    intro j
    by_cases hj : j ∈ J_good
    · obtain ⟨p, hp⟩ := (mem_filter.mp hj).2
      have hp_hc : p ∈ High_col := (mem_inter.mp hp).2
      have hpj : p.1.2 = j := by
        have hpC := (mem_inter.mp hp).1
        rw [hC_col_def] at hpC
        exact (mem_filter.mp hpC).2
      refine ⟨neighbors (gridGraph G) (C_col j) p, neighbors_subset, fun _ => ⟨?_, ?_⟩⟩
      · refine triangleFree_neighbors_indep ?_ (mem_inter.mp hp).1
        exact triangleFree_subset hG_TF (by rw [hC_col_def]; exact (filter_subset _ _).trans hU_trim_sub)
      · rw [← hpj]
        exact hHigh_col_deg p hp_hc
    · exact ⟨∅, empty_subset _, fun hj' => absurd hj' hj⟩
  choose I_col hI_col_sub hI_col_prop using hexists_I_col
  have hI_col_sub' : ∀ j ∈ J_good, I_col j ⊆ C_col j := fun j _ => hI_col_sub j
  have hI_col_ind' : ∀ j ∈ J_good, (gridGraph G).IsIndepSet (I_col j : Set ((ι × κ) × V)) :=
    fun j hj => (hI_col_prop j hj).1
  have hI_col_ge' : ∀ j ∈ J_good, N_grid / (8 * (α' : ℝ)) ≤ ((I_col j).card : ℝ) :=
    fun j hj => (hI_col_prop j hj).2
  let U : Finset ((ι × κ) × V) := J_good.biUnion I_col
  have hU_disj : Set.PairwiseDisjoint (J_good : Set κ) I_col := by
    intro j₁ hj₁ j₂ hj₂ hne
    change Disjoint _ _
    rw [disjoint_left]
    intro p hp1 hp2
    have h1 := hI_col_sub' j₁ hj₁ hp1
    have h2 := hI_col_sub' j₂ hj₂ hp2
    rw [hC_col_def] at h1 h2
    exact hne ((mem_filter.mp h1).2.symm.trans (mem_filter.mp h2).2)
  have hU_card : (M₀ : ℝ) * N_grid / (32 * (X : ℝ) * (α' : ℝ)) ≤ (U.card : ℝ) := by
    have h1 : (U.card : ℝ) = ∑ j ∈ J_good, ((I_col j).card : ℝ) := by
      exact_mod_cast card_biUnion hU_disj
    rw [h1]
    calc
      (M₀ : ℝ) * N_grid / (32 * (X : ℝ) * (α' : ℝ))
        = (N_grid / (4 * (s₁ : ℝ) * (X : ℝ))) * (N_grid / (8 * (α' : ℝ))) := by
          rw [hN_grid_eq]
          have hs10 : (s₁ : ℝ) ≠ 0 := by exact_mod_cast (by omega : s₁ ≠ 0)
          have hX0 : (X : ℝ) ≠ 0 := by exact_mod_cast (by omega : X ≠ 0)
          have hα0 : (α' : ℝ) ≠ 0 := by positivity
          field_simp; ring
      _ ≤ (J_good.card : ℝ) * (N_grid / (8 * (α' : ℝ))) :=
          mul_le_mul_of_nonneg_right hJ_good_ge (div_nonneg hN_nn (by positivity))
      _ = ∑ _j ∈ J_good, (N_grid / (8 * (α' : ℝ))) := by rw [sum_const, nsmul_eq_mul]
      _ ≤ ∑ j ∈ J_good, ((I_col j).card : ℝ) := sum_le_sum hI_col_ge'
  have hK_row : ∀ i : ι, ∃ K_i ⊆ U ∩ R_row i,
      i ∈ I_cur → (gridGraph G).IsIndepSet (K_i : Set ((ι × κ) × V)) ∧ (U ∩ R_row i).card ≤ 2 * K_i.card ^ 2 := by
    intro i
    by_cases hi : i ∈ I_cur
    · obtain ⟨K_i, h1, h2, h3⟩ := card_triangle_free_subset (gridGraph G) (U ∩ R_row i)
        (triangleFree_subset hG_TF (inter_subset_right.trans (fun p hp =>
          hU_trim_sub (hU_trim_eq ▸ mem_biUnion.mpr ⟨i, hi, hp⟩))))
      exact ⟨K_i, h1, fun _ => ⟨h2, h3⟩⟩
    · exact ⟨∅, empty_subset _, fun hi' => absurd hi' hi⟩
  choose K_row hK_sub hK_prop using hK_row
  have hK_sub' : ∀ i ∈ I_cur, K_row i ⊆ U ∩ R_row i := fun i _ => hK_sub i
  have hK_ind' : ∀ i ∈ I_cur, (gridGraph G).IsIndepSet (K_row i : Set ((ι × κ) × V)) :=
    fun i hi => (hK_prop i hi).1
  have hK_sq' : ∀ i ∈ I_cur, (U ∩ R_row i).card ≤ 2 * (K_row i).card ^ 2 :=
    fun i hi => (hK_prop i hi).2
  let K_all := I_cur.biUnion K_row
  have hK_all_ind : (gridGraph G).IsIndepSet (K_all : Set ((ι × κ) × V)) := by
    rw [(gridGraph G).isIndepSet_iff]
    intro p hp q hq hpq hadj
    simp only [K_all, mem_coe, mem_biUnion] at hp hq
    obtain ⟨i₁, hi₁, hpK⟩ := hp
    obtain ⟨i₂, hi₂, hqK⟩ := hq
    by_cases hi : i₁ = i₂
    · subst hi
      exact ((gridGraph G).isIndepSet_iff.mp (hK_ind' i₁ hi₁)) hpK hqK hpq hadj
    · have hpR := hK_sub' i₁ hi₁ hpK
      have hqR := hK_sub' i₂ hi₂ hqK
      obtain ⟨j₁, _, hpcell⟩ := mem_biUnion.mp (hR_sub' i₁ hi₁ (mem_inter.mp hpR).2)
      obtain ⟨j₂, _, hqcell⟩ := mem_biUnion.mp (hR_sub' i₂ hi₂ (mem_inter.mp hqR).2)
      have hp12 := hcell_fst i₁ j₁ p hpcell
      have hq12 := hcell_fst i₂ j₂ q hqcell
      have hj_eq : j₁ = j₂ := by
        by_contra hnj
        exact hG_cross p (hU_trim_sub (hU_trim_eq ▸ mem_biUnion.mpr ⟨i₁, hi₁, (mem_inter.mp hpR).2⟩))
          q (hU_trim_sub (hU_trim_eq ▸ mem_biUnion.mpr ⟨i₂, hi₂, (mem_inter.mp hqR).2⟩))
          (by rw [hp12.1, hq12.1]; exact hi) (by rw [hp12.2, hq12.2]; exact hnj) hadj
      obtain ⟨jc₁, hjc₁, hpIc⟩ := mem_biUnion.mp (mem_inter.mp hpR).1
      obtain ⟨jc₂, hjc₂, hqIc⟩ := mem_biUnion.mp (mem_inter.mp hqR).1
      have hjc1 : jc₁ = j₁ := by
        have hc := hI_col_sub' jc₁ hjc₁ hpIc
        rw [hC_col_def] at hc
        exact (mem_filter.mp hc).2.symm.trans hp12.2
      have hjc2 : jc₂ = j₂ := by
        have hc := hI_col_sub' jc₂ hjc₂ hqIc
        rw [hC_col_def] at hc
        exact (mem_filter.mp hc).2.symm.trans hq12.2
      have heq_jc : jc₁ = jc₂ := hjc1.trans (hj_eq.trans hjc2.symm)
      subst heq_jc
      exact ((gridGraph G).isIndepSet_iff.mp (hI_col_ind' jc₁ hjc₁)) hpIc hqIc hpq hadj
  have hK_disj : Set.PairwiseDisjoint (I_cur : Set ι) K_row := by
    intro i₁ hi₁ i₂ hi₂ hne
    change Disjoint _ _
    rw [disjoint_left]
    intro p hp1 hp2
    exact (disjoint_left.mp (hR_disj hi₁ hi₂ hne))
      (mem_inter.mp (hK_sub' i₁ hi₁ hp1)).2 (mem_inter.mp (hK_sub' i₂ hi₂ hp2)).2
  have hK_sum_le : ∑ i ∈ I_cur, ((K_row i).card : ℝ) ≤ (α' : ℝ) := by
    have h1 : K_all.card = ∑ i ∈ I_cur, (K_row i).card := card_biUnion hK_disj
    have hK_all_U : K_all ⊆ U_grid := by
      intro p hp
      obtain ⟨i, hi, hpK⟩ := mem_biUnion.mp hp
      exact hU_trim_sub (hU_trim_eq ▸ mem_biUnion.mpr ⟨i, hi, (mem_inter.mp (hK_sub' i hi hpK)).2⟩)
    exact_mod_cast h1 ▸ hG_ind K_all hK_all_U hK_all_ind
  have hU_part : U.card = ∑ i ∈ I_cur, (U ∩ R_row i).card := by
    have hdisj_r : Set.PairwiseDisjoint (I_cur : Set ι) (fun i => U ∩ R_row i) := by
      intro i₁ hi₁ i₂ hi₂ hne
      change Disjoint _ _
      rw [disjoint_left]
      intro p hp1 hp2
      exact (disjoint_left.mp (hR_disj hi₁ hi₂ hne)) (mem_inter.mp hp1).2 (mem_inter.mp hp2).2
    have heq : U = I_cur.biUnion (fun i => U ∩ R_row i) := by
      ext p
      dsimp [U]
      rw [mem_biUnion, mem_biUnion]
      constructor
      · rintro ⟨j, hj, hpIc⟩
        have hpC := hI_col_sub' j hj hpIc
        rw [hC_col_def] at hpC
        have hpUtrim : p ∈ U_trim := filter_subset _ _ hpC
        rw [hU_trim_eq] at hpUtrim
        obtain ⟨i, hi, hpR⟩ := mem_biUnion.mp hpUtrim
        exact ⟨i, hi, mem_inter.mpr ⟨mem_biUnion.mpr ⟨j, hj, hpIc⟩, hpR⟩⟩
      · rintro ⟨_, _, hp⟩
        exact mem_biUnion.mp (mem_inter.mp hp).1
    conv_lhs => rw [heq]
    exact card_biUnion hdisj_r
  have hU_le_sqrt : (U.card : ℝ) ≤ Real.sqrt (2 * (M₀ : ℝ)) * (α' : ℝ) := by
    have hUr : (U.card : ℝ) = ∑ i ∈ I_cur, ((U ∩ R_row i).card : ℝ) := by exact_mod_cast hU_part
    rw [hUr]
    have hterm : ∀ i ∈ I_cur, ((U ∩ R_row i).card : ℝ) ≤
        Real.sqrt (2 * (M₀ : ℝ)) * ((K_row i).card : ℝ) := by
      intro i hi
      have ha1 : ((U ∩ R_row i).card : ℝ) ≤ (M₀ : ℝ) := by
        rw [← hR_card' i hi]
        exact_mod_cast card_le_card inter_subset_right
      have ha2 : ((U ∩ R_row i).card : ℝ) ≤ 2 * ((K_row i).card : ℝ) ^ 2 := by
        exact_mod_cast hK_sq' i hi
      have hsq : ((U ∩ R_row i).card : ℝ) ^ 2 ≤
          (Real.sqrt (2 * (M₀ : ℝ)) * ((K_row i).card : ℝ)) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (by positivity)]
        calc
          ((U ∩ R_row i).card : ℝ) ^ 2
            = ((U ∩ R_row i).card : ℝ) * ((U ∩ R_row i).card : ℝ) := by ring
          _ ≤ (M₀ : ℝ) * (2 * ((K_row i).card : ℝ) ^ 2) :=
              mul_le_mul ha1 ha2 (by positivity) (by positivity)
          _ = 2 * (M₀ : ℝ) * ((K_row i).card : ℝ) ^ 2 := by ring
      exact le_of_pow_le_pow_left₀ (by decide) (by positivity) hsq
    calc
      ∑ i ∈ I_cur, ((U ∩ R_row i).card : ℝ)
        ≤ ∑ i ∈ I_cur, Real.sqrt (2 * (M₀ : ℝ)) * ((K_row i).card : ℝ) := sum_le_sum hterm
      _ = Real.sqrt (2 * (M₀ : ℝ)) * ∑ i ∈ I_cur, ((K_row i).card : ℝ) := by rw [mul_sum]
      _ ≤ Real.sqrt (2 * (M₀ : ℝ)) * (α' : ℝ) := by gcongr
  have hU_sq : (U.card : ℝ) ^ 2 ≤ 2 * (M₀ : ℝ) * (α' : ℝ) ^ 2 := by
    have hsq := pow_le_pow_left₀ (by positivity) hU_le_sqrt 2
    rw [mul_pow, Real.sq_sqrt (by positivity)] at hsq
    exact hsq
  have hM₀_rpos : (0 : ℝ) < (M₀ : ℝ) := by exact_mod_cast hM₀_pos
  have hmain_r : (s₁ : ℝ) ^ 2 * (M₀ : ℝ) ^ 3 ≤ 2 * 32 ^ 2 * (X : ℝ) ^ 2 * (α' : ℝ) ^ 4 := by
    have h1 : ((s₁ : ℝ) * (M₀ : ℝ) ^ 2 / (32 * (X : ℝ) * (α' : ℝ))) ^ 2 ≤
        2 * (M₀ : ℝ) * (α' : ℝ) ^ 2 := by
      have h1' : (s₁ : ℝ) * (M₀ : ℝ) ^ 2 / (32 * (X : ℝ) * (α' : ℝ)) ≤ (U.card : ℝ) := by
        rw [hN_grid_eq] at hU_card
        linarith [hU_card, show (M₀ : ℝ) * ((s₁ : ℝ) * (M₀ : ℝ)) / (32 * (X : ℝ) * (α' : ℝ)) =
          (s₁ : ℝ) * (M₀ : ℝ) ^ 2 / (32 * (X : ℝ) * (α' : ℝ)) by ring]
      exact (pow_le_pow_left₀ (by positivity) h1' 2).trans hU_sq
    have hX_rpos : (0 : ℝ) < (X : ℝ) := by exact_mod_cast hX_pos
    have h2 : (s₁ : ℝ) ^ 2 * (M₀ : ℝ) ^ 4 ≤ 2 * 32 ^ 2 * (M₀ : ℝ) * (X : ℝ) ^ 2 * (α' : ℝ) ^ 4 := by
      have heq1 : ((s₁ : ℝ) * (M₀ : ℝ) ^ 2 / (32 * (X : ℝ) * (α' : ℝ))) ^ 2 =
          ((s₁ : ℝ) ^ 2 * (M₀ : ℝ) ^ 4) / (32 ^ 2 * (X : ℝ) ^ 2 * (α' : ℝ) ^ 2) := by ring
      rw [heq1, div_le_iff₀ (by positivity)] at h1
      linarith [show (2 * (M₀ : ℝ) * (α' : ℝ) ^ 2) * (32 ^ 2 * (X : ℝ) ^ 2 * (α' : ℝ) ^ 2) =
        2 * 32 ^ 2 * (M₀ : ℝ) * (X : ℝ) ^ 2 * (α' : ℝ) ^ 4 by ring]
    exact le_of_mul_le_mul_left (by linarith [h2]) hM₀_rpos
  have hs1_ge : (s₀ : ℝ) / 2 ≤ (s₁ : ℝ) := by
    have : (s₀ : ℝ) ≤ 2 * (s₁ : ℝ) := by exact_mod_cast hs1_2.le
    linarith
  have hTXpos : (0 : ℝ) ≤ T * (X : ℝ) / 3 := by linarith
  have hfinal_r : ((s₀ : ℝ) / 2) ^ 2 * (T * (X : ℝ) / 3) ^ 3 ≤
      2 * 32 ^ 2 * (X : ℝ) ^ 2 * (α' : ℝ) ^ 4 := by
    calc
      ((s₀ : ℝ) / 2) ^ 2 * (T * (X : ℝ) / 3) ^ 3
        ≤ (s₁ : ℝ) ^ 2 * (M₀ : ℝ) ^ 3 :=
          mul_le_mul (pow_le_pow_left₀ (by positivity) hs1_ge 2)
            (pow_le_pow_left₀ hTXpos hM₀_ge 3) (by positivity) (by positivity)
      _ ≤ 2 * 32 ^ 2 * (X : ℝ) ^ 2 * (α' : ℝ) ^ 4 := hmain_r
  rw [hα'eq] at hfinal_r
  have heqL : (s₀ : ℝ) ^ 2 * T ^ 3 * (X : ℝ) * (X : ℝ) ^ 2 =
      108 * (((s₀ : ℝ) / 2) ^ 2 * (T * (X : ℝ) / 3) ^ 3) := by ring
  have heqR : 108 * (2 * 32 ^ 2 * (X : ℝ) ^ 2 * (4 * (α_orig : ℝ)) ^ 4) =
      56623104 * (α_orig : ℝ) ^ 4 * (X : ℝ) ^ 2 := by ring
  have hcancel : (s₀ : ℝ) ^ 2 * T ^ 3 * (X : ℝ) * (X : ℝ) ^ 2 ≤
      56623104 * (α_orig : ℝ) ^ 4 * (X : ℝ) ^ 2 := by
    linarith only [hfinal_r, heqL, heqR]
  have hX_rpos : (0 : ℝ) < (X : ℝ) := by exact_mod_cast hX_pos
  have hX2_pos : (0 : ℝ) < (X : ℝ) ^ 2 := by positivity
  dsimp [s₀] at hcancel
  exact le_of_mul_le_mul_right hcancel hX2_pos

private lemma grid_lemma {ι κ V : Type*} [DecidableEq ι] [DecidableEq κ] [DecidableEq V]
    [Fintype ι] [Fintype κ] [Fintype V]
    (G : SimpleGraph V) (α_orig : ℕ) (hα : 1 ≤ α_orig)
    (hInd : ∀ I : Finset V, G.IsIndepSet (I : Set V) → I.card ≤ α_orig)
    (I_rows : Finset ι) (J_cols : Finset κ) (A : ι → κ → Finset V)
    (L_verts : Finset V) (hL_TF : TriangleFree G L_verts)
    (hA_sub : ∀ i ∈ I_rows, ∀ j ∈ J_cols, A i j ⊆ L_verts)
    (hA_mult : ∀ z ∈ L_verts, ((I_rows ×ˢ J_cols).filter (fun p => z ∈ A p.1 p.2)).card ≤ 4)
    (X : ℕ) (hX_pos : 1 ≤ X) (hA_card : ∀ i ∈ I_rows, ∀ j ∈ J_cols, (A i j).card ≤ X)
    (T : ℝ) (hT_ge : (I_rows.card : ℝ) ≤ T) (hs₀_pos : 1 ≤ I_rows.card)
    (hA_row_disj : ∀ i ∈ I_rows, ∀ j₁ ∈ J_cols, ∀ j₂ ∈ J_cols, j₁ ≠ j₂ → Disjoint (A i j₁) (A i j₂))
    (hA_row_lb : ∀ i ∈ I_rows, T * (X : ℝ) ≤ ((J_cols.biUnion (A i)).card : ℝ))
    (hTX6 : 6 ≤ T * (X : ℝ))
    (hA_cross : ∀ i₁ ∈ I_rows, ∀ i₂ ∈ I_rows, ∀ j₁ ∈ J_cols, ∀ j₂ ∈ J_cols,
      i₁ ≠ i₂ → j₁ ≠ j₂ → ∀ z₁ ∈ A i₁ j₁, ∀ z₂ ∈ A i₂ j₂, ¬ G.Adj z₁ z₂) :
    ((I_rows.card : ℝ) * T * (X : ℝ) ≤ 96 * (α_orig : ℝ)) ∨
    ((I_rows.card : ℝ) ^ 2 * T ^ 3 * (X : ℝ) ≤ 56623104 * (α_orig : ℝ) ^ 4) ∨
    ((I_rows.card : ℝ) ^ 2 * T * (X : ℝ) ≤ 3072 * (α_orig : ℝ) ^ 2) ∨
    ((I_rows.card : ℝ) ^ 3 * T ^ 3 * (X : ℝ) ^ 2 ≤ 9663676416 * (α_orig : ℝ) ^ 5) := by
  classical
  let s₀ : ℕ := I_rows.card
  let α' : ℕ := 4 * α_orig
  have hα'pos : 1 ≤ α' := by omega
  have hα'eq : (α' : ℝ) = 4 * (α_orig : ℝ) := by exact_mod_cast rfl
  have hT_pos : 0 < T := lt_of_lt_of_le (by exact_mod_cast hs₀_pos) hT_ge
  let U_grid : Finset ((ι × κ) × V) :=
    ((I_rows ×ˢ J_cols) ×ˢ L_verts).filter (fun q => q.2 ∈ A q.1.1 q.1.2)
  have hG_ind : ∀ S ⊆ U_grid, (gridGraph G).IsIndepSet (S : Set ((ι × κ) × V)) → S.card ≤ α' := by
    intro S hSU hS
    let S_V := S.image Prod.snd
    have hSV_ind : G.IsIndepSet (S_V : Set V) := by
      rw [G.isIndepSet_iff]
      intro z₁ hz₁ z₂ hz₂ hne
      obtain ⟨p₁, hp₁, rfl⟩ := mem_image.mp hz₁
      obtain ⟨p₂, hp₂, rfl⟩ := mem_image.mp hz₂
      have hpne : p₁ ≠ p₂ := fun h => hne (congrArg Prod.snd h)
      intro hadj
      exact ((gridGraph G).isIndepSet_iff.mp hS) hp₁ hp₂ hpne ⟨hpne, hadj⟩
    have hSV_le : S_V.card ≤ α_orig := hInd S_V hSV_ind
    have hfib : ∀ z ∈ S_V, (S.filter (fun p => p.2 = z)).card ≤ 4 := by
      intro z hz
      obtain ⟨p₀, hp₀, rfl⟩ := mem_image.mp hz
      have hzL : p₀.2 ∈ L_verts := (mem_product.mp (mem_filter.mp (hSU hp₀)).1).2
      have hinj : (S.filter (fun p => p.2 = p₀.2)).card ≤
          ((I_rows ×ˢ J_cols).filter (fun r => p₀.2 ∈ A r.1 r.2)).card := by
        refine card_le_card_of_injOn Prod.fst ?_ ?_
        · intro p hp
          obtain ⟨hpS, hpz⟩ := mem_filter.mp hp
          have hpU := mem_filter.mp (hSU hpS)
          exact mem_filter.mpr ⟨(mem_product.mp hpU.1).1, hpz ▸ hpU.2⟩
        · intro p₁ hp₁ p₂ hp₂ heq
          exact Prod.ext heq ((mem_filter.mp hp₁).2.trans (mem_filter.mp hp₂).2.symm)
      exact hinj.trans (hA_mult p₀.2 hzL)
    have hS_sub : S ⊆ S_V.biUnion (fun z => S.filter (fun p => p.2 = z)) := by
      intro p hp
      exact mem_biUnion.mpr ⟨p.2, mem_image.mpr ⟨p, hp, rfl⟩, mem_filter.mpr ⟨hp, rfl⟩⟩
    calc
      S.card ≤ ∑ z ∈ S_V, (S.filter (fun p => p.2 = z)).card :=
        (card_le_card hS_sub).trans card_biUnion_le
      _ ≤ ∑ _z ∈ S_V, 4 := sum_le_sum hfib
      _ = S_V.card * 4 := by simp
      _ ≤ 4 * α_orig := by omega
  have hG_TF : TriangleFree (gridGraph G) U_grid := by
    intro p₁ hp₁ p₂ hp₂ p₃ hp₃ h12 h23 h13
    have hz1 : p₁.2 ∈ L_verts := (mem_product.mp (mem_filter.mp hp₁).1).2
    have hz2 : p₂.2 ∈ L_verts := (mem_product.mp (mem_filter.mp hp₂).1).2
    have hz3 : p₃.2 ∈ L_verts := (mem_product.mp (mem_filter.mp hp₃).1).2
    exact hL_TF p₁.2 hz1 p₂.2 hz2 p₃.2 hz3 h12.2 h23.2 h13.2
  have hG_cross : ∀ p ∈ U_grid, ∀ q ∈ U_grid,
      p.1.1 ≠ q.1.1 → p.1.2 ≠ q.1.2 → ¬ (gridGraph G).Adj p q := by
    intro p hp q hq hi hj hadj
    have hp' := mem_filter.mp hp
    have hq' := mem_filter.mp hq
    have hpIJ := mem_product.mp (mem_product.mp hp'.1).1
    have hqIJ := mem_product.mp (mem_product.mp hq'.1).1
    exact hA_cross p.1.1 hpIJ.1 q.1.1 hqIJ.1 p.1.2 hpIJ.2 q.1.2 hqIJ.2 hi hj p.2 hp'.2 q.2 hq'.2 hadj.2
  let cell (i : ι) (j : κ) : Finset ((ι × κ) × V) :=
    U_grid.filter (fun p => p.1.1 = i ∧ p.1.2 = j)
  have hcell_U : ∀ i j, cell i j ⊆ U_grid := fun i j => filter_subset _ _
  have hcell_fst : ∀ i j p, p ∈ cell i j → p.1.1 = i ∧ p.1.2 = j :=
    fun i j p hp => (mem_filter.mp hp).2
  have hcell_card : ∀ i ∈ I_rows, ∀ j ∈ J_cols, (cell i j).card = (A i j).card := by
    intro i hi j hj
    refine card_bij (fun p _ => p.2) ?_ ?_ ?_
    · intro p hp
      exact (mem_filter.mp (mem_filter.mp hp).1).2 |> fun h =>
        (mem_filter.mp hp).2.1 ▸ (mem_filter.mp hp).2.2 ▸ h
    · intro p₁ hp₁ p₂ hp₂ heq
      have h1 := (mem_filter.mp hp₁).2
      have h2 := (mem_filter.mp hp₂).2
      exact Prod.ext (Prod.ext (h1.1.trans h2.1.symm) (h1.2.trans h2.2.symm)) heq
    · intro z hz
      have hzL : z ∈ L_verts := hA_sub i hi j hj hz
      refine ⟨((i, j), z), mem_filter.mpr ⟨mem_filter.mpr
        ⟨mem_product.mpr ⟨mem_product.mpr ⟨hi, hj⟩, hzL⟩, hz⟩, rfl, rfl⟩, rfl⟩
  obtain ⟨I_cur, hI_cur, J_cur, hJ_cur, hs1_2, hDel, hNoBad⟩ :=
    grid_clean G α' hα'pos I_rows J_cols U_grid cell hcell_U hcell_fst hG_ind hG_cross T hT_pos hs₀_pos
  let s₁ := I_cur.card
  have hs₁_pos : 1 ≤ s₁ := by omega
  have hRow_lb : ∀ i ∈ I_cur, (T / 2) * (X : ℝ) ≤ ((J_cur.biUnion (cell i)).card : ℝ) := by
    intro i hi
    have hdisj_c : Set.PairwiseDisjoint (J_cols : Set κ) (cell i) := by
      intro j₁ _ j₂ _ hne
      change Disjoint _ _
      rw [disjoint_left]
      intro p hp1 hp2
      exact hne ((hcell_fst i j₁ p hp1).2.symm.trans (hcell_fst i j₂ p hp2).2)
    have hJsplit : J_cols.biUnion (cell i) ⊆ J_cur.biUnion (cell i) ∪ (J_cols \ J_cur).biUnion (cell i) := by
      intro p hp
      obtain ⟨j, hj, hpcell⟩ := mem_biUnion.mp hp
      by_cases hjc : j ∈ J_cur
      · exact mem_union_left _ (mem_biUnion.mpr ⟨j, hjc, hpcell⟩)
      · exact mem_union_right _ (mem_biUnion.mpr ⟨j, mem_sdiff.mpr ⟨hj, hjc⟩, hpcell⟩)
    have hfull_eq : (J_cols.biUnion (cell i)).card = (J_cols.biUnion (A i)).card := by
      rw [card_biUnion hdisj_c, card_biUnion (hA_row_disj i (hI_cur hi))]
      exact sum_congr rfl fun j hj => hcell_card i (hI_cur hi) j hj
    have hdel_le : (((J_cols \ J_cur).biUnion (cell i)).card : ℝ) ≤ (T / 2) * (X : ℝ) := by
      have hc1 : ((J_cols \ J_cur).biUnion (cell i)).card ≤
          ∑ j ∈ J_cols \ J_cur, (cell i j).card := card_biUnion_le
      have hc2 : ∑ j ∈ J_cols \ J_cur, (cell i j).card ≤ (J_cols \ J_cur).card * X := by
        calc
          ∑ j ∈ J_cols \ J_cur, (cell i j).card ≤ ∑ _j ∈ J_cols \ J_cur, X := by
            refine sum_le_sum fun j hj => ?_
            rw [hcell_card i (hI_cur hi) j (mem_sdiff.mp hj).1]
            exact hA_card i (hI_cur hi) j (mem_sdiff.mp hj).1
          _ = (J_cols \ J_cur).card * X := by simp
      have hc2r : (((J_cols \ J_cur).biUnion (cell i)).card : ℝ) ≤
          ((J_cols \ J_cur).card : ℝ) * (X : ℝ) := by
        exact_mod_cast hc1.trans hc2
      have hdel_half : ((J_cols \ J_cur).card : ℝ) ≤ T / 2 := by
        have hdiff_le : ((s₀ - s₁ : ℕ) : ℝ) ≤ (s₀ : ℝ) / 2 := by
          have hnat : 2 * (s₀ - s₁) ≤ s₀ := by omega
          have hr : (2 : ℝ) * ((s₀ - s₁ : ℕ) : ℝ) ≤ (s₀ : ℝ) := by exact_mod_cast hnat
          linarith only [hr]
        have h1 : ((s₀ - s₁ : ℕ) : ℝ) * (T / (s₀ : ℝ)) ≤ ((s₀ : ℝ) / 2) * (T / (s₀ : ℝ)) := by
          gcongr
        have hs₀r0 : (s₀ : ℝ) ≠ 0 := by exact_mod_cast (by omega : s₀ ≠ 0)
        have h2 : ((s₀ : ℝ) / 2) * (T / (s₀ : ℝ)) = T / 2 := by field_simp
        linarith
      nlinarith [hc2r, hdel_half, (by positivity : (0 : ℝ) ≤ (X : ℝ))]
    have hc_union : (J_cols.biUnion (cell i)).card ≤
        (J_cur.biUnion (cell i)).card + ((J_cols \ J_cur).biUnion (cell i)).card :=
      (card_le_card hJsplit).trans (card_union_le _ _)
    have hc_unionR : ((J_cols.biUnion (cell i)).card : ℝ) ≤
        ((J_cur.biUnion (cell i)).card : ℝ) + (((J_cols \ J_cur).biUnion (cell i)).card : ℝ) := by
      exact_mod_cast hc_union
    have horig := hA_row_lb i (hI_cur hi)
    rw [← hfull_eq] at horig
    linarith
  let M₀ : ℕ := Nat.floor (T * (X : ℝ) / 2)
  have hM₀_ge : T * (X : ℝ) / 3 ≤ (M₀ : ℝ) := by
    have hfl : T * (X : ℝ) / 2 - 1 < (M₀ : ℝ) := Nat.sub_one_lt_floor _
    linarith
  have hM₀_le : (M₀ : ℝ) ≤ T * (X : ℝ) / 2 := Nat.floor_le (by positivity)
  have hM₀_pos : 1 ≤ M₀ := by
    have : (1 : ℝ) ≤ (M₀ : ℝ) := by linarith
    exact_mod_cast this
  have hM₀_le_row : ∀ i ∈ I_cur, M₀ ≤ (J_cur.biUnion (cell i)).card := by
    intro i hi
    have h1 := hRow_lb i hi
    have h2 : (M₀ : ℝ) ≤ ((J_cur.biUnion (cell i)).card : ℝ) := by linarith
    exact_mod_cast h2
  have hR_all : ∀ i : ι, ∃ R ⊆ J_cur.biUnion (cell i), i ∈ I_cur → R.card = M₀ := by
    intro i
    by_cases hi : i ∈ I_cur
    · obtain ⟨R, h1, h2⟩ := exists_subset_card_eq (hM₀_le_row i hi)
      exact ⟨R, h1, fun _ => h2⟩
    · exact ⟨∅, empty_subset _, fun hi' => absurd hi' hi⟩
  choose R_row hR_sub hR_card using hR_all
  have hR_sub' : ∀ i ∈ I_cur, R_row i ⊆ J_cur.biUnion (cell i) := fun i _ => hR_sub i
  have hR_card' : ∀ i ∈ I_cur, (R_row i).card = M₀ := fun i hi => hR_card i hi
  let U_trim : Finset ((ι × κ) × V) := I_cur.biUnion R_row
  have hU_trim_sub : U_trim ⊆ U_grid := by
    intro p hp
    obtain ⟨i, hi, hpR⟩ := mem_biUnion.mp hp
    obtain ⟨j, _, hpcell⟩ := mem_biUnion.mp (hR_sub' i hi hpR)
    exact hcell_U i j hpcell
  have hR_disj : Set.PairwiseDisjoint (I_cur : Set ι) R_row := by
    intro i₁ hi₁ i₂ hi₂ hne
    change Disjoint _ _
    rw [disjoint_left]
    intro p hp1 hp2
    obtain ⟨j₁, _, hp_1⟩ := mem_biUnion.mp (hR_sub' i₁ hi₁ hp1)
    obtain ⟨j₂, _, hp_2⟩ := mem_biUnion.mp (hR_sub' i₂ hi₂ hp2)
    exact hne ((hcell_fst i₁ j₁ p hp_1).1.symm.trans (hcell_fst i₂ j₂ p hp_2).1)
  have hN_grid : U_trim.card = s₁ * M₀ := by
    rw [card_biUnion hR_disj]
    calc
      ∑ i ∈ I_cur, (R_row i).card = ∑ _i ∈ I_cur, M₀ := sum_congr rfl hR_card'
      _ = s₁ * M₀ := by rw [sum_const, smul_eq_mul]
  let N_grid : ℝ := (U_trim.card : ℝ)
  have hN_grid_eq : N_grid = (s₁ : ℝ) * (M₀ : ℝ) := by
    dsimp [N_grid]
    exact_mod_cast hN_grid
  have hN_grid_ge : (s₀ : ℝ) * T * (X : ℝ) / 6 ≤ N_grid := by
    have hs1_ge : (s₀ : ℝ) / 2 ≤ (s₁ : ℝ) := by
      have : (s₀ : ℝ) ≤ 2 * (s₁ : ℝ) := by exact_mod_cast hs1_2.le
      linarith
    rw [hN_grid_eq]
    calc
      (s₀ : ℝ) * T * (X : ℝ) / 6 = ((s₀ : ℝ) / 2) * (T * (X : ℝ) / 3) := by ring
      _ ≤ (s₁ : ℝ) * (M₀ : ℝ) :=
          mul_le_mul hs1_ge hM₀_ge (div_nonneg (mul_nonneg hT_pos.le (Nat.cast_nonneg _)) (by norm_num))
            (Nat.cast_nonneg _)
  by_cases hsmallN : N_grid < 4 * (α' : ℝ)
  · left
    have h1 : (s₀ : ℝ) * T * (X : ℝ) / 6 < 4 * (α' : ℝ) := lt_of_le_of_lt hN_grid_ge hsmallN
    rw [hα'eq] at h1
    dsimp [s₀] at h1
    linarith
  have hN_4a : 4 * (α' : ℝ) ≤ N_grid := le_of_not_gt hsmallN
  let C_col (j : κ) : Finset ((ι × κ) × V) := U_trim.filter (fun p => p.1.2 = j)
  have hC_col_le : ∀ j : κ, (C_col j).card ≤ s₁ * X := by
    intro j
    have hsub : C_col j ⊆ I_cur.biUnion (fun i => cell i j) := by
      intro p hp
      obtain ⟨hpU, hpj⟩ := mem_filter.mp hp
      obtain ⟨i, hi, hpR⟩ := mem_biUnion.mp hpU
      obtain ⟨j', _, hpcell⟩ := mem_biUnion.mp (hR_sub' i hi hpR)
      have hj' : j' = j := (hcell_fst i j' p hpcell).2.symm.trans hpj
      exact mem_biUnion.mpr ⟨i, hi, hj' ▸ hpcell⟩
    have h1 : (C_col j).card ≤ ∑ i ∈ I_cur, (cell i j).card :=
      (card_le_card hsub).trans card_biUnion_le
    by_cases hj : j ∈ J_cols
    · calc
        (C_col j).card ≤ ∑ i ∈ I_cur, (cell i j).card := h1
        _ ≤ ∑ _i ∈ I_cur, X := sum_le_sum fun i hi => by
            rw [hcell_card i (hI_cur hi) j hj]
            exact hA_card i (hI_cur hi) j hj
        _ = s₁ * X := by simp [s₁]
    · have hEmpty : C_col j = ∅ := by
        rw [eq_empty_iff_forall_notMem]
        intro p hp
        obtain ⟨hpU, hpj⟩ := mem_filter.mp hp
        obtain ⟨i, hi, hpR⟩ := mem_biUnion.mp hpU
        obtain ⟨j', hj', hpcell⟩ := mem_biUnion.mp (hR_sub' i hi hpR)
        have hj'eq : j' = j := (hcell_fst i j' p hpcell).2.symm.trans hpj
        exact hj (hj'eq ▸ hJ_cur hj')
      simp [hEmpty]
  let Low := U_trim.filter (fun p => ((neighbors (gridGraph G) U_trim p).card : ℝ) < N_grid / (4 * (α' : ℝ)))
  let High := U_trim \ Low
  have hLow_le : (Low.card : ℝ) ≤ N_grid / 2 := by
    have hcb : (Low.card : ℝ) ≤ (α' : ℝ) * (N_grid / (4 * (α' : ℝ)) + 1) := by
      refine cover_bound (gridGraph G) Low (α' : ℝ) (N_grid / (4 * (α' : ℝ)))
        (fun I hIL hI => by exact_mod_cast hG_ind I (hIL.trans (filter_subset _ _ |>.trans hU_trim_sub)) hI)
        (div_nonneg (by dsimp [N_grid]; exact Nat.cast_nonneg _) (mul_nonneg (by norm_num) (Nat.cast_nonneg _)))
        (fun p hp => ?_)
      have h1 : (neighbors (gridGraph G) Low p).card ≤ (neighbors (gridGraph G) U_trim p).card :=
        card_le_card (neighbors_mono (filter_subset _ _) p)
      have h1r : ((neighbors (gridGraph G) Low p).card : ℝ) ≤ ((neighbors (gridGraph G) U_trim p).card : ℝ) := by
        exact_mod_cast h1
      exact h1r.trans (mem_filter.mp hp).2.le
    have hα'0 : (α' : ℝ) ≠ 0 := by positivity
    have hsimp : (α' : ℝ) * (N_grid / (4 * (α' : ℝ)) + 1) = N_grid / 4 + (α' : ℝ) := by field_simp
    linarith
  have hHigh_ge : N_grid / 2 ≤ (High.card : ℝ) := by
    have hsplit : N_grid = (High.card : ℝ) + (Low.card : ℝ) := by
      dsimp [N_grid]
      exact_mod_cast (card_sdiff_add_card_inter U_trim Low).symm.trans (by
        rw [inter_eq_right.mpr (filter_subset _ _)])
    linarith
  let High_row := High.filter (fun p => N_grid / (8 * (α' : ℝ)) ≤ ((neighbors (gridGraph G) (R_row p.1.1) p).card : ℝ))
  let High_col := High.filter (fun p => N_grid / (8 * (α' : ℝ)) ≤ ((neighbors (gridGraph G) (C_col p.1.2) p).card : ℝ))
  have hHigh_cover : High ⊆ High_row ∪ High_col := by
    intro p hp
    have hpU : p ∈ U_trim := sdiff_subset hp
    have hdeg_ge : N_grid / (4 * (α' : ℝ)) ≤ ((neighbors (gridGraph G) U_trim p).card : ℝ) := by
      by_contra! hlt
      exact (mem_sdiff.mp hp).2 (mem_filter.mpr ⟨hpU, hlt⟩)
    have hnbr_sub : neighbors (gridGraph G) U_trim p ⊆
        neighbors (gridGraph G) (R_row p.1.1) p ∪ neighbors (gridGraph G) (C_col p.1.2) p := by
      intro q hq
      obtain ⟨hqU, hpq⟩ := mem_neighbors.mp hq
      by_cases hi : q.1.1 = p.1.1
      · obtain ⟨i, hiI, hqR⟩ := mem_biUnion.mp hqU
        have hpi : p.1.1 = i := by
          obtain ⟨j', _, hqcell⟩ := mem_biUnion.mp (hR_sub' i hiI hqR)
          exact hi.symm.trans (hcell_fst i j' q hqcell).1
        exact mem_union_left _ (mem_neighbors.mpr ⟨hpi ▸ hqR, hpq⟩)
      · have hj : q.1.2 = p.1.2 := by
          by_contra hnj
          exact hG_cross p (hU_trim_sub hpU) q (hU_trim_sub hqU) (Ne.symm hi) (Ne.symm hnj) hpq
        exact mem_union_right _ (mem_neighbors.mpr ⟨mem_filter.mpr ⟨hqU, hj⟩, hpq⟩)
    have hc : ((neighbors (gridGraph G) U_trim p).card : ℝ) ≤
        ((neighbors (gridGraph G) (R_row p.1.1) p).card : ℝ) + ((neighbors (gridGraph G) (C_col p.1.2) p).card : ℝ) := by
      exact_mod_cast (card_le_card hnbr_sub).trans (card_union_le _ _)
    by_cases hr : N_grid / (8 * (α' : ℝ)) ≤ ((neighbors (gridGraph G) (R_row p.1.1) p).card : ℝ)
    · exact mem_union_left _ (mem_filter.mpr ⟨hp, hr⟩)
    · refine mem_union_right _ (mem_filter.mpr ⟨hp, ?_⟩)
      have hr' : ((neighbors (gridGraph G) (R_row p.1.1) p).card : ℝ) < N_grid / (8 * (α' : ℝ)) :=
        lt_of_not_ge hr
      linarith only [hdeg_ge, hc, hr',
        show N_grid / (4 * (α' : ℝ)) = 2 * (N_grid / (8 * (α' : ℝ))) by ring]
  have hHigh_cases : N_grid / 4 ≤ (High_row.card : ℝ) ∨ N_grid / 4 ≤ (High_col.card : ℝ) := by
    have hc : (High.card : ℝ) ≤ (High_row.card : ℝ) + (High_col.card : ℝ) := by
      exact_mod_cast (card_le_card hHigh_cover).trans (card_union_le _ _)
    by_cases hr : N_grid / 4 ≤ (High_row.card : ℝ)
    · exact Or.inl hr
    · right; linarith
  rcases hHigh_cases with hRow_case | hCol_case
  · right; right
    exact grid_row_case G α_orig α' hα'eq hα'pos I_rows J_cols U_grid cell hcell_fst hG_ind hG_TF
      hG_cross X M₀ T hT_pos hT_ge hs₀_pos I_cur J_cur hs1_2 hNoBad R_row hR_sub' hR_card'
      hR_disj U_trim rfl hU_trim_sub N_grid hN_grid_eq hN_grid_ge hN_4a C_col (fun _ => rfl)
      High_row ((filter_subset _ _).trans sdiff_subset) (fun p hp => (mem_filter.mp hp).2) hRow_case
  · right; left
    exact grid_col_case G α_orig α' hα'eq hα'pos I_rows J_cols U_grid cell hcell_fst hG_ind hG_TF
      hG_cross X M₀ hX_pos T hTX6 I_cur J_cur hs1_2 R_row hR_sub' hR_card' hR_disj hM₀_ge hM₀_pos
      U_trim rfl hU_trim_sub N_grid hN_grid_eq C_col (fun _ => rfl) hC_col_le High_col
      ((filter_subset _ _).trans sdiff_subset) (fun p hp => (mem_filter.mp hp).2) hCol_case

end GridLemma

section Claim2AndMain

variable {V : Type*} [DecidableEq V] [Fintype V]

private lemma ext_subset_N_tri_adj (G : SimpleGraph V) (hK4 : Clique4Free G)
    (V' : Finset V) (outN : V → Finset V)
    (hout_sub : ∀ u ∈ V', outN u ⊆ neighbors G V' u)
    {v u w z : V} (huV' : u ∈ V') (huv_adj : G.Adj u v)
    (hw_out : w ∈ outN u) (hw_nv : G.Adj v w)
    (hz_out : z ∈ outN u) (hwz : G.Adj w z) (hzv : z ≠ v) :
    z ∈ N_tri G v := by
  have huw_adj : G.Adj u w := (mem_neighbors.mp (hout_sub u huV' hw_out)).2
  have huz_adj : G.Adj u z := (mem_neighbors.mp (hout_sub u huV' hz_out)).2
  have hnvz : ¬ G.Adj v z := by
    intro hvz
    let K : Finset V := {v, u, w, z}
    have hKc : K.card = 4 := by
      rw [card_insert_of_notMem (by simp [huv_adj.ne.symm, hw_nv.ne, hzv.symm]),
          card_insert_of_notMem (by simp [huw_adj.ne, huz_adj.ne]),
          card_pair hwz.ne]
    refine hK4 K hKc ?_
    intro a ha b hb hab
    simp only [K, coe_insert, coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
    rcases ha with rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl
    · exact False.elim (hab rfl)
    · exact huv_adj.symm
    · exact hw_nv
    · exact hvz
    · exact huv_adj
    · exact False.elim (hab rfl)
    · exact huw_adj
    · exact huz_adj
    · exact hw_nv.symm
    · exact huw_adj.symm
    · exact False.elim (hab rfl)
    · exact hwz
    · exact hvz.symm
    · exact huz_adj.symm
    · exact hwz.symm
    · exact False.elim (hab rfl)
  refine mem_N_tri.mpr ⟨hzv, hnvz, ({u, w} : Finset V), ?_, ?_⟩
  · refine mem_edgesIn.mpr ⟨?_, card_pair huw_adj.ne, ?_⟩
    · intro a ha
      simp only [mem_insert, mem_singleton] at ha
      rcases ha with rfl | rfl
      · exact mem_neighbors.mpr ⟨mem_univ _, huv_adj.symm⟩
      · exact mem_neighbors.mpr ⟨mem_univ _, hw_nv⟩
    · intro a ha b hb hab
      simp only [coe_insert, coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
      · exact False.elim (hab rfl)
      · exact huw_adj
      · exact huw_adj.symm
      · exact False.elim (hab rfl)
  · intro a ha
    simp only [mem_insert, mem_singleton] at ha
    rcases ha with rfl | rfl
    · exact huz_adj.symm
    · exact hwz.symm

private lemma claim2_case_C (n : ℕ) (G : SimpleGraph (Fin n)) (α : ℕ)
    (hInd : ∀ I : Finset (Fin n), G.IsIndepSet (I : Set (Fin n)) → I.card ≤ α)
    (hK4 : Clique4Free G) (hLoc : LocalIndep G) (L : ℕ)
    (hnR : (1 : ℝ) ≤ (n : ℝ)) (hαR : (1 : ℝ) ≤ (α : ℝ)) (hLR : (1 : ℝ) ≤ (L : ℝ))
    (hpoly : ∀ (p j q : ℕ), 1 ≤ p → ∀ (C : ℝ), 0 ≤ C → 5 * q ≤ 12 * p → 12 * j ≤ q →
      C ^ 12 ≤ (10 ^ 30 : ℝ) ^ q → C * (L : ℝ) ^ j * (α : ℝ) ^ q < (n : ℝ) ^ p)
    (V' : Finset (Fin n)) (outN : Fin n → Finset (Fin n))
    (hout_sub' : ∀ u ∈ V', outN u ⊆ neighbors G V' u)
    (x_nat : ℕ) (hx_nat_R : (1 : ℝ) ≤ (x_nat : ℝ))
    (hx_nat_lb : (n : ℝ) / (64 * (α : ℝ) ^ 2) ≤ (x_nat : ℝ))
    (v : Fin n) (hNv_TF : TriangleFree G (neighbors G Finset.univ v))
    (s t : ℕ) (hs_pos : 1 ≤ s) (ht_pos : 1 ≤ t) (ht_le_a : t ≤ α)
    (hst2_n6 : (n : ℝ) ^ 6 / (5184 * 64 ^ 6 * (L : ℝ) * (α : ℝ) ^ 12) ≤ (s : ℝ) * (t : ℝ) ^ 2)
    (S_leaves : Finset (Fin n)) (hS_leaves_card : S_leaves.card = s)
    (hS_sub_V' : S_leaves ⊆ V')
    (hleaf_prop : ∀ u ∈ S_leaves, u ∈ neighbors G V' v ∧ t ≤ (outN v ∩ outN u).card)
    (T_u : Fin n → Finset (Fin n)) (hTu_card' : ∀ u ∈ S_leaves, (T_u u).card = t)
    (ext₀ : Fin n → Fin n → Finset (Fin n))
    (hext₀_sub : ∀ u ∈ S_leaves, ∀ w ∈ T_u u,
      ext₀ u w ⊆ (N_tri G v ∩ outN u) ∩ neighbors G Finset.univ w)
    (hext₀_disj : ∀ u ∈ S_leaves, ∀ w₁ ∈ T_u u, ∀ w₂ ∈ T_u u,
      w₁ ≠ w₂ → Disjoint (ext₀ u w₁) (ext₀ u w₂))
    (M : Finset (Fin n × Fin n))
    (hM_mem : ∀ p ∈ M, p.1 ∈ S_leaves ∧ p.2 ∈ T_u p.1)
    (hM_nv : ∀ p ∈ M, p.1 ∈ neighbors G Finset.univ v ∧ p.2 ∈ neighbors G Finset.univ v ∧ G.Adj p.1 p.2)
    (C_set : Finset (Fin n)) (C_part : Fin n → Finset (Fin n))
    (hC_biU : C_set = (neighbors G Finset.univ v).biUnion C_part)
    (hC_disj : ∀ c₁ ∈ neighbors G Finset.univ v, ∀ c₂ ∈ neighbors G Finset.univ v, c₁ ≠ c₂ →
      Disjoint (C_part c₁) (C_part c₂) ∧ ∀ x ∈ C_part c₁, ∀ y ∈ C_part c₂, ¬ G.Adj x y)
    (hC_ctr : ∀ c ∈ neighbors G Finset.univ v, ∀ w ∈ C_part c, ∀ e ∈ vTris G v w, c ∈ e)
    (M_C : Finset (Fin n × Fin n)) (hMC_sub : M_C ⊆ M)
    (hMC_prop : ∀ p ∈ M_C, x_nat ≤ 3 * (ext₀ p.1 p.2 ∩ C_set).card)
    (hC_maj : s * t ≤ 3 * M_C.card) :
    False := by
  classical
  let Nv := neighbors G Finset.univ v
  have hMC_nv : ∀ p ∈ M_C, p.1 ∈ Nv ∧ p.2 ∈ Nv ∧ G.Adj p.1 p.2 := fun p hp =>
    hM_nv p (hMC_sub hp)
  obtain ⟨M', hM'sub, hM'disj, hM'card⟩ :=
    greedy_matching_of_directed G Nv α hNv_TF (fun I _ hI => hInd I hI) M_C hMC_nv
  let N_e (p : Fin n × Fin n) : Finset (Fin n) := ext₀ p.1 p.2 ∩ C_set
  have hN_sub : ∀ p ∈ M', N_e p ⊆ N_tri G v ∧ ∀ z ∈ N_e p, G.Adj z p.1 ∧ G.Adj z p.2 := by
    intro p hp
    have hpM : p ∈ M := hMC_sub (hM'sub hp)
    obtain ⟨hu, hw⟩ := hM_mem p hpM
    have hsub := hext₀_sub p.1 hu p.2 hw
    refine ⟨inter_subset_left.trans (hsub.trans (inter_subset_left.trans inter_subset_left)), fun z hz => ?_⟩
    have hz_ext := (mem_inter.mp hz).1
    have hz_out := (mem_inter.mp (mem_inter.mp (hsub hz_ext)).1).2
    have hz_w := (mem_neighbors.mp (mem_inter.mp (hsub hz_ext)).2).2
    have hz_u : G.Adj p.1 z := (mem_neighbors.mp (hout_sub' p.1 (hS_sub_V' hu) hz_out)).2
    exact ⟨hz_u.symm, hz_w.symm⟩
  have hind_U : G.IsIndepSet (↑(M'.biUnion N_e) : Set (Fin n)) :=
    indep_of_disjoint_edge_exts G hK4 hLoc v M' (fun p hp => hMC_nv p (hM'sub hp))
      hM'disj N_e hN_sub
  have hdisj_N : Set.PairwiseDisjoint (M' : Set (Fin n × Fin n)) N_e := by
    intro p hp q hq hpq
    change Disjoint _ _
    rw [disjoint_left]
    intro z hzp hzq
    have hzC : z ∈ C_set := (mem_inter.mp hzp).2
    rw [hC_biU] at hzC
    obtain ⟨c, hcNv, hzc⟩ := mem_biUnion.mp hzC
    have hep : ({p.1, p.2} : Finset (Fin n)) ∈ vTris G v z := by
      refine mem_vTris.mpr ⟨mem_edgesIn.mpr ⟨?_, card_pair (hMC_nv p (hM'sub hp)).2.2.ne, ?_⟩, ?_⟩
      · intro a ha; simp only [mem_insert, mem_singleton] at ha
        rcases ha with rfl | rfl; exact (hMC_nv p (hM'sub hp)).1; exact (hMC_nv p (hM'sub hp)).2.1
      · intro a ha b hb hab
        simp only [coe_insert, coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
        rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
        · exact False.elim (hab rfl)
        · exact (hMC_nv p (hM'sub hp)).2.2
        · exact (hMC_nv p (hM'sub hp)).2.2.symm
        · exact False.elim (hab rfl)
      · intro a ha; simp only [mem_insert, mem_singleton] at ha
        rcases ha with rfl | rfl; exact (hN_sub p hp).2 z hzp |>.1; exact (hN_sub p hp).2 z hzp |>.2
    have heq : ({q.1, q.2} : Finset (Fin n)) ∈ vTris G v z := by
      refine mem_vTris.mpr ⟨mem_edgesIn.mpr ⟨?_, card_pair (hMC_nv q (hM'sub hq)).2.2.ne, ?_⟩, ?_⟩
      · intro a ha; simp only [mem_insert, mem_singleton] at ha
        rcases ha with rfl | rfl; exact (hMC_nv q (hM'sub hq)).1; exact (hMC_nv q (hM'sub hq)).2.1
      · intro a ha b hb hab
        simp only [coe_insert, coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
        rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
        · exact False.elim (hab rfl)
        · exact (hMC_nv q (hM'sub hq)).2.2
        · exact (hMC_nv q (hM'sub hq)).2.2.symm
        · exact False.elim (hab rfl)
      · intro a ha; simp only [mem_insert, mem_singleton] at ha
        rcases ha with rfl | rfl; exact (hN_sub q hq).2 z hzq |>.1; exact (hN_sub q hq).2 z hzq |>.2
    have hcp := hC_ctr c hcNv z hzc _ hep
    have hcq := hC_ctr c hcNv z hzc _ heq
    have hd := hM'disj p hp q hq hpq
    simp only [mem_insert, mem_singleton] at hcp hcq
    rcases hcp with hcp | hcp <;> rcases hcq with hcq | hcq
    · exact hd.1 (hcp.symm.trans hcq)
    · exact hd.2.1 (hcp.symm.trans hcq)
    · exact hd.2.2.1 (hcp.symm.trans hcq)
    · exact hd.2.2.2 (hcp.symm.trans hcq)
  have hstx_le : (s : ℝ) * (t : ℝ) * (x_nat : ℝ) ≤ 36 * (α : ℝ) ^ 2 := by
    have hU_le : ((M'.biUnion N_e).card : ℝ) ≤ (α : ℝ) := by exact_mod_cast hInd _ hind_U
    have hU_ge : (M'.card : ℝ) * (x_nat : ℝ) / 3 ≤ ((M'.biUnion N_e).card : ℝ) := by
      have h1 : (M'.biUnion N_e).card = ∑ p ∈ M', (N_e p).card := card_biUnion hdisj_N
      have h1r : ((M'.biUnion N_e).card : ℝ) = ∑ p ∈ M', ((N_e p).card : ℝ) := by exact_mod_cast h1
      rw [h1r]
      calc
        (M'.card : ℝ) * (x_nat : ℝ) / 3 = ∑ _p ∈ M', ((x_nat : ℝ) / 3) := by
          rw [sum_const, nsmul_eq_mul]; ring
        _ ≤ ∑ p ∈ M', ((N_e p).card : ℝ) := by
          refine sum_le_sum fun p hp => ?_
          have h3 : (x_nat : ℝ) ≤ 3 * ((N_e p).card : ℝ) := by
            exact_mod_cast hMC_prop p (hM'sub hp)
          linarith
    have h1 : (M'.card : ℝ) * (x_nat : ℝ) ≤ 3 * (α : ℝ) := by linarith
    have h2 : (s : ℝ) * (t : ℝ) ≤ 12 * (α : ℝ) * (M'.card : ℝ) := by
      have ha1 : (s : ℝ) * (t : ℝ) ≤ 3 * (M_C.card : ℝ) := by exact_mod_cast hC_maj
      have ha2 : (M_C.card : ℝ) ≤ 4 * (α : ℝ) * (M'.card : ℝ) := by exact_mod_cast hM'card
      nlinarith
    calc
      (s : ℝ) * (t : ℝ) * (x_nat : ℝ)
        ≤ (12 * (α : ℝ) * (M'.card : ℝ)) * (x_nat : ℝ) := by gcongr
      _ = 12 * (α : ℝ) * ((M'.card : ℝ) * (x_nat : ℝ)) := by ring
      _ ≤ 12 * (α : ℝ) * (3 * (α : ℝ)) := by gcongr
      _ = 36 * (α : ℝ) ^ 2 := by ring
  have ht_lb : (n : ℝ) ^ 7 / (36 * 5184 * 64 ^ 7 * (L : ℝ) * (α : ℝ) ^ 16) ≤ (t : ℝ) := by
    have hst_le : (s : ℝ) * (t : ℝ) ≤ 36 * 64 * (α : ℝ) ^ 4 / (n : ℝ) := by
      have h1 : (s : ℝ) * (t : ℝ) * ((n : ℝ) / (64 * (α : ℝ) ^ 2)) ≤ (s : ℝ) * (t : ℝ) * (x_nat : ℝ) := by
        gcongr
      have h2 : (s : ℝ) * (t : ℝ) * ((n : ℝ) / (64 * (α : ℝ) ^ 2)) ≤ 36 * (α : ℝ) ^ 2 := h1.trans hstx_le
      rw [le_div_iff₀ (by positivity)]
      have heq : (s : ℝ) * (t : ℝ) * (n : ℝ) =
          ((s : ℝ) * (t : ℝ) * ((n : ℝ) / (64 * (α : ℝ) ^ 2))) * (64 * (α : ℝ) ^ 2) := by
        have : (α : ℝ) ≠ 0 := by positivity
        field_simp
      nlinarith [h2, heq, (by positivity : (0 : ℝ) < (α : ℝ) ^ 2)]
    have hmul : (n : ℝ) ^ 6 / (5184 * 64 ^ 6 * (L : ℝ) * (α : ℝ) ^ 12) ≤
        (t : ℝ) * (36 * 64 * (α : ℝ) ^ 4 / (n : ℝ)) := by
      calc
        (n : ℝ) ^ 6 / (5184 * 64 ^ 6 * (L : ℝ) * (α : ℝ) ^ 12) ≤ (s : ℝ) * (t : ℝ) ^ 2 := hst2_n6
        _ = (t : ℝ) * ((s : ℝ) * (t : ℝ)) := by ring
        _ ≤ (t : ℝ) * (36 * 64 * (α : ℝ) ^ 4 / (n : ℝ)) := by gcongr
    rw [div_le_iff₀ (by positivity)]
    have hclear : (n : ℝ) ^ 6 * (n : ℝ) ≤
        ((t : ℝ) * (36 * 64 * (α : ℝ) ^ 4 / (n : ℝ))) * (n : ℝ) * (5184 * 64 ^ 6 * (L : ℝ) * (α : ℝ) ^ 12) := by
      have hn0 : (n : ℝ) ≠ 0 := by positivity
      have h1' : (n : ℝ) ^ 6 ≤ ((t : ℝ) * (36 * 64 * (α : ℝ) ^ 4 / (n : ℝ))) *
          (5184 * 64 ^ 6 * (L : ℝ) * (α : ℝ) ^ 12) := by
        rw [div_le_iff₀ (by positivity)] at hmul
        exact hmul
      nlinarith
    have heq_rhs : ((t : ℝ) * (36 * 64 * (α : ℝ) ^ 4 / (n : ℝ))) * (n : ℝ) *
        (5184 * 64 ^ 6 * (L : ℝ) * (α : ℝ) ^ 12) =
        (t : ℝ) * (36 * 5184 * 64 ^ 7 * (L : ℝ) * (α : ℝ) ^ 16) := by
      have hn0 : (n : ℝ) ≠ 0 := by positivity
      field_simp
    rw [heq_rhs] at hclear
    linarith [show (n : ℝ) ^ 7 = (n : ℝ) ^ 6 * (n : ℝ) by ring]
  let M_C_src := M_C.filter (fun p => x_nat ≤ 6 * (ext₀ p.1 p.2 ∩ C_part p.1).card)
  let M_C_sink := M_C.filter (fun p => x_nat ≤ 6 * (ext₀ p.1 p.2 ∩ C_part p.2).card)
  have hMC_split : M_C ⊆ M_C_src ∪ M_C_sink := by
    intro p hp
    have hpM : p ∈ M := hMC_sub hp
    obtain ⟨hu, hw⟩ := hM_mem p hpM
    have hp3 : x_nat ≤ 3 * (ext₀ p.1 p.2 ∩ C_set).card := hMC_prop p hp
    have hsub : ext₀ p.1 p.2 ∩ C_set ⊆
        (ext₀ p.1 p.2 ∩ C_part p.1) ∪ (ext₀ p.1 p.2 ∩ C_part p.2) := by
      intro z hz
      have hz_ext := (mem_inter.mp hz).1
      have hz_C := (mem_inter.mp hz).2
      rw [hC_biU] at hz_C
      obtain ⟨c, hcNv, hzc⟩ := mem_biUnion.mp hz_C
      have hz_sub := hext₀_sub p.1 hu p.2 hw hz_ext
      have hz_out := (mem_inter.mp (mem_inter.mp hz_sub).1).2
      have hz_w := (mem_neighbors.mp (mem_inter.mp hz_sub).2).2
      have hz_u : G.Adj p.1 z := (mem_neighbors.mp (hout_sub' p.1 (hS_sub_V' hu) hz_out)).2
      have he : ({p.1, p.2} : Finset (Fin n)) ∈ vTris G v z := by
        refine mem_vTris.mpr ⟨mem_edgesIn.mpr ⟨?_, card_pair (hMC_nv p hp).2.2.ne, ?_⟩, ?_⟩
        · intro a ha; simp only [mem_insert, mem_singleton] at ha
          rcases ha with rfl | rfl; exact (hMC_nv p hp).1; exact (hMC_nv p hp).2.1
        · intro a ha b hb hab
          simp only [coe_insert, coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
          rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
          · exact False.elim (hab rfl)
          · exact (hMC_nv p hp).2.2
          · exact (hMC_nv p hp).2.2.symm
          · exact False.elim (hab rfl)
        · intro a ha; simp only [mem_insert, mem_singleton] at ha
          rcases ha with rfl | rfl; exact hz_u.symm; exact hz_w.symm
      have hcp := hC_ctr c hcNv z hzc _ he
      simp only [mem_insert, mem_singleton] at hcp
      rcases hcp with hcp | hcp
      · exact mem_union_left _ (mem_inter.mpr ⟨hz_ext, hcp ▸ hzc⟩)
      · exact mem_union_right _ (mem_inter.mpr ⟨hz_ext, hcp ▸ hzc⟩)
    have hcle := (card_le_card hsub).trans (card_union_le _ _)
    by_cases h1 : x_nat ≤ 6 * (ext₀ p.1 p.2 ∩ C_part p.1).card
    · exact mem_union_left _ (mem_filter.mpr ⟨hp, h1⟩)
    · refine mem_union_right _ (mem_filter.mpr ⟨hp, ?_⟩)
      omega
  have hsrc_or_sink : s * t ≤ 6 * M_C_sink.card ∨ s * t ≤ 6 * M_C_src.card := by
    have h1 : M_C.card ≤ M_C_src.card + M_C_sink.card :=
      (card_le_card hMC_split).trans (card_union_le _ _)
    omega
  rcases hsrc_or_sink with hSink | hSrc
  · -- Subcase C-sink
    have hex_u : ∃ u ∈ S_leaves, t ≤ 6 * (M_C_sink.filter (fun p => p.1 = u)).card := by
      by_contra! hlt
      have hsub : M_C_sink ⊆ S_leaves.biUnion (fun u => M_C_sink.filter (fun p => p.1 = u)) := by
        intro p hp
        exact mem_biUnion.mpr ⟨p.1, (hM_mem p (hMC_sub (filter_subset _ _ hp))).1,
          mem_filter.mpr ⟨hp, rfl⟩⟩
      have hsum_le : 6 * M_C_sink.card < ∑ _u ∈ S_leaves, t := by
        calc
          6 * M_C_sink.card ≤ 6 * ∑ u ∈ S_leaves, (M_C_sink.filter (fun p => p.1 = u)).card :=
            Nat.mul_le_mul_left 6 ((card_le_card hsub).trans card_biUnion_le)
          _ = ∑ u ∈ S_leaves, 6 * (M_C_sink.filter (fun p => p.1 = u)).card := by rw [mul_sum]
          _ < ∑ _u ∈ S_leaves, t := sum_lt_sum (fun u hu => (hlt u hu).le) (by
              obtain ⟨u₀, hu₀⟩ := card_pos.mp (by rw [hS_leaves_card]; exact hs_pos)
              exact ⟨u₀, hu₀, hlt u₀ hu₀⟩)
      rw [sum_const, smul_eq_mul, hS_leaves_card] at hsum_le
      omega
    obtain ⟨u, hu, hsink_u⟩ := hex_u
    let W_u := (T_u u).filter (fun w => (u, w) ∈ M_C_sink)
    have hW_eq : (M_C_sink.filter (fun p => p.1 = u)).card = W_u.card := by
      refine card_bij (fun p _ => p.2) ?_ ?_ ?_
      · intro p hp
        obtain ⟨hp_sink, hpu⟩ := mem_filter.mp hp
        have hpM : p ∈ M := hMC_sub (filter_subset _ _ hp_sink)
        have hpw : p.2 ∈ T_u p.1 := (hM_mem p hpM).2
        have hp_eq : (u, p.2) = p := Prod.ext hpu.symm rfl
        exact mem_filter.mpr ⟨hpu ▸ hpw, hp_eq ▸ hp_sink⟩
      · intro p₁ hp₁ p₂ hp₂ heq
        exact Prod.ext ((mem_filter.mp hp₁).2.trans (mem_filter.mp hp₂).2.symm) heq
      · intro w hw
        obtain ⟨_, hw_sink⟩ := mem_filter.mp hw
        exact ⟨(u, w), mem_filter.mpr ⟨hw_sink, rfl⟩, rfl⟩
    rw [hW_eq] at hsink_u
    let B (w : Fin n) : Finset (Fin n) := ext₀ u w ∩ C_part w
    have hB_ind : G.IsIndepSet (↑(W_u.biUnion B) : Set (Fin n)) := by
      rw [G.isIndepSet_iff]
      intro z₁ hz₁ z₂ hz₂ hzne hadj
      simp only [mem_coe, mem_biUnion] at hz₁ hz₂
      obtain ⟨w₁, hw₁, hz₁B⟩ := hz₁
      obtain ⟨w₂, hw₂, hz₂B⟩ := hz₂
      by_cases hw : w₁ = w₂
      · subst hw
        have hz1_sub := hext₀_sub u hu w₁ (filter_subset _ _ hw₁) (mem_inter.mp hz₁B).1
        have hz2_sub := hext₀_sub u hu w₁ (filter_subset _ _ hw₁) (mem_inter.mp hz₂B).1
        have hz1_out := (mem_inter.mp (mem_inter.mp hz1_sub).1).2
        have hz2_out := (mem_inter.mp (mem_inter.mp hz2_sub).1).2
        have hz1_w := (mem_neighbors.mp (mem_inter.mp hz1_sub).2).2
        have hz2_w := (mem_neighbors.mp (mem_inter.mp hz2_sub).2).2
        have huV' : u ∈ V' := hS_sub_V' hu
        have hz1_u : G.Adj u z₁ := (mem_neighbors.mp (hout_sub' u huV' hz1_out)).2
        have hz2_u : G.Adj u z₂ := (mem_neighbors.mp (hout_sub' u huV' hz2_out)).2
        have huw : G.Adj u w₁ := (hM_nv (u, w₁) (hMC_sub (filter_subset _ _ (mem_filter.mp hw₁).2))).2.2
        let K : Finset (Fin n) := {u, w₁, z₁, z₂}
        have hKc : K.card = 4 := by
          rw [card_insert_of_notMem (by simp [huw.ne, hz1_u.ne, hz2_u.ne]),
              card_insert_of_notMem (by simp [hz1_w.ne, hz2_w.ne]), card_pair hzne]
        refine hK4 K hKc ?_
        intro a ha b hb hab
        simp only [K, coe_insert, coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
        rcases ha with rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl
        · exact False.elim (hab rfl)
        · exact huw
        · exact hz1_u
        · exact hz2_u
        · exact huw.symm
        · exact False.elim (hab rfl)
        · exact hz1_w
        · exact hz2_w
        · exact hz1_u.symm
        · exact hz1_w.symm
        · exact False.elim (hab rfl)
        · exact hadj
        · exact hz2_u.symm
        · exact hz2_w.symm
        · exact hadj.symm
        · exact False.elim (hab rfl)
      · have hw1_nv : w₁ ∈ Nv := (hM_nv (u, w₁) (hMC_sub (filter_subset _ _ (mem_filter.mp hw₁).2))).2.1
        have hw2_nv : w₂ ∈ Nv := (hM_nv (u, w₂) (hMC_sub (filter_subset _ _ (mem_filter.mp hw₂).2))).2.1
        exact (hC_disj w₁ hw1_nv w₂ hw2_nv hw).2 z₁ (mem_inter.mp hz₁B).2 z₂ (mem_inter.mp hz₂B).2 hadj
    have hB_disj : Set.PairwiseDisjoint (W_u : Set (Fin n)) B := by
      intro w₁ hw₁ w₂ hw₂ hne
      change Disjoint _ _
      rw [disjoint_left]
      intro z hz1 hz2
      have hw1_nv : w₁ ∈ Nv := (hM_nv (u, w₁) (hMC_sub (filter_subset _ _ (mem_filter.mp hw₁).2))).2.1
      have hw2_nv : w₂ ∈ Nv := (hM_nv (u, w₂) (hMC_sub (filter_subset _ _ (mem_filter.mp hw₂).2))).2.1
      exact (disjoint_left.mp (hC_disj w₁ hw1_nv w₂ hw2_nv hne).1)
        (mem_inter.mp hz1).2 (mem_inter.mp hz2).2
    have hB_sum : (t : ℝ) * (x_nat : ℝ) / 36 ≤ (α : ℝ) := by
      have h1 : ((W_u.biUnion B).card : ℝ) ≤ (α : ℝ) := by exact_mod_cast hInd _ hB_ind
      have h2 : (W_u.biUnion B).card = ∑ w ∈ W_u, (B w).card := card_biUnion hB_disj
      have h2r : ((W_u.biUnion B).card : ℝ) = ∑ w ∈ W_u, ((B w).card : ℝ) := by exact_mod_cast h2
      have h3 : (W_u.card : ℝ) * ((x_nat : ℝ) / 6) ≤ ∑ w ∈ W_u, ((B w).card : ℝ) := by
        rw [← nsmul_eq_mul, ← sum_const]
        refine sum_le_sum fun w hw => ?_
        have h6 : (x_nat : ℝ) ≤ 6 * ((B w).card : ℝ) := by
          exact_mod_cast (mem_filter.mp (mem_filter.mp hw).2).2
        linarith
      have hw_ge : (t : ℝ) / 6 ≤ (W_u.card : ℝ) := by
        have : (t : ℝ) ≤ 6 * (W_u.card : ℝ) := by exact_mod_cast hsink_u
        linarith
      have h4 : (t : ℝ) * (x_nat : ℝ) / 36 ≤ (W_u.card : ℝ) * ((x_nat : ℝ) / 6) := by
        calc
          (t : ℝ) * (x_nat : ℝ) / 36 = ((t : ℝ) / 6) * ((x_nat : ℝ) / 6) := by ring
          _ ≤ (W_u.card : ℝ) * ((x_nat : ℝ) / 6) := by gcongr
      linarith
    have hcontra8 : (n : ℝ) ^ 8 ≤ 36 ^ 2 * 5184 * 64 ^ 8 * (L : ℝ) * (α : ℝ) ^ 19 := by
      have h1 : (n : ℝ) ^ 7 / (36 * 5184 * 64 ^ 7 * (L : ℝ) * (α : ℝ) ^ 16) *
          ((n : ℝ) / (64 * (α : ℝ) ^ 2)) ≤ 36 * (α : ℝ) := by
        have htx : (t : ℝ) * (x_nat : ℝ) ≤ 36 * (α : ℝ) := by linarith
        calc
          (n : ℝ) ^ 7 / (36 * 5184 * 64 ^ 7 * (L : ℝ) * (α : ℝ) ^ 16) * ((n : ℝ) / (64 * (α : ℝ) ^ 2))
            ≤ (t : ℝ) * (x_nat : ℝ) := by gcongr
          _ ≤ 36 * (α : ℝ) := htx
      have heqL : (n : ℝ) ^ 7 / (36 * 5184 * 64 ^ 7 * (L : ℝ) * (α : ℝ) ^ 16) *
          ((n : ℝ) / (64 * (α : ℝ) ^ 2)) =
          (n : ℝ) ^ 8 / (36 * 5184 * 64 ^ 8 * (L : ℝ) * (α : ℝ) ^ 18) := by ring
      rw [heqL, div_le_iff₀ (by positivity)] at h1
      linarith [show (36 * (α : ℝ)) * (36 * 5184 * 64 ^ 8 * (L : ℝ) * (α : ℝ) ^ 18) =
        36 ^ 2 * 5184 * 64 ^ 8 * (L : ℝ) * (α : ℝ) ^ 19 by ring]
    have hpoly8 : 36 ^ 2 * 5184 * 64 ^ 8 * (L : ℝ) * (α : ℝ) ^ 19 < (n : ℝ) ^ 8 := by
      simpa using hpoly 8 1 19 (by decide) (36 ^ 2 * 5184 * 64 ^ 8) (by norm_num) (by decide) (by decide) (by norm_num)
    linarith
  · -- Subcase C-source
    let W_src (u : Fin n) : Finset (Fin n) := (T_u u).filter (fun w => (u, w) ∈ M_C_src)
    have hW_eq : ∀ u ∈ S_leaves, (M_C_src.filter (fun p => p.1 = u)).card = (W_src u).card := by
      intro u _
      refine card_bij (fun p _ => p.2) ?_ ?_ ?_
      · intro p hp
        obtain ⟨hp_src, hpu⟩ := mem_filter.mp hp
        have hpM : p ∈ M := hMC_sub (filter_subset _ _ hp_src)
        have hp_eq : (u, p.2) = p := Prod.ext hpu.symm rfl
        exact mem_filter.mpr ⟨hpu ▸ (hM_mem p hpM).2, hp_eq ▸ hp_src⟩
      · intro p₁ hp₁ p₂ hp₂ heq
        exact Prod.ext ((mem_filter.mp hp₁).2.trans (mem_filter.mp hp₂).2.symm) heq
      · intro w hw
        obtain ⟨_, hw_src⟩ := mem_filter.mp hw
        exact ⟨(u, w), mem_filter.mpr ⟨hw_src, rfl⟩, rfl⟩
    let S'_leaves := S_leaves.filter (fun u => t ≤ 12 * (W_src u).card)
    have hS'_card : (s : ℝ) / 12 ≤ (S'_leaves.card : ℝ) := by
      have hsub : M_C_src ⊆ S_leaves.biUnion (fun u => M_C_src.filter (fun p => p.1 = u)) := by
        intro p hp
        exact mem_biUnion.mpr ⟨p.1, (hM_mem p (hMC_sub (filter_subset _ _ hp))).1,
          mem_filter.mpr ⟨hp, rfl⟩⟩
      have hsum_c : (M_C_src.card : ℝ) ≤ ∑ u ∈ S_leaves, ((W_src u).card : ℝ) := by
        have h1 : M_C_src.card ≤ ∑ u ∈ S_leaves, (M_C_src.filter (fun p => p.1 = u)).card :=
          (card_le_card hsub).trans card_biUnion_le
        have h2 : ∑ u ∈ S_leaves, (M_C_src.filter (fun p => p.1 = u)).card =
            ∑ u ∈ S_leaves, (W_src u).card := sum_congr rfl hW_eq
        exact_mod_cast h1.trans_eq h2
      have hsplit : ∑ u ∈ S_leaves, ((W_src u).card : ℝ) =
          ∑ u ∈ S'_leaves, ((W_src u).card : ℝ) + ∑ u ∈ S_leaves \ S'_leaves, ((W_src u).card : ℝ) := by
        rw [← sum_union disjoint_sdiff_self_right, union_sdiff_of_subset (filter_subset _ _)]
      have h1 : ∑ u ∈ S'_leaves, ((W_src u).card : ℝ) ≤ (S'_leaves.card : ℝ) * (t : ℝ) := by
        calc
          ∑ u ∈ S'_leaves, ((W_src u).card : ℝ) ≤ ∑ _u ∈ S'_leaves, (t : ℝ) := by
            refine sum_le_sum fun u hu => ?_
            have : (W_src u).card ≤ (T_u u).card := card_le_card (filter_subset _ _)
            rw [hTu_card' u (filter_subset _ _ hu)] at this
            exact_mod_cast this
          _ = (S'_leaves.card : ℝ) * (t : ℝ) := by rw [sum_const, nsmul_eq_mul]
      have h2 : ∑ u ∈ S_leaves \ S'_leaves, ((W_src u).card : ℝ) ≤ (s : ℝ) * ((t : ℝ) / 12) := by
        have hsle : ((S_leaves \ S'_leaves).card : ℝ) ≤ (s : ℝ) := by
          rw [← hS_leaves_card]
          exact_mod_cast card_le_card sdiff_subset
        calc
          ∑ u ∈ S_leaves \ S'_leaves, ((W_src u).card : ℝ) ≤ ∑ _u ∈ S_leaves \ S'_leaves, ((t : ℝ) / 12) := by
            refine sum_le_sum fun u hu => ?_
            have hnot : ¬ t ≤ 12 * (W_src u).card := fun hle =>
              (mem_sdiff.mp hu).2 (mem_filter.mpr ⟨(mem_sdiff.mp hu).1, hle⟩)
            have hlt : 12 * ((W_src u).card : ℝ) < (t : ℝ) := by exact_mod_cast Nat.lt_of_not_le hnot
            linarith
          _ = ((S_leaves \ S'_leaves).card : ℝ) * ((t : ℝ) / 12) := by rw [sum_const, nsmul_eq_mul]
          _ ≤ (s : ℝ) * ((t : ℝ) / 12) := by gcongr
      have hsrcR : (s : ℝ) * (t : ℝ) / 6 ≤ (M_C_src.card : ℝ) := by
        have : (s : ℝ) * (t : ℝ) ≤ 6 * (M_C_src.card : ℝ) := by exact_mod_cast hSrc
        linarith
      have htpos : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht_pos
      nlinarith
    have hS'_ne : S'_leaves.Nonempty := by
      rw [← card_pos]
      have hpos : (0 : ℝ) < (S'_leaves.card : ℝ) := by
        have : (0 : ℝ) < (s : ℝ) / 12 := by
          have : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hs_pos
          positivity
        linarith
      exact_mod_cast hpos
    let D_u (u : Fin n) : Finset (Fin n) := (W_src u).biUnion (fun w => ext₀ u w ∩ C_part u)
    have hDu_card : ∀ u ∈ S'_leaves, (t : ℝ) * (x_nat : ℝ) / 72 ≤ ((D_u u).card : ℝ) := by
      intro u hu
      have huS : u ∈ S_leaves := (filter_subset _ _) hu
      have hdisj_w : Set.PairwiseDisjoint (W_src u : Set (Fin n)) (fun w => ext₀ u w ∩ C_part u) := by
        intro w₁ hw₁ w₂ hw₂ hne
        change Disjoint _ _
        rw [disjoint_left]
        intro z hz1 hz2
        exact (disjoint_left.mp (hext₀_disj u huS w₁ (filter_subset _ _ hw₁)
          w₂ (filter_subset _ _ hw₂) hne))
          (mem_inter.mp hz1).1 (mem_inter.mp hz2).1
      have h1 : (D_u u).card = ∑ w ∈ W_src u, (ext₀ u w ∩ C_part u).card :=
        card_biUnion hdisj_w
      have h1r : ((D_u u).card : ℝ) = ∑ w ∈ W_src u, ((ext₀ u w ∩ C_part u).card : ℝ) := by
        exact_mod_cast h1
      have h2 : ((W_src u).card : ℝ) * ((x_nat : ℝ) / 6) ≤ ((D_u u).card : ℝ) := by
        rw [h1r, ← nsmul_eq_mul, ← sum_const]
        refine sum_le_sum fun w hw => ?_
        have h6 : (x_nat : ℝ) ≤ 6 * ((ext₀ u w ∩ C_part u).card : ℝ) := by
          exact_mod_cast (mem_filter.mp (mem_filter.mp hw).2).2
        linarith
      have hw_ge : (t : ℝ) / 12 ≤ ((W_src u).card : ℝ) := by
        have h12 : (t : ℝ) ≤ 12 * ((W_src u).card : ℝ) := by exact_mod_cast (mem_filter.mp hu).2
        linarith
      calc
        (t : ℝ) * (x_nat : ℝ) / 72 = ((t : ℝ) / 12) * ((x_nat : ℝ) / 6) := by ring
        _ ≤ ((W_src u).card : ℝ) * ((x_nat : ℝ) / 6) := by gcongr
        _ ≤ ((D_u u).card : ℝ) := h2
    have hDu_ind : ∀ u : Fin n, ∃ I_u ⊆ D_u u, u ∈ S'_leaves →
        G.IsIndepSet (I_u : Set (Fin n)) ∧ (D_u u).card ≤ 2 * I_u.card ^ 2 := by
      intro u
      by_cases hu : u ∈ S'_leaves
      · obtain ⟨I, h1, h2, h3⟩ := card_triangle_free_subset G (D_u u) (by
          refine triangleFree_subset (N_tri_triangle_free G hK4 hLoc v) ?_
          intro z hz
          obtain ⟨w, hw, hzw⟩ := mem_biUnion.mp hz
          have huS : u ∈ S_leaves := (filter_subset _ _) hu
          have hwT : w ∈ T_u u := (filter_subset _ _) hw
          exact (mem_inter.mp (mem_inter.mp (hext₀_sub u huS w hwT (mem_inter.mp hzw).1)).1).1)
        exact ⟨I, h1, fun _ => ⟨h2, h3⟩⟩
      · exact ⟨∅, empty_subset _, fun hu' => absurd hu' hu⟩
    choose I_u hIu_sub hIu_prop using hDu_ind
    have hIu_sub' : ∀ u ∈ S'_leaves, I_u u ⊆ D_u u := fun u _ => hIu_sub u
    have hIu_ind' : ∀ u ∈ S'_leaves, G.IsIndepSet (I_u u : Set (Fin n)) :=
      fun u hu => (hIu_prop u hu).1
    have hIu_sq' : ∀ u ∈ S'_leaves, (D_u u).card ≤ 2 * (I_u u).card ^ 2 :=
      fun u hu => (hIu_prop u hu).2
    have hIu_in_C : ∀ u ∈ S'_leaves, I_u u ⊆ C_part u := by
      intro u hu z hz
      obtain ⟨w, _, hzw⟩ := mem_biUnion.mp (hIu_sub' u hu hz)
      exact (mem_inter.mp hzw).2
    have hIu_all_ind : G.IsIndepSet (↑(S'_leaves.biUnion I_u) : Set (Fin n)) := by
      rw [G.isIndepSet_iff]
      intro z₁ hz₁ z₂ hz₂ hzne hadj
      simp only [mem_coe, mem_biUnion] at hz₁ hz₂
      obtain ⟨u₁, hu₁, hz₁I⟩ := hz₁
      obtain ⟨u₂, hu₂, hz₂I⟩ := hz₂
      by_cases hu_eq : u₁ = u₂
      · subst hu_eq
        exact (G.isIndepSet_iff.mp (hIu_ind' u₁ hu₁)) hz₁I hz₂I hzne hadj
      · have hu1_nv : u₁ ∈ Nv := mem_neighbors.mpr
          ⟨mem_univ _, (mem_neighbors.mp (hleaf_prop u₁ (filter_subset _ _ hu₁)).1).2⟩
        have hu2_nv : u₂ ∈ Nv := mem_neighbors.mpr
          ⟨mem_univ _, (mem_neighbors.mp (hleaf_prop u₂ (filter_subset _ _ hu₂)).1).2⟩
        exact (hC_disj u₁ hu1_nv u₂ hu2_nv hu_eq).2 z₁ (hIu_in_C u₁ hu₁ hz₁I)
          z₂ (hIu_in_C u₂ hu₂ hz₂I) hadj
    have hIu_disj : Set.PairwiseDisjoint (S'_leaves : Set (Fin n)) I_u := by
      intro u₁ hu₁ u₂ hu₂ hne
      change Disjoint _ _
      rw [disjoint_left]
      intro z hz1 hz2
      have hu1_nv : u₁ ∈ Nv := mem_neighbors.mpr
        ⟨mem_univ _, (mem_neighbors.mp (hleaf_prop u₁ (filter_subset _ _ hu₁)).1).2⟩
      have hu2_nv : u₂ ∈ Nv := mem_neighbors.mpr
        ⟨mem_univ _, (mem_neighbors.mp (hleaf_prop u₂ (filter_subset _ _ hu₂)).1).2⟩
      exact (disjoint_left.mp (hC_disj u₁ hu1_nv u₂ hu2_nv hne).1)
        (hIu_in_C u₁ hu₁ hz1) (hIu_in_C u₂ hu₂ hz2)
    have hIu_sum : ∑ u ∈ S'_leaves, (I_u u).card ≤ α := by
      rw [← card_biUnion hIu_disj]
      exact hInd _ hIu_all_ind
    obtain ⟨u₀, hu₀, hu₀_min⟩ := S'_leaves.exists_min_image (fun u => (I_u u).card) hS'_ne
    have hmin_le : (S'_leaves.card : ℝ) * ((I_u u₀).card : ℝ) ≤ (α : ℝ) := by
      have h1 : S'_leaves.card * (I_u u₀).card ≤ α := by
        calc
          S'_leaves.card * (I_u u₀).card = ∑ _u ∈ S'_leaves, (I_u u₀).card := by simp
          _ ≤ ∑ u ∈ S'_leaves, (I_u u).card := sum_le_sum fun u hu => hu₀_min u hu
          _ ≤ α := hIu_sum
      exact_mod_cast h1
    have hsq_min : (s : ℝ) ^ 2 / 144 * ((t : ℝ) * (x_nat : ℝ) / 144) ≤ (α : ℝ) ^ 2 := by
      have hI0_lb : (t : ℝ) * (x_nat : ℝ) / 144 ≤ ((I_u u₀).card : ℝ) ^ 2 := by
        have h1 : ((D_u u₀).card : ℝ) ≤ 2 * ((I_u u₀).card : ℝ) ^ 2 := by
          exact_mod_cast hIu_sq' u₀ hu₀
        linarith [hDu_card u₀ hu₀]
      have hs_sq : (s : ℝ) ^ 2 / 144 ≤ (S'_leaves.card : ℝ) ^ 2 := by
        have h1 : (s : ℝ) / 12 ≤ (S'_leaves.card : ℝ) := hS'_card
        have hsq := pow_le_pow_left₀ (div_nonneg (Nat.cast_nonneg s) (by norm_num)) h1 2
        nlinarith only [hsq]
      have hprod : ((S'_leaves.card : ℝ) * ((I_u u₀).card : ℝ)) ^ 2 ≤ (α : ℝ) ^ 2 :=
        pow_le_pow_left₀ (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) hmin_le 2
      calc
        (s : ℝ) ^ 2 / 144 * ((t : ℝ) * (x_nat : ℝ) / 144)
          ≤ (S'_leaves.card : ℝ) ^ 2 * ((I_u u₀).card : ℝ) ^ 2 :=
            mul_le_mul hs_sq hI0_lb
              (div_nonneg (mul_nonneg (Nat.cast_nonneg t) (Nat.cast_nonneg x_nat)) (by norm_num))
              (sq_nonneg _)
        _ = ((S'_leaves.card : ℝ) * ((I_u u₀).card : ℝ)) ^ 2 := by ring
        _ ≤ (α : ℝ) ^ 2 := hprod
    have hcontra13 : (n : ℝ) ^ 13 ≤
        2 * 72 * 144 * 64 * 5184 ^ 2 * 64 ^ 12 * (L : ℝ) ^ 2 * (α : ℝ) ^ 31 := by
      have htR_le_a : (t : ℝ) ≤ (α : ℝ) := by exact_mod_cast ht_le_a
      have hstx_le : (s : ℝ) ^ 2 * (t : ℝ) * (x_nat : ℝ) ≤ 144 * 144 * (α : ℝ) ^ 2 := by linarith only [hsq_min]
      have hL_posR : (0 : ℝ) < (L : ℝ) := lt_of_lt_of_le zero_lt_one hLR
      have hα_posR : (0 : ℝ) < (α : ℝ) := lt_of_lt_of_le zero_lt_one hαR
      have hden6_pos : (0 : ℝ) < 5184 * 64 ^ 6 * (L : ℝ) * (α : ℝ) ^ 12 :=
        mul_pos (mul_pos (by norm_num) hL_posR) (pow_pos hα_posR 12)
      have hst2_sq : ((n : ℝ) ^ 6 / (5184 * 64 ^ 6 * (L : ℝ) * (α : ℝ) ^ 12)) ^ 2 ≤
          ((s : ℝ) * (t : ℝ) ^ 2) ^ 2 :=
        pow_le_pow_left₀ (div_nonneg (pow_nonneg (Nat.cast_nonneg n) 6) hden6_pos.le) hst2_n6 2
      have h64a2_nn : (0 : ℝ) ≤ (n : ℝ) / (64 * (α : ℝ) ^ 2) :=
        div_nonneg (Nat.cast_nonneg n) (mul_nonneg (by norm_num) (sq_nonneg _))
      have hlow : ((n : ℝ) ^ 6 / (5184 * 64 ^ 6 * (L : ℝ) * (α : ℝ) ^ 12)) ^ 2 *
          ((n : ℝ) / (64 * (α : ℝ) ^ 2)) ≤
          (s : ℝ) ^ 2 * (t : ℝ) * (x_nat : ℝ) * (α : ℝ) ^ 3 := by
        calc
          ((n : ℝ) ^ 6 / (5184 * 64 ^ 6 * (L : ℝ) * (α : ℝ) ^ 12)) ^ 2 * ((n : ℝ) / (64 * (α : ℝ) ^ 2))
            ≤ ((s : ℝ) * (t : ℝ) ^ 2) ^ 2 * (x_nat : ℝ) :=
              mul_le_mul hst2_sq hx_nat_lb h64a2_nn (sq_nonneg _)
          _ = (s : ℝ) ^ 2 * (t : ℝ) * (x_nat : ℝ) * (t : ℝ) ^ 3 := by ring
          _ ≤ (s : ℝ) ^ 2 * (t : ℝ) * (x_nat : ℝ) * (α : ℝ) ^ 3 :=
              mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg t) htR_le_a 3)
                (mul_nonneg (mul_nonneg (sq_nonneg _) (Nat.cast_nonneg t)) (Nat.cast_nonneg x_nat))
      have h1 : (n : ℝ) ^ 13 / (64 * 5184 ^ 2 * 64 ^ 12 * (L : ℝ) ^ 2 * (α : ℝ) ^ 26) ≤
          144 * 144 * (α : ℝ) ^ 5 := by
        have heq : ((n : ℝ) ^ 6 / (5184 * 64 ^ 6 * (L : ℝ) * (α : ℝ) ^ 12)) ^ 2 *
            ((n : ℝ) / (64 * (α : ℝ) ^ 2)) =
            (n : ℝ) ^ 13 / (64 * 5184 ^ 2 * 64 ^ 12 * (L : ℝ) ^ 2 * (α : ℝ) ^ 26) := by ring
        have h2 : (s : ℝ) ^ 2 * (t : ℝ) * (x_nat : ℝ) * (α : ℝ) ^ 3 ≤
            144 * 144 * (α : ℝ) ^ 2 * (α : ℝ) ^ 3 :=
          mul_le_mul_of_nonneg_right hstx_le (pow_nonneg hα_posR.le 3)
        rw [← heq]
        exact hlow.trans (h2.trans_eq (by ring))
      have hden26_pos : (0 : ℝ) < 64 * 5184 ^ 2 * 64 ^ 12 * (L : ℝ) ^ 2 * (α : ℝ) ^ 26 :=
        mul_pos (mul_pos (by norm_num) (pow_pos hL_posR 2)) (pow_pos hα_posR 26)
      rw [div_le_iff₀ hden26_pos] at h1
      linarith only [h1, show (144 * 144 * (α : ℝ) ^ 5) * (64 * 5184 ^ 2 * 64 ^ 12 * (L : ℝ) ^ 2 * (α : ℝ) ^ 26) =
        2 * 72 * 144 * 64 * 5184 ^ 2 * 64 ^ 12 * (L : ℝ) ^ 2 * (α : ℝ) ^ 31 by ring]
    have hpoly13 : 2 * 72 * 144 * 64 * 5184 ^ 2 * 64 ^ 12 * (L : ℝ) ^ 2 * (α : ℝ) ^ 31 < (n : ℝ) ^ 13 :=
      hpoly 13 2 31 (by decide) (2 * 72 * 144 * 64 * 5184 ^ 2 * 64 ^ 12) (by norm_num) (by decide) (by decide) (by norm_num)
    linarith

private lemma claim2_case_L_le (n : ℕ) (G : SimpleGraph (Fin n)) (α : ℕ)
    (hInd : ∀ I : Finset (Fin n), G.IsIndepSet (I : Set (Fin n)) → I.card ≤ α)
    (hK4 : Clique4Free G) (hLoc : LocalIndep G) (L : ℕ)
    (hnR : (1 : ℝ) ≤ (n : ℝ)) (hαR : (1 : ℝ) ≤ (α : ℝ)) (hLR : (1 : ℝ) ≤ (L : ℝ))
    (hpoly : ∀ (p j q : ℕ), 1 ≤ p → ∀ (C : ℝ), 0 ≤ C → 5 * q ≤ 12 * p → 12 * j ≤ q →
      C ^ 12 ≤ (10 ^ 30 : ℝ) ^ q → C * (L : ℝ) ^ j * (α : ℝ) ^ q < (n : ℝ) ^ p)
    (V' : Finset (Fin n)) (outN : Fin n → Finset (Fin n))
    (hout_sub' : ∀ u ∈ V', outN u ⊆ neighbors G V' u)
    (x_nat : ℕ) (hx_nat_R : (1 : ℝ) ≤ (x_nat : ℝ))
    (hx_nat_lb : (n : ℝ) / (64 * (α : ℝ) ^ 2) ≤ (x_nat : ℝ))
    (v : Fin n) (hNv_TF : TriangleFree G (neighbors G Finset.univ v))
    (s t : ℕ) (hst2_n6 : (n : ℝ) ^ 6 / (5184 * 64 ^ 6 * (L : ℝ) * (α : ℝ) ^ 12) ≤ (s : ℝ) * (t : ℝ) ^ 2)
    (S_leaves : Finset (Fin n)) (hS_sub_V' : S_leaves ⊆ V') (T_u : Fin n → Finset (Fin n))
    (ext₀ : Fin n → Fin n → Finset (Fin n))
    (hext₀_sub : ∀ u ∈ S_leaves, ∀ w ∈ T_u u,
      ext₀ u w ⊆ (N_tri G v ∩ outN u) ∩ neighbors G Finset.univ w)
    (M : Finset (Fin n × Fin n))
    (hM_mem : ∀ p ∈ M, p.1 ∈ S_leaves ∧ p.2 ∈ T_u p.1)
    (hM_nv : ∀ p ∈ M, p.1 ∈ neighbors G Finset.univ v ∧ p.2 ∈ neighbors G Finset.univ v ∧ G.Adj p.1 p.2)
    (L_set : Finset (Fin n)) (hL4 : ∀ w ∈ L_set, (vTris G v w).card ≤ 4)
    (M_L : Finset (Fin n × Fin n)) (hML_sub : M_L ⊆ M)
    (hML_prop : ∀ p ∈ M_L, x_nat ≤ 3 * (ext₀ p.1 p.2 ∩ L_set).card)
    (hL_maj : s * t ≤ 3 * M_L.card) (hst_cmp : t ≤ 72 * s) :
    False := by
  classical
  let Nv := neighbors G Finset.univ v
  have hML_nv : ∀ p ∈ M_L, p.1 ∈ Nv ∧ p.2 ∈ Nv ∧ G.Adj p.1 p.2 := fun p hp =>
    hM_nv p (hML_sub hp)
  obtain ⟨M', hM'sub, hM'disj, hM'card⟩ :=
    greedy_matching_of_directed G Nv α hNv_TF (fun I _ hI => hInd I hI) M_L hML_nv
  let N_e (p : Fin n × Fin n) : Finset (Fin n) := ext₀ p.1 p.2 ∩ L_set
  have hN_sub : ∀ p ∈ M', N_e p ⊆ N_tri G v ∧ ∀ z ∈ N_e p, G.Adj z p.1 ∧ G.Adj z p.2 := by
    intro p hp
    have hpM : p ∈ M := hML_sub (hM'sub hp)
    obtain ⟨hu, hw⟩ := hM_mem p hpM
    have hsub := hext₀_sub p.1 hu p.2 hw
    refine ⟨inter_subset_left.trans (hsub.trans (inter_subset_left.trans inter_subset_left)), fun z hz => ?_⟩
    have hz_ext := (mem_inter.mp hz).1
    have hz_out := (mem_inter.mp (mem_inter.mp (hsub hz_ext)).1).2
    have hz_w := (mem_neighbors.mp (mem_inter.mp (hsub hz_ext)).2).2
    have hz_u : G.Adj p.1 z := (mem_neighbors.mp (hout_sub' p.1 (hS_sub_V' hu) hz_out)).2
    exact ⟨hz_u.symm, hz_w.symm⟩
  have hind_U : G.IsIndepSet (↑(M'.biUnion N_e) : Set (Fin n)) :=
    indep_of_disjoint_edge_exts G hK4 hLoc v M' (fun p hp => hML_nv p (hM'sub hp))
      hM'disj N_e hN_sub
  have hU_le : (M'.biUnion N_e).card ≤ α := hInd _ hind_U
  have hsum_le_4 : ∑ p ∈ M', (N_e p).card ≤ 4 * (M'.biUnion N_e).card := by
    let U := M'.biUnion N_e
    have h1 : ∑ p ∈ M', (N_e p).card = ∑ p ∈ M', ∑ z ∈ U, if z ∈ N_e p then 1 else 0 := by
      refine sum_congr rfl fun p hp => ?_
      rw [sum_boole, Nat.cast_id]
      congr 1; ext z; simp only [mem_filter]
      exact ⟨fun h => ⟨mem_biUnion.mpr ⟨p, hp, h⟩, h⟩, fun h => h.2⟩
    rw [h1, sum_comm]
    calc
      ∑ z ∈ U, ∑ p ∈ M', (if z ∈ N_e p then 1 else 0)
        = ∑ z ∈ U, (M'.filter (fun p => z ∈ N_e p)).card := by
          refine sum_congr rfl fun z _ => ?_; rw [sum_boole, Nat.cast_id]
      _ ≤ ∑ _z ∈ U, 4 := by
          refine sum_le_sum fun z hz => ?_
          obtain ⟨_, _, hzp₀⟩ := mem_biUnion.mp hz
          have hzL : z ∈ L_set := (mem_inter.mp hzp₀).2
          have hinj : (M'.filter (fun p => z ∈ N_e p)).card ≤ (vTris G v z).card := by
            refine card_le_card_of_injOn (fun p => ({p.1, p.2} : Finset (Fin n))) ?_ ?_
            · intro p hp
              obtain ⟨hpM', hzp⟩ := mem_filter.mp hp
              refine mem_vTris.mpr ⟨mem_edgesIn.mpr ⟨?_, card_pair (hML_nv p (hM'sub hpM')).2.2.ne, ?_⟩, ?_⟩
              · intro a ha; simp only [mem_insert, mem_singleton] at ha
                rcases ha with rfl | rfl; exact (hML_nv p (hM'sub hpM')).1; exact (hML_nv p (hM'sub hpM')).2.1
              · intro a ha b hb hab
                simp only [coe_insert, coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
                rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
                · exact False.elim (hab rfl)
                · exact (hML_nv p (hM'sub hpM')).2.2
                · exact (hML_nv p (hM'sub hpM')).2.2.symm
                · exact False.elim (hab rfl)
              · intro a ha; simp only [mem_insert, mem_singleton] at ha
                rcases ha with rfl | rfl; exact (hN_sub p hpM').2 z hzp |>.1; exact (hN_sub p hpM').2 z hzp |>.2
            · intro p₁ hp₁ p₂ hp₂ heq
              by_contra hne
              have hd := hM'disj p₁ (mem_filter.mp hp₁).1 p₂ (mem_filter.mp hp₂).1 hne
              dsimp only at heq
              have hm : p₁.1 ∈ ({p₂.1, p₂.2} : Finset (Fin n)) := by rw [← heq]; simp
              simp only [mem_insert, mem_singleton] at hm
              rcases hm with h | h
              · exact hd.1 h
              · exact hd.2.1 h
          exact hinj.trans (hL4 z hzL)
      _ = 4 * U.card := by rw [sum_const, smul_eq_mul]; ring
  have hstx_le : (s : ℝ) * (t : ℝ) * (x_nat : ℝ) ≤ 144 * (α : ℝ) ^ 2 := by
    have h1 : (M'.card : ℝ) * ((x_nat : ℝ) / 3) ≤ ∑ p ∈ M', ((N_e p).card : ℝ) := by
      rw [← nsmul_eq_mul, ← sum_const]
      refine sum_le_sum fun p hp => ?_
      have h3 : (x_nat : ℝ) ≤ 3 * ((N_e p).card : ℝ) := by
        exact_mod_cast hML_prop p (hM'sub hp)
      linarith
    have h2 : (∑ p ∈ M', ((N_e p).card : ℝ)) ≤ 4 * (α : ℝ) := by
      exact_mod_cast hsum_le_4.trans (Nat.mul_le_mul_left 4 hU_le)
    have h3 : (M'.card : ℝ) * (x_nat : ℝ) ≤ 12 * (α : ℝ) := by linarith
    have h4 : (s : ℝ) * (t : ℝ) ≤ 12 * (α : ℝ) * (M'.card : ℝ) := by
      have ha1 : (s : ℝ) * (t : ℝ) ≤ 3 * (M_L.card : ℝ) := by exact_mod_cast hL_maj
      have ha2 : (M_L.card : ℝ) ≤ 4 * (α : ℝ) * (M'.card : ℝ) := by exact_mod_cast hM'card
      nlinarith
    calc
      (s : ℝ) * (t : ℝ) * (x_nat : ℝ)
        ≤ (12 * (α : ℝ) * (M'.card : ℝ)) * (x_nat : ℝ) := by gcongr
      _ = 12 * (α : ℝ) * ((M'.card : ℝ) * (x_nat : ℝ)) := by ring
      _ ≤ 12 * (α : ℝ) * (12 * (α : ℝ)) := by gcongr
      _ = 144 * (α : ℝ) ^ 2 := by ring
  have hst_le : (s : ℝ) * (t : ℝ) ≤ 144 * 64 * (α : ℝ) ^ 4 / (n : ℝ) := by
    have h1 : (s : ℝ) * (t : ℝ) * ((n : ℝ) / (64 * (α : ℝ) ^ 2)) ≤ 144 * (α : ℝ) ^ 2 := by
      calc
        (s : ℝ) * (t : ℝ) * ((n : ℝ) / (64 * (α : ℝ) ^ 2)) ≤ (s : ℝ) * (t : ℝ) * (x_nat : ℝ) := by gcongr
        _ ≤ 144 * (α : ℝ) ^ 2 := hstx_le
    rw [le_div_iff₀ (by positivity)]
    have : (α : ℝ) ≠ 0 := by positivity
    have heq : (s : ℝ) * (t : ℝ) * (n : ℝ) =
        ((s : ℝ) * (t : ℝ) * ((n : ℝ) / (64 * (α : ℝ) ^ 2))) * (64 * (α : ℝ) ^ 2) := by
      field_simp
    nlinarith [h1, heq, (by positivity : (0 : ℝ) < (α : ℝ) ^ 2)]
  have hst_cube : ((n : ℝ) ^ 6 / (5184 * 64 ^ 6 * (L : ℝ) * (α : ℝ) ^ 12)) ^ 2 ≤
      72 * (144 * 64 * (α : ℝ) ^ 4 / (n : ℝ)) ^ 3 := by
    have h1 : ((n : ℝ) ^ 6 / (5184 * 64 ^ 6 * (L : ℝ) * (α : ℝ) ^ 12)) ^ 2 ≤
        ((s : ℝ) * (t : ℝ) ^ 2) ^ 2 := pow_le_pow_left₀ (by positivity) hst2_n6 2
    have h2 : ((s : ℝ) * (t : ℝ) ^ 2) ^ 2 ≤ 72 * ((s : ℝ) * (t : ℝ)) ^ 3 := by
      have ht72 : (t : ℝ) ≤ 72 * (s : ℝ) := by exact_mod_cast hst_cmp
      calc
        ((s : ℝ) * (t : ℝ) ^ 2) ^ 2 = (s : ℝ) ^ 2 * (t : ℝ) * (t : ℝ) ^ 3 := by ring
        _ ≤ (s : ℝ) ^ 2 * (72 * (s : ℝ)) * (t : ℝ) ^ 3 := by gcongr
        _ = 72 * ((s : ℝ) * (t : ℝ)) ^ 3 := by ring
    have h3 : 72 * ((s : ℝ) * (t : ℝ)) ^ 3 ≤ 72 * (144 * 64 * (α : ℝ) ^ 4 / (n : ℝ)) ^ 3 := by
      gcongr
    exact h1.trans (h2.trans h3)
  have hcontra15 : (n : ℝ) ^ 15 ≤
      72 * (144 * 64) ^ 3 * 5184 ^ 2 * 64 ^ 12 * (L : ℝ) ^ 2 * (α : ℝ) ^ 36 := by
    have heqL : ((n : ℝ) ^ 6 / (5184 * 64 ^ 6 * (L : ℝ) * (α : ℝ) ^ 12)) ^ 2 =
        (n : ℝ) ^ 12 / (5184 ^ 2 * 64 ^ 12 * (L : ℝ) ^ 2 * (α : ℝ) ^ 24) := by ring
    have heqR : 72 * (144 * 64 * (α : ℝ) ^ 4 / (n : ℝ)) ^ 3 =
        (72 * (144 * 64) ^ 3 * (α : ℝ) ^ 12) / (n : ℝ) ^ 3 := by ring
    rw [heqL, heqR, div_le_div_iff₀ (by positivity) (by positivity)] at hst_cube
    linarith [show (n : ℝ) ^ 12 * (n : ℝ) ^ 3 = (n : ℝ) ^ 15 by ring,
      show (72 * (144 * 64) ^ 3 * (α : ℝ) ^ 12) * (5184 ^ 2 * 64 ^ 12 * (L : ℝ) ^ 2 * (α : ℝ) ^ 24) =
        72 * (144 * 64) ^ 3 * 5184 ^ 2 * 64 ^ 12 * (L : ℝ) ^ 2 * (α : ℝ) ^ 36 by ring]
  have hpoly15 : 72 * (144 * 64) ^ 3 * 5184 ^ 2 * 64 ^ 12 * (L : ℝ) ^ 2 * (α : ℝ) ^ 36 < (n : ℝ) ^ 15 :=
    hpoly 15 2 36 (by decide) (72 * (144 * 64) ^ 3 * 5184 ^ 2 * 64 ^ 12) (by norm_num) (by decide) (by decide) (by norm_num)
  linarith

private lemma claim2_case_L_gt (n : ℕ) (G : SimpleGraph (Fin n)) (α : ℕ) (hα : 1 ≤ α)
    (hInd : ∀ I : Finset (Fin n), G.IsIndepSet (I : Set (Fin n)) → I.card ≤ α)
    (_hK4 : Clique4Free G) (hLoc : LocalIndep G) (L : ℕ)
    (hnR : (1 : ℝ) ≤ (n : ℝ)) (_hαR : (1 : ℝ) ≤ (α : ℝ)) (hLR : (1 : ℝ) ≤ (L : ℝ))
    (hpoly : ∀ (p j q : ℕ), 1 ≤ p → ∀ (C : ℝ), 0 ≤ C → 5 * q ≤ 12 * p → 12 * j ≤ q →
      C ^ 12 ≤ (10 ^ 30 : ℝ) ^ q → C * (L : ℝ) ^ j * (α : ℝ) ^ q < (n : ℝ) ^ p)
    (V' : Finset (Fin n)) (outN : Fin n → Finset (Fin n))
    (hout_sub' : ∀ u ∈ V', outN u ⊆ neighbors G V' u)
    (x_nat : ℕ) (hx_nat_30 : 30 ≤ x_nat) (hx_nat_pos : 1 ≤ x_nat)
    (hx_nat_lb : (n : ℝ) / (64 * (α : ℝ) ^ 2) ≤ (x_nat : ℝ))
    (v : Fin n)
    (s t : ℕ) (hs_pos : 1 ≤ s) (ht_le_a : t ≤ α)
    (hst2_n6 : (n : ℝ) ^ 6 / (5184 * 64 ^ 6 * (L : ℝ) * (α : ℝ) ^ 12) ≤ (s : ℝ) * (t : ℝ) ^ 2)
    (S_leaves : Finset (Fin n)) (hS_leaves_card : S_leaves.card = s)
    (hS_sub_V' : S_leaves ⊆ V')
    (T_u : Fin n → Finset (Fin n)) (hTu_card' : ∀ u ∈ S_leaves, (T_u u).card = t)
    (ext₀ : Fin n → Fin n → Finset (Fin n))
    (hext₀_card : ∀ u ∈ S_leaves, ∀ w ∈ T_u u, (ext₀ u w).card = x_nat)
    (hext₀_sub : ∀ u ∈ S_leaves, ∀ w ∈ T_u u,
      ext₀ u w ⊆ (N_tri G v ∩ outN u) ∩ neighbors G Finset.univ w)
    (hext₀_disj : ∀ u ∈ S_leaves, ∀ w₁ ∈ T_u u, ∀ w₂ ∈ T_u u,
      w₁ ≠ w₂ → Disjoint (ext₀ u w₁) (ext₀ u w₂))
    (M : Finset (Fin n × Fin n))
    (hM_mem : ∀ p ∈ M, p.1 ∈ S_leaves ∧ p.2 ∈ T_u p.1)
    (hM_nv : ∀ p ∈ M, p.1 ∈ neighbors G Finset.univ v ∧ p.2 ∈ neighbors G Finset.univ v ∧ G.Adj p.1 p.2)
    (L_set : Finset (Fin n)) (hL_TF : TriangleFree G L_set) (hL4 : ∀ w ∈ L_set, (vTris G v w).card ≤ 4)
    (M_L : Finset (Fin n × Fin n)) (hML_sub : M_L ⊆ M)
    (hML_prop : ∀ p ∈ M_L, x_nat ≤ 3 * (ext₀ p.1 p.2 ∩ L_set).card)
    (hL_maj : s * t ≤ 3 * M_L.card) (hts72 : 72 * s < t) :
    False := by
  classical
  let Nv := neighbors G Finset.univ v
  have hML_cut : ∀ p ∈ M_L, p.1 ∈ Nv ∧ p.2 ∈ Nv ∧ p.1 ≠ p.2 := fun p hp =>
    ⟨(hM_nv p (hML_sub hp)).1, (hM_nv p (hML_sub hp)).2.1, (hM_nv p (hML_sub hp)).2.2.ne⟩
  obtain ⟨U₀, _, hE'_ge⟩ := bipartite_cut_exists Nv M_L hML_cut
  let E' := M_L.filter (fun p => p.1 ∈ U₀ ∧ p.2 ∉ U₀)
  have hE'_lb : s * t ≤ 12 * E'.card := by dsimp [E']; omega
  let U₁ := S_leaves.filter (fun u => t ≤ 24 * (E'.filter (fun p => p.1 = u)).card)
  have hU₁_card_lb : s ≤ 24 * U₁.card := by
    have hsub : E' ⊆ S_leaves.biUnion (fun u => E'.filter (fun p => p.1 = u)) := by
      intro p hp
      exact mem_biUnion.mpr ⟨p.1, (hM_mem p (hML_sub (filter_subset _ _ hp))).1,
        mem_filter.mpr ⟨hp, rfl⟩⟩
    have hsum_e : (E'.card : ℝ) ≤ ∑ u ∈ S_leaves, ((E'.filter (fun p => p.1 = u)).card : ℝ) := by
      exact_mod_cast (card_le_card hsub).trans card_biUnion_le
    have hsplit : ∑ u ∈ S_leaves, ((E'.filter (fun p => p.1 = u)).card : ℝ) =
        ∑ u ∈ U₁, ((E'.filter (fun p => p.1 = u)).card : ℝ) +
        ∑ u ∈ S_leaves \ U₁, ((E'.filter (fun p => p.1 = u)).card : ℝ) := by
      rw [← sum_union disjoint_sdiff_self_right, union_sdiff_of_subset (filter_subset _ _)]
    have h1 : ∑ u ∈ U₁, ((E'.filter (fun p => p.1 = u)).card : ℝ) ≤ (U₁.card : ℝ) * (t : ℝ) := by
      calc
        ∑ u ∈ U₁, ((E'.filter (fun p => p.1 = u)).card : ℝ) ≤ ∑ _u ∈ U₁, (t : ℝ) := by
          refine sum_le_sum fun u hu => ?_
          have hinj : (E'.filter (fun p => p.1 = u)).card ≤ (T_u u).card := by
            refine card_le_card_of_injOn Prod.snd ?_ ?_
            · intro p hp
              obtain ⟨hpE, hpu⟩ := mem_filter.mp hp
              have hpM : p ∈ M := hML_sub ((filter_subset _ _) hpE)
              exact hpu ▸ (hM_mem p hpM).2
            · intro p₁ hp₁ p₂ hp₂ heq
              exact Prod.ext ((mem_filter.mp hp₁).2.trans (mem_filter.mp hp₂).2.symm) heq
          rw [hTu_card' u (filter_subset _ _ hu)] at hinj
          exact_mod_cast hinj
        _ = (U₁.card : ℝ) * (t : ℝ) := by rw [sum_const, nsmul_eq_mul]
    have h2 : ∑ u ∈ S_leaves \ U₁, ((E'.filter (fun p => p.1 = u)).card : ℝ) ≤
        (s : ℝ) * ((t : ℝ) / 24) := by
      have hsle : ((S_leaves \ U₁).card : ℝ) ≤ (s : ℝ) := by
        rw [← hS_leaves_card]
        exact_mod_cast card_le_card sdiff_subset
      calc
        ∑ u ∈ S_leaves \ U₁, ((E'.filter (fun p => p.1 = u)).card : ℝ)
          ≤ ∑ _u ∈ S_leaves \ U₁, ((t : ℝ) / 24) := by
            refine sum_le_sum fun u hu => ?_
            have hnot : ¬ t ≤ 24 * (E'.filter (fun p => p.1 = u)).card := fun hle =>
              (mem_sdiff.mp hu).2 (mem_filter.mpr ⟨(mem_sdiff.mp hu).1, hle⟩)
            have hlt : 24 * ((E'.filter (fun p => p.1 = u)).card : ℝ) < (t : ℝ) := by
              exact_mod_cast Nat.lt_of_not_le hnot
            linarith
        _ = ((S_leaves \ U₁).card : ℝ) * ((t : ℝ) / 24) := by rw [sum_const, nsmul_eq_mul]
        _ ≤ (s : ℝ) * ((t : ℝ) / 24) := by gcongr
    have hE'r : (s : ℝ) * (t : ℝ) / 12 ≤ (E'.card : ℝ) := by
      have : (s : ℝ) * (t : ℝ) ≤ 12 * (E'.card : ℝ) := by exact_mod_cast hE'_lb
      linarith
    have htpos : (0 : ℝ) < (t : ℝ) := by exact_mod_cast (by omega : 0 < t)
    have hle_r : (s : ℝ) ≤ 24 * (U₁.card : ℝ) := by nlinarith
    exact_mod_cast hle_r
  have hU₁_pos : 1 ≤ U₁.card := by omega
  have hU₁_le_s : U₁.card ≤ s := by
    rw [← hS_leaves_card]; exact card_le_card (filter_subset _ _)
  have hU₁_sub_U₀ : U₁ ⊆ U₀ := by
    intro u hu
    have h24 : t ≤ 24 * (E'.filter (fun p => p.1 = u)).card := (mem_filter.mp hu).2
    obtain ⟨p, hp⟩ := card_pos.mp (by omega : 0 < (E'.filter (fun p => p.1 = u)).card)
    have hpu := (mem_filter.mp hp).2
    have hpE := (mem_filter.mp hp).1
    exact hpu ▸ (mem_filter.mp hpE).2.1
  let W₁ := Nv \ U₀
  let A (u w : Fin n) : Finset (Fin n) := if (u, w) ∈ E' then ext₀ u w ∩ L_set else ∅
  let T_grid : ℝ := (t : ℝ) / 72
  have hGrid := grid_lemma G α hα hInd U₁ W₁ A L_set hL_TF
    (fun u _ w _ => by
      dsimp [A]
      split_ifs
      · exact inter_subset_right
      · exact empty_subset _)
    (fun z hz => by
      have hinj : ((U₁ ×ˢ W₁).filter (fun p => z ∈ A p.1 p.2)).card ≤ (vTris G v z).card := by
        refine card_le_card_of_injOn (fun p => ({p.1, p.2} : Finset (Fin n))) ?_ ?_
        · intro p hp
          obtain ⟨_, hzp⟩ := mem_filter.mp hp
          have hpE : p ∈ E' := by
            by_contra hnot
            have hAe : A p.1 p.2 = ∅ := by dsimp [A]; rw [if_neg hnot]
            rw [hAe] at hzp; simp at hzp
          have hzp' : z ∈ ext₀ p.1 p.2 ∩ L_set := by
            dsimp [A] at hzp; rwa [if_pos hpE] at hzp
          have hpM : p ∈ M := hML_sub ((filter_subset _ _) hpE)
          obtain ⟨hu, hw⟩ := hM_mem p hpM
          have hsub := hext₀_sub p.1 hu p.2 hw (mem_inter.mp hzp').1
          have hz_out := (mem_inter.mp (mem_inter.mp hsub).1).2
          have hz_w := (mem_neighbors.mp (mem_inter.mp hsub).2).2
          have hz_u : G.Adj p.1 z := (mem_neighbors.mp (hout_sub' p.1 (hS_sub_V' hu) hz_out)).2
          refine mem_vTris.mpr ⟨mem_edgesIn.mpr ⟨?_, card_pair (hM_nv p hpM).2.2.ne, ?_⟩, ?_⟩
          · intro a ha; simp only [mem_insert, mem_singleton] at ha
            rcases ha with rfl | rfl; exact (hM_nv p hpM).1; exact (hM_nv p hpM).2.1
          · intro a ha b hb hab
            simp only [coe_insert, coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
            rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
            · exact False.elim (hab rfl)
            · exact (hM_nv p hpM).2.2
            · exact (hM_nv p hpM).2.2.symm
            · exact False.elim (hab rfl)
          · intro a ha; simp only [mem_insert, mem_singleton] at ha
            rcases ha with rfl | rfl; exact hz_u.symm; exact hz_w.symm
        · intro p₁ hp₁ p₂ hp₂ heq
          have hp1 := mem_product.mp (mem_filter.mp hp₁).1
          have hp2 := mem_product.mp (mem_filter.mp hp₂).1
          have hu1 : p₁.1 ∈ U₀ := hU₁_sub_U₀ hp1.1
          have hw1 : p₁.2 ∉ U₀ := (mem_sdiff.mp hp1.2).2
          have hu2 : p₂.1 ∈ U₀ := hU₁_sub_U₀ hp2.1
          have hw2 : p₂.2 ∉ U₀ := (mem_sdiff.mp hp2.2).2
          dsimp only at heq
          have hm1 : p₁.1 ∈ ({p₂.1, p₂.2} : Finset (Fin n)) := by rw [← heq]; simp
          have hm2 : p₁.2 ∈ ({p₂.1, p₂.2} : Finset (Fin n)) := by rw [← heq]; simp
          simp only [mem_insert, mem_singleton] at hm1 hm2
          have hfst : p₁.1 = p₂.1 := by
            rcases hm1 with h | h
            · exact h
            · exact False.elim (hw2 (h ▸ hu1))
          have hsnd : p₁.2 = p₂.2 := by
            rcases hm2 with h | h
            · exact False.elim (hw1 (h ▸ hu2))
            · exact h
          exact Prod.ext hfst hsnd
      exact hinj.trans (hL4 z hz))
    x_nat hx_nat_pos
    (fun u hu w _ => by
      dsimp [A]
      split_ifs with hE'
      · have hpM : (u, w) ∈ M := hML_sub ((filter_subset _ _) hE')
        have hmem := hM_mem (u, w) hpM
        calc
          (ext₀ u w ∩ L_set).card ≤ (ext₀ u w).card := card_le_card inter_subset_left
          _ = x_nat := hext₀_card u hmem.1 w hmem.2
      · simp)
    T_grid
    (by
      have h1 : (U₁.card : ℝ) ≤ (s : ℝ) := by exact_mod_cast hU₁_le_s
      have h2 : 72 * (s : ℝ) < (t : ℝ) := by exact_mod_cast hts72
      dsimp [T_grid]; linarith)
    hU₁_pos
    (fun u hu w₁ hw₁ w₂ hw₂ hne => by
      dsimp [A]
      split_ifs with h1 h2
      · have hm1 := hM_mem (u, w₁) (hML_sub ((filter_subset _ _) h1))
        have hm2 := hM_mem (u, w₂) (hML_sub ((filter_subset _ _) h2))
        exact Disjoint.mono inter_subset_left inter_subset_left (hext₀_disj u hm1.1 w₁ hm1.2 w₂ hm2.2 hne)
      · simp
      · simp
      · simp)
    (fun u hu => by
      let W_u := W₁.filter (fun w => (u, w) ∈ E')
      have hW_u_card : (E'.filter (fun p => p.1 = u)).card = W_u.card := by
        refine card_bij (fun p _ => p.2) ?_ ?_ ?_
        · intro p hp
          obtain ⟨hpE, hpu⟩ := mem_filter.mp hp
          have hpML : p ∈ M_L := (filter_subset _ _) hpE
          have hp2_nv := (hML_cut p hpML).2.1
          have hp2_not := (mem_filter.mp hpE).2.2
          have hp_eq : (u, p.2) = p := Prod.ext hpu.symm rfl
          exact mem_filter.mpr ⟨mem_sdiff.mpr ⟨hp2_nv, hp2_not⟩, hp_eq ▸ hpE⟩
        · intro p₁ hp₁ p₂ hp₂ heq
          exact Prod.ext ((mem_filter.mp hp₁).2.trans (mem_filter.mp hp₂).2.symm) heq
        · intro w hw
          obtain ⟨_, hwE⟩ := mem_filter.mp hw
          exact ⟨(u, w), mem_filter.mpr ⟨hwE, rfl⟩, rfl⟩
      have hWu_ge : (t : ℝ) / 24 ≤ (W_u.card : ℝ) := by
        have h24 : t ≤ 24 * (E'.filter (fun p => p.1 = u)).card := (mem_filter.mp hu).2
        rw [hW_u_card] at h24
        have h24r : (t : ℝ) ≤ 24 * (W_u.card : ℝ) := by exact_mod_cast h24
        linarith only [h24r]
      have hsub_u : W_u.biUnion (A u) ⊆ W₁.biUnion (A u) :=
        biUnion_subset_biUnion_of_subset_left _ (filter_subset _ _)
      have hdisj_u : Set.PairwiseDisjoint (W_u : Set (Fin n)) (A u) := by
        intro w₁ hw₁ w₂ hw₂ hne
        change Disjoint _ _
        rw [disjoint_left]
        intro z hz10 hz20
        have hw1E := (mem_filter.mp hw₁).2
        have hw2E := (mem_filter.mp hw₂).2
        have hm1 := hM_mem (u, w₁) (hML_sub ((filter_subset _ _) hw1E))
        have hm2 := hM_mem (u, w₂) (hML_sub ((filter_subset _ _) hw2E))
        have hz1 : z ∈ ext₀ u w₁ := by
          dsimp [A] at hz10; rw [if_pos hw1E] at hz10; exact (mem_inter.mp hz10).1
        have hz2 : z ∈ ext₀ u w₂ := by
          dsimp [A] at hz20; rw [if_pos hw2E] at hz20; exact (mem_inter.mp hz20).1
        exact (disjoint_left.mp (hext₀_disj u hm1.1 w₁ hm1.2 w₂ hm2.2 hne)) hz1 hz2
      have hsum_u : (W_u.card : ℝ) * ((x_nat : ℝ) / 3) ≤ ((W_u.biUnion (A u)).card : ℝ) := by
        have h1 : (W_u.biUnion (A u)).card = ∑ w ∈ W_u, (A u w).card := card_biUnion hdisj_u
        have h1r : ((W_u.biUnion (A u)).card : ℝ) = ∑ w ∈ W_u, ((A u w).card : ℝ) := by
          exact_mod_cast h1
        rw [h1r, ← nsmul_eq_mul, ← sum_const]
        refine sum_le_sum fun w hw => ?_
        have hwE := (mem_filter.mp hw).2
        have hwML := (filter_subset _ _) hwE
        have h3 : (x_nat : ℝ) ≤ 3 * ((ext₀ u w ∩ L_set).card : ℝ) := by
          exact_mod_cast hML_prop (u, w) hwML
        have hAe : A u w = ext₀ u w ∩ L_set := by dsimp [A]; rw [if_pos hwE]
        rw [hAe]; linarith
      have hle_bi : ((W_u.biUnion (A u)).card : ℝ) ≤ ((W₁.biUnion (A u)).card : ℝ) := by
        exact_mod_cast card_le_card hsub_u
      calc
        T_grid * (x_nat : ℝ) = ((t : ℝ) / 24) * ((x_nat : ℝ) / 3) := by dsimp [T_grid]; ring
        _ ≤ (W_u.card : ℝ) * ((x_nat : ℝ) / 3) := by gcongr
        _ ≤ ((W_u.biUnion (A u)).card : ℝ) := hsum_u
        _ ≤ ((W₁.biUnion (A u)).card : ℝ) := hle_bi)
    (by
      have ht72 : 72 < t := by omega
      have ht73 : (73 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht72
      have hx30 : (30 : ℝ) ≤ (x_nat : ℝ) := by exact_mod_cast hx_nat_30
      dsimp [T_grid]; nlinarith)
    (fun u₁ hu₁ u₂ hu₂ w₁ hw₁ w₂ hw₂ hnu hnw z₁ hz₁ z₂ hz₂ => by
      dsimp [A] at hz₁ hz₂
      split_ifs at hz₁ with h1
      · split_ifs at hz₂ with h2
        · have hp1M : (u₁, w₁) ∈ M := hML_sub ((filter_subset _ _) h1)
          have hp2M : (u₂, w₂) ∈ M := hML_sub ((filter_subset _ _) h2)
          obtain ⟨hu1S, hw1T⟩ := hM_mem (u₁, w₁) hp1M
          obtain ⟨hu2S, hw2T⟩ := hM_mem (u₂, w₂) hp2M
          have hz1_sub := hext₀_sub u₁ hu1S w₁ hw1T (mem_inter.mp hz₁).1
          have hz2_sub := hext₀_sub u₂ hu2S w₂ hw2T (mem_inter.mp hz₂).1
          have hz1N : z₁ ∈ N_tri G v := (mem_inter.mp (mem_inter.mp hz1_sub).1).1
          have hz2N : z₂ ∈ N_tri G v := (mem_inter.mp (mem_inter.mp hz2_sub).1).1
          have hz1_u : G.Adj u₁ z₁ := (mem_neighbors.mp (hout_sub' u₁ (hS_sub_V' hu1S)
            (mem_inter.mp (mem_inter.mp hz1_sub).1).2)).2
          have hz1_w : G.Adj w₁ z₁ := (mem_neighbors.mp (mem_inter.mp hz1_sub).2).2
          have hz2_u : G.Adj u₂ z₂ := (mem_neighbors.mp (hout_sub' u₂ (hS_sub_V' hu2S)
            (mem_inter.mp (mem_inter.mp hz2_sub).1).2)).2
          have hz2_w : G.Adj w₂ z₂ := (mem_neighbors.mp (mem_inter.mp hz2_sub).2).2
          have he1 : ({u₁, w₁} : Finset (Fin n)) ∈ vTris G v z₁ := by
            refine mem_vTris.mpr ⟨mem_edgesIn.mpr ⟨?_, card_pair (hM_nv (u₁, w₁) hp1M).2.2.ne, ?_⟩, ?_⟩
            · intro a ha; simp only [mem_insert, mem_singleton] at ha
              rcases ha with ha | ha
              · rw [ha]; exact (hM_nv (u₁, w₁) hp1M).1
              · rw [ha]; exact (hM_nv (u₁, w₁) hp1M).2.1
            · intro a ha b hb hab
              simp only [coe_insert, coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
              rcases ha with ha | ha <;> rcases hb with hb | hb
              · exact False.elim (hab (ha.trans hb.symm))
              · rw [ha, hb]; exact (hM_nv (u₁, w₁) hp1M).2.2
              · rw [ha, hb]; exact (hM_nv (u₁, w₁) hp1M).2.2.symm
              · exact False.elim (hab (ha.trans hb.symm))
            · intro a ha; simp only [mem_insert, mem_singleton] at ha
              rcases ha with ha | ha
              · rw [ha]; exact hz1_u.symm
              · rw [ha]; exact hz1_w.symm
          have he2 : ({u₂, w₂} : Finset (Fin n)) ∈ vTris G v z₂ := by
            refine mem_vTris.mpr ⟨mem_edgesIn.mpr ⟨?_, card_pair (hM_nv (u₂, w₂) hp2M).2.2.ne, ?_⟩, ?_⟩
            · intro a ha; simp only [mem_insert, mem_singleton] at ha
              rcases ha with ha | ha
              · rw [ha]; exact (hM_nv (u₂, w₂) hp2M).1
              · rw [ha]; exact (hM_nv (u₂, w₂) hp2M).2.1
            · intro a ha b hb hab
              simp only [coe_insert, coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
              rcases ha with ha | ha <;> rcases hb with hb | hb
              · exact False.elim (hab (ha.trans hb.symm))
              · rw [ha, hb]; exact (hM_nv (u₂, w₂) hp2M).2.2
              · rw [ha, hb]; exact (hM_nv (u₂, w₂) hp2M).2.2.symm
              · exact False.elim (hab (ha.trans hb.symm))
            · intro a ha; simp only [mem_insert, mem_singleton] at ha
              rcases ha with ha | ha
              · rw [ha]; exact hz2_u.symm
              · rw [ha]; exact hz2_w.symm
          have hdisj : Disjoint ({u₁, w₁} : Finset (Fin n)) ({u₂, w₂} : Finset (Fin n)) := by
            rw [disjoint_left]
            intro a ha hb
            have hu10 : u₁ ∈ U₀ := hU₁_sub_U₀ hu₁
            have hu20 : u₂ ∈ U₀ := hU₁_sub_U₀ hu₂
            have hw10 : w₁ ∉ U₀ := (mem_sdiff.mp hw₁).2
            have hw20 : w₂ ∉ U₀ := (mem_sdiff.mp hw₂).2
            simp only [mem_insert, mem_singleton] at ha hb
            rcases ha with ha | ha <;> rcases hb with hb | hb
            · exact hnu (ha.symm.trans hb)
            · exact hw20 (hb ▸ ha ▸ hu10)
            · exact hw10 (ha ▸ hb ▸ hu20)
            · exact hnw (ha.symm.trans hb)
          exact no_adj_disjoint_vTris G hLoc hz1N hz2N he1 he2 hdisj
        · simp at hz₂
      · simp at hz₁)
  have hU₁_geR : (s : ℝ) / 24 ≤ (U₁.card : ℝ) := by
    have : (s : ℝ) ≤ 24 * (U₁.card : ℝ) := by exact_mod_cast hU₁_card_lb
    linarith
  have htR_le_a : (t : ℝ) ≤ (α : ℝ) := by exact_mod_cast ht_le_a
  have hx_nat_nn : 0 ≤ (x_nat : ℝ) := by positivity
  rcases hGrid with hD1 | hD2 | hD3 | hD4
  · have h1 : ((s : ℝ) / 24) * ((t : ℝ) / 72) * ((n : ℝ) / (64 * (α : ℝ) ^ 2)) ≤ 96 * (α : ℝ) := by
      calc
        ((s : ℝ) / 24) * ((t : ℝ) / 72) * ((n : ℝ) / (64 * (α : ℝ) ^ 2))
          ≤ (U₁.card : ℝ) * T_grid * (x_nat : ℝ) := by dsimp [T_grid]; gcongr
        _ ≤ 96 * (α : ℝ) := hD1
    have h2 : (n : ℝ) ^ 6 / (5184 * 64 ^ 6 * (L : ℝ) * (α : ℝ) ^ 12) ≤ (s : ℝ) * (t : ℝ) * (α : ℝ) := by
      calc
        (n : ℝ) ^ 6 / (5184 * 64 ^ 6 * (L : ℝ) * (α : ℝ) ^ 12)
          ≤ (s : ℝ) * (t : ℝ) ^ 2 := hst2_n6
        _ = (s : ℝ) * (t : ℝ) * (t : ℝ) := by ring
        _ ≤ (s : ℝ) * (t : ℝ) * (α : ℝ) := by gcongr
    have h3 : (n : ℝ) ^ 7 / (24 * 72 * 64 * 5184 * 64 ^ 6 * (L : ℝ) * (α : ℝ) ^ 15) ≤ 96 * (α : ℝ) := by
      have heq : (n : ℝ) ^ 7 / (24 * 72 * 64 * 5184 * 64 ^ 6 * (L : ℝ) * (α : ℝ) ^ 15) =
          (((n : ℝ) ^ 6 / (5184 * 64 ^ 6 * (L : ℝ) * (α : ℝ) ^ 12)) / (24 * 72 * (α : ℝ))) *
            ((n : ℝ) / (64 * (α : ℝ) ^ 2)) := by
        have hα0 : (α : ℝ) ≠ 0 := by positivity
        field_simp
      have hst_ge : (n : ℝ) ^ 6 / (5184 * 64 ^ 6 * (L : ℝ) * (α : ℝ) ^ 12) / (24 * 72 * (α : ℝ)) ≤
          ((s : ℝ) / 24) * ((t : ℝ) / 72) := by
        rw [div_le_iff₀ (by positivity)]
        linarith [h2, show ((s : ℝ) / 24) * ((t : ℝ) / 72) * (24 * 72 * (α : ℝ)) =
          (s : ℝ) * (t : ℝ) * (α : ℝ) by ring]
      calc
        (n : ℝ) ^ 7 / (24 * 72 * 64 * 5184 * 64 ^ 6 * (L : ℝ) * (α : ℝ) ^ 15)
          = (((n : ℝ) ^ 6 / (5184 * 64 ^ 6 * (L : ℝ) * (α : ℝ) ^ 12)) / (24 * 72 * (α : ℝ))) *
              ((n : ℝ) / (64 * (α : ℝ) ^ 2)) := heq
        _ ≤ ((s : ℝ) / 24) * ((t : ℝ) / 72) * ((n : ℝ) / (64 * (α : ℝ) ^ 2)) := by gcongr
        _ ≤ 96 * (α : ℝ) := h1
    rw [div_le_iff₀ (by positivity)] at h3
    have hcontra7 : (n : ℝ) ^ 7 ≤
        96 * 24 * 72 * 64 * 5184 * 64 ^ 6 * (L : ℝ) * (α : ℝ) ^ 16 := by
      linarith [show (96 * (α : ℝ)) * (24 * 72 * 64 * 5184 * 64 ^ 6 * (L : ℝ) * (α : ℝ) ^ 15) =
        96 * 24 * 72 * 64 * 5184 * 64 ^ 6 * (L : ℝ) * (α : ℝ) ^ 16 by ring]
    have hpoly7 : 96 * 24 * 72 * 64 * 5184 * 64 ^ 6 * (L : ℝ) * (α : ℝ) ^ 16 < (n : ℝ) ^ 7 := by
      simpa using hpoly 7 1 16 (by decide) (96 * 24 * 72 * 64 * 5184 * 64 ^ 6) (by norm_num) (by decide) (by decide) (by norm_num)
    linarith
  · have h1 : ((s : ℝ) / 24) ^ 2 * ((t : ℝ) / 72) ^ 3 * ((n : ℝ) / (64 * (α : ℝ) ^ 2)) ≤
        56623104 * (α : ℝ) ^ 4 := by
      calc
        ((s : ℝ) / 24) ^ 2 * ((t : ℝ) / 72) ^ 3 * ((n : ℝ) / (64 * (α : ℝ) ^ 2))
          ≤ (U₁.card : ℝ) ^ 2 * T_grid ^ 3 * (x_nat : ℝ) := by dsimp [T_grid]; gcongr
        _ ≤ 56623104 * (α : ℝ) ^ 4 := hD2
    have hst2_sq : ((n : ℝ) ^ 6 / (5184 * 64 ^ 6 * (L : ℝ) * (α : ℝ) ^ 12)) ^ 2 ≤
        (s : ℝ) ^ 2 * (t : ℝ) ^ 3 * (α : ℝ) := by
      have hsq := pow_le_pow_left₀ (by positivity) hst2_n6 2
      calc
        ((n : ℝ) ^ 6 / (5184 * 64 ^ 6 * (L : ℝ) * (α : ℝ) ^ 12)) ^ 2 ≤ ((s : ℝ) * (t : ℝ) ^ 2) ^ 2 := hsq
        _ = (s : ℝ) ^ 2 * (t : ℝ) ^ 3 * (t : ℝ) := by ring
        _ ≤ (s : ℝ) ^ 2 * (t : ℝ) ^ 3 * (α : ℝ) := by gcongr
    have h2 : (n : ℝ) ^ 13 / (24 ^ 2 * 72 ^ 3 * 64 * 5184 ^ 2 * 64 ^ 12 * (L : ℝ) ^ 2 * (α : ℝ) ^ 27) ≤
        56623104 * (α : ℝ) ^ 4 := by
      have hle_lhs : ((n : ℝ) ^ 6 / (5184 * 64 ^ 6 * (L : ℝ) * (α : ℝ) ^ 12)) ^ 2 /
          (24 ^ 2 * 72 ^ 3 * (α : ℝ)) ≤ ((s : ℝ) / 24) ^ 2 * ((t : ℝ) / 72) ^ 3 := by
        rw [div_le_iff₀ (by positivity)]
        linarith [hst2_sq, show ((s : ℝ) / 24) ^ 2 * ((t : ℝ) / 72) ^ 3 * (24 ^ 2 * 72 ^ 3 * (α : ℝ)) =
          (s : ℝ) ^ 2 * (t : ℝ) ^ 3 * (α : ℝ) by ring]
      have heq : (n : ℝ) ^ 13 / (24 ^ 2 * 72 ^ 3 * 64 * 5184 ^ 2 * 64 ^ 12 * (L : ℝ) ^ 2 * (α : ℝ) ^ 27) =
          (((n : ℝ) ^ 6 / (5184 * 64 ^ 6 * (L : ℝ) * (α : ℝ) ^ 12)) ^ 2 / (24 ^ 2 * 72 ^ 3 * (α : ℝ))) *
            ((n : ℝ) / (64 * (α : ℝ) ^ 2)) := by
        have hα0 : (α : ℝ) ≠ 0 := by positivity
        field_simp
      rw [heq]
      calc
        (((n : ℝ) ^ 6 / (5184 * 64 ^ 6 * (L : ℝ) * (α : ℝ) ^ 12)) ^ 2 / (24 ^ 2 * 72 ^ 3 * (α : ℝ))) *
            ((n : ℝ) / (64 * (α : ℝ) ^ 2))
          ≤ ((s : ℝ) / 24) ^ 2 * ((t : ℝ) / 72) ^ 3 * ((n : ℝ) / (64 * (α : ℝ) ^ 2)) := by gcongr
        _ ≤ 56623104 * (α : ℝ) ^ 4 := h1
    rw [div_le_iff₀ (by positivity)] at h2
    have hcontra13 : (n : ℝ) ^ 13 ≤
        56623104 * 24 ^ 2 * 72 ^ 3 * 64 * 5184 ^ 2 * 64 ^ 12 * (L : ℝ) ^ 2 * (α : ℝ) ^ 31 := by
      linarith [show (56623104 * (α : ℝ) ^ 4) *
        (24 ^ 2 * 72 ^ 3 * 64 * 5184 ^ 2 * 64 ^ 12 * (L : ℝ) ^ 2 * (α : ℝ) ^ 27) =
        56623104 * 24 ^ 2 * 72 ^ 3 * 64 * 5184 ^ 2 * 64 ^ 12 * (L : ℝ) ^ 2 * (α : ℝ) ^ 31 by ring]
    have hpoly13 : 56623104 * 24 ^ 2 * 72 ^ 3 * 64 * 5184 ^ 2 * 64 ^ 12 * (L : ℝ) ^ 2 * (α : ℝ) ^ 31 <
        (n : ℝ) ^ 13 :=
      hpoly 13 2 31 (by decide) (56623104 * 24 ^ 2 * 72 ^ 3 * 64 * 5184 ^ 2 * 64 ^ 12)
        (by norm_num) (by decide) (by decide) (by norm_num)
    linarith
  · have h1 : ((s : ℝ) / 24) ^ 2 * ((t : ℝ) / 72) * ((n : ℝ) / (64 * (α : ℝ) ^ 2)) ≤
        3072 * (α : ℝ) ^ 2 := by
      calc
        ((s : ℝ) / 24) ^ 2 * ((t : ℝ) / 72) * ((n : ℝ) / (64 * (α : ℝ) ^ 2))
          ≤ (U₁.card : ℝ) ^ 2 * T_grid * (x_nat : ℝ) := by dsimp [T_grid]; gcongr
        _ ≤ 3072 * (α : ℝ) ^ 2 := hD3
    have hst2_sq : ((n : ℝ) ^ 6 / (5184 * 64 ^ 6 * (L : ℝ) * (α : ℝ) ^ 12)) ^ 2 ≤
        (s : ℝ) ^ 2 * (t : ℝ) * (α : ℝ) ^ 3 := by
      have hsq := pow_le_pow_left₀ (by positivity) hst2_n6 2
      calc
        ((n : ℝ) ^ 6 / (5184 * 64 ^ 6 * (L : ℝ) * (α : ℝ) ^ 12)) ^ 2 ≤ ((s : ℝ) * (t : ℝ) ^ 2) ^ 2 := hsq
        _ = (s : ℝ) ^ 2 * (t : ℝ) * (t : ℝ) ^ 3 := by ring
        _ ≤ (s : ℝ) ^ 2 * (t : ℝ) * (α : ℝ) ^ 3 := by gcongr
    have h2 : (n : ℝ) ^ 13 / (24 ^ 2 * 72 * 64 * 5184 ^ 2 * 64 ^ 12 * (L : ℝ) ^ 2 * (α : ℝ) ^ 29) ≤
        3072 * (α : ℝ) ^ 2 := by
      have hle_lhs : ((n : ℝ) ^ 6 / (5184 * 64 ^ 6 * (L : ℝ) * (α : ℝ) ^ 12)) ^ 2 /
          (24 ^ 2 * 72 * (α : ℝ) ^ 3) ≤ ((s : ℝ) / 24) ^ 2 * ((t : ℝ) / 72) := by
        rw [div_le_iff₀ (by positivity)]
        linarith [hst2_sq, show ((s : ℝ) / 24) ^ 2 * ((t : ℝ) / 72) * (24 ^ 2 * 72 * (α : ℝ) ^ 3) =
          (s : ℝ) ^ 2 * (t : ℝ) * (α : ℝ) ^ 3 by ring]
      have heq : (n : ℝ) ^ 13 / (24 ^ 2 * 72 * 64 * 5184 ^ 2 * 64 ^ 12 * (L : ℝ) ^ 2 * (α : ℝ) ^ 29) =
          (((n : ℝ) ^ 6 / (5184 * 64 ^ 6 * (L : ℝ) * (α : ℝ) ^ 12)) ^ 2 / (24 ^ 2 * 72 * (α : ℝ) ^ 3)) *
            ((n : ℝ) / (64 * (α : ℝ) ^ 2)) := by
        have hα0 : (α : ℝ) ≠ 0 := by positivity
        field_simp
      rw [heq]
      calc
        (((n : ℝ) ^ 6 / (5184 * 64 ^ 6 * (L : ℝ) * (α : ℝ) ^ 12)) ^ 2 / (24 ^ 2 * 72 * (α : ℝ) ^ 3)) *
            ((n : ℝ) / (64 * (α : ℝ) ^ 2))
          ≤ ((s : ℝ) / 24) ^ 2 * ((t : ℝ) / 72) * ((n : ℝ) / (64 * (α : ℝ) ^ 2)) := by gcongr
        _ ≤ 3072 * (α : ℝ) ^ 2 := h1
    rw [div_le_iff₀ (by positivity)] at h2
    have hcontra13 : (n : ℝ) ^ 13 ≤
        3072 * 24 ^ 2 * 72 * 64 * 5184 ^ 2 * 64 ^ 12 * (L : ℝ) ^ 2 * (α : ℝ) ^ 31 := by
      linarith [show (3072 * (α : ℝ) ^ 2) *
        (24 ^ 2 * 72 * 64 * 5184 ^ 2 * 64 ^ 12 * (L : ℝ) ^ 2 * (α : ℝ) ^ 29) =
        3072 * 24 ^ 2 * 72 * 64 * 5184 ^ 2 * 64 ^ 12 * (L : ℝ) ^ 2 * (α : ℝ) ^ 31 by ring]
    have hpoly13 : 3072 * 24 ^ 2 * 72 * 64 * 5184 ^ 2 * 64 ^ 12 * (L : ℝ) ^ 2 * (α : ℝ) ^ 31 <
        (n : ℝ) ^ 13 :=
      hpoly 13 2 31 (by decide) (3072 * 24 ^ 2 * 72 * 64 * 5184 ^ 2 * 64 ^ 12)
        (by norm_num) (by decide) (by decide) (by norm_num)
    linarith
  · have h1 : ((s : ℝ) / 24) ^ 3 * ((t : ℝ) / 72) ^ 3 * ((n : ℝ) / (64 * (α : ℝ) ^ 2)) ^ 2 ≤
        9663676416 * (α : ℝ) ^ 5 := by
      calc
        ((s : ℝ) / 24) ^ 3 * ((t : ℝ) / 72) ^ 3 * ((n : ℝ) / (64 * (α : ℝ) ^ 2)) ^ 2
          ≤ (U₁.card : ℝ) ^ 3 * T_grid ^ 3 * (x_nat : ℝ) ^ 2 := by dsimp [T_grid]; gcongr
        _ ≤ 9663676416 * (α : ℝ) ^ 5 := hD4
    have hst2_cu : ((n : ℝ) ^ 6 / (5184 * 64 ^ 6 * (L : ℝ) * (α : ℝ) ^ 12)) ^ 3 ≤
        (s : ℝ) ^ 3 * (t : ℝ) ^ 3 * (α : ℝ) ^ 3 := by
      have hcu := pow_le_pow_left₀ (by positivity) hst2_n6 3
      calc
        ((n : ℝ) ^ 6 / (5184 * 64 ^ 6 * (L : ℝ) * (α : ℝ) ^ 12)) ^ 3 ≤ ((s : ℝ) * (t : ℝ) ^ 2) ^ 3 := hcu
        _ = (s : ℝ) ^ 3 * (t : ℝ) ^ 3 * (t : ℝ) ^ 3 := by ring
        _ ≤ (s : ℝ) ^ 3 * (t : ℝ) ^ 3 * (α : ℝ) ^ 3 := by gcongr
    have h2 : (n : ℝ) ^ 20 / (24 ^ 3 * 72 ^ 3 * 64 ^ 2 * 5184 ^ 3 * 64 ^ 18 * (L : ℝ) ^ 3 * (α : ℝ) ^ 43) ≤
        9663676416 * (α : ℝ) ^ 5 := by
      have hle_lhs : ((n : ℝ) ^ 6 / (5184 * 64 ^ 6 * (L : ℝ) * (α : ℝ) ^ 12)) ^ 3 /
          (24 ^ 3 * 72 ^ 3 * (α : ℝ) ^ 3) ≤ ((s : ℝ) / 24) ^ 3 * ((t : ℝ) / 72) ^ 3 := by
        rw [div_le_iff₀ (by positivity)]
        linarith [hst2_cu, show ((s : ℝ) / 24) ^ 3 * ((t : ℝ) / 72) ^ 3 * (24 ^ 3 * 72 ^ 3 * (α : ℝ) ^ 3) =
          (s : ℝ) ^ 3 * (t : ℝ) ^ 3 * (α : ℝ) ^ 3 by ring]
      have heq : (n : ℝ) ^ 20 / (24 ^ 3 * 72 ^ 3 * 64 ^ 2 * 5184 ^ 3 * 64 ^ 18 * (L : ℝ) ^ 3 * (α : ℝ) ^ 43) =
          (((n : ℝ) ^ 6 / (5184 * 64 ^ 6 * (L : ℝ) * (α : ℝ) ^ 12)) ^ 3 / (24 ^ 3 * 72 ^ 3 * (α : ℝ) ^ 3)) *
            ((n : ℝ) / (64 * (α : ℝ) ^ 2)) ^ 2 := by
        have hα0 : (α : ℝ) ≠ 0 := by positivity
        field_simp
      rw [heq]
      calc
        (((n : ℝ) ^ 6 / (5184 * 64 ^ 6 * (L : ℝ) * (α : ℝ) ^ 12)) ^ 3 / (24 ^ 3 * 72 ^ 3 * (α : ℝ) ^ 3)) *
            ((n : ℝ) / (64 * (α : ℝ) ^ 2)) ^ 2
          ≤ ((s : ℝ) / 24) ^ 3 * ((t : ℝ) / 72) ^ 3 * ((n : ℝ) / (64 * (α : ℝ) ^ 2)) ^ 2 := by gcongr
        _ ≤ 9663676416 * (α : ℝ) ^ 5 := h1
    rw [div_le_iff₀ (by positivity)] at h2
    have hcontra20 : (n : ℝ) ^ 20 ≤
        9663676416 * 24 ^ 3 * 72 ^ 3 * 64 ^ 2 * 5184 ^ 3 * 64 ^ 18 * (L : ℝ) ^ 3 * (α : ℝ) ^ 48 := by
      linarith [show (9663676416 * (α : ℝ) ^ 5) *
        (24 ^ 3 * 72 ^ 3 * 64 ^ 2 * 5184 ^ 3 * 64 ^ 18 * (L : ℝ) ^ 3 * (α : ℝ) ^ 43) =
        9663676416 * 24 ^ 3 * 72 ^ 3 * 64 ^ 2 * 5184 ^ 3 * 64 ^ 18 * (L : ℝ) ^ 3 * (α : ℝ) ^ 48 by ring]
    have hpoly20 : 9663676416 * 24 ^ 3 * 72 ^ 3 * 64 ^ 2 * 5184 ^ 3 * 64 ^ 18 * (L : ℝ) ^ 3 * (α : ℝ) ^ 48 <
        (n : ℝ) ^ 20 :=
      hpoly 20 3 48 (by decide) (9663676416 * 24 ^ 3 * 72 ^ 3 * 64 ^ 2 * 5184 ^ 3 * 64 ^ 18)
        (by norm_num) (by decide) (by decide) (by norm_num)
    linarith

private lemma claim2_case_I (n : ℕ) (G : SimpleGraph (Fin n)) (α : ℕ) (hα : 1 ≤ α)
    (hInd : ∀ I : Finset (Fin n), G.IsIndepSet (I : Set (Fin n)) → I.card ≤ α)
    (L : ℕ)
    (_hnR : (1 : ℝ) ≤ (n : ℝ)) (hαR : (1 : ℝ) ≤ (α : ℝ)) (hLR : (1 : ℝ) ≤ (L : ℝ))
    (hpoly : ∀ (p j q : ℕ), 1 ≤ p → ∀ (C : ℝ), 0 ≤ C → 5 * q ≤ 12 * p → 12 * j ≤ q →
      C ^ 12 ≤ (10 ^ 30 : ℝ) ^ q → C * (L : ℝ) ^ j * (α : ℝ) ^ q < (n : ℝ) ^ p)
    (V' : Finset (Fin n)) (outN : Fin n → Finset (Fin n))
    (hout_sub' : ∀ u ∈ V', outN u ⊆ neighbors G V' u)
    (x_nat : ℕ) (hx_nat_30 : 30 ≤ x_nat) (hx_nat_pos : 1 ≤ x_nat)
    (hx_nat_lb : (n : ℝ) / (64 * (α : ℝ) ^ 2) ≤ (x_nat : ℝ))
    (v : Fin n)
    (s t : ℕ) (hs_pos : 1 ≤ s) (ht_ge2 : 2 ≤ t)
    (hst2_n6 : (n : ℝ) ^ 6 / (5184 * 64 ^ 6 * (L : ℝ) * (α : ℝ) ^ 12) ≤ (s : ℝ) * (t : ℝ) ^ 2)
    (S_leaves : Finset (Fin n)) (hS_leaves_card : S_leaves.card = s)
    (hleaf_prop : ∀ u ∈ S_leaves, u ∈ neighbors G V' v ∧ t ≤ (outN v ∩ outN u).card)
    (T_u : Fin n → Finset (Fin n))
    (ext₀ : Fin n → Fin n → Finset (Fin n))
    (hext₀_sub : ∀ u ∈ S_leaves, ∀ w ∈ T_u u,
      ext₀ u w ⊆ (N_tri G v ∩ outN u) ∩ neighbors G Finset.univ w)
    (hext₀_disj : ∀ u ∈ S_leaves, ∀ w₁ ∈ T_u u, ∀ w₂ ∈ T_u u,
      w₁ ≠ w₂ → Disjoint (ext₀ u w₁) (ext₀ u w₂))
    (M : Finset (Fin n × Fin n))
    (hM_mem : ∀ p ∈ M, p.1 ∈ S_leaves ∧ p.2 ∈ T_u p.1)
    (I_set : Finset (Fin n)) (hIind : G.IsIndepSet (I_set : Set (Fin n)))
    (M_I : Finset (Fin n × Fin n)) (hMI_sub : M_I ⊆ M)
    (hM_I_prop : ∀ p ∈ M_I, x_nat ≤ 3 * (ext₀ p.1 p.2 ∩ I_set).card)
    (hI_maj : s * t ≤ 3 * M_I.card)
    (commonOut : Finset (Fin n) → Finset (Fin n))
    (hco_def : ∀ e z, z ∈ commonOut e ↔ z ∈ V' ∧ ∀ a ∈ e, z ∈ outN a)
    (s_v_val : ℕ) (hst2_lb : (s_v_val : ℝ) ≤ 2 * (L : ℝ) * (s : ℝ) * (t : ℝ) ^ 2) :
    ((s_v_val : ℝ) * (x_nat : ℝ) ^ 2) ^ 2 / (2 * 1296 ^ 2 * (L : ℝ) ^ 2 * (α : ℝ) ^ 3) ≤
      ((∑ e ∈ edgesIn G (neighbors G V' v), (commonOut e).card.choose 2 : ℕ) : ℝ) := by
  classical
  let K_count_v : ℕ := ∑ e ∈ edgesIn G (neighbors G V' v), (commonOut e).card.choose 2
  change _ ≤ (K_count_v : ℝ)
  let T_u_I (u : Fin n) : Finset (Fin n) := (T_u u).filter (fun w => (u, w) ∈ M_I)
  have hMI_sum : M_I.card = ∑ u ∈ S_leaves, (T_u_I u).card := by
    have hdisj : Set.PairwiseDisjoint (S_leaves : Set (Fin n))
        (fun u => (T_u_I u).image (fun w => (u, w))) := by
      intro u₁ _ u₂ _ hne
      change Disjoint _ _
      rw [disjoint_left]
      intro p hp1 hp2
      obtain ⟨w₁, _, rfl⟩ := mem_image.mp hp1
      obtain ⟨w₂, _, heq⟩ := mem_image.mp hp2
      exact hne (congrArg Prod.fst heq).symm
    have heq : M_I = S_leaves.biUnion (fun u => (T_u_I u).image (fun w => (u, w))) := by
      ext p
      rw [mem_biUnion]
      constructor
      · intro hp
        have hpM := hMI_sub hp
        obtain ⟨hu, hw⟩ := hM_mem p hpM
        exact ⟨p.1, hu, mem_image.mpr ⟨p.2, mem_filter.mpr ⟨hw, hp⟩, rfl⟩⟩
      · rintro ⟨u, _, hpw⟩
        obtain ⟨w, hw, rfl⟩ := mem_image.mp hpw
        exact (mem_filter.mp hw).2
    rw [heq, card_biUnion hdisj]
    refine sum_congr rfl fun u _ => card_image_of_injective _ (fun w₁ w₂ h => congrArg Prod.snd h)
  have hsum_I : (s : ℝ) * (t : ℝ) * (x_nat : ℝ) / 9 ≤
      ∑ u ∈ S_leaves, ((outN u ∩ I_set).card : ℝ) := by
    have h1 : ∀ u ∈ S_leaves, ((T_u_I u).card : ℝ) * (x_nat : ℝ) / 3 ≤
        ((outN u ∩ I_set).card : ℝ) := by
      intro u hu
      let B_u := (T_u_I u).biUnion (fun w => ext₀ u w ∩ I_set)
      have hB_sub : B_u ⊆ outN u ∩ I_set := by
        intro z hz
        obtain ⟨w, hw, hzw⟩ := mem_biUnion.mp hz
        have hz_ext := (mem_inter.mp (hext₀_sub u hu w (filter_subset _ _ hw) (mem_inter.mp hzw).1)).1
        exact mem_inter.mpr ⟨(mem_inter.mp hz_ext).2, (mem_inter.mp hzw).2⟩
      have hdisj_w : Set.PairwiseDisjoint (T_u_I u : Set (Fin n)) (fun w => ext₀ u w ∩ I_set) := by
        intro w₁ hw₁ w₂ hw₂ hne
        change Disjoint _ _
        rw [disjoint_left]
        intro z hz1 hz2
        exact (disjoint_left.mp (hext₀_disj u hu w₁ (filter_subset _ _ hw₁)
          w₂ (filter_subset _ _ hw₂) hne))
          (mem_inter.mp hz1).1 (mem_inter.mp hz2).1
      have hB_eq : B_u.card = ∑ w ∈ T_u_I u, (ext₀ u w ∩ I_set).card := card_biUnion hdisj_w
      have hB_ge : ((T_u_I u).card : ℝ) * ((x_nat : ℝ) / 3) ≤ (B_u.card : ℝ) := by
        have hBr : (B_u.card : ℝ) = ∑ w ∈ T_u_I u, ((ext₀ u w ∩ I_set).card : ℝ) := by
          exact_mod_cast hB_eq
        rw [hBr, ← nsmul_eq_mul, ← sum_const]
        refine sum_le_sum fun w hw => ?_
        have h3 : (x_nat : ℝ) ≤ 3 * ((ext₀ u w ∩ I_set).card : ℝ) := by
          exact_mod_cast hM_I_prop (u, w) (mem_filter.mp hw).2
        linarith
      have hle_out : (B_u.card : ℝ) ≤ ((outN u ∩ I_set).card : ℝ) := by
        exact_mod_cast card_le_card hB_sub
      linarith
    have hsum1 : ∑ u ∈ S_leaves, ((T_u_I u).card : ℝ) * (x_nat : ℝ) / 3 ≤
        ∑ u ∈ S_leaves, ((outN u ∩ I_set).card : ℝ) := sum_le_sum h1
    have h2 : (s : ℝ) * (t : ℝ) * (x_nat : ℝ) / 9 ≤
        ∑ u ∈ S_leaves, ((T_u_I u).card : ℝ) * (x_nat : ℝ) / 3 := by
      have hMI_r : (M_I.card : ℝ) = ∑ u ∈ S_leaves, ((T_u_I u).card : ℝ) := by exact_mod_cast hMI_sum
      have hMaj : (s : ℝ) * (t : ℝ) ≤ 3 * (M_I.card : ℝ) := by exact_mod_cast hI_maj
      have hx0 : 0 ≤ (x_nat : ℝ) := by positivity
      calc
        (s : ℝ) * (t : ℝ) * (x_nat : ℝ) / 9 ≤ (3 * (M_I.card : ℝ)) * (x_nat : ℝ) / 9 := by gcongr
        _ = (M_I.card : ℝ) * (x_nat : ℝ) / 3 := by ring
        _ = (∑ u ∈ S_leaves, ((T_u_I u).card : ℝ)) * (x_nat : ℝ) / 3 := by rw [hMI_r]
        _ = ∑ u ∈ S_leaves, ((T_u_I u).card : ℝ) * (x_nat : ℝ) / 3 := by
            rw [sum_mul, sum_div]
    exact h2.trans hsum1
  let P_pairs := I_set.powersetCard 2
  let C_pair (p : Finset (Fin n)) : Finset (Fin n) :=
    S_leaves.filter (fun u => ∀ z ∈ p, z ∈ outN u)
  have hP_sum : ∑ p ∈ P_pairs, ((C_pair p).card : ℝ) =
      ∑ u ∈ S_leaves, (((outN u ∩ I_set).card.choose 2 : ℕ) : ℝ) := by
    have hnat : ∑ p ∈ P_pairs, (C_pair p).card =
        ∑ u ∈ S_leaves, (outN u ∩ I_set).card.choose 2 := by
      have h1 : ∀ p ∈ P_pairs, (C_pair p).card =
          ∑ u ∈ S_leaves, if p ⊆ outN u ∩ I_set then 1 else 0 := by
        intro p hp
        rw [sum_boole, Nat.cast_id]
        congr 1; ext u; rw [mem_filter, mem_filter]
        have hpI : p ⊆ I_set := (mem_powersetCard.mp hp).1
        exact ⟨fun ⟨hu, hz⟩ => ⟨hu, fun z hz' => mem_inter.mpr ⟨hz z hz', hpI hz'⟩⟩,
               fun ⟨hu, hz⟩ => ⟨hu, fun z hz' => (mem_inter.mp (hz hz')).1⟩⟩
      have h2 : ∀ u ∈ S_leaves, (outN u ∩ I_set).card.choose 2 =
          ∑ p ∈ P_pairs, if p ⊆ outN u ∩ I_set then 1 else 0 := by
        intro u _
        rw [sum_boole, Nat.cast_id, ← card_powersetCard 2 (outN u ∩ I_set)]
        congr 1; ext p; dsimp [P_pairs]; rw [mem_powersetCard, mem_filter, mem_powersetCard]
        exact ⟨fun ⟨hp_sub, hp2⟩ => ⟨⟨hp_sub.trans inter_subset_right, hp2⟩, hp_sub⟩,
               fun ⟨⟨_, hp2⟩, hp_sub⟩ => ⟨hp_sub, hp2⟩⟩
      rw [sum_congr rfl h1, sum_comm, sum_congr rfl h2]
    exact_mod_cast hnat
  have hP_lb : (s : ℝ) * (t : ℝ) ^ 2 * (x_nat : ℝ) ^ 2 / 324 ≤
      ∑ p ∈ P_pairs, ((C_pair p).card : ℝ) := by
    rw [hP_sum]
    let S_sum : ℝ := ∑ u ∈ S_leaves, ((outN u ∩ I_set).card : ℝ)
    have hCS_u := cauchy_schwarz_finset S_leaves (fun u => ((outN u ∩ I_set).card : ℝ))
    have hS_leaves_rpos : (0 : ℝ) < (S_leaves.card : ℝ) := by
      rw [hS_leaves_card]; exact_mod_cast hs_pos
    have hS_sum_ge : 2 * (s : ℝ) ≤ S_sum := by
      have h1 : 2 * (s : ℝ) ≤ (s : ℝ) * (t : ℝ) * (x_nat : ℝ) / 9 := by
        have ht2 : (2 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht_ge2
        have hx30 : (30 : ℝ) ≤ (x_nat : ℝ) := by exact_mod_cast hx_nat_30
        have hs0 : (0 : ℝ) ≤ (s : ℝ) := Nat.cast_nonneg s
        have htx : (18 : ℝ) ≤ (t : ℝ) * (x_nat : ℝ) := by nlinarith only [ht2, hx30]
        rw [le_div_iff₀ (by norm_num)]
        nlinarith only [htx, hs0]
      exact h1.trans hsum_I
    have hchoose_sum : S_sum ^ 2 / (4 * (s : ℝ)) ≤
        ∑ u ∈ S_leaves, (((outN u ∩ I_set).card.choose 2 : ℕ) : ℝ) := by
      have h2ch : 2 * ∑ u ∈ S_leaves, (((outN u ∩ I_set).card.choose 2 : ℕ) : ℝ) =
          ∑ u ∈ S_leaves, ((outN u ∩ I_set).card : ℝ) ^ 2 - S_sum := by
        rw [mul_sum]
        have hterm : ∀ u ∈ S_leaves, (2 : ℝ) * (((outN u ∩ I_set).card.choose 2 : ℕ) : ℝ) =
            ((outN u ∩ I_set).card : ℝ) ^ 2 - ((outN u ∩ I_set).card : ℝ) := by
          intro u _
          have hnat : 2 * (outN u ∩ I_set).card.choose 2 + (outN u ∩ I_set).card =
              (outN u ∩ I_set).card ^ 2 := by
            rw [Nat.choose_two_right]
            have h2 : 2 ∣ (outN u ∩ I_set).card * ((outN u ∩ I_set).card - 1) := by
              rcases Nat.even_or_odd (outN u ∩ I_set).card with ⟨k, hk⟩ | ⟨k, hk⟩
              · exact ⟨k * ((outN u ∩ I_set).card - 1), by rw [hk]; ring⟩
              · have : (outN u ∩ I_set).card - 1 = 2 * k := by omega
                exact ⟨(outN u ∩ I_set).card * k, by rw [this]; ring⟩
            rw [Nat.mul_div_cancel' h2]
            rcases Nat.eq_zero_or_pos (outN u ∩ I_set).card with h0 | hpos
            · simp [h0]
            · have hc1 : 1 ≤ (outN u ∩ I_set).card := hpos
              zify [hc1]; ring
          have hreal : (2 : ℝ) * (((outN u ∩ I_set).card.choose 2 : ℕ) : ℝ) +
              ((outN u ∩ I_set).card : ℝ) = ((outN u ∩ I_set).card : ℝ) ^ 2 := by
            exact_mod_cast hnat
          linarith
        rw [sum_congr rfl hterm, sum_sub_distrib]
      have hsq_ge : S_sum ^ 2 / (s : ℝ) ≤ ∑ u ∈ S_leaves, ((outN u ∩ I_set).card : ℝ) ^ 2 := by
        rw [div_le_iff₀ (by exact_mod_cast hs_pos), mul_comm]
        change S_sum ^ 2 ≤ (S_leaves.card : ℝ) * ∑ u ∈ S_leaves, ((outN u ∩ I_set).card : ℝ) ^ 2 at hCS_u
        rw [hS_leaves_card] at hCS_u
        exact hCS_u
      have hs0 : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hs_pos
      have hS_nn : (0 : ℝ) ≤ S_sum := sum_nonneg fun _ _ => Nat.cast_nonneg _
      have h2s_pos : (0 : ℝ) < 2 * (s : ℝ) := mul_pos (by norm_num) hs0
      have hsub_ge : S_sum ^ 2 / (2 * (s : ℝ)) ≤ S_sum ^ 2 / (s : ℝ) - S_sum := by
        have hmul : S_sum ≤ S_sum ^ 2 / (2 * (s : ℝ)) := by
          rw [le_div_iff₀ h2s_pos]
          nlinarith only [hS_sum_ge, hS_nn]
        have heq : S_sum ^ 2 / (s : ℝ) - S_sum ^ 2 / (2 * (s : ℝ)) = S_sum ^ 2 / (2 * (s : ℝ)) := by ring
        linarith only [hmul, heq]
      have heq4 : S_sum ^ 2 / (2 * (s : ℝ)) = 2 * (S_sum ^ 2 / (4 * (s : ℝ))) := by ring
      linarith only [h2ch, hsq_ge, hsub_ge, heq4]
    have h4s_pos : (0 : ℝ) < 4 * (s : ℝ) := mul_pos (by norm_num) (by exact_mod_cast hs_pos)
    have hnum : ((s : ℝ) * (t : ℝ) * (x_nat : ℝ) / 9) ^ 2 / (4 * (s : ℝ)) ≤ S_sum ^ 2 / (4 * (s : ℝ)) := by
      have hLHS_nn : 0 ≤ (s : ℝ) * (t : ℝ) * (x_nat : ℝ) / 9 :=
        div_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg s) (Nat.cast_nonneg t)) (Nat.cast_nonneg x_nat))
          (by norm_num)
      have hsq : ((s : ℝ) * (t : ℝ) * (x_nat : ℝ) / 9) ^ 2 ≤ S_sum ^ 2 :=
        pow_le_pow_left₀ hLHS_nn hsum_I 2
      exact div_le_div_of_nonneg_right hsq h4s_pos.le
    have heq_num : ((s : ℝ) * (t : ℝ) * (x_nat : ℝ) / 9) ^ 2 / (4 * (s : ℝ)) =
        (s : ℝ) * (t : ℝ) ^ 2 * (x_nat : ℝ) ^ 2 / 324 := by
      have hs0 : (s : ℝ) ≠ 0 := by exact_mod_cast (by omega : s ≠ 0)
      field_simp; ring
    exact (heq_num.symm.trans_le hnum).trans hchoose_sum
  let P' := P_pairs.filter (fun p => 2 * α ≤ (C_pair p).card)
  have hP_card_le : (P_pairs.card : ℝ) ≤ (α : ℝ) ^ 2 / 2 := by
    have hI_le : I_set.card ≤ α := hInd I_set hIind
    have hch : P_pairs.card = I_set.card.choose 2 := card_powersetCard _ _
    have hle2 : 2 * P_pairs.card ≤ α ^ 2 := by
      rw [hch, Nat.choose_two_right]
      have h1 : I_set.card * (I_set.card - 1) / 2 * 2 ≤ I_set.card * (I_set.card - 1) :=
        Nat.div_mul_le_self _ _
      have h2 : I_set.card * (I_set.card - 1) ≤ I_set.card ^ 2 := by
        rw [sq]; exact Nat.mul_le_mul_left _ (Nat.sub_le _ _)
      have h3 : I_set.card ^ 2 ≤ α ^ 2 := Nat.pow_le_pow_left hI_le 2
      omega
    have h2r : 2 * (P_pairs.card : ℝ) ≤ (α : ℝ) ^ 2 := by exact_mod_cast hle2
    linarith
  have hL_posR : (0 : ℝ) < (L : ℝ) := lt_of_lt_of_le zero_lt_one hLR
  have hα_posR : (0 : ℝ) < (α : ℝ) := lt_of_lt_of_le zero_lt_one hαR
  have hP'_sum : (s : ℝ) * (t : ℝ) ^ 2 * (x_nat : ℝ) ^ 2 / 648 ≤
      ∑ p ∈ P', ((C_pair p).card : ℝ) := by
    have hsplit : ∑ p ∈ P_pairs, ((C_pair p).card : ℝ) =
        ∑ p ∈ P', ((C_pair p).card : ℝ) + ∑ p ∈ P_pairs \ P', ((C_pair p).card : ℝ) := by
      rw [← sum_union disjoint_sdiff_self_right, union_sdiff_of_subset (filter_subset _ _)]
    have hsmall : ∑ p ∈ P_pairs \ P', ((C_pair p).card : ℝ) ≤ (α : ℝ) ^ 3 := by
      have hs_le : ((P_pairs \ P').card : ℝ) ≤ (P_pairs.card : ℝ) := by
        exact_mod_cast card_le_card sdiff_subset
      calc
        ∑ p ∈ P_pairs \ P', ((C_pair p).card : ℝ) ≤ ∑ _p ∈ P_pairs \ P', (2 * (α : ℝ)) := by
          refine sum_le_sum fun p hp => ?_
          have hnot : ¬ 2 * α ≤ (C_pair p).card := fun hle =>
            (mem_sdiff.mp hp).2 (mem_filter.mpr ⟨(mem_sdiff.mp hp).1, hle⟩)
          exact_mod_cast (Nat.lt_of_not_le hnot).le
        _ = ((P_pairs \ P').card : ℝ) * (2 * (α : ℝ)) := by rw [sum_const, nsmul_eq_mul]
        _ ≤ (P_pairs.card : ℝ) * (2 * (α : ℝ)) :=
            mul_le_mul_of_nonneg_right hs_le (mul_nonneg (by norm_num) hα_posR.le)
        _ ≤ ((α : ℝ) ^ 2 / 2) * (2 * (α : ℝ)) :=
            mul_le_mul_of_nonneg_right hP_card_le (mul_nonneg (by norm_num) hα_posR.le)
        _ = (α : ℝ) ^ 3 := by ring
    have h2a_le : (α : ℝ) ^ 3 ≤ (s : ℝ) * (t : ℝ) ^ 2 * (x_nat : ℝ) ^ 2 / 648 := by
      have h1 : (n : ℝ) ^ 8 / (648 * 5184 * 64 ^ 8 * (L : ℝ) * (α : ℝ) ^ 16) ≤
          (s : ℝ) * (t : ℝ) ^ 2 * (x_nat : ℝ) ^ 2 / 648 := by
        have hx2 : ((n : ℝ) / (64 * (α : ℝ) ^ 2)) ^ 2 ≤ (x_nat : ℝ) ^ 2 :=
          pow_le_pow_left₀ (div_nonneg (Nat.cast_nonneg n) (mul_nonneg (by norm_num) (sq_nonneg _))) hx_nat_lb 2
        calc
          (n : ℝ) ^ 8 / (648 * 5184 * 64 ^ 8 * (L : ℝ) * (α : ℝ) ^ 16)
            = ((n : ℝ) ^ 6 / (5184 * 64 ^ 6 * (L : ℝ) * (α : ℝ) ^ 12)) *
                ((n : ℝ) / (64 * (α : ℝ) ^ 2)) ^ 2 / 648 := by ring
          _ ≤ (s : ℝ) * (t : ℝ) ^ 2 * (x_nat : ℝ) ^ 2 / 648 :=
              div_le_div_of_nonneg_right
                (mul_le_mul hst2_n6 hx2 (sq_nonneg _) (mul_nonneg (Nat.cast_nonneg s) (sq_nonneg _)))
                (by norm_num)
      have hpoly8 : 648 * 5184 * 64 ^ 8 * (L : ℝ) * (α : ℝ) ^ 19 < (n : ℝ) ^ 8 := by
        simpa using hpoly 8 1 19 (by decide) (648 * 5184 * 64 ^ 8) (by norm_num) (by decide) (by decide) (by norm_num)
      have h2 : (α : ℝ) ^ 3 ≤ (n : ℝ) ^ 8 / (648 * 5184 * 64 ^ 8 * (L : ℝ) * (α : ℝ) ^ 16) := by
        have hden16_pos : (0 : ℝ) < 648 * 5184 * 64 ^ 8 * (L : ℝ) * (α : ℝ) ^ 16 :=
          mul_pos (mul_pos (by norm_num) hL_posR) (pow_pos hα_posR 16)
        rw [le_div_iff₀ hden16_pos]
        linarith only [hpoly8, show (α : ℝ) ^ 3 * (648 * 5184 * 64 ^ 8 * (L : ℝ) * (α : ℝ) ^ 16) =
          648 * 5184 * 64 ^ 8 * (L : ℝ) * (α : ℝ) ^ 19 by ring]
      exact h2.trans h1
    linarith only [hP_lb, hsplit, hsmall, h2a_le]
  have hP'_ne : P'.Nonempty := by
    by_contra hPe
    rw [not_nonempty_iff_eq_empty.mp hPe, sum_empty] at hP'_sum
    have hs0 : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hs_pos
    have ht0 : (0 : ℝ) < (t : ℝ) := by exact_mod_cast (by omega : 0 < t)
    have hx0 : (0 : ℝ) < (x_nat : ℝ) := by exact_mod_cast hx_nat_pos
    have hpos : (0 : ℝ) < (s : ℝ) * (t : ℝ) ^ 2 * (x_nat : ℝ) ^ 2 / 648 :=
      div_pos (mul_pos (mul_pos hs0 (pow_pos ht0 2)) (pow_pos hx0 2)) (by norm_num)
    linarith only [hpos, hP'_sum]
  have hP'_pos : (0 : ℝ) < (P'.card : ℝ) := by exact_mod_cast card_pos.mpr hP'_ne
  have hP'_le : (P'.card : ℝ) ≤ (α : ℝ) ^ 2 / 2 :=
    (by exact_mod_cast card_le_card (filter_subset _ _) : (P'.card : ℝ) ≤ (P_pairs.card : ℝ)).trans hP_card_le
  have hsum_edges_P' : ((s : ℝ) * (t : ℝ) ^ 2 * (x_nat : ℝ) ^ 2 / 648) ^ 2 / (2 * (α : ℝ) ^ 3) ≤
      ∑ p ∈ P', ((edgesIn G (C_pair p)).card : ℝ) := by
    have hCS := cauchy_schwarz_finset P' (fun p => ((C_pair p).card : ℝ))
    have hTuran : ∑ p ∈ P', ((C_pair p).card : ℝ) ^ 2 ≤
        4 * (α : ℝ) * ∑ p ∈ P', ((edgesIn G (C_pair p)).card : ℝ) := by
      rw [mul_sum]
      refine sum_le_sum fun p hp => ?_
      exact edgesIn_ge_of_indep_le G (C_pair p) α hα (fun I _ hI => hInd I hI) (mem_filter.mp hp).2
    have hLHS_nn : 0 ≤ (s : ℝ) * (t : ℝ) ^ 2 * (x_nat : ℝ) ^ 2 / 648 :=
      div_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg s) (sq_nonneg _)) (sq_nonneg _)) (by norm_num)
    have hnum : ((s : ℝ) * (t : ℝ) ^ 2 * (x_nat : ℝ) ^ 2 / 648) ^ 2 ≤
        (∑ p ∈ P', ((C_pair p).card : ℝ)) ^ 2 :=
      pow_le_pow_left₀ hLHS_nn hP'_sum 2
    have h4α_pos : (0 : ℝ) < 4 * (α : ℝ) := mul_pos (by norm_num) hα_posR
    have h4ap : 4 * (α : ℝ) * (P'.card : ℝ) ≤ 2 * (α : ℝ) ^ 3 := by
      have h1 := mul_le_mul_of_nonneg_left hP'_le h4α_pos.le
      linarith only [h1, show 4 * (α : ℝ) * ((α : ℝ) ^ 2 / 2) = 2 * (α : ℝ) ^ 3 by ring]
    have h4aP'_pos : 0 < 4 * (α : ℝ) * (P'.card : ℝ) := mul_pos h4α_pos hP'_pos
    calc
      ((s : ℝ) * (t : ℝ) ^ 2 * (x_nat : ℝ) ^ 2 / 648) ^ 2 / (2 * (α : ℝ) ^ 3)
        ≤ (∑ p ∈ P', ((C_pair p).card : ℝ)) ^ 2 / (4 * (α : ℝ) * (P'.card : ℝ)) :=
          div_le_div₀ (sq_nonneg _) hnum h4aP'_pos h4ap
      _ = ((∑ p ∈ P', ((C_pair p).card : ℝ)) ^ 2 / (P'.card : ℝ)) / (4 * (α : ℝ)) := by ring
      _ ≤ (∑ p ∈ P', ((C_pair p).card : ℝ) ^ 2) / (4 * (α : ℝ)) :=
          div_le_div_of_nonneg_right ((div_le_iff₀ hP'_pos).mpr (by rw [mul_comm]; exact hCS)) h4α_pos.le
      _ ≤ ∑ p ∈ P', ((edgesIn G (C_pair p)).card : ℝ) :=
          (div_le_iff₀ h4α_pos).mpr (by rw [mul_comm]; exact hTuran)
  have hK_ge_P' : ∑ p ∈ P', (edgesIn G (C_pair p)).card ≤ K_count_v := by
    have hL : ∀ p ∈ P', (edgesIn G (C_pair p)).card ≤
        ∑ e ∈ edgesIn G (neighbors G V' v), if p ⊆ commonOut e then 1 else 0 := by
      intro p _
      rw [sum_boole, Nat.cast_id]
      refine card_le_card fun e he => ?_
      rw [mem_edgesIn] at he
      obtain ⟨heC, he2, hcl⟩ := he
      have he_nv : e ⊆ neighbors G V' v := fun u hu =>
        (hleaf_prop u (filter_subset _ _ (heC hu))).1
      refine mem_filter.mpr ⟨mem_edgesIn.mpr ⟨he_nv, he2, hcl⟩, fun z hz => (hco_def e z).mpr ⟨?_, fun u hu => ?_⟩⟩
      · obtain ⟨u, hu⟩ := card_pos.mp (by omega : 0 < e.card)
        have huV' : u ∈ V' := (mem_neighbors.mp (he_nv hu)).1
        exact (mem_neighbors.mp (hout_sub' u huV' ((mem_filter.mp (heC hu)).2 z hz))).1
      · exact (mem_filter.mp (heC hu)).2 z hz
    have hR : ∀ e ∈ edgesIn G (neighbors G V' v),
        (∑ p ∈ P', if p ⊆ commonOut e then 1 else 0) ≤ (commonOut e).card.choose 2 := by
      intro e _
      rw [sum_boole, Nat.cast_id, ← card_powersetCard 2 (commonOut e)]
      refine card_le_card fun p hp => ?_
      rw [mem_filter] at hp
      rw [mem_powersetCard]
      exact ⟨hp.2, (mem_powersetCard.mp ((filter_subset _ _) hp.1)).2⟩
    calc
      ∑ p ∈ P', (edgesIn G (C_pair p)).card
        ≤ ∑ p ∈ P', ∑ e ∈ edgesIn G (neighbors G V' v), if p ⊆ commonOut e then 1 else 0 :=
          sum_le_sum hL
      _ = ∑ e ∈ edgesIn G (neighbors G V' v), ∑ p ∈ P', if p ⊆ commonOut e then 1 else 0 :=
          sum_comm
      _ ≤ ∑ e ∈ edgesIn G (neighbors G V' v), (commonOut e).card.choose 2 := sum_le_sum hR
  have hK_ge_P'R : (∑ p ∈ P', ((edgesIn G (C_pair p)).card : ℝ)) ≤ (K_count_v : ℝ) := by
    exact_mod_cast hK_ge_P'
  have h_sv_sq : ((s_v_val : ℝ) * (x_nat : ℝ) ^ 2) ^ 2 / (2 * 1296 ^ 2 * (L : ℝ) ^ 2 * (α : ℝ) ^ 3) ≤
      ((s : ℝ) * (t : ℝ) ^ 2 * (x_nat : ℝ) ^ 2 / 648) ^ 2 / (2 * (α : ℝ) ^ 3) := by
    have h1 : (s_v_val : ℝ) * (x_nat : ℝ) ^ 2 / (1296 * (L : ℝ)) ≤
        (s : ℝ) * (t : ℝ) ^ 2 * (x_nat : ℝ) ^ 2 / 648 := by
      calc
        (s_v_val : ℝ) * (x_nat : ℝ) ^ 2 / (1296 * (L : ℝ))
          ≤ (2 * (L : ℝ) * (s : ℝ) * (t : ℝ) ^ 2) * (x_nat : ℝ) ^ 2 / (1296 * (L : ℝ)) :=
            div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hst2_lb (sq_nonneg _))
              (mul_nonneg (by norm_num) hL_posR.le)
        _ = (s : ℝ) * (t : ℝ) ^ 2 * (x_nat : ℝ) ^ 2 / 648 := by
            have hL0 : (L : ℝ) ≠ 0 := hL_posR.ne'
            field_simp; ring
    have h2 : ((s_v_val : ℝ) * (x_nat : ℝ) ^ 2 / (1296 * (L : ℝ))) ^ 2 ≤
        ((s : ℝ) * (t : ℝ) ^ 2 * (x_nat : ℝ) ^ 2 / 648) ^ 2 :=
      pow_le_pow_left₀
        (div_nonneg (mul_nonneg (Nat.cast_nonneg s_v_val) (sq_nonneg _))
          (mul_nonneg (by norm_num) hL_posR.le))
        h1 2
    have h3 : (((s_v_val : ℝ) * (x_nat : ℝ) ^ 2 / (1296 * (L : ℝ))) ^ 2) / (2 * (α : ℝ) ^ 3) ≤
        (((s : ℝ) * (t : ℝ) ^ 2 * (x_nat : ℝ) ^ 2 / 648) ^ 2) / (2 * (α : ℝ) ^ 3) :=
      div_le_div_of_nonneg_right h2 (mul_nonneg (by norm_num) (pow_nonneg hα_posR.le 3))
    have heq : (((s_v_val : ℝ) * (x_nat : ℝ) ^ 2 / (1296 * (L : ℝ))) ^ 2) / (2 * (α : ℝ) ^ 3) =
        ((s_v_val : ℝ) * (x_nat : ℝ) ^ 2) ^ 2 / (2 * 1296 ^ 2 * (L : ℝ) ^ 2 * (α : ℝ) ^ 3) := by
      ring
    exact heq.symm.trans_le h3
  exact h_sv_sq.trans (hsum_edges_P'.trans hK_ge_P'R)

private lemma claim2_per_v (n : ℕ) (G : SimpleGraph (Fin n)) (α : ℕ) (hα : 1 ≤ α)
    (hInd : ∀ I : Finset (Fin n), G.IsIndepSet (I : Set (Fin n)) → I.card ≤ α)
    (hK4 : Clique4Free G) (hLoc : LocalIndep G) (L : ℕ)
    (hnR : (1 : ℝ) ≤ (n : ℝ)) (hαR : (1 : ℝ) ≤ (α : ℝ)) (hLR : (1 : ℝ) ≤ (L : ℝ))
    (hLeq : L = Nat.log 2 n + 1)
    (hpoly : ∀ (p j q : ℕ), 1 ≤ p → ∀ (C : ℝ), 0 ≤ C → 5 * q ≤ 12 * p → 12 * j ≤ q →
      C ^ 12 ≤ (10 ^ 30 : ℝ) ^ q → C * (L : ℝ) ^ j * (α : ℝ) ^ q < (n : ℝ) ^ p)
    (V' : Finset (Fin n)) (outN : Fin n → Finset (Fin n))
    (hout_sub' : ∀ u ∈ V', outN u ⊆ neighbors G V' u)
    (x : ℝ) (_hx_pos : 0 < x)
    (hout_exp' : ∀ u ∈ V', ∀ A ⊆ outN u, G.IsIndepSet (A : Set (Fin n)) →
      x * (A.card : ℝ) ≤ ((near G (outN u) A).card : ℝ))
    (x_nat : ℕ) (hx_nat_30 : 30 ≤ x_nat) (hx_nat_pos : 1 ≤ x_nat)
    (hx_nat_le : (x_nat : ℝ) ≤ x - 1)
    (hx_nat_lb : (n : ℝ) / (64 * (α : ℝ) ^ 2) ≤ (x_nat : ℝ))
    (commonOut : Finset (Fin n) → Finset (Fin n))
    (hco_def : ∀ e z, z ∈ commonOut e ↔ z ∈ V' ∧ ∀ a ∈ e, z ∈ outN a)
    (v : Fin n) (hvV' : v ∈ V')
    (s_v_val : ℕ) (hs_v_eq : s_v_val = ∑ e ∈ (edgesIn G V').filter (fun e => v ∈ e), (commonOut e).card.choose 2)
    (hsv_n6 : (n : ℝ) ^ 6 / (2592 * 64 ^ 6 * (α : ℝ) ^ 12) ≤ (s_v_val : ℝ)) :
    ((s_v_val : ℝ) * (x_nat : ℝ) ^ 2) ^ 2 / (2 * 1296 ^ 2 * (L : ℝ) ^ 2 * (α : ℝ) ^ 3) ≤
      ((∑ e ∈ edgesIn G (neighbors G V' v), (commonOut e).card.choose 2 : ℕ) : ℝ) := by
  classical
  let S_star_v := (edgesIn G V').filter (fun e => v ∈ e)
  have hx_nat_R : (1 : ℝ) ≤ (x_nat : ℝ) := by exact_mod_cast hx_nat_pos
  have hsv_pos : 0 < s_v_val := by
    have : (0 : ℝ) < (s_v_val : ℝ) := lt_of_lt_of_le (by positivity) hsv_n6
    exact_mod_cast this
  have hcommon_le_a : ∀ e ∈ S_star_v, (commonOut e).card ≤ α := by
    intro e he
    have heV' := (filter_subset _ _) he
    obtain ⟨he_sub, he2, hecl⟩ := mem_edgesIn.mp heV'
    obtain ⟨a, b, hab, rfl⟩ := card_eq_two.mp he2
    have hab_adj : G.Adj a b :=
      hecl (mem_insert_self a {b}) (mem_insert_of_mem (mem_singleton_self b)) hab
    refine hInd (commonOut {a, b}) ?_
    rw [G.isIndepSet_iff]
    intro z₁ hz₁ z₂ hz₂ hzne hz12
    obtain ⟨_, hz1_all⟩ := (hco_def {a, b} z₁).mp hz₁
    obtain ⟨_, hz2_all⟩ := (hco_def {a, b} z₂).mp hz₂
    have haV' : a ∈ V' := he_sub (mem_insert_self a {b})
    have hbV' : b ∈ V' := he_sub (mem_insert_of_mem (mem_singleton_self b))
    have haz1 : G.Adj a z₁ := (mem_neighbors.mp (hout_sub' a haV' (hz1_all a (mem_insert_self a {b})))).2
    have hbz1 : G.Adj b z₁ := (mem_neighbors.mp (hout_sub' b hbV' (hz1_all b (mem_insert_of_mem (mem_singleton_self b))))).2
    have haz2 : G.Adj a z₂ := (mem_neighbors.mp (hout_sub' a haV' (hz2_all a (mem_insert_self a {b})))).2
    have hbz2 : G.Adj b z₂ := (mem_neighbors.mp (hout_sub' b hbV' (hz2_all b (mem_insert_of_mem (mem_singleton_self b))))).2
    let K : Finset (Fin n) := {a, b, z₁, z₂}
    have hKc : K.card = 4 := by
      rw [card_insert_of_notMem (by simp [hab, haz1.ne, haz2.ne]),
          card_insert_of_notMem (by simp [hbz1.ne, hbz2.ne]), card_pair hzne]
    refine hK4 K hKc ?_
    intro p hp q hq hpq
    simp only [K, coe_insert, coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at hp hq
    rcases hp with rfl | rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl | rfl
    · exact False.elim (hpq rfl)
    · exact hab_adj
    · exact haz1
    · exact haz2
    · exact hab_adj.symm
    · exact False.elim (hpq rfl)
    · exact hbz1
    · exact hbz2
    · exact haz1.symm
    · exact hbz1.symm
    · exact False.elim (hpq rfl)
    · exact hz12
    · exact haz2.symm
    · exact hbz2.symm
    · exact hz12.symm
    · exact False.elim (hpq rfl)
  have hcommon_le_n : ∀ e ∈ S_star_v, (commonOut e).card ≤ n := fun e _ =>
    (card_le_univ (commonOut e)).trans_eq (Fintype.card_fin n)
  have hs_v_pos_sum : 0 < ∑ e ∈ S_star_v, (commonOut e).card.choose 2 := by
    rw [← hs_v_eq]; exact hsv_pos
  obtain ⟨j, t, hj1, hjb, ht_eq, htn, hSne, hdyad⟩ :=
    dyadic_pigeonhole S_star_v (fun e => (commonOut e).card) n hcommon_le_n hs_v_pos_sum
  let S := S_star_v.filter (fun e => t ≤ (commonOut e).card ∧ (commonOut e).card < 2 * t)
  let s : ℕ := S.card
  have hs_pos : 1 ≤ s := card_pos.mpr hSne
  have ht_ge2 : 2 ≤ t := by
    have h21 : 2 ^ 1 ≤ 2 ^ j := Nat.pow_le_pow_right (by decide) hj1
    rw [ht_eq]; simpa using h21
  have ht_pos : 1 ≤ t := by omega
  have ht_le_a : t ≤ α := by
    obtain ⟨e₀, he₀⟩ := hSne
    exact (mem_filter.mp he₀).2.1.trans (hcommon_le_a e₀ (mem_filter.mp he₀).1)
  have hst2_lb : (s_v_val : ℝ) ≤ 2 * (L : ℝ) * (s : ℝ) * (t : ℝ) ^ 2 := by
    rw [hs_v_eq]
    have h1 : ((∑ e ∈ S_star_v, (commonOut e).card.choose 2 : ℕ) : ℝ) ≤
        ((Nat.log 2 n + 1 : ℕ) : ℝ) * (2 * (s : ℝ) * (t : ℝ) ^ 2) := by
      exact_mod_cast hdyad
    have hLeq' : ((Nat.log 2 n + 1 : ℕ) : ℝ) = (L : ℝ) := by rw [hLeq]
    dsimp [S_star_v] at h1
    rw [hLeq'] at h1
    linarith only [h1]
  have hst2_n6 : (n : ℝ) ^ 6 / (5184 * 64 ^ 6 * (L : ℝ) * (α : ℝ) ^ 12) ≤ (s : ℝ) * (t : ℝ) ^ 2 := by
    have h2 : (s_v_val : ℝ) / (2 * (L : ℝ)) ≤ (s : ℝ) * (t : ℝ) ^ 2 := by
      rw [div_le_iff₀ (by positivity)]
      linarith
    have h3 : (n : ℝ) ^ 6 / (2592 * 64 ^ 6 * (α : ℝ) ^ 12) / (2 * (L : ℝ)) ≤ (s_v_val : ℝ) / (2 * (L : ℝ)) := by
      gcongr
    calc
      (n : ℝ) ^ 6 / (5184 * 64 ^ 6 * (L : ℝ) * (α : ℝ) ^ 12)
        = (n : ℝ) ^ 6 / (2592 * 64 ^ 6 * (α : ℝ) ^ 12) / (2 * (L : ℝ)) := by ring
      _ ≤ (s : ℝ) * (t : ℝ) ^ 2 := h3.trans h2
  let S_leaves : Finset (Fin n) := V'.filter (fun u => ({v, u} : Finset (Fin n)) ∈ S)
  have hS_leaves_card : S_leaves.card = s := by
    refine card_bij (fun u _ => ({v, u} : Finset (Fin n))) ?_ ?_ ?_
    · intro u hu; exact (mem_filter.mp hu).2
    · intro u₁ hu₁ u₂ hu₂ heq
      have hu₁_in : ({v, u₁} : Finset (Fin n)) ∈ S_star_v := (filter_subset _ _) (mem_filter.mp hu₁).2
      have hcard1 := (mem_edgesIn.mp (filter_subset _ _ hu₁_in)).2.1
      have hne1 : v ≠ u₁ := by
        intro h; rw [h, pair_eq_singleton, card_singleton] at hcard1; omega
      have hmem : u₁ ∈ ({v, u₂} : Finset (Fin n)) := by rw [← heq]; simp
      simp only [mem_insert, mem_singleton] at hmem
      rcases hmem with rfl | rfl
      · exact False.elim (hne1 rfl)
      · rfl
    · intro e he
      have he_star : e ∈ S_star_v := (filter_subset _ _) he
      have he_V' : e ∈ edgesIn G V' := (filter_subset _ _) he_star
      have hv_in : v ∈ e := (mem_filter.mp he_star).2
      obtain ⟨he_sub, he2, _⟩ := mem_edgesIn.mp he_V'
      obtain ⟨a, b, _, he_eq⟩ := card_eq_two.mp he2
      rw [he_eq] at hv_in
      simp only [mem_insert, mem_singleton] at hv_in
      rcases hv_in with hva | hvb
      · have he_vb : ({v, b} : Finset (Fin n)) = e := by rw [he_eq, hva]
        refine ⟨b, mem_filter.mpr ⟨he_sub (by rw [← he_vb]; exact mem_insert_of_mem (mem_singleton_self _)), ?_⟩, he_vb⟩
        rwa [he_vb]
      · have he_va : ({v, a} : Finset (Fin n)) = e := by rw [he_eq, hvb, pair_comm]
        refine ⟨a, mem_filter.mpr ⟨he_sub (by rw [← he_va]; exact mem_insert_of_mem (mem_singleton_self _)), ?_⟩, he_va⟩
        rwa [he_va]
  have hleaf_prop : ∀ u ∈ S_leaves,
      u ∈ neighbors G V' v ∧ t ≤ (outN v ∩ outN u).card := by
    intro u hu
    have huV' : u ∈ V' := (filter_subset _ _) hu
    have heS : ({v, u} : Finset (Fin n)) ∈ S := (mem_filter.mp hu).2
    have heV' : ({v, u} : Finset (Fin n)) ∈ edgesIn G V' :=
      (filter_subset _ _) ((filter_subset _ _) heS)
    obtain ⟨_, he2, hecl⟩ := mem_edgesIn.mp heV'
    have hvu_ne : v ≠ u := by
      intro h; rw [h, pair_eq_singleton, card_singleton] at he2; omega
    have hvu_adj : G.Adj v u :=
      hecl (mem_insert_self v {u}) (mem_insert_of_mem (mem_singleton_self u)) hvu_ne
    have ht_le : t ≤ (commonOut {v, u}).card := (mem_filter.mp heS).2.1
    have hsub : commonOut {v, u} ⊆ outN v ∩ outN u := by
      intro z hz
      have hz' := ((hco_def {v, u} z).mp hz).2
      exact mem_inter.mpr ⟨hz' v (mem_insert_self v {u}), hz' u (mem_insert_of_mem (mem_singleton_self u))⟩
    exact ⟨mem_neighbors.mpr ⟨huV', hvu_adj⟩, ht_le.trans (card_le_card hsub)⟩
  have hT_all : ∀ u : Fin n, ∃ T ⊆ outN v ∩ outN u, u ∈ S_leaves → T.card = t := by
    intro u
    by_cases hu : u ∈ S_leaves
    · obtain ⟨T, h1, h2⟩ := exists_subset_card_eq (hleaf_prop u hu).2
      exact ⟨T, h1, fun _ => h2⟩
    · exact ⟨∅, empty_subset _, fun hu' => absurd hu' hu⟩
  choose T_u hTu_sub hTu_card using hT_all
  have hTu_sub' : ∀ u ∈ S_leaves, T_u u ⊆ outN v ∩ outN u := fun u _ => hTu_sub u
  have hTu_card' : ∀ u ∈ S_leaves, (T_u u).card = t := fun u hu => hTu_card u hu
  let Nv := neighbors G Finset.univ v
  have hNv_TF : TriangleFree G Nv := by
    intro a ha b hb c hc hab hbc hac
    let K : Finset (Fin n) := {v, a, b, c}
    have hva := (mem_neighbors.mp ha).2
    have hvb := (mem_neighbors.mp hb).2
    have hvc := (mem_neighbors.mp hc).2
    have hKc : K.card = 4 := by
      rw [card_insert_of_notMem (by simp [hva.ne, hvb.ne, hvc.ne]),
          card_insert_of_notMem (by simp [hab.ne, hac.ne]), card_pair hbc.ne]
    refine hK4 K hKc ?_
    intro p hp q hq hpq
    simp only [K, coe_insert, coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at hp hq
    rcases hp with rfl | rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl | rfl
    · exact False.elim (hpq rfl)
    · exact hva
    · exact hvb
    · exact hvc
    · exact hva.symm
    · exact False.elim (hpq rfl)
    · exact hab
    · exact hac
    · exact hvb.symm
    · exact hab.symm
    · exact False.elim (hpq rfl)
    · exact hbc
    · exact hvc.symm
    · exact hac.symm
    · exact hbc.symm
    · exact False.elim (hpq rfl)
  have hexists_ext0 : ∀ u ∈ S_leaves, ∃ f : T_u u → Fin x_nat → Fin n,
      Function.Injective (fun p : T_u u × Fin x_nat => f p.1 p.2) ∧
      ∀ w : T_u u, ∀ i : Fin x_nat,
        f w i ∈ (N_tri G v ∩ outN u) ∩ neighbors G Finset.univ w.1 := by
    intro u hu
    have huV' : u ∈ V' := (filter_subset _ _) hu
    have huv_adj : G.Adj u v := (mem_neighbors.mp (hleaf_prop u hu).1).2.symm
    let F : (T_u u × Fin x_nat) → Finset (Fin n) :=
      fun p => (N_tri G v ∩ outN u) ∩ neighbors G Finset.univ p.1.1
    have hHall : ∀ Q : Finset (T_u u × Fin x_nat), Q.card ≤ (Q.biUnion F).card := by
      intro Q
      let A : Finset (Fin n) := Q.image (fun p => p.1.1)
      rcases A.eq_empty_or_nonempty with hAe | hAne
      · have hQe : Q = ∅ := by
          rw [eq_empty_iff_forall_notMem]
          intro p hp
          have : p.1.1 ∈ A := mem_image.mpr ⟨p, hp, rfl⟩
          rw [hAe] at this; simp at this
        simp [hQe]
      have hQ_le : Q.card ≤ A.card * x_nat := by
        have hsub : Q ⊆ (Q.image Prod.fst) ×ˢ Finset.univ := by
          intro p hp
          exact mem_product.mpr ⟨mem_image.mpr ⟨p, hp, rfl⟩, mem_univ _⟩
        have himg : (Q.image Prod.fst).card = A.card := by
          refine card_bij (fun w _ => w.1) ?_ ?_ ?_
          · intro w hw
            obtain ⟨p, hp, rfl⟩ := mem_image.mp hw
            exact mem_image.mpr ⟨p, hp, rfl⟩
          · intro w₁ _ w₂ _ h; exact Subtype.ext h
          · intro z hz
            obtain ⟨p, hp, rfl⟩ := mem_image.mp hz
            exact ⟨p.1, mem_image.mpr ⟨p, hp, rfl⟩, rfl⟩
        calc
          Q.card ≤ ((Q.image Prod.fst) ×ˢ (Finset.univ : Finset (Fin x_nat))).card :=
            card_le_card hsub
          _ = A.card * x_nat := by rw [card_product, himg, card_univ, Fintype.card_fin]
      have hA_sub_out : A ⊆ outN u := by
        intro w hw
        obtain ⟨p, _, rfl⟩ := mem_image.mp hw
        exact (mem_inter.mp (hTu_sub' u hu p.1.2)).2
      have hA_ind : G.IsIndepSet (A : Set (Fin n)) := by
        have hA_nbr : A ⊆ neighbors G Nv u := by
          intro w hw
          obtain ⟨p, _, hpw⟩ := mem_image.mp hw
          have hw_out_v := (mem_inter.mp (hTu_sub' u hu p.1.2)).1
          have hw_out_u := (mem_inter.mp (hTu_sub' u hu p.1.2)).2
          have hw_nv : w ∈ Nv := mem_neighbors.mpr
            ⟨mem_univ _, by rw [← hpw]; exact (mem_neighbors.mp (hout_sub' v hvV' hw_out_v)).2⟩
          have huw : G.Adj u w := by
            rw [← hpw]; exact (mem_neighbors.mp (hout_sub' u huV' hw_out_u)).2
          exact mem_neighbors.mpr ⟨hw_nv, huw⟩
        have hu_nv : u ∈ Nv := mem_neighbors.mpr ⟨mem_univ _, huv_adj.symm⟩
        exact indep_mono hA_nbr (triangleFree_neighbors_indep hNv_TF hu_nv)
      have hexp := hout_exp' u huV' A hA_sub_out hA_ind
      have hnear_sub : (near G (outN u) A).erase v ⊆ Q.biUnion F := by
        intro z hz
        have hzv : z ≠ v := (mem_erase.mp hz).1
        obtain ⟨hz_out, w, hwA, hwz⟩ := mem_near.mp (mem_of_mem_erase hz)
        obtain ⟨p, hpQ, hpw⟩ := mem_image.mp hwA
        have hw_out_v := (mem_inter.mp (hTu_sub' u hu p.1.2)).1
        have hw_out_u := (mem_inter.mp (hTu_sub' u hu p.1.2)).2
        have hvw_adj : G.Adj v w := by
          rw [← hpw]
          exact (mem_neighbors.mp (hout_sub' v hvV' hw_out_v)).2
        have hz_tri : z ∈ N_tri G v :=
          ext_subset_N_tri_adj G hK4 V' outN hout_sub' huV' huv_adj (by rw [← hpw]; exact hw_out_u)
            hvw_adj hz_out hwz hzv
        exact mem_biUnion.mpr ⟨p, hpQ, mem_inter.mpr ⟨mem_inter.mpr ⟨hz_tri, hz_out⟩,
          mem_neighbors.mpr ⟨mem_univ _, by rw [hpw]; exact hwz⟩⟩⟩
      have hnear_pos : 1 ≤ (near G (outN u) A).card := by
        have hA1 : (1 : ℝ) ≤ (A.card : ℝ) := by exact_mod_cast card_pos.mpr hAne
        have hx1 : (1 : ℝ) ≤ x := by linarith only [hx_nat_le, hx_nat_R]
        have : (1 : ℝ) ≤ ((near G (outN u) A).card : ℝ) := by nlinarith only [hA1, hx1, hexp]
        exact_mod_cast this
      have hcard_er : (A.card : ℝ) * (x_nat : ℝ) ≤ (((near G (outN u) A).erase v).card : ℝ) := by
        have h1 : (near G (outN u) A).card - 1 ≤ ((near G (outN u) A).erase v).card :=
          card_erase_ge_sub_one _ _
        have hcast : (((near G (outN u) A).card - 1 : ℕ) : ℝ) =
            ((near G (outN u) A).card : ℝ) - 1 := by
          rw [Nat.cast_sub hnear_pos]; norm_num
        have h1r : ((near G (outN u) A).card : ℝ) - 1 ≤ (((near G (outN u) A).erase v).card : ℝ) := by
          rw [← hcast]; exact_mod_cast h1
        have hA1 : (1 : ℝ) ≤ (A.card : ℝ) := by exact_mod_cast card_pos.mpr hAne
        calc
          (A.card : ℝ) * (x_nat : ℝ)
            ≤ (A.card : ℝ) * (x - 1) := mul_le_mul_of_nonneg_left hx_nat_le (Nat.cast_nonneg _)
          _ = x * (A.card : ℝ) - (A.card : ℝ) := by ring
          _ ≤ x * (A.card : ℝ) - 1 := by linarith only [hA1]
          _ ≤ ((near G (outN u) A).card : ℝ) - 1 := by linarith only [hexp]
          _ ≤ (((near G (outN u) A).erase v).card : ℝ) := h1r
      have hcard_erN : A.card * x_nat ≤ ((near G (outN u) A).erase v).card := by exact_mod_cast hcard_er
      exact hQ_le.trans (hcard_erN.trans (card_le_card hnear_sub))
    obtain ⟨g, hg_inj, hg_mem⟩ := (Finset.all_card_le_biUnion_card_iff_existsInjective' F).mp hHall
    exact ⟨fun w i => g (w, i), hg_inj, fun w i => hg_mem (w, i)⟩
  have hf_all : ∀ u : Fin n, ∃ f : T_u u → Fin x_nat → Fin n,
      (u ∈ S_leaves → Function.Injective (fun p : T_u u × Fin x_nat => f p.1 p.2)) ∧
      (u ∈ S_leaves → ∀ w : T_u u, ∀ i : Fin x_nat,
        f w i ∈ (N_tri G v ∩ outN u) ∩ neighbors G Finset.univ w.1) := by
    intro u
    by_cases hu : u ∈ S_leaves
    · obtain ⟨f, hf1, hf2⟩ := hexists_ext0 u hu
      exact ⟨f, fun _ => hf1, fun _ => hf2⟩
    · exact ⟨fun _ _ => v, fun hu' => absurd hu' hu, fun hu' => absurd hu' hu⟩
  choose f_ext hf_prop using hf_all
  have hf_inj' : ∀ u ∈ S_leaves,
      Function.Injective (fun p : T_u u × Fin x_nat => f_ext u p.1 p.2) :=
    fun u hu => (hf_prop u).1 hu
  have hf_mem' : ∀ u ∈ S_leaves, ∀ w : T_u u, ∀ i : Fin x_nat,
      f_ext u w i ∈ (N_tri G v ∩ outN u) ∩ neighbors G Finset.univ w.1 :=
    fun u hu => (hf_prop u).2 hu
  let ext₀ (u w : Fin n) : Finset (Fin n) :=
    if hu : u ∈ S_leaves then
      if hw : w ∈ T_u u then Finset.univ.image (fun i : Fin x_nat => f_ext u ⟨w, hw⟩ i)
      else ∅
    else ∅
  have hext₀_card : ∀ u ∈ S_leaves, ∀ w ∈ T_u u, (ext₀ u w).card = x_nat := by
    intro u hu w hw
    simp only [ext₀, dif_pos hu, dif_pos hw]
    rw [card_image_of_injective _ (fun i₁ i₂ h => by
      have := hf_inj' u hu (a₁ := (⟨w, hw⟩, i₁)) (a₂ := (⟨w, hw⟩, i₂)) h
      exact congrArg Prod.snd this), card_univ, Fintype.card_fin]
  have hext₀_sub : ∀ u ∈ S_leaves, ∀ w ∈ T_u u,
      ext₀ u w ⊆ (N_tri G v ∩ outN u) ∩ neighbors G Finset.univ w := by
    intro u hu w hw z hz
    simp only [ext₀, dif_pos hu, dif_pos hw, mem_image, mem_univ, true_and] at hz
    obtain ⟨i, rfl⟩ := hz
    exact hf_mem' u hu ⟨w, hw⟩ i
  have hext₀_disj : ∀ u ∈ S_leaves, ∀ w₁ ∈ T_u u, ∀ w₂ ∈ T_u u,
      w₁ ≠ w₂ → Disjoint (ext₀ u w₁) (ext₀ u w₂) := by
    intro u hu w₁ hw₁ w₂ hw₂ hne
    rw [disjoint_left]
    intro z hz₁ hz₂
    simp only [ext₀, dif_pos hu, dif_pos hw₁, dif_pos hw₂, mem_image, mem_univ, true_and] at hz₁ hz₂
    obtain ⟨i₁, rfl⟩ := hz₁
    obtain ⟨i₂, heq⟩ := hz₂
    have := hf_inj' u hu (a₁ := (⟨w₁, hw₁⟩, i₁)) (a₂ := (⟨w₂, hw₂⟩, i₂)) heq.symm
    exact hne (congrArg (fun p => p.1.1) this)
  let M : Finset (Fin n × Fin n) := S_leaves.biUnion (fun u => (T_u u).image (fun w => (u, w)))
  have hM_card : M.card = s * t := by
    have hdisj : Set.PairwiseDisjoint (S_leaves : Set (Fin n))
        (fun u => (T_u u).image (fun w => (u, w))) := by
      intro u₁ _ u₂ _ hne
      change Disjoint _ _
      rw [disjoint_left]
      intro p hp1 hp2
      obtain ⟨w₁, _, rfl⟩ := mem_image.mp hp1
      obtain ⟨w₂, _, heq⟩ := mem_image.mp hp2
      exact hne (congrArg Prod.fst heq).symm
    rw [card_biUnion hdisj]
    calc
      ∑ u ∈ S_leaves, ((T_u u).image (fun w => (u, w))).card
        = ∑ u ∈ S_leaves, (T_u u).card := sum_congr rfl fun u _ =>
            card_image_of_injective _ (fun w₁ w₂ h => congrArg Prod.snd h)
      _ = ∑ _u ∈ S_leaves, t := sum_congr rfl hTu_card'
      _ = S_leaves.card * t := by rw [sum_const, smul_eq_mul]
      _ = s * t := by rw [hS_leaves_card]
  have hM_mem : ∀ p ∈ M, p.1 ∈ S_leaves ∧ p.2 ∈ T_u p.1 := by
    intro p hp
    obtain ⟨u, hu, hpw⟩ := mem_biUnion.mp hp
    obtain ⟨w, hw, rfl⟩ := mem_image.mp hpw
    exact ⟨hu, hw⟩
  have hM_nv : ∀ p ∈ M, p.1 ∈ Nv ∧ p.2 ∈ Nv ∧ G.Adj p.1 p.2 := by
    intro p hp
    obtain ⟨hu, hw⟩ := hM_mem p hp
    have huV' : p.1 ∈ V' := (filter_subset _ _) hu
    have hu_nv : p.1 ∈ Nv := mem_neighbors.mpr ⟨mem_univ _, (mem_neighbors.mp (hleaf_prop p.1 hu).1).2⟩
    have hw_out_v := (mem_inter.mp (hTu_sub' p.1 hu hw)).1
    have hw_out_u := (mem_inter.mp (hTu_sub' p.1 hu hw)).2
    have hw_nv : p.2 ∈ Nv := mem_neighbors.mpr
      ⟨mem_univ _, (mem_neighbors.mp (hout_sub' v hvV' hw_out_v)).2⟩
    have hadj : G.Adj p.1 p.2 := (mem_neighbors.mp (hout_sub' p.1 huV' hw_out_u)).2
    exact ⟨hu_nv, hw_nv, hadj⟩
  obtain ⟨L_set, I_set, C_set, C_part, hUnion, hLI, hLC, hIC, hL4, hIind, hC_biU, hC_disj, hC_ctr⟩ :=
    partition_N_tri G hLoc v
  let M_C := M.filter (fun p => x_nat ≤ 3 * (ext₀ p.1 p.2 ∩ C_set).card)
  let M_L := (M \ M_C).filter (fun p => x_nat ≤ 3 * (ext₀ p.1 p.2 ∩ L_set).card)
  let M_I := (M \ M_C) \ M_L
  have hM_split : M.card = M_C.card + M_L.card + M_I.card := by
    have h1 : M.card = M_C.card + (M \ M_C).card :=
      (card_sdiff_add_card_inter M M_C).symm.trans (by
        rw [inter_eq_right.mpr (filter_subset _ _), add_comm])
    have h2 : (M \ M_C).card = M_L.card + M_I.card :=
      (card_sdiff_add_card_inter (M \ M_C) M_L).symm.trans (by
        rw [inter_eq_right.mpr (filter_subset _ _), add_comm])
    omega
  have hM_I_prop : ∀ p ∈ M_I, x_nat ≤ 3 * (ext₀ p.1 p.2 ∩ I_set).card := by
    intro p hp
    have hp_not_L : ¬ x_nat ≤ 3 * (ext₀ p.1 p.2 ∩ L_set).card := by
      intro hle; exact (mem_sdiff.mp hp).2 (mem_filter.mpr ⟨(mem_sdiff.mp hp).1, hle⟩)
    have hp_not_C : ¬ x_nat ≤ 3 * (ext₀ p.1 p.2 ∩ C_set).card := by
      intro hle
      exact (mem_sdiff.mp (mem_sdiff.mp hp).1).2
        (mem_filter.mpr ⟨(mem_sdiff.mp (mem_sdiff.mp hp).1).1, hle⟩)
    have hpM : p ∈ M := (mem_sdiff.mp (mem_sdiff.mp hp).1).1
    obtain ⟨hu, hw⟩ := hM_mem p hpM
    have hsub : ext₀ p.1 p.2 ⊆ L_set ∪ I_set ∪ C_set :=
      hUnion ▸ (hext₀_sub p.1 hu p.2 hw).trans (inter_subset_left.trans inter_subset_left)
    have h_eq : ext₀ p.1 p.2 =
        (ext₀ p.1 p.2 ∩ L_set) ∪ (ext₀ p.1 p.2 ∩ I_set) ∪ (ext₀ p.1 p.2 ∩ C_set) := by
      ext z; simp only [mem_union, mem_inter]
      constructor
      · intro hz; have h1 := hsub hz; simp only [mem_union] at h1; tauto
      · intro h; tauto
    have hd1 : Disjoint (ext₀ p.1 p.2 ∩ L_set) (ext₀ p.1 p.2 ∩ I_set) :=
      Disjoint.mono inter_subset_right inter_subset_right hLI
    have hd2 : Disjoint (ext₀ p.1 p.2 ∩ L_set ∪ ext₀ p.1 p.2 ∩ I_set) (ext₀ p.1 p.2 ∩ C_set) :=
      Disjoint.mono
        (union_subset (inter_subset_right.trans subset_union_left)
          (inter_subset_right.trans subset_union_right))
        inter_subset_right (disjoint_union_left.mpr ⟨hLC, hIC⟩)
    have hpart : (ext₀ p.1 p.2).card =
        (ext₀ p.1 p.2 ∩ L_set).card + (ext₀ p.1 p.2 ∩ I_set).card + (ext₀ p.1 p.2 ∩ C_set).card :=
      (congrArg Finset.card h_eq).trans
        ((card_union_of_disjoint hd2).trans
          (congrArg (· + (ext₀ p.1 p.2 ∩ C_set).card) (card_union_of_disjoint hd1)))
    rw [hext₀_card p.1 hu p.2 hw] at hpart
    omega
  have hcases : s * t ≤ 3 * M_C.card ∨ s * t ≤ 3 * M_L.card ∨ s * t ≤ 3 * M_I.card := by
    rw [← hM_card]; omega
  rcases hcases with hC_maj | hL_maj | hI_maj
  · exact False.elim (claim2_case_C n G α hInd hK4 hLoc L hnR hαR hLR hpoly V' outN hout_sub'
      x_nat hx_nat_R hx_nat_lb v hNv_TF s t hs_pos ht_pos ht_le_a hst2_n6
      S_leaves hS_leaves_card (filter_subset _ _) hleaf_prop T_u hTu_card' ext₀ hext₀_sub hext₀_disj
      M hM_mem hM_nv C_set C_part hC_biU hC_disj hC_ctr
      M_C (filter_subset _ _) (fun p hp => (mem_filter.mp hp).2) hC_maj)
  · have hL_TF : TriangleFree G L_set :=
      triangleFree_subset (N_tri_triangle_free G hK4 hLoc v)
        (fun w hw => (hUnion ▸ mem_union_left _ (mem_union_left _ hw) : w ∈ N_tri G v))
    by_cases hst_cmp : t ≤ 72 * s
    · exact False.elim (claim2_case_L_le n G α hInd hK4 hLoc L hnR hαR hLR hpoly V' outN hout_sub'
        x_nat hx_nat_R hx_nat_lb v hNv_TF s t hst2_n6 S_leaves (filter_subset _ _) T_u ext₀ hext₀_sub
        M hM_mem hM_nv L_set hL4 M_L ((filter_subset _ _).trans sdiff_subset)
        (fun p hp => (mem_filter.mp hp).2) hL_maj hst_cmp)
    · have hts72 : 72 * s < t := Nat.lt_of_not_le hst_cmp
      exact False.elim (claim2_case_L_gt n G α hα hInd hK4 hLoc L hnR hαR hLR hpoly V' outN hout_sub'
        x_nat hx_nat_30 hx_nat_pos hx_nat_lb v s t hs_pos ht_le_a hst2_n6
        S_leaves hS_leaves_card (filter_subset _ _) T_u hTu_card' ext₀ hext₀_card hext₀_sub hext₀_disj
        M hM_mem hM_nv L_set hL_TF hL4 M_L ((filter_subset _ _).trans sdiff_subset)
        (fun p hp => (mem_filter.mp hp).2) hL_maj hts72)
  · exact claim2_case_I n G α hα hInd L hnR hαR hLR hpoly V' outN hout_sub'
      x_nat hx_nat_30 hx_nat_pos hx_nat_lb v s t hs_pos ht_ge2 hst2_n6
      S_leaves hS_leaves_card hleaf_prop T_u ext₀ hext₀_sub hext₀_disj
      M hM_mem I_set hIind M_I (sdiff_subset.trans sdiff_subset) hM_I_prop hI_maj
      commonOut hco_def s_v_val hst2_lb

private lemma localIndep_bound (n : ℕ) (hn : 100 ≤ n) (G : SimpleGraph (Fin n)) (α : ℕ)
    (hInd : ∀ I : Finset (Fin n), G.IsIndepSet (I : Set (Fin n)) → I.card ≤ α)
    (hLoc : LocalIndep G) :
    (n : ℝ) ^ 5 ≤ (10 ^ 30 : ℝ) * ((Nat.log 2 n + 1 : ℕ) : ℝ) * (α : ℝ) ^ 12 := by
  classical
  by_contra! hbad
  let L : ℕ := Nat.log 2 n + 1
  have hn_pos : 1 ≤ n := by omega
  have hL_pos : 1 ≤ L := by omega
  have hα : 1 ≤ α := by
    have h0 : ({⟨0, by omega⟩} : Finset (Fin n)).card ≤ α := hInd _ (by simp)
    simpa using h0
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn_pos
  have hLR : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL_pos
  have hαR : (1 : ℝ) ≤ (α : ℝ) := by exact_mod_cast hα
  have hbad' : (10 ^ 30 : ℝ) * (L : ℝ) * (α : ℝ) ^ 12 < (n : ℝ) ^ 5 := hbad
  have hpoly : ∀ (p j q : ℕ), 1 ≤ p → ∀ (C : ℝ), 0 ≤ C → 5 * q ≤ 12 * p → 12 * j ≤ q →
      C ^ 12 ≤ (10 ^ 30 : ℝ) ^ q → C * (L : ℝ) ^ j * (α : ℝ) ^ q < (n : ℝ) ^ p :=
    fun p j q hp C hC0 hpq hjq hC => lt_of_rpow_poly hnR hLR hαR hbad' p j q hp C hC0 hpq hjq hC
  have hK4 : Clique4Free G := by
    intro K hKc hK
    have hTF : TriangleFree G (Finset.univ \ K) := k4_gives_triangle_free_rest G hLoc hKc hK
    obtain ⟨I, _, hI, hle⟩ := card_triangle_free_subset G (Finset.univ \ K) hTF
    have hcard_sdiff : (Finset.univ \ K).card = n - 4 := by
      have h1 : K ⊆ Finset.univ := subset_univ K
      rw [card_sdiff_of_subset h1, card_univ, Fintype.card_fin, hKc]
    have hle_a : n - 4 ≤ 2 * α ^ 2 := by
      rw [← hcard_sdiff]
      exact hle.trans (Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left (hInd I hI) 2))
    have hn4 : n ≤ 4 * α ^ 2 := by omega
    have h4a : 4 * (α : ℝ) ^ 2 < (n : ℝ) := by
      simpa using hpoly 1 0 2 (by decide) 4 (by norm_num) (by decide) (by decide) (by norm_num)
    have hn4R : (n : ℝ) ≤ 4 * (α : ℝ) ^ 2 := by exact_mod_cast hn4
    linarith
  have h4a_lt : 4 * (α : ℝ) < (n : ℝ) := by
    simpa using hpoly 1 0 1 (by decide) 4 (by norm_num) (by decide) (by decide) (by norm_num)
  have hprune := prune_min_deg G (by rw [Fintype.card_fin]; exact hn_pos) α hα hInd
  rw [Fintype.card_fin] at hprune
  obtain hbad4 | ⟨V', _, hV'2, hdeg⟩ := hprune
  · linarith
  have h1000a : 1000 * (α : ℝ) ^ 2 < (n : ℝ) := by
    simpa using hpoly 1 0 2 (by decide) 1000 (by norm_num) (by decide) (by decide) (by norm_num)
  let x : ℝ := (n : ℝ) / (32 * (α : ℝ) ^ 2)
  have hx_gt31 : 31 < x := by
    dsimp [x]
    rw [lt_div_iff₀ (by positivity)]
    linarith
  have hx_pos : 0 < x := by linarith
  let x_nat : ℕ := Nat.floor (x - 1)
  have hx_nat_30 : 30 ≤ x_nat := by
    rw [Nat.le_floor_iff (by linarith)]
    push_cast; linarith
  have hx_nat_pos : 1 ≤ x_nat := by omega
  have hx_nat_le : (x_nat : ℝ) ≤ x - 1 := Nat.floor_le (by linarith)
  have hx_nat_lb : (n : ℝ) / (64 * (α : ℝ) ^ 2) ≤ (x_nat : ℝ) := by
    have hfl : x - 2 < (x_nat : ℝ) := by
      have := Nat.sub_one_lt_floor (x - 1)
      linarith
    have hhalf : x / 2 ≤ x - 2 := by linarith
    have heq : (n : ℝ) / (64 * (α : ℝ) ^ 2) = x / 2 := by dsimp [x]; ring
    linarith
  have hexp_all : ∀ u : Fin n, ∃ T ⊆ neighbors G V' u,
      (u ∈ V' → ((neighbors G V' u).card : ℝ) - (α : ℝ) * (x + 1) ≤ (T.card : ℝ)) ∧
      ∀ A ⊆ T, G.IsIndepSet (A : Set (Fin n)) → x * (A.card : ℝ) ≤ ((near G T A).card : ℝ) := by
    intro u
    by_cases hu : u ∈ V'
    · obtain ⟨T, h1, h2, h3⟩ := expanding_neighbors G (neighbors G V' u) (α : ℝ) x
        (fun I _ hI => by exact_mod_cast hInd I hI) hx_pos.le
      exact ⟨T, h1, fun _ => h2, h3⟩
    · exact ⟨∅, empty_subset _, fun hu' => absurd hu' hu, fun A hA _ => by
        have : A = ∅ := subset_empty.mp hA
        simp [this, near]⟩
  choose outN hout_sub hout_card hout_exp using hexp_all
  have hout_sub' : ∀ u ∈ V', outN u ⊆ neighbors G V' u := fun u _ => hout_sub u
  have hout_card' : ∀ u ∈ V',
      ((neighbors G V' u).card : ℝ) - (α : ℝ) * (x + 1) ≤ ((outN u).card : ℝ) := hout_card
  have hout_lb : ∀ u ∈ V', (n : ℝ) / (16 * (α : ℝ)) ≤ ((outN u).card : ℝ) := by
    intro u hu
    have h1 := hout_card' u hu
    have h2 := hdeg u hu
    have hax : (α : ℝ) * (x + 1) = (n : ℝ) / (32 * (α : ℝ)) + (α : ℝ) := by
      dsimp [x]
      have hα0 : (α : ℝ) ≠ 0 := by positivity
      field_simp
    have ha_le : (α : ℝ) ≤ (n : ℝ) / (32 * (α : ℝ)) := by
      rw [le_div_iff₀ (by positivity)]
      linarith
    have hdiv_eq : (n : ℝ) / (8 * (α : ℝ)) - (n : ℝ) / (32 * (α : ℝ)) - (n : ℝ) / (32 * (α : ℝ)) =
        (n : ℝ) / (16 * (α : ℝ)) := by ring
    linarith
  have hx_sum_lb : (n : ℝ) ^ 2 / (32 * (α : ℝ)) ≤ ∑ u ∈ V', ((outN u).card : ℝ) := by
    have hV'half : (n : ℝ) / 2 ≤ (V'.card : ℝ) := by
      have : (n : ℝ) ≤ 2 * (V'.card : ℝ) := by exact_mod_cast hV'2
      linarith
    calc
      (n : ℝ) ^ 2 / (32 * (α : ℝ)) = ((n : ℝ) / 2) * ((n : ℝ) / (16 * (α : ℝ))) := by ring
      _ ≤ (V'.card : ℝ) * ((n : ℝ) / (16 * (α : ℝ))) := by gcongr
      _ = ∑ _u ∈ V', ((n : ℝ) / (16 * (α : ℝ))) := by rw [sum_const, nsmul_eq_mul]
      _ ≤ ∑ u ∈ V', ((outN u).card : ℝ) := sum_le_sum hout_lb
  have hN3_contra : 16 * 9 * 64 ^ 3 * (α : ℝ) ^ 7 < (n : ℝ) ^ 3 := by
    simpa using hpoly 3 0 7 (by decide) (16 * 9 * 64 ^ 3) (by norm_num) (by decide) (by decide) (by norm_num)
  have hT4 := claim1_T4_lower G hK4 hLoc α hα hInd V' outN hout_sub' x hx_pos (fun u _ => hout_exp u)
    x_nat hx_nat_le hx_nat_pos (by simpa [Fintype.card_fin] using hx_nat_lb)
    (by simpa [Fintype.card_fin] using hx_sum_lb) (by simpa [Fintype.card_fin] using hN3_contra)
  rw [Fintype.card_fin] at hT4
  let commonOut (e : Finset (Fin n)) : Finset (Fin n) := V'.filter (fun z => ∀ a ∈ e, z ∈ outN a)
  let T4 : ℕ := ∑ e ∈ edgesIn G V', (commonOut e).card.choose 2
  have hT4_ge : (n : ℝ) ^ 7 ≤ 2592 * 64 ^ 6 * (α : ℝ) ^ 12 * (T4 : ℝ) := by
    dsimp [T4, commonOut]; convert hT4
  have hT4_pos : 0 < T4 := by
    by_contra h0
    have hz : T4 = 0 := by omega
    rw [hz, Nat.cast_zero, mul_zero] at hT4_ge
    have : (0 : ℝ) < (n : ℝ) ^ 7 := by positivity
    linarith
  let S_star (v : Fin n) : Finset (Finset (Fin n)) := (edgesIn G V').filter (fun e => v ∈ e)
  let s_v (v : Fin n) : ℕ := ∑ e ∈ S_star v, (commonOut e).card.choose 2
  have hsum_sv : ∑ v ∈ V', s_v v = 2 * T4 := by
    have h1 : ∀ v ∈ V', s_v v =
        ∑ e ∈ edgesIn G V', if v ∈ e then (commonOut e).card.choose 2 else 0 := by
      intro v _
      dsimp [s_v, S_star]
      rw [sum_filter]
    rw [sum_congr rfl h1, sum_comm]
    dsimp [T4]
    rw [mul_sum]
    refine sum_congr rfl fun e he => ?_
    obtain ⟨heV', he2, _⟩ := mem_edgesIn.mp he
    rw [← sum_filter, filter_mem_eq_inter, inter_eq_right.mpr heV', sum_const, smul_eq_mul, he2]
  let V'_star := V'.filter (fun v => (T4 : ℝ) / (n : ℝ) ≤ (s_v v : ℝ))
  have hV'_star_sum : (T4 : ℝ) ≤ ∑ v ∈ V'_star, (s_v v : ℝ) := by
    have hsplit : ∑ v ∈ V', (s_v v : ℝ) =
        ∑ v ∈ V'_star, (s_v v : ℝ) + ∑ v ∈ V' \ V'_star, (s_v v : ℝ) := by
      rw [← sum_union disjoint_sdiff_self_right, union_sdiff_of_subset (filter_subset _ _)]
    have hlow : ∑ v ∈ V' \ V'_star, (s_v v : ℝ) ≤ (T4 : ℝ) := by
      have hcard_n : ((V' \ V'_star).card : ℝ) ≤ (n : ℝ) := by
        exact_mod_cast (card_le_univ (V' \ V'_star)).trans_eq (Fintype.card_fin n)
      calc
        ∑ v ∈ V' \ V'_star, (s_v v : ℝ) ≤ ∑ _v ∈ V' \ V'_star, ((T4 : ℝ) / (n : ℝ)) := by
            refine sum_le_sum fun v hv => ?_
            have hnot : ¬ (T4 : ℝ) / (n : ℝ) ≤ (s_v v : ℝ) := by
              intro hle
              exact (mem_sdiff.mp hv).2 (mem_filter.mpr ⟨(mem_sdiff.mp hv).1, hle⟩)
            linarith
        _ = ((V' \ V'_star).card : ℝ) * ((T4 : ℝ) / (n : ℝ)) := by rw [sum_const, nsmul_eq_mul]
        _ ≤ (n : ℝ) * ((T4 : ℝ) / (n : ℝ)) := by gcongr
        _ = (T4 : ℝ) := by
            have hn0 : (n : ℝ) ≠ 0 := by positivity
            field_simp
    have hsumR : ∑ v ∈ V', (s_v v : ℝ) = 2 * (T4 : ℝ) := by exact_mod_cast hsum_sv
    linarith
  have hV'_star_ne : V'_star.Nonempty := by
    by_contra hVe
    rw [not_nonempty_iff_eq_empty.mp hVe, sum_empty] at hV'_star_sum
    have : (0 : ℝ) < (T4 : ℝ) := by exact_mod_cast hT4_pos
    linarith
  let K_count (v : Fin n) : ℕ := ∑ e ∈ edgesIn G (neighbors G V' v), (commonOut e).card.choose 2
  have hK_ub : ∑ v ∈ V'_star, (K_count v : ℝ) ≤ (α : ℝ) * (T4 : ℝ) := by
    have hnat : ∑ v ∈ V'_star, K_count v ≤ α * T4 := by
      have h1 : ∀ v ∈ V'_star, K_count v =
          ∑ e ∈ edgesIn G V', if e ⊆ neighbors G V' v then (commonOut e).card.choose 2 else 0 := by
        intro v _
        dsimp [K_count]
        have heq : edgesIn G (neighbors G V' v) =
            (edgesIn G V').filter (fun e => e ⊆ neighbors G V' v) := by
          ext e
          rw [mem_filter, mem_edgesIn, mem_edgesIn]
          exact ⟨fun ⟨h1, h2, h3⟩ => ⟨⟨h1.trans neighbors_subset, h2, h3⟩, h1⟩,
                 fun ⟨⟨_, h2, h3⟩, h1⟩ => ⟨h1, h2, h3⟩⟩
        rw [heq, sum_filter]
      rw [sum_congr rfl h1, sum_comm]
      dsimp [T4]
      rw [mul_sum]
      refine sum_le_sum fun e he => ?_
      rw [← sum_filter, sum_const, smul_eq_mul]
      refine Nat.mul_le_mul_right _ ?_
      obtain ⟨_, he2, hecl⟩ := mem_edgesIn.mp he
      obtain ⟨a, b, hab, rfl⟩ := card_eq_two.mp he2
      have hab_adj : G.Adj a b :=
        hecl (mem_insert_self a {b}) (mem_insert_of_mem (mem_singleton_self b)) hab
      refine hInd _ ?_
      rw [G.isIndepSet_iff]
      intro v₁ hv₁ v₂ hv₂ hvne hv12
      have hv1_n := (mem_filter.mp hv₁).2
      have hv2_n := (mem_filter.mp hv₂).2
      have hv1a : G.Adj v₁ a := (mem_neighbors.mp (hv1_n (mem_insert_self a {b}))).2
      have hv1b : G.Adj v₁ b := (mem_neighbors.mp (hv1_n (mem_insert_of_mem (mem_singleton_self b)))).2
      have hv2a : G.Adj v₂ a := (mem_neighbors.mp (hv2_n (mem_insert_self a {b}))).2
      have hv2b : G.Adj v₂ b := (mem_neighbors.mp (hv2_n (mem_insert_of_mem (mem_singleton_self b)))).2
      let K : Finset (Fin n) := {a, b, v₁, v₂}
      have hKc : K.card = 4 := by
        rw [card_insert_of_notMem (by simp [hab, hv1a.ne.symm, hv2a.ne.symm]),
            card_insert_of_notMem (by simp [hv1b.ne.symm, hv2b.ne.symm]), card_pair hvne]
      refine hK4 K hKc ?_
      intro p hp q hq hpq
      simp only [K, coe_insert, coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at hp hq
      rcases hp with rfl | rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl | rfl
      · exact False.elim (hpq rfl)
      · exact hab_adj
      · exact hv1a.symm
      · exact hv2a.symm
      · exact hab_adj.symm
      · exact False.elim (hpq rfl)
      · exact hv1b.symm
      · exact hv2b.symm
      · exact hv1a
      · exact hv1b
      · exact False.elim (hpq rfl)
      · exact hv12
      · exact hv2a
      · exact hv2b
      · exact hv12.symm
      · exact False.elim (hpq rfl)
    exact_mod_cast hnat
  have hK_per_v : ∀ v ∈ V'_star,
      ((s_v v : ℝ) * (x_nat : ℝ) ^ 2) ^ 2 / (2 * 1296 ^ 2 * (L : ℝ) ^ 2 * (α : ℝ) ^ 3) ≤
        (K_count v : ℝ) := by
    intro v hv_star
    have hvV' : v ∈ V' := (filter_subset _ _) hv_star
    have hsv_lb : (T4 : ℝ) / (n : ℝ) ≤ (s_v v : ℝ) := (mem_filter.mp hv_star).2
    have hsv_n6 : (n : ℝ) ^ 6 / (2592 * 64 ^ 6 * (α : ℝ) ^ 12) ≤ (s_v v : ℝ) := by
      have h2 : (n : ℝ) ^ 7 / (2592 * 64 ^ 6 * (α : ℝ) ^ 12) ≤ (T4 : ℝ) := by
        rw [div_le_iff₀ (by positivity)]
        linarith
      have h3 : (n : ℝ) ^ 6 / (2592 * 64 ^ 6 * (α : ℝ) ^ 12) ≤ (T4 : ℝ) / (n : ℝ) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        linarith [show (n : ℝ) ^ 6 * (n : ℝ) = (n : ℝ) ^ 7 by ring]
      exact h3.trans hsv_lb
    exact claim2_per_v n G α hα hInd hK4 hLoc L hnR hαR hLR rfl hpoly V' outN hout_sub'
      x hx_pos (fun u _ => hout_exp u) x_nat hx_nat_30 hx_nat_pos hx_nat_le hx_nat_lb
      commonOut (fun e z => by simp [commonOut]) v hvV' (s_v v) rfl hsv_n6
  have hV'_star_pos : (0 : ℝ) < (V'_star.card : ℝ) := by exact_mod_cast card_pos.mpr hV'_star_ne
  have hV'_star_le : (V'_star.card : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast (card_le_univ V'_star).trans_eq (Fintype.card_fin n)
  have hCS_star := cauchy_schwarz_finset V'_star (fun v => (s_v v : ℝ))
  have hsum_sq_star : (T4 : ℝ) ^ 2 / (n : ℝ) ≤ ∑ v ∈ V'_star, (s_v v : ℝ) ^ 2 := by
    have h1 : (T4 : ℝ) ^ 2 ≤ (∑ v ∈ V'_star, (s_v v : ℝ)) ^ 2 :=
      pow_le_pow_left₀ (Nat.cast_nonneg T4) hV'_star_sum 2
    calc
      (T4 : ℝ) ^ 2 / (n : ℝ) ≤ (∑ v ∈ V'_star, (s_v v : ℝ)) ^ 2 / (V'_star.card : ℝ) :=
          div_le_div₀ (sq_nonneg _) h1 hV'_star_pos hV'_star_le
      _ ≤ ∑ v ∈ V'_star, (s_v v : ℝ) ^ 2 := by
          rw [div_le_iff₀ hV'_star_pos, mul_comm]; exact hCS_star
  have hsum_K_lb : ((T4 : ℝ) ^ 2 / (n : ℝ)) * ((n : ℝ) / (64 * (α : ℝ) ^ 2)) ^ 4 /
      (2 * 1296 ^ 2 * (L : ℝ) ^ 2 * (α : ℝ) ^ 3) ≤ ∑ v ∈ V'_star, (K_count v : ℝ) := by
    have h1 : ∑ v ∈ V'_star,
        ((s_v v : ℝ) * (x_nat : ℝ) ^ 2) ^ 2 / (2 * 1296 ^ 2 * (L : ℝ) ^ 2 * (α : ℝ) ^ 3) ≤
        ∑ v ∈ V'_star, (K_count v : ℝ) := sum_le_sum hK_per_v
    have hfactor : ∑ v ∈ V'_star,
        ((s_v v : ℝ) * (x_nat : ℝ) ^ 2) ^ 2 / (2 * 1296 ^ 2 * (L : ℝ) ^ 2 * (α : ℝ) ^ 3) =
        ((x_nat : ℝ) ^ 4 / (2 * 1296 ^ 2 * (L : ℝ) ^ 2 * (α : ℝ) ^ 3)) *
          ∑ v ∈ V'_star, (s_v v : ℝ) ^ 2 := by
      rw [mul_sum]; refine sum_congr rfl fun v _ => ?_; ring
    rw [hfactor] at h1
    have hx4 : ((n : ℝ) / (64 * (α : ℝ) ^ 2)) ^ 4 ≤ (x_nat : ℝ) ^ 4 := by gcongr
    have h2 : ((T4 : ℝ) ^ 2 / (n : ℝ)) * ((n : ℝ) / (64 * (α : ℝ) ^ 2)) ^ 4 /
        (2 * 1296 ^ 2 * (L : ℝ) ^ 2 * (α : ℝ) ^ 3) ≤
        ((x_nat : ℝ) ^ 4 / (2 * 1296 ^ 2 * (L : ℝ) ^ 2 * (α : ℝ) ^ 3)) *
          ∑ v ∈ V'_star, (s_v v : ℝ) ^ 2 := by
      have heq : ((T4 : ℝ) ^ 2 / (n : ℝ)) * ((n : ℝ) / (64 * (α : ℝ) ^ 2)) ^ 4 /
          (2 * 1296 ^ 2 * (L : ℝ) ^ 2 * (α : ℝ) ^ 3) =
          (((n : ℝ) / (64 * (α : ℝ) ^ 2)) ^ 4 / (2 * 1296 ^ 2 * (L : ℝ) ^ 2 * (α : ℝ) ^ 3)) *
            ((T4 : ℝ) ^ 2 / (n : ℝ)) := by ring
      rw [heq]
      exact mul_le_mul (div_le_div_of_nonneg_right hx4 (by positivity)) hsum_sq_star
        (by positivity) (by positivity)
    exact h2.trans h1
  have hT4_ub : (T4 : ℝ) * (n : ℝ) ^ 3 ≤ 2 * 1296 ^ 2 * 64 ^ 4 * (L : ℝ) ^ 2 * (α : ℝ) ^ 12 := by
    have h1 : ((T4 : ℝ) ^ 2 / (n : ℝ)) * ((n : ℝ) / (64 * (α : ℝ) ^ 2)) ^ 4 /
        (2 * 1296 ^ 2 * (L : ℝ) ^ 2 * (α : ℝ) ^ 3) ≤ (α : ℝ) * (T4 : ℝ) := hsum_K_lb.trans hK_ub
    have hT4_rpos : (0 : ℝ) < (T4 : ℝ) := by exact_mod_cast hT4_pos
    have heq : ((T4 : ℝ) ^ 2 / (n : ℝ)) * ((n : ℝ) / (64 * (α : ℝ) ^ 2)) ^ 4 /
        (2 * 1296 ^ 2 * (L : ℝ) ^ 2 * (α : ℝ) ^ 3) =
        ((T4 : ℝ) * ((T4 : ℝ) * (n : ℝ) ^ 3)) / (2 * 1296 ^ 2 * 64 ^ 4 * (L : ℝ) ^ 2 * (α : ℝ) ^ 11) := by
      have hn0 : (n : ℝ) ≠ 0 := by positivity
      have hL0 : (L : ℝ) ≠ 0 := by positivity
      have hα0 : (α : ℝ) ≠ 0 := by positivity
      field_simp
    rw [heq, div_le_iff₀ (by positivity)] at h1
    have h2 : (T4 : ℝ) * ((T4 : ℝ) * (n : ℝ) ^ 3) ≤
        (T4 : ℝ) * (2 * 1296 ^ 2 * 64 ^ 4 * (L : ℝ) ^ 2 * (α : ℝ) ^ 12) := by
      linarith [show ((α : ℝ) * (T4 : ℝ)) * (2 * 1296 ^ 2 * 64 ^ 4 * (L : ℝ) ^ 2 * (α : ℝ) ^ 11) =
        (T4 : ℝ) * (2 * 1296 ^ 2 * 64 ^ 4 * (L : ℝ) ^ 2 * (α : ℝ) ^ 12) by ring]
    exact le_of_mul_le_mul_left h2 hT4_rpos
  have hcontra10 : (n : ℝ) ^ 10 ≤
      2592 * 64 ^ 6 * 2 * 1296 ^ 2 * 64 ^ 4 * (L : ℝ) ^ 2 * (α : ℝ) ^ 24 := by
    calc
      (n : ℝ) ^ 10 = (n : ℝ) ^ 7 * (n : ℝ) ^ 3 := by ring
      _ ≤ (2592 * 64 ^ 6 * (α : ℝ) ^ 12 * (T4 : ℝ)) * (n : ℝ) ^ 3 := by gcongr
      _ = 2592 * 64 ^ 6 * (α : ℝ) ^ 12 * ((T4 : ℝ) * (n : ℝ) ^ 3) := by ring
      _ ≤ 2592 * 64 ^ 6 * (α : ℝ) ^ 12 * (2 * 1296 ^ 2 * 64 ^ 4 * (L : ℝ) ^ 2 * (α : ℝ) ^ 12) := by gcongr
      _ = 2592 * 64 ^ 6 * 2 * 1296 ^ 2 * 64 ^ 4 * (L : ℝ) ^ 2 * (α : ℝ) ^ 24 := by ring
  have hpoly10 : 2592 * 64 ^ 6 * 2 * 1296 ^ 2 * 64 ^ 4 * (L : ℝ) ^ 2 * (α : ℝ) ^ 24 < (n : ℝ) ^ 10 :=
    hpoly 10 2 24 (by decide) (2592 * 64 ^ 6 * 2 * 1296 ^ 2 * 64 ^ 4) (by norm_num) (by decide) (by decide) (by norm_num)
  linarith

private lemma h_poly_lower (n : ℕ) (hn : 100 ≤ n) :
    (n : ℝ) ^ 5 ≤ (10 ^ 30 : ℝ) * ((Nat.log 2 n + 1 : ℕ) : ℝ) * (Erdos813.h n : ℝ) ^ 12 := by
  classical
  let S : Set ℕ := {k | ∃ G : SimpleGraph (Fin n), Erdos813.EverySevenHasTriangle G ∧ G.cliqueNum = k}
  have hS : S.Nonempty := ⟨(⊤ : SimpleGraph (Fin n)).cliqueNum,
    ⟨⊤, Erdos813.everySevenHasTriangle_top n, rfl⟩⟩
  obtain ⟨G₀, hG₀, hk⟩ := Nat.sInf_mem hS
  have hInd : ∀ I : Finset (Fin n), G₀ᶜ.IsIndepSet (I : Set (Fin n)) → I.card ≤ Erdos813.h n := by
    intro I hI
    have hcl : G₀.IsClique (I : Set (Fin n)) := by
      simpa using hI
    unfold Erdos813.h
    rw [← hk]
    exact hcl.card_le_cliqueNum
  have hLoc : LocalIndep G₀ᶜ := by
    intro A hA
    obtain ⟨I, hIA, hIc⟩ := hG₀ A hA
    exact ⟨I, hIA, hIc.card_eq, by simpa using hIc.isClique⟩
  exact localIndep_bound n hn G₀ᶜ (Erdos813.h n) hInd hLoc

end Claim2AndMain

end

end E813BuSu

/-- Bucic-Sudakov lower bound for Erdos Problem 813. -/
theorem OMA.solution : type_of% @Erdos813.erdos_813.variants.bucic_sudakov := by
  intro ε hε
  by_cases hlt : ε < 5 / 12
  · let r : ℝ := 12 * ε
    have hr : 0 < r := by dsimp [r]; linarith
    have hlo : Real.log =o[Filter.atTop] fun x : ℝ => x ^ r := isLittleO_log_rpow_atTop hr
    have hc_pos : 0 < Real.log 2 / (2 * (10 ^ 30 : ℝ)) := by
      have : 0 < Real.log 2 := Real.log_pos (by norm_num)
      positivity
    have h_ev_log : ∀ᶠ n : ℕ in Filter.atTop,
        ‖Real.log (n : ℝ)‖ ≤ (Real.log 2 / (2 * (10 ^ 30 : ℝ))) * ‖(n : ℝ) ^ r‖ :=
      (tendsto_natCast_atTop_atTop (R := ℝ)).eventually (hlo.bound hc_pos)
    have h_ev_rpow : ∀ᶠ n : ℕ in Filter.atTop, 2 * (10 ^ 30 : ℝ) ≤ (n : ℝ) ^ r :=
      (tendsto_natCast_atTop_atTop (R := ℝ)).eventually
        ((tendsto_rpow_atTop hr).eventually_ge_atTop (2 * (10 ^ 30 : ℝ)))
    filter_upwards [Filter.eventually_ge_atTop 100, h_ev_log, h_ev_rpow] with n hn hlog hrpow
    have hpoly := E813BuSu.h_poly_lower n hn
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
    have hn0 : (0 : ℝ) < (n : ℝ) := by positivity
    have hlog_nn : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hn1
    have hrpow_nn : 0 ≤ (n : ℝ) ^ r := by positivity
    rw [Real.norm_of_nonneg hlog_nn, Real.norm_of_nonneg hrpow_nn] at hlog
    have hnatlog : (Nat.log 2 n : ℝ) * Real.log 2 ≤ Real.log (n : ℝ) := by
      have hpow : (2 : ℝ) ^ (Nat.log 2 n : ℕ) ≤ (n : ℝ) := by
        exact_mod_cast Nat.pow_log_le_self 2 (by omega)
      have h2pos : 0 < (2 : ℝ) ^ (Nat.log 2 n : ℕ) := by positivity
      have hl := Real.log_le_log h2pos hpow
      rwa [Real.log_pow] at hl
    have hL_le : (10 ^ 30 : ℝ) * ((Nat.log 2 n + 1 : ℕ) : ℝ) ≤ (n : ℝ) ^ r := by
      have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
      have hnatlog_div : (Nat.log 2 n : ℝ) ≤ Real.log (n : ℝ) / Real.log 2 :=
        (le_div_iff₀ hlog2).mpr hnatlog
      have hlog_div : Real.log (n : ℝ) / Real.log 2 ≤ (n : ℝ) ^ r / (2 * (10 ^ 30 : ℝ)) := by
        rw [div_le_iff₀ hlog2]
        have : (Real.log 2 / (2 * (10 ^ 30 : ℝ))) * (n : ℝ) ^ r =
            ((n : ℝ) ^ r / (2 * (10 ^ 30 : ℝ))) * Real.log 2 := by ring
        linarith
      have hL_cast : ((Nat.log 2 n + 1 : ℕ) : ℝ) = (Nat.log 2 n : ℝ) + 1 := by push_cast; rfl
      rw [hL_cast]
      calc
        (10 ^ 30 : ℝ) * ((Nat.log 2 n : ℝ) + 1)
          ≤ (10 ^ 30 : ℝ) * ((n : ℝ) ^ r / (2 * (10 ^ 30 : ℝ)) + 1) := by gcongr; linarith
        _ = (n : ℝ) ^ r / 2 + 10 ^ 30 := by ring
        _ ≤ (n : ℝ) ^ r / 2 + (n : ℝ) ^ r / 2 := by linarith
        _ = (n : ℝ) ^ r := by ring
    have h12 : (n : ℝ) ^ (5 - 12 * ε : ℝ) ≤ (Erdos813.h n : ℝ) ^ (12 : ℕ) := by
      have h5 : (n : ℝ) ^ 5 ≤ (n : ℝ) ^ r * (Erdos813.h n : ℝ) ^ 12 := by
        calc
          (n : ℝ) ^ 5 ≤ ((10 ^ 30 : ℝ) * ((Nat.log 2 n + 1 : ℕ) : ℝ)) * (Erdos813.h n : ℝ) ^ 12 := hpoly
          _ ≤ (n : ℝ) ^ r * (Erdos813.h n : ℝ) ^ 12 := by gcongr
      have h5' : (n : ℝ) ^ (5 : ℝ) ≤ (n : ℝ) ^ r * (Erdos813.h n : ℝ) ^ (12 : ℕ) := by
        simpa [Real.rpow_natCast] using h5
      have hmul := mul_le_mul_of_nonneg_right h5' (by positivity : 0 ≤ (n : ℝ) ^ (-r))
      have hLHS : (n : ℝ) ^ (5 : ℝ) * (n : ℝ) ^ (-r) = (n : ℝ) ^ (5 - 12 * ε : ℝ) :=
        (Real.rpow_add hn0 5 (-r)).symm.trans
          (congrArg ((n : ℝ) ^ ·) (show (5 : ℝ) + -r = 5 - 12 * ε by dsimp [r]; ring))
      have hRHS : (n : ℝ) ^ r * (Erdos813.h n : ℝ) ^ (12 : ℕ) * (n : ℝ) ^ (-r) =
          (Erdos813.h n : ℝ) ^ (12 : ℕ) := by
        have h1 : (n : ℝ) ^ r * (n : ℝ) ^ (-r) = 1 := by
          rw [← Real.rpow_add hn0, add_neg_cancel, Real.rpow_zero]
        calc
          (n : ℝ) ^ r * (Erdos813.h n : ℝ) ^ (12 : ℕ) * (n : ℝ) ^ (-r)
            = ((n : ℝ) ^ r * (n : ℝ) ^ (-r)) * (Erdos813.h n : ℝ) ^ (12 : ℕ) := by ring
          _ = (Erdos813.h n : ℝ) ^ (12 : ℕ) := by rw [h1, one_mul]
      linarith
    have hrpow_root := Real.rpow_le_rpow (by positivity : 0 ≤ (n : ℝ) ^ (5 - 12 * ε : ℝ)) h12
      (by norm_num : (0 : ℝ) ≤ 1 / 12)
    have hL_root : ((n : ℝ) ^ (5 - 12 * ε : ℝ)) ^ (1 / 12 : ℝ) = (n : ℝ) ^ (5 / 12 - ε : ℝ) := by
      rw [← Real.rpow_mul hn0.le]
      congr 1; ring
    have hR_root : ((Erdos813.h n : ℝ) ^ (12 : ℕ)) ^ (1 / 12 : ℝ) = (Erdos813.h n : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
      norm_num
    rw [hL_root, hR_root] at hrpow_root
    exact hrpow_root
  · have hge : 5 / 12 ≤ ε := le_of_not_gt hlt
    rw [Filter.eventually_atTop]
    refine ⟨1, fun n hn => ?_⟩
    have hne : {k : ℕ | ∃ G : SimpleGraph (Fin n),
        Erdos813.EverySevenHasTriangle G ∧ G.cliqueNum = k}.Nonempty :=
      ⟨_, ⊤, Erdos813.everySevenHasTriangle_top n, rfl⟩
    obtain ⟨G, _, hG⟩ := Nat.sInf_mem hne
    have h1 : 1 ≤ Erdos813.h n := by
      unfold Erdos813.h
      rw [← hG]
      have hc : G.IsClique (↑({(⟨0, by omega⟩ : Fin n)} : Finset (Fin n))) := by
        rw [Finset.coe_singleton]
        exact SimpleGraph.isClique_singleton _
      have hcard := hc.card_le_cliqueNum
      rw [Finset.card_singleton] at hcard
      exact hcard
    have h2 : (n : ℝ) ^ (5 / 12 - ε : ℝ) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hn) (by linarith)
    have h3 : (1 : ℝ) ≤ (Erdos813.h n : ℝ) := by exact_mod_cast h1
    linarith
