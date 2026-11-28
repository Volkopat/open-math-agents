import OMAReductions.R_RamseyNumbers_ramsey_number_five_five_upper_bound_R1

/-!
The finite pattern selection of Angeltveit and McKay, Proposition 5.3 in
R(5,5) ≤ 46. See https://arxiv.org/html/2409.15709#S5.

The remaining graph inputs are the two computations in Lemmas 5.1 and 5.2
and the maximum-degree consequence of the 22-vertex lower edge count in
Table 1. The incidence and weight arguments are verified below.
-/

/- Double-counting the finite incidences in Angeltveit–McKay, Proposition 5.3. -/

namespace OMA.Ramsey55Pattern

open Finset
open scoped BigOperators

theorem sum_filter_card_comm {I X : Type*} (indices : Finset I) (points : Finset X)
    (R : I → X → Prop) [DecidableRel R] :
    (∑ i ∈ indices, (points.filter (R i)).card) =
      ∑ x ∈ points, (indices.filter (fun i => R i x)).card := by
  calc
    _ = ∑ i ∈ indices, ∑ x ∈ points, if R i x then (1 : ℕ) else 0 := by simp
    _ = ∑ x ∈ points, ∑ i ∈ indices, if R i x then (1 : ℕ) else 0 := sum_comm
    _ = _ := by simp

/-- Count an incident point and a (k)-set of its incident indices in either order. -/
theorem sum_choose_incidence {I X : Type*} [DecidableEq I] (indices : Finset I)
    (points : Finset X) (R : I → X → Prop) [DecidableRel R] (k : ℕ) :
    (∑ x ∈ points, (indices.filter (fun i => R i x)).card.choose k) =
      ∑ J ∈ indices.powersetCard k, (points.filter (fun x => ∀ i ∈ J, R i x)).card := by
  classical
  have hfiber (x : X) :
      (indices.filter (fun i => R i x)).powersetCard k =
        (indices.powersetCard k).filter (fun J => ∀ i ∈ J, R i x) := by
    ext J
    simp only [mem_powersetCard, mem_filter]
    constructor
    · rintro ⟨hsub, hcard⟩
      exact ⟨⟨fun i hi => (mem_filter.mp (hsub hi)).1, hcard⟩,
        fun i hi => (mem_filter.mp (hsub hi)).2⟩
    · rintro ⟨⟨hsub, hcard⟩, hR⟩
      exact ⟨fun i hi => mem_filter.mpr ⟨hsub hi, hR i hi⟩, hcard⟩
  calc
    _ = ∑ x ∈ points, ((indices.powersetCard k).filter (fun J => ∀ i ∈ J, R i x)).card := by
      apply sum_congr rfl
      intro x _
      rw [← hfiber, card_powersetCard]
    _ = _ := (sum_filter_card_comm (indices.powersetCard k) points
      (fun J x => ∀ i ∈ J, R i x)).symm

/-- Four subsets of a 15-set, each with at least 11 members, have a pair
whose intersection has at least eight members. -/
theorem exists_large_common_pair {I X : Type*} [DecidableEq I]
    (indices : Finset I) (points : Finset X) (R : I → X → Prop) [DecidableRel R]
    (hi : indices.card = 4) (hx : points.card = 15)
    (hLarge : ∀ i ∈ indices, 11 ≤ (points.filter (R i)).card) :
    ∃ J ∈ indices.powersetCard 2, 8 ≤ (points.filter (fun x => ∀ i ∈ J, R i x)).card := by
  classical
  by_contra! hnone
  let m (x : X) := (indices.filter (fun i => R i x)).card
  have hFour (x : X) : m x ≤ 4 := (card_filter_le _ _).trans hi.le
  have hpoint (x : X) : 2 * m x ≤ (m x).choose 2 + 3 := by
    have h := hFour x
    have hcases : m x = 0 ∨ m x = 1 ∨ m x = 2 ∨ m x = 3 ∨ m x = 4 := by omega
    rcases hcases with h0 | h1 | h2 | h3 | h4 <;>
      first | rw [h0] | rw [h1] | rw [h2] | rw [h3] | rw [h4]
    all_goals decide
  have hMult : 44 ≤ ∑ x ∈ points, m x := by
    change 44 ≤ ∑ x ∈ points, (indices.filter fun i => R i x).card
    rw [← sum_filter_card_comm indices points R]
    calc
      44 = ∑ _ ∈ indices, (11 : ℕ) := by rw [sum_const, hi]; decide
      _ ≤ _ := sum_le_sum hLarge
  have hPair : (∑ x ∈ points, (m x).choose 2) ≤ 42 := by
    change (∑ x ∈ points, (indices.filter fun i => R i x).card.choose 2) ≤ 42
    rw [sum_choose_incidence indices points R 2]
    calc
      _ ≤ ∑ _ ∈ indices.powersetCard 2, (7 : ℕ) :=
        sum_le_sum (fun J hJ => by have h := hnone J hJ; omega)
      _ = 42 := by rw [sum_const, card_powersetCard, hi]; decide
  have h := sum_le_sum (s := points) (fun x _ => hpoint x)
  simp only [← mul_sum, sum_add_distrib, sum_const, hx] at h
  rw [show (15 : ℕ) • (3 : ℕ) = 45 by decide] at h
  omega

end OMA.Ramsey55Pattern

/- The outside-neighbor bound for a four-clique in a ((5,5))-graph. -/

namespace OMA.Ramsey55Pattern

open Finset SimpleGraph
open scoped BigOperators

theorem card_lt_of_cliqueFree {V : Type*} {G : SimpleGraph V} {n : ℕ}
    (hFree : G.CliqueFree n) {S : Finset V} (hS : G.IsClique (S : Set V)) :
    S.card < n := by
  by_contra! hcard
  obtain ⟨T, hTS, hc⟩ := exists_subset_card_eq hcard
  exact hFree T ⟨hS.subset (show (T : Set V) ⊆ ↑S from hTS), hc⟩

/-- In a graph with no five-clique the common neighbors of a three-clique
form a clique of the complement. -/
theorem common_neighbors_clique_compl {V : Type*} [DecidableEq V]
    {G : SimpleGraph V} (hG : G.CliqueFree 5) {T U : Finset V}
    (hT : G.IsNClique 3 T) (hU : ∀ u ∈ U, ∀ t ∈ T, G.Adj u t) :
    Gᶜ.IsClique (U : Set V) := by
  intro a ha b hb hne
  refine (G.compl_adj a b).mpr ⟨hne, fun hab => ?_⟩
  have h4 := hT.insert (a := a) (hU a ha)
  apply hG (insert b (insert a T))
  apply h4.insert
  intro t ht
  rcases mem_insert.mp ht with (rfl | htT)
  · exact hab.symm
  · exact hU b hb t htT

/-- In a ((5,5))-graph, a four-clique sends at most (2|O|+12) incidences
to any disjoint set of vertices (O). -/
theorem clique_four_outside_bound {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hK : G.CliqueFree 5) (hI : Gᶜ.CliqueFree 5)
    (Q O : Finset V) (hQ : G.IsNClique 4 Q) (hDisj : Disjoint Q O) :
    (∑ q ∈ Q, (O.filter (fun u => G.Adj u q)).card) ≤ 2 * O.card + 12 := by
  classical
  let m (u : V) := (Q.filter (G.Adj u)).card
  have hSmall (u : V) (hu : u ∈ O) : m u ≤ 3 := by
    let C := Q.filter (G.Adj u)
    have huQ : u ∉ Q := fun huQ => Finset.disjoint_left.mp hDisj huQ hu
    have hC : G.IsClique (C : Set V) := hQ.isClique.subset (Finset.filter_subset _ _)
    have hclique : G.IsClique ((insert u C : Finset V) : Set V) := by
      rw [coe_insert]
      exact hC.insert fun v hv _ => (Finset.mem_filter.mp hv).2
    have hcard := card_lt_of_cliqueFree hK hclique
    rw [card_insert_of_notMem (fun h => huQ ((Finset.mem_filter.mp h).1))] at hcard
    change m u + 1 < 5 at hcard
    omega
  have hPoints (u : V) (hu : u ∈ O) : m u ≤ 2 + (m u).choose 3 := by
    have h := hSmall u hu
    have hc : m u = 0 ∨ m u = 1 ∨ m u = 2 ∨ m u = 3 := by omega
    rcases hc with h0 | h1 | h2 | h3 <;>
      first | rw [h0] | rw [h1] | rw [h2] | rw [h3]
    all_goals decide
  have hTriple (T : Finset V) (hT : T ∈ Q.powersetCard 3) :
      (O.filter (fun x => ∀ t ∈ T, G.Adj x t)).card ≤ 3 := by
    obtain ⟨hTQ, hTcard⟩ := mem_powersetCard.mp hT
    have hc : G.IsNClique 3 T :=
      ⟨hQ.isClique.subset (show (T : Set V) ⊆ ↑Q from hTQ), hTcard⟩
    obtain ⟨q, hqQ, hqT⟩ :=
      exists_mem_notMem_of_card_lt_card (s := T) (t := Q) (by rw [hTcard, hQ.card_eq]; decide)
    let U := O.filter (fun x => ∀ t ∈ T, G.Adj x t)
    have hqU : q ∉ U := fun hqU =>
      Finset.disjoint_left.mp hDisj hqQ (Finset.mem_filter.mp hqU).1
    have hCommon : ∀ x ∈ insert q U, ∀ t ∈ T, G.Adj x t := by
      intro x hx t ht
      rcases mem_insert.mp hx with (rfl | hxU)
      · exact hQ.isClique hqQ (hTQ ht) (fun he => hqT (he.symm ▸ ht))
      · exact (Finset.mem_filter.mp hxU).2 t ht
    have h := card_lt_of_cliqueFree hI (common_neighbors_clique_compl hK hc hCommon)
    rw [card_insert_of_notMem hqU] at h
    change U.card ≤ 3
    omega
  have hTotal : (∑ u ∈ O, (m u).choose 3) ≤ 12 := by
    change (∑ u ∈ O, (Q.filter (fun q => G.Adj u q)).card.choose 3) ≤ 12
    rw [sum_choose_incidence Q O (fun q u => G.Adj u q) 3]
    calc
      _ ≤ ∑ _ ∈ Q.powersetCard 3, (3 : ℕ) := sum_le_sum hTriple
      _ = 12 := by rw [sum_const, card_powersetCard, hQ.card_eq]; decide
  rw [sum_filter_card_comm Q O (fun q u => G.Adj u q)]
  have hsum := sum_le_sum (s := O) (fun u hu => hPoints u hu)
  rw [sum_add_distrib, sum_const, Nat.nsmul_eq_mul, mul_comm O.card 2] at hsum
  change (∑ u ∈ O, m u) ≤ _ + _ at hsum
  change (∑ u ∈ O, m u) ≤ _
  omega

end OMA.Ramsey55Pattern

/- Neighbor counts and clique restrictions on a finite induced vertex set. -/

namespace OMA.Ramsey55Pattern

open Finset SimpleGraph

theorem card_lt_of_cliqueFreeOn {V : Type*} {G : SimpleGraph V} {n : ℕ}
    {S T : Finset V} (hFree : G.CliqueFreeOn (S : Set V) n)
    (hTS : T ⊆ S) (hT : G.IsClique (T : Set V)) : T.card < n := by
  by_contra! hcard
  obtain ⟨Q, hQT, hQ⟩ := exists_subset_card_eq hcard
  exact hFree (show (Q : Set V) ⊆ ↑S from hQT.trans hTS)
    ⟨hT.subset (show (Q : Set V) ⊆ ↑T from hQT), hQ⟩

theorem induce_compl_eq {V : Type*} (G : SimpleGraph V) (S : Set V) :
    (G.induce S)ᶜ = Gᶜ.induce S := by
  ext a b
  change (a ≠ b ∧ ¬G.Adj (a : V) (b : V)) ↔
    ((a : V) ≠ (b : V) ∧ ¬G.Adj (a : V) (b : V))
  exact and_congr ⟨fun h he => h (Subtype.ext he), fun h he => h (congrArg Subtype.val he)⟩ Iff.rfl

theorem induce_compl_cliqueFreeOn {V : Type*} {G : SimpleGraph V} {S : Set V}
    {n : ℕ} (h : Gᶜ.CliqueFreeOn S n) : (G.induce S)ᶜ.CliqueFree n := by
  rw [induce_compl_eq]
  exact (cliqueFree_induce_iff Gᶜ S n).mpr h

theorem degree_induce_eq_filter_card {V : Type*} (G : SimpleGraph V)
    [DecidableRel G.Adj] (S : Finset V) (v : ↥(S : Set V)) :
    (G.induce (S : Set V)).degree v = (S.filter (G.Adj v)).card := by
  classical
  have h : Fintype.card ((G.induce (S : Set V)).neighborSet v) =
      Fintype.card ↥(S.filter (G.Adj v)) := by
    apply Fintype.card_congr
    exact
      { toFun := fun u => ⟨u.val.val, mem_filter.mpr ⟨u.val.prop, u.prop⟩⟩
        invFun := fun u => ⟨⟨u.val, (mem_filter.mp u.prop).1⟩, (mem_filter.mp u.prop).2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  simpa only [card_neighborSet_eq_degree, Fintype.card_coe] using h

theorem filter_card_adj_add_compl {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) {v : V}
    (hv : v ∈ S) :
    (S.filter (G.Adj v)).card + (S.filter (Gᶜ.Adj v)).card + 1 = S.card := by
  have hadj : (S.erase v).filter (G.Adj v) = S.filter (G.Adj v) := by
    ext x
    simp only [mem_filter, mem_erase]
    exact ⟨fun h => ⟨h.1.2, h.2⟩, fun h => ⟨⟨h.2.ne.symm, h.1⟩, h.2⟩⟩
  have hcompl : ((S.erase v).filter fun x => ¬G.Adj v x) = S.filter (Gᶜ.Adj v) := by
    ext x
    simp only [mem_filter, mem_erase, compl_adj]
    exact ⟨fun h => ⟨h.1.2, h.1.1.symm, h.2⟩, fun h => ⟨⟨h.2.1.symm, h.1⟩, h.2.2⟩⟩
  have h := card_filter_add_card_filter_not (s := S.erase v) (G.Adj v)
  rw [hadj, hcompl, card_erase_of_mem hv] at h
  have hpos := card_pos.mpr ⟨v, hv⟩
  omega

theorem compl_cliqueFreeOn_nonadj {V : Type*} [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {S : Finset V} {v : V} {n : ℕ}
    (h : Gᶜ.CliqueFreeOn (S : Set V) (n + 1)) (hv : v ∈ S) :
    Gᶜ.CliqueFreeOn ((S.filter (Gᶜ.Adj v) : Finset V) : Set V) n := by
  apply (CliqueFreeOn.of_succ Gᶜ h (show v ∈ (S : Set V) from hv)).subset
  intro x hx
  exact mem_filter.mp hx

/-- With no independent triple, the nonneighbors other than the vertex itself
form a clique, so a five-clique-free graph has at most four of them. -/
theorem lower_degree_on_53 {V : Type*} [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {S : Finset V} {v : V}
    (hK : G.CliqueFreeOn (S : Set V) 5) (hI : Gᶜ.CliqueFreeOn (S : Set V) 3)
    (hv : v ∈ S) : S.card ≤ (S.filter (G.Adj v)).card + 5 := by
  let U := S.filter (Gᶜ.Adj v)
  have hfree : Gᶜ.CliqueFreeOn (U : Set V) 2 := compl_cliqueFreeOn_nonadj hI hv
  have hC : G.IsClique (U : Set V) := by
    intro a ha b hb hne
    by_contra hab
    exact ((cliqueFreeOn_two Gᶜ).mp hfree) ha hb hne ((G.compl_adj a b).mpr ⟨hne, hab⟩)
  have hcard := card_lt_of_cliqueFreeOn hK (filter_subset _ _) hC
  have hsum := filter_card_adj_add_compl G S hv
  change U.card < 5 at hcard
  change (S.filter (G.Adj v)).card + U.card + 1 = S.card at hsum
  omega

theorem compl_cliqueFreeOn_after_isolated {V : Type*} [DecidableEq V]
    {G : SimpleGraph V} (hI : Gᶜ.CliqueFree 5) {A S : Finset V} {n : ℕ}
    (hA : Gᶜ.IsClique (A : Set V)) (hDisj : Disjoint A S)
    (hCross : ∀ a ∈ A, ∀ s ∈ S, ¬G.Adj a s) (hCard : A.card + n = 5) :
    Gᶜ.CliqueFreeOn (S : Set V) n := by
  intro T hTS hT
  have hd : Disjoint A T := hDisj.mono_right (show T ⊆ S from hTS)
  apply hI (A ∪ T)
  refine ⟨?_, by rw [card_union_of_disjoint hd, hT.card_eq, hCard]⟩
  change (↑(A ∪ T) : Set V).Pairwise Gᶜ.Adj
  rw [coe_union, Set.pairwise_union]
  refine ⟨hA, hT.isClique, fun a ha b hb hne => ?_⟩
  have hab := (G.compl_adj a b).mpr ⟨hne, hCross a ha b (hTS hb)⟩
  exact ⟨hab, hab.symm⟩

end OMA.Ramsey55Pattern

/-
# The upper bound for the Ramsey number R(3,5)

The neighbors of a vertex in a triangle-free graph are independent, and an
independent set in its nonneighbors can be enlarged by the vertex. The
degree constraints prove the bound for R(3,3); handshaking rules out the
resulting 3-regular graph on nine vertices for R(3,4).
-/

open Finset SimpleGraph
open scoped BigOperators

namespace OMA.Ramsey55Pattern

private theorem degree_lt_of_cliqueFree {V : Type*} {G : SimpleGraph V}
    {k : ℕ} (v : V) [Fintype (G.neighborSet v)]
    (hT : G.CliqueFree 3) (hI : Gᶜ.CliqueFree k) :
    G.degree v < k := by
  classical
  by_contra! h
  obtain ⟨s, hsub, hs⟩ := exists_subset_card_eq
    (show k ≤ (G.neighborFinset v).card from h)
  have hc : Gᶜ.IsClique (G.neighborFinset v : Set V) := by
    rw [coe_neighborFinset, isClique_compl]
    exact G.isIndepSet_neighborSet_of_triangleFree hT v
  exact hI s ⟨hc.subset hsub, hs⟩

private theorem induce_free {V : Type*} {G : SimpleGraph V} {k : ℕ}
    (h : G.CliqueFree k) (S : Set V) : (G.induce S).CliqueFree k := by
  intro t ht
  exact h _ ((G.isNClique_induce_iff S t k).mp ht)

private theorem ramsey35_induce_compl_eq {V : Type*} (G : SimpleGraph V) (S : Set V) :
    (G.induce S)ᶜ = Gᶜ.induce S := by
  ext x y
  simp only [compl_adj, induce_adj]
  refine and_congr ?_ Iff.rfl
  exact ⟨fun h h' => h (Subtype.ext h'), fun h h' => h (congrArg Subtype.val h')⟩

private theorem anti_induce_free {V : Type*} {G : SimpleGraph V} {k : ℕ}
    (h : Gᶜ.CliqueFree (k + 1)) (v : V) :
    (G.induce (Gᶜ.neighborSet v))ᶜ.CliqueFree k := by
  classical
  rw [ramsey35_induce_compl_eq]
  intro t ht
  let S := Gᶜ.neighborSet v
  let e : S ↪ V := .subtype _
  let u := t.map e
  have hu : Gᶜ.IsNClique k u := (Gᶜ.isNClique_induce_iff S t k).mp ht
  have hadj (x : V) (hx : x ∈ u) : Gᶜ.Adj v x := by
    obtain ⟨z, _, rfl⟩ := mem_map.mp hx
    exact z.property
  have hv : v ∉ u := fun hv => Gᶜ.irrefl (hadj v hv)
  have hc : Gᶜ.IsClique (insert v (u : Set V)) :=
    hu.isClique.insert (fun x hx _ => hadj x hx)
  exact h (insert v u) ⟨by simpa only [coe_insert] using hc,
    by rw [card_insert_of_notMem hv, hu.card_eq]⟩

private theorem ramsey33_of_card {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hV : 6 ≤ Fintype.card V) : ¬ (G.CliqueFree 3 ∧ Gᶜ.CliqueFree 3) := by
  classical
  rintro ⟨hT, hI⟩
  obtain ⟨v⟩ := Fintype.card_pos_iff.mp (show 0 < Fintype.card V by omega)
  have h₁ := degree_lt_of_cliqueFree v hT hI
  have hT' : Gᶜᶜ.CliqueFree 3 := by simpa only [compl_compl] using hT
  have h₂ := degree_lt_of_cliqueFree v hI hT'
  have hsum := G.degree_compl v
  omega

private theorem ramsey34_of_card {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hV : 9 ≤ Fintype.card V) : ¬ (G.CliqueFree 3 ∧ Gᶜ.CliqueFree 4) := by
  classical
  rintro ⟨hT, hI⟩
  have hdeg_upper (v : V) := degree_lt_of_cliqueFree v hT hI
  have hanti (v : V) : Gᶜ.degree v < 6 := by
    by_contra! h
    have hc : 6 ≤ Fintype.card (Gᶜ.neighborSet v) := by
      simpa only [card_neighborSet_eq_degree] using h
    exact ramsey33_of_card _ hc ⟨induce_free hT _, anti_induce_free hI v⟩
  obtain ⟨v₀⟩ := Fintype.card_pos_iff.mp (show 0 < Fintype.card V by omega)
  have hcard : Fintype.card V = 9 := by
    have h₁ := hdeg_upper v₀
    have h₂ := hanti v₀
    have h₃ := G.degree_compl v₀
    omega
  have hdeg (v : V) : G.degree v = 3 := by
    have h₁ := hdeg_upper v
    have h₂ := hanti v
    have h₃ := G.degree_compl v
    omega
  have hhand := G.sum_degrees_eq_twice_card_edges
  simp only [hdeg, sum_const, card_univ, Nat.nsmul_eq_mul, hcard] at hhand
  omega

theorem ramsey35_upper_of_card {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hV : 14 ≤ Fintype.card V) : ¬ (G.CliqueFree 3 ∧ Gᶜ.CliqueFree 5) := by
  classical
  rintro ⟨hT, hI⟩
  obtain ⟨v⟩ := Fintype.card_pos_iff.mp (show 0 < Fintype.card V by omega)
  have hdeg := degree_lt_of_cliqueFree v hT hI
  have hanti := G.degree_compl v
  have hc : 9 ≤ Fintype.card (Gᶜ.neighborSet v) := by
    rw [card_neighborSet_eq_degree]
    omega
  exact ramsey34_of_card _ hc ⟨induce_free hT _, anti_induce_free hI v⟩

theorem ramsey35_upper :
    ∀ G : SimpleGraph (Fin 14), ¬ (G.CliqueFree 3 ∧ Gᶜ.CliqueFree 5) := by
  intro G
  exact ramsey35_upper_of_card G (by simp)

end OMA.Ramsey55Pattern

/- The three- and four-vertex cases for the second neighborhood class. -/

namespace OMA.Ramsey55Pattern

open Finset SimpleGraph

theorem shared_nonadj_card_bound {V : Type*} [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hK : G.CliqueFree 5) (hI : Gᶜ.CliqueFree 5)
    {B C J : Finset V} (hBC : Disjoint B C) (hB : Gᶜ.IsClique (B : Set V))
    (hBdeg : ∀ b ∈ B, ((B ∪ C).filter (G.Adj b)).card ≤ 4)
    (hBsize : 3 ≤ B.card) (hJB : J ⊆ B) (hJsize : J.card = 2) :
    (C.filter (fun x => ∀ j ∈ J, ¬G.Adj j x)).card + B.card ≤ 11 := by
  classical
  let U := C.filter (fun x => ∀ j ∈ J, ¬G.Adj j x)
  let S := (B \ J) ∪ U
  have hUS : U ⊆ C := filter_subset _ _
  have hBU : Disjoint (B \ J) U := hBC.mono sdiff_subset hUS
  have hJS : Disjoint J S := by
    apply Finset.disjoint_left.mpr
    intro j hj hjs
    rcases mem_union.mp hjs with hj' | hj'
    · exact (mem_sdiff.mp hj').2 hj
    · exact Finset.disjoint_left.mp hBC (hJB hj) (hUS hj')
  have hCross : ∀ j ∈ J, ∀ x ∈ S, ¬G.Adj j x := by
    intro j hj x hx
    rcases mem_union.mp hx with hx' | hx'
    · have hxb := mem_sdiff.mp hx'
      have hne : j ≠ x := fun he => hxb.2 (he ▸ hj)
      exact ((G.compl_adj j x).mp (hB (hJB hj) hxb.1 hne)).2
    · exact (mem_filter.mp hx').2 j hj
  have hNoIndep3 : Gᶜ.CliqueFreeOn (S : Set V) 3 :=
    compl_cliqueFreeOn_after_isolated hI (hB.subset (show (J : Set V) ⊆ ↑B from hJB))
      hJS hCross (by omega)
  obtain ⟨v, hv⟩ := card_pos.mp (show 0 < (B \ J).card by
    rw [card_sdiff_of_subset hJB]; omega)
  have hvS : v ∈ S := mem_union_left _ hv
  have hDegree := lower_degree_on_53 hK.cliqueFreeOn hNoIndep3 hvS
  have hFilter : (S.filter (G.Adj v)).card ≤ 4 := by
    apply le_trans _ (hBdeg v (mem_sdiff.mp hv).1)
    apply card_mono
    apply filter_subset_filter
    exact union_subset (sdiff_subset.trans (subset_union_left (s₂ := C)))
      (hUS.trans (subset_union_right (s₁ := B)))
  have hSize : S.card = B.card - 2 + U.card := by
    rw [card_union_of_disjoint hBU, card_sdiff_of_subset hJB, hJsize]
  change U.card + B.card ≤ 11
  omega

theorem exclude_weight23_many_low {V : Type*} [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hK : G.CliqueFree 5) (hI : Gᶜ.CliqueFree 5)
    {B C : Finset V} (hBC : Disjoint B C) (hB : Gᶜ.IsClique (B : Set V))
    (hBdeg : ∀ b ∈ B, ((B ∪ C).filter (G.Adj b)).card ≤ 4)
    (hsize : 2 * B.card + C.card = 23) (hBsize : B.card = 3 ∨ B.card = 4) :
    False := by
  classical
  have hMany (b : V) (hb : b ∈ B) :
      C.card ≤ (C.filter (fun x => ¬G.Adj b x)).card + 4 := by
    have hc := card_filter_add_card_filter_not (s := C) (G.Adj b)
    have hdeg := (card_mono (filter_subset_filter (p := G.Adj b)
      (subset_union_right (s₁ := B) (s₂ := C)))).trans (hBdeg b hb)
    omega
  have hBounds := fun J hJ hc => shared_nonadj_card_bound hK hI hBC hB hBdeg
    (show 3 ≤ B.card by omega) (J := J) hJ hc
  rcases hBsize with hb3 | hb4
  · have hc17 : C.card = 17 := by omega
    obtain ⟨J, hJB, hJ⟩ := exists_subset_card_eq (s := B) (n := 2) (by omega)
    have hSmall := hBounds J hJB hJ
    obtain ⟨a, b, _, rfl⟩ := card_eq_two.mp hJ
    have ha : a ∈ B := hJB (by simp)
    have hb : b ∈ B := hJB (by simp)
    let U₁ := C.filter (fun x => ¬G.Adj a x)
    let U₂ := C.filter (fun x => ¬G.Adj b x)
    have hEq : C.filter (fun x => ∀ j ∈ ({a, b} : Finset V), ¬G.Adj j x) = U₁ ∩ U₂ := by
      ext x
      simp [U₁, U₂, and_assoc, and_left_comm]
    rw [hEq] at hSmall
    have hCard := card_inter_add_card_union U₁ U₂
    have hSize : (U₁ ∪ U₂).card ≤ C.card :=
      card_mono (union_subset (filter_subset _ _) (filter_subset _ _))
    have ha' : C.card ≤ U₁.card + 4 := hMany a ha
    have hb' : C.card ≤ U₂.card + 4 := hMany b hb
    omega
  · have hc15 : C.card = 15 := by omega
    obtain ⟨J, hJ, hLarge⟩ := exists_large_common_pair B C (fun b x => ¬G.Adj b x)
      hb4 hc15 (fun b hb => by have h := hMany b hb; omega)
    have hSmall := hBounds J (mem_powersetCard.mp hJ).1 (mem_powersetCard.mp hJ).2
    omega

end OMA.Ramsey55Pattern

/- Degree budgets for a selected four-clique in Angeltveit–McKay, Proposition 5.3. -/

namespace OMA.Ramsey55Pattern

open Finset SimpleGraph
open scoped BigOperators

theorem clique_four_degree_budget {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hK : G.CliqueFree 5) (hI : Gᶜ.CliqueFree 5)
    {Q S : Finset V} (hQ : G.IsNClique 4 Q) (hQS : Q ⊆ S) :
    (∑ q ∈ Q, G.degree q) ≤
      (∑ q ∈ Q, (S.filter (G.Adj q)).card) + 2 * (Fintype.card V - S.card) + 12 := by
  classical
  let O := univ \ S
  have hDisj : Disjoint S O := disjoint_sdiff
  have hUnion : S ∪ O = univ := by ext x; simp [O]
  have hCard : O.card = Fintype.card V - S.card := by
    simp [O, card_sdiff_of_subset (subset_univ S)]
  have hSplit (q : V) :
      G.degree q = (S.filter (G.Adj q)).card + (O.filter (fun u => G.Adj u q)).card := by
    rw [← card_neighborFinset_eq_degree, neighborFinset_eq_filter, ← hUnion,
      filter_union, card_union_of_disjoint
        (hDisj.mono (filter_subset _ _) (filter_subset _ _))]
    have hComm : O.filter (G.Adj q) = O.filter (fun u => G.Adj u q) :=
      filter_congr fun u _ => G.adj_comm q u
    rw [hComm]
  simp_rw [hSplit, sum_add_distrib]
  have hOutside := clique_four_outside_bound G hK hI Q O hQ (hDisj.mono_left hQS)
  rw [hCard] at hOutside
  omega

theorem clique_four_degree_lower {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {Q D : Finset V} (hQ : Q.card = 4)
    (hD : D.card ≤ 1) (hMin : ∀ v ∈ Q, 21 ≤ G.degree v)
    (hBig : ∀ v ∈ Q, v ∉ D → 22 ≤ G.degree v) :
    87 ≤ ∑ v ∈ Q, G.degree v := by
  classical
  have hb (v : V) (hv : v ∈ Q) :
      (22 : ℕ) ≤ G.degree v + if v ∈ D then 1 else 0 := by
    split
    · have hh := hMin v hv
      omega
    · have hh := hBig v hv ‹v ∉ D›
      omega
  have hsum := sum_le_sum (s := Q) (fun v hv => hb v hv)
  simp only [sum_const, hQ, Nat.nsmul_eq_mul, sum_add_distrib, sum_boole, Nat.cast_id] at hsum
  have hfilter : (Q.filter fun v => v ∈ D).card ≤ D.card := by
    apply card_mono
    intro v hv
    exact (mem_filter.mp hv).2
  omega

theorem clique_four_degree_lower_all {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {Q : Finset V} (hQ : Q.card = 4)
    (hBig : ∀ v ∈ Q, 22 ≤ G.degree v) :
    88 ≤ ∑ v ∈ Q, G.degree v := by
  calc
    88 = ∑ _ ∈ Q, (22 : ℕ) := by rw [sum_const, hQ]; decide
    _ ≤ _ := sum_le_sum hBig

end OMA.Ramsey55Pattern

/-
# The one-class-one case of the exceptional weight bound

This is the weight-23 case with one isolated class-one vertex in
Angeltveit–McKay, Proposition 5.3. Lemma 5.1 supplies the input for induced
17-vertex graphs.
-/

namespace OMA.Ramsey55Pattern

open Finset SimpleGraph

theorem exclude_large_capped_54 {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {M : Finset V}
    (hK : G.CliqueFreeOn (M : Set V) 5) (hI : Gᶜ.CliqueFreeOn (M : Set V) 4)
    (hMdeg : ∀ x ∈ M, (M.filter (G.Adj x)).card ≤ 7) (hCard : 17 ≤ M.card)
    (h17 : ∀ (V : Type) [Fintype V] [DecidableEq V] (H : SimpleGraph V)
      [DecidableRel H.Adj], Fintype.card V = 17 →
        H.CliqueFree 5 → Hᶜ.CliqueFree 4 → ∃ v, 8 ≤ H.degree v) : False := by
  classical
  obtain ⟨S, hSM, hS⟩ := exists_subset_card_eq hCard
  let H := G.induce (S : Set V)
  have hSubtype : Fintype.card ↥(S : Set V) = 17 :=
    (Fintype.card_coe S).trans hS
  have hSK : H.CliqueFree 5 := (G.cliqueFree_induce_iff (S : Set V) 5).mpr
    (CliqueFreeOn.subset G (show (S : Set V) ⊆ (M : Set V) from hSM) hK)
  have hSI : Hᶜ.CliqueFree 4 := induce_compl_cliqueFreeOn
    (CliqueFreeOn.subset Gᶜ (show (S : Set V) ⊆ (M : Set V) from hSM) hI)
  obtain ⟨v, hv⟩ := h17 ↥(S : Set V) H hSubtype hSK hSI
  have hEq : H.degree v = (S.filter (G.Adj v.val)).card := degree_induce_eq_filter_card G S v
  have hCardMono := card_le_card (filter_subset_filter (G.Adj v.val) hSM)
  have hUpper := hMdeg v.val (hSM v.property)
  omega

theorem exclude_weight23_one {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {B M : Finset V}
    (hBsub : B ⊆ M) (hB : Gᶜ.IsClique (B : Set V))
    (hK : G.CliqueFreeOn (M : Set V) 5) (hI : Gᶜ.CliqueFreeOn (M : Set V) 4)
    (hBdeg : ∀ b ∈ B, (M.filter (G.Adj b)).card ≤ 4)
    (hMdeg : ∀ x ∈ M, (M.filter (G.Adj x)).card ≤ 7)
    (hCard : B.card + M.card = 18)
    (h17 : ∀ (V : Type) [Fintype V] [DecidableEq V] (H : SimpleGraph V)
      [DecidableRel H.Adj], Fintype.card V = 17 →
        H.CliqueFree 5 → Hᶜ.CliqueFree 4 → ∃ v, 8 ≤ H.degree v) : False := by
  classical
  by_cases hSmall : B.card ≤ 1
  · exact exclude_large_capped_54 G hK hI hMdeg (by omega) h17
  · have hBlt := card_lt_of_cliqueFreeOn hI hBsub hB
    obtain ⟨b, hb⟩ := card_pos.mp (show 0 < B.card by omega)
    obtain ⟨c, hc⟩ := card_pos.mp (show 0 < (B.erase b).card by
      rw [card_erase_of_mem hb]
      omega)
    obtain ⟨hcb, hcB⟩ := mem_erase.mp hc
    let N := M.filter (Gᶜ.Adj b)
    have hcN : c ∈ N := mem_filter.mpr ⟨hBsub hcB, hB hb hcB hcb.symm⟩
    have hNsub : N ⊆ M := filter_subset _ _
    have hNcard : 10 ≤ N.card := by
      have hSum := filter_card_adj_add_compl G M (hBsub hb)
      have hUpper := hBdeg b hb
      change (M.filter (G.Adj b)).card + N.card + 1 = M.card at hSum
      omega
    have hNK : G.CliqueFreeOn (N : Set V) 5 :=
      CliqueFreeOn.subset G (show (N : Set V) ⊆ (M : Set V) from hNsub) hK
    have hNI : Gᶜ.CliqueFreeOn (N : Set V) 3 := compl_cliqueFreeOn_nonadj hI (hBsub hb)
    have hLower := lower_degree_on_53 hNK hNI hcN
    have hCardMono := card_le_card (filter_subset_filter (G.Adj c) hNsub)
    have hUpper := hBdeg c hcB
    omega

end OMA.Ramsey55Pattern

/- Saturation of the exceptional weight bound with two isolated vertices. -/

namespace OMA.Ramsey55Pattern

open Finset SimpleGraph

/-- After removing two isolated vertices, weight at least 23 forces the other
exceptional vertices to form the thirteen-vertex class counted by `D`. -/
theorem weight_two_profile {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {B C D : Finset V}
    (hBC : Disjoint B C) (hDC : D ⊆ C)
    (hK : G.CliqueFreeOn ((B ∪ C : Finset V) : Set V) 5)
    (hI : Gᶜ.CliqueFreeOn ((B ∪ C : Finset V) : Set V) 3)
    (hB : Gᶜ.IsClique (B : Set V))
    (hBdeg : ∀ b ∈ B, ((B ∪ C).filter (G.Adj b)).card ≤ 4)
    (hCdeg : ∀ c ∈ C, c ∉ D → ((B ∪ C).filter (G.Adj c)).card ≤ 7)
    (hWeight : 23 ≤ 10 + 2 * B.card + C.card) :
    10 + 2 * B.card + C.card = 23 ∧ D.card = 13 := by
  have hBcard : B.card ≤ 2 :=
    Nat.le_of_lt_succ (card_lt_of_cliqueFreeOn hI subset_union_left hB)
  have hUnion := card_union_of_disjoint hBC
  have hBempty : B = ∅ := by
    apply not_nonempty_iff_eq_empty.mp
    rintro ⟨b, hb⟩
    have hlo := lower_degree_on_53 hK hI (mem_union_left C hb)
    have hhi := hBdeg b hb
    omega
  have hBzero : B.card = 0 := by simp [hBempty]
  have hCupper : C.card ≤ 13 := by
    by_contra! hlarge
    let S := ((B ∪ C : Finset V) : Set V)
    have hCard : 14 ≤ Fintype.card ↥S := by
      change 14 ≤ Fintype.card ↥(B ∪ C : Finset V)
      rw [Fintype.card_coe]
      omega
    have hTriangle : (G.induce S)ᶜ.CliqueFree 3 := induce_compl_cliqueFreeOn hI
    have hFive : (G.induce S).CliqueFree 5 := (cliqueFree_induce_iff G S 5).mpr hK
    have hFive' : (G.induce S)ᶜᶜ.CliqueFree 5 := by
      simpa only [compl_compl] using hFive
    exact ramsey35_upper_of_card (G.induce S)ᶜ hCard ⟨hTriangle, hFive'⟩
  have hCcard : C.card = 13 := by omega
  have hCD : C ⊆ D := by
    intro c hc
    by_contra hn
    have hlo := lower_degree_on_53 hK hI (mem_union_right B hc)
    have hhi := hCdeg c hc hn
    omega
  have hD : D = C := subset_antisymm hDC hCD
  exact ⟨by omega, by rw [hD, hCcard]⟩

end OMA.Ramsey55Pattern

/- Weight 23 with no isolated first-class vertices in Proposition 5.3. -/

namespace OMA.Ramsey55Pattern

open Finset SimpleGraph
open scoped BigOperators

private theorem exclude_twentyThree_nonexceptional
    (G : SimpleGraph (Fin 46)) [DecidableRel G.Adj]
    (hK : G.CliqueFree 5) (hI : Gᶜ.CliqueFree 5) {S D : Finset (Fin 46)}
    (hS : S.card = 23) (hD : D.card ≤ 1)
    (hSmall : ∀ x ∈ S, (S.filter (G.Adj x)).card ≤ 7)
    (hBig : ∀ x ∈ S, x ∉ D → 22 ≤ G.degree x)
    (h22 : ∀ (V : Type) [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj],
      Fintype.card V = 22 → H.CliqueFree 4 → Hᶜ.CliqueFree 5 → ∃ v, 8 ≤ H.degree v) :
    False := by
  classical
  let U := S \ D
  have hUS : U ⊆ S := sdiff_subset
  have hNoClique (Q : Finset (Fin 46)) (hQU : Q ⊆ U) (hQ : G.IsNClique 4 Q) : False := by
    have hQS := hQU.trans hUS
    have hInside : (∑ q ∈ Q, (S.filter (G.Adj q)).card) ≤ 28 := by
      calc
        _ ≤ ∑ _ ∈ Q, (7 : ℕ) := sum_le_sum fun q hq => hSmall q (hQS hq)
        _ = 28 := by rw [sum_const, hQ.card_eq]; decide
    have hLower := clique_four_degree_lower_all G hQ.card_eq (fun q hq =>
      hBig q (hQS hq) (mem_sdiff.mp (hQU hq)).2)
    have hBudget := clique_four_degree_budget G hK hI hQ hQS
    rw [hS, Fintype.card_fin] at hBudget
    omega
  obtain ⟨T, hTU, hCard⟩ := exists_subset_card_eq (s := U) (n := 22) (by
    have hd := le_card_sdiff D S
    change S.card - D.card ≤ U.card at hd
    omega)
  let H := G.induce (T : Set (Fin 46))
  have hHK : H.CliqueFree 4 := by
    refine (cliqueFree_induce_iff G _ 4).mpr ?_
    intro Q hQT hQ
    exact hNoClique Q ((show Q ⊆ T from hQT).trans hTU) hQ
  have hHI : Hᶜ.CliqueFree 5 := induce_compl_cliqueFreeOn hI.cliqueFreeOn
  obtain ⟨v, hv⟩ := h22 (↥(T : Set (Fin 46))) H (by simpa using hCard) hHK hHI
  change 8 ≤ (G.induce (T : Set (Fin 46))).degree v at hv
  rw [degree_induce_eq_filter_card] at hv
  have hFilter := card_mono (filter_subset_filter (p := G.Adj v) (hTU.trans hUS))
  have hCap := hSmall v (hUS (hTU v.property))
  omega

private theorem exclude_twentyOne_two_low
    (G : SimpleGraph (Fin 46)) [DecidableRel G.Adj]
    (hK : G.CliqueFree 5) (hI : Gᶜ.CliqueFree 5) {S D : Finset (Fin 46)}
    (hS : S.card = 21) (hD : D.card ≤ 1)
    (hSmall : ∀ x ∈ S, (S.filter (G.Adj x)).card ≤ 7)
    (hMin : ∀ x ∈ S, 21 ≤ G.degree x)
    (hBig : ∀ x ∈ S, x ∉ D → 22 ≤ G.degree x)
    {a b : Fin 46} (ha : a ∈ S) (hb : b ∈ S) (hab : a ≠ b) (hN : ¬G.Adj a b)
    (ha4 : (S.filter (G.Adj a)).card ≤ 4) (hb4 : (S.filter (G.Adj b)).card ≤ 4)
    (h21 : ∀ (V : Type) [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj],
      Fintype.card V = 21 → H.CliqueFree 5 → Hᶜ.CliqueFree 5 →
      ∀ a b : V, a ≠ b → ¬H.Adj a b → H.degree a ≤ 4 → H.degree b ≤ 4 →
        (∃ v, 8 ≤ H.degree v) ∨
          ∃ Q : Finset V, H.IsNClique 4 Q ∧ (∑ q ∈ Q, H.degree q) ≤ 24) :
    False := by
  classical
  let H := G.induce (S : Set (Fin 46))
  let a' : ↥(S : Set (Fin 46)) := ⟨a, ha⟩
  let b' : ↥(S : Set (Fin 46)) := ⟨b, hb⟩
  have ha' : H.degree a' ≤ 4 := by
    change (G.induce (S : Set (Fin 46))).degree a' ≤ 4
    rw [degree_induce_eq_filter_card]
    exact ha4
  have hb' : H.degree b' ≤ 4 := by
    change (G.induce (S : Set (Fin 46))).degree b' ≤ 4
    rw [degree_induce_eq_filter_card]
    exact hb4
  have hHK : H.CliqueFree 5 := (cliqueFree_induce_iff G _ 5).mpr hK.cliqueFreeOn
  have hHI : Hᶜ.CliqueFree 5 := induce_compl_cliqueFreeOn hI.cliqueFreeOn
  obtain ⟨v, hv⟩ | ⟨P, hP, hPsum⟩ :=
    h21 (↥(S : Set (Fin 46))) H (by simpa using hS) hHK hHI a' b'
      (fun he => hab (congrArg Subtype.val he)) hN ha' hb'
  · change 8 ≤ (G.induce (S : Set (Fin 46))).degree v at hv
    rw [degree_induce_eq_filter_card] at hv
    exact (not_le_of_gt hv) (hSmall v v.property)
  · let e : ↥(S : Set (Fin 46)) ↪ Fin 46 := Function.Embedding.subtype _
    let Q := P.map e
    have hQS : Q ⊆ S := by
      intro q hq
      obtain ⟨v, _, rfl⟩ := mem_map.mp hq
      exact v.property
    have hQ : G.IsNClique 4 Q := by
      refine ⟨?_, (card_map e).trans hP.card_eq⟩
      intro q hq r hr hqr
      obtain ⟨q', hq', rfl⟩ := mem_map.mp hq
      obtain ⟨r', hr', rfl⟩ := mem_map.mp hr
      exact hP.isClique hq' hr' (fun he => hqr (congrArg e he))
    have hInside : (∑ q ∈ Q, (S.filter (G.Adj q)).card) ≤ 24 := by
      change (∑ q ∈ P.map e, (S.filter (G.Adj q)).card) ≤ 24
      rw [sum_map]
      have hEq : ∀ q : ↥(S : Set (Fin 46)), (S.filter (G.Adj (e q))).card = H.degree q :=
        fun q => (degree_induce_eq_filter_card G S q).symm
      simp only [hEq]
      exact hPsum
    have hLower := clique_four_degree_lower G hQ.card_eq hD
      (fun q hq => hMin q (hQS hq)) (fun q hq => hBig q (hQS hq))
    have hBudget := clique_four_degree_budget G hK hI hQ hQS
    rw [hS, Fintype.card_fin] at hBudget
    omega

theorem exclude_weight23_zero
    (G : SimpleGraph (Fin 46)) [DecidableRel G.Adj]
    (hK : G.CliqueFree 5) (hI : Gᶜ.CliqueFree 5) {B M D : Finset (Fin 46)}
    (hBsub : B ⊆ M) (hB : Gᶜ.IsClique (B : Set (Fin 46)))
    (hBdeg : ∀ x ∈ B, (M.filter (G.Adj x)).card ≤ 4)
    (hMdeg : ∀ x ∈ M, (M.filter (G.Adj x)).card ≤ 7)
    (hCard : B.card + M.card = 23) (hD : D.card ≤ 1)
    (hMin : ∀ x ∈ M, 21 ≤ G.degree x)
    (hBig : ∀ x ∈ M, x ∉ D → 22 ≤ G.degree x)
    (h17 : ∀ (V : Type) [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj],
      Fintype.card V = 17 → H.CliqueFree 5 → Hᶜ.CliqueFree 4 → ∃ v, 8 ≤ H.degree v)
    (h21 : ∀ (V : Type) [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj],
      Fintype.card V = 21 → H.CliqueFree 5 → Hᶜ.CliqueFree 5 →
      ∀ a b : V, a ≠ b → ¬H.Adj a b → H.degree a ≤ 4 → H.degree b ≤ 4 →
        (∃ v, 8 ≤ H.degree v) ∨
          ∃ Q : Finset V, H.IsNClique 4 Q ∧ (∑ q ∈ Q, H.degree q) ≤ 24)
    (h22 : ∀ (V : Type) [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj],
      Fintype.card V = 22 → H.CliqueFree 4 → Hᶜ.CliqueFree 5 → ∃ v, 8 ≤ H.degree v) :
    False := by
  classical
  have hBsize := card_lt_of_cliqueFree hI hB
  rcases (show B.card = 0 ∨ B.card = 1 ∨ B.card = 2 ∨ B.card = 3 ∨ B.card = 4 by omega)
    with h0 | h1 | h2 | h34
  · exact exclude_twentyThree_nonexceptional G hK hI (by omega) hD hMdeg hBig h22
  · obtain ⟨b, hb⟩ := card_pos.mp (show 0 < B.card by omega)
    let T := M.filter (Gᶜ.Adj b)
    have hTsub : T ⊆ M := filter_subset _ _
    have hTsize : 17 ≤ T.card := by
      have h := filter_card_adj_add_compl G M (hBsub hb)
      have hd := hBdeg b hb
      change (M.filter (G.Adj b)).card + T.card + 1 = M.card at h
      omega
    have hTI : Gᶜ.CliqueFreeOn (T : Set (Fin 46)) 4 :=
      compl_cliqueFreeOn_nonadj hI.cliqueFreeOn (hBsub hb)
    apply exclude_large_capped_54 G hK.cliqueFreeOn hTI _ hTsize h17
    intro x hx
    exact (card_mono (filter_subset_filter (p := G.Adj x) hTsub)).trans (hMdeg x (hTsub hx))
  · have hMcard : M.card = 21 := by omega
    obtain ⟨a, b, hne, rfl⟩ := card_eq_two.mp h2
    have ha : a ∈ ({a,b} : Finset (Fin 46)) := by simp
    have hb : b ∈ ({a,b} : Finset (Fin 46)) := by simp
    exact exclude_twentyOne_two_low G hK hI hMcard hD hMdeg hMin hBig
      (hBsub ha) (hBsub hb) hne ((G.compl_adj a b).mp (hB ha hb hne)).2
      (hBdeg a ha) (hBdeg b hb) h21
  · let C := M \ B
    have hBC : Disjoint B C := disjoint_sdiff
    have hM : B ∪ C = M := by
      ext x
      simp [C]
      exact fun hx => hBsub hx
    have hMC : M.card = B.card + C.card := by rw [← hM, card_union_of_disjoint hBC]
    apply exclude_weight23_many_low hK hI hBC hB _ (by omega) h34
    intro b hb
    simpa only [hM] using hBdeg b hb

end OMA.Ramsey55Pattern

/- Bounds for isolated class-one vertices in the exceptional subgraph. -/

namespace OMA.Ramsey55Pattern

open Finset SimpleGraph

private theorem clique_set_card_le_four {V : Type*} [DecidableEq V]
    {G : SimpleGraph V} (h : G.CliqueFree 5) {A : Finset V}
    (hA : G.IsClique (A : Set V)) : A.card ≤ 4 := by
  by_contra! hcard
  obtain ⟨S, hS, hSize⟩ := exists_subset_card_eq (show 5 ≤ A.card by omega)
  exact h S ⟨hA.subset hS, hSize⟩

private theorem independent_set_card_le_four {V : Type*} [DecidableEq V]
    {G : SimpleGraph V} (h : Gᶜ.CliqueFree 5) {A : Finset V}
    (hA : G.IsIndepSet (A : Set V)) : A.card ≤ 4 :=
  clique_set_card_le_four h (by rwa [isClique_compl])

private theorem union_with_isolated_isIndepSet {V : Type*} [DecidableEq V]
    {G : SimpleGraph V} {A R T : Finset V} (hT : T ⊆ R)
    (hA : ∀ x ∈ A, ∀ y ∈ A ∪ R, ¬ G.Adj x y)
    (hind : G.IsIndepSet (T : Set V)) : G.IsIndepSet (↑(A ∪ T) : Set V) := by
  intro x hx y hy hxy hAdj
  rcases mem_union.mp hx with hx | hx
  · rcases mem_union.mp hy with hy | hy
    · exact hA x hx y (mem_union_left _ hy) hAdj
    · exact hA x hx y (mem_union_right _ (hT hy)) hAdj
  · rcases mem_union.mp hy with hy | hy
    · exact hA y hy x (mem_union_right _ (hT hx)) hAdj.symm
    · exact hind hx hy hxy hAdj

/-- The isolated vertices contribute at most two when the exceptional weight is at least 21. -/
theorem classOne_bounds {V : Type*} [DecidableEq V]
    {G : SimpleGraph V} (hG : G.CliqueFree 5) (hGc : Gᶜ.CliqueFree 5)
    (A B C : Finset V) (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    (hA : ∀ x ∈ A, ∀ y ∈ A ∪ (B ∪ C), ¬ G.Adj x y)
    (hB : G.IsIndepSet (B : Set V)) :
    A.card ≤ 4 ∧ (21 ≤ 5 * A.card + 2 * B.card + C.card → A.card ≤ 2) := by
  have hIndA : G.IsIndepSet (A : Set V) := by
    intro x hx y hy _ hAdj
    exact hA x hx y (mem_union_left _ hy) hAdj
  have ha := independent_set_card_le_four hGc hIndA
  refine ⟨ha, fun hweight => ?_⟩
  by_contra! ha2
  have hDisj : Disjoint A (B ∪ C) := disjoint_union_right.mpr ⟨hAB, hAC⟩
  have hRCard := card_union_of_disjoint hBC
  have hbound {T : Finset V} (hT : T ⊆ B ∪ C)
      (hInd : G.IsIndepSet (T : Set V)) : A.card + T.card ≤ 4 := by
    have hDisjT : Disjoint A T := hDisj.mono_right hT
    rw [← card_union_of_disjoint hDisjT]
    exact independent_set_card_le_four hGc (union_with_isolated_isIndepSet hT hA hInd)
  by_cases h4 : A.card = 4
  · obtain ⟨v, hv⟩ := card_pos.mp (show 0 < (B ∪ C).card by omega)
    have hSingle : G.IsIndepSet (↑({v} : Finset V) : Set V) := by simp
    have h := hbound (singleton_subset_iff.mpr hv) hSingle
    rw [card_singleton] at h
    omega
  have h3 : A.card = 3 := by omega
  have hb : B.card ≤ 1 := by
    have h := hbound subset_union_left hB
    omega
  have hR_not_clique : ¬ G.IsClique (↑(B ∪ C) : Set V) := by
    intro hClique
    have h := clique_set_card_le_four hG hClique
    omega
  rw [not_isClique_iff] at hR_not_clique
  obtain ⟨v, w, hvw, hNotAdj⟩ := hR_not_clique
  let T : Finset V := {v.val, w.val}
  have hvwVal : v.val ≠ w.val := fun h => hvw (Subtype.ext h)
  have hT : T ⊆ B ∪ C := by
    intro x hx
    simp only [T, mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact v.property
    · exact w.property
  have hIndT : G.IsIndepSet (T : Set V) := by
    intro x hx y hy hxy hAdj
    change x ∈ T at hx
    change y ∈ T at hy
    simp only [T, mem_insert, mem_singleton] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact hxy rfl
    · exact hNotAdj hAdj
    · exact hNotAdj hAdj.symm
    · exact hxy rfl
  have hTCard : T.card = 2 := by simp [T, hvwVal]
  have h := hbound hT hIndT
  omega

end OMA.Ramsey55Pattern

/- Retain enough of class three to reach weight 23 with at most one exception. -/

namespace OMA.Ramsey55Pattern

open Finset

theorem trim_class_three {V : Type*} [DecidableEq V] (A B C D : Finset V)
    (hDC : D ⊆ C) (hA : A.card ≤ 1) (hAB : A.card + B.card ≤ 4)
    (hweight : 23 ≤ 5 * A.card + 2 * B.card + C.card)
    (hD : D.card ≤ 5 * A.card + 2 * B.card + C.card - 22) :
    ∃ C' ⊆ C, 5 * A.card + 2 * B.card + C'.card = 23 ∧ (C' ∩ D).card ≤ 1 := by
  let k := 23 - (5 * A.card + 2 * B.card)
  have hk : 5 * A.card + 2 * B.card + k = 23 := by dsimp [k]; omega
  have hkC : k ≤ C.card := by dsimp [k]; omega
  have hdiff : (C \ D).card = C.card - D.card := by
    rw [card_sdiff, inter_eq_left.mpr hDC]
  have hkD : k ≤ (C \ D).card + 1 := by rw [hdiff]; dsimp [k]; omega
  by_cases hsmall : k ≤ (C \ D).card
  · obtain ⟨T, hT, hCardT⟩ := exists_subset_card_eq hsmall
    have hInter : T ∩ D ⊆ ∅ := by
      intro x hx
      exact False.elim ((mem_sdiff.mp (hT (mem_inter.mp hx).1)).2 (mem_inter.mp hx).2)
    have hZero := card_le_card hInter
    refine ⟨T, hT.trans sdiff_subset, ?_, ?_⟩
    · rwa [hCardT]
    · simpa only [card_empty] using hZero.trans (Nat.zero_le 1)
  · have hDpos : 0 < D.card := by omega
    obtain ⟨d, hd⟩ := card_pos.mp hDpos
    have hd' : d ∉ C \ D := fun h => (mem_sdiff.mp h).2 hd
    have hTCard : (insert d (C \ D)).card = k := by
      rw [card_insert_of_notMem hd']
      omega
    have hInter : insert d (C \ D) ∩ D ⊆ {d} := by
      intro x hx
      apply mem_singleton.mpr
      rcases mem_insert.mp (mem_inter.mp hx).1 with h | h
      · exact h
      · exact False.elim ((mem_sdiff.mp h).2 (mem_inter.mp hx).2)
    have hTSubset : insert d (C \ D) ⊆ C := by
      intro x hx
      rcases mem_insert.mp hx with rfl | hx
      · exact hDC hd
      · exact (mem_sdiff.mp hx).1
    refine ⟨insert d (C \ D), hTSubset, ?_, ?_⟩
    · rwa [hTCard]
    · simpa only [card_singleton] using card_le_card hInter

end OMA.Ramsey55Pattern

/- The one-sided weight constraints from Proposition 5.3. -/

namespace OMA.Ramsey55Pattern

open Finset SimpleGraph
open scoped BigOperators

theorem graph_profile
    (G : SimpleGraph (Fin 46)) [DecidableRel G.Adj]
    (hK : G.CliqueFree 5) (hI : Gᶜ.CliqueFree 5)
    (A B C D : Finset (Fin 46))
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C) (hDC : D ⊆ C)
    (hA : ∀ a ∈ A, ∀ x ∈ A ∪ (B ∪ C), ¬G.Adj a x)
    (hB : Gᶜ.IsClique (B : Set (Fin 46)))
    (hBDeg : ∀ b ∈ B, ((A ∪ (B ∪ C)).filter (G.Adj b)).card ≤ 4)
    (hC0Deg : ∀ c ∈ C, c ∉ D → ((A ∪ (B ∪ C)).filter (G.Adj c)).card ≤ 7)
    (hCDDeg : ∀ c ∈ D, (((A ∪ (B ∪ C)) \ D).filter (G.Adj c)).card ≤ 7)
    (hMin : ∀ x, 21 ≤ G.degree x)
    (hBig : ∀ x ∈ B ∪ C, x ∉ D → 22 ≤ G.degree x)
    (h17 : ∀ (V : Type) [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj],
      Fintype.card V = 17 → H.CliqueFree 5 → Hᶜ.CliqueFree 4 → ∃ v, 8 ≤ H.degree v)
    (h21 : ∀ (V : Type) [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj],
      Fintype.card V = 21 → H.CliqueFree 5 → Hᶜ.CliqueFree 5 →
      ∀ a b : V, a ≠ b → ¬H.Adj a b → H.degree a ≤ 4 → H.degree b ≤ 4 →
        (∃ v, 8 ≤ H.degree v) ∨
          ∃ Q : Finset V, H.IsNClique 4 Q ∧ (∑ q ∈ Q, H.degree q) ≤ 24)
    (h22 : ∀ (V : Type) [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj],
      Fintype.card V = 22 → H.CliqueFree 4 → Hᶜ.CliqueFree 5 → ∃ v, 8 ≤ H.degree v) :
    let w := 5 * A.card + 2 * B.card + C.card
    A.card ≤ 4 ∧ (21 ≤ w → A.card ≤ 2) ∧
      (23 ≤ w → (w = 23 ∧ A.card = 2 ∧ D.card = 13) ∨ (A.card ≤ 1 ∧ w ≤ D.card + 21)) := by
  classical
  dsimp only
  let E := A ∪ (B ∪ C)
  obtain ⟨hA4, hA2⟩ := classOne_bounds hK hI A B C hAB hAC hBC hA
    (by simpa only [isClique_compl] using hB)
  refine ⟨hA4, hA2, fun hw => ?_⟩
  have hAle2 := hA2 (by omega)
  have hAclique : Gᶜ.IsClique (A : Set (Fin 46)) := by
    intro a ha a' ha' hne
    exact (G.compl_adj a a').mpr ⟨hne, hA a ha a' (mem_union_left _ ha')⟩
  have hAunionB : A.card + B.card ≤ 4 := by
    have hC : Gᶜ.IsClique ((A ∪ B : Finset (Fin 46)) : Set (Fin 46)) := by
      change (↑(A ∪ B) : Set (Fin 46)).Pairwise Gᶜ.Adj
      rw [coe_union, Set.pairwise_union]
      refine ⟨hAclique, hB, fun a ha b hb hne => ?_⟩
      have h := (G.compl_adj a b).mpr ⟨hne, hA a ha b (mem_union_right _ (mem_union_left _ hb))⟩
      exact ⟨h, h.symm⟩
    have hCcard := card_lt_of_cliqueFree hI hC
    rw [card_union_of_disjoint hAB] at hCcard
    omega
  have hBCtoE : B ∪ C ⊆ E := subset_union_right
  have hABtoC : Disjoint A (B ∪ C) := by
    apply Finset.disjoint_left.mpr
    intro x hx hxc
    rcases mem_union.mp hxc with hb | hc
    · exact Finset.disjoint_left.mp hAB hx hb
    · exact Finset.disjoint_left.mp hAC hx hc
  have hBsmall : ∀ b ∈ B, ((B ∪ C).filter (G.Adj b)).card ≤ 4 := fun b hb =>
    (card_mono (filter_subset_filter (p := G.Adj b) hBCtoE)).trans (hBDeg b hb)
  by_cases hAeq : A.card = 2
  · have hFree : Gᶜ.CliqueFreeOn ((B ∪ C : Finset (Fin 46)) : Set (Fin 46)) 3 :=
      compl_cliqueFreeOn_after_isolated hI hAclique hABtoC
        (fun a ha x hx => hA a ha x (hBCtoE hx)) (by omega)
    have hCsmall : ∀ c ∈ C, c ∉ D → ((B ∪ C).filter (G.Adj c)).card ≤ 7 :=
      fun c hc hd =>
        (card_mono (filter_subset_filter (p := G.Adj c) hBCtoE)).trans (hC0Deg c hc hd)
    obtain ⟨hW, hD⟩ := weight_two_profile G hBC hDC hK.cliqueFreeOn hFree hB hBsmall hCsmall
      (by omega)
    exact Or.inl ⟨by omega, hAeq, hD⟩
  · have hAle1 : A.card ≤ 1 := by omega
    refine Or.inr ⟨hAle1, ?_⟩
    by_contra! hDsmall
    obtain ⟨C', hC'C, hW, hD'⟩ :=
      trim_class_three A B C D hDC hAle1 hAunionB hw (by omega)
    let M := B ∪ C'
    let D' := C' ∩ D
    have hBsub : B ⊆ M := subset_union_left
    have hMsub : M ⊆ B ∪ C := union_subset_union_right hC'C
    have hMtoE : M ⊆ E := hMsub.trans hBCtoE
    have hBdeg : ∀ b ∈ B, (M.filter (G.Adj b)).card ≤ 4 := fun b hb =>
      (card_mono (filter_subset_filter (p := G.Adj b) hMtoE)).trans (hBDeg b hb)
    have hDIn (x : Fin 46) (hx : x ∈ M) (hd : x ∈ D) : x ∈ D' := by
      rcases mem_union.mp hx with hb | hc
      · exact False.elim (Finset.disjoint_left.mp hBC hb (hDC hd))
      · exact mem_inter.mpr ⟨hc, hd⟩
    have hMdeg : ∀ x ∈ M, (M.filter (G.Adj x)).card ≤ 7 := by
      intro x hx
      rcases mem_union.mp hx with hb | hc
      · exact (hBdeg x hb).trans (by decide)
      by_cases hDx : x ∈ D
      · apply le_trans _ (hCDDeg x hDx)
        apply card_mono
        intro y hy
        obtain ⟨hyM, hyx⟩ := mem_filter.mp hy
        refine mem_filter.mpr ⟨mem_sdiff.mpr ⟨hMtoE hyM, ?_⟩, hyx⟩
        intro hDy
        exact hyx.ne (card_le_one.mp hD' x (hDIn x hx hDx) y (hDIn y hyM hDy))
      · exact (card_mono (filter_subset_filter (p := G.Adj x) hMtoE)).trans
          (hC0Deg x (hC'C hc) hDx)
    have hMcard : M.card = B.card + C'.card :=
      card_union_of_disjoint (hBC.mono_right hC'C)
    have hAM : Disjoint A M := hABtoC.mono_right hMsub
    have hcross : ∀ a ∈ A, ∀ x ∈ M, ¬G.Adj a x := fun a ha x hx =>
      hA a ha x (hMtoE hx)
    by_cases hAone : A.card = 1
    · have hI4 : Gᶜ.CliqueFreeOn (M : Set (Fin 46)) 4 :=
        compl_cliqueFreeOn_after_isolated hI hAclique hAM hcross (by omega)
      exact exclude_weight23_one G hBsub hB hK.cliqueFreeOn hI4 hBdeg hMdeg (by omega) h17
    · have hA0 : A.card = 0 := by omega
      have hMbig : ∀ x ∈ M, x ∉ D' → 22 ≤ G.degree x := fun x hx hn =>
        hBig x (hMsub hx) (fun hd => hn (hDIn x hx hd))
      exact exclude_weight23_zero G hK hI hBsub hB hBdeg hMdeg (by omega) hD'
        (fun x _ => hMin x) hMbig h17 h21 h22

end OMA.Ramsey55Pattern

/- Translate the five absent neighborhood patterns into degree-profile constraints. -/

namespace OMA.Ramsey55Pattern

open Finset SimpleGraph
open scoped BigOperators

theorem profile_of_no_pattern
    (G : SimpleGraph (Fin 46)) [DecidableRel G.Adj] (L : Fin 46 → ℕ)
    (hRange : ∀ v, L v ≤ 3)
    (hClass21 : ∀ v, G.degree v = 21 → L v = 0 ∨ L v = 3)
    (hNo : ¬∃ v, (L v = 1 ∧ ∃ u, G.Adj v u ∧ L u ≠ 0) ∨
      (L v = 2 ∧ ∃ u, G.Adj v u ∧ L u = 2) ∨
      (L v = 2 ∧ 5 ≤ (univ.filter fun u => G.Adj v u ∧ L u ≠ 0).card) ∨
      (L v = 3 ∧ G.degree v ≠ 21 ∧
        8 ≤ (univ.filter fun u => G.Adj v u ∧ L u ≠ 0).card) ∨
      (L v = 3 ∧ G.degree v = 21 ∧
        8 ≤ (univ.filter fun u => G.Adj v u ∧ L u ≠ 0 ∧ G.degree u ≠ 21).card))
    (hK : G.CliqueFree 5) (hI : Gᶜ.CliqueFree 5) (hMin : ∀ v, 21 ≤ G.degree v)
    (h17 : ∀ (V : Type) [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj],
      Fintype.card V = 17 → H.CliqueFree 5 → Hᶜ.CliqueFree 4 → ∃ v, 8 ≤ H.degree v)
    (h21 : ∀ (V : Type) [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj],
      Fintype.card V = 21 → H.CliqueFree 5 → Hᶜ.CliqueFree 5 →
      ∀ a b : V, a ≠ b → ¬H.Adj a b → H.degree a ≤ 4 → H.degree b ≤ 4 →
        (∃ v, 8 ≤ H.degree v) ∨
          ∃ Q : Finset V, H.IsNClique 4 Q ∧ (∑ q ∈ Q, H.degree q) ≤ 24)
    (h22 : ∀ (V : Type) [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj],
      Fintype.card V = 22 → H.CliqueFree 4 → Hᶜ.CliqueFree 5 → ∃ v, 8 ≤ H.degree v) :
    let A := (univ : Finset (Fin 46)).filter (fun v => L v = 1)
    let B := (univ : Finset (Fin 46)).filter (fun v => L v = 2)
    let C := (univ : Finset (Fin 46)).filter (fun v => L v = 3)
    let D := C.filter (fun v => G.degree v = 21)
    let w := 5 * A.card + 2 * B.card + C.card
    A.card ≤ 4 ∧ (21 ≤ w → A.card ≤ 2) ∧
      (23 ≤ w → (w = 23 ∧ A.card = 2 ∧ D.card = 13) ∨ (A.card ≤ 1 ∧ w ≤ D.card + 21)) := by
  classical
  intro A B C D w
  have hA (v : Fin 46) : v ∈ A ↔ L v = 1 := by simp [A]
  have hB (v : Fin 46) : v ∈ B ↔ L v = 2 := by simp [B]
  have hC (v : Fin 46) : v ∈ C ↔ L v = 3 := by simp [C]
  have hD (v : Fin 46) : v ∈ D ↔ L v = 3 ∧ G.degree v = 21 := by simp [D, hC]
  have hPos (v : Fin 46) : v ∈ A ∪ (B ∪ C) ↔ L v ≠ 0 := by
    simp only [mem_union, hA, hB, hC]
    have h := hRange v
    omega
  have hPosNoD (v : Fin 46) : v ∈ (A ∪ (B ∪ C)) \ D ↔ L v ≠ 0 ∧ G.degree v ≠ 21 := by
    rw [mem_sdiff, hPos, hD]
    refine ⟨fun h => ⟨h.1, fun hd => ?_⟩, fun h => ⟨h.1, fun hd => h.2 hd.2⟩⟩
    exact h.2 ⟨(hClass21 v hd).resolve_left h.1, hd⟩
  have hCount (v : Fin 46) :
      (A ∪ (B ∪ C)).filter (G.Adj v) = univ.filter (fun u => G.Adj v u ∧ L u ≠ 0) := by
    ext u
    simp only [mem_filter, mem_univ, true_and, hPos, and_comm]
  have hCountNoD (v : Fin 46) :
      ((A ∪ (B ∪ C)) \ D).filter (G.Adj v) =
        (univ.filter fun u => G.Adj v u ∧ L u ≠ 0 ∧ G.degree u ≠ 21) := by
    ext u
    simp only [mem_filter, mem_univ, true_and, hPosNoD]
    exact and_comm
  have hAB : Disjoint A B := Finset.disjoint_left.mpr fun v ha hb => by
    have ha' := (hA v).mp ha
    have hb' := (hB v).mp hb
    omega
  have hAC : Disjoint A C := Finset.disjoint_left.mpr fun v ha hc => by
    have ha' := (hA v).mp ha
    have hc' := (hC v).mp hc
    omega
  have hBC : Disjoint B C := Finset.disjoint_left.mpr fun v hb hc => by
    have hb' := (hB v).mp hb
    have hc' := (hC v).mp hc
    omega
  have hDsub : D ⊆ C := filter_subset _ _
  have hIsoA : ∀ a ∈ A, ∀ x ∈ A ∪ (B ∪ C), ¬G.Adj a x := by
    intro a ha x hx hadj
    exact hNo ⟨a, Or.inl ⟨(hA a).mp ha, x, hadj, (hPos x).mp hx⟩⟩
  have hIndB : Gᶜ.IsClique (B : Set (Fin 46)) := by
    intro a ha b hb hne
    refine (G.compl_adj a b).mpr ⟨hne, fun hadj => ?_⟩
    exact hNo ⟨a, Or.inr (Or.inl ⟨(hB a).mp ha, b, hadj, (hB b).mp hb⟩)⟩
  have hBDeg : ∀ b ∈ B, ((A ∪ (B ∪ C)).filter (G.Adj b)).card ≤ 4 := by
    intro b hb
    rw [hCount]
    by_contra! h5
    exact hNo ⟨b, Or.inr (Or.inr (Or.inl ⟨(hB b).mp hb, by omega⟩))⟩
  have hC0Deg : ∀ c ∈ C, c ∉ D → ((A ∪ (B ∪ C)).filter (G.Adj c)).card ≤ 7 := by
    intro c hc hnd
    rw [hCount]
    by_contra! h8
    have h' := (hC c).mp hc
    have hDeg : G.degree c ≠ 21 := fun hd => hnd ((hD c).mpr ⟨h', hd⟩)
    exact hNo ⟨c, Or.inr (Or.inr (Or.inr (Or.inl ⟨h', hDeg, by omega⟩)))⟩
  have hCDDeg : ∀ c ∈ D, (((A ∪ (B ∪ C)) \ D).filter (G.Adj c)).card ≤ 7 := by
    intro c hc
    rw [hCountNoD]
    by_contra! h8
    have hc' := (hD c).mp hc
    exact hNo ⟨c, Or.inr (Or.inr (Or.inr (Or.inr ⟨hc'.1, hc'.2, by omega⟩)))⟩
  have hBig : ∀ x ∈ B ∪ C, x ∉ D → 22 ≤ G.degree x := by
    intro x hx hnd
    have hxpos := (hPos x).mp (mem_union_right _ hx)
    have hne : G.degree x ≠ 21 := fun he =>
      hnd ((hD x).mpr ⟨(hClass21 x he).resolve_left hxpos, he⟩)
    have h := hMin x
    omega
  exact graph_profile G hK hI A B C D hAB hAC hBC hDsub hIsoA hIndB hBDeg hC0Deg hCDDeg
    hMin hBig h17 h21 h22

theorem sum_weights (L : Fin 46 → ℕ) :
    (∑ v : Fin 46, if L v = 1 then (5 : ℤ) else if L v = 2 then 2 else if L v = 3 then 1 else 0) =
    ((5 * ((univ : Finset (Fin 46)).filter (fun v => L v = 1)).card +
      2 * ((univ : Finset (Fin 46)).filter (fun v => L v = 2)).card +
      ((univ : Finset (Fin 46)).filter (fun v => L v = 3)).card : ℕ) : ℤ) := by
  have hv (v : Fin 46) :
      (if L v = 1 then (5 : ℤ) else if L v = 2 then 2 else if L v = 3 then 1 else 0) =
        5 * (if L v = 1 then (1 : ℤ) else 0) + 2 * (if L v = 2 then 1 else 0) +
          (if L v = 3 then 1 else 0) := by
    by_cases h1 : L v = 1
    · simp [h1]
    by_cases h2 : L v = 2
    · simp [h2]
    by_cases h3 : L v = 3
    · simp [h3]
    simp [h1, h2, h3]
  simp only [hv, sum_add_distrib, ← mul_sum, sum_boole, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]

end OMA.Ramsey55Pattern

/- The numerical contradiction at the end of Angeltveit–McKay Proposition 5.3. -/

namespace OMA.Ramsey55Pattern

private theorem inconsistent_ordered_exception_weights
    (w w' isolated isolated' degree21 degree21' : ℕ)
    (horder : w' ≤ w) (hisolated' : isolated' ≤ 4)
    (hmedium : 21 ≤ w → isolated ≤ 2) (hmedium' : 21 ≤ w' → isolated' ≤ 2)
    (hhigh : 23 ≤ w →
      (w = 23 ∧ isolated = 2 ∧ degree21 = 13) ∨ (isolated ≤ 1 ∧ w ≤ degree21 + 21))
    (hhigh' : 23 ≤ w' →
      (w' = 23 ∧ isolated' = 2 ∧ degree21' = 13) ∨ (isolated' ≤ 1 ∧ w' ≤ degree21' + 21))
    (hweight : 46 + (degree21 - isolated') + (degree21' - isolated) ≤ w + w') :
    False := by
  have hw : 23 ≤ w := by omega
  have hwProfile := hhigh hw
  have hwBound : w ≤ degree21 + 21 := by
    rcases hwProfile with ⟨rfl, _, rfl⟩ | ⟨_, h⟩
    · decide
    · exact h
  by_cases hw' : 21 ≤ w'
  · have hi' := hmedium' hw'
    have hw'Large : 23 ≤ w' := by omega
    have hw'Profile := hhigh' hw'Large
    have hw'Bound : w' ≤ degree21' + 21 := by
      rcases hw'Profile with ⟨rfl, _, rfl⟩ | ⟨_, h⟩
      · decide
      · exact h
    have hi := hmedium (by omega)
    have hIsolated : 4 ≤ isolated + isolated' := by omega
    rcases hwProfile with ⟨rfl, rfl, rfl⟩ | ⟨_, _⟩ <;>
      rcases hw'Profile with ⟨rfl, rfl, rfl⟩ | ⟨_, _⟩ <;> omega
  · omega

/-- Two profiles satisfying the no-pattern bounds cannot meet the corrected total weight. -/
theorem inconsistent_exception_weights
    (w w' isolated isolated' degree21 degree21' : ℕ)
    (hisolated : isolated ≤ 4) (hisolated' : isolated' ≤ 4)
    (hmedium : 21 ≤ w → isolated ≤ 2) (hmedium' : 21 ≤ w' → isolated' ≤ 2)
    (hhigh : 23 ≤ w →
      (w = 23 ∧ isolated = 2 ∧ degree21 = 13) ∨ (isolated ≤ 1 ∧ w ≤ degree21 + 21))
    (hhigh' : 23 ≤ w' →
      (w' = 23 ∧ isolated' = 2 ∧ degree21' = 13) ∨ (isolated' ≤ 1 ∧ w' ≤ degree21' + 21))
    (hweight : 46 + (degree21 - isolated') + (degree21' - isolated) ≤ w + w') :
    False := by
  rcases le_total w' w with h | h
  · exact inconsistent_ordered_exception_weights w w' isolated isolated' degree21 degree21'
      h hisolated' hmedium hmedium' hhigh hhigh' hweight
  · exact inconsistent_ordered_exception_weights w' w isolated' isolated degree21' degree21
      h hisolated hmedium' hmedium hhigh' hhigh (by omega)

end OMA.Ramsey55Pattern

/- Compare degree-21 exceptions with the corresponding degree-24 deficits. -/

namespace OMA.Ramsey55Pattern

open Finset SimpleGraph

theorem degree21_sub_classOne_le_dual_deficit
    (G : SimpleGraph (Fin 46)) [DecidableRel G.Adj] (rank : Fin 46 → ℕ) (D : Finset (Fin 46))
    (hD : ∀ v ∈ D, G.degree v = 21) :
    D.card - (univ.filter fun v => rank v = 1).card ≤
      (univ.filter fun v => Gᶜ.degree v = 24 ∧ rank v ≠ 1).card := by
  classical
  let A := univ.filter fun v => rank v = 1
  let X := univ.filter fun v => Gᶜ.degree v = 24 ∧ rank v ≠ 1
  change D.card - A.card ≤ X.card
  have hsub : D ⊆ A ∪ X := by
    intro v hv
    by_cases hr : rank v = 1
    · exact mem_union_left _ (mem_filter.mpr ⟨mem_univ _, hr⟩)
    · have hd : Gᶜ.degree v = 24 := by
        rw [degree_compl, hD v hv]
        simp
      exact mem_union_right _ (mem_filter.mpr ⟨mem_univ _, hd, hr⟩)
  have hcard := (card_le_card hsub).trans (card_union_le A X)
  omega

end OMA.Ramsey55Pattern

namespace OMA.R_RamseyNumbers_ramsey_number_five_five_upper_bound_R1_H3_R1

open Finset SimpleGraph OMA.Ramsey55Pattern
open scoped BigOperators

/-- Angeltveit–McKay Lemma 5.1. -/
def H1 : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj],
    Fintype.card V = 17 → H.CliqueFree 5 → Hᶜ.CliqueFree 4 → ∃ v, 8 ≤ H.degree v

/-- Angeltveit–McKay Lemma 5.2. -/
def H2 : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj],
    Fintype.card V = 21 → H.CliqueFree 5 → Hᶜ.CliqueFree 5 →
    ∀ a b : V, a ≠ b → ¬H.Adj a b → H.degree a ≤ 4 → H.degree b ≤ 4 →
      (∃ v, 8 ≤ H.degree v) ∨
        ∃ Q : Finset V, H.IsNClique 4 Q ∧ (∑ q ∈ Q, H.degree q) ≤ 24

/-- The minimum of 88 edges on 22 vertices in Appendix A implies this
weaker bound by summing degrees. -/
def H3 : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj],
    Fintype.card V = 22 → H.CliqueFree 4 → Hᶜ.CliqueFree 5 → ∃ v, 8 ≤ H.degree v

theorem main : H1 → H2 → H3 → OMA.R_RamseyNumbers_ramsey_number_five_five_upper_bound_R1.H3 := by
  intro h17 h21 h22
  unfold OMA.R_RamseyNumbers_ramsey_number_five_five_upper_bound_R1.H3
  intro k K S W X cap G _ hK hI hDeg hDeg' _ _ hTotal
  classical
  by_contra hNo
  have hkRange (d e : ℕ) : k d e ≤ 3 := by
    dsimp only [k]
    split
    · decide
    · split
      · decide
      · split <;> decide
  have hk21 (e : ℕ) : k 21 e = 0 ∨ k 21 e = 3 := by
    by_cases he : e = 107 <;> simp [k, he]
  have hProfileG := profile_of_no_pattern G (K G) (fun v => hkRange _ _)
    (fun v h => by simpa only [K, h] using hk21 _)
    (fun h => hNo (Or.inl h)) hK hI (fun v => (hDeg v).1) h17 h21 h22
  have hGcc : Gᶜᶜ.CliqueFree 5 := by simpa only [compl_compl] using hK
  have hProfileC := profile_of_no_pattern Gᶜ (K Gᶜ) (fun v => hkRange _ _)
    (fun v h => by simpa only [K, h] using hk21 _)
    (fun h => hNo (Or.inr h)) hI hGcc (fun v => (hDeg' v).1) h17 h21 h22
  let A := (univ : Finset (Fin 46)).filter (fun v => K G v = 1)
  let B := (univ : Finset (Fin 46)).filter (fun v => K G v = 2)
  let C := (univ : Finset (Fin 46)).filter (fun v => K G v = 3)
  let D := C.filter (fun v => G.degree v = 21)
  let A' := (univ : Finset (Fin 46)).filter (fun v => K Gᶜ v = 1)
  let B' := (univ : Finset (Fin 46)).filter (fun v => K Gᶜ v = 2)
  let C' := (univ : Finset (Fin 46)).filter (fun v => K Gᶜ v = 3)
  let D' := C'.filter (fun v => Gᶜ.degree v = 21)
  let w := 5 * A.card + 2 * B.card + C.card
  let w' := 5 * A'.card + 2 * B'.card + C'.card
  have hSums : (∑ v : Fin 46, W G v) = (w : ℤ) := sum_weights (K G)
  have hSums' : (∑ v : Fin 46, W Gᶜ v) = (w' : ℤ) := sum_weights (K Gᶜ)
  rw [hSums, hSums'] at hTotal
  have hD (v : Fin 46) (hv : v ∈ D) : G.degree v = 21 := (mem_filter.mp hv).2
  have hD' (v : Fin 46) (hv : v ∈ D') : Gᶜ.degree v = 21 := (mem_filter.mp hv).2
  have hXC : ((D.card - A'.card : ℕ) : ℤ) ≤ ∑ v : Fin 46, X Gᶜ v := by
    have hc := degree21_sub_classOne_le_dual_deficit G (K Gᶜ) D hD
    unfold X
    rw [sum_boole]
    exact_mod_cast hc
  have hCCDegree (v : Fin 46) : Gᶜᶜ.degree v = G.degree v := by
    have h₁ := (Gᶜ).degree_compl v
    have h₂ := G.degree_compl v
    rw [Fintype.card_fin] at h₁ h₂
    have h := (hDeg v).2
    omega
  have hX : ((D'.card - A.card : ℕ) : ℤ) ≤ ∑ v : Fin 46, X G v := by
    have hc := degree21_sub_classOne_le_dual_deficit Gᶜ (K G) D' hD'
    unfold X
    rw [sum_boole]
    exact_mod_cast (by simpa only [hCCDegree] using hc :
      D'.card - A.card ≤ (univ.filter fun v => G.degree v = 24 ∧ K G v ≠ 1).card)
  have hFinal : 46 + (D.card - A'.card) + (D'.card - A.card) ≤ w + w' := by omega
  exact inconsistent_exception_weights w w' A.card A'.card D.card D'.card
    hProfileG.1 hProfileC.1 hProfileG.2.1 hProfileC.2.1 hProfileG.2.2 hProfileC.2.2 hFinal

end OMA.R_RamseyNumbers_ramsey_number_five_five_upper_bound_R1_H3_R1
