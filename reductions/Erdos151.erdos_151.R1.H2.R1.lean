import OMAReductions.R_Erdos151_erdos_151_R1

-- Reduction Erdos151.erdos_151.R1.H2.R1 of step Erdos151.erdos_151.R1.H2
-- Credit: @Alewawa

/-!
A graph containing a four-clique with triangle-free complement admits a
triangle-free spanning subgraph that hits each nontrivial maximal clique.
The remaining graphs have low maximum degree and are minimal under passing
to a proper spanning subgraph whose maximal cliques refine the original ones.
-/

namespace OMA.R_Erdos151_erdos_151_R1_H2_R1

open Finset SimpleGraph
open scoped Classical

/-- The remaining case with a four-clique whose complement has triangles but no four-clique. -/
def H1 : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin (n + 1))) (K : Finset (Fin (n + 1))),
    Erdos151.H n < Erdos151.H (n + 1) →
    G.IsNClique 4 K →
    G.CliqueFreeOn (↑K : Set (Fin (n + 1)))ᶜ 4 →
    ¬ G.CliqueFreeOn (↑K : Set (Fin (n + 1)))ᶜ 3 →
    (∀ v, (univ.filter (G.Adj v)).card < Erdos151.H (n + 1)) →
    (∀ J : SimpleGraph (Fin (n + 1)), J < G → ¬ J.CliqueFree 4 →
      ∃ s, G.IsBigMaximalClique s ∧ ∀ t ⊆ s, ¬ J.IsBigMaximalClique t) →
    (¬ ∃ F : SimpleGraph (Fin (n + 1)), F.CliqueFree 3 ∧
      ∀ s, G.IsBigMaximalClique s → ∃ u ∈ s, ∃ v ∈ s, F.Adj u v) →
    G.cliqueTransversalNumber ≤ (n + 1) - Erdos151.H (n + 1)

/-- The remaining case in which every four-clique has a disjoint four-clique. -/
def H2 : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin (n + 1))),
    Erdos151.H n < Erdos151.H (n + 1) →
    ¬ G.CliqueFree 4 →
    (∀ K, G.IsNClique 4 K → ¬ G.CliqueFreeOn (↑K : Set (Fin (n + 1)))ᶜ 4) →
    (∀ v, (univ.filter (G.Adj v)).card < Erdos151.H (n + 1)) →
    (∀ J : SimpleGraph (Fin (n + 1)), J < G → ¬ J.CliqueFree 4 →
      ∃ s, G.IsBigMaximalClique s ∧ ∀ t ⊆ s, ¬ J.IsBigMaximalClique t) →
    (¬ ∃ F : SimpleGraph (Fin (n + 1)), F.CliqueFree 3 ∧
      ∀ s, G.IsBigMaximalClique s → ∃ u ∈ s, ∃ v ∈ s, F.Adj u v) →
    G.cliqueTransversalNumber ≤ (n + 1) - Erdos151.H (n + 1)

lemma mem_maximal_of_adj {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {s : Finset V} (hs : G.IsBigMaximalClique s) {x : V}
    (hx : ∀ y ∈ s, x ≠ y → G.Adj x y) : x ∈ s := by
  have hins : G.IsClique (↑(insert x s) : Set V) := by
    intro a ha b hb hab
    simp only [Finset.mem_coe, mem_insert] at ha hb
    rcases ha with rfl | ha
    · rcases hb with rfl | hb
      · exact (hab rfl).elim
      · exact hx b hb hab
    · rcases hb with rfl | hb
      · exact (hx a ha hab.symm).symm
      · exact hs.1.1 ha hb hab
  exact hs.1.2 hins (subset_insert x s) (mem_insert_self x s)

lemma neighborhood_bound {m : ℕ} (G : SimpleGraph (Fin m)) (v : Fin m)
    (hv : Erdos151.H m ≤ (univ.filter (G.Adj v)).card) :
    G.cliqueTransversalNumber ≤ m - Erdos151.H m := by
  classical
  let S := univ.filter (G.Adj v)
  have hT : G.IsCliqueTransversal Sᶜ := by
    intro s hs
    by_contra! hmiss
    have hadj (x : Fin m) (hx : x ∈ s) : G.Adj v x := by
      have hmem : x ∈ S := by simpa using hmiss x hx
      exact (mem_filter.mp hmem).2
    have hvs : v ∈ s := mem_maximal_of_adj hs (fun x hx _ => hadj x hx)
    exact (hadj v hvs).ne rfl
  calc
    G.cliqueTransversalNumber ≤ Sᶜ.card := csInf_le' ⟨Sᶜ, hT, rfl⟩
    _ = m - S.card := by rw [card_compl, Fintype.card_fin]
    _ ≤ m - Erdos151.H m := Nat.sub_le_sub_left hv m

/-- A transversal for the smaller graph still works if each original big maximal
clique contains a big maximal clique of the smaller graph. -/
lemma transversal_le_of_contained {V : Type*} (G J : SimpleGraph V)
    [Fintype V] [DecidableEq V]
    (hcontain : ∀ s, G.IsBigMaximalClique s → ∃ t ⊆ s, J.IsBigMaximalClique t) :
    G.cliqueTransversalNumber ≤ J.cliqueTransversalNumber := by
  have hne : {k | ∃ T : Finset V, J.IsCliqueTransversal T ∧ T.card = k}.Nonempty := by
    refine ⟨univ.card, univ, ?_, rfl⟩
    intro s hs
    obtain ⟨v, hv⟩ := card_pos.mp (by have := hs.2; omega : 0 < s.card)
    exact ⟨v, hv, mem_univ v⟩
  obtain ⟨T, hT, hsize⟩ := Nat.sInf_mem hne
  apply csInf_le'
  refine ⟨T, ?_, hsize⟩
  intro s hs
  obtain ⟨t, hts, ht⟩ := hcontain s hs
  obtain ⟨v, hv, hvT⟩ := hT t ht
  exact ⟨v, hts hv, hvT⟩

lemma max_pair_no_common {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {x y : V} (hs : G.IsBigMaximalClique {x, y}) :
    ¬ ∃ z, G.Adj x z ∧ G.Adj y z := by
  rintro ⟨z, hxz, hyz⟩
  have hz : z ∈ ({x, y} : Finset V) :=
    mem_maximal_of_adj hs (by
      intro w hw _
      simp only [mem_insert, mem_singleton] at hw
      rcases hw with rfl | rfl
      · exact hxz.symm
      · exact hyz.symm)
  simp [hxz.ne.symm, hyz.ne.symm] at hz

/-- Keep the outside edges, the cut between two halves of the four-clique, and the
edges in no triangle. An uncovered maximal triple has one outside vertex and one
full half. Join its outside vertex to the fixed representative of that half. -/
lemma hitting_of_four_clique {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    {K : Finset V} (hK₄ : G.IsNClique 4 K) (hW : G.CliqueFreeOn (↑K : Set V)ᶜ 3) :
    ∃ F : SimpleGraph V, F ≤ G ∧ F.CliqueFree 3 ∧
      ∀ s, G.IsBigMaximalClique s → ∃ u ∈ s, ∃ v ∈ s, F.Adj u v := by
  obtain ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, rfl⟩ := card_eq_four.mp hK₄.card_eq
  let A : Finset V := {a, b}
  let B : Finset V := {c, d}
  let K : Finset V := A ∪ B
  have hKK : K = {a, b, c, d} := by
    ext x
    simp [K, A, B]
    tauto
  have hK : G.IsClique (↑K : Set V) := by rw [hKK]; exact hK₄.isClique
  have hW' : G.CliqueFreeOn (↑K : Set V)ᶜ 3 := by rw [hKK]; exact hW
  have ha : a ∈ A := by simp [A]
  have hb : b ∈ A := by simp [A]
  have hc : c ∈ B := by simp [B]
  have hd : d ∈ B := by simp [B]
  have hdisj : Disjoint A B := by simp [A, B, hac.symm, had.symm, hbc.symm, hbd.symm]
  have hAa {x : V} : x ∈ A ↔ x = a ∨ x = b := by simp [A]
  have hBb {x : V} : x ∈ B ↔ x = c ∨ x = d := by simp [B]
  have hmem {x : V} : x ∈ K ↔ x ∈ A ∨ x ∈ B := mem_union
  let P (x : V) := x ∉ K ∧ G.IsBigMaximalClique (insert x A)
  let Q (x : V) := x ∉ K ∧ G.IsBigMaximalClique (insert x B)
  have independent (T : Finset V) (hT : T ⊆ K) {x y : V}
      (hx : x ∉ K ∧ G.IsBigMaximalClique (insert x T))
      (hy : y ∉ K ∧ G.IsBigMaximalClique (insert y T)) (hxy : G.Adj x y) : False := by
    have hy' : y ∈ insert x T := mem_maximal_of_adj hx.2 (by
      intro z hz hyz
      rcases mem_insert.mp hz with rfl | hz
      · exact hxy.symm
      · exact hy.2.1.1 (mem_insert_self y T) (mem_insert_of_mem hz) hyz)
    rcases mem_insert.mp hy' with h | h
    · exact hxy.ne h.symm
    · exact hy.1 (hT h)
  have hPQ {x : V} (hp : P x) (hq : Q x) : False := by
    have hca : c ∉ A := fun h => Finset.disjoint_left.mp hdisj h hc
    have hc' : c ∈ insert x A := mem_maximal_of_adj hp.2 (by
      intro z hz hcz
      rcases mem_insert.mp hz with hzx | hz
      · subst z
        exact hq.2.1.1 (mem_insert_of_mem hc) (mem_insert_self x B) hcz
      · exact hK (hmem.mpr (Or.inr hc)) (hmem.mpr (Or.inl hz)) hcz)
    rcases mem_insert.mp hc' with h | h
    · exact hp.1 (h ▸ hmem.mpr (Or.inr hc))
    · exact hca h

  let cut (x y : V) := (x ∈ A ∧ y ∈ B) ∨ (y ∈ A ∧ x ∈ B)
  let spoke (x y : V) := (x = a ∧ P y) ∨ (x = c ∧ Q y)
  let lone (x y : V) := ¬ ∃ z, G.Adj x z ∧ G.Adj y z
  let F : SimpleGraph V := {
    Adj := fun x y => G.Adj x y ∧
      ((x ∉ K ∧ y ∉ K) ∨ cut x y ∨ spoke x y ∨ spoke y x ∨ lone x y)
    symm := ⟨by
      intro x y h
      refine ⟨h.1.symm, ?_⟩
      rcases h.2 with hout | hcut | hs | hs | hl
      · exact Or.inl hout.symm
      · exact Or.inr (Or.inl (hcut.elim Or.inr Or.inl))
      · exact Or.inr (Or.inr (Or.inr (Or.inl hs)))
      · exact Or.inr (Or.inr (Or.inl hs))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (fun ⟨z, hyz, hxz⟩ => hl ⟨z, hxz, hyz⟩))))⟩
    loopless := ⟨fun x h => h.1.ne rfl⟩
  }
  have hsub : F ≤ G := fun _ _ h => h.1
  have spoke_out {x y : V} (h : spoke x y) : x ∈ K ∧ y ∉ K := by
    rcases h with ⟨rfl, hp⟩ | ⟨rfl, hq⟩
    · exact ⟨hmem.mpr (Or.inl ha), hp.1⟩
    · exact ⟨hmem.mpr (Or.inr hc), hq.1⟩
  have cut_in {x y : V} (h : cut x y) : x ∈ K ∧ y ∈ K := by
    rcases h with ⟨hx, hy⟩ | ⟨hy, hx⟩
    · exact ⟨hmem.mpr (Or.inl hx), hmem.mpr (Or.inr hy)⟩
    · exact ⟨hmem.mpr (Or.inr hx), hmem.mpr (Or.inl hy)⟩
  have inside_edge {x y : V} (hx : x ∈ K) (hy : y ∈ K) (h : F.Adj x y)
      (hl : ¬ lone x y) : cut x y := by
    rcases h.2 with ho | hcut | hs | hs | h'
    · exact (ho.1 hx).elim
    · exact hcut
    · exact ((spoke_out hs).2 hy).elim
    · exact ((spoke_out hs).2 hx).elim
    · exact (hl h').elim
  have crossing_edge {x y : V} (hx : x ∈ K) (hy : y ∉ K) (h : F.Adj x y)
      (hl : ¬ lone x y) : spoke x y := by
    rcases h.2 with ho | hcut | hs | hs | h'
    · exact (ho.1 hx).elim
    · exact (hy (cut_in hcut).2).elim
    · exact hs
    · exact (hy (spoke_out hs).1).elim
    · exact (hl h').elim
  have spoke_left_unique {x y z : V} (hxy : spoke x z) (hyz : spoke y z) : x = y := by
    rcases hxy with ⟨rfl, hp⟩ | ⟨rfl, hq⟩ <;>
      rcases hyz with ⟨rfl, hp'⟩ | ⟨rfl, hq'⟩
    · rfl
    · exact (hPQ hp hq').elim
    · exact (hPQ hp' hq).elim
    · rfl
  have spoke_right_indep {x y z : V} (hxy : spoke x y) (hxz : spoke x z) :
      ¬ G.Adj y z := by
    intro hyz
    rcases hxy with ⟨hxa, hp⟩ | ⟨hxc, hq⟩ <;>
      rcases hxz with ⟨hxa', hp'⟩ | ⟨hxc', hq'⟩
    · exact independent A subset_union_left hp hp' hyz
    · exact hac (hxa.symm.trans hxc')
    · exact hac (hxa'.symm.trans hxc)
    · exact independent B subset_union_right hq hq' hyz

  have hF : F.CliqueFree 3 := by
    intro s hs
    obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := is3Clique_iff.mp hs
    have triangle (u v w : V) (huw : F.Adj u w) (hvw : F.Adj v w) :
        ¬ lone u v := fun hl => hl ⟨w, hsub huw, hsub hvw⟩
    have two_inside (u v w : V) (hu : u ∈ K) (hv : v ∈ K) (hw : w ∉ K)
        (huv : F.Adj u v) (huw : F.Adj u w) (hvw : F.Adj v w) : False := by
      have hus := crossing_edge hu hw huw (triangle u w v huv hvw.symm)
      have hvs := crossing_edge hv hw hvw (triangle v w u huv.symm huw.symm)
      exact huv.ne (spoke_left_unique hus hvs)
    have one_inside (u v w : V) (hu : u ∈ K) (hv : v ∉ K) (hw : w ∉ K)
        (huv : F.Adj u v) (huw : F.Adj u w) (hvw : F.Adj v w) : False := by
      have hus := crossing_edge hu hv huv (triangle u v w huw hvw)
      have hvs := crossing_edge hu hw huw (triangle u w v huv hvw.symm)
      exact spoke_right_indep hus hvs (hsub hvw)
    by_cases hx : x ∈ K <;> by_cases hy : y ∈ K <;> by_cases hz : z ∈ K
    · have cxy := inside_edge hx hy hxy (triangle x y z hxz hyz)
      have cxz := inside_edge hx hz hxz (triangle x z y hxy hyz.symm)
      have cyz := inside_edge hy hz hyz (triangle y z x hxy.symm hxz.symm)
      have clash {v : V} (hvA : v ∈ A) (hvB : v ∈ B) : False :=
        Finset.disjoint_left.mp hdisj hvA hvB
      rcases cxy with ⟨hxA, hyB⟩ | ⟨hyA, hxB⟩
      · rcases cxz with ⟨_, hzB⟩ | ⟨_, hxB⟩
        · rcases cyz with ⟨hyA, _⟩ | ⟨hzA, _⟩
          · exact clash hyA hyB
          · exact clash hzA hzB
        · exact clash hxA hxB
      · rcases cxz with ⟨hxA, _⟩ | ⟨hzA, _⟩
        · exact clash hxA hxB
        · rcases cyz with ⟨_, hzB⟩ | ⟨_, hyB⟩
          · exact clash hzA hzB
          · exact clash hyA hyB
    · exact two_inside x y z hx hy hz hxy hxz hyz
    · exact two_inside x z y hx hz hy hxz hxy hyz.symm
    · exact one_inside x y z hx hy hz hxy hxz hyz
    · exact two_inside y z x hy hz hx hyz hxy.symm hxz.symm
    · exact one_inside y x z hy hx hz hxy.symm hyz hxz
    · exact one_inside z x y hz hx hy hxz.symm hyz.symm hxy
    · apply hW' (t := {x, y, z}) ?_ (is3Clique_triple_iff.mpr ⟨hsub hxy, hsub hxz, hsub hyz⟩)
      intro w hw
      simp only [Finset.mem_coe, mem_insert, mem_singleton] at hw
      rcases hw with rfl | rfl | rfl
      · exact hx
      · exact hy
      · exact hz

  refine ⟨F, hsub, hF, ?_⟩
  intro s hs
  by_contra! hmiss
  have no_outside_pair {x y : V} (hx : x ∈ s) (hy : y ∈ s) (hxK : x ∉ K) (hyK : y ∉ K) :
      x = y := by
    by_contra hne
    exact hmiss x hx y hy ⟨hs.1.1 hx hy hne, Or.inl ⟨hxK, hyK⟩⟩
  have no_cut {x y : V} (hx : x ∈ s) (hy : y ∈ s) (hxA : x ∈ A) (hyB : y ∈ B) : False := by
    have hne : x ≠ y := fun h => Finset.disjoint_left.mp hdisj (h ▸ hxA) hyB
    exact hmiss x hx y hy ⟨hs.1.1 hx hy hne, Or.inr (Or.inl (Or.inl ⟨hxA, hyB⟩))⟩
  have hout : ∃ x ∈ s, x ∉ K := by
    by_contra! hinside
    have hKs : K ⊆ s := hs.1.2 hK (fun z hz => hinside z hz)
    exact no_cut (hKs (hmem.mpr (Or.inl ha))) (hKs (hmem.mpr (Or.inr hc))) ha hc
  obtain ⟨x, hxs, hxK⟩ := hout
  have rest_in_K {y : V} (hy : y ∈ s) (hne : y ≠ x) : y ∈ K := by
    by_contra hyK
    exact hne (no_outside_pair hy hxs hyK hxK)
  have locked_pair (T : Finset V) (r t : V) (hTK : T ⊆ K)
      (hT : ∀ y, y ∈ T ↔ y = r ∨ y = t)
      (hrest : ∀ y ∈ s, y ≠ x → y ∈ T)
      (hspoke : x ∉ K ∧ G.IsBigMaximalClique (insert x T) → spoke r x) : False := by
    have hrx : r ≠ x := fun h => hxK (h ▸ hTK ((hT r).mpr (Or.inl rfl)))
    have htx : t ≠ x := fun h => hxK (h ▸ hTK ((hT t).mpr (Or.inr rfl)))
    have hin : s ⊆ insert x T := by
      intro y hy
      by_cases heq : y = x
      · exact mem_insert.mpr (Or.inl heq)
      · exact mem_insert_of_mem (hrest y hy heq)
    have hcases {y : V} (hy : y ∈ s) : y = x ∨ y = r ∨ y = t := by
      have hy' := hin hy
      rwa [mem_insert, hT] at hy'
    by_cases hrs : r ∈ s <;> by_cases hts : t ∈ s
    · have hEq : s = insert x T := by
        refine Subset.antisymm hin ?_
        intro y hy
        rw [mem_insert, hT] at hy
        rcases hy with rfl | rfl | rfl
        · exact hxs
        · exact hrs
        · exact hts
      exact hmiss r hrs x hxs ⟨hs.1.1 hrs hxs hrx,
        Or.inr (Or.inr (Or.inl (hspoke ⟨hxK, hEq ▸ hs⟩)))⟩
    · have hEq : s = {x, r} := by
        ext y
        simp only [mem_insert, mem_singleton]
        constructor
        · intro hy
          rcases hcases hy with rfl | rfl | rfl
          · exact Or.inl rfl
          · exact Or.inr rfl
          · exact (hts hy).elim
        · rintro (rfl | rfl)
          · exact hxs
          · exact hrs
      exact hmiss x hxs r hrs ⟨hs.1.1 hxs hrs hrx.symm,
        Or.inr (Or.inr (Or.inr (Or.inr (max_pair_no_common (hEq ▸ hs)))))⟩
    · have hEq : s = {x, t} := by
        ext y
        simp only [mem_insert, mem_singleton]
        constructor
        · intro hy
          rcases hcases hy with rfl | rfl | rfl
          · exact Or.inl rfl
          · exact (hrs hy).elim
          · exact Or.inr rfl
        · rintro (rfl | rfl)
          · exact hxs
          · exact hts
      exact hmiss x hxs t hts ⟨hs.1.1 hxs hts htx.symm,
        Or.inr (Or.inr (Or.inr (Or.inr (max_pair_no_common (hEq ▸ hs)))))⟩
    · have hEq : s = {x} := by
        ext y
        simp only [mem_singleton]
        constructor
        · intro hy
          rcases hcases hy with rfl | rfl | rfl
          · rfl
          · exact (hrs hy).elim
          · exact (hts hy).elim
        · rintro rfl
          exact hxs
      have hcard := hs.2
      simp [hEq] at hcard
  by_cases hA : ∃ y ∈ s, y ∈ A
  · obtain ⟨y, hys, hyA⟩ := hA
    refine locked_pair A a b subset_union_left (fun _ => hAa) ?_ (fun hp => Or.inl ⟨rfl, hp⟩)
    intro z hzs hne
    rcases hmem.mp (rest_in_K hzs hne) with hz | hz
    · exact hz
    · exact (no_cut hys hzs hyA hz).elim
  · refine locked_pair B c d subset_union_right (fun _ => hBb) ?_ (fun hq => Or.inr ⟨rfl, hq⟩)
    intro z hzs hne
    rcases hmem.mp (rest_in_K hzs hne) with hz | hz
    · exact (hA ⟨z, hzs, hz⟩).elim
    · exact hz

theorem main : H1 → H2 → OMA.R_Erdos151_erdos_151_R1.H2 := by
  classical
  intro h1 h2 n G hjump hK₄ _
  have bound (d : ℕ) (G : SimpleGraph (Fin (n + 1))) (hd : G.edgeFinset.card = d)
      (hK₄ : ¬ G.CliqueFree 4) : G.cliqueTransversalNumber ≤ (n + 1) - Erdos151.H (n + 1) := by
    induction d using Nat.strong_induction_on generalizing G with
    | h d ih =>
      by_cases hgood : ∃ F : SimpleGraph (Fin (n + 1)), F.CliqueFree 3 ∧
          ∀ s, G.IsBigMaximalClique s → ∃ u ∈ s, ∃ v ∈ s, F.Adj u v
      · obtain ⟨F, hF, hit⟩ := hgood
        exact OMA.R_Erdos151_erdos_151_R1.bound_of_hitting (n + 1) G F hF hit
      by_cases hhigh : ∃ v, Erdos151.H (n + 1) ≤ (univ.filter (G.Adj v)).card
      · obtain ⟨v, hv⟩ := hhigh
        exact neighborhood_bound G v hv
      have hlow (v : Fin (n + 1)) : (univ.filter (G.Adj v)).card < Erdos151.H (n + 1) :=
        lt_of_not_ge (fun h => hhigh ⟨v, h⟩)
      by_cases hdel : ∃ J : SimpleGraph (Fin (n + 1)), J < G ∧ ¬ J.CliqueFree 4 ∧
          ∀ s, G.IsBigMaximalClique s → ∃ t ⊆ s, J.IsBigMaximalClique t
      · obtain ⟨J, hJG, hJ₄, hcontain⟩ := hdel
        have hcard : J.edgeFinset.card < d := by
          rw [← hd]
          exact card_lt_card (edgeFinset_strict_mono hJG)
        exact (transversal_le_of_contained G J hcontain).trans (ih _ hcard J rfl hJ₄)
      have hminimal (J : SimpleGraph (Fin (n + 1))) (hJG : J < G) (hJ₄ : ¬ J.CliqueFree 4) :
          ∃ s, G.IsBigMaximalClique s ∧ ∀ t ⊆ s, ¬ J.IsBigMaximalClique t := by
        by_contra! h
        exact hdel ⟨J, hJG, hJ₄, h⟩
      by_cases hnear : ∃ K : Finset (Fin (n + 1)), G.IsNClique 4 K ∧
          G.CliqueFreeOn (↑K : Set (Fin (n + 1)))ᶜ 4
      · obtain ⟨K, hK, hW⟩ := hnear
        refine h1 n G K hjump hK hW ?_ hlow hminimal hgood
        intro ht
        obtain ⟨F, _, hF, hit⟩ := hitting_of_four_clique G hK ht
        exact hgood ⟨F, hF, hit⟩
      · exact h2 n G hjump hK₄ (fun K hK hW => hnear ⟨K, hK, hW⟩) hlow hminimal hgood
  exact bound G.edgeFinset.card G rfl hK₄

end OMA.R_Erdos151_erdos_151_R1_H2_R1
