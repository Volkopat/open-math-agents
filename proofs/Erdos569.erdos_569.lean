import FormalConjectures.ErdosProblems.«569»

/-! Haggkvist bound via depth-first search (see HAGGKVIST.md). -/

namespace OMA569
open SimpleGraph

/-- Bridge: a duplicate-free list of consecutively adjacent vertices of length at least `k`
gives a copy of `pathGraph k`. -/
theorem pathGraph_le_of_chain {V : Type*} (G : SimpleGraph V) (k : ℕ) (L : List V)
    (hnd : L.Nodup) (hc : L.IsChain G.Adj) (hlen : k ≤ L.length) : pathGraph k ⊑ G := by
  let f : Fin k → V := fun i => L[(i : ℕ)]'(by omega)
  have hf : Function.Injective f := by
    intro i j h
    have := (List.Nodup.getElem_inj_iff hnd).mp h
    exact Fin.ext this
  have hadj : ∀ i j : Fin k, (i : ℕ) + 1 = j → G.Adj (f i) (f j) := by
    intro i j h
    have := hc.getElem i (by omega)
    simp only [f]
    convert this using 2
    exact h.symm
  exact ⟨⟨⟨f, fun {a b} h => by
    rcases pathGraph_adj.mp h with h | h
    exacts [hadj a b h, (hadj b a h).symm]⟩, hf⟩⟩

/-- Under `P_k`-freeness, a duplicate-free chain has at most `k - 1` vertices. -/
theorem length_le_of_pathFree {V : Type*} (G : SimpleGraph V) (k : ℕ)
    (hfree : (pathGraph k).Free G) (L : List V) (hnd : L.Nodup) (hc : L.IsChain G.Adj) :
    L.length + 1 ≤ k := by
  by_contra h
  exact hfree (pathGraph_le_of_chain G k L hnd hc (by omega))

/-- DFS state: `T` finished, `Q` the stack (head = top), `S` unvisited. -/
def DfsValid {V : Type*} [Fintype V] (G : SimpleGraph V) (T S : Finset V) (Q : List V) : Prop :=
  Disjoint T S ∧ Q.Nodup ∧ (∀ x ∈ Q, x ∉ T ∧ x ∉ S) ∧ Q.IsChain G.Adj ∧
    (∀ x ∈ T, ∀ y ∈ S, ¬ G.Adj x y) ∧ T.card + S.card + Q.length = Fintype.card V

/-- Step 4: from a valid state with `T ≠ univ`, reach one with one more finished vertex and a
short stack. -/
theorem dfs_step {V : Type*} [Fintype V] (G : SimpleGraph V) (k : ℕ)
    (hfree : (pathGraph k).Free G) : ∀ (n : ℕ) (T S : Finset V) (Q : List V), S.card = n →
    DfsValid G T S Q → T.card < Fintype.card V →
    ∃ T' S' : Finset V, ∃ Q' : List V, DfsValid G T' S' Q' ∧ T'.card = T.card + 1 ∧
      Q'.length + 2 ≤ k := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro T S Q hn hv hT
  obtain ⟨hTS, hnd, hQ, hc, hno, hcard⟩ := hv
  cases Q with
  | nil =>
    have hS : S.Nonempty := by
      rw [← Finset.card_pos]; simp at hcard; omega
    obtain ⟨s, hs⟩ := hS
    refine ih (S.erase s).card (hn ▸ Finset.card_erase_lt_of_mem hs) T (S.erase s) [s]
      rfl ⟨Finset.disjoint_of_subset_right (Finset.erase_subset _ _) hTS, by simp, ?_,
        List.isChain_singleton _, fun x hx y hy => hno x hx y (Finset.mem_of_mem_erase hy), ?_⟩ hT
    · intro x hx
      simp at hx; subst hx
      exact ⟨fun h => Finset.disjoint_left.mp hTS h hs, by simp⟩
    · rw [Finset.card_erase_of_mem hs]
      have := Finset.card_pos.mpr ⟨s, hs⟩
      simp at hcard ⊢; omega
  | cons q Q' =>
    by_cases hnb : ∃ s ∈ S, G.Adj s q
    · obtain ⟨s, hs, hsq⟩ := hnb
      have hsQ : s ∉ q :: Q' := fun h => (hQ s h).2 hs
      refine ih (S.erase s).card (hn ▸ Finset.card_erase_lt_of_mem hs) T (S.erase s)
        (s :: q :: Q') rfl ⟨Finset.disjoint_of_subset_right (Finset.erase_subset _ _) hTS,
          List.nodup_cons.mpr ⟨hsQ, hnd⟩, ?_, List.isChain_cons_cons.mpr ⟨hsq, hc⟩,
          fun x hx y hy => hno x hx y (Finset.mem_of_mem_erase hy), ?_⟩ hT
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact ⟨fun h => Finset.disjoint_left.mp hTS h hs, by simp⟩
        · exact ⟨(hQ x hx).1, fun h => (hQ x hx).2 (Finset.mem_of_mem_erase h)⟩
      · rw [Finset.card_erase_of_mem hs]
        have := Finset.card_pos.mpr ⟨s, hs⟩
        simp at hcard ⊢; omega
    · push Not at hnb
      have hlen := length_le_of_pathFree G k hfree _ hnd hc
      have hqT : q ∉ T := (hQ q List.mem_cons_self).1
      have hqS : q ∉ S := (hQ q List.mem_cons_self).2
      have hnd' := List.nodup_cons.mp hnd
      refine ⟨insert q T, S, Q', ⟨?_, hnd'.2, ?_, hc.tail, ?_, ?_⟩,
        Finset.card_insert_of_notMem hqT, by simp at hlen; omega⟩
      · exact Finset.disjoint_insert_left.mpr ⟨hqS, hTS⟩
      · intro x hx
        have h1 := hQ x (List.mem_cons_of_mem _ hx)
        refine ⟨?_, h1.2⟩
        rw [Finset.mem_insert, not_or]
        exact ⟨fun h => hnd'.1 (h ▸ hx), h1.1⟩
      · intro x hx y hy
        rcases Finset.mem_insert.mp hx with rfl | hx
        · exact fun h => hnb y hy h.symm
        · exact hno x hx y hy
      · rw [Finset.card_insert_of_notMem hqT]
        simp at hcard ⊢; omega

/-- Step 5: every size `t ≤ |V|` of finished set is reached with a short stack. -/
theorem dfs_reach {V : Type*} [Fintype V] (G : SimpleGraph V) (k : ℕ) (hk : 2 ≤ k)
    (hfree : (pathGraph k).Free G) : ∀ t : ℕ, t ≤ Fintype.card V →
    ∃ T S : Finset V, ∃ Q : List V, DfsValid G T S Q ∧ T.card = t ∧ Q.length + 2 ≤ k := by
  classical
  intro t
  induction t with
  | zero =>
    intro _
    refine ⟨∅, Finset.univ, [], ⟨by simp, by simp, by simp, List.IsChain.nil, by simp, ?_⟩,
      by simp, by simpa using hk⟩
    simp
  | succ t ih =>
    intro ht
    obtain ⟨T, S, Q, hv, hT, _⟩ := ih (by omega)
    obtain ⟨T', S', Q', hv', hT', hQ'⟩ := dfs_step G k hfree S.card T S Q rfl hv (by omega)
    exact ⟨T', S', Q', hv', by omega, hQ'⟩

theorem haggkvist {V : Type*} [Fintype V] (G : SimpleGraph V) (k a b : ℕ) (hk : 2 ≤ k)
    (hfree : (pathGraph k).Free G) (hcard : a + b + k - 2 ≤ Fintype.card V) :
    ∃ A B : Finset V, A.card = a ∧ B.card = b ∧ Disjoint A B ∧ ∀ x ∈ A, ∀ y ∈ B, ¬ G.Adj x y := by
  obtain ⟨T, S, Q, ⟨hTS, -, -, -, hno, hc⟩, hT, hQ⟩ := dfs_reach G k hk hfree a (by omega)
  obtain ⟨B, hBS, hB⟩ := Finset.exists_subset_card_eq (s := S) (n := b) (by omega)
  exact ⟨T, B, hT, hB, Finset.disjoint_of_subset_right hBS hTS,
    fun x hx y hy => hno x hx y (hBS hy)⟩

end OMA569


namespace OMA569
open SimpleGraph

/-- A duplicate-free adjacency chain of length `n` gives a copy of `pathGraph n`. -/
theorem pathGraph_isContained_of_list {V : Type*} (G : SimpleGraph V) (l : List V)
    (hnd : l.Nodup) (hc : l.IsChain G.Adj) : pathGraph l.length ⊑ G := by
  refine ⟨⟨⟨fun i => l.get i, fun {a b} h => ?_⟩, List.nodup_iff_injective_get.mp hnd⟩⟩
  have key : ∀ (i : ℕ) (h : i + 1 < l.length), G.Adj l[i] l[i + 1] :=
    List.isChain_iff_getElem.mp hc
  rcases pathGraph_adj.mp h with h | h
  · have := key a (h ▸ b.2)
    simp only [List.get_eq_getElem]
    convert this using 2; simp [← h]
  · have := key b (h ▸ a.2)
    simp only [List.get_eq_getElem]
    convert this.symm using 2; simp [← h]

/-- In a `P_j`-free graph every nonempty vertex set `T` has a vertex with at most `j - 2`
neighbours inside `T`. -/
theorem exists_low_degree_of_pathFree {V : Type*} (G : SimpleGraph V) (j : ℕ) (hj : 2 ≤ j)
    (hfree : (pathGraph j).Free G) [DecidableRel G.Adj] (T : Finset V) (hT : T.Nonempty) :
    ∃ x ∈ T, (T.filter (G.Adj x)).card ≤ j - 2 := by
  classical
  by_contra hcon
  push Not at hcon
  have grow : ∀ n, 1 ≤ n → n ≤ j → ∃ l : List V, l.length = n ∧ l.Nodup ∧
      l.IsChain G.Adj ∧ ∀ v ∈ l, v ∈ T := by
    intro n hn hnj
    induction n with
    | zero => omega
    | succ n ih =>
      rcases Nat.eq_zero_or_pos n with rfl | hpos
      · obtain ⟨x, hx⟩ := hT
        exact ⟨[x], rfl, List.nodup_singleton x, List.isChain_singleton x, by simpa using hx⟩
      obtain ⟨l, hlen, hnd, hc, hT'⟩ := ih hpos (by omega)
      obtain ⟨a, rest, rfl⟩ : ∃ a rest, l = a :: rest :=
        List.exists_cons_of_length_pos (by omega)
      have hlt := hcon a (hT' a (by simp))
      have hnot : ¬ T.filter (G.Adj a) ⊆ (a :: rest).toFinset.erase a := by
        intro hsub
        have h1 := Finset.card_le_card hsub
        have h2 := Finset.card_erase_le (s := (a :: rest).toFinset) (a := a)
        rw [Finset.card_erase_of_mem (by simp), List.toFinset_card_of_nodup hnd] at h1
        simp at hlen h1
        omega
      obtain ⟨b, hb, hbnot⟩ := Finset.not_subset.mp hnot
      rw [Finset.mem_filter] at hb
      have hba : b ≠ a := (G.ne_of_adj hb.2).symm
      have hbl : b ∉ a :: rest := fun hm =>
        hbnot (Finset.mem_erase.mpr ⟨hba, List.mem_toFinset.mpr hm⟩)
      refine ⟨b :: a :: rest, by simpa using hlen, List.nodup_cons.mpr ⟨hbl, hnd⟩,
        List.isChain_cons_cons.mpr ⟨hb.2.symm, hc⟩, ?_⟩
      intro v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · exact hb.1
      · exact hT' v hv
  obtain ⟨l, hlen, hnd, hc, -⟩ := grow j (by omega) le_rfl
  exact hfree (hlen ▸ pathGraph_isContained_of_list G l hnd hc)

theorem indep_of_pathFree {V : Type*} [Fintype V] (G : SimpleGraph V) (j t : ℕ) (hj : 2 ≤ j)
    (hfree : (pathGraph j).Free G) (hcard : (j - 1) * (t - 1) < Fintype.card V) :
    ∃ s : Finset V, s.card = t ∧ G.IsIndepSet (s : Set V) := by
  classical
  have main : ∀ t : ℕ, ∀ T : Finset V, (j - 1) * t < T.card →
      ∃ s ⊆ T, s.card = t + 1 ∧ G.IsIndepSet (s : Set V) := by
    intro t
    induction t with
    | zero =>
      intro T hT
      obtain ⟨x, hx⟩ := Finset.card_pos.mp (by omega)
      exact ⟨{x}, by simpa using hx, by simp, by simp⟩
    | succ t ih =>
      intro T hT
      obtain ⟨x, hxT, hdeg⟩ :=
        exists_low_degree_of_pathFree G j hj hfree T (Finset.card_pos.mp (by
          have := Nat.zero_le ((j - 1) * (t + 1)); omega))
      set T' := T.filter (fun y => y ≠ x ∧ ¬ G.Adj x y) with hT'
      have hsub : T ⊆ insert x (T' ∪ T.filter (G.Adj x)) := by
        intro y hy
        by_cases hyx : y = x
        · simp [hyx]
        · by_cases ha : G.Adj x y <;> simp [hT', hy, hyx, ha]
      have hc1 := (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _)
      have hc2 := Finset.card_union_le T' (T.filter (G.Adj x))
      obtain ⟨s, hsT', hs, hind⟩ := ih T' (by
        have : (j - 1) * (t + 1) = (j - 1) * t + (j - 1) := by ring
        omega)
      have hxs : x ∉ s := fun h => by simpa [hT'] using hsT' h
      refine ⟨insert x s, ?_, by rw [Finset.card_insert_of_notMem hxs, hs], ?_⟩
      · exact Finset.insert_subset hxT (hsT'.trans (Finset.filter_subset _ _))
      · rw [Finset.coe_insert]
        refine hind.insert fun y hy _ => ?_
        have := (Finset.mem_filter.mp (hsT' hy)).2.2
        exact ⟨this, fun h => this h.symm⟩
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · exact ⟨∅, rfl, by simp⟩
  obtain ⟨s, -, hs, hind⟩ := main (t - 1) Finset.univ (by simpa using hcard)
  exact ⟨s, by omega, hind⟩

end OMA569


namespace OMA569
open SimpleGraph

/-- Häggkvist inside a Finset `U` of the vertex type. -/
theorem haggkvist_finset {V : Type*} [Fintype V] (G : SimpleGraph V) (k a b : ℕ) (hk : 2 ≤ k)
    (hfree : (pathGraph k).Free G) (U : Finset V) (hcard : a + b + k - 2 ≤ U.card) :
    ∃ A B : Finset V, A ⊆ U ∧ B ⊆ U ∧ A.card = a ∧ B.card = b ∧ Disjoint A B ∧
      ∀ x ∈ A, ∀ y ∈ B, ¬ G.Adj x y := by
  have hf' : (pathGraph k).Free (G.induce (U : Set V)) := fun h =>
    hfree (h.trans ⟨Copy.induce G _⟩)
  obtain ⟨A, B, hA, hB, hd, he⟩ :=
    haggkvist (G.induce (U : Set V)) k a b hk hf' (by simpa using hcard)
  refine ⟨A.map (Function.Embedding.subtype _), B.map (Function.Embedding.subtype _),
    ?_, ?_, by simp [hA], by simp [hB], Finset.disjoint_map _ |>.mpr hd, ?_⟩
  · intro x hx
    simp only [Finset.mem_map, Function.Embedding.coe_subtype] at hx
    obtain ⟨y, -, rfl⟩ := hx
    exact y.2
  · intro x hx
    simp only [Finset.mem_map, Function.Embedding.coe_subtype] at hx
    obtain ⟨y, -, rfl⟩ := hx
    exact y.2
  · intro x hx y hy
    simp only [Finset.mem_map, Function.Embedding.coe_subtype] at hx hy
    obtain ⟨x, hxA, rfl⟩ := hx
    obtain ⟨y, hyB, rfl⟩ := hy
    exact he x hxA y hyB

/-- Blue complete multipartite embedding, Finset form: colour classes `C < c` of `T`
embed into `U` with no red edge between images of `H`-adjacent vertices. -/
theorem blue_claim {V W : Type*} [Fintype V] [Nonempty V] (G : SimpleGraph V)
    (H : SimpleGraph W) (k : ℕ) (hk : 2 ≤ k) (hfree : (pathGraph k).Free G) (C : W → ℕ)
    (hC : ∀ x y, H.Adj x y → C x ≠ C y) :
    ∀ c : ℕ, ∀ T : Finset W, (∀ w ∈ T, C w < c) → ∀ U : Finset V,
      T.card + (k - 2) * (c - 1) ≤ U.card →
      ∃ f : W → V, Set.InjOn f T ∧ (∀ w ∈ T, f w ∈ U) ∧
        ∀ x ∈ T, ∀ y ∈ T, H.Adj x y → ¬ G.Adj (f x) (f y) := by
  classical
  intro c
  induction c with
  | zero =>
    intro T hT U _
    refine ⟨fun _ => Classical.arbitrary V, ?_, ?_, ?_⟩
    · intro x hx
      exact absurd (hT x hx) (Nat.not_lt_zero _)
    · intro x hx
      exact absurd (hT x hx) (Nat.not_lt_zero _)
    · intro x hx
      exact absurd (hT x hx) (Nat.not_lt_zero _)
  | succ c ih =>
    intro T hT U hU
    set S := T.filter (fun w => C w = c) with hSdef
    set T' := T.filter (fun w => ¬ C w = c) with hT'def
    have hsplit : S.card + T'.card = T.card := Finset.card_filter_add_card_filter_not _
    have hT' : ∀ w ∈ T', C w < c := by
      intro w hw
      rw [hT'def, Finset.mem_filter] at hw
      have := hT w hw.1
      omega
    obtain ⟨A, B, hAU, hBU, hA, hB, hd, he⟩ : ∃ A B : Finset V, A ⊆ U ∧ B ⊆ U ∧
        A.card = S.card ∧ B.card = T'.card + (k - 2) * (c - 1) ∧ Disjoint A B ∧
        ∀ x ∈ A, ∀ y ∈ B, ¬ G.Adj x y := by
      rcases Nat.eq_zero_or_pos c with h0 | hpos
      · subst h0
        have hT'e : T' = ∅ := Finset.eq_empty_of_forall_notMem fun w hw =>
          Nat.not_lt_zero _ (hT' w hw)
        obtain ⟨A, hAU, hA⟩ := Finset.exists_subset_card_eq (s := U) (n := S.card)
          (by simp at hU; omega)
        exact ⟨A, ∅, hAU, Finset.empty_subset _, hA, by simp [hT'e], Finset.disjoint_empty_right _,
          by simp⟩
      · obtain ⟨c', rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
        apply haggkvist_finset G k _ _ hk hfree U
        obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
        simp only [Nat.add_sub_cancel] at hU ⊢
        have hmul : m * (c' + 1) = m * c' + m := Nat.mul_succ m c'
        rw [hmul] at hU
        omega
    obtain ⟨f', hf'inj, hf'U, hf'e⟩ := ih T' hT' B (by rw [hB])
    obtain ⟨g, hgA, hginj⟩ := Set.Finite.exists_injOn_of_encard_le (s := (S : Set W))
      (t := (A : Set V)) S.finite_toSet
      (by rw [Set.encard_coe_eq_coe_finsetCard, Set.encard_coe_eq_coe_finsetCard, hA])
    have hgA' : ∀ w ∈ T, C w = c → g w ∈ A := fun w hw hc =>
      hgA (show w ∈ (S : Set W) by simp [hSdef, hw, hc])
    have hf'B : ∀ w ∈ T, ¬ C w = c → f' w ∈ B := fun w hw hc =>
      hf'U w (by simp [hT'def, hw, hc])
    have memS : ∀ w ∈ T, C w = c → w ∈ (S : Set W) := fun w hw hc => by simp [hSdef, hw, hc]
    have memT' : ∀ w ∈ T, ¬ C w = c → w ∈ (T' : Set W) := fun w hw hc => by
      simp [hT'def, hw, hc]
    refine ⟨fun w => if C w = c then g w else f' w, ?_, ?_, ?_⟩
    · intro x hx y hy hxy
      simp only at hxy
      by_cases hcx : C x = c <;> by_cases hcy : C y = c <;> simp only [hcx, hcy, if_true,
        if_false] at hxy
      · exact hginj (memS x hx hcx) (memS y hy hcy) hxy
      · have h1 := hf'B y hy hcy
        rw [← hxy] at h1
        exact (Finset.disjoint_left.mp hd (hgA' x hx hcx) h1).elim
      · have h1 := hf'B x hx hcx
        rw [hxy] at h1
        exact (Finset.disjoint_left.mp hd (hgA' y hy hcy) h1).elim
      · exact hf'inj (memT' x hx hcx) (memT' y hy hcy) hxy
    · intro w hw
      simp only
      split_ifs with hc
      · exact hAU (hgA' w hw hc)
      · exact hBU (hf'B w hw hc)
    · intro x hx y hy hadj
      simp only
      by_cases hcx : C x = c <;> by_cases hcy : C y = c <;> simp only [hcx, hcy, if_true,
        if_false]
      · exact absurd (hcx.trans hcy.symm) (hC x y hadj)
      · exact he _ (hgA' x hx hcx) _ (hf'B y hy hcy)
      · exact fun h => he _ (hgA' y hy hcy) _ (hf'B x hx hcx) h.symm
      · exact hf'e x (memT' x hx hcx) y (memT' y hy hcy) hadj

/-- Lemma C (paper Lemma 5): no red `P_k` and enough vertices ⇒ blue copy of any `c`-colourable `H`. -/
theorem blue_of_pathFree {V W : Type*} [Fintype V] [Fintype W] (G : SimpleGraph V) (H : SimpleGraph W)
    (k c : ℕ) (hk : 2 ≤ k) (hc : 1 ≤ c) (hcol : H.Colorable c) (hfree : (pathGraph k).Free G)
    (hcard : Fintype.card W + (k - 2) * (c - 1) ≤ Fintype.card V) : H ⊑ Gᶜ := by
  classical
  rcases isEmpty_or_nonempty W with hW | hW
  · exact ⟨⟨⟨fun w => isEmptyElim w, fun {a} => isEmptyElim a⟩, fun a => isEmptyElim a⟩⟩
  have : Nonempty V := by
    rw [← Fintype.card_pos_iff] at hW ⊢
    omega
  obtain ⟨col⟩ := hcol
  obtain ⟨f, hinj, -, hedge⟩ := blue_claim G H k hk hfree (fun w => (col w : ℕ))
    (fun x y h e => col.valid h (Fin.ext e)) c Finset.univ (fun w _ => (col w).isLt)
    Finset.univ (by simpa using hcard)
  have hinj' : Function.Injective f := fun x y hxy => hinj (by simp) (by simp) hxy
  exact ⟨⟨⟨f, fun {a b} h => (compl_adj G (f a) (f b)).mpr
    ⟨fun e => H.ne_of_adj h (hinj' e), hedge a (by simp) b (by simp) h⟩⟩, hinj'⟩⟩

end OMA569


namespace OMA569
open SimpleGraph

/-- Extending a colouring of `K.erase v` to `K` when `v` has few neighbours in `K`. -/
theorem colorable_induce_of_erase {W : Type*} [Fintype W] [DecidableEq W] (H : SimpleGraph W)
    [DecidableRel H.Adj] (K : Finset W) (v : W) (n : ℕ)
    (hcol : (H.induce ((K.erase v : Finset W) : Set W)).Colorable n)
    (hfew : (H.neighborFinset v ∩ K).card < n) :
    (H.induce (K : Set W)).Colorable n := by
  classical
  obtain ⟨C, hC⟩ := (colorable_iff_exists_bdd_nat_coloring n).1 hcol
  let g : W → ℕ := fun x => if h : x ∈ K.erase v then C ⟨x, Finset.mem_coe.2 h⟩ else 0
  have hg : ∀ x (h : x ∈ K.erase v), g x = C ⟨x, Finset.mem_coe.2 h⟩ := by
    intro x h; simp only [g, dif_pos h]
  obtain ⟨a, ha, haS⟩ : ∃ a ∈ Finset.range n, a ∉ (H.neighborFinset v ∩ K).image g := by
    by_contra hne
    push Not at hne
    have := Finset.card_le_card hne
    have := (Finset.card_image_le (s := H.neighborFinset v ∩ K) (f := g))
    simp at *; omega
  refine (colorable_iff_exists_bdd_nat_coloring n).2
    ⟨Coloring.mk (fun x => if (x : W) = v then a else g x) ?_, ?_⟩
  · rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
    change H.Adj x y at hxy
    have hx' : x ∈ K := Finset.mem_coe.1 hx
    have hy' : y ∈ K := Finset.mem_coe.1 hy
    by_cases hxv : x = v
    · subst hxv
      have hyv : y ≠ x := (H.ne_of_adj hxy).symm
      change (if x = x then a else g x) ≠ (if y = x then a else g y)
      rw [if_pos rfl, if_neg hyv]
      intro hEq
      exact haS (Finset.mem_image.2 ⟨y, by simp [hxy, hy'], hEq.symm⟩)
    · by_cases hyv : y = v
      · subst hyv
        change (if x = y then a else g x) ≠ (if y = y then a else g y)
        rw [if_pos rfl, if_neg hxv]
        intro hEq
        exact haS (Finset.mem_image.2 ⟨x, by simp [hxy.symm, hx'], hEq⟩)
      · change (if x = v then a else g x) ≠ (if y = v then a else g y)
        rw [if_neg hxv, if_neg hyv]
        have hxe : x ∈ K.erase v := Finset.mem_erase.2 ⟨hxv, hx'⟩
        have hye : y ∈ K.erase v := Finset.mem_erase.2 ⟨hyv, hy'⟩
        rw [hg x hxe, hg y hye]
        exact C.valid (by simpa using hxy)
  · rintro ⟨x, hx⟩
    by_cases hxv : x = v
    · show (if x = v then a else g x) < n
      rw [if_pos hxv]
      simpa using ha
    · have hxe : x ∈ K.erase v := Finset.mem_erase.2 ⟨hxv, Finset.mem_coe.1 hx⟩
      show (if x = v then a else g x) < n
      rw [if_neg hxv, hg x hxe]
      exact hC _

theorem edges_ge_of_chromatic {W : Type*} [Fintype W] [DecidableEq W] (H : SimpleGraph W) [DecidableRel H.Adj]
    (c : ℕ) (hdeg : ∀ v, 2 ≤ H.degree v) (hc : ¬ H.Colorable (c - 1)) :
    2 * Fintype.card W + c * (c - 3) ≤ 2 * H.edgeFinset.card := by
  classical
  rw [← sum_degrees_eq_twice_card_edges]
  by_cases hc3 : c ≤ 3
  · have h0 : c * (c - 3) = 0 := by simp [Nat.sub_eq_zero_of_le hc3]
    rw [h0, add_zero]
    have := Finset.card_nsmul_le_sum Finset.univ (fun v => H.degree v) 2 (fun v _ => hdeg v)
    simp at this
    linarith
  push Not at hc3
  let P : Finset W → Prop := fun K => ¬ (H.induce (K : Set W)).Colorable (c - 1)
  obtain ⟨K, hKmem, hKmin⟩ := Finset.exists_min_image (Finset.univ.filter P) Finset.card
    ⟨Finset.univ, by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, P]
      exact fun hcol => hc (hcol.of_hom ⟨fun x => ⟨x, by simp⟩, fun h => h⟩)⟩
  have hK : P K := (Finset.mem_filter.1 hKmem).2
  have hnb : ∀ v ∈ K, c - 1 ≤ H.degree v := by
    intro v hv
    have hle : (H.neighborFinset v ∩ K).card ≤ H.degree v := by
      rw [← card_neighborFinset_eq_degree]
      exact Finset.card_le_card Finset.inter_subset_left
    by_contra h
    push Not at h
    apply hK
    refine colorable_induce_of_erase H K v _ ?_ (by omega)
    by_contra h2
    have h3 := hKmin (K.erase v) (by simp [P, h2])
    have h4 := Finset.card_erase_lt_of_mem hv
    omega
  have hKc : c ≤ K.card := by
    by_contra h
    apply hK
    refine (H.induce (K : Set W)).colorable_of_fintype.mono ?_
    simp
    omega
  rw [← Finset.sum_add_sum_compl K]
  have h1 := Finset.card_nsmul_le_sum K (fun v => H.degree v) (c - 1) hnb
  have h2 := Finset.card_nsmul_le_sum Kᶜ (fun v => H.degree v) 2 (fun v _ => hdeg v)
  have hn : Kᶜ.card + K.card = Fintype.card W := by
    rw [Finset.card_compl]; have := Finset.card_le_univ K; omega
  simp only [smul_eq_mul] at h1 h2
  obtain ⟨e, rfl⟩ : ∃ e, c = e + 3 := ⟨c - 3, by omega⟩
  simp only [Nat.add_sub_cancel] at h1 ⊢
  have he : e + 3 - 1 = e + 2 := by omega
  rw [he] at h1
  nlinarith

end OMA569


namespace OMA569
open SimpleGraph Finset

/-- Edges of an induced subgraph inject into the edges of `H` with both ends in `B`. -/
theorem card_edgeFinset_induce_le {W : Type*} [Fintype W] [DecidableEq W] (H : SimpleGraph W)
    [DecidableRel H.Adj] (B : Finset W) :
    (H.induce (B : Set W)).edgeFinset.card ≤
      (H.edgeFinset.filter (fun e => ∀ x ∈ e, x ∈ B)).card := by
  refine Finset.card_le_card_of_injOn (Sym2.map Subtype.val) ?_ ?_
  · intro e he
    induction e using Sym2.ind with
    | h a b =>
      simp only [coe_filter, mem_edgeFinset, mem_edgeSet, Set.mem_ofPred_eq, Sym2.map_mk,
        Sym2.mem_iff, forall_eq_or_imp, forall_eq, mem_coe] at he ⊢
      exact ⟨by simpa using he, by simp, by simp⟩
  · exact (Sym2.map.injective Subtype.val_injective).injOn

/-- Number of `b`-subsets containing two fixed distinct vertices. -/
theorem card_pair_superset {W : Type*} [Fintype W] [DecidableEq W] (u v : W) (huv : u ≠ v)
    (b : ℕ) (hb : 2 ≤ b) :
    ((powersetCard b (univ : Finset W)).filter (fun B => u ∈ B ∧ v ∈ B)).card =
      (Fintype.card W - 2).choose (b - 2) := by
  have h2 : ({u, v} : Finset W).card = 2 := card_pair huv
  rw [← card_univ, ← h2, ← card_sdiff_of_subset (subset_univ _), ← card_powersetCard]
  refine card_nbij' (fun B => B \ {u, v}) (fun C => C ∪ {u, v}) ?_ ?_ ?_ ?_
  · intro B hB
    simp only [coe_filter, mem_powersetCard, Set.mem_ofPred_eq] at hB
    have hs : ({u, v} : Finset W) ⊆ B := by
      intro x hx; simp only [mem_insert, mem_singleton] at hx
      rcases hx with rfl | rfl
      exacts [hB.2.1, hB.2.2]
    simp only [mem_coe, mem_powersetCard]
    refine ⟨sdiff_subset_sdiff (subset_univ _) le_rfl, ?_⟩
    rw [card_sdiff_of_subset hs, hB.1.2, h2]
  · intro C hC
    simp only [mem_coe, mem_powersetCard] at hC
    have hd : Disjoint C {u, v} := by
      rw [disjoint_iff_ne]; intro a ha c hc h; subst h
      have := hC.1 ha; simp only [mem_sdiff] at this; exact this.2 hc
    simp only [coe_filter, mem_powersetCard, Set.mem_ofPred_eq, mem_union, mem_insert,
      mem_singleton, true_or, or_true, and_true]
    refine ⟨subset_univ _, ?_⟩
    rw [card_union_of_disjoint hd, hC.2, h2]; omega
  · intro B hB
    simp only [coe_filter, mem_powersetCard, Set.mem_ofPred_eq] at hB
    ext x; simp only [mem_union, mem_sdiff, mem_insert, mem_singleton]
    constructor
    · rintro (h | h | h)
      exacts [h.1, h ▸ hB.2.1, h ▸ hB.2.2]
    · intro h; by_cases hx : x = u ∨ x = v
      · right; exact hx
      · left; exact ⟨h, hx⟩
  · intro C hC
    simp only [mem_coe, mem_powersetCard] at hC
    ext x; simp only [mem_union, mem_sdiff, mem_insert, mem_singleton]
    constructor
    · rintro ⟨h | h, h'⟩
      · exact h
      · exact absurd h h'
    · intro h; refine ⟨Or.inl h, ?_⟩
      have := hC.1 h; simp only [mem_sdiff, mem_insert, mem_singleton] at this; exact this.2

/-- Double counting: summing the edges spanned over all `b`-subsets. -/
theorem sum_card_filter_powersetCard {W : Type*} [Fintype W] [DecidableEq W] (H : SimpleGraph W)
    [DecidableRel H.Adj] (b : ℕ) (hb : 2 ≤ b) :
    ∑ B ∈ powersetCard b (univ : Finset W), (H.edgeFinset.filter (fun e => ∀ x ∈ e, x ∈ B)).card =
      H.edgeFinset.card * (Fintype.card W - 2).choose (b - 2) := by
  simp_rw [card_filter]
  rw [sum_comm, card_eq_sum_ones, sum_mul]
  refine sum_congr rfl fun e he => ?_
  rw [← card_filter, one_mul]
  induction e using Sym2.ind with
  | h u v =>
    have huv : u ≠ v := (mem_edgeFinset.1 he).ne
    simp only [Sym2.mem_iff, forall_eq_or_imp, forall_eq]
    exact card_pair_superset u v huv b hb

theorem exists_sparse_part {W : Type*} [Fintype W] [DecidableEq W] (H : SimpleGraph W) [DecidableRel H.Adj]
    (hn : 3 ≤ Fintype.card W) (hm : 1 ≤ H.edgeFinset.card) :
    ∃ B : Finset W, B.card = Fintype.card W - (Fintype.card W / 2 + 1) ∧
      4 * (H.induce (B : Set W)).edgeFinset.card < H.edgeFinset.card := by
  by_cases hb2 : Fintype.card W - (Fintype.card W / 2 + 1) < 2
  · obtain ⟨B, -, hB⟩ := exists_subset_card_eq (s := (univ : Finset W))
      (n := Fintype.card W - (Fintype.card W / 2 + 1)) (by rw [card_univ]; omega)
    refine ⟨B, hB, ?_⟩
    have he : H.edgeFinset.filter (fun e => ∀ x ∈ e, x ∈ B) = ∅ := by
      rw [filter_eq_empty_iff]; intro e he hall
      induction e using Sym2.ind with
      | h u v =>
        have huv : u ≠ v := (mem_edgeFinset.1 he).ne
        have hs : ({u, v} : Finset W) ⊆ B := by
          intro x hx; simp only [mem_insert, mem_singleton] at hx
          rcases hx with rfl | rfl
          exacts [hall _ (Sym2.mem_mk_left _ _), hall _ (Sym2.mem_mk_right _ _)]
        have := card_le_card hs; rw [card_pair huv] at this; omega
    have := card_edgeFinset_induce_le H B
    rw [he, card_empty] at this; omega
  · push Not at hb2
    by_contra hcon
    push Not at hcon
    have hle : ∑ B ∈ powersetCard (Fintype.card W - (Fintype.card W / 2 + 1)) (univ : Finset W),
        H.edgeFinset.card ≤
        ∑ B ∈ powersetCard (Fintype.card W - (Fintype.card W / 2 + 1)) (univ : Finset W),
          4 * (H.edgeFinset.filter (fun e => ∀ x ∈ e, x ∈ B)).card :=
      sum_le_sum fun B hB => (hcon B (mem_powersetCard.1 hB).2).trans
        (Nat.mul_le_mul_left 4 (card_edgeFinset_induce_le H B))
    rw [sum_const, card_powersetCard, card_univ, smul_eq_mul, ← mul_sum,
      sum_card_filter_powersetCard H _ hb2] at hle
    obtain ⟨n, hn'⟩ : ∃ n, Fintype.card W = n + 2 := ⟨Fintype.card W - 2, by omega⟩
    obtain ⟨b, hb'⟩ : ∃ b, Fintype.card W - (Fintype.card W / 2 + 1) = b + 2 :=
      ⟨Fintype.card W - (Fintype.card W / 2 + 1) - 2, by omega⟩
    have h2b : 2 * (b + 2) < n + 2 := by omega
    rw [hb', hn'] at hle
    simp only [Nat.add_sub_cancel] at hle
    have k1 := Nat.add_one_mul_choose_eq (n + 1) (b + 1)
    have k2 := Nat.add_one_mul_choose_eq n b
    have hX : 0 < (n + 2).choose (b + 2) := Nat.choose_pos (by omega)
    have key : (n + 2) * (n + 1) * n.choose b = (n + 2).choose (b + 2) * ((b + 2) * (b + 1)) := by
      calc (n + 2) * (n + 1) * n.choose b = (n + 2) * ((n + 1) * n.choose b) := by ring
        _ = (n + 2) * ((n + 1).choose (b + 1) * (b + 1)) := by rw [k2]
        _ = ((n + 1 + 1) * (n + 1).choose (b + 1)) * (b + 1) := by ring
        _ = _ := by rw [k1]; ring
    have h4 : 4 * ((b + 2) * (b + 1)) < (n + 2) * (n + 1) := by nlinarith
    set X := (n + 2).choose (b + 2)
    set m := H.edgeFinset.card
    have hXm : 0 < X * m := Nat.mul_pos hX hm
    have : X * m * ((n + 2) * (n + 1)) ≤ X * m * (4 * ((b + 2) * (b + 1))) := by
      calc X * m * ((n + 2) * (n + 1)) ≤ 4 * (m * n.choose b) * ((n + 2) * (n + 1)) :=
            Nat.mul_le_mul_right _ hle
        _ = 4 * m * ((n + 2) * (n + 1) * n.choose b) := by ring
        _ = X * m * (4 * ((b + 2) * (b + 1))) := by rw [key]; ring
    have := Nat.le_of_mul_le_mul_left this hXm
    omega

end OMA569


namespace OMA569
open SimpleGraph

/-- A cyclic injective sequence `f : Fin (n+2) → V` (consecutive vertices adjacent, including
`f (last)` to `f 0`) gives a copy of `cycleGraph (n + 2)` in `G`. -/
theorem cycle_of_seq {V : Type*} (G : SimpleGraph V) (n : ℕ) (f : Fin (n + 2) → V)
    (hf : Function.Injective f) (hadj : ∀ i, G.Adj (f i) (f (i + 1))) :
    (cycleGraph (n + 2)).IsContained G :=
  ⟨⟨⟨f, fun {a b} h => by
      rcases cycleGraph_adj.mp h with h | h
      · have : a = b + 1 := by rw [← h]; abel
        subst this; exact (hadj b).symm
      · have : b = a + 1 := by rw [← h]; abel
        subst this; exact hadj a⟩, hf⟩⟩

/-- E1: a vertex red to all of a red path on `L - 1` vertices closes a red `C_L`. -/
theorem cycle_of_path_nbhd {V : Type*} (G : SimpleGraph V) (L : ℕ) (hL : 3 ≤ L) (v : V)
    (S : Set V) (hvS : v ∉ S) (hadj : ∀ x ∈ S, G.Adj v x)
    (hP : (pathGraph (L - 1)).IsContained (G.induce S)) : (cycleGraph L).IsContained G := by
  obtain ⟨n, rfl⟩ : ∃ n, L = n + 2 := ⟨L - 2, by omega⟩
  obtain ⟨c⟩ := hP
  have hn : n + 2 - 1 = n + 1 := by omega
  rw [hn] at c
  let x : Fin (n + 1) → V := fun j => (c j).1
  have hxS : ∀ j, x j ∈ S := fun j => (c j).2
  have hxinj : Function.Injective x := fun a b h => c.injective (Subtype.ext h)
  have hxadj : ∀ j : Fin (n + 1), ∀ k : Fin (n + 1), (j : ℕ) + 1 = k → G.Adj (x j) (x k) :=
    fun j k h => by
      have := c.toHom.map_rel (pathGraph_adj.mpr (Or.inl h))
      simpa using this
  let f : Fin (n + 2) → V := Fin.cases v x
  apply cycle_of_seq G n f
  · intro a b h
    induction a using Fin.cases with
    | zero =>
      induction b using Fin.cases with
      | zero => rfl
      | succ b =>
        simp only [f, Fin.cases_zero, Fin.cases_succ] at h
        exact absurd (h ▸ hxS b) hvS
    | succ a =>
      induction b using Fin.cases with
      | zero =>
        simp only [f, Fin.cases_zero, Fin.cases_succ] at h
        exact absurd (h ▸ hxS a) hvS
      | succ b => exact congrArg _ (hxinj h)
  · intro i
    induction i using Fin.cases with
    | zero =>
      have h1 : (0 : Fin (n + 2)) + 1 = Fin.succ 0 := by
        ext; simp
      rw [h1]; exact hadj _ (hxS 0)
    | succ j =>
      by_cases hj : (j : ℕ) < n
      · have h1 : j.succ + 1 = Fin.succ ⟨j + 1, by omega⟩ := by
          ext; simp [Fin.val_add]; omega
        rw [h1]; exact hxadj j _ rfl
      · have h1 : j = Fin.last n := Fin.ext (by simp; omega)
        subst h1
        rw [Fin.succ_last, Fin.last_add_one]; exact (hadj _ (hxS (Fin.last n))).symm

end OMA569

namespace OMA569
open SimpleGraph


/-- A clique on at least `j` vertices contains a path on `j` vertices. -/
theorem pathGraph_of_clique {U : Type*} [Fintype U] (H : SimpleGraph U) (j : ℕ)
    (hj : j ≤ Fintype.card U) (h : ∀ a b : U, a ≠ b → H.Adj a b) : pathGraph j ⊑ H := by
  obtain ⟨f⟩ := Function.Embedding.nonempty_of_card_le (by simpa using hj : Fintype.card (Fin j) ≤ Fintype.card U)
  exact ⟨⟨⟨f, fun hik => h _ _ (f.injective.ne hik.ne)⟩, f.injective⟩⟩

/-- Three pairwise adjacent vertices give a triangle. -/
theorem triangle_of_adj {V : Type*} (G : SimpleGraph V) (a b c : V) (hab : G.Adj a b)
    (hac : G.Adj a c) (hbc : G.Adj b c) : (completeGraph (Fin 3)).IsContained G := by
  refine ⟨⟨⟨![a, b, c], fun {i k} hik => ?_⟩, fun i k hik => ?_⟩⟩
  · fin_cases i <;> fin_cases k <;> simp_all [hab.symm, hac.symm, hbc.symm]
  · fin_cases i <;> fin_cases k <;> simp_all [hab.ne, hac.ne, hbc.ne, hab.ne.symm, hac.ne.symm, hbc.ne.symm]

/-- K3 case: `R(C_L, K_3) ≤ 3L` for `L ≥ 5`. -/
theorem cycle_or_blue_triangle {V : Type*} [Fintype V] (G : SimpleGraph V) (L : ℕ) (hL : 5 ≤ L)
    (hcard : 3 * L ≤ Fintype.card V) :
    (cycleGraph L).IsContained G ∨ (completeGraph (Fin 3)).IsContained Gᶜ := by
  classical
  by_cases hC : (cycleGraph L).IsContained G
  · exact Or.inl hC
  right
  have hne : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨x⟩ := hne
  set B := Finset.univ.filter (fun y => Gᶜ.Adj x y) with hB
  set R := Finset.univ.filter (fun y => G.Adj x y) with hR
  have hsplit : Fintype.card V ≤ 1 + B.card + R.card := by
    have : (Finset.univ : Finset V) ⊆ insert x (B ∪ R) := by
      intro y _
      by_cases hy : y = x
      · simp [hy]
      · by_cases hG : G.Adj x y
        · simp [hR, hG]
        · simp [hB, hG, Ne.symm hy]
    calc Fintype.card V = (Finset.univ : Finset V).card := Finset.card_univ.symm
      _ ≤ (insert x (B ∪ R)).card := Finset.card_le_card this
      _ ≤ (B ∪ R).card + 1 := Finset.card_insert_le _ _
      _ ≤ B.card + R.card + 1 := by have := Finset.card_union_le B R; omega
      _ = 1 + B.card + R.card := by ring
  by_cases hBL : L ≤ B.card
  · by_cases hbl : ∃ y ∈ B, ∃ z ∈ B, Gᶜ.Adj y z
    · obtain ⟨y, hy, z, hz, hyz⟩ := hbl
      simp only [hB, Finset.mem_filter, Finset.mem_univ, true_and] at hy hz
      exact triangle_of_adj Gᶜ x y z hy hz hyz
    push Not at hbl
    have hcl : ∀ y ∈ B, ∀ z ∈ B, y ≠ z → G.Adj y z := by
      intro y hy z hz hyz
      by_contra hG
      exact hbl y hy z hz ((compl_adj G y z).mpr ⟨hyz, hG⟩)
    obtain ⟨y, hy⟩ : B.Nonempty := Finset.card_pos.mp (by omega)
    refine absurd (cycle_of_path_nbhd G L (by omega) y ((B.erase y : Finset V) : Set V)
      (by simp) (fun z hz => ?_) ?_) hC
    · simp only [Finset.coe_erase, Set.mem_sdiff, Finset.mem_coe, Set.mem_singleton_iff] at hz
      exact hcl y hy z hz.1 (Ne.symm hz.2)
    · apply pathGraph_of_clique
      · simp only [Finset.coe_sort_coe, Fintype.card_coe]
        rw [Finset.card_erase_of_mem hy]; omega
      · intro a b hab
        simp only [comap_adj, Function.Embedding.coe_subtype]
        have ha := a.2
        have hb := b.2
        simp only [Finset.coe_erase, Set.mem_sdiff, Finset.mem_coe] at ha hb
        exact hcl a ha.1 b hb.1 (fun e => hab (Subtype.ext e))
  · push Not at hBL
    have hRc : 2 * L ≤ R.card := by omega
    have hfree : (pathGraph (L - 1)).Free (G.induce ((R : Finset V) : Set V)) := by
      intro hP
      exact hC (cycle_of_path_nbhd G L (by omega) x (R : Set V) (by simp [hR])
        (fun z hz => by simpa [hR] using hz) hP)
    obtain ⟨s, hs3, hind⟩ := indep_of_pathFree (G.induce ((R : Finset V) : Set V)) (L - 1) 3
      (by omega) hfree (by simp only [Finset.coe_sort_coe, Fintype.card_coe]; omega)
    obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp hs3
    have key : ∀ p q : ((R : Finset V) : Set V), p ∈ ({a, b, c} : Finset _) →
        q ∈ ({a, b, c} : Finset _) → p ≠ q → Gᶜ.Adj p q := by
      intro p q hp hq hpq
      refine (compl_adj G p q).mpr ⟨fun e => hpq (Subtype.ext e), ?_⟩
      have := hind (Finset.mem_coe.mpr hp) (Finset.mem_coe.mpr hq) hpq
      simpa using this
    exact triangle_of_adj Gᶜ a b c (key a b (by simp) (by simp) hab)
      (key a c (by simp) (by simp) hac) (key b c (by simp) (by simp) hbc)

/-- Lower bound: `L ≤ R(C_L, K_2)`. -/
theorem le_graphRamsey_K2 (L : ℕ) (hL : 3 ≤ L) :
    L ≤ graphRamsey (cycleGraph L) (completeGraph (Fin 2)) := by
  classical
  apply le_csInf
  · refine ⟨L, fun C => ?_⟩
    by_cases h : ∃ x y : Fin L, x ≠ y ∧ ¬ C.Adj x y
    · obtain ⟨x, y, hxy, hC⟩ := h
      right
      refine ⟨⟨⟨![x, y], fun {i k} hik => ?_⟩, fun i k hik => ?_⟩⟩
      · have hc : Cᶜ.Adj x y := (compl_adj C x y).mpr ⟨hxy, hC⟩
        fin_cases i <;> fin_cases k <;> simp_all [hc.symm]
      · fin_cases i <;> fin_cases k <;> simp_all [Ne.symm hxy]
    · push Not at h
      left
      exact ⟨⟨⟨id, fun {a b} hab => h a b hab.ne⟩, Function.injective_id⟩⟩
  · intro n hn
    rcases hn ⊤ with ⟨⟨f⟩⟩ | ⟨⟨f⟩⟩
    · simpa using Fintype.card_le_of_injective _ f.injective
    · exfalso
      have := f.toHom.map_adj (show (completeGraph (Fin 2)).Adj 0 1 by simp)
      simp at this

end OMA569


namespace OMA569
open SimpleGraph

/-- M2a: extend a blue copy of `H - u`, or find a red star from an image of a neighbour of `u`.
CORRECTED: the frozen statement is false for `V` empty, `W = {u}` (hF holds vacuously, but neither
disjunct can hold), so the hypothesis `hV : Fintype.card W ≤ Fintype.card V` is added. -/
theorem extend_or_star {V W : Type*} [Fintype V] [Fintype W] (G : SimpleGraph V)
    (H : SimpleGraph W) [DecidableRel H.Adj] (u : W)
    (hF : (H.induce ({u}ᶜ : Set W)).IsContained Gᶜ)
    (hV : Fintype.card W ≤ Fintype.card V) :
    H.IsContained Gᶜ ∨ ∃ v : V, ∃ S : Finset V, v ∉ S ∧ (∀ x ∈ S, G.Adj v x) ∧
      Fintype.card V + 1 ≤ H.degree u * S.card + Fintype.card W := by
  classical
  obtain ⟨φ⟩ := hF
  set F : Finset V := Finset.univ.image φ with hFdef
  set O : Finset V := Finset.univ \ F with hOdef
  have hmemF : ∀ w : ({u}ᶜ : Set W), φ w ∈ F := fun w => Finset.mem_image_of_mem _ (by simp)
  have hFcard : F.card + 1 ≤ Fintype.card W := by
    have h0 : F.card ≤ Fintype.card ({u}ᶜ : Set W) := Finset.card_image_le.trans_eq Finset.card_univ
    have h1 := Fintype.card_subtype_compl (fun w : W => w = u)
    have h2 : Fintype.card {w : W // w = u} = 1 := Fintype.card_unique
    have h3 : Fintype.card {w : W // w = u} ≤ Fintype.card W := Fintype.card_subtype_le _
    have h4 : Fintype.card ({u}ᶜ : Set W) = Fintype.card {w : W // ¬ w = u} :=
      Fintype.card_congr (Equiv.refl _)
    omega
  have hOcard : O.card + F.card = Fintype.card V := by
    rw [hOdef, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ]
    have := Finset.card_le_univ F
    omega
  have hne : ∀ {w : W}, H.Adj u w → w ≠ u := fun h => (H.ne_of_adj h).symm
  by_cases hc : ∃ x ∈ O, ∀ w (hw : H.Adj u w), Gᶜ.Adj x (φ ⟨w, hne hw⟩)
  · left
    obtain ⟨x, hxO, hx⟩ := hc
    have hxF : x ∉ F := (Finset.mem_sdiff.mp hxO).2
    let ψ : W → V := fun w => if h : w = u then x else φ ⟨w, h⟩
    have hψ : ∀ {a b : W}, H.Adj a b → Gᶜ.Adj (ψ a) (ψ b) := by
      intro a b hab
      by_cases ha : a = u <;> by_cases hb : b = u
      · subst ha; subst hb; exact absurd hab (H.irrefl)
      · subst ha; simp only [ψ, dif_pos, dif_neg hb]; exact hx b hab
      · subst hb; simp only [ψ, dif_pos, dif_neg ha]; exact (hx a hab.symm).symm
      · simp only [ψ, dif_neg ha, dif_neg hb]
        exact φ.toHom.map_rel (a := ⟨a, ha⟩) (b := ⟨b, hb⟩) (by simpa using hab)
    have hinj : Function.Injective ψ := by
      intro a b hab
      by_cases ha : a = u <;> by_cases hb : b = u
      · rw [ha, hb]
      · simp only [ψ, dif_pos ha, dif_neg hb] at hab
        exact absurd (hab ▸ hmemF ⟨b, hb⟩) hxF
      · simp only [ψ, dif_pos hb, dif_neg ha] at hab
        exact absurd (hab ▸ hmemF ⟨a, ha⟩) hxF
      · simp only [ψ, dif_neg ha, dif_neg hb] at hab
        exact congrArg Subtype.val (φ.injective hab)
    exact ⟨⟨⟨ψ, hψ⟩, hinj⟩⟩
  · right
    push Not at hc
    let Sw : W → Finset V := fun w => O.filter (fun x => ∃ h : w ≠ u, G.Adj (φ ⟨w, h⟩) x)
    have hcov : O ⊆ (H.neighborFinset u).biUnion Sw := by
      intro x hxO
      obtain ⟨w, hw, hnot⟩ := hc x hxO
      have hxF : x ∉ F := (Finset.mem_sdiff.mp hxO).2
      have hxne : x ≠ φ ⟨w, hne hw⟩ := fun h => hxF (h ▸ hmemF _)
      have hG : G.Adj (φ ⟨w, hne hw⟩) x := by
        rw [compl_adj] at hnot
        push Not at hnot
        exact (hnot hxne).symm
      exact Finset.mem_biUnion.mpr ⟨w, (mem_neighborFinset _ _ _).mpr hw,
        Finset.mem_filter.mpr ⟨hxO, hne hw, hG⟩⟩
    have hOpos : 0 < O.card := by omega
    obtain ⟨x0, hx0⟩ := Finset.card_pos.mp hOpos
    obtain ⟨w0, hw0, -⟩ := Finset.mem_biUnion.mp (hcov hx0)
    obtain ⟨wm, hwm, hmax⟩ :=
      Finset.exists_max_image (H.neighborFinset u) (fun w => (Sw w).card) ⟨w0, hw0⟩
    have hwmne : wm ≠ u := hne ((mem_neighborFinset _ _ _).mp hwm)
    refine ⟨φ ⟨wm, hwmne⟩, Sw wm, ?_, ?_, ?_⟩
    · intro hmem
      exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hmem).1).2 (hmemF _)
    · intro x hx
      obtain ⟨-, _, hG⟩ := Finset.mem_filter.mp hx
      exact hG
    · have h1 : O.card ≤ ∑ w ∈ H.neighborFinset u, (Sw w).card :=
        (Finset.card_le_card hcov).trans Finset.card_biUnion_le
      have h2 : ∑ w ∈ H.neighborFinset u, (Sw w).card ≤
          (H.neighborFinset u).card * (Sw wm).card := by
        simpa using Finset.sum_le_card_nsmul _ _ _ hmax
      rw [card_neighborFinset_eq_degree] at h2
      omega

end OMA569


namespace OMA569
open SimpleGraph

/-- `H` has no isolated vertices. -/
def NoIso {W : Type*} (H : SimpleGraph W) : Prop := ∀ v, ∃ w, H.Adj v w

/-- Every red graph on at least `L * e(H)` vertices has a red `C_L` or a blue `H`. -/
def Good (L : ℕ) {W : Type} (H : SimpleGraph W) : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
    L * H.edgeSet.ncard ≤ Fintype.card V → (cycleGraph L).IsContained G ∨ H.IsContained Gᶜ

/-- A graph without isolated vertices has at most twice as many vertices as edges. -/
theorem card_le_two_mul_edges {X : Type*} [Fintype X] (K : SimpleGraph X) (hK : NoIso K) :
    Fintype.card X ≤ 2 * K.edgeSet.ncard := by
  classical
  rw [← coe_edgeFinset, Set.ncard_coe_finset, ← sum_degrees_eq_twice_card_edges]
  calc Fintype.card X = ∑ _v : X, 1 := by simp
    _ ≤ ∑ v, K.degree v := Finset.sum_le_sum fun v _ => (K.degree_pos_iff_exists_adj v).mpr (hK v)

/-- Edges of the two sides of a closed vertex set add up to at most the edges of `H`. -/
theorem edges_split {W : Type*} [Finite W] (H : SimpleGraph W) (S : Set W) :
    (H.induce S).edgeSet.ncard + (H.induce Sᶜ).edgeSet.ncard ≤ H.edgeSet.ncard := by
  rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq,
    ← Nat.card_sum]
  refine Nat.card_le_card_of_injective
    (Sum.elim (Copy.induce H S).mapEdgeSet (Copy.induce H Sᶜ).mapEdgeSet) ?_
  have key : ∀ (e1 : (H.induce S).edgeSet) (e2 : (H.induce Sᶜ).edgeSet),
      (Copy.induce H S).mapEdgeSet e1 ≠ (Copy.induce H Sᶜ).mapEdgeSet e2 := by
    rintro ⟨e1, he1⟩ ⟨e2, he2⟩ h
    have h' := congrArg Subtype.val h
    induction e1 using Sym2.ind with
    | h a b =>
    induction e2 using Sym2.ind with
    | h c d =>
    change Sym2.map Subtype.val s(a, b) = Sym2.map Subtype.val s(c, d) at h'
    have hm : (a : W) ∈ Sym2.map Subtype.val s(c, d) := by
      rw [← h']; exact Sym2.mem_map.mpr ⟨a, Sym2.mem_mk_left _ _, rfl⟩
    obtain ⟨y, -, hy⟩ := Sym2.mem_map.mp hm
    exact y.2 (hy ▸ a.2)
  rintro (e1 | e1) (e2 | e2) h
  · exact congrArg Sum.inl ((Copy.induce H S).mapEdgeSet.injective h)
  · exact absurd h (key e1 e2)
  · exact absurd h.symm (key e2 e1)
  · exact congrArg Sum.inr ((Copy.induce H Sᶜ).mapEdgeSet.injective h)

/-- A graph with an edge has positive edge count. -/
theorem ncard_edgeSet_pos {X : Type*} [Finite X] (K : SimpleGraph X) (a b : X) (h : K.Adj a b) :
    0 < K.edgeSet.ncard :=
  Set.ncard_pos (Set.toFinite _) |>.mpr ⟨s(a, b), h⟩

/-- M1: a graph without isolated vertices that is not connected is `Good` once all graphs with
fewer edges are. -/
theorem good_of_not_connected (L : ℕ) (hL : 3 ≤ L) {W : Type} [Fintype W] (H : SimpleGraph W)
    (hH : NoIso H) (hnc : ¬ H.Connected)
    (hIH : ∀ (W' : Type) [Fintype W'] (H' : SimpleGraph W'), NoIso H' →
      H'.edgeSet.ncard < H.edgeSet.ncard → Good L H') : Good L H := by
  classical
  intro V _ G hV
  rcases isEmpty_or_nonempty W with hW | ⟨⟨w⟩⟩
  · exact Or.inr ⟨⟨⟨isEmptyElim, fun {a} => isEmptyElim a⟩, fun a => isEmptyElim a⟩⟩
  set S : Set W := (H.connectedComponentMk w).supp with hSdef
  have hS : ∀ u v, u ∈ S → H.Adj u v → v ∈ S := fun u v hu huv =>
    ConnectedComponent.mem_supp_of_adj_mem_supp _ hu huv
  have hSc : ∀ u v, u ∈ Sᶜ → H.Adj u v → v ∈ Sᶜ := fun u v hu huv hv =>
    hu (hS v u hv huv.symm)
  obtain ⟨x, hx⟩ : ∃ x, x ∉ S := by
    by_contra hall
    push Not at hall
    refine hnc (connected_iff _ |>.mpr ⟨fun u v => ?_, ⟨w⟩⟩)
    have hu := ConnectedComponent.mem_supp_iff _ _ |>.mp (hall u)
    have hv := ConnectedComponent.mem_supp_iff _ _ |>.mp (hall v)
    exact ConnectedComponent.exact (hu.trans hv.symm)
  have hwS : w ∈ S := ConnectedComponent.mem_supp_iff _ _ |>.mpr rfl
  set H1 := H.induce S
  set H2 := H.induce Sᶜ
  have hN1 : NoIso H1 := fun v => by
    obtain ⟨y, hy⟩ := hH v
    exact ⟨⟨y, hS _ _ v.2 hy⟩, hy⟩
  have hN2 : NoIso H2 := fun v => by
    obtain ⟨y, hy⟩ := hH v
    exact ⟨⟨y, hSc _ _ v.2 hy⟩, hy⟩
  have hsplit : H1.edgeSet.ncard + H2.edgeSet.ncard ≤ H.edgeSet.ncard := edges_split H S
  obtain ⟨w', hw'⟩ := hH w
  obtain ⟨x', hx'⟩ := hH x
  have he1 : 0 < H1.edgeSet.ncard :=
    ncard_edgeSet_pos H1 ⟨w, hwS⟩ ⟨w', hS _ _ hwS hw'⟩ hw'
  have he2 : 0 < H2.edgeSet.ncard :=
    ncard_edgeSet_pos H2 ⟨x, hx⟩ ⟨x', hSc _ _ hx hx'⟩ hx'
  have hG1 : Good L H1 := hIH _ H1 hN1 (by omega)
  have hG2 : Good L H2 := hIH _ H2 hN2 (by omega)
  have hcardS : Fintype.card S ≤ 2 * H1.edgeSet.ncard := card_le_two_mul_edges H1 hN1
  have hmul : L * H1.edgeSet.ncard + L * H2.edgeSet.ncard ≤ L * H.edgeSet.ncard := by
    rw [← mul_add]; exact Nat.mul_le_mul_left _ hsplit
  have h2L : 2 * H1.edgeSet.ncard ≤ L * H1.edgeSet.ncard := Nat.mul_le_mul_right _ (by omega)
  rcases hG1 V G (by omega) with hcyc | hf1
  · exact Or.inl hcyc
  obtain ⟨f1⟩ := hf1
  set R : Set V := (Set.range f1)ᶜ
  have hcardR : Fintype.card V - Fintype.card S ≤ Fintype.card R := by
    rw [Fintype.card_compl_set]
    have := Nat.card_congr (Equiv.ofInjective _ f1.injective)
    simp only [Nat.card_eq_fintype_card] at this
    rw [this]
    exact le_rfl
  rcases hG2 R (G.induce R) (by omega) with hcyc | hf2
  · exact Or.inl (hcyc.trans ⟨Copy.induce G R⟩)
  obtain ⟨f2⟩ := hf2
  refine Or.inr ⟨⟨⟨fun v => if h : v ∈ S then f1 ⟨v, h⟩ else (f2 ⟨v, h⟩ : V), ?_⟩, ?_⟩⟩
  · intro a b hab
    by_cases ha : a ∈ S
    · have hb : b ∈ S := hS _ _ ha hab
      simp only [ha, hb, dite_true]
      exact f1.toHom.map_rel (show H1.Adj ⟨a, ha⟩ ⟨b, hb⟩ from hab)
    · have hb : b ∉ S := hSc _ _ ha hab
      simp only [ha, hb, dite_false]
      have := f2.toHom.map_rel (show H2.Adj ⟨a, ha⟩ ⟨b, hb⟩ from hab)
      rw [compl_adj] at this ⊢
      exact ⟨fun h => this.1 (Subtype.ext h), this.2⟩
  · intro a b hab
    have mem : ∀ (c : W) (hc : c ∉ S) (d : S), (f2 ⟨c, hc⟩ : V) ≠ f1 d := fun c hc d h =>
      (f2 ⟨c, hc⟩).2 ⟨d, h.symm⟩
    dsimp at hab
    by_cases ha : a ∈ S <;> by_cases hb : b ∈ S <;> simp only [ha, hb, dite_true, dite_false] at hab
    · exact congrArg Subtype.val (f1.injective hab)
    · exact absurd hab.symm (mem b hb _)
    · exact absurd hab (mem a ha _)
    · exact congrArg Subtype.val (f2.injective (Subtype.ext hab))

end OMA569

/-! E3: the second neighbourhood of a vertex in a red-C_L-free graph has no red P_(L+1). -/

namespace OMA569
open SimpleGraph

theorem cyc_E3 {V : Type*} (G : SimpleGraph V) (l : List V) (h3 : 3 ≤ l.length) (hnd : l.Nodup)
    (hc : (l ++ l.take 1).IsChain G.Adj) : (cycleGraph l.length).IsContained G := by
  obtain ⟨m, hm⟩ : ∃ m, l.length = m + 2 := ⟨l.length - 2, by omega⟩
  have hc' := List.isChain_iff_getElem.mp hc
  rw [hm]
  let f : Fin (m + 2) → V := fun i => l[(i : ℕ)]'(by omega)
  have hf : Function.Injective f := by
    intro i j h
    exact Fin.ext ((List.Nodup.getElem_inj_iff hnd).mp h)
  have hadj : ∀ i, G.Adj (f i) (f (i + 1)) := by
    intro i
    by_cases hi : (i : ℕ) + 1 < m + 2
    · have hv : ((i + 1 : Fin (m + 2)) : ℕ) = i + 1 := by
        rw [Fin.val_add_one_of_lt (by rw [Fin.lt_def]; simp; omega)]
      have := hc' i (by simp; omega)
      simp only [f]
      rw [List.getElem_append_left (by omega), List.getElem_append_left (by omega)] at this
      convert this using 2
    · have hi' : (i : ℕ) = m + 1 := by omega
      have hv : ((i + 1 : Fin (m + 2)) : ℕ) = 0 := by
        have : i = Fin.last (m + 1) := Fin.ext (by simp [hi'])
        subst this; simp
      have := hc' (m + 1) (by simp; omega)
      rw [List.getElem_append_left (by omega), List.getElem_append_right (by omega)] at this
      simp only [List.getElem_take] at this
      have e1 : f i = l[m + 1] := by simp [f, hi']
      have e2 : f (i + 1) = l[m + 1 + 1 - l.length] := by simp only [f, hv]; congr 1; omega
      rw [e1, e2]; exact this
  exact ⟨⟨⟨f, fun {a b} h => by
      rcases cycleGraph_adj.mp h with h | h
      · have : a = b + 1 := by rw [← h]; abel
        subst this; exact (hadj b).symm
      · have : b = a + 1 := by rw [← h]; abel
        subst this; exact hadj a⟩, hf⟩⟩

/-- The segment `x a, x (a+1), ..., x (a+n-1)`. -/
def segE3 {V : Type*} (x : ℕ → V) (a n : ℕ) : List V := (List.range' a n).map x

theorem segE3_mem {V : Type*} (x : ℕ → V) (a n : ℕ) (y : V) :
    y ∈ segE3 x a n ↔ ∃ i, a ≤ i ∧ i < a + n ∧ x i = y := by
  simp only [segE3, List.mem_map, List.mem_range'_1]
  constructor
  · rintro ⟨i, ⟨h1, h2⟩, h3⟩; exact ⟨i, h1, h2, h3⟩
  · rintro ⟨i, h1, h2, h3⟩; exact ⟨i, ⟨h1, h2⟩, h3⟩

theorem segE3_head {V : Type*} (x : ℕ → V) (a n : ℕ) : (segE3 x a (n + 1)).head? = some (x a) := by
  simp [segE3, List.range'_succ]

theorem segE3_last {V : Type*} (x : ℕ → V) (a n : ℕ) :
    (segE3 x a (n + 1)).getLast? = some (x (a + n)) := by
  simp [segE3, List.range'_concat]

theorem segE3_chain {V : Type*} (G : SimpleGraph V) (x : ℕ → V) (L : ℕ)
    (hadj : ∀ i, i < L → G.Adj (x i) (x (i + 1))) (a n : ℕ) (h : a + n ≤ L + 1) :
    (segE3 x a n).IsChain G.Adj := by
  rw [List.isChain_iff_getElem]
  intro i hi
  simp only [segE3, List.length_map, List.length_range'] at hi
  simp only [segE3, List.getElem_map, List.getElem_range']
  have := hadj (a + 1 * i) (by omega)
  simpa [Nat.add_assoc] using this

theorem segE3_nodup {V : Type*} (x : ℕ → V) (L : ℕ)
    (hinj : ∀ i j, i ≤ L → j ≤ L → x i = x j → i = j) (a n : ℕ) (h : a + n ≤ L + 1) :
    (segE3 x a n).Nodup := by
  apply List.Nodup.map_on _ List.nodup_range'
  intro i hi j hj e
  rw [List.mem_range'_1] at hi hj
  exact hinj i j (by omega) (by omega) e

theorem twoU_E3 {V : Type*} (G : SimpleGraph V) (L : ℕ) (x u : ℕ → V) (v : V)
    (hC : ∀ l : List V, l.length = L → l.Nodup → (l ++ l.take 1).IsChain G.Adj → False)
    (hxadj : ∀ i, i < L → G.Adj (x i) (x (i + 1)))
    (hxinj : ∀ i j, i ≤ L → j ≤ L → x i = x j → i = j)
    (hux : ∀ i, G.Adj (u i) (x i)) (hvu : ∀ j, G.Adj v (u j))
    (hxu : ∀ i j, x i ≠ u j) (hxv : ∀ i, x i ≠ v) (huv : ∀ j, u j ≠ v)
    (a n : ℕ) (han : a + n ≤ L) (hn : n + 4 = L) (hne : u a ≠ u (a + n)) : False := by
  apply hC (v :: u a :: (segE3 x a (n + 1) ++ [u (a + n)]))
  · simp [segE3]; omega
  · have hs := segE3_nodup x L hxinj a (n + 1) (by omega)
    have hk : ∀ y ∈ segE3 x a (n + 1), y ≠ v ∧ ∀ j, y ≠ u j := by
      intro y hy
      obtain ⟨i, -, -, rfl⟩ := (segE3_mem x a _ y).mp hy
      exact ⟨hxv i, hxu i⟩
    refine List.nodup_cons.mpr ⟨?_, List.nodup_cons.mpr ⟨?_,
      List.nodup_append.mpr ⟨hs, List.nodup_singleton _, ?_⟩⟩⟩
    · simp only [List.mem_cons, List.mem_append, List.not_mem_nil, not_or, or_false]
      exact ⟨(huv a).symm, fun h => (hk v h).1 rfl, (huv _).symm⟩
    · simp only [List.mem_append, List.mem_singleton, not_or]
      exact ⟨fun h => (hk _ h).2 a rfl, hne⟩
    · intro y hy z hz
      simp only [List.mem_singleton] at hz; subst hz; exact (hk y hy).2 _
  · have hs := segE3_chain G x L hxadj a (n + 1) (by omega)
    simp only [List.take_succ_cons, List.take_zero, List.cons_append, List.append_assoc]
    rw [List.isChain_cons_cons]
    refine ⟨hvu a, ?_⟩
    rw [← List.singleton_append, List.isChain_append]
    refine ⟨List.isChain_singleton _, ?_, ?_⟩
    · rw [List.isChain_append]
      refine ⟨hs, ?_, ?_⟩
      · simp [List.isChain_cons_cons, (hvu _).symm]
      · rw [segE3_last]; simp [(hux _).symm]
    · rw [List.head?_append, segE3_head]; simp [hux]

theorem oneU_E3 {V : Type*} (G : SimpleGraph V) (L : ℕ) (x u : ℕ → V)
    (hC : ∀ l : List V, l.length = L → l.Nodup → (l ++ l.take 1).IsChain G.Adj → False)
    (hxadj : ∀ i, i < L → G.Adj (x i) (x (i + 1)))
    (hxinj : ∀ i j, i ≤ L → j ≤ L → x i = x j → i = j)
    (hux : ∀ i, G.Adj (u i) (x i)) (hxu : ∀ i j, x i ≠ u j)
    (a n : ℕ) (han : a + n ≤ L) (hn : n + 2 = L) (he : u a = u (a + n)) : False := by
  apply hC (u a :: segE3 x a (n + 1))
  · simp [segE3]; omega
  · have hs := segE3_nodup x L hxinj a (n + 1) (by omega)
    refine List.nodup_cons.mpr ⟨?_, hs⟩
    rw [segE3_mem]
    rintro ⟨i, -, -, h⟩; exact hxu i a h
  · have hs := segE3_chain G x L hxadj a (n + 1) (by omega)
    simp only [List.take_succ_cons, List.take_zero, List.cons_append]
    rw [← List.singleton_append, List.isChain_append]
    refine ⟨List.isChain_singleton _, ?_, ?_⟩
    · rw [List.isChain_append]
      refine ⟨hs, List.isChain_singleton _, ?_⟩
      rw [segE3_last]; simp [he, (hux _).symm]
    · rw [List.head?_append, segE3_head]; simp [hux]

theorem core_E3 {V : Type*} (G : SimpleGraph V) (L : ℕ) (hL : 5 ≤ L) (hodd : Odd L)
    (x u : ℕ → V) (v : V)
    (hC : ∀ l : List V, l.length = L → l.Nodup → (l ++ l.take 1).IsChain G.Adj → False)
    (hxadj : ∀ i, i < L → G.Adj (x i) (x (i + 1)))
    (hxinj : ∀ i j, i ≤ L → j ≤ L → x i = x j → i = j)
    (hux : ∀ i, G.Adj (u i) (x i)) (hvu : ∀ j, G.Adj v (u j))
    (hxu : ∀ i j, x i ≠ u j) (hxv : ∀ i, x i ≠ v) (huv : ∀ j, u j ≠ v) : False := by
  have A := twoU_E3 G L x u v hC hxadj hxinj hux hvu hxu hxv huv
  have B := oneU_E3 G L x u hC hxadj hxinj hux hxu
  have hxeq : ∀ i j, i ≤ L → j ≤ L → (x i = x j ↔ i = j) :=
    fun i j hi hj => ⟨hxinj i j hi hj, fun h => h ▸ rfl⟩
  have hux' : ∀ i j, u j ≠ x i := fun i j h => hxu i j h.symm
  by_cases h5 : L = 5
  · subst h5
    by_cases e01 : u 0 = u 1
    · by_cases e12 : u 1 = u 2
      · by_cases e23 : u 2 = u 3
        · exact B 0 3 (by omega) (by omega) (by rw [e01, e12, e23])
        · exact A 2 1 (by omega) (by omega) e23
      · exact A 1 1 (by omega) (by omega) e12
    · exact A 0 1 (by omega) (by omega) e01
  have h7 : 7 ≤ L := by obtain ⟨k, rfl⟩ := hodd; omega
  have c8 : ∀ i, i ≤ 4 → u i = u (L - 4 + i) := by
    intro i hi
    by_contra h
    exact A i (L - 4) (by omega) (by omega) (by rwa [show i + (L - 4) = L - 4 + i by omega])
  have c9 : ∀ i, i ≤ 2 → u i ≠ u (i + 2) := by
    intro i hi h
    exact B i (L - 2) (by omega) (by omega)
      (by rw [h, c8 (i + 2) (by omega)]; congr 1; omega)
  by_cases h7' : L = 7
  · subst h7'
    have e25 : u 2 = u 5 := c8 2 (by omega)
    have e03 : u 0 = u 3 := c8 0 (by omega)
    have e36 : u 3 = u 6 := c8 3 (by omega)
    have n02 : u 0 ≠ u 2 := c9 0 (by omega)
    apply hC [u 0, x 0, x 1, x 2, u 2, x 5, x 6] rfl
    · simp [hxeq, hxu, hux', n02]
    · simp only [List.cons_append, List.nil_append, List.take_succ_cons, List.take_zero,
        List.isChain_cons_cons, List.isChain_singleton, and_true]
      refine ⟨hux 0, hxadj 0 (by omega), hxadj 1 (by omega), (hux 2).symm, ?_,
        hxadj 5 (by omega), ?_⟩
      · rw [e25]; exact hux 5
      · rw [e03, e36]; exact (hux 6).symm
  have h9 : 9 ≤ L := by obtain ⟨k, rfl⟩ := hodd; omega
  have hk : ∀ a m, ∀ y ∈ segE3 x a m, ∃ i, a ≤ i ∧ i < a + m ∧ x i = y :=
    fun a m y hy => (segE3_mem x a m y).mp hy
  have n02 : u 0 ≠ u 2 := c9 0 (by omega)
  have hx4 : ∀ i j, i ≤ 4 → j ≤ 4 → (x i = x j ↔ i = j) :=
    fun i j hi hj => hxeq i j (by omega) (by omega)
  by_cases e04 : u 0 = u 4
  · obtain ⟨n, hn⟩ : ∃ n, L = n + 6 := ⟨L - 6, by omega⟩
    have e2 : u 2 = u (4 + n) := by rw [c8 2 (by omega)]; congr 1; omega
    have hs := segE3_chain G x L hxadj 4 (n + 1) (by omega)
    have hsn := segE3_nodup x L hxinj 4 (n + 1) (by omega)
    apply hC ([u 0, x 0, x 1, x 2, u 2] ++ (segE3 x 4 (n + 1)).reverse)
    · simp [segE3]; omega
    · refine List.nodup_append.mpr ⟨by simp [hx4, hxu, hux', n02], List.nodup_reverse.mpr hsn, ?_⟩
      intro y hy z hz
      rw [List.mem_reverse] at hz
      obtain ⟨i, hi1, hi2, rfl⟩ := hk _ _ z hz
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with rfl | rfl | rfl | rfl | rfl
      · exact hux' i 0
      · exact fun h => by have := hxinj 0 i (by omega) (by omega) h; omega
      · exact fun h => by have := hxinj 1 i (by omega) (by omega) h; omega
      · exact fun h => by have := hxinj 2 i (by omega) (by omega) h; omega
      · exact hux' i 2
    · have hr : ((segE3 x 4 (n + 1)).reverse).IsChain G.Adj :=
        List.isChain_reverse.mpr (hs.imp fun _ _ h => h.symm)
      rw [List.take_append_of_le_length (by simp), List.isChain_append]
      refine ⟨?_, List.isChain_singleton _, ?_⟩
      · rw [List.isChain_append]
        refine ⟨?_, hr, ?_⟩
        · simp only [List.isChain_cons_cons, List.isChain_singleton, and_true]
          exact ⟨hux 0, hxadj 0 (by omega), hxadj 1 (by omega), (hux 2).symm⟩
        · rw [List.head?_reverse, segE3_last]; simp [e2, hux]
      · rw [List.getLast?_append_of_ne_nil _ (by simp [segE3]), List.getLast?_reverse, segE3_head]
        simp [e04, (hux 4).symm]
  · obtain ⟨n, hn⟩ : ∃ n, L = n + 8 := ⟨L - 8, by omega⟩
    have e0 : u 0 = u (4 + n) := by rw [c8 0 (by omega)]; congr 1; omega
    have n24 : u 2 ≠ u 4 := c9 2 (by omega)
    have hs := segE3_chain G x L hxadj 4 (n + 1) (by omega)
    have hsn := segE3_nodup x L hxinj 4 (n + 1) (by omega)
    apply hC ([u 0, x 0, x 1, x 2, u 2, v, u 4] ++ segE3 x 4 (n + 1))
    · simp [segE3]; omega
    · refine List.nodup_append.mpr ⟨?_, hsn, ?_⟩
      · simp [hx4, hxu, hux', n02, n24, e04, huv, hxv, (huv _).symm]
      intro y hy z hz
      obtain ⟨i, hi1, hi2, rfl⟩ := hk _ _ z hz
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact hux' i 0
      · exact fun h => by have := hxinj 0 i (by omega) (by omega) h; omega
      · exact fun h => by have := hxinj 1 i (by omega) (by omega) h; omega
      · exact fun h => by have := hxinj 2 i (by omega) (by omega) h; omega
      · exact hux' i 2
      · exact fun h => hxv i h.symm
      · exact hux' i 4
    · rw [List.take_append_of_le_length (by simp), List.isChain_append]
      refine ⟨?_, List.isChain_singleton _, ?_⟩
      · rw [List.isChain_append]
        refine ⟨?_, hs, ?_⟩
        · simp only [List.isChain_cons_cons, List.isChain_singleton, and_true]
          exact ⟨hux 0, hxadj 0 (by omega), hxadj 1 (by omega), (hux 2).symm, (hvu 2).symm,
            hvu 4⟩
        · rw [segE3_head]; simp [hux]
      · rw [List.getLast?_append_of_ne_nil _ (by simp [segE3]), segE3_last]
        simp [e0, (hux _).symm]

/-- E3: in a red-`C_L`-free graph (`L ≥ 5` odd), the red second neighbourhood of `v` through `U`
has no red path on `L + 1` vertices. -/
theorem pathFree_second_nbhd {V : Type*} (G : SimpleGraph V) (L : ℕ) (hL : 5 ≤ L) (hodd : Odd L)
    (hC : (cycleGraph L).Free G) (v : V) (U : Set V) (hvU : v ∉ U) (hU : ∀ u ∈ U, G.Adj v u)
    (Γ : Set V) (hΓ : ∀ x ∈ Γ, x ≠ v ∧ x ∉ U ∧ ∃ u ∈ U, G.Adj u x) :
    (pathGraph (L + 1)).Free (G.induce Γ) := by
  rintro ⟨φ⟩
  let x : ℕ → V := fun i => (φ ⟨min i L, by omega⟩ : V)
  have hxΓ : ∀ i, x i ∈ Γ := fun i => (φ _).2
  have hex : ∀ i, ∃ w, w ∈ U ∧ G.Adj w (x i) := fun i => (hΓ _ (hxΓ i)).2.2
  choose u hu hux using hex
  refine core_E3 G L hL hodd x u v ?_ ?_ ?_ hux (fun j => hU _ (hu j))
    (fun i j h => (hΓ _ (hxΓ i)).2.1 (h ▸ hu j)) (fun i => (hΓ _ (hxΓ i)).1)
    (fun j h => hvU (h ▸ hu j))
  · intro l hlen hnd hc
    exact hC (hlen ▸ cyc_E3 G l (by omega) hnd hc)
  · intro i hi
    have hp : (pathGraph (L + 1)).Adj ⟨min i L, by omega⟩ ⟨min (i + 1) L, by omega⟩ := by
      rw [pathGraph_adj]; left; simp; omega
    exact φ.toHom.map_rel hp
  · intro i j hi hj h
    have := congrArg Fin.val (φ.injective (Subtype.ext h))
    simp at this; omega

end OMA569

namespace OMA569
open SimpleGraph

/-- Pure arithmetic: the U1 size condition. -/
theorem u1_arith (L n S : ℕ) (hL : 5 ≤ L) (h : (L - 1) * n ≤ 2 * S) (hn : 1 ≤ n) :
    (L - 1 - 1) * (n / 2 + 1 - 1) < S := by
  obtain ⟨l, rfl⟩ : ∃ l, L = l + 5 := ⟨L - 5, by omega⟩
  have e1 : l + 5 - 1 - 1 = l + 3 := by omega
  have e2 : l + 5 - 1 = l + 4 := by omega
  rw [e1, Nat.add_sub_cancel]
  rw [e2] at h
  have h2 := Nat.mul_le_mul_left (l + 3) (Nat.div_mul_le_self n 2)
  nlinarith

/-- Pure arithmetic: the final count is contradictory. -/
theorem count_contra (L n m c e : ℕ) (hL : 5 ≤ L) (hn : 4 ≤ n) (hc2 : 2 ≤ c) (hcn : c ≤ n)
    (he : 4 * e < m) (hD : 2 * n + c * (c - 3) ≤ 2 * m)
    (hcount : L * m + 1 ≤ 2 * n + (L - 1) * (c - 1) + L * e) : False := by
  obtain ⟨l, rfl⟩ : ∃ l, L = l + 5 := ⟨L - 5, by omega⟩
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
  have e1 : l + 5 - 1 = l + 4 := by omega
  rw [e1] at hcount
  have hLe : (l + 5) * (4 * e + 1) ≤ (l + 5) * m := Nat.mul_le_mul_left _ he
  by_cases hc3 : c ≤ 3
  · have h0 : c * (c - 3) = 0 := by simp [Nat.sub_eq_zero_of_le hc3]
    rw [h0] at hD
    have hc1 : c - 1 ≤ 2 := by omega
    have h1 := Nat.mul_le_mul_left (l + 4) hc1
    have h2 : (l + 5) * (k + 4) ≤ (l + 5) * m := Nat.mul_le_mul_left _ (by omega)
    nlinarith
  · push Not at hc3
    obtain ⟨d, rfl⟩ : ∃ d, c = d + 4 := ⟨c - 4, by omega⟩
    have e2 : d + 4 - 3 = d + 1 := by omega
    have e3 : d + 4 - 1 = d + 3 := by omega
    rw [e2] at hD
    rw [e3] at hcount
    obtain ⟨j, rfl⟩ : ∃ j, k = d + j := ⟨k - d, by omega⟩
    have h3 := Nat.mul_le_mul_left (l + 5) hD
    nlinarith [Nat.zero_le (l * j), Nat.zero_le (l * d), Nat.zero_le (l * d * d),
      Nat.zero_le (d * d)]

end OMA569

namespace OMA569
open SimpleGraph

/-- A blue copy inside an induced subgraph is a blue copy in the whole graph. -/
theorem lift_compl {V : Type*} (G : SimpleGraph V) (T : Set V) : (G.induce T)ᶜ ⊑ Gᶜ :=
  ⟨⟨⟨Subtype.val, fun {a b} h => by
    rw [compl_adj] at h ⊢
    exact ⟨fun e => h.1 (Subtype.ext e), h.2⟩⟩, Subtype.val_injective⟩⟩

/-- Tool B inside a Finset: a red-`P_j`-free set `S` contains a red-independent `t`-set. -/
theorem indep_in {V : Type*} [Fintype V] (G : SimpleGraph V) (S : Finset V) (j t : ℕ)
    (hj : 2 ≤ j) (hfree : (pathGraph j).Free (G.induce (S : Set V)))
    (hcard : (j - 1) * (t - 1) < S.card) :
    ∃ U ⊆ S, U.card = t ∧ ∀ x ∈ U, ∀ y ∈ U, ¬ G.Adj x y := by
  classical
  obtain ⟨s, hs, hind⟩ := indep_of_pathFree (G.induce (S : Set V)) j t hj hfree
    (by simpa using hcard)
  refine ⟨s.map (Function.Embedding.subtype _), ?_, by simp [hs], ?_⟩
  · intro x hx
    simp only [Finset.mem_map, Function.Embedding.coe_subtype] at hx
    obtain ⟨y, -, rfl⟩ := hx
    exact y.2
  · intro x hx y hy hxy
    simp only [Finset.mem_map, Function.Embedding.coe_subtype] at hx hy
    obtain ⟨x, hx, rfl⟩ := hx
    obtain ⟨y, hy, rfl⟩ := hy
    have hne : x ≠ y := fun e => G.ne_of_adj hxy (congrArg Subtype.val e)
    exact hind hx hy hne hxy

/-- Lemma C, contrapositive form inside a Finset `T`. -/
theorem card_lt_of_not_blue {V W : Type*} [Fintype V] [Fintype W] (G : SimpleGraph V)
    (H : SimpleGraph W) (T : Finset V) (k c : ℕ) (hk : 2 ≤ k) (hc : 1 ≤ c)
    (hcol : H.Colorable c) (hfree : (pathGraph k).Free (G.induce (T : Set V)))
    (hnb : ¬ H ⊑ Gᶜ) : T.card < Fintype.card W + (k - 2) * (c - 1) := by
  by_contra h
  push Not at h
  exact hnb ((blue_of_pathFree (G.induce (T : Set V)) H k c hk hc hcol hfree
    (by simpa using h)).trans (lift_compl G _))

/-- Gluing two injective pieces with disjoint images. -/
theorem injOn_ite_of_disjoint {α β : Type*} (p : α → Prop) [DecidablePred p] (s : Set α)
    (f g : α → β) (X Y : Set β) (hf : Set.InjOn f {x | x ∈ s ∧ p x})
    (hfX : ∀ x ∈ s, p x → f x ∈ X) (hg : Set.InjOn g {x | x ∈ s ∧ ¬ p x})
    (hgY : ∀ x ∈ s, ¬ p x → g x ∈ Y) (hXY : Disjoint X Y) :
    Set.InjOn (fun x => if p x then f x else g x) s := by
  intro x hx y hy hxy
  simp only at hxy
  by_cases hpx : p x <;> by_cases hpy : p y
  · rw [if_pos hpx, if_pos hpy] at hxy
    exact hf ⟨hx, hpx⟩ ⟨hy, hpy⟩ hxy
  · rw [if_pos hpx, if_neg hpy] at hxy
    exact absurd (hxy ▸ hfX x hx hpx) (Set.disjoint_left.mp hXY.symm (hgY y hy hpy))
  · rw [if_neg hpx, if_pos hpy] at hxy
    exact absurd (hxy ▸ hgY x hx hpx) (Set.disjoint_left.mp hXY (hfX y hy hpy))
  · rw [if_neg hpx, if_neg hpy] at hxy
    exact hg ⟨hx, hpx⟩ ⟨hy, hpy⟩ hxy

/-- Step 4 gluing: `A = Bᶜ` goes into the red-independent set `U1`, `B` goes into `U2`
(all `U1`–`U2` pairs blue), using a blue copy of `H[B']` in `U2`, where `B'` carries
every edge inside `B`. -/
theorem glue_blue {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W] (G : SimpleGraph V)
    (H : SimpleGraph W) (B B' : Finset W) (U1 U2 : Finset V) (hB'B : B' ⊆ B)
    (hB' : ∀ x ∈ B, ∀ y ∈ B, H.Adj x y → x ∈ B')
    (hA : (Finset.univ \ B).card ≤ U1.card) (hU2 : B.card ≤ U2.card)
    (hU1 : ∀ x ∈ U1, ∀ y ∈ U1, ¬ G.Adj x y) (hcross : ∀ x ∈ U1, ∀ y ∈ U2, ¬ G.Adj x y)
    (hdisj : Disjoint U1 U2)
    (hcopy : (H.induce (B' : Set W)) ⊑ (G.induce (U2 : Set V))ᶜ) : H ⊑ Gᶜ := by
  classical
  rcases isEmpty_or_nonempty V with hV | hV
  · have h1 : U1.card = 0 := by
      have := Finset.card_le_univ U1; rw [Fintype.card_eq_zero] at this; omega
    have h2 : U2.card = 0 := by
      have := Finset.card_le_univ U2; rw [Fintype.card_eq_zero] at this; omega
    have hW : IsEmpty W := by
      rw [← Fintype.card_eq_zero_iff]
      rw [Finset.card_univ_sdiff] at hA
      omega
    exact ⟨⟨⟨fun w => isEmptyElim w, fun {a} => isEmptyElim a⟩, fun a => isEmptyElim a⟩⟩
  obtain ⟨φ⟩ := hcopy
  let φ' : W → V := fun w => if h : w ∈ B' then (φ ⟨w, Finset.mem_coe.2 h⟩ : V)
    else Classical.arbitrary V
  have hφ'eq : ∀ w (h : w ∈ B'), φ' w = (φ ⟨w, Finset.mem_coe.2 h⟩ : V) := by
    intro w h; simp only [φ', dif_pos h]
  have hφ'U2 : ∀ w ∈ B', φ' w ∈ U2 := by
    intro w h; rw [hφ'eq w h]; exact Finset.mem_coe.1 (φ ⟨w, Finset.mem_coe.2 h⟩).2
  have hφ'inj : Set.InjOn φ' (B' : Set W) := by
    intro x hx y hy hxy
    rw [hφ'eq x hx, hφ'eq y hy] at hxy
    have := φ.injective (Subtype.ext hxy)
    simpa using this
  have hφ'adj : ∀ x ∈ B', ∀ y ∈ B', H.Adj x y → ¬ G.Adj (φ' x) (φ' y) := by
    intro x hx y hy hxy
    rw [hφ'eq x hx, hφ'eq y hy]
    have := φ.toHom.map_rel (show (H.induce (B' : Set W)).Adj ⟨x, Finset.mem_coe.2 hx⟩
      ⟨y, Finset.mem_coe.2 hy⟩ from hxy)
    rw [compl_adj] at this
    exact this.2
  set Im := B'.image φ' with hIm
  have hImc : Im.card = B'.card := Finset.card_image_of_injOn hφ'inj
  have hImU2 : Im ⊆ U2 := by
    intro y hy
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 hy
    exact hφ'U2 w hw
  obtain ⟨gI, hgI, hgIinj⟩ := Set.Finite.exists_injOn_of_encard_le
    (s := ((B \ B' : Finset W) : Set W)) (t := ((U2 \ Im : Finset V) : Set V))
    (Finset.finite_toSet _) (by
      rw [Set.encard_coe_eq_coe_finsetCard, Set.encard_coe_eq_coe_finsetCard]
      norm_cast
      rw [Finset.card_sdiff_of_subset hB'B, Finset.card_sdiff_of_subset hImU2, hImc]
      omega)
  obtain ⟨gA, hgA, hgAinj⟩ := Set.Finite.exists_injOn_of_encard_le
    (s := ((Finset.univ \ B : Finset W) : Set W)) (t := (U1 : Set V))
    (Finset.finite_toSet _) (by
      rw [Set.encard_coe_eq_coe_finsetCard, Set.encard_coe_eq_coe_finsetCard]
      exact_mod_cast hA)
  let fB : W → V := fun w => if w ∈ B' then φ' w else gI w
  let f : W → V := fun w => if w ∈ B then fB w else gA w
  have hfB_U2 : ∀ w ∈ B, fB w ∈ U2 := by
    intro w hw
    simp only [fB]
    split_ifs with h
    · exact hφ'U2 w h
    · have := hgI (show w ∈ ((B \ B' : Finset W) : Set W) by simp [hw, h])
      exact (Finset.mem_sdiff.1 (Finset.mem_coe.1 this)).1
  have hfBinj : Set.InjOn fB (B : Set W) := by
    refine injOn_ite_of_disjoint (· ∈ B') (B : Set W) φ' gI (Im : Set V)
      ((U2 \ Im : Finset V) : Set V) ?_ ?_ ?_ ?_ ?_
    · intro x hx y hy hxy
      exact hφ'inj (Finset.mem_coe.2 hx.2) (Finset.mem_coe.2 hy.2) hxy
    · intro x _ hx
      exact Finset.mem_coe.2 (Finset.mem_image_of_mem _ hx)
    · intro x hx y hy hxy
      exact hgIinj (show x ∈ ((B \ B' : Finset W) : Set W) by simp [Finset.mem_coe.1 hx.1, hx.2])
        (show y ∈ ((B \ B' : Finset W) : Set W) by simp [Finset.mem_coe.1 hy.1, hy.2]) hxy
    · intro x hx hx'
      exact hgI (show x ∈ ((B \ B' : Finset W) : Set W) by simp [Finset.mem_coe.1 hx, hx'])
    · rw [Finset.disjoint_coe]
      exact Finset.disjoint_sdiff
  have hfinj : Function.Injective f := by
    have := injOn_ite_of_disjoint (· ∈ B) Set.univ fB gA (U2 : Set V) (U1 : Set V)
      (fun x hx y hy hxy => hfBinj (Finset.mem_coe.2 hx.2) (Finset.mem_coe.2 hy.2) hxy)
      (fun x _ hx => Finset.mem_coe.2 (hfB_U2 x hx))
      (fun x hx y hy hxy => hgAinj (show x ∈ ((Finset.univ \ B : Finset W) : Set W) by
          simp [hx.2]) (show y ∈ ((Finset.univ \ B : Finset W) : Set W) by simp [hy.2]) hxy)
      (fun x _ hx => hgA (show x ∈ ((Finset.univ \ B : Finset W) : Set W) by simp [hx]))
      (by rw [Finset.disjoint_coe]; exact hdisj.symm)
    exact fun x y hxy => this (Set.mem_univ x) (Set.mem_univ y) hxy
  have hfB : ∀ w ∈ B, f w ∈ U2 := fun w hw => by
    simp only [f, if_pos hw]; exact hfB_U2 w hw
  have hfA : ∀ w ∉ B, f w ∈ U1 := fun w hw => by
    simp only [f, if_neg hw]
    exact Finset.mem_coe.1 (hgA (show w ∈ ((Finset.univ \ B : Finset W) : Set W) by simp [hw]))
  refine ⟨⟨⟨f, fun {x y} hxy => (compl_adj G (f x) (f y)).mpr
    ⟨fun e => H.ne_of_adj hxy (hfinj e), ?_⟩⟩, hfinj⟩⟩
  by_cases hx : x ∈ B <;> by_cases hy : y ∈ B
  · have hx' := hB' x hx y hy hxy
    have hy' := hB' y hy x hx hxy.symm
    have ex : f x = φ' x := by simp only [f, fB, if_pos hx, if_pos hx']
    have ey : f y = φ' y := by simp only [f, fB, if_pos hy, if_pos hy']
    rw [ex, ey]
    exact hφ'adj x hx' y hy' hxy
  · exact fun h => hcross _ (hfA y hy) _ (hfB x hx) h.symm
  · exact hcross _ (hfA x hx) _ (hfB y hy)
  · exact hU1 _ (hfA x hx) _ (hfA y hy)

end OMA569

namespace OMA569
open SimpleGraph

/-- M2b: the dense case `L ≥ 5`, `δ(H) ≥ 2`, `n ≥ 4` (paper's U1 / Γ / U2 count). -/
theorem close_dense {V W : Type} [Fintype V] [Fintype W] (G : SimpleGraph V) (H : SimpleGraph W)
    [DecidableRel H.Adj] (L : ℕ) (hL : 5 ≤ L) (hodd : Odd L)
    (hIH : ∀ (W' : Type) [Fintype W'] (H' : SimpleGraph W'), NoIso H' →
      H'.edgeSet.ncard < H.edgeSet.ncard → Good L H')
    (hC : (cycleGraph L).Free G) (hδ : ∀ w, 2 ≤ H.degree w) (hn : 4 ≤ Fintype.card W)
    (hV : L * H.edgeSet.ncard ≤ Fintype.card V) (v : V) (S : Finset V) (hvS : v ∉ S)
    (hS : ∀ x ∈ S, G.Adj v x) (hSc : (L - 1) * Fintype.card W ≤ 2 * S.card) :
    H.IsContained Gᶜ := by
  classical
  by_contra hblue
  have hmn : H.edgeSet.ncard = H.edgeFinset.card := by
    rw [← coe_edgeFinset, Set.ncard_coe_finset]
  -- chromatic number
  have hex : ∃ c, H.Colorable c := ⟨_, H.colorable_of_fintype⟩
  set c := Nat.find hex with hc_def
  have hcol : H.Colorable c := Nat.find_spec hex
  have hcn : c ≤ Fintype.card W := Nat.find_min' hex H.colorable_of_fintype
  obtain ⟨w0⟩ : Nonempty W := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨w1, hw01⟩ : ∃ w1, H.Adj w0 w1 :=
    (degree_pos_iff_exists_adj H w0).mp (by have := hδ w0; omega)
  have hc2 : 2 ≤ c := by
    by_contra h
    obtain ⟨C⟩ := hcol.mono (show c ≤ 1 by omega)
    exact C.valid hw01 (Subsingleton.elim _ _)
  have hnc : ¬ H.Colorable (c - 1) := Nat.find_min hex (by omega)
  have hD := edges_ge_of_chromatic H c hδ hnc
  -- U1
  have hPfree : (pathGraph (L - 1)).Free (G.induce (S : Set V)) := fun h =>
    hC (cycle_of_path_nbhd G L (by omega) v (S : Set V) (by simpa using hvS)
      (fun x hx => hS x hx) h)
  obtain ⟨U1, hU1S, hU1c, hU1i⟩ := indep_in G S (L - 1) (Fintype.card W / 2 + 1) (by omega)
    hPfree (u1_arith L _ _ hL hSc (by omega))
  have hvU1 : v ∉ U1 := fun h => hvS (hU1S h)
  -- Γ
  set Γ := Finset.univ.filter (fun x => x ≠ v ∧ x ∉ U1 ∧ ∃ u ∈ U1, G.Adj u x) with hΓ_def
  have hΓfree := pathFree_second_nbhd G L hL hodd hC v (U1 : Set V) (by simpa using hvU1)
    (fun u hu => hS u (hU1S hu)) (Γ : Set V) (by
      intro x hx
      simp only [Γ, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hx
      simpa using hx)
  have hΓ := card_lt_of_not_blue G H Γ (L + 1) c (by omega) (by omega) hcol hΓfree hblue
  rw [show L + 1 - 2 = L - 1 by omega] at hΓ
  -- B, B', H2
  have hm1 : 1 ≤ H.edgeFinset.card := by
    have := Nat.zero_le (c * (c - 3)); omega
  obtain ⟨B, hBc, hBe⟩ := exists_sparse_part H (by omega) hm1
  set B' := B.filter (fun x => ∃ y ∈ B, H.Adj x y) with hB'_def
  have hB'B : B' ⊆ B := Finset.filter_subset _ _
  have hNo : NoIso (H.induce (B' : Set W)) := by
    rintro ⟨x, hx⟩
    have hx' := Finset.mem_coe.1 hx
    rw [hB'_def, Finset.mem_filter] at hx'
    obtain ⟨hxB, y, hyB, hxy⟩ := hx'
    refine ⟨⟨y, Finset.mem_coe.2 ?_⟩, hxy⟩
    rw [hB'_def, Finset.mem_filter]
    exact ⟨hyB, x, hxB, hxy.symm⟩
  have he2 : (H.induce (B' : Set W)).edgeSet.ncard ≤ (H.induce (B : Set W)).edgeFinset.card := by
    let ψ : (H.induce (B' : Set W)).Copy (H.induce (B : Set W)) :=
      ⟨⟨fun x => ⟨x.1, Finset.mem_coe.2 (hB'B (Finset.mem_coe.1 x.2))⟩, fun h => h⟩,
        fun a b h => Subtype.ext (congrArg Subtype.val h :)⟩
    calc (H.induce (B' : Set W)).edgeSet.ncard
        = Nat.card (H.induce (B' : Set W)).edgeSet := (Nat.card_coe_set_eq _).symm
      _ ≤ Nat.card (H.induce (B : Set W)).edgeSet :=
          Nat.card_le_card_of_injective _ ψ.mapEdgeSet.injective
      _ = _ := by rw [Nat.card_coe_set_eq, ← coe_edgeFinset, Set.ncard_coe_finset]
  have hlt : (H.induce (B' : Set W)).edgeSet.ncard < H.edgeSet.ncard := by omega
  have hGood := hIH _ (H.induce (B' : Set W)) hNo hlt
  -- U2
  set U2 := Finset.univ.filter (fun y => y ≠ v ∧ y ∉ U1 ∧ y ∉ Γ) with hU2_def
  have hcross : ∀ x ∈ U1, ∀ y ∈ U2, ¬ G.Adj x y := by
    intro x hx y hy hxy
    rw [hU2_def, Finset.mem_filter] at hy
    apply hy.2.2.2
    rw [hΓ_def, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hy.2.1, hy.2.2.1, x, hx, hxy⟩
  have hdisj : Disjoint U1 U2 := by
    rw [Finset.disjoint_left]
    intro x hx hx2
    rw [hU2_def, Finset.mem_filter] at hx2
    exact hx2.2.2.1 hx
  have hU2 : U2.card + 1 ≤ L * (H.induce (B' : Set W)).edgeSet.ncard + B.card := by
    by_contra h
    push Not at h
    rcases hGood (U2 : Set V) (G.induce (U2 : Set V)) (by simp; omega) with hcy | hcp
    · exact hC (hcy.trans ⟨Copy.induce G _⟩)
    · apply hblue
      refine glue_blue G H B B' U1 U2 hB'B ?_ ?_ (by omega) hU1i hcross hdisj hcp
      · intro x hx y hy hxy
        rw [hB'_def, Finset.mem_filter]
        exact ⟨hx, y, hy, hxy⟩
      · rw [Finset.card_univ_sdiff, hBc, hU1c]
        omega
  -- count
  have hcover : Fintype.card V ≤ 1 + U1.card + Γ.card + U2.card := by
    have hsub : (Finset.univ : Finset V) ⊆ insert v (U1 ∪ Γ ∪ U2) := by
      intro y _
      by_cases h1 : y = v
      · simp [h1]
      by_cases h2 : y ∈ U1
      · simp [h2]
      by_cases h3 : y ∈ Γ
      · simp [h3]
      have : y ∈ U2 := by
        rw [hU2_def, Finset.mem_filter]
        exact ⟨Finset.mem_univ _, h1, h2, h3⟩
      simp [this]
    have := Finset.card_le_card hsub
    have := Finset.card_insert_le v (U1 ∪ Γ ∪ U2)
    have := Finset.card_union_le (U1 ∪ Γ) U2
    have := Finset.card_union_le U1 Γ
    rw [Finset.card_univ] at *
    omega
  have h4 : 4 * (H.induce (B' : Set W)).edgeSet.ncard < H.edgeFinset.card := by omega
  refine count_contra L (Fintype.card W) H.edgeFinset.card c
    (H.induce (B' : Set W)).edgeSet.ncard hL hn hc2 hcn h4 hD ?_
  rw [hmn] at hV
  omega

end OMA569

namespace OMA569
open SimpleGraph

/-- A red-independent set of at least `|W|` vertices carries a blue copy of any `H` on `W`. -/
theorem blue_of_indep {V W : Type*} [Fintype W] (G : SimpleGraph V) (H : SimpleGraph W)
    (U : Finset V) (hU : Fintype.card W ≤ U.card) (hind : ∀ x ∈ U, ∀ y ∈ U, ¬ G.Adj x y) :
    H ⊑ Gᶜ := by
  obtain ⟨f⟩ := Function.Embedding.nonempty_of_card_le
    (show Fintype.card W ≤ Fintype.card U by simpa using hU)
  refine ⟨⟨⟨fun w => (f w).1, fun {a b} hab => ?_⟩, ?_⟩⟩
  · rw [compl_adj]
    exact ⟨fun e => hab.ne (f.injective (Subtype.ext e)), hind _ (f a).2 _ (f b).2⟩
  · exact fun a b e => f.injective (Subtype.ext e)

/-- Every graph on three vertices sits in a triangle. -/
theorem le_triangle {W : Type*} [Fintype W] (H : SimpleGraph W) (hn : Fintype.card W = 3) :
    H ⊑ completeGraph (Fin 3) := by
  let e := Fintype.equivFinOfCardEq hn
  exact ⟨⟨⟨e, fun {a b} hab => by simpa using e.injective.ne hab.ne⟩, e.injective⟩⟩

/-- M2c: the connected case. -/
theorem good_of_connected (L : ℕ) (hL : 3 ≤ L) (hodd : Odd L) {W : Type} [Fintype W]
    (H : SimpleGraph W) (hH : NoIso H) (hc : H.Connected)
    (hIH : ∀ (W' : Type) [Fintype W'] (H' : SimpleGraph W'), NoIso H' →
      H'.edgeSet.ncard < H.edgeSet.ncard → Good L H') : Good L H := by
  classical
  intro V _ G hV
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hC, hB⟩ := hcon
  have hmn : H.edgeSet.ncard = H.edgeFinset.card := by
    rw [← coe_edgeFinset, Set.ncard_coe_finset]
  have hW2 : Fintype.card W ≤ 2 * H.edgeSet.ncard := card_le_two_mul_edges H hH
  have : Nonempty W := hc.nonempty
  obtain ⟨u, hu⟩ := H.exists_minimal_degree_vertex
  have hmin : ∀ w, H.degree u ≤ H.degree w := fun w => hu ▸ H.minDegree_le_degree w
  obtain ⟨u', huu'⟩ := hH u
  have hn2 : 2 ≤ Fintype.card W := by
    have : 1 < Fintype.card W := Fintype.one_lt_card_iff.mpr ⟨u, u', huu'.ne⟩
    omega
  have hm1 : 1 ≤ H.edgeSet.ncard := ncard_edgeSet_pos H u u' huu'
  -- the case of a single edge
  by_cases hm : H.edgeSet.ncard = 1
  · by_cases hall : ∃ x y : V, x ≠ y ∧ ¬ G.Adj x y
    · obtain ⟨x, y, hxy, hG⟩ := hall
      apply hB
      refine blue_of_indep G H {x, y} ?_ ?_
      · rw [Finset.card_pair hxy]; omega
      · intro a ha b hb hab
        simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
        rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
        · exact G.irrefl hab
        · exact hG hab
        · exact hG hab.symm
        · exact G.irrefl hab
    · push Not at hall
      have hVL : L ≤ Fintype.card V := by rw [hm] at hV; omega
      have hne : Nonempty V := Fintype.card_pos_iff.mp (by omega)
      obtain ⟨v⟩ := hne
      apply hC
      refine cycle_of_path_nbhd G L hL v ((Finset.univ.erase v : Finset V) : Set V)
        (by simp) (fun x hx => hall v x (by simp at hx; exact Ne.symm hx)) ?_
      apply pathGraph_of_clique
      · simp
        omega
      · intro a b hab
        exact hall a b (fun e => hab (Subtype.ext e))
  have hm2 : 2 ≤ H.edgeSet.ncard := by omega
  set d := H.degree u with hd
  have hd1 : 1 ≤ d := (H.degree_pos_iff_exists_adj u).mpr ⟨u', huu'⟩
  -- handshake
  have hhs : d * Fintype.card W ≤ 2 * H.edgeSet.ncard := by
    rw [hmn, ← sum_degrees_eq_twice_card_edges]
    calc d * Fintype.card W = ∑ _w : W, d := by simp [mul_comm]
      _ ≤ ∑ w, H.degree w := Finset.sum_le_sum fun w _ => hmin w
  -- `H - u` has no isolated vertices
  have hnoiso : NoIso (H.induce ({u}ᶜ : Set W)) := by
    rintro ⟨w, hw⟩
    by_contra hno
    push Not at hno
    have hwu : w ≠ u := hw
    have honly : ∀ x, H.Adj w x → x = u := by
      intro x hx
      by_contra hxu
      exact hno ⟨x, hxu⟩ hx
    obtain ⟨w1, hw1⟩ := hH w
    have hwu' : H.Adj w u := honly w1 hw1 ▸ hw1
    have hdegw : H.degree w ≤ 1 := by
      rw [← card_neighborFinset_eq_degree]
      calc (H.neighborFinset w).card ≤ ({u} : Finset W).card :=
            Finset.card_le_card fun x hx => by simpa using honly x (by simpa using hx)
        _ = 1 := by simp
    have huonly : ∀ x, H.Adj u x → x = w := by
      intro x hx
      by_contra hxw
      have h2 : ({w, x} : Finset W) ⊆ H.neighborFinset u := by
        intro y hy
        simp only [Finset.mem_insert, Finset.mem_singleton] at hy
        rcases hy with rfl | rfl
        · simpa using hwu'.symm
        · simpa using hx
      have := Finset.card_le_card h2
      rw [Finset.card_pair (Ne.symm hxw), card_neighborFinset_eq_degree] at this
      have := hmin w
      omega
    have hall : ∀ x, x = u ∨ x = w := by
      intro x
      by_contra hx
      push Not at hx
      obtain ⟨p⟩ := hc.preconnected u x
      obtain ⟨dt, -, h1, h2⟩ := p.exists_boundary_dart ({u, w} : Set W) (by simp)
        (by simp [hx.1, hx.2])
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h1 h2
      push Not at h2
      rcases h1 with h1 | h1
      · exact h2.2 (huonly _ (h1 ▸ dt.adj))
      · exact h2.1 (honly _ (h1 ▸ dt.adj))
    have hsub : H.edgeSet ⊆ {s(u, w)} := by
      intro e he
      induction e using Sym2.ind with
      | h a b =>
      have hab : H.Adj a b := he
      rcases hall a with rfl | rfl <;> rcases hall b with rfl | rfl
      · exact absurd hab H.irrefl
      · rfl
      · exact Set.mem_singleton_iff.mpr Sym2.eq_swap
      · exact absurd hab H.irrefl
    have := Set.ncard_le_ncard hsub
    rw [Set.ncard_singleton] at this
    omega
  -- `H - u` has fewer edges
  have hlt : (H.induce ({u}ᶜ : Set W)).edgeSet.ncard < H.edgeSet.ncard := by
    have h1 := card_edgeFinset_induce_compl_singleton H u
    have h2 := card_edgeFinset_deleteIncidenceSet H u
    rw [← coe_edgeFinset, Set.ncard_coe_finset]
    convert (show H.edgeFinset.card - d < H.edgeSet.ncard by omega) using 1
    rw [h1, h2]
  have hF : (H.induce ({u}ᶜ : Set W)).IsContained Gᶜ := by
    rcases hIH _ _ hnoiso hlt V G (le_trans (Nat.mul_le_mul_left L hlt.le) hV) with h | h
    · exact absurd h hC
    · exact h
  have hWV : Fintype.card W ≤ Fintype.card V := by nlinarith
  rcases extend_or_star G H u hF hWV with h | ⟨v, S, hvS, hS, hcount⟩
  · exact hB h
  have hfreeS : (pathGraph (L - 1)).Free (G.induce (S : Set V)) := fun hP =>
    hC (cycle_of_path_nbhd G L hL v (S : Set V) (by simpa using hvS) (fun x hx => hS x hx) hP)
  have key : ¬ (L - 2) * (Fintype.card W - 1) < S.card := by
    intro hlt'
    obtain ⟨U, -, hU, hind⟩ := indep_in G S (L - 1) (Fintype.card W) (by omega) hfreeS
      (by rw [show L - 1 - 1 = L - 2 by omega]; exact hlt')
    exact hB (blue_of_indep G H U hU.ge hind)
  apply key
  set n := Fintype.card W with hn
  set m := H.edgeSet.ncard with hmdef
  set s := S.card with hs
  rw [← hd] at hcount
  by_cases hd1' : d = 1
  · -- tree-like bound `n ≤ m + 1`
    have htree : n ≤ m + 1 := by
      have := hc.card_vert_le_card_edgeSet_add_one
      rw [Nat.card_eq_fintype_card, Nat.card_coe_set_eq] at this
      exact this
    rw [hd1', one_mul] at hcount
    obtain ⟨l, rfl⟩ : ∃ l, L = l + 3 := ⟨L - 3, by omega⟩
    obtain ⟨n', hn'⟩ : ∃ n', n = n' + 2 := ⟨n - 2, by omega⟩
    rw [hn'] at htree hcount ⊢
    rw [show l + 3 - 2 = l + 1 by omega, show n' + 2 - 1 = n' + 1 by omega]
    nlinarith
  have hd2 : 2 ≤ d := by omega
  have hδ : ∀ w, 2 ≤ H.degree w := fun w => le_trans hd2 (hmin w)
  by_cases hL3 : L = 3
  · subst hL3
    rw [show 3 - 2 = 1 by omega, one_mul]
    by_contra hns
    push Not at hns
    have h1 : d * s ≤ d * (n - 1) := Nat.mul_le_mul_left d (by omega)
    have h2 : d * (n - 1) + d = d * n := by
      rw [← Nat.mul_succ]; congr 1; omega
    nlinarith
  have hL5 : 5 ≤ L := by obtain ⟨j, hj⟩ := hodd; omega
  exfalso
  by_cases hn3 : n = 3
  · have hm3 : 3 ≤ m := by nlinarith
    rcases cycle_or_blue_triangle G L hL5 (by nlinarith) with h | h
    · exact hC h
    · exact hB ((le_triangle H hn3).trans h)
  have hdn : d < n := H.degree_lt_card_verts u
  have hn4 : 4 ≤ n := by omega
  have hSc : (L - 1) * n ≤ 2 * s := by
    by_contra hns
    push Not at hns
    have h1 : d * (2 * s) + d ≤ d * ((L - 1) * n) := by
      rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left d hns
    have h3 : (L - 1) * n + n = L * n := by
      rw [← Nat.succ_mul]; congr 1; omega
    nlinarith
  exact hB (close_dense G H L hL5 hodd hIH hC hδ hn4 hV v S hvS hS hSc)

/-- Theorem T. -/
theorem good_of_noIso (L : ℕ) (hL : 3 ≤ L) (hodd : Odd L) :
    ∀ (W : Type) [Fintype W] (H : SimpleGraph W), NoIso H → Good L H := by
  suffices h : ∀ k (W : Type) [Fintype W] (H : SimpleGraph W), H.edgeSet.ncard = k →
      NoIso H → Good L H from fun W _ H hH => h _ W H rfl hH
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro W _ H hk hH
  have hIH : ∀ (W' : Type) [Fintype W'] (H' : SimpleGraph W'), NoIso H' →
      H'.edgeSet.ncard < H.edgeSet.ncard → Good L H' :=
    fun W' _ H' h1 h2 => ih _ (hk ▸ h2) W' H' rfl h1
  by_cases hc : H.Connected
  · exact good_of_connected L hL hodd H hH hc hIH
  · exact good_of_not_connected L hL H hH hc hIH

end OMA569

noncomputable def OMA.answer : ℕ → ℝ := fun k => 2 * (k : ℝ) + 1

theorem OMA.solution : Erdos569.erdos_569.answer = OMA.answer → type_of% @Erdos569.erdos_569 := by
  intro h
  rw [h]
  intro k hk
  have hL : 3 ≤ 2 * k + 1 := by omega
  have hodd : Odd (2 * k + 1) := odd_two_mul_add_one k
  have hcast : ((2 * k + 1 : ℕ) : ℝ) = OMA.answer k := by simp [OMA.answer]
  rw [← hcast]
  apply IsLeast.csInf_eq
  constructor
  · refine ⟨by positivity, fun m W _ H _ hdeg hm => ?_⟩
    have hH : OMA569.NoIso H := fun v => (H.degree_pos_iff_exists_adj v).mp (hdeg v)
    have hgood := OMA569.good_of_noIso (2 * k + 1) hL hodd W H hH
    have hR : SimpleGraph.graphRamsey (SimpleGraph.cycleGraph (2 * k + 1)) H ≤
        (2 * k + 1) * m := by
      apply Nat.sInf_le
      intro C
      exact hgood (Fin ((2 * k + 1) * m)) C (by simp [hm])
    exact_mod_cast hR
  · rintro C ⟨-, hC⟩
    have h1 := hC 1 (Fin 2) (SimpleGraph.completeGraph (Fin 2))
      (fun v => (SimpleGraph.degree_pos_iff_exists_adj _ v).mpr
        ⟨v + 1, by fin_cases v <;> decide⟩)
      (by
        rw [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset,
          SimpleGraph.card_edgeFinset_top_eq_card_choose_two]
        simp)
    have h2 := OMA569.le_graphRamsey_K2 (2 * k + 1) hL
    have h3 : ((2 * k + 1 : ℕ) : ℝ) ≤
        (SimpleGraph.graphRamsey (SimpleGraph.cycleGraph (2 * k + 1))
          (SimpleGraph.completeGraph (Fin 2)) : ℝ) := by exact_mod_cast h2
    simpa using h3.trans h1
