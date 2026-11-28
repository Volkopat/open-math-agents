import OMAStatements.S_oeis_a239455
import Mathlib

-- OEIS A239455, conjecture of Gus Wiseman (2025): a partition is Look-and-Say if and only if
-- its parts can be listed so that all run-lengths are distinct.
--
-- Both properties are about writing the multiset y of parts as a union of blocks
--   (v copies of the value f v),  v ranging over a finite set D of positive integers.
-- Look-and-Say: such (D, f) exists (D = distinct parts of p, f = multiplicity in p).
-- Distinct run-lengths: such (D, f) exists together with an ordering of D in which
--   consecutive blocks have different values (the blocks are then exactly the runs).
-- Proof of the nontrivial direction: take (D, f) with |D| minimal. If the blocks of some value x
-- were more than half of all blocks plus one half, then for the longest such block M and every
-- other block a of value x the number a + M would have to be the length of a block of another
-- value (otherwise merge a and M), which gives too many other blocks. So no value has more than
-- (|D| + 1) / 2 blocks, and then a greedy choice orders the blocks without equal neighbours.

/-- y is the union of the blocks: v copies of f v, for v in D. -/
def a239455_Rep (y : Multiset ℕ) (D : Finset ℕ) (f : ℕ → ℕ) : Prop :=
  (∀ v ∈ D, 0 < v) ∧ ∑ v ∈ D, Multiset.replicate v (f v) = y

theorem a239455_coe_flatten : ∀ B : List (List ℕ),
    Multiset.ofList B.flatten = (B.map Multiset.ofList).sum
  | [] => by simp
  | b :: T => by
      rw [List.flatten_cons, ← Multiset.coe_add, a239455_coe_flatten T, List.map_cons,
        List.sum_cons]

/-- Ordering blocks so that neighbours have different values, when no value is too frequent. -/
theorem a239455_arr : ∀ (k : ℕ) (D : Finset ℕ) (f : ℕ → ℕ) (c : ℕ), D.card = k →
    (∀ x, 2 * (D.filter (fun v => f v = x)).card ≤ k + 1) →
    2 * (D.filter (fun v => f v = c)).card ≤ k →
    ∃ L : List ℕ, L.Nodup ∧ L.toFinset = D ∧ (c :: L.map f).IsChain (· ≠ ·)
  | 0, D, f, c, hk, _, _ => by
      refine ⟨[], List.nodup_nil, ?_, by simp⟩
      rw [Finset.card_eq_zero.mp hk]
      rfl
  | k + 1, D, f, c, hk, hall, hc => by
      classical
      have hne : (D.filter (fun v => f v ≠ c)).Nonempty := by
        by_contra hempty
        rw [Finset.not_nonempty_iff_eq_empty, Finset.filter_eq_empty_iff] at hempty
        have hD : D.filter (fun v => f v = c) = D :=
          Finset.filter_true_of_mem (fun v hv => by simpa using hempty hv)
        rw [hD, hk] at hc
        omega
      obtain ⟨e, he, hmax⟩ := Finset.exists_max_image _
        (fun v => (D.filter (fun w => f w = f v)).card) hne
      rw [Finset.mem_filter] at he
      obtain ⟨heD, hec⟩ := he
      have hcard : (D.erase e).card = k := by
        rw [Finset.card_erase_of_mem heD, hk]
        rfl
      have hcls : ∀ x, ((D.erase e).filter (fun v => f v = x)).card =
          (D.filter (fun v => f v = x)).card - (if f e = x then 1 else 0) := by
        intro x
        rw [Finset.filter_erase]
        split_ifs with h
        · rw [Finset.card_erase_of_mem (Finset.mem_filter.mpr ⟨heD, h⟩)]
        · rw [Finset.erase_eq_of_notMem (by simp [h]), Nat.sub_zero]
      have hdisj : ∀ x x', x ≠ x' →
          (D.filter (fun v => f v = x)).card + (D.filter (fun v => f v = x')).card ≤ k + 1 := by
        intro x x' hxx
        rw [← hk, ← Finset.card_union_of_disjoint]
        · exact Finset.card_le_card
            (Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _))
        · rw [Finset.disjoint_filter]
          intro v _ h1 h2
          exact hxx (h1.symm.trans h2)
      have hA : ∀ x, 2 * ((D.erase e).filter (fun v => f v = x)).card ≤ k + 1 := by
        intro x
        rw [hcls x]
        by_cases hx : f e = x
        · rw [if_pos hx]
          have h1 := hall x
          omega
        · rw [if_neg hx, Nat.sub_zero]
          by_cases hxc : x = c
          · rw [hxc]
            omega
          · by_cases hx0 : (D.filter (fun v => f v = x)).card = 0
            · omega
            · obtain ⟨v, hv⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hx0)
              rw [Finset.mem_filter] at hv
              have h1 := hmax v (Finset.mem_filter.mpr ⟨hv.1, by rw [hv.2]; exact hxc⟩)
              simp only [hv.2] at h1
              have h2 := hdisj (f e) x hx
              omega
      have hB : 2 * ((D.erase e).filter (fun v => f v = f e)).card ≤ k := by
        rw [hcls (f e), if_pos rfl]
        have h1 := hall (f e)
        omega
      obtain ⟨L, hL1, hL2, hL3⟩ := a239455_arr k (D.erase e) f (f e) hcard hA hB
      refine ⟨e :: L, ?_, ?_, ?_⟩
      · rw [List.nodup_cons]
        refine ⟨?_, hL1⟩
        intro hmem
        have h1 : e ∈ L.toFinset := List.mem_toFinset.mpr hmem
        rw [hL2] at h1
        exact (Finset.notMem_erase e D) h1
      · rw [List.toFinset_cons, hL2, Finset.insert_erase heD]
      · rw [List.map_cons, List.isChain_cons_cons]
        exact ⟨fun h => hec h.symm, hL3⟩

/-- Two blocks of the same value can be merged when the new length is free. -/
theorem a239455_merge (y : Multiset ℕ) (D : Finset ℕ) (f : ℕ → ℕ) (hR : a239455_Rep y D f)
    (a M x : ℕ) (ha : a ∈ D) (hM : M ∈ D) (haM : a ≠ M) (hfa : f a = x) (hfM : f M = x)
    (hnew : a + M ∉ D) :
    ∃ (D' : Finset ℕ) (f' : ℕ → ℕ), a239455_Rep y D' f' ∧ D'.card + 1 = D.card := by
  classical
  have hnot : a + M ∉ (D.erase a).erase M :=
    fun h => hnew (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase h))
  have hM' : M ∈ D.erase a := Finset.mem_erase.mpr ⟨fun h => haM h.symm, hM⟩
  refine ⟨insert (a + M) ((D.erase a).erase M), Function.update f (a + M) x, ⟨?_, ?_⟩, ?_⟩
  · intro v hv
    rcases Finset.mem_insert.mp hv with rfl | hv
    · have h1 := hR.1 a ha
      omega
    · exact hR.1 v (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hv))
  · rw [Finset.sum_insert hnot, Function.update_self]
    have hcongr : ∑ v ∈ (D.erase a).erase M,
        Multiset.replicate v (Function.update f (a + M) x v) =
        ∑ v ∈ (D.erase a).erase M, Multiset.replicate v (f v) := by
      apply Finset.sum_congr rfl
      intro v hv
      rw [Function.update_of_ne (fun h : v = a + M => hnot (by rw [← h]; exact hv))]
    have e1 : Multiset.replicate a (f a) + ∑ v ∈ D.erase a, Multiset.replicate v (f v) =
        ∑ v ∈ D, Multiset.replicate v (f v) :=
      Finset.add_sum_erase D (fun v => Multiset.replicate v (f v)) ha
    have e2 : Multiset.replicate M (f M) + ∑ v ∈ (D.erase a).erase M, Multiset.replicate v (f v) =
        ∑ v ∈ D.erase a, Multiset.replicate v (f v) :=
      Finset.add_sum_erase (D.erase a) (fun v => Multiset.replicate v (f v)) hM'
    rw [hcongr, ← hR.2, ← e1, ← e2, hfa, hfM, Multiset.replicate_add, add_assoc]
  · have h2 : 1 < D.card := Finset.one_lt_card.mpr ⟨a, ha, M, hM, haM⟩
    rw [Finset.card_insert_of_notMem hnot, Finset.card_erase_of_mem hM',
      Finset.card_erase_of_mem ha]
    omega

/-- In a representation with the fewest blocks no value has more than half of the blocks,
rounded up. -/
theorem a239455_star (y : Multiset ℕ) (D : Finset ℕ) (f : ℕ → ℕ) (hR : a239455_Rep y D f)
    (hmin : ∀ (D' : Finset ℕ) (f' : ℕ → ℕ), a239455_Rep y D' f' → D.card ≤ D'.card) (x : ℕ) :
    2 * (D.filter (fun v => f v = x)).card ≤ D.card + 1 := by
  classical
  by_contra hcon
  have hAne : (D.filter (fun v => f v = x)).Nonempty := by
    apply Finset.card_pos.mp
    omega
  obtain ⟨M, hMdef⟩ : ∃ M, M = (D.filter (fun v => f v = x)).max' hAne := ⟨_, rfl⟩
  have hMA : M ∈ D.filter (fun v => f v = x) := by
    rw [hMdef]
    exact Finset.max'_mem _ hAne
  have hMmax : ∀ b ∈ D.filter (fun v => f v = x), b ≤ M := by
    intro b hb
    rw [hMdef]
    exact Finset.le_max' _ b hb
  have hinj : ((D.filter (fun v => f v = x)).erase M).card ≤
      (D \ D.filter (fun v => f v = x)).card := by
    apply Finset.card_le_card_of_injOn (fun a => a + M)
    · intro a ha
      have ha' : a ∈ (D.filter (fun v => f v = x)).erase M := ha
      rw [Finset.mem_erase] at ha'
      have haD : a ∈ D := (Finset.mem_filter.mp ha'.2).1
      show a + M ∈ D \ D.filter (fun v => f v = x)
      rw [Finset.mem_sdiff]
      constructor
      · by_contra hnew
        obtain ⟨D', f', hR', hcard⟩ := a239455_merge y D f hR a M x haD
          (Finset.mem_filter.mp hMA).1 ha'.1 (Finset.mem_filter.mp ha'.2).2
          (Finset.mem_filter.mp hMA).2 hnew
        have h1 := hmin D' f' hR'
        omega
      · intro hmem
        have hle := hMmax (a + M) hmem
        have hapos := hR.1 a haD
        omega
    · intro a _ b _ h
      have h' : a + M = b + M := h
      omega
  have h1 : ((D.filter (fun v => f v = x)).erase M).card =
      (D.filter (fun v => f v = x)).card - 1 := Finset.card_erase_of_mem hMA
  have h3 : (D \ D.filter (fun v => f v = x)).card + (D.filter (fun v => f v = x)).card =
      D.card := Finset.card_sdiff_add_card_eq_card (Finset.filter_subset _ _)
  omega

/-- From an ordering of the blocks without equal neighbours to a list with distinct runs. -/
theorem a239455_build (y : Multiset ℕ) (D : Finset ℕ) (f : ℕ → ℕ) (hR : a239455_Rep y D f)
    (L : List ℕ) (hL1 : L.Nodup) (hL2 : L.toFinset = D) (hL3 : (L.map f).IsChain (· ≠ ·)) :
    ∃ l : List ℕ, (l : Multiset ℕ) = y ∧ (OMA.S_oeis_a239455.runLengths l).Nodup := by
  have hpos : ∀ v ∈ L, 0 < v := fun v hv => hR.1 v (by rw [← hL2]; exact List.mem_toFinset.mpr hv)
  refine ⟨(L.map (fun v => List.replicate v (f v))).flatten, ?_, ?_⟩
  · show Multiset.ofList (L.map (fun v => List.replicate v (f v))).flatten = y
    rw [a239455_coe_flatten, List.map_map, ← hR.2, ← hL2, List.sum_toFinset _ hL1]
    congr 1
  · unfold OMA.S_oeis_a239455.runLengths
    rw [List.splitBy_flatten]
    · rw [List.map_map]
      have e : (List.length ∘ fun v => List.replicate v (f v)) = id := by
        funext v
        simp
      rw [e, List.map_id]
      exact hL1
    · intro hmem
      obtain ⟨v, hv, hv'⟩ := List.mem_map.mp hmem
      have h1 := hpos v hv
      have h2 : v = 0 := by simpa using hv'
      omega
    · intro m hm
      obtain ⟨v, -, rfl⟩ := List.mem_map.mp hm
      exact (List.pairwise_replicate.mpr (Or.inr (by simp))).isChain
    · rw [List.isChain_map]
      have h3 := (List.isChain_map f).mp hL3
      rw [List.isChain_iff_getElem] at h3 ⊢
      intro i hi
      have hv := hpos L[i] (List.getElem_mem _)
      have hw := hpos L[i + 1] (List.getElem_mem _)
      refine ⟨by simp; omega, by simp; omega, ?_⟩
      simp only [List.getLast_replicate, List.head_replicate]
      simpa using h3 i hi

theorem a239455_const : ∀ g : List ℕ, g.IsChain (fun x y => (x == y) = true) →
    g = List.replicate g.length (g.headD 0)
  | [], _ => rfl
  | [_], _ => rfl
  | a :: b :: t, h => by
      rw [List.isChain_cons_cons] at h
      have hab : a = b := by simpa using h.1
      have ih := a239455_const (b :: t) h.2
      subst hab
      simp only [List.length_cons, List.headD_cons] at ih ⊢
      rw [List.replicate_succ]
      congr 1

theorem a239455_find : ∀ G : List (List ℕ), (G.map List.length).Nodup → ∀ g ∈ G,
    G.find? (fun h => decide (h.length = g.length)) = some g
  | [], _, g, hg => by simp at hg
  | h :: T, hnd, g, hg => by
      rw [List.map_cons, List.nodup_cons] at hnd
      rcases List.mem_cons.mp hg with rfl | hgT
      · simp
      · have hne : h.length ≠ g.length := by
          intro e
          apply hnd.1
          rw [e]
          exact List.mem_map.mpr ⟨g, hgT, rfl⟩
        rw [List.find?_cons_of_neg (by simpa using hne)]
        exact a239455_find T hnd.2 g hgT

/-- A list with distinct run-lengths gives a representation by blocks. -/
theorem a239455_of_perm (y : Multiset ℕ) (l : List ℕ) (hl : (l : Multiset ℕ) = y)
    (hnd : (OMA.S_oeis_a239455.runLengths l).Nodup) :
    ∃ (D : Finset ℕ) (f : ℕ → ℕ), a239455_Rep y D f := by
  unfold OMA.S_oeis_a239455.runLengths at hnd
  obtain ⟨G, hG⟩ : ∃ G, G = l.splitBy (· == ·) := ⟨_, rfl⟩
  rw [← hG] at hnd
  have hGne : ∀ g ∈ G, g ≠ [] := fun g hg => List.ne_nil_of_mem_splitBy (hG ▸ hg)
  have hGc : ∀ g ∈ G, g = List.replicate g.length (g.headD 0) :=
    fun g hg => a239455_const g (List.isChain_of_mem_splitBy (hG ▸ hg))
  refine ⟨(G.map List.length).toFinset,
    fun v => ((G.find? (fun h => decide (h.length = v))).map (fun g => g.headD 0)).getD 0, ?_, ?_⟩
  · intro v hv
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hv)
    exact List.length_pos_iff.mpr (hGne g hg)
  · rw [List.sum_toFinset _ hnd, List.map_map, ← hl]
    have hflat : l = G.flatten := by rw [hG, List.flatten_splitBy]
    show _ = Multiset.ofList l
    rw [hflat, a239455_coe_flatten]
    congr 1
    apply List.map_congr_left
    intro g hg
    simp only [Function.comp_apply]
    rw [a239455_find G hnd g hg]
    simp only [Option.map_some, Option.getD_some]
    rw [← Multiset.coe_replicate, ← hGc g hg]

theorem a239455_rep_of_ls {n : ℕ} (y : Nat.Partition n) (h : OMA.S_oeis_a239455.IsLookAndSay y) :
    ∃ (D : Finset ℕ) (f : ℕ → ℕ), a239455_Rep y.parts D f := by
  obtain ⟨p, hp⟩ := h
  exact ⟨p.parts.toFinset, fun v => p.parts.count v,
    fun v hv => p.parts_pos (Multiset.mem_toFinset.mp hv), hp⟩

theorem a239455_ls_of_rep {n : ℕ} (y : Nat.Partition n) (D : Finset ℕ) (f : ℕ → ℕ)
    (hR : a239455_Rep y.parts D f) : OMA.S_oeis_a239455.IsLookAndSay y := by
  classical
  have hf : ∀ v ∈ D, 0 < f v := by
    intro v hv
    apply y.parts_pos
    rw [← hR.2, Multiset.mem_sum]
    exact ⟨v, hv, Multiset.mem_replicate.mpr ⟨(hR.1 v hv).ne', rfl⟩⟩
  obtain ⟨P, hP⟩ : ∃ P : Multiset ℕ, P = ∑ v ∈ D, Multiset.replicate (f v) v := ⟨_, rfl⟩
  have hcount : ∀ v ∈ D, P.count v = f v := by
    intro v hv
    rw [hP, Multiset.count_sum']
    simp only [Multiset.count_replicate]
    rw [Finset.sum_ite_eq' D v f, if_pos hv]
  have hmem : ∀ v, v ∈ P ↔ v ∈ D := by
    intro v
    rw [hP, Multiset.mem_sum]
    constructor
    · rintro ⟨w, hw, hvw⟩
      rw [Multiset.mem_replicate] at hvw
      rw [hvw.2]
      exact hw
    · intro hv
      exact ⟨v, hv, Multiset.mem_replicate.mpr ⟨(hf v hv).ne', rfl⟩⟩
  have hsum : P.sum = n := by
    have h1 : P.sum = ∑ v ∈ D, f v * v := by
      rw [hP, Multiset.sum_sum]
      apply Finset.sum_congr rfl
      intro v _
      rw [Multiset.sum_replicate, smul_eq_mul]
    have h2 : y.parts.sum = ∑ v ∈ D, v * f v := by
      rw [← hR.2, Multiset.sum_sum]
      apply Finset.sum_congr rfl
      intro v _
      rw [Multiset.sum_replicate, smul_eq_mul]
    rw [h1, ← y.parts_sum, h2]
    exact Finset.sum_congr rfl (fun v _ => Nat.mul_comm _ _)
  refine ⟨⟨P, fun {i} hi => hR.1 i ((hmem i).mp hi), hsum⟩, ?_⟩
  show ∑ v ∈ P.toFinset, Multiset.replicate v (P.count v) = y.parts
  have hfin : P.toFinset = D := by
    ext v
    rw [Multiset.mem_toFinset, hmem]
  rw [hfin, ← hR.2]
  exact Finset.sum_congr rfl (fun v hv => by rw [hcount v hv])

theorem OMA.solution : type_of% @OMA.S_oeis_a239455.main := by
  intro n y
  constructor
  · intro h
    classical
    obtain ⟨D0, f0, hR0⟩ := a239455_rep_of_ls y h
    have hex : ∃ k : ℕ, ∃ (D : Finset ℕ) (f : ℕ → ℕ), a239455_Rep y.parts D f ∧ D.card = k :=
      ⟨_, D0, f0, hR0, rfl⟩
    obtain ⟨D, f, hR, hk⟩ := Nat.find_spec hex
    have hmin : ∀ (D' : Finset ℕ) (f' : ℕ → ℕ), a239455_Rep y.parts D' f' →
        D.card ≤ D'.card := by
      intro D' f' h'
      rw [hk]
      exact Nat.find_min' hex ⟨D', f', h', rfl⟩
    have hstar := a239455_star y.parts D f hR hmin
    have hc : 2 * (D.filter (fun v => f v = D.sup f + 1)).card ≤ D.card := by
      have he : D.filter (fun v => f v = D.sup f + 1) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro v hv h1
        have h2 := Finset.le_sup (f := f) hv
        omega
      rw [he]
      simp
    obtain ⟨L, hL1, hL2, hL3⟩ := a239455_arr D.card D f (D.sup f + 1) rfl hstar hc
    obtain ⟨l, hl1, hl2⟩ := a239455_build y.parts D f hR L hL1 hL2 hL3.tail
    exact ⟨l, hl1, hl2⟩
  · rintro ⟨l, hl1, hl2⟩
    obtain ⟨D, f, hR⟩ := a239455_of_perm y.parts l hl1 hl2
    exact a239455_ls_of_rep y D f hR
