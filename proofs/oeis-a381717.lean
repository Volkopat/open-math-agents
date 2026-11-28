import OMAStatements.S_oeis_a381717
import Mathlib

-- OEIS A381717, conjecture of Gus Wiseman (2025): a partition cannot be partitioned into
-- constant blocks with distinct sums if and only if no listing of its parts has all run-sums
-- distinct. This is the negated form of the equivalence proved below (a381717_iff).
--
-- Both properties are about writing the multiset y of parts as a union of blocks
--   (s / f s copies of the value f s),  s ranging over a finite set D of positive integers,
-- where f s divides s, so that s is the sum of its block.
-- Constant blocks with distinct sums: such (D, f) exists.
-- Distinct run-sums: such (D, f) exists together with an ordering of D in which
--   consecutive blocks have different values (the blocks are then exactly the runs).
-- Proof of the nontrivial direction: take (D, f) with |D| minimal. Let x be a value, M the
-- largest sum of a block of value x. For every other block a of value x the number a + M must
-- be the sum of a block of another value (otherwise merge a and M; it exceeds M, so it is not
-- a block of value x). So no value has more than (|D| + 1) / 2 blocks, and then a greedy choice
-- orders the blocks without equal neighbours.

/-- y is the union of the blocks: s / f s copies of f s, for s in D. -/
def a381717_Rep (y : Multiset ℕ) (D : Finset ℕ) (f : ℕ → ℕ) : Prop :=
  (∀ s ∈ D, 0 < s ∧ f s ∣ s) ∧ ∑ s ∈ D, Multiset.replicate (s / f s) (f s) = y

theorem a381717_coe_flatten : ∀ B : List (List ℕ),
    Multiset.ofList B.flatten = (B.map Multiset.ofList).sum
  | [] => by simp
  | b :: T => by
      rw [List.flatten_cons, ← Multiset.coe_add, a381717_coe_flatten T, List.map_cons,
        List.sum_cons]

/-- Ordering blocks so that neighbours have different values, when no value is too frequent. -/
theorem a381717_arr : ∀ (k : ℕ) (D : Finset ℕ) (f : ℕ → ℕ) (c : ℕ), D.card = k →
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
      obtain ⟨L, hL1, hL2, hL3⟩ := a381717_arr k (D.erase e) f (f e) hcard hA hB
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

/-- Two blocks of the same value can be merged when the new sum is free. -/
theorem a381717_merge (y : Multiset ℕ) (D : Finset ℕ) (f : ℕ → ℕ) (hR : a381717_Rep y D f)
    (a M x : ℕ) (ha : a ∈ D) (hM : M ∈ D) (haM : a ≠ M) (hfa : f a = x) (hfM : f M = x)
    (hnew : a + M ∉ D) :
    ∃ (D' : Finset ℕ) (f' : ℕ → ℕ), a381717_Rep y D' f' ∧ D'.card + 1 = D.card := by
  classical
  have hnot : a + M ∉ (D.erase a).erase M :=
    fun h => hnew (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase h))
  have hM' : M ∈ D.erase a := Finset.mem_erase.mpr ⟨fun h => haM h.symm, hM⟩
  have hxa : x ∣ a := by
    rw [← hfa]
    exact (hR.1 a ha).2
  have hxM : x ∣ M := by
    rw [← hfM]
    exact (hR.1 M hM).2
  refine ⟨insert (a + M) ((D.erase a).erase M), Function.update f (a + M) x, ⟨?_, ?_⟩, ?_⟩
  · intro v hv
    rcases Finset.mem_insert.mp hv with hv | hv
    · rw [hv, Function.update_self]
      have h1 := (hR.1 a ha).1
      exact ⟨by omega, dvd_add hxa hxM⟩
    · rw [Function.update_of_ne (fun h : v = a + M => hnot (by rw [← h]; exact hv))]
      exact hR.1 v (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hv))
  · rw [Finset.sum_insert hnot, Function.update_self]
    have hcongr : ∑ v ∈ (D.erase a).erase M,
        Multiset.replicate (v / Function.update f (a + M) x v) (Function.update f (a + M) x v) =
        ∑ v ∈ (D.erase a).erase M, Multiset.replicate (v / f v) (f v) := by
      apply Finset.sum_congr rfl
      intro v hv
      rw [Function.update_of_ne (fun h : v = a + M => hnot (by rw [← h]; exact hv))]
    have e1 : Multiset.replicate (a / f a) (f a) +
        ∑ v ∈ D.erase a, Multiset.replicate (v / f v) (f v) =
        ∑ v ∈ D, Multiset.replicate (v / f v) (f v) :=
      Finset.add_sum_erase D (fun v => Multiset.replicate (v / f v) (f v)) ha
    have e2 : Multiset.replicate (M / f M) (f M) +
        ∑ v ∈ (D.erase a).erase M, Multiset.replicate (v / f v) (f v) =
        ∑ v ∈ D.erase a, Multiset.replicate (v / f v) (f v) :=
      Finset.add_sum_erase (D.erase a) (fun v => Multiset.replicate (v / f v) (f v)) hM'
    rw [hcongr, ← hR.2, ← e1, ← e2, hfa, hfM, Nat.add_div_of_dvd_right hxa,
      Multiset.replicate_add, add_assoc]
  · have h2 : 1 < D.card := Finset.one_lt_card.mpr ⟨a, ha, M, hM, haM⟩
    rw [Finset.card_insert_of_notMem hnot, Finset.card_erase_of_mem hM',
      Finset.card_erase_of_mem ha]
    omega

/-- In a representation with the fewest blocks no value has more than half of the blocks,
rounded up. -/
theorem a381717_star (y : Multiset ℕ) (D : Finset ℕ) (f : ℕ → ℕ) (hR : a381717_Rep y D f)
    (hmin : ∀ (D' : Finset ℕ) (f' : ℕ → ℕ), a381717_Rep y D' f' → D.card ≤ D'.card) (x : ℕ) :
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
        obtain ⟨D', f', hR', hcard⟩ := a381717_merge y D f hR a M x haD
          (Finset.mem_filter.mp hMA).1 ha'.1 (Finset.mem_filter.mp ha'.2).2
          (Finset.mem_filter.mp hMA).2 hnew
        have h1 := hmin D' f' hR'
        omega
      · intro hmem
        have hle := hMmax (a + M) hmem
        have hapos := (hR.1 a haD).1
        omega
    · intro a _ b _ h
      have h' : a + M = b + M := h
      omega
  have h1 : ((D.filter (fun v => f v = x)).erase M).card =
      (D.filter (fun v => f v = x)).card - 1 := Finset.card_erase_of_mem hMA
  have h3 : (D \ D.filter (fun v => f v = x)).card + (D.filter (fun v => f v = x)).card =
      D.card := Finset.card_sdiff_add_card_eq_card (Finset.filter_subset _ _)
  omega

/-- From an ordering of the blocks without equal neighbours to a list with distinct run-sums. -/
theorem a381717_build (y : Multiset ℕ) (D : Finset ℕ) (f : ℕ → ℕ) (hR : a381717_Rep y D f)
    (L : List ℕ) (hL1 : L.Nodup) (hL2 : L.toFinset = D) (hL3 : (L.map f).IsChain (· ≠ ·)) :
    ∃ l : List ℕ, (l : Multiset ℕ) = y ∧ (OMA.S_oeis_a381717.runSums l).Nodup := by
  have hmem : ∀ v ∈ L, v ∈ D := fun v hv => by
    rw [← hL2]
    exact List.mem_toFinset.mpr hv
  have hpos : ∀ v ∈ L, 0 < v / f v := by
    intro v hv
    obtain ⟨h1, h2⟩ := hR.1 v (hmem v hv)
    exact Nat.div_pos (Nat.le_of_dvd h1 h2) (Nat.pos_of_dvd_of_pos h2 h1)
  refine ⟨(L.map (fun v => List.replicate (v / f v) (f v))).flatten, ?_, ?_⟩
  · show Multiset.ofList (L.map (fun v => List.replicate (v / f v) (f v))).flatten = y
    rw [a381717_coe_flatten, List.map_map, ← hR.2, ← hL2, List.sum_toFinset _ hL1]
    congr 1
  · unfold OMA.S_oeis_a381717.runSums
    rw [List.splitBy_flatten]
    · rw [List.map_map]
      have e : L.map (List.sum ∘ fun v => List.replicate (v / f v) (f v)) = L.map id := by
        apply List.map_congr_left
        intro v hv
        simp only [Function.comp_apply, List.sum_replicate, smul_eq_mul, id]
        exact Nat.div_mul_cancel (hR.1 v (hmem v hv)).2
      rw [e, List.map_id]
      exact hL1
    · intro hmem'
      obtain ⟨v, hv, hv'⟩ := List.mem_map.mp hmem'
      have h1 := hpos v hv
      have h2 : (List.replicate (v / f v) (f v)).length = 0 := by
        rw [show List.replicate (v / f v) (f v) = [] from hv']
        rfl
      rw [List.length_replicate] at h2
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
      refine ⟨List.ne_nil_of_length_pos (by simpa using hv),
        List.ne_nil_of_length_pos (by simpa using hw), ?_⟩
      simp only [List.getLast_replicate, List.head_replicate]
      simpa using h3 i hi

theorem a381717_const : ∀ g : List ℕ, g.IsChain (fun x y => (x == y) = true) →
    g = List.replicate g.length (g.headD 0)
  | [], _ => rfl
  | [_], _ => rfl
  | a :: b :: t, h => by
      rw [List.isChain_cons_cons] at h
      have hab : a = b := by simpa using h.1
      have ih := a381717_const (b :: t) h.2
      subst hab
      simp only [List.length_cons, List.headD_cons] at ih ⊢
      rw [List.replicate_succ]
      congr 1

/-- A list with distinct run-sums gives constant blocks with distinct sums: its runs. -/
theorem a381717_of_perm (y : Multiset ℕ) (l : List ℕ) (hl : (l : Multiset ℕ) = y)
    (hnd : (OMA.S_oeis_a381717.runSums l).Nodup) :
    ∃ P : Multiset (Multiset ℕ), P.sum = y ∧
      (∀ b ∈ P, b ≠ 0 ∧ ∃ v, b = Multiset.replicate (Multiset.card b) v) ∧
      (P.map Multiset.sum).Nodup := by
  unfold OMA.S_oeis_a381717.runSums at hnd
  obtain ⟨G, hG⟩ : ∃ G, G = l.splitBy (· == ·) := ⟨_, rfl⟩
  rw [← hG] at hnd
  have hGne : ∀ g ∈ G, g ≠ [] := fun g hg => List.ne_nil_of_mem_splitBy (hG ▸ hg)
  have hGc : ∀ g ∈ G, g = List.replicate g.length (g.headD 0) :=
    fun g hg => a381717_const g (List.isChain_of_mem_splitBy (hG ▸ hg))
  have hflat : l = G.flatten := by rw [hG, List.flatten_splitBy]
  refine ⟨Multiset.ofList (G.map Multiset.ofList), ?_, ?_, ?_⟩
  · rw [Multiset.sum_coe, ← a381717_coe_flatten, ← hflat]
    exact hl
  · intro b hb
    rw [Multiset.mem_coe] at hb
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hb
    refine ⟨?_, g.headD 0, ?_⟩
    · intro h0
      exact hGne g hg ((Multiset.coe_eq_zero g).mp h0)
    · rw [Multiset.coe_card, ← Multiset.coe_replicate, ← hGc g hg]
  · rw [Multiset.map_coe, Multiset.coe_nodup, List.map_map]
    have e : G.map (Multiset.sum ∘ Multiset.ofList) = G.map List.sum := by
      apply List.map_congr_left
      intro g _
      simp only [Function.comp_apply, Multiset.sum_coe]
    rw [e]
    exact hnd

/-- Constant blocks with distinct sums give a representation indexed by the sums. -/
theorem a381717_rep_of_blocks : ∀ P : Multiset (Multiset ℕ),
    (∀ b ∈ P, ∃ m v, 0 < m ∧ 0 < v ∧ b = Multiset.replicate m v) →
    (P.map Multiset.sum).Nodup →
    ∃ (D : Finset ℕ) (f : ℕ → ℕ), a381717_Rep P.sum D f ∧ ∀ s ∈ D, s ∈ P.map Multiset.sum := by
  classical
  intro P
  induction P using Multiset.induction_on with
  | empty =>
      intro _ _
      exact ⟨∅, fun _ => 0, ⟨by simp, by simp⟩, by simp⟩
  | cons b P ih =>
      intro hb hnd
      rw [Multiset.map_cons, Multiset.nodup_cons] at hnd
      obtain ⟨D, f, hR, hD⟩ := ih (fun c hc => hb c (Multiset.mem_cons_of_mem hc)) hnd.2
      obtain ⟨m, v, hm, hv, hbmv⟩ := hb b (Multiset.mem_cons_self b P)
      have hsum : b.sum = m * v := by
        rw [hbmv, Multiset.sum_replicate, smul_eq_mul]
      rw [hsum] at hnd
      have hnot : m * v ∉ D := fun h => hnd.1 (hD _ h)
      have hupd : ∀ s ∈ D, Function.update f (m * v) v s = f s := by
        intro s hs
        rw [Function.update_of_ne (fun h : s = m * v => hnot (by rw [← h]; exact hs))]
      refine ⟨insert (m * v) D, Function.update f (m * v) v, ⟨?_, ?_⟩, ?_⟩
      · intro s hs
        rcases Finset.mem_insert.mp hs with hs | hs
        · rw [hs, Function.update_self]
          exact ⟨Nat.mul_pos hm hv, dvd_mul_left v m⟩
        · rw [hupd s hs]
          exact hR.1 s hs
      · rw [Finset.sum_insert hnot, Function.update_self, Multiset.sum_cons,
          Nat.mul_div_cancel m hv, ← hbmv]
        congr 1
        rw [← hR.2]
        apply Finset.sum_congr rfl
        intro s hs
        rw [hupd s hs]
      · intro s hs
        rw [Multiset.map_cons, Multiset.mem_cons, hsum]
        rcases Finset.mem_insert.mp hs with hs | hs
        · exact Or.inl hs
        · exact Or.inr (hD s hs)

theorem a381717_iff {n : ℕ} (y : Nat.Partition n) :
    OMA.S_oeis_a381717.HasConstBlockPartition y ↔ OMA.S_oeis_a381717.HasDistinctRunSumPerm y := by
  constructor
  · rintro ⟨P, hP1, hP2, hP3⟩
    classical
    have hblocks : ∀ b ∈ P, ∃ m v, 0 < m ∧ 0 < v ∧ b = Multiset.replicate m v := by
      intro b hb
      obtain ⟨hb0, v, hbv⟩ := hP2 b hb
      have hm : 0 < Multiset.card b := Multiset.card_pos.mpr hb0
      refine ⟨Multiset.card b, v, hm, ?_, hbv⟩
      apply y.parts_pos
      rw [← hP1]
      refine Multiset.mem_join.mpr ⟨b, hb, ?_⟩
      rw [hbv]
      exact Multiset.mem_replicate.mpr ⟨hm.ne', rfl⟩
    obtain ⟨D0, f0, hR0, -⟩ := a381717_rep_of_blocks P hblocks hP3
    rw [hP1] at hR0
    have hex : ∃ k : ℕ, ∃ (D : Finset ℕ) (f : ℕ → ℕ), a381717_Rep y.parts D f ∧ D.card = k :=
      ⟨_, D0, f0, hR0, rfl⟩
    obtain ⟨D, f, hR, hk⟩ := Nat.find_spec hex
    have hmin : ∀ (D' : Finset ℕ) (f' : ℕ → ℕ), a381717_Rep y.parts D' f' →
        D.card ≤ D'.card := by
      intro D' f' h'
      rw [hk]
      exact Nat.find_min' hex ⟨D', f', h', rfl⟩
    have hstar := a381717_star y.parts D f hR hmin
    have hc : 2 * (D.filter (fun v => f v = D.sup f + 1)).card ≤ D.card := by
      have he : D.filter (fun v => f v = D.sup f + 1) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro v hv h1
        have h2 := Finset.le_sup (f := f) hv
        omega
      rw [he]
      simp
    obtain ⟨L, hL1, hL2, hL3⟩ := a381717_arr D.card D f (D.sup f + 1) rfl hstar hc
    obtain ⟨l, hl1, hl2⟩ := a381717_build y.parts D f hR L hL1 hL2 hL3.tail
    exact ⟨l, hl1, hl2⟩
  · rintro ⟨l, hl1, hl2⟩
    exact a381717_of_perm y.parts l hl1 hl2

theorem OMA.solution : type_of% @OMA.S_oeis_a381717.main := by
  intro n y
  exact not_congr (a381717_iff y)
