import OMAReductions.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R2_H2_R1_H1_R1
-- Written on the Wall II, Graph 189. Integration by @ali-hamdan-007.
-- Short-order theorem and protected-path estimates by @carl2sheriff,
-- https://github.com/lefttosolve2/open-math-agents/pull/22587
-- R2 by @carl2sheriff, with R1 path and metric arguments by
-- @computerfreak97 (PR 2971) and philipsaint's Dirac formalization.
-- The linked-set theorem of Ma, Ning and Zhao was formalized by @koolkao,
-- https://github.com/lefttosolve2/open-math-agents/pull/7971
-- Sources and credits are in github.com/ali-hamdan-007/open-math-agents,
-- research/parallel-lean-results, research/graph189/full/direct/continuation.
section
open SimpleGraph
open scoped BigOperators
namespace OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
lemma degree_pair [DecidableRel G.Adj] [Nontrivial V] (x y : V) (hne : x ≠ y) :
    secondSmallestDegree G ≤ G.degree x ∨ secondSmallestDegree G ≤ G.degree y := by
  classical
  let ds := degreeSequence G
  have hlen : 2 ≤ ds.length := by
    simpa [ds, degreeSequence] using Nat.succ_le_of_lt (Fintype.one_lt_card (α := V))
  obtain ⟨a,b,l,heq⟩ : ∃ a b l, ds = a :: b :: l := by
    cases h : ds with
    | nil => simp [h] at hlen
    | cons a tail =>
      cases hh : tail with
      | nil => simp [h, hh] at hlen
      | cons b l => exact ⟨a,b,l,rfl⟩
  have hs : ds.Pairwise (· ≤ ·) := by simp [ds, degreeSequence]
  rw [heq] at hs
  have hlow : ∀ t ∈ l, b ≤ t := (List.pairwise_cons.mp (List.pairwise_cons.mp hs).2).1
  have hnil : l.filter (fun t => decide (t < b)) = [] := by
    simpa [List.filter_eq_nil_iff] using hlow
  have hct : (ds.filter (fun t => decide (t < b))).length ≤ 1 := by
    rw [heq]
    by_cases h : a < b <;> simp [h,hnil]
  have hcoeds : (↑ds : Multiset ℕ) = Finset.univ.val.map (fun v : V => G.degree v) := by
    simp [ds, degreeSequence]
  let low := Finset.univ.filter (fun v : V => G.degree v < b)
  have hl : low.card ≤ 1 := by
    change (Multiset.filter (fun t => G.degree t < b) Finset.univ.val).card ≤ 1
    have hct' : (Multiset.filter (fun t => t < b) (↑ds : Multiset ℕ)).card ≤ 1 := hct
    rw [hcoeds, Multiset.filter_map, Multiset.card_map] at hct'
    exact hct'
  have hb : secondSmallestDegree G = b := by
    change ds.getD 1 0 = b
    simp [heq]
  rw [hb]
  by_contra! h
  exact hne (Finset.card_le_one.mp hl x (by simpa [low] using h.1) y (by simpa [low] using h.2))
end OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1
end
section
namespace Graph189CutSides
open SimpleGraph Finset
open OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
omit [DecidableEq V] [DecidableRel G.Adj] in
theorem connected_after_smaller_deletion (T : Finset V) (ht : T.card < G.vertexConnectivity) :
    (G.induce {u : V | u ∉ T}).Connected := by
  classical
  by_contra bad
  have hn := Fintype.one_lt_card (α := V)
  have bound : G.vertexConnectivity ≤ T.card := by
    unfold vertexConnectivity
    rw [if_neg (by omega : ¬ Fintype.card V ≤ 1)]
    exact Nat.sInf_le ⟨T,rfl,Or.inl bad⟩
  omega
end Graph189CutSides
end
section
namespace OMA.BondyK
open SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
lemma chain_sub {R : V → V → Prop} {l l₁ : List V} (h : l.IsChain R) (hs : l₁ <:+: l) :
    l₁.IsChain R := by
  obtain ⟨s, t, rfl⟩ := hs
  exact (List.isChain_append.mp (List.isChain_append.mp h).1).2.1
lemma chain_pre {R : V → V → Prop} {l l₁ : List V} (h : l.IsChain R) (hs : l₁ <+: l) :
    l₁.IsChain R := by
  obtain ⟨t, rfl⟩ := hs
  exact (List.isChain_append.mp h).1
def ABP (G : SimpleGraph V) (A B : Finset V) (l : List V) : Prop :=
  l.Nodup ∧ l.IsChain G.Adj ∧ (∃ a ∈ A, l.head? = some a) ∧ (∃ b ∈ B, l.getLast? = some b)
def Sep (G : SimpleGraph V) (A B S : Finset V) : Prop :=
  ∀ l, ABP G A B l → ∃ x ∈ l, x ∈ S
lemma getLast?_app_cons (p q : List V) (y : V) :
    (p ++ y :: q).getLast? = (y :: q).getLast? := by
  rw [List.getLast?_append, List.getLast?_cons]; rfl
lemma erase_loops {R : V → V → Prop} : ∀ l : List V, l.IsChain R →
    ∃ l' : List V, l'.Nodup ∧ l'.IsChain R ∧ l'.head? = l.head? ∧
      l'.getLast? = l.getLast? ∧ ∀ z ∈ l', z ∈ l
  | [], _ => ⟨[], List.nodup_nil, List.isChain_nil, rfl, rfl, fun _ h => h⟩
  | z :: t, h => by
    obtain ⟨t', hnd, hch, hhd, hlast, hsub⟩ := erase_loops t (List.isChain_cons.mp h).2
    by_cases hz : z ∈ t'
    · obtain ⟨u, w, rfl⟩ := List.append_of_mem hz
      have ht : t ≠ [] := by
        rintro rfl; exact absurd (hsub z (by simp)) (by simp)
      obtain ⟨c, hc⟩ : ∃ c, t.getLast? = some c := by
        cases h' : t.getLast? with
        | none => exact absurd (List.getLast?_eq_none_iff.mp h') ht
        | some c => exact ⟨c, rfl⟩
      refine ⟨z :: w, hnd.sublist (List.sublist_append_right u _), hch.right_of_append, rfl,
        ?_, ?_⟩
      · rw [getLast?_app_cons] at hlast
        rw [hlast, hc, List.getLast?_cons, hc]; rfl
      · intro a ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (hsub a (by simp [ha]))
    · refine ⟨z :: t', List.nodup_cons.mpr ⟨hz, hnd⟩,
        hch.cons (fun y hy => (List.isChain_cons.mp h).1 y (by rw [← hhd]; exact hy)), rfl,
        by rw [List.getLast?_cons, List.getLast?_cons, hlast], ?_⟩
      intro a ha
      rcases List.mem_cons.mp ha with rfl | ha
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (hsub a ha)
lemma sep_chain {A B S : Finset V} (hS : Sep G A B S) {l : List V}
    (hch : l.IsChain G.Adj) (hA : ∃ a ∈ A, l.head? = some a)
    (hB : ∃ b ∈ B, l.getLast? = some b) : ∃ z ∈ l, z ∈ S := by
  obtain ⟨l', hnd, hch', hhd, hlast, hsub⟩ := erase_loops l hch
  obtain ⟨z, hz, hzS⟩ := hS l' ⟨hnd, hch', by rw [hhd]; exact hA, by rw [hlast]; exact hB⟩
  exact ⟨z, hsub z hz, hzS⟩
lemma abp_mono {H : SimpleGraph V} (hle : H ≤ G) {A B : Finset V} {l : List V}
    (h : ABP H A B l) : ABP G A B l :=
  ⟨h.1, h.2.1.imp (fun _ _ h => hle h), h.2.2⟩
lemma abp_reverse {A B : Finset V} {l : List V} (h : ABP G A B l) : ABP G B A l.reverse := by
  obtain ⟨hnd, hch, ⟨a, ha, hha⟩, ⟨b, hb, hlb⟩⟩ := h
  exact ⟨List.nodup_reverse.mpr hnd, List.isChain_reverse.mpr (hch.imp fun _ _ h => h.symm),
    ⟨b, hb, by simpa using hlb⟩, ⟨a, ha, by simpa using hha⟩⟩
lemma sep_reverse {A B S : Finset V} (h : Sep G A B S) : Sep G B A S := fun l hl => by
  obtain ⟨z, hz, hzS⟩ := h l.reverse (abp_reverse hl)
  exact ⟨z, List.mem_reverse.mp hz, hzS⟩
lemma exists_bad {R R' : V → V → Prop} : ∀ l : List V, l.IsChain R → ¬ l.IsChain R' →
    ∃ p u v q, l = p ++ u :: v :: q ∧ R u v ∧ ¬ R' u v
  | [], _, h' => absurd List.isChain_nil h'
  | [a], _, h' => absurd (List.isChain_singleton a) h'
  | a :: b :: t, h, h' => by
    rw [List.isChain_cons_cons] at h
    by_cases hab : R' a b
    · have : ¬ (b :: t).IsChain R' := fun hc => h' (List.isChain_cons_cons.mpr ⟨hab, hc⟩)
      obtain ⟨p, u, v, q, hl, h1, h2⟩ := exists_bad (b :: t) h.2 this
      exact ⟨a :: p, u, v, q, by rw [hl]; rfl, h1, h2⟩
    · exact ⟨[], a, b, t, rfl, h.1, hab⟩
lemma chain_del {H : SimpleGraph V} {x y : V}
    (hH : ∀ u v, H.Adj u v ↔ G.Adj u v ∧ s(u, v) ≠ s(x, y))
    {l : List V} (hl : l.IsChain G.Adj) (hy : y ∉ l ∨ x ∉ l) : l.IsChain H.Adj :=
  hl.imp_of_mem_imp fun u v hu hv huv => (hH u v).mpr ⟨huv, fun he => by
    rcases Sym2.eq_iff.mp he with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> subst h1 h2 <;> tauto⟩
lemma nodup_aux {p q : List V} {a b : V} (h : (p ++ a :: b :: q).Nodup) : b ∉ p ++ [a] := by
  intro hb
  rw [List.nodup_append] at h
  rcases List.mem_append.mp hb with hb | hb
  · exact h.2.2 b hb b (by simp) rfl
  · have := List.nodup_cons.mp h.2.1
    simp at hb; subst hb; exact this.1 (by simp)
lemma nodup_aux2 {p q : List V} {a b : V} (h : (p ++ a :: b :: q).Nodup) : a ∉ b :: q :=
  (List.nodup_cons.mp (List.nodup_append.mp h).2.1).1
lemma abp_of_prefix {A B : Finset V} {m l : List V} (hp : m <+: l) (hnd : l.Nodup)
    (hA : ∃ a ∈ A, l.head? = some a) (hch : m.IsChain G.Adj)
    (hB : ∃ b ∈ B, m.getLast? = some b) : ABP G A B m := by
  refine ⟨hnd.sublist hp.sublist, hch, ?_, hB⟩
  obtain ⟨t, rfl⟩ := hp
  obtain ⟨b, -, hb⟩ := hB
  obtain ⟨a, ha, hha⟩ := hA
  cases m with
  | nil => simp at hb
  | cons c m => exact ⟨a, ha, by simpa using hha⟩
lemma sep_last {A X : Finset V} : Sep G A X X := fun l hl => by
  obtain ⟨b, hb, hlb⟩ := hl.2.2.2
  exact ⟨b, List.mem_of_getLast? hlb, hb⟩
lemma sep_of_pre {H : SimpleGraph V} {A B X T : Finset V}
    (hpre : ∀ l, ABP G A B l → ∃ m, m <+: l ∧ ABP H A X m) (hT : Sep H A X T) :
    Sep G A B T := fun l hl => by
  obtain ⟨m, hm, hmX⟩ := hpre l hl
  obtain ⟨z, hz, hzT⟩ := hT m hmX
  exact ⟨z, hm.subset hz, hzT⟩
lemma sep_of_suf {H : SimpleGraph V} {A B Y T : Finset V}
    (hsuf : ∀ l, ABP G A B l → ∃ m, m <:+ l ∧ ABP H Y B m) (hT : Sep H Y B T) :
    Sep G A B T := fun l hl => by
  obtain ⟨m, hm, hmX⟩ := hsuf l hl
  obtain ⟨z, hz, hzT⟩ := hT m hmX
  exact ⟨z, hm.subset hz, hzT⟩
lemma exists_first (P : V → Prop) : ∀ l : List V, (∃ z ∈ l, P z) →
    ∃ l1 z l2, l = l1 ++ z :: l2 ∧ P z ∧ ∀ w ∈ l1, ¬ P w
  | [], h => by simp at h
  | a :: t, h => by
    by_cases ha : P a
    · exact ⟨[], a, t, rfl, ha, by simp⟩
    · obtain ⟨z, hz, hPz⟩ := h
      have : ∃ z ∈ t, P z := by
        rcases List.mem_cons.mp hz with rfl | hz
        · exact absurd hPz ha
        · exact ⟨z, hz, hPz⟩
      obtain ⟨l1, z', l2, rfl, h1, h2⟩ := exists_first P t this
      exact ⟨a :: l1, z', l2, rfl, h1, by simp [ha]; exact h2⟩
lemma exists_last (P : V → Prop) (l : List V) (h : ∃ z ∈ l, P z) :
    ∃ l1 z l2, l = l1 ++ z :: l2 ∧ P z ∧ ∀ w ∈ l2, ¬ P w := by
  obtain ⟨l1, z, l2, hl, h1, h2⟩ := exists_first P l.reverse (by simpa using h)
  refine ⟨l2.reverse, z, l1.reverse, ?_, h1, by simpa using h2⟩
  rw [← List.reverse_reverse l, hl]; simp
lemma trim {A B : Finset V} {l : List V} (hl : ABP G A B l) :
    ∃ l', ABP G A B l' ∧ (∀ x ∈ l'.tail, x ∉ A) ∧ (∀ x ∈ l'.dropLast, x ∉ B) ∧
      ∀ x ∈ l', x ∈ l := by
  obtain ⟨hnd, hch, ⟨a, ha, hha⟩, ⟨b, hb, hlb⟩⟩ := hl
  obtain ⟨l1, b', l2, rfl, hb', hl1⟩ :=
    exists_first (· ∈ B) l ⟨b, List.mem_of_getLast? hlb, hb⟩
  have hmA : ∃ z ∈ l1 ++ [b'], z ∈ A := by
    refine ⟨a, ?_, ha⟩
    rcases l1 with _ | ⟨c, l1'⟩
    · simp at hha; simp [hha]
    · simp at hha; simp [hha]
  obtain ⟨m1, a', m2, hm, ha', hm2⟩ := exists_last (· ∈ A) (l1 ++ [b']) hmA
  have hL : l1 ++ b' :: l2 = m1 ++ (a' :: m2) ++ l2 := by
    rw [← hm]; simp
  have hinf : a' :: m2 <:+: l1 ++ b' :: l2 := ⟨m1, l2, hL.symm⟩
  refine ⟨a' :: m2, ⟨hnd.sublist hinf.sublist, chain_sub hch hinf, ⟨a', ha', rfl⟩,
    ⟨b', hb', ?_⟩⟩, hm2, ?_, fun z hz => hinf.subset hz⟩
  · rw [← getLast?_app_cons m1, ← hm]; simp
  · have : l1 = m1 ++ (a' :: m2).dropLast := by
      rw [← List.dropLast_append_cons, ← hm, List.dropLast_concat]
    intro z hz
    exact hl1 z (by rw [this]; exact List.mem_append_right _ hz)
lemma trim_family {A B : Finset V} {k : ℕ} {P : Fin k → List V} (hP : ∀ i, ABP G A B (P i))
    (hd : ∀ i j, i ≠ j → ∀ x ∈ P i, x ∉ P j) :
    ∃ P' : Fin k → List V, (∀ i, ABP G A B (P' i) ∧ (∀ x ∈ (P' i).tail, x ∉ A) ∧
        (∀ x ∈ (P' i).dropLast, x ∉ B)) ∧ ∀ i j, i ≠ j → ∀ x ∈ P' i, x ∉ P' j := by
  choose P' h1 h2 h3 h4 using fun i => trim (hP i)
  exact ⟨P', fun i => ⟨h1 i, h2 i, h3 i⟩,
    fun i j hij x hx hx' => hd i j hij x (h4 i x hx) (h4 j x hx')⟩
lemma base {A B : Finset V} {k : ℕ} (hE : ∀ u v, ¬ G.Adj u v)
    (hsep : ∀ S, Sep G A B S → k ≤ S.card) :
    ∃ P : Fin k → List V, (∀ i, ABP G A B (P i)) ∧ ∀ i j, i ≠ j → ∀ x ∈ P i, x ∉ P j := by
  have hk : k ≤ (A ∩ B).card := hsep _ (fun l hl => by
    obtain ⟨hnd, hch, ⟨a, ha, hha⟩, ⟨b, hb, hlb⟩⟩ := hl
    obtain ⟨t, rfl⟩ := List.head?_eq_some_iff.mp hha
    cases t with
    | nil =>
      simp at hlb
      exact ⟨a, by simp, Finset.mem_inter.mpr ⟨ha, by rw [hlb]; exact hb⟩⟩
    | cons c t => exact absurd (List.isChain_cons_cons.mp hch).1 (hE a c))
  let e := (A ∩ B).equivFin.symm
  refine ⟨fun i => [(e (Fin.castLE hk i)).1], fun i => ⟨List.nodup_singleton _,
    List.isChain_singleton _, ⟨_, (Finset.mem_inter.mp (e _).2).1, rfl⟩,
    ⟨_, (Finset.mem_inter.mp (e _).2).2, rfl⟩⟩, ?_⟩
  intro i j hij x hx hx'
  simp only [List.mem_singleton] at hx hx'
  exact hij (Fin.castLE_injective hk (e.injective (Subtype.ext (hx.symm.trans hx'))))
lemma pre {H : SimpleGraph V} {x y : V}
    (hH : ∀ u v, H.Adj u v ↔ G.Adj u v ∧ s(u, v) ≠ s(x, y))
    {A B S : Finset V} (hSH : Sep H A B S) {q : List V} (hq : (y :: q).IsChain H.Adj)
    (hqB : ∃ b ∈ B, (y :: q).getLast? = some b) (hqS : ∀ z ∈ y :: q, z ∉ S)
    {l : List V} (hl : ABP G A B l) : ∃ m, m <+: l ∧ ABP H A (insert x S) m := by
  obtain ⟨hnd, hch, hA, hB⟩ := hl
  have key : ∀ l1, l1 <+: l → l1.IsChain H.Adj → (∃ z ∈ l1, z ∈ S) →
      ∃ m, m <+: l ∧ ABP H A (insert x S) m := by
    rintro l1 hp hc ⟨z, hz, hzS⟩
    obtain ⟨s, t, rfl⟩ := List.append_of_mem hz
    have hp' : s ++ [z] <+: s ++ z :: t := ⟨t, by simp⟩
    exact ⟨s ++ [z], hp'.trans hp, abp_of_prefix (hp'.trans hp) hnd hA (chain_pre hc hp')
      ⟨z, Finset.mem_insert_of_mem hzS, by simp⟩⟩
  by_cases hl : l.IsChain H.Adj
  · exact key l (List.prefix_refl l) hl (sep_chain hSH hl hA hB)
  · obtain ⟨p, u, v, q', rfl, huv, hnuv⟩ := exists_bad l hch hl
    have he : s(u, v) = s(x, y) := by
      by_contra hne; exact hnuv ((hH u v).mpr ⟨huv, hne⟩)
    have hp : p ++ [u] <+: p ++ u :: v :: q' := ⟨v :: q', by simp⟩
    rcases Sym2.eq_iff.mp he with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · subst h1 h2
      exact ⟨p ++ [u], hp, abp_of_prefix hp hnd hA
        (chain_del hH (chain_pre hch hp) (Or.inl (nodup_aux hnd)))
        ⟨u, Finset.mem_insert_self _ _, by simp⟩⟩
    · subst h1 h2
      have hc : (p ++ [u]).IsChain H.Adj :=
        chain_del hH (chain_pre hch hp) (Or.inr (nodup_aux hnd))
      by_cases hm : ∃ z ∈ p ++ [u], z ∈ S
      · exact key _ hp hc hm
      · exfalso
        push_neg at hm
        obtain ⟨z, hz, hzS⟩ := sep_chain hSH (l := p ++ u :: q)
          (List.isChain_split.mpr ⟨hc, hq⟩) (by simpa using hA)
          (by rw [getLast?_app_cons]; exact hqB)
        rcases List.mem_append.mp hz with hz | hz
        · exact hm z (List.mem_append_left _ hz) hzS
        · exact hqS z hz hzS
lemma suf {H : SimpleGraph V} {x y : V}
    (hH : ∀ u v, H.Adj u v ↔ G.Adj u v ∧ s(u, v) ≠ s(x, y))
    {A B S : Finset V} (hSH : Sep H A B S) {p : List V} (hp : (p ++ [x]).IsChain H.Adj)
    (hpA : ∃ a ∈ A, (p ++ [x]).head? = some a) (hpS : ∀ z ∈ p ++ [x], z ∉ S)
    {l : List V} (hl : ABP G A B l) : ∃ m, m <:+ l ∧ ABP H (insert y S) B m := by
  have hH' : ∀ u v, H.Adj u v ↔ G.Adj u v ∧ s(u, v) ≠ s(y, x) := by
    intro u v; rw [Sym2.eq_swap (a := y)]; exact hH u v
  have e : x :: p.reverse = (p ++ [x]).reverse := by simp
  obtain ⟨m, hm, hmA⟩ := pre (x := y) (y := x) (q := p.reverse) hH' (sep_reverse hSH)
    (by rw [e]; exact List.isChain_reverse.mpr (hp.imp fun _ _ h => h.symm))
    (by rw [e, List.getLast?_reverse]; exact hpA)
    (fun z hz => hpS z (by rw [e] at hz; simp at hz ⊢; tauto)) (abp_reverse hl)
  exact ⟨m.reverse, List.reverse_prefix.mp (by simpa using hm), by simpa using abp_reverse hmA⟩
lemma mem_tail_of {c d : List V} {v z : V} (hz : z ∈ d) : z ∈ (c ++ v :: d).tail := by
  cases c <;> simp [hz]
lemma glue {H : SimpleGraph V} (hle : H ≤ G) {x y : V} (hxy : G.Adj x y) {A B S : Finset V}
    (hx : x ∉ S) (hy : y ∉ S) (hSH : Sep H A B S) {k : ℕ} (hk : S.card + 1 = k)
    {P Q : Fin k → List V}
    (hP : ∀ i, ABP H A (insert x S) (P i) ∧ ∀ z ∈ (P i).dropLast, z ∉ insert x S)
    (hPd : ∀ i j, i ≠ j → ∀ z ∈ P i, z ∉ P j)
    (hQ : ∀ j, ABP H (insert y S) B (Q j) ∧ ∀ z ∈ (Q j).tail, z ∉ insert y S)
    (hQd : ∀ i j, i ≠ j → ∀ z ∈ Q i, z ∉ Q j) :
    ∃ R : Fin k → List V, (∀ i, ABP G A B (R i)) ∧ ∀ i j, i ≠ j → ∀ z ∈ R i, z ∉ R j := by
  have hxy' : x ≠ y := G.ne_of_adj hxy
  choose lt hltX hlt using fun i => (hP i).1.2.2.2
  choose hd hhdY hhd using fun j => (hQ j).1.2.2.1
  have hPdec : ∀ i, ∃ a, P i = a ++ [lt i] := fun i => List.getLast?_eq_some_iff.mp (hlt i)
  have hQdec : ∀ j, ∃ d, Q j = hd j :: d := fun j => List.head?_eq_some_iff.mp (hhd j)
  have hltmem : ∀ i, lt i ∈ P i := fun i => List.mem_of_getLast? (hlt i)
  have hhdmem : ∀ j, hd j ∈ Q j := fun j => List.mem_of_head? (hhd j)
  have hPS : ∀ i, ∀ z ∈ P i, z ∈ S → z = lt i := by
    intro i z hz hzS
    obtain ⟨a, ha⟩ := hPdec i
    rw [ha] at hz
    rcases List.mem_append.mp hz with h | h
    · exact absurd (Finset.mem_insert_of_mem hzS)
        ((hP i).2 z (by rw [ha, List.dropLast_concat]; exact h))
    · simpa using h
  have hQS : ∀ j, ∀ z ∈ Q j, z ∈ S → z = hd j := by
    intro j z hz hzS
    obtain ⟨d, hd'⟩ := hQdec j
    rw [hd'] at hz
    rcases List.mem_cons.mp hz with h | h
    · exact h
    · exact absurd (Finset.mem_insert_of_mem hzS) ((hQ j).2 z (by rw [hd']; exact h))
  have meet : ∀ i j, ∀ v ∈ P i, v ∈ Q j → v ∈ S := by
    intro i j v hvP hvQ
    by_contra hvS
    obtain ⟨a, b, hab⟩ := List.append_of_mem hvP
    obtain ⟨c, d, hcd⟩ := List.append_of_mem hvQ
    have h1 : (a ++ [v]).IsChain H.Adj := chain_pre (hP i).1.2.1 ⟨b, by rw [hab]; simp⟩
    have h2 : (v :: d).IsChain H.Adj := (hQ j).1.2.1.suffix ⟨c, hcd.symm⟩
    obtain ⟨a0, ha0, hha0⟩ := (hP i).1.2.2.1
    obtain ⟨b0, hb0, hlb0⟩ := (hQ j).1.2.2.2
    obtain ⟨z, hz, hzS⟩ := sep_chain hSH (List.isChain_split.mpr ⟨h1, h2⟩)
      ⟨a0, ha0, by rw [hab] at hha0; simpa using hha0⟩
      ⟨b0, hb0, by rw [hcd, getLast?_app_cons] at hlb0; rw [getLast?_app_cons]; exact hlb0⟩
    rcases List.mem_append.mp hz with hz | hz
    · exact (hP i).2 z (by rw [hab, List.dropLast_append_cons]; exact List.mem_append_left _ hz)
        (Finset.mem_insert_of_mem hzS)
    · rcases List.mem_cons.mp hz with rfl | hz
      · exact hvS hzS
      · exact (hQ j).2 z (by rw [hcd]; exact mem_tail_of hz) (Finset.mem_insert_of_mem hzS)
  have hdinj : Function.Injective hd := by
    intro j j' h
    by_contra hne
    exact hQd j j' hne (hd j) (hhdmem j) (h ▸ hhdmem j')
  have hY : (insert y S).card = k := by rw [Finset.card_insert_of_notMem hy, hk]
  have hsurj : ∀ w ∈ insert y S, ∃ j, hd j = w := by
    have himg : Finset.univ.image hd = insert y S := by
      apply Finset.eq_of_subset_of_card_le
      · intro w hw
        obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hw
        exact hhdY j
      · rw [Finset.card_image_of_injective _ hdinj, Finset.card_univ, Fintype.card_fin, hY]
    intro w hw
    rw [← himg] at hw
    obtain ⟨j, -, hj⟩ := Finset.mem_image.mp hw
    exact ⟨j, hj⟩
  obtain ⟨f, hf⟩ : ∃ f : V → V, f = fun v => if v = x then y else v := ⟨_, rfl⟩
  have hfx : f x = y := by simp [hf]
  have hfS : ∀ v, v ≠ x → f v = v := by intro v hv; simp [hf, hv]
  have hltS : ∀ i, lt i ≠ x → lt i ∈ S := fun i h =>
    (Finset.mem_insert.mp (hltX i)).resolve_left h
  have hfY : ∀ i, f (lt i) ∈ insert y S := by
    intro i
    by_cases h : lt i = x
    · rw [h, hfx]; exact Finset.mem_insert_self _ _
    · rw [hfS _ h]; exact Finset.mem_insert_of_mem (hltS i h)
  choose σ hσ using fun i => hsurj _ (hfY i)
  have hσinj : Function.Injective σ := by
    intro i i' h
    have h1 : f (lt i) = f (lt i') := by rw [← hσ i, ← hσ i', h]
    have h2 : lt i = lt i' := by
      by_cases ha : lt i = x <;> by_cases hb : lt i' = x
      · rw [ha, hb]
      · rw [ha, hfx, hfS _ hb] at h1; exact absurd (h1 ▸ hltS i' hb) hy
      · rw [hb, hfx, hfS _ ha] at h1; exact absurd (h1.symm ▸ hltS i ha) hy
      · rwa [hfS _ ha, hfS _ hb] at h1
    by_contra hne
    exact hPd i i' hne _ (hltmem i) (h2 ▸ hltmem i')
  obtain ⟨R, hR⟩ : ∃ R : Fin k → List V, R = fun i =>
      if lt i = x then P i ++ Q (σ i) else P i ++ (Q (σ i)).tail := ⟨_, rfl⟩
  have memR : ∀ i z, z ∈ R i → z ∈ P i ∨ z ∈ Q (σ i) := by
    intro i z hz
    rw [hR] at hz
    simp only at hz
    split_ifs at hz
    · exact List.mem_append.mp hz
    · rcases List.mem_append.mp hz with h | h
      · exact Or.inl h
      · exact Or.inr (List.mem_of_mem_tail h)
  have hRabp : ∀ i, ABP G A B (R i) := by
    intro i
    obtain ⟨a, ha⟩ := hPdec i
    obtain ⟨d, hd'⟩ := hQdec (σ i)
    have hPch : (P i).IsChain G.Adj := (hP i).1.2.1.imp fun _ _ h => hle h
    have hQch : (Q (σ i)).IsChain G.Adj := (hQ (σ i)).1.2.1.imp fun _ _ h => hle h
    have hPnd := (hP i).1.1
    have hQnd := (hQ (σ i)).1.1
    obtain ⟨a0, ha0, hha0⟩ := (hP i).1.2.2.1
    obtain ⟨b0, hb0, hlb0⟩ := (hQ (σ i)).1.2.2.2
    rw [ha] at hPch hPnd hha0
    rw [hd'] at hQch hQnd hlb0
    by_cases hx' : lt i = x
    · have hdy : hd (σ i) = y := by rw [hσ i, hx', hfx]
      have hRi : R i = a ++ [lt i] ++ hd (σ i) :: d := by
        rw [hR]; simp only [if_pos hx']; rw [ha, hd']
      rw [hRi]
      refine ⟨?_, ?_, ⟨a0, ha0, by simpa using hha0⟩,
        ⟨b0, hb0, by rw [getLast?_app_cons]; exact hlb0⟩⟩
      · rw [List.nodup_append]
        refine ⟨hPnd, hQnd, ?_⟩
        rintro z hz z' hz' rfl
        have hzS := meet i (σ i) z (by rw [ha]; exact hz) (by rw [hd']; exact hz')
        have := hPS i z (by rw [ha]; exact hz) hzS
        exact hx (by rw [← hx', ← this]; exact hzS)
      · refine hPch.append hQch ?_
        intro u hu w hw
        simp at hu hw
        rw [← hu, ← hw, hx', hdy]; exact hxy
    · have hdl : hd (σ i) = lt i := by rw [hσ i, hfS _ hx']
      have hRi : R i = a ++ lt i :: d := by
        rw [hR]; simp only [if_neg hx']; rw [ha, hd', hdl]; simp
      rw [hdl] at hQch hQnd hlb0
      rw [hRi]
      refine ⟨?_, List.isChain_split.mpr ⟨hPch, hQch⟩, ⟨a0, ha0, by simpa using hha0⟩,
        ⟨b0, hb0, by rw [getLast?_app_cons]; exact hlb0⟩⟩
      have e : a ++ lt i :: d = (a ++ [lt i]) ++ d := by simp
      rw [e, List.nodup_append]
      refine ⟨hPnd, (List.nodup_cons.mp hQnd).2, ?_⟩
      rintro z hz z' hz' rfl
      have hzQ : z ∈ Q (σ i) := by rw [hd', hdl]; exact List.mem_cons_of_mem _ hz'
      have hzS := meet i (σ i) z (by rw [ha]; exact hz) hzQ
      have := hQS (σ i) z hzQ hzS
      rw [hdl] at this
      exact (List.nodup_cons.mp hQnd).1 (this ▸ hz')
  refine ⟨R, hRabp, ?_⟩
  have cross : ∀ i i', i ≠ i' → ∀ z ∈ P i, z ∉ Q (σ i') := by
    intro i i' hii' z h1 h2
    have hzS := meet i (σ i') z h1 h2
    have e1 := hPS i z h1 hzS
    have e2 := hQS (σ i') z h2 hzS
    have hne : lt i ≠ x := fun h => hx (by rw [← h, ← e1]; exact hzS)
    have : hd (σ i) = hd (σ i') := by rw [hσ i, hfS _ hne, ← e1, e2]
    exact hii' (hσinj (hdinj this))
  intro i i' hii' z hz hz'
  rcases memR i z hz with h1 | h1 <;> rcases memR i' z hz' with h2 | h2
  · exact hPd i i' hii' z h1 h2
  · exact cross i i' hii' z h1 h2
  · exact cross i' i (Ne.symm hii') z h2 h1
  · exact hQd (σ i) (σ i') (fun h => hii' (hσinj h)) z h1 h2
lemma step {H : SimpleGraph V} {x y : V} (hle : H ≤ G) (hxy : G.Adj x y)
    (hH : ∀ u v, H.Adj u v ↔ G.Adj u v ∧ s(u, v) ≠ s(x, y))
    (ih : ∀ (A B : Finset V) (k : ℕ), (∀ S, Sep H A B S → k ≤ S.card) →
      ∃ P : Fin k → List V, (∀ i, ABP H A B (P i)) ∧ ∀ i j, i ≠ j → ∀ z ∈ P i, z ∉ P j)
    {A B : Finset V} {k : ℕ} (hsep : ∀ S, Sep G A B S → k ≤ S.card)
    {S : Finset V} (hSH : Sep H A B S) (hSk : S.card < k)
    {p q : List V} (hl0 : ABP G A B (p ++ x :: y :: q)) (hav : ∀ z ∈ p ++ x :: y :: q, z ∉ S) :
    ∃ P : Fin k → List V, (∀ i, ABP G A B (P i)) ∧ ∀ i j, i ≠ j → ∀ z ∈ P i, z ∉ P j := by
  obtain ⟨hnd, hch, hA, hB⟩ := hl0
  have hx : x ∉ S := hav x (by simp)
  have hy : y ∉ S := hav y (by simp)
  have hp : p ++ [x] <+: p ++ x :: y :: q := ⟨y :: q, by simp⟩
  have hs : y :: q <:+ p ++ x :: y :: q := ⟨p ++ [x], by simp⟩
  have hpch : (p ++ [x]).IsChain H.Adj :=
    chain_del hH (chain_pre hch hp) (Or.inl (nodup_aux hnd))
  have hqch : (y :: q).IsChain H.Adj :=
    chain_del hH (hch.suffix hs) (Or.inr (nodup_aux2 hnd))
  have hpre : ∀ l, ABP G A B l → ∃ m, m <+: l ∧ ABP H A (insert x S) m := fun l hl =>
    pre hH hSH hqch (by rw [← getLast?_app_cons p]; simpa using hB)
      (fun z hz => hav z (by simp at hz ⊢; tauto)) hl
  have hsuf : ∀ l, ABP G A B l → ∃ m, m <:+ l ∧ ABP H (insert y S) B m := fun l hl =>
    suf hH hSH hpch (by simpa using hA) (fun z hz => hav z (by simp at hz ⊢; tauto)) hl
  have hXk : k ≤ (insert x S).card := hsep _ (sep_of_pre hpre sep_last)
  have hk : S.card + 1 = k := by rw [Finset.card_insert_of_notMem hx] at hXk; omega
  obtain ⟨P, hP, hPd⟩ := ih A (insert x S) k (fun T hT => hsep T (sep_of_pre hpre hT))
  obtain ⟨Q, hQ, hQd⟩ := ih (insert y S) B k (fun T hT => hsep T (sep_of_suf hsuf hT))
  obtain ⟨P', hP', hP'd⟩ := trim_family hP hPd
  obtain ⟨Q', hQ', hQ'd⟩ := trim_family hQ hQd
  exact glue hle hxy hx hy hSH hk (fun i => ⟨(hP' i).1, (hP' i).2.2⟩) hP'd
    (fun j => ⟨(hQ' j).1, (hQ' j).2.1⟩) hQ'd
theorem menger_aux (G : SimpleGraph V) : ∀ (A B : Finset V) (k : ℕ),
    (∀ S, Sep G A B S → k ≤ S.card) →
    ∃ P : Fin k → List V, (∀ i, ABP G A B (P i)) ∧ ∀ i j, i ≠ j → ∀ x ∈ P i, x ∉ P j := by
  induction G using WellFoundedLT.induction with
  | _ G ih =>
  intro A B k hsep
  by_cases hE : ∃ x y, G.Adj x y
  swap
  · push_neg at hE; exact base hE hsep
  obtain ⟨x, y, hxy⟩ := hE
  obtain ⟨H, hHdef⟩ : ∃ H, H = G.deleteEdges {s(x, y)} := ⟨_, rfl⟩
  have hH : ∀ u v, H.Adj u v ↔ G.Adj u v ∧ s(u, v) ≠ s(x, y) := by
    intro u v; rw [hHdef, deleteEdges_adj]; simp
  have hle : H ≤ G := hHdef ▸ deleteEdges_le _
  have hlt : H < G := lt_of_le_of_ne hle (fun h => ((hH x y).mp (by rw [h]; exact hxy)).2 rfl)
  by_cases hc : ∀ S, Sep H A B S → k ≤ S.card
  · obtain ⟨P, hP, hPd⟩ := ih H hlt A B k hc
    exact ⟨P, fun i => abp_mono hle (hP i), hPd⟩
  · push_neg at hc
    obtain ⟨S, hSH, hSk⟩ := hc
    have hnG : ¬ Sep G A B S := fun h => absurd (hsep S h) (by omega)
    simp only [Sep, not_forall, not_exists, not_and] at hnG
    obtain ⟨l0, hl0, hav⟩ := hnG
    have hnH : ¬ l0.IsChain H.Adj := fun hc => by
      obtain ⟨z, hz, hzS⟩ := hSH l0 ⟨hl0.1, hc, hl0.2.2⟩; exact hav z hz hzS
    obtain ⟨p, u, v, q, rfl, huv, hnuv⟩ := exists_bad l0 hl0.2.1 hnH
    have he : s(u, v) = s(x, y) := by
      by_contra hne; exact hnuv ((hH u v).mpr ⟨huv, hne⟩)
    rcases Sym2.eq_iff.mp he with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] at hl0 hav
    · exact step hle hxy hH (ih H hlt) hsep hSH hSk hl0 hav
    · exact step hle hxy.symm (fun a b => by rw [hH a b, Sym2.eq_swap (a := x) (b := y)])
        (ih H hlt) hsep hSH hSk hl0 hav
theorem menger [DecidableRel G.Adj] (A B : Finset V) (k : ℕ)
    (hsep : ∀ S : Finset V, (∀ l, ABP G A B l → ∃ x ∈ l, x ∈ S) → k ≤ S.card) :
    ∃ P : Fin k → List V, (∀ i, ABP G A B (P i)) ∧
      ∀ i j, i ≠ j → ∀ x ∈ P i, x ∉ P j := by
  exact menger_aux G A B k hsep
theorem menger_trim [DecidableRel G.Adj] (A B : Finset V) (k : ℕ)
    (hsep : ∀ S : Finset V, (∀ l, ABP G A B l → ∃ x ∈ l, x ∈ S) → k ≤ S.card) :
    ∃ P : Fin k → List V, (∀ i, ABP G A B (P i) ∧ (∀ x ∈ (P i).tail, x ∉ A) ∧
        (∀ x ∈ (P i).dropLast, x ∉ B)) ∧
      ∀ i j, i ≠ j → ∀ x ∈ P i, x ∉ P j := by
  obtain ⟨P, hP, hPd⟩ := menger A B k hsep
  exact trim_family hP hPd
variable {c : ℕ} {f : ℕ → V}
variable {H : Finset V}
end OMA.BondyK
end
section
namespace Graph189ExteriorDegreeCycle
open SimpleGraph Finset
noncomputable def exactTwo {V : Type*} [Fintype V] (G : SimpleGraph V) (x : V) : Finset V := by
  classical
  exact univ.filter (fun v => G.dist x v = 2)
end Graph189ExteriorDegreeCycle
end
section
namespace Graph189ExteriorDegreeCycle
open SimpleGraph Finset
open OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1
theorem degree_induce_filter {V : Type*} [Fintype V] {G : SimpleGraph V}
    [DecidableRel G.Adj] (S : Set V) [Fintype S] [DecidablePred (· ∈ S)] (x : S) :
    (G.induce S).degree x = ((G.neighborFinset x.val).filter (fun v => v ∈ S)).card := by
  classical
  let f : S ↪ V := ⟨Subtype.val,Subtype.val_injective⟩
  have same : ((G.induce S).neighborFinset x).map f =
      (G.neighborFinset x.val).filter (fun y => y ∈ S) := by
    ext y
    constructor
    · intro hy
      obtain ⟨u,hu,rfl⟩ := mem_map.mp hy
      exact mem_filter.mpr ⟨(G.mem_neighborFinset _ _).mpr
        (((G.induce S).mem_neighborFinset _ _).mp hu),u.property⟩
    · intro hy
      obtain ⟨he,hs⟩ := mem_filter.mp hy
      exact mem_map.mpr ⟨⟨y,hs⟩,((G.induce S).mem_neighborFinset _ _).mpr
        ((G.mem_neighborFinset _ _).mp he),rfl⟩
  have card := congrArg Finset.card same
  rwa [card_map,(G.induce S).card_neighborFinset_eq_degree] at card
end Graph189ExteriorDegreeCycle
end
section
namespace Graph189
open SimpleGraph Finset
private theorem append_chain {V : Type*} {G : SimpleGraph V} {L R : List V}
    {a b : V} (hl : L.IsChain G.Adj) (hr : R.IsChain G.Adj)
    (ha : L.getLast? = some a) (hb : R.head? = some b) (h : G.Adj a b) :
    (L ++ R).IsChain G.Adj := by
  apply hl.append hr
  intro x hx y hy
  rw [ha] at hx
  rw [hb] at hy
  have hax : a = x := by simpa using hx
  have hby : b = y := by simpa using hy
  exact hax ▸ hby ▸ h
private theorem reverse_chain {V : Type*} {G : SimpleGraph V} {L : List V}
    (h : L.IsChain G.Adj) : L.reverse.IsChain G.Adj :=
  List.isChain_reverse.mpr (h.imp fun _ _ h => h.symm)
private theorem split_at_pair {V : Type*} (l : List V) (i : ℕ) (hi : i + 1 < l.length) :
    ∃ P Q, l = P ++ l[i]'(by omega) :: l[i + 1] :: Q := by
  refine ⟨l.take i, l.drop (i + 2), ?_⟩
  conv_lhs => rw [← List.take_append_drop i l]
  rw [List.drop_eq_getElem_cons (by omega : i < l.length), List.drop_eq_getElem_cons hi]
private theorem trace_of_list {V : Type*} [DecidableEq V] {G : SimpleGraph V} (l : List V)
    (hn : l.Nodup) (hc : l.IsChain G.Adj) (hall : ∀ z : V, z ∈ l) (hne : l ≠ []) :
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian := by
  let p := Walk.ofSupport l hne hc
  have hs : p.support = l := Walk.support_ofSupport hne hc
  exact ⟨_, _, p, (Walk.IsPath.mk' (by rwa [hs])).isHamiltonian_of_mem (fun z => by
    rw [hs]
    exact hall z)⟩
private theorem trace_of_permuted_chain {V : Type*} [DecidableEq V] {G : SimpleGraph V} {l W : List V}
    (hn : l.Nodup) (hall : ∀ z : V, z ∈ l) (h : W.Perm l) (hc : W.IsChain G.Adj)
    (x : V) : ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian := by
  have hm (z : V) : z ∈ W := h.mem_iff.mpr (hall z)
  exact trace_of_list W (h.nodup_iff.mpr hn) hc hm (List.ne_nil_of_mem (hm x))
private theorem augmented_chain_excluding {V : Type*} {G : SimpleGraph V} {l : List V}
    {x y : V} (hc : l.IsChain (G ⊔ edge x y).Adj) (h : x ∉ l ∨ y ∉ l) :
    l.IsChain G.Adj := by
  apply List.isChain_iff_forall_rel_of_append_cons_cons.mpr
  intro a b P Q he
  have ha : a ∈ l := by rw [he]; simp
  have hb : b ∈ l := by rw [he]; simp
  have hab := List.isChain_iff_forall_rel_of_append_cons_cons.mp hc he
  rcases hab with hab | hab
  · exact hab
  · have hr := (edge_adj x y a b).mp hab
    rcases hr.1 with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact (h.elim (fun hn => hn ha) (fun hn => hn hb)).elim
    · exact (h.elim (fun hn => hn hb) (fun hn => hn ha)).elim
private theorem repair_left {V : Type*} {G : SimpleGraph V} {L R : List V}
    {x y u v : V} (hl : L.IsChain G.Adj) (hr : R.IsChain G.Adj)
    (hx : L.getLast? = some x) (hy : R.head? = some y)
    (hxu : G.Adj x u) (hyv : G.Adj y v)
    {P Q : List V} (hcut : L = P ++ u :: v :: Q) :
    ∃ W : List V, W.Perm (L ++ R) ∧ W.IsChain G.Adj := by
  let L₁ := P ++ [u]
  let L₂ := v :: Q
  have hl12 : L = L₁ ++ L₂ := by simpa [L₁,L₂,List.append_assoc] using hcut
  have hl₁ : L₁.IsChain G.Adj := (hl12 ▸ hl).left_of_append
  have hl₂ : L₂.IsChain G.Adj := (hl12 ▸ hl).right_of_append
  have hx₂ : L₂.getLast? = some x := by
    rw [hl12, List.getLast?_append_of_ne_nil _ (by simp [L₂])] at hx
    exact hx
  have hv₂ : L₂.head? = some v := by simp [L₂]
  have hrevH : L₂.reverse.head? = some x := by rwa [List.head?_reverse]
  have hrevL : L₂.reverse.getLast? = some v := by rwa [List.getLast?_reverse]
  have hlast : L₁.getLast? = some u := by simp [L₁]
  refine ⟨L₁ ++ (L₂.reverse ++ R), ?_, ?_⟩
  · apply (((List.reverse_perm L₂).append_right R).append_left L₁).trans
    exact List.Perm.of_eq ((List.append_assoc L₁ L₂ R).symm.trans
      (congrArg (· ++ R) hl12.symm))
  · have hjoin := append_chain (reverse_chain hl₂) hr hrevL hy hyv.symm
    apply append_chain hl₁ hjoin hlast _ hxu.symm
    simp [hrevH]
private theorem repair_right {V : Type*} {G : SimpleGraph V} {L R : List V}
    {x y u v : V} (hl : L.IsChain G.Adj) (hr : R.IsChain G.Adj)
    (hx : L.getLast? = some x) (hy : R.head? = some y)
    (hxu : G.Adj x u) (hyv : G.Adj y v)
    {P Q : List V} (hcut : R = P ++ u :: v :: Q) :
    ∃ W : List V, W.Perm (L ++ R) ∧ W.IsChain G.Adj := by
  have hy' : R.reverse.getLast? = some y := by rwa [List.getLast?_reverse]
  have hx' : L.reverse.head? = some x := by rwa [List.head?_reverse]
  have hcut' : R.reverse = Q.reverse ++ v :: u :: P.reverse := by
    rw [hcut]
    simp [List.reverse_append, List.reverse_cons, List.append_assoc]
  obtain ⟨W, hW, hc⟩ :=
    repair_left (reverse_chain hr) (reverse_chain hl) hy' hx' hyv hxu hcut'
  refine ⟨W, hW.trans ?_, hc⟩
  rw [← List.reverse_append]
  exact List.reverse_perm _
private theorem split_closure {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {x y : V}
    (hd : Fintype.card V ≤ G.degree x + G.degree y + 1)
    (P Q : List V) (hn : (P ++ x :: y :: Q).Nodup)
    (hc : (P ++ x :: y :: Q).IsChain (G ⊔ edge x y).Adj)
    (hall : ∀ z : V, z ∈ P ++ x :: y :: Q) :
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian := by
  classical
  let L := P ++ [x]
  let R := y :: Q
  let l := L ++ R
  have hLRe : l = P ++ x :: y :: Q := by simp [l,L,R,List.append_assoc]
  rw [← hLRe] at hn hc hall
  have hno_x : x ∉ R := by
    intro h
    exact (List.nodup_append.mp hn).2.2 x (by simp [L]) x h rfl
  have hno_y : y ∉ L := by
    intro h
    exact (List.nodup_append.mp hn).2.2 y h y (by simp [R]) rfl
  have hl := augmented_chain_excluding (x := x) (y := y) hc.left_of_append (Or.inr hno_y)
  have hr := augmented_chain_excluding (x := x) (y := y) hc.right_of_append (Or.inl hno_x)
  have hx : L.getLast? = some x := by simp [L]
  have hy : R.head? = some y := by simp [R]
  have hLe : L ≠ [] := by simp [L]
  have hRe : R ≠ [] := by simp [R]
  let s := L.head hLe
  let t := R.getLast hRe
  have hs : L.head? = some s := List.head?_eq_some_head hLe
  have ht : R.getLast? = some t := List.getLast?_eq_some_getLast hRe
  have hst : l.head? = some s := by simp [l,hs]
  have htt : l.getLast? = some t := by simp [l,ht]
  by_cases hxt : G.Adj x t
  · apply trace_of_permuted_chain hn hall ((List.reverse_perm R).append_left L) _ x
    apply append_chain hl (reverse_chain hr) hx _ hxt
    rwa [List.head?_reverse]
  by_cases hys : G.Adj y s
  · apply trace_of_permuted_chain hn hall ((List.reverse_perm L).append_right R) _ x
    apply append_chain (reverse_chain hl) hr _ hy hys.symm
    rwa [List.getLast?_reverse]
  have hlen : l.length = Fintype.card V := by
    rw [← List.toFinset_card_of_nodup hn]
    have he : l.toFinset = univ := by ext z; simp [hall]
    simp [he]
  let I := Fin (l.length - 1)
  let u (i : I) : V := l[i.val]'(by have := i.isLt; omega)
  let v (i : I) : V := l[i.val+1]'(by have := i.isLt; omega)
  let S : Finset I := univ.filter fun i => G.Adj x (u i)
  let T : Finset I := univ.filter fun i => G.Adj y (v i)
  have hS : G.degree x ≤ S.card := by
    have hsub : G.neighborFinset x ⊆ S.image u := by
      intro z hz
      have hzx := (mem_neighborFinset G x z).mp hz
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem (hall z)
      have hjlt : j < l.length - 1 := by
        by_contra! hh
        have hj' : j + 1 = l.length := by omega
        have hz : l[j] = t := by
          have hlne : l ≠ [] := List.ne_nil_of_mem (hall x)
          have hget : l.getLast hlne = t := List.getLast_of_getLast?_eq_some htt
          rw [List.getLast_eq_getElem] at hget
          have he : j = l.length - 1 := by omega
          exact he ▸ hget
        exact hxt (hz ▸ hzx)
      refine mem_image.mpr ⟨⟨j,hjlt⟩, mem_filter.mpr ⟨mem_univ _, ?_⟩, rfl⟩
      exact hzx
    exact (card_le_card hsub).trans card_image_le
  have hT : G.degree y ≤ T.card := by
    have hsub : G.neighborFinset y ⊆ T.image v := by
      intro z hz
      have hzy := (mem_neighborFinset G y z).mp hz
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem (hall z)
      have hj0 : 0 < j := by
        by_contra! hh
        have he : j = 0 := by omega
        have hlne : l ≠ [] := List.ne_nil_of_mem (hall x)
        have hget : l.head hlne = s := List.head_of_head?_eq_some hst
        rw [List.head_eq_getElem] at hget
        subst j
        exact hys (hget ▸ hzy)
      have hjlt : j - 1 < l.length - 1 := by omega
      let i : I := ⟨j - 1, hjlt⟩
      have hi : v i = l[j] := by
        change l[j - 1 + 1]'(by omega) = l[j]
        congr 1
        omega
      exact mem_image.mpr ⟨i, mem_filter.mpr ⟨mem_univ _, hi.symm ▸ hzy⟩, hi⟩
    exact (card_le_card hsub).trans card_image_le
  have hpidx : P.length < l.length - 1 := by rw [hLRe]; simp
  let i₀ : I := ⟨P.length, hpidx⟩
  have hu₀ : u i₀ = x := by
    change (L ++ R)[P.length]'(by simp [L, R]) = x
    rw [List.getElem_append_left (by simp [L]), List.getElem_append_right le_rfl]
    simp
  have hv₀ : v i₀ = y := by
    change (L ++ R)[P.length + 1]'(by simp [L, R]) = y
    rw [List.getElem_append_right (by simp [L])]
    simp [L, R]
  have hout : i₀ ∉ S ∪ T := by
    simp [S,T,hu₀,hv₀]
  have hcap : (S ∪ T).card < l.length - 1 := by
    have hne : S ∪ T ≠ (univ : Finset I) := fun h => hout (h ▸ mem_univ _)
    have hh := card_lt_card (ssubset_univ_iff.mpr hne)
    simpa [I] using hh
  obtain ⟨i, hiS, hiT⟩ : ∃ i, i ∈ S ∧ i ∈ T := by
    by_contra! h
    have hdis : Disjoint S T := disjoint_left.mpr h
    have hcard := card_union_of_disjoint hdis
    omega
  have hxu : G.Adj x (u i) := (mem_filter.mp hiS).2
  have hyv : G.Adj y (v i) := (mem_filter.mp hiT).2
  have hin : i.val ≠ P.length := by
    intro h
    have hi0 : i = i₀ := Fin.ext h
    exact hout (mem_union_left _ (hi0 ▸ hiS))
  have hit := i.isLt
  have hLv : L.length = P.length + 1 := by simp [L]
  rcases lt_or_gt_of_ne hin with hbefore | hafter
  · have hixy : i.val + 1 < L.length := by omega
    obtain ⟨A,B,hAB⟩ := split_at_pair L i.val hixy
    have hu : u i = L[i.val]'(by omega) := List.getElem_append_left (by omega)
    have hv : v i = L[i.val+1] := List.getElem_append_left hixy
    rw [← hu, ← hv] at hAB
    obtain ⟨W, hw, hWc⟩ := repair_left hl hr hx hy hxu hyv hAB
    exact trace_of_permuted_chain hn hall hw hWc x
  · let j := i.val - L.length
    have hlen' : l.length = L.length + R.length := List.length_append
    have hj : j + 1 < R.length := by dsimp [j]; omega
    obtain ⟨A,B,hAB⟩ := split_at_pair R j hj
    have hu : u i = R[j]'(by omega) := List.getElem_append_right (by omega)
    have hv : v i = R[j+1] := by
      unfold v
      change (L ++ R)[i.val+1] = R[j+1]
      rw [List.getElem_append_right (by omega)]
      congr 1
      dsimp [j]
      omega
    rw [← hu, ← hv] at hAB
    obtain ⟨W, hw, hWc⟩ := repair_right hl hr hx hy hxu hyv hAB
    exact trace_of_permuted_chain hn hall hw hWc x
theorem traceable_of_sup_edge {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {x y : V}
    (_hne : x ≠ y) (_hxy : ¬ G.Adj x y)
    (hd : Fintype.card V ≤ G.degree x + G.degree y + 1)
    (hpath : ∃ a b : V, ∃ p : (G ⊔ edge x y).Walk a b, p.IsHamiltonian) :
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian := by
  obtain ⟨a,b,p,hp⟩ := hpath
  let l := p.support
  have hn := hp.isPath.support_nodup
  have hall := hp.mem_support
  have hc := p.isChain_adj_support
  by_cases hG : l.IsChain G.Adj
  · exact trace_of_list l hn hG hall p.support_ne_nil
  obtain ⟨i, hi, hbad⟩ := List.exists_not_getElem_of_not_isChain hG
  obtain ⟨P,Q,he⟩ := split_at_pair l i hi
  have hu : (G ⊔ edge x y).Adj l[i] l[i+1] :=
    List.isChain_iff_forall_rel_of_append_cons_cons.mp hc he
  rcases hu with h | h
  · exact (hbad h).elim
  have hh := (edge_adj x y _ _).mp h
  rcases hh.1 with ⟨hx,hy⟩ | ⟨hx,hy⟩
  · rw [hx,hy] at he
    exact split_closure hd P Q (he ▸ hn) (he ▸ hc) (he ▸ hall)
  · rw [hx,hy] at he
    have hc' : l.IsChain (G ⊔ edge y x).Adj := by simpa only [edge_comm y x] using hc
    exact split_closure (by omega) P Q (he ▸ hn) (he ▸ hc') (he ▸ hall)
end Graph189
end
section
open SimpleGraph
namespace Graph189ExteriorGap
variable {V : Type*} {G : SimpleGraph V} {x y a b : V}
theorem gap_length_of_detour (p : G.Walk x y) (hp : p.IsPath)
    (longest : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → r.length ≤ p.length)
    (A J B : List V) (split : p.support = A ++ J ++ B)
    (q : G.Walk a b) (hq : q.IsPath) (disjoint : List.Disjoint q.support p.support)
    (left : ∀ z∈A.getLast?, G.Adj z a) (right : ∀ z∈B.head?, G.Adj b z) :
    q.support.length ≤ J.length := by
  classical
  let L := (A ++ q.support) ++ B
  have pnd := hp.support_nodup
  have pc := p.isChain_adj_support
  rw [split] at pnd pc disjoint
  have ca := pc.left_of_append.left_of_append
  have cb := pc.right_of_append
  have qsHead : q.support.head? = some a := by
    rw [List.head?_eq_some_head q.support_ne_nil, q.head_support]
  have qsLast : q.support.getLast? = some b := by
    rw [List.getLast?_eq_some_getLast q.support_ne_nil, q.getLast_support]
  have first : (A++q.support).IsChain G.Adj := by
    apply ca.append q.isChain_adj_support
    intro z hz w hw
    rw [qsHead] at hw
    have same : a=w := by simpa using hw
    exact same ▸ left z hz
  have chain : L.IsChain G.Adj := by
    apply first.append cb
    intro z hz w hw
    have last : (A++q.support).getLast? = some b := by
      simp [List.getLast?_append,qsLast]
    rw [last] at hz
    have same : b=z := by simpa using hz
    exact same ▸ right w hw
  have nd : L.Nodup := by
    refine List.Nodup.append ?_ pnd.of_append_right ?_
    · apply List.Nodup.append pnd.of_append_left.of_append_left hq.support_nodup
      rw [List.disjoint_left]
      intro z hzA hzQ
      exact List.disjoint_left.mp disjoint hzQ (by simp [hzA])
    · rw [List.disjoint_left]
      intro z hz hzB
      rcases List.mem_append.mp hz with hzA | hzQ
      · exact List.disjoint_left.mp pnd.disjoint (by simp [hzA]) hzB
      · exact List.disjoint_left.mp disjoint hzQ (by simp [hzB])
  have hn : L≠[] := by simp [L,q.support_ne_nil]
  let r := Walk.ofSupport L hn chain
  have rs : r.support = L := Walk.support_ofSupport hn chain
  have rlen := longest r (Walk.IsPath.mk' (by rwa [rs]))
  have lhs := r.length_support
  have rhs := p.length_support
  rw [rs] at lhs
  rw [split] at rhs
  simp only [L,List.length_append] at lhs rhs
  omega
end Graph189ExteriorGap
end
section
open SimpleGraph
namespace Graph189ExteriorGap
variable {V : Type*} {G : SimpleGraph V} {x y a b : V}
theorem prefix_of_detour (p : G.Walk x y) (hp : p.IsPath)
    (longest : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → r.length ≤ p.length)
    (i : Fin p.support.length) (q : G.Walk a b) (hq : q.IsPath)
    (disjoint : List.Disjoint q.support p.support)
    (contact : G.Adj b p.support[i.val]) : q.support.length ≤ i.val := by
  let L := p.support
  have head : (L.drop i.val).head? = some L[i.val] := by
    simp [List.head?_drop]
  have gap := gap_length_of_detour p hp longest [] (L.take i.val) (L.drop i.val)
    (by simp [L]) q hq disjoint (by simp) (by
      intro z hz
      rw [head] at hz
      have eq : L[i.val] = z := by simpa using hz
      exact eq ▸ contact)
  have small := List.length_take_le i.val L
  omega
theorem suffix_of_detour (p : G.Walk x y) (hp : p.IsPath)
    (longest : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → r.length ≤ p.length)
    (i : Fin p.support.length) (q : G.Walk a b) (hq : q.IsPath)
    (disjoint : List.Disjoint q.support p.support)
    (contact : G.Adj p.support[i.val] a) : i.val + 1 + q.support.length ≤ p.support.length := by
  let L := p.support
  have last : (L.take (i.val+1)).getLast? = some L[i.val] := by
    exact (congrArg List.getLast? (List.take_succ_eq_append_getElem
      (l := L) (i := i.val) i.isLt)).trans List.getLast?_concat
  have gap := gap_length_of_detour p hp longest (L.take (i.val+1)) (L.drop (i.val+1)) []
    (by simp [L]) q hq disjoint (by
      intro z hz
      rw [last] at hz
      have eq : L[i.val] = z := by simpa using hz
      exact eq ▸ contact) (by simp)
  simp only [L,List.length_drop] at gap
  have hi := i.isLt
  omega
theorem interval_of_detour (p : G.Walk x y) (hp : p.IsPath)
    (longest : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → r.length ≤ p.length)
    (i j : Fin p.support.length) (hij : i < j) (q : G.Walk a b) (hq : q.IsPath)
    (disjoint : List.Disjoint q.support p.support)
    (left : G.Adj p.support[i.val] a) (right : G.Adj b p.support[j.val]) :
    i.val+1+q.support.length ≤ j.val := by
  let L := p.support
  let gap := j.val-(i.val+1)
  have ij : i.val+1+gap=j.val := by
    change i.val < j.val at hij
    dsimp [gap]
    omega
  have split : L = L.take (i.val+1) ++ (L.drop (i.val+1)).take gap ++ L.drop j.val := by
    rw [←List.take_add,ij,List.take_append_drop]
  have last : (L.take (i.val+1)).getLast? = some L[i.val] := by
    exact (congrArg List.getLast? (List.take_succ_eq_append_getElem
      (l := L) (i := i.val) i.isLt)).trans List.getLast?_concat
  have head : (L.drop j.val).head? = some L[j.val] := by
    simp [List.head?_drop]
  have bound := gap_length_of_detour p hp longest _ _ _ split q hq disjoint (by
    intro z hz
    rw [last] at hz
    have eq : L[i.val] = z := by simpa using hz
    exact eq ▸ left) (by
    intro z hz
    rw [head] at hz
    have eq : L[j.val] = z := by simpa using hz
    exact eq ▸ right)
  have small := List.length_take_le gap (L.drop (i.val+1))
  omega
end Graph189ExteriorGap
end
section
open SimpleGraph
namespace Graph189ExteriorGap
variable {V : Type*} {G : SimpleGraph V} {x y : V}
theorem omitted_contact_internal (p : G.Walk x y) (hp : p.IsPath)
    (longest : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → r.length ≤ p.length)
    {a : V} (outside : a∉p.support) (i : Fin p.support.length) (contact : G.Adj p.support[i.val] a) :
    0 < i.val ∧ i.val + 1 < p.support.length := by
  let q : G.Walk a a := Walk.nil
  have hq : q.IsPath := by simp [q]
  have hd : List.Disjoint q.support p.support := by simpa [q,List.disjoint_left] using outside
  have h₁ := prefix_of_detour p hp longest i q hq hd contact.symm
  have h₂ := suffix_of_detour p hp longest i q hq hd contact
  simp only [q,Walk.support_nil,List.length_singleton] at h₁ h₂
  omega
theorem omitted_contact_spacing (p : G.Walk x y) (hp : p.IsPath)
    (longest : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → r.length ≤ p.length)
    {a : V} (outside : a∉p.support) (i j : Fin p.support.length) (ordered : i < j)
    (first : G.Adj p.support[i.val] a) (second : G.Adj p.support[j.val] a) :
    i.val+2 ≤ j.val := by
  let q : G.Walk a a := Walk.nil
  have hq : q.IsPath := by simp [q]
  have hd : List.Disjoint q.support p.support := by simpa [q,List.disjoint_left] using outside
  exact interval_of_detour p hp longest i j ordered q hq hd first second.symm
theorem adjacent_omitted_contact_spacing (p : G.Walk x y) (hp : p.IsPath)
    (longest : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → r.length ≤ p.length)
    {a b : V} (ha : a∉p.support) (hb : b∉p.support) (ab : G.Adj a b)
    (i j : Fin p.support.length) (ordered : i < j)
    (first : G.Adj p.support[i.val] a) (second : G.Adj p.support[j.val] b) :
    i.val+3 ≤ j.val := by
  let q : G.Walk a b := Walk.cons ab Walk.nil
  have hq : q.IsPath := Walk.IsPath.mk' (by simp [q,ab.ne])
  have hd : List.Disjoint q.support p.support := by
    rw [List.disjoint_left]
    intro z hz h
    rcases (show z=a ∨ z=b by simpa [q] using hz) with rfl | rfl
    · exact ha h
    · exact hb h
  exact interval_of_detour p hp longest i j ordered q hq hd first second.symm
end Graph189ExteriorGap
end
section
open SimpleGraph Finset
namespace Graph189ExteriorGap
variable {V : Type*} {G : SimpleGraph V} {x y : V}
def crossIndices (A B : Finset ℕ) : Finset ℕ :=
  (A.image (fun i => i-1) ∪ (A∩B).image (fun i => i+1)) ∪ (B \ A)
private theorem card_crossIndices (A B : Finset ℕ) (positive : ∀ i∈A, 0 < i)
    (separated : ∀ i∈A, ∀ j∈B, i=j ∨ i+3 ≤ j ∨ j+3 ≤ i) :
    (crossIndices A B).card = A.card+B.card := by
  have dis₁ : Disjoint (A.image (fun i => i-1)) ((A∩B).image (fun i => i+1)) := by
    rw [Finset.disjoint_left]
    intro t ht hw
    obtain ⟨i,hi,ei⟩ := Finset.mem_image.mp ht
    obtain ⟨j,hj,ej⟩ := Finset.mem_image.mp hw
    have := positive i hi
    rcases separated i hi j (Finset.mem_inter.mp hj).2 with h | h | h <;> omega
  have dis₂ : Disjoint (A.image (fun i => i-1) ∪ (A∩B).image (fun i => i+1)) (B \ A) := by
    rw [Finset.disjoint_left]
    intro t ht hw
    have hb := (Finset.mem_sdiff.mp hw).1
    rcases Finset.mem_union.mp ht with h | h
    · obtain ⟨i,hi,eq⟩ := Finset.mem_image.mp h
      have := positive i hi
      rcases separated i hi t hb with h | h | h <;> omega
    · obtain ⟨i,hi,eq⟩ := Finset.mem_image.mp h
      rcases separated i (Finset.mem_inter.mp hi).1 t hb with h | h | h <;> omega
  have inj : Set.InjOn (fun i : ℕ => i-1) (A : Set ℕ) := by
    intro i hi j hj heq
    change i-1=j-1 at heq
    have := positive i hi
    have := positive j hj
    omega
  have cover : (B \ A) ∪ (A∩B) = B := by ext t; simp; tauto
  have dis : Disjoint (B \ A) (A∩B) := Finset.disjoint_left.mpr
    (fun _ h₁ h₂ => (Finset.mem_sdiff.mp h₁).2 (Finset.mem_inter.mp h₂).1)
  have hc := Finset.card_union_of_disjoint dis
  rw [cover] at hc
  rw [crossIndices,Finset.card_union_of_disjoint dis₂,Finset.card_union_of_disjoint dis₁,
    Finset.card_image_of_injOn inj,Finset.card_image_of_injective _
      (show Function.Injective (fun i : ℕ => i+1) by intro i j h; change i+1=j+1 at h; omega)]
  omega
noncomputable def contactPositions (p : G.Walk x y) (a : V) : Finset ℕ := by
  classical
  exact (Finset.range p.support.length).filter (fun i => G.Adj (p.getVert i) a)
theorem mem_contactPositions (p : G.Walk x y) (a : V) (i : ℕ) :
    i∈contactPositions p a ↔ i < p.support.length ∧ G.Adj (p.getVert i) a := by
  classical
  simp [contactPositions]
theorem get_at (p : G.Walk x y) {i : ℕ} (hi : i < p.support.length) :
    p.support[i] = p.getVert i := (p.getVert_eq_support_getElem (by
      have := p.length_support
      omega)).symm
theorem two_step_metric {a b z : V} (different : a≠b) (missing : ¬G.Adj a b)
    (az : G.Adj a z) (bz : G.Adj b z) : G.dist a b = 2 := by
  have h := SimpleGraph.edist_eq_two_iff.mpr ⟨different,missing,⟨z,az,bz⟩⟩
  simp [SimpleGraph.dist,h]
theorem cross_position_witnesses [DecidableEq V] (p : G.Walk x y) (hp : p.IsPath)
    (longest : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → r.length ≤ p.length)
    {a b : V} (ha : a∉p.support) (hb : b∉p.support) (ab : G.Adj a b) :
    let A := contactPositions p a
    let B := contactPositions p b
    (crossIndices A B).card=A.card+B.card ∧
    (∀ i∈crossIndices A B, i < p.support.length ∧ G.dist a (p.getVert i)=2) := by
  classical
  let A := contactPositions p a
  let B := contactPositions p b
  have inside (i : ℕ) (h : i∈A) : 0 < i ∧ i+1 < p.support.length := by
    obtain ⟨hi,hc⟩ := (mem_contactPositions p a i).mp h
    exact omitted_contact_internal p hp longest ha ⟨i,hi⟩ (by simpa [get_at] using hc)
  have own (i j : ℕ) (hi : i∈A) (hj : j∈A) (lt : i < j) : i+2 ≤ j := by
    obtain ⟨ri,ci⟩ := (mem_contactPositions p a i).mp hi
    obtain ⟨rj,cj⟩ := (mem_contactPositions p a j).mp hj
    exact omitted_contact_spacing p hp longest ha ⟨i,ri⟩ ⟨j,rj⟩ lt
      (by simpa [get_at] using ci) (by simpa [get_at] using cj)
  have separate (i : ℕ) (hi : i∈A) (j : ℕ) (hj : j∈B) : i=j ∨ i+3 ≤ j ∨ j+3 ≤ i := by
    obtain ⟨ri,ci⟩ := (mem_contactPositions p a i).mp hi
    obtain ⟨rj,cj⟩ := (mem_contactPositions p b j).mp hj
    rcases lt_trichotomy i j with lt | same | gt
    · exact Or.inr (Or.inl (adjacent_omitted_contact_spacing p hp longest ha hb ab
        ⟨i,ri⟩ ⟨j,rj⟩ lt (by simpa [get_at] using ci) (by simpa [get_at] using cj)))
    · exact Or.inl same
    · exact Or.inr (Or.inr (adjacent_omitted_contact_spacing p hp longest hb ha ab.symm
        ⟨j,rj⟩ ⟨i,ri⟩ gt (by simpa [get_at] using cj) (by simpa [get_at] using ci)))
  have shell (i : ℕ) (hi : i∈crossIndices A B) : i < p.support.length ∧ G.dist a (p.getVert i)=2 := by
    have different (j : ℕ) : a≠p.getVert j := fun eq => ha (eq ▸ p.getVert_mem_support j)
    have ls := p.length_support
    have via (i j : ℕ) (hpi : i < p.support.length) (hj : j∈A) (no : i∉A)
        (ij : G.Adj (p.getVert i) (p.getVert j)) : G.dist a (p.getVert i)=2 := by
      have hc := ((mem_contactPositions p a j).mp hj).2
      exact two_step_metric (different _) (fun h => no ((mem_contactPositions p a i).mpr ⟨hpi,h.symm⟩)) hc.symm ij
    rcases Finset.mem_union.mp hi with h | h
    · rcases Finset.mem_union.mp h with h | h
      · obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp h
        obtain ⟨pos,back⟩ := inside j hj
        have inrange : j-1 < p.support.length := by omega
        refine ⟨inrange,via (j-1) j inrange hj (fun hi => ?_) ?_⟩
        · have aux := own (j-1) j hi hj (by omega)
          omega
        · have edge := p.adj_getVert_succ (i := j-1) (by omega)
          rwa [show j-1+1=j by omega] at edge
      · obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp h
        have jA := (Finset.mem_inter.mp hj).1
        obtain ⟨_,back⟩ := inside j jA
        refine ⟨back,via (j+1) j back jA (fun hi => ?_) ?_⟩
        · have aux := own j (j+1) jA hi (by omega)
          omega
        · exact (p.adj_getVert_succ (i := j) (by omega)).symm
    · obtain ⟨hB,hA⟩ := Finset.mem_sdiff.mp h
      obtain ⟨ri,ci⟩ := (mem_contactPositions p b i).mp hB
      exact ⟨ri,two_step_metric (different _) (fun h => hA ((mem_contactPositions p a i).mpr ⟨ri,h.symm⟩)) ab ci⟩
  exact ⟨card_crossIndices A B (fun i h => (inside i h).1) separate,shell⟩
theorem cross_positions_le_path_shell [DecidableEq V] (p : G.Walk x y) (hp : p.IsPath)
    (longest : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → r.length ≤ p.length)
    {a b : V} (ha : a∉p.support) (hb : b∉p.support) (ab : G.Adj a b) :
    (contactPositions p a).card + (contactPositions p b).card ≤
      (p.support.toFinset.filter (fun z => G.dist a z=2)).card := by
  classical
  let A := contactPositions p a
  let B := contactPositions p b
  obtain ⟨count,shell⟩ := cross_position_witnesses p hp longest ha hb ab
  change (crossIndices A B).card=A.card+B.card at count
  have inj : Set.InjOn p.getVert ((crossIndices A B : Finset ℕ) : Set ℕ) := by
    intro i hi j hj same
    exact hp.getVert_injOn (by change i ≤ p.length; have := (shell i hi).1; have := p.length_support; omega)
      (by change j ≤ p.length; have := (shell j hj).1; have := p.length_support; omega) same
  have incl : (crossIndices A B).image p.getVert ⊆ p.support.toFinset.filter (fun z => G.dist a z=2) := by
    intro z hz
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hz
    exact Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr (p.getVert_mem_support i),(shell i hi).2⟩
  have bound := Finset.card_le_card incl
  rw [Finset.card_image_of_injOn inj,count] at bound
  exact bound
end Graph189ExteriorGap
end
section
open SimpleGraph Finset
namespace Graph189ExteriorGap
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {x y : V}
theorem contact_card_neighbors (p : G.Walk x y) (hp : p.IsPath) (a : V) :
    (contactPositions p a).card = (G.neighborFinset a ∩ p.support.toFinset).card := by
  classical
  have inj : Set.InjOn p.getVert ((contactPositions p a : Finset ℕ) : Set ℕ) := by
    intro i hi j hj h
    have il := ((mem_contactPositions p a i).mp hi).1
    have jl := ((mem_contactPositions p a j).mp hj).1
    have ls := p.length_support
    exact hp.getVert_injOn (by change i ≤ p.length; omega) (by change j ≤ p.length; omega) h
  have eq : (contactPositions p a).image p.getVert = G.neighborFinset a ∩ p.support.toFinset := by
    ext z
    constructor
    · intro hz
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hz
      have nb := ((mem_contactPositions p a i).mp hi).2.symm
      exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset a _).mpr nb,List.mem_toFinset.mpr (p.getVert_mem_support i)⟩
    · intro hz
      obtain ⟨hadj,hm⟩ := Finset.mem_inter.mp hz
      have hza := ((G.mem_neighborFinset a z).mp hadj).symm
      obtain ⟨i,hi,he⟩ := List.mem_iff_getElem.mp (List.mem_toFinset.mp hm)
      have eql : p.getVert i=z := (get_at p hi).symm.trans he
      exact Finset.mem_image.mpr ⟨i,(mem_contactPositions p a i).mpr ⟨hi,eql ▸ hza⟩,eql⟩
  rw [←eq,Finset.card_image_of_injOn inj]
theorem exterior_contact_degree (p : G.Walk x y) (hp : p.IsPath)
    (longest : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → r.length ≤ p.length)
    {a b : V} (ha : a∉p.support) (hb : b∉p.support) (ab : G.Adj a b)
    {k : ℕ} (quota : (Finset.univ.filter (fun z => G.dist a z=2)).card ≤ k) :
    (G.neighborFinset a ∩ p.support.toFinset).card + G.degree b ≤
      k+1+((G.neighborFinset b \ p.support.toFinset) ∩ G.neighborFinset a).card := by
  classical
  let P := p.support.toFinset
  let A := G.neighborFinset a
  let B := G.neighborFinset b
  let D := B \ P
  let C := D ∩ A
  let X := (D.erase a) \ A
  let Q := P.filter (fun z => G.dist a z=2)
  have acol := cross_positions_le_path_shell p hp longest ha hb ab
  rw [contact_card_neighbors p hp a,contact_card_neighbors p hp b] at acol
  change (A∩P).card+(B∩P).card ≤ Q.card at acol
  have ain : a∈D := Finset.mem_sdiff.mpr ⟨(G.mem_neighborFinset _ _).mpr ab.symm,
    fun h => ha (List.mem_toFinset.mp h)⟩
  have inter : (D.erase a) ∩ A = C := by
    ext z
    simp only [C,Finset.mem_inter,Finset.mem_erase]
    constructor
    · rintro ⟨⟨_,hd⟩,hA⟩
      exact ⟨hd,hA⟩
    · rintro ⟨hd,hA⟩
      exact ⟨⟨fun eq => G.irrefl (eq ▸ (G.mem_neighborFinset a z).mp hA),hd⟩,hA⟩
  have part₁ := Finset.card_sdiff_add_card_inter B P
  have part₂ := Finset.card_erase_add_one ain
  have part₃ := Finset.card_sdiff_add_card_inter (D.erase a) A
  rw [inter] at part₃
  change X.card+C.card=(D.erase a).card at part₃
  have shell (z : V) (hz : z∈X) : G.dist a z=2 := by
    obtain ⟨hD,hA⟩ := Finset.mem_sdiff.mp hz
    obtain ⟨ne,hd⟩ := Finset.mem_erase.mp hD
    have hzB := (Finset.mem_sdiff.mp hd).1
    exact two_step_metric ne.symm (fun hadj => hA ((G.mem_neighborFinset a z).mpr hadj)) ab
      ((G.mem_neighborFinset b z).mp hzB).symm
  have dis : Disjoint Q X := Finset.disjoint_left.mpr (by
    intro z hQ hX
    have dm := (Finset.mem_erase.mp (Finset.mem_sdiff.mp hX).1).2
    exact (Finset.mem_sdiff.mp dm).2 (Finset.mem_filter.mp hQ).1)
  have incl : Q ∪ X ⊆ Finset.univ.filter (fun z => G.dist a z=2) := by
    intro z hz
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩
    rcases Finset.mem_union.mp hz with h | h
    · exact (Finset.mem_filter.mp h).2
    · exact shell z h
  have total := (Finset.card_le_card incl).trans quota
  rw [Finset.card_union_of_disjoint dis] at total
  change D.card+(B∩P).card=B.card at part₁
  change (A∩P).card+B.card ≤ k+1+C.card
  omega
theorem cross_contact_degree (p : G.Walk x y) (hp : p.IsPath)
    (longest : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → r.length ≤ p.length)
    {a b : V} (ha : a∉p.support) (hb : b∉p.support) (ab : G.Adj a b)
    {k : ℕ} (quota : (Finset.univ.filter (fun z => G.dist a z=2)).card ≤ k) :
    (G.neighborFinset a ∩ p.support.toFinset).card + G.degree b ≤
      k+(G.neighborFinset a \ p.support.toFinset).card := by
  classical
  let P := p.support.toFinset
  let A := G.neighborFinset a
  let B := G.neighborFinset b
  let C := (B \ P) ∩ A
  have bound := exterior_contact_degree p hp longest ha hb ab quota
  change (A∩P).card+G.degree b ≤ k+1+C.card at bound
  have absent : b∉C := by
    intro h
    have nb := (Finset.mem_sdiff.mp (Finset.mem_inter.mp h).1).1
    exact G.irrefl ((G.mem_neighborFinset _ _).mp nb)
  have share : insert b C ⊆ A \ P := by
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl | h
    · exact Finset.mem_sdiff.mpr ⟨(G.mem_neighborFinset _ _).mpr ab,
        fun h => hb (List.mem_toFinset.mp h)⟩
    · obtain ⟨hD,hA⟩ := Finset.mem_inter.mp h
      exact Finset.mem_sdiff.mpr ⟨hA,(Finset.mem_sdiff.mp hD).2⟩
  have count := Finset.card_le_card share
  rw [Finset.card_insert_of_notMem absent] at count
  change (A∩P).card+G.degree b ≤ k+(A \ P).card
  omega
theorem half_degree_outside_longest (p : G.Walk x y) (hp : p.IsPath)
    (longest : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → r.length ≤ p.length)
    {a b : V} (ha : a∉p.support) (hb : b∉p.support) (ab : G.Adj a b)
    {k : ℕ} (quota : (Finset.univ.filter (fun z => G.dist a z=2)).card ≤ k)
    (high : k ≤ G.degree b) :
    G.degree a ≤ 2*(G.neighborFinset a \ p.support.toFinset).card := by
  have cross := cross_contact_degree p hp longest ha hb ab quota
  have parts := Finset.card_sdiff_add_card_inter (G.neighborFinset a) p.support.toFinset
  change (G.neighborFinset a).card ≤ 2*(G.neighborFinset a \ p.support.toFinset).card
  omega
end Graph189ExteriorGap
end
section
namespace Graph189ExteriorGap
open SimpleGraph Finset
variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} {x y : V}
theorem single_positions_lt_path_shell (p : G.Walk x y) (hp : p.IsPath)
    (longest : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → r.length ≤ p.length)
    {a : V} (ha : a ∉ p.support) (touch : (contactPositions p a).Nonempty) :
    (contactPositions p a).card + 1 ≤
      (p.support.toFinset.filter (fun v => G.dist a v = 2)).card := by
  classical
  let A := contactPositions p a
  let m := A.max' touch
  have hm : m ∈ A := Finset.max'_mem _ _
  have internal (i : ℕ) (hi : i ∈ A) : 0 < i ∧ i+1 < p.support.length := by
    obtain ⟨ri,ci⟩ := (mem_contactPositions p a i).mp hi
    exact omitted_contact_internal p hp longest ha ⟨i,ri⟩ (by simpa [get_at] using ci)
  have spaced (i j : ℕ) (hi : i ∈ A) (hj : j ∈ A) (lt : i < j) : i+2 ≤ j := by
    obtain ⟨ri,ci⟩ := (mem_contactPositions p a i).mp hi
    obtain ⟨rj,cj⟩ := (mem_contactPositions p a j).mp hj
    exact omitted_contact_spacing p hp longest ha ⟨i,ri⟩ ⟨j,rj⟩ lt
      (by simpa [get_at] using ci) (by simpa [get_at] using cj)
  let B := A.image (fun i => i-1)
  let W := insert (m+1) B
  have different (i : ℕ) : a ≠ p.getVert i := fun eq => ha (eq ▸ p.getVert_mem_support i)
  have ls := p.length_support
  have via (i j : ℕ) (hi : i < p.support.length) (hj : j ∈ A) (no : i ∉ A)
      (edge : G.Adj (p.getVert i) (p.getVert j)) : G.dist a (p.getVert i) = 2 := by
    have c := ((mem_contactPositions p a j).mp hj).2
    exact two_step_metric (different _) (fun h => no ((mem_contactPositions p a i).mpr ⟨hi,h.symm⟩)) c.symm edge
  have valid (i : ℕ) (hi : i ∈ W) : i < p.support.length ∧ G.dist a (p.getVert i) = 2 := by
    rcases mem_insert.mp hi with rfl|h
    · have ht := (internal m hm).2
      refine ⟨ht,via _ m ht hm (fun mem => ?_) ((p.adj_getVert_succ (i:=m) (by omega)).symm)⟩
      have := spaced m (m+1) hm mem (by omega)
      omega
    · obtain ⟨j,hj,rfl⟩ := mem_image.mp h
      obtain ⟨positive,back⟩ := internal j hj
      have lim : j-1 < p.support.length := by omega
      refine ⟨lim,via _ j lim hj (fun mem => ?_) ?_⟩
      · have := spaced (j-1) j mem hj (by omega)
        omega
      · have edge := p.adj_getVert_succ (i:=j-1) (by omega)
        rwa [show j-1+1=j by omega] at edge
  have maxoutside : m+1 ∉ B := by
    intro h
    obtain ⟨i,hi,eq⟩ := mem_image.mp h
    have lim : i ≤ m := Finset.le_max' _ _ hi
    omega
  have predinj : Set.InjOn (fun i : ℕ => i-1) (A : Set ℕ) := by
    intro i hi j hj eq
    have := (internal i hi).1
    have := (internal j hj).1
    change i-1=j-1 at eq
    omega
  have nodeinj : Set.InjOn p.getVert (W : Set ℕ) := by
    intro i hi j hj eq
    exact hp.getVert_injOn (by change i ≤ p.length; have := (valid i hi).1; omega)
      (by change j ≤ p.length; have := (valid j hj).1; omega) eq
  have sub : W.image p.getVert ⊆ p.support.toFinset.filter (fun v => G.dist a v = 2) := by
    intro v hv
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hv
    exact mem_filter.mpr ⟨List.mem_toFinset.mpr (p.getVert_mem_support _),(valid i hi).2⟩
  have count := card_le_card sub
  rw [card_image_of_injOn nodeinj,show W = insert (m+1) B from rfl,card_insert_of_notMem maxoutside,
    show B = A.image (fun i => i-1) from rfl,card_image_of_injOn predinj] at count
  exact count
end Graph189ExteriorGap
end
section
open SimpleGraph Finset
namespace Graph189ExteriorGap
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {x y : V}
theorem adjacent_ambient_degree_sum (p : G.Walk x y) (hp : p.IsPath)
    (longest : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → r.length ≤ p.length)
    {a b : V} (ha : a∉p.support) (hb : b∉p.support) (ab : G.Adj a b)
    {k : ℕ} (quota : (Finset.univ.filter (fun z => G.dist a z=2)).card ≤ k) :
    G.degree a + G.degree b ≤ k+2*(G.neighborFinset a \ p.support.toFinset).card := by
  have cross := cross_contact_degree p hp longest ha hb ab quota
  have parts := Finset.card_sdiff_add_card_inter (G.neighborFinset a) p.support.toFinset
  change (G.neighborFinset a).card + G.degree b ≤ k+2*(G.neighborFinset a \ p.support.toFinset).card
  omega
theorem nonisolated_exterior_half (p : G.Walk x y) (hp : p.IsPath)
    (longest : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → r.length ≤ p.length)
    {a : V} (ha : a∉p.support) (nonisolated : (G.neighborFinset a \ p.support.toFinset).Nonempty)
    {k : ℕ} (quota : (Finset.univ.filter (fun z => G.dist a z=2)).card ≤ k)
    (high : k ≤ G.degree a) (minimum : ∀ v : V, 3 ≤ G.degree v)
    (uniqueLow : ∀ u v : V, G.degree u < k → G.degree v < k → u=v) :
    (∃ b : V, b∉p.support ∧ G.Adj a b ∧ k ≤ G.degree b) ∧
      G.degree a ≤ 2*(G.neighborFinset a \ p.support.toFinset).card := by
  let E := G.neighborFinset a \ p.support.toFinset
  have member (z : V) (hz : z∈E) : z∉p.support ∧ G.Adj a z :=
    ⟨fun h => (Finset.mem_sdiff.mp hz).2 (List.mem_toFinset.mpr h),
      (G.mem_neighborFinset _ _).mp (Finset.mem_sdiff.mp hz).1⟩
  obtain ⟨w,hw⟩ := nonisolated
  obtain ⟨hwo,aw⟩ := member w hw
  have sum := adjacent_ambient_degree_sum p hp longest ha hwo aw quota
  have card : 1 < E.card := by
    change G.degree a + G.degree w ≤ k + 2*E.card at sum
    have := minimum w
    omega
  obtain ⟨s,hs,t,ht,ne⟩ := Finset.one_lt_card.mp card
  have good : ∃ b∈E, k ≤ G.degree b := by
    by_cases highS : k ≤ G.degree s
    · exact ⟨s,hs,highS⟩
    · refine ⟨t,ht,?_⟩
      by_contra! lowT
      exact ne (uniqueLow s t (by omega) lowT)
  obtain ⟨b,hb,highB⟩ := good
  obtain ⟨off,adj⟩ := member b hb
  exact ⟨⟨b,off,adj,highB⟩,half_degree_outside_longest p hp longest ha off adj quota highB⟩
end Graph189ExteriorGap
end
section
open SimpleGraph Finset
namespace Graph189ExteriorGap
variable {V : Type*} {G : SimpleGraph V} {x y : V}
def ExteriorRoute (p : G.Walk x y) (a b : V) (k : ℕ) : Prop :=
  ∃ q : G.Walk a b, q.IsPath ∧ List.Disjoint q.support p.support ∧ k ≤ q.support.length
theorem longest_matched_route_order (p : G.Walk x y) (hp : p.IsPath)
    (longest : ∀ {a b}, ∀ r : G.Walk a b, r.IsPath → r.length ≤ p.length)
    {j middle left right : ℕ} (mark : Fin (j+1) ↪o Fin p.support.length)
    (port : Fin (j+1) → V) (contacts : ∀ i, G.Adj p.support[(mark i).val] (port i))
    (inner : ∀ i : Fin j, ExteriorRoute p (port i.castSucc) (port i.succ) middle)
    (before : ∃ a, ExteriorRoute p a (port 0) left)
    (after : ∃ b, ExteriorRoute p (port (Fin.last j)) b right) :
    left + j*(middle+1) + 1 + right ≤ p.support.length := by
  obtain ⟨a,q,hq,hdis,hlen⟩ := before
  have hfirst := prefix_of_detour p hp longest (mark 0) q hq hdis (contacts 0).symm
  obtain ⟨b,r,hr,hother,hend⟩ := after
  have hlast := suffix_of_detour p hp longest (mark (Fin.last j)) r hr hother (contacts _)
  have spread (i : Fin j) : (mark i.castSucc).val + 1 + middle ≤ (mark i.succ).val := by
    obtain ⟨t,ht,hd,hm⟩ := inner i
    have bound := interval_of_detour p hp longest _ _ (mark.strictMono i.castSucc_lt_succ)
      t ht hd (contacts _) (contacts _).symm
    omega
  have positions : ∀ i : Fin (j+1), left+i.val*(middle+1) ≤ (mark i).val := by
    intro i
    induction i using Fin.induction with
    | zero => simpa using hlen.trans hfirst
    | succ i ih =>
      have step := spread i
      simp only [Fin.val_succ,Fin.val_castSucc,Nat.succ_mul] at ih ⊢
      omega
  have last := positions (Fin.last j)
  simp only [Fin.val_last] at last
  omega
theorem card_outside_add_path [Fintype V] [DecidableEq V] (p : G.Walk x y) (hp : p.IsPath)
    (W : Finset V) (outside : ∀ z∈W, z∉p.support) :
    W.card+p.support.length ≤ Fintype.card V := by
  have dis : Disjoint W p.support.toFinset := Finset.disjoint_left.mpr (by
    intro z hz h
    exact outside z hz (List.mem_toFinset.mp h))
  have bound := (W ∪ p.support.toFinset).card_le_univ
  rw [Finset.card_union_of_disjoint dis,List.toFinset_card_of_nodup hp.support_nodup] at bound
  exact bound
end Graph189ExteriorGap
end
section
open SimpleGraph Finset
namespace Graph189ExteriorGap
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {x y : V}
theorem high_exterior_half (p : G.Walk x y) (hp : p.IsPath)
    (longest : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → r.length ≤ p.length)
    {a : V} (ha : a∉p.support) {k : ℕ}
    (quota : (Finset.univ.filter (fun z => G.dist a z=2)).card ≤ k)
    (high : k ≤ G.degree a) (minimum : ∀ v : V, 3 ≤ G.degree v)
    (uniqueLow : ∀ u v : V, G.degree u < k → G.degree v < k → u=v) :
    (∃ b : V, b∉p.support ∧ G.Adj a b ∧ k ≤ G.degree b) ∧
      G.degree a ≤ 2*(G.neighborFinset a \ p.support.toFinset).card := by
  classical
  apply nonisolated_exterior_half p hp longest ha _ quota high minimum uniqueLow
  by_contra! empty
  have parts := Finset.card_sdiff_add_card_inter (G.neighborFinset a) p.support.toFinset
  rw [empty,Finset.card_empty,zero_add] at parts
  have num := contact_card_neighbors p hp a
  have min := minimum a
  change 3 ≤ (G.neighborFinset a).card at min
  have touch : (contactPositions p a).Nonempty := Finset.card_pos.mp (by omega)
  have shift := single_positions_lt_path_shell p hp longest ha touch
  have sub : p.support.toFinset.filter (fun z => G.dist a z=2) ⊆
      Finset.univ.filter (fun z => G.dist a z=2) := by
    intro z hz
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hz).2⟩
  have size := (Finset.card_le_card sub).trans quota
  change k ≤ (G.neighborFinset a).card at high
  omega
end Graph189ExteriorGap
end
section
namespace Graph189ExteriorDegreeCycle
open SimpleGraph Finset Graph189ExteriorGap
open OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1
private theorem exact_quota {V : Type*} [Fintype V] {G : SimpleGraph V} (a : V) {k : ℕ} (cap : G.distEven a ≤ k+1) :
    (exactTwo G a).card ≤ k := by
  classical
  let T := exactTwo G a
  have missing : a ∉ T := by
    intro h
    have two : G.dist a a=2 := (mem_filter.mp h).2
    simp at two
  have cover : insert a T ⊆ univ.filter (fun z => Even (G.dist a z)) := by
    intro v hv
    refine mem_filter.mpr ⟨mem_univ _,?_⟩
    rcases mem_insert.mp hv with rfl|h
    · simp
    · rw [show G.dist a v=2 from (mem_filter.mp h).2]; decide
  have sz := card_le_card cover
  rw [card_insert_of_notMem missing] at sz
  change T.card+1 ≤ G.distEven a at sz
  change T.card ≤ k
  omega
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
private theorem no_high_off_almost_longest {u v : V} (p : G.Walk u v) (hp : p.IsPath)
    (longest : ∀ {x y}, ∀ r : G.Walk x y, r.IsPath → r.length ≤ p.length)
    (near : Fintype.card V ≤ p.support.length+3)
    (k5 : 5 ≤ G.secondSmallestDegree)
    (cap : ∀ v, G.distEven v ≤ G.secondSmallestDegree+1)
    (minimum : ∀ v, 3 ≤ G.degree v) {x : V} (hx : x ∉ p.support) :
    G.degree x < G.secondSmallestDegree := by
  classical
  by_contra! hi
  have uq (a b : V) (ha : G.degree a < G.secondSmallestDegree) (hb : G.degree b < G.secondSmallestDegree) :
      a=b := by
    by_contra h
    exact (degree_pair (G:=G) a b h).elim (fun h => by omega) (fun h => by omega)
  obtain ⟨_,half⟩ := high_exterior_half p hp longest hx (exact_quota x (cap x)) hi minimum uq
  let T := univ \ p.support.toFinset
  have sz : T.card + p.support.length = Fintype.card V := by
    have h := card_sdiff_add_card_inter (univ : Finset V) p.support.toFinset
    rwa [univ_inter,List.toFinset_card_of_nodup hp.support_nodup,card_univ] at h
  have xin : x ∈ T := mem_sdiff.mpr ⟨mem_univ _,fun h => hx (List.mem_toFinset.mp h)⟩
  have sub : G.neighborFinset x \ p.support.toFinset ⊆ T.erase x := by
    intro y hy
    obtain ⟨edge,off⟩ := mem_sdiff.mp hy
    exact mem_erase.mpr ⟨((G.mem_neighborFinset _ _).mp edge).ne.symm,mem_sdiff.mpr ⟨mem_univ _,off⟩⟩
  have bound := card_le_card sub
  have one := card_erase_add_one xin
  omega
theorem near_longest_has_hamiltonian_low_deletion {u v : V} (p : G.Walk u v) (hp : p.IsPath)
    (longest : ∀ {x y}, ∀ r : G.Walk x y, r.IsPath → r.length ≤ p.length)
    (near : Fintype.card V ≤ p.support.length+3)
    (notTrace : ¬ ∃ x y, ∃ q : G.Walk x y, q.IsHamiltonian)
    (k5 : 5 ≤ G.secondSmallestDegree) (cap : ∀ v, G.distEven v ≤ G.secondSmallestDegree+1)
    (minimum : ∀ v : V, 3 ≤ G.degree v) :
    ∃ z : V, G.degree z < G.secondSmallestDegree ∧
      ∃ x y, ∃ q : (G.induce {a : V | a ≠ z}).Walk x y, q.IsHamiltonian := by
  classical
  obtain ⟨a,ha⟩ : ∃ a, a ∉ p.support := by
    by_contra! covers
    exact notTrace ⟨u,v,p,hp.isHamiltonian_of_mem covers⟩
  have low := no_high_off_almost_longest p hp longest near k5 cap minimum ha
  let S := {z : V | z ≠ a}
  have sub : ∀ x ∈ p.support, x ∈ S := fun z hz eq => ha (eq ▸ hz)
  let q := p.induce S sub
  let f := (Embedding.induce (G:=G) S).toHom
  have mapped : q.map f = p := Walk.map_induce p sub
  have path : q.IsPath := (Walk.isPath_map_iff_of_injective (f:=f) Subtype.val_injective).mp
    (by rw [mapped]; exact hp)
  refine ⟨a,low,_,_,q,path.isHamiltonian_of_mem ?_⟩
  intro z
  have belongs : z.val ∈ p.support := by
    by_contra off
    have zlow := no_high_off_almost_longest p hp longest near k5 cap minimum off
    exact (degree_pair (G:=G) z.val a z.property).elim (fun h => by omega) (fun h => by omega)
  have supp : List.map Subtype.val q.support = p.support := by
    calc
      List.map Subtype.val q.support = (q.map f).support := (Walk.support_map f q).symm
      _ = p.support := congrArg (fun r : G.Walk u v => r.support) mapped
  rw [←supp] at belongs
  obtain ⟨t,ht,eq⟩ := List.mem_map.mp belongs
  exact (Subtype.ext eq : t = z) ▸ ht
end Graph189ExteriorDegreeCycle
end
section
open SimpleGraph Finset
namespace Graph189TerminalLeafClosure
variable {V : Type*}
def terminalAdj (G : SimpleGraph V) (u v : V) : V ⊕ Bool → V ⊕ Bool → Prop
  | .inl a, .inl b => G.Adj a b
  | .inl a, .inr leaf => a = (if leaf then v else u)
  | .inr leaf, .inl a => a = (if leaf then v else u)
  | .inr _, .inr _ => False
def terminalLeaves (G : SimpleGraph V) (u v : V) : SimpleGraph (V ⊕ Bool) where
  Adj := terminalAdj G u v
  symm := by
    constructor
    intro a b h
    cases a <;> cases b
    · exact G.adj_symm h
    · exact h
    · exact h
    · exact h
  loopless := by
    constructor
    intro a
    cases a with
    | inl a => exact G.irrefl
    | inr l => exact id
instance terminalDecidable (G : SimpleGraph V) [DecidableEq V] [DecidableRel G.Adj] (u v : V) :
    DecidableRel (terminalLeaves G u v).Adj := by
  intro a b
  cases a <;> cases b <;> simp only [terminalLeaves,terminalAdj] <;> infer_instance
theorem core_degree_le [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (u v z : V) : G.degree z ≤ (terminalLeaves G u v).degree (.inl z) := by
  classical
  have inc : (G.neighborFinset z).image (Sum.inl : V → V ⊕ Bool) ⊆
      (terminalLeaves G u v).neighborFinset (.inl z) := by
    intro b hb
    obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp hb
    simp only [SimpleGraph.mem_neighborFinset] at hc ⊢
    exact hc
  have h := Finset.card_le_card inc
  rw [Finset.card_image_of_injective _ (fun _ _ h => Sum.inl.inj h)] at h
  exact h
theorem terminalLeaves_sup_edge (G : SimpleGraph V) (u v a b : V) :
    terminalLeaves (G ⊔ edge a b) u v =
      terminalLeaves G u v ⊔ edge (.inl a) (.inl b) := by
  ext x y
  cases x <;> cases y <;> simp [terminalLeaves,terminalAdj,SimpleGraph.edge_adj]
theorem leaf_traceable_of_core_edge [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (u v a b : V) (hne : a≠b) (hab : ¬G.Adj a b)
    (degree : Fintype.card V + 1 ≤ G.degree a + G.degree b)
    (path : ∃ x y, ∃ p : (terminalLeaves (G ⊔ edge a b) u v).Walk x y, p.IsHamiltonian) :
    ∃ x y, ∃ p : (terminalLeaves G u v).Walk x y, p.IsHamiltonian := by
  rw [terminalLeaves_sup_edge] at path
  apply Graph189.traceable_of_sup_edge (G := terminalLeaves G u v) (x := .inl a) (y := .inl b)
  · exact fun h => hne (Sum.inl.inj h)
  · exact hab
  · have ha := core_degree_le G u v a
    have hb := core_degree_le G u v b
    simp only [Fintype.card_sum, Fintype.card_bool]
    omega
  · exact path
end Graph189TerminalLeafClosure
end
section
open SimpleGraph
namespace Graph189TerminalLeafClosure
variable {V : Type*} {G : SimpleGraph V} {u v : V}
theorem neighbor_of_leaf {y : V ⊕ Bool} {l : Bool}
    (h : (terminalLeaves G u v).Adj y (.inr l)) :
    y = .inl (if l then v else u) := by
  cases y with
  | inl y => exact congrArg Sum.inl h
  | inr y => exact False.elim h
theorem leaf_not_interior {a b : V ⊕ Bool} (p : (terminalLeaves G u v).Walk a b)
    (hp : p.IsPath) {i : ℕ} (hpos : 0 < i) (hbefore : i < p.length)
    {l : Bool} (atLeaf : p.getVert i = .inr l) : False := by
  have hi : i-1+1=i := by omega
  have left := p.adj_getVert_succ (i := i-1) (by omega)
  rw [hi,atLeaf] at left
  have right := (p.adj_getVert_succ hbefore).symm
  rw [atLeaf] at right
  have same : p.getVert (i-1) = p.getVert (i+1) :=
    (neighbor_of_leaf left).trans (neighbor_of_leaf right).symm
  have bad : i-1=i+1 := hp.getVert_injOn
      (show i-1 ≤ p.length by omega) (show i+1 ≤ p.length by omega) same
  omega
theorem hamiltonian_leaf_at_end [DecidableEq V] {a b : V ⊕ Bool}
    (p : (terminalLeaves G u v).Walk a b) (hp : p.IsHamiltonian) (l : Bool) :
    a = .inr l ∨ b = .inr l := by
  obtain ⟨i,hi⟩ := hp.getVert_surjective (Sum.inr l)
  by_cases hz : i=0
  · left
    simpa [hz] using hi
  by_cases small : i < p.length
  · exact False.elim (leaf_not_interior p hp.isPath (i := i) (Nat.pos_of_ne_zero hz) small hi)
  · right
    rwa [p.getVert_of_length_le (by omega)] at hi
end Graph189TerminalLeafClosure
end
section
open SimpleGraph
namespace Graph189TerminalLeafClosure
variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} {u v : V}
private theorem strip_oriented
    (p : (terminalLeaves G u v).Walk (.inr false) (.inr true)) (hp : p.IsHamiltonian) :
    ∃ q : G.Walk u v, q.IsHamiltonian := by
  have nonnil : ¬p.Nil := Walk.not_nil_of_ne (by simp)
  have first : p.snd = .inl u := neighbor_of_leaf (p.adj_snd nonnil).symm
  have qnn : ¬p.tail.Nil := Walk.not_nil_of_ne (by rw [first]; simp)
  have last : p.tail.penultimate = .inl v := neighbor_of_leaf (p.tail.adj_penultimate qnn)
  let t := p.tail.dropLast
  have parts : (.inr false) :: (t.support ++ [.inr true]) = p.support := by
    rw [show t.support ++ [.inr true] = p.tail.support from Walk.support_dropLast_concat qnn]
    exact Walk.cons_support_tail nonnil
  have nd := hp.isPath.support_nodup
  rw [←parts] at nd
  have ndf := List.nodup_cons.mp nd
  have core : ∀ z∈t.support, ∃ w : V, z = Sum.inl w := by
    intro z hz
    cases z with
    | inl w => exact ⟨w,rfl⟩
    | inr l =>
      cases l
      · exact (ndf.1 (List.mem_append_left _ hz)).elim
      · exact (List.disjoint_left.mp ndf.2.disjoint hz (by simp)).elim
  let project : V ⊕ Bool → V := Sum.elim id (fun l => if l then v else u)
  let L := t.support.map project
  have hn : L ≠ [] := by simp [L, t.support_ne_nil]
  have chain : L.IsChain G.Adj := by
    apply (List.isChain_map project).2
    apply t.isChain_adj_support.imp_of_mem_imp
    intro a b ha hb hab
    obtain ⟨i,rfl⟩ := core a ha
    obtain ⟨j,rfl⟩ := core b hb
    exact hab
  have nodup : L.Nodup := by
    apply List.Nodup.map_on _ ndf.2.of_append_left
    intro a ha b hb h
    obtain ⟨i,rfl⟩ := core a ha
    obtain ⟨j,rfl⟩ := core b hb
    exact congrArg Sum.inl h
  have all (w : V) : w ∈ L := by
    have hw := hp.mem_support (.inl w)
    rw [←parts] at hw
    have hmem : Sum.inl w ∈ t.support := by simpa using hw
    exact List.mem_map.mpr ⟨.inl w,hmem,rfl⟩
  let q := Walk.ofSupport L hn chain
  have qs : q.support = L := Walk.support_ofSupport hn chain
  have qh : q.IsHamiltonian := (Walk.IsPath.mk' (by rwa [qs])).isHamiltonian_of_mem
    (fun w => by rw [qs]; exact all w)
  have hstart : L.head hn = u := by
    simp [L,List.head_map,t,project,first]
  have hfinish : L.getLast hn = v := by
    simp [L,List.getLast_map,t,project,last]
  exact ⟨q.copy hstart hfinish, fun w => by simpa [Walk.support_copy] using qh w⟩
theorem prescribed_of_leaf_traceable
    (path : ∃ x y, ∃ p : (terminalLeaves G u v).Walk x y, p.IsHamiltonian) :
    ∃ p : G.Walk u v, p.IsHamiltonian := by
  obtain ⟨x,y,p,hp⟩ := path
  rcases hamiltonian_leaf_at_end p hp false with hx | hy
  · subst x
    rcases hamiltonian_leaf_at_end p hp true with hf | hy
    · simp at hf
    · subst y
      exact strip_oriented p hp
  · subst y
    rcases hamiltonian_leaf_at_end p hp true with hx | hf
    · subst x
      apply strip_oriented p.reverse
      intro w
      simpa using hp w
    · simp at hf
end Graph189TerminalLeafClosure
end
section
open SimpleGraph
namespace Graph189TerminalLeafClosure
variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} {u v : V}
def oldEmbedding (G : SimpleGraph V) (u v : V) : G →g terminalLeaves G u v where
  toFun := Sum.inl
  map_rel' := fun h => h
theorem leaf_traceable_of_prescribed {p : G.Walk u v} (hp : p.IsHamiltonian) :
    ∃ x y, ∃ q : (terminalLeaves G u v).Walk x y, q.IsHamiltonian := by
  let h₁ : (terminalLeaves G u v).Adj (.inr false) (.inl u) := rfl
  let h₂ : (terminalLeaves G u v).Adj (.inl v) (.inr true) := rfl
  let q := Walk.cons h₁ ((p.map (oldEmbedding G u v)).concat h₂)
  have qs : q.support = Sum.inr false :: (p.support.map Sum.inl ++ [Sum.inr true]) := by
    simp [q,oldEmbedding]
    intro a ha
    rfl
  have mapped : (p.support.map (Sum.inl : V → V⊕Bool)).Nodup :=
    hp.isPath.support_nodup.map (fun _ _ h => Sum.inl.inj h)
  have nd : q.support.Nodup := by
    rw [qs]
    simp [List.nodup_append',mapped]
  refine ⟨_,_,q,(Walk.IsPath.mk' nd).isHamiltonian_of_mem ?_⟩
  intro w
  rw [qs]
  cases w with
  | inl z => simp [hp.mem_support z]
  | inr l => cases l <;> simp
theorem prescribed_of_sup_edge [Fintype V] [DecidableRel G.Adj] {a b : V}
    (distinct : a≠b) (missing : ¬G.Adj a b)
    (degree : Fintype.card V+1 ≤ G.degree a+G.degree b)
    (path : ∃ p : (G⊔edge a b).Walk u v, p.IsHamiltonian) :
    ∃ p : G.Walk u v, p.IsHamiltonian := by
  obtain ⟨p,hp⟩ := path
  exact prescribed_of_leaf_traceable (leaf_traceable_of_core_edge G u v a b distinct missing degree
    (leaf_traceable_of_prescribed hp))
end Graph189TerminalLeafClosure
end
section
open SimpleGraph
namespace Graph189TerminalLeafClosure
variable {V : Type*} [Fintype V] [DecidableEq V]
theorem prescribed_of_supergraph {G H : SimpleGraph V} [DecidableRel G.Adj] (incl : G ≤ H)
    (degree : ∀ a b, H.Adj a b → ¬G.Adj a b → Fintype.card V+1 ≤ G.degree a+G.degree b)
    {u v : V} (path : ∃ p : H.Walk u v, p.IsHamiltonian) :
    ∃ p : G.Walk u v, p.IsHamiltonian := by
  classical
  suffices all : ∀ J : SimpleGraph V, G ≤ J → J ≤ H → ∃ p : J.Walk u v, p.IsHamiltonian by
    exact all G le_rfl incl
  intro J
  induction J using WellFoundedGT.induction with
  | ind J ih =>
    intro lower upper
    by_cases eq : J=H
    · subst J
      exact path
    have missing : ∃ a b, H.Adj a b ∧ ¬J.Adj a b := by
      by_contra! all
      exact eq (le_antisymm upper fun a b hab => all a b hab)
    obtain ⟨a,b,hab,hnot⟩ := missing
    have hEdge : edge a b ≤ H := by
      intro i j hij
      obtain ⟨h,_⟩ := (edge_adj a b i j).mp hij
      rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact hab
      · exact hab.symm
    have strict : J < J⊔edge a b := by
      apply lt_of_le_of_ne le_sup_left
      intro same
      have key : (J⊔edge a b).Adj a b := Or.inr ((edge_adj _ _ _ _).mpr ⟨Or.inl ⟨rfl,rfl⟩,hab.ne⟩)
      exact hnot (same.symm ▸ key)
    apply prescribed_of_sup_edge hab.ne hnot _ (ih _ strict (lower.trans le_sup_left) (sup_le upper hEdge))
    exact (degree _ _ hab (fun h => hnot (lower h))).trans
      (Nat.add_le_add (degree_le_of_le (v := a) lower) (degree_le_of_le (v := b) lower))
theorem complete_prescribed (u v : V) (hne : u ≠ v) :
    ∃ p : (⊤ : SimpleGraph V).Walk u v, p.IsHamiltonian := by
  classical
  let M := ((Finset.univ.erase u).erase v).toList
  let L := u :: (M ++ [v])
  have nd : L.Nodup := by
    simp [L,M,List.nodup_append',Finset.nodup_toList,hne]
  have chain : L.IsChain (⊤ : SimpleGraph V).Adj := by
    apply List.isChain_iff_forall_rel_of_append_cons_cons.mpr
    intro x y A B eq
    apply (top_adj _ _).mpr
    intro same
    subst y
    rw [eq] at nd
    have tail := nd.of_append_right
    exact (List.nodup_cons.mp tail).1 (by simp)
  have hn : L ≠ [] := by simp [L]
  let p := Walk.ofSupport L hn chain
  have ps : p.support = L := Walk.support_ofSupport hn chain
  have ph : p.IsHamiltonian := (Walk.IsPath.mk' (by rwa [ps])).isHamiltonian_of_mem (by
    intro z
    rw [ps]
    by_cases hzu : z=u
    · simp [L,hzu]
    by_cases hzv : z=v <;> simp [L,M,hzu,hzv])
  have hs : L.head hn = u := by simp [L]
  have he : L.getLast hn = v := by simp [L]
  exact ⟨p.copy hs he, fun z => by simpa [Walk.support_copy] using ph z⟩
end Graph189TerminalLeafClosure
end
section
open Finset SimpleGraph
namespace Graph189RotationExterior
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
private theorem neighbors_in_prefix {x y : V} (p : G.Walk x y) (hp : p.IsPath)
    (maximal : ∀ {a b}, ∀ r : G.Walk a b, r.IsPath → r.length ≤ p.length)
    {L : ℕ} (two : 2 ≤ L) (short : ∀ v (q : G.Walk v v), q.IsCycle → q.length ≤ L) :
    G.neighborFinset x ⊆ (p.support.take L).toFinset := by
  intro v hv
  have edge := (G.mem_neighborFinset _ _).mp hv
  have mem : v ∈ p.support := by
    by_contra miss
    have bound := maximal (p.cons edge.symm) (Walk.IsPath.mk' (by simp [miss,hp.support_nodup]))
    simp at bound
  apply List.mem_toFinset.mpr
  apply (List.mem_take_iff_idxOf_lt mem).mpr
  by_contra! far
  let T := p.takeUntil v mem
  have len : L ≤ T.length := by rwa [p.length_takeUntil mem]
  have cycle : (T.cons edge.symm).IsCycle := by
    apply Walk.isCycle_iff_isPath_tail_and_le_length.mpr
    refine ⟨?_,by simp only [Walk.length_cons]; omega⟩
    rw [Walk.tail_cons]
    exact (Walk.isPath_copy _ _ _).mpr (hp.takeUntil mem)
  have bound := short v _ cycle
  simp only [Walk.length_cons] at bound
  omega
omit [Fintype V] [DecidableRel G.Adj] in
private theorem rotate {x y : V} (p : G.Walk x y) (hp : p.IsPath) {i L : ℕ}
    (inside : i+1 < p.support.length) (near : i+1 ≤ L)
    (pivot : G.Adj x (p.getVert (i+1))) :
    ∃ b, ∃ r : G.Walk (p.getVert i) b, r.IsPath ∧ r.length=p.length ∧
      (r.support.take L).toFinset=(p.support.take L).toFinset := by
  let A := p.support.take (i+1)
  let B := p.support.drop (i+1)
  have split : p.support=A++B := (List.take_append_drop _ _).symm
  have size : A.length=i+1 := by
    change (p.support.take (i+1)).length=i+1
    exact List.length_take_of_le (by omega)
  have last : A.getLast?=some (p.getVert i) := by
    have nearI : i < p.support.length := by omega
    rw [←Graph189ExteriorGap.get_at p nearI]
    exact (congrArg List.getLast? (List.take_succ_eq_append_getElem (l:=p.support) (i:=i) nearI)).trans
      List.getLast?_concat
  have first : A.head?=some x := by
    simp only [A,List.head?_take,show i+1≠0 by omega,if_false]
    rw [List.head?_eq_some_head p.support_ne_nil,p.head_support]
  have startB : B.head?=some (p.getVert (i+1)) := by
    simp only [B,List.head?_drop,List.getElem?_eq_getElem inside,Graph189ExteriorGap.get_at]
  let S := A.reverse++B
  have chain := p.isChain_adj_support
  have nd := hp.support_nodup
  rw [split] at chain nd
  have chainR : A.reverse.IsChain G.Adj := List.isChain_reverse.mpr
    (chain.left_of_append.imp (fun _ _ edge => edge.symm))
  have chainS : S.IsChain G.Adj := by
    apply chainR.append chain.right_of_append
    intro v hv w hw
    rw [List.getLast?_reverse, first] at hv
    rw [startB] at hw
    exact (Option.mem_some_iff.mp hv) ▸ (Option.mem_some_iff.mp hw) ▸ pivot
  have ndS : S.Nodup := List.Nodup.append (by simpa using nd.of_append_left) nd.of_append_right
    (by simpa using nd.disjoint)
  have headS : S.head?=some (p.getVert i) := by simp [S,List.head?_append,last]
  have sNe : S≠[] := by intro empty; simp [empty] at headS
  let r := Walk.ofSupport S sNe chainS
  have supp : r.support=S := Walk.support_ofSupport sNe chainS
  have start : S.head sNe=p.getVert i := by rw [List.head?_eq_some_head sNe] at headS; simpa using headS
  have path : r.IsPath := Walk.IsPath.mk' (by rwa [supp])
  have len : r.length=p.length := by
    have lhs := r.length_support
    have rhs := p.length_support
    rw [supp] at lhs
    rw [split] at rhs
    simp only [S,List.length_append,List.length_reverse] at lhs rhs
    omega
  have sets : (S.take L).toFinset=(p.support.take L).toFinset := by
    have le : A.length ≤ L := size.trans_le near
    have rev : A.reverse.length ≤ L := by simpa using le
    rw [split]
    simp only [S,List.take_append,List.take_of_length_le le,List.take_of_length_le rev,List.length_reverse]
    simp
  exact ⟨_,r.copy start rfl,(Walk.isPath_copy _ _ _).mpr path,by simpa using len,by simpa [supp] using sets⟩
theorem degree_window_at {x y : V} (p : G.Walk x y) (hp : p.IsPath)
    (mx : ∀ {u v}, ∀ q : G.Walk u v, q.IsPath → q.length ≤ p.length)
    {d L : ℕ} (two : 2 ≤ L) (degree : d ≤ G.degree x)
    (short : ∀ v (q : G.Walk v v), q.IsCycle → q.length ≤ L) :
    ∃ B E : Finset V, d ≤ E.card ∧ E⊆B ∧ B.card ≤ L ∧
      ∀ v∈E, G.neighborFinset v⊆B := by
  classical
  let B := (p.support.take L).toFinset
  let N := G.neighborFinset x
  let idx (v : V) := p.support.idxOf v
  let prev (v : V) := p.getVert (idx v-1)
  let E := N.image prev
  have initial : N ⊆ B := neighbors_in_prefix p hp mx two short
  have mem {v : V} (hv : v ∈ N) : v ∈ p.support := List.mem_of_mem_take (List.mem_toFinset.mp (initial hv))
  have range {v : V} (hv : v ∈ N) : idx v < p.support.length := List.idxOf_lt_length_iff.mpr (mem hv)
  have value {v : V} (hv : v ∈ N) : p.getVert (idx v)=v :=
    (Graph189ExteriorGap.get_at p (range hv)).symm.trans (List.getElem_idxOf (range hv))
  have pos {v : V} (hv : v ∈ N) : 0 < idx v := by
    by_contra! zero
    have eq := value hv
    rw [show idx v=0 by omega,Walk.getVert_zero] at eq
    exact ((G.mem_neighborFinset _ _).mp hv).ne eq
  have near {v : V} (hv : v ∈ N) : idx v < L :=
    (List.mem_take_iff_idxOf_lt (mem hv)).mp (List.mem_toFinset.mp (initial hv))
  have inj : Set.InjOn prev (N : Set V) := by
    intro a ha b hb eq
    have pa := pos ha
    have pb := pos hb
    have ra := range ha
    have rb := range hb
    have := p.length_support
    have same : idx a-1=idx b-1 := hp.getVert_injOn
      (by change idx a-1 ≤ p.length; omega) (by change idx b-1 ≤ p.length; omega) eq
    have index : idx a=idx b := by omega
    exact (value ha).symm.trans ((congrArg p.getVert index).trans (value hb))
  have enough : d ≤ E.card := by
    change d ≤ (N.image prev).card
    rw [card_image_of_injOn inj]
    exact degree.trans_eq (G.card_neighborFinset_eq_degree x).symm
  have sub : E ⊆ B := by
    intro v hv
    obtain ⟨w,hw,rfl⟩ := mem_image.mp hv
    let j := idx w-1
    have jw : j < p.support.length := by have := range hw; dsimp [j]; omega
    have jl : j < L := by have := near hw; dsimp [j]; omega
    apply List.mem_toFinset.mpr
    apply List.mem_take_iff_getElem.mpr
    exact ⟨j,lt_min jl jw, Graph189ExteriorGap.get_at p jw⟩
  have constrained (v : V) (hv : v ∈ E) : G.neighborFinset v ⊆ B := by
    obtain ⟨w,hw,rfl⟩ := mem_image.mp hv
    have pp := pos hw
    have len := range hw
    have small := near hw
    have step : idx w-1+1=idx w := by omega
    obtain ⟨b,r,hr,eq,same⟩ := rotate p hp (i:=idx w-1) (L:=L) (by omega) (by omega)
      (by rw [step,value hw]; exact (G.mem_neighborFinset _ _).mp hw)
    have mx' {a b} (s : G.Walk a b) (hs : s.IsPath) : s.length ≤ r.length := (mx s hs).trans_eq eq.symm
    have bound := neighbors_in_prefix r hr mx' two short
    rw [same] at bound
    exact bound
  have lengthB : B.card ≤ L := (List.toFinset_card_le _).trans (List.length_take_le _ _)
  exact ⟨B,E,enough,sub,lengthB,constrained⟩
end Graph189RotationExterior
end
section
open SimpleGraph
namespace Graph189ExteriorGap
variable {V : Type*} {G : SimpleGraph V} {x y a b : V}
theorem splice_support (p : G.Walk x y) (hp : p.IsPath)
    (A J B : List V) (split : p.support = A ++ J ++ B)
    (q : G.Walk a b) (hq : q.IsPath) (disjoint : List.Disjoint q.support p.support)
    (left : ∀ z∈A.getLast?, G.Adj z a) (right : ∀ z∈B.head?, G.Adj b z) :
    ∃ u v, ∃ r : G.Walk u v, r.IsPath ∧ r.support = A ++ q.support ++ B := by
  classical
  let L := (A ++ q.support) ++ B
  have pnd := hp.support_nodup
  have pc := p.isChain_adj_support
  rw [split] at pnd pc disjoint
  have ca := pc.left_of_append.left_of_append
  have cb := pc.right_of_append
  have qsHead : q.support.head? = some a := by
    rw [List.head?_eq_some_head q.support_ne_nil, q.head_support]
  have qsLast : q.support.getLast? = some b := by
    rw [List.getLast?_eq_some_getLast q.support_ne_nil, q.getLast_support]
  have first : (A++q.support).IsChain G.Adj := by
    apply ca.append q.isChain_adj_support
    intro z hz w hw
    rw [qsHead] at hw
    have same : a=w := by simpa using hw
    exact same ▸ left z hz
  have chain : L.IsChain G.Adj := by
    apply first.append cb
    intro z hz w hw
    have last : (A++q.support).getLast? = some b := by
      simp [List.getLast?_append,qsLast]
    rw [last] at hz
    have same : b=z := by simpa using hz
    exact same ▸ right w hw
  have nd : L.Nodup := by
    refine List.Nodup.append ?_ pnd.of_append_right ?_
    · apply List.Nodup.append pnd.of_append_left.of_append_left hq.support_nodup
      rw [List.disjoint_left]
      intro z hzA hzQ
      exact List.disjoint_left.mp disjoint hzQ (by simp [hzA])
    · rw [List.disjoint_left]
      intro z hz hzB
      rcases List.mem_append.mp hz with hzA | hzQ
      · exact List.disjoint_left.mp pnd.disjoint (by simp [hzA]) hzB
      · exact List.disjoint_left.mp disjoint hzQ (by simp [hzB])
  have hn : L≠[] := by simp [L,q.support_ne_nil]
  let r := Walk.ofSupport L hn chain
  have rs : r.support = L := Walk.support_ofSupport hn chain
  exact ⟨_,_,r,Walk.IsPath.mk' (by rwa [rs]),rs⟩
private theorem kept_gap (p : G.Walk x y) (hp : p.IsPath) (t : Fin p.support.length)
    (longest : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → p.support[t.val] ∈ r.support →
      r.length ≤ p.length)
    (A J B : List V) (split : p.support = A ++ J ++ B)
    (kept : p.support[t.val] ∈ A ∨ p.support[t.val] ∈ B)
    (q : G.Walk a b) (hq : q.IsPath) (disjoint : List.Disjoint q.support p.support)
    (left : ∀ z∈A.getLast?, G.Adj z a) (right : ∀ z∈B.head?, G.Adj b z) :
    q.support.length ≤ J.length := by
  obtain ⟨u,v,r,hr,rs⟩ := splice_support p hp A J B split q hq disjoint left right
  have member : p.support[t.val] ∈ r.support := by
    rw [rs]
    rcases kept with h | h <;> simp [h]
  have cmp := longest r hr member
  have pr := p.length_support
  have qr := r.length_support
  rw [split] at pr
  rw [rs] at qr
  simp only [List.length_append] at pr qr
  omega
private theorem mem_kept_suffix {L : List V} {t i : Fin L.length} (hi : i ≤ t) :
    L[t.val] ∈ L.drop i.val := by
  apply List.mem_drop_iff_getElem.mpr
  have le : i.val ≤ t.val := hi
  exact ⟨t.val-i.val,by have := t.isLt; omega,by simp [Nat.add_sub_of_le le]⟩
private theorem mem_kept_prefix {L : List V} {t i : Fin L.length} (hi : t ≤ i) :
    L[t.val] ∈ L.take (i.val+1) := by
  apply List.mem_take_iff_getElem.mpr
  exact ⟨t.val,lt_min (by change t.val ≤ i.val at hi; omega) t.isLt,rfl⟩
theorem protected_prefix_of_detour (p : G.Walk x y) (hp : p.IsPath)
    (t : Fin p.support.length)
    (longest : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → p.support[t.val] ∈ r.support → r.length ≤ p.length)
    (i : Fin p.support.length) (hi : i ≤ t) (q : G.Walk a b) (hq : q.IsPath)
    (disjoint : List.Disjoint q.support p.support)
    (contact : G.Adj b p.support[i.val]) : q.support.length ≤ i.val := by
  let L := p.support
  have head : (L.drop i.val).head? = some L[i.val] := by
    simp [List.head?_drop]
  have gap := kept_gap p hp t longest [] (L.take i.val) (L.drop i.val)
    (by simp [L]) (Or.inr (mem_kept_suffix hi)) q hq disjoint (by simp) (by
      intro z hz
      rw [head] at hz
      have eq : L[i.val] = z := by simpa using hz
      exact eq ▸ contact)
  have small := List.length_take_le i.val L
  omega
theorem protected_suffix_of_detour (p : G.Walk x y) (hp : p.IsPath)
    (t : Fin p.support.length)
    (longest : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → p.support[t.val] ∈ r.support → r.length ≤ p.length)
    (i : Fin p.support.length) (ht : t ≤ i) (q : G.Walk a b) (hq : q.IsPath)
    (disjoint : List.Disjoint q.support p.support)
    (contact : G.Adj p.support[i.val] a) : i.val + 1 + q.support.length ≤ p.support.length := by
  let L := p.support
  have last : (L.take (i.val+1)).getLast? = some L[i.val] := by
    exact (congrArg List.getLast? (List.take_succ_eq_append_getElem
      (l := L) (i := i.val) i.isLt)).trans List.getLast?_concat
  have gap := kept_gap p hp t longest (L.take (i.val+1)) (L.drop (i.val+1)) []
    (by simp [L]) (Or.inl (mem_kept_prefix ht)) q hq disjoint (by
      intro z hz
      rw [last] at hz
      have eq : L[i.val] = z := by simpa using hz
      exact eq ▸ contact) (by simp)
  simp only [L,List.length_drop] at gap
  have ilt := i.isLt
  omega
theorem protected_interval_of_detour (p : G.Walk x y) (hp : p.IsPath)
    (t : Fin p.support.length)
    (longest : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → p.support[t.val] ∈ r.support → r.length ≤ p.length)
    (i j : Fin p.support.length) (hij : i < j) (ht : j ≤ t ∨ t ≤ i) (q : G.Walk a b) (hq : q.IsPath)
    (disjoint : List.Disjoint q.support p.support)
    (left : G.Adj p.support[i.val] a) (right : G.Adj b p.support[j.val]) :
    i.val+1+q.support.length ≤ j.val := by
  let L := p.support
  let gap := j.val-(i.val+1)
  have ij : i.val+1+gap=j.val := by
    change i.val < j.val at hij
    dsimp [gap]
    omega
  have split : L = L.take (i.val+1) ++ (L.drop (i.val+1)).take gap ++ L.drop j.val := by
    rw [←List.take_add,ij,List.take_append_drop]
  have last : (L.take (i.val+1)).getLast? = some L[i.val] := by
    exact (congrArg List.getLast? (List.take_succ_eq_append_getElem
      (l := L) (i := i.val) i.isLt)).trans List.getLast?_concat
  have head : (L.drop j.val).head? = some L[j.val] := by
    simp [List.head?_drop]
  have bound := kept_gap p hp t longest _ _ _ split (ht.elim (fun h => Or.inr (mem_kept_suffix h))
    (fun h => Or.inl (mem_kept_prefix h))) q hq disjoint (by
    intro z hz
    rw [last] at hz
    have eq : L[i.val] = z := by simpa using hz
    exact eq ▸ left) (by
    intro z hz
    rw [head] at hz
    have eq : L[j.val] = z := by simpa using hz
    exact eq ▸ right)
  have small := List.length_take_le gap (L.drop (i.val+1))
  omega
end Graph189ExteriorGap
end
section
open SimpleGraph Finset
namespace Graph189ExteriorGap
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {x y : V}
omit [Fintype V] in
theorem route_of_induced_hamilton (p : G.Walk x y) (K : Finset V)
    (outside : ∀ z∈K, z∉p.support) {a b : K}
    {q : (G.induce (K : Set V)).Walk a b} (hq : q.IsHamiltonian) :
    ExteriorRoute p a.val b.val K.card := by
  let e := SimpleGraph.Embedding.induce (G := G) (K : Set V)
  let r := q.map e.toHom
  refine ⟨r, hq.isPath.map e.injective, ?_, ?_⟩
  · rw [List.disjoint_left]
    intro z hz hp
    change z∈(q.map e.toHom).support at hz
    rw [Walk.support_map] at hz
    obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hz
    exact outside w.val w.property hp
  · change K.card≤(q.map e.toHom).support.length
    rw [Walk.support_map,List.length_map,hq.length_support]
    simp
theorem exterior_hamilton_connected_matching (p : G.Walk x y) (hp : p.IsPath)
    (longest : ∀ {a b}, ∀ r : G.Walk a b, r.IsPath → r.length ≤ p.length)
    (K : Finset V) (size : 1 < K.card) (outside : ∀ z∈K, z∉p.support)
    (hconn : ∀ a b : K, a≠b → ∃ q : (G.induce (K : Set V)).Walk a b, q.IsHamiltonian)
    (marks : Finset (Fin p.support.length)) (nonempty : marks.Nonempty)
    (attach : marks ↪ K) (contacts : ∀ i : marks, G.Adj p.support[i.val.val] (attach i).val) :
    (marks.card+2)*K.card + marks.card ≤ Fintype.card V := by
  classical
  obtain ⟨j,hj⟩ : ∃ j : ℕ, marks.card=j+1 := ⟨marks.card-1, by
    have := Finset.card_pos.mpr nonempty
    omega⟩
  let iso := marks.orderIsoOfFin hj
  let M := marks.orderEmbOfFin hj
  let T := fun i : Fin (j+1) => attach (iso i)
  have touching (i : Fin (j+1)) : G.Adj p.support[(M i).val] (T i).val := contacts (iso i)
  have inj : Function.Injective T := attach.injective.comp iso.injective
  have route (a b : K) (ne : a≠b) : ExteriorRoute p a.val b.val K.card := by
    obtain ⟨q,hq⟩ := hconn a b ne
    exact route_of_induced_hamilton p K outside hq
  have another (w : K) : ∃ z : K, z≠w := by
    obtain ⟨a,ha,b,hb,hab⟩ := Finset.one_lt_card.mp size
    by_cases eq : a=w.val
    · exact ⟨⟨b,hb⟩,fun h => hab (eq.trans (congrArg Subtype.val h).symm)⟩
    · exact ⟨⟨a,ha⟩,fun h => eq (congrArg Subtype.val h)⟩
  have inner (i : Fin j) : ExteriorRoute p (T i.castSucc).val (T i.succ).val K.card :=
    route _ _ (inj.ne (ne_of_lt i.castSucc_lt_succ))
  obtain ⟨a,ha⟩ := another (T 0)
  obtain ⟨b,hb⟩ := another (T (Fin.last j))
  have bound := longest_matched_route_order p hp longest M (fun i => (T i).val) touching inner
    ⟨a.val,route _ _ ha⟩ ⟨b.val,route _ _ hb.symm⟩
  have total := card_outside_add_path p hp K outside
  rw [hj]
  simp only [Nat.mul_add,Nat.mul_one,Nat.add_mul] at bound ⊢
  omega
end Graph189ExteriorGap
end
section
open Finset
namespace Graph189ExteriorGap
variable {L R : Type*} [Fintype L] [DecidableEq L] [DecidableEq R]
theorem hall_at_least (neighbors : L → Finset R) (s : ℕ) (small : s ≤ Fintype.card L)
    (hall : ∀ T : Finset L, T.card ≤ (T.biUnion neighbors).card + (Fintype.card L-s)) :
    ∃ U : Finset L, s ≤ U.card ∧ ∃ f : U ↪ R, ∀ u, f u ∈ neighbors u.val := by
  classical
  let d := Fintype.card L-s
  let choices := fun u : L => (neighbors u).disjSum (Finset.univ : Finset (Fin d))
  have full (T : Finset L) : T.card ≤ (T.biUnion choices).card := by
    by_cases empty : T=∅
    · simp [empty]
    obtain ⟨u,hu⟩ := Finset.nonempty_iff_ne_empty.mpr empty
    have eq : T.biUnion choices = (T.biUnion neighbors).disjSum (Finset.univ : Finset (Fin d)) := by
      ext k
      cases k with
      | inl x => simp [choices]
      | inr y =>
        simp [choices]
        exact ⟨u,hu⟩
    rw [eq,Finset.card_disjSum,Finset.card_univ,Fintype.card_fin]
    exact hall T
  obtain ⟨f,hf,acceptable⟩ := (Finset.all_card_le_biUnion_card_iff_existsInjective' choices).mp full
  let U := (Finset.univ : Finset L).filter (fun u => ∃ r : R, f u = Sum.inl r)
  have real (u : U) : ∃ r : R, f u.val = Sum.inl r := (Finset.mem_filter.mp u.property).2
  let g := fun u : U => (real u).choose
  have hg (u : U) : f u.val = Sum.inl (g u) := (real u).choose_spec
  have gi : Function.Injective g := by
    intro u v eq
    apply Subtype.ext
    apply hf
    exact (hg u).trans ((congrArg Sum.inl eq).trans (hg v).symm)
  let D := (Finset.univ : Finset L) \ U
  have dummy (u : D) : ∃ i : Fin d, f u.val = Sum.inr i := by
    cases eq : f u.val with
    | inr j => exact ⟨j,rfl⟩
    | inl r => exact ((Finset.mem_sdiff.mp u.property).2 (Finset.mem_filter.mpr
        ⟨Finset.mem_univ _,r,eq⟩)).elim
  let index := fun u : D => (dummy u).choose
  have di : Function.Injective index := by
    intro u v eq
    apply Subtype.ext
    apply hf
    exact (dummy u).choose_spec.trans ((congrArg Sum.inr eq).trans (dummy v).choose_spec.symm)
  have cap := Fintype.card_le_of_injective index di
  change Fintype.card D ≤ Fintype.card (Fin d) at cap
  simp only [Fintype.card_coe,Fintype.card_fin] at cap
  have part := Finset.card_sdiff_add_card_inter (Finset.univ : Finset L) U
  simp only [Finset.univ_inter,Finset.card_univ] at part
  change D.card+U.card=Fintype.card L at part
  refine ⟨U,by dsimp [d] at cap; omega,⟨g,gi⟩,?_⟩
  intro u
  have spec := acceptable u.val
  rw [hg] at spec
  simpa [choices] using spec
theorem hall_on_dense_vertices (neighbors : L → Finset R) (s : ℕ)
    (U : Finset L) (size : U.card=s) (degree : ∀ u∈U, s ≤ (neighbors u).card) :
    ∃ f : U ↪ R, ∀ u, f u ∈ neighbors u.val := by
  classical
  let links := fun u : U => neighbors u.val
  have h (T : Finset U) : T.card ≤ (T.biUnion links).card := by
    by_cases empty : T=∅
    · simp [empty]
    obtain ⟨u,hu⟩ := Finset.nonempty_iff_ne_empty.mpr empty
    have subset : links u ⊆ T.biUnion links := by
      intro z hz
      exact Finset.mem_biUnion.mpr ⟨u,hu,hz⟩
    have small : T.card ≤ U.card := by simpa using T.card_le_univ
    exact (small.trans (size.le.trans (degree u.val u.property))).trans (Finset.card_le_card subset)
  obtain ⟨f,hi,good⟩ := (Finset.all_card_le_biUnion_card_iff_existsInjective' links).mp h
  exact ⟨⟨f,hi⟩,good⟩
end Graph189ExteriorGap
end
section
open Finset SimpleGraph
namespace Graph189ExteriorAttachment
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {x y : V}
theorem marks_of_many_neighbors (p : G.Walk x y) (W : Finset V) (j : ℕ)
    (size : j ≤ W.card)
    (rows : ∀ w ∈ W, j ≤ ((univ : Finset (Fin p.support.length)).filter
      (fun i => G.Adj p.support[i.val] w)).card) :
    ∃ marks : Finset (Fin p.support.length), marks.card = j ∧
      ∃ attach : marks ↪ W, ∀ i : marks, G.Adj p.support[i.val.val] (attach i).val := by
  classical
  obtain ⟨U,uw,us⟩ := exists_subset_card_eq size
  let N (w : V) := (univ : Finset (Fin p.support.length)).filter (fun i => G.Adj p.support[i.val] w)
  obtain ⟨f,edges⟩ := Graph189ExteriorGap.hall_on_dense_vertices N j U us (fun w hw => rows w (uw hw))
  let M := (univ : Finset U).image f
  let f' (u : U) : M := ⟨f u,mem_image_of_mem _ (mem_univ _)⟩
  have bij : Function.Bijective f' := by
    constructor
    · intro a b eq; exact f.injective (congrArg Subtype.val eq)
    · intro m
      obtain ⟨u,_,eq⟩ := mem_image.mp m.property
      exact ⟨u,Subtype.ext eq⟩
  let equiv := Equiv.ofBijective f' bij
  let inc : U ↪ W := ⟨fun u => ⟨u.val,uw u.property⟩,
    fun _ _ eq => Subtype.ext (congrArg (fun w : W => w.val) eq)⟩
  have card : M.card = U.card := by simpa using Fintype.card_congr equiv.symm
  refine ⟨M,card.trans us,equiv.symm.toEmbedding.trans inc,?_⟩
  intro m
  have eq : f (equiv.symm m) = m.val := congrArg Subtype.val (equiv.apply_symm_apply m)
  have edge := (mem_filter.mp (edges (equiv.symm m))).2
  rw [eq] at edge
  exact edge
end Graph189ExteriorAttachment
end
section
open SimpleGraph Finset
namespace Graph189ExteriorGap
variable {V : Type*} {G : SimpleGraph V} {x y : V}
theorem protected_matched_route_order (p : G.Walk x y) (hp : p.IsPath)
    (t : Fin p.support.length)
    (longest : ∀ {a b}, ∀ r : G.Walk a b, r.IsPath → p.support[t.val] ∈ r.support →
      r.length ≤ p.length)
    {j m : ℕ} (mark : Fin (j+1) ↪o Fin p.support.length)
    (port : Fin (j+1) → V) (contacts : ∀ i, G.Adj p.support[(mark i).val] (port i))
    (inner : ∀ i : Fin j, ExteriorRoute p (port i.castSucc) (port i.succ) m)
    (before : ∃ a, ExteriorRoute p a (port 0) m)
    (after : ∃ b, ExteriorRoute p (port (Fin.last j)) b m) :
    (j+1)*(m+1) ≤ p.support.length := by
  let pos (i : Fin (j+1)) := (mark i).val + if t < mark i then m else 0
  have first : m ≤ pos 0 := by
    by_cases h : t < mark 0
    · simp [pos,h]
    obtain ⟨a,q,hq,dis,order⟩ := before
    have bound := protected_prefix_of_detour p hp t longest (mark 0) (le_of_not_gt h)
      q hq dis (contacts 0).symm
    simpa [pos,h] using order.trans bound
  have step (i : Fin j) : pos i.castSucc + (m+1) ≤ pos i.succ := by
    have lt := mark.strictMono i.castSucc_lt_succ
    by_cases left : t < mark i.castSucc
    · obtain ⟨q,hq,dis,order⟩ := inner i
      have bound := protected_interval_of_detour p hp t longest _ _ lt (Or.inr left.le)
        q hq dis (contacts _) (contacts _).symm
      simp only [pos,if_pos left,if_pos (left.trans lt)]
      omega
    by_cases right : t < mark i.succ
    · simp only [pos,if_neg left,if_pos right]
      change (mark i.castSucc).val < (mark i.succ).val at lt
      omega
    obtain ⟨q,hq,dis,order⟩ := inner i
    have bound := protected_interval_of_detour p hp t longest _ _ lt (Or.inl (le_of_not_gt right))
      q hq dis (contacts _) (contacts _).symm
    simp only [pos,if_neg left,if_neg right]
    omega
  have positions (i : Fin (j+1)) : m+i.val*(m+1) ≤ pos i := by
    induction i using Fin.induction with
    | zero => simpa using first
    | succ i ih =>
      have hs := step i
      simp only [Fin.val_succ,Fin.val_castSucc,Nat.succ_mul] at ih ⊢
      omega
  have finish : pos (Fin.last j)+1 ≤ p.support.length := by
    by_cases h : t < mark (Fin.last j)
    · obtain ⟨b,q,hq,dis,order⟩ := after
      have bound := protected_suffix_of_detour p hp t longest _ h.le q hq dis (contacts _)
      simp only [pos,if_pos h]
      omega
    · simpa [pos,h] using (mark (Fin.last j)).isLt
  have last := positions (Fin.last j)
  simp only [Fin.val_last,Nat.succ_mul] at last ⊢
  omega
theorem protected_hamilton_connected_matching [Fintype V] [DecidableEq V] (p : G.Walk x y) (hp : p.IsPath)
    (t : Fin p.support.length)
    (longest : ∀ {a b}, ∀ r : G.Walk a b, r.IsPath → p.support[t.val] ∈ r.support → r.length ≤ p.length)
    (K : Finset V) (size : 1 < K.card) (outside : ∀ z∈K, z∉p.support)
    (hconn : ∀ a b : K, a≠b → ∃ q : (G.induce (K : Set V)).Walk a b, q.IsHamiltonian)
    (marks : Finset (Fin p.support.length)) (nonempty : marks.Nonempty)
    (attach : marks ↪ K) (contacts : ∀ i : marks, G.Adj p.support[i.val.val] (attach i).val) :
    (marks.card+1)*K.card + marks.card ≤ Fintype.card V := by
  classical
  obtain ⟨j,hj⟩ : ∃ j : ℕ, marks.card=j+1 := ⟨marks.card-1, by
    have := Finset.card_pos.mpr nonempty
    omega⟩
  let iso := marks.orderIsoOfFin hj
  let M := marks.orderEmbOfFin hj
  let T := fun i : Fin (j+1) => attach (iso i)
  have touching (i : Fin (j+1)) : G.Adj p.support[(M i).val] (T i).val := contacts (iso i)
  have inj : Function.Injective T := attach.injective.comp iso.injective
  have route (a b : K) (ne : a≠b) : ExteriorRoute p a.val b.val K.card := by
    obtain ⟨q,hq⟩ := hconn a b ne
    exact route_of_induced_hamilton p K outside hq
  have another (w : K) : ∃ z : K, z≠w := by
    obtain ⟨a,ha,b,hb,hab⟩ := Finset.one_lt_card.mp size
    by_cases eq : a=w.val
    · exact ⟨⟨b,hb⟩,fun h => hab (eq.trans (congrArg Subtype.val h).symm)⟩
    · exact ⟨⟨a,ha⟩,fun h => eq (congrArg Subtype.val h)⟩
  have inner (i : Fin j) : ExteriorRoute p (T i.castSucc).val (T i.succ).val K.card :=
    route _ _ (inj.ne (ne_of_lt i.castSucc_lt_succ))
  obtain ⟨a,ha⟩ := another (T 0)
  obtain ⟨b,hb⟩ := another (T (Fin.last j))
  have bound := protected_matched_route_order p hp t longest M (fun i => (T i).val) touching inner
    ⟨a.val,route _ _ ha⟩ ⟨b.val,route _ _ hb.symm⟩
  have total := card_outside_add_path p hp K outside
  rw [hj]
  simp only [Nat.mul_add,Nat.mul_one,Nat.add_mul,Nat.one_mul] at bound ⊢
  omega
end Graph189ExteriorGap
end
section
open SimpleGraph Finset
namespace Graph189ExteriorGap
variable {V : Type*} {G : SimpleGraph V} {x y : V}
theorem protected_contact_internal (p : G.Walk x y) (hp : p.IsPath)
    (t : Fin p.support.length)
    (longest : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → p.support[t.val] ∈ r.support → r.length ≤ p.length)
    {a : V} (outside : a∉p.support) (i : Fin p.support.length) (contact : G.Adj p.support[i.val] a) :
    0 < i.val ∧ i.val + 1 < p.support.length := by
  let q : G.Walk a a := Walk.nil
  have hq : q.IsPath := by simp [q]
  have hd : List.Disjoint q.support p.support := by simpa [q,List.disjoint_left] using outside
  constructor
  · by_contra! zero
    have le : i ≤ t := by change i.val ≤ t.val; omega
    have bound := protected_prefix_of_detour p hp t longest i le q hq hd contact.symm
    simp only [q,Walk.support_nil,List.length_singleton] at bound
    omega
  · by_contra! last
    have le : t ≤ i := by change t.val ≤ i.val; have := t.isLt; omega
    have bound := protected_suffix_of_detour p hp t longest i le q hq hd contact
    simp only [q,Walk.support_nil,List.length_singleton] at bound
    omega
theorem protected_contact_spacing (p : G.Walk x y) (hp : p.IsPath)
    (t : Fin p.support.length)
    (longest : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → p.support[t.val] ∈ r.support → r.length ≤ p.length)
    {a : V} (outside : a∉p.support) (i j : Fin p.support.length) (ordered : i < j)
    (first : G.Adj p.support[i.val] a) (second : G.Adj p.support[j.val] a) :
    i.val+2 ≤ j.val := by
  let q : G.Walk a a := Walk.nil
  have hq : q.IsPath := by simp [q]
  have hd : List.Disjoint q.support p.support := by simpa [q,List.disjoint_left] using outside
  by_contra! close
  have le : j ≤ t ∨ t ≤ i := by
    change j.val ≤ t.val ∨ t.val ≤ i.val
    change i.val < j.val at ordered
    omega
  have h := protected_interval_of_detour p hp t longest i j ordered le q hq hd first second.symm
  simp only [q,Walk.support_nil,List.length_singleton] at h
  omega
theorem protected_cross_spacing (p : G.Walk x y) (hp : p.IsPath)
    (t : Fin p.support.length)
    (longest : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → p.support[t.val] ∈ r.support → r.length ≤ p.length)
    {a b : V} (ha : a∉p.support) (hb : b∉p.support) (ab : G.Adj a b)
    (i j : Fin p.support.length) (ordered : i < j)
    (first : G.Adj p.support[i.val] a) (second : G.Adj p.support[j.val] b) :
    i.val+3 ≤ j.val ∨ i.val+1=t.val ∧ t.val+1=j.val := by
  let q : G.Walk a b := Walk.cons ab Walk.nil
  have hq : q.IsPath := Walk.IsPath.mk' (by simp [q,ab.ne])
  have hd : List.Disjoint q.support p.support := by
    rw [List.disjoint_left]
    intro z hz h
    rcases (show z=a ∨ z=b by simpa [q] using hz) with rfl | rfl
    · exact ha h
    · exact hb h
  by_cases le : j ≤ t ∨ t ≤ i
  · left
    exact protected_interval_of_detour p hp t longest i j ordered le q hq hd first second.symm
  · change ¬(j.val ≤ t.val ∨ t.val ≤ i.val) at le
    omega
private theorem card_protected_cross (A B : Finset ℕ) (t : ℕ) (positive : ∀ i∈A, 0 < i)
    (separated : ∀ i∈A, ∀ j∈B, i=j ∨ i+3 ≤ j ∨ j+3 ≤ i ∨ (i+1=t ∧ t+1=j) ∨ (j+1=t ∧ t+1=i)) :
    A.card+B.card ≤ (crossIndices A B).card+1 := by
  have overlap : ((A.image (fun i => i-1)) ∩ ((A∩B).image (fun i => i+1))) ⊆ {t} := by
    intro v hv
    obtain ⟨i,hi,ei⟩ := mem_image.mp (mem_inter.mp hv).1
    obtain ⟨j,hj,ej⟩ := mem_image.mp (mem_inter.mp hv).2
    have := positive i hi
    have := separated i hi j (mem_inter.mp hj).2
    apply mem_singleton.mpr
    omega
  have loss := Finset.card_le_card overlap
  rw [card_singleton] at loss
  have dis₂ : Disjoint (A.image (fun i => i-1) ∪ (A∩B).image (fun i => i+1)) (B \ A) := by
    rw [Finset.disjoint_left]
    intro t ht hw
    have hb := (Finset.mem_sdiff.mp hw).1
    rcases Finset.mem_union.mp ht with h | h
    · obtain ⟨i,hi,eq⟩ := Finset.mem_image.mp h
      have := positive i hi
      have := separated i hi t hb
      omega
    · obtain ⟨i,hi,eq⟩ := Finset.mem_image.mp h
      have := separated i (Finset.mem_inter.mp hi).1 t hb
      omega
  have inj : Set.InjOn (fun i : ℕ => i-1) (A : Set ℕ) := by
    intro i hi j hj heq
    change i-1=j-1 at heq
    have := positive i hi
    have := positive j hj
    omega
  have cover : (B \ A) ∪ (A∩B) = B := by ext t; simp; tauto
  have dis : Disjoint (B \ A) (A∩B) := Finset.disjoint_left.mpr
    (fun _ h₁ h₂ => (Finset.mem_sdiff.mp h₁).2 (Finset.mem_inter.mp h₂).1)
  have hc := Finset.card_union_of_disjoint dis
  rw [cover] at hc
  have total := card_union_add_card_inter (A.image (fun i => i-1)) ((A∩B).image (fun i => i+1))
  rw [card_image_of_injOn inj,card_image_of_injective _
    (show Function.Injective (fun i : ℕ => i+1) by intro i j h; change i+1=j+1 at h; omega)] at total
  rw [crossIndices,card_union_of_disjoint dis₂]
  omega
theorem protected_cross_indices [DecidableEq V] (p : G.Walk x y) (hp : p.IsPath)
    (t : Fin p.support.length)
    (longest : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → p.support[t.val] ∈ r.support → r.length ≤ p.length)
    {a b : V} (ha : a∉p.support) (hb : b∉p.support) (ab : G.Adj a b) :
    ((contactPositions p a).card + (contactPositions p b).card ≤
      (crossIndices (contactPositions p a) (contactPositions p b)).card+1) ∧
      ∀ i ∈ crossIndices (contactPositions p a) (contactPositions p b),
        i < p.support.length ∧ G.dist a (p.getVert i)=2 := by
  classical
  let A := contactPositions p a
  let B := contactPositions p b
  have inside (i : ℕ) (h : i∈A) : 0 < i ∧ i+1 < p.support.length := by
    obtain ⟨hi,hc⟩ := (mem_contactPositions p a i).mp h
    exact protected_contact_internal p hp t longest ha ⟨i,hi⟩ (by simpa [get_at] using hc)
  have own (i j : ℕ) (hi : i∈A) (hj : j∈A) (lt : i < j) : i+2 ≤ j := by
    obtain ⟨ri,ci⟩ := (mem_contactPositions p a i).mp hi
    obtain ⟨rj,cj⟩ := (mem_contactPositions p a j).mp hj
    exact protected_contact_spacing p hp t longest ha ⟨i,ri⟩ ⟨j,rj⟩ lt
      (by simpa [get_at] using ci) (by simpa [get_at] using cj)
  have separate (i : ℕ) (hi : i∈A) (j : ℕ) (hj : j∈B) :
      i=j ∨ i+3 ≤ j ∨ j+3 ≤ i ∨ (i+1=t.val ∧ t.val+1=j) ∨ (j+1=t.val ∧ t.val+1=i) := by
    obtain ⟨ri,ci⟩ := (mem_contactPositions p a i).mp hi
    obtain ⟨rj,cj⟩ := (mem_contactPositions p b j).mp hj
    rcases lt_trichotomy i j with lt | same | gt
    · have h := protected_cross_spacing p hp t longest ha hb ab ⟨i,ri⟩ ⟨j,rj⟩ lt
        (by simpa [get_at] using ci) (by simpa [get_at] using cj)
      change i+3 ≤ j ∨ i+1=t.val ∧ t.val+1=j at h
      tauto
    · exact Or.inl same
    · have h := protected_cross_spacing p hp t longest hb ha ab.symm ⟨j,rj⟩ ⟨i,ri⟩ gt
        (by simpa [get_at] using cj) (by simpa [get_at] using ci)
      change j+3 ≤ i ∨ j+1=t.val ∧ t.val+1=i at h
      tauto
  have shell (i : ℕ) (hi : i∈crossIndices A B) : i < p.support.length ∧ G.dist a (p.getVert i)=2 := by
    have different (j : ℕ) : a≠p.getVert j := fun eq => ha (eq ▸ p.getVert_mem_support j)
    have ls := p.length_support
    have via (i j : ℕ) (hpi : i < p.support.length) (hj : j∈A) (no : i∉A)
        (ij : G.Adj (p.getVert i) (p.getVert j)) : G.dist a (p.getVert i)=2 := by
      have hc := ((mem_contactPositions p a j).mp hj).2
      exact two_step_metric (different _) (fun h => no ((mem_contactPositions p a i).mpr ⟨hpi,h.symm⟩)) hc.symm ij
    rcases Finset.mem_union.mp hi with h | h
    · rcases Finset.mem_union.mp h with h | h
      · obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp h
        obtain ⟨pos,back⟩ := inside j hj
        have inrange : j-1 < p.support.length := by omega
        refine ⟨inrange,via (j-1) j inrange hj (fun hi => ?_) ?_⟩
        · have aux := own (j-1) j hi hj (by omega)
          omega
        · have edge := p.adj_getVert_succ (i := j-1) (by omega)
          rwa [show j-1+1=j by omega] at edge
      · obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp h
        have jA := (Finset.mem_inter.mp hj).1
        obtain ⟨_,back⟩ := inside j jA
        refine ⟨back,via (j+1) j back jA (fun hi => ?_) ?_⟩
        · have aux := own j (j+1) jA hi (by omega)
          omega
        · exact (p.adj_getVert_succ (i := j) (by omega)).symm
    · obtain ⟨hB,hA⟩ := Finset.mem_sdiff.mp h
      obtain ⟨ri,ci⟩ := (mem_contactPositions p b i).mp hB
      exact ⟨ri,two_step_metric (different _) (fun h => hA ((mem_contactPositions p a i).mpr ⟨ri,h.symm⟩)) ab ci⟩
  exact ⟨card_protected_cross A B t.val (fun i h => (inside i h).1) separate,shell⟩
theorem protected_cross_positions [DecidableEq V] (p : G.Walk x y) (hp : p.IsPath)
    (t : Fin p.support.length)
    (longest : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → p.support[t.val] ∈ r.support → r.length ≤ p.length)
    {a b : V} (ha : a∉p.support) (hb : b∉p.support) (ab : G.Adj a b) :
    (contactPositions p a).card + (contactPositions p b).card ≤
      (p.support.toFinset.filter (fun z => G.dist a z=2)).card+1 := by
  classical
  let A := contactPositions p a
  let B := contactPositions p b
  obtain ⟨count,shell⟩ := protected_cross_indices p hp t longest ha hb ab
  have inj : Set.InjOn p.getVert ((crossIndices A B : Finset ℕ) : Set ℕ) := by
    intro i hi j hj same
    exact hp.getVert_injOn (by change i ≤ p.length; have := (shell i hi).1; have := p.length_support; omega)
      (by change j ≤ p.length; have := (shell j hj).1; have := p.length_support; omega) same
  have incl : (crossIndices A B).image p.getVert ⊆ p.support.toFinset.filter (fun z => G.dist a z=2) := by
    intro z hz
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hz
    exact Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr (p.getVert_mem_support i),(shell i hi).2⟩
  have bound := Finset.card_le_card incl
  rw [Finset.card_image_of_injOn inj] at bound
  exact count.trans (Nat.add_le_add_right bound 1)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
theorem protected_exterior_contact_degree (p : G.Walk x y) (hp : p.IsPath)
    (t : Fin p.support.length)
    (longest : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → p.support[t.val] ∈ r.support → r.length ≤ p.length)
    {a b : V} (ha : a∉p.support) (hb : b∉p.support) (ab : G.Adj a b)
    {k : ℕ} (quota : (Finset.univ.filter (fun z => G.dist a z=2)).card ≤ k) :
    (G.neighborFinset a ∩ p.support.toFinset).card + G.degree b ≤
      k+2+((G.neighborFinset b \ p.support.toFinset) ∩ G.neighborFinset a).card := by
  classical
  let P := p.support.toFinset
  let A := G.neighborFinset a
  let B := G.neighborFinset b
  let D := B \ P
  let C := D ∩ A
  let X := (D.erase a) \ A
  let Q := P.filter (fun z => G.dist a z=2)
  have acol := protected_cross_positions p hp t longest ha hb ab
  rw [contact_card_neighbors p hp a,contact_card_neighbors p hp b] at acol
  change (A∩P).card+(B∩P).card ≤ Q.card+1 at acol
  have ain : a∈D := Finset.mem_sdiff.mpr ⟨(G.mem_neighborFinset _ _).mpr ab.symm,
    fun h => ha (List.mem_toFinset.mp h)⟩
  have inter : (D.erase a) ∩ A = C := by
    ext z
    simp only [C,Finset.mem_inter,Finset.mem_erase]
    constructor
    · rintro ⟨⟨_,hd⟩,hA⟩
      exact ⟨hd,hA⟩
    · rintro ⟨hd,hA⟩
      exact ⟨⟨fun eq => G.irrefl (eq ▸ (G.mem_neighborFinset a z).mp hA),hd⟩,hA⟩
  have part₁ := Finset.card_sdiff_add_card_inter B P
  have part₂ := Finset.card_erase_add_one ain
  have part₃ := Finset.card_sdiff_add_card_inter (D.erase a) A
  rw [inter] at part₃
  change X.card+C.card=(D.erase a).card at part₃
  have shell (z : V) (hz : z∈X) : G.dist a z=2 := by
    obtain ⟨hD,hA⟩ := Finset.mem_sdiff.mp hz
    obtain ⟨ne,hd⟩ := Finset.mem_erase.mp hD
    have hzB := (Finset.mem_sdiff.mp hd).1
    exact two_step_metric ne.symm (fun hadj => hA ((G.mem_neighborFinset a z).mpr hadj)) ab
      ((G.mem_neighborFinset b z).mp hzB).symm
  have dis : Disjoint Q X := Finset.disjoint_left.mpr (by
    intro z hQ hX
    have dm := (Finset.mem_erase.mp (Finset.mem_sdiff.mp hX).1).2
    exact (Finset.mem_sdiff.mp dm).2 (Finset.mem_filter.mp hQ).1)
  have incl : Q ∪ X ⊆ Finset.univ.filter (fun z => G.dist a z=2) := by
    intro z hz
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩
    rcases Finset.mem_union.mp hz with h | h
    · exact (Finset.mem_filter.mp h).2
    · exact shell z h
  have total := (Finset.card_le_card incl).trans quota
  rw [Finset.card_union_of_disjoint dis] at total
  change D.card+(B∩P).card=B.card at part₁
  change (A∩P).card+B.card ≤ k+2+C.card
  omega
theorem protected_cross_contact_degree (p : G.Walk x y) (hp : p.IsPath)
    (t : Fin p.support.length)
    (longest : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → p.support[t.val] ∈ r.support → r.length ≤ p.length)
    {a b : V} (ha : a∉p.support) (hb : b∉p.support) (ab : G.Adj a b)
    {k : ℕ} (quota : (Finset.univ.filter (fun z => G.dist a z=2)).card ≤ k) :
    (G.neighborFinset a ∩ p.support.toFinset).card + G.degree b ≤
      k+1+(G.neighborFinset a \ p.support.toFinset).card := by
  classical
  let P := p.support.toFinset
  let A := G.neighborFinset a
  let B := G.neighborFinset b
  let C := (B \ P) ∩ A
  have bound := protected_exterior_contact_degree p hp t longest ha hb ab quota
  change (A∩P).card+G.degree b ≤ k+2+C.card at bound
  have absent : b∉C := by
    intro h
    have nb := (Finset.mem_sdiff.mp (Finset.mem_inter.mp h).1).1
    exact G.irrefl ((G.mem_neighborFinset _ _).mp nb)
  have share : insert b C ⊆ A \ P := by
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl | h
    · exact Finset.mem_sdiff.mpr ⟨(G.mem_neighborFinset _ _).mpr ab,
        fun h => hb (List.mem_toFinset.mp h)⟩
    · obtain ⟨hD,hA⟩ := Finset.mem_inter.mp h
      exact Finset.mem_sdiff.mpr ⟨hA,(Finset.mem_sdiff.mp hD).2⟩
  have count := Finset.card_le_card share
  rw [Finset.card_insert_of_notMem absent] at count
  change (A∩P).card+G.degree b ≤ k+1+(A \ P).card
  omega
theorem protected_half_degree (p : G.Walk x y) (hp : p.IsPath)
    (t : Fin p.support.length)
    (longest : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → p.support[t.val] ∈ r.support → r.length ≤ p.length)
    {a b : V} (ha : a∉p.support) (hb : b∉p.support) (ab : G.Adj a b)
    {k : ℕ} (quota : (Finset.univ.filter (fun z => G.dist a z=2)).card ≤ k)
    (high : k ≤ G.degree b) :
    G.degree a ≤ 2*(G.neighborFinset a \ p.support.toFinset).card+1 := by
  have cross := protected_cross_contact_degree p hp t longest ha hb ab quota
  have parts := Finset.card_sdiff_add_card_inter (G.neighborFinset a) p.support.toFinset
  change (G.neighborFinset a).card ≤ 2*(G.neighborFinset a \ p.support.toFinset).card+1
  omega
omit [Fintype V] [DecidableRel G.Adj] in
theorem protected_single_shell (p : G.Walk x y) (hp : p.IsPath)
    (t : Fin p.support.length)
    (longest : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → p.support[t.val] ∈ r.support → r.length ≤ p.length)
    {a : V} (ha : a ∉ p.support) (touch : (contactPositions p a).Nonempty) :
    (contactPositions p a).card + 1 ≤
      (p.support.toFinset.filter (fun v => G.dist a v = 2)).card := by
  classical
  let A := contactPositions p a
  let m := A.max' touch
  have hm : m ∈ A := Finset.max'_mem _ _
  have internal (i : ℕ) (hi : i ∈ A) : 0 < i ∧ i+1 < p.support.length := by
    obtain ⟨ri,ci⟩ := (mem_contactPositions p a i).mp hi
    exact protected_contact_internal p hp t longest ha ⟨i,ri⟩ (by simpa [get_at] using ci)
  have spaced (i j : ℕ) (hi : i ∈ A) (hj : j ∈ A) (lt : i < j) : i+2 ≤ j := by
    obtain ⟨ri,ci⟩ := (mem_contactPositions p a i).mp hi
    obtain ⟨rj,cj⟩ := (mem_contactPositions p a j).mp hj
    exact protected_contact_spacing p hp t longest ha ⟨i,ri⟩ ⟨j,rj⟩ lt
      (by simpa [get_at] using ci) (by simpa [get_at] using cj)
  let B := A.image (fun i => i-1)
  let W := insert (m+1) B
  have different (i : ℕ) : a ≠ p.getVert i := fun eq => ha (eq ▸ p.getVert_mem_support i)
  have ls := p.length_support
  have via (i j : ℕ) (hi : i < p.support.length) (hj : j ∈ A) (no : i ∉ A)
      (edge : G.Adj (p.getVert i) (p.getVert j)) : G.dist a (p.getVert i) = 2 := by
    have c := ((mem_contactPositions p a j).mp hj).2
    exact two_step_metric (different _) (fun h => no ((mem_contactPositions p a i).mpr ⟨hi,h.symm⟩)) c.symm edge
  have valid (i : ℕ) (hi : i ∈ W) : i < p.support.length ∧ G.dist a (p.getVert i) = 2 := by
    rcases mem_insert.mp hi with rfl|h
    · have ht := (internal m hm).2
      refine ⟨ht,via _ m ht hm (fun mem => ?_) ((p.adj_getVert_succ (i:=m) (by omega)).symm)⟩
      have := spaced m (m+1) hm mem (by omega)
      omega
    · obtain ⟨j,hj,rfl⟩ := mem_image.mp h
      obtain ⟨positive,back⟩ := internal j hj
      have lim : j-1 < p.support.length := by omega
      refine ⟨lim,via _ j lim hj (fun mem => ?_) ?_⟩
      · have := spaced (j-1) j mem hj (by omega)
        omega
      · have edge := p.adj_getVert_succ (i:=j-1) (by omega)
        rwa [show j-1+1=j by omega] at edge
  have maxoutside : m+1 ∉ B := by
    intro h
    obtain ⟨i,hi,eq⟩ := mem_image.mp h
    have lim : i ≤ m := Finset.le_max' _ _ hi
    omega
  have predinj : Set.InjOn (fun i : ℕ => i-1) (A : Set ℕ) := by
    intro i hi j hj eq
    have := (internal i hi).1
    have := (internal j hj).1
    change i-1=j-1 at eq
    omega
  have nodeinj : Set.InjOn p.getVert (W : Set ℕ) := by
    intro i hi j hj eq
    exact hp.getVert_injOn (by change i ≤ p.length; have := (valid i hi).1; omega)
      (by change j ≤ p.length; have := (valid j hj).1; omega) eq
  have sub : W.image p.getVert ⊆ p.support.toFinset.filter (fun v => G.dist a v = 2) := by
    intro v hv
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hv
    exact mem_filter.mpr ⟨List.mem_toFinset.mpr (p.getVert_mem_support _),(valid i hi).2⟩
  have count := card_le_card sub
  rw [card_image_of_injOn nodeinj,show W = insert (m+1) B from rfl,card_insert_of_notMem maxoutside,
    show B = A.image (fun i => i-1) from rfl,card_image_of_injOn predinj] at count
  exact count
end Graph189ExteriorGap
end
section
open SimpleGraph Finset
namespace Graph189ExteriorGap
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {x y : V}
omit [Fintype V] in
theorem vertex_positions_equiv (p : G.Walk x y) (M : Finset V) (onPath : ∀ z∈M, z∈p.support) :
    ∃ marks : Finset (Fin p.support.length), ∃ e : marks ≃ M,
      ∀ i : marks, p.support[i.val.val]=(e i).val := by
  classical
  let pos (u : M) : Fin p.support.length :=
    ⟨p.support.idxOf u.val,List.idxOf_lt_length_iff.mpr (onPath u.val u.property)⟩
  have eval (u : M) : p.support[(pos u).val] = u.val := List.getElem_idxOf (List.idxOf_lt_length_iff.mpr (onPath u.val u.property))
  have inj : Function.Injective pos := by
    intro a b h
    apply Subtype.ext
    calc
      a.val = p.support[(pos a).val] := (eval a).symm
      _ = p.support[(pos b).val] := by rw [h]
      _ = b.val := eval b
  let marks := M.attach.image pos
  let embed (u : M) : marks := ⟨pos u, Finset.mem_image.mpr ⟨u,Finset.mem_attach _ _,rfl⟩⟩
  have bij : Function.Bijective embed := by
    constructor
    · intro a b eq
      exact inj (congrArg Subtype.val eq)
    · intro i
      obtain ⟨u,hu,eq⟩ := Finset.mem_image.mp i.property
      exact ⟨u,Subtype.ext eq⟩
  let e := Equiv.ofBijective embed bij
  refine ⟨marks,e.symm,?_⟩
  intro i
  have posEq : pos (e.symm i)=i.val := congrArg Subtype.val (e.apply_symm_apply i)
  have value := eval (e.symm i)
  rwa [posEq] at value
end Graph189ExteriorGap
end
section
open Finset SimpleGraph
namespace Graph189DenseExteriorOrder
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
variable [DecidableRel G.Adj] {x y : V}
theorem neighbors_on_path (p : G.Walk x y) (W : Finset V)
    (boundary : ∀ w ∈ W, ∀ v, G.Adj w v → v ∉ W → v ∈ p.support)
    {w : V} (hw : w ∈ W) :
    G.degree w+1 ≤ W.card+((univ : Finset (Fin p.support.length)).filter
      (fun i => G.Adj p.support[i.val] w)).card := by
  classical
  let R := (univ : Finset (Fin p.support.length)).filter (fun i => G.Adj p.support[i.val] w)
  let P := R.image (fun i => p.support[i.val])
  have sub : insert w (G.neighborFinset w) ⊆ W ∪ P := by
    intro v hv
    rcases mem_insert.mp hv with rfl | h
    · exact mem_union_left _ hw
    have edge := (G.mem_neighborFinset _ _).mp h
    by_cases vw : v ∈ W
    · exact mem_union_left _ vw
    obtain ⟨i,hi,eq⟩ := List.mem_iff_getElem.mp (boundary w hw v edge vw)
    exact mem_union_right _ (mem_image.mpr ⟨⟨i,hi⟩,
      mem_filter.mpr ⟨mem_univ _,by simpa only [eq] using edge.symm⟩,eq⟩)
  have h := (card_le_card sub).trans (card_union_le W P)
  rw [card_insert_of_notMem (by simp),G.card_neighborFinset_eq_degree] at h
  exact h.trans (Nat.add_le_add_left card_image_le _)
end Graph189DenseExteriorOrder
end
section
open SimpleGraph Finset
namespace Graph189ExteriorGap
variable {V : Type*} {G : SimpleGraph V} {x y : V}
private theorem singleton_gap (p : G.Walk x y) (hp : p.IsPath) {z : V}
    (outside : z ∉ p.support) {m : ℕ}
    (maximal : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → z ∈ r.support →
      r.support.length+m ≤ p.support.length+1)
    (A J B : List V) (split : p.support=A++J++B)
    (left : ∀ v∈A.getLast?, G.Adj v z) (right : ∀ v∈B.head?, G.Adj z v) :
    m ≤ J.length := by
  let q : G.Walk z z := Walk.nil
  have dis : List.Disjoint q.support p.support := by simpa [q,List.disjoint_left] using outside
  obtain ⟨a,b,r,hr,rs⟩ := splice_support p hp A J B split q (by simp [q]) dis left right
  have count := maximal r hr (by simp [rs,q])
  rw [rs,split] at count
  simp only [q,Walk.support_nil,List.length_append,List.length_singleton] at count
  omega
private theorem first_tail (p : G.Walk x y) (hp : p.IsPath)
    {m : ℕ} {z : V} (outside : z ∉ p.support)
    (maximal : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → z ∈ r.support →
      r.support.length + m ≤ p.support.length+1)
    (i : Fin p.support.length)
    (contact : G.Adj z p.support[i.val]) : m ≤ i.val := by
  let L := p.support
  have head : (L.drop i.val).head? = some L[i.val] := by
    simp [List.head?_drop]
  have gap := singleton_gap p hp outside maximal [] (L.take i.val) (L.drop i.val)
    (by simp [L]) (by simp) (by
      intro z hz
      rw [head] at hz
      have eq : L[i.val] = z := by simpa using hz
      exact eq ▸ contact)
  have small := List.length_take_le i.val L
  omega
private theorem last_tail (p : G.Walk x y) (hp : p.IsPath)
    {m : ℕ} {z : V} (outside : z ∉ p.support)
    (maximal : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → z ∈ r.support →
      r.support.length + m ≤ p.support.length+1)
    (i : Fin p.support.length)
    (contact : G.Adj p.support[i.val] z) : i.val + 1 + m ≤ p.support.length := by
  let L := p.support
  have last : (L.take (i.val+1)).getLast? = some L[i.val] := by
    exact (congrArg List.getLast? (List.take_succ_eq_append_getElem
      (l := L) (i := i.val) i.isLt)).trans List.getLast?_concat
  have gap := singleton_gap p hp outside maximal (L.take (i.val+1)) (L.drop (i.val+1)) []
    (by simp [L]) (by
      intro z hz
      rw [last] at hz
      have eq : L[i.val] = z := by simpa using hz
      exact eq ▸ contact) (by simp)
  simp only [L,List.length_drop] at gap
  have hi := i.isLt
  omega
private theorem inner_gap (p : G.Walk x y) (hp : p.IsPath)
    {m : ℕ} {z : V} (outside : z ∉ p.support)
    (maximal : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → z ∈ r.support →
      r.support.length + m ≤ p.support.length+1)
    (i j : Fin p.support.length) (hij : i < j)
    (left : G.Adj p.support[i.val] z) (right : G.Adj z p.support[j.val]) :
    i.val+1+m ≤ j.val := by
  let L := p.support
  let gap := j.val-(i.val+1)
  have ij : i.val+1+gap=j.val := by
    change i.val < j.val at hij
    dsimp [gap]
    omega
  have split : L = L.take (i.val+1) ++ (L.drop (i.val+1)).take gap ++ L.drop j.val := by
    rw [←List.take_add,ij,List.take_append_drop]
  have last : (L.take (i.val+1)).getLast? = some L[i.val] := by
    exact (congrArg List.getLast? (List.take_succ_eq_append_getElem
      (l := L) (i := i.val) i.isLt)).trans List.getLast?_concat
  have head : (L.drop j.val).head? = some L[j.val] := by
    simp [List.head?_drop]
  have bound := singleton_gap p hp outside maximal _ _ _ split (by
    intro z hz
    rw [last] at hz
    have eq : L[i.val] = z := by simpa using hz
    exact eq ▸ left) (by
    intro z hz
    rw [head] at hz
    have eq : L[j.val] = z := by simpa using hz
    exact eq ▸ right)
  have small := List.length_take_le gap (L.drop (i.val+1))
  omega
variable [DecidableEq V] [Fintype V] [DecidableRel G.Adj]
theorem protected_exterior_size_upper (p : G.Walk x y) (hp : p.IsPath) {z : V}
    (outside : z ∉ p.support) (all : ∀ v, v ≠ z → v ∈ p.support)
    (pos : 0 < G.degree z) {a b : V} (Q : G.Walk a b) (hQ : Q.IsPath)
    (maximal : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → z ∈ r.support → r.length ≤ Q.length) :
    1+G.degree z+(G.degree z+1)*(Q.support.toFinsetᶜ : Finset V).card ≤ Fintype.card V := by
  classical
  let m := (Q.support.toFinsetᶜ : Finset V).card
  have size : p.support.length+1=Fintype.card V := by
    have h : insert z p.support.toFinset=univ := by
      ext v
      by_cases e : v=z
      · simp [e]
      · simp [all v e]
    have eq := congrArg Finset.card h
    rwa [card_insert_of_notMem (by simpa using outside),
      List.toFinset_card_of_nodup hp.support_nodup,card_univ] at eq
  have mx {u v} (r : G.Walk u v) (hr : r.IsPath) (contains : z∈r.support) :
      r.support.length + m ≤ p.support.length+1 := by
    have bound := maximal r hr contains
    have total := card_add_card_compl Q.support.toFinset
    rw [List.toFinset_card_of_nodup hQ.support_nodup] at total
    change Q.support.length+m=Fintype.card V at total
    have := Q.length_support
    have := r.length_support
    omega
  let N := G.neighborFinset z
  have onPath (v : V) (hv : v∈N) : v∈p.support :=
    all v ((G.mem_neighborFinset _ _).mp hv).ne.symm
  obtain ⟨marks,e,values⟩ := vertex_positions_equiv p N onPath
  have card : marks.card = G.degree z := by
    have eq : marks.card = N.card := by
      simpa only [Fintype.card_coe] using Fintype.card_congr e
    exact eq.trans (G.card_neighborFinset_eq_degree z)
  let j := marks.card-1
  have hj : marks.card = j+1 := by dsimp [j]; omega
  let iso := marks.orderIsoOfFin hj
  let M := marks.orderEmbOfFin hj
  have adj (i : Fin (j+1)) : G.Adj z p.support[(M i).val] := by
    change G.Adj z p.support[(iso i).val.val]
    rw [values (iso i)]
    exact (G.mem_neighborFinset _ _).mp (e (iso i)).property
  have fst := first_tail p hp outside mx (M 0) (adj _)
  have lst := last_tail p hp outside mx (M (Fin.last j)) (adj _).symm
  have spread (i : Fin j) : (M i.castSucc).val+1+m ≤ (M i.succ).val :=
    inner_gap p hp outside mx (M i.castSucc) (M i.succ) (M.strictMono i.castSucc_lt_succ)
      (adj _).symm (adj _)
  have lower (i : Fin (j+1)) : (i.val+1)*m+i.val ≤ (M i).val := by
    induction i using Fin.induction with
    | zero => simpa using fst
    | succ i ih =>
      have step := spread i
      simp only [Fin.val_castSucc,Fin.val_succ,Nat.succ_mul] at ih step ⊢
      omega
  have final := lower (Fin.last j)
  simp only [Fin.val_last] at final
  change 1+G.degree z+(G.degree z+1)*m ≤ _
  rw [←card,hj]
  rw [Nat.succ_mul]
  omega
omit [DecidableRel G.Adj] [DecidableEq V] in
theorem exists_longest_through (G : SimpleGraph V) (z : V) :
    ∃ a b, ∃ Q : G.Walk a b, Q.IsPath ∧ ∃ t : Fin Q.support.length,
      Q.support[t.val] = z ∧
        ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → z ∈ r.support → r.length ≤ Q.length := by
  classical
  let Good (n : ℕ) := ∃ a b, ∃ Q : G.Walk a b, Q.IsPath ∧ z ∈ Q.support ∧ Q.length=n
  have base : Good 0 := ⟨z,z,.nil,by simp,by simp,rfl⟩
  obtain ⟨a,b,Q,hQ,mem,sz⟩ := Nat.findGreatest_spec (Nat.zero_le (Fintype.card V)) base
  obtain ⟨i,hi,eq⟩ := List.mem_iff_getElem.mp mem
  refine ⟨a,b,Q,hQ,⟨i,hi⟩,eq,?_⟩
  intro u v r hr member
  rw [sz]
  have len := r.length_support
  have bound := hr.support_nodup.length_le_card
  exact Nat.le_findGreatest (by omega) (show Good r.length from ⟨u,v,r,hr,member,rfl⟩)
theorem protected_size_of_traceable_deletion (z : V) (pos : 0 < G.degree z)
    {x y : {v : V | v ≠ z}} (p : (G.induce {v : V | v ≠ z}).Walk x y) (hp : p.IsHamiltonian)
    {a b : V} (Q : G.Walk a b) (hQ : Q.IsPath)
    (maximal : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → z ∈ r.support → r.length ≤ Q.length) :
    1+G.degree z+(G.degree z+1)*(Q.support.toFinsetᶜ : Finset V).card ≤ Fintype.card V := by
  let e := Embedding.induce (G:=G) {v : V | v ≠ z}
  apply protected_exterior_size_upper (p.map e.toHom) (hp.isPath.map e.injective) _ _ pos Q hQ maximal
  · rw [Walk.support_map]
    intro h
    obtain ⟨v,_,eq⟩ := List.mem_map.mp h
    exact v.property eq
  · intro v ne
    rw [Walk.support_map]
    exact List.mem_map.mpr ⟨⟨v,ne⟩,hp.mem_support _,rfl⟩
end Graph189ExteriorGap
end
section
open SimpleGraph Finset
namespace Graph189CutSides
variable {V : Type*} [Fintype V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]
theorem connectivity_le_degree (z : V) : G.vertexConnectivity ≤ G.degree z := by
  classical
  let S := G.neighborFinset z
  have sz : S.card=G.degree z := G.card_neighborFinset_eq_degree z
  have convention : G.vertexConnectivity ≤ Fintype.card V-1 := by
    unfold vertexConnectivity
    rw [if_neg (not_le.mpr (Fintype.one_lt_card (α:=V)))]
    exact Nat.sInf_le ⟨univ.erase z,by simp,Or.inr (by simp)⟩
  by_contra! fail
  have conn := connected_after_smaller_deletion (G:=G) S (sz ▸ fail)
  let W := {v : V | v ∉ S}
  let z' : W := ⟨z, show z ∉ G.neighborFinset z by simp⟩
  have card : 1 < Fintype.card W := by
    have same : W = ((Sᶜ : Finset V) : Set V) := by ext v; simp [W]
    rw [Fintype.card_congr (Equiv.setCongr same)]
    change 1 < Fintype.card (Sᶜ : Finset V)
    rw [Fintype.card_coe,Finset.card_compl]
    omega
  let _ : Nontrivial W := Fintype.one_lt_card_iff_nontrivial.mp card
  obtain ⟨w,edge⟩ := conn.preconnected.exists_adj_of_nontrivial z'
  exact w.property ((G.mem_neighborFinset z w.val).mpr edge)
end Graph189CutSides
end
section
open SimpleGraph Finset
namespace Graph189FourTerminalGap
open Graph189ExteriorGap
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {a b : V}
theorem impossible_of_exact_length (p : G.Walk a b) (hp : p.IsPath) {x : V} (outside : x ∉ p.support)
    {i j lo hi m : ℕ} (left : 0 < i) (spaced : i+2 ≤ j) (right : j+1 < p.support.length)
    (marks : contactPositions p x = {i,j})
    (bound : hi ≤ p.support.length) (size : lo+m=hi)
    (unmarked : ∀ h ∈ Ico lo hi, h ≠ i ∧ h ≠ j)
    (via : ∀ h ∈ Ico lo hi, ∃ w, G.Adj x w ∧ G.Adj (p.getVert h) w)
    (quota : (univ.filter (fun y => G.dist x y=2)).card ≤ m+1) : False := by
  classical
  let J := Ico lo hi
  let W : Finset ℕ := {i-1,i+1,j-1,j+1}
  have skipI : ¬(lo ≤ i ∧ i < hi) := fun h => (unmarked i (mem_Ico.mpr h)).1 rfl
  have skipJ : ¬(lo ≤ j ∧ j < hi) := fun h => (unmarked j (mem_Ico.mpr h)).2 rfl
  have pair : ∃ u ∈ W, ∃ v ∈ W, u≠v ∧ u∉J ∧ v∉J := by
    by_cases before : hi ≤ i
    · refine ⟨j-1,by simp [W],j+1,by simp [W],by omega,?_,?_⟩ <;> simp [J] <;> omega
    by_cases after : j < lo
    · refine ⟨i-1,by simp [W],i+1,by simp [W],by omega,?_,?_⟩ <;> simp [J] <;> omega
    refine ⟨i-1,by simp [W],j+1,by simp [W],by omega,?_,?_⟩ <;> simp [J] <;> omega
  obtain ⟨u,hu,v,hv,ne,uout,vout⟩ := pair
  have mark {h : ℕ} (m : h=i ∨ h=j) : G.Adj x (p.getVert h) := by
    have hm : h ∈ contactPositions p x := by simpa [marks] using m
    exact ((mem_contactPositions p x h).mp hm).2.symm
  have charge (h : ℕ) (hh : h < p.support.length) (missing : h≠i ∧ h≠j)
      (link : ∃ w, G.Adj x w ∧ G.Adj (p.getVert h) w) : G.dist x (p.getVert h)=2 := by
    obtain ⟨w,hx,hw⟩ := link
    have different : x ≠ p.getVert h := fun eq => outside (eq ▸ p.getVert_mem_support h)
    apply two_step_metric different _ hx hw
    intro adj
    have hm := (mem_contactPositions p x h).mpr ⟨hh,adj.symm⟩
    rw [marks] at hm
    simp only [mem_insert,mem_singleton,missing.1,missing.2,or_self] at hm
  have shifts (h : ℕ) (hh : h∈W) : h < p.support.length ∧ G.dist x (p.getVert h)=2 := by
    have len := p.length_support
    have before (t : ℕ) (pos : 0 < t) (range : t < p.support.length) (hit : t=i ∨ t=j)
        (miss : t-1≠i ∧ t-1≠j) : G.dist x (p.getVert (t-1))=2 := by
      have step := p.adj_getVert_succ (i:=t-1) (by omega)
      rw [show t-1+1=t by omega] at step
      exact charge _ (by omega) miss ⟨_,mark hit,step⟩
    have after (t : ℕ) (range : t+1 < p.support.length) (hit : t=i ∨ t=j)
        (miss : t+1≠i ∧ t+1≠j) : G.dist x (p.getVert (t+1))=2 :=
      charge _ range miss ⟨_,mark hit,(p.adj_getVert_succ (i:=t) (by omega)).symm⟩
    simp only [W,mem_insert,mem_singleton] at hh
    rcases hh with rfl|rfl|rfl|rfl
    · exact ⟨by omega,before i left (by omega) (Or.inl rfl) (by omega)⟩
    · exact ⟨by omega,after i (by omega) (Or.inl rfl) (by omega)⟩
    · exact ⟨by omega,before j (by omega) (by omega) (Or.inr rfl) (by omega)⟩
    · exact ⟨right,after j right (Or.inr rfl) (by omega)⟩
  let T := insert u (insert v J)
  have good (h : ℕ) (hh : h ∈ T) : h < p.support.length ∧ G.dist x (p.getVert h)=2 := by
    rcases mem_insert.mp hh with rfl | hrest
    · exact shifts _ hu
    rcases mem_insert.mp hrest with rfl | member
    · exact shifts _ hv
    have r := (mem_Ico.mp member).2.trans_le bound
    exact ⟨r,charge _ r (unmarked _ member) (via _ member)⟩
  have count : T.card=m+2 := by
    have jcard : J.card=hi-lo := Nat.card_Ico _ _
    rw [show T=insert u (insert v J) from rfl,card_insert_of_notMem (by simpa [ne] using uout),
      card_insert_of_notMem vout,jcard]
    omega
  have inj : Set.InjOn p.getVert (T : Set ℕ) := by
    intro h hh e he eq
    have := (good _ hh).1
    have := (good _ he).1
    have := p.length_support
    exact hp.getVert_injOn (by change h ≤ p.length; omega) (by change e ≤ p.length; omega) eq
  have sub : T.image p.getVert ⊆ univ.filter (fun y => G.dist x y=2) := by
    intro w hw
    obtain ⟨e,he,rfl⟩ := mem_image.mp hw
    exact mem_filter.mpr ⟨mem_univ _,(good _ he).2⟩
  have large := (card_le_card sub).trans quota
  rw [card_image_of_injOn inj,count] at large
  omega
theorem impossible_of_length (p : G.Walk a b) (hp : p.IsPath) {x : V} (outside : x ∉ p.support)
    {i j lo hi m : ℕ} (left : 0 < i) (spaced : i+2 ≤ j) (right : j+1 < p.support.length)
    (marks : contactPositions p x = {i,j})
    (bound : hi ≤ p.support.length) (size : lo+m=hi)
    (unmarked : ∀ h ∈ Ico lo hi, h ≠ i ∧ h ≠ j)
    (via : ∀ h ∈ Ico lo hi, ∃ w, G.Adj x w ∧ G.Adj (p.getVert h) w)
    (cap : G.distEven x ≤ m+2) : False := by
  classical
  apply impossible_of_exact_length p hp outside left spaced right marks bound size unmarked via
  let T := univ.filter (fun y => G.dist x y=2)
  have missing : x ∉ T := by simp [T]
  have sub : insert x T ⊆ univ.filter (fun y => Even (G.dist x y)) := by
    intro w hw
    rcases mem_insert.mp hw with rfl|h
    · simp
    · exact mem_filter.mpr ⟨mem_univ _,by rw [(mem_filter.mp h).2]; decide⟩
  have count := card_le_card sub
  rw [card_insert_of_notMem missing] at count
  change T.card+1 ≤ G.distEven x at count
  change T.card ≤ m+1
  omega
end Graph189FourTerminalGap
end
section
namespace Graph189ExteriorGap
theorem exists_tight_protected_gap {L j m : ℕ} (t : Fin L)
    (a : Fin (j+1) ↪o Fin L)
    (prefix_pos : 0 < (a 0).val)
    (suffix_pos : (a (Fin.last j)).val+1 < L)
    (gap_pos : ∀ i : Fin j, (a i.castSucc).val+2 ≤ (a i.succ).val)
    (prefix_min : a 0 ≤ t → m ≤ (a 0).val)
    (suffix_min : t ≤ a (Fin.last j) → (a (Fin.last j)).val+1+m ≤ L)
    (gap_min : ∀ i : Fin j, a i.succ ≤ t ∨ t ≤ a i.castSucc →
      (a i.castSucc).val+1+m ≤ (a i.succ).val)
    (cap : L ≤ (j+1)*m+2*(j+1)) :
    (a 0 ≤ t ∧ (a 0).val=m) ∨
    (t ≤ a (Fin.last j) ∧ (a (Fin.last j)).val+1+m=L) ∨
    ∃ i : Fin j, (a i.succ ≤ t ∨ t ≤ a i.castSucc) ∧
      (a i.castSucc).val+1+m=(a i.succ).val := by
  by_contra! fail
  obtain ⟨first,last,inside⟩ := fail
  let pos (i : Fin (j+1)) := (a i).val + if t < a i then m else 0
  have base : m+1 ≤ pos 0 := by
    by_cases h : t < a 0
    · simp only [pos,if_pos h]; omega
    have le := le_of_not_gt h
    have := first le
    have := prefix_min le
    simp only [pos,if_neg h]; omega
  have step (i : Fin j) : pos i.castSucc+(m+2) ≤ pos i.succ := by
    have ordered := a.strictMono i.castSucc_lt_succ
    by_cases l : t < a i.castSucc
    · have h : a i.succ ≤ t ∨ t ≤ a i.castSucc := Or.inr l.le
      have := gap_min i h
      have := inside i h
      simp only [pos,if_pos l,if_pos (l.trans ordered)]; omega
    by_cases r : t < a i.succ
    · have := gap_pos i
      simp only [pos,if_neg l,if_pos r]; omega
    have h : a i.succ ≤ t ∨ t ≤ a i.castSucc := Or.inl (le_of_not_gt r)
    have := gap_min i h
    have := inside i h
    simp only [pos,if_neg l,if_neg r]; omega
  have acc (i : Fin (j+1)) : m+1+i.val*(m+2) ≤ pos i := by
    induction i using Fin.induction with
    | zero => simpa using base
    | succ i ih =>
      have h := step i
      simp only [Fin.val_succ,Fin.val_castSucc,Nat.succ_mul] at ih ⊢
      omega
  have finish : pos (Fin.last j)+2 ≤ L := by
    by_cases h : t < a (Fin.last j)
    · have := suffix_min h.le
      have := last h.le
      simp only [pos,if_pos h]; omega
    · simp only [pos,if_neg h]; omega
  have lower := acc (Fin.last j)
  simp only [Fin.val_last,Nat.mul_add,Nat.succ_mul] at lower cap
  omega
end Graph189ExteriorGap
end
section
namespace Graph189ExteriorGap
open Finset
theorem locate_tight_protected_gap {L j m : ℕ} (t : Fin L)
    (M : Finset (Fin L)) (count : M.card=j+1) (positive : 0 < m)
    (prefix_pos : 0 < (M.orderEmbOfFin count 0).val)
    (suffix_pos : (M.orderEmbOfFin count (Fin.last j)).val+1 < L)
    (gap_pos : ∀ i : Fin j, (M.orderEmbOfFin count i.castSucc).val+2 ≤ (M.orderEmbOfFin count i.succ).val)
    (prefix_min : M.orderEmbOfFin count 0 ≤ t → m ≤ (M.orderEmbOfFin count 0).val)
    (suffix_min : t ≤ M.orderEmbOfFin count (Fin.last j) →
      (M.orderEmbOfFin count (Fin.last j)).val+1+m ≤ L)
    (gap_min : ∀ i : Fin j, M.orderEmbOfFin count i.succ ≤ t ∨ t ≤ M.orderEmbOfFin count i.castSucc →
      (M.orderEmbOfFin count i.castSucc).val+1+m ≤ (M.orderEmbOfFin count i.succ).val)
    (cap : L ≤ (j+1)*m+2*(j+1)) :
    ∃ lo hi, lo < hi ∧ hi ≤ L ∧ hi-lo=m ∧ (t.val < lo ∨ hi ≤ t.val) ∧
      (lo=0 ∨ ∃ i∈M, i.val+1=lo) ∧ (hi=L ∨ ∃ i∈M, i.val=hi) ∧
      (0 < lo ∨ hi < L) ∧ ∀ i∈M, i.val < lo ∨ hi ≤ i.val := by
  let a := M.orderEmbOfFin count
  have marked (i : Fin (j+1)) : a i ∈ M := M.orderEmbOfFin_mem count i
  have preimage (i : Fin L) (hi : i∈M) : ∃ h, a h=i := by
    change i ∈ Set.range (M.orderEmbOfFin count)
    rwa [M.range_orderEmbOfFin]
  rcases exists_tight_protected_gap t a prefix_pos suffix_pos gap_pos prefix_min suffix_min gap_min cap
      with ⟨safe,size⟩ | ⟨safe,size⟩ | ⟨d,safe,size⟩
  · refine ⟨0,(a 0).val,by omega,(a 0).isLt.le,by omega,Or.inr safe,Or.inl rfl,
      Or.inr ⟨_,marked 0,rfl⟩,Or.inr (a 0).isLt,?_⟩
    intro i hi
    obtain ⟨d,rfl⟩ := preimage i hi
    exact Or.inr (a.monotone (Fin.zero_le d))
  · refine ⟨(a (Fin.last j)).val+1,L,by omega,le_rfl,by omega,Or.inl ?_,
      Or.inr ⟨_,marked _,rfl⟩,Or.inl rfl,Or.inl (by omega),?_⟩
    · change t.val ≤ (a (Fin.last j)).val at safe
      omega
    · intro i hi
      obtain ⟨d,rfl⟩ := preimage i hi
      exact Or.inl (Nat.lt_succ_of_le (show (a d).val ≤ (a (Fin.last j)).val from a.monotone (Fin.le_last d)))
  · refine ⟨(a d.castSucc).val+1,(a d.succ).val,by omega,(a d.succ).isLt.le,by omega,?_,
      Or.inr ⟨_,marked _,rfl⟩,Or.inr ⟨_,marked _,rfl⟩,Or.inl (by omega),?_⟩
    · rcases safe with left|right
      · exact Or.inr left
      · exact Or.inl (Nat.lt_succ_of_le right)
    · intro i hi
      obtain ⟨h,rfl⟩ := preimage i hi
      by_cases small : h ≤ d.castSucc
      · exact Or.inl (Nat.lt_succ_of_le (show (a h).val ≤ (a d.castSucc).val from a.monotone small))
      · exact Or.inr (a.monotone (show d.succ ≤ h by
          change ¬ h.val ≤ d.val at small
          change d.val+1 ≤ h.val
          omega))
end Graph189ExteriorGap
end
section
open SimpleGraph
namespace Graph189ExteriorGap
variable {V : Type*} {G : SimpleGraph V} {a b x y : V}
theorem protected_swap_neighbors_with_route (p : G.Walk a b) (hp : p.IsPath) (z : V)
    (A J B : List V) (split : p.support=A++J++B) (kept : z ∈ A ∨ z ∈ B)
    (q : G.Walk x y) (hq : q.IsPath) (dis : List.Disjoint q.support p.support)
    (size : q.support.length=J.length)
    (left : ∀ v∈A.getLast?, G.Adj v x) (right : ∀ v∈B.head?, G.Adj y v)
    (uniform : ∀ {i j}, ∀ r : G.Walk i j, r.IsPath → z ∈ r.support → q.support ⊆ r.support → r.length=p.length →
      ∀ c ∈ r.support, ∀ v ∉ r.support, ∀ w ∉ r.support, G.Adj c v → G.Adj c w)
    {c : V} (contact : c ∈ A ∨ c ∈ B) (neighbor : ∃ v ∈ J, G.Adj c v) :
    ∀ v ∈ J, G.Adj c v := by
  obtain ⟨i,j,r,hr,e⟩ := splice_support p hp A J B split q hq dis left right
  have nd := hp.support_nodup
  rw [split] at nd
  have separated (v : V) (hv : v ∈ J) : v ∉ r.support := by
    rw [e]
    intro h
    rcases List.mem_append.mp h with mid | last
    · rcases List.mem_append.mp mid with first | new
      · exact List.disjoint_left.mp nd.of_append_left.disjoint first hv
      · exact List.disjoint_left.mp dis new (by simp [split,hv])
    · exact List.disjoint_left.mp nd.disjoint (by simp [hv]) last
  have length : r.length=p.length := by
    have h := r.length_support
    have g := p.length_support
    rw [split] at g
    rw [e] at h
    simp only [List.length_append,size] at h g
    omega
  have keep (v : V) (h : v∈A ∨ v∈B) : v∈r.support := by
    rw [e]
    rcases h with h | h <;> simp [h]
  obtain ⟨v,hv,edge⟩ := neighbor
  exact fun w hw => uniform r hr (keep z kept) (fun v hv => by rw [e]; simp [hv]) length c (keep c contact)
    v (separated v hv) w (separated w hw) edge
theorem protected_swap_neighbors (p : G.Walk a b) (hp : p.IsPath) (z : V)
    (A J B : List V) (split : p.support=A++J++B) (kept : z ∈ A ∨ z ∈ B)
    (q : G.Walk x y) (hq : q.IsPath) (dis : List.Disjoint q.support p.support)
    (size : q.support.length=J.length)
    (left : ∀ v∈A.getLast?, G.Adj v x) (right : ∀ v∈B.head?, G.Adj y v)
    (uniform : ∀ {i j}, ∀ r : G.Walk i j, r.IsPath → z ∈ r.support → r.length=p.length →
      ∀ c ∈ r.support, ∀ v ∉ r.support, ∀ w ∉ r.support, G.Adj c v → G.Adj c w)
    {c : V} (contact : c ∈ A ∨ c ∈ B) (neighbor : ∃ v ∈ J, G.Adj c v) :
    ∀ v ∈ J, G.Adj c v := by
  apply protected_swap_neighbors_with_route p hp z A J B split kept q hq dis size left right _ contact neighbor
  exact fun r hr hz _ => uniform r hr hz
end Graph189ExteriorGap
end
section
open SimpleGraph Finset
namespace Graph189ExteriorGap
variable {V : Type*} {G : SimpleGraph V} {a b x y : V}
theorem interval_exchange_witnesses_with_route (p : G.Walk a b) (hp : p.IsPath) (t : Fin p.support.length)
    (M : Finset (Fin p.support.length)) (q : G.Walk x y) (hq : q.IsPath)
    (dis : List.Disjoint q.support p.support)
    (touch : ∀ i ∈ M, G.Adj p.support[i.val] x ∧ G.Adj p.support[i.val] y)
    (uniform : ∀ {i j}, ∀ r : G.Walk i j, r.IsPath → p.support[t.val] ∈ r.support → q.support ⊆ r.support → r.length=p.length →
      ∀ c ∈ r.support, ∀ v ∉ r.support, ∀ w ∉ r.support, G.Adj c v → G.Adj c w)
    {lo hi : ℕ} (nonempty : lo < hi) (bound : hi ≤ p.support.length) (size : hi-lo=q.support.length)
    (safe : t.val < lo ∨ hi ≤ t.val) (lower : lo=0 ∨ ∃ i∈M, i.val+1=lo)
    (upper : hi=p.support.length ∨ ∃ i∈M, i.val=hi) (one : 0 < lo ∨ hi < p.support.length) :
    ∀ i ∈ Ico lo hi, ∃ w, G.Adj x w ∧ G.Adj (p.getVert i) w := by
  let L := p.support
  let A := L.take lo
  let J := (L.drop lo).take (hi-lo)
  let B := L.drop hi
  have split : p.support=A++J++B := by
    change L=L.take lo++(L.drop lo).take (hi-lo)++L.drop hi
    rw [←List.take_add, Nat.add_sub_of_le nonempty.le,List.take_append_drop]
  have kept (i : Fin L.length) (s : i.val < lo ∨ hi ≤ i.val) : L[i.val]∈A ∨ L[i.val]∈B := by
    rcases s with u|v
    · exact Or.inl (List.mem_take_iff_getElem.mpr ⟨i.val,lt_min u i.isLt,rfl⟩)
    · exact Or.inr (List.mem_drop_iff_getElem.mpr
        ⟨i.val-hi,by have := i.isLt; omega,by simp [Nat.add_sub_of_le v]⟩)
  have inside (i : ℕ) (u : lo ≤ i) (v : i < hi) : p.getVert i ∈ J := by
    have ri : i < L.length := v.trans_le bound
    apply List.mem_take_iff_getElem.mpr
    refine ⟨i-lo,?_,?_⟩
    · rw [List.length_drop]
      exact lt_min (Nat.sub_lt_sub_right u v) (Nat.sub_lt_sub_right u ri)
    · simpa only [List.getElem_drop, Nat.add_sub_of_le u] using get_at p ri
  have left : ∀ v∈A.getLast?, G.Adj v x := by
    intro v hv
    rcases lower with h | ⟨i,mem,e⟩
    · simp [A,h] at hv
    · have last : A.getLast? = some L[i.val] := by
        change (L.take lo).getLast? = _
        rw [←e]
        exact (congrArg List.getLast? (List.take_succ_eq_append_getElem
          (l:=L) (i:=i.val) i.isLt)).trans List.getLast?_concat
      have same : L[i.val]=v := by simpa [last] using hv
      exact same ▸ (touch i mem).1
  have right : ∀ v∈B.head?, G.Adj y v := by
    intro v hv
    rcases upper with h | ⟨i,mem,e⟩
    · simp [B,L,h] at hv
    · have first : B.head?=some L[i.val] := by simp [B,←e,List.head?_drop]
      have same : L[i.val]=v := by simpa [first] using hv
      exact same ▸ (touch i mem).2.symm
  have length : q.support.length=J.length := by
    simp only [J,List.length_take,List.length_drop]
    rw [min_eq_left (Nat.sub_le_sub_right bound lo)]
    exact size.symm
  have witness : ∃ c, (c∈A ∨ c∈B) ∧ G.Adj x c ∧ ∃ v∈J, G.Adj c v := by
    rcases one with first|last
    · obtain zero | ⟨i,mem,e⟩ := lower
      · omega
      have edge := p.adj_getVert_succ (i:=i.val) (by have := p.length_support; omega)
      rw [e] at edge
      refine ⟨L[i.val],kept i (Or.inl (by omega)),(touch i mem).1.symm,
        p.getVert lo,inside lo le_rfl nonempty,?_⟩
      change G.Adj p.support[i.val] _
      rw [get_at p i.isLt]
      exact edge
    · obtain tail | ⟨i,mem,e⟩ := upper
      · omega
      have edge := p.adj_getVert_succ (i:=hi-1) (by have := p.length_support; omega)
      rw [show hi-1+1=hi by omega] at edge
      refine ⟨L[i.val],kept i (Or.inr e.ge),(touch i mem).1.symm,
        p.getVert (hi-1),inside _ (by omega) (by omega),?_⟩
      change G.Adj p.support[i.val] _
      rw [get_at p i.isLt,e]
      exact edge.symm
  obtain ⟨c,hc,cx,neighbor⟩ := witness
  have all := protected_swap_neighbors_with_route p hp _ A J B split (kept t safe) q hq dis length left right uniform hc neighbor
  intro i h
  exact ⟨c,cx,(all _ (inside i (mem_Ico.mp h).1 (mem_Ico.mp h).2)).symm⟩
theorem interval_exchange_witnesses (p : G.Walk a b) (hp : p.IsPath) (t : Fin p.support.length)
    (M : Finset (Fin p.support.length)) (q : G.Walk x y) (hq : q.IsPath)
    (dis : List.Disjoint q.support p.support)
    (touch : ∀ i ∈ M, G.Adj p.support[i.val] x ∧ G.Adj p.support[i.val] y)
    (uniform : ∀ {i j}, ∀ r : G.Walk i j, r.IsPath → p.support[t.val] ∈ r.support → r.length=p.length →
      ∀ c ∈ r.support, ∀ v ∉ r.support, ∀ w ∉ r.support, G.Adj c v → G.Adj c w)
    {lo hi : ℕ} (nonempty : lo < hi) (bound : hi ≤ p.support.length) (size : hi-lo=q.support.length)
    (safe : t.val < lo ∨ hi ≤ t.val) (lower : lo=0 ∨ ∃ i∈M, i.val+1=lo)
    (upper : hi=p.support.length ∨ ∃ i∈M, i.val=hi) (one : 0 < lo ∨ hi < p.support.length) :
    ∀ i ∈ Ico lo hi, ∃ w, G.Adj x w ∧ G.Adj (p.getVert i) w := by
  apply interval_exchange_witnesses_with_route p hp t M q hq dis touch _ nonempty bound size safe lower upper one
  exact fun r hr hz _ => uniform r hr hz
end Graph189ExteriorGap
end
section
open SimpleGraph Finset
namespace Graph189ExteriorGap
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {a b : V}
theorem two_mark_exchange (p : G.Walk a b) (hp : p.IsPath) (t : Fin p.support.length)
    (mx : ∀ {u v}, ∀ q : G.Walk u v, q.IsPath → p.support[t.val]∈q.support → q.length ≤ p.length)
    (E : Finset V) (many : 1 < E.card) (outside : ∀ {v}, v∈E → v∉p.support)
    (routes : ∀ x y : E, x≠y → ∃ q : (G.induce (E : Set V)).Walk x y, q.IsHamiltonian)
    (M : Finset (Fin p.support.length)) (sz : M.card=2)
    (links : ∀ w∈E, ∀ i : Fin p.support.length, G.Adj p.support[i.val] w ↔ i∈M)
    (common : ∀ {i j}, ∀ r : G.Walk i j, r.IsPath → p.support[t.val]∈r.support →
      r.length=p.length → ∀ v∈r.support, ∀ u∉r.support, ∀ w∉r.support, G.Adj v u → G.Adj v w)
    (room : p.support.length ≤ 2*E.card+4) (cap : ∀ x∈E, G.distEven x ≤ E.card+2) : False := by
  classical
  obtain ⟨x,hx⟩ := card_pos.mp (by omega : 0 < E.card)
  let X : E := ⟨x,hx⟩
  obtain ⟨y,hy,ne⟩ := exists_mem_ne many x
  let Y : E := ⟨y,hy⟩
  obtain ⟨w,hw⟩ := routes X Y (fun e => ne (congrArg Subtype.val e).symm)
  let inc := (Embedding.induce (G:=G) (E : Set V)).toHom
  let q := w.map inc
  have hq : q.IsPath := hw.isPath.map Subtype.val_injective
  have dis : List.Disjoint q.support p.support := by
    apply List.disjoint_left.mpr
    intro v hv
    rw [show q.support=w.support.map inc from Walk.support_map _ _] at hv
    obtain ⟨u,_,rfl⟩ := List.mem_map.mp hv
    exact outside u.property
  have qlen : q.support.length=E.card := by
    change (w.map inc).support.length=E.card
    rw [Walk.support_map,List.length_map,hw.length_support]
    exact Fintype.card_coe E
  have touch (i : Fin p.support.length) (hi : i∈M) :
      G.Adj p.support[i.val] x ∧ G.Adj p.support[i.val] y := ⟨(links x hx i).mpr hi,(links y hy i).mpr hi⟩
  let A := M.orderEmbOfFin (show M.card=1+1 from sz)
  have mem (i : Fin 2) : A i∈M := M.orderEmbOfFin_mem sz i
  have adj (i : Fin 2) := touch (A i) (mem i)
  have first := (protected_contact_internal p hp t mx (outside hx) _ (adj 0).1).1
  have last := (protected_contact_internal p hp t mx (outside hx) _ (adj (Fin.last 1)).1).2
  have space (i : Fin 1) := protected_contact_spacing p hp t mx (outside hx) _ _ (A.strictMono i.castSucc_lt_succ)
    (adj i.castSucc).1 (adj i.succ).1
  obtain ⟨lo,hi,nonempty,bound,len,safe,lb,ub,one,unmarked⟩ := locate_tight_protected_gap t M
    (j:=1) (m:=E.card) sz (by omega) first last space
    (fun h => by have ql := protected_prefix_of_detour p hp t mx _ h q hq dis (adj 0).2.symm; simpa only [qlen] using ql)
    (fun h => by have ql := protected_suffix_of_detour p hp t mx _ h q hq dis (adj _).1; simpa only [qlen] using ql)
    (fun i h => by have ql := protected_interval_of_detour p hp t mx _ _ (A.strictMono i.castSucc_lt_succ) h
                    q hq dis (adj i.castSucc).1 (adj i.succ).2.symm; simpa only [qlen] using ql)
    room
  have witnesses := interval_exchange_witnesses p hp t M q hq dis touch common nonempty bound
    (len.trans qlen.symm) safe lb ub one
  let I := A 0
  let J := A (Fin.last 1)
  have spaced : I.val+2 ≤ J.val := space 0
  have neq : I≠J := fun e => by rw [e] at spaced; omega
  have pair : M={I,J} := by
    symm
    apply eq_of_subset_of_card_le (by
      intro v hv
      rcases mem_insert.mp hv with rfl|h
      · exact mem 0
      obtain rfl := mem_singleton.mp h
      exact mem (Fin.last 1))
    rw [card_pair neq,sz]
  have mark : contactPositions p x = {I.val,J.val} := by
    ext l
    constructor
    · intro h
      obtain ⟨hl,edge⟩ := (mem_contactPositions p x l).mp h
      have inM := (links x hx ⟨l,hl⟩).mp (by simpa [get_at] using edge)
      rw [pair] at inM
      simpa only [mem_insert,mem_singleton,Fin.ext_iff] using inM
    · intro h
      rcases mem_insert.mp h with rfl|other
      · exact (mem_contactPositions p x I.val).mpr ⟨I.isLt,by simpa [get_at] using (adj 0).1⟩
      have e := mem_singleton.mp other
      subst l
      exact (mem_contactPositions p x J.val).mpr ⟨J.isLt,by rw [←get_at p J.isLt]; exact (adj (Fin.last 1)).1⟩
  have range : lo+E.card=hi := by rw [←len,Nat.add_sub_of_le nonempty.le]
  refine Graph189FourTerminalGap.impossible_of_length p hp (outside hx) (i:=I.val) (j:=J.val) (lo:=lo) (hi:=hi) first spaced last mark bound range ?_ witnesses ?_
  · intro l hl
    have h := mem_Ico.mp hl
    have old := unmarked I (mem 0)
    have next := unmarked J (mem (Fin.last 1))
    omega
  · exact cap x hx
end Graph189ExteriorGap
end
section
open Finset SimpleGraph
namespace Graph189ExteriorAttachment
theorem extra_port {V : Type*} {G : SimpleGraph V} [DecidableRel G.Adj] {x y : V}
    (p : G.Walk x y) (W : Finset V) (j : ℕ) (many : j < W.card)
    (rows : ∀ w ∈ W, j ≤ ((univ : Finset (Fin p.support.length)).filter
      (fun i => G.Adj p.support[i.val] w)).card)
    (cover : j < (W.biUnion (fun w => (univ : Finset (Fin p.support.length)).filter
      (fun i => G.Adj p.support[i.val] w))).card) :
    ∃ marks : Finset (Fin p.support.length), marks.card = j+1 ∧
      ∃ attach : marks ↪ W, ∀ i : marks, G.Adj p.support[i.val.val] (attach i).val := by
  classical
  let N (w : V) := (univ : Finset (Fin p.support.length)).filter (fun i => G.Adj p.support[i.val] w)
  let F (w : W) := N w.val
  have size : Fintype.card W = W.card := Fintype.card_coe W
  have whole : (univ.biUnion F).card = (W.biUnion N).card := by
    congr 1
    ext i
    constructor
    · intro hi
      obtain ⟨w,_,hw⟩ := mem_biUnion.mp hi
      exact mem_biUnion.mpr ⟨w.val,w.property,hw⟩
    · intro hi
      obtain ⟨w,hw,edge⟩ := mem_biUnion.mp hi
      exact mem_biUnion.mpr ⟨⟨w,hw⟩,mem_univ _,edge⟩
  have hall (T : Finset W) : T.card ≤ (T.biUnion F).card + (Fintype.card W-(j+1)) := by
    by_cases all : T=univ
    · rw [all,card_univ,whole,size]
      change j < (W.biUnion N).card at cover
      omega
    rcases T.eq_empty_or_nonempty with rfl | ⟨w,hw⟩
    · simp
    have proper : T.card < W.card := by
      by_contra! h
      exact all (Finset.eq_of_subset_of_card_le (subset_univ _) (by simpa using h))
    have incl : F w ⊆ T.biUnion F := fun i hi => mem_biUnion.mpr ⟨w,hw,hi⟩
    have lower := (rows w.val w.property).trans (card_le_card incl)
    omega
  obtain ⟨U,large,f,edge⟩ := Graph189ExteriorGap.hall_at_least F (j+1) (by omega) hall
  obtain ⟨B,sub,cardB⟩ := exists_subset_card_eq large
  let inc : B ↪ U := ⟨fun b => ⟨b.val,sub b.property⟩,
    fun _ _ e => Subtype.ext (congrArg (fun w : U => w.val) e)⟩
  let pos := inc.trans f
  let M := (univ : Finset B).image pos
  let chosen (b : B) : M := ⟨pos b,mem_image_of_mem _ (mem_univ _)⟩
  have bij : Function.Bijective chosen := by
    constructor
    · intro u v eq
      exact pos.injective (congrArg Subtype.val eq)
    · intro i
      obtain ⟨b,_,eq⟩ := mem_image.mp i.property
      exact ⟨b,Subtype.ext eq⟩
  let equiv := Equiv.ofBijective chosen bij
  let vertex : B ↪ W := ⟨Subtype.val,Subtype.val_injective⟩
  have card : M.card = B.card := by simpa using Fintype.card_congr equiv.symm
  refine ⟨M,card.trans cardB,equiv.symm.toEmbedding.trans vertex,?_⟩
  intro i
  have value : pos (equiv.symm i) = i.val := congrArg Subtype.val (equiv.apply_symm_apply i)
  have adj := (mem_filter.mp (edge (inc (equiv.symm i)))).2
  change G.Adj p.support[(pos (equiv.symm i)).val] (equiv.symm i).val.val at adj
  exact (congrArg (fun index : Fin p.support.length =>
    G.Adj (p.support.get index) (equiv.symm i).val.val) value).mp adj
end Graph189ExteriorAttachment
end
section
open SimpleGraph Finset
namespace Graph189LayerCover
variable {V : Type*} [Fintype V]
noncomputable def layer (G : SimpleGraph V) (z : V) (n : ℕ) : Finset V := by
  classical
  exact univ.filter (fun v => G.dist z v = n)
@[simp] theorem in_layer {G : SimpleGraph V} {z y : V} {n : ℕ} :
    y ∈ layer G z n ↔ G.dist z y = n := by classical simp [layer]
private theorem minimal_cover (A B : Finset V) (R : V → V → Prop)
    (hc : ∀ b ∈ B, ∃ a ∈ A, R a b) :
    ∃ T ⊆ A, (∀ b ∈ B, ∃ a ∈ T, R a b) ∧
      ∀ a ∈ T, ∃ b ∈ B, R a b ∧ ∀ a' ∈ T, a' ≠ a → ¬ R a' b := by
  classical
  let covers (S : Finset V) := ∀ b ∈ B, ∃ a ∈ S, R a b
  let family := A.powerset.filter covers
  have ha : A ∈ family := mem_filter.mpr ⟨mem_powerset.mpr (fun _ h => h), hc⟩
  obtain ⟨T,hT,hmin⟩ := family.exists_min_image Finset.card ⟨A,ha⟩
  obtain ⟨hsub,hcovers⟩ := mem_filter.mp hT
  have hsub' := mem_powerset.mp hsub
  refine ⟨T,hsub',hcovers,?_⟩
  intro a haT
  have missing : ¬ covers (T.erase a) := by
    intro h
    have hs : T.erase a ∈ family := mem_filter.mpr
      ⟨mem_powerset.mpr ((erase_subset a T).trans hsub'),h⟩
    exact (not_le_of_gt (card_erase_lt_of_mem haT)) (hmin _ hs)
  change ¬ (∀ b ∈ B, ∃ a' ∈ T.erase a, R a' b) at missing
  push Not at missing
  obtain ⟨b,hb,hprivate⟩ := missing
  obtain ⟨x,hx,hxb⟩ := hcovers b hb
  have hxa : x = a := by
    by_contra h
    exact hprivate x (mem_erase.mpr ⟨h,hx⟩) hxb
  exact ⟨b,hb,hxa ▸ hxb,fun a' ha' hdiff => hprivate a' (mem_erase.mpr ⟨hdiff,ha'⟩)⟩
omit [Fintype V] in
private theorem predecessor {G : SimpleGraph V} {z y : V} {d : ℕ}
    (h : G.dist z y = d+1) : ∃ p, G.dist z p = d ∧ G.Adj p y := by
  have hr : G.dist y z = d+1 := by rwa [dist_comm]
  have hpos : G.Reachable y z := Reachable.of_dist_ne_zero (by omega)
  obtain ⟨walk,hlen⟩ := hpos.exists_walk_length_eq_dist
  cases walk with
  | nil => simp at h
  | cons hy tail =>
    rename_i p
    have hlen' : tail.length = d := by rw [Walk.length_cons,hr] at hlen; omega
    have hle : G.dist z p ≤ d := by rw [dist_comm]; exact hlen' ▸ G.dist_le tail
    have ht := hy.diff_dist_adj (u := z)
    exact ⟨p,by omega,hy.symm⟩
omit [Fintype V] in
private theorem dist_two {G : SimpleGraph V} {x y q : V}
    (hne : x ≠ y) (hna : ¬G.Adj x y) (h1 : G.Adj x q) (h2 : G.Adj q y) :
    G.dist x y = 2 := by
  let w : G.Walk x y := .cons h1 (.cons h2 .nil)
  have hlo := w.reachable.one_lt_dist_of_ne_of_not_adj hne hna
  have hhi : G.dist x y ≤ 2 := G.dist_le w
  omega
omit [Fintype V] in
private theorem second_step {G : SimpleGraph V} (hc : G.Connected) (z y : V)
    (h : 2 ≤ G.dist z y) : ∃ b, G.dist z b = 2 ∧ G.dist z y = 2 + G.dist b y := by
  generalize hd : G.dist z y = d at h ⊢
  induction d using Nat.strong_induction_on generalizing y with
  | h d ih =>
    by_cases e : d=2
    · exact ⟨y,hd.trans e,by simp [e]⟩
    · obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show d≠0 by omega)
      obtain ⟨p,hp,hpy⟩ := predecessor hd
      obtain ⟨b,hb,split⟩ := ih m (by omega) p hp (by omega)
      have up := hc.dist_triangle (u:=b) (v:=p) (w:=y)
      rw [dist_eq_one_iff_adj.mpr hpy] at up
      have low := hc.dist_triangle (u:=z) (v:=b) (w:=y)
      exact ⟨b,hb,by omega⟩
theorem order_of_cover (G : SimpleGraph V) [DecidableRel G.Adj] (hc : G.Connected)
    (z : V) (k : ℕ) (cap : ∀ v, G.distEven v ≤ k+1) (R : Finset V)
    (arms : ∀ a ∈ R, G.Adj z a)
    (covers : ∀ b ∈ layer G z 2, ∃ a ∈ R, G.Adj a b) :
    ∃ t ≤ R.card, t ≤ k+1 ∧ Fintype.card V ≤ 1+G.degree z+k+t*(k+1-t) := by
  classical
  obtain ⟨T,hTR,hTc,hTp⟩ := minimal_cover R (layer G z 2) G.Adj covers
  let port (a : V) : V := if h : a ∈ T then (hTp a h).choose else z
  have hp (a : V) (h : a ∈ T) : G.dist z (port a) = 2 ∧ G.Adj a (port a) ∧
      ∀ a' ∈ T, a' ≠ a → ¬ G.Adj a' (port a) := by
    simpa [port,h] using (hTp a h).choose_spec
  have hA (a : V) (h : a ∈ T) : G.dist z a = 1 := dist_eq_one_iff_adj.mpr (arms a (hTR h))
  let evenSet (a : V) := (univ.filter (fun v => Even (G.dist a v))).erase a
  have quota (a : V) : (evenSet a).card ≤ k := by
    have self : a ∈ univ.filter (fun v => Even (G.dist a v)) := by simp
    have bound := cap a
    change (univ.filter (fun v => Even (G.dist a v))).card ≤ k+1 at bound
    unfold evenSet
    rw [card_erase_of_mem self]
    omega
  have evenMem {a v : V} (n : a ≠ v) (ev : Even (G.dist a v)) : v ∈ evenSet a :=
    mem_erase.mpr ⟨Ne.symm n, mem_filter.mpr ⟨mem_univ _,ev⟩⟩
  let F := univ.filter (fun v => 3 ≤ G.dist z v ∧ ¬ Even (G.dist z v))
  let W (a : V) := F.filter (fun c => c ∈ evenSet a)
  have cov : F ⊆ T.biUnion W := by
    intro c hcF
    obtain ⟨far,odd⟩ := (mem_filter.mp hcF).2
    obtain ⟨b,hb,hsplit⟩ := second_step hc z c (by omega)
    obtain ⟨a,ha,hab⟩ := hTc b (in_layer.mpr hb)
    have upper := hc.dist_triangle (u:=a) (v:=b) (w:=c)
    rw [dist_eq_one_iff_adj.mpr hab] at upper
    have lower := hc.dist_triangle (u:=z) (v:=a) (w:=c)
    have unit := hA a ha
    have distinct : a ≠ c := by rintro rfl; omega
    have even : Even (G.dist a c) := by rw [Nat.even_iff] at odd ⊢; omega
    exact mem_biUnion.mpr ⟨a,ha,mem_filter.mpr ⟨hcF,evenMem distinct even⟩⟩
  have row (a : V) (ha : a ∈ T) : (W a).card + T.card ≤ k+1 := by
    let f (j : V) := if G.Adj a j then port j else j
    have hzj (j : V) (hj : j ∈ T) : G.dist z (f j) ≤ 2 := by
      by_cases h : G.Adj a j <;> simp [f,h,(hp j hj).1,hA j hj]
    have finj : Set.InjOn f ↑(T.erase a) := by
      intro j hj l hl hEq
      obtain ⟨_,hjT⟩ := mem_erase.mp hj
      obtain ⟨_,hlT⟩ := mem_erase.mp hl
      by_cases hjA : G.Adj a j <;> by_cases hlA : G.Adj a l <;> simp [f,hjA,hlA] at hEq
      · by_contra hne
        exact (hp l hlT).2.2 j hjT hne (hEq ▸ (hp j hjT).2.1)
      · have h1 := (hp j hjT).1; have h2 := hA l hlT; rw [hEq] at h1; omega
      · have h1 := (hp l hlT).1; have h2 := hA j hjT; rw [hEq] at h2; omega
      · exact hEq
    let E := (T.erase a).image f
    have heq : E.card = (T.erase a).card := card_image_of_injOn finj
    have hdis : Disjoint (W a) E := by
      apply Finset.disjoint_left.mpr
      intro x hx hw
      obtain ⟨j,hj,rfl⟩ := mem_image.mp hw
      have h1 := (mem_filter.mp (mem_filter.mp hx).1).2.1
      have h2 := hzj j (mem_erase.mp hj).2
      omega
    have incl : W a ∪ E ⊆ evenSet a := by
      intro x hx
      rcases mem_union.mp hx with hw|he
      · exact (mem_filter.mp hw).2
      · obtain ⟨j,hj,rfl⟩ := mem_image.mp he
        obtain ⟨hne,hj⟩ := mem_erase.mp hj
        suffices hd : G.dist a (f j) = 2 by
          apply evenMem _ (by simp [hd])
          intro eq
          rw [← eq, SimpleGraph.dist_self] at hd
          omega
        by_cases haj : G.Adj a j
        · simp only [f,if_pos haj]
          have hza := hA a ha
          have hzj' := (hp j hj).1
          apply dist_two _ ((hp j hj).2.2 a ha hne.symm) haj (hp j hj).2.1
          rintro heq'; rw [heq'] at hza; omega
        · simp only [f,if_neg haj]
          exact dist_two hne.symm haj (dist_eq_one_iff_adj.mp (hA a ha)).symm
            (dist_eq_one_iff_adj.mp (hA j hj))
    have hcount := (card_le_card incl).trans (quota a)
    rw [card_union_of_disjoint hdis,heq] at hcount
    have he := card_erase_add_one ha
    omega
  have hsize : T.card ≤ k+1 := by
    rcases T.eq_empty_or_nonempty with he|⟨a,ha⟩
    · simp [he]
    · have := row a ha; omega
  have farCount : F.card ≤ T.card*(k+1-T.card) := by
    calc F.card ≤ (T.biUnion W).card := card_le_card cov
         _ ≤ ∑ a ∈ T, (W a).card := card_biUnion_le
         _ ≤ ∑ _ ∈ T, (k+1-T.card) := sum_le_sum (fun a ha => by have := row a ha; omega)
         _ = T.card*(k+1-T.card) := by simp
  have all : (univ : Finset V) ⊆ (({z} ∪ G.neighborFinset z) ∪ evenSet z) ∪ F := by
    intro v hv
    by_cases same : v = z
    · subst v; simp
    by_cases adj : G.Adj z v
    · exact mem_union_left _ (mem_union_left _ (mem_union_right _ ((G.mem_neighborFinset z v).mpr adj)))
    by_cases e : Even (G.dist z v)
    · exact mem_union_left _ (mem_union_right _ (evenMem (Ne.symm same) e))
    have pos := (hc z v).one_lt_dist_of_ne_of_not_adj (Ne.symm same) adj
    exact mem_union_right _ (mem_filter.mpr ⟨hv,by rw [Nat.even_iff] at e; omega, e⟩)
  have one := card_union_le ({z} : Finset V) (G.neighborFinset z)
  have two := card_union_le ({z} ∪ G.neighborFinset z) (evenSet z)
  have three := card_union_le (({z} ∪ G.neighborFinset z) ∪ evenSet z) F
  have hcard := card_le_card all
  rw [card_univ] at hcard
  simp only [card_singleton,G.card_neighborFinset_eq_degree] at one
  exact ⟨T.card,card_le_card hTR,hsize,by have h := quota z; omega⟩
end Graph189LayerCover
end
section
open SimpleGraph Finset
namespace Graph189LayerCutoff
variable {V : Type*} [Fintype V]
private theorem row_mono {a t k : ℕ} (hta : t ≤ a) (ha : 2*a ≤ k+1) :
    t*(k+1-t) ≤ a*(k+1-a) := by
  have ht : t ≤ k+1 := by omega
  have hak : a ≤ k+1 := by omega
  have hsum : a+t ≤ k+1 := by omega
  have h : 0 ≤ (a-t : ℤ) * ((k:ℤ)+1-a-t) :=
    mul_nonneg (by omega) (by omega)
  zify [ht, hak]
  nlinarith
theorem order_of_small_cover (G : SimpleGraph V) [DecidableRel G.Adj] (hc : G.Connected)
    (z : V) (k : ℕ) (cap : ∀ v, G.distEven v ≤ k+1) (R : Finset V)
    (arms : ∀ a ∈ R, G.Adj z a)
    (covers : ∀ b ∈ Graph189LayerCover.layer G z 2, ∃ a ∈ R, G.Adj a b)
    (hs : 2*R.card ≤ k+1) :
    Fintype.card V ≤ 1+G.degree z+k+R.card*(k+1-R.card) := by
  obtain ⟨t, hta, _, horder⟩ := Graph189LayerCover.order_of_cover G hc z k cap R arms covers
  exact horder.trans (Nat.add_le_add_left (row_mono hta hs) _)
theorem order_of_small_degree (G : SimpleGraph V) [DecidableRel G.Adj] (hc : G.Connected)
    (z : V) (k : ℕ) (cap : ∀ v, G.distEven v ≤ k+1) (hs : 2*G.degree z ≤ k+1) :
    Fintype.card V ≤ 1+G.degree z+k+G.degree z*(k+1-G.degree z) := by
  classical
  have covers : ∀ b ∈ Graph189LayerCover.layer G z 2, ∃ a ∈ G.neighborFinset z, G.Adj a b := by
    intro b hb
    have two := Graph189LayerCover.in_layer.mp hb
    obtain ⟨walk, hlen⟩ := (hc b z).exists_walk_length_eq_dist
    have hdist : G.dist b z = 2 := by rwa [dist_comm]
    rw [hdist] at hlen
    cases walk with
    | nil => simp at hlen
    | cons e walk =>
      rename_i a
      have hlen' : walk.length = 1 := by rw [Walk.length_cons] at hlen; omega
      have hle : G.dist z a ≤ 1 := by rw [dist_comm]; exact hlen' ▸ G.dist_le walk
      have had := e.diff_dist_adj (u := z)
      exact ⟨a, (G.mem_neighborFinset z a).mpr (dist_eq_one_iff_adj.mp (by omega)), e.symm⟩
  simpa only [G.card_neighborFinset_eq_degree] using
    (order_of_small_cover G hc z k cap (G.neighborFinset z)
      (fun a ha => (G.mem_neighborFinset z a).mp ha) covers (by simpa using hs))
end Graph189LayerCutoff
end
section
open Finset SimpleGraph
open OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1
namespace Graph189ExteriorGap
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {a b : V}
theorem uniform_contacts_of_order (Q : G.Walk a b) (hQ : Q.IsPath)
    (t : Fin Q.support.length)
    (maximal : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → Q.support[t.val] ∈ r.support → r.length ≤ Q.length)
    (E : Finset V) (outside : ∀ w ∈ E, w ∉ Q.support) (many : 1 < E.card)
    (routes : ∀ x y : E, x ≠ y → ∃ q : (G.induce (E : Set V)).Walk x y, q.IsHamiltonian)
    (s : ℕ) (small : s < E.card) (upper : Fintype.card V < (s+2)*E.card+(s+1))
    (rows : ∀ v ∈ E, s ≤ ((univ : Finset (Fin Q.support.length)).filter
      (fun i => G.Adj Q.support[i.val] v)).card) :
    ∃ marks : Finset (Fin Q.support.length), marks.card = s ∧
      ∀ w ∈ E, ∀ i : Fin Q.support.length, G.Adj Q.support[i.val] w ↔ i ∈ marks := by
  classical
  let N (w : V) := (univ : Finset (Fin Q.support.length)).filter (fun i => G.Adj Q.support[i.val] w)
  let A := E.biUnion N
  have bound : A.card ≤ s := by
    by_contra! extra
    obtain ⟨marks,number,f,edge⟩ := Graph189ExteriorAttachment.extra_port Q E s small rows extra
    have order := protected_hamilton_connected_matching Q hQ t maximal E many outside routes marks
      (card_pos.mp (by omega)) f edge
    rw [number] at order
    exact (not_lt_of_ge order) upper
  have incl {w : V} (hw : w ∈ E) : N w ⊆ A := fun _ hi => mem_biUnion.mpr ⟨w,hw,hi⟩
  have same {w : V} (hw : w ∈ E) : N w = A :=
    eq_of_subset_of_card_le (incl hw) (bound.trans (rows w hw))
  obtain ⟨w,hw⟩ := card_pos.mp (show 0 < E.card by omega)
  exact ⟨A,le_antisymm bound ((rows w hw).trans (card_le_card (incl hw))),fun v hv i => by
    rw [← same hv]
    simp [N]⟩
theorem exterior_clique_of_common_contacts (Q : G.Walk a b)
    (marks : Finset (Fin Q.support.length)) (k : ℕ)
    (fits : (Q.support.toFinsetᶜ : Finset V).card+marks.card ≤ k+1)
    (high : ∀ w ∈ (Q.support.toFinsetᶜ : Finset V), k ≤ G.degree w)
    (contacts : ∀ w ∈ (Q.support.toFinsetᶜ : Finset V), ∀ i : Fin Q.support.length,
      G.Adj Q.support[i.val] w → i ∈ marks) :
    G.IsClique ((Q.support.toFinsetᶜ : Finset V) : Set V) := by
  classical
  let E := (Q.support.toFinsetᶜ : Finset V)
  let A := marks.image (fun i => Q.support[i.val])
  have small : A.card ≤ marks.card := card_image_le
  intro w hw v hv ne
  change w ∈ E at hw
  change v ∈ E at hv
  let candidates := E.erase w ∪ A
  have included : G.neighborFinset w ⊆ candidates := by
    intro x hx
    have edge := (G.mem_neighborFinset _ _).mp hx
    by_cases h : x ∈ E
    · exact mem_union_left _ (mem_erase.mpr ⟨edge.ne.symm,h⟩)
    have member : x ∈ Q.support := by simpa [E] using h
    obtain ⟨i,hi,value⟩ := List.mem_iff_getElem.mp member
    let pos : Fin Q.support.length := ⟨i,hi⟩
    have marked := contacts w hw pos (by simpa [pos,value] using edge.symm)
    exact mem_union_right _ (mem_image.mpr ⟨pos,marked,value⟩)
  have cap := card_union_le (E.erase w) A
  have erased := card_erase_add_one hw
  have large := high w hw
  rw [←G.card_neighborFinset_eq_degree] at large
  change E.card+marks.card ≤ k+1 at fits
  have all : G.neighborFinset w = candidates :=
    eq_of_subset_of_card_le included (by change candidates.card ≤ _ at cap; omega)
  apply (G.mem_neighborFinset _ _).mp
  rw [all]
  exact mem_union_left _ (mem_erase.mpr ⟨ne.symm,hv⟩)
variable [Nontrivial V]
end Graph189ExteriorGap
end
section
open SimpleGraph Finset
namespace Graph189ParentConnectivity
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]
theorem two_of_deletions (hc : G.Connected) (order : 3 ≤ Fintype.card V)
    (deletion : ∀ z : V, (G.induce {v : V | v≠z}).Connected) : 2 ≤ G.vertexConnectivity := by
  classical
  let M : Set ℕ := {j | ∃ S : Finset V, S.card=j ∧
    (¬(G.induce ((S : Set V)ᶜ)).Connected ∨ S.card=Fintype.card V-1)}
  have h : G.vertexConnectivity=sInf M := by
    unfold vertexConnectivity
    rw [if_neg (by omega : ¬Fintype.card V≤1)]
  obtain ⟨z⟩ := hc.nonempty
  have ex : M.Nonempty := ⟨_,univ.erase z,rfl,Or.inr (by simp)⟩
  rw [h]
  obtain ⟨T,sz,bad|full⟩ := Nat.sInf_mem ex
  · by_contra! small
    apply bad
    change (G.induce {v : V | v∉T}).Connected
    by_cases empty : T=∅
    · subst T
      rw [show {v : V | v∉(∅ : Finset V)}=Set.univ by ext; simp]
      exact hc.map G.induceUnivIso.symm.toHom G.induceUnivIso.symm.surjective
    obtain ⟨v,rfl⟩ := card_eq_one.mp (show T.card=1 by
      have := card_pos.mpr (nonempty_iff_ne_empty.mpr empty)
      omega)
    rw [show {w : V | w∉({v} : Finset V)}={w : V | w≠v} by ext; simp]
    exact deletion v
  · omega
end Graph189ParentConnectivity
end
section
open SimpleGraph Finset Graph189ExteriorGap
namespace Graph189TwoExteriorLinks
variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} {x y : V}
structure Arm (p : G.Walk x y) (W : Finset V) where
  mark : Fin p.support.length
  root : V
  inside : root∈W
  port : V
  contact : G.Adj port p.support[mark.val]
  route : G.Walk root port
  simple : route.IsPath
  off : ∀ v∈route.support, v∉p.support
  away : ∀ v∈route.support.tail, v∉W
theorem arm_of_list (p : G.Walk x y) {W : Finset V}
    (apart : ∀ v∈W, v∉p.support) {l : List V}
    (h : OMA.BondyK.ABP G W p.support.toFinset l ∧
      (∀ v∈l.tail, v∉W) ∧ (∀ v∈l.dropLast,v∉p.support.toFinset)) :
    ∃ a : Arm p W, (∀ v∈a.route.support, v∈l) ∧ p.support[a.mark.val]∈l := by
  obtain ⟨⟨nd,ch,⟨r,hr,first⟩,⟨b,hb,last⟩⟩,tail,lastOff⟩ := h
  have ne : l≠[] := by intro e; simp [e] at first
  have split : l=l.dropLast++[b] := by
    rw [List.getLast?_eq_getLast_of_ne_nil ne,Option.some.injEq] at last
    rw [←last,List.dropLast_append_getLast]
  let M := l.dropLast
  have mne : M≠[] := by
    intro eq
    change l.dropLast=[] at eq
    rw [split,eq] at first
    simp only [List.nil_append,List.head?_cons,Option.some.injEq] at first
    exact apart r hr (first ▸ List.mem_toFinset.mp hb)
  have hd : M.head mne=r := by
    have e : l=M++[b] := split
    rw [e,List.head?_append,List.head?_eq_some_head mne] at first
    simpa using first
  have dc := nd
  have cc := ch
  change l=M++[b] at split
  rw [split] at dc cc
  have subch := (List.isChain_append.mp cc).1
  let q := Walk.ofSupport M mne subch
  have supp : q.support=M := Walk.support_ofSupport mne subch
  let j : Fin p.support.length := ⟨p.support.idxOf b,List.idxOf_lt_length_iff.mpr (List.mem_toFinset.mp hb)⟩
  have mark : p.support[j.val]=b := List.getElem_idxOf j.isLt
  have touch : G.Adj (M.getLast mne) p.support[j.val] := by
    rw [mark]
    exact (List.isChain_append.mp cc).2.2 _ (List.getLast?_eq_getLast_of_ne_nil mne) _ rfl
  let a : Arm p W := {
    mark := j
    root := M.head mne
    inside := hd ▸ hr
    port := M.getLast mne
    contact := touch
    route := q
    simple := Walk.IsPath.mk' (by rw [supp]; exact dc.of_append_left)
    off := by
      intro v hv hit
      rw [supp] at hv
      exact lastOff v hv (List.mem_toFinset.mpr hit)
    away := by
      intro v hv
      rw [supp] at hv
      apply tail
      rw [split,List.tail_append_of_ne_nil mne]
      exact List.mem_append_left _ hv }
  refine ⟨a,?_,?_⟩
  · intro v hv
    change v∈q.support at hv
    rw [supp] at hv
    rw [split]
    exact List.mem_append_left _ hv
  · change p.support[j.val]∈l
    rw [mark]
    exact List.mem_of_getLast? last
omit [DecidableEq V] in
private theorem Arm.start {p : G.Walk x y} {W : Finset V} (a : Arm p W)
    (outside : ∀ v∈W, v∉p.support) {b : V} (q : G.Walk a.root b) (hq : q.IsPath)
    (uses : ∀ v∈q.support, v∈W) :
    (a.route.reverse.append q).IsPath ∧
      ∀ v∈(a.route.reverse.append q).support, v∉p.support := by
  constructor
  · apply Walk.IsPath.mk'
    rw [Walk.support_append_eq_support_dropLast_append,Walk.support_reverse,List.dropLast_reverse]
    apply List.Nodup.append (by simpa using a.simple.support_nodup.tail) hq.support_nodup
    intro u hu hv
    exact a.away u (List.mem_reverse.mp hu) (uses u hv)
  · intro v hv
    rcases (Walk.mem_support_append_iff _ _).mp hv with ha|hb
    · exact a.off v (by simpa using ha)
    · exact outside v (uses v hb)
omit [DecidableEq V] in
theorem ordered_positions {p : G.Walk x y} (hp : p.IsPath)
    (longest : ∀ {u v}, ∀ q : G.Walk u v, q.IsPath → q.length ≤ p.length)
    {W : Finset V} (outside : ∀ v∈W, v∉p.support)
    (a b : Arm p W) (before : a.mark < b.mark)
    (distinct : ∀ v∈a.route.support, v∉b.route.support) {m t : ℕ}
    (start : ∀ r∈W, ∃ u, ∃ q : G.Walk r u, q.IsPath ∧ m ≤ q.support.length ∧ ∀ v∈q.support,v∈W)
    (join : ∀ r∈W, ∀ s∈W, r≠s → ∃ q : G.Walk r s, q.IsPath ∧ t ≤ q.support.length ∧ ∀ v∈q.support,v∈W) :
    m ≤ a.mark.val ∧ a.mark.val+1+t ≤ b.mark.val ∧ b.mark.val+1+m ≤ p.support.length := by
  obtain ⟨_,q1,h1,len1,W1⟩ := start a.root a.inside
  obtain ⟨h1',off1⟩ := a.start outside q1 h1 W1
  obtain ⟨_,q2,h2,len2,W2⟩ := start b.root b.inside
  obtain ⟨h2',off2⟩ := b.start outside q2 h2 W2
  have localDis {i j} (q : G.Walk i j) (h : ∀ v∈q.support,v∉p.support) :
      List.Disjoint q.support p.support := List.disjoint_left.mpr h
  have l := prefix_of_detour p hp longest a.mark (a.route.reverse.append q1).reverse h1'.reverse
    (by
      apply List.disjoint_left.mpr
      intro v hv
      rw [Walk.support_reverse,List.mem_reverse] at hv
      exact off1 v hv) a.contact
  have r := suffix_of_detour p hp longest b.mark _ h2' (localDis _ off2) b.contact.symm
  have diff : a.root≠b.root := by
    intro eq
    apply distinct _ a.route.start_mem_support
    rw [eq]
    exact b.route.start_mem_support
  obtain ⟨q,hq,len,mem⟩ := join a.root a.inside b.root b.inside diff
  obtain ⟨path,dis⟩ := a.start outside q hq mem
  let T := (a.route.reverse.append q).append b.route
  have pathT : T.IsPath := by
    apply Walk.IsPath.mk'
    rw [show T=(a.route.reverse.append q).append b.route from rfl,Walk.support_append]
    apply List.Nodup.append path.support_nodup b.simple.support_nodup.tail
    intro u hu hv
    rcases (Walk.mem_support_append_iff _ _).mp hu with ha|hh
    · exact distinct u (by simpa using ha) (List.mem_of_mem_tail hv)
    · exact b.away u hv (mem u hh)
  have disT : List.Disjoint T.support p.support := by
    apply List.disjoint_left.mpr
    intro v hv
    rcases (Walk.mem_support_append_iff _ _).mp hv with h|h
    · exact dis v h
    · exact b.off v h
  have inner := interval_of_detour p hp longest a.mark b.mark before T pathT disT a.contact.symm b.contact
  have plen := p.length_support
  simp only [T,Walk.length_support,Walk.length_append,Walk.length_reverse] at l r inner len1 len2 len
  exact ⟨by omega,by omega,by omega⟩
theorem arms [Fintype V] [Nontrivial V] [DecidableRel G.Adj]
    (p : G.Walk x y) (hp : p.IsPath) (W : Finset V) (outside : ∀ v∈W,v∉p.support)
    (count : ℕ) (conn : count ≤ G.vertexConnectivity) (wide : count ≤ W.card) (longP : count ≤ p.support.length) :
    ∃ A : Fin count→Arm p W, Function.Injective (fun i => (A i).mark) ∧
      ∀ i j, i≠j → ∀ v∈(A i).route.support,v∉(A j).route.support := by
  classical
  let P := p.support.toFinset
  have szP : count ≤ P.card := by
    rw [show P=p.support.toFinset from rfl,List.toFinset_card_of_nodup hp.support_nodup]
    exact longP
  obtain ⟨L,hL,separate⟩ := OMA.BondyK.menger_trim (G:=G) W P count (by
    intro S separates
    by_contra! small
    have leftover (T : Finset V) (big : count ≤ T.card) : ∃ v∈T,v∉S := by
      by_contra! inc
      have := card_le_card (show T⊆S from inc)
      omega
    obtain ⟨r,hr,rS⟩ := leftover W wide
    obtain ⟨b,hb,bS⟩ := leftover P szP
    obtain ⟨q,hq⟩ := (Graph189CutSides.connected_after_smaller_deletion (G:=G) S (small.trans_le conn)).exists_isPath
      (⟨r,rS⟩ : {v : V | v∉S}) ⟨b,bS⟩
    obtain ⟨v,hv,vs⟩ := separates (q.support.map Subtype.val) ⟨hq.support_nodup.map Subtype.val_injective,
      (List.isChain_map Subtype.val).mpr q.isChain_adj_support,
      ⟨r,hr,by rw [←q.cons_tail_support,List.map_cons,List.head?_cons]⟩,
      ⟨b,hb,by rw [List.getLast?_map,List.getLast?_eq_getLast_of_ne_nil q.support_ne_nil,q.getLast_support]; rfl⟩⟩
    obtain ⟨v,_,rfl⟩ := List.mem_map.mp hv
    exact v.property vs)
  choose A included ends using fun i => arm_of_list p outside (hL i)
  refine ⟨A,?_,fun i j ne v hi hj => separate i j ne v (included i v hi) (included j v hj)⟩
  intro i j eq
  by_contra ne
  apply separate i j ne _ (ends i)
  change (A i).mark=(A j).mark at eq
  simpa only [eq] using ends j
theorem path_of_routes [Fintype V] [Nontrivial V] [DecidableRel G.Adj]
    (p : G.Walk x y) (hp : p.IsPath)
    (longest : ∀ {u v}, ∀ q : G.Walk u v, q.IsPath → q.length ≤ p.length)
    (conn : 2 ≤ G.vertexConnectivity) (W : Finset V) (outside : ∀ v∈W,v∉p.support)
    (wide : 2 ≤ W.card) (longP : 2 ≤ p.support.length) {m t : ℕ}
    (start : ∀ r∈W, ∃ u, ∃ q : G.Walk r u, q.IsPath ∧ m ≤ q.support.length ∧ ∀ v∈q.support,v∈W)
    (join : ∀ r∈W, ∀ s∈W, r≠s → ∃ q : G.Walk r s, q.IsPath ∧ t ≤ q.support.length ∧ ∀ v∈q.support,v∈W) :
    2*m+t+2 ≤ p.support.length := by
  classical
  obtain ⟨A,inj,separate⟩ := arms p hp W outside 2 conn wide longP
  let a := A 0
  let b := A 1
  have dis := separate 0 1 (by decide)
  have diff : a.mark≠b.mark := fun eq => (show (0:Fin 2)≠1 by decide) (inj eq)
  rcases lt_or_gt_of_ne diff with ab|ba
  · obtain ⟨l,mid,r⟩ := ordered_positions hp longest outside a b ab dis start join
    omega
  · obtain ⟨l,mid,r⟩ := ordered_positions hp longest outside b a ba (fun v hb ha => dis v ha hb) start join
    omega
theorem cycle_routes {r : V} (C : G.Walk r r) (hc : C.IsCycle) :
    let W := C.support.toFinset
    C.length ≤ W.card ∧
    (∀ a∈W, ∃ u, ∃ q : G.Walk a u, q.IsPath ∧ C.length ≤ q.support.length ∧ ∀ v∈q.support,v∈W) ∧
    (∀ a∈W, ∀ b∈W, a≠b → ∃ q : G.Walk a b, q.IsPath ∧ (C.length+1)/2+1 ≤ q.support.length ∧ ∀ v∈q.support,v∈W) := by
  classical
  let W := C.support.toFinset
  have width : C.length ≤ W.card := by
    have sub : C.support.tail.toFinset⊆W := by
      intro v hv
      exact List.mem_toFinset.mpr (List.mem_of_mem_tail (List.mem_toFinset.mp hv))
    have h := card_le_card sub
    rw [List.toFinset_card_of_nodup hc.support_nodup,List.length_tail,C.length_support] at h
    omega
  have contains (a : V) (ha : a∈W) (v : V) (hv : v∈(C.rotate a (List.mem_toFinset.mp ha)).support) :
      v∈W := List.mem_toFinset.mpr ((C.mem_support_rotate_iff a _).mp hv)
  have start (a : V) (ha : a∈W) :
      ∃ u, ∃ q : G.Walk a u, q.IsPath ∧ C.length ≤ q.support.length ∧ ∀ v∈q.support, v∈W := by
    let R := C.rotate a (List.mem_toFinset.mp ha)
    have rc : R.IsCycle := hc.rotate _
    have l : R.length=C.length := C.length_rotate _ _
    have h := R.length_dropLast_add_one rc.not_nil
    refine ⟨_,R.dropLast,rc.isPath_dropLast,by rw [Walk.length_support]; omega,?_⟩
    intro v hv
    apply contains a ha
    rw [Walk.support_dropLast rc.not_nil] at hv
    exact List.dropLast_subset _ hv
  have pair (a : V) (ha : a∈W) (b : V) (hb : b∈W) (diff : a≠b) :
      ∃ q : G.Walk a b, q.IsPath ∧ (C.length+1)/2+1 ≤ q.support.length ∧ ∀ v∈q.support,v∈W := by
    let R := C.rotate a (List.mem_toFinset.mp ha)
    have rc : R.IsCycle := hc.rotate _
    have on : b∈R.support := (C.mem_support_rotate_iff a _).mpr (List.mem_toFinset.mp hb)
    let L := R.takeUntil b on
    let T := R.dropUntil b on
    have split : L.append T=R := R.take_spec on
    have cycle : (L.append T).IsCycle := split ▸ rc
    have lp : L.IsPath := rc.isPath_takeUntil on
    have tp : T.IsPath := cycle.isPath_of_append_right (L.not_nil_of_ne diff)
    have lengths : L.length+T.length=C.length := by
      rw [←Walk.length_append,split]
      exact C.length_rotate _ _
    by_cases large : (C.length+1)/2 ≤ L.length
    · exact ⟨L,lp,by rw [L.length_support]; omega,fun v hv =>
        contains a ha v (R.support_takeUntil_subset_support on hv)⟩
    · exact ⟨T.reverse,tp.reverse,by rw [Walk.length_support,Walk.length_reverse]; omega,fun v hv =>
        contains a ha v (R.support_dropUntil_subset_support on (by simpa using hv))⟩
  exact ⟨width,start,pair⟩
theorem path_of_cycle [Fintype V] [Nontrivial V] [DecidableRel G.Adj]
    (p : G.Walk x y) (hp : p.IsPath)
    (longest : ∀ {u v}, ∀ q : G.Walk u v, q.IsPath → q.length ≤ p.length)
    (conn : 2 ≤ G.vertexConnectivity) {r : V} (C : G.Walk r r) (hc : C.IsCycle)
    (outside : ∀ v∈C.support,v∉p.support) :
    2*C.length+(C.length+1)/2+3 ≤ p.support.length := by
  classical
  let W := C.support.toFinset
  obtain ⟨width,start,pair⟩ := cycle_routes C hc
  change C.length ≤ W.card at width
  obtain ⟨_,q,hq,ql,_⟩ := start r (List.mem_toFinset.mpr C.start_mem_support)
  have mx := longest q hq
  have hq' := q.length_support
  have hp' := p.length_support
  have three := hc.three_le_length
  have ord := path_of_routes p hp longest conn W (fun v hv => outside v (List.mem_toFinset.mp hv))
    (by omega) (by omega) start pair
  omega
theorem order_of_cycle [Fintype V] [Nontrivial V] [DecidableRel G.Adj]
    (p : G.Walk x y) (hp : p.IsPath)
    (longest : ∀ {u v}, ∀ q : G.Walk u v, q.IsPath → q.length ≤ p.length)
    (conn : 2 ≤ G.vertexConnectivity) {r : V} (C : G.Walk r r) (hc : C.IsCycle)
    (outside : ∀ v∈C.support,v∉p.support) :
    3*C.length+(C.length+1)/2+3 ≤ Fintype.card V := by
  classical
  have n := card_outside_add_path p hp C.support.toFinset (fun v hv => outside v (List.mem_toFinset.mp hv))
  have width := (cycle_routes C hc).1
  have l := path_of_cycle p hp longest conn C hc outside
  omega
end Graph189TwoExteriorLinks
end
section
open SimpleGraph Finset Graph189ExteriorGap
namespace Graph189ThreeRegularMinimum
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
omit [DecidableEq V] [DecidableRel G.Adj] in
theorem longest_path (z : V) :
    ∃ x y : V, ∃ p : G.Walk x y, p.IsPath ∧
      ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → r.length ≤ p.length := by
  classical
  let Good (n : ℕ) := ∃ x y : V, ∃ p : G.Walk x y, p.IsPath ∧ p.length = n
  have base : Good 0 := ⟨z,z,.nil,by simp,rfl⟩
  obtain ⟨x,y,p,hp,hlen⟩ := Nat.findGreatest_spec (Nat.zero_le (Fintype.card V)) base
  refine ⟨x,y,p,hp,?_⟩
  intro u v r hr
  rw [hlen]
  have card := hr.support_nodup.length_le_card
  have size := r.length_support
  exact Nat.le_findGreatest (by omega) (show Good r.length from ⟨u,v,r,hr,rfl⟩)
end Graph189ThreeRegularMinimum
end
section
open Finset SimpleGraph Graph189ExteriorGap Graph189ExteriorDegreeCycle
namespace Graph189OrdinaryRotationWindow
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]
omit [Nontrivial V] in
theorem full_ports {x y : V} (p : G.Walk x y) (hp : p.IsPath)
    (mx : ∀ {u v}, ∀ q : G.Walk u v, q.IsPath → q.length ≤ p.length)
    (W D : Finset V) (lower : 4 ≤ W.card) (upper : W.card≤5) (many : 3 ≤ D.card) (sub : D⊆W)
    (outside : ∀ v∈W, v∉p.support)
    (clique : ∀ a∈D, ∀ b∈W, a≠b → G.Adj a b)
    (bound : ∀ a∈D, ∀ b, G.Adj a b → b∉W → b∈p.support)
    (high : ∀ a∈D, W.card+2 ≤ G.degree a) : 5*W.card+3 ≤ Fintype.card V := by
  classical
  let H := G.induce (W : Set V)
  have degree (a : W) : 3 ≤ H.degree a := by
    change 3≤(G.induce (W : Set V)).degree a
    rw [degree_induce_filter]
    by_cases inside : a.val∈D
    · have inc : W.erase a.val⊆(G.neighborFinset a.val).filter (fun v => v∈(W : Set V)) := by
        intro v hv
        obtain ⟨ne,mem⟩ := mem_erase.mp hv
        exact mem_filter.mpr ⟨(G.mem_neighborFinset _ _).mpr (clique _ inside _ mem ne.symm),mem⟩
      have h := card_le_card inc
      rw [card_erase_of_mem a.property] at h
      omega
    · have inc : D⊆(G.neighborFinset a.val).filter (fun v => v∈(W : Set V)) := by
        intro v hv
        exact mem_filter.mpr ⟨(G.mem_neighborFinset _ _).mpr
          (clique v hv _ a.property (fun e => inside (e ▸ hv))).symm,sub hv⟩
      exact many.trans (card_le_card inc)
  have hc (a b : W) (ne : a≠b) : ∃ q : H.Walk a b, q.IsHamiltonian := by
    apply Graph189TerminalLeafClosure.prescribed_of_supergraph (G:=H) le_top _
      (Graph189TerminalLeafClosure.complete_prescribed a b ne)
    intro u v _ _
    have h1 := degree u
    have h2 := degree v
    change Fintype.card W+1 ≤ H.degree u+H.degree v
    rw [Fintype.card_coe]
    omega
  have rows (a : V) (ha : a∈D) : 3≤((univ : Finset (Fin p.support.length)).filter
      (fun i => G.Adj p.support[i.val] a)).card := by
    let R := (univ : Finset (Fin p.support.length)).filter (fun i => G.Adj p.support[i.val] a)
    let P := R.image (fun i => p.support[i.val])
    have subset : insert a (G.neighborFinset a)⊆W∪P := by
      intro v hv
      rcases mem_insert.mp hv with rfl|h
      · exact mem_union_left _ (sub ha)
      have adj := (G.mem_neighborFinset _ _).mp h
      by_cases vw : v∈W
      · exact mem_union_left _ vw
      obtain ⟨i,hi,e⟩ := List.mem_iff_getElem.mp (bound a ha v adj vw)
      exact mem_union_right _ (mem_image.mpr ⟨⟨i,hi⟩,mem_filter.mpr
        ⟨mem_univ _,by simpa only [e] using adj.symm⟩,e⟩)
    have h := (card_le_card subset).trans (card_union_le W P)
    rw [card_insert_of_notMem (by simp),G.card_neighborFinset_eq_degree] at h
    have pc : P.card ≤ R.card := card_image_le
    have d := high a ha
    change 3 ≤ R.card
    omega
  obtain ⟨M,sz,f,adj⟩ := Graph189ExteriorAttachment.marks_of_many_neighbors p D 3 many rows
  let inc : D ↪ W := ⟨fun v => ⟨v.val,sub v.property⟩,fun _ _ h => Subtype.ext (congrArg (fun t : W => (t : V)) h)⟩
  have h := exterior_hamilton_connected_matching p hp mx W (by omega) outside hc M
    (card_pos.mp (by omega)) (f.trans inc) adj
  rw [sz] at h
  exact h
theorem of_cycle_cap {x y : V} (p : G.Walk x y) (hp : p.IsPath)
    (mx : ∀ {u v}, ∀ q : G.Walk u v, q.IsPath → q.length ≤ p.length)
    {k d L : ℕ} (original : G.secondSmallestDegree=k)
    (positive : 0 < d) (rounding : 2*d ≤ k+1) (two : 2 ≤ L)
    (bounded : ∀ {r}, ∀ C : G.Walk r r, C.IsCycle → (∀ v∈C.support,v∉p.support) → C.length ≤ L)
    (minimum : ∀ v, 3 ≤ G.degree v) (quota : ∀ v, (univ.filter (fun w => G.dist v w=2)).card ≤ k)
    {highVertex : V} (omitted : highVertex∉p.support) (large : k ≤ G.degree highVertex) :
    let E := p.support.toFinsetᶜ
    let J := G.induce (E : Set V)
    (∀ a : E, k ≤ G.degree a.val → d ≤ J.degree a) ∧
    ∃ B R : Finset E, d ≤ R.card ∧ R⊆B ∧ B.card ≤ L ∧ ∀ v∈R,J.neighborFinset v⊆B := by
  classical
  let E := p.support.toFinsetᶜ
  let J := G.induce (E : Set V)
  let emb := Embedding.induce (G:=G) (E : Set V)
  have off (a : E) : a.val∉p.support := fun hit => (mem_compl.mp a.property) (List.mem_toFinset.mpr hit)
  have unique (a b : V) (aLow : G.degree a < k) (bLow : G.degree b < k) : a=b := by
    by_contra ne
    have pair := OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1.degree_pair (G:=G) a b ne
    omega
  have degree (a : E) (hi : k ≤ G.degree a.val) : d ≤ J.degree a := by
    have lower := (high_exterior_half p hp mx (off a) (quota _) hi minimum unique).2
    have eq : J.degree a=(G.neighborFinset a.val \ p.support.toFinset).card := by
      rw [degree_induce_filter]
      congr 1
      ext v
      simp [E]
    omega
  have short (a : E) (c : J.Walk a a) (hc : c.IsCycle) : c.length ≤ L := by
    have bound := bounded (c.map emb.toHom) (hc.map emb.injective) (fun v hv => by
      rw [Walk.support_map] at hv
      obtain ⟨w,_,rfl⟩ := List.mem_map.mp hv
      exact off w)
    simpa only [Walk.length_map] using bound
  let h : E := ⟨highVertex,mem_compl.mpr fun mem => omitted (List.mem_toFinset.mp mem)⟩
  obtain ⟨a,b,q,hq,maxQ⟩ := Graph189ThreeRegularMinimum.longest_path (G:=J) h
  have positive : 0 < q.length := by
    have dh := degree h large
    obtain ⟨w,e⟩ := card_pos.mp (show 0<(J.neighborFinset h).card by
      rw [J.card_neighborFinset_eq_degree]
      omega)
    have edge := (J.mem_neighborFinset _ _).mp e
    have length := maxQ edge.toWalk edge.isPath_toWalk
    rw [edge.length_toWalk] at length
    omega
  have ab : a≠b := by
    intro eq
    subst b
    have zero := (Walk.isPath_iff_nil.mp hq).length_eq_zero
    omega
  have endpoints := OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1.degree_pair (G:=G) a.val b.val
    (fun e => ab (Subtype.ext e))
  have win : ∃ B R : Finset E, d ≤ R.card ∧ R⊆B ∧ B.card ≤ L ∧ ∀ v∈R,J.neighborFinset v⊆B := by
    rcases endpoints with ha|hb
    · exact Graph189RotationExterior.degree_window_at q hq maxQ two (degree a (by omega)) short
    · apply Graph189RotationExterior.degree_window_at q.reverse hq.reverse _ two (degree b (by omega)) short
      intro u v r hr
      simpa using maxQ r hr
  exact ⟨degree,win⟩
theorem of_high {x y : V} (p : G.Walk x y) (hp : p.IsPath)
    (mx : ∀ {u v}, ∀ q : G.Walk u v, q.IsPath → q.length ≤ p.length)
    (conn : 2 ≤ G.vertexConnectivity) {k d L : ℕ} (original : G.secondSmallestDegree=k)
    (positive : 0 < d) (rounding : 2*d ≤ k+1) (two : 2 ≤ L)
    (oversized : ∀ q, L < q → Fintype.card V<3*q+(q+1)/2+3)
    (minimum : ∀ v, 3 ≤ G.degree v) (quota : ∀ v, (univ.filter (fun w => G.dist v w=2)).card ≤ k)
    {highVertex : V} (omitted : highVertex∉p.support) (large : k ≤ G.degree highVertex) :
    let E := p.support.toFinsetᶜ
    let J := G.induce (E : Set V)
    (∀ a : E, k ≤ G.degree a.val → d ≤ J.degree a) ∧
    ∃ B R : Finset E, d ≤ R.card ∧ R⊆B ∧ B.card ≤ L ∧ ∀ v∈R,J.neighborFinset v⊆B := by
  apply of_cycle_cap p hp mx original positive rounding two _ minimum quota omitted large
  intro r c hc out
  have n := Graph189TwoExteriorLinks.order_of_cycle p hp mx conn c hc out
  by_contra! longer
  exact (not_lt_of_ge n) (oversized c.length longer)
end Graph189OrdinaryRotationWindow
end
section
open SimpleGraph Finset Graph189ExteriorDegreeCycle
open OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1
namespace Graph189AllHighExterior
open Graph189ExteriorGap
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {a b : V}
theorem minimum (p : G.Walk a b) (hp : p.IsPath)
    (t : Fin p.support.length)
    (longest : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → p.support[t.val] ∈ r.support → r.length ≤ p.length)
    (positive : 0 < G.secondSmallestDegree)
    (high : ∀ {v : V}, v∉p.support → G.secondSmallestDegree ≤ G.degree v)
    (cap : ∀ v, G.distEven v ≤ G.secondSmallestDegree+1) (x : (p.support.toFinsetᶜ : Finset V)) :
    G.secondSmallestDegree / 2 ≤ (G.induce ((p.support.toFinsetᶜ : Finset V) : Set V)).degree x := by
  classical
  let P := p.support.toFinset
  let E := Pᶜ
  let k := G.secondSmallestDegree
  have quota (v : V) : (univ.filter (fun y => G.dist v y = 2)).card ≤ k := by
    let T := univ.filter (fun y => G.dist v y = 2)
    have miss : v ∉ T := by simp [T]
    have sub : insert v T ⊆ univ.filter (fun y => Even (G.dist v y)) := by
      intro y hy
      rcases mem_insert.mp hy with rfl | h
      · simp
      · exact mem_filter.mpr ⟨mem_univ _,by rw [(mem_filter.mp h).2]; decide⟩
    have h := card_le_card sub
    rw [card_insert_of_notMem miss] at h
    change T.card+1 ≤ G.distEven v at h
    have capv := cap v
    change G.distEven v ≤ k+1 at capv
    change T.card ≤ k
    omega
  have outside : x.val ∉ p.support := fun h => (mem_compl.mp x.property) (List.mem_toFinset.mpr h)
  have gram : ((G.neighborFinset x.val).filter (fun u => u ∈ (E : Set V))) = G.neighborFinset x.val \ P := by
    ext v
    simp [E]
  change k/2 ≤ (G.induce (E : Set V)).degree x
  rw [degree_induce_filter,gram]
  obtain ⟨y,hy⟩ : (G.neighborFinset x.val \ P).Nonempty := by
    apply Classical.byContradiction
    intro empty
    have sub : G.neighborFinset x.val ⊆ P := by
      intro v hv
      by_contra out
      exact empty ⟨v,mem_sdiff.mpr ⟨hv,out⟩⟩
    have eq : (contactPositions p x.val).card = G.degree x.val := by
      rw [contact_card_neighbors p hp]
      change (G.neighborFinset x.val ∩ P).card = G.degree x.val
      rw [inter_eq_left.mpr sub, G.card_neighborFinset_eq_degree]
    have hx := high outside
    have pos : (contactPositions p x.val).Nonempty := card_pos.mp (by change 0 < k at positive; omega)
    have shift := protected_single_shell p hp t longest outside pos
    have shell : P.filter (fun y => G.dist x.val y=2) ⊆ univ.filter (fun y => G.dist x.val y=2) :=
      filter_subset_filter _ (subset_univ _)
    have count := (card_le_card shell).trans (quota _)
    change (contactPositions p x.val).card + 1 ≤ (P.filter _).card at shift
    omega
  have outy : y ∉ p.support := fun h => (mem_sdiff.mp hy).2 (List.mem_toFinset.mpr h)
  have bound := protected_half_degree p hp t longest outside outy
    ((G.mem_neighborFinset _ _).mp (mem_sdiff.mp hy).1) (quota _) (high outy)
  have := high outside
  change G.degree x.val ≤ 2*(G.neighborFinset x.val \ P).card+1 at bound
  omega
end Graph189AllHighExterior
end
section
open Finset SimpleGraph Graph189ExteriorGap
namespace Graph189ProtectedTripleFloor
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {x y : V}
theorem order (p : G.Walk x y) (hp : p.IsPath) (t : Fin p.support.length)
    (mx : ∀ {a b}, ∀ q : G.Walk a b, q.IsPath → p.support[t.val]∈q.support → q.length ≤ p.length)
    (E : Finset V) (outside : ∀ v∈E, v∉p.support) (three : 3 ≤ E.card)
    (routes : ∀ u v : E, u≠v → ∃ q : (G.induce (E : Set V)).Walk u v, q.IsHamiltonian)
    (rows : ∀ u∈E, 3≤((univ : Finset (Fin p.support.length)).filter
      (fun i => G.Adj p.support[i.val] u)).card) : 4*E.card+4 ≤ Fintype.card V := by
  classical
  obtain ⟨M,count,f,touching⟩ := Graph189ExteriorAttachment.marks_of_many_neighbors p E 3 three rows
  let A := M.orderEmbOfFin count
  let T := fun i : Fin 3 => f (M.orderIsoOfFin count i)
  have inj : Function.Injective T := f.injective.comp (M.orderIsoOfFin count).injective
  have touch (i : Fin 3) : G.Adj p.support[(A i).val] (T i).val := touching (M.orderIsoOfFin count i)
  have path (i j : Fin 3) (ne : i≠j) : ExteriorRoute p (T i).val (T j).val E.card := by
    obtain ⟨q,hq⟩ := routes _ _ (inj.ne ne)
    exact route_of_induced_hamilton p E outside hq
  have pre (safe : (A 0).val ≤ t.val) : E.card≤(A 0).val := by
    obtain ⟨q,hq,dis,len⟩ := path 1 0 (by decide)
    exact len.trans (protected_prefix_of_detour p hp t mx _ safe q hq dis (touch 0).symm)
  have post (safe : t.val≤(A 2).val) : (A 2).val+1+E.card ≤ p.support.length := by
    obtain ⟨q,hq,dis,len⟩ := path 2 0 (by decide)
    have bound := protected_suffix_of_detour p hp t mx _ safe q hq dis (touch 2)
    omega
  have inner (i j : Fin 3) (ij : i < j) (safe : (A j).val ≤ t.val ∨ t.val≤(A i).val) :
      (A i).val+1+E.card≤(A j).val := by
    obtain ⟨q,hq,dis,len⟩ := path i j ij.ne
    have bound := protected_interval_of_detour p hp t mx _ _ (A.strictMono ij) safe q hq dis (touch i) (touch j).symm
    omega
  have first := inner 0 1 (by decide)
  have last := inner 1 2 (by decide)
  have ab : (A 0).val < (A 1).val := A.strictMono (by decide : (0:Fin 3)<1)
  have bc : (A 1).val < (A 2).val := A.strictMono (by decide : (1:Fin 3)<2)
  have tail := (A 2).isLt
  have tpos := t.isLt
  have total := card_outside_add_path p hp E outside
  omega
end Graph189ProtectedTripleFloor
end
section
open Finset SimpleGraph Graph189ExteriorGap
namespace Graph189SixExterior
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]
theorem data {u v : V} (p : G.Walk u v) (hp : p.IsPath) (t : Fin p.support.length)
    (mx : ∀ {a b}, ∀ q : G.Walk a b, q.IsPath → p.support[t.val]∈q.support → q.length ≤ p.length)
    (six : G.secondSmallestDegree=6) (order : Fintype.card V≤19)
    (cap : ∀ w, G.distEven w ≤ G.secondSmallestDegree+1)
    (high : ∀ {w : V}, w∉p.support → G.secondSmallestDegree ≤ G.degree w)
    (present : (p.support.toFinsetᶜ : Finset V).Nonempty)
    (small : (p.support.toFinsetᶜ : Finset V).card≤5) :
    let E := (p.support.toFinsetᶜ : Finset V)
    E.card=5 ∧ (∀ x y : E, x≠y → ∃ q : (G.induce (E : Set V)).Walk x y, q.IsHamiltonian) ∧
      ∃ M : Finset (Fin p.support.length), M.card=2 ∧
        ∀ w∈E, ∀ i : Fin p.support.length, G.Adj p.support[i.val] w ↔ i∈M := by
  classical
  let E := (p.support.toFinsetᶜ : Finset V)
  let H := G.induce (E : Set V)
  change E.card≤5 at small
  have out (w : V) (hw : w∈E) : w∉p.support := by simpa [E] using hw
  have deg (w : E) : 3 ≤ H.degree w := by
    have d := Graph189AllHighExterior.minimum p hp t mx (by omega) high cap w
    rw [six] at d
    exact d
  obtain ⟨x,hx⟩ := present
  let X : E := ⟨x,hx⟩
  have four : 4 ≤ E.card := by
    have h := H.degree_lt_card_verts X
    change H.degree X < Fintype.card E at h
    rw [Fintype.card_coe] at h
    have := deg X
    omega
  have routes (x y : E) (ne : x≠y) : ∃ q : H.Walk x y, q.IsHamiltonian := by
    apply Graph189TerminalLeafClosure.prescribed_of_supergraph (G:=H) le_top _ (Graph189TerminalLeafClosure.complete_prescribed x y ne)
    intro i j _ _
    have := deg i
    have := deg j
    change Fintype.card E+1 ≤ H.degree i+H.degree j
    rw [Fintype.card_coe]
    omega
  have rows (w : V) (hw : w∈E) := Graph189DenseExteriorOrder.neighbors_on_path p E
    (fun _ _ x _ nx => by simpa [E] using nx) hw
  have five : E.card=5 := by
    by_contra diff
    have bound := Graph189ProtectedTripleFloor.order p hp t mx E out (by omega) routes (by
      intro w hw
      have A := rows w hw
      have B := high (out w hw)
      omega)
    omega
  refine ⟨five,routes,uniform_contacts_of_order p hp t mx E out (by omega) routes 2 (by omega) (by omega) ?_⟩
  intro w hw
  have A := rows w hw
  have B := high (out w hw)
  omega
end Graph189SixExterior
end
section
namespace OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R2_H2_R2
section Aux
open SimpleGraph OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R2
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
lemma h11 [Nontrivial V] [DecidableRel G.Adj] (hconn : G.Connected)
    (hH : ∀ x, distEven G x ≤ 1 + secondSmallestDegree G)
    (hn : 2 * secondSmallestDegree G + 3 ≤ Fintype.card V) : ∀ v, 2 ≤ G.degree v := by
  classical
  intro v
  by_contra hlt
  push Not at hlt
  have hpos : 0 < G.degree v := by
    obtain ⟨w, hw⟩ := exists_ne v
    obtain ⟨p⟩ := hconn.preconnected v w
    cases p with
    | nil => exact absurd rfl hw
    | cons h _ =>
      rw [← card_neighborFinset_eq_degree]
      exact Finset.card_pos.mpr ⟨_, (mem_neighborFinset _ _ _).mpr h⟩
  have h1 : G.degree v = 1 := by omega
  obtain ⟨c', hc', huniq⟩ := (G.degree_eq_one_iff_existsUnique_adj).mp h1
  have hdist : ∀ w, w ≠ v → G.dist v w = 1 + G.dist c' w := by
    intro w hw
    apply le_antisymm
    · have := hconn.dist_triangle (u := v) (v := c') (w := w)
      have h2 : G.dist v c' = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hc'
      omega
    · obtain ⟨p, hp⟩ := hconn.exists_walk_length_eq_dist v w
      cases p with
      | nil => exact absurd rfl hw
      | @cons _ z _ h q =>
        have hz : z = c' := huniq z h
        subst hz
        have := SimpleGraph.dist_le q
        simp only [Walk.length_cons] at hp
        omega
  have key : ∀ w, Even (G.dist c' w) ↔ ¬ Even (G.dist v w) := by
    intro w
    by_cases hw : w = v
    · subst hw
      have : G.dist c' w = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hc'.symm
      simp [this]
    · rw [hdist w hw, Nat.even_iff, Nat.even_iff]
      omega
  have hsum : distEven G v + distEven G c' = Fintype.card V := by
    unfold distEven
    have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset V))
      (fun w => Even (G.dist v w))
    simp only [key] at *
    rw [Finset.card_univ] at this
    simpa [key] using this
  have := hH v
  have := hH c'
  omega
lemma sigma_ge [Nontrivial V] [DecidableRel G.Adj] (h : ∀ v, 2 ≤ G.degree v) :
    2 ≤ secondSmallestDegree G := by
  have hlen : 1 < (degreeSequence G).length := by
    simp only [degreeSequence, Multiset.length_sort, Multiset.card_map, Finset.card_val,
      Finset.card_univ]
    exact Fintype.one_lt_card
  have hmem : secondSmallestDegree G ∈ degreeSequence G := by
    unfold secondSmallestDegree
    rw [List.getD_eq_getElem _ _ hlen]
    exact List.getElem_mem _
  simp only [degreeSequence, Multiset.mem_sort, Multiset.mem_map] at hmem
  obtain ⟨v, -, hv⟩ := hmem
  rw [← hv]; exact h v
lemma lemma4x [DecidableRel G.Adj] (hconn : G.Connected) (l : List V) (hne : l ≠ [])
    (hnd : l.Nodup) (hch : l.IsChain G.Adj)
    (hmax : ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → (∀ v ∈ l, v ∈ l') → l'.length ≤ l.length)
    (hlt : l.length < Fintype.card V) (h2 : 2 ≤ l.length) :
    (∀ y, G.Adj (l.head hne) y → y ∈ l) ∧ (∀ y, G.Adj (l.getLast hne) y → y ∈ l) ∧
      G.degree (l.head hne) + G.degree (l.getLast hne) + 1 ≤ l.length ∧
      (∀ j, j + 1 < l.length → G.Adj (l.head hne) (l.getD (j + 1) (l.head hne)) →
        ¬ G.Adj (l.getD j (l.head hne)) (l.getLast hne)) ∧
      G.degree (l.head hne) ≤ ((Finset.range (l.length - 1)).filter
        (fun j => G.Adj (l.head hne) (l.getD (j + 1) (l.head hne)))).card ∧
      G.degree (l.getLast hne) ≤ ((Finset.range (l.length - 1)).filter
        (fun j => G.Adj (l.getD j (l.head hne)) (l.getLast hne))).card := by
  classical
  set n := Fintype.card V with hn
  have hlnd := hnd
  have hlch := hch
  set q0 := l.head hne
  set z := l.getLast hne
  have ext_head : ∀ y, G.Adj q0 y → y ∈ l := by
    intro y hy
    by_contra hyl
    have := hmax (y :: l) (List.nodup_cons.2 ⟨hyl, hlnd⟩)
      (List.IsChain.cons_of_ne_nil hne hlch ((hy).symm))
      (fun v hv => List.mem_cons_of_mem _ hv)
    simp only [List.length_cons] at this
    omega
  have ext_last : ∀ y, G.Adj z y → y ∈ l := by
    intro y hy
    by_contra hyl
    have hch : (l ++ [y]).IsChain G.Adj := by
      refine List.isChain_append.2 ⟨hlch, List.isChain_singleton _, ?_⟩
      intro x hx y' hy'
      rw [List.getLast?_eq_some_getLast hne] at hx
      simp at hx hy'
      subst hx hy'
      exact hy
    have hnd : (l ++ [y]).Nodup := by
      rw [List.nodup_append]
      refine ⟨hlnd, List.nodup_singleton _, ?_⟩
      intro a ha b hb
      simp at hb
      subst hb
      rintro rfl
      exact hyl ha
    have := hmax _ hnd hch (fun v hv => List.mem_append_left _ hv)
    simp only [List.length_append, List.length_singleton] at this
    omega
  have hl_ne := hne
  set m := l.length with hm
  have hq0 : l.getD 0 q0 = q0 := getD_zero l hl_ne q0
  have hz : l.getD (m - 1) q0 = z := getD_last l hl_ne q0
  have htwo : 2 ≤ m := h2
  have hneEnds : q0 ≠ z := by
    intro he
    have ieq : l[0]'(by omega) = l[m-1]'(by omega) := by
      rw [← List.getD_eq_getElem (d := q0), ← List.getD_eq_getElem (d := q0), hq0, hz]
      exact he
    have hh := hlnd.getElem_inj_iff.mp ieq
    omega
  let S := (Finset.range (m - 1)).filter (fun j => G.Adj q0 (l.getD (j + 1) q0))
  let T := (Finset.range (m - 1)).filter (fun j => G.Adj (l.getD j q0) z)
  have hS : G.degree q0 ≤ S.card := by
    rw [← card_neighborFinset_eq_degree]
    refine le_trans (Finset.card_le_card ?_) (Finset.card_image_le (s := S)
      (f := fun j => l.getD (j + 1) q0))
    intro y hy
    rw [mem_neighborFinset] at hy
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem (ext_head y hy)
    have hk0 : k ≠ 0 := by
      rintro rfl
      apply hy.ne
      rw [← List.getD_eq_getElem (d := q0), hq0]
    rw [Finset.mem_image]
    refine ⟨k - 1, ?_, ?_⟩
    · rw [Finset.mem_filter, Finset.mem_range]
      refine ⟨by omega, ?_⟩
      rw [show k - 1 + 1 = k by omega, List.getD_eq_getElem _ _ hk]
      exact hy
    · rw [show k - 1 + 1 = k by omega, List.getD_eq_getElem _ _ hk]
  have hT : G.degree z ≤ T.card := by
    rw [← card_neighborFinset_eq_degree]
    refine le_trans (Finset.card_le_card ?_) (Finset.card_image_le (s := T)
      (f := fun j => l.getD j q0))
    intro y hy
    rw [mem_neighborFinset] at hy
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem (ext_last y hy)
    have hkm : k ≠ m - 1 := by
      rintro rfl
      apply hy.ne
      rw [← List.getD_eq_getElem (d := q0), hz]
    rw [Finset.mem_image]
    refine ⟨k, ?_, List.getD_eq_getElem _ _ hk⟩
    rw [Finset.mem_filter, Finset.mem_range]
    refine ⟨by omega, ?_⟩
    rw [List.getD_eq_getElem _ _ hk]
    exact (hy).symm
  have hdisj : ∀ j, j ∈ S → j ∈ T → False := by
    intro j hjS hjT
    rw [Finset.mem_filter, Finset.mem_range] at hjS hjT
    obtain ⟨hjm, hA⟩ := hjS
    obtain ⟨-, hB⟩ := hjT
    set c := l.take (j + 1) ++ (l.drop (j + 1)).reverse with hcdef
    have hperm : c.Perm l := by
      have := (List.Perm.append_left (l.take (j + 1)) (List.reverse_perm (l.drop (j + 1))))
      rw [List.take_append_drop] at this
      exact this
    have hcnd : c.Nodup := hperm.nodup_iff.mpr hlnd
    have hj1 : j < m := by omega
    have hj2 : j + 1 < m := by omega
    have e1 : (l.take (j + 1)).getLast? = some (l.getD j q0) := by
      rw [List.getLast?_take, List.getD_eq_getElem _ _ hj1]
      simp [List.getElem?_eq_getElem hj1]
    have e2 : (l.drop (j + 1)).reverse.head? = some z := by
      rw [List.head?_reverse, List.getLast?_drop, if_neg (by omega), List.getLast?_eq_some_getLast hl_ne]
    have e3 : c.getLast? = some (l.getD (j + 1) q0) := by
      rw [hcdef, List.getLast?_append, List.getLast?_reverse, List.head?_drop,
        List.getElem?_eq_getElem hj2, List.getD_eq_getElem _ _ hj2]
      rfl
    have e4 : c.head? = some q0 := by
      rw [hcdef, List.head?_append, List.head?_take]
      simp [List.head?_eq_some_head hl_ne, q0]
    have hcyc : c.IsChain G.Adj ∧ ∀ a ∈ c.getLast?, ∀ b ∈ c.head?, G.Adj a b := by
      refine ⟨List.isChain_append.2 ⟨hlch.take _, ?_, ?_⟩, ?_⟩
      · rw [List.isChain_reverse]
        exact (hlch.drop _).imp (fun a b h => h.symm)
      · intro x hx y hy
        rw [e1] at hx
        rw [e2] at hy
        simp at hx hy
        subst hx hy
        exact hB
      · intro a ha b hb
        rw [e3] at ha
        rw [e4] at hb
        simp at ha hb
        subst ha hb
        exact (hA).symm
    have hall : ∀ w, w ∈ l := by
      intro w
      by_contra hw
      obtain ⟨p⟩ := hconn q0 w
      obtain ⟨d, -, hd1, hd2⟩ := p.exists_boundary_dart {x | x ∈ l} (List.head_mem hl_ne) hw
      have hqc : d.fst ∈ c := hperm.mem_iff.mpr hd1
      obtain ⟨c', hc'p, hc'ch, hc'h⟩ := rot hcyc hqc
      have hnd' : (d.snd :: c').Nodup := by
        refine List.nodup_cons.2 ⟨?_, (hc'p.trans hperm).nodup_iff.mpr hlnd⟩
        intro hmem
        exact hd2 ((hc'p.trans hperm).mem_iff.mp hmem)
      have hch' : (d.snd :: c').IsChain G.Adj := by
        refine List.isChain_cons.2 ⟨?_, hc'ch⟩
        intro y hy
        rw [hc'h] at hy
        simp at hy
        subst hy
        exact (d.adj).symm
      have := hmax _ hnd' hch' (fun v hv => List.mem_cons_of_mem _
        ((hc'p.trans hperm).mem_iff.mpr hv))
      rw [List.length_cons, (hc'p.trans hperm).length_eq] at this
      omega
    have hmn' : m = n := by
      have h1 : l.toFinset = Finset.univ := by
        ext w
        simp [hall w]
      have h2 := List.toFinset_card_of_nodup hlnd
      rw [h1, Finset.card_univ] at h2
      omega
    omega
  have hdisj' : Disjoint S T := Finset.disjoint_left.mpr (fun j h1 h2 => hdisj j h1 h2)
  have hsub : S ∪ T ⊆ Finset.range (m - 1) := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact (Finset.mem_filter.mp hx).1
    · exact (Finset.mem_filter.mp hx).1
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj', Finset.card_range] at hcard
  refine ⟨ext_head, ext_last, by omega, ?_, hS, hT⟩
  intro j hj hA hB
  apply hdisj j
  · simp only [S, Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, hA⟩
  · simp only [T, Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, hB⟩
lemma longer_of_perm_x (l : List V) (hnd : l.Nodup)
    (hmax : ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → (∀ v ∈ l, v ∈ l') → l'.length ≤ l.length)
    (y : V) (hy : y ∉ l) {c : List V} (hc : c.Perm (y :: l)) (hch : c.IsChain G.Adj) : False := by
  have hnd' : c.Nodup := hc.nodup_iff.mpr (List.nodup_cons.2 ⟨hy, hnd⟩)
  have := hmax c hnd' hch (fun v hv => hc.mem_iff.mpr (List.mem_cons_of_mem _ hv))
  rw [hc.length_eq] at this
  simp only [List.length_cons] at this
  omega
lemma no_insert_x (l : List V) (hnd : l.Nodup) (hch : l.IsChain G.Adj)
    (hmax : ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → (∀ v ∈ l, v ∈ l') → l'.length ≤ l.length)
    (y : V) (hy : y ∉ l) (k : ℕ) (hk0 : 0 < k) (hk : k < l.length)
    (h1 : G.Adj (l[k - 1]'(by omega)) y) (h2 : G.Adj y (l[k]'hk)) : False := by
  refine longer_of_perm_x l hnd hmax y hy (c := l.take k ++ y :: l.drop k)
    (List.perm_middle.trans ?_) ?_
  · rw [List.take_append_drop]
  · refine List.isChain_append.2 ⟨hch.take _, ?_, ?_⟩
    · refine List.isChain_cons.2 ⟨?_, hch.drop _⟩
      intro z hz
      rw [List.head?_drop, List.getElem?_eq_getElem hk] at hz
      simp only [Option.mem_def, Option.some.injEq] at hz
      subst hz
      exact h2
    · intro x hx z hz
      rw [List.getLast?_take, if_neg (by omega)] at hx
      simp only [List.getElem?_eq_getElem (by omega : k - 1 < l.length), Option.some_or,
        Option.mem_def, Option.some.injEq] at hx
      simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hz
      subst hx hz
      exact h1
lemma lemma5abx [DecidableRel G.Adj] (hconn : G.Connected) (l : List V) (hne : l ≠ [])
    (hnd : l.Nodup) (hch : l.IsChain G.Adj)
    (hmax : ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → (∀ v ∈ l, v ∈ l') → l'.length ≤ l.length)
    (y : V) (hy : y ∉ l) (j : ℕ) (hj : j < l.length) (hadj : G.Adj y (l.getD j y)) :
    0 < j ∧ j + 1 < l.length ∧ ¬ G.Adj y (l.getD (j + 1) y) ∧ ¬ G.Adj y (l.getD (j - 1) y) ∧
      ¬ G.Adj (l.head hne) (l.getD (j + 1) y) ∧ ¬ G.Adj (l.getLast hne) (l.getD (j - 1) y) := by
  have hjd : l.getD j y = l[j] := List.getD_eq_getElem _ _ hj
  rw [hjd] at hadj
  have hlast : l.getLast hne = l[l.length - 1]'(by omega) := List.getLast_eq_getElem _
  have hhead : l.head hne = l[0]'(by omega) := by
    cases l with
    | nil => exact absurd rfl hne
    | cons a t => rfl
  have h0 : 0 < j := by
    by_contra h
    have hj0 : j = 0 := by omega
    subst hj0
    refine longer_of_perm_x l hnd hmax y hy (c := y :: l) (List.Perm.refl _) ?_
    refine List.IsChain.cons_of_ne_nil hne hch ?_
    rw [hhead]
    exact hadj
  have h1 : j + 1 < l.length := by
    by_contra h
    have hjl : j = l.length - 1 := by omega
    subst hjl
    refine longer_of_perm_x l hnd hmax y hy (c := l ++ [y]) (List.perm_append_comm.trans (List.Perm.refl _)) ?_
    refine List.isChain_append.2 ⟨hch, List.isChain_singleton _, ?_⟩
    intro x hx y' hy'
    rw [List.getLast?_eq_some_getLast hne] at hx
    simp at hx hy'
    subst hx hy'
    rw [hlast]
    exact hadj.symm
  refine ⟨h0, h1, ?_, ?_, ?_, ?_⟩
  · rw [List.getD_eq_getElem _ _ h1]
    intro hadj2
    exact no_insert_x l hnd hch hmax y hy (j + 1) (by omega) h1 (by simpa using hadj.symm) hadj2
  · rw [List.getD_eq_getElem _ _ (by omega : j - 1 < l.length)]
    intro hadj2
    exact no_insert_x l hnd hch hmax y hy j h0 hj hadj2.symm hadj
  · rw [List.getD_eq_getElem _ _ h1, hhead]
    intro hadj2
    refine longer_of_perm_x l hnd hmax y hy
      (c := y :: ((l.take (j + 1)).reverse ++ l.drop (j + 1))) ?_ ?_
    · refine List.Perm.cons _ ?_
      exact ((List.reverse_perm _).append_right _).trans (by rw [List.take_append_drop])
    · refine List.isChain_cons.2 ⟨?_, ?_⟩
      · intro z hz
        rw [List.head?_append, List.head?_reverse] at hz
        have e : (l.take (j + 1)).getLast? = some l[j] := by
          rw [List.getLast?_take]
          simp [List.getElem?_eq_getElem hj]
        rw [e] at hz
        simp only [Option.some_or, Option.mem_def, Option.some.injEq] at hz
        subst hz
        exact hadj.symm.symm
      · refine List.isChain_append.2 ⟨?_, hch.drop _, ?_⟩
        · rw [List.isChain_reverse]
          exact (hch.take _).imp (fun a b h => h.symm)
        · intro x hx z hz
          rw [List.getLast?_reverse] at hx
          rw [List.head?_drop, List.getElem?_eq_getElem h1] at hz
          simp only [Option.mem_def, Option.some.injEq] at hx hz
          subst hz
          have : (l.take (j + 1)).head? = some l[0] := by
            rw [List.head?_take, if_neg (by omega), List.head?_eq_some_head hne, hhead]
          rw [this] at hx
          simp only [Option.some.injEq] at hx
          subst hx
          exact hadj2
  · rw [List.getD_eq_getElem _ _ (by omega : j - 1 < l.length), hlast]
    intro hadj2
    refine longer_of_perm_x l hnd hmax y hy
      (c := (l.take j ++ (l.drop j).reverse) ++ [y]) ?_ ?_
    · refine List.perm_append_singleton _ _ |>.trans (List.Perm.cons _ ?_)
      exact (List.Perm.append_left _ (List.reverse_perm _)).trans (by rw [List.take_append_drop])
    · have e1 : (l.take j).getLast? = some l[j - 1] := by
        rw [List.getLast?_take, if_neg (by omega)]
        simp [List.getElem?_eq_getElem (by omega : j - 1 < l.length)]
      have e2 : (l.drop j).reverse.head? = some l[l.length - 1] := by
        rw [List.head?_reverse, List.getLast?_drop, if_neg (by omega),
          List.getLast?_eq_some_getLast hne, hlast]
      refine List.isChain_append.2 ⟨?_, List.isChain_singleton _, ?_⟩
      · refine List.isChain_append.2 ⟨hch.take _, ?_, ?_⟩
        · rw [List.isChain_reverse]
          exact (hch.drop _).imp (fun a b h => h.symm)
        · intro x hx z hz
          rw [e1] at hx
          rw [e2] at hz
          simp only [Option.mem_def, Option.some.injEq] at hx hz
          subst hx hz
          exact hadj2.symm
      · intro x hx z hz
        simp at hz
        subst hz
        have e3 : (l.take j ++ (l.drop j).reverse).getLast? = some l[j] := by
          rw [List.getLast?_append, List.getLast?_reverse, List.head?_drop,
            List.getElem?_eq_getElem hj]
          rfl
        rw [e3] at hx
        simp only [Option.mem_def, Option.some.injEq] at hx
        subst hx
        exact hadj.symm
lemma exists_longest_x0 [DecidableRel G.Adj] (x₀ : V) :
    ∃ l : List V, l ≠ [] ∧ l.Nodup ∧ l.IsChain G.Adj ∧ x₀ ∈ l ∧
      ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → x₀ ∈ l' → l'.length ≤ l.length := by
  classical
  let PP : ℕ → Prop := fun k => ∃ l : List V, (l.Nodup ∧ l.IsChain G.Adj ∧ x₀ ∈ l) ∧ l.length = k
  have h1 : PP 1 := ⟨[x₀], ⟨by simp, List.isChain_singleton _, by simp⟩, rfl⟩
  have hpos : 1 ≤ Fintype.card V := Fintype.card_pos_iff.mpr ⟨x₀⟩
  obtain ⟨l, ⟨hlnd, hlch, hlx⟩, hlM⟩ := Nat.findGreatest_spec (P := PP) hpos h1
  have hmax : ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → x₀ ∈ l' →
      l'.length ≤ Nat.findGreatest PP (Fintype.card V) :=
    fun l' a b c => Nat.le_findGreatest a.length_le_card ⟨l', ⟨a, b, c⟩, rfl⟩
  exact ⟨l, List.ne_nil_of_mem hlx, hlnd, hlch, hlx, fun l' a b c => hlM ▸ hmax l' a b c⟩
lemma chain_rev {l : List V} (h : l.IsChain G.Adj) : l.reverse.IsChain G.Adj := by
  rw [List.isChain_reverse]
  exact h.imp (fun a b h => h.symm)
lemma rot_head [DecidableRel G.Adj] (x₀ : V) (hδ : ∀ v, 2 ≤ G.degree v) (l : List V)
    (hne : l ≠ []) (hnd : l.Nodup) (hch : l.IsChain G.Adj) (hx : x₀ ∈ l)
    (hmax : ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → x₀ ∈ l' → l'.length ≤ l.length)
    (hh : l.head hne = x₀) :
    ∃ l' : List V, ∃ h : l' ≠ [], l'.Nodup ∧ l'.IsChain G.Adj ∧ x₀ ∈ l' ∧
      l'.length = l.length ∧ l'.head h ≠ x₀ ∧ l'.getLast h ≠ x₀ := by
  classical
  cases l with
  | nil => exact absurd rfl hne
  | cons a t =>
    have hax : a = x₀ := hh
    subst hax
    have hxt : a ∉ t := (List.nodup_cons.mp hnd).1
    have hnt : t.Nodup := (List.nodup_cons.mp hnd).2
    have hnbr : ∀ y, G.Adj a y → y ∈ t := by
      intro y hy
      by_contra hyt
      have hyl : y ∉ a :: t := by
        simp only [List.mem_cons, not_or]
        exact ⟨hy.ne.symm, hyt⟩
      have := hmax (y :: a :: t) (List.nodup_cons.2 ⟨hyl, hnd⟩)
        (List.IsChain.cons_of_ne_nil hne hch hy.symm) (by simp)
      simp only [List.length_cons] at this
      omega
    have hcard : 1 < (G.neighborFinset a).card := by
      rw [card_neighborFinset_eq_degree]; have := hδ a; omega
    cases t with
    | nil =>
      obtain ⟨y, hy⟩ := Finset.card_pos.mp (by omega : 0 < (G.neighborFinset a).card)
      simpa using hnbr y ((mem_neighborFinset _ _ _).mp hy)
    | cons u t' =>
      obtain ⟨w, hw, hwu⟩ := Finset.exists_mem_ne hcard u
      have hwadj : G.Adj a w := (mem_neighborFinset _ _ _).mp hw
      have hwt : w ∈ u :: t' := hnbr w hwadj
      obtain ⟨A, B, hAB⟩ := List.append_of_mem hwt
      have hA : A ≠ [] := by
        rintro rfl
        simp only [List.nil_append, List.cons.injEq] at hAB
        exact hwu hAB.1.symm
      have hch' : (A ++ w :: B).IsChain G.Adj := by
        rw [← hAB]; exact (List.isChain_cons.mp hch).2
      rw [List.isChain_append] at hch'
      have hlink : ∀ y ∈ A.head?, G.Adj a y := by
        intro y hy
        have hAh : (u :: t').head? = A.head? := by
          rw [hAB]
          cases A with
          | nil => exact absurd rfl hA
          | cons a1 A' => rfl
        exact (List.isChain_cons.mp hch).1 y (by rw [hAh]; exact hy)
      have hperm : (A.reverse ++ a :: w :: B).Perm (a :: u :: t') := by
        rw [List.perm_iff_count]
        intro z
        have h2 : (u :: t') = A ++ w :: B := hAB
        rw [h2]
        simp [List.count_cons, List.count_append]
        omega
      have hnd' : (A.reverse ++ a :: w :: B).Nodup := hperm.nodup_iff.mpr hnd
      refine ⟨A.reverse ++ a :: w :: B, by simp, hnd', ?_, by simp, hperm.length_eq, ?_, ?_⟩
      · rw [List.isChain_append]
        refine ⟨chain_rev hch'.1, ?_, ?_⟩
        · exact List.isChain_cons.mpr ⟨fun y hy => by
            simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hy
            subst hy; exact hwadj, hch'.2.1⟩
        · intro x hx y hy
          simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hy
          subst hy
          rw [List.getLast?_reverse] at hx
          exact (hlink x hx).symm
      · have hxA : a ∉ A := fun h => hxt (by rw [hAB]; exact List.mem_append_left _ h)
        intro hh2
        have hmem : (A.reverse ++ a :: w :: B).head (by simp) ∈ A.reverse := by
          rw [List.head_append_of_ne_nil (by simpa using hA)]
          exact List.head_mem _
        rw [hh2] at hmem
        exact hxA (List.mem_reverse.mp hmem)
      · intro hh2
        have hg := List.getLast_eq_getElem (l := A.reverse ++ a :: w :: B) (by simp)
        have hi : (A.reverse ++ a :: w :: B)[A.reverse.length]'(by simp) = a := by
          rw [List.getElem_append_right (by omega)]; simp
        have hinj := (List.Nodup.getElem_inj_iff hnd').mp (hi.trans (hh2.symm.trans hg))
        simp at hinj
lemma h18 [DecidableRel G.Adj] (hconn : G.Connected) (x₀ : V) (hδ : ∀ v, 2 ≤ G.degree v)
    (hlt : ∀ l : List V, l.Nodup → l.IsChain G.Adj → x₀ ∈ l → l.length < Fintype.card V) :
    ∃ l : List V, ∃ h : l ≠ [], l.Nodup ∧ l.IsChain G.Adj ∧ x₀ ∈ l ∧
      l.head h ≠ x₀ ∧ l.getLast h ≠ x₀ ∧
      (∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → x₀ ∈ l' → l'.length ≤ l.length) := by
  obtain ⟨l, hne, hnd, hch, hx, hmax⟩ := exists_longest_x0 (G := G) x₀
  by_cases h1 : l.head hne = x₀
  · obtain ⟨l', h', hnd', hch', hx', hlen, h2, h3⟩ :=
      rot_head x₀ hδ l hne hnd hch hx hmax h1
    exact ⟨l', h', hnd', hch', hx', h2, h3, fun l'' a b c => (hmax l'' a b c).trans hlen.ge⟩
  by_cases h2 : l.getLast hne = x₀
  · have hrne : l.reverse ≠ [] := by simpa using hne
    have hhead : l.reverse.head hrne = x₀ := by
      rw [List.head_reverse]; exact h2
    have hmaxr : ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → x₀ ∈ l' →
        l'.length ≤ l.reverse.length := by
      intro l' a b c; rw [List.length_reverse]; exact hmax l' a b c
    obtain ⟨l', h', hnd', hch', hx', hlen, h3, h4⟩ :=
      rot_head x₀ hδ l.reverse hrne (List.nodup_reverse.mpr hnd) (chain_rev hch)
        (List.mem_reverse.mpr hx) hmaxr hhead
    exact ⟨l', h', hnd', hch', hx', h3, h4, fun l'' a b c => (hmaxr l'' a b c).trans hlen.ge⟩
  · exact ⟨l, hne, hnd, hch, hx, h1, h2, hmax⟩
lemma Cadre.hmax_sup [Nontrivial V] [DecidableRel G.Adj] {x₀ : V} {l : List V}
    (hconn : G.Connected) (hb : ∀ c : V, (G.induce {x | x ≠ c}).Connected)
    (hH : ∀ x, distEven G x ≤ 1 + secondSmallestDegree G)
    (hmin : ∀ v, G.degree x₀ ≤ G.degree v)
    (hx0 : ∀ v, v ≠ x₀ → secondSmallestDegree G ≤ G.degree v)
    (hδ : ∀ v, 2 ≤ G.degree v) (hne : l ≠ []) (hnd : l.Nodup) (hch : l.IsChain G.Adj)
    (hmem : x₀ ∈ l) (hhd : l.head hne ≠ x₀) (hlast : l.getLast hne ≠ x₀)
    (hmax : ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → x₀ ∈ l' → l'.length ≤ l.length)
    (hlt : l.length < Fintype.card V) :
    ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → (∀ v ∈ l, v ∈ l') → l'.length ≤ l.length := by
  intro l' h1 h2 h3
  exact hmax l' h1 h2 (h3 x₀ hmem)
lemma Cadre.reverse [Nontrivial V] [DecidableRel G.Adj] {x₀ : V} {l : List V}
    (hconn : G.Connected) (hb : ∀ c : V, (G.induce {x | x ≠ c}).Connected)
    (hH : ∀ x, distEven G x ≤ 1 + secondSmallestDegree G)
    (hmin : ∀ v, G.degree x₀ ≤ G.degree v)
    (hx0 : ∀ v, v ≠ x₀ → secondSmallestDegree G ≤ G.degree v)
    (hδ : ∀ v, 2 ≤ G.degree v) (hne : l ≠ []) (hnd : l.Nodup) (hch : l.IsChain G.Adj)
    (hmem : x₀ ∈ l) (hhd : l.head hne ≠ x₀) (hlast : l.getLast hne ≠ x₀)
    (hmax : ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → x₀ ∈ l' → l'.length ≤ l.length)
    (hlt : l.length < Fintype.card V) :
    ∃ hne' : l.reverse ≠ [], l.reverse.Nodup ∧ l.reverse.IsChain G.Adj ∧ x₀ ∈ l.reverse ∧
      l.reverse.head hne' ≠ x₀ ∧ l.reverse.getLast hne' ≠ x₀ ∧
      (∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → x₀ ∈ l' → l'.length ≤ l.reverse.length) ∧
      l.reverse.length < Fintype.card V := by
  have hne' : l.reverse ≠ [] := by simpa using hne
  refine ⟨hne', List.nodup_reverse.mpr hnd, chain_rev hch, List.mem_reverse.mpr hmem, ?_, ?_, ?_, ?_⟩
  · rw [List.head_reverse]; exact hlast
  · rw [List.getLast_reverse]; exact hhd
  · intro l' a b c; rw [List.length_reverse]; exact hmax l' a b c
  · rw [List.length_reverse]; exact hlt
lemma Cadre.exists_cadre [Nontrivial V] [DecidableRel G.Adj] (hconn : G.Connected)
    (hH : ∀ x, distEven G x ≤ 1 + secondSmallestDegree G)
    (hn : 2 * secondSmallestDegree G + 3 ≤ Fintype.card V) {x₀ : V}
    (hmin : ∀ v, G.degree x₀ ≤ G.degree v) :
    (∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian) ∨
      ∃ l : List V, ∃ hne : l ≠ [], l.Nodup ∧ l.IsChain G.Adj ∧ x₀ ∈ l ∧
        l.head hne ≠ x₀ ∧ l.getLast hne ≠ x₀ ∧
        (∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → x₀ ∈ l' → l'.length ≤ l.length) ∧
        l.length < Fintype.card V := by
  classical
  have hδ := h11 hconn hH hn
  by_cases hall : ∀ l : List V, l.Nodup → l.IsChain G.Adj → x₀ ∈ l → l.length < Fintype.card V
  · right
    obtain ⟨l, hne, hnd, hch, hx, h1h, hlast, hmax⟩ := h18 hconn x₀ hδ hall
    exact ⟨l, hne, hnd, hch, hx, h1h, hlast, hmax, hall l hnd hch hx⟩
  · left
    push Not at hall
    obtain ⟨l, hnd, hch, hx, hlen⟩ := hall
    have hne : l ≠ [] := List.ne_nil_of_mem hx
    exact ham_of_list l hne hnd hch (le_antisymm hnd.length_le_card hlen)
lemma card_le_gamma [DecidableRel G.Adj] (hconn : G.Connected)
    (hH : ∀ x, distEven G x ≤ 1 + secondSmallestDegree G) (v : V) (S : Finset V)
    (hS : ∀ w ∈ S, G.dist v w = 2) : S.card ≤ secondSmallestDegree G := by
  classical
  have hsub : S ⊆ (Finset.univ.filter fun w => Even (G.dist v w)).erase v := by
    intro w hw
    have h2 := hS w hw
    have hwv : w ≠ v := by
      rintro rfl
      simp at h2
    simp [hwv, h2]
  have hvm : v ∈ Finset.univ.filter fun w => Even (G.dist v w) := by simp
  have := Finset.card_le_card hsub
  rw [Finset.card_erase_of_mem hvm] at this
  have h3 := hH v
  unfold distEven at h3
  omega
lemma cut_closed (hb : ∀ c : V, (G.induce {x | x ≠ c}).Connected) (c : V) (S : Finset V)
    (hc : c ∉ S) (hS : S.Nonempty) (hcl : ∀ v ∈ S, ∀ w, G.Adj v w → w ≠ c → w ∈ S)
    (hout : ∃ w, w ≠ c ∧ w ∉ S) : False := by
  classical
  obtain ⟨s, hs⟩ := hS
  obtain ⟨w, hwc, hwS⟩ := hout
  have hsc : s ≠ c := fun h => hc (h ▸ hs)
  obtain ⟨p⟩ := (hb c) ⟨s, hsc⟩ ⟨w, hwc⟩
  obtain ⟨d, -, hd1, hd2⟩ := p.exists_boundary_dart {x | x.1 ∈ S} hs hwS
  exact hd2 (hcl _ hd1 _ d.adj d.snd.2)
lemma Cadre.no_longer [Nontrivial V] [DecidableRel G.Adj] {x₀ : V} {l : List V}
    (hconn : G.Connected) (hb : ∀ c : V, (G.induce {x | x ≠ c}).Connected)
    (hH : ∀ x, distEven G x ≤ 1 + secondSmallestDegree G)
    (hmin : ∀ v, G.degree x₀ ≤ G.degree v)
    (hx0 : ∀ v, v ≠ x₀ → secondSmallestDegree G ≤ G.degree v)
    (hδ : ∀ v, 2 ≤ G.degree v) (hne : l ≠ []) (hnd : l.Nodup) (hch : l.IsChain G.Adj)
    (hmem : x₀ ∈ l) (hhd : l.head hne ≠ x₀) (hlast : l.getLast hne ≠ x₀)
    (hmax : ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → x₀ ∈ l' → l'.length ≤ l.length)
    (hlt : l.length < Fintype.card V)
    (l' : List V) (h1 : l'.Nodup) (h2 : l'.IsChain G.Adj) (h3 : x₀ ∈ l')
    (h4 : l.length < l'.length) : False := by
  have := hmax l' h1 h2 h3
  omega
lemma b5_chain3 {A B C : List V} (hB : B ≠ []) (hA : A.IsChain G.Adj) (hb : B.IsChain G.Adj)
    (hc : C.IsChain G.Adj) (hAB : ∀ x ∈ A.getLast?, ∀ y ∈ B.head?, G.Adj x y)
    (hBC : ∀ x ∈ B.getLast?, ∀ y ∈ C.head?, G.Adj x y) : (A ++ B ++ C).IsChain G.Adj := by
  rw [List.isChain_append]
  refine ⟨List.isChain_append.2 ⟨hA, hb, hAB⟩, hc, ?_⟩
  intro x hx y hy
  rw [List.getLast?_append_of_ne_nil _ hB] at hx
  exact hBC x hx y hy
lemma b5_idx {l : List V} {x : V} (h : x ∈ l) : ∃ i, i < l.length ∧ l.getD i x = x := by
  obtain ⟨i, hi, e⟩ := List.mem_iff_getElem.mp h
  exact ⟨i, hi, by rw [List.getD_eq_getElem _ _ hi]; exact e⟩
lemma b5_mem_td {l : List V} {x : V} {A B i : ℕ} (hi : i < l.length) (h : l.getD i x = x)
    (hc : i < A ∨ B ≤ i) : x ∈ l.take A ∨ x ∈ l.drop B := by
  rw [List.getD_eq_getElem _ _ hi] at h
  rcases hc with hc | hc
  · left
    exact List.mem_iff_getElem.mpr ⟨i, by simp; omega, by simpa using h⟩
  · right
    refine List.mem_iff_getElem.mpr ⟨i - B, by simp; omega, ?_⟩
    rw [List.getElem_drop]
    have : B + (i - B) = i := by omega
    simpa [this] using h
lemma b5_head_drop {l : List V} {b : ℕ} (d : V) (hb : b < l.length) :
    (l.drop b).head? = some (l.getD b d) := by
  rw [List.head?_drop, List.getD_eq_getElem _ _ hb, List.getElem?_eq_getElem hb]
lemma b5_last_take {l : List V} {a : ℕ} (d : V) (ha : a < l.length) :
    (l.take (a + 1)).getLast? = some (l.getD a d) := by
  rw [List.getLast?_take, List.getD_eq_getElem _ _ ha]
  simp [List.getElem?_eq_getElem ha]
lemma b5_nodup_td {l : List V} (hnd : l.Nodup) {A B : ℕ} (hAB : A ≤ B) :
    (l.take A ++ l.drop B).Nodup := by
  have hsub : (l.take A ++ l.drop B).Sublist l := by
    have h1 : l.drop B = (l.drop A).drop (B - A) := by
      rw [List.drop_drop]; congr 1; omega
    have h2 : (l.take A ++ (l.drop A).drop (B - A)).Sublist (l.take A ++ l.drop A) :=
      List.Sublist.append (List.Sublist.refl _) (List.drop_sublist _ _)
    rw [h1]
    simpa using h2
  exact hsub.nodup hnd
lemma Cadre.no_mid [Nontrivial V] [DecidableRel G.Adj] {x₀ : V} {l : List V}
    (hconn : G.Connected) (hb : ∀ c : V, (G.induce {x | x ≠ c}).Connected)
    (hH : ∀ x, distEven G x ≤ 1 + secondSmallestDegree G)
    (hmin : ∀ v, G.degree x₀ ≤ G.degree v)
    (hx0 : ∀ v, v ≠ x₀ → secondSmallestDegree G ≤ G.degree v)
    (hδ : ∀ v, 2 ≤ G.degree v) (hne : l ≠ []) (hnd : l.Nodup) (hch : l.IsChain G.Adj)
    (hmem : x₀ ∈ l) (hhd : l.head hne ≠ x₀) (hlast : l.getLast hne ≠ x₀)
    (hmax : ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → x₀ ∈ l' → l'.length ≤ l.length)
    (hlt : l.length < Fintype.card V)
    (s : List V) (hs : s ≠ []) (snd : s.Nodup) (sch : s.IsChain G.Adj) (sl : ∀ v ∈ s, v ∉ l) (a b : ℕ) (hab : a < b) (hb' : b < l.length)
    (h1 : G.Adj (l.getD a x₀) (s.head hs)) (h2 : G.Adj (s.getLast hs) (l.getD b x₀))
    (hx : ∀ i, a < i → i < b → l.getD i x₀ ≠ x₀) (hlen : b - a - 1 < s.length) : False := by
  have hT : (l.take (a + 1)).length = a + 1 := by simp; omega
  have hD : (l.drop b).length = l.length - b := by simp
  refine Cadre.no_longer hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt
    (l.take (a + 1) ++ s ++ l.drop b) ?_ ?_ ?_ ?_
  · have hTD := b5_nodup_td hnd (A := a + 1) (B := b) (by omega)
    rw [List.nodup_append]
    refine ⟨List.nodup_append.2 ⟨hnd.sublist (List.take_sublist _ _), snd, ?_⟩,
      hnd.sublist (List.drop_sublist _ _), ?_⟩
    · intro x hx y hy hxy
      exact sl y hy (hxy ▸ List.take_subset _ _ hx)
    · intro x hx y hy
      rcases List.mem_append.mp hx with hx | hx
      · exact (List.nodup_append.1 hTD).2.2 x hx y hy
      · rintro rfl
        exact sl x hx (List.drop_subset _ _ hy)
  · refine b5_chain3 hs (hch.take _) sch (hch.drop _) ?_ ?_
    · intro x hx y hy
      rw [b5_last_take x₀ (by omega)] at hx
      rw [List.head?_eq_head hs] at hy
      simp only [Option.mem_def, Option.some.injEq] at hx hy
      subst hx; subst hy; exact h1
    · intro x hx y hy
      rw [b5_head_drop x₀ hb'] at hy
      rw [List.getLast?_eq_getLast hs] at hx
      simp only [Option.mem_def, Option.some.injEq] at hx hy
      subst hx; subst hy; exact h2
  · obtain ⟨i, hi, hxi⟩ := b5_idx hmem
    have hc : i < a + 1 ∨ b ≤ i := by
      by_contra hcon
      push Not at hcon
      exact hx i (by omega) hcon.2 (by rw [hxi])
    rcases b5_mem_td hi hxi hc with h | h
    · simp [h]
    · simp [h]
  · simp only [List.length_append, hT, hD]
    omega
lemma ring_card (J : Finset ℕ) (h0 : 0 ∉ J) :
    (J.image (· + 1) ∪ J.image (· - 1)).card + (J.filter (fun j => j + 2 ∈ J)).card =
      2 * J.card := by
  have h1 : (J.image (· + 1)).card = J.card :=
    Finset.card_image_of_injective _ (add_left_injective 1)
  have h2 : (J.image (· - 1)).card = J.card := by
    refine Finset.card_image_of_injOn ?_
    intro a ha b hb hab
    have ha0 : a ≠ 0 := fun h => h0 (h ▸ ha)
    have hb0 : b ≠ 0 := fun h => h0 (h ▸ hb)
    simp only at hab
    omega
  have h3 : J.image (· + 1) ∩ J.image (· - 1) = (J.filter (fun j => j + 2 ∈ J)).image (· + 1) := by
    ext x
    simp only [Finset.mem_inter, Finset.mem_image, Finset.mem_filter]
    constructor
    · rintro ⟨⟨a, ha, rfl⟩, ⟨b, hb, hbx⟩⟩
      have hb0 : b ≠ 0 := fun h => h0 (h ▸ hb)
      refine ⟨a, ⟨ha, ?_⟩, rfl⟩
      have : b = a + 2 := by omega
      rw [← this]; exact hb
    · rintro ⟨a, ⟨ha, ha2⟩, rfl⟩
      exact ⟨⟨a, ha, rfl⟩, ⟨a + 2, ha2, by simp⟩⟩
  have h4 : ((J.filter (fun j => j + 2 ∈ J)).image (· + 1)).card = (J.filter (fun j => j + 2 ∈ J)).card :=
    Finset.card_image_of_injective _ (add_left_injective 1)
  have h5 := Finset.card_union_add_card_inter (J.image (· + 1)) (J.image (· - 1))
  rw [h3, h4, h1, h2] at h5
  omega
lemma T_lt (J : Finset ℕ) (hJ : J.Nonempty) :
    (J.filter (fun j => j + 2 ∈ J)).card + 1 ≤ J.card := by
  have hsub : J.filter (fun j => j + 2 ∈ J) ⊆ J.erase (J.max' hJ) := by
    intro j hj
    rw [Finset.mem_filter] at hj
    rw [Finset.mem_erase]
    refine ⟨?_, hj.1⟩
    have := Finset.le_max' J _ hj.2
    omega
  have := Finset.card_le_card hsub
  rw [Finset.card_erase_of_mem (Finset.max'_mem J hJ)] at this
  have := Finset.card_pos.mpr hJ
  omega
lemma Cadre.J_bounds [Nontrivial V] [DecidableRel G.Adj] {x₀ : V} {l : List V}
    (hconn : G.Connected) (hb : ∀ c : V, (G.induce {x | x ≠ c}).Connected)
    (hH : ∀ x, distEven G x ≤ 1 + secondSmallestDegree G)
    (hmin : ∀ v, G.degree x₀ ≤ G.degree v)
    (hx0 : ∀ v, v ≠ x₀ → secondSmallestDegree G ≤ G.degree v)
    (hδ : ∀ v, 2 ≤ G.degree v) (hne : l ≠ []) (hnd : l.Nodup) (hch : l.IsChain G.Adj)
    (hmem : x₀ ∈ l) (hhd : l.head hne ≠ x₀) (hlast : l.getLast hne ≠ x₀)
    (hmax : ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → x₀ ∈ l' → l'.length ≤ l.length)
    (hlt : l.length < Fintype.card V)
    {y : V} (hy : y ∉ l) {j : ℕ} (hj : j ∈ ((Finset.range l.length).filter (fun i => G.Adj y (l.getD i x₀)))) : 0 < j ∧ j + 1 < l.length := by
  rw [Finset.mem_filter, Finset.mem_range] at hj
  obtain ⟨hjl, hadj⟩ := hj
  have hhs := Cadre.hmax_sup hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt
  have hgd : l.getD j y = l.getD j x₀ := by
    rw [List.getD_eq_getElem _ _ hjl, List.getD_eq_getElem _ _ hjl]
  have := lemma5abx hconn l hne hnd hch hhs y hy j hjl (by rw [hgd]; exact hadj)
  exact ⟨this.1, this.2.1⟩
lemma Cadre.dset_dist [Nontrivial V] [DecidableRel G.Adj] {x₀ : V} {l : List V}
    (hconn : G.Connected) (hb : ∀ c : V, (G.induce {x | x ≠ c}).Connected)
    (hH : ∀ x, distEven G x ≤ 1 + secondSmallestDegree G)
    (hmin : ∀ v, G.degree x₀ ≤ G.degree v)
    (hx0 : ∀ v, v ≠ x₀ → secondSmallestDegree G ≤ G.degree v)
    (hδ : ∀ v, 2 ≤ G.degree v) (hne : l ≠ []) (hnd : l.Nodup) (hch : l.IsChain G.Adj)
    (hmem : x₀ ∈ l) (hhd : l.head hne ≠ x₀) (hlast : l.getLast hne ≠ x₀)
    (hmax : ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → x₀ ∈ l' → l'.length ≤ l.length)
    (hlt : l.length < Fintype.card V)
    {y : V} (hy : y ∉ l) {i : ℕ} (hi : i ∈ (((Finset.range l.length).filter (fun i => G.Adj y (l.getD i x₀))).image (· + 1) ∪ ((Finset.range l.length).filter (fun i => G.Adj y (l.getD i x₀))).image (· - 1))) :
    i < l.length ∧ G.dist y (l.getD i x₀) = 2 := by
  have hhs := Cadre.hmax_sup hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt
  simp only [Finset.mem_union, Finset.mem_image, Finset.mem_filter, Finset.mem_range] at hi
  have key : ∀ j, j < l.length → G.Adj y (l.getD j x₀) →
      (j + 1 < l.length ∧ G.dist y (l.getD (j + 1) x₀) = 2) ∧
        (0 < j ∧ G.dist y (l.getD (j - 1) x₀) = 2) := by
    intro j hjl hadj
    have hgd : ∀ k, k < l.length → l.getD k y = l.getD k x₀ := by
      intro k hk; rw [List.getD_eq_getElem _ _ hk, List.getD_eq_getElem _ _ hk]
    have h5 := lemma5abx hconn l hne hnd hch hhs y hy j hjl (by rw [hgd j hjl]; exact hadj)
    obtain ⟨h0, h1, h2, h3, -, -⟩ := h5
    have hk1 : j + 1 < l.length := h1
    have hk2 : j - 1 < l.length := by omega
    rw [hgd _ hk1] at h2
    rw [hgd _ hk2] at h3
    have hch' : ∀ k, k + 1 < l.length → G.Adj (l.getD k x₀) (l.getD (k + 1) x₀) := by
      intro k hk
      have := List.isChain_iff_getElem.mp hch k hk
      rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ hk]
      exact this
    have hne1 : l.getD (j + 1) x₀ ≠ y := by
      intro h; apply hy; rw [← h, List.getD_eq_getElem _ _ hk1]; exact List.getElem_mem _
    have hne2 : l.getD (j - 1) x₀ ≠ y := by
      intro h; apply hy; rw [← h, List.getD_eq_getElem _ _ hk2]; exact List.getElem_mem _
    refine ⟨⟨hk1, dist_two hconn hadj (hch' j hk1) h2 hne1⟩, ⟨h0, ?_⟩⟩
    have hj1 : j - 1 + 1 = j := by omega
    have hc2 : G.Adj (l.getD j x₀) (l.getD (j - 1) x₀) := by
      have := hch' (j - 1) (by omega)
      rw [hj1] at this
      exact this.symm
    exact dist_two hconn hadj hc2 h3 hne2
  rcases hi with ⟨j, ⟨hjl, hadj⟩, rfl⟩ | ⟨j, ⟨hjl, hadj⟩, rfl⟩
  · exact ⟨(key j hjl hadj).1.1, (key j hjl hadj).1.2⟩
  · have := (key j hjl hadj).2
    exact ⟨by omega, this.2⟩
lemma Cadre.degree_split [Nontrivial V] [DecidableRel G.Adj] {x₀ : V} {l : List V}
    (hconn : G.Connected) (hb : ∀ c : V, (G.induce {x | x ≠ c}).Connected)
    (hH : ∀ x, distEven G x ≤ 1 + secondSmallestDegree G)
    (hmin : ∀ v, G.degree x₀ ≤ G.degree v)
    (hx0 : ∀ v, v ≠ x₀ → secondSmallestDegree G ≤ G.degree v)
    (hδ : ∀ v, 2 ≤ G.degree v) (hne : l ≠ []) (hnd : l.Nodup) (hch : l.IsChain G.Adj)
    (hmem : x₀ ∈ l) (hhd : l.head hne ≠ x₀) (hlast : l.getLast hne ≠ x₀)
    (hmax : ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → x₀ ∈ l' → l'.length ≤ l.length)
    (hlt : l.length < Fintype.card V)
    {y : V} (hy : y ∉ l) :
    G.degree y = (((Finset.range l.length).filter (fun i => G.Adj y (l.getD i x₀)))).card + ((Finset.univ.filter (fun t => t ∉ l)).filter (G.Adj y)).card := by
  classical
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  have hdisj : Disjoint (((Finset.range l.length).filter (fun i => G.Adj y (l.getD i x₀))).image
      (fun i => l.getD i x₀)) ((Finset.univ.filter (fun t => t ∉ l)).filter (G.Adj y)) := by
    rw [Finset.disjoint_left]
    intro w hw1 hw2
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_range, Finset.mem_univ, true_and] at hw1 hw2
    obtain ⟨i, ⟨hi, _⟩, rfl⟩ := hw1
    apply hw2.1
    rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem _
  have hN : G.neighborFinset y = ((Finset.range l.length).filter (fun i => G.Adj y (l.getD i x₀))).image
      (fun i => l.getD i x₀) ∪ ((Finset.univ.filter (fun t => t ∉ l)).filter (G.Adj y)) := by
    ext w
    simp only [SimpleGraph.mem_neighborFinset, Finset.mem_union, Finset.mem_image, Finset.mem_filter,
      Finset.mem_range, Finset.mem_univ, true_and]
    constructor
    · intro hw
      by_cases hwl : w ∈ l
      · left
        obtain ⟨i, hi, hiw⟩ := List.mem_iff_getElem.mp hwl
        refine ⟨i, ⟨hi, ?_⟩, ?_⟩
        · rw [List.getD_eq_getElem _ _ hi, hiw]; exact hw
        · rw [List.getD_eq_getElem _ _ hi, hiw]
      · right; exact ⟨hwl, hw⟩
    · rintro (⟨i, ⟨hi, hadj⟩, rfl⟩ | ⟨_, hw⟩)
      · exact hadj
      · exact hw
  rw [hN, Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injOn]
  intro i hi j hj hij
  simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq] at hi hj
  simp only at hij
  rw [List.getD_eq_getElem _ _ hi.1, List.getD_eq_getElem _ _ hj.1] at hij
  exact (List.Nodup.getElem_inj_iff hnd).mp hij
lemma Cadre.count_Q2 [Nontrivial V] [DecidableRel G.Adj] {x₀ : V} {l : List V}
    (hconn : G.Connected) (hb : ∀ c : V, (G.induce {x | x ≠ c}).Connected)
    (hH : ∀ x, distEven G x ≤ 1 + secondSmallestDegree G)
    (hmin : ∀ v, G.degree x₀ ≤ G.degree v)
    (hx0 : ∀ v, v ≠ x₀ → secondSmallestDegree G ≤ G.degree v)
    (hδ : ∀ v, 2 ≤ G.degree v) (hne : l ≠ []) (hnd : l.Nodup) (hch : l.IsChain G.Adj)
    (hmem : x₀ ∈ l) (hhd : l.head hne ≠ x₀) (hlast : l.getLast hne ≠ x₀)
    (hmax : ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → x₀ ∈ l' → l'.length ≤ l.length)
    (hlt : l.length < Fintype.card V)
    (y : V) (hy : y ∉ l) (Bp K2 : Finset V)
    (hB : ∀ w ∈ Bp, w ∈ l ∧ ¬ G.Adj y w ∧ ∃ z, z ∉ l ∧ G.Adj y z ∧ G.Adj z w)
    (hK : ∀ w ∈ K2, w ∉ l ∧ w ≠ y ∧ ¬ G.Adj y w ∧ ∃ z, G.Adj y z ∧ G.Adj z w) :
    ((((Finset.range l.length).filter (fun i => G.Adj y (l.getD i x₀))).image (· + 1) ∪ ((Finset.range l.length).filter (fun i => G.Adj y (l.getD i x₀))).image (· - 1))).card + Bp.card + K2.card ≤ secondSmallestDegree G := by
  classical
  have hhs := Cadre.hmax_sup hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt
  have hDd : ∀ i ∈ (((Finset.range l.length).filter (fun i => G.Adj y (l.getD i x₀))).image (· + 1) ∪ ((Finset.range l.length).filter (fun i => G.Adj y (l.getD i x₀))).image (· - 1)),
      i < l.length ∧ G.dist y (l.getD i x₀) = 2 := fun i hi =>
    Cadre.dset_dist hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt hy hi
  have hdisjDB : Disjoint ((((Finset.range l.length).filter (fun i => G.Adj y (l.getD i x₀))).image (· + 1) ∪ ((Finset.range l.length).filter (fun i => G.Adj y (l.getD i x₀))).image (· - 1)).image (fun i => l.getD i x₀)) Bp := by
    rw [Finset.disjoint_left]
    intro w hw1 hw2
    obtain ⟨i, hiD, rfl⟩ := Finset.mem_image.mp hw1
    obtain ⟨-, -, z, hz, hyz, hzw⟩ := hB _ hw2
    simp only [Finset.mem_union, Finset.mem_image, Finset.mem_filter, Finset.mem_range] at hiD
    rcases hiD with ⟨j, ⟨hjl, hadj⟩, rfl⟩ | ⟨j, ⟨hjl, hadj⟩, rfl⟩
    · have hjb := Cadre.J_bounds hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt hy
        (j := j) (by simp only [Finset.mem_filter, Finset.mem_range]; exact ⟨hjl, hadj⟩)
      refine Cadre.no_mid hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt [y, z] (by simp) (by simp; exact G.ne_of_adj hyz) (by simp [hyz]) (by intro v hv; simp at hv; rcases hv with rfl | rfl <;> assumption) j (j + 1) (by omega) hjb.2 (by simpa using hadj.symm) (by simpa using hzw) (by intro i h1 h2; omega) (by simp)
    · have hjb := Cadre.J_bounds hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt hy
        (j := j) (by simp only [Finset.mem_filter, Finset.mem_range]; exact ⟨hjl, hadj⟩)
      refine Cadre.no_mid hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt [z, y] (by simp) (by simp; exact (G.ne_of_adj hyz).symm) (by simp [hyz.symm]) (by intro v hv; simp at hv; rcases hv with rfl | rfl <;> assumption) (j - 1) j (by omega) (by omega) (by simpa using hzw.symm) (by simpa using hadj) (by intro i h1 h2; omega) (by simp only [List.length_cons, List.length_nil]; omega)
  have hdisjK : Disjoint ((((Finset.range l.length).filter (fun i => G.Adj y (l.getD i x₀))).image (· + 1) ∪ ((Finset.range l.length).filter (fun i => G.Adj y (l.getD i x₀))).image (· - 1)).image (fun i => l.getD i x₀) ∪ Bp) K2 := by
    rw [Finset.disjoint_left]
    intro w hw1 hw2
    have hwl : w ∈ l := by
      rcases Finset.mem_union.mp hw1 with h | h
      · obtain ⟨i, hiD, rfl⟩ := Finset.mem_image.mp h
        rw [List.getD_eq_getElem _ _ (hDd i hiD).1]; exact List.getElem_mem _
      · exact (hB w h).1
    exact (hK w hw2).1 hwl
  have hinj : Set.InjOn (fun i => l.getD i x₀) (((((Finset.range l.length).filter (fun i => G.Adj y (l.getD i x₀))).image (· + 1) ∪ ((Finset.range l.length).filter (fun i => G.Adj y (l.getD i x₀))).image (· - 1)) : Finset ℕ) : Set ℕ) := by
    intro i hi j hj hij
    have hi' := (hDd i hi).1
    have hj' := (hDd j hj).1
    simp only at hij
    rw [List.getD_eq_getElem _ _ hi', List.getD_eq_getElem _ _ hj'] at hij
    exact (List.Nodup.getElem_inj_iff hnd).mp hij
  have hcard := card_le_gamma hconn hH y
    ((((((Finset.range l.length).filter (fun i => G.Adj y (l.getD i x₀))).image (· + 1) ∪ ((Finset.range l.length).filter (fun i => G.Adj y (l.getD i x₀))).image (· - 1)).image (fun i => l.getD i x₀) ∪ Bp) ∪ K2)) (by
      intro w hw
      rcases Finset.mem_union.mp hw with h | h
      · rcases Finset.mem_union.mp h with h | h
        · obtain ⟨i, hiD, rfl⟩ := Finset.mem_image.mp h
          exact (hDd i hiD).2
        · obtain ⟨hwl, hnadj, z, -, hyz, hzw⟩ := hB w h
          exact dist_two hconn hyz hzw hnadj (fun h => hy (h ▸ hwl))
      · obtain ⟨-, hwy, hnadj, z, hyz, hzw⟩ := hK w h
        exact dist_two hconn hyz hzw hnadj hwy)
  rw [Finset.card_union_of_disjoint hdisjK, Finset.card_union_of_disjoint hdisjDB,
    Finset.card_image_of_injOn hinj] at hcard
  exact hcard
lemma b15_adj {l : List V} (d : V) (hch : l.IsChain G.Adj) {i : ℕ} (hi : i + 1 < l.length) :
    G.Adj (l.getD i d) (l.getD (i + 1) d) := by
  rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ hi]
  exact List.isChain_iff_getElem.1 hch i hi
lemma b15_inj {l : List V} (d : V) (hnd : l.Nodup) {i j : ℕ} (hi : i < l.length)
    (hj : j < l.length) (h : l.getD i d = l.getD j d) : i = j := by
  rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hj] at h
  exact (List.Nodup.getElem_inj_iff hnd).1 h
lemma b15_mem {l : List V} (d : V) {i : ℕ} (hi : i < l.length) : l.getD i d ∈ l := by
  rw [List.getD_eq_getElem _ _ hi]
  exact List.getElem_mem _
lemma b15_dflt {l : List V} {i : ℕ} (hi : i < l.length) (d d' : V) : l.getD i d = l.getD i d' := by
  rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hi]
lemma b17_decomp (l : List V) (d : V) {i : ℕ} (hi : i + 1 < l.length) :
    l = l.take i ++ l.getD i d :: l.getD (i + 1) d :: l.drop (i + 2) := by
  have h := List.take_append_drop i l
  rw [List.drop_eq_getElem_cons (by omega), List.drop_eq_getElem_cons (by omega)] at h
  rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ hi]
  exact h.symm
lemma b17_long {x₀ : V} {l s c : List V} (hnd : l.Nodup) (sl : ∀ v ∈ s, v ∉ l)
    (snd : s.Nodup) (hs : s ≠ []) (hmem : x₀ ∈ l)
    (hmax : ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → x₀ ∈ l' → l'.length ≤ l.length)
    (hc : c.Perm (s ++ l)) (hch : c.IsChain G.Adj) : False := by
  have hnd' : (s ++ l).Nodup :=
    List.nodup_append.2 ⟨snd, hnd, (fun a ha b hb h => sl a ha (h ▸ hb))⟩
  have h := hmax c (hc.nodup_iff.2 hnd') hch (hc.mem_iff.2 (List.mem_append_right _ hmem))
  rw [hc.length_eq, List.length_append] at h
  have := List.length_pos_of_ne_nil hs
  omega
lemma b17_perm1 (t d s : List V) (u x : V) :
    (t ++ x :: u :: (s ++ d)).Perm (s ++ (t ++ u :: x :: d)) := by
  refine List.perm_iff_count.2 (fun a => ?_)
  simp only [List.count_append, List.count_cons]
  split_ifs <;> omega
lemma b17_perm2 (t d s : List V) (w x : V) :
    (t ++ (s ++ w :: x :: d)).Perm (s ++ (t ++ x :: w :: d)) := by
  refine List.perm_iff_count.2 (fun a => ?_)
  simp only [List.count_append, List.count_cons]
  split_ifs <;> omega
lemma b17_head_app {s : List V} (hs : s ≠ []) (d : List V) : (s ++ d).head? = some (s.head hs) := by
  cases s with
  | nil => exact absurd rfl hs
  | cons a t => rfl
lemma b17_last_take {l : List V} (d : V) {p : ℕ} (hp : 1 ≤ p) (hpl : p ≤ l.length) :
    (l.take p).getLast? = some (l.getD (p - 1) d) := by
  rw [List.getLast?_take, if_neg (by omega), List.getD_eq_getElem _ _ (by omega)]
  simp [List.getElem?_eq_getElem (by omega : p - 1 < l.length)]
lemma b17_head_drop {l : List V} (d : V) {n : ℕ} (hn : n < l.length) :
    (l.drop n).head? = some (l.getD n d) := by
  rw [List.head?_drop, List.getD_eq_getElem _ _ hn, List.getElem?_eq_getElem hn]
lemma Cadre.hole_x0 [Nontrivial V] [DecidableRel G.Adj] {x₀ : V} {l : List V}
    (hconn : G.Connected) (hb : ∀ c : V, (G.induce {x | x ≠ c}).Connected)
    (hH : ∀ x, distEven G x ≤ 1 + secondSmallestDegree G)
    (hmin : ∀ v, G.degree x₀ ≤ G.degree v)
    (hx0 : ∀ v, v ≠ x₀ → secondSmallestDegree G ≤ G.degree v)
    (hδ : ∀ v, 2 ≤ G.degree v) (hne : l ≠ []) (hnd : l.Nodup) (hch : l.IsChain G.Adj)
    (hmem : x₀ ∈ l) (hhd : l.head hne ≠ x₀) (hlast : l.getLast hne ≠ x₀)
    (hmax : ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → x₀ ∈ l' → l'.length ≤ l.length)
    (hlt : l.length < Fintype.card V)
    (S : Finset V) (hS : ∀ y ∈ S, y ∉ l) (p : ℕ) (hp : 1 ≤ p) (hp3 : p + 3 < l.length)
    (hx : l.getD (p + 1) x₀ = x₀)
    (hSA : ∀ y ∈ S, G.Adj y (l.getD p x₀) ∨ G.Adj y (l.getD (p + 2) x₀))
    (s : List V) (hs : s ≠ []) (snd : s.Nodup) (sch : s.IsChain G.Adj) (sl : ∀ v ∈ s, v ∉ l)
    (h1 : G.Adj (l.getD p x₀) (s.head hs)) (h2 : G.Adj (s.getLast hs) (l.getD (p + 2) x₀)) :
    S.card + 2 ≤ secondSmallestDegree G := by
  have hp2 : p + 2 < l.length := by omega
  have hA : G.Adj (l.getD p x₀) x₀ := by
    have := b15_adj (G := G) x₀ hch (i := p) (by omega)
    rwa [hx] at this
  have hB : G.Adj x₀ (l.getD (p + 2) x₀) := by
    have := b15_adj (G := G) x₀ hch (i := p + 1) (by omega)
    rwa [hx] at this
  have hAa : G.Adj (l.getD (p - 1) x₀) (l.getD p x₀) := by
    have := b15_adj (G := G) x₀ hch (i := p - 1) (by omega)
    rwa [Nat.sub_add_cancel hp] at this
  have hBb : G.Adj (l.getD (p + 2) x₀) (l.getD (p + 3) x₀) :=
    b15_adj (G := G) x₀ hch (i := p + 2) (by omega)
  have hsl := List.getLast?_eq_getLast hs
  have hna : ¬ G.Adj (l.getD (p - 1) x₀) x₀ := by
    intro hadj
    refine b17_long (l := l) (s := s) (c := l.take p ++ x₀ :: l.getD p x₀ :: (s ++ l.drop (p + 2)))
      hnd sl snd hs hmem hmax ?_ ?_
    · have hd := b17_decomp l x₀ (i := p) (by omega)
      rw [hx] at hd
      have := b17_perm1 (l.take p) (l.drop (p + 2)) s (l.getD p x₀) x₀
      rwa [← hd] at this
    · refine List.isChain_append.2 ⟨hch.take _, ?_, ?_⟩
      · refine List.isChain_cons.2 ⟨?_, List.isChain_cons.2 ⟨?_, List.isChain_append.2 ⟨sch, hch.drop _, ?_⟩⟩⟩
        · intro z hz
          simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hz
          subst hz; exact hA.symm
        · intro z hz
          rw [b17_head_app hs, Option.mem_def, Option.some.injEq] at hz
          subst hz; exact h1
        · intro z hz w hw
          rw [hsl, Option.mem_def, Option.some.injEq] at hz
          rw [b17_head_drop x₀ hp2, Option.mem_def, Option.some.injEq] at hw
          subst hz hw; exact h2
      · intro z hz w hw
        rw [b17_last_take x₀ hp (by omega), Option.mem_def, Option.some.injEq] at hz
        simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hw
        subst hz hw; exact hadj
  have hnb : ¬ G.Adj x₀ (l.getD (p + 3) x₀) := by
    intro hadj
    refine b17_long (l := l) (s := s) (c := l.take (p + 1) ++ (s ++ l.getD (p + 2) x₀ :: x₀ :: l.drop (p + 3)))
      hnd sl snd hs hmem hmax ?_ ?_
    · have hd := b17_decomp l x₀ (i := p + 1) (by omega)
      rw [hx] at hd
      have := b17_perm2 (l.take (p + 1)) (l.drop (p + 1 + 2)) s (l.getD (p + 1 + 1) x₀) x₀
      rwa [← hd] at this
    · refine List.isChain_append.2 ⟨hch.take _, List.isChain_append.2 ⟨sch, ?_, ?_⟩, ?_⟩
      · refine List.isChain_cons.2 ⟨?_, List.isChain_cons.2 ⟨?_, hch.drop _⟩⟩
        · intro z hz
          simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hz
          subst hz; exact hB.symm
        · intro z hz
          rw [b17_head_drop x₀ (by omega), Option.mem_def, Option.some.injEq] at hz
          subst hz; exact hadj
      · intro z hz w hw
        rw [hsl, Option.mem_def, Option.some.injEq] at hz
        simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hw
        subst hz hw; exact h2
      · intro z hz w hw
        rw [List.getLast?_take, if_neg (by omega)] at hz
        have hw' := hw
        rw [b17_head_app hs, Option.mem_def, Option.some.injEq] at hw'
        subst hw'
        simp only [List.getElem?_eq_getElem (by omega : p + 1 - 1 < l.length), Option.some_or,
          Option.mem_def, Option.some.injEq] at hz
        subst hz
        have e1 : l[p + 1 - 1]'(by omega) = l.getD p x₀ := by
          rw [List.getD_eq_getElem _ _ (by omega)]; simp
        rw [e1]; exact h1
  have hne_a : l.getD (p - 1) x₀ ≠ x₀ := by
    intro h
    have := b15_inj x₀ hnd (by omega) (by omega) (h.trans hx.symm)
    omega
  have hne_b : l.getD (p + 3) x₀ ≠ x₀ := by
    intro h
    have := b15_inj x₀ hnd (by omega) (by omega) (h.trans hx.symm)
    omega
  have hab : l.getD (p - 1) x₀ ≠ l.getD (p + 3) x₀ := by
    intro h
    have := b15_inj x₀ hnd (by omega) (by omega) h
    omega
  have hSd : ∀ y ∈ S, G.dist x₀ y = 2 := by
    intro y hy
    have hyl := hS y hy
    have hyx : y ≠ x₀ := fun h => hyl (h ▸ hmem)
    have hmx := Cadre.hmax_sup hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt
    have key : ¬ G.Adj y x₀ := by
      intro hadj
      have hadj' : G.Adj y (l.getD (p + 1) y) := by
        rw [b15_dflt (l := l) (i := p + 1) (by omega) y x₀, hx]; exact hadj
      obtain ⟨-, -, h5, h6, -, -⟩ := lemma5abx hconn l hne hnd hch hmx y hyl (p + 1) (by omega) hadj'
      rw [Nat.add_sub_cancel] at h6
      rcases hSA y hy with h | h
      · exact h6 (by rwa [b15_dflt (l := l) (i := p) (by omega) y x₀])
      · exact h5 (by rwa [b15_dflt (l := l) (i := p + 1 + 1) (by omega) y x₀])
    rcases hSA y hy with h | h
    · exact dist_two hconn hA.symm h.symm (fun h' => key h'.symm) hyx
    · exact dist_two hconn hB h.symm (fun h' => key h'.symm) hyx
  have hall : ∀ w ∈ insert (l.getD (p - 1) x₀) (insert (l.getD (p + 3) x₀) S), G.dist x₀ w = 2 := by
    intro w hw
    rcases Finset.mem_insert.1 hw with rfl | hw
    · exact dist_two hconn hA.symm hAa.symm (fun h' => hna h'.symm) hne_a
    rcases Finset.mem_insert.1 hw with rfl | hw
    · exact dist_two hconn hB hBb hnb hne_b
    · exact hSd w hw
  have hc := card_le_gamma hconn hH x₀ _ hall
  have hAS : l.getD (p - 1) x₀ ∉ S := fun h => hS _ h (b15_mem x₀ (by omega))
  have hBS : l.getD (p + 3) x₀ ∉ S := fun h => hS _ h (b15_mem x₀ (by omega))
  rw [Finset.card_insert_of_notMem (by rw [Finset.mem_insert]; rintro (h | h); exacts [hab h, hAS h]),
    Finset.card_insert_of_notMem hBS] at hc
  omega
lemma b10_side [Nontrivial V] [DecidableRel G.Adj] {x₀ : V} {l : List V}
    (hconn : G.Connected) (hb : ∀ c : V, (G.induce {x | x ≠ c}).Connected)
    (hH : ∀ x, distEven G x ≤ 1 + secondSmallestDegree G)
    (hmin : ∀ v, G.degree x₀ ≤ G.degree v)
    (hx0 : ∀ v, v ≠ x₀ → secondSmallestDegree G ≤ G.degree v)
    (hδ : ∀ v, 2 ≤ G.degree v) (hne : l ≠ []) (hnd : l.Nodup) (hch : l.IsChain G.Adj)
    (hmem : x₀ ∈ l) (hhd : l.head hne ≠ x₀) (hlast : l.getLast hne ≠ x₀)
    (hmax : ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → x₀ ∈ l' → l'.length ≤ l.length)
    (hlt : l.length < Fintype.card V)
    (y z : V) (hy : y ∉ l) (hz : z ∉ l) (hyz : G.Adj y z)
    (hNy : ∀ w, w ∉ l → G.Adj y w → w = z) :
    (∀ i, i < l.length → G.Adj z (l.getD i x₀) → G.Adj y (l.getD i x₀)) ∧
    secondSmallestDegree G = ((Finset.range l.length).filter (fun i => G.Adj y (l.getD i x₀))).card + 1 ∧
    ((((Finset.range l.length).filter (fun i => G.Adj y (l.getD i x₀))).filter (fun j => j + 2 ∈ ((Finset.range l.length).filter (fun i => G.Adj y (l.getD i x₀))))).card + 1 =
      ((Finset.range l.length).filter (fun i => G.Adj y (l.getD i x₀))).card) := by
  classical
  obtain ⟨J, hJ⟩ : ∃ J : Finset ℕ, J = (Finset.range l.length).filter (fun i => G.Adj y (l.getD i x₀)) := ⟨_, rfl⟩
  rw [← hJ]
  have hjb : ∀ j ∈ J, 0 < j ∧ j + 1 < l.length := by
    intro j hj
    rw [hJ] at hj
    exact Cadre.J_bounds hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt hy hj
  have h0 : 0 ∉ J := fun h => (Nat.lt_irrefl 0) (hjb 0 h).1
  have hdeg := Cadre.degree_split hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt hy
  rw [← hJ] at hdeg
  have hR : (Finset.univ.filter (fun t => t ∉ l)).filter (G.Adj y) = {z} := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · rintro ⟨hw, hadj⟩; exact hNy w hw hadj
    · rintro rfl; exact ⟨hz, hyz⟩
  rw [hR, Finset.card_singleton] at hdeg
  have hy0 : y ≠ x₀ := fun h => hy (h ▸ hmem)
  have hdy := hx0 y hy0
  have hσ2 := sigma_ge hδ
  obtain ⟨Bp, hBp⟩ : ∃ Bp : Finset V, Bp = Finset.univ.filter (fun w => w ∈ l ∧ ¬ G.Adj y w ∧ G.Adj z w) := ⟨_, rfl⟩
  have hQ := Cadre.count_Q2 hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt y hy Bp ∅
    (by
      intro w hw
      rw [hBp] at hw
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
      exact ⟨hw.1, hw.2.1, z, hz, hyz, hw.2.2⟩)
    (by intro w hw; simp at hw)
  rw [← hJ] at hQ
  simp only [Finset.card_empty] at hQ
  have hring := ring_card J h0
  have hJne : J.Nonempty := Finset.card_pos.mp (by omega)
  have hT := T_lt J hJne
  have hBp0 : Bp.card = 0 := by omega
  refine ⟨?_, by omega, by omega⟩
  intro i hi hadj
  by_contra hn
  have hmemBp : l.getD i x₀ ∈ Bp := by
    rw [hBp]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨?_, hn, hadj⟩
    rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem _
  rw [Finset.card_eq_zero.mp hBp0] at hmemBp
  simp at hmemBp
lemma Cadre.no_edge_comp [Nontrivial V] [DecidableRel G.Adj] {x₀ : V} {l : List V}
    (hconn : G.Connected) (hb : ∀ c : V, (G.induce {x | x ≠ c}).Connected)
    (hH : ∀ x, distEven G x ≤ 1 + secondSmallestDegree G)
    (hmin : ∀ v, G.degree x₀ ≤ G.degree v)
    (hx0 : ∀ v, v ≠ x₀ → secondSmallestDegree G ≤ G.degree v)
    (hδ : ∀ v, 2 ≤ G.degree v) (hne : l ≠ []) (hnd : l.Nodup) (hch : l.IsChain G.Adj)
    (hmem : x₀ ∈ l) (hhd : l.head hne ≠ x₀) (hlast : l.getLast hne ≠ x₀)
    (hmax : ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → x₀ ∈ l' → l'.length ≤ l.length)
    (hlt : l.length < Fintype.card V)
    (y z : V) (hy : y ∉ l) (hz : z ∉ l) (hyz : G.Adj y z)
    (hNy : ∀ w, w ∉ l → G.Adj y w → w = z) (hNz : ∀ w, w ∉ l → G.Adj z w → w = y) : False := by
  classical
  obtain ⟨hs1, hσ1, ht1⟩ := b10_side hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt y z hy hz hyz hNy
  obtain ⟨hs2, -, -⟩ := b10_side hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt z y hz hy hyz.symm hNz
  obtain ⟨J, hJ⟩ : ∃ J : Finset ℕ, J = (Finset.range l.length).filter (fun i => G.Adj y (l.getD i x₀)) := ⟨_, rfl⟩
  rw [← hJ] at hσ1 ht1
  have hjb : ∀ j ∈ J, 0 < j ∧ j + 1 < l.length := by
    intro j hj
    rw [hJ] at hj
    exact Cadre.J_bounds hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt hy hj
  have hJmem : ∀ j, j ∈ J ↔ j < l.length ∧ G.Adj y (l.getD j x₀) := by
    intro j; rw [hJ]; simp only [Finset.mem_filter, Finset.mem_range]
  have hσ2 := sigma_ge hδ
  have hxj : ∀ j ∈ J.filter (fun j => j + 2 ∈ J), l.getD (j + 1) x₀ = x₀ := by
    intro j hj
    rw [Finset.mem_filter] at hj
    obtain ⟨hjJ, hj2⟩ := hj
    by_contra hne1
    obtain ⟨hjl, hjadj⟩ := (hJmem j).mp hjJ
    obtain ⟨hj2l, hj2adj⟩ := (hJmem (j + 2)).mp hj2
    exact Cadre.no_mid hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt [y, z] (by simp)
      (by simp; exact G.ne_of_adj hyz) (by simp [hyz])
      (by intro v hv; simp at hv; rcases hv with rfl | rfl <;> assumption) j (j + 2) (by omega) hj2l
      (by simpa using hjadj.symm) (by simpa using hs2 (j + 2) hj2l hj2adj)
      (by intro i h1 h2; have : i = j + 1 := by omega
          subst this; exact hne1) (by simp)
  have hT1 : (J.filter (fun j => j + 2 ∈ J)).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb'
    have ha' := hxj a ha
    have hb'' := hxj b hb'
    have haJ := (Finset.mem_filter.mp ha)
    have hbJ := (Finset.mem_filter.mp hb')
    have hal := (hjb a haJ.1).2
    have hbl := (hjb b hbJ.1).2
    have e1 := ha'
    have e2 := hb''
    rw [List.getD_eq_getElem _ _ hal] at e1
    rw [List.getD_eq_getElem _ _ hbl] at e2
    have := (List.Nodup.getElem_inj_iff hnd).mp (e1.trans e2.symm)
    omega
  have hcpos : 0 < J.card := by omega
  have hc : J.card = 1 ∨ J.card = 2 := by omega
  rcases hc with hc | hc
  ·
    obtain ⟨p, hp⟩ := Finset.card_eq_one.mp hc
    have hpJ : p ∈ J := by rw [hp]; exact Finset.mem_singleton_self p
    obtain ⟨hpl, hpadj⟩ := (hJmem p).mp hpJ
    obtain ⟨hp0, hp1⟩ := hjb p hpJ
    have hxp : l.getD p x₀ ∈ l := by rw [List.getD_eq_getElem _ _ hpl]; exact List.getElem_mem _
    have hidx : ∀ i, i < l.length → G.Adj y (l.getD i x₀) → i = p := by
      intro i hi hadj
      have : i ∈ J := (hJmem i).mpr ⟨hi, hadj⟩
      rw [hp] at this; exact Finset.mem_singleton.mp this
    refine cut_closed hb (l.getD p x₀) {y, z} ?_ ⟨y, by simp⟩ ?_ ?_
    · intro h
      simp only [Finset.mem_insert, Finset.mem_singleton] at h
      rcases h with h | h
      · exact hy (h ▸ hxp)
      · exact hz (h ▸ hxp)
    · intro v hv w hvw hwc
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv ⊢
      by_cases hwl : w ∈ l
      · exfalso
        obtain ⟨i, hi, hiw⟩ := List.mem_iff_getElem.mp hwl
        have hgi : l.getD i x₀ = w := by rw [List.getD_eq_getElem _ _ hi, hiw]
        rcases hv with rfl | rfl
        · have := hidx i hi (by rw [hgi]; exact hvw)
          apply hwc; rw [← hgi, this]
        · have := hidx i hi (hs1 i hi (by rw [hgi]; exact hvw))
          apply hwc; rw [← hgi, this]
      · rcases hv with rfl | rfl
        · exact Or.inr (hNy w hwl hvw)
        · exact Or.inl (hNz w hwl hvw)
    · refine ⟨l.getD 0 x₀, ?_, ?_⟩
      · intro h
        rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ hpl] at h
        have h' := (List.Nodup.getElem_inj_iff hnd).mp h
        omega
      · have h0l : l.getD 0 x₀ ∈ l := by rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _
        intro h
        simp only [Finset.mem_insert, Finset.mem_singleton] at h
        rcases h with h | h
        · exact hy (h ▸ h0l)
        · exact hz (h ▸ h0l)
  ·
    have htc : (J.filter (fun j => j + 2 ∈ J)).card = 1 := by omega
    obtain ⟨j, hj⟩ := Finset.card_pos.mp (by omega : 0 < (J.filter (fun j => j + 2 ∈ J)).card)
    have hxj' := hxj j hj
    obtain ⟨hjJ, hj2⟩ := Finset.mem_filter.mp hj
    obtain ⟨hjl, hjadj⟩ := (hJmem j).mp hjJ
    obtain ⟨hj2l, hj2adj⟩ := (hJmem (j + 2)).mp hj2
    obtain ⟨hj0, -⟩ := hjb j hjJ
    obtain ⟨-, hj3⟩ := hjb (j + 2) hj2
    have hres := Cadre.hole_x0 hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt {y, z}
      (by intro v hv; simp only [Finset.mem_insert, Finset.mem_singleton] at hv
          rcases hv with rfl | rfl <;> assumption) j hj0 (by omega) hxj'
      (by intro v hv; simp only [Finset.mem_insert, Finset.mem_singleton] at hv
          rcases hv with rfl | rfl
          · exact Or.inl hjadj
          · exact Or.inl (hs2 j hjl hjadj))
      [y, z] (by simp) (by simp; exact G.ne_of_adj hyz) (by simp [hyz])
      (by intro v hv; simp at hv; rcases hv with rfl | rfl <;> assumption)
      (by simpa using hjadj.symm) (by simpa using hs2 (j + 2) hj2l hj2adj)
    rw [Finset.card_pair (G.ne_of_adj hyz)] at hres
    omega
lemma Cadre.Rdeg2 [Nontrivial V] [DecidableRel G.Adj] {x₀ : V} {l : List V}
    (hconn : G.Connected) (hb : ∀ c : V, (G.induce {x | x ≠ c}).Connected)
    (hH : ∀ x, distEven G x ≤ 1 + secondSmallestDegree G)
    (hmin : ∀ v, G.degree x₀ ≤ G.degree v)
    (hx0 : ∀ v, v ≠ x₀ → secondSmallestDegree G ≤ G.degree v)
    (hδ : ∀ v, 2 ≤ G.degree v) (hne : l ≠ []) (hnd : l.Nodup) (hch : l.IsChain G.Adj)
    (hmem : x₀ ∈ l) (hhd : l.head hne ≠ x₀) (hlast : l.getLast hne ≠ x₀)
    (hmax : ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → x₀ ∈ l' → l'.length ≤ l.length)
    (hlt : l.length < Fintype.card V)
    (y : V) (hy : y ∉ l) : 2 ≤ ((Finset.univ.filter (fun t => t ∉ l)).filter (G.Adj y)).card := by
  classical
  by_contra hlt2
  push Not at hlt2
  obtain ⟨J, hJ⟩ : ∃ J : Finset ℕ, J = (Finset.range l.length).filter (fun i => G.Adj y (l.getD i x₀)) := ⟨_, rfl⟩
  have hjb : ∀ j ∈ J, 0 < j ∧ j + 1 < l.length := by
    intro j hj
    rw [hJ] at hj
    exact Cadre.J_bounds hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt hy hj
  have h0 : 0 ∉ J := fun h => (Nat.lt_irrefl 0) (hjb 0 h).1
  have hdeg := Cadre.degree_split hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt hy
  rw [← hJ] at hdeg
  have hy0 : y ≠ x₀ := fun h => hy (h ▸ hmem)
  have hdy := hx0 y hy0
  have hσ2 := sigma_ge hδ
  have hring := ring_card J h0
  have hk : ((Finset.univ.filter (fun t => t ∉ l)).filter (G.Adj y)).card = 0 ∨
      ((Finset.univ.filter (fun t => t ∉ l)).filter (G.Adj y)).card = 1 := by omega
  rcases hk with hk | hk
  · have hQ := Cadre.count_Q2 hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt y hy ∅ ∅
      (by intro w hw; simp at hw) (by intro w hw; simp at hw)
    rw [← hJ] at hQ
    simp only [Finset.card_empty] at hQ
    have hJne : J.Nonempty := Finset.card_pos.mp (by omega)
    have hT := T_lt J hJne
    omega
  · obtain ⟨z, hz⟩ := Finset.card_eq_one.mp hk
    have hzmem : z ∈ (Finset.univ.filter (fun t => t ∉ l)).filter (G.Adj y) := by rw [hz]; exact Finset.mem_singleton_self z
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hzmem
    have hNy : ∀ w, w ∉ l → G.Adj y w → w = z := by
      intro w hw hadj
      have : w ∈ (Finset.univ.filter (fun t => t ∉ l)).filter (G.Adj y) := by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨hw, hadj⟩
      rw [hz] at this; exact Finset.mem_singleton.mp this
    by_cases hex : ∃ w, w ∉ l ∧ G.Adj z w ∧ w ≠ y
    · obtain ⟨w, hwl, hzw, hwy⟩ := hex
      have hnadj : ¬ G.Adj y w := by
        intro h
        have := hNy w hwl h
        subst this
        exact G.loopless.irrefl _ hzw
      have hQ := Cadre.count_Q2 hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt y hy ∅ {w}
        (by intro w hw; simp at hw)
        (by intro w' hw'; rw [Finset.mem_singleton] at hw'; subst hw'; exact ⟨hwl, hwy, hnadj, z, hzmem.2, hzw⟩)
      rw [← hJ] at hQ
      simp only [Finset.card_empty, Finset.card_singleton] at hQ
      have hJne : J.Nonempty := Finset.card_pos.mp (by omega)
      have hT := T_lt J hJne
      omega
    · push Not at hex
      exact Cadre.no_edge_comp hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt y z hy hzmem.1 hzmem.2 hNy
        hex
lemma Cadre.m_ge [Nontrivial V] [DecidableRel G.Adj] {x₀ : V} {l : List V}
    (hconn : G.Connected) (hb : ∀ c : V, (G.induce {x | x ≠ c}).Connected)
    (hH : ∀ x, distEven G x ≤ 1 + secondSmallestDegree G)
    (hmin : ∀ v, G.degree x₀ ≤ G.degree v)
    (hx0 : ∀ v, v ≠ x₀ → secondSmallestDegree G ≤ G.degree v)
    (hδ : ∀ v, 2 ≤ G.degree v) (hne : l ≠ []) (hnd : l.Nodup) (hch : l.IsChain G.Adj)
    (hmem : x₀ ∈ l) (hhd : l.head hne ≠ x₀) (hlast : l.getLast hne ≠ x₀)
    (hmax : ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → x₀ ∈ l' → l'.length ≤ l.length)
    (hlt : l.length < Fintype.card V) :
    2 * secondSmallestDegree G + 2 ≤ l.length := by
  classical
  by_contra hcon
  push Not at hcon
  have hhs := Cadre.hmax_sup hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt
  set σ := secondSmallestDegree G with hσ
  set a := l.head hne with ha
  set b := l.getLast hne with hbd
  set m := l.length with hm
  have hm2 : 2 ≤ m := by
    by_contra h2
    have h1 : m = 1 := by have := List.length_pos_of_ne_nil hne; omega
    obtain ⟨e, he⟩ := List.length_eq_one_iff.mp h1
    subst he
    simp at hmem hhd
    exact hhd hmem.symm
  obtain ⟨hNa, hNb, hsum, hdisj, hSd, hTd⟩ := lemma4x hconn l hne hnd hch hhs hlt hm2
  simp only [← ha, ← hbd] at hNa hNb hsum hdisj hSd hTd
  have hxa : σ ≤ G.degree a := hx0 a hhd
  have hxb : σ ≤ G.degree b := hx0 b hlast
  have hsum' : G.degree a + G.degree b + 1 ≤ m := hsum
  have hmσ : m = 2 * σ + 1 := by omega
  set f : ℕ → V := fun i => l.getD i a with hf
  have hf_get : ∀ i (hi : i < m), f i = l[i] := fun i hi => List.getD_eq_getElem _ _ hi
  have hf_mem : ∀ i, i < m → f i ∈ l := fun i hi => by rw [hf_get i hi]; exact List.getElem_mem _
  have hf_inj : ∀ i j, i < m → j < m → f i = f j → i = j := by
    intro i j hi hj h
    rw [hf_get i hi, hf_get j hj] at h
    exact hnd.getElem_inj_iff.mp h
  have hf_ex : ∀ w ∈ l, ∃ i, i < m ∧ f i = w := by
    intro w hw
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hw
    exact ⟨k, hk, hf_get k hk⟩
  have hf0 : f 0 = a := by
    rw [hf_get 0 (by omega)]
    cases l with
    | nil => exact absurd rfl hne
    | cons x t => rfl
  set S := (Finset.range (m - 1)).filter (fun j => G.Adj a (f (j + 1))) with hS
  set T := (Finset.range (m - 1)).filter (fun j => G.Adj (f j) b) with hT
  have hSc : σ ≤ S.card := hxa.trans hSd
  have hTc : σ ≤ T.card := hxb.trans hTd
  have hdisjST : Disjoint S T := by
    refine Finset.disjoint_left.mpr (fun j h1 h2 => ?_)
    simp only [hS, hT, Finset.mem_filter, Finset.mem_range] at h1 h2
    exact hdisj j (by omega) h1.2 h2.2
  have hunion : S ∪ T = Finset.range (m - 1) := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      rcases Finset.mem_union.mp hx with hx | hx <;> exact (Finset.mem_filter.mp hx).1
    · rw [Finset.card_union_of_disjoint hdisjST, Finset.card_range]
      omega
  have hTcard : T.card = σ := by
    have hc := Finset.card_union_of_disjoint hdisjST
    rw [hunion, Finset.card_range] at hc
    omega
  have hpart : ∀ j, j + 1 < m → G.Adj a (f (j + 1)) ∨ G.Adj (f j) b := by
    intro j hj
    have : j ∈ S ∪ T := by rw [hunion]; simp; omega
    rcases Finset.mem_union.mp this with h | h
    · exact Or.inl (Finset.mem_filter.mp h).2
    · exact Or.inr (Finset.mem_filter.mp h).2
  have hNa' : ∀ y, y ∉ l → ¬ G.Adj a y := fun y hy h => hy (hNa y h)
  have hyN : ∀ y, y ∉ l → ∀ j, (hj : j < m) → G.Adj y (f j) → G.Adj a (f j) ∧ f j ≠ a := by
    intro y hy j hj hw
    have hy' : l.getD j y = f j := by
      rw [List.getD_eq_getElem _ _ hj, hf_get j hj]
    obtain ⟨h0, h1, -, -, -, h6⟩ := lemma5abx hconn l hne hnd hch hhs y hy j hj
      (by rw [hy']; exact hw)
    have hy1 : l.getD (j - 1) y = f (j - 1) := by
      rw [List.getD_eq_getElem _ _ (by omega), hf_get (j - 1) (by omega)]
    rw [← hbd, hy1] at h6
    have h6' : ¬ G.Adj b (f (j - 1)) := h6
    refine ⟨?_, fun h => ?_⟩
    · rcases hpart (j - 1) (by omega) with h | h
      · rw [show j - 1 + 1 = j by omega] at h
        exact h
      · exact absurd h.symm h6'
    · have := hf_inj j 0 hj (by omega) (h.trans hf0.symm)
      omega
  have hd2 : ∀ u, u ≠ a → ¬ G.Adj a u → 2 ≤ G.dist a u := by
    intro u hu1 hu2
    have h0 : G.dist a u ≠ 0 := fun h => hu1 (hconn.dist_eq_zero_iff.mp h).symm
    have h1 : G.dist a u ≠ 1 := fun h => hu2 (SimpleGraph.dist_eq_one_iff_adj.mp h)
    omega
  have hdist2 : ∀ y, y ∉ l → ∀ j, (hj : j < m) → G.Adj y (f j) → G.dist a y = 2 := by
    intro y hy j hj hadj
    obtain ⟨h1, -⟩ := hyN y hy j hj hadj
    refine dist_two hconn h1 hadj.symm (hNa' y hy) ?_
    intro h
    exact hy (by rw [h]; exact List.head_mem hne)
  set Timg := T.image (fun i => f (i + 1)) with hTimg
  have hTi_card : Timg.card = σ := by
    rw [hTimg, Finset.card_image_of_injOn, hTcard]
    intro i hi i' hi' h
    have hi1 := Finset.mem_range.mp (Finset.mem_filter.mp hi).1
    have hi1' := Finset.mem_range.mp (Finset.mem_filter.mp hi').1
    have := hf_inj (i + 1) (i' + 1) (by omega) (by omega) h
    omega
  have hTimg_l : ∀ u ∈ Timg, u ∈ l := by
    intro u hu
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hu
    have := Finset.mem_range.mp (Finset.mem_filter.mp hi).1
    exact hf_mem _ (by omega)
  have hTimg_d : ∀ u ∈ Timg, 2 ≤ G.dist a u := by
    intro u hu
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hu
    have hi1 := Finset.mem_range.mp (Finset.mem_filter.mp hi).1
    apply hd2
    · intro h
      have := hf_inj (i + 1) 0 (by omega) (by omega) (h.trans hf0.symm)
      omega
    · intro h
      exact Finset.disjoint_left.mp hdisjST
        (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hi1, h⟩) hi
  have hTim : ∀ k, k < m → k ≠ 0 → ¬ G.Adj a (f k) → f k ∈ Timg := by
    intro k hk hk0 hna
    rcases hpart (k - 1) (by omega) with h | h
    · rw [show k - 1 + 1 = k by omega] at h; exact absurd h hna
    · exact Finset.mem_image.mpr ⟨k - 1, Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr (by omega), h⟩, by rw [show k - 1 + 1 = k by omega]⟩
  set U := Finset.univ.filter (fun w => 2 ≤ G.dist a w) with hU
  set Rs := Finset.univ.filter (fun t => t ∉ l) with hRs
  have hRU : Rs ∪ Timg ⊆ U := by
    intro u hu
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rcases Finset.mem_union.mp hu with h | h
    · have hul : u ∉ l := by simpa [hRs] using h
      apply hd2
      · intro h'; exact hul (by rw [h']; exact List.head_mem hne)
      · exact hNa' u hul
    · exact hTimg_d u h
  have hdisjRT : Disjoint Rs Timg :=
    Finset.disjoint_left.mpr (fun u h1 h2 => by simp [hRs] at h1; exact h1 (hTimg_l u h2))
  have hUcard : Rs.card + σ ≤ U.card := by
    have := Finset.card_le_card hRU
    rw [Finset.card_union_of_disjoint hdisjRT, hTi_card] at this
    exact this
  set F := Finset.univ.filter (fun w => 3 ≤ G.dist a w ∧ Odd (G.dist a w)) with hF
  set R₀ := Rs.filter (fun y => ∀ j, j < m → ¬ G.Adj y (f j)) with hR₀
  have hFsub : F ⊆ insert x₀ R₀ := by
    intro w hwF
    simp only [hF, Finset.mem_filter, Finset.mem_univ, true_and] at hwF
    obtain ⟨hw3, -⟩ := hwF
    rw [Finset.mem_insert]
    by_cases hwl : w ∈ l
    · left
      obtain ⟨k, hk, rfl⟩ := hf_ex w hwl
      have hk0 : k ≠ 0 := by rintro rfl; rw [hf0] at hw3; simp at hw3
      have hna : ¬ G.Adj a (f k) := fun h => by
        have := SimpleGraph.dist_eq_one_iff_adj.mpr h; omega
      have hwT : f k ∈ Timg := hTim k hk hk0 hna
      by_contra hwx
      have hdeg := hx0 (f k) hwx
      have hnb : G.neighborFinset (f k) ⊆ Timg.erase (f k) := by
        intro u hu
        rw [SimpleGraph.mem_neighborFinset] at hu
        have hu2 := lemma3a hconn a (f k) hw3 u hu
        rw [Finset.mem_erase]
        refine ⟨hu.ne.symm, ?_⟩
        by_cases hul : u ∈ l
        · obtain ⟨k', hk', rfl⟩ := hf_ex u hul
          have hk0' : k' ≠ 0 := by rintro rfl; rw [hf0] at hu2; simp at hu2
          apply hTim k' hk' hk0'
          intro h
          have := SimpleGraph.dist_eq_one_iff_adj.mpr h; omega
        · exfalso
          exact hna (hyN u hul k hk hu.symm).1
      have hdw := Finset.card_le_card hnb
      rw [Finset.card_erase_of_mem hwT, hTi_card, SimpleGraph.card_neighborFinset_eq_degree] at hdw
      have hpos : 0 < Timg.card := Finset.card_pos.mpr ⟨_, hwT⟩
      omega
    · right
      simp only [hR₀, hRs, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨hwl, fun j hj hadj => ?_⟩
      have := hdist2 w hwl j hj hadj
      omega
  have h3b : U.card ≤ σ + F.card := lemma3b hconn a (hH a)
  have hFc : F.card ≤ R₀.card + 1 := by
    have h1 := Finset.card_le_card hFsub
    have h2 := Finset.card_insert_le x₀ R₀
    omega
  obtain ⟨v, hv, y, hy, hvy⟩ := exists_out_edge hconn l hne hnd hlt
  have hyRs : y ∈ Rs := by simp [hRs, hy]
  have h2y := Cadre.Rdeg2 hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt y hy
  have hR3 : 3 ≤ Rs.card := by
    have hsub : (Finset.univ.filter (fun t => t ∉ l)).filter (G.Adj y) ⊆ Rs.erase y := by
      intro w hw
      rw [Finset.mem_erase]
      refine ⟨?_, (Finset.mem_filter.mp hw).1⟩
      rintro rfl
      exact G.loopless.irrefl _ (Finset.mem_filter.mp hw).2
    have := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem hyRs] at this
    omega
  set R₁ := Rs.filter (fun y => ¬ ∀ j, j < m → ¬ G.Adj y (f j)) with hR₁
  have hsplit : R₀.card + R₁.card = Rs.card := Finset.card_filter_add_card_filter_not _
  have hR1le : R₁.card ≤ 1 := by omega
  have hyR1 : y ∈ R₁ := by
    obtain ⟨j, hj, rfl⟩ := hf_ex v hv
    simp only [hR₁, Finset.mem_filter]
    exact ⟨hyRs, fun h => h j hj hvy.symm⟩
  have hR1eq : ∀ w ∈ R₁, w = y := fun w hw =>
    Finset.card_le_one.mp hR1le w hw y hyR1
  have hy0 : y ∉ R₀ := by
    intro h
    simp only [hR₀, Finset.mem_filter] at h
    simp only [hR₁, Finset.mem_filter] at hyR1
    exact hyR1.2 h.2
  have hR0pos : R₀.Nonempty := Finset.card_pos.mp (by omega)
  refine cut_closed hb y R₀ hy0 hR0pos ?_ ⟨a, ?_, ?_⟩
  · intro w hw w' hww' hw'y
    simp only [hR₀, Finset.mem_filter] at hw
    by_cases hwl : w' ∈ l
    · obtain ⟨j, hj, rfl⟩ := hf_ex w' hwl
      exact absurd hww' (hw.2 j hj)
    · by_contra hn
      have hw'R : w' ∈ R₁ := by
        simp only [hR₁, hR₀, Finset.mem_filter] at hn ⊢
        have hw'Rs : w' ∈ Rs := by simp [hRs, hwl]
        exact ⟨hw'Rs, fun h => hn ⟨hw'Rs, h⟩⟩
      exact hw'y (hR1eq w' hw'R)
  · intro h
    exact hy (by rw [← h]; exact List.head_mem hne)
  · intro h
    simp only [hR₀, hRs, Finset.mem_filter, Finset.mem_univ, true_and] at h
    exact h.1 (List.head_mem hne)
lemma b25_hx0 [Nontrivial V] [DecidableRel G.Adj] {x₀ : V}
    (hmin : ∀ v, G.degree x₀ ≤ G.degree v) : ∀ v, v ≠ x₀ → secondSmallestDegree G ≤ G.degree v := by
  intro v hv
  by_contra hlt
  push Not at hlt
  have hlen : 1 < (degreeSequence G).length := by
    simp only [degreeSequence, Multiset.length_sort, Multiset.card_map, Finset.card_val,
      Finset.card_univ]
    exact Fintype.one_lt_card
  have hsorted : (degreeSequence G).Pairwise (· ≤ ·) := by
    simp [degreeSequence]
  have hb : secondSmallestDegree G = (degreeSequence G)[1] := by
    unfold secondSmallestDegree
    rw [List.getD_eq_getElem _ _ hlen]
  have hle1 : ((degreeSequence G).filter (fun d => decide (d < secondSmallestDegree G))).length ≤ 1 := by
    rcases hds : degreeSequence G with _ | ⟨a, _ | ⟨b, tail⟩⟩
    · simp [hds] at hlen
    · simp [hds] at hlen
    · have hbb : secondSmallestDegree G = b := by
        simp [secondSmallestDegree, hds]
      rw [hds] at hsorted
      have ht : ∀ t ∈ tail, b ≤ t := by
        intro t ht
        exact (List.pairwise_cons.mp (List.pairwise_cons.mp hsorted).2).1 t ht
      rw [hbb]
      simp only [List.filter_cons]
      have : tail.filter (fun d => decide (d < b)) = [] := by
        rw [List.filter_eq_nil_iff]
        intro t htt; have := ht t htt; simp; omega
      simp only [this]
      by_cases h1 : a < b <;> simp [h1]
  have hcnt : 2 ≤ (Finset.univ.filter (fun w => G.degree w < secondSmallestDegree G)).card := by
    have h2 : ({x₀, v} : Finset V) ⊆ Finset.univ.filter (fun w => G.degree w < secondSmallestDegree G) := by
      intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rcases hw with rfl | rfl
      · exact lt_of_le_of_lt (hmin v) hlt
      · exact hlt
    have := Finset.card_le_card h2
    rwa [Finset.card_pair (Ne.symm hv)] at this
  have heq : ((degreeSequence G).filter (fun d => decide (d < secondSmallestDegree G))).length
      = (Finset.univ.filter (fun w => G.degree w < secondSmallestDegree G)).card := by
    have hm : (degreeSequence G : Multiset ℕ) = Finset.univ.val.map (fun w => G.degree w) := by
      simp [degreeSequence]
    have := congrArg (fun m : Multiset ℕ => (m.filter (fun d => d < secondSmallestDegree G)).card) hm
    simp only [Multiset.filter_map, Multiset.card_map] at this
    rw [Finset.card_def, Finset.filter_val]
    have h3 : (Multiset.filter (fun d => d < secondSmallestDegree G) (degreeSequence G : Multiset ℕ)).card
        = ((degreeSequence G).filter (fun d => decide (d < secondSmallestDegree G))).length := by
      simp [Multiset.filter_coe]
    rw [← h3]
    simpa [Function.comp_def] using this
  omega
end Aux
end OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R2_H2_R2
end
section
open Finset SimpleGraph Graph189ExteriorGap
open OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R2_H2_R2
namespace Graph189SixOrder
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]
theorem of_deletions (hc : G.Connected)
    (bound : (univ.image (distEven G)).max' (by simp)≤1+G.secondSmallestDegree)
    (six : G.secondSmallestDegree=6) (order : Fintype.card V≤19)
    (hn : 2*G.secondSmallestDegree+3 ≤ Fintype.card V) (uncut : ∀ c : V, (G.induce {v : V | v≠c}).Connected) :
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian := by
  classical
  have upper (v : V) : G.distEven v≤1+G.secondSmallestDegree :=
    (le_max' _ _ (mem_image_of_mem _ (mem_univ v))).trans bound
  have cap (v : V) : G.distEven v ≤ G.secondSmallestDegree+1 := by simpa only [Nat.add_comm] using upper v
  obtain ⟨z,hz⟩ := G.exists_minimal_degree_vertex
  have hmin (v : V) : G.degree z ≤ G.degree v := by rw [←hz]; exact G.minDegree_le_degree v
  have high := b25_hx0 (G:=G) hmin
  obtain ham | ⟨l,hne,hnd,hch,hmem,hhd,hlast,hmax,hlt⟩ := Cadre.exists_cadre hc upper hn hmin
  · exact ham
  exfalso
  have minLength := Cadre.m_ge hc uncut upper hmin high (h11 hc upper hn) hne hnd hch hmem hhd hlast hmax hlt
  let p := Walk.ofSupport l hne hch
  have supp : p.support=l := Walk.support_ofSupport hne hch
  have hp : p.IsPath := Walk.IsPath.mk' (by rwa [supp])
  have contains : z∈p.support := by rwa [supp]
  obtain ⟨i,hi,atZ⟩ := List.mem_iff_getElem.mp contains
  let t : Fin p.support.length := ⟨i,hi⟩
  have eq : p.support[t.val]=z := atZ
  have longest {a b} (q : G.Walk a b) (hq : q.IsPath) (seen : z∈q.support) : q.length ≤ p.length := by
    have h := hmax q.support hq.support_nodup q.isChain_adj_support seen
    rw [←supp,q.length_support,p.length_support] at h
    omega
  have mx : ∀ {a b}, ∀ q : G.Walk a b, q.IsPath → p.support[t.val]∈q.support → q.length ≤ p.length :=
    fun q hq h => longest q hq (eq ▸ h)
  let E := (p.support.toFinsetᶜ : Finset V)
  have total := card_add_card_compl p.support.toFinset
  rw [List.toFinset_card_of_nodup hp.support_nodup] at total
  change p.support.length+E.card=Fintype.card V at total
  rw [←supp] at minLength hlt
  have nonempty : E.Nonempty := card_pos.mp (by omega)
  obtain ⟨size,routes,M,sz,links⟩ := Graph189SixExterior.data p hp t mx six order cap
    (fun miss => high _ (fun e => miss (by simpa only [e] using contains))) nonempty (by change E.card≤5; omega)
  change E.card=5 at size
  have common {i j} (r : G.Walk i j) (hr : r.IsPath) (retained : p.support[t.val]∈r.support)
      (same : r.length=p.length) (w : V) (hw : w∈r.support) (x : V) (hx : x∉r.support)
      (y : V) (hy : y∉r.support) (wx : G.Adj w x) : G.Adj w y := by
    have count := card_add_card_compl r.support.toFinset
    rw [List.toFinset_card_of_nodup hr.support_nodup] at count
    have len : r.support.length=p.support.length := by rw [r.length_support,same,←p.length_support]
    have keep : z∈r.support := eq ▸ retained
    obtain ⟨j,hj,atZ⟩ := List.mem_iff_getElem.mp keep
    let T : Fin r.support.length := ⟨j,hj⟩
    have mx' : ∀ {u v}, ∀ q : G.Walk u v, q.IsPath → r.support[T.val]∈q.support → q.length ≤ r.length := by
      intro _ _ q hq ht
      rw [same]
      apply longest q hq
      simpa only [T,atZ] using ht
    obtain ⟨_,_,_,_,both⟩ := Graph189SixExterior.data r hr T mx' six order cap
      (fun miss => high _ (fun e => miss (by simpa only [e] using keep))) (card_pos.mp (by omega)) (by omega)
    obtain ⟨l,hl,ev⟩ := List.mem_iff_getElem.mp hw
    rw [←ev] at wx ⊢
    exact (both y (by simpa using hy) ⟨l,hl⟩).mpr ((both x (by simpa using hx) ⟨l,hl⟩).mp wx)
  exact two_mark_exchange p hp t mx E (by omega) (fun {v} h => by simpa [E] using h)
    routes M sz links common (by omega) (by intro v _; have := cap v; omega)
end Graph189SixOrder
end
section
open Finset SimpleGraph Graph189ExteriorGap
namespace Graph189FivePortOrder
variable {W : Type*} [Fintype W] [DecidableEq W] (H : SimpleGraph W) [DecidableRel H.Adj]
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {a b : V}
omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
private theorem mapped {W : Finset V} (p : G.Walk a b) (outside : ∀ z∈W, z∉p.support)
    {u v : W} (q : (G.induce (W : Set V)).Walk u v) (hq : q.IsPath) :
    ∃ r : G.Walk u.val v.val, r.IsPath ∧ List.Disjoint r.support p.support ∧ r.support.length=q.support.length := by
  let inc := (Embedding.induce (G:=G) (W : Set V)).toHom
  have ds : List.Disjoint (q.map inc).support p.support := by
    rw [Walk.support_map,List.disjoint_left]
    intro z hz
    obtain ⟨t,_,rfl⟩ := List.mem_map.mp hz
    exact outside t.val t.property
  have len : (q.map inc).support.length=q.support.length := by rw [Walk.support_map,List.length_map]
  exact ⟨q.map inc,hq.map Subtype.val_injective,ds,len⟩
omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem order (p : G.Walk a b) (hp : p.IsPath)
    (longest : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → r.length ≤ p.length)
    (W : Finset V) (outside : ∀ z∈W, z∉p.support)
    {i j : Fin p.support.length} {u v : W}
    (ij : i < j) (left : G.Adj p.support[i.val] u.val) (right : G.Adj p.support[j.val] v.val)
    (l s d : ℕ)
    (leftTail : ∃ w, ∃ q : (G.induce (W : Set V)).Walk u w, q.IsPath ∧ l ≤ q.support.length)
    (rightTail : ∃ w, ∃ q : (G.induce (W : Set V)).Walk v w, q.IsPath ∧ s ≤ q.support.length)
    (inner : ∃ q : (G.induce (W : Set V)).Walk u v, q.IsPath ∧ d ≤ q.support.length) :
    l+s+d+2 ≤ p.support.length := by
  obtain ⟨_,q,hq,l⟩ := leftTail
  obtain ⟨r,hr,dis,len⟩ := mapped p outside q hq
  have rc : List.Disjoint r.reverse.support p.support := by simpa [Walk.support_reverse] using dis
  have f := prefix_of_detour p hp longest i r.reverse hr.reverse rc left.symm
  rw [Walk.support_reverse,List.length_reverse,len] at f
  obtain ⟨_,q',hq',l'⟩ := rightTail
  obtain ⟨r',hr',dis',len'⟩ := mapped p outside q' hq'
  have g := suffix_of_detour p hp longest j r' hr' dis' right
  rw [len'] at g
  obtain ⟨q'',hq'',l''⟩ := inner
  obtain ⟨r'',hr'',dis'',len''⟩ := mapped p outside q'' hq''
  have h := interval_of_detour p hp longest i j ij r'' hr'' dis'' left right.symm
  rw [len''] at h
  omega
end Graph189FivePortOrder
end
section
open SimpleGraph Finset Graph189ExteriorGap Graph189ExteriorDegreeCycle
namespace Graph189SixRotation
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]
theorem no_high {x y : V} (p : G.Walk x y) (hp : p.IsPath)
    (mx : ∀ {u v}, ∀ q : G.Walk u v, q.IsPath → q.length ≤ p.length)
    (conn : 2 ≤ G.vertexConnectivity) (order : Fintype.card V≤20)
    (six : G.secondSmallestDegree=6) (minimum : ∀ v, 3 ≤ G.degree v)
    (quota : ∀ v, (univ.filter (fun w => G.dist v w=2)).card≤6)
    {highVertex : V} (omitted : highVertex∉p.support) (large : 6 ≤ G.degree highVertex) : False := by
  classical
  let E := p.support.toFinsetᶜ
  let J := G.induce (E : Set V)
  let f : E ↪ V := ⟨Subtype.val,Subtype.val_injective⟩
  have off (a : E) : a.val∉p.support := fun hit => (mem_compl.mp a.property) (List.mem_toFinset.mpr hit)
  have unique {a b : E} (la : G.degree a.val<6) (lb : G.degree b.val<6) : a=b := by
    apply Subtype.ext
    by_contra ne
    have pair := OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1.degree_pair (G:=G) _ _ ne
    omega
  obtain ⟨degree,B,R,rank,sub,width,trapped⟩ := Graph189OrdinaryRotationWindow.of_high p hp mx conn
    (d:=3) (L:=4) six (by decide) (by decide) (by decide) (by omega) minimum quota omitted large
  let H := fun a : E => 6 ≤ G.degree a.val
  let D := B.filter (fun a => H a ∧ J.neighborFinset a⊆B)
  have good {a : E} (ar : a∈R) (hi : H a) : a∈D := mem_filter.mpr ⟨sub ar,hi,trapped a ar⟩
  have few : (R\D).card≤1 := by
    apply card_le_one.mpr
    intro a ha b hb
    apply unique
    · by_contra! hi
      exact (mem_sdiff.mp ha).2 (good (mem_sdiff.mp ha).1 hi)
    · by_contra! hi
      exact (mem_sdiff.mp hb).2 (good (mem_sdiff.mp hb).1 hi)
  have split := card_sdiff_add_card_inter R D
  have common : (R∩D).card ≤ D.card := card_le_card inter_subset_right
  have two : 2 ≤ D.card := by omega
  have full {a : E} (ha : a∈D) : J.neighborFinset a=B.erase a ∧ B.card=4 := by
    obtain ⟨ab,hi,trap⟩ := mem_filter.mp ha
    have deg : 3 ≤ J.degree a := degree a hi
    have inc : J.neighborFinset a⊆B.erase a := by
      intro v hv
      exact mem_erase.mpr ⟨((J.mem_neighborFinset _ _).mp hv).ne.symm,trap hv⟩
    have h := card_le_card inc
    rw [J.card_neighborFinset_eq_degree,card_erase_of_mem ab] at h
    exact ⟨eq_of_subset_of_card_le inc (by
      rw [J.card_neighborFinset_eq_degree,card_erase_of_mem ab]
      omega),by omega⟩
  obtain ⟨a,ha,b,hb,ab⟩ := one_lt_card.mp (show 1 < D.card by omega)
  have size := (full ha).2
  have edge {u v : E} (hu : u∈D) (hv : v∈B) (diff : u≠v) : J.Adj u v := by
    apply (J.mem_neighborFinset _ _).mp
    rw [(full hu).1]
    exact mem_erase.mpr ⟨diff.symm,hv⟩
  by_cases three : 3 ≤ D.card
  · have ord := Graph189OrdinaryRotationWindow.full_ports p hp mx (B.map f) (D.map f)
      (by rw [card_map,size]) (by rw [card_map,size]; decide) (by rwa [card_map])
      (map_subset_map.mpr (filter_subset _ _))
      (fun v hv => by obtain ⟨v,_,rfl⟩ := mem_map.mp hv; exact off v)
      (by
        intro first ha second hb ne
        obtain ⟨u,hu,rfl⟩ := mem_map.mp ha
        obtain ⟨v,hv,rfl⟩ := mem_map.mp hb
        exact edge hu hv (fun e => ne (congrArg f e)))
      (by
        intro first ha v e no
        obtain ⟨u,hu,rfl⟩ := mem_map.mp ha
        by_contra miss
        let j : E := ⟨v,mem_compl.mpr fun h => miss (List.mem_toFinset.mp h)⟩
        have step : J.Adj u j := e
        exact no (mem_map.mpr ⟨j,(mem_filter.mp hu).2.2 ((J.mem_neighborFinset _ _).mpr step),rfl⟩))
      (by
        intro first ha
        obtain ⟨u,hu,rfl⟩ := mem_map.mp ha
        rw [card_map,size]
        exact (mem_filter.mp hu).2.1)
    rw [card_map,size] at ord
    omega
  obtain ⟨z,zr,low⟩ : ∃ z∈R, ¬H z := by
    by_contra! all
    have inc : R⊆D := fun u hu => good hu (all u hu)
    have := card_le_card inc
    omega
  have wc : ∃ c∈B, c∉R := by
    by_contra! inc
    have same : B=R := Subset.antisymm inc sub
    have bad : (B\D).card≤1 := by simpa only [same] using few
    have h := card_sdiff_add_card_eq_card (show D⊆B from filter_subset _ _)
    omega
  obtain ⟨c,cb,cr⟩ := wc
  have rest : B.erase c=R := by
    apply (eq_of_subset_of_card_le (show R⊆B.erase c from fun v vr =>
      mem_erase.mpr ⟨fun eq => cr (eq ▸ vr),sub vr⟩) ?_).symm
    rw [card_erase_of_mem cb,size]
    omega
  have others {u : E} (ub : u∈B) (diff : u≠c) : u∈R := by
    rw [←rest]
    exact mem_erase.mpr ⟨diff,ub⟩
  have cz : c≠z := fun h => cr (h ▸ zr)
  have hi_c : H c := by
    by_contra lo
    exact cz (unique (Nat.lt_of_not_ge lo) (Nat.lt_of_not_ge low))
  have cd : c∉D := by
    intro hc
    have inc : insert c (R∩D)⊆D := insert_subset hc inter_subset_right
    have h := card_le_card inc
    rw [card_insert_of_notMem (fun e => cr (mem_inter.mp e).1)] at h
    omega
  obtain ⟨w,neighbor,wb⟩ : ∃ w∈J.neighborFinset c,w∉B := by
    by_contra! confined
    exact cd (mem_filter.mpr ⟨cb,hi_c,confined⟩)
  have cw := (J.mem_neighborFinset _ _).mp neighbor
  have hi_w : H w := by
    by_contra lo
    have wz := unique (Nat.lt_of_not_ge lo) (Nat.lt_of_not_ge low)
    exact wb (wz ▸ sub zr)
  have outside : insert w ((J.neighborFinset w).erase c)⊆Bᶜ := by
    intro v hv
    apply mem_compl.mpr
    rcases mem_insert.mp hv with rfl|h
    · exact wb
    intro vb
    obtain ⟨ne,nv⟩ := mem_erase.mp h
    have vr := others vb ne
    exact wb (trapped v vr ((J.mem_neighborFinset _ _).mpr ((J.mem_neighborFinset _ _).mp nv).symm))
  have lower := card_le_card outside
  have self : w∉(J.neighborFinset w).erase c := fun e => ((J.mem_neighborFinset _ _).mp (mem_erase.mp e).2).ne rfl
  rw [card_insert_of_notMem self,card_erase_of_mem ((J.mem_neighborFinset _ _).mpr cw.symm),
    J.card_neighborFinset_eq_degree] at lower
  have grow : 3 ≤ J.degree w := degree w hi_w
  have totalB := card_add_card_compl B
  have ambient := card_add_card_compl p.support.toFinset
  rw [List.toFinset_card_of_nodup hp.support_nodup] at ambient
  change p.support.length+E.card=Fintype.card V at ambient
  change B.card+Bᶜ.card=Fintype.card E at totalB
  rw [Fintype.card_coe] at totalB
  have short : p.support.length≤13 := by omega
  have mark {u : E} (hu : u∈D) : 3≤(contactPositions p u.val).card := by
    have de := (full hu).1
    have int : J.degree u=3 := by
      rw [←J.card_neighborFinset_eq_degree,de,card_erase_of_mem (mem_filter.mp hu).1,size]
    have eq : J.degree u=(G.neighborFinset u.val\p.support.toFinset).card := by
      rw [degree_induce_filter]
      congr 1
      ext v
      simp [E]
    rw [contact_card_neighbors p hp]
    have cnt := card_sdiff_add_card_inter (G.neighborFinset u.val) p.support.toFinset
    have hi := (mem_filter.mp hu).2.1
    change 6 ≤ G.degree u.val at hi
    rw [G.card_neighborFinset_eq_degree] at cnt
    omega
  obtain ⟨i,mi⟩ := card_pos.mp (show 0<(contactPositions p a.val).card by have := mark ha; omega)
  obtain ⟨j,mj,ji⟩ := exists_mem_ne (show 1<(contactPositions p b.val).card by have := mark hb; omega) i
  have ti := (mem_contactPositions p a.val i).mp mi
  have tj := (mem_contactPositions p b.val j).mp mj
  let I : Fin p.support.length := ⟨i,ti.1⟩
  let K : Fin p.support.length := ⟨j,tj.1⟩
  have ia : G.Adj p.support[I.val] a.val := by simpa only [I,get_at] using ti.2
  have jb : G.Adj p.support[K.val] b.val := by simpa only [K,get_at] using tj.2
  have distinct {u : E} (hu : u∈D) : u≠z ∧ u≠c ∧ u≠w := by
    exact ⟨fun e => low (e ▸ (mem_filter.mp hu).2.1),fun e => cd (e ▸ hu),
      fun e => wb (e ▸ (mem_filter.mp hu).1)⟩
  have az := distinct ha
  have bz := distinct hb
  have zw : z≠w := fun e => wb (e ▸ sub zr)
  have eaz := edge ha (sub zr) az.1
  have ebz := edge hb (sub zr) bz.1
  have eac := edge ha cb az.2.1
  have ebc := edge hb cb bz.2.1
  let ta := Walk.cons eaz (Walk.cons ebz.symm (Walk.cons ebc (Walk.cons cw .nil)))
  let tb := Walk.cons ebz (Walk.cons eaz.symm (Walk.cons eac (Walk.cons cw .nil)))
  let middle := Walk.cons eaz (Walk.cons ebz.symm .nil)
  have pa : ta.IsPath := Walk.IsPath.mk' (by
    simp [ta,az.1,ab,az.2.1,az.2.2,bz.1.symm,cz.symm,zw,bz.2.1,bz.2.2,cw.ne])
  have pb : tb.IsPath := Walk.IsPath.mk' (by
    simp [tb,bz.1,ab.symm,bz.2.1,bz.2.2,az.1.symm,cz.symm,zw,az.2.1,az.2.2,cw.ne])
  have pm : middle.IsPath := Walk.IsPath.mk' (by simp [middle,az.1,ab,bz.1.symm])
  have out (v : V) (hv : v∈E) : v∉p.support := off ⟨v,hv⟩
  have diff : I≠K := fun e => ji (congrArg Fin.val e).symm
  rcases lt_or_gt_of_ne diff with forward|backward
  · have n := Graph189FivePortOrder.order p hp mx E out forward ia jb 5 5 3
      ⟨w,ta,pa,by simp [ta]⟩ ⟨w,tb,pb,by simp [tb]⟩ ⟨middle,pm,by simp [middle]⟩
    omega
  · have n := Graph189FivePortOrder.order p hp mx E out backward jb ia 5 5 3
      ⟨w,tb,pb,by simp [tb]⟩ ⟨w,ta,pa,by simp [ta]⟩ ⟨middle.reverse,pm.reverse,by simp [middle]⟩
    omega
theorem omitted_low {x y : V} (p : G.Walk x y) (hp : p.IsPath)
    (mx : ∀ {u v}, ∀ q : G.Walk u v, q.IsPath → q.length ≤ p.length)
    (conn : 2 ≤ G.vertexConnectivity) (order : Fintype.card V≤20)
    (six : G.secondSmallestDegree=6) (minimum : 3 ≤ G.minDegree)
    (cap : ∀ v, G.distEven v ≤ G.secondSmallestDegree+1) {v : V} (outside : v∉p.support) : G.degree v<6 := by
  classical
  by_contra! hi
  apply no_high p hp mx conn order six (fun x => minimum.trans (G.minDegree_le_degree x)) _ outside hi
  intro a
  let D := univ.filter (fun u => G.dist a u=2)
  have sub : insert a D⊆univ.filter (fun u => Even (G.dist a u)) := by
    intro u hu
    rcases mem_insert.mp hu with rfl|h
    · simp
    · exact mem_filter.mpr ⟨mem_univ _,by simp [(mem_filter.mp h).2]⟩
  have miss : a∉D := by simp [D]
  have h := card_le_card sub
  rw [card_insert_of_notMem miss] at h
  change D.card+1 ≤ G.distEven a at h
  change D.card≤6
  have upper := cap a
  omega
end Graph189SixRotation
end
section
open Finset SimpleGraph
namespace Graph189ProtectedExchange
open Graph189ExteriorGap
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {a b : V}
private theorem overlap (A : Finset ℕ) (lo hi : ℕ)
    (unmarked : ∀ i ∈ Ico lo hi, i ∉ A)
    (internal : ∀ i ∈ A, 0 < i) :
    ((crossIndices A A) ∩ Ico lo hi).card ≤ 2 := by
  have subset : (crossIndices A A) ∩ Ico lo hi ⊆ {lo,hi-1} := by
    intro v hv
    obtain ⟨w,hv⟩ := mem_inter.mp hv
    obtain ⟨vlow,vhigh⟩ := mem_Ico.mp hv
    have shifts : v ∈ A.image (fun i => i-1) ∪ A.image (fun i => i+1) := by
      rcases mem_union.mp w with h | h
      · simpa only [inter_self] using h
      · exact False.elim ((mem_sdiff.mp h).2 (mem_sdiff.mp h).1)
    apply mem_insert.mpr
    rcases mem_union.mp shifts with left | right
    · obtain ⟨i,hiA,eq⟩ := mem_image.mp left
      have := internal i hiA
      have notInside : ¬(lo ≤ i ∧ i < hi) := fun h => unmarked i (mem_Ico.mpr h) hiA
      exact Or.inr (mem_singleton.mpr (by omega))
    · obtain ⟨i,hiA,eq⟩ := mem_image.mp right
      have notInside : ¬(lo ≤ i ∧ i < hi) := fun h => unmarked i (mem_Ico.mpr h) hiA
      exact Or.inl (by omega)
  exact (card_le_card subset).trans card_le_two
theorem terminal_contradiction (p : G.Walk a b) (hp : p.IsPath)
    (t : Fin p.support.length)
    (longest : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → p.support[t.val] ∈ r.support → r.length ≤ p.length)
    {x y : V} (outx : x ∉ p.support) (outy : y ∉ p.support) (edge : G.Adj x y)
    (shared : contactPositions p y = contactPositions p x)
    {lo hi k : ℕ} (bound : hi ≤ p.support.length)
    (unmarked : ∀ i ∈ Ico lo hi, i ∉ contactPositions p x)
    (via : ∀ i ∈ Ico lo hi, ∃ w, G.Adj x w ∧ G.Adj (p.getVert i) w)
    (tight : hi-lo+(contactPositions p x).card = k+1)
    (three : 3 ≤ (contactPositions p x).card)
    (cap : G.distEven x ≤ k+1) : False := by
  classical
  let A := contactPositions p x
  let W := crossIndices A A
  let J := Ico lo hi
  obtain ⟨count,witness⟩ := protected_cross_indices p hp t longest outx outy edge
  rw [shared] at count witness
  change A.card+A.card ≤ W.card+1 at count
  have internal (i : ℕ) (h : i ∈ A) : 0 < i := by
    obtain ⟨hi,adj⟩ := (mem_contactPositions p x i).mp h
    exact (protected_contact_internal p hp t longest outx ⟨i,hi⟩ (by simpa [get_at] using adj)).1
  have lose : (W ∩ J).card ≤ 2 := overlap A lo hi unmarked internal
  have good (i : ℕ) (mem : i ∈ W ∪ J) : i < p.support.length ∧ G.dist x (p.getVert i)=2 := by
    rcases mem_union.mp mem with h|h
    · exact witness i h
    · obtain ⟨_,lt⟩ := mem_Ico.mp h
      have ri := lt.trans_le bound
      obtain ⟨w,hx,hw⟩ := via i h
      have different : x ≠ p.getVert i := fun e => outx (e ▸ p.getVert_mem_support i)
      have missing : ¬G.Adj x (p.getVert i) := fun adj =>
        unmarked i h ((mem_contactPositions p x i).mpr ⟨ri,adj.symm⟩)
      exact ⟨ri,two_step_metric different missing hx hw⟩
  let T := (W ∪ J).image p.getVert
  have inj : Set.InjOn p.getVert ((W ∪ J : Finset ℕ) : Set ℕ) := by
    intro i hi j hj eq
    have := (good _ hi).1
    have := (good _ hj).1
    have := p.length_support
    exact hp.getVert_injOn (by change i ≤ p.length; omega) (by change j ≤ p.length; omega) eq
  have absent : x ∉ T := by
    intro h
    obtain ⟨i,_,eq⟩ := mem_image.mp h
    exact outx (eq ▸ p.getVert_mem_support i)
  have sub : insert x T ⊆ univ.filter (fun v => Even (G.dist x v)) := by
    intro v h
    rcases mem_insert.mp h with rfl|mem
    · simp
    · obtain ⟨i,hi,rfl⟩ := mem_image.mp mem
      exact mem_filter.mpr ⟨mem_univ _,by rw [(good _ hi).2]; decide⟩
  have total := card_le_card sub
  change (insert x T).card ≤ G.distEven x at total
  rw [card_insert_of_notMem absent,show T.card=(W∪J).card from card_image_of_injOn inj] at total
  have union := card_union_add_card_inter W J
  have size : J.card=hi-lo := Nat.card_Ico _ _
  change hi-lo+A.card=k+1 at tight
  change 3 ≤ A.card at three
  omega
theorem contradiction_of_uniform_marks (p : G.Walk a b) (hp : p.IsPath)
    (t : Fin p.support.length)
    (longest : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → p.support[t.val] ∈ r.support → r.length ≤ p.length)
    {x y : V} (outx : x ∉ p.support) (outy : y ∉ p.support) (edge : G.Adj x y)
    (marks : Finset (Fin p.support.length))
    (mx : ∀ i : Fin p.support.length, G.Adj p.support[i.val] x ↔ i ∈ marks)
    (my : ∀ i : Fin p.support.length, G.Adj p.support[i.val] y ↔ i ∈ marks)
    {lo hi k : ℕ} (bound : hi ≤ p.support.length)
    (unmarked : ∀ i : Fin p.support.length, lo ≤ i.val → i.val < hi → i ∉ marks)
    (via : ∀ i : Fin p.support.length, lo ≤ i.val → i.val < hi →
      ∃ w, G.Adj x w ∧ G.Adj p.support[i.val] w)
    (tight : hi-lo+marks.card = k+1) (three : 3 ≤ marks.card)
    (cap : G.distEven x ≤ k+1) : False := by
  classical
  have eq {v : V} (mark : ∀ i : Fin p.support.length, G.Adj p.support[i.val] v ↔ i ∈ marks) :
      contactPositions p v=marks.image Fin.val := by
    ext i
    constructor
    · intro h
      obtain ⟨ri,edge⟩ := (mem_contactPositions p v i).mp h
      exact mem_image.mpr ⟨⟨i,ri⟩,(mark ⟨i,ri⟩).mp (by simpa [get_at] using edge),rfl⟩
    · intro h
      obtain ⟨j,hj,rfl⟩ := mem_image.mp h
      exact (mem_contactPositions p v j.val).mpr ⟨j.isLt,by simpa [get_at] using (mark j).mpr hj⟩
  have size : (contactPositions p x).card=marks.card := by
    rw [eq mx,card_image_of_injective _ Fin.val_injective]
  apply terminal_contradiction (lo:=lo) (hi:=hi) (k:=k) p hp t longest outx outy edge ((eq my).trans (eq mx).symm) bound _ _
    (by simpa [size] using tight) (by simpa [size] using three) cap
  · intro i hiA h
    obtain ⟨ri,edge⟩ := (mem_contactPositions p x i).mp h
    obtain ⟨left,right⟩ := mem_Ico.mp hiA
    exact (unmarked ⟨i,ri⟩ left right) ((mx ⟨i,ri⟩).mp (by simpa [get_at] using edge))
  · intro i hiA
    obtain ⟨left,right⟩ := mem_Ico.mp hiA
    let j : Fin p.support.length := ⟨i,right.trans_le bound⟩
    obtain ⟨w,hx,edge⟩ := via j left right
    exact ⟨w,hx,by simpa only [get_at] using edge⟩
end Graph189ProtectedExchange
end
section
open Finset SimpleGraph Graph189ExteriorGap
namespace Graph189SaturatedExterior
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]
private theorem data {a b : V} (p : G.Walk a b) (hp : p.IsPath) (t : Fin p.support.length)
    (mx : ∀ {i j}, ∀ q : G.Walk i j, q.IsPath → p.support[t.val]∈q.support → q.length ≤ p.length)
    (high : ∀ {v : V}, v∉p.support → G.secondSmallestDegree ≤ G.degree v)
    (cap : ∀ v, G.distEven v ≤ G.secondSmallestDegree+1)
    (m s : ℕ) (size : (p.support.toFinsetᶜ : Finset V).card=m)
    (sum : m+s=G.secondSmallestDegree+1) (three : 3 ≤ s) (less : s < m)
    (order : Fintype.card V<(s+2)*m+(s+1)) :
    let E := (p.support.toFinsetᶜ : Finset V)
    (∀ x y : E, x≠y → ∃ q : (G.induce (E : Set V)).Walk x y, q.IsHamiltonian) ∧
    ∃ M : Finset (Fin p.support.length), M.card=s ∧
      (∀ w∈E, ∀ i : Fin p.support.length, G.Adj p.support[i.val] w ↔ i∈M) ∧ G.IsClique (E : Set V) := by
  classical
  let E := (p.support.toFinsetᶜ : Finset V)
  let H := G.induce (E : Set V)
  change E.card=m at size
  have out (w : V) (hw : w∈E) : w∉p.support := by simpa [E] using hw
  have routes (x y : E) (ne : x≠y) : ∃ q : H.Walk x y, q.IsHamiltonian := by
    apply Graph189TerminalLeafClosure.prescribed_of_supergraph (G:=H) le_top _
      (Graph189TerminalLeafClosure.complete_prescribed x y ne)
    intro i j _ _
    have deg (w : E) : G.secondSmallestDegree/2 ≤ H.degree w :=
      Graph189AllHighExterior.minimum p hp t mx (by omega) high cap w
    have := deg i
    have := deg j
    change Fintype.card E+1 ≤ H.degree i+H.degree j
    rw [Fintype.card_coe,size]
    omega
  obtain ⟨M,sz,links⟩ := uniform_contacts_of_order p hp t mx E out (by omega) routes s
    (by omega) (by rwa [size]) (by
      intro w hw
      have reach := Graph189DenseExteriorOrder.neighbors_on_path p E
        (fun _ _ x _ nx => by simpa [E] using nx) hw
      have := high (out w hw)
      omega)
  exact ⟨routes,M,sz,links,exterior_clique_of_common_contacts p M G.secondSmallestDegree
    (by change E.card+M.card ≤ _; omega) (fun w hw => high (out w hw))
    (fun w hw i => (links w hw i).mp)⟩
theorem exclude {a b : V} (p : G.Walk a b) (path : p.IsPath) (t : Fin p.support.length)
    (mx : ∀ {i j}, ∀ q : G.Walk i j, q.IsPath → p.support[t.val]∈q.support → q.length ≤ p.length)
    (high : ∀ v, v≠p.support[t.val] → G.secondSmallestDegree ≤ G.degree v)
    (cap : ∀ v, G.distEven v ≤ G.secondSmallestDegree+1)
    (m s : ℕ) (size : (p.support.toFinsetᶜ : Finset V).card=m)
    (sum : m+s=G.secondSmallestDegree+1) (three : 3 ≤ s) (less : s < m)
    (order : Fintype.card V<(s+2)*m+(s+1)) (room : p.support.length ≤ s*m+2*s) : False := by
  classical
  let E := (p.support.toFinsetᶜ : Finset V)
  let k := G.secondSmallestDegree
  change E.card=m at size
  have rootmem : p.support[t.val]∈p.support := List.getElem_mem _
  have outside : ∀ {w : V}, w∉p.support → G.secondSmallestDegree ≤ G.degree w :=
    fun {w} h => high w (fun eq => h (by simpa only [eq] using rootmem))
  obtain ⟨paths,M,sz,contacts,clique⟩ := data p path t mx outside cap m s size sum three less order
  have uniform {i j} (r : G.Walk i j) (hr : r.IsPath) (retain : p.support[t.val]∈r.support)
      (same : r.length=p.length) (w : V) (hw : w∈r.support) (u : V) (hu : u∉r.support)
      (v : V) (hv : v∉r.support) (wu : G.Adj w u) : G.Adj w v := by
    obtain ⟨l,hl,atZ⟩ := List.mem_iff_getElem.mp retain
    let T : Fin r.support.length := ⟨l,hl⟩
    have eq : r.support[T.val]=p.support[t.val] := atZ
    have mx' : ∀ {i j}, ∀ q : G.Walk i j, q.IsPath → r.support[T.val]∈q.support → q.length ≤ r.length :=
      fun q hq seen => by rw [same]; exact mx q hq (eq ▸ seen)
    have total := card_add_card_compl r.support.toFinset
    have orig := card_add_card_compl p.support.toFinset
    rw [List.toFinset_card_of_nodup hr.support_nodup,r.length_support,same,←p.length_support] at total
    rw [List.toFinset_card_of_nodup path.support_nodup] at orig
    change p.support.length+E.card=Fintype.card V at orig
    obtain ⟨_,_,_,links,_⟩ := data r hr T mx'
      (fun {v} h => high v (fun e => h (by simpa only [e] using retain))) cap m s (by omega) sum three less order
    obtain ⟨j,hj,atW⟩ := List.mem_iff_getElem.mp hw
    rw [←atW] at wu ⊢
    exact (links v (by simpa using hv) ⟨j,hj⟩).mpr ((links u (by simpa using hu) ⟨j,hj⟩).mp wu)
  obtain ⟨x,hx,y,hy,ne⟩ := one_lt_card.mp (show 1 < E.card by omega)
  let X : E := ⟨x,hx⟩
  let Y : E := ⟨y,hy⟩
  have out {v : V} (h : v∈E) : v∉p.support := by simpa [E] using h
  obtain ⟨w,hw⟩ := paths X Y (fun h => ne (congrArg Subtype.val h))
  let inc := (Embedding.induce (G:=G) (E : Set V)).toHom
  let q := w.map inc
  have hq : q.IsPath := hw.isPath.map Subtype.val_injective
  have dis : List.Disjoint q.support p.support := by
    apply List.disjoint_left.mpr
    intro v hv
    rw [show q.support=w.support.map inc from Walk.support_map _ _] at hv
    obtain ⟨u,_,rfl⟩ := List.mem_map.mp hv
    exact out u.property
  have qlen : q.support.length=m := by
    change (w.map inc).support.length=m
    rw [Walk.support_map,List.length_map,hw.length_support]
    change Fintype.card E=m
    exact (Fintype.card_coe E).trans size
  have touch (i : Fin p.support.length) (hi : i∈M) : G.Adj p.support[i.val] x ∧ G.Adj p.support[i.val] y :=
    ⟨(contacts x hx i).mpr hi,(contacts y hy i).mpr hi⟩
  obtain ⟨j,hj⟩ : ∃ j, M.card=j+1 := ⟨s-1,by omega⟩
  let A := M.orderEmbOfFin hj
  have adj (i : Fin (j+1)) := touch (A i) (M.orderEmbOfFin_mem hj i)
  have close : p.support.length≤(j+1)*m+2*(j+1) := by rwa [←hj,sz]
  obtain ⟨lo,hi,nonempty,le,size,safe,left,right,one,unmarked⟩ :=
    locate_tight_protected_gap t M hj (by omega : 0 < m)
      (protected_contact_internal p path t mx (out hx) _ (adj 0).1).1
      (protected_contact_internal p path t mx (out hx) _ (adj (Fin.last j)).1).2
      (fun i => protected_contact_spacing p path t mx (out hx) _ _ (A.strictMono i.castSucc_lt_succ)
        (adj i.castSucc).1 (adj i.succ).1)
      (fun h => qlen ▸ protected_prefix_of_detour p path t mx _ h q hq dis (adj 0).2.symm)
      (fun h => qlen ▸ protected_suffix_of_detour p path t mx _ h q hq dis (adj _).1)
      (fun i h => qlen ▸ protected_interval_of_detour p path t mx _ _ (A.strictMono i.castSucc_lt_succ)
        h q hq dis (adj i.castSucc).1 (adj i.succ).2.symm) close
  have via := interval_exchange_witnesses p path t M q hq dis touch uniform nonempty le
    (size.trans qlen.symm) safe left right one
  apply Graph189ProtectedExchange.contradiction_of_uniform_marks (lo:=lo) (hi:=hi) (k:=k) p path t mx (out hx) (out hy)
    (clique hx hy ne) M (contacts _ hx) (contacts _ hy) le _ _
    (by rw [size,sz]; exact sum) (by simpa only [sz] using three) (cap x)
  · intro i lo' hi' mem
    exact (unmarked i mem).elim (Nat.not_lt.mpr lo') (Nat.not_le.mpr hi')
  · intro i lo' hi'
    obtain ⟨c,xc,ic⟩ := via i.val (mem_Ico.mpr ⟨lo',hi'⟩)
    exact ⟨c,xc,(get_at p i.isLt).symm ▸ ic⟩
end Graph189SaturatedExterior
end
section
open Finset SimpleGraph Graph189ExteriorGap
namespace Graph189SixProtected
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]
theorem traceable (z : V) (three : 3 ≤ G.degree z) (six : G.secondSmallestDegree=6)
    (high : ∀ w, w≠z → G.secondSmallestDegree ≤ G.degree w)
    (cap : ∀ w, G.distEven w ≤ G.secondSmallestDegree+1) (order : Fintype.card V≤22)
    {a b : {w : V | w≠z}} (P : (G.induce {w : V | w≠z}).Walk a b) (hP : P.IsHamiltonian) :
    ∃ u v : V, ∃ p : G.Walk u v, p.IsHamiltonian := by
  classical
  obtain ⟨u,v,p,hp,t,atZ,longest⟩ := exists_longest_through G z
  let E := (p.support.toFinsetᶜ : Finset V)
  by_cases present : E.Nonempty
  swap
  · refine ⟨u,v,p,hp.isHamiltonian_of_mem (fun w => ?_)⟩
    by_contra absent
    exact present ⟨w,by simpa [E] using absent⟩
  exfalso
  have mx : ∀ {i j}, ∀ r : G.Walk i j, r.IsPath → p.support[t.val]∈r.support → r.length ≤ p.length :=
    fun r hr h => longest r hr (atZ ▸ h)
  have exc (w : V) (diff : w≠p.support[t.val]) : G.secondSmallestDegree ≤ G.degree w :=
    high w (by simpa only [atZ] using diff)
  obtain ⟨x,hx⟩ := present
  let X : E := ⟨x,hx⟩
  let H := G.induce (E : Set V)
  have kernel := Graph189AllHighExterior.minimum p hp t mx (by omega)
    (fun {w} off => exc w (fun eq => off (by rw [eq]; exact List.getElem_mem _))) cap X
  change G.secondSmallestDegree/2 ≤ H.degree X at kernel
  have vertices := H.degree_lt_card_verts X
  change H.degree X < Fintype.card E at vertices
  rw [Fintype.card_coe] at vertices
  have gaps := protected_size_of_traceable_deletion z (by omega) P hP p hp longest
  change 1+G.degree z+(G.degree z+1)*E.card ≤ Fintype.card V at gaps
  have scale := Nat.mul_le_mul_right E.card (show 4 ≤ G.degree z+1 by omega)
  have size : E.card=4 := by omega
  have count := card_add_card_compl p.support.toFinset
  rw [List.toFinset_card_of_nodup hp.support_nodup] at count
  change p.support.length+E.card=Fintype.card V at count
  exact Graph189SaturatedExterior.exclude p hp t mx exc cap 4 3 size (by omega) (by decide) (by decide) (by omega) (by omega)
end Graph189SixProtected
end
section
open SimpleGraph Finset
namespace Graph189SixMinimumThree
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]
theorem traceable (conn : 2 ≤ G.vertexConnectivity) (six : G.secondSmallestDegree=6)
    (minimum : 3 ≤ G.minDegree) (small : Fintype.card V≤20)
    (localCap : ∀v,G.distEven v ≤ G.secondSmallestDegree+1) :
    ∃a b,∃p : G.Walk a b,p.IsHamiltonian := by
  classical
  have min (v : V) : 3 ≤ G.degree v := minimum.trans (G.minDegree_le_degree v)
  obtain ⟨z⟩ := (inferInstance : Nonempty V)
  obtain ⟨a,b,p,hp,mx⟩ := Graph189ThreeRegularMinimum.longest_path (G:=G) z
  let E := p.support.toFinsetᶜ
  have low (v : V) (hv : v∈E) : G.degree v<6 :=
    Graph189SixRotation.omitted_low p hp mx conn small six (by omega) localCap (by simpa [E] using hv)
  have few : E.card≤1 := by
    apply card_le_one.mpr
    intro u hu v hv
    by_contra ne
    have pair := OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1.degree_pair (G:=G) u v ne
    have l1 := low u hu
    have l2 := low v hv
    omega
  have pop := card_add_card_compl p.support.toFinset
  rw [List.toFinset_card_of_nodup hp.support_nodup] at pop
  change p.support.length+E.card=Fintype.card V at pop
  by_contra nontrace
  obtain ⟨w,lw,_,_,r,hr⟩ := Graph189ExteriorDegreeCycle.near_longest_has_hamiltonian_low_deletion
    p hp mx (by omega) nontrace (by omega) localCap min
  have high (x : V) (ne : x≠w) : G.secondSmallestDegree ≤ G.degree x :=
    (OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1.degree_pair (G:=G) x w ne).resolve_right
      (not_le.mpr lw)
  exact nontrace (Graph189SixProtected.traceable w (min w) six high localCap (by omega) r hr)
end Graph189SixMinimumThree
end
section
open SimpleGraph Finset
open OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1
namespace Graph189ModerateForDesk
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]
theorem six (hc : G.Connected) (cap : (univ.image (distEven G)).max' (by simp)≤1+G.secondSmallestDegree)
    (uncut : ∀z : V,(G.induce {v : V | v≠z}).Connected) (conn : 2 ≤ G.vertexConnectivity)
    (k6 : G.secondSmallestDegree=6) (lower : 2*G.secondSmallestDegree+3 ≤ Fintype.card V)
    (upper : Fintype.card V≤3*G.secondSmallestDegree+2) :
    ∃a b,∃r : G.Walk a b,r.IsHamiltonian := by
  classical
  have point (v : V) : G.distEven v ≤ G.secondSmallestDegree+1 := by
    simpa only [Nat.add_comm] using (le_max' _ _ (mem_image_of_mem _ (mem_univ v))).trans cap
  obtain ⟨z,hz⟩ := G.exists_minimal_degree_vertex
  have fd := Graph189CutSides.connectivity_le_degree (G:=G) z
  by_cases low : G.degree z=2
  · have bd := Graph189LayerCutoff.order_of_small_degree G hc z _ point (by omega)
    rw [low,k6] at bd
    exact Graph189SixOrder.of_deletions hc cap k6 (by omega) lower uncut
  exact Graph189SixMinimumThree.traceable conn k6 (by omega) (by omega) point
end Graph189ModerateForDesk
end
section
open SimpleGraph Finset
namespace Graph189ModerateSplitProofs
private theorem maximum {V : Type} [Fintype V] [DecidableEq V] [Nontrivial V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (point : ∀ x, G.distEven x ≤ 1+G.secondSmallestDegree) :
    (univ.image (distEven G)).max' (by simp) ≤ 1+G.secondSmallestDegree := by
  classical
  apply max'_le
  intro _ hw
  obtain ⟨w,_,rfl⟩ := mem_image.mp hw
  exact point w
theorem six : OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R2_H2_R1_H1_R1.H3 := by
  intro V _ _ _ G _ hc point lower uncut upper _wide degree
  have conn := Graph189ParentConnectivity.two_of_deletions hc (by omega) uncut
  exact Graph189ModerateForDesk.six hc (maximum G point) uncut conn degree lower upper
end Graph189ModerateSplitProofs
end
theorem OMA.solution : OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R2_H2_R1_H1_R1.H3 := Graph189ModerateSplitProofs.six
