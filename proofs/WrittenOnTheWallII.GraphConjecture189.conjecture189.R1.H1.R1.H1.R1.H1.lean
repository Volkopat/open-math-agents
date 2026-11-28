import OMAReductions.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1_H1_R1_H1_R1

/-! Center case of Graph Conjecture 189: the closure makes the neighbourhood of `u`
completely joined to its non-neighbourhood, and an alternating path finishes. -/

namespace OMA.Gap189Center

open SimpleGraph
open OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1_H1_R1_H1_R1

variable {V : Type} [Fintype V] [DecidableEq V]

lemma two_step {G : SimpleGraph V} {c y x : V} (h1 : G.Adj c y) (h2 : x = y ∨ G.Adj y x) :
    G.dist c x ≤ 2 := by
  rcases h2 with rfl | h2
  · exact (dist_le (Walk.cons h1 Walk.nil)).trans (by simp)
  · exact (dist_le (Walk.cons h1 (Walk.cons h2 Walk.nil))).trans (by simp)

lemma dist_two {G : SimpleGraph V} (hc : G.Connected) {c y x : V} (h1 : G.Adj c y)
    (h2 : G.Adj y x) (hne : c ≠ x) (hna : ¬ G.Adj c x) : G.dist c x = 2 := by
  have h := two_step h1 (Or.inr h2)
  have h' := hc.one_lt_dist_of_ne_of_not_adj hne hna
  omega

lemma mid_of_length_two {G : SimpleGraph V} {x y : V} (p : G.Walk x y) (hp : p.length = 2) :
    ∃ z, G.Adj x z ∧ G.Adj z y := by
  cases p with
  | nil => simp at hp
  | cons h1 q =>
    cases q with
    | nil => simp at hp
    | cons h2 r =>
      cases r with
      | nil => exact ⟨_, h1, h2⟩
      | cons h3 t => simp at hp

lemma degree_add_two {G H : SimpleGraph V} [DecidableRel G.Adj] [DecidableRel H.Adj]
    (hGH : G ≤ H) {b x y : V} (hxy : x ≠ y) (hx : H.Adj b x) (hy : H.Adj b y)
    (hgx : ¬ G.Adj b x) (hgy : ¬ G.Adj b y) : G.degree b + 2 ≤ H.degree b := by
  rw [← card_neighborFinset_eq_degree, ← card_neighborFinset_eq_degree]
  have hsub : insert x (insert y (G.neighborFinset b)) ⊆ H.neighborFinset b := by
    intro z hz
    simp only [Finset.mem_insert, mem_neighborFinset] at hz ⊢
    rcases hz with rfl | rfl | hz
    · exact hx
    · exact hy
    · exact hGH hz
  have hle := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem] at hle
  · omega
  · simpa using hgy
  · simp [hxy, hgx]

lemma min_le_second [Nontrivial V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    G.minDegree ≤ G.secondSmallestDegree := by
  have hlen : 2 ≤ (degreeSequence G).length := by
    simpa [degreeSequence] using Nat.succ_le_of_lt (Fintype.one_lt_card (α := V))
  have hmem : G.secondSmallestDegree ∈ degreeSequence G := by
    unfold secondSmallestDegree
    rw [List.getD_eq_getElem _ _ (by omega)]
    exact List.getElem_mem _
  have hmem' : G.secondSmallestDegree ∈ (Finset.univ.val.map fun x : V => G.degree x) := by
    simpa [degreeSequence] using hmem
  obtain ⟨x, _, hx⟩ := Multiset.mem_map.mp hmem'
  exact hx ▸ G.minDegree_le_degree x

end OMA.Gap189Center

open SimpleGraph OMA.Gap189Center
open OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1_H1_R1_H1_R1 in
theorem OMA.solution : OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1_H1_R1_H1_R1.H1 := by
  classical
  intro V _ _ _ G _ hc hd hm2 heven hhall v u w huw hn hauw hcen hdu hcard
  set s := G.secondSmallestDegree with hs
  have neigh (x : V) : G.Adj v x ↔ x = u ∨ x = w := by
    rw [← G.mem_neighborFinset, hn]
    simp
  have hu : G.Adj v u := (neigh u).mpr (Or.inl rfl)
  have hw : G.Adj v w := (neigh w).mpr (Or.inr rfl)
  have hvdeg : G.degree v = 2 := by
    rw [← card_neighborFinset_eq_degree, hn, Finset.card_pair huw]
  have hv : G.degree v = G.minDegree := by rw [hm2, hvdeg]
  have hlow {x : V} (hx : x ≠ v) : s ≤ G.degree x := high_off_minimum hv hx
  have hs2 : 2 ≤ s := by
    have := min_le_second G
    omega
  let A := ((G.neighborFinset u).erase v).erase w
  let B := (Finset.univ.filter (fun x => ¬ G.Adj u x)).erase u
  have memA (x : V) : x ∈ A ↔ x ≠ w ∧ x ≠ v ∧ G.Adj u x := by simp [A]
  have memB (x : V) : x ∈ B ↔ x ≠ u ∧ ¬ G.Adj u x := by simp [B]
  have huvm := (G.mem_neighborFinset u v).mpr hu.symm
  have hwA : w ∈ (G.neighborFinset u).erase v := by simp [hw.ne.symm, hauw]
  have hA : A.card = s := by
    simp [A, Finset.card_erase_of_mem hwA, Finset.card_erase_of_mem huvm, hdu]
  have hset := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset V)) (p := G.Adj u)
  rw [← neighborFinset_eq_filter, card_neighborFinset_eq_degree, Finset.card_univ] at hset
  have huB : u ∈ Finset.univ.filter (fun x => ¬ G.Adj u x) := by simp
  have hB : B.card = s := by
    change ((Finset.univ.filter _).erase u).card = s
    rw [Finset.card_erase_of_mem huB]
    omega
  have hBv {b : V} (hb : b ∈ B) : b ≠ v := fun h => ((memB b).mp hb).2 (h ▸ hu.symm)
  have hBw {b : V} (hb : b ∈ B) : b ≠ w := fun h => ((memB b).mp hb).2 (h ▸ hauw)
  -- the neighbour `w` of `v` has no neighbour outside the closed neighbourhood of `u`
  have hwB : ∀ b ∈ B, ¬ G.Adj w b := by
    intro b hb hwb
    have hev := heven v
    have hsub : insert v (insert b A) ⊆ Finset.univ.filter (fun x => Even (G.dist v x)) := by
      intro x hx
      simp only [Finset.mem_insert] at hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rcases hx with rfl | rfl | hx
      · simp
      · rw [dist_two hc hw hwb (hBv hb).symm (fun h => by
          rcases (neigh x).mp h with h' | h'
          · exact ((memB x).mp hb).1 h'
          · exact hBw hb h')]
        exact even_two
      · obtain ⟨hxw, hxv, hux⟩ := (memA x).mp hx
        rw [dist_two hc hu hux (Ne.symm hxv) (fun h => by
          rcases (neigh x).mp h with h' | h'
          · exact G.loopless.irrefl u (h' ▸ hux)
          · exact hxw h')]
        exact even_two
    have hbA : b ∉ A := fun h => ((memB b).mp hb).2 ((memA b).mp h).2.2
    have hvbA : v ∉ insert b A := by
      simp only [Finset.mem_insert, not_or]
      exact ⟨(hBv hb).symm, fun h => ((memA v).mp h).2.1 rfl⟩
    have hcardle := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem hvbA, Finset.card_insert_of_notMem hbA, hA] at hcardle
    unfold distEven at hev
    omega
  apply hamiltonian_of_spanning_path
  by_contra hno
  obtain ⟨H, hGH, hH, hsat⟩ := maximal_nontraceable hno
  have hhigh {x : V} (hx : x ≠ v) : s ≤ H.degree x := (hlow hx).trans (degree_le_of_le hGH)
  have hucore {x : V} (hx : x ≠ v) (hxu : x ≠ u) : H.Adj u x := by
    by_contra h
    have hfail := hsat u x hxu.symm h
    have : G.degree u ≤ H.degree u := degree_le_of_le hGH
    have := hhigh hx
    omega
  have hadj {x y : V} (hxy : x ≠ y) (h : 2 * s + 2 ≤ H.degree x + H.degree y) : H.Adj x y := by
    by_contra h'
    have := hsat x y hxy h'
    omega
  have hsub {x : V} (h : H.degree x ≤ G.degree x) {y : V} (hy : H.Adj x y) : G.Adj x y := by
    by_contra h'
    have := degree_grows_of_new_edge hGH hy h'
    omega
  have hBH : ∀ b ∈ B, s + 1 ≤ H.degree b := by
    intro b hb
    have hnew := degree_grows_of_new_edge hGH (hucore (hBv hb) ((memB b).mp hb).1).symm
      (fun h => ((memB b).mp hb).2 h.symm)
    have := hlow (hBv hb)
    omega
  have hcross : ∀ b ∈ B, ∀ a ∈ A, H.Adj b a := by
    intro b hb a ha
    obtain ⟨haw, hav, hua⟩ := (memA a).mp ha
    by_contra hnab
    have hba : b ≠ a := fun h => ((memB b).mp hb).2 (h ▸ hua)
    have hfail := hsat b a hba hnab
    have hHa := hhigh hav
    have hHb := hBH b hb
    -- `w` keeps its degree
    have hbw : ¬ H.Adj b w := by
      intro h
      have := degree_add_two hGH (hauw.ne.symm) h (hucore (hBv hb) ((memB b).mp hb).1).symm
        (fun h' => hwB b hb h'.symm) (fun h' => ((memB b).mp hb).2 h'.symm)
      have := hlow (hBv hb)
      omega
    have hwdeg : H.degree w ≤ s := by
      have := hsat b w (hBw hb) hbw
      omega
    have hwG {y : V} (hy : H.Adj w y) : G.Adj w y :=
      hsub (hwdeg.trans (hlow hw.ne.symm)) hy
    -- every vertex of `B` only gains the edge to `u`
    have hBonly : ∀ b' ∈ B, ∀ y, H.Adj b' y → y ≠ u → G.Adj b' y := by
      intro b' hb' y hy hyu
      by_contra hg
      have hnw : ¬ H.Adj w b' := fun h => hwB b' hb' (hwG h)
      have hle := hsat w b' (hBw hb').symm hnw
      have := degree_add_two hGH hyu hy (hucore (hBv hb') ((memB b').mp hb').1).symm hg
        (fun h' => ((memB b').mp hb').2 h'.symm)
      have := hlow (hBv hb')
      have := hhigh hw.ne.symm
      omega
    have hBcl : ∀ x ∈ B, ∀ y ∈ B, x ≠ y → G.Adj x y := by
      intro x hx y hy hxy
      have h1 := hBH x hx
      have h2 := hBH y hy
      exact hBonly x hx y (hadj hxy (by omega)) ((memB y).mp hy).1
    -- a common neighbour of `u` and `b`
    obtain ⟨p, hp⟩ := hc.exists_walk_length_eq_dist u b
    have hdub : G.dist u b = 2 := by
      have := hcen b
      have := hc.one_lt_dist_of_ne_of_not_adj ((memB b).mp hb).1.symm ((memB b).mp hb).2
      omega
    obtain ⟨a0, hua0, ha0b⟩ := mid_of_length_two p (hp.trans hdub)
    have ha0v : a0 ≠ v := by
      rintro rfl
      rcases (neigh b).mp ha0b with h | h
      · exact ((memB b).mp hb).1 h
      · exact hBw hb h
    have ha0w : a0 ≠ w := by
      rintro rfl
      exact hwB b hb ha0b
    have ha0u : a0 ≠ u := G.ne_of_adj hua0.symm
    -- `a0` sees everything within distance two
    have hall0 : ∀ x, G.dist a0 x ≤ 2 := by
      intro x
      by_cases hx : x ∈ B
      · by_cases hxb : x = b
        · exact two_step ha0b (Or.inl hxb)
        · exact two_step ha0b (Or.inr (hBcl b hb x hx (Ne.symm hxb)))
      · have hx' : x = u ∨ G.Adj u x := by
          by_contra h
          push Not at h
          exact hx ((memB x).mpr h)
        exact two_step hua0.symm hx'
    have hdeg0 : s + 2 ≤ G.degree a0 := by
      have h1 := order_from_center hall0
      have h2 := heven a0
      omega
    have hHa0 : s + 2 ≤ H.degree a0 := hdeg0.trans (degree_le_of_le hGH)
    have hBa0 : ∀ x ∈ B, G.Adj x a0 := by
      intro x hx
      have := hBH x hx
      exact hBonly x hx a0 (hadj (fun h => ((memB x).mp hx).2 (h ▸ hua0)) (by omega)) ha0u
    have haa0 : a ≠ a0 := by
      rintro rfl
      exact hnab (hGH ha0b.symm)
    have hHaa0 : H.Adj a a0 := hadj haa0 (by omega)
    have hGa : G.degree a ≤ H.degree a := degree_le_of_le hGH
    have hGas := hlow hav
    have hGaa0 : G.Adj a a0 := hsub (by omega) hHaa0
    have hall : ∀ x, G.dist a x ≤ 2 := by
      intro x
      by_cases hx : x ∈ B
      · exact two_step hGaa0 (Or.inr (hBa0 x hx).symm)
      · have hx' : x = u ∨ G.Adj u x := by
          by_contra h
          push Not at h
          exact hx ((memB x).mpr h)
        exact two_step hua.symm hx'
    have h1 := order_from_center hall
    have h2 := heven a
    omega
  obtain ⟨b1, hb1⟩ : B.Nonempty := Finset.card_pos.mp (by omega)
  have hdis : Disjoint B A := Finset.disjoint_left.mpr fun x hx hy =>
    ((memB x).mp hx).2 ((memA x).mp hy).2.2
  obtain ⟨l, hh, hnd, hch, hl⟩ := alternating_chain (G := H) B A (hB.trans hA.symm) hdis hcross b1 hb1
  have hmemb (x : V) : x ∈ l ↔ (x ≠ u ∧ ¬ G.Adj u x) ∨ (x ≠ w ∧ x ≠ v ∧ G.Adj u x) := by
    rw [← List.mem_toFinset, hl, Finset.mem_union, memB, memA]
  apply hH
  refine ⟨v :: w :: u :: l, ?_, ?_, ?_⟩
  · have hvl : v ∉ l := by
      rw [hmemb]
      rintro (⟨_, h⟩ | ⟨_, h, _⟩)
      · exact h hu.symm
      · exact h rfl
    have hwl : w ∉ l := by
      rw [hmemb]
      rintro (⟨_, h⟩ | ⟨h, _, _⟩)
      · exact h hauw
      · exact h rfl
    have hul : u ∉ l := by
      rw [hmemb]
      rintro (⟨h, _⟩ | ⟨_, _, h⟩)
      · exact h rfl
      · exact G.loopless.irrefl u h
    refine List.nodup_cons.mpr ⟨?_, List.nodup_cons.mpr ⟨?_, List.nodup_cons.mpr ⟨hul, hnd⟩⟩⟩
    · simp only [List.mem_cons, not_or]
      exact ⟨hw.ne, hu.ne, hvl⟩
    · simp only [List.mem_cons, not_or]
      exact ⟨huw.symm, hwl⟩
  · intro x
    simp only [List.mem_cons, hmemb]
    tauto
  · refine List.isChain_cons.mpr ⟨by simpa using hGH hw, List.isChain_cons.mpr
      ⟨by simpa using hGH hauw.symm, List.isChain_cons.mpr ⟨?_, hch⟩⟩⟩
    intro y hy
    have hyb : y = b1 := by simpa [hh, eq_comm] using hy
    exact hyb ▸ hucore (hBv hb1) ((memB b1).mp hb1).1
