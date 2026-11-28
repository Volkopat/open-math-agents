import OMAReductions.R_DisjointNPPairs_no_complete_disjoint_NP_pair_variants_exists_of_NP_eq_coNP_R1_H1_R1

-- Shorter proof by misothy, assisted by ChatGPT (GPT-6.2).
-- Original solver credit remains with the original merged proof.
-- Composition of sublists replaces the separate length-sum argument.
private theorem block {α β : Type} (f : α → List β) {l : List α} {x : α}
    (h : x ∈ l) : (f x).Sublist (l.flatMap f) :=
  List.sublist_flatten_of_mem (List.mem_map.mpr ⟨x,h,rfl⟩)

theorem OMA.solution : OMA.R_DisjointNPPairs_no_complete_disjoint_NP_pair_variants_exists_of_NP_eq_coNP_R1_H1_R1.H2 := by
  intro F a
  let lit (t : Bool × ℕ) := [true,t.1] ++ List.replicate t.2 true ++ [false]
  let clause (c : List (Bool × ℕ)) := c.flatMap lit ++ [false]
  let L := (F.flatMap clause).length
  refine ⟨(List.range L).map a,by simp [L,clause,lit],?_⟩
  intro c hc t ht
  have h := ((block lit ht).trans ((List.sublist_append_left _ [false]).trans (block clause hc))).length_le
  change (lit t).length ≤ L at h
  have e : (lit t).length = t.2 + 3 := by simp [lit]
  rw [e] at h
  rw [List.getElem?_map,List.getElem?_range (by omega)]
  rfl
