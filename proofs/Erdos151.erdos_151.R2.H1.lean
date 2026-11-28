import OMAReductions.R_Erdos151_erdos_151_R2

/-! Five-colorable graphs satisfy the clique transversal bound in Erdős Problem 151.
Credit: @ellisjr. The triangle-free hitting criterion is from the parent reduction by @sun-jiao. -/

namespace OMA.FiveColor

open Finset SimpleGraph
open scoped Classical

/-- Greedily extend a proper coloring from a finite set of vertices. -/
lemma color_of_degree_four {n : ℕ} (G : SimpleGraph (Fin n))
    (hdeg : ∀ v, (univ.filter (G.Adj v)).card ≤ 4) :
    ∃ c : Fin n → Fin 5, ∀ ⦃x y⦄, G.Adj x y → c x ≠ c y := by
  classical
  have extend (s : Finset (Fin n)) :
      ∃ c : Fin n → Fin 5, ∀ x ∈ s, ∀ y ∈ s, G.Adj x y → c x ≠ c y := by
    induction s using Finset.induction_on with
    | empty => exact ⟨fun _ => 0, by simp⟩
    | @insert v s hv ih =>
      obtain ⟨c, hc⟩ := ih
      let used := (univ.filter (G.Adj v)).image c
      have hcard : used.card < (univ : Finset (Fin 5)).card := by
        have hle := (card_image_le (f := c) (s := univ.filter (G.Adj v))).trans (hdeg v)
        simpa [used] using Nat.lt_succ_of_le hle
      obtain ⟨a, _, ha⟩ := exists_mem_notMem_of_card_lt_card hcard
      have free {y} (hy : G.Adj v y) : a ≠ c y := by
        intro he
        exact ha (he ▸ mem_image_of_mem c (mem_filter.mpr ⟨mem_univ y, hy⟩))
      refine ⟨fun x => if x = v then a else c x, ?_⟩
      intro x hx y hy hxy
      by_cases h₁ : x = v
      · subst x
        simpa [hxy.ne.symm] using free hxy
      by_cases h₂ : y = v
      · subst y
        simpa [h₁] using (free hxy.symm).symm
      simpa [h₁, h₂] using hc x ((mem_insert.mp hx).resolve_left h₁)
        y ((mem_insert.mp hy).resolve_left h₂) hxy
  obtain ⟨c, hc⟩ := extend univ
  exact ⟨c, fun {x y} => hc x (mem_univ x) y (mem_univ y)⟩

/-- The pentagon and its complement have no triangle. -/
private lemma pentagon_no_triangle : ∀ a b c : Fin 5, (cycleGraph 5).Adj a b →
    (cycleGraph 5).Adj a c → ¬ (cycleGraph 5).Adj b c := by decide

private lemma pentagon_hits_triple : ∀ a b c : Fin 5, a ≠ b → a ≠ c → b ≠ c →
    (cycleGraph 5).Adj a b ∨ (cycleGraph 5).Adj a c ∨ (cycleGraph 5).Adj b c := by decide

/-- Retain the pentagon edges and the edges of G lying in no triangle. -/
lemma hitting_graph {n : ℕ} (G : SimpleGraph (Fin n))
    (c : Fin n → Fin 5) (proper : ∀ ⦃x y⦄, G.Adj x y → c x ≠ c y) :
    ∃ F : SimpleGraph (Fin n), F.CliqueFree 3 ∧
      ∀ s, G.IsBigMaximalClique s → ∃ u ∈ s, ∃ v ∈ s, F.Adj u v := by
  classical
  let F : SimpleGraph (Fin n) := {
    Adj := fun x y => G.Adj x y ∧
      ((cycleGraph 5).Adj (c x) (c y) ∨ ¬ ∃ w, G.Adj x w ∧ G.Adj y w)
    symm := ⟨fun x y h => ⟨h.1.symm, h.2.imp (fun e => e.symm)
      (fun hn ⟨w, hy, hx⟩ => hn ⟨w, hx, hy⟩)⟩⟩
    loopless := ⟨fun _ h => G.irrefl h.1⟩
  }
  refine ⟨F, ?_, ?_⟩
  · intro t ht
    obtain ⟨x, y, z, hxy, hxz, hyz, _⟩ := is3Clique_iff.mp ht
    exact pentagon_no_triangle (c x) (c y) (c z)
      (hxy.2.resolve_right fun hn => hn ⟨z, hxz.1, hyz.1⟩)
      (hxz.2.resolve_right fun hn => hn ⟨y, hxy.1, hyz.1.symm⟩)
      (hyz.2.resolve_right fun hn => hn ⟨x, hxy.1.symm, hxz.1.symm⟩)
  · intro s hs
    by_cases h : 2 < s.card
    · obtain ⟨x, y, z, hx, hy, hz, hxy, hxz, hyz⟩ := two_lt_card_iff.mp h
      have exy := hs.1.1 hx hy hxy
      have exz := hs.1.1 hx hz hxz
      have eyz := hs.1.1 hy hz hyz
      rcases pentagon_hits_triple _ _ _ (proper exy) (proper exz) (proper eyz) with e | e | e
      · exact ⟨x, hx, y, hy, exy, Or.inl e⟩
      · exact ⟨x, hx, z, hz, exz, Or.inl e⟩
      · exact ⟨y, hy, z, hz, eyz, Or.inl e⟩
    · obtain ⟨u, v, huv, rfl⟩ := card_eq_two.mp (le_antisymm (le_of_not_gt h) hs.2)
      have hu : u ∈ ({u, v} : Finset (Fin n)) := by simp
      have hv : v ∈ ({u, v} : Finset (Fin n)) := by simp
      refine ⟨u, hu, v, hv, hs.1.1 hu hv huv, Or.inr ?_⟩
      rintro ⟨w, huw, hvw⟩
      have hcl : G.IsClique (↑(insert w ({u, v} : Finset (Fin n))) : Set (Fin n)) := by
        rw [coe_insert]
        apply hs.1.1.insert
        intro t ht _
        rcases (show t = u ∨ t = v by simpa using ht) with rfl | rfl
        · exact huw.symm
        · exact hvw.symm
      have hw := hs.1.2 hcl (subset_insert _ _) (mem_insert_self w _)
      rcases (show w = u ∨ w = v by simpa using hw) with rfl | rfl
      · exact G.irrefl huw
      · exact G.irrefl hvw

lemma bound_of_five_colors {n : ℕ} (G : SimpleGraph (Fin n))
    (c : Fin n → Fin 5) (proper : ∀ ⦃x y⦄, G.Adj x y → c x ≠ c y) :
    G.cliqueTransversalNumber ≤ n - Erdos151.H n := by
  obtain ⟨F, hF, hit⟩ := hitting_graph G c proper
  exact OMA.R_Erdos151_erdos_151_R2.bound_of_hitting G F hF hit

lemma bound_of_threshold_le_five {n : ℕ} (G : SimpleGraph (Fin n)) (hk : Erdos151.H n ≤ 5) :
    G.cliqueTransversalNumber ≤ n - Erdos151.H n := by
  by_cases h : ∃ v, Erdos151.H n ≤ (univ.filter (G.Adj v)).card
  · obtain ⟨v, hv⟩ := h
    exact OMA.R_Erdos151_erdos_151_R2.neighborhood_bound G v hv
  · have hdeg (v) : (univ.filter (G.Adj v)).card ≤ 4 := by
      have hv : ¬ Erdos151.H n ≤ (univ.filter (G.Adj v)).card := fun hv => h ⟨v, hv⟩
      omega
    obtain ⟨c, hc⟩ := color_of_degree_four G hdeg
    exact bound_of_five_colors G c hc

end OMA.FiveColor

theorem OMA.solution : OMA.R_Erdos151_erdos_151_R2.H1 := by
  intro n G hk _ _ _ _
  exact OMA.FiveColor.bound_of_threshold_le_five G hk.le
