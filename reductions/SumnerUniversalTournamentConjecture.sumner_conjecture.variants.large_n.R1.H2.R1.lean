import OMAReductions.R_SumnerUniversalTournamentConjecture_sumner_conjecture_variants_large_n_R1

/-!
# Large Sumner tournaments with pendant siblings

The proof of the prescribed-root semidegree lemma and its orientation helper below are
adapted from @iskamag's merged pull request 1552 in lefttosolve2/open-math-agents.
The pruning and extension lemmas below attach a whole set of pendant siblings at one vertex.
The existing parent reduction supplies the tournament degree count used to choose its image.
-/

open Finset SimpleGraph Digraph SumnerUniversalTournamentConjecture

namespace OMA.R_SumnerUniversalTournamentConjecture_sumner_conjecture_variants_large_n_R1_H2_R1

/-- The residual case excludes an ordered transitive subtournament and any set of
pendant siblings large enough for the rooted minimum-semidegree embedding. -/
def H1 : Prop := ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
  ∀ {W : Type} [Fintype W] [DecidableEq W] (D : Digraph W) [DecidableRel D.Adj],
    Fintype.card W = n → IsOrientedTree D →
    (¬ ∃ c : W, ∀ u v, D.Adj u v → u = c ∨ v = c) →
    (∃ x : W, 3 < {w | D.Adj x w ∨ D.Adj w x}.ncard) →
    ∀ {V : Type} [Fintype V] [DecidableEq V] (G : Digraph V) [DecidableRel G.Adj],
      Fintype.card V = 2*n-2 → G.IsTournament →
      (¬ ∃ s : Fin n ↪ V, ∀ i j, i < j → G.Adj (s i) (s j)) →
      (¬ ∃ (p : W) (L : Finset W), p ∉ L ∧
        ((∀ a b, D.Adj a b → a ∉ L ∧ (b ∈ L → a = p)) ∨
         (∀ a b, D.Adj a b → b ∉ L ∧ (a ∈ L → b = p))) ∧
        ∀ v : V, n-L.card-1 ≤ (univ.filter (G.Adj v)).card ∧
          n-L.card-1 ≤ (univ.filter (fun w => G.Adj w v)).card) →
      Embeds D G

/-- A finite oriented tree admits an injective topological numbering. -/
def H2 : Prop :=
  ∀ (n : ℕ) {W : Type} [Fintype W] [DecidableEq W] (D : Digraph W),
    Fintype.card W = n → IsOrientedTree D →
    ∃ f : W → ℕ, Function.Injective f ∧ (∀ w, f w < n) ∧
      ∀ u v, D.Adj u v → f u < f v

lemma adj_or_rev_orient {W : Type*} {D : Digraph W} {T : SimpleGraph W}
    (hO : D.IsOrientation T) {u v : W} (hT : T.Adj u v) : D.Adj u v ∨ D.Adj v u := by
  by_cases h : D.Adj u v
  · exact Or.inl h
  · exact Or.inr (not_not.mp ((hO.2 u v hT).not.mp h))

-- Every oriented tree on m vertices (1 <= m <= d + 1) embeds into any irreflexive digraph G
-- with min(outdeg, indeg) >= d, sending a prescribed root r to ANY prescribed vertex v0!
lemma embeds_rooted_of_minDeg_ge :
    ∀ (m : ℕ), 1 ≤ m →
      ∀ {W : Type} [Fintype W] [DecidableEq W] (D : Digraph W) [DecidableRel D.Adj],
        Fintype.card W = m → IsOrientedTree D →
        ∀ (r : W) {V : Type} [Fintype V] [DecidableEq V] (G : Digraph V) [DecidableRel G.Adj],
          (∀ v : V, ¬ G.Adj v v) →
          ∀ (d : ℕ), m ≤ d + 1 →
          (∀ v : V, d ≤ (Finset.univ.filter (fun u : V => G.Adj v u)).card ∧
                    d ≤ (Finset.univ.filter (fun u : V => G.Adj u v)).card) →
          ∀ (v0 : V), ∃ f : D →g G, Function.Injective f ∧ f r = v0 := by
  intro m
  induction m with
  | zero => intro h0; omega
  | succ m' ih =>
    intro _ W _ _ D _ hW hD r V _ _ G _ hirr d hmd hdeg v0
    classical
    obtain ⟨T, hT, hO⟩ := hD
    by_cases hm' : m' = 0
    · -- Base case: |W| = 1, every vertex equals r!
      subst hm'
      have hall_r : ∀ w : W, w = r := by
        intro w
        by_contra hne
        have hlt : 1 < Fintype.card W := Fintype.one_lt_card_iff.mpr ⟨w, r, hne⟩
        omega
      refine ⟨⟨fun _ => v0, ?_⟩, ?_, rfl⟩
      · intro a b hab
        exact absurd ((hall_r a).trans (hall_r b).symm) (T.ne_of_adj (hO.1 a b hab))
      · intro a b _; exact (hall_r a).trans (hall_r b).symm
    · -- Inductive step: |W| = m' + 1 >= 2. Pick a leaf l != r!
      have : Nontrivial W := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
      obtain ⟨l1, l2, hl12, hl1deg, hl2deg⟩ := hT.exists_ne_and_degree_eq_one
      have hex_leaf : ∃ l : W, l ≠ r ∧ T.degree l = 1 := by
        by_cases h1 : l1 = r
        · exact ⟨l2, fun h => hl12 (h1.trans h.symm), hl2deg⟩
        · exact ⟨l1, h1, hl1deg⟩
      obtain ⟨l, hlr, hldeg⟩ := hex_leaf
      -- Unique neighbor p of l in T
      have hnb_card : (T.neighborFinset l).card = 1 := by
        rw [SimpleGraph.card_neighborFinset_eq_degree]; exact hldeg
      obtain ⟨p, hp_eq⟩ := Finset.card_eq_one.mp hnb_card
      have hTlp : T.Adj l p := by
        have : p ∈ T.neighborFinset l := hp_eq.symm ▸ Finset.mem_singleton_self p
        exact (SimpleGraph.mem_neighborFinset T l p).mp this
      have hpl_ne : p ≠ l := (T.ne_of_adj hTlp).symm
      have hl_uniq : ∀ z : W, T.Adj l z → z = p := by
        intro z hz
        have : z ∈ ({p} : Finset W) := hp_eq ▸ (SimpleGraph.mem_neighborFinset T l z).mpr hz
        exact Finset.mem_singleton.mp this
      -- Remove l: T' = T.induce {l}ᶜ is a tree on m' vertices containing r and p!
      let S : Set W := ({l} : Set W)ᶜ
      have hT' : (T.induce S).IsTree :=
        ⟨hT.connected.induce_compl_singleton_of_degree_eq_one hldeg, hT.isAcyclic.induce S⟩
      let D' : Digraph S := ⟨fun a b => D.Adj a.1 b.1⟩
      have hO' : D'.IsOrientation (T.induce S) :=
        ⟨fun a b h => hO.1 a.1 b.1 h, fun a b h => hO.2 a.1 b.1 h⟩
      have hcardS : Fintype.card S = m' := by
        have h1 : Fintype.card S = Fintype.card ↥(Finset.univ.erase l) := by
          refine Fintype.card_of_bijective (f := fun x : S => (⟨x.1, Finset.mem_erase.mpr ⟨x.2, Finset.mem_univ _⟩⟩ : Finset.univ.erase l)) ⟨?_, ?_⟩
          · intro a b h; exact Subtype.ext (congrArg (fun z : ↥(Finset.univ.erase l) => z.1) h)
          · rintro ⟨w, hw⟩; exact ⟨⟨w, (Finset.mem_erase.mp hw).1⟩, rfl⟩
        rw [h1, Fintype.card_coe, Finset.card_erase_of_mem (Finset.mem_univ l), Finset.card_univ, hW]; omega
      have hrS : r ∈ S := fun h => hlr (Set.mem_singleton_iff.mp h).symm
      have hpS : p ∈ S := fun h => hpl_ne (Set.mem_singleton_iff.mp h)
      obtain ⟨f', hf'_inj, hf'_r⟩ := ih (by omega) D' hcardS ⟨T.induce S, hT', hO'⟩
        ⟨r, hrS⟩ G hirr d (by omega) hdeg v0
      let img : Finset V := Finset.univ.image f'
      have himg_card : img.card = m' := by
        rw [Finset.card_image_of_injective _ hf'_inj, Finset.card_univ, hcardS]
      have hfp_mem : f' ⟨p, hpS⟩ ∈ img := Finset.mem_image_of_mem f' (Finset.mem_univ _)
      -- Choose image z of l in N+(f' p) \ img or N-(f' p) \ img!
      have hex_z : ∃ z : V, z ∉ img ∧
          (D.Adj p l → G.Adj (f' ⟨p, hpS⟩) z) ∧ (D.Adj l p → G.Adj z (f' ⟨p, hpS⟩)) := by
        rcases adj_or_rev_orient hO hTlp.symm with hDpl | hDlp
        · have hsub : (Finset.univ.filter (fun u : V => G.Adj (f' ⟨p, hpS⟩) u)) \
              (img.erase (f' ⟨p, hpS⟩)) ⊆
              (Finset.univ.filter (fun u : V => G.Adj (f' ⟨p, hpS⟩) u)) \ img := by
            intro u hu
            simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and,
              Finset.mem_erase] at hu ⊢
            refine ⟨hu.1, fun huimg => hu.2 ⟨?_, huimg⟩⟩
            intro heq; exact hirr u (heq ▸ hu.1)
          have hc1 := Finset.card_le_card hsub
          have hc2 := Finset.le_card_sdiff (img.erase (f' ⟨p, hpS⟩))
            (Finset.univ.filter (fun u : V => G.Adj (f' ⟨p, hpS⟩) u))
          have hc3 : (img.erase (f' ⟨p, hpS⟩)).card = m' - 1 := by
            rw [Finset.card_erase_of_mem hfp_mem, himg_card]
          have hd_le := (hdeg (f' ⟨p, hpS⟩)).1
          obtain ⟨z, hz⟩ := Finset.card_pos.mp (by omega :
            0 < ((Finset.univ.filter (fun u : V => G.Adj (f' ⟨p, hpS⟩) u)) \ img).card)
          simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and] at hz
          exact ⟨z, hz.2, fun _ => hz.1, fun h => absurd h ((hO.2 p l (hO.1 p l hDpl)).mp hDpl)⟩
        · have hsub : (Finset.univ.filter (fun u : V => G.Adj u (f' ⟨p, hpS⟩))) \
              (img.erase (f' ⟨p, hpS⟩)) ⊆
              (Finset.univ.filter (fun u : V => G.Adj u (f' ⟨p, hpS⟩))) \ img := by
            intro u hu
            simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and,
              Finset.mem_erase] at hu ⊢
            refine ⟨hu.1, fun huimg => hu.2 ⟨?_, huimg⟩⟩
            intro heq; exact hirr u (heq ▸ hu.1)
          have hc1 := Finset.card_le_card hsub
          have hc2 := Finset.le_card_sdiff (img.erase (f' ⟨p, hpS⟩))
            (Finset.univ.filter (fun u : V => G.Adj u (f' ⟨p, hpS⟩)))
          have hc3 : (img.erase (f' ⟨p, hpS⟩)).card = m' - 1 := by
            rw [Finset.card_erase_of_mem hfp_mem, himg_card]
          have hd_le := (hdeg (f' ⟨p, hpS⟩)).2
          obtain ⟨z, hz⟩ := Finset.card_pos.mp (by omega :
            0 < ((Finset.univ.filter (fun u : V => G.Adj u (f' ⟨p, hpS⟩))) \ img).card)
          simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and] at hz
          exact ⟨z, hz.2, fun h => absurd h ((hO.2 l p (hO.1 l p hDlp)).mp hDlp), fun _ => hz.1⟩
      obtain ⟨z, hz_not, hz_out, hz_in⟩ := hex_z
      let f : W → V := fun w => if hw : w = l then z else f' ⟨w, hw⟩
      refine ⟨⟨f, ?_⟩, ?_, ?_⟩
      · intro a b hab
        by_cases hal : a = l <;> by_cases hbl : b = l
        · exact absurd (hal.trans hbl.symm) (T.ne_of_adj (hO.1 a b hab))
        · subst hal
          have hbp : b = p := hl_uniq b (hO.1 a b hab)
          subst hbp
          simp only [f, hbl, ↓reduceDIte]
          exact hz_in hab
        · subst hbl
          have hap : a = p := hl_uniq a (hO.1 a b hab).symm
          subst hap
          simp only [f, hal, ↓reduceDIte]
          exact hz_out hab
        · simp only [f, hal, hbl, ↓reduceDIte]
          exact f'.map_adj' hab
      · intro a b hEq
        change f a = f b at hEq
        by_cases hal : a = l <;> by_cases hbl : b = l
        · exact hal.trans hbl.symm
        · simp only [f, hal, hbl, ↓reduceDIte] at hEq
          exact absurd (hEq ▸ Finset.mem_image_of_mem f' (Finset.mem_univ (⟨b, hbl⟩ : S))) hz_not
        · simp only [f, hal, hbl, ↓reduceDIte] at hEq
          exact absurd (hEq.symm ▸ Finset.mem_image_of_mem f' (Finset.mem_univ (⟨a, hal⟩ : S))) hz_not
        · simp only [f, hal, hbl, ↓reduceDIte] at hEq
          exact congrArg Subtype.val (hf'_inj hEq)
      · change f r = v0
        simp only [f, hlr.symm, ↓reduceDIte]

        exact hf'_r

lemma tree_prune_siblings {W : Type} [Fintype W] [DecidableEq W] (D : Digraph W)
    (hD : IsOrientedTree D) (p : W) (L : Finset W) (hp : p ∉ L)
    (hleaves : ∀ a b, D.Adj a b → a ∉ L ∧ (b ∈ L → a = p)) :
    IsOrientedTree (⟨fun a b : ↥(Lᶜ : Finset W) => D.Adj a.val b.val⟩ : Digraph _) := by
  classical
  obtain ⟨T, hT, hO⟩ := hD
  let S : Set W := ↑(Lᶜ : Finset W)
  have memS (w : W) : w ∈ S ↔ w ∉ L := Finset.mem_compl
  let q : S := ⟨p, (memS p).2 hp⟩
  let π (w : W) : S := if hw : w ∈ S then ⟨w, hw⟩ else q
  have πfix (w : S) : π w.val = w := by simp [π, w.property]
  have πp : π p = q := πfix q
  have adj_parent {a b : W} (ha : a ∈ L) (hab : T.Adj a b) : b = p := by
    by_cases hd : D.Adj b a
    · exact (hleaves b a hd).2 ha
    · exact False.elim ((hleaves a b ((hO.2 a b hab).2 hd)).1 ha)
  have mapStep (a b : W) (hab : T.Adj a b) :
      Relation.ReflTransGen (T.induce S).Adj (π a) (π b) := by
    by_cases ha : a ∈ S
    · by_cases hb : b ∈ S
      · apply Relation.ReflTransGen.single
        simpa only [π, dif_pos ha, dif_pos hb, SimpleGraph.induce_adj] using hab
      · have hbL : b ∈ L := by simpa only [memS, not_not] using hb
        have he := adj_parent hbL hab.symm
        rw [he, πp]
        simpa only [π, dif_neg hb] using
          (Relation.ReflTransGen.refl : Relation.ReflTransGen (T.induce S).Adj q q)
    · have haL : a ∈ L := by simpa only [memS, not_not] using ha
      have he := adj_parent haL hab
      rw [he, πp]
      simpa only [π, dif_neg ha] using
        (Relation.ReflTransGen.refl : Relation.ReflTransGen (T.induce S).Adj q q)
  have hC : (T.induce S).Connected := by
    let _ : Nonempty S := ⟨q⟩
    constructor
    intro a b
    apply ((T.induce S).reachable_iff_reflTransGen _ _).2
    have hab := (T.reachable_iff_reflTransGen _ _).1 (hT.connected a.val b.val)
    have him : Relation.ReflTransGen (T.induce S).Adj (π a.val) (π b.val) :=
      Relation.ReflTransGen.lift' π mapStep _ _ hab
    simpa only [πfix] using him
  exact ⟨T.induce S, ⟨hC, hT.isAcyclic.induce S⟩,
    (fun a b h => hO.1 a.val b.val h), (fun a b h => hO.2 a.val b.val h)⟩

lemma extend_out_leaves {W V : Type} [Fintype W] [DecidableEq W]
    [Fintype V] [DecidableEq V] (D : Digraph W) (G : Digraph V) [DecidableRel G.Adj]
    (L : Finset W) (p : W) (hp : p ∉ L)
    (leaves : ∀ a b, D.Adj a b → a ∉ L ∧ (b ∈ L → a = p))
    (v : V) (hirr : ¬ G.Adj v v)
    (hdeg : Fintype.card W - 1 ≤ (univ.filter (G.Adj v)).card)
    (f : { Adj := fun a b : ↥(Lᶜ : Finset W) => D.Adj a.val b.val } →g G)
    (inj : Function.Injective f) (anchor : f ⟨p, mem_compl.mpr hp⟩ = v) : Embeds D G := by
  classical
  let used : Finset V := univ.image f
  let nbrs : Finset V := univ.filter (G.Adj v)
  let free := nbrs \ used
  have centerUsed : v ∈ used := anchor ▸ mem_image_of_mem f (mem_univ _)
  have usedCard : used.card = Fintype.card W - L.card := by
    rw [card_image_of_injective _ inj, card_univ, Fintype.card_coe, card_compl]
  have compPos : 0 < used.card := card_pos.mpr ⟨v, centerUsed⟩
  have sub : nbrs \ used.erase v ⊆ free := by
    intro w hw
    obtain ⟨hn, hne⟩ := mem_sdiff.mp hw
    refine mem_sdiff.mpr ⟨hn, fun hit => hne (mem_erase.mpr ⟨?_, hit⟩)⟩
    intro hv
    exact hirr (hv ▸ (mem_filter.mp hn).2)
  have nFree : L.card ≤ free.card := by
    have h₁ := le_card_sdiff (used.erase v) nbrs
    have h₂ := card_le_card sub
    have h₃ := card_erase_of_mem centerUsed
    have h₄ := L.card_le_univ
    change Fintype.card W - 1 ≤ nbrs.card at hdeg
    omega
  obtain ⟨g⟩ : Nonempty (↥L ↪ ↥free) :=
    Function.Embedding.nonempty_of_card_le (by simpa only [Fintype.card_coe] using nFree)
  let F (a : W) := if h : a ∈ L then (g ⟨a,h⟩).val else f ⟨a, mem_compl.mpr h⟩
  have inside (a : W) (h : a ∈ L) : F a = (g ⟨a,h⟩).val := dif_pos h
  have outside (a : W) (h : a ∉ L) : F a = f ⟨a, mem_compl.mpr h⟩ := dif_neg h
  have outsideUsed (a : W) (h : a ∉ L) : F a ∈ used := by
    rw [outside a h]
    exact mem_image_of_mem f (mem_univ _)
  have insideUnused (a : W) (h : a ∈ L) : F a ∉ used := by
    rw [inside a h]
    exact (mem_sdiff.mp (g ⟨a,h⟩).property).2
  refine ⟨⟨F,?_⟩,?_⟩
  · intro a b hab
    obtain ⟨ha, hb⟩ := leaves a b hab
    by_cases h : b ∈ L
    · rw [hb h, outside p hp, anchor, inside b h]
      exact (mem_filter.mp (mem_sdiff.mp (g ⟨b,h⟩).property).1).2
    · rw [outside a ha, outside b h]
      exact f.map_adj' hab
  · intro a b eq
    change F a = F b at eq
    by_cases ha : a ∈ L <;> by_cases hb : b ∈ L
    · rw [inside a ha, inside b hb] at eq
      exact congrArg Subtype.val (g.injective (Subtype.ext eq))
    · exact (insideUnused a ha (eq.symm ▸ outsideUsed b hb)).elim
    · exact (insideUnused b hb (eq ▸ outsideUsed a ha)).elim
    · rw [outside a ha, outside b hb] at eq
      exact congrArg Subtype.val (inj eq)

lemma out_leaf_fan_of_core {W V : Type} [Fintype W] [DecidableEq W]
    [Fintype V] [DecidableEq V] (D : Digraph W) [DecidableRel D.Adj]
    (G : Digraph V) [DecidableRel G.Adj] (n : ℕ) (hn : 2 ≤ n)
    (hW : Fintype.card W = n) (hV : Fintype.card V = 2*n-2) (tour : G.IsTournament)
    (L : Finset W) (p : W) (hp : p ∉ L)
    (leaves : ∀ a b, D.Adj a b → a ∉ L ∧ (b ∈ L → a = p))
    (tree : IsOrientedTree ({ Adj := fun a b : ↥(Lᶜ : Finset W) => D.Adj a.val b.val }))
    (hmin : ∀ v : V, n-L.card-1 ≤ (univ.filter (G.Adj v)).card ∧
      n-L.card-1 ≤ (univ.filter (fun w => G.Adj w v)).card) : Embeds D G := by
  classical
  let K : Digraph ↥(Lᶜ : Finset W) := ⟨fun a b => D.Adj a.val b.val⟩
  have hK : Fintype.card ↥(Lᶜ : Finset W) = n - L.card := by
    rw [Fintype.card_coe, card_compl, hW]
  have nonemptyK : Nonempty ↥(Lᶜ : Finset W) := ⟨⟨p, mem_compl.mpr hp⟩⟩
  have pos : 0 < n-L.card := hK ▸ Fintype.card_pos_iff.mpr nonemptyK
  obtain ⟨v, deg, _⟩ := SumnerStars.center G tour (n-1) 0 (by omega) (by omega)
  obtain ⟨f, inj, anchor⟩ := embeds_rooted_of_minDeg_ge
    (n-L.card) pos K hK tree ⟨p, mem_compl.mpr hp⟩ G tour.1 (n-L.card-1) (by omega) hmin v
  exact extend_out_leaves D G L p hp leaves v (tour.1 v) (hW ▸ deg) f inj anchor

lemma pendant_out_siblings {W V : Type} [Fintype W] [DecidableEq W]
    [Fintype V] [DecidableEq V] (D : Digraph W) [DecidableRel D.Adj]
    (G : Digraph V) [DecidableRel G.Adj] (n : ℕ) (hn : 2 ≤ n)
    (hW : Fintype.card W = n) (hV : Fintype.card V = 2*n-2)
    (tree : IsOrientedTree D) (tour : G.IsTournament) (p : W) (L : Finset W) (hp : p ∉ L)
    (leaves : ∀ a b, D.Adj a b → a ∉ L ∧ (b ∈ L → a = p))
    (hmin : ∀ v : V, n-L.card-1 ≤ (univ.filter (G.Adj v)).card ∧
      n-L.card-1 ≤ (univ.filter (fun w => G.Adj w v)).card) : Embeds D G :=
  out_leaf_fan_of_core D G n hn hW hV tour L p hp leaves
    (tree_prune_siblings D tree p L hp leaves) hmin

lemma pendant_in_siblings {W V : Type} [Fintype W] [DecidableEq W]
    [Fintype V] [DecidableEq V] (D : Digraph W) [DecidableRel D.Adj]
    (G : Digraph V) [DecidableRel G.Adj] (n : ℕ) (hn : 2 ≤ n)
    (hW : Fintype.card W = n) (hV : Fintype.card V = 2*n-2)
    (tree : IsOrientedTree D) (tour : G.IsTournament) (p : W) (L : Finset W) (hp : p ∉ L)
    (leaves : ∀ a b, D.Adj a b → b ∉ L ∧ (a ∈ L → b = p))
    (hmin : ∀ v : V, n-L.card-1 ≤ (univ.filter (G.Adj v)).card ∧
      n-L.card-1 ≤ (univ.filter (fun w => G.Adj w v)).card) : Embeds D G := by
  classical
  let R : Digraph W := ⟨fun a b => D.Adj b a⟩
  let H : Digraph V := ⟨fun a b => G.Adj b a⟩
  obtain ⟨T, hT, ori⟩ := tree
  have treeR : IsOrientedTree R := ⟨T, hT, (fun a b h => (ori.1 b a h).symm),
    fun a b h => ori.2 b a h.symm⟩
  have tourH : H.IsTournament := ⟨tour.1, fun a b ne => tour.2 b a ne.symm⟩
  obtain ⟨f, inj⟩ := pendant_out_siblings R H n hn hW hV treeR tourH p L hp
    (fun a b h => leaves b a h) (fun v => (hmin v).symm)
  exact ⟨⟨f, fun {_ _} h => f.map_adj' h⟩, inj⟩

theorem main : H1 → H2 →
    OMA.R_SumnerUniversalTournamentConjecture_sumner_conjecture_variants_large_n_R1.H2 := by
  intro residual ordering
  obtain ⟨N, residual⟩ := residual
  refine ⟨max 2 N, ?_⟩
  intro n hn W _ _ D _ hW tree nonstar high V _ _ G _ hV tour
  have hn' : 2 ≤ n := (le_max_left _ _).trans hn
  by_cases transitive : ∃ s : Fin n ↪ V, ∀ i j, i < j → G.Adj (s i) (s j)
  · obtain ⟨s, arcs⟩ := transitive
    obtain ⟨f, inj, bound, increasing⟩ := ordering n D hW tree
    let position (w : W) : Fin n := ⟨f w, bound w⟩
    refine ⟨⟨fun w => s (position w), fun {a b} hab =>
      arcs (position a) (position b) (increasing a b hab)⟩, ?_⟩
    intro a b eq
    exact inj (congrArg Fin.val (s.injective eq))
  · apply (Classical.byContradiction (p := Embeds D G))
    intro noembed
    apply noembed
    apply residual n ((le_max_right _ _).trans hn) D hW tree nonstar high G hV tour transitive
    rintro ⟨p, L, hp, leaves | leaves, hmin⟩
    · exact noembed (pendant_out_siblings D G n hn' hW hV tree tour p L hp leaves hmin)
    · exact noembed (pendant_in_siblings D G n hn' hW hV tree tour p L hp leaves hmin)

end OMA.R_SumnerUniversalTournamentConjecture_sumner_conjecture_variants_large_n_R1_H2_R1
