import FormalConjectures.Paper.BollobasEldridgeCatlinConjecture

/-!
# Clean switches at a single conflicting edge

Report all edges in the same coordinates, by pulling the blue graph back
along a near-packing. A link from x to w is a two-edge walk that changes
colour. The middle vertex and the order of colours both count.

In a nonpacking with unique common edge xy, every w outside {x,y} receives
a link from x. If there were none, swapping x and w would pack the graphs.
At x there are at least two links back to x, one of each order through y.
Double counting the links, together with the four degrees at x,y, gives a
lower bound for the number of vertices outside both coloured neighbourhoods
of both endpoints that receive exactly one link from x.
-/
-- Credit: @Pixelstorm44

namespace OMA.R_BollobasEldridgeCatlinConjecture_bollobas_eldridge_catlin_conjecture_R1

open SimpleGraph BollobasEldridgeCatlinConjecture

variable {V : Type}

lemma sum_adj [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (x : V) :
    (∑ w : V, if G.Adj x w then 1 else 0) = G.degree x := by
  rw [← G.card_neighborFinset_eq_degree, ← Finset.card_filter]
  congr 1
  ext w
  simp

lemma count_walks [Fintype V] (R B : SimpleGraph V) [DecidableRel R.Adj] [DecidableRel B.Adj] (x : V) :
    (∑ w : V, ∑ z ∈ R.neighborFinset x, if B.Adj z w then 1 else 0)
      ≤ R.degree x * B.maxDegree := by
  rw [Finset.sum_comm]
  simp_rw [sum_adj]
  calc
    _ ≤ ∑ _z ∈ R.neighborFinset x, B.maxDegree :=
      Finset.sum_le_sum fun z _ => B.degree_le_maxDegree z
    _ = _ := by simp

lemma walk_pos [Fintype V] (R B : SimpleGraph V) [DecidableRel R.Adj] [DecidableRel B.Adj]
    {x z w : V} (hx : R.Adj x z) (hw : B.Adj z w) :
    1 ≤ ∑ t ∈ R.neighborFinset x, if B.Adj t w then 1 else 0 := by
  simpa [hw] using
    (Finset.single_le_sum (f := fun t => if B.Adj t w then 1 else 0)
      (fun t _ => Nat.zero_le _) ((R.mem_neighborFinset x z).mpr hx))

lemma swap_packs [DecidableEq V] (R B : SimpleGraph V) {x y w : V}
    (honly : ∀ a b, R.Adj a b → B.Adj a b → (a = x ∧ b = y) ∨ (a = y ∧ b = x))
    (hw : w ≠ y) (hwx : w ≠ x)
    (hRB : ∀ z, R.Adj x z → ¬B.Adj z w)
    (hBR : ∀ z, B.Adj x z → ¬R.Adj z w) : Packs R B := by
  let s := Equiv.swap x w
  have away (a b : V) (ha : a = x ∨ a = w) (hb : b ≠ x) (hb' : b ≠ w)
      (hr : R.Adj a b) : ¬B.Adj (s a) (s b) := by
    rcases ha with rfl | rfl
    · simpa [s, Equiv.swap_apply_of_ne_of_ne hb hb', B.adj_comm w b] using hRB b hr
    · intro h
      have : B.Adj x b := by simpa [s, Equiv.swap_apply_of_ne_of_ne hb hb'] using h
      exact hBR b this hr.symm
  refine ⟨s, fun a b hr hb => ?_⟩
  by_cases ha : a = x ∨ a = w
  · by_cases h : b = x ∨ b = w
    · rcases ha with ha | ha <;> rcases h with h | h <;> subst a <;> subst b
      · exact hr.ne rfl
      · have hc : B.Adj x w := by simpa [s, B.adj_comm w x] using hb
        rcases honly _ _ hr hc with h | h
        · exact hw h.2
        · exact hwx h.2
      · have hc : B.Adj w x := by simpa [s, B.adj_comm x w] using hb
        rcases honly _ _ hr hc with h | h
        · exact hwx h.1
        · exact hw h.1
      · exact hr.ne rfl
    · exact away _ _ ha (fun e => h (.inl e)) (fun e => h (.inr e)) hr hb
  · by_cases h : b = x ∨ b = w
    · exact away _ _ h (fun e => ha (.inl e)) (fun e => ha (.inr e)) hr.symm hb.symm
    · have hc : B.Adj a b := by
        simpa only [s, Equiv.swap_apply_of_ne_of_ne (not_or.mp ha).1 (not_or.mp ha).2,
          Equiv.swap_apply_of_ne_of_ne (not_or.mp h).1 (not_or.mp h).2] using hb
      rcases honly _ _ hr hc with h' | h'
      · exact ha (.inl h'.1)
      · exact h (.inl h'.2)

/-- Incidence count for the clean, singly linked vertices at one endpoint. -/
lemma clean_count [Fintype V] [DecidableEq V] (R B : SimpleGraph V) [DecidableRel R.Adj] [DecidableRel B.Adj]
    {x y : V} (hr : R.Adj x y) (hb : B.Adj x y)
    (honly : ∀ a b, R.Adj a b → B.Adj a b → (a = x ∧ b = y) ∨ (a = y ∧ b = x))
    (hnp : ¬Packs R B) :
    let links := fun w =>
      (∑ z ∈ R.neighborFinset x, if B.Adj z w then 1 else 0) +
      (∑ z ∈ B.neighborFinset x, if R.Adj z w then 1 else 0)
    let clean := Finset.univ.filter fun w =>
      ¬R.Adj x w ∧ ¬B.Adj x w ∧ ¬R.Adj y w ∧ ¬B.Adj y w ∧ links w = 1
    Fintype.card V ≤ R.degree x * B.maxDegree + B.degree x * R.maxDegree ∧
    2 * Fintype.card V + 2 ≤ R.degree x * B.maxDegree + B.degree x * R.maxDegree +
      R.degree x + B.degree x + R.degree y + B.degree y + clean.card := by
  dsimp only
  let rb : V → ℕ := fun w => ∑ z ∈ R.neighborFinset x, if B.Adj z w then 1 else 0
  let br : V → ℕ := fun w => ∑ z ∈ B.neighborFinset x, if R.Adj z w then 1 else 0
  let links := fun w => rb w + br w
  let good := fun w =>
    ¬R.Adj x w ∧ ¬B.Adj x w ∧ ¬R.Adj y w ∧ ¬B.Adj y w ∧ links w = 1
  have hroot : 2 ≤ links x := Nat.add_le_add (walk_pos R B hr hb.symm) (walk_pos B R hb hr.symm)
  have hpos {w} (hwx : w ≠ x) (hwy : w ≠ y) : 1 ≤ links w := by
    by_contra! hz
    change rb w + br w < 1 at hz
    apply hnp (swap_packs R B honly hwy hwx ?_ ?_)
    · intro z h1 h2
      have : 1 ≤ rb w := walk_pos R B h1 h2
      omega
    · intro z h1 h2
      have : 1 ≤ br w := walk_pos B R h1 h2
      omega
  have hwalk : (∑ w, links w) ≤ R.degree x * B.maxDegree + B.degree x * R.maxDegree := by
    simpa only [links, Finset.sum_add_distrib, rb, br] using
      Nat.add_le_add (count_walks R B x) (count_walks B R x)
  have cover (w : V) :
      1 + (if w = x then 1 else 0) ≤ links w + (if w = y then 1 else 0) := by
    by_cases hx : w = x
    · subst w
      simpa [hr.ne] using hroot
    by_cases hy : w = y
    · simp [hy, hr.ne.symm]
    · simpa [hx, hy] using hpos hx hy
  have total := Finset.sum_le_sum (s := Finset.univ) (fun w _ => cover w)
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    mul_one, Finset.sum_ite_eq', Finset.mem_univ, if_true] at total
  have local_bound (w : V) :
      2 + (if w = x then 2 else 0) ≤ links w +
        (if R.Adj x w then 1 else 0) + (if B.Adj x w then 1 else 0) +
        (if R.Adj y w then 1 else 0) + (if B.Adj y w then 1 else 0) +
        (if good w then 1 else 0) := by
    by_cases hx : w = x
    · subst w
      simp [good, hr.symm, hb.symm]
      omega
    by_cases hy : w = y
    · subst w
      simp [good, hr, hb, hx]
    have hl := hpos hx hy
    simp only [if_neg hx, Nat.add_zero]
    by_cases h : good w
    · have hc := h
      rcases hc with ⟨a,b,c,d,e⟩
      simp [a,b,c,d,e,h]
    · split_ifs <;> simp_all [good]
      all_goals try omega
      have := hpos hx hy
      omega
  have s := Finset.sum_le_sum (s := Finset.univ) (fun w _ => local_bound w)
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, sum_adj] at s
  rw [Finset.sum_boole good] at s
  change _ ∧ _ ≤ _ + (Finset.univ.filter good).card
  simp only [Nat.cast_id] at s total
  constructor
  · omega
  · rw [Nat.mul_comm 2]
    exact s.trans (by gcongr)

/-- Deleting a chosen edge of a minimal counterexample gives a placement
with exactly that edge in common. -/
lemma critical_position (G B : SimpleGraph V) (hmin : Minimal (fun D => ¬Packs D B) G)
    {x y : V} (hxy : G.Adj x y) :
    ∃ σ : Equiv.Perm V, ¬Packs G (B.comap σ) ∧ (B.comap σ).Adj x y ∧
      ∀ a b, G.Adj a b → (B.comap σ).Adj a b → (a = x ∧ b = y) ∨ (a = y ∧ b = x) := by
  classical
  let D := G.deleteEdges ({s(x,y)} : Set (Sym2 V))
  have hlt : D < G := by
    refine lt_of_le_of_ne (G.deleteEdges_le _) ?_
    intro heq
    have hd : D.Adj x y := heq.symm ▸ hxy
    simp [D] at hd
  obtain ⟨σ, hσ⟩ := not_not.mp (hmin.not_prop_of_lt hlt)
  let C := B.comap σ
  have hn : ¬Packs G C := by
    rintro ⟨τ, ht⟩
    exact hmin.1 ⟨τ.trans σ, ht⟩
  have only : ∀ a b, G.Adj a b → C.Adj a b → (a = x ∧ b = y) ∨ (a = y ∧ b = x) := by
    intro a b hab hcab
    apply Sym2.eq_iff.mp
    by_contra he
    exact hσ a b ((SimpleGraph.deleteEdges_adj).mpr ⟨hab, he⟩) hcab
  refine ⟨σ, hn, ?_, only⟩
  by_contra h
  apply hn
  refine ⟨1, fun a b hab hcab => ?_⟩
  change C.Adj a b at hcab
  rcases only a b hab hcab with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact h hcab
  · exact h hcab.symm

lemma comap_degree [Fintype V] (B : SimpleGraph V) [DecidableRel B.Adj] (σ : Equiv.Perm V)
    [DecidableRel (B.comap σ).Adj] : (B.comap σ).maxDegree = B.maxDegree := by
  let iso := SimpleGraph.Iso.comap σ B
  exact le_antisymm iso.toCopy.maxDegree_mono iso.symm.toCopy.maxDegree_mono

lemma edge_of_nonpacking (G B : SimpleGraph V) (hn : ¬Packs G B) : ∃ x y, G.Adj x y := by
  by_contra! h
  exact hn ⟨1, fun a b ha => (h a b ha).elim⟩

/-- A component containing an edge in a finite forest supplies a degree-one vertex. -/
lemma forest_leaf [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hf : G.IsAcyclic)
    {u v : V} (huv : G.Adj u v) : ∃ x y, G.Adj x y ∧ G.degree x = 1 := by
  classical
  let c := G.connectedComponentMk u
  have hu : u ∈ c.supp := rfl
  have hv := c.mem_supp_of_adj_mem_supp hu huv
  let _ : Nontrivial c := ⟨⟨⟨u,hu⟩, ⟨v,hv⟩, fun h => huv.ne (congrArg Subtype.val h)⟩⟩
  obtain ⟨x, hx⟩ := (hf.isTree_connectedComponent c).exists_vert_degree_one_of_nontrivial
  obtain ⟨y, hxy, huniq⟩ := degree_eq_one_iff_existsUnique_adj.mp hx
  refine ⟨x.val, y.val, hxy, degree_eq_one_iff_existsUnique_adj.mpr ⟨y.val, hxy, ?_⟩⟩
  intro z hz
  exact congrArg Subtype.val (huniq ⟨z, c.mem_supp_of_adj_mem_supp x.prop hz⟩ hz)

/-- Unconditional forest case of the Bollobás–Eldridge–Catlin degree bound. -/
theorem packs_forest [Fintype V] [DecidableEq V] (R B : SimpleGraph V) [DecidableRel R.Adj] [DecidableRel B.Adj]
    (hf : R.IsAcyclic) (h : (R.maxDegree + 1) * (B.maxDegree + 1) ≤ Fintype.card V + 1) :
    Packs R B := by
  classical
  by_contra hn
  obtain ⟨G, hGR, hmin⟩ := exists_minimal_le_of_wellFoundedLT (fun D => ¬Packs D B) R hn
  obtain ⟨u,v,huv⟩ := edge_of_nonpacking G B hmin.1
  obtain ⟨x,y,hxy,hdeg⟩ := forest_leaf G (hf.anti hGR) huv
  obtain ⟨σ, hnp, hb, only⟩ := critical_position G B hmin hxy
  have cover := (clean_count G (B.comap σ) hxy hb only hnp).1
  have degB := (B.comap σ).degree_le_maxDegree x
  rw [comap_degree] at degB cover
  rw [hdeg, one_mul] at cover
  have pos : 1 ≤ R.maxDegree := hdeg ▸ (G.degree_le_maxDegree x).trans (maxDegree_mono hGR)
  have prod := Nat.mul_le_mul degB (maxDegree_mono hGR)
  rw [Nat.mul_comm B.maxDegree R.maxDegree] at prod
  simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one] at h
  omega

/-- The degree-two packing theorem of Aigner and Brandt (1993). -/
def H1 : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (R B : SimpleGraph V)
    [DecidableRel R.Adj] [DecidableRel B.Adj], R.maxDegree ≤ 2 →
    (R.maxDegree + 1) * (B.maxDegree + 1) ≤ Fintype.card V + 1 → Packs R B

/-- The remaining switching problem. The red endpoint x has least positive
degree. Each endpoint has at least two clean, singly linked alternatives,
with two further alternatives per vertex of slack in the degree bound. -/
def H2 : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (R B : SimpleGraph V)
    [DecidableRel R.Adj] [DecidableRel B.Adj] (x y : V),
    3 ≤ R.maxDegree → 3 ≤ B.maxDegree → ¬R.IsAcyclic → ¬B.IsAcyclic →
    (R.maxDegree + 1) * (B.maxDegree + 1) ≤ Fintype.card V + 1 →
    R.Adj x y → B.Adj x y →
    (∀ a b, R.Adj a b → R.degree x ≤ R.degree a) →
    (∀ a b, R.Adj a b → B.Adj a b → (a = x ∧ b = y) ∨ (a = y ∧ b = x)) →
    (∀ p q, (p = x ∧ q = y) ∨ (p = y ∧ q = x) →
      let links := fun w =>
        (∑ z ∈ R.neighborFinset p, if B.Adj z w then 1 else 0) +
        (∑ z ∈ B.neighborFinset p, if R.Adj z w then 1 else 0)
      let clean := Finset.univ.filter fun w =>
        ¬R.Adj p w ∧ ¬B.Adj p w ∧ ¬R.Adj q w ∧ ¬B.Adj q w ∧ links w = 1
      Fintype.card V ≤ R.degree p * B.maxDegree + B.degree p * R.maxDegree ∧
      2 + 2 * (Fintype.card V + 1 - (R.maxDegree + 1) * (B.maxDegree + 1)) ≤ clean.card) →
    Packs R B

lemma endpoint_bounds [Fintype V] [DecidableEq V] (R B : SimpleGraph V) [DecidableRel R.Adj] [DecidableRel B.Adj]
    {p q : V} (hr : R.Adj p q) (hb : B.Adj p q)
    (honly : ∀ a b, R.Adj a b → B.Adj a b → (a = p ∧ b = q) ∨ (a = q ∧ b = p))
    (hnp : ¬Packs R B)
    (bound : (R.maxDegree + 1) * (B.maxDegree + 1) ≤ Fintype.card V + 1) :
    let links := fun w =>
      (∑ z ∈ R.neighborFinset p, if B.Adj z w then 1 else 0) +
      (∑ z ∈ B.neighborFinset p, if R.Adj z w then 1 else 0)
    let clean := Finset.univ.filter fun w =>
      ¬R.Adj p w ∧ ¬B.Adj p w ∧ ¬R.Adj q w ∧ ¬B.Adj q w ∧ links w = 1
    Fintype.card V ≤ R.degree p * B.maxDegree + B.degree p * R.maxDegree ∧
    2 + 2 * (Fintype.card V + 1 - (R.maxDegree + 1) * (B.maxDegree + 1)) ≤ clean.card := by
  obtain ⟨h1, h2⟩ := clean_count R B hr hb honly hnp
  refine ⟨h1, ?_⟩
  dsimp only at h2 ⊢
  have prod₁ := Nat.mul_le_mul_right B.maxDegree (R.degree_le_maxDegree p)
  have prod₂ := Nat.mul_le_mul_right R.maxDegree (B.degree_le_maxDegree p)
  rw [Nat.mul_comm B.maxDegree R.maxDegree] at prod₂
  have hp := R.degree_le_maxDegree p
  have hq := R.degree_le_maxDegree q
  have hp' := B.degree_le_maxDegree p
  have hq' := B.degree_le_maxDegree q
  simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one] at bound ⊢
  omega

theorem main : H1 → H2 → type_of% @BollobasEldridgeCatlinConjecture.bollobas_eldridge_catlin_conjecture := by
  intro low high V _ _ R B
  classical
  intro _ _ original_bound
  by_contra hn
  obtain ⟨G, hGR, hminimal⟩ := exists_minimal_le_of_wellFoundedLT (fun D => ¬Packs D B) R hn
  have hnp := hminimal.1
  have bound := (Nat.mul_le_mul_right (B.maxDegree + 1)
    (Nat.add_le_add_right (maxDegree_mono hGR) 1)).trans original_bound
  by_cases hg : G.maxDegree ≤ 2
  · exact hnp (low G B hg bound)
  by_cases hb : B.maxDegree ≤ 2
  · exact hnp (low B G hb (by simpa only [Nat.mul_comm] using bound)).symm
  have edge := edge_of_nonpacking G B hnp
  let active := Finset.univ.filter fun a => ∃ b, G.Adj a b
  have hact : active.Nonempty := by
    obtain ⟨a,b,h⟩ := edge
    exact ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, b, h⟩⟩
  obtain ⟨x, hx, hmin⟩ := active.exists_min_image (fun t => G.degree t) hact
  obtain ⟨y, hxy⟩ := (Finset.mem_filter.mp hx).2
  obtain ⟨σ, hbad, blue, only⟩ := critical_position G B hminimal hxy
  let C := B.comap σ
  have same : C.maxDegree = B.maxDegree := comap_degree B σ
  have bc : (G.maxDegree + 1) * (C.maxDegree + 1) ≤ Fintype.card V + 1 := same ▸ bound
  have red_cycle : ¬G.IsAcyclic := fun h => hnp (packs_forest G B h bound)
  have blue_cycle : ¬C.IsAcyclic := fun h => hbad
    (packs_forest C G h (by simpa only [Nat.mul_comm] using bc)).symm
  apply hbad (high G C x y (by omega) (by omega) red_cycle blue_cycle bc hxy blue ?_ only ?_)
  · intro a b h
    exact hmin a (Finset.mem_filter.mpr ⟨Finset.mem_univ _, b, h⟩)
  · intro p q hpq
    rcases hpq with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact endpoint_bounds G C hxy blue only hbad bc
    · exact endpoint_bounds G C hxy.symm blue.symm
        (fun a b ha hb' => (only a b ha hb').symm) hbad bc

end OMA.R_BollobasEldridgeCatlinConjecture_bollobas_eldridge_catlin_conjecture_R1
