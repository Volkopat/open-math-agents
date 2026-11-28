import FormalConjectures.ErdosProblems.«1032»

/-! Joining two odd cycles gives the six-critical graphs. -/

open Filter SimpleGraph
open scoped SimpleGraph

namespace OMA

def diracJoin (m : ℕ) : SimpleGraph (Fin m ⊕ Fin m) where
  Adj
    | .inl u, .inl v => (cycleGraph m).Adj u v
    | .inr u, .inr v => (cycleGraph m).Adj u v
    | _, _ => True
  symm := ⟨by intro u v h; cases u <;> cases v <;> first | exact h.symm | exact h⟩
  loopless := ⟨by intro u h; cases u <;> exact (cycleGraph m).irrefl h⟩

lemma diracJoin_swapped {m : ℕ} {u v : Fin m ⊕ Fin m}
    (h : (diracJoin m).Adj u v) : (diracJoin m).Adj u.swap v.swap := by
  cases u <;> cases v <;> exact h

def diracParity {k : ℕ} (r u : Fin (k + 3)) : Fin 2 :=
  ⟨(u - r).val % 2, Nat.mod_lt _ (by decide)⟩

lemma diracCycle_step {k : ℕ} {u v : Fin (k + 3)}
    (hadj : (cycleGraph (k + 3)).Adj u v) : u + 1 = v ∨ v + 1 = u := by
  simpa [sub_eq_iff_eq_add, add_comm, eq_comm, or_comm] using
    (cycleGraph_adj (n := k + 1)).mp hadj

lemma diracParity_eq_of_step {k : ℕ} {r u v : Fin (k + 3)}
    (hstep : u + 1 = v) (heq : diracParity r u = diracParity r v) : v = r := by
  have hshift : v - r = (u - r) + 1 := by rw [← hstep]; abel
  have hval : (v-r).val = ((u-r).val+1) % (k+3) := by
    rw [hshift, Fin.val_add, Fin.val_one]
  have hpar : (u-r).val % 2 = (v-r).val % 2 := congrArg Fin.val heq
  by_cases h : (u-r).val+1 < k+3
  · rw [Nat.mod_eq_of_lt h] at hval
    omega
  have hw : (u-r).val+1 = k+3 := by have := (u-r).isLt; omega
  exact sub_eq_zero.mp (Fin.ext (by simp [hval,hw]))

lemma diracParity_collision {k : ℕ} {r u v : Fin (k + 3)}
    (hadj : (cycleGraph (k + 3)).Adj u v) (h : diracParity r u = diracParity r v) :
    (u + 1 = v ∧ v = r) ∨ (v + 1 = u ∧ u = r) :=
  (diracCycle_step hadj).imp (fun hs => ⟨hs, diracParity_eq_of_step hs h⟩)
    (fun hs => ⟨hs, diracParity_eq_of_step hs h.symm⟩)

lemma diracParity_valid_away {k : ℕ} {r u v : Fin (k + 3)} (hu : u ≠ r) (hv : v ≠ r)
    (hadj : (cycleGraph (k + 3)).Adj u v) : diracParity r u ≠ diracParity r v := by
  intro h
  exact (diracParity_collision hadj h).elim (fun hc => hv hc.2) (fun hc => hu hc.2)

lemma diracParity_valid_without_edge {k : ℕ} {a b u v : Fin (k + 3)} (hab : a + 1 = b)
    (hpair : s(u, v) ≠ s(a, b)) (hadj : (cycleGraph (k + 3)).Adj u v) :
    diracParity b u ≠ diracParity b v := by
  intro h
  rcases diracParity_collision hadj h with ⟨hstep, hv⟩ | ⟨hstep, hu⟩
  · have hu : u = a := add_right_cancel (hstep.trans (hv.trans hab.symm))
    exact hpair (Sym2.eq_iff.mpr (Or.inl ⟨hu, hv⟩))
  · have hv : v = a := add_right_cancel (hstep.trans (hu.trans hab.symm))
    exact hpair (Sym2.eq_iff.mpr (Or.inr ⟨hu, hv⟩))

lemma diracSumColors_ne {m p q : ℕ} {f : Fin m → Fin p} {g : Fin m → Fin q}
    {x y : Fin m ⊕ Fin m}
    (hl : ∀ u v, x = .inl u → y = .inl v → f u ≠ f v)
    (hr : ∀ u v, x = .inr u → y = .inr v → g u ≠ g v) :
    finSumFinEquiv (Sum.map f g x) ≠ finSumFinEquiv (Sum.map f g y) := by
  intro h
  have he := finSumFinEquiv.injective h
  cases x <;> cases y <;> simp_all

lemma diracJoin_chromatic (m : ℕ) (hm : 2 ≤ m) (hodd : Odd m) :
    (diracJoin m).chromaticNumber = 6 := by
  classical
  apply le_antisymm
  · let tri := cycleGraph.tricoloring m hm
    have h : (diracJoin m).Colorable 6 := by
      refine ⟨Coloring.mk (fun x => finSumFinEquiv (Sum.map tri tri x)) ?_⟩
      intro x y hadj
      apply diracSumColors_ne
      · rintro u v rfl rfl
        exact tri.valid hadj
      · rintro u v rfl rfl
        exact tri.valid hadj
    exact h.chromaticNumber_le
  · change ((6 : ℕ) : ℕ∞) ≤ (diracJoin m).chromaticNumber
    apply (le_chromaticNumber_iff_not_colorable (G := diracJoin m) (by decide)).mpr
    rintro ⟨C⟩
    have needThree (c : Fin m → Fin 5)
        (hc : ∀ u v, (cycleGraph m).Adj u v → c u ≠ c v) :
        3 ≤ (Finset.univ.image c).card := by
      let S := Finset.univ.image c
      let D : (cycleGraph m).Coloring S := Coloring.mk
        (fun u => ⟨c u, Finset.mem_image_of_mem _ (Finset.mem_univ u)⟩)
        (fun {u v} hadj h => hc u v hadj (congrArg Subtype.val h))
      have h := D.colorable.chromaticNumber_le
      rw [chromaticNumber_cycleGraph_of_odd m hm hodd, Fintype.card_coe] at h
      exact_mod_cast h
    let left := Finset.univ.image (fun u : Fin m => C (Sum.inl u))
    let right := Finset.univ.image (fun u : Fin m => C (Sum.inr u))
    have hl : 3 ≤ left.card := needThree _ (fun _ _ hadj => C.valid hadj)
    have hr : 3 ≤ right.card := needThree _ (fun _ _ hadj => C.valid hadj)
    have hd : Disjoint left right := by
      refine Finset.disjoint_left.mpr fun x hx hy => ?_
      obtain ⟨u, _, hu⟩ := Finset.mem_image.mp hx
      obtain ⟨v, _, hv⟩ := Finset.mem_image.mp hy
      have h : (diracJoin m).Adj (Sum.inl u) (Sum.inr v) := trivial
      exact C.valid h (hu.trans hv.symm)
    have hcard : (left ∪ right).card ≤ 5 := by simpa using Finset.card_le_univ (left ∪ right)
    rw [Finset.card_union_of_disjoint hd] at hcard
    omega

lemma diracColors_without_left_vertex {k : ℕ} (r : Fin (k + 3)) :
    ∃ f : (Fin (k + 3) ⊕ Fin (k + 3)) → Fin 5,
      ∀ x y, x ≠ .inl r → y ≠ .inl r → (diracJoin (k + 3)).Adj x y → f x ≠ f y := by
  let tri := cycleGraph.tricoloring (k + 3) (by omega)
  refine ⟨fun x => finSumFinEquiv (Sum.map (diracParity r) tri x), ?_⟩
  intro x y hx hy hadj
  apply diracSumColors_ne
  · rintro u v rfl rfl
    exact diracParity_valid_away (fun h => hx (congrArg Sum.inl h))
      (fun h => hy (congrArg Sum.inl h)) hadj
  · rintro u v rfl rfl
    exact tri.valid hadj

lemma diracColors_without_vertex {k : ℕ} (r : Fin (k + 3) ⊕ Fin (k + 3)) :
    ∃ f : (Fin (k + 3) ⊕ Fin (k + 3)) → Fin 5,
      ∀ x y, x ≠ r → y ≠ r → (diracJoin (k + 3)).Adj x y → f x ≠ f y := by
  cases r with
  | inl u => exact diracColors_without_left_vertex u
  | inr u =>
    obtain ⟨f, hf⟩ := diracColors_without_left_vertex u
    refine ⟨fun x => f x.swap, fun x y hx hy hadj => hf _ _ ?_ ?_ (diracJoin_swapped hadj)⟩
    · intro he
      exact hx (by simpa using congrArg Sum.swap he)
    · intro he
      exact hy (by simpa using congrArg Sum.swap he)

lemma diracColors_without_left_step {k : ℕ} {a b : Fin (k + 3)} (hab : a + 1 = b) :
    ∃ f : (Fin (k + 3) ⊕ Fin (k + 3)) → Fin 5, ∀ x y,
      s(x, y) ≠ s(Sum.inl a, Sum.inl b) →
      (diracJoin (k + 3)).Adj x y → f x ≠ f y := by
  let tri := cycleGraph.tricoloring (k + 3) (by omega)
  refine ⟨fun x => finSumFinEquiv (Sum.map (diracParity b) tri x), ?_⟩
  intro x y hpair hadj
  apply diracSumColors_ne
  · rintro u v rfl rfl
    apply diracParity_valid_without_edge hab _ hadj
    intro he
    exact hpair (congrArg (Sym2.map Sum.inl) he)
  · rintro u v rfl rfl
    exact tri.valid hadj

lemma diracColors_without_left_edge {k : ℕ} {a b : Fin (k + 3)}
    (hab : (cycleGraph (k + 3)).Adj a b) :
    ∃ f : (Fin (k + 3) ⊕ Fin (k + 3)) → Fin 5, ∀ x y,
      s(x, y) ≠ s(Sum.inl a, Sum.inl b) →
      (diracJoin (k + 3)).Adj x y → f x ≠ f y := by
  rcases diracCycle_step hab with h | h
  · exact diracColors_without_left_step h
  · obtain ⟨f, hf⟩ := diracColors_without_left_step h
    refine ⟨f, fun x y hx hadj => hf x y ?_ hadj⟩
    rwa [Sym2.eq_swap (a := Sum.inl b) (b := Sum.inl a)]

def diracMarkedParity {k : ℕ} {C : Type*} (e : Fin 2 ↪ C) (r u : Fin (k + 3)) :
    Option C := if u = r then none else some (e (diracParity r u))

lemma diracMarkedParity_valid {k : ℕ} {C : Type*} (e : Fin 2 ↪ C) (r : Fin (k + 3))
    {u v : Fin (k + 3)} (h : (cycleGraph (k + 3)).Adj u v) :
    diracMarkedParity e r u ≠ diracMarkedParity e r v := by
  intro he
  by_cases hu : u = r <;> by_cases hv : v = r <;> simp [diracMarkedParity, hu, hv] at he
  · exact h.ne (hu.trans hv.symm)
  · exact diracParity_valid_away hu hv h he


lemma diracColors_without_cross_edge {k : ℕ} (a b : Fin (k + 3)) :
    ∃ f : (Fin (k + 3) ⊕ Fin (k + 3)) → Fin 5, ∀ x y,
      s(x, y) ≠ s(Sum.inl a, Sum.inr b) →
      (diracJoin (k + 3)).Adj x y → f x ≠ f y := by
  let left := diracMarkedParity (Function.Embedding.inl : Fin 2 ↪ Fin 2 ⊕ Fin 2) a
  let right := diracMarkedParity (Function.Embedding.inr : Fin 2 ↪ Fin 2 ⊕ Fin 2) b
  let e : Option (Fin 2 ⊕ Fin 2) ≃ Fin 5 := Fintype.equivFinOfCardEq (by decide)
  have heq (u v : Fin (k + 3)) (h : left u = right v) : u = a ∧ v = b := by
    by_cases hu : u = a <;> by_cases hv : v = b <;> simp_all [left, right, diracMarkedParity]
  refine ⟨fun x => e (Sum.elim left right x), ?_⟩
  intro x y hpair hadj h
  have he := e.injective h
  cases x with
  | inl u =>
    cases y with
    | inl v => exact diracMarkedParity_valid _ _ hadj he
    | inr v =>
      obtain ⟨rfl, rfl⟩ := heq u v he
      exact hpair rfl
  | inr u =>
    cases y with
    | inl v =>
      obtain ⟨rfl, rfl⟩ := heq v u he.symm
      exact hpair Sym2.eq_swap
    | inr v => exact diracMarkedParity_valid _ _ hadj he

lemma diracColors_without_edge {k : ℕ} {a b : Fin (k + 3) ⊕ Fin (k + 3)}
    (hab : (diracJoin (k + 3)).Adj a b) :
    ∃ f : (Fin (k + 3) ⊕ Fin (k + 3)) → Fin 5, ∀ x y,
      s(x, y) ≠ s(a, b) → (diracJoin (k + 3)).Adj x y → f x ≠ f y := by
  cases a with
  | inl u =>
    cases b with
    | inl v => exact diracColors_without_left_edge hab
    | inr v => exact diracColors_without_cross_edge u v
  | inr u =>
    cases b with
    | inl v =>
      obtain ⟨f, hf⟩ := diracColors_without_cross_edge v u
      refine ⟨f, fun x y hx hadj => hf x y ?_ hadj⟩
      rwa [Sym2.eq_swap (a := Sum.inl v) (b := Sum.inr u)]
    | inr v =>
      obtain ⟨f, hf⟩ := diracColors_without_left_edge (a := u) (b := v) hab
      refine ⟨fun x => f x.swap, fun x y hx hadj => hf _ _ ?_ (diracJoin_swapped hadj)⟩
      intro h
      exact hx (by simpa using congrArg (Sym2.map Sum.swap) h)

open scoped Classical in
lemma diracJoin_minDegree (k : ℕ) : k + 4 ≤ (diracJoin (k + 3)).minDegree := by
  classical
  apply le_minDegree_of_forall_le_degree
  intro x
  let nbr : (Fin (k + 3) ⊕ Unit) → Fin (k + 3) ⊕ Fin (k + 3)
    | .inl v =>
      match x with
      | .inl _ => .inr v
      | .inr _ => .inl v
    | .inr _ =>
      match x with
      | .inl u => .inl (u + 1)
      | .inr u => .inr (u + 1)
  have hstep (u : Fin (k + 3)) : (cycleGraph (k + 3)).Adj u (u + 1) :=
    (cycleGraph_adj (n := k + 1)).mpr (Or.inr (by simp))
  have hAdj (z : Fin (k + 3) ⊕ Unit) : (diracJoin (k + 3)).Adj x (nbr z) := by
    cases x <;> cases z <;> first | trivial | exact hstep _
  have hnbr : Function.Injective nbr := by
    intro u v h
    cases x <;> cases u <;> cases v <;> simp_all [nbr]
  let e : (Fin (k + 3) ⊕ Unit) ↪ (diracJoin (k + 3)).neighborSet x :=
    ⟨fun z => ⟨nbr z, hAdj z⟩, fun _ _ h => hnbr (congrArg Subtype.val h)⟩
  have h := Fintype.card_le_of_embedding e
  rw [← card_neighborSet_eq_degree]
  simpa only [Fintype.card_sum, Fintype.card_fin, Fintype.card_unit] using h

lemma diracJoin_comap_critical {V : Type*} {k : ℕ}
    (e : V ≃ (Fin (k + 3) ⊕ Fin (k + 3))) (hodd : Odd (k + 3)) :
    Erdos1032.IsKCritical ((diracJoin (k + 3)).comap e) 6 := by
  let G := (diracJoin (k + 3)).comap e
  let iso : G ≃g diracJoin (k + 3) := SimpleGraph.Iso.comap e _
  have hχ : G.chromaticNumber = 6 :=
    (SimpleGraph.chromaticNumber_congr iso).trans (diracJoin_chromatic _ (by omega) hodd)
  change Erdos1032.IsKCritical G 6
  refine ⟨⟨hχ, ?_⟩, ?_⟩
  · intro r
    let S := (⊤ : G.Subgraph).deleteVerts ({r} : Set V)
    change S.coe.chromaticNumber < (⊤ : G.Subgraph).coe.chromaticNumber
    rw [SimpleGraph.chromaticNumber_congr (SimpleGraph.Subgraph.topIso (G := G)), hχ]
    obtain ⟨f, hf⟩ := diracColors_without_vertex (iso r)
    have hcol : S.coe.Colorable 5 := by
      refine ⟨Coloring.mk (fun x => f (iso x.val)) ?_⟩
      intro u v hadj
      have hp (x : S.verts) : iso x.val ≠ iso r := by
        have hx := x.property
        simp only [S, Subgraph.deleteVerts_verts, Set.mem_sdiff, Set.mem_singleton_iff] at hx
        exact fun h => hx.2 (iso.injective h)
      exact hf _ _ (hp u) (hp v) (iso.toHom.map_adj (S.coe_adj_sub _ _ hadj))
    exact hcol.chromaticNumber_le.trans_lt (by decide)
  · refine Sym2.ind fun a b hmem => ?_
    change (G.deleteEdges ({s(a, b)} : Set (Sym2 V))).chromaticNumber < G.chromaticNumber
    rw [hχ]
    obtain ⟨f, hf⟩ := diracColors_without_edge (iso.toHom.map_adj (show G.Adj a b from hmem))
    have hcol : (G.deleteEdges ({s(a, b)} : Set (Sym2 V))).Colorable 5 := by
      refine ⟨Coloring.mk (fun x => f (iso x)) ?_⟩
      intro u v hadj
      obtain ⟨hAdj, hne⟩ := deleteEdges_adj.mp hadj
      apply hf _ _ _ (iso.toHom.map_adj hAdj)
      intro he
      exact hne (Set.mem_singleton_iff.mpr (Sym2.map.injective iso.injective he))
    exact hcol.chromaticNumber_le.trans_lt (by decide)

end OMA

theorem OMA.solution : type_of% @Erdos1032.erdos_1032.variants.dirac_six := by
  classical
  refine frequently_atTop.mpr fun N => ?_
  let k := 2 * N
  let m := k + 3
  let n := m + m
  let e : Fin n ≃ (Fin m ⊕ Fin m) := finSumFinEquiv.symm
  let G := (OMA.diracJoin m).comap e
  let iso : G ≃g OMA.diracJoin m := SimpleGraph.Iso.comap e _
  have hodd : Odd m := ⟨N + 1, by dsimp [m, k]; omega⟩
  refine ⟨n, by dsimp [n, m, k]; omega, G, OMA.diracJoin_comap_critical e hodd, ?_⟩
  have hlo : k + 4 ≤ G.minDegree := by
    rw [iso.minDegree_eq]
    exact OMA.diracJoin_minDegree k
  have hR : (k : ℝ) + 4 ≤ (G.minDegree : ℝ) := by exact_mod_cast hlo
  calc
    (n : ℝ) / 2 = (k : ℝ) + 3 := by simp only [n, m, Nat.cast_add, Nat.cast_ofNat]; ring
    _ < (k : ℝ) + 4 := by linarith
    _ ≤ (G.minDegree : ℝ) := hR
