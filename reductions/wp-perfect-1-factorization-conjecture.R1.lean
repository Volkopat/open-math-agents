import OMAStatements.S_wp_perfect_1_factorization_conjecture

-- Reduction wp-perfect-1-factorization-conjecture.R1 of Perfect 1-factorization conjecture
-- Credit: @Pixelstorm44
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

namespace OMA.R_wp_perfect_1_factorization_conjecture_R1

open SimpleGraph
open scoped BigOperators

/-- Count one rooted matching by grouping the remaining vertices according to their
membership in the prescribed cuts. Every group must be paired internally. -/
def H1 : Prop := by
  classical
  exact ∀ (m : ℕ) (c : Fin m) (D : Finset (Finset (Fin (m+1)))),
    let V := Fin (m+1)
    let P := {M : (completeGraph V).Subgraph // M.IsPerfectMatching ∧ M.Adj (Fin.last m) c.castSucc}
    let weight (c : Fin m) (D : Finset (Finset V)) : ℕ :=
      let rem := (Finset.univ.erase (Fin.last m)).erase c.castSucc
      let sig := fun v : V => D.filter (v ∈ ·)
      if sig (Fin.last m) ≠ sig c.castSucc then 0 else
        ∏ s ∈ rem.image sig, let k := (rem.filter (sig · = s)).card
                             if Even k then Nat.doubleFactorial (k - 1) else 0
    (Finset.univ.filter (fun M : P => ∀ S ∈ D, ∀ x ∈ S, ∀ y, M.val.Adj x y → y ∈ S)).card =
      weight c D

/-- Strict positivity of a signed sum of products of double factorials. The terms
are indexed entirely by pairs of colors and vertex subsets. -/
def H2 : Prop := by
  classical
  exact ∀ n : ℕ,
    let m := 2*n+1
    let V := Fin (m+1)
    let weight (c : Fin m) (D : Finset (Finset V)) : ℕ :=
      let rem := (Finset.univ.erase (Fin.last m)).erase c.castSucc
      let sig := fun v : V => D.filter (v ∈ ·)
      if sig (Fin.last m) ≠ sig c.castSucc then 0 else
        ∏ s ∈ rem.image sig, let k := (rem.filter (sig · = s)).card
                             if Even k then Nat.doubleFactorial (k - 1) else 0
    let E := (Finset.univ : Finset (Fin m × Fin m × Finset V)).filter
      fun (i,j,S) => i < j ∧ S.Nonempty ∧ Fin.last m ∉ S
    let cuts := fun (T : Finset (Fin m × Fin m × Finset V)) (c : Fin m) =>
      (T.filter (fun e => e.1 = c ∨ e.2.1 = c)).image (fun e => e.2.2)
    0 < ∑ T ∈ E.powerset, (-1 : ℤ)^T.card * ∏ c, (weight c (cuts T c) : ℤ)

/-- Two matchings with distinct root partners form one alternating cycle if
they preserve no common nonempty vertex subset away from the root. -/
lemma cycle_of_no_common_cut : ∀ (m : ℕ) (i j : Fin m), i ≠ j →
  ∀ A B : (completeGraph (Fin (m+1))).Subgraph, A.IsPerfectMatching → B.IsPerfectMatching →
    A.Adj (Fin.last m) i.castSucc → B.Adj (Fin.last m) j.castSucc →
    (∀ S : Finset (Fin (m+1)), S.Nonempty → Fin.last m ∉ S →
      ¬ ((∀ x ∈ S, ∀ y, A.Adj x y → y ∈ S) ∧ (∀ x ∈ S, ∀ y, B.Adj x y → y ∈ S))) →
    Disjoint A.edgeSet B.edgeSet ∧ (A ⊔ B).spanningCoe.IsHamiltonian := by
  classical
  intro m i j hij A B hA hB hAi hBj avoid
  let root := Fin.last m
  let G := (A ⊔ B).spanningCoe
  have oneA := Subgraph.isPerfectMatching_iff.mp hA
  have oneB := Subgraph.isPerfectMatching_iff.mp hB
  have rootDistinct (x : Fin (m+1)) (ha : A.Adj root x) (hb : B.Adj root x) : False :=
    hij (Fin.castSucc_injective _ ((oneA root).unique hAi ha |>.trans ((oneB root).unique hb hBj)))
  have shared {x y : Fin (m+1)} (ha : A.Adj x y) (hb : B.Adj x y) : False := by
    have hx : root ≠ x := fun e => rootDistinct y (e ▸ ha) (e ▸ hb)
    have hy : root ≠ y := fun e => rootDistinct x (e ▸ A.adj_symm ha) (e ▸ B.adj_symm hb)
    have closedPair (M : (completeGraph (Fin (m+1))).Subgraph) (hm : M.IsPerfectMatching)
        (hxy : M.Adj x y) : ∀ u ∈ ({x,y} : Finset _), ∀ v, M.Adj u v → v ∈ ({x,y} : Finset _) := by
      intro u hu v hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu ⊢
      rcases hu with rfl | rfl
      · exact Or.inr ((Subgraph.isPerfectMatching_iff.mp hm _).unique hv hxy)
      · exact Or.inl ((Subgraph.isPerfectMatching_iff.mp hm _).unique hv (M.adj_symm hxy))
    exact avoid {x,y} (by simp) (by simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using And.intro hx hy) ⟨closedPair A hA ha, closedPair B hB hb⟩
  constructor
  · apply Set.disjoint_left.mpr
    intro e
    induction e using Sym2.inductionOn with
    | _ x y => exact fun ha hb => shared ha hb
  · let C := G.connectedComponentMk root
    have spans (x : Fin (m+1)) : x ∈ C.supp := by
      by_contra hx
      let S := C.suppᶜ.toFinset
      have hS : S.Nonempty := ⟨x, by simpa [S] using hx⟩
      have hr : root ∉ S := by simp [S, C, ConnectedComponent.mem_supp_iff]
      have stable {v w} (hv : v ∈ S) (hadj : G.Adj v w) : w ∈ S := by
        simp only [S, Set.mem_toFinset, Set.mem_compl_iff] at hv ⊢
        exact fun hw => hv ((C.mem_supp_congr_adj hadj).mpr hw)
      exact avoid S hS hr ⟨fun _ hv _ h => stable hv (Or.inl h), fun _ hv _ h => stable hv (Or.inr h)⟩
    have cycles : G.IsCycles := by
      intro v _
      obtain ⟨a, ha, ua⟩ := oneA v
      obtain ⟨b, hb, ub⟩ := oneB v
      have hs : G.neighborSet v = {a,b} := by
        ext w
        change (A.Adj v w ∨ B.Adj v w) ↔ w = a ∨ w = b
        exact ⟨fun h => h.imp (ua w) (ub w), fun h => h.elim (fun e => Or.inl (e ▸ ha)) (fun e => Or.inr (e ▸ hb))⟩
      rw [hs]
      exact Set.ncard_pair fun e => shared ha (e ▸ hb)
    obtain ⟨p, hp, hverts⟩ := cycles.exists_cycle_toSubgraph_verts_eq_connectedComponentSupp
      (spans root) ⟨i.castSucc, Or.inl hAi⟩
    intro _
    refine ⟨root, p, hp, hp.isPath_tail.isHamiltonian_of_mem ?_⟩
    intro x
    have hx : x ∈ p.support := p.mem_verts_toSubgraph.mp (hverts ▸ spans x)
    rw [← Walk.cons_support_tail hp.not_nil, List.mem_cons] at hx
    exact hx.elim (fun e => e ▸ p.tail.end_mem_support) id

lemma mem_fold {α ι : Type*} [Fintype α] [DecidableEq α] (s : Finset ι)
    (f : ι → Finset α) (x : α) : x ∈ s.inf f ↔ ∀ i ∈ s, x ∈ f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => simp [Finset.inf_insert, ih]

theorem main : H1 → H2 → type_of% @OMA.S_wp_perfect_1_factorization_conjecture.main := by
  classical
  intro count positive n
  cases n with
  | zero =>
    refine ⟨Empty, Empty.elim, fun i => i.elim, fun i => i.elim, ?_, fun i => i.elim⟩
    intro e
    induction e using Sym2.inductionOn with
    | _ x y => exact Fin.elim0 x
  | succ n =>
    let m := 2*n+1
    let V := Fin (m+1)
    let P := fun c : Fin m => {M : (completeGraph V).Subgraph //
      M.IsPerfectMatching ∧ M.Adj (Fin.last m) c.castSucc}
    let F := (c : Fin m) → P c
    let closed := fun (M : (completeGraph V).Subgraph) (S : Finset V) =>
      ∀ x ∈ S, ∀ y, M.Adj x y → y ∈ S
    let weight (c : Fin m) (D : Finset (Finset V)) : ℕ :=
      let rem := (Finset.univ.erase (Fin.last m)).erase c.castSucc
      let sig := fun v : V => D.filter (v ∈ ·)
      if sig (Fin.last m) ≠ sig c.castSucc then 0 else
        ∏ s ∈ rem.image sig, let k := (rem.filter (sig · = s)).card
                             if Even k then Nat.doubleFactorial (k - 1) else 0
    let E := (Finset.univ : Finset (Fin m × Fin m × Finset V)).filter
      fun (i,j,S) => i < j ∧ S.Nonempty ∧ Fin.last m ∉ S
    let cuts := fun (T : Finset (Fin m × Fin m × Finset V)) (c : Fin m) =>
      (T.filter (fun e => e.1 = c ∨ e.2.1 = c)).image (fun e => e.2.2)
    let bad := fun (e : Fin m × Fin m × Finset V) =>
      Finset.univ.filter fun f : F => closed (f e.1).val e.2.2 ∧ closed (f e.2.1).val e.2.2
    let options := fun (T : Finset (Fin m × Fin m × Finset V)) (c : Fin m) =>
      Finset.univ.filter fun p : P c => ∀ S ∈ cuts T c, closed p.val S
    have factor (T : Finset (Fin m × Fin m × Finset V)) :
        T.inf bad = Fintype.piFinset (options T) := by
      ext f
      rw [Fintype.mem_piFinset (t := options T) (f := f)]
      simp only [mem_fold, bad, options, Finset.mem_filter, Finset.mem_univ, true_and,
        cuts, Finset.mem_image]
      constructor
      · intro h c S ⟨e, ⟨he, hc⟩, hS⟩
        subst S
        rcases hc with hc | hc
        · subst c
          exact (h e he).1
        · subst c
          exact (h e he).2
      · intro h e he
        exact ⟨h e.1 _ ⟨e, ⟨he, Or.inl rfl⟩, rfl⟩, h e.2.1 _ ⟨e, ⟨he, Or.inr rfl⟩, rfl⟩⟩
    have hpos := positive n
    change 0 < ∑ T ∈ E.powerset, (-1 : ℤ)^T.card * ∏ c, (weight c (cuts T c) : ℤ) at hpos
    have optCard (T) (c) : (options T c).card = weight c (cuts T c) := count m c (cuts T c)
    have total := Finset.inclusion_exclusion_card_inf_compl E bad
    have term (T) : ((T.inf bad).card : ℤ) = ∏ c, (weight c (cuts T c) : ℤ) := by
      rw [factor T, Fintype.card_piFinset (options T), Nat.cast_prod]
      simp only [optCard]
    simp only [term] at total
    rw [← total] at hpos
    obtain ⟨f, hf⟩ := Finset.card_pos.mp (show 0 < (E.inf (fun e => (bad e)ᶜ)).card by exact_mod_cast hpos)
    have avoid (i j : Fin m) (hij : i < j) (S : Finset V) (hs : S.Nonempty) (hr : Fin.last m ∉ S) :
        ¬ (closed (f i).val S ∧ closed (f j).val S) := by
      have he : (i,j,S) ∈ E := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij, hs, hr⟩
      simpa [bad] using (mem_fold _ _ _).mp hf (i,j,S) he
    have pair (i j : Fin m) (hij : i ≠ j) := cycle_of_no_common_cut m i j hij (f i).val (f j).val
      (f i).property.1 (f j).property.1 (f i).property.2 (f j).property.2 (by
        intro S hs hr
        rcases lt_or_gt_of_ne hij with h | h
        · exact avoid i j h S hs hr
        · exact fun hS => avoid j i h S hs hr hS.symm)
    refine ⟨Fin m, fun c => (f c).val, fun c => (f c).property.1,
      fun i j h => (pair i j h).1, ?_, fun i j h => (pair i j h).2⟩
    intro e
    induction e using Sym2.inductionOn with
    | _ x y =>
      intro he
      have hxy : x ≠ y := he
      have one (c : Fin m) := (Subgraph.isPerfectMatching_iff.mp (f c).property.1 x).exists
      let mate (c : Fin m) : {v : V // v ≠ x} := ⟨(one c).choose,
        (Subgraph.Adj.ne (one c).choose_spec).symm⟩
      have inj : Function.Injective mate := by
        intro i j h
        by_contra hij
        have eqv := congrArg Subtype.val h
        change (one i).choose = (one j).choose at eqv
        exact Set.disjoint_left.mp (pair i j hij).1
          (show s(x, (one i).choose) ∈ (f i).val.edgeSet from (one i).choose_spec)
          (show (f j).val.Adj x (one i).choose from eqv ▸ (one j).choose_spec)
      have bij := (Fintype.bijective_iff_injective_and_card mate).mpr ⟨inj, by simp [V]⟩
      obtain ⟨c, hc⟩ := bij.surjective ⟨y, hxy.symm⟩
      have eqy : (one c).choose = y := congrArg Subtype.val hc
      exact ⟨c, (show (f c).val.Adj x y from eqy ▸ (one c).choose_spec)⟩

end OMA.R_wp_perfect_1_factorization_conjecture_R1
