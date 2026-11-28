import OMAStatements.S_wp_1_factorization_conjecture

-- Reduction wp-1-factorization-conjecture.R1 of 1-factorization conjecture
-- Credit: @PandaWill
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
-- A k-regular graph is 1-factorable iff its edges have a proper k-colouring (proved below: every colour
-- class is a perfect matching). Proved here outright, for every n:
--   k = 2n - 1 (the complete graph K_2n): the round-robin colouring {x,y} ↦ (x+y)/2 mod 2n-1, {x,∞} ↦ x;
--   k = 2n - 2 (K_2n minus a perfect matching): the missing matching and a colour class of the round robin
--       are fixed-point-free involutions, hence conjugate (same cycle type), and relabelling the round robin
--       by the conjugating permutation puts the missing matching on colour 0.
-- What is left:
--   H1: the dense range 12n/7 ≤ k ≤ 2n - 3, a known theorem (Chetwynd–Hilton 1985, "Regular graphs of high
--       degree are 1-factorizable", Proc. LMS 50, 193–206).
--   k = 1 (a perfect matching is its own colour class).
--   H2: the open middle range of the conjecture, n (or n - 1) ≤ k < 12n/7, with 2 ≤ k ≤ 2n - 3 (so n ≥ 3). Proved for all sufficiently
--       large n by Csaba–Kühn–Lo–Osthus–Treglown (Mem. AMS 2016), open in general.

namespace OMA.R_wp_1_factorization_conjecture_R1

open SimpleGraph

def H1 : Prop :=
  ∀ n k : ℕ, 12 * n ≤ 7 * k → k + 3 ≤ 2 * n →
    ∀ (G : SimpleGraph (Fin (2 * n))) [DecidableRel G.Adj],
      G.IsRegularOfDegree k → Nonempty (G.lineGraph.Coloring (Fin k))

def H2 : Prop :=
  ∀ n k : ℕ, ((Odd n ∧ n ≤ k) ∨ (Even n ∧ n - 1 ≤ k)) → 7 * k < 12 * n → 2 ≤ k → k + 3 ≤ 2 * n →
    ∀ (G : SimpleGraph (Fin (2 * n))) [DecidableRel G.Adj],
      G.IsRegularOfDegree k → Nonempty (G.lineGraph.Coloring (Fin k))

lemma factorable_of_coloring {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (k : ℕ) (hG : G.IsRegularOfDegree k) (c : G.lineGraph.Coloring (Fin k)) :
    OMA.S_wp_1_factorization_conjecture.IsOneFactorable G := by
  classical
  let col : ∀ v w, G.Adj v w → Fin k := fun v w h => c ⟨s(v, w), h⟩
  have colsymm : ∀ v w (h : G.Adj v w), col w v h.symm = col v w h := by
    intro v w h; simp only [col, Sym2.eq_swap]
  let M : Fin k → G.Subgraph := fun i =>
    { verts := Set.univ
      Adj := fun v w => ∃ h : G.Adj v w, col v w h = i
      adj_sub := fun ⟨h, _⟩ => h
      edge_vert := fun _ => Set.mem_univ _
      symm := ⟨fun v w ⟨h, e⟩ => ⟨h.symm, (colsymm v w h).trans e⟩⟩ }
  -- the colours at a vertex are distinct
  have inj : ∀ v w w' (h : G.Adj v w) (h' : G.Adj v w'), col v w h = col v w' h' → w = w' := by
    intro v w w' h h' e
    by_contra hne
    have hadj : G.lineGraph.Adj ⟨s(v, w), h⟩ ⟨s(v, w'), h'⟩ := by
      rw [lineGraph_adj_iff_exists]
      refine ⟨?_, v, Sym2.mem_mk_left _ _, Sym2.mem_mk_left _ _⟩
      intro heq
      have := congrArg Subtype.val heq
      simp only [Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk] at this
      rcases this with ⟨-, h2⟩ | ⟨h1, h2⟩
      · exact hne h2
      · exact hne (h2.trans h1)
    exact c.valid hadj e
  refine ⟨Fin k, M, ?_, ?_, ?_⟩
  · intro i
    rw [Subgraph.isPerfectMatching_iff]
    intro v
    let f : ∀ w, w ∈ G.neighborFinset v → Fin k := fun w hw => col v w ((mem_neighborFinset _ _ _).1 hw)
    obtain ⟨w, hw, e⟩ := Finset.surj_on_of_inj_on_of_card_le f (fun _ _ => Finset.mem_univ _)
      (fun a b ha hb hab => inj v a b _ _ hab) (by simp [card_neighborFinset_eq_degree, hG v]) i
      (Finset.mem_univ _)
    refine ⟨w, ⟨(mem_neighborFinset _ _ _).1 hw, e.symm⟩, ?_⟩
    rintro y ⟨hy, ey⟩
    exact inj v y w hy _ (ey.trans e)
  · intro i j hij
    rw [Set.disjoint_left]
    intro e
    induction e using Sym2.ind with
    | _ v w =>
      simp only [Subgraph.mem_edgeSet]
      rintro ⟨h, hi⟩ ⟨h', hj⟩
      exact hij (hi.symm.trans hj)
  · intro e he
    induction e using Sym2.ind with
    | _ v w => exact ⟨col v w he, by simp only [Subgraph.mem_edgeSet]; exact ⟨he, rfl⟩⟩

lemma rr (j : ℕ) : ∃ (c : Option (ZMod (2*j+1)) → Option (ZMod (2*j+1)) → ZMod (2*j+1))
    (τ : Option (ZMod (2*j+1)) → Option (ZMod (2*j+1))),
    (∀ x y, c x y = c y x) ∧ (∀ v y z, v ≠ y → v ≠ z → c v y = c v z → y = z) ∧
    (∀ y, τ (τ y) = y) ∧ (∀ y, τ y ≠ y) ∧ (∀ y, c y (τ y) = 0) ∧
    (∀ y z, y ≠ z → c y z = 0 → z = τ y) := by
  let h : ZMod (2*j+1) := ((j+1 : ℕ) : ZMod (2*j+1))
  have h2 : 2 * h = 1 := by
    have : ((2*j+1 : ℕ) : ZMod (2*j+1)) = 0 := ZMod.natCast_self _
    simp only [h]; push_cast at this ⊢; linear_combination this
  have cancel : ∀ a b : ZMod (2*j+1), h * a = h * b → a = b := fun a b e => by
    have := congrArg (2 * ·) e; simpa only [← mul_assoc, h2, one_mul] using this
  have dbl : ∀ a : ZMod (2*j+1), h * (a + a) = a := fun a => by
    rw [← two_mul, ← mul_assoc, mul_comm h 2, h2, one_mul]
  refine ⟨fun x y => match x, y with
      | none, none => 0 | none, some y => y | some x, none => x | some x, some y => h * (x + y),
    fun x => match x with | none => some 0 | some x => if x = 0 then none else some (-x),
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro (_|x) (_|y) <;> simp [add_comm]
  · rintro (_|v) (_|y) (_|z) hvy hvz e <;> simp only [ne_eq, reduceCtorEq, not_false_eq_true,
      Option.some.injEq, not_true_eq_false] at hvy hvz e ⊢
    · exact e
    · exact hvz (add_left_cancel (cancel _ _ (by rw [dbl]; exact e)))
    · exact hvy (add_left_cancel (cancel _ _ (by rw [dbl]; exact e.symm)))
    · exact add_left_cancel (cancel _ _ e)
  · rintro (_|x)
    · simp
    · by_cases hx : x = 0 <;> simp [hx]
  · rintro (_|x)
    · simp
    · by_cases hx : x = 0
      · simp [hx]
      · simp only [hx, if_false, ne_eq, Option.some.injEq]
        intro e; apply hx
        have : x + x = 0 := by linear_combination -e
        rw [← dbl x, this, mul_zero]
  · rintro (_|x)
    · simp
    · by_cases hx : x = 0 <;> simp [hx]
  · rintro (_|y) (_|z) hyz e <;> simp only [ne_eq, reduceCtorEq, not_false_eq_true,
      Option.some.injEq, not_true_eq_false] at hyz e ⊢
    · simp [e]
    · simp [e]
    · have hs : y + z = 0 := cancel _ _ (by rw [e, mul_zero])
      by_cases hy : y = 0
      · subst hy; simp at hs; exact (hyz hs.symm).elim
      · rw [if_neg hy, Option.some.injEq]; linear_combination hs

lemma coloring_of_pair {V α : Type*} (G : SimpleGraph V) (c : V → V → α) (hs : ∀ x y, c x y = c y x)
    (hc : ∀ v y z, G.Adj v y → G.Adj v z → c v y = c v z → y = z) :
    Nonempty (G.lineGraph.Coloring α) := by
  refine ⟨Coloring.mk (fun e => Sym2.lift ⟨c, hs⟩ e.val) ?_⟩
  rintro ⟨e1, h1⟩ ⟨e2, h2⟩ hadj heq
  rw [lineGraph_adj_iff_exists] at hadj
  obtain ⟨hne, v, hv1, hv2⟩ := hadj
  obtain ⟨y, rfl⟩ := Sym2.mem_iff_exists.1 hv1
  obtain ⟨z, rfl⟩ := Sym2.mem_iff_exists.1 hv2
  simp only [Sym2.lift_mk] at heq
  obtain rfl := hc v y z h1 h2 heq
  exact hne rfl

lemma coloring_fin {V α : Type*} [Fintype α] (G : SimpleGraph V) {k : ℕ} (hk : Fintype.card α = k)
    (h : Nonempty (G.Coloring α)) : Nonempty (G.Coloring (Fin k)) := by
  obtain ⟨c⟩ := h
  let e := Fintype.equivFinOfCardEq hk
  exact ⟨Coloring.mk (fun v => e (c v)) (fun hvw h => c.valid hvw (e.injective h))⟩

lemma cycleType_fpf {α : Type*} [Fintype α] [DecidableEq α] (σ : Equiv.Perm α) (N : ℕ)
    (hinv : ∀ x, σ (σ x) = x) (hfp : ∀ x, σ x ≠ x) (hc : Fintype.card α = 2 * N) (hN : 1 ≤ N) :
    σ.cycleType = Multiset.replicate N 2 := by
  have hne : Nonempty α := Fintype.card_pos_iff.1 (by omega)
  have ho : orderOf σ = 2 := by
    apply orderOf_eq_prime
    · ext x; simp [sq, hinv]
    · intro h1; obtain ⟨x⟩ := hne; exact hfp x (by simp [h1])
  obtain ⟨a, ha⟩ := Equiv.Perm.cycleType_prime_order (ho ▸ Nat.prime_two)
  have hs := Equiv.Perm.sum_cycleType σ
  have hsup : σ.support = Finset.univ := Finset.eq_univ_iff_forall.2 fun x => by simp [hfp x]
  rw [ha, hsup, Finset.card_univ, hc, ho, Multiset.sum_replicate, smul_eq_mul] at hs
  rw [ha, ho]; congr 1; omega

lemma top_case {V : Type*} [Fintype V] (G : SimpleGraph V) (j : ℕ) (hV : Fintype.card V = 2 * j + 2) :
    Nonempty (G.lineGraph.Coloring (Fin (2 * j + 1))) := by
  obtain ⟨c, τ, hs, hc, -⟩ := rr j
  let E : V ≃ Option (ZMod (2*j+1)) := Fintype.equivOfCardEq (by simp [hV, ZMod.card])
  exact coloring_fin _ (by simp [ZMod.card]) (coloring_of_pair G (fun x y => c (E x) (E y))
    (fun x y => hs _ _) (fun v y z hy hz e =>
      E.injective (hc _ _ _ (E.injective.ne hy.ne) (E.injective.ne hz.ne) e)))

lemma second_case {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (j : ℕ) (hj : 1 ≤ j) (hV : Fintype.card V = 2 * j + 2) (hG : G.IsRegularOfDegree (2 * j)) :
    Nonempty (G.lineGraph.Coloring (Fin (2 * j))) := by
  obtain ⟨c, τ, hs, hc, hτ, hτf, hτ0, h0τ⟩ := rr j
  -- the unique non-neighbour
  have h1 : ∀ v, ((Finset.univ.erase v) \ G.neighborFinset v).card = 1 := fun v => by
    rw [Finset.card_sdiff_of_subset (fun w hw => Finset.mem_erase.2 ⟨(G.ne_of_adj ((G.mem_neighborFinset _ _).1 hw)).symm,
      Finset.mem_univ _⟩), Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, hV,
      card_neighborFinset_eq_degree, hG v]; omega
  choose μ hμ using fun v => Finset.card_eq_one.1 (h1 v)
  have mem : ∀ v w, w ∈ (Finset.univ.erase v) \ G.neighborFinset v ↔ w ≠ v ∧ ¬ G.Adj v w := by
    intro v w; simp [Finset.mem_sdiff, Finset.mem_erase]
  have μspec : ∀ v w, (w ≠ v ∧ ¬ G.Adj v w) ↔ w = μ v := fun v w => by
    rw [← mem, hμ v, Finset.mem_singleton]
  have μinv : ∀ v, μ (μ v) = v := fun v => by
    have := (μspec v (μ v)).2 rfl
    exact ((μspec (μ v) v).1 ⟨this.1.symm, fun h => this.2 h.symm⟩).symm
  let E0 : V ≃ Option (ZMod (2*j+1)) := Fintype.equivOfCardEq (by simp [hV, ZMod.card])
  let μ' : Equiv.Perm (Option (ZMod (2*j+1))) :=
    E0.symm.trans ((Function.Involutive.toPerm μ μinv).trans E0)
  let τ' : Equiv.Perm (Option (ZMod (2*j+1))) := Function.Involutive.toPerm τ hτ
  have hμ' : ∀ z, μ' z = E0 (μ (E0.symm z)) := fun z => rfl
  have hcard : Fintype.card (Option (ZMod (2*j+1))) = 2 * (j+1) := by simp [ZMod.card]; ring
  have hconj : IsConj μ' τ' := by
    rw [Equiv.Perm.isConj_iff_cycleType_eq,
      cycleType_fpf μ' (j+1) (fun z => by simp [hμ', μinv]) (fun z h => by
        have := (μspec (E0.symm z) (μ (E0.symm z))).2 rfl
        rw [hμ'] at h
        exact this.1 (by simpa using congrArg E0.symm h)) hcard (by omega),
      cycleType_fpf τ' (j+1) hτ hτf hcard (by omega)]
  obtain ⟨σ, hσ⟩ := isConj_iff.1 hconj
  have semi : ∀ z, τ (σ z) = σ (μ' z) := fun z => by
    have := congrArg (fun p : Equiv.Perm _ => p (σ z)) hσ
    simp [Equiv.Perm.mul_apply, τ'] at this
    exact this.symm
  let E : V → Option (ZMod (2*j+1)) := fun x => σ (E0 x)
  have Einj : Function.Injective E := σ.injective.comp E0.injective
  have Eμ : ∀ x, E (μ x) = τ (E x) := fun x => by
    simp only [E, semi, hμ', Equiv.symm_apply_apply]
  have nz : ∀ x y, G.Adj x y → c (E x) (E y) ≠ 0 := fun x y hxy h => by
    have := h0τ _ _ (Einj.ne hxy.ne) h
    rw [← Eμ] at this
    exact ((μspec x y).2 (Einj this)).2 hxy
  have : Fact (1 < 2 * j + 1) := ⟨by omega⟩
  let d : V → V → {z : ZMod (2*j+1) // z ≠ 0} := fun x y =>
    if h : c (E x) (E y) = 0 then ⟨1, one_ne_zero⟩ else ⟨_, h⟩
  refine coloring_fin _ ?_ (coloring_of_pair G d (fun x y => by simp only [d, hs (E x)]) ?_)
  · rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq, ZMod.card]; omega
  · intro v y z hy hz e
    simp only [d, dif_neg (nz _ _ hy), dif_neg (nz _ _ hz), Subtype.mk.injEq] at e
    exact Einj (hc _ _ _ (Einj.ne hy.ne) (Einj.ne hz.ne) e)

lemma one_case {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.IsRegularOfDegree 1) : Nonempty (G.lineGraph.Coloring (Fin 1)) :=
  coloring_of_pair G (fun _ _ => 0) (fun _ _ => rfl) fun v y z hy hz _ =>
    Finset.card_le_one.1 (by rw [card_neighborFinset_eq_degree, hG v]) y
      ((G.mem_neighborFinset _ _).2 hy) z ((G.mem_neighborFinset _ _).2 hz)

theorem main : H1 → H2 → type_of% @OMA.S_wp_1_factorization_conjecture.main := by
  intro h1 h2 n k hk G _ hG
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨Empty, Empty.elim, fun i => i.elim, fun i => i.elim,
      fun e _ => by induction e using Sym2.ind with | _ x _ => exact x.elim0⟩
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
  have hV : Fintype.card (Fin (2 * (j + 1))) = 2 * j + 2 := by simp; ring
  have hlt : k < 2 * j + 2 := by
    have := G.degree_lt_card_verts (⟨0, by omega⟩ : Fin (2 * (j + 1)))
    rwa [hG.degree_eq, hV] at this
  by_cases hA : k = 2 * j + 1
  · subst hA; exact factorable_of_coloring G _ hG (top_case G j hV).some
  by_cases hB : k = 2 * j
  · subst hB
    have hj : 1 ≤ j := by
      rcases hk with ⟨-, h⟩ | ⟨he, -⟩
      · omega
      · rcases Nat.eq_zero_or_pos j with rfl | h
        · simp at he
        · exact h
    exact factorable_of_coloring G _ hG (second_case G j hj hV hG).some
  by_cases hD : k = 1
  · subst hD; exact factorable_of_coloring G _ hG (one_case G hG).some
  by_cases hC : 12 * (j + 1) ≤ 7 * k
  · exact factorable_of_coloring G k hG (h1 (j + 1) k hC (by omega) G hG).some
  · exact factorable_of_coloring G k hG (h2 (j + 1) k hk (by omega) (by rcases hk with ⟨-, h⟩ | ⟨-, h⟩ <;> omega) (by omega) G hG).some

end OMA.R_wp_1_factorization_conjecture_R1
