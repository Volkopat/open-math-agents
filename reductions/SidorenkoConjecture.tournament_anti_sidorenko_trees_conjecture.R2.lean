import FormalConjectures.Wikipedia.SidorenkoConjecture

-- Reduction SidorenkoConjecture.tournament_anti_sidorenko_trees_conjecture.R2 of Tournament Anti-Sidorenko (TAS) Trees Conjecture.
-- Credit: @Pixelstorm44
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

open scoped Classical
open Finset

namespace OMA.R_SidorenkoConjecture_tournament_anti_sidorenko_trees_conjecture_R2

-- Restrict each homomorphism to the surviving vertices and record the two images.
private lemma count_pair {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W]
    [DecidableEq W] (a b c : V) (hc : c ≠ a ∧ c ≠ b)
    (D : Digraph V) (B : Digraph {x : V // x ≠ a ∧ x ≠ b}) (G : Digraph W)
    [DecidableRel D.Adj] [DecidableRel B.Adj] [DecidableRel G.Adj]
    (hG : G.IsTournament) (ha : D.Adj a c) (hb : D.Adj c b)
    (hsub : ∀ i j, B.Adj i j → D.Adj i.val j.val) :
    4 * D.homCount G ≤ B.homCount G * Fintype.card W ^ 2 := by
  classical
  let center : {x : V // x ≠ a ∧ x ≠ b} := ⟨c, hc⟩
  let restrict (f : D →g G) : B →g G :=
    ⟨fun i => f i.val, fun {i j} h => f.map_adj' (hsub i j h)⟩
  let fiber (g : B →g G) := {x : W // G.Adj x (g center)} × {y : W // G.Adj (g center) y}
  let encode (f : D →g G) : Σ g : B →g G, fiber g :=
    ⟨restrict f, ⟨f a, f.map_adj' ha⟩, ⟨f b, f.map_adj' hb⟩⟩
  have inj : Function.Injective encode := by
    intro f g h
    have hr := congrArg Sigma.fst h
    have hin := congrArg (fun z : Σ k : B →g G, fiber k => z.2.1.val) h
    have hout := congrArg (fun z : Σ k : B →g G, fiber k => z.2.2.val) h
    have eqf : f.toFun = g.toFun := by
      funext x
      by_cases hxa : x = a
      · subst x
        exact hin
      by_cases hxb : x = b
      · subst x
        exact hout
      exact congrArg (fun k : B →g G => k ⟨x, hxa, hxb⟩) hr
    cases f
    cases g
    congr
  have bound (g : B →g G) : 4 * Fintype.card (fiber g) ≤ Fintype.card W ^ 2 := by
    let incoming := univ.filter (fun x : W => G.Adj x (g center))
    let outgoing := univ.filter (fun x : W => G.Adj (g center) x)
    have dis : Disjoint incoming outgoing := by
      refine Finset.disjoint_left.mpr ?_
      intro x hi ho
      have hx := (Finset.mem_filter.mp hi).2
      have hy := (Finset.mem_filter.mp ho).2
      by_cases he : x = g center
      · exact hG.1 _ (he ▸ hx)
      · exact ((hG.2 _ _ he).mp hx) hy
    have sumle : incoming.card + outgoing.card ≤ Fintype.card W := by
      rw [← Finset.card_union_of_disjoint dis]
      exact Finset.card_le_univ _
    have ci : Fintype.card {x : W // G.Adj x (g center)} = incoming.card :=
      Fintype.card_of_subtype _ (by simp [incoming])
    have co : Fintype.card {x : W // G.Adj (g center) x} = outgoing.card :=
      Fintype.card_of_subtype _ (by simp [outgoing])
    rw [show Fintype.card (fiber g) = _ from Fintype.card_prod _ _, ci, co]
    calc
      _ ≤ (incoming.card + outgoing.card)^2 := by
        zify
        nlinarith [sq_nonneg ((incoming.card : ℤ) - outgoing.card)]
      _ ≤ _ := Nat.pow_le_pow_left sumle _
  calc
    4 * D.homCount G ≤ 4 * Fintype.card (Σ g : B →g G, fiber g) :=
      Nat.mul_le_mul_left _ (Fintype.card_le_of_injective encode inj)
    _ = ∑ g : B →g G, 4 * Fintype.card (fiber g) := by rw [Fintype.card_sigma, Finset.mul_sum]
    _ ≤ ∑ _g : B →g G, Fintype.card W ^ 2 := Finset.sum_le_sum (fun g _ => bound g)
    _ = _ := by simp [Digraph.homCount]

-- Deleting the two leaves successively preserves connectedness and acyclicity.
private lemma prune_tree {V : Type*} [Fintype V] [DecidableEq V] (T : SimpleGraph V)
    [DecidableRel T.Adj] (ht : T.IsTree) (a b c : V) (hab : a ≠ b)
    (ha : ∀ x, T.Adj a x ↔ x = c) (hb : ∀ x, T.Adj b x ↔ x = c) :
    (T.induce {x : V | x ≠ a ∧ x ≠ b}).IsTree := by
  classical
  have hca : c ≠ a := (ha c |>.mpr rfl).ne.symm
  let A : Set V := {a}ᶜ
  let b' : A := ⟨b, hab.symm⟩
  let c' : A := ⟨c, hca⟩
  have da : T.degree a = 1 := SimpleGraph.degree_eq_one_iff_existsUnique_adj.mpr
    ⟨c, (ha c).mpr rfl, fun x hx => (ha x).mp hx⟩
  have connA : (T.induce A).Connected := ht.connected.induce_compl_singleton_of_degree_eq_one da
  have db : (T.induce A).degree b' = 1 := by
    apply SimpleGraph.degree_eq_one_iff_existsUnique_adj.mpr
    exact ⟨c', (hb c).mpr rfl, fun x hx => Subtype.ext ((hb x.val).mp hx)⟩
  let K : Set A := {b'}ᶜ
  have connK : ((T.induce A).induce K).Connected := connA.induce_compl_singleton_of_degree_eq_one db
  let project : SimpleGraph.Hom ((T.induce A).induce K) (T.induce {x : V | x ≠ a ∧ x ≠ b}) :=
    ⟨fun i => ⟨i.val.val, i.val.property, fun e => i.property (Subtype.ext e)⟩, fun h => h⟩
  refine ⟨SimpleGraph.Connected.map project ?_ connK, ht.isAcyclic.induce _⟩
  intro i
  exact ⟨⟨⟨i.val, i.property.1⟩, fun e => i.property.2 (congrArg Subtype.val e)⟩, rfl⟩

-- Keep the surviving arcs and direct the two new edges along a → c → b.
private lemma add_pair {V : Type*} [Fintype V] [DecidableEq V] (T : SimpleGraph V)
    [DecidableRel T.Adj] (a b c : V) (hab : a ≠ b)
    (ha : ∀ x, T.Adj a x ↔ x = c) (hb : ∀ x, T.Adj b x ↔ x = c)
    (B : Digraph {x : V // x ≠ a ∧ x ≠ b})
    (hB : B.IsOrientation (T.induce {x : V | x ≠ a ∧ x ≠ b})) :
    ∃ D : Digraph V, D.IsOrientation T ∧ D.Adj a c ∧ D.Adj c b ∧
      ∀ i j, B.Adj i j → D.Adj i.val j.val := by
  classical
  have hca : c ≠ a := ((ha c).mpr rfl).ne.symm
  have hcb : c ≠ b := ((hb c).mpr rfl).ne.symm
  let D : Digraph V := ⟨fun x y =>
    if hx : x ≠ a ∧ x ≠ b then
      if hy : y ≠ a ∧ y ≠ b then B.Adj ⟨x, hx⟩ ⟨y, hy⟩ else y = b ∧ T.Adj x y
    else x = a ∧ T.Adj x y⟩
  refine ⟨D, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · intro x y h
    dsimp [D] at h
    split at h
    · split at h
      · exact hB.1 _ _ h
      · exact h.2
    · exact h.2
  · intro x y hxy
    have hyx := hxy.symm
    by_cases hx : x ≠ a ∧ x ≠ b <;> by_cases hy : y ≠ a ∧ y ≠ b
    · exact (by simpa [D, hx, hy] using hB.2 ⟨x, hx⟩ ⟨y, hy⟩ hxy)
    · simp [D, hx, hy, hxy, hyx]
      grind
    · simp [D, hx, hy, hxy, hyx]
      grind
    · exfalso
      grind
  · simp [D, (ha c).mpr rfl]
  · simp [D, hca, hcb, ((hb c).mpr rfl).symm]
  · intro i j h
    simpa [D, i.property.1, i.property.2, j.property.1, j.property.2] using h

/-- The path case after all pairs of sibling leaves have been pruned. -/
def H1 : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (T : SimpleGraph V) [DecidableRel T.Adj], T.IsTree →
    (∀ a b c : V, a ≠ b → (∀ x, T.Adj a x ↔ x = c) → ¬ (∀ x, T.Adj b x ↔ x = c)) →
    (∀ z : V, T.degree z ≤ 2) → ∃ D : Digraph V, D.IsOrientation T ∧
      ∀ {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : Digraph W)
        [DecidableRel G.Adj], G.IsTournament → D.homDensity G ≤ (1 / 2 : ℝ) ^ T.edgeFinset.card

/-- The remaining branching trees have at most one leaf adjacent to each vertex. -/
def H2 : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (T : SimpleGraph V) [DecidableRel T.Adj], T.IsTree →
    (∀ a b c : V, a ≠ b → (∀ x, T.Adj a x ↔ x = c) → ¬ (∀ x, T.Adj b x ↔ x = c)) →
    (∃ z : V, 3 ≤ T.degree z) → ∃ D : Digraph V, D.IsOrientation T ∧
      ∀ {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : Digraph W)
        [DecidableRel G.Adj], G.IsTournament → D.homDensity G ≤ (1 / 2 : ℝ) ^ T.edgeFinset.card

theorem prune_induction (paths : H1) (branching : H2)
    (n : ℕ) : ∀ {V : Type} [Fintype V] [DecidableEq V] (T : SimpleGraph V) [DecidableRel T.Adj], Fintype.card V = n →
    T.IsTree → ∃ D : Digraph V, D.IsOrientation T ∧
      ∀ {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : Digraph W)
        [DecidableRel G.Adj], G.IsTournament → D.homDensity G ≤ (1 / 2 : ℝ) ^ T.edgeFinset.card := by
  classical
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro V _ _ T _ hn ht
    by_cases pair : ∃ a b c : V, a ≠ b ∧ (∀ x, T.Adj a x ↔ x = c) ∧ (∀ x, T.Adj b x ↔ x = c)
    · obtain ⟨a, b, c, hab, ha, hb⟩ := pair
      let S : Set V := {x | x ≠ a ∧ x ≠ b}
      let K := T.induce S
      have hK : K.IsTree := prune_tree T ht a b c hab ha hb
      have hca : c ≠ a := ((ha c).mpr rfl).ne.symm
      have hcb : c ≠ b := ((hb c).mpr rfl).ne.symm
      have hsmall : Fintype.card S + 2 = Fintype.card V := by
        have he : Fintype.card S = ((univ.erase a).erase b).card :=
          Fintype.card_of_subtype _ (by intro x; simp [S, and_comm])
        have h₁ := Finset.card_erase_add_one (s := (univ : Finset V)) (a := a) (by simp)
        have h₂ := Finset.card_erase_add_one (s := univ.erase a) (a := b) (by simp [hab.symm])
        simp only [Finset.card_univ] at h₁
        omega
      have hedges : T.edgeFinset.card = K.edgeFinset.card + 2 := by
        have hp := ht.card_edgeFinset
        have hk := hK.card_edgeFinset
        omega
      obtain ⟨B, hB, hgood⟩ := ih (Fintype.card S) (by omega) K rfl hK
      obtain ⟨D, hD, hac, hcb', hsub⟩ := add_pair T a b c hab ha hb B hB
      refine ⟨D, hD, ?_⟩
      intro W _ _ _ G _ hG
      have hc := count_pair a b c ⟨hca, hcb⟩ D B G hG hac hcb' hsub
      have hp := hgood G hG
      unfold Digraph.homDensity at hp ⊢
      have hpos : (0 : ℝ) < Fintype.card W := by exact_mod_cast Fintype.card_pos
      have hc' : 4 * (D.homCount G : ℝ) ≤ (B.homCount G : ℝ) * (Fintype.card W : ℝ)^2 := by
        exact_mod_cast hc
      have hh := (div_le_iff₀ (pow_pos hpos _)).mp hp
      apply (div_le_iff₀ (pow_pos hpos _)).mpr
      rw [← hsmall, hedges, pow_add, pow_add]
      have hm := mul_le_mul_of_nonneg_right hh (sq_nonneg (Fintype.card W : ℝ))
      nlinarith only [hc', hm]
    · have core : ∀ a b c : V, a ≠ b → (∀ x, T.Adj a x ↔ x = c) → ¬ (∀ x, T.Adj b x ↔ x = c) :=
        fun a b c hab ha hb => pair ⟨a, b, c, hab, ha, hb⟩
      by_cases hdeg : ∀ z : V, T.degree z ≤ 2
      · exact paths T ht core hdeg
      · push Not at hdeg
        exact branching T ht core hdeg

theorem main : H1 → H2 → type_of% @SidorenkoConjecture.tournament_anti_sidorenko_trees_conjecture := by
  classical
  intro paths branching V _ _ T _ ht
  let e := Fintype.equivFin V
  let K := T.comap e.symm
  let iso : SimpleGraph.Iso T K := { toEquiv := e, map_rel_iff' := by intro x y; simp [K] }
  have kt := iso.isTree_iff.mp ht
  obtain ⟨B, hB, bound⟩ := prune_induction paths branching _ K rfl kt
  let D : Digraph V := ⟨fun x y => B.Adj (e x) (e y)⟩
  refine ⟨D, ⟨?_, ?_⟩, ?_⟩
  · intro x y h
    exact iso.map_rel_iff.mp (hB.1 _ _ h)
  · intro x y h
    exact hB.2 _ _ (iso.map_rel_iff.mpr h)
  · intro W _ _ _ G _ hG
    let q := Fintype.equivFin W
    let J : Digraph (Fin (Fintype.card W)) := ⟨fun i j => G.Adj (q.symm i) (q.symm j)⟩
    have jt : J.IsTournament := ⟨fun i => hG.1 _, fun i j hij =>
      hG.2 _ _ (fun h => hij (q.symm.injective h))⟩
    have : Nonempty (Fin (Fintype.card W)) := Nonempty.map q inferInstance
    have hj := bound J jt
    let encode (f : D →g G) : B →g J :=
      ⟨fun i => q (f (e.symm i)), fun {i j} hij => by
        change G.Adj (q.symm (q _)) (q.symm (q _))
        simp only [Equiv.symm_apply_apply]
        apply f.map_adj'
        simpa [D] using hij⟩
    have hinj : Function.Injective encode := by
      intro f g h
      have heq : f.toFun = g.toFun := by
        funext x
        have he := congrArg (fun k : B →g J => k (e x)) h
        apply q.injective
        simpa [encode] using he
      cases f
      cases g
      congr
    have hcount : D.homCount G ≤ B.homCount J := Fintype.card_le_of_injective encode hinj
    have edges := iso.card_edgeFinset_eq
    rw [Digraph.homDensity] at hj ⊢
    simp only [Fintype.card_fin] at hj
    rw [edges]
    exact (div_le_div_of_nonneg_right (by exact_mod_cast hcount) (by positivity)).trans hj

end OMA.R_SidorenkoConjecture_tournament_anti_sidorenko_trees_conjecture_R2
