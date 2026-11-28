import OMAStatements.S_oeis_a059442

/-!
# A059442, the fence conjecture

Credit: @grp06.
The conjecture is due to Jianglin Luo, https://oeis.org/A059442/internal.
The finite Ramsey induction, restriction of graph copies, and counting argument
for the probabilistic lower bound are adapted from @TheWaler's proof of Erdős
Problem 78 in https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/299
(`proofs/Erdos78.erdos_78.variants.nonconstructive.lean`).

At `m = n = 65536`, a finite union bound gives a graph with no homogeneous
`m`-subset on more vertices than the fence bound. A partition is encoded by
the multiplicities of its small parts and a padded list of its large parts.
-/

namespace FenceCounterexample

open scoped BigOperators

open SimpleGraph

private def copy_comap {α β γ : Type*} {G : SimpleGraph α} {H : SimpleGraph γ}
    (e : β ↪ γ) (f : Copy G (H.comap e)) : Copy G H where
  toHom :=
    { toFun := fun x => e (f x)
      map_rel' := fun h => f.toHom.map_rel' h }
  injective' := e.injective.comp f.injective

private def copy_comap_compl {α β γ : Type*} {G : SimpleGraph α} {H : SimpleGraph γ}
    (e : β ↪ γ) (f : Copy G (H.comap e)ᶜ) : Copy G Hᶜ where
  toHom :=
    { toFun := fun x => e (f x)
      map_rel' := fun h => by
        have h' := f.toHom.map_rel' h
        rw [SimpleGraph.compl_adj] at h' ⊢
        exact ⟨fun heq => h'.1 (e.injective heq), h'.2⟩ }
  injective' := e.injective.comp f.injective

private def extend_complete_copy {V : Type*} {C : SimpleGraph V} {k : ℕ}
    (v₀ : V) (S : Finset V) (hS : ∀ v ∈ S, v ≠ v₀ ∧ C.Adj v₀ v)
    (f : Copy (completeGraph (Fin k)) (C.comap (Function.Embedding.subtype (· ∈ S)))) :
    Copy (completeGraph (Fin (k + 1))) C where
  toHom :=
    { toFun := fun i => if h : i.1 < k then (f ⟨i.1, h⟩).1 else v₀
      map_rel' := by
        intro i j hij
        change i ≠ j at hij
        by_cases hi : i.1 < k
        · by_cases hj : j.1 < k
          · simp only [hi, hj, ↓reduceDIte]
            have hne : (⟨i.1, hi⟩ : Fin k) ≠ ⟨j.1, hj⟩ := by
              intro heq
              apply hij
              have hval : i.1 = j.1 := congrArg (fun x : Fin k => x.1) heq
              exact Fin.ext hval
            exact f.toHom.map_rel' hne
          · simp only [hi, hj, ↓reduceDIte]
            exact (C.adj_comm _ _).mp (hS (f ⟨i.1, hi⟩).1 (f ⟨i.1, hi⟩).2).2
        · by_cases hj : j.1 < k
          · simp only [hi, hj, ↓reduceDIte]
            exact (hS (f ⟨j.1, hj⟩).1 (f ⟨j.1, hj⟩).2).2
          · exfalso
            apply hij
            apply Fin.ext
            omega }
  injective' := by
    intro i j hij
    change (if h : i.1 < k then (f ⟨i.1, h⟩).1 else v₀) =
      (if h : j.1 < k then (f ⟨j.1, h⟩).1 else v₀) at hij
    by_cases hi : i.1 < k
    · by_cases hj : j.1 < k
      · simp only [hi, hj, ↓reduceDIte] at hij
        have heq : f ⟨i.1, hi⟩ = f ⟨j.1, hj⟩ := Subtype.ext hij
        have hval : i.1 = j.1 := congrArg (fun x : Fin k => x.1) (f.injective heq)
        exact Fin.ext hval
      · simp only [hi, hj, ↓reduceDIte] at hij
        exact absurd hij (hS (f ⟨i.1, hi⟩).1 (f ⟨i.1, hi⟩).2).1
    · by_cases hj : j.1 < k
      · simp only [hi, hj, ↓reduceDIte] at hij
        exact absurd hij.symm (hS (f ⟨j.1, hj⟩).1 (f ⟨j.1, hj⟩).2).1
      · apply Fin.ext
        omega

private lemma ramsey_exists_aux : ∀ s k l : ℕ, k + l = s →
    ∃ N : ℕ, ∀ (V : Type) [Fintype V], N ≤ Fintype.card V →
      ∀ C : SimpleGraph V,
        (completeGraph (Fin k)).IsContained C ∨ (completeGraph (Fin l)).IsContained Cᶜ := by
  intro s
  induction s with
  | zero =>
    intro k l hkl
    have hk : k = 0 := by omega
    subst hk
    refine ⟨0, fun V _ _ C => Or.inl ⟨⟨⟨Fin.elim0, fun {a} => Fin.elim0 a⟩, fun a => Fin.elim0 a⟩⟩⟩
  | succ s ih =>
    intro k l hkl
    cases k with
    | zero =>
      refine ⟨0, fun V _ _ C => Or.inl ⟨⟨⟨Fin.elim0, fun {a} => Fin.elim0 a⟩, fun a => Fin.elim0 a⟩⟩⟩
    | succ k' =>
      cases l with
      | zero =>
        refine ⟨0, fun V _ _ C => Or.inr ⟨⟨⟨Fin.elim0, fun {a} => Fin.elim0 a⟩, fun a => Fin.elim0 a⟩⟩⟩
      | succ l' =>
        obtain ⟨N₁, hN₁⟩ := ih k' (l' + 1) (by omega)
        obtain ⟨N₂, hN₂⟩ := ih (k' + 1) l' (by omega)
        refine ⟨N₁ + N₂ + 1, ?_⟩
        intro V _ hcard C
        classical
        have hpos : 0 < Fintype.card V := by omega
        obtain ⟨v₀⟩ := Fintype.card_pos_iff.mp hpos
        let S₁ : Finset V := Finset.univ.filter (fun v => v ≠ v₀ ∧ C.Adj v₀ v)
        let S₂ : Finset V := Finset.univ.filter (fun v => v ≠ v₀ ∧ ¬ C.Adj v₀ v)
        have hdisj : Disjoint S₁ S₂ := by
          rw [Finset.disjoint_left]
          intro v hv1 hv2
          simp only [S₁, S₂, Finset.mem_filter, Finset.mem_univ, true_and] at hv1 hv2
          exact hv2.2 hv1.2
        have hunion : S₁ ∪ S₂ = Finset.univ.erase v₀ := by
          ext v
          simp only [S₁, S₂, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
            Finset.mem_erase]
          tauto
        have hsum : S₁.card + S₂.card = Fintype.card V - 1 := by
          rw [← Finset.card_union_of_disjoint hdisj, hunion,
            Finset.card_erase_of_mem (Finset.mem_univ v₀), Finset.card_univ]
        have hsplit : N₁ ≤ S₁.card ∨ N₂ ≤ S₂.card := by omega
        rcases hsplit with h1 | h2
        · let e₁ : {v : V // v ∈ S₁} ↪ V := Function.Embedding.subtype (· ∈ S₁)
          have hcard1 : N₁ ≤ Fintype.card {v : V // v ∈ S₁} := by
            simpa [Fintype.card_coe] using h1
          rcases hN₁ {v : V // v ∈ S₁} hcard1 (C.comap e₁) with hf | hf
          · rcases (hf : Nonempty _) with ⟨f⟩
            left
            refine ⟨extend_complete_copy v₀ S₁ ?_ f⟩
            intro v hv
            simp only [S₁, Finset.mem_filter, Finset.mem_univ, true_and] at hv
            exact ⟨hv.1, hv.2⟩
          · rcases (hf : Nonempty _) with ⟨f⟩
            right
            exact ⟨copy_comap_compl e₁ f⟩
        · let e₂ : {v : V // v ∈ S₂} ↪ V := Function.Embedding.subtype (· ∈ S₂)
          have hcard2 : N₂ ≤ Fintype.card {v : V // v ∈ S₂} := by
            simpa [Fintype.card_coe] using h2
          rcases hN₂ {v : V // v ∈ S₂} hcard2 (C.comap e₂) with hf | hf
          · rcases (hf : Nonempty _) with ⟨f⟩
            left
            exact ⟨copy_comap e₂ f⟩
          · rcases (hf : Nonempty _) with ⟨f⟩
            right
            have hcompl_eq : (C.comap e₂)ᶜ = Cᶜ.comap e₂ := by
              ext x y
              simp only [SimpleGraph.compl_adj, SimpleGraph.comap_adj, e₂,
                Function.Embedding.coe_subtype, ne_eq, Subtype.ext_iff]
            rw [hcompl_eq] at f
            refine ⟨extend_complete_copy v₀ S₂ ?_ f⟩
            intro v hv
            simp only [S₂, Finset.mem_filter, Finset.mem_univ, true_and] at hv
            exact ⟨hv.1, by rw [SimpleGraph.compl_adj]; exact ⟨hv.1.symm, hv.2⟩⟩

private abbrev Pair (n : ℕ) := { p : Fin n × Fin n // p.1 < p.2 }

private def toGraph {n : ℕ} (c : Pair n → Bool) : SimpleGraph (Fin n) where
  Adj u v :=
    if h : u < v then c ⟨(u, v), h⟩ = true
    else if h' : v < u then c ⟨(v, u), h'⟩ = true
    else False
  symm := ⟨by
    intro u v huv
    by_cases h1 : u < v
    · have h2 : ¬ v < u := not_lt_of_gt h1
      simp only [h1, h2, ↓reduceDIte] at huv ⊢
      exact huv
    · by_cases h2 : v < u
      · simp only [h1, h2, ↓reduceDIte] at huv ⊢
        exact huv
      · simp only [h1, h2, ↓reduceDIte] at huv⟩
  loopless := ⟨by
    intro u
    simp⟩

private lemma toGraph_adj_of_lt {n : ℕ} (c : Pair n → Bool) {u v : Fin n} (h : u < v) :
    (toGraph c).Adj u v ↔ c ⟨(u, v), h⟩ = true := by
  simp [toGraph, h]

private lemma toGraph_compl_adj_of_lt {n : ℕ} (c : Pair n → Bool) {u v : Fin n} (h : u < v) :
    (toGraph c)ᶜ.Adj u v ↔ c ⟨(u, v), h⟩ = false := by
  simp [SimpleGraph.compl_adj, ne_of_lt h, toGraph, h]

private def pairsIn {n : ℕ} (s : Finset (Fin n)) : Finset (Pair n) :=
  Finset.univ.filter (fun p => p.1.1 ∈ s ∧ p.1.2 ∈ s)

private lemma pairsIn_card {n : ℕ} (s : Finset (Fin n)) :
    (pairsIn s).card = s.card * (s.card - 1) / 2 := by
  let L : Finset (Fin n × Fin n) := (s ×ˢ s).filter (fun p => p.1 < p.2)
  let G : Finset (Fin n × Fin n) := (s ×ˢ s).filter (fun p => p.2 < p.1)
  let D : Finset (Fin n × Fin n) := (s ×ˢ s).filter (fun p => p.1 = p.2)
  have hPL : (pairsIn s).card = L.card := by
    refine Finset.card_bij (fun p _ => p.1) ?_ ?_ ?_
    · intro p hp
      simp only [pairsIn, Finset.mem_filter, Finset.mem_univ, true_and] at hp
      simp only [L, Finset.mem_filter, Finset.mem_product]
      exact ⟨hp, p.2⟩
    · intro p₁ _ p₂ _ h
      exact Subtype.ext h
    · intro q hq
      simp only [L, Finset.mem_filter, Finset.mem_product] at hq
      exact ⟨⟨q, hq.2⟩, by simp [pairsIn, hq.1], rfl⟩
  have hLG : L.card = G.card := by
    refine Finset.card_bij (fun p _ => (p.2, p.1)) ?_ ?_ ?_
    · intro p hp
      simp only [L, Finset.mem_filter, Finset.mem_product] at hp
      simp only [G, Finset.mem_filter, Finset.mem_product]
      exact ⟨⟨hp.1.2, hp.1.1⟩, hp.2⟩
    · intro p₁ _ p₂ _ h
      cases p₁; cases p₂
      simp only [Prod.mk.injEq] at h
      exact Prod.ext h.2 h.1
    · intro q hq
      simp only [G, Finset.mem_filter, Finset.mem_product] at hq
      exact ⟨(q.2, q.1), by simp [L, hq.1.1, hq.1.2, hq.2], by simp⟩
  have hDs : D.card = s.card := by
    refine Finset.card_bij (fun p _ => p.1) ?_ ?_ ?_
    · intro p hp
      simp only [D, Finset.mem_filter, Finset.mem_product] at hp
      exact hp.1.1
    · intro p₁ hp₁ p₂ hp₂ h
      simp only [D, Finset.mem_filter, Finset.mem_product] at hp₁ hp₂
      exact Prod.ext h (hp₁.2.symm.trans (h.trans hp₂.2))
    · intro x hx
      exact ⟨(x, x), by simp [D, hx], rfl⟩
  have hdisj1 : Disjoint L G := by
    rw [Finset.disjoint_left]
    intro p hp1 hp2
    simp only [L, G, Finset.mem_filter] at hp1 hp2
    exact lt_asymm hp1.2 hp2.2
  have hdisj2 : Disjoint (L ∪ G) D := by
    rw [Finset.disjoint_left]
    intro p hp1 hp2
    simp only [L, G, D, Finset.mem_union, Finset.mem_filter] at hp1 hp2
    rcases hp1 with h1 | h1
    · exact ne_of_lt h1.2 hp2.2
    · exact ne_of_gt h1.2 hp2.2
  have hunion : (L ∪ G) ∪ D = s ×ˢ s := by
    ext ⟨u, v⟩
    simp only [L, G, D, Finset.mem_union, Finset.mem_filter, Finset.mem_product]
    constructor
    · rintro ((⟨h, _⟩ | ⟨h, _⟩) | ⟨h, _⟩) <;> exact h
    · intro h
      rcases lt_trichotomy u v with hlt | heq | hgt
      · exact Or.inl (Or.inl ⟨h, hlt⟩)
      · exact Or.inr ⟨h, heq⟩
      · exact Or.inl (Or.inr ⟨h, hgt⟩)
  have htotal : 2 * (pairsIn s).card + s.card = s.card * s.card := by
    have hc : ((L ∪ G) ∪ D).card = (s ×ˢ s).card := congrArg Finset.card hunion
    rw [Finset.card_union_of_disjoint hdisj2, Finset.card_union_of_disjoint hdisj1,
      Finset.card_product, ← hLG, ← hPL, hDs] at hc
    omega
  cases hk : s.card with
  | zero =>
    rw [hk] at htotal
    omega
  | succ m =>
    rw [hk] at htotal
    have hmul : (m + 1) * (m + 1) = (m + 1) * m + (m + 1) := by ring
    rw [hmul] at htotal
    have h2 : 2 * (pairsIn s).card = (m + 1) * m := by omega
    simp only [Nat.add_sub_cancel]
    omega

private def monoGraphs {n : ℕ} (s : Finset (Fin n)) (b : Bool) : Finset (Pair n → Bool) :=
  Finset.univ.filter (fun c => ∀ p ∈ pairsIn s, c p = b)

private lemma monoGraphs_card_mul {n : ℕ} (s : Finset (Fin n)) (b : Bool) :
    (monoGraphs s b).card * 2 ^ (pairsIn s).card ≤ 2 ^ Fintype.card (Pair n) := by
  let res : (Pair n → Bool) → ({p : Pair n // p ∉ pairsIn s} → Bool) :=
    fun c p => c p.1
  have hinj : Set.InjOn res (monoGraphs s b) := by
    intro c₁ hc₁ c₂ hc₂ heq
    simp only [Finset.mem_coe, monoGraphs, Finset.mem_filter, Finset.mem_univ, true_and] at hc₁ hc₂
    funext p
    by_cases hp : p ∈ pairsIn s
    · rw [hc₁ p hp, hc₂ p hp]
    · exact congrFun heq ⟨p, hp⟩
  have hle : (monoGraphs s b).card ≤ Fintype.card ({p : Pair n // p ∉ pairsIn s} → Bool) := by
    have h := Finset.card_le_card_of_injOn res (fun _ _ => Finset.mem_univ _) hinj
    simpa [Finset.card_univ] using h
  rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_subtype_compl, Fintype.card_coe] at hle
  have hsub : (pairsIn s).card ≤ Fintype.card (Pair n) := Finset.card_le_univ (pairsIn s)
  have hmul := Nat.mul_le_mul_right (2 ^ (pairsIn s).card) hle
  rwa [← pow_add, Nat.sub_add_cancel hsub] at hmul

private lemma exists_ramsey_counterexample {n k : ℕ}
    (hlt : 2 * n.choose k < 2 ^ (k * (k - 1) / 2)) :
    ∃ C : SimpleGraph (Fin n),
      ¬ (completeGraph (Fin k)).IsContained C ∧ ¬ (completeGraph (Fin k)).IsContained Cᶜ := by
  let Bad : Finset (Pair n → Bool) :=
    ((Finset.univ : Finset (Fin n)).powersetCard k).biUnion
      (fun s => monoGraphs s true ∪ monoGraphs s false)
  have hbad_mul : Bad.card * 2 ^ (k * (k - 1) / 2) ≤
      (2 * n.choose k) * 2 ^ Fintype.card (Pair n) := by
    have h1 : Bad.card ≤
        ∑ s ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
          (monoGraphs s true ∪ monoGraphs s false).card :=
      Finset.card_biUnion_le
    calc Bad.card * 2 ^ (k * (k - 1) / 2)
        ≤ (∑ s ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
            (monoGraphs s true ∪ monoGraphs s false).card) * 2 ^ (k * (k - 1) / 2) :=
          Nat.mul_le_mul_right _ h1
      _ = ∑ s ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
            (monoGraphs s true ∪ monoGraphs s false).card * 2 ^ (k * (k - 1) / 2) :=
          Finset.sum_mul _ _ _
      _ ≤ ∑ _s ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
            (2 * 2 ^ Fintype.card (Pair n)) := by
          refine Finset.sum_le_sum fun s hs => ?_
          have hscard : s.card = k := (Finset.mem_powersetCard.mp hs).2
          have hpcard : (pairsIn s).card = k * (k - 1) / 2 := by
            rw [pairsIn_card, hscard]
          rw [← hpcard]
          have hu := Finset.card_union_le (monoGraphs s true) (monoGraphs s false)
          calc (monoGraphs s true ∪ monoGraphs s false).card * 2 ^ (pairsIn s).card
              ≤ ((monoGraphs s true).card + (monoGraphs s false).card) * 2 ^ (pairsIn s).card :=
                Nat.mul_le_mul_right _ hu
            _ = (monoGraphs s true).card * 2 ^ (pairsIn s).card +
                (monoGraphs s false).card * 2 ^ (pairsIn s).card :=
                Nat.add_mul _ _ _
            _ ≤ 2 ^ Fintype.card (Pair n) + 2 ^ Fintype.card (Pair n) :=
                Nat.add_le_add (monoGraphs_card_mul s true) (monoGraphs_card_mul s false)
            _ = 2 * 2 ^ Fintype.card (Pair n) := by ring
      _ = ((Finset.univ : Finset (Fin n)).powersetCard k).card *
            (2 * 2 ^ Fintype.card (Pair n)) := by
          rw [Finset.sum_const, smul_eq_mul]
      _ = (2 * n.choose k) * 2 ^ Fintype.card (Pair n) := by
          rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
          ring
  have hbad_lt_mul : Bad.card * 2 ^ (k * (k - 1) / 2) <
      2 ^ (k * (k - 1) / 2) * 2 ^ Fintype.card (Pair n) :=
    lt_of_le_of_lt hbad_mul (Nat.mul_lt_mul_of_pos_right hlt (by positivity))
  have hbad_lt : Bad.card < (Finset.univ : Finset (Pair n → Bool)).card := by
    have hlt' : Bad.card < 2 ^ Fintype.card (Pair n) := by
      rw [mul_comm (2 ^ (k * (k - 1) / 2))] at hbad_lt_mul
      exact Nat.lt_of_mul_lt_mul_right hbad_lt_mul
    simpa [Finset.card_univ, Fintype.card_fun, Fintype.card_bool] using hlt'
  have hex : ∃ c : Pair n → Bool, c ∉ Bad := by
    by_contra hall
    push Not at hall
    have hsub : (Finset.univ : Finset (Pair n → Bool)) ⊆ Bad := fun c _ => hall c
    exact not_le_of_gt hbad_lt (Finset.card_le_card hsub)
  obtain ⟨c, hc⟩ := hex
  refine ⟨toGraph c, ?_, ?_⟩
  · intro hf
    rcases (hf : Nonempty _) with ⟨f⟩
    let s : Finset (Fin n) := Finset.univ.image f
    have hscard : s.card = k := by
      dsimp only [s]
      rw [← SimpleGraph.Copy.coe_toHom, Finset.card_image_of_injective _ f.injective,
        Finset.card_univ, Fintype.card_fin]
    have hs_mem : s ∈ (Finset.univ : Finset (Fin n)).powersetCard k :=
      Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hscard⟩
    have hc_mono : c ∈ monoGraphs s true := by
      simp only [monoGraphs, Finset.mem_filter, Finset.mem_univ, true_and]
      intro p hp
      simp only [pairsIn, Finset.mem_filter, Finset.mem_univ, true_and] at hp
      obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hp.1
      obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hp.2
      have hij : i ≠ j := by
        intro h
        subst h
        exact ne_of_lt p.2 (hi.symm.trans hj)
      have hadj : (toGraph c).Adj p.1.1 p.1.2 := by
        rw [← hi, ← hj]
        exact f.toHom.map_rel' hij
      exact (toGraph_adj_of_lt c p.2).mp hadj
    exact hc (Finset.mem_biUnion.mpr ⟨s, hs_mem, Finset.mem_union_left _ hc_mono⟩)
  · intro hf
    rcases (hf : Nonempty _) with ⟨f⟩
    let s : Finset (Fin n) := Finset.univ.image f
    have hscard : s.card = k := by
      dsimp only [s]
      rw [← SimpleGraph.Copy.coe_toHom, Finset.card_image_of_injective _ f.injective,
        Finset.card_univ, Fintype.card_fin]
    have hs_mem : s ∈ (Finset.univ : Finset (Fin n)).powersetCard k :=
      Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hscard⟩
    have hc_mono : c ∈ monoGraphs s false := by
      simp only [monoGraphs, Finset.mem_filter, Finset.mem_univ, true_and]
      intro p hp
      simp only [pairsIn, Finset.mem_filter, Finset.mem_univ, true_and] at hp
      obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hp.1
      obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hp.2
      have hij : i ≠ j := by
        intro h
        subst h
        exact ne_of_lt p.2 (hi.symm.trans hj)
      have hadj : (toGraph c)ᶜ.Adj p.1.1 p.1.2 := by
        rw [← hi, ← hj]
        exact f.toHom.map_rel' hij
      exact (toGraph_compl_adj_of_lt c p.2).mp hadj
    exact hc (Finset.mem_biUnion.mpr ⟨s, hs_mem, Finset.mem_union_right _ hc_mono⟩)

private lemma choose_le_pow (n k : ℕ) : n.choose k ≤ n ^ k := by
  calc n.choose k
      ≤ k.factorial * n.choose k := Nat.le_mul_of_pos_left _ (Nat.factorial_pos k)
    _ = n.descFactorial k := (Nat.descFactorial_eq_factorial_mul_choose n k).symm
    _ ≤ n ^ k := Nat.descFactorial_le_pow n k

private lemma exp_ineq_nat {k : ℕ} (hk : 9 ≤ k) :
    2 * (2 ^ (k / 3)).choose k < 2 ^ (k * (k - 1) / 2) := by
  have hexp : 1 + (k / 3) * k < k * (k - 1) / 2 := by
    have h3 : 3 * (k / 3) ≤ k := Nat.mul_div_le k 3
    have h6 : 6 * (1 + (k / 3) * k + 1) ≤ 3 * (k * (k - 1)) := by
      have hmul : 3 * ((k / 3) * k) ≤ k * k := by
        rw [← mul_assoc]
        exact Nat.mul_le_mul_right k h3
      have hkm : k * (k - 1) + k = k * k := by
        cases k with
        | zero => omega
        | succ m =>
          simp only [Nat.add_sub_cancel]
          ring
      nlinarith
    omega
  calc 2 * (2 ^ (k / 3)).choose k
      ≤ 2 * (2 ^ (k / 3)) ^ k := Nat.mul_le_mul_left 2 (choose_le_pow _ _)
    _ = 2 ^ (1 + (k / 3) * k) := by rw [← pow_mul, pow_add, pow_one]
    _ < 2 ^ (k * (k - 1) / 2) := Nat.pow_lt_pow_right (by norm_num) hexp

private lemma ramsey_gt_of_counterexample {n k : ℕ} (C : SimpleGraph (Fin n))
    (h₁ : ¬ (completeGraph (Fin k)).IsContained C)
    (h₂ : ¬ (completeGraph (Fin k)).IsContained Cᶜ) :
    n < OMA.S_oeis_a059442.ramsey k k := by
  let S : Set ℕ :=
    {N | ∀ G : SimpleGraph (Fin N), ¬ G.CliqueFree k ∨ ¬ Gᶜ.CliqueFree k}
  have hS : S.Nonempty := by
    obtain ⟨N, hN⟩ := ramsey_exists_aux (k + k) k k rfl
    refine ⟨N, fun G => ?_⟩
    simpa only [SimpleGraph.not_cliqueFree_iff_top_isContained] using
      hN (Fin N) (by simp) G
  have hmem : OMA.S_oeis_a059442.ramsey k k ∈ S := Nat.sInf_mem hS
  by_contra h
  have hle : OMA.S_oeis_a059442.ramsey k k ≤ n := Nat.le_of_not_gt h
  let e : Fin (OMA.S_oeis_a059442.ramsey k k) ↪ Fin n := Fin.castLEEmb hle
  rcases hmem (C.comap e) with hC | hC
  · obtain ⟨f⟩ := (SimpleGraph.not_cliqueFree_iff_top_isContained k).mp hC
    exact h₁ ⟨copy_comap e f⟩
  · obtain ⟨f⟩ := (SimpleGraph.not_cliqueFree_iff_top_isContained k).mp hC
    exact h₂ ⟨copy_comap_compl e f⟩

private lemma mul_card_le_sum (a : ℕ) (s : Multiset ℕ) :
    (∀ x ∈ s, a ≤ x) → s.card * a ≤ s.sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons x s ih =>
    intro h
    have hx : a ≤ x := h x (Multiset.mem_cons_self _ _)
    have hs : s.card * a ≤ s.sum :=
      ih fun y hy => h y (Multiset.mem_cons_of_mem hy)
    rw [Multiset.card_cons, Multiset.sum_cons, Nat.add_mul, Nat.one_mul, add_comm (s.card * a)]
    exact Nat.add_le_add hx hs

private def largeParts {N : ℕ} (p : Nat.Partition N) : Multiset ℕ :=
  p.parts.filter (fun x => 512 < x)

private def largeList {N : ℕ} (p : Nat.Partition N) : List ℕ :=
  (largeParts p).sort (· ≤ ·)

private lemma largeList_length (p : Nat.Partition 196602) : (largeList p).length ≤ 512 := by
  have hsplit := Multiset.filter_add_not (fun x : ℕ => 512 < x) p.parts
  have hsum := congrArg Multiset.sum hsplit
  rw [Multiset.sum_add, p.parts_sum] at hsum
  have hlarge : (largeParts p).sum ≤ 196602 := by
    have h := Nat.le_add_right (largeParts p).sum ((p.parts.filter (fun x : ℕ => ¬ 512 < x)).sum)
    exact h.trans_eq hsum
  have hweight := mul_card_le_sum 513 (largeParts p) (by
    intro x hx
    exact Nat.succ_le_of_lt (Multiset.mem_filter.mp hx).2)
  have hcard := hweight.trans hlarge
  rw [largeList, Multiset.length_sort]
  omega

private def smallCode (p : Nat.Partition 196602) (i : Fin 512) : Fin 196603 :=
  ⟨p.parts.count (i.val + 1), by
    have h := mul_card_le_sum 1 p.parts (fun _ hx => p.parts_pos hx)
    rw [Nat.mul_one, p.parts_sum] at h
    exact Nat.lt_succ_of_le ((Multiset.count_le_card _ _).trans h)⟩

private def largeCode (p : Nat.Partition 196602) (i : Fin 512) : Option (Fin 196603) :=
  if h : i.val < (largeList p).length then
    some ⟨(largeList p)[i.val]'h, by
      apply Nat.lt_succ_of_le
      apply p.le_of_mem_parts
      exact (Multiset.mem_filter.mp
        ((Multiset.mem_sort (· ≤ ·)).mp (List.getElem_mem h))).1⟩
  else none

private lemma largeCode_read (p : Nat.Partition 196602) (i : Fin 512) :
    (largeCode p i).map Fin.val = (largeList p)[i.val]? := by
  by_cases hi : i.val < (largeList p).length
  · rw [List.getElem?_eq_getElem hi]
    simp [largeCode, hi]
  · rw [List.getElem?_eq_none (Nat.le_of_not_gt hi)]
    simp [largeCode, hi]

private def partitionCode (p : Nat.Partition 196602) :
    (Fin 512 → Fin 196603) × (Fin 512 → Option (Fin 196603)) :=
  (smallCode p, largeCode p)

private lemma partitionCode_injective : Function.Injective partitionCode := by
  intro p q h
  have hl : largeList p = largeList q := by
    apply List.ext_getElem?'
    intro i hi
    have hb : i < 512 := hi.trans_le (max_le (largeList_length p) (largeList_length q))
    let j : Fin 512 := ⟨i, hb⟩
    have he := congrArg (fun f => (f.2 j).map Fin.val) h
    change (largeCode p j).map Fin.val = (largeCode q j).map Fin.val at he
    simpa only [largeCode_read] using he
  have hlarge : largeParts p = largeParts q := by
    have he := congrArg (fun l : List ℕ => (l : Multiset ℕ)) hl
    simpa only [largeList, Multiset.sort_eq] using he
  apply Nat.Partition.ext
  apply Multiset.ext'
  intro x
  by_cases hgt : 512 < x
  · calc p.parts.count x = (largeParts p).count x :=
          (Multiset.count_filter_of_pos hgt).symm
      _ = (largeParts q).count x := by rw [hlarge]
      _ = q.parts.count x := Multiset.count_filter_of_pos hgt
  · by_cases hx : x = 0
    · subst x
      have hp : 0 ∉ p.parts := fun hm => (Nat.lt_irrefl 0) (p.parts_pos hm)
      have hq : 0 ∉ q.parts := fun hm => (Nat.lt_irrefl 0) (q.parts_pos hm)
      rw [Multiset.count_eq_zero_of_notMem hp, Multiset.count_eq_zero_of_notMem hq]
    · let i : Fin 512 := ⟨x - 1, by omega⟩
      have he := congrArg (fun f => (f.1 i).val) h
      change p.parts.count (i.val + 1) = q.parts.count (i.val + 1) at he
      have hi : i.val + 1 = x := by
        change x - 1 + 1 = x
        omega
      simpa only [hi] using he

private lemma mul_pow_bound (a b d : ℕ) (ha : a ≤ 2 ^ 18) (hb : b ≤ 2 ^ 18) :
    a ^ d * b ^ d ≤ 2 ^ (18 * d + 18 * d) := by
  calc
    _ ≤ (2 ^ 18) ^ d * (2 ^ 18) ^ d :=
      Nat.mul_le_mul (Nat.pow_le_pow_left ha d) (Nat.pow_le_pow_left hb d)
    _ = _ := by rw [← pow_mul, ← pow_add]

private lemma T_le_card (N k : ℕ) :
    OMA.S_oeis_a059442.T N k ≤ Fintype.card (Nat.Partition N) := by
  unfold OMA.S_oeis_a059442.T
  exact Finset.card_le_univ _

private lemma partition_bound (k : ℕ) : OMA.S_oeis_a059442.T 196602 k ≤ 2 ^ 18432 := by
  classical
  have hc := Fintype.card_le_of_injective partitionCode partitionCode_injective
  simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, Fintype.card_option] at hc
  have h₁ : (196603 : ℕ) ≤ 2 ^ 18 := by decide
  have h₂ : (196603 : ℕ) + 1 ≤ 2 ^ 18 := by decide
  have hd := mul_pow_bound 196603 (196603 + 1) 512 h₁ h₂
  have he : (18 : ℕ) * 512 + 18 * 512 = 18432 := by decide
  rw [he] at hd
  exact (T_le_card 196602 k).trans (hc.trans hd)

private lemma partition_bound_of_eq {N k : ℕ} (hN : N = 196602) :
    OMA.S_oeis_a059442.T N k ≤ 2 ^ 18432 := by
  subst N
  exact partition_bound k

private lemma fence_arithmetic (m t a b c : ℕ)
    (hcoeff : 2 * m - 1 ≤ 2 ^ a) (ht : t ≤ 2 ^ b)
    (hrest : m + 1 ≤ 2 ^ a) (hexp : a + b + 1 ≤ c) :
    (2 * m - 1) * t + m + 1 ≤ 2 ^ c := by
  have htwo : (0 : ℕ) < 2 := by decide
  have hmain : (2 * m - 1) * t ≤ 2 ^ (a + b) := by
    rw [pow_add]
    exact Nat.mul_le_mul hcoeff ht
  have hlast : m + 1 ≤ 2 ^ (a + b) :=
    hrest.trans (Nat.pow_le_pow_right htwo (Nat.le_add_right a b))
  calc
    _ ≤ 2 ^ (a + b) + 2 ^ (a + b) := by
      rw [add_assoc]
      exact Nat.add_le_add hmain hlast
    _ = 2 ^ (a + b + 1) := by rw [← two_mul, ← pow_succ']
    _ ≤ 2 ^ c := Nat.pow_le_pow_right htwo hexp

private lemma fence_bound :
    (2 * 65536 - 1) * OMA.S_oeis_a059442.T (2 * 65536 - 6 + 65536) 65536 + 65536 + 1 ≤
      2 ^ (65536 / 3) := by
  have hN : (2 : ℕ) * 65536 - 6 + 65536 = 196602 := by decide
  have ht := partition_bound_of_eq (k := 65536) hN
  exact fence_arithmetic 65536 _ 17 18432 (65536 / 3) (by decide) ht (by decide) (by decide)

private lemma diagonal_violation (k : ℕ) (hk : 9 ≤ k) {V : ℕ} (hV : V ≤ 2 ^ (k / 3)) :
    ¬ OMA.S_oeis_a059442.ramsey k k ≤ V := by
  obtain ⟨C, h₁, h₂⟩ := exists_ramsey_counterexample (exp_ineq_nat hk)
  have hgt := ramsey_gt_of_counterexample C h₁ h₂
  exact fun h => (not_le_of_gt hgt) (h.trans hV)

end FenceCounterexample

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a059442.main) := by
  intro h
  exact FenceCounterexample.diagonal_violation 65536 (by decide)
    FenceCounterexample.fence_bound (h 65536 65536 (by decide) le_rfl)
