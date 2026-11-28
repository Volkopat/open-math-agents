import OMAStatements.S_opg_behzads_conjecture
import Mathlib

-- Reduction opg-behzads-conjecture.R2 of Behzad's conjecture (total colouring)
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

/-!
# Behzad's conjecture: the lower bound, the cases Δ ≤ 2, and the Total Colouring Conjecture

Behzad's conjecture says `χ''(G) ∈ {Δ + 1, Δ + 2}`. This file proves the easy half and all
cases `Δ ≤ 2`, and isolates the upper bound (the Total Colouring Conjecture, TCC) for `Δ ≥ 3`:

* lower bound (proved here): every total colouring of a nonempty graph uses at least `Δ + 1`
  colours, since a vertex of maximum degree and its `Δ` incident edges pairwise conflict;
* `Δ ≤ 1` (proved here): an explicit `(Δ + 2)`-total colouring;
* `Δ = 2` (proved here): every graph with maximum degree at most 2 has a 4-total colouring.
  Proof by induction on the vertex set: add a vertex `v`; if `v` has two earlier neighbours
  `u`, `w`, recolour `u` (whose only other neighbour is fixed) and choose colours for `v`,
  `uv`, `vw` by a finite check over `Fin 4`; the cases of fewer neighbours are greedy;
* `H1` (known): a `(Δ + 2)`-total colouring exists when `3 ≤ Δ ≤ 5`
  (Rosenfeld 1971 and Vijayaditya 1971 for `Δ = 3`, Kostochka 1977 and 1996 for `Δ ≤ 5`);
* `H2` (open core): a `(Δ + 2)`-total colouring exists when `Δ ≥ 6`.

Since the minimum is attained (`Nat.sInf_mem`), the two bounds give the disjunction.
-/

namespace OMA.R_opg_behzads_conjecture_R2

open OMA.S_opg_behzads_conjecture

/-- Total Colouring Conjecture for `3 ≤ Δ ≤ 5` (known: Rosenfeld, Vijayaditya, Kostochka). -/
def H1 : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj],
    3 ≤ G.maxDegree → G.maxDegree ≤ 5 →
      ∃ (cv : V → Fin (G.maxDegree + 2)) (ce : G.edgeSet → Fin (G.maxDegree + 2)),
        IsTotalColoring G cv ce

/-- Total Colouring Conjecture for `Δ ≥ 6` (open). -/
def H2 : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj],
    6 ≤ G.maxDegree →
      ∃ (cv : V → Fin (G.maxDegree + 2)) (ce : G.edgeSet → Fin (G.maxDegree + 2)),
        IsTotalColoring G cv ce

/-- Lower bound: a total colouring of a nonempty graph uses at least `Δ + 1` colours. -/
theorem lower_bound {V : Type} [Fintype V] [Nonempty V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {k : ℕ} (cv : V → Fin k) (ce : G.edgeSet → Fin k)
    (h : IsTotalColoring G cv ce) : G.maxDegree + 1 ≤ k := by
  obtain ⟨v, hv⟩ := G.exists_maximal_degree_vertex
  have hadj : ∀ w : G.neighborFinset v, s(v, w.1) ∈ G.edgeSet := fun w =>
    (SimpleGraph.mem_edgeSet G).2 ((G.mem_neighborFinset v w.1).1 w.2)
  let g : Option (G.neighborFinset v) → Fin k := fun o =>
    match o with
    | none => cv v
    | some w => ce ⟨s(v, w.1), hadj w⟩
  have hg : Function.Injective g := by
    rintro (_ | w) (_ | w') heq
    · rfl
    · exact absurd heq.symm (h.2.2 ⟨s(v, w'.1), hadj w'⟩ v (Sym2.mem_mk_left _ _))
    · exact absurd heq (h.2.2 ⟨s(v, w.1), hadj w⟩ v (Sym2.mem_mk_left _ _))
    · by_contra hne
      refine h.2.1 ⟨s(v, w.1), hadj w⟩ ⟨s(v, w'.1), hadj w'⟩ ?_
        ⟨v, Sym2.mem_mk_left _ _, Sym2.mem_mk_left _ _⟩ heq
      intro he
      apply hne
      have h1 : s(v, w.1) = s(v, w'.1) := congrArg Subtype.val he
      have h2 : w.1 = w'.1 := (Sym2.congr_right).1 h1
      exact congrArg some (Subtype.ext h2)
  have hc := Fintype.card_le_of_injective g hg
  rw [Fintype.card_option, Fintype.card_coe, SimpleGraph.card_neighborFinset_eq_degree,
    Fintype.card_fin] at hc
  omega

/-- In a graph with `Δ ≤ 1`, two neighbours of a vertex coincide. -/
theorem nbr_unique {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hΔ : G.maxDegree ≤ 1) {u a b : V} (ha : G.Adj u a) (hb : G.Adj u b) : a = b := by
  have hd : (G.neighborFinset u).card ≤ 1 := by
    rw [SimpleGraph.card_neighborFinset_eq_degree]
    exact (G.degree_le_maxDegree u).trans hΔ
  exact Finset.card_le_one.1 hd a ((G.mem_neighborFinset u a).2 ha) b
    ((G.mem_neighborFinset u b).2 hb)

/-- The conjecture's upper bound for `Δ ≤ 1`: an explicit `(Δ + 2)`-total colouring. -/
theorem small_delta {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hΔ : G.maxDegree ≤ 1) :
    ∃ (cv : V → Fin (G.maxDegree + 2)) (ce : G.edgeSet → Fin (G.maxDegree + 2)),
      IsTotalColoring G cv ce := by
  classical
  let e := Fintype.equivFin V
  let cv : V → Fin (G.maxDegree + 2) := fun v =>
    if ∃ w, G.Adj v w ∧ e w < e v then ⟨1, by omega⟩ else ⟨0, by omega⟩
  let ce : G.edgeSet → Fin (G.maxDegree + 2) := fun _ => ⟨G.maxDegree + 1, by omega⟩
  -- an edge forces `Δ ≥ 1`
  have hpos : ∀ u v : V, G.Adj u v → 1 ≤ G.maxDegree := by
    intro u v huv
    have h1 : 0 < G.degree u := by
      rw [← SimpleGraph.card_neighborFinset_eq_degree]
      exact Finset.card_pos.2 ⟨v, (G.mem_neighborFinset u v).2 huv⟩
    exact h1.trans_le (G.degree_le_maxDegree u)
  -- if `e u < e v` and `u ~ v` then `cv u = 0` and `cv v = 1`
  have key : ∀ u v : V, G.Adj u v → e u < e v → cv u ≠ cv v := by
    intro u v huv hlt
    have hv : cv v = ⟨1, by omega⟩ := if_pos ⟨u, huv.symm, hlt⟩
    have hu : cv u = ⟨0, by omega⟩ := by
      refine if_neg ?_
      rintro ⟨w, huw, hwu⟩
      have := nbr_unique G hΔ huw huv
      subst this
      exact absurd (hlt.trans hwu) (lt_irrefl _)
    rw [hu, hv]
    intro h01
    exact absurd (congrArg Fin.val h01) (by simp)
  refine ⟨cv, ce, ?_, ?_, ?_⟩
  · intro u v huv
    rcases lt_trichotomy (e u) (e v) with hlt | heq | hgt
    · exact key u v huv hlt
    · exact absurd (e.injective heq ▸ huv) (G.irrefl)
    · exact fun h => key v u huv.symm hgt h.symm
  · rintro ⟨x, hx⟩ ⟨y, hy⟩ hne ⟨v, hvx, hvy⟩
    exfalso
    apply hne
    obtain ⟨a, rfl⟩ := (Sym2.mem_iff_exists).1 hvx
    obtain ⟨b, rfl⟩ := (Sym2.mem_iff_exists).1 hvy
    have hab : a = b := nbr_unique G hΔ ((SimpleGraph.mem_edgeSet G).1 hx)
      ((SimpleGraph.mem_edgeSet G).1 hy)
    subst hab
    rfl
  · rintro ⟨x, hx⟩ v hv
    obtain ⟨a, rfl⟩ := (Sym2.mem_iff_exists).1 hv
    have h1 := hpos v a ((SimpleGraph.mem_edgeSet G).1 hx)
    intro h
    have h2 := congrArg Fin.val h
    have h3 : (cv v).val ≤ 1 := by
      simp only [cv]
      split_ifs <;> simp
    have h4 : (ce ⟨s(v, a), hx⟩).val = G.maxDegree + 1 := rfl
    omega


theorem colour2 (p q cw r : Fin 4) : ∃ cu a b c : Fin 4, cu ≠ p ∧ cu ≠ q ∧ a ≠ cu ∧ a ≠ q ∧
    b ≠ cw ∧ b ≠ r ∧ a ≠ b ∧ c ≠ cu ∧ c ≠ cw ∧ c ≠ a ∧ c ≠ b := by
  fin_cases p <;> fin_cases q <;> fin_cases cw <;> fin_cases r <;> decide

theorem colour1 (cu q : Fin 4) : ∃ a c : Fin 4, a ≠ cu ∧ a ≠ q ∧ c ≠ cu ∧ c ≠ a := by
  fin_cases cu <;> fin_cases q <;> decide

theorem one_nbr {V : Type} (G : SimpleGraph V) (S : Finset V) (cv : V → Fin 4)
    (ce : Sym2 V → Fin 4) (u : V) (huniq : ∀ y y', (G.Adj u y ∧ u ∈ S ∧ y ∈ S) → (G.Adj u y' ∧ u ∈ S ∧ y' ∈ S) → y = y') :
    ∃ p q : Fin 4, ∀ y, (G.Adj u y ∧ u ∈ S ∧ y ∈ S) → cv y = p ∧ ce s(u, y) = q := by
  by_cases h : ∃ y, (G.Adj u y ∧ u ∈ S ∧ y ∈ S)
  · obtain ⟨y0, hy0⟩ := h
    exact ⟨cv y0, ce s(u, y0), fun y hy => by rw [huniq y y0 hy hy0]; exact ⟨rfl, rfl⟩⟩
  · exact ⟨0, 0, fun y hy => absurd ⟨y, hy⟩ h⟩

theorem sym2_ne {V : Type} {x y v z : V} (hx : x ≠ v) (hy : y ≠ v) : s(x, y) ≠ s(v, z) := by
  intro h
  rcases Sym2.eq_iff.1 h with h | h
  · exact hx h.1
  · exact hy h.2

theorem step {V : Type} [DecidableEq V] (G : SimpleGraph V)
    (hdeg : ∀ x y z t, G.Adj x y → G.Adj x z → G.Adj x t → y = z ∨ y = t ∨ z = t)
    (S : Finset V) (v : V) (hv : v ∉ S) (cv : V → Fin 4) (ce : Sym2 V → Fin 4)
    (h : ((∀ x y, G.Adj x y ∧ x ∈ S ∧ y ∈ S → cv x ≠ cv y) ∧
      (∀ x y z, G.Adj x y ∧ x ∈ S ∧ y ∈ S → G.Adj x z ∧ x ∈ S ∧ z ∈ S → y ≠ z →
        ce s(x, y) ≠ ce s(x, z)) ∧
      (∀ x y, G.Adj x y ∧ x ∈ S ∧ y ∈ S → ce s(x, y) ≠ cv x))) : ∃ (cv' : V → Fin 4) (ce' : Sym2 V → Fin 4), ((∀ x y, G.Adj x y ∧ x ∈ (insert v S) ∧ y ∈ (insert v S) → cv' x ≠ cv' y) ∧
      (∀ x y z, G.Adj x y ∧ x ∈ (insert v S) ∧ y ∈ (insert v S) → G.Adj x z ∧ x ∈ (insert v S) ∧ z ∈ (insert v S) → y ≠ z →
        ce' s(x, y) ≠ ce' s(x, z)) ∧
      (∀ x y, G.Adj x y ∧ x ∈ (insert v S) ∧ y ∈ (insert v S) → ce' s(x, y) ≠ cv' x)) := by
  classical
  obtain ⟨h1, h2, h3⟩ := h
  have uniq : ∀ u, G.Adj u v → ∀ y y', (G.Adj u y ∧ u ∈ S ∧ y ∈ S) → (G.Adj u y' ∧ u ∈ S ∧ y' ∈ S) → y = y' := by
    intro u huv y y' hy hy'
    rcases hdeg u v y y' huv hy.1 hy'.1 with h | h | h
    · exact absurd (h ▸ hy.2.2) hv
    · exact absurd (h ▸ hy'.2.2) hv
    · exact h
  have hvS : ∀ x, x ∈ S → x ≠ v := fun x hx h => hv (h ▸ hx)
  -- an edge of the new relation avoiding `v` is an old edge
  have old : ∀ x y, (G.Adj x y ∧ x ∈ (insert v S) ∧ y ∈ (insert v S)) → x ≠ v → y ≠ v → (G.Adj x y ∧ x ∈ S ∧ y ∈ S) := by
    rintro x y ⟨hxy, hx, hy⟩ hxv hyv
    exact ⟨hxy, (Finset.mem_insert.1 hx).resolve_left hxv,
      (Finset.mem_insert.1 hy).resolve_left hyv⟩
  -- a new neighbour of `v` lies in `S`
  have nbrS : ∀ y, (G.Adj v y ∧ v ∈ (insert v S) ∧ y ∈ (insert v S)) → y ∈ S := by
    rintro y ⟨hxy, _, hy⟩
    exact (Finset.mem_insert.1 hy).resolve_left (fun h => G.ne_of_adj hxy h.symm)
  by_cases hA : ∃ u, u ∈ S ∧ G.Adj v u
  · obtain ⟨u, huS, hvu⟩ := hA
    have huv : u ≠ v := hvS u huS
    obtain ⟨p, q, hpq⟩ := one_nbr G S cv ce u (uniq u hvu.symm)
    by_cases hB : ∃ w, w ∈ S ∧ G.Adj v w ∧ w ≠ u
    · -- two neighbours `u`, `w`: recolour `u`
      obtain ⟨w, hwS, hvw, hwu⟩ := hB
      have hwv : w ≠ v := hvS w hwS
      obtain ⟨p', r, hr⟩ := one_nbr G S cv ce w (uniq w hvw.symm)
      have hN : ∀ y, (G.Adj v y ∧ v ∈ (insert v S) ∧ y ∈ (insert v S)) → y = u ∨ y = w := by
        intro y hy
        rcases hdeg v u w y hvu hvw hy.1 with h | h | h
        · exact absurd h hwu.symm
        · exact Or.inl h.symm
        · exact Or.inr h.symm
      obtain ⟨cu, a, b, c, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11⟩ :=
        colour2 p q (cv w) r
      obtain ⟨cv', hcv'⟩ : ∃ f : V → Fin 4,
          f = fun x => if x = v then c else if x = u then cu else cv x := ⟨_, rfl⟩
      obtain ⟨ce', hce'⟩ : ∃ f : Sym2 V → Fin 4,
          f = fun e => if e = s(v, u) then a else if e = s(v, w) then b else ce e := ⟨_, rfl⟩
      have cvv : cv' v = c := by rw [hcv']; simp
      have cvu : cv' u = cu := by rw [hcv']; simp [huv]
      have cvo : ∀ x, x ≠ v → x ≠ u → cv' x = cv x := by
        intro x hxv hxu; rw [hcv']; simp [hxv, hxu]
      have hvwu : s(v, w) ≠ s(v, u) := fun h => hwu (Sym2.congr_right.1 h)
      have cevu : ce' s(v, u) = a := by rw [hce']; simp
      have ceuv : ce' s(u, v) = a := by rw [Sym2.eq_swap]; exact cevu
      have cevw : ce' s(v, w) = b := by rw [hce']; simp [hvwu]
      have cewv : ce' s(w, v) = b := by rw [Sym2.eq_swap]; exact cevw
      have ceo : ∀ x y, x ≠ v → y ≠ v → ce' s(x, y) = ce s(x, y) := by
        intro x y hxv hyv
        rw [hce']
        simp only [if_neg (sym2_ne hxv hyv)]
      have nbrv : ∀ x, (G.Adj x v ∧ x ∈ (insert v S) ∧ v ∈ (insert v S)) → x = u ∨ x = w := by
        rintro x ⟨hxy, hx, hy⟩
        exact hN x ⟨hxy.symm, hy, hx⟩
      refine ⟨cv', ce', ?_, ?_, ?_⟩
      · intro x y hxy
        by_cases hxv : x = v
        · rw [hxv] at hxy ⊢
          rcases hN y hxy with hy | hy <;> rw [hy]
          · rw [cvv, cvu]; exact k8
          · rw [cvv, cvo w hwv hwu]; exact k9
        by_cases hyv : y = v
        · rw [hyv] at hxy ⊢
          rcases nbrv x hxy with hx | hx <;> rw [hx]
          · rw [cvv, cvu]; exact k8.symm
          · rw [cvv, cvo w hwv hwu]; exact k9.symm
        have hS := old x y hxy hxv hyv
        by_cases hxu : x = u
        · rw [hxu] at hS ⊢
          have hyu : y ≠ u := fun h => G.ne_of_adj hS.1 h.symm
          rw [cvu, cvo y hyv hyu, (hpq y hS).1]; exact k1
        by_cases hyu : y = u
        · rw [hyu] at hS ⊢
          have hS' : (G.Adj u x ∧ u ∈ S ∧ x ∈ S) := ⟨hS.1.symm, hS.2.2, hS.2.1⟩
          rw [cvu, cvo x hxv hxu, (hpq x hS').1]; exact k1.symm
        rw [cvo x hxv hxu, cvo y hyv hyu]; exact h1 x y hS
      · intro x y z hxy hxz hyz
        by_cases hxv : x = v
        · rw [hxv] at hxy hxz ⊢
          rcases hN y hxy with hy | hy <;> rcases hN z hxz with hz | hz <;> rw [hy, hz] at hyz ⊢
          · exact absurd rfl hyz
          · rw [cevu, cevw]; exact k7
          · rw [cevu, cevw]; exact k7.symm
          · exact absurd rfl hyz
        by_cases hyv : y = v
        · have hzv : z ≠ v := fun h => hyz (hyv.trans h.symm)
          have hzS := old x z hxz hxv hzv
          rw [hyv] at hxy ⊢
          rw [ceo x z hxv hzv]
          rcases nbrv x hxy with hx | hx
          · rw [hx] at hzS ⊢; rw [ceuv, (hpq z hzS).2]; exact k4
          · rw [hx] at hzS ⊢; rw [cewv, (hr z hzS).2]; exact k6
        by_cases hzv : z = v
        · have hyS := old x y hxy hxv hyv
          rw [hzv] at hxz ⊢
          rw [ceo x y hxv hyv]
          rcases nbrv x hxz with hx | hx
          · rw [hx] at hyS ⊢; rw [ceuv, (hpq y hyS).2]; exact k4.symm
          · rw [hx] at hyS ⊢; rw [cewv, (hr y hyS).2]; exact k6.symm
        rw [ceo x y hxv hyv, ceo x z hxv hzv]
        exact h2 x y z (old x y hxy hxv hyv) (old x z hxz hxv hzv) hyz
      · intro x y hxy
        by_cases hxv : x = v
        · rw [hxv] at hxy ⊢
          rcases hN y hxy with hy | hy <;> rw [hy]
          · rw [cevu, cvv]; exact k10.symm
          · rw [cevw, cvv]; exact k11.symm
        by_cases hyv : y = v
        · rw [hyv] at hxy ⊢
          rcases nbrv x hxy with hx | hx <;> rw [hx]
          · rw [ceuv, cvu]; exact k3
          · rw [cewv, cvo w hwv hwu]; exact k5
        have hS := old x y hxy hxv hyv
        rw [ceo x y hxv hyv]
        by_cases hxu : x = u
        · rw [hxu] at hS ⊢
          rw [cvu, (hpq y hS).2]; exact k2.symm
        rw [cvo x hxv hxu]; exact h3 x y hS
    · -- one neighbour `u`
      have hN : ∀ y, (G.Adj v y ∧ v ∈ (insert v S) ∧ y ∈ (insert v S)) → y = u := by
        intro y hy
        by_contra hyu
        exact hB ⟨y, nbrS y hy, hy.1, hyu⟩
      obtain ⟨a, c, k1, k2, k3, k4⟩ := colour1 (cv u) q
      obtain ⟨cv', hcv'⟩ : ∃ f : V → Fin 4,
          f = fun x => if x = v then c else cv x := ⟨_, rfl⟩
      obtain ⟨ce', hce'⟩ : ∃ f : Sym2 V → Fin 4,
          f = fun e => if e = s(v, u) then a else ce e := ⟨_, rfl⟩
      have cvv : cv' v = c := by rw [hcv']; simp
      have cvo : ∀ x, x ≠ v → cv' x = cv x := by
        intro x hxv; rw [hcv']; simp [hxv]
      have cevu : ce' s(v, u) = a := by rw [hce']; simp
      have ceuv : ce' s(u, v) = a := by rw [Sym2.eq_swap]; exact cevu
      have ceo : ∀ x y, x ≠ v → y ≠ v → ce' s(x, y) = ce s(x, y) := by
        intro x y hxv hyv
        rw [hce']
        simp only [if_neg (sym2_ne hxv hyv)]
      have nbrv : ∀ x, (G.Adj x v ∧ x ∈ (insert v S) ∧ v ∈ (insert v S)) → x = u := by
        rintro x ⟨hxy, hx, hy⟩
        exact hN x ⟨hxy.symm, hy, hx⟩
      refine ⟨cv', ce', ?_, ?_, ?_⟩
      · intro x y hxy
        by_cases hxv : x = v
        · rw [hxv] at hxy ⊢
          rw [hN y hxy, cvv, cvo u huv]; exact k3
        by_cases hyv : y = v
        · rw [hyv] at hxy ⊢
          rw [nbrv x hxy, cvv, cvo u huv]; exact k3.symm
        rw [cvo x hxv, cvo y hyv]; exact h1 x y (old x y hxy hxv hyv)
      · intro x y z hxy hxz hyz
        by_cases hxv : x = v
        · rw [hxv] at hxy hxz
          exact absurd ((hN y hxy).trans (hN z hxz).symm) hyz
        by_cases hyv : y = v
        · have hzv : z ≠ v := fun h => hyz (hyv.trans h.symm)
          have hzS := old x z hxz hxv hzv
          rw [hyv] at hxy ⊢
          rw [ceo x z hxv hzv, nbrv x hxy]
          rw [nbrv x hxy] at hzS
          rw [ceuv, (hpq z hzS).2]; exact k2
        by_cases hzv : z = v
        · have hyS := old x y hxy hxv hyv
          rw [hzv] at hxz ⊢
          rw [ceo x y hxv hyv, nbrv x hxz]
          rw [nbrv x hxz] at hyS
          rw [ceuv, (hpq y hyS).2]; exact k2.symm
        rw [ceo x y hxv hyv, ceo x z hxv hzv]
        exact h2 x y z (old x y hxy hxv hyv) (old x z hxz hxv hzv) hyz
      · intro x y hxy
        by_cases hxv : x = v
        · rw [hxv] at hxy ⊢
          rw [hN y hxy, cevu, cvv]; exact k4.symm
        by_cases hyv : y = v
        · rw [hyv] at hxy ⊢
          rw [nbrv x hxy, ceuv, cvo u huv]; exact k1
        rw [ceo x y hxv hyv, cvo x hxv]; exact h3 x y (old x y hxy hxv hyv)
  · -- no neighbour: keep the colouring
    have old' : ∀ x y, (G.Adj x y ∧ x ∈ (insert v S) ∧ y ∈ (insert v S)) → (G.Adj x y ∧ x ∈ S ∧ y ∈ S) := by
      intro x y hxy
      have hxv : x ≠ v := by
        intro h
        rw [h] at hxy
        exact hA ⟨y, nbrS y hxy, hxy.1⟩
      have hyv : y ≠ v := by
        intro h
        rw [h] at hxy
        exact hA ⟨x, nbrS x ⟨hxy.1.symm, hxy.2.2, hxy.2.1⟩, hxy.1.symm⟩
      exact old x y hxy hxv hyv
    exact ⟨cv, ce, fun x y hxy => h1 x y (old' x y hxy),
      fun x y z hxy hxz hyz => h2 x y z (old' x y hxy) (old' x z hxz) hyz,
      fun x y hxy => h3 x y (old' x y hxy)⟩

/-- Every graph in which each vertex has at most two neighbours has a 4-total colouring
(in the `Sym2`-indexed form). -/
theorem tc_all {V : Type} [Fintype V] (G : SimpleGraph V)
    (hdeg : ∀ x y z t, G.Adj x y → G.Adj x z → G.Adj x t → y = z ∨ y = t ∨ z = t) :
    ∃ (cv : V → Fin 4) (ce : Sym2 V → Fin 4), ((∀ x y, G.Adj x y ∧ x ∈ Finset.univ ∧ y ∈ Finset.univ → cv x ≠ cv y) ∧
      (∀ x y z, G.Adj x y ∧ x ∈ Finset.univ ∧ y ∈ Finset.univ → G.Adj x z ∧ x ∈ Finset.univ ∧ z ∈ Finset.univ → y ≠ z →
        ce s(x, y) ≠ ce s(x, z)) ∧
      (∀ x y, G.Adj x y ∧ x ∈ Finset.univ ∧ y ∈ Finset.univ → ce s(x, y) ≠ cv x)) := by
  classical
  induction (Finset.univ : Finset V) using Finset.induction_on with
  | empty =>
    refine ⟨fun _ => 0, fun _ => 0, ?_, ?_, ?_⟩
    · intro x y hxy; exact absurd hxy.2.1 (Finset.notMem_empty x)
    · intro x y z hxy; exact absurd hxy.2.1 (Finset.notMem_empty x)
    · intro x y hxy; exact absurd hxy.2.1 (Finset.notMem_empty x)
  | insert v S hv ih =>
    obtain ⟨cv, ce, h⟩ := ih
    exact step G hdeg S v hv cv ce h

/-- Three neighbours of a vertex in a graph with `Δ ≤ 2` are not distinct. -/
theorem hdeg_of_maxDegree_le_two {V : Type} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hΔ : G.maxDegree ≤ 2) :
    ∀ x y z t, G.Adj x y → G.Adj x z → G.Adj x t → y = z ∨ y = t ∨ z = t := by
  classical
  intro x y z t hy hz ht
  by_contra hc
  push Not at hc
  obtain ⟨hyz, hyt, hzt⟩ := hc
  have hsub : ({y, z, t} : Finset V) ⊆ G.neighborFinset x := by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rw [SimpleGraph.mem_neighborFinset]
    rcases ha with rfl | rfl | rfl <;> assumption
  have h3 : ({y, z, t} : Finset V).card = 3 := Finset.card_eq_three.2 ⟨y, z, t, hyz, hyt, hzt, rfl⟩
  have := Finset.card_le_card hsub
  rw [h3, SimpleGraph.card_neighborFinset_eq_degree] at this
  have := G.degree_le_maxDegree x
  omega

/-- The Total Colouring Conjecture for `Δ ≤ 2`: a 4-total colouring exists. -/
theorem coloring_four_of_maxDegree_le_two {V : Type} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hΔ : G.maxDegree ≤ 2) :
    ∃ (cv : V → Fin 4) (ce : G.edgeSet → Fin 4), IsTotalColoring G cv ce := by
  obtain ⟨cv, ce, h1, h2, h3⟩ := tc_all G (hdeg_of_maxDegree_le_two G hΔ)
  have hR : ∀ x y, G.Adj x y → (G.Adj x y ∧ x ∈ Finset.univ ∧ y ∈ Finset.univ) :=
    fun x y hxy => ⟨hxy, Finset.mem_univ x, Finset.mem_univ y⟩
  refine ⟨cv, fun e => ce e.1, ?_, ?_, ?_⟩
  · intro u v huv
    exact h1 u v (hR u v huv)
  · rintro e f hef ⟨v, hve, hvf⟩
    obtain ⟨a, ha⟩ := Sym2.mem_iff_exists.1 hve
    obtain ⟨b, hb⟩ := Sym2.mem_iff_exists.1 hvf
    have hea : G.Adj v a := by have := e.2; rw [ha] at this; exact this
    have heb : G.Adj v b := by have := f.2; rw [hb] at this; exact this
    have hab : a ≠ b := by
      intro hab
      apply hef
      apply Subtype.ext
      rw [ha, hb, hab]
    show ce e.1 ≠ ce f.1
    rw [ha, hb]
    exact h2 v a b (hR v a hea) (hR v b heb) hab
  · intro e v hve
    obtain ⟨a, ha⟩ := Sym2.mem_iff_exists.1 hve
    have hea : G.Adj v a := by have := e.2; rw [ha] at this; exact this
    show ce e.1 ≠ cv v
    rw [ha]
    exact h3 v a (hR v a hea)


/-- `Δ = 2`: a `(Δ + 2)`-total colouring. -/
theorem delta_two {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hΔ : G.maxDegree = 2) :
    ∃ (cv : V → Fin (G.maxDegree + 2)) (ce : G.edgeSet → Fin (G.maxDegree + 2)),
      IsTotalColoring G cv ce := by
  obtain ⟨cv, ce, h1, h2, h3⟩ := coloring_four_of_maxDegree_le_two G hΔ.le
  have h4 : 4 ≤ G.maxDegree + 2 := by omega
  refine ⟨fun v => Fin.castLE h4 (cv v), fun e => Fin.castLE h4 (ce e), ?_, ?_, ?_⟩
  · intro u v huv hc
    exact h1 u v huv (Fin.castLE_injective h4 hc)
  · intro e f hef hs hc
    exact h2 e f hef hs (Fin.castLE_injective h4 hc)
  · intro e v hv hc
    exact h3 e v hv (Fin.castLE_injective h4 hc)

theorem main : H1 → H2 → type_of% @OMA.S_opg_behzads_conjecture.main := by
  intro h1 h2 V _ _ G _
  have hcol : ∃ (cv : V → Fin (G.maxDegree + 2)) (ce : G.edgeSet → Fin (G.maxDegree + 2)),
      IsTotalColoring G cv ce := by
    by_cases hA : G.maxDegree ≤ 1
    · exact small_delta G hA
    · by_cases hT : G.maxDegree = 2
      · exact delta_two G hT
      · by_cases hB : G.maxDegree ≤ 5
        · exact h1 V G (by omega) hB
        · exact h2 V G (by omega)
  obtain ⟨cv, ce, hc⟩ := hcol
  have hmemS : G.maxDegree + 2 ∈
      {k : ℕ | ∃ (cv : V → Fin k) (ce : G.edgeSet → Fin k), IsTotalColoring G cv ce} :=
    ⟨cv, ce, hc⟩
  have hle : totalChromaticNumber G ≤ G.maxDegree + 2 := Nat.sInf_le hmemS
  obtain ⟨cv', ce', hc'⟩ := Nat.sInf_mem ⟨_, hmemS⟩
  have hge : G.maxDegree + 1 ≤ totalChromaticNumber G := lower_bound G cv' ce' hc'
  omega

end OMA.R_opg_behzads_conjecture_R2
