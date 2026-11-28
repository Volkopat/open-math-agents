import OMAReductions.R_Erdos604_erdos_604_variants_average_R2_H2_R1_H1_R1
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# Proof of Erdos604.erdos_604.variants.average.R2.H2.R1.H1.R1.H1

Proves the Crossing Number Inequality (Ajtai-Chvatal-Newborn-Szemeredi / Leighton)
for simple graphs drawn by injective continuous curves (in particular circular arcs)
in `ℝ²`, completely elementarily without external topology axioms:
1. Sweep-line vertical slab decomposition for crossing-free polygonal subdivisions
   in `ℝ × ℝ`, yielding Euler's inequality `F ≥ 1 + |E| - |A|` and mod-2 boundary
   evenness `3 * (F - 1) ≤ 2 * |E|`, hence `|E| ≤ 3 * |A|`.
2. Crossing-free continuous injective curve drawings approximate to simple polygonal
   subdivisions (radial balls around vertices + loop erasure), hence `|E| ≤ 3 * |A|`.
3. Adjacent-crossing elimination on continuous injective curve drawings via the
   4-point circle-chord shortcut in small balls `B(p, ε)` + loop excision, preserving
   finiteness and strictly decreasing total crossings `X`.
4. Finite `Finset.powersetCard` averaging over vertex subsets gives the Crossing Lemma
   `|E| ≤ K * |A| ∨ |E| ^ 3 ≤ K * |A| ^ 2 * X`.
-/

namespace OMA.Erdos604CrossingLemma

open Finset SimpleGraph
open scoped Classical

/- ### Part 1: Combinatorial graph-component and Eulerian parity helpers -/

/-- Removing an edge from a finite `SimpleGraph` increases the number of connected components
by at most 1; hence `#ConnComp ≥ #V - #E`. -/
private lemma card_connectedComponent_ge_sub_edges
    {α : Type*} [Fintype α] [DecidableEq α] (G : SimpleGraph α) [DecidableRel G.Adj] :
    Fintype.card α ≤ Fintype.card G.ConnectedComponent + G.edgeFinset.card := by
  classical
  -- Induction on the number of edges in G
  suffices h : ∀ (m : ℕ) (H : SimpleGraph α) [DecidableRel H.Adj],
      H.edgeFinset.card = m →
      Fintype.card α ≤ Fintype.card H.ConnectedComponent + m from
    h G.edgeFinset.card G rfl
  intro m
  induction m with
  | zero =>
    intro H _ hm
    have hbot : H = ⊥ := by
      ext u v
      simp only [SimpleGraph.bot_adj, iff_false]
      intro hadj
      have hmem : s(u, v) ∈ H.edgeFinset := SimpleGraph.mem_edgeFinset.mpr hadj
      have hpos : 0 < H.edgeFinset.card := Finset.card_pos.mpr ⟨s(u, v), hmem⟩
      omega
    subst hbot
    have hinj : Function.Injective (⊥ : SimpleGraph α).connectedComponentMk := by
      intro u v h
      have hr : (⊥ : SimpleGraph α).Reachable u v :=
        SimpleGraph.ConnectedComponent.exact h
      obtain ⟨w⟩ := hr
      cases w with
      | nil => rfl
      | cons hadj _ => exact False.elim hadj
    have hle := Fintype.card_le_of_injective _ hinj
    omega
  | succ m ih =>
    intro H _ hm
    have hne : H.edgeFinset.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨e, he⟩ := hne
    induction e using Sym2.ind with
    | _ u v =>
      have huv : H.Adj u v := SimpleGraph.mem_edgeFinset.mp he
      let H' : SimpleGraph α := H.deleteEdges {s(u, v)}
      have hcard' : H'.edgeFinset.card = m := by
        have h1 : H'.edgeFinset = H.edgeFinset.erase s(u, v) := by
          ext e'
          simp only [H', SimpleGraph.mem_edgeFinset, SimpleGraph.edgeSet_deleteEdges,
            Set.mem_sdiff, Set.mem_singleton_iff, Finset.mem_erase]
          tauto
        rw [h1, Finset.card_erase_of_mem he, hm]
        omega
      have hih := ih H' hcard'
      -- Map H'.ConnectedComponent → H.ConnectedComponent; at most 2 components merge!
      let φ : H'.ConnectedComponent → H.ConnectedComponent :=
        SimpleGraph.ConnectedComponent.map (SimpleGraph.Hom.ofLE (SimpleGraph.deleteEdges_le _))
      -- Every vertex in α is reachable in H' from its H'-component;
      -- any two H'-components mapping to the same H-component must either be equal
      -- or be the two components of u and v!
      have hfiber : ∀ c₁ c₂ : H'.ConnectedComponent,
          φ c₁ = φ c₂ →
          c₁ = c₂ ∨
          (c₁ = H'.connectedComponentMk u ∧ c₂ = H'.connectedComponentMk v) ∨
          (c₁ = H'.connectedComponentMk v ∧ c₂ = H'.connectedComponentMk u) := by
        intro c₁ c₂ hmap
        induction c₁ using SimpleGraph.ConnectedComponent.ind with | _ a =>
        induction c₂ using SimpleGraph.ConnectedComponent.ind with | _ b =>
        have hr : H.Reachable a b := SimpleGraph.ConnectedComponent.exact hmap
        obtain ⟨w⟩ := hr
        -- Walk in H from a to b: if it never uses {u,v}, then H'.Reachable a b;
        -- otherwise split at first and last use of {u,v}!
        have hwalk : ∀ {x y : α} (p : H.Walk x y),
            H'.Reachable x y ∨
            (H'.Reachable x u ∧ H'.Reachable v y) ∨
            (H'.Reachable x v ∧ H'.Reachable u y) := by
          intro x y p
          induction p with
          | nil => exact Or.inl (SimpleGraph.Reachable.refl _)
          | @cons x z y hxz p' ihp =>
            by_cases hsame : s(x, z) = s(u, v)
            · have hxz_uv : (x = u ∧ z = v) ∨ (x = v ∧ z = u) := Sym2.eq_iff.mp hsame
              rcases hxz_uv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
              · rcases ihp with h1 | ⟨h1, h2⟩ | ⟨h1, h2⟩
                · exact Or.inr (Or.inl ⟨SimpleGraph.Reachable.refl _, h1⟩)
                · exact Or.inr (Or.inl ⟨SimpleGraph.Reachable.refl _, h2⟩)
                · exact Or.inl h2
              · rcases ihp with h1 | ⟨h1, h2⟩ | ⟨h1, h2⟩
                · exact Or.inr (Or.inr ⟨SimpleGraph.Reachable.refl _, h1⟩)
                · exact Or.inl h2
                · exact Or.inr (Or.inr ⟨SimpleGraph.Reachable.refl _, h2⟩)
            · have hxz' : H'.Adj x z := by
                simp only [H', SimpleGraph.deleteEdges_adj, Set.mem_singleton_iff]
                exact ⟨hxz, hsame⟩
              have hr1 : H'.Reachable x z := hxz'.reachable
              rcases ihp with h1 | ⟨h1, h2⟩ | ⟨h1, h2⟩
              · exact Or.inl (hr1.trans h1)
              · exact Or.inr (Or.inl ⟨hr1.trans h1, h2⟩)
              · exact Or.inr (Or.inr ⟨hr1.trans h1, h2⟩)
        rcases hwalk w with h1 | ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inl (SimpleGraph.ConnectedComponent.sound h1)
        · exact Or.inr (Or.inl ⟨SimpleGraph.ConnectedComponent.sound h1,
            SimpleGraph.ConnectedComponent.sound h2.symm⟩)
        · exact Or.inr (Or.inr ⟨SimpleGraph.ConnectedComponent.sound h1,
            SimpleGraph.ConnectedComponent.sound h2.symm⟩)
      -- Therefore Fintype.card H'.ConnectedComponent ≤ Fintype.card H.ConnectedComponent + 1
      have hcomp_le : Fintype.card H'.ConnectedComponent ≤ Fintype.card H.ConnectedComponent + 1 := by
        let cu := H'.connectedComponentMk u
        have hinj_erase : Set.InjOn φ (Finset.univ.erase cu : Set H'.ConnectedComponent) := by
          intro c₁ hc₁ c₂ hc₂ hfeq
          have h1 : c₁ ≠ cu := (Finset.mem_erase.mp hc₁).1
          have h2 : c₂ ≠ cu := (Finset.mem_erase.mp hc₂).1
          rcases hfiber c₁ c₂ hfeq with h | ⟨rfl, _⟩ | ⟨_, rfl⟩
          · exact h
          · exact (h1 rfl).elim
          · exact (h2 rfl).elim
        have hcard_img : ((Finset.univ.erase cu).image φ).card = (Finset.univ.erase cu).card :=
          Finset.card_image_of_injOn hinj_erase
        have hsub : ((Finset.univ.erase cu).image φ).card ≤ Fintype.card H.ConnectedComponent := by
          calc ((Finset.univ.erase cu).image φ).card
              ≤ (Finset.univ : Finset H.ConnectedComponent).card :=
                Finset.card_le_card (Finset.subset_univ _)
            _ = Fintype.card H.ConnectedComponent := Finset.card_univ
        have herase : (Finset.univ.erase cu).card + 1 = Fintype.card H'.ConnectedComponent := by
          rw [Finset.card_erase_of_mem (Finset.mem_univ cu), Finset.card_univ]
          have hpos : 0 < Fintype.card H'.ConnectedComponent :=
            Fintype.card_pos_iff.mpr ⟨cu⟩
          omega
        omega
      omega

/-- Parity telescope: in `Fin (k + 1) → Bool`, the number of adjacent flips `f i ≠ f (i+1)`
has the same parity as `f 0 ≠ f k`. -/
private lemma count_flips_mod_two (k : ℕ) (f : Fin (k + 1) → Bool) :
    ((Finset.univ : Finset (Fin k)).filter (fun i => f i.castSucc ≠ f i.succ)).card % 2 =
      if f 0 ≠ f (Fin.last k) then 1 else 0 := by
  induction k with
  | zero =>
    simp
  | succ k ih =>
    let f' : Fin (k + 1) → Bool := fun j => f j.castSucc
    have hsplit :
        ((Finset.univ : Finset (Fin (k + 1))).filter (fun i => f i.castSucc ≠ f i.succ)).card =
        ((Finset.univ : Finset (Fin k)).filter (fun i => f' i.castSucc ≠ f' i.succ)).card +
        (if f (Fin.last k).castSucc ≠ f (Fin.last (k + 1)) then 1 else 0) := by
      simp_rw [Finset.card_filter]
      rw [Fin.sum_univ_castSucc]
      have h1 : (Fin.last k).succ = Fin.last (k + 1) := by ext; simp
      rw [h1]
      congr 1
    have hih := ih f'
    have hf0 : f' 0 = f 0 := rfl
    have hfl : f' (Fin.last k) = f (Fin.last k).castSucc := rfl
    rw [hf0, hfl] at hih
    rw [hsplit]
    cases hf0_v : f 0 <;> cases hfm_v : f (Fin.last k).castSucc <;> cases hfl_v : f (Fin.last (k + 1)) <;>
      simp only [hf0_v, hfm_v, ne_eq, Bool.false_eq_true, Bool.true_eq_false,
        not_true_eq_false, not_false_eq_true, ite_true, ite_false] at hih ⊢ <;> omega

/-- Every nonempty simple Eulerian graph (even degree at every vertex) has at least 3 edges. -/
private lemma card_ge_three_of_simple_eulerian
    {α : Type*} [DecidableEq α] (A : Finset α) (E : Finset ℕ)
    (uEnd vEnd : ℕ → α)
    (hEnd_mem : ∀ i ∈ E, uEnd i ∈ A ∧ vEnd i ∈ A ∧ uEnd i ≠ vEnd i)
    (hEnd_simple : Set.InjOn (fun i => ({uEnd i, vEnd i} : Finset α)) (E : Set ℕ))
    (hne : E.Nonempty)
    (heven : ∀ v ∈ A, Even (E.filter (fun i => uEnd i = v ∨ vEnd i = v)).card) :
    3 ≤ E.card := by
  obtain ⟨e₁, he₁⟩ := hne
  obtain ⟨hu1, hv1, huv1⟩ := hEnd_mem e₁ he₁
  have hdeg_ge2 : ∀ v ∈ A, ∀ e ∈ E, (uEnd e = v ∨ vEnd e = v) →
      ∃ e' ∈ E, e' ≠ e ∧ (uEnd e' = v ∨ vEnd e' = v) := by
    intro v hv e he hinc
    have hmem : e ∈ E.filter (fun i => uEnd i = v ∨ vEnd i = v) :=
      Finset.mem_filter.mpr ⟨he, hinc⟩
    have hpos : 0 < (E.filter (fun i => uEnd i = v ∨ vEnd i = v)).card :=
      Finset.card_pos.mpr ⟨e, hmem⟩
    obtain ⟨m, hm⟩ := heven v hv
    have hge2 : 2 ≤ (E.filter (fun i => uEnd i = v ∨ vEnd i = v)).card := by omega
    have h1 : 1 < (E.filter (fun i => uEnd i = v ∨ vEnd i = v)).card := by omega
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp h1
    by_cases hae : a = e
    · subst hae
      have hb' := Finset.mem_filter.mp hb
      exact ⟨b, hb'.1, hab.symm, hb'.2⟩
    · have ha' := Finset.mem_filter.mp ha
      exact ⟨a, ha'.1, hae, ha'.2⟩
  obtain ⟨e₂, he₂, hne21, hinc2⟩ := hdeg_ge2 (uEnd e₁) hu1 e₁ he₁ (Or.inl rfl)
  obtain ⟨e₃, he₃, hne31, hinc3⟩ := hdeg_ge2 (vEnd e₁) hv1 e₁ he₁ (Or.inr rfl)
  have hne23 : e₂ ≠ e₃ := by
    intro heq
    subst heq
    have hset : ({uEnd e₂, vEnd e₂} : Finset α) = {uEnd e₁, vEnd e₁} := by
      have hu2v2 := (hEnd_mem e₂ he₂).2.2
      rcases hinc2 with h2u | h2v <;> rcases hinc3 with h3u | h3v
      · exact (huv1 (h2u.symm.trans h3u)).elim
      · rw [h2u, h3v]
      · rw [h2v, h3u, Finset.pair_comm]
      · exact (huv1 (h2v.symm.trans h3v)).elim
    exact hne21 (hEnd_simple he₂ he₁ hset)
  have hsub : ({e₁, e₂, e₃} : Finset ℕ) ⊆ E := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> assumption
  have hcard3 : ({e₁, e₂, e₃} : Finset ℕ).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
    · simp [hne23]
    · simp [hne21.symm, hne31.symm]
  calc 3 = ({e₁, e₂, e₃} : Finset ℕ).card := hcard3.symm
    _ ≤ E.card := Finset.card_le_card hsub

/- ### Part 2: Sweep-line vertical slab decomposition for crossing-free polygonal subdivisions -/

/-- Closed line segment between two points in `ℝ × ℝ`. -/
private def pseg (p q : ℝ × ℝ) : Set (ℝ × ℝ) :=
  {r | ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ r = ((1 - t) * p.1 + t * q.1, (1 - t) * p.2 + t * q.2)}

/-- Open line segment between two points in `ℝ × ℝ`. -/
private def poseg (p q : ℝ × ℝ) : Set (ℝ × ℝ) :=
  {r | ∃ t : ℝ, 0 < t ∧ t < 1 ∧ r = ((1 - t) * p.1 + t * q.1, (1 - t) * p.2 + t * q.2)}

/-- Linear interpolation `y`-value of a non-vertical segment `(p, q)` at coordinate `x`. -/
private noncomputable def yAt (s : (ℝ × ℝ) × (ℝ × ℝ)) (x : ℝ) : ℝ :=
  s.1.2 + (x - s.1.1) / (s.2.1 - s.1.1) * (s.2.2 - s.1.2)

private lemma yAt_left {s : (ℝ × ℝ) × (ℝ × ℝ)} : yAt s s.1.1 = s.1.2 := by
  simp [yAt]

private lemma yAt_right {s : (ℝ × ℝ) × (ℝ × ℝ)} (h : s.1.1 ≠ s.2.1) : yAt s s.2.1 = s.2.2 := by
  have hne : s.2.1 - s.1.1 ≠ 0 := sub_ne_zero.mpr h.symm
  unfold yAt
  rw [div_self hne, one_mul]
  ring

private lemma mem_pseg_of_yAt {s : (ℝ × ℝ) × (ℝ × ℝ)} {x : ℝ}
    (hlt : s.1.1 < s.2.1) (hx1 : s.1.1 ≤ x) (hx2 : x ≤ s.2.1) :
    (x, yAt s x) ∈ pseg s.1 s.2 := by
  refine ⟨(x - s.1.1) / (s.2.1 - s.1.1),
    div_nonneg (sub_nonneg.mpr hx1) (sub_pos.mpr hlt).le,
    (div_le_one (sub_pos.mpr hlt)).mpr (by linarith), ?_⟩
  have hne : s.2.1 - s.1.1 ≠ 0 := (sub_pos.mpr hlt).ne'
  apply Prod.ext
  · dsimp only
    field_simp [hne]
    ring
  · dsimp only [yAt]
    field_simp [hne]
    ring

private lemma mem_poseg_of_yAt {s : (ℝ × ℝ) × (ℝ × ℝ)} {x : ℝ}
    (hlt : s.1.1 < s.2.1) (hx1 : s.1.1 < x) (hx2 : x < s.2.1) :
    (x, yAt s x) ∈ poseg s.1 s.2 := by
  refine ⟨(x - s.1.1) / (s.2.1 - s.1.1),
    div_pos (sub_pos.mpr hx1) (sub_pos.mpr hlt),
    (div_lt_one (sub_pos.mpr hlt)).mpr (by linarith), ?_⟩
  have hne : s.2.1 - s.1.1 ≠ 0 := (sub_pos.mpr hlt).ne'
  apply Prod.ext
  · dsimp only
    field_simp [hne]
    ring
  · dsimp only [yAt]
    field_simp [hne]
    ring

/-- Two affine functions whose graphs do not cross on `(a, b)` maintain strict order on `(a, b)`
and weak order on `[a, b]`. -/
private lemma yAt_lt_of_disjoint_open
    {s₁ s₂ : (ℝ × ℝ) × (ℝ × ℝ)} {a b x₁ x₂ : ℝ}
    (h1 : s₁.1.1 < s₁.2.1) (h2 : s₂.1.1 < s₂.2.1)
    (_ha1 : s₁.1.1 ≤ a) (_hb1 : b ≤ s₁.2.1)
    (_ha2 : s₂.1.1 ≤ a) (_hb2 : b ≤ s₂.2.1)
    (hdisj : ∀ x, a < x → x < b → yAt s₁ x ≠ yAt s₂ x)
    (hx1a : a < x₁) (hx1b : x₁ < b)
    (hx2a : a < x₂) (hx2b : x₂ < b)
    (hylt : yAt s₁ x₁ < yAt s₂ x₁) :
    yAt s₁ x₂ < yAt s₂ x₂ := by
  by_contra hge
  push Not at hge
  rcases eq_or_lt_of_le hge with heq | hgt
  · exact hdisj x₂ hx2a hx2b heq.symm
  · -- Linear IVT: find x strictly between x₁ and x₂ where yAt s₁ x = yAt s₂ x
    let d : ℝ → ℝ := fun x => yAt s₂ x - yAt s₁ x
    have hd_aff : ∀ x t : ℝ, d ((1 - t) * x₁ + t * x₂) = (1 - t) * d x₁ + t * d x₂ := by
      intro x t
      dsimp only [d, yAt]
      have hne1 : s₁.2.1 - s₁.1.1 ≠ 0 := (sub_pos.mpr h1).ne'
      have hne2 : s₂.2.1 - s₂.1.1 ≠ 0 := (sub_pos.mpr h2).ne'
      field_simp [hne1, hne2]
      ring
    have hd1 : 0 < d x₁ := sub_pos.mpr hylt
    have hd2 : d x₂ < 0 := sub_neg.mpr hgt
    have hdenom : 0 < d x₁ - d x₂ := by linarith
    let t : ℝ := d x₁ / (d x₁ - d x₂)
    have ht0 : 0 < t := div_pos hd1 hdenom
    have ht1 : t < 1 := (div_lt_one hdenom).mpr (by linarith)
    let xm : ℝ := (1 - t) * x₁ + t * x₂
    have hxa : a < xm := by nlinarith
    have hxb : xm < b := by nlinarith
    have hdm : d xm = 0 := by
      have := hd_aff xm t
      rw [this]
      dsimp only [t]
      field_simp [hdenom.ne']
      ring
    exact hdisj xm hxa hxb (by dsimp only [d] at hdm; linarith)

private lemma yAt_le_endpoint_of_lt_mid
    {s₁ s₂ : (ℝ × ℝ) × (ℝ × ℝ)} {a b x : ℝ}
    (h1 : s₁.1.1 < s₁.2.1) (h2 : s₂.1.1 < s₂.2.1)
    (_ha1 : s₁.1.1 ≤ a) (_hb1 : b ≤ s₁.2.1)
    (_ha2 : s₂.1.1 ≤ a) (_hb2 : b ≤ s₂.2.1)
    (hab : a < b)
    (hdisj : ∀ z, a < z → z < b → yAt s₁ z ≠ yAt s₂ z)
    (hmid : yAt s₁ ((a + b) / 2) < yAt s₂ ((a + b) / 2))
    (hxa : a ≤ x) (hxb : x ≤ b) :
    yAt s₁ x ≤ yAt s₂ x := by
  by_contra hgt
  push Not at hgt
  let d : ℝ → ℝ := fun z => yAt s₂ z - yAt s₁ z
  let m := (a + b) / 2
  have hd_aff : ∀ t : ℝ, d ((1 - t) * m + t * x) = (1 - t) * d m + t * d x := by
    intro t
    dsimp only [d, yAt]
    have hne1 : s₁.2.1 - s₁.1.1 ≠ 0 := (sub_pos.mpr h1).ne'
    have hne2 : s₂.2.1 - s₂.1.1 ≠ 0 := (sub_pos.mpr h2).ne'
    field_simp [hne1, hne2]
    ring
  have hdm : 0 < d m := sub_pos.mpr hmid
  have hdx : d x < 0 := sub_neg.mpr hgt
  have hdenom : 0 < d m - d x := by linarith
  let t : ℝ := d m / (d m - d x)
  have ht0 : 0 < t := div_pos hdm hdenom
  have ht1 : t < 1 := (div_lt_one hdenom).mpr (by linarith)
  let z := (1 - t) * m + t * x
  have hza : a < z := by dsimp only [z, m]; nlinarith
  have hzb : z < b := by dsimp only [z, m]; nlinarith
  have hdz : d z = 0 := by
    rw [hd_aff t]
    dsimp only [t]
    field_simp [hdenom.ne']
    ring
  exact hdisj z hza hzb (by dsimp only [d] at hdz; linarith)

/-- A crossing-free polygonal subdivision in `ℝ × ℝ` of a simple graph `(A, E)` whose vertices `Q`
all have strictly distinct `x`-coordinates. -/
private structure XDistinctPLSubdiv (A : Finset (ℝ × ℝ)) (E : Finset ℕ) where
  Q : Finset (ℝ × ℝ)
  hAQ : A ⊆ Q
  hx_inj : ∀ p ∈ Q, ∀ q ∈ Q, p.1 = q.1 → p = q
  S : Finset ((ℝ × ℝ) × (ℝ × ℝ))
  hS_mem : ∀ s ∈ S, s.1 ∈ Q ∧ s.2 ∈ Q ∧ s.1.1 < s.2.1
  hS_noncross : ∀ s₁ ∈ S, ∀ s₂ ∈ S, s₁ ≠ s₂ → poseg s₁.1 s₁.2 ∩ pseg s₂.1 s₂.2 = ∅
  hS_avoidQ : ∀ s ∈ S, ∀ r ∈ Q, r ∉ poseg s.1 s.2
  -- Simple graph endpoints for E
  uEnd : ℕ → ℝ × ℝ
  vEnd : ℕ → ℝ × ℝ
  hEnd_mem : ∀ i ∈ E, uEnd i ∈ A ∧ vEnd i ∈ A ∧ uEnd i ≠ vEnd i
  hEnd_simple : Set.InjOn (fun i => ({uEnd i, vEnd i} : Finset (ℝ × ℝ))) (E : Set ℕ)
  -- Partition of S into edges E
  edgeOf : (ℝ × ℝ) × (ℝ × ℝ) → ℕ
  hedgeOf_mem : ∀ s ∈ S, edgeOf s ∈ E
  -- Every edge i ∈ E has a nonempty path of segments whose count minus internal vertices = 1,
  -- and every internal vertex q ∈ Q \ A has degree exactly 2 in S with both segments in the same edge,
  -- and for every i ∈ E, the segments of S_i form a connected path from uEnd i to vEnd i.
  hpath : ∀ i ∈ E,
    let Si := S.filter (fun s => edgeOf s = i)
    let Qi := (Q \ A).filter (fun r => ∃ s ∈ Si, s.1 = r ∨ s.2 = r)
    Si.Nonempty ∧
    Si.card = Qi.card + 1 ∧
    -- Incident count of Si at each vertex of A: 1 at uEnd i and vEnd i, 0 elsewhere
    (∀ a ∈ A, (Si.filter (fun s => s.1 = a ∨ s.2 = a)).card =
      if a = uEnd i ∨ a = vEnd i then 1 else 0) ∧
    -- Internal vertices of Qi have degree 2 in Si and 0 outside Si
    (∀ r ∈ Qi, (Si.filter (fun s => s.1 = r ∨ s.2 = r)).card = 2) ∧
    -- Every segment in Si is connected to every other segment in Si through internal bends Qi
    (∀ P : ((ℝ × ℝ) × (ℝ × ℝ)) → Prop,
      (∀ r ∈ Qi, ∀ s₁ ∈ Si, ∀ s₂ ∈ Si, (s₁.1 = r ∨ s₁.2 = r) → (s₂.1 = r ∨ s₂.2 = r) →
        (P s₁ ↔ P s₂)) →
      ∀ s₁ ∈ Si, ∀ s₂ ∈ Si, (P s₁ ↔ P s₂))
  hQ_internal : ∀ r ∈ Q \ A, (S.filter (fun s => s.1 = r ∨ s.2 = r)).card = 2 ∧
    ∃ i ∈ E, ∀ s ∈ S, (s.1 = r ∨ s.2 = r) → edgeOf s = i

/-- Sweep-line decomposition data for an `x`-distinct polygonal subdivision. -/
private structure SweepData (A : Finset (ℝ × ℝ)) (E : Finset ℕ) (D : XDistinctPLSubdiv A E) where
  M : ℕ
  hQcard : D.Q.card = M
  x : Fin M → ℝ
  hx_strict : StrictMono x
  q : Fin M → ℝ × ℝ
  hq_inj : Function.Injective q
  hq_surj : ∀ p ∈ D.Q, ∃ k : Fin M, q k = p
  Active : Fin (M + 1) → Finset ((ℝ × ℝ) × (ℝ × ℝ))
  hActive_last : Active (Fin.last M) = ∅
  hActive_bounds : ∀ (k : Fin (M + 1)) (s : (ℝ × ℝ) × (ℝ × ℝ)),
    s ∈ Active k → ∃ h : 0 < k.val ∧ k.val < M,
      s ∈ D.S ∧ s.1.1 ≤ x ⟨k.val - 1, by omega⟩ ∧ x ⟨k.val, h.2⟩ ≤ s.2.1
  rk : Fin (M + 1) → ((ℝ × ℝ) × (ℝ × ℝ)) → ℕ
  hrk_lt : ∀ (k : Fin (M + 1)) {s}, s ∈ Active k → rk k s < (Active k).card
  hrk_inj : ∀ (k : Fin (M + 1)), Set.InjOn (rk k) (Active k : Set _)
  hrk_surj : ∀ (k : Fin (M + 1)), ∀ j < (Active k).card, ∃ s ∈ Active k, rk k s = j
  Below : Fin M → Finset ((ℝ × ℝ) × (ℝ × ℝ))
  Above : Fin M → Finset ((ℝ × ℝ) × (ℝ × ℝ))
  hL_sub : ∀ k : Fin M, D.S.filter (fun s => s.2 = q k) ⊆ Active k.castSucc
  hR_sub : ∀ k : Fin M, D.S.filter (fun s => s.1 = q k) ⊆ Active k.succ
  hActiveL_eq : ∀ k : Fin M,
    Active k.castSucc = D.S.filter (fun s => s.1.1 < x k ∧ x k < s.2.1) ∪
      D.S.filter (fun s => s.2 = q k)
  hActiveR_eq : ∀ k : Fin M,
    Active k.succ = D.S.filter (fun s => s.1.1 < x k ∧ x k < s.2.1) ∪
      D.S.filter (fun s => s.1 = q k)
  hPass_split : ∀ k : Fin M,
    D.S.filter (fun s => s.1.1 < x k ∧ x k < s.2.1) = Below k ∪ Above k
  hrk_Below_eq : ∀ (k : Fin M) {s}, s ∈ Below k →
    rk k.castSucc s = rk k.succ s ∧ rk k.castSucc s < (Below k).card
  hrk_Above_eq : ∀ (k : Fin M) {s}, s ∈ Above k →
    (Below k).card + (D.S.filter (fun s => s.2 = q k)).card ≤ rk k.castSucc s ∧
    rk k.succ s + (D.S.filter (fun s => s.2 = q k)).card =
      rk k.castSucc s + (D.S.filter (fun s => s.1 = q k)).card
  hrk_L_range : ∀ (k : Fin M) {s}, s ∈ D.S.filter (fun s => s.2 = q k) →
    (Below k).card ≤ rk k.castSucc s ∧
      rk k.castSucc s < (Below k).card + (D.S.filter (fun s => s.2 = q k)).card
  hrk_R_range : ∀ (k : Fin M) {s}, s ∈ D.S.filter (fun s => s.1 = q k) →
    (Below k).card ≤ rk k.succ s ∧
      rk k.succ s < (Below k).card + (D.S.filter (fun s => s.1 = q k)).card
  hd_castSucc : ∀ k : Fin M,
    (Active k.castSucc).card = (D.S.filter (fun s => s.1.1 < x k ∧ x k < s.2.1)).card +
      (D.S.filter (fun s => s.2 = q k)).card
  hd_succ : ∀ k : Fin M,
    (Active k.succ).card = (D.S.filter (fun s => s.1.1 < x k ∧ x k < s.2.1)).card +
      (D.S.filter (fun s => s.1 = q k)).card
  hal_le_d : ∀ k : Fin M,
    (Below k).card + (D.S.filter (fun s => s.2 = q k)).card ≤ (Active k.castSucc).card
  har_le_d : ∀ k : Fin M,
    (Below k).card + (D.S.filter (fun s => s.1 = q k)).card ≤ (Active k.succ).card

private noncomputable abbrev SweepData.L {A : Finset (ℝ × ℝ)} {E : Finset ℕ} {D : XDistinctPLSubdiv A E}
    (SD : SweepData A E D) (k : Fin SD.M) := D.S.filter (fun s => s.2 = SD.q k)
private noncomputable abbrev SweepData.R {A : Finset (ℝ × ℝ)} {E : Finset ℕ} {D : XDistinctPLSubdiv A E}
    (SD : SweepData A E D) (k : Fin SD.M) := D.S.filter (fun s => s.1 = SD.q k)
private noncomputable abbrev SweepData.Pass {A : Finset (ℝ × ℝ)} {E : Finset ℕ} {D : XDistinctPLSubdiv A E}
    (SD : SweepData A E D) (k : Fin SD.M) := D.S.filter (fun s => s.1.1 < SD.x k ∧ SD.x k < s.2.1)
private abbrev SweepData.d {A : Finset (ℝ × ℝ)} {E : Finset ℕ} {D : XDistinctPLSubdiv A E}
    (SD : SweepData A E D) (k : Fin (SD.M + 1)) := (SD.Active k).card
private noncomputable abbrev SweepData.l {A : Finset (ℝ × ℝ)} {E : Finset ℕ} {D : XDistinctPLSubdiv A E}
    (SD : SweepData A E D) (k : Fin SD.M) := (SD.L k).card
private noncomputable abbrev SweepData.r {A : Finset (ℝ × ℝ)} {E : Finset ℕ} {D : XDistinctPLSubdiv A E}
    (SD : SweepData A E D) (k : Fin SD.M) := (SD.R k).card
private abbrev SweepData.a {A : Finset (ℝ × ℝ)} {E : Finset ℕ} {D : XDistinctPLSubdiv A E}
    (SD : SweepData A E D) (k : Fin SD.M) := (SD.Below k).card
private abbrev SweepData.Slab {A : Finset (ℝ × ℝ)} {E : Finset ℕ} {D : XDistinctPLSubdiv A E}
    (SD : SweepData A E D) := Σ k : Fin (SD.M + 1), Fin (SD.d k + 1)
private abbrev SweepData.portal {A : Finset (ℝ × ℝ)} {E : Finset ℕ} {D : XDistinctPLSubdiv A E}
    (SD : SweepData A E D) (k : Fin SD.M) (j₁ : Fin (SD.d k.castSucc + 1))
    (j₂ : Fin (SD.d k.succ + 1)) : Prop :=
  (j₁.val ≤ SD.a k ∧ j₂.val = j₁.val) ∨
  (SD.a k + SD.l k ≤ j₁.val ∧ j₂.val + SD.l k = j₁.val + SD.r k)
private def SweepData.Gslab {A : Finset (ℝ × ℝ)} {E : Finset ℕ} {D : XDistinctPLSubdiv A E}
    (SD : SweepData A E D) : SimpleGraph SD.Slab where
  Adj u v :=
    (∃ k : Fin SD.M, ∃ (h1 : u.1 = k.castSucc) (h2 : v.1 = k.succ),
      SD.portal k (h1 ▸ u.2) (h2 ▸ v.2)) ∨
    (∃ k : Fin SD.M, ∃ (h1 : v.1 = k.castSucc) (h2 : u.1 = k.succ),
      SD.portal k (h1 ▸ v.2) (h2 ▸ u.2))
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨fun _ h => by
    rcases h with ⟨k, h1, h2, _⟩ | ⟨k, h1, h2, _⟩
    · have := congrArg Fin.val (h1.symm.trans h2); simp at this
    · have := congrArg Fin.val (h1.symm.trans h2); simp at this⟩

private lemma SweepData.hportal_adj {A : Finset (ℝ × ℝ)} {E : Finset ℕ} {D : XDistinctPLSubdiv A E}
    (SD : SweepData A E D) (k : Fin SD.M) (j₁ : Fin (SD.d k.castSucc + 1))
    (j₂ : Fin (SD.d k.succ + 1)) (hp : SD.portal k j₁ j₂) :
    SD.Gslab.Adj ⟨k.castSucc, j₁⟩ ⟨k.succ, j₂⟩ :=
  Or.inl ⟨k, rfl, rfl, hp⟩

/-- Build the sweep-line decomposition data for an `x`-distinct polygonal subdivision. -/
private noncomputable def mkSweepData
    (A : Finset (ℝ × ℝ)) (E : Finset ℕ) (D : XDistinctPLSubdiv A E) :
    SweepData A E D := by
  classical
  -- Sort Q by x-coordinate using Q.image Prod.fst
  let xs : Finset ℝ := D.Q.image Prod.fst
  set M : ℕ := xs.card
  have hQcard : D.Q.card = M := by
    have hinj : Set.InjOn Prod.fst (D.Q : Set (ℝ × ℝ)) := fun p hp q hq h => D.hx_inj p hp q hq h
    exact (Finset.card_image_of_injOn hinj).symm
  let xIso : Fin M ≃o xs := xs.orderIsoOfFin rfl
  let x : Fin M → ℝ := fun k => (xIso k).1
  have hx_strict : StrictMono x := fun i j hij => by
    change (xIso i).1 < (xIso j).1
    exact xIso.strictMono hij
  have hx_mem : ∀ k : Fin M, ∃ p ∈ D.Q, p.1 = x k := fun k => Finset.mem_image.mp (xIso k).2
  let q : Fin M → ℝ × ℝ := fun k => (hx_mem k).choose
  have hq_mem : ∀ k : Fin M, q k ∈ D.Q := fun k => (hx_mem k).choose_spec.1
  have hq_fst : ∀ k : Fin M, (q k).1 = x k := fun k => (hx_mem k).choose_spec.2
  have hq_inj : Function.Injective q := by
    intro i j hij
    have h1 : x i = x j := by rw [← hq_fst i, ← hq_fst j, hij]
    exact hx_strict.injective h1
  have hq_surj : ∀ p ∈ D.Q, ∃ k : Fin M, q k = p := by
    intro p hp
    have hpx : p.1 ∈ xs := Finset.mem_image.mpr ⟨p, hp, rfl⟩
    let k : Fin M := xIso.symm ⟨p.1, hpx⟩
    refine ⟨k, D.hx_inj (q k) (hq_mem k) p hp ?_⟩
    rw [hq_fst k]
    change (xIso (xIso.symm ⟨p.1, hpx⟩)).1 = p.1
    simp
  have hq_eq_iff : ∀ k : Fin M, ∀ p ∈ D.Q, p = q k ↔ p.1 = x k := by
    intro k p hp
    constructor
    · rintro rfl; exact hq_fst k
    · intro h; exact D.hx_inj p hp (q k) (hq_mem k) (h.trans (hq_fst k).symm)
  -- Active segments in strip k : Fin (M + 1)
  let Active : Fin (M + 1) → Finset ((ℝ × ℝ) × (ℝ × ℝ)) := fun k =>
    if h : 0 < k.val ∧ k.val < M then
      D.S.filter (fun s => s.1.1 ≤ x ⟨k.val - 1, by omega⟩ ∧ x ⟨k.val, h.2⟩ ≤ s.2.1)
    else ∅
  let mid : Fin (M + 1) → ℝ := fun k =>
    if h : 0 < k.val ∧ k.val < M then
      (x ⟨k.val - 1, by omega⟩ + x ⟨k.val, h.2⟩) / 2
    else 0
  have hActive_zero : Active ⟨0, Nat.zero_lt_succ M⟩ = ∅ := by simp [Active]
  have hActive_last : Active (Fin.last M) = ∅ := by simp [Active, Fin.last]
  have hActive_bounds : ∀ (k : Fin (M + 1)) (s : (ℝ × ℝ) × (ℝ × ℝ)),
      s ∈ Active k → ∃ h : 0 < k.val ∧ k.val < M,
        s ∈ D.S ∧ s.1.1 ≤ x ⟨k.val - 1, by omega⟩ ∧ x ⟨k.val, h.2⟩ ≤ s.2.1 := by
    intro k s hs
    dsimp only [Active] at hs
    split_ifs at hs with h
    · have hs' := Finset.mem_filter.mp hs
      exact ⟨h, hs'.1, hs'.2.1, hs'.2.2⟩
    · simp at hs
  have hActive_disj_y : ∀ (k : Fin (M + 1)) (h : 0 < k.val ∧ k.val < M)
      {s₁ s₂ : (ℝ × ℝ) × (ℝ × ℝ)}, s₁ ∈ Active k → s₂ ∈ Active k → s₁ ≠ s₂ →
      ∀ z : ℝ, x ⟨k.val - 1, by omega⟩ < z → z < x ⟨k.val, h.2⟩ → yAt s₁ z ≠ yAt s₂ z := by
    intro k h s₁ s₂ hs₁ hs₂ hne z hz1 hz2 heq
    obtain ⟨_, hS1, ha1, hb1⟩ := hActive_bounds k s₁ hs₁
    obtain ⟨_, hS2, ha2, hb2⟩ := hActive_bounds k s₂ hs₂
    have hlt1 := (D.hS_mem s₁ hS1).2.2
    have hlt2 := (D.hS_mem s₂ hS2).2.2
    have hm1 : (z, yAt s₁ z) ∈ poseg s₁.1 s₁.2 :=
      mem_poseg_of_yAt hlt1 (lt_of_le_of_lt ha1 hz1) (lt_of_lt_of_le hz2 hb1)
    have hm2 : (z, yAt s₁ z) ∈ pseg s₂.1 s₂.2 := by
      rw [heq]
      exact mem_pseg_of_yAt hlt2 (le_of_lt (lt_of_le_of_lt ha2 hz1)) (le_of_lt (lt_of_lt_of_le hz2 hb2))
    have hemp := D.hS_noncross s₁ hS1 s₂ hS2 hne
    have : (z, yAt s₁ z) ∈ (∅ : Set (ℝ × ℝ)) := hemp ▸ ⟨hm1, hm2⟩
    exact this
  have hActive_y_inj : ∀ (k : Fin (M + 1)), Set.InjOn (fun s => yAt s (mid k)) (Active k : Set _) := by
    intro k s₁ hs₁ s₂ hs₂ heq
    by_contra hne
    obtain ⟨h, _, _, _⟩ := hActive_bounds k s₁ hs₁
    have hxlt : x ⟨k.val - 1, by omega⟩ < x ⟨k.val, h.2⟩ :=
      hx_strict (Fin.lt_def.mpr (by dsimp only; omega))
    have hmid_eq : mid k = (x ⟨k.val - 1, by omega⟩ + x ⟨k.val, h.2⟩) / 2 := dif_pos h
    rw [hmid_eq] at heq
    exact hActive_disj_y k h hs₁ hs₂ hne ((x ⟨k.val - 1, by omega⟩ + x ⟨k.val, h.2⟩) / 2)
      (by linarith) (by linarith) heq
  -- Rank of a segment in Active k
  let rk : Fin (M + 1) → ((ℝ × ℝ) × (ℝ × ℝ)) → ℕ := fun k s =>
    ((Active k).filter (fun s' => yAt s' (mid k) < yAt s (mid k))).card
  have hrk_lt : ∀ (k : Fin (M + 1)) {s}, s ∈ Active k → rk k s < (Active k).card := by
    intro k s hs
    apply Finset.card_lt_card
    rw [Finset.ssubset_iff_subset_ne]
    refine ⟨Finset.filter_subset _ _, fun heq => ?_⟩
    have hmem : s ∈ (Active k).filter (fun s' => yAt s' (mid k) < yAt s (mid k)) := heq.symm ▸ hs
    exact lt_irrefl _ (Finset.mem_filter.mp hmem).2
  have hrk_mono : ∀ (k : Fin (M + 1)) {s₁ s₂}, s₁ ∈ Active k → s₂ ∈ Active k →
      yAt s₁ (mid k) < yAt s₂ (mid k) → rk k s₁ < rk k s₂ := by
    intro k s₁ s₂ hs₁ hs₂ hylt
    apply Finset.card_lt_card
    rw [Finset.ssubset_iff_subset_ne]
    refine ⟨fun s' hs' => ?_, fun heq => ?_⟩
    · have hs'' := Finset.mem_filter.mp hs'
      exact Finset.mem_filter.mpr ⟨hs''.1, hs''.2.trans hylt⟩
    · have hmem : s₁ ∈ (Active k).filter (fun s' => yAt s' (mid k) < yAt s₂ (mid k)) :=
        Finset.mem_filter.mpr ⟨hs₁, hylt⟩
      rw [← heq] at hmem
      exact lt_irrefl _ (Finset.mem_filter.mp hmem).2
  have hrk_inj : ∀ (k : Fin (M + 1)), Set.InjOn (rk k) (Active k : Set _) := by
    intro k s₁ hs₁ s₂ hs₂ heq
    by_contra hne
    have hyne : yAt s₁ (mid k) ≠ yAt s₂ (mid k) := fun h => hne (hActive_y_inj k hs₁ hs₂ h)
    rcases lt_or_gt_of_ne hyne with hlt | hgt
    · exact (ne_of_lt (hrk_mono k hs₁ hs₂ hlt)) heq
    · exact (ne_of_gt (hrk_mono k hs₂ hs₁ hgt)) heq
  have hrk_surj : ∀ (k : Fin (M + 1)) (j : ℕ), j < (Active k).card →
      ∃ s ∈ Active k, rk k s = j := by
    intro k j hj
    have himg : (Active k).image (rk k) = Finset.range (Active k).card := by
      apply Finset.eq_of_subset_of_card_le
      · intro r hr
        obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hr
        exact Finset.mem_range.mpr (hrk_lt k hs)
      · rw [Finset.card_range, Finset.card_image_of_injOn (hrk_inj k)]
    have hmem : j ∈ (Active k).image (rk k) := himg ▸ Finset.mem_range.mpr hj
    exact Finset.mem_image.mp hmem
  -- Left-ending L k, Right-starting R k, and Pass-through Pass k at each vertex q k
  let L : Fin M → Finset ((ℝ × ℝ) × (ℝ × ℝ)) := fun k => D.S.filter (fun s => s.2 = q k)
  let R : Fin M → Finset ((ℝ × ℝ) × (ℝ × ℝ)) := fun k => D.S.filter (fun s => s.1 = q k)
  let Pass : Fin M → Finset ((ℝ × ℝ) × (ℝ × ℝ)) := fun k =>
    D.S.filter (fun s => s.1.1 < x k ∧ x k < s.2.1)
  have hL_sub : ∀ k : Fin M, L k ⊆ Active k.castSucc := by
    intro k s hs
    have hs' := Finset.mem_filter.mp hs
    have hS := hs'.1
    have h2 := hs'.2
    obtain ⟨h1Q, _, hlt⟩ := D.hS_mem s hS
    obtain ⟨j₁, hj₁⟩ := hq_surj s.1 h1Q
    have hj₁_lt : j₁ < k := by
      by_contra hge
      push Not at hge
      have : x k ≤ x j₁ := hx_strict.monotone hge
      rw [← hq_fst j₁, hj₁, ← hq_fst k, ← h2] at this
      linarith
    have hk_pos : 0 < k.val := by omega
    have hkm : k.val < M := k.isLt
    have hxle : s.1.1 ≤ x ⟨k.val - 1, by omega⟩ := by
      rw [← hj₁, hq_fst j₁]
      exact hx_strict.monotone (show j₁ ≤ ⟨k.val - 1, by omega⟩ by simp [Fin.le_def]; omega)
    dsimp only [Active]
    rw [dif_pos ⟨hk_pos, hkm⟩]
    refine Finset.mem_filter.mpr ⟨hS, hxle, ?_⟩
    have hkeq : (⟨k.castSucc.val, hkm⟩ : Fin M) = k := Fin.ext rfl
    rw [hkeq, h2, hq_fst k]
  have hR_sub : ∀ k : Fin M, R k ⊆ Active k.succ := by
    intro k s hs
    have hs' := Finset.mem_filter.mp hs
    have hS := hs'.1
    have h1 := hs'.2
    obtain ⟨_, h2Q, hlt⟩ := D.hS_mem s hS
    obtain ⟨j₂, hj₂⟩ := hq_surj s.2 h2Q
    have hk_lt : k < j₂ := by
      by_contra hge
      push Not at hge
      have : x j₂ ≤ x k := hx_strict.monotone hge
      rw [← hq_fst j₂, hj₂, ← hq_fst k, ← h1] at this
      linarith
    have hkp_pos : 0 < k.succ.val := Nat.succ_pos _
    have hkp_lt : k.succ.val < M := by simp [Fin.val_succ]; omega
    have hxle : x ⟨k.succ.val, hkp_lt⟩ ≤ s.2.1 := by
      rw [← hj₂, hq_fst j₂]
      exact hx_strict.monotone (show (⟨k.succ.val, hkp_lt⟩ : Fin M) ≤ j₂ by
        simp [Fin.le_def, Fin.val_succ]; omega)
    dsimp only [Active]
    rw [dif_pos ⟨hkp_pos, hkp_lt⟩]
    refine Finset.mem_filter.mpr ⟨hS, ?_, hxle⟩
    have hsub : (⟨k.succ.val - 1, by omega⟩ : Fin M) = k := by ext; simp [Fin.val_succ]
    rw [hsub, h1, hq_fst k]
  have hActiveL_eq : ∀ k : Fin M, Active k.castSucc = Pass k ∪ L k := by
    intro k
    ext s
    simp only [Finset.mem_union, Pass, L, Finset.mem_filter]
    constructor
    · intro hs
      obtain ⟨h, hS, ha, hb⟩ := hActive_bounds k.castSucc s hs
      have hk_pos : 0 < k.val := h.1
      have h1lt : s.1.1 < x k := by
        have hxlt : x ⟨k.val - 1, by omega⟩ < x k :=
          hx_strict (Fin.lt_def.mpr (by dsimp only; omega))
        exact lt_of_le_of_lt ha hxlt
      rcases eq_or_lt_of_le hb with heq | hgt
      · right
        exact ⟨hS, (hq_eq_iff k s.2 (D.hS_mem s hS).2.1).mpr heq.symm⟩
      · left
        exact ⟨hS, h1lt, hgt⟩
    · rintro (⟨hS, h1lt, h2gt⟩ | hL)
      · obtain ⟨h1Q, _, _⟩ := D.hS_mem s hS
        obtain ⟨j₁, hj₁⟩ := hq_surj s.1 h1Q
        have hj₁_lt : j₁ < k := by
          by_contra hge
          push Not at hge
          have := hx_strict.monotone hge
          rw [← hq_fst j₁, hj₁] at this
          linarith
        have hk_pos : 0 < k.val := by omega
        dsimp only [Active]
        rw [dif_pos ⟨hk_pos, k.isLt⟩]
        refine Finset.mem_filter.mpr ⟨hS, ?_, h2gt.le⟩
        rw [← hj₁, hq_fst j₁]
        exact hx_strict.monotone (show j₁ ≤ ⟨k.val - 1, by omega⟩ by simp [Fin.le_def]; omega)
      · exact hL_sub k (Finset.mem_filter.mpr hL)
  have hActiveR_eq : ∀ k : Fin M, Active k.succ = Pass k ∪ R k := by
    intro k
    ext s
    simp only [Finset.mem_union, Pass, R, Finset.mem_filter]
    constructor
    · intro hs
      obtain ⟨h, hS, ha, hb⟩ := hActive_bounds k.succ s hs
      have hsub : (⟨k.succ.val - 1, by omega⟩ : Fin M) = k := by ext; simp [Fin.val_succ]
      rw [hsub] at ha
      have h2gt : x k < s.2.1 := by
        have hxlt : x k < x ⟨k.succ.val, h.2⟩ :=
          hx_strict (show k < ⟨k.succ.val, h.2⟩ from Fin.lt_def.mpr (by dsimp only [Fin.val_succ]; omega))
        exact lt_of_lt_of_le hxlt hb
      rcases eq_or_lt_of_le ha with heq | hlt
      · right
        exact ⟨hS, (hq_eq_iff k s.1 (D.hS_mem s hS).1).mpr heq⟩
      · left
        exact ⟨hS, hlt, h2gt⟩
    · rintro (⟨hS, h1lt, h2gt⟩ | hR)
      · obtain ⟨_, h2Q, _⟩ := D.hS_mem s hS
        obtain ⟨j₂, hj₂⟩ := hq_surj s.2 h2Q
        have hk_lt : k < j₂ := by
          by_contra hge
          push Not at hge
          have := hx_strict.monotone hge
          rw [← hq_fst j₂, hj₂] at this
          linarith
        have hkp_lt : k.succ.val < M := by simp [Fin.val_succ]; omega
        dsimp only [Active]
        rw [dif_pos ⟨Nat.succ_pos _, hkp_lt⟩]
        have hsub : (⟨k.succ.val - 1, by omega⟩ : Fin M) = k := by ext; simp [Fin.val_succ]
        refine Finset.mem_filter.mpr ⟨hS, by rw [hsub]; exact h1lt.le, ?_⟩
        rw [← hj₂, hq_fst j₂]
        exact hx_strict.monotone (show (⟨k.succ.val, hkp_lt⟩ : Fin M) ≤ j₂ by
          simp [Fin.le_def, Fin.val_succ]; omega)
      · exact hR_sub k (Finset.mem_filter.mpr hR)
  have hDisj_PL : ∀ k : Fin M, Disjoint (Pass k) (L k) := by
    intro k; rw [Finset.disjoint_left]; intro s hp hl
    have h1 := (Finset.mem_filter.mp hp).2.2
    have h2 := (Finset.mem_filter.mp hl).2
    rw [h2, hq_fst k] at h1; linarith
  have hDisj_PR : ∀ k : Fin M, Disjoint (Pass k) (R k) := by
    intro k; rw [Finset.disjoint_left]; intro s hp hr
    have h1 := (Finset.mem_filter.mp hp).2.1
    have h2 := (Finset.mem_filter.mp hr).2
    rw [h2, hq_fst k] at h1; linarith
  have hPass_ne_y : ∀ (k : Fin M) {s}, s ∈ Pass k → yAt s (x k) ≠ (q k).2 := by
    intro k s hs heq
    have hs' := Finset.mem_filter.mp hs
    have hmem : q k ∈ poseg s.1 s.2 := by
      have hp : (x k, yAt s (x k)) = q k := Prod.ext (hq_fst k).symm heq
      rw [← hp]
      exact mem_poseg_of_yAt (D.hS_mem s hs'.1).2.2 hs'.2.1 hs'.2.2
    exact D.hS_avoidQ s hs'.1 (q k) (hq_mem k) hmem
  -- Split Pass k into Below k and Above k
  let Below : Fin M → Finset ((ℝ × ℝ) × (ℝ × ℝ)) := fun k =>
    (Pass k).filter (fun s => yAt s (x k) < (q k).2)
  let Above : Fin M → Finset ((ℝ × ℝ) × (ℝ × ℝ)) := fun k =>
    (Pass k).filter (fun s => (q k).2 < yAt s (x k))
  have hPass_split : ∀ k : Fin M, Pass k = Below k ∪ Above k := by
    intro k; ext s
    simp only [Finset.mem_union, Below, Above, Finset.mem_filter]
    constructor
    · intro hs
      rcases lt_or_gt_of_ne (hPass_ne_y k hs) with h | h
      · exact Or.inl ⟨hs, h⟩
      · exact Or.inr ⟨hs, h⟩
    · rintro (⟨hs, _⟩ | ⟨hs, _⟩) <;> exact hs
  have hDisj_BA : ∀ k : Fin M, Disjoint (Below k) (Above k) := by
    intro k; rw [Finset.disjoint_left]; intro s hb ha
    have h1 := (Finset.mem_filter.mp hb).2
    have h2 := (Finset.mem_filter.mp ha).2
    linarith
  -- Order preservation across x k: on strip kL and kR, segments in Pass k keep exact y-order at x k,
  -- and Below k < L k < Above k in kL, Below k < R k < Above k in kR!
  have hy_lt_kL_of_xk : ∀ (k : Fin M) {s₁ s₂}, s₁ ∈ Active k.castSucc → s₂ ∈ Active k.castSucc →
      yAt s₁ (x k) < yAt s₂ (x k) → yAt s₁ (mid k.castSucc) < yAt s₂ (mid k.castSucc) := by
    intro k s₁ s₂ hs₁ hs₂ hylt
    by_contra hge
    push Not at hge
    have hne : s₁ ≠ s₂ := fun h => by subst h; linarith
    have hyne : yAt s₁ (mid k.castSucc) ≠ yAt s₂ (mid k.castSucc) :=
      fun h => hne (hActive_y_inj k.castSucc hs₁ hs₂ h)
    have hgt : yAt s₂ (mid k.castSucc) < yAt s₁ (mid k.castSucc) := lt_of_le_of_ne hge hyne.symm
    obtain ⟨h, hS1, ha1, hb1⟩ := hActive_bounds k.castSucc s₁ hs₁
    obtain ⟨_, hS2, ha2, hb2⟩ := hActive_bounds k.castSucc s₂ hs₂
    have hk_pos : 0 < k.val := h.1
    have hxlt : x ⟨k.val - 1, by omega⟩ < x k :=
      hx_strict (Fin.lt_def.mpr (by dsimp only; omega))
    have hmid_eq : mid k.castSucc = (x ⟨k.val - 1, by omega⟩ + x k) / 2 := dif_pos h
    rw [hmid_eq] at hgt
    have hle := yAt_le_endpoint_of_lt_mid (D.hS_mem s₂ hS2).2.2 (D.hS_mem s₁ hS1).2.2
      ha2 hb2 ha1 hb1 hxlt (hActive_disj_y k.castSucc h hs₂ hs₁ hne.symm) hgt hxlt.le (le_refl _)
    linarith
  have hy_lt_kR_of_xk : ∀ (k : Fin M) {s₁ s₂}, s₁ ∈ Active k.succ → s₂ ∈ Active k.succ →
      yAt s₁ (x k) < yAt s₂ (x k) → yAt s₁ (mid k.succ) < yAt s₂ (mid k.succ) := by
    intro k s₁ s₂ hs₁ hs₂ hylt
    by_contra hge
    push Not at hge
    have hne : s₁ ≠ s₂ := fun h => by subst h; linarith
    have hyne : yAt s₁ (mid k.succ) ≠ yAt s₂ (mid k.succ) :=
      fun h => hne (hActive_y_inj k.succ hs₁ hs₂ h)
    have hgt : yAt s₂ (mid k.succ) < yAt s₁ (mid k.succ) := lt_of_le_of_ne hge hyne.symm
    obtain ⟨h, hS1, ha1, hb1⟩ := hActive_bounds k.succ s₁ hs₁
    obtain ⟨_, hS2, ha2, hb2⟩ := hActive_bounds k.succ s₂ hs₂
    have hsub : (⟨k.succ.val - 1, by omega⟩ : Fin M) = k := by ext; simp [Fin.val_succ]
    rw [hsub] at ha1 ha2
    have hxlt : x k < x ⟨k.succ.val, h.2⟩ :=
      hx_strict (show k < ⟨k.succ.val, h.2⟩ from Fin.lt_def.mpr (by dsimp only [Fin.val_succ]; omega))
    have hmid_eq : mid k.succ = (x k + x ⟨k.succ.val, h.2⟩) / 2 := by
      dsimp only [mid]; rw [dif_pos h, hsub]
    rw [hmid_eq] at hgt
    have hdisj := hActive_disj_y k.succ h hs₂ hs₁ hne.symm
    rw [hsub] at hdisj
    have hle := yAt_le_endpoint_of_lt_mid (D.hS_mem s₂ hS2).2.2 (D.hS_mem s₁ hS1).2.2
      ha2 hb2 ha1 hb1 hxlt hdisj hgt (le_refl _) hxlt.le
    linarith
  have hL_yAt : ∀ (k : Fin M) {s}, s ∈ L k → yAt s (x k) = (q k).2 := by
    intro k s hs
    have hs' := Finset.mem_filter.mp hs
    rw [← hq_fst k, ← hs'.2]
    exact yAt_right (D.hS_mem s hs'.1).2.2.ne
  have hR_yAt : ∀ (k : Fin M) {s}, s ∈ R k → yAt s (x k) = (q k).2 := by
    intro k s hs
    have hs' := Finset.mem_filter.mp hs
    rw [← hq_fst k, ← hs'.2]
    exact yAt_left
  have hPass_y_inj_xk : ∀ (k : Fin M) {s₁ s₂}, s₁ ∈ Pass k → s₂ ∈ Pass k → s₁ ≠ s₂ →
      yAt s₁ (x k) ≠ yAt s₂ (x k) := by
    intro k s₁ s₂ hs₁ hs₂ hne heq
    have h1 := Finset.mem_filter.mp hs₁
    have h2 := Finset.mem_filter.mp hs₂
    have hm1 : (x k, yAt s₁ (x k)) ∈ poseg s₁.1 s₁.2 :=
      mem_poseg_of_yAt (D.hS_mem s₁ h1.1).2.2 h1.2.1 h1.2.2
    have hm2 : (x k, yAt s₁ (x k)) ∈ pseg s₂.1 s₂.2 := by
      rw [heq]
      exact mem_pseg_of_yAt (D.hS_mem s₂ h2.1).2.2 h2.2.1.le h2.2.2.le
    have hemp := D.hS_noncross s₁ h1.1 s₂ h2.1 hne
    exact (hemp ▸ ⟨hm1, hm2⟩ : (x k, yAt s₁ (x k)) ∈ (∅ : Set (ℝ × ℝ)))
  -- Shorthand cardinalities
  let d : Fin (M + 1) → ℕ := fun k => (Active k).card
  let a : Fin M → ℕ := fun k => (Below k).card
  let l : Fin M → ℕ := fun k => (L k).card
  let r : Fin M → ℕ := fun k => (R k).card
  have hd_castSucc : ∀ k : Fin M, d k.castSucc = (Pass k).card + l k := by
    intro k; dsimp only [d, l]; rw [hActiveL_eq k, Finset.card_union_of_disjoint (hDisj_PL k)]
  have hd_succ : ∀ k : Fin M, d k.succ = (Pass k).card + r k := by
    intro k; dsimp only [d, r]; rw [hActiveR_eq k, Finset.card_union_of_disjoint (hDisj_PR k)]
  have hPass_card : ∀ k : Fin M, (Pass k).card = a k + (Above k).card := by
    intro k; dsimp only [a]; rw [hPass_split k, Finset.card_union_of_disjoint (hDisj_BA k)]
  have hal_le_d : ∀ k : Fin M, a k + l k ≤ d k.castSucc := by
    intro k; have := hd_castSucc k; have := hPass_card k; omega
  have har_le_d : ∀ k : Fin M, a k + r k ≤ d k.succ := by
    intro k; have := hd_succ k; have := hPass_card k; omega
  -- Rank shift lemmas for Below, L, R, Above!
  have hrk_Below_L : ∀ (k : Fin M) {s}, s ∈ Below k →
      rk k.castSucc s = ((Below k).filter (fun s' => yAt s' (x k) < yAt s (x k))).card := by
    intro k s hs
    have hsP : s ∈ Pass k := (Finset.mem_filter.mp hs).1
    have hsy : yAt s (x k) < (q k).2 := (Finset.mem_filter.mp hs).2
    have hsA : s ∈ Active k.castSucc := by rw [hActiveL_eq k]; exact Finset.mem_union_left _ hsP
    dsimp only [rk]
    congr 1
    ext s'
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hs'A, hmid⟩
      have hs'B : s' ∈ Below k := by
        rw [hActiveL_eq k, hPass_split k] at hs'A
        rcases Finset.mem_union.mp hs'A with hs'P | hs'L
        · rcases Finset.mem_union.mp hs'P with hB | hA
          · exact hB
          · exfalso
            have hlt := hy_lt_kL_of_xk k hsA (by rw [hActiveL_eq k, hPass_split k]; exact Finset.mem_union_left _ (Finset.mem_union_right _ hA))
              (hsy.trans (Finset.mem_filter.mp hA).2)
            linarith
        · exfalso
          have hlt := hy_lt_kL_of_xk k hsA (hL_sub k hs'L) (by rw [hL_yAt k hs'L]; exact hsy)
          linarith
      refine ⟨hs'B, ?_⟩
      have hs'P : s' ∈ Pass k := (Finset.mem_filter.mp hs'B).1
      have hne : s' ≠ s := fun h => by subst h; linarith
      rcases lt_or_gt_of_ne (hPass_y_inj_xk k hs'P hsP hne) with hlt | hgt
      · exact hlt
      · exfalso
        have := hy_lt_kL_of_xk k hsA hs'A hgt
        linarith
    · rintro ⟨hs'B, hylt⟩
      have hs'A : s' ∈ Active k.castSucc := by
        rw [hActiveL_eq k]; exact Finset.mem_union_left _ (Finset.mem_filter.mp hs'B).1
      exact ⟨hs'A, hy_lt_kL_of_xk k hs'A hsA hylt⟩
  have hrk_Below_R : ∀ (k : Fin M) {s}, s ∈ Below k →
      rk k.succ s = ((Below k).filter (fun s' => yAt s' (x k) < yAt s (x k))).card := by
    intro k s hs
    have hsP : s ∈ Pass k := (Finset.mem_filter.mp hs).1
    have hsy : yAt s (x k) < (q k).2 := (Finset.mem_filter.mp hs).2
    have hsA : s ∈ Active k.succ := by rw [hActiveR_eq k]; exact Finset.mem_union_left _ hsP
    dsimp only [rk]
    congr 1
    ext s'
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hs'A, hmid⟩
      have hs'B : s' ∈ Below k := by
        rw [hActiveR_eq k, hPass_split k] at hs'A
        rcases Finset.mem_union.mp hs'A with hs'P | hs'R
        · rcases Finset.mem_union.mp hs'P with hB | hA
          · exact hB
          · exfalso
            have hlt := hy_lt_kR_of_xk k hsA (by rw [hActiveR_eq k, hPass_split k]; exact Finset.mem_union_left _ (Finset.mem_union_right _ hA))
              (hsy.trans (Finset.mem_filter.mp hA).2)
            linarith
        · exfalso
          have hlt := hy_lt_kR_of_xk k hsA (hR_sub k hs'R) (by rw [hR_yAt k hs'R]; exact hsy)
          linarith
      refine ⟨hs'B, ?_⟩
      have hs'P : s' ∈ Pass k := (Finset.mem_filter.mp hs'B).1
      have hne : s' ≠ s := fun h => by subst h; linarith
      rcases lt_or_gt_of_ne (hPass_y_inj_xk k hs'P hsP hne) with hlt | hgt
      · exact hlt
      · exfalso
        have := hy_lt_kR_of_xk k hsA hs'A hgt
        linarith
    · rintro ⟨hs'B, hylt⟩
      have hs'A : s' ∈ Active k.succ := by
        rw [hActiveR_eq k]; exact Finset.mem_union_left _ (Finset.mem_filter.mp hs'B).1
      exact ⟨hs'A, hy_lt_kR_of_xk k hs'A hsA hylt⟩
  have hrk_Below_lt : ∀ (k : Fin M) {s}, s ∈ Below k → rk k.castSucc s < a k := by
    intro k s hs
    rw [hrk_Below_L k hs]
    apply Finset.card_lt_card
    rw [Finset.ssubset_iff_subset_ne]
    refine ⟨Finset.filter_subset _ _, fun heq => ?_⟩
    have hmem : s ∈ (Below k).filter (fun s' => yAt s' (x k) < yAt s (x k)) := heq.symm ▸ hs
    exact lt_irrefl _ (Finset.mem_filter.mp hmem).2
  have hrk_L_range : ∀ (k : Fin M) {s}, s ∈ L k →
      a k ≤ rk k.castSucc s ∧ rk k.castSucc s < a k + l k := by
    intro k s hs
    have hsA : s ∈ Active k.castSucc := hL_sub k hs
    have hsy : yAt s (x k) = (q k).2 := hL_yAt k hs
    let F := (Active k.castSucc).filter (fun s' => yAt s' (mid k.castSucc) < yAt s (mid k.castSucc))
    have hBsub : Below k ⊆ F := by
      intro s' hs'B
      have hs'A : s' ∈ Active k.castSucc := by
        rw [hActiveL_eq k]; exact Finset.mem_union_left _ (Finset.mem_filter.mp hs'B).1
      exact Finset.mem_filter.mpr ⟨hs'A, hy_lt_kL_of_xk k hs'A hsA (by rw [hsy]; exact (Finset.mem_filter.mp hs'B).2)⟩
    have hFsub : F ⊆ Below k ∪ L k := by
      intro s' hs'
      have hs'' := Finset.mem_filter.mp hs'
      rw [hActiveL_eq k, hPass_split k] at hs''
      rcases Finset.mem_union.mp hs''.1 with hs'P | hs'L
      · rcases Finset.mem_union.mp hs'P with hB | hA
        · exact Finset.mem_union_left _ hB
        · exfalso
          have hs'A : s' ∈ Active k.castSucc := by
            rw [hActiveL_eq k]; exact Finset.mem_union_left _ (Finset.mem_filter.mp hA).1
          have hlt := hy_lt_kL_of_xk k hsA hs'A (by rw [hsy]; exact (Finset.mem_filter.mp hA).2)
          linarith [hs''.2]
      · exact Finset.mem_union_right _ hs'L
    have hs_not : s ∉ F := fun hm => lt_irrefl _ (Finset.mem_filter.mp hm).2
    have hFssub : F ⊂ Below k ∪ L k := by
      rw [Finset.ssubset_iff_subset_ne]
      exact ⟨hFsub, fun heq => hs_not (heq ▸ Finset.mem_union_right _ hs)⟩
    have hdisj : Disjoint (Below k) (L k) :=
      (hDisj_PL k).mono_left (Finset.filter_subset _ _)
    constructor
    · exact Finset.card_le_card hBsub
    · calc rk k.castSucc s = F.card := rfl
        _ < (Below k ∪ L k).card := Finset.card_lt_card hFssub
        _ = a k + l k := Finset.card_union_of_disjoint hdisj
  have hrk_R_range : ∀ (k : Fin M) {s}, s ∈ R k →
      a k ≤ rk k.succ s ∧ rk k.succ s < a k + r k := by
    intro k s hs
    have hsA : s ∈ Active k.succ := hR_sub k hs
    have hsy : yAt s (x k) = (q k).2 := hR_yAt k hs
    let F := (Active k.succ).filter (fun s' => yAt s' (mid k.succ) < yAt s (mid k.succ))
    have hBsub : Below k ⊆ F := by
      intro s' hs'B
      have hs'A : s' ∈ Active k.succ := by
        rw [hActiveR_eq k]; exact Finset.mem_union_left _ (Finset.mem_filter.mp hs'B).1
      exact Finset.mem_filter.mpr ⟨hs'A, hy_lt_kR_of_xk k hs'A hsA (by rw [hsy]; exact (Finset.mem_filter.mp hs'B).2)⟩
    have hFsub : F ⊆ Below k ∪ R k := by
      intro s' hs'
      have hs'' := Finset.mem_filter.mp hs'
      rw [hActiveR_eq k, hPass_split k] at hs''
      rcases Finset.mem_union.mp hs''.1 with hs'P | hs'R
      · rcases Finset.mem_union.mp hs'P with hB | hA
        · exact Finset.mem_union_left _ hB
        · exfalso
          have hs'A : s' ∈ Active k.succ := by
            rw [hActiveR_eq k]; exact Finset.mem_union_left _ (Finset.mem_filter.mp hA).1
          have hlt := hy_lt_kR_of_xk k hsA hs'A (by rw [hsy]; exact (Finset.mem_filter.mp hA).2)
          linarith [hs''.2]
      · exact Finset.mem_union_right _ hs'R
    have hs_not : s ∉ F := fun hm => lt_irrefl _ (Finset.mem_filter.mp hm).2
    have hFssub : F ⊂ Below k ∪ R k := by
      rw [Finset.ssubset_iff_subset_ne]
      exact ⟨hFsub, fun heq => hs_not (heq ▸ Finset.mem_union_right _ hs)⟩
    have hdisj : Disjoint (Below k) (R k) :=
      (hDisj_PR k).mono_left (Finset.filter_subset _ _)
    constructor
    · exact Finset.card_le_card hBsub
    · calc rk k.succ s = F.card := rfl
        _ < (Below k ∪ R k).card := Finset.card_lt_card hFssub
        _ = a k + r k := Finset.card_union_of_disjoint hdisj
  have hrk_Above_L : ∀ (k : Fin M) {s}, s ∈ Above k →
      rk k.castSucc s = a k + l k + ((Above k).filter (fun s' => yAt s' (x k) < yAt s (x k))).card := by
    intro k s hs
    have hsP : s ∈ Pass k := (Finset.mem_filter.mp hs).1
    have hsy : (q k).2 < yAt s (x k) := (Finset.mem_filter.mp hs).2
    have hsA : s ∈ Active k.castSucc := by rw [hActiveL_eq k]; exact Finset.mem_union_left _ hsP
    have hEq : (Active k.castSucc).filter (fun s' => yAt s' (mid k.castSucc) < yAt s (mid k.castSucc)) =
        (Below k ∪ L k) ∪ (Above k).filter (fun s' => yAt s' (x k) < yAt s (x k)) := by
      ext s'
      simp only [Finset.mem_union, Finset.mem_filter]
      constructor
      · rintro ⟨hs'A, hmid⟩
        rw [hActiveL_eq k, hPass_split k] at hs'A
        rcases Finset.mem_union.mp hs'A with hs'P | hs'L
        · rcases Finset.mem_union.mp hs'P with hB | hA
          · exact Or.inl (Or.inl hB)
          · right
            refine ⟨hA, ?_⟩
            have hne : s' ≠ s := fun h => by subst h; linarith
            rcases lt_or_gt_of_ne (hPass_y_inj_xk k (Finset.mem_filter.mp hA).1 hsP hne) with hlt | hgt
            · exact hlt
            · exfalso
              have hs'A' : s' ∈ Active k.castSucc := by
                rw [hActiveL_eq k]; exact Finset.mem_union_left _ (Finset.mem_filter.mp hA).1
              have := hy_lt_kL_of_xk k hsA hs'A' hgt
              linarith
        · exact Or.inl (Or.inr hs'L)
      · rintro ((hB | hL) | ⟨hA, hylt⟩)
        · have hs'A : s' ∈ Active k.castSucc := by
            rw [hActiveL_eq k]; exact Finset.mem_union_left _ (Finset.mem_filter.mp hB).1
          exact ⟨hs'A, hy_lt_kL_of_xk k hs'A hsA ((Finset.mem_filter.mp hB).2.trans hsy)⟩
        · have hs'A := hL_sub k hL
          exact ⟨hs'A, hy_lt_kL_of_xk k hs'A hsA (by rw [hL_yAt k hL]; exact hsy)⟩
        · have hs'A : s' ∈ Active k.castSucc := by
            rw [hActiveL_eq k]; exact Finset.mem_union_left _ (Finset.mem_filter.mp hA).1
          exact ⟨hs'A, hy_lt_kL_of_xk k hs'A hsA hylt⟩
    dsimp only [rk]
    rw [hEq]
    have hd1 : Disjoint (Below k) (L k) := (hDisj_PL k).mono_left (Finset.filter_subset _ _)
    have hd2 : Disjoint (Below k ∪ L k) ((Above k).filter (fun s' => yAt s' (x k) < yAt s (x k))) := by
      rw [Finset.disjoint_union_left]
      exact ⟨(hDisj_BA k).mono_right (Finset.filter_subset _ _),
        (hDisj_PL k).symm.mono_right ((Finset.filter_subset _ _).trans (Finset.filter_subset _ _))⟩
    rw [Finset.card_union_of_disjoint hd2, Finset.card_union_of_disjoint hd1]
  have hrk_Above_R : ∀ (k : Fin M) {s}, s ∈ Above k →
      rk k.succ s = a k + r k + ((Above k).filter (fun s' => yAt s' (x k) < yAt s (x k))).card := by
    intro k s hs
    have hsP : s ∈ Pass k := (Finset.mem_filter.mp hs).1
    have hsy : (q k).2 < yAt s (x k) := (Finset.mem_filter.mp hs).2
    have hsA : s ∈ Active k.succ := by rw [hActiveR_eq k]; exact Finset.mem_union_left _ hsP
    have hEq : (Active k.succ).filter (fun s' => yAt s' (mid k.succ) < yAt s (mid k.succ)) =
        (Below k ∪ R k) ∪ (Above k).filter (fun s' => yAt s' (x k) < yAt s (x k)) := by
      ext s'
      simp only [Finset.mem_union, Finset.mem_filter]
      constructor
      · rintro ⟨hs'A, hmid⟩
        rw [hActiveR_eq k, hPass_split k] at hs'A
        rcases Finset.mem_union.mp hs'A with hs'P | hs'R
        · rcases Finset.mem_union.mp hs'P with hB | hA
          · exact Or.inl (Or.inl hB)
          · right
            refine ⟨hA, ?_⟩
            have hne : s' ≠ s := fun h => by subst h; linarith
            rcases lt_or_gt_of_ne (hPass_y_inj_xk k (Finset.mem_filter.mp hA).1 hsP hne) with hlt | hgt
            · exact hlt
            · exfalso
              have hs'A' : s' ∈ Active k.succ := by
                rw [hActiveR_eq k]; exact Finset.mem_union_left _ (Finset.mem_filter.mp hA).1
              have := hy_lt_kR_of_xk k hsA hs'A' hgt
              linarith
        · exact Or.inl (Or.inr hs'R)
      · rintro ((hB | hR) | ⟨hA, hylt⟩)
        · have hs'A : s' ∈ Active k.succ := by
            rw [hActiveR_eq k]; exact Finset.mem_union_left _ (Finset.mem_filter.mp hB).1
          exact ⟨hs'A, hy_lt_kR_of_xk k hs'A hsA ((Finset.mem_filter.mp hB).2.trans hsy)⟩
        · have hs'A := hR_sub k hR
          exact ⟨hs'A, hy_lt_kR_of_xk k hs'A hsA (by rw [hR_yAt k hR]; exact hsy)⟩
        · have hs'A : s' ∈ Active k.succ := by
            rw [hActiveR_eq k]; exact Finset.mem_union_left _ (Finset.mem_filter.mp hA).1
          exact ⟨hs'A, hy_lt_kR_of_xk k hs'A hsA hylt⟩
    dsimp only [rk]
    rw [hEq]
    have hd1 : Disjoint (Below k) (R k) := (hDisj_PR k).mono_left (Finset.filter_subset _ _)
    have hd2 : Disjoint (Below k ∪ R k) ((Above k).filter (fun s' => yAt s' (x k) < yAt s (x k))) := by
      rw [Finset.disjoint_union_left]
      exact ⟨(hDisj_BA k).mono_right (Finset.filter_subset _ _),
        (hDisj_PR k).symm.mono_right ((Finset.filter_subset _ _).trans (Finset.filter_subset _ _))⟩
    rw [Finset.card_union_of_disjoint hd2, Finset.card_union_of_disjoint hd1]
  exact
    { M := M, hQcard := hQcard, x := x, hx_strict := hx_strict, q := q,
      hq_inj := hq_inj, hq_surj := hq_surj, Active := Active,
      hActive_last := hActive_last, hActive_bounds := hActive_bounds,
      rk := rk, hrk_lt := hrk_lt, hrk_inj := hrk_inj, hrk_surj := hrk_surj,
      Below := Below, Above := Above, hL_sub := hL_sub, hR_sub := hR_sub,
      hActiveL_eq := hActiveL_eq, hActiveR_eq := hActiveR_eq,
      hPass_split := hPass_split,
      hrk_Below_eq := fun k _ hB => ⟨(hrk_Below_L k hB).trans (hrk_Below_R k hB).symm, hrk_Below_lt k hB⟩,
      hrk_Above_eq := fun k _ hA => by
        have h1 := hrk_Above_L k hA; have h2 := hrk_Above_R k hA
        dsimp only [a, l, r, L, R] at h1 h2; omega,
      hrk_L_range := hrk_L_range, hrk_R_range := hrk_R_range,
      hd_castSucc := hd_castSucc, hd_succ := hd_succ,
      hal_le_d := hal_le_d, har_le_d := har_le_d }

/-- Euler's inequality `1 + E.card ≤ F + A.card` from the slab-portal graph. -/
private lemma sweepData_euler
    (A : Finset (ℝ × ℝ)) (E : Finset ℕ) (D : XDistinctPLSubdiv A E)
    (SD : SweepData A E D) :
    1 + E.card ≤ Fintype.card SD.Gslab.ConnectedComponent + A.card := by
  classical
  let M := SD.M; let q := SD.q; let Active := SD.Active
  have hQcard : D.Q.card = M := SD.hQcard
  have hq_inj : Function.Injective q := SD.hq_inj
  have hq_surj : ∀ p ∈ D.Q, ∃ k : Fin M, q k = p := SD.hq_surj
  have hActive_last : Active (Fin.last M) = ∅ := SD.hActive_last
  let L := SD.L; let R := SD.R; let Pass := SD.Pass
  let d := SD.d; let l := SD.l; let r := SD.r; let a := SD.a
  have hd_castSucc : ∀ k : Fin M, d k.castSucc = (Pass k).card + l k := SD.hd_castSucc
  have hd_succ : ∀ k : Fin M, d k.succ = (Pass k).card + r k := SD.hd_succ
  have hal_le_d : ∀ k : Fin M, a k + l k ≤ d k.castSucc := SD.hal_le_d
  have har_le_d : ∀ k : Fin M, a k + r k ≤ d k.succ := SD.har_le_d
  let Slab := SD.Slab; let portal := SD.portal; let Gslab := SD.Gslab
  have hportal_adj : ∀ (k : Fin M) (j₁ : Fin (d k.castSucc + 1)) (j₂ : Fin (d k.succ + 1)),
      portal k j₁ j₂ → Gslab.Adj ⟨k.castSucc, j₁⟩ ⟨k.succ, j₂⟩ := SD.hportal_adj
  -- Count vertices of Slab
  have hSlab_card : Fintype.card Slab = (M + 1) + ∑ k : Fin M, d k.castSucc := by
    change Fintype.card (Σ k : Fin (M + 1), Fin (d k + 1)) = _
    rw [Fintype.card_sigma, Fin.sum_univ_castSucc]
    have hlast : Fintype.card (Fin (d (Fin.last M) + 1)) = 1 := by
      have : d (Fin.last M) = 0 := by change (Active (Fin.last M)).card = 0; rw [hActive_last]; rfl
      rw [this]; simp
    rw [hlast]
    simp_rw [Fintype.card_fin, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, smul_eq_mul, mul_one]
    omega
  -- Count edges of Gslab via bijection with Sigma over k of valid portal pairs!
  let portalPairs (k : Fin M) : Finset (Fin (d k.castSucc + 1) × Fin (d k.succ + 1)) :=
    Finset.univ.filter (fun p => portal k p.1 p.2)
  have hportal_card : ∀ k : Fin M, (portalPairs k).card =
      if l k + r k = 0 then d k.castSucc + 1 else d k.castSucc - l k + 2 := by
    intro k
    have hdd : d k.succ + l k = d k.castSucc + r k := by
      have := hd_castSucc k; have := hd_succ k; omega
    have hal := hal_le_d k
    have har := har_le_d k
    -- Split into low (j₁ ≤ a k, j₂ = j₁) and high (a k + l k ≤ j₁, j₂ + l k = j₁ + r k)
    let P_lo : Finset (Fin (d k.castSucc + 1) × Fin (d k.succ + 1)) :=
      Finset.univ.filter (fun p => p.1.val ≤ a k ∧ p.2.val = p.1.val)
    let P_hi : Finset (Fin (d k.castSucc + 1) × Fin (d k.succ + 1)) :=
      Finset.univ.filter (fun p => a k + l k ≤ p.1.val ∧ p.2.val + l k = p.1.val + r k)
    have hPeq : portalPairs k = P_lo ∪ P_hi := by
      ext p
      simp only [portalPairs, P_lo, P_hi, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
      rfl
    have hlo_card : P_lo.card = a k + 1 := by
      refine (Finset.card_bij (fun p _ => p.1.val) ?_ ?_ ?_).trans (Finset.card_range (a k + 1))
      · intro p hp; exact Finset.mem_range.mpr (by have := (Finset.mem_filter.mp hp).2.1; omega)
      · intro p₁ hp₁ p₂ hp₂ heq
        have h1 := (Finset.mem_filter.mp hp₁).2.2
        have h2 := (Finset.mem_filter.mp hp₂).2.2
        exact Prod.ext (Fin.ext heq) (Fin.ext (by omega))
      · intro m hm
        have hma : m ≤ a k := by have := Finset.mem_range.mp hm; omega
        exact ⟨(⟨m, by omega⟩, ⟨m, by omega⟩),
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hma, rfl⟩, rfl⟩
    have hhi_card : P_hi.card = d k.castSucc - (a k + l k) + 1 := by
      refine (Finset.card_bij (fun p _ => p.1.val - (a k + l k)) ?_ ?_ ?_).trans
        (Finset.card_range (d k.castSucc - (a k + l k) + 1))
      · intro p hp
        have h1 := (Finset.mem_filter.mp hp).2.1
        have h2 := p.1.isLt
        exact Finset.mem_range.mpr (by omega)
      · intro p₁ hp₁ p₂ hp₂ heq
        have ha1 := (Finset.mem_filter.mp hp₁).2.1
        have he1 := (Finset.mem_filter.mp hp₁).2.2
        have ha2 := (Finset.mem_filter.mp hp₂).2.1
        have he2 := (Finset.mem_filter.mp hp₂).2.2
        exact Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega))
      · intro m hm
        have hm' : m ≤ d k.castSucc - (a k + l k) := by have := Finset.mem_range.mp hm; omega
        refine ⟨(⟨a k + l k + m, by omega⟩, ⟨a k + r k + m, by omega⟩),
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, by dsimp only; omega, by dsimp only; omega⟩, ?_⟩
        dsimp only; omega
    split_ifs with h0
    · have hl0 : l k = 0 := by omega
      have hr0 : r k = 0 := by omega
      have hsub : P_lo ∩ P_hi = {(⟨a k, by omega⟩, ⟨a k, by omega⟩)} := by
        ext p
        simp only [Finset.mem_inter, P_lo, P_hi, Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_singleton, Prod.ext_iff, Fin.ext_iff]
        constructor
        · rintro ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩; omega
        · rintro ⟨h1, h2⟩; omega
      have huc := Finset.card_union_add_card_inter P_lo P_hi
      rw [← hPeq, hlo_card, hhi_card, hsub, Finset.card_singleton] at huc
      omega
    · have hdisj : Disjoint P_lo P_hi := by
        rw [Finset.disjoint_left]; intro p h1 h2
        have a1 := (Finset.mem_filter.mp h1).2
        have a2 := (Finset.mem_filter.mp h2).2
        omega
      rw [hPeq, Finset.card_union_of_disjoint hdisj, hlo_card, hhi_card]
      omega
  have hEdge_card : Gslab.edgeFinset.card = ∑ k : Fin M, (portalPairs k).card := by
    rw [← Finset.card_sigma]
    symm
    refine Finset.card_bij
      (fun (x : Σ k : Fin M, Fin (d k.castSucc + 1) × Fin (d k.succ + 1)) _ =>
        s((⟨x.1.castSucc, x.2.1⟩ : Slab), (⟨x.1.succ, x.2.2⟩ : Slab))) ?_ ?_ ?_
    · intro x hx
      rw [SimpleGraph.mem_edgeFinset]
      exact hportal_adj x.1 x.2.1 x.2.2 (Finset.mem_filter.mp (Finset.mem_sigma.mp hx).2).2
    · intro x₁ _ x₂ _ heq
      rcases Sym2.eq_iff.mp heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have hk : x₁.1 = x₂.1 := Fin.ext (by
          have := congrArg (fun u : Slab => u.1.val) h1
          simp at this; exact this)
        cases x₁ with | mk k₁ p₁ =>
        cases x₂ with | mk k₂ p₂ =>
        dsimp only at hk; subst hk
        have hp1 : p₁.1 = p₂.1 := eq_of_heq (Sigma.mk.inj h1).2
        have hp2 : p₁.2 = p₂.2 := eq_of_heq (Sigma.mk.inj h2).2
        cases p₁; cases p₂; simp_all
      · exfalso
        have h1' := congrArg (fun u : Slab => u.1.val) h1
        have h2' := congrArg (fun u : Slab => u.1.val) h2
        simp at h1' h2'
        omega
    · intro e he
      induction e using Sym2.ind with | _ u v =>
      have hadj : Gslab.Adj u v := SimpleGraph.mem_edgeFinset.mp he
      rcases hadj with ⟨k, h1, h2, hp⟩ | ⟨k, h1, h2, hp⟩
      · refine ⟨⟨k, (h1 ▸ u.2, h2 ▸ v.2)⟩, Finset.mem_sigma.mpr ⟨Finset.mem_univ _,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp⟩⟩, ?_⟩
        cases u with | mk ku ju =>
        cases v with | mk kv jv =>
        dsimp only at h1 h2; subst h1; subst h2; rfl
      · refine ⟨⟨k, (h1 ▸ v.2, h2 ▸ u.2)⟩, Finset.mem_sigma.mpr ⟨Finset.mem_univ _,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp⟩⟩, ?_⟩
        cases u with | mk ku ju =>
        cases v with | mk kv jv =>
        dsimp only at h1 h2; subst h1; subst h2
        exact Sym2.eq_swap
  -- Relate ∑ k, l k = D.S.card and D.S.card = E.card + (D.Q \ A).card
  have hsum_l : ∑ k : Fin M, l k = D.S.card := by
    have hpart : ∀ s ∈ D.S, ∃! k : Fin M, s ∈ L k := by
      intro s hs
      obtain ⟨k, hk⟩ := hq_surj s.2 (D.hS_mem s hs).2.1
      refine ⟨k, Finset.mem_filter.mpr ⟨hs, hk.symm⟩, fun k' hk' => ?_⟩
      exact hq_inj ((Finset.mem_filter.mp hk').2.symm.trans hk.symm)
    have hbi : (Finset.univ : Finset (Fin M)).biUnion L = D.S := by
      ext s
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, L, Finset.mem_filter]
      constructor
      · rintro ⟨_, hs, _⟩; exact hs
      · intro hs
        obtain ⟨k, hk⟩ := hq_surj s.2 (D.hS_mem s hs).2.1
        exact ⟨k, hs, hk.symm⟩
    have hpw : ((Finset.univ : Finset (Fin M)) : Set (Fin M)).PairwiseDisjoint L := by
      intro k₁ _ k₂ _ hne
      dsimp only [Function.onFun]
      rw [Finset.disjoint_left]; intro s h1 h2
      exact hne (hq_inj ((Finset.mem_filter.mp h1).2.symm.trans (Finset.mem_filter.mp h2).2))
    rw [← hbi, Finset.card_biUnion hpw]
  have hS_eq_E_add : D.S.card = E.card + (D.Q \ A).card := by
    -- Partition D.S by edgeOf into E, and partition D.Q \ A by the unique i ∈ E!
    have hS_part : D.S.card = ∑ i ∈ E, (D.S.filter (fun s => D.edgeOf s = i)).card := by
      rw [Finset.card_eq_sum_card_fiberwise (f := D.edgeOf) (t := E) (fun s hs => D.hedgeOf_mem s hs)]
    let edgeOfInt : ℝ × ℝ → ℕ := fun r =>
      if h : r ∈ D.Q \ A then (D.hQ_internal r h).2.choose else 0
    have hQ_part : (D.Q \ A).card =
        ∑ i ∈ E, ((D.Q \ A).filter (fun r => ∃ s ∈ D.S.filter (fun s => D.edgeOf s = i),
          s.1 = r ∨ s.2 = r)).card := by
      have hfib : (D.Q \ A).card = ∑ i ∈ E, ((D.Q \ A).filter (fun r => edgeOfInt r = i)).card := by
        rw [Finset.card_eq_sum_card_fiberwise (f := edgeOfInt) (t := E)]
        intro r hr
        have hr' : r ∈ D.Q \ A := Finset.mem_coe.mp hr
        dsimp only [edgeOfInt]; rw [dif_pos hr']
        exact (D.hQ_internal r hr').2.choose_spec.1
      rw [hfib]
      apply Finset.sum_congr rfl
      intro i hi
      congr 1; ext r
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hr, heq⟩
        refine ⟨hr, ?_⟩
        have hpos : 0 < (D.S.filter (fun s => s.1 = r ∨ s.2 = r)).card := by
          rw [(D.hQ_internal r hr).1]; omega
        obtain ⟨s, hs⟩ := Finset.card_pos.mp hpos
        have hs' := Finset.mem_filter.mp hs
        have he : D.edgeOf s = i := by
          have hch := (D.hQ_internal r hr).2.choose_spec.2 s hs'.1 hs'.2
          dsimp only [edgeOfInt] at heq; rw [dif_pos hr] at heq
          exact hch.trans heq
        exact ⟨s, ⟨hs'.1, he⟩, hs'.2⟩
      · rintro ⟨hr, s, ⟨hsS, hse⟩, hinc⟩
        refine ⟨hr, ?_⟩
        have hch := (D.hQ_internal r hr).2.choose_spec.2 s hsS hinc
        dsimp only [edgeOfInt]; rw [dif_pos hr]
        exact hch.symm.trans hse
    rw [hS_part, hQ_part]
    have hsum : ∑ i ∈ E, (D.S.filter (fun s => D.edgeOf s = i)).card =
        ∑ i ∈ E, (((D.Q \ A).filter (fun r => ∃ s ∈ D.S.filter (fun s => D.edgeOf s = i),
          s.1 = r ∨ s.2 = r)).card + 1) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact (D.hpath i hi).2.1
    rw [hsum, Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one]
    omega
  -- Euler's inequality: F + A.card ≥ 1 + E.card!
  set F := Fintype.card Gslab.ConnectedComponent
  have hEuler : 1 + E.card ≤ F + A.card := by
    have hcc := card_connectedComponent_ge_sub_edges Gslab
    rw [hSlab_card, hEdge_card] at hcc
    have hEdge_le : ∑ k : Fin M, (portalPairs k).card + D.S.card ≤
        (∑ k : Fin M, d k.castSucc) + M + (A.card + (D.Q \ A).card) := by
      have hAQ_card : A.card + (D.Q \ A).card = M := by
        rw [← hQcard, add_comm, Finset.card_sdiff_add_card_eq_card D.hAQ]
      -- Each k contributes ≤ d k.castSucc - l k + 2! Wait: if l k + r k = 0, then l k = 0 so d + 1 ≤ d - 0 + 2!
      have hterm : ∀ k : Fin M, (portalPairs k).card + l k ≤ d k.castSucc + 2 := by
        intro k
        rw [hportal_card k]
        split_ifs with h0
        · omega
        · have := hal_le_d k; omega
      have hsum_le := Finset.sum_le_sum (fun k (_ : k ∈ Finset.univ) => hterm k)
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hsum_l,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hsum_le
      omega
    omega
  exact hEuler

/-- Face-boundary double counting `3 * (F - 1) ≤ 2 * E.card` via mod-2 boundary evenness. -/
private lemma sweepData_double_count
    (A : Finset (ℝ × ℝ)) (E : Finset ℕ) (D : XDistinctPLSubdiv A E)
    (SD : SweepData A E D) :
    3 * (Fintype.card SD.Gslab.ConnectedComponent - 1) ≤ 2 * E.card := by
  classical
  let M := SD.M; let x := SD.x; let q := SD.q; let Active := SD.Active
  let rk := SD.rk; let L := SD.L; let R := SD.R; let Pass := SD.Pass
  let Below := SD.Below; let Above := SD.Above
  let d := SD.d; let l := SD.l; let r := SD.r; let a := SD.a
  let Slab := Σ k : Fin (M + 1), Fin (d k + 1)
  let Gslab : SimpleGraph Slab := SD.Gslab
  have hx_strict : StrictMono x := SD.hx_strict
  have hq_surj : ∀ p ∈ D.Q, ∃ k : Fin M, q k = p := SD.hq_surj
  have hActive_bounds : ∀ (k : Fin (M + 1)) (s : (ℝ × ℝ) × (ℝ × ℝ)),
      s ∈ Active k → ∃ h : 0 < k.val ∧ k.val < M,
        s ∈ D.S ∧ s.1.1 ≤ x ⟨k.val - 1, by omega⟩ ∧ x ⟨k.val, h.2⟩ ≤ s.2.1 := SD.hActive_bounds
  have hrk_lt : ∀ (k : Fin (M + 1)) {s}, s ∈ Active k → rk k s < d k := SD.hrk_lt
  have hrk_inj : ∀ (k : Fin (M + 1)), Set.InjOn (rk k) (Active k : Set _) := SD.hrk_inj
  have hrk_surj : ∀ (k : Fin (M + 1)), ∀ j < d k, ∃ s ∈ Active k, rk k s = j := SD.hrk_surj
  have hL_sub : ∀ k : Fin M, L k ⊆ Active k.castSucc := SD.hL_sub
  have hR_sub : ∀ k : Fin M, R k ⊆ Active k.succ := SD.hR_sub
  have hActiveL_eq : ∀ k : Fin M, Active k.castSucc = Pass k ∪ L k := SD.hActiveL_eq
  have hActiveR_eq : ∀ k : Fin M, Active k.succ = Pass k ∪ R k := SD.hActiveR_eq
  have hPass_split : ∀ k : Fin M, Pass k = Below k ∪ Above k := SD.hPass_split
  have hrk_Below_eq : ∀ (k : Fin M) {s}, s ∈ Below k → rk k.castSucc s = rk k.succ s ∧ rk k.castSucc s < a k := SD.hrk_Below_eq
  have hrk_Above_eq : ∀ (k : Fin M) {s}, s ∈ Above k → a k + l k ≤ rk k.castSucc s ∧ rk k.succ s + l k = rk k.castSucc s + r k := SD.hrk_Above_eq
  have hrk_L_range : ∀ (k : Fin M) {s}, s ∈ L k → a k ≤ rk k.castSucc s ∧ rk k.castSucc s < a k + l k := SD.hrk_L_range
  have hrk_R_range : ∀ (k : Fin M) {s}, s ∈ R k → a k ≤ rk k.succ s ∧ rk k.succ s < a k + r k := SD.hrk_R_range
  have hal_le_d : ∀ k : Fin M, a k + l k ≤ d k.castSucc := SD.hal_le_d
  have har_le_d : ∀ k : Fin M, a k + r k ≤ d k.succ := SD.har_le_d
  have hportal_adj : ∀ (k : Fin M) (j₁ : Fin (d k.castSucc + 1)) (j₂ : Fin (d k.succ + 1)),
      ((j₁.val ≤ a k ∧ j₂.val = j₁.val) ∨ (a k + l k ≤ j₁.val ∧ j₂.val + l k = j₁.val + r k)) →
      Gslab.Adj ⟨k.castSucc, j₁⟩ ⟨k.succ, j₂⟩ := SD.hportal_adj
  set F := Fintype.card Gslab.ConnectedComponent
  let comp : Slab → Gslab.ConnectedComponent := Gslab.connectedComponentMk
  have hcomp_eq : ∀ {kA kB : Fin (M + 1)} (hk : kA = kB) {jA : Fin (d kA + 1)} {jB : Fin (d kB + 1)},
      jA.val = jB.val → comp ⟨kA, jA⟩ = comp ⟨kB, jB⟩ := by
    intro kA kB hk jA jB hj; subst hk; congr 2; exact Fin.ext hj
  let cOut : Gslab.ConnectedComponent := comp ⟨⟨0, Nat.zero_lt_succ M⟩, ⟨0, Nat.zero_lt_succ _⟩⟩
  -- Every bottom slab (k, 0) is in cOut!
  have hbot_cOut : ∀ k : Fin (M + 1), comp ⟨k, ⟨0, Nat.zero_lt_succ _⟩⟩ = cOut := by
    intro k
    induction k using Fin.induction with
    | zero => rfl
    | succ k ih =>
      rw [← ih]
      apply SimpleGraph.ConnectedComponent.sound
      exact (hportal_adj k ⟨0, Nat.zero_lt_succ _⟩ ⟨0, Nat.zero_lt_succ _⟩ (Or.inl ⟨Nat.zero_le _, rfl⟩)).symm.reachable
  -- For any segment s ∈ D.S, its bottom and top face components are invariant across all strips k where s ∈ Active k!
  have hseg_active_nonempty : ∀ s ∈ D.S, ∃ k : Fin (M + 1), s ∈ Active k := by
    intro s hs
    obtain ⟨j₁, hj₁⟩ := hq_surj s.1 (D.hS_mem s hs).1
    exact ⟨j₁.succ, hR_sub j₁ (Finset.mem_filter.mpr ⟨hs, hj₁.symm⟩)⟩
  have hseg_face_step : ∀ (k : Fin M) {s} (hs : s ∈ Pass k),
      let kL := k.castSucc
      let kR := k.succ
      have hL_act : s ∈ Active kL := by rw [hActiveL_eq k]; exact Finset.mem_union_left _ hs
      have hR_act : s ∈ Active kR := by rw [hActiveR_eq k]; exact Finset.mem_union_left _ hs
      comp ⟨kL, ⟨rk kL s, Nat.lt_succ_of_lt (hrk_lt kL hL_act)⟩⟩ =
        comp ⟨kR, ⟨rk kR s, Nat.lt_succ_of_lt (hrk_lt kR hR_act)⟩⟩ ∧
      comp ⟨kL, ⟨rk kL s + 1, Nat.succ_lt_succ (hrk_lt kL hL_act)⟩⟩ =
        comp ⟨kR, ⟨rk kR s + 1, Nat.succ_lt_succ (hrk_lt kR hR_act)⟩⟩ := by
    intro k s hs
    have hL_act : s ∈ Active k.castSucc := by rw [hActiveL_eq k]; exact Finset.mem_union_left _ hs
    have hR_act : s ∈ Active k.succ := by rw [hActiveR_eq k]; exact Finset.mem_union_left _ hs
    rw [hPass_split k] at hs
    rcases Finset.mem_union.mp hs with hB | hA
    · obtain ⟨heq, hlt⟩ := hrk_Below_eq k hB
      constructor
      · apply SimpleGraph.ConnectedComponent.sound
        exact (hportal_adj k _ _ (Or.inl ⟨by dsimp only; omega, by dsimp only; omega⟩)).reachable
      · apply SimpleGraph.ConnectedComponent.sound
        exact (hportal_adj k _ _ (Or.inl ⟨by dsimp only; omega, by dsimp only; omega⟩)).reachable
    · obtain ⟨hge, heq⟩ := hrk_Above_eq k hA
      constructor
      · apply SimpleGraph.ConnectedComponent.sound
        exact (hportal_adj k _ _ (Or.inr ⟨by dsimp only; omega, by dsimp only; omega⟩)).reachable
      · apply SimpleGraph.ConnectedComponent.sound
        exact (hportal_adj k _ _ (Or.inr ⟨by dsimp only; omega, by dsimp only; omega⟩)).reachable
  -- Show Active strips of s form a contiguous interval of Fin (M + 1), so bot/top faces are independent of k!
  have hseg_face_indep : ∀ {s}, s ∈ D.S → ∀ (k₁ k₂ : Fin (M + 1))
      (h₁ : s ∈ Active k₁) (h₂ : s ∈ Active k₂),
      comp ⟨k₁, ⟨rk k₁ s, Nat.lt_succ_of_lt (hrk_lt k₁ h₁)⟩⟩ =
        comp ⟨k₂, ⟨rk k₂ s, Nat.lt_succ_of_lt (hrk_lt k₂ h₂)⟩⟩ ∧
      comp ⟨k₁, ⟨rk k₁ s + 1, Nat.succ_lt_succ (hrk_lt k₁ h₁)⟩⟩ =
        comp ⟨k₂, ⟨rk k₂ s + 1, Nat.succ_lt_succ (hrk_lt k₂ h₂)⟩⟩ := by
    intro s hs
    have hle_step : ∀ (k₁ k₂ : Fin (M + 1)), k₁.val ≤ k₂.val →
        ∀ (h₁ : s ∈ Active k₁) (h₂ : s ∈ Active k₂),
        comp ⟨k₁, ⟨rk k₁ s, Nat.lt_succ_of_lt (hrk_lt k₁ h₁)⟩⟩ =
          comp ⟨k₂, ⟨rk k₂ s, Nat.lt_succ_of_lt (hrk_lt k₂ h₂)⟩⟩ ∧
        comp ⟨k₁, ⟨rk k₁ s + 1, Nat.succ_lt_succ (hrk_lt k₁ h₁)⟩⟩ =
          comp ⟨k₂, ⟨rk k₂ s + 1, Nat.succ_lt_succ (hrk_lt k₂ h₂)⟩⟩ := by
      intro k₁ k₂ hle
      obtain ⟨t, ht⟩ := Nat.exists_eq_add_of_le hle
      induction t generalizing k₂ with
      | zero =>
        intro h₁ h₂
        have hk : k₁ = k₂ := Fin.ext (by omega)
        subst hk; exact ⟨rfl, rfl⟩
      | succ t ih =>
        intro h₁ h₂
        have hk2_pos : 0 < k₂.val := by omega
        have hkm : k₂.val - 1 < M := by have := k₂.isLt; omega
        let k' : Fin M := ⟨k₂.val - 1, hkm⟩
        have hk'L : k'.castSucc.val = k₂.val - 1 := rfl
        have hk'R : k'.succ = k₂ := Fin.ext (by dsimp only [k', Fin.val_succ]; omega)
        -- s ∈ Active k₁ and s ∈ Active k₂ with k₁ ≤ k'.castSucc < k₂ => s ∈ Pass k'!
        have hsP : s ∈ Pass k' := by
          obtain ⟨hb1, _, ha1, _⟩ := hActive_bounds k₁ s h₁
          obtain ⟨hb2, _, _, hb2'⟩ := hActive_bounds k₂ s h₂
          have hlt1 : s.1.1 < x k' := by
            have : x ⟨k₁.val - 1, by omega⟩ < x k' :=
              hx_strict (show (⟨k₁.val - 1, by omega⟩ : Fin M) < k' from Fin.lt_def.mpr (by dsimp only [k']; omega))
            exact lt_of_le_of_lt ha1 this
          have hlt2 : x k' < s.2.1 := by
            have : x k' < x ⟨k₂.val, hb2.2⟩ :=
              hx_strict (show k' < ⟨k₂.val, hb2.2⟩ from Fin.lt_def.mpr (by dsimp only [k']; omega))
            exact lt_of_lt_of_le this hb2'
          exact Finset.mem_filter.mpr ⟨hs, hlt1, hlt2⟩
        have h' : s ∈ Active k'.castSucc := by
          rw [hActiveL_eq k']; exact Finset.mem_union_left _ hsP
        have hstep := hseg_face_step k' hsP
        have hprev := ih k'.castSucc (by omega) (by omega) h₁ h'
        exact ⟨hprev.1.trans (hstep.1.trans (hcomp_eq hk'R (by dsimp only; rw [hk'R]))),
               hprev.2.trans (hstep.2.trans (hcomp_eq hk'R (by dsimp only; rw [hk'R])))⟩
    intro k₁ k₂ h₁ h₂
    rcases le_total k₁.val k₂.val with h | h
    · exact hle_step k₁ k₂ h h₁ h₂
    · have := hle_step k₂ k₁ h h₂ h₁
      exact ⟨this.1.symm, this.2.symm⟩
  -- Define botFace and topFace for every segment s ∈ D.S
  let botFace : ((ℝ × ℝ) × (ℝ × ℝ)) → Gslab.ConnectedComponent := fun s =>
    if hs : s ∈ D.S then
      let k := (hseg_active_nonempty s hs).choose
      let hk := (hseg_active_nonempty s hs).choose_spec
      comp ⟨k, ⟨rk k s, Nat.lt_succ_of_lt (hrk_lt k hk)⟩⟩
    else cOut
  let topFace : ((ℝ × ℝ) × (ℝ × ℝ)) → Gslab.ConnectedComponent := fun s =>
    if hs : s ∈ D.S then
      let k := (hseg_active_nonempty s hs).choose
      let hk := (hseg_active_nonempty s hs).choose_spec
      comp ⟨k, ⟨rk k s + 1, Nat.succ_lt_succ (hrk_lt k hk)⟩⟩
    else cOut
  have hbotFace_eq : ∀ (k : Fin (M + 1)) {s} (hs : s ∈ Active k),
      botFace s = comp ⟨k, ⟨rk k s, Nat.lt_succ_of_lt (hrk_lt k hs)⟩⟩ := by
    intro k s hs
    have hS : s ∈ D.S := (hActive_bounds k s hs).2.1
    dsimp only [botFace]; rw [dif_pos hS]
    exact (hseg_face_indep hS _ k (hseg_active_nonempty s hS).choose_spec hs).1
  have htopFace_eq : ∀ (k : Fin (M + 1)) {s} (hs : s ∈ Active k),
      topFace s = comp ⟨k, ⟨rk k s + 1, Nat.succ_lt_succ (hrk_lt k hs)⟩⟩ := by
    intro k s hs
    have hS : s ∈ D.S := (hActive_bounds k s hs).2.1
    dsimp only [topFace]; rw [dif_pos hS]
    exact (hseg_face_indep hS _ k (hseg_active_nonempty s hS).choose_spec hs).2
  -- At any degree-2 vertex q k (l k + r k = 2), its two incident segments have the SAME unordered pair {botFace, topFace}!
  have hdeg2_facePair : ∀ (k : Fin M), l k + r k = 2 →
      ∀ s₁ ∈ D.S, ∀ s₂ ∈ D.S, (s₁.1 = q k ∨ s₁.2 = q k) → (s₂.1 = q k ∨ s₂.2 = q k) →
      ({botFace s₁, topFace s₁} : Finset Gslab.ConnectedComponent) = {botFace s₂, topFace s₂} := by
    intro k hdeg s₁ hs₁ s₂ hs₂ hinc₁ hinc₂
    by_cases hsame : s₁ = s₂
    · subst hsame; rfl
    have hLR : ∀ s ∈ D.S, (s.1 = q k ∨ s.2 = q k) → s ∈ L k ∨ s ∈ R k := by
      intro s hs h; rcases h with h1 | h2
      · exact Or.inr (Finset.mem_filter.mpr ⟨hs, h1⟩)
      · exact Or.inl (Finset.mem_filter.mpr ⟨hs, h2⟩)
    -- Portal equality at bottom and top of q k
    have hbot_eq : comp ⟨k.castSucc, ⟨a k, Nat.lt_succ_of_le (by have := hal_le_d k; omega)⟩⟩ =
        comp ⟨k.succ, ⟨a k, Nat.lt_succ_of_le (by have := har_le_d k; omega)⟩⟩ :=
      SimpleGraph.ConnectedComponent.sound (hportal_adj k _ _ (Or.inl ⟨le_refl _, rfl⟩)).reachable
    have htop_eq : comp ⟨k.castSucc, ⟨a k + l k, Nat.lt_succ_of_le (hal_le_d k)⟩⟩ =
        comp ⟨k.succ, ⟨a k + r k, Nat.lt_succ_of_le (har_le_d k)⟩⟩ :=
      SimpleGraph.ConnectedComponent.sound (hportal_adj k _ _ (Or.inr ⟨le_refl _, by dsimp only; omega⟩)).reachable
    rcases hLR s₁ hs₁ hinc₁ with h1L | h1R <;> rcases hLR s₂ hs₂ hinc₂ with h2L | h2R
    · -- Both in L k => l k = 2, r k = 0!
      have hl2 : l k = 2 := by
        have hsub : ({s₁, s₂} : Finset _) ⊆ L k := by
          intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz
          rcases hz with rfl | rfl <;> assumption
        have h2 : 2 ≤ l k := by rw [← Finset.card_pair hsame]; exact Finset.card_le_card hsub
        omega
      have hr0 : r k = 0 := by omega
      have hwrap : comp ⟨k.castSucc, ⟨a k, Nat.lt_succ_of_le (by have := hal_le_d k; omega)⟩⟩ =
          comp ⟨k.castSucc, ⟨a k + 2, Nat.lt_succ_of_le (by have := hal_le_d k; omega)⟩⟩ := by
        have h1' := hbot_eq
        have h2' := htop_eq
        simp only [hl2, hr0, add_zero] at h2'
        exact h1'.trans h2'.symm
      have hr1 := hrk_L_range k h1L
      have hr2 := hrk_L_range k h2L
      have hrne : rk k.castSucc s₁ ≠ rk k.castSucc s₂ := fun h => hsame (hrk_inj k.castSucc (hL_sub k h1L) (hL_sub k h2L) h)
      rw [hbotFace_eq k.castSucc (hL_sub k h1L), htopFace_eq k.castSucc (hL_sub k h1L),
          hbotFace_eq k.castSucc (hL_sub k h2L), htopFace_eq k.castSucc (hL_sub k h2L)]
      have hcases : (rk k.castSucc s₁ = a k ∧ rk k.castSucc s₂ = a k + 1) ∨
                    (rk k.castSucc s₁ = a k + 1 ∧ rk k.castSucc s₂ = a k) := by omega
      rcases hcases with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · have hb1 : comp ⟨k.castSucc, ⟨rk k.castSucc s₁, Nat.lt_succ_of_lt (hrk_lt k.castSucc (hL_sub k h1L))⟩⟩ =
            comp ⟨k.castSucc, ⟨a k, Nat.lt_succ_of_le (by have := hal_le_d k; omega)⟩⟩ :=
          hcomp_eq rfl (by dsimp only; omega)
        have ht1 : comp ⟨k.castSucc, ⟨rk k.castSucc s₁ + 1, Nat.succ_lt_succ (hrk_lt k.castSucc (hL_sub k h1L))⟩⟩ =
            comp ⟨k.castSucc, ⟨a k + 1, Nat.lt_succ_of_le (by have := hal_le_d k; omega)⟩⟩ :=
          hcomp_eq rfl (by dsimp only; omega)
        have hb2 : comp ⟨k.castSucc, ⟨rk k.castSucc s₂, Nat.lt_succ_of_lt (hrk_lt k.castSucc (hL_sub k h2L))⟩⟩ =
            comp ⟨k.castSucc, ⟨a k + 1, Nat.lt_succ_of_le (by have := hal_le_d k; omega)⟩⟩ :=
          hcomp_eq rfl (by dsimp only; omega)
        have ht2 : comp ⟨k.castSucc, ⟨rk k.castSucc s₂ + 1, Nat.succ_lt_succ (hrk_lt k.castSucc (hL_sub k h2L))⟩⟩ =
            comp ⟨k.castSucc, ⟨a k + 2, Nat.lt_succ_of_le (by have := hal_le_d k; omega)⟩⟩ :=
          hcomp_eq rfl (by dsimp only; omega)
        rw [hb1, ht1, hb2, ht2, hwrap, Finset.pair_comm]
      · have hb1 : comp ⟨k.castSucc, ⟨rk k.castSucc s₁, Nat.lt_succ_of_lt (hrk_lt k.castSucc (hL_sub k h1L))⟩⟩ =
            comp ⟨k.castSucc, ⟨a k + 1, Nat.lt_succ_of_le (by have := hal_le_d k; omega)⟩⟩ :=
          hcomp_eq rfl (by dsimp only; omega)
        have ht1 : comp ⟨k.castSucc, ⟨rk k.castSucc s₁ + 1, Nat.succ_lt_succ (hrk_lt k.castSucc (hL_sub k h1L))⟩⟩ =
            comp ⟨k.castSucc, ⟨a k + 2, Nat.lt_succ_of_le (by have := hal_le_d k; omega)⟩⟩ :=
          hcomp_eq rfl (by dsimp only; omega)
        have hb2 : comp ⟨k.castSucc, ⟨rk k.castSucc s₂, Nat.lt_succ_of_lt (hrk_lt k.castSucc (hL_sub k h2L))⟩⟩ =
            comp ⟨k.castSucc, ⟨a k, Nat.lt_succ_of_le (by have := hal_le_d k; omega)⟩⟩ :=
          hcomp_eq rfl (by dsimp only; omega)
        have ht2 : comp ⟨k.castSucc, ⟨rk k.castSucc s₂ + 1, Nat.succ_lt_succ (hrk_lt k.castSucc (hL_sub k h2L))⟩⟩ =
            comp ⟨k.castSucc, ⟨a k + 1, Nat.lt_succ_of_le (by have := hal_le_d k; omega)⟩⟩ :=
          hcomp_eq rfl (by dsimp only; omega)
        rw [hb1, ht1, hb2, ht2, hwrap, Finset.pair_comm]
    · -- s₁ ∈ L k, s₂ ∈ R k => l k = 1, r k = 1!
      have hl1 : l k = 1 := by
        have h1 : 1 ≤ l k := Finset.card_pos.mpr ⟨s₁, h1L⟩
        have h2 : 1 ≤ r k := Finset.card_pos.mpr ⟨s₂, h2R⟩
        omega
      have hr1_eq : r k = 1 := by omega
      have h1r := hrk_L_range k h1L
      have h2r := hrk_R_range k h2R
      rw [hbotFace_eq k.castSucc (hL_sub k h1L), htopFace_eq k.castSucc (hL_sub k h1L),
          hbotFace_eq k.succ (hR_sub k h2R), htopFace_eq k.succ (hR_sub k h2R)]
      have hb1 : comp ⟨k.castSucc, ⟨rk k.castSucc s₁, Nat.lt_succ_of_lt (hrk_lt k.castSucc (hL_sub k h1L))⟩⟩ =
          comp ⟨k.castSucc, ⟨a k, Nat.lt_succ_of_le (by have := hal_le_d k; omega)⟩⟩ :=
        hcomp_eq rfl (by dsimp only; omega)
      have ht1 : comp ⟨k.castSucc, ⟨rk k.castSucc s₁ + 1, Nat.succ_lt_succ (hrk_lt k.castSucc (hL_sub k h1L))⟩⟩ =
          comp ⟨k.castSucc, ⟨a k + l k, Nat.lt_succ_of_le (hal_le_d k)⟩⟩ :=
        hcomp_eq rfl (by dsimp only; omega)
      have hb2 : comp ⟨k.succ, ⟨rk k.succ s₂, Nat.lt_succ_of_lt (hrk_lt k.succ (hR_sub k h2R))⟩⟩ =
          comp ⟨k.succ, ⟨a k, Nat.lt_succ_of_le (by have := har_le_d k; omega)⟩⟩ :=
        hcomp_eq rfl (by dsimp only; omega)
      have ht2 : comp ⟨k.succ, ⟨rk k.succ s₂ + 1, Nat.succ_lt_succ (hrk_lt k.succ (hR_sub k h2R))⟩⟩ =
          comp ⟨k.succ, ⟨a k + r k, Nat.lt_succ_of_le (har_le_d k)⟩⟩ :=
        hcomp_eq rfl (by dsimp only; omega)
      rw [hb1, ht1, hb2, ht2, hbot_eq, htop_eq]
    · -- s₁ ∈ R k, s₂ ∈ L k => l k = 1, r k = 1!
      have hl1 : l k = 1 := by
        have h1 : 1 ≤ r k := Finset.card_pos.mpr ⟨s₁, h1R⟩
        have h2 : 1 ≤ l k := Finset.card_pos.mpr ⟨s₂, h2L⟩
        omega
      have hr1_eq : r k = 1 := by omega
      have h1r := hrk_R_range k h1R
      have h2r := hrk_L_range k h2L
      rw [hbotFace_eq k.succ (hR_sub k h1R), htopFace_eq k.succ (hR_sub k h1R),
          hbotFace_eq k.castSucc (hL_sub k h2L), htopFace_eq k.castSucc (hL_sub k h2L)]
      have hb1 : comp ⟨k.succ, ⟨rk k.succ s₁, Nat.lt_succ_of_lt (hrk_lt k.succ (hR_sub k h1R))⟩⟩ =
          comp ⟨k.succ, ⟨a k, Nat.lt_succ_of_le (by have := har_le_d k; omega)⟩⟩ :=
        hcomp_eq rfl (by dsimp only; omega)
      have ht1 : comp ⟨k.succ, ⟨rk k.succ s₁ + 1, Nat.succ_lt_succ (hrk_lt k.succ (hR_sub k h1R))⟩⟩ =
          comp ⟨k.succ, ⟨a k + r k, Nat.lt_succ_of_le (har_le_d k)⟩⟩ :=
        hcomp_eq rfl (by dsimp only; omega)
      have hb2 : comp ⟨k.castSucc, ⟨rk k.castSucc s₂, Nat.lt_succ_of_lt (hrk_lt k.castSucc (hL_sub k h2L))⟩⟩ =
          comp ⟨k.castSucc, ⟨a k, Nat.lt_succ_of_le (by have := hal_le_d k; omega)⟩⟩ :=
        hcomp_eq rfl (by dsimp only; omega)
      have ht2 : comp ⟨k.castSucc, ⟨rk k.castSucc s₂ + 1, Nat.succ_lt_succ (hrk_lt k.castSucc (hL_sub k h2L))⟩⟩ =
          comp ⟨k.castSucc, ⟨a k + l k, Nat.lt_succ_of_le (hal_le_d k)⟩⟩ :=
        hcomp_eq rfl (by dsimp only; omega)
      rw [hb1, ht1, hb2, ht2, hbot_eq, htop_eq]
    · -- Both in R k => r k = 2, l k = 0!
      have hr2 : r k = 2 := by
        have hsub : ({s₁, s₂} : Finset _) ⊆ R k := by
          intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz
          rcases hz with rfl | rfl <;> assumption
        have h2 : 2 ≤ r k := by rw [← Finset.card_pair hsame]; exact Finset.card_le_card hsub
        omega
      have hl0 : l k = 0 := by omega
      have hwrap : comp ⟨k.succ, ⟨a k, Nat.lt_succ_of_le (by have := har_le_d k; omega)⟩⟩ =
          comp ⟨k.succ, ⟨a k + 2, Nat.lt_succ_of_le (by have := har_le_d k; omega)⟩⟩ := by
        have h1' := hbot_eq
        have h2' := htop_eq
        simp only [hl0, hr2, add_zero] at h2'
        exact h1'.symm.trans h2'
      have h1r := hrk_R_range k h1R
      have h2r := hrk_R_range k h2R
      have hrne : rk k.succ s₁ ≠ rk k.succ s₂ := fun h => hsame (hrk_inj k.succ (hR_sub k h1R) (hR_sub k h2R) h)
      rw [hbotFace_eq k.succ (hR_sub k h1R), htopFace_eq k.succ (hR_sub k h1R),
          hbotFace_eq k.succ (hR_sub k h2R), htopFace_eq k.succ (hR_sub k h2R)]
      have hcases : (rk k.succ s₁ = a k ∧ rk k.succ s₂ = a k + 1) ∨
                    (rk k.succ s₁ = a k + 1 ∧ rk k.succ s₂ = a k) := by omega
      rcases hcases with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · have hb1 : comp ⟨k.succ, ⟨rk k.succ s₁, Nat.lt_succ_of_lt (hrk_lt k.succ (hR_sub k h1R))⟩⟩ =
            comp ⟨k.succ, ⟨a k, Nat.lt_succ_of_le (by have := har_le_d k; omega)⟩⟩ :=
          hcomp_eq rfl (by dsimp only; omega)
        have ht1 : comp ⟨k.succ, ⟨rk k.succ s₁ + 1, Nat.succ_lt_succ (hrk_lt k.succ (hR_sub k h1R))⟩⟩ =
            comp ⟨k.succ, ⟨a k + 1, Nat.lt_succ_of_le (by have := har_le_d k; omega)⟩⟩ :=
          hcomp_eq rfl (by dsimp only; omega)
        have hb2 : comp ⟨k.succ, ⟨rk k.succ s₂, Nat.lt_succ_of_lt (hrk_lt k.succ (hR_sub k h2R))⟩⟩ =
            comp ⟨k.succ, ⟨a k + 1, Nat.lt_succ_of_le (by have := har_le_d k; omega)⟩⟩ :=
          hcomp_eq rfl (by dsimp only; omega)
        have ht2 : comp ⟨k.succ, ⟨rk k.succ s₂ + 1, Nat.succ_lt_succ (hrk_lt k.succ (hR_sub k h2R))⟩⟩ =
            comp ⟨k.succ, ⟨a k + 2, Nat.lt_succ_of_le (by have := har_le_d k; omega)⟩⟩ :=
          hcomp_eq rfl (by dsimp only; omega)
        rw [hb1, ht1, hb2, ht2, hwrap, Finset.pair_comm]
      · have hb1 : comp ⟨k.succ, ⟨rk k.succ s₁, Nat.lt_succ_of_lt (hrk_lt k.succ (hR_sub k h1R))⟩⟩ =
            comp ⟨k.succ, ⟨a k + 1, Nat.lt_succ_of_le (by have := har_le_d k; omega)⟩⟩ :=
          hcomp_eq rfl (by dsimp only; omega)
        have ht1 : comp ⟨k.succ, ⟨rk k.succ s₁ + 1, Nat.succ_lt_succ (hrk_lt k.succ (hR_sub k h1R))⟩⟩ =
            comp ⟨k.succ, ⟨a k + 2, Nat.lt_succ_of_le (by have := har_le_d k; omega)⟩⟩ :=
          hcomp_eq rfl (by dsimp only; omega)
        have hb2 : comp ⟨k.succ, ⟨rk k.succ s₂, Nat.lt_succ_of_lt (hrk_lt k.succ (hR_sub k h2R))⟩⟩ =
            comp ⟨k.succ, ⟨a k, Nat.lt_succ_of_le (by have := har_le_d k; omega)⟩⟩ :=
          hcomp_eq rfl (by dsimp only; omega)
        have ht2 : comp ⟨k.succ, ⟨rk k.succ s₂ + 1, Nat.succ_lt_succ (hrk_lt k.succ (hR_sub k h2R))⟩⟩ =
            comp ⟨k.succ, ⟨a k + 1, Nat.lt_succ_of_le (by have := har_le_d k; omega)⟩⟩ :=
          hcomp_eq rfl (by dsimp only; omega)
        rw [hb1, ht1, hb2, ht2, hwrap, Finset.pair_comm]
  -- Hence every segment of edge i ∈ E has the SAME unordered pair {botFace s, topFace s}!
  have hedge_facePair_const : ∀ i ∈ E, ∀ s₁ ∈ D.S, ∀ s₂ ∈ D.S,
      D.edgeOf s₁ = i → D.edgeOf s₂ = i →
      ({botFace s₁, topFace s₁} : Finset Gslab.ConnectedComponent) = {botFace s₂, topFace s₂} := by
    intro i hi s₁ hs₁ s₂ hs₂ he₁ he₂
    let Si := D.S.filter (fun s => D.edgeOf s = i)
    let P : ((ℝ × ℝ) × (ℝ × ℝ)) → Prop := fun s =>
      ({botFace s, topFace s} : Finset Gslab.ConnectedComponent) = {botFace s₁, topFace s₁}
    have hconn := (D.hpath i hi).2.2.2.2 P (by
      intro v hv t₁ ht₁ t₂ ht₂ hi₁ hi₂
      have hvQA : v ∈ D.Q \ A := (Finset.mem_filter.mp hv).1
      obtain ⟨k, hk⟩ := hq_surj v (Finset.mem_sdiff.mp hvQA).1
      have hdeg2 : l k + r k = 2 := by
        have hcard := (D.hQ_internal v hvQA).1
        have hunion : D.S.filter (fun s => s.1 = q k ∨ s.2 = q k) = R k ∪ L k := by
          ext s; simp only [Finset.mem_union, R, L, Finset.mem_filter]; tauto
        have hdisj : Disjoint (R k) (L k) := by
          rw [Finset.disjoint_left]; intro s h1 h2
          have := (D.hS_mem s (Finset.mem_filter.mp h1).1).2.2
          rw [(Finset.mem_filter.mp h1).2, (Finset.mem_filter.mp h2).2] at this
          linarith
        rw [← hk, hunion, Finset.card_union_of_disjoint hdisj] at hcard
        change r k + l k = 2 at hcard; omega
      have heq := hdeg2_facePair k hdeg2 t₁ (Finset.mem_filter.mp ht₁).1 t₂ (Finset.mem_filter.mp ht₂).1
        (hk.symm ▸ hi₁) (hk.symm ▸ hi₂)
      dsimp only [P]; rw [heq])
    exact ((hconn s₁ (Finset.mem_filter.mpr ⟨hs₁, he₁⟩) s₂ (Finset.mem_filter.mpr ⟨hs₂, he₂⟩)).mp rfl).symm
  -- Define boundary edge set ∂E c for each bounded face c ≠ cOut
  let bdryS (c : Gslab.ConnectedComponent) : Finset ((ℝ × ℝ) × (ℝ × ℝ)) :=
    D.S.filter (fun s => (botFace s = c) ≠ (topFace s = c))
  let bdryE (c : Gslab.ConnectedComponent) : Finset ℕ :=
    E.filter (fun i => ∃ s ∈ D.S, D.edgeOf s = i ∧ s ∈ bdryS c)
  have hbdryS_iff_bdryE : ∀ (c : Gslab.ConnectedComponent) {s}, s ∈ D.S →
      (s ∈ bdryS c ↔ D.edgeOf s ∈ bdryE c) := by
    intro c s hs
    have hi : D.edgeOf s ∈ E := D.hedgeOf_mem s hs
    constructor
    · intro h
      exact Finset.mem_filter.mpr ⟨hi, s, hs, rfl, h⟩
    · intro h
      obtain ⟨t, htS, hte, htb⟩ := (Finset.mem_filter.mp h).2
      have hpair := hedge_facePair_const (D.edgeOf s) hi s hs t htS rfl hte
      have htb' := (Finset.mem_filter.mp htb).2
      -- Note: (a = c) ≠ (b = c) iff c ∈ {a, b} ∧ ({a, b}.card = 2)
      have hchar : ∀ a b : Gslab.ConnectedComponent,
          ((a = c) ≠ (b = c)) ↔ (c ∈ ({a, b} : Finset _) ∧ a ≠ b) := by
        intro a b
        simp only [Finset.mem_insert, Finset.mem_singleton, ne_eq]
        constructor
        · intro hne
          by_cases ha : a = c
          · exact ⟨Or.inl ha.symm, fun hab => hne (by rw [← hab])⟩
          · by_cases hb : b = c
            · exact ⟨Or.inr hb.symm, fun hab => ha (hab.trans hb)⟩
            · exfalso; exact hne (by simp [ha, hb])
        · rintro ⟨hc1 | hc2, hab⟩ heq
          · have ha : a = c := hc1.symm
            have hb : b = c := (iff_of_eq heq).mp ha
            exact hab (ha.trans hb.symm)
          · have hb : b = c := hc2.symm
            have ha : a = c := (iff_of_eq heq).mpr hb
            exact hab (ha.trans hb.symm)
      have hcard2 : ∀ a b : Gslab.ConnectedComponent,
          a ≠ b ↔ ({a, b} : Finset _).card = 2 := by
        intro a b
        constructor
        · intro h; exact Finset.card_pair h
        · intro h hab; subst hab; simp at h
      refine Finset.mem_filter.mpr ⟨hs, ?_⟩
      rw [hchar, hcard2, hpair, ← hcard2, ← hchar]
      exact htb'
  -- Step A: For every c ≠ cOut, bdryS c is nonempty, hence bdryE c is nonempty!
  have hbdryE_nonempty : ∀ c : Gslab.ConnectedComponent, c ≠ cOut → (bdryE c).Nonempty := by
    intro c hc
    -- Pick a slab in c minimizing j.val!
    have hex : ∃ u : Slab, comp u = c := by
      induction c using SimpleGraph.ConnectedComponent.ind with | _ u => exact ⟨u, rfl⟩
    let Sc : Finset Slab := Finset.univ.filter (fun u => comp u = c)
    have hSc_ne : Sc.Nonempty := by
      obtain ⟨u, hu⟩ := hex
      exact ⟨u, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu⟩⟩
    obtain ⟨u, hu_mem, hu_min⟩ := Finset.exists_min_image Sc (fun u => u.2.val) hSc_ne
    have huc : comp u = c := (Finset.mem_filter.mp hu_mem).2
    have hu_pos : 0 < u.2.val := by
      by_contra h0
      have : comp u = cOut :=
        (hcomp_eq (kA := u.1) (kB := u.1) rfl (jA := u.2) (jB := ⟨0, Nat.zero_lt_succ _⟩) (by dsimp only; omega)).trans
          (hbot_cOut u.1)
      exact hc (huc.symm.trans this)
    -- So u.2.val - 1 < d u.1; let s ∈ Active u.1 have rk u.1 s = u.2.val - 1!
    obtain ⟨s, hsA, hsrk⟩ := hrk_surj u.1 (u.2.val - 1) (by have := u.2.isLt; omega)
    have hS : s ∈ D.S := (hActive_bounds u.1 s hsA).2.1
    have htop_c : topFace s = c := by
      rw [htopFace_eq u.1 hsA]
      exact (hcomp_eq (kA := u.1) (kB := u.1) rfl (jA := ⟨rk u.1 s + 1, Nat.succ_lt_succ (hrk_lt u.1 hsA)⟩)
        (jB := u.2) (by dsimp only; omega)).trans huc
    have hbot_nc : botFace s ≠ c := by
      rw [hbotFace_eq u.1 hsA]
      intro hbc
      let u' : Slab := ⟨u.1, ⟨rk u.1 s, Nat.lt_succ_of_lt (hrk_lt u.1 hsA)⟩⟩
      have hu'_mem : u' ∈ Sc := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbc⟩
      have hle := hu_min u' hu'_mem
      dsimp only [u'] at hle
      omega
    have hs_bdry : s ∈ bdryS c := Finset.mem_filter.mpr ⟨hS, by simp [htop_c, hbot_nc]⟩
    exact ⟨D.edgeOf s, (hbdryS_iff_bdryE c hS).mp hs_bdry⟩
  -- Step B: For every c and every vertex q k, deg_{bdryS c}(q k) is EVEN!
  have hbdryS_even : ∀ (c : Gslab.ConnectedComponent) (k : Fin M),
      Even ((bdryS c).filter (fun s => s.1 = q k ∨ s.2 = q k)).card := by
    intro c k
    have hsplit : (bdryS c).filter (fun s => s.1 = q k ∨ s.2 = q k) =
        ((L k).filter (fun s => s ∈ bdryS c)) ∪ ((R k).filter (fun s => s ∈ bdryS c)) := by
      ext s
      simp only [Finset.mem_union, Finset.mem_filter, L, R, bdryS]
      tauto
    have hdisj : Disjoint ((L k).filter (fun s => s ∈ bdryS c)) ((R k).filter (fun s => s ∈ bdryS c)) := by
      rw [Finset.disjoint_left]; intro s h1 h2
      have hS := (Finset.mem_filter.mp (Finset.mem_filter.mp h1).1).1
      have e1 := (Finset.mem_filter.mp (Finset.mem_filter.mp h1).1).2
      have e2 := (Finset.mem_filter.mp (Finset.mem_filter.mp h2).1).2
      have := (D.hS_mem s hS).2.2
      rw [e1, e2] at this; linarith
    rw [hsplit, Finset.card_union_of_disjoint hdisj]
    -- Biject L k onto Fin (l k) via rk k.castSucc - a k, and R k onto Fin (r k) via rk k.succ - a k!
    let fL : Fin (l k + 1) → Bool := fun t =>
      decide (comp ⟨k.castSucc, ⟨a k + t.val, by have := hal_le_d k; omega⟩⟩ = c)
    let fR : Fin (r k + 1) → Bool := fun t =>
      decide (comp ⟨k.succ, ⟨a k + t.val, by have := har_le_d k; omega⟩⟩ = c)
    have hL_card : ((L k).filter (fun s => s ∈ bdryS c)).card =
        ((Finset.univ : Finset (Fin (l k))).filter (fun t => fL t.castSucc ≠ fL t.succ)).card := by
      refine Finset.card_bij
        (fun s hs => ⟨rk k.castSucc s - a k, by
          have h1 := hrk_L_range k (Finset.mem_filter.mp hs).1; omega⟩) ?_ ?_ ?_
      · intro s hs
        have hsL := (Finset.mem_filter.mp hs).1
        have hsb := (Finset.mem_filter.mp (Finset.mem_filter.mp hs).2).2
        have h1 := hrk_L_range k hsL
        have hsA := hL_sub k hsL
        rw [hbotFace_eq k.castSucc hsA, htopFace_eq k.castSucc hsA] at hsb
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        dsimp only [fL, Fin.val_castSucc, Fin.val_succ]
        have he1 : comp ⟨k.castSucc, ⟨a k + (rk k.castSucc s - a k), by have := hal_le_d k; omega⟩⟩ =
            comp ⟨k.castSucc, ⟨rk k.castSucc s, Nat.lt_succ_of_lt (hrk_lt k.castSucc hsA)⟩⟩ :=
          hcomp_eq rfl (by dsimp only; omega)
        have he2 : comp ⟨k.castSucc, ⟨a k + (rk k.castSucc s - a k + 1), by have := hal_le_d k; omega⟩⟩ =
            comp ⟨k.castSucc, ⟨rk k.castSucc s + 1, Nat.succ_lt_succ (hrk_lt k.castSucc hsA)⟩⟩ :=
          hcomp_eq rfl (by dsimp only; omega)
        simp only [he1, he2]
        intro hdec
        exact hsb (by simpa [decide_eq_decide] using hdec)
      · intro s₁ hs₁ s₂ hs₂ heq
        have h1 := hrk_L_range k (Finset.mem_filter.mp hs₁).1
        have h2 := hrk_L_range k (Finset.mem_filter.mp hs₂).1
        have hv := congrArg Fin.val heq; dsimp only at hv
        exact hrk_inj k.castSucc (hL_sub k (Finset.mem_filter.mp hs₁).1)
          (hL_sub k (Finset.mem_filter.mp hs₂).1) (by omega)
      · intro t ht
        have htf := (Finset.mem_filter.mp ht).2
        obtain ⟨s, hsA, hsrk⟩ := hrk_surj k.castSucc (a k + t.val) (by have := hal_le_d k; omega)
        have hsL : s ∈ L k := by
          rw [hActiveL_eq k, hPass_split k] at hsA
          rcases Finset.mem_union.mp hsA with hsP | hsL
          · rcases Finset.mem_union.mp hsP with hB | hA
            · have := (hrk_Below_eq k hB).2; omega
            · have := (hrk_Above_eq k hA).1; omega
          · exact hsL
        have hS := (Finset.mem_filter.mp hsL).1
        have hsb : s ∈ bdryS c := by
          refine Finset.mem_filter.mpr ⟨hS, ?_⟩
          rw [hbotFace_eq k.castSucc hsA, htopFace_eq k.castSucc hsA]
          have he1 : comp ⟨k.castSucc, ⟨rk k.castSucc s, Nat.lt_succ_of_lt (hrk_lt k.castSucc hsA)⟩⟩ =
              comp ⟨k.castSucc, ⟨a k + t.val, by have := hal_le_d k; omega⟩⟩ :=
            hcomp_eq rfl (by dsimp only; omega)
          have he2 : comp ⟨k.castSucc, ⟨rk k.castSucc s + 1, Nat.succ_lt_succ (hrk_lt k.castSucc hsA)⟩⟩ =
              comp ⟨k.castSucc, ⟨a k + (t.val + 1), by have := hal_le_d k; omega⟩⟩ :=
            hcomp_eq rfl (by dsimp only; omega)
          rw [he1, he2]
          intro heq
          apply htf
          dsimp only [fL, Fin.val_castSucc, Fin.val_succ]
          exact decide_eq_decide.mpr (iff_of_eq heq)
        exact ⟨s, Finset.mem_filter.mpr ⟨hsL, hsb⟩, Fin.ext (by dsimp only; omega)⟩
    have hR_card : ((R k).filter (fun s => s ∈ bdryS c)).card =
        ((Finset.univ : Finset (Fin (r k))).filter (fun t => fR t.castSucc ≠ fR t.succ)).card := by
      refine Finset.card_bij
        (fun s hs => ⟨rk k.succ s - a k, by
          have h1 := hrk_R_range k (Finset.mem_filter.mp hs).1; omega⟩) ?_ ?_ ?_
      · intro s hs
        have hsR := (Finset.mem_filter.mp hs).1
        have hsb := (Finset.mem_filter.mp (Finset.mem_filter.mp hs).2).2
        have h1 := hrk_R_range k hsR
        have hsA := hR_sub k hsR
        rw [hbotFace_eq k.succ hsA, htopFace_eq k.succ hsA] at hsb
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        dsimp only [fR, Fin.val_castSucc, Fin.val_succ]
        have he1 : comp ⟨k.succ, ⟨a k + (rk k.succ s - a k), by have := har_le_d k; omega⟩⟩ =
            comp ⟨k.succ, ⟨rk k.succ s, Nat.lt_succ_of_lt (hrk_lt k.succ hsA)⟩⟩ :=
          hcomp_eq rfl (by dsimp only; omega)
        have he2 : comp ⟨k.succ, ⟨a k + (rk k.succ s - a k + 1), by have := har_le_d k; omega⟩⟩ =
            comp ⟨k.succ, ⟨rk k.succ s + 1, Nat.succ_lt_succ (hrk_lt k.succ hsA)⟩⟩ :=
          hcomp_eq rfl (by dsimp only; omega)
        simp only [he1, he2]
        intro hdec
        exact hsb (by simpa [decide_eq_decide] using hdec)
      · intro s₁ hs₁ s₂ hs₂ heq
        have h1 := hrk_R_range k (Finset.mem_filter.mp hs₁).1
        have h2 := hrk_R_range k (Finset.mem_filter.mp hs₂).1
        have hv := congrArg Fin.val heq; dsimp only at hv
        exact hrk_inj k.succ (hR_sub k (Finset.mem_filter.mp hs₁).1)
          (hR_sub k (Finset.mem_filter.mp hs₂).1) (by omega)
      · intro t ht
        have htf := (Finset.mem_filter.mp ht).2
        obtain ⟨s, hsA, hsrk⟩ := hrk_surj k.succ (a k + t.val) (by have := har_le_d k; omega)
        have hsR : s ∈ R k := by
          rw [hActiveR_eq k, hPass_split k] at hsA
          rcases Finset.mem_union.mp hsA with hsP | hsR
          · rcases Finset.mem_union.mp hsP with hB | hA
            · obtain ⟨h1, h2⟩ := hrk_Below_eq k hB; omega
            · obtain ⟨h1, h2⟩ := hrk_Above_eq k hA; omega
          · exact hsR
        have hS := (Finset.mem_filter.mp hsR).1
        have hsb : s ∈ bdryS c := by
          refine Finset.mem_filter.mpr ⟨hS, ?_⟩
          rw [hbotFace_eq k.succ hsA, htopFace_eq k.succ hsA]
          have he1 : comp ⟨k.succ, ⟨rk k.succ s, Nat.lt_succ_of_lt (hrk_lt k.succ hsA)⟩⟩ =
              comp ⟨k.succ, ⟨a k + t.val, by have := har_le_d k; omega⟩⟩ :=
            hcomp_eq rfl (by dsimp only; omega)
          have he2 : comp ⟨k.succ, ⟨rk k.succ s + 1, Nat.succ_lt_succ (hrk_lt k.succ hsA)⟩⟩ =
              comp ⟨k.succ, ⟨a k + (t.val + 1), by have := har_le_d k; omega⟩⟩ :=
            hcomp_eq rfl (by dsimp only; omega)
          rw [he1, he2]
          intro heq
          apply htf
          dsimp only [fR, Fin.val_castSucc, Fin.val_succ]
          exact decide_eq_decide.mpr (iff_of_eq heq)
        exact ⟨s, Finset.mem_filter.mpr ⟨hsR, hsb⟩, Fin.ext (by dsimp only; omega)⟩
    have hf0 : fL 0 = fR 0 := by
      have hbot : comp ⟨k.castSucc, ⟨a k + 0, by have := hal_le_d k; omega⟩⟩ =
          comp ⟨k.succ, ⟨a k + 0, by have := har_le_d k; omega⟩⟩ :=
        SimpleGraph.ConnectedComponent.sound (hportal_adj k _ _ (Or.inl ⟨by dsimp only; omega, rfl⟩)).reachable
      show decide (comp ⟨k.castSucc, ⟨a k + 0, by have := hal_le_d k; omega⟩⟩ = c) =
           decide (comp ⟨k.succ, ⟨a k + 0, by have := har_le_d k; omega⟩⟩ = c)
      simp only [hbot]
    have hfl : fL (Fin.last (l k)) = fR (Fin.last (r k)) := by
      dsimp only [fL, fR, Fin.val_last]
      have htop : comp ⟨k.castSucc, ⟨a k + l k, by have := hal_le_d k; omega⟩⟩ =
          comp ⟨k.succ, ⟨a k + r k, by have := har_le_d k; omega⟩⟩ :=
        SimpleGraph.ConnectedComponent.sound (hportal_adj k _ _ (Or.inr ⟨le_refl _, by dsimp only; omega⟩)).reachable
      simp only [htop]
    rw [hL_card, hR_card, Nat.even_iff]
    have hm1 := count_flips_mod_two (l k) fL
    have hm2 := count_flips_mod_two (r k) fR
    rw [hf0, hfl] at hm1
    omega
  -- Step C: Lift even degree from bdryS c to bdryE c at every v ∈ A, so 3 ≤ (bdryE c).card!
  have hbdryE_ge3 : ∀ c : Gslab.ConnectedComponent, c ≠ cOut → 3 ≤ (bdryE c).card := by
    intro c hc
    apply card_ge_three_of_simple_eulerian A (bdryE c) D.uEnd D.vEnd
      (fun i hi => D.hEnd_mem i (Finset.mem_filter.mp hi).1)
      (D.hEnd_simple.mono (fun i hi => (Finset.mem_filter.mp hi).1))
      (hbdryE_nonempty c hc)
    intro v hv
    obtain ⟨k, hk⟩ := hq_surj v (D.hAQ hv)
    have hdeg_eq : ((bdryE c).filter (fun i => D.uEnd i = v ∨ D.vEnd i = v)).card =
        ((bdryS c).filter (fun s => s.1 = q k ∨ s.2 = q k)).card := by
      rw [hk]
      -- Each i ∈ bdryE c incident to v contributes EXACTLY 1 segment in bdryS c incident to v!
      have hfib := Finset.card_eq_sum_card_fiberwise
        (s := (bdryS c).filter (fun s => s.1 = v ∨ s.2 = v))
        (t := (bdryE c).filter (fun i => D.uEnd i = v ∨ D.vEnd i = v))
        (f := D.edgeOf) (by
          intro s hs
          have hs' := Finset.mem_filter.mp hs
          have hS := (Finset.mem_filter.mp hs'.1).1
          have hiE := (hbdryS_iff_bdryE c hS).mp hs'.1
          have hinc_card := (D.hpath (D.edgeOf s) (D.hedgeOf_mem s hS)).2.2.1 v hv
          have hpos : 0 < ((D.S.filter (fun t => D.edgeOf t = D.edgeOf s)).filter
              (fun t => t.1 = v ∨ t.2 = v)).card :=
            Finset.card_pos.mpr ⟨s, Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hS, rfl⟩, hs'.2⟩⟩
          have hvEnd : v = D.uEnd (D.edgeOf s) ∨ v = D.vEnd (D.edgeOf s) := by
            by_contra hno; rw [if_neg hno] at hinc_card; omega
          exact Finset.mem_filter.mpr ⟨hiE, by tauto⟩)
      rw [hfib]
      symm
      rw [Finset.card_eq_sum_ones]
      apply Finset.sum_congr rfl
      intro i hi
      have hi' := Finset.mem_filter.mp hi
      have hiE := (Finset.mem_filter.mp hi'.1).1
      have h1 := (D.hpath i hiE).2.2.1 v hv
      have hv_eq : v = D.uEnd i ∨ v = D.vEnd i := by tauto
      rw [if_pos hv_eq] at h1
      symm; rw [← h1]
      congr 1; ext s
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨⟨hS, hedge⟩, hinc⟩
        exact ⟨⟨(hbdryS_iff_bdryE c hS).mpr (hedge.symm ▸ hi'.1), hinc⟩, hedge⟩
      · rintro ⟨⟨hsb, hinc⟩, hedge⟩
        exact ⟨⟨(Finset.mem_filter.mp hsb).1, hedge⟩, hinc⟩
    rw [hdeg_eq]
    exact hbdryS_even c k
  -- Step D: Double count 3 * (F - 1) ≤ ∑_{c ≠ cOut} (bdryE c).card ≤ 2 * E.card!
  have hdouble : 3 * (F - 1) ≤ 2 * E.card := by
    let Bfaces : Finset Gslab.ConnectedComponent := Finset.univ.erase cOut
    have hBcard : Bfaces.card = F - 1 := by
      dsimp only [Bfaces, F]
      rw [Finset.card_erase_of_mem (Finset.mem_univ cOut), Finset.card_univ]
    have hlo : 3 * (F - 1) ≤ ∑ c ∈ Bfaces, (bdryE c).card := by
      rw [← hBcard, mul_comm, ← smul_eq_mul, ← Finset.sum_const]
      exact Finset.sum_le_sum (fun c hc => hbdryE_ge3 c (Finset.mem_erase.mp hc).1)
    have hhi : ∑ c ∈ Bfaces, (bdryE c).card ≤ 2 * E.card := by
      have hswap : ∑ c ∈ Bfaces, (bdryE c).card =
          ∑ i ∈ E, (Bfaces.filter (fun c => i ∈ bdryE c)).card := by
        calc ∑ c ∈ Bfaces, (bdryE c).card
            = ∑ c ∈ Bfaces, ∑ i ∈ E, if i ∈ bdryE c then 1 else 0 := by
              apply Finset.sum_congr rfl; intro c _
              rw [← Finset.card_filter]
              congr 1; ext i; simp only [Finset.mem_filter, bdryE]; tauto
          _ = ∑ i ∈ E, ∑ c ∈ Bfaces, if i ∈ bdryE c then 1 else 0 := Finset.sum_comm
          _ = _ := by
              apply Finset.sum_congr rfl; intro i _
              rw [Finset.card_filter]
      rw [hswap]
      calc ∑ i ∈ E, (Bfaces.filter (fun c => i ∈ bdryE c)).card
          ≤ ∑ _i ∈ E, 2 := by
            apply Finset.sum_le_sum
            intro i hi
            obtain ⟨s, hs⟩ := (D.hpath i hi).1
            have hS := (Finset.mem_filter.mp hs).1
            have he := (Finset.mem_filter.mp hs).2
            have hsub : Bfaces.filter (fun c => i ∈ bdryE c) ⊆ {botFace s, topFace s} := by
              intro c hc
              have hi_in := (Finset.mem_filter.mp hc).2
              have hsb : s ∈ bdryS c := (hbdryS_iff_bdryE c hS).mpr (he.symm ▸ hi_in)
              have hne := (Finset.mem_filter.mp hsb).2
              simp only [Finset.mem_insert, Finset.mem_singleton]
              by_cases h1 : botFace s = c
              · exact Or.inl h1.symm
              · by_cases h2 : topFace s = c
                · exact Or.inr h2.symm
                · exfalso; exact hne (by simp [h1, h2])
            exact (Finset.card_le_card hsub).trans Finset.card_le_two
        _ = 2 * E.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
    exact hlo.trans hhi
  exact hdouble

/-- Sweep-line vertical slab decomposition proves Euler's bound `E.card ≤ 3 * A.card`
for any crossing-free `x`-distinct polygonal subdivision of a simple graph `(A, E)`. -/
private theorem xDistinctPLSubdiv_edge_bound
    (A : Finset (ℝ × ℝ)) (E : Finset ℕ) (D : XDistinctPLSubdiv A E) :
    E.card ≤ 3 * A.card := by
  let SD := mkSweepData A E D
  have hEuler := sweepData_euler A E D SD
  have hdouble := sweepData_double_count A E D SD
  have hF_pos : 1 ≤ Fintype.card SD.Gslab.ConnectedComponent :=
    Fintype.card_pos_iff.mpr ⟨SD.Gslab.connectedComponentMk ⟨⟨0, Nat.zero_lt_succ SD.M⟩, ⟨0, Nat.zero_lt_succ _⟩⟩⟩
  omega

/- ### Part 2b: Simple polygonal drawing and shear to `XDistinctPLSubdiv` -/

/-- A crossing-free polygonal drawing of a simple graph `(A, E)` in `ℝ × ℝ` given by a simple
polygonal chain `P i : List (ℝ × ℝ)` for each edge `i ∈ E`. -/
private structure SimplePLDrawing (A : Finset (ℝ × ℝ)) (E : Finset ℕ) where
  P : ℕ → List (ℝ × ℝ)
  hlen : ∀ i ∈ E, 2 ≤ (P i).length
  hnodup : ∀ i ∈ E, (P i).Nodup
  hstart : ∀ (i : ℕ) (hi : i ∈ E), (P i)[0]'(by have := hlen i hi; omega) ∈ A
  hend : ∀ (i : ℕ) (hi : i ∈ E), (P i)[(P i).length - 1]'(by have := hlen i hi; omega) ∈ A
  hint_notA : ∀ i ∈ E, ∀ k : ℕ, (hk0 : 0 < k) → (hk1 : k + 1 < (P i).length) →
    (P i)[k]'(by omega) ∉ A
  hsimple : Set.InjOn
    (fun i => if hi : i ∈ E then
      ({(P i)[0]'(by have := hlen i hi; omega),
        (P i)[(P i).length - 1]'(by have := hlen i hi; omega)} : Finset (ℝ × ℝ))
      else ∅) (E : Set ℕ)
  -- Internal vertices of distinct edges are disjoint
  hint_disj : ∀ i ∈ E, ∀ j ∈ E, i ≠ j →
    ∀ k₁ : ℕ, (h1 : 0 < k₁ ∧ k₁ + 1 < (P i).length) →
    ∀ k₂ : ℕ, (h2 : 0 < k₂ ∧ k₂ + 1 < (P j).length) →
    (P i)[k₁]'(by omega) ≠ (P j)[k₂]'(by omega)
  -- No two distinct segments (same or different edges) cross in the interior
  hseg_noncross : ∀ i ∈ E, ∀ j ∈ E,
    ∀ k₁ : ℕ, (h1 : k₁ + 1 < (P i).length) →
    ∀ k₂ : ℕ, (h2 : k₂ + 1 < (P j).length) →
    (i ≠ j ∨ k₁ ≠ k₂) →
    poseg ((P i)[k₁]'(by omega)) ((P i)[k₁ + 1]'h1) ∩
      pseg ((P j)[k₂]'(by omega)) ((P j)[k₂ + 1]'h2) = ∅
  -- No vertex (of A or any chain) lies on any open segment
  hseg_avoid : ∀ i ∈ E, ∀ k : ℕ, (hk : k + 1 < (P i).length) →
    ∀ r : ℝ × ℝ, (r ∈ A ∨ ∃ j ∈ E, r ∈ P j) →
    r ∉ poseg ((P i)[k]'(by omega)) ((P i)[k + 1]'hk)

private lemma exists_shear_inj (Q : Finset (ℝ × ℝ)) :
    ∃ c : ℝ, ∀ p ∈ Q, ∀ q ∈ Q, p.1 + c * p.2 = q.1 + c * q.2 → p = q := by
  classical
  let bad : Finset ℝ :=
    (Q ×ˢ Q).image (fun pq => if pq.1.2 = pq.2.2 then 0 else -(pq.1.1 - pq.2.1) / (pq.1.2 - pq.2.2))
  -- ℝ is infinite, so pick c ∉ bad
  have hinf : (Set.univ : Set ℝ).Infinite := Set.infinite_univ
  obtain ⟨c, -, hc⟩ := hinf.exists_notMem_finset bad
  refine ⟨c, fun p hp q hq heq => ?_⟩
  by_cases hy : p.2 = q.2
  · exact Prod.ext (by rw [hy] at heq; linarith) hy
  · exfalso
    apply hc
    refine Finset.mem_image.mpr ⟨(p, q), Finset.mem_product.mpr ⟨hp, hq⟩, ?_⟩
    rw [if_neg hy]
    have hne : p.2 - q.2 ≠ 0 := sub_ne_zero.mpr hy
    field_simp [hne]
    linarith

private lemma simplePLDrawing_edge_bound
    (A : Finset (ℝ × ℝ)) (E : Finset ℕ) (D : SimplePLDrawing A E) :
    E.card ≤ 3 * A.card := by
  classical
  -- Collect all vertices Q0 = A ∪ ⋃_{i ∈ E} (P i).toFinset
  let Q0 : Finset (ℝ × ℝ) := A ∪ E.biUnion (fun i => (D.P i).toFinset)
  obtain ⟨c, hc_inj⟩ := exists_shear_inj Q0
  let φ : ℝ × ℝ → ℝ × ℝ := fun p => (p.1 + c * p.2, p.2)
  have hφ_inj : Function.Injective φ := by
    intro p q h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    dsimp only [φ] at h1 h2
    exact Prod.ext (by rw [h2] at h1; linarith) h2
  have hφ_pseg : ∀ p q r : ℝ × ℝ, φ r ∈ pseg (φ p) (φ q) ↔ r ∈ pseg p q := by
    intro p q r
    constructor
    · rintro ⟨t, ht0, ht1, hr⟩
      refine ⟨t, ht0, ht1, ?_⟩
      apply hφ_inj
      rw [hr]; apply Prod.ext <;> (dsimp only [φ]; try ring)
    · rintro ⟨t, ht0, ht1, hr⟩
      refine ⟨t, ht0, ht1, ?_⟩
      rw [hr]; apply Prod.ext <;> (dsimp only [φ]; try ring)
  have hφ_poseg : ∀ p q r : ℝ × ℝ, φ r ∈ poseg (φ p) (φ q) ↔ r ∈ poseg p q := by
    intro p q r
    constructor
    · rintro ⟨t, ht0, ht1, hr⟩
      refine ⟨t, ht0, ht1, ?_⟩
      apply hφ_inj
      rw [hr]; apply Prod.ext <;> (dsimp only [φ]; try ring)
    · rintro ⟨t, ht0, ht1, hr⟩
      refine ⟨t, ht0, ht1, ?_⟩
      rw [hr]; apply Prod.ext <;> (dsimp only [φ]; try ring)
  have hpseg_comm : ∀ p q : ℝ × ℝ, pseg p q = pseg q p := by
    intro p q; ext r; constructor <;>
    · rintro ⟨t, ht0, ht1, hr⟩
      refine ⟨1 - t, by linarith, by linarith, ?_⟩
      rw [hr]; apply Prod.ext <;> ring
  have hposeg_comm : ∀ p q : ℝ × ℝ, poseg p q = poseg q p := by
    intro p q; ext r; constructor <;>
    · rintro ⟨t, ht0, ht1, hr⟩
      refine ⟨1 - t, by linarith, by linarith, ?_⟩
      rw [hr]; apply Prod.ext <;> ring
  -- Helper: orient segment (φ a, φ b) left-to-right
  let orient (a b : ℝ × ℝ) : (ℝ × ℝ) × (ℝ × ℝ) :=
    if (φ a).1 < (φ b).1 then (φ a, φ b) else (φ b, φ a)
  have horient_lt : ∀ a b : ℝ × ℝ, a ∈ Q0 → b ∈ Q0 → a ≠ b → (orient a b).1.1 < (orient a b).2.1 := by
    intro a b ha hb hab
    have hne : (φ a).1 ≠ (φ b).1 := fun h => hab (hc_inj a ha b hb h)
    dsimp only [orient]
    split_ifs with h
    · exact h
    · exact lt_of_le_of_ne (not_lt.mp h) hne.symm
  have horient_pseg : ∀ a b : ℝ × ℝ, pseg (orient a b).1 (orient a b).2 = pseg (φ a) (φ b) := by
    intro a b; dsimp only [orient]; split_ifs
    · rfl
    · exact hpseg_comm _ _
  have horient_poseg : ∀ a b : ℝ × ℝ, poseg (orient a b).1 (orient a b).2 = poseg (φ a) (φ b) := by
    intro a b; dsimp only [orient]; split_ifs
    · rfl
    · exact hposeg_comm _ _
  have horient_ends : ∀ a b r : ℝ × ℝ, ((orient a b).1 = φ r ∨ (orient a b).2 = φ r) ↔ (a = r ∨ b = r) := by
    intro a b r
    dsimp only [orient]
    split_ifs <;> (simp only [hφ_inj.eq_iff]; try tauto)
  have horient_eq : ∀ a b c d : ℝ × ℝ, orient a b = orient c d →
      (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
    intro a b c d h
    dsimp only [orient] at h
    split_ifs at h with h1 h2 h2
    · exact Or.inl ⟨hφ_inj (congrArg Prod.fst h), hφ_inj (congrArg Prod.snd h)⟩
    · exact Or.inr ⟨hφ_inj (congrArg Prod.fst h), hφ_inj (congrArg Prod.snd h)⟩
    · exact Or.inr ⟨hφ_inj (congrArg Prod.snd h), hφ_inj (congrArg Prod.fst h)⟩
    · exact Or.inl ⟨hφ_inj (congrArg Prod.snd h), hφ_inj (congrArg Prod.fst h)⟩
  -- For each i ∈ E, list its segments as a Finset
  let segAt (i : ℕ) (hi : i ∈ E) (k : Fin ((D.P i).length - 1)) : (ℝ × ℝ) × (ℝ × ℝ) :=
    orient ((D.P i)[k.val]'(by have := k.isLt; omega)) ((D.P i)[k.val + 1]'(by have := k.isLt; omega))
  let Si_set (i : ℕ) : Finset ((ℝ × ℝ) × (ℝ × ℝ)) :=
    if hi : i ∈ E then Finset.univ.image (segAt i hi) else ∅
  -- Distinct pairs (i, k₁) ≠ (j, k₂) produce distinct oriented segments!
  have hseg_disj_all : ∀ (i : ℕ) (hi : i ∈ E) (k₁ : Fin ((D.P i).length - 1))
      (j : ℕ) (hj : j ∈ E) (k₂ : Fin ((D.P j).length - 1)),
      segAt i hi k₁ = segAt j hj k₂ → i = j ∧ k₁.val = k₂.val := by
    intro i hi k₁ j hj k₂ heq
    have hcases := horient_eq _ _ _ _ heq
    have hne_i : (D.P i)[k₁.val]'(by omega) ≠ (D.P i)[k₁.val + 1]'(by omega) := by
      intro h
      have := (D.hnodup i hi).getElem_inj_iff.mp h
      omega
    -- Check if (i ≠ j ∨ k₁.val ≠ k₂.val), then the midpoint of segAt i hi k₁ lies in poseg of both!
    by_contra hnot
    have hdiff : i ≠ j ∨ k₁.val ≠ k₂.val := by
      by_cases hij : i = j
      · right; intro hk; exact hnot ⟨hij, hk⟩
      · left; exact hij
    have hemp := D.hseg_noncross i hi j hj k₁.val (by omega) k₂.val (by omega) hdiff
    let a := (D.P i)[k₁.val]'(by omega)
    let b := (D.P i)[k₁.val + 1]'(by omega)
    let m : ℝ × ℝ := ((1 - (1 / 2 : ℝ)) * a.1 + (1 / 2 : ℝ) * b.1,
                      (1 - (1 / 2 : ℝ)) * a.2 + (1 / 2 : ℝ) * b.2)
    have hm1 : m ∈ poseg a b := ⟨1 / 2, by norm_num, by norm_num, rfl⟩
    have hm2 : m ∈ pseg ((D.P j)[k₂.val]'(by omega)) ((D.P j)[k₂.val + 1]'(by omega)) := by
      rcases hcases with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [← h1, ← h2]; exact ⟨1 / 2, by norm_num, by norm_num, rfl⟩
      · rw [← h1, ← h2, hpseg_comm]; exact ⟨1 / 2, by norm_num, by norm_num, rfl⟩
    exact (hemp ▸ ⟨hm1, hm2⟩ : m ∈ (∅ : Set (ℝ × ℝ)))
  -- Total segment set S = E.biUnion Si_set
  let S : Finset ((ℝ × ℝ) × (ℝ × ℝ)) := E.biUnion Si_set
  have hS_mem_iff : ∀ s, s ∈ S ↔ ∃ i ∈ E, ∃ hi : i ∈ E, ∃ k : Fin ((D.P i).length - 1), segAt i hi k = s := by
    intro s
    simp only [S, Finset.mem_biUnion, Si_set]
    constructor
    · rintro ⟨i, hi, hs⟩
      rw [dif_pos hi] at hs
      obtain ⟨k, -, hk⟩ := Finset.mem_image.mp hs
      exact ⟨i, hi, hi, k, hk⟩
    · rintro ⟨i, hi, _, k, rfl⟩
      refine ⟨i, hi, ?_⟩
      rw [dif_pos hi]
      exact Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩
  let edgeOf : (ℝ × ℝ) × (ℝ × ℝ) → ℕ := fun s =>
    if h : ∃ i ∈ E, s ∈ Si_set i then h.choose else 0
  have hedgeOf_eq : ∀ (i : ℕ) (hi : i ∈ E) (k : Fin ((D.P i).length - 1)),
      edgeOf (segAt i hi k) = i := by
    intro i hi k
    have hex : ∃ j ∈ E, segAt i hi k ∈ Si_set j := by
      refine ⟨i, hi, ?_⟩; dsimp only [Si_set]; rw [dif_pos hi]
      exact Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩
    dsimp only [edgeOf]; rw [dif_pos hex]
    have hch := hex.choose_spec
    have hsj := hch.2; dsimp only [Si_set] at hsj; rw [dif_pos hch.1] at hsj
    obtain ⟨k₂, -, hk₂⟩ := Finset.mem_image.mp hsj
    exact (hseg_disj_all _ hch.1 k₂ i hi k hk₂).1
  have hS_filter_eq : ∀ i ∈ E, S.filter (fun s => edgeOf s = i) = Si_set i := by
    intro i hi; ext s
    simp only [Finset.mem_filter, hS_mem_iff]
    constructor
    · rintro ⟨⟨j, hj, _, k, rfl⟩, he⟩
      rw [hedgeOf_eq j hj k] at he; subst he
      dsimp only [Si_set]; rw [dif_pos hi]
      exact Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩
    · intro hs
      dsimp only [Si_set] at hs; rw [dif_pos hi] at hs
      obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hs
      exact ⟨⟨i, hi, hi, k, rfl⟩, hedgeOf_eq i hi k⟩
  have hSi_card : ∀ i ∈ E, (Si_set i).card = (D.P i).length - 1 := by
    intro i hi
    dsimp only [Si_set]; rw [dif_pos hi]
    rw [Finset.card_image_of_injective _ (fun k₁ k₂ h => Fin.ext (hseg_disj_all i hi k₁ i hi k₂ h).2)]
    simp
  -- Construct the XDistinctPLSubdiv on A.image φ and E!
  let A' : Finset (ℝ × ℝ) := A.image φ
  let Q' : Finset (ℝ × ℝ) := Q0.image φ
  have hAQ' : A' ⊆ Q' := Finset.image_subset_image Finset.subset_union_left
  have hQ'_sdiff : Q' \ A' = (Q0 \ A).image φ := by
    ext z
    simp only [Finset.mem_sdiff, Finset.mem_image, Q', A']
    constructor
    · rintro ⟨⟨p, hp, rfl⟩, hna⟩
      exact ⟨p, ⟨hp, fun ha => hna ⟨p, ha, rfl⟩⟩, rfl⟩
    · rintro ⟨p, ⟨hp, hna⟩, rfl⟩
      exact ⟨⟨p, hp, rfl⟩, fun ⟨q, hq, heq⟩ => hna (hφ_inj heq ▸ hq)⟩
  -- For any r ∈ Q0 \ A, find the unique i ∈ E and internal index k with (D.P i)[k] = r!
  have hint_unique : ∀ r ∈ Q0 \ A, ∃ i ∈ E, ∃ k : ℕ,
      0 < k ∧ ∃ hk1 : k + 1 < (D.P i).length, (D.P i)[k]'(by omega) = r := by
    intro r hr
    have hrQ := (Finset.mem_sdiff.mp hr).1
    have hrnA := (Finset.mem_sdiff.mp hr).2
    have hrmem : r ∈ E.biUnion (fun i => (D.P i).toFinset) := by
      rcases Finset.mem_union.mp hrQ with hA | hB
      · exact (hrnA hA).elim
      · exact hB
    obtain ⟨i, hi, hri⟩ := Finset.mem_biUnion.mp hrmem
    have hlist : r ∈ D.P i := List.mem_toFinset.mp hri
    obtain ⟨k, hk, hget⟩ := List.mem_iff_getElem.mp hlist
    have hk0 : 0 < k := by
      by_contra h0; have : k = 0 := by omega
      subst this; exact hrnA (hget ▸ D.hstart i hi)
    have hk1 : k + 1 < (D.P i).length := by
      by_contra h1; have : k = (D.P i).length - 1 := by omega
      subst this; exact hrnA (hget ▸ D.hend i hi)
    exact ⟨i, hi, k, hk0, hk1, hget⟩
  -- Helper: count segments in Si_set i incident to φ r
  have hSi_inc_card : ∀ (i : ℕ) (hi : i ∈ E) (r : ℝ × ℝ),
      ((Si_set i).filter (fun s => s.1 = φ r ∨ s.2 = φ r)).card =
      ((Finset.univ : Finset (Fin ((D.P i).length - 1))).filter
        (fun k => (D.P i)[k.val]'(by omega) = r ∨ (D.P i)[k.val + 1]'(by omega) = r)).card := by
    intro i hi r
    dsimp only [Si_set]; rw [dif_pos hi]
    refine Finset.card_bij (fun s hs => ?_) ?_ ?_ ?_
    · -- inverse map: choose k with segAt i hi k = s
      exact (Finset.mem_image.mp (Finset.mem_filter.mp hs).1).choose
    · intro s hs
      have hs' := Finset.mem_filter.mp hs
      have hch := (Finset.mem_image.mp hs'.1).choose_spec
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      have hinc := hs'.2
      rw [← hch.2] at hinc
      exact (horient_ends _ _ r).mp hinc
    · intro s₁ hs₁ s₂ hs₂ heq
      have h1 := (Finset.mem_image.mp (Finset.mem_filter.mp hs₁).1).choose_spec.2
      have h2 := (Finset.mem_image.mp (Finset.mem_filter.mp hs₂).1).choose_spec.2
      rw [← h1, ← h2, heq]
    · intro k hk
      have hinc := (Finset.mem_filter.mp hk).2
      refine ⟨segAt i hi k, Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩,
        (horient_ends _ _ r).mpr hinc⟩, ?_⟩
      have hmem : segAt i hi k ∈ Finset.univ.image (segAt i hi) :=
        Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩
      have hch := (Finset.mem_image.mp hmem).choose_spec.2
      exact Fin.ext (hseg_disj_all i hi _ i hi k hch).2
  -- Endpoints of D'
  let uEnd' : ℕ → ℝ × ℝ := fun i => if hi : i ∈ E then φ ((D.P i)[0]'(by have := D.hlen i hi; omega)) else (0, 0)
  let vEnd' : ℕ → ℝ × ℝ := fun i => if hi : i ∈ E then φ ((D.P i)[(D.P i).length - 1]'(by have := D.hlen i hi; omega)) else (0, 0)
  -- Build XDistinctPLSubdiv A' E
  let D' : XDistinctPLSubdiv A' E :=
    { Q := Q'
      hAQ := hAQ'
      hx_inj := by
        intro p hp q hq hx
        obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hp
        obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hq
        exact congrArg φ (hc_inj a ha b hb hx)
      S := S
      hS_mem := by
        intro s hs
        obtain ⟨i, hi, _, k, rfl⟩ := (hS_mem_iff s).mp hs
        have h1Q : (D.P i)[k.val]'(by omega) ∈ Q0 :=
          Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨i, hi, List.mem_toFinset.mpr (List.getElem_mem _)⟩)
        have h2Q : (D.P i)[k.val + 1]'(by omega) ∈ Q0 :=
          Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨i, hi, List.mem_toFinset.mpr (List.getElem_mem _)⟩)
        have hne : (D.P i)[k.val]'(by omega) ≠ (D.P i)[k.val + 1]'(by omega) := fun h => by
          have := (D.hnodup i hi).getElem_inj_iff.mp h; omega
        refine ⟨?_, ?_, horient_lt _ _ h1Q h2Q hne⟩
        · dsimp only [segAt, orient]; split_ifs <;> exact Finset.mem_image_of_mem φ ‹_›
        · dsimp only [segAt, orient]; split_ifs <;> exact Finset.mem_image_of_mem φ ‹_›
      hS_noncross := by
        intro s₁ hs₁ s₂ hs₂ hne
        obtain ⟨i, hi, _, k₁, rfl⟩ := (hS_mem_iff s₁).mp hs₁
        obtain ⟨j, hj, _, k₂, rfl⟩ := (hS_mem_iff s₂).mp hs₂
        have hdiff : i ≠ j ∨ k₁.val ≠ k₂.val := by
          by_contra h; push Not at h
          rcases h with ⟨rfl, hk⟩
          exact hne (congrArg (segAt i hi) (Fin.ext hk))
        rw [horient_poseg, horient_pseg]
        ext z
        simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false]
        rintro ⟨hz1, hz2⟩
        let r : ℝ × ℝ := (z.1 - c * z.2, z.2)
        have hzr : φ r = z := by apply Prod.ext <;> (dsimp only [φ, r]; try ring)
        rw [← hzr, hφ_poseg] at hz1
        rw [← hzr, hφ_pseg] at hz2
        have hemp := D.hseg_noncross i hi j hj k₁.val (by omega) k₂.val (by omega) hdiff
        exact (hemp ▸ ⟨hz1, hz2⟩ : r ∈ (∅ : Set (ℝ × ℝ)))
      hS_avoidQ := by
        intro s hs z hz hmem
        obtain ⟨i, hi, _, k, rfl⟩ := (hS_mem_iff s).mp hs
        obtain ⟨r, hrQ, rfl⟩ := Finset.mem_image.mp hz
        rw [horient_poseg, hφ_poseg] at hmem
        have hr_disj : r ∈ A ∨ ∃ j ∈ E, r ∈ D.P j := by
          rcases Finset.mem_union.mp hrQ with hA | hB
          · exact Or.inl hA
          · obtain ⟨j, hj, hrj⟩ := Finset.mem_biUnion.mp hB
            exact Or.inr ⟨j, hj, List.mem_toFinset.mp hrj⟩
        exact D.hseg_avoid i hi k.val (by omega) r hr_disj hmem
      uEnd := uEnd'
      vEnd := vEnd'
      hEnd_mem := by
        intro i hi
        dsimp only [uEnd', vEnd']; rw [dif_pos hi, dif_pos hi]
        refine ⟨Finset.mem_image_of_mem φ (D.hstart i hi), Finset.mem_image_of_mem φ (D.hend i hi), ?_⟩
        intro heq
        have hlen := D.hlen i hi
        have := (D.hnodup i hi).getElem_inj_iff.mp (hφ_inj heq)
        omega
      hEnd_simple := by
        intro i hi j hj heq
        have hi' : i ∈ E := hi
        have hj' : j ∈ E := hj
        dsimp only [uEnd', vEnd'] at heq
        rw [dif_pos hi', dif_pos hi', dif_pos hj', dif_pos hj'] at heq
        apply D.hsimple hi hj
        dsimp only
        rw [dif_pos hi', dif_pos hj']
        have himg : ({(D.P i)[0]'(by have := D.hlen i hi; omega),
            (D.P i)[(D.P i).length - 1]'(by have := D.hlen i hi; omega)} : Finset _).image φ =
            ({(D.P j)[0]'(by have := D.hlen j hj; omega),
            (D.P j)[(D.P j).length - 1]'(by have := D.hlen j hj; omega)} : Finset _).image φ := by
          simpa using heq
        ext x
        have hx := Finset.ext_iff.mp himg (φ x)
        simp only [Finset.mem_image, hφ_inj.eq_iff, exists_eq_right] at hx
        exact hx
      edgeOf := edgeOf
      hedgeOf_mem := by
        intro s hs
        obtain ⟨i, hi, _, k, rfl⟩ := (hS_mem_iff s).mp hs
        rw [hedgeOf_eq i hi k]; exact hi
      hpath := by
        intro i hi
        dsimp only
        rw [hS_filter_eq i hi]
        have hlen := D.hlen i hi
        -- Identify Qi with image of internal indices 1 .. len-2!
        let Qi := (Q' \ A').filter (fun z => ∃ s ∈ Si_set i, s.1 = z ∨ s.2 = z)
        have hQi_eq : Qi = (Finset.Ioo 0 ((D.P i).length - 1)).attach.image
            (fun k => φ ((D.P i)[k.1]'(by have := (Finset.mem_Ioo.mp k.2).2; omega))) := by
          ext z
          simp only [Qi, Finset.mem_filter, hQ'_sdiff, Finset.mem_image, Finset.mem_attach, true_and, Subtype.exists]
          constructor
          · rintro ⟨⟨r, hr, rfl⟩, s, hs, hinc⟩
            dsimp only [Si_set] at hs; rw [dif_pos hi] at hs
            obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hs
            have hor := (horient_ends _ _ r).mp hinc
            have hrnA := (Finset.mem_sdiff.mp hr).2
            rcases hor with h1 | h2
            · have hk0 : 0 < k.val := by
                by_contra h0; have : k.val = 0 := by omega
                exact hrnA (by rw [← h1]; convert D.hstart i hi)
              exact ⟨k.val, Finset.mem_Ioo.mpr ⟨hk0, k.isLt⟩, by rw [h1]⟩
            · have hk1 : k.val + 1 < (D.P i).length - 1 := by
                by_contra h1; have : k.val + 1 = (D.P i).length - 1 := by omega
                exact hrnA (by rw [← h2]; convert D.hend i hi)
              exact ⟨k.val + 1, Finset.mem_Ioo.mpr ⟨Nat.succ_pos _, hk1⟩, by rw [h2]⟩
          · rintro ⟨k, hk, rfl⟩
            have hk' := Finset.mem_Ioo.mp hk
            have hrnA : (D.P i)[k]'(by omega) ∉ A := D.hint_notA i hi k hk'.1 (by omega)
            have hrQ0 : (D.P i)[k]'(by omega) ∈ Q0 :=
              Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨i, hi, List.mem_toFinset.mpr (List.getElem_mem _)⟩)
            refine ⟨⟨(D.P i)[k]'(by omega), Finset.mem_sdiff.mpr ⟨hrQ0, hrnA⟩, rfl⟩,
              segAt i hi ⟨k, hk'.2⟩, ?_, (horient_ends _ _ _).mpr (Or.inl rfl)⟩
            dsimp only [Si_set]; rw [dif_pos hi]
            exact Finset.mem_image.mpr ⟨⟨k, hk'.2⟩, Finset.mem_univ _, rfl⟩
        have hQi_card : Qi.card = (D.P i).length - 2 := by
          rw [hQi_eq, Finset.card_image_of_injective]
          · rw [Finset.card_attach, Nat.card_Ioo]; omega
          · intro k₁ k₂ heq
            exact Subtype.ext ((D.hnodup i hi).getElem_inj_iff.mp (hφ_inj heq))
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · exact Finset.card_pos.mp (by rw [hSi_card i hi]; omega)
        · rw [hSi_card i hi, hQi_card]; omega
        · -- Incident count at a ∈ A'
          intro z hz
          obtain ⟨r, hrA, rfl⟩ := Finset.mem_image.mp hz
          rw [hSi_inc_card i hi r]
          dsimp only [uEnd', vEnd']; simp only [dif_pos hi, hφ_inj.eq_iff]
          by_cases hu : r = (D.P i)[0]'(by omega)
          · rw [if_pos (Or.inl hu)]
            have hset : (Finset.univ : Finset (Fin ((D.P i).length - 1))).filter
                (fun k => (D.P i)[k.val]'(by omega) = r ∨ (D.P i)[k.val + 1]'(by omega) = r) =
                {⟨0, by omega⟩} := by
              ext k; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, Fin.ext_iff]
              constructor
              · rintro (h1 | h2)
                · exact (D.hnodup i hi).getElem_inj_iff.mp (h1.trans hu)
                · have := (D.hnodup i hi).getElem_inj_iff.mp (h2.trans hu); omega
              · intro hk; left; simp [hk, hu]
            rw [hset, Finset.card_singleton]
          · by_cases hv : r = (D.P i)[(D.P i).length - 1]'(by omega)
            · rw [if_pos (Or.inr hv)]
              have hset : (Finset.univ : Finset (Fin ((D.P i).length - 1))).filter
                  (fun k => (D.P i)[k.val]'(by omega) = r ∨ (D.P i)[k.val + 1]'(by omega) = r) =
                  {⟨(D.P i).length - 2, by omega⟩} := by
                ext k; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, Fin.ext_iff]
                constructor
                · rintro (h1 | h2)
                  · have := (D.hnodup i hi).getElem_inj_iff.mp (h1.trans hv); omega
                  · have := (D.hnodup i hi).getElem_inj_iff.mp (h2.trans hv); omega
                · intro hk; right; simp [hk, show (D.P i).length - 2 + 1 = (D.P i).length - 1 by omega, hv]
              rw [hset, Finset.card_singleton]
            · rw [if_neg (by tauto)]
              rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
              intro k _ hinc
              rcases hinc with h1 | h2
              · by_cases hk0 : k.val = 0
                · exact hu (h1.symm.trans (by congr 1))
                · exact D.hint_notA i hi k.val (by omega) (by omega) (h1.symm ▸ hrA)
              · by_cases hk1 : k.val + 1 = (D.P i).length - 1
                · exact hv (h2.symm.trans (by congr 1))
                · exact D.hint_notA i hi (k.val + 1) (by omega) (by omega) (h2.symm ▸ hrA)
        · -- Internal vertices of Qi have degree 2 in Si_set i
          intro z hz
          change z ∈ Qi at hz
          rw [hQi_eq] at hz
          obtain ⟨⟨k, hk⟩, -, rfl⟩ := Finset.mem_image.mp hz
          have hk' := Finset.mem_Ioo.mp hk
          rw [hSi_inc_card i hi]
          have hset : (Finset.univ : Finset (Fin ((D.P i).length - 1))).filter
              (fun m => (D.P i)[m.val]'(by omega) = (D.P i)[k]'(by omega) ∨
                        (D.P i)[m.val + 1]'(by omega) = (D.P i)[k]'(by omega)) =
              {⟨k - 1, by omega⟩, ⟨k, by omega⟩} := by
            ext m
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
              Finset.mem_singleton, Fin.ext_iff]
            constructor
            · rintro (h1 | h2)
              · right; exact (D.hnodup i hi).getElem_inj_iff.mp h1
              · left; have := (D.hnodup i hi).getElem_inj_iff.mp h2; omega
            · rintro (hm | hm)
              · right; congr 1; omega
              · left; congr 1
          rw [hset, Finset.card_pair (by intro h; have := congrArg Fin.val h; dsimp only at this; omega)]
        · -- Connectedness along the path P i
          intro PropP hstep s₁ hs₁ s₂ hs₂
          dsimp only [Si_set] at hs₁ hs₂; rw [dif_pos hi] at hs₁ hs₂
          obtain ⟨k₁, -, rfl⟩ := Finset.mem_image.mp hs₁
          obtain ⟨k₂, -, rfl⟩ := Finset.mem_image.mp hs₂
          -- Show PropP (segAt i hi k) ↔ PropP (segAt i hi 0) by induction on k.val!
          have hall : ∀ (m : ℕ) (hm : m < (D.P i).length - 1),
              PropP (segAt i hi ⟨m, hm⟩) ↔ PropP (segAt i hi ⟨0, by omega⟩) := by
            intro m
            induction m with
            | zero => intro _; exact Iff.rfl
            | succ m ih =>
              intro hm
              have hmem_q : φ ((D.P i)[m + 1]'(by omega)) ∈ Qi := by
                rw [hQi_eq]
                exact Finset.mem_image.mpr ⟨⟨m + 1, Finset.mem_Ioo.mpr ⟨Nat.succ_pos _, hm⟩⟩,
                  Finset.mem_attach _ _, rfl⟩
              have hsm : segAt i hi ⟨m, by omega⟩ ∈ Si_set i := by
                dsimp only [Si_set]; rw [dif_pos hi]
                exact Finset.mem_image.mpr ⟨⟨m, by omega⟩, Finset.mem_univ _, rfl⟩
              have hsm1 : segAt i hi ⟨m + 1, hm⟩ ∈ Si_set i := by
                dsimp only [Si_set]; rw [dif_pos hi]
                exact Finset.mem_image.mpr ⟨⟨m + 1, hm⟩, Finset.mem_univ _, rfl⟩
              have hlink := hstep _ hmem_q _ hsm1 _ hsm
                ((horient_ends _ _ _).mpr (Or.inl rfl))
                ((horient_ends _ _ _).mpr (Or.inr rfl))
              exact hlink.trans (ih (by omega))
          exact (hall k₁.val k₁.isLt).trans (hall k₂.val k₂.isLt).symm
      hQ_internal := by
        intro z hz
        rw [hQ'_sdiff] at hz
        obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hz
        obtain ⟨i, hi, k, hk0, hk1, hget⟩ := hint_unique r hr
        have huniq : ∀ s ∈ S, (s.1 = φ r ∨ s.2 = φ r) → edgeOf s = i := by
          intro s hs hinc
          obtain ⟨j, hj, _, m, rfl⟩ := (hS_mem_iff s).mp hs
          rw [hedgeOf_eq j hj m]
          by_contra hji
          have hor := (horient_ends _ _ r).mp hinc
          have hrnA := (Finset.mem_sdiff.mp hr).2
          rcases hor with h1 | h2
          · have hm0 : 0 < m.val := by
              by_contra h0; have : m.val = 0 := by omega
              exact hrnA (by rw [← h1]; convert D.hstart j hj)
            exact D.hint_disj j hj i hi hji m.val ⟨hm0, by have := m.isLt; omega⟩ k ⟨hk0, hk1⟩ (h1.trans hget.symm)
          · have hm1 : m.val + 1 < (D.P j).length - 1 := by
              by_contra h1; have : m.val + 1 = (D.P j).length - 1 := by omega
              exact hrnA (by rw [← h2]; convert D.hend j hj)
            exact D.hint_disj j hj i hi hji (m.val + 1) ⟨Nat.succ_pos _, by omega⟩ k ⟨hk0, hk1⟩ (h2.trans hget.symm)
        refine ⟨?_, i, hi, huniq⟩
        have hfilt : S.filter (fun s => s.1 = φ r ∨ s.2 = φ r) =
            (Si_set i).filter (fun s => s.1 = φ r ∨ s.2 = φ r) := by
          ext s; simp only [Finset.mem_filter]
          constructor
          · rintro ⟨hs, hinc⟩
            have he := huniq s hs hinc
            rw [← hS_filter_eq i hi]
            exact ⟨Finset.mem_filter.mpr ⟨hs, he⟩, hinc⟩
          · rintro ⟨hs, hinc⟩
            rw [← hS_filter_eq i hi] at hs
            exact ⟨(Finset.mem_filter.mp hs).1, hinc⟩
        rw [hfilt, hSi_inc_card i hi r]
        have hset : (Finset.univ : Finset (Fin ((D.P i).length - 1))).filter
            (fun m => (D.P i)[m.val]'(by omega) = r ∨ (D.P i)[m.val + 1]'(by omega) = r) =
            {⟨k - 1, by omega⟩, ⟨k, by omega⟩} := by
          ext m
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
            Finset.mem_singleton, Fin.ext_iff]
          constructor
          · rintro (h1 | h2)
            · right; exact (D.hnodup i hi).getElem_inj_iff.mp (h1.trans hget.symm)
            · left; have := (D.hnodup i hi).getElem_inj_iff.mp (h2.trans hget.symm); omega
          · rintro (hm | hm)
            · right; rw [← hget]; congr 1; omega
            · left; rw [← hget]; congr 1
        rw [hset, Finset.card_pair (by intro h; have := congrArg Fin.val h; dsimp only at this; omega)] }
  have hbound := xDistinctPLSubdiv_edge_bound A' E D'
  rwa [Finset.card_image_of_injective A hφ_inj] at hbound

/- ### Part 3: Probabilistic Crossing Number Inequality (`Finset.powersetCard` averaging) -/

/-- A continuous curve drawing of a simple graph `(A, E)` in `ℝ²` with finite pairwise intersections
outside `A`. -/
private structure CurveDrawing (A : Finset (EuclideanSpace ℝ (Fin 2))) (E : Finset ℕ) where
  γ : ℕ → C(unitInterval, EuclideanSpace ℝ (Fin 2))
  hinj : ∀ i ∈ E, Function.Injective (γ i)
  h0 : ∀ i ∈ E, γ i 0 ∈ A
  h1 : ∀ i ∈ E, γ i 1 ∈ A
  hint : ∀ i ∈ E, ∀ t : unitInterval, 0 < t → t < 1 → γ i t ∉ A
  hsimple : Set.InjOn (fun i => ({γ i 0, γ i 1} : Finset (EuclideanSpace ℝ (Fin 2)))) (E : Set ℕ)
  hfin : ∀ i ∈ E, ∀ j ∈ E, i ≠ j →
    ((Set.range (γ i) ∩ Set.range (γ j)) \ (A : Set (EuclideanSpace ℝ (Fin 2)))).Finite

private noncomputable def totalCrossings {A : Finset (EuclideanSpace ℝ (Fin 2))} {E : Finset ℕ}
    (D : CurveDrawing A E) : ℕ :=
  ∑ i ∈ E, ∑ j ∈ E.erase i,
    ((Set.range (D.γ i) ∩ Set.range (D.γ j)) \ (A : Set (EuclideanSpace ℝ (Fin 2)))).ncard

private lemma curveDrawing_ends_ne {A : Finset (EuclideanSpace ℝ (Fin 2))} {E : Finset ℕ}
    (D : CurveDrawing A E) {i : ℕ} (hi : i ∈ E) : D.γ i 0 ≠ D.γ i 1 :=
  fun h => zero_ne_one (D.hinj i hi h)

/-- Restrict a `CurveDrawing` to a subset of edges `E' ⊆ E`. -/
private def CurveDrawing.restrictEdges {A : Finset (EuclideanSpace ℝ (Fin 2))} {E : Finset ℕ}
    (D : CurveDrawing A E) {E' : Finset ℕ} (hsub : E' ⊆ E) : CurveDrawing A E' :=
  { γ := D.γ
    hinj := fun i hi => D.hinj i (hsub hi)
    h0 := fun i hi => D.h0 i (hsub hi)
    h1 := fun i hi => D.h1 i (hsub hi)
    hint := fun i hi => D.hint i (hsub hi)
    hsimple := D.hsimple.mono hsub
    hfin := fun i hi j hj hne => D.hfin i (hsub hi) j (hsub hj) hne }

/-- Restrict a `CurveDrawing` to an induced vertex subset `S ⊆ A` (keeping edges with both
endpoints in `S`). -/
private def CurveDrawing.induce {A : Finset (EuclideanSpace ℝ (Fin 2))} {E : Finset ℕ}
    (D : CurveDrawing A E) (S : Finset (EuclideanSpace ℝ (Fin 2))) (hSA : S ⊆ A) :
    CurveDrawing S (E.filter (fun i => D.γ i 0 ∈ S ∧ D.γ i 1 ∈ S)) :=
  { γ := D.γ
    hinj := fun i hi => D.hinj i (Finset.mem_filter.mp hi).1
    h0 := fun i hi => (Finset.mem_filter.mp hi).2.1
    h1 := fun i hi => (Finset.mem_filter.mp hi).2.2
    hint := fun i hi t h0 h1 hm => D.hint i (Finset.mem_filter.mp hi).1 t h0 h1 (hSA hm)
    hsimple := D.hsimple.mono (Finset.filter_subset _ _)
    hfin := fun i hi j hj hne => by
      have hsub : (Set.range (D.γ i) ∩ Set.range (D.γ j)) \ (S : Set _) ⊆
          (Set.range (D.γ i) ∩ Set.range (D.γ j)) \ (A : Set _) ∪ (A : Set _) := by
        intro x hx; by_cases hxA : x ∈ (A : Set _)
        · exact Or.inr hxA
        · exact Or.inl ⟨hx.1, hxA⟩
      exact ((D.hfin i (Finset.mem_filter.mp hi).1 j (Finset.mem_filter.mp hj).1 hne).union
        A.finite_toSet).subset hsub }

/-- Deleting one edge from a crossing pair decreases `totalCrossings` by at least 2, giving the
linear crossing lower bound `E.card ≤ 3 * A.card + totalCrossings D / 2` from the planar bound. -/
private lemma linear_crossing_bound
    (hplanar : ∀ (A : Finset (EuclideanSpace ℝ (Fin 2))) (E : Finset ℕ) (D : CurveDrawing A E),
      totalCrossings D = 0 → E.card ≤ 3 * A.card)
    (A : Finset (EuclideanSpace ℝ (Fin 2))) (E : Finset ℕ) (D : CurveDrawing A E) :
    2 * E.card ≤ 6 * A.card + totalCrossings D := by
  classical
  -- Induction on E.card
  suffices h : ∀ (m : ℕ) (E' : Finset ℕ) (D' : CurveDrawing A E'),
      E'.card = m → 2 * E'.card ≤ 6 * A.card + totalCrossings D' from
    h E.card E D rfl
  intro m
  induction m with
  | zero => intro E' _ hm; omega
  | succ m ih =>
    intro E' D' hm
    by_cases hX0 : totalCrossings D' = 0
    · have := hplanar A E' D' hX0; omega
    · -- Find i ∈ E', j ∈ E'.erase i with crossing count ≥ 1
      have hpos : 0 < ∑ i ∈ E', ∑ j ∈ E'.erase i,
          ((Set.range (D'.γ i) ∩ Set.range (D'.γ j)) \ (A : Set _)).ncard := Nat.pos_of_ne_zero hX0
      obtain ⟨i₀, hi₀, hi₀_pos⟩ := Finset.exists_ne_zero_of_sum_ne_zero hX0
      obtain ⟨j₀, hj₀, hj₀_ne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hi₀_pos
      have hj₀E : j₀ ∈ E' := (Finset.mem_erase.mp hj₀).2
      have hij : j₀ ≠ i₀ := (Finset.mem_erase.mp hj₀).1
      let D'' := D'.restrictEdges (Finset.erase_subset i₀ E')
      have hcard'' : (E'.erase i₀).card = m := by rw [Finset.card_erase_of_mem hi₀, hm]; omega
      have hih := ih (E'.erase i₀) D'' hcard''
      -- Compare totalCrossings D' vs totalCrossings D''
      let c (i j : ℕ) : ℕ :=
        ((Set.range (D'.γ i) ∩ Set.range (D'.γ j)) \ (A : Set _)).ncard
      have hc_symm : ∀ i j, c i j = c j i := fun i j => by
        dsimp only [c]; rw [Set.inter_comm]
      have hX_split : totalCrossings D'' + 2 ≤ totalCrossings D' := by
        have h1 : totalCrossings D' =
            (∑ j ∈ E'.erase i₀, c i₀ j) + ∑ i ∈ E'.erase i₀, ∑ j ∈ E'.erase i, c i j := by
          dsimp only [totalCrossings, c]
          exact (Finset.add_sum_erase E' (fun i => ∑ j ∈ E'.erase i, c i j) hi₀).symm
        have h2 : ∑ i ∈ E'.erase i₀, ∑ j ∈ E'.erase i, c i j =
            (∑ i ∈ E'.erase i₀, c i i₀) + totalCrossings D'' := by
          dsimp only [totalCrossings, D'', CurveDrawing.restrictEdges, c]
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro i hi
          have hi₀_in : i₀ ∈ E'.erase i := Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hi).1.symm, hi₀⟩
          rw [← Finset.add_sum_erase (E'.erase i) (fun j => c i j) hi₀_in]
          congr 2; ext j; simp only [Finset.mem_erase]; tauto
        have hj₀_pos : 1 ≤ c i₀ j₀ := Nat.pos_of_ne_zero hj₀_ne
        have hc1 : 1 ≤ ∑ j ∈ E'.erase i₀, c i₀ j :=
          hj₀_pos.trans (Finset.single_le_sum (f := fun j => c i₀ j) (fun _ _ => Nat.zero_le _) hj₀)
        have hc2 : 1 ≤ ∑ i ∈ E'.erase i₀, c i i₀ := by
          have hle := Finset.single_le_sum (f := fun i => c i i₀) (fun _ _ => Nat.zero_le _) hj₀
          rw [hc_symm] at hle
          exact hj₀_pos.trans hle
        omega
      rw [hcard''] at hih
      omega

/-- Exact count of `m`-subsets of `A` containing a fixed `k`-subset `T ⊆ A`. -/
private lemma card_powersetCard_superset {α : Type*} [DecidableEq α]
    (A T : Finset α) (hTA : T ⊆ A) {m : ℕ} (hTm : T.card ≤ m) :
    ((A.powersetCard m).filter (fun S => T ⊆ S)).card = (A.card - T.card).choose (m - T.card) := by
  have hbij : ((A.powersetCard m).filter (fun S => T ⊆ S)).card =
      ((A \ T).powersetCard (m - T.card)).card := by
    refine Finset.card_bij (fun S _ => S \ T) ?_ ?_ ?_
    · intro S hS
      have hS' := Finset.mem_filter.mp hS
      have hSp := Finset.mem_powersetCard.mp hS'.1
      refine Finset.mem_powersetCard.mpr ⟨Finset.sdiff_subset_sdiff hSp.1 (le_refl T), ?_⟩
      have := Finset.card_sdiff_add_card_eq_card hS'.2
      omega
    · intro S₁ hS₁ S₂ hS₂ heq
      have h1 := (Finset.mem_filter.mp hS₁).2
      have h2 := (Finset.mem_filter.mp hS₂).2
      rw [← Finset.sdiff_union_of_subset h1, ← Finset.sdiff_union_of_subset h2, heq]
    · intro U hU
      have hUp := Finset.mem_powersetCard.mp hU
      have hdisj : Disjoint U T := Finset.disjoint_sdiff.symm.mono_left hUp.1
      refine ⟨U ∪ T, Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr
        ⟨Finset.union_subset (hUp.1.trans Finset.sdiff_subset) hTA, ?_⟩,
        Finset.subset_union_right⟩, ?_⟩
      · rw [Finset.card_union_of_disjoint hdisj, hUp.2]; omega
      · rw [Finset.union_sdiff_cancel_right hdisj]
  rw [hbij, Finset.card_powersetCard, Finset.card_sdiff_of_subset hTA]

/-- Probabilistic Crossing Number Inequality: given the planar bound `E.card ≤ 3 * A.card`
and adjacent-crossing elimination, we obtain `E.card ≤ 24 * A.card ∨ E.card ^ 3 ≤ 1024 * A.card ^ 2 * X`. -/
private lemma crossing_lemma_of_planar_and_no_adj
    (hplanar : ∀ (A : Finset (EuclideanSpace ℝ (Fin 2))) (E : Finset ℕ) (D : CurveDrawing A E),
      totalCrossings D = 0 → E.card ≤ 3 * A.card)
    (hno_adj : ∀ (A : Finset (EuclideanSpace ℝ (Fin 2))) (E : Finset ℕ) (D : CurveDrawing A E),
      ∃ D' : CurveDrawing A E,
        totalCrossings D' ≤ totalCrossings D ∧
        ∀ i ∈ E, ∀ j ∈ E, i ≠ j →
          (D'.γ i 0 = D'.γ j 0 ∨ D'.γ i 0 = D'.γ j 1 ∨ D'.γ i 1 = D'.γ j 0 ∨ D'.γ i 1 = D'.γ j 1) →
          (Set.range (D'.γ i) ∩ Set.range (D'.γ j)) \ (A : Set _) = ∅)
    (A : Finset (EuclideanSpace ℝ (Fin 2))) (E : Finset ℕ) (D : CurveDrawing A E) :
    E.card ≤ 24 * A.card ∨ E.card ^ 3 ≤ 1024 * A.card ^ 2 * totalCrossings D := by
  classical
  by_cases hlin : E.card ≤ 24 * A.card
  · exact Or.inl hlin
  right
  obtain ⟨D', hXle, hNoAdj⟩ := hno_adj A E D
  set n := A.card
  set e := E.card
  set X' := totalCrossings D'
  -- Since simple graph has e ≤ n*(n-1)/2 and 24*n < e, we get 49 ≤ n!
  have he_le_pairs : 2 * e ≤ n * (n - 1) := by
    have hmap : E.card ≤ (A.powersetCard 2).card := by
      have hinj := D'.hsimple
      rw [← Finset.card_image_of_injOn hinj]
      apply Finset.card_le_card
      intro P hP
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hP
      refine Finset.mem_powersetCard.mpr ⟨?_, Finset.card_pair (curveDrawing_ends_ne D' hi)⟩
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact D'.h0 i hi
      · exact D'.h1 i hi
    rw [Finset.card_powersetCard, Nat.choose_two_right] at hmap
    change e ≤ n * (n - 1) / 2 at hmap
    have hdiv : 2 * (n * (n - 1) / 2) = n * (n - 1) :=
      Nat.mul_div_cancel' (Nat.even_mul_pred_self n).two_dvd
    omega
  have hn_ge49 : 49 ≤ n := by
    by_contra h
    have hmul : n * (n - 1) ≤ n * 48 := Nat.mul_le_mul_left n (by omega)
    omega
  -- Choose m = (6 * n * n) / e + 2; check 4 ≤ m ≤ n
  set m : ℕ := (6 * n * n) / e + 2
  have hm_ge4 : 4 ≤ m := by
    have h1 : 2 * e ≤ n * n := he_le_pairs.trans (Nat.mul_le_mul_left n (Nat.sub_le n 1))
    have h2 : 2 ≤ (6 * n * n) / e := by
      rw [Nat.le_div_iff_mul_le (by omega)]
      nlinarith
    omega
  have hm_le_n : m ≤ n := by
    have hdiv : (6 * n * n) / e ≤ n / 4 := by
      have h1 : (6 * n * n) / e * e ≤ 6 * n * n := Nat.div_mul_le_self _ _
      have h2 : 24 * n < e := by omega
      have h3 : (6 * n * n) / e * (24 * n) ≤ 6 * n * n := (Nat.mul_le_mul_left _ h2.le).trans h1
      have h4 : (6 * n * n) / e * 4 ≤ n := by nlinarith
      omega
    omega
  -- Average the linear bound over all S ∈ A.powersetCard m!
  let c' (i j : ℕ) : ℕ :=
    ((Set.range (D'.γ i) ∩ Set.range (D'.γ j)) \ (A : Set _)).ncard
  have hind_cross_eq : ∀ (S : Finset (EuclideanSpace ℝ (Fin 2))) (hS : S ∈ A.powersetCard m),
      totalCrossings (D'.induce S (Finset.mem_powersetCard.mp hS).1) =
      ∑ i ∈ E.filter (fun i => D'.γ i 0 ∈ S ∧ D'.γ i 1 ∈ S),
        ∑ j ∈ (E.filter (fun i => D'.γ i 0 ∈ S ∧ D'.γ i 1 ∈ S)).erase i, c' i j := by
    intro S hS
    have hSA : S ⊆ A := (Finset.mem_powersetCard.mp hS).1
    dsimp only [totalCrossings, CurveDrawing.induce, c']
    apply Finset.sum_congr rfl; intro i hi
    apply Finset.sum_congr rfl; intro j hj
    have hiE := (Finset.mem_filter.mp hi).1
    have hjE := (Finset.mem_filter.mp (Finset.mem_erase.mp hj).2).1
    -- For i, j with endpoints in S, any point of range (γ i) ∩ range (γ j) in A MUST be an endpoint, hence in S!
    congr 1; ext x
    simp only [Set.mem_sdiff, Set.mem_inter_iff, Finset.mem_coe]
    constructor
    · rintro ⟨⟨⟨t₁, rfl⟩, ⟨t₂, h2⟩⟩, hxS⟩
      refine ⟨⟨⟨t₁, rfl⟩, ⟨t₂, h2⟩⟩, fun hxA => hxS ?_⟩
      by_cases h0 : t₁ = 0
      · subst h0; exact (Finset.mem_filter.mp hi).2.1
      · by_cases h1 : t₁ = 1
        · subst h1; exact (Finset.mem_filter.mp hi).2.2
        · exfalso
          exact D'.hint i hiE t₁ (lt_of_le_of_ne t₁.2.1 (Ne.symm h0))
            (lt_of_le_of_ne t₁.2.2 h1) hxA
    · rintro ⟨hmem, hxA⟩
      exact ⟨hmem, fun hxS => hxA (hSA hxS)⟩
  have hper_S : ∀ S ∈ A.powersetCard m,
      2 * (E.filter (fun i => D'.γ i 0 ∈ S ∧ D'.γ i 1 ∈ S)).card ≤
      6 * m + ∑ i ∈ E.filter (fun i => D'.γ i 0 ∈ S ∧ D'.γ i 1 ∈ S),
        ∑ j ∈ (E.filter (fun i => D'.γ i 0 ∈ S ∧ D'.γ i 1 ∈ S)).erase i, c' i j := by
    intro S hS
    have hSA := (Finset.mem_powersetCard.mp hS).1
    have hSc := (Finset.mem_powersetCard.mp hS).2
    have hlinS := linear_crossing_bound hplanar S _ (D'.induce S hSA)
    rw [hSc, hind_cross_eq S hS] at hlinS
    exact hlinS
  have havg := Finset.sum_le_sum hper_S
  -- LHS = 2 * e * (n - 2).choose (m - 2)
  have hlhs : ∑ S ∈ A.powersetCard m, 2 * (E.filter (fun i => D'.γ i 0 ∈ S ∧ D'.γ i 1 ∈ S)).card =
      2 * e * (n - 2).choose (m - 2) := by
    rw [← Finset.mul_sum]
    have hswap : ∑ S ∈ A.powersetCard m, (E.filter (fun i => D'.γ i 0 ∈ S ∧ D'.γ i 1 ∈ S)).card =
        ∑ i ∈ E, ((A.powersetCard m).filter (fun S => ({D'.γ i 0, D'.γ i 1} : Finset _) ⊆ S)).card := by
      calc ∑ S ∈ A.powersetCard m, (E.filter (fun i => D'.γ i 0 ∈ S ∧ D'.γ i 1 ∈ S)).card
          = ∑ S ∈ A.powersetCard m, ∑ i ∈ E, if D'.γ i 0 ∈ S ∧ D'.γ i 1 ∈ S then 1 else 0 := by
            apply Finset.sum_congr rfl; intro S _; rw [Finset.card_filter]
        _ = ∑ i ∈ E, ∑ S ∈ A.powersetCard m, if D'.γ i 0 ∈ S ∧ D'.γ i 1 ∈ S then 1 else 0 := Finset.sum_comm
        _ = _ := by
            apply Finset.sum_congr rfl; intro i _
            rw [← Finset.card_filter]
            congr 1; ext S
            simp only [Finset.mem_filter, Finset.insert_subset_iff, Finset.singleton_subset_iff]
    rw [hswap]
    have hconst : ∑ i ∈ E, ((A.powersetCard m).filter (fun S => ({D'.γ i 0, D'.γ i 1} : Finset _) ⊆ S)).card =
        ∑ _i ∈ E, (n - 2).choose (m - 2) := by
      apply Finset.sum_congr rfl; intro i hi
      have hsub : ({D'.γ i 0, D'.γ i 1} : Finset _) ⊆ A := by
        intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl; exact D'.h0 i hi; exact D'.h1 i hi
      have hcard2 : ({D'.γ i 0, D'.γ i 1} : Finset _).card = 2 := Finset.card_pair (curveDrawing_ends_ne D' hi)
      rw [card_powersetCard_superset A _ hsub (by omega), hcard2]
    rw [hconst, Finset.sum_const, smul_eq_mul]; ring
  -- RHS = 6 * m * n.choose m + X' * (n - 4).choose (m - 4)
  have hrhs : ∑ S ∈ A.powersetCard m,
      (6 * m + ∑ i ∈ E.filter (fun i => D'.γ i 0 ∈ S ∧ D'.γ i 1 ∈ S),
        ∑ j ∈ (E.filter (fun i => D'.γ i 0 ∈ S ∧ D'.γ i 1 ∈ S)).erase i, c' i j) =
      6 * m * n.choose m + X' * (n - 4).choose (m - 4) := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_powersetCard, smul_eq_mul, mul_comm (n.choose m)]
    congr 1
    have hswap : ∑ S ∈ A.powersetCard m,
        ∑ i ∈ E.filter (fun i => D'.γ i 0 ∈ S ∧ D'.γ i 1 ∈ S),
          ∑ j ∈ (E.filter (fun i => D'.γ i 0 ∈ S ∧ D'.γ i 1 ∈ S)).erase i, c' i j =
        ∑ i ∈ E, ∑ j ∈ E.erase i,
          ((A.powersetCard m).filter (fun S =>
            ({D'.γ i 0, D'.γ i 1, D'.γ j 0, D'.γ j 1} : Finset _) ⊆ S)).card * c' i j := by
      calc ∑ S ∈ A.powersetCard m,
            ∑ i ∈ E.filter (fun i => D'.γ i 0 ∈ S ∧ D'.γ i 1 ∈ S),
              ∑ j ∈ (E.filter (fun i => D'.γ i 0 ∈ S ∧ D'.γ i 1 ∈ S)).erase i, c' i j
          = ∑ S ∈ A.powersetCard m, ∑ i ∈ E, ∑ j ∈ E.erase i,
              if ({D'.γ i 0, D'.γ i 1, D'.γ j 0, D'.γ j 1} : Finset _) ⊆ S then c' i j else 0 := by
            apply Finset.sum_congr rfl; intro S _
            rw [Finset.sum_filter]
            apply Finset.sum_congr rfl; intro i _
            by_cases hiS : D'.γ i 0 ∈ S ∧ D'.γ i 1 ∈ S
            · rw [if_pos hiS]
              have hfeq : (E.filter (fun i => D'.γ i 0 ∈ S ∧ D'.γ i 1 ∈ S)).erase i =
                  (E.erase i).filter (fun j => D'.γ j 0 ∈ S ∧ D'.γ j 1 ∈ S) := by
                ext j; simp only [Finset.mem_erase, Finset.mem_filter]; tauto
              rw [hfeq, Finset.sum_filter]
              apply Finset.sum_congr rfl; intro j _
              simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff, hiS.1, hiS.2, true_and]
            · rw [if_neg hiS]
              symm; apply Finset.sum_eq_zero; intro j _
              rw [if_neg]; simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]; tauto
        _ = ∑ i ∈ E, ∑ S ∈ A.powersetCard m, ∑ j ∈ E.erase i,
              if ({D'.γ i 0, D'.γ i 1, D'.γ j 0, D'.γ j 1} : Finset _) ⊆ S then c' i j else 0 := Finset.sum_comm
        _ = ∑ i ∈ E, ∑ j ∈ E.erase i, ∑ S ∈ A.powersetCard m,
              if ({D'.γ i 0, D'.γ i 1, D'.γ j 0, D'.γ j 1} : Finset _) ⊆ S then c' i j else 0 := by
            apply Finset.sum_congr rfl; intro i _; exact Finset.sum_comm
        _ = _ := by
            apply Finset.sum_congr rfl; intro i _
            apply Finset.sum_congr rfl; intro j _
            rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul]
    rw [hswap]
    have hterm : ∑ i ∈ E, ∑ j ∈ E.erase i,
        ((A.powersetCard m).filter (fun S =>
          ({D'.γ i 0, D'.γ i 1, D'.γ j 0, D'.γ j 1} : Finset _) ⊆ S)).card * c' i j =
        ∑ i ∈ E, ∑ j ∈ E.erase i, (n - 4).choose (m - 4) * c' i j := by
      apply Finset.sum_congr rfl; intro i hi
      apply Finset.sum_congr rfl; intro j hj
      by_cases hc0 : c' i j = 0
      · simp [hc0]
      · have hjE := (Finset.mem_erase.mp hj).2
        have hij := (Finset.mem_erase.mp hj).1
        -- Since c' i j ≠ 0 and D' has no adjacent crossings, all 4 endpoints are pairwise distinct!
        have hdisj : ¬ (D'.γ i 0 = D'.γ j 0 ∨ D'.γ i 0 = D'.γ j 1 ∨ D'.γ i 1 = D'.γ j 0 ∨ D'.γ i 1 = D'.γ j 1) := by
          intro hadj
          have hemp := hNoAdj i hi j hjE hij.symm hadj
          apply hc0
          dsimp only [c']
          rw [hemp, Set.ncard_empty]
        push Not at hdisj
        have hne_i := curveDrawing_ends_ne D' hi
        have hne_j := curveDrawing_ends_ne D' hjE
        have hcard4 : ({D'.γ i 0, D'.γ i 1, D'.γ j 0, D'.γ j 1} : Finset _).card = 4 := by
          rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
              Finset.card_insert_of_notMem, Finset.card_singleton]
          · simp [hne_j]
          · simp [hdisj.2.2.1, hdisj.2.2.2]
          · simp [hne_i, hdisj.1, hdisj.2.1]
        have hsub4 : ({D'.γ i 0, D'.γ i 1, D'.γ j 0, D'.γ j 1} : Finset _) ⊆ A := by
          intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl | rfl | rfl
          · exact D'.h0 i hi
          · exact D'.h1 i hi
          · exact D'.h0 j hjE
          · exact D'.h1 j hjE
        rw [card_powersetCard_superset A _ hsub4 (by omega), hcard4]
    rw [hterm]
    simp_rw [← Finset.mul_sum]
    rw [mul_comm]; rfl
  rw [hlhs, hrhs] at havg
  -- Eliminate binomial coefficients cleanly!
  -- Multiply havg by m * (m - 1) * (n - 2) * (n - 3)
  have hC1 : n.choose m * m * (m - 1) = n * (n - 1) * (n - 2).choose (m - 2) := by
    have ha : n.choose m * m = n * (n - 1).choose (m - 1) := by
      have := Nat.add_one_mul_choose_eq (n - 1) (m - 1)
      rw [show n - 1 + 1 = n by omega, show m - 1 + 1 = m by omega] at this; linarith
    have hb : (n - 1).choose (m - 1) * (m - 1) = (n - 1) * (n - 2).choose (m - 2) := by
      have := Nat.add_one_mul_choose_eq (n - 2) (m - 2)
      rw [show n - 2 + 1 = n - 1 by omega, show m - 2 + 1 = m - 1 by omega] at this; linarith
    calc n.choose m * m * (m - 1) = n * ((n - 1).choose (m - 1) * (m - 1)) := by rw [ha]; ring
      _ = n * ((n - 1) * (n - 2).choose (m - 2)) := by rw [hb]
      _ = _ := by ring
  have hC2 : (n - 2).choose (m - 2) * (m - 2) * (m - 3) = (n - 2) * (n - 3) * (n - 4).choose (m - 4) := by
    have ha : (n - 2).choose (m - 2) * (m - 2) = (n - 2) * (n - 3).choose (m - 3) := by
      have := Nat.add_one_mul_choose_eq (n - 3) (m - 3)
      rw [show n - 3 + 1 = n - 2 by omega, show m - 3 + 1 = m - 2 by omega] at this; linarith
    have hb : (n - 3).choose (m - 3) * (m - 3) = (n - 3) * (n - 4).choose (m - 4) := by
      have := Nat.add_one_mul_choose_eq (n - 4) (m - 4)
      rw [show n - 4 + 1 = n - 3 by omega, show m - 4 + 1 = m - 3 by omega] at this; linarith
    calc (n - 2).choose (m - 2) * (m - 2) * (m - 3)
        = (n - 2) * ((n - 3).choose (m - 3) * (m - 3)) := by rw [ha]; ring
      _ = (n - 2) * ((n - 3) * (n - 4).choose (m - 4)) := by rw [hb]
      _ = _ := by ring
  have hposC : 0 < (n - 2).choose (m - 2) := Nat.choose_pos (by omega)
  have hmul := Nat.mul_le_mul_left ((m - 1) * (n - 2) * (n - 3)) havg
  have hkey : (n - 2).choose (m - 2) * (2 * e * (m - 1) * (n - 2) * (n - 3)) ≤
      (n - 2).choose (m - 2) * (6 * n * (n - 1) * (n - 2) * (n - 3) +
        X' * (m - 1) * (m - 2) * (m - 3)) := by
    calc (n - 2).choose (m - 2) * (2 * e * (m - 1) * (n - 2) * (n - 3))
        = (m - 1) * (n - 2) * (n - 3) * (2 * e * (n - 2).choose (m - 2)) := by ring
      _ ≤ (m - 1) * (n - 2) * (n - 3) * (6 * m * n.choose m + X' * (n - 4).choose (m - 4)) := hmul
      _ = 6 * (n.choose m * m * (m - 1)) * (n - 2) * (n - 3) +
          X' * (m - 1) * ((n - 2) * (n - 3) * (n - 4).choose (m - 4)) := by ring
      _ = 6 * (n * (n - 1) * (n - 2).choose (m - 2)) * (n - 2) * (n - 3) +
          X' * (m - 1) * ((n - 2).choose (m - 2) * (m - 2) * (m - 3)) := by rw [hC1, ← hC2]
      _ = _ := by ring
  have hlin2 : 2 * e * (m - 1) * (n - 2) * (n - 3) ≤
      6 * n * (n - 1) * (n - 2) * (n - 3) + X' * (m - 1) * (m - 2) * (m - 3) :=
    Nat.le_of_mul_le_mul_left hkey hposC
  -- Since m - 1 = 6*n*n/e + 1 > 6*n*n/e, we have e * (m - 1) ≥ 6 * n * n!
  have hem1 : 6 * n * n ≤ e * (m - 1) := by
    have hdiv := Nat.div_add_mod (6 * n * n) e
    have hmod : (6 * n * n) % e < e := Nat.mod_lt _ (by omega)
    have hm1 : m - 1 = (6 * n * n) / e + 1 := by omega
    rw [hm1]; nlinarith
  have hm_ub : m * e ≤ 8 * n * n := by
    have h1 : (6 * n * n) / e * e ≤ 6 * n * n := Nat.div_mul_le_self _ _
    have h2 : 2 * e ≤ n * n := he_le_pairs.trans (Nat.mul_le_mul_left n (Nat.sub_le n 1))
    have hm_eq : m = (6 * n * n) / e + 2 := rfl
    rw [hm_eq, Nat.add_mul]
    nlinarith only [h1, h2]
  -- From hlin2: e * (m - 1) * (n - 2) * (n - 3) ≤ X' * (m - 1) * (m - 2) * (m - 3)
  have hstep1 : e * (m - 1) * (n - 2) * (n - 3) ≤ X' * (m - 1) * (m - 2) * (m - 3) := by
    have h6 : 6 * n * (n - 1) * (n - 2) * (n - 3) ≤ e * (m - 1) * (n - 2) * (n - 3) := by
      have : 6 * n * (n - 1) ≤ e * (m - 1) :=
        (Nat.mul_le_mul_left (6 * n) (Nat.sub_le n 1)).trans hem1
      exact Nat.mul_le_mul_right (n - 3) (Nat.mul_le_mul_right (n - 2) this)
    have h2e : 2 * e * (m - 1) * (n - 2) * (n - 3) =
        e * (m - 1) * (n - 2) * (n - 3) + e * (m - 1) * (n - 2) * (n - 3) := by ring
    omega
  have hstep2 : e * (n - 2) * (n - 3) ≤ X' * (m - 2) * (m - 3) := by
    have hpos_m1 : 0 < m - 1 := by omega
    have hrew : (m - 1) * (e * (n - 2) * (n - 3)) ≤ (m - 1) * (X' * (m - 2) * (m - 3)) := by
      nlinarith only [hstep1]
    exact Nat.le_of_mul_le_mul_left hrew hpos_m1
  have hstep3 : e * (n - 2) * (n - 3) ≤ X' * m * m := by
    have : (m - 2) * (m - 3) ≤ m * m := Nat.mul_le_mul (Nat.sub_le _ _) (Nat.sub_le _ _)
    nlinarith only [hstep2, this]
  -- Multiply by e^2: e^3 * (n-2)*(n-3) ≤ X' * (m*e)^2 ≤ X' * 64 * n^4
  have hstep4 : e ^ 3 * ((n - 2) * (n - 3)) ≤ X' * (64 * n ^ 4) := by
    have hm2 : (m * e) ^ 2 ≤ (8 * n * n) ^ 2 := Nat.pow_le_pow_left hm_ub 2
    calc e ^ 3 * ((n - 2) * (n - 3)) = e ^ 2 * (e * (n - 2) * (n - 3)) := by ring
      _ ≤ e ^ 2 * (X' * m * m) := Nat.mul_le_mul_left (e ^ 2) hstep3
      _ = X' * (m * e) ^ 2 := by ring
      _ ≤ X' * (8 * n * n) ^ 2 := Nat.mul_le_mul_left X' hm2
      _ = X' * (64 * n ^ 4) := by ring
  -- Since n ≥ 49, 2 * (n-2)*(n-3) ≥ n^2 (in fact 16 * (n-2)*(n-3) ≥ n^2 trivially!)
  have hn2 : n ^ 2 ≤ 2 * ((n - 2) * (n - 3)) := by
    zify [show 2 ≤ n by omega, show 3 ≤ n by omega]
    nlinarith only [hn_ge49]
  have hfinal : e ^ 3 * n ^ 2 ≤ (1024 * n ^ 2 * X') * n ^ 2 := by
    calc e ^ 3 * n ^ 2 ≤ e ^ 3 * (2 * ((n - 2) * (n - 3))) := Nat.mul_le_mul_left _ hn2
      _ = 2 * (e ^ 3 * ((n - 2) * (n - 3))) := by ring
      _ ≤ 2 * (X' * (64 * n ^ 4)) := Nat.mul_le_mul_left 2 hstep4
      _ = 128 * (n ^ 4 * X') := by ring
      _ ≤ 1024 * (n ^ 4 * X') := Nat.mul_le_mul_right _ (by omega)
      _ = (1024 * n ^ 2 * X') * n ^ 2 := by ring
  have hX'_final : e ^ 3 ≤ 1024 * n ^ 2 * X' :=
    Nat.le_of_mul_le_mul_right hfinal (by nlinarith only [hn_ge49])
  exact hX'_final.trans (Nat.mul_le_mul_left (1024 * n ^ 2) hXle)

/- ### Part 4: Planar Curve Drawing → Simple Polygonal Drawing (`planar_curveDrawing_bound`) -/

private def toProd (x : EuclideanSpace ℝ (Fin 2)) : ℝ × ℝ := (x 0, x 1)

private lemma toProd_inj : Function.Injective toProd := by
  intro x y h
  have h0 : x 0 = y 0 := congrArg Prod.fst h
  have h1 : x 1 = y 1 := congrArg Prod.snd h
  ext i
  fin_cases i
  · exact h0
  · exact h1

private def seg2 (a b : EuclideanSpace ℝ (Fin 2)) : Set (EuclideanSpace ℝ (Fin 2)) :=
  {x | ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ x = (1 - t) • a + t • b}

private def oseg2 (a b : EuclideanSpace ℝ (Fin 2)) : Set (EuclideanSpace ℝ (Fin 2)) :=
  {x | ∃ t : ℝ, 0 < t ∧ t < 1 ∧ x = (1 - t) • a + t • b}

private lemma mem_pseg_toProd {a b x : EuclideanSpace ℝ (Fin 2)} :
    toProd x ∈ pseg (toProd a) (toProd b) ↔ x ∈ seg2 a b := by
  constructor
  · rintro ⟨t, ht0, ht1, h⟩
    refine ⟨t, ht0, ht1, toProd_inj ?_⟩
    rw [h]; apply Prod.ext <;> simp [toProd]
  · rintro ⟨t, ht0, ht1, rfl⟩
    refine ⟨t, ht0, ht1, ?_⟩
    apply Prod.ext <;> simp [toProd]

private lemma mem_poseg_toProd {a b x : EuclideanSpace ℝ (Fin 2)} :
    toProd x ∈ poseg (toProd a) (toProd b) ↔ x ∈ oseg2 a b := by
  constructor
  · rintro ⟨t, ht0, ht1, h⟩
    refine ⟨t, ht0, ht1, toProd_inj ?_⟩
    rw [h]; apply Prod.ext <;> simp [toProd]
  · rintro ⟨t, ht0, ht1, rfl⟩
    refine ⟨t, ht0, ht1, ?_⟩
    apply Prod.ext <;> simp [toProd]

private lemma toProd_surj (p : ℝ × ℝ) : ∃ x : EuclideanSpace ℝ (Fin 2), toProd x = p := by
  refine ⟨!₂[p.1, p.2], ?_⟩
  apply Prod.ext <;> simp [toProd]

private lemma isCompact_seg2 (a b : EuclideanSpace ℝ (Fin 2)) : IsCompact (seg2 a b) := by
  have heq : seg2 a b = (fun t : ℝ => (1 - t) • a + t • b) '' Set.Icc (0 : ℝ) 1 := by
    ext x
    simp only [seg2, Set.mem_ofPred_eq, Set.mem_image, Set.mem_Icc]
    constructor
    · rintro ⟨t, h0, h1, rfl⟩; exact ⟨t, ⟨h0, h1⟩, rfl⟩
    · rintro ⟨t, ⟨h0, h1⟩, rfl⟩; exact ⟨t, h0, h1, rfl⟩
  rw [heq]
  exact isCompact_Icc.image (by fun_prop)

private lemma dist_seg2_le {a b p : EuclideanSpace ℝ (Fin 2)} {r : ℝ}
    (ha : dist a p ≤ r) (hb : dist b p ≤ r) {x : EuclideanSpace ℝ (Fin 2)} (hx : x ∈ seg2 a b) :
    dist x p ≤ r := by
  rcases hx with ⟨t, ht0, ht1, rfl⟩
  rw [dist_eq_norm] at ha hb ⊢
  have heq : (1 - t) • a + t • b - p = (1 - t) • (a - p) + t • (b - p) := by
    simp only [smul_sub, sub_smul, one_smul]; abel
  rw [heq]
  calc ‖(1 - t) • (a - p) + t • (b - p)‖
      ≤ ‖(1 - t) • (a - p)‖ + ‖t • (b - p)‖ := norm_add_le _ _
    _ = (1 - t) * ‖a - p‖ + t * ‖b - p‖ := by
        rw [norm_smul, norm_smul, Real.norm_of_nonneg (by linarith), Real.norm_of_nonneg ht0]
    _ ≤ (1 - t) * r + t * r := by nlinarith
    _ = r := by ring

private lemma radial_seg2_dist_eq {w a x : EuclideanSpace ℝ (Fin 2)} {δ : ℝ}
    (ha : dist a w = δ) (hx : x ∈ seg2 w a) :
    ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ x = (1 - t) • w + t • a ∧ dist x w = t * δ := by
  rcases hx with ⟨t, ht0, ht1, rfl⟩
  refine ⟨t, ht0, ht1, rfl, ?_⟩
  rw [dist_eq_norm] at ha ⊢
  have heq : (1 - t) • w + t • a - w = t • (a - w) := by
    simp only [smul_sub, sub_smul, one_smul]; abel
  rw [heq, norm_smul, Real.norm_of_nonneg ht0, ha]

private lemma radial_seg2_inter {w a b x : EuclideanSpace ℝ (Fin 2)} {δ : ℝ}
    (hδ : 0 < δ) (ha : dist a w = δ) (hb : dist b w = δ) (hab : a ≠ b)
    (hx1 : x ∈ seg2 w a) (hx2 : x ∈ seg2 w b) : x = w := by
  obtain ⟨t, ht0, ht1, hxt, hdt⟩ := radial_seg2_dist_eq ha hx1
  obtain ⟨s, hs0, hs1, hxs, hds⟩ := radial_seg2_dist_eq hb hx2
  have hts : t = s := by nlinarith
  subst hts
  by_cases ht : t = 0
  · subst ht; rw [hxt]; simp
  · exfalso
    have hdiff : t • (a - w) = t • (b - w) := by
      have h1 : (1 - t) • w + t • a - w = t • (a - w) := by
        simp only [smul_sub, sub_smul, one_smul]; abel
      have h2 : (1 - t) • w + t • b - w = t • (b - w) := by
        simp only [smul_sub, sub_smul, one_smul]; abel
      rw [← h1, ← h2, ← hxt, ← hxs]
    have hsub : a - w = b - w := smul_right_injective _ ht hdiff
    exact hab (sub_left_injective hsub)

private lemma radial_seg2_sphere_eq {w a x : EuclideanSpace ℝ (Fin 2)} {δ : ℝ}
    (hδ : 0 < δ) (ha : dist a w = δ) (hx : x ∈ seg2 w a) (hdx : dist x w = δ) : x = a := by
  obtain ⟨t, ht0, ht1, hxt, hdt⟩ := radial_seg2_dist_eq ha hx
  have ht1' : t = 1 := by nlinarith
  subst ht1'; rw [hxt]; simp

private lemma exists_pos_dist_of_disjoint_compact
    {K₁ K₂ : Set (EuclideanSpace ℝ (Fin 2))}
    (hK₁ : IsCompact K₁) (hK₂ : IsCompact K₂) (hdisj : Disjoint K₁ K₂) :
    ∃ d : ℝ, 0 < d ∧ ∀ x ∈ K₁, ∀ y ∈ K₂, d ≤ dist x y := by
  by_cases h1 : K₁.Nonempty
  · by_cases h2 : K₂.Nonempty
    · have hcont : Continuous (fun p : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) => dist p.1 p.2) :=
        continuous_fst.dist continuous_snd
      obtain ⟨⟨x₀, y₀⟩, hmem, hmin⟩ :=
        (hK₁.prod hK₂).exists_isMinOn (h1.prod h2) hcont.continuousOn
      have hne : x₀ ≠ y₀ := fun h => by
        subst h
        exact Set.disjoint_left.mp hdisj hmem.1 hmem.2
      refine ⟨dist x₀ y₀, dist_pos.mpr hne, fun x hx y hy => ?_⟩
      exact isMinOn_iff.mp hmin (x, y) ⟨hx, hy⟩
    · rw [Set.not_nonempty_iff_eq_empty] at h2
      subst h2; exact ⟨1, one_pos, fun _ _ _ hy => hy.elim⟩
  · rw [Set.not_nonempty_iff_eq_empty] at h1
    subst h1; exact ⟨1, one_pos, fun _ hx => hx.elim⟩

/- #### Loop erasure on polygonal chains in `ℝ × ℝ` -/

private def chainUnion (L : List (ℝ × ℝ)) : Set (ℝ × ℝ) :=
  {x | ∃ (k : ℕ) (hk : k + 1 < L.length), x ∈ pseg (L[k]'(by omega)) (L[k + 1]'hk)}

private def IsSimpleChain (L : List (ℝ × ℝ)) : Prop :=
  2 ≤ L.length ∧
  L.Nodup ∧
  (∀ (k₁ : ℕ) (h1 : k₁ + 1 < L.length) (k₂ : ℕ) (h2 : k₂ + 1 < L.length), k₁ ≠ k₂ →
    poseg (L[k₁]'(by omega)) (L[k₁ + 1]'h1) ∩ pseg (L[k₂]'(by omega)) (L[k₂ + 1]'h2) = ∅) ∧
  (∀ (k : ℕ) (hk : k + 1 < L.length) (r : ℝ × ℝ), r ∈ L →
    r ∉ poseg (L[k]'(by omega)) (L[k + 1]'hk))

private lemma pseg_sub_of_mem {a b c : ℝ × ℝ} (hc : c ∈ pseg a b) :
    pseg a c ⊆ pseg a b ∧ pseg c b ⊆ pseg a b := by
  rcases hc with ⟨t, ht0, ht1, rfl⟩
  constructor
  · rintro x ⟨s, hs0, hs1, rfl⟩
    refine ⟨s * t, by nlinarith, by nlinarith, ?_⟩
    apply Prod.ext <;> dsimp only <;> ring
  · rintro x ⟨s, hs0, hs1, rfl⟩
    refine ⟨(1 - s) * t + s, by nlinarith, by nlinarith, ?_⟩
    apply Prod.ext <;> dsimp only <;> ring

private lemma poseg_subset_pseg {a b : ℝ × ℝ} : poseg a b ⊆ pseg a b :=
  fun _ ⟨t, h0, h1, hx⟩ => ⟨t, h0.le, h1.le, hx⟩

private lemma poseg_adj_collinear {a b c p : ℝ × ℝ} (hac : a ≠ c)
    (hp1 : p ∈ poseg a b) (hp2 : p ∈ poseg b c) :
    a ∈ poseg b c ∨ c ∈ poseg a b := by
  rcases hp1 with ⟨t, ht0, ht1, hp1⟩
  rcases hp2 with ⟨s, hs0, hs1, hp2⟩
  have heq : ((1 - t) * a.1 + t * b.1, (1 - t) * a.2 + t * b.2) =
             ((1 - s) * b.1 + s * c.1, (1 - s) * b.2 + s * c.2) := hp1.symm.trans hp2
  have h1 := congrArg Prod.fst heq
  have h2 := congrArg Prod.snd heq
  dsimp only at h1 h2
  rcases lt_trichotomy (1 - t) s with hlt | heqts | hgt
  · right
    refine ⟨1 - (1 - t) / s, by rw [sub_pos, div_lt_one hs0]; exact hlt,
      by have : 0 < (1 - t) / s := div_pos (by linarith) hs0; linarith, ?_⟩
    apply Prod.ext <;> dsimp only
    · field_simp [hs0.ne']; linarith
    · field_simp [hs0.ne']; linarith
  · exfalso
    apply hac
    rw [← heqts] at h1 h2
    apply Prod.ext
    · have : (1 - t) * a.1 = (1 - t) * c.1 := by linarith
      exact mul_left_cancel₀ (by linarith) this
    · have : (1 - t) * a.2 = (1 - t) * c.2 := by linarith
      exact mul_left_cancel₀ (by linarith) this
  · left
    have hpos : 0 < 1 - t := by linarith
    refine ⟨s / (1 - t), div_pos hs0 hpos, (div_lt_one hpos).mpr hgt, ?_⟩
    apply Prod.ext <;> dsimp only
    · field_simp [hpos.ne']; linarith
    · field_simp [hpos.ne']; linarith

private lemma exists_simple_chain :
    ∀ (n : ℕ) (L : List (ℝ × ℝ)), L.length = n → (hge2 : 2 ≤ L.length) →
      L[0]'(by omega) ≠ L[L.length - 1]'(by omega) →
      ∃ L' : List (ℝ × ℝ), IsSimpleChain L' ∧
        ∃ (h0 : 0 < L'.length) (h1 : L'.length - 1 < L'.length),
          L'[0]'h0 = L[0]'(by omega) ∧
          L'[L'.length - 1]'h1 = L[L.length - 1]'(by omega) ∧
          chainUnion L' ⊆ chainUnion L := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro L hLen hge2 hne
    -- Case 1: L has a duplicate vertex
    by_cases hnd : L.Nodup
    · -- Case 2: some vertex of L lies on an open segment of L
      by_cases hv : ∃ (k : ℕ) (hk : k + 1 < L.length) (b : ℕ) (hb : b < L.length),
          L[b]'hb ∈ poseg (L[k]'(by omega)) (L[k + 1]'hk)
      · obtain ⟨k, hk, b, hb, hmem⟩ := hv
        have hne_k : L[k]'(by omega) ≠ L[k + 1]'hk := fun h => by
          have := hnd.getElem_inj_iff.mp h; omega
        have hbk : b ≠ k := by
          rintro rfl
          rcases hmem with ⟨t, ht0, _, heq⟩
          apply hne_k; apply Prod.ext
          · have h1 := congrArg Prod.fst heq; dsimp only at h1; nlinarith
          · have h2 := congrArg Prod.snd heq; dsimp only at h2; nlinarith
        have hbk1 : b ≠ k + 1 := by
          rintro rfl
          rcases hmem with ⟨t, _, ht1, heq⟩
          apply hne_k; apply Prod.ext
          · have h1 := congrArg Prod.fst heq; dsimp only at h1; nlinarith
          · have h2 := congrArg Prod.snd heq; dsimp only at h2; nlinarith
        rcases lt_or_gt_of_ne hbk with hlt | hgt
        · -- b < k: shortcut L[b] directly to L[k + 1]
          let L₁ := L.take (b + 1) ++ L.drop (k + 1)
          have hlen1 : L₁.length = b + 1 + (L.length - (k + 1)) := by
            simp [L₁, Nat.min_eq_left (by omega : b + 1 ≤ L.length)]
          have hlt_len : L₁.length < n := by omega
          have hge2_1 : 2 ≤ L₁.length := by omega
          have hget1 : ∀ (m : ℕ) (hm : m < L₁.length),
              L₁[m]'hm = if h : m ≤ b then L[m]'(by omega) else L[m + (k - b)]'(by omega) := by
            intro m hm
            dsimp only [L₁]
            rw [List.getElem_append]
            have htl : (L.take (b + 1)).length = b + 1 := by simp [Nat.min_eq_left (by omega : b + 1 ≤ L.length)]
            split_ifs with h1 h2
            · simp
            · omega
            · omega
            · simp only [List.getElem_drop, htl]; congr 1; omega
          have h0_1 : L₁[0]'(by omega) = L[0]'(by omega) := by
            rw [hget1 0 (by omega)]; simp
          have hlast_1 : L₁[L₁.length - 1]'(by omega) = L[L.length - 1]'(by omega) := by
            rw [hget1 (L₁.length - 1) (by omega)]
            rw [dif_neg (by omega)]; congr 1; omega
          have hsub1 : chainUnion L₁ ⊆ chainUnion L := by
            rintro x ⟨m, hm, hx⟩
            rw [hget1 m (by omega), hget1 (m + 1) hm] at hx
            by_cases hmb : m < b
            · rw [dif_pos (by omega), dif_pos (by omega)] at hx
              exact ⟨m, by omega, hx⟩
            · by_cases hmeq : m = b
              · rw [dif_pos (by omega), dif_neg (by omega)] at hx
                have hidx : m + 1 + (k - b) = k + 1 := by omega
                have hx' : x ∈ pseg (L[b]'hb) (L[k + 1]'hk) := by
                  convert hx using 2; simp [hmeq]; congr 1; exact hidx.symm
                exact ⟨k, hk, (pseg_sub_of_mem (poseg_subset_pseg hmem)).2 hx'⟩
              · rw [dif_neg (by omega), dif_neg (by omega)] at hx
                refine ⟨m + (k - b), by omega, ?_⟩
                convert hx using 2; congr 1; omega
          obtain ⟨L', hS, h0', h1', he0, he1, hsub⟩ :=
            ih L₁.length hlt_len L₁ rfl hge2_1 (by rw [h0_1, hlast_1]; exact hne)
          exact ⟨L', hS, h0', h1', he0.trans h0_1, he1.trans hlast_1, hsub.trans hsub1⟩
        · -- k + 1 < b: shortcut L[k] directly to L[b]
          have hgt1 : k + 1 < b := by omega
          let L₁ := L.take (k + 1) ++ L.drop b
          have hlen1 : L₁.length = k + 1 + (L.length - b) := by
            simp [L₁, Nat.min_eq_left (by omega : k + 1 ≤ L.length)]
          have hlt_len : L₁.length < n := by omega
          have hge2_1 : 2 ≤ L₁.length := by omega
          have hget1 : ∀ (m : ℕ) (hm : m < L₁.length),
              L₁[m]'hm = if h : m ≤ k then L[m]'(by omega) else L[m + (b - k - 1)]'(by omega) := by
            intro m hm
            dsimp only [L₁]
            rw [List.getElem_append]
            have htl : (L.take (k + 1)).length = k + 1 := by simp [Nat.min_eq_left (by omega : k + 1 ≤ L.length)]
            split_ifs with h1 h2
            · simp
            · omega
            · omega
            · simp only [List.getElem_drop, htl]; congr 1; omega
          have h0_1 : L₁[0]'(by omega) = L[0]'(by omega) := by
            rw [hget1 0 (by omega)]; simp
          have hlast_1 : L₁[L₁.length - 1]'(by omega) = L[L.length - 1]'(by omega) := by
            rw [hget1 (L₁.length - 1) (by omega)]
            rw [dif_neg (by omega)]; congr 1; omega
          have hsub1 : chainUnion L₁ ⊆ chainUnion L := by
            rintro x ⟨m, hm, hx⟩
            rw [hget1 m (by omega), hget1 (m + 1) hm] at hx
            by_cases hmk : m < k
            · rw [dif_pos (by omega), dif_pos (by omega)] at hx
              exact ⟨m, by omega, hx⟩
            · by_cases hmeq : m = k
              · rw [dif_pos (by omega), dif_neg (by omega)] at hx
                have hx' : x ∈ pseg (L[k]'(by omega)) (L[b]'hb) := by
                  convert hx using 2; simp [hmeq]; congr 1; omega
                exact ⟨k, hk, (pseg_sub_of_mem (poseg_subset_pseg hmem)).1 hx'⟩
              · rw [dif_neg (by omega), dif_neg (by omega)] at hx
                refine ⟨m + (b - k - 1), by omega, ?_⟩
                convert hx using 2; congr 1; omega
          obtain ⟨L', hS, h0', h1', he0, he1, hsub⟩ :=
            ih L₁.length hlt_len L₁ rfl hge2_1 (by rw [h0_1, hlast_1]; exact hne)
          exact ⟨L', hS, h0', h1', he0.trans h0_1, he1.trans hlast_1, hsub.trans hsub1⟩
      · -- Case 3: some two distinct segments cross
        by_cases hcr : ∃ (k₁ : ℕ) (h1 : k₁ + 1 < L.length) (k₂ : ℕ) (h2 : k₂ + 1 < L.length),
            k₁ ≠ k₂ ∧ ∃ p, p ∈ poseg (L[k₁]'(by omega)) (L[k₁ + 1]'h1) ∩
              pseg (L[k₂]'(by omega)) (L[k₂ + 1]'h2)
        · obtain ⟨k₁, h1, k₂, h2, hne_k, p, hp1, hp2⟩ := hcr
          -- p cannot be L[k₂] or L[k₂ + 1] (else contradicts ¬ hv), so p ∈ poseg L[k₂] L[k₂ + 1]!
          have hp2_open : p ∈ poseg (L[k₂]'(by omega)) (L[k₂ + 1]'h2) := by
            rcases hp2 with ⟨t, ht0, ht1, rfl⟩
            have ht0' : 0 < t := lt_of_le_of_ne ht0 (fun h => by
              subst h; apply hv
              exact ⟨k₁, h1, k₂, by omega, by simpa using hp1⟩)
            have ht1' : t < 1 := lt_of_le_of_ne ht1 (fun h => by
              subst h; apply hv
              exact ⟨k₁, h1, k₂ + 1, h2, by simpa using hp1⟩)
            exact ⟨t, ht0', ht1', rfl⟩
          -- WLOG a < b with p ∈ poseg a ∩ poseg b
          obtain ⟨a, ha, b, hb, hab, hpa, hpb⟩ :
              ∃ (a : ℕ) (ha : a + 1 < L.length) (b : ℕ) (hb : b + 1 < L.length),
                a < b ∧ p ∈ poseg (L[a]'(by omega)) (L[a + 1]'ha) ∧
                p ∈ poseg (L[b]'(by omega)) (L[b + 1]'hb) := by
            rcases lt_or_gt_of_ne hne_k with hlt | hgt
            · exact ⟨k₁, h1, k₂, h2, hlt, hp1, hp2_open⟩
            · exact ⟨k₂, h2, k₁, h1, hgt, hp2_open, hp1⟩
          -- Cannot have b = a + 1 by poseg_adj_collinear + ¬ hv!
          have hab2 : a + 2 ≤ b := by
            by_contra h
            have hba : b = a + 1 := by omega
            subst hba
            have hne_ac : L[a]'(by omega) ≠ L[a + 2]'hb := fun heq => by
              have := hnd.getElem_inj_iff.mp heq; omega
            rcases poseg_adj_collinear hne_ac hpa hpb with hmemA | hmemC
            · exact hv ⟨a + 1, hb, a, by omega, hmemA⟩
            · exact hv ⟨a, ha, a + 2, hb, hmemC⟩
          -- Splice: L₁ = L.take (a + 1) ++ (p :: L.drop (b + 1))
          let L₁ := L.take (a + 1) ++ (p :: L.drop (b + 1))
          have hlen1 : L₁.length = a + 2 + (L.length - (b + 1)) := by
            simp [L₁, Nat.min_eq_left (by omega : a + 1 ≤ L.length)]; omega
          have hlt_len : L₁.length < n := by omega
          have hge2_1 : 2 ≤ L₁.length := by omega
          have hget1 : ∀ (m : ℕ) (hm : m < L₁.length),
              L₁[m]'hm =
                if h1 : m ≤ a then L[m]'(by omega)
                else if h2 : m = a + 1 then p
                else L[m + (b - a - 1)]'(by omega) := by
            intro m hm
            dsimp only [L₁]
            rw [List.getElem_append]
            have htl : (L.take (a + 1)).length = a + 1 := by simp [Nat.min_eq_left (by omega : a + 1 ≤ L.length)]
            split_ifs with hlt hle heq
            · simp
            · omega
            · omega
            · omega
            · rw [List.getElem_cons]
              simp [htl, show m - (a + 1) = 0 by omega]
            · rw [List.getElem_cons]
              have hpos : m - (L.take (a + 1)).length ≠ 0 := by omega
              simp only [hpos, dite_false, List.getElem_drop]
              congr 1; omega
          have h0_1 : L₁[0]'(by omega) = L[0]'(by omega) := by
            rw [hget1 0 (by omega)]; simp
          have hlast_1 : L₁[L₁.length - 1]'(by omega) = L[L.length - 1]'(by omega) := by
            rw [hget1 (L₁.length - 1) (by omega)]
            rw [dif_neg (by omega), dif_neg (by omega)]; congr 1; omega
          have hsub1 : chainUnion L₁ ⊆ chainUnion L := by
            rintro x ⟨m, hm, hx⟩
            rw [hget1 m (by omega), hget1 (m + 1) hm] at hx
            by_cases hm1 : m < a
            · rw [dif_pos (by omega), dif_pos (by omega)] at hx
              exact ⟨m, by omega, hx⟩
            · by_cases hm2 : m = a
              · rw [dif_pos (by omega), dif_neg (by omega), dif_pos (by omega)] at hx
                have hx' : x ∈ pseg (L[a]'(by omega)) p := by convert hx using 2; simp [hm2]
                exact ⟨a, ha, (pseg_sub_of_mem (poseg_subset_pseg hpa)).1 hx'⟩
              · by_cases hm3 : m = a + 1
                · rw [dif_neg (by omega), dif_pos (by omega), dif_neg (by omega), dif_neg (by omega)] at hx
                  have hx' : x ∈ pseg p (L[b + 1]'hb) := by
                    convert hx using 2; congr 1; omega
                  exact ⟨b, hb, (pseg_sub_of_mem (poseg_subset_pseg hpb)).2 hx'⟩
                · rw [dif_neg (by omega), dif_neg (by omega), dif_neg (by omega), dif_neg (by omega)] at hx
                  refine ⟨m + (b - a - 1), by omega, ?_⟩
                  convert hx using 2; congr 1; omega
          obtain ⟨L', hS, h0', h1', he0, he1, hsub⟩ :=
            ih L₁.length hlt_len L₁ rfl hge2_1 (by rw [h0_1, hlast_1]; exact hne)
          exact ⟨L', hS, h0', h1', he0.trans h0_1, he1.trans hlast_1, hsub.trans hsub1⟩
        · -- Case 4: L is already simple!
          refine ⟨L, ⟨hge2, hnd, ?_, ?_⟩, by omega, by omega, rfl, rfl, Set.Subset.rfl⟩
          · intro k₁ h1 k₂ h2 hne_k
            ext p; simp only [Set.mem_empty_iff_false, iff_false]
            intro hp; exact hcr ⟨k₁, h1, k₂, h2, hne_k, p, hp⟩
          · intro k hk r hr hmem
            obtain ⟨b, hb, rfl⟩ := List.mem_iff_getElem.mp hr
            exact hv ⟨k, hk, b, hb, hmem⟩
    · -- Case 1: ¬ L.Nodup → find a < b with L[a] = L[b]
      have hdup : ∃ (a b : ℕ) (hb : b < L.length) (hab : a < b), L[a]'(by omega) = L[b]'hb := by
        by_contra hno
        apply hnd
        rw [List.nodup_iff_injective_getElem]
        intro i j hij
        by_contra hne_ij
        rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne_ij) with hlt | hgt
        · exact hno ⟨i.val, j.val, j.isLt, hlt, hij⟩
        · exact hno ⟨j.val, i.val, i.isLt, hgt, hij.symm⟩
      obtain ⟨a, b, hb, hab, heq_ab⟩ := hdup
      have hnot_both : ¬ (a = 0 ∧ b = L.length - 1) := by
        rintro ⟨rfl, rfl⟩; exact hne heq_ab
      let L₁ := L.take (a + 1) ++ L.drop (b + 1)
      have hlen1 : L₁.length = a + 1 + (L.length - (b + 1)) := by
        simp [L₁, Nat.min_eq_left (by omega : a + 1 ≤ L.length)]
      have hlt_len : L₁.length < n := by omega
      have hge2_1 : 2 ≤ L₁.length := by omega
      have hget1 : ∀ (m : ℕ) (hm : m < L₁.length),
          L₁[m]'hm = if h : m ≤ a then L[m]'(by omega) else L[m + (b - a)]'(by omega) := by
        intro m hm
        dsimp only [L₁]
        rw [List.getElem_append]
        have htl : (L.take (a + 1)).length = a + 1 := by simp [Nat.min_eq_left (by omega : a + 1 ≤ L.length)]
        split_ifs with h1 h2
        · simp
        · omega
        · omega
        · simp only [List.getElem_drop, htl]; congr 1; omega
      have h0_1 : L₁[0]'(by omega) = L[0]'(by omega) := by
        rw [hget1 0 (by omega)]; simp
      have hlast_1 : L₁[L₁.length - 1]'(by omega) = L[L.length - 1]'(by omega) := by
        rw [hget1 (L₁.length - 1) (by omega)]
        by_cases hbl : b = L.length - 1
        · rw [dif_pos (by omega)]
          have hidx : L₁.length - 1 = a := by omega
          calc L[L₁.length - 1]'(by omega) = L[a]'(by omega) := by congr 1
            _ = L[b]'hb := heq_ab
            _ = L[L.length - 1]'(by omega) := by congr 1
        · rw [dif_neg (by omega)]; congr 1; omega
      have hsub1 : chainUnion L₁ ⊆ chainUnion L := by
        rintro x ⟨m, hm, hx⟩
        rw [hget1 m (by omega), hget1 (m + 1) hm] at hx
        by_cases hma : m < a
        · rw [dif_pos (by omega), dif_pos (by omega)] at hx
          exact ⟨m, by omega, hx⟩
        · by_cases hmeq : m = a
          · rw [dif_pos (by omega), dif_neg (by omega)] at hx
            refine ⟨b, by omega, ?_⟩
            convert hx using 2
            · calc L[b]'hb = L[a]'(by omega) := heq_ab.symm
                _ = L[m]'(by omega) := by congr 1; omega
            · congr 1; omega
          · rw [dif_neg (by omega), dif_neg (by omega)] at hx
            refine ⟨m + (b - a), by omega, ?_⟩
            convert hx using 2; congr 1; omega
      obtain ⟨L', hS, h0', h1', he0, he1, hsub⟩ :=
        ih L₁.length hlt_len L₁ rfl hge2_1 (by rw [h0_1, hlast_1]; exact hne)
      exact ⟨L', hS, h0', h1', he0.trans h0_1, he1.trans hlast_1, hsub.trans hsub1⟩

/-- Every crossing-free continuous curve drawing of a simple graph `(A, E)` in `ℝ²`
satisfies Euler's edge bound `E.card ≤ 3 * A.card`. -/
private lemma planar_curveDrawing_bound
    (A : Finset (EuclideanSpace ℝ (Fin 2))) (E : Finset ℕ) (D : CurveDrawing A E)
    (hX : totalCrossings D = 0) :
    E.card ≤ 3 * A.card := by
  classical
  -- Extract pairwise disjointness outside A
  have hdisj_int : ∀ i ∈ E, ∀ j ∈ E, i ≠ j →
      (Set.range (D.γ i) ∩ Set.range (D.γ j)) \ (A : Set _) = ∅ := by
    intro i hi j hj hne
    have hi0 : ∑ k ∈ E.erase i,
        ((Set.range (D.γ i) ∩ Set.range (D.γ k)) \ (A : Set _)).ncard = 0 :=
      (Finset.sum_eq_zero_iff.mp hX) i hi
    have hj0 : ((Set.range (D.γ i) ∩ Set.range (D.γ j)) \ (A : Set _)).ncard = 0 :=
      (Finset.sum_eq_zero_iff.mp hi0) j (Finset.mem_erase.mpr ⟨hne.symm, hj⟩)
    exact (Set.ncard_eq_zero (D.hfin i hi j hj hne)).mp hj0
  -- Step 1: Choose δ > 0 isolating all vertices in A and non-incident curves
  have hδ_A : ∃ d₁ : ℝ, 0 < d₁ ∧ ∀ u ∈ A, ∀ v ∈ A, u ≠ v → d₁ ≤ dist u v := by
    let P := (A ×ˢ A).filter (fun p => p.1 ≠ p.2)
    by_cases hP : P.Nonempty
    · obtain ⟨p₀, hp₀, hmin⟩ := Finset.exists_min_image P (fun p => dist p.1 p.2) hP
      have hne : p₀.1 ≠ p₀.2 := (Finset.mem_filter.mp hp₀).2
      refine ⟨dist p₀.1 p₀.2, dist_pos.mpr hne, fun u hu v hv huv => ?_⟩
      exact hmin (u, v) (Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hu, hv⟩, huv⟩)
    · rw [Finset.not_nonempty_iff_eq_empty] at hP
      refine ⟨1, one_pos, fun u hu v hv huv => ?_⟩
      exfalso
      have : (u, v) ∈ P := Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hu, hv⟩, huv⟩
      rw [hP] at this; exact Finset.notMem_empty _ this
  have hδ_C : ∃ d₂ : ℝ, 0 < d₂ ∧ ∀ i ∈ E, ∀ v ∈ A, v ≠ D.γ i 0 → v ≠ D.γ i 1 →
      ∀ t : unitInterval, d₂ ≤ dist v (D.γ i t) := by
    let Pairs := (E ×ˢ A).filter (fun p => p.2 ≠ D.γ p.1 0 ∧ p.2 ≠ D.γ p.1 1)
    have hper : ∀ p ∈ Pairs, ∃ d : ℝ, 0 < d ∧ ∀ t : unitInterval, d ≤ dist p.2 (D.γ p.1 t) := by
      intro p hp
      have hp' := Finset.mem_filter.mp hp
      have hiE : p.1 ∈ E := (Finset.mem_product.mp hp'.1).1
      have hvA : p.2 ∈ A := (Finset.mem_product.mp hp'.1).2
      have hdisj : Disjoint ({p.2} : Set _) (Set.range (D.γ p.1)) := by
        rw [Set.disjoint_singleton_left]
        rintro ⟨t, ht⟩
        by_cases h0 : t = 0
        · subst h0; exact hp'.2.1 ht.symm
        · by_cases h1 : t = 1
          · subst h1; exact hp'.2.2 ht.symm
          · exact D.hint p.1 hiE t (lt_of_le_of_ne t.2.1 (Ne.symm h0))
              (lt_of_le_of_ne t.2.2 h1) (ht.symm ▸ hvA)
      obtain ⟨d, hd, hle⟩ := exists_pos_dist_of_disjoint_compact isCompact_singleton
        (isCompact_range (D.γ p.1).continuous) hdisj
      exact ⟨d, hd, fun t => hle p.2 rfl (D.γ p.1 t) ⟨t, rfl⟩⟩
    by_cases hP : Pairs.Nonempty
    · let f : ℕ × EuclideanSpace ℝ (Fin 2) → ℝ := fun p =>
        if h : p ∈ Pairs then (hper p h).choose else 1
      obtain ⟨p₀, hp₀, hmin⟩ := Finset.exists_min_image Pairs f hP
      have hpos : 0 < f p₀ := by dsimp only [f]; rw [dif_pos hp₀]; exact (hper p₀ hp₀).choose_spec.1
      refine ⟨f p₀, hpos, fun i hi v hv h0 h1 t => ?_⟩
      have hp : (i, v) ∈ Pairs := Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hi, hv⟩, h0, h1⟩
      have hle1 : f p₀ ≤ f (i, v) := hmin (i, v) hp
      have hle2 : f (i, v) ≤ dist v (D.γ i t) := by
        dsimp only [f]; rw [dif_pos hp]; exact (hper (i, v) hp).choose_spec.2 t
      exact hle1.trans hle2
    · rw [Finset.not_nonempty_iff_eq_empty] at hP
      refine ⟨1, one_pos, fun i hi v hv h0 h1 _ => ?_⟩
      exfalso
      have : (i, v) ∈ Pairs := Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hi, hv⟩, h0, h1⟩
      rw [hP] at this; exact Finset.notMem_empty _ this
  obtain ⟨d₁, hd₁, hA_sep⟩ := hδ_A
  obtain ⟨d₂, hd₂, hC_sep⟩ := hδ_C
  let δ : ℝ := min (d₁ / 4) (d₂ / 4)
  have hδ_pos : 0 < δ := lt_min (by linarith) (by linarith)
  have hδ_A3 : ∀ u ∈ A, ∀ v ∈ A, u ≠ v → 3 * δ ≤ dist u v := fun u hu v hv huv => by
    have := hA_sep u hu v hv huv; have : δ ≤ d₁ / 4 := min_le_left _ _; linarith
  have hδ_C2 : ∀ i ∈ E, ∀ v ∈ A, v ≠ D.γ i 0 → v ≠ D.γ i 1 →
      ∀ t : unitInterval, 2 * δ ≤ dist v (D.γ i t) := fun i hi v hv h0 h1 t => by
    have := hC_sep i hi v hv h0 h1 t; have : δ ≤ d₂ / 4 := min_le_right _ _; linarith
  -- Step 2: For each edge i ∈ E, extract last exit s_i from B̄(u_i, δ) and first entry e_i into B̄(v_i, δ)
  have hex_se : ∀ i ∈ E, ∃ (s e : unitInterval),
      0 < s ∧ s < e ∧ e < 1 ∧
      dist (D.γ i s) (D.γ i 0) = δ ∧
      dist (D.γ i e) (D.γ i 1) = δ ∧
      (∀ t : unitInterval, s < t → δ < dist (D.γ i t) (D.γ i 0)) ∧
      (∀ t : unitInterval, s ≤ t → t < e → δ < dist (D.γ i t) (D.γ i 1)) := by
    intro i hi
    let u := D.γ i 0
    let v := D.γ i 1
    have huv : 3 * δ ≤ dist u v := hδ_A3 u (D.h0 i hi) v (D.h1 i hi) (curveDrawing_ends_ne D hi)
    -- Compact set S = {t | dist (γ i t) u ≤ δ}
    let S : Set unitInterval := {t | dist (D.γ i t) u ≤ δ}
    have hS_cl : IsClosed S := isClosed_le (continuous_dist.comp ((D.γ i).continuous.prodMk continuous_const)) continuous_const
    have hS_ne : S.Nonempty := ⟨0, by simp [S, u, hδ_pos.le]⟩
    obtain ⟨s, hsS, hs_max⟩ := hS_cl.isCompact.exists_isMaxOn hS_ne continuous_id.continuousOn
    have hs_lt1 : s < 1 := by
      refine lt_of_le_of_ne s.2.2 (fun h => ?_)
      subst h
      have h1 : dist v u ≤ δ := hsS
      rw [_root_.dist_comm] at h1; linarith
    have hs_gt : ∀ t : unitInterval, s < t → δ < dist (D.γ i t) u := by
      intro t hst
      by_contra hle; push Not at hle
      exact not_lt.mpr (hs_max hle) hst
    have hs_dist : dist (D.γ i s) u = δ := by
      apply le_antisymm hsS
      by_contra hlt; push Not at hlt
      have hopen : IsOpen {t : unitInterval | dist (D.γ i t) u < δ} :=
        isOpen_lt (continuous_dist.comp ((D.γ i).continuous.prodMk continuous_const)) continuous_const
      have hnhds := hopen.mem_nhds hlt
      rw [Metric.mem_nhds_iff] at hnhds
      obtain ⟨r, hr, hball⟩ := hnhds
      let t_val : ℝ := s.1 + min (r / 2) ((1 - s.1) / 2)
      have ht_mem : t_val ∈ Set.Icc (0 : ℝ) 1 := by
        have h1 : 0 ≤ s.1 := s.2.1
        have h2 : s.1 < 1 := hs_lt1
        have hm : 0 < min (r / 2) ((1 - s.1) / 2) := lt_min (by linarith) (by linarith)
        have hm2 : min (r / 2) ((1 - s.1) / 2) ≤ (1 - s.1) / 2 := min_le_right _ _
        exact ⟨by linarith, by linarith⟩
      let t : unitInterval := ⟨t_val, ht_mem⟩
      have hst : s < t := by
        show s.1 < t_val
        have hm : 0 < min (r / 2) ((1 - s.1) / 2) := lt_min (by linarith) (by have : s.1 < 1 := hs_lt1; linarith)
        linarith
      have htb : t ∈ Metric.ball s r := by
        rw [Metric.mem_ball, Subtype.dist_eq, Real.dist_eq]
        have hm1 : min (r / 2) ((1 - s.1) / 2) ≤ r / 2 := min_le_left _ _
        have hm0 : 0 < min (r / 2) ((1 - s.1) / 2) := lt_min (by linarith) (by have : s.1 < 1 := hs_lt1; linarith)
        have hsub : t.1 - s.1 = min (r / 2) ((1 - s.1) / 2) := by dsimp only [t, t_val]; ring
        rw [hsub, abs_of_pos hm0]; linarith
      exact (not_lt.mpr (hs_gt t hst).le) (hball htb)
    have hs_pos : 0 < s := lt_of_le_of_ne s.2.1 (fun h => by
      have : dist (D.γ i 0) u = δ := h ▸ hs_dist
      simp [u] at this; linarith)
    -- Compact set T = {t | s ≤ t ∧ dist (γ i t) v ≤ δ}
    let T : Set unitInterval := {t | s ≤ t ∧ dist (D.γ i t) v ≤ δ}
    have hT_cl : IsClosed T :=
      (isClosed_le continuous_const continuous_id).inter
        (isClosed_le (continuous_dist.comp ((D.γ i).continuous.prodMk continuous_const)) continuous_const)
    have hT_ne : T.Nonempty := ⟨1, s.2.2, by simp [v, hδ_pos.le]⟩
    obtain ⟨e, heT, he_min⟩ := hT_cl.isCompact.exists_isMinOn hT_ne continuous_id.continuousOn
    have hs_lt_e : s < e := lt_of_le_of_ne heT.1 (fun h => by
      have hdv : dist (D.γ i s) v ≤ δ := h ▸ heT.2
      have htri := dist_triangle u (D.γ i s) v
      rw [dist_comm u (D.γ i s), hs_dist] at htri
      linarith)
    have he_lt : ∀ t : unitInterval, s ≤ t → t < e → δ < dist (D.γ i t) v := by
      intro t hst hte
      by_contra hle; push Not at hle
      exact not_lt.mpr (he_min ⟨hst, hle⟩) hte
    have he_dist : dist (D.γ i e) v = δ := by
      apply le_antisymm heT.2
      by_contra hlt; push Not at hlt
      have hopen : IsOpen {t : unitInterval | dist (D.γ i t) v < δ} :=
        isOpen_lt (continuous_dist.comp ((D.γ i).continuous.prodMk continuous_const)) continuous_const
      obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hopen.mem_nhds hlt)
      let t_val : ℝ := e.1 - min (r / 2) ((e.1 - s.1) / 2)
      have hse_r : s.1 < e.1 := hs_lt_e
      have hm0 : 0 < min (r / 2) ((e.1 - s.1) / 2) := lt_min (by linarith) (by linarith)
      have hm2 : min (r / 2) ((e.1 - s.1) / 2) ≤ (e.1 - s.1) / 2 := min_le_right _ _
      have ht_mem : t_val ∈ Set.Icc (0 : ℝ) 1 :=
        ⟨by have := s.2.1; linarith, by have := e.2.2; linarith⟩
      let t : unitInterval := ⟨t_val, ht_mem⟩
      have hst : s ≤ t := show s.1 ≤ t_val by linarith
      have hte : t < e := show t_val < e.1 by linarith
      have htb : t ∈ Metric.ball e r := by
        rw [Metric.mem_ball, Subtype.dist_eq, Real.dist_eq]
        have hm1 : min (r / 2) ((e.1 - s.1) / 2) ≤ r / 2 := min_le_left _ _
        have hsub : t.1 - e.1 = -min (r / 2) ((e.1 - s.1) / 2) := by dsimp only [t, t_val]; ring
        rw [hsub, abs_neg, abs_of_pos hm0]; linarith
      exact (not_lt.mpr (he_lt t hst hte).le) (hball htb)
    have he_lt1 : e < 1 := lt_of_le_of_ne e.2.2 (fun h => by
      have : dist (D.γ i 1) v = δ := h ▸ he_dist
      simp [v] at this; linarith)
    exact ⟨s, e, hs_pos, hs_lt_e, he_lt1, hs_dist, he_dist, hs_gt, he_lt⟩
  let sI (i : ℕ) : unitInterval := if h : i ∈ E then (hex_se i h).choose else 0
  let eI (i : ℕ) : unitInterval := if h : i ∈ E then (hex_se i h).choose_spec.choose else 1
  have hse_spec : ∀ i ∈ E,
      0 < sI i ∧ sI i < eI i ∧ eI i < 1 ∧
      dist (D.γ i (sI i)) (D.γ i 0) = δ ∧
      dist (D.γ i (eI i)) (D.γ i 1) = δ ∧
      (∀ t : unitInterval, sI i < t → δ < dist (D.γ i t) (D.γ i 0)) ∧
      (∀ t : unitInterval, sI i ≤ t → t < eI i → δ < dist (D.γ i t) (D.γ i 1)) := by
    intro i hi
    dsimp only [sI, eI]; rw [dif_pos hi, dif_pos hi]
    exact (hex_se i hi).choose_spec.choose_spec
  -- Define compact middle arcs M i and radial unions Krad i
  let M (i : ℕ) : Set (EuclideanSpace ℝ (Fin 2)) := D.γ i '' Set.Icc (sI i) (eI i)
  let Krad (i : ℕ) : Set (EuclideanSpace ℝ (Fin 2)) :=
    seg2 (D.γ i 0) (D.γ i (sI i)) ∪ seg2 (D.γ i 1) (D.γ i (eI i))
  have hM_comp : ∀ i, IsCompact (M i) := fun i => isCompact_Icc.image (D.γ i).continuous
  have hKrad_comp : ∀ i, IsCompact (Krad i) := fun i =>
    (isCompact_seg2 _ _).union (isCompact_seg2 _ _)
  -- Key disjointness properties between M i, Krad j, and A!
  have hM_dist_A : ∀ i ∈ E, ∀ x ∈ M i, ∀ w ∈ A, δ ≤ dist x w := by
    intro i hi x hx w hw
    obtain ⟨t, ⟨hts, hte⟩, rfl⟩ := hx
    have hsp := hse_spec i hi
    by_cases hw0 : w = D.γ i 0
    · subst hw0
      rcases eq_or_lt_of_le hts with rfl | hlt
      · exact hsp.2.2.2.1.ge
      · exact (hsp.2.2.2.2.2.1 t hlt).le
    · by_cases hw1 : w = D.γ i 1
      · subst hw1
        rcases eq_or_lt_of_le hte with rfl | hlt
        · exact hsp.2.2.2.2.1.ge
        · exact (hsp.2.2.2.2.2.2 t hts hlt).le
      · rw [_root_.dist_comm]; linarith [hδ_C2 i hi w hw hw0 hw1 t]
  have hM_disj_M : ∀ i ∈ E, ∀ j ∈ E, i ≠ j → Disjoint (M i) (M j) := by
    intro i hi j hj hne
    rw [Set.disjoint_left]
    intro x hxi hxj
    obtain ⟨t₁, ⟨h1a, h1b⟩, rfl⟩ := hxi
    obtain ⟨t₂, _, h2eq⟩ := hxj
    have hsp1 := hse_spec i hi
    have hnotA : D.γ i t₁ ∉ (A : Set _) :=
      D.hint i hi t₁ (lt_of_lt_of_le hsp1.1 h1a) (lt_of_le_of_lt h1b hsp1.2.2.1)
    have hmem : D.γ i t₁ ∈ (Set.range (D.γ i) ∩ Set.range (D.γ j)) \ (A : Set _) :=
      ⟨⟨⟨t₁, rfl⟩, ⟨t₂, h2eq⟩⟩, hnotA⟩
    rw [hdisj_int i hi j hj hne] at hmem
    exact hmem
  have hM_disj_Krad : ∀ i ∈ E, ∀ j ∈ E, i ≠ j → Disjoint (M i) (Krad j) := by
    intro i hi j hj hne
    rw [Set.disjoint_left]
    intro x hxi hxj
    obtain ⟨t₁, ⟨h1a, h1b⟩, rfl⟩ := hxi
    have hsp1 := hse_spec i hi
    have hsp2 := hse_spec j hj
    have hnotA : D.γ i t₁ ∉ (A : Set _) :=
      D.hint i hi t₁ (lt_of_lt_of_le hsp1.1 h1a) (lt_of_le_of_lt h1b hsp1.2.2.1)
    rcases hxj with hx0 | hx1
    · have hle : dist (D.γ i t₁) (D.γ j 0) ≤ δ :=
        dist_seg2_le (by simp [hδ_pos.le]) hsp2.2.2.2.1.le hx0
      have hge : δ ≤ dist (D.γ i t₁) (D.γ j 0) := hM_dist_A i hi _ ⟨t₁, ⟨h1a, h1b⟩, rfl⟩ _ (D.h0 j hj)
      have heq : D.γ i t₁ = D.γ j (sI j) :=
        radial_seg2_sphere_eq hδ_pos hsp2.2.2.2.1 hx0 (le_antisymm hle hge)
      have hmem : D.γ i t₁ ∈ (Set.range (D.γ i) ∩ Set.range (D.γ j)) \ (A : Set _) :=
        ⟨⟨⟨t₁, rfl⟩, ⟨sI j, heq.symm⟩⟩, hnotA⟩
      rw [hdisj_int i hi j hj hne] at hmem; exact hmem
    · have hle : dist (D.γ i t₁) (D.γ j 1) ≤ δ :=
        dist_seg2_le (by simp [hδ_pos.le]) hsp2.2.2.2.2.1.le hx1
      have hge : δ ≤ dist (D.γ i t₁) (D.γ j 1) := hM_dist_A i hi _ ⟨t₁, ⟨h1a, h1b⟩, rfl⟩ _ (D.h1 j hj)
      have heq : D.γ i t₁ = D.γ j (eI j) :=
        radial_seg2_sphere_eq hδ_pos hsp2.2.2.2.2.1 hx1 (le_antisymm hle hge)
      have hmem : D.γ i t₁ ∈ (Set.range (D.γ i) ∩ Set.range (D.γ j)) \ (A : Set _) :=
        ⟨⟨⟨t₁, rfl⟩, ⟨eI j, heq.symm⟩⟩, hnotA⟩
      rw [hdisj_int i hi j hj hne] at hmem; exact hmem
  have hKrad_inter : ∀ i ∈ E, ∀ j ∈ E, i ≠ j → ∀ x ∈ Krad i, x ∈ Krad j → x ∈ A := by
    intro i hi j hj hne x hxi hxj
    have hsp1 := hse_spec i hi
    have hsp2 := hse_spec j hj
    have haux : ∀ (w₁ a₁ w₂ a₂ : EuclideanSpace ℝ (Fin 2)),
        w₁ ∈ A → w₂ ∈ A → dist a₁ w₁ = δ → dist a₂ w₂ = δ → a₁ ≠ a₂ →
        x ∈ seg2 w₁ a₁ → x ∈ seg2 w₂ a₂ → x ∈ A := by
      intro w₁ a₁ w₂ a₂ hw1 hw2 ha1 ha2 hnea h1 h2
      by_cases hw : w₁ = w₂
      · subst hw
        have := radial_seg2_inter hδ_pos ha1 ha2 hnea h1 h2
        subst this; exact hw1
      · exfalso
        have hle1 : dist x w₁ ≤ δ := dist_seg2_le (by simp [hδ_pos.le]) ha1.le h1
        have hle2 : dist x w₂ ≤ δ := dist_seg2_le (by simp [hδ_pos.le]) ha2.le h2
        have hsep := hδ_A3 w₁ hw1 w₂ hw2 hw
        have htri := dist_triangle w₁ x w₂
        rw [dist_comm w₁ x] at htri
        linarith
    have hneq : ∀ (t₁ t₂ : unitInterval), 0 < t₁ → t₁ < 1 → D.γ i t₁ ≠ D.γ j t₂ := by
      intro t₁ t₂ h0 h1 heq
      have hnotA := D.hint i hi t₁ h0 h1
      have hmem : D.γ i t₁ ∈ (Set.range (D.γ i) ∩ Set.range (D.γ j)) \ (A : Set _) :=
        ⟨⟨⟨t₁, rfl⟩, ⟨t₂, heq.symm⟩⟩, hnotA⟩
      rw [hdisj_int i hi j hj hne] at hmem; exact hmem
    rcases hxi with h1 | h1 <;> rcases hxj with h2 | h2
    · exact haux _ _ _ _ (D.h0 i hi) (D.h0 j hj) hsp1.2.2.2.1 hsp2.2.2.2.1
        (hneq _ _ hsp1.1 (hsp1.2.1.trans hsp1.2.2.1)) h1 h2
    · exact haux _ _ _ _ (D.h0 i hi) (D.h1 j hj) hsp1.2.2.2.1 hsp2.2.2.2.2.1
        (hneq _ _ hsp1.1 (hsp1.2.1.trans hsp1.2.2.1)) h1 h2
    · exact haux _ _ _ _ (D.h1 i hi) (D.h0 j hj) hsp1.2.2.2.2.1 hsp2.2.2.2.1
        (hneq _ _ (hsp1.1.trans hsp1.2.1) hsp1.2.2.1) h1 h2
    · exact haux _ _ _ _ (D.h1 i hi) (D.h1 j hj) hsp1.2.2.2.2.1 hsp2.2.2.2.2.1
        (hneq _ _ (hsp1.1.trans hsp1.2.1) hsp1.2.2.1) h1 h2
  -- Step 3: Pick ε > 0 with 3*ε ≤ δ and 3*ε ≤ dist(M i, M j ∪ Krad j) for all i ≠ j!
  have hε_ex : ∃ ε : ℝ, 0 < ε ∧ 3 * ε ≤ δ ∧
      ∀ i ∈ E, ∀ j ∈ E, i ≠ j → ∀ x ∈ M i, ∀ y ∈ M j ∪ Krad j, 3 * ε ≤ dist x y := by
    let Pairs := (E ×ˢ E).filter (fun p => p.1 ≠ p.2)
    have hper : ∀ p ∈ Pairs, ∃ d : ℝ, 0 < d ∧ ∀ x ∈ M p.1, ∀ y ∈ M p.2 ∪ Krad p.2, d ≤ dist x y := by
      intro p hp
      have hp' := Finset.mem_filter.mp hp
      have h1 := (Finset.mem_product.mp hp'.1).1
      have h2 := (Finset.mem_product.mp hp'.1).2
      exact exists_pos_dist_of_disjoint_compact (hM_comp p.1)
        ((hM_comp p.2).union (hKrad_comp p.2))
        (Set.disjoint_union_right.mpr ⟨hM_disj_M p.1 h1 p.2 h2 hp'.2, hM_disj_Krad p.1 h1 p.2 h2 hp'.2⟩)
    by_cases hP : Pairs.Nonempty
    · let f : ℕ × ℕ → ℝ := fun p => if h : p ∈ Pairs then (hper p h).choose else 1
      obtain ⟨p₀, hp₀, hmin⟩ := Finset.exists_min_image Pairs f hP
      have hpos : 0 < f p₀ := by dsimp only [f]; rw [dif_pos hp₀]; exact (hper p₀ hp₀).choose_spec.1
      refine ⟨min (δ / 3) (f p₀ / 3), lt_min (by linarith) (by linarith),
        by have := min_le_left (δ / 3) (f p₀ / 3); linarith, fun i hi j hj hne x hx y hy => ?_⟩
      have hp : (i, j) ∈ Pairs := Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hi, hj⟩, hne⟩
      have hle1 : f p₀ ≤ f (i, j) := hmin (i, j) hp
      have hle2 : f (i, j) ≤ dist x y := by
        dsimp only [f]; rw [dif_pos hp]; exact (hper (i, j) hp).choose_spec.2 x hx y hy
      have hm : min (δ / 3) (f p₀ / 3) ≤ f p₀ / 3 := min_le_right _ _
      linarith
    · rw [Finset.not_nonempty_iff_eq_empty] at hP
      refine ⟨δ / 3, by linarith, by linarith, fun i hi j hj hne _ _ _ _ => ?_⟩
      exfalso
      have : (i, j) ∈ Pairs := Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hi, hj⟩, hne⟩
      rw [hP] at this; exact Finset.notMem_empty _ this
  obtain ⟨ε, hε_pos, hε_δ, hε_sep⟩ := hε_ex
  -- Step 4: Uniform-continuity polygonal sampling of each M i + loop erasure!
  have hraw_chain : ∀ i ∈ E, ∃ L : List (ℝ × ℝ),
      IsSimpleChain L ∧
      (∃ (h0 : 0 < L.length) (h1 : L.length - 1 < L.length),
        L[0]'h0 = toProd (D.γ i 0) ∧ L[L.length - 1]'h1 = toProd (D.γ i 1)) ∧
      ∀ x : EuclideanSpace ℝ (Fin 2), toProd x ∈ chainUnion L →
        x ∈ Krad i ∨ ∃ y ∈ M i, dist x y < ε := by
    intro i hi
    have hsp := hse_spec i hi
    have huc : UniformContinuous (D.γ i) := CompactSpace.uniformContinuous_of_continuous (D.γ i).continuous
    obtain ⟨η, hη_pos, hη_dist⟩ := Metric.uniformContinuous_iff.mp huc ε hε_pos
    obtain ⟨N0, hN0⟩ := exists_nat_gt (1 / η)
    let N : ℕ := N0 + 1
    have hN_pos : (0 : ℝ) < (N : ℝ) := by positivity
    have hN_inv : 1 / (N : ℝ) < η := by
      have h1 : 1 / η < (N : ℝ) := lt_of_lt_of_le hN0 (by exact_mod_cast Nat.le_succ N0)
      rw [div_lt_iff₀ hN_pos]
      have h2 := (div_lt_iff₀ hη_pos).mp h1
      linarith
    -- Grid points tGrid k ∈ [sI i, eI i] for k = 0..N
    let tGrid (k : ℕ) : unitInterval :=
      if hk : k ≤ N then
        ⟨(1 - (k : ℝ) / (N : ℝ)) * (sI i).1 + ((k : ℝ) / (N : ℝ)) * (eI i).1, by
          have hk0 : 0 ≤ (k : ℝ) / (N : ℝ) := by positivity
          have hk1 : (k : ℝ) / (N : ℝ) ≤ 1 := (div_le_one hN_pos).mpr (by exact_mod_cast hk)
          have hs0 := (sI i).2.1; have hs1 := (sI i).2.2
          have he0 := (eI i).2.1; have he1 := (eI i).2.2
          exact ⟨by nlinarith, by nlinarith⟩⟩
      else eI i
    have htGrid_0 : tGrid 0 = sI i := by
      apply Subtype.ext; dsimp only [tGrid]; rw [dif_pos (Nat.zero_le N)]; simp
    have htGrid_N : tGrid N = eI i := by
      apply Subtype.ext; dsimp only [tGrid]; rw [dif_pos (le_refl N)]
      simp
    have htGrid_mem : ∀ k ≤ N, tGrid k ∈ Set.Icc (sI i) (eI i) := by
      intro k hk
      have hse_le : (sI i).1 ≤ (eI i).1 := hsp.2.1.le
      have hk0 : 0 ≤ (k : ℝ) / (N : ℝ) := by positivity
      have hk1 : (k : ℝ) / (N : ℝ) ≤ 1 := (div_le_one hN_pos).mpr (by exact_mod_cast hk)
      constructor
      · show (sI i).1 ≤ (tGrid k).1
        dsimp only [tGrid]; rw [dif_pos hk]; nlinarith
      · show (tGrid k).1 ≤ (eI i).1
        dsimp only [tGrid]; rw [dif_pos hk]; nlinarith
    have htGrid_step : ∀ k < N, dist (D.γ i (tGrid k)) (D.γ i (tGrid (k + 1))) < ε := by
      intro k hk
      apply hη_dist
      rw [Subtype.dist_eq, Real.dist_eq]
      dsimp only [tGrid]; rw [dif_pos hk.le, dif_pos (Nat.succ_le_of_lt hk)]
      have hdiff : ((1 - (k : ℝ) / (N : ℝ)) * (sI i).1 + (k : ℝ) / (N : ℝ) * (eI i).1) -
          ((1 - ((k + 1 : ℕ) : ℝ) / (N : ℝ)) * (sI i).1 + ((k + 1 : ℕ) : ℝ) / (N : ℝ) * (eI i).1) =
          -(((eI i).1 - (sI i).1) / (N : ℝ)) := by
        push_cast; field_simp [hN_pos.ne']; ring
      rw [hdiff, abs_neg]
      have hse_pos : 0 ≤ (eI i).1 - (sI i).1 := by have : (sI i).1 < (eI i).1 := hsp.2.1; linarith
      have hse_le1 : (eI i).1 - (sI i).1 ≤ 1 := by have := (eI i).2.2; have := (sI i).2.1; linarith
      rw [abs_of_nonneg (div_nonneg hse_pos hN_pos.le)]
      calc ((eI i).1 - (sI i).1) / (N : ℝ) ≤ 1 / (N : ℝ) := div_le_div_of_nonneg_right hse_le1 hN_pos.le
        _ < η := hN_inv
    -- Raw polygonal list: (γ i 0) :: ((grid 0..N) ++ [γ i 1])
    let rawPts : List (EuclideanSpace ℝ (Fin 2)) :=
      D.γ i 0 :: ((List.range (N + 1)).map (fun k => D.γ i (tGrid k)) ++ [D.γ i 1])
    let Lraw : List (ℝ × ℝ) := rawPts.map toProd
    have hLraw_len : Lraw.length = N + 3 := by simp [Lraw, rawPts]
    have hraw_get : ∀ (m : ℕ) (hm : m < N + 3),
        rawPts[m]'(by simp [rawPts]; omega) =
          if m = 0 then D.γ i 0
          else if m ≤ N + 1 then D.γ i (tGrid (m - 1))
          else D.γ i 1 := by
      intro m hm
      dsimp only [rawPts]
      rcases m with _ | m'
      · simp
      · simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, List.getElem_cons_succ]
        rw [List.getElem_append]
        have hml : ((List.range (N + 1)).map (fun k => D.γ i (tGrid k))).length = N + 1 := by simp
        split_ifs with h1 h2
        · simp
        · omega
        · omega
        · simp
    have hLraw_0 : Lraw[0]'(by omega) = toProd (D.γ i 0) := by
      simp [Lraw, rawPts]
    have hLraw_last : Lraw[Lraw.length - 1]'(by omega) = toProd (D.γ i 1) := by
      have hidx : Lraw.length - 1 = N + 2 := by omega
      simp only [Lraw, List.getElem_map]
      have h1 : rawPts[Lraw.length - 1]'(by simp [rawPts, Lraw]) = rawPts[N + 2]'(by simp [rawPts]) := by
        congr 1
      rw [h1, hraw_get (N + 2) (by omega)]
      simp [show ¬ (N + 2 ≤ N + 1) by omega]
    have hLraw_cov : ∀ x : EuclideanSpace ℝ (Fin 2), toProd x ∈ chainUnion Lraw →
        x ∈ Krad i ∨ ∃ y ∈ M i, dist x y < ε := by
      rintro x ⟨m, hm, hx⟩
      rw [hLraw_len] at hm
      have hx' : x ∈ seg2 (rawPts[m]'(by simp [rawPts]; omega)) (rawPts[m + 1]'(by simp [rawPts]; omega)) := by
        rw [← mem_pseg_toProd]
        simpa [Lraw] using hx
      rw [hraw_get m (by omega), hraw_get (m + 1) hm] at hx'
      by_cases hm0 : m = 0
      · subst hm0
        simp only [↓reduceIte, Nat.add_eq_zero_iff, one_ne_zero, and_false, show 1 ≤ N + 1 by omega,
          Nat.sub_self, htGrid_0] at hx'
        exact Or.inl (Or.inl hx')
      · by_cases hmN : m ≤ N
        · simp only [hm0, ↓reduceIte, show m ≤ N + 1 by omega, show ¬ (m + 1 = 0) by omega,
            show m + 1 ≤ N + 1 by omega, Nat.add_sub_cancel] at hx'
          right
          refine ⟨D.γ i (tGrid (m - 1)), ⟨tGrid (m - 1), htGrid_mem (m - 1) (by omega), rfl⟩, ?_⟩
          have hstep : dist (D.γ i (tGrid (m - 1))) (D.γ i (tGrid m)) < ε := by
            have := htGrid_step (m - 1) (by omega)
            rwa [show m - 1 + 1 = m by omega] at this
          rw [_root_.dist_comm] at hstep
          have hle := dist_seg2_le (p := D.γ i (tGrid (m - 1))) (r := dist (D.γ i (tGrid m)) (D.γ i (tGrid (m - 1))))
            (by simp [dist_nonneg]) le_rfl hx'
          exact lt_of_le_of_lt hle hstep
        · have hm_eq : m = N + 1 := by omega
          subst hm_eq
          simp only [show ¬ (N + 1 = 0) by omega, ↓reduceIte, le_refl, Nat.add_sub_cancel, htGrid_N,
            show ¬ (N + 1 + 1 = 0) by omega, show ¬ (N + 1 + 1 ≤ N + 1) by omega] at hx'
          left; right
          rcases hx' with ⟨t, ht0, ht1, rfl⟩
          refine ⟨1 - t, by linarith, by linarith, ?_⟩
          simp only [sub_sub_cancel]; abel
    have hne_raw : Lraw[0]'(by omega) ≠ Lraw[Lraw.length - 1]'(by omega) := by
      rw [hLraw_0, hLraw_last]
      exact fun h => curveDrawing_ends_ne D hi (toProd_inj h)
    obtain ⟨L', hS', h0', h1', he0', he1', hsub'⟩ :=
      exists_simple_chain Lraw.length Lraw rfl (by omega) hne_raw
    exact ⟨L', hS', ⟨h0', h1', he0'.trans hLraw_0, he1'.trans hLraw_last⟩,
      fun x hx => hLraw_cov x (hsub' hx)⟩
  -- Step 5: Assemble SimplePLDrawing (A.image toProd) E!
  let P (i : ℕ) : List (ℝ × ℝ) := if h : i ∈ E then (hraw_chain i h).choose else []
  have hP_spec : ∀ i ∈ E,
      IsSimpleChain (P i) ∧
      (∃ (h0 : 0 < (P i).length) (h1 : (P i).length - 1 < (P i).length),
        (P i)[0]'h0 = toProd (D.γ i 0) ∧ (P i)[(P i).length - 1]'h1 = toProd (D.γ i 1)) ∧
      ∀ x : EuclideanSpace ℝ (Fin 2), toProd x ∈ chainUnion (P i) →
        x ∈ Krad i ∨ ∃ y ∈ M i, dist x y < ε := by
    intro i hi; dsimp only [P]; rw [dif_pos hi]; exact (hraw_chain i hi).choose_spec
  -- Cross-edge separation: for i ≠ j, chainUnion (P i) ∩ chainUnion (P j) ⊆ A.image toProd!
  have hcross_disj : ∀ i ∈ E, ∀ j ∈ E, i ≠ j →
      ∀ z : ℝ × ℝ, z ∈ chainUnion (P i) → z ∈ chainUnion (P j) → z ∈ A.image toProd := by
    intro i hi j hj hne z hzi hzj
    obtain ⟨x, rfl⟩ := toProd_surj z
    have hxi := (hP_spec i hi).2.2 x hzi
    have hxj := (hP_spec j hj).2.2 x hzj
    have hxA : x ∈ A := by
      rcases hxi with hki | ⟨yi, hyi, hdi⟩
      · rcases hxj with hkj | ⟨yj, hyj, hdj⟩
        · exact hKrad_inter i hi j hj hne x hki hkj
        · exfalso
          have hsep := hε_sep j hj i hi hne.symm yj hyj x (Or.inr hki)
          rw [_root_.dist_comm] at hdj; linarith
      · rcases hxj with hkj | ⟨yj, hyj, hdj⟩
        · exfalso
          have hsep := hε_sep i hi j hj hne yi hyi x (Or.inr hkj)
          rw [_root_.dist_comm] at hdi; linarith
        · exfalso
          have hsep := hε_sep i hi j hj hne yi hyi yj (Or.inl hyj)
          have htri := dist_triangle yi x yj
          rw [_root_.dist_comm yi x] at htri; linarith
    exact Finset.mem_image_of_mem toProd hxA
  -- For any i ∈ E and w ∈ A, if toProd w ∈ chainUnion (P i), then w = D.γ i 0 ∨ w = D.γ i 1!
  have hA_in_chain : ∀ i ∈ E, ∀ w ∈ A, toProd w ∈ chainUnion (P i) →
      w = D.γ i 0 ∨ w = D.γ i 1 := by
    intro i hi w hw hmem
    rcases (hP_spec i hi).2.2 w hmem with hk | ⟨y, hy, hdy⟩
    · have hsp := hse_spec i hi
      rcases hk with h0 | h1
      · by_cases hw0 : w = D.γ i 0
        · exact Or.inl hw0
        · exfalso
          have hle := dist_seg2_le (p := D.γ i 0) (r := δ) (by simp [hδ_pos.le]) hsp.2.2.2.1.le h0
          have hsep := hδ_A3 w hw (D.γ i 0) (D.h0 i hi) hw0
          linarith
      · by_cases hw1 : w = D.γ i 1
        · exact Or.inr hw1
        · exfalso
          have hle := dist_seg2_le (p := D.γ i 1) (r := δ) (by simp [hδ_pos.le]) hsp.2.2.2.2.1.le h1
          have hsep := hδ_A3 w hw (D.γ i 1) (D.h1 i hi) hw1
          linarith
    · exfalso
      have hge := hM_dist_A i hi y hy w hw
      rw [_root_.dist_comm] at hdy; linarith
  -- Every vertex of P i lies in chainUnion (P i)
  have hmem_chainUnion : ∀ i ∈ E, ∀ r ∈ P i, r ∈ chainUnion (P i) := by
    intro i hi r hr
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hr
    have hlen := (hP_spec i hi).1.1
    by_cases hk1 : k + 1 < (P i).length
    · exact ⟨k, hk1, ⟨0, le_refl _, zero_le_one, by simp⟩⟩
    · have hkp : k = (P i).length - 1 := by omega
      refine ⟨(P i).length - 2, by omega, ⟨1, zero_le_one, le_refl _, ?_⟩⟩
      simp; congr 1; omega
  let Dpl : SimplePLDrawing (A.image toProd) E :=
    { P := P
      hlen := fun i hi => (hP_spec i hi).1.1
      hnodup := fun i hi => (hP_spec i hi).1.2.1
      hstart := fun i hi => by
        obtain ⟨h0, _, he0, _⟩ := (hP_spec i hi).2.1
        rw [he0]; exact Finset.mem_image_of_mem toProd (D.h0 i hi)
      hend := fun i hi => by
        obtain ⟨_, h1, _, he1⟩ := (hP_spec i hi).2.1
        rw [he1]; exact Finset.mem_image_of_mem toProd (D.h1 i hi)
      hint_notA := fun i hi k hk0 hk1 hmemA => by
        obtain ⟨w, hwA, hw_eq⟩ := Finset.mem_image.mp hmemA
        have hcu : toProd w ∈ chainUnion (P i) := hw_eq.symm ▸ hmem_chainUnion i hi _ (List.getElem_mem _)
        obtain ⟨h0, h1, he0, he1⟩ := (hP_spec i hi).2.1
        rcases hA_in_chain i hi w hwA hcu with rfl | rfl
        · have := (hP_spec i hi).1.2.1.getElem_inj_iff.mp (hw_eq.symm.trans he0.symm); omega
        · have := (hP_spec i hi).1.2.1.getElem_inj_iff.mp (hw_eq.symm.trans he1.symm); omega
      hsimple := by
        intro i hi j hj heq
        have hi' : i ∈ E := hi; have hj' : j ∈ E := hj
        dsimp only at heq; rw [dif_pos hi', dif_pos hj'] at heq
        obtain ⟨_, _, hi0, hi1⟩ := (hP_spec i hi').2.1
        obtain ⟨_, _, hj0, hj1⟩ := (hP_spec j hj').2.1
        rw [hi0, hi1, hj0, hj1] at heq
        apply D.hsimple hi hj
        ext x
        have hx := Finset.ext_iff.mp heq (toProd x)
        simp only [Finset.mem_insert, Finset.mem_singleton, toProd_inj.eq_iff] at hx ⊢
        exact hx
      hint_disj := fun i hi j hj hne k₁ h1 k₂ h2 heq => by
        have h1cu : (P i)[k₁]'(by omega) ∈ chainUnion (P i) := hmem_chainUnion i hi _ (List.getElem_mem _)
        have h2cu : (P i)[k₁]'(by omega) ∈ chainUnion (P j) := heq ▸ hmem_chainUnion j hj _ (List.getElem_mem _)
        have hA := hcross_disj i hi j hj hne _ h1cu h2cu
        obtain ⟨w, hwA, hw_eq⟩ := Finset.mem_image.mp hA
        obtain ⟨_, _, hi0, hi1⟩ := (hP_spec i hi).2.1
        rcases hA_in_chain i hi w hwA (hw_eq.symm ▸ h1cu) with rfl | rfl
        · have := (hP_spec i hi).1.2.1.getElem_inj_iff.mp (hw_eq.symm.trans hi0.symm); omega
        · have := (hP_spec i hi).1.2.1.getElem_inj_iff.mp (hw_eq.symm.trans hi1.symm); omega
      hseg_noncross := fun i hi j hj k₁ h1 k₂ h2 hdiff => by
        by_cases hij : i = j
        · subst hij
          exact (hP_spec i hi).1.2.2.1 k₁ h1 k₂ h2 (hdiff.resolve_left (fun h => h rfl))
        · ext z; simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false]
          rintro ⟨hz1, hz2⟩
          have hzi : z ∈ chainUnion (P i) := ⟨k₁, h1, poseg_subset_pseg hz1⟩
          have hzj : z ∈ chainUnion (P j) := ⟨k₂, h2, hz2⟩
          have hA := hcross_disj i hi j hj hij z hzi hzj
          obtain ⟨w, hwA, rfl⟩ := Finset.mem_image.mp hA
          obtain ⟨_, _, hi0, hi1⟩ := (hP_spec i hi).2.1
          rcases hA_in_chain i hi w hwA hzi with rfl | rfl
          · exact (hP_spec i hi).1.2.2.2 k₁ h1 _ (hi0 ▸ List.getElem_mem _) hz1
          · exact (hP_spec i hi).1.2.2.2 k₁ h1 _ (hi1 ▸ List.getElem_mem _) hz1
      hseg_avoid := fun i hi k hk r hr hmem => by
        have hzi : r ∈ chainUnion (P i) := ⟨k, hk, poseg_subset_pseg hmem⟩
        obtain ⟨_, _, hi0, hi1⟩ := (hP_spec i hi).2.1
        rcases hr with hrA | ⟨j, hj, hrj⟩
        · obtain ⟨w, hwA, rfl⟩ := Finset.mem_image.mp hrA
          rcases hA_in_chain i hi w hwA hzi with rfl | rfl
          · exact (hP_spec i hi).1.2.2.2 k hk _ (hi0 ▸ List.getElem_mem _) hmem
          · exact (hP_spec i hi).1.2.2.2 k hk _ (hi1 ▸ List.getElem_mem _) hmem
        · by_cases hij : i = j
          · subst hij; exact (hP_spec i hi).1.2.2.2 k hk r hrj hmem
          · have hA := hcross_disj i hi j hj hij r hzi (hmem_chainUnion j hj r hrj)
            obtain ⟨w, hwA, rfl⟩ := Finset.mem_image.mp hA
            rcases hA_in_chain i hi w hwA hzi with rfl | rfl
            · exact (hP_spec i hi).1.2.2.2 k hk _ (hi0 ▸ List.getElem_mem _) hmem
            · exact (hP_spec i hi).1.2.2.2 k hk _ (hi1 ▸ List.getElem_mem _) hmem }
  have hbound := simplePLDrawing_edge_bound (A.image toProd) E Dpl
  rwa [Finset.card_image_of_injective A toProd_inj] at hbound

/- ### Part 5: Adjacent-Crossing Elimination (`exists_no_adj_crossing`) -/

private lemma norm_sq_eq_coords (w : EuclideanSpace ℝ (Fin 2)) :
    ‖w‖ ^ 2 = (w 0) ^ 2 + (w 1) ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity), Fin.sum_univ_two]
  simp [Real.norm_eq_abs]

private lemma sphere_not_mem_oseg2 {p a b x : EuclideanSpace ℝ (Fin 2)} {r : ℝ}
    (hr : 0 < r) (ha : dist a p = r) (hb : dist b p = r) (hab : a ≠ b) (hx : x ∈ oseg2 a b) :
    dist x p < r := by
  rcases hx with ⟨t, ht0, ht1, rfl⟩
  rw [dist_eq_norm] at ha hb ⊢
  have hdiff_ne : a - b ≠ 0 := sub_ne_zero.mpr hab
  have hdiff_pos : 0 < ‖a - b‖ ^ 2 := by positivity
  have heq : (1 - t) • a + t • b - p = (1 - t) • (a - p) + t • (b - p) := by
    simp only [smul_sub, sub_smul, one_smul]; abel
  have hsq : ‖(1 - t) • a + t • b - p‖ ^ 2 =
      (1 - t) * ‖a - p‖ ^ 2 + t * ‖b - p‖ ^ 2 - t * (1 - t) * ‖a - b‖ ^ 2 := by
    rw [heq, norm_sq_eq_coords, norm_sq_eq_coords, norm_sq_eq_coords, norm_sq_eq_coords]
    have h0 : ((1 - t) • (a - p) + t • (b - p)) 0 = (1 - t) * (a 0 - p 0) + t * (b 0 - p 0) := by simp
    have h1 : ((1 - t) • (a - p) + t • (b - p)) 1 = (1 - t) * (a 1 - p 1) + t * (b 1 - p 1) := by simp
    have ha0 : (a - p) 0 = a 0 - p 0 := rfl
    have ha1 : (a - p) 1 = a 1 - p 1 := rfl
    have hb0 : (b - p) 0 = b 0 - p 0 := rfl
    have hb1 : (b - p) 1 = b 1 - p 1 := rfl
    have hab0 : (a - b) 0 = a 0 - b 0 := rfl
    have hab1 : (a - b) 1 = a 1 - b 1 := rfl
    rw [h0, h1, ha0, ha1, hb0, hb1, hab0, hab1]; ring
  have hlt_sq : ‖(1 - t) • a + t • b - p‖ ^ 2 < r ^ 2 := by
    rw [hsq, ha, hb]
    have hprod : 0 < t * (1 - t) * ‖a - b‖ ^ 2 := mul_pos (mul_pos ht0 (by linarith)) hdiff_pos
    nlinarith
  nlinarith [norm_nonneg ((1 - t) • a + t • b - p)]

private lemma sphere_inter_seg2 {p a b x : EuclideanSpace ℝ (Fin 2)} {r : ℝ}
    (hr : 0 < r) (ha : dist a p = r) (hb : dist b p = r) (hab : a ≠ b)
    (hx : x ∈ seg2 a b) (hdx : dist x p = r) : x = a ∨ x = b := by
  rcases hx with ⟨t, ht0, ht1, rfl⟩
  by_cases h0 : t = 0
  · left; subst h0; simp
  · by_cases h1 : t = 1
    · right; subst h1; simp
    · exfalso
      have hlt := sphere_not_mem_oseg2 hr ha hb hab ⟨t, lt_of_le_of_ne ht0 (Ne.symm h0),
        lt_of_le_of_ne ht1 h1, rfl⟩
      linarith

private lemma four_point_circle_chords {p a₁ b₁ a₂ b₂ : EuclideanSpace ℝ (Fin 2)} {r : ℝ}
    (hr : 0 < r)
    (ha₁ : dist a₁ p = r) (hb₁ : dist b₁ p = r) (ha₂ : dist a₂ p = r) (hb₂ : dist b₂ p = r)
    (h12 : a₁ ≠ b₁) (h13 : a₁ ≠ a₂) (h14 : a₁ ≠ b₂)
    (h23 : b₁ ≠ a₂) (h24 : b₁ ≠ b₂) (h34 : a₂ ≠ b₂) :
    seg2 a₁ b₁ ∩ seg2 a₂ b₂ = ∅ ∨ seg2 a₁ b₂ ∩ seg2 a₂ b₁ = ∅ := by
  by_contra hboth
  push Not at hboth
  obtain ⟨⟨x, hx1, hx2⟩, ⟨y, hy1, hy2⟩⟩ := hboth
  have hopen : ∀ (u v w z q : EuclideanSpace ℝ (Fin 2)),
      dist u p = r → dist v p = r → dist w p = r → dist z p = r →
      u ≠ v → w ≠ z → u ≠ w → u ≠ z → v ≠ w → v ≠ z →
      q ∈ seg2 u v → q ∈ seg2 w z → q ∈ oseg2 u v ∧ q ∈ oseg2 w z := by
    intro u v w z q hu hv hw hz huv hwz huw huz hvw hvz hq1 hq2
    have hq_not_uv : q ≠ u ∧ q ≠ v := by
      constructor
      · rintro rfl
        rcases sphere_inter_seg2 hr hw hz hwz hq2 hu with rfl | rfl
        · exact huw rfl
        · exact huz rfl
      · rintro rfl
        rcases sphere_inter_seg2 hr hw hz hwz hq2 hv with rfl | rfl
        · exact hvw rfl
        · exact hvz rfl
    have hq_not_wz : q ≠ w ∧ q ≠ z := by
      constructor
      · rintro rfl
        rcases sphere_inter_seg2 hr hu hv huv hq1 hw with rfl | rfl
        · exact huw rfl
        · exact hvw rfl
      · rintro rfl
        rcases sphere_inter_seg2 hr hu hv huv hq1 hz with rfl | rfl
        · exact huz rfl
        · exact hvz rfl
    constructor
    · rcases hq1 with ⟨t, ht0, ht1, rfl⟩
      refine ⟨t, lt_of_le_of_ne ht0 (fun h => hq_not_uv.1 (by subst h; simp)),
        lt_of_le_of_ne ht1 (fun h => hq_not_uv.2 (by subst h; simp)), rfl⟩
    · rcases hq2 with ⟨t, ht0, ht1, rfl⟩
      refine ⟨t, lt_of_le_of_ne ht0 (fun h => hq_not_wz.1 (by subst h; simp)),
        lt_of_le_of_ne ht1 (fun h => hq_not_wz.2 (by subst h; simp)), rfl⟩
  obtain ⟨⟨t, ht0, ht1, hxt⟩, ⟨s, hs0, hs1, hxs⟩⟩ :=
    hopen a₁ b₁ a₂ b₂ x ha₁ hb₁ ha₂ hb₂ h12 h34 h13 h14 h23 h24 hx1 hx2
  obtain ⟨⟨t', ht'0, ht'1, hyt⟩, ⟨s', hs'0, hs'1, hys⟩⟩ :=
    hopen a₁ b₂ a₂ b₁ y ha₁ hb₂ ha₂ hb₁ h14 h23.symm h13 h12 h34.symm h24.symm hy1 hy2
  have eq1 : (1 - t) • a₁ + t • b₁ = (1 - s) • a₂ + s • b₂ := hxt.symm.trans hxs
  have eq2 : (1 - t') • a₁ + t' • b₂ = (1 - s') • a₂ + s' • b₁ := hyt.symm.trans hys
  let α : ℝ := t' * (1 - t) + s * (1 - t')
  let β : ℝ := t' * t - s * s'
  let γ : ℝ := t' * (1 - s) + s * (1 - s')
  have hα : 0 < α := by dsimp only [α]; nlinarith
  have hγ : 0 < γ := by dsimp only [γ]; nlinarith
  have hsum : α + β = γ := by dsimp only [α, β, γ]; ring
  -- Linear identity: α • a₁ + β • b₁ = γ • a₂
  have hlin : α • a₁ + β • b₁ = γ • a₂ := by
    have hcomb : t' • ((1 - t) • a₁ + t • b₁) + s • ((1 - t') • a₁ + t' • b₂) =
        t' • ((1 - s) • a₂ + s • b₂) + s • ((1 - s') • a₂ + s' • b₁) := by
      rw [eq1, eq2]
    ext i
    have hi := congrArg (fun v : EuclideanSpace ℝ (Fin 2) => v i) hcomb
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at hi ⊢
    dsimp only [α, β, γ]
    ring_nf at hi ⊢; linarith
  rcases lt_trichotomy β 0 with hβ_lt | hβ_eq | hβ_gt
  · -- β < 0 => a₁ = (γ / α) • a₂ + ((-β) / α) • b₁ ∈ oseg2 a₂ b₁
    have hmem : a₁ ∈ oseg2 a₂ b₁ := by
      refine ⟨(-β) / α, div_pos (by linarith) hα, (div_lt_one hα).mpr (by linarith), ?_⟩
      ext i
      have hi := congrArg (fun v : EuclideanSpace ℝ (Fin 2) => v i) hlin
      simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at hi ⊢
      have hαne : α ≠ 0 := hα.ne'
      field_simp [hαne]; linarith
    have := sphere_not_mem_oseg2 hr ha₂ hb₁ h23.symm hmem
    linarith
  · -- β = 0 => α = γ > 0 and α • a₁ = α • a₂ => a₁ = a₂
    have heq : α • a₁ = α • a₂ := by
      have : α = γ := by linarith
      rw [hβ_eq, zero_smul, add_zero, ← this] at hlin; exact hlin
    exact h13 (smul_right_injective _ hα.ne' heq)
  · -- β > 0 => a₂ = (α / γ) • a₁ + (β / γ) • b₁ ∈ oseg2 a₁ b₁
    have hmem : a₂ ∈ oseg2 a₁ b₁ := by
      refine ⟨β / γ, div_pos hβ_gt hγ, (div_lt_one hγ).mpr (by linarith), ?_⟩
      ext i
      have hi := congrArg (fun v : EuclideanSpace ℝ (Fin 2) => v i) hlin
      simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at hi ⊢
      have hγne : γ ≠ 0 := hγ.ne'
      field_simp [hγne]; linarith
    have := sphere_not_mem_oseg2 hr ha₁ hb₁ h12 hmem
    linarith

private lemma two_circle_chords_inter_subsingleton {p a₁ b₁ a₂ b₂ : EuclideanSpace ℝ (Fin 2)} {r : ℝ}
    (ha₁ : dist a₁ p = r) (hb₁ : dist b₁ p = r) (ha₂ : dist a₂ p = r) (_hb₂ : dist b₂ p = r)
    (h12 : a₁ ≠ b₁) (h13 : a₁ ≠ a₂) (_h14 : a₁ ≠ b₂)
    (h23 : b₁ ≠ a₂) (_h24 : b₁ ≠ b₂) (_h34 : a₂ ≠ b₂) :
    (seg2 a₁ b₁ ∩ seg2 a₂ b₂).Subsingleton := by
  intro x hx y hy
  by_contra hxy
  rcases hx with ⟨⟨t₁, _, _, hxt1⟩, ⟨s₁, _, _, hxs1⟩⟩
  rcases hy with ⟨⟨t₂, _, _, hyt2⟩, ⟨s₂, _, _, hys2⟩⟩
  have htne : t₂ - t₁ ≠ 0 := fun h => hxy (by
    have : t₁ = t₂ := by linarith
    rw [hxt1, hyt2, this])
  have hsne : s₂ - s₁ ≠ 0 := fun h => hxy (by
    have : s₁ = s₂ := by linarith
    rw [hxs1, hys2, this])
  -- All 3 points a₁, b₁, a₂ lie on the line {x + λ • (y - x)}!
  let v := y - x
  have hv_pos : 0 < ‖v‖ ^ 2 := by
    have : v ≠ 0 := sub_ne_zero.mpr (Ne.symm hxy)
    positivity
  have hline : ∀ (u w : EuclideanSpace ℝ (Fin 2)) (c₁ c₂ : ℝ), c₂ - c₁ ≠ 0 →
      x = (1 - c₁) • u + c₁ • w → y = (1 - c₂) • u + c₂ • w →
      (u = x + (-c₁ / (c₂ - c₁)) • v) ∧ (w = x + ((1 - c₁) / (c₂ - c₁)) • v) := by
    intro u w c₁ c₂ hne hx' hy'
    constructor <;> (ext i
                     have h1 := congrArg (fun z : EuclideanSpace ℝ (Fin 2) => z i) hx'
                     have h2 := congrArg (fun z : EuclideanSpace ℝ (Fin 2) => z i) hy'
                     simp only [PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, v] at h1 h2 ⊢
                     field_simp [hne]; rw [h1, h2]; ring)
  obtain ⟨ha1_eq, hb1_eq⟩ := hline a₁ b₁ t₁ t₂ htne hxt1 hyt2
  obtain ⟨ha2_eq, _⟩ := hline a₂ b₂ s₁ s₂ hsne hxs1 hys2
  let lam₁ := -t₁ / (t₂ - t₁)
  let lam₂ := (1 - t₁) / (t₂ - t₁)
  let lam₃ := -s₁ / (s₂ - s₁)
  have hlam12 : lam₁ ≠ lam₂ := fun h => h12 (by rw [ha1_eq, hb1_eq]; exact congrArg (fun c => x + c • v) h)
  have hlam13 : lam₁ ≠ lam₃ := fun h => h13 (by rw [ha1_eq, ha2_eq]; exact congrArg (fun c => x + c • v) h)
  have hlam23 : lam₂ ≠ lam₃ := fun h => h23 (by rw [hb1_eq, ha2_eq]; exact congrArg (fun c => x + c • v) h)
  -- Each lam satisfies A * lam^2 + B * lam + C = r^2 with A = ‖v‖^2 > 0
  let B : ℝ := 2 * ((x 0 - p 0) * v 0 + (x 1 - p 1) * v 1)
  let C : ℝ := ‖x - p‖ ^ 2
  have hquad : ∀ (q : EuclideanSpace ℝ (Fin 2)) (c : ℝ), q = x + c • v → dist q p = r →
      ‖v‖ ^ 2 * c ^ 2 + B * c + C = r ^ 2 := by
    intro q c hq hd
    rw [dist_eq_norm] at hd
    have hqp : q - p = (x - p) + c • v := by rw [hq]; abel
    have hsq : ‖q - p‖ ^ 2 = ‖v‖ ^ 2 * c ^ 2 + B * c + C := by
      rw [hqp, norm_sq_eq_coords, norm_sq_eq_coords]
      have h0 : ((x - p) + c • v) 0 = (x 0 - p 0) + c * v 0 := by simp
      have h1 : ((x - p) + c • v) 1 = (x 1 - p 1) + c * v 1 := by simp
      have hx0 : (x - p) 0 = x 0 - p 0 := rfl
      have hx1 : (x - p) 1 = x 1 - p 1 := rfl
      dsimp only [B, C]; rw [h0, h1, norm_sq_eq_coords, hx0, hx1]; ring
    rw [← hsq, hd]
  have hq1 := hquad a₁ lam₁ ha1_eq ha₁
  have hq2 := hquad b₁ lam₂ hb1_eq hb₁
  have hq3 := hquad a₂ lam₃ ha2_eq ha₂
  have h12' : ‖v‖ ^ 2 * (lam₁ + lam₂) + B = 0 := by
    have : (lam₁ - lam₂) * (‖v‖ ^ 2 * (lam₁ + lam₂) + B) = 0 := by nlinarith
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hlam12)
  have h13' : ‖v‖ ^ 2 * (lam₁ + lam₃) + B = 0 := by
    have : (lam₁ - lam₃) * (‖v‖ ^ 2 * (lam₁ + lam₃) + B) = 0 := by nlinarith
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hlam13)
  have : ‖v‖ ^ 2 * (lam₂ - lam₃) = 0 := by linarith
  exact hlam23 (sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hv_pos.ne'))

/- #### Piecewise continuous curve combinators on `unitInterval` -/

private noncomputable def clampI (x : ℝ) : unitInterval :=
  ⟨min 1 (max 0 x), ⟨le_min zero_le_one (le_max_left 0 x), min_le_left 1 _⟩⟩

private lemma continuous_clampI : Continuous clampI :=
  Continuous.subtype_mk (continuous_const.min (continuous_const.max continuous_id)) _

private lemma clampI_of_mem {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    (clampI x : unitInterval).1 = x := by
  dsimp only [clampI]; rw [max_eq_right h0, min_eq_right h1]

private def curveReverse (γ : C(unitInterval, EuclideanSpace ℝ (Fin 2))) :
    C(unitInterval, EuclideanSpace ℝ (Fin 2)) :=
  γ.comp ⟨unitInterval.symm, continuous_iff_continuousAt.mpr fun _ =>
    (Continuous.subtype_mk (continuous_const.sub continuous_subtype_val) _).continuousAt⟩

private lemma curveReverse_apply (γ : C(unitInterval, EuclideanSpace ℝ (Fin 2))) (t : unitInterval) :
    curveReverse γ t = γ (unitInterval.symm t) := rfl

private lemma curveReverse_inj {γ : C(unitInterval, EuclideanSpace ℝ (Fin 2))}
    (h : Function.Injective γ) : Function.Injective (curveReverse γ) :=
  fun _ _ heq => unitInterval.symm_bijective.1 (h heq)

private lemma curveReverse_range (γ : C(unitInterval, EuclideanSpace ℝ (Fin 2))) :
    Set.range (curveReverse γ) = Set.range γ := by
  ext x; constructor
  · rintro ⟨t, rfl⟩; exact ⟨unitInterval.symm t, rfl⟩
  · rintro ⟨t, rfl⟩; exact ⟨unitInterval.symm t, by simp [curveReverse_apply]⟩

/-- Splice prefix `γ₁[0..t₁]` + straight chord `[γ₁ t₁, γ₂ t₂]` + suffix `γ₂[t₂..1]`. -/
private noncomputable def curveSpliceChord
    (γ₁ γ₂ : C(unitInterval, EuclideanSpace ℝ (Fin 2)))
    (t₁ t₂ : unitInterval) : C(unitInterval, EuclideanSpace ℝ (Fin 2)) :=
  let f₁ : unitInterval → EuclideanSpace ℝ (Fin 2) := fun t => γ₁ (clampI (3 * t.1 * t₁.1))
  let f₂ : unitInterval → EuclideanSpace ℝ (Fin 2) :=
    fun t => (1 - (3 * t.1 - 1)) • γ₁ t₁ + (3 * t.1 - 1) • γ₂ t₂
  let f₃ : unitInterval → EuclideanSpace ℝ (Fin 2) :=
    fun t => γ₂ (clampI (t₂.1 + (3 * t.1 - 2) * (1 - t₂.1)))
  have hf₁ : Continuous f₁ := γ₁.continuous.comp (continuous_clampI.comp (by fun_prop))
  have hf₂ : Continuous f₂ := by fun_prop
  have hf₃ : Continuous f₃ := γ₂.continuous.comp (continuous_clampI.comp (by fun_prop))
  have h23 : Continuous (fun t : unitInterval => if t.1 ≤ 2 / 3 then f₂ t else f₃ t) :=
    Continuous.if_le hf₂ hf₃ continuous_subtype_val continuous_const (fun t ht => by
      dsimp only [f₂, f₃]
      have hc : clampI (t₂.1 + (3 * t.1 - 2) * (1 - t₂.1)) = t₂ := by
        apply Subtype.ext
        rw [ht]; norm_num
        exact clampI_of_mem t₂.2.1 t₂.2.2
      rw [hc, ht]; norm_num)
  ⟨fun t => if t.1 ≤ 1 / 3 then f₁ t else if t.1 ≤ 2 / 3 then f₂ t else f₃ t,
    Continuous.if_le hf₁ h23 continuous_subtype_val continuous_const (fun t ht => by
      have hle2 : t.1 ≤ 2 / 3 := by linarith
      rw [if_pos hle2]
      dsimp only [f₁, f₂]
      have hc : clampI (3 * t.1 * t₁.1) = t₁ := by
        apply Subtype.ext
        rw [ht]; norm_num
        exact clampI_of_mem t₁.2.1 t₁.2.2
      rw [hc, ht]; norm_num)⟩

private lemma curveSpliceChord_zero (γ₁ γ₂ : C(unitInterval, EuclideanSpace ℝ (Fin 2)))
    (t₁ t₂ : unitInterval) : curveSpliceChord γ₁ γ₂ t₁ t₂ 0 = γ₁ 0 := by
  change (if (0 : ℝ) ≤ 1 / 3 then γ₁ (clampI (3 * 0 * t₁.1)) else _) = γ₁ 0
  rw [if_pos (by norm_num)]
  congr 1; apply Subtype.ext; simp [clampI]

private lemma curveSpliceChord_one (γ₁ γ₂ : C(unitInterval, EuclideanSpace ℝ (Fin 2)))
    (t₁ t₂ : unitInterval) : curveSpliceChord γ₁ γ₂ t₁ t₂ 1 = γ₂ 1 := by
  change (if (1 : ℝ) ≤ 1 / 3 then _ else if (1 : ℝ) ≤ 2 / 3 then _ else
    γ₂ (clampI (t₂.1 + (3 * 1 - 2) * (1 - t₂.1)))) = γ₂ 1
  rw [if_neg (by norm_num), if_neg (by norm_num)]
  congr 1; apply Subtype.ext
  have : t₂.1 + (3 * 1 - 2) * (1 - t₂.1) = 1 := by ring
  rw [this]; exact clampI_of_mem zero_le_one (le_refl 1)

private lemma curveSpliceChord_range (γ₁ γ₂ : C(unitInterval, EuclideanSpace ℝ (Fin 2)))
    (t₁ t₂ : unitInterval) (ht₁ : 0 < t₁) (ht₂ : t₂ < 1) :
    Set.range (curveSpliceChord γ₁ γ₂ t₁ t₂) =
      (γ₁ '' Set.Icc 0 t₁) ∪ seg2 (γ₁ t₁) (γ₂ t₂) ∪ (γ₂ '' Set.Icc t₂ 1) := by
  ext x; constructor
  · rintro ⟨t, rfl⟩
    change (if t.1 ≤ 1 / 3 then γ₁ (clampI (3 * t.1 * t₁.1))
            else if t.1 ≤ 2 / 3 then (1 - (3 * t.1 - 1)) • γ₁ t₁ + (3 * t.1 - 1) • γ₂ t₂
            else γ₂ (clampI (t₂.1 + (3 * t.1 - 2) * (1 - t₂.1)))) ∈ _
    split_ifs with h1 h2
    · left; left
      refine ⟨clampI (3 * t.1 * t₁.1), ⟨?_, ?_⟩, rfl⟩
      · exact (clampI _).2.1
      · show (clampI (3 * t.1 * t₁.1)).1 ≤ t₁.1
        rw [clampI_of_mem (by nlinarith [t.2.1, t₁.2.1]) (by nlinarith [t.2.1, t₁.2.2])]
        nlinarith [t₁.2.1]
    · left; right
      exact ⟨3 * t.1 - 1, by linarith, by linarith, rfl⟩
    · right
      refine ⟨clampI (t₂.1 + (3 * t.1 - 2) * (1 - t₂.1)), ⟨?_, ?_⟩, rfl⟩
      · show t₂.1 ≤ (clampI _).1
        rw [clampI_of_mem (by nlinarith [t.2.2, t₂.2.1, t₂.2.2]) (by nlinarith [t.2.2, t₂.2.1, t₂.2.2])]
        nlinarith [t₂.2.2]
      · exact (clampI _).2.2
  · rintro ((⟨s, ⟨hs0, hs1⟩, rfl⟩ | ⟨u, hu0, hu1, rfl⟩) | ⟨s, ⟨hs0, hs1⟩, rfl⟩)
    · have ht1p : (0 : ℝ) < t₁.1 := ht₁
      let t : unitInterval := ⟨s.1 / (3 * t₁.1), ⟨div_nonneg s.2.1 (by linarith), by
        rw [div_le_iff₀ (by linarith)]; have : s.1 ≤ t₁.1 := hs1; linarith⟩⟩
      refine ⟨t, ?_⟩
      change (if t.1 ≤ 1 / 3 then γ₁ (clampI (3 * t.1 * t₁.1)) else _) = γ₁ s
      have hle : t.1 ≤ 1 / 3 := by
        show s.1 / (3 * t₁.1) ≤ 1 / 3
        rw [div_le_div_iff₀ (by linarith) (by norm_num)]
        have : s.1 ≤ t₁.1 := hs1; linarith
      rw [if_pos hle]
      congr 1; apply Subtype.ext
      have hmul : 3 * (s.1 / (3 * t₁.1)) * t₁.1 = s.1 := by field_simp [ht1p.ne']
      show (clampI (3 * (s.1 / (3 * t₁.1)) * t₁.1)).1 = s.1
      rw [hmul]; exact clampI_of_mem s.2.1 s.2.2
    · let t : unitInterval := ⟨(u + 1) / 3, ⟨by linarith, by linarith⟩⟩
      refine ⟨t, ?_⟩
      change (if t.1 ≤ 1 / 3 then γ₁ (clampI (3 * t.1 * t₁.1)) else if t.1 ≤ 2 / 3 then
        (1 - (3 * t.1 - 1)) • γ₁ t₁ + (3 * t.1 - 1) • γ₂ t₂ else _) = _
      by_cases hu0' : u = 0
      · subst hu0'
        rw [if_pos (by show (0 + 1 : ℝ) / 3 ≤ 1 / 3; norm_num)]
        have hc : clampI (3 * ((0 + 1 : ℝ) / 3) * t₁.1) = t₁ := by
          apply Subtype.ext; norm_num; exact clampI_of_mem t₁.2.1 t₁.2.2
        dsimp only [t]; rw [hc]; simp
      · rw [if_neg (by show ¬ ((u + 1) / 3 ≤ 1 / 3); have : 0 < u := lt_of_le_of_ne hu0 (Ne.symm hu0'); linarith),
            if_pos (by show (u + 1) / 3 ≤ 2 / 3; linarith)]
        have h3 : 3 * ((u + 1) / 3) - 1 = u := by ring
        simp [t, h3]
    · have ht2p : (0 : ℝ) < 1 - t₂.1 := by have : t₂.1 < 1 := ht₂; linarith
      let t : unitInterval := ⟨(2 + (s.1 - t₂.1) / (1 - t₂.1)) / 3, by
        have hge : 0 ≤ (s.1 - t₂.1) / (1 - t₂.1) := div_nonneg (by have : t₂.1 ≤ s.1 := hs0; linarith) ht2p.le
        have hle : (s.1 - t₂.1) / (1 - t₂.1) ≤ 1 := (div_le_one ht2p).mpr (by have := s.2.2; linarith)
        exact ⟨by linarith, by linarith⟩⟩
      refine ⟨t, ?_⟩
      change (if t.1 ≤ 1 / 3 then _ else if t.1 ≤ 2 / 3 then
        (1 - (3 * t.1 - 1)) • γ₁ t₁ + (3 * t.1 - 1) • γ₂ t₂ else
        γ₂ (clampI (t₂.1 + (3 * t.1 - 2) * (1 - t₂.1)))) = γ₂ s
      by_cases hst2 : s = t₂
      · rw [hst2]
        have htval : t.1 = 2 / 3 := by dsimp only [t]; rw [hst2]; ring
        rw [if_neg (by linarith), if_pos (by linarith), htval]; norm_num
      · have hgt : t₂.1 < s.1 := lt_of_le_of_ne hs0 (fun h => hst2 (Subtype.ext h.symm))
        have hpos_q : 0 < (s.1 - t₂.1) / (1 - t₂.1) := div_pos (by linarith) ht2p
        rw [if_neg (by show ¬ ((2 + (s.1 - t₂.1) / (1 - t₂.1)) / 3 ≤ 1 / 3); linarith),
            if_neg (by show ¬ ((2 + (s.1 - t₂.1) / (1 - t₂.1)) / 3 ≤ 2 / 3); linarith)]
        congr 1; apply Subtype.ext
        have hval : t₂.1 + (3 * ((2 + (s.1 - t₂.1) / (1 - t₂.1)) / 3) - 2) * (1 - t₂.1) = s.1 := by
          field_simp [ht2p.ne']; ring
        show (clampI _).1 = s.1
        rw [hval]; exact clampI_of_mem s.2.1 s.2.2

private lemma curveSpliceChord_inj
    {γ₁ γ₂ : C(unitInterval, EuclideanSpace ℝ (Fin 2))} {t₁ t₂ : unitInterval}
    (ht₁ : 0 < t₁) (ht₂ : t₂ < 1)
    (hinj₁ : Function.Injective γ₁) (hinj₂ : Function.Injective γ₂)
    (hne_ab : γ₁ t₁ ≠ γ₂ t₂)
    (hdisj12 : ∀ s : unitInterval, s < t₁ → γ₁ s ∉ seg2 (γ₁ t₁) (γ₂ t₂))
    (hdisj23 : ∀ s : unitInterval, t₂ < s → γ₂ s ∉ seg2 (γ₁ t₁) (γ₂ t₂))
    (hdisj13 : ∀ s₁ : unitInterval, s₁ ≤ t₁ → ∀ s₂ : unitInterval, t₂ ≤ s₂ → γ₁ s₁ ≠ γ₂ s₂) :
    Function.Injective (curveSpliceChord γ₁ γ₂ t₁ t₂) := by
  have ht1p : (0 : ℝ) < t₁.1 := ht₁
  have ht2p : (0 : ℝ) < 1 - t₂.1 := by have : t₂.1 < 1 := ht₂; linarith
  -- Helper: evaluate in the 3 regions [0, 1/3), [1/3, 2/3], (2/3, 1]
  have hmem1 : ∀ t : unitInterval, t.1 < 1 / 3 →
      ∃ s : unitInterval, s < t₁ ∧ curveSpliceChord γ₁ γ₂ t₁ t₂ t = γ₁ s ∧ s.1 = 3 * t.1 * t₁.1 := by
    intro t ht
    refine ⟨clampI (3 * t.1 * t₁.1), ?_, ?_, clampI_of_mem (by nlinarith [t.2.1, t₁.2.1]) (by nlinarith [t.2.1, t₁.2.2])⟩
    · show (clampI (3 * t.1 * t₁.1)).1 < t₁.1
      rw [clampI_of_mem (by nlinarith [t.2.1, t₁.2.1]) (by nlinarith [t.2.1, t₁.2.2])]
      nlinarith
    · change (if t.1 ≤ 1 / 3 then γ₁ (clampI (3 * t.1 * t₁.1)) else _) = _
      rw [if_pos ht.le]
  have hmem2 : ∀ t : unitInterval, 1 / 3 ≤ t.1 → t.1 ≤ 2 / 3 →
      curveSpliceChord γ₁ γ₂ t₁ t₂ t = (1 - (3 * t.1 - 1)) • γ₁ t₁ + (3 * t.1 - 1) • γ₂ t₂ := by
    intro t h1 h2
    change (if t.1 ≤ 1 / 3 then γ₁ (clampI (3 * t.1 * t₁.1))
            else if t.1 ≤ 2 / 3 then (1 - (3 * t.1 - 1)) • γ₁ t₁ + (3 * t.1 - 1) • γ₂ t₂ else _) = _
    by_cases heq : t.1 = 1 / 3
    · rw [if_pos heq.le]
      have hc : clampI (3 * t.1 * t₁.1) = t₁ := by
        apply Subtype.ext; rw [heq]; norm_num; exact clampI_of_mem t₁.2.1 t₁.2.2
      rw [hc, heq]; norm_num
    · rw [if_neg (not_le.mpr (lt_of_le_of_ne h1 (Ne.symm heq))), if_pos h2]
  have hmem3 : ∀ t : unitInterval, 2 / 3 < t.1 →
      ∃ s : unitInterval, t₂ < s ∧ curveSpliceChord γ₁ γ₂ t₁ t₂ t = γ₂ s ∧
        s.1 = t₂.1 + (3 * t.1 - 2) * (1 - t₂.1) := by
    intro t ht
    refine ⟨clampI (t₂.1 + (3 * t.1 - 2) * (1 - t₂.1)), ?_, ?_,
      clampI_of_mem (by nlinarith [t.2.2, t₂.2.1, t₂.2.2]) (by nlinarith [t.2.2, t₂.2.1, t₂.2.2])⟩
    · show t₂.1 < (clampI _).1
      rw [clampI_of_mem (by nlinarith [t.2.2, t₂.2.1, t₂.2.2]) (by nlinarith [t.2.2, t₂.2.1, t₂.2.2])]
      nlinarith
    · change (if t.1 ≤ 1 / 3 then _ else if t.1 ≤ 2 / 3 then _ else _) = _
      rw [if_neg (by linarith), if_neg (by linarith)]
  have hseg_inj : ∀ u v : ℝ, (1 - u) • γ₁ t₁ + u • γ₂ t₂ = (1 - v) • γ₁ t₁ + v • γ₂ t₂ → u = v := by
    intro u v heq
    have hdiff : (u - v) • (γ₂ t₂ - γ₁ t₁) = 0 := by
      rw [sub_smul, smul_sub, smul_sub]
      have h1 : (1 - u) • γ₁ t₁ + u • γ₂ t₂ - ((1 - v) • γ₁ t₁ + v • γ₂ t₂) = 0 := sub_eq_zero.mpr heq
      rw [sub_smul, sub_smul, one_smul] at h1
      abel_nf at h1 ⊢; exact h1
    exact sub_eq_zero.mp ((smul_eq_zero.mp hdiff).resolve_right (sub_ne_zero.mpr hne_ab.symm))
  intro x y heq
  apply Subtype.ext
  by_cases hx1 : x.1 < 1 / 3 <;> by_cases hy1 : y.1 < 1 / 3
  · obtain ⟨sx, -, hfx, hsx⟩ := hmem1 x hx1
    obtain ⟨sy, -, hfy, hsy⟩ := hmem1 y hy1
    have := congrArg Subtype.val (hinj₁ (hfx.symm.trans (heq.trans hfy)))
    nlinarith
  · obtain ⟨sx, hsx_lt, hfx, -⟩ := hmem1 x hx1
    by_cases hy2 : y.1 ≤ 2 / 3
    · exfalso
      have hfy := hmem2 y (not_lt.mp hy1) hy2
      exact hdisj12 sx hsx_lt ⟨3 * y.1 - 1, by linarith [not_lt.mp hy1], by linarith, hfx.symm.trans (heq.trans hfy)⟩
    · exfalso
      obtain ⟨sy, hsy_gt, hfy, -⟩ := hmem3 y (not_le.mp hy2)
      exact hdisj13 sx hsx_lt.le sy hsy_gt.le (hfx.symm.trans (heq.trans hfy))
  · obtain ⟨sy, hsy_lt, hfy, -⟩ := hmem1 y hy1
    by_cases hx2 : x.1 ≤ 2 / 3
    · exfalso
      have hfx := hmem2 x (not_lt.mp hx1) hx2
      exact hdisj12 sy hsy_lt ⟨3 * x.1 - 1, by linarith [not_lt.mp hx1], by linarith, hfy.symm.trans (heq.symm.trans hfx)⟩
    · exfalso
      obtain ⟨sx, hsx_gt, hfx, -⟩ := hmem3 x (not_le.mp hx2)
      exact hdisj13 sy hsy_lt.le sx hsx_gt.le (hfy.symm.trans (heq.symm.trans hfx))
  · by_cases hx2 : x.1 ≤ 2 / 3 <;> by_cases hy2 : y.1 ≤ 2 / 3
    · have hfx := hmem2 x (not_lt.mp hx1) hx2
      have hfy := hmem2 y (not_lt.mp hy1) hy2
      have := hseg_inj (3 * x.1 - 1) (3 * y.1 - 1) (hfx.symm.trans (heq.trans hfy))
      linarith
    · exfalso
      have hfx := hmem2 x (not_lt.mp hx1) hx2
      obtain ⟨sy, hsy_gt, hfy, -⟩ := hmem3 y (not_le.mp hy2)
      exact hdisj23 sy hsy_gt ⟨3 * x.1 - 1, by linarith [not_lt.mp hx1], by linarith, hfy.symm.trans (heq.symm.trans hfx)⟩
    · exfalso
      obtain ⟨sx, hsx_gt, hfx, -⟩ := hmem3 x (not_le.mp hx2)
      have hfy := hmem2 y (not_lt.mp hy1) hy2
      exact hdisj23 sx hsx_gt ⟨3 * y.1 - 1, by linarith [not_lt.mp hy1], by linarith, hfx.symm.trans (heq.trans hfy)⟩
    · obtain ⟨sx, -, hfx, hsx⟩ := hmem3 x (not_le.mp hx2)
      obtain ⟨sy, -, hfy, hsy⟩ := hmem3 y (not_le.mp hy2)
      have := congrArg Subtype.val (hinj₂ (hfx.symm.trans (heq.trans hfy)))
      nlinarith

/-- Concatenate prefix `γ₁[0..s₀]` with suffix `γ₂[u₀..1]` at a shared point `γ₁ s₀ = γ₂ u₀`. -/
private noncomputable def curveConcatAt
    (γ₁ γ₂ : C(unitInterval, EuclideanSpace ℝ (Fin 2)))
    (s₀ u₀ : unitInterval) (hmatch : γ₁ s₀ = γ₂ u₀) :
    C(unitInterval, EuclideanSpace ℝ (Fin 2)) :=
  let f₁ : unitInterval → EuclideanSpace ℝ (Fin 2) := fun t => γ₁ (clampI (2 * t.1 * s₀.1))
  let f₂ : unitInterval → EuclideanSpace ℝ (Fin 2) :=
    fun t => γ₂ (clampI (u₀.1 + (2 * t.1 - 1) * (1 - u₀.1)))
  have hf₁ : Continuous f₁ := γ₁.continuous.comp (continuous_clampI.comp (by fun_prop))
  have hf₂ : Continuous f₂ := γ₂.continuous.comp (continuous_clampI.comp (by fun_prop))
  ⟨fun t => if t.1 ≤ 1 / 2 then f₁ t else f₂ t,
    Continuous.if_le hf₁ hf₂ continuous_subtype_val continuous_const (fun t ht => by
      dsimp only [f₁, f₂]
      have h1 : clampI (2 * t.1 * s₀.1) = s₀ := by
        apply Subtype.ext; rw [ht]; norm_num; exact clampI_of_mem s₀.2.1 s₀.2.2
      have h2 : clampI (u₀.1 + (2 * t.1 - 1) * (1 - u₀.1)) = u₀ := by
        apply Subtype.ext; rw [ht]; norm_num; exact clampI_of_mem u₀.2.1 u₀.2.2
      rw [h1, h2, hmatch])⟩

private lemma curveConcatAt_zero (γ₁ γ₂ : C(unitInterval, EuclideanSpace ℝ (Fin 2)))
    (s₀ u₀ : unitInterval) (hmatch : γ₁ s₀ = γ₂ u₀) :
    curveConcatAt γ₁ γ₂ s₀ u₀ hmatch 0 = γ₁ 0 := by
  change (if (0 : ℝ) ≤ 1 / 2 then γ₁ (clampI (2 * 0 * s₀.1)) else _) = γ₁ 0
  rw [if_pos (by norm_num)]; congr 1; apply Subtype.ext; simp [clampI]

private lemma curveConcatAt_one (γ₁ γ₂ : C(unitInterval, EuclideanSpace ℝ (Fin 2)))
    (s₀ u₀ : unitInterval) (hmatch : γ₁ s₀ = γ₂ u₀) :
    curveConcatAt γ₁ γ₂ s₀ u₀ hmatch 1 = γ₂ 1 := by
  change (if (1 : ℝ) ≤ 1 / 2 then _ else γ₂ (clampI (u₀.1 + (2 * 1 - 1) * (1 - u₀.1)))) = γ₂ 1
  rw [if_neg (by norm_num)]; congr 1; apply Subtype.ext
  have : u₀.1 + (2 * 1 - 1) * (1 - u₀.1) = 1 := by ring
  rw [this]; exact clampI_of_mem zero_le_one (le_refl 1)

private lemma curveConcatAt_range (γ₁ γ₂ : C(unitInterval, EuclideanSpace ℝ (Fin 2)))
    (s₀ u₀ : unitInterval) (hmatch : γ₁ s₀ = γ₂ u₀) (hs₀ : 0 < s₀) (hu₀ : u₀ < 1) :
    Set.range (curveConcatAt γ₁ γ₂ s₀ u₀ hmatch) = (γ₁ '' Set.Icc 0 s₀) ∪ (γ₂ '' Set.Icc u₀ 1) := by
  ext x; constructor
  · rintro ⟨t, rfl⟩
    change (if t.1 ≤ 1 / 2 then γ₁ (clampI (2 * t.1 * s₀.1))
            else γ₂ (clampI (u₀.1 + (2 * t.1 - 1) * (1 - u₀.1)))) ∈ _
    split_ifs with h1
    · left
      refine ⟨clampI (2 * t.1 * s₀.1), ⟨(clampI _).2.1, ?_⟩, rfl⟩
      show (clampI (2 * t.1 * s₀.1)).1 ≤ s₀.1
      rw [clampI_of_mem (by nlinarith [t.2.1, s₀.2.1]) (by nlinarith [t.2.1, s₀.2.2])]
      nlinarith [s₀.2.1]
    · right
      refine ⟨clampI (u₀.1 + (2 * t.1 - 1) * (1 - u₀.1)), ⟨?_, (clampI _).2.2⟩, rfl⟩
      show u₀.1 ≤ (clampI _).1
      rw [clampI_of_mem (by nlinarith [t.2.2, u₀.2.1, u₀.2.2]) (by nlinarith [t.2.2, u₀.2.1, u₀.2.2])]
      nlinarith [u₀.2.2]
  · rintro (⟨s, ⟨hs0, hs1⟩, rfl⟩ | ⟨s, ⟨hs0, hs1⟩, rfl⟩)
    · have hs0p : (0 : ℝ) < s₀.1 := hs₀
      let t : unitInterval := ⟨s.1 / (2 * s₀.1), ⟨div_nonneg s.2.1 (by linarith), by
        rw [div_le_iff₀ (by linarith)]; have : s.1 ≤ s₀.1 := hs1; linarith⟩⟩
      refine ⟨t, ?_⟩
      change (if t.1 ≤ 1 / 2 then γ₁ (clampI (2 * t.1 * s₀.1)) else _) = γ₁ s
      have hle : t.1 ≤ 1 / 2 := by
        show s.1 / (2 * s₀.1) ≤ 1 / 2
        rw [div_le_div_iff₀ (by linarith) (by norm_num)]
        have : s.1 ≤ s₀.1 := hs1; linarith
      rw [if_pos hle]; congr 1; apply Subtype.ext
      have hmul : 2 * (s.1 / (2 * s₀.1)) * s₀.1 = s.1 := by field_simp [hs0p.ne']
      show (clampI _).1 = s.1; rw [hmul]; exact clampI_of_mem s.2.1 s.2.2
    · have hu0p : (0 : ℝ) < 1 - u₀.1 := by have : u₀.1 < 1 := hu₀; linarith
      by_cases hsu : s = u₀
      · rw [hsu]
        refine ⟨⟨1 / 2, by norm_num, by norm_num⟩, ?_⟩
        change (if (1 / 2 : ℝ) ≤ 1 / 2 then γ₁ (clampI (2 * (1 / 2) * s₀.1)) else _) = γ₂ u₀
        rw [if_pos le_rfl]
        have hc : clampI (2 * (1 / 2 : ℝ) * s₀.1) = s₀ := by
          apply Subtype.ext; norm_num; exact clampI_of_mem s₀.2.1 s₀.2.2
        rw [hc, hmatch]
      · have hgt : u₀.1 < s.1 := lt_of_le_of_ne hs0 (fun h => hsu (Subtype.ext h.symm))
        let t : unitInterval := ⟨(1 + (s.1 - u₀.1) / (1 - u₀.1)) / 2, by
          have hge : 0 ≤ (s.1 - u₀.1) / (1 - u₀.1) := div_nonneg (by linarith) hu0p.le
          have hle : (s.1 - u₀.1) / (1 - u₀.1) ≤ 1 := (div_le_one hu0p).mpr (by have := s.2.2; linarith)
          exact ⟨by linarith, by linarith⟩⟩
        refine ⟨t, ?_⟩
        change (if t.1 ≤ 1 / 2 then _ else γ₂ (clampI (u₀.1 + (2 * t.1 - 1) * (1 - u₀.1)))) = γ₂ s
        have hpos : 0 < (s.1 - u₀.1) / (1 - u₀.1) := div_pos (by linarith) hu0p
        rw [if_neg (by show ¬ ((1 + (s.1 - u₀.1) / (1 - u₀.1)) / 2 ≤ 1 / 2); linarith)]
        congr 1; apply Subtype.ext
        have hval : u₀.1 + (2 * ((1 + (s.1 - u₀.1) / (1 - u₀.1)) / 2) - 1) * (1 - u₀.1) = s.1 := by
          field_simp [hu0p.ne']; ring
        show (clampI _).1 = s.1; rw [hval]; exact clampI_of_mem s.2.1 s.2.2

private lemma curveConcatAt_inj
    {γ₁ γ₂ : C(unitInterval, EuclideanSpace ℝ (Fin 2))} {s₀ u₀ : unitInterval}
    (hmatch : γ₁ s₀ = γ₂ u₀) (hs₀ : 0 < s₀) (hu₀ : u₀ < 1)
    (hinj₁ : Function.Injective γ₁) (hinj₂ : Function.Injective γ₂)
    (hdisj : ∀ s : unitInterval, s < s₀ → ∀ u : unitInterval, u₀ ≤ u → γ₁ s ≠ γ₂ u) :
    Function.Injective (curveConcatAt γ₁ γ₂ s₀ u₀ hmatch) := by
  have hs0p : (0 : ℝ) < s₀.1 := hs₀
  have hu0p : (0 : ℝ) < 1 - u₀.1 := by have : u₀.1 < 1 := hu₀; linarith
  intro x y heq
  apply Subtype.ext
  change (if x.1 ≤ 1 / 2 then γ₁ (clampI (2 * x.1 * s₀.1)) else γ₂ (clampI (u₀.1 + (2 * x.1 - 1) * (1 - u₀.1)))) =
         (if y.1 ≤ 1 / 2 then γ₁ (clampI (2 * y.1 * s₀.1)) else γ₂ (clampI (u₀.1 + (2 * y.1 - 1) * (1 - u₀.1)))) at heq
  split_ifs at heq with hx hy hy
  · have h1 := congrArg Subtype.val (hinj₁ heq)
    rw [clampI_of_mem (by nlinarith [x.2.1, s₀.2.1]) (by nlinarith [x.2.1, s₀.2.2]),
        clampI_of_mem (by nlinarith [y.2.1, s₀.2.1]) (by nlinarith [y.2.1, s₀.2.2])] at h1
    nlinarith
  · exfalso
    by_cases hx_eq : x.1 = 1 / 2
    · have hcx : clampI (2 * x.1 * s₀.1) = s₀ := by
        apply Subtype.ext; rw [hx_eq]; norm_num; exact clampI_of_mem s₀.2.1 s₀.2.2
      rw [hcx, hmatch] at heq
      have h1 := congrArg Subtype.val (hinj₂ heq)
      rw [clampI_of_mem (by nlinarith [y.2.2, u₀.2.1, u₀.2.2]) (by nlinarith [y.2.2, u₀.2.1, u₀.2.2])] at h1
      nlinarith
    · have hs_lt : clampI (2 * x.1 * s₀.1) < s₀ := by
        show (clampI (2 * x.1 * s₀.1)).1 < s₀.1
        rw [clampI_of_mem (by nlinarith [x.2.1, s₀.2.1]) (by nlinarith [x.2.1, s₀.2.2])]
        have hxlt : x.1 < 1 / 2 := lt_of_le_of_ne hx hx_eq
        nlinarith
      have hu_ge : u₀ ≤ clampI (u₀.1 + (2 * y.1 - 1) * (1 - u₀.1)) := by
        show u₀.1 ≤ (clampI _).1
        rw [clampI_of_mem (by nlinarith [y.2.2, u₀.2.1, u₀.2.2]) (by nlinarith [y.2.2, u₀.2.1, u₀.2.2])]
        nlinarith
      exact hdisj _ hs_lt _ hu_ge heq
  · exfalso
    by_cases hy_eq : y.1 = 1 / 2
    · have hcy : clampI (2 * y.1 * s₀.1) = s₀ := by
        apply Subtype.ext; rw [hy_eq]; norm_num; exact clampI_of_mem s₀.2.1 s₀.2.2
      rw [hcy, hmatch] at heq
      have h1 := congrArg Subtype.val (hinj₂ heq)
      rw [clampI_of_mem (by nlinarith [x.2.2, u₀.2.1, u₀.2.2]) (by nlinarith [x.2.2, u₀.2.1, u₀.2.2])] at h1
      nlinarith
    · have hs_lt : clampI (2 * y.1 * s₀.1) < s₀ := by
        show (clampI (2 * y.1 * s₀.1)).1 < s₀.1
        rw [clampI_of_mem (by nlinarith [y.2.1, s₀.2.1]) (by nlinarith [y.2.1, s₀.2.2])]
        have hylt : y.1 < 1 / 2 := lt_of_le_of_ne hy hy_eq
        nlinarith
      have hu_ge : u₀ ≤ clampI (u₀.1 + (2 * x.1 - 1) * (1 - u₀.1)) := by
        show u₀.1 ≤ (clampI _).1
        rw [clampI_of_mem (by nlinarith [x.2.2, u₀.2.1, u₀.2.2]) (by nlinarith [x.2.2, u₀.2.1, u₀.2.2])]
        nlinarith
      exact hdisj _ hs_lt _ hu_ge heq.symm
  · have h1 := congrArg Subtype.val (hinj₂ heq)
    rw [clampI_of_mem (by nlinarith [x.2.2, u₀.2.1, u₀.2.2]) (by nlinarith [x.2.2, u₀.2.1, u₀.2.2]),
        clampI_of_mem (by nlinarith [y.2.2, u₀.2.1, u₀.2.2]) (by nlinarith [y.2.2, u₀.2.1, u₀.2.2])] at h1
    nlinarith

/-- Set-cardinality comparison via union and intersection inclusion. -/
private lemma ncard_add_le_of_union_inter {α : Type*} {X₁' X₂' X₁ X₂ : Set α}
    (h1 : X₁.Finite) (h2 : X₂.Finite)
    (hun : X₁' ∪ X₂' ⊆ X₁ ∪ X₂) (hin : X₁' ∩ X₂' ⊆ X₁ ∩ X₂) :
    X₁'.ncard + X₂'.ncard ≤ X₁.ncard + X₂.ncard := by
  have h1' : X₁'.Finite := (h1.union h2).subset (Set.subset_union_left.trans hun)
  have h2' : X₂'.Finite := (h1.union h2).subset (Set.subset_union_right.trans hun)
  have hL := Set.ncard_union_add_ncard_inter X₁' X₂' h1' h2'
  have hR := Set.ncard_union_add_ncard_inter X₁ X₂ h1 h2
  have hle1 : (X₁' ∪ X₂').ncard ≤ (X₁ ∪ X₂).ncard := Set.ncard_le_ncard hun (h1.union h2)
  have hle2 : (X₁' ∩ X₂').ncard ≤ (X₁ ∩ X₂).ncard := Set.ncard_le_ncard hin (h1.inter_of_left X₂)
  omega

/-- Split a finite set's `ncard` across a ball `B`: `S.ncard = (S \ B).ncard + (S ∩ B).ncard`. -/
private lemma ncard_split_ball {α : Type*} {S B : Set α} (hS : S.Finite) :
    S.ncard = (S \ B).ncard + (S ∩ B).ncard := by
  have hdisj : Disjoint (S \ B) (S ∩ B) := by
    rw [Set.disjoint_left]; intro x h1 h2; exact h1.2 h2.2
  rw [← Set.ncard_union_eq hdisj hS.sdiff (hS.inter_of_left B), Set.sdiff_union_inter]

private lemma ncard_le_one_of_subsingleton {α : Type*} {S : Set α} (hS : S.Subsingleton) :
    S.ncard ≤ 1 := by
  rcases hS.eq_empty_or_singleton with rfl | ⟨a, rfl⟩
  · simp
  · simp

/-- Single step of adjacent-crossing elimination: if two distinct edges sharing a vertex intersect
outside `A`, we can strictly decrease `totalCrossings` by at least 2. -/
private lemma adjacent_crossing_step
    (A : Finset (EuclideanSpace ℝ (Fin 2))) (E : Finset ℕ) (D : CurveDrawing A E)
    {i₁ i₂ : ℕ} (hi₁ : i₁ ∈ E) (hi₂ : i₂ ∈ E) (h12 : i₁ ≠ i₂)
    (hadj : D.γ i₁ 0 = D.γ i₂ 0 ∨ D.γ i₁ 0 = D.γ i₂ 1 ∨ D.γ i₁ 1 = D.γ i₂ 0 ∨ D.γ i₁ 1 = D.γ i₂ 1)
    (hcr : ((Set.range (D.γ i₁) ∩ Set.range (D.γ i₂)) \ (A : Set _)).Nonempty) :
    ∃ D' : CurveDrawing A E, totalCrossings D' + 2 ≤ totalCrossings D := by
  classical
  -- Step 1: First re-orient i₁ and i₂ so that γ i₁ 0 = γ i₂ 0!
  suffices hsame0 : ∀ (D0 : CurveDrawing A E),
      D0.γ i₁ 0 = D0.γ i₂ 0 →
      ((Set.range (D0.γ i₁) ∩ Set.range (D0.γ i₂)) \ (A : Set _)).Nonempty →
      ∃ D' : CurveDrawing A E, totalCrossings D' + 2 ≤ totalCrossings D0 by
    let rev₁ : Bool := decide (D.γ i₁ 1 = D.γ i₂ 0 ∨ D.γ i₁ 1 = D.γ i₂ 1)
    let rev₂ : Bool := decide ((if rev₁ then D.γ i₁ 1 else D.γ i₁ 0) = D.γ i₂ 1)
    let γ0 (k : ℕ) : C(unitInterval, EuclideanSpace ℝ (Fin 2)) :=
      if k = i₁ then (if rev₁ then curveReverse (D.γ i₁) else D.γ i₁)
      else if k = i₂ then (if rev₂ then curveReverse (D.γ i₂) else D.γ i₂)
      else D.γ k
    have hrange0 : ∀ k, Set.range (γ0 k) = Set.range (D.γ k) := by
      intro k; dsimp only [γ0]
      split_ifs with h1 h2 h3 h4
      · subst h1; exact curveReverse_range _
      · subst h1; rfl
      · subst h3; exact curveReverse_range _
      · subst h3; rfl
      · rfl
    have hends0 : ∀ k, ({γ0 k 0, γ0 k 1} : Finset _) = {D.γ k 0, D.γ k 1} := by
      intro k; dsimp only [γ0]
      split_ifs with h1 h2 h3 h4
      · subst h1; simp [curveReverse_apply, Finset.pair_comm]
      · subst h1; rfl
      · subst h3; simp [curveReverse_apply, Finset.pair_comm]
      · subst h3; rfl
      · rfl
    have hD0_inj : ∀ k ∈ E, Function.Injective (γ0 k) := by
      intro k hk; dsimp only [γ0]
      split_ifs
      · exact curveReverse_inj (D.hinj i₁ hi₁)
      · exact D.hinj i₁ hi₁
      · exact curveReverse_inj (D.hinj i₂ hi₂)
      · exact D.hinj i₂ hi₂
      · exact D.hinj k hk
    have hD0_ends : ∀ k ∈ E, γ0 k 0 ∈ A ∧ γ0 k 1 ∈ A := by
      intro k hk
      have hmem : ∀ x ∈ ({γ0 k 0, γ0 k 1} : Finset _), x ∈ A := by
        rw [hends0 k]; intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl; exact D.h0 k hk; exact D.h1 k hk
      exact ⟨hmem _ (Finset.mem_insert_self _ _), hmem _ (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))⟩
    have hD0_int : ∀ k ∈ E, ∀ t : unitInterval, 0 < t → t < 1 → γ0 k t ∉ A := by
      intro k hk t h0 h1
      have hsymm : 0 < unitInterval.symm t ∧ unitInterval.symm t < 1 := by
        constructor
        · show (0 : ℝ) < 1 - t.1; have : t.1 < 1 := h1; linarith
        · show 1 - t.1 < (1 : ℝ); have : 0 < t.1 := h0; linarith
      dsimp only [γ0]
      split_ifs
      · exact D.hint i₁ hi₁ _ hsymm.1 hsymm.2
      · exact D.hint i₁ hi₁ t h0 h1
      · exact D.hint i₂ hi₂ _ hsymm.1 hsymm.2
      · exact D.hint i₂ hi₂ t h0 h1
      · exact D.hint k hk t h0 h1
    let D0 : CurveDrawing A E :=
      { γ := γ0
        hinj := hD0_inj
        h0 := fun k hk => (hD0_ends k hk).1
        h1 := fun k hk => (hD0_ends k hk).2
        hint := hD0_int
        hsimple := fun a ha b hb heq => by
          apply D.hsimple ha hb; dsimp only; rw [← hends0 a, ← hends0 b]; exact heq
        hfin := fun a ha b hb hne => by
          rw [hrange0 a, hrange0 b]; exact D.hfin a ha b hb hne }
    have hX0 : totalCrossings D0 = totalCrossings D := by
      dsimp only [totalCrossings, D0]
      apply Finset.sum_congr rfl; intro a _
      apply Finset.sum_congr rfl; intro b _
      rw [hrange0 a, hrange0 b]
    have h0eq : D0.γ i₁ 0 = D0.γ i₂ 0 := by
      dsimp only [D0, γ0]
      rw [if_pos rfl, if_neg h12.symm, if_pos rfl]
      by_cases hr1 : D.γ i₁ 1 = D.γ i₂ 0 ∨ D.γ i₁ 1 = D.γ i₂ 1
      · have hrv1 : rev₁ = true := decide_eq_true hr1
        simp only [hrv1, ↓reduceIte, curveReverse_apply, unitInterval.symm_zero]
        rcases hr1 with h1 | h2
        · by_cases h2' : D.γ i₁ 1 = D.γ i₂ 1
          · exfalso; exact curveDrawing_ends_ne D hi₂ (h1.symm.trans h2')
          · have hrv2 : rev₂ = false := by dsimp only [rev₂]; simp [hrv1, h2']
            simp [hrv2, h1]
        · have hrv2 : rev₂ = true := by dsimp only [rev₂]; simp [hrv1, h2]
          simp [hrv2, curveReverse_apply, h2]
      · have hrv1 : rev₁ = false := decide_eq_false hr1
        simp only [hrv1, Bool.false_eq_true, ↓reduceIte]
        have h0or : D.γ i₁ 0 = D.γ i₂ 0 ∨ D.γ i₁ 0 = D.γ i₂ 1 := by tauto
        rcases h0or with h1 | h2
        · by_cases h2' : D.γ i₁ 0 = D.γ i₂ 1
          · exfalso; exact curveDrawing_ends_ne D hi₂ (h1.symm.trans h2')
          · have hrv2 : rev₂ = false := by dsimp only [rev₂]; simp [hrv1, h2']
            simp [hrv2, h1]
        · have hrv2 : rev₂ = true := by dsimp only [rev₂]; simp [hrv1, h2]
          simp [hrv2, curveReverse_apply, h2]
    obtain ⟨D', hlt⟩ := hsame0 D0 h0eq (by dsimp only [D0]; rw [hrange0 i₁, hrange0 i₂]; exact hcr)
    exact ⟨D', hX0 ▸ hlt⟩
  -- Now assume D.γ i₁ 0 = D.γ i₂ 0!
  clear hadj hcr D
  intro D h0eq hcr
  have h1ne : D.γ i₁ 1 ≠ D.γ i₂ 1 := by
    intro heq
    apply h12
    apply D.hsimple hi₁ hi₂
    dsimp only; rw [h0eq, heq]
  -- Step 2: Pick the FIRST interior intersection p = D.γ i₁ t₁ = D.γ i₂ t₂ minimizing t₁!
  let I12 : Set (EuclideanSpace ℝ (Fin 2)) := (Set.range (D.γ i₁) ∩ Set.range (D.γ i₂)) \ (A : Set _)
  have hI12_fin : I12.Finite := D.hfin i₁ hi₁ i₂ hi₂ h12
  let T12 : Finset unitInterval :=
    hI12_fin.toFinset.image (fun x => if h : x ∈ Set.range (D.γ i₁) then h.choose else 0)
  have hT12_ne : T12.Nonempty := by
    obtain ⟨x, hx⟩ := hcr
    exact ⟨_, Finset.mem_image_of_mem _ (hI12_fin.mem_toFinset.mpr hx)⟩
  obtain ⟨t₁, ht₁_mem, ht₁_min⟩ := Finset.exists_min_image T12 id hT12_ne
  obtain ⟨p, hp_fin, hp_t₁⟩ := Finset.mem_image.mp ht₁_mem
  have hp_I12 : p ∈ I12 := hI12_fin.mem_toFinset.mp hp_fin
  have hp_r1 : p ∈ Set.range (D.γ i₁) := hp_I12.1.1
  have hp_r2 : p ∈ Set.range (D.γ i₂) := hp_I12.1.2
  have hp_nA : p ∉ (A : Set _) := hp_I12.2
  have hp_eq1 : D.γ i₁ t₁ = p := by
    rw [← hp_t₁, dif_pos hp_r1]; exact hp_r1.choose_spec
  have ⟨t₂, hp_eq2⟩ := hp_r2
  have ht₁_int : 0 < t₁ ∧ t₁ < 1 := by
    constructor
    · exact lt_of_le_of_ne t₁.2.1 (fun h => hp_nA (hp_eq1 ▸ h ▸ D.h0 i₁ hi₁))
    · exact lt_of_le_of_ne t₁.2.2 (fun h => hp_nA (hp_eq1 ▸ h ▸ D.h1 i₁ hi₁))
  have ht₂_int : 0 < t₂ ∧ t₂ < 1 := by
    constructor
    · exact lt_of_le_of_ne t₂.2.1 (fun h => hp_nA (hp_eq2 ▸ h ▸ D.h0 i₂ hi₂))
    · exact lt_of_le_of_ne t₂.2.2 (fun h => hp_nA (hp_eq2 ▸ h ▸ D.h1 i₂ hi₂))
  have ht₁_first : ∀ s : unitInterval, 0 < s → s < t₁ → D.γ i₁ s ∉ Set.range (D.γ i₂) := by
    intro s hs0 hst hmem2
    have hsnA : D.γ i₁ s ∉ (A : Set _) := D.hint i₁ hi₁ s hs0 (hst.trans ht₁_int.2)
    have hI : D.γ i₁ s ∈ I12 := ⟨⟨⟨s, rfl⟩, hmem2⟩, hsnA⟩
    have hs_in : s ∈ T12 := by
      refine Finset.mem_image.mpr ⟨D.γ i₁ s, hI12_fin.mem_toFinset.mpr hI, ?_⟩
      have hr : D.γ i₁ s ∈ Set.range (D.γ i₁) := ⟨s, rfl⟩
      rw [dif_pos hr]; exact D.hinj i₁ hi₁ hr.choose_spec
    exact not_lt.mpr (ht₁_min s hs_in) hst
  -- Step 3: Let H = {k ∈ E | p ∈ range (γ k)}, choose small ε > 0 isolating B̄(p, ε)
  let H : Finset ℕ := E.filter (fun k => p ∈ Set.range (D.γ k))
  have hi₁H : i₁ ∈ H := Finset.mem_filter.mpr ⟨hi₁, hp_r1⟩
  have hi₂H : i₂ ∈ H := Finset.mem_filter.mpr ⟨hi₂, hp_r2⟩
  -- Collect all bad sets disjoint from {p}: A, range(γ k) for k ∈ E \ H, and other intersections!
  let KnonH : Set (EuclideanSpace ℝ (Fin 2)) :=
    (A : Set _) ∪ ⋃ k ∈ (E \ H), Set.range (D.γ k)
  let Kother : Set (EuclideanSpace ℝ (Fin 2)) :=
    ⋃ k ∈ E, ⋃ m ∈ E.erase k, ((Set.range (D.γ k) ∩ Set.range (D.γ m)) \ (A : Set _)) \ {p}
  have hKnonH_comp : IsCompact KnonH :=
    A.finite_toSet.isCompact.union (Finset.isCompact_biUnion _ fun k _ => isCompact_range (D.γ k).continuous)
  have hKother_fin : Kother.Finite :=
    E.finite_toSet.biUnion fun k hk => (E.erase k).finite_toSet.biUnion fun m hm =>
      (D.hfin k hk m (Finset.mem_erase.mp hm).2 (Finset.mem_erase.mp hm).1.symm).sdiff
  have hK_comp : IsCompact (KnonH ∪ Kother) := hKnonH_comp.union hKother_fin.isCompact
  have hK_disj : Disjoint ({p} : Set _) (KnonH ∪ Kother) := by
    rw [Set.disjoint_singleton_left]
    rintro ((hpA | hmem_nonH) | hmem_other)
    · exact hp_nA hpA
    · simp only [Set.mem_iUnion, Finset.mem_sdiff] at hmem_nonH
      obtain ⟨k, ⟨hkE, hknH⟩, hpr⟩ := hmem_nonH
      exact hknH (Finset.mem_filter.mpr ⟨hkE, hpr⟩)
    · simp only [Kother, Set.mem_iUnion, Set.mem_sdiff, Set.mem_singleton_iff, not_true_eq_false,
        and_false, exists_false] at hmem_other
  obtain ⟨d0, hd0, hd0_sep⟩ := exists_pos_dist_of_disjoint_compact isCompact_singleton hK_comp hK_disj
  let ε : ℝ := d0 / 2
  have hε_pos : 0 < ε := by dsimp only [ε]; linarith
  let B : Set (EuclideanSpace ℝ (Fin 2)) := Metric.closedBall p ε
  have hB_disj_A : ∀ w ∈ A, w ∉ B := fun w hw hB => by
    have h1 := hd0_sep p rfl w (Or.inl (Or.inl hw))
    have h2 : dist w p ≤ ε := hB
    rw [_root_.dist_comm] at h2; dsimp only [ε] at h2; linarith
  have hB_disj_nonH : ∀ k ∈ E, k ∉ H → ∀ x ∈ Set.range (D.γ k), x ∉ B := fun k hk hknH x hx hB => by
    have h1 := hd0_sep p rfl x (Or.inl (Or.inr (Set.mem_biUnion (Finset.mem_sdiff.mpr ⟨hk, hknH⟩) hx)))
    have h2 : dist x p ≤ ε := hB
    rw [_root_.dist_comm] at h2; dsimp only [ε] at h2; linarith
  have hB_no_other : ∀ k ∈ E, ∀ m ∈ E, k ≠ m → ∀ x,
      x ∈ Set.range (D.γ k) → x ∈ Set.range (D.γ m) → x ∈ B → x = p := by
    intro k hk m hm hne x hxk hxm hxB
    by_contra hxp
    have hxnA : x ∉ (A : Set _) := fun hA => hB_disj_A x hA hxB
    have hmem : x ∈ Kother := by
      refine Set.mem_biUnion hk (Set.mem_biUnion (Finset.mem_erase.mpr ⟨hne.symm, hm⟩) ?_)
      exact ⟨⟨⟨hxk, hxm⟩, hxnA⟩, hxp⟩
    have h1 := hd0_sep p rfl x (Or.inr hmem)
    have h2 : dist x p ≤ ε := hxB
    rw [_root_.dist_comm] at h2; dsimp only [ε] at h2; linarith
  -- Step 4: For every k ∈ H, find first entry t⁻ k and last exit t⁺ k of D.γ k in B̄(p, ε)
  have hex_pm : ∀ k ∈ H, ∃ (tM tP : unitInterval),
      0 < tM ∧ tM < tP ∧ tP < 1 ∧
      dist (D.γ k tM) p = ε ∧ dist (D.γ k tP) p = ε ∧
      (∀ t : unitInterval, t < tM → ε < dist (D.γ k t) p) ∧
      (∀ t : unitInterval, tP < t → ε < dist (D.γ k t) p) ∧
      (∀ t : unitInterval, D.γ k t = p → tM < t ∧ t < tP) := by
    intro k hk
    have hkE : k ∈ E := (Finset.mem_filter.mp hk).1
    obtain ⟨tk, htk⟩ := (Finset.mem_filter.mp hk).2
    let S : Set unitInterval := {t | dist (D.γ k t) p ≤ ε}
    have hS_cl : IsClosed S :=
      isClosed_le (continuous_dist.comp ((D.γ k).continuous.prodMk continuous_const)) continuous_const
    have hS_ne : S.Nonempty := ⟨tk, by simp [S, htk, hε_pos.le]⟩
    obtain ⟨tM, htM_S, htM_min⟩ := hS_cl.isCompact.exists_isMinOn hS_ne continuous_id.continuousOn
    obtain ⟨tP, htP_S, htP_max⟩ := hS_cl.isCompact.exists_isMaxOn hS_ne continuous_id.continuousOn
    have h0_out : ε < dist (D.γ k 0) p := by
      have := hB_disj_A (D.γ k 0) (D.h0 k hkE); exact not_le.mp this
    have h1_out : ε < dist (D.γ k 1) p := by
      have := hB_disj_A (D.γ k 1) (D.h1 k hkE); exact not_le.mp this
    have htM_pos : 0 < tM := lt_of_le_of_ne tM.2.1 (fun h => by
      have : dist (D.γ k 0) p ≤ ε := h ▸ htM_S; linarith)
    have htP_lt1 : tP < 1 := lt_of_le_of_ne tP.2.2 (fun h => by
      have : dist (D.γ k 1) p ≤ ε := h ▸ htP_S; linarith)
    have htM_lt : ∀ t : unitInterval, t < tM → ε < dist (D.γ k t) p := fun t h => by
      by_contra hle; push Not at hle; exact not_lt.mpr (htM_min hle) h
    have htP_gt : ∀ t : unitInterval, tP < t → ε < dist (D.γ k t) p := fun t h => by
      by_contra hle; push Not at hle; exact not_lt.mpr (htP_max hle) h
    have htM_dist : dist (D.γ k tM) p = ε := by
      apply le_antisymm htM_S
      by_contra hlt; push Not at hlt
      have hopen : IsOpen {t : unitInterval | dist (D.γ k t) p < ε} :=
        isOpen_lt (continuous_dist.comp ((D.γ k).continuous.prodMk continuous_const)) continuous_const
      obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hopen.mem_nhds hlt)
      have hpos : 0 < tM.1 := htM_pos
      have hm0 : 0 < min (r / 2) (tM.1 / 2) := lt_min (by linarith) (by linarith)
      have hm1 : min (r / 2) (tM.1 / 2) ≤ r / 2 := min_le_left _ _
      have hm2 : min (r / 2) (tM.1 / 2) ≤ tM.1 / 2 := min_le_right _ _
      let t : unitInterval := ⟨tM.1 - min (r / 2) (tM.1 / 2), ⟨by linarith, by have := tM.2.2; linarith⟩⟩
      have htb : t ∈ Metric.ball tM r := by
        rw [Metric.mem_ball, Subtype.dist_eq, Real.dist_eq]
        have hsub : t.1 - tM.1 = -min (r / 2) (tM.1 / 2) := by dsimp only [t]; ring
        rw [hsub, abs_neg, abs_of_pos hm0]; linarith
      exact not_lt.mpr (htM_lt t (show t.1 < tM.1 by dsimp only [t]; linarith)).le (hball htb)
    have htP_dist : dist (D.γ k tP) p = ε := by
      apply le_antisymm htP_S
      by_contra hlt; push Not at hlt
      have hopen : IsOpen {t : unitInterval | dist (D.γ k t) p < ε} :=
        isOpen_lt (continuous_dist.comp ((D.γ k).continuous.prodMk continuous_const)) continuous_const
      obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hopen.mem_nhds hlt)
      have hlt1 : tP.1 < 1 := htP_lt1
      have hm0 : 0 < min (r / 2) ((1 - tP.1) / 2) := lt_min (by linarith) (by linarith)
      have hm1 : min (r / 2) ((1 - tP.1) / 2) ≤ r / 2 := min_le_left _ _
      have hm2 : min (r / 2) ((1 - tP.1) / 2) ≤ (1 - tP.1) / 2 := min_le_right _ _
      let t : unitInterval := ⟨tP.1 + min (r / 2) ((1 - tP.1) / 2), ⟨by have := tP.2.1; linarith, by linarith⟩⟩
      have htb : t ∈ Metric.ball tP r := by
        rw [Metric.mem_ball, Subtype.dist_eq, Real.dist_eq]
        have hsub : t.1 - tP.1 = min (r / 2) ((1 - tP.1) / 2) := by dsimp only [t]; ring
        rw [hsub, abs_of_pos hm0]; linarith
      exact not_lt.mpr (htP_gt t (show tP.1 < t.1 by dsimp only [t]; linarith)).le (hball htb)
    have htk_between : ∀ t : unitInterval, D.γ k t = p → tM < t ∧ t < tP := by
      intro t ht
      have htS : t ∈ S := by simp [S, ht, hε_pos.le]
      constructor
      · exact lt_of_le_of_ne (htM_min htS) (fun h => by
          have : dist (D.γ k t) p = ε := h ▸ htM_dist
          rw [ht, _root_.dist_self] at this; linarith)
      · exact lt_of_le_of_ne (htP_max htS) (fun h => by
          have : dist (D.γ k t) p = ε := h ▸ htP_dist
          rw [ht, _root_.dist_self] at this; linarith)
    have htMP : tM < tP := (htk_between tk htk).1.trans (htk_between tk htk).2
    exact ⟨tM, tP, htM_pos, htMP, htP_lt1, htM_dist, htP_dist, htM_lt, htP_gt, htk_between⟩
  let tM (k : ℕ) : unitInterval := if h : k ∈ H then (hex_pm k h).choose else 0
  let tP (k : ℕ) : unitInterval := if h : k ∈ H then (hex_pm k h).choose_spec.choose else 1
  have hpm_spec : ∀ k ∈ H,
      0 < tM k ∧ tM k < tP k ∧ tP k < 1 ∧
      dist (D.γ k (tM k)) p = ε ∧ dist (D.γ k (tP k)) p = ε ∧
      (∀ t : unitInterval, t < tM k → ε < dist (D.γ k t) p) ∧
      (∀ t : unitInterval, tP k < t → ε < dist (D.γ k t) p) ∧
      (∀ t : unitInterval, D.γ k t = p → tM k < t ∧ t < tP k) := by
    intro k hk; dsimp only [tM, tP]; rw [dif_pos hk, dif_pos hk]
    exact (hex_pm k hk).choose_spec.choose_spec
  let aPt (k : ℕ) := D.γ k (tM k)
  let bPt (k : ℕ) := D.γ k (tP k)
  -- All 2*|H| sphere points {aPt k, bPt k | k ∈ H} are pairwise distinct!
  have hab_ne : ∀ k ∈ H, aPt k ≠ bPt k := fun k hk h => by
    have hkE := (Finset.mem_filter.mp hk).1
    exact (hpm_spec k hk).2.1.ne (D.hinj k hkE h)
  have hpts_disj : ∀ k ∈ H, ∀ m ∈ H, k ≠ m →
      aPt k ≠ aPt m ∧ aPt k ≠ bPt m ∧ bPt k ≠ aPt m ∧ bPt k ≠ bPt m := by
    intro k hk m hm hne
    have hkE := (Finset.mem_filter.mp hk).1
    have hmE := (Finset.mem_filter.mp hm).1
    have hsp_k := hpm_spec k hk
    have hsp_m := hpm_spec m hm
    refine ⟨?_, ?_, ?_, ?_⟩ <;> intro heq
    · have hp' := hB_no_other k hkE m hmE hne (aPt k) ⟨tM k, rfl⟩ ⟨tM m, heq.symm⟩ hsp_k.2.2.2.1.le
      have hdist : dist (aPt k) p = ε := hsp_k.2.2.2.1
      rw [hp', _root_.dist_self] at hdist; linarith
    · have hp' := hB_no_other k hkE m hmE hne (aPt k) ⟨tM k, rfl⟩ ⟨tP m, heq.symm⟩ hsp_k.2.2.2.1.le
      have hdist : dist (aPt k) p = ε := hsp_k.2.2.2.1
      rw [hp', _root_.dist_self] at hdist; linarith
    · have hp' := hB_no_other k hkE m hmE hne (bPt k) ⟨tP k, rfl⟩ ⟨tM m, heq.symm⟩ hsp_k.2.2.2.2.1.le
      have hdist : dist (bPt k) p = ε := hsp_k.2.2.2.2.1
      rw [hp', _root_.dist_self] at hdist; linarith
    · have hp' := hB_no_other k hkE m hmE hne (bPt k) ⟨tP k, rfl⟩ ⟨tP m, heq.symm⟩ hsp_k.2.2.2.2.1.le
      have hdist : dist (bPt k) p = ε := hsp_k.2.2.2.2.1
      rw [hp', _root_.dist_self] at hdist; linarith
  -- Helper: standard chord-shortcut for any k ∈ H
  have hshort_ok : ∀ k ∈ H,
      let γk := curveSpliceChord (D.γ k) (D.γ k) (tM k) (tP k)
      Function.Injective γk ∧
      γk 0 = D.γ k 0 ∧ γk 1 = D.γ k 1 ∧
      (∀ t : unitInterval, 0 < t → t < 1 → γk t ∉ A) ∧
      Set.range γk \ B ⊆ Set.range (D.γ k) \ B ∧
      Set.range γk ∩ B = seg2 (aPt k) (bPt k) := by
    intro k hk
    have hkE := (Finset.mem_filter.mp hk).1
    have hsp := hpm_spec k hk
    have hrange := curveSpliceChord_range (D.γ k) (D.γ k) (tM k) (tP k) hsp.1 hsp.2.2.1
    have hch_B : seg2 (aPt k) (bPt k) ⊆ B :=
      fun _ hx => dist_seg2_le hsp.2.2.2.1.le hsp.2.2.2.2.1.le hx
    have hinj : Function.Injective (curveSpliceChord (D.γ k) (D.γ k) (tM k) (tP k)) := by
      apply curveSpliceChord_inj hsp.1 hsp.2.2.1 (D.hinj k hkE) (D.hinj k hkE) (hab_ne k hk)
      · intro s hs hmem
        have h1 := hsp.2.2.2.2.2.1 s hs
        have h2 : dist (D.γ k s) p ≤ ε := hch_B hmem
        linarith
      · intro s hs hmem
        have h1 := hsp.2.2.2.2.2.2.1 s hs
        have h2 : dist (D.γ k s) p ≤ ε := hch_B hmem
        linarith
      · intro s₁ hs₁ s₂ hs₂ heq
        have hss := D.hinj k hkE heq
        subst hss
        exact not_lt.mpr (hs₂.trans hs₁) hsp.2.1
    refine ⟨hinj, curveSpliceChord_zero _ _ _ _, curveSpliceChord_one _ _ _ _, ?_, ?_, ?_⟩
    · intro t h0 h1 hA
      have hmem : curveSpliceChord (D.γ k) (D.γ k) (tM k) (tP k) t ∈ Set.range (curveSpliceChord (D.γ k) (D.γ k) (tM k) (tP k)) := ⟨t, rfl⟩
      rw [hrange] at hmem
      rcases hmem with (⟨s, ⟨_, hs1⟩, heq⟩ | hseg) | ⟨s, ⟨hs0, _⟩, heq⟩
      · have hs0' : s = 0 := by
          by_contra hne
          exact D.hint k hkE s (lt_of_le_of_ne s.2.1 (Ne.symm hne)) (lt_of_le_of_lt hs1 (hsp.2.1.trans hsp.2.2.1)) (heq ▸ hA)
        subst hs0'
        exact h0.ne' (hinj (heq.symm.trans (curveSpliceChord_zero _ _ _ _).symm))
      · exact hB_disj_A _ hA (hch_B hseg)
      · have hs1' : s = 1 := by
          by_contra hne
          exact D.hint k hkE s (lt_of_lt_of_le (hsp.1.trans hsp.2.1) hs0) (lt_of_le_of_ne s.2.2 hne) (heq ▸ hA)
        subst hs1'
        exact h1.ne (hinj (heq.symm.trans (curveSpliceChord_one _ _ _ _).symm))
    · rintro x ⟨hx, hxnB⟩
      rw [hrange] at hx
      rcases hx with (⟨s, _, rfl⟩ | hseg) | ⟨s, _, rfl⟩
      · exact ⟨⟨s, rfl⟩, hxnB⟩
      · exact (hxnB (hch_B hseg)).elim
      · exact ⟨⟨s, rfl⟩, hxnB⟩
    · ext x; constructor
      · rintro ⟨hx, hxB⟩
        rw [hrange] at hx
        rcases hx with (⟨s, ⟨_, hs1⟩, rfl⟩ | hseg) | ⟨s, ⟨hs0, _⟩, rfl⟩
        · have hs_eq : s = tM k := le_antisymm hs1 (by
            by_contra hlt; push Not at hlt
            exact not_lt.mpr hxB (hsp.2.2.2.2.2.1 s hlt))
          subst hs_eq; exact ⟨0, le_refl _, zero_le_one, by simp [aPt]⟩
        · exact hseg
        · have hs_eq : s = tP k := le_antisymm (by
            by_contra hlt; push Not at hlt
            exact not_lt.mpr hxB (hsp.2.2.2.2.2.2.1 s hlt)) hs0
          subst hs_eq; exact ⟨1, zero_le_one, le_refl _, by simp [bPt]⟩
      · intro hseg
        exact ⟨by rw [hrange]; exact Or.inl (Or.inr hseg), hch_B hseg⟩
  -- Apply 4-point circle chord lemma to aPt i₁, bPt i₁, aPt i₂, bPt i₂!
  have hsp1 := hpm_spec i₁ hi₁H
  have hsp2 := hpm_spec i₂ hi₂H
  have hsp1_lt : ∀ t : unitInterval, t < tM i₁ → ε < dist (D.γ i₁ t) p := hsp1.2.2.2.2.2.1
  have hsp1_gt : ∀ t : unitInterval, tP i₁ < t → ε < dist (D.γ i₁ t) p := hsp1.2.2.2.2.2.2.1
  have hsp2_lt : ∀ t : unitInterval, t < tM i₂ → ε < dist (D.γ i₂ t) p := hsp2.2.2.2.2.2.1
  have hsp2_gt : ∀ t : unitInterval, tP i₂ < t → ε < dist (D.γ i₂ t) p := hsp2.2.2.2.2.2.2.1
  obtain ⟨haa, hab12, hba21, hbb⟩ := hpts_disj i₁ hi₁H i₂ hi₂H h12
  rcases four_point_circle_chords hε_pos hsp1.2.2.2.1 hsp1.2.2.2.2.1 hsp2.2.2.2.1 hsp2.2.2.2.2.1
      (hab_ne i₁ hi₁H) haa hab12 hba21 hbb (hab_ne i₂ hi₂H) with hUncross | hSwap
  · -- OPTION A: [a₁, b₁] ∩ [a₂, b₂] = ∅! Shortcut every k ∈ H to [a_k, b_k]!
    let γ' (k : ℕ) : C(unitInterval, EuclideanSpace ℝ (Fin 2)) :=
      if k ∈ H then curveSpliceChord (D.γ k) (D.γ k) (tM k) (tP k) else D.γ k
    have hγ'_range_out : ∀ k ∈ E, Set.range (γ' k) \ B ⊆ Set.range (D.γ k) \ B := by
      intro k hk; dsimp only [γ']; split_ifs with hkH
      · exact (hshort_ok k hkH).2.2.2.2.1
      · exact Set.Subset.rfl
    have hγ'_range_in : ∀ k ∈ E, Set.range (γ' k) ∩ B = if k ∈ H then seg2 (aPt k) (bPt k) else ∅ := by
      intro k hk; dsimp only [γ']; split_ifs with hkH
      · exact (hshort_ok k hkH).2.2.2.2.2
      · ext x; simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false]
        rintro ⟨hx, hxB⟩; exact hB_disj_nonH k hk hkH x hx hxB
    have hpair_fin : ∀ k ∈ E, ∀ m ∈ E, k ≠ m →
        ((Set.range (γ' k) ∩ Set.range (γ' m)) \ (A : Set _)).Finite := by
      intro k hk m hm hne
      have hsub : (Set.range (γ' k) ∩ Set.range (γ' m)) \ (A : Set _) ⊆
          ((Set.range (D.γ k) ∩ Set.range (D.γ m)) \ (A : Set _)) ∪
          ((Set.range (γ' k) ∩ B) ∩ (Set.range (γ' m) ∩ B)) := by
        intro x ⟨⟨hxk, hxm⟩, hxnA⟩
        by_cases hxB : x ∈ B
        · exact Or.inr ⟨⟨hxk, hxB⟩, ⟨hxm, hxB⟩⟩
        · exact Or.inl ⟨⟨(hγ'_range_out k hk ⟨hxk, hxB⟩).1, (hγ'_range_out m hm ⟨hxm, hxB⟩).1⟩, hxnA⟩
      have hin_fin : ((Set.range (γ' k) ∩ B) ∩ (Set.range (γ' m) ∩ B)).Finite := by
        rw [hγ'_range_in k hk, hγ'_range_in m hm]
        split_ifs with hkH hmH
        · obtain ⟨d1, d2, d3, d4⟩ := hpts_disj k hkH m hmH hne
          exact (two_circle_chords_inter_subsingleton
            (hpm_spec k hkH).2.2.2.1 (hpm_spec k hkH).2.2.2.2.1
            (hpm_spec m hmH).2.2.2.1 (hpm_spec m hmH).2.2.2.2.1
            (hab_ne k hkH) d1 d2 d3 d4 (hab_ne m hmH)).finite
        · simp
        · simp
        · simp
      exact ((D.hfin k hk m hm hne).union hin_fin).subset hsub
    let D' : CurveDrawing A E :=
      { γ := γ'
        hinj := fun k hk => by dsimp only [γ']; split_ifs with hkH; exact (hshort_ok k hkH).1; exact D.hinj k hk
        h0 := fun k hk => by dsimp only [γ']; split_ifs with hkH; rw [(hshort_ok k hkH).2.1]; exact D.h0 k hk; exact D.h0 k hk
        h1 := fun k hk => by dsimp only [γ']; split_ifs with hkH; rw [(hshort_ok k hkH).2.2.1]; exact D.h1 k hk; exact D.h1 k hk
        hint := fun k hk t h0 h1 => by
          dsimp only [γ']; split_ifs with hkH; exact (hshort_ok k hkH).2.2.2.1 t h0 h1; exact D.hint k hk t h0 h1
        hsimple := fun a ha b hb heq => by
          apply D.hsimple ha hb
          have ha0 : γ' a 0 = D.γ a 0 := by dsimp only [γ']; split_ifs with h; exact (hshort_ok a h).2.1; rfl
          have ha1 : γ' a 1 = D.γ a 1 := by dsimp only [γ']; split_ifs with h; exact (hshort_ok a h).2.2.1; rfl
          have hb0 : γ' b 0 = D.γ b 0 := by dsimp only [γ']; split_ifs with h; exact (hshort_ok b h).2.1; rfl
          have hb1 : γ' b 1 = D.γ b 1 := by dsimp only [γ']; split_ifs with h; exact (hshort_ok b h).2.2.1; rfl
          dsimp only at heq
          rwa [ha0, ha1, hb0, hb1] at heq
        hfin := hpair_fin }
    -- Compare every pair (k, m): c' k m ≤ c k m, and for {i₁, i₂} strictly drops by ≥ 1!
    have hpair_le : ∀ k ∈ E, ∀ m ∈ E, k ≠ m →
        ((Set.range (γ' k) ∩ Set.range (γ' m)) \ (A : Set _)).ncard ≤
        ((Set.range (D.γ k) ∩ Set.range (D.γ m)) \ (A : Set _)).ncard := by
      intro k hk m hm hne
      rw [ncard_split_ball (B := B) (hpair_fin k hk m hm hne),
          ncard_split_ball (B := B) (D.hfin k hk m hm hne)]
      have hout : (((Set.range (γ' k) ∩ Set.range (γ' m)) \ (A : Set _)) \ B).ncard ≤
          (((Set.range (D.γ k) ∩ Set.range (D.γ m)) \ (A : Set _)) \ B).ncard := by
        apply Set.ncard_le_ncard _ (D.hfin k hk m hm hne).sdiff
        rintro x ⟨⟨⟨hxk, hxm⟩, hxnA⟩, hxnB⟩
        exact ⟨⟨⟨(hγ'_range_out k hk ⟨hxk, hxnB⟩).1, (hγ'_range_out m hm ⟨hxm, hxnB⟩).1⟩, hxnA⟩, hxnB⟩
      have hin : (((Set.range (γ' k) ∩ Set.range (γ' m)) \ (A : Set _)) ∩ B).ncard ≤
          (((Set.range (D.γ k) ∩ Set.range (D.γ m)) \ (A : Set _)) ∩ B).ncard := by
        by_cases hkmH : k ∈ H ∧ m ∈ H
        · have hsub1 : ((Set.range (γ' k) ∩ Set.range (γ' m)) \ (A : Set _)) ∩ B ⊆
              seg2 (aPt k) (bPt k) ∩ seg2 (aPt m) (bPt m) := by
            rintro x ⟨⟨⟨hxk, hxm⟩, _⟩, hxB⟩
            have h1 : x ∈ Set.range (γ' k) ∩ B := ⟨hxk, hxB⟩
            have h2 : x ∈ Set.range (γ' m) ∩ B := ⟨hxm, hxB⟩
            rw [hγ'_range_in k hk, if_pos hkmH.1] at h1
            rw [hγ'_range_in m hm, if_pos hkmH.2] at h2
            exact ⟨h1, h2⟩
          obtain ⟨d1, d2, d3, d4⟩ := hpts_disj k hkmH.1 m hkmH.2 hne
          have hsub_ss := (two_circle_chords_inter_subsingleton
            (hpm_spec k hkmH.1).2.2.2.1 (hpm_spec k hkmH.1).2.2.2.2.1
            (hpm_spec m hkmH.2).2.2.2.1 (hpm_spec m hkmH.2).2.2.2.2.1
            (hab_ne k hkmH.1) d1 d2 d3 d4 (hab_ne m hkmH.2)).anti hsub1
          have hle1 : (((Set.range (γ' k) ∩ Set.range (γ' m)) \ (A : Set _)) ∩ B).ncard ≤ 1 :=
            ncard_le_one_of_subsingleton hsub_ss
          have hge1 : 1 ≤ (((Set.range (D.γ k) ∩ Set.range (D.γ m)) \ (A : Set _)) ∩ B).ncard := by
            have hp_in : p ∈ ((Set.range (D.γ k) ∩ Set.range (D.γ m)) \ (A : Set _)) ∩ B :=
              ⟨⟨⟨(Finset.mem_filter.mp hkmH.1).2, (Finset.mem_filter.mp hkmH.2).2⟩, hp_nA⟩,
                Metric.mem_closedBall_self hε_pos.le⟩
            exact Set.ncard_pos ((D.hfin k hk m hm hne).inter_of_left B) |>.mpr ⟨p, hp_in⟩
          omega
        · have hemp : ((Set.range (γ' k) ∩ Set.range (γ' m)) \ (A : Set _)) ∩ B = ∅ := by
            ext x; simp only [Set.mem_inter_iff, Set.mem_sdiff, Set.mem_empty_iff_false, iff_false]
            rintro ⟨⟨⟨hxk, hxm⟩, _⟩, hxB⟩
            by_cases hkH : k ∈ H
            · have hmH : m ∉ H := fun h => hkmH ⟨hkH, h⟩
              have h2 : x ∈ Set.range (γ' m) ∩ B := ⟨hxm, hxB⟩
              rw [hγ'_range_in m hm, if_neg hmH] at h2; exact h2
            · have h1 : x ∈ Set.range (γ' k) ∩ B := ⟨hxk, hxB⟩
              rw [hγ'_range_in k hk, if_neg hkH] at h1; exact h1
          rw [hemp, Set.ncard_empty]; exact Nat.zero_le _
      omega
    have hpair_drop : ∀ k m, (k = i₁ ∧ m = i₂) ∨ (k = i₂ ∧ m = i₁) →
        ((Set.range (γ' k) ∩ Set.range (γ' m)) \ (A : Set _)).ncard + 1 ≤
        ((Set.range (D.γ k) ∩ Set.range (D.γ m)) \ (A : Set _)).ncard := by
      intro k m hkm
      have hkE : k ∈ E := by rcases hkm with ⟨hk, _⟩ | ⟨hk, _⟩ <;> rw [hk] <;> assumption
      have hmE : m ∈ E := by rcases hkm with ⟨_, hm⟩ | ⟨_, hm⟩ <;> rw [hm] <;> assumption
      have hne : k ≠ m := by rcases hkm with ⟨hk, hm⟩ | ⟨hk, hm⟩ <;> rw [hk, hm]; exact h12; exact h12.symm
      rw [ncard_split_ball (B := B) (hpair_fin k hkE m hmE hne),
          ncard_split_ball (B := B) (D.hfin k hkE m hmE hne)]
      have hout : (((Set.range (γ' k) ∩ Set.range (γ' m)) \ (A : Set _)) \ B).ncard ≤
          (((Set.range (D.γ k) ∩ Set.range (D.γ m)) \ (A : Set _)) \ B).ncard := by
        apply Set.ncard_le_ncard _ (D.hfin k hkE m hmE hne).sdiff
        rintro x ⟨⟨⟨hxk, hxm⟩, hxnA⟩, hxnB⟩
        exact ⟨⟨⟨(hγ'_range_out k hkE ⟨hxk, hxnB⟩).1, (hγ'_range_out m hmE ⟨hxm, hxnB⟩).1⟩, hxnA⟩, hxnB⟩
      have hin0 : ((Set.range (γ' k) ∩ Set.range (γ' m)) \ (A : Set _)) ∩ B = ∅ := by
        ext x; simp only [Set.mem_inter_iff, Set.mem_sdiff, Set.mem_empty_iff_false, iff_false]
        rintro ⟨⟨⟨hxk, hxm⟩, _⟩, hxB⟩
        rcases hkm with ⟨hk, hm⟩ | ⟨hk, hm⟩
        · rw [hk] at hxk; rw [hm] at hxm
          have h1 : x ∈ seg2 (aPt i₁) (bPt i₁) := by
            have : x ∈ Set.range (γ' i₁) ∩ B := ⟨hxk, hxB⟩
            rwa [hγ'_range_in i₁ hi₁, if_pos hi₁H] at this
          have h2 : x ∈ seg2 (aPt i₂) (bPt i₂) := by
            have : x ∈ Set.range (γ' i₂) ∩ B := ⟨hxm, hxB⟩
            rwa [hγ'_range_in i₂ hi₂, if_pos hi₂H] at this
          exact (hUncross ▸ ⟨h1, h2⟩ : x ∈ (∅ : Set _))
        · rw [hk] at hxk; rw [hm] at hxm
          have h1 : x ∈ seg2 (aPt i₂) (bPt i₂) := by
            have : x ∈ Set.range (γ' i₂) ∩ B := ⟨hxk, hxB⟩
            rwa [hγ'_range_in i₂ hi₂, if_pos hi₂H] at this
          have h2 : x ∈ seg2 (aPt i₁) (bPt i₁) := by
            have : x ∈ Set.range (γ' i₁) ∩ B := ⟨hxm, hxB⟩
            rwa [hγ'_range_in i₁ hi₁, if_pos hi₁H] at this
          exact (hUncross ▸ ⟨h2, h1⟩ : x ∈ (∅ : Set _))
      have hge1 : 1 ≤ (((Set.range (D.γ k) ∩ Set.range (D.γ m)) \ (A : Set _)) ∩ B).ncard := by
        have hp_in : p ∈ ((Set.range (D.γ k) ∩ Set.range (D.γ m)) \ (A : Set _)) ∩ B := by
          refine ⟨⟨⟨?_, ?_⟩, hp_nA⟩, Metric.mem_closedBall_self hε_pos.le⟩
          · rcases hkm with ⟨hk, _⟩ | ⟨hk, _⟩ <;> rw [hk]; exact hp_r1; exact hp_r2
          · rcases hkm with ⟨_, hm⟩ | ⟨_, hm⟩ <;> rw [hm]; exact hp_r2; exact hp_r1
        exact (Set.ncard_pos ((D.hfin k hkE m hmE hne).inter_of_left B)).mpr ⟨p, hp_in⟩
      rw [hin0, Set.ncard_empty]; omega
    refine ⟨D', ?_⟩
    -- Sum drop over E × E
    let c (k m : ℕ) := ((Set.range (D.γ k) ∩ Set.range (D.γ m)) \ (A : Set _)).ncard
    let c' (k m : ℕ) := ((Set.range (γ' k) ∩ Set.range (γ' m)) \ (A : Set _)).ncard
    have hrow : ∀ k ∈ E, (∑ m ∈ E.erase k, c' k m) + (if k = i₁ ∨ k = i₂ then 1 else 0) ≤
        ∑ m ∈ E.erase k, c k m := by
      intro k hk
      split_ifs with hk12
      · rcases hk12 with hk1 | hk2
        · rw [hk1]
          have hi2_er : i₂ ∈ E.erase i₁ := Finset.mem_erase.mpr ⟨h12.symm, hi₂⟩
          rw [← Finset.add_sum_erase _ _ hi2_er, ← Finset.add_sum_erase _ _ hi2_er]
          have hd : c' i₁ i₂ + 1 ≤ c i₁ i₂ := hpair_drop i₁ i₂ (Or.inl ⟨rfl, rfl⟩)
          have hrest : ∑ m ∈ (E.erase i₁).erase i₂, c' i₁ m ≤ ∑ m ∈ (E.erase i₁).erase i₂, c i₁ m :=
            Finset.sum_le_sum fun m hm => hpair_le i₁ hi₁ m (Finset.mem_erase.mp (Finset.mem_erase.mp hm).2).2
              (Finset.mem_erase.mp (Finset.mem_erase.mp hm).2).1.symm
          omega
        · rw [hk2]
          have hi1_er : i₁ ∈ E.erase i₂ := Finset.mem_erase.mpr ⟨h12, hi₁⟩
          rw [← Finset.add_sum_erase _ _ hi1_er, ← Finset.add_sum_erase _ _ hi1_er]
          have hd : c' i₂ i₁ + 1 ≤ c i₂ i₁ := hpair_drop i₂ i₁ (Or.inr ⟨rfl, rfl⟩)
          have hrest : ∑ m ∈ (E.erase i₂).erase i₁, c' i₂ m ≤ ∑ m ∈ (E.erase i₂).erase i₁, c i₂ m :=
            Finset.sum_le_sum fun m hm => hpair_le i₂ hi₂ m (Finset.mem_erase.mp (Finset.mem_erase.mp hm).2).2
              (Finset.mem_erase.mp (Finset.mem_erase.mp hm).2).1.symm
          omega
      · rw [add_zero]
        exact Finset.sum_le_sum fun m hm => hpair_le k hk m (Finset.mem_erase.mp hm).2 (Finset.mem_erase.mp hm).1.symm
    have hsum := Finset.sum_le_sum hrow
    rw [Finset.sum_add_distrib] at hsum
    have h2 : ∑ k ∈ E, (if k = i₁ ∨ k = i₂ then (1 : ℕ) else 0) = 2 := by
      rw [← Finset.card_filter]
      have hf : E.filter (fun k => k = i₁ ∨ k = i₂) = {i₁, i₂} := by
        ext k; simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · exact And.right
        · rintro (rfl | rfl); exact ⟨hi₁, Or.inl rfl⟩; exact ⟨hi₂, Or.inr rfl⟩
      rw [hf, Finset.card_pair h12]
    rw [h2] at hsum
    exact hsum
  · -- OPTION B: [a₁, b₂] ∩ [a₂, b₁] = ∅! Swap prefixes/tails of i₁, i₂ across B̄(p, ε)!
    -- First build γ'₂ = γ₁[0..tM i₁] ++ [a₁, b₂] ++ γ₂[tP i₂..1] (automatically injective!)
    let γ₂' := curveSpliceChord (D.γ i₁) (D.γ i₂) (tM i₁) (tP i₂)
    have hch12_B : seg2 (aPt i₁) (bPt i₂) ⊆ B :=
      fun _ hx => dist_seg2_le hsp1.2.2.2.1.le hsp2.2.2.2.2.1.le hx
    have hγ₂'_range := curveSpliceChord_range (D.γ i₁) (D.γ i₂) (tM i₁) (tP i₂) hsp1.1 hsp2.2.2.1
    have hγ₂'_inj : Function.Injective γ₂' := by
      apply curveSpliceChord_inj hsp1.1 hsp2.2.2.1 (D.hinj i₁ hi₁) (D.hinj i₂ hi₂) hab12
      · intro s hs hmem
        have h1 := hsp1_lt s hs
        have h2 : dist (D.γ i₁ s) p ≤ ε := hch12_B hmem
        linarith
      · intro s hs hmem
        have h1 := hsp2_gt s hs
        have h2 : dist (D.γ i₂ s) p ≤ ε := hch12_B hmem
        linarith
      · intro s₁ hs₁ s₂ hs₂ heq
        by_cases hs10 : s₁ = 0
        · subst hs10
          have : D.γ i₂ 0 = D.γ i₂ s₂ := h0eq.symm.trans heq
          have : (0 : unitInterval) = s₂ := D.hinj i₂ hi₂ this
          exact (hsp2.1.trans hsp2.2.1).not_ge (this ▸ hs₂)
        · have hs1_lt : s₁ < t₁ := lt_of_le_of_lt hs₁ (hsp1.2.2.2.2.2.2.2 t₁ hp_eq1).1
          exact ht₁_first s₁ (lt_of_le_of_ne s₁.2.1 (Ne.symm hs10)) hs1_lt ⟨s₂, heq.symm⟩
    have hγ₂'_0 : γ₂' 0 = D.γ i₂ 0 := (curveSpliceChord_zero _ _ _ _).trans h0eq
    have hγ₂'_1 : γ₂' 1 = D.γ i₂ 1 := curveSpliceChord_one _ _ _ _
    have hγ₂'_int : ∀ t : unitInterval, 0 < t → t < 1 → γ₂' t ∉ A := by
      intro t h0 h1 hA
      have hmem : γ₂' t ∈ Set.range γ₂' := ⟨t, rfl⟩
      rw [hγ₂'_range] at hmem
      rcases hmem with (⟨s, ⟨_, hs1⟩, heq⟩ | hseg) | ⟨s, ⟨hs0, _⟩, heq⟩
      · have hs0' : s = 0 := by
          by_contra hne
          exact D.hint i₁ hi₁ s (lt_of_le_of_ne s.2.1 (Ne.symm hne)) (lt_of_le_of_lt hs1 (hsp1.2.1.trans hsp1.2.2.1)) (heq ▸ hA)
        subst hs0'
        exact h0.ne' (hγ₂'_inj (heq.symm.trans (curveSpliceChord_zero _ _ _ _).symm))
      · exact hB_disj_A _ hA (hch12_B hseg)
      · have hs1' : s = 1 := by
          by_contra hne
          exact D.hint i₂ hi₂ s (lt_of_lt_of_le (hsp2.1.trans hsp2.2.1) hs0) (lt_of_le_of_ne s.2.2 hne) (heq ▸ hA)
        subst hs1'
        exact h1.ne (hγ₂'_inj (heq.symm.trans (curveSpliceChord_one _ _ _ _).symm))
    have hγ₂'_inB : Set.range γ₂' ∩ B = seg2 (aPt i₁) (bPt i₂) := by
      ext x; constructor
      · rintro ⟨hx, hxB⟩; rw [hγ₂'_range] at hx
        rcases hx with (⟨s, ⟨_, hs1⟩, rfl⟩ | hseg) | ⟨s, ⟨hs0, _⟩, rfl⟩
        · have hs_eq : s = tM i₁ := le_antisymm hs1 (by
            by_contra hlt; push Not at hlt; exact not_lt.mpr hxB (hsp1_lt s hlt))
          subst hs_eq; exact ⟨0, le_refl _, zero_le_one, by simp [aPt]⟩
        · exact hseg
        · have hs_eq : s = tP i₂ := le_antisymm (by
            by_contra hlt; push Not at hlt; exact not_lt.mpr hxB (hsp2_gt s hlt)) hs0
          subst hs_eq; exact ⟨1, zero_le_one, le_refl _, by simp [bPt]⟩
      · intro hseg; exact ⟨by rw [hγ₂'_range]; exact Or.inl (Or.inr hseg), hch12_B hseg⟩
    -- Next build γ'₁: either shortcut γ₂[0..s₀] ++ γ₁[u₀..1] if self-intersection exists, else splice chord [a₂, b₁]!
    have hγ₁'_ex : ∃ γ₁' : C(unitInterval, EuclideanSpace ℝ (Fin 2)),
        Function.Injective γ₁' ∧ γ₁' 0 = D.γ i₁ 0 ∧ γ₁' 1 = D.γ i₁ 1 ∧
        (∀ t : unitInterval, 0 < t → t < 1 → γ₁' t ∉ A) ∧
        Set.range γ₁' \ B ⊆ (D.γ i₂ '' Set.Icc 0 (tM i₂)) ∪ (D.γ i₁ '' Set.Icc (tP i₁) 1) ∧
        Set.range γ₁' ∩ B ⊆ seg2 (aPt i₂) (bPt i₁) := by
      let Sself : Set (EuclideanSpace ℝ (Fin 2)) :=
        (D.γ i₂ '' Set.Icc 0 (tM i₂)) ∩ (D.γ i₁ '' Set.Icc (tP i₁) 1)
      by_cases hself : Sself.Nonempty
      · -- Self-intersection exists: excise loop at minimum s₀ along γ₂!
        have hSself_sub : Sself ⊆ I12 := by
          rintro x ⟨⟨s, ⟨_, hs1⟩, rfl⟩, ⟨u, ⟨hu0, _⟩, hu_eq⟩⟩
          refine ⟨⟨⟨u, hu_eq⟩, ⟨s, rfl⟩⟩, fun hA => ?_⟩
          by_cases hs0 : s = 0
          · subst hs0
            have : D.γ i₁ u = D.γ i₁ 0 := hu_eq.trans h0eq.symm
            exact (hsp1.1.trans hsp1.2.1).not_ge (D.hinj i₁ hi₁ this ▸ hu0)
          · exact D.hint i₂ hi₂ s (lt_of_le_of_ne s.2.1 (Ne.symm hs0))
              (lt_of_le_of_lt hs1 (hsp2.2.1.trans hsp2.2.2.1)) hA
        have hSself_fin : Sself.Finite := hI12_fin.subset hSself_sub
        let Ts : Finset unitInterval :=
          hSself_fin.toFinset.image (fun x => if h : x ∈ Set.range (D.γ i₂) then h.choose else 0)
        have hTs_ne : Ts.Nonempty := by
          obtain ⟨x, hx⟩ := hself
          exact ⟨_, Finset.mem_image_of_mem _ (hSself_fin.mem_toFinset.mpr hx)⟩
        obtain ⟨s₀, hs₀_mem, hs₀_min⟩ := Finset.exists_min_image Ts id hTs_ne
        obtain ⟨q, hq_fin, hq_s₀⟩ := Finset.mem_image.mp hs₀_mem
        have hq_S : q ∈ Sself := hSself_fin.mem_toFinset.mp hq_fin
        have hq_r2 : q ∈ Set.range (D.γ i₂) := by rcases hq_S.1 with ⟨s, _, rfl⟩; exact ⟨s, rfl⟩
        have hq_eq2 : D.γ i₂ s₀ = q := by rw [← hq_s₀, dif_pos hq_r2]; exact hq_r2.choose_spec
        obtain ⟨s', ⟨_, hs'1⟩, hs'_eq⟩ := hq_S.1
        have hs₀_le : s₀ ≤ tM i₂ := by
          have : s₀ = s' := D.hinj i₂ hi₂ (hq_eq2.trans hs'_eq.symm); exact this ▸ hs'1
        obtain ⟨u₀, ⟨hu₀_ge, _⟩, hu₀_eq⟩ := hq_S.2
        have hmatch : D.γ i₂ s₀ = D.γ i₁ u₀ := hq_eq2.trans hu₀_eq.symm
        have hq_nA : q ∉ (A : Set _) := (hSself_sub hq_S).2
        have hs₀_pos : 0 < s₀ := lt_of_le_of_ne s₀.2.1 (fun h => hq_nA (hq_eq2 ▸ h ▸ D.h0 i₂ hi₂))
        have hu₀_lt1 : u₀ < 1 := lt_of_le_of_ne u₀.2.2 (fun h => hq_nA (hu₀_eq ▸ h ▸ D.h1 i₁ hi₁))
        have hs₀_lt : s₀ < tM i₂ := lt_of_le_of_ne hs₀_le (fun h => by
          have ha2_eq : aPt i₂ = D.γ i₁ u₀ := by dsimp only [aPt]; rw [← h]; exact hmatch
          have hp' := hB_no_other i₂ hi₂ i₁ hi₁ h12.symm (aPt i₂) ⟨tM i₂, rfl⟩ ⟨u₀, ha2_eq.symm⟩ hsp2.2.2.2.1.le
          have hdist : dist (aPt i₂) p = ε := hsp2.2.2.2.1
          rw [hp', _root_.dist_self] at hdist; linarith)
        have hu₀_gt : tP i₁ < u₀ := lt_of_le_of_ne hu₀_ge (fun h => by
          have hb1_eq : bPt i₁ = D.γ i₂ s₀ := by dsimp only [bPt]; rw [h]; exact hmatch.symm
          have hp' := hB_no_other i₁ hi₁ i₂ hi₂ h12 (bPt i₁) ⟨tP i₁, rfl⟩ ⟨s₀, hb1_eq.symm⟩ hsp1.2.2.2.2.1.le
          have hdist : dist (bPt i₁) p = ε := hsp1.2.2.2.2.1
          rw [hp', _root_.dist_self] at hdist; linarith)
        have hdisj_su : ∀ s : unitInterval, s < s₀ → ∀ u : unitInterval, u₀ ≤ u → D.γ i₂ s ≠ D.γ i₁ u := by
          intro s hs u hu heq
          have hmemS : D.γ i₂ s ∈ Sself := ⟨⟨s, ⟨s.2.1, hs.le.trans hs₀_le⟩, rfl⟩, ⟨u, ⟨hu₀_ge.trans hu, u.2.2⟩, heq.symm⟩⟩
          have hs_in : s ∈ Ts := by
            refine Finset.mem_image.mpr ⟨D.γ i₂ s, hSself_fin.mem_toFinset.mpr hmemS, ?_⟩
            have hr : D.γ i₂ s ∈ Set.range (D.γ i₂) := ⟨s, rfl⟩
            rw [dif_pos hr]; exact D.hinj i₂ hi₂ hr.choose_spec
          exact not_lt.mpr (hs₀_min s hs_in) hs
        let γ₁' := curveConcatAt (D.γ i₂) (D.γ i₁) s₀ u₀ hmatch
        have hinj₁' := curveConcatAt_inj hmatch hs₀_pos hu₀_lt1 (D.hinj i₂ hi₂) (D.hinj i₁ hi₁) hdisj_su
        have hrange₁' := curveConcatAt_range (D.γ i₂) (D.γ i₁) s₀ u₀ hmatch hs₀_pos hu₀_lt1
        refine ⟨γ₁', hinj₁', (curveConcatAt_zero _ _ _ _ _).trans h0eq.symm, curveConcatAt_one _ _ _ _ _, ?_, ?_, ?_⟩
        · intro t h0 h1 hA
          have hmem : γ₁' t ∈ Set.range γ₁' := ⟨t, rfl⟩
          rw [hrange₁'] at hmem
          rcases hmem with ⟨s, ⟨_, hs1⟩, heq⟩ | ⟨u, ⟨hu0, _⟩, heq⟩
          · have hs0' : s = 0 := by
              by_contra hne
              exact D.hint i₂ hi₂ s (lt_of_le_of_ne s.2.1 (Ne.symm hne))
                (lt_of_le_of_lt (hs1.trans hs₀_le) (hsp2.2.1.trans hsp2.2.2.1)) (heq ▸ hA)
            subst hs0'
            exact h0.ne' (hinj₁' (heq.symm.trans (curveConcatAt_zero _ _ _ _ _).symm))
          · have hu1' : u = 1 := by
              by_contra hne
              exact D.hint i₁ hi₁ u (lt_of_lt_of_le (hsp1.1.trans hsp1.2.1) (hu₀_ge.trans hu0))
                (lt_of_le_of_ne u.2.2 hne) (heq ▸ hA)
            subst hu1'
            exact h1.ne (hinj₁' (heq.symm.trans (curveConcatAt_one _ _ _ _ _).symm))
        · rintro x ⟨hx, _⟩
          rw [hrange₁'] at hx
          rcases hx with ⟨s, ⟨hs0, hs1⟩, rfl⟩ | ⟨u, ⟨hu0, hu1⟩, rfl⟩
          · exact Or.inl ⟨s, ⟨hs0, hs1.trans hs₀_le⟩, rfl⟩
          · exact Or.inr ⟨u, ⟨hu₀_ge.trans hu0, hu1⟩, rfl⟩
        · rintro x ⟨hx, hxB⟩
          exfalso; rw [hrange₁'] at hx
          rcases hx with ⟨s, ⟨_, hs1⟩, rfl⟩ | ⟨u, ⟨hu0, _⟩, rfl⟩
          · exact not_lt.mpr hxB (hsp2_lt s (lt_of_le_of_lt hs1 hs₀_lt))
          · exact not_lt.mpr hxB (hsp1_gt u (lt_of_lt_of_le hu₀_gt hu0))
      · -- No self-intersection: splice chord [a₂, b₁]!
        rw [Set.not_nonempty_iff_eq_empty] at hself
        let γ₁' := curveSpliceChord (D.γ i₂) (D.γ i₁) (tM i₂) (tP i₁)
        have hch21_B : seg2 (aPt i₂) (bPt i₁) ⊆ B :=
          fun _ hx => dist_seg2_le hsp2.2.2.2.1.le hsp1.2.2.2.2.1.le hx
        have hrange₁' := curveSpliceChord_range (D.γ i₂) (D.γ i₁) (tM i₂) (tP i₁) hsp2.1 hsp1.2.2.1
        have hinj₁' : Function.Injective γ₁' := by
          apply curveSpliceChord_inj hsp2.1 hsp1.2.2.1 (D.hinj i₂ hi₂) (D.hinj i₁ hi₁) hba21.symm
          · intro s hs hmem
            exact not_lt.mpr (hch21_B hmem) (hsp2_lt s hs)
          · intro s hs hmem
            exact not_lt.mpr (hch21_B hmem) (hsp1_gt s hs)
          · intro s₁ hs₁ s₂ hs₂ heq
            have hmem : D.γ i₂ s₁ ∈ Sself := ⟨⟨s₁, ⟨s₁.2.1, hs₁⟩, rfl⟩, ⟨s₂, ⟨hs₂, s₂.2.2⟩, heq.symm⟩⟩
            rw [hself] at hmem; exact hmem
        refine ⟨γ₁', hinj₁', (curveSpliceChord_zero _ _ _ _).trans h0eq.symm, curveSpliceChord_one _ _ _ _, ?_, ?_, ?_⟩
        · intro t h0 h1 hA
          have hmem : γ₁' t ∈ Set.range γ₁' := ⟨t, rfl⟩
          rw [hrange₁'] at hmem
          rcases hmem with (⟨s, ⟨_, hs1⟩, heq⟩ | hseg) | ⟨s, ⟨hs0, _⟩, heq⟩
          · have hs0' : s = 0 := by
              by_contra hne
              exact D.hint i₂ hi₂ s (lt_of_le_of_ne s.2.1 (Ne.symm hne)) (lt_of_le_of_lt hs1 (hsp2.2.1.trans hsp2.2.2.1)) (heq ▸ hA)
            subst hs0'
            exact h0.ne' (hinj₁' (heq.symm.trans (curveSpliceChord_zero _ _ _ _).symm))
          · exact hB_disj_A _ hA (hch21_B hseg)
          · have hs1' : s = 1 := by
              by_contra hne
              exact D.hint i₁ hi₁ s (lt_of_lt_of_le (hsp1.1.trans hsp1.2.1) hs0) (lt_of_le_of_ne s.2.2 hne) (heq ▸ hA)
            subst hs1'
            exact h1.ne (hinj₁' (heq.symm.trans (curveSpliceChord_one _ _ _ _).symm))
        · rintro x ⟨hx, hxnB⟩
          rw [hrange₁'] at hx
          rcases hx with (h1 | hseg) | h2
          · exact Or.inl h1
          · exact (hxnB (hch21_B hseg)).elim
          · exact Or.inr h2
        · rintro x ⟨hx, hxB⟩
          rw [hrange₁'] at hx
          rcases hx with (⟨s, ⟨_, hs1⟩, rfl⟩ | hseg) | ⟨s, ⟨hs0, _⟩, rfl⟩
          · have hs_eq : s = tM i₂ := le_antisymm hs1 (by
              by_contra hlt; push Not at hlt; exact not_lt.mpr hxB (hsp2_lt s hlt))
            subst hs_eq; exact ⟨0, le_refl _, zero_le_one, by simp [aPt]⟩
          · exact hseg
          · have hs_eq : s = tP i₁ := le_antisymm (by
              by_contra hlt; push Not at hlt; exact not_lt.mpr hxB (hsp1_gt s hlt)) hs0
            subst hs_eq; exact ⟨1, zero_le_one, le_refl _, by simp [bPt]⟩
    obtain ⟨γ₁', hγ₁'_inj, hγ₁'_0, hγ₁'_1, hγ₁'_int, hγ₁'_out, hγ₁'_in⟩ := hγ₁'_ex
    have hγ₂'_out : Set.range γ₂' \ B ⊆ (D.γ i₁ '' Set.Icc 0 (tM i₁)) ∪ (D.γ i₂ '' Set.Icc (tP i₂) 1) := by
      rintro x ⟨hx, hxnB⟩; rw [hγ₂'_range] at hx
      rcases hx with (h1 | hseg) | h2
      · exact Or.inl h1
      · exact (hxnB (hch12_B hseg)).elim
      · exact Or.inr h2
    -- Build new curve family γ' for Option B!
    let γ' (k : ℕ) : C(unitInterval, EuclideanSpace ℝ (Fin 2)) :=
      if k = i₁ then γ₁'
      else if k = i₂ then γ₂'
      else if k ∈ H then curveSpliceChord (D.γ k) (D.γ k) (tM k) (tP k)
      else D.γ k
    have hγ'_i1 : γ' i₁ = γ₁' := if_pos rfl
    have hγ'_i2 : γ' i₂ = γ₂' := by dsimp only [γ']; rw [if_neg h12.symm, if_pos rfl]
    have hγ'_other : ∀ k, k ≠ i₁ → k ≠ i₂ →
        γ' k = if k ∈ H then curveSpliceChord (D.γ k) (D.γ k) (tM k) (tP k) else D.γ k := by
      intro k h1 h2; dsimp only [γ']; rw [if_neg h1, if_neg h2]
    have hγ'_ends : ∀ k ∈ E, γ' k 0 = D.γ k 0 ∧ γ' k 1 = D.γ k 1 := by
      intro k hk; dsimp only [γ']
      split_ifs with h1 h2 hkH
      · rw [h1]; exact ⟨hγ₁'_0, hγ₁'_1⟩
      · rw [h2]; exact ⟨hγ₂'_0, hγ₂'_1⟩
      · exact ⟨(hshort_ok k hkH).2.1, (hshort_ok k hkH).2.2.1⟩
      · exact ⟨rfl, rfl⟩
    have hγ'_other_out : ∀ k ∈ E, k ≠ i₁ → k ≠ i₂ → Set.range (γ' k) \ B ⊆ Set.range (D.γ k) \ B := by
      intro k hk h1 h2; rw [hγ'_other k h1 h2]; split_ifs with hkH
      · exact (hshort_ok k hkH).2.2.2.2.1
      · exact Set.Subset.rfl
    have hγ'_other_in : ∀ k ∈ E, k ≠ i₁ → k ≠ i₂ →
        Set.range (γ' k) ∩ B = if k ∈ H then seg2 (aPt k) (bPt k) else ∅ := by
      intro k hk h1 h2; rw [hγ'_other k h1 h2]; split_ifs with hkH
      · exact (hshort_ok k hkH).2.2.2.2.2
      · ext x; simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false]
        rintro ⟨hx, hxB⟩; exact hB_disj_nonH k hk hkH x hx hxB
    -- Outside B: range γ₁' ∩ range γ₂' ⊆ range γ₁ ∩ range γ₂!
    have h12_out_sub : (Set.range γ₁' ∩ Set.range γ₂') \ B ⊆ (Set.range (D.γ i₁) ∩ Set.range (D.γ i₂)) \ B := by
      rintro x ⟨⟨hx1, hx2⟩, hxnB⟩
      have h1 := hγ₁'_out ⟨hx1, hxnB⟩
      have h2 := hγ₂'_out ⟨hx2, hxnB⟩
      refine ⟨⟨?_, ?_⟩, hxnB⟩
      · rcases h1 with ⟨s2, ⟨_, hs2⟩, rfl⟩ | ⟨u1, ⟨hu1, _⟩, rfl⟩
        · rcases h2 with ⟨s1, _, heq⟩ | ⟨u2, ⟨hu2, _⟩, heq⟩
          · exact ⟨s1, heq⟩
          · exfalso
            have := D.hinj i₂ hi₂ heq
            exact hsp2.2.1.not_ge (hs2.trans' (this ▸ hu2))
        · exact ⟨u1, rfl⟩
      · rcases h1 with ⟨s2, _, rfl⟩ | ⟨u1, ⟨hu1, _⟩, rfl⟩
        · exact ⟨s2, rfl⟩
        · rcases h2 with ⟨s1, ⟨_, hs1⟩, heq⟩ | ⟨u2, _, heq⟩
          · exfalso
            have := D.hinj i₁ hi₁ heq
            exact hsp1.2.1.not_ge (hs1.trans' (this ▸ hu1))
          · exact ⟨u2, heq⟩
    have h12_in_empty : (Set.range γ₁' ∩ Set.range γ₂') ∩ B = ∅ := by
      ext x; simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false]
      rintro ⟨⟨hx1, hx2⟩, hxB⟩
      have h1 : x ∈ seg2 (aPt i₂) (bPt i₁) := hγ₁'_in ⟨hx1, hxB⟩
      have h2 : x ∈ seg2 (aPt i₁) (bPt i₂) := by rw [← hγ₂'_inB]; exact ⟨hx2, hxB⟩
      exact (hSwap ▸ ⟨h2, h1⟩ : x ∈ (∅ : Set _))
    -- Inside B, every pair (k, m) with k ≠ m meets in a subsingleton (finite, ncard ≤ 1)!
    have hin_subsing : ∀ k ∈ E, ∀ m ∈ E, k ≠ m →
        ((Set.range (γ' k) ∩ Set.range (γ' m)) ∩ B).Subsingleton := by
      intro k hk m hm hne
      have hchord : ∀ u ∈ E, ∃ (S : Set (EuclideanSpace ℝ (Fin 2))),
          Set.range (γ' u) ∩ B ⊆ S ∧
          (S = ∅ ∨
           (u = i₁ ∧ S = seg2 (aPt i₂) (bPt i₁)) ∨
           (u = i₂ ∧ S = seg2 (aPt i₁) (bPt i₂)) ∨
           (u ≠ i₁ ∧ u ≠ i₂ ∧ u ∈ H ∧ S = seg2 (aPt u) (bPt u))) := by
        intro u hu
        by_cases hu1 : u = i₁
        · exact ⟨seg2 (aPt i₂) (bPt i₁), by rw [hu1, hγ'_i1]; exact hγ₁'_in, Or.inr (Or.inl ⟨hu1, rfl⟩)⟩
        · by_cases hu2 : u = i₂
          · exact ⟨seg2 (aPt i₁) (bPt i₂), by rw [hu2, hγ'_i2, hγ₂'_inB], Or.inr (Or.inr (Or.inl ⟨hu2, rfl⟩))⟩
          · by_cases huH : u ∈ H
            · exact ⟨seg2 (aPt u) (bPt u), by rw [hγ'_other_in u hu hu1 hu2, if_pos huH], Or.inr (Or.inr (Or.inr ⟨hu1, hu2, huH, rfl⟩))⟩
            · exact ⟨∅, by rw [hγ'_other_in u hu hu1 hu2, if_neg huH], Or.inl rfl⟩
      obtain ⟨Sk, hSk_sub, hSk_case⟩ := hchord k hk
      obtain ⟨Sm, hSm_sub, hSm_case⟩ := hchord m hm
      have hboth : (Set.range (γ' k) ∩ Set.range (γ' m)) ∩ B ⊆ Sk ∩ Sm := by
        rintro x ⟨⟨hxk, hxm⟩, hxB⟩; exact ⟨hSk_sub ⟨hxk, hxB⟩, hSm_sub ⟨hxm, hxB⟩⟩
      refine Set.Subsingleton.anti ?_ hboth
      rcases hSk_case with rfl | ⟨hk_eq, rfl⟩ | ⟨hk_eq, rfl⟩ | ⟨hk1, hk2, hkH, rfl⟩
      · simp
      · rcases hSm_case with rfl | ⟨hm_eq, rfl⟩ | ⟨hm_eq, rfl⟩ | ⟨hm1, hm2, hmH, rfl⟩
        · simp
        · exact (hne (hk_eq.trans hm_eq.symm)).elim
        · rw [Set.inter_comm, hSwap]; exact Set.subsingleton_empty
        · obtain ⟨d1, d2, d3, d4⟩ := hpts_disj i₂ hi₂H m hmH hm2.symm
          obtain ⟨e1, e2, e3, e4⟩ := hpts_disj i₁ hi₁H m hmH hm1.symm
          exact two_circle_chords_inter_subsingleton hsp2.2.2.2.1 hsp1.2.2.2.2.1
            (hpm_spec m hmH).2.2.2.1 (hpm_spec m hmH).2.2.2.2.1
            hba21.symm d1 d2 e3 e4 (hab_ne m hmH)
      · rcases hSm_case with rfl | ⟨hm_eq, rfl⟩ | ⟨hm_eq, rfl⟩ | ⟨hm1, hm2, hmH, rfl⟩
        · simp
        · rw [hSwap]; exact Set.subsingleton_empty
        · exact (hne (hk_eq.trans hm_eq.symm)).elim
        · obtain ⟨d1, d2, d3, d4⟩ := hpts_disj i₁ hi₁H m hmH hm1.symm
          obtain ⟨e1, e2, e3, e4⟩ := hpts_disj i₂ hi₂H m hmH hm2.symm
          exact two_circle_chords_inter_subsingleton hsp1.2.2.2.1 hsp2.2.2.2.2.1
            (hpm_spec m hmH).2.2.2.1 (hpm_spec m hmH).2.2.2.2.1
            hab12 d1 d2 e3 e4 (hab_ne m hmH)
      · rcases hSm_case with rfl | ⟨hm_eq, rfl⟩ | ⟨hm_eq, rfl⟩ | ⟨hm1, hm2, hmH, rfl⟩
        · simp
        · obtain ⟨d1, d2, d3, d4⟩ := hpts_disj k hkH i₂ hi₂H hk2
          obtain ⟨e1, e2, e3, e4⟩ := hpts_disj k hkH i₁ hi₁H hk1
          exact two_circle_chords_inter_subsingleton (hpm_spec k hkH).2.2.2.1 (hpm_spec k hkH).2.2.2.2.1
            hsp2.2.2.2.1 hsp1.2.2.2.2.1
            (hab_ne k hkH) d1 e2 d3 e4 hba21.symm
        · obtain ⟨d1, d2, d3, d4⟩ := hpts_disj k hkH i₁ hi₁H hk1
          obtain ⟨e1, e2, e3, e4⟩ := hpts_disj k hkH i₂ hi₂H hk2
          exact two_circle_chords_inter_subsingleton (hpm_spec k hkH).2.2.2.1 (hpm_spec k hkH).2.2.2.2.1
            hsp1.2.2.2.1 hsp2.2.2.2.2.1
            (hab_ne k hkH) d1 e2 d3 e4 hab12
        · obtain ⟨d1, d2, d3, d4⟩ := hpts_disj k hkH m hmH hne
          exact two_circle_chords_inter_subsingleton (hpm_spec k hkH).2.2.2.1 (hpm_spec k hkH).2.2.2.2.1
            (hpm_spec m hmH).2.2.2.1 (hpm_spec m hmH).2.2.2.2.1
            (hab_ne k hkH) d1 d2 d3 d4 (hab_ne m hmH)
    have hpair_fin : ∀ k ∈ E, ∀ m ∈ E, k ≠ m →
        ((Set.range (γ' k) ∩ Set.range (γ' m)) \ (A : Set _)).Finite := by
      intro k hk m hm hne
      have hsub_tot : (Set.range (γ' k) ∩ Set.range (γ' m)) \ (A : Set _) ⊆
          (((Set.range (γ' k) ∩ Set.range (γ' m)) \ (A : Set _)) \ B) ∪
          ((Set.range (γ' k) ∩ Set.range (γ' m)) ∩ B) := by
        intro x hx; by_cases hxB : x ∈ B
        · exact Or.inr ⟨hx.1, hxB⟩
        · exact Or.inl ⟨hx, hxB⟩
      have hout_fin : (((Set.range (γ' k) ∩ Set.range (γ' m)) \ (A : Set _)) \ B).Finite := by
        have hout_sub : ∀ u ∈ E, Set.range (γ' u) \ B ⊆
            if u = i₁ ∨ u = i₂ then (Set.range (D.γ i₁) ∪ Set.range (D.γ i₂)) \ B else Set.range (D.γ u) \ B := by
          intro u hu
          split_ifs with hu12
          · rcases hu12 with hu1 | hu2
            · rw [hu1, hγ'_i1]; rintro x hx; refine ⟨?_, hx.2⟩
              rcases hγ₁'_out hx with ⟨s, _, rfl⟩ | ⟨s, _, rfl⟩
              · exact Or.inr ⟨s, rfl⟩
              · exact Or.inl ⟨s, rfl⟩
            · rw [hu2, hγ'_i2]; rintro x hx; refine ⟨?_, hx.2⟩
              rcases hγ₂'_out hx with ⟨s, _, rfl⟩ | ⟨s, _, rfl⟩
              · exact Or.inl ⟨s, rfl⟩
              · exact Or.inr ⟨s, rfl⟩
          · push Not at hu12; exact hγ'_other_out u hu hu12.1 hu12.2
        by_cases hk12 : k = i₁ ∨ k = i₂
        · by_cases hm12 : m = i₁ ∨ m = i₂
          · have hsub : ((Set.range (γ' k) ∩ Set.range (γ' m)) \ (A : Set _)) \ B ⊆
                (Set.range (D.γ i₁) ∩ Set.range (D.γ i₂)) \ (A : Set _) := by
              rintro x ⟨⟨⟨hxk, hxm⟩, hxnA⟩, hxnB⟩
              rcases hk12 with hk1 | hk2 <;> rcases hm12 with hm1 | hm2
              · exact (hne (hk1.trans hm1.symm)).elim
              · rw [hk1, hγ'_i1] at hxk; rw [hm2, hγ'_i2] at hxm
                exact ⟨(h12_out_sub ⟨⟨hxk, hxm⟩, hxnB⟩).1, hxnA⟩
              · rw [hk2, hγ'_i2] at hxk; rw [hm1, hγ'_i1] at hxm
                exact ⟨(h12_out_sub ⟨⟨hxm, hxk⟩, hxnB⟩).1, hxnA⟩
              · exact (hne (hk2.trans hm2.symm)).elim
            exact (D.hfin i₁ hi₁ i₂ hi₂ h12).subset hsub
          · push Not at hm12
            have hsub : ((Set.range (γ' k) ∩ Set.range (γ' m)) \ (A : Set _)) \ B ⊆
                ((Set.range (D.γ i₁) ∩ Set.range (D.γ m)) \ (A : Set _)) ∪
                ((Set.range (D.γ i₂) ∩ Set.range (D.γ m)) \ (A : Set _)) := by
              rintro x ⟨⟨⟨hxk, hxm⟩, hxnA⟩, hxnB⟩
              have h1 := hout_sub k hk ⟨hxk, hxnB⟩; rw [if_pos hk12] at h1
              have h2 := hγ'_other_out m hm hm12.1 hm12.2 ⟨hxm, hxnB⟩
              rcases h1.1 with hx1 | hx2
              · exact Or.inl ⟨⟨hx1, h2.1⟩, hxnA⟩
              · exact Or.inr ⟨⟨hx2, h2.1⟩, hxnA⟩
            exact ((D.hfin i₁ hi₁ m hm hm12.1.symm).union (D.hfin i₂ hi₂ m hm hm12.2.symm)).subset hsub
        · push Not at hk12
          by_cases hm12 : m = i₁ ∨ m = i₂
          · have hsub : ((Set.range (γ' k) ∩ Set.range (γ' m)) \ (A : Set _)) \ B ⊆
                ((Set.range (D.γ k) ∩ Set.range (D.γ i₁)) \ (A : Set _)) ∪
                ((Set.range (D.γ k) ∩ Set.range (D.γ i₂)) \ (A : Set _)) := by
              rintro x ⟨⟨⟨hxk, hxm⟩, hxnA⟩, hxnB⟩
              have h1 := hγ'_other_out k hk hk12.1 hk12.2 ⟨hxk, hxnB⟩
              have h2 := hout_sub m hm ⟨hxm, hxnB⟩; rw [if_pos hm12] at h2
              rcases h2.1 with hx1 | hx2
              · exact Or.inl ⟨⟨h1.1, hx1⟩, hxnA⟩
              · exact Or.inr ⟨⟨h1.1, hx2⟩, hxnA⟩
            exact ((D.hfin k hk i₁ hi₁ hk12.1).union (D.hfin k hk i₂ hi₂ hk12.2)).subset hsub
          · push Not at hm12
            have hsub : ((Set.range (γ' k) ∩ Set.range (γ' m)) \ (A : Set _)) \ B ⊆
                (Set.range (D.γ k) ∩ Set.range (D.γ m)) \ (A : Set _) := by
              rintro x ⟨⟨⟨hxk, hxm⟩, hxnA⟩, hxnB⟩
              exact ⟨⟨(hγ'_other_out k hk hk12.1 hk12.2 ⟨hxk, hxnB⟩).1,
                (hγ'_other_out m hm hm12.1 hm12.2 ⟨hxm, hxnB⟩).1⟩, hxnA⟩
            exact (D.hfin k hk m hm hne).subset hsub
      exact (hout_fin.union (hin_subsing k hk m hm hne).finite).subset hsub_tot
    let D' : CurveDrawing A E :=
      { γ := γ'
        hinj := fun k hk => by
          dsimp only [γ']; split_ifs with h1 h2 hkH
          · exact hγ₁'_inj
          · exact hγ₂'_inj
          · exact (hshort_ok k hkH).1
          · exact D.hinj k hk
        h0 := fun k hk => (hγ'_ends k hk).1.symm ▸ D.h0 k hk
        h1 := fun k hk => (hγ'_ends k hk).2.symm ▸ D.h1 k hk
        hint := fun k hk t h0 h1 => by
          dsimp only [γ']; split_ifs with h1' h2' hkH
          · exact hγ₁'_int t h0 h1
          · exact hγ₂'_int t h0 h1
          · exact (hshort_ok k hkH).2.2.2.1 t h0 h1
          · exact D.hint k hk t h0 h1
        hsimple := fun a ha b hb heq => by
          apply D.hsimple ha hb
          dsimp only at heq ⊢
          rw [← (hγ'_ends a ha).1, ← (hγ'_ends a ha).2, ← (hγ'_ends b hb).1, ← (hγ'_ends b hb).2]
          exact heq
        hfin := hpair_fin }
    -- Now compare totalCrossings D' vs totalCrossings D!
    let c (k m : ℕ) := ((Set.range (D.γ k) ∩ Set.range (D.γ m)) \ (A : Set _)).ncard
    let c' (k m : ℕ) := ((Set.range (γ' k) ∩ Set.range (γ' m)) \ (A : Set _)).ncard
    have hc_symm : ∀ k m, c k m = c m k := fun k m => by dsimp only [c]; rw [Set.inter_comm]
    have hc'_symm : ∀ k m, c' k m = c' m k := fun k m => by dsimp only [c']; rw [Set.inter_comm]
    -- (1) For k, m ∉ {i₁, i₂}, c' k m ≤ c k m
    have hother_le : ∀ k ∈ E, k ≠ i₁ → k ≠ i₂ → ∀ m ∈ E, m ≠ i₁ → m ≠ i₂ → k ≠ m →
        c' k m ≤ c k m := by
      intro k hk hk1 hk2 m hm hm1 hm2 hne
      dsimp only [c', c]
      rw [ncard_split_ball (B := B) (hpair_fin k hk m hm hne),
          ncard_split_ball (B := B) (D.hfin k hk m hm hne)]
      have hout : (((Set.range (γ' k) ∩ Set.range (γ' m)) \ (A : Set _)) \ B).ncard ≤
          (((Set.range (D.γ k) ∩ Set.range (D.γ m)) \ (A : Set _)) \ B).ncard := by
        apply Set.ncard_le_ncard _ (D.hfin k hk m hm hne).sdiff
        rintro x ⟨⟨⟨hxk, hxm⟩, hxnA⟩, hxnB⟩
        exact ⟨⟨⟨(hγ'_other_out k hk hk1 hk2 ⟨hxk, hxnB⟩).1,
          (hγ'_other_out m hm hm1 hm2 ⟨hxm, hxnB⟩).1⟩, hxnA⟩, hxnB⟩
      have hin : (((Set.range (γ' k) ∩ Set.range (γ' m)) \ (A : Set _)) ∩ B).ncard ≤
          (((Set.range (D.γ k) ∩ Set.range (D.γ m)) \ (A : Set _)) ∩ B).ncard := by
        by_cases hkmH : k ∈ H ∧ m ∈ H
        · have hss : (((Set.range (γ' k) ∩ Set.range (γ' m)) \ (A : Set _)) ∩ B).Subsingleton :=
            (hin_subsing k hk m hm hne).anti (fun _ hx => ⟨hx.1.1, hx.2⟩)
          have hle1 : (((Set.range (γ' k) ∩ Set.range (γ' m)) \ (A : Set _)) ∩ B).ncard ≤ 1 :=
            ncard_le_one_of_subsingleton hss
          have hge1 : 1 ≤ (((Set.range (D.γ k) ∩ Set.range (D.γ m)) \ (A : Set _)) ∩ B).ncard := by
            have hp_in : p ∈ ((Set.range (D.γ k) ∩ Set.range (D.γ m)) \ (A : Set _)) ∩ B :=
              ⟨⟨⟨(Finset.mem_filter.mp hkmH.1).2, (Finset.mem_filter.mp hkmH.2).2⟩, hp_nA⟩,
                Metric.mem_closedBall_self hε_pos.le⟩
            exact (Set.ncard_pos ((D.hfin k hk m hm hne).inter_of_left B)).mpr ⟨p, hp_in⟩
          omega
        · have hemp : ((Set.range (γ' k) ∩ Set.range (γ' m)) \ (A : Set _)) ∩ B = ∅ := by
            ext x; simp only [Set.mem_inter_iff, Set.mem_sdiff, Set.mem_empty_iff_false, iff_false]
            rintro ⟨⟨⟨hxk, hxm⟩, _⟩, hxB⟩
            by_cases hkH : k ∈ H
            · have hmH : m ∉ H := fun h => hkmH ⟨hkH, h⟩
              have h2 : x ∈ Set.range (γ' m) ∩ B := ⟨hxm, hxB⟩
              rw [hγ'_other_in m hm hm1 hm2, if_neg hmH] at h2; exact h2
            · have h1 : x ∈ Set.range (γ' k) ∩ B := ⟨hxk, hxB⟩
              rw [hγ'_other_in k hk hk1 hk2, if_neg hkH] at h1; exact h1
          rw [hemp, Set.ncard_empty]; exact Nat.zero_le _
      omega
    -- (2) For k ∉ {i₁, i₂}, c' k i₁ + c' k i₂ ≤ c k i₁ + c k i₂!
    have hcross_pair_le : ∀ k ∈ E, k ≠ i₁ → k ≠ i₂ →
        c' k i₁ + c' k i₂ ≤ c k i₁ + c k i₂ := by
      intro k hk hk1 hk2
      dsimp only [c', c]
      rw [ncard_split_ball (B := B) (hpair_fin k hk i₁ hi₁ hk1),
          ncard_split_ball (B := B) (hpair_fin k hk i₂ hi₂ hk2),
          ncard_split_ball (B := B) (D.hfin k hk i₁ hi₁ hk1),
          ncard_split_ball (B := B) (D.hfin k hk i₂ hi₂ hk2)]
      have hout : (((Set.range (γ' k) ∩ Set.range (γ' i₁)) \ (A : Set _)) \ B).ncard +
                  (((Set.range (γ' k) ∩ Set.range (γ' i₂)) \ (A : Set _)) \ B).ncard ≤
                  (((Set.range (D.γ k) ∩ Set.range (D.γ i₁)) \ (A : Set _)) \ B).ncard +
                  (((Set.range (D.γ k) ∩ Set.range (D.γ i₂)) \ (A : Set _)) \ B).ncard := by
        apply ncard_add_le_of_union_inter (D.hfin k hk i₁ hi₁ hk1).sdiff (D.hfin k hk i₂ hi₂ hk2).sdiff
        · rintro x (⟨⟨⟨hxk, hx1⟩, hxnA⟩, hxnB⟩ | ⟨⟨⟨hxk, hx2⟩, hxnA⟩, hxnB⟩)
          · have h1 := (hγ'_other_out k hk hk1 hk2 ⟨hxk, hxnB⟩).1
            rw [hγ'_i1] at hx1
            rcases hγ₁'_out ⟨hx1, hxnB⟩ with ⟨s, _, rfl⟩ | ⟨s, _, rfl⟩
            · exact Or.inr ⟨⟨⟨h1, ⟨s, rfl⟩⟩, hxnA⟩, hxnB⟩
            · exact Or.inl ⟨⟨⟨h1, ⟨s, rfl⟩⟩, hxnA⟩, hxnB⟩
          · have h1 := (hγ'_other_out k hk hk1 hk2 ⟨hxk, hxnB⟩).1
            rw [hγ'_i2] at hx2
            rcases hγ₂'_out ⟨hx2, hxnB⟩ with ⟨s, _, rfl⟩ | ⟨s, _, rfl⟩
            · exact Or.inl ⟨⟨⟨h1, ⟨s, rfl⟩⟩, hxnA⟩, hxnB⟩
            · exact Or.inr ⟨⟨⟨h1, ⟨s, rfl⟩⟩, hxnA⟩, hxnB⟩
        · rintro x ⟨⟨⟨⟨hxk, hx1⟩, hxnA⟩, hxnB⟩, ⟨⟨⟨_, hx2⟩, _⟩, _⟩⟩
          have hk' := (hγ'_other_out k hk hk1 hk2 ⟨hxk, hxnB⟩).1
          rw [hγ'_i1] at hx1; rw [hγ'_i2] at hx2
          have h12 := (h12_out_sub ⟨⟨hx1, hx2⟩, hxnB⟩).1
          exact ⟨⟨⟨⟨hk', h12.1⟩, hxnA⟩, hxnB⟩, ⟨⟨⟨hk', h12.2⟩, hxnA⟩, hxnB⟩⟩
      have hin : (((Set.range (γ' k) ∩ Set.range (γ' i₁)) \ (A : Set _)) ∩ B).ncard +
                 (((Set.range (γ' k) ∩ Set.range (γ' i₂)) \ (A : Set _)) ∩ B).ncard ≤
                 (((Set.range (D.γ k) ∩ Set.range (D.γ i₁)) \ (A : Set _)) ∩ B).ncard +
                 (((Set.range (D.γ k) ∩ Set.range (D.γ i₂)) \ (A : Set _)) ∩ B).ncard := by
        by_cases hkH : k ∈ H
        · have hss1 : (((Set.range (γ' k) ∩ Set.range (γ' i₁)) \ (A : Set _)) ∩ B).Subsingleton :=
            (hin_subsing k hk i₁ hi₁ hk1).anti (fun _ hx => ⟨hx.1.1, hx.2⟩)
          have hss2 : (((Set.range (γ' k) ∩ Set.range (γ' i₂)) \ (A : Set _)) ∩ B).Subsingleton :=
            (hin_subsing k hk i₂ hi₂ hk2).anti (fun _ hx => ⟨hx.1.1, hx.2⟩)
          have hle1 : (((Set.range (γ' k) ∩ Set.range (γ' i₁)) \ (A : Set _)) ∩ B).ncard ≤ 1 :=
            ncard_le_one_of_subsingleton hss1
          have hle2 : (((Set.range (γ' k) ∩ Set.range (γ' i₂)) \ (A : Set _)) ∩ B).ncard ≤ 1 :=
            ncard_le_one_of_subsingleton hss2
          have hge1 : 1 ≤ (((Set.range (D.γ k) ∩ Set.range (D.γ i₁)) \ (A : Set _)) ∩ B).ncard :=
            (Set.ncard_pos ((D.hfin k hk i₁ hi₁ hk1).inter_of_left B)).mpr
              ⟨p, ⟨⟨(Finset.mem_filter.mp hkH).2, hp_r1⟩, hp_nA⟩, Metric.mem_closedBall_self hε_pos.le⟩
          have hge2 : 1 ≤ (((Set.range (D.γ k) ∩ Set.range (D.γ i₂)) \ (A : Set _)) ∩ B).ncard :=
            (Set.ncard_pos ((D.hfin k hk i₂ hi₂ hk2).inter_of_left B)).mpr
              ⟨p, ⟨⟨(Finset.mem_filter.mp hkH).2, hp_r2⟩, hp_nA⟩, Metric.mem_closedBall_self hε_pos.le⟩
          omega
        · have he1 : ((Set.range (γ' k) ∩ Set.range (γ' i₁)) \ (A : Set _)) ∩ B = ∅ := by
            ext x; simp only [Set.mem_inter_iff, Set.mem_sdiff, Set.mem_empty_iff_false, iff_false]
            rintro ⟨⟨⟨hxk, _⟩, _⟩, hxB⟩
            have h1 : x ∈ Set.range (γ' k) ∩ B := ⟨hxk, hxB⟩
            rw [hγ'_other_in k hk hk1 hk2, if_neg hkH] at h1; exact h1
          have he2 : ((Set.range (γ' k) ∩ Set.range (γ' i₂)) \ (A : Set _)) ∩ B = ∅ := by
            ext x; simp only [Set.mem_inter_iff, Set.mem_sdiff, Set.mem_empty_iff_false, iff_false]
            rintro ⟨⟨⟨hxk, _⟩, _⟩, hxB⟩
            have h1 : x ∈ Set.range (γ' k) ∩ B := ⟨hxk, hxB⟩
            rw [hγ'_other_in k hk hk1 hk2, if_neg hkH] at h1; exact h1
          rw [he1, he2, Set.ncard_empty]; omega
      omega
    -- (3) For (i₁, i₂), c' i₁ i₂ + 1 ≤ c i₁ i₂!
    have h12_drop : c' i₁ i₂ + 1 ≤ c i₁ i₂ := by
      dsimp only [c', c]
      rw [ncard_split_ball (B := B) (hpair_fin i₁ hi₁ i₂ hi₂ h12),
          ncard_split_ball (B := B) (D.hfin i₁ hi₁ i₂ hi₂ h12)]
      have hout : (((Set.range (γ' i₁) ∩ Set.range (γ' i₂)) \ (A : Set _)) \ B).ncard ≤
          (((Set.range (D.γ i₁) ∩ Set.range (D.γ i₂)) \ (A : Set _)) \ B).ncard := by
        apply Set.ncard_le_ncard _ (D.hfin i₁ hi₁ i₂ hi₂ h12).sdiff
        rintro x ⟨⟨⟨hx1, hx2⟩, hxnA⟩, hxnB⟩
        rw [hγ'_i1] at hx1; rw [hγ'_i2] at hx2
        exact ⟨⟨(h12_out_sub ⟨⟨hx1, hx2⟩, hxnB⟩).1, hxnA⟩, hxnB⟩
      have hin0 : ((Set.range (γ' i₁) ∩ Set.range (γ' i₂)) \ (A : Set _)) ∩ B = ∅ := by
        ext x; simp only [Set.mem_inter_iff, Set.mem_sdiff, Set.mem_empty_iff_false, iff_false]
        rintro ⟨⟨⟨hx1, hx2⟩, _⟩, hxB⟩
        rw [hγ'_i1] at hx1; rw [hγ'_i2] at hx2
        exact (h12_in_empty ▸ ⟨⟨hx1, hx2⟩, hxB⟩ : x ∈ (∅ : Set _))
      have hge1 : 1 ≤ (((Set.range (D.γ i₁) ∩ Set.range (D.γ i₂)) \ (A : Set _)) ∩ B).ncard :=
        (Set.ncard_pos ((D.hfin i₁ hi₁ i₂ hi₂ h12).inter_of_left B)).mpr
          ⟨p, ⟨⟨hp_r1, hp_r2⟩, hp_nA⟩, Metric.mem_closedBall_self hε_pos.le⟩
      rw [hin0, Set.ncard_empty]; omega
    -- Assemble totalCrossings D' + 2 ≤ totalCrossings D by splitting E = {i₁, i₂} ∪ Erest!
    refine ⟨D', ?_⟩
    let Erest := (E.erase i₁).erase i₂
    have hsplit_sum : ∀ (f : ℕ → ℕ → ℕ), (∀ a b, f a b = f b a) →
        (∑ k ∈ E, ∑ m ∈ E.erase k, f k m) =
        2 * f i₁ i₂ + 2 * (∑ k ∈ Erest, (f k i₁ + f k i₂)) +
        ∑ k ∈ Erest, ∑ m ∈ Erest.erase k, f k m := by
      intro f hfsymm
      have hi2_in : i₂ ∈ E.erase i₁ := Finset.mem_erase.mpr ⟨h12.symm, hi₂⟩
      rw [← Finset.add_sum_erase E (fun k => ∑ m ∈ E.erase k, f k m) hi₁,
          ← Finset.add_sum_erase (E.erase i₁) (fun k => ∑ m ∈ E.erase k, f k m) hi2_in]
      have hrow1 : ∑ m ∈ E.erase i₁, f i₁ m = f i₁ i₂ + ∑ k ∈ Erest, f k i₁ := by
        rw [← Finset.add_sum_erase (E.erase i₁) _ hi2_in]
        congr 1; exact Finset.sum_congr rfl fun k _ => hfsymm i₁ k
      have hrow2 : ∑ m ∈ E.erase i₂, f i₂ m = f i₁ i₂ + ∑ k ∈ Erest, f k i₂ := by
        have hi1_in : i₁ ∈ E.erase i₂ := Finset.mem_erase.mpr ⟨h12, hi₁⟩
        rw [← Finset.add_sum_erase (E.erase i₂) _ hi1_in, hfsymm i₂ i₁]
        congr 1
        have heq_er : (E.erase i₂).erase i₁ = Erest := by
          ext x; simp only [Erest, Finset.mem_erase]; tauto
        rw [heq_er]; exact Finset.sum_congr rfl fun k _ => hfsymm i₂ k
      have hrest : ∑ k ∈ Erest, ∑ m ∈ E.erase k, f k m =
          (∑ k ∈ Erest, (f k i₁ + f k i₂)) + ∑ k ∈ Erest, ∑ m ∈ Erest.erase k, f k m := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl; intro k hk
        have hk2 : k ≠ i₂ := (Finset.mem_erase.mp hk).1
        have hk1 : k ≠ i₁ := (Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).1
        have hi1_ek : i₁ ∈ E.erase k := Finset.mem_erase.mpr ⟨hk1.symm, hi₁⟩
        have hi2_ek : i₂ ∈ (E.erase k).erase i₁ := Finset.mem_erase.mpr ⟨h12.symm, Finset.mem_erase.mpr ⟨hk2.symm, hi₂⟩⟩
        rw [← Finset.add_sum_erase (E.erase k) _ hi1_ek,
            ← Finset.add_sum_erase ((E.erase k).erase i₁) _ hi2_ek]
        have heq_set : ((E.erase k).erase i₁).erase i₂ = Erest.erase k := by
          ext x; simp only [Erest, Finset.mem_erase]; tauto
        rw [heq_set]; omega
      rw [hrow1, hrow2, hrest, Finset.sum_add_distrib]
      omega
    have hX' := hsplit_sum c' hc'_symm
    have hX := hsplit_sum c hc_symm
    have hsum_cross : ∑ k ∈ Erest, (c' k i₁ + c' k i₂) ≤ ∑ k ∈ Erest, (c k i₁ + c k i₂) := by
      apply Finset.sum_le_sum; intro k hk
      have hk2 := (Finset.mem_erase.mp hk).1
      have hk1 := (Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).1
      have hkE := (Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).2
      exact hcross_pair_le k hkE hk1 hk2
    have hsum_other : ∑ k ∈ Erest, ∑ m ∈ Erest.erase k, c' k m ≤
        ∑ k ∈ Erest, ∑ m ∈ Erest.erase k, c k m := by
      apply Finset.sum_le_sum; intro k hk
      apply Finset.sum_le_sum; intro m hm
      have hk2 := (Finset.mem_erase.mp hk).1
      have hk1 := (Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).1
      have hkE := (Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).2
      have hkm := (Finset.mem_erase.mp hm).1
      have hm_r := (Finset.mem_erase.mp hm).2
      have hm2 := (Finset.mem_erase.mp hm_r).1
      have hm1 := (Finset.mem_erase.mp (Finset.mem_erase.mp hm_r).2).1
      have hmE := (Finset.mem_erase.mp (Finset.mem_erase.mp hm_r).2).2
      exact hother_le k hkE hk1 hk2 m hmE hm1 hm2 hkm.symm
    change (∑ k ∈ E, ∑ m ∈ E.erase k, c' k m) + 2 ≤ ∑ k ∈ E, ∑ m ∈ E.erase k, c k m
    rw [hX', hX]
    omega

/-- Eliminating all adjacent-edge crossings without increasing `totalCrossings`, by strong
induction on `totalCrossings`. -/
private lemma exists_no_adj_crossing
    (A : Finset (EuclideanSpace ℝ (Fin 2))) (E : Finset ℕ) (D : CurveDrawing A E) :
    ∃ D' : CurveDrawing A E,
      totalCrossings D' ≤ totalCrossings D ∧
      ∀ i ∈ E, ∀ j ∈ E, i ≠ j →
        (D'.γ i 0 = D'.γ j 0 ∨ D'.γ i 0 = D'.γ j 1 ∨ D'.γ i 1 = D'.γ j 0 ∨ D'.γ i 1 = D'.γ j 1) →
        (Set.range (D'.γ i) ∩ Set.range (D'.γ j)) \ (A : Set _) = ∅ := by
  suffices h : ∀ (N : ℕ) (D0 : CurveDrawing A E), totalCrossings D0 = N →
      ∃ D' : CurveDrawing A E,
        totalCrossings D' ≤ totalCrossings D0 ∧
        ∀ i ∈ E, ∀ j ∈ E, i ≠ j →
          (D'.γ i 0 = D'.γ j 0 ∨ D'.γ i 0 = D'.γ j 1 ∨ D'.γ i 1 = D'.γ j 0 ∨ D'.γ i 1 = D'.γ j 1) →
          (Set.range (D'.γ i) ∩ Set.range (D'.γ j)) \ (A : Set _) = ∅ from
    h (totalCrossings D) D rfl
  intro N
  induction N using Nat.strong_induction_on with
  | h N ih =>
    intro D0 hN
    by_cases hbad : ∃ i ∈ E, ∃ j ∈ E, i ≠ j ∧
        (D0.γ i 0 = D0.γ j 0 ∨ D0.γ i 0 = D0.γ j 1 ∨ D0.γ i 1 = D0.γ j 0 ∨ D0.γ i 1 = D0.γ j 1) ∧
        ((Set.range (D0.γ i) ∩ Set.range (D0.γ j)) \ (A : Set _)).Nonempty
    · obtain ⟨i, hi, j, hj, hne, hadj, hcr⟩ := hbad
      obtain ⟨D1, hdrop⟩ := adjacent_crossing_step A E D0 hi hj hne hadj hcr
      obtain ⟨D', hle, hno⟩ := ih (totalCrossings D1) (by omega) D1 rfl
      exact ⟨D', hle.trans (by omega), hno⟩
    · refine ⟨D0, le_refl _, fun i hi j hj hne hadj => ?_⟩
      by_contra hne_emp
      exact hbad ⟨i, hi, j, hj, hne, hadj, Set.nonempty_iff_ne_empty.mpr hne_emp⟩

end OMA.Erdos604CrossingLemma

/- ### Part 6: Top-Level Solution -/

theorem OMA.solution : OMA.R_Erdos604_erdos_604_variants_average_R2_H2_R1_H1_R1.H1 := by
  refine ⟨1024, by norm_num, fun A E γ hγ hsimple hfin => ?_⟩
  let D : OMA.Erdos604CrossingLemma.CurveDrawing A E :=
    { γ := γ
      hinj := fun i hi => (hγ i hi).1
      h0 := fun i hi => (hγ i hi).2.1
      h1 := fun i hi => (hγ i hi).2.2.1
      hint := fun i hi => (hγ i hi).2.2.2.1
      hsimple := hsimple
      hfin := hfin }
  rcases OMA.Erdos604CrossingLemma.crossing_lemma_of_planar_and_no_adj
    OMA.Erdos604CrossingLemma.planar_curveDrawing_bound
    OMA.Erdos604CrossingLemma.exists_no_adj_crossing A E D with h | h
  · exact Or.inl (h.trans (Nat.mul_le_mul_right A.card (by norm_num)))
  · exact Or.inr h

