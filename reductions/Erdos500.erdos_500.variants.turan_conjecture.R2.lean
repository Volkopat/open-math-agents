import FormalConjectures.ErdosProblems.«500»

-- Reduction Erdos500.erdos_500.variants.turan_conjecture.R2 of Erdős Problem 500 — turan conjecture
-- Credit: @mucoucah
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
Turan's tetrahedron conjecture: ex(n, K_4^3) ~ (5/9) C(n,3).
This file proves the lower half completely (Turan's balanced 3-partite construction gives
ex(n) >= (5/9 - 5/n) C(n,3) for every n >= 3), so only the asymptotic upper bound is left.
The upper bound is split by the maximum pair codegree of a K_4^3-free 3-graph H on n vertices
(the number of z with xyz an edge). In Turan's construction the maximum codegree is about 2n/3.
H1: graphs with some pair of codegree above 2n/3 have at most (5/9 + eps) C(n,3) edges.
H2: graphs with every pair of codegree at most 2n/3 have at most (5/9 + eps) C(n,3) edges.
Both follow from the conjecture; together they give it.
-/

namespace OMA.R_Erdos500_erdos_500_variants_turan_conjecture_R2

open Filter Asymptotics

theorem two_mul_choose_two (n : ℕ) : 2 * n.choose 2 = n * (n - 1) := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Nat.choose_succ_succ, Nat.choose_one_right, mul_add, ih]
    cases k with
    | zero => simp
    | succ m =>
      simp only [Nat.add_sub_cancel]
      ring

theorem six_mul_choose_three (n : ℕ) : 6 * n.choose 3 = n * (n - 1) * (n - 2) := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Nat.choose_succ_succ, mul_add, ih]
    have h2 : 6 * k.choose 2 = 3 * (k * (k - 1)) := by
      have := two_mul_choose_two k
      omega
    rw [h2]
    rcases k with _ | _ | m
    · simp
    · simp
    · rw [show m + 1 + 1 - 1 = m + 1 by omega, show m + 1 + 1 - 2 = m by omega,
          show m + 1 + 1 + 1 - 1 = m + 2 by omega, show m + 1 + 1 + 1 - 2 = m + 1 by omega]
      ring

theorem choose_three_step (n : ℕ) (hn : 3 ≤ n) :
    (n - 2) * (n + 1).choose 3 = (n + 1) * n.choose 3 := by
  have h1 := six_mul_choose_three (n + 1)
  have h2 := six_mul_choose_three n
  have h3 : 6 * ((n - 2) * (n + 1).choose 3) = 6 * ((n + 1) * n.choose 3) := by
    calc 6 * ((n - 2) * (n + 1).choose 3)
        = (n - 2) * (6 * (n + 1).choose 3) := by ring
      _ = (n - 2) * ((n + 1) * n * (n - 1)) := by
          rw [h1]
          have : n + 1 - 1 = n := by omega
          have : n + 1 - 2 = n - 1 := by omega
          simp_all
      _ = (n + 1) * (n * (n - 1) * (n - 2)) := by ring
      _ = (n + 1) * (6 * n.choose 3) := by rw [h2]
      _ = 6 * ((n + 1) * n.choose 3) := by ring
  omega

open scoped Classical in
/-- Any K_4^3-free 3-uniform hypergraph on Fin n has at most cliqueExtremalNumber n 3 4 edges. -/
theorem cliqueExtremalNumber_ge_card {n : ℕ} (H : Finset (Finset (Fin n)))
    (hunif : ∀ e ∈ H, e.card = 3) (hfree : ¬ H.ContainsCompleteHypergraph 3 4) :
    H.card ≤ Hypergraph.cliqueExtremalNumber n 3 4 := by
  unfold Hypergraph.cliqueExtremalNumber Hypergraph.extremalNumber
  apply Finset.le_sup (f := Finset.card)
  simp only [Finset.mem_filter, Finset.mem_powerset]
  refine ⟨?_, hfree⟩
  intro e he
  rw [Finset.mem_powersetCard]
  exact ⟨Finset.subset_univ e, hunif e he⟩

open scoped Classical in
/-- There exists an extremal K_4^3-free 3-uniform hypergraph on Fin n. -/
theorem exists_extremal_hypergraph (n : ℕ) :
    ∃ H : Finset (Finset (Fin n)),
      (∀ e ∈ H, e.card = 3) ∧
      ¬ H.ContainsCompleteHypergraph 3 4 ∧
      H.card = Hypergraph.cliqueExtremalNumber n 3 4 := by
  let F : Finset (Finset (Finset (Fin n))) :=
    ((Finset.univ : Finset (Fin n)).powersetCard 3).powerset.filter
      (fun H => ¬ H.ContainsCompleteHypergraph 3 4)
  have hempty : (∅ : Finset (Finset (Fin n))) ∈ F := by
    simp only [F, Finset.mem_filter, Finset.mem_powerset]
    refine ⟨Finset.empty_subset _, ?_⟩
    rintro ⟨S, hScard, hSsub⟩
    have hcard : (S.powersetCard 3).card = 0 := by
      rw [Finset.subset_empty.mp hSsub]
      simp
    rw [Finset.card_powersetCard, hScard] at hcard
    norm_num at hcard
  obtain ⟨H, hHF, hHsup⟩ := Finset.exists_mem_eq_sup F ⟨∅, hempty⟩ Finset.card
  simp only [F, Finset.mem_filter, Finset.mem_powerset] at hHF
  refine ⟨H, ?_, hHF.2, ?_⟩
  · intro e he
    exact (Finset.mem_powersetCard.mp (hHF.1 he)).2
  · unfold Hypergraph.cliqueExtremalNumber Hypergraph.extremalNumber
    convert hHsup.symm

theorem colorCount_sum {n : ℕ} (S : Finset (Fin n)) :
    ((S).filter (fun x_c => x_c.val % 3 = 0)).card + ((S).filter (fun x_c => x_c.val % 3 = 1)).card + ((S).filter (fun x_c => x_c.val % 3 = 2)).card = S.card := by
  have hd01 : Disjoint (S.filter (fun v => v.val % 3 = 0)) (S.filter (fun v => v.val % 3 = 1)) := by
    rw [Finset.disjoint_filter]
    intro v _ h0 h1
    omega
  have hd012 : Disjoint (S.filter (fun v => v.val % 3 = 0) ∪ S.filter (fun v => v.val % 3 = 1))
      (S.filter (fun v => v.val % 3 = 2)) := by
    rw [Finset.disjoint_left]
    intro v hv1 hv2
    simp only [Finset.mem_union, Finset.mem_filter] at hv1 hv2
    omega
  rw [← Finset.card_union_of_disjoint hd01, ← Finset.card_union_of_disjoint hd012]
  congr 1
  ext v
  simp only [Finset.mem_union, Finset.mem_filter]
  constructor
  · rintro ((⟨hv, _⟩ | ⟨hv, _⟩) | ⟨hv, _⟩) <;> exact hv
  · intro hv
    have hmod : v.val % 3 = 0 ∨ v.val % 3 = 1 ∨ v.val % 3 = 2 := by omega
    rcases hmod with h | h | h
    · exact Or.inl (Or.inl ⟨hv, h⟩)
    · exact Or.inl (Or.inr ⟨hv, h⟩)
    · exact Or.inr ⟨hv, h⟩

theorem colorCount_erase {n : ℕ} (S : Finset (Fin n)) (v : Fin n) (hv : v ∈ S) (r : ℕ) :
    (((S.erase v)).filter (fun x_c => x_c.val % 3 = r)).card =
      if v.val % 3 = r then ((S).filter (fun x_c => x_c.val % 3 = r)).card - 1 else ((S).filter (fun x_c => x_c.val % 3 = r)).card := by
  by_cases hr : v.val % 3 = r
  · rw [if_pos hr]
    have heq : (S.erase v).filter (fun x => x.val % 3 = r) =
        (S.filter (fun x => x.val % 3 = r)).erase v := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_erase]
      tauto
    rw [heq, Finset.card_erase_of_mem (Finset.mem_filter.mpr ⟨hv, hr⟩)]
  · rw [if_neg hr]
    congr 1
    ext x
    simp only [Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro ⟨⟨_, hxS⟩, hxr⟩
      exact ⟨hxS, hxr⟩
    · rintro ⟨hxS, hxr⟩
      exact ⟨⟨fun h => hr (h ▸ hxr), hxS⟩, hxr⟩

/-- Turan's construction contains no complete 3-graph on 4 vertices. -/
theorem turanGraph_no_K4 (n : ℕ) : ¬ ((((Finset.univ : Finset (Fin n)).powersetCard 3).filter (fun e_t => ((((e_t).filter (fun x_c => x_c.val % 3 = 0)).card = 1 ∧ ((e_t).filter (fun x_c => x_c.val % 3 = 1)).card = 1 ∧ ((e_t).filter (fun x_c => x_c.val % 3 = 2)).card = 1) ∨ (((e_t).filter (fun x_c => x_c.val % 3 = 0)).card = 2 ∧ ((e_t).filter (fun x_c => x_c.val % 3 = 1)).card = 1 ∧ ((e_t).filter (fun x_c => x_c.val % 3 = 2)).card = 0) ∨ (((e_t).filter (fun x_c => x_c.val % 3 = 0)).card = 0 ∧ ((e_t).filter (fun x_c => x_c.val % 3 = 1)).card = 2 ∧ ((e_t).filter (fun x_c => x_c.val % 3 = 2)).card = 1) ∨ (((e_t).filter (fun x_c => x_c.val % 3 = 0)).card = 1 ∧ ((e_t).filter (fun x_c => x_c.val % 3 = 1)).card = 0 ∧ ((e_t).filter (fun x_c => x_c.val % 3 = 2)).card = 2))))).ContainsCompleteHypergraph 3 4 := by
  rintro ⟨S, hScard, hSsub⟩
  have hsum : ((S).filter (fun x_c => x_c.val % 3 = 0)).card + ((S).filter (fun x_c => x_c.val % 3 = 1)).card + ((S).filter (fun x_c => x_c.val % 3 = 2)).card = 4 := by
    rw [colorCount_sum, hScard]
  have herase : ∀ v ∈ S, (((((S.erase v)).filter (fun x_c => x_c.val % 3 = 0)).card = 1 ∧ (((S.erase v)).filter (fun x_c => x_c.val % 3 = 1)).card = 1 ∧ (((S.erase v)).filter (fun x_c => x_c.val % 3 = 2)).card = 1) ∨ ((((S.erase v)).filter (fun x_c => x_c.val % 3 = 0)).card = 2 ∧ (((S.erase v)).filter (fun x_c => x_c.val % 3 = 1)).card = 1 ∧ (((S.erase v)).filter (fun x_c => x_c.val % 3 = 2)).card = 0) ∨ ((((S.erase v)).filter (fun x_c => x_c.val % 3 = 0)).card = 0 ∧ (((S.erase v)).filter (fun x_c => x_c.val % 3 = 1)).card = 2 ∧ (((S.erase v)).filter (fun x_c => x_c.val % 3 = 2)).card = 1) ∨ ((((S.erase v)).filter (fun x_c => x_c.val % 3 = 0)).card = 1 ∧ (((S.erase v)).filter (fun x_c => x_c.val % 3 = 1)).card = 0 ∧ (((S.erase v)).filter (fun x_c => x_c.val % 3 = 2)).card = 2)) := by
    intro v hv
    have hmem : S.erase v ∈ S.powersetCard 3 := by
      rw [Finset.mem_powersetCard]
      exact ⟨Finset.erase_subset v S, by rw [Finset.card_erase_of_mem hv, hScard]⟩
    exact (Finset.mem_filter.mp (hSsub hmem)).2
  have hstep : ∀ r : ℕ, 0 < ((S).filter (fun x_c => x_c.val % 3 = r)).card →
      ∃ v ∈ S, v.val % 3 = r ∧ (((((S.erase v)).filter (fun x_c => x_c.val % 3 = 0)).card = 1 ∧ (((S.erase v)).filter (fun x_c => x_c.val % 3 = 1)).card = 1 ∧ (((S.erase v)).filter (fun x_c => x_c.val % 3 = 2)).card = 1) ∨ ((((S.erase v)).filter (fun x_c => x_c.val % 3 = 0)).card = 2 ∧ (((S.erase v)).filter (fun x_c => x_c.val % 3 = 1)).card = 1 ∧ (((S.erase v)).filter (fun x_c => x_c.val % 3 = 2)).card = 0) ∨ ((((S.erase v)).filter (fun x_c => x_c.val % 3 = 0)).card = 0 ∧ (((S.erase v)).filter (fun x_c => x_c.val % 3 = 1)).card = 2 ∧ (((S.erase v)).filter (fun x_c => x_c.val % 3 = 2)).card = 1) ∨ ((((S.erase v)).filter (fun x_c => x_c.val % 3 = 0)).card = 1 ∧ (((S.erase v)).filter (fun x_c => x_c.val % 3 = 1)).card = 0 ∧ (((S.erase v)).filter (fun x_c => x_c.val % 3 = 2)).card = 2)) := by
    intro r hr
    obtain ⟨v, hv⟩ := Finset.card_pos.mp hr
    rw [Finset.mem_filter] at hv
    exact ⟨v, hv.1, hv.2, herase v hv.1⟩
  have h0 : 0 < ((S).filter (fun x_c => x_c.val % 3 = 0)).card →
      (((S).filter (fun x_c => x_c.val % 3 = 0)).card = 2 ∧ ((S).filter (fun x_c => x_c.val % 3 = 1)).card = 1 ∧ ((S).filter (fun x_c => x_c.val % 3 = 2)).card = 1) ∨
      (((S).filter (fun x_c => x_c.val % 3 = 0)).card = 3 ∧ ((S).filter (fun x_c => x_c.val % 3 = 1)).card = 1 ∧ ((S).filter (fun x_c => x_c.val % 3 = 2)).card = 0) ∨
      (((S).filter (fun x_c => x_c.val % 3 = 0)).card = 1 ∧ ((S).filter (fun x_c => x_c.val % 3 = 1)).card = 2 ∧ ((S).filter (fun x_c => x_c.val % 3 = 2)).card = 1) ∨
      (((S).filter (fun x_c => x_c.val % 3 = 0)).card = 2 ∧ ((S).filter (fun x_c => x_c.val % 3 = 1)).card = 0 ∧ ((S).filter (fun x_c => x_c.val % 3 = 2)).card = 2) := by
    intro hr
    obtain ⟨v, hv, hvr, hedge⟩ := hstep 0 hr
    rw [colorCount_erase S v hv 0, colorCount_erase S v hv 1,
      colorCount_erase S v hv 2] at hedge
    simp only [hvr, ↓reduceIte, show (0 : ℕ) ≠ 1 by decide, show (0 : ℕ) ≠ 2 by decide] at hedge
    omega
  have h1 : 0 < ((S).filter (fun x_c => x_c.val % 3 = 1)).card →
      (((S).filter (fun x_c => x_c.val % 3 = 0)).card = 1 ∧ ((S).filter (fun x_c => x_c.val % 3 = 1)).card = 2 ∧ ((S).filter (fun x_c => x_c.val % 3 = 2)).card = 1) ∨
      (((S).filter (fun x_c => x_c.val % 3 = 0)).card = 2 ∧ ((S).filter (fun x_c => x_c.val % 3 = 1)).card = 2 ∧ ((S).filter (fun x_c => x_c.val % 3 = 2)).card = 0) ∨
      (((S).filter (fun x_c => x_c.val % 3 = 0)).card = 0 ∧ ((S).filter (fun x_c => x_c.val % 3 = 1)).card = 3 ∧ ((S).filter (fun x_c => x_c.val % 3 = 2)).card = 1) ∨
      (((S).filter (fun x_c => x_c.val % 3 = 0)).card = 1 ∧ ((S).filter (fun x_c => x_c.val % 3 = 1)).card = 1 ∧ ((S).filter (fun x_c => x_c.val % 3 = 2)).card = 2) := by
    intro hr
    obtain ⟨v, hv, hvr, hedge⟩ := hstep 1 hr
    rw [colorCount_erase S v hv 0, colorCount_erase S v hv 1,
      colorCount_erase S v hv 2] at hedge
    simp only [hvr, ↓reduceIte, show (1 : ℕ) ≠ 0 by decide, show (1 : ℕ) ≠ 2 by decide] at hedge
    omega
  have h2 : 0 < ((S).filter (fun x_c => x_c.val % 3 = 2)).card →
      (((S).filter (fun x_c => x_c.val % 3 = 0)).card = 1 ∧ ((S).filter (fun x_c => x_c.val % 3 = 1)).card = 1 ∧ ((S).filter (fun x_c => x_c.val % 3 = 2)).card = 2) ∨
      (((S).filter (fun x_c => x_c.val % 3 = 0)).card = 2 ∧ ((S).filter (fun x_c => x_c.val % 3 = 1)).card = 1 ∧ ((S).filter (fun x_c => x_c.val % 3 = 2)).card = 1) ∨
      (((S).filter (fun x_c => x_c.val % 3 = 0)).card = 0 ∧ ((S).filter (fun x_c => x_c.val % 3 = 1)).card = 2 ∧ ((S).filter (fun x_c => x_c.val % 3 = 2)).card = 2) ∨
      (((S).filter (fun x_c => x_c.val % 3 = 0)).card = 1 ∧ ((S).filter (fun x_c => x_c.val % 3 = 1)).card = 0 ∧ ((S).filter (fun x_c => x_c.val % 3 = 2)).card = 3) := by
    intro hr
    obtain ⟨v, hv, hvr, hedge⟩ := hstep 2 hr
    rw [colorCount_erase S v hv 0, colorCount_erase S v hv 1,
      colorCount_erase S v hv 2] at hedge
    simp only [hvr, ↓reduceIte, show (2 : ℕ) ≠ 0 by decide, show (2 : ℕ) ≠ 1 by decide] at hedge
    omega
  omega

theorem div_three_le_card_colorClass (n r : ℕ) (hr : r < 3) :
    n / 3 ≤ (((Finset.univ : Finset (Fin n)).filter (fun x_c => x_c.val % 3 = r))).card := by
  let emb : Fin (n / 3) ↪ Fin n :=
    ⟨fun k => ⟨3 * k.val + r, by omega⟩, by
      intro a b h
      ext
      have := congrArg Fin.val h
      dsimp at this
      omega⟩
  have hsub : (Finset.univ : Finset (Fin (n / 3))).map emb ⊆ ((Finset.univ : Finset (Fin n)).filter (fun x_c => x_c.val % 3 = r)) := by
    intro x hx
    obtain ⟨k, _, rfl⟩ := Finset.mem_map.mp hx
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, by change (3 * k.val + r) % 3 = r; omega⟩
  have := Finset.card_le_card hsub
  simpa using this

theorem card_turanGraph_ge (n : ℕ) :
    (n / 3) ^ 3 + 3 * ((n / 3).choose 2 * (n / 3)) ≤ ((((Finset.univ : Finset (Fin n)).powersetCard 3).filter (fun e_t => ((((e_t).filter (fun x_c => x_c.val % 3 = 0)).card = 1 ∧ ((e_t).filter (fun x_c => x_c.val % 3 = 1)).card = 1 ∧ ((e_t).filter (fun x_c => x_c.val % 3 = 2)).card = 1) ∨ (((e_t).filter (fun x_c => x_c.val % 3 = 0)).card = 2 ∧ ((e_t).filter (fun x_c => x_c.val % 3 = 1)).card = 1 ∧ ((e_t).filter (fun x_c => x_c.val % 3 = 2)).card = 0) ∨ (((e_t).filter (fun x_c => x_c.val % 3 = 0)).card = 0 ∧ ((e_t).filter (fun x_c => x_c.val % 3 = 1)).card = 2 ∧ ((e_t).filter (fun x_c => x_c.val % 3 = 2)).card = 1) ∨ (((e_t).filter (fun x_c => x_c.val % 3 = 0)).card = 1 ∧ ((e_t).filter (fun x_c => x_c.val % 3 = 1)).card = 0 ∧ ((e_t).filter (fun x_c => x_c.val % 3 = 2)).card = 2))))).card := by
  classical
  let V0 := ((Finset.univ : Finset (Fin n)).filter (fun x_c => x_c.val % 3 = 0))
  let V1 := ((Finset.univ : Finset (Fin n)).filter (fun x_c => x_c.val % 3 = 1))
  let V2 := ((Finset.univ : Finset (Fin n)).filter (fun x_c => x_c.val % 3 = 2))
  let E_rain : Finset (Finset (Fin n)) :=
    (V0 ×ˢ (V1 ×ˢ V2)).image (fun t => {t.1, t.2.1, t.2.2})
  let E_01 : Finset (Finset (Fin n)) :=
    (V0.powersetCard 2 ×ˢ V1).image (fun t => insert t.2 t.1)
  let E_12 : Finset (Finset (Fin n)) :=
    (V1.powersetCard 2 ×ˢ V2).image (fun t => insert t.2 t.1)
  let E_20 : Finset (Finset (Fin n)) :=
    (V2.powersetCard 2 ×ˢ V0).image (fun t => insert t.2 t.1)
  have hfilter_triple : ∀ a ∈ V0, ∀ b ∈ V1, ∀ c ∈ V2,
      ({a, b, c} : Finset (Fin n)).filter (fun v => v.val % 3 = 0) = {a} ∧
      ({a, b, c} : Finset (Fin n)).filter (fun v => v.val % 3 = 1) = {b} ∧
      ({a, b, c} : Finset (Fin n)).filter (fun v => v.val % 3 = 2) = {c} := by
    intro a ha b hb c hc
    have ha0 : a.val % 3 = 0 := (Finset.mem_filter.mp ha).2
    have hb1 : b.val % 3 = 1 := (Finset.mem_filter.mp hb).2
    have hc2 : c.val % 3 = 2 := (Finset.mem_filter.mp hc).2
    refine ⟨?_, ?_, ?_⟩
    · ext x; simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨rfl | rfl | rfl, hx⟩ <;> omega
      · rintro rfl; exact ⟨Or.inl rfl, ha0⟩
    · ext x; simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨rfl | rfl | rfl, hx⟩ <;> omega
      · rintro rfl; exact ⟨Or.inr (Or.inl rfl), hb1⟩
    · ext x; simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨rfl | rfl | rfl, hx⟩ <;> omega
      · rintro rfl; exact ⟨Or.inr (Or.inr rfl), hc2⟩
  have hfilter_pair : ∀ (r1 r2 : ℕ), r1 ≠ r2 → ∀ p ∈ (((Finset.univ : Finset (Fin n)).filter (fun x_c => x_c.val % 3 = r1))).powersetCard 2,
      ∀ c ∈ ((Finset.univ : Finset (Fin n)).filter (fun x_c => x_c.val % 3 = r2)),
      (insert c p).filter (fun v => v.val % 3 = r1) = p ∧
      (insert c p).filter (fun v => v.val % 3 = r2) = {c} ∧
      (∀ r3, r3 ≠ r1 → r3 ≠ r2 → (insert c p).filter (fun v => v.val % 3 = r3) = ∅) ∧
      (insert c p).card = 3 := by
    intro r1 r2 hne p hp c hc
    rw [Finset.mem_powersetCard] at hp
    have hc_mod : c.val % 3 = r2 := (Finset.mem_filter.mp hc).2
    have hp_mod : ∀ x ∈ p, x.val % 3 = r1 := fun x hx => (Finset.mem_filter.mp (hp.1 hx)).2
    have hc_not : c ∉ p := fun h => hne ((hp_mod c h).symm.trans hc_mod)
    refine ⟨?_, ?_, ?_, ?_⟩
    · ext x; simp only [Finset.mem_filter, Finset.mem_insert]
      constructor
      · rintro ⟨rfl | hxp, hx⟩
        · exact absurd (hc_mod.symm.trans hx) hne.symm
        · exact hxp
      · intro hxp
        exact ⟨Or.inr hxp, hp_mod x hxp⟩
    · ext x; simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨rfl | hxp, hx⟩
        · rfl
        · exact absurd ((hp_mod x hxp).symm.trans hx) hne
      · rintro rfl
        exact ⟨Or.inl rfl, hc_mod⟩
    · intro r3 h31 h32
      ext x; simp only [Finset.mem_filter, Finset.mem_insert, Finset.notMem_empty, iff_false]
      rintro ⟨rfl | hxp, hx⟩
      · exact h32 (hx.symm.trans hc_mod)
      · exact h31 (hx.symm.trans (hp_mod x hxp))
    · rw [Finset.card_insert_of_notMem hc_not, hp.2]
  have hrain_counts : ∀ e ∈ E_rain,
      ((e).filter (fun x_c => x_c.val % 3 = 0)).card = 1 ∧ ((e).filter (fun x_c => x_c.val % 3 = 1)).card = 1 ∧ ((e).filter (fun x_c => x_c.val % 3 = 2)).card = 1 ∧ e.card = 3 := by
    intro e he
    obtain ⟨⟨a, b, c⟩, ht, rfl⟩ := Finset.mem_image.mp he
    rw [Finset.mem_product, Finset.mem_product] at ht
    obtain ⟨f0, f1, f2⟩ := hfilter_triple a ht.1 b ht.2.1 c ht.2.2
    have c0 : ((({a, b, c} : Finset (Fin n))).filter (fun x_c => x_c.val % 3 = 0)).card = 1 := by rw [f0]; simp
    have c1 : ((({a, b, c} : Finset (Fin n))).filter (fun x_c => x_c.val % 3 = 1)).card = 1 := by rw [f1]; simp
    have c2 : ((({a, b, c} : Finset (Fin n))).filter (fun x_c => x_c.val % 3 = 2)).card = 1 := by rw [f2]; simp
    have hsum := colorCount_sum ({a, b, c} : Finset (Fin n))
    dsimp only
    exact ⟨c0, c1, c2, by omega⟩
  have h01_counts : ∀ e ∈ E_01,
      ((e).filter (fun x_c => x_c.val % 3 = 0)).card = 2 ∧ ((e).filter (fun x_c => x_c.val % 3 = 1)).card = 1 ∧ ((e).filter (fun x_c => x_c.val % 3 = 2)).card = 0 ∧ e.card = 3 := by
    intro e he
    obtain ⟨⟨p, c⟩, ht, rfl⟩ := Finset.mem_image.mp he
    rw [Finset.mem_product] at ht
    obtain ⟨f0, f1, f2, hcard⟩ := hfilter_pair 0 1 (by decide) p ht.1 c ht.2
    refine ⟨?_, ?_, ?_, hcard⟩
    · rw [f0]; exact (Finset.mem_powersetCard.mp ht.1).2
    · rw [f1]; simp
    · rw [f2 2 (by decide) (by decide)]; simp
  have h12_counts : ∀ e ∈ E_12,
      ((e).filter (fun x_c => x_c.val % 3 = 0)).card = 0 ∧ ((e).filter (fun x_c => x_c.val % 3 = 1)).card = 2 ∧ ((e).filter (fun x_c => x_c.val % 3 = 2)).card = 1 ∧ e.card = 3 := by
    intro e he
    obtain ⟨⟨p, c⟩, ht, rfl⟩ := Finset.mem_image.mp he
    rw [Finset.mem_product] at ht
    obtain ⟨f1, f2, f0, hcard⟩ := hfilter_pair 1 2 (by decide) p ht.1 c ht.2
    refine ⟨?_, ?_, ?_, hcard⟩
    · rw [f0 0 (by decide) (by decide)]; simp
    · rw [f1]; exact (Finset.mem_powersetCard.mp ht.1).2
    · rw [f2]; simp
  have h20_counts : ∀ e ∈ E_20,
      ((e).filter (fun x_c => x_c.val % 3 = 0)).card = 1 ∧ ((e).filter (fun x_c => x_c.val % 3 = 1)).card = 0 ∧ ((e).filter (fun x_c => x_c.val % 3 = 2)).card = 2 ∧ e.card = 3 := by
    intro e he
    obtain ⟨⟨p, c⟩, ht, rfl⟩ := Finset.mem_image.mp he
    rw [Finset.mem_product] at ht
    obtain ⟨f2, f0, f1, hcard⟩ := hfilter_pair 2 0 (by decide) p ht.1 c ht.2
    refine ⟨?_, ?_, ?_, hcard⟩
    · rw [f0]; simp
    · rw [f1 1 (by decide) (by decide)]; simp
    · rw [f2]; exact (Finset.mem_powersetCard.mp ht.1).2
  have hcard_rain : E_rain.card = V0.card * (V1.card * V2.card) := by
    rw [Finset.card_image_of_injOn]
    · simp [Finset.card_product]
    · rintro ⟨a1, b1, c1⟩ h1 ⟨a2, b2, c2⟩ h2 heq
      dsimp only at heq
      rw [Finset.mem_coe, Finset.mem_product, Finset.mem_product] at h1 h2
      obtain ⟨f10, f11, f12⟩ := hfilter_triple a1 h1.1 b1 h1.2.1 c1 h1.2.2
      obtain ⟨f20, f21, f22⟩ := hfilter_triple a2 h2.1 b2 h2.2.1 c2 h2.2.2
      have ha : ({a1} : Finset (Fin n)) = {a2} := by rw [← f10, heq, f20]
      have hb : ({b1} : Finset (Fin n)) = {b2} := by rw [← f11, heq, f21]
      have hc : ({c1} : Finset (Fin n)) = {c2} := by rw [← f12, heq, f22]
      simp only [Finset.singleton_inj] at ha hb hc
      simp [ha, hb, hc]
  have hcard_pair : ∀ (r1 r2 : ℕ), r1 ≠ r2 →
      (((((Finset.univ : Finset (Fin n)).filter (fun x_c => x_c.val % 3 = r1))).powersetCard 2 ×ˢ ((Finset.univ : Finset (Fin n)).filter (fun x_c => x_c.val % 3 = r2))).image
        (fun t => insert t.2 t.1)).card =
      (((Finset.univ : Finset (Fin n)).filter (fun x_c => x_c.val % 3 = r1))).card.choose 2 * (((Finset.univ : Finset (Fin n)).filter (fun x_c => x_c.val % 3 = r2))).card := by
    intro r1 r2 hne
    rw [Finset.card_image_of_injOn]
    · simp [Finset.card_product, Finset.card_powersetCard]
    · rintro ⟨p1, c1⟩ h1 ⟨p2, c2⟩ h2 heq
      dsimp only at heq
      rw [Finset.mem_coe, Finset.mem_product] at h1 h2
      obtain ⟨fp1, fc1, _, _⟩ := hfilter_pair r1 r2 hne p1 h1.1 c1 h1.2
      obtain ⟨fp2, fc2, _, _⟩ := hfilter_pair r1 r2 hne p2 h2.1 c2 h2.2
      have hp : p1 = p2 := by rw [← fp1, heq, fp2]
      have hc : ({c1} : Finset (Fin n)) = {c2} := by rw [← fc1, heq, fc2]
      simp only [Finset.singleton_inj] at hc
      simp [hp, hc]
  have hcard_01 : E_01.card = V0.card.choose 2 * V1.card := hcard_pair 0 1 (by decide)
  have hcard_12 : E_12.card = V1.card.choose 2 * V2.card := hcard_pair 1 2 (by decide)
  have hcard_20 : E_20.card = V2.card.choose 2 * V0.card := hcard_pair 2 0 (by decide)
  have hd_r_01 : Disjoint E_rain E_01 := by
    rw [Finset.disjoint_left]
    intro e h1 h2
    have := hrain_counts e h1
    have := h01_counts e h2
    omega
  have hd_r01_12 : Disjoint (E_rain ∪ E_01) E_12 := by
    rw [Finset.disjoint_left]
    intro e h1 h2
    have := h12_counts e h2
    rcases Finset.mem_union.mp h1 with hr | h01
    · have := hrain_counts e hr; omega
    · have := h01_counts e h01; omega
  have hd_all_20 : Disjoint (E_rain ∪ E_01 ∪ E_12) E_20 := by
    rw [Finset.disjoint_left]
    intro e h1 h2
    have := h20_counts e h2
    rcases Finset.mem_union.mp h1 with h1' | h12
    · rcases Finset.mem_union.mp h1' with hr | h01
      · have := hrain_counts e hr; omega
      · have := h01_counts e h01; omega
    · have := h12_counts e h12; omega
  have hsub : E_rain ∪ E_01 ∪ E_12 ∪ E_20 ⊆ (((Finset.univ : Finset (Fin n)).powersetCard 3).filter (fun e_t => ((((e_t).filter (fun x_c => x_c.val % 3 = 0)).card = 1 ∧ ((e_t).filter (fun x_c => x_c.val % 3 = 1)).card = 1 ∧ ((e_t).filter (fun x_c => x_c.val % 3 = 2)).card = 1) ∨ (((e_t).filter (fun x_c => x_c.val % 3 = 0)).card = 2 ∧ ((e_t).filter (fun x_c => x_c.val % 3 = 1)).card = 1 ∧ ((e_t).filter (fun x_c => x_c.val % 3 = 2)).card = 0) ∨ (((e_t).filter (fun x_c => x_c.val % 3 = 0)).card = 0 ∧ ((e_t).filter (fun x_c => x_c.val % 3 = 1)).card = 2 ∧ ((e_t).filter (fun x_c => x_c.val % 3 = 2)).card = 1) ∨ (((e_t).filter (fun x_c => x_c.val % 3 = 0)).card = 1 ∧ ((e_t).filter (fun x_c => x_c.val % 3 = 1)).card = 0 ∧ ((e_t).filter (fun x_c => x_c.val % 3 = 2)).card = 2)))) := by
    intro e he
    rw [Finset.mem_filter, Finset.mem_powersetCard]
    rcases Finset.mem_union.mp he with h1 | h20
    · rcases Finset.mem_union.mp h1 with h2 | h12
      · rcases Finset.mem_union.mp h2 with hr | h01
        · obtain ⟨c0, c1, c2, hc⟩ := hrain_counts e hr
          exact ⟨⟨Finset.subset_univ _, hc⟩, Or.inl ⟨c0, c1, c2⟩⟩
        · obtain ⟨c0, c1, c2, hc⟩ := h01_counts e h01
          exact ⟨⟨Finset.subset_univ _, hc⟩, Or.inr (Or.inl ⟨c0, c1, c2⟩)⟩
      · obtain ⟨c0, c1, c2, hc⟩ := h12_counts e h12
        exact ⟨⟨Finset.subset_univ _, hc⟩, Or.inr (Or.inr (Or.inl ⟨c0, c1, c2⟩))⟩
    · obtain ⟨c0, c1, c2, hc⟩ := h20_counts e h20
      exact ⟨⟨Finset.subset_univ _, hc⟩, Or.inr (Or.inr (Or.inr ⟨c0, c1, c2⟩))⟩
  have hle_total : E_rain.card + E_01.card + E_12.card + E_20.card ≤ ((((Finset.univ : Finset (Fin n)).powersetCard 3).filter (fun e_t => ((((e_t).filter (fun x_c => x_c.val % 3 = 0)).card = 1 ∧ ((e_t).filter (fun x_c => x_c.val % 3 = 1)).card = 1 ∧ ((e_t).filter (fun x_c => x_c.val % 3 = 2)).card = 1) ∨ (((e_t).filter (fun x_c => x_c.val % 3 = 0)).card = 2 ∧ ((e_t).filter (fun x_c => x_c.val % 3 = 1)).card = 1 ∧ ((e_t).filter (fun x_c => x_c.val % 3 = 2)).card = 0) ∨ (((e_t).filter (fun x_c => x_c.val % 3 = 0)).card = 0 ∧ ((e_t).filter (fun x_c => x_c.val % 3 = 1)).card = 2 ∧ ((e_t).filter (fun x_c => x_c.val % 3 = 2)).card = 1) ∨ (((e_t).filter (fun x_c => x_c.val % 3 = 0)).card = 1 ∧ ((e_t).filter (fun x_c => x_c.val % 3 = 1)).card = 0 ∧ ((e_t).filter (fun x_c => x_c.val % 3 = 2)).card = 2))))).card := by
    have := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hd_all_20, Finset.card_union_of_disjoint hd_r01_12,
      Finset.card_union_of_disjoint hd_r_01] at this
    exact this
  have hV0 : n / 3 ≤ V0.card := div_three_le_card_colorClass n 0 (by decide)
  have hV1 : n / 3 ≤ V1.card := div_three_le_card_colorClass n 1 (by decide)
  have hV2 : n / 3 ≤ V2.card := div_three_le_card_colorClass n 2 (by decide)
  have hr_ge : (n / 3) ^ 3 ≤ E_rain.card := by
    rw [hcard_rain, pow_three]
    exact Nat.mul_le_mul hV0 (Nat.mul_le_mul hV1 hV2)
  have h01_ge : (n / 3).choose 2 * (n / 3) ≤ E_01.card := by
    rw [hcard_01]
    exact Nat.mul_le_mul (Nat.choose_le_choose 2 hV0) hV1
  have h12_ge : (n / 3).choose 2 * (n / 3) ≤ E_12.card := by
    rw [hcard_12]
    exact Nat.mul_le_mul (Nat.choose_le_choose 2 hV1) hV2
  have h20_ge : (n / 3).choose 2 * (n / 3) ≤ E_20.card := by
    rw [hcard_20]
    exact Nat.mul_le_mul (Nat.choose_le_choose 2 hV2) hV0
  omega

/-- Explicit Turan lower bound: cliqueExtremalNumber n 3 4 >= q^3 + 3 * choose(q, 2) * q. -/
theorem turan_extremal_lower_nat (n : ℕ) :
    (n / 3) ^ 3 + 3 * ((n / 3).choose 2 * (n / 3)) ≤ Hypergraph.cliqueExtremalNumber n 3 4 := by
  have hunif : ∀ e ∈ (((Finset.univ : Finset (Fin n)).powersetCard 3).filter (fun e_t => ((((e_t).filter (fun x_c => x_c.val % 3 = 0)).card = 1 ∧ ((e_t).filter (fun x_c => x_c.val % 3 = 1)).card = 1 ∧ ((e_t).filter (fun x_c => x_c.val % 3 = 2)).card = 1) ∨ (((e_t).filter (fun x_c => x_c.val % 3 = 0)).card = 2 ∧ ((e_t).filter (fun x_c => x_c.val % 3 = 1)).card = 1 ∧ ((e_t).filter (fun x_c => x_c.val % 3 = 2)).card = 0) ∨ (((e_t).filter (fun x_c => x_c.val % 3 = 0)).card = 0 ∧ ((e_t).filter (fun x_c => x_c.val % 3 = 1)).card = 2 ∧ ((e_t).filter (fun x_c => x_c.val % 3 = 2)).card = 1) ∨ (((e_t).filter (fun x_c => x_c.val % 3 = 0)).card = 1 ∧ ((e_t).filter (fun x_c => x_c.val % 3 = 1)).card = 0 ∧ ((e_t).filter (fun x_c => x_c.val % 3 = 2)).card = 2)))), e.card = 3 := fun e he =>
    (Finset.mem_powersetCard.mp (Finset.mem_filter.mp he).1).2
  exact (card_turanGraph_ge n).trans
    (cliqueExtremalNumber_ge_card ((((Finset.univ : Finset (Fin n)).powersetCard 3).filter (fun e_t => ((((e_t).filter (fun x_c => x_c.val % 3 = 0)).card = 1 ∧ ((e_t).filter (fun x_c => x_c.val % 3 = 1)).card = 1 ∧ ((e_t).filter (fun x_c => x_c.val % 3 = 2)).card = 1) ∨ (((e_t).filter (fun x_c => x_c.val % 3 = 0)).card = 2 ∧ ((e_t).filter (fun x_c => x_c.val % 3 = 1)).card = 1 ∧ ((e_t).filter (fun x_c => x_c.val % 3 = 2)).card = 0) ∨ (((e_t).filter (fun x_c => x_c.val % 3 = 0)).card = 0 ∧ ((e_t).filter (fun x_c => x_c.val % 3 = 1)).card = 2 ∧ ((e_t).filter (fun x_c => x_c.val % 3 = 2)).card = 1) ∨ (((e_t).filter (fun x_c => x_c.val % 3 = 0)).card = 1 ∧ ((e_t).filter (fun x_c => x_c.val % 3 = 1)).card = 0 ∧ ((e_t).filter (fun x_c => x_c.val % 3 = 2)).card = 2))))) hunif (turanGraph_no_K4 n))

/-- Explicit lower bound from Turan's construction, for all n >= 3. -/
theorem five_ninths_sub_le (n : ℕ) (hn : 3 ≤ n) :
    (5 / 9 - 5 / (n : ℝ)) * (n.choose 3 : ℝ) ≤ Hypergraph.cliqueExtremalNumber n 3 4 := by
  have hCpos : (0 : ℝ) < (n.choose 3 : ℝ) := by exact_mod_cast Nat.choose_pos hn
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  by_cases h9 : n < 9
  · have hnonpos : 5 / 9 - 5 / (n : ℝ) ≤ 0 := by
      rw [sub_nonpos, div_le_div_iff₀ (by norm_num) hn_pos]
      have hn_le : (n : ℝ) ≤ 9 := by exact_mod_cast (by omega : n ≤ 9)
      linarith
    nlinarith [Nat.cast_nonneg (α := ℝ) (Hypergraph.cliqueExtremalNumber n 3 4)]
  · push Not at h9
    have hnat : 2 * ((n / 3) ^ 3 + 3 * ((n / 3).choose 2 * (n / 3))) ≤
        2 * Hypergraph.cliqueExtremalNumber n 3 4 :=
      Nat.mul_le_mul_left 2 (turan_extremal_lower_nat n)
    have h2ch : 2 * (n / 3).choose 2 = (n / 3) * (n / 3 - 1) := two_mul_choose_two (n / 3)
    have hq_pos : 1 ≤ n / 3 := by omega
    have hq_real : (5 : ℝ) * ((n / 3 : ℕ) : ℝ) ^ 3 - 3 * ((n / 3 : ℕ) : ℝ) ^ 2 ≤
        2 * (Hypergraph.cliqueExtremalNumber n 3 4 : ℝ) := by
      have hnat2 : 2 * (n / 3) ^ 3 + 3 * ((n / 3) * (n / 3 - 1) * (n / 3)) ≤
          2 * Hypergraph.cliqueExtremalNumber n 3 4 := by
        calc 2 * (n / 3) ^ 3 + 3 * ((n / 3) * (n / 3 - 1) * (n / 3))
            = 2 * (n / 3) ^ 3 + 3 * (2 * (n / 3).choose 2 * (n / 3)) := by rw [h2ch]
          _ = 2 * ((n / 3) ^ 3 + 3 * ((n / 3).choose 2 * (n / 3))) := by ring
          _ ≤ 2 * Hypergraph.cliqueExtremalNumber n 3 4 := hnat
      have hcast : (2 : ℝ) * ((n / 3 : ℕ) : ℝ) ^ 3 +
          3 * (((n / 3 : ℕ) : ℝ) * ((n / 3 - 1 : ℕ) : ℝ) * ((n / 3 : ℕ) : ℝ)) ≤
          2 * (Hypergraph.cliqueExtremalNumber n 3 4 : ℝ) := by
        exact_mod_cast hnat2
      have hsub : ((n / 3 - 1 : ℕ) : ℝ) = ((n / 3 : ℕ) : ℝ) - 1 := by
        rw [Nat.cast_sub hq_pos, Nat.cast_one]
      rw [hsub] at hcast
      linarith
    have hq_lo : (n : ℝ) - 2 ≤ 3 * ((n / 3 : ℕ) : ℝ) := by
      have : n ≤ 3 * (n / 3) + 2 := by omega
      have : (n : ℝ) ≤ 3 * ((n / 3 : ℕ) : ℝ) + 2 := by exact_mod_cast this
      linarith
    have hq_hi : 3 * ((n / 3 : ℕ) : ℝ) ≤ (n : ℝ) := by
      have : 3 * (n / 3) ≤ n := by omega
      exact_mod_cast this
    have hq_nonneg : (0 : ℝ) ≤ ((n / 3 : ℕ) : ℝ) := Nat.cast_nonneg _
    have hn_ge9 : (9 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h9
    have hcube : ((n : ℝ) - 2) ^ 3 ≤ (3 * ((n / 3 : ℕ) : ℝ)) ^ 3 :=
      pow_le_pow_left₀ (by linarith) hq_lo 3
    have hsq : (3 * ((n / 3 : ℕ) : ℝ)) ^ 2 ≤ (n : ℝ) ^ 2 := by
      nlinarith
    have hex_ge : 5 / 9 * (n : ℝ) ^ 3 - 5 * (n : ℝ) ^ 2 ≤
        6 * (Hypergraph.cliqueExtremalNumber n 3 4 : ℝ) := by
      nlinarith
    have hchoose_le : 6 * (n.choose 3 : ℝ) ≤ (n : ℝ) ^ 3 := by
      have h6 := six_mul_choose_three n
      have hle_nat : 6 * n.choose 3 ≤ n ^ 3 := by
        rw [h6, pow_three, ← mul_assoc]
        exact Nat.mul_le_mul (Nat.mul_le_mul le_rfl (Nat.sub_le n 1)) (Nat.sub_le n 2)
      exact_mod_cast hle_nat
    have hcoeff_nonneg : 0 ≤ 5 / 9 - 5 / (n : ℝ) := by
      rw [sub_nonneg, div_le_div_iff₀ hn_pos (by norm_num)]
      linarith
    have hmul6 : (5 / 9 - 5 / (n : ℝ)) * (6 * (n.choose 3 : ℝ)) ≤
        6 * (Hypergraph.cliqueExtremalNumber n 3 4 : ℝ) := by
      calc (5 / 9 - 5 / (n : ℝ)) * (6 * (n.choose 3 : ℝ))
          ≤ (5 / 9 - 5 / (n : ℝ)) * (n : ℝ) ^ 3 :=
            mul_le_mul_of_nonneg_left hchoose_le hcoeff_nonneg
        _ = 5 / 9 * (n : ℝ) ^ 3 - 5 * (n : ℝ) ^ 2 := by field_simp
        _ ≤ 6 * (Hypergraph.cliqueExtremalNumber n 3 4 : ℝ) := hex_ge
    linarith

/-- Upper bound when some pair of vertices has codegree above 2n/3. -/
def H1 : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∀ H : Finset (Finset (Fin n)),
    (∀ e ∈ H, e.card = 3) →
    (¬ ∃ S : Finset (Fin n), S.card = 4 ∧ S.powersetCard 3 ⊆ H) →
    (∃ x y : Fin n, x ≠ y ∧
      2 * n < 3 * (Finset.univ.filter (fun z => ({x, y, z} : Finset (Fin n)) ∈ H)).card) →
    (H.card : ℝ) ≤ (5 / 9 + ε) * (n.choose 3 : ℝ)

/-- Upper bound when every pair of vertices has codegree at most 2n/3. -/
def H2 : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∀ H : Finset (Finset (Fin n)),
    (∀ e ∈ H, e.card = 3) →
    (¬ ∃ S : Finset (Fin n), S.card = 4 ∧ S.powersetCard 3 ⊆ H) →
    (∀ x y : Fin n, x ≠ y →
      3 * (Finset.univ.filter (fun z => ({x, y, z} : Finset (Fin n)) ∈ H)).card ≤ 2 * n) →
    (H.card : ℝ) ≤ (5 / 9 + ε) * (n.choose 3 : ℝ)

theorem main : H1 → H2 → type_of% @Erdos500.erdos_500.variants.turan_conjecture := by
  intro h1 h2
  have hup : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      (Hypergraph.cliqueExtremalNumber n 3 4 : ℝ) ≤ (5 / 9 + ε) * (n.choose 3 : ℝ) := by
    intro ε hε
    filter_upwards [h1 ε hε, h2 ε hε] with n hA hB
    obtain ⟨H, hunif, hfree, hcard⟩ := exists_extremal_hypergraph n
    have hfree' : ¬ ∃ S : Finset (Fin n), S.card = 4 ∧ S.powersetCard 3 ⊆ H := hfree
    rw [← hcard]
    by_cases hc : ∃ x y : Fin n, x ≠ y ∧
        2 * n < 3 * (Finset.univ.filter (fun z => ({x, y, z} : Finset (Fin n)) ∈ H)).card
    · exact hA H hunif hfree' hc
    · refine hB H hunif hfree' (fun x y hxy => ?_)
      by_contra hlt
      exact hc ⟨x, y, hxy, lt_of_not_ge hlt⟩
  have hlow : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      (5 / 9 - ε) * (n.choose 3 : ℝ) ≤ Hypergraph.cliqueExtremalNumber n 3 4 := by
    intro ε hε
    filter_upwards [eventually_ge_atTop 3, eventually_ge_atTop ⌈5 / ε⌉₊] with n hn3 hnε
    have hl := five_ninths_sub_le n hn3
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have h5 : 5 / (n : ℝ) ≤ ε := by
      rw [div_le_iff₀ hnpos]
      have h := Nat.ceil_le.mp hnε
      rw [div_le_iff₀ hε] at h
      linarith
    have hC : (0 : ℝ) ≤ n.choose 3 := Nat.cast_nonneg _
    nlinarith
  refine Asymptotics.isLittleO_iff.mpr ?_
  intro c hc
  have hε : 0 < c * (5 / 9) := by positivity
  filter_upwards [hlow (c * (5 / 9)) hε, hup (c * (5 / 9)) hε] with n hl hu
  have hC : (0 : ℝ) ≤ (n.choose 3 : ℝ) := Nat.cast_nonneg _
  rw [Pi.sub_apply, Real.norm_eq_abs, Real.norm_of_nonneg (by positivity), abs_le]
  constructor <;> nlinarith

end OMA.R_Erdos500_erdos_500_variants_turan_conjecture_R2
