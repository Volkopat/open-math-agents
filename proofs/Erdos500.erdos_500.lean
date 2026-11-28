import FormalConjectures.ErdosProblems.«500»

/-! Direct inclusion-exclusion formula for the finite tetrahedron extremal number. -/

open Finset in
private def ie (n : ℕ) : ℕ :=
  let E := (univ : Finset (Fin n)).powersetCard 3
  let B := (univ : Finset (Fin n)).powersetCard 4
  ((Icc 1 E.card).filter fun q => 0 < ∑ T ∈ B.powerset,
    let u := (T.biUnion (·.powersetCard 3)).card
    if u ≤ q then (-1 : ℤ) ^ T.card * (E.card - u).choose (q - u) else 0).card

def OMA.answer : ℕ → ℕ := ie

open scoped Classical in
open Finset in
theorem OMA.solution : Erdos500.erdos_500.answer = OMA.answer →
    type_of% @Erdos500.erdos_500 := by
  intro h; rw [h]; funext n; symm
  let E := (univ : Finset (Fin n)).powersetCard 3
  let B := (univ : Finset (Fin n)).powersetCard 4
  let P (H : Finset (Finset (Fin n))) : Prop := ¬ H.ContainsCompleteHypergraph 3 4
  let s := E.powerset.filter P
  have hie (q : ℕ) :
      (∑ T ∈ B.powerset,
        let u := (T.biUnion (·.powersetCard 3)).card
        if u ≤ q then (-1 : ℤ) ^ T.card * ((E.card - u).choose (q - u) : ℤ) else 0) =
      ((E.powersetCard q).filter P).card := by
    have hc (T : Finset (Finset (Fin n))) :
        (let u := (T.biUnion (·.powersetCard 3)).card
         if u ≤ q then (-1 : ℤ) ^ T.card * ((E.card - u).choose (q - u) : ℤ) else 0) =
        ∑ H ∈ E.powersetCard q, if T.biUnion (·.powersetCard 3) ⊆ H then (-1 : ℤ) ^ T.card else 0 := by
      dsimp only
      set F := T.biUnion (·.powersetCard 3)
      have hF : F ⊆ E := fun e he => by
        obtain ⟨S, _, heS⟩ := mem_biUnion.mp he
        exact mem_powersetCard.mpr ⟨subset_univ e, (mem_powersetCard.mp heS).2⟩
      rw [← sum_filter, sum_const, nsmul_eq_mul, mul_comm]
      by_cases hu : F.card ≤ q
      · rw [if_pos hu, card_filter_powersetCard_subset F E q hF hu]
      · have he : (E.powersetCard q).filter (F ⊆ ·) = ∅ := eq_empty_iff_forall_notMem.mpr fun H hH =>
          hu ((card_mono (mem_filter.mp hH).2).trans_eq (mem_powersetCard.mp (mem_filter.mp hH).1).2)
        rw [if_neg hu, he, card_empty]; simp
    have hi (H : Finset (Finset (Fin n))) :
        (∑ T ∈ B.powerset, if T.biUnion (·.powersetCard 3) ⊆ H then (-1 : ℤ) ^ T.card else 0) =
          if P H then 1 else 0 := by
      let bad := B.filter (·.powersetCard 3 ⊆ H)
      have hb : B.powerset.filter (fun T => T.biUnion (·.powersetCard 3) ⊆ H) = bad.powerset := by
        ext T; simp only [mem_filter, mem_powerset]
        rw [biUnion_subset_iff_forall_subset]; simp [bad, subset_iff, forall_and]
      have hp : (bad = ∅) ↔ P H := by
        simp [bad, P, B, Finset.ContainsCompleteHypergraph, eq_empty_iff_forall_notMem]
      rw [← sum_filter, hb, sum_powerset_neg_one_pow_card]; simp [hp]
    calc _ = ∑ T ∈ B.powerset, ∑ H ∈ E.powersetCard q,
              if T.biUnion (·.powersetCard 3) ⊆ H then (-1 : ℤ) ^ T.card else 0 :=
            sum_congr rfl fun T _ => hc T
      _ = ∑ H ∈ E.powersetCard q, if P H then 1 else 0 := by
            rw [sum_comm]; exact sum_congr rfl fun H _ => hi H
      _ = _ := by rw [← sum_filter]; simp
  have hset : ((Icc 1 E.card).filter fun q => 0 < ∑ T ∈ B.powerset,
      let u := (T.biUnion (·.powersetCard 3)).card
      if u ≤ q then (-1 : ℤ) ^ T.card * ((E.card - u).choose (q - u) : ℤ) else 0) =
      Icc 1 (s.sup card) := by
    ext q
    simp only [mem_filter, mem_Icc, hie, Int.natCast_pos, card_pos, Finset.Nonempty, mem_powersetCard]
    constructor
    · rintro ⟨⟨h1, _⟩, H, ⟨hHE, rfl⟩, hHP⟩
      exact ⟨h1, le_sup (mem_filter.mpr ⟨mem_powerset.mpr hHE, hHP⟩)⟩
    · rintro ⟨h1, hq⟩
      obtain ⟨H, hHs, hqH⟩ := (Finset.le_sup_iff h1).mp hq
      obtain ⟨hHE, hHP⟩ := mem_filter.mp hHs
      obtain ⟨D, hDH, rfl⟩ := exists_subset_card_eq hqH
      have hDE := hDH.trans (mem_powerset.mp hHE)
      exact ⟨⟨h1, card_le_card hDE⟩, D, ⟨hDE, rfl⟩, fun ⟨S, hS, hSD⟩ => hHP ⟨S, hS, hSD.trans hDH⟩⟩
  unfold OMA.answer ie Hypergraph.cliqueExtremalNumber Hypergraph.extremalNumber
  dsimp only [E, B, s, P] at hset ⊢
  rw [hset, Nat.card_Icc, Nat.add_sub_cancel]
  convert rfl
