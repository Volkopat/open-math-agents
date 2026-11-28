import FormalConjectures.ErdosProblems.«723»

/-!
# A certificate with 103 partial transversals in one Latin square

The three coordinates are row, column, and symbol. Each ten-cell partial
transversal omits one value in each coordinate. Two transversals are compatible
when their number of common cells plus their number of equal missing coordinates
is one. The first hypothesis asks for an explicit square and 103 such sets.
The second converts any certificate into all 157 projective lines.
The two lemmas converting labeled lines to a plane are by @ian139, from
open-math-agents PR 3312.
-/

namespace OMA.R_Erdos723_erdos_723_variants_eq_12_R3

open Configuration

/-- Construct one Latin square of order eleven and 103 compatible ten-cell partial transversals. -/
def H1 : Prop :=
  ∃ (s : (Fin 11 × Fin 11) → Fin 11) (B : Fin 103 → Finset (Fin 11 × Fin 11)),
    let c : Fin 3 → (Fin 11 × Fin 11) → Fin 11 := ![Prod.fst, Prod.snd, s]
    (∀ r : Fin 11, Function.Injective (fun k : Fin 11 => s (r,k))) ∧
    (∀ k : Fin 11, Function.Injective (fun r : Fin 11 => s (r,k))) ∧
    (∀ i, (B i).card = 10 ∧ ∀ d, Set.InjOn (c d) (B i : Set (Fin 11 × Fin 11))) ∧
    ∀ i j, i ≠ j →
      (B i ∩ B j).card + (Finset.univ.filter (fun d : Fin 3 =>
        ∃ a : Fin 11, a ∉ (B i).image (c d) ∧ a ∉ (B j).image (c d))).card = 1

/-- Complete the certificate to 157 size-thirteen lines, meeting once in each pair. -/
def H2 : Prop :=
  ∀ (s : (Fin 11 × Fin 11) → Fin 11) (B : Fin 103 → Finset (Fin 11 × Fin 11)),
    let c : Fin 3 → (Fin 11 × Fin 11) → Fin 11 := ![Prod.fst, Prod.snd, s]
    (∀ r : Fin 11, Function.Injective (fun k : Fin 11 => s (r,k))) →
    (∀ k : Fin 11, Function.Injective (fun r : Fin 11 => s (r,k))) →
    (∀ i, (B i).card = 10 ∧ ∀ d, Set.InjOn (c d) (B i : Set (Fin 11 × Fin 11))) →
    (∀ i j, i ≠ j →
      (B i ∩ B j).card + (Finset.univ.filter (fun d : Fin 3 =>
        ∃ a : Fin 11, a ∉ (B i).image (c d) ∧ a ∉ (B j).image (c d))).card = 1) →
    ∃ L : Fin 157 → Finset (Fin 157), (∀ i, (L i).card = 13) ∧
      ∀ i j, i ≠ j → ∃! p, p ∈ L i ∧ p ∈ L j

lemma third_point (s : Finset (Fin 157)) (hs : s.card = 13) (a b : Fin 157) :
    ∃ x ∈ s, x ≠ a ∧ x ≠ b := by
  classical
  by_contra hn
  have sub : s ⊆ {a, b} := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton]
    by_contra! h
    exact hn ⟨x, hx, h⟩
  have hle := Finset.card_le_card sub
  have hpair : ({a, b} : Finset (Fin 157)).card ≤ 2 := by
    by_cases h : a = b <;> simp [h]
  omega

lemma plane_of_blocks (B : Fin 157 → Finset (Fin 157)) (size : ∀ i, (B i).card = 13)
    (meet : ∀ i j, i ≠ j → ∃! x, x ∈ B i ∧ x ∈ B j) :
    type_of% @Erdos723.erdos_723.variants.eq_12 := by
  classical
  letI : Membership (Fin 157) (Fin 157) := ⟨fun l p => p ∈ B l⟩
  have outside (i j : Fin 157) : ∃ p, p ∉ B i ∧ p ∉ B j := by
    by_contra hn
    have sub : Finset.univ ⊆ B i ∪ B j := by
      intro p _
      simp only [Finset.mem_union]
      by_contra! hh
      exact hn ⟨p, hh⟩
    have hle := Finset.card_le_card sub
    have hu := Finset.card_union_le (B i) (B j)
    simp only [Finset.card_univ, Fintype.card_fin] at hle
    rw [size, size] at hu
    omega
  have misses (p : Fin 157) : ∃ i, p ∉ B i := by
    by_contra! hall
    choose f hf using fun i => third_point (B i) (size i) p p
    have inj : Function.Injective f := by
      intro i j h
      by_contra hij
      exact (hf i).2.1 ((meet i j hij).unique ⟨(hf i).1, h ▸ (hf j).1⟩ ⟨hall i, hall j⟩)
    obtain ⟨i, hi⟩ := (Finite.surjective_of_injective inj) p
    exact (hf i).2.1 hi
  letI : HasPoints (Fin 157) (Fin 157) := {
    exists_point := fun l => (outside l l).imp fun _ h => h.1
    exists_line := misses
    eq_or_eq := by
      intro p q l m hpl hql hpm hqm
      by_cases h : l = m
      · exact Or.inr h
      · exact Or.inl ((meet l m h).unique ⟨hpl, hpm⟩ ⟨hql, hqm⟩)
    mkPoint := fun {l m} h => (meet l m h).choose
    mkPoint_ax := fun {l m} h => (meet l m h).choose_spec.1 }
  letI := HasPoints.hasLines (P := Fin 157) (L := Fin 157) rfl
  obtain ⟨p, hp, _⟩ := meet 0 1 (by decide)
  obtain ⟨l, hl⟩ := misses p
  have hl0 : l ≠ 0 := by rintro rfl; exact hl hp.1
  obtain ⟨z, hz, _⟩ := meet l 0 hl0
  obtain ⟨q, hq, hqz, hqp⟩ := third_point (B 0) (size 0) z p
  obtain ⟨u, hu⟩ := outside 0 1
  letI pp : ProjectivePlane (Fin 157) (Fin 157) :=
    { (inferInstance : HasPoints (Fin 157) (Fin 157)),
      (inferInstance : HasLines (Fin 157) (Fin 157)) with
      exists_config := ⟨u, p, q, l, 0, 1, hu.1, hu.2, hl, hp.1, hp.2,
        fun h => hqz ((meet l 0 hl0).unique ⟨h, hq⟩ hz), hq,
        fun h => hqp ((meet 0 1 (by decide)).unique ⟨hq, h⟩ hp)⟩ }
  refine ⟨Fin 157, Fin 157, inferInstance, inferInstance, inferInstance, pp, ?_⟩
  have hc := ProjectivePlane.pointCount_eq (Fin 157) (0 : Fin 157)
  have hk : pointCount (Fin 157) (0 : Fin 157) = 13 := by
    change Nat.card {p : Fin 157 // p ∈ B 0} = 13
    simpa only [Nat.card_eq_fintype_card, Fintype.card_coe] using size 0
  change ProjectivePlane.order (Fin 157) (Fin 157) = 12
  omega

theorem main : H1 → H2 → type_of% @Erdos723.erdos_723.variants.eq_12 := by
  rintro ⟨s, B, rows, cols, transversals, pairs⟩ complete
  obtain ⟨L, size, meet⟩ := complete s B rows cols transversals pairs
  exact plane_of_blocks L size meet

end OMA.R_Erdos723_erdos_723_variants_eq_12_R3
