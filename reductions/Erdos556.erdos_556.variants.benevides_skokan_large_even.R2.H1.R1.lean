import OMAReductions.R_Erdos556_erdos_556_variants_benevides_skokan_large_even_R2

-- Reduction Erdos556.erdos_556.variants.benevides_skokan_large_even.R2.H1.R1
-- of step Erdos556.erdos_556.variants.benevides_skokan_large_even.R2.H1
-- Credit: @tgg6956g2z-bot

/-!
# `R2.H1` from Lemma 5, Lemma 7 and stability, stated exactly as in `R1`

`R2.H2` (EC2 absorption) is proved, so the R2 route needs only EC1 absorption (Lemma 5 of
[BeSk09]), EC3 absorption (Lemma 7) and the 3-colour stability theorem. These are already open
as steps `R1.H1`, `R1.H3` and `R1.H4` of the sibling reduction
`Erdos556.erdos_556.variants.benevides_skokan_large_even.R1`. The three hypotheses below are
copied from that file character for character (`H1` = `R1.H1`, `H2` = `R1.H3`, `H3` = `R1.H4`),
so a proof of either copy is a proof of the other, and no new open lemma is created: proving
`R1.H1`, `R1.H3`, `R1.H4` closes the problem through R2 without `R1.H2`.

`main` translates the `Fin (2 * n)`, `Even n`, `C_n`, ordered-pair-count encoding of R1 into the
`Fin (4 * m)`, `C_{2m}`, neighbourhood-sum encoding of `R2.H1` (with `n = 2m`, the identity colour
permutation, and the symmetry of adjacency for the green and blue pairs of EC2).
-/

open Filter SimpleGraph
open scoped Fin.NatCast

namespace OMA.R_Erdos556_erdos_556_variants_benevides_skokan_large_even_R2_H1_R1


lemma ncard_eq {V : Type*} [Fintype V] (p : V → Prop) [DecidablePred p] :
    Nat.card {v // p v} = (Finset.univ.filter p).card := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

lemma pairs_eq {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (p q : V → Prop) [DecidablePred p] [DecidablePred q] :
    (Nat.card {e : V × V // p e.1 ∧ q e.2 ∧ G.Adj e.1 e.2} : ℝ) =
      ∑ x ∈ Finset.univ.filter p, (((Finset.univ.filter q).filter (G.Adj x)).card : ℝ) := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, ← Nat.cast_sum]
  congr 1
  rw [Finset.card_filter, Fintype.sum_prod_type, Finset.sum_filter]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  by_cases hx : p x
  · simp only [hx, true_and, if_true, Finset.card_filter, Finset.sum_filter]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    by_cases hy : q y <;> simp [hy]
  · simp [hx]

lemma pairs_symm {V : Type*} (G : SimpleGraph V) (p q : V → Prop) :
    Nat.card {e : V × V // p e.1 ∧ q e.2 ∧ G.Adj e.1 e.2} =
      Nat.card {e : V × V // q e.1 ∧ p e.2 ∧ G.Adj e.1 e.2} :=
  Nat.card_congr
    { toFun := fun e => ⟨e.1.swap, e.2.2.1, e.2.1, e.2.2.2.symm⟩
      invFun := fun e => ⟨e.1.swap, e.2.2.1, e.2.1, e.2.2.2.symm⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

lemma dense_of {A B s : ℝ} {α α' : ℝ} (hαα : α' ≤ α) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (h : (1 - α') * A * B ≤ s) : (1 - α) * A * B ≤ s := by
  have : 0 ≤ A * B := mul_nonneg hA hB
  nlinarith

/-- Benevides–Skokan, Lemma 5 (colourings of type EC1). Blocks `A, B, C, D` are `f⁻¹ 0, …, f⁻¹ 3`
on the `2n` vertices; colours `0, 1, 2` are red, green, blue. There is `α₀ > 0` such that for
every `0 < α ≤ α₀`, for all large even `n`, every 3-colouring of `K_{2n}` with every block of size
`≥ (1 - α)·2n/4` and with red `[A,B]`, `[C,D]`, green `[A,D]`, `[B,C]`, blue `[A,C]`, `[B,D]`
all `(1 - α)`-dense contains a monochromatic `C_n`. -/
def H1 : Prop :=
  ∃ α₀ : ℝ, 0 < α₀ ∧ ∀ α : ℝ, 0 < α → α ≤ α₀ →
    ∀ᶠ n : ℕ in atTop, Even n →
      ∀ c : Fin 3 → SimpleGraph (Fin (2 * n)), (⊤ : SimpleGraph (Fin (2 * n))).IsEdgeColouring c →
        ∀ f : Fin (2 * n) → Fin 4,
          (∀ j, (1 - α) * n / 2 ≤ (Nat.card {v // f v = j} : ℝ)) →
          (∀ k S T, (k, S, T) ∈ ([(0, {0}, {1}), (0, {2}, {3}), (1, {0}, {3}), (1, {1}, {2}), (2, {0}, {2}), (2, {1}, {3})] : List (Fin 3 × Finset (Fin 4) × Finset (Fin 4))) →
            (1 - α) * Nat.card {v // f v ∈ S} * Nat.card {v // f v ∈ T} ≤
              (Nat.card {e : Fin (2 * n) × Fin (2 * n) // f e.1 ∈ S ∧ f e.2 ∈ T ∧ (c k).Adj e.1 e.2} : ℝ)) →
          ∃ i, cycleGraph n ⊑ c i

/-- Benevides–Skokan, Lemma 7 with `c₁ = 4/5`, `c₂ = 3/10` (colourings of type EC3): there is
`μ₀ > 0` such that for every `0 < μ ≤ μ₀` there is `δ₀ > 0` such that, for all large even `n`
and every `0 < δ ≤ δ₀`, every 3-colouring of `K_{2n}` of type `EC3(μ, 4/5, 3/10, δ)`
(`|A|, |B|, |C| ≥ (1 - c₁μ)·2n/4`, `|D| ≥ μ·2n/4`, `|A| ≥ max(|B|, |C|, |D|) + μ·2n/4`,
`|A ∪ D| ≤ (1 + c₂μ)·2n/2`, and the six EC1 pairs `(1 - δ)`-dense) contains a monochromatic `C_n`. -/
def H2 : Prop :=
  ∃ μ₀ : ℝ, 0 < μ₀ ∧ ∀ μ : ℝ, 0 < μ → μ ≤ μ₀ → ∃ δ₀ : ℝ, 0 < δ₀ ∧
    ∀ᶠ n : ℕ in atTop, Even n → ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      ∀ c : Fin 3 → SimpleGraph (Fin (2 * n)), (⊤ : SimpleGraph (Fin (2 * n))).IsEdgeColouring c →
        ∀ f : Fin (2 * n) → Fin 4,
          (let a : Fin 4 → ℝ := (fun j => Nat.card {v // f v = j});
            (1 - 4 / 5 * μ) * n / 2 ≤ min (a 0) (min (a 1) (a 2)) ∧ μ * n / 2 ≤ a 3 ∧
            max (a 1) (max (a 2) (a 3)) + μ * n / 2 ≤ a 0 ∧ a 0 + a 3 ≤ (1 + 3 / 10 * μ) * n) →
          (∀ k S T, (k, S, T) ∈ ([(0, {0}, {1}), (0, {2}, {3}), (1, {0}, {3}), (1, {1}, {2}), (2, {0}, {2}), (2, {1}, {3})] : List (Fin 3 × Finset (Fin 4) × Finset (Fin 4))) →
            (1 - δ) * Nat.card {v // f v ∈ S} * Nat.card {v // f v ∈ T} ≤
              (Nat.card {e : Fin (2 * n) × Fin (2 * n) // f e.1 ∈ S ∧ f e.2 ∈ T ∧ (c k).Adj e.1 e.2} : ℝ)) →
          ∃ i, cycleGraph n ⊑ c i

/-- Stability (Benevides–Skokan, Theorem 4 applied to the reduced graph of the regularity
lemma, as in their Section 5): for small `α` and `μ₁` there is `μ < μ₁` such that, for every
`δ > 0` and all large even `n`, every 3-colouring of `K_{2n}` contains a monochromatic `C_n`
or is of type `EC1(α, α)`, `EC2(α, α)` or `EC3(μ, 4/5, 3/10, δ)`. -/
def H3 : Prop :=
  ∃ α₀ μ₀ : ℝ, 0 < α₀ ∧ 0 < μ₀ ∧ ∀ α : ℝ, 0 < α → α ≤ α₀ → ∀ μ₁ : ℝ, 0 < μ₁ → μ₁ ≤ μ₀ →
    ∃ μ : ℝ, 0 < μ ∧ μ < μ₁ ∧ ∀ δ : ℝ, 0 < δ →
    ∀ᶠ n : ℕ in atTop, Even n →
      ∀ c : Fin 3 → SimpleGraph (Fin (2 * n)), (⊤ : SimpleGraph (Fin (2 * n))).IsEdgeColouring c →
        (∃ i, cycleGraph n ⊑ c i) ∨
        (∃ f : Fin (2 * n) → Fin 4,
          (∀ j, (1 - α) * n / 2 ≤ (Nat.card {v // f v = j} : ℝ)) ∧
          (∀ k S T, (k, S, T) ∈ ([(0, {0}, {1}), (0, {2}, {3}), (1, {0}, {3}), (1, {1}, {2}), (2, {0}, {2}), (2, {1}, {3})] : List (Fin 3 × Finset (Fin 4) × Finset (Fin 4))) →
            (1 - α) * Nat.card {v // f v ∈ S} * Nat.card {v // f v ∈ T} ≤
              (Nat.card {e : Fin (2 * n) × Fin (2 * n) // f e.1 ∈ S ∧ f e.2 ∈ T ∧ (c k).Adj e.1 e.2} : ℝ))) ∨
        (∃ f : Fin (2 * n) → Fin 4,
          (∀ j, (1 - α) * n / 2 ≤ (Nat.card {v // f v = j} : ℝ)) ∧
          (∀ k S T, (k, S, T) ∈ ([(0, {0}, {1}), (1, {0, 1}, {2}), (2, {0, 1}, {3})] : List (Fin 3 × Finset (Fin 4) × Finset (Fin 4))) →
            (1 - α) * Nat.card {v // f v ∈ S} * Nat.card {v // f v ∈ T} ≤
              (Nat.card {e : Fin (2 * n) × Fin (2 * n) // f e.1 ∈ S ∧ f e.2 ∈ T ∧ (c k).Adj e.1 e.2} : ℝ))) ∨
        (∃ f : Fin (2 * n) → Fin 4,
          (let a : Fin 4 → ℝ := (fun j => Nat.card {v // f v = j});
            (1 - 4 / 5 * μ) * n / 2 ≤ min (a 0) (min (a 1) (a 2)) ∧ μ * n / 2 ≤ a 3 ∧
            max (a 1) (max (a 2) (a 3)) + μ * n / 2 ≤ a 0 ∧ a 0 + a 3 ≤ (1 + 3 / 10 * μ) * n) ∧
          (∀ k S T, (k, S, T) ∈ ([(0, {0}, {1}), (0, {2}, {3}), (1, {0}, {3}), (1, {1}, {2}), (2, {0}, {2}), (2, {1}, {3})] : List (Fin 3 × Finset (Fin 4) × Finset (Fin 4))) →
            (1 - δ) * Nat.card {v // f v ∈ S} * Nat.card {v // f v ∈ T} ≤
              (Nat.card {e : Fin (2 * n) × Fin (2 * n) // f e.1 ∈ S ∧ f e.2 ∈ T ∧ (c k).Adj e.1 e.2} : ℝ)))

theorem main : H1 → H2 → H3 →
    OMA.R_Erdos556_erdos_556_variants_benevides_skokan_large_even_R2.H1 := by
  intro h1 h3 h4 α hα
  obtain ⟨a1, ha1, h1⟩ := h1
  obtain ⟨u3, hu3, h3⟩ := h3
  obtain ⟨a4, u4, ha4, hu4, h4⟩ := h4
  set α' : ℝ := min α (min a1 a4) with hα'def
  have hα' : 0 < α' := lt_min hα (lt_min ha1 ha4)
  have hα'α : α' ≤ α := min_le_left _ _
  obtain ⟨μ, hμ, hμ1, h4⟩ := h4 α' hα' ((min_le_right _ _).trans (min_le_right _ _))
    (min u3 u4) (lt_min hu3 hu4) (min_le_right _ _)
  obtain ⟨δ, hδ, h3⟩ := h3 μ hμ (hμ1.le.trans (min_le_left _ _))
  have e1 := h1 α' hα' ((min_le_right _ _).trans (min_le_left _ _))
  have e4 := h4 δ hδ
  obtain ⟨N, hN⟩ := eventually_atTop.1 (e1.and (h3.and e4))
  refine eventually_atTop.2 ⟨N, fun m hm => ?_⟩
  obtain ⟨h1n, h3n, h4n⟩ := hN (2 * m) (by omega)
  have hev : Even (2 * m) := even_two_mul m
  rw [show 4 * m = 2 * (2 * m) by ring]
  intro c _ hc
  rcases h4n hev c hc with h | ⟨f, hs, hd⟩ | ⟨f, hs, hd⟩ | ⟨f, hs, hd⟩
  · exact Or.inl h
  · exact Or.inl (h1n hev c hc f hs hd)
  · right
    refine ⟨f, 1, ?_⟩
    have hU : (Finset.univ.filter (fun v => f v = 0) ∪ Finset.univ.filter (fun v => f v = 1)) =
        Finset.univ.filter (fun v => f v ∈ ({0, 1} : Finset (Fin 4))) := by
      ext v; simp
    have hW : ∀ j : Fin 4, Finset.univ.filter (fun v => f v = j) =
        Finset.univ.filter (fun v => f v ∈ ({j} : Finset (Fin 4))) := by
      intro j; ext v; simp
    have d0 := hd 0 {0} {1} (by simp)
    have d1 := hd 1 {0, 1} {2} (by simp)
    have d2 := hd 2 {0, 1} {3} (by simp)
    rw [pairs_symm (c 1) (fun v => f v ∈ ({0, 1} : Finset (Fin 4)))
      (fun v => f v ∈ ({2} : Finset (Fin 4)))] at d1
    rw [pairs_symm (c 2) (fun v => f v ∈ ({0, 1} : Finset (Fin 4)))
      (fun v => f v ∈ ({3} : Finset (Fin 4)))] at d2
    rw [pairs_eq (c 0) (fun v => f v ∈ ({0} : Finset (Fin 4)))
      (fun v => f v ∈ ({1} : Finset (Fin 4)))] at d0
    rw [pairs_eq (c 1) (fun v => f v ∈ ({2} : Finset (Fin 4)))
      (fun v => f v ∈ ({0, 1} : Finset (Fin 4)))] at d1
    rw [pairs_eq (c 2) (fun v => f v ∈ ({3} : Finset (Fin 4)))
      (fun v => f v ∈ ({0, 1} : Finset (Fin 4)))] at d2
    simp only [ncard_eq] at d0 d1 d2 hs
    simp only [Equiv.Perm.one_apply]
    refine ⟨fun j => ?_, ?_, ?_, ?_⟩
    · have := hs j
      push_cast at this
      have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      nlinarith
    · rw [hW 0, hW 1]
      exact dense_of hα'α (Nat.cast_nonneg _) (Nat.cast_nonneg _) d0
    · rw [hW 2, hU]
      rw [mul_right_comm] at d1
      exact dense_of hα'α (Nat.cast_nonneg _) (Nat.cast_nonneg _) d1
    · rw [hW 3, hU]
      rw [mul_right_comm] at d2
      exact dense_of hα'α (Nat.cast_nonneg _) (Nat.cast_nonneg _) d2
  · exact Or.inl (h3n hev δ hδ le_rfl c hc f hs hd)

end OMA.R_Erdos556_erdos_556_variants_benevides_skokan_large_even_R2_H1_R1
