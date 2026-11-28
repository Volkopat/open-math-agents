import OMAReductions.R_wp_frankl_conjecture_R1

-- Step wp-frankl-conjecture.R1.H1: hypothesis H1 of reduction wp-frankl-conjecture.R1
-- Credit: @nnkostov

/-!
# Sarvate-Renaud Case of Frankl's Union-Closed Sets Conjecture (Set Version)

If a finite union-closed family `F : Finset (Set α)` contains a set `S = {x, y}`
(covering both singletons `x = y` and pairs `x ≠ y`), then either `x` or `y` belongs
to at least half of the sets in `F`. The map `A ↦ A ∪ {x, y}` embeds the subfamily
containing neither `x` nor `y` injectively into the subfamily containing both,
yielding `|F| ≤ |F_x| + |F_y|`.
-/

open Classical in
theorem OMA.solution : OMA.R_wp_frankl_conjecture_R1.H1 := by
  intro α F huc ⟨S, hSF, x, y, hSxy⟩
  subst hSxy
  let Fx := F.filter (fun A => x ∈ A)
  let Fnx := F.filter (fun A => x ∉ A)
  let Fy := F.filter (fun A => y ∈ A)
  let F11 := Fx.filter (fun A => y ∈ A)
  let F10 := Fx.filter (fun A => y ∉ A)
  let F01 := Fnx.filter (fun A => y ∈ A)
  let F00 := Fnx.filter (fun A => y ∉ A)
  have hsplit : Fx.card + Fnx.card = F.card :=
    Finset.card_filter_add_card_filter_not (s := F) (fun A => x ∈ A)
  have hsplitx : F11.card + F10.card = Fx.card :=
    Finset.card_filter_add_card_filter_not (s := Fx) (fun A => y ∈ A)
  have hsplitnx : F01.card + F00.card = Fnx.card :=
    Finset.card_filter_add_card_filter_not (s := Fnx) (fun A => y ∈ A)
  have hsplity : F11.card + F01.card = Fy.card := by
    have h := Finset.card_filter_add_card_filter_not (s := Fy) (fun A => x ∈ A)
    have h1 : Fy.filter (fun A => x ∈ A) = F11 := by
      ext A
      simp only [Fy, F11, Fx, Finset.mem_filter]
      tauto
    have h2 : Fy.filter (fun A => x ∉ A) = F01 := by
      ext A
      simp only [Fy, F01, Fnx, Finset.mem_filter]
      tauto
    rw [h1, h2] at h
    exact h
  have hinj : F00.card ≤ F11.card := by
    refine Finset.card_le_card_of_injOn (fun A => A ∪ {x, y}) ?_ ?_
    · intro A hA
      simp only [F00, F11, Fnx, Fx, Finset.mem_coe, Finset.mem_filter] at hA ⊢
      refine ⟨⟨huc A hA.1.1 {x, y} hSF, ?_⟩, ?_⟩
      · exact Or.inr (Set.mem_insert x {y})
      · exact Or.inr (Set.mem_insert_of_mem x (Set.mem_singleton y))
    · intro A hA B hB hAB
      simp only [F00, Fnx, Finset.mem_coe, Finset.mem_filter] at hA hB
      ext z
      by_cases hzx : z = x
      · subst hzx
        exact iff_of_false hA.1.2 hB.1.2
      · by_cases hzy : z = y
        · subst hzy
          exact iff_of_false hA.2 hB.2
        · have hz := Set.ext_iff.mp hAB z
          simpa only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, hzx, hzy,
            or_self, or_false] using hz
  by_cases hx : F.card ≤ 2 * Fx.card
  · exact ⟨x, hx⟩
  · have hfy : F.card ≤ 2 * Fy.card := by omega
    exact ⟨y, hfy⟩
