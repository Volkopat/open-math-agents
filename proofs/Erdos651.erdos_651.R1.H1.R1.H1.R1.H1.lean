import OMAReductions.R_Erdos651_erdos_651_R1_H1_R1_H1_R1

/-!
Finite two-color Ramsey for ordered triples. The induction on uniformity
uses the link coloring at one vertex and allows separate sizes for the
two colors.
-/

open Finset

private def monochromatic {V : Type} (paint : Finset V → Bool) (r n : ℕ)
    (color : Bool) (S : Finset V) : Prop :=
  ∃ T ⊆ S, T.card = n ∧ ∀ E ⊆ T, E.card = r → paint E = color

private theorem mono_mono {V : Type} {paint : Finset V → Bool} {r n : ℕ} {c : Bool}
    {S S' : Finset V} (hs : S ⊆ S') (h : monochromatic paint r n c S) :
    monochromatic paint r n c S' := by
  obtain ⟨T, hT, hn, h'⟩ := h
  exact ⟨T, hT.trans hs, hn, h'⟩

private theorem mono_zero {V : Type} (paint : Finset V → Bool) (r : ℕ)
    (c : Bool) (S : Finset V) : monochromatic paint (r + 1) 0 c S := by
  refine ⟨∅, empty_subset _, card_empty, ?_⟩
  intro E hE hcard
  have he : E = ∅ := subset_empty.mp hE
  simp [he] at hcard

private theorem mono_extend {V : Type} [DecidableEq V] {paint : Finset V → Bool}
    {S T : Finset V} {v : V} {r k : ℕ} {c : Bool}
    (hv : v ∈ S) (hTS : T ⊆ S.erase v) (hcard : T.card = k)
    (hmono : ∀ E ⊆ T, E.card = r + 1 → paint E = c)
    (hlink : ∀ E ⊆ T, E.card = r → paint (insert v E) = c) :
    monochromatic paint (r + 1) (k + 1) c S := by
  have hvT : v ∉ T := fun h => notMem_erase v S (hTS h)
  refine ⟨insert v T, insert_subset hv (hTS.trans (erase_subset _ _)),
    by rw [card_insert_of_notMem hvT, hcard], ?_⟩
  intro E hE hEc
  by_cases hvE : v ∈ E
  · have hsub : E.erase v ⊆ T := by
      intro x hx
      obtain ⟨hxv, hxE⟩ := mem_erase.mp hx
      exact (mem_insert.mp (hE hxE)).resolve_left hxv
    have hsmall : (E.erase v).card = r := by rw [card_erase_of_mem hvE, hEc]; omega
    simpa only [insert_erase hvE] using hlink (E.erase v) hsub hsmall
  · apply hmono E _ hEc
    intro x hx
    exact (mem_insert.mp (hE hx)).resolve_left fun he => hvE (he ▸ hx)

private theorem finite_ramsey (r : ℕ) : ∀ k l : ℕ, ∃ N : ℕ,
    ∀ {V : Type} [DecidableEq V] (S : Finset V), N ≤ S.card →
      ∀ paint : Finset V → Bool,
        monochromatic paint r k true S ∨ monochromatic paint r l false S := by
  classical
  induction r with
  | zero =>
    intro k l
    refine ⟨max k l, ?_⟩
    intro V _ S hS paint
    cases h : paint ∅
    · right
      obtain ⟨T, hTS, hT⟩ := exists_subset_card_eq ((le_max_right k l).trans hS)
      exact ⟨T, hTS, hT, fun E _ hE => (card_eq_zero.mp hE).symm ▸ h⟩
    · left
      obtain ⟨T, hTS, hT⟩ := exists_subset_card_eq ((le_max_left k l).trans hS)
      exact ⟨T, hTS, hT, fun E _ hE => (card_eq_zero.mp hE).symm ▸ h⟩
  | succ r lower =>
    intro k
    induction k with
    | zero =>
      intro l
      exact ⟨0, fun S _ paint => Or.inl (mono_zero paint r true S)⟩
    | succ k leftIH =>
      intro l
      induction l with
      | zero => exact ⟨0, fun S _ paint => Or.inr (mono_zero paint r false S)⟩
      | succ l rightIH =>
        obtain ⟨A, hA⟩ := leftIH (l + 1)
        obtain ⟨B, hB⟩ := rightIH
        obtain ⟨N, hN⟩ := lower A B
        refine ⟨N + 1, ?_⟩
        intro V _ S hS paint
        obtain ⟨v, hv⟩ := card_pos.mp (by omega : 0 < S.card)
        have hEr : N ≤ (S.erase v).card := by rw [card_erase_of_mem hv]; omega
        let link (E : Finset V) := paint (insert v E)
        rcases hN (S.erase v) hEr link with hlink | hlink
        · obtain ⟨L, hLE, hL, hwhole⟩ := hlink
          rcases hA L hL.ge paint with hred | hblue
          · obtain ⟨T, hTL, hT, hred⟩ := hred
            exact Or.inl (mono_extend hv (hTL.trans hLE) hT hred
              (fun E he hh => hwhole E (he.trans hTL) hh))
          · exact Or.inr (mono_mono (hLE.trans (erase_subset _ _)) hblue)
        · obtain ⟨L, hLE, hL, hwhole⟩ := hlink
          rcases hB L hL.ge paint with hred | hblue
          · exact Or.inl (mono_mono (hLE.trans (erase_subset _ _)) hred)
          · obtain ⟨T, hTL, hT, hblue⟩ := hblue
            exact Or.inr (mono_extend hv (hTL.trans hLE) hT hblue
              (fun E he hh => hwhole E (he.trans hTL) hh))

private noncomputable def colorOfSet {V : Type} [LinearOrder V]
    (C : V → V → V → Bool) (E : Finset V) : Bool :=
  if h : E.card = 3 then
    C (E.orderEmbOfFin h 0) (E.orderEmbOfFin h 1) (E.orderEmbOfFin h 2)
  else false

private theorem colorOfSet_triple {V : Type} [LinearOrder V] (C : V → V → V → Bool)
    {a b c : V} (hab : a < b) (hbc : b < c) :
    colorOfSet C {a, b, c} = C a b c := by
  have hcard : ({a, b, c} : Finset V).card = 3 :=
    card_eq_three.mpr ⟨a, b, c, hab.ne, (hab.trans hbc).ne, hbc.ne, rfl⟩
  let v : Fin 3 → V := ![a, b, c]
  have vmono : StrictMono v := by
    apply Fin.strictMono_iff_lt_succ.mpr
    intro j
    fin_cases j
    · exact hab
    · exact hbc
  have hmem (j : Fin 3) : v j ∈ ({a, b, c} : Finset V) := by
    fin_cases j <;> simp [v]
  have heq := (orderEmbOfFin_unique hcard hmem vmono).symm
  unfold colorOfSet
  rw [dif_pos hcard]
  change C (({a, b, c} : Finset V).orderEmbOfFin hcard 0)
    (({a, b, c} : Finset V).orderEmbOfFin hcard 1)
    (({a, b, c} : Finset V).orderEmbOfFin hcard 2) = _
  rw [heq]
  rfl

theorem OMA.solution : OMA.R_Erdos651_erdos_651_R1_H1_R1_H1_R1.H1 := by
  intro m
  classical
  obtain ⟨k, hk⟩ := finite_ramsey 3 m m
  refine ⟨k, ?_⟩
  intro C
  obtain ⟨b, hb⟩ : ∃ b, monochromatic (colorOfSet C) 3 m b (univ : Finset (Fin k)) := by
    rcases hk univ (by simp) (colorOfSet C) with h | h
    · exact ⟨true, h⟩
    · exact ⟨false, h⟩
  obtain ⟨T, _, hTcard, hT⟩ := hb
  let f := T.orderEmbOfFin hTcard
  refine ⟨f, b, f.strictMono, ?_⟩
  intro i j l hij hjl
  have h1 := f.strictMono hij
  have h2 := f.strictMono hjl
  have hsub : ({f i, f j, f l} : Finset (Fin k)) ⊆ T := by
    intro x hx
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> exact T.orderEmbOfFin_mem hTcard _
  have hcard : ({f i, f j, f l} : Finset (Fin k)).card = 3 :=
    card_eq_three.mpr ⟨f i, f j, f l, h1.ne, (h1.trans h2).ne, h2.ne, rfl⟩
  exact (colorOfSet_triple C h1 h2).symm.trans (hT _ hsub hcard)

