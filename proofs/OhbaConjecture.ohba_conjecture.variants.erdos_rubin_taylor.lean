import FormalConjectures.Wikipedia.OhbaConjecture

open Finset

-- Problem: Ohba's conjecture (2002; proved by Noel, Reed and Wu 2015) — erdos rubin taylor
-- Upstream: formal-conjectures FormalConjectures/Wikipedia/OhbaConjecture.lean:74 (declaration OhbaConjecture.ohba_conjecture.variants.erdos_rubin_taylor)
-- Credit: @LordMike (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMA

open Finset

/-- List colouring of `K_{2,...,2}` on the parts in `s`: if some part has a common colour in its
two lists, use it on that part and recurse; otherwise the lists within each part are disjoint
and Hall's theorem gives pairwise distinct colours. -/
lemma ert_aux {ι : Type} [DecidableEq ι] : ∀ (n : ℕ) (s : Finset ι), s.card = n →
    ∀ L : ι → Fin 2 → Finset ℕ, (∀ i ∈ s, ∀ a, n ≤ (L i a).card) →
    ∃ c : ι → Fin 2 → ℕ, (∀ i ∈ s, ∀ a, c i a ∈ L i a) ∧
      ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ∀ a b, c i a ≠ c j b := by
  intro n
  induction n with
  | zero =>
    intro s hs L _
    rw [Finset.card_eq_zero] at hs
    subst hs
    exact ⟨fun _ _ => 0, by simp, by simp⟩
  | succ n ih =>
    intro s hs L hL
    by_cases hA : ∃ i ∈ s, ∃ x, x ∈ L i 0 ∧ x ∈ L i 1
    · obtain ⟨i, hi, x, hx0, hx1⟩ := hA
      obtain ⟨c, hc1, hc2⟩ := ih (s.erase i) (by rw [card_erase_of_mem hi, hs]; rfl)
        (fun j a => (L j a).erase x) (by
          intro j hj a
          have h1 := hL j (mem_of_mem_erase hj) a
          have h2 := pred_card_le_card_erase (s := L j a) (a := x)
          omega)
      refine ⟨Function.update c i (fun _ => x), ?_, ?_⟩
      · intro j hj a
        by_cases hji : j = i
        · subst hji
          simp only [Function.update_self]
          fin_cases a <;> assumption
        · rw [Function.update_of_ne hji]
          exact mem_of_mem_erase (hc1 j (mem_erase.mpr ⟨hji, hj⟩) a)
      · intro j hj l hl hjl a b
        by_cases hji : j = i
        · subst hji
          have hlj : l ≠ j := Ne.symm hjl
          rw [Function.update_self, Function.update_of_ne hlj]
          have h := hc1 l (mem_erase.mpr ⟨hlj, hl⟩) b
          exact fun h' => (ne_of_mem_erase h) h'.symm
        · by_cases hli : l = i
          · subst hli
            rw [Function.update_self, Function.update_of_ne hji]
            exact ne_of_mem_erase (hc1 j (mem_erase.mpr ⟨hji, hj⟩) a)
          · rw [Function.update_of_ne hji, Function.update_of_ne hli]
            exact hc2 j (mem_erase.mpr ⟨hji, hj⟩) l (mem_erase.mpr ⟨hli, hl⟩) hjl a b
    · push Not at hA
      have hall := (all_card_le_biUnion_card_iff_exists_injective
        (fun v : {i // i ∈ s} × Fin 2 => L v.1.1 v.2)).mp ?_
      · obtain ⟨f, hf, hfm⟩ := hall
        refine ⟨fun i a => if h : i ∈ s then f (⟨i, h⟩, a) else 0, ?_, ?_⟩
        · intro i hi a
          simp only [dif_pos hi]
          exact hfm (⟨i, hi⟩, a)
        · intro i hi j hj hij a b
          simp only [dif_pos hi, dif_pos hj]
          intro h
          have h' := hf h
          simp only [Prod.mk.injEq, Subtype.mk.injEq] at h'
          exact hij h'.1
      · intro S
        by_cases hS : ∃ i : {i // i ∈ s}, (i, (0 : Fin 2)) ∈ S ∧ (i, (1 : Fin 2)) ∈ S
        · obtain ⟨i, h0, h1⟩ := hS
          have hdisj : Disjoint (L i.1 0) (L i.1 1) :=
            disjoint_left.mpr (fun x hx0 hx1 => hA i.1 i.2 x hx0 hx1)
          have h1' : (L i.1 0 ∪ L i.1 1).card ≤
              (S.biUnion (fun v : {i // i ∈ s} × Fin 2 => L v.1.1 v.2)).card :=
            card_le_card (union_subset
              (subset_biUnion_of_mem (fun v : {i // i ∈ s} × Fin 2 => L v.1.1 v.2) h0)
              (subset_biUnion_of_mem (fun v : {i // i ∈ s} × Fin 2 => L v.1.1 v.2) h1))
          rw [card_union_of_disjoint hdisj] at h1'
          have hScard : S.card ≤ (n + 1) * 2 := by
            calc S.card ≤ Fintype.card ({i // i ∈ s} × Fin 2) := card_le_univ S
              _ = (n + 1) * 2 := by simp [hs]
          have e0 := hL i.1 i.2 0
          have e1 := hL i.1 i.2 1
          omega
        · push Not at hS
          rcases S.eq_empty_or_nonempty with rfl | ⟨v, hv⟩
          · simp
          · have h1 : (L v.1.1 v.2).card ≤
                (S.biUnion (fun v : {i // i ∈ s} × Fin 2 => L v.1.1 v.2)).card :=
              card_le_card
                (subset_biUnion_of_mem (fun v : {i // i ∈ s} × Fin 2 => L v.1.1 v.2) hv)
            have hinj : Set.InjOn (Prod.fst : {i // i ∈ s} × Fin 2 → {i // i ∈ s}) S := by
              rintro ⟨i, a⟩ ha ⟨j, b⟩ hb h
              simp only at h
              subst h
              have hi := hS i
              fin_cases a <;> fin_cases b <;> simp_all
            have h2 : S.card ≤ n + 1 := by
              calc S.card = (S.image Prod.fst).card := (Finset.card_image_of_injOn hinj).symm
                _ ≤ Fintype.card {i // i ∈ s} := card_le_univ _
                _ = n + 1 := by simp [hs]
            have e := hL v.1.1 v.1.2 v.2
            omega

end OMA

theorem OMA.solution : type_of% @OhbaConjecture.ohba_conjecture.variants.erdos_rubin_taylor := by
  intro k L hL
  obtain ⟨c, hc1, hc2⟩ := OMA.ert_aux k (univ : Finset (Fin k)) (by simp)
    (fun i a => L ⟨i, a⟩) (fun i _ a => (hL ⟨i, a⟩).ge)
  refine ⟨fun v => c v.1 v.2, fun v => hc1 v.1 (mem_univ _) v.2, ?_⟩
  intro u v huv
  exact hc2 u.1 (mem_univ _) v.1 (mem_univ _) huv u.2 v.2
