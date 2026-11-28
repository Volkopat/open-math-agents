import OMAStatements.S_mo_356664
import Mathlib

open OMA.S_mo_356664

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_356664.main) := by
  intro h
  set a : Fin 6 → Fin 6 := ![0, 0, 0, 1, 2, 4] with ha
  have haC : a ∈ C 6 := by
    refine ⟨fun x y hxy => ?_, fun x => ?_⟩
    · revert x y; simp only [ha]; decide
    · revert x; simp only [ha]; decide
  have hnil : IsRNilpotent a 3 := by
    refine ⟨?_, ?_⟩
    · intro x; revert x; simp only [ha]; decide
    · intro k hk
      interval_cases k
      · intro hz; have := hz 1; simp at this
      · intro hz; have := hz 3; simp [ha] at this
      · intro hz; have := hz 5; simp [ha] at this
  obtain ⟨e⟩ := h 6 3 a haC hnil
  -- the three elements of the sandwich
  set g : Fin 6 → Fin 6 → Fin 6 := fun v x => if x = 5 then v else 0 with hg
  have hS : sandwich a = (({g 0, g 1, g 2} : Finset (Fin 6 → Fin 6)) : Set (Fin 6 → Fin 6)) := by
    ext f
    simp only [sandwich, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨β, ⟨_, hdec⟩, rfl⟩
      have low : ∀ y : Fin 6, y ≤ 2 → a y = 0 := by simp only [ha]; decide
      have top : ∀ y : Fin 6, y ≤ 4 → a y = 0 ∨ a y = 1 ∨ a y = 2 := by simp only [ha]; decide
      have hax : ∀ x : Fin 6, x ≠ 5 → a x ≤ 2 := by simp only [ha]; decide
      have hfx : ∀ x : Fin 6, x ≠ 5 → a (β (a x)) = 0 :=
        fun x hx => low _ ((hdec _).trans (hax x hx))
      have h5 : a 5 = 4 := by simp [ha]
      have key : a ∘ β ∘ a = g (a (β 4)) := by
        funext x
        simp only [Function.comp, hg]
        by_cases hx : x = 5
        · subst hx; rw [h5]; simp
        · rw [if_neg hx, hfx x hx]
      rw [key]
      rcases top (β 4) (hdec 4) with h0 | h0 | h0 <;> rw [h0] <;> simp
    · rintro (rfl | rfl | rfl)
      · refine ⟨fun _ => 0, ⟨fun _ _ _ => le_rfl, fun x => Fin.zero_le x⟩, ?_⟩
        funext x; revert x; simp only [ha, hg]; decide
      · refine ⟨![0, 0, 0, 0, 3, 3], ⟨fun x y hxy => ?_, fun x => ?_⟩, ?_⟩
        · revert x y; decide
        · revert x; decide
        · funext x; revert x; simp only [ha, hg]; decide
      · refine ⟨![0, 0, 0, 0, 4, 4], ⟨fun x y hxy => ?_, fun x => ?_⟩, ?_⟩
        · revert x y; decide
        · revert x; decide
        · funext x; revert x; simp only [ha, hg]; decide
  have hN : N 3 = (({![0, 0, 0], ![0, 0, 1]} : Finset (Fin 3 → Fin 3)) : Set (Fin 3 → Fin 3)) := by
    ext α
    simp only [N, C, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨⟨hmono, hdec⟩, k, hk⟩
      have nofix : ∀ x : Fin 3, x ≠ 0 → α x ≠ x := by
        intro x hx hfix
        have := hk x
        rw [Function.iterate_fixed hfix] at this
        exact hx (Fin.ext this)
      have hm : ∀ x y : Fin 3, x ≤ y → α x ≤ α y := fun x y hxy => hmono hxy
      have h1 := nofix 1 (by decide)
      have h2 := nofix 2 (by decide)
      clear nofix hk hmono
      revert hm hdec h1 h2
      revert α
      decide
    · rintro (rfl | rfl)
      · refine ⟨⟨fun x y hxy => ?_, fun x => ?_⟩, 1, fun x => ?_⟩
        · revert x y; decide
        · revert x; decide
        · revert x; decide
      · refine ⟨⟨fun x y hxy => ?_, fun x => ?_⟩, 2, fun x => ?_⟩
        · revert x y; decide
        · revert x; decide
        · revert x; decide
  have c1 : Nat.card (sandwich a) = 3 := by
    rw [hS, Nat.card_coe_set_eq, Set.ncard_coe_finset]; decide
  have c2 : Nat.card (N 3) = 2 := by
    rw [hN, Nat.card_coe_set_eq, Set.ncard_coe_finset]; decide
  have := Nat.card_congr e
  omega
