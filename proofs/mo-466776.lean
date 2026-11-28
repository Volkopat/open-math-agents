import OMAStatements.S_mo_466776
import Mathlib

/-! The construction is from domotorp's MathOverflow answer. The finite
intersection test follows the approach of @SudharsanAnimations in PR #17789. -/

namespace OMA.WangThree

open OMA.S_mo_466776

private def tiles : Fin 3 → Fin 4 → ℕ :=
  ![![1, 2, 1, 2], ![1, 3, 1, 3], ![2, 3, 2, 3]]

private lemma left_right (t : Fin 3) (r : Fin 4) :
    side (tiles t) r 1 = side (tiles t) r 3 := by
  revert t r
  decide

private lemma top_bottom (t : Fin 3) (r : Fin 4) :
    side (tiles t) r 0 = side (tiles t) r 2 := by
  revert t r
  decide

private lemma integer_constant (f : ℤ → ℕ) (h : ∀ i, f (i+1) = f i) (i : ℤ) :
    f i = f 0 := by
  induction i using Int.induction_on with
  | zero => rfl
  | succ i ih => exact (h (i : ℤ)).trans ih
  | pred i ih =>
    have hs := h (-(i : ℤ) - 1)
    rw [show -(i : ℤ) - 1 + 1 = -(i : ℤ) by omega] at hs
    exact hs.symm.trans ih

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
private lemma finite_obstruction (r₀ r₁ r₂ : Fin 4) :
    ¬ ∀ i j : Fin 3, ∃ t : Fin 3, ∃ s : Fin 4,
      side (tiles t) s 0 = side (tiles i) (![r₀,r₁,r₂] i) 0 ∧
      side (tiles t) s 1 = side (tiles j) (![r₀,r₁,r₂] j) 1 := by
  revert r₀ r₁ r₂
  decide +kernel

private lemma no_tiling : ¬ Tiles tiles Finset.univ := by
  rintro ⟨g, _, hE, hN, hused⟩
  let H (i j : ℤ) := side (tiles (g (i,j)).1) (g (i,j)).2 1
  let V (i j : ℤ) := side (tiles (g (i,j)).1) (g (i,j)).2 0
  have hH (i j : ℤ) : H i j = H 0 j :=
    integer_constant (fun k => H k j) (fun k => by
      exact ((hE k j).trans (left_right _ _).symm).symm) i
  have hV (i j : ℤ) : V i j = V i 0 :=
    integer_constant (V i) (fun k => by
      exact ((hN i k).trans (top_bottom _ _).symm).symm) j
  choose cell hcell using fun t : Fin 3 => hused t (Finset.mem_univ t)
  let rot (t : Fin 3) := (g (cell t)).2
  have hr (t : Fin 3) : (![rot 0, rot 1, rot 2] : Fin 3 → Fin 4) t = rot t := by
    fin_cases t <;> rfl
  apply finite_obstruction (rot 0) (rot 1) (rot 2)
  intro a b
  let c : ℤ × ℤ := ((cell a).1,(cell b).2)
  refine ⟨(g c).1,(g c).2, ?_, ?_⟩
  · rw [hr]
    have h := (hV (cell a).1 (cell b).2).trans (hV (cell a).1 (cell a).2).symm
    change side (tiles (g c).1) (g c).2 0 =
      side (tiles (g (cell a)).1) (g (cell a)).2 0 at h
    simpa only [hcell] using h
  · rw [hr]
    have h := (hH (cell a).1 (cell b).2).trans (hH (cell b).1 (cell b).2).symm
    change side (tiles (g c).1) (g c).2 1 =
      side (tiles (g (cell b)).1) (g (cell b)).2 1 at h
    simpa only [hcell] using h

private lemma two_tiles (k a b : Fin 3) (ra rb : Fin 4)
    (hset : Finset.univ.erase k = {a,b})
    (hmatch : side (tiles a) ra 1 = side (tiles b) rb 1) :
    Tiles tiles (Finset.univ.erase k) := by
  let g (c : ℤ × ℤ) : Fin 3 × Fin 4 := if (2 : ℤ) ∣ c.1 then (a,ra) else (b,rb)
  have hside (i j : ℤ) :
      side (tiles (g (i,j)).1) (g (i,j)).2 1 = side (tiles a) ra 1 := by
    by_cases hi : (2 : ℤ) ∣ i
    · simp [g,hi]
    · simp [g,hi,hmatch.symm]
  refine ⟨g,?_,?_,?_,?_⟩
  · intro c
    rw [hset]
    by_cases h : (2 : ℤ) ∣ c.1 <;> simp [g,h]
  · intro i j
    rw [← left_right]
    exact (hside i j).trans (hside (i+1) j).symm
  · intro i j
    have he : g (i,j) = g (i,j+1) := rfl
    rw [← he]
    exact top_bottom _ _
  · intro t ht
    rw [hset] at ht
    rcases Finset.mem_insert.mp ht with rfl | hb
    · exact ⟨(0,0), by norm_num [g]⟩
    · have he := Finset.mem_singleton.mp hb
      subst t
      exact ⟨(1,0), by norm_num [g]⟩

private lemma all_deletions (k : Fin 3) : Tiles tiles (Finset.univ.erase k) := by
  fin_cases k
  · exact two_tiles 0 1 2 0 0 (by decide) (by decide)
  · exact two_tiles 1 0 2 0 1 (by decide) (by decide)
  · exact two_tiles 2 0 1 1 1 (by decide) (by decide)

theorem result :
    ∃ (n : ℕ) (T : Fin n → Fin 4 → ℕ), 3 ≤ n ∧ ¬ Tiles T Finset.univ ∧
      ∀ k : Fin n, Tiles T (Finset.univ.erase k) :=
  ⟨3, tiles, le_rfl, no_tiling, all_deletions⟩

end OMA.WangThree

theorem OMA.solution : type_of% @OMA.S_mo_466776.main := OMA.WangThree.result
