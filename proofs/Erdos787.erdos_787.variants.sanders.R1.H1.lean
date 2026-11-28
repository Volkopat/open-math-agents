import OMAReductions.R_Erdos787_erdos_787_variants_sanders_R1
import Mathlib.Algebra.Module.Submodule.Union

/-! Choi's transfer `g ℤ n ≤ g ℝ n` via an injective `ℚ`-linear functional. -/

open Finset Erdos787

theorem OMA.solution : OMA.R_Erdos787_erdos_787_variants_sanders_R1.H1 :=
  fun n => csSup_le' fun m hm => le_g fun A hA => by
    classical
    let D := ((A ×ˢ A).image fun p => p.1 - p.2).erase 0
    obtain ⟨f, hf⟩ := Module.exists_dual_forall_apply_ne_zero (K := ℚ)
      (Subtype.val : D → ℝ) fun v => (mem_erase.1 v.2).1
    let d := ∏ a ∈ A, (f a).den
    have hd : (d : ℚ) ≠ 0 := by exact_mod_cast (prod_pos fun a _ => (f a).pos).ne'
    let F (a : ℝ) : ℤ := (d / (f a).den : ℕ) * (f a).num
    have hF a (ha : a ∈ A) : (F a : ℚ) = d * f a := by
      have hdiv : ((d / (f a).den : ℕ) : ℚ) * (f a).den = d := by
        exact_mod_cast Nat.div_mul_cancel (dvd_prod_of_mem _ ha)
      simp only [F, Int.cast_mul, Int.cast_natCast, ← Rat.mul_den_eq_num]
      rw [mul_left_comm, hdiv, mul_comm]
    have hInj : Set.InjOn F A := fun a ha b hb hab => by
      by_contra hne
      have hq : (d : ℚ) * f a = d * f b := by
        simpa [hF a ha, hF b hb] using congrArg (Int.cast : ℤ → ℚ) hab
      exact hf ⟨a - b, mem_erase.2 ⟨sub_ne_zero.2 hne,
        mem_image.2 ⟨(a, b), mem_product.2 ⟨ha, hb⟩, rfl⟩⟩⟩
        (by rw [map_sub, mul_left_cancel₀ hd hq, sub_self])
    obtain ⟨C, hCA, hmC, hCdisj⟩ := hm (A.image F) ((card_image_of_injOn hInj).trans hA)
    let B := A.filter (F · ∈ C)
    have hCB : C ⊆ B.image F := fun c hc => by
      obtain ⟨a, ha, rfl⟩ := mem_image.1 (hCA hc)
      exact mem_image.2 ⟨a, mem_filter.2 ⟨ha, hc⟩, rfl⟩
    refine ⟨B, filter_subset _ _, hmC.trans ((card_le_card hCB).trans card_image_le),
      (disjoint_restrictedSumset_iff A B).2 fun a ha b hb hne hsum => ?_⟩
    obtain ⟨haA, haC⟩ := mem_filter.1 ha
    obtain ⟨hbA, hbC⟩ := mem_filter.1 hb
    have hadd : F a + F b = F (a + b) := Rat.intCast_injective <| by
      rw [Int.cast_add, hF a haA, hF b hbA, hF (a + b) hsum, map_add, mul_add]
    exact (disjoint_restrictedSumset_iff (A.image F) C).1 hCdisj (F a) haC (F b) hbC
      (fun h => hne (hInj haA hbA h)) (hadd ▸ mem_image_of_mem F hsum)
