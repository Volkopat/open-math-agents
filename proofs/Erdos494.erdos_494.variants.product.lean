import FormalConjectures.ErdosProblems.«494»

/-! Multiplying every element by a nontrivial cube root of unity preserves triple products. -/

open Erdos494 Finset

theorem OMA.solution : type_of% @Erdos494.erdos_494.variants.product := by
  classical
  let ω : ℂ := Complex.exp (2 * Real.pi * Complex.I / 3)
  have hω : IsPrimitiveRoot ω 3 := Complex.isPrimitiveRoot_exp 3 (by decide)
  have hpow : ω ^ 3 = 1 := hω.pow_eq_one
  have hω0 : ω ≠ 0 := Complex.exp_ne_zero _
  let e : ℂ ↪ ℂ := ⟨fun z => ω * z, fun _ _ h => mul_left_cancel₀ hω0 h⟩
  let A : Finset ℂ := {1, 2, 3, 4}
  refine ⟨A, A.map e, by norm_num [A, card_insert_of_notMem], by simp,
    by norm_num [A], ?_, ?_, ?_⟩
  · intro h
    obtain ⟨a, ha, he⟩ := mem_map.mp h
    change ω * a = 0 at he
    have hz := (mul_eq_zero.mp he).resolve_left hω0
    norm_num [A, hz] at ha
  · unfold prodMultiset
    rw [powersetCard_map, map_val, Multiset.map_map]
    refine Multiset.map_congr rfl fun s hs => ?_
    have hcard := (mem_powersetCard.mp (show s ∈ A.powersetCard 3 from hs)).2
    change s.prod id = (s.map e).prod id
    rw [prod_map]
    change (∏ x ∈ s, x) = ∏ x ∈ s, ω * x
    rw [prod_mul_distrib, prod_const, hcard, hpow, one_mul]
  · intro heq
    have hA : ω ∈ A := heq.symm ▸
      (mem_map.mpr ⟨1, by simp [A], by change ω * 1 = ω; simp⟩)
    simp only [A, mem_insert, mem_singleton] at hA
    rcases hA with h | h | h | h
    · exact hω.ne_one (by decide) h
    all_goals norm_num [h] at hpow
