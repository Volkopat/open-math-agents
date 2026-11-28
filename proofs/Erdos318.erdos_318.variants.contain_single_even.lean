import FormalConjectures.ErdosProblems.«318»

open Finset

theorem OMA.solution : type_of% @Erdos318.erdos_318.variants.contain_single_even := by
  classical
  intro A hA h hP
  obtain ⟨e, he⟩ := Set.ncard_eq_one.mp h
  have he' : e ∈ {n | n ∈ A \ {0} ∧ Even n} := by rw [he]; rfl
  obtain ⟨heA, heE⟩ := he'
  obtain ⟨o, ho, ho'⟩ := hA.exists_notMem_finset ({0, e} : Finset ℕ)
  simp at ho'
  let f (n : ℕ) : ℝ := if n = e then -1 else 1
  obtain ⟨S, hS, hsub, hs⟩ := hP f
    (fun h => by have := congrFun h ⟨e, heA⟩; norm_num [f] at this)
    (fun h => by have := congrFun h ⟨o, ho, ho'.1⟩; norm_num [f, ho'.2] at this)
    (by rintro _ ⟨n, rfl⟩; by_cases hn : n = e <;> simp [f, hn])
  have nz (n) (hn : n ∈ S) : (n : ℝ) ≠ 0 := by exact_mod_cast (hsub hn).2
  by_cases hes : e ∈ S
  · let T := S.erase e
    let p := ∏ n ∈ T, n
    have odd : Odd p := prod_induction _ _ (fun _ _ => Odd.mul) odd_one fun n hn =>
      Nat.not_even_iff_odd.mp fun h => (mem_erase.mp hn).1 (by
        rw [← Set.mem_singleton_iff, ← he]
        exact ⟨hsub (mem_of_mem_erase hn), h⟩)
    have clear :
        (p : ℝ) * (∑ n ∈ T, f n / n) = ↑(∑ n ∈ T, ∏ j ∈ T.erase n, j) := by
      rw [mul_sum, Nat.cast_sum]
      refine sum_congr rfl fun n hn => ?_
      simp only [f, if_neg (mem_erase.mp hn).1, mul_one_div]
      rw [div_eq_iff (nz n (mem_of_mem_erase hn)), ← Nat.cast_mul, prod_erase_mul _ _ hn]
    rw [← add_sum_erase _ _ hes, show f e = -1 from if_pos rfl, neg_div] at hs
    have hsum : ∑ n ∈ T, f n / n = 1 / e := by dsimp [T]; linarith
    rw [hsum, mul_one_div, div_eq_iff (nz e hes)] at clear
    have pe : p = (∑ n ∈ T, ∏ j ∈ T.erase n, j) * e := by exact_mod_cast clear
    exact (Nat.not_even_iff_odd.mpr odd) (pe ▸ heE.mul_left _)
  · have hpos : 0 < ∑ n ∈ S, f n / n := sum_pos (fun n hn => by
      have hn' : n ≠ e := fun h => hes (h ▸ hn)
      simp [f, hn', Nat.pos_of_ne_zero (hsub hn).2]) hS
    exact hpos.ne' hs

