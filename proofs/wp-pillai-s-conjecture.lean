import OMAStatements.S_wp_pillai_s_conjecture

/-!
Disproof of the statement as formalized (statement loophole, not Pillai's conjecture itself).

The formal statement quantifies over all integers `A B C`, including `A = B = C = 0`, for which
every pair of positive integers solves `A * x ^ m - B * y ^ n = C`. (Pillai's conjecture needs
`A, B, C` nonzero / positive.) The solution set then contains `(k + 1, 1)` for every `k`,
so it is infinite.
-/

namespace OMA.Proof_wp_pillai_s_conjecture
open OMA.S_wp_pillai_s_conjecture

theorem not_main : ¬ (type_of% @OMA.S_wp_pillai_s_conjecture.main) := by
  intro h
  have hfin := h 0 0 0 3 3 (by norm_num) (by norm_num) (by norm_num)
  have hinj : Function.Injective (fun k : ℕ => (((k : ℤ) + 1, 1) : ℤ × ℤ)) := by
    intro a b hab
    simp only [Prod.mk.injEq, and_true] at hab
    omega
  have hinf : Set.Infinite (Set.range (fun k : ℕ => (((k : ℤ) + 1, 1) : ℤ × ℤ))) :=
    Set.infinite_range_of_injective hinj
  apply hinf
  apply hfin.subset
  rintro _ ⟨k, rfl⟩
  refine ⟨?_, ?_, ?_⟩
  · show (0 : ℤ) < (k : ℤ) + 1
    omega
  · show (0 : ℤ) < 1
    norm_num
  · simp

end OMA.Proof_wp_pillai_s_conjecture

theorem OMA.disproof : ¬ (type_of% @OMA.S_wp_pillai_s_conjecture.main) :=
  OMA.Proof_wp_pillai_s_conjecture.not_main
