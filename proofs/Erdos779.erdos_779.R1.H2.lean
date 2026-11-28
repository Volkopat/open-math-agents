import OMAReductions.R_Erdos779_erdos_779_R1
-- Credit: @kofls (shorter proof)
open Finset Nat
set_option maxRecDepth 100000 in
theorem OMA.solution : OMA.R_Erdos779_erdos_779_R1.H2 := by
  have c (i q : ℕ) (h : q.Prime := by norm_num) (e : count Nat.Prime q = i := by decide) : nth Nat.Prime i = q :=
    e ▸ nth_count h
  intro n _ _
  interval_cases n <;> simp only [prod_range_succ, prod_range_zero, c 0 2, c 1 3, c 2 5, c 3 7, c 4 11, c 5 13,
    c 6 17, c 7 19, c 8 23, c 9 29, c 10 31]
  exacts [⟨5, by norm_num⟩, ⟨7, by norm_num⟩, ⟨13, by norm_num⟩, ⟨23, by norm_num⟩, ⟨17, by norm_num⟩,
    ⟨19, by norm_num⟩, ⟨23, by norm_num⟩, ⟨37, by norm_num⟩, ⟨61, by norm_num⟩, ⟨67, by norm_num⟩]
