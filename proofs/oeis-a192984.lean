import OMAStatements.S_oeis_a192984

-- Problem: A192984: In repeated iterations of function m->m/3 if m == 0 (mod 3), m->4m+a if 4m+a == 0 (mod 3) where a = 1 or 2, a(n) is maximum value achieved if starting from n.
-- Upstream: formal-conjectures statements/oeis-a192984.lean:0 (declaration OMA.S_oeis_a192984.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea (the entry's argument): the maximum M = step^[k](n) satisfies step(M) <= M and
-- step(step(M)) <= M. If 3 does not divide m then step(m) >= 4m + 1 > m, so 3 divides M and
-- step(M) = M/3. If 3 did not divide M/3, then step(M/3) >= 4(M/3) + 1 > M. So 9 divides M.

open OMA.S_oeis_a192984 in
theorem OMA.solution : type_of% @OMA.S_oeis_a192984.main := by
  intro n _ M hM
  obtain ⟨⟨k, hk⟩, hub⟩ := hM
  have hle : ∀ j : ℕ, step^[j] n ≤ M := fun j => hub ⟨j, rfl⟩
  have e1 : step^[k + 1] n = step (step^[k] n) := Function.iterate_succ_apply' (f := step) k n
  have e2 : step^[k + 1 + 1] n = step (step^[k + 1] n) :=
    Function.iterate_succ_apply' (f := step) (k + 1) n
  have h1 : step M ≤ M := by
    have h := hle (k + 1)
    rw [e1, hk] at h
    exact h
  have h2 : step (step M) ≤ M := by
    have h := hle (k + 1 + 1)
    rw [e2, e1, hk] at h
    exact h
  have hgt : ∀ m : ℕ, m % 3 ≠ 0 → 4 * m + 1 ≤ step m := by
    intro m hm
    unfold step
    split_ifs <;> omega
  have hdiv : ∀ m : ℕ, m % 3 = 0 → step m = m / 3 := by
    intro m hm
    unfold step
    rw [if_pos hm]
  by_cases h3 : M % 3 = 0
  · rw [hdiv M h3] at h2
    by_cases h9 : M / 3 % 3 = 0
    · omega
    · have h4 := hgt (M / 3) h9
      omega
  · have h4 := hgt M h3
    omega
