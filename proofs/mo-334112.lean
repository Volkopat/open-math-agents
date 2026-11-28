import OMAStatements.S_mo_334112
import Mathlib

-- Problem: mo-334112, is there c = c(k, alpha) > 0 with c E[X] <= E[min(X, k)] for every
-- finitely supported law on the naturals with P(X > k) < alpha and E[X] > 0?
-- Credit: @ivillar (the owner of the agent is credited as the solver)
--
-- No, already for k = 1 and alpha = 1. Let X be 0 or N with probability 1/2 each (N >= 2).
-- Then P(X > 1) = 1/2 < 1, E[X] = N/2 and E[min(X, 1)] = 1/2, so c N <= 1 for every N,
-- which is impossible for c > 0.

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_334112.main) := by
  intro h
  obtain ⟨c, hc, hmain⟩ := h 1 one_pos 1 one_pos le_rfl
  obtain ⟨M, hM⟩ := exists_nat_gt (1 / c)
  have hN : (0 : ℕ) ≠ M + 2 := by omega
  have hcN : 1 < c * ((M + 2 : ℕ) : ℝ) := by
    have h1 : 1 / c < ((M + 2 : ℕ) : ℝ) := by
      push_cast
      linarith
    have h2 := (div_lt_iff₀ hc).mp h1
    linarith
  have e1 : OMA.S_mo_334112.expect {0, M + 2} (fun _ => (1 / 2 : ℝ)) (fun x => (x : ℝ)) =
      ((M + 2 : ℕ) : ℝ) / 2 := by
    unfold OMA.S_mo_334112.expect
    rw [Finset.sum_pair hN]
    push_cast
    ring
  have e2 : OMA.S_mo_334112.expect {0, M + 2} (fun _ => (1 / 2 : ℝ))
      (fun x => if 1 < x then 1 else 0) = 1 / 2 := by
    unfold OMA.S_mo_334112.expect
    rw [Finset.sum_pair hN]
    have h1 : 1 < M + 2 := by omega
    simp [h1]
  have e3 : OMA.S_mo_334112.expect {0, M + 2} (fun _ => (1 / 2 : ℝ))
      (fun x => ((min x 1 : ℕ) : ℝ)) = 1 / 2 := by
    unfold OMA.S_mo_334112.expect
    rw [Finset.sum_pair hN]
    have h1 : min (M + 2) 1 = 1 := by omega
    simp [h1]
  have key := hmain {0, M + 2} (fun _ => 1 / 2) (fun x _ => by norm_num)
    (by rw [Finset.sum_pair hN]; norm_num) (by rw [e1]; positivity) (by rw [e2]; norm_num)
  rw [e1, e3] at key
  linarith
