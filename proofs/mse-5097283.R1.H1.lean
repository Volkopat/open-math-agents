import OMAReductions.R_mse_5097283_R1

/-! A kernel-checked computation over 1 ≤ n ≤ 5000: the Boolean `chk` compares
`decide (4^n < (3^(n+1) mod 2^n) · 2^n + 3^n)` with `n ∈ {1, 2, 5, 10}` for every n < 5001.
The arithmetic is exact on natural numbers. -/

namespace OMA.Mse5097283

def chk : Bool :=
  (List.range 5001).all fun n =>
    n == 0 || (decide (4 ^ n < 3 ^ (n + 1) % 2 ^ n * 2 ^ n + 3 ^ n) ==
      (n == 1 || n == 2 || n == 5 || n == 10))

set_option maxRecDepth 100000 in
theorem chk_eq : chk = true := by decide +kernel

end OMA.Mse5097283

theorem OMA.solution : OMA.R_mse_5097283_R1.H1 := by
  intro n h1 h2
  have h := List.all_eq_true.1 OMA.Mse5097283.chk_eq n (List.mem_range.2 (by omega))
  have hn0 : (n == 0) = false := by
    cases n with
    | zero => omega
    | succ m => rfl
  rw [hn0, Bool.false_or, beq_iff_eq, Bool.eq_iff_iff] at h
  simpa [or_assoc] using h
