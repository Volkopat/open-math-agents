import Mathlib

namespace OMA.S_oeis_a331957

/-- Stirling numbers of the second kind `S(n, k)`. -/
def stirling2 : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 0
  | n + 1, k + 1 => (k + 1) * stirling2 n (k + 1) + stirling2 n k

/-- Number of rooted chains in set partitions of `{1, ..., n}` (`A331957`):
`a(0) = 1`, and for `n ≥ 1`, `a(n) = 1 + ∑_{k=1}^{n-1} S(n, k) * a(k)`. -/
def a331957 : ℕ → ℕ
  | 0 => 1
  | n + 1 => 1 + ∑ k : Fin n, stirling2 (n + 1) (k.1 + 1) * a331957 (k.1 + 1)
termination_by n => n
decreasing_by have := k.isLt; omega

/-- Mikhail Kurkov's triangle `R(n, k)`:
`R(0, 0) = 1`, `R(n, k) = (k + 1) * ∑_{j=k}^{n-1} R(n - 1, j)` for `0 ≤ k < n`,
`R(n, n) = ∑_{j=0}^{n-1} R(n, j)`. -/
def kurkovR : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k =>
    if k < n + 1 then
      (k + 1) * ∑ j ∈ Finset.Ico k (n + 1), kurkovR n j
    else if k = n + 1 then
      ∑ j : Fin (n + 1), kurkovR (n + 1) j.1
    else 0
termination_by n k => (n, if k < n then 0 else 1)
decreasing_by
  all_goals simp_wf
  · left; omega
  · right
    have hj : j.1 ≤ n := Nat.lt_succ_iff.mp j.isLt
    simp [hj, show ¬(k ≤ n) by omega]

theorem main :
    ∀ n : ℕ, a331957 n = kurkovR n 0 := by
  sorry

end OMA.S_oeis_a331957
