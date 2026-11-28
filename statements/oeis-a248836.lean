import Mathlib

namespace OMA.S_oeis_a248836

/-- Number of length-n arrays `x : Fin n → ℕ` with `x i ≤ i + 1` (i.e. `x(i) ∈ 0..i` for `i = 1..n`)
and no value appearing more than 2 times. -/
noncomputable def a248836 (n : ℕ) : ℕ :=
  ({x : Fin n → ℕ | (∀ i : Fin n, x i ≤ i.1 + 1) ∧
    (∀ v : ℕ, (Finset.univ.filter (fun i : Fin n => x i = v)).card ≤ 2)}).ncard

/-- Formal power series `sin(x) = ∑_{m≥0} (-1)^m x^{2m+1} / (2m+1)!`. -/
def sinSeries : PowerSeries ℚ :=
  PowerSeries.mk fun n =>
    if n % 2 = 1 then ((-1 : ℚ) ^ (n / 2)) / (Nat.factorial n : ℚ) else 0

/-- Exponential generating function `∑_{n≥0} a(n) x^n / n!`. -/
noncomputable def a248836Egf : PowerSeries ℚ :=
  PowerSeries.mk fun n => (a248836 n : ℚ) / (Nat.factorial n : ℚ)

/-- Mikhail Kurkov's Seidel-type triangle `R(n, k)`. -/
def kurkovR : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k =>
    if k < n + 1 then
      ∑ j ∈ Finset.range (n + 1 - k), kurkovR n j
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
    (1 - sinSeries) ^ 2 * a248836Egf = 1 ∧
      ∀ n : ℕ, a248836 n = kurkovR (n + 1) 0 := by
  sorry

end OMA.S_oeis_a248836
