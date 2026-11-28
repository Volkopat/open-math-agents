import Mathlib

/-!
# A225692

Number of Dyck paths of semilength `n` avoiding the pattern `U^(n-1) D^(n-1)`.

Source: https://oeis.org/A225692
Credit: @mbilenko03

Offset 2. The first terms are `0, 0, 4, 25, 106, 392, 1380, 4797`.

A Dyck path of semilength `n` is a map `w : Fin (2 * n) → Bool`, where `true` is an up step
and `false` is a down step, with `n` steps of each kind, such that every initial segment has
at least as many up steps as down steps.

The path contains `U^(n-1) D^(n-1)` when that word occurs as a subsequence: some strictly
increasing `ι : Fin (2 * (n - 1)) → Fin (2 * n)` reads `n - 1` ups and then `n - 1` downs.
Avoiding the pattern is the negation of that condition.

`main` is the conjunction of the two conjectures recorded by OEIS:

* R. J. Mathar, 9 July 2013. For every integer `n ≥ 5`,
  `-10*(n+1)*(n-4)*a(n) + (51*n^2 - 196*n + 80)*a(n-1) + (-45*n^2 + 134*n - 99)*a(n-2) + 2*(2*n-5)*(n-3)*a(n-3) = 0`.
  The lower bound `n ≥ 5` keeps every index `n`, `n-1`, `n-2`, and `n-3` at least 2, which is the offset.
* Vaclav Kotesovec, 30 November 2017. `a(n) ~ 4^n / (sqrt(π) * n^(3/2))` as `n → ∞`.
-/

namespace OMA.S_oeis_a225692

/-- A Dyck path of semilength `n`. `true` is an up step and `false` is a down step. -/
def IsDyck (n : ℕ) (w : Fin (2 * n) → Bool) : Prop :=
  (Finset.univ.filter (fun i : Fin (2 * n) => w i = true)).card = n ∧
    ∀ k : ℕ, k ≤ 2 * n →
      (Finset.univ.filter (fun i : Fin (2 * n) => i.val < k ∧ w i = false)).card ≤
        (Finset.univ.filter (fun i : Fin (2 * n) => i.val < k ∧ w i = true)).card

/-- The pattern `U^(n-1) D^(n-1)` occurs as a subsequence. -/
def ContainsPattern (n : ℕ) (w : Fin (2 * n) → Bool) : Prop :=
  ∃ ι : Fin (2 * (n - 1)) → Fin (2 * n), StrictMono ι ∧
    (∀ k : Fin (2 * (n - 1)), k.val < n - 1 → w (ι k) = true) ∧
    (∀ k : Fin (2 * (n - 1)), n - 1 ≤ k.val → w (ι k) = false)

/-- Number of Dyck paths of semilength `n` avoiding `U^(n-1) D^(n-1)`. -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.card { w : Fin (2 * n) → Bool // IsDyck n w ∧ ¬ ContainsPattern n w }

/-- Mathar's recurrence for every `n ≥ 5`, and Kotesovec's asymptotic. -/
theorem main :
    (∀ n : ℕ, 5 ≤ n →
      -10 * ((n : ℤ) + 1) * ((n : ℤ) - 4) * (a n : ℤ) +
        (51 * (n : ℤ) ^ 2 - 196 * (n : ℤ) + 80) * (a (n - 1) : ℤ) +
        (-45 * (n : ℤ) ^ 2 + 134 * (n : ℤ) - 99) * (a (n - 2) : ℤ) +
        2 * (2 * (n : ℤ) - 5) * ((n : ℤ) - 3) * (a (n - 3) : ℤ) = 0) ∧
    Filter.Tendsto
      (fun n : ℕ =>
        (a n : ℝ) / ((4 : ℝ) ^ n / (Real.sqrt Real.pi * (n : ℝ) ^ ((3 : ℝ) / 2))))
      Filter.atTop (nhds 1) := by
  sorry

end OMA.S_oeis_a225692
