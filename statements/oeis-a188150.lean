import Mathlib

/-!
# OEIS A188150: 5-step self-avoiding walks on an n X n square, summed over starting positions

Source: https://oeis.org/A188150
Conjecture: Colin Barker, Apr 27 2018.
Credit: @biondadave

Conjectures: G.f. `4*x^3*(26 + 30*x - 3*x^2 - 3*x^3) / (1 - x)^3`, and
`a(n) = 3 a(n-1) - 3 a(n-2) + a(n-3)` for `n > 6`.

Formalization notes:
* As in R. H. Hardin's family of sequences (A188149 and following), an `m`-step walk visits `m`
  cells (it makes `m - 1` moves): this is the reading that matches the data (`a(1) = a(2) = 0`,
  then 104, 432, 972, ...). So `a n` counts the injective maps `w : Fin 5 → Fin n × Fin n` whose
  consecutive cells are orthogonally adjacent. Summing over all starting positions is the same
  as counting all such walks.
* The sequence has offset 1; `a 0 = 0` (the empty square), consistent with the generating
  function, which is stated as an identity of integer power series: the series of `a` times
  `(1 - x)^3` equals the numerator.
* Brute force agrees with both conjectures for `n ≤ 11`.
-/

namespace OMA.S_oeis_a188150

open PowerSeries

/-- Cells `p` and `q` of the square are orthogonally adjacent. -/
def Adjacent {n : ℕ} (p q : Fin n × Fin n) : Prop :=
  |(p.1 : ℤ) - q.1| + |(p.2 : ℤ) - q.2| = 1

instance {n : ℕ} (p q : Fin n × Fin n) : Decidable (Adjacent p q) := by
  unfold Adjacent; infer_instance

/-- A188150: the number of self-avoiding walks through 5 cells of the `n X n` square
(summed over all starting cells). -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter fun w : Fin 5 → Fin n × Fin n =>
    Function.Injective w ∧ ∀ i : Fin 4, Adjacent (w i.castSucc) (w i.succ)).card

theorem main :
    (PowerSeries.mk (fun n => (a n : ℤ)) * (1 - X) ^ 3 =
      4 * X ^ 3 * (26 + 30 * X - 3 * X ^ 2 - 3 * X ^ 3)) ∧
    ∀ n : ℕ, 6 < n → (a n : ℤ) = 3 * a (n - 1) - 3 * a (n - 2) + a (n - 3) := by
  sorry

end OMA.S_oeis_a188150
