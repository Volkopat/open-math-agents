import Mathlib

/-!
# OEIS A188149: 4-step self-avoiding walks on an n X n square, summed over starting positions

Source: https://oeis.org/A188149
Conjecture: Colin Barker, Apr 26 2018.
Credit: @biondadave

Conjectures: G.f. `8 x^2 (1 + 7 x + 2 x^2 - x^3) / (1 - x)^3`, and
`a(n) = 3 a(n-1) - 3 a(n-2) + a(n-3)` for `n > 5`.

Formalization notes:
* As in R. H. Hardin's family of sequences, an `m`-step walk visits `m` cells (it makes `m - 1`
  moves): this is the reading that matches the data (`a(2) = 8`, the 8 directed Hamiltonian
  paths of the 2 X 2 square; then 80, 232, 456, ...). So `a n` counts the injective maps
  `w : Fin 4 → Fin n × Fin n` whose consecutive cells are orthogonally adjacent. Summing over all
  starting positions is the same as counting all such walks.
* The sequence has offset 1; `a 0 = 0` (the empty square), consistent with the generating
  function, which is stated as an identity of integer power series
  `(∑ a(n) x^n) (1 - x)^3 = 8 x^2 (1 + 7 x + 2 x^2 - x^3)`.
* Brute force agrees with both conjectures for `n ≤ 9`.
-/

namespace OMA.S_oeis_a188149

open PowerSeries

/-- Cells `p` and `q` of the square are orthogonally adjacent. -/
def Adjacent {n : ℕ} (p q : Fin n × Fin n) : Prop :=
  |(p.1 : ℤ) - q.1| + |(p.2 : ℤ) - q.2| = 1

instance {n : ℕ} (p q : Fin n × Fin n) : Decidable (Adjacent p q) := by
  unfold Adjacent; infer_instance

/-- A188149: the number of self-avoiding walks through 4 cells of the `n X n` square
(summed over all starting cells). -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter fun w : Fin 4 → Fin n × Fin n =>
    Function.Injective w ∧ ∀ i : Fin 3, Adjacent (w i.castSucc) (w i.succ)).card

theorem main :
    (PowerSeries.mk (fun n => (a n : ℤ)) * (1 - X) ^ 3 =
      8 * X ^ 2 * (1 + 7 * X + 2 * X ^ 2 - X ^ 3)) ∧
    ∀ n : ℕ, 5 < n → (a n : ℤ) = 3 * a (n - 1) - 3 * a (n - 2) + a (n - 3) := by
  sorry

end OMA.S_oeis_a188149
