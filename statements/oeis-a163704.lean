import Mathlib

/-!
# A163704: Number of n X 2 binary arrays with all 1s connected, a path of 1s from left column to lower right corner, and no 1 having more than two 1s adjacent

Source: https://oeis.org/A163704
Credit: @Dariusthedoggie
OEIS Foundation and contributors, CC BY-SA 4.0. Retrieved 2026-11-27.

Offset: 1,2
Data: 1, 5, 11, 21, 38, 66, 112, 187, 309, 507, 828, 1348, 2190, 3553, ...

Conventions:
- An n X 2 binary array is represented as a function `A : Fin n → Fin 2 → Fin 2`,
  with entries `0` and `1`.
- Two cells are adjacent if they are orthogonally adjacent (horizontally or vertically).
- Connectivity of 1s is the reflexive-transitive closure of orthogonal adjacency
  restricted to cells with value 1.
- A path of 1s from left column to lower right corner means there exists a cell `(r, 0)`
  in column `0` with value 1 connected in the 1s subgraph to the lower right corner
  `(n - 1, 1)` (which also has value 1).
- No 1 having more than two 1s adjacent means every cell with value 1 has at most 2
  orthogonally adjacent cells with value 1.
- For generating-function indexing, `a 0 = 0` and for `n ≥ 1`, `a n` is the number of
  valid n X 2 binary arrays.

Conjectures (OEIS formula section):
- Empirical: a(n) = 3*a(n-1) - 2*a(n-2) - a(n-3) + a(n-4) for n >= 6.
- Conjectures from Colin Barker, Mar 25 2018:
  G.f.: x*(1 + 2*x - 2*x^2 - x^3 + x^4) / ((1 - x)^2*(1 - x - x^2)).
  a(n) = -4 + (2^(-n)*((1-sqrt(5))^n*(-5+2*sqrt(5)) + (1+sqrt(5))^n*(5+2*sqrt(5)))) / sqrt(5) - n for n>1.
-/

namespace OMA.S_oeis_a163704

open PowerSeries

def isAdj {n : ℕ} (p q : Fin n × Fin 2) : Prop :=
  ((p.1 : ℕ) = q.1 ∧ ((p.2 : ℕ) + 1 = q.2 ∨ (q.2 : ℕ) + 1 = p.2)) ∨
  ((p.2 : ℕ) = q.2 ∧ ((p.1 : ℕ) + 1 = q.1 ∨ (q.1 : ℕ) + 1 = p.1))

instance {n : ℕ} (p q : Fin n × Fin 2) : Decidable (isAdj p q) := by
  unfold isAdj; infer_instance

def adjOne {n : ℕ} (A : Fin n → Fin 2 → Fin 2) (p q : Fin n × Fin 2) : Prop :=
  A p.1 p.2 = 1 ∧ A q.1 q.2 = 1 ∧ isAdj p q

def isValid (n : ℕ) (A : Fin n → Fin 2 → Fin 2) : Prop :=
  (∀ p q : Fin n × Fin 2, A p.1 p.2 = 1 → A q.1 q.2 = 1 →
    Relation.ReflTransGen (adjOne A) p q) ∧
  (∃ (hn : 0 < n) (r : Fin n),
    A r 0 = 1 ∧ A ⟨n - 1, Nat.sub_lt hn Nat.one_pos⟩ 1 = 1 ∧
    Relation.ReflTransGen (adjOne A) (r, 0) (⟨n - 1, Nat.sub_lt hn Nat.one_pos⟩, 1)) ∧
  (∀ p : Fin n × Fin 2, A p.1 p.2 = 1 →
    (Finset.univ.filter (fun q : Fin n × Fin 2 => A q.1 q.2 = 1 ∧ isAdj p q)).card ≤ 2)

noncomputable def a (n : ℕ) : ℕ :=
  if n = 0 then 0 else Nat.card { A : Fin n → Fin 2 → Fin 2 // isValid n A }

theorem main :
    (∀ n ≥ 6, (a n : ℤ) =
      3 * (a (n - 1) : ℤ) - 2 * (a (n - 2) : ℤ) - (a (n - 3) : ℤ) + (a (n - 4) : ℤ)) ∧
    (((1 - X) ^ 2 * (1 - X - X ^ 2) : PowerSeries ℤ) * PowerSeries.mk (fun n => (a n : ℤ)) =
      X * (1 + 2 * X - 2 * X ^ 2 - X ^ 3 + X ^ 4)) ∧
    (∀ n > 1, (a n : ℝ) =
      -4 + ((2 : ℝ) ^ (-(n : ℤ)) *
        ((1 - Real.sqrt 5) ^ n * (-5 + 2 * Real.sqrt 5) +
         (1 + Real.sqrt 5) ^ n * (5 + 2 * Real.sqrt 5))) / Real.sqrt 5 - (n : ℝ)) := by
  sorry

end OMA.S_oeis_a163704
