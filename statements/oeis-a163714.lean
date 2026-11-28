import Mathlib

/-!
# A163714: Number of n X 2 binary arrays with all 1s connected, a path of 1s from top row to bottom row, and no 1 having more than two 1s adjacent

Source: https://oeis.org/A163714
Credit: @Dariusthedoggie
OEIS Foundation and contributors, CC BY-SA 4.0. Retrieved 2026-11-27.

Offset: 1,1
Data: 3, 7, 10, 16, 26, 42, 68, 110, 178, 288, 466, 754, 1220, 1974, ...

Conventions:
- An n X 2 binary array is represented as a function `A : Fin n → Fin 2 → Fin 2`,
  with entries `0` and `1`.
- Two cells are adjacent if they are orthogonally adjacent (horizontally or vertically,
  i.e., sharing a row with columns differing by 1, or sharing a column with rows
  differing by 1).
- Connectivity of 1s is the reflexive-transitive closure of orthogonal adjacency
  restricted to cells with value 1.
- A path of 1s from top row to bottom row means there exist cells in row `0` and
  row `n - 1`, both with value 1, connected in the 1s subgraph.
- No 1 having more than two 1s adjacent means every cell with value 1 has at most 2
  orthogonally adjacent cells with value 1.
- For generating-function indexing, `a 0 = 0` and for `n ≥ 1`, `a n` is the number of
  valid n X 2 binary arrays.

Conjectures (OEIS formula section):
- Empirical: a(n) = a(n-1) + a(n-2) for n>=5.
- Conjectures from Colin Barker, Feb 22 2018:
  G.f.: x*(1 + x)*(3 + x - x^2) / (1 - x - x^2).
  a(n) = (2^(-n)*((1-sqrt(5))^n*(-3+sqrt(5)) + (1+sqrt(5))^n*(3+sqrt(5)))) / sqrt(5) for n>2.
-/

namespace OMA.S_oeis_a163714

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
  (∃ (hn : 0 < n) (c₁ c₂ : Fin 2),
    A ⟨0, hn⟩ c₁ = 1 ∧ A ⟨n - 1, Nat.sub_lt hn Nat.one_pos⟩ c₂ = 1 ∧
    Relation.ReflTransGen (adjOne A) (⟨0, hn⟩, c₁) (⟨n - 1, Nat.sub_lt hn Nat.one_pos⟩, c₂)) ∧
  (∀ p : Fin n × Fin 2, A p.1 p.2 = 1 →
    (Finset.univ.filter (fun q : Fin n × Fin 2 => A q.1 q.2 = 1 ∧ isAdj p q)).card ≤ 2)

noncomputable def a (n : ℕ) : ℕ :=
  if n = 0 then 0 else Nat.card { A : Fin n → Fin 2 → Fin 2 // isValid n A }

theorem main :
    (∀ n ≥ 5, a n = a (n - 1) + a (n - 2)) ∧
    ((1 - X - X ^ 2 : PowerSeries ℤ) * PowerSeries.mk (fun n => (a n : ℤ)) =
      X * (1 + X) * (3 + X - X ^ 2)) ∧
    (∀ n > 2, (a n : ℝ) =
      ((2 : ℝ) ^ (-(n : ℤ)) *
        ((1 - Real.sqrt 5) ^ n * (-3 + Real.sqrt 5) +
         (1 + Real.sqrt 5) ^ n * (3 + Real.sqrt 5))) / Real.sqrt 5) := by
  sorry

end OMA.S_oeis_a163714
