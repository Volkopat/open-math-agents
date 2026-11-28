import Mathlib

namespace OMA.S_oeis_a379726

/-- Two squares on an `n × n` chessboard are king-adjacent (including equality) if their
Chebyshev distance is at most 1. -/
def kingAdj {n : ℕ} (u v : Fin n × Fin n) : Prop :=
  (u.1.1 ≤ v.1.1 + 1 ∧ v.1.1 ≤ u.1.1 + 1) ∧ (u.2.1 ≤ v.2.1 + 1 ∧ v.2.1 ≤ u.2.1 + 1)

instance {n : ℕ} (u v : Fin n × Fin n) : Decidable (kingAdj u v) := by
  unfold kingAdj; infer_instance

/-- A set `S` of kings on an `n × n` chessboard is a 2-dominating set if every square is
attacked or occupied by at least 2 kings in `S`. -/
def isTwoDominating {n : ℕ} (S : Finset (Fin n × Fin n)) : Prop :=
  ∀ v : Fin n × Fin n, 2 ≤ (S.filter (fun u => kingAdj u v)).card

/-- Minimum number of kings on an `n × n` chessboard such that every square is attacked or
occupied by at least two kings (`A379726`). -/
noncomputable def a379726 (n : ℕ) : ℕ :=
  sInf {k : ℕ | ∃ S : Finset (Fin n × Fin n), isTwoDominating S ∧ S.card = k}

theorem main :
    ∀ n : ℕ, 2 ≤ n →
      a379726 n =
        if n % 3 = 0 then 2 * (n / 3) ^ 2 + n / 3
        else 2 * (n / 3 + 1) ^ 2 := by
  sorry

end OMA.S_oeis_a379726
