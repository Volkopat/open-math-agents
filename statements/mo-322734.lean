import Mathlib

/-!
# MathOverflow 322734

Source: https://mathoverflow.net/questions/322734
-/

namespace OMA.S_mo_322734

def majorityColouring {n k : ℕ} (edges : Finset (Fin n × Fin n)) (c : Fin n → Fin k) : Prop :=
  ∀ v : Fin n,
    2 * (edges.filter (fun e => e.2=v ∧ c e.1=c v)).card ≤
      (edges.filter (fun e => e.2=v)).card

def permittedColourCounts {n : ℕ} (edges : Finset (Fin n × Fin n)) : Set ℕ :=
  {k | 0 < k ∧ ∃ c : Fin n → Fin k, majorityColouring edges c}

theorem main : ∃ n : ℕ, ∃ E : Finset (Fin n × Fin n),
      (∀ x : Fin n, (x,x) ∉ E) ∧
      ∃ a b : Fin n, a ≠ b ∧ (a,b) ∉ E ∧
        ∃ k l : ℕ, IsLeast (permittedColourCounts E) k ∧
          IsLeast (permittedColourCounts (insert (a,b) E)) l ∧ l<k := by
  sorry

end OMA.S_mo_322734
