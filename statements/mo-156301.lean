import Mathlib

open Filter
open scoped Topology

namespace OMA.S_mo_156301

/-- Each nontrivial p q-adic idempotent has normal digits in base p q. -/
theorem main :
    ∀ p q : ℕ, p.Prime → q.Prime → p ≠ q →
      let base := p * q
      ∃ residue : ℕ → ℕ,
        (∀ n, residue n < base ^ n ∧
          Nat.ModEq (p ^ n) (residue n) 1 ∧ Nat.ModEq (q ^ n) (residue n) 0) ∧
        let digit (i : ℕ) := (residue (i + 1) / base ^ i) % base
        ∀ (length : ℕ), 0 < length → ∀ word : Fin length → Fin base,
          Tendsto
            (fun N : ℕ =>
              (((Finset.range N).filter
                (fun i => ∀ j : Fin length, digit (i + j.val) = (word j).val)).card : ℝ) / N)
            atTop (𝓝 (1 / (base : ℝ) ^ length)) := by
  sorry

end OMA.S_mo_156301
