import Mathlib.Data.Int.Basic

/-! Source: https://mathoverflow.net/questions/418146 -/

namespace OMA.S_mo_418146

/-- The source's b(q,x), with q the iteration number. -/
def b : ℕ → ℕ → ℕ
  | 0, x => x
  | q + 1, x =>
    let old := b q x
    ((old : ℤ) - ((q + 1 : ℕ) : ℤ) - ((old % (q + 1) : ℕ) : ℤ)).natAbs

/-- One-based rank after the given number of Josephus sieve rounds.
Rank zero means deletion. Round k removes every (k+1)-st position. -/
def sieveRank : ℕ → ℕ → ℕ
  | 0, x => x
  | k + 1, x =>
    let old := sieveRank k x
    if old % (k + 2) = 0 then 0 else old - old / (k + 2)

/-- The last signed difference gives the deletion round or the eventual survivor rank. -/
theorem main :
    ∀ n : ℕ, 0 < n → ∃ q : ℕ, 0 < q ∧ b q n = b q (n - 1) ∧
      (∀ j : ℕ, j < q → b j n ≠ b j (n - 1)) ∧
      let d : ℤ := (b (q - 1) n : ℤ) - b (q - 1) (n - 1)
      (0 < d → sieveRank (d.toNat - 1) n ≠ 0 ∧ sieveRank d.toNat n = 0) ∧
      (d < 0 → ∃ s : ℕ, ∀ r : ℕ, s ≤ r → sieveRank r n = d.natAbs) := by
  sorry

end OMA.S_mo_418146
