import Mathlib

/-!
# Rank of the Hadamard square of a signed circulant matrix

Source: xoxo, https://mathoverflow.net/questions/507197 (CC BY-SA 4.0).
Credit: @connoranderson.

The source asks when the support matrix A of a signed circulant B of rank r
has rank between Ω(r) and 2^{polylog(r)}. The upper bound r² holds for every
size. A sufficient condition for the lower bound is sparsity: if each row
of A has w ones and A is nonzero, then n ≤ w rank(A), so wr ≤ n gives
rank(A) ≥ r. Without a condition the rank can be one even when n=q² and r=q
for every q≥3. This family satisfies the specified lower growth rate on r
for every 0<δ<1 and has r/n tending to zero.
-/

namespace OMA.S_mo_507197

/-- Number of ones in each row of the entrywise square of a signed circulant. -/
noncomputable def weight {n : ℕ} [NeZero n] (v : ZMod n → ℝ) : ℕ :=
  (Finset.univ.filter fun i => v i ≠ 0).card

theorem main :
    (∀ (n : ℕ) [NeZero n] (v : ZMod n → ℝ),
      (∀ i, v i = -1 ∨ v i = 0 ∨ v i = 1) →
      let B := Matrix.circulant v
      let A := Matrix.circulant (fun i => v i ^ 2)
      A.rank ≤ B.rank ^ 2 ∧
        ((∃ i, v i ≠ 0) → n ≤ weight v * A.rank ∧
          (weight v * B.rank ≤ n → B.rank ≤ A.rank))) ∧
    (∀ (q : ℕ) [NeZero q], 3 ≤ q →
      ∃ v : ZMod (q*q) → ℝ, (∀ i, v i = -1 ∨ v i = 0 ∨ v i = 1) ∧
        (Matrix.circulant v).rank = q ∧
        (Matrix.circulant (fun i => v i ^ 2)).rank = 1) := by
  sorry

end OMA.S_mo_507197
