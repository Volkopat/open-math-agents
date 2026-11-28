import Mathlib

namespace OMA.S_oeis_a064173

/-- The largest part of a partition `p : Nat.Partition n` (`0` if `p` has no parts). -/
def maxPart {n : ℕ} (p : Nat.Partition n) : ℕ :=
  p.parts.fold max 0

/-- OEIS A064173: number of partitions of `n` with positive rank
(`largest part - number of parts > 0`, i.e., `p.parts.card < maxPart p`). -/
def posRankCount (n : ℕ) : ℕ :=
  ((Finset.univ : Finset (Nat.Partition n)).filter (fun p => p.parts.card < maxPart p)).card

/-- Partition generating function `P(q) = ∑_{n ≥ 0} p(n) q^n` over `PowerSeries ℚ`. -/
noncomputable def partitionGF : PowerSeries ℚ :=
  PowerSeries.mk fun n => (Fintype.card (Nat.Partition n) : ℚ)

/-- Pentagonal series `S(q) = ∑_{k ≥ 1} (-1)^k * (-q^(k*(3*k+1)/2)) = ∑_{k ≥ 1} (-1)^(k-1) q^(k*(3*k+1)/2)`. -/
noncomputable def pentPosSeries : PowerSeries ℚ :=
  PowerSeries.mk fun n =>
    ∑ k ∈ Finset.Icc 1 n,
      if k * (3 * k + 1) / 2 = n then (-1 : ℚ) ^ k * (-1) else 0

/-- OEIS A064173 conjecture:
`G.f.: Product_{k ≥ 1} (1/(1 - q^k)) * Sum_{k ≥ 1} ((-1)^k * (-q^(3*k^2/2 + k/2)))`.
Formally, the generating function `∑_{n ≥ 0} posRankCount n * q^n` equals
`partitionGF * pentPosSeries` (where `partitionGF` satisfies
`partitionGF * ∏_{k=1}^N (1 - q^k) ≡ 1 (mod q^(N+1))`). -/
theorem main :
    PowerSeries.mk (fun n => (posRankCount n : ℚ)) = partitionGF * pentPosSeries := by
  sorry

end OMA.S_oeis_a064173
