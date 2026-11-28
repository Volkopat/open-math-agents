import Mathlib

/-!
# Capacity of the binary deletion channel

Source: https://github.com/gokhanmergen/information-theory-problems/blob/main/problems/deletion-channel.md
Credit: @juansolana

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the body of `main` is left empty. A person reviews the translation before merging.

Formalization notes:
* The binary deletion channel takes `x : Fin n → Bool` as input and deletes each bit
  independently with probability `d`. The output is the concatenation of the surviving bits,
  with no indication of which positions were deleted, i.e. a sequence of length `m ≤ n`.
  For a fixed input `x` and output `y` of length `m`, `outProb d x m y` is the sum over all
  subsets `S ⊆ Fin n` with `S.card = m` whose surviving subsequence equals `y`:
  `d ^ (n - m) * (1 - d) ^ m` each.
* Input is drawn from a probability mass function `p` on `Fin n → Bool`.
* Mutual information is in bits: `I(X; Y) = Σ p(x) P(y|x) log₂ (P(y|x) / outLaw(y))`.
* The per-block-letter normalized mutual information is `(1/n) * max over p of I(X; Y)`.
* The capacity exists (Dobrushin): the sequence of per-letter normalized mutual information
  is the object whose limit is `C(d)`; the exact value of `C(d)` for `0 < d < 1` is open.
* The theorem below states that the normalized per-letter mutual information converges to a
  limit — the existence of the capacity. The actual value (no closed form, single-letter
  characterization, or matching bounds are known) is not asserted; it is the open part.
-/

namespace OMA.S_itp_deletion_channel

open Finset Filter Topology

/-- The surviving subsequence of `x : Fin n → Bool` at positions `S : Finset (Fin n)`,
taken in increasing order. -/
noncomputable def survivingSubseq {n : ℕ} (x : Fin n → Bool) {m : ℕ} (S : Finset (Fin n))
    (h : S.card = m) : Fin m → Bool :=
  fun i => x (S.orderEmbOfFin h i)

/-- Probability that input `x` (length `n`) yields output `y` (length `m`) under the binary
deletion channel with deletion probability `d`: the sum over subsets `S` of size `m` whose
surviving subsequence equals `y` of `d ^ (n - m) * (1 - d) ^ m`. -/
noncomputable def outProb {n : ℕ} (d : ℝ) (x : Fin n → Bool) (m : ℕ) (y : Fin m → Bool) : ℝ :=
  ∑ _S ∈ Finset.univ.filter (fun (_S : Finset (Fin n)) =>
    ∃ h : _S.card = m, ∀ i : Fin m, x (_S.orderEmbOfFin h i) = y i),
    d ^ (n - m) * (1 - d) ^ m

/-- Total probability of output `y` of length `m` under input distribution `p`. -/
noncomputable def outLaw {n : ℕ} (d : ℝ) (p : (Fin n → Bool) → ℝ) (m : ℕ) (y : Fin m → Bool) : ℝ :=
  ∑ x, p x * outProb d x m y

/-- A probability mass function on `Fin n → Bool`. -/
def IsPMF {n : ℕ} (p : (Fin n → Bool) → ℝ) : Prop :=
  (∀ x, 0 ≤ p x) ∧ (∑ x, p x = 1)

/-- Mutual information, in bits, of input `x` and output `y` under input distribution `p`. -/
noncomputable def mutualInfoBits {n : ℕ} (d : ℝ) (p : (Fin n → Bool) → ℝ) : ℝ :=
  ∑ x, ∑ m ∈ Finset.range (n + 1),
    ∑ y : Fin m → Bool,
      p x * outProb d x m y * Real.logb 2 (outProb d x m y / outLaw d p m y)

/-- Per-block-letter normalized mutual information at block length `n`: the supremum over all
input distributions of `(1/n) * I(X; Y)`. -/
noncomputable def mutualInfoValues (d : ℝ) (n : ℕ) : Set ℝ :=
  {r | ∃ p : (Fin n → Bool) → ℝ, IsPMF p ∧ mutualInfoBits d p = r}

noncomputable def capacitySeq (d : ℝ) (n : ℕ) : ℝ :=
  if n = 0 then 0
  else (1 / (n : ℝ)) * sSup (mutualInfoValues d n)

/-- The capacity of the binary deletion channel with deletion probability `d`: the limit of the
per-block-letter normalized mutual information. Dobrushin showed this limit exists.
The value of `C(d)` for any `d ∈ (0, 1)` is unknown: no closed form, single-letter
characterization, or matching bounds are known. -/
theorem main :
    ∀ d : ℝ, (0 < d ∧ d < 1) →
      ∃ C : ℝ, Tendsto (fun n : ℕ => capacitySeq d n) atTop (𝓝 C) := by
  sorry

end OMA.S_itp_deletion_channel
