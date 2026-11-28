import Mathlib

/-!
# A056862: Triangle T(n,k) is the number of restricted growth strings (RGS) of set partitions of {1..n} that have a decrease at index k (1<=k<n)

Source: https://oeis.org/A056862
Credit: @timlantin

The entry defines a restricted growth string of a set partition of `{1, ..., n}` as
`[s_1, ..., s_n]` with `s_1 = 1` and `s_i <= 1 + max(j<i, s_j)` (the `s_i` are block labels,
so they are positive), and `T(n,k)`, for `1 <= k < n`, as the number of them with a fall
`s_k > s_{k+1}`. Its formula section has the line

  Conjecture: T(n,3) = 2*A011965(n). - R. J. Mathar, Mar 08 2016

where A011965 (offset 0: 1, 2, 7, 27, 114, 523, ...) is the sequence of second differences of the
Bell numbers, `A011965(m) = A000110(m+2) - 2*A000110(m+1) + A000110(m)` (Magma program of
https://oeis.org/A011965; `A000110` is `Nat.bell`).

Offset. Column 3 of the triangle exists for `n >= 4` and reads 4, 14, 54, 228, 1046, 5178, ...
(rows `n = 4, 5, 6, ...` of the data of A056862), which is twice 2, 7, 27, 114, 523, 2589, ...,
the terms `A011965(1), A011965(2), ...`. So, with the offsets of the two entries, the line
`T(n,3) = 2*A011965(n)` is false as literally written (`T(4,3) = 4` and `2*A011965(4) = 228`):
it identifies the two sequences up to a shift of the index, as such OEIS lines often do. The
reading that agrees with the data, which is the one stated here, is

  T(n,3) = 2*A011965(n-3)   for all n >= 4.

Indexing. A string `[s_1, ..., s_n]` is a function `s : Fin n → ℕ` with `s i` standing for
`s_{i+1}`; `k` keeps its meaning from the source (the fall at index `k` is `s_k > s_{k+1}`).
-/

namespace OMA.S_oeis_a056862

/-- Restricted growth strings `[s_1, ..., s_n]`: every entry is positive and at most one more
than the maximum of the earlier entries. The maximum of no entries is `0`, so the condition at
the first entry says `s_1 = 1`. -/
def IsRGS {n : ℕ} (s : Fin n → ℕ) : Prop :=
  ∀ i : Fin n, 1 ≤ s i ∧ s i ≤ 1 + (Finset.Iio i).sup s

/-- `T(n,k)`: the number of restricted growth strings of length `n` with a fall at index `k`,
that is `s_k > s_{k+1}` (in the indexing from `0`: `s i > s j` with `i + 1 = k` and `j = k`). -/
noncomputable def T (n k : ℕ) : ℕ :=
  Set.ncard {s : Fin n → ℕ | IsRGS s ∧
    ∃ i j : Fin n, (i : ℕ) + 1 = k ∧ (j : ℕ) = k ∧ s j < s i}

/-- A011965, offset 0: the second differences of the Bell numbers. -/
def A011965 (m : ℕ) : ℤ :=
  (Nat.bell (m + 2) : ℤ) - 2 * (Nat.bell (m + 1) : ℤ) + (Nat.bell m : ℤ)

theorem main : ∀ n : ℕ, 4 ≤ n → (T n 3 : ℤ) = 2 * A011965 (n - 3) := by
  sorry

end OMA.S_oeis_a056862
