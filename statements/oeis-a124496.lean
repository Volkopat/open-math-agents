import Mathlib

/-!
# A124496: Triangle read by rows: T(n,k) is the number of set partitions of {1,2,...,n} in which the size of the last block is k, 1<=k<=n; the blocks are ordered with increasing least elements

Source: https://oeis.org/A124496
Credit: @timlantin

The formula section of the entry has the line

  Conjectures: T(n,n-3) = A000096(n). T(n,n-4)= A055831(n+1). - R. J. Mathar, Mar 13 2016

Definition of `T`. The entry describes the same triangle a second time, in a comment by the
author of the conjectures:

  Number of restricted growth functions of length n with a multiplicity k of the maximum value.
  RGF's are here defined as f(1)=1, f(i) <= 1+max_{1<=j<i} f(j). - R. J. Mathar, Mar 18 2016

(`f(i)` is the index of the block of `i` when the blocks are ordered with increasing least
elements, so the values are positive and the last block is the set of positions of the maximum
value.) `T` is defined here by this second description of the source.

Offsets. A000096 has offset 0 and `A000096(m) = m*(m+3)/2` (0, 2, 5, 9, 14, 20, 27, ...);
A055831 has offset 4 and `A055831(m) = (m-3)*(m^2+6*m-10)/6` for `m > 3` (5, 15, 31, 54, 85, ...),
as its formula section says. In the triangle `1 <= k <= n`, so `T(n,n-3)` exists for `n >= 4`
and `T(n,n-4)` for `n >= 5`.

* `T(n,n-4)` reads 31, 54, 85, 125, 175, ... for `n = 5, 6, 7, ...` (data of A124496), which is
  `A055831(6), A055831(7), ...`: the second conjecture holds on the data exactly as written,
  and it is stated as written, for all `n >= 5`.
* `T(n,n-3)` reads 9, 14, 20, 27, 35, ... for `n = 4, 5, 6, ...`, which is
  `A000096(3), A000096(4), ...`. So the first line is false as literally written
  (`T(4,1) = 9` and `A000096(4) = 14`): it identifies the two sequences up to a shift of the
  index, as such OEIS lines often do. The reading that agrees with the data, which is the one
  stated here, is `T(n,n-3) = A000096(n-1)` for all `n >= 4`.

Indexing. A function `f` on `{1, ..., n}` is `s : Fin n → ℕ` with `s i` standing for `f(i+1)`.
-/

namespace OMA.S_oeis_a124496

/-- Restricted growth functions of length `n`: every value is positive and at most one more
than the maximum of the earlier values. The maximum of no values is `0`, so the condition at
the first position says `f(1) = 1`. -/
def IsRGF {n : ℕ} (s : Fin n → ℕ) : Prop :=
  ∀ i : Fin n, 1 ≤ s i ∧ s i ≤ 1 + (Finset.Iio i).sup s

/-- `T(n,k)`: the number of restricted growth functions of length `n` whose maximum value is
taken exactly `k` times. -/
noncomputable def T (n k : ℕ) : ℕ :=
  Set.ncard {s : Fin n → ℕ | IsRGF s ∧
    (Finset.univ.filter fun i => s i = Finset.univ.sup s).card = k}

/-- A000096, offset 0: `m*(m+3)/2`. -/
def A000096 (m : ℕ) : ℕ := m * (m + 3) / 2

/-- A055831, offset 4: `(m-3)*(m^2+6*m-10)/6` (used for `m ≥ 4` only). -/
def A055831 (m : ℕ) : ℕ := (m - 3) * (m ^ 2 + 6 * m - 10) / 6

theorem main :
    (∀ n : ℕ, 4 ≤ n → T n (n - 3) = A000096 (n - 1)) ∧
    (∀ n : ℕ, 5 ≤ n → T n (n - 4) = A055831 (n + 1)) := by
  sorry

end OMA.S_oeis_a124496
