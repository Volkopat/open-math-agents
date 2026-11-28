import Mathlib

/-!
# A257470: a(n+1) = least number not occurring earlier such that max{a(n), a(n+1)} >= 2 min{a(n), a(n+1)}; a(0) = 0.

Source: https://oeis.org/A257470
Credit: @avivorly

Definition (the entry's name): `a(n+1)` = least number not occurring earlier such that
`max{a(n), a(n+1)} >= 2 min{a(n), a(n+1)}`; `a(0) = 0`.

Conjecture (M. F. Hasler, in the entry), verbatim: I conjecture the following properties:
(i) For all k>0, a(3k+2) = a(3k-1)+2 except for k in S = {1, 8, 9, 13, 14, 22, 23, 31, 32, 40, 41, 49, 50,...}
where a(3k+2) = a(3k-1)+1.
(ii) Let D = (7, 1, 4, 1, 8, 1, 8, 1, 8, 1, 8, 1, 8, ...) be the first differences of the sequence S.
Then D(2k) = 1 for all k>0.
(iii) D(2k+1) = 4 or 8 for all k>0; except for the first one, the 4's always come twice in a row
(e.g., for k in {8, 9}, {13, 14}, {22, 23}, ...).
(iv) The length of runs of 8's in the subsequence D(2k+1) are: 6 (k=2..7), 3 (k=10..12), 7 (k=15..21),
7 (k=24..30), 7 (k=33..39), 7 (k=42..48), 7 (k=51..57), 7 (k=60..66), 3 (k=69..71), 3 (k=74..76), 7,...
It seems that except for the first two terms, this consists of runs of 7 of various length, but always
interrupted by two 3's.

Conventions:
- `a` follows the name literally, with offset 0: `a 0 = 0`, and `a (n + 1)` is the least `m : ℕ` with
  `m ≠ a i` for every `i ≤ n` (not occurring earlier) and `2 * min (a n) m ≤ max (a n) m`. It is written as
  `sInf` of that set; the set is never empty (only finitely many numbers occur earlier, and every `m ≥ 2 * a n`
  satisfies the inequality), so `sInf` is its least element. The definitions reproduce the data:
  `a 0, a 1, ... = 0, 1, 2, 4, 8, 3, 6, 12, 5, 10, 20, 7, ...` (all 87 terms of the entry's data checked
  against a computable twin).
- `a(3k-1)` is `a (3 * k - 1)`; the subtraction never truncates, since only `k > 0` occurs.
- `S` is the set of conjecture (i), the `k > 0` with `a(3k+2) = a(3k-1)+1`. Part (i) then says that every
  other `k > 0` gives `a(3k+2) = a(3k-1)+2`, that is: for every `k > 0` one of the two equations holds.
  With this `S`, the elements up to 50 are exactly the printed `1, 8, 9, 13, 14, 22, 23, 31, 32, 40, 41, 49, 50`
  (computable twin).
- `s j = Nat.nth (· ∈ S) j` is the `j`-th smallest element of `S`, counted from `j = 0`, so `s 0 = 1`, `s 1 = 8`,
  `s 2 = 9`. The first differences are indexed from 1 as in the entry: `D j = s j - s (j - 1)` for `j ≥ 1`,
  so `D 1, D 2, D 3, ... = 7, 1, 4, 1, 8, 1, 8, 1, 8, 1, 8, 1, 8` as printed (`D 0` is never used).
  `Nat.nth` enumerates an infinite set correctly; part (ii) also asserts that `S` is infinite.
- `E k = D (2 * k + 1)` is the subsequence `D(2k+1)`, `k ≥ 1`, of (iii) and (iv).
- `MaxBlock f v lo i j`: the indices `i ≤ j` (all `≥ lo`) form a maximal block of consecutive terms equal to
  `v` in the sequence `f lo, f (lo + 1), ...`. `InPairs f v lo`: in that sequence every term equal to `v` lies
  in a maximal block of terms equal to `v` (so no block is infinite), and every maximal block has length
  exactly 2.
- (iii), the 4's: the first 4 is `E 1 = 4`, and it is alone (`E 2 ≠ 4`); every later 4 comes twice in a row,
  formalized as `InPairs E 4 2` (maximal blocks of 4's in `E 2, E 3, ...`; as `E 2 ≠ 4`, these are exactly the
  maximal blocks of 4's in `E 1, E 2, ...` other than the first one).
- (iv), the runs: `RunStart k` says that `k ≥ 1` is the first index of a maximal run of 8's in
  `E 1, E 2, ...`, and `R j` (`j ≥ 1`) is the length of the `j`-th run: the number of consecutive 8's from its
  first index `Nat.nth RunStart (j - 1)` (an infinite run would give `R j = sInf ∅ = 0`, which the claims
  exclude). With these definitions `R 1, R 2, ... = 6, 3, 7, 7, 7, 7, 7, 7, 3, 3, 7` with the printed
  `k`-ranges `2..7, 10..12, 15..21, ...` (twin). The run lengths form an infinite sequence (there are
  infinitely many runs). The first two terms are `R 1 = 6` and `R 2 = 3`. After them (`j ≥ 3`) every `R j` is
  3 or 7, and the 3's among `R 3, R 4, ...` come in maximal blocks of exactly two (`InPairs R 3 3`): runs of
  7's interrupted by two 3's. The stronger reading of always interrupted is also stated: the 3's never stop
  (`∀ j, ∃ j' > j, R j' = 3`), so no run of 7's is infinite. The words of various length only describe the
  runs of 7's and are not formalized.
-/

namespace OMA.S_oeis_a257470

/-- The sequence of the entry: `a 0 = 0`, and `a (n + 1)` is the least `m` not occurring earlier
(`a i ≠ m` for all `i ≤ n`) with `max (a n) m ≥ 2 * min (a n) m`. -/
noncomputable def a : ℕ → ℕ
  | 0 => 0
  | n + 1 => sInf {m : ℕ | (∀ i ≤ n, a i ≠ m) ∧ 2 * min (a n) m ≤ max (a n) m}

/-- The set `S` of conjecture (i): the `k > 0` with `a (3k+2) = a (3k-1) + 1`. -/
def S : Set ℕ := {k | 0 < k ∧ a (3 * k + 2) = a (3 * k - 1) + 1}

/-- `s j` is the `j`-th smallest element of `S`, counting from `s 0` (`s 0 = 1`, `s 1 = 8`, `s 2 = 9`). -/
noncomputable def s (j : ℕ) : ℕ := Nat.nth (· ∈ S) j

/-- The first differences of `S`, indexed from 1 as in the entry: `D j = s j - s (j - 1)` for `j ≥ 1`
(`D 1 = 7`, `D 2 = 1`, `D 3 = 4`). -/
noncomputable def D (j : ℕ) : ℕ := s j - s (j - 1)

/-- The subsequence `D(2k+1)`, `k ≥ 1`, of conjectures (iii) and (iv). -/
noncomputable def E (k : ℕ) : ℕ := D (2 * k + 1)

/-- The indices `i ≤ j` form a maximal block of consecutive terms equal to `v` in the sequence
`f lo, f (lo + 1), ...`. -/
def MaxBlock (f : ℕ → ℕ) (v lo i j : ℕ) : Prop :=
  lo ≤ i ∧ i ≤ j ∧ (∀ k, i ≤ k → k ≤ j → f k = v) ∧ (i = lo ∨ f (i - 1) ≠ v) ∧ f (j + 1) ≠ v

/-- In the sequence `f lo, f (lo + 1), ...` the terms equal to `v` come in pairs: each of them lies in a
maximal block of terms equal to `v`, and every maximal block has length exactly 2. -/
def InPairs (f : ℕ → ℕ) (v lo : ℕ) : Prop :=
  (∀ k, lo ≤ k → f k = v → ∃ i j, i ≤ k ∧ k ≤ j ∧ MaxBlock f v lo i j) ∧
    ∀ i j, MaxBlock f v lo i j → j = i + 1

/-- `k ≥ 1` is the first index of a maximal run of 8's in the sequence `E 1, E 2, ...`. -/
def RunStart (k : ℕ) : Prop := 1 ≤ k ∧ E k = 8 ∧ (k = 1 ∨ E (k - 1) ≠ 8)

/-- `R j` (`j ≥ 1`) is the length of the `j`-th run of 8's in `E 1, E 2, ...`: the number of consecutive
8's from its first index. -/
noncomputable def R (j : ℕ) : ℕ := sInf {t : ℕ | E (Nat.nth RunStart (j - 1) + t) ≠ 8}

theorem main :
    -- (i)
    (∀ k, 0 < k → a (3 * k + 2) = a (3 * k - 1) + 2 ∨ a (3 * k + 2) = a (3 * k - 1) + 1) ∧
    -- (ii)
    (S.Infinite ∧ ∀ k, 0 < k → D (2 * k) = 1) ∧
    -- (iii)
    ((∀ k, 0 < k → E k = 4 ∨ E k = 8) ∧ E 1 = 4 ∧ E 2 ≠ 4 ∧ InPairs E 4 2) ∧
    -- (iv)
    ({k | RunStart k}.Infinite ∧ R 1 = 6 ∧ R 2 = 3 ∧ (∀ j, 3 ≤ j → R j = 3 ∨ R j = 7) ∧
      InPairs R 3 3 ∧ ∀ j, ∃ j', j < j' ∧ R j' = 3) := by
  sorry

end OMA.S_oeis_a257470
