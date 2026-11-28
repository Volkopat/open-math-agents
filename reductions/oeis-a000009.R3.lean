import OMAStatements.S_oeis_a000009

/-!
# Reduction oeis-a000009.R3 of A000009 (two conjectures of Zhi-Wei Sun)

Credit: @Bondyboy2001, building on @Jwolf52's R2

Refines R2: the representation conjecture is still proved unconditionally for every
`n ≤ 997436`. Beyond that bound, `H1` is now the exact missing object: an infinite
strictly increasing sequence of strict-partition values, pairwise non-dividing and
non-dividing in both directions against the 44-term seed, starting no higher than the
seed interval width `997200`, and with each successive term at most twice its predecessor.
`H2`, `H3`, `H4` are the three non-divisibility conjectures, unchanged.

Foundations proved here (no `native_decide`; kernel evaluation only):
* `strictPartitionCount_eq_subsetCount`: `q(n)` is the number of subsets of `{1, …, n}` with
  sum `n`; `subsetCount_succ` is the recursion `Q(K+1, n) = Q(K, n) + Q(K, n - (K+1))`.
* `tbl_getD`, `strictPartitionCount_eq_rec`: a list DP (written as a `Nat.rec` term) for the
  coefficients of `∏ (1 + x^k)`; one kernel evaluation gives every `q(n)` with `n ≤ N`
  (`N = 250` takes seconds), and `mem_qList` turns list membership into `∃ m, x = q m`.
* `testBit_foldr`: subset sums of a list as one natural number (bit `s` is set iff some
  subset sums to `s`); `testBit_of_mask` checks a whole interval of bits with one identity.
* `H1_le`: the representation conjecture for `0 < n ≤ 997436`, from the 44-term seed antichain of
  note #43523 (its subset sums cover `[237, 997436]`) and 236 explicit small-case witnesses.
* `rep_of_finset`, `extend_cover` (as in R1), and the new inductions `chain_width`,
  `chain_cover` and `tail_from_coverage`: a compatible doubling sequence as in `H1`
  extends the seed interval until it covers every larger integer.
-/

namespace OMA.R_oeis_a000009_R3

open OMA.S_oeis_a000009

/-- The exact missing object in the representation conjecture: an infinite doubling
extension of the kernel-checked seed antichain, staying a divisibility antichain. -/
def H1 : Prop :=
  ∃ a : ℕ → ℕ,
    (∀ i, ∃ m : ℕ, 0 < m ∧ a i = strictPartitionCount m) ∧
    StrictMono a ∧
    a 0 ≤ 997200 ∧
    (∀ i, a (i + 1) ≤ 2 * a i) ∧
    (∀ i j, i ≠ j → ¬ a i ∣ a j) ∧
    (∀ x ∈ [18, 22, 27, 32, 38, 46, 89, 104, 122, 142, 165, 222, 296, 340, 390, 585, 668,
    982, 1113, 1816, 2590, 2910, 3658, 4097, 4582, 5718, 6378, 7108, 7917, 8808, 12076, 13394,
    16444, 20132, 27130, 29927, 48446, 58499, 64234, 84756, 101698, 111322, 159046, 189586], ∀ i, (¬ x ∣ a i) ∧ (¬ a i ∣ x))

/-- `q(n)` does not divide `p(n)` for `n > 7`. -/
def H2 : Prop :=
  ∀ n : ℕ, 7 < n → ¬ strictPartitionCount n ∣ partitionCount n

/-- `q(n)` does not divide `p(n) - 1` for `n > 7`. -/
def H3 : Prop :=
  ∀ n : ℕ, 7 < n → ¬ strictPartitionCount n ∣ partitionCount n - 1

/-- `q(n)` does not divide `p(n) + 1` for `n > 7`. -/
def H4 : Prop :=
  ∀ n : ℕ, 7 < n → ¬ strictPartitionCount n ∣ partitionCount n + 1

/-! ## `q(n)` as a subset count -/

/-- Distinct-part partitions of `n` are the subsets of `{1, …, n}` summing to `n`. -/
theorem strictPartitionCount_eq_subsetCount (n : ℕ) :
    strictPartitionCount n =
      ((Finset.Icc 1 n).powerset.filter (fun s => ∑ x ∈ s, x = n)).card := by
  unfold strictPartitionCount
  refine Finset.card_bij' (fun p _ => p.parts.toFinset)
    (fun s hs => ⟨s.val, fun {i} hi => by
        have := (Finset.mem_powerset.1 (Finset.mem_filter.1 hs).1) hi
        exact (Finset.mem_Icc.1 this).1,
      by simpa [Finset.sum_val] using (Finset.mem_filter.1 hs).2⟩) ?_ ?_ ?_ ?_
  · intro p hp
    have hnd : p.parts.Nodup := (Finset.mem_filter.1 hp).2
    simp only [Finset.mem_filter, Finset.mem_powerset]
    refine ⟨fun i hi => ?_, ?_⟩
    · rw [Multiset.mem_toFinset] at hi
      exact Finset.mem_Icc.2 ⟨p.parts_pos hi, by
        have := Multiset.le_sum_of_mem hi; rw [p.parts_sum] at this; exact this⟩
    · rw [Finset.sum_eq_multiset_sum, Multiset.toFinset_val, Multiset.dedup_eq_self.2 hnd]
      simpa using p.parts_sum
  · intro s hs
    simp only [Nat.Partition.distincts, Finset.mem_filter, Finset.mem_univ, true_and]
    exact s.nodup
  · intro p hp
    have hnd : p.parts.Nodup := (Finset.mem_filter.1 hp).2
    ext1
    simp [Multiset.dedup_eq_self.2 hnd]
  · intro s hs
    ext1
    simp

theorem subsetCount_zero (n : ℕ) :
    ((Finset.Icc 1 0).powerset.filter (fun s => ∑ x ∈ s, x = n)).card =
      if n = 0 then 1 else 0 := by
  by_cases h : n = 0 <;> simp [h, Finset.filter_singleton, eq_comm]

theorem subsetCount_succ (K n : ℕ) :
    ((Finset.Icc 1 (K + 1)).powerset.filter (fun s => ∑ x ∈ s, x = n)).card =
      ((Finset.Icc 1 K).powerset.filter (fun s => ∑ x ∈ s, x = n)).card +
        if K + 1 ≤ n then
          ((Finset.Icc 1 K).powerset.filter (fun s => ∑ x ∈ s, x = n - (K + 1))).card
        else 0 := by
  simp only [Finset.card_filter]
  have hIcc : Finset.Icc 1 (K + 1) = insert (K + 1) (Finset.Icc 1 K) := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
  have hnot : K + 1 ∉ Finset.Icc 1 K := by simp
  rw [hIcc, Finset.sum_powerset_insert hnot]
  congr 1
  have key : ∀ t ∈ (Finset.Icc 1 K).powerset,
      (if ∑ x ∈ insert (K + 1) t, x = n then 1 else 0) =
        if K + 1 ≤ n then (if ∑ x ∈ t, x = n - (K + 1) then 1 else 0) else 0 := by
    intro t ht
    have hKt : K + 1 ∉ t := fun h => hnot (Finset.mem_powerset.1 ht h)
    rw [Finset.sum_insert hKt]
    split_ifs <;> omega
  rw [Finset.sum_congr rfl key]
  split_ifs <;> simp

/-- For `n ≤ K` the bound `K` on the parts is irrelevant. -/
theorem subsetCount_of_le (n : ℕ) : ∀ K, n ≤ K →
    ((Finset.Icc 1 K).powerset.filter (fun s => ∑ x ∈ s, x = n)).card =
      ((Finset.Icc 1 n).powerset.filter (fun s => ∑ x ∈ s, x = n)).card := by
  intro K hK
  induction K, hK using Nat.le_induction with
  | base => rfl
  | succ K hK ih =>
    rw [subsetCount_succ, if_neg (by omega), add_zero, ih]

/-! ## The coefficient table of `∏ (1 + x^k)` -/

section Table

variable (N : ℕ) (t : ℕ → List ℕ) (h0 : t 0 = 1 :: List.replicate N 0)
  (hs : ∀ K, t (K + 1) = List.zipWith (· + ·) (t K) (List.replicate (K + 1) 0 ++ t K))
include h0 hs

theorem tbl_length (K : ℕ) : (t K).length = N + 1 := by
  induction K with
  | zero => simp [h0]
  | succ K ih => simp [hs, ih]

theorem tbl_getD (K : ℕ) : ∀ i ≤ N, (t K).getD i 0 =
    ((Finset.Icc 1 K).powerset.filter (fun s => ∑ x ∈ s, x = i)).card := by
  induction K with
  | zero =>
    intro i hi
    rw [subsetCount_zero]
    rcases i with _ | i
    · simp [h0]
    · simp [h0, List.getD_eq_getElem?_getD, List.getElem?_replicate]; split <;> rfl
  | succ K ih =>
    intro i hi
    have hlen := tbl_length N t h0 hs K
    rw [subsetCount_succ, ← ih i hi]
    simp only [hs, List.getD_eq_getElem?_getD, List.getElem?_zipWith]
    have h1 : i < (t K).length := by omega
    rw [List.getElem?_eq_getElem h1]
    by_cases hk : K + 1 ≤ i
    · rw [if_pos hk, ← ih (i - (K + 1)) (by omega), List.getElem?_append_right (by simp; omega)]
      simp only [List.length_replicate, List.getD_eq_getElem?_getD]
      rw [List.getElem?_eq_getElem (by omega)]
      simp
    · rw [if_neg hk, List.getElem?_append_left (by simp; omega), List.getElem?_replicate]
      simp [show i < K + 1 by omega]

end Table

/-- One table gives every value `q(n)` with `n ≤ N`. -/
theorem strictPartitionCount_eq_rec (N n : ℕ) (hn : n ≤ N) :
    strictPartitionCount n = (Nat.rec (motive := fun _ => List ℕ) (1 :: List.replicate N 0)
      (fun k l => List.zipWith (· + ·) l (List.replicate (k + 1) 0 ++ l)) N).getD n 0 := by
  rw [strictPartitionCount_eq_subsetCount,
    tbl_getD N (fun K => Nat.rec (motive := fun _ => List ℕ) (1 :: List.replicate N 0)
      (fun k l => List.zipWith (· + ·) l (List.replicate (k + 1) 0 ++ l)) K) rfl (fun _ => rfl)
      N n hn,
    subsetCount_of_le n N hn]

/-- Entries `1, …, N` of the table are values of `q`. -/
theorem mem_qList {N x : ℕ} (hx : x ∈ (Nat.rec (motive := fun _ => List ℕ)
    (1 :: List.replicate N 0)
    (fun k l => List.zipWith (· + ·) l (List.replicate (k + 1) 0 ++ l)) N).drop 1) :
    ∃ m, 0 < m ∧ x = strictPartitionCount m := by
  rw [List.mem_iff_getElem] at hx
  obtain ⟨i, hi, rfl⟩ := hx
  have hlen := tbl_length N (fun K => Nat.rec (motive := fun _ => List ℕ)
    (1 :: List.replicate N 0)
    (fun k l => List.zipWith (· + ·) l (List.replicate (k + 1) 0 ++ l)) K) rfl (fun _ => rfl) N
  simp only [List.length_drop] at hi
  refine ⟨i + 1, by omega, ?_⟩
  rw [strictPartitionCount_eq_rec N (i + 1) (by omega), List.getElem_drop,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
  simp [Nat.add_comm]

/-! ## Subset sums as a bitset -/

/-- Bit `s` of `l.foldr (fun a b => b ||| b <<< a) 1` is set iff some subset of `l` sums to `s`. -/
theorem testBit_foldr (l : List ℕ) (hl : l.Nodup) (s : ℕ) :
    (l.foldr (fun a b => b ||| b <<< a) 1).testBit s = true ↔
      ∃ T ⊆ l.toFinset, ∑ x ∈ T, x = s := by
  induction l generalizing s with
  | nil =>
    simp only [List.foldr_nil, List.toFinset_nil, Finset.subset_empty, exists_eq_left,
      Finset.sum_empty]
    rcases s with _ | s <;> simp [Nat.testBit_succ]
  | cons a l ih =>
    have ha : a ∉ l := (List.nodup_cons.1 hl).1
    have hl' : l.Nodup := (List.nodup_cons.1 hl).2
    simp only [List.foldr_cons, Nat.testBit_lor, Nat.testBit_shiftLeft, Bool.or_eq_true,
      Bool.and_eq_true, decide_eq_true_eq, ih hl', List.toFinset_cons]
    constructor
    · rintro (⟨T, hT, hs⟩ | ⟨hsa, T, hT, hs⟩)
      · exact ⟨T, hT.trans (Finset.subset_insert _ _), hs⟩
      · have haT : a ∉ T := fun h => ha (List.mem_toFinset.1 (hT h))
        refine ⟨insert a T, Finset.insert_subset_insert _ hT, ?_⟩
        rw [Finset.sum_insert haT, hs]; omega
    · rintro ⟨T, hT, hs⟩
      by_cases haT : a ∈ T
      · right
        have hle : a ≤ ∑ x ∈ T, x :=
          Finset.single_le_sum (f := fun x => x) (fun _ _ => Nat.zero_le _) haT
        refine ⟨by omega, T.erase a, ?_, ?_⟩
        · intro x hx
          have hx' := Finset.mem_erase.1 hx
          rcases Finset.mem_insert.1 (hT hx'.2) with h | h
          · exact absurd h hx'.1
          · exact h
        · have := Finset.sum_erase_add T (fun x => x) haT
          omega
      · left
        refine ⟨T, fun x hx => ?_, hs⟩
        rcases Finset.mem_insert.1 (hT hx) with h | h
        · exact absurd (h ▸ hx) haT
        · exact h

/-- One big-number identity certifies that bits `L, …, L + k - 1` are all set. -/
theorem testBit_of_mask (B L k : ℕ) (h : (B >>> L) % 2 ^ k = 2 ^ k - 1) :
    ∀ s, L ≤ s → s < L + k → B.testBit s = true := by
  intro s h1 h2
  have := congrArg (fun x => x.testBit (s - L)) h
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one] at this
  rw [show L + (s - L) = s by omega] at this
  simpa [show s - L < k by omega] using this

/-! ## The seed antichain of note #43523, checked by the kernel -/

theorem seed_exists : ∃ seed : List ℕ, seed = [18, 22, 27, 32, 38, 46, 89, 104, 122, 142,
    165, 222, 296, 340, 390, 585, 668, 982, 1113, 1816, 2590, 2910, 3658, 4097, 4582, 5718,
    6378, 7108, 7917, 8808, 12076, 13394, 16444, 20132, 27130, 29927, 48446, 58499, 64234,
    84756, 101698, 111322, 159046, 189586] ∧ seed.Nodup ∧
    (∀ x ∈ seed, x ∈ (Nat.rec (motive := fun _ => List ℕ) (1 :: List.replicate 90 0)
      (fun k l => List.zipWith (· + ·) l (List.replicate (k + 1) 0 ++ l)) 90).drop 1) ∧
    (∀ x ∈ seed, ∀ y ∈ seed, x ≠ y → y % x ≠ 0) ∧
    ((seed.foldr (fun a b => b ||| b <<< a) 1) >>> 237) % 2 ^ 997200 = 2 ^ 997200 - 1 :=
  ⟨[18, 22, 27, 32, 38, 46, 89, 104, 122, 142, 165, 222, 296, 340, 390, 585, 668,
    982, 1113, 1816, 2590, 2910, 3658, 4097, 4582, 5718, 6378, 7108, 7917, 8808, 12076, 13394,
    16444, 20132, 27130, 29927, 48446, 58499, 64234, 84756, 101698, 111322, 159046, 189586],
    rfl, by decide +kernel⟩

/-! ## Small cases, checked by the kernel -/

theorem small_exists : ∃ W : List (List ℕ), ∀ i < 236, ((W.getD i []).sum = i + 1 ∧
    (W.getD i []).Nodup ∧
    (∀ x ∈ W.getD i [], x ∈ (Nat.rec (motive := fun _ => List ℕ) (1 :: List.replicate 28 0)
      (fun k l => List.zipWith (· + ·) l (List.replicate (k + 1) 0 ++ l)) 28).drop 1) ∧
    ∀ x ∈ W.getD i [], ∀ y ∈ W.getD i [], x ≠ y → y % x ≠ 0) :=
  ⟨[[1], [2], [3], [4], [5], [6], [5, 2], [8], [5, 4], [10], [8, 3], [12], [10, 3], [10, 4], [15],
    [10, 6], [15, 2], [18], [15, 4], [12, 8], [15, 6], [22], [18, 5], [10, 8, 6], [22, 3], [22, 4],
    [27], [22, 6], [27, 2], [22, 8], [27, 4], [32], [27, 6], [27, 5, 2], [32, 3], [27, 5, 4],
    [32, 5], [38], [27, 12], [32, 5, 3], [38, 3], [38, 4], [38, 5], [38, 6], [38, 4, 3], [46],
    [38, 5, 4], [38, 10], [46, 3], [46, 4], [46, 5], [46, 6], [46, 4, 3], [54], [46, 5, 4],
    [46, 10], [46, 8, 3], [54, 4], [54, 5], [46, 10, 4], [46, 15], [54, 8], [54, 5, 4], [64],
    [46, 15, 4], [54, 12], [64, 3], [54, 10, 4], [64, 5], [64, 6], [54, 12, 5], [64, 5, 3],
    [54, 15, 4], [64, 10], [64, 6, 5], [76], [64, 10, 3], [46, 32], [76, 3], [64, 10, 6], [76, 5],
    [76, 6], [54, 15, 10, 4], [76, 8], [64, 15, 6], [76, 10], [76, 8, 3], [76, 12], [89],
    [76, 8, 6], [89, 2], [89, 3], [89, 4], [89, 5], [89, 6], [89, 5, 2], [89, 8], [89, 5, 4],
    [89, 10], [89, 8, 3], [89, 12], [89, 10, 3], [89, 10, 4], [104], [89, 10, 6], [89, 15, 2],
    [104, 3], [89, 15, 4], [104, 5], [104, 6], [89, 22], [104, 5, 3], [89, 10, 8, 6], [104, 10],
    [104, 6, 5], [104, 12], [104, 10, 3], [89, 27, 2], [104, 15], [104, 10, 6], [104, 12, 5],
    [122], [89, 27, 5, 2], [89, 32, 3], [122, 3], [122, 4], [122, 5], [122, 6], [122, 4, 3],
    [122, 8], [122, 5, 4], [122, 10], [122, 8, 3], [122, 12], [122, 10, 3], [122, 10, 4],
    [122, 15], [122, 10, 6], [122, 12, 5], [122, 18], [122, 15, 4], [142], [122, 15, 6],
    [122, 22], [142, 3], [142, 4], [142, 5], [142, 6], [142, 4, 3], [142, 8], [142, 5, 4],
    [142, 10], [142, 8, 3], [142, 12], [142, 10, 3], [142, 10, 4], [142, 15], [142, 10, 6],
    [142, 12, 5], [142, 18], [142, 15, 4], [142, 12, 8], [142, 15, 6], [142, 22], [165],
    [142, 10, 8, 6], [165, 2], [142, 22, 4], [165, 4], [142, 22, 6], [165, 6], [142, 22, 8],
    [165, 8], [142, 32], [165, 10], [142, 22, 12], [165, 12], [142, 27, 5, 4], [165, 10, 4],
    [142, 38], [165, 10, 6], [142, 32, 5, 3], [165, 18], [142, 38, 4], [165, 12, 8], [142, 38, 6],
    [165, 22], [142, 46], [165, 10, 8, 6], [142, 38, 10], [165, 22, 4], [192], [165, 22, 6],
    [165, 27, 2], [165, 22, 8], [165, 27, 4], [192, 5], [165, 27, 6], [165, 22, 12], [165, 27, 8],
    [165, 22, 10, 4], [192, 10], [165, 38], [165, 27, 12], [165, 22, 18], [165, 27, 10, 4],
    [192, 15], [165, 27, 10, 6], [165, 38, 6], [192, 18], [165, 46], [165, 27, 12, 8],
    [165, 38, 10], [192, 22], [192, 18, 5], [165, 27, 10, 8, 6], [192, 15, 10], [165, 27, 22, 4],
    [192, 27], [192, 18, 10], [165, 46, 10], [222], [165, 54, 4], [192, 27, 5], [192, 18, 15],
    [222, 4], [222, 5], [165, 27, 22, 10, 4], [192, 27, 10], [222, 8], [222, 5, 4], [222, 10],
    [165, 54, 10, 4], [222, 12], [222, 8, 5], [222, 10, 4]],
    by decide +kernel⟩

/-! ## The representation conjecture below one million -/

theorem H1_le (n : ℕ) (hn : 0 < n) (hle : n ≤ 997436) : ∃ T : Finset ℕ,
    (∀ x ∈ T, ∃ m : ℕ, 0 < m ∧ x = strictPartitionCount m) ∧
    (∀ x ∈ T, ∀ y ∈ T, x ≠ y → ¬ x ∣ y) ∧
    (∑ x ∈ T, x) = n := by
  by_cases hs : n < 237
  · obtain ⟨W, hW⟩ := small_exists
    obtain ⟨hsum, hnd, hq, han⟩ := hW (n - 1) (by omega)
    refine ⟨(W.getD (n - 1) []).toFinset, ?_, ?_, ?_⟩
    · intro x hx; exact mem_qList (N := 28) (hq x (List.mem_toFinset.1 hx))
    · intro x hx y hy hxy hd
      exact han x (List.mem_toFinset.1 hx) y (List.mem_toFinset.1 hy) hxy
        (Nat.mod_eq_zero_of_dvd hd)
    · rw [List.sum_toFinset _ hnd, List.map_id', hsum]; omega
  · obtain ⟨seed, _hseedeq, hnd, hq, han, hmask⟩ := seed_exists
    have hb := testBit_of_mask _ _ _ hmask n (by omega) (by omega)
    obtain ⟨T, hT, hsum⟩ := (testBit_foldr seed hnd n).1 hb
    refine ⟨T, ?_, ?_, hsum⟩
    · intro x hx; exact mem_qList (N := 90) (hq x (List.mem_toFinset.1 (hT hx)))
    · intro x hx y hy hxy hd
      exact han x (List.mem_toFinset.1 (hT hx)) y (List.mem_toFinset.1 (hT hy)) hxy
        (Nat.mod_eq_zero_of_dvd hd)

/-! ## From sets to the target's form, and the greedy step -/

theorem rep_of_finset (T : Finset ℕ)
    (hq : ∀ x ∈ T, ∃ m : ℕ, 0 < m ∧ x = strictPartitionCount m)
    (hanti : ∀ x ∈ T, ∀ y ∈ T, x ≠ y → ¬ x ∣ y) :
    ∃ k : ℕ, ∃ terms : Fin k → ℕ,
      (∀ i, ∃ m : ℕ, 0 < m ∧ terms i = strictPartitionCount m) ∧
      (∑ i, terms i) = ∑ x ∈ T, x ∧
      (∀ i j, i ≠ j → ¬ terms i ∣ terms j) := by
  let e : T ≃ Fin T.card := T.equivFin
  refine ⟨T.card, fun i => (e.symm i : ℕ), ?_, ?_, ?_⟩
  · intro i
    exact hq _ (e.symm i).2
  · rw [Equiv.sum_comp e.symm (fun x : T => (x : ℕ))]
    exact Finset.sum_coe_sort T (fun x => x)
  · intro i j hij
    apply hanti _ (e.symm i).2 _ (e.symm j).2
    intro h
    exact hij (e.symm.injective (Subtype.ext h))

/-- The greedy extension step: adding a new element `a ≤ U + 1 - L` to a set whose subset
sums cover `[L, U]` yields a set whose subset sums cover `[L, U + a]`. -/
theorem extend_cover (S : Finset ℕ) (a L U : ℕ) (ha : a ∉ S)
    (hcov : ∀ n, L ≤ n → n ≤ U → ∃ T ⊆ S, (∑ x ∈ T, x) = n)
    (hle : a ≤ U + 1 - L) :
    ∀ n, L ≤ n → n ≤ U + a → ∃ T ⊆ insert a S, (∑ x ∈ T, x) = n := by
  intro n hLn hnU
  by_cases h : n ≤ U
  · obtain ⟨T, hT, hs⟩ := hcov n hLn h
    exact ⟨T, hT.trans (Finset.subset_insert a S), hs⟩
  · rw [not_le] at h
    obtain ⟨T, hT, hs⟩ := hcov (n - a) (by omega) (by omega)
    have haT : a ∉ T := fun h' => ha (hT h')
    refine ⟨insert a T, Finset.insert_subset_insert a hT, ?_⟩
    rw [Finset.sum_insert haT, hs]
    omega

theorem strictPartitionCount_pos (m : ℕ) (hm : 0 < m) : 0 < strictPartitionCount m := by
  unfold strictPartitionCount
  refine Finset.card_pos.2 ⟨Nat.Partition.indiscrete m, ?_⟩
  simp only [Nat.Partition.distincts, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [Nat.Partition.indiscrete_parts hm.ne']
  simp

theorem le_sum_of_positive (a : ℕ → ℕ) (hpos : ∀ i, 0 < a i) :
    ∀ r, r ≤ ∑ i ∈ Finset.range r, a i := by
  intro r
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Finset.sum_range_succ]
    have hr := hpos r
    omega

theorem chain_width (a : ℕ → ℕ) (L U : ℕ) (hLU : L ≤ U)
    (h0 : a 0 ≤ U + 1 - L)
    (hd : ∀ i, a (i + 1) ≤ 2 * a i) :
    ∀ r, a r ≤ (U + ∑ i ∈ Finset.range r, a i) + 1 - L := by
  intro r
  induction r with
  | zero => simpa using h0
  | succ r ih =>
    have hdoub := hd r
    rw [Finset.sum_range_succ]
    omega

theorem chain_cover (seed : List ℕ) (a : ℕ → ℕ) (L U : ℕ) (hLU : L ≤ U)
    (hcov0 : ∀ n, L ≤ n → n ≤ U → ∃ T ⊆ seed.toFinset, (∑ x ∈ T, x) = n)
    (h0 : a 0 ≤ U + 1 - L)
    (hd : ∀ i, a (i + 1) ≤ 2 * a i)
    (hstrict : StrictMono a)
    (hnotseed : ∀ i, a i ∉ seed.toFinset) :
    ∀ r n, L ≤ n → n ≤ U + ∑ i ∈ Finset.range r, a i →
      ∃ T ⊆ seed.toFinset ∪ (Finset.range r).image a, (∑ x ∈ T, x) = n := by
  intro r
  induction r with
  | zero =>
    intro n hLn hn
    have hnU : n ≤ U := by simpa using hn
    obtain ⟨T, hT, hs⟩ := hcov0 n hLn hnU
    refine ⟨T, ?_, hs⟩
    intro x hx
    exact Finset.mem_union_left _ (hT hx)
  | succ r ih =>
    intro n hLn hn
    have hwidth := chain_width a L U hLU h0 hd r
    have hnotin : a r ∉ seed.toFinset ∪ (Finset.range r).image a := by
      intro hmem
      rcases Finset.mem_union.1 hmem with hseed | himg
      · exact hnotseed r hseed
      · rcases Finset.mem_image.1 himg with ⟨i, hir, hia⟩
        have hirlt : i < r := Finset.mem_range.1 hir
        have hlt : a i < a r := hstrict hirlt
        rw [hia] at hlt
        exact (lt_irrefl _ hlt)
    have hcovr : ∀ m, L ≤ m → m ≤ U + ∑ i ∈ Finset.range r, a i →
        ∃ T ⊆ seed.toFinset ∪ (Finset.range r).image a, (∑ x ∈ T, x) = m := ih
    have step := extend_cover (seed.toFinset ∪ (Finset.range r).image a) (a r) L
      (U + ∑ i ∈ Finset.range r, a i) hnotin hcovr hwidth
    rw [Finset.sum_range_succ] at hn
    have hn' : n ≤ U + (∑ i ∈ Finset.range r, a i) + a r := by omega
    obtain ⟨T, hT, hs⟩ := step n hLn hn'
    refine ⟨T, ?_, hs⟩
    intro x hx
    have hxins := hT hx
    rcases Finset.mem_insert.1 hxins with rfl | hxS
    · exact Finset.mem_union_right _ (Finset.mem_image.2 ⟨r, by simp, rfl⟩)
    · rcases Finset.mem_union.1 hxS with hseed | himg
      · exact Finset.mem_union_left _ hseed
      · rcases Finset.mem_image.1 himg with ⟨i, hir, hia⟩
        refine Finset.mem_union_right _ (Finset.mem_image.2 ⟨i, ?_, hia⟩)
        exact Finset.mem_range.2 (Nat.lt_trans (Finset.mem_range.1 hir) (Nat.lt_succ_self r))


theorem tail_from_coverage (seed : List ℕ) (a : ℕ → ℕ)
    (hcov0 : ∀ n, 237 ≤ n → n ≤ 997436 → ∃ T ⊆ seed.toFinset, (∑ x ∈ T, x) = n)
    (hseedq : ∀ x ∈ seed, ∃ m : ℕ, 0 < m ∧ x = strictPartitionCount m)
    (hseedanti : ∀ x ∈ seed, ∀ y ∈ seed, x ≠ y → ¬ x ∣ y)
    (haq : ∀ i, ∃ m : ℕ, 0 < m ∧ a i = strictPartitionCount m)
    (hstrict : StrictMono a)
    (ha0 : a 0 ≤ 997200)
    (hdoub : ∀ i, a (i + 1) ≤ 2 * a i)
    (haseqanti : ∀ i j, i ≠ j → ¬ a i ∣ a j)
    (hcross : ∀ x ∈ seed, ∀ i, (¬ x ∣ a i) ∧ (¬ a i ∣ x))
    (n : ℕ) (hn : 997436 < n) : ∃ T : Finset ℕ,
    (∀ x ∈ T, ∃ m : ℕ, 0 < m ∧ x = strictPartitionCount m) ∧
    (∀ x ∈ T, ∀ y ∈ T, x ≠ y → ¬ x ∣ y) ∧
    (∑ x ∈ T, x) = n := by
  have hnotseed : ∀ i, a i ∉ seed.toFinset := by
    intro i hi
    have hxmem : a i ∈ seed := List.mem_toFinset.1 hi
    exact (hcross (a i) hxmem i).1 dvd_rfl
  have hpos : ∀ i, 0 < a i := by
    intro i
    obtain ⟨m, hm, hai⟩ := haq i
    rw [hai]
    exact strictPartitionCount_pos m hm
  have hsumlower := le_sum_of_positive a hpos n
  have hnU : n ≤ 997436 + ∑ i ∈ Finset.range n, a i := by omega
  have ha0' : a 0 ≤ 997436 + 1 - 237 := by omega
  obtain ⟨T, hT, hsum⟩ := chain_cover seed a 237 997436 (by omega) hcov0 ha0' hdoub
    hstrict hnotseed n n (by omega) hnU
  refine ⟨T, ?_, ?_, hsum⟩
  · intro x hx
    have hxu := hT hx
    rcases Finset.mem_union.1 hxu with hxseed | hxseq
    · exact hseedq x (List.mem_toFinset.1 hxseed)
    · rcases Finset.mem_image.1 hxseq with ⟨i, _hi, rfl⟩
      exact haq i
  · intro x hx y hy hxy hd
    have hxu := hT hx
    have hyu := hT hy
    rcases Finset.mem_union.1 hxu with hxseed | hxseq <;>
      rcases Finset.mem_union.1 hyu with hyseed | hyseq
    · exact hseedanti x (List.mem_toFinset.1 hxseed) y (List.mem_toFinset.1 hyseed) hxy hd
    · rcases Finset.mem_image.1 hyseq with ⟨j, _hj, rfl⟩
      exact (hcross x (List.mem_toFinset.1 hxseed) j).1 hd
    · rcases Finset.mem_image.1 hxseq with ⟨i, _hi, rfl⟩
      exact (hcross y (List.mem_toFinset.1 hyseed) i).2 hd
    · rcases Finset.mem_image.1 hxseq with ⟨i, _hi, rfl⟩
      rcases Finset.mem_image.1 hyseq with ⟨j, _hj, rfl⟩
      have hij : i ≠ j := fun h => hxy (congrArg a h)
      exact haseqanti i j hij hd

theorem main : H1 → H2 → H3 → H4 → type_of% @OMA.S_oeis_a000009.main := by
  intro h1 h2 h3 h4
  refine ⟨?_, fun n hn => ⟨h2 n hn, h3 n hn, h4 n hn⟩⟩
  intro n hn
  obtain ⟨T, hq, hanti, hsum⟩ : ∃ T : Finset ℕ,
      (∀ x ∈ T, ∃ m : ℕ, 0 < m ∧ x = strictPartitionCount m) ∧
      (∀ x ∈ T, ∀ y ∈ T, x ≠ y → ¬ x ∣ y) ∧ (∑ x ∈ T, x) = n := by
    by_cases hb : n ≤ 997436
    · exact H1_le n hn hb
    · obtain ⟨a, haq, hstrict, ha0, hdoub, haseqanti, hcross⟩ := h1
      obtain ⟨seed, hseedeq, hnd, hqmem, hanmod, hmask⟩ := seed_exists
      have hcov0 : ∀ m, 237 ≤ m → m ≤ 997436 →
          ∃ T ⊆ seed.toFinset, (∑ x ∈ T, x) = m := by
        intro m hmL hmU
        have hb := testBit_of_mask _ _ _ hmask m hmL (by omega)
        exact (testBit_foldr seed hnd m).1 hb
      have hseedq : ∀ x ∈ seed, ∃ m : ℕ, 0 < m ∧ x = strictPartitionCount m := by
        intro x hx
        exact mem_qList (N := 90) (hqmem x hx)
      have hseedanti : ∀ x ∈ seed, ∀ y ∈ seed, x ≠ y → ¬ x ∣ y := by
        intro x hx y hy hxy hd
        exact hanmod x hx y hy hxy (Nat.mod_eq_zero_of_dvd hd)
      have hcross' : ∀ x ∈ seed, ∀ i, (¬ x ∣ a i) ∧ (¬ a i ∣ x) := by
        rw [hseedeq]
        exact hcross
      exact tail_from_coverage seed a hcov0 hseedq hseedanti haq hstrict ha0 hdoub
        haseqanti hcross' n (by omega)
  obtain ⟨k, terms, hterms, hs, hdiv⟩ := rep_of_finset T hq hanti
  exact ⟨k, terms, hterms, hs.trans hsum, hdiv⟩

end OMA.R_oeis_a000009_R3
