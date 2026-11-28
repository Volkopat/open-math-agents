import OMAStatements.S_oeis_a000009

/-!
# Reduction oeis-a000009.R8 of A000009 (two conjectures of Zhi-Wei Sun)

Credit: @Jwolf52

Refines R6: the same three open steps, with the proved range of the representation
conjecture raised from `n ≤ 141959953174382074575523` (about `1.4 · 10^23`) to
`n ≤ 1900360634358457428632022870866610` (about `1.9 · 10^33`). A greedy chain of 741 further
values `q(m)`, `96 ≤ m ≤ 2000`, extends the seed cover (`chain_inv`, `H1_chain`). Each value is
compatible with all kept values and at most `U + 1 - 237`. One Boolean fold, checked by the
kernel, certifies the whole chain. The q-values come from a guarded packed table with 111-bit
slots (one guard bit per slot, checked after every row), not `N + 1`-bit slots.

* `H1`: the representation conjecture for `n > 1900360634358457428632022870866610`.
* `H2`, `H3`: the three non-divisibility conjectures, for `n > 1000`, in a reduced form.
  For `n > 7`, `q(n) ≥ 3`, so `q(n)` divides at most one of `p(n) - 1, p(n), p(n) + 1`
  (`at_most_one`). Together they say `2 ≤ p(n) % q(n) ≤ q(n) - 2` (`three_iff_mod`).
  `q(n)` is odd exactly when `n` is a generalized pentagonal number
  (`strictPartitionCount_odd_iff`, from Mathlib's pentagonal number theorem reduced mod 2).
  When `q(n)` is even, the parity of `p(n)` settles two of the three claims (`parity_split`).
  So only pentagonal `n` need the full condition, and every other `n` needs one claim.

Proved unconditionally here (no `native_decide`; kernel evaluation only):
* everything in R2: the `q`-table, the subset-sum bitset, `H1_le`, `rep_of_finset`, `extend_cover`;
* `partitionCount_eq_rec`: `p(n)` equals entry `n` of a list DP, through the recursion
  `c(K+1, n) = c(K, n) + c(K+1, n - (K+1))` for partitions with parts `≤ K`
  (`bounded_succ`, via Mathlib's `partitionWithPartEquiv`);
* `pack_digit`, `pack_add`, `pack_shift`, `pack_take`: packed lists with `w`-bit slots;
* `strictPartitionCount_eq_packed`, `partitionCount_eq_packed`: `q(n)` and `p(n)` are slot `n` of
  packed tables. The p-step multiplies by a truncated geometric series (`geo_iter`). The slot
  width is safe because `p(n) ≤ 2 ^ n` (`partitionCount_le_two_pow`, via compositions);
* `nondiv_le`: `q(n)` divides none of `p(n), p(n) - 1, p(n) + 1` for `8 ≤ n ≤ 1000`
  (about 25 s and 9.4 GB in a local check);
* `lt_of_testBit_false`, `testBit_pack`, `entries_lt_of_guard`, `Q_eq_pack_guard`, `guard_pass`,
  `strictPartitionCount_eq_guarded`: guarded packed tables. With slot width `v + 1`, if no guard
  bit (bit `v` of a slot) is set after a row, every entry of the row is below `2 ^ v`. The next
  q-step adds two such entries and cannot overflow a slot. A failed guard sends the one-pass
  recursion to `0`, so one check `≠ 0` certifies every row;
* `chain_step`, `chain_flag`, `chain_inv`: a general chain certificate for `extend_cover`;
  `H1_chain`: the representation conjecture for `237 ≤ n ≤ 1900360634358457428632022870866610`;
* `three_iff_mod`, `at_most_one`, `parity_split`, `strictPartitionCount_odd_iff`, `H234_of_pentagonal`.
-/

namespace OMA.R_oeis_a000009_R8

open OMA.S_oeis_a000009

/-- The H1 core: above `X0 = 1900360634358457428632022870866610 / 2 + 1`, every interval `[x, 3x/2]` contains a primitive
q-value: one that no q-value `s` with `18 ≤ s ≤ a / 2` divides. -/
def H1 : Prop :=
  ∀ x : ℕ, 1900360634358457428632022870866610 / 2 + 1 ≤ x → ∃ a : ℕ, (∃ m : ℕ, 0 < m ∧ a = strictPartitionCount m) ∧
    x ≤ a ∧ 2 * a ≤ 3 * x ∧ ∀ s : ℕ, (∃ m : ℕ, 0 < m ∧ s = strictPartitionCount m) →
      18 ≤ s → 2 * s ≤ a → ¬ s ∣ a

/-- `q(n) ∤ p(n)`, needed only when `n` is pentagonal or `p(n)` is even. -/
def H2 : Prop :=
  ∀ n : ℕ, 1000 < n → (n ∈ Set.range pentagonal ∨ partitionCount n % 2 = 0) →
    ¬ strictPartitionCount n ∣ partitionCount n

/-- `2 ≤ p(n) % q(n) ≤ q(n) - 2`, needed only when `n` is pentagonal or `p(n)` is odd. -/
def H3 : Prop :=
  ∀ n : ℕ, 1000 < n → (n ∈ Set.range pentagonal ∨ partitionCount n % 2 = 1) →
    2 ≤ partitionCount n % strictPartitionCount n ∧
      partitionCount n % strictPartitionCount n + 2 ≤ strictPartitionCount n

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

theorem seed_exists : ∃ seed : List ℕ, seed.Nodup ∧
    (∀ x ∈ seed, x ∈ (Nat.rec (motive := fun _ => List ℕ) (1 :: List.replicate 90 0)
      (fun k l => List.zipWith (· + ·) l (List.replicate (k + 1) 0 ++ l)) 90).drop 1) ∧
    (∀ x ∈ seed, ∀ y ∈ seed, x ≠ y → y % x ≠ 0) ∧
    ((seed.foldr (fun a b => b ||| b <<< a) 1) >>> 237) % 2 ^ 997200 = 2 ^ 997200 - 1 :=
  ⟨[18, 22, 27, 32, 38, 46, 89, 104, 122, 142, 165, 222, 296, 340, 390, 585, 668,
    982, 1113, 1816, 2590, 2910, 3658, 4097, 4582, 5718, 6378, 7108, 7917, 8808, 12076, 13394,
    16444, 20132, 27130, 29927, 48446, 58499, 64234, 84756, 101698, 111322, 159046, 189586],
    by decide +kernel⟩

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
  · obtain ⟨seed, hnd, hq, han, hmask⟩ := seed_exists
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

/-! ## `p(n)` as a table -/

/-- Partitions of `n` with every part at most `K`. -/
theorem pc_le_card (n : ℕ) : ∀ p : n.Partition, ∀ i ∈ p.parts, i ≤ n := by
  intro p i hi
  have := Multiset.le_sum_of_mem hi
  rw [p.parts_sum] at this
  exact this

theorem partitionCount_eq_bounded (n : ℕ) :
    partitionCount n = (Finset.univ.filter (fun p : n.Partition => ∀ i ∈ p.parts, i ≤ n)).card := by
  unfold partitionCount
  rw [Finset.filter_true_of_mem (fun p _ => pc_le_card n p), Finset.card_univ]

theorem bounded_zero (n : ℕ) :
    (Finset.univ.filter (fun p : n.Partition => ∀ i ∈ p.parts, i ≤ 0)).card =
      if n = 0 then 1 else 0 := by
  have key : ∀ p : n.Partition, (∀ i ∈ p.parts, i ≤ 0) ↔ p.parts = 0 := by
    intro p
    constructor
    · intro h
      rw [Multiset.eq_zero_iff_forall_notMem]
      intro i hi
      have := p.parts_pos hi
      have := h i hi
      omega
    · intro h i hi
      rw [h] at hi
      simp at hi
  simp only [key]
  split_ifs with hn
  · subst hn
    rw [Finset.card_eq_one]
    refine ⟨Nat.Partition.indiscrete 0, ?_⟩
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro _; exact Subsingleton.elim _ _
    · intro _
      have := p.parts_sum
      rw [Multiset.eq_zero_iff_forall_notMem]
      intro i hi
      have h1 := p.parts_pos hi
      have h2 := Multiset.le_sum_of_mem hi
      omega
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro p _ hp
    have := p.parts_sum
    rw [hp] at this
    simp at this
    omega

theorem bounded_succ (K n : ℕ) :
    (Finset.univ.filter (fun p : n.Partition => ∀ i ∈ p.parts, i ≤ K + 1)).card =
      (Finset.univ.filter (fun p : n.Partition => ∀ i ∈ p.parts, i ≤ K)).card +
        if K + 1 ≤ n then
          (Finset.univ.filter (fun p : (n - (K + 1)).Partition => ∀ i ∈ p.parts, i ≤ K + 1)).card
        else 0 := by
  rw [← Finset.card_filter_add_card_filter_not (fun p : n.Partition => K + 1 ∈ p.parts),
    Finset.filter_filter, Finset.filter_filter, add_comm]
  congr 1
  · congr 1
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨h, hK⟩ i hi
      have := h i hi
      have : i ≠ K + 1 := fun e => hK (e ▸ hi)
      omega
    · intro h
      exact ⟨fun i hi => by have := h i hi; omega, fun hm => by have := h _ hm; omega⟩
  · split_ifs with hn
    · refine Finset.card_bij'
        (fun p hp => Nat.Partition.partitionWithPartEquiv (by omega) hn
          ⟨p, (Finset.mem_filter.1 hp).2.2⟩)
        (fun q _ => ((Nat.Partition.partitionWithPartEquiv (n := n) (a := K + 1)
          (by omega) hn).symm q).1) ?_ ?_ ?_ ?_
      · intro p hp
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
        intro i hi
        rw [Nat.Partition.partitionWithPartEquiv_apply_parts] at hi
        exact hp.1 i (Multiset.mem_of_mem_erase hi)
      · intro q hq
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
        rw [Nat.Partition.partitionWithPartEquiv_symm_apply_parts]
        refine ⟨fun i hi => ?_, Multiset.mem_cons_self _ _⟩
        rcases Multiset.mem_cons.1 hi with h | h
        · omega
        · exact hq i h
      · intro p hp
        simp
      · intro q hq
        simp
    · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      rintro p _ ⟨_, hm⟩
      have := pc_le_card n p _ hm
      omega


theorem bounded_of_le (n : ℕ) : ∀ K, n ≤ K →
    (Finset.univ.filter (fun p : n.Partition => ∀ i ∈ p.parts, i ≤ K)).card =
      (Finset.univ.filter (fun p : n.Partition => ∀ i ∈ p.parts, i ≤ n)).card := by
  intro K hK
  induction K, hK using Nat.le_induction with
  | base => rfl
  | succ K hK ih => rw [bounded_succ, if_neg (by omega), add_zero, ih]

/-- The reversed scan computing `new i = old i + new (i - (k+1))`. -/
theorem scan_spec (N k : ℕ) (old : List ℕ) (f : ℕ → ℕ)
    (hf : ∀ i ≤ N, f i = old.getD i 0 + if k + 1 ≤ i then f (i - (k + 1)) else 0) :
    ∀ m ≤ N + 1, (Nat.rec (motive := fun _ => List ℕ) []
      (fun i r => (old.getD i 0 + if k + 1 ≤ i then r.getD k 0 else 0) :: r) m).length = m ∧
      ∀ j < m, (Nat.rec (motive := fun _ => List ℕ) []
      (fun i r => (old.getD i 0 + if k + 1 ≤ i then r.getD k 0 else 0) :: r) m).getD j 0 =
        f (m - 1 - j) := by
  intro m hm
  induction m with
  | zero => simp
  | succ m ih =>
    obtain ⟨hlen, hget⟩ := ih (by omega)
    refine ⟨congrArg Nat.succ hlen, ?_⟩
    intro j hj
    rcases j with _ | j
    · show List.getD (_ :: _) 0 0 = _
      rw [List.getD_cons_zero, show m + 1 - 1 - 0 = m by omega, hf m (by omega)]
      congr 1
      split_ifs with h
      · rw [hget k (by omega)]; congr 1; omega
      · rfl
    · show List.getD (_ :: _) (j + 1) 0 = _
      rw [List.getD_cons_succ, hget j (by omega)]
      congr 1; omega

theorem getD_reverse_of_lt (l : List ℕ) (i : ℕ) (hi : i < l.length) :
    l.reverse.getD i 0 = l.getD (l.length - 1 - i) 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_reverse hi]

theorem scan_rev (N k : ℕ) (old : List ℕ) (f : ℕ → ℕ)
    (hf : ∀ i ≤ N, f i = old.getD i 0 + if k + 1 ≤ i then f (i - (k + 1)) else 0) :
    ∀ i ≤ N, (Nat.rec (motive := fun _ => List ℕ) []
      (fun i r => (old.getD i 0 + if k + 1 ≤ i then r.getD k 0 else 0) :: r) (N + 1)).reverse.getD
        i 0 = f i := by
  intro i hi
  obtain ⟨hlen, hget⟩ := scan_spec N k old f hf (N + 1) le_rfl
  rw [getD_reverse_of_lt _ i (by omega), hlen, hget _ (by omega)]
  congr 1; omega

/-- Row `K` of the table holds the number of partitions of `i` with parts `≤ K`. -/
theorem prow_spec (N : ℕ) (K : ℕ) :
    (Nat.rec (motive := fun _ => List ℕ) (1 :: List.replicate N 0)
      (fun k old => (Nat.rec (motive := fun _ => List ℕ) []
        (fun i r => (old.getD i 0 + if k + 1 ≤ i then r.getD k 0 else 0) :: r) (N + 1)).reverse)
      K).length = N + 1 ∧
    ∀ i ≤ N, (Nat.rec (motive := fun _ => List ℕ) (1 :: List.replicate N 0)
      (fun k old => (Nat.rec (motive := fun _ => List ℕ) []
        (fun i r => (old.getD i 0 + if k + 1 ≤ i then r.getD k 0 else 0) :: r) (N + 1)).reverse)
      K).getD i 0 =
      (Finset.univ.filter (fun p : i.Partition => ∀ j ∈ p.parts, j ≤ K)).card := by
  induction K with
  | zero =>
    refine ⟨by simp, fun i hi => ?_⟩
    rw [bounded_zero]
    rcases i with _ | i
    · simp
    · simp [List.getD_eq_getElem?_getD, List.getElem?_replicate]; split <;> rfl
  | succ K ih =>
    obtain ⟨_, hrow⟩ := ih
    have hf : ∀ i ≤ N,
        (Finset.univ.filter (fun p : i.Partition => ∀ j ∈ p.parts, j ≤ K + 1)).card =
          (Nat.rec (motive := fun _ => List ℕ) (1 :: List.replicate N 0)
            (fun k old => (Nat.rec (motive := fun _ => List ℕ) []
              (fun i r => (old.getD i 0 + if k + 1 ≤ i then r.getD k 0 else 0) :: r)
                (N + 1)).reverse) K).getD i 0 +
          if K + 1 ≤ i then
            (Finset.univ.filter (fun p : (i - (K + 1)).Partition => ∀ j ∈ p.parts, j ≤ K + 1)).card
          else 0 := by
      intro i hi
      rw [hrow i hi, bounded_succ]
    obtain ⟨hlen, _⟩ := scan_spec N K _ _ hf (N + 1) le_rfl
    exact ⟨by simp only [List.length_reverse]; exact hlen, scan_rev N K _ _ hf⟩

/-- One table gives every value `p(n)` with `n ≤ N`. -/
theorem partitionCount_eq_rec (N n : ℕ) (hn : n ≤ N) :
    partitionCount n = (Nat.rec (motive := fun _ => List ℕ) (1 :: List.replicate N 0)
      (fun k old => (Nat.rec (motive := fun _ => List ℕ) []
        (fun i r => (old.getD i 0 + if k + 1 ≤ i then r.getD k 0 else 0) :: r) (N + 1)).reverse)
      N).getD n 0 := by
  rw [(prow_spec N N).2 n hn, bounded_of_le n N hn, ← partitionCount_eq_bounded]

/-! ## Step 2: the three non-divisibility claims are one statement about `P % Q` -/

theorem succ_mod_of_lt (x Q : ℕ) (hx : x < Q) : (x + 1) % Q = if x + 1 = Q then 0 else x + 1 := by
  split_ifs with h
  · rw [h, Nat.mod_self]
  · exact Nat.mod_eq_of_lt (by omega)

/-- For `Q ≥ 3` and `P ≥ 1`: `Q` divides none of `P - 1, P, P + 1` iff `2 ≤ P % Q ≤ Q - 2`. -/
theorem three_iff_mod (P Q : ℕ) (hP : 1 ≤ P) (hQ : 3 ≤ Q) :
    (¬ Q ∣ P ∧ ¬ Q ∣ P - 1 ∧ ¬ Q ∣ P + 1) ↔ (2 ≤ P % Q ∧ P % Q + 2 ≤ Q) := by
  simp only [Nat.dvd_iff_mod_eq_zero]
  have hr : P % Q < Q := Nat.mod_lt _ (by omega)
  have hs : (P - 1) % Q < Q := Nat.mod_lt _ (by omega)
  have h1 : P % Q = ((P - 1) % Q + 1) % Q := by
    conv_lhs => rw [show P = (P - 1) + 1 by omega]
    rw [Nat.add_mod, Nat.mod_eq_of_lt (show 1 < Q by omega)]
  have h2 : (P + 1) % Q = (P % Q + 1) % Q := by
    rw [Nat.add_mod, Nat.mod_eq_of_lt (show 1 < Q by omega)]
  rw [succ_mod_of_lt _ _ hs] at h1
  rw [succ_mod_of_lt _ _ hr] at h2
  split_ifs at h1 h2 <;> omega

/-- At most one of the three divisibilities can hold (for `Q ≥ 3`). -/
theorem at_most_one (P Q : ℕ) (hP : 1 ≤ P) (hQ : 3 ≤ Q) :
    (Q ∣ P → ¬ Q ∣ P - 1 ∧ ¬ Q ∣ P + 1) ∧ (Q ∣ P - 1 → ¬ Q ∣ P + 1) := by
  refine ⟨fun h => ⟨fun h' => ?_, fun h' => ?_⟩, fun h h' => ?_⟩
  · have := Nat.dvd_sub h h'; rw [show P - (P - 1) = 1 by omega] at this
    exact absurd (Nat.le_of_dvd one_pos this) (by omega)
  · have := Nat.dvd_sub h' h; rw [show P + 1 - P = 1 by omega] at this
    exact absurd (Nat.le_of_dvd one_pos this) (by omega)
  · have := Nat.dvd_sub h' h; rw [show P + 1 - (P - 1) = 2 by omega] at this
    exact absurd (Nat.le_of_dvd two_pos this) (by omega)

/-! ## Step 3: the parity split -/

/-- If `Q` is even, the parity of `P` rules out either `Q ∣ P` or both `Q ∣ P ∓ 1`. -/
theorem parity_split (P Q : ℕ) (hP : 1 ≤ P) (hQ : 2 ∣ Q) :
    (P % 2 = 1 → ¬ Q ∣ P) ∧ (P % 2 = 0 → ¬ Q ∣ P - 1 ∧ ¬ Q ∣ P + 1) := by
  refine ⟨fun h hd => ?_, fun h => ⟨fun hd => ?_, fun hd => ?_⟩⟩
  · have := Nat.mod_eq_zero_of_dvd (hQ.trans hd); omega
  · have := Nat.mod_eq_zero_of_dvd (hQ.trans hd); omega
  · have := Nat.mod_eq_zero_of_dvd (hQ.trans hd); omega

/-! ## Side facts: `p(n) ≥ 1`, `q(n) ≥ 3` for `n ≥ 5` -/

theorem partitionCount_pos (n : ℕ) : 1 ≤ partitionCount n :=
  Fintype.card_pos_iff.2 ⟨Nat.Partition.indiscrete n⟩

theorem three_le_strictPartitionCount (n : ℕ) (hn : 5 ≤ n) : 3 ≤ strictPartitionCount n := by
  rw [strictPartitionCount_eq_subsetCount]
  have hsub : ({{n}, {1, n - 1}, {2, n - 2}} : Finset (Finset ℕ)) ⊆
      (Finset.Icc 1 n).powerset.filter (fun s => ∑ x ∈ s, x = n) := by
    intro s hs
    simp only [Finset.mem_insert, Finset.mem_singleton] at hs
    simp only [Finset.mem_filter, Finset.mem_powerset]
    rcases hs with rfl | rfl | rfl
    · exact ⟨by intro x hx; simp at hx; simp [hx]; omega, by simp⟩
    · refine ⟨by intro x hx; simp at hx; rcases hx with rfl | rfl <;> simp <;> omega, ?_⟩
      rw [Finset.sum_pair (by omega)]; omega
    · refine ⟨by intro x hx; simp at hx; rcases hx with rfl | rfl <;> simp <;> omega, ?_⟩
      rw [Finset.sum_pair (by omega)]; omega
  have hcard : ({{n}, {1, n - 1}, {2, n - 2}} : Finset (Finset ℕ)).card = 3 := by
    have a1 : ({n} : Finset ℕ) ≠ {1, n - 1} := by
      intro h; have := congrArg Finset.card h
      rw [Finset.card_singleton, Finset.card_pair (by omega)] at this; omega
    have a2 : ({n} : Finset ℕ) ≠ {2, n - 2} := by
      intro h; have := congrArg Finset.card h
      rw [Finset.card_singleton, Finset.card_pair (by omega)] at this; omega
    have a3 : ({1, n - 1} : Finset ℕ) ≠ {2, n - 2} := by
      intro h; have : (1 : ℕ) ∈ ({2, n - 2} : Finset ℕ) := h ▸ by simp
      simp at this; omega
    rw [Finset.card_insert_of_notMem (by simp [a1, a2]), Finset.card_pair a3]
  exact hcard ▸ Finset.card_le_card hsub


/-! ## Step 4: `q(n)` is odd iff `n` is a generalized pentagonal number -/

open PowerSeries PowerSeries.WithPiTopology in
/-- 4b: in characteristic 2, `1 + X^k = 1 - X^k`. -/
theorem one_add_X_pow_eq_one_sub (k : ℕ) :
    (1 + X ^ k : (ZMod 2)⟦X⟧) = 1 - X ^ k := by
  ext m
  simp only [map_add, map_sub, coeff_one, coeff_X_pow]
  split_ifs <;> decide

open PowerSeries PowerSeries.WithPiTopology in
/-- 4a–4e: `q(n)` is odd iff `n` is a generalized pentagonal number. -/
theorem strictPartitionCount_odd_iff (n : ℕ) :
    strictPartitionCount n % 2 = 1 ↔ n ∈ Set.range pentagonal := by
  let _ : TopologicalSpace (ZMod 2) := ⊥
  have _ : DiscreteTopology (ZMod 2) := ⟨rfl⟩
  have h1 := Nat.Partition.hasProd_powerSeriesMk_card_countRestricted (ZMod 2) (m := 2) two_pos
  have hfac : (fun i : ℕ => ∑ j ∈ Finset.range 2, (X : (ZMod 2)⟦X⟧) ^ ((i + 1) * j)) =
      fun i => 1 - X ^ (i + 1) := by
    funext i
    rw [Finset.sum_range_succ, Finset.sum_range_one, mul_zero, pow_zero, mul_one,
      one_add_X_pow_eq_one_sub]
  rw [hfac] at h1
  have heq := h1.unique (hasProd_one_sub_X_pow (ZMod 2))
  have hc := congrArg (PowerSeries.coeff n) heq
  rw [PowerSeries.coeff_mk, Nat.Partition.countRestricted_two] at hc
  have key : ((strictPartitionCount n : ℕ) : ZMod 2) = 0 ↔ n ∉ Set.range pentagonal := by
    rw [← coeff_pentagonalSeries_eq_zero_iff (R := ZMod 2), ← hc]
    rfl
  rw [ZMod.natCast_eq_zero_iff, Nat.dvd_iff_mod_eq_zero] at key
  constructor
  · intro h
    by_contra hn
    have := key.2 hn
    omega
  · intro hn
    by_contra h
    exact (key.1 (by omega)) hn

/-! ## Packed tables: one natural number per row, with `w`-bit slots -/

/-- A packed list with slot width `w` is less than `2 ^ (w * length)`. -/
theorem pack_lt (w : ℕ) (l : List ℕ) (hl : ∀ x ∈ l, x < 2 ^ w) :
    l.foldr (fun a acc => a + 2 ^ w * acc) 0 < 2 ^ (w * l.length) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have ha : a < 2 ^ w := hl a (by simp)
    have hP := ih (fun x hx => hl x (by simp [hx]))
    simp only [List.foldr_cons, List.length_cons]
    calc a + 2 ^ w * l.foldr (fun a acc => a + 2 ^ w * acc) 0
        < 2 ^ w * (l.foldr (fun a acc => a + 2 ^ w * acc) 0 + 1) := by rw [mul_add]; omega
      _ ≤ 2 ^ w * 2 ^ (w * l.length) := Nat.mul_le_mul_left _ hP
      _ = 2 ^ (w * (l.length + 1)) := by rw [← pow_add]; ring_nf

/-- Slot `i` of a packed list is entry `i`. -/
theorem pack_digit (w : ℕ) (l : List ℕ) (hl : ∀ x ∈ l, x < 2 ^ w) (i : ℕ) :
    (l.foldr (fun a acc => a + 2 ^ w * acc) 0 / 2 ^ (w * i)) % 2 ^ w = l.getD i 0 := by
  induction l generalizing i with
  | nil => simp
  | cons a l ih =>
    have ha : a < 2 ^ w := hl a (by simp)
    have hl' : ∀ x ∈ l, x < 2 ^ w := fun x hx => hl x (by simp [hx])
    have hpos : 0 < 2 ^ w := Nat.two_pow_pos w
    simp only [List.foldr_cons]
    rcases i with _ | i
    · rw [mul_zero, pow_zero, Nat.div_one, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha]
      simp
    · rw [show w * (i + 1) = w + w * i by ring, pow_add, ← Nat.div_div_eq_div_mul,
        Nat.add_mul_div_left _ _ hpos, Nat.div_eq_of_lt ha, zero_add, ih hl' i]
      simp

theorem pack_append (w : ℕ) (l₁ l₂ : List ℕ) :
    (l₁ ++ l₂).foldr (fun a acc => a + 2 ^ w * acc) 0 =
      l₁.foldr (fun a acc => a + 2 ^ w * acc) 0 +
        2 ^ (w * l₁.length) * l₂.foldr (fun a acc => a + 2 ^ w * acc) 0 := by
  induction l₁ with
  | nil => simp
  | cons a l₁ ih =>
    simp only [List.cons_append, List.foldr_cons, List.length_cons, ih]
    rw [show w * (l₁.length + 1) = w + w * l₁.length by ring, pow_add]
    ring

theorem pack_replicate_zero (w k : ℕ) :
    (List.replicate k 0).foldr (fun a acc => a + 2 ^ w * acc) 0 = 0 := by
  induction k with
  | zero => simp
  | succ k ih => simp [List.replicate_succ, ih]

/-- A shift by `k` slots is a multiplication by `2 ^ (w * k)`. -/
theorem pack_shift (w k : ℕ) (l : List ℕ) :
    (List.replicate k 0 ++ l).foldr (fun a acc => a + 2 ^ w * acc) 0 =
      2 ^ (w * k) * l.foldr (fun a acc => a + 2 ^ w * acc) 0 := by
  rw [pack_append, pack_replicate_zero, List.length_replicate, zero_add]

/-- Entrywise addition (equal lengths) is addition of the packed numbers. -/
theorem pack_add (w : ℕ) (l₁ l₂ : List ℕ) (h : l₁.length = l₂.length) :
    (List.zipWith (· + ·) l₁ l₂).foldr (fun a acc => a + 2 ^ w * acc) 0 =
      l₁.foldr (fun a acc => a + 2 ^ w * acc) 0 + l₂.foldr (fun a acc => a + 2 ^ w * acc) 0 := by
  induction l₁ generalizing l₂ with
  | nil => cases l₂ <;> simp_all
  | cons a l₁ ih =>
    cases l₂ with
    | nil => simp at h
    | cons b l₂ =>
      simp only [List.zipWith_cons_cons, List.foldr_cons, List.length_cons] at h ⊢
      rw [ih l₂ (by omega)]
      ring

/-- Truncation to `m` entries is reduction modulo `2 ^ (w * m)`. -/
theorem pack_take (w m : ℕ) (l : List ℕ) (hl : ∀ x ∈ l, x < 2 ^ w) :
    (l.take m).foldr (fun a acc => a + 2 ^ w * acc) 0 =
      l.foldr (fun a acc => a + 2 ^ w * acc) 0 % 2 ^ (w * m) := by
  have hsplit := pack_append w (l.take m) (l.drop m)
  rw [List.take_append_drop] at hsplit
  have hlt := pack_lt w (l.take m) (fun x hx => hl x (List.mem_of_mem_take hx))
  rw [List.length_take] at hsplit hlt
  rcases le_total m l.length with hm | hm
  · rw [min_eq_left hm] at hsplit hlt
    rw [hsplit, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]
  · rw [min_eq_right hm] at hsplit hlt
    rw [List.take_of_length_le hm]
    have hfull := pack_lt w l hl
    refine (Nat.mod_eq_of_lt (lt_of_lt_of_le hfull ?_)).symm
    exact Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left _ hm)

/-! ### The packed q-table -/

section PackQ

variable (w N : ℕ) (hw : N < w) (t : ℕ → List ℕ) (h0 : t 0 = 1 :: List.replicate N 0)
  (hs : ∀ K, t (K + 1) = List.zipWith (· + ·) (t K) (List.replicate (K + 1) 0 ++ t K))
  (Q : ℕ → ℕ) (hQ0 : Q 0 = 1)
  (hQs : ∀ K, Q (K + 1) = Q K + (2 ^ (w * (K + 1)) * Q K) % 2 ^ (w * (N + 1)))
include h0 hs

theorem tbl_entry_le (K x : ℕ) (hx : x ∈ t K) : x ≤ 2 ^ K := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hx
  have hlen := tbl_length N t h0 hs K
  have h := tbl_getD N t h0 hs K i (by omega)
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some] at h
  rw [h]
  calc _ ≤ ((Finset.Icc 1 K).powerset).card := Finset.card_filter_le _ _
    _ = 2 ^ K := by rw [Finset.card_powerset, Nat.card_Icc]; congr 1

include hw hQ0 hQs in
theorem Q_eq_pack : ∀ K ≤ N, Q K = (t K).foldr (fun a acc => a + 2 ^ w * acc) 0 := by
  intro K hK
  induction K with
  | zero =>
    rw [hQ0, h0]
    simp only [List.foldr_cons, pack_replicate_zero]
    ring
  | succ K ih =>
    have hl := tbl_length N t h0 hs K
    have hbound : ∀ x ∈ List.replicate (K + 1) 0 ++ t K, x < 2 ^ w := by
      intro x hx
      rcases List.mem_append.1 hx with h | h
      · rw [List.eq_of_mem_replicate h]; exact Nat.two_pow_pos w
      · exact lt_of_le_of_lt (tbl_entry_le N t h0 hs K x h)
          (Nat.pow_lt_pow_right (by norm_num) (by omega))
    rw [hQs, ih (by omega), hs, List.zipWith_eq_zipWith_take_min]
    have hmin : min (t K).length (List.replicate (K + 1) 0 ++ t K).length = N + 1 := by
      simp [hl]
    rw [hmin, List.take_of_length_le (by omega),
      pack_add w _ _ (by simp [hl]), pack_take w (N + 1) _ hbound, pack_shift]

end PackQ

/-- `q(n)` is slot `n` of the packed q-table. -/
theorem strictPartitionCount_eq_packed (w N n : ℕ) (hw : N < w) (hn : n ≤ N) :
    strictPartitionCount n = ((Nat.rec (motive := fun _ => ℕ) 1
      (fun K B => B + (2 ^ (w * (K + 1)) * B) % 2 ^ (w * (N + 1))) N) / 2 ^ (w * n)) % 2 ^ w := by
  have ht0 : (fun K => Nat.rec (motive := fun _ => List ℕ) (1 :: List.replicate N 0)
      (fun k l => List.zipWith (· + ·) l (List.replicate (k + 1) 0 ++ l)) K) 0 =
      1 :: List.replicate N 0 := rfl
  have hts : ∀ K, (fun K => Nat.rec (motive := fun _ => List ℕ) (1 :: List.replicate N 0)
      (fun k l => List.zipWith (· + ·) l (List.replicate (k + 1) 0 ++ l)) K) (K + 1) =
      List.zipWith (· + ·) ((fun K => Nat.rec (motive := fun _ => List ℕ) (1 :: List.replicate N 0)
        (fun k l => List.zipWith (· + ·) l (List.replicate (k + 1) 0 ++ l)) K) K)
        (List.replicate (K + 1) 0 ++ (fun K => Nat.rec (motive := fun _ => List ℕ)
          (1 :: List.replicate N 0)
          (fun k l => List.zipWith (· + ·) l (List.replicate (k + 1) 0 ++ l)) K) K) :=
    fun _ => rfl
  rw [Q_eq_pack w N hw _ ht0 hts (fun K => Nat.rec (motive := fun _ => ℕ) 1
      (fun K B => B + (2 ^ (w * (K + 1)) * B) % 2 ^ (w * (N + 1))) K) rfl (fun _ => rfl) N le_rfl,
    pack_digit w _ (fun x hx => lt_of_le_of_lt (tbl_entry_le N _ ht0 hts N x hx)
      (Nat.pow_lt_pow_right (by norm_num) hw)) n]
  exact strictPartitionCount_eq_rec N n hn


/-! ## Guard bits -/

theorem lt_of_testBit_false (x v : ℕ) (hx : x < 2 ^ (v + 1)) (hb : x.testBit v = false) :
    x < 2 ^ v := by
  rw [Nat.testBit_eq_decide_div_mod_eq] at hb
  have h2 : x / 2 ^ v < 2 := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos v)]
    rw [pow_succ] at hx; linarith
  have h0 : x / 2 ^ v = 0 := by
    have hne : x / 2 ^ v % 2 ≠ 1 := by simpa using hb
    generalize x / 2 ^ v = y at h2 hne ⊢
    omega
  exact (Nat.div_eq_zero_iff_lt (Nat.two_pow_pos v)).1 h0

theorem testBit_pack (w : ℕ) (l : List ℕ) (hl : ∀ x ∈ l, x < 2 ^ w) (i b : ℕ) (hb : b < w) :
    (l.foldr (fun a acc => a + 2 ^ w * acc) 0).testBit (w * i + b) = (l.getD i 0).testBit b := by
  rw [← pack_digit w l hl i, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, Nat.add_comm]
  simp [hb]

/-- The guard check: if no guard bit is set, every entry is below `2 ^ v`. -/
theorem entries_lt_of_guard (v : ℕ) (l : List ℕ) (hl : ∀ x ∈ l, x < 2 ^ (v + 1))
    (hG : (l.foldr (fun a acc => a + 2 ^ (v + 1) * acc) 0 &&&
      (List.replicate l.length (2 ^ v)).foldr (fun a acc => a + 2 ^ (v + 1) * acc) 0) = 0) :
    ∀ x ∈ l, x < 2 ^ v := by
  intro x hx
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hx
  apply lt_of_testBit_false _ v (hl _ hx)
  have hrep : ∀ y ∈ List.replicate l.length (2 ^ v), y < 2 ^ (v + 1) := by
    intro y hy; rw [List.eq_of_mem_replicate hy]
    exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  have h1 := congrArg (fun z => z.testBit ((v + 1) * i + v)) hG
  simp only [Nat.testBit_land, Nat.zero_testBit] at h1
  rw [testBit_pack _ l hl i v (by omega), testBit_pack _ _ hrep i v (by omega)] at h1
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some] at h1
  rw [List.getD_eq_getElem?_getD, List.getElem?_replicate, if_pos (by omega)] at h1
  simpa [Nat.testBit_two_pow_self] using h1

section Guard

variable (v N : ℕ) (hv : 1 ≤ v) (t : ℕ → List ℕ) (h0 : t 0 = 1 :: List.replicate N 0)
  (hs : ∀ K, t (K + 1) = List.zipWith (· + ·) (t K) (List.replicate (K + 1) 0 ++ t K))
  (Q : ℕ → ℕ) (hQ0 : Q 0 = 1)
  (hQs : ∀ K < N, Q (K + 1) = Q K + (2 ^ ((v + 1) * (K + 1)) * Q K) % 2 ^ ((v + 1) * (N + 1)))
  (hG : ∀ K < N, (Q (K + 1) &&& (List.replicate (N + 1) (2 ^ v)).foldr
    (fun a acc => a + 2 ^ (v + 1) * acc) 0) = 0)
include hv h0 hs hQ0 hQs hG

theorem Q_eq_pack_guard : ∀ K ≤ N, Q K = (t K).foldr (fun a acc => a + 2 ^ (v + 1) * acc) 0 ∧
    ∀ x ∈ t K, x < 2 ^ v := by
  intro K hK
  induction K with
  | zero =>
    refine ⟨?_, ?_⟩
    · rw [hQ0, h0]; simp only [List.foldr_cons, pack_replicate_zero]; ring
    · intro x hx
      rw [h0] at hx
      rcases List.mem_cons.1 hx with rfl | hx
      · exact Nat.one_lt_two_pow (by omega)
      · rw [List.eq_of_mem_replicate hx]; exact Nat.two_pow_pos v
  | succ K ih =>
    obtain ⟨hQK, hbK⟩ := ih (by omega)
    have hl := tbl_length N t h0 hs K
    have hsbound : ∀ x ∈ List.replicate (K + 1) 0 ++ t K, x < 2 ^ v := by
      intro x hx
      rcases List.mem_append.1 hx with h | h
      · rw [List.eq_of_mem_replicate h]; exact Nat.two_pow_pos v
      · exact hbK x h
    have hsw : ∀ x ∈ List.replicate (K + 1) 0 ++ t K, x < 2 ^ (v + 1) := fun x hx =>
      lt_trans (hsbound x hx) (Nat.pow_lt_pow_right (by norm_num) (by omega))
    -- the new row is exact
    have hpack : Q (K + 1) = (t (K + 1)).foldr (fun a acc => a + 2 ^ (v + 1) * acc) 0 := by
      rw [hQs K (by omega), hQK, hs, List.zipWith_eq_zipWith_take_min]
      have hmin : min (t K).length (List.replicate (K + 1) 0 ++ t K).length = N + 1 := by
        simp [hl]
      rw [hmin, List.take_of_length_le (by omega),
        pack_add _ _ _ (by simp [hl]), pack_take _ (N + 1) _ hsw, pack_shift]
    -- entries of the new row are below `2 ^ (v + 1)` (sums of two entries below `2 ^ v`)
    have hw1 : ∀ x ∈ t (K + 1), x < 2 ^ (v + 1) := by
      intro x hx
      rw [hs] at hx
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hx
      rw [List.getElem_zipWith]
      simp only [List.length_zipWith, List.length_append, List.length_replicate, hl] at hi
      have ha := hbK ((t K)[i]'(by omega)) (List.getElem_mem _)
      have hb := hsbound ((List.replicate (K + 1) 0 ++ t K)[i]'(by simp [hl]; omega))
        (List.getElem_mem _)
      rw [pow_succ]; omega
    refine ⟨hpack, ?_⟩
    -- the guard check gives entries below `2 ^ v`
    have hG' := hG K (by omega)
    rw [hpack, ← tbl_length N t h0 hs (K + 1)] at hG'
    exact entries_lt_of_guard v _ hw1 hG'

end Guard

/-- One pass: if a guarded recursion (a failed guard gives `0`, and `0` stays `0`) is not `0`
at `N`, then every step before `N` is the normal step, and every guard passed. -/
theorem guard_pass (N H : ℕ) (Q : ℕ → ℕ) (S : ℕ → ℕ → ℕ) (hS0 : ∀ K, S 0 K = 0)
    (hQs : ∀ K, Q (K + 1) = if (S (Q K) K &&& H) == 0 then S (Q K) K else 0)
    (hN : Q N ≠ 0) :
    ∀ K < N, Q (K + 1) = S (Q K) K ∧ (S (Q K) K &&& H) = 0 := by
  -- first: no value up to `N` is `0`
  have hne : ∀ j ≤ N, Q (N - j) ≠ 0 := by
    intro j hj
    induction j with
    | zero => simpa using hN
    | succ j ih =>
      intro h0
      apply ih (by omega)
      rw [show N - j = (N - (j + 1)) + 1 by omega, hQs, h0, hS0]
      simp
  intro K hK
  have hK1 : Q (K + 1) ≠ 0 := by
    have := hne (N - (K + 1)) (by omega); rwa [show N - (N - (K + 1)) = K + 1 by omega] at this
  rw [hQs] at hK1 ⊢
  by_cases hg : (S (Q K) K &&& H) == 0
  · rw [if_pos hg]; exact ⟨rfl, by simpa using hg⟩
  · rw [if_neg hg] at hK1; exact absurd rfl hK1


/-- `q(n)` is slot `n` of the one-pass guarded table (slot width `v + 1`), when the result
at `N` is not `0`, i.e. every guard passed. -/
theorem strictPartitionCount_eq_guarded (v N n : ℕ) (hv : 1 ≤ v) (hn : n ≤ N)
    (hN : (Nat.rec (motive := fun _ => ℕ) 1 (fun K B => if ((B + (2 ^ ((v + 1) * (K + 1)) * B) % 2 ^ ((v + 1) * (N + 1))) &&& (List.replicate (N + 1) (2 ^ v)).foldr (fun a acc => a + 2 ^ (v + 1) * acc) 0) == 0 then B + (2 ^ ((v + 1) * (K + 1)) * B) % 2 ^ ((v + 1) * (N + 1)) else 0) N) ≠ 0) :
    strictPartitionCount n = ((Nat.rec (motive := fun _ => ℕ) 1 (fun K B => if ((B + (2 ^ ((v + 1) * (K + 1)) * B) % 2 ^ ((v + 1) * (N + 1))) &&& (List.replicate (N + 1) (2 ^ v)).foldr (fun a acc => a + 2 ^ (v + 1) * acc) 0) == 0 then B + (2 ^ ((v + 1) * (K + 1)) * B) % 2 ^ ((v + 1) * (N + 1)) else 0) N) / 2 ^ ((v + 1) * n)) % 2 ^ (v + 1) := by
  have ht0 : (fun K => Nat.rec (motive := fun _ => List ℕ) (1 :: List.replicate N 0) (fun k l => List.zipWith (· + ·) l (List.replicate (k + 1) 0 ++ l)) K) 0 = 1 :: List.replicate N 0 := rfl
  have hts : ∀ K, (fun K => Nat.rec (motive := fun _ => List ℕ) (1 :: List.replicate N 0) (fun k l => List.zipWith (· + ·) l (List.replicate (k + 1) 0 ++ l)) K) (K + 1) =
      List.zipWith (· + ·) ((fun K => Nat.rec (motive := fun _ => List ℕ) (1 :: List.replicate N 0) (fun k l => List.zipWith (· + ·) l (List.replicate (k + 1) 0 ++ l)) K) K)
        (List.replicate (K + 1) 0 ++ (fun K => Nat.rec (motive := fun _ => List ℕ) (1 :: List.replicate N 0) (fun k l => List.zipWith (· + ·) l (List.replicate (k + 1) 0 ++ l)) K) K) := fun _ => rfl
  have hpass := guard_pass N ((List.replicate (N + 1) (2 ^ v)).foldr
      (fun a acc => a + 2 ^ (v + 1) * acc) 0) (fun K => Nat.rec (motive := fun _ => ℕ) 1 (fun K B => if ((B + (2 ^ ((v + 1) * (K + 1)) * B) % 2 ^ ((v + 1) * (N + 1))) &&& (List.replicate (N + 1) (2 ^ v)).foldr (fun a acc => a + 2 ^ (v + 1) * acc) 0) == 0 then B + (2 ^ ((v + 1) * (K + 1)) * B) % 2 ^ ((v + 1) * (N + 1)) else 0) K)
    (fun B K => B + (2 ^ ((v + 1) * (K + 1)) * B) % 2 ^ ((v + 1) * (N + 1)))
    (fun K => by simp) (fun _ => rfl) hN
  obtain ⟨hQ, hb⟩ := Q_eq_pack_guard v N hv (fun K => Nat.rec (motive := fun _ => List ℕ) (1 :: List.replicate N 0) (fun k l => List.zipWith (· + ·) l (List.replicate (k + 1) 0 ++ l)) K) ht0 hts
    (fun K => Nat.rec (motive := fun _ => ℕ) 1 (fun K B => if ((B + (2 ^ ((v + 1) * (K + 1)) * B) % 2 ^ ((v + 1) * (N + 1))) &&& (List.replicate (N + 1) (2 ^ v)).foldr (fun a acc => a + 2 ^ (v + 1) * acc) 0) == 0 then B + (2 ^ ((v + 1) * (K + 1)) * B) % 2 ^ ((v + 1) * (N + 1)) else 0) K) rfl (fun K hK => (hpass K hK).1)
    (fun K hK => by rw [(hpass K hK).1]; exact (hpass K hK).2) N le_rfl
  rw [hQ, pack_digit (v + 1) _ (fun x hx => lt_trans (hb x hx)
    (Nat.pow_lt_pow_right (by norm_num) (by omega))) n]
  exact strictPartitionCount_eq_rec N n hn

/-! ### The packed p-table -/
/-! ## H1 beyond one million: a greedy chain, checked by the kernel -/

section Chain

variable (L N : ℕ) (isQ : ℕ → Prop) (d : ℕ → ℕ) (hd : ∀ m, 0 < m → m ≤ N → isQ (d m))

include hd in
/-- The invariant of the chain: a duplicate-free antichain of q-values whose subset sums
cover `[L, U]`. -/
theorem chain_step (l : List ℕ) (U m : ℕ)
    (hnd : l.Nodup) (hq : ∀ x ∈ l, isQ x) (han : ∀ x ∈ l, ∀ y ∈ l, x ≠ y → ¬ x ∣ y)
    (hcov : ∀ n, L ≤ n → n ≤ U → ∃ T ⊆ l.toFinset, (∑ x ∈ T, x) = n)
    (hc : (decide (0 < m) && decide (m ≤ N) && decide (d m ≤ U + 1 - L) &&
      l.all (fun s => d m % s != 0 && s % d m != 0)) = true) :
    (d m :: l).Nodup ∧ (∀ x ∈ d m :: l, isQ x) ∧
      (∀ x ∈ d m :: l, ∀ y ∈ d m :: l, x ≠ y → ¬ x ∣ y) ∧
      (∀ n, L ≤ n → n ≤ U + d m → ∃ T ⊆ (d m :: l).toFinset, (∑ x ∈ T, x) = n) := by
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, bne_iff_ne, ne_eq] at hc
  obtain ⟨⟨⟨hm0, hmN⟩, hle⟩, hall⟩ := hc
  have hnot : d m ∉ l := by
    intro h
    exact (hall _ h).1 (Nat.mod_self _)
  refine ⟨List.nodup_cons.2 ⟨hnot, hnd⟩, ?_, ?_, ?_⟩
  · intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact hd m hm0 hmN
    · exact hq x hx
  · intro x hx y hy hxy hdvd
    rcases List.mem_cons.1 hx with rfl | hx <;> rcases List.mem_cons.1 hy with rfl | hy
    · exact hxy rfl
    · exact (hall y hy).2 (Nat.mod_eq_zero_of_dvd hdvd)
    · exact (hall x hx).1 (Nat.mod_eq_zero_of_dvd hdvd)
    · exact han x hx y hy hxy hdvd
  · rw [List.toFinset_cons]
    exact extend_cover _ _ L U (fun h => hnot (List.mem_toFinset.1 h)) hcov hle

/-- Once the flag is `false`, the fold keeps it `false`. -/
theorem chain_flag (ms : List ℕ) : ∀ (st : List ℕ × ℕ × Bool),
    (ms.foldl (fun st m => (d m :: st.1, st.2.1 + d m, st.2.2 &&
      (decide (0 < m) && decide (m ≤ N) && decide (d m ≤ st.2.1 + 1 - L) &&
        st.1.all (fun s => d m % s != 0 && s % d m != 0)))) st).2.2 = true → st.2.2 = true := by
  induction ms with
  | nil => intro st h; exact h
  | cons m ms ih =>
    intro st h
    have := ih _ h
    simp only [Bool.and_eq_true] at this
    exact this.1

include hd in
/-- The whole chain, checked by one Boolean fold, keeps the invariant. -/
theorem chain_inv (ms : List ℕ) : ∀ (st : List ℕ × ℕ × Bool),
    st.1.Nodup → (∀ x ∈ st.1, isQ x) → (∀ x ∈ st.1, ∀ y ∈ st.1, x ≠ y → ¬ x ∣ y) →
    (∀ n, L ≤ n → n ≤ st.2.1 → ∃ T ⊆ st.1.toFinset, (∑ x ∈ T, x) = n) →
    (ms.foldl (fun st m => (d m :: st.1, st.2.1 + d m, st.2.2 &&
      (decide (0 < m) && decide (m ≤ N) && decide (d m ≤ st.2.1 + 1 - L) &&
        st.1.all (fun s => d m % s != 0 && s % d m != 0)))) st).2.2 = true →
    let fin := ms.foldl (fun st m => (d m :: st.1, st.2.1 + d m, st.2.2 &&
      (decide (0 < m) && decide (m ≤ N) && decide (d m ≤ st.2.1 + 1 - L) &&
        st.1.all (fun s => d m % s != 0 && s % d m != 0)))) st
    (∀ x ∈ fin.1, isQ x) ∧ (∀ x ∈ fin.1, ∀ y ∈ fin.1, x ≠ y → ¬ x ∣ y) ∧
      (∀ n, L ≤ n → n ≤ fin.2.1 → ∃ T ⊆ fin.1.toFinset, (∑ x ∈ T, x) = n) := by
  induction ms with
  | nil => intro st _ hq han hcov _; exact ⟨hq, han, hcov⟩
  | cons m ms ih =>
    intro st hnd hq han hcov hok
    have hstep := chain_flag L N d ms _ hok
    simp only [Bool.and_eq_true] at hstep
    obtain ⟨hnd', hq', han', hcov'⟩ := chain_step L N isQ d hd st.1 st.2.1 m hnd hq han hcov
      (by simpa only [Bool.and_eq_true] using hstep.2)
    exact ih _ hnd' hq' han' hcov' hok

end Chain



set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The base state for the reduction to `P(X0)`: the seed antichain (subset sums cover
`[237, 997436]`) and 741 further values `q(m)`, `96 ≤ m ≤ 2000` (`chain_inv`), give an
antichain of q-values `≥ 18` whose subset sums cover `[237, U]` with `U ≥ 1900360634358457428632022870866610`, and every kept
value is at most `U / 2`. The values come from the one-pass guarded q-table with 111-bit
slots (`strictPartitionCount_eq_guarded`). -/
theorem base_state : ∃ (l : List ℕ) (U : ℕ), 1900360634358457428632022870866610 ≤ U ∧
    (∀ x ∈ l, ∃ m : ℕ, 0 < m ∧ x = strictPartitionCount m) ∧ (∀ x ∈ l, 18 ≤ x) ∧
    (∀ x ∈ l, 2 * x ≤ U) ∧ (∀ x ∈ l, ∀ y ∈ l, x ≠ y → ¬ x ∣ y) ∧
    (∀ n, 237 ≤ n → n ≤ U → ∃ T ⊆ l.toFinset, (∑ x ∈ T, x) = n) := by
  have hnd : ([18, 22, 27, 32, 38, 46, 89, 104, 122, 142, 165, 222, 296, 340, 390, 585, 668, 982, 1113, 1816, 2590, 2910, 3658, 4097, 4582, 5718, 6378, 7108, 7917, 8808, 12076, 13394, 16444, 20132, 27130, 29927, 48446, 58499, 64234, 84756, 101698, 111322, 159046, 189586] : List ℕ).Nodup := by decide +kernel
  have hq : ∀ x ∈ ([18, 22, 27, 32, 38, 46, 89, 104, 122, 142, 165, 222, 296, 340, 390, 585, 668, 982, 1113, 1816, 2590, 2910, 3658, 4097, 4582, 5718, 6378, 7108, 7917, 8808, 12076, 13394, 16444, 20132, 27130, 29927, 48446, 58499, 64234, 84756, 101698, 111322, 159046, 189586] : List ℕ), x ∈ (Nat.rec (motive := fun _ => List ℕ)
      (1 :: List.replicate 90 0)
      (fun k l => List.zipWith (· + ·) l (List.replicate (k + 1) 0 ++ l)) 90).drop 1 := by
    decide +kernel
  have han : ∀ x ∈ ([18, 22, 27, 32, 38, 46, 89, 104, 122, 142, 165, 222, 296, 340, 390, 585, 668, 982, 1113, 1816, 2590, 2910, 3658, 4097, 4582, 5718, 6378, 7108, 7917, 8808, 12076, 13394, 16444, 20132, 27130, 29927, 48446, 58499, 64234, 84756, 101698, 111322, 159046, 189586] : List ℕ), ∀ y ∈ ([18, 22, 27, 32, 38, 46, 89, 104, 122, 142, 165, 222, 296, 340, 390, 585, 668, 982, 1113, 1816, 2590, 2910, 3658, 4097, 4582, 5718, 6378, 7108, 7917, 8808, 12076, 13394, 16444, 20132, 27130, 29927, 48446, 58499, 64234, 84756, 101698, 111322, 159046, 189586] : List ℕ), x ≠ y → y % x ≠ 0 := by
    decide +kernel
  have hmask : ((([18, 22, 27, 32, 38, 46, 89, 104, 122, 142, 165, 222, 296, 340, 390, 585, 668, 982, 1113, 1816, 2590, 2910, 3658, 4097, 4582, 5718, 6378, 7108, 7917, 8808, 12076, 13394, 16444, 20132, 27130, 29927, 48446, 58499, 64234, 84756, 101698, 111322, 159046, 189586] : List ℕ).foldr (fun a b => b ||| b <<< a) 1) >>> 237) % 2 ^ 997200 =
      2 ^ 997200 - 1 := by decide +kernel
  have hguard : (Nat.rec (motive := fun _ => ℕ) 1 (fun K B => if ((B + (2 ^ ((110 + 1) * (K + 1)) * B) % 2 ^ ((110 + 1) * (2000 + 1))) &&& (List.replicate (2000 + 1) (2 ^ 110)).foldr (fun a acc => a + 2 ^ (110 + 1) * acc) 0) == 0 then B + (2 ^ ((110 + 1) * (K + 1)) * B) % 2 ^ ((110 + 1) * (2000 + 1)) else 0) 2000) ≠ 0 := by decide +kernel
  obtain ⟨d, hdef⟩ : ∃ d : ℕ → ℕ, d = fun m => ((Nat.rec (motive := fun _ => ℕ) 1 (fun K B => if ((B + (2 ^ ((110 + 1) * (K + 1)) * B) % 2 ^ ((110 + 1) * (2000 + 1))) &&& (List.replicate (2000 + 1) (2 ^ 110)).foldr (fun a acc => a + 2 ^ (110 + 1) * acc) 0) == 0 then B + (2 ^ ((110 + 1) * (K + 1)) * B) % 2 ^ ((110 + 1) * (2000 + 1)) else 0) 2000) / 2 ^ ((110 + 1) * m)) % 2 ^ (110 + 1) := ⟨_, rfl⟩
  have hd : ∀ m, 0 < m → m ≤ 2000 →
      (fun x => ∃ m : ℕ, 0 < m ∧ x = strictPartitionCount m) (d m) := by
    intro m h0 hm
    subst hdef
    exact ⟨m, h0, (strictPartitionCount_eq_guarded 110 2000 m (by norm_num) hm hguard).symm⟩
  have hchk : (([96, 99, 100, 101, 102, 106, 108, 112, 113, 116, 117, 118, 123, 127, 130, 132, 133, 134, 136, 140, 141, 142, 143, 144, 145, 146, 147, 149, 151, 154, 155, 157, 161, 162, 166, 171, 172, 173, 174, 175, 176, 177, 179, 187, 188, 190, 194, 196, 198, 207, 208, 210, 212, 213, 217, 221, 222, 230, 232, 235, 237, 238, 240, 244, 245, 246, 247, 248, 251, 256, 257, 259, 260, 266, 270, 272, 274, 276, 282, 285, 286, 287, 288, 289, 290, 295, 296, 299, 301, 303, 304, 307, 308, 309, 310, 311, 315, 317, 320, 326, 329, 330, 333, 334, 337, 340, 341, 342, 345, 347, 348, 350, 351, 354, 356, 361, 363, 364, 368, 372, 373, 375, 376, 380, 382, 383, 387, 389, 391, 392, 394, 396, 400, 406, 407, 408, 409, 415, 417, 422, 424, 425, 426, 428, 429, 430, 432, 435, 438, 441, 442, 443, 446, 447, 463, 465, 466, 472, 473, 474, 476, 477, 479, 481, 483, 487, 489, 491, 492, 493, 495, 496, 497, 498, 502, 503, 504, 510, 512, 513, 519, 520, 523, 524, 525, 526, 529, 530, 532, 534, 535, 543, 546, 548, 549, 551, 554, 557, 559, 561, 563, 568, 569, 572, 583, 586, 587, 590, 591, 594, 596, 598, 601, 606, 608, 610, 613, 614, 615, 625, 626, 627, 628, 629, 630, 635, 638, 639, 640, 647, 650, 651, 653, 660, 662, 663, 664, 669, 671, 672, 673, 677, 678, 682, 683, 684, 694, 695, 697, 701, 705, 706, 710, 711, 715, 717, 719, 721, 728, 729, 730, 731, 732, 736, 737, 740, 741, 744, 745, 747, 751, 754, 755, 757, 762, 766, 768, 771, 773, 776, 779, 783, 784, 788, 789, 791, 792, 793, 796, 799, 801, 802, 805, 807, 809, 810, 812, 814, 817, 823, 825, 829, 833, 835, 837, 838, 840, 843, 847, 852, 855, 858, 860, 866, 867, 876, 877, 879, 880, 881, 882, 883, 884, 888, 895, 897, 898, 899, 900, 902, 906, 914, 915, 922, 925, 926, 932, 933, 934, 935, 936, 939, 941, 950, 952, 959, 960, 963, 966, 967, 968, 970, 973, 974, 975, 976, 979, 986, 987, 989, 990, 992, 993, 994, 997, 999, 1000, 1001, 1002, 1005, 1007, 1014, 1016, 1018, 1020, 1024, 1025, 1026, 1027, 1031, 1033, 1036, 1038, 1044, 1048, 1051, 1052, 1053, 1059, 1065, 1068, 1069, 1071, 1074, 1076, 1078, 1080, 1081, 1082, 1084, 1085, 1087, 1088, 1090, 1091, 1092, 1094, 1098, 1106, 1107, 1110, 1113, 1114, 1122, 1123, 1135, 1139, 1141, 1144, 1145, 1147, 1150, 1153, 1154, 1158, 1159, 1162, 1163, 1165, 1168, 1169, 1176, 1178, 1179, 1180, 1181, 1183, 1186, 1187, 1188, 1189, 1191, 1194, 1199, 1201, 1205, 1208, 1209, 1211, 1213, 1214, 1215, 1217, 1221, 1225, 1227, 1228, 1232, 1233, 1234, 1235, 1244, 1246, 1247, 1249, 1254, 1256, 1257, 1260, 1262, 1263, 1265, 1271, 1273, 1274, 1276, 1277, 1279, 1282, 1284, 1285, 1286, 1289, 1290, 1291, 1293, 1295, 1297, 1298, 1305, 1306, 1312, 1316, 1317, 1318, 1319, 1322, 1327, 1328, 1331, 1332, 1334, 1335, 1339, 1340, 1342, 1343, 1344, 1349, 1350, 1351, 1353, 1354, 1357, 1362, 1363, 1365, 1374, 1376, 1377, 1378, 1388, 1394, 1396, 1397, 1401, 1403, 1404, 1405, 1407, 1412, 1414, 1418, 1420, 1426, 1427, 1428, 1429, 1431, 1432, 1434, 1438, 1439, 1447, 1451, 1452, 1454, 1456, 1457, 1458, 1459, 1461, 1462, 1469, 1473, 1475, 1477, 1482, 1483, 1484, 1492, 1495, 1499, 1503, 1504, 1506, 1507, 1510, 1511, 1518, 1519, 1520, 1522, 1524, 1528, 1529, 1530, 1531, 1533, 1536, 1538, 1543, 1544, 1548, 1552, 1555, 1560, 1565, 1566, 1568, 1569, 1570, 1572, 1577, 1578, 1583, 1584, 1588, 1595, 1597, 1598, 1601, 1602, 1605, 1608, 1609, 1613, 1614, 1616, 1617, 1629, 1631, 1634, 1638, 1641, 1642, 1650, 1651, 1652, 1653, 1656, 1659, 1660, 1672, 1673, 1674, 1681, 1682, 1683, 1691, 1692, 1702, 1703, 1704, 1709, 1714, 1715, 1716, 1717, 1718, 1730, 1733, 1734, 1735, 1739, 1742, 1746, 1748, 1751, 1752, 1753, 1755, 1756, 1758, 1760, 1764, 1766, 1768, 1771, 1773, 1774, 1777, 1779, 1783, 1785, 1786, 1790, 1791, 1799, 1800, 1807, 1808, 1810, 1811, 1813, 1815, 1817, 1819, 1820, 1821, 1823, 1824, 1825, 1826, 1828, 1829, 1832, 1834, 1845, 1846, 1847, 1850, 1851, 1854, 1855, 1857, 1859, 1866, 1867, 1869, 1880, 1884, 1887, 1889, 1891, 1898, 1904, 1910, 1911, 1913, 1921, 1923, 1926, 1927, 1928, 1937, 1938, 1940, 1942, 1945, 1946, 1951, 1955, 1960, 1961, 1962, 1964, 1965, 1966, 1968, 1971, 1973, 1976, 1978, 1980, 1982, 1986, 1987, 1988, 1992, 1999] : List ℕ).foldl (fun st m => (d m :: st.1, st.2.1 + d m, st.2.2 && (decide (0 < m) && decide (m ≤ 2000) && decide (d m ≤ st.2.1 + 1 - 237) && st.1.all (fun s => d m % s != 0 && s % d m != 0)))) (([18, 22, 27, 32, 38, 46, 89, 104, 122, 142, 165, 222, 296, 340, 390, 585, 668, 982, 1113, 1816, 2590, 2910, 3658, 4097, 4582, 5718, 6378, 7108, 7917, 8808, 12076, 13394, 16444, 20132, 27130, 29927, 48446, 58499, 64234, 84756, 101698, 111322, 159046, 189586] : List ℕ), 997436, true)).2.2 = true ∧ 1900360634358457428632022870866610 ≤ (([96, 99, 100, 101, 102, 106, 108, 112, 113, 116, 117, 118, 123, 127, 130, 132, 133, 134, 136, 140, 141, 142, 143, 144, 145, 146, 147, 149, 151, 154, 155, 157, 161, 162, 166, 171, 172, 173, 174, 175, 176, 177, 179, 187, 188, 190, 194, 196, 198, 207, 208, 210, 212, 213, 217, 221, 222, 230, 232, 235, 237, 238, 240, 244, 245, 246, 247, 248, 251, 256, 257, 259, 260, 266, 270, 272, 274, 276, 282, 285, 286, 287, 288, 289, 290, 295, 296, 299, 301, 303, 304, 307, 308, 309, 310, 311, 315, 317, 320, 326, 329, 330, 333, 334, 337, 340, 341, 342, 345, 347, 348, 350, 351, 354, 356, 361, 363, 364, 368, 372, 373, 375, 376, 380, 382, 383, 387, 389, 391, 392, 394, 396, 400, 406, 407, 408, 409, 415, 417, 422, 424, 425, 426, 428, 429, 430, 432, 435, 438, 441, 442, 443, 446, 447, 463, 465, 466, 472, 473, 474, 476, 477, 479, 481, 483, 487, 489, 491, 492, 493, 495, 496, 497, 498, 502, 503, 504, 510, 512, 513, 519, 520, 523, 524, 525, 526, 529, 530, 532, 534, 535, 543, 546, 548, 549, 551, 554, 557, 559, 561, 563, 568, 569, 572, 583, 586, 587, 590, 591, 594, 596, 598, 601, 606, 608, 610, 613, 614, 615, 625, 626, 627, 628, 629, 630, 635, 638, 639, 640, 647, 650, 651, 653, 660, 662, 663, 664, 669, 671, 672, 673, 677, 678, 682, 683, 684, 694, 695, 697, 701, 705, 706, 710, 711, 715, 717, 719, 721, 728, 729, 730, 731, 732, 736, 737, 740, 741, 744, 745, 747, 751, 754, 755, 757, 762, 766, 768, 771, 773, 776, 779, 783, 784, 788, 789, 791, 792, 793, 796, 799, 801, 802, 805, 807, 809, 810, 812, 814, 817, 823, 825, 829, 833, 835, 837, 838, 840, 843, 847, 852, 855, 858, 860, 866, 867, 876, 877, 879, 880, 881, 882, 883, 884, 888, 895, 897, 898, 899, 900, 902, 906, 914, 915, 922, 925, 926, 932, 933, 934, 935, 936, 939, 941, 950, 952, 959, 960, 963, 966, 967, 968, 970, 973, 974, 975, 976, 979, 986, 987, 989, 990, 992, 993, 994, 997, 999, 1000, 1001, 1002, 1005, 1007, 1014, 1016, 1018, 1020, 1024, 1025, 1026, 1027, 1031, 1033, 1036, 1038, 1044, 1048, 1051, 1052, 1053, 1059, 1065, 1068, 1069, 1071, 1074, 1076, 1078, 1080, 1081, 1082, 1084, 1085, 1087, 1088, 1090, 1091, 1092, 1094, 1098, 1106, 1107, 1110, 1113, 1114, 1122, 1123, 1135, 1139, 1141, 1144, 1145, 1147, 1150, 1153, 1154, 1158, 1159, 1162, 1163, 1165, 1168, 1169, 1176, 1178, 1179, 1180, 1181, 1183, 1186, 1187, 1188, 1189, 1191, 1194, 1199, 1201, 1205, 1208, 1209, 1211, 1213, 1214, 1215, 1217, 1221, 1225, 1227, 1228, 1232, 1233, 1234, 1235, 1244, 1246, 1247, 1249, 1254, 1256, 1257, 1260, 1262, 1263, 1265, 1271, 1273, 1274, 1276, 1277, 1279, 1282, 1284, 1285, 1286, 1289, 1290, 1291, 1293, 1295, 1297, 1298, 1305, 1306, 1312, 1316, 1317, 1318, 1319, 1322, 1327, 1328, 1331, 1332, 1334, 1335, 1339, 1340, 1342, 1343, 1344, 1349, 1350, 1351, 1353, 1354, 1357, 1362, 1363, 1365, 1374, 1376, 1377, 1378, 1388, 1394, 1396, 1397, 1401, 1403, 1404, 1405, 1407, 1412, 1414, 1418, 1420, 1426, 1427, 1428, 1429, 1431, 1432, 1434, 1438, 1439, 1447, 1451, 1452, 1454, 1456, 1457, 1458, 1459, 1461, 1462, 1469, 1473, 1475, 1477, 1482, 1483, 1484, 1492, 1495, 1499, 1503, 1504, 1506, 1507, 1510, 1511, 1518, 1519, 1520, 1522, 1524, 1528, 1529, 1530, 1531, 1533, 1536, 1538, 1543, 1544, 1548, 1552, 1555, 1560, 1565, 1566, 1568, 1569, 1570, 1572, 1577, 1578, 1583, 1584, 1588, 1595, 1597, 1598, 1601, 1602, 1605, 1608, 1609, 1613, 1614, 1616, 1617, 1629, 1631, 1634, 1638, 1641, 1642, 1650, 1651, 1652, 1653, 1656, 1659, 1660, 1672, 1673, 1674, 1681, 1682, 1683, 1691, 1692, 1702, 1703, 1704, 1709, 1714, 1715, 1716, 1717, 1718, 1730, 1733, 1734, 1735, 1739, 1742, 1746, 1748, 1751, 1752, 1753, 1755, 1756, 1758, 1760, 1764, 1766, 1768, 1771, 1773, 1774, 1777, 1779, 1783, 1785, 1786, 1790, 1791, 1799, 1800, 1807, 1808, 1810, 1811, 1813, 1815, 1817, 1819, 1820, 1821, 1823, 1824, 1825, 1826, 1828, 1829, 1832, 1834, 1845, 1846, 1847, 1850, 1851, 1854, 1855, 1857, 1859, 1866, 1867, 1869, 1880, 1884, 1887, 1889, 1891, 1898, 1904, 1910, 1911, 1913, 1921, 1923, 1926, 1927, 1928, 1937, 1938, 1940, 1942, 1945, 1946, 1951, 1955, 1960, 1961, 1962, 1964, 1965, 1966, 1968, 1971, 1973, 1976, 1978, 1980, 1982, 1986, 1987, 1988, 1992, 1999] : List ℕ).foldl (fun st m => (d m :: st.1, st.2.1 + d m, st.2.2 && (decide (0 < m) && decide (m ≤ 2000) && decide (d m ≤ st.2.1 + 1 - 237) && st.1.all (fun s => d m % s != 0 && s % d m != 0)))) (([18, 22, 27, 32, 38, 46, 89, 104, 122, 142, 165, 222, 296, 340, 390, 585, 668, 982, 1113, 1816, 2590, 2910, 3658, 4097, 4582, 5718, 6378, 7108, 7917, 8808, 12076, 13394, 16444, 20132, 27130, 29927, 48446, 58499, 64234, 84756, 101698, 111322, 159046, 189586] : List ℕ), 997436, true)).2.1 ∧
      (([96, 99, 100, 101, 102, 106, 108, 112, 113, 116, 117, 118, 123, 127, 130, 132, 133, 134, 136, 140, 141, 142, 143, 144, 145, 146, 147, 149, 151, 154, 155, 157, 161, 162, 166, 171, 172, 173, 174, 175, 176, 177, 179, 187, 188, 190, 194, 196, 198, 207, 208, 210, 212, 213, 217, 221, 222, 230, 232, 235, 237, 238, 240, 244, 245, 246, 247, 248, 251, 256, 257, 259, 260, 266, 270, 272, 274, 276, 282, 285, 286, 287, 288, 289, 290, 295, 296, 299, 301, 303, 304, 307, 308, 309, 310, 311, 315, 317, 320, 326, 329, 330, 333, 334, 337, 340, 341, 342, 345, 347, 348, 350, 351, 354, 356, 361, 363, 364, 368, 372, 373, 375, 376, 380, 382, 383, 387, 389, 391, 392, 394, 396, 400, 406, 407, 408, 409, 415, 417, 422, 424, 425, 426, 428, 429, 430, 432, 435, 438, 441, 442, 443, 446, 447, 463, 465, 466, 472, 473, 474, 476, 477, 479, 481, 483, 487, 489, 491, 492, 493, 495, 496, 497, 498, 502, 503, 504, 510, 512, 513, 519, 520, 523, 524, 525, 526, 529, 530, 532, 534, 535, 543, 546, 548, 549, 551, 554, 557, 559, 561, 563, 568, 569, 572, 583, 586, 587, 590, 591, 594, 596, 598, 601, 606, 608, 610, 613, 614, 615, 625, 626, 627, 628, 629, 630, 635, 638, 639, 640, 647, 650, 651, 653, 660, 662, 663, 664, 669, 671, 672, 673, 677, 678, 682, 683, 684, 694, 695, 697, 701, 705, 706, 710, 711, 715, 717, 719, 721, 728, 729, 730, 731, 732, 736, 737, 740, 741, 744, 745, 747, 751, 754, 755, 757, 762, 766, 768, 771, 773, 776, 779, 783, 784, 788, 789, 791, 792, 793, 796, 799, 801, 802, 805, 807, 809, 810, 812, 814, 817, 823, 825, 829, 833, 835, 837, 838, 840, 843, 847, 852, 855, 858, 860, 866, 867, 876, 877, 879, 880, 881, 882, 883, 884, 888, 895, 897, 898, 899, 900, 902, 906, 914, 915, 922, 925, 926, 932, 933, 934, 935, 936, 939, 941, 950, 952, 959, 960, 963, 966, 967, 968, 970, 973, 974, 975, 976, 979, 986, 987, 989, 990, 992, 993, 994, 997, 999, 1000, 1001, 1002, 1005, 1007, 1014, 1016, 1018, 1020, 1024, 1025, 1026, 1027, 1031, 1033, 1036, 1038, 1044, 1048, 1051, 1052, 1053, 1059, 1065, 1068, 1069, 1071, 1074, 1076, 1078, 1080, 1081, 1082, 1084, 1085, 1087, 1088, 1090, 1091, 1092, 1094, 1098, 1106, 1107, 1110, 1113, 1114, 1122, 1123, 1135, 1139, 1141, 1144, 1145, 1147, 1150, 1153, 1154, 1158, 1159, 1162, 1163, 1165, 1168, 1169, 1176, 1178, 1179, 1180, 1181, 1183, 1186, 1187, 1188, 1189, 1191, 1194, 1199, 1201, 1205, 1208, 1209, 1211, 1213, 1214, 1215, 1217, 1221, 1225, 1227, 1228, 1232, 1233, 1234, 1235, 1244, 1246, 1247, 1249, 1254, 1256, 1257, 1260, 1262, 1263, 1265, 1271, 1273, 1274, 1276, 1277, 1279, 1282, 1284, 1285, 1286, 1289, 1290, 1291, 1293, 1295, 1297, 1298, 1305, 1306, 1312, 1316, 1317, 1318, 1319, 1322, 1327, 1328, 1331, 1332, 1334, 1335, 1339, 1340, 1342, 1343, 1344, 1349, 1350, 1351, 1353, 1354, 1357, 1362, 1363, 1365, 1374, 1376, 1377, 1378, 1388, 1394, 1396, 1397, 1401, 1403, 1404, 1405, 1407, 1412, 1414, 1418, 1420, 1426, 1427, 1428, 1429, 1431, 1432, 1434, 1438, 1439, 1447, 1451, 1452, 1454, 1456, 1457, 1458, 1459, 1461, 1462, 1469, 1473, 1475, 1477, 1482, 1483, 1484, 1492, 1495, 1499, 1503, 1504, 1506, 1507, 1510, 1511, 1518, 1519, 1520, 1522, 1524, 1528, 1529, 1530, 1531, 1533, 1536, 1538, 1543, 1544, 1548, 1552, 1555, 1560, 1565, 1566, 1568, 1569, 1570, 1572, 1577, 1578, 1583, 1584, 1588, 1595, 1597, 1598, 1601, 1602, 1605, 1608, 1609, 1613, 1614, 1616, 1617, 1629, 1631, 1634, 1638, 1641, 1642, 1650, 1651, 1652, 1653, 1656, 1659, 1660, 1672, 1673, 1674, 1681, 1682, 1683, 1691, 1692, 1702, 1703, 1704, 1709, 1714, 1715, 1716, 1717, 1718, 1730, 1733, 1734, 1735, 1739, 1742, 1746, 1748, 1751, 1752, 1753, 1755, 1756, 1758, 1760, 1764, 1766, 1768, 1771, 1773, 1774, 1777, 1779, 1783, 1785, 1786, 1790, 1791, 1799, 1800, 1807, 1808, 1810, 1811, 1813, 1815, 1817, 1819, 1820, 1821, 1823, 1824, 1825, 1826, 1828, 1829, 1832, 1834, 1845, 1846, 1847, 1850, 1851, 1854, 1855, 1857, 1859, 1866, 1867, 1869, 1880, 1884, 1887, 1889, 1891, 1898, 1904, 1910, 1911, 1913, 1921, 1923, 1926, 1927, 1928, 1937, 1938, 1940, 1942, 1945, 1946, 1951, 1955, 1960, 1961, 1962, 1964, 1965, 1966, 1968, 1971, 1973, 1976, 1978, 1980, 1982, 1986, 1987, 1988, 1992, 1999] : List ℕ).foldl (fun st m => (d m :: st.1, st.2.1 + d m, st.2.2 && (decide (0 < m) && decide (m ≤ 2000) && decide (d m ≤ st.2.1 + 1 - 237) && st.1.all (fun s => d m % s != 0 && s % d m != 0)))) (([18, 22, 27, 32, 38, 46, 89, 104, 122, 142, 165, 222, 296, 340, 390, 585, 668, 982, 1113, 1816, 2590, 2910, 3658, 4097, 4582, 5718, 6378, 7108, 7917, 8808, 12076, 13394, 16444, 20132, 27130, 29927, 48446, 58499, 64234, 84756, 101698, 111322, 159046, 189586] : List ℕ), 997436, true)).1.all (fun s => decide (18 ≤ s) && decide (2 * s ≤ (([96, 99, 100, 101, 102, 106, 108, 112, 113, 116, 117, 118, 123, 127, 130, 132, 133, 134, 136, 140, 141, 142, 143, 144, 145, 146, 147, 149, 151, 154, 155, 157, 161, 162, 166, 171, 172, 173, 174, 175, 176, 177, 179, 187, 188, 190, 194, 196, 198, 207, 208, 210, 212, 213, 217, 221, 222, 230, 232, 235, 237, 238, 240, 244, 245, 246, 247, 248, 251, 256, 257, 259, 260, 266, 270, 272, 274, 276, 282, 285, 286, 287, 288, 289, 290, 295, 296, 299, 301, 303, 304, 307, 308, 309, 310, 311, 315, 317, 320, 326, 329, 330, 333, 334, 337, 340, 341, 342, 345, 347, 348, 350, 351, 354, 356, 361, 363, 364, 368, 372, 373, 375, 376, 380, 382, 383, 387, 389, 391, 392, 394, 396, 400, 406, 407, 408, 409, 415, 417, 422, 424, 425, 426, 428, 429, 430, 432, 435, 438, 441, 442, 443, 446, 447, 463, 465, 466, 472, 473, 474, 476, 477, 479, 481, 483, 487, 489, 491, 492, 493, 495, 496, 497, 498, 502, 503, 504, 510, 512, 513, 519, 520, 523, 524, 525, 526, 529, 530, 532, 534, 535, 543, 546, 548, 549, 551, 554, 557, 559, 561, 563, 568, 569, 572, 583, 586, 587, 590, 591, 594, 596, 598, 601, 606, 608, 610, 613, 614, 615, 625, 626, 627, 628, 629, 630, 635, 638, 639, 640, 647, 650, 651, 653, 660, 662, 663, 664, 669, 671, 672, 673, 677, 678, 682, 683, 684, 694, 695, 697, 701, 705, 706, 710, 711, 715, 717, 719, 721, 728, 729, 730, 731, 732, 736, 737, 740, 741, 744, 745, 747, 751, 754, 755, 757, 762, 766, 768, 771, 773, 776, 779, 783, 784, 788, 789, 791, 792, 793, 796, 799, 801, 802, 805, 807, 809, 810, 812, 814, 817, 823, 825, 829, 833, 835, 837, 838, 840, 843, 847, 852, 855, 858, 860, 866, 867, 876, 877, 879, 880, 881, 882, 883, 884, 888, 895, 897, 898, 899, 900, 902, 906, 914, 915, 922, 925, 926, 932, 933, 934, 935, 936, 939, 941, 950, 952, 959, 960, 963, 966, 967, 968, 970, 973, 974, 975, 976, 979, 986, 987, 989, 990, 992, 993, 994, 997, 999, 1000, 1001, 1002, 1005, 1007, 1014, 1016, 1018, 1020, 1024, 1025, 1026, 1027, 1031, 1033, 1036, 1038, 1044, 1048, 1051, 1052, 1053, 1059, 1065, 1068, 1069, 1071, 1074, 1076, 1078, 1080, 1081, 1082, 1084, 1085, 1087, 1088, 1090, 1091, 1092, 1094, 1098, 1106, 1107, 1110, 1113, 1114, 1122, 1123, 1135, 1139, 1141, 1144, 1145, 1147, 1150, 1153, 1154, 1158, 1159, 1162, 1163, 1165, 1168, 1169, 1176, 1178, 1179, 1180, 1181, 1183, 1186, 1187, 1188, 1189, 1191, 1194, 1199, 1201, 1205, 1208, 1209, 1211, 1213, 1214, 1215, 1217, 1221, 1225, 1227, 1228, 1232, 1233, 1234, 1235, 1244, 1246, 1247, 1249, 1254, 1256, 1257, 1260, 1262, 1263, 1265, 1271, 1273, 1274, 1276, 1277, 1279, 1282, 1284, 1285, 1286, 1289, 1290, 1291, 1293, 1295, 1297, 1298, 1305, 1306, 1312, 1316, 1317, 1318, 1319, 1322, 1327, 1328, 1331, 1332, 1334, 1335, 1339, 1340, 1342, 1343, 1344, 1349, 1350, 1351, 1353, 1354, 1357, 1362, 1363, 1365, 1374, 1376, 1377, 1378, 1388, 1394, 1396, 1397, 1401, 1403, 1404, 1405, 1407, 1412, 1414, 1418, 1420, 1426, 1427, 1428, 1429, 1431, 1432, 1434, 1438, 1439, 1447, 1451, 1452, 1454, 1456, 1457, 1458, 1459, 1461, 1462, 1469, 1473, 1475, 1477, 1482, 1483, 1484, 1492, 1495, 1499, 1503, 1504, 1506, 1507, 1510, 1511, 1518, 1519, 1520, 1522, 1524, 1528, 1529, 1530, 1531, 1533, 1536, 1538, 1543, 1544, 1548, 1552, 1555, 1560, 1565, 1566, 1568, 1569, 1570, 1572, 1577, 1578, 1583, 1584, 1588, 1595, 1597, 1598, 1601, 1602, 1605, 1608, 1609, 1613, 1614, 1616, 1617, 1629, 1631, 1634, 1638, 1641, 1642, 1650, 1651, 1652, 1653, 1656, 1659, 1660, 1672, 1673, 1674, 1681, 1682, 1683, 1691, 1692, 1702, 1703, 1704, 1709, 1714, 1715, 1716, 1717, 1718, 1730, 1733, 1734, 1735, 1739, 1742, 1746, 1748, 1751, 1752, 1753, 1755, 1756, 1758, 1760, 1764, 1766, 1768, 1771, 1773, 1774, 1777, 1779, 1783, 1785, 1786, 1790, 1791, 1799, 1800, 1807, 1808, 1810, 1811, 1813, 1815, 1817, 1819, 1820, 1821, 1823, 1824, 1825, 1826, 1828, 1829, 1832, 1834, 1845, 1846, 1847, 1850, 1851, 1854, 1855, 1857, 1859, 1866, 1867, 1869, 1880, 1884, 1887, 1889, 1891, 1898, 1904, 1910, 1911, 1913, 1921, 1923, 1926, 1927, 1928, 1937, 1938, 1940, 1942, 1945, 1946, 1951, 1955, 1960, 1961, 1962, 1964, 1965, 1966, 1968, 1971, 1973, 1976, 1978, 1980, 1982, 1986, 1987, 1988, 1992, 1999] : List ℕ).foldl (fun st m => (d m :: st.1, st.2.1 + d m, st.2.2 && (decide (0 < m) && decide (m ≤ 2000) && decide (d m ≤ st.2.1 + 1 - 237) && st.1.all (fun s => d m % s != 0 && s % d m != 0)))) (([18, 22, 27, 32, 38, 46, 89, 104, 122, 142, 165, 222, 296, 340, 390, 585, 668, 982, 1113, 1816, 2590, 2910, 3658, 4097, 4582, 5718, 6378, 7108, 7917, 8808, 12076, 13394, 16444, 20132, 27130, 29927, 48446, 58499, 64234, 84756, 101698, 111322, 159046, 189586] : List ℕ), 997436, true)).2.1)) = true := by
    subst hdef
    decide +kernel
  obtain ⟨hq', han', hcov'⟩ := chain_inv 237 2000
    (fun x => ∃ m : ℕ, 0 < m ∧ x = strictPartitionCount m) d hd ([96, 99, 100, 101, 102, 106, 108, 112, 113, 116, 117, 118, 123, 127, 130, 132, 133, 134, 136, 140, 141, 142, 143, 144, 145, 146, 147, 149, 151, 154, 155, 157, 161, 162, 166, 171, 172, 173, 174, 175, 176, 177, 179, 187, 188, 190, 194, 196, 198, 207, 208, 210, 212, 213, 217, 221, 222, 230, 232, 235, 237, 238, 240, 244, 245, 246, 247, 248, 251, 256, 257, 259, 260, 266, 270, 272, 274, 276, 282, 285, 286, 287, 288, 289, 290, 295, 296, 299, 301, 303, 304, 307, 308, 309, 310, 311, 315, 317, 320, 326, 329, 330, 333, 334, 337, 340, 341, 342, 345, 347, 348, 350, 351, 354, 356, 361, 363, 364, 368, 372, 373, 375, 376, 380, 382, 383, 387, 389, 391, 392, 394, 396, 400, 406, 407, 408, 409, 415, 417, 422, 424, 425, 426, 428, 429, 430, 432, 435, 438, 441, 442, 443, 446, 447, 463, 465, 466, 472, 473, 474, 476, 477, 479, 481, 483, 487, 489, 491, 492, 493, 495, 496, 497, 498, 502, 503, 504, 510, 512, 513, 519, 520, 523, 524, 525, 526, 529, 530, 532, 534, 535, 543, 546, 548, 549, 551, 554, 557, 559, 561, 563, 568, 569, 572, 583, 586, 587, 590, 591, 594, 596, 598, 601, 606, 608, 610, 613, 614, 615, 625, 626, 627, 628, 629, 630, 635, 638, 639, 640, 647, 650, 651, 653, 660, 662, 663, 664, 669, 671, 672, 673, 677, 678, 682, 683, 684, 694, 695, 697, 701, 705, 706, 710, 711, 715, 717, 719, 721, 728, 729, 730, 731, 732, 736, 737, 740, 741, 744, 745, 747, 751, 754, 755, 757, 762, 766, 768, 771, 773, 776, 779, 783, 784, 788, 789, 791, 792, 793, 796, 799, 801, 802, 805, 807, 809, 810, 812, 814, 817, 823, 825, 829, 833, 835, 837, 838, 840, 843, 847, 852, 855, 858, 860, 866, 867, 876, 877, 879, 880, 881, 882, 883, 884, 888, 895, 897, 898, 899, 900, 902, 906, 914, 915, 922, 925, 926, 932, 933, 934, 935, 936, 939, 941, 950, 952, 959, 960, 963, 966, 967, 968, 970, 973, 974, 975, 976, 979, 986, 987, 989, 990, 992, 993, 994, 997, 999, 1000, 1001, 1002, 1005, 1007, 1014, 1016, 1018, 1020, 1024, 1025, 1026, 1027, 1031, 1033, 1036, 1038, 1044, 1048, 1051, 1052, 1053, 1059, 1065, 1068, 1069, 1071, 1074, 1076, 1078, 1080, 1081, 1082, 1084, 1085, 1087, 1088, 1090, 1091, 1092, 1094, 1098, 1106, 1107, 1110, 1113, 1114, 1122, 1123, 1135, 1139, 1141, 1144, 1145, 1147, 1150, 1153, 1154, 1158, 1159, 1162, 1163, 1165, 1168, 1169, 1176, 1178, 1179, 1180, 1181, 1183, 1186, 1187, 1188, 1189, 1191, 1194, 1199, 1201, 1205, 1208, 1209, 1211, 1213, 1214, 1215, 1217, 1221, 1225, 1227, 1228, 1232, 1233, 1234, 1235, 1244, 1246, 1247, 1249, 1254, 1256, 1257, 1260, 1262, 1263, 1265, 1271, 1273, 1274, 1276, 1277, 1279, 1282, 1284, 1285, 1286, 1289, 1290, 1291, 1293, 1295, 1297, 1298, 1305, 1306, 1312, 1316, 1317, 1318, 1319, 1322, 1327, 1328, 1331, 1332, 1334, 1335, 1339, 1340, 1342, 1343, 1344, 1349, 1350, 1351, 1353, 1354, 1357, 1362, 1363, 1365, 1374, 1376, 1377, 1378, 1388, 1394, 1396, 1397, 1401, 1403, 1404, 1405, 1407, 1412, 1414, 1418, 1420, 1426, 1427, 1428, 1429, 1431, 1432, 1434, 1438, 1439, 1447, 1451, 1452, 1454, 1456, 1457, 1458, 1459, 1461, 1462, 1469, 1473, 1475, 1477, 1482, 1483, 1484, 1492, 1495, 1499, 1503, 1504, 1506, 1507, 1510, 1511, 1518, 1519, 1520, 1522, 1524, 1528, 1529, 1530, 1531, 1533, 1536, 1538, 1543, 1544, 1548, 1552, 1555, 1560, 1565, 1566, 1568, 1569, 1570, 1572, 1577, 1578, 1583, 1584, 1588, 1595, 1597, 1598, 1601, 1602, 1605, 1608, 1609, 1613, 1614, 1616, 1617, 1629, 1631, 1634, 1638, 1641, 1642, 1650, 1651, 1652, 1653, 1656, 1659, 1660, 1672, 1673, 1674, 1681, 1682, 1683, 1691, 1692, 1702, 1703, 1704, 1709, 1714, 1715, 1716, 1717, 1718, 1730, 1733, 1734, 1735, 1739, 1742, 1746, 1748, 1751, 1752, 1753, 1755, 1756, 1758, 1760, 1764, 1766, 1768, 1771, 1773, 1774, 1777, 1779, 1783, 1785, 1786, 1790, 1791, 1799, 1800, 1807, 1808, 1810, 1811, 1813, 1815, 1817, 1819, 1820, 1821, 1823, 1824, 1825, 1826, 1828, 1829, 1832, 1834, 1845, 1846, 1847, 1850, 1851, 1854, 1855, 1857, 1859, 1866, 1867, 1869, 1880, 1884, 1887, 1889, 1891, 1898, 1904, 1910, 1911, 1913, 1921, 1923, 1926, 1927, 1928, 1937, 1938, 1940, 1942, 1945, 1946, 1951, 1955, 1960, 1961, 1962, 1964, 1965, 1966, 1968, 1971, 1973, 1976, 1978, 1980, 1982, 1986, 1987, 1988, 1992, 1999] : List ℕ)
    (([18, 22, 27, 32, 38, 46, 89, 104, 122, 142, 165, 222, 296, 340, 390, 585, 668, 982, 1113, 1816, 2590, 2910, 3658, 4097, 4582, 5718, 6378, 7108, 7917, 8808, 12076, 13394, 16444, 20132, 27130, 29927, 48446, 58499, 64234, 84756, 101698, 111322, 159046, 189586] : List ℕ), 997436, true) hnd
    (fun x hx => mem_qList (N := 90) (hq x hx))
    (fun x hx y hy hxy hdvd => han x hx y hy hxy (Nat.mod_eq_zero_of_dvd hdvd))
    (fun n h1 h2 => (testBit_foldr _ hnd n).1 (testBit_of_mask _ _ _ hmask n h1
      (by have h2' : n ≤ 997436 := h2; omega)))
    hchk.1
  obtain ⟨_, hU, hall⟩ := hchk
  rw [List.all_eq_true] at hall
  refine ⟨_, _, hU, hq', fun x hx => ?_, fun x hx => ?_, han', hcov'⟩
  · have := hall x hx
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    exact this.1
  · have := hall x hx
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    exact this.2


/-! ## The H1 core as a statement about primitive q-values -/

/-- Values within a factor `2` of each other do not divide each other. -/
theorem not_dvd_of_lt_of_lt_two_mul {a b : ℕ} (hab : a < b) (hb : b < 2 * a) : ¬ a ∣ b := by
  rintro ⟨k, rfl⟩
  rcases k with _ | _ | k
  · omega
  · omega
  · nlinarith

/-- `q(n+1) ≤ 2 q(n)`, in the subset form `q(n) = #{s ⊆ {1..n} : ∑ s = n}`. -/
theorem subsetCount_succ_le_two_mul (n : ℕ) :
    ((Finset.Icc 1 (n + 1)).powerset.filter (fun s => ∑ x ∈ s, x = n + 1)).card ≤
      2 * ((Finset.Icc 1 n).powerset.filter (fun s => ∑ x ∈ s, x = n)).card := by
  set F1 := (Finset.Icc 1 (n + 1)).powerset.filter (fun s => ∑ x ∈ s, x = n + 1)
  set F0 := (Finset.Icc 1 n).powerset.filter (fun s => ∑ x ∈ s, x = n)
  have hmem1 : ∀ s, s ∈ F1 ↔ s ⊆ Finset.Icc 1 (n + 1) ∧ ∑ x ∈ s, x = n + 1 := by
    intro s; simp [F1]
  have hmem0 : ∀ s, s ∈ F0 ↔ s ⊆ Finset.Icc 1 n ∧ ∑ x ∈ s, x = n := by
    intro s; simp [F0]
  -- two distinct elements of a set with sum `n + 1` have sum at most `n + 1`
  have hpair : ∀ s : Finset ℕ, ∑ x ∈ s, x = n + 1 → ∀ a ∈ s, ∀ b ∈ s, a ≠ b → a + b ≤ n + 1 := by
    intro s hs a ha b hb hab
    have hsub : ({a, b} : Finset ℕ) ⊆ s := by
      intro x hx; simp at hx; rcases hx with rfl | rfl <;> assumption
    have := Finset.sum_le_sum_of_subset (f := fun x => x) hsub
    rw [Finset.sum_pair hab] at this
    omega
  rw [← Finset.card_filter_add_card_filter_not (s := F1) (fun s => 1 ∈ s), two_mul]
  apply add_le_add
  · -- part A: remove the part `1`
    refine Finset.card_le_card_of_injOn (fun s => s.erase 1) ?_ ?_
    · intro s hs
      simp only [Finset.coe_filter, Set.mem_setOf_eq] at hs
      obtain ⟨hsF, h1⟩ := hs
      obtain ⟨hsub, hsum⟩ := (hmem1 s).1 hsF
      rw [Finset.mem_coe, hmem0]
      refine ⟨?_, ?_⟩
      · intro x hx
        obtain ⟨hx1, hxs⟩ := Finset.mem_erase.1 hx
        have hxI := Finset.mem_Icc.1 (hsub hxs)
        have := hpair s hsum 1 h1 x hxs (Ne.symm hx1)
        exact Finset.mem_Icc.2 ⟨hxI.1, by omega⟩
      · show ∑ x ∈ s.erase 1, x = n
        have := Finset.sum_erase_add s (fun x => x) h1
        omega
    · intro s hs t ht hst
      simp only [Finset.coe_filter, Set.mem_setOf_eq] at hs ht
      rw [← Finset.insert_erase hs.2, ← Finset.insert_erase ht.2]
      exact congrArg (insert 1) hst
  · -- part B: make the smallest part one smaller
    refine Finset.card_le_card_of_injOn
      (fun s => if h : s.Nonempty then insert (s.min' h - 1) (s.erase (s.min' h)) else ∅) ?_ ?_
    · intro s hs
      simp only [Finset.coe_filter, Set.mem_setOf_eq] at hs
      obtain ⟨hsF, h1⟩ := hs
      obtain ⟨hsub, hsum⟩ := (hmem1 s).1 hsF
      have hne : s.Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]; rintro rfl; simp at hsum
      simp only [hne, dite_true]
      set m := s.min' hne with hm
      have hms : m ∈ s := Finset.min'_mem s hne
      have hmI := Finset.mem_Icc.1 (hsub hms)
      have hm2 : 2 ≤ m := by
        have : m ≠ 1 := fun h => h1 (h ▸ hms)
        omega
      have hmin : ∀ x ∈ s, m ≤ x := fun x hx => Finset.min'_le s x hx
      have hnot : m - 1 ∉ s.erase m := by
        intro h
        have := hmin _ (Finset.mem_of_mem_erase h)
        omega
      rw [Finset.mem_coe, hmem0]
      refine ⟨?_, ?_⟩
      · intro x hx
        rcases Finset.mem_insert.1 hx with rfl | hx
        · exact Finset.mem_Icc.2 ⟨by omega, by omega⟩
        · obtain ⟨hxm, hxs⟩ := Finset.mem_erase.1 hx
          have hxI := Finset.mem_Icc.1 (hsub hxs)
          have := hpair s hsum m hms x hxs (Ne.symm hxm)
          exact Finset.mem_Icc.2 ⟨hxI.1, by omega⟩
      · rw [Finset.sum_insert hnot]
        have := Finset.sum_erase_add s (fun x => x) hms
        omega
    · intro s hs t ht hst
      simp only [Finset.coe_filter, Set.mem_setOf_eq] at hs ht
      obtain ⟨hsF, hs1⟩ := hs
      obtain ⟨htF, ht1⟩ := ht
      obtain ⟨hssub, hssum⟩ := (hmem1 s).1 hsF
      obtain ⟨htsub, htsum⟩ := (hmem1 t).1 htF
      have hsne : s.Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]; rintro rfl; simp at hssum
      have htne : t.Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]; rintro rfl; simp at htsum
      simp only [hsne, htne, dite_true] at hst
      set a := s.min' hsne
      set b := t.min' htne
      have has : a ∈ s := Finset.min'_mem s hsne
      have hbt : b ∈ t := Finset.min'_mem t htne
      have ha2 : 2 ≤ a := by
        have : a ≠ 1 := fun h => hs1 (h ▸ has)
        have := (Finset.mem_Icc.1 (hssub has)).1; omega
      have hb2 : 2 ≤ b := by
        have : b ≠ 1 := fun h => ht1 (h ▸ hbt)
        have := (Finset.mem_Icc.1 (htsub hbt)).1; omega
      have hamin : ∀ x ∈ s, a ≤ x := fun x hx => Finset.min'_le s x hx
      have hbmin : ∀ x ∈ t, b ≤ x := fun x hx => Finset.min'_le t x hx
      -- the two new smallest parts agree
      have hab : a = b := by
        have h1 : a - 1 ∈ insert (b - 1) (t.erase b) := hst ▸ Finset.mem_insert_self _ _
        have h2 : b - 1 ∈ insert (a - 1) (s.erase a) := hst.symm ▸ Finset.mem_insert_self _ _
        rcases Finset.mem_insert.1 h1 with e1 | e1
        · omega
        · rcases Finset.mem_insert.1 h2 with e2 | e2
          · omega
          · have := hbmin _ (Finset.mem_of_mem_erase e1)
            have := hamin _ (Finset.mem_of_mem_erase e2)
            omega
      have hnots : a - 1 ∉ s.erase a := by
        intro h; have := hamin _ (Finset.mem_of_mem_erase h); omega
      have hnott : b - 1 ∉ t.erase b := by
        intro h; have := hbmin _ (Finset.mem_of_mem_erase h); omega
      have herase : s.erase a = t.erase b := by
        have := congrArg (fun u => u.erase (a - 1)) hst
        rw [Finset.erase_insert hnots, hab, Finset.erase_insert hnott] at this
        rw [hab]; exact this
      rw [← Finset.insert_erase has, ← Finset.insert_erase hbt, herase, hab]

/-- `q(n+1) ≤ 2 q(n)` for all `n`: every interval `[x, 2x]` with `x ≥ 1` contains a q-value. -/
theorem strictPartitionCount_succ_le_two_mul (n : ℕ) :
    strictPartitionCount (n + 1) ≤ 2 * strictPartitionCount n := by
  rw [strictPartitionCount_eq_subsetCount, strictPartitionCount_eq_subsetCount]
  exact subsetCount_succ_le_two_mul n

section Reduction

variable (isQ : ℕ → Prop) (X0 : ℕ)
  (hP : ∀ x, X0 ≤ x → ∃ a, isQ a ∧ x ≤ a ∧ 2 * a ≤ 3 * x ∧
    ∀ s, isQ s → 18 ≤ s → 2 * s ≤ a → ¬ s ∣ a)

include hP in
/-- One step of the reduction: from a state (an antichain of q-values `≥ 18`, all `≤ U / 2`,
whose subset sums cover `[237, U]`) with `U ≥ 1000`, a primitive value
`a ∈ [U/2 + 1, 3(U/2 + 1)/2]` gives the same kind of state for `a :: l` and `U + a`. -/
theorem inv_step (l : List ℕ) (U : ℕ) (hU : 1000 ≤ U) (hX : X0 ≤ U / 2 + 1)
    (hq : ∀ x ∈ l, isQ x) (h18 : ∀ x ∈ l, 18 ≤ x) (h2 : ∀ x ∈ l, 2 * x ≤ U)
    (han : ∀ x ∈ l, ∀ y ∈ l, x ≠ y → ¬ x ∣ y)
    (hcov : ∀ n, 237 ≤ n → n ≤ U → ∃ T ⊆ l.toFinset, (∑ x ∈ T, x) = n) :
    ∃ a, U + 1 ≤ U + a ∧ (∀ x ∈ a :: l, isQ x) ∧ (∀ x ∈ a :: l, 18 ≤ x) ∧
      (∀ x ∈ a :: l, 2 * x ≤ U + a) ∧ (∀ x ∈ a :: l, ∀ y ∈ a :: l, x ≠ y → ¬ x ∣ y) ∧
      (∀ n, 237 ≤ n → n ≤ U + a → ∃ T ⊆ (a :: l).toFinset, (∑ x ∈ T, x) = n) := by
  obtain ⟨a, haq, hxa, ha3, hprim⟩ := hP (U / 2 + 1) hX
  have hgt : ∀ s ∈ l, s < a := fun s hs => by have := h2 s hs; omega
  have hnot : a ∉ l := fun h => lt_irrefl a (hgt a h)
  refine ⟨a, by omega, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx; rcases List.mem_cons.1 hx with ex | hx'
    · rw [ex]; exact haq
    · exact hq x hx'
  · intro x hx; rcases List.mem_cons.1 hx with ex | hx'
    · rw [ex]; omega
    · exact h18 x hx'
  · intro x hx; rcases List.mem_cons.1 hx with ex | hx'
    · rw [ex]; omega
    · have := h2 x hx'; omega
  · have hsa : ∀ s ∈ l, ¬ s ∣ a := by
      intro s hs hd
      by_cases hc : 2 * s ≤ a
      · exact hprim s (hq s hs) (h18 s hs) hc hd
      · exact not_dvd_of_lt_of_lt_two_mul (hgt s hs) (by omega) hd
    have has : ∀ s ∈ l, ¬ a ∣ s := by
      intro s hs hd
      have := Nat.le_of_dvd (by have := h18 s hs; omega) hd
      have := hgt s hs; omega
    intro x hx y hy hxy
    rcases List.mem_cons.1 hx with ex | hx' <;> rcases List.mem_cons.1 hy with ey | hy'
    · exact absurd (ex.trans ey.symm) hxy
    · rw [ex]; exact has y hy'
    · rw [ey]; exact hsa x hx'
    · exact han x hx' y hy' hxy
  · rw [List.toFinset_cons]
    exact extend_cover _ a 237 U (fun h => hnot (List.mem_toFinset.1 h)) hcov (by omega)

include hP in
/-- `P(X0)` and a base state with `U0 ≥ 1000` and `X0 ≤ U0 / 2 + 1` give the representation
conjecture for every `n ≥ 237`. -/
theorem rep_of_P (l0 : List ℕ) (U0 : ℕ) (hU0 : 1000 ≤ U0) (hX : X0 ≤ U0 / 2 + 1)
    (hq : ∀ x ∈ l0, isQ x) (h18 : ∀ x ∈ l0, 18 ≤ x) (h2 : ∀ x ∈ l0, 2 * x ≤ U0)
    (han : ∀ x ∈ l0, ∀ y ∈ l0, x ≠ y → ¬ x ∣ y)
    (hcov : ∀ n, 237 ≤ n → n ≤ U0 → ∃ T ⊆ l0.toFinset, (∑ x ∈ T, x) = n)
    (n : ℕ) (hn : 237 ≤ n) :
    ∃ T : Finset ℕ, (∀ x ∈ T, isQ x) ∧ (∀ x ∈ T, ∀ y ∈ T, x ≠ y → ¬ x ∣ y) ∧
      (∑ x ∈ T, x) = n := by
  have hiter : ∀ k, ∃ (l : List ℕ) (U : ℕ), U0 + k ≤ U ∧ (∀ x ∈ l, isQ x) ∧
      (∀ x ∈ l, 18 ≤ x) ∧ (∀ x ∈ l, 2 * x ≤ U) ∧ (∀ x ∈ l, ∀ y ∈ l, x ≠ y → ¬ x ∣ y) ∧
      (∀ n, 237 ≤ n → n ≤ U → ∃ T ⊆ l.toFinset, (∑ x ∈ T, x) = n) := by
    intro k
    induction k with
    | zero => exact ⟨l0, U0, le_refl _, hq, h18, h2, han, hcov⟩
    | succ k ih =>
      obtain ⟨l, U, hk, hq1, h181, h21, han1, hcov1⟩ := ih
      obtain ⟨a, ha, rest⟩ := inv_step isQ X0 hP l U (by omega) (by omega) hq1 h181 h21 han1 hcov1
      exact ⟨a :: l, U + a, by omega, rest⟩
  obtain ⟨l, U, hk, hq1, _, _, han1, hcov1⟩ := hiter n
  obtain ⟨T, hT, hsum⟩ := hcov1 n hn (by omega)
  exact ⟨T, fun x hx => hq1 x (List.mem_toFinset.1 (hT hx)),
    fun x hx y hy => han1 x (List.mem_toFinset.1 (hT hx)) y (List.mem_toFinset.1 (hT hy)), hsum⟩

end Reduction

theorem partitionCount_le_two_pow (n : ℕ) : partitionCount n ≤ 2 ^ n := by
  unfold partitionCount
  calc Fintype.card (Nat.Partition n) ≤ Fintype.card (Composition n) :=
        Fintype.card_le_of_surjective _ Nat.Partition.ofComposition_surj
    _ = 2 ^ (n - 1) := composition_card n
    _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)

/-- Horner iteration: if `P ≡ A + X P`, then `P ≡ A (1 + X + ⋯ + X^j) + X^(j+1) P`. -/
theorem geo_iter (A P X M : ℕ) (G : ℕ → ℕ) (hG0 : G 0 = 1)
    (hGs : ∀ j, G (j + 1) = (1 + X * G j) % M) (h : P ≡ A + X * P [MOD M]) :
    ∀ j, P ≡ A * G j + X ^ (j + 1) * P [MOD M] := by
  intro j
  induction j with
  | zero => simpa [hG0] using h
  | succ j ih =>
    have step : P ≡ A + X * (A * G j + X ^ (j + 1) * P) [MOD M] :=
      h.trans (Nat.ModEq.add_left _ (Nat.ModEq.mul_left _ ih))
    refine step.trans ?_
    have e : A + X * (A * G j + X ^ (j + 1) * P) =
        A * (1 + X * G j) + X ^ (j + 1 + 1) * P := by ring
    rw [e, hGs]
    exact Nat.ModEq.add_right _ (Nat.ModEq.mul_left _ (Nat.mod_modEq _ _).symm)

section PackP

variable (w N : ℕ) (hw : N < w) (pr : ℕ → List ℕ)
  (hpr : ∀ K, pr K = Nat.rec (motive := fun _ => List ℕ) (1 :: List.replicate N 0)
    (fun k old => (Nat.rec (motive := fun _ => List ℕ) []
      (fun i r => (old.getD i 0 + if k + 1 ≤ i then r.getD k 0 else 0) :: r) (N + 1)).reverse) K)
include hpr

theorem pr_length (K : ℕ) : (pr K).length = N + 1 := by rw [hpr]; exact (prow_spec N K).1

theorem pr_getD (K i : ℕ) (hi : i ≤ N) : (pr K).getD i 0 =
    (Finset.univ.filter (fun p : i.Partition => ∀ j ∈ p.parts, j ≤ K)).card := by
  rw [hpr]; exact (prow_spec N K).2 i hi

include hw in
theorem pr_entry_lt (K x : ℕ) (hx : x ∈ pr K) : x < 2 ^ w := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hx
  have hlen := pr_length N pr hpr K
  have h := pr_getD N pr hpr K i (by omega)
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some] at h
  rw [h]
  calc _ ≤ (Finset.univ : Finset i.Partition).card := Finset.card_filter_le _ _
    _ = partitionCount i := by rw [Finset.card_univ]; rfl
    _ ≤ 2 ^ i := partitionCount_le_two_pow i
    _ < 2 ^ w := Nat.pow_lt_pow_right (by norm_num) (by omega)

/-- The list identity behind the packed step: `new = old + shift (K+1) new`, truncated. -/
theorem pr_succ_eq (K : ℕ) : pr (K + 1) =
    List.zipWith (· + ·) (pr K) ((List.replicate (K + 1) 0 ++ pr (K + 1)).take (N + 1)) := by
  apply List.ext_getElem
  · simp [pr_length N pr hpr]
  · intro i h1 h2
    have hi : i ≤ N := by rw [pr_length N pr hpr] at h1; omega
    have e1 := pr_getD N pr hpr (K + 1) i hi
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1, Option.getD_some] at e1
    rw [e1, List.getElem_zipWith, List.getElem_take, bounded_succ]
    have e0 := pr_getD N pr hpr K i hi
    rw [List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by rw [pr_length N pr hpr]; omega), Option.getD_some] at e0
    rw [e0]
    congr 1
    by_cases hk : K + 1 ≤ i
    · rw [if_pos hk, List.getElem_append_right (by simp; omega)]
      have e2 := pr_getD N pr hpr (K + 1) (i - (K + 1)) (by omega)
      rw [List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem (by rw [pr_length N pr hpr]; omega), Option.getD_some] at e2
      simp only [List.length_replicate]
      rw [e2]
    · rw [if_neg hk, List.getElem_append_left (by simp; omega)]
      simp

include hw in
theorem P_eq_pack (P : ℕ → ℕ) (hP0 : P 0 = 1)
    (hPs : ∀ K, P (K + 1) = (P K * Nat.rec (motive := fun _ => ℕ) 1
      (fun _ g => (1 + 2 ^ (w * (K + 1)) * g) % 2 ^ (w * (N + 1))) (N / (K + 1)))
        % 2 ^ (w * (N + 1))) :
    ∀ K, P K = (pr K).foldr (fun a acc => a + 2 ^ w * acc) 0 := by
  intro K
  induction K with
  | zero =>
    rw [hP0, hpr]
    show 1 = (1 :: List.replicate N 0).foldr (fun a acc => a + 2 ^ w * acc) 0
    simp only [List.foldr_cons, pack_replicate_zero]; ring
  | succ K ih =>
    set M := 2 ^ (w * (N + 1)) with hM
    set X := 2 ^ (w * (K + 1)) with hX
    set A := (pr K).foldr (fun a acc => a + 2 ^ w * acc) 0
    set Pk := (pr (K + 1)).foldr (fun a acc => a + 2 ^ w * acc) 0 with hPk
    have hbound : ∀ x ∈ List.replicate (K + 1) 0 ++ pr (K + 1), x < 2 ^ w := by
      intro x hx
      rcases List.mem_append.1 hx with h | h
      · rw [List.eq_of_mem_replicate h]; exact Nat.two_pow_pos w
      · exact pr_entry_lt w N hw pr hpr (K + 1) x h
    have hP : Pk = A + (X * Pk) % M := by
      rw [hPk]
      conv_lhs => rw [pr_succ_eq N pr hpr K]
      rw [pack_add w _ _ (by simp [pr_length N pr hpr]), pack_take w (N + 1) _ hbound,
        pack_shift]
    have hPlt : Pk < M := by
      have := pack_lt w (pr (K + 1)) (fun x hx => pr_entry_lt w N hw pr hpr (K + 1) x hx)
      rwa [pr_length N pr hpr] at this
    have hmod : Pk ≡ A + X * Pk [MOD M] := by
      conv_lhs => rw [hP]
      exact Nat.ModEq.add_left _ (Nat.mod_modEq _ _)
    have hit := geo_iter A Pk X M (fun j => Nat.rec (motive := fun _ => ℕ) 1
      (fun _ g => (1 + X * g) % M) j) rfl (fun _ => rfl) hmod (N / (K + 1))
    have hdvd : M ∣ X ^ (N / (K + 1) + 1) := by
      rw [hM, hX, ← pow_mul]
      apply Nat.pow_dvd_pow
      have : N + 1 ≤ (K + 1) * (N / (K + 1) + 1) := Nat.lt_mul_div_succ N (by omega)
      calc w * (N + 1) ≤ w * ((K + 1) * (N / (K + 1) + 1)) := Nat.mul_le_mul_left _ this
        _ = w * (K + 1) * (N / (K + 1) + 1) := by ring
    have hzero : X ^ (N / (K + 1) + 1) * Pk ≡ 0 [MOD M] :=
      (Nat.modEq_zero_iff_dvd.2 (Dvd.dvd.mul_right hdvd Pk))
    have hfin := hit.trans (Nat.ModEq.add_left _ hzero)
    rw [add_zero] at hfin
    rw [hPs, ih]
    exact Eq.trans (hfin.symm : _ % M = Pk % M) (Nat.mod_eq_of_lt hPlt)

end PackP

/-- `p(n)` is slot `n` of the packed p-table. -/
theorem partitionCount_eq_packed (w N n : ℕ) (hw : N < w) (hn : n ≤ N) :
    partitionCount n = ((Nat.rec (motive := fun _ => ℕ) 1
      (fun K B => (B * Nat.rec (motive := fun _ => ℕ) 1
        (fun _ g => (1 + 2 ^ (w * (K + 1)) * g) % 2 ^ (w * (N + 1))) (N / (K + 1)))
          % 2 ^ (w * (N + 1))) N) / 2 ^ (w * n)) % 2 ^ w := by
  have hpr : ∀ K, (fun K => Nat.rec (motive := fun _ => List ℕ) (1 :: List.replicate N 0)
      (fun k old => (Nat.rec (motive := fun _ => List ℕ) []
        (fun i r => (old.getD i 0 + if k + 1 ≤ i then r.getD k 0 else 0) :: r) (N + 1)).reverse)
      K) K = Nat.rec (motive := fun _ => List ℕ) (1 :: List.replicate N 0)
      (fun k old => (Nat.rec (motive := fun _ => List ℕ) []
        (fun i r => (old.getD i 0 + if k + 1 ≤ i then r.getD k 0 else 0) :: r) (N + 1)).reverse) K :=
    fun _ => rfl
  rw [P_eq_pack w N hw _ hpr (fun K => Nat.rec (motive := fun _ => ℕ) 1
      (fun K B => (B * Nat.rec (motive := fun _ => ℕ) 1
        (fun _ g => (1 + 2 ^ (w * (K + 1)) * g) % 2 ^ (w * (N + 1))) (N / (K + 1)))
          % 2 ^ (w * (N + 1))) K) rfl (fun _ => rfl) N,
    pack_digit w _ (fun x hx => pr_entry_lt w N hw _ hpr N x hx) n]
  exact partitionCount_eq_rec N n hn

/-! ## The finite range `8 ≤ n ≤ 1000`, checked by the kernel -/

/-- From the Boolean range check to the three claims, for each `8 ≤ n ≤ N`. -/
theorem nondiv_of_check (w N : ℕ) (hw : N < w)
    (h : (List.range (N + 1)).all (fun n => n ≤ 7 ||
      (((Nat.rec (motive := fun _ => ℕ) 1
        (fun K B => (B * Nat.rec (motive := fun _ => ℕ) 1
          (fun _ g => (1 + 2 ^ (w * (K + 1)) * g) % 2 ^ (w * (N + 1))) (N / (K + 1)))
            % 2 ^ (w * (N + 1))) N) / 2 ^ (w * n)) % 2 ^ w %
        (((Nat.rec (motive := fun _ => ℕ) 1
          (fun K B => B + (2 ^ (w * (K + 1)) * B) % 2 ^ (w * (N + 1))) N) / 2 ^ (w * n)) % 2 ^ w)
          != 0 &&
       ((((Nat.rec (motive := fun _ => ℕ) 1
        (fun K B => (B * Nat.rec (motive := fun _ => ℕ) 1
          (fun _ g => (1 + 2 ^ (w * (K + 1)) * g) % 2 ^ (w * (N + 1))) (N / (K + 1)))
            % 2 ^ (w * (N + 1))) N) / 2 ^ (w * n)) % 2 ^ w) - 1) %
        (((Nat.rec (motive := fun _ => ℕ) 1
          (fun K B => B + (2 ^ (w * (K + 1)) * B) % 2 ^ (w * (N + 1))) N) / 2 ^ (w * n)) % 2 ^ w)
          != 0 &&
       ((((Nat.rec (motive := fun _ => ℕ) 1
        (fun K B => (B * Nat.rec (motive := fun _ => ℕ) 1
          (fun _ g => (1 + 2 ^ (w * (K + 1)) * g) % 2 ^ (w * (N + 1))) (N / (K + 1)))
            % 2 ^ (w * (N + 1))) N) / 2 ^ (w * n)) % 2 ^ w) + 1) %
        (((Nat.rec (motive := fun _ => ℕ) 1
          (fun K B => B + (2 ^ (w * (K + 1)) * B) % 2 ^ (w * (N + 1))) N) / 2 ^ (w * n)) % 2 ^ w)
          != 0)) = true)
    (n : ℕ) (h7 : 7 < n) (hn : n ≤ N) :
    ¬ strictPartitionCount n ∣ partitionCount n ∧
    ¬ strictPartitionCount n ∣ partitionCount n - 1 ∧
    ¬ strictPartitionCount n ∣ partitionCount n + 1 := by
  rw [List.all_eq_true] at h
  have hb := h n (List.mem_range.2 (by omega))
  rw [← strictPartitionCount_eq_packed w N n hw hn, ← partitionCount_eq_packed w N n hw hn] at hb
  simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, bne_iff_ne, ne_eq] at hb
  rcases hb with hb | hb
  · omega
  · simp only [Nat.dvd_iff_mod_eq_zero]
    exact ⟨hb.1.1, hb.1.2, hb.2⟩

theorem nondiv_le (n : ℕ) (h7 : 7 < n) (hn : n ≤ 1000) :
    ¬ strictPartitionCount n ∣ partitionCount n ∧
    ¬ strictPartitionCount n ∣ partitionCount n - 1 ∧
    ¬ strictPartitionCount n ∣ partitionCount n + 1 :=
  nondiv_of_check (1000 + 1) 1000 (by norm_num) (by decide +kernel) n h7 hn

/-! ## The pentagonal form of the three non-divisibility conjectures -/

/-- Beyond any bound `B ≥ 7`: only pentagonal `n` need the full condition; every other `n`
needs one claim, chosen by the parity of `p(n)`. -/
theorem H234_of_pentagonal (B : ℕ) (hB : 7 ≤ B)
    (h2 : ∀ n, B < n → (n ∈ Set.range pentagonal ∨ partitionCount n % 2 = 0) →
      ¬ strictPartitionCount n ∣ partitionCount n)
    (h34 : ∀ n, B < n → (n ∈ Set.range pentagonal ∨ partitionCount n % 2 = 1) →
      2 ≤ partitionCount n % strictPartitionCount n ∧
        partitionCount n % strictPartitionCount n + 2 ≤ strictPartitionCount n) :
    ∀ n, B < n → ¬ strictPartitionCount n ∣ partitionCount n ∧
      ¬ strictPartitionCount n ∣ partitionCount n - 1 ∧
      ¬ strictPartitionCount n ∣ partitionCount n + 1 := by
  intro n hn
  have hP := partitionCount_pos n
  have hQ := three_le_strictPartitionCount n (by omega)
  by_cases hq : strictPartitionCount n % 2 = 1
  · have hpent := (strictPartitionCount_odd_iff n).1 hq
    exact ⟨h2 n hn (Or.inl hpent), ((three_iff_mod _ _ hP hQ).2 (h34 n hn (Or.inl hpent))).2⟩
  · have hq2 : 2 ∣ strictPartitionCount n := Nat.dvd_of_mod_eq_zero (by omega)
    have hpar := parity_split (partitionCount n) _ hP hq2
    by_cases hp : partitionCount n % 2 = 1
    · have h34' := (three_iff_mod _ _ hP hQ).2 (h34 n hn (Or.inr hp))
      exact ⟨hpar.1 hp, h34'.2⟩
    · have hp0 : partitionCount n % 2 = 0 := by omega
      exact ⟨h2 n hn (Or.inr hp0), hpar.2 hp0⟩

theorem main : H1 → H2 → H3 → type_of% @OMA.S_oeis_a000009.main := by
  intro h1 h2 h3
  refine ⟨?_, fun n hn => ?_⟩
  · intro n hn
    obtain ⟨T, hq, hanti, hsum⟩ : ∃ T : Finset ℕ,
        (∀ x ∈ T, ∃ m : ℕ, 0 < m ∧ x = strictPartitionCount m) ∧
        (∀ x ∈ T, ∀ y ∈ T, x ≠ y → ¬ x ∣ y) ∧ (∑ x ∈ T, x) = n := by
      by_cases hb : n < 237
      · exact H1_le n hn (by omega)
      · obtain ⟨l, U, hU, hq0, h180, h20, han0, hcov0⟩ := base_state
        exact rep_of_P (fun x => ∃ m : ℕ, 0 < m ∧ x = strictPartitionCount m)
          (1900360634358457428632022870866610 / 2 + 1) h1 l U (by omega) (by omega) hq0 h180 h20 han0 hcov0 n (by omega)
    obtain ⟨k, terms, hterms, hs, hdiv⟩ := rep_of_finset T hq hanti
    exact ⟨k, terms, hterms, hs.trans hsum, hdiv⟩
  · by_cases hb : n ≤ 1000
    · exact nondiv_le n hn hb
    · exact H234_of_pentagonal 1000 (by norm_num) h2 h3 n (by omega)

end OMA.R_oeis_a000009_R8
