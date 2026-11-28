import OMAStatements.S_oeis_a000009

/-!
# A000009 via descent on the remainder and a small-divisor test

Credit: @wispiANt. The coefficient tables, small cases, and finite
non-divisibility check come from R8 (PR #20438). The second seed is from
note #92063. The descent subtracts a nonempty group of large summands chosen for each target.
All summands in the group lie within a factor of two.
Each finite cap may use its own compatible seed and list of overlapping translations.
The smaller finite base uses 176 indices and the larger one uses 256. The tail can restrict every new term
to a chosen support and test cross-divisibility only against possible terms in that support.
The primitive-window comparison uses the condition reported by @Jwolf52 in note #95249.

Both certificates start with 52 seed values. The first adds 124 values through
index 2200 and the second adds another 80 through index 6200. Each translation
overlaps or touches the preceding interval, as in PR #17774. Each upper endpoint
is the sum of the selected values minus 20301. The 256-value base also supports
49 further values from indices 6201 through 6261 simultaneously.
-/
-- uses note #92063

namespace OMA.R_oeis_a000009_R10

open OMA.S_oeis_a000009

/-- Start from a checked seed interval and add compatible values in right-to-left
list order. Each translation must touch the cumulative interval. Descent handles
targets above the resulting endpoint through the chosen cap. -/
def H1 : Prop :=
  ∀ cap : ℕ, ∃ seed xs : List ℕ, ∃ pool : Finset ℕ,
  let members := xs ++ seed
  let st := xs.foldr (fun a (v : ℕ × Bool) => (v.1+a, v.2 && decide (a ≤ v.1+1-20301))) (3069181,true)
  members.Nodup ∧ (∀ s ∈ members, 1000 ≤ s ∧ s ∈ pool ∧ ∃ m : ℕ, 0 < m ∧ s = strictPartitionCount m) ∧
  (∀ x ∈ members, ∀ y ∈ members, x ≠ y → ¬ x ∣ y) ∧
  ((seed.foldr (fun a b => b ||| b <<< a) 1) >>> 20301) % 2^3048881 = 2^3048881-1 ∧ st.2 = true ∧
  ∀ n : ℕ, st.1 < n → n ≤ cap → ∃ A : Finset ℕ, ∃ r : ℕ,
    A.Nonempty ∧ n = (∑ z ∈ A, z)+r ∧ 20301 ≤ r ∧
    (∀ z ∈ A, 1000 ≤ z ∧ z ∈ pool ∧ (∃ m : ℕ, 0 < m ∧ z = strictPartitionCount m)) ∧
    (∀ x ∈ A, ∀ y ∈ A, y < 2*x) ∧
    ∀ z ∈ A, ∀ s, 1000 ≤ s → (s ∈ pool ∧ (∃ m : ℕ, 0 < m ∧ s = strictPartitionCount m)) →
      (s = r ∨ s + 1000 ≤ r) → ¬ s ∣ z ∧ ¬ z ∣ s

def H2 : Prop :=
  ∀ n : ℕ, 1000 < n → ∀ k : Fin 3,
    let q := strictPartitionCount n
    let y := partitionCount n - 1 + k.val
    let d := (q % 9338866572734899200).gcd 9338866572734899200
    d ∣ y % 9338866572734899200 → ¬ q / d ∣ y / d

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

theorem partitionCount_pos (n : ℕ) : 1 ≤ partitionCount n :=
  Fintype.card_pos_iff.2 ⟨Nat.Partition.indiscrete n⟩
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

/-- Dropping whole low slots of a packed row is an integer division. -/
theorem pack_drop_slots (w k : ℕ) (l : List ℕ) (hk : k ≤ l.length)
    (bound : ∀ x ∈ l, x < 2^w) :
    (l.drop k).foldr (fun a b => a+2^w*b) 0 =
      l.foldr (fun a b => a+2^w*b) 0 / 2^(w*k) := by
  have split := pack_append w (l.take k) (l.drop k)
  have small := pack_lt w (l.take k) (fun x hx => bound x (List.mem_of_mem_take hx))
  rw [List.length_take_of_le hk] at split small
  rw [List.take_append_drop] at split
  rw [split, Nat.add_mul_div_left _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt small, zero_add]

/-- With coefficient zero in the highest slot, adjoining part k shifts the row
right. Bits shifted past the end disappear without a separate truncation. -/
theorem reverse_row_step (w k : ℕ) (l : List ℕ) (hk : k ≤ l.length)
    (bound : ∀ x ∈ l, x < 2^w) :
    (List.zipWith (· + ·) l (List.replicate k 0 ++ l)).reverse.foldr (fun a b => a+2^w*b) 0 =
      l.reverse.foldr (fun a b => a+2^w*b) 0 +
        (l.reverse.foldr (fun a b => a+2^w*b) 0 >>> (w*k)) := by
  rw [List.zipWith_eq_zipWith_take_min]
  simp only [List.length_append, List.length_replicate, Nat.min_eq_left (Nat.le_add_left _ _),
    List.take_length]
  rw [List.reverse_zipWith (by simp), pack_add _ _ _ (by simp)]
  congr 1
  rw [List.take_append, List.take_of_length_le (by simpa using hk), List.reverse_append,
    List.reverse_take, List.reverse_replicate, pack_append, pack_replicate_zero]
  simp only [List.length_replicate, Nat.sub_sub_self hk, mul_zero, add_zero, Nat.shiftRight_eq_div_pow]
  exact pack_drop_slots w k l.reverse (by simpa using hk) (fun x hx => bound x (by simpa using hx))

/-- The periodic guard mask as a geometric sum, without constructing its list of slots. -/
theorem guard_mask_eq (w n a : ℕ) (hw : 0 < w) :
    (List.replicate n a).foldr (fun x b => x+2^w*b) 0 =
      ((2^(w*n)-1)/(2^w-1))*a := by
  let f := fun n => (List.replicate n 1).foldr (fun x b => x+2^w*b) 0
  have pos : 1 < 2^w := Nat.one_lt_two_pow (by omega)
  have series (k : ℕ) : f k * (2^w-1) + 1 = 2^(w*k) := by
    induction k with
    | zero => simp [f]
    | succ k ih =>
      change (1 + 2^w*f k) * (2^w-1) + 1 = 2^(w*(k+1))
      rw [Nat.mul_add,pow_add,mul_one, ← ih]
      have eq : 2^w-1+1 = 2^w := by omega
      calc
        _ = f k * (2^w-1) * 2^w + (2^w-1+1) := by ring
        _ = _ := by rw [eq]; ring
  rw [← series n, Nat.add_sub_cancel, Nat.mul_div_cancel _ (by omega)]
  induction n with
  | zero => simp [f]
  | succ n ih =>
    change a + 2^w * _ = (1+2^w*f n)*a
    rw [ih]
    ring

/-- Extract q(n) from a reversed, guarded table. The nonzero final row certifies
that every intermediate guard passed. -/
theorem strictPartitionCount_of_reverse (v N : ℕ) (hv : 0 < v) (row : ℕ → ℕ) (mask : ℕ)
    (mask_eq : mask = (List.replicate (N+1) (2^v)).foldr (fun a b => a+2^(v+1)*b) 0)
    (initial : row 0 = 2^((v+1)*N))
    (step : ∀ k, row (k+1) = let c := row k + (row k >>> ((v+1)*(k+1)))
      if c &&& mask == 0 then c else 0) (ok : row N ≠ 0) (n : ℕ) (hn : n ≤ N) :
    strictPartitionCount n = (row N >>> ((v+1)*(N-n))) % 2^(v+1) := by
  let t := Nat.rec (motive := fun _ => List ℕ) (1 :: List.replicate N 0)
    (fun k l => List.zipWith (· + ·) l (List.replicate (k+1) 0 ++ l))
  have start : t 0 = 1 :: List.replicate N 0 := rfl
  have next : ∀ k, t (k+1) = List.zipWith (· + ·) (t k) (List.replicate (k+1) 0 ++ t k) := fun _ => rfl
  have len := tbl_length N t start next
  have pass := guard_pass N mask row (fun b k => b + (b >>> ((v+1)*(k+1))))
    (fun _ => by simp) step ok
  have exactRows (k : ℕ) (hk : k ≤ N) :
      row k = (t k).reverse.foldr (fun a b => a+2^(v+1)*b) 0 ∧ ∀ x ∈ t k, x < 2^v := by
    induction k with
    | zero =>
      refine ⟨?_,?_⟩
      · rw [initial,start,List.reverse_cons,List.reverse_replicate,pack_shift]
        simp
      · intro x hx
        rw [start] at hx
        rcases List.mem_cons.mp hx with rfl | h
        · exact Nat.one_lt_two_pow (by omega)
        · rw [List.eq_of_mem_replicate h]; exact Nat.two_pow_pos _
    | succ k ih =>
      obtain ⟨eq,bound⟩ := ih (by omega)
      have wide : ∀ x ∈ t k, x < 2^(v+1) := fun x hx =>
        lt_trans (bound x hx) (Nat.pow_lt_pow_right (by decide) (by omega))
      have packed : row (k+1) = (t (k+1)).reverse.foldr (fun a b => a+2^(v+1)*b) 0 := by
        rw [(pass k (by omega)).1,eq,next,reverse_row_step _ _ _ (by rw [len]; omega) wide]
      have guard := (pass k (by omega)).2
      rw [← (pass k (by omega)).1,packed,mask_eq,← len (k+1),← List.length_reverse (as := t (k+1))] at guard
      refine ⟨packed,fun x hx => entries_lt_of_guard v _ ?_ guard x (by simpa using hx)⟩
      intro x hx
      have hmem : x ∈ t (k+1) := by simpa using hx
      rw [next] at hmem
      obtain ⟨i,hi,rfl⟩ := List.mem_iff_getElem.mp hmem
      rw [List.getElem_zipWith]
      simp only [List.length_zipWith, List.length_append, List.length_replicate, len] at hi
      have hleft := bound _ (List.getElem_mem (l := t k) (n := i) (by rw [len]; omega))
      have hright : ∀ z ∈ List.replicate (k+1) 0 ++ t k, z < 2^v := by
        intro z hz
        rcases List.mem_append.mp hz with hz | hz
        · rw [List.eq_of_mem_replicate hz]; exact Nat.two_pow_pos _
        · exact bound z hz
      have hr := hright _ (List.getElem_mem (l := List.replicate (k+1) 0 ++ t k) (n := i) (by simp [len]; omega))
      rw [pow_succ]; omega
  obtain ⟨eq,bound⟩ := exactRows N le_rfl
  rw [eq,Nat.shiftRight_eq_div_pow,pack_digit _ _ (fun x hx =>
    lt_trans (bound x (by simpa using hx)) (Nat.pow_lt_pow_right (by decide) (by omega)))]
  have h := strictPartitionCount_eq_rec N n hn
  change strictPartitionCount n = (t N).getD n 0 at h
  rw [h]
  simp only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem (by rw [len]; omega : n < (t N).length),
    List.getElem?_eq_getElem (by rw [List.length_reverse,len]; omega : N-n < (t N).reverse.length),
    Option.getD_some,List.getElem_reverse]
  congr 1
  rw [len]; omega

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

/-- Evaluate the truncated geometric factor by a single natural division. -/
theorem geom_fast (X M j : ℕ) (hx : 1 < X) (hm : 1 < M) :
    Nat.rec (motive := fun _ => ℕ) 1 (fun _ g => (1 + X * g) % M) j =
      ((X^(j+1)-1)/(X-1)) % M := by
  let F (t : ℕ) := Nat.rec (motive := fun _ => ℕ) 1 (fun _ g => 1 + X*g) t
  have series (t : ℕ) : F t * (X-1) + 1 = X^(t+1) := by
    induction t with
    | zero => change 1 * (X-1) + 1 = X^1; simp; omega
    | succ t ih =>
      change (1+X*F t)*(X-1)+1 = X^(t+1+1)
      rw [pow_succ, ← ih]
      have h : X-1+1 = X := by omega
      calc
        _ = F t*(X-1)*X + (X-1+1) := by ring
        _ = _ := by rw [h]; ring
  have reduction (t : ℕ) :
      Nat.rec (motive := fun _ => ℕ) 1 (fun _ g => (1 + X*g) % M) t = F t % M := by
    induction t with
    | zero => exact (Nat.mod_eq_of_lt hm).symm
    | succ t ih =>
      change (1+X*_ ) % M = (1+ X*F t) % M
      rw [ih]
      exact Nat.ModEq.add_left 1 (Nat.ModEq.mul_left X (Nat.mod_modEq _ _))
  rw [reduction, ← series, Nat.add_sub_cancel, Nat.mul_div_cancel _ (by omega)]

theorem partitionCount_eq_fast (w N n : ℕ) (hw : N < w) (hn : n ≤ N) :
    partitionCount n = ((Nat.rec (motive := fun _ => ℕ) 1 (fun K B =>
      (B * (((2 ^ (w*(K+1)*(N/(K+1)+1))-1) / (2 ^ (w*(K+1))-1)) % 2 ^ (w*(N+1))))
        % 2 ^ (w*(N+1))) N) / 2^(w*n)) % 2^w := by
  rw [partitionCount_eq_packed w N n hw hn]
  have hwpos : 0 < w := by omega
  have factor (K : ℕ) :
      Nat.rec (motive := fun _ => ℕ) 1
        (fun _ g => (1+2^(w*(K+1))*g) % 2^(w*(N+1))) (N/(K+1)) =
        ((2^(w*(K+1)*(N/(K+1)+1))-1)/(2^(w*(K+1))-1)) % 2^(w*(N+1)) := by
    rw [geom_fast, ← pow_mul] <;> apply Nat.one_lt_two_pow <;> positivity
  simp_rw [factor]

/-! ## The finite range `8 ≤ n ≤ 1000`, checked by the kernel -/

/-- From the Boolean range check to the three claims, for each `8 ≤ n ≤ N`. -/
theorem nondiv_of_check (w N : ℕ) (hw : N < w)
    (h : (List.range (N + 1)).all (fun n => n ≤ 7 ||
      (((Nat.rec (motive := fun _ => ℕ) 1
        (fun K B => (B * (((2^(w*(K+1)*(N/(K+1)+1))-1)/(2^(w*(K+1))-1)) % 2^(w*(N+1))))
            % 2 ^ (w * (N + 1))) N) / 2 ^ (w * n)) % 2 ^ w %
        (((Nat.rec (motive := fun _ => ℕ) 1
          (fun K B => B + (2 ^ (w * (K + 1)) * B) % 2 ^ (w * (N + 1))) N) / 2 ^ (w * n)) % 2 ^ w)
          != 0 &&
       ((((Nat.rec (motive := fun _ => ℕ) 1
        (fun K B => (B * (((2^(w*(K+1)*(N/(K+1)+1))-1)/(2^(w*(K+1))-1)) % 2^(w*(N+1))))
            % 2 ^ (w * (N + 1))) N) / 2 ^ (w * n)) % 2 ^ w) - 1) %
        (((Nat.rec (motive := fun _ => ℕ) 1
          (fun K B => B + (2 ^ (w * (K + 1)) * B) % 2 ^ (w * (N + 1))) N) / 2 ^ (w * n)) % 2 ^ w)
          != 0 &&
       ((((Nat.rec (motive := fun _ => ℕ) 1
        (fun K B => (B * (((2^(w*(K+1)*(N/(K+1)+1))-1)/(2^(w*(K+1))-1)) % 2^(w*(N+1))))
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
  rw [← strictPartitionCount_eq_packed w N n hw hn, ← partitionCount_eq_fast w N n hw hn] at hb
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


open Finset

/-- A positive multiple of a that is smaller than 2*a must equal a. -/
theorem band_nondiv {a b : ℕ} (pos : 0 < b) (near : b < 2*a) (ne : a ≠ b) : ¬ a ∣ b :=
  fun dv => ne (Nat.eq_of_dvd_of_lt_two_mul pos.ne' dv near).symm

/-- A member of a finite sum exhausts it or leaves at least one other term. -/
theorem remainder_term (T : Finset ℕ) (B s : ℕ) (hs : s ∈ T) (lower : ∀ t ∈ T, B ≤ t) :
    s = ∑ t ∈ T, t ∨ s+B ≤ ∑ t ∈ T, t := by
  have total := Finset.add_sum_erase T (fun t : ℕ => t) hs
  by_cases h : (T.erase s).Nonempty
  · obtain ⟨t,ht⟩ := h
    have := single_le_sum (f := fun t : ℕ => t) (fun _ _ => Nat.zero_le _) ht
    have := lower t (mem_of_mem_erase ht)
    exact Or.inr (by omega)
  · rw [not_nonempty_iff_eq_empty.mp h, sum_empty] at total
    exact Or.inl (by simpa using total)

/-- Distinct summands within a factor of two cannot divide one another.
Only possible terms of the remainder need a cross-divisibility test. -/
theorem descent (Q : ℕ → Prop) (B L U cap : ℕ) (positive : 0 < B)
    (base : ∀ n, L ≤ n → n ≤ U → ∃ T : Finset ℕ,
      (∀ s ∈ T, B ≤ s ∧ Q s) ∧
      (∀ x ∈ T, ∀ y ∈ T, x ≠ y → ¬ x ∣ y) ∧ (∑ s ∈ T, s) = n)
    (tail : ∀ n, U < n → n ≤ cap → ∃ A : Finset ℕ, ∃ r : ℕ,
      A.Nonempty ∧ n = (∑ z ∈ A, z)+r ∧ L ≤ r ∧
      (∀ z ∈ A, B ≤ z ∧ Q z) ∧ (∀ x ∈ A, ∀ y ∈ A, y < 2*x) ∧
      ∀ z ∈ A, ∀ s, B ≤ s → Q s → (s = r ∨ s+B ≤ r) → ¬ s ∣ z ∧ ¬ z ∣ s) :
    ∀ n, L ≤ n → n ≤ cap → ∃ T : Finset ℕ,
      (∀ s ∈ T, B ≤ s ∧ Q s) ∧
      (∀ x ∈ T, ∀ y ∈ T, x ≠ y → ¬ x ∣ y) ∧ (∑ s ∈ T, s) = n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn hcap
    by_cases hsmall : n ≤ U
    · exact base n hn hsmall
    obtain ⟨A,r,⟨a,ha⟩,eq,rl,newTerm,near,clean⟩ := tail n (by omega) hcap
    have asum := single_le_sum (f := fun i : ℕ => i) (fun _ _ => Nat.zero_le _) ha
    have ab := (newTerm a ha).1
    obtain ⟨T,good,anti,hs⟩ := ih r (by omega) rl (by omega)
    have compatible {z s : ℕ} (hz : z ∈ A) (ht : s ∈ T) : ¬ s ∣ z ∧ ¬ z ∣ s :=
      clean z hz s (good s ht).1 (good s ht).2
        (hs ▸ remainder_term T B s ht (fun t h => (good t h).1))
    have disj : Disjoint A T := disjoint_left.mpr fun z hz ht => (compatible hz ht).1 dvd_rfl
    refine ⟨A ∪ T, ?_, ?_, by rw [sum_union disj, hs, eq]⟩
    · intro z hz
      rcases mem_union.mp hz with h | h
      · exact newTerm z h
      · exact good z h
    · intro x hx y hy ne
      rcases mem_union.mp hx with xa | xt <;> rcases mem_union.mp hy with ya | yt
      · exact band_nondiv (lt_of_lt_of_le positive (newTerm y ya).1) (near x xa y ya) ne
      · exact (compatible xa yt).2
      · exact (compatible ya xt).1
      · exact anti x xt y yt ne

/-- A primitive value a can also be used just above 2a, until the excess reaches 1000.
At 2a itself the remainder could be the singleton {a}. -/
theorem primitive_step (a r : ℕ) (big : 1000 ≤ a)
    (primitive : ∀ s, 1000 ≤ s → (∃ m : ℕ, 0 < m ∧ s = strictPartitionCount m) →
      2*s ≤ a → ¬ s ∣ a)
    (near : r < a+1000) (different : r ≠ a) :
    ∀ s, 1000 ≤ s → (∃ m : ℕ, 0 < m ∧ s = strictPartitionCount m) →
      (s = r ∨ s+1000 ≤ r) → ¬ s ∣ a ∧ ¬ a ∣ s := by
  intro s bs qs fit
  have ne : s ≠ a := by rcases fit with h | h <;> omega
  have small : s < 2*a := by rcases fit with h | h <;> omega
  refine ⟨?_, band_nondiv (by omega) small (Ne.symm ne)⟩
  by_cases h : 2*s ≤ a
  · exact primitive s bs qs h
  · exact band_nondiv (by omega) (by omega) ne

/-- Through a fixed cap, every added term is at most the cap. Keep the required
base values as well, even when the cap is below the certified interval. -/
theorem finite_support (indices : List ℕ) (f : ℕ → ℕ) (Q keep : ℕ → Prop) (B L U cap : ℕ)
    (base : ∀ i ∈ indices, keep (f i))
    (tail : ∀ n, U < n → n ≤ cap → ∃ A : Finset ℕ, ∃ r : ℕ,
      A.Nonempty ∧ n = (∑ z ∈ A, z)+r ∧ L ≤ r ∧
      (∀ z ∈ A, B ≤ z ∧ keep z ∧ Q z) ∧ (∀ x ∈ A, ∀ y ∈ A, y < 2*x) ∧
      ∀ z ∈ A, ∀ s, B ≤ s → (keep s ∧ Q s) → (s = r ∨ s+B ≤ r) → ¬ s ∣ z ∧ ¬ z ∣ s) :
    ∃ pool : Finset ℕ, (∀ i ∈ indices, f i ∈ pool) ∧
      ∀ n, U < n → n ≤ cap → ∃ A : Finset ℕ, ∃ r : ℕ,
      A.Nonempty ∧ n = (∑ z ∈ A, z)+r ∧ L ≤ r ∧
      (∀ z ∈ A, B ≤ z ∧ z ∈ pool ∧ Q z) ∧ (∀ x ∈ A, ∀ y ∈ A, y < 2*x) ∧
      ∀ z ∈ A, ∀ s, B ≤ s → (s ∈ pool ∧ Q s) → (s = r ∨ s+B ≤ r) → ¬ s ∣ z ∧ ¬ z ∣ s := by
  classical
  let pool := (indices.map f).toFinset ∪ (range (cap+1)).filter keep
  have kept {s : ℕ} (hs : s ∈ pool) : keep s := by
    rcases mem_union.mp hs with h | h
    · obtain ⟨i,hi,eq⟩ := List.mem_map.mp (List.mem_toFinset.mp h)
      exact eq ▸ base i hi
    · exact (mem_filter.mp h).2
  refine ⟨pool,fun i hi => mem_union_left _ (List.mem_toFinset.mpr (List.mem_map.mpr ⟨i,hi,rfl⟩)),?_⟩
  intro n hn hc
  obtain ⟨A,r,ne,total,lo,values,band,clean⟩ := tail n hn hc
  refine ⟨A,r,ne,total,lo,?_,band,fun z hz s hs hq => clean z hz s hs ⟨kept hq.1,hq.2⟩⟩
  intro z hz
  have small := single_le_sum (f := fun x : ℕ => x) (fun _ _ => Nat.zero_le _) hz
  exact ⟨(values z hz).1, mem_union_right _ (mem_filter.mpr
    ⟨mem_range.mpr (by omega),(values z hz).2.1⟩), (values z hz).2.2⟩

/-- A finite sequence suffices up to cap when its last interval reaches cap. -/
theorem finite_tail_of_spacing (Q : ℕ → Prop) (a : ℕ → ℕ) (B L U cap last : ℕ)
    (positive : 0 < B) (values : ∀ i ≤ last, B ≤ a i ∧ Q (a i))
    (primitive : ∀ i ≤ last, ∀ s, B ≤ s → Q s → 2*s ≤ a i → ¬ s ∣ a i)
    (start : a 0 + L ≤ U+1) (spacing : ∀ i < last, a (i+1) + L ≤ 2*a i)
    (finish : cap < 2*a last) :
    ∀ n, U < n → n ≤ cap → ∃ A : Finset ℕ, ∃ r : ℕ,
      A.Nonempty ∧ n = (∑ z ∈ A, z)+r ∧ L ≤ r ∧
      (∀ z ∈ A, B ≤ z ∧ Q z) ∧ (∀ x ∈ A, ∀ y ∈ A, y < 2*x) ∧
      ∀ z ∈ A, ∀ s, B ≤ s → Q s → (s = r ∨ s+B ≤ r) → ¬ s ∣ z ∧ ¬ z ∣ s := by
  intro n hn hc
  have cover (k : ℕ) : k ≤ last → n < 2*a k → ∃ i ≤ k, a i+L ≤ n ∧ n < 2*a i := by
    induction k with
    | zero => exact fun _ h => ⟨0,le_rfl,by omega,h⟩
    | succ k ih =>
      intro hk h
      by_cases prev : n < 2*a k
      · obtain ⟨i,le,lo,hi⟩ := ih (by omega) prev
        exact ⟨i,by omega,lo,hi⟩
      · exact ⟨k+1,le_rfl,by have := spacing k (by omega); omega,h⟩
  obtain ⟨i,ile,lo,hi⟩ := cover last le_rfl (by omega)
  have pos := lt_of_lt_of_le positive (values i ile).1
  refine ⟨{a i},n-a i,singleton_nonempty _,by simp; omega,by omega,?_,?_,?_⟩
  · simpa using values i ile
  · simpa using (show a i < 2*a i by omega)
  · intro z hz s bs qs fit
    obtain rfl := mem_singleton.mp hz
    have lt : s < a i := by rcases fit with h | h <;> omega
    refine ⟨?_,fun dv => (Nat.not_le_of_lt lt) (Nat.le_of_dvd (by omega) dv)⟩
    by_cases h : 2*s ≤ a i
    · exact primitive i ile s bs qs h
    · exact band_nondiv pos (by omega) (Nat.ne_of_lt lt)

/-- A finite antichain of certified base values and additional witnesses supplies
both the support and every cross-divisibility test needed up to cap. -/
theorem finite_tail_of_antichain (Q : ℕ → Prop) (seed : Finset ℕ) (a : ℕ → ℕ)
    (B L U cap last : ℕ) (pos : 0 < B)
    (values : ∀ i ≤ last, B ≤ a i ∧ Q (a i))
    (start : a 0 + L ≤ U+1) (spacing : ∀ i < last, a (i+1)+L ≤ 2*a i)
    (finish : cap < 2*a last) :
    let pool := seed ∪ (range (last+1)).image a
    (∀ x ∈ pool, ∀ y ∈ pool, x ≠ y → ¬ x ∣ y) →
    ∀ n, U < n → n ≤ cap → ∃ A : Finset ℕ, ∃ r : ℕ,
      A.Nonempty ∧ n = (∑ z ∈ A, z)+r ∧ L ≤ r ∧
      (∀ z ∈ A, B ≤ z ∧ z ∈ pool ∧ Q z) ∧ (∀ x ∈ A, ∀ y ∈ A, y < 2*x) ∧
      ∀ z ∈ A, ∀ s, B ≤ s → (s ∈ pool ∧ Q s) → (s = r ∨ s+B ≤ r) → ¬ s ∣ z ∧ ¬ z ∣ s := by
  intro pool anti
  have mem (i : ℕ) (hi : i ≤ last) : a i ∈ pool :=
    mem_union_right _ (mem_image.mpr ⟨i,mem_range.mpr (by omega),rfl⟩)
  apply finite_tail_of_spacing (fun s => s ∈ pool ∧ Q s) a B L U cap last pos
    (fun i hi => ⟨(values i hi).1,mem i hi,(values i hi).2⟩) _ start spacing finish
  intro i hi s bs hs small
  exact anti s hs.1 (a i) (mem i hi) (by omega)

/-- To construct the tail on a chosen support Q, only proper divisors in Q need
to be excluded. The sequence and every summand in the induction belong to Q. -/
theorem tail_of_supported_spacing (Q : ℕ → Prop) (a : ℕ → ℕ) (B L U : ℕ)
    (positive : 0 < B) (values : ∀ i, B ≤ a i ∧ Q (a i))
    (primitive : ∀ i s, B ≤ s → Q s → 2*s ≤ a i → ¬ s ∣ a i)
    (start : a 0 + L ≤ U+1) (spacing : ∀ i, a (i+1) + L ≤ 2*a i)
    (unbounded : ∀ n, ∃ i, n < 2*a i) :
    ∀ n, U < n → ∃ A : Finset ℕ, ∃ r : ℕ,
      A.Nonempty ∧ n = (∑ z ∈ A, z)+r ∧ L ≤ r ∧
      (∀ z ∈ A, B ≤ z ∧ Q z) ∧ (∀ x ∈ A, ∀ y ∈ A, y < 2*x) ∧
      ∀ z ∈ A, ∀ s, B ≤ s → Q s → (s = r ∨ s+B ≤ r) → ¬ s ∣ z ∧ ¬ z ∣ s := by
  intro n hn
  obtain ⟨last,finish⟩ := unbounded n
  exact finite_tail_of_spacing Q a B L U n last positive (fun i _ => values i)
    (fun i _ => primitive i) start (fun i _ => spacing i) finish n hn le_rfl

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

/-- Extend an interval of subset sums by adding fresh values in order.
The Boolean records whether each translated interval overlaps or touches. -/
theorem translate_chain (L U : ℕ) (seed xs : List ℕ)
    (base : ∀ n, L ≤ n → n ≤ U → ∃ T ⊆ seed.toFinset, (∑ z ∈ T, z) = n)
    (nd : (xs ++ seed).Nodup) :
    let st := xs.foldr (fun a (v : ℕ × Bool) => (v.1+a, v.2 && decide (a ≤ v.1+1-L))) (U,true)
    st.2 = true → ∀ n, L ≤ n → n ≤ st.1 → ∃ T ⊆ (xs ++ seed).toFinset, (∑ z ∈ T, z) = n := by
  induction xs with
  | nil => exact fun _ => base
  | cons a rest ih =>
    dsimp only
    intro ok
    obtain ⟨prior,fit⟩ := Bool.and_eq_true_iff.mp ok
    obtain ⟨fresh,nodup⟩ := List.nodup_cons.mp nd
    simpa only [List.cons_append, List.toFinset_cons, List.foldr_cons] using extend_cover (rest ++ seed).toFinset a L _ (fun h => fresh (List.mem_toFinset.mp h))
      (ih nodup prior) (of_decide_eq_true fit)

/-- A divisor test using two bounded residues, followed by exact cancellation. -/
theorem residual_iff (q y M : ℕ) (hM : 0 < M) :
    let d := (q % M).gcd M
    (¬ q ∣ y) ↔ (d ∣ y % M → ¬ q / d ∣ y / d) := by
  dsimp only
  rw [← Nat.gcd_rec M q, Nat.gcd_comm M q]
  let d := q.gcd M
  have dq : d ∣ q := Nat.gcd_dvd_left _ _
  have dm : d ∣ M := Nat.gcd_dvd_right _ _
  have pos : 0 < d := Nat.gcd_pos_of_pos_right _ hM
  change (¬ q ∣ y) ↔ (d ∣ y % M → ¬ q / d ∣ y / d)
  rw [Nat.dvd_mod_iff dm]
  constructor
  · intro hn dy h
    apply hn
    have hy := (Nat.div_dvd_iff_dvd_mul dq pos).mp h
    simpa only [Nat.mul_div_cancel' dy] using hy
  · intro h hy
    exact h (dvd_trans dq hy) (Nat.div_dvd_div dq hy)

/-- The three original tests are equivalent to checking just the surviving offsets. -/
theorem triple_iff (P Q M : ℕ) (hP : 0 < P) (hM : 0 < M) :
    (¬ Q ∣ P ∧ ¬ Q ∣ P-1 ∧ ¬ Q ∣ P+1) ↔
      ∀ k : Fin 3, let y := P-1+k.val
        let d := (Q % M).gcd M
        d ∣ y % M → ¬ Q / d ∣ y / d := by
  constructor
  · intro h k
    apply (residual_iff _ _ _ hM).mp
    fin_cases k
    · exact h.2.1
    · change ¬ Q ∣ P - 1 + 1
      rw [Nat.sub_add_cancel hP]
      exact h.1
    · change ¬ Q ∣ P - 1 + 2
      rw [show P-1+2 = P+1 by omega]
      exact h.2.2
  · intro h
    have each (k : Fin 3) := (residual_iff _ _ _ hM).mpr (h k)
    have low := each 0
    have mid := each 1
    have high := each 2
    simp only [Fin.val_zero, Fin.val_one, Fin.val_two, Nat.add_zero] at low mid high
    exact ⟨by convert mid using 2; omega, low, by convert high using 2; omega⟩


set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The three coefficient lists are certified separately from the subset-sum and divisibility checks. -/
theorem chain_coefficients (withNext : Bool := false) (withBand : Bool := false) :
    let initial : List ℕ := [40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 60, 61, 62, 63, 64, 65, 66, 67, 69, 70, 71, 72, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 92, 93, 94, 95]
    let seed : List ℕ := [1113, 1260, 1426, 1610, 1816, 2048, 2304, 2590, 2910, 3264, 3658, 4097, 4582, 5120, 5718, 6378, 7108, 7917, 8808, 10880, 12076, 13394, 14848, 16444, 18200, 20132, 22250, 27130, 29927, 32992, 36352, 44046, 48446, 53250, 58499, 64234, 70488, 77312, 84756, 92864, 101698, 111322, 121792, 133184, 145578, 159046, 173682, 189586, 225585, 245920, 267968, 291874]
    let earlier : List ℕ := [
    124, 133, 142, 151, 161, 171, 181, 192, 203, 214, 225, 237, 249, 261, 274, 287, 300, 314, 328,
    342, 356, 371, 386, 401, 417, 433, 449, 466, 483, 500, 517, 535, 553, 571, 590, 608, 627, 646,
    665, 685, 705, 726, 747, 768, 789, 811, 833, 855, 878, 900, 923, 945, 969, 993, 1017, 1040,
    1065, 1090, 1116, 1142, 1168, 1194, 1221, 1248, 1274, 1302, 1330, 1358, 1386, 1415, 1444,
    1473, 1503, 1533, 1562, 1591, 1622, 1653, 1684, 1716, 1748, 1779, 1812, 1845, 1876, 1909,
    1943, 1976, 2010, 2045, 2080, 2114, 2149, 2166, 2167, 2168, 2169, 2170, 2171, 2172, 2173,
    2174, 2175, 2176, 2177, 2178, 2179, 2180, 2181, 2182, 2183, 2185, 2186, 2187, 2188, 2189,
    2190, 2191, 2192, 2193, 2194, 2197, 2199, 2200]
    let middle : List ℕ := [
    2974400, 5802008, 11086968, 20792120, 40982540, 79229676, 150473568, 299016608, 583473184,
    1119555488, 2114965120, 4163989458, 8067955712, 15400801856, 30542758738, 59656252987,
    114872472064, 229184682870, 450666531450, 874201606890, 1674182409148, 3313846677248,
    6474200116480, 12493440408000, 24867441720078, 48880168540672, 94946245905984,
    189885350594524, 375210787343946, 732986521245024, 1416439699443142, 2813432400120490,
    5526916854475456, 10743948315198452, 21436830186242063, 40841012493194682, 79850366709300780,
    154605520700705120, 296566421243219584, 583064907329563392, 1135514750730008498,
    2264099687978533120, 4471243846198231222, 8749076605552831010, 16969018471958594188,
    33658554486099838720, 66167480560136966222, 128959762210836804066, 256797752929721054144,
    492244122149966911170, 963936587035181776118, 1819432729601465049152, 3608821796790641279424,
    7099574931537767204250, 13856795874852965173664, 26114238731192528551360,
    51603947016881466592794, 101187082100171176234122, 202217398295763141057824,
    400974246199817583894742, 789100539835396883939358, 1541605650408283495393522,
    3067246836584607264472876, 6057832938243693897513760, 11587856205784909926984270,
    23133214031490814970843946, 45849222558168996948474368, 90237721732402250231404576,
    176399164530456252077526460, 350741742631318772385582430, 692632149839450032033159272,
    1358720023681540379617941670, 2709554728070710803686491766, 5367264525360833458692206290,
    10328159113745691088153035474, 19757024974832794901430315808, 39271931648224901602532811744,
    77564687783000975558719979596, 152245211464478503515661835584, 303468944818089580243371962908,
    601119078496968105240844836482, 1158781895436941400454219080758,
    2316170889443722154127194213952, 4601150472448384542496370017042,
    8720147493887027887169515613502, 17125122235360043981237309102106,
    34122295129109726757172201549258, 66250476361820092866089672434520,
    130500758305232545022214498828800, 260708483130336361445704424770194,
    517825573584622961930450020039098, 1003110675762233960017588378359296,
    1970615048942618101201014150229370, 2730189046780230565216352391033856,
    2782944698114717778427427165372650, 2836707450938719652759075016862144,
    2891496298934917812574271524969138, 2947330589686561286495922675738294,
    3004230031192170155185912537909504, 3062214698498721998695345515901472,
    3121305040455450114757635634686810, 3181521886590420275371284875879978,
    3242886454112091247959266251495074, 3305420355038103440786935453055146,
    3369145603453579851856655156280206, 3434084622901264018061540697870528,
    3500260253905860889063285152534608, 3567695761634988500456669586623526,
    3636414843699191005803609796313196, 3706441638093507059784082442443890,
    3777800731283131737958736774463626, 3924616451803206622397933581141549,
    4000124569255080003904403193838496, 4077067982967062771640042697374910,
    4155473648266740119900852854611456, 4235369020639694010031564061084928,
    4316782064898767180813986633691570, 4399741264519412854917029197537024,
    4484275631144102539847529636077830, 4570414714258816883142527366951504,
    4658188611044698021214746026795904, 4931628582570689013431218105121792,
    5122673319178024297743108598313984, 5220920096638635664895868609268224]
    let extension : List ℕ := [2367, 2404, 2441, 2479, 2517, 2556, 2595, 2634, 2674, 2714, 2754, 2794, 2835, 2876,
      2917, 2957, 2998, 3040, 3082, 3125, 3168, 3211, 3255, 3299, 3343, 3387, 3432, 3477,
      3521, 3567, 3613, 3659, 3706, 3753, 3800, 3847, 3895, 3943, 3991, 4039, 4086, 4135,
      4184, 4233, 4283, 4333, 4384, 4435, 4486, 4536, 4588, 4640, 4692, 4744, 4797, 4849,
      4903, 4957, 5008, 5062, 5117, 5172, 5226, 5282, 5338, 5394, 5448, 5505, 5561, 5618,
      5676, 5734, 5792, 5850, 5909, 5968, 6027, 6086, 6146, 6200]
    let last : List ℕ := [117665756756784825837202462472388254, 231197095144609850980382573599363746,
      451964286803372727940950418977015372, 895045353711368482580656120894531498,
      1763429740087757195717887235787763820, 3518497365105720386333174445200590820,
      6984153482976505032007039759539892800, 13793599366905064745471518657960637664,
      27579888174107950819208884203702759780, 54865729937189791085600571152170744772,
      108605461223285745666736417479920383552, 213939196255654544589154838716454140982,
      426525638061811746282267188032768265598, 846203123020354672658671530625835171424,
      1670796750746766135823086757120901090406, 3230002940319946889011539904499195302738,
      6319277464475912872342436814650459035136, 12508722483843654573732491901257133757522,
      24646077793710701359867593500143074424040, 49119584729121300101049137845273511977280,
      97440285461053023702522791788603466845184, 192415494209288506142450928091133815910900,
      384240014916809130588519457072165074514742, 763785395041754273233433823158028579349560,
      1511421819291950091832705626428329968260266, 2977718866142536806650369196391153815974528,
      5931043231667205919403663625553146259764455, 11761176958536667539840749369777804056948142,
      22873621071019499776229273253021208391832364, 45651357740828869985748096860546974511873280,
      90713174397377262677516940143749759977051488, 179481956820573901843449847974871997656565504,
      358857684842826558894383840901453966105337796, 714410216421606067458487555038480635368139250,
      1416223591908431854325153080295594397869225920, 2795815461506865765382581687872542087100172760,
      5576198394376176485044998273949899721490807530, 11075176274368349037957417753016126040799059808,
      21906781818228464444917784011949573295135209364, 43157257393629924614289263717349003130010264128,
      83507526212000697859553907630835753433694476256, 165527029171904683332773658951584197299304604958,
      326798094356650130228479563997752275903735278114, 642669206702463746245831575765797045333947216384,
      1276335181157687550813565967354099369634108011222, 2524816144328294749111339409749718727653624547886,
      5042971577907052033638901514905621170760332056248, 10032809563936137372897732514175808209418916697726,
      19882328820672696927542502746678752833629484741120, 38732283057095097350557425447807253975989625528540,
      77196181371552881019262524695389996574644350532316, 153266310583994569021944055206263667259135901586140,
      303147192092284368969244368565597803510734640714312, 597369976756256161657816587497538531423999743485184,
      1188123831793389036109705657166408103321453475031144, 2324159233979146821469009853355386013606240199841748,
      4647811860200069759413646270244144669265803090414498, 9259720758827089566182517281584494319655746895531976,
      17694602288773760397768490921260567352592026147099578, 35001707525417313393239325310897256370358391852747784,
      69859071623159284378516377127850078399482585894353160, 138920517015051718969193560143508091530519356387539588,
      271868746298467172926564948990960362844057427974208780, 543479672735312927554423493389653350596104814016126208,
      1082517769462016526254871805980646857453108404213312650, 2148517820824559798247482756461825778682134690434290194,
      4147315399246098851055270327284177266872873977052409336, 8274640457002581252834239451185311767216403994938970432,
      16254611560703250070622193326193286896212528004046681004, 32206597031343087683063932799606203763465015493295827904,
      64357296433776787789093588870847051156650781606863182914, 128154964196767275610628949557443430864796339873793061888,
      254320008992188698895624796836336779127602644626496881600, 502985286768421664796355489166449322725034613689331096462,
      1003113894477255641067400169773941102873618276709313952704, 1993739284306144150513398921604885165270907946761272515584,
      3949401902475447407037832941792146338306246285580941557752, 7797588330336638168452762081945635097782585000359481952640,
      15521982489439769174201559480094487075251892984927646423036, 28760948436164145408705288538638349951127885748752914972416]
    let bandIndices : List ℕ := [6201, 6203, 6205, 6206, 6208, 6210, 6211, 6212, 6213, 6214, 6215, 6216, 6218, 6219, 6221, 6222, 6223, 6224,
      6225, 6227, 6228, 6229, 6230, 6231, 6233, 6234, 6235, 6236, 6237, 6238, 6239, 6240, 6241, 6242, 6243,
      6244, 6246, 6247, 6248, 6250, 6252, 6253, 6254, 6256, 6257, 6258, 6259, 6260, 6261]
    let bandValues : List ℕ := [29090594252516759840173920707699110105324342633332184909690, 29761182806267740289667025854829485253070097408043849074622,
      30447118915337484819268115873819572709850816159625875801134,
      30795950979378113838974545112378767154719622459708373270340,
      31505564762534328157487149720590388221167914207231328655232,
      32231412760276493606870317419424021318876934304740377378968,
      32600539498790010133764627084322099804004275611121921311776,
      32973863714497093280614246765986265429962539344117347491960,
      33351432800879501757088845428670416398013059982086774153562,
      33733294682752522189862524354051823117839178986984359356700,
      34119497822179703146169873432433753831961852713856224771934,
      34510091224452965981182041008234275517752539434548312173700,
      35304647591191337482758380313008272320590737030898421673976,
      35708711337132831190899209168759372807202177307652751041866,
      36530666157175027341128421198110425459656015498964052092160,
      36948661438747021301572431525711803152198530342498357480128,
      37371405746996563979152621657289651114782906980048553793024,
      37798952656412202105820095929606464150800092263558495821218,
      38231356341594820683625089079870110276909404597951248377954,
      39110953778347911932385462726042540358717789010819989795640,
      39558258940123174941479362282948888998266594293227006546944,
      40010643711796133128936762264092826587853242539524768890394,
      40468165370135737163576838105219530905883341778483117652118,
      40930881833193251048046679564171241106427826147113435659552,
      41872134094932811397907138479759648486763634382825407346944,
      42350789000686528175097125544104078959284760167289458596096,
      42834876939956938671922018285475747884835198131103398683976,
      43324459145732532397942010125003804138783999937976666215168,
      43819597536257455986322949067090688737450330635711693200850,
      44320354722646075699418480060885187335681656525822113543958,
      44826794016581556250544938982581728865028321268192943520904,
      45338979438099376412751327562468252757848099538201903459656,
      45856975723456711898879711073347908995792614155071467444520,
      46380848333088626118870706379583876513290166389879536667072,
      46910663459652019651254562303316536046747828908488665521580,
      47446488036158299607253229244922064979306694450097462854080,
      48536437022242518950136538665320382606783484887615290286720,
      49090699074071414704731357186761256855794750828052097699328,
      49651245877247182310839560306849198411928561771280701827078,
      50791477568499273325792125974992210013717081784184763637174,
      51957707721192530853739133513249376691697490694264994249920,
      52550755633999940987327983462598703529689136705424268474208,
      53150524900961482840607671116297253932412945422729242554474,
      54370530902718733297983762568588136777548923736162164717628,
      54990921462656669813328105570294719805302557917567023496398,
      55618341045893339257989154961235183711771677261775542139086,
      56252868730073477517004666754606784561885040564751121060802,
      56894584476211126396793937148764911733695276333794849631960,
      57543569138488182544503530867339359792600248483006991925504]
    initial.map strictPartitionCount = seed ∧ earlier.map strictPartitionCount = middle ∧
      (if withBand then bandIndices.map strictPartitionCount = bandValues else if withNext then (extension ++ [6261]).map strictPartitionCount =
        last ++ [57543569138488182544503530867339359792600248483006991925504]
       else extension.map strictPartitionCount = last) := by
  intro initial seed earlier middle extension last bandIndices bandValues
  let mask := (2^(197*6262)-1)/(2^197-1)*2^196
  let row := Nat.rec (motive := fun _ => ℕ) (2^((196+1)*6261)) (fun k b =>
    let c := b + (b >>> (197*(k+1)))
    if c &&& mask == 0 then c else 0)
  let d (j : ℕ) := (row 6261 >>> (197*(6261-j))) % 2^197
  have checked : row 6261 ≠ 0 ∧ initial.map d = seed ∧ earlier.map d = middle ∧ extension.map d = last ∧ d 6261 = 57543569138488182544503530867339359792600248483006991925504 ∧ bandIndices.map d = bandValues := by
    decide +kernel
  have digit (j : ℕ) (hj : j ≤ 6261) : strictPartitionCount j = d j :=
    strictPartitionCount_of_reverse 196 6261 (by decide) row mask (guard_mask_eq 197 6262 (2^196) (by decide)).symm
      rfl (fun _ => rfl) checked.1 j hj
  have decode (ms vs : List ℕ) (limits : ∀ i ∈ ms, i ≤ 6261) (eq : ms.map d = vs) :
      ms.map strictPartitionCount = vs :=
    (List.map_congr_left fun i hi => digit i (limits i hi)).trans eq
  have old := decode extension last (by decide +kernel) checked.2.2.2.1
  have next := (digit 6261 le_rfl).trans checked.2.2.2.2.1
  refine ⟨decode _ _ (by decide +kernel) checked.2.1,decode _ _ (by decide +kernel) checked.2.2.1,?_⟩
  cases withBand
  · cases withNext
    · exact old
    · simp only [Bool.false_eq_true,if_false,if_true,List.map_append,List.map_cons,List.map_nil,old,next]
  · exact decode bandIndices bandValues (by decide +kernel) checked.2.2.2.2.2

/-- Test each unordered pair once. For positive unequal values only the smaller
can divide the larger; equality itself fails the remainder test. -/
theorem checked_antichain (l : List ℕ) (pos : ∀ x ∈ l, 0 < x) :
    let st := l.foldr (fun a (v : List ℕ × Bool) =>
      (a::v.1,v.2 && v.1.all (fun b => if a ≤ b then b % a != 0 else a % b != 0))) ([],true)
    st.2 = true → l.Nodup ∧ ∀ x ∈ l, ∀ y ∈ l, x ≠ y → y % x ≠ 0 := by
  let step := fun (a : ℕ) (v : List ℕ × Bool) =>
    (a::v.1,v.2 && v.1.all (fun b => if a ≤ b then b % a != 0 else a % b != 0))
  have elements (t : List ℕ) : (t.foldr step ([],true)).1 = t := by
    induction t with
    | nil => rfl
    | cons a t ih => exact congrArg (a :: ·) ih
  change (l.foldr step ([],true)).2 = true → _
  induction l with
  | nil => simp
  | cons a l ih =>
    intro valid
    obtain ⟨tail,pairs⟩ := Bool.and_eq_true_iff.mp valid
    change ((l.foldr step ([],true)).1.all _) = true at pairs
    rw [elements] at pairs
    obtain ⟨nd,anti⟩ := ih (fun x hx => pos x (List.mem_cons_of_mem _ hx)) tail
    have clean (b : ℕ) (hb : b ∈ l) : b % a ≠ 0 ∧ a % b ≠ 0 := by
      have h := List.all_eq_true.mp pairs b hb
      have ha := pos a List.mem_cons_self
      have hp := pos b (List.mem_cons_of_mem _ hb)
      by_cases le : a ≤ b
      · simp only [if_pos le,bne_iff_ne] at h
        have ne : a ≠ b := by rintro rfl; simp at h
        exact ⟨h,by rw [Nat.mod_eq_of_lt (by omega : a < b)]; omega⟩
      · simp only [if_neg le,bne_iff_ne] at h
        exact ⟨by rw [Nat.mod_eq_of_lt (by omega : b < a)]; omega,h⟩
    refine ⟨List.nodup_cons.mpr ⟨fun h => (clean a h).1 (Nat.mod_self _),nd⟩,?_⟩
    intro x hx y hy ne
    rcases List.mem_cons.mp hx with ex | xt <;> rcases List.mem_cons.mp hy with ey | yt
    · exact (ne (ex.trans ey.symm)).elim
    · rw [ex]; exact (clean y yt).1
    · rw [ey]; exact (clean x xt).2
    · exact anti x xt y yt ne

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem certified_chain_choice (extended : Bool) (keep : ℕ → Prop)
    (allowed : ∀ i ∈ ([40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57,
      58, 60, 61, 62, 63, 64, 65, 66, 67, 69, 70, 71, 72, 74, 75, 76, 77, 78,
      79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 92, 93, 94, 95, 124, 133,
      142, 151, 161, 171, 181, 192, 203, 214, 225, 237, 249, 261, 274, 287, 300, 314, 328, 342,
      356, 371, 386, 401, 417, 433, 449, 466, 483, 500, 517, 535, 553, 571, 590, 608, 627, 646,
      665, 685, 705, 726, 747, 768, 789, 811, 833, 855, 878, 900, 923, 945, 969, 993, 1017, 1040,
      1065, 1090, 1116, 1142, 1168, 1194, 1221, 1248, 1274, 1302, 1330, 1358, 1386, 1415, 1444, 1473, 1503, 1533,
      1562, 1591, 1622, 1653, 1684, 1716, 1748, 1779, 1812, 1845, 1876, 1909, 1943, 1976, 2010, 2045, 2080, 2114,
      2149, 2166, 2167, 2168, 2169, 2170, 2171, 2172, 2173, 2174, 2175, 2176, 2177, 2178, 2179, 2180, 2181, 2182,
      2183, 2185, 2186, 2187, 2188, 2189, 2190, 2191, 2192, 2193, 2194, 2197, 2199, 2200] ++ (if extended then [2367, 2404, 2441, 2479, 2517, 2556, 2595, 2634, 2674, 2714, 2754, 2794, 2835, 2876,
      2917, 2957, 2998, 3040, 3082, 3125, 3168, 3211, 3255, 3299, 3343, 3387, 3432, 3477,
      3521, 3567, 3613, 3659, 3706, 3753, 3800, 3847, 3895, 3943, 3991, 4039, 4086, 4135,
      4184, 4233, 4283, 4333, 4384, 4435, 4486, 4536, 4588, 4640, 4692, 4744, 4797, 4849,
      4903, 4957, 5008, 5062, 5117, 5172, 5226, 5282, 5338, 5394, 5448, 5505, 5561, 5618,
      5676, 5734, 5792, 5850, 5909, 5968, 6027, 6086, 6146, 6200] else []) : List ℕ), keep (strictPartitionCount i))
    : ∃ seed xs : List ℕ,
    let members := xs ++ seed
  let st := xs.foldr (fun a (v : ℕ × Bool) => (v.1+a, v.2 && decide (a ≤ v.1+1-20301))) (3069181,true)
  members.Nodup ∧ (∀ s ∈ members, 1000 ≤ s ∧ keep s ∧ ∃ m : ℕ, 0 < m ∧ s = strictPartitionCount m) ∧
  (∀ x ∈ members, ∀ y ∈ members, x ≠ y → ¬ x ∣ y) ∧
  ((seed.foldr (fun a b => b ||| b <<< a) 1) >>> 20301) % 2^3048881 = 2^3048881-1 ∧ st.2 = true ∧ st.1 = (if extended then 60041801547539377118140226416919083619432043396280785479393 else 120213635240125999281329002393675834) := by
  let initial : List ℕ := [40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 60, 61, 62, 63, 64, 65, 66, 67, 69, 70, 71, 72, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 92, 93, 94, 95]
  let earlier : List ℕ := [
    124, 133, 142, 151, 161, 171, 181, 192, 203, 214, 225, 237, 249, 261, 274, 287, 300, 314, 328,
    342, 356, 371, 386, 401, 417, 433, 449, 466, 483, 500, 517, 535, 553, 571, 590, 608, 627, 646,
    665, 685, 705, 726, 747, 768, 789, 811, 833, 855, 878, 900, 923, 945, 969, 993, 1017, 1040,
    1065, 1090, 1116, 1142, 1168, 1194, 1221, 1248, 1274, 1302, 1330, 1358, 1386, 1415, 1444,
    1473, 1503, 1533, 1562, 1591, 1622, 1653, 1684, 1716, 1748, 1779, 1812, 1845, 1876, 1909,
    1943, 1976, 2010, 2045, 2080, 2114, 2149, 2166, 2167, 2168, 2169, 2170, 2171, 2172, 2173,
    2174, 2175, 2176, 2177, 2178, 2179, 2180, 2181, 2182, 2183, 2185, 2186, 2187, 2188, 2189,
    2190, 2191, 2192, 2193, 2194, 2197, 2199, 2200]
  let extension : List ℕ := [2367, 2404, 2441, 2479, 2517, 2556, 2595, 2634, 2674, 2714, 2754, 2794, 2835, 2876,
      2917, 2957, 2998, 3040, 3082, 3125, 3168, 3211, 3255, 3299, 3343, 3387, 3432, 3477,
      3521, 3567, 3613, 3659, 3706, 3753, 3800, 3847, 3895, 3943, 3991, 4039, 4086, 4135,
      4184, 4233, 4283, 4333, 4384, 4435, 4486, 4536, 4588, 4640, 4692, 4744, 4797, 4849,
      4903, 4957, 5008, 5062, 5117, 5172, 5226, 5282, 5338, 5394, 5448, 5505, 5561, 5618,
      5676, 5734, 5792, 5850, 5909, 5968, 6027, 6086, 6146, 6200]
  let ms := earlier ++ (if extended then extension else [])
  let seed := initial.map strictPartitionCount
  let as := earlier.map strictPartitionCount ++ (if extended then extension.map strictPartitionCount else [])
  let pool := as.reverse ++ seed
  let st := as.reverse.foldr (fun a (v : ℕ × Bool) => (v.1+a, v.2 && decide (a ≤ v.1+1-20301))) (3069181,true)
  let full := (extension.map strictPartitionCount).reverse ++ (earlier.map strictPartitionCount).reverse ++ seed
  have sub : pool.Sublist full := by
    cases extended
    · simpa only [pool,full,as,Bool.false_eq_true,if_false,List.append_nil,List.append_assoc] using
        List.sublist_append_right (extension.map strictPartitionCount).reverse ((earlier.map strictPartitionCount).reverse ++ seed)
    · simp only [pool,full,as,if_true,List.reverse_append,List.Sublist.refl]
  have fullCheck : (∀ x ∈ full, 1000 ≤ x) ∧
      (full.foldr (fun a (v : List ℕ × Bool) =>
        (a::v.1,v.2 && v.1.all (fun b => if a ≤ b then b % a != 0 else a % b != 0))) ([],true)).2 = true := by
    dsimp only [full,seed]
    rw [chain_coefficients.1,chain_coefficients.2.1,chain_coefficients.2.2]
    decide +kernel
  have ⟨fullNd,fullAnti⟩ := checked_antichain full (fun x hx => lt_of_lt_of_le (by decide) (fullCheck.1 x hx)) fullCheck.2
  have nodup := sub.nodup fullNd
  have terms (x : ℕ) (hx : x ∈ pool) := fullCheck.1 x (sub.subset hx)
  have anti (x : ℕ) (hx : x ∈ pool) (y : ℕ) (hy : y ∈ pool) := fullAnti x (sub.subset hx) y (sub.subset hy)
  have start : ((seed.foldr (fun a b => b ||| b <<< a) 1) >>> 20301) % 2^3048881 = 2^3048881-1 := by
    dsimp only [seed]
    rw [chain_coefficients.1]
    decide +kernel
  have check : st.2 = true ∧ st.1 = (if extended then 60041801547539377118140226416919083619432043396280785479393 else 120213635240125999281329002393675834) := by
    dsimp only [st,as]
    rw [chain_coefficients.2.1,chain_coefficients.2.2]
    cases extended <;> decide +kernel
  have lookup : ms.map strictPartitionCount = as := by cases extended <;> simp only [ms,as,List.map_append] <;> rfl
  have limits : ∀ m ∈ initial ++ ms, 0 < m := by cases extended <;> decide +kernel
  refine ⟨seed,as.reverse,nodup,?_,fun x hx y hy ne dv => anti x hx y hy ne (Nat.mod_eq_zero_of_dvd dv),
    start,check⟩
  intro x hx
  refine ⟨terms x hx,?_⟩
  have witnessed (m : ℕ) (hm : m ∈ initial ++ ms) (val : x = strictPartitionCount m) :
      keep x ∧ ∃ j : ℕ, 0 < j ∧ x = strictPartitionCount j :=
    ⟨val ▸ allowed m (by cases extended <;> exact hm),m,limits m hm,val⟩
  rcases List.mem_append.mp hx with ha | hs
  · rw [List.mem_reverse, ← lookup] at ha
    obtain ⟨m,hm,eq⟩ := List.mem_map.mp ha
    exact witnessed m (List.mem_append_right _ hm) eq.symm
  · obtain ⟨m,hm,eq⟩ := List.mem_map.mp hs
    exact witnessed m (List.mem_append_left _ hm) eq.symm

/-- The seed bit mask certifies each integer in the starting interval. -/
theorem seed_interval (seed : List ℕ) (nd : seed.Nodup)
    (start : ((seed.foldr (fun a b => b ||| b <<< a) 1) >>> 20301) % 2^3048881 = 2^3048881-1) :
    ∀ t, 20301 ≤ t → t ≤ 3069181 → ∃ T ⊆ seed.toFinset, (∑ x ∈ T, x) = t := by
  intro t hl hu
  exact (testBit_foldr seed nd t).mp (testBit_of_mask _ _ _ start t hl (by omega))

/-- Each endpoint is the initial upper bound plus every translation. -/
theorem chain_endpoint (L U : ℕ) (xs : List ℕ) :
    (xs.foldr (fun a (v : ℕ × Bool) => (v.1+a,v.2 && decide (a ≤ v.1+1-L))) (U,true)).1 =
      U + xs.sum := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    simp only [List.foldr_cons,List.sum_cons]
    rw [ih]; omega

/-- Compatible translation lists with arbitrarily large sums suffice for H1.
A list reaching a given cap leaves no tail obligations for that cap. -/
theorem H1_of_cumulative_chains (chains : ∀ cap : ℕ, ∃ seed xs : List ℕ,
    (xs ++ seed).Nodup ∧
    (∀ s ∈ xs ++ seed, 1000 ≤ s ∧ ∃ m : ℕ, 0 < m ∧ s = strictPartitionCount m) ∧
    (∀ x ∈ xs ++ seed, ∀ y ∈ xs ++ seed, x ≠ y → ¬ x ∣ y) ∧
    ((seed.foldr (fun a b => b ||| b <<< a) 1) >>> 20301) % 2^3048881 = 2^3048881-1 ∧
    (xs.foldr (fun a (v : ℕ × Bool) => (v.1+a,v.2 && decide (a ≤ v.1+1-20301))) (3069181,true)).2 = true ∧
    cap ≤ 3069181 + xs.sum) : H1 := by
  intro cap
  obtain ⟨seed,xs,nd,terms,anti,start,fit,reach⟩ := chains cap
  refine ⟨seed,xs,(xs++seed).toFinset,nd,fun s h => ⟨(terms s h).1,List.mem_toFinset.mpr h,(terms s h).2⟩,
    anti,start,fit,?_⟩
  intro n hn hc
  rw [chain_endpoint] at hn
  omega

/-- Every target in the cumulative interval has a representation using only the listed values. -/
theorem cumulative_base (seed xs : List ℕ) (keep : ℕ → Prop)
    (nd : (xs ++ seed).Nodup)
    (terms : ∀ s ∈ xs ++ seed, 1000 ≤ s ∧ keep s ∧ ∃ m : ℕ, 0 < m ∧ s = strictPartitionCount m)
    (anti : ∀ x ∈ xs ++ seed, ∀ y ∈ xs ++ seed, x ≠ y → ¬ x ∣ y)
    (start : ((seed.foldr (fun a b => b ||| b <<< a) 1) >>> 20301) % 2^3048881 = 2^3048881-1) :
    let st := xs.foldr (fun a (v : ℕ × Bool) => (v.1+a, v.2 && decide (a ≤ v.1+1-20301))) (3069181,true)
    st.2 = true → ∀ n : ℕ, 20301 ≤ n → n ≤ st.1 →
    ∃ T : Finset ℕ, (∀ s ∈ T, 1000 ≤ s ∧ keep s ∧ ∃ m : ℕ, 0 < m ∧ s = strictPartitionCount m) ∧
      (∀ x ∈ T, ∀ y ∈ T, x ≠ y → ¬ x ∣ y) ∧ (∑ s ∈ T, s) = n := by
  intro st fits n lo hi
  obtain ⟨T,sub,sum⟩ := translate_chain 20301 3069181 seed xs
    (seed_interval seed (List.nodup_append.mp nd).2.1 start) nd fits n lo hi
  have member {x : ℕ} (hx : x ∈ T) := List.mem_toFinset.mp (sub hx)
  exact ⟨T,fun x hx => terms x (member hx),fun x hx y hy => anti x (member hx) y (member hy),sum⟩

theorem bounded_base_choice (extended : Bool) (keep : ℕ → Prop)
    (allowed : ∀ i ∈ ([40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57,
      58, 60, 61, 62, 63, 64, 65, 66, 67, 69, 70, 71, 72, 74, 75, 76, 77, 78,
      79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 92, 93, 94, 95, 124, 133,
      142, 151, 161, 171, 181, 192, 203, 214, 225, 237, 249, 261, 274, 287, 300, 314, 328, 342,
      356, 371, 386, 401, 417, 433, 449, 466, 483, 500, 517, 535, 553, 571, 590, 608, 627, 646,
      665, 685, 705, 726, 747, 768, 789, 811, 833, 855, 878, 900, 923, 945, 969, 993, 1017, 1040,
      1065, 1090, 1116, 1142, 1168, 1194, 1221, 1248, 1274, 1302, 1330, 1358, 1386, 1415, 1444, 1473, 1503, 1533,
      1562, 1591, 1622, 1653, 1684, 1716, 1748, 1779, 1812, 1845, 1876, 1909, 1943, 1976, 2010, 2045, 2080, 2114,
      2149, 2166, 2167, 2168, 2169, 2170, 2171, 2172, 2173, 2174, 2175, 2176, 2177, 2178, 2179, 2180, 2181, 2182,
      2183, 2185, 2186, 2187, 2188, 2189, 2190, 2191, 2192, 2193, 2194, 2197, 2199, 2200] ++ (if extended then [2367, 2404, 2441, 2479, 2517, 2556, 2595, 2634, 2674, 2714, 2754, 2794, 2835, 2876,
      2917, 2957, 2998, 3040, 3082, 3125, 3168, 3211, 3255, 3299, 3343, 3387, 3432, 3477,
      3521, 3567, 3613, 3659, 3706, 3753, 3800, 3847, 3895, 3943, 3991, 4039, 4086, 4135,
      4184, 4233, 4283, 4333, 4384, 4435, 4486, 4536, 4588, 4640, 4692, 4744, 4797, 4849,
      4903, 4957, 5008, 5062, 5117, 5172, 5226, 5282, 5338, 5394, 5448, 5505, 5561, 5618,
      5676, 5734, 5792, 5850, 5909, 5968, 6027, 6086, 6146, 6200] else []) : List ℕ), keep (strictPartitionCount i))
    (n : ℕ) (lo : 20301 ≤ n) (hi : n ≤ (if extended then 60041801547539377118140226416919083619432043396280785479393 else 120213635240125999281329002393675834)) :
    ∃ T : Finset ℕ, (∀ s ∈ T, 1000 ≤ s ∧ keep s ∧ ∃ m : ℕ, 0 < m ∧ s = strictPartitionCount m) ∧
      (∀ x ∈ T, ∀ y ∈ T, x ≠ y → ¬ x ∣ y) ∧ (∑ s ∈ T, s) = n := by
  obtain ⟨seed,xs,nd,terms,anti,start,fits,eq⟩ := certified_chain_choice extended keep allowed
  exact cumulative_base seed xs keep nd terms anti start fits n lo (eq.symm ▸ hi)

/-- The two fixed bases are instances of the cumulative certificate. -/
theorem H1_of_fixed_bases (previous : ∀ cap : ℕ, ∃ extended : Bool,
  let seed := List.range' 40 19 ++ List.range' 60 8 ++ List.range' 69 4 ++
    List.range' 74 17 ++ List.range' 92 4
  let indices : List ℕ := seed ++ [124, 133,
      142, 151, 161, 171, 181, 192, 203, 214, 225, 237, 249, 261, 274, 287, 300, 314, 328, 342,
      356, 371, 386, 401, 417, 433, 449, 466, 483, 500, 517, 535, 553, 571, 590, 608, 627, 646,
      665, 685, 705, 726, 747, 768, 789, 811, 833, 855, 878, 900, 923, 945, 969, 993, 1017, 1040,
      1065, 1090, 1116, 1142, 1168, 1194, 1221, 1248, 1274, 1302, 1330, 1358, 1386, 1415, 1444, 1473, 1503, 1533,
      1562, 1591, 1622, 1653, 1684, 1716, 1748, 1779, 1812, 1845, 1876, 1909, 1943, 1976, 2010, 2045, 2080, 2114,
      2149] ++ List.range' 2166 18 ++ [2185, 2186, 2187, 2188, 2189, 2190, 2191, 2192, 2193, 2194, 2197, 2199, 2200] ++ (if extended then [2367, 2404, 2441, 2479, 2517, 2556, 2595, 2634, 2674, 2714, 2754, 2794, 2835, 2876,
      2917, 2957, 2998, 3040, 3082, 3125, 3168, 3211, 3255, 3299, 3343, 3387, 3432, 3477,
      3521, 3567, 3613, 3659, 3706, 3753, 3800, 3847, 3895, 3943, 3991, 4039, 4086, 4135,
      4184, 4233, 4283, 4333, 4384, 4435, 4486, 4536, 4588, 4640, 4692, 4744, 4797, 4849,
      4903, 4957, 5008, 5062, 5117, 5172, 5226, 5282, 5338, 5394, 5448, 5505, 5561, 5618,
      5676, 5734, 5792, 5850, 5909, 5968, 6027, 6086, 6146, 6200] else [])
  ∃ pool : Finset ℕ, (∀ i ∈ indices, strictPartitionCount i ∈ pool) ∧
  ∀ n : ℕ, (if extended then 60041801547539377118140226416919083619432043396280785479393 else 120213635240125999281329002393675834) < n → n ≤ cap → ∃ A : Finset ℕ, ∃ r : ℕ,
    A.Nonempty ∧ n = (∑ z ∈ A, z)+r ∧ 20301 ≤ r ∧
    (∀ z ∈ A, 1000 ≤ z ∧ z ∈ pool ∧ (∃ m : ℕ, 0 < m ∧ z = strictPartitionCount m)) ∧
    (∀ x ∈ A, ∀ y ∈ A, y < 2*x) ∧
    ∀ z ∈ A, ∀ s, 1000 ≤ s → (s ∈ pool ∧ (∃ m : ℕ, 0 < m ∧ s = strictPartitionCount m)) →
      (s = r ∨ s + 1000 ≤ r) → ¬ s ∣ z ∧ ¬ z ∣ s) : H1 := by
  intro cap
  obtain ⟨extended,pool,allowed,tail⟩ := previous cap
  obtain ⟨seed,xs,nd,terms,anti,start,fits,eq⟩ := certified_chain_choice extended (· ∈ pool) allowed
  exact ⟨seed,xs,pool,nd,terms,anti,start,fits,fun n hn => tail n (eq ▸ hn)⟩

/-- Choosing all values recovers the previous unrestricted descent condition. -/
theorem H1_of_unrestricted (tail : ∀ n : ℕ, 60041801547539377118140226416919083619432043396280785479393 < n → ∃ A : Finset ℕ, ∃ r : ℕ,
    A.Nonempty ∧ n = (∑ z ∈ A, z)+r ∧ 20301 ≤ r ∧
    (∀ z ∈ A, 1000 ≤ z ∧ (∃ m : ℕ, 0 < m ∧ z = strictPartitionCount m)) ∧
    (∀ x ∈ A, ∀ y ∈ A, y < 2*x) ∧
    ∀ z ∈ A, ∀ s, 1000 ≤ s → (∃ m : ℕ, 0 < m ∧ s = strictPartitionCount m) →
      (s = r ∨ s + 1000 ≤ r) → ¬ s ∣ z ∧ ¬ z ∣ s) : H1 := by
  apply H1_of_fixed_bases
  intro cap
  refine ⟨true, finite_support _ _ _ (fun _ => True) _ _ _ cap (fun _ _ => trivial) ?_⟩
  intro n hn _
  obtain ⟨A,r,ne,total,lo,terms,band,safe⟩ := tail n hn
  exact ⟨A,r,ne,total,lo,fun z hz => ⟨(terms z hz).1,trivial,(terms z hz).2⟩,
    band,fun z hz s hs qs => safe z hz s hs qs.2⟩

/-- A singleton in the interval for a target supplies the entire descent witness. -/
theorem H1_of_intervals (cover : ∀ n : ℕ, 60041801547539377118140226416919083619432043396280785479393 < n →
    ∃ a : ℕ, (∃ m : ℕ, 0 < m ∧ a = strictPartitionCount m) ∧ 1000 ≤ a ∧
      a+20301 ≤ n ∧ n < 2*a+1000 ∧ n ≠ 2*a ∧
      ∀ s, 1000 ≤ s → (∃ m : ℕ, 0 < m ∧ s = strictPartitionCount m) → 2*s ≤ a → ¬ s ∣ a) :
    H1 := by
  apply H1_of_unrestricted
  intro n hn
  obtain ⟨a,qa,big,lo,hi,ne,prim⟩ := cover n hn
  refine ⟨{a},n-a,singleton_nonempty _,by simp; omega,by omega,?_,?_,?_⟩
  · simpa using And.intro big qa
  · simpa using (show a < 2*a by omega)
  · simpa using primitive_step a (n-a) big prim (by omega) (by omega)

/-- Successive primitive values suffice when their unpunctured intervals touch. -/
theorem H1_of_spacing (a : ℕ → ℕ)
    (values : ∀ i, (∃ m : ℕ, 0 < m ∧ a i = strictPartitionCount m) ∧ 1000 ≤ a i ∧
      ∀ s, 1000 ≤ s → (∃ m : ℕ, 0 < m ∧ s = strictPartitionCount m) → 2*s ≤ a i → ¬ s ∣ a i)
    (start : a 0 + 20301 ≤ 60041801547539377118140226416919083619432043396280785479394)
    (spacing : ∀ i, a (i+1) + 20301 ≤ 2*a i) (unbounded : ∀ n, ∃ i, n < 2*a i) : H1 := by
  apply H1_of_unrestricted
  exact tail_of_supported_spacing _ a 1000 20301 _ (by decide)
    (fun i => ⟨(values i).2.1,(values i).1⟩) (fun i => (values i).2.2) start spacing unbounded

/-- The primitive-window assumption reported for R9 in desk note #95249 implies H1. -/
theorem H1_of_windows (windows : ∀ x : ℕ, 19290627658796608 / 2 + 1 ≤ x →
    ∃ a : ℕ, (∃ m : ℕ, 0 < m ∧ a = strictPartitionCount m) ∧ x ≤ a ∧ 2*a ≤ 3*x ∧
      ∀ s, 1000 ≤ s → (∃ m : ℕ, 0 < m ∧ s = strictPartitionCount m) → 2*s ≤ a → ¬ s ∣ a) :
    H1 := by
  apply H1_of_intervals
  intro n hn
  obtain ⟨a,qa,lo,hi,h⟩ := windows (n/2+1) (by omega)
  exact ⟨a,qa,by omega,by omega,by omega,by omega,h⟩

/-- The original support and cutoff remain available. -/
theorem bounded_base_supported (keep : ℕ → Prop)
    (allowed : ∀ i ∈ ([40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57,
      58, 60, 61, 62, 63, 64, 65, 66, 67, 69, 70, 71, 72, 74, 75, 76, 77, 78,
      79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 92, 93, 94, 95, 124, 133,
      142, 151, 161, 171, 181, 192, 203, 214, 225, 237, 249, 261, 274, 287, 300, 314, 328, 342,
      356, 371, 386, 401, 417, 433, 449, 466, 483, 500, 517, 535, 553, 571, 590, 608, 627, 646,
      665, 685, 705, 726, 747, 768, 789, 811, 833, 855, 878, 900, 923, 945, 969, 993, 1017, 1040,
      1065, 1090, 1116, 1142, 1168, 1194, 1221, 1248, 1274, 1302, 1330, 1358, 1386, 1415, 1444, 1473, 1503, 1533,
      1562, 1591, 1622, 1653, 1684, 1716, 1748, 1779, 1812, 1845, 1876, 1909, 1943, 1976, 2010, 2045, 2080, 2114,
      2149, 2166, 2167, 2168, 2169, 2170, 2171, 2172, 2173, 2174, 2175, 2176, 2177, 2178, 2179, 2180, 2181, 2182,
      2183, 2185, 2186, 2187, 2188, 2189, 2190, 2191, 2192, 2193, 2194, 2197, 2199, 2200] : List ℕ), keep (strictPartitionCount i))
    (n : ℕ) (lo : 20301 ≤ n) (hi : n ≤ 120213635240125999281329002393675834) :
    ∃ T : Finset ℕ, (∀ s ∈ T, 1000 ≤ s ∧ keep s ∧ ∃ m : ℕ, 0 < m ∧ s = strictPartitionCount m) ∧
      (∀ x ∈ T, ∀ y ∈ T, x ≠ y → ¬ x ∣ y) ∧ (∑ s ∈ T, s) = n := by
  exact bounded_base_choice false keep allowed n lo hi

/-- Forgetting the support recovers the unconditional base interval. -/
theorem bounded_base (n : ℕ) (lo : 20301 ≤ n) (hi : n ≤ 60041801547539377118140226416919083619432043396280785479393) :
    ∃ T : Finset ℕ, (∀ s ∈ T, 1000 ≤ s ∧ ∃ m : ℕ, 0 < m ∧ s = strictPartitionCount m) ∧
      (∀ x ∈ T, ∀ y ∈ T, x ≠ y → ¬ x ∣ y) ∧ (∑ s ∈ T, s) = n := by
  obtain ⟨T,good,anti,total⟩ := bounded_base_choice true (fun _ => True) (fun _ _ => trivial) n lo hi
  exact ⟨T,fun s hs => ⟨(good s hs).1,(good s hs).2.2⟩,anti,total⟩

/-- Translate a whole list against the original interval. The remainder stays
in that interval and each selected translation is used at most once. -/
theorem band_subsum (xs : List ℕ) (L U : ℕ) (nd : xs.Nodup)
    (fit : ∀ x ∈ xs, x+L ≤ U+1) :
    ∀ n, L ≤ n → n ≤ U + xs.sum → ∃ A ⊆ xs.toFinset, ∃ r, L ≤ r ∧ r ≤ U ∧
      (∑ x ∈ A, x) + r = n := by
  induction xs with
  | nil =>
    intro n lo hi
    exact ⟨∅,by simp,n,lo,by simpa using hi,by simp⟩
  | cons a xs ih =>
    intro n lo hi
    have prev := ih (List.nodup_cons.mp nd).2 (fun x hx => fit x (List.mem_cons_of_mem _ hx))
    rw [List.sum_cons] at hi
    by_cases covered : n ≤ U+xs.sum
    · obtain ⟨A,sub,r,rl,ru,total⟩ := prev n lo covered
      exact ⟨A,sub.trans (by simp),r,rl,ru,total⟩
    · have bound := fit a List.mem_cons_self
      obtain ⟨A,sub,r,rl,ru,total⟩ := prev (n-a) (by omega) (by omega)
      have fresh : a ∉ A := fun h => (List.nodup_cons.mp nd).1 (List.mem_toFinset.mp (sub h))
      refine ⟨insert a A,?_,r,rl,ru,?_⟩
      · simpa only [List.toFinset_cons] using Finset.insert_subset_insert a sub
      · rw [sum_insert fresh]; omega

/-- In a factor-two band only cross-divisibility against the original
representation needs checking. The new upper endpoint increases by the band's sum. -/
theorem cover_by_band (Q : ℕ → Prop) (xs : List ℕ) (L U b : ℕ) (nd : xs.Nodup)
    (values : ∀ x ∈ xs, Q x ∧ 0 < x ∧ b ≤ x ∧ x < 2*b ∧ x+L ≤ U+1)
    (base : ∀ r, L ≤ r → r ≤ U → ∃ T : Finset ℕ,
      (∀ s ∈ T, Q s ∧ ∀ z ∈ xs, ¬ s ∣ z ∧ ¬ z ∣ s) ∧
      (∀ x ∈ T, ∀ y ∈ T, x ≠ y → ¬ x ∣ y) ∧ (∑ x ∈ T, x) = r) :
    ∀ n, L ≤ n → n ≤ U + xs.sum → ∃ T : Finset ℕ, (∀ s ∈ T, Q s) ∧
      (∀ x ∈ T, ∀ y ∈ T, x ≠ y → ¬ x ∣ y) ∧ (∑ x ∈ T, x) = n := by
  intro n lo hi
  obtain ⟨A,sub,r,rl,ru,total⟩ := band_subsum xs L U nd (fun x h => (values x h).2.2.2.2) n lo hi
  obtain ⟨T,good,anti,ts⟩ := base r rl ru
  have mem {x : ℕ} (h : x ∈ A) := List.mem_toFinset.mp (sub h)
  have dis : Disjoint A T := disjoint_left.mpr fun x hx ht => ((good x ht).2 x (mem hx)).1 dvd_rfl
  refine ⟨A ∪ T,?_,?_,by rw [sum_union dis,ts,total]⟩
  · intro x hx
    exact (mem_union.mp hx).elim (fun h => (values x (mem h)).1) (fun h => (good x h).1)
  · intro x hx y hy ne
    rcases mem_union.mp hx with xa | xt <;> rcases mem_union.mp hy with ya | yt
    · have h := values x (mem xa)
      have k := values y (mem ya)
      exact band_nondiv k.2.1 (by omega) ne
    · exact ((good y yt).2 x (mem xa)).2
    · exact ((good x xt).2 y (mem ya)).1
    · exact anti x xt y yt ne

/-- A family of admissible lists closed under one compatible extension from
each member supplies chains reaching every cap. -/
theorem H1_of_local_extensions (seed : List ℕ) (P : List ℕ → Prop) (init : P [])
    (nd : seed.Nodup)
    (terms : ∀ s ∈ seed, 1000 ≤ s ∧ ∃ m : ℕ, 0 < m ∧ s = strictPartitionCount m)
    (anti : ∀ x ∈ seed, ∀ y ∈ seed, x ≠ y → ¬ x ∣ y)
    (start : ((seed.foldr (fun a b => b ||| b <<< a) 1) >>> 20301) % 2^3048881 = 2^3048881-1)
    (more : ∀ xs, P xs → ∃ a, P (a::xs) ∧
      (1000 ≤ a ∧ ∃ m : ℕ, 0 < m ∧ a = strictPartitionCount m) ∧
      a+20301 ≤ 3069181+xs.sum+1 ∧ ∀ b ∈ xs++seed, ¬ a ∣ b ∧ ¬ b ∣ a) : H1 := by
  apply H1_of_cumulative_chains
  intro cap
  have grow (k : ℕ) : ∃ xs : List ℕ, P xs ∧ (xs++seed).Nodup ∧
      (∀ s ∈ xs++seed, 1000 ≤ s ∧ ∃ m : ℕ, 0 < m ∧ s = strictPartitionCount m) ∧
      (∀ x ∈ xs++seed, ∀ y ∈ xs++seed, x ≠ y → ¬ x ∣ y) ∧
      (xs.foldr (fun a (v : ℕ × Bool) => (v.1+a,v.2 && decide (a ≤ v.1+1-20301))) (3069181,true)).2 = true ∧
      k ≤ xs.sum := by
    induction k with
    | zero => exact ⟨[],init,nd,terms,anti,rfl,le_rfl⟩
    | succ k ih =>
      obtain ⟨xs,p,prev,good,inc,fitted,reach⟩ := ih
      obtain ⟨a,p',ga,fit,cross⟩ := more xs p
      have fresh : a ∉ xs++seed := fun h => (cross a h).1 dvd_rfl
      refine ⟨a::xs,p',List.nodup_cons.mpr ⟨fresh,prev⟩,?_,?_,?_,?_⟩
      · intro s hs
        rcases List.mem_cons.mp hs with rfl | h
        · exact ga
        · exact good s h
      · intro x hx y hy ne
        rcases List.mem_cons.mp hx with ex | xt <;> rcases List.mem_cons.mp hy with ey | yt
        · exact (ne (ex.trans ey.symm)).elim
        · rw [ex]; exact (cross y yt).1
        · rw [ey]; exact (cross x xt).2
        · exact inc x xt y yt ne
      · simp only [List.foldr_cons,Bool.and_eq_true,decide_eq_true_eq]
        exact ⟨fitted,by rw [chain_endpoint]; omega⟩
      · simp only [List.sum_cons]
        have := ga.1
        omega
  obtain ⟨xs,_,nd',g,h,f,reach⟩ := grow cap
  exact ⟨seed,xs,nd',g,h,start,f,by omega⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Simultaneously translate by the compatible terminal band through index 6261. -/
theorem terminal_band_6261 (n : ℕ) (lo : 20301 ≤ n)
    (hi : n ≤ 2129818274671752911527586538199627191846904355313687681409069) :
    ∃ T : Finset ℕ, (∀ s ∈ T, 1000 ≤ s ∧ ∃ m : ℕ, 0 < m ∧ s = strictPartitionCount m) ∧
      (∀ x ∈ T, ∀ y ∈ T, x ≠ y → ¬ x ∣ y) ∧ (∑ s ∈ T, s) = n := by
  let ids : List ℕ := [6201, 6203, 6205, 6206, 6208, 6210, 6211, 6212, 6213, 6214, 6215, 6216, 6218, 6219, 6221, 6222, 6223, 6224,
      6225, 6227, 6228, 6229, 6230, 6231, 6233, 6234, 6235, 6236, 6237, 6238, 6239, 6240, 6241, 6242, 6243,
      6244, 6246, 6247, 6248, 6250, 6252, 6253, 6254, 6256, 6257, 6258, 6259, 6260, 6261]
  let xs := ids.map strictPartitionCount
  let b := 29090594252516759840173920707699110105324342633332184909690
  let U := 60041801547539377118140226416919083619432043396280785479393
  have eqs : ids.map strictPartitionCount = _ := (chain_coefficients false true).2.2
  have checks : xs.Nodup ∧ ∀ x ∈ xs, 1000 ≤ x ∧ 0 < x ∧ b ≤ x ∧ x < 2*b ∧ x+20301 ≤ U+1 := by
    dsimp only [xs]; rw [eqs]; decide +kernel
  have positive : ∀ i ∈ ids, 0 < i := by decide +kernel
  have endpoint : U + xs.sum = 2129818274671752911527586538199627191846904355313687681409069 := by
    dsimp only [xs]; rw [eqs]; decide +kernel
  have approved (first mid last x y z : List ℕ)
      (h₁ : first.map strictPartitionCount = x) (h₂ : mid.map strictPartitionCount = y)
      (h₃ : last.map strictPartitionCount = z)
      (ok : (x++y++z).all (fun s => xs.all (fun t => s % t != 0 && t % s != 0)) = true)
      (i : ℕ) (hi : i ∈ (first++mid)++last) (t : ℕ) (ht : t ∈ xs) :
      ¬ strictPartitionCount i ∣ t ∧ ¬ t ∣ strictPartitionCount i := by
    have h : strictPartitionCount i ∈ ((first++mid)++last).map strictPartitionCount :=
      List.mem_map.mpr ⟨i,hi,rfl⟩
    rw [List.map_append,List.map_append,h₁,h₂,h₃] at h
    have pair := List.all_eq_true.mp (List.all_eq_true.mp ok _ h) t ht
    simp only [Bool.and_eq_true,bne_iff_ne] at pair
    exact ⟨fun e => pair.2 (Nat.mod_eq_zero_of_dvd e),fun e => pair.1 (Nat.mod_eq_zero_of_dvd e)⟩
  apply cover_by_band _ xs 20301 U b checks.1 _ _ n lo (endpoint.symm ▸ hi)
  · intro x hx
    obtain ⟨m,hm,e⟩ := List.mem_map.mp hx
    exact ⟨⟨(checks.2 x hx).1,m,positive m hm,e.symm⟩,(checks.2 x hx).2⟩
  · intro r rl ru
    obtain ⟨T,g,anti,total⟩ := bounded_base_choice true
      (fun s => ∀ t ∈ xs, ¬ s ∣ t ∧ ¬ t ∣ s)
      (approved _ _ _ _ _ _ chain_coefficients.1 chain_coefficients.2.1 chain_coefficients.2.2
        (by dsimp only [xs]; rw [eqs]; decide +kernel)) r rl ru
    exact ⟨T,fun s h => ⟨⟨(g s h).1,(g s h).2.2⟩,(g s h).2.1⟩,anti,total⟩

theorem cumulative_6261 (n : ℕ) (lo : 20301 ≤ n)
    (hi : n ≤ 117585370686027559662643757284258443412032291879287777404897) :
    ∃ T : Finset ℕ, (∀ s ∈ T, 1000 ≤ s ∧ ∃ m : ℕ, 0 < m ∧ s = strictPartitionCount m) ∧
      (∀ x ∈ T, ∀ y ∈ T, x ≠ y → ¬ x ∣ y) ∧ (∑ s ∈ T, s) = n := by
  exact terminal_band_6261 n lo (by omega)

/-- Every positive target through the certified endpoint satisfies the first conjecture. -/
theorem representation_through_6261 (n : ℕ) (hn : 0 < n)
    (hi : n ≤ 2129818274671752911527586538199627191846904355313687681409069) :
    ∃ k : ℕ, ∃ terms : Fin k → ℕ,
      (∀ i, ∃ m : ℕ, 0 < m ∧ terms i = strictPartitionCount m) ∧
      (∑ i, terms i) = n ∧ (∀ i j, i ≠ j → ¬ terms i ∣ terms j) := by
  have rep : ∃ T : Finset ℕ, (∀ x ∈ T, ∃ m : ℕ, 0 < m ∧ x = strictPartitionCount m) ∧
      (∀ x ∈ T, ∀ y ∈ T, x ≠ y → ¬ x ∣ y) ∧ (∑ x ∈ T, x) = n := by
    by_cases h : n < 20301
    · exact H1_le n hn (by omega)
    · obtain ⟨T,g,anti,sum⟩ := terminal_band_6261 n (by omega) hi
      exact ⟨T,fun x hx => (g x hx).2,anti,sum⟩
  obtain ⟨T,g,anti,sum⟩ := rep
  obtain ⟨k,t,good,total,incomp⟩ := rep_of_finset T g anti
  exact ⟨k,t,good,total.trans sum,incomp⟩

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a000009.main := by
  intro localTail residual
  refine ⟨?_, fun n hn => ?_⟩
  · intro n hn
    by_cases hsmall : n < 20301
    · obtain ⟨T,g,anti,total⟩ := H1_le n hn (by omega)
      obtain ⟨k,a,ga,hs,ha⟩ := rep_of_finset T g anti
      exact ⟨k,a,ga,hs.trans total,ha⟩
    obtain ⟨seed,xs,pool,nd,terms,anti,start,fits,tail⟩ := localTail n
    obtain ⟨T,g,anti,total⟩ := descent (fun a => a ∈ pool ∧ ∃ m : ℕ, 0 < m ∧ a = strictPartitionCount m)
      1000 20301 _ n (by decide) (cumulative_base seed xs (· ∈ pool) nd terms anti start fits)
      tail n (by omega) le_rfl
    obtain ⟨k,a,ga,hs,ha⟩ := rep_of_finset T (fun x hx => (g x hx).2.2) anti
    exact ⟨k,a,ga,hs.trans total,ha⟩
  · by_cases hb : n ≤ 1000
    · exact nondiv_le n hn hb
    · exact (triple_iff _ _ _ (partitionCount_pos n) (by decide : 0 < 9338866572734899200)).mpr
        (residual n (by omega))

end OMA.R_oeis_a000009_R10
