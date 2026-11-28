import OMAReductions.R_oeis_a000009_R8

/-!
# Reduction oeis-a000009.R8.H3.R1 of step oeis-a000009.R8.H3

Credit: @Jwolf52

The step R8.H3 says `2 ≤ p(n) % q(n) ≤ q(n) - 2` for `n > 1000` when `n` is pentagonal or
`p(n)` is odd (`q = strictPartitionCount`, `p = partitionCount`). This reduction proves the range
`1000 < n ≤ 4700` and splits the rest by the parity of `q(n)`.

* `H1`: `n > 4700`, `n` not pentagonal, `p(n)` odd. Then `q(n)` is even (R8,
  `strictPartitionCount_odd_iff`), so `p(n) % q(n)` is odd and the step needs only
  `p(n) % q(n) ≠ 1` and `p(n) % q(n) ≠ q(n) - 1`, that is `q(n) ∤ p(n) - 1` and `q(n) ∤ p(n) + 1`.
* `H2`: `n > 4700`, `n` pentagonal (then `q(n)` is odd): the full condition. Together with
  R8.H2.R1.H2 this is the whole pentagonal part of Sun's second conjecture.

Proved here (no `native_decide`; kernel evaluation only):
* `pack_shiftRight`, `pack_pad`, `rstep_pack`, `rfold`, `pack_one_rev`, `qshifts_spec`:
  reversed guarded tables. Entry `n` sits in slot `N - n`, so one shift-add step is
  `b + (b >>> w·s)` with automatic truncation (the idea of desk note #97196). The same shift-fold
  gives `q` (shifts `1, …, N`) and `p` (shifts `(k+1)·2^j`, from `1/(1-x^k) = Π_j (1 + x^{k·2^j})`).
  `shift_double`, `shift_congr`, `shifts_spec`, `getD_map_range` are copied from R8.H2.R1
  (PR #29526), so this file needs only R8 (#20438).
* `mod_of_rcheck`, `mod_le`: `2 ≤ p(n) % q(n) ≤ q(n) - 2` for `8 ≤ n ≤ 4700`, from one Boolean
  check on the two tables (slot widths `181` bits for `q` and `246` bits for `p`).
* `odd_case`: for even `q` and odd `p`, the two claims of `H1` give the full condition.
-/

namespace OMA.R_oeis_a000009_R8_H3_R1

open OMA.S_oeis_a000009
open OMA.R_oeis_a000009_R8 (strictPartitionCount_odd_iff
  three_le_strictPartitionCount bounded_zero bounded_succ bounded_of_le partitionCount_eq_bounded
  subsetCount_zero subsetCount_succ subsetCount_of_le strictPartitionCount_eq_subsetCount
  pack_lt pack_digit pack_append pack_replicate_zero pack_add entries_lt_of_guard)

/-- The step for non-pentagonal `n > 4700` with `p(n)` odd: `q(n) ∤ p(n) - 1`, `q(n) ∤ p(n) + 1`. -/
def H1 : Prop :=
  ∀ n : ℕ, 4700 < n → n ∉ Set.range pentagonal → partitionCount n % 2 = 1 →
    partitionCount n % strictPartitionCount n ≠ 1 ∧
      partitionCount n % strictPartitionCount n + 1 ≠ strictPartitionCount n

/-- The step for pentagonal `n > 4700`. -/
def H2 : Prop :=
  ∀ n : ℕ, 4700 < n → n ∈ Set.range pentagonal →
    2 ≤ partitionCount n % strictPartitionCount n ∧
      partitionCount n % strictPartitionCount n + 2 ≤ strictPartitionCount n

/-! ## The narrow `p`-table: `1/(1-x^k) = (1+x^k)(1+x^{2k})(1+x^{4k})⋯` (from R8.H2.R1) -/

theorem shift_double (K : ℕ) (c c' : ℕ → ℕ)
    (hc' : ∀ n, c' n = c n + if K + 1 ≤ n then c' (n - (K + 1)) else 0) :
    ∀ J n, c' n = (((List.range J).map (fun j => (K + 1) * 2 ^ j)).foldl
      (fun f s n => f n + if s ≤ n then f (n - s) else 0) c) n +
      if (K + 1) * 2 ^ J ≤ n then c' (n - (K + 1) * 2 ^ J) else 0 := by
  intro J
  induction J with
  | zero => intro n; simpa using hc' n
  | succ J ih =>
    intro n
    rw [List.range_succ, List.map_append, List.foldl_append, List.map_cons, List.map_nil,
      List.foldl_cons, List.foldl_nil]
    generalize ((List.range J).map (fun j => (K + 1) * 2 ^ j)).foldl
      (fun f s n => f n + if s ≤ n then f (n - s) else 0) c = D at ih ⊢
    have e : (K + 1) * 2 ^ (J + 1) = (K + 1) * 2 ^ J + (K + 1) * 2 ^ J := by ring
    rw [e, ih n]
    generalize (K + 1) * 2 ^ J = s at ih ⊢
    show D n + (if s ≤ n then c' (n - s) else 0) =
      (D n + if s ≤ n then D (n - s) else 0) + if s + s ≤ n then c' (n - (s + s)) else 0
    by_cases h1 : s ≤ n
    · rw [if_pos h1, if_pos h1, ih (n - s)]
      by_cases h2 : s + s ≤ n
      · rw [if_pos (by omega), if_pos h2, show n - s - s = n - (s + s) by omega]; ring
      · rw [if_neg (by omega), if_neg h2]; ring
    · rw [if_neg h1, if_neg h1, if_neg (by omega)]

theorem shift_congr (N : ℕ) (l : List ℕ) : ∀ (f g : ℕ → ℕ), (∀ n ≤ N, f n = g n) →
    ∀ n ≤ N, (l.foldl (fun f s n => f n + if s ≤ n then f (n - s) else 0) f) n =
      (l.foldl (fun f s n => f n + if s ≤ n then f (n - s) else 0) g) n := by
  induction l with
  | nil => intro f g h n hn; exact h n hn
  | cons s l ih =>
    intro f g h n hn
    rw [List.foldl_cons, List.foldl_cons]
    apply ih _ _ _ n hn
    intro m hm
    show f m + (if s ≤ m then f (m - s) else 0) = g m + if s ≤ m then g (m - s) else 0
    rw [h m hm, h (m - s) (by omega)]

/-- After the shifts for the parts `1, …, K`, slot `n ≤ N` holds the number of partitions of
`n` with parts `≤ K`. -/
theorem shifts_spec (N : ℕ) : ∀ K, ∀ n ≤ N,
    (((List.range K).flatMap (fun k => (List.range (Nat.log2 (N / (k + 1)) + 1)).map
      (fun j => (k + 1) * 2 ^ j))).foldl (fun f s n => f n + if s ≤ n then f (n - s) else 0)
      (fun n => if n = 0 then 1 else 0)) n =
      (Finset.univ.filter (fun p : n.Partition => ∀ i ∈ p.parts, i ≤ K)).card := by
  intro K
  induction K with
  | zero => intro n _; rw [bounded_zero]; simp
  | succ K ih =>
    intro n hn
    rw [List.range_succ, List.flatMap_append, List.foldl_append, List.flatMap_cons,
      List.flatMap_nil, List.append_nil]
    rw [shift_congr N _ _ (fun n => (Finset.univ.filter
      (fun p : n.Partition => ∀ i ∈ p.parts, i ≤ K)).card) ih n hn]
    have hJ : N < (K + 1) * 2 ^ (Nat.log2 (N / (K + 1)) + 1) := by
      have h := Nat.lt_log2_self (n := N / (K + 1))
      rw [Nat.div_lt_iff_lt_mul (by omega)] at h
      linarith
    have := shift_double K (fun n => (Finset.univ.filter
      (fun p : n.Partition => ∀ i ∈ p.parts, i ≤ K)).card)
      (fun n => (Finset.univ.filter (fun p : n.Partition => ∀ i ∈ p.parts, i ≤ K + 1)).card)
      (fun n => bounded_succ K n) (Nat.log2 (N / (K + 1)) + 1) n
    rw [if_neg (by omega), add_zero] at this
    exact this.symm

theorem getD_map_range (N n : ℕ) (f : ℕ → ℕ) (hn : n ≤ N) :
    ((List.range (N + 1)).map f).getD n 0 = f n := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (by omega)]; rfl

/-! ## Reversed packing: entry `n` in slot `N - n`; a shift-add step is `b + (b >>> w·s)` -/

theorem pack_shiftRight (w : ℕ) (l : List ℕ) (hl : ∀ x ∈ l, x < 2 ^ w) (s : ℕ) :
    l.foldr (fun a acc => a + 2 ^ w * acc) 0 >>> (w * s) =
      (l.drop s).foldr (fun a acc => a + 2 ^ w * acc) 0 := by
  rw [Nat.shiftRight_eq_div_pow]
  conv_lhs => rw [← List.take_append_drop s l]
  rw [pack_append, List.length_take]
  have ht : ∀ x ∈ l.take s, x < 2 ^ w := fun x hx => hl x (List.mem_of_mem_take hx)
  have hlt := pack_lt w (l.take s) ht
  rw [List.length_take] at hlt
  by_cases hs : s ≤ l.length
  · rw [min_eq_left hs] at hlt ⊢
    rw [Nat.add_mul_div_left _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt hlt, zero_add]
  · push_neg at hs
    rw [List.drop_eq_nil_of_le hs.le, min_eq_right hs.le]
    rw [min_eq_right hs.le] at hlt
    simp only [List.foldr_nil, mul_zero, add_zero]
    exact Nat.div_eq_of_lt (lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by norm_num)
      (Nat.mul_le_mul_left _ hs.le)))

theorem pack_pad (w : ℕ) (l : List ℕ) (k : ℕ) :
    (l ++ List.replicate k 0).foldr (fun a acc => a + 2 ^ w * acc) 0 =
      l.foldr (fun a acc => a + 2 ^ w * acc) 0 := by
  rw [pack_append, pack_replicate_zero, mul_zero, add_zero]

/-- One reversed shift-add step. -/
theorem rstep_pack (v N s : ℕ) (f : ℕ → ℕ) (hf : ∀ n ≤ N, f n < 2 ^ v) :
    ((List.range (N + 1)).map (fun i => f (N - i))).foldr (fun a acc => a + 2 ^ (v + 1) * acc) 0 +
      (((List.range (N + 1)).map (fun i => f (N - i))).foldr
        (fun a acc => a + 2 ^ (v + 1) * acc) 0 >>> ((v + 1) * s)) =
      ((List.range (N + 1)).map (fun i => (fun n => f n + if s ≤ n then f (n - s) else 0)
        (N - i))).foldr (fun a acc => a + 2 ^ (v + 1) * acc) 0 := by
  have hv : 2 ^ v < 2 ^ (v + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hb : ∀ x ∈ (List.range (N + 1)).map (fun i => f (N - i)), x < 2 ^ (v + 1) := by
    intro x hx
    obtain ⟨i, _, rfl⟩ := List.mem_map.1 hx
    exact lt_trans (hf _ (by omega)) hv
  rw [pack_shiftRight _ _ hb,
    ← pack_pad (v + 1) (((List.range (N + 1)).map (fun i => f (N - i))).drop s) (min s (N + 1)),
    ← pack_add _ _ _ (by simp; omega)]
  congr 1
  apply List.ext_getElem (by simp; omega)
  intro i h1 h2
  simp only [List.length_zipWith, List.length_map, List.length_range, List.length_append,
    List.length_drop, List.length_replicate] at h1
  simp only [List.getElem_zipWith, List.getElem_map, List.getElem_range, List.getElem_append,
    List.getElem_drop, List.getElem_replicate, List.length_drop, List.length_map,
    List.length_range]
  split_ifs with ha hb'
  · rw [show N - (s + i) = N - i - s by omega]
  · omega
  · omega
  · rfl

/-- The one-pass guarded reversed fold. -/
theorem rfold (v N : ℕ) : ∀ (l : List ℕ) (f : ℕ → ℕ), (∀ n ≤ N, f n < 2 ^ v) →
    l.foldl (fun C s => if ((C + (C >>> ((v + 1) * s))) &&&
      (List.replicate (N + 1) (2 ^ v)).foldr (fun a acc => a + 2 ^ (v + 1) * acc) 0) == 0
      then C + (C >>> ((v + 1) * s)) else 0)
      (((List.range (N + 1)).map (fun i => f (N - i))).foldr (fun a acc => a + 2 ^ (v + 1) * acc) 0) ≠ 0 →
    l.foldl (fun C s => if ((C + (C >>> ((v + 1) * s))) &&&
      (List.replicate (N + 1) (2 ^ v)).foldr (fun a acc => a + 2 ^ (v + 1) * acc) 0) == 0
      then C + (C >>> ((v + 1) * s)) else 0)
      (((List.range (N + 1)).map (fun i => f (N - i))).foldr (fun a acc => a + 2 ^ (v + 1) * acc) 0) =
      ((List.range (N + 1)).map (fun i =>
        (l.foldl (fun f s n => f n + if s ≤ n then f (n - s) else 0) f) (N - i))).foldr
        (fun a acc => a + 2 ^ (v + 1) * acc) 0 ∧
    ∀ n ≤ N, (l.foldl (fun f s n => f n + if s ≤ n then f (n - s) else 0) f) n < 2 ^ v := by
  have hzero : ∀ l : List ℕ, l.foldl (fun C s => if ((C + (C >>> ((v + 1) * s))) &&&
      (List.replicate (N + 1) (2 ^ v)).foldr (fun a acc => a + 2 ^ (v + 1) * acc) 0) == 0
      then C + (C >>> ((v + 1) * s)) else 0) 0 = 0 := by
    intro l
    induction l with
    | nil => rfl
    | cons s l ih => rw [List.foldl_cons]; simpa using ih
  intro l
  induction l with
  | nil => intro f hf _; exact ⟨rfl, hf⟩
  | cons s l ih =>
    intro f hf hne
    rw [List.foldl_cons] at hne ⊢
    rw [List.foldl_cons]
    rw [rstep_pack v N s f hf] at hne ⊢
    have hw1 : ∀ x ∈ (List.range (N + 1)).map (fun i =>
        (fun n => f n + if s ≤ n then f (n - s) else 0) (N - i)), x < 2 ^ (v + 1) := by
      intro x hx
      obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
      have hi' := List.mem_range.1 hi
      have := hf (N - i) (by omega)
      rw [pow_succ]
      simp only
      split_ifs
      · have := hf (N - i - s) (by omega); omega
      · omega
    by_cases hg : ((((List.range (N + 1)).map (fun i =>
        (fun n => f n + if s ≤ n then f (n - s) else 0) (N - i))).foldr
        (fun a acc => a + 2 ^ (v + 1) * acc) 0) &&& (List.replicate (N + 1) (2 ^ v)).foldr
        (fun a acc => a + 2 ^ (v + 1) * acc) 0) == 0
    · rw [if_pos hg] at hne ⊢
      have hG : (((List.range (N + 1)).map (fun i =>
          (fun n => f n + if s ≤ n then f (n - s) else 0) (N - i))).foldr
          (fun a acc => a + 2 ^ (v + 1) * acc) 0) &&& (List.replicate
          ((List.range (N + 1)).map (fun i =>
            (fun n => f n + if s ≤ n then f (n - s) else 0) (N - i))).length
          (2 ^ v)).foldr (fun a acc => a + 2 ^ (v + 1) * acc) 0 = 0 := by
        rw [List.length_map, List.length_range]; simpa using hg
      have hlt := entries_lt_of_guard v _ hw1 hG
      exact ih _ (fun n hn => by
        have := hlt _ (List.mem_map.2 ⟨N - n, List.mem_range.2 (by omega), rfl⟩)
        rwa [show N - (N - n) = n by omega] at this) hne
    · rw [if_neg hg, hzero] at hne; exact absurd rfl hne

theorem pack_one_rev (w N : ℕ) :
    ((List.range (N + 1)).map (fun i => (fun n => if n = 0 then 1 else 0) (N - i))).foldr
      (fun a acc => a + 2 ^ w * acc) 0 = 2 ^ (w * N) := by
  rw [List.range_succ, List.map_append, pack_append, List.map_singleton, List.length_map,
    List.length_range]
  have : (List.range N).map (fun i => (fun n => if n = 0 then 1 else 0) (N - i)) =
      List.replicate N 0 := by
    apply List.ext_getElem (by simp)
    intro i h1 h2
    simp only [List.getElem_map, List.getElem_range, List.getElem_replicate]
    simp only [List.length_map, List.length_range] at h1
    rw [if_neg (by omega)]
  rw [this, pack_replicate_zero]; simp

/-- The distinct-part counts are the shift-fold with the shifts `1, 2, …, K`. -/
theorem qshifts_spec : ∀ K n,
    (((List.range K).map (· + 1)).foldl (fun f s n => f n + if s ≤ n then f (n - s) else 0)
      (fun n => if n = 0 then 1 else 0)) n =
      ((Finset.Icc 1 K).powerset.filter (fun s => ∑ x ∈ s, x = n)).card := by
  intro K
  induction K with
  | zero => intro n; rw [subsetCount_zero]; rfl
  | succ K ih =>
    intro n
    rw [List.range_succ, List.map_append, List.foldl_append, List.map_singleton, List.foldl_cons,
      List.foldl_nil, subsetCount_succ K n]
    show _ + (if K + 1 ≤ n then _ else 0) = _
    rw [ih n]
    split_ifs
    · rw [ih (n - (K + 1))]
    · rfl


/-- `2 ≤ p(n) % q(n) ≤ q(n) - 2` for `8 ≤ n ≤ N` from one Boolean check on two reversed guarded
tables (slot width `u + 1` for `q`, `v + 1` for `p`; entry `n` in slot `N - n`). -/
theorem mod_of_rcheck (u v N : ℕ) (hu : 1 ≤ u) (hv : 1 ≤ v)
    (h : ((fun (P Q : ℕ) => P != 0 && Q != 0 && (List.range (N + 1)).all (fun n => n ≤ 7 ||
      (fun r d => decide (2 ≤ r) && decide (r + 2 ≤ d))
        (((P >>> ((v + 1) * (N - n))) &&& (2 ^ (v + 1) - 1)) %
          ((Q >>> ((u + 1) * (N - n))) &&& (2 ^ (u + 1) - 1)))
        ((Q >>> ((u + 1) * (N - n))) &&& (2 ^ (u + 1) - 1))))
      (((List.range N).flatMap (fun k => (List.range (Nat.log2 (N / (k + 1)) + 1)).map
        (fun j => (k + 1) * 2 ^ j))).foldl (fun C s => if ((C + (C >>> ((v + 1) * s))) &&&
        (List.replicate (N + 1) (2 ^ v)).foldr (fun a acc => a + 2 ^ (v + 1) * acc) 0) == 0
        then C + (C >>> ((v + 1) * s)) else 0) (2 ^ ((v + 1) * N)))
      (((List.range N).map (· + 1)).foldl (fun C s => if ((C + (C >>> ((u + 1) * s))) &&&
        (List.replicate (N + 1) (2 ^ u)).foldr (fun a acc => a + 2 ^ (u + 1) * acc) 0) == 0
        then C + (C >>> ((u + 1) * s)) else 0) (2 ^ ((u + 1) * N)))) = true)
    (n : ℕ) (h7 : 7 < n) (hn : n ≤ N) :
    2 ≤ partitionCount n % strictPartitionCount n ∧
      partitionCount n % strictPartitionCount n + 2 ≤ strictPartitionCount n := by
  have hδ : ∀ w, 1 ≤ w → ∀ m ≤ N, (fun m : ℕ => if m = 0 then 1 else 0) m < 2 ^ w := by
    intro w hw m _
    show (if m = 0 then 1 else 0) < 2 ^ w
    split_ifs
    · exact Nat.one_lt_two_pow (by omega)
    · exact Nat.two_pow_pos w
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, List.all_eq_true] at h
  obtain ⟨⟨hP, hQ⟩, hall⟩ := h
  rw [← pack_one_rev (v + 1) N] at hP
  rw [← pack_one_rev (u + 1) N] at hQ
  obtain ⟨hPe, hPb⟩ := rfold v N _ _ (hδ v hv) hP
  obtain ⟨hQe, hQb⟩ := rfold u N _ _ (hδ u hu) hQ
  rw [pack_one_rev] at hPe hQe
  have hb := hall n (List.mem_range.2 (by omega))
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hb
  rcases hb with hb | hb
  · omega
  rw [hPe, hQe, Nat.and_two_pow_sub_one_eq_mod, Nat.and_two_pow_sub_one_eq_mod,
    Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow] at hb
  have hwP : ∀ x ∈ (List.range (N + 1)).map (fun i =>
      (((List.range N).flatMap (fun k => (List.range (Nat.log2 (N / (k + 1)) + 1)).map
        (fun j => (k + 1) * 2 ^ j))).foldl (fun f s n => f n + if s ≤ n then f (n - s) else 0)
        (fun n => if n = 0 then 1 else 0)) (N - i)), x < 2 ^ (v + 1) := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
    exact lt_trans (hPb _ (by omega)) (Nat.pow_lt_pow_right (by norm_num) (by omega))
  have hwQ : ∀ x ∈ (List.range (N + 1)).map (fun i =>
      (((List.range N).map (· + 1)).foldl (fun f s n => f n + if s ≤ n then f (n - s) else 0)
        (fun n => if n = 0 then 1 else 0)) (N - i)), x < 2 ^ (u + 1) := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
    exact lt_trans (hQb _ (by omega)) (Nat.pow_lt_pow_right (by norm_num) (by omega))
  rw [pack_digit _ _ hwP, pack_digit _ _ hwQ, getD_map_range N (N - n) _ (by omega),
    getD_map_range N (N - n) _ (by omega), show N - (N - n) = n by omega,
    shifts_spec N N n hn, bounded_of_le n N hn, ← partitionCount_eq_bounded,
    qshifts_spec N n, subsetCount_of_le n N hn, ← strictPartitionCount_eq_subsetCount] at hb
  exact hb

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mod_le (n : ℕ) (h7 : 7 < n) (hn : n ≤ 4700) :
    2 ≤ partitionCount n % strictPartitionCount n ∧
      partitionCount n % strictPartitionCount n + 2 ≤ strictPartitionCount n :=
  mod_of_rcheck 180 245 4700 (by norm_num) (by norm_num) (by decide +kernel) n h7 hn

/-- For even `q ≥ 3` and odd `p`, the residue `p % q` is odd, so `≠ 1` and `≠ q - 1` suffice. -/
theorem odd_case (P Q : ℕ) (hQ : 3 ≤ Q) (hQ2 : Q % 2 = 0) (hP : P % 2 = 1)
    (h1 : P % Q ≠ 1) (h2 : P % Q + 1 ≠ Q) : 2 ≤ P % Q ∧ P % Q + 2 ≤ Q := by
  have hr : P % Q < Q := Nat.mod_lt _ (by omega)
  have hpar : P % Q % 2 = 1 := by
    rw [Nat.mod_mod_of_dvd P (Nat.dvd_of_mod_eq_zero hQ2)]; exact hP
  omega

theorem main : H1 → H2 → OMA.R_oeis_a000009_R8.H3 := by
  intro h1 h2 n hn hcase
  by_cases hle : n ≤ 4700
  · exact mod_le n (by omega) hle
  rw [not_le] at hle
  by_cases hpent : n ∈ Set.range pentagonal
  · exact h2 n hle hpent
  have hp : partitionCount n % 2 = 1 := hcase.resolve_left hpent
  have hq2 : strictPartitionCount n % 2 = 0 := by
    have := (strictPartitionCount_odd_iff n).not.2 hpent
    omega
  obtain ⟨a, b⟩ := h1 n hle hpent hp
  exact odd_case _ _ (three_le_strictPartitionCount n (by omega)) hq2 hp a b

end OMA.R_oeis_a000009_R8_H3_R1
