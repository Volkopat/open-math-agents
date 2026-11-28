import OMAReductions.R_oeis_a000009_R8

/-!
# Reduction oeis-a000009.R8.H2.R1 of step oeis-a000009.R8.H2

Credit: @Jwolf52

The step R8.H2 says `q(n) ∤ p(n)` for `n > 1000` when `n` is pentagonal or `p(n)` is even
(`q = strictPartitionCount`, `p = partitionCount`). This reduction proves the range
`1000 < n ≤ 3000` and the cases with a small witness prime. Two smaller steps stay open.

A prime `l` is a witness for `n` when `v_l(q(n)) > v_l(p(n))`. One witness gives `q(n) ∤ p(n)`
(`not_dvd_of_witness`). In the data for `n ≤ 10000`, primes `l ≤ 1000` settle about 91 % of the
cases. The rest behaves like random integers, so a fixed bound on the witness does not work.

* `H1`: `n > 3000`, `n` not pentagonal, `p(n)` even, and no prime `l ≤ 1000` is a witness.
* `H2`: `n > 3000`, `n` pentagonal (then `q(n)` is odd, so `l = 2` is never a witness),
  and no prime `l ≤ 1000` is a witness.

Proved here (no `native_decide`; kernel evaluation only):
* `dvd_iff_padic`, `not_dvd_of_witness`, `no_small_witness`: the prime-power form of `q ∣ p`;
* `not_dvd_mod4`: `p ≡ 2 (mod 4)` and `4 ∣ q` give `q ∤ p`;
* `conv_of_rec`, `partitionCount_eq_conv`: `p(n) = Σ_{m ≤ n/2} q(n - 2m) · p(m)`, i.e.
  `P(x) = Q(x) · P(x²)`. So `q(n) ∣ p(n)` iff `q(n)` divides `Σ_{1 ≤ m ≤ n/2} q(n - 2m) · p(m)`.
  The proof works in `ℤ⟦X⟧` by induction on the largest part;
* `shift_double`, `shift_congr`, `shifts_spec`, `gstep_pack`, `gfold`, `partitionCount_eq_gpacked`:
  a narrow guarded `p`-table. `1 / (1 - x^k) = (1 + x^k)(1 + x^{2k})(1 + x^{4k}) ⋯` gives
  shift-and-add steps only, with one guard bit per slot (201-bit slots, not `N + 1`-bit slots);
* `nondiv_of_gcheck`, `nondiv_le`: `q(n)` divides none of `p(n), p(n) ± 1` for `8 ≤ n ≤ 3000`.

The packing, guard and partition-count lemmas come from R8 (#20438).
-/

namespace OMA.R_oeis_a000009_R8_H2_R1

open OMA.S_oeis_a000009
open OMA.R_oeis_a000009_R8 (pack_shift pack_take pack_add pack_digit pack_replicate_zero
  entries_lt_of_guard bounded_zero bounded_succ bounded_of_le partitionCount_eq_bounded
  strictPartitionCount_eq_guarded subsetCount_zero subsetCount_succ subsetCount_of_le
  strictPartitionCount_eq_subsetCount partitionCount_pos)

/-- `q(n) ∤ p(n)` for non-pentagonal `n > 3000` with `p(n)` even and no witness prime `≤ 1000`. -/
def H1 : Prop :=
  ∀ n : ℕ, 3000 < n → n ∉ Set.range pentagonal → partitionCount n % 2 = 0 →
    (∀ l : ℕ, l ≤ 1000 → l.Prime →
      padicValNat l (strictPartitionCount n) ≤ padicValNat l (partitionCount n)) →
    ¬ strictPartitionCount n ∣ partitionCount n

/-- `q(n) ∤ p(n)` for pentagonal `n > 3000` with no witness prime `≤ 1000`. -/
def H2 : Prop :=
  ∀ n : ℕ, 3000 < n → n ∈ Set.range pentagonal →
    (∀ l : ℕ, l ≤ 1000 → l.Prime →
      padicValNat l (strictPartitionCount n) ≤ padicValNat l (partitionCount n)) →
    ¬ strictPartitionCount n ∣ partitionCount n

/-! ## The prime-power form of `q ∣ p` -/
theorem dvd_iff_padic {q p : ℕ} (hq : q ≠ 0) (hp : p ≠ 0) :
    q ∣ p ↔ ∀ l : ℕ, l.Prime → padicValNat l q ≤ padicValNat l p := by
  rw [← Nat.factorization_le_iff_dvd hq hp]
  constructor
  · intro h l hl
    rw [← Nat.factorization_def q hl, ← Nat.factorization_def p hl]
    exact h l
  · intro h l
    by_cases hl : l.Prime
    · rw [Nat.factorization_def q hl, Nat.factorization_def p hl]
      exact h l hl
    · rw [Nat.factorization_eq_zero_of_not_prime q hl]
      exact Nat.zero_le _

/-- S2: one witness prime settles non-divisibility. -/
theorem not_dvd_of_witness {q p l : ℕ} (hl : l.Prime) (hp : p ≠ 0)
    (h : padicValNat l p < padicValNat l q) : ¬ q ∣ p := by
  intro hd
  have hq : q ≠ 0 := by rintro rfl; exact hp (zero_dvd_iff.1 hd)
  exact absurd ((dvd_iff_padic hq hp).1 hd l hl) (not_le.2 h)

/-- S2, with a bound: if `q ∣ p` then no prime `≤ B` is a witness. -/
theorem no_small_witness {q p : ℕ} (B : ℕ) (hp : p ≠ 0) (hd : q ∣ p) :
    ∀ l ≤ B, l.Prime → padicValNat l q ≤ padicValNat l p := by
  intro l _ hl
  by_contra h
  exact not_dvd_of_witness hl hp (not_le.1 h) hd

/-- S4: `p ≡ 2 (mod 4)` and `4 ∣ q` give `q ∤ p`. -/
theorem not_dvd_mod4 {q p : ℕ} (hp : p % 4 = 2) (hq : 4 ∣ q) : ¬ q ∣ p := by
  intro hd
  have := Nat.mod_eq_zero_of_dvd (dvd_trans hq hd)
  omega


/-! ## The narrow guarded `p`-table: `1/(1-x^k) = (1+x^k)(1+x^{2k})(1+x^{4k})⋯` -/

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

theorem pack_one (w N : ℕ) :
    ((List.range (N + 1)).map (fun n => if n = 0 then 1 else 0)).foldr
      (fun a acc => a + 2 ^ w * acc) 0 = 1 := by
  rw [List.range_succ_eq_map, List.map_cons, List.map_map]
  have : ((fun n => if n = 0 then 1 else 0) ∘ Nat.succ) = fun _ => (0 : ℕ) := by
    funext i; simp
  rw [this, List.map_const', List.length_range, List.foldr_cons, pack_replicate_zero]; simp

theorem getD_map_range (N n : ℕ) (f : ℕ → ℕ) (hn : n ≤ N) :
    ((List.range (N + 1)).map f).getD n 0 = f n := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (by omega)]; rfl

/-- One shift-add step on a packed row of slot width `v + 1` with entries below `2 ^ v`. -/
theorem gstep_pack (v N s : ℕ) (f : ℕ → ℕ) (hf : ∀ n ≤ N, f n < 2 ^ v) :
    ((List.range (N + 1)).map f).foldr (fun a acc => a + 2 ^ (v + 1) * acc) 0 +
      (2 ^ ((v + 1) * s) * ((List.range (N + 1)).map f).foldr
        (fun a acc => a + 2 ^ (v + 1) * acc) 0) % 2 ^ ((v + 1) * (N + 1)) =
      ((List.range (N + 1)).map (fun n => f n + if s ≤ n then f (n - s) else 0)).foldr
        (fun a acc => a + 2 ^ (v + 1) * acc) 0 := by
  have hv : 2 ^ v < 2 ^ (v + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hb : ∀ x ∈ List.replicate s 0 ++ (List.range (N + 1)).map f, x < 2 ^ (v + 1) := by
    intro x hx
    rcases List.mem_append.1 hx with h | h
    · rw [List.eq_of_mem_replicate h]; exact Nat.two_pow_pos _
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.1 h
      exact lt_trans (hf i (by have := List.mem_range.1 hi; omega)) hv
  rw [← pack_shift, ← pack_take _ _ _ hb, ← pack_add _ _ _ (by simp)]
  congr 1
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.length_zipWith, List.length_map, List.length_range, List.length_take,
    List.length_append, List.length_replicate] at h1
  rw [List.getElem_zipWith, List.getElem_map, List.getElem_map, List.getElem_range,
    List.getElem_take, List.getElem_append]
  simp only [List.length_replicate, List.getElem_replicate]
  split_ifs with ha hb' <;> first | omega | rfl | simp [List.getElem_map, List.getElem_range]

/-- The one-pass guarded fold: if the result is not `0`, every guard passed, and the packed
row is exact with entries below `2 ^ v`. -/
theorem gfold (v N : ℕ) : ∀ (l : List ℕ) (f : ℕ → ℕ), (∀ n ≤ N, f n < 2 ^ v) →
    l.foldl (fun C s => if ((C + (2 ^ ((v + 1) * s) * C) % 2 ^ ((v + 1) * (N + 1))) &&&
      (List.replicate (N + 1) (2 ^ v)).foldr (fun a acc => a + 2 ^ (v + 1) * acc) 0) == 0
      then C + (2 ^ ((v + 1) * s) * C) % 2 ^ ((v + 1) * (N + 1)) else 0)
      (((List.range (N + 1)).map f).foldr (fun a acc => a + 2 ^ (v + 1) * acc) 0) ≠ 0 →
    l.foldl (fun C s => if ((C + (2 ^ ((v + 1) * s) * C) % 2 ^ ((v + 1) * (N + 1))) &&&
      (List.replicate (N + 1) (2 ^ v)).foldr (fun a acc => a + 2 ^ (v + 1) * acc) 0) == 0
      then C + (2 ^ ((v + 1) * s) * C) % 2 ^ ((v + 1) * (N + 1)) else 0)
      (((List.range (N + 1)).map f).foldr (fun a acc => a + 2 ^ (v + 1) * acc) 0) =
      ((List.range (N + 1)).map
        (l.foldl (fun f s n => f n + if s ≤ n then f (n - s) else 0) f)).foldr
        (fun a acc => a + 2 ^ (v + 1) * acc) 0 ∧
    ∀ n ≤ N, (l.foldl (fun f s n => f n + if s ≤ n then f (n - s) else 0) f) n < 2 ^ v := by
  have hzero : ∀ l : List ℕ, l.foldl (fun C s => if ((C + (2 ^ ((v + 1) * s) * C) %
      2 ^ ((v + 1) * (N + 1))) &&& (List.replicate (N + 1) (2 ^ v)).foldr
      (fun a acc => a + 2 ^ (v + 1) * acc) 0) == 0
      then C + (2 ^ ((v + 1) * s) * C) % 2 ^ ((v + 1) * (N + 1)) else 0) 0 = 0 := by
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
    rw [gstep_pack v N s f hf] at hne ⊢
    have hw1 : ∀ x ∈ (List.range (N + 1)).map (fun n => f n + if s ≤ n then f (n - s) else 0),
        x < 2 ^ (v + 1) := by
      intro x hx
      obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
      have hi' := List.mem_range.1 hi
      have := hf i (by omega)
      rw [pow_succ]
      split_ifs
      · have := hf (i - s) (by omega); omega
      · omega
    by_cases hg : ((((List.range (N + 1)).map (fun n => f n + if s ≤ n then f (n - s) else 0)).foldr
        (fun a acc => a + 2 ^ (v + 1) * acc) 0) &&& (List.replicate (N + 1) (2 ^ v)).foldr
        (fun a acc => a + 2 ^ (v + 1) * acc) 0) == 0
    · rw [if_pos hg] at hne ⊢
      have hG : (((List.range (N + 1)).map (fun n => f n + if s ≤ n then f (n - s) else 0)).foldr
          (fun a acc => a + 2 ^ (v + 1) * acc) 0) &&& (List.replicate
          ((List.range (N + 1)).map (fun n => f n + if s ≤ n then f (n - s) else 0)).length
          (2 ^ v)).foldr (fun a acc => a + 2 ^ (v + 1) * acc) 0 = 0 := by
        rw [List.length_map, List.length_range]; simpa using hg
      have hlt := entries_lt_of_guard v _ hw1 hG
      exact ih _ (fun n hn => hlt _ (List.mem_map.2 ⟨n, List.mem_range.2 (by omega), rfl⟩)) hne
    · rw [if_neg hg, hzero] at hne; exact absurd rfl hne

/-- `p(n)` is slot `n` of the narrow guarded table, when the fold result is not `0`. -/
theorem partitionCount_eq_gpacked (v N n : ℕ) (hv : 1 ≤ v) (hn : n ≤ N)
    (hN : ((List.range N).flatMap (fun k => (List.range (Nat.log2 (N / (k + 1)) + 1)).map
      (fun j => (k + 1) * 2 ^ j))).foldl (fun C s => if ((C + (2 ^ ((v + 1) * s) * C) %
      2 ^ ((v + 1) * (N + 1))) &&& (List.replicate (N + 1) (2 ^ v)).foldr
      (fun a acc => a + 2 ^ (v + 1) * acc) 0) == 0
      then C + (2 ^ ((v + 1) * s) * C) % 2 ^ ((v + 1) * (N + 1)) else 0) 1 ≠ 0) :
    partitionCount n = ((((List.range N).flatMap (fun k => (List.range (Nat.log2 (N / (k + 1)) + 1)).map
      (fun j => (k + 1) * 2 ^ j))).foldl (fun C s => if ((C + (2 ^ ((v + 1) * s) * C) %
      2 ^ ((v + 1) * (N + 1))) &&& (List.replicate (N + 1) (2 ^ v)).foldr
      (fun a acc => a + 2 ^ (v + 1) * acc) 0) == 0
      then C + (2 ^ ((v + 1) * s) * C) % 2 ^ ((v + 1) * (N + 1)) else 0) 1) /
        2 ^ ((v + 1) * n)) % 2 ^ (v + 1) := by
  have h0 : ∀ m ≤ N, (fun m : ℕ => if m = 0 then 1 else 0) m < 2 ^ v := by
    intro m _
    show (if m = 0 then 1 else 0) < 2 ^ v
    split_ifs
    · exact Nat.one_lt_two_pow (by omega)
    · exact Nat.two_pow_pos v
  have hP1 := pack_one (v + 1) N
  obtain ⟨hP, hb⟩ := gfold v N _ _ h0 (by rw [hP1]; exact hN)
  rw [hP1] at hP
  have hbound : ∀ x ∈ (List.range (N + 1)).map (((List.range N).flatMap (fun k =>
      (List.range (Nat.log2 (N / (k + 1)) + 1)).map (fun j => (k + 1) * 2 ^ j))).foldl
      (fun f s n => f n + if s ≤ n then f (n - s) else 0) (fun n => if n = 0 then 1 else 0)),
      x < 2 ^ (v + 1) := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
    exact lt_trans (hb i (by have := List.mem_range.1 hi; omega))
      (Nat.pow_lt_pow_right (by norm_num) (by omega))
  rw [hP, pack_digit (v + 1) _ hbound n, getD_map_range N n _ hn, shifts_spec N N n hn,
    bounded_of_le n N hn, ← partitionCount_eq_bounded]

/-- The finite range `8 ≤ n ≤ N` from one Boolean check on the two narrow guarded tables. -/
theorem nondiv_of_gcheck (v N : ℕ) (hv : 1 ≤ v)
    (h : ((fun (P Q : ℕ) => P != 0 && Q != 0 && (List.range (N + 1)).all (fun n => n ≤ 7 ||
      ((P / 2 ^ ((v + 1) * n)) % 2 ^ (v + 1) % ((Q / 2 ^ ((v + 1) * n)) % 2 ^ (v + 1)) != 0 &&
       ((P / 2 ^ ((v + 1) * n)) % 2 ^ (v + 1) - 1) % ((Q / 2 ^ ((v + 1) * n)) % 2 ^ (v + 1)) != 0 &&
       ((P / 2 ^ ((v + 1) * n)) % 2 ^ (v + 1) + 1) % ((Q / 2 ^ ((v + 1) * n)) % 2 ^ (v + 1)) != 0)))
      (((List.range N).flatMap (fun k => (List.range (Nat.log2 (N / (k + 1)) + 1)).map
      (fun j => (k + 1) * 2 ^ j))).foldl (fun C s => if ((C + (2 ^ ((v + 1) * s) * C) %
      2 ^ ((v + 1) * (N + 1))) &&& (List.replicate (N + 1) (2 ^ v)).foldr
      (fun a acc => a + 2 ^ (v + 1) * acc) 0) == 0
      then C + (2 ^ ((v + 1) * s) * C) % 2 ^ ((v + 1) * (N + 1)) else 0) 1)
      (Nat.rec (motive := fun _ => ℕ) 1 (fun K B => if ((B + (2 ^ ((v + 1) * (K + 1)) * B) % 2 ^ ((v + 1) * (N + 1))) &&& (List.replicate (N + 1) (2 ^ v)).foldr (fun a acc => a + 2 ^ (v + 1) * acc) 0) == 0 then B + (2 ^ ((v + 1) * (K + 1)) * B) % 2 ^ ((v + 1) * (N + 1)) else 0) N)) = true)
    (n : ℕ) (h7 : 7 < n) (hn : n ≤ N) :
    ¬ strictPartitionCount n ∣ partitionCount n ∧
    ¬ strictPartitionCount n ∣ partitionCount n - 1 ∧
    ¬ strictPartitionCount n ∣ partitionCount n + 1 := by
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, List.all_eq_true] at h
  obtain ⟨⟨hP, hQ⟩, hall⟩ := h
  have hb := hall n (List.mem_range.2 (by omega))
  rw [← strictPartitionCount_eq_guarded v N n hv hn hQ,
    ← partitionCount_eq_gpacked v N n hv hn hP] at hb
  simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, bne_iff_ne, ne_eq] at hb
  rcases hb with hb | hb
  · omega
  · simp only [Nat.dvd_iff_mod_eq_zero]
    exact ⟨hb.1.1, hb.1.2, hb.2⟩

/-! ## `P(x) = Q(x) · P(x²)` -/

open PowerSeries in

/-- S5, abstract form. `c K n` counts partitions of `n` with parts `≤ K`, `t K n` counts
distinct-part partitions of `n` with parts `≤ K` (only the recursions are used). Then
`c K n = Σ_{i + j = n} t K i · [j even] c K (j / 2)`, i.e. `P_K(x) = Q_K(x) · P_K(x²)`. -/
theorem conv_of_rec (c t : ℕ → ℕ → ℕ)
    (hc0 : ∀ n, c 0 n = if n = 0 then 1 else 0)
    (hcs : ∀ K n, c (K + 1) n = c K n + if K + 1 ≤ n then c (K + 1) (n - (K + 1)) else 0)
    (ht0 : ∀ n, t 0 n = if n = 0 then 1 else 0)
    (hts : ∀ K n, t (K + 1) n = t K n + if K + 1 ≤ n then t K (n - (K + 1)) else 0) :
    ∀ K n, c K n = ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n,
      t K ij.1 * (if Even ij.2 then c K (ij.2 / 2) else 0) := by
  -- the three power series over `ℤ`
  have hC : ∀ K, mk (fun n => (c (K + 1) n : ℤ)) * (1 - X ^ (K + 1)) =
      mk (fun n => (c K n : ℤ)) := by
    intro K
    ext n
    simp only [mul_sub, mul_one, map_sub, coeff_mul_X_pow', coeff_mk]
    rw [hcs K n]
    split_ifs with h
    · push_cast; ring
    · push_cast; ring
  have hT : ∀ K, mk (fun n => (t (K + 1) n : ℤ)) =
      mk (fun n => (t K n : ℤ)) * (1 + X ^ (K + 1)) := by
    intro K
    ext n
    simp only [mul_add, mul_one, map_add, coeff_mul_X_pow', coeff_mk]
    rw [hts K n]
    split_ifs with h
    · push_cast; ring
    · push_cast; ring
  have hE : ∀ K, mk (fun n => if Even n then (c (K + 1) (n / 2) : ℤ) else 0) *
      (1 - X ^ (2 * (K + 1))) = mk (fun n => if Even n then (c K (n / 2) : ℤ) else 0) := by
    intro K
    ext n
    simp only [mul_sub, mul_one, map_sub, coeff_mul_X_pow', coeff_mk]
    by_cases he : Even n
    · rw [if_pos he, if_pos he, hcs K (n / 2)]
      obtain ⟨r, hr⟩ := he
      by_cases h1 : 2 * (K + 1) ≤ n
      · rw [if_pos h1, if_pos (show Even (n - 2 * (K + 1)) from ⟨r - (K + 1), by omega⟩),
          if_pos (show K + 1 ≤ n / 2 by omega),
          show (n - 2 * (K + 1)) / 2 = n / 2 - (K + 1) by omega]
        push_cast; ring
      · rw [if_neg h1, if_neg (show ¬ K + 1 ≤ n / 2 by omega)]
        push_cast; ring
    · rw [if_neg he, if_neg he]
      by_cases h1 : 2 * (K + 1) ≤ n
      · rw [if_pos h1, if_neg]
        · ring
        · rintro ⟨r, hr⟩; exact he ⟨r + (K + 1), by omega⟩
      · rw [if_neg h1]; ring
  have hne : ∀ K, (1 - X ^ (K + 1) : ℤ⟦X⟧) ≠ 0 := by
    intro K h
    have := congrArg (coeff 0) h
    rw [map_sub, coeff_one, coeff_X_pow] at this
    simp at this
  have hmain : ∀ K, mk (fun n => (c K n : ℤ)) = mk (fun n => (t K n : ℤ)) *
      mk (fun n => if Even n then (c K (n / 2) : ℤ) else 0) := by
    intro K
    induction K with
    | zero =>
      have h1 : mk (fun n => (c 0 n : ℤ)) = 1 := by
        ext n; rw [coeff_mk, coeff_one, hc0]; split_ifs <;> simp
      have h2 : mk (fun n => (t 0 n : ℤ)) = 1 := by
        ext n; rw [coeff_mk, coeff_one, ht0]; split_ifs <;> simp
      have h3 : mk (fun n => if Even n then (c 0 (n / 2) : ℤ) else 0) = 1 := by
        ext n
        rw [coeff_mk, coeff_one]
        by_cases h : n = 0
        · subst h; simp [hc0]
        · rw [if_neg h]
          split_ifs with he
          · obtain ⟨r, hr⟩ := he
            rw [hc0, if_neg (by omega)]; simp
          · rfl
      rw [h1, h2, h3, mul_one]
    | succ K ih =>
      apply mul_right_cancel₀ (hne K)
      rw [hC K, ih, hT K]
      have e2 : (X : ℤ⟦X⟧) ^ (2 * (K + 1)) = (X ^ (K + 1)) ^ 2 := by rw [← pow_mul, mul_comm]
      calc mk (fun n => (t K n : ℤ)) * mk (fun n => if Even n then (c K (n / 2) : ℤ) else 0)
          = mk (fun n => (t K n : ℤ)) * (mk (fun n => if Even n then (c (K + 1) (n / 2) : ℤ)
              else 0) * (1 - X ^ (2 * (K + 1)))) := by rw [hE K]
        _ = mk (fun n => (t K n : ℤ)) * (1 + X ^ (K + 1)) *
              mk (fun n => if Even n then (c (K + 1) (n / 2) : ℤ) else 0) * (1 - X ^ (K + 1)) := by
            rw [e2]; ring
  intro K n
  have := congrArg (coeff n) (hmain K)
  rw [coeff_mk, coeff_mul] at this
  simp only [coeff_mk] at this
  have h' : ((∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n,
      t K ij.1 * (if Even ij.2 then c K (ij.2 / 2) else 0) : ℕ) : ℤ) = (c K n : ℤ) := by
    rw [this]; push_cast
    refine Finset.sum_congr rfl (fun ij _ => ?_)
    split_ifs <;> simp
  exact_mod_cast h'.symm


theorem sum_range_even (F : ℕ → ℕ) : ∀ n, (∑ k ∈ Finset.range (n + 1), if Even k then F k else 0) =
    ∑ m ∈ Finset.range (n / 2 + 1), F (2 * m) := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    rcases Nat.even_or_odd n with ⟨r, hr⟩ | ⟨r, hr⟩
    · rw [if_neg (by rintro ⟨s, hs⟩; omega), add_zero,
        show (n + 1) / 2 = n / 2 by omega]
    · rw [if_pos ⟨r + 1, by omega⟩, show (n + 1) / 2 + 1 = n / 2 + 1 + 1 by omega,
        Finset.sum_range_succ (fun m => F (2 * m)) (n / 2 + 1),
        show 2 * (n / 2 + 1) = n + 1 by omega]

/-- S5: `p(n) = Σ_{m ≤ n/2} q(n - 2m) · p(m)`, from `P(x) = Q(x) · P(x²)`. -/
theorem partitionCount_eq_conv (n : ℕ) :
    partitionCount n = ∑ m ∈ Finset.range (n / 2 + 1),
      strictPartitionCount (n - 2 * m) * partitionCount m := by
  have key := conv_of_rec
    (fun K n => (Finset.univ.filter (fun p : n.Partition => ∀ i ∈ p.parts, i ≤ K)).card)
    (fun K n => ((Finset.Icc 1 K).powerset.filter (fun s => ∑ x ∈ s, x = n)).card)
    bounded_zero bounded_succ subsetCount_zero subsetCount_succ n n
  rw [partitionCount_eq_bounded, ← bounded_of_le n n le_rfl, key,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, ← Finset.sum_range_reflect]
  calc _ = ∑ k ∈ Finset.range (n + 1),
        (if Even k then strictPartitionCount (n - k) * partitionCount (k / 2) else 0) := by
        refine Finset.sum_congr rfl (fun k hk => ?_)
        have hk' := Finset.mem_range.1 hk
        simp only [Nat.succ_eq_add_one]
        rw [show n + 1 - 1 - k = n - k by omega, show n - (n - k) = k by omega]
        split_ifs with he
        · rw [subsetCount_of_le (n - k) n (by omega), ← strictPartitionCount_eq_subsetCount,
            bounded_of_le (k / 2) n (by omega), ← partitionCount_eq_bounded]
        · simp
    _ = ∑ m ∈ Finset.range (n / 2 + 1),
        strictPartitionCount (n - 2 * m) * partitionCount (2 * m / 2) :=
        sum_range_even (fun j => strictPartitionCount (n - j) * partitionCount (j / 2)) n
    _ = _ := by
        refine Finset.sum_congr rfl (fun m _ => ?_)
        rw [show 2 * m / 2 = m by omega]

/-! ## The finite range `8 ≤ n ≤ 3000`, checked by the kernel -/

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nondiv_le (n : ℕ) (h7 : 7 < n) (hn : n ≤ 3000) :
    ¬ strictPartitionCount n ∣ partitionCount n ∧
    ¬ strictPartitionCount n ∣ partitionCount n - 1 ∧
    ¬ strictPartitionCount n ∣ partitionCount n + 1 :=
  nondiv_of_gcheck 200 3000 (by norm_num) (by decide +kernel) n h7 hn

theorem main : H1 → H2 → OMA.R_oeis_a000009_R8.H2 := by
  intro h1 h2 n hn hcase
  by_cases hb : n ≤ 3000
  · exact (nondiv_le n (by omega) hb).1
  · intro hd
    have hp : partitionCount n ≠ 0 := by have := partitionCount_pos n; omega
    have hw := no_small_witness 1000 hp hd
    by_cases hpent : n ∈ Set.range pentagonal
    · exact h2 n (by omega) hpent hw hd
    · have heven : partitionCount n % 2 = 0 := hcase.resolve_left hpent
      exact h1 n (by omega) hpent heven hw hd

end OMA.R_oeis_a000009_R8_H2_R1
