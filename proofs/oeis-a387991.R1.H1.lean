import OMAReductions.R_oeis_a387991_R1

namespace OMA.A387991FiniteCover

open OMA.S_oeis_a387991

private noncomputable def weight (i : ℕ) : ℕ := i * prime i

-- As the prefix grows, record its prime count and the weighted value of each prime.
-- The condition involving minFac computes primality by checking small factors.
private def primeTerms : ℕ → ℕ × List ℕ
  | 0 => (0, [])
  | p + 1 =>
    let previous := primeTerms p
    if 2 ≤ p ∧ p.minFac = p then
      (previous.1 + 1, ((previous.1 + 1) * p) :: previous.2)
    else previous

private theorem primeTerms_count (p : ℕ) : (primeTerms p).1 = Nat.count Nat.Prime p := by
  induction p with
  | zero => simp [primeTerms]
  | succ p ih =>
    rw [primeTerms, Nat.count_succ]
    by_cases hp : Nat.Prime p
    · simp [hp, Nat.prime_def_minFac.mp hp, ih]
    · have hm : ¬ (2 ≤ p ∧ p.minFac = p) := fun h => hp (Nat.prime_def_minFac.mpr h)
      simp [hp, hm, ih]

private theorem primeTerms_sound (p d : ℕ) (hd : d ∈ (primeTerms p).2) :
    ∃ i : ℕ, 1 ≤ i ∧ d = weight i := by
  induction p with
  | zero => simp [primeTerms] at hd
  | succ p ih =>
    rw [primeTerms] at hd
    split at hd
    next h =>
      rw [List.mem_cons] at hd
      rcases hd with hd | hd
      · let i := (primeTerms p).1 + 1
        have hp : Nat.Prime p := Nat.prime_def_minFac.mpr h
        have hprime : prime i = p := by
          simpa only [i, prime, Nat.add_sub_cancel, primeTerms_count] using Nat.nth_count hp
        exact ⟨i, Nat.succ_pos _, by simpa only [weight, hprime] using hd⟩
      · exact ih hd
    next => exact ih hd

-- Bit n is set when n is represented. Each pass adds one weighted prime.
private def extend (m : ℕ) : List ℕ → ℕ
  | [] => 0
  | d :: ds => (m <<< d) ||| extend m ds

private theorem bit_extend (m n : ℕ) (ds : List ℕ) :
    (extend m ds).testBit n = true ↔
      ∃ d ∈ ds, ∃ k : ℕ, m.testBit k = true ∧ n = k + d := by
  induction ds with
  | nil => simp [extend]
  | cons d ds ih =>
    simp only [extend, Nat.testBit_or, Bool.or_eq_true, Nat.testBit_shiftLeft,
      Bool.and_eq_true, decide_eq_true_eq, ih, List.mem_cons]
    constructor
    · rintro (⟨hle, hb⟩ | ⟨e, he, k, hk, hn⟩)
      · exact ⟨d, Or.inl rfl, n - d, hb, by omega⟩
      · exact ⟨e, Or.inr he, k, hk, hn⟩
    · rintro ⟨e, rfl | he, k, hk, hn⟩
      · exact Or.inl ⟨by omega, by rwa [show n - e = k by omega]⟩
      · exact Or.inr ⟨e, he, k, hk, hn⟩

-- The 119 primes below 654 already suffice for the finite interval.
private def sums : ℕ → ℕ
  | 0 => 1
  | r + 1 => extend (sums r) (primeTerms 654).2

private def IsSum : ℕ → ℕ → Prop
  | 0, n => n = 0
  | r + 1, n => ∃ i k : ℕ, 1 ≤ i ∧ IsSum r k ∧ n = k + weight i

private theorem sums_sound (r n : ℕ) (h : (sums r).testBit n = true) :
    IsSum r n := by
  induction r generalizing n with
  | zero =>
    exact Nat.testBit_one_eq_true_iff_self_eq_zero.mp h
  | succ r ih =>
    change (extend (sums r) (primeTerms 654).2).testBit n = true at h
    obtain ⟨d, hd, k, hk, hn⟩ := (bit_extend _ _ _).mp h
    obtain ⟨i, hi, rfl⟩ := primeTerms_sound _ _ hd
    exact ⟨i, k, hi, ih k hk, hn⟩

private def intervalMask : ℕ := (1 <<< (200000 - 3070 + 1)) - 1

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
private theorem cover : ((sums 4 >>> 3070) &&& intervalMask) = intervalMask := by
  decide +kernel

private theorem bit_of_cover (m mask b t n : ℕ)
    (h : (m >>> b) &&& mask = mask) (ht : mask.testBit t = true) (hn : b + t = n) :
    m.testBit n = true := by
  subst n
  have hb : ((m >>> b) &&& mask).testBit t = mask.testBit t :=
    congrArg (fun x : ℕ => x.testBit t) h
  rwa [Nat.testBit_and, ht, Bool.and_true, Nat.testBit_shiftRight] at hb

private theorem low_mask_bit (s t : ℕ) (ht : t < s) :
    ((1 <<< s) - 1).testBit t = true := by
  rw [Nat.shiftLeft_eq, Nat.one_mul, Nat.testBit_two_pow_sub_one]
  exact decide_eq_true ht

private theorem covered (n : ℕ) (hlo : 3070 ≤ n) (hhi : n ≤ 200000) :
    (sums 4).testBit n = true := by
  have ht : n - 3070 < 200000 - 3070 + 1 := by omega
  have hn : 3070 + (n - 3070) = n := by omega
  exact bit_of_cover (sums 4) intervalMask 3070 (n - 3070) n cover (low_mask_bit _ _ ht) hn

private theorem compare_sum (f : ℕ → ℕ) (a b : ℕ) :
    f (min a b) + f (max a b) = f a + f b := by
  rcases le_total a b with h | h
  · rw [min_eq_left h, max_eq_right h]
  · rw [min_eq_right h, max_eq_left h, add_comm]

-- Sort four indices with two pairwise comparisons and a merge of the two pairs.
private theorem ordered (a b c d : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) (hd : 1 ≤ d) :
    ∃ i j k m : ℕ, 1 ≤ i ∧ i ≤ j ∧ j ≤ k ∧ k ≤ m ∧
      weight i + weight j + weight k + weight m = weight a + weight b + weight c + weight d := by
  let al := min a b
  let ah := max a b
  let bl := min c d
  let bh := max c d
  let i := min al bl
  let m := max ah bh
  let x := max al bl
  let y := min ah bh
  have hal : al ≤ ah := (min_le_left a b).trans (le_max_left a b)
  have hbl : bl ≤ bh := (min_le_left c d).trans (le_max_left c d)
  have hil : i ≤ al := min_le_left al bl
  have hir : i ≤ bl := min_le_right al bl
  have hlm : ah ≤ m := le_max_left ah bh
  have hrm : bh ≤ m := le_max_right ah bh
  refine ⟨i, min x y, max x y, m, le_min (le_min ha hb) (le_min hc hd), ?_, ?_, ?_, ?_⟩
  · exact le_min (hil.trans (le_max_left al bl)) (le_min (hil.trans hal) (hir.trans hbl))
  · exact (min_le_left x y).trans (le_max_left x y)
  · exact max_le (max_le (hal.trans hlm) (hbl.trans hrm)) ((min_le_left ah bh).trans hlm)
  · calc
      _ = weight i + (weight (min x y) + weight (max x y)) + weight m := by ac_rfl
      _ = (weight i + weight x) + (weight y + weight m) := by rw [compare_sum]; ac_rfl
      _ = (weight al + weight bl) + (weight ah + weight bh) := by
        change (weight (min al bl) + weight (max al bl)) +
          (weight (min ah bh) + weight (max ah bh)) = _
        rw [compare_sum, compare_sum]
      _ = (weight al + weight ah) + (weight bl + weight bh) := by ac_rfl
      _ = (weight a + weight b) + (weight c + weight d) := by
        change (weight (min a b) + weight (max a b)) + (weight (min c d) + weight (max c d)) = _
        rw [compare_sum, compare_sum]
      _ = _ := by ac_rfl

end OMA.A387991FiniteCover

open OMA.A387991FiniteCover in
theorem OMA.solution : OMA.R_oeis_a387991_R1.H1 := by
  intro n hlo hhi
  have h := sums_sound 4 n (covered n hlo hhi)
  simp only [IsSum] at h
  obtain ⟨d, n₃, hd, ⟨c, n₂, hc, ⟨b, n₁, hb, ⟨a, n₀, ha, h₀, h₁⟩, h₂⟩, h₃⟩, h₄⟩ := h
  obtain ⟨i, j, k, m, hi, hij, hjk, hkm, hsum⟩ := ordered a b c d ha hb hc hd
  refine ⟨i, j, k, m, hi, hij, hjk, hkm, ?_⟩
  change n = weight i + weight j + weight k + weight m
  rw [hsum]
  omega
