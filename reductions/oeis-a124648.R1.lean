import OMAStatements.S_oeis_a124648

-- Reduction oeis-a124648.R1 of A124648.
-- Credit: @yuka30240

namespace OMA.R_oeis_a124648_R1

-- Count the six-power candidates in the band from 100^k up to 100^(k+1).
def H1 : Prop :=
  ∃ K : ℕ, ∀ k ≥ K,
    let bases := (Finset.Ico (100 ^ k) (100 ^ (k + 1))).filter fun n =>
      ∀ i : Fin 6, 0 ∉ Nat.digits 10 (n ^ (i.val + 1))
    2 * bases.card < 2 ^ k

-- c j counts candidates whose seventh power passes j blocks of seven low digits.
-- A block has 9^7 zeroless strings out of 10^7, less than half. Measure only
-- the excess over halving at each stage, with natural subtraction discarding deficits.
def H2 : Prop :=
  ∃ K : ℕ, ∀ k ≥ K,
    let bases := (Finset.Ico (100 ^ k) (100 ^ (k + 1))).filter fun n =>
      ∀ i : Fin 6, 0 ∉ Nat.digits 10 (n ^ (i.val + 1))
    let c := fun j : ℕ => (bases.filter fun n =>
      ∀ t : Fin (7 * j), n ^ 7 / 10 ^ t.val % 10 ≠ 0).card
    2 * (∑ j ∈ Finset.range k, 2 ^ j * (2 * c (j + 1) - c j)) ≤ 2 ^ k

lemma low_digits_succ (d n : ℕ) :
    (∀ t : Fin (d + 1), n / 10 ^ t.val % 10 ≠ 0) ↔
      n % 10 ≠ 0 ∧ ∀ t : Fin d, n / 10 / 10 ^ t.val % 10 ≠ 0 := by
  constructor
  · intro h
    refine ⟨by simpa using h 0, fun t => ?_⟩
    simpa only [Fin.val_succ, pow_succ', Nat.div_div_eq_div_mul] using h t.succ
  · rintro ⟨h0, hs⟩ t
    refine Fin.cases (by simpa using h0) (fun i => ?_) t
    simpa only [Fin.val_succ, pow_succ', Nat.div_div_eq_div_mul] using hs i

lemma count_zeroless_blocks (d : ℕ) :
    ((Finset.range (10 ^ d)).filter fun n =>
      ∀ t : Fin d, n / 10 ^ t.val % 10 ≠ 0).card = 9 ^ d := by
  induction d with
  | zero => simp
  | succ d ih =>
    let tails := (Finset.range (10 ^ d)).filter fun n =>
      ∀ t : Fin d, n / 10 ^ t.val % 10 ≠ 0
    rw [show 9 ^ (d + 1) = 9 * tails.card by rw [pow_succ', ← ih]]
    rw [show 9 = (Finset.Icc 1 9).card by decide, ← Finset.card_product]
    refine Finset.card_bij' (fun n _ => (n % 10, n / 10)) (fun p _ => p.1 + 10 * p.2) ?_ ?_ ?_ ?_
    · intro n hn
      obtain ⟨hb, hp⟩ := Finset.mem_filter.mp hn
      obtain ⟨h0, hs⟩ := (low_digits_succ d n).mp hp
      simp only [Finset.mem_product, Finset.mem_Icc, tails, Finset.mem_filter, Finset.mem_range]
      refine ⟨⟨Nat.pos_of_ne_zero h0, by omega⟩, ?_, hs⟩
      exact (Nat.div_lt_iff_lt_mul (by decide : 0 < 10)).2
        (by simpa only [pow_succ, Finset.mem_range] using hb)
    · rintro ⟨a, b⟩ hp
      simp only [Finset.mem_product, Finset.mem_Icc, tails, Finset.mem_filter, Finset.mem_range] at hp
      obtain ⟨⟨ha1, ha9⟩, hbound, htail⟩ := hp
      have ha10 : a < 10 := by omega
      have hm : (a + 10 * b) % 10 = a := by simp [Nat.mod_eq_of_lt ha10]
      have hq : (a + 10 * b) / 10 = b := by simp [Nat.add_mul_div_left, Nat.div_eq_of_lt ha10]
      simp only [Finset.mem_filter, Finset.mem_range]
      refine ⟨?_, (low_digits_succ d (a + 10 * b)).mpr ?_⟩
      · rw [pow_succ]
        omega
      · rw [hm, hq]
        exact ⟨by omega, htail⟩
    · intro n _
      exact Nat.mod_add_div n 10
    · rintro ⟨a, b⟩ hp
      have ha := (Finset.mem_Icc.mp (Finset.mem_product.mp hp).1).2
      change a ≤ 9 at ha
      have ha10 : a < 10 := by omega
      simp [Nat.mod_eq_of_lt ha10, Nat.add_mul_div_left, Nat.div_eq_of_lt ha10]

-- For B divisible by a full block, the quadratic and higher increments in
-- the binomial expansion disappear modulo B * 10^7.
lemma seventh_block_lift (B r t : ℕ) (hB : 10 ^ 7 ∣ B) (hpos : 0 < B) :
    ((r + B * t) ^ 7 / B) % 10 ^ 7 =
      (r ^ 7 / B + 7 * r ^ 6 * t) % 10 ^ 7 := by
  let rest := 21 * r ^ 5 * t ^ 2 + 35 * r ^ 4 * B * t ^ 3 +
    35 * r ^ 3 * B ^ 2 * t ^ 4 + 21 * r ^ 2 * B ^ 3 * t ^ 5 +
    7 * r * B ^ 4 * t ^ 6 + B ^ 5 * t ^ 7
  have expand : (r + B * t) ^ 7 = r ^ 7 + B * (7 * r ^ 6 * t + B * rest) := by
    dsimp [rest]
    ring
  rw [expand, Nat.add_mul_div_left _ _ hpos, ← add_assoc]
  obtain ⟨s, hs⟩ := hB
  rw [show B * rest = 10 ^ 7 * (s * rest) by rw [← mul_assoc, ← hs],
    Nat.add_mul_mod_self_left]

lemma seventh_block_perm (B r : ℕ) (hB : 10 ^ 7 ∣ B) (hpos : 0 < B) (hr : r.Coprime 10) :
    Function.Bijective (fun t : ZMod (10 ^ 7) =>
      (((r + B * t.val) ^ 7 / B : ℕ) : ZMod (10 ^ 7))) := by
  have hu : IsUnit ((7 * r ^ 6 : ℕ) : ZMod (10 ^ 7)) :=
    (ZMod.isUnit_iff_coprime _ _).2
      (((by decide : Nat.Coprime 7 10).mul_left (hr.pow_left 6)).pow_right 7)
  obtain ⟨u, hu⟩ := hu
  let e := u.mulLeft.trans (Equiv.addLeft ((r ^ 7 / B : ℕ) : ZMod (10 ^ 7)))
  have he (t : ZMod (10 ^ 7)) :
      (((r + B * t.val) ^ 7 / B : ℕ) : ZMod (10 ^ 7)) = e t := by
    change _ = ((r ^ 7 / B : ℕ) : ZMod (10 ^ 7)) + (u : ZMod (10 ^ 7)) * t
    rw [hu]
    push_cast
    simpa only [ZMod.natCast_zmod_val, Nat.cast_add, Nat.cast_mul, Nat.cast_pow,
      Nat.cast_ofNat] using
      (ZMod.natCast_eq_natCast_iff _ _ (10 ^ 7)).2 (seventh_block_lift B r t.val hB hpos)
  simpa only [funext he] using e.bijective

-- Count the unconditioned block lifts above a residue coprime to ten.
lemma count_seventh_block_lifts (B r : ℕ) (hB : 10 ^ 7 ∣ B) (hpos : 0 < B)
    (hr : r.Coprime 10) :
    (Finset.univ.filter fun t : ZMod (10 ^ 7) =>
      ∀ i : Fin 7, ((r + B * t.val) ^ 7 / B % 10 ^ 7) / 10 ^ i.val % 10 ≠ 0).card = 9 ^ 7 := by
  let good := fun n : ℕ => ∀ i : Fin 7, n / 10 ^ i.val % 10 ≠ 0
  let f := fun t : ZMod (10 ^ 7) => (((r + B * t.val) ^ 7 / B : ℕ) : ZMod (10 ^ 7))
  calc
    _ = (Finset.univ.filter fun x : ZMod (10 ^ 7) => good x.val).card := by
      apply Finset.card_bijective f (seventh_block_perm B r hB hpos hr)
      intro t
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, f, good, ZMod.val_natCast]
    _ = ((Finset.range (10 ^ 7)).filter good).card := by
      refine Finset.card_bij' (fun x _ => x.val) (fun n _ => (n : ZMod (10 ^ 7))) ?_ ?_ ?_ ?_
      · intro x hx
        exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr x.val_lt, (Finset.mem_filter.mp hx).2⟩
      · intro n hn
        obtain ⟨hb, hg⟩ := Finset.mem_filter.mp hn
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
        simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt (Finset.mem_range.mp hb)] using hg
      · intro x _
        exact ZMod.natCast_zmod_val x
      · intro n hn
        exact (ZMod.val_natCast _ _).trans (Nat.mod_eq_of_lt (Finset.mem_range.mp (Finset.mem_filter.mp hn).1))
    _ = _ := count_zeroless_blocks 7

lemma block_sieve_bound (c : ℕ → ℕ) (k : ℕ) :
    2 ^ k * c k ≤ c 0 + ∑ j ∈ Finset.range k, 2 ^ j * (2 * c (j + 1) - c j) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Finset.sum_range_succ]
    have step : 2 * c (k + 1) ≤ c k + (2 * c (k + 1) - c k) := by omega
    calc
      2 ^ k * 2 * c (k + 1) = 2 ^ k * (2 * c (k + 1)) := Nat.mul_assoc _ _ _
      _ ≤ 2 ^ k * c k + 2 ^ k * (2 * c (k + 1) - c k) := by
        simpa only [Nat.mul_add] using Nat.mul_le_mul_left (2 ^ k) step
      _ ≤ _ := by omega

lemma digit_ne_zero {m t : ℕ} (hm : 0 ∉ Nat.digits 10 m) (ht : 10 ^ t ≤ m) :
    m / 10 ^ t % 10 ≠ 0 := by
  have h := (Nat.lt_digits_length_iff (by decide : 1 < 10) m).2 ht
  rw [← Nat.getD_digits m t (by decide : 2 ≤ 10), List.getD_eq_getElem _ _ h]
  intro hz
  exact hm (hz ▸ List.getElem_mem h)

open OMA.S_oeis_a124648

lemma isTerm_iff_finite_tests (n : ℕ) :
    IsTerm n ↔ n ≠ 0 ∧ ∀ i : Fin 7, 0 ∉ Nat.digits 10 (n ^ (i.val + 1)) := by
  constructor
  · intro h
    exact ⟨by simpa using (h 1 (by decide) (by decide)).1,
      fun i => (h (i.val + 1) (by omega) (by omega)).2⟩
  · rintro ⟨hn, h⟩ i hi h7
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
    exact ⟨pow_ne_zero _ hn, h ⟨j, by omega⟩⟩

lemma suffix_digit {m j d : ℕ} (hj : j < d) :
    (m % 10 ^ d) / 10 ^ j % 10 = m / 10 ^ j % 10 := by
  rw [show d = j + (d - j) by omega, pow_add, Nat.mod_mul_right_div_self]
  apply Nat.mod_mod_of_dvd
  exact dvd_pow_self 10 (by omega)

lemma necessary_suffix {n d : ℕ} (hn : IsTerm n) (hd : 10 ^ d ≤ n) :
    ∀ i : Fin 7, ∀ t : Fin d, (n % 10 ^ d) ^ (i.val + 1) / 10 ^ t.val % 10 ≠ 0 := by
  intro i t
  rw [← suffix_digit (m := (n % 10 ^ d) ^ (i.val + 1)) t.isLt, ← Nat.pow_mod, suffix_digit t.isLt]
  apply digit_ne_zero (hn (i.val + 1) (by omega) (by omega)).2
  exact ((Nat.pow_le_pow_right (by decide) t.isLt.le).trans hd).trans (Nat.le_self_pow (by omega) n)

lemma scan_digits_correct (scan : ℕ → ℕ → Bool) (stop : scan 0 0 = true)
    (step : ∀ f m, scan (f + 1) m = (m == 0 || (m % 10 != 0 && scan f (m / 10))))
    (f m : ℕ) (hm : m < 10 ^ f) :
    scan f m = true ↔ 0 ∉ Nat.digits 10 m := by
  induction f generalizing m with
  | zero =>
    have hm0 : m = 0 := by simpa using hm
    simp [hm0, stop]
  | succ f ih =>
    rw [step]
    by_cases hz : m = 0
    · simp [hz]
    · have hdiv : m / 10 < 10 ^ f := (Nat.div_lt_iff_lt_mul (by decide : 0 < 10)).2
        (by simpa only [pow_succ] using hm)
      simp [hz, ih (m / 10) hdiv, Nat.digits_eq_cons_digits_div (by decide : 1 < 10) hz, ne_comm]

-- A three-digit residue sieve reduces the exhaustive check to the surviving suffixes.
set_option maxRecDepth 32000 in
set_option maxHeartbeats 4000000 in
lemma terms_below_100000 {n : ℕ} (hbound : n < 100000) :
    IsTerm n ↔ n ∈ [1, 2, 3, 5, 6, 68, 76, 3944, 15483] := by
  let short := fun s : ℕ => (List.range 10).map fun d => s + 100 * d
  let block := fun s : ℕ =>
    let suffixes := (short s).filter fun r =>
      decide (∀ i : Fin 7, ∀ j : Fin 3, r ^ (i.val + 1) / 10 ^ j.val % 10 ≠ 0)
    short s ++ suffixes.flatMap fun r => (List.range' 1 99).map fun q => r + 1000 * q
  let scan : ℕ → ℕ → Bool := Nat.rec (motive := fun _ => ℕ → Bool) (fun _ => true)
    (fun _ next m => m == 0 || (m % 10 != 0 && next (m / 10)))
  let test := fun m : ℕ => m != 0 && (List.range 7).all fun i => scan 35 (m ^ (i + 1))
  have htest (m : ℕ) (hm : m < 100000) : test m = true ↔ IsTerm m := by
    rw [isTerm_iff_finite_tests]
    simp only [test, Bool.and_eq_true, bne_iff_ne, List.all_eq_true, List.mem_range]
    have digit_test (i : ℕ) (hi : i < 7) :
        scan 35 (m ^ (i + 1)) = true ↔ 0 ∉ Nat.digits 10 (m ^ (i + 1)) := by
      refine scan_digits_correct scan rfl (fun _ _ => rfl) 35 (m ^ (i + 1)) ?_
      calc
        m ^ (i + 1) < 100000 ^ (i + 1) := Nat.pow_lt_pow_left hm (by omega)
        _ ≤ 100000 ^ 7 := Nat.pow_le_pow_right (by decide) (by omega)
        _ = 10 ^ 35 := by decide
    exact and_congr_right fun _ =>
      ⟨fun h i => (digit_test i.val i.isLt).mp (h i.val i.isLt),
       fun h i hi => (digit_test i hi).mpr (h ⟨i, hi⟩)⟩
  have complete (h : IsTerm n) : n ∈ block (n % 100) := by
    have hshort : n % 1000 ∈ short (n % 100) := by
      apply List.mem_map.mpr
      refine ⟨n % 1000 / 100, List.mem_range.mpr (by omega), ?_⟩
      simpa only [Nat.mod_mod_of_dvd n (by decide : 100 ∣ 1000)] using
        Nat.mod_add_div (n % 1000) 100
    apply List.mem_append.mpr
    by_cases hs : n < 1000
    · exact Or.inl (by simpa only [Nat.mod_eq_of_lt hs] using hshort)
    · right
      apply List.mem_flatMap.mpr
      refine ⟨n % 1000, List.mem_filter.mpr ⟨hshort, ?_⟩, ?_⟩
      · exact decide_eq_true (necessary_suffix (d := 3) h (by omega))
      · exact List.mem_map.mpr ⟨n / 1000, List.mem_range'_1.mpr (by omega), Nat.mod_add_div _ _⟩
  let known : List ℕ := [1, 2, 3, 5, 6, 68, 76, 3944, 15483]
  have table (s : Fin 100) : (block s.val).filter test =
      known.filter (fun m => m % 100 == s.val) := by
    dsimp only [block, short, test, scan, known]
    fin_cases s <;> decide +kernel
  have checked := table ⟨n % 100, by omega⟩
  change IsTerm n ↔ n ∈ known
  have equiv : n ∈ (block (n % 100)).filter test ↔ n ∈ known := by
    rw [checked]
    simp
  rw [← equiv, List.mem_filter, htest n hbound]
  exact ⟨fun h => ⟨complete h, h⟩, And.right⟩

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a124648.main := by
  rintro ⟨K₁, size⟩ ⟨K₂, excess⟩
  refine (Set.finite_Iio (100 ^ (max K₁ K₂) : ℕ)).subset ?_
  intro n hn
  change OMA.S_oeis_a124648.IsTerm n at hn
  change n < 100 ^ (max K₁ K₂)
  by_contra! hlarge
  have hn0 : n ≠ 0 := by simpa using (hn 1 (by decide) (by decide)).1
  let k := Nat.log 100 n
  have hk : max K₁ K₂ ≤ k := (Nat.le_log_iff_pow_le (by decide : 1 < 100) hn0).2 hlarge
  have hlow : 100 ^ k ≤ n := Nat.pow_log_le_self 100 hn0
  let bases := (Finset.Ico (100 ^ k) (100 ^ (k + 1))).filter fun m =>
    ∀ i : Fin 6, 0 ∉ Nat.digits 10 (m ^ (i.val + 1))
  let c := fun j : ℕ => (bases.filter fun m =>
    ∀ t : Fin (7 * j), m ^ 7 / 10 ^ t.val % 10 ≠ 0).card
  have hbase : n ∈ bases := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨hlow, ?_⟩, ?_⟩
    · exact Nat.lt_pow_succ_log_self (by decide : 1 < 100) n
    · intro i
      exact (hn (i.val + 1) (by omega) (by omega)).2
  -- The tested suffix lies inside the significant digits of the seventh power.
  have hlength : 10 ^ (14 * k) ≤ n ^ 7 := calc
    10 ^ (14 * k) = (100 ^ k : ℕ) ^ 7 := by
      rw [show (100 : ℕ) = 10 ^ 2 by decide, ← pow_mul, ← pow_mul]
      congr 1
      omega
    _ ≤ n ^ 7 := Nat.pow_le_pow_left hlow 7
  have survives : 0 < c k := by
    refine Finset.card_pos.mpr ⟨n, Finset.mem_filter.mpr ⟨hbase, ?_⟩⟩
    intro t
    apply digit_ne_zero (hn 7 (by decide) (by decide)).2
    exact (Nat.pow_le_pow_right (by decide : 0 < 10) (by omega : t.val ≤ 14 * k)).trans hlength
  have hzero : c 0 = bases.card := by simp [c]
  have hsize : 2 * c 0 < 2 ^ k := by
    rw [hzero]
    exact size k ((le_max_left K₁ K₂).trans hk)
  have hexcess : 2 * (∑ j ∈ Finset.range k, 2 ^ j * (2 * c (j + 1) - c j)) ≤ 2 ^ k :=
    excess k ((le_max_right K₁ K₂).trans hk)
  have bound := block_sieve_bound c k
  have one := Nat.le_mul_of_pos_right (2 ^ k) survives
  omega

end OMA.R_oeis_a124648_R1
