import FormalConjectures.ErdosProblems.«269»

/-
Erdős Problem 269, variant `rational`: disproof.

For P = {2, 3} the sum is irrational.  Writing e(j) = ⌊j log₂ 3⌋ and
t_j = 1 / (3^j 2^{e(j)}), S2 = Σ t_j, the series factors as 1 + S1 * S2 with
S1 + 2 * S2 = 4, so it equals 1 + 4 S2 - 2 S2^2.  A Dirichlet / least-index
argument produces rationals c / (D - 1) with 0 < |S2 - c/(D-1)| much smaller
than 1 / (D - 1)^2, which is incompatible with 1 + 4 S2 - 2 S2^2 being rational.

The factorisation S = S1 * S2 and the identity (p-1) S1 + (q-1) S2 = p + q - 1
are due to Steve Fan (erdosproblems.com forum thread for problem 269).

Written with Claude Code (AI-assisted).
-/

namespace E269

/-- The prime set {2, 3}, as the coercion of a `Finset` (the form the target uses). -/
abbrev P23 : Set ℕ := ((({2, 3} : Finset ℕ)) : Set ℕ)

/-- e(j) = ⌊j log₂ 3⌋. -/
abbrev e (j : ℕ) : ℕ := Nat.log 2 (3 ^ j)

/-- f(i) = ⌊i log₃ 2⌋. -/
abbrev f (i : ℕ) : ℕ := Nat.log 3 (2 ^ i)

/-- t_j = 1 / (3^j 2^{e(j)}). -/
noncomputable abbrev t (j : ℕ) : ℝ := 1 / ((3 : ℝ) ^ j * (2 : ℝ) ^ (e j))

/-- S1 = Σ_i 1 / (2^i 3^{f(i)}). -/
noncomputable abbrev S1 : ℝ := ∑' i : ℕ, 1 / ((2 : ℝ) ^ i * (3 : ℝ) ^ (f i))

/-- S2 = Σ_j t_j. -/
noncomputable abbrev S2 : ℝ := ∑' j : ℕ, t j



open Erdos269 Filter
open scoped Topology

-- ## L1: the {2,3}-smooth numbers

theorem mem_P23 (p : ℕ) : p ∈ P23 ↔ p = 2 ∨ p = 3 := by
  simp [P23]

theorem smooth_of_pow (i j : ℕ) : HasPrimeFactorsIn P23 (2 ^ i * 3 ^ j) := by
  refine ⟨by positivity, fun p hp hd => ?_⟩
  rw [mem_P23]
  rcases (Nat.Prime.dvd_mul hp).mp hd with h | h
  · left; exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h)
  · right; exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp (hp.dvd_of_dvd_pow h)

theorem pow_of_smooth : ∀ n, HasPrimeFactorsIn P23 n → ∃ i j, n = 2 ^ i * 3 ^ j := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rintro ⟨hpos, hpr⟩
    rcases eq_or_ne n 1 with h1 | h1
    · exact ⟨0, 0, by simp [h1]⟩
    · obtain ⟨p, hp, k, rfl⟩ := Nat.exists_prime_and_dvd h1
      have hk : 0 < k := by
        rcases Nat.eq_zero_or_pos k with h | h
        · subst h; simp at hpos
        · exact h
      have hlt : k < p * k := by nlinarith [hp.two_le]
      obtain ⟨i, j, rfl⟩ := ih k hlt ⟨hk, fun p' hp' hd => hpr p' hp' (Dvd.dvd.mul_left hd p)⟩
      rcases (mem_P23 p).mp (hpr p hp (dvd_mul_right p _)) with rfl | rfl
      · exact ⟨i + 1, j, by ring⟩
      · exact ⟨i, j + 1, by ring⟩

theorem smooth_iff (n : ℕ) : HasPrimeFactorsIn P23 n ↔ ∃ i j, n = 2 ^ i * 3 ^ j :=
  ⟨pow_of_smooth n, by rintro ⟨i, j, rfl⟩; exact smooth_of_pow i j⟩

theorem pow_inj {i j k l : ℕ} (h : 2 ^ i * 3 ^ j = 2 ^ k * 3 ^ l) : i = k ∧ j = l := by
  have c23 : ∀ a b : ℕ, Nat.Coprime (2 ^ a) (3 ^ b) := fun a b => Nat.Coprime.pow a b (by norm_num)
  have c32 : ∀ a b : ℕ, Nat.Coprime (3 ^ a) (2 ^ b) := fun a b => Nat.Coprime.pow a b (by norm_num)
  have h1 : i ≤ k := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp
    ((c23 i l).dvd_of_dvd_mul_right ⟨3 ^ j, h.symm⟩)
  have h2 : k ≤ i := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp
    ((c23 k j).dvd_of_dvd_mul_right ⟨3 ^ l, h⟩)
  have h3 : j ≤ l := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp
    ((c32 j k).dvd_of_dvd_mul_left ⟨2 ^ i, by rw [← h]; ring⟩)
  have h4 : l ≤ j := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp
    ((c32 l i).dvd_of_dvd_mul_left ⟨2 ^ k, by rw [h]; ring⟩)
  exact ⟨le_antisymm h1 h2, le_antisymm h3 h4⟩

theorem smooth_infinite : (Set.ofPred (HasPrimeFactorsIn P23)).Infinite := by
  refine (Set.infinite_range_of_injective (f := fun k : ℕ => 2 ^ k)
    (Nat.pow_right_injective (le_refl 2))).mono ?_
  rintro _ ⟨k, rfl⟩
  have h := smooth_of_pow k 0
  rw [pow_zero, mul_one] at h
  exact h

-- ## L2: logarithms of smooth numbers

theorem log2_smooth (i j : ℕ) : Nat.log 2 (2 ^ i * 3 ^ j) = i + e j := by
  induction i with
  | zero => simp [e]
  | succ n ih =>
    rw [show 2 ^ (n + 1) * 3 ^ j = 2 ^ n * 3 ^ j * 2 by ring,
      Nat.log_mul_base (by norm_num) (by positivity), ih]
    ring

theorem log3_smooth (i j : ℕ) : Nat.log 3 (2 ^ i * 3 ^ j) = j + f i := by
  induction j with
  | zero => simp [f]
  | succ n ih =>
    rw [show 2 ^ i * 3 ^ (n + 1) = 2 ^ i * 3 ^ n * 3 by ring,
      Nat.log_mul_base (by norm_num) (by positivity), ih]
    ring

-- ## L3: the partial lcm

theorem partialLcm_zero : partialLcm P23 0 = 1 := by
  simp [partialLcm]

theorem partialLcm_succ (n : ℕ) :
    partialLcm P23 (n + 1) = 2 ^ (Nat.log 2 (a P23 n)) * 3 ^ (Nat.log 3 (a P23 n)) := by
  classical
  have hmem : ∀ k, HasPrimeFactorsIn P23 (a P23 k) := Nat.nth_mem_of_infinite smooth_infinite
  have hpos : 0 < a P23 n := (hmem n).1
  have key : ∀ x, HasPrimeFactorsIn P23 x → x ≤ a P23 n → x ∣ partialLcm P23 (n + 1) := by
    intro x hs hle
    have hc : a P23 (Nat.count (HasPrimeFactorsIn P23) x) = x := Nat.nth_count hs
    have hk : Nat.count (HasPrimeFactorsIn P23) x ≤ n := by
      have : a P23 (Nat.count (HasPrimeFactorsIn P23) x) ≤ a P23 n := by rw [hc]; exact hle
      exact (Nat.nth_le_nth smooth_infinite).mp this
    have hd : a P23 (Nat.count (HasPrimeFactorsIn P23) x) ∣ partialLcm P23 (n + 1) :=
      Finset.dvd_lcm (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))
    rwa [hc] at hd
  apply Nat.dvd_antisymm
  · unfold partialLcm
    rw [Finset.lcm_dvd_iff]
    intro k hk
    have hk' : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have hle : a P23 k ≤ a P23 n := (Nat.nth_le_nth smooth_infinite).mpr hk'
    obtain ⟨i', j', hk2⟩ := pow_of_smooth _ (hmem k)
    rw [hk2] at hle ⊢
    apply Nat.mul_dvd_mul
    · apply Nat.pow_dvd_pow
      apply Nat.le_log_of_pow_le (by norm_num)
      exact le_trans (Nat.le_mul_of_pos_right _ (by positivity)) hle
    · apply Nat.pow_dvd_pow
      apply Nat.le_log_of_pow_le (by norm_num)
      exact le_trans (Nat.le_mul_of_pos_left _ (by positivity)) hle
  · apply Nat.Coprime.mul_dvd_of_dvd_of_dvd (Nat.Coprime.pow _ _ (by norm_num))
    · have hs := smooth_of_pow (Nat.log 2 (a P23 n)) 0
      rw [pow_zero, mul_one] at hs
      exact key _ hs (Nat.pow_log_le_self 2 hpos.ne')
    · have hs := smooth_of_pow 0 (Nat.log 3 (a P23 n))
      rw [pow_zero, one_mul] at hs
      exact key _ hs (Nat.pow_log_le_self 3 hpos.ne')

-- ## L4: the exponent sequence `e`

theorem e_spec (j : ℕ) : 2 ^ e j ≤ 3 ^ j ∧ 3 ^ j < 2 ^ (e j + 1) :=
  ⟨Nat.pow_log_le_self 2 (by positivity), Nat.lt_pow_succ_log_self (by norm_num) _⟩

theorem f_spec (i : ℕ) : 3 ^ f i ≤ 2 ^ i ∧ 2 ^ i < 3 ^ (f i + 1) :=
  ⟨Nat.pow_log_le_self 3 (by positivity), Nat.lt_pow_succ_log_self (by norm_num) _⟩

theorem e_step (j : ℕ) : e j + 1 ≤ e (j + 1) := by
  have h1 := (e_spec j).1
  have h2 := (e_spec (j + 1)).2
  have h3 : 2 ^ (e j + 1) < 2 ^ (e (j + 1) + 1) := by
    calc 2 ^ (e j + 1) = 2 * 2 ^ e j := by ring
      _ ≤ 2 * 3 ^ j := Nat.mul_le_mul_left 2 h1
      _ ≤ 3 * 3 ^ j := Nat.mul_le_mul_right _ (by norm_num)
      _ = 3 ^ (j + 1) := by ring
      _ < _ := h2
  have := (Nat.pow_lt_pow_iff_right (by norm_num)).mp h3
  omega

theorem e_mono : Monotone e :=
  monotone_nat_of_le_succ (fun j => by have := e_step j; omega)

theorem e_ge (j : ℕ) : j ≤ e j := by
  induction j with
  | zero => exact Nat.zero_le _
  | succ n ih => have := e_step n; omega

theorem e_add (j Q : ℕ) : e (j + Q) = e j + e Q ∨ e (j + Q) = e j + e Q + 1 := by
  have h1 : 2 ^ (e j + e Q) < 2 ^ (e (j + Q) + 1) := by
    calc 2 ^ (e j + e Q) = 2 ^ e j * 2 ^ e Q := by ring
      _ ≤ 3 ^ j * 3 ^ Q := Nat.mul_le_mul (e_spec j).1 (e_spec Q).1
      _ = 3 ^ (j + Q) := by ring
      _ < _ := (e_spec (j + Q)).2
  have h2 : 2 ^ e (j + Q) < 2 ^ (e j + e Q + 2) := by
    calc 2 ^ e (j + Q) ≤ 3 ^ (j + Q) := (e_spec (j + Q)).1
      _ = 3 ^ j * 3 ^ Q := by ring
      _ < 2 ^ (e j + 1) * 2 ^ (e Q + 1) := Nat.mul_lt_mul'' (e_spec j).2 (e_spec Q).2
      _ = 2 ^ (e j + e Q + 2) := by ring
  have := (Nat.pow_lt_pow_iff_right (by norm_num)).mp h1
  have := (Nat.pow_lt_pow_iff_right (by norm_num)).mp h2
  omega

theorem e_zero : e 0 = 0 := by simp [e]

theorem e_one : e 1 = 1 := by
  have h := e_spec 1
  have h1 : e 1 < 2 := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp (lt_of_le_of_lt h.1 (by norm_num))
  have h2 : 1 < e 1 + 1 := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp (lt_trans (by norm_num) h.2)
  omega

theorem e_two : e 2 = 3 := by
  have h := e_spec 2
  have h1 : e 2 < 4 := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp (lt_of_le_of_lt h.1 (by norm_num))
  have h2 : 3 < e 2 + 1 := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp (lt_trans (by norm_num) h.2)
  omega

-- ## L5: size of the terms

theorem t_pos (j : ℕ) : 0 < t j := by unfold t; positivity

theorem t_bounds (j : ℕ) : 1 / (9 : ℝ) ^ j ≤ t j ∧ t j < 2 / (9 : ℝ) ^ j := by
  have h1 : (2 : ℝ) ^ e j ≤ 3 ^ j := by exact_mod_cast (e_spec j).1
  have h2 : (3 : ℝ) ^ j < 2 ^ (e j + 1) := by exact_mod_cast (e_spec j).2
  have h9 : (9 : ℝ) ^ j = 3 ^ j * 3 ^ j := by rw [← mul_pow]; norm_num
  have p3 : (0 : ℝ) < 3 ^ j := by positivity
  have p2 : (0 : ℝ) < 2 ^ e j := by positivity
  constructor
  · unfold t
    apply one_div_le_one_div_of_le (by positivity)
    rw [h9]
    exact mul_le_mul_of_nonneg_left h1 p3.le
  · unfold t
    rw [div_lt_div_iff₀ (by positivity) (by positivity), h9, one_mul]
    rw [pow_succ] at h2
    nlinarith

theorem t_summable : Summable t := by
  refine Summable.of_nonneg_of_le (fun j => (t_pos j).le) (fun j => (t_bounds j).2.le)
    (f := fun j : ℕ => 2 / (9 : ℝ) ^ j) ?_
  have := (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 9) (by norm_num)).mul_left 2
  refine this.congr (fun j => ?_)
  rw [one_div, inv_pow]; rfl

theorem t_tail (J : ℕ) : ∑' j, t (j + J) < (9 / 4) / (9 : ℝ) ^ J := by
  have hs : Summable (fun j => t (j + J)) := (summable_nat_add_iff J).mpr t_summable
  have hg : Summable (fun j : ℕ => 2 / (9 : ℝ) ^ J * (1 / 9 : ℝ) ^ j) :=
    (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 9) (by norm_num)).mul_left _
  have hle : ∀ j, t (j + J) ≤ 2 / (9 : ℝ) ^ J * (1 / 9 : ℝ) ^ j := by
    intro j
    refine le_of_lt (lt_of_lt_of_eq (t_bounds (j + J)).2 ?_)
    rw [pow_add, one_div, inv_pow]; field_simp
  have hlt : t (0 + J) < 2 / (9 : ℝ) ^ J * (1 / 9 : ℝ) ^ 0 := by
    refine lt_of_lt_of_eq (t_bounds (0 + J)).2 ?_
    rw [zero_add, pow_zero, mul_one]
  have := Summable.tsum_lt_tsum hle hlt hs hg
  rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)] at this
  calc ∑' j, t (j + J) < 2 / (9 : ℝ) ^ J * (1 - 1 / 9)⁻¹ := this
    _ = (9 / 4) / (9 : ℝ) ^ J := by norm_num; ring

/-- The `S1`-terms are dominated by a geometric series. -/
theorem s1_term_le (i : ℕ) : 1 / ((2 : ℝ) ^ i * (3 : ℝ) ^ (f i)) ≤ (1 / 2 : ℝ) ^ i := by
  rw [one_div_pow]
  apply one_div_le_one_div_of_le (by positivity)
  have : (1 : ℝ) ≤ 3 ^ f i := one_le_pow₀ (by norm_num)
  nlinarith [show (0 : ℝ) < 2 ^ i by positivity]

theorem s1_summable : Summable (fun i : ℕ => 1 / ((2 : ℝ) ^ i * (3 : ℝ) ^ (f i))) :=
  Summable.of_nonneg_of_le (fun i => by positivity) s1_term_le
    (summable_geometric_of_lt_one (by norm_num) (by norm_num))

-- ## L6: bounds for `S2`

theorem S2_bounds : 7 / 6 ≤ S2 ∧ S2 < 6 / 5 := by
  have h3 := Summable.sum_add_tsum_nat_add 3 t_summable
  have ht0 : t 0 = 1 := by unfold t; rw [e_zero]; norm_num
  have ht1 : t 1 = 1 / 6 := by unfold t; rw [e_one]; norm_num
  have ht2 : t 2 = 1 / 72 := by unfold t; rw [e_two]; norm_num
  have htail := t_tail 3
  have hpos : 0 ≤ ∑' j, t (j + 3) := tsum_nonneg (fun j => (t_pos _).le)
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one, ht0, ht1, ht2] at h3
  have hS : S2 = 1 + 1 / 6 + 1 / 72 + ∑' j, t (j + 3) := h3.symm
  constructor
  · rw [hS]; linarith
  · rw [hS]; norm_num at htail ⊢; linarith

-- ## L10-L13: Diophantine key lemma

/- ### Generic facts about `Int.floor` / `Int.fract` of a sum -/

theorem floor_add_eq_iff (x y : ℝ) :
    ⌊x + y⌋ = ⌊x⌋ + ⌊y⌋ ↔ Int.fract x + Int.fract y < 1 := by
  have hx := Int.floor_add_fract x
  have hy := Int.floor_add_fract y
  have hx0 := Int.fract_nonneg x
  have hy0 := Int.fract_nonneg y
  rw [Int.floor_eq_iff]
  push_cast
  constructor
  · rintro ⟨_, h⟩
    linarith
  · intro h
    constructor <;> linarith

theorem floor_add_eq_succ_iff (x y : ℝ) :
    ⌊x + y⌋ = ⌊x⌋ + ⌊y⌋ + 1 ↔ 1 ≤ Int.fract x + Int.fract y := by
  have hx := Int.floor_add_fract x
  have hy := Int.floor_add_fract y
  have hx1 := Int.fract_lt_one x
  have hy1 := Int.fract_lt_one y
  rw [Int.floor_eq_iff]
  push_cast
  constructor
  · rintro ⟨h, _⟩
    linarith
  · intro h
    constructor <;> linarith

theorem fract_add_of_lt (x y : ℝ) (h : Int.fract x + Int.fract y < 1) :
    Int.fract (x + y) = Int.fract x + Int.fract y := by
  have hx := Int.floor_add_fract x
  have hy := Int.floor_add_fract y
  have hx0 := Int.fract_nonneg x
  have hy0 := Int.fract_nonneg y
  rw [Int.fract_eq_iff]
  refine ⟨by linarith, h, ⌊x⌋ + ⌊y⌋, ?_⟩
  push_cast
  linarith

theorem fract_add_of_ge (x y : ℝ) (h : 1 ≤ Int.fract x + Int.fract y) :
    Int.fract (x + y) = Int.fract x + Int.fract y - 1 := by
  have hx := Int.floor_add_fract x
  have hy := Int.floor_add_fract y
  have hx1 := Int.fract_lt_one x
  have hy1 := Int.fract_lt_one y
  rw [Int.fract_eq_iff]
  refine ⟨by linarith, by linarith, ⌊x⌋ + ⌊y⌋ + 1, ?_⟩
  push_cast
  linarith

/- ### L10 -/

theorem logb_two_three_pos : 0 < Real.logb 2 3 :=
  Real.logb_pos (by norm_num) (by norm_num)

/-- L10a: `e j = ⌊j · log₂ 3⌋`. -/
theorem e_cast_eq_floor (j : ℕ) : ((e j : ℕ) : ℤ) = ⌊(j : ℝ) * Real.logb 2 3⌋ := by
  have h1 : (j : ℝ) * Real.logb 2 3 = Real.logb ((2 : ℕ) : ℝ) ((3 ^ j : ℕ) : ℝ) := by
    push_cast
    rw [Real.logb_pow]
  have h2 : 0 ≤ (j : ℝ) * Real.logb 2 3 :=
    mul_nonneg (Nat.cast_nonneg j) logb_two_three_pos.le
  rw [← Int.natCast_floor_eq_floor h2, h1, Real.natFloor_logb_natCast]

/-- L10b: `i · log₂ 3` is never an integer for `i ≥ 1`. -/
theorem mul_logb_ne_int (i : ℕ) (hi : 1 ≤ i) (n : ℤ) : (i : ℝ) * Real.logb 2 3 ≠ (n : ℝ) := by
  intro h
  have hi' : (0 : ℝ) < (i : ℝ) := by exact_mod_cast hi
  have hpos : 0 < (i : ℝ) * Real.logb 2 3 := mul_pos hi' logb_two_three_pos
  have hn : 0 < n := by
    have h0 : (0 : ℝ) < (n : ℝ) := by rw [← h]; exact hpos
    exact_mod_cast h0
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn.le
  have hm : 0 < m := by exact_mod_cast hn
  have h3 : (3 : ℝ) ^ i = (2 : ℝ) ^ m := by
    have h4 : Real.logb 2 ((3 : ℝ) ^ i) = Real.logb 2 ((2 : ℝ) ^ m) := by
      rw [Real.logb_pow, Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one]
      exact_mod_cast h
    exact Real.logb_injOn_pos (by norm_num) (Set.mem_Ioi.2 (by positivity))
      (Set.mem_Ioi.2 (by positivity)) h4
  have h5 : 3 ^ i = 2 ^ m := by exact_mod_cast h3
  have h6 : Odd (3 ^ i) := Odd.pow (by decide)
  have h7 : Even (3 ^ i) := by
    rw [h5]
    exact (even_two).pow_of_ne_zero hm.ne'
  exact (Nat.not_even_iff_odd.2 h6) h7

/- ### L11 -/

/-- L11: `e (j+Q) = e j + e Q` iff the fractional parts do not carry. -/
theorem e_add_eq_iff (j Q : ℕ) :
    e (j + Q) = e j + e Q ↔
      Int.fract ((j : ℝ) * Real.logb 2 3) + Int.fract ((Q : ℝ) * Real.logb 2 3) < 1 := by
  have h1 := e_cast_eq_floor (j + Q)
  have h2 := e_cast_eq_floor j
  have h3 := e_cast_eq_floor Q
  rw [Nat.cast_add, add_mul] at h1
  rw [← floor_add_eq_iff, ← h1, ← h2, ← h3]
  exact ⟨fun h => by exact_mod_cast h, fun h => by exact_mod_cast h⟩

/-- L11': `e (j+Q) = e j + e Q + 1` iff the fractional parts carry. -/
theorem e_add_eq_succ_iff (j Q : ℕ) :
    e (j + Q) = e j + e Q + 1 ↔
      1 ≤ Int.fract ((j : ℝ) * Real.logb 2 3) + Int.fract ((Q : ℝ) * Real.logb 2 3) := by
  have h1 := e_cast_eq_floor (j + Q)
  have h2 := e_cast_eq_floor j
  have h3 := e_cast_eq_floor Q
  rw [Nat.cast_add, add_mul] at h1
  rw [← floor_add_eq_succ_iff, ← h1, ← h2, ← h3]
  exact ⟨fun h => by exact_mod_cast h, fun h => by exact_mod_cast h⟩

/- ### L12 -/

/-- Real-variable core of L12. -/
theorem key_real (β : ℝ) (hβ : ∀ i : ℕ, 1 ≤ i → ∀ n : ℤ, (i : ℝ) * β ≠ (n : ℝ))
    (K : ℕ) (hK : 1 ≤ K) :
    ∃ Q : ℕ, 1 ≤ Q ∧
      ((∀ j : ℕ, j < Q + K →
          Int.fract ((j : ℝ) * β) + Int.fract ((Q : ℝ) * β) < 1) ∨
        (∀ j : ℕ, 1 ≤ j → j < Q + K →
          1 ≤ Int.fract ((j : ℝ) * β) + Int.fract ((Q : ℝ) * β))) := by
  classical
  obtain ⟨θ, hθ⟩ : ∃ θ : ℕ → ℝ, ∀ j, θ j = Int.fract ((j : ℝ) * β) := ⟨_, fun _ => rfl⟩
  obtain ⟨D, hD⟩ : ∃ D : ℕ → ℝ, ∀ j, D j = min (θ j) (1 - θ j) := ⟨_, fun _ => rfl⟩
  have hθ1 : ∀ j, θ j < 1 := fun j => by rw [hθ]; exact Int.fract_lt_one _
  have hθpos : ∀ j, 1 ≤ j → 0 < θ j := by
    intro j hj
    rw [hθ]
    rcases (Int.fract_nonneg ((j : ℝ) * β)).lt_or_eq with h | h
    · exact h
    · exfalso
      have h2 := Int.floor_add_fract ((j : ℝ) * β)
      rw [← h, add_zero] at h2
      exact hβ j hj _ h2.symm
  have hθ0 : θ 0 = 0 := by rw [hθ]; simp
  have hD1 : ∀ j, D j ≤ θ j := fun j => by rw [hD]; exact min_le_left _ _
  have hD2 : ∀ j, D j ≤ 1 - θ j := fun j => by rw [hD]; exact min_le_right _ _
  have hD3 : ∀ j, D j = θ j ∨ D j = 1 - θ j := fun j => by rw [hD]; exact min_choice _ _
  have hDpos : ∀ j, 1 ≤ j → 0 < D j := by
    intro j hj
    rw [hD]
    exact lt_min (hθpos j hj) (by linarith [hθ1 j])
  have hD4 : ∀ j : ℕ, |(j : ℝ) * β - round ((j : ℝ) * β)| = D j := by
    intro j
    rw [hD, hθ, abs_sub_round_eq_min]
  have hθadd1 : ∀ a b : ℕ, θ a + θ b < 1 → θ (a + b) = θ a + θ b := by
    intro a b h
    rw [hθ a, hθ b] at h
    rw [hθ (a + b), hθ a, hθ b, Nat.cast_add, add_mul]
    exact fract_add_of_lt _ _ h
  have hθadd2 : ∀ a b : ℕ, 1 ≤ θ a + θ b → θ (a + b) = θ a + θ b - 1 := by
    intro a b h
    rw [hθ a, hθ b] at h
    rw [hθ (a + b), hθ a, hθ b, Nat.cast_add, add_mul]
    exact fract_add_of_ge _ _ h
  -- the minimum over `1 ≤ i ≤ K`
  have hμ : ∀ K : ℕ, ∃ μ : ℝ, 0 < μ ∧ ∀ i : ℕ, 1 ≤ i → i ≤ K → μ ≤ D i := by
    intro K
    induction K with
    | zero => exact ⟨1, one_pos, fun i h1 h2 => by omega⟩
    | succ n ih =>
      obtain ⟨μ, hμ0, h⟩ := ih
      refine ⟨min μ (D (n + 1)), lt_min hμ0 (hDpos (n + 1) (by omega)), fun i h1 h2 => ?_⟩
      rcases Nat.lt_or_ge i (n + 1) with h3 | h3
      · exact (min_le_left _ _).trans (h i h1 (by omega))
      · have h4 : i = n + 1 := by omega
        rw [h4]
        exact min_le_right _ _
  obtain ⟨μ, hμ0, hμK⟩ := hμ K
  have hμhalf : μ ≤ 1 / 2 := by
    have h1 := hμK 1 le_rfl hK
    have h2 := hD1 1
    have h3 := hD2 1
    linarith
  -- Dirichlet
  have hex : ∃ k : ℕ, 1 ≤ k ∧ D k < μ / 2 := by
    obtain ⟨N, hN⟩ := exists_nat_gt (2 / μ)
    have hNpos : 0 < N := by
      have h0 : (0 : ℝ) < 2 / μ := by positivity
      have h1 : (0 : ℝ) < (N : ℝ) := h0.trans hN
      exact_mod_cast h1
    obtain ⟨k, hk0, _, hk⟩ := Real.exists_nat_abs_mul_sub_round_le β hNpos
    refine ⟨k, hk0, ?_⟩
    rw [hD4] at hk
    refine lt_of_le_of_lt hk ?_
    rw [div_lt_iff₀ hμ0] at hN
    have hN1 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
    rw [div_lt_iff₀ hN1]
    nlinarith
  have hQ := Nat.find_spec hex
  have hmin : ∀ j : ℕ, 1 ≤ j → j < Nat.find hex → μ / 2 ≤ D j := by
    intro j hj1 hj
    by_contra hc
    rw [not_le] at hc
    exact Nat.find_min hex hj ⟨hj1, hc⟩
  generalize Nat.find hex = Q at hQ hmin
  obtain ⟨hQ1, hQδ⟩ := hQ
  have hKQ : K < Q := by
    by_contra hc
    rw [not_lt] at hc
    have := hμK Q hQ1 hc
    linarith
  refine ⟨Q, hQ1, ?_⟩
  rcases hD3 Q with hcase | hcase
  · -- case U
    left
    intro j hj
    rw [← hθ j, ← hθ Q]
    rcases Nat.eq_zero_or_pos j with hj0 | hj0
    · rw [hj0, hθ0]
      linarith [hθ1 Q]
    rcases Nat.lt_or_ge j Q with hjQ | hjQ
    · have h1 := hmin j hj0 hjQ
      have h2 := hD2 j
      linarith
    · obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le hjQ
      have hiK : i < K := by omega
      rcases Nat.eq_zero_or_pos i with hi0 | hi0
      · rw [hi0, add_zero]
        linarith
      · have h1 := hμK i hi0 hiK.le
        have h2 := hD2 i
        have h3 := hθadd1 Q i (by linarith)
        rw [h3]
        linarith
  · -- case L
    right
    intro j hj0 hj
    rw [← hθ j, ← hθ Q]
    rcases Nat.lt_or_ge j Q with hjQ | hjQ
    · have h1 := hmin j hj0 hjQ
      have h2 := hD1 j
      linarith
    · obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le hjQ
      have hiK : i < K := by omega
      rcases Nat.eq_zero_or_pos i with hi0 | hi0
      · rw [hi0, add_zero]
        linarith
      · have h1 := hμK i hi0 hiK.le
        have h2 := hD1 i
        have h3 := hθadd2 Q i (by linarith)
        rw [h3]
        linarith

/-- L12 (KEY): for every `K ≥ 1` there is `Q ≥ 1` in case U or case L. -/
theorem key (K : ℕ) (hK : 1 ≤ K) :
    ∃ Q : ℕ, 1 ≤ Q ∧
      ((∀ j : ℕ, j < Q + K → e (j + Q) = e j + e Q) ∨
        (∀ j : ℕ, 1 ≤ j → j < Q + K → e (j + Q) = e j + e Q + 1)) := by
  obtain ⟨Q, hQ, h⟩ := key_real (Real.logb 2 3) mul_logb_ne_int K hK
  refine ⟨Q, hQ, ?_⟩
  rcases h with h | h
  · exact Or.inl fun j hj => (e_add_eq_iff j Q).2 (h j hj)
  · exact Or.inr fun j hj1 hj => (e_add_eq_succ_iff j Q).2 (h j hj1 hj)

/- ### L13 -/

/-- L13a: the pattern is never case U for all j. -/
theorem exists_e_add_eq_succ (Q : ℕ) (hQ : 1 ≤ Q) : ∃ j : ℕ, e (j + Q) = e j + e Q + 1 := by
  by_contra hne
  have hall : ∀ j : ℕ,
      Int.fract ((j : ℝ) * Real.logb 2 3) + Int.fract ((Q : ℝ) * Real.logb 2 3) < 1 := by
    intro j
    by_contra h
    rw [not_lt] at h
    exact hne ⟨j, (e_add_eq_succ_iff j Q).2 h⟩
  have hpos : 0 < Int.fract ((Q : ℝ) * Real.logb 2 3) := by
    rcases (Int.fract_nonneg ((Q : ℝ) * Real.logb 2 3)).lt_or_eq with h | h
    · exact h
    · exfalso
      have h2 := Int.floor_add_fract ((Q : ℝ) * Real.logb 2 3)
      rw [← h, add_zero] at h2
      exact mul_logb_ne_int Q hQ _ h2.symm
  have hind : ∀ m : ℕ, Int.fract (((m * Q : ℕ) : ℝ) * Real.logb 2 3) =
      (m : ℝ) * Int.fract ((Q : ℝ) * Real.logb 2 3) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      have h := fract_add_of_lt _ _ (hall (m * Q))
      have hc : (((m + 1) * Q : ℕ) : ℝ) * Real.logb 2 3 =
          ((m * Q : ℕ) : ℝ) * Real.logb 2 3 + (Q : ℝ) * Real.logb 2 3 := by
        push_cast
        ring
      rw [hc, h, ih]
      push_cast
      ring
  obtain ⟨m, hm⟩ := exists_nat_gt (1 / Int.fract ((Q : ℝ) * Real.logb 2 3))
  rw [div_lt_iff₀ hpos] at hm
  have h1 := hind m
  have h2 := Int.fract_lt_one (((m * Q : ℕ) : ℝ) * Real.logb 2 3)
  linarith

/-- L13b: the pattern is never case L for all j ≥ 1. -/
theorem exists_e_add_eq (Q : ℕ) (hQ : 1 ≤ Q) : ∃ j : ℕ, 1 ≤ j ∧ e (j + Q) = e j + e Q := by
  by_contra hne
  have hall : ∀ j : ℕ, 1 ≤ j →
      1 ≤ Int.fract ((j : ℝ) * Real.logb 2 3) + Int.fract ((Q : ℝ) * Real.logb 2 3) := by
    intro j hj
    by_contra h
    rw [not_le] at h
    exact hne ⟨j, hj, (e_add_eq_iff j Q).2 h⟩
  have hlt := Int.fract_lt_one ((Q : ℝ) * Real.logb 2 3)
  have hind : ∀ m : ℕ, Int.fract ((((m + 1) * Q : ℕ) : ℝ) * Real.logb 2 3) =
      1 - ((m : ℝ) + 1) * (1 - Int.fract ((Q : ℝ) * Real.logb 2 3)) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      have hp : 1 ≤ (m + 1) * Q := Nat.mul_pos (Nat.succ_pos m) hQ
      have h := fract_add_of_ge _ _ (hall ((m + 1) * Q) hp)
      have hc : (((m + 1 + 1) * Q : ℕ) : ℝ) * Real.logb 2 3 =
          (((m + 1) * Q : ℕ) : ℝ) * Real.logb 2 3 + (Q : ℝ) * Real.logb 2 3 := by
        push_cast
        ring
      rw [hc, h, ih]
      push_cast
      ring
  obtain ⟨m, hm⟩ := exists_nat_gt (1 / (1 - Int.fract ((Q : ℝ) * Real.logb 2 3)))
  rw [div_lt_iff₀ (by linarith)] at hm
  have h1 := hind m
  have h2 := Int.fract_nonneg ((((m + 1) * Q : ℕ) : ℝ) * Real.logb 2 3)
  nlinarith


-- ## L14-L15: approximation


lemma approx_t_pos (j : ℕ) : 0 < t j := by
  unfold t; positivity

lemma approx_t_zero : t 0 = 1 := by
  simp [t, e]

lemma approx_t_shift_eq {j Q : ℕ} (h : e (j + Q) = e j + e Q) :
    t (j + Q) = t j / (3 ^ Q * 2 ^ (e Q)) := by
  unfold t
  rw [h, pow_add, pow_add]
  field_simp

lemma approx_t_shift_succ {j Q : ℕ} (h : e (j + Q) = e j + e Q + 1) :
    t (j + Q) = t j / (3 ^ Q * 2 ^ (e Q)) / 2 := by
  unfold t
  rw [h, pow_add, pow_add, pow_add]
  field_simp

lemma approx_two_pow_e_le (Q : ℕ) : (2 : ℝ) ^ (e Q) ≤ 3 ^ Q := by
  have h : 2 ^ (e Q) ≤ 3 ^ Q := Nat.pow_log_le_self 2 (by positivity)
  exact_mod_cast h

/-- Tail estimate shared by both cases. -/
lemma approx_tail_core {g : ℕ → ℝ} {D : ℝ} (J : ℕ) (hsum : Summable t)
    (hg0 : ∀ j, 0 ≤ g j) (hgle : ∀ j, g j ≤ t j / D) (hpos : ∃ j, J ≤ j ∧ 0 < g j) :
    Summable g ∧ 0 < ∑' j, g (j + J) ∧ ∑' j, g (j + J) ≤ (∑' j, t (j + J)) / D := by
  have hsD : Summable (fun j => t j / D) := hsum.div_const D
  have hg : Summable g := Summable.of_nonneg_of_le hg0 hgle hsD
  have hgJ : Summable (fun j => g (j + J)) := (summable_nat_add_iff J).2 hg
  have htJ : Summable (fun j => t (j + J)) := (summable_nat_add_iff J).2 hsum
  refine ⟨hg, ?_, ?_⟩
  · obtain ⟨j, hj, hjp⟩ := hpos
    refine hgJ.tsum_pos (fun i => hg0 _) (j - J) ?_
    simpa [Nat.sub_add_cancel hj] using hjp
  · rw [← tsum_div_const]
    exact hgJ.tsum_le_tsum (fun i => hgle _) (htJ.div_const D)

/-- Final numeric step shared by both cases: from `X = E * D` small, get the two bounds. -/
lemma approx_final {X D : ℝ} {Q K : ℕ} (hK : 1 ≤ K) (hQ : 1 ≤ Q) (hD3 : 3 ≤ D)
    (hD9 : D ≤ 2 * 9 ^ Q) (hX0 : 0 < X) (hX : X < (9 / 4) / 9 ^ (Q + K)) :
    (D - 1) ^ 2 * (X / (D - 1)) < 9 / 9 ^ K ∧ X / (D - 1) < 1 / 20 := by
  have hD1 : 0 < D - 1 := by linarith
  have h9K : (0 : ℝ) < 9 ^ K := by positivity
  have h9Q : (0 : ℝ) < 9 ^ Q := by positivity
  have hX' : X * (9 ^ Q * 9 ^ K) < 9 / 4 := by
    rw [← pow_add]
    exact (lt_div_iff₀ (by positivity)).1 hX
  constructor
  · have e1 : (D - 1) ^ 2 * (X / (D - 1)) = (D - 1) * X := by
      field_simp
    rw [e1, lt_div_iff₀ h9K]
    have h1 : (D - 1) * X ≤ 2 * 9 ^ Q * X :=
      mul_le_mul_of_nonneg_right (by linarith) hX0.le
    have h2 : (D - 1) * X * 9 ^ K ≤ 2 * 9 ^ Q * X * 9 ^ K :=
      mul_le_mul_of_nonneg_right h1 h9K.le
    nlinarith [h2, hX']
  · have h81 : (9 : ℝ) ^ 2 ≤ 9 ^ (Q + K) :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    have hXs : X < 1 / 36 := by
      have : (9 / 4 : ℝ) / 9 ^ (Q + K) ≤ (9 / 4) / 9 ^ 2 :=
        div_le_div_of_nonneg_left (by norm_num) (by norm_num) h81
      norm_num at this
      linarith
    rw [div_lt_iff₀ hD1]
    nlinarith

/-- `T * D` is a natural number (case U). -/
lemma approx_cast_c (he_mono : Monotone e) (Q m : ℕ) (hm : e Q ≤ m) :
    ((∑ j ∈ Finset.range Q, 3 ^ (Q - j) * 2 ^ (m - e j) : ℕ) : ℝ)
      = (∑ j ∈ Finset.range Q, t j) * (3 ^ Q * 2 ^ m) := by
  push_cast
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  have hjQ : j ≤ Q := (Finset.mem_range.1 hj).le
  have hem : e j ≤ m := (he_mono hjQ).trans hm
  have h3 : (3 : ℝ) ^ Q = 3 ^ (Q - j) * 3 ^ j := by
    rw [← pow_add, Nat.sub_add_cancel hjQ]
  have h2 : (2 : ℝ) ^ m = 2 ^ (m - e j) * 2 ^ (e j) := by
    rw [← pow_add, Nat.sub_add_cancel hem]
  rw [h3, h2]
  unfold t
  field_simp

/-- **L14** (case U of the key lemma), signed form. -/
theorem approx_U
    (he_mono : Monotone e)
    (hstep : ∀ j Q, e (j + Q) = e j + e Q ∨ e (j + Q) = e j + e Q + 1)
    (hsum : Summable t)
    (htail : ∀ J : ℕ, ∑' j, t (j + J) < (9 / 4) / 9 ^ J)
    (hnp : ∀ Q, 1 ≤ Q → ∃ j, e (j + Q) = e j + e Q + 1)
    {K Q : ℕ} (hK : 1 ≤ K) (hQ : 1 ≤ Q)
    (hU : ∀ j, j < Q + K → e (j + Q) = e j + e Q) :
    ∃ c D : ℕ, 2 ≤ D ∧ 0 < (c : ℝ) / ((D : ℝ) - 1) - S2 ∧
      ((D : ℝ) - 1) ^ 2 * ((c : ℝ) / ((D : ℝ) - 1) - S2) < 9 / 9 ^ K ∧
      (c : ℝ) / ((D : ℝ) - 1) - S2 < 1 / 20 := by
  refine ⟨∑ j ∈ Finset.range Q, 3 ^ (Q - j) * 2 ^ (e Q - e j), 3 ^ Q * 2 ^ (e Q), ?_⟩
  have hc := approx_cast_c he_mono Q (e Q) le_rfl
  have hDn : 3 ≤ 3 ^ Q * 2 ^ (e Q) := by
    have h1 : 3 ^ 1 ≤ 3 ^ Q := Nat.pow_le_pow_right (by norm_num) hQ
    have h2 : 1 ≤ 2 ^ (e Q) := Nat.one_le_two_pow
    nlinarith
  have hDcast : ((3 ^ Q * 2 ^ (e Q) : ℕ) : ℝ) = 3 ^ Q * 2 ^ (e Q) := by push_cast; rfl
  rw [hDcast]
  have hD3' : (3 : ℝ) ≤ ((3 ^ Q * 2 ^ (e Q) : ℕ) : ℝ) := by exact_mod_cast hDn
  rw [hDcast] at hD3'
  generalize hDdef : (3 : ℝ) ^ Q * 2 ^ (e Q) = D at *
  have hD0 : 0 < D := by linarith
  have hD1 : 0 < D - 1 := by linarith
  have hD9 : D ≤ 2 * 9 ^ Q := by
    have h := approx_two_pow_e_le Q
    have h3 : (0 : ℝ) < 3 ^ Q := by positivity
    have : (9 : ℝ) ^ Q = 3 ^ Q * 3 ^ Q := by
      rw [← mul_pow]; norm_num
    rw [← hDdef, this]
    nlinarith [mul_le_mul_of_nonneg_left h h3.le]
  -- the defect function
  set g : ℕ → ℝ := fun j => t j / D - t (j + Q) with hgdef
  have hgU : ∀ j, e (j + Q) = e j + e Q → g j = 0 := by
    intro j h
    simp only [hgdef, approx_t_shift_eq h, hDdef, sub_self]
  have hgS : ∀ j, e (j + Q) = e j + e Q + 1 → g j = t j / D / 2 := by
    intro j h
    simp only [hgdef, approx_t_shift_succ h, hDdef]
    ring
  have htD : ∀ j, 0 < t j / D := fun j => div_pos (approx_t_pos j) hD0
  have hg0 : ∀ j, 0 ≤ g j := by
    intro j
    rcases hstep j Q with h | h
    · rw [hgU j h]
    · rw [hgS j h]; linarith [htD j]
  have hgle : ∀ j, g j ≤ t j / D := by
    intro j
    simp only [hgdef]
    linarith [approx_t_pos (j + Q)]
  have hpos : ∃ j, Q + K ≤ j ∧ 0 < g j := by
    obtain ⟨j, hj⟩ := hnp Q hQ
    refine ⟨j, ?_, ?_⟩
    · by_contra hlt
      have := hU j (not_le.1 hlt)
      omega
    · rw [hgS j hj]; linarith [htD j]
  obtain ⟨hg, hEpos, hEle⟩ := approx_tail_core (Q + K) hsum hg0 hgle hpos
  have htQ : Summable (fun j => t (j + Q)) := (summable_nat_add_iff Q).2 hsum
  have hsplit := hg.sum_add_tsum_nat_add (Q + K)
  have hfin : ∑ i ∈ Finset.range (Q + K), g i = 0 :=
    Finset.sum_eq_zero (fun i hi => hgU i (hU i (Finset.mem_range.1 hi)))
  have hgsum : ∑' j, g j = S2 / D - ∑' j, t (j + Q) := by
    simp only [hgdef]
    rw [(hsum.div_const D).tsum_sub htQ, tsum_div_const]
  have hS2 : S2 = ∑ j ∈ Finset.range Q, t j + ∑' j, t (j + Q) :=
    (hsum.sum_add_tsum_nat_add Q).symm
  have hE : ∑' j, g (j + (Q + K)) =
      S2 / D - (S2 - ∑ j ∈ Finset.range Q, t j) := by
    rw [hfin, zero_add] at hsplit
    rw [hsplit, hgsum, hS2]; ring
  have hXle : (∑' j, g (j + (Q + K))) * D ≤ ∑' j, t (j + (Q + K)) :=
    (le_div_iff₀ hD0).1 hEle
  have key : ((∑ j ∈ Finset.range Q, 3 ^ (Q - j) * 2 ^ (e Q - e j) : ℕ) : ℝ) / (D - 1) - S2
      = (∑' j, g (j + (Q + K))) * D / (D - 1) := by
    rw [hc, hE]
    field_simp
    ring
  rw [key]
  have hX0 : 0 < (∑' j, g (j + (Q + K))) * D := mul_pos hEpos hD0
  obtain ⟨h1, h2⟩ := approx_final hK hQ hD3' hD9 hX0 (lt_of_le_of_lt hXle (htail (Q + K)))
  exact ⟨by omega, div_pos hX0 hD1, h1, h2⟩

/-- **L15** (case L of the key lemma), signed form. -/
theorem approx_L
    (he_mono : Monotone e)
    (hstep : ∀ j Q, e (j + Q) = e j + e Q ∨ e (j + Q) = e j + e Q + 1)
    (hsum : Summable t)
    (htail : ∀ J : ℕ, ∑' j, t (j + J) < (9 / 4) / 9 ^ J)
    (hnp : ∀ Q, 1 ≤ Q → ∃ j, 1 ≤ j ∧ e (j + Q) = e j + e Q)
    {K Q : ℕ} (hK : 1 ≤ K) (hQ : 1 ≤ Q)
    (hL : ∀ j, 1 ≤ j → j < Q + K → e (j + Q) = e j + e Q + 1) :
    ∃ c D : ℕ, 2 ≤ D ∧ 0 < S2 - (c : ℝ) / ((D : ℝ) - 1) ∧
      ((D : ℝ) - 1) ^ 2 * (S2 - (c : ℝ) / ((D : ℝ) - 1)) < 9 / 9 ^ K ∧
      S2 - (c : ℝ) / ((D : ℝ) - 1) < 1 / 20 := by
  refine ⟨(∑ j ∈ Finset.range Q, 3 ^ (Q - j) * 2 ^ (e Q + 1 - e j)) + 1,
    3 ^ Q * 2 ^ (e Q + 1), ?_⟩
  have hc := approx_cast_c he_mono Q (e Q + 1) (Nat.le_succ _)
  have hDn : 3 ≤ 3 ^ Q * 2 ^ (e Q + 1) := by
    have h1 : 3 ^ 1 ≤ 3 ^ Q := Nat.pow_le_pow_right (by norm_num) hQ
    have h2 : 1 ≤ 2 ^ (e Q + 1) := Nat.one_le_two_pow
    nlinarith
  have hDcast : ((3 ^ Q * 2 ^ (e Q + 1) : ℕ) : ℝ) = 3 ^ Q * 2 ^ (e Q + 1) := by
    push_cast; rfl
  rw [hDcast]
  have hD3' : (3 : ℝ) ≤ ((3 ^ Q * 2 ^ (e Q + 1) : ℕ) : ℝ) := by exact_mod_cast hDn
  rw [hDcast] at hD3'
  have hDhalf : (3 : ℝ) ^ Q * 2 ^ (e Q) = 3 ^ Q * 2 ^ (e Q + 1) / 2 := by
    rw [pow_succ]; ring
  have hD9 : (3 : ℝ) ^ Q * 2 ^ (e Q + 1) ≤ 2 * 9 ^ Q := by
    have h := approx_two_pow_e_le Q
    have h3 : (0 : ℝ) < 3 ^ Q := by positivity
    have : (9 : ℝ) ^ Q = 3 ^ Q * 3 ^ Q := by
      rw [← mul_pow]; norm_num
    rw [this, pow_succ]
    nlinarith [mul_le_mul_of_nonneg_left h h3.le]
  generalize hDdef : (3 : ℝ) ^ Q * 2 ^ (e Q + 1) = D at *
  have hD0 : 0 < D := by linarith
  have hD1 : 0 < D - 1 := by linarith
  -- the defect function
  set g : ℕ → ℝ := fun j => t (j + Q) - t j / D with hgdef
  have hgU : ∀ j, e (j + Q) = e j + e Q → g j = t j / D := by
    intro j h
    simp only [hgdef, approx_t_shift_eq h, hDhalf]
    field_simp
    ring
  have hgS : ∀ j, e (j + Q) = e j + e Q + 1 → g j = 0 := by
    intro j h
    simp only [hgdef, approx_t_shift_succ h, hDhalf]
    field_simp
    ring
  have htD : ∀ j, 0 < t j / D := fun j => div_pos (approx_t_pos j) hD0
  have hg0 : ∀ j, 0 ≤ g j := by
    intro j
    rcases hstep j Q with h | h
    · rw [hgU j h]; exact (htD j).le
    · rw [hgS j h]
  have hgle : ∀ j, g j ≤ t j / D := by
    intro j
    rcases hstep j Q with h | h
    · rw [hgU j h]
    · rw [hgS j h]; exact (htD j).le
  have hpos : ∃ j, Q + K ≤ j ∧ 0 < g j := by
    obtain ⟨j, hj1, hj⟩ := hnp Q hQ
    refine ⟨j, ?_, ?_⟩
    · by_contra hlt
      have := hL j hj1 (not_le.1 hlt)
      omega
    · rw [hgU j hj]; exact htD j
  obtain ⟨hg, hEpos, hEle⟩ := approx_tail_core (Q + K) hsum hg0 hgle hpos
  have htQ : Summable (fun j => t (j + Q)) := (summable_nat_add_iff Q).2 hsum
  have hsplit := hg.sum_add_tsum_nat_add (Q + K)
  have he0 : e (0 + Q) = e 0 + e Q := by simp [e]
  have hfin : ∑ i ∈ Finset.range (Q + K), g i = 1 / D := by
    rw [Finset.sum_eq_single 0]
    · rw [hgU 0 he0, approx_t_zero]
    · intro i hi hi0
      exact hgS i (hL i (Nat.pos_of_ne_zero hi0) (Finset.mem_range.1 hi))
    · intro h
      exact absurd (Finset.mem_range.2 (by omega)) h
  have hgsum : ∑' j, g j = ∑' j, t (j + Q) - S2 / D := by
    simp only [hgdef]
    rw [htQ.tsum_sub (hsum.div_const D), tsum_div_const]
  have hS2 : S2 = ∑ j ∈ Finset.range Q, t j + ∑' j, t (j + Q) :=
    (hsum.sum_add_tsum_nat_add Q).symm
  have hE : ∑' j, g (j + (Q + K)) =
      (S2 - ∑ j ∈ Finset.range Q, t j) - S2 / D - 1 / D := by
    rw [hfin] at hsplit
    have h2 : ∑' j, g (j + (Q + K)) = ∑' j, g j - 1 / D := by linarith
    rw [h2, hgsum, hS2]; ring
  have hXle : (∑' j, g (j + (Q + K))) * D ≤ ∑' j, t (j + (Q + K)) :=
    (le_div_iff₀ hD0).1 hEle
  have key : S2 - (((∑ j ∈ Finset.range Q, 3 ^ (Q - j) * 2 ^ (e Q + 1 - e j)) + 1 : ℕ) : ℝ)
        / (D - 1) = (∑' j, g (j + (Q + K))) * D / (D - 1) := by
    rw [Nat.cast_add, hc, hE]
    push_cast
    field_simp
    ring
  rw [key]
  have hX0 : 0 < (∑' j, g (j + (Q + K))) * D := mul_pos hEpos hD0
  obtain ⟨h1, h2⟩ := approx_final hK hQ hD3' hD9 hX0 (lt_of_le_of_lt hXle (htail (Q + K)))
  exact ⟨by omega, div_pos hX0 hD1, h1, h2⟩

/-- **L14**, absolute-value form. -/
theorem approx_U_abs
    (he_mono : Monotone e)
    (hstep : ∀ j Q, e (j + Q) = e j + e Q ∨ e (j + Q) = e j + e Q + 1)
    (hsum : Summable t)
    (htail : ∀ J : ℕ, ∑' j, t (j + J) < (9 / 4) / 9 ^ J)
    (hnp : ∀ Q, 1 ≤ Q → ∃ j, e (j + Q) = e j + e Q + 1)
    {K Q : ℕ} (hK : 1 ≤ K) (hQ : 1 ≤ Q)
    (hU : ∀ j, j < Q + K → e (j + Q) = e j + e Q) :
    ∃ c D : ℕ, 2 ≤ D ∧ 0 < (c : ℝ) / ((D : ℝ) - 1) - S2 ∧
      ((D : ℝ) - 1) ^ 2 * |(c : ℝ) / ((D : ℝ) - 1) - S2| < 9 / 9 ^ K ∧
      |(c : ℝ) / ((D : ℝ) - 1) - S2| < 1 / 20 := by
  obtain ⟨c, D, hD, h0, h1, h2⟩ := approx_U he_mono hstep hsum htail hnp hK hQ hU
  refine ⟨c, D, hD, h0, ?_, ?_⟩
  · rw [abs_of_pos h0]; exact h1
  · rw [abs_of_pos h0]; exact h2

/-- **L15**, absolute-value form. -/
theorem approx_L_abs
    (he_mono : Monotone e)
    (hstep : ∀ j Q, e (j + Q) = e j + e Q ∨ e (j + Q) = e j + e Q + 1)
    (hsum : Summable t)
    (htail : ∀ J : ℕ, ∑' j, t (j + J) < (9 / 4) / 9 ^ J)
    (hnp : ∀ Q, 1 ≤ Q → ∃ j, 1 ≤ j ∧ e (j + Q) = e j + e Q)
    {K Q : ℕ} (hK : 1 ≤ K) (hQ : 1 ≤ Q)
    (hL : ∀ j, 1 ≤ j → j < Q + K → e (j + Q) = e j + e Q + 1) :
    ∃ c D : ℕ, 2 ≤ D ∧ 0 < S2 - (c : ℝ) / ((D : ℝ) - 1) ∧
      ((D : ℝ) - 1) ^ 2 * |(c : ℝ) / ((D : ℝ) - 1) - S2| < 9 / 9 ^ K ∧
      |(c : ℝ) / ((D : ℝ) - 1) - S2| < 1 / 20 := by
  obtain ⟨c, D, hD, h0, h1, h2⟩ := approx_L he_mono hstep hsum htail hnp hK hQ hL
  refine ⟨c, D, hD, h0, ?_, ?_⟩
  · rw [abs_sub_comm, abs_of_pos h0]; exact h1
  · rw [abs_sub_comm, abs_of_pos h0]; exact h2


/-- **Step F combined** (L12 + L13 + L14 + L15): for every `K ≥ 1` a good approximation exists. -/
theorem approx_exists
    (he_mono : Monotone e)
    (hstep : ∀ j Q, e (j + Q) = e j + e Q ∨ e (j + Q) = e j + e Q + 1)
    (hsum : Summable t)
    (htail : ∀ J : ℕ, ∑' j, t (j + J) < (9 / 4) / 9 ^ J)
    (K : ℕ) (hK : 1 ≤ K) :
    ∃ c D : ℕ, 2 ≤ D ∧ (c : ℝ) / ((D : ℝ) - 1) - S2 ≠ 0 ∧
      ((D : ℝ) - 1) ^ 2 * |(c : ℝ) / ((D : ℝ) - 1) - S2| < 9 / 9 ^ K ∧
      |(c : ℝ) / ((D : ℝ) - 1) - S2| < 1 / 20 := by
  obtain ⟨Q, hQ, hU | hL⟩ := key K hK
  · obtain ⟨c, D, hD, h0, h1, h2⟩ :=
      approx_U_abs he_mono hstep hsum htail exists_e_add_eq_succ hK hQ hU
    exact ⟨c, D, hD, h0.ne', h1, h2⟩
  · obtain ⟨c, D, hD, h0, h1, h2⟩ :=
      approx_L_abs he_mono hstep hsum htail exists_e_add_eq hK hQ hL
    refine ⟨c, D, hD, ?_, h1, h2⟩
    intro h
    linarith


-- ## L7: the series as a product

theorem lcm_term (i j n : ℕ) (h : a P23 n = 2 ^ i * 3 ^ j) :
    (1 : ℝ) / (partialLcm P23 (n + 1)) = 1 / ((2 : ℝ) ^ i * (3 : ℝ) ^ (f i)) * t j := by
  rw [partialLcm_succ, h, log2_smooth, log3_smooth]
  unfold t
  push_cast
  rw [pow_add, pow_add]
  field_simp

theorem series_formula :
    Summable (fun n => (1 : ℝ) / (partialLcm P23 n)) ∧ series P23 = 1 + S1 * S2 := by
  classical
  have hmem : ∀ k, HasPrimeFactorsIn P23 (a P23 k) := Nat.nth_mem_of_infinite smooth_infinite
  let φ : ℕ × ℕ → ℕ := fun z => Nat.count (HasPrimeFactorsIn P23) (2 ^ z.1 * 3 ^ z.2)
  have hφ : ∀ z, a P23 (φ z) = 2 ^ z.1 * 3 ^ z.2 := fun z => Nat.nth_count (smooth_of_pow z.1 z.2)
  have hbij : Function.Bijective φ := by
    constructor
    · intro z w h
      have h' : 2 ^ z.1 * 3 ^ z.2 = 2 ^ w.1 * 3 ^ w.2 := by rw [← hφ z, ← hφ w, h]
      exact Prod.ext (pow_inj h').1 (pow_inj h').2
    · intro n
      obtain ⟨i, j, hij⟩ := pow_of_smooth _ (hmem n)
      refine ⟨(i, j), ?_⟩
      apply Nat.nth_injective smooth_infinite
      show a P23 (φ (i, j)) = a P23 n
      rw [hφ, hij]
  let E : ℕ × ℕ ≃ ℕ := Equiv.ofBijective φ hbij
  let F : ℕ × ℕ → ℝ := fun z => 1 / ((2 : ℝ) ^ z.1 * (3 : ℝ) ^ (f z.1)) * t z.2
  have hF : Summable F :=
    Summable.mul_of_nonneg s1_summable t_summable
      (fun i => by show (0 : ℝ) ≤ 1 / ((2 : ℝ) ^ i * (3 : ℝ) ^ (f i)); positivity)
      (fun j => (t_pos j).le)
  have hterm : ∀ z, (1 : ℝ) / (partialLcm P23 (E z + 1)) = F z :=
    fun z => lcm_term z.1 z.2 _ (hφ z)
  have hsum1 : Summable (fun n => (1 : ℝ) / (partialLcm P23 (n + 1))) := by
    rw [← Equiv.summable_iff E]
    exact hF.congr (fun z => (hterm z).symm)
  have hsum : Summable (fun n => (1 : ℝ) / (partialLcm P23 n)) :=
    (summable_nat_add_iff 1).mp hsum1
  refine ⟨hsum, ?_⟩
  have h1 : ∑' n, (1 : ℝ) / (partialLcm P23 (n + 1)) = ∑' z, F z := by
    rw [← Equiv.tsum_eq E (fun n => (1 : ℝ) / (partialLcm P23 (n + 1)))]
    exact tsum_congr hterm
  have h2 : S1 * S2 = ∑' z, F z := Summable.tsum_mul_tsum s1_summable t_summable hF
  unfold series
  rw [hsum.tsum_eq_zero_add, h1, ← h2, partialLcm_zero]
  norm_num

-- ## L8: S1 + 2 S2 = 4

theorem geom_Ico (m n : ℕ) (hmn : m ≤ n) :
    ∑ i ∈ Finset.Ico m n, (1 / 2 : ℝ) ^ i = 2 * (1 / 2) ^ m - 2 * (1 / 2) ^ n := by
  induction n, hmn using Nat.le_induction with
  | base => simp
  | succ n hn ih => rw [Finset.sum_Ico_succ_top hn, ih, pow_succ]; ring

theorem f_eq_of_mem (J i : ℕ) (h1 : e J < i) (h2 : i ≤ e (J + 1)) : f i = J := by
  unfold f
  rw [Nat.log_eq_iff (Or.inr ⟨by norm_num, by positivity⟩)]
  constructor
  · exact le_of_lt (lt_of_lt_of_le (e_spec J).2 (Nat.pow_le_pow_right (by norm_num) h1))
  · have hle : 2 ^ i ≤ 3 ^ (J + 1) :=
      le_trans (Nat.pow_le_pow_right (by norm_num) h2) (e_spec (J + 1)).1
    refine lt_of_le_of_ne hle ?_
    intro heq
    have h2d : 2 ∣ 2 ^ i := dvd_pow_self 2 (by omega)
    rw [heq] at h2d
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_two h2d
    omega

theorem s1_partial (J : ℕ) :
    ∑ i ∈ Finset.range (e J + 1), 1 / ((2 : ℝ) ^ i * (3 : ℝ) ^ (f i)) =
      1 + ∑ j ∈ Finset.range J, (t j - 3 * t (j + 1)) := by
  induction J with
  | zero => simp [e_zero, f]
  | succ J ih =>
    rw [Finset.sum_range_succ _ J, ← add_assoc, ← ih]
    have hle : e J + 1 ≤ e (J + 1) + 1 := by have := e_step J; omega
    rw [← Finset.sum_range_add_sum_Ico _ hle]
    congr 1
    have hc : ∀ i ∈ Finset.Ico (e J + 1) (e (J + 1) + 1),
        1 / ((2 : ℝ) ^ i * (3 : ℝ) ^ (f i)) = 1 / (3 : ℝ) ^ J * (1 / 2 : ℝ) ^ i := by
      intro i hi
      rw [Finset.mem_Ico] at hi
      rw [f_eq_of_mem J i (by omega) (by omega), one_div_pow]
      field_simp
    rw [Finset.sum_congr rfl hc, ← Finset.mul_sum, geom_Ico _ _ hle]
    unfold t
    simp only [one_div, inv_pow, pow_succ]
    field_simp

theorem S1_add_two_S2 : S1 + 2 * S2 = 4 := by
  have hA : Tendsto (fun J => ∑ i ∈ Finset.range (e J + 1), 1 / ((2 : ℝ) ^ i * (3 : ℝ) ^ (f i)))
      atTop (𝓝 S1) := by
    have h := s1_summable.hasSum.tendsto_sum_nat
    have hT : Tendsto (fun J => e J + 1) atTop atTop :=
      tendsto_atTop_mono (fun J => by have := e_ge J; show J ≤ e J + 1; omega) tendsto_id
    exact h.comp hT
  have hs1 : Summable (fun j => 3 * t (j + 1)) :=
    ((summable_nat_add_iff 1).mpr t_summable).mul_left 3
  have hs3 : Summable (fun j => t j - 3 * t (j + 1)) := t_summable.sub hs1
  have hB := (hs3.hasSum.tendsto_sum_nat).const_add 1
  have heq : (fun J => ∑ i ∈ Finset.range (e J + 1), 1 / ((2 : ℝ) ^ i * (3 : ℝ) ^ (f i))) =
      fun J => 1 + ∑ j ∈ Finset.range J, (t j - 3 * t (j + 1)) := funext s1_partial
  rw [heq] at hA
  have hu := tendsto_nhds_unique hA hB
  have ht0 : t 0 = 1 := by unfold t; rw [e_zero]; norm_num
  have h0 : S2 = t 0 + ∑' j, t (j + 1) := t_summable.tsum_eq_zero_add
  have h1 : ∑' j, (t j - 3 * t (j + 1)) = S2 - 3 * ∑' j, t (j + 1) := by
    rw [Summable.tsum_sub t_summable hs1, tsum_mul_left]
  rw [h1] at hu
  linarith

-- ## L9: the series as a quadratic in S2

theorem series_quadratic : series P23 = 1 + 4 * S2 - 2 * S2 ^ 2 := by
  have h1 := series_formula.2
  have h2 : S1 = 4 - 2 * S2 := by linarith [S1_add_two_S2]
  rw [h1, h2]; ring

-- ## L16, L17: the series for {2, 3} is irrational

theorem not_rational : ¬ ∃ q : ℚ, (q : ℝ) = series P23 := by
  rintro ⟨q, hq⟩
  obtain ⟨c, D, hD, hne, hsmall, h20⟩ :=
    approx_exists e_mono e_add t_summable t_tail (q.den + 1) (by omega)
  obtain ⟨hlo, hhi⟩ := S2_bounds
  have hD' : (2 : ℝ) ≤ D := by exact_mod_cast hD
  have hd : (1 : ℝ) ≤ (D : ℝ) - 1 := by linarith
  have hd0 : (D : ℝ) - 1 ≠ 0 := by linarith
  have hb : (0 : ℝ) < q.den := by exact_mod_cast q.den_pos
  have hx : (q : ℝ) - (1 + 4 * ((c : ℝ) / ((D : ℝ) - 1)) - 2 * ((c : ℝ) / ((D : ℝ) - 1)) ^ 2) =
      ((c : ℝ) / ((D : ℝ) - 1) - S2) * (2 * (S2 + (c : ℝ) / ((D : ℝ) - 1)) - 4) := by
    rw [hq, series_quadratic]; ring
  have hqr : (q : ℝ) = (q.num : ℝ) / (q.den : ℝ) := by
    exact_mod_cast (Rat.num_div_den q).symm
  have hZ : (((q.num * ((D : ℤ) - 1) ^ 2 -
      q.den * (((D : ℤ) - 1) ^ 2 + 4 * c * ((D : ℤ) - 1) - 2 * c ^ 2) : ℤ)) : ℝ) =
      q.den * ((D : ℝ) - 1) ^ 2 *
        ((q : ℝ) - (1 + 4 * ((c : ℝ) / ((D : ℝ) - 1)) - 2 * ((c : ℝ) / ((D : ℝ) - 1)) ^ 2)) := by
    rw [hqr]; push_cast; field_simp
  rw [hx] at hZ
  rw [abs_lt] at h20
  have hf1 : 2 * (S2 + (c : ℝ) / ((D : ℝ) - 1)) - 4 < 1 := by linarith
  have hf2 : 0 < 2 * (S2 + (c : ℝ) / ((D : ℝ) - 1)) - 4 := by linarith
  have hZne : (q.num * ((D : ℤ) - 1) ^ 2 -
      q.den * (((D : ℤ) - 1) ^ 2 + 4 * c * ((D : ℤ) - 1) - 2 * c ^ 2) : ℤ) ≠ 0 := by
    intro h0
    rw [h0, Int.cast_zero] at hZ
    have : q.den * ((D : ℝ) - 1) ^ 2 *
        (((c : ℝ) / ((D : ℝ) - 1) - S2) * (2 * (S2 + (c : ℝ) / ((D : ℝ) - 1)) - 4)) ≠ 0 :=
      mul_ne_zero (mul_ne_zero hb.ne' (pow_ne_zero 2 hd0)) (mul_ne_zero hne hf2.ne')
    exact this hZ.symm
  have habs : (1 : ℝ) ≤ |(((q.num * ((D : ℤ) - 1) ^ 2 -
      q.den * (((D : ℤ) - 1) ^ 2 + 4 * c * ((D : ℤ) - 1) - 2 * c ^ 2) : ℤ)) : ℝ)| := by
    rw [← Int.cast_abs]
    exact_mod_cast Int.one_le_abs hZne
  rw [hZ, abs_mul, abs_mul, abs_mul, abs_of_pos hb, abs_of_pos (by positivity : (0:ℝ) < ((D : ℝ) - 1) ^ 2),
    abs_of_pos hf2] at habs
  have hpos : 0 < |(c : ℝ) / ((D : ℝ) - 1) - S2| := abs_pos.mpr hne
  have hden : (q.den : ℝ) < 9 ^ q.den := by exact_mod_cast Nat.lt_pow_self (by norm_num : 1 < 9)
  have h9 : (0 : ℝ) < 9 ^ q.den := by positivity
  have hK : (9 : ℝ) / 9 ^ (q.den + 1) = 1 / 9 ^ q.den := by rw [pow_succ]; field_simp
  rw [hK] at hsmall
  have hbs : (q.den : ℝ) * (((D : ℝ) - 1) ^ 2 * |(c : ℝ) / ((D : ℝ) - 1) - S2|) < 1 := by
    calc (q.den : ℝ) * (((D : ℝ) - 1) ^ 2 * |(c : ℝ) / ((D : ℝ) - 1) - S2|)
        < q.den * (1 / 9 ^ q.den) := mul_lt_mul_of_pos_left hsmall hb
      _ = q.den / 9 ^ q.den := by ring
      _ < 1 := (div_lt_one h9).mpr hden
  have hprod : 0 < (q.den : ℝ) * (((D : ℝ) - 1) ^ 2 * |(c : ℝ) / ((D : ℝ) - 1) - S2|) := by positivity
  nlinarith

end E269

theorem OMA.disproof : ¬ (type_of% @Erdos269.erdos_269.variants.rational) := by
  intro h
  have h23 := h {2, 3}
    (by intro p hp; simp at hp; rcases hp with rfl | rfl <;> norm_num)
    (by decide)
  exact E269.not_rational h23
