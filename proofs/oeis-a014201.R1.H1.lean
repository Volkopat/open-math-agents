import OMAReductions.R_oeis_a014201_R1
import Mathlib

-- Credit: @ptc-prover-bot
/-!
Step H1 of reduction oeis-a014201.R1: the Gauss-type bound
a(n) = (2 π / √3) n + O(√n) for the lattice points with x² + x y + y² ≤ n.

Proof idea (column counting). Since 4 (x² + x y + y²) = (2 x + y)² + 3 y², for a fixed y the
admissible x are those with |2 x + y| ≤ s, where s = ⌊√(4 n − 3 y²)⌋; there are s or s + 1 of them.
With r = √(4 n / 3) we have √(4 n − 3 y²) = √3 · √(r² − y²), and the columns are |y| ≤ ⌊r⌋.
The quarter-disc comparison Σ_{j<⌊r⌋} √(r² − (j+1)²) = π r² / 4 + O(r) (antitone sum against
integral) gives the main term √3 π r² / 2 = 2 π n / √3 with error O(r) = O(√n).
The disc lemmas (g, quarter, sum_bounds, sum_even, col_iff) are copied from the compiled
module hilbert-db lemmas/NumberTheory/GaussCircle.lean (own work, textbook Gauss circle proof).
-/

open Finset Real intervalIntegral

namespace A014201Proof

noncomputable def g (r x : ℝ) : ℝ := √(r ^ 2 - x ^ 2)

lemma g_anti (r : ℝ) : AntitoneOn (g r) (Set.Ici 0) := by
  intro x hx y hy hxy
  apply Real.sqrt_le_sqrt
  have : x ^ 2 ≤ y ^ 2 := pow_le_pow_left₀ hx hxy 2
  linarith

lemma g_cont (r : ℝ) : Continuous (g r) := by unfold g; fun_prop

lemma g_le (r x : ℝ) (hr : 0 ≤ r) : g r x ≤ r := by
  unfold g
  calc √(r ^ 2 - x ^ 2) ≤ √(r ^ 2) := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg x])
    _ = r := Real.sqrt_sq hr

lemma g_nonneg (r x : ℝ) : 0 ≤ g r x := Real.sqrt_nonneg _

lemma g_even (r x : ℝ) : g r (-x) = g r x := by simp [g]

lemma quarter (r : ℝ) (hr : 0 < r) : ∫ x in (0 : ℝ)..r, g r x = π * r ^ 2 / 4 := by
  have hfull : ∫ x in (-r)..r, g r x = π * r ^ 2 / 2 := by
    have h1 : ∫ u in (-1 : ℝ)..1, g r (r * u) = r * (π / 2) := by
      rw [← integral_sqrt_one_sub_sq, ← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro u _
      simp only [g]
      rw [show r ^ 2 - (r * u) ^ 2 = r ^ 2 * (1 - u ^ 2) by ring,
        Real.sqrt_mul (by positivity), Real.sqrt_sq hr.le]
    rw [intervalIntegral.integral_comp_mul_left (g r) hr.ne'] at h1
    simp only [mul_neg, mul_one, smul_eq_mul] at h1
    field_simp at h1
    linarith
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    ((g_cont r).intervalIntegrable (μ := MeasureTheory.volume) (-r) 0)
    ((g_cont r).intervalIntegrable (μ := MeasureTheory.volume) 0 r)
  have hneg : ∫ x in (-r)..0, g r x = ∫ x in (0 : ℝ)..r, g r x := by
    have := intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := r) (g r)
    simp only [g_even, neg_zero] at this
    linarith
  linarith

lemma sum_bounds (r : ℝ) (hr : 0 < r) (R : ℕ) (hR : (R : ℝ) ≤ r) (hR1 : r < R + 1) :
    (∫ x in (0 : ℝ)..r, g r x) - r ≤ ∑ j ∈ range R, g r (j + 1) ∧
      ∑ j ∈ range R, g r (j + 1) ≤ ∫ x in (0 : ℝ)..r, g r x := by
  have hint : ∀ a b : ℝ, IntervalIntegrable (g r) MeasureTheory.volume a b :=
    fun a b => (g_cont r).intervalIntegrable a b
  have hanti : ∀ x₀ : ℝ, 0 ≤ x₀ → ∀ a : ℕ, AntitoneOn (g r) (Set.Icc x₀ (x₀ + a)) :=
    fun x₀ h a => (g_anti r).mono (fun x hx => le_trans h hx.1)
  constructor
  · have h1 := (hanti 1 zero_le_one R).integral_le_sum
    have e1 : ∑ i ∈ range R, g r (1 + (i : ℝ)) = ∑ j ∈ range R, g r (j + 1) := by
      apply sum_congr rfl; intro i _; rw [add_comm]
    rw [e1] at h1
    have h2 : ∫ x in (0 : ℝ)..r, g r x ≤ ∫ x in (0 : ℝ)..(1 + (R : ℝ)), g r x := by
      rw [← intervalIntegral.integral_add_adjacent_intervals (hint 0 r) (hint r (1 + (R : ℝ)))]
      have : 0 ≤ ∫ x in r..(1 + (R : ℝ)), g r x :=
        intervalIntegral.integral_nonneg (by linarith) (fun x _ => g_nonneg r x)
      linarith
    have h3 : (∫ x in (0 : ℝ)..1, g r x) + (∫ x in (1 : ℝ)..(1 + (R : ℝ)), g r x) =
        ∫ x in (0 : ℝ)..(1 + (R : ℝ)), g r x :=
      intervalIntegral.integral_add_adjacent_intervals (hint 0 1) (hint 1 (1 + (R : ℝ)))
    have h1' : ∫ x in (1 : ℝ)..(1 + (R : ℝ)), g r x ≤ ∑ j ∈ range R, g r (j + 1) := h1
    have h4 : ∫ x in (0 : ℝ)..1, g r x ≤ r := by
      have := intervalIntegral.integral_mono_on zero_le_one (hint 0 1) intervalIntegrable_const
        (fun x _ => g_le r x hr.le)
      simpa using this
    have k : ∫ x in (0 : ℝ)..r, g r x ≤ r + ∑ j ∈ range R, g r (j + 1) :=
      calc ∫ x in (0 : ℝ)..r, g r x ≤ ∫ x in (0 : ℝ)..(1 + (R : ℝ)), g r x := h2
        _ = (∫ x in (0 : ℝ)..1, g r x) + (∫ x in (1 : ℝ)..(1 + (R : ℝ)), g r x) := h3.symm
        _ ≤ r + ∑ j ∈ range R, g r (j + 1) := add_le_add h4 h1'
    linarith
  · have h1 := (hanti 0 le_rfl R).sum_le_integral
    simp only [zero_add] at h1
    have e1 : ∑ i ∈ range R, g r ((↑(i + 1) : ℝ)) = ∑ j ∈ range R, g r (j + 1) := by
      apply sum_congr rfl; intro i _; push_cast; rfl
    rw [e1] at h1
    have h2 : ∫ x in (0 : ℝ)..R, g r x ≤ ∫ x in (0 : ℝ)..r, g r x := by
      rw [← intervalIntegral.integral_add_adjacent_intervals (hint 0 R) (hint R r)]
      have : 0 ≤ ∫ x in (R : ℝ)..r, g r x :=
        intervalIntegral.integral_nonneg hR (fun x _ => g_nonneg r x)
      linarith
    linarith

lemma sum_even (F : ℤ → ℝ) (hF : ∀ m, F (-m) = F m) (R : ℕ) :
    ∑ m ∈ Icc (-(R : ℤ)) R, F m = F 0 + 2 * ∑ j ∈ range R, F (j + 1) := by
  induction R with
  | zero => simp
  | succ R ih =>
    have hset : Icc (-((R + 1 : ℕ) : ℤ)) ((R + 1 : ℕ) : ℤ) =
        insert (-((R : ℤ) + 1)) (insert ((R : ℤ) + 1) (Icc (-(R : ℤ)) R)) := by
      ext x; simp only [mem_insert, mem_Icc]; push_cast; omega
    rw [hset, sum_insert (by simp only [mem_insert, mem_Icc]; omega),
      sum_insert (by simp only [mem_Icc]; omega), ih, sum_range_succ, hF]
    push_cast; ring

lemma col_iff (s : ℝ) (hs : 0 ≤ s) (n : ℤ) : (n : ℝ) ^ 2 ≤ s ↔ |n| ≤ ⌊√s⌋ := by
  rw [Int.le_floor]
  push_cast
  constructor
  · intro h
    calc (|n| : ℝ) = √((n : ℝ) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
      _ ≤ √s := Real.sqrt_le_sqrt h
  · intro h
    have h0 : (0 : ℝ) ≤ |(n : ℝ)| := abs_nonneg _
    calc (n : ℝ) ^ 2 = |(n : ℝ)| ^ 2 := (sq_abs _).symm
      _ ≤ (√s) ^ 2 := pow_le_pow_left₀ h0 h 2
      _ = s := Real.sq_sqrt hs

/-! ## The ellipse `x² + x y + y² ≤ n` by columns -/

/-- Radius of the comparison disc: `r² = 4 n / 3`. -/
noncomputable def rad (n : ℕ) : ℝ := √((4 * n : ℝ) / 3)

/-- Number of columns on each side. -/
noncomputable def Rn (n : ℕ) : ℕ := ⌊rad n⌋₊

/-- Column half-height in the variable `2 x + y`. -/
noncomputable def s (n : ℕ) (y : ℤ) : ℤ := ⌊√((4 * n : ℝ) - 3 * (y : ℝ) ^ 2)⌋

noncomputable def lo (n : ℕ) (y : ℤ) : ℤ := -((s n y + y) / 2)

noncomputable def hi (n : ℕ) (y : ℤ) : ℤ := (s n y - y) / 2

noncomputable def col (n : ℕ) (y : ℤ) : Finset (ℤ × ℤ) :=
  (Icc (lo n y) (hi n y)).image (fun x => (x, y))

noncomputable def T (n : ℕ) : Finset (ℤ × ℤ) := (Icc (-(Rn n : ℤ)) (Rn n)).biUnion (col n)

lemma key (n : ℕ) (x y : ℤ) :
    x ^ 2 + x * y + y ^ 2 ≤ (n : ℤ) ↔ ((2 * x + y : ℤ) : ℝ) ^ 2 ≤ (4 * n : ℝ) - 3 * (y : ℝ) ^ 2 := by
  have e : ((2 * x + y : ℤ) : ℝ) ^ 2 = 4 * ((x ^ 2 + x * y + y ^ 2 : ℤ) : ℝ) - 3 * (y : ℝ) ^ 2 := by
    push_cast; ring
  rw [e]
  constructor
  · intro h
    have : ((x ^ 2 + x * y + y ^ 2 : ℤ) : ℝ) ≤ ((n : ℤ) : ℝ) := Int.cast_le.mpr h
    rw [Int.cast_natCast] at this
    linarith
  · intro h
    have : ((x ^ 2 + x * y + y ^ 2 : ℤ) : ℝ) ≤ ((n : ℤ) : ℝ) := by
      rw [Int.cast_natCast]; linarith
    exact Int.cast_le.mp this

lemma D_iff (n : ℕ) (y : ℤ) : 0 ≤ (4 * n : ℝ) - 3 * (y : ℝ) ^ 2 ↔ |y| ≤ (Rn n : ℤ) := by
  have h0 : (0 : ℝ) ≤ (4 * n : ℝ) / 3 := by positivity
  have e : ((Rn n : ℕ) : ℤ) = ⌊rad n⌋ := Int.natCast_floor_eq_floor (Real.sqrt_nonneg _)
  rw [e, rad, ← col_iff _ h0]
  constructor <;> intro h <;> linarith

lemma mem_col_iff (n : ℕ) (x y : ℤ) (hD : 0 ≤ (4 * n : ℝ) - 3 * (y : ℝ) ^ 2) :
    x ^ 2 + x * y + y ^ 2 ≤ (n : ℤ) ↔ lo n y ≤ x ∧ x ≤ hi n y := by
  have h2 : ((2 * x + y : ℤ) : ℝ) ^ 2 ≤ (4 * n : ℝ) - 3 * (y : ℝ) ^ 2 ↔ |2 * x + y| ≤ s n y :=
    col_iff _ hD _
  rw [key, h2, abs_le]
  unfold lo hi
  omega

lemma setT (n : ℕ) :
    {v : ℤ × ℤ | v.1 ^ 2 + v.1 * v.2 + v.2 ^ 2 ≤ (n : ℤ)} = ((T n : Finset (ℤ × ℤ)) : Set (ℤ × ℤ)) := by
  ext ⟨x, y⟩
  simp only [Set.mem_ofPred_eq, Finset.mem_coe, T, Finset.mem_biUnion, col, Finset.mem_image,
    Finset.mem_Icc, Prod.mk.injEq]
  constructor
  · intro h
    have hD : 0 ≤ (4 * n : ℝ) - 3 * (y : ℝ) ^ 2 := by
      have := (key n x y).mp h
      nlinarith [sq_nonneg ((2 * x + y : ℤ) : ℝ)]
    have hy := abs_le.mp ((D_iff n y).mp hD)
    exact ⟨y, ⟨hy.1, hy.2⟩, x, (mem_col_iff n x y hD).mp h, rfl, rfl⟩
  · rintro ⟨y', ⟨h1, h2⟩, x', hx', rfl, rfl⟩
    have hD := (D_iff n y').mpr (abs_le.mpr ⟨h1, h2⟩)
    exact (mem_col_iff n x' y' hD).mpr hx'

lemma card_T (n : ℕ) : ((T n).card : ℝ) =
    ∑ y ∈ Icc (-(Rn n : ℤ)) (Rn n), (((hi n y + 1 - lo n y).toNat : ℕ) : ℝ) := by
  unfold T
  rw [card_biUnion]
  · rw [Nat.cast_sum]
    apply sum_congr rfl
    intro y _
    unfold col
    rw [card_image_of_injective _ (fun a b hab => (Prod.mk.inj hab).1), Int.card_Icc]
  · intro a _ b _ hab
    rw [Function.onFun, disjoint_left]
    intro v hva hvb
    obtain ⟨_, _, rfl⟩ := mem_image.mp hva
    obtain ⟨_, _, he⟩ := mem_image.mp hvb
    exact hab (Prod.mk.inj he).2.symm

lemma col_bounds (n : ℕ) (y : ℤ) (hD : 0 ≤ (4 * n : ℝ) - 3 * (y : ℝ) ^ 2) :
    √((4 * n : ℝ) - 3 * (y : ℝ) ^ 2) - 1 ≤ (((hi n y + 1 - lo n y).toNat : ℕ) : ℝ) ∧
      (((hi n y + 1 - lo n y).toNat : ℕ) : ℝ) ≤ √((4 * n : ℝ) - 3 * (y : ℝ) ^ 2) + 1 := by
  have hs0 : 0 ≤ s n y := Int.floor_nonneg.mpr (Real.sqrt_nonneg _)
  have e : (((hi n y + 1 - lo n y).toNat : ℕ) : ℤ) = hi n y + 1 - lo n y :=
    Int.toNat_of_nonneg (by unfold hi lo; omega)
  have b1 : s n y ≤ hi n y + 1 - lo n y := by unfold hi lo; omega
  have b2 : hi n y + 1 - lo n y ≤ s n y + 1 := by unfold hi lo; omega
  have c : (((hi n y + 1 - lo n y).toNat : ℕ) : ℝ) = ((hi n y + 1 - lo n y : ℤ) : ℝ) := by
    have h := congrArg (fun z : ℤ => (z : ℝ)) e
    simpa only [Int.cast_natCast] using h
  have b1' : ((s n y : ℤ) : ℝ) ≤ ((hi n y + 1 - lo n y : ℤ) : ℝ) := Int.cast_le.mpr b1
  have b2' : ((hi n y + 1 - lo n y : ℤ) : ℝ) ≤ ((s n y : ℤ) : ℝ) + 1 := by exact_mod_cast b2
  have f1 : ((s n y : ℤ) : ℝ) ≤ √((4 * n : ℝ) - 3 * (y : ℝ) ^ 2) := Int.floor_le _
  have f2 : √((4 * n : ℝ) - 3 * (y : ℝ) ^ 2) < ((s n y : ℤ) : ℝ) + 1 := Int.lt_floor_add_one _
  rw [c]
  constructor <;> linarith

lemma sqrtD (n : ℕ) (y : ℤ) :
    √((4 * n : ℝ) - 3 * (y : ℝ) ^ 2) = √3 * g (rad n) (y : ℝ) := by
  unfold g
  rw [← Real.sqrt_mul (by norm_num)]
  congr 1
  rw [rad, Real.sq_sqrt (by positivity)]
  ring

theorem bound (n : ℕ) (hn : 1 ≤ n) :
    |(OMA.S_oeis_a014201.a n : ℝ) - 2 * (π / √3) * n| ≤ 10 * √(n : ℝ) := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hρ0 : 0 < rad n := Real.sqrt_pos.mpr (by positivity)
  have hρ2 : rad n ^ 2 = 4 * n / 3 := Real.sq_sqrt (by positivity)
  have hMr : (Rn n : ℝ) ≤ rad n := Nat.floor_le hρ0.le
  have hMr1 : rad n < Rn n + 1 := Nat.lt_floor_add_one (rad n)
  -- a n = #T - 1
  have h0T : ((0 : ℤ), (0 : ℤ)) ∈ T n := by
    have h : ((0 : ℤ), (0 : ℤ)) ∈ {v : ℤ × ℤ | v.1 ^ 2 + v.1 * v.2 + v.2 ^ 2 ≤ (n : ℤ)} := by
      simp
    rw [setT] at h
    exact Finset.mem_coe.mp h
  have hset : {v : ℤ × ℤ | v ≠ (0, 0) ∧ v.1 ^ 2 + v.1 * v.2 + v.2 ^ 2 ≤ (n : ℤ)} =
      (((T n).erase (0, 0) : Finset (ℤ × ℤ)) : Set (ℤ × ℤ)) := by
    rw [Finset.coe_erase, ← setT n]
    ext v
    simp only [Set.mem_ofPred_eq, Set.mem_sdiff, Set.mem_singleton_iff]
    tauto
  have ha : OMA.S_oeis_a014201.a n = (T n).card - 1 := by
    unfold OMA.S_oeis_a014201.a
    rw [hset, Set.ncard_coe_finset, card_erase_of_mem h0T]
  have hpos : 1 ≤ (T n).card := Finset.card_pos.mpr ⟨_, h0T⟩
  have ha' : (OMA.S_oeis_a014201.a n : ℝ) = ((T n).card : ℝ) - 1 := by
    rw [ha, Nat.cast_sub hpos, Nat.cast_one]
  -- column sums
  set I := Icc (-(Rn n : ℤ)) (Rn n) with hIdef
  have hI : (I.card : ℝ) = 2 * Rn n + 1 := by
    have : I.card = 2 * Rn n + 1 := by rw [hIdef, Int.card_Icc]; omega
    rw [this]; push_cast; ring
  have hcol : ∀ y ∈ I, √3 * g (rad n) (y : ℝ) - 1 ≤ (((hi n y + 1 - lo n y).toNat : ℕ) : ℝ) ∧
      (((hi n y + 1 - lo n y).toNat : ℕ) : ℝ) ≤ √3 * g (rad n) (y : ℝ) + 1 := by
    intro y hy
    have hD : 0 ≤ (4 * n : ℝ) - 3 * (y : ℝ) ^ 2 :=
      (D_iff n y).mpr (abs_le.mpr (Finset.mem_Icc.mp hy))
    rw [← sqrtD]
    exact col_bounds n y hD
  have hup : ((T n).card : ℝ) ≤ ∑ y ∈ I, √3 * g (rad n) (y : ℝ) + I.card := by
    rw [card_T]
    calc ∑ y ∈ I, (((hi n y + 1 - lo n y).toNat : ℕ) : ℝ)
        ≤ ∑ y ∈ I, (√3 * g (rad n) (y : ℝ) + 1) := sum_le_sum (fun y hy => (hcol y hy).2)
      _ = _ := by rw [sum_add_distrib]; simp
  have hlow : ∑ y ∈ I, √3 * g (rad n) (y : ℝ) - I.card ≤ ((T n).card : ℝ) := by
    rw [card_T]
    calc ∑ y ∈ I, √3 * g (rad n) (y : ℝ) - I.card
        = ∑ y ∈ I, (√3 * g (rad n) (y : ℝ) - 1) := by rw [sum_sub_distrib]; simp
      _ ≤ _ := sum_le_sum (fun y hy => (hcol y hy).1)
  have heven := sum_even (fun m : ℤ => g (rad n) (m : ℝ))
    (by intro m; push_cast; exact g_even _ _) (Rn n)
  have ecast : ∀ j : ℕ, g (rad n) (((j : ℤ) + 1 : ℤ) : ℝ) = g (rad n) ((j : ℝ) + 1) := by
    intro j; push_cast; rfl
  simp only [ecast, Int.cast_zero] at heven
  have hg0 : g (rad n) 0 = rad n := by
    unfold g; simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, sub_zero]
    exact Real.sqrt_sq hρ0.le
  set G := ∑ j ∈ range (Rn n), g (rad n) ((j : ℝ) + 1) with hG
  have hsum : ∑ y ∈ I, √3 * g (rad n) (y : ℝ) = √3 * (rad n + 2 * G) := by
    rw [← mul_sum, hIdef, heven, hg0]
  obtain ⟨l, u⟩ := sum_bounds (rad n) hρ0 (Rn n) hMr hMr1
  have hq := quarter (rad n) hρ0
  rw [hq] at l u
  have s3 : (0 : ℝ) ≤ √3 := Real.sqrt_nonneg _
  have hs33 : √3 * √3 = 3 := Real.mul_self_sqrt (by norm_num)
  have s3le : √3 ≤ 2 := by
    have h4 : √(4 : ℝ) = 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    rw [← h4]; exact Real.sqrt_le_sqrt (by norm_num)
  have m1 : √3 * G ≤ √3 * (π * rad n ^ 2 / 4) := mul_le_mul_of_nonneg_left u s3
  have m2 : √3 * (π * rad n ^ 2 / 4 - rad n) ≤ √3 * G := mul_le_mul_of_nonneg_left l s3
  have m3 : √3 * rad n ≤ 2 * rad n := mul_le_mul_of_nonneg_right s3le hρ0.le
  have hmain : 2 * (π / √3) * n = √3 * (π * rad n ^ 2 / 4) * 2 := by
    have hne : √3 ≠ 0 := by positivity
    have e1 : π / √3 = √3 * π / 3 := by
      rw [div_eq_div_iff hne (by norm_num)]
      linear_combination (-π) * hs33
    rw [e1, hρ2]
    ring
  have hρle : rad n ≤ 2 * √(n : ℝ) := by
    have h4 : √(4 * (n : ℝ)) = 2 * √(n : ℝ) := by
      rw [Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num,
        Real.sqrt_sq (by norm_num)]
    rw [← h4, rad]
    exact Real.sqrt_le_sqrt (by linarith)
  have hsq1 : 1 ≤ √(n : ℝ) := Real.one_le_sqrt.mpr hn'
  rw [ha', hmain, abs_le]
  constructor <;> nlinarith

end A014201Proof

theorem OMA.solution : OMA.R_oeis_a014201_R1.H1 := by
  unfold OMA.R_oeis_a014201_R1.H1
  apply Asymptotics.IsBigO.of_bound 10
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _), ← Real.sqrt_eq_rpow]
  exact A014201Proof.bound n hn

