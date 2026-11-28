import OMAStatements.S_mo_18264
import Mathlib

open scoped BigOperators

namespace OMASequenceBlocks

noncomputable section

def blockRepeat (m : ℕ) [NeZero m] (a : ℝ) (x : ℕ → ℝ) (j : ℕ) : ℝ :=
  a * x ((Nat.divModEquiv m j).1)

def blockAverage (m : ℕ) [NeZero m] (a : ℝ) (x : ℕ → ℝ) (i : ℕ) : ℝ :=
  a * ∑ k : Fin m, x ((Nat.divModEquiv m).symm (i,k))

lemma blockAverage_repeat (m : ℕ) [NeZero m] {a : ℝ}
    (ha : (m : ℝ) * a ^ 2 = 1) (x : ℕ → ℝ) :
    blockAverage m a (blockRepeat m a x) = x := by
  funext i
  simp only [blockAverage, blockRepeat, Equiv.apply_symm_apply, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  linear_combination (x i) * ha

lemma blockAverage_sub (m : ℕ) [NeZero m] (a : ℝ) (x y : ℕ → ℝ) :
    blockAverage m a (x - y) = blockAverage m a x - blockAverage m a y := by
  funext i
  simp [blockAverage, Finset.sum_sub_distrib, mul_sub]

lemma blockRepeat_sub (m : ℕ) [NeZero m] (a : ℝ) (x y : ℕ → ℝ) :
    blockRepeat m a (x - y) = blockRepeat m a x - blockRepeat m a y := by
  funext i
  simp [blockRepeat, mul_sub]

lemma block_sum_eq (m : ℕ) [NeZero m] (f : ℕ → ℝ) (hf : Summable f) :
    (∑' i, ∑ k : Fin m, f ((Nat.divModEquiv m).symm (i,k))) = ∑' j, f j := by
  let e := Nat.divModEquiv m
  have h : Summable (fun ij : ℕ × Fin m => f (e.symm ij)) :=
    e.symm.summable_iff.mpr hf
  simpa only [tsum_fintype] using (h.tsum_prod' (fun _ => Summable.of_finite)).symm.trans
    (e.symm.tsum_eq f)

lemma block_sum_summable (m : ℕ) [NeZero m] (f : ℕ → ℝ)
    (h0 : ∀ i, 0 ≤ f i) (hf : Summable f) :
    Summable (fun i => ∑ k : Fin m, f ((Nat.divModEquiv m).symm (i,k))) := by
  let e := Nat.divModEquiv m
  have h : Summable (fun ij : ℕ × Fin m => f (e.symm ij)) :=
    e.symm.summable_iff.mpr hf
  simpa only [tsum_fintype] using
    ((summable_prod_of_nonneg (fun ij : ℕ × Fin m => h0 (e.symm ij))).1 h).2

lemma repeat_moment (m : ℕ) [NeZero m] {a : ℝ} (ha : 0 ≤ a)
    (p : ℕ) (x : ℕ → ℝ) (hx : Summable (fun i => |x i| ^ p)) :
    Summable (fun i => |blockRepeat m a x i| ^ p) ∧
    (∑' i, |blockRepeat m a x i| ^ p) = ((m : ℝ) * a ^ p) * ∑' i, |x i| ^ p := by
  let e := Nat.divModEquiv m
  have he (ij : ℕ × Fin m) :
      |blockRepeat m a x (e.symm ij)| ^ p = a ^ p * |x ij.1| ^ p := by
    change |a * x ((e (e.symm ij)).1)| ^ p = _
    rw [e.apply_symm_apply, abs_mul, abs_of_nonneg ha, mul_pow]
  have hb : Summable (fun ij : ℕ × Fin m => a ^ p * |x ij.1| ^ p) := by
    apply (summable_prod_of_nonneg (fun _ => by positivity)).2
    refine ⟨fun _ => Summable.of_finite, ?_⟩
    simpa only [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, ← mul_assoc] using hx.mul_left ((m : ℝ) * a ^ p)
  have hr : Summable (fun ij : ℕ × Fin m => |blockRepeat m a x (e.symm ij)| ^ p) :=
    hb.congr fun ij => (he ij).symm
  refine ⟨e.symm.summable_iff.mp hr, ?_⟩
  rw [← e.symm.tsum_eq (fun i => |blockRepeat m a x i| ^ p), tsum_congr he,
    hb.tsum_prod' (fun _ => Summable.of_finite)]
  simp only [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, ← mul_assoc, tsum_mul_left]

lemma average_moment (m : ℕ) [NeZero m] {a : ℝ} (ha : 0 ≤ a)
    {p : ℕ} (hp : 1 ≤ p) (x : ℕ → ℝ) (hx : Summable (fun i => |x i| ^ p)) :
    Summable (fun i => |blockAverage m a x i| ^ p) ∧
    (∑' i, |blockAverage m a x i| ^ p) ≤
      ((m : ℝ) ^ (p - 1) * a ^ p) * ∑' i, |x i| ^ p := by
  let C : ℝ := (m : ℝ) ^ (p - 1) * a ^ p
  let f (i : ℕ) := |x i| ^ p
  have hf : ∀ i, 0 ≤ f i := fun _ => by positivity
  have hC : 0 ≤ C := by positivity
  have h (i : ℕ) :
      |blockAverage m a x i| ^ p ≤ C * ∑ k : Fin m, f ((Nat.divModEquiv m).symm (i,k)) := by
    let g (k : Fin m) := x ((Nat.divModEquiv m).symm (i,k))
    have h1 : |∑ k, g k| ≤ ∑ k, |g k| := Finset.abs_sum_le_sum_abs _ _
    have h2 := Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg Finset.univ
      (f := fun k : Fin m => |g k|) (show (1 : ℝ) ≤ (p : ℝ) by exact_mod_cast hp)
      (fun k _ => abs_nonneg (g k))
    have hsub : (p : ℝ) - 1 = ((p - 1 : ℕ) : ℝ) := by
      rw [Nat.cast_sub hp]
      norm_num
    rw [hsub] at h2
    simp only [Real.rpow_natCast, Finset.card_univ, Fintype.card_fin] at h2
    change |a * ∑ k, g k| ^ p ≤ C * ∑ k, |g k| ^ p
    rw [abs_mul, abs_of_nonneg ha, mul_pow]
    calc
      a ^ p * |∑ k, g k| ^ p ≤ a ^ p * (∑ k, |g k|) ^ p :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) h1 _) (by positivity)
      _ ≤ a ^ p * ((m : ℝ) ^ (p - 1) * ∑ k, |g k| ^ p) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = _ := by dsimp [C]; ring
  have hB := (block_sum_summable m f hf hx).mul_left C
  have hS : Summable (fun i => |blockAverage m a x i| ^ p) :=
    Summable.of_nonneg_of_le (fun _ => by positivity) h hB
  refine ⟨hS, ?_⟩
  calc
    _ ≤ ∑' i, C * ∑ k : Fin m, f ((Nat.divModEquiv m).symm (i,k)) :=
      hS.tsum_le_tsum h hB
    _ = _ := by rw [tsum_mul_left, block_sum_eq m f hx]

end

end OMASequenceBlocks

namespace OMASequenceBlocks

open OMA.S_mo_18264

private lemma square_sum (x : ℕ → ℝ) (hx : x ∈ K) :
    Summable (fun i => |x i| ^ (2 : ℕ)) := by
  simpa only [sq_abs] using hx.1

private lemma point_le_one (x : ℕ → ℝ) (hx : x ∈ K) (i : ℕ) : |x i| ≤ 1 := by
  have h := (hx.1.sum_le_tsum {i} (fun i _ => sq_nonneg (x i))).trans hx.2
  simp only [Finset.sum_singleton, ← sq_abs (x i)] at h
  nlinarith [abs_nonneg (x i)]

private lemma sum_sq_sub (x y : ℕ → ℝ) (hx : x ∈ K) (hy : y ∈ K) :
    Summable (fun i => |(x-y) i| ^ (2 : ℕ)) := by
  apply Summable.of_nonneg_of_le (fun _ => by positivity) _
    (((hx.1).add (hy.1)).mul_left (2 : ℝ))
  intro i
  simp only [Pi.sub_apply, sq_abs]
  nlinarith [sq_nonneg (x i + y i)]

private lemma sum_pow_sub {p : ℕ} (hp : 2 ≤ p) {x y : ℕ → ℝ} (hx : x ∈ K) (hy : y ∈ K) :
    Summable (fun i => |(x-y) i| ^ p) := by
  have h := sum_sq_sub x y hx hy
  apply Summable.of_nonneg_of_le (fun _ => by positivity) _ (h.mul_left (2 ^ (p - 2) : ℝ))
  intro i
  have hh : |(x-y) i| ≤ 2 := by
    simp only [Pi.sub_apply]
    exact (abs_sub _ _).trans (by linarith [point_le_one x hx i, point_le_one y hy i])
  conv_lhs => rw [← Nat.sub_add_cancel hp, pow_add]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) hh _) (by positivity)

private lemma integer_norm (x : ℕ → ℝ) (p : ℕ) :
    lpNorm (p : ℝ) x = (∑' i, |x i| ^ p) ^ ((1 : ℝ) / p) := by
  simp only [lpNorm, Real.rpow_natCast]

private lemma root_power (z : ℝ) (hz : 0 ≤ z) (p : ℕ) (hp : p ≠ 0) :
    (z ^ p) ^ ((1 : ℝ) / p) = z := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hz, mul_one_div_cancel (by exact_mod_cast hp),
    Real.rpow_one]

private lemma scaled_average_three (k : ℕ) (hk : 0 < k) {x y : ℕ → ℝ}
    (hx : x ∈ K) (hy : y ∈ K) [NeZero (k ^ 12)] :
    lpNorm 3 (blockAverage (k ^ 12) ((k : ℝ) ^ 6)⁻¹ (x-y))
      ≤ (k : ℝ) ^ 2 * lpNorm 3 (x-y) := by
  have hk0 : (k : ℝ) ≠ 0 := by positivity
  have h := (average_moment (k ^ 12) (a := ((k : ℝ) ^ 6)⁻¹) (by positivity)
    (p := 3) (by decide) (x-y) (sum_pow_sub (p := 3) (by decide) hx hy)).2
  have hcoef : ((k ^ 12 : ℕ) : ℝ) ^ (3 - 1 : ℕ) * ((k : ℝ) ^ 6)⁻¹ ^ (3 : ℕ) =
      ((k : ℝ) ^ (2 : ℕ)) ^ (3 : ℕ) := by
    push_cast
    field_simp
  rw [hcoef] at h
  rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, integer_norm, integer_norm]
  refine (Real.rpow_le_rpow (tsum_nonneg fun _ => by positivity) h (by positivity)).trans_eq ?_
  rw [Real.mul_rpow (by positivity) (tsum_nonneg fun _ => by positivity),
    root_power _ (by positivity) 3 (by decide)]

private lemma scaled_repeat_four (k : ℕ) (hk : 0 < k) {x y : ℕ → ℝ}
    (hx : x ∈ K) (hy : y ∈ K) [NeZero (k ^ 12)] :
    lpNorm 4 (blockRepeat (k ^ 12) ((k : ℝ) ^ 6)⁻¹ (x-y)) =
      (((k : ℝ) ^ 3)⁻¹) * lpNorm 4 (x-y) := by
  have hk0 : (k : ℝ) ≠ 0 := by positivity
  have h := (repeat_moment (k ^ 12) (a := ((k : ℝ) ^ 6)⁻¹) (by positivity)
    4 (x-y) (sum_pow_sub (p := 4) (by decide) hx hy)).2
  have hcoef : ((k ^ 12 : ℕ) : ℝ) * ((k : ℝ) ^ 6)⁻¹ ^ (4 : ℕ) =
      (((k : ℝ) ^ (3 : ℕ))⁻¹) ^ (4 : ℕ) := by
    push_cast
    field_simp
  rw [hcoef] at h
  rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, integer_norm, integer_norm, h,
    Real.mul_rpow (by positivity) (tsum_nonneg fun _ => by positivity),
    root_power _ (by positivity) 4 (by decide)]

/-- Repetition and averaging preserve the squared-norm bound. Their combined
effect on the mixed-norm estimate divides its coefficient by the block parameter. -/
theorem mixed_norm_counterexample_of_bounded_ratio (F : (ℕ → ℝ) → (ℕ → ℝ))
    (hF : ∀ x ∈ K, F x ∈ K) (hn : ∀ x ∈ K, F x ≠ x)
    (L : ℝ) (hL : 0 ≤ L)
    (hLip : ∀ x ∈ K, ∀ y ∈ K, lpNorm 4 (F x - F y) ≤ L * lpNorm 3 (x-y)) :
    ¬ (type_of% @OMA.S_mo_18264.main) := by
  intro main
  obtain ⟨k, hk⟩ := exists_nat_gt L
  have hk0 : 0 < k := by exact_mod_cast (hL.trans_lt hk)
  have hkR : (k : ℝ) ≠ 0 := by positivity
  let _ : NeZero (k ^ 12) := ⟨pow_ne_zero _ (Nat.ne_of_gt hk0)⟩
  let a : ℝ := ((k : ℝ) ^ 6)⁻¹
  have ha : 0 ≤ a := by positivity
  have hscale : ((k ^ 12 : ℕ) : ℝ) * a ^ 2 = 1 := by
    dsimp [a]
    push_cast
    field_simp
  let R := blockRepeat (k ^ 12) a
  let A := blockAverage (k ^ 12) a
  have hR (x : ℕ → ℝ) (hx : x ∈ K) : R x ∈ K := by
    have hr := repeat_moment (k ^ 12) ha 2 x (square_sum x hx)
    rw [hscale, one_mul] at hr
    simp only [sq_abs] at hr
    exact ⟨hr.1, hr.2.le.trans hx.2⟩
  have hA (x : ℕ → ℝ) (hx : x ∈ K) : A x ∈ K := by
    have hr := average_moment (k ^ 12) ha (p := 2) (by decide) x (square_sum x hx)
    simp only [sq_abs, show (2 - 1 : ℕ) = 1 by decide, pow_one, hscale, one_mul] at hr
    exact ⟨hr.1, hr.2.trans hx.2⟩
  let T := fun x => R (F (A x))
  have hT (x : ℕ → ℝ) (hx : x ∈ K) : T x ∈ K := hR _ (hF _ (hA _ hx))
  have hTLip (x : ℕ → ℝ) (hx : x ∈ K) (y : ℕ → ℝ) (hy : y ∈ K) :
      lpNorm 4 (T x - T y) ≤ lpNorm 3 (x-y) := by
    change lpNorm 4 (R (F (A x)) - R (F (A y))) ≤ _
    rw [show ∀ u v, R u - R v = R (u-v) from fun u v => (blockRepeat_sub _ _ u v).symm,
      scaled_repeat_four k hk0 (hF _ (hA _ hx)) (hF _ (hA _ hy))]
    have h1 := hLip (A x) (hA _ hx) (A y) (hA _ hy)
    rw [show A x - A y = A (x-y) from (blockAverage_sub _ _ _ _).symm] at h1
    have h2 := scaled_average_three k hk0 hx hy
    have h3 : 0 ≤ lpNorm 3 (x-y) := by
      rw [lpNorm]
      exact Real.rpow_nonneg (tsum_nonneg fun _ => by positivity) _
    have h4 : ((k : ℝ) ^ 3)⁻¹ * (L * ((k : ℝ) ^ 2)) ≤ 1 := by
      calc
        _ ≤ ((k : ℝ) ^ 3)⁻¹ * ((k : ℝ) * ((k : ℝ) ^ 2)) := by gcongr
        _ = 1 := by field_simp
    calc
      _ ≤ ((k : ℝ) ^ 3)⁻¹ * (L * lpNorm 3 (A (x-y))) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
      _ ≤ ((k : ℝ) ^ 3)⁻¹ * (L * ((k : ℝ) ^ 2 * lpNorm 3 (x-y))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 hL) (by positivity)
      _ = (((k : ℝ) ^ 3)⁻¹ * (L * ((k : ℝ) ^ 2))) * lpNorm 3 (x-y) := by ring
      _ ≤ _ := by simpa only [one_mul] using mul_le_mul_of_nonneg_right h4 h3
  obtain ⟨x, hx, he⟩ := main T hT hTLip
  have ee : ∀ z, A (R z) = z := blockAverage_repeat _ hscale
  exact hn (A x) (hA x hx) (by simpa only [T, ee] using congrArg A he)

end OMASequenceBlocks

namespace OMASequenceBlocks

open OMA.S_mo_18264 Filter

noncomputable section

def level (n : ℕ) : ℝ := (1/8) * (1/2) ^ n

lemma level_zero : level 0 = 1/8 := by norm_num [level]

lemma level_pos (n : ℕ) : 0 < level n := by unfold level; positivity

lemma level_succ (n : ℕ) : level (n+1) = level n / 2 := by
  simp [level, pow_succ]
  ring

lemma level_antitone : Antitone level := by
  apply antitone_nat_of_succ_le
  intro n
  rw [level_succ]
  linarith [level_pos n]

lemma level_le (n : ℕ) : level n ≤ 1/8 := by
  rw [← level_zero]
  exact level_antitone (Nat.zero_le _)

lemma exists_level_interval {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1/8) :
    ∃ n : ℕ, level (n+1) ≤ t ∧ t ≤ level n := by
  have hlim : Tendsto level atTop (nhds 0) := by
    unfold level
    simpa using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (show (0:ℝ) ≤ 1/2 by norm_num)
        (show (1/2:ℝ) < 1 by norm_num)).const_mul (1/8 : ℝ)
  obtain ⟨m, hm⟩ := (hlim.eventually (eventually_lt_nhds ht)).exists
  let h : ∃ n : ℕ, level (n+1) ≤ t := ⟨m, (level_antitone (Nat.le_succ m)).trans hm.le⟩
  refine ⟨Nat.find h, Nat.find_spec h, ?_⟩
  cases hfind : Nat.find h with
  | zero => simpa only [level_zero] using ht'
  | succ n =>
    exact (lt_of_not_ge (Nat.find_min h (hfind ▸ Nat.lt_succ_self n))).le

/-- Interpolation between consecutive dyadic levels has at most two nonzero coordinates. -/
def bump (t : ℝ) (n : ℕ) : ℝ :=
  max 0 (min (2 * (t - level (n+1))) (2 * level n - t))

lemma bump_nonneg (t : ℝ) (n : ℕ) : 0 ≤ bump t n := le_max_left _ _

lemma bump_zero_zero (n : ℕ) : bump 0 n = 0 := by
  unfold bump
  apply max_eq_left
  have hp := level_pos (n+1)
  exact (min_le_left _ _).trans (by linarith)

lemma bump_lipschitz (s t : ℝ) (n : ℕ) : |bump s n - bump t n| ≤ 2 * |s-t| := by
  unfold bump
  let v (r : ℝ) := min (2*(r-level (n+1))) (2*level n-r)
  have h : |max 0 (v s) - max 0 (v t)| ≤ |v s - v t| := by
    have h' := abs_max_sub_max_le_max (0:ℝ) (v s) 0 (v t)
    rw [sub_self, abs_zero, max_eq_right (abs_nonneg (v s - v t))] at h'
    exact h'
  refine h.trans ?_
  dsimp [v]
  apply (abs_min_sub_min_le_max _ _ _ _).trans
  apply max_le
  · rw [show 2*(s-level (n+1)) - 2*(t-level (n+1)) = 2*(s-t) by ring,
      abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
  · rw [show 2*level n-s-(2*level n-t) = -(s-t) by ring, abs_neg]
    linarith [abs_nonneg (s-t)]

lemma bump_pair {t : ℝ} {n : ℕ} (hl : level (n+1) ≤ t) (hu : t ≤ level n) :
    bump t n = 2*t-level n ∧ bump t (n+1) = level n-t ∧
    ∀ i : ℕ, i ∉ ({n,n+1} : Finset ℕ) → bump t i = 0 := by
  have h := level_succ n
  have hh := level_succ (n+1)
  refine ⟨?_, ?_, ?_⟩
  · unfold bump
    rw [min_eq_left (by linarith), max_eq_right (by linarith)]
    linarith
  · unfold bump
    rw [min_eq_right (by linarith), max_eq_right (by linarith)]
    linarith
  · intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi
    unfold bump
    apply max_eq_left
    by_cases hii : i < n
    · have hli := level_antitone (show i+1 ≤ n by omega)
      exact (min_le_left _ _).trans (by linarith)
    · have hli := level_antitone (show n+1 ≤ i-1 by omega)
      have hle := level_succ (i-1)
      rw [show i-1+1=i by omega] at hle
      exact (min_le_right _ _).trans (by linarith)

lemma bump_support {t : ℝ} (ht : 0 ≤ t) (ht' : t ≤ 1/8) :
    ∃ s : Finset ℕ, s.card ≤ 2 ∧ (∀ i ∉ s, bump t i = 0) ∧
      Summable (bump t) ∧ ∑' i, bump t i = t := by
  rcases ht.eq_or_lt with h | h
  · subst t
    have hz (i : ℕ) (_ : i ∉ (∅ : Finset ℕ)) := bump_zero_zero i
    exact ⟨∅, by simp, hz, summable_of_ne_finset_zero hz, by rw [tsum_eq_sum hz]; simp⟩
  obtain ⟨n, hl, hu⟩ := exists_level_interval h ht'
  obtain ⟨hn, hn', hsup⟩ := bump_pair hl hu
  refine ⟨{n,n+1}, by simp, hsup, summable_of_ne_finset_zero hsup, ?_⟩
  rw [tsum_eq_sum hsup, Finset.sum_insert (by simp),
    Finset.sum_singleton, hn, hn']
  ring

lemma bump_large {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1/8) :
    ∃ i, t/2 ≤ bump t i ∧ level (i+1) ≤ t := by
  obtain ⟨n, hl, hu⟩ := exists_level_interval ht ht'
  obtain ⟨ha,hb,-⟩ := bump_pair hl hu
  by_cases h : t/2 ≤ bump t n
  · exact ⟨n,h,hl⟩
  · exact ⟨n+1, by linarith, (level_antitone (Nat.le_succ (n+1))).trans hl⟩

def supAbs (x : ℕ → ℝ) : ℝ := ⨆ i, |x i|

lemma abs_le_supAbs {x : ℕ → ℝ} (hx : x ∈ K) (i : ℕ) : |x i| ≤ supAbs x :=
  le_ciSup (f := fun j => |x j|) ⟨1, by rintro _ ⟨j,rfl⟩; exact point_le_one x hx j⟩ i

def cutoff (x : ℕ → ℝ) : ℝ := max 0 (1/8 - supAbs x)

lemma cutoff_nonneg (x : ℕ → ℝ) : 0 ≤ cutoff x := le_max_left _ _

lemma cutoff_le {x : ℕ → ℝ} (hx : x ∈ K) : cutoff x ≤ 1/8 := by
  unfold cutoff
  apply max_le (by norm_num)
  linarith [abs_le_supAbs hx 0, abs_nonneg (x 0)]

def diagonal (i : ℕ) : ℝ := 1 - level (i+1)

lemma diagonal_nonneg (i : ℕ) : 0 ≤ diagonal i := by
  unfold diagonal
  linarith [level_le (i+1)]

lemma diagonal_le_one (i : ℕ) : diagonal i ≤ 1 := by
  unfold diagonal
  linarith [level_pos (i+1)]

/-- The positive term moves to higher coordinates as the cutoff tends to zero. -/
def auxiliaryMap (x : ℕ → ℝ) (i : ℕ) : ℝ :=
  (1 - cutoff x) * (diagonal i * x i) + bump (cutoff x) i

lemma auxiliaryMap_mem {x : ℕ → ℝ} (hx : x ∈ K) : auxiliaryMap x ∈ K := by
  let t := cutoff x
  have ht : 0 ≤ t := cutoff_nonneg x
  have ht' : t ≤ 1/8 := cutoff_le hx
  have h1 : 0 ≤ 1-t := by dsimp [t]; linarith
  obtain ⟨s, hs, hz, hb, hb'⟩ := bump_support ht ht'
  have hB (i : ℕ) : bump t i ≤ t := by
    have h := hb.sum_le_tsum {i} (fun j _ => bump_nonneg t j)
    rw [Finset.sum_singleton, hb'] at h
    exact h
  have hsq (i : ℕ) : auxiliaryMap x i ^ 2 ≤ (1-t) * x i ^ 2 + bump t i := by
    change ((1-t) * (diagonal i*x i) + bump t i)^2 ≤ _
    have hd : diagonal i ^ 2 ≤ 1 := by
      have := mul_nonneg (diagonal_nonneg i) (sub_nonneg.mpr (diagonal_le_one i))
      nlinarith [diagonal_le_one i]
    by_cases hh : t = 0
    · simp [hh, bump_zero_zero, mul_pow]
      exact mul_le_of_le_one_left (sq_nonneg _) hd
    have htp : 0 < t := lt_of_le_of_ne ht (Ne.symm hh)
    let v := bump t i / t
    have hv : 0 ≤ v := div_nonneg (bump_nonneg t i) ht
    have hv1 : v ≤ 1 := (div_le_one htp).mpr (hB i)
    have he : t*v = bump t i := by dsimp [v]; field_simp
    have hcv : ((1-t)*(diagonal i*x i)+t*v)^2 ≤
        (1-t)*(diagonal i*x i)^2 + t*v^2 := by
      nlinarith [mul_nonneg (mul_nonneg h1 ht) (sq_nonneg (diagonal i*x i-v))]
    rw [he] at hcv
    apply hcv.trans
    have hdx : (diagonal i*x i)^2 ≤ x i ^ 2 := by
      rw [mul_pow]
      exact mul_le_of_le_one_left (sq_nonneg _) hd
    have hvv : v^2 ≤ v := by nlinarith [mul_nonneg hv (sub_nonneg.mpr hv1)]
    rw [← he]
    exact add_le_add (mul_le_mul_of_nonneg_left hdx h1) (mul_le_mul_of_nonneg_left hvv ht)
  have hS := (hx.1.mul_left (1-t)).add hb
  have hM : Summable (fun i => auxiliaryMap x i ^ 2) :=
    Summable.of_nonneg_of_le (fun _ => sq_nonneg _) hsq hS
  refine ⟨hM, (hM.tsum_le_tsum hsq hS).trans ?_⟩
  rw [Summable.tsum_add (hx.1.mul_left (1-t)) hb, tsum_mul_left, hb']
  nlinarith [mul_le_mul_of_nonneg_left hx.2 h1]

lemma auxiliaryMap_no_fixed {x : ℕ → ℝ} (hx : x ∈ K) : auxiliaryMap x ≠ x := by
  intro he
  let t := cutoff x
  have ht : 0 ≤ t := cutoff_nonneg x
  have hte (i : ℕ) : (t + (1-t)*level (i+1)) * x i = bump t i := by
    have h := congrFun he i
    change (1-t)*(diagonal i*x i)+bump t i = x i at h
    unfold diagonal at h
    linear_combination -h
  by_cases hz : t = 0
  · have hzero (i : ℕ) : x i = 0 := by
      have h := hte i
      simp only [hz, sub_zero, one_mul, zero_add, bump_zero_zero] at h
      exact (mul_eq_zero.mp h).resolve_left (level_pos (i+1)).ne'
    have hsup : supAbs x = 0 := by simp [supAbs, hzero]
    dsimp [t, cutoff] at hz
    rw [hsup] at hz
    norm_num at hz
  have htp : 0 < t := lt_of_le_of_ne ht (Ne.symm hz)
  obtain ⟨i, hi, hlev⟩ := bump_large htp (cutoff_le hx)
  have hsmall : supAbs x < 1/8 := by
    change 0 < max 0 (1/8-supAbs x) at htp
    exact sub_pos.mp ((lt_max_iff.mp htp).resolve_left (lt_irrefl _))
  have hc : 0 ≤ t+(1-t)*level (i+1) := by
    apply add_nonneg ht
    exact mul_nonneg (by dsimp [t]; linarith [cutoff_le hx]) (level_pos _).le
  have hc' : t+(1-t)*level (i+1) ≤ 2*t := by
    nlinarith [mul_nonneg ht (level_pos (i+1)).le]
  have hxi : x i ≤ 1/8 := (le_abs_self _).trans ((abs_le_supAbs hx i).trans hsmall.le)
  have hbound := mul_le_mul_of_nonneg_right hc' (by norm_num : (0:ℝ) ≤ 1/8)
  have hbound' := mul_le_mul_of_nonneg_left hxi hc
  linarith only [hte i, hi, hbound, hbound', htp]

end

end OMASequenceBlocks

namespace OMASequenceBlocks

open OMA.S_mo_18264

noncomputable section

private lemma pow_four_add_three {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    (a + b + c)^4 ≤ 81*(a^4 + b^4 + c^4) := by
  let m := max a (max b c)
  have hma : a ≤ m := le_max_left _ _
  have hmb : b ≤ m := (le_max_left _ _).trans (le_max_right _ _)
  have hmc : c ≤ m := (le_max_right _ _).trans (le_max_right _ _)
  have hm : m^4 ≤ a^4+b^4+c^4 := by
    dsimp [m]
    rcases le_total a (max b c) with h | h
    · rw [max_eq_right h]
      rcases le_total b c with hbc | hcb
      · rw [max_eq_right hbc]
        nlinarith [show 0 ≤ a^4 by positivity, show 0 ≤ b^4 by positivity]
      · rw [max_eq_left hcb]
        nlinarith [show 0 ≤ a^4 by positivity, show 0 ≤ c^4 by positivity]
    · rw [max_eq_left h]
      nlinarith [show 0 ≤ b^4 by positivity, show 0 ≤ c^4 by positivity]
  calc
    _ ≤ (3*m)^4 := pow_le_pow_left₀ (by positivity) (by linarith) _
    _ = 81*m^4 := by ring
    _ ≤ _ := by linarith

private lemma cutoff_difference {x y : ℕ → ℝ} (hx : x ∈ K) (hy : y ∈ K) {d : ℝ}
    (hf : ∀ i, |(x-y) i| ≤ d) : |cutoff x - cutoff y| ≤ d := by
  have hxle : supAbs x ≤ supAbs y + d := by
    apply ciSup_le
    intro i
    have h := abs_sub_abs_le_abs_sub (x i) (y i)
    have hfi := hf i
    simp only [Pi.sub_apply] at hfi
    linarith [hfi, abs_le_supAbs hy i]
  have hyle : supAbs y ≤ supAbs x + d := by
    apply ciSup_le
    intro i
    have h := abs_sub_abs_le_abs_sub (y i) (x i)
    rw [abs_sub_comm] at h
    have hfi := hf i
    simp only [Pi.sub_apply] at hfi
    linarith [hfi, abs_le_supAbs hx i]
  unfold cutoff
  refine (abs_max_sub_max_le_max 0 _ 0 _).trans (max_le ?_ ?_)
  · simp
    exact (abs_nonneg _).trans (hf 0)
  · rw [abs_le]
    constructor <;> linarith

private lemma bump_difference {t u d : ℝ}
    (ht : 0 ≤ t) (ht' : t ≤ 1/8) (hu : 0 ≤ u) (hu' : u ≤ 1/8)
    (he : |t-u| ≤ d) :
    Summable (fun i => |bump t i - bump u i| ^ (4 : ℕ)) ∧
      (∑' i, |bump t i - bump u i| ^ (4 : ℕ)) ≤ 64*d^4 := by
  obtain ⟨s, hs, hzs, _, _⟩ := bump_support ht ht'
  obtain ⟨v, hv, hzv, _, _⟩ := bump_support hu hu'
  let w := s ∪ v
  have hw : w.card ≤ 4 := (Finset.card_union_le _ _).trans (by omega)
  have hz (i : ℕ) (hi : i ∉ w) : |bump t i - bump u i| ^ (4 : ℕ) = 0 := by
    simp only [w, Finset.mem_union, not_or] at hi
    simp [hzs i hi.1, hzv i hi.2]
  have h : Summable (fun i => |bump t i - bump u i| ^ (4 : ℕ)) :=
    summable_of_ne_finset_zero hz
  refine ⟨h, ?_⟩
  rw [tsum_eq_sum hz]
  calc
    _ ≤ ∑ i ∈ w, (2*d) ^ (4 : ℕ) := by
      apply Finset.sum_le_sum
      intro i hi
      exact pow_le_pow_left₀ (abs_nonneg _) ((bump_lipschitz t u i).trans (by gcongr)) _
    _ = (w.card : ℝ) * (2*d) ^ (4 : ℕ) := by simp
    _ ≤ 4 * (2*d) ^ (4 : ℕ) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hw) (by positivity)
    _ = 64*d^4 := by ring


set_option maxHeartbeats 700000 in
private lemma auxiliaryMap_lipschitz {x y : ℕ → ℝ} (hx : x ∈ K) (hy : y ∈ K) :
    lpNorm 4 (auxiliaryMap x - auxiliaryMap y) ≤ 10 * lpNorm 3 (x-y) := by
  let t := cutoff x
  let u := cutoff y
  have ht : 0 ≤ t := cutoff_nonneg x
  have hu : 0 ≤ u := cutoff_nonneg y
  have ht' : t ≤ 1/8 := cutoff_le hx
  have hu' : u ≤ 1/8 := cutoff_le hy
  have ht1 : 0 ≤ 1-t := by linarith
  let z := x-y
  have h3 := sum_pow_sub (p := 3) (by decide) hx hy
  have h4 := sum_pow_sub (p := 4) (by decide) hx hy
  let d := (∑' i, |z i| ^ (3 : ℕ)) ^ ((1:ℝ)/3)
  have hd : 0 ≤ d := Real.rpow_nonneg (tsum_nonneg fun _ => by positivity) _
  have he : d^3 = ∑' i, |z i| ^ (3 : ℕ) := by
    dsimp [d]
    rw [← Real.rpow_natCast _ 3, ← Real.rpow_mul (tsum_nonneg fun _ => by positivity)]
    norm_num
  have hpoint (i : ℕ) : |z i| ≤ d := by
    have hh := h3.sum_le_tsum {i} (fun j _ => show 0 ≤ |z j|^3 by positivity)
    simp only [Finset.sum_singleton] at hh
    have hh' := Real.rpow_le_rpow (by positivity) hh (by norm_num : (0:ℝ) ≤ 1/3)
    exact (root_power (|z i|) (abs_nonneg _) 3 (by decide)).symm.le.trans hh'
  have hzu : (∑' i, |z i| ^ (4 : ℕ)) ≤ d ^ 4 := by
    calc
      _ ≤ ∑' i, d * |z i| ^ (3 : ℕ) :=
        h4.tsum_le_tsum (fun i => by
          change |z i|^4 ≤ d*|z i|^3
          rw [show (4:ℕ) = 3+1 by decide, pow_add, pow_one, mul_comm (|z i|^3)]
          exact mul_le_mul_of_nonneg_right (hpoint i) (by positivity)) (h3.mul_left _)
      _ = _ := by rw [tsum_mul_left, ← he]; ring
  have htu : |t-u| ≤ d := cutoff_difference hx hy hpoint
  obtain ⟨hB, hBn⟩ := bump_difference ht ht' hu hu' htu
  let w := auxiliaryMap x-auxiliaryMap y
  have hW := sum_pow_sub (p := 4) (by decide) (auxiliaryMap_mem hx) (auxiliaryMap_mem hy)
  have hy4 (i : ℕ) : |y i| ^ (4 : ℕ) ≤ y i ^ 2 := by
    have hh := point_le_one y hy i
    calc
      _ = |y i| ^ 2 * |y i| ^ 2 := by ring
      _ ≤ 1 * |y i| ^ 2 := mul_le_mul_of_nonneg_right
        (by simpa using pow_le_pow_left₀ (abs_nonneg (y i)) hh 2) (by positivity)
      _ = _ := by rw [one_mul, sq_abs]
  have hs (i : ℕ) : |w i| ≤ |z i| + d*|y i| + |bump t i-bump u i| := by
    have hd0 := diagonal_nonneg i
    have hd1 := diagonal_le_one i
    have hprod : (1-t)*diagonal i ≤ 1 :=
      (mul_le_mul_of_nonneg_left hd1 ht1).trans (by linarith)
    have hh : w i = (1-t)*diagonal i*z i+(u-t)*diagonal i*y i+(bump t i-bump u i) := by
      change (1-t)*(diagonal i*x i)+bump t i - ((1-u)*(diagonal i*y i)+bump u i) = _
      dsimp [z]
      ring
    rw [hh]
    apply (abs_add_le ..).trans
    refine add_le_add ?_ le_rfl
    apply (abs_add_le ..).trans
    simp only [abs_mul, abs_of_nonneg ht1, abs_of_nonneg hd0]
    apply add_le_add
    · exact mul_le_of_le_one_left (abs_nonneg _) hprod
    · apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
      exact (mul_le_of_le_one_right (abs_nonneg _) hd1).trans (by rwa [abs_sub_comm])
  have hp (i : ℕ) : |w i| ^ (4 : ℕ) ≤
      81*(|z i|^4 + d^4*y i^2 + |bump t i-bump u i|^4) := by
    refine (pow_le_pow_left₀ (abs_nonneg _) (hs i) _).trans ?_
    refine (pow_four_add_three (abs_nonneg _) (mul_nonneg hd (abs_nonneg _))
      (abs_nonneg _)).trans ?_
    rw [mul_pow]
    gcongr
    exact hy4 i
  have hdy := hy.1.mul_left (d^4)
  have hsum := ((h4.add hdy).add hB).mul_left (81:ℝ)
  have hmerge : (∑' i, |w i| ^ (4 : ℕ)) ≤ (10*d)^4 := by
    calc
      _ ≤ ∑' i, 81*(|z i|^4 + d^4*y i^2 + |bump t i-bump u i|^4) :=
        hW.tsum_le_tsum hp hsum
      _ = 81*((∑' i, |z i|^4) + d^4*(∑' i, y i^2) + ∑' i, |bump t i-bump u i|^4) := by
        rw [tsum_mul_left, Summable.tsum_add (h4.add hdy) hB, Summable.tsum_add h4 hdy, tsum_mul_left]
      _ ≤ 81*(d^4 + d^4 + 64*d^4) := by
        exact mul_le_mul_of_nonneg_left
          (add_le_add (add_le_add hzu (mul_le_of_le_one_right (by positivity) hy.2)) hBn)
          (by norm_num)
      _ ≤ (10*d)^4 := by nlinarith [sq_nonneg (d^2)]
  have hResult := Real.rpow_le_rpow (tsum_nonneg fun _ => by positivity) hmerge
    (by norm_num : (0:ℝ) ≤ 1/4)
  change lpNorm 4 w ≤ 10 * lpNorm 3 z
  rw [show (4:ℝ) = ((4:ℕ):ℝ) by norm_num, integer_norm,
    show (3:ℝ) = ((3:ℕ):ℝ) by norm_num, integer_norm]
  change (∑' i, |w i| ^ (4 : ℕ)) ^ ((1:ℝ)/(↑(4:ℕ):ℝ)) ≤
    ((10*d)^4) ^ ((1:ℝ)/(↑(4:ℕ):ℝ)) at hResult
  rw [root_power (10*d) (by positivity) 4 (by decide)] at hResult
  exact hResult

end

end OMASequenceBlocks

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_18264.main) :=
  OMASequenceBlocks.mixed_norm_counterexample_of_bounded_ratio OMASequenceBlocks.auxiliaryMap
    (fun _ hx => OMASequenceBlocks.auxiliaryMap_mem hx)
    (fun _ hx => OMASequenceBlocks.auxiliaryMap_no_fixed hx)
    10 (by norm_num) (fun _ hx _ hy => OMASequenceBlocks.auxiliaryMap_lipschitz hx hy)