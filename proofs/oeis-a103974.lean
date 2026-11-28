import OMAStatements.S_oeis_a103974

/-!
Credit: @grp06

The Pell parameterization follows Alec Mihailovs and David Terr's comments of
March 7, 2005 on OEIS A103974, https://oeis.org/A103974/internal.
OEIS source text: OEIS Foundation, CC BY-SA 4.0.
-/

open Filter Topology Real
open OMA.S_oeis_a103974

namespace A103974Proof

private def U : Pell.Solution₁ 3 := Pell.Solution₁.mk 2 1 (by norm_num)

private theorem fundamental : Pell.IsFundamental U := by
  refine ⟨by norm_num [U], by norm_num [U], ?_⟩
  intro b hb
  change 2 ≤ b.x
  omega

private theorem x_step (n : ℕ) :
    (U ^ (n + 1)).x = 2 * (U ^ n).x + 3 * (U ^ n).y := by
  simp only [pow_succ, Pell.Solution₁.x_mul]
  change (U ^ n).x * 2 + 3 * ((U ^ n).y * 1) = _
  ring

private theorem x_residue (n : ℕ) :
    (U ^ n).x % 3 = if n % 2 = 0 then 1 else 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [x_step]
    split at ih <;> split <;> omega

private def W (n : ℕ) : Pell.Solution₁ 3 := U ^ (2 * n)

private theorem x_pos (n : ℕ) : 0 < (W n).x :=
  Pell.Solution₁.x_pow_pos fundamental.x_pos _

private theorem y_nonneg (n : ℕ) : 0 ≤ (W n).y := by
  unfold W
  generalize 2 * n = j
  cases j with
  | zero => simp
  | succ j =>
    exact (Pell.Solution₁.y_pow_succ_pos fundamental.x_pos fundamental.2.1 j).le

private theorem w_residue (n : ℕ) : (W n).x % 3 = 1 := by
  have h : (2 * n) % 2 = 0 := by omega
  simpa only [W, h, if_true] using x_residue (2 * n)

private theorem w_step (n : ℕ) :
    (W (n + 1)).x = (W n).x * 7 + 3 * ((W n).y * 4) ∧
    (W (n + 1)).y = (W n).x * 4 + (W n).y * 7 := by
  have hw : W (n + 1) = W n * U ^ 2 := by
    unfold W
    rw [Nat.mul_add, Nat.mul_one, pow_add]
  have hx : (U ^ 2).x = 7 := by norm_num [pow_two, U]
  have hy : (U ^ 2).y = 4 := by norm_num [pow_two, U]
  rw [hw, Pell.Solution₁.x_mul, Pell.Solution₁.y_mul, hx, hy]
  exact ⟨rfl, rfl⟩

private def A (n : ℕ) : ℕ := ((2 * (W n).x + 1) / 3).toNat

private theorem a_relation (n : ℕ) : 3 * (A n : ℤ) = 2 * (W n).x + 1 := by
  have h := w_residue n
  have hx := x_pos n
  have hp : 0 ≤ (2 * (W n).x + 1) / 3 := by omega
  unfold A
  rw [Int.toNat_of_nonneg hp]
  omega

private theorem odd_of_area (a m : ℕ)
    (h : 16 * (m : ℤ)^2 = ((a : ℤ) + 1)^2 * ((3 * (a : ℤ) + 1) * ((a : ℤ) - 1))) :
    (a : ℤ) % 2 = 1 := by
  by_contra hn
  generalize hbdef : (a : ℤ) % 16 = b
  have hb : 0 ≤ b ∧ b < 16 ∧ b % 2 = 0 := by
    rw [← hbdef]
    omega
  have he : b ≡ (a : ℤ) [ZMOD 16] := by
    rw [← hbdef]
    exact Int.mod_modEq _ _
  have hm : (16 * (m : ℤ)^2 : ℤ) ≡ 0 [ZMOD 16] :=
    Int.modEq_zero_iff_dvd.mpr ⟨(m : ℤ)^2, rfl⟩
  rw [h] at hm
  have hz : (b + 1)^2 * ((3 * b + 1) * (b - 1)) ≡ 0 [ZMOD 16] :=
    (((he.add_right 1).pow 2).mul (((he.mul_left 3).add_right 1).mul
      (he.sub_right 1))).trans hm
  have hb0 := hb.1
  have hb1 := hb.2.1
  have hb2 := hb.2.2
  clear hb
  interval_cases b <;> norm_num at hb2 <;> norm_num [Int.ModEq] at hz

private theorem heron (a : ℚ) :
    3 / 16 * a^4 + 1 / 4 * a^3 - 1 / 8 * a^2 - 1 / 4 * a - 1 / 16 =
      (a + 1)^2 * ((3*a + 1) * (a - 1)) / 16 := by ring

private theorem heron_odd (k : ℚ) :
    (2*k - 1 + 1)^2 * ((3*(2*k - 1) + 1) * (2*k - 1 - 1)) / 16 =
      k^2 * ((3*k - 1) * (k - 1)) := by ring

private theorem p_iff (a : ℕ) : P a ↔ ∃ n, A n = a := by
  unfold P
  constructor
  · rintro ⟨ha, m, hm⟩
    rw [heron] at hm
    have h16 : 16 * (m : ℤ)^2 =
        ((a : ℤ) + 1)^2 * ((3 * (a : ℤ) + 1) * ((a : ℤ) - 1)) := by
      have hq : 16 * (m : ℚ)^2 =
          ((a : ℚ) + 1)^2 * ((3 * (a : ℚ) + 1) * ((a : ℚ) - 1)) := by
        linear_combination 16 * hm
      exact_mod_cast hq
    have hodd := odd_of_area a m h16
    let k : ℤ := ((a : ℤ) + 1) / 2
    have hk : 1 ≤ k := by dsimp [k]; omega
    have hak : (a : ℤ) = 2 * k - 1 := by dsimp [k]; omega
    have haq : (a : ℚ) = 2 * (k : ℚ) - 1 := by exact_mod_cast hak
    rw [haq, heron_odd] at hm
    have hkq : (k : ℚ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
    have hsq : IsSquare (↑((3*k - 1) * (k - 1)) : ℚ) := by
      refine ⟨(m : ℚ) / (k : ℚ), ?_⟩
      push_cast
      field_simp [hkq]
      nlinarith only [hm]
    obtain ⟨z, hz⟩ := Rat.isSquare_intCast_iff.mp hsq
    let y : ℤ := (z.natAbs : ℤ)
    have hy : 0 ≤ y := by positivity
    have hy2 : y^2 = (3*k - 1) * (k - 1) := by
      rcases le_total 0 z with hz0 | hz0
      · dsimp [y]
        rw [Int.natAbs_of_nonneg hz0]
        nlinarith only [hz]
      · have hneg : (z.natAbs : ℤ) = -z := by
          simpa only [Int.natAbs_neg] using Int.natAbs_of_nonneg (show 0 ≤ -z by omega)
        dsimp [y]
        rw [hneg]
        nlinarith only [hz]
    let B : Pell.Solution₁ 3 := Pell.Solution₁.mk (3*k - 2) y (by
      linear_combination -3 * hy2)
    have hx : 0 < B.x := by change 0 < 3*k - 2; omega
    obtain ⟨j, hj⟩ := fundamental.eq_pow_of_nonneg hx (show 0 ≤ B.y from hy)
    have hxj : (U ^ j).x = 3*k - 2 := by rw [← hj]; rfl
    have hr := x_residue j
    rw [hxj] at hr
    have hj2 : j % 2 = 0 := by split at hr <;> omega
    let n := j / 2
    have hn : j = 2 * n := by dsimp [n]; omega
    have hwn : (W n).x = 3*k - 2 := by simpa only [W, ← hn] using hxj
    refine ⟨n, ?_⟩
    have hh := a_relation n
    omega
  · rintro ⟨n, rfl⟩
    have hx := x_pos n
    have hr := w_residue n
    have hA := a_relation n
    let k : ℤ := ((W n).x + 2) / 3
    let y : ℤ := (W n).y
    have hk : 1 ≤ k := by dsimp [k]; omega
    have hxk : (W n).x = 3*k - 2 := by dsimp [k]; omega
    have hak : (A n : ℤ) = 2*k - 1 := by omega
    have haq : (A n : ℚ) = 2 * (k : ℚ) - 1 := by exact_mod_cast hak
    have hp := (W n).prop
    change (W n).x^2 - 3*y^2 = 1 at hp
    rw [hxk] at hp
    have hy2 : y^2 = (3*k - 1) * (k - 1) := by nlinarith only [hp]
    have hy := y_nonneg n
    change 0 ≤ y at hy
    let m := (k*y).toNat
    have hm : (m : ℤ) = k*y := Int.toNat_of_nonneg (mul_nonneg (by omega) hy)
    have hmq : (m : ℚ) = (k : ℚ) * (y : ℚ) := by exact_mod_cast hm
    have hyq : (y : ℚ)^2 = (3 * (k : ℚ) - 1) * ((k : ℚ) - 1) := by exact_mod_cast hy2
    refine ⟨by omega, m, ?_⟩
    rw [heron, haq, heron_odd, hmq, mul_pow, hyq]

private theorem a_mono : StrictMono A := by
  apply strictMono_nat_of_lt_succ
  intro n
  have hs := (w_step n).1
  have hx := x_pos n
  have hy := y_nonneg n
  have ha := a_relation n
  have hb := a_relation (n + 1)
  omega

private theorem nth_eq (n : ℕ) : Nat.nth P n = A n := by
  have he : Set.range A = Set.ofPred P := by
    ext a
    exact (p_iff a).symm
  have hi : (Set.ofPred P).Infinite := he ▸ Set.infinite_range_of_injective a_mono.injective
  have hindex (j : ℕ) : ∀ hf : Set.Finite (Set.ofPred P), j < hf.toFinset.card :=
    fun hf => (hi hf).elim
  have hs : Set.SurjOn A
      {j : ℕ | ∀ hf : Set.Finite (Set.ofPred P), j < hf.toFinset.card} (Set.ofPred P) := by
    intro a ha
    obtain ⟨j, hj⟩ := (p_iff a).mp ha
    exact ⟨j, hindex j, hj⟩
  have hm : Set.MapsTo A
      {j : ℕ | ∀ hf : Set.Finite (Set.ofPred P), j < hf.toFinset.card} (Set.ofPred P) :=
    fun _ _ => (p_iff _).mpr ⟨_, rfl⟩
  exact (Nat.eq_nth_of_strictMonoOn_of_mapsTo_of_surjOn A hs hm (a_mono.strictMonoOn _)
    (hindex n)).symm

private theorem power_formula (t : ℝ) (ht : t^2 = 3) (n : ℕ) :
    ((W n).x : ℝ) + ((W n).y : ℝ) * t = (7 + 4*t)^n := by
  induction n with
  | zero => simp [W]
  | succ n ih =>
    rw [pow_succ, ← ih, (w_step n).1, (w_step n).2]
    push_cast
    linear_combination -4 * ((W n).y : ℝ) * ht

private theorem ratio_limit :
    Tendsto (fun n : ℕ => (A (n + 1) : ℝ) / A n) atTop (𝓝 (7 + 4 * √3)) := by
  let t : ℝ := √3
  let r : ℝ := 7 + 4*t
  let s : ℝ := 7 - 4*t
  have ht : t^2 = 3 := Real.sq_sqrt (by norm_num)
  have ht0 : 0 ≤ t := Real.sqrt_nonneg _
  have htlo : (3 : ℝ)/2 < t := by
    by_contra! h
    nlinarith [mul_nonneg (sub_nonneg.mpr h) (show 0 ≤ 3/2 + t by linarith)]
  have hthi : t < (7 : ℝ)/4 := by
    by_contra! h
    nlinarith [mul_nonneg (sub_nonneg.mpr h) (show 0 ≤ t + 7/4 by linarith)]
  have hs0 : 0 < s := by dsimp [s]; linarith
  have hs1 : s < 1 := by dsimp [s]; linarith
  have hrs : r*s = 1 := by dsimp [r, s]; nlinarith only [ht]
  have htneg : (-t)^2 = 3 := by simpa only [neg_sq] using ht
  have hA (n : ℕ) : 3 * (A n : ℝ) = r^n + s^n + 1 := by
    have ha : 3 * (A n : ℝ) = 2 * ((W n).x : ℝ) + 1 := by exact_mod_cast a_relation n
    have hp : ((W n).x : ℝ) + ((W n).y : ℝ)*t = r^n := power_formula t ht n
    have hm : ((W n).x : ℝ) + ((W n).y : ℝ)*(-t) = s^n := by
      simpa only [mul_neg, ← sub_eq_add_neg, s] using power_formula (-t) htneg n
    linear_combination ha + hp + hm
  let B (n : ℕ) : ℝ := (A n : ℝ) * s^n
  have hB (n : ℕ) : B n = (1 + s^n * s^n + s^n)/3 := by
    have hn : r^n * s^n = 1 := by rw [← mul_pow, hrs, one_pow]
    dsimp [B]
    linear_combination (s^n * hA n + hn) / 3
  have hs_lim : Tendsto (fun n : ℕ => s^n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hs0.le hs1
  have hB_lim : Tendsto B atTop (𝓝 (1/3 : ℝ)) := by
    have he : B = (fun n : ℕ => (1 + s^n * s^n + s^n)/3) := funext hB
    rw [he]
    simpa using (((tendsto_const_nhds (x := (1 : ℝ))).add
      (hs_lim.mul hs_lim)).add hs_lim).div_const 3
  have hB_shift : Tendsto (fun n : ℕ => B (n + 1)) atTop (𝓝 (1/3 : ℝ)) :=
    hB_lim.comp (tendsto_add_atTop_nat 1)
  have hlim : Tendsto (fun n : ℕ => r * B (n + 1) / B n) atTop (𝓝 r) := by
    have hd := ((tendsto_const_nhds (x := r)).mul hB_shift).div hB_lim
      (by norm_num : (1/3 : ℝ) ≠ 0)
    have hr : r * (1/3 : ℝ) / (1/3 : ℝ) = r := by ring
    rwa [hr] at hd
  change Tendsto (fun n : ℕ => (A (n + 1) : ℝ) / A n) atTop (𝓝 r)
  apply hlim.congr
  intro n
  have he : r * B (n + 1) = (A (n + 1) : ℝ) * s^n := by
    dsimp [B]
    rw [pow_succ]
    calc
      r * ((A (n + 1) : ℝ) * (s^n * s)) = (A (n + 1) : ℝ) * s^n * (r*s) := by ring
      _ = _ := by rw [hrs, mul_one]
  rw [he]
  exact mul_div_mul_right _ _ (pow_ne_zero _ hs0.ne')

end A103974Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a103974.main := by
  simp_rw [A103974Proof.nth_eq]
  exact A103974Proof.ratio_limit
