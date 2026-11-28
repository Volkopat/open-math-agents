import OMAReductions.R_Erdos542_erdos_542_variants_only_two_R1_H3_R1

open OMA.R_Erdos542_erdos_542_variants_only_two_R1_H3_R1
open Finset

namespace OMA.Erdos542Middle

private theorem reciprocal_bound (n : ℕ) (A : Finset ℕ)
    (hA : Erdos542.IsLcmFree n A) (hsmall : ∀ a ∈ A, n < 4 * a) :
    ∑ a ∈ A, (1 : ℝ) / a ≤
      (∑ a ∈ Ioc (n / 2) n, (1 : ℝ) / a) +
      (1 / 2) * (∑ a ∈ Ioc (n / 3) (n / 2), (1 : ℝ) / a) +
      (1 / 6) * (∑ a ∈ Ioc (n / 4) (n / 3), (1 : ℝ) / a) := by
  classical
  let B := A.filter fun a => 2 * a ≤ n
  let C := A.filter fun a => ¬ 2 * a ≤ n
  let L := B.filter fun a => 3 * a ≤ n
  let M := B.filter fun a => ¬ 3 * a ≤ n
  let D := B.image (fun a => 2 * a)
  let E := L.image (fun a => 3 * a)
  let f (a : ℕ) : ℝ := 1 / a
  have hs : ∑ a ∈ A, f a = (∑ a ∈ B, f a) + ∑ a ∈ C, f a :=
    (sum_filter_add_sum_filter_not _ _ _).symm
  have hb : ∑ a ∈ B, f a = (∑ a ∈ L, f a) + ∑ a ∈ M, f a :=
    (sum_filter_add_sum_filter_not _ _ _).symm
  have memB {a} (ha : a ∈ B) : a ∈ A ∧ 2 * a ≤ n := mem_filter.mp ha
  have memL {a} (ha : a ∈ L) : a ∈ A ∧ 3 * a ≤ n :=
    ⟨(memB (mem_filter.mp ha).1).1, (mem_filter.mp ha).2⟩
  have unique {a b x : ℕ} (ha : a ∈ A) (hb : b ∈ A) (hx : 0 < x)
      (hn : x ≤ n) (had : a ∣ x) (hbd : b ∣ x) : a = b := by
    by_contra hne
    have hlt := hA.2 (mem_coe.mpr ha) (mem_coe.mpr hb) hne
    have hle := Nat.le_of_dvd hx (Nat.lcm_dvd had hbd)
    omega
  have hC : C ⊆ Ioc (n / 2) n := by
    intro a ha
    obtain ⟨ha, h2⟩ := mem_filter.mp ha
    have hu := (mem_Icc.mp (hA.1 ha)).2
    exact mem_Ioc.mpr ⟨by omega, hu⟩
  have hD : D ⊆ Ioc (n / 2) n := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := mem_image.mp hx
    exact mem_Ioc.mpr ⟨by have := hsmall a (memB ha).1; omega, (memB ha).2⟩
  have hE : E ⊆ Ioc (n / 2) n := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := mem_image.mp hx
    exact mem_Ioc.mpr ⟨by have := hsmall a (memL ha).1; omega, (memL ha).2⟩
  have hCD : Disjoint C D := by
    rw [disjoint_left]
    intro x hx hd
    obtain ⟨a, ha, rfl⟩ := mem_image.mp hd
    have hpos := (mem_Icc.mp (hA.1 (memB ha).1)).1
    have heq := unique (memB ha).1 (mem_filter.mp hx).1 (by omega) (memB ha).2
      (Dvd.intro_left 2 rfl) (dvd_refl _)
    omega
  have hCE : Disjoint C E := by
    rw [disjoint_left]
    intro x hx he
    obtain ⟨a, ha, rfl⟩ := mem_image.mp he
    have hpos := (mem_Icc.mp (hA.1 (memL ha).1)).1
    have heq := unique (memL ha).1 (mem_filter.mp hx).1 (by omega) (memL ha).2
      (Dvd.intro_left 3 rfl) (dvd_refl _)
    omega
  have hDE : Disjoint D E := by
    rw [disjoint_left]
    intro x hd he
    obtain ⟨a, ha, rfl⟩ := mem_image.mp hd
    obtain ⟨b, hb, hab⟩ := mem_image.mp he
    have hpos := (mem_Icc.mp (hA.1 (memB ha).1)).1
    have heq := unique (memB ha).1 (memL hb).1 (by omega) (memB ha).2
      (Dvd.intro_left 2 rfl) (Dvd.intro_left 3 hab)
    omega
  have hhigh : (∑ a ∈ C, f a) + (∑ a ∈ D, f a) + (∑ a ∈ E, f a) ≤
      ∑ a ∈ Ioc (n / 2) n, f a := by
    rw [← sum_union hCD, ← sum_union (disjoint_union_left.mpr ⟨hCE, hDE⟩)]
    exact sum_le_sum_of_subset_of_nonneg (union_subset (union_subset hC hD) hE)
      (fun a _ _ => by dsimp [f]; positivity)
  have hd : ∑ a ∈ D, f a = (1 / 2) * ∑ a ∈ B, f a := by
    rw [show D = B.image (fun a => 2 * a) from rfl,
      sum_image (fun x _ y _ h => by omega), mul_sum]
    refine sum_congr rfl (fun a _ => ?_)
    dsimp [f]
    push_cast
    ring
  have he : ∑ a ∈ E, f a = (1 / 3) * ∑ a ∈ L, f a := by
    rw [show E = L.image (fun a => 3 * a) from rfl,
      sum_image (fun x _ y _ h => by omega), mul_sum]
    refine sum_congr rfl (fun a _ => ?_)
    dsimp [f]
    push_cast
    ring
  have hm : ∑ a ∈ M, f a ≤ ∑ a ∈ Ioc (n / 3) (n / 2), f a := by
    apply sum_le_sum_of_subset_of_nonneg
    · intro a ha
      obtain ⟨ha, h3⟩ := mem_filter.mp ha
      have := (memB ha).2
      exact mem_Ioc.mpr ⟨by omega, by omega⟩
    · intro a _ _
      dsimp [f]
      positivity
  have hl : ∑ a ∈ L, f a ≤ ∑ a ∈ Ioc (n / 4) (n / 3), f a := by
    apply sum_le_sum_of_subset_of_nonneg
    · intro a ha
      have := hsmall a (memL ha).1
      have := (memL ha).2
      exact mem_Ioc.mpr ⟨by omega, by omega⟩
    · intro a _ _
      dsimp [f]
      positivity
  change ∑ a ∈ A, f a ≤ _
  rw [hd, he, hb] at hhigh
  rw [hs, hb]
  change _ ≤ (∑ a ∈ Ioc (n / 2) n, f a) +
    (1 / 2) * (∑ a ∈ Ioc (n / 3) (n / 2), f a) +
    (1 / 6) * (∑ a ∈ Ioc (n / 4) (n / 3), f a)
  linarith

private theorem finite_estimate (n : ℕ) (hn : 12 ≤ n) (hn' : n < 64) :
    (∑ a ∈ Ioc (n / 2) n, (1 : ℚ) / a) +
      (1 / 2) * (∑ a ∈ Ioc (n / 3) (n / 2), (1 : ℚ) / a) +
      (1 / 6) * (∑ a ∈ Ioc (n / 4) (n / 3), (1 : ℚ) / a) ≤ 1 := by
  have h : ∀ i : Fin 52,
      (∑ a ∈ Ioc ((i.val + 12) / 2) (i.val + 12), (1 : ℚ) / a) +
        (1 / 2) * (∑ a ∈ Ioc ((i.val + 12) / 3) ((i.val + 12) / 2), (1 : ℚ) / a) +
        (1 / 6) * (∑ a ∈ Ioc ((i.val + 12) / 4) ((i.val + 12) / 3), (1 : ℚ) / a) ≤ 1 := by
    decide +kernel
  simpa only [show n - 12 + 12 = n by omega] using h ⟨n - 12, by omega⟩

private theorem weighted_estimate (n : ℕ) (hn : 12 ≤ n) :
    (∑ a ∈ Ioc (n / 2) n, (1 : ℝ) / a) +
      (1 / 2) * (∑ a ∈ Ioc (n / 3) (n / 2), (1 : ℝ) / a) +
      (1 / 6) * (∑ a ∈ Ioc (n / 4) (n / 3), (1 : ℝ) / a) ≤ 1 := by
  rcases lt_or_ge n 64 with hs | hl
  · have h := finite_estimate n hn hs
    have hc := (Rat.cast_le (K := ℝ)).mpr h
    push_cast at hc
    exact hc
  have h₁ := harmonic_Ioc_le (n / 2) (by omega) n (by omega)
  have h₂ := harmonic_Ioc_le (n / 3) (by omega) (n / 2) (by omega)
  have h₃ := harmonic_Ioc_le (n / 4) (by omega) (n / 3) (by omega)
  let x : ℝ := n
  let u : ℝ := (n / 2 : ℕ)
  let v : ℝ := (n / 3 : ℕ)
  let w : ℝ := (n / 4 : ℕ)
  have hx : 0 < x := by dsimp [x]; exact_mod_cast (show 0 < n by omega)
  have hu : 0 < u := by dsimp [u]; exact_mod_cast (show 0 < n / 2 by omega)
  have hv : 0 < v := by dsimp [v]; exact_mod_cast (show 0 < n / 3 by omega)
  have hw : 0 < w := by dsimp [w]; exact_mod_cast (show 0 < n / 4 by omega)
  have hlog (y c : ℝ) (hy : 0 < y) (hxy : x / y ≤ c) :
      Real.log x - Real.log y ≤ Real.log c := by
    rw [← Real.log_div hx.ne' hy.ne']
    exact Real.log_le_log (div_pos hx hy) hxy
  have hxu : x / u ≤ 21 / 10 := by
    apply (div_le_iff₀ hu).2
    have h : 10 * n ≤ 21 * (n / 2) := by omega
    have hc : (10 : ℝ) * x ≤ 21 * u := by dsimp [x, u]; exact_mod_cast h
    linarith
  have hxv : x / v ≤ 31 / 10 := by
    apply (div_le_iff₀ hv).2
    have h : 10 * n ≤ 31 * (n / 3) := by omega
    have hc : (10 : ℝ) * x ≤ 31 * v := by dsimp [x, v]; exact_mod_cast h
    linarith
  have hxw : x / w ≤ 42 / 10 := by
    apply (div_le_iff₀ hw).2
    have h : 10 * n ≤ 42 * (n / 4) := by omega
    have hc : (10 : ℝ) * x ≤ 42 * w := by dsimp [x, w]; exact_mod_cast h
    linarith
  have hc : 3 * Real.log (21 / 10) + 2 * Real.log (31 / 10) + Real.log (42 / 10) < 6 := by
    have hEq : 3 * Real.log (21 / 10) + 2 * Real.log (31 / 10) + Real.log (42 / 10) =
        Real.log (((21 / 10 : ℝ) ^ 3 * (31 / 10) ^ 2) * (42 / 10)) := by
      rw [Real.log_mul (by positivity) (by norm_num),
        Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
      norm_num
    rw [hEq, Real.log_lt_iff_lt_exp (by positivity)]
    have hexp : Real.exp 6 = Real.exp 1 ^ 6 := by
      rw [← Real.exp_nat_mul]
      norm_num
    rw [hexp]
    have hp : (27 / 10 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    calc _ < (27 / 10 : ℝ) ^ 6 := by norm_num
         _ < _ := by gcongr
  have hU := hlog u (21 / 10) hu hxu
  have hV := hlog v (31 / 10) hv hxv
  have hW := hlog w (42 / 10) hw hxw
  change _ ≤ Real.log x - Real.log u at h₁
  change _ ≤ Real.log u - Real.log v at h₂
  change _ ≤ Real.log v - Real.log w at h₃
  linarith

end OMA.Erdos542Middle


theorem OMA.solution : OMA.R_Erdos542_erdos_542_variants_only_two_R1_H3_R1.H1 := by
  intro n A hn hA _ hsmall _
  have hsum : ∑ a ∈ A, (1 : ℝ) / a ≤ 1 :=
    (OMA.Erdos542Middle.reciprocal_bound n A hA hsmall).trans
      (OMA.Erdos542Middle.weighted_estimate n hn)
  have hcount := OMA.R_Erdos542_erdos_542_variants_only_two_R1.count_identity hA
  have hpos : ∀ a ∈ A, 0 < a := fun a ha => by
    have := mem_Icc.mp (hA.1 ha)
    omega
  have hreal : ∑ a ∈ A, ((n % a : ℕ) : ℝ) / a ≤ ((Erdos542.uncovered n A).card : ℝ) := by
    have hterm : ∀ a ∈ A, ((n % a : ℕ) : ℝ) / a = n * ((1 : ℝ) / a) - ((n / a : ℕ) : ℝ) := by
      intro a ha
      have ha0 : (a : ℝ) ≠ 0 := by exact_mod_cast (hpos a ha).ne'
      have hdm : (n : ℝ) = (a : ℝ) * ((n / a : ℕ) : ℝ) + ((n % a : ℕ) : ℝ) := by
        exact_mod_cast (Nat.div_add_mod n a).symm
      field_simp
      linarith
    rw [sum_congr rfl hterm, sum_sub_distrib, ← mul_sum]
    have hc : (∑ a ∈ A, ((n / a : ℕ) : ℝ)) + ((Erdos542.uncovered n A).card : ℝ) = n := by
      exact_mod_cast hcount
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith
  have hcast : ((∑ a ∈ A, ((n % a : ℕ) : ℚ) / a : ℚ) : ℝ) = ∑ a ∈ A, ((n % a : ℕ) : ℝ) / a := by
    push_cast
    rfl
  have : ((∑ a ∈ A, ((n % a : ℕ) : ℚ) / a : ℚ) : ℝ) ≤ (((Erdos542.uncovered n A).card : ℚ) : ℝ) := by
    rw [hcast]
    push_cast
    exact hreal
  exact_mod_cast this
