import OMAReductions.R_ArtinPrimitiveRootsConjecture_conditional_artin_primitive_roots_parts_i_R1

-- Step ArtinPrimitiveRootsConjecture.conditional_artin_primitive_roots.parts.i.R1.H2: hypothesis H2 of reduction ArtinPrimitiveRootsConjecture.conditional_artin_primitive_roots.parts.i.R1
-- Credit: @senamakel
-- Brun-Titchmarsh for primes 1 mod q with the constant 20000, by the Selberg upper-bound sieve
-- (sieve vendored from PrimeNumberTheoremAnd, arithmetic-progression set-up from artin-grh).

section
noncomputable section
open scoped BigOperators ArithmeticFunction ArithmeticFunction.Moebius ArithmeticFunction.omega
open Nat ArithmeticFunction Finset
namespace ArithmeticFunction.IsMultiplicative
variable {R : Type*}
end ArithmeticFunction.IsMultiplicative
namespace Aux
theorem sum_over_dvd_ite {α : Type _} [Ring α] {P : ℕ} (hP : P ≠ 0) {n : ℕ} (hn : n ∣ P)
    {f : ℕ → α} : ∑ d ∈ n.divisors, f d = ∑ d ∈ P.divisors, if d ∣ n then f d else 0 :=
  by
  rw [←Finset.sum_filter, Nat.divisors_filter_dvd_of_dvd hP hn]
theorem ite_sum_zero {p : Prop} [Decidable p] (s : Finset ℕ) (f : ℕ → ℝ) :
    (if p then (∑ x ∈ s, f x) else 0) = ∑ x ∈ s, if p then f x else 0 := by
  split_ifs <;> simp
theorem conv_lambda_sq_larger_sum (f : ℕ → ℕ → ℕ → ℝ) (n : ℕ) :
    (∑ d ∈ n.divisors,
        ∑ d1 ∈ d.divisors,
          ∑ d2 ∈ d.divisors, if d = Nat.lcm d1 d2 then f d1 d2 d else 0) =
      ∑ d ∈ n.divisors,
        ∑ d1 ∈ n.divisors,
          ∑ d2 ∈ n.divisors, if d = Nat.lcm d1 d2 then f d1 d2 d else 0 := by
  apply sum_congr rfl; intro d hd
  rw [mem_divisors] at hd
  simp_rw [←Nat.divisors_filter_dvd_of_dvd hd.2 hd.1, sum_filter, ←ite_and, ite_sum_zero,
    ←ite_and]
  congr with d1
  congr with d2
  congr
  rw [eq_iff_iff]
  refine ⟨fun ⟨_, _, h⟩ ↦ h, ?_⟩
  rintro rfl
  exact ⟨Nat.dvd_lcm_left d1 d2, Nat.dvd_lcm_right d1 d2, rfl⟩
theorem moebius_inv_dvd_lower_bound (l m : ℕ) (hm : Squarefree m) :
    (∑ d ∈ m.divisors, if l ∣ d then (μ d:ℤ) else 0) = if l = m then (μ l:ℤ) else 0 := by
  have hm_pos : 0 < m := Nat.pos_of_ne_zero hm.ne_zero
  revert hm
  revert m
  apply (ArithmeticFunction.sum_eq_iff_sum_smul_moebius_eq_on
    {n | Squarefree n} (fun _ _ => Squarefree.squarefree_of_dvd)).mpr
  intro m hm_pos hm
  rw [sum_divisorsAntidiagonal' (f:= fun x y => μ x • if l=y then μ l else 0)]
  by_cases hl : l ∣ m
  · rw [if_pos hl, sum_eq_single l]
    · have hmul : m / l * l = m := Nat.div_mul_cancel hl
      rw [if_pos rfl, smul_eq_mul, ←isMultiplicative_moebius.map_mul_of_coprime,
        hmul]
      apply coprime_of_squarefree_mul; rw [hmul]; exact hm
    · intro d _ hdl; rw [if_neg hdl.symm, smul_zero]
    · intro h; rw[mem_divisors] at h; exfalso; exact h ⟨hl, (Nat.ne_of_lt hm_pos).symm⟩
  · rw [if_neg hl, sum_eq_zero]; intro d hd
    rw [if_neg, smul_zero]
    by_contra h; rw [←h] at hd; exact hl (dvd_of_mem_divisors hd)
theorem moebius_inv_dvd_lower_bound' {P : ℕ} (hP : Squarefree P) (l m : ℕ) (hm : m ∣ P) :
    (∑ d ∈ P.divisors, if l ∣ d ∧ d ∣ m then μ d else 0) = if l = m then μ l else 0 := by
  rw [←moebius_inv_dvd_lower_bound _ _ (Squarefree.squarefree_of_dvd hm hP),
    sum_over_dvd_ite hP.ne_zero hm]
  simp_rw[ite_and, ←sum_filter, filter_comm]
theorem moebius_inv_dvd_lower_bound_real {P : ℕ} (hP : Squarefree P) (l m : ℕ) (hm : m ∣ P) :
    (∑ d ∈ P.divisors, if l ∣ d ∧ d ∣ m then (μ d : ℝ) else 0) =
      if l = m then (μ l : ℝ) else 0 := by
  norm_cast
  apply moebius_inv_dvd_lower_bound' hP l m hm
theorem multiplicative_zero_of_zero_dvd (f : ArithmeticFunction ℝ) (h_mult : IsMultiplicative f)
    {m n : ℕ} (h_sq : Squarefree n) (hmn : m ∣ n) (h_zero : f m = 0) : f n = 0 := by
  rcases hmn with ⟨k, rfl⟩
  simp only [MulZeroClass.zero_mul,
    h_mult.map_mul_of_coprime (coprime_of_squarefree_mul h_sq), h_zero]
theorem div_mult_of_dvd_squarefree (f : ArithmeticFunction ℝ) (h_mult : IsMultiplicative f)
    (l d : ℕ) (hdl : d ∣ l) (hl : Squarefree l) (hd : f d ≠ 0) : f l / f d = f (l / d) := by
  apply div_eq_of_eq_mul hd
  rw [← h_mult.right, Nat.div_mul_cancel hdl]
  apply coprime_of_squarefree_mul
  convert hl
  exact Nat.div_mul_cancel hdl
theorem inv_sub_antitoneOn_gt
    {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] (c : R) :
    AntitoneOn (fun x:R ↦ (x-c)⁻¹) (Set.Ioi c) := by
  refine antitoneOn_iff_forall_lt.mpr ?_
  intro a ha b hb hab
  rw [Set.mem_Ioi] at ha hb
  gcongr
theorem inv_sub_antitoneOn_Icc
    {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    (a b c : R) (ha : c < a) :
    AntitoneOn (fun x ↦ (x-c)⁻¹) (Set.Icc a b) := by
  by_cases hab : a ≤ b
  · exact inv_sub_antitoneOn_gt c |>.mono <| (Set.Icc_subset_Ioi_iff hab).mpr ha
  · simp [hab, Set.Subsingleton.antitoneOn]
theorem inv_antitoneOn_Icc {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    (a b : R) (ha : 0 < a) :
    AntitoneOn (fun x ↦ x⁻¹) (Set.Icc a b) := by
  convert inv_sub_antitoneOn_Icc a b 0 ha; ring
theorem log_add_one_le_sum_inv (n : ℕ) :
    Real.log ↑(n+1) ≤ ∑ d ∈ Finset.Icc 1 n, (d:ℝ)⁻¹ := by
  calc _ = ∫ x in (1)..↑(n+1), x⁻¹ := ?_
       _ = ∫ x in (1:ℕ)..↑(n+1), x⁻¹ := ?_
       _ ≤ _ := ?_
  · rw[integral_inv (by simp[(show ¬ (1:ℝ) ≤ 0 by norm_num)] )]; congr; ring
  · norm_num
  · apply AntitoneOn.integral_le_sum_Ico (by norm_num)
    apply inv_antitoneOn_Icc
    norm_num
theorem log_le_sum_inv (y : ℝ) (hy : 1 ≤ y) :
    Real.log y ≤ ∑ d ∈ Finset.Icc 1 (⌊y⌋₊), (d:ℝ)⁻¹ := by
  calc _ ≤ Real.log ↑(Nat.floor y + 1) := ?_
       _ ≤ _ := ?_
  · gcongr
    apply (le_ceil y).trans
    norm_cast
    exact ceil_le_floor_add_one y
  · apply log_add_one_le_sum_inv
theorem sum_inv_le_log (n : ℕ) (hn : 1 ≤ n) :
    ∑ d ∈ Finset.Icc 1 n, (d : ℝ)⁻¹ ≤ 1 + Real.log ↑n :=
  by
  rw [← Finset.sum_erase_add (Icc 1 n) _ (by simp [hn] : 1 ∈ Icc 1 n), add_comm]
  gcongr
  · norm_num
  simp only [Icc_erase_left]
  calc
    ∑ d ∈ Ico 2 (n + 1), (d : ℝ)⁻¹ = ∑ d ∈ Ico 2 (n + 1), (↑(d + 1) - 1)⁻¹ := ?_
    _ ≤ ∫ x in (2).. ↑(n + 1), (x - 1)⁻¹  := ?_
    _ = Real.log ↑n := ?_
  · congr; norm_num;
  · apply @AntitoneOn.sum_le_integral_Ico 2 (n + 1) fun x : ℝ => (x - 1)⁻¹
    · linarith [hn]
    apply inv_sub_antitoneOn_Icc; norm_num
  rw [intervalIntegral.integral_comp_sub_right _ 1, integral_inv]
  · norm_num
  norm_num; simp[hn, show (0:ℝ) < 1 by norm_num]
theorem sum_inv_le_log_real (y : ℝ) (hy : 1 ≤ y) :
    ∑ d ∈ Finset.Icc 1 (⌊y⌋₊), (d:ℝ)⁻¹ ≤ 1 + Real.log y := by
  trans (1 + Real.log (⌊y⌋₊))
  · apply sum_inv_le_log (⌊y⌋₊)
    apply le_floor; norm_cast
  gcongr
  · norm_cast; apply Nat.lt_of_succ_le; apply le_floor; norm_cast
  · apply floor_le; linarith
theorem sum_pow_cardDistinctFactors_div_self_le_log_pow {P k : ℕ} (x : ℝ) (hx : 1 ≤ x)
    (hP : Squarefree P) :
    (∑ d ∈ P.divisors, if d ≤ x then (k:ℝ) ^ (ω d) / (d : ℝ) else (0 : ℝ))
    ≤ (1 + Real.log x) ^ k := by
  have hx_pos : 0 < x := by
    linarith
  calc
    _ = ∑ d ∈ P.divisors,
          ∑ a ∈ Fintype.piFinset fun _i : Fin k => P.divisors,
            if ∏ i, a i = d ∧ d ∣ P then if ↑d ≤ x then (d : ℝ)⁻¹ else 0 else 0 := ?_
    _ = ∑ a ∈ Fintype.piFinset fun _i : Fin k => P.divisors,
          if ∏ i, a i ∣ P then if ↑(∏ i, a i) ≤ x then ∏ i, (a i : ℝ)⁻¹ else 0 else 0 := ?_
    _ ≤ ∑ a ∈ Fintype.piFinset fun _i : Fin k => P.divisors,
          if ↑(∏ i, a i) ≤ x then ∏ i, (a i : ℝ)⁻¹ else 0 := ?_
    _ ≤ ∑ a ∈ Fintype.piFinset fun _i : Fin k => P.divisors,
          ∏ i, if ↑(a i) ≤ x then (a i : ℝ)⁻¹ else 0 := ?_
    _ = ∏ _i : Fin k, ∑ d ∈ P.divisors, if ↑d ≤ x then (d : ℝ)⁻¹ else 0 := by rw [prod_univ_sum]
    _ = (∑ d ∈ P.divisors, if ↑d ≤ x then (d : ℝ)⁻¹ else 0) ^ k := by
      rw [prod_const, Finset.card_fin]
    _ ≤ (1 + Real.log x) ^ k := ?_
  · apply sum_congr rfl; intro d hd
    rw [mem_divisors] at hd
    simp_rw [ite_and];
    rw [← sum_filter, Finset.sum_const, ← finMulAntidiag_eq_piFinset_divisors_filter hd.1 hd.2,
      card_finMulAntidiag_of_squarefree <| hP.squarefree_of_dvd hd.1, if_pos hd.1]
    simp only [div_eq_mul_inv, nsmul_eq_mul, cast_pow, mul_ite, mul_zero]
  · rw [sum_comm]; apply sum_congr rfl; intro a _; rw [sum_eq_single (∏ i, a i)]
    · apply if_ctx_congr _ _ (fun _ => rfl)
      · rw [Iff.comm, iff_and_self]; exact fun _ => rfl
      · intro; rw [cast_prod, ← prod_inv_distrib]
    · exact fun d _ hd_ne ↦ if_neg fun h => hd_ne.symm h.1
    · exact fun h ↦ if_neg fun h' => h (mem_divisors.mpr ⟨h'.2, hP.ne_zero⟩)
  · apply sum_le_sum; intro a _
    by_cases h : (∏ i, a i ∣ P)
    · rw [if_pos h]
    rw [if_neg h]
    split_ifs with h'
    · apply prod_nonneg; intro i _; norm_num
    · rfl
  · apply sum_le_sum; intro a ha
    split_ifs with h
    · gcongr with i hi
      rw [if_pos]
      apply le_trans _ h
      norm_cast
      rw [←prod_erase_mul (a:=i) (h:= hi)]
      apply Nat.le_mul_of_pos_left
      rw [Fintype.mem_piFinset] at ha
      apply prod_pos; intro j _; apply pos_of_mem_divisors (ha j)
    · apply prod_nonneg; intro j _
      split_ifs
      · norm_num
      · rfl
  · rw [←sum_filter]
    gcongr
    trans (∑ d ∈ Icc 1 (floor x), (d:ℝ)⁻¹)
    · apply sum_le_sum_of_subset_of_nonneg
      · intro d; rw[mem_filter, mem_Icc]
        intro hd
        constructor
        · rw [Nat.succ_le_iff]; exact pos_of_mem_divisors hd.1
        · rw [le_floor_iff hx_pos.le]
          exact hd.2
      · norm_num
    apply sum_inv_le_log_real
    linarith
theorem sum_pow_cardDistinctFactors_le_self_mul_log_pow {P h : ℕ} (x : ℝ) (hx : 1 ≤ x)
    (hP : Squarefree P) :
    (∑ d ∈ P.divisors, if ↑d ≤ x then (h : ℝ) ^ ω d else (0 : ℝ)) ≤
      x * (1 + Real.log x) ^ h := by
  trans (∑ d ∈ P.divisors, x * if ↑d ≤ x then (h : ℝ) ^ ω d / d else (0 : ℝ))
  · simp_rw [mul_ite, mul_zero, ←sum_filter]
    gcongr with i hi
    rw [div_eq_mul_inv, mul_comm _ (i:ℝ)⁻¹, ←mul_assoc]
    trans (1*(h:ℝ)^ω i)
    · rw [one_mul]
    gcongr
    rw [mem_filter] at hi
    rw [←div_eq_mul_inv]
    apply one_le_div (by norm_cast; apply Nat.pos_of_mem_divisors hi.1) |>.mpr hi.2
  rw [←mul_sum];
  gcongr
  apply sum_pow_cardDistinctFactors_div_self_le_log_pow x hx hP
end Aux
end
end

section
noncomputable section
open scoped BigOperators ArithmeticFunction ArithmeticFunction.Moebius
open Finset Real Nat Aux BoundingSieve
namespace SelbergSieve
variable (s : BoundingSieve)
def selbergTerms : ArithmeticFunction ℝ :=
  s.nu.pmul (.prodPrimeFactors fun p =>  1 / (1 - (BoundingSieve.nu s) p))
theorem selbergTerms_apply (d : ℕ) :
    (SelbergSieve.selbergTerms s) d = (BoundingSieve.nu s) d * ∏ p ∈ d.primeFactors, 1/(1 - (BoundingSieve.nu s) p) := by
  unfold selbergTerms
  by_cases h : d=0
  · rw [h]; simp
  rw [ArithmeticFunction.pmul_apply, ArithmeticFunction.prodPrimeFactors_apply h]
section UpperBoundSieve
structure UpperBoundSieve where mk ::
  μPlus : ℕ → ℝ
  hμPlus : IsUpperMoebius μPlus
instance ubToμPlus : CoeFun UpperBoundSieve fun _ => ℕ → ℝ where coe ub := ub.μPlus
def IsLowerMoebius (μMinus : ℕ → ℝ) : Prop :=
  ∀ n : ℕ, ∑ d ∈ n.divisors, μMinus d ≤ (if n=1 then 1 else 0)
structure LowerBoundSieve where mk ::
  μMinus : ℕ → ℝ
  hμMinus : IsLowerMoebius μMinus
instance lbToμMinus : CoeFun LowerBoundSieve fun _ => ℕ → ℝ where coe lb := lb.μMinus
end UpperBoundSieve
section SieveLemmas
theorem selbergTerms_pos (l : ℕ) (hl : l ∣ (BoundingSieve.prodPrimes s)) : 0 < (SelbergSieve.selbergTerms s) l := by
  rw [selbergTerms_apply]
  apply mul_pos
  · exact nu_pos_of_dvd_prodPrimes hl
  apply prod_pos
  intro p hp
  rw [one_div_pos]
  have hp_prime : p.Prime := prime_of_mem_primeFactors hp
  have hp_dvd : p ∣ (BoundingSieve.prodPrimes s) := (Nat.dvd_of_mem_primeFactors hp).trans hl
  linarith only [s.nu_lt_one_of_prime p hp_prime hp_dvd]
theorem selbergTerms_mult : ArithmeticFunction.IsMultiplicative (SelbergSieve.selbergTerms s) := by
  unfold selbergTerms
  arith_mult
theorem one_div_selbergTerms_eq_conv_moebius_nu (l : ℕ) (hl : Squarefree l)
    (hnu_nonzero : (BoundingSieve.nu s) l ≠ 0) : 1 / (SelbergSieve.selbergTerms s) l = ∑ d ∈ l.divisors, (μ <| l / d) * ((BoundingSieve.nu s) d)⁻¹ :=
  by
  rw [selbergTerms_apply]
  simp only [one_div, prod_inv_distrib, mul_inv, inv_inv]
  rw [(s.nu_mult).prodPrimeFactors_one_sub_of_squarefree _ hl]
  rw [mul_sum]
  apply symm
  rw [← Nat.sum_divisorsAntidiagonal' fun d e : ℕ => ↑(μ d) * ((BoundingSieve.nu s) e)⁻¹]
  rw [Nat.sum_divisorsAntidiagonal fun d e : ℕ => ↑(μ d) * ((BoundingSieve.nu s) e)⁻¹]
  apply sum_congr rfl; intro d hd
  have hd_dvd : d ∣ l := dvd_of_mem_divisors hd
  rw [←div_mult_of_dvd_squarefree (BoundingSieve.nu s) s.nu_mult l d (dvd_of_mem_divisors hd) hl, inv_div]
  · ring
  revert hnu_nonzero; contrapose!
  exact multiplicative_zero_of_zero_dvd (BoundingSieve.nu s) s.nu_mult hl hd_dvd
theorem nu_eq_conv_one_div_selbergTerms (d : ℕ) (hdP : d ∣ (BoundingSieve.prodPrimes s)) :
    ((BoundingSieve.nu s) d)⁻¹ = ∑ l ∈ divisors (BoundingSieve.prodPrimes s), if l ∣ d then 1 / (SelbergSieve.selbergTerms s) l else 0 := by
  apply symm
  rw [←sum_filter, Nat.divisors_filter_dvd_of_dvd prodPrimes_ne_zero hdP]
  have hd_pos : 0 < d := Nat.pos_of_ne_zero <| ne_zero_of_dvd_ne_zero prodPrimes_ne_zero hdP
  revert hdP; revert d
  apply (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq_on {d | d ∣ (BoundingSieve.prodPrimes s)} (fun _ _ => Nat.dvd_trans)).mpr
  intro l _ hlP
  rw [sum_divisorsAntidiagonal' (f:=fun x y => (μ <| x) * ((BoundingSieve.nu s) y)⁻¹) (n:=l)]
  apply symm
  exact one_div_selbergTerms_eq_conv_moebius_nu _ l
    (Squarefree.squarefree_of_dvd hlP s.prodPrimes_squarefree)
    (_root_.ne_of_gt <| nu_pos_of_dvd_prodPrimes hlP)
theorem conv_selbergTerms_eq_selbergTerms_mul_nu {d : ℕ} (hd : d ∣ (BoundingSieve.prodPrimes s)) :
    (∑ l ∈ divisors (BoundingSieve.prodPrimes s), if l ∣ d then (SelbergSieve.selbergTerms s) l else 0) = (SelbergSieve.selbergTerms s) d * ((BoundingSieve.nu s) d)⁻¹ := by
  calc
    (∑ l ∈ divisors (BoundingSieve.prodPrimes s), if l ∣ d then (SelbergSieve.selbergTerms s) l else 0) =
        ∑ l ∈ divisors (BoundingSieve.prodPrimes s), if l ∣ d then (SelbergSieve.selbergTerms s) (d / l) else 0 := by
      rw [← sum_over_dvd_ite prodPrimes_ne_zero hd,
        ← Nat.sum_divisorsAntidiagonal fun x _ => (SelbergSieve.selbergTerms s) x,
        Nat.sum_divisorsAntidiagonal' fun x _ => (SelbergSieve.selbergTerms s) x, sum_over_dvd_ite prodPrimes_ne_zero hd]
    _ = (SelbergSieve.selbergTerms s) d * ∑ l ∈ divisors (BoundingSieve.prodPrimes s), if l ∣ d then 1 / (SelbergSieve.selbergTerms s) l else 0 := by
      rw [mul_sum]; apply sum_congr rfl; intro l hl
      rw [mul_ite_zero]; apply if_ctx_congr Iff.rfl _ (fun _ => rfl); intro h
      rw [← div_mult_of_dvd_squarefree (SelbergSieve.selbergTerms s) (selbergTerms_mult s) d l h]
      · ring
      · apply Squarefree.squarefree_of_dvd hd s.prodPrimes_squarefree
      · apply _root_.ne_of_gt; rw [mem_divisors] at hl; apply selbergTerms_pos; exact hl.left
    _ = (SelbergSieve.selbergTerms s) d * ((BoundingSieve.nu s) d)⁻¹ := by rw [← nu_eq_conv_one_div_selbergTerms s d hd]
theorem siftedSum_le_mainSum_errSum_of_UpperBoundSieve (μPlus : UpperBoundSieve) :
    siftedSum (s := s) ≤ (BoundingSieve.totalMass s) * mainSum (s := s) μPlus + errSum (s := s) μPlus := by
  apply siftedSum_le_mainSum_errSum_of_upperMoebius _ μPlus.hμPlus
end SieveLemmas
section LambdaSquared
def lambdaSquared (weights : ℕ → ℝ) : ℕ → ℝ := fun d =>
  ∑ d1 ∈ d.divisors, ∑ d2 ∈ d.divisors,
    if d = Nat.lcm d1 d2 then weights d1 * weights d2 else 0
private theorem lambdaSquared_eq_zero_of_support_wlog {w : ℕ → ℝ} {y : ℝ}
    (hw : ∀ (d : ℕ), ¬d ^ 2 ≤ y → w d = 0)
    {d : ℕ} (hd : ¬↑d ≤ y) (d1 : ℕ) (d2 : ℕ) (h : d = Nat.lcm d1 d2) (hle : d1 ≤ d2) :
    w d1 * w d2 = 0 := by
  rw [hw d2, mul_zero]
  by_contra hyp; apply hd
  apply le_trans _ hyp
  norm_cast
  calc _ ≤ (d1.lcm d2) := by rw [h]
      _ ≤ (d1*d2) := Nat.div_le_self _ _
      _ ≤ _       := ?_
  · rw [sq]; gcongr
theorem lambdaSquared_eq_zero_of_support (w : ℕ → ℝ) (y : ℝ)
    (hw : ∀ d : ℕ, ¬d ^ 2 ≤ y → w d = 0) (d : ℕ) (hd : ¬d ≤ y) :
    lambdaSquared w d = 0 := by
  dsimp only [lambdaSquared]
  by_cases hy : 0 ≤ y
  swap
  · push Not at hd hy
    have : ∀ d' : ℕ, w d' = 0 := by
      intro d'; apply hw
      have : (0:ℝ) ≤ (d') ^ 2 := by norm_num
      linarith
    apply sum_eq_zero; intro d1 _
    apply sum_eq_zero; intro d2 _
    rw [this d1, this d2]
    simp only [mul_zero, ite_self]
  apply sum_eq_zero; intro d1 _
  apply sum_eq_zero; intro d2 _
  split_ifs with h
  swap
  · rfl
  rcases Nat.le_or_le d1 d2 with hle | hle
  · apply lambdaSquared_eq_zero_of_support_wlog hw hd d1 d2 h hle
  · rw [mul_comm]
    apply lambdaSquared_eq_zero_of_support_wlog hw hd d2 d1
      (Nat.lcm_comm d1 d2 ▸ h) hle
theorem upperMoebius_of_lambda_sq (weights : ℕ → ℝ) (hw : weights 1 = 1) :
    IsUpperMoebius <| lambdaSquared weights := by
  dsimp [IsUpperMoebius, lambdaSquared]
  intro n
  have h_sq :
    (∑ d ∈ n.divisors, ∑ d1 ∈ d.divisors, ∑ d2 ∈ d.divisors,
      if d = Nat.lcm d1 d2 then weights d1 * weights d2 else 0) =
      (∑ d ∈ n.divisors, weights d) ^ 2 := by
    rw [sq, mul_sum, conv_lambda_sq_larger_sum _ n, sum_comm]
    apply sum_congr rfl; intro d1 hd1
    rw [sum_mul, sum_comm]
    apply sum_congr rfl; intro d2 hd2
    rw [sum_ite_eq_of_mem']
    · ring
    rw [mem_divisors, Nat.lcm_dvd_iff]
    exact ⟨⟨dvd_of_mem_divisors hd1, dvd_of_mem_divisors hd2⟩, (mem_divisors.mp hd1).2⟩
  rw [h_sq]
  split_ifs with hn
  · rw [hn]; simp [hw]
  · apply sq_nonneg
theorem lambdaSquared_mainSum_eq_quad_form (w : ℕ → ℝ) :
    mainSum (s := s) (lambdaSquared w) =
      ∑ d1 ∈ divisors (BoundingSieve.prodPrimes s), ∑ d2 ∈ divisors (BoundingSieve.prodPrimes s),
        (BoundingSieve.nu s) d1 * w d1 * (BoundingSieve.nu s) d2 * w d2 * ((BoundingSieve.nu s) (d1.gcd d2))⁻¹ := by
  dsimp only [mainSum, lambdaSquared]
  trans (∑ d ∈ divisors (BoundingSieve.prodPrimes s), ∑ d1 ∈ divisors d, ∑ d2 ∈ divisors d,
          if d = d1.lcm d2 then w d1 * w d2 * (BoundingSieve.nu s) d else 0)
  · rw [sum_congr rfl]; intro d _
    rw [sum_mul, sum_congr rfl]; intro d1 _
    rw [sum_mul, sum_congr rfl]; intro d2 _
    rw [ite_zero_mul]
  trans (∑ d ∈ divisors (BoundingSieve.prodPrimes s), ∑ d1 ∈ divisors (BoundingSieve.prodPrimes s), ∑ d2 ∈ divisors (BoundingSieve.prodPrimes s),
          if d = d1.lcm d2 then w d1 * w d2 * (BoundingSieve.nu s) d else 0)
  · apply conv_lambda_sq_larger_sum
  rw [sum_comm, sum_congr rfl]; intro d1 hd1
  rw [sum_comm, sum_congr rfl]; intro d2 hd2
  have h : d1.lcm d2 ∣ (BoundingSieve.prodPrimes s) :=
    Nat.lcm_dvd_iff.mpr ⟨dvd_of_mem_divisors hd1, dvd_of_mem_divisors hd2⟩
  rw [sum_ite_eq_of_mem' (divisors (BoundingSieve.prodPrimes s)) (d1.lcm d2) _ (mem_divisors.mpr ⟨h, prodPrimes_ne_zero⟩)]
  rw [s.nu_mult.map_lcm]
  · ring
  refine _root_.ne_of_gt (nu_pos_of_dvd_prodPrimes ?_)
  trans d1
  · exact Nat.gcd_dvd_left d1 d2
  · exact dvd_of_mem_divisors hd1
theorem lambdaSquared_mainSum_eq_diag_quad_form (w : ℕ → ℝ) :
    mainSum (s := s) (lambdaSquared w) =
      ∑ l ∈ divisors (BoundingSieve.prodPrimes s),
        1 / (SelbergSieve.selbergTerms s) l * (∑ d ∈ divisors (BoundingSieve.prodPrimes s), if l ∣ d then (BoundingSieve.nu s) d * w d else 0) ^ 2 :=
  by
  rw [lambdaSquared_mainSum_eq_quad_form s w]
  trans (∑ d1 ∈ divisors (BoundingSieve.prodPrimes s), ∑ d2 ∈ divisors (BoundingSieve.prodPrimes s), (∑ l ∈ divisors (BoundingSieve.prodPrimes s),
          if l ∣ d1.gcd d2 then 1 / (SelbergSieve.selbergTerms s) l * ((BoundingSieve.nu s) d1 * w d1) * ((BoundingSieve.nu s) d2 * w d2) else 0))
  · apply sum_congr rfl; intro d1 hd1; apply sum_congr rfl; intro d2 _
    have hgcd_dvd: d1.gcd d2 ∣ (BoundingSieve.prodPrimes s) := Trans.trans (Nat.gcd_dvd_left d1 d2) (dvd_of_mem_divisors hd1)
    rw [nu_eq_conv_one_div_selbergTerms s _ hgcd_dvd, mul_sum]
    apply sum_congr rfl; intro l _
    rw [mul_ite_zero]; apply if_congr Iff.rfl _ rfl
    ring
  trans (∑ l ∈ divisors (BoundingSieve.prodPrimes s), ∑ d1 ∈ divisors (BoundingSieve.prodPrimes s), ∑ d2 ∈ divisors (BoundingSieve.prodPrimes s),
        if l ∣ Nat.gcd d1 d2 then 1 / selbergTerms s l * ((BoundingSieve.nu s) d1 * w d1) * ((BoundingSieve.nu s) d2 * w d2) else 0)
  · apply symm; rw [sum_comm, sum_congr rfl]; intro d1 _
    rw [sum_comm]
  apply sum_congr rfl; intro l _
  rw [sq, sum_mul, mul_sum, sum_congr rfl]; intro d1 _
  rw [mul_sum, mul_sum, sum_congr rfl]; intro d2 _
  rw [ite_zero_mul_ite_zero, mul_ite_zero]
  apply if_congr (Nat.dvd_gcd_iff) _ rfl;
  ring
end LambdaSquared
end SelbergSieve
end
end

section
noncomputable section
open scoped BigOperators Classical SelbergSieve ArithmeticFunction.Moebius ArithmeticFunction.omega
open Finset Real Nat SelbergSieve.UpperBoundSieve ArithmeticFunction SelbergSieve BoundingSieve
namespace SelbergSieve
variable (s : SelbergSieve)
@[simp]
def selbergBoundingSum : ℝ :=
  ∑ l ∈ divisors (BoundingSieve.prodPrimes (SelbergSieve.toBoundingSieve s)), if l ^ 2 ≤ (SelbergSieve.level s) then (SelbergSieve.selbergTerms (SelbergSieve.toBoundingSieve s)) l else 0
theorem selbergBoundingSum_pos :
    0 < (SelbergSieve.selbergBoundingSum s) := by
  dsimp only [selbergBoundingSum]
  rw [← sum_filter]
  apply sum_pos;
  · intro l hl
    rw [mem_filter, mem_divisors] at hl
    · apply selbergTerms_pos _ _ (hl.1.1)
  · simp_rw [Finset.Nonempty, mem_filter]; use 1
    constructor
    · apply one_mem_divisors.mpr prodPrimes_ne_zero
    rw [cast_one, one_pow]
    exact s.one_le_level
theorem selbergBoundingSum_ne_zero : (SelbergSieve.selbergBoundingSum s) ≠ 0 := by
  apply _root_.ne_of_gt
  exact s.selbergBoundingSum_pos
theorem selbergBoundingSum_nonneg : 0 ≤ (SelbergSieve.selbergBoundingSum s) := _root_.le_of_lt s.selbergBoundingSum_pos
def selbergWeights : ℕ → ℝ := fun d =>
  if d ∣ (BoundingSieve.prodPrimes (SelbergSieve.toBoundingSieve s)) then
    ((BoundingSieve.nu (SelbergSieve.toBoundingSieve s)) d)⁻¹ * (SelbergSieve.selbergTerms (SelbergSieve.toBoundingSieve s)) d * μ d * (SelbergSieve.selbergBoundingSum s)⁻¹ *
      ∑ m ∈ divisors (BoundingSieve.prodPrimes (SelbergSieve.toBoundingSieve s)), if (d * m) ^ 2 ≤ (SelbergSieve.level s) ∧ m.Coprime d then (SelbergSieve.selbergTerms (SelbergSieve.toBoundingSieve s)) m else 0
  else 0
theorem selbergWeights_eq_zero_of_not_dvd {d : ℕ} (hd : ¬ d ∣ (BoundingSieve.prodPrimes (SelbergSieve.toBoundingSieve s))) :
    (SelbergSieve.selbergWeights s) d = 0 := by
  rw [selbergWeights, if_neg hd]
theorem selbergWeights_eq_zero (d : ℕ) (hd : ¬d ^ 2 ≤ (SelbergSieve.level s)) :
    (SelbergSieve.selbergWeights s) d = 0 := by
  dsimp only [selbergWeights]
  split_ifs with h
  · rw [mul_eq_zero_of_right _]
    apply Finset.sum_eq_zero
    refine fun m hm => if_neg ?_
    intro hyp
    have : (d^2:ℝ) ≤ (d*m)^2 := by
      norm_cast;
      refine Nat.pow_le_pow_left ?h 2
      exact Nat.le_mul_of_pos_right _ (Nat.pos_of_mem_divisors hm)
    linarith [hyp.1]
  · rfl
theorem selbergWeights_mul_mu_nonneg (d : ℕ) (hdP : d ∣ (BoundingSieve.prodPrimes (SelbergSieve.toBoundingSieve s))) :
    0 ≤ (SelbergSieve.selbergWeights s) d * μ d := by
  dsimp only [selbergWeights]
  rw [if_pos hdP, mul_assoc]
  trans ((μ d :ℝ)^2 * ((BoundingSieve.nu (SelbergSieve.toBoundingSieve s)) d)⁻¹ * (SelbergSieve.selbergTerms (SelbergSieve.toBoundingSieve s)) d * (SelbergSieve.selbergBoundingSum s)⁻¹ * ∑ m ∈ divisors (BoundingSieve.prodPrimes (SelbergSieve.toBoundingSieve s)),
          if (d * m) ^ 2 ≤ (SelbergSieve.level s) ∧ Coprime m d then (SelbergSieve.selbergTerms (SelbergSieve.toBoundingSieve s)) m else 0)
  swap
  · apply le_of_eq; ring
  refine mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ?_ ?_) ?_) ?_) ?_
  · apply sq_nonneg
  · exact inv_nonneg.mpr (le_of_lt <| nu_pos_of_dvd_prodPrimes hdP)
  · exact le_of_lt <| selbergTerms_pos _ d hdP
  · exact inv_nonneg.mpr s.selbergBoundingSum_nonneg
  apply sum_nonneg; intro m hm
  split_ifs with h
  · exact le_of_lt <| selbergTerms_pos _ m (dvd_of_mem_divisors hm)
  · rfl
lemma sum_mul_subst (k n : ℕ) {f : ℕ → ℝ} (h : ∀ l, l ∣ n → ¬ k ∣ l → f l = 0) :
      ∑ l ∈ n.divisors, f l
    = ∑ m ∈ n.divisors, if k*m ∣ n then f (k*m) else 0 := by
  by_cases hn: n = 0
  · simp [hn]
  by_cases hkn : k ∣ n
  swap
  · rw [sum_eq_zero, sum_eq_zero]
    · rintro m _
      rw [if_neg]
      rintro h
      apply hkn
      exact (Nat.dvd_mul_right k m).trans h
    · intro l hl; apply h l (dvd_of_mem_divisors hl)
      apply fun hkl => hkn <| hkl.trans (dvd_of_mem_divisors hl)
  trans (∑ l ∈ n.divisors, ∑ m ∈ n.divisors, if l=k*m then f l else 0)
  · rw [sum_congr rfl]; intro l hl
    by_cases hkl : k ∣ l
    swap
    · rw [h l (dvd_of_mem_divisors hl) hkl, sum_eq_zero];
      intro m _; rw [ite_id]
    rw [sum_eq_single (l/k)]
    · rw[if_pos]; rw [Nat.mul_div_cancel' hkl]
    · intro m _ hmlk
      apply if_neg; revert hmlk; contrapose!; intro hlkm
      rw [hlkm, mul_comm, Nat.mul_div_cancel];
      apply Nat.pos_of_dvd_of_pos hkn (Nat.pos_of_ne_zero hn)
    · contrapose!; intro _
      rw [mem_divisors]
      exact ⟨Trans.trans (Nat.div_dvd_of_dvd hkl) (dvd_of_mem_divisors hl), hn⟩
  · rw [sum_comm, sum_congr rfl]; intro m _
    split_ifs with hdvd
    · rw [sum_ite_eq_of_mem']
      simp only [mem_divisors, hdvd, ne_eq, hn, not_false_eq_true, and_self]
    · apply sum_eq_zero; intro l hl
      apply if_neg;
      rintro rfl
      simp only [mem_divisors, ne_eq] at hl
      exact hdvd hl.1
theorem selbergWeights_eq_dvds_sum (d : ℕ) :
    (BoundingSieve.nu (SelbergSieve.toBoundingSieve s)) d * (SelbergSieve.selbergWeights s) d =
      (SelbergSieve.selbergBoundingSum s)⁻¹ * μ d *
        ∑ l ∈ divisors (BoundingSieve.prodPrimes (SelbergSieve.toBoundingSieve s)), if d ∣ l ∧ l ^ 2 ≤ (SelbergSieve.level s) then (SelbergSieve.selbergTerms (SelbergSieve.toBoundingSieve s)) l else 0 := by
  by_cases h_dvd : d ∣ (BoundingSieve.prodPrimes (SelbergSieve.toBoundingSieve s))
  swap
  · dsimp only [selbergWeights]; rw [if_neg h_dvd]
    rw [sum_eq_zero]
    · ring
    intro l hl; rw [mem_divisors] at hl
    rw [if_neg]; push Not; intro h
    exfalso; exact h_dvd (dvd_trans h hl.left)
  dsimp only [selbergWeights]
  rw [if_pos h_dvd]
  repeat rw [mul_sum]
  apply symm
  rw [sum_mul_subst d (BoundingSieve.prodPrimes (SelbergSieve.toBoundingSieve s))]
  · apply sum_congr rfl
    intro m hm
    rw [mul_ite_zero, ←ite_and, mul_ite_zero, mul_ite_zero]
    apply if_ctx_congr _ _ fun _ => rfl
    · rw [coprime_comm]
      constructor
      · intro h
        push_cast at h
        exact ⟨h.2.2, coprime_of_squarefree_mul
          <| Squarefree.squarefree_of_dvd h.1 s.prodPrimes_squarefree⟩
      · intro h
        push_cast
        exact ⟨ Coprime.mul_dvd_of_dvd_of_dvd h.2 h_dvd (dvd_of_mem_divisors hm),
          Nat.dvd_mul_right d m, h.1⟩
    · intro h
      trans (((BoundingSieve.nu (SelbergSieve.toBoundingSieve s)) d)⁻¹ * ((BoundingSieve.nu (SelbergSieve.toBoundingSieve s)) d) * (SelbergSieve.selbergTerms (SelbergSieve.toBoundingSieve s)) d * μ d / (SelbergSieve.selbergBoundingSum s) * (SelbergSieve.selbergTerms (SelbergSieve.toBoundingSieve s)) m)
      · rw [inv_mul_cancel₀ (nu_ne_zero h_dvd),
          (selbergTerms_mult _).map_mul_of_coprime <| coprime_comm.mp h.2]
        ring
      ring
  · intro l _ hdl
    rw [if_neg, mul_zero]
    push Not; intro h; contradiction
theorem selbergWeights_diagonalisation (l : ℕ) (hl : l ∈ divisors (BoundingSieve.prodPrimes (SelbergSieve.toBoundingSieve s))) :
    (∑ d ∈ divisors (BoundingSieve.prodPrimes (SelbergSieve.toBoundingSieve s)), if l ∣ d then (BoundingSieve.nu (SelbergSieve.toBoundingSieve s)) d * (SelbergSieve.selbergWeights s) d else 0) =
      if l ^ 2 ≤ (SelbergSieve.level s) then (SelbergSieve.selbergTerms (SelbergSieve.toBoundingSieve s)) l * μ l * (SelbergSieve.selbergBoundingSum s)⁻¹ else 0 := by
  calc
    (∑ d ∈ divisors (BoundingSieve.prodPrimes (SelbergSieve.toBoundingSieve s)), if l ∣ d then (BoundingSieve.nu (SelbergSieve.toBoundingSieve s)) d * (SelbergSieve.selbergWeights s) d else 0) =
        ∑ d ∈ divisors (BoundingSieve.prodPrimes (SelbergSieve.toBoundingSieve s)), ∑ k ∈ divisors (BoundingSieve.prodPrimes (SelbergSieve.toBoundingSieve s)),
          if l ∣ d ∧ d ∣ k ∧ k ^ 2 ≤ (SelbergSieve.level s) then (SelbergSieve.selbergTerms (SelbergSieve.toBoundingSieve s)) k * (SelbergSieve.selbergBoundingSum s)⁻¹ * (μ d:ℝ) else 0 := by
      apply sum_congr rfl; intro d _
      rw [selbergWeights_eq_dvds_sum, ← boole_mul, mul_sum, mul_sum]
      apply sum_congr rfl; intro k _
      rw [mul_ite_zero, ite_zero_mul_ite_zero]
      apply if_ctx_congr Iff.rfl _ (fun _ => rfl);
      intro _; ring
    _ = ∑ k ∈ divisors (BoundingSieve.prodPrimes (SelbergSieve.toBoundingSieve s)), if k ^ 2 ≤ (SelbergSieve.level s) then
            (∑ d ∈ divisors (BoundingSieve.prodPrimes (SelbergSieve.toBoundingSieve s)), if l ∣ d ∧ d ∣ k then (μ d:ℝ) else 0) * (SelbergSieve.selbergTerms (SelbergSieve.toBoundingSieve s)) k * (SelbergSieve.selbergBoundingSum s)⁻¹
          else 0 := by
      rw [sum_comm]; apply sum_congr rfl; intro k _
      apply symm
      rw [← boole_mul, sum_mul, sum_mul, mul_sum, sum_congr rfl]
      intro d _
      rw [ite_zero_mul, ite_zero_mul, ite_zero_mul, one_mul, ←ite_and]
      apply if_ctx_congr _ _ (fun _ => rfl)
      · tauto
      intro _; ring
    _ = if l ^ 2 ≤ (SelbergSieve.level s) then (SelbergSieve.selbergTerms (SelbergSieve.toBoundingSieve s)) l * μ l * (SelbergSieve.selbergBoundingSum s)⁻¹ else 0 := by
      rw [← sum_ite_eq_of_mem' (divisors (BoundingSieve.prodPrimes (SelbergSieve.toBoundingSieve s))) l (fun _ => if l^2 ≤ (SelbergSieve.level s) then (SelbergSieve.selbergTerms (SelbergSieve.toBoundingSieve s)) l * μ l * (SelbergSieve.selbergBoundingSum s)⁻¹ else 0) hl]
      apply sum_congr rfl; intro k hk
      rw [Aux.moebius_inv_dvd_lower_bound_real s.prodPrimes_squarefree l _ (dvd_of_mem_divisors hk),
        ←ite_and, ite_zero_mul, ite_zero_mul, ← ite_and]
      apply if_ctx_congr _ _ fun _ => rfl
      · rw [and_comm, eq_comm]; apply and_congr_right
        intro heq; rw [heq]
      · intro h; rw [h.1]; ring
def selbergMuPlus : ℕ → ℝ :=
  lambdaSquared (SelbergSieve.selbergWeights s)
theorem weight_one_of_selberg : (SelbergSieve.selbergWeights s) 1 = 1 := by
  dsimp only [selbergWeights]
  rw [if_pos (one_dvd (BoundingSieve.prodPrimes (SelbergSieve.toBoundingSieve s))), s.nu_mult.left, (selbergTerms_mult _).map_one]
  simp only [inv_one, mul_one, isUnit_one, IsUnit.squarefree, moebius_apply_of_squarefree,
    cardFactors_one, _root_.pow_zero, Int.cast_one, selbergBoundingSum, one_mul,
    coprime_one_right_eq_true, and_true, cast_one]
  rw [inv_mul_cancel₀]
  convert! s.selbergBoundingSum_ne_zero
theorem selbergμPlus_eq_zero (d : ℕ) (hd : ¬d ≤ (SelbergSieve.level s)) : (SelbergSieve.selbergMuPlus s) d = 0 := by
  apply lambdaSquared_eq_zero_of_support _ (SelbergSieve.level s) _ d hd
  apply s.selbergWeights_eq_zero
def selbergUbSieve : UpperBoundSieve :=
  ⟨(SelbergSieve.selbergMuPlus s), upperMoebius_of_lambda_sq (SelbergSieve.selbergWeights s) (s.weight_one_of_selberg)⟩
theorem mainSum_eq_diag_quad_form :
    mainSum (s := s.toBoundingSieve) (SelbergSieve.selbergMuPlus s) =
      ∑ l ∈ divisors (BoundingSieve.prodPrimes (SelbergSieve.toBoundingSieve s)),
        1 / (SelbergSieve.selbergTerms (SelbergSieve.toBoundingSieve s)) l *
          (∑ d ∈ divisors (BoundingSieve.prodPrimes (SelbergSieve.toBoundingSieve s)), if l ∣ d then (BoundingSieve.nu (SelbergSieve.toBoundingSieve s)) d * (SelbergSieve.selbergWeights s) d else 0) ^ 2 :=
  by apply lambdaSquared_mainSum_eq_diag_quad_form
theorem selberg_bound_simple_mainSum :
    mainSum (s := s.toBoundingSieve) (SelbergSieve.selbergMuPlus s) = (SelbergSieve.selbergBoundingSum s)⁻¹ := by
  rw [mainSum_eq_diag_quad_form]
  trans (∑ l ∈ divisors (BoundingSieve.prodPrimes (SelbergSieve.toBoundingSieve s)), (if l ^ 2 ≤ (SelbergSieve.level s) then (SelbergSieve.selbergTerms (SelbergSieve.toBoundingSieve s)) l * ((SelbergSieve.selbergBoundingSum s)⁻¹) ^ 2 else 0))
  · apply sum_congr rfl; intro l hl
    rw [s.selbergWeights_diagonalisation l hl, ite_pow, zero_pow two_ne_zero, mul_ite_zero]
    apply if_congr Iff.rfl _ rfl
    trans (1/(SelbergSieve.selbergTerms (SelbergSieve.toBoundingSieve s)) l * (SelbergSieve.selbergTerms (SelbergSieve.toBoundingSieve s)) l * (SelbergSieve.selbergTerms (SelbergSieve.toBoundingSieve s)) l * (μ l:ℝ)^2  * ((SelbergSieve.selbergBoundingSum s)⁻¹) ^ 2)
    · ring
    norm_cast; rw [moebius_sq_eq_one_of_squarefree <| squarefree_of_mem_divisors_prodPrimes hl]
    rw [one_div_mul_cancel <| _root_.ne_of_gt <| selbergTerms_pos _ l <| dvd_of_mem_divisors hl]
    ring
  conv => {lhs; congr; {skip}; {ext i; rw [← ite_zero_mul]}}
  dsimp only [selbergBoundingSum]
  rw [←sum_mul, sq, ←mul_assoc, mul_inv_cancel₀]
  · ring
  · apply _root_.ne_of_gt; apply selbergBoundingSum_pos
lemma eq_gcd_mul_of_dvd_of_coprime {k d m : ℕ} (hkd : k ∣ d) (hmd : Coprime m d) (hk : k ≠ 0) :
    k = d.gcd (k*m) := by
  obtain ⟨r, hr⟩ := hkd
  have hrdvd : r ∣ d := by use k; rw [mul_comm]; exact hr
  apply symm; rw [hr, Nat.gcd_mul_left, mul_eq_left₀ hk, Nat.gcd_comm]
  apply Coprime.coprime_dvd_right hrdvd hmd
private lemma _helper {k m d : ℕ} (hkd : k ∣ d) (hk : k ∈ divisors (BoundingSieve.prodPrimes (SelbergSieve.toBoundingSieve s))) (hm : m ∈ divisors (BoundingSieve.prodPrimes (SelbergSieve.toBoundingSieve s))) :
    k * m ∣ (BoundingSieve.prodPrimes (SelbergSieve.toBoundingSieve s)) ∧ k = Nat.gcd d (k * m) ∧ (k * m) ^ 2 ≤ (SelbergSieve.level s) ↔
    (k * m) ^ 2 ≤ (SelbergSieve.level s) ∧ Coprime m d := by
  constructor
  · intro h
    constructor
    · exact h.2.2
    · obtain ⟨r, hr⟩ := hkd
      rw [hr, Nat.gcd_mul_left, eq_comm, mul_eq_left₀ (by rintro rfl; simp at hk ⊢)] at h
      rw [hr, coprime_comm]; apply Coprime.mul_left
      · apply coprime_of_squarefree_mul <| Squarefree.squarefree_of_dvd h.1 s.prodPrimes_squarefree
      · exact h.2.1
  · intro h
    constructor
    · apply Nat.Coprime.mul_dvd_of_dvd_of_dvd
      · rw [coprime_comm]; exact Coprime.coprime_dvd_right hkd h.2
      · exact dvd_of_mem_divisors hk
      · exact dvd_of_mem_divisors hm
    constructor
    · exact eq_gcd_mul_of_dvd_of_coprime hkd h.2 (by rintro rfl; simp at hk ⊢)
    · exact h.1
theorem selbergBoundingSum_ge {d : ℕ} (hdP : d ∣ (BoundingSieve.prodPrimes (SelbergSieve.toBoundingSieve s))) :
    (SelbergSieve.selbergBoundingSum s) ≥ (SelbergSieve.selbergWeights s) d * ↑(μ d) * (SelbergSieve.selbergBoundingSum s) := by
  calc
  _ = (∑ k ∈ divisors (BoundingSieve.prodPrimes (SelbergSieve.toBoundingSieve s)), ∑ l ∈ divisors (BoundingSieve.prodPrimes (SelbergSieve.toBoundingSieve s)), if k = d.gcd l ∧ l ^ 2 ≤ (SelbergSieve.level s) then (SelbergSieve.selbergTerms (SelbergSieve.toBoundingSieve s)) l else 0) := by
    dsimp only [selbergBoundingSum]
    rw [sum_comm, sum_congr rfl]; intro l _
    simp_rw [ite_and]
    rw [sum_ite_eq_of_mem']
    · rw [mem_divisors]
      exact ⟨(Nat.gcd_dvd_left d l).trans (hdP), prodPrimes_ne_zero⟩
  _ = (∑ k ∈ divisors (BoundingSieve.prodPrimes (SelbergSieve.toBoundingSieve s)),
          if k ∣ d then
            (SelbergSieve.selbergTerms (SelbergSieve.toBoundingSieve s)) k * ∑ m ∈ divisors (BoundingSieve.prodPrimes (SelbergSieve.toBoundingSieve s)), if (k * m) ^ 2 ≤ (SelbergSieve.level s) ∧ m.Coprime d then (SelbergSieve.selbergTerms (SelbergSieve.toBoundingSieve s)) m else 0
          else 0) := by
    apply sum_congr rfl; intro k hk
    rw [mul_sum]
    split_ifs with hkd
    swap
    · rw [sum_eq_zero]; intro l _
      rw [if_neg]
      push Not; intro h; exfalso
      rw [h] at hkd
      exact hkd <| Nat.gcd_dvd_left d l
    rw [sum_mul_subst k (BoundingSieve.prodPrimes (SelbergSieve.toBoundingSieve s)), sum_congr rfl]
    · intro m hm
      rw [mul_ite_zero, ← ite_and]
      apply if_ctx_congr _ _ fun _ => rfl
      · exact_mod_cast s._helper hkd hk hm
      · intro h
        apply (selbergTerms_mult _).map_mul_of_coprime
        rw [gcd_comm]; apply h.2.coprime_dvd_right hkd
    · intro l _ hkl; apply if_neg
      push Not; intro h; exfalso
      rw [h] at hkl; exact hkl (Nat.gcd_dvd_right d l)
  _ ≥ (∑ k ∈ divisors (BoundingSieve.prodPrimes (SelbergSieve.toBoundingSieve s)), if k ∣ d
          then (SelbergSieve.selbergTerms (SelbergSieve.toBoundingSieve s)) k * ∑ m ∈ divisors (BoundingSieve.prodPrimes (SelbergSieve.toBoundingSieve s)), if (d * m) ^ 2 ≤ (SelbergSieve.level s) ∧ m.Coprime d then (SelbergSieve.selbergTerms (SelbergSieve.toBoundingSieve s)) m else 0
          else 0 ) := by
    apply sum_le_sum; intro k _
    split_ifs with hkd
    swap
    · rfl
    apply mul_le_mul le_rfl _ _ (le_of_lt <| selbergTerms_pos _ k <| hkd.trans hdP)
    · apply sum_le_sum; intro m hm
      split_ifs with h h' h'
      · rfl
      · exfalso; apply h'
        refine ⟨?_, h.2⟩
        · trans ((d*m)^2:ℝ)
          · norm_cast; gcongr
            refine Nat.le_of_dvd ?_ hkd
            apply Nat.pos_of_ne_zero; apply ne_zero_of_dvd_ne_zero prodPrimes_ne_zero hdP
          exact h.1
      · refine le_of_lt <| selbergTerms_pos _ m <| dvd_of_mem_divisors hm
      · rfl
    apply sum_nonneg; intro m hm
    split_ifs
    · apply le_of_lt <| selbergTerms_pos _ m <| dvd_of_mem_divisors hm
    · rfl
  _ = _ := by
    conv => enter [1, 2, k]; rw [← ite_zero_mul]
    rw [←sum_mul, conv_selbergTerms_eq_selbergTerms_mul_nu _ hdP]
    trans ((SelbergSieve.selbergBoundingSum s) * (SelbergSieve.selbergBoundingSum s)⁻¹ * (μ d:ℝ)^2 * ((BoundingSieve.nu (SelbergSieve.toBoundingSieve s)) d)⁻¹ * (SelbergSieve.selbergTerms (SelbergSieve.toBoundingSieve s)) d * (∑ m ∈ divisors (BoundingSieve.prodPrimes (SelbergSieve.toBoundingSieve s)), if (d*m) ^ 2 ≤ (SelbergSieve.level s) ∧
      Coprime m d then (SelbergSieve.selbergTerms (SelbergSieve.toBoundingSieve s)) m else 0))
    · rw [mul_inv_cancel₀, ←Int.cast_pow, moebius_sq_eq_one_of_squarefree]
      · ring
      · exact Squarefree.squarefree_of_dvd hdP s.prodPrimes_squarefree
      · exact _root_.ne_of_gt <| s.selbergBoundingSum_pos
    dsimp only [selbergWeights]; rw [if_pos hdP]
    ring
theorem selberg_bound_weights (d : ℕ) : |(SelbergSieve.selbergWeights s) d| ≤ 1 := by
  by_cases hdP : d ∣ (BoundingSieve.prodPrimes (SelbergSieve.toBoundingSieve s))
  swap
  · rw [s.selbergWeights_eq_zero_of_not_dvd hdP]; simp only [zero_le_one, abs_zero]
  have : 1*(SelbergSieve.selbergBoundingSum s) ≥ (SelbergSieve.selbergWeights s) d * ↑(μ d) * (SelbergSieve.selbergBoundingSum s) := by
    rw[one_mul]
    exact s.selbergBoundingSum_ge hdP
  replace this : (SelbergSieve.selbergWeights s) d * μ d ≤ 1 := by
    apply le_of_mul_le_mul_of_pos_right this (s.selbergBoundingSum_pos)
  convert this using 1
  rw [← abs_of_nonneg <| s.selbergWeights_mul_mu_nonneg d hdP,
    abs_mul, ←Int.cast_abs, abs_moebius_eq_one_of_squarefree <|
    (s.prodPrimes_squarefree.squarefree_of_dvd hdP), Int.cast_one, mul_one]
theorem selberg_bound_muPlus (n : ℕ) (hn : n ∈ divisors (BoundingSieve.prodPrimes (SelbergSieve.toBoundingSieve s))) :
    |(SelbergSieve.selbergMuPlus s) n| ≤ (3:ℝ) ^ ω n := by
  let f : ℕ → ℕ → ℝ := fun x z : ℕ => if n = x.lcm z then 1 else 0
  dsimp only [selbergMuPlus, lambdaSquared]
  calc
    |∑ d1 ∈ n.divisors, ∑ d2 ∈ n.divisors, if n = d1.lcm d2 then (SelbergSieve.selbergWeights s) d1 * (SelbergSieve.selbergWeights s) d2 else 0| ≤
        ∑ d1 ∈ n.divisors, |∑ d2 ∈ n.divisors, if n = d1.lcm d2 then (SelbergSieve.selbergWeights s) d1 * (SelbergSieve.selbergWeights s) d2 else 0| := ?_
    _ ≤ ∑ d1 ∈ n.divisors, ∑ d2 ∈ n.divisors, |if n = d1.lcm d2 then (SelbergSieve.selbergWeights s) d1 * (SelbergSieve.selbergWeights s) d2 else 0| := ?_
    _ ≤ ∑ d1 ∈ n.divisors, ∑ d2 ∈ n.divisors, f d1 d2 := ?_
    _ = (n.divisors ×ˢ n.divisors).sum fun p => f p.fst p.snd := ?_
    _ = Finset.card ((n.divisors ×ˢ n.divisors).filter fun p : ℕ × ℕ => n = p.fst.lcm p.snd) := ?_
    _ = (3:ℕ) ^ ω n := ?_
    _ = (3:ℝ) ^ ω n := ?_
  · apply abs_sum_le_sum_abs
  · gcongr; apply abs_sum_le_sum_abs
  · gcongr with d1 _ d2
    rw [apply_ite abs, abs_zero, abs_mul]
    simp only [f]
    by_cases h : n = d1.lcm d2
    · rw [if_pos h, if_pos h]
      exact (mul_le_of_le_one_left (abs_nonneg <| (SelbergSieve.selbergWeights s) d2) (s.selberg_bound_weights d1)).trans
        (s.selberg_bound_weights d2)
    rw [if_neg h, if_neg h]
  · rw [← Finset.sum_product']
  · rw [← sum_filter, Finset.sum_const, smul_one_eq_cast]
  · norm_cast
    simp [← card_pair_lcm_eq (squarefree_of_mem_divisors_prodPrimes hn), eq_comm]
  norm_num
theorem selberg_bound_simple_errSum :
    errSum (s := s.toBoundingSieve) (SelbergSieve.selbergMuPlus s) ≤
      ∑ d ∈ divisors (BoundingSieve.prodPrimes (SelbergSieve.toBoundingSieve s)), if (d : ℝ) ≤ (SelbergSieve.level s) then (3:ℝ) ^ ω d * |(BoundingSieve.rem (s := (SelbergSieve.toBoundingSieve s))) d| else 0 := by
  dsimp only [errSum]
  gcongr with d hd
  split_ifs with h
  · apply mul_le_mul _ le_rfl (abs_nonneg <| (BoundingSieve.rem (s := (SelbergSieve.toBoundingSieve s))) d) (pow_nonneg _ <| ω d)
    · apply s.selberg_bound_muPlus d hd
    · norm_num
  · rw [s.selbergμPlus_eq_zero d h, abs_zero, zero_mul]
theorem selberg_bound_simple :
    siftedSum (s := s.toBoundingSieve) ≤
      (BoundingSieve.totalMass (SelbergSieve.toBoundingSieve s)) / (SelbergSieve.selbergBoundingSum s) +
        ∑ d ∈ divisors (BoundingSieve.prodPrimes (SelbergSieve.toBoundingSieve s)), if (d : ℝ) ≤ (SelbergSieve.level s) then (3:ℝ) ^ ω d * |(BoundingSieve.rem (s := (SelbergSieve.toBoundingSieve s))) d| else 0 := by
  let μPlus := s.selbergUbSieve
  calc
    siftedSum ≤ (BoundingSieve.totalMass (SelbergSieve.toBoundingSieve s)) * mainSum μPlus + errSum μPlus :=
      siftedSum_le_mainSum_errSum_of_UpperBoundSieve _ μPlus
    _ ≤ _ := ?_
  gcongr
  · erw [s.selberg_bound_simple_mainSum, div_eq_mul_inv]
  · apply s.selberg_bound_simple_errSum
end SelbergSieve
end
end

section
open scoped Nat ArithmeticFunction BigOperators Classical ArithmeticFunction.zeta
  ArithmeticFunction.omega
open BoundingSieve SelbergSieve
noncomputable section
namespace Sieve
lemma prodDistinctPrimes_squarefree (s : Finset ℕ) (h : ∀ p ∈ s, p.Prime) :
    Squarefree (∏ p ∈ s, p) := by
  refine Iff.mpr Nat.squarefree_iff_prime_squarefree ?_
  intro p hp; by_contra h_dvd
  by_cases hps : p ∈ s
  · rw [←Finset.mul_prod_erase (a:=p) (h := hps), mul_dvd_mul_iff_left (Nat.Prime.ne_zero hp)]
      at h_dvd
    obtain ⟨q, hq⟩ := hp.prime.exists_mem_finset_dvd h_dvd
    rw [Finset.mem_erase] at hq
    exact hq.1.1 <| symm <| (Nat.prime_dvd_prime_iff_eq hp (h q hq.1.2)).mp hq.2
  · have : p ∣ ∏ p ∈ s, p := Trans.trans (dvd_mul_right p p) h_dvd
    obtain ⟨q, hq⟩ := hp.prime.exists_mem_finset_dvd this
    have heq : p = q := by
      rw [←Nat.prime_dvd_prime_iff_eq hp (h q hq.1)]
      exact hq.2
    rw [heq] at hps; exact hps hq.1
def CompletelyMultiplicative (f : ArithmeticFunction ℝ) : Prop :=
  f 1 = 1 ∧ ∀ a b, f (a*b) = f a * f b
namespace CompletelyMultiplicative
open ArithmeticFunction
theorem zeta : CompletelyMultiplicative ζ := by
  unfold CompletelyMultiplicative
  simp_rw [ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply, one_ne_zero, ite_false,
    mul_eq_zero, Nat.cast_ite, Nat.cast_one, CharP.cast_eq_zero, mul_ite, mul_zero, mul_one,
    true_and, ← ite_or, or_comm, implies_true]
theorem id : CompletelyMultiplicative ArithmeticFunction.id := by
    constructor <;> simp
theorem pmul (f g : ArithmeticFunction ℝ) (hf : CompletelyMultiplicative f)
    (hg : CompletelyMultiplicative g) :
    CompletelyMultiplicative (ArithmeticFunction.pmul f g) := by
  constructor
  · rw [pmul_apply, hf.1, hg.1, mul_one]
  intro a b
  simp_rw [pmul_apply, hf.2, hg.2]; ring
theorem pdiv {f g : ArithmeticFunction ℝ} (hf : CompletelyMultiplicative f)
    (hg : CompletelyMultiplicative g) :
    CompletelyMultiplicative (ArithmeticFunction.pdiv f g) := by
  constructor
  · rw [pdiv_apply, hf.1, hg.1, div_one]
  intro a b
  simp_rw [pdiv_apply, hf.2, hg.2]; ring
theorem isMultiplicative {f : ArithmeticFunction ℝ} (hf : CompletelyMultiplicative f) :
    ArithmeticFunction.IsMultiplicative f :=
  ⟨hf.1, fun _ => hf.2 _ _⟩
theorem apply_pow (f : ArithmeticFunction ℝ) (hf : CompletelyMultiplicative f) (a n : ℕ) :
    f (a^n) = f a ^ n := by
  induction n with
  | zero => simp_rw [pow_zero, hf.1]
  | succ n' ih => simp_rw [pow_succ, hf.2, ih]
end CompletelyMultiplicative
theorem prod_factors_one_div_compMult_ge (M : ℕ) (f : ArithmeticFunction ℝ)
    (hf : CompletelyMultiplicative f) (hf_nonneg : ∀ n, 0 ≤ f n) (d : ℕ) (hd : Squarefree d)
    (hf_size : ∀ n, n.Prime → n ∣ d → f n < 1) :
    f d * ∏ p ∈ d.primeFactors, 1 / (1 - f p)
    ≥ ∏ p ∈ d.primeFactors, ∑ n ∈ Finset.Icc 1 M, f (p^n) := by
  calc f d * ∏ p ∈ d.primeFactors, 1 / (1 - f p)
    = ∏ p ∈ d.primeFactors, f p / (1 - f p)                 := by
        conv => { lhs; congr; rw [←Nat.prod_primeFactors_of_squarefree hd] }
        rw [hf.isMultiplicative.map_prod_of_subset_primeFactors _ _ subset_rfl,
          ←Finset.prod_mul_distrib]
        simp_rw[one_div, div_eq_mul_inv]
  _ ≥ ∏ p ∈ d.primeFactors, ∑ n ∈ Finset.Icc 1 M, (f p)^n  := by
    gcongr with p hp
    · exact fun p _ => Finset.sum_nonneg fun n _ => pow_nonneg (hf_nonneg p) n
    rw [Nat.mem_primeFactors_of_ne_zero hd.ne_zero] at hp
    rw [← Finset.Ico_add_one_right_eq_Icc, geom_sum_Ico,
      ← mul_div_mul_left (c := (-1 : ℝ)) (f p ^ (M + 1) - f p ^ 1)]
    · gcongr
      · apply hf_nonneg
      · linarith [hf_size p hp.1 hp.2]
      · rw [pow_one]
        have : 0 ≤ f p ^ (M + 1) := by
          apply pow_nonneg
          apply hf_nonneg
        linarith only [this]
      · linarith only
    · norm_num
    · apply ne_of_lt <| hf_size p hp.1 hp.2
    · apply Nat.succ_le_iff.mpr (Nat.succ_pos _)
  _ = ∏ p ∈ d.primeFactors, ∑ n ∈ Finset.Icc 1 M, f (p^n)  := by
     simp_rw [hf.apply_pow]
theorem prod_factors_sum_pow_compMult (M : ℕ) (hM : M ≠ 0) (f : ArithmeticFunction ℝ)
    (hf : CompletelyMultiplicative f) (d : ℕ) (hd : Squarefree d) :
    ∏ p ∈ d.primeFactors, ∑ n ∈ Finset.Icc 1 M, f (p^n)
    = ∑ m ∈ (d^M).divisors.filter (d ∣ ·), f m := by
  rw [Finset.prod_sum]
  let i : (a:_) → (ha : a ∈ Finset.pi d.primeFactors fun p => Finset.Icc 1 M) → ℕ :=
    fun a _ => ∏ p ∈ d.primeFactors.attach, p.1 ^ (a p p.2)
  have hfact_i : ∀ a ha,
      ∀ p , Nat.factorization (i a ha) p = if hp : p ∈ d.primeFactors then a p hp else 0 := by
    intro a ha p
    by_cases hp : p ∈ d.primeFactors
    · rw [dif_pos hp, Nat.factorization_prod, Finset.sum_apply',
        Finset.sum_eq_single ⟨p, hp⟩, Nat.factorization_pow, Finsupp.smul_apply,
        Nat.Prime.factorization_self (Nat.prime_of_mem_primeFactorsList <| List.mem_toFinset.mp hp)]
      · ring
      · intro q _ hq
        rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_zero]; right
        apply Nat.factorization_eq_zero_of_not_dvd
        rw [Nat.Prime.dvd_iff_eq, ← exists_eq_subtype_mk_iff]
        · push Not
          exact fun _ => hq
        · exact Nat.prime_of_mem_primeFactorsList <| List.mem_toFinset.mp q.2
        · exact (Nat.prime_of_mem_primeFactorsList <| List.mem_toFinset.mp hp).ne_one
      · intro h
        exfalso
        exact h (Finset.mem_attach _ _)
      · exact fun q _ => pow_ne_zero _ (ne_of_gt (Nat.pos_of_mem_primeFactorsList
          (List.mem_toFinset.mp q.2)))
    · rw [dif_neg hp]
      by_cases hpp : p.Prime
      swap
      · apply Nat.factorization_eq_zero_of_not_prime _ hpp
      apply Nat.factorization_eq_zero_of_not_dvd
      intro hp_dvd
      obtain ⟨⟨q, hq⟩, _, hp_dvd_pow⟩ := Prime.exists_mem_finset_dvd hpp.prime hp_dvd
      apply hp
      rw [Nat.mem_primeFactors]
      constructor
      · exact hpp
      refine ⟨?_, hd.ne_zero⟩
      trans q
      · apply Nat.Prime.dvd_of_dvd_pow hpp hp_dvd_pow
      · apply Nat.dvd_of_mem_primeFactorsList <| List.mem_toFinset.mp hq
  have hi_ne_zero : ∀ (a : _) (ha : a ∈ Finset.pi d.primeFactors fun _p => Finset.Icc 1 M),
      i a ha ≠ 0 := by
    intro a ha
    erw [Finset.prod_ne_zero_iff]
    exact fun p _ => pow_ne_zero _ (ne_of_gt (Nat.pos_of_mem_primeFactorsList
      (List.mem_toFinset.mp p.property)))
  have hi : ∀ (a : _) (ha : a ∈ Finset.pi d.primeFactors fun _p => Finset.Icc 1 M),
      i a ha ∈ (d^M).divisors.filter (d ∣ ·) := by
    intro a ha
    rw [Finset.mem_filter, Nat.mem_divisors, ←Nat.factorization_le_iff_dvd hd.ne_zero
      (hi_ne_zero a ha),← Nat.factorization_le_iff_dvd (hi_ne_zero a ha) (pow_ne_zero _ hd.ne_zero)]
    constructor; constructor
    · rw [Finsupp.le_iff]; intro p _
      rw [hfact_i a ha]
      by_cases hp : p ∈ d.primeFactors
      · rw [dif_pos hp]
        rw [Nat.factorization_pow, Finsupp.smul_apply]
        simp_rw [Finset.mem_pi, Finset.mem_Icc] at ha
        trans (M • 1)
        · norm_num
          exact (ha p hp).2
        · gcongr
          rw [Nat.mem_primeFactors_of_ne_zero hd.ne_zero] at hp
          rw [←Nat.Prime.dvd_iff_one_le_factorization hp.1 hd.ne_zero]
          exact hp.2
      · rw [dif_neg hp]; norm_num
    · apply pow_ne_zero _ hd.ne_zero
    · rw [Finsupp.le_iff]; intro p hp
      rw [Nat.support_factorization] at hp
      rw [hfact_i a ha]
      rw [dif_pos hp]
      trans 1
      · exact hd.natFactorization_le_one p
      simp_rw [Finset.mem_pi, Finset.mem_Icc] at ha
      exact (ha p hp).1
  have h : ∀ (a : _) (ha : a ∈ Finset.pi d.primeFactors fun _p => Finset.Icc 1 M),
      ∏ p ∈ d.primeFactors.attach, f (p.1 ^ (a p p.2)) = f (i a ha) := by
    intro a ha
    apply symm
    apply hf.isMultiplicative.map_prod
    intro x _ y _ hxy
    simp_rw [Finset.mem_pi, Finset.mem_Icc, Nat.succ_le_iff] at ha
    apply (Nat.coprime_pow_left_iff (ha x x.2).1 ..).mpr
    apply (Nat.coprime_pow_right_iff (ha y y.2).1 ..).mpr
    have hxp := Nat.prime_of_mem_primeFactorsList (List.mem_toFinset.mp x.2)
    rw [Nat.Prime.coprime_iff_not_dvd hxp]
    rw [Nat.prime_dvd_prime_iff_eq hxp <| Nat.prime_of_mem_primeFactorsList
      (List.mem_toFinset.mp y.2)]
    exact fun hc => hxy (Subtype.ext hc)
  have i_inj : ∀ a ha b hb, i a ha = i b hb → a = b := by
    intro a ha b hb hiab
    apply_fun Nat.factorization at hiab
    ext p hp
    obtain hiabp := DFunLike.ext_iff.mp hiab p
    rw [hfact_i a ha, hfact_i b hb, dif_pos hp, dif_pos hp] at hiabp
    exact hiabp
  have i_surj : ∀ (b : ℕ), b ∈ (d^M).divisors.filter (d ∣ ·) → ∃ a ha, i a ha = b := by
    intro b hb
    have h : (fun p _ => b.factorization p) ∈ Finset.pi d.primeFactors fun p => Finset.Icc 1 M := by
      rw [Finset.mem_pi]; intro p hp
      rw [Finset.mem_Icc]
      rw [Finset.mem_filter] at hb
      have hb_ne_zero : b ≠ 0 := ne_of_gt <| Nat.pos_of_mem_divisors hb.1
      have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
      constructor
      · rw [←Nat.Prime.dvd_iff_one_le_factorization hpp hb_ne_zero]
        · exact Trans.trans (Nat.dvd_of_mem_primeFactors hp) hb.2
      · rw [Nat.mem_divisors] at hb
        trans Nat.factorization (d^M) p
        · exact (Nat.factorization_le_iff_dvd hb_ne_zero hb.left.right).mpr hb.left.left p
        rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
        have : d.factorization p ≤ 1 := by
          apply hd.natFactorization_le_one
        exact (mul_le_iff_le_one_right (Nat.pos_of_ne_zero hM)).mpr this
    use (fun p _ => Nat.factorization b p)
    use h
    apply Nat.eq_of_factorization_eq
    · apply hi_ne_zero _ h
    · exact ne_of_gt <| Nat.pos_of_mem_divisors (Finset.mem_filter.mp hb).1
    intro p
    rw [hfact_i (fun p _ => (Nat.factorization b) p) h p]
    rw [Finset.mem_filter, Nat.mem_divisors] at hb
    by_cases hp : p ∈ d.primeFactors
    · rw [dif_pos hp]
    · rw [dif_neg hp, eq_comm, Nat.factorization_eq_zero_iff, ←or_assoc]
      rw [Nat.mem_primeFactors] at hp
      left
      push Not at hp
      by_cases hpp : p.Prime
      · right; intro h
        apply absurd (hp hpp)
        push Not
        exact ⟨hpp.dvd_of_dvd_pow (h.trans hb.1.1), hd.ne_zero⟩
      · left; exact hpp
  exact Finset.sum_bij i hi i_inj i_surj h
theorem prod_primes_dvd_of_dvd (P : ℕ) {s : Finset ℕ} (h : ∀ p ∈ s, p ∣ P) (h' : ∀ p ∈ s, p.Prime) :
    ∏ p ∈ s, p ∣ P := by
  simp_rw [Nat.prime_iff] at h'
  apply Finset.prod_primes_dvd _ h' h
lemma sqrt_le_self (x : ℝ) (hx : 1 ≤ x) : Real.sqrt x ≤ x := by
  refine Iff.mpr Real.sqrt_le_iff ?_
  constructor
  · linarith
  refine le_self_pow₀ hx ?right.h
  norm_num
lemma Nat.squarefree_dvd_pow (a b N : ℕ) (ha : Squarefree a) (hab : a ∣ b ^ N) : a ∣ b := by
  by_cases hN : N=0
  · rw [hN, pow_zero, Nat.dvd_one] at hab
    rw [hab]; simp
  rw [Squarefree.dvd_pow_iff_dvd ha hN] at hab
  exact hab
open ArithmeticFunction
theorem selbergBoundingSum_ge_sum_div_coprime (s : SelbergSieve) (q : ℕ)
    (hP : ∀ p : ℕ, p.Prime → (p:ℝ) ≤ s.level → ¬ p ∣ q → p ∣ s.prodPrimes)
    (hnu : CompletelyMultiplicative s.nu) (hnu_nonneg : ∀ n, 0 ≤ s.nu n)
    (hnu_lt : ∀ p, p.Prime → p ∣ s.prodPrimes → s.nu p < 1) :
    s.selbergBoundingSum ≥ ∑ m ∈ (Finset.Icc 1 (Nat.floor <| Real.sqrt s.level)).filter
      (fun m => m.Coprime q), s.nu m := by
  unfold selbergBoundingSum
  calc ∑ l ∈ s.prodPrimes.divisors, (if l ^ 2 ≤ s.level then selbergTerms _ l else 0)
     ≥ ∑ l ∈ s.prodPrimes.divisors.filter (fun (l:ℕ) => l^2 ≤ s.level),
        ∑ m ∈ (l^(Nat.floor s.level)).divisors.filter (l ∣ ·), s.nu m         := ?_
   _ ≥ ∑ m ∈ (Finset.Icc 1 (Nat.floor <| Real.sqrt s.level)).filter
          (fun m => m.Coprime q), s.nu m := ?_
  · rw [←Finset.sum_filter]; apply Finset.sum_le_sum; intro l hl
    rw [Finset.mem_filter, Nat.mem_divisors] at hl
    have hlsq : Squarefree l := Squarefree.squarefree_of_dvd hl.1.1 s.prodPrimes_squarefree
    trans (∏ p ∈ l.primeFactors, ∑ n ∈ Finset.Icc 1 (Nat.floor s.level), s.nu (p^n))
    · rw [prod_factors_sum_pow_compMult (Nat.floor s.level) _ s.nu]
      · exact hnu
      · exact hlsq
      · rw [ne_eq, Nat.floor_eq_zero, not_lt]
        exact s.one_le_level
    rw [selbergTerms_apply _ l]
    apply prod_factors_one_div_compMult_ge _ _ hnu _ _ hlsq
    · intro p hpp hpl
      apply hnu_lt p hpp (Trans.trans hpl hl.1.1)
    · exact hnu_nonneg
  rw [←Finset.sum_biUnion]
  · apply Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => hnu_nonneg _)
    intro m hm'
    rw [Finset.mem_filter] at hm'
    obtain ⟨hm, hmq⟩ := hm'
    have hprod_pos : 0 < (∏ p ∈ m.primeFactors, p) := by
      apply Finset.prod_pos;
      intro p hp; exact Nat.pos_of_mem_primeFactorsList <| List.mem_toFinset.mp hp
    have hprod_ne_zero :  (∏ p ∈ m.primeFactors, p) ^ ⌊s.level⌋₊ ≠ 0 := by
      apply pow_ne_zero; apply ne_of_gt; apply hprod_pos
    rw [Finset.mem_biUnion]; simp_rw [Finset.mem_filter, Nat.mem_divisors]
    rw [Finset.mem_Icc, Nat.le_floor_iff] at hm
    · have hm_ne_zero : m ≠ 0 := by
        exact ne_of_gt <| Nat.succ_le_iff.mp hm.1
      use ∏ p ∈ m.primeFactors, p
      constructor; constructor; constructor
      · apply prod_primes_dvd_of_dvd <;> intro p hp
        · refine hP p (Nat.prime_of_mem_primeFactors hp) ?_ ?_
          · trans (m:ℝ)
            · exact_mod_cast Nat.le_of_mem_primeFactors hp
            trans (Real.sqrt s.level)
            · exact hm.2
            apply sqrt_le_self s.level s.one_le_level
          · intro hpq
            have hcop : p.Coprime q := hmq.coprime_dvd_left (Nat.dvd_of_mem_primeFactors hp)
            exact (Nat.prime_of_mem_primeFactors hp).one_lt.ne' (hcop.eq_one_of_dvd hpq)
        exact Nat.prime_of_mem_primeFactors hp
      · exact prodPrimes_ne_zero
      · rw [←Real.sqrt_le_sqrt_iff (by linarith only [s.one_le_level]), Real.sqrt_sq]
        · trans (m:ℝ)
          · norm_cast; apply Nat.le_of_dvd (Nat.succ_le_iff.mp hm.1)
            exact Nat.prod_primeFactors_dvd m
          exact hm.2
        apply le_of_lt; norm_cast
      constructor; constructor
      · rw [←Nat.factorization_le_iff_dvd _ hprod_ne_zero, Nat.factorization_pow]
        · intro p
          have hy_mul_prod_nonneg :
              0 ≤ ⌊s.level⌋₊ * (Nat.factorization (∏ p ∈ m.primeFactors, p)) p := by
            apply mul_nonneg
            · apply Nat.le_floor; norm_cast; linarith only [s.one_le_level]
            · norm_num
          trans (Nat.factorization m) p * 1
          · rw [mul_one]
          rw [Finsupp.smul_apply, smul_eq_mul]
          by_cases hpp : p.Prime
          swap
          · rw [Nat.factorization_eq_zero_of_not_prime _ hpp, zero_mul]; exact hy_mul_prod_nonneg
          by_cases hpdvd : p ∣ m
          swap
          · rw [Nat.factorization_eq_zero_of_not_dvd hpdvd, zero_mul]; exact hy_mul_prod_nonneg
          apply mul_le_mul
          · trans m
            · apply le_of_lt <| Nat.factorization_lt _ _
              apply hm_ne_zero
            apply Nat.le_floor
            refine le_trans hm.2 ?_
            apply sqrt_le_self _ s.one_le_level
          · rw [←Nat.Prime.pow_dvd_iff_le_factorization hpp <| ne_of_gt hprod_pos, pow_one]
            apply Finset.dvd_prod_of_mem
            rw [Nat.mem_primeFactors]
            exact ⟨hpp, hpdvd, hm_ne_zero⟩
          · norm_num
          · norm_num
        exact hm_ne_zero
      · exact hprod_ne_zero
      · exact Nat.prod_primeFactors_dvd m
    · apply Real.sqrt_nonneg
  · intro i hi j hj hij t hti htj x hx
    simp only [Finset.bot_eq_empty, Finset.notMem_empty]
    specialize hti hx
    specialize htj hx
    simp_rw [Finset.mem_coe, Finset.mem_filter, Nat.mem_divisors] at *
    have h : ∀ i j {n}, i ∣ s.prodPrimes → i ∣ x → x ∣ j ^ n → i ∣ j := by
      intro i j n hiP hix hij
      apply Nat.squarefree_dvd_pow i j n (squarefree_of_dvd_prodPrimes hiP)
      exact Trans.trans hix hij
    have hidvdj : i ∣ j := by
      apply h i j hi.1.1 hti.2 htj.1.1
    have hjdvdi : j ∣ i := by
      apply h j i hj.1.1 htj.2 hti.1.1
    exact hij <| Nat.dvd_antisymm hidvdj hjdvdi
theorem rem_sum_le_of_const_of_dvd (s : SelbergSieve) (C : ℝ)
    (hrem : ∀ d ∈ s.prodPrimes.divisors, |rem (s := s.toBoundingSieve) d| ≤ C) :
    ∑ d ∈ s.prodPrimes.divisors,
        (if (d : ℝ) ≤ s.level then (3:ℝ) ^ ω d * |rem (s := s.toBoundingSieve) d| else 0)
      ≤ C * s.level * (1+Real.log s.level)^3 := by
  rw [←Finset.sum_filter]
  trans (∑ d ∈  Finset.filter (fun d:ℕ => ↑d ≤ s.level) (s.prodPrimes.divisors),  3 ^ ω d * C )
  · gcongr with d hd
    rw [Finset.mem_filter] at hd
    exact hrem d hd.1
  rw [←Finset.sum_mul, mul_comm, mul_assoc]
  gcongr
  · have h1 : 1 ∈ s.prodPrimes.divisors := Nat.one_mem_divisors.mpr prodPrimes_ne_zero
    linarith [abs_nonneg <| rem (s := s.toBoundingSieve) 1, hrem 1 h1]
  rw [Finset.sum_filter]
  apply Aux.sum_pow_cardDistinctFactors_le_self_mul_log_pow (hx := s.one_le_level)
  apply prodPrimes_squarefree
end Sieve
end
end

section
open Finset Sieve SelbergSieve BoundingSieve
open scoped Nat ArithmeticFunction ArithmeticFunction.zeta ArithmeticFunction.omega
noncomputable section
namespace Artin.BrunTitchmarsh
theorem sum_inv_coprime_ge (q N : ℕ) :
    ((q.totient : ℝ) / q) * ∑ m ∈ Icc 1 N, (m : ℝ)⁻¹ ≤
      ∑ m ∈ (Icc 1 N).filter (fun m => m.Coprime q), (m : ℝ)⁻¹ := by
  induction q using Nat.recOnPrimePow generalizing N with
  | zero =>
    simp only [Nat.totient_zero, CharP.cast_eq_zero, zero_div, zero_mul]
    exact sum_nonneg fun _ _ => by positivity
  | one => simp
  | prime_pow_mul a p n hp hpa hn ih =>
    have ha : a ≠ 0 := by rintro rfl; exact hpa (dvd_zero p)
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
    set T := (Icc 1 N).filter (fun m => m.Coprime a) with hT
    have hsplit : ∑ m ∈ T, (m : ℝ)⁻¹ =
        ∑ m ∈ (Icc 1 N).filter (fun m => m.Coprime (p ^ n * a)), (m : ℝ)⁻¹ +
          ∑ m ∈ T.filter (fun m => p ∣ m), (m : ℝ)⁻¹ := by
      rw [← sum_filter_not_add_sum_filter T (fun m => p ∣ m), hT, filter_filter]
      congr 2
      ext m
      simp only [mem_filter, Nat.coprime_mul_iff_right, Nat.coprime_pow_right_iff hn,
        Nat.coprime_comm (m := p), Nat.Prime.coprime_iff_not_dvd hp]
      tauto
    have hmult : ∑ m ∈ T.filter (fun m => p ∣ m), (m : ℝ)⁻¹ ≤ (p : ℝ)⁻¹ * ∑ m ∈ T, (m : ℝ)⁻¹ := by
      have hsub : T.filter (fun m => p ∣ m) ⊆ T.image (fun m => p * m) := by
        intro m hm
        simp only [hT, mem_filter, mem_Icc] at hm
        obtain ⟨⟨⟨h1, hN⟩, hcop⟩, k, rfl⟩ := hm
        refine mem_image.mpr ⟨k, ?_, rfl⟩
        simp only [hT, mem_filter, mem_Icc]
        have hk : 1 ≤ k := by
          rcases Nat.eq_zero_or_pos k with h | h
          · rw [h, mul_zero] at h1; omega
          · exact h
        refine ⟨⟨hk, ?_⟩, hcop.coprime_dvd_left (dvd_mul_left k p)⟩
        nlinarith [hp.two_le]
      calc ∑ m ∈ T.filter (fun m => p ∣ m), (m : ℝ)⁻¹
          ≤ ∑ m ∈ T.image (fun m => p * m), (m : ℝ)⁻¹ :=
            sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
        _ = ∑ m ∈ T, ((p * m : ℕ) : ℝ)⁻¹ := by
            rw [sum_image]
            intro i _ j _ hij
            exact Nat.eq_of_mul_eq_mul_left hp.pos hij
        _ = (p : ℝ)⁻¹ * ∑ m ∈ T, (m : ℝ)⁻¹ := by
            rw [mul_sum]
            refine sum_congr rfl fun m _ => ?_
            push_cast
            rw [mul_inv]
    have htot : ((p ^ n * a).totient : ℝ) / ((p ^ n * a : ℕ) : ℝ) =
        (1 - (p : ℝ)⁻¹) * ((a.totient : ℝ) / a) := by
      have hcop : (p ^ n).Coprime a :=
        Nat.Coprime.pow_left n ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpa)
      rw [Nat.totient_mul hcop, Nat.totient_prime_pow hp hn]
      have hp1 : (((p - 1 : ℕ)) : ℝ) = p - 1 := by
        rw [Nat.cast_sub hp.one_lt.le]; simp
      have ha0 : (a : ℝ) ≠ 0 := by exact_mod_cast ha
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      push_cast
      rw [hp1]
      field_simp
      ring
    have hB := ih N
    have hH : 0 ≤ ∑ m ∈ Icc 1 N, (m : ℝ)⁻¹ := sum_nonneg fun _ _ => by positivity
    have hpinv : (p : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast hp.one_lt.le)
    rw [htot]
    calc (1 - (p : ℝ)⁻¹) * ((a.totient : ℝ) / a) * ∑ m ∈ Icc 1 N, (m : ℝ)⁻¹
        = (1 - (p : ℝ)⁻¹) * (((a.totient : ℝ) / a) * ∑ m ∈ Icc 1 N, (m : ℝ)⁻¹) := by ring
      _ ≤ (1 - (p : ℝ)⁻¹) * ∑ m ∈ T, (m : ℝ)⁻¹ :=
          mul_le_mul_of_nonneg_left hB (by linarith)
      _ ≤ _ := by linarith
def sievePrimes (q : ℕ) (z : ℝ) : Finset ℕ :=
  (range (⌊z⌋₊ + 1)).filter fun p => p.Prime ∧ ¬ p ∣ q
def sieveProd (q : ℕ) (z : ℝ) : ℕ := ∏ p ∈ sievePrimes q z, p
lemma sieveProd_squarefree (q : ℕ) (z : ℝ) : Squarefree (sieveProd q z) :=
  prodDistinctPrimes_squarefree _ fun _ hp => (mem_filter.mp hp).2.1
lemma coprime_sieveProd (q : ℕ) (z : ℝ) : (sieveProd q z).Coprime q :=
  Nat.Coprime.prod_left fun _ hp =>
    (Nat.Prime.coprime_iff_not_dvd (mem_filter.mp hp).2.1).mpr (mem_filter.mp hp).2.2
lemma dvd_sieveProd {q p : ℕ} {z : ℝ} (hp : p.Prime) (hpz : (p : ℝ) ≤ z) (hpq : ¬ p ∣ q) :
    p ∣ sieveProd q z := by
  apply dvd_prod_of_mem
  simp only [sievePrimes, mem_filter, mem_range]
  refine ⟨Nat.lt_succ_of_le (Nat.le_floor hpz), hp, hpq⟩
lemma coprime_sieveProd_of_lt {q p : ℕ} {z : ℝ} (hp : p.Prime) (hpz : ⌊z⌋₊ < p) :
    (sieveProd q z).Coprime p :=
  Nat.Coprime.prod_left fun r hr => by
    simp only [sievePrimes, mem_filter, mem_range] at hr
    exact (Nat.coprime_primes hr.2.1 hp).mpr (by omega)
def apSieve (q : ℕ) (x z : ℝ) (hz : 1 ≤ z) : SelbergSieve where
  support := (range (⌊x⌋₊ + 1)).filter (· ≡ 1 [MOD q])
  prodPrimes := sieveProd q z
  prodPrimes_squarefree := sieveProd_squarefree q z
  weights := fun _ => 1
  weights_nonneg := fun _ => zero_le_one
  totalMass := x / q
  nu := (ζ : ArithmeticFunction ℝ).pdiv .id
  nu_mult := by arith_mult
  nu_pos_of_prime := fun p hp _ => by
    simp [if_neg hp.ne_zero, Nat.pos_of_ne_zero hp.ne_zero]
  nu_lt_one_of_prime := fun p hp _ => by
    simp only [ArithmeticFunction.pdiv_apply, ArithmeticFunction.natCoe_apply,
      ArithmeticFunction.zeta_apply, hp.ne_zero, ↓reduceIte, Nat.cast_one,
      ArithmeticFunction.id_apply, one_div]
    apply inv_lt_one_of_one_lt₀
    exact_mod_cast hp.one_lt
  level := z
  one_le_level := hz
lemma apSieve_nu_apply {d : ℕ} (hd : d ≠ 0) :
    ((ζ : ArithmeticFunction ℝ).pdiv .id) d = (d : ℝ)⁻¹ := by
  simp [hd]
lemma card_filter_modEq_one_dvd (q d M : ℕ) (hq : 0 < q) (hd : 0 < d) (hcop : q.Coprime d) :
    ∃ e : ℕ, e ≤ 1 ∧
      ((range M).filter (fun n => n ≡ 1 [MOD q] ∧ d ∣ n)).card = M / (q * d) + e := by
  have hcrt := (Nat.chineseRemainder hcop 1 0).prop
  set c := (Nat.chineseRemainder hcop 1 0 : ℕ)
  have hset : (range M).filter (fun n => n ≡ 1 [MOD q] ∧ d ∣ n) =
      (range M).filter (· ≡ c [MOD q * d]) := by
    ext n
    simp only [mem_filter]
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨h1, Nat.chineseRemainder_modEq_unique hcop h2 (Nat.modEq_zero_iff_dvd.mpr h3)⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, (h2.of_mul_right d).trans hcrt.1,
        Nat.modEq_zero_iff_dvd.mp ((h2.of_mul_left q).trans hcrt.2)⟩
  rw [hset, ← Nat.count_eq_card_filter_range, Nat.count_modEq_card _ (Nat.mul_pos hq hd)]
  exact ⟨_, by split_ifs <;> simp, rfl⟩
lemma abs_rem_apSieve_le (q : ℕ) (hq : 0 < q) (x z : ℝ) (hx : 0 ≤ x) (hz : 1 ≤ z) {d : ℕ}
    (hd : d ∈ (sieveProd q z).divisors) :
    |rem (s := (apSieve q x z hz).toBoundingSieve) d| ≤ 2 := by
  have hd0 : d ≠ 0 := Nat.ne_of_gt (Nat.pos_of_mem_divisors hd)
  have hcop : q.Coprime d :=
    ((coprime_sieveProd q z).coprime_dvd_left (Nat.dvd_of_mem_divisors hd)).symm
  obtain ⟨e, he, hcard⟩ := card_filter_modEq_one_dvd q d (⌊x⌋₊ + 1) hq (Nat.pos_of_ne_zero hd0) hcop
  have hmult : multSum (s := (apSieve q x z hz).toBoundingSieve) d =
      (((⌊x⌋₊ + 1) / (q * d) + e : ℕ) : ℝ) := by
    rw [← hcard]
    simp only [multSum, apSieve, sum_filter, ← sum_boole]
    refine sum_congr rfl fun n _ => ?_
    by_cases h1 : n ≡ 1 [MOD q] <;> by_cases h2 : d ∣ n <;> simp [h1, h2]
  rw [rem, hmult]
  simp only [apSieve, apSieve_nu_apply hd0]
  set M := ⌊x⌋₊ + 1
  set r := M / (q * d)
  set D : ℝ := (q : ℝ) * d
  have hD1 : (1 : ℝ) ≤ D := by
    have : 1 ≤ q * d := Nat.mul_pos hq (Nat.pos_of_ne_zero hd0)
    simp only [D]; exact_mod_cast this
  have hD : (0 : ℝ) < D := by linarith
  have hdiv := Nat.div_add_mod M (q * d)
  have hmod := Nat.mod_lt M (Nat.mul_pos hq (Nat.pos_of_ne_zero hd0))
  have hMR : (M : ℝ) = D * r + ((M % (q * d) : ℕ) : ℝ) := by
    simp only [D, r]; exact_mod_cast hdiv.symm
  have hmodR : ((M % (q * d) : ℕ) : ℝ) < D := by simp only [D]; exact_mod_cast hmod
  have hmod0 : (0 : ℝ) ≤ ((M % (q * d) : ℕ) : ℝ) := Nat.cast_nonneg _
  have hxM : x < M := by simp only [M]; push_cast; exact Nat.lt_floor_add_one x
  have hMx : (M : ℝ) ≤ x + 1 := by simp only [M]; push_cast; linarith [Nat.floor_le hx]
  have heq : (d : ℝ)⁻¹ * (x / q) = x / D := by
    simp only [D]; field_simp
  rw [heq]
  have hlo : (r : ℝ) - 1 ≤ x / D := by
    rw [le_div_iff₀ hD]; nlinarith
  have hhi : x / D ≤ r + 1 := by
    rw [div_le_iff₀ hD]; nlinarith
  have he' : (e : ℝ) ≤ 1 := by exact_mod_cast he
  have he0 : (0 : ℝ) ≤ e := Nat.cast_nonneg e
  push_cast
  rw [abs_le]
  constructor <;> linarith
def primeCountAP (q : ℕ) (x : ℝ) : ℕ :=
  ((range (⌊x⌋₊ + 1)).filter fun p => p.Prime ∧ p ≡ 1 [MOD q]).card
lemma one_add_log_pow_four_le {t : ℝ} (ht : 1 ≤ t) :
    (1 + Real.log t) ^ 4 ≤ 6561 * Real.sqrt t := by
  have ht0 : 0 ≤ t := by linarith
  have h8 : Real.log t ≤ t ^ (1 / 8 : ℝ) / (1 / 8) := Real.log_le_rpow_div ht0 (by norm_num)
  have h1 : 1 ≤ t ^ (1 / 8 : ℝ) := Real.one_le_rpow ht (by norm_num)
  have hlog : 0 ≤ Real.log t := Real.log_nonneg ht
  have h9 : 1 + Real.log t ≤ 9 * t ^ (1 / 8 : ℝ) := by linarith
  have hpow : (t ^ (1 / 8 : ℝ)) ^ 4 = Real.sqrt t := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul ht0]
    norm_num
  calc (1 + Real.log t) ^ 4 ≤ (9 * t ^ (1 / 8 : ℝ)) ^ 4 := by
        gcongr
    _ = 6561 * Real.sqrt t := by rw [mul_pow, hpow]; norm_num
theorem primeCountAP_le (q : ℕ) (hq : 1 ≤ q) (x : ℝ) (hqx : (q : ℝ) < x) :
    (primeCountAP q x : ℝ) ≤ 20000 * x / (q.totient * Real.log (x / q)) := by
  classical
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hx0 : 0 < x := by linarith
  set t := x / q with ht_def
  have ht1 : 1 < t := by rw [ht_def, lt_div_iff₀ hq0]; linarith
  have hlogt : 0 < Real.log t := Real.log_pos ht1
  set z := Real.sqrt t with hz_def
  have hz1 : 1 ≤ z := by rw [hz_def, Real.one_le_sqrt]; linarith
  have hlogz : Real.log z = Real.log t / 2 := by
    rw [hz_def, Real.log_sqrt (by linarith)]
  have hphi : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr hq
  have hphiq : (q.totient : ℝ) ≤ q := by exact_mod_cast Nat.totient_le q
  set s := apSieve q x z hz1 with hs
  have h1 : (primeCountAP q x : ℝ) ≤ siftedSum (s := s.toBoundingSieve) + z := by
    have hsift : siftedSum (s := s.toBoundingSieve) =
        (((range (⌊x⌋₊ + 1)).filter (· ≡ 1 [MOD q])).filter
          (fun n => (sieveProd q z).Coprime n)).card := by
      simp only [siftedSum, hs, apSieve]
      rw [← sum_boole, sum_filter]
    have hsub : (range (⌊x⌋₊ + 1)).filter (fun p => p.Prime ∧ p ≡ 1 [MOD q]) ⊆
        (((range (⌊x⌋₊ + 1)).filter (· ≡ 1 [MOD q])).filter
          (fun n => (sieveProd q z).Coprime n)) ∪ Icc 1 ⌊z⌋₊ := by
      intro p hp
      simp only [mem_filter] at hp
      obtain ⟨hpx, hp, hp1⟩ := hp
      rw [mem_union]
      by_cases hpz : p ≤ ⌊z⌋₊
      · right; exact mem_Icc.mpr ⟨hp.one_lt.le, hpz⟩
      · left
        simp only [mem_filter]
        exact ⟨⟨hpx, hp1⟩, coprime_sieveProd_of_lt hp (by omega)⟩
    rw [hsift, primeCountAP]
    calc (((range (⌊x⌋₊ + 1)).filter (fun p => p.Prime ∧ p ≡ 1 [MOD q])).card : ℝ)
        ≤ ((((range (⌊x⌋₊ + 1)).filter (· ≡ 1 [MOD q])).filter
          (fun n => (sieveProd q z).Coprime n)) ∪ Icc 1 ⌊z⌋₊).card := by
          exact_mod_cast card_le_card hsub
      _ ≤ ((((range (⌊x⌋₊ + 1)).filter (· ≡ 1 [MOD q])).filter
          (fun n => (sieveProd q z).Coprime n)).card : ℝ) + (Icc 1 ⌊z⌋₊).card := by
          exact_mod_cast card_union_le _ _
      _ ≤ _ := by
          gcongr
          rw [Nat.card_Icc, Nat.add_sub_cancel]
          exact Nat.floor_le (by linarith)
  have h2 := SelbergSieve.selberg_bound_simple s
  have h3 : ∑ d ∈ Nat.divisors (s.prodPrimes), (if (d : ℝ) ≤ s.level then
      (3 : ℝ) ^ ω d * |rem (s := s.toBoundingSieve) d| else 0) ≤ 2 * z * (1 + Real.log z) ^ 3 :=
    rem_sum_le_of_const_of_dvd s 2 fun d hd => abs_rem_apSieve_le q hq x z hx0.le hz1 hd
  have hnu_eq : s.nu = (ζ : ArithmeticFunction ℝ).pdiv .id := rfl
  have h4 : ((q.totient : ℝ) / q) * (Real.log t / 4) ≤ s.selbergBoundingSum := by
    have hS := selbergBoundingSum_ge_sum_div_coprime s q
      (fun p hp hpz hpq => dvd_sieveProd hp hpz hpq)
      (by rw [hnu_eq]; exact CompletelyMultiplicative.zeta.pdiv CompletelyMultiplicative.id)
      (fun n => by
        rw [hnu_eq]
        by_cases h : n = 0 <;> simp [h])
      (fun p hp _ => s.nu_lt_one_of_prime p hp (by assumption))
    have hlev : s.level = z := rfl
    rw [hlev] at hS
    have hsqz : 1 ≤ Real.sqrt z := by rw [Real.one_le_sqrt]; exact hz1
    have hsum : ∑ m ∈ (Icc 1 ⌊Real.sqrt z⌋₊).filter (fun m => m.Coprime q), s.nu m =
        ∑ m ∈ (Icc 1 ⌊Real.sqrt z⌋₊).filter (fun m => m.Coprime q), (m : ℝ)⁻¹ := by
      refine sum_congr rfl fun m hm => ?_
      have : m ≠ 0 := by
        simp only [mem_filter, mem_Icc] at hm; omega
      rw [hnu_eq, apSieve_nu_apply this]
    have hlog := Aux.log_le_sum_inv (Real.sqrt z) hsqz
    have hlogsq : Real.log (Real.sqrt z) = Real.log t / 4 := by
      rw [Real.log_sqrt (by linarith), hlogz]; ring
    have hcop := sum_inv_coprime_ge q ⌊Real.sqrt z⌋₊
    have hfrac : 0 ≤ (q.totient : ℝ) / q := by positivity
    calc ((q.totient : ℝ) / q) * (Real.log t / 4)
        = ((q.totient : ℝ) / q) * Real.log (Real.sqrt z) := by rw [hlogsq]
      _ ≤ ((q.totient : ℝ) / q) * ∑ d ∈ Icc 1 ⌊Real.sqrt z⌋₊, (d : ℝ)⁻¹ :=
          mul_le_mul_of_nonneg_left hlog hfrac
      _ ≤ _ := hcop
      _ = _ := hsum.symm
      _ ≤ _ := hS
  have hX : s.totalMass = x / q := rfl
  have h5 : s.totalMass / s.selbergBoundingSum ≤ 4 * x / (q.totient * Real.log t) := by
    rw [hX]
    have hpos : 0 < ((q.totient : ℝ) / q) * (Real.log t / 4) := by positivity
    calc x / q / s.selbergBoundingSum ≤ x / q / (((q.totient : ℝ) / q) * (Real.log t / 4)) :=
          div_le_div_of_nonneg_left (by positivity) hpos h4
      _ = 4 * x / (q.totient * Real.log t) := by
          field_simp
  have h6 : 2 * z * (1 + Real.log z) ^ 3 + z ≤ 19683 * x / (q.totient * Real.log t) := by
    have hlz : Real.log z ≤ Real.log t := by rw [hlogz]; linarith
    have hlz0 : 0 ≤ Real.log z := Real.log_nonneg hz1
    have hA : 1 ≤ (1 + Real.log z) ^ 3 := one_le_pow₀ (by linarith)
    have hz0 : 0 ≤ z := by linarith
    have hstep : 2 * z * (1 + Real.log z) ^ 3 + z ≤ 3 * z * (1 + Real.log t) ^ 3 := by
      have : (1 + Real.log z) ^ 3 ≤ (1 + Real.log t) ^ 3 := by gcongr
      nlinarith
    have hzz : z * z = t := Real.mul_self_sqrt (by linarith)
    have hkey : 3 * z * (1 + Real.log t) ^ 3 * Real.log t ≤ 19683 * t := by
      have h4' := one_add_log_pow_four_le ht1.le
      have hB : (1 + Real.log t) ^ 3 * Real.log t ≤ (1 + Real.log t) ^ 4 := by
        rw [pow_succ]
        have : 0 ≤ (1 + Real.log t) ^ 3 := by positivity
        nlinarith
      calc 3 * z * (1 + Real.log t) ^ 3 * Real.log t
          = 3 * z * ((1 + Real.log t) ^ 3 * Real.log t) := by ring
        _ ≤ 3 * z * (6561 * z) :=
            mul_le_mul_of_nonneg_left (hB.trans h4') (by positivity)
        _ = 19683 * t := by rw [← hzz]; ring
    have htx : 19683 * t / Real.log t ≤ 19683 * x / (q.totient * Real.log t) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have hxq : x / q * q.totient ≤ x := by
        rw [div_mul_eq_mul_div, div_le_iff₀ hq0]; nlinarith
      have h19 : 0 ≤ 19683 * Real.log t := by positivity
      rw [ht_def] at h19 ⊢
      nlinarith [mul_le_mul_of_nonneg_right hxq h19]
    calc 2 * z * (1 + Real.log z) ^ 3 + z ≤ 3 * z * (1 + Real.log t) ^ 3 := hstep
      _ ≤ 19683 * t / Real.log t := by rw [le_div_iff₀ hlogt]; exact hkey
      _ ≤ _ := htx
  calc (primeCountAP q x : ℝ) ≤ siftedSum (s := s.toBoundingSieve) + z := h1
    _ ≤ s.totalMass / s.selbergBoundingSum + 2 * z * (1 + Real.log z) ^ 3 + z := by
        have : s.level = z := rfl
        simp only [this] at h2 h3
        linarith
    _ ≤ 4 * x / (q.totient * Real.log t) + 19683 * x / (q.totient * Real.log t) := by
        linarith
    _ ≤ 20000 * x / (q.totient * Real.log t) := by
        rw [← add_div]
        gcongr
        linarith
end Artin.BrunTitchmarsh
end
end

theorem OMA.solution : OMA.R_ArtinPrimitiveRootsConjecture_conditional_artin_primitive_roots_parts_i_R1.H2 :=
  fun q hq x hx => Artin.BrunTitchmarsh.primeCountAP_le q hq x hx
