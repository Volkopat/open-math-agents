import OMAStatements.S_oeis_a113598

-- Credit: @rleshner

/-!
# Prime digit permutations at every decimal width

For Amarnath Murthy’s OEIS A113598 conjecture, use explicit witnesses below
eight digits and the pigeonhole principle with a Chebyshev interval estimate
from eight digits onward. Digits are counted with multiplicity. The finite
witnesses use the leading-zero convention explained by R. J. Mathar.
-/

namespace PrimePerm

private theorem err_bound (n : ℕ) (hn : 8 ≤ n) :
    80*(n+1) + 160*n*4^n ≤ 10^n := by
  induction n, hn using Nat.le_induction with
  | base => decide
  | succ n hn ih =>
    calc
      80*(n+1+1) + 160*(n+1)*4^(n+1) ≤ 10*(80*(n+1) + 160*n*4^n) := by
        rw [pow_succ]
        nlinarith [Nat.mul_le_mul_right (4^n) (show 1 ≤ n by omega)]
      _ ≤ 10*10^n := Nat.mul_le_mul_left _ ih
      _ = _ := by rw [pow_succ, Nat.mul_comm]

private theorem color_bound (n : ℕ) (hn : 8 ≤ n) :
    16*n^2*Nat.choose (n+9) 9 < 10^n := by
  induction n, hn using Nat.le_induction with
  | base => decide
  | succ n hn ih =>
    have h := Nat.choose_mul_succ_eq (n+9) 9
    rw [show n + 9 + 1 - 9 = n+1 by omega] at h
    have hchoose : Nat.choose (n+1+9) 9 ≤ 2*Nat.choose (n+9) 9 := by
      apply Nat.le_of_mul_le_mul_right (c:=n+1) _ (by omega)
      rw [show n + 1 + 9 = n+9+1 by omega, ← h]
      nlinarith [Nat.mul_le_mul_left (Nat.choose (n+9) 9) (show n+9+1 ≤ 2*(n+1) by omega)]
    calc
      16*(n+1)^2*Nat.choose (n+1+9) 9 ≤ 16*(2*n)^2*(2*Nat.choose (n+9) 9) := by
        gcongr; omega
      _ ≤ 10*(16*n^2*Nat.choose (n+9) 9) := by nlinarith
      _ < 10*10^n := by omega
      _ = _ := by rw [pow_succ, Nat.mul_comm]

private theorem log_bounds : (1:ℝ)/2 ≤ Real.log 2 ∧ Real.log 4 ≤ 2 ∧ Real.log 10 ≤ 4 := by
  have lo := Real.one_sub_inv_le_log_of_pos (x:=(2:ℝ)) (by norm_num)
  have hi := Real.log_le_sub_one_of_pos (x:=(2:ℝ)) (by norm_num)
  have h4 := Real.log_pow (2:ℝ) 2
  have h16 := Real.log_pow (2:ℝ) 4
  have cmp := Real.log_le_log (by norm_num : (0:ℝ)<10) (by norm_num : (10:ℝ)≤16)
  norm_num at lo hi h4 h16
  exact ⟨by linarith, by linarith, by linarith⟩

private theorem theta_diff_upper (a b : ℕ) (h : a≤b) :
    Chebyshev.theta b - Chebyshev.theta a ≤
      ((Nat.primesLE b) \ (Nat.primesLE a)).card * Real.log b := by
  classical
  rw [Chebyshev.theta_eq_sum_primesLE_log, Chebyshev.theta_eq_sum_primesLE_log]
  have eq := Finset.sum_sdiff (f:=fun p : ℕ => Real.log p) (Nat.primesLE_mono h)
  have le : ∑ p ∈ (Nat.primesLE b \ Nat.primesLE a), Real.log p ≤
      ∑ _p ∈ (Nat.primesLE b \ Nat.primesLE a), Real.log b := by
    apply Finset.sum_le_sum
    intro p hp
    have I := Nat.mem_primesLE.mp (Finset.mem_sdiff.mp hp).1
    exact Real.log_le_log (by exact_mod_cast I.2.pos) (by exact_mod_cast I.1)
  simp only [Finset.sum_const, nsmul_eq_mul] at le
  linarith

theorem abundant_primes (n : ℕ) (hn : 8 ≤ n) :
    (n-1) * Nat.choose (n+9) 9 < ((Nat.primesLE (10^n)) \ (Nat.primesLE (10^(n-1)))).card := by
  obtain ⟨log2, log4, log10⟩ := log_bounds
  have h10 : 1 ≤ (10:ℝ)^n := one_le_pow₀ (by norm_num)
  have logx : Real.log ((10:ℝ)^n) ≤ 4*n := by
    rw [Real.log_pow]; nlinarith [mul_le_mul_of_nonneg_left log10 (Nat.cast_nonneg (α:=ℝ) n)]
  have logx1 : Real.log ((10:ℝ)^n + 1) ≤ 4*(n+1) := by
    calc
      _ ≤ Real.log ((10:ℝ)^(n+1)) := Real.log_le_log (by positivity) (by rw [pow_succ]; linarith)
      _ ≤ _ := by rw [Real.log_pow]; push_cast; ring_nf; nlinarith [mul_le_mul_of_nonneg_left log10 (Nat.cast_nonneg (α:=ℝ) n)]
  have sqrtx : Real.sqrt ((10:ℝ)^n) ≤ 4^n := by
    apply (Real.sqrt_le_iff).mpr
    refine ⟨by positivity, ?_⟩
    rw [← pow_mul, Nat.mul_comm, pow_mul]; gcongr; norm_num
  have err : 80*((n:ℝ)+1) + 160*n*4^n ≤ 10^n := by exact_mod_cast err_bound n hn
  have col : 16*(n:ℝ)^2*(Nat.choose (n+9) 9 : ℝ) < 10^n := by exact_mod_cast color_bound n hn
  have thetaLo := Chebyshev.theta_ge (10^n)
  have thetaHi := Chebyshev.theta_le_log4_mul_x (x:=(10:ℝ)^(n-1)) (by positivity)
  push_cast at thetaLo
  have hprev : (10:ℝ)^(n-1) * 10 = 10^n := by
    rw [← pow_succ, show n-1+1=n by omega]
  have hsum := theta_diff_upper (10^(n-1)) (10^n) (Nat.pow_le_pow_right (by decide) (by omega))
  push_cast at hsum
  have hlognn := Real.log_nonneg h10
  have e1 := mul_le_mul sqrtx logx hlognn (by positivity)
  have e2 := mul_le_mul_of_nonneg_right log4 (show 0 ≤ (10:ℝ)^(n-1) by positivity)
  have e3 := mul_le_mul_of_nonneg_left log2 (show 0 ≤ (10:ℝ)^n by positivity)
  let c := ((Nat.primesLE (10^n)) \ (Nat.primesLE (10^(n-1)))).card
  have hcard : Chebyshev.theta ((10:ℝ)^n) - Chebyshev.theta ((10:ℝ)^(n-1)) ≤ c*(4*n) :=
    hsum.trans (mul_le_mul_of_nonneg_left logx (by positivity))
  by_contra! he
  have he' : c ≤ n*Nat.choose (n+9) 9 := he.trans (Nat.mul_le_mul_right _ (by omega))
  have heR : (c:ℝ) ≤ n*(Nat.choose (n+9) 9 : ℝ) := by exact_mod_cast he'
  have e4 := mul_le_mul_of_nonneg_right heR (show 0 ≤ 4*(n:ℝ) by positivity)
  nlinarith only [err, col, thetaLo, thetaHi, hprev, e1, e2, e3, e4, hcard, logx1]

end PrimePerm

namespace PrimePerm
open OMA.S_oeis_a113598

private theorem permPrimes_finite (p : ℕ) : (permPrimes p).Finite := by
  apply Set.Finite.subset (Set.toFinite ((Nat.ofDigits 10) '' (↑((Nat.digits 10 p).permutations.toFinset) : Set (List ℕ)))) ?_
  intro q h
  obtain ⟨_, l, hl, rfl⟩ := h
  exact ⟨l, by simpa [List.mem_permutations] using hl, rfl⟩

private def colorDigit (d : ℕ) : Fin 10 := ⟨d%10, Nat.mod_lt _ (by decide)⟩

private theorem recoverDigits (x : ℕ) :
    ((Nat.digits 10 x).map colorDigit).map Fin.val = Nat.digits 10 x := by
  rw [List.map_map]
  exact List.map_congr_left (fun d hd => Nat.mod_eq_of_lt (Nat.digits_lt_base (by decide) hd)) |>.trans (List.map_id _)

theorem witness_from_count (n : ℕ) (hn : 1 ≤ n)
    (H : (n-1) * Nat.choose (n+9) 9 < ((Nat.primesLE (10^n)) \ (Nat.primesLE (10^(n-1)))).card) :
    ∃ p : ℕ, p.Prime ∧ (Nat.digits 10 p).length = n ∧ n ≤ Nat.card (permPrimes p) := by
  classical
  let S := (Nat.primesLE (10^n)) \ (Nat.primesLE (10^(n-1)))
  have props {p : ℕ} (hp : p ∈ S) : p.Prime ∧ (Nat.digits 10 p).length = n := by
    obtain ⟨h₁,h₂⟩ := Finset.mem_sdiff.mp hp
    obtain ⟨hle,hpr⟩ := Nat.mem_primesLE.mp h₁
    have hne : p ≠ 10^n := by
      rintro rfl
      have h := Nat.Prime.eq_one_of_pow hpr
      subst n
      norm_num at hpr
    have hlo : 10^(n-1) < p := lt_of_not_ge (fun h => h₂ (Nat.mem_primesLE.mpr ⟨h,hpr⟩))
    refine ⟨hpr, ?_⟩
    rw [Nat.length_digits 10 _ (by decide) hpr.ne_zero]
    have up := (Nat.log_lt_iff_lt_pow (by decide : 1<10) hpr.ne_zero).mpr (lt_of_le_of_ne hle hne)
    have lo := (Nat.le_log_iff_pow_le (by decide : 1<10) hpr.ne_zero).mpr hlo.le
    omega
  let col (p : S) : Sym (Fin 10) n := ⟨(Nat.digits 10 p.val).map colorDigit, by simp [(props p.property).2]⟩
  have countColors : Fintype.card (Sym (Fin 10) n) = Nat.choose (n+9) 9 := by
    rw [Sym.card_sym_eq_choose]; simp only [Fintype.card_fin]
    rw [show 10 + n - 1 = n+9 by omega, ← Nat.choose_symm_add]
  have ch : Fintype.card (Sym (Fin 10) n) * (n-1) < Fintype.card S := by
    simpa only [countColors, Fintype.card_coe, Nat.mul_comm] using H
  obtain ⟨c,hc⟩ := Fintype.exists_lt_card_fiber_of_mul_lt_card col ch
  let fiber := Finset.univ.filter (fun p : S => col p = c)
  have hc' : n ≤ fiber.card := by change n ≤ (Finset.univ.filter _).card; omega
  obtain ⟨p,hp⟩ := Finset.card_pos.mp (lt_of_lt_of_le (by omega : 0<n) hc')
  refine ⟨p.val,(props p.property).1,(props p.property).2, ?_⟩
  let _ : Finite (permPrimes p.val) := (permPrimes_finite _).to_subtype
  let f (q : fiber) : permPrimes p.val := by
    have eqcol : col q.val = col p := (Finset.mem_filter.mp q.property).2.trans (Finset.mem_filter.mp hp).2.symm
    have heq := congrArg (fun z : Sym (Fin 10) n => z.val) eqcol
    have hperm : ((Nat.digits 10 q.val.val).map colorDigit).Perm ((Nat.digits 10 p.val).map colorDigit) := Quotient.exact heq
    have hr := hperm.map Fin.val
    rw [recoverDigits, recoverDigits] at hr
    exact ⟨q.val.val,(props q.val.property).1,Nat.digits 10 q.val.val,hr,(Nat.ofDigits_digits 10 _).symm⟩
  have inj : Function.Injective f := by
    intro q r h
    exact Subtype.ext (Subtype.ext (congrArg (fun z : permPrimes p.val => z.val) h))
  apply hc'.trans
  have bound := Nat.card_le_card_of_injective f inj
  rwa [Nat.card_eq_fintype_card (α := fiber), Fintype.card_coe] at bound
end PrimePerm

open OMA.S_oeis_a113598

namespace PrimePerm

private lemma written_digits (p : ℕ) (ds : List ℕ)
    (hv : Nat.ofDigits 10 ds = p) (hb : ∀ d ∈ ds, d < 10)
    (hz : ∀ h : ds ≠ [], ds.getLast h ≠ 0) : Nat.digits 10 p = ds := by
  rw [← hv]
  exact Nat.digits_ofDigits 10 (by decide) ds hb hz

private lemma with_lists (n p : ℕ) (ds : List ℕ) (qs : List ℕ)
    (hp : p.Prime) (hds : Nat.digits 10 p = ds) (hlen : ds.length = n)
    (hnum : n ≤ qs.length) (hn : qs.Nodup)
    (hqs : ∀ q ∈ qs, Nat.Prime q ∧ ∃ l, l.Perm ds ∧ q = Nat.ofDigits 10 l) :
    ∃ p : ℕ, p.Prime ∧ (Nat.digits 10 p).length = n ∧ n ≤ Nat.card (permPrimes p) := by
  refine ⟨p, hp, hds ▸ hlen, ?_⟩
  have fin : (permPrimes p).Finite := by
    refine (Set.finite_Iio (10 ^ n)).subset ?_
    rintro m ⟨_, w, hw, rfl⟩
    have h := Nat.ofDigits_lt_base_pow_length (by decide : 1<10)
      (fun d (hd : d ∈ w) => Nat.digits_lt_base (by decide) (hw.mem_iff.mp hd))
    simpa [hw.length_eq, hds, hlen] using h
  have sub : (↑qs.toFinset : Set ℕ) ⊆ permPrimes p := by
    intro q hq
    simpa [permPrimes, hds] using hqs q (by simpa using hq)
  have hc := Set.ncard_le_ncard sub fin
  rw [Set.ncard_coe_finset, List.toFinset_card_of_nodup hn] at hc
  exact hnum.trans hc

private theorem row_1 : ∃ p : ℕ, p.Prime ∧ (Nat.digits 10 p).length = 1 ∧ 1 ≤ Nat.card (permPrimes p) := by
  apply with_lists 1 2 [2] [2] (by norm_num)
    (written_digits _ _ (by decide) (by decide) (by intro h; norm_num)) rfl (by decide) (by decide)
  intro q h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl
  · exact ⟨by norm_num, [2], by decide, by decide⟩
private theorem row_2 : ∃ p : ℕ, p.Prime ∧ (Nat.digits 10 p).length = 2 ∧ 2 ≤ Nat.card (permPrimes p) := by
  apply with_lists 2 13 [3, 1] [13, 31] (by norm_num)
    (written_digits _ _ (by decide) (by decide) (by intro h; norm_num)) rfl (by decide) (by decide)
  intro q h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl
  · exact ⟨by norm_num, [3, 1], by decide, by decide⟩
  · exact ⟨by norm_num, [1, 3], by decide, by decide⟩
private theorem row_3 : ∃ p : ℕ, p.Prime ∧ (Nat.digits 10 p).length = 3 ∧ 3 ≤ Nat.card (permPrimes p) := by
  apply with_lists 3 103 [3, 0, 1] [13, 31, 103] (by norm_num)
    (written_digits _ _ (by decide) (by decide) (by intro h; norm_num)) rfl (by decide) (by decide)
  intro q h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl
  · exact ⟨by norm_num, [3, 1, 0], by decide, by decide⟩
  · exact ⟨by norm_num, [1, 3, 0], by decide, by decide⟩
  · exact ⟨by norm_num, [3, 0, 1], by decide, by decide⟩
private theorem row_4 : ∃ p : ℕ, p.Prime ∧ (Nat.digits 10 p).length = 4 ∧ 4 ≤ Nat.card (permPrimes p) := by
  apply with_lists 4 1009 [9, 0, 0, 1] [19, 109, 1009, 9001] (by norm_num)
    (written_digits _ _ (by decide) (by decide) (by intro h; norm_num)) rfl (by decide) (by decide)
  intro q h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl
  · exact ⟨by norm_num, [9, 1, 0, 0], by decide, by decide⟩
  · exact ⟨by norm_num, [9, 0, 1, 0], by decide, by decide⟩
  · exact ⟨by norm_num, [9, 0, 0, 1], by decide, by decide⟩
  · exact ⟨by norm_num, [1, 0, 0, 9], by decide, by decide⟩
private theorem row_5 : ∃ p : ℕ, p.Prime ∧ (Nat.digits 10 p).length = 5 ∧ 5 ≤ Nat.card (permPrimes p) := by
  apply with_lists 5 10007 [7, 0, 0, 0, 1] [17, 71, 107, 701, 7001] (by norm_num)
    (written_digits _ _ (by decide) (by decide) (by intro h; norm_num)) rfl (by decide) (by decide)
  intro q h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl
  · exact ⟨by norm_num, [7, 1, 0, 0, 0], by decide, by decide⟩
  · exact ⟨by norm_num, [1, 7, 0, 0, 0], by decide, by decide⟩
  · exact ⟨by norm_num, [7, 0, 1, 0, 0], by decide, by decide⟩
  · exact ⟨by norm_num, [1, 0, 7, 0, 0], by decide, by decide⟩
  · exact ⟨by norm_num, [1, 0, 0, 7, 0], by decide, by decide⟩
private theorem row_6 : ∃ p : ℕ, p.Prime ∧ (Nat.digits 10 p).length = 6 ∧ 6 ≤ Nat.card (permPrimes p) := by
  apply with_lists 6 100019 [9, 1, 0, 0, 0, 1] [191, 911, 1019, 1091, 1109, 1901] (by norm_num)
    (written_digits _ _ (by decide) (by decide) (by intro h; norm_num)) rfl (by decide) (by decide)
  intro q h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨by norm_num, [1, 9, 1, 0, 0, 0], by decide, by decide⟩
  · exact ⟨by norm_num, [1, 1, 9, 0, 0, 0], by decide, by decide⟩
  · exact ⟨by norm_num, [9, 1, 0, 1, 0, 0], by decide, by decide⟩
  · exact ⟨by norm_num, [1, 9, 0, 1, 0, 0], by decide, by decide⟩
  · exact ⟨by norm_num, [9, 0, 1, 1, 0, 0], by decide, by decide⟩
  · exact ⟨by norm_num, [1, 0, 9, 1, 0, 0], by decide, by decide⟩
private theorem row_7 : ∃ p : ℕ, p.Prime ∧ (Nat.digits 10 p).length = 7 ∧ 7 ≤ Nat.card (permPrimes p) := by
  apply with_lists 7 2100001 [1, 0, 0, 0, 0, 1, 2] [211, 1021, 1201, 2011, 20011, 20101, 21001] (by norm_num)
    (written_digits _ _ (by decide) (by decide) (by intro h; norm_num)) rfl (by decide) (by decide)
  intro q h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨by norm_num, [1, 1, 2, 0, 0, 0, 0], by decide, by decide⟩
  · exact ⟨by norm_num, [1, 2, 0, 1, 0, 0, 0], by decide, by decide⟩
  · exact ⟨by norm_num, [1, 0, 2, 1, 0, 0, 0], by decide, by decide⟩
  · exact ⟨by norm_num, [1, 1, 0, 2, 0, 0, 0], by decide, by decide⟩
  · exact ⟨by norm_num, [1, 1, 0, 0, 2, 0, 0], by decide, by decide⟩
  · exact ⟨by norm_num, [1, 0, 1, 0, 2, 0, 0], by decide, by decide⟩
  · exact ⟨by norm_num, [1, 0, 0, 1, 2, 0, 0], by decide, by decide⟩

theorem finite_n (n : ℕ) (hn : 1≤n) (ht : n<8) : ∃ p : ℕ, p.Prime ∧ (Nat.digits 10 p).length = n ∧ n ≤ Nat.card (permPrimes p) := by
  interval_cases n
  · exact row_1
  · exact row_2
  · exact row_3
  · exact row_4
  · exact row_5
  · exact row_6
  · exact row_7

end PrimePerm

theorem OMA.solution : type_of% @OMA.S_oeis_a113598.main := by
  intro n hn
  by_cases h : 8 ≤ n
  · exact PrimePerm.witness_from_count n hn (PrimePerm.abundant_primes n h)
  · exact PrimePerm.finite_n n hn (by omega)
