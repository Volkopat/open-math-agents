import OMAStatements.S_oeis_a006530

-- Problem: A006530: Gpf(n): greatest prime dividing n, for n >= 2; a(1)=1.
-- Credit: @sobrien032

/-!
M. Farrokhi D. G. asked for a bound on the sizes of these orbits in OEIS A006530.
The board formalization is by David Ganz. For a = 1 and b = −1, a prime p > 2
maps to the largest prime factor of p − 1. William D. Banks and Igor E. Shparlinski
proved a quantitative lower bound for the number of iterations to reach 2 in
Corollary 1.5 of On values taken by the largest prime factor of shifted primes
(2007), doi 10.1017/S1446788700017511.

Here a finite Euler product bounds every logarithmic moment of prime reciprocals
at each fixed depth. Euler's divergence theorem then rules out a common depth.
Lean proof by Codex.
-/

namespace GpfBounds

noncomputable def weight (k n : ℕ) : ℝ := (1 + Real.log n)^k / n

def parent (p : ℕ) : ℕ := (p-1).primeFactors.sup id

def shallow : ℕ → ℕ → Prop
  | 0, p => p ≤ 2
  | d+1, p => p ≤ 2 ∨ shallow d (parent p)

def SmoothBound : Prop :=
  ∃ (D : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ q : ℕ, 2 ≤ q → ∀ F : Finset ℕ,
    (∀ m ∈ F, m ∈ (q+1).smoothNumbers) →
    ∑ m ∈ F, (m:ℝ) ^ ((1 / (4*(1+Real.log q)) : ℝ)-1) ≤ C*(1+Real.log q)^D

def FiberBound (k : ℕ) : Prop :=
  ∃ (K : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ q : ℕ, 2 ≤ q → ∀ F : Finset ℕ,
    (∀ p ∈ F, p.Prime ∧ 2 < p ∧ parent p = q) →
    ∑ p ∈ F, weight k p ≤ C * weight K q

end GpfBounds

namespace GpfBounds

theorem zeta_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 < t → t ≤ 1 →
    (∑' m : ℕ, (m : ℝ) ^ (-1-t)) ≤ C / t := by
  refine ⟨2, by norm_num, ?_⟩
  intro t ht ht1
  have hs : 1 < 1+t := by linarith
  have hsum : Summable (fun m : ℕ ↦ (m : ℝ) ^ (-1-t)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  rw [hsum.tsum_eq_zero_add]
  simp only [Nat.cast_zero, Real.zero_rpow (by linarith : (-1:ℝ)-t ≠ 0), zero_add]
  have hterm : 0 ≤ ZetaAsymptotics.termTSum (1+t) :=
    tsum_nonneg fun n ↦ ZetaAsymptotics.term_nonneg (n+1) (1+t)
  have hb := ZetaAsymptotics.zeta_limit_aux1 hs
  rw [show 1+t-1=t by ring] at hb
  have hle : 1 ≤ 1/t := (le_div_iff₀ ht).mpr (by simpa using ht1)
  calc
    (∑' m : ℕ, ((m+1 : ℕ) : ℝ)^(-1-t)) =
      ∑' m : ℕ, 1 / (m+1 : ℝ)^(1+t) := by
        apply tsum_congr
        intro m
        rw [Nat.cast_add, Nat.cast_one, show -1-t = -(1+t) by ring,
          Real.rpow_neg (by positivity), one_div]
    _ ≤ 1/t + 1 := by nlinarith [mul_nonneg (by linarith : 0 ≤ 1+t) hterm]
    _ ≤ 2/t := by linarith [show 2/t = 1/t + 1/t by ring]

end GpfBounds

namespace GpfBounds

private noncomputable def natPowHom (s : ℝ) : ℕ →* ℝ where
  toFun n := (n : ℝ) ^ s
  map_one' := by simp
  map_mul' a b := by
    rw [Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg a) (Nat.cast_nonneg b)]

private theorem smooth_euler (Q : ℕ) (s : ℝ) (hs : s < 0) :
    HasSum (fun m : Q.smoothNumbers ↦ (m.val : ℝ)^s)
      (∏ p ∈ Q.primesBelow, (1-(p:ℝ)^s)⁻¹) := by
  apply (EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_geometric
    (f := natPowHom s) _ Q).2
  intro p hp
  change ‖(p:ℝ)^s‖ < 1
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
  exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp.one_lt) hs

private theorem factor_le_pow {x y : ℝ} (hx : 0 ≤ x) (hx' : x ≤ 2/3)
    (hy : y < 1) (hxy : x ≤ 2*y) :
    (1-x)⁻¹ ≤ ((1-y)⁻¹)^6 := by
  have hp : 0 < 1-x := by linarith
  have hq : 0 < 1-y := by linarith
  apply (Real.log_le_log_iff (inv_pos.mpr hp) (pow_pos (inv_pos.mpr hq) 6)).mp
  rw [Real.log_inv, Real.log_pow, Real.log_inv]
  have hl := Real.one_sub_inv_le_log_of_pos hp
  have hu := Real.log_le_sub_one_of_pos hq
  have hh : (1-x)⁻¹ ≤ 1+3*x := by
    rw [inv_eq_one_div, div_le_iff₀ hp]
    nlinarith [mul_nonneg hx (sub_nonneg.mpr hx')]
  norm_num
  linarith

private theorem prime_factor_comparison (q p : ℕ) (hp : p.Prime) (hpq : p ≤ q) :
    let t : ℝ := 1 / (4 * (1+Real.log q))
    (1 - (p:ℝ)^(t-1))⁻¹ ≤ ((1 - (p:ℝ)^(-1-t))⁻¹)^6 := by
  let t : ℝ := 1 / (4 * (1+Real.log q))
  change (1 - (p:ℝ)^(t-1))⁻¹ ≤ ((1 - (p:ℝ)^(-1-t))⁻¹)^6
  have hp1 : (1:ℝ) < p := by exact_mod_cast hp.one_lt
  have hp2 : (2:ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hpr : (0:ℝ) < p := by linarith
  have hlp : Real.log p ≤ Real.log q := Real.log_le_log hpr (by exact_mod_cast hpq)
  have hlq : 0 ≤ Real.log q := (Real.log_nonneg hp1.le).trans hlp
  have ht : 0 < t := by dsimp [t]; positivity
  have hpt : 0 < (p:ℝ)^t := Real.rpow_pos_of_pos hpr _
  have hlog : Real.log p * t ≤ 1/4 := by
    dsimp [t]
    rw [mul_one_div, div_le_iff₀ (by positivity)]
    linarith
  have hptle : (p:ℝ)^t ≤ 4/3 := by
    apply (Real.log_le_log_iff hpt (by norm_num)).mp
    rw [Real.log_rpow hpr, mul_comm]
    have h := Real.one_sub_inv_le_log_of_pos (show (0:ℝ) < 4/3 by norm_num)
    norm_num at h
    linarith
  have hu : (p:ℝ)^(t-1) = (p:ℝ)^t / p := by rw [Real.rpow_sub hpr, Real.rpow_one]
  have hv : (p:ℝ)^(-1-t) = 1 / ((p:ℝ)^t * p) := by
    rw [show -1-t = -(t+1) by ring, Real.rpow_neg hpr.le, Real.rpow_add hpr, Real.rpow_one,
      one_div]
  apply factor_le_pow (Real.rpow_nonneg hpr.le _)
  · rw [hu, div_le_iff₀ hpr]
    linarith
  · exact Real.rpow_lt_one_of_one_lt_of_neg hp1 (by linarith)
  · rw [hu, hv]
    rw [mul_one_div, div_le_div_iff₀ hpr (mul_pos hpt hpr)]
    have hsquare : ((p:ℝ)^t)^2 ≤ (4/3:ℝ)^2 := by gcongr
    nlinarith [mul_nonneg (show 0 ≤ 2-((p:ℝ)^t)^2 by nlinarith) hpr.le]

theorem smooth_bound : SmoothBound := by
  obtain ⟨C, hC, hbound⟩ := zeta_bound
  refine ⟨6, (4*C)^6, by positivity, ?_⟩
  intro q hq F hF
  let t : ℝ := 1 / (4*(1+Real.log q))
  have hl : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast show 1 ≤ q by omega)
  have ht : 0 < t := by dsimp [t]; positivity
  have ht1 : t < 1 := by
    dsimp [t]
    rw [div_lt_one (by positivity)]
    linarith
  have hplus := smooth_euler (q+1) (t-1) (by linarith)
  have hminus := smooth_euler (q+1) (-1-t) (by linarith)
  let i : F → (q+1).smoothNumbers := fun x ↦ ⟨x.val, hF _ x.property⟩
  have hi : Function.Injective i := fun x y h ↦ Subtype.ext (congrArg (fun z : (q+1).smoothNumbers ↦ z.val) h)
  have hFin := tsum_comp_le_tsum_of_inj hplus.summable
    (fun x ↦ Real.rpow_nonneg (Nat.cast_nonneg _) _) hi
  have hsum : (∑ m ∈ F, (m:ℝ)^(t-1)) ≤ ∏ p ∈ (q+1).primesBelow, (1-(p:ℝ)^(t-1))⁻¹ := by
    rw [← hplus.tsum_eq]
    rw [← Finset.sum_attach F (fun m : ℕ ↦ (m:ℝ)^(t-1))]
    simpa [i, Function.comp_def, tsum_fintype] using hFin
  have heuler : (∏ p ∈ (q+1).primesBelow, (1-(p:ℝ)^(-1-t))⁻¹) ≤ C/t := by
    rw [← hminus.tsum_eq]
    apply le_trans _ (hbound t ht ht1.le)
    exact tsum_comp_le_tsum_of_inj (Real.summable_nat_rpow.mpr (by linarith))
      (fun n ↦ Real.rpow_nonneg (Nat.cast_nonneg _) _) Subtype.val_injective
  apply hsum.trans
  calc
    _ ≤ ∏ p ∈ (q+1).primesBelow, ((1-(p:ℝ)^(-1-t))⁻¹)^6 := by
      apply Finset.prod_le_prod
      · intro p hp
        apply inv_nonneg.mpr
        apply sub_nonneg.mpr
        exact (Real.rpow_lt_one_of_one_lt_of_neg
          (by exact_mod_cast (Nat.prime_of_mem_primesBelow hp).one_lt) (by linarith : t-1<0)).le
      · intro p hp
        exact prime_factor_comparison q p (Nat.prime_of_mem_primesBelow hp)
          (by have := (Nat.lt_of_mem_primesBelow hp); omega)
    _ = (∏ p ∈ (q+1).primesBelow, (1-(p:ℝ)^(-1-t))⁻¹)^6 := by rw [Finset.prod_pow]
    _ ≤ (C/t)^6 := by
      apply pow_le_pow_left₀ _ heuler
      rw [← hminus.tsum_eq]
      exact tsum_nonneg (fun _ ↦ Real.rpow_nonneg (Nat.cast_nonneg _) _)
    _ = (4*C)^6*(1+Real.log q)^6 := by simp only [t, div_eq_mul_inv, one_mul, inv_inv]; ring

end GpfBounds

namespace GpfBounds

open Real Finset

private theorem scalar_fiber_bound (k : ℕ) (q m p : ℝ) (hq : 1 ≤ q) (hm : 1 ≤ m)
    (hlo : q*m ≤ p) (hhi : p ≤ 2*q*m) :
    (1+log p)^k / p ≤ (4^k * (k.factorial : ℝ) * exp 1) * (1+log q)^k / q *
      m ^ ((1 / (4*(1+log q)) : ℝ)-1) := by
  have hq0 : 0 < q := by linarith
  have hm0 : 0 < m := by linarith
  have hqm : 0 < q*m := mul_pos hq0 hm0
  have hp0 := hqm.trans_le hlo
  have hp1 : 1 ≤ p := (one_le_mul_of_one_le_of_one_le hq hm).trans hlo
  let L := 1 + log q
  have hL : 0 < L := by dsimp [L]; linarith [log_nonneg hq]
  have hlogm := log_nonneg hm
  have hlogp : 1 + log p ≤ 4*L + log m := by
    have h := log_le_log hp0 hhi
    rw [log_mul (mul_pos (by norm_num) hq0).ne' hm0.ne', log_mul (by norm_num) hq0.ne'] at h
    dsimp [L]
    linarith [log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2), log_nonneg hq]
  let x := 1 + log m * (1/(4*L))
  have hx : 0 ≤ x := by dsimp [x]; positivity
  have hxmul : 4*L*x = 4*L + log m := by
    dsimp [x]
    field_simp
  have hpow := pow_le_pow_left₀ (by linarith [log_nonneg hp1] : 0 ≤ 1+log p)
      (hlogp.trans_eq hxmul.symm) k
  have hfac : 0 < (k.factorial : ℝ) := by positivity
  have hex := (div_le_iff₀ hfac).mp (Real.pow_div_factorial_le_exp x hx k)
  have hrewrite : exp x = exp 1 * m ^ (1/(4*L) : ℝ) := by
    rw [rpow_def_of_pos hm0]
    exact exp_add _ _
  rw [hrewrite] at hex
  rw [mul_pow] at hpow
  have hK : 0 ≤ (4*L)^k := by positivity
  calc
    (1+log p)^k / p ≤ ((4*L)^k * (exp 1 * m ^ (1/(4*L) : ℝ) * k.factorial)) / (q*m) :=
      div_le_div₀ (by positivity) (hpow.trans (mul_le_mul_of_nonneg_left hex hK)) hqm hlo
    _ = _ := by
      change _ = (4^k * (k.factorial : ℝ) * exp 1) * L^k / q *
        m ^ ((1/(4*L) : ℝ)-1)
      rw [rpow_sub_one hm0.ne', mul_pow]
      ring

private theorem fiber_arithmetic {p q : ℕ} (hq : 2 ≤ q) (hp : 2 < p) (he : parent p = q) :
    q * ((p-1)/q) + 1 = p ∧ (p-1)/q ∈ (q+1).smoothNumbers := by
  have hs : q ≤ (p-1).primeFactors.sup id := by rw [← he]; rfl
  obtain ⟨a, ha, hqa⟩ := (Finset.le_sup_iff (by change 0 < q; omega)).mp hs
  have haq : a ≤ q := by simpa only [← he, parent, id_eq] using
    (Finset.le_sup (f := @id ℕ) ha)
  have haq' : a = q := le_antisymm haq hqa
  have hqmem : q ∈ (p-1).primeFactors := haq' ▸ ha
  have hd := Nat.dvd_of_mem_primeFactors hqmem
  have heq := Nat.mul_div_cancel' hd
  refine ⟨by omega, Nat.mem_smoothNumbers_of_dvd ?_ (Nat.div_dvd_of_dvd hd)⟩
  apply Nat.mem_smoothNumbers'.mpr
  intro l hl hld
  have hlm : l ∈ (p-1).primeFactors := Nat.mem_primeFactors.mpr ⟨hl,hld,by omega⟩
  have hle := Finset.le_sup (f := @id ℕ) hlm
  change l ≤ parent p at hle
  omega

theorem fiber_bound (hSmooth : SmoothBound) (k : ℕ) : FiberBound k := by
  obtain ⟨D,C,hC,hS⟩ := hSmooth
  let A : ℝ := 4^k * (k.factorial : ℝ) * exp 1
  have hA : 0 ≤ A := by dsimp [A]; positivity
  refine ⟨k+D,A*C,mul_nonneg hA hC,?_⟩
  intro q hq F hF
  let m := fun p : ℕ => (p-1)/q
  have hqR : 1 ≤ (q:ℝ) := by exact_mod_cast (show 1 ≤ q by omega)
  have hq0 : 0 < (q:ℝ) := by linarith
  have haux : ∀ p ∈ F, q * m p + 1 = p ∧ m p ∈ (q+1).smoothNumbers := by
    intro p hp
    exact fiber_arithmetic hq (hF p hp).2.1 (hF p hp).2.2
  have hinj : Set.InjOn m F := by
    intro p hp r hr hpr
    have a := (haux p hp).1
    have b := (haux r hr).1
    rw [hpr] at a
    omega
  let e : ℝ := 1 / (4*(1+log q)) - 1
  let B : ℝ := A*(1+log q)^k / q
  have hB : 0 ≤ B := by dsimp [B]; positivity [log_nonneg hqR]
  have hsum := hS q hq (F.image m) (by
    intro t ht
    obtain ⟨p,hp,rfl⟩ := mem_image.mp ht
    exact (haux p hp).2)
  change ∑ t ∈ F.image m, (t:ℝ)^e ≤ _ at hsum
  calc
    ∑ p ∈ F, weight k p ≤ ∑ p ∈ F, B * (m p : ℝ)^e := by
      apply sum_le_sum
      intro p hp
      have hmp : 0 < m p := Nat.pos_of_ne_zero (Nat.ne_zero_of_mem_smoothNumbers (haux p hp).2)
      have hmR : 1 ≤ (m p : ℝ) := by exact_mod_cast hmp
      have har : (q:ℝ) * (m p:ℝ) + 1 = p := by exact_mod_cast (haux p hp).1
      refine scalar_fiber_bound k q (m p) p hqR hmR (by linarith) ?_
      nlinarith [one_le_mul_of_one_le_of_one_le hqR hmR]
    _ = B * ∑ t ∈ F.image m, (t:ℝ)^e := by rw [sum_image hinj, mul_sum]
    _ ≤ B * (C*(1+log q)^D) := mul_le_mul_of_nonneg_left hsum hB
    _ = A * C * weight (k+D) q := by unfold B weight; rw [pow_add]; ring

end GpfBounds

namespace GpfBounds

open OMA.S_oeis_a006530

private theorem parent_mem {p : ℕ} (hb : 2 < p) :
    parent p ∈ (p - 1).primeFactors := by
  have h : (p-1).primeFactors.Nonempty :=
    ⟨(p-1).minFac, Nat.mem_primeFactors.mpr
      ⟨Nat.minFac_prime (by omega), Nat.minFac_dvd _, by omega⟩⟩
  obtain ⟨q, hq, heq⟩ := Finset.exists_mem_eq_sup _ h id
  simpa [parent, heq] using hq

theorem parent_prime (_hp : p.Prime) (hb : 2 < p) : (parent p).Prime :=
  Nat.prime_of_mem_primeFactors (parent_mem hb)

private theorem parent_lt {p : ℕ} (hb : 2 < p) : parent p < p := by
  have h := Nat.le_of_dvd (show 0 < p-1 by omega) (Nat.dvd_of_mem_primeFactors (parent_mem hb))
  omega

private theorem next_parent {p : ℕ} (hb : 2 < p) :
    f 1 (-1) (p : ℤ) = (parent p : ℤ) := by
  have he : (1 : ℤ) * p + (-1) = ((p-1 : ℕ) : ℤ) := by omega
  rw [f, he]
  simp [gpf, parent, show p-1 ≠ 0 by omega, show p-1 ≠ 1 by omega]

private theorem long_orbit (d : ℕ) {p : ℕ} (hp : p.Prime) (hs : ¬ shallow d p) :
    ∃ s : Finset ℤ, s.card = d+1 ∧ (∀ x ∈ s, x ≤ (p : ℤ)) ∧
      (s : Set ℤ) ⊆ Set.range (fun k : ℕ => (f 1 (-1))^[k] (p : ℤ)) := by
  induction d generalizing p with
  | zero =>
    refine ⟨{(p : ℤ)}, by simp, ?_, ?_⟩
    · simp
    · intro x hx
      have hx' : x = (p : ℤ) := by simpa using hx
      exact ⟨0, hx'.symm⟩
  | succ d ih =>
    change ¬(p ≤ 2 ∨ shallow d (parent p)) at hs
    have hb : 2 < p := lt_of_not_ge (fun h => hs (Or.inl h))
    obtain ⟨s, hc, hle, hsub⟩ := ih (parent_prime hp hb) (fun h => hs (Or.inr h))
    have hlt : (parent p : ℤ) < (p : ℤ) := by exact_mod_cast parent_lt hb
    have hn : (p : ℤ) ∉ s := fun hm => (hlt.not_ge (hle _ hm))
    refine ⟨insert (p : ℤ) s, by simp [hn,hc], ?_, ?_⟩
    · intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · rfl
      · exact (hle _ hx).trans hlt.le
    · intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact ⟨0,rfl⟩
      · obtain ⟨k,hk⟩ := hsub hx
        refine ⟨k+1, ?_⟩
        change (f 1 (-1))^[k.succ] (p : ℤ) = x
        rw [Function.iterate_succ_apply, next_parent hb]
        exact hk

theorem universal_shallow (h : type_of% @OMA.S_oeis_a006530.main) :
    ∃ d : ℕ, ∀ p : ℕ, p.Prime → shallow d p := by
  obtain ⟨d,hd⟩ := h 1 (-1) (by decide) (by decide)
  refine ⟨d, fun p hp => ?_⟩
  by_contra hbad
  obtain ⟨s,hc,_,hsub⟩ := long_orbit d hp hbad
  obtain ⟨hfin,hbound⟩ := hd (p : ℤ)
  have hle := (Set.ncard_le_ncard hsub hfin).trans hbound
  rw [Set.ncard_coe_finset,hc] at hle
  omega

end GpfBounds

namespace GpfBounds

private theorem weight_nonneg (k p : ℕ) : 0 ≤ weight k p := by
  unfold weight
  positivity

theorem depth_bound (hfib : ∀ k, FiberBound k)
    (hprime : ∀ {p : ℕ}, p.Prime → 2 < p → (parent p).Prime)
    (d k : ℕ) : ∃ U : ℝ, ∀ F : Finset ℕ, (∀ p ∈ F, p.Prime ∧ shallow d p) →
      ∑ p ∈ F, weight k p ≤ U := by
  classical
  induction d generalizing k with
  | zero =>
    refine ⟨weight k 2, ?_⟩
    intro F hF
    have hsub : F ⊆ {2} := by
      intro p hp
      obtain ⟨hp', hs⟩ := hF p hp
      exact Finset.mem_singleton.mpr (le_antisymm hs hp'.two_le)
    calc
      _ ≤ ∑ p ∈ ({2} : Finset ℕ), weight k p :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ ↦ weight_nonneg k p)
      _ = _ := Finset.sum_singleton _ _
  | succ d ih =>
    obtain ⟨K, C, hC, hfiber⟩ := hfib k
    obtain ⟨U, hU⟩ := ih K
    refine ⟨C * U + weight k 2, ?_⟩
    intro F hF
    let A := F.erase 2
    let Q := A.image parent
    have ha : ∀ p ∈ A, p.Prime ∧ 2 < p ∧ shallow d (parent p) := by
      intro p hp
      obtain ⟨hne, hmem⟩ := Finset.mem_erase.mp hp
      obtain ⟨hpr, hs⟩ := hF p hmem
      have hbig : 2 < p := lt_of_le_of_ne hpr.two_le (Ne.symm hne)
      exact ⟨hpr, hbig, hs.resolve_left (not_le.mpr hbig)⟩
    have hq : ∀ q ∈ Q, q.Prime ∧ shallow d q := by
      intro q hmem
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hmem
      obtain ⟨hpr, hbig, hs⟩ := ha p hp
      exact ⟨hprime hpr hbig, hs⟩
    have hA : ∑ p ∈ A, weight k p ≤ C * U := calc
      _ = ∑ q ∈ Q, ∑ p ∈ A.filter (fun p ↦ parent p = q), weight k p :=
        (Finset.sum_fiberwise_of_maps_to (fun p hp ↦ Finset.mem_image_of_mem parent hp)
          (weight k)).symm
      _ ≤ ∑ q ∈ Q, C * weight K q := by
        apply Finset.sum_le_sum
        intro q hmem
        apply hfiber q (hq q hmem).1.two_le
        intro p hp
        obtain ⟨hp', heq⟩ := Finset.mem_filter.mp hp
        exact ⟨(ha p hp').1, (ha p hp').2.1, heq⟩
      _ = C * ∑ q ∈ Q, weight K q := (Finset.mul_sum ..).symm
      _ ≤ C * U := mul_le_mul_of_nonneg_left (hU Q hq) hC
    by_cases hh : 2 ∈ F
    · rw [← Finset.sum_erase_add _ _ hh]
      exact add_le_add hA le_rfl
    · have hAF : A = F := Finset.erase_eq_of_notMem hh
      rw [hAF] at hA
      linarith [weight_nonneg k 2]

end GpfBounds

namespace GpfBounds

theorem no_uniform
    (hd : ∀ d k : ℕ, ∃ U : ℝ, ∀ F : Finset ℕ,
      (∀ p ∈ F, p.Prime ∧ shallow d p) → ∑ p ∈ F, weight k p ≤ U)
    (h : ∃ d, ∀ p : ℕ, p.Prime → shallow d p) : False := by
  obtain ⟨d,hsh⟩ := h
  obtain ⟨U,hU⟩ := hd d 0
  apply Nat.Primes.not_summable_one_div
  apply summable_of_sum_le (c := U) (fun p => by positivity)
  intro s
  let e : Nat.Primes ↪ ℕ := Function.Embedding.subtype _
  have hmem (p) (hp : p ∈ s.map e) : p.Prime ∧ shallow d p := by
    obtain ⟨q,_,rfl⟩ := Finset.mem_map.mp hp
    exact ⟨q.property, hsh _ q.property⟩
  have hm := (Finset.sum_map s e (weight 0)).symm.le.trans (hU _ hmem)
  have he (p : Nat.Primes) : weight 0 (e p) = (1 / p : ℝ) := by
    change (1 + Real.log (p : ℕ))^0 / (p : ℕ) = _
    rw [pow_zero]
  simpa only [he] using hm

end GpfBounds

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a006530.main) := by
  intro h
  apply GpfBounds.no_uniform _ (GpfBounds.universal_shallow h)
  exact GpfBounds.depth_bound (GpfBounds.fiber_bound GpfBounds.smooth_bound)
    (fun hp hb ↦ GpfBounds.parent_prime hp hb)
