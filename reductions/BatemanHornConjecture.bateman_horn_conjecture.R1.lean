import FormalConjectures.Wikipedia.BatemanHornConjecture

-- Reduction BatemanHornConjecture.bateman_horn_conjecture.R1 of the Bateman-Horn conjecture
-- Credit: @swaymun
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# Bateman-Horn: everything that is known, proved from two classical theorems, and the open rest

The Bateman-Horn conjecture asserts two things about an admissible set of polynomials: the
Euler product defining the constant converges to a positive limit, and the number of `n ≤ x` at
which all the polynomials are prime is asymptotic to the main term built from that limit.

This file proves the following from the hypotheses below.

* The convergence of the constant to a positive limit, for every admissible set. For sets of
  linear polynomials (the Hardy-Littlewood and Dickson setting, twin primes included) this is
  proved outright; a polynomial of degree at least two enters only through `H2`.
* The whole conjecture for a single linear polynomial `a X + b`, the only case that is a
  theorem. The partial products are eventually equal to `a / φ(a)` and the count is asymptotic to
  `a / φ(a) * x / log x`.

The hypotheses:

* `H1` (de la Vallee Poussin 1896): the prime number theorem in arithmetic progressions,
  `π(x; q, a) ~ x / (φ(q) log x)` for `gcd(a, q) = 1`. Not in Mathlib at this version.
* `H2` (Landau 1903): for one irreducible `f` of degree at least two, with `ω_f(p)` the number
  of roots of `f` modulo `p`, the series `∑ (ω_f(p) - 1) / p` over the primes in increasing
  order converges. This is Mertens' theorem for the number field `ℚ[x]/(f)` against Mertens'
  theorem for `ℚ`; it follows from the prime ideal theorem.
* `H3`: for every admissible set other than a single linear polynomial, the count is asymptotic
  to the main term built from the limit of the partial products. This is the open part. It
  contains the twin prime asymptotic and the asymptotic for `n^2 + 1`; no instance is known.
-/

namespace OMA.R_BatemanHornConjecture_bateman_horn_conjecture_R1

open Polynomial Asymptotics Filter Topology BatemanHornConjecture

/-- The prime number theorem in arithmetic progressions. -/
def H1 : Prop :=
  ∀ q a : ℕ, 0 < q → a.Coprime q →
    (fun x : ℝ => (((Finset.range (⌊x⌋₊ + 1)).filter
      (fun p : ℕ => p.Prime ∧ p ≡ a [MOD q])).card : ℝ))
      ~[atTop] (fun x : ℝ => x / ((q.totient : ℝ) * Real.log x))

/-- Mertens' theorem for the number field of one irreducible polynomial of degree at least two,
in root-counting form: the series of `(ω_f(p) - 1) / p` over the primes converges. -/
def H2 : Prop :=
  ∀ f : ℤ[X], BunyakovskyCondition f → 2 ≤ f.natDegree →
    ∃ c : ℝ, Tendsto (fun N : ℕ => ∑ p ∈ Nat.primesBelow N, ((OmegaP {f} p : ℝ) - 1) / p)
      atTop (𝓝 c)

/-- The open part: the asymptotic count, away from the single linear case, given the constant. -/
def H3 : Prop :=
  ∀ polys : Finset ℤ[X], polys.Nonempty → (∀ f ∈ polys, BunyakovskyCondition f) →
    SchinzelCondition polys → ¬ (∃ f : ℤ[X], polys = {f} ∧ f.natDegree = 1) →
    ∀ C : ℝ, 0 < C → Tendsto (BatemanHornPartialProduct polys) atTop (𝓝 C) →
      (fun x : ℝ => (CountSimultaneousPrimes polys x : ℝ)) ~[atTop]
        (fun x : ℝ => C / DegreesProduct polys * x / (Real.log x) ^ polys.card)

-- The shape of a linear polynomial

lemma eval_linear {f : ℤ[X]} (hdeg : f.natDegree = 1) (n : ℤ) :
    f.eval n = f.coeff 1 * n + f.coeff 0 := by
  conv_lhs => rw [eq_X_add_C_of_natDegree_le_one hdeg.le]
  simp

lemma coeff_one_pos {f : ℤ[X]} (hdeg : f.natDegree = 1) (hlead : 0 < f.leadingCoeff) :
    0 < f.coeff 1 := by
  rwa [leadingCoeff, hdeg] at hlead

lemma coprime_coeffs {f : ℤ[X]} (hdeg : f.natDegree = 1) (hirr : Irreducible f) :
    IsCoprime (f.coeff 1) (f.coeff 0) := by
  have hprim := hirr.isPrimitive (by omega)
  rw [Int.isCoprime_iff_gcd_eq_one]
  have hd : C ((Int.gcd (f.coeff 1) (f.coeff 0) : ℕ) : ℤ) ∣ f := by
    rw [C_dvd_iff_dvd_coeff]
    intro i
    rcases i with _ | _ | i
    · exact Int.gcd_dvd_right _ _
    · exact Int.gcd_dvd_left _ _
    · rw [coeff_eq_zero_of_natDegree_lt (show f.natDegree < i + 1 + 1 by omega)]
      exact dvd_zero _
  have hu := hprim _ hd
  rw [Int.isUnit_iff_natAbs_eq] at hu
  simpa using hu

-- The local factors and the constant

lemma omega_linear {f : ℤ[X]} (hdeg : f.natDegree = 1) (hirr : Irreducible f) (p : ℕ)
    (hp : p.Prime) : OmegaP {f} p = if (p : ℤ) ∣ f.coeff 1 then 0 else 1 := by
  have := Fact.mk hp
  have hset : {n : ZMod p | ∃ g ∈ ({f} : Finset ℤ[X]),
      (g.map (Int.castRingHom (ZMod p))).eval n = 0}
      = {n : ZMod p | ((f.coeff 1 : ℤ) : ZMod p) * n + ((f.coeff 0 : ℤ) : ZMod p) = 0} := by
    ext n
    simp only [Finset.mem_singleton, exists_eq_left, Set.mem_ofPred_eq]
    conv_lhs => rw [eq_X_add_C_of_natDegree_le_one hdeg.le]
    simp
  unfold OmegaP
  rw [hset]
  split_ifs with hdvd
  · have ha0 : ((f.coeff 1 : ℤ) : ZMod p) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 hdvd
    have hb0 : ((f.coeff 0 : ℤ) : ZMod p) ≠ 0 := by
      intro hb
      have hdvd' := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 hb
      have hu := (coprime_coeffs hdeg hirr).isUnit_of_dvd' hdvd hdvd'
      rw [Int.isUnit_iff_natAbs_eq, Int.natAbs_natCast] at hu
      exact hp.one_lt.ne' hu
    simp [ha0, hb0]
  · have ha0 : ((f.coeff 1 : ℤ) : ZMod p) ≠ 0 := fun h =>
      hdvd ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 h)
    have hsing : {n : ZMod p | ((f.coeff 1 : ℤ) : ZMod p) * n + ((f.coeff 0 : ℤ) : ZMod p) = 0}
        = {-((f.coeff 0 : ℤ) : ZMod p) / ((f.coeff 1 : ℤ) : ZMod p)} := by
      ext n
      simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
      constructor
      · intro h
        field_simp
        linear_combination h
      · intro h
        rw [h]
        field_simp
        ring
    rw [hsing, Set.ncard_singleton]

lemma primesBelow_filter_dvd {A N : ℕ} (hA : 0 < A) (hN : A < N) :
    (Nat.primesBelow N).filter (fun p => p ∣ A) = A.primeFactors := by
  ext p
  simp only [Finset.mem_filter, Nat.mem_primesBelow, Nat.mem_primeFactors]
  constructor
  · rintro ⟨⟨_, hp⟩, hd⟩
    exact ⟨hp, hd, hA.ne'⟩
  · rintro ⟨hp, hd, _⟩
    exact ⟨⟨lt_of_le_of_lt (Nat.le_of_dvd hA hd) hN, hp⟩, hd⟩

lemma partialProduct_linear {f : ℤ[X]} (hdeg : f.natDegree = 1) (hirr : Irreducible f)
    (hlead : 0 < f.leadingCoeff) (N : ℕ) (hN : (f.coeff 1).natAbs < N) :
    BatemanHornPartialProduct {f} N
      = ((f.coeff 1).natAbs : ℝ) / ((f.coeff 1).natAbs.totient : ℝ) := by
  have hApos : 0 < (f.coeff 1).natAbs := Int.natAbs_pos.2 (coeff_one_pos hdeg hlead).ne'
  have hfac : ∀ p ∈ Nat.primesBelow N,
      (1 - (1 : ℝ) / p) ^ (-(({f} : Finset ℤ[X]).card : ℤ)) * (1 - (OmegaP {f} p : ℝ) / p)
        = if p ∣ (f.coeff 1).natAbs then (1 - (p : ℝ)⁻¹)⁻¹ else 1 := by
    intro p hp
    have hpp := (Nat.mem_primesBelow.1 hp).2
    rw [omega_linear hdeg hirr p hpp]
    have hiff : (p : ℤ) ∣ f.coeff 1 ↔ p ∣ (f.coeff 1).natAbs := Int.natCast_dvd
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hpp.two_le
    have hinv : (p : ℝ)⁻¹ ≤ 2⁻¹ := inv_anti₀ (by norm_num) hp2
    have hne : (1 - (p : ℝ)⁻¹) ≠ 0 := by
      have : (2 : ℝ)⁻¹ < 1 := by norm_num
      linarith
    simp only [Finset.card_singleton, Nat.cast_one, zpow_neg, zpow_one, one_div, hiff]
    split_ifs
    · simp
    · simp [hne]
  unfold BatemanHornPartialProduct
  rw [Finset.prod_congr rfl hfac, ← Finset.prod_filter]
  rw [primesBelow_filter_dvd hApos hN, Finset.prod_inv_distrib]
  have htot := congrArg (fun q : ℚ => (q : ℝ))
    (Nat.totient_eq_mul_prod_factors (f.coeff 1).natAbs)
  simp only [Rat.cast_natCast, Rat.cast_mul, Rat.cast_prod, Rat.cast_sub, Rat.cast_one,
    Rat.cast_inv] at htot
  have hA0 : ((f.coeff 1).natAbs : ℝ) ≠ 0 := by exact_mod_cast hApos.ne'
  rw [htot, ← div_div, div_self hA0, one_div]

-- Counting: values of `a n + b` against primes in the progression `b mod a`

lemma count_le_progression (a b : ℤ) (ha : 0 < a) (x : ℝ) (hx : 0 ≤ x) :
    ((Finset.range (⌊x⌋₊ + 1)).filter (fun n : ℕ => (a * n + b).natAbs.Prime)).card
      ≤ ((Finset.range (⌊(a : ℝ) * x + b⌋₊ + 1)).filter
          (fun p : ℕ => p.Prime ∧ p ≡ (b % a).toNat [MOD a.natAbs])).card + (b.natAbs + 1) := by
  refine (Finset.card_le_card_sdiff_add_card (t := Finset.range (b.natAbs + 1))).trans ?_
  rw [Finset.card_range]
  refine Nat.add_le_add_right ?_ _
  have hpos : ∀ n : ℕ, b.natAbs + 1 ≤ n → 0 < a * n + b := by
    intro n hn
    have h1 : (n : ℤ) ≤ a * n := le_mul_of_one_le_left (Int.natCast_nonneg n) ha
    omega
  refine Finset.card_le_card_of_injOn (fun n : ℕ => (a * n + b).natAbs) ?_ ?_
  · intro n hn
    simp only [Finset.coe_sdiff, Finset.coe_filter, Finset.mem_range, Finset.coe_range,
      Set.mem_sdiff, Set.mem_ofPred_eq, Set.mem_Iio, not_lt] at hn
    obtain ⟨⟨hnx, hprime⟩, hnK⟩ := hn
    have hp := hpos n hnK
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq]
    refine ⟨Nat.lt_succ_of_le (Nat.le_floor ?_), hprime, ?_⟩
    · have hcast : (((a * n + b).natAbs : ℕ) : ℝ) = (a : ℝ) * n + b := by
        rw [← Int.cast_natCast (R := ℝ), Int.natAbs_of_nonneg hp.le]
        push_cast
        ring
      rw [hcast]
      have hnx' : (n : ℝ) ≤ x :=
        le_trans (by exact_mod_cast Nat.lt_succ_iff.1 hnx) (Nat.floor_le hx)
      have ha' : (0 : ℝ) ≤ a := by exact_mod_cast ha.le
      nlinarith
    · rw [← Int.natCast_modEq_iff, Int.natAbs_of_nonneg hp.le,
        Int.toNat_of_nonneg (Int.emod_nonneg b ha.ne'), Int.natAbs_of_nonneg ha.le,
        Int.modEq_iff_dvd]
      exact ⟨-(b / a) - n, by rw [Int.emod_def]; ring⟩
  · intro n hn m hm hnm
    simp only [Finset.coe_sdiff, Finset.coe_filter, Finset.mem_range, Finset.coe_range,
      Set.mem_sdiff, Set.mem_ofPred_eq, Set.mem_Iio, not_lt] at hn hm
    have hpn := hpos n hn.2
    have hpm := hpos m hm.2
    have h : a * n + b = a * m + b := by
      have := congrArg (fun k : ℕ => (k : ℤ)) hnm
      simpa [Int.natAbs_of_nonneg hpn.le, Int.natAbs_of_nonneg hpm.le] using this
    have h' : a * (n : ℤ) = a * m := by linarith
    exact_mod_cast mul_left_cancel₀ ha.ne' h'

lemma progression_le_count (a b : ℤ) (ha : 0 < a) (x : ℝ) :
    ((Finset.range (⌊(a : ℝ) * x + b⌋₊ + 1)).filter
        (fun p : ℕ => p.Prime ∧ p ≡ (b % a).toNat [MOD a.natAbs])).card
      ≤ ((Finset.range (⌊x⌋₊ + 1)).filter (fun n : ℕ => (a * n + b).natAbs.Prime)).card
        + (b.natAbs + 1) := by
  refine (Finset.card_le_card_sdiff_add_card (t := Finset.range (b.natAbs + 1))).trans ?_
  rw [Finset.card_range]
  refine Nat.add_le_add_right ?_ _
  refine le_trans (Finset.card_le_card ?_)
    (Finset.card_image_le (f := fun n : ℕ => (a * n + b).natAbs))
  intro p hp
  simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_range, not_lt] at hp
  obtain ⟨⟨hpy, hprime, hmod⟩, hpK⟩ := hp
  rw [← Int.natCast_modEq_iff, Int.toNat_of_nonneg (Int.emod_nonneg b ha.ne'),
    Int.natAbs_of_nonneg ha.le] at hmod
  have hmod' : b ≡ (p : ℤ) [ZMOD a] := ((hmod.trans (Int.mod_modEq b a)).symm)
  obtain ⟨c, hc⟩ := (Int.modEq_iff_dvd.1 hmod')
  have hcpos : 0 < c := by
    have h1 : 0 < a * c := by omega
    by_contra h
    push Not at h
    nlinarith
  have hcn : ((c.toNat : ℕ) : ℤ) = c := Int.toNat_of_nonneg hcpos.le
  have hval : a * c + b = (p : ℤ) := by omega
  rw [Finset.mem_image]
  refine ⟨c.toNat, ?_, ?_⟩
  · rw [Finset.mem_filter, Finset.mem_range]
    refine ⟨Nat.lt_succ_of_le (Nat.le_floor ?_), ?_⟩
    · have hp0 : p ≠ 0 := by omega
      have hpy' : (p : ℝ) ≤ (a : ℝ) * x + b := (Nat.le_floor_iff' hp0).1 (Nat.lt_succ_iff.1 hpy)
      have hpc : (p : ℝ) = (a : ℝ) * c + b := by exact_mod_cast hval.symm
      have ha' : (0 : ℝ) < a := by exact_mod_cast ha
      have hcx : (c : ℝ) ≤ x := le_of_mul_le_mul_left (by linarith) ha'
      have hcc : ((c.toNat : ℕ) : ℝ) = (c : ℝ) := by
        rw [← Int.cast_natCast (R := ℝ), hcn]
      rw [hcc]
      exact hcx
    · rw [hcn, hval, Int.natAbs_natCast]
      exact hprime
  · show (a * ((c.toNat : ℕ) : ℤ) + b).natAbs = p
    rw [hcn, hval, Int.natAbs_natCast]

-- Asymptotics

lemma one_isLittleO_div_log :
    (fun _ : ℝ => (1 : ℝ)) =o[atTop] (fun x : ℝ => x / Real.log x) := by
  have h := Real.isLittleO_log_id_atTop.mul_isBigO
    (isBigO_refl (fun x : ℝ => (Real.log x)⁻¹) atTop)
  refine h.congr' ?_ ?_
  · filter_upwards [eventually_gt_atTop 1] with x hx
    exact mul_inv_cancel₀ (Real.log_pos hx).ne'
  · exact Eventually.of_forall (fun x => by simp [div_eq_mul_inv])

lemma log_affine_equiv (a b : ℝ) (ha : 0 < a) :
    (fun x : ℝ => Real.log (a * x + b)) ~[atTop] Real.log := by
  have hlim : Tendsto (fun x : ℝ => Real.log (a + b / x)) atTop (𝓝 (Real.log a)) := by
    have h1 : Tendsto (fun x : ℝ => a + b / x) atTop (𝓝 (a + 0)) :=
      tendsto_const_nhds.add (tendsto_const_nhds.div_atTop tendsto_id)
    rw [add_zero] at h1
    exact (Real.continuousAt_log ha.ne').tendsto.comp h1
  have hO : (fun x : ℝ => Real.log (a + b / x)) =O[atTop] (fun _ : ℝ => (1 : ℝ)) :=
    hlim.isBigO_one ℝ
  have ho : (fun x : ℝ => Real.log (a + b / x)) =o[atTop] Real.log :=
    hO.trans_isLittleO Real.isLittleO_const_log_atTop
  have hL : Tendsto (fun x : ℝ => a * x + b) atTop atTop :=
    tendsto_atTop_add_const_right _ _ (tendsto_id.const_mul_atTop ha)
  show ((fun x : ℝ => Real.log (a * x + b)) - Real.log) =o[atTop] Real.log
  refine ho.congr' ?_ EventuallyEq.rfl
  filter_upwards [eventually_gt_atTop 0, hL.eventually_gt_atTop 0] with x hx hLx
  simp only [Pi.sub_apply]
  rw [← Real.log_div hLx.ne' hx.ne']
  congr 1
  field_simp

lemma main_term_equiv (a b t : ℝ) (ha : 0 < a) :
    (fun x : ℝ => (a * x + b) / (t * Real.log (a * x + b)))
      ~[atTop] (fun x : ℝ => a / t * x / Real.log x) := by
  have hnum : (fun x : ℝ => a * x + b) ~[atTop] (fun x : ℝ => a * x) := by
    have hb : (fun _ : ℝ => b) =o[atTop] (fun x : ℝ => a * x) :=
      (isLittleO_const_id_atTop b).trans_isBigO (isBigO_self_const_mul ha.ne' id atTop)
    exact IsEquivalent.refl.add_isLittleO hb
  have hden : (fun x : ℝ => t * Real.log (a * x + b)) ~[atTop] (fun x : ℝ => t * Real.log x) :=
    (IsEquivalent.refl (u := fun _ : ℝ => t)).mul (log_affine_equiv a b ha)
  refine (hnum.div hden).congr_right (Eventually.of_forall (fun x => ?_))
  simp only [Pi.div_apply]
  ring

-- The single linear case of Bateman-Horn from the prime number theorem in progressions

lemma linear_asymp (h1 : H1) (a b : ℤ) (ha : 0 < a) (hcop : IsCoprime a b) :
    (fun x : ℝ => (((Finset.range (⌊x⌋₊ + 1)).filter
        (fun n : ℕ => (a * n + b).natAbs.Prime)).card : ℝ))
      ~[atTop] (fun x : ℝ => (a.natAbs : ℝ) / (a.natAbs.totient : ℝ) * x / Real.log x) := by
  have hApos : 0 < a.natAbs := Int.natAbs_pos.2 ha.ne'
  have hr : 0 ≤ b % a := Int.emod_nonneg b ha.ne'
  have hcopr : Nat.Coprime (b % a).toNat a.natAbs := by
    rw [← Nat.isCoprime_iff_coprime, Int.toNat_of_nonneg hr, Int.natAbs_of_nonneg ha.le]
    have h := hcop.symm.add_mul_left_left (-(b / a))
    have e : b + a * -(b / a) = b % a := by
      rw [Int.emod_def]
      ring
    rwa [e] at h
  have hP := h1 a.natAbs (b % a).toNat hApos hcopr
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  have hL : Tendsto (fun x : ℝ => (a : ℝ) * x + b) atTop atTop :=
    tendsto_atTop_add_const_right _ _ (tendsto_id.const_mul_atTop ha')
  have hPL := (hP.comp_tendsto hL).trans
    (main_term_equiv (a : ℝ) (b : ℝ) (a.natAbs.totient : ℝ) ha')
  have hcast : ((a.natAbs : ℕ) : ℝ) = (a : ℝ) := by
    rw [← Int.cast_natCast (R := ℝ), Int.natAbs_of_nonneg ha.le]
  rw [hcast]
  have hE : (fun x : ℝ => (((Finset.range (⌊x⌋₊ + 1)).filter
        (fun n : ℕ => (a * n + b).natAbs.Prime)).card : ℝ)
      - (((Finset.range (⌊(a : ℝ) * x + b⌋₊ + 1)).filter
          (fun p : ℕ => p.Prime ∧ p ≡ (b % a).toNat [MOD a.natAbs])).card : ℝ))
      =O[atTop] (fun _ : ℝ => (1 : ℝ)) := by
    refine IsBigO.of_bound ((b.natAbs : ℝ) + 1) ?_
    filter_upwards [eventually_ge_atTop 0] with x hx
    have h1 := (Nat.cast_le (α := ℝ)).2 (count_le_progression a b ha x hx)
    have h2 := (Nat.cast_le (α := ℝ)).2 (progression_le_count a b ha x)
    push_cast at h1 h2
    rw [Real.norm_eq_abs, norm_one, mul_one, abs_le]
    constructor <;> linarith
  have hg : (fun _ : ℝ => (1 : ℝ)) =o[atTop]
      (fun x : ℝ => (a : ℝ) / (a.natAbs.totient : ℝ) * x / Real.log x) := by
    have hc : (a : ℝ) / (a.natAbs.totient : ℝ) ≠ 0 :=
      div_ne_zero ha'.ne' (by exact_mod_cast (Nat.totient_pos.2 hApos).ne')
    refine (one_isLittleO_div_log.const_mul_right hc).congr_right (fun x => ?_)
    ring
  refine (hPL.add_isLittleO (hE.trans_isLittleO hg)).congr_left (Eventually.of_forall (fun x => ?_))
  simp only [Pi.add_apply, Function.comp_apply]
  ring

lemma linear_case (h1 : H1) (f : ℤ[X]) (hdeg : f.natDegree = 1) (hirr : Irreducible f)
    (hlead : 0 < f.leadingCoeff) :
    ∃ C : ℝ, 0 < C ∧ Tendsto (BatemanHornPartialProduct {f}) atTop (𝓝 C) ∧
      (fun x : ℝ => (CountSimultaneousPrimes {f} x : ℝ)) ~[atTop]
        (fun x : ℝ => C / DegreesProduct {f} * x / (Real.log x) ^ ({f} : Finset ℤ[X]).card) := by
  have ha := coeff_one_pos hdeg hlead
  have hApos : 0 < (f.coeff 1).natAbs := Int.natAbs_pos.2 ha.ne'
  refine ⟨((f.coeff 1).natAbs : ℝ) / ((f.coeff 1).natAbs.totient : ℝ), ?_, ?_, ?_⟩
  · exact div_pos (by exact_mod_cast hApos) (by exact_mod_cast Nat.totient_pos.2 hApos)
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop (f.coeff 1).natAbs] with N hN
    exact (partialProduct_linear hdeg hirr hlead N hN).symm
  · have h := linear_asymp h1 (f.coeff 1) (f.coeff 0) ha (coprime_coeffs hdeg hirr)
    have hcount : ∀ x : ℝ, CountSimultaneousPrimes {f} x
        = ((Finset.range (⌊x⌋₊ + 1)).filter
            (fun n : ℕ => (f.coeff 1 * n + f.coeff 0).natAbs.Prime)).card := by
      intro x
      unfold CountSimultaneousPrimes
      congr 1
      refine Finset.filter_congr (fun n _ => ?_)
      simp [eval_linear hdeg]
    simp only [hcount]
    simpa [DegreesProduct, hdeg] using h

lemma natDegree_pos_of_bunyakovsky {f : ℤ[X]} (h : BunyakovskyCondition f) : 0 < f.natDegree :=
  natDegree_pos_iff_degree_pos.2 (lt_of_lt_of_le (by norm_num) h.1)

-- From a convergent series to a convergent Euler product

lemma prod_tendsto_of_log_close (F s : ℕ → ℝ) (hF : ∀ n, 0 < F n) (c K : ℝ)
    (hs : Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, s n) atTop (𝓝 c))
    (hclose : ∀ᶠ n : ℕ in atTop, |Real.log (F n) - s n| ≤ K / (n : ℝ) ^ 2) :
    ∃ C : ℝ, 0 < C ∧ Tendsto (fun N : ℕ => ∏ n ∈ Finset.range N, F n) atTop (𝓝 C) := by
  have hsum : Summable (fun n : ℕ => Real.log (F n) - s n) := by
    refine Summable.of_norm_bounded_eventually_nat (g := fun n : ℕ => K * (1 / (n : ℝ) ^ 2)) ?_ ?_
    · exact (Real.summable_one_div_nat_pow.2 (by norm_num)).mul_left K
    · filter_upwards [hclose] with n hn
      rw [Real.norm_eq_abs]
      calc |Real.log (F n) - s n| ≤ K / (n : ℝ) ^ 2 := hn
        _ = K * (1 / (n : ℝ) ^ 2) := by ring
  have hE := hsum.hasSum.tendsto_sum_nat
  have hlog : Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, Real.log (F n)) atTop
      (𝓝 (c + ∑' n, (Real.log (F n) - s n))) := by
    refine (hs.add hE).congr (fun N => ?_)
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun n _ => by ring)
  refine ⟨Real.exp (c + ∑' n, (Real.log (F n) - s n)), Real.exp_pos _, ?_⟩
  refine ((Real.continuous_exp.tendsto _).comp hlog).congr (fun N => ?_)
  simp only [Function.comp_apply]
  rw [Real.exp_sum]
  exact Finset.prod_congr rfl (fun n _ => Real.exp_log (hF n))

lemma abs_log_one_sub_add_le (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1 / 2) :
    |Real.log (1 - t) + t| ≤ 2 * t ^ 2 := by
  have h := Real.abs_log_sub_add_sum_range_le (x := t) (by rw [abs_of_nonneg h0]; linarith) 1
  have h' : |t + Real.log (1 - t)| ≤ t ^ 2 / (1 - t) := by
    simpa [abs_of_nonneg h0] using h
  have h2 : t ^ 2 / (1 - t) ≤ 2 * t ^ 2 := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith [sq_nonneg t]
  rw [add_comm]
  exact h'.trans h2

lemma euler_product_converges (k D : ℕ) (w : ℕ → ℕ) (s : ℕ → ℝ) (c : ℝ)
    (hw_lt : ∀ p : ℕ, p.Prime → w p < p) (hw_le : ∀ p : ℕ, p.Prime → w p ≤ D)
    (hs : Tendsto (fun N : ℕ => ∑ p ∈ Nat.primesBelow N, s p) atTop (𝓝 c))
    (hsw : ∀ᶠ p : ℕ in atTop, p.Prime → s p = ((k : ℝ) - w p) / p) :
    ∃ C : ℝ, 0 < C ∧ Tendsto (fun N : ℕ => ∏ p ∈ Nat.primesBelow N,
      (1 - (1 : ℝ) / p) ^ (-(k : ℤ)) * (1 - (w p : ℝ) / p)) atTop (𝓝 C) := by
  have hpos1 : ∀ p : ℕ, p.Prime → 0 < 1 - (1 : ℝ) / p := by
    intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    have : (1 : ℝ) / p ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hp2
    linarith
  have hpos2 : ∀ p : ℕ, p.Prime → 0 < 1 - (w p : ℝ) / p := by
    intro p hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
    have : (w p : ℝ) < p := by exact_mod_cast hw_lt p hp
    rw [sub_pos, div_lt_one hp0]
    exact this
  obtain ⟨C, hC, hT⟩ := prod_tendsto_of_log_close
    (fun n : ℕ => if n.Prime then (1 - (1 : ℝ) / n) ^ (-(k : ℤ)) * (1 - (w n : ℝ) / n) else 1)
    (fun n : ℕ => if n.Prime then s n else 0)
    (fun n => by
      split_ifs with hn
      · exact mul_pos (zpow_pos (hpos1 n hn) _) (hpos2 n hn)
      · exact one_pos)
    c (2 * k + 2 * (D : ℝ) ^ 2)
    (by
      refine hs.congr (fun N => ?_)
      unfold Nat.primesBelow
      rw [Finset.sum_filter])
    (by
      filter_upwards [hsw, eventually_ge_atTop (2 * D + 2)] with n hn hnD
      have hn0 : (0 : ℝ) < n := by
        have : 0 < n := by omega
        exact_mod_cast this
      split_ifs with hp
      · have h1 := hpos1 n hp
        have h2 := hpos2 n hp
        have ht1 : (1 : ℝ) / n ≤ 1 / 2 := by
          have hp2 : (2 : ℝ) ≤ n := by exact_mod_cast hp.two_le
          exact one_div_le_one_div_of_le (by norm_num) hp2
        have hwD : (w n : ℝ) ≤ D := by exact_mod_cast hw_le n hp
        have hDn : 2 * (D : ℝ) ≤ n := by
          have : 2 * D ≤ n := by omega
          exact_mod_cast this
        have ht2 : (w n : ℝ) / n ≤ 1 / 2 := by
          rw [div_le_iff₀ hn0]
          linarith
        have hlog : Real.log ((1 - (1 : ℝ) / n) ^ (-(k : ℤ)) * (1 - (w n : ℝ) / n))
            = -(k : ℝ) * Real.log (1 - (1 : ℝ) / n) + Real.log (1 - (w n : ℝ) / n) := by
          rw [Real.log_mul (zpow_ne_zero _ h1.ne') h2.ne', Real.log_zpow]
          push_cast
          ring
        have e1 := abs_log_one_sub_add_le ((1 : ℝ) / n) (by positivity) ht1
        have e2 := abs_log_one_sub_add_le ((w n : ℝ) / n) (by positivity) ht2
        rw [hn hp, hlog]
        have hrew : -(k : ℝ) * Real.log (1 - (1 : ℝ) / n) + Real.log (1 - (w n : ℝ) / n)
            - ((k : ℝ) - w n) / n
            = -(k : ℝ) * (Real.log (1 - (1 : ℝ) / n) + 1 / n)
              + (Real.log (1 - (w n : ℝ) / n) + (w n : ℝ) / n) := by ring
        rw [hrew]
        have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
        have hw2 : ((w n : ℝ) / n) ^ 2 ≤ (D : ℝ) ^ 2 / (n : ℝ) ^ 2 := by
          rw [div_pow]
          gcongr
        calc |-(k : ℝ) * (Real.log (1 - (1 : ℝ) / n) + 1 / n)
              + (Real.log (1 - (w n : ℝ) / n) + (w n : ℝ) / n)|
            ≤ |-(k : ℝ) * (Real.log (1 - (1 : ℝ) / n) + 1 / n)|
              + |Real.log (1 - (w n : ℝ) / n) + (w n : ℝ) / n| := abs_add_le _ _
          _ = (k : ℝ) * |Real.log (1 - (1 : ℝ) / n) + 1 / n|
              + |Real.log (1 - (w n : ℝ) / n) + (w n : ℝ) / n| := by
            rw [abs_mul, abs_neg, abs_of_nonneg hk0]
          _ ≤ (k : ℝ) * (2 * ((1 : ℝ) / n) ^ 2) + 2 * ((D : ℝ) ^ 2 / (n : ℝ) ^ 2) := by
            have := mul_le_mul_of_nonneg_left e1 hk0
            linarith
          _ = (2 * k + 2 * (D : ℝ) ^ 2) / (n : ℝ) ^ 2 := by
            field_simp
      · simp only [Real.log_one, sub_self, abs_zero]
        positivity)
  refine ⟨C, hC, hT.congr (fun N => ?_)⟩
  unfold Nat.primesBelow
  rw [Finset.prod_filter]

-- Root counts modulo a prime

lemma map_ne_zero_of_irreducible {f : ℤ[X]} (hirr : Irreducible f) (hdeg : f.natDegree ≠ 0)
    (p : ℕ) (hp : p.Prime) : f.map (Int.castRingHom (ZMod p)) ≠ 0 := by
  intro h
  have hd : C (p : ℤ) ∣ f := by
    rw [C_dvd_iff_dvd_coeff]
    intro i
    have hi := congrArg (fun q : (ZMod p)[X] => q.coeff i) h
    simp only [coeff_map, coeff_zero] at hi
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 (by simpa using hi)
  have hu := hirr.isPrimitive hdeg _ hd
  rw [Int.isUnit_iff_natAbs_eq, Int.natAbs_natCast] at hu
  exact hp.one_lt.ne' hu

lemma omega_eq_card_biUnion (polys : Finset ℤ[X]) (p : ℕ) [Fact p.Prime]
    (hmap : ∀ f ∈ polys, f.map (Int.castRingHom (ZMod p)) ≠ 0) :
    OmegaP polys p
      = (polys.biUnion (fun f => (f.map (Int.castRingHom (ZMod p))).roots.toFinset)).card := by
  unfold OmegaP
  rw [← Set.ncard_coe_finset]
  congr 1
  ext n
  simp only [Set.mem_ofPred_eq, Finset.coe_biUnion, Finset.mem_coe, Set.mem_iUnion,
    Multiset.mem_toFinset, exists_prop]
  constructor
  · rintro ⟨f, hf, h⟩
    exact ⟨f, hf, (mem_roots (hmap f hf)).2 h⟩
  · rintro ⟨f, hf, h⟩
    exact ⟨f, hf, (mem_roots (hmap f hf)).1 h⟩

lemma omega_le_sum_natDegree (polys : Finset ℤ[X]) (hb : ∀ f ∈ polys, BunyakovskyCondition f)
    (p : ℕ) (hp : p.Prime) : OmegaP polys p ≤ ∑ f ∈ polys, f.natDegree := by
  have := Fact.mk hp
  rw [omega_eq_card_biUnion polys p (fun f hf => map_ne_zero_of_irreducible (hb f hf).2.1
    (natDegree_pos_of_bunyakovsky (hb f hf)).ne' p hp)]
  refine Finset.card_biUnion_le.trans (Finset.sum_le_sum (fun f _ => ?_))
  exact (Multiset.toFinset_card_le _).trans ((card_roots' _).trans natDegree_map_le)

lemma omega_eq_sum_of_disjoint (polys : Finset ℤ[X]) (p : ℕ) [Fact p.Prime]
    (hmap : ∀ f ∈ polys, f.map (Int.castRingHom (ZMod p)) ≠ 0)
    (hdisj : ∀ f ∈ polys, ∀ g ∈ polys, f ≠ g → ∀ n : ZMod p,
      ¬ ((f.map (Int.castRingHom (ZMod p))).eval n = 0
        ∧ (g.map (Int.castRingHom (ZMod p))).eval n = 0)) :
    OmegaP polys p = ∑ f ∈ polys, OmegaP {f} p := by
  rw [omega_eq_card_biUnion polys p hmap, Finset.card_biUnion]
  · refine Finset.sum_congr rfl (fun f hf => ?_)
    rw [omega_eq_card_biUnion {f} p (by simpa using hmap f hf)]
    simp
  · intro f hf g hg hfg
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro n hnf hng
    rw [Multiset.mem_toFinset, mem_roots (hmap f hf)] at hnf
    rw [Multiset.mem_toFinset, mem_roots (hmap g hg)] at hng
    exact hdisj f hf g hg hfg n ⟨hnf, hng⟩

lemma omega_lt (polys : Finset ℤ[X]) (hs : SchinzelCondition polys) (p : ℕ) (hp : p.Prime) :
    OmegaP polys p < p := by
  have := Fact.mk hp
  obtain ⟨n, hn⟩ := hs p hp
  unfold OmegaP
  have hne : {m : ZMod p | ∃ f ∈ polys, (f.map (Int.castRingHom (ZMod p))).eval m = 0}
      ≠ Set.univ := by
    intro h
    have hmem : ((n : ℤ) : ZMod p) ∈ {m : ZMod p | ∃ f ∈ polys,
        (f.map (Int.castRingHom (ZMod p))).eval m = 0} := by
      rw [h]
      exact Set.mem_univ _
    obtain ⟨f, hf, h0⟩ := hmem
    rw [eval_intCast_map] at h0
    exact hn f hf ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 (by simpa using h0))
  have hlt := Set.ncard_lt_card hne
  rwa [Nat.card_zmod] at hlt

-- Two distinct admissible polynomials have no common root modulo a large prime

lemma exists_bezout {f g : ℤ[X]} (hf : BunyakovskyCondition f) (hg : BunyakovskyCondition g)
    (hne : f ≠ g) : ∃ (U V : ℤ[X]) (R : ℤ), R ≠ 0 ∧ U * f + V * g = C R := by
  have hfp := hf.2.1.isPrimitive (natDegree_pos_of_bunyakovsky hf).ne'
  have hF : Irreducible (f.map (Int.castRingHom ℚ)) :=
    (IsPrimitive.Int.irreducible_iff_irreducible_map_cast hfp).1 hf.2.1
  have hndvd : ¬ f.map (Int.castRingHom ℚ) ∣ g.map (Int.castRingHom ℚ) := by
    intro h
    have hdvd : f ∣ g := (IsPrimitive.Int.dvd_iff_map_cast_dvd_map_cast f g hfp).2 h
    obtain ⟨u, hu⟩ := hf.2.1.associated_of_dvd hg.2.1 hdvd
    obtain ⟨r, hr, hru⟩ := Polynomial.isUnit_iff.1 u.isUnit
    have hlc : g.leadingCoeff = f.leadingCoeff * r := by
      rw [← hu, ← hru, leadingCoeff_mul, leadingCoeff_C]
    rcases Int.isUnit_iff.1 hr with h1 | h1
    · apply hne
      rw [← hu, ← hru, h1]
      simp
    · have hgl := hg.2.2
      have hfl := hf.2.2
      rw [hlc, h1] at hgl
      linarith
  obtain ⟨u, v, huv⟩ := (hF.coprime_iff_not_dvd).2 hndvd
  obtain ⟨b, hb, hU⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors ℤ) u
  obtain ⟨b', hb', hV⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors ℤ) v
  refine ⟨C b' * IsLocalization.integerNormalization (nonZeroDivisors ℤ) u,
    C b * IsLocalization.integerNormalization (nonZeroDivisors ℤ) v, b * b',
    mul_ne_zero (nonZeroDivisors.ne_zero hb) (nonZeroDivisors.ne_zero hb'), ?_⟩
  apply Polynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective
  rw [algebraMap_int_eq] at hU hV
  simp only [Polynomial.map_add, Polynomial.map_mul, map_C, hU, hV]
  calc C ((Int.castRingHom ℚ) b') * (b • u) * map (Int.castRingHom ℚ) f
        + C ((Int.castRingHom ℚ) b) * (b' • v) * map (Int.castRingHom ℚ) g
      = C ((Int.castRingHom ℚ) b) * C ((Int.castRingHom ℚ) b')
        * (u * map (Int.castRingHom ℚ) f + v * map (Int.castRingHom ℚ) g) := by
        simp only [zsmul_eq_mul, eq_intCast, ← map_intCast (C : ℚ →+* ℚ[X])]
        ring
    _ = C ((Int.castRingHom ℚ) (b * b')) := by
        rw [huv, mul_one, ← C_mul, ← map_mul]

lemma exists_bound_no_common_root (polys : Finset ℤ[X])
    (hb : ∀ f ∈ polys, BunyakovskyCondition f) :
    ∃ B : ℕ, ∀ p : ℕ, p.Prime → B < p → ∀ f ∈ polys, ∀ g ∈ polys, f ≠ g → ∀ n : ZMod p,
      ¬ ((f.map (Int.castRingHom (ZMod p))).eval n = 0
        ∧ (g.map (Int.castRingHom (ZMod p))).eval n = 0) := by
  have hpair : ∀ q ∈ polys ×ˢ polys, ∃ B : ℕ, ∀ p : ℕ, p.Prime → B < p → q.1 ≠ q.2 →
      ∀ n : ZMod p, ¬ ((q.1.map (Int.castRingHom (ZMod p))).eval n = 0
        ∧ (q.2.map (Int.castRingHom (ZMod p))).eval n = 0) := by
    rintro ⟨f, g⟩ hq
    rw [Finset.mem_product] at hq
    by_cases hfg : f = g
    · exact ⟨0, fun _ _ _ h => absurd hfg h⟩
    · obtain ⟨U, V, R, hR, hUV⟩ := exists_bezout (hb f hq.1) (hb g hq.2) hfg
      refine ⟨R.natAbs, fun p hp hBp _ n hn => ?_⟩
      have h := congrArg (fun q : ℤ[X] => (q.map (Int.castRingHom (ZMod p))).eval n) hUV
      simp only [Polynomial.map_add, Polynomial.map_mul, eval_add, eval_mul, hn.1, hn.2,
        mul_zero, add_zero, map_C, eval_C] at h
      have hdvd : (p : ℤ) ∣ R := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 (by simpa using h.symm)
      have hle : p ≤ R.natAbs := Nat.le_of_dvd (Int.natAbs_pos.2 hR) (Int.natCast_dvd.1 hdvd)
      omega
  choose! B hB using hpair
  refine ⟨(polys ×ˢ polys).sup B, fun p hp hBp f hf g hg hfg n => ?_⟩
  have hmem : (f, g) ∈ polys ×ˢ polys := Finset.mem_product.2 ⟨hf, hg⟩
  exact hB (f, g) hmem p hp (lt_of_le_of_lt (Finset.le_sup hmem) hBp) hfg n

-- The constant converges for every admissible set

lemma series_linear {f : ℤ[X]} (hdeg : f.natDegree = 1) (hirr : Irreducible f)
    (hlead : 0 < f.leadingCoeff) :
    ∃ c : ℝ, Tendsto (fun N : ℕ => ∑ p ∈ Nat.primesBelow N, ((OmegaP {f} p : ℝ) - 1) / p)
      atTop (𝓝 c) := by
  have hApos : 0 < (f.coeff 1).natAbs := Int.natAbs_pos.2 (coeff_one_pos hdeg hlead).ne'
  refine ⟨∑ p ∈ (f.coeff 1).natAbs.primeFactors, (-1 : ℝ) / p, tendsto_const_nhds.congr' ?_⟩
  filter_upwards [eventually_gt_atTop (f.coeff 1).natAbs] with N hN
  rw [← primesBelow_filter_dvd hApos hN, Finset.sum_filter]
  refine Finset.sum_congr rfl (fun p hp => ?_)
  have hpp := (Nat.mem_primesBelow.1 hp).2
  rw [omega_linear hdeg hirr p hpp]
  have hiff : (p : ℤ) ∣ f.coeff 1 ↔ p ∣ (f.coeff 1).natAbs := Int.natCast_dvd
  simp only [hiff]
  split_ifs <;> simp

lemma constant_converges_of_series (polys : Finset ℤ[X])
    (hb : ∀ f ∈ polys, BunyakovskyCondition f) (hs : SchinzelCondition polys)
    (hser : ∀ f ∈ polys, ∃ c : ℝ, Tendsto (fun N : ℕ =>
      ∑ p ∈ Nat.primesBelow N, ((OmegaP {f} p : ℝ) - 1) / p) atTop (𝓝 c)) :
    ∃ C : ℝ, 0 < C ∧ Tendsto (BatemanHornPartialProduct polys) atTop (𝓝 C) := by
  choose! c hc using hser
  obtain ⟨B, hB⟩ := exists_bound_no_common_root polys hb
  have hmap : ∀ p : ℕ, p.Prime → ∀ f ∈ polys, f.map (Int.castRingHom (ZMod p)) ≠ 0 :=
    fun p hp f hf => map_ne_zero_of_irreducible (hb f hf).2.1
      (natDegree_pos_of_bunyakovsky (hb f hf)).ne' p hp
  have hsum : Tendsto (fun N : ℕ => ∑ p ∈ Nat.primesBelow N,
      ∑ f ∈ polys, (1 - (OmegaP {f} p : ℝ)) / p) atTop (𝓝 (∑ f ∈ polys, -(c f))) := by
    have h := tendsto_finsetSum polys (fun f hf => (hc f hf).neg)
    refine h.congr (fun N => ?_)
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun f _ => ?_)
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun p _ => by ring)
  exact euler_product_converges polys.card (∑ f ∈ polys, f.natDegree) (OmegaP polys)
    (fun p => ∑ f ∈ polys, (1 - (OmegaP {f} p : ℝ)) / p) _
    (omega_lt polys hs) (omega_le_sum_natDegree polys hb) hsum
    (by
      filter_upwards [eventually_gt_atTop B] with p hBp hp
      have := Fact.mk hp
      show ∑ f ∈ polys, (1 - (OmegaP {f} p : ℝ)) / p
        = ((polys.card : ℝ) - (OmegaP polys p : ℝ)) / p
      rw [omega_eq_sum_of_disjoint polys p (hmap p hp) (hB p hp hBp), ← Finset.sum_div]
      congr 1
      rw [Finset.sum_sub_distrib]
      simp)

/-- Unconditional: for an admissible set of linear polynomials (the Hardy-Littlewood and Dickson
setting, twin primes included) the Bateman-Horn constant converges to a positive limit. -/
lemma constant_converges_of_linear (polys : Finset ℤ[X])
    (hb : ∀ f ∈ polys, BunyakovskyCondition f) (hs : SchinzelCondition polys)
    (hlin : ∀ f ∈ polys, f.natDegree = 1) :
    ∃ C : ℝ, 0 < C ∧ Tendsto (BatemanHornPartialProduct polys) atTop (𝓝 C) :=
  constant_converges_of_series polys hb hs
    (fun f hf => series_linear (hlin f hf) (hb f hf).2.1 (hb f hf).2.2)

lemma constant_converges (h2 : H2) (polys : Finset ℤ[X])
    (hb : ∀ f ∈ polys, BunyakovskyCondition f) (hs : SchinzelCondition polys) :
    ∃ C : ℝ, 0 < C ∧ Tendsto (BatemanHornPartialProduct polys) atTop (𝓝 C) := by
  refine constant_converges_of_series polys hb hs (fun f hf => ?_)
  have hbf := hb f hf
  by_cases hdeg : f.natDegree = 1
  · exact series_linear hdeg hbf.2.1 hbf.2.2
  · have hpos := natDegree_pos_of_bunyakovsky hbf
    exact h2 f hbf (by omega)

theorem main : H1 → H2 → H3 → type_of% @BatemanHornConjecture.bateman_horn_conjecture := by
  intro h1 h2 h3 polys hne hb hs
  by_cases h : ∃ f : ℤ[X], polys = {f} ∧ f.natDegree = 1
  · obtain ⟨f, rfl, hdeg⟩ := h
    have hf := hb f (Finset.mem_singleton_self f)
    exact linear_case h1 f hdeg hf.2.1 hf.2.2
  · obtain ⟨C, hC, hT⟩ := constant_converges h2 polys hb hs
    exact ⟨C, hC, hT, h3 polys hne hb hs h C hC hT⟩

end OMA.R_BatemanHornConjecture_bateman_horn_conjecture_R1
