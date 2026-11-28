import OMAStatements.S_oeis_a006318
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.RingTheory.PowerSeries.Catalan
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.RingTheory.Polynomial.Eisenstein.Criterion

-- Credit: @Alewawa

/-!
Replace irreducibility of the reversed Schröder truncation by finite-field certificates.
Rabin's criterion gives one coprimality test per prime divisor of the degree.
At prime degree, splitting over the degree-n extension leaves only linear factors or
one full-degree factor, so it suffices to exclude base-field roots.
The Catalan generating function gives the mod-four coefficient congruence, so the
integer polynomial is 2-Eisenstein and the prime 2 cannot witness the conjecture.
-/

namespace OMA.R_oeis_a006318_R1.SchroderEisenstein

open Finset PowerSeries
open OMA.S_oeis_a006318 (schroder)

private theorem hsubst :
    PowerSeries.HasSubst (PowerSeries.X * (PowerSeries.mk 1 : PowerSeries (ZMod 4)) ^ 2) :=
  .of_constantCoeff_zero' (by simp)

private theorem coeff_subst_succ (n : ℕ) :
    PowerSeries.coeff (n + 1) (PowerSeries.subst (PowerSeries.X * (PowerSeries.mk 1 : PowerSeries (ZMod 4)) ^ 2)
      (PowerSeries.map (Nat.castRingHom (ZMod 4)) catalanSeries)) =
      ∑ k ∈ range (n + 2),
        ((n + k).choose (2 * k - 1) : ZMod 4) * catalan k -
        ∑ k ∈ range (n + 2), if k = 0 then (1 : ZMod 4) else 0 := by
  rw [PowerSeries.coeff_subst' hsubst, finsum_eq_sum_of_support_subset _ (s := range (n + 2))]
  · rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hkn : k ≤ n + 1 := by have := mem_range.mp hk; omega
    cases k with
    | zero => simp
    | succ k =>
      have hpow : 2 * (k + 1) = 2 * k + 1 + 1 := by omega
      have hidx : 2 * k + 1 + (n + 1 - (k + 1)) = n + (k + 1) := by omega
      rw [mul_pow, ← pow_mul, PowerSeries.coeff_X_pow_mul', if_pos hkn, hpow,
        PowerSeries.mk_one_pow_eq_mk_choose_add, PowerSeries.coeff_mk, hidx]
      simp [PowerSeries.coeff_map, smul_eq_mul, mul_comm]
  · intro k hk
    by_contra h
    have hk' : ¬ k ≤ n + 1 := by simpa [Nat.lt_succ_iff] using h
    exact hk (by simp [mul_pow, PowerSeries.coeff_X_pow_mul', hk'])

private theorem schroder_difference (n : ℕ) :
    (schroder (n + 1) : ZMod 4) - (schroder n : ZMod 4) =
      ∑ k ∈ range (n + 2),
        ((n + k).choose (2 * k - 1) : ZMod 4) * catalan k -
        ∑ k ∈ range (n + 2), if k = 0 then (1 : ZMod 4) else 0 := by
  have hextra : (n + (n + 1)).choose (2 * (n + 1)) = 0 :=
    Nat.choose_eq_zero_of_lt (by omega)
  simp only [schroder, Nat.cast_sum, Nat.cast_mul, Nat.add_assoc]
  have hsum : (∑ k ∈ range (n + 2), ((n + k).choose (2 * k) : ZMod 4) * ↑(catalan k)) =
      ∑ k ∈ range (n + 1), ((n + k).choose (2 * k) : ZMod 4) * ↑(catalan k) := by
    rw [show n + 2 = (n + 1) + 1 by omega, sum_range_succ, hextra]
    simp
  rw [← hsum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  cases k with
  | zero => simp
  | succ k =>
    have hrow : n + (1 + (k + 1)) = n + (k + 1) + 1 := by omega
    have hcol : 2 * (k + 1) = (2 * (k + 1) - 1) + 1 := by omega
    rw [hrow, hcol, Nat.choose_succ_succ']
    push_cast
    simp [add_mul]

private theorem substituted_catalan :
    PowerSeries.subst (PowerSeries.X * (PowerSeries.mk 1 : PowerSeries (ZMod 4)) ^ 2)
      (PowerSeries.map (Nat.castRingHom (ZMod 4)) catalanSeries) =
      (PowerSeries.mk fun n => (schroder n : ZMod 4)) * (1 - PowerSeries.X) := by
  ext n
  cases n with
  | zero =>
    rw [PowerSeries.coeff_subst' hsubst, finsum_eq_single _ 0]
    · simp [schroder, coeff_zero_eq_constantCoeff_apply]
    · intro k hk
      simp [mul_pow, PowerSeries.coeff_X_pow_mul', show ¬ k ≤ 0 by omega]
  | succ n =>
    rw [coeff_subst_succ, ← schroder_difference]
    simp [mul_sub]

private theorem catalan_equation (y : PowerSeries (ZMod 4)) (hy : PowerSeries.HasSubst y) :
    let c := PowerSeries.subst y (PowerSeries.map (Nat.castRingHom (ZMod 4)) catalanSeries)
    c ^ 2 * y + 1 = c := by
  let c := PowerSeries.map (Nat.castRingHom (ZMod 4)) catalanSeries
  have h := congrArg (PowerSeries.map (Nat.castRingHom (ZMod 4)))
    PowerSeries.catalanSeries_sq_mul_X_add_one
  have hc : c ^ 2 * PowerSeries.X + 1 = c := by simpa [c] using h
  have hsub := congrArg (PowerSeries.substAlgHom (R := ZMod 4) hy) hc
  simpa only [map_add, map_mul, map_pow, map_one, PowerSeries.substAlgHom_X,
    PowerSeries.coe_substAlgHom] using hsub

private theorem series_equation :
    let a := PowerSeries.mk fun n => (schroder n : ZMod 4)
    a = 1 + PowerSeries.X * a + PowerSeries.X * a ^ 2 := by
  let a := PowerSeries.mk fun n => (schroder n : ZMod 4)
  let g : PowerSeries (ZMod 4) := PowerSeries.mk 1
  let x : PowerSeries (ZMod 4) := PowerSeries.X
  change a = 1 + x * a + x * a ^ 2
  have hg : g * (1 - x) = 1 := PowerSeries.mk_one_mul_one_sub_eq_one (ZMod 4)
  have h := catalan_equation _ hsubst
  dsimp only at h
  rw [substituted_catalan] at h
  change (a * (1 - x)) ^ 2 * (x * g ^ 2) + 1 = a * (1 - x) at h
  rw [show (a * (1 - x)) ^ 2 * (x * g ^ 2) = x * a ^ 2 * (g * (1 - x)) ^ 2 by ring,
    hg, one_pow, mul_one] at h
  linear_combination -h

/-- Every positive-index coefficient of the Schröder series is 2 modulo 4. -/
theorem schroder_cast_four (n : ℕ) (hn : 0 < n) : (schroder n : ZMod 4) = 2 := by
  let a := PowerSeries.mk fun n => (schroder n : ZMod 4)
  let g : PowerSeries (ZMod 4) := PowerSeries.mk 1
  let x : PowerSeries (ZMod 4) := PowerSeries.X
  let b := 1 + PowerSeries.C 2 * (x * g)
  have hg : g * (1 - x) = 1 := PowerSeries.mk_one_mul_one_sub_eq_one (ZMod 4)
  have h4 : (2 : PowerSeries (ZMod 4)) + 2 = 0 := by
    have h2 : PowerSeries.C (2 : ZMod 4) = (2 : PowerSeries (ZMod 4)) :=
      map_natCast PowerSeries.C 2
    simpa only [map_add, map_zero, h2] using
      congrArg (PowerSeries.C (R := ZMod 4)) (show (2 : ZMod 4) + 2 = 0 by decide)
  have h22 : (2 : PowerSeries (ZMod 4)) * 2 = 0 := by
    rw [show (2 : PowerSeries (ZMod 4)) * 2 = 2 + 2 by ring, h4]
  have hbsq : b ^ 2 = 1 := by
    change (1 + 2 * (x * g)) ^ 2 = 1
    calc
      _ = 1 + (2 + 2) * (x * g) + (2 * 2) * (x * g) ^ 2 := by ring
      _ = 1 := by rw [h4, h22]; simp
  have hb : b = 1 + x * b + x * b ^ 2 := by
    rw [hbsq]
    change 1 + 2 * (x * g) = 1 + x * (1 + 2 * (x * g)) + x * 1
    linear_combination 2 * x * hg
  have ha : a = 1 + x * a + x * a ^ 2 := series_equation
  have hz : (a - b) * (1 - x - x * (a + b)) = 0 := by
    linear_combination ha - hb
  have hu : IsUnit (1 - x - x * (a + b)) :=
    PowerSeries.isUnit_iff_constantCoeff.mpr (by simp [x])
  have heq : a = b := sub_eq_zero.mp (hu.mul_left_eq_zero.mp hz)
  cases n with
  | zero => omega
  | succ n =>
    have hc := congrArg (PowerSeries.coeff (n + 1)) heq
    simpa [a, b, x, g, PowerSeries.coeff_C_mul] using hc

private theorem schroder_mod_four (n : ℕ) (hn : 0 < n) :
    schroder n % 4 = 2 :=
  (ZMod.natCast_eq_natCast_iff' (schroder n) 2 4).mp (schroder_cast_four n hn)

private theorem schroder_even (n : ℕ) (hn : 0 < n) : 2 ∣ schroder n := by
  have h := schroder_mod_four n hn
  exact Nat.dvd_iff_mod_eq_zero.mpr (by omega)

open Polynomial

private theorem integral_coeff (n d : ℕ) (hd : d ≤ n) :
    (∑ k ∈ range (n + 1),
      Polynomial.C (schroder k : ℤ) * Polynomial.X ^ (n - k)).coeff d = (schroder (n - d) : ℤ) := by
  rw [finsetSum_coeff, Finset.sum_eq_single (n - d)]
  · have h : d = n - (n - d) := by omega
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_pos h, mul_one]
  · intro k hk hkne
    have hk' := mem_range.mp hk
    have h : d ≠ n - k := by omega
    simp [Polynomial.coeff_X_pow, h]
  · intro h
    exact (h (mem_range.mpr (by omega))).elim

private theorem integral_degree (n : ℕ) : (∑ k ∈ range (n + 1),
      Polynomial.C (schroder k : ℤ) * Polynomial.X ^ (n - k)).natDegree = n := by
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · apply natDegree_sum_le_of_forall_le
    intro k _
    exact (natDegree_C_mul_X_pow_le _ _).trans (Nat.sub_le _ _)
  · rw [integral_coeff n n le_rfl]
    simp [schroder]

private theorem integral_monic (n : ℕ) : (∑ k ∈ range (n + 1),
      Polynomial.C (schroder k : ℤ) * Polynomial.X ^ (n - k)).Monic := by
  unfold Monic leadingCoeff
  rw [integral_degree, integral_coeff n n le_rfl]
  simp [schroder]

/-- The polynomial is 2-Eisenstein in every positive degree. -/
theorem integral_irreducible (n : ℕ) (hn : 0 < n) :
    Irreducible (∑ k ∈ range (n + 1),
      Polynomial.C (schroder k : ℤ) * Polynomial.X ^ (n - k)) := by
  let P : Ideal ℤ := Ideal.span {2}
  have hprime : Prime (2 : ℤ) := by norm_num
  have hproper : P.IsPrime := Ideal.isPrime_span_singleton_of_prime hprime
  have hmonic := integral_monic n
  apply irreducible_of_eisenstein_criterion hproper _ _ _ _ hmonic.isPrimitive
  · rw [hmonic.leadingCoeff]
    intro h
    exact hproper.ne_top (Ideal.eq_top_of_isUnit_mem P h isUnit_one)
  · intro d hd
    have hdn := coe_lt_degree.mp hd
    rw [integral_degree] at hdn
    rw [integral_coeff n d hdn.le]
    exact Ideal.mem_span_singleton.mpr (by
      exact_mod_cast schroder_even (n - d) (by omega))
  · apply natDegree_pos_iff_degree_pos.mp
    rwa [integral_degree]
  · change (∑ k ∈ range (n + 1),
      Polynomial.C (schroder k : ℤ) * Polynomial.X ^ (n - k)).coeff 0 ∉ (Ideal.span {2} : Ideal ℤ) ^ 2
    rw [integral_coeff n 0 (Nat.zero_le _), Nat.sub_zero, pow_two, Ideal.span_singleton_mul_span_singleton]
    intro h
    have h4 : (4 : ℤ) ∣ (schroder n : ℤ) := Ideal.mem_span_singleton.mp h
    have hmod := Nat.dvd_iff_mod_eq_zero.mp (show 4 ∣ schroder n by exact_mod_cast h4)
    have := schroder_mod_four n hn
    omega

theorem rational_irreducible (n : ℕ) (hn : 0 < n) :
    Irreducible ((∑ k ∈ range (n + 1),
      Polynomial.C (schroder k : ℤ) * Polynomial.X ^ (n - k)).map (Int.castRingHom ℚ)) :=
  (Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast
    (integral_monic n).isPrimitive).mp (integral_irreducible n hn)

theorem mod_two_eq_X_pow (n : ℕ) :
    OMA.S_oeis_a006318.schroderPoly 2 n = Polynomial.X ^ n := by
  unfold OMA.S_oeis_a006318.schroderPoly
  rw [Finset.sum_eq_single 0]
  · simp [schroder]
  · intro k _ hk
    have h := schroder_even k (Nat.pos_of_ne_zero hk)
    simp [(ZMod.natCast_eq_zero_iff _ _).mpr h]
  · simp

theorem mod_two_reducible (n : ℕ) (hn : 1 < n) :
    ¬ Irreducible (OMA.S_oeis_a006318.schroderPoly 2 n) := by
  rw [mod_two_eq_X_pow]
  exact not_irreducible_pow (by omega)

end OMA.R_oeis_a006318_R1.SchroderEisenstein

open Finset Polynomial OMA.S_oeis_a006318

namespace OMA.R_oeis_a006318_R1

private theorem schroder_degree (p n : ℕ) [Fact p.Prime] :
    (schroderPoly p n).natDegree = n := by
  unfold schroderPoly
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · apply natDegree_sum_le_of_forall_le
    intro k _
    exact (natDegree_C_mul_X_pow_le _ _).trans (Nat.sub_le _ _)
  · rw [finsetSum_coeff, Finset.sum_eq_single 0]
    · simp [schroder]
    · intro k hk hne
      have hkn : k < n + 1 := mem_range.mp hk
      have h : n ≠ n - k := by omega
      simp [h]
    · simp

private theorem irreducible_of_full_degree_factor {K : Type*} [Field K]
    {f g : K[X]} (hf : f ≠ 0) (hg : Irreducible g)
    (hd : g ∣ f) (hdeg : g.natDegree = f.natDegree) : Irreducible f := by
  obtain ⟨u, rfl⟩ := hd
  have hu : u ≠ 0 := by rintro rfl; simp at hf
  rw [natDegree_mul hg.ne_zero hu] at hdeg
  have hzero : u.natDegree = 0 := by omega
  have hunit : IsUnit u := by
    rw [eq_C_of_natDegree_eq_zero hzero]
    exact isUnit_C.mpr (isUnit_iff_ne_zero.mpr (by
      intro he
      exact hu ((eq_C_of_natDegree_eq_zero hzero).trans (by simp [he]))))
  exact (irreducible_mul_isUnit hunit).mpr hg

/-- Rabin's test, with one coprimality check for each prime divisor of the degree. -/
private theorem rabin {p n : ℕ} [Fact p.Prime] {f : (ZMod p)[X]}
    (hn : 0 < n) (hdeg : f.natDegree = n) :
    Irreducible f ↔
      f ∣ X ^ (p^n) - X ∧
      ∀ r : ℕ, r.Prime → r ∣ n → IsCoprime f (X ^ (p^(n/r)) - X) := by
  have hcard : Nat.card (ZMod p) = p := by rw [Nat.card_eq_fintype_card, ZMod.card]
  have hcriterion {g : (ZMod p)[X]} (hg : Irreducible g) (d : ℕ) :
      g.natDegree ∣ d ↔ g ∣ X ^ (p^d) - X := by
    simpa only [hcard] using hg.natDegree_dvd_iff_dvd_X_pow_card_pow_sub_X (n := d)
  constructor
  · intro hf
    refine ⟨(hcriterion hf n).mp (hdeg ▸ dvd_rfl), ?_⟩
    intro r hr hrd
    rcases hf.isCoprime_or_dvd (X ^ (p^(n/r)) - X) with hc | hd
    · exact hc
    · have h := (hcriterion hf (n/r)).mpr hd
      rw [hdeg] at h
      have hpos : 0 < n/r := Nat.div_pos (Nat.le_of_dvd hn hrd) hr.pos
      exact (not_le_of_gt (Nat.div_lt_self hn hr.one_lt) (Nat.le_of_dvd hpos h)).elim
  · rintro ⟨hfull, hcop⟩
    have hfpos : 0 < f.natDegree := hdeg ▸ hn
    have hf0 : f ≠ 0 := ne_zero_of_natDegree_gt hfpos
    obtain ⟨g, hg, hgf⟩ := exists_irreducible_of_natDegree_pos hfpos
    have hd : g.natDegree ∣ n := (hcriterion hg n).mpr (hgf.trans hfull)
    apply irreducible_of_full_degree_factor hf0 hg hgf
    rw [hdeg]
    obtain ⟨s, hs⟩ := hd
    have hs0 : s ≠ 0 := by rintro rfl; simp at hs; omega
    by_cases hs1 : s = 1
    · simpa [hs1] using hs.symm
    obtain ⟨r, hr, hrD⟩ := Nat.exists_prime_and_dvd hs1
    have hrN : r ∣ n := hs ▸ dvd_mul_of_dvd_right hrD _
    have hd' : g.natDegree ∣ n/r := by
      rw [hs, Nat.mul_div_assoc _ hrD]
      exact dvd_mul_right _ _
    exact (hg.not_isUnit ((hcop r hr hrN).isUnit_of_dvd' hgf
      ((hcriterion hg (n/r)).mp hd'))).elim

private theorem prime_degree_certificate {p n : ℕ} [Fact p.Prime]
    {f : (ZMod p)[X]} (hn : n.Prime) (hdeg : f.natDegree = n)
    (hfull : f ∣ X ^ (p^n) - X) (hroot : ∀ a : ZMod p, ¬ IsRoot f a) :
    Irreducible f := by
  have hfpos : 0 < f.natDegree := hdeg ▸ hn.pos
  have hf0 : f ≠ 0 := ne_zero_of_natDegree_gt hfpos
  obtain ⟨g, hg, hgf⟩ := exists_irreducible_of_natDegree_pos hfpos
  have hcard : Nat.card (ZMod p) = p := by rw [Nat.card_eq_fintype_card, ZMod.card]
  have hd : g.natDegree ∣ n := by
    apply hg.natDegree_dvd_of_dvd_X_pow_card_pow_sub_X
    rw [hcard]
    exact hgf.trans hfull
  rcases (Nat.dvd_prime hn).mp hd with he | he
  · obtain ⟨a, ha⟩ := exists_root_of_degree_eq_one (p := g) (by
      rw [degree_eq_natDegree hg.ne_zero, he, Nat.cast_one])
    exact (hroot a (dvd_iff_isRoot.mp ((dvd_iff_isRoot.mpr ha).trans hgf))).elim
  · exact irreducible_of_full_degree_factor hf0 hg hgf (he.trans hdeg.symm)

/-- The degree-three case has an irreducible reduction at p = 3. -/
private theorem degree_three : Irreducible (schroderPoly 3 3) := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  apply irreducible_of_degree_le_three_of_not_isRoot
  · rw [schroder_degree]
    simp
  · have h0 : schroder 0 = 1 := by
      norm_num [schroder, Finset.sum_range_succ, catalan_zero, catalan_one, catalan_two, catalan_three, Nat.choose]
    have h1 : schroder 1 = 2 := by
      norm_num [schroder, Finset.sum_range_succ, catalan_zero, catalan_one, catalan_two, catalan_three, Nat.choose]
    have h2 : schroder 2 = 6 := by
      norm_num [schroder, Finset.sum_range_succ, catalan_zero, catalan_one, catalan_two, catalan_three, Nat.choose]
    have h3 : schroder 3 = 22 := by
      norm_num [schroder, Finset.sum_range_succ, catalan_zero, catalan_one, catalan_two, catalan_three, Nat.choose]
    intro a
    have heval : (schroderPoly 3 3).eval a =
          a^3 + 2*a^2 + 6*a + 22 := by
      norm_num [schroderPoly, Finset.sum_range_succ, h0, h1, h2, h3]
    rw [IsRoot, heval]
    fin_cases a <;> decide

/-- At prime degrees, a modular certificate consists of complete splitting over
the extension of degree n and absence of roots in the base field. -/
def H1 : Prop :=
  ∀ n : ℕ, 3 < n → n.Prime →
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ p < n*(n+1) ∧
      schroderPoly p n ∣ (X ^ (p^n) - X : (ZMod p)[X]) ∧
      ∀ a : ZMod p, ¬ IsRoot (schroderPoly p n) a

/-- At composite degrees, choose a prime satisfying the full Rabin test. -/
def H2 : Prop :=
  ∀ n : ℕ, 3 < n → ¬ n.Prime →
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ p < n*(n+1) ∧
      schroderPoly p n ∣ (X ^ (p^n) - X : (ZMod p)[X]) ∧
      ∀ r : ℕ, r.Prime → r ∣ n → IsCoprime (schroderPoly p n) (X ^ (p^(n/r)) - X)

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a006318.main := by
  intro h1 h2 n hn
  obtain rfl | hn' := eq_or_lt_of_le (show 3 ≤ n by omega)
  · exact ⟨3, by decide, by decide, degree_three⟩
  by_cases hp : n.Prime
  · obtain ⟨p, hpp, _, hsmall, hfull, hroot⟩ := h1 n hn' hp
    let : Fact p.Prime := ⟨hpp⟩
    exact ⟨p, hpp, hsmall, prime_degree_certificate hp (schroder_degree p n) hfull hroot⟩
  · obtain ⟨p, hpp, _, hsmall, hfull, hcop⟩ := h2 n hn' hp
    let : Fact p.Prime := ⟨hpp⟩
    exact ⟨p, hpp, hsmall, (rabin (by omega) (schroder_degree p n)).mpr ⟨hfull, hcop⟩⟩

/-- The two certificate conditions are also necessary in their respective degrees. -/
theorem certificate_equiv : (H1 ∧ H2) ↔ (type_of% @OMA.S_oeis_a006318.main) := by
  constructor
  · rintro ⟨h1,h2⟩
    exact main h1 h2
  · intro h
    constructor
    · intro n hn hprime
      obtain ⟨p, hp, hpbound, hirr⟩ := h n (by omega)
      have hp2 : p ≠ 2 := by
        rintro rfl
        exact SchroderEisenstein.mod_two_reducible n (by omega) hirr
      let : Fact p.Prime := ⟨hp⟩
      obtain ⟨hfull, hcop⟩ := (rabin (by omega) (schroder_degree p n)).mp hirr
      refine ⟨p, hp, hp2, hpbound, hfull, fun a ha => ?_⟩
      have hc := hcop n hprime (dvd_refl n)
      rw [Nat.div_self hprime.pos, pow_one] at hc
      have hd : X - C a ∣ (X^p - X : (ZMod p)[X]) := by
        apply dvd_iff_isRoot.mpr
        simp [IsRoot, ZMod.pow_card]
      exact (irreducible_X_sub_C a).not_isUnit (hc.isUnit_of_dvd' (dvd_iff_isRoot.mpr ha) hd)
    · intro n hn _
      obtain ⟨p, hp, hpbound, hirr⟩ := h n (by omega)
      have hp2 : p ≠ 2 := by
        rintro rfl
        exact SchroderEisenstein.mod_two_reducible n (by omega) hirr
      let : Fact p.Prime := ⟨hp⟩
      obtain ⟨hfull, hcop⟩ := (rabin (by omega) (schroder_degree p n)).mp hirr
      exact ⟨p, hp, hp2, hpbound, hfull, hcop⟩

end OMA.R_oeis_a006318_R1
