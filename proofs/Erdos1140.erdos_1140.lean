import FormalConjectures.ErdosProblems.«1140»
import Mathlib

/-! Erdős problem 1140. For every sufficiently large prime p, a
quadratic character modulo 8p detects a prime divisor of a positive
value p − 2x². The lower bound for L(1,χ) comes from the primitive
Siegel bound in OMA #8180, including both Euler factors at level 8p.
The upper bound uses the Burgess fourth moment in OMA #6435. Local
factorization confines the divisor convolution to squares and twice-squares
if every small odd prime is inert. Source notices accompany the arguments. -/

/- For a prime p, the quadratic character of discriminant 8p detects a small
prime divisor of p − 2x². When such a divisor is absent, the convolution
of this character with the constant-one function has support confined to
squares and twice-squares. Two analytic estimates contradict that bound.
The square-support and comparison arguments are adapted from plby/lean-proofs
(8822f7ddef30fadbd92e1c6ab4ed897af356af5e), under the Apache 2.0 license. -/

open Filter
namespace OMA.R_Erdos1140_erdos_1140_R2

def H1 : Prop :=
  ∀ᶠ p : ℕ in atTop, ∀ (_hp : p.Prime) [NeZero (8*p)] (χ : DirichletCharacter ℂ (8*p)),
    χ ≠ 1 → χ^2=1 → ((8*p:ℕ):ℝ)^(-(1/1024:ℝ)) ≤ (χ.LFunction 1).re

def H2 : Prop :=
  ∀ᶠ p : ℕ in atTop, ∀ (_hp : p.Prime) [NeZero (8*p)] (χ : DirichletCharacter ℂ (8*p)),
    (∀ n : ℕ, χ n = ((if n.Coprime (8*p) then jacobiSym ((2*p:ℕ):ℤ) n else 0 : ℤ) : ℂ)) →
    let X := Nat.sqrt p / 4
    ‖(∑ n ∈ Finset.Icc 1 X, χ.zetaMul n * ((1-(n:ℝ)/X : ℝ):ℂ)) -
      ((X:ℂ)/2) * χ.LFunction 1‖ ≤ 400*(p:ℝ)^(2041/4096:ℝ)

end OMA.R_Erdos1140_erdos_1140_R2

/- Adapted from plby/lean-proofs, Erdos1140Analytic, commit 8822f7ddef30fadbd92e1c6ab4ed897af356af5e.
Copyright (c) 2026 Boris Alexeev. Released under the Apache 2.0 license. -/
namespace OMA.E1140
open Filter

private theorem eventually_const_mul_nat_rpow_le_const_mul_nat_rpow
    {C d a b : ℝ} (_hC : 0 ≤ C) (hd : 0 < d) (hab : a < b) :
    ∀ᶠ m : ℕ in atTop,
      C * (m : ℝ) ^ a ≤ d * (m : ℝ) ^ b := by
  have hpow : Tendsto (fun m : ℕ ↦ (m : ℝ) ^ (b - a)) atTop atTop :=
    (tendsto_rpow_atTop (sub_pos.mpr hab)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
  have hlarge := hpow.eventually (eventually_ge_atTop (C / d))
  filter_upwards [hlarge, eventually_ge_atTop 1] with m hm hm1
  have hmpos : 0 < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
  have hratio : C ≤ d * (m : ℝ) ^ (b - a) := by
    simpa only [mul_comm] using (div_le_iff₀ hd).mp hm
  calc
    C * (m : ℝ) ^ a ≤ (d * (m : ℝ) ^ (b - a)) * (m : ℝ) ^ a := by
      gcongr
    _ = d * ((m : ℝ) ^ (b - a) * (m : ℝ) ^ a) := by ring
    _ = d * (m : ℝ) ^ b := by
      rw [← Real.rpow_add hmpos]
      congr 2
      ring

theorem eventually_pollackCutoff_bounds :
    ∀ᶠ p : ℕ in atTop,
      0 < (Nat.sqrt p / 4 : ℕ) ∧
      (Nat.sqrt p / 4 : ℕ) + 1 < p ∧
      2 * (Nat.sqrt p / 4 : ℕ) ^ 2 + (Nat.sqrt p / 4 : ℕ) < p ∧
      (p : ℝ) ^ (1 / 2 : ℝ) ≤ 8 * (Nat.sqrt p / 4 : ℕ) ∧
      ((Nat.sqrt p / 4 : ℕ) : ℝ) ≤ (p : ℝ) ^ (1 / 2 : ℝ) := by
  filter_upwards [eventually_ge_atTop 100] with p hp
  let s := p.sqrt
  let X := (Nat.sqrt p / 4 : ℕ)
  have hs10 : 10 ≤ s := by
    rw [show s = Nat.sqrt p by rfl, Nat.le_sqrt']
    norm_num
    exact hp
  have hX : X = s / 4 := rfl
  have hXpos : 0 < X := by rw [hX]; omega
  have h4X : 4 * X ≤ s := by rw [hX]; omega
  have hsX : s + 1 ≤ 8 * X := by rw [hX]; omega
  have hsSq : s ^ 2 ≤ p := Nat.sqrt_le' p
  have hsmall : 2 * X ^ 2 + X < s ^ 2 := by nlinarith
  have hsreal : (s : ℝ) ≤ Real.sqrt (p : ℝ) :=
    Real.nat_sqrt_le_real_sqrt
  have hsrealUpper : Real.sqrt (p : ℝ) ≤ (s + 1 : ℕ) :=
    by simpa [s] using (Real.real_sqrt_le_nat_sqrt_succ (a := p))
  refine ⟨hXpos, ?_, hsmall.trans_le hsSq, ?_, ?_⟩
  · nlinarith [hsSq]
  · rw [← Real.sqrt_eq_rpow]
    exact hsrealUpper.trans (by exact_mod_cast hsX)
  · rw [← Real.sqrt_eq_rpow]
    have hXs : (X : ℝ) ≤ (s : ℝ) := by
      exact_mod_cast (show X ≤ s by omega)
    exact hXs.trans hsreal

theorem window_gap :
    ∀ᶠ p : ℕ in atTop,
      2 * (Nat.sqrt ((Nat.sqrt p / 4 : ℕ)) + 1 : ℕ) +
          400 * (p : ℝ) ^ (2041 / 4096 : ℝ) <
        ((((Nat.sqrt p / 4 : ℕ) : ℝ) / 2) * ((8 * p : ℕ) : ℝ) ^ (-(1 / 1024 : ℝ))) := by
  have hcompare := eventually_const_mul_nat_rpow_le_const_mul_nat_rpow
    (C := 405) (d := (1 / 128 : ℝ))
    (a := (2041 / 4096 : ℝ)) (b := (2044 / 4096 : ℝ))
    (by positivity) (by positivity) (by norm_num)
  filter_upwards [eventually_pollackCutoff_bounds,
    hcompare,
    eventually_ge_atTop 8] with p hcut hcompare hp8
  let X := (Nat.sqrt p / 4 : ℕ)
  let P : ℝ := p
  let A : ℝ := P ^ (1 / 2 : ℝ)
  let E : ℝ := P ^ (2041 / 4096 : ℝ)
  have hPpos : 0 < P := by dsimp [P]; positivity
  have hPone : 1 ≤ P := by
    dsimp [P]
    exact_mod_cast (show 1 ≤ p by omega)
  have hXpos : (0 : ℝ) < X := by exact_mod_cast hcut.1
  have hXupper : (X : ℝ) ≤ A := by simpa [X, A, P] using hcut.2.2.2.2
  have hXlower : A ≤ 8 * (X : ℝ) := by simpa [X, A, P] using hcut.2.2.2.1
  have hEpos : 0 < E := Real.rpow_pos_of_pos hPpos _
  have hpow (a b : ℝ) (hab : a ≤ b) : P ^ a ≤ P ^ b :=
    Real.rpow_le_rpow_of_exponent_le hPone hab
  have hsqrtA : Real.sqrt A = P ^ (1 / 4 : ℝ) := by
    dsimp [A]
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hPpos.le]
    congr 1
    ring
  have hsqrtX : (Nat.sqrt X : ℝ) ≤ P ^ (1 / 4 : ℝ) := by
    calc
      (Nat.sqrt X : ℝ) ≤ Real.sqrt (X : ℝ) :=
        Real.nat_sqrt_le_real_sqrt
      _ ≤ Real.sqrt A := Real.sqrt_le_sqrt hXupper
      _ = P ^ (1 / 4 : ℝ) := hsqrtA
  have hquarterOne : 1 ≤ P ^ (1 / 4 : ℝ) :=
    Real.one_le_rpow hPone (by norm_num)
  have hsparse : (2 * (Nat.sqrt X + 1 : ℕ) : ℕ) ≤ 4 * E := by
    have hsparseReal : ((2 * (Nat.sqrt X + 1 : ℕ) : ℕ) : ℝ) ≤
        4 * P ^ (1 / 4 : ℝ) := by
      push_cast
      nlinarith
    exact hsparseReal.trans
      (mul_le_mul_of_nonneg_left (hpow _ _ (by norm_num)) (by norm_num))
  have h8pow : (1 / 8 : ℝ) ≤ (8 : ℝ) ^ (-(1 / 1024 : ℝ)) := by
    calc
      (1 / 8 : ℝ) = (8 : ℝ) ^ (-(1 : ℝ)) := by
        rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 8), Real.rpow_one]
        norm_num
      _ ≤ (8 : ℝ) ^ (-(1 / 1024 : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
  have hqpow : (1 / 8 : ℝ) * P ^ (-(1 / 1024 : ℝ)) ≤
      ((8 * p : ℕ) : ℝ) ^ (-(1 / 1024 : ℝ)) := by
    rw [show (((8 * p : ℕ) : ℝ)) = 8 * P by simp [P],
      Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 8) hPpos.le]
    exact mul_le_mul_of_nonneg_right h8pow
      (Real.rpow_nonneg hPpos.le (-(1 / 1024 : ℝ)))
  have hmainPower :
      A * P ^ (-(1 / 1024 : ℝ)) = P ^ (2044 / 4096 : ℝ) := by
    dsimp [A]
    rw [← Real.rpow_add hPpos]
    congr 1
    ring
  have hmain : (1 / 128 : ℝ) * P ^ (2044 / 4096 : ℝ) ≤
      ((((Nat.sqrt p / 4 : ℕ) : ℝ) / 2) * ((8 * p : ℕ) : ℝ) ^ (-(1 / 1024 : ℝ))) := by
    change (1 / 128 : ℝ) * P ^ (2044 / 4096 : ℝ) ≤
      ((X : ℝ) / 2) * ((8 * p : ℕ) : ℝ) ^ (-(1 / 1024 : ℝ))
    calc
      (1 / 128 : ℝ) * P ^ (2044 / 4096 : ℝ) =
          (A / 16) * ((1 / 8 : ℝ) * P ^ (-(1 / 1024 : ℝ))) := by
        rw [← hmainPower]
        ring
      _ ≤ ((X : ℝ) / 2) * ((8 * p : ℕ) : ℝ) ^ (-(1 / 1024 : ℝ)) := by
        have hcoef : A / 16 ≤ (X : ℝ) / 2 := by linarith
        exact mul_le_mul hcoef hqpow (by positivity) (by positivity)
  have htotal :
      (2 * (Nat.sqrt X + 1 : ℕ) : ℕ) +
          400 * E ≤ 404 * E := by
    nlinarith
  have hstrict : 404 * E < 405 * E := by nlinarith
  have hcompare' : 405 * E ≤ (1 / 128 : ℝ) * P ^ (2044 / 4096 : ℝ) := by
    simpa [E, P] using hcompare
  have hfinal := htotal.trans_lt (hstrict.trans_le (hcompare'.trans hmain))
  norm_num at hfinal ⊢
  simpa [X] using hfinal


end OMA.E1140

/- Square-support estimates for the discriminant 8p, adapted and generalized from
plby/lean-proofs 8822f7ddef30fadbd92e1c6ab4ed897af356af5e,
ErdosProblems/Erdos1140/Erdos1140Analytic.lean, Apache-2.0.
Copyright (c) 2026 Boris Alexeev. The original argument is due to Mihai Epure,
Alexandru Gica, Richard A. Mollin and Hugh C. Williams. -/
namespace OMA.E1140
open ArithmeticFunction
lemma zetaMul_prime_pow_eq_geom
    {q r e : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hr : r.Prime) :
    χ.zetaMul (r ^ e) =
      ∑ i ∈ Finset.range (e + 1), (χ (r : ZMod q)) ^ i := by
  calc
    χ.zetaMul (r ^ e) = ∑ d ∈ (r^e).divisors,
        (toArithmeticFunction (fun n : ℕ => χ (n : ZMod q))) d :=
      @ArithmeticFunction.coe_zeta_mul_apply ℂ _ (toArithmeticFunction (fun n : ℕ => χ (n : ZMod q))) (r^e)
    _ = _ := by
      simp only [Nat.sum_divisors_prime_pow hr, toArithmeticFunction, coe_mk,
        pow_eq_zero_iff', hr.ne_zero, ne_eq, false_and, ↓reduceIte, Nat.cast_pow, map_pow]


theorem local_coefficient {q X : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (zero : χ 2 = 0)
    (neg : ∀ r : ℕ, r.Prime → r ≠ 2 → r ≤ X → χ r = -1)
    {r : ℕ} (hr : r.Prime) (hrX : r ≤ X) (e : ℕ) :
    χ.zetaMul (r^e) = if r=2 ∨ Even e then 1 else 0 := by
  rw [zetaMul_prime_pow_eq_geom χ hr]
  by_cases h : r=2
  · subst r
    simp [zero]
  · rw [neg _ hr h hrX,neg_one_geom_sum]
    by_cases he : Even e
    · simp [h,he]
    · simp [h,he,(Nat.not_even_iff_odd.mp he).add_one]

theorem coefficient_support {q X : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (zero : χ 2 = 0)
    (neg : ∀ r : ℕ, r.Prime → r ≠ 2 → r ≤ X → χ r = -1)
    {n : ℕ} (hn : 0<n) (hnX : n≤X) (hnonzero : χ.zetaMul n ≠0) :
    χ.zetaMul n=1 ∧ ∃ b : ℕ, n=b^2 ∨ n=2*b^2 := by
  classical
  have hfactor : χ.zetaMul n =
      ∏ r ∈ n.primeFactors, χ.zetaMul (r ^ n.factorization r) :=
    by
      simpa [Finsupp.prod] using
        ArithmeticFunction.IsMultiplicative.multiplicative_factorization χ.zetaMul
          χ.isMultiplicative_zetaMul hn.ne'
  have hlocal : ∀ r ∈ n.primeFactors,
      χ.zetaMul (r ^ n.factorization r) =
        if r = 2 ∨ Even (n.factorization r) then 1 else 0 := by
    intro r hr
    have hrp : r.Prime := Nat.prime_of_mem_primeFactors hr
    have hrdvd : r ∣ n := (Nat.mem_primeFactors.mp hr).2.1
    have hrn : r ≤ n := Nat.le_of_dvd hn hrdvd
    exact local_coefficient χ zero neg hrp (hrn.trans hnX) _
  have hall : ∀ r ∈ n.primeFactors,
      r = 2 ∨ Even (n.factorization r) := by
    intro r hr
    by_contra hbad
    apply hnonzero
    rw [hfactor]
    apply Finset.prod_eq_zero hr
    rw [hlocal r hr, if_neg hbad]
  have hcoeff : χ.zetaMul n = 1 := by
    rw [hfactor]
    apply Finset.prod_eq_one
    intro r hr
    rw [hlocal r hr, if_pos (hall r hr)]
  refine ⟨hcoeff, ?_⟩
  obtain ⟨a, b, ha, hb, hab, hasq⟩ := Nat.sq_mul_squarefree_of_pos hn
  have hsubset : a.primeFactors ⊆ {2} := by
    intro r hra
    have hrp : r.Prime := Nat.prime_of_mem_primeFactors hra
    have hradvd : r ∣ a := (Nat.mem_primeFactors.mp hra).2.1
    have hrn : r ∣ n := by
      rw [← hab]
      exact dvd_trans hradvd (dvd_mul_left a (b ^ 2))
    have hrmem : r ∈ n.primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hrp, hrn, hn.ne'⟩
    rcases hall r hrmem with hr2 | heven
    · simp [hr2]
    · have hfac : n.factorization r = 2 * b.factorization r + 1 := by
        rw [← hab, Nat.factorization_mul (pow_ne_zero 2 hb.ne') ha.ne',
          Finsupp.add_apply, Nat.factorization_pow,
          Finsupp.smul_apply, Nat.factorization_eq_one_of_squarefree hasq hrp hradvd]
        simp
      exfalso
      rcases heven with ⟨k, hk⟩
      rw [hfac] at hk
      omega
  rcases Finset.subset_singleton_iff.mp hsubset with haempty | hasingle
  · have ha1 : a = 1 := by
      rw [← Nat.prod_primeFactors_of_squarefree hasq, haempty]
      simp
    refine ⟨b, Or.inl ?_⟩
    rw [← hab, ha1]
    simp
  · have ha2 : a = 2 := by
      rw [← Nat.prod_primeFactors_of_squarefree hasq, hasingle]
      simp
    refine ⟨b, Or.inr ?_⟩
    rw [← hab, ha2]
    ring

theorem sparse_smoothed {q X : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (zero : χ 2 = 0)
    (neg : ∀ r : ℕ, r.Prime → r ≠ 2 → r ≤ X → χ r = -1) (hX : 0<X) :
    ‖∑ n ∈ Finset.Icc 1 X, χ.zetaMul n * ((1-(n:ℝ)/X : ℝ) : ℂ)‖ ≤ 2 * (X.sqrt + 1 : ℕ) := by
  classical
  let indices := Finset.Icc 1 X
  let roots := Finset.range (X.sqrt + 1)
  let squares := roots.image (fun b : ℕ ↦ b ^ 2)
  let twiceSquares := roots.image (fun b : ℕ ↦ 2 * b ^ 2)
  let candidates := squares ∪ twiceSquares
  let weight : ℕ → ℂ := fun n ↦
    ((1 - (n : ℝ) / (X : ℝ) : ℝ) : ℂ)
  let term : ℕ → ℂ := fun n ↦ χ.zetaMul n * weight n
  have hcandidates : candidates.card ≤ 2 * (X.sqrt + 1) := by
    dsimp [candidates, squares, twiceSquares, roots]
    calc
      ((Finset.range (X.sqrt + 1)).image (fun b : ℕ ↦ b ^ 2) ∪
          (Finset.range (X.sqrt + 1)).image (fun b : ℕ ↦ 2 * b ^ 2)).card ≤
          ((Finset.range (X.sqrt + 1)).image (fun b : ℕ ↦ b ^ 2)).card +
            ((Finset.range (X.sqrt + 1)).image (fun b : ℕ ↦ 2 * b ^ 2)).card :=
        Finset.card_union_le _ _
      _ ≤ (Finset.range (X.sqrt + 1)).card +
            (Finset.range (X.sqrt + 1)).card :=
        add_le_add Finset.card_image_le Finset.card_image_le
      _ = 2 * (X.sqrt + 1) := by simp; omega
  have hsupport : ∀ n ∈ indices, χ.zetaMul n ≠ 0 → n ∈ candidates := by
    intro n hn hnonzero
    have hnbounds := Finset.mem_Icc.mp hn
    rcases (coefficient_support χ zero neg (by omega) hnbounds.2 hnonzero).2 with ⟨b, hb | hb⟩
    · have hbroot : b ≤ X.sqrt := Nat.le_sqrt'.mpr (by simpa [hb] using hnbounds.2)
      apply Finset.mem_union_left twiceSquares
      exact Finset.mem_image.mpr ⟨b, by simp [roots, hbroot], hb.symm⟩
    · have hb2X : b ^ 2 ≤ X := by omega
      have hbroot : b ≤ X.sqrt := Nat.le_sqrt'.mpr hb2X
      apply Finset.mem_union_right squares
      exact Finset.mem_image.mpr ⟨b, by simp [roots, hbroot], hb.symm⟩
  have hterm : ∀ n ∈ indices, ‖term n‖ ≤ 1 := by
    intro n hn
    have hnbounds := Finset.mem_Icc.mp hn
    by_cases hzero : χ.zetaMul n = 0
    · simp [term, hzero]
    · have hcoeff := (coefficient_support χ zero neg (by omega) hnbounds.2 hzero).1
      change χ.zetaMul n = 1 at hcoeff
      have hXreal : (0 : ℝ) < X := by exact_mod_cast hX
      have hratio0 : (0 : ℝ) ≤ (n : ℝ) / X := by positivity
      have hratio1 : (n : ℝ) / X ≤ 1 :=
        (div_le_one hXreal).2 (by exact_mod_cast hnbounds.2)
      have hweight : ‖weight n‖ ≤ 1 := by
        change ‖((1 - (n : ℝ) / (X : ℝ) : ℝ) : ℂ)‖ ≤ 1
        rw [Complex.norm_real, Real.norm_of_nonneg (sub_nonneg.mpr hratio1)]
        linarith
      change ‖χ.zetaMul n * weight n‖ ≤ 1
      rw [norm_mul, hcoeff, norm_one, one_mul]
      exact hweight
  have hsumEq :
      (∑ n ∈ indices, term n) = ∑ n ∈ indices ∩ candidates, term n := by
    symm
    apply Finset.sum_subset Finset.inter_subset_left
    intro n hnindices hnnot
    have hnotcand : n ∉ candidates := by
      intro hncand
      exact hnnot (Finset.mem_inter.mpr ⟨hnindices, hncand⟩)
    have hzero : χ.zetaMul n = 0 := by
      by_contra hnonzero
      exact hnotcand (hsupport n hnindices hnonzero)
    simp [term, hzero]
  change ‖∑ n ∈ indices, term n‖ ≤ _
  rw [hsumEq]
  calc
    ‖∑ n ∈ indices ∩ candidates, term n‖ ≤
        ∑ n ∈ indices ∩ candidates, ‖term n‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ indices ∩ candidates, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro n hn
      exact hterm n (Finset.mem_inter.mp hn).1
    _ = ((indices ∩ candidates).card : ℝ) := by simp
    _ ≤ (candidates.card : ℝ) := by
      exact_mod_cast Finset.card_le_card Finset.inter_subset_right
    _ ≤ ((2 * (X.sqrt + 1) : ℕ) : ℝ) := by exact_mod_cast hcandidates
    _ = 2 * (X.sqrt + 1 : ℕ) := by norm_num


end OMA.E1140

/- Square-support estimates for the discriminant 8p, adapted and generalized from
plby/lean-proofs 8822f7ddef30fadbd92e1c6ab4ed897af356af5e,
ErdosProblems/Erdos1140/Erdos1140Analytic.lean and ErdosProblems/Erdos1141/AttachedCharacter.lean, Apache-2.0.
Copyright (c) 2026 Boris Alexeev. The original argument is due to Mihai Epure,
Alexandru Gica, Richard A. Mollin and Hugh C. Williams. -/

namespace OMA.E1140

theorem negative_test {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    Nat.Coprime (4*p-1) (8*p) ∧ jacobiSym ((2*p:ℕ):ℤ) (4*p-1) = -1 := by
  let a := 4 * p - 1
  have hpodd : Odd p := hp.eq_two_or_odd'.resolve_left hp2
  have haodd : Odd a := by
    rcases hpodd with ⟨k, hk⟩
    refine ⟨4 * k + 1, ?_⟩
    dsimp [a]
    omega
  have ha8 : a % 8 = 3 := by
    rcases hpodd with ⟨k, hk⟩
    dsimp [a]
    omega
  have ha4 : a % 4 = 3 := by omega
  have hcop4p : Nat.Coprime a (4 * p) := by
    dsimp [a]
    rw [Nat.coprime_self_sub_left (by nlinarith [hp.pos])]
    simp
  have hcop2 : Nat.Coprime a 2 := Nat.coprime_two_right.mpr haodd
  have hcop : Nat.Coprime a (8 * p) := by
    rw [show 8 * p = 2 * (4 * p) by ring, Nat.coprime_mul_iff_right]
    exact ⟨hcop2, hcop4p⟩
  refine ⟨hcop,?_⟩
  have htwo : jacobiSym (2 : ℤ) a = -1 := by
    rw [jacobiSym.at_two haodd, ZMod.χ₈_nat_eq_if_mod_eight]
    have ha2 : a % 2 = 1 := Nat.odd_iff.mp haodd
    simp [ha2, ha8]
  have haInt : (a : ℤ) = 4 * (p : ℤ) - 1 := by
    dsimp [a]
    omega
  have hswapNeg : jacobiSym (a : ℤ) p = jacobiSym (-1 : ℤ) p := by
    apply jacobiSym.mod_left'
    rw [haInt]
    simp
  have hpJacobi : jacobiSym (p : ℤ) a = 1 := by
    rcases Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp hpodd) with hp1 | hp3
    · rw [jacobiSym.quadratic_reciprocity_one_mod_four hp1 haodd,
          hswapNeg, jacobiSym.at_neg_one hpodd,
          ZMod.χ₄_nat_one_mod_four hp1]
    · rw [jacobiSym.quadratic_reciprocity_three_mod_four hp3 ha4,
          hswapNeg, jacobiSym.at_neg_one hpodd,
          ZMod.χ₄_nat_three_mod_four hp3]
      norm_num
  rw [show ((2 * p : ℕ) : ℤ) = (2 : ℤ) * (p : ℤ) by norm_num,
    jacobiSym.mul_left, htwo, hpJacobi]
  norm_num

/-- The quadratic character of discriminant 8p, specified explicitly on all integers. -/
theorem exists_attached {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    ∃ χ : DirichletCharacter ℂ (8*p), χ ≠ 1 ∧ χ^2 = 1 ∧
    ∀ n : ℕ, χ n = ((if Nat.Coprime n (8*p) then jacobiSym ((2*p:ℕ):ℤ) n else 0 : ℤ) : ℂ) := by
  classical
  let m := 8*p
  have hm : m ≠ 0 := mul_ne_zero (by decide) hp.ne_zero
  let : NeZero m := ⟨hm⟩
  let f (n : ℕ) : ℤ := if n.Coprime m then jacobiSym ((2*p:ℕ):ℤ) n else 0
  have odd {n : ℕ} (c : n.Coprime m) : Odd n := Nat.coprime_two_right.mp
    (c.coprime_dvd_right (show 2∣m by exact ⟨4*p,by dsimp [m];ring⟩))
  have mm : 4*((2*p:ℕ):ℤ).natAbs=m := by change 4*(2*p)=8*p; ring
  have per {a b : ℕ} (e : Nat.ModEq m a b) : f a = f b := by
    have same : a.Coprime m ↔ b.Coprime m := by simp only [Nat.coprime_iff_gcd_eq_one,e.gcd_eq]
    by_cases ac : a.Coprime m
    · have bc := same.mp ac
      simp only [f,if_pos ac,if_pos bc]
      calc
        _ = jacobiSym ((2*p:ℕ):ℤ) (a%m) := by
          simpa only [mm] using jacobiSym.mod_right ((2*p:ℕ):ℤ) (odd ac)
        _ = jacobiSym ((2*p:ℕ):ℤ) (b%m) := congrArg _ e
        _ = _ := by simpa only [mm] using (jacobiSym.mod_right ((2*p:ℕ):ℤ) (odd bc)).symm
    · simp [f,ac,mt same.mpr ac]
  have mult (a b : ℕ) : f (a*b) = f a * f b := by
    by_cases ac : a.Coprime m
    · by_cases bc : b.Coprime m
      · unfold f
        rw [if_pos ((Nat.coprime_mul_iff_left).mpr ⟨ac,bc⟩),if_pos ac,if_pos bc]
        apply jacobiSym.mul_right'
        · obtain ⟨k,hk⟩ := odd ac
          omega
        · obtain ⟨k,hk⟩ := odd bc
          omega
      · unfold f
        rw [if_neg (fun h => bc (Nat.coprime_mul_iff_left.mp h).2),if_neg bc,mul_zero]
    · unfold f
      rw [if_neg (fun h => ac (Nat.coprime_mul_iff_left.mp h).1),if_neg ac,zero_mul]
  let χ : DirichletCharacter ℂ m := {
    toFun := fun a => (f a.val:ℂ)
    map_one' := by
      have h : f (1:ZMod m).val=f 1 := per (by rw [← ZMod.natCast_eq_natCast_iff]; simp)
      change (f (1:ZMod m).val:ℂ)=1
      rw [h]
      simp [f]
    map_mul' := fun a b => by
      have h : f (a*b).val=f (a.val*b.val) := per (by rw [← ZMod.natCast_eq_natCast_iff]; simp)
      simp [h,mult]
    map_nonunit' := fun a ha => by
      have hc : ¬a.val.Coprime m := fun cp => ha <| by
        simpa using (ZMod.isUnit_iff_coprime _ _).mpr cp
      simp [f,hc] }
  have val (a : ℕ) : χ a = (f a:ℂ) := congrArg (fun z : ℤ => (z:ℂ))
    (per (show Nat.ModEq m (a:ZMod m).val a by rw [← ZMod.natCast_eq_natCast_iff];simp))
  refine ⟨χ,?_,?_,val⟩
  · intro principal
    obtain ⟨cp,j⟩ := negative_test hp hp2
    have unit : IsUnit ((4*p-1:ℕ):ZMod m) := (ZMod.isUnit_iff_coprime ..).mpr cp
    have h := val (4*p-1)
    rw [principal,MulChar.one_apply unit] at h
    change (1:ℂ) = ((if (4*p-1).Coprime (8*p) then _ else _ : ℤ):ℂ) at h
    rw [if_pos cp,j] at h
    norm_num at h
  · apply MulChar.isQuadratic_iff_sq_eq_one.mp
    intro a
    change (f a.val:ℂ) = 0 ∨ (f a.val:ℂ)=1 ∨ (f a.val:ℂ)= -1
    by_cases c : a.val.Coprime m
    · have cp : a.val.Coprime (2*p) := c.coprime_dvd_right ⟨4,by dsimp [m];ring⟩
      have gcd : Int.gcd ((2*p:ℕ):ℤ) a.val = 1 := by
        rw [Int.gcd_eq_natAbs]
        exact cp.symm.gcd_eq_one
      rcases jacobiSym.eq_one_or_neg_one (a:=((2*p:ℕ):ℤ)) (b:=a.val) gcd with one|minus
      · right; left; unfold f; rw [if_pos c,one]; norm_num
      · right; right; unfold f; rw [if_pos c,minus]; norm_num
    · left; unfold f; rw [if_neg c]; norm_num

end OMA.E1140

open Filter
namespace OMA.E1140

theorem soluble_of_square {p ℓ : ℕ} (hp : ℓ.Prime) (odd : ℓ≠2)
    (sq : IsSquare (((2*p:ℕ):ℤ) : ZMod ℓ)) :
    ∃ x : ℕ, Nat.ModEq ℓ (2*x^2) p := by
  let : Fact ℓ.Prime := ⟨hp⟩
  have h2 : (2 : ZMod ℓ) ≠ 0 := by
    change ((2:ℕ) : ZMod ℓ) ≠ 0
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro d
    exact odd ((Nat.dvd_prime Nat.prime_two).mp d |>.resolve_left hp.ne_one)
  obtain ⟨y,hy⟩ := sq
  have h : (2:ZMod ℓ)*p = y^2 := by simpa [pow_two] using hy
  refine ⟨(y/2).val, ?_⟩
  rw [← ZMod.natCast_eq_natCast_iff]
  push_cast
  rw [ZMod.natCast_zmod_val]
  calc
    (2:ZMod ℓ)*(y/2)^2 = y^2/2 := by field_simp
    _ = _ := by rw [←h]; field_simp

theorem small_soluble_prime (L : OMA.R_Erdos1140_erdos_1140_R2.H1) (B : OMA.R_Erdos1140_erdos_1140_R2.H2) :
    ∀ᶠ p : ℕ in atTop, p.Prime → ∃ ℓ : ℕ, ℓ.Prime ∧ 2*ℓ^2+ℓ<p ∧
      ∃ x : ℕ, Nat.ModEq ℓ (2*x^2) p := by
  filter_upwards [L,B,window_gap,eventually_pollackCutoff_bounds,eventually_ge_atTop 3]
    with p lower smooth gap cutoff p3
  intro hp
  let : NeZero (8*p) := ⟨mul_ne_zero (by decide) hp.ne_zero⟩
  obtain ⟨χ,nontrivial,quadratic,attached⟩ := exists_attached hp (by omega)
  have hL := lower hp χ nontrivial quadratic
  have estimate := smooth hp χ attached
  let X := (Nat.sqrt p / 4 : ℕ)
  let S : ℂ := ∑ n ∈ Finset.Icc 1 X, χ.zetaMul n * ((1-(n:ℝ)/X : ℝ):ℂ)
  let main : ℂ := ((X:ℂ)/2)*χ.LFunction 1
  change ‖S-main‖ ≤ _ at estimate
  have zero : χ 2=0 := by
    have c : ¬ (2:ℕ).Coprime (8*p) := by
      intro h
      exact (by decide : ¬ (2:ℕ).Coprime 8) (Nat.coprime_mul_iff_right.mp h).1
    simpa [c] using attached 2
  by_contra no
  have neg (r : ℕ) (hr : r.Prime) (odd : r≠2) (leX : r≤X) : χ r = -1 := by
    have smallr : 2*r^2+r<p := lt_of_le_of_lt
      (add_le_add (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left leX _)) leX) cutoff.2.2.1
    have rp : r<p := leX.trans_lt (by dsimp [X]; omega)
    have rc : r.Coprime (8*p) := by
      rw [Nat.coprime_mul_iff_right,show 8=2^3 by decide,Nat.coprime_pow_right_iff (by decide : 0<3)]
      exact ⟨hr.coprime_iff_not_dvd.mpr (fun d => odd ((Nat.dvd_prime Nat.prime_two).mp d |>.resolve_left hr.ne_one)),
        hr.coprime_iff_not_dvd.mpr (fun d => rp.ne ((Nat.dvd_prime hp).mp d |>.resolve_left hr.ne_one))⟩
    have ns : ¬ IsSquare (((2*p:ℕ):ℤ):ZMod r) := fun square =>
      no ⟨r,hr,smallr,soluble_of_square hr odd square⟩
    let : Fact r.Prime := ⟨hr⟩
    have hJ := ZMod.nonsquare_iff_jacobiSym_eq_neg_one.mpr ns
    rw [attached r,if_pos rc,hJ]
    norm_num
  have sparse := sparse_smoothed χ zero neg cutoff.1
  change ‖S‖ ≤ _ at sparse
  have lowMain : ((((Nat.sqrt p / 4 : ℕ) : ℝ) / 2) * ((8 * p : ℕ) : ℝ) ^ (-(1 / 1024 : ℝ))) ≤ ‖main‖ := by
    have scale : ‖((X:ℂ)/2)‖ = (X:ℝ)/2 := by rw [norm_div,Complex.norm_natCast]; norm_num
    dsimp only [main]
    rw [norm_mul,scale]
    exact mul_le_mul_of_nonneg_left (hL.trans (Complex.re_le_norm _)) (by positivity)
  have htriangle : ‖main‖ ≤ ‖S‖ + ‖S-main‖ := by
    calc
      ‖main‖ = ‖S-(S-main)‖ := by abel_nf
      _ ≤ _ := norm_sub_le _ _
  exact (not_lt_of_ge (lowMain.trans (htriangle.trans (add_le_add sparse estimate)))) gap

end OMA.E1140

/- A centered root produces a small proper divisor for the prime-value problem. -/

namespace OMA.E1140

/-- A quadratic congruence has a representative in the lower half of the residues. -/
theorem centered_root {p n : ℕ} (hp : 0 < p) (hs : ∃ x, 2*x^2 ≡ n [MOD p]) :
    ∃ y ≤ p/2, 2*y^2 ≡ n [MOD p] := by
  obtain ⟨x, hx⟩ := hs
  let r := x % p
  have hr : r < p := Nat.mod_lt _ hp
  have hmod : 2*r^2 ≡ n [MOD p] := (((Nat.mod_modEq x p).pow 2).mul_left 2).trans hx
  by_cases h : r ≤ p/2
  · exact ⟨r, h, hmod⟩
  refine ⟨p-r, by omega, Nat.ModEq.trans ?_ hmod⟩
  apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
  push_cast [Nat.cast_sub hr.le]
  rw [ZMod.natCast_self]
  ring

/-- A balanced representative yields a proper divisor of one of the required prime values. -/
theorem bad_of_centered_prime {n p : ℕ} (hp : p.Prime)
    (hsize : 2*(p/2)^2+p < n) (hs : ∃ x, 2*x^2 ≡ n [MOD p]) :
    ¬ Erdos1140.Erdos1140Prop n := by
  obtain ⟨y, hy, hc⟩ := centered_root hp.pos hs
  have hy2 := Nat.pow_le_pow_left hy 2
  have hlt : 2*y^2+p < n := by omega
  intro good
  have hprime := good.2 y (by omega)
  have hdiv : p ∣ n-2*y^2 := (Nat.modEq_iff_dvd' (by omega)).mp hc
  rcases (Nat.dvd_prime hprime).mp hdiv with hone | heq
  · exact hp.ne_one hone
  · omega

theorem finite_of_eventual_centered (hs : ∀ᶠ n : ℕ in Filter.atTop,
    n.Prime → ∃ p, Nat.Prime p ∧ 2*(p/2)^2+p < n ∧ ∃ x, 2*x^2 ≡ n [MOD p]) :
    ¬ {n : ℕ | Erdos1140.Erdos1140Prop n}.Infinite := by
  obtain ⟨N,hN⟩ := Filter.eventually_atTop.mp hs
  apply Set.Finite.not_infinite
  apply (Set.finite_Iio N).subset
  intro n hn
  change Erdos1140.Erdos1140Prop n at hn
  by_contra! h
  have hp : n.Prime := by simpa using hn.2 0 (by simpa using hn.1)
  obtain ⟨p, hpr, hsize, hx⟩ := hN n (by simpa using h) hp
  exact bad_of_centered_prime hpr hsize hx hn

end OMA.E1140

/- Elementary classification adapted from plby/lean-proofs/ErdosProblems/Erdos1140/Erdos1140Base,
commit 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Copyright (c) 2026 Boris Alexeev.
Released under the Apache 2.0 license. Authors: GPT-5.4 Pro. -/
namespace OMA.E1140
/-- Taking `x = 0` shows that every good number is itself prime. -/
lemma prime_of_good {n : ℕ} (hn : Erdos1140.Erdos1140Prop n) : Nat.Prime n := by
  simpa using hn.2 0 (by simpa using hn.1)

/-- Write `n` just beyond the last value `2*m^2`.  The remainder of a
good number cannot lie in the first half of the resulting interval: reflecting
`m` modulo that remainder would make another required prime value factor. -/
lemma twice_lt_last_remainder {n m r : ℕ} (hn : Erdos1140.Erdos1140Prop n)
    (hdecomp : n = 2 * m ^ 2 + r) (hrpos : 0 < r) :
    2 * m < r := by
  have hmlt : 2 * m ^ 2 < n := by
    rw [hdecomp]
    omega
  have hrprime : Nat.Prime r := by
    have hp := hn.2 m hmlt
    have hvalue : n - 2 * m ^ 2 = r := by
      rw [hdecomp, Nat.add_sub_cancel_left]
    simpa [hvalue] using hp
  by_contra hnot
  have hrhalf : r ≤ 2 * m := by omega
  obtain ⟨x, hxm, hxsq⟩ :
      ∃ x : ℕ, x ≤ m ∧
        (x : ℤ) ^ 2 = ((m : ℤ) - (r : ℤ)) ^ 2 := by
    by_cases hrm : r ≤ m
    · refine ⟨m - r, by omega, ?_⟩
      rw [Nat.cast_sub hrm]
    · refine ⟨r - m, by omega, ?_⟩
      rw [Nat.cast_sub (by omega : m ≤ r)]
      ring
  have hfactor :
      n - 2 * x ^ 2 = r * (4 * m - 2 * r + 1) := by
    have hsub : 2 * x ^ 2 ≤ n := by
      rw [hdecomp]
      by_contra h
      have hcast : (n : ℤ) < (2 * x ^ 2 : ℕ) := by exact_mod_cast (by omega)
      push_cast at hcast
      rw [hxsq] at hcast
      nlinarith
    apply Nat.cast_injective (R := ℤ)
    rw [Nat.cast_sub hsub, hdecomp]
    push_cast
    rw [hxsq, Nat.cast_sub (by omega : 2 * r ≤ 4 * m)]
    push_cast
    ring
  have hsecondpos : 0 < 4 * m - 2 * r + 1 := by omega
  have hxlt : 2 * x ^ 2 < n := by
    rw [← Nat.sub_pos_iff_lt, hfactor]
    positivity
  have hp := hn.2 x hxlt
  rw [hfactor, Nat.prime_mul_iff] at hp
  rcases hp with ⟨_, hsecondOne⟩ | ⟨_, hrone⟩
  · have hremainder : r = 2 * m := by omega
    have hnprime := prime_of_good hn
    have hneven : Even n := by
      refine ⟨m ^ 2 + m, ?_⟩
      rw [hdecomp, hremainder]
      ring
    have hnTwo : n = 2 := (hnprime.even_iff.mp hneven)
    rw [hnTwo, hremainder] at hdecomp
    have hmpos : 0 < m := by omega
    nlinarith
  · exact hrprime.ne_one hrone

/-- If `n = 2*m^2 + 2*m + s` lies in the interval determined by the last
admissible square, then primality at the index reflected across `m` forces
`s` to be one of the two endpoints.  This is the elementary reduction to
the two quadratic families occurring in the classical class-number proof. -/
lemma offset_eq_one_or_top {n m s : ℕ} (hn : Erdos1140.Erdos1140Prop n)
    (hdecomp : n = 2 * m ^ 2 + 2 * m + s)
    (hspos : 0 < s) (hstop : s ≤ 2 * m + 1) :
    s = 1 ∨ s = 2 * m + 1 := by
  by_cases hsone : s = 1
  · exact Or.inl hsone
  right
  have hsTwo : 2 ≤ s := by omega
  by_contra hstopEq
  have hsTop : s ≤ 2 * m := by omega
  by_cases hsMid : s ≤ m + 1
  · let x := m + 1 - s
    have hxs : x + s = m + 1 := by
      dsimp [x]
      omega
    have hx : x ≤ m := by
      dsimp [x]
      omega
    have hfactor :
        n - 2 * x ^ 2 = (2 * s - 1) * (2 * m - s + 2) := by
      have hsub : 2 * x ^ 2 ≤ n := by
        rw [hdecomp]
        nlinarith [sq_nonneg (m - x)]
      apply Nat.cast_injective (R := ℤ)
      rw [Nat.cast_sub hsub, hdecomp]
      push_cast
      have hxZ : (x : ℤ) = (m : ℤ) + 1 - (s : ℤ) := by
        omega
      have hleftZ : ((2 * s - 1 : ℕ) : ℤ) = 2 * (s : ℤ) - 1 := by
        omega
      rw [hxZ, hleftZ, Nat.cast_sub hsTop]
      push_cast
      ring
    have hxlt : 2 * x ^ 2 < n := by
      rw [hdecomp]
      dsimp [x]
      nlinarith
    have hp := hn.2 x hxlt
    rw [hfactor] at hp
    have hleft : 1 < 2 * s - 1 := by omega
    have hright : 1 < 2 * m - s + 2 := by omega
    rw [Nat.prime_mul_iff] at hp
    rcases hp with ⟨_, hrightOne⟩ | ⟨_, hleftOne⟩ <;> omega
  · let x := s - (m + 1)
    have hxs : x + (m + 1) = s := by
      dsimp [x]
      omega
    have hx : x ≤ m := by
      dsimp [x]
      omega
    have hfactor :
        n - 2 * x ^ 2 = (2 * s - 1) * (2 * m - s + 2) := by
      have hsub : 2 * x ^ 2 ≤ n := by
        rw [hdecomp]
        nlinarith [sq_nonneg (m - x)]
      apply Nat.cast_injective (R := ℤ)
      rw [Nat.cast_sub hsub, hdecomp]
      push_cast
      have hxZ : (x : ℤ) = (s : ℤ) - ((m : ℤ) + 1) := by
        omega
      have hleftZ : ((2 * s - 1 : ℕ) : ℤ) = 2 * (s : ℤ) - 1 := by
        omega
      rw [hxZ, hleftZ, Nat.cast_sub hsTop]
      push_cast
      ring
    have hxlt : 2 * x ^ 2 < n := by
      rw [hdecomp]
      dsimp [x]
      nlinarith
    have hp := hn.2 x hxlt
    rw [hfactor] at hp
    have hleft : 1 < 2 * s - 1 := by omega
    have hright : 1 < 2 * m - s + 2 := by omega
    rw [Nat.prime_mul_iff] at hp
    rcases hp with ⟨_, hrightOne⟩ | ⟨_, hleftOne⟩ <;> omega

/-- Combining the reflected-remainder argument with `offset_eq_one_or_top`
puts a good number in one of the two quadratic families, provided `m` is
the last admissible square index. -/
lemma normal_form_of_last_remainder {n m r : ℕ} (hn : Erdos1140.Erdos1140Prop n)
    (hdecomp : n = 2 * m ^ 2 + r) (hrpos : 0 < r)
    (hrtop : r ≤ 4 * m + 1) :
    n = 2 * m ^ 2 + 2 * m + 1 ∨
      n = 2 * (m + 1) ^ 2 - 1 := by
  have hrbottom : 2 * m < r :=
    twice_lt_last_remainder hn hdecomp hrpos
  let s := r - 2 * m
  have hrs : r = 2 * m + s := by
    dsimp [s]
    omega
  have hspos : 0 < s := by
    dsimp [s]
    omega
  have hstop : s ≤ 2 * m + 1 := by
    dsimp [s]
    omega
  have hdecomp' : n = 2 * m ^ 2 + 2 * m + s := by
    rw [hdecomp, hrs]
    omega
  rcases offset_eq_one_or_top hn hdecomp' hspos hstop with hs | hs
  · left
    simpa [hs] using hdecomp'
  · right
    rw [hdecomp', hs]
    have hid : 2 * (m + 1) ^ 2 = 2 * m ^ 2 + 4 * m + 2 := by ring
    rw [hid]
    omega

/-- Every good number other than `2` belongs to one of the two classical
quadratic families. -/
theorem good_eq_two_or_quadratic_family {n : ℕ} (hn : Erdos1140.Erdos1140Prop n) :
    n = 2 ∨ ∃ m : ℕ,
      n = 2 * m ^ 2 + 2 * m + 1 ∨
        n = 2 * (m + 1) ^ 2 - 1 := by
  by_cases hnTwo : n = 2
  · exact Or.inl hnTwo
  right
  have hnprime := prime_of_good hn
  obtain ⟨k, hk⟩ := hnprime.odd_of_ne_two hnTwo
  let m := Nat.sqrt k
  let r := n - 2 * m ^ 2
  have hmSq : m * m ≤ k := by
    simpa [m] using Nat.sqrt_le k
  have hkTop : k < (m + 1) * (m + 1) := by
    simpa [m] using Nat.lt_succ_sqrt k
  have hmBelow : 2 * m ^ 2 < n := by
    rw [hk]
    nlinarith
  have hrpos : 0 < r := by
    dsimp [r]
    omega
  have hdecomp : n = 2 * m ^ 2 + r := by
    dsimp [r]
    omega
  have hrtop : r ≤ 4 * m + 1 := by
    have hnTop : n ≤ 2 * m ^ 2 + (4 * m + 1) := by
      rw [hk]
      nlinarith
    omega
  exact ⟨m, normal_form_of_last_remainder hn hdecomp hrpos hrtop⟩


set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
/-- The only positive integers through one million for which every positive
value of n−2x² is prime are the eight known examples. -/
theorem one_million {n : ℕ} (h : n ≤ 1000000) :
    Erdos1140.Erdos1140Prop n ↔ n ∈ ([2,5,7,13,31,61,181,199] : List ℕ) := by
  let knownList := ([2,5,7,13,31,61,181,199] : List ℕ)
  let smallDivisors := ([2,3,5,7,11,13,17,19,23,29,31,37,41,43] : List ℕ)
  let tableRow (n : ℕ) : Bool :=
    decide (1000000 < n ∨ n ∈ knownList) ||
    (List.range 17).any (fun x =>
      decide (n = 2*x^2+1) ||
      smallDivisors.any (fun d => decide (1 < d ∧ 2*x^2+d < n ∧ (n-2*x^2)%d = 0)))
  have row_sound {n : ℕ} (hn : n ≤ 1000000) (row : tableRow n = true)
      (hg : Erdos1140.Erdos1140Prop n) : n ∈ knownList := by
    simp only [tableRow, Bool.or_eq_true, decide_eq_true_eq, List.any_eq_true] at row
    rcases row with h | ⟨x, _, h | ⟨d, _, hd, hx, hr⟩⟩
    · exact h.resolve_left (by omega)
    · have hh := hg.2 x (by omega)
      have : n-2*x^2 = 1 := by omega
      simp [this] at hh
    · have hh := hg.2 x (by omega)
      rcases (Nat.dvd_prime hh).mp (Nat.dvd_of_mod_eq_zero hr) with he | he <;> omega
  let rowPair (m : ℕ) : Bool := tableRow (2*m^2+2*m+1) && tableRow (2*(m+1)^2-1)
  have rows_checked : ((List.range 708).all rowPair) = true := by
    dsimp only [rowPair, tableRow, knownList, smallDivisors]
    decide +kernel
  refine ⟨fun hg => ?_, Erdos1140.known_examples n⟩
  obtain he | ⟨m, ha | hb⟩ := good_eq_two_or_quadratic_family hg
  · simp [he]
  · have hm : m < 708 := by
      by_contra! hh
      have := Nat.pow_le_pow_left hh 2
      omega
    have pair := List.all_eq_true.mp rows_checked m (List.mem_range.mpr hm)
    dsimp only [rowPair] at pair
    rw [Bool.and_eq_true] at pair
    exact row_sound h (by simpa only [ha] using pair.1) hg
  · have hm : m < 708 := by
      by_contra! hh
      have hp : 709 ≤ m+1 := by omega
      have := Nat.pow_le_pow_left hp 2
      omega
    have pair := List.all_eq_true.mp rows_checked m (List.mem_range.mpr hm)
    dsimp only [rowPair] at pair
    rw [Bool.and_eq_true] at pair
    exact row_sound h (by simpa only [hb] using pair.2) hg

end OMA.E1140

namespace OMA.R_Erdos1140_erdos_1140_R2

theorem main : H1 → H2 → ¬ {n : ℕ | Erdos1140.Erdos1140Prop n}.Infinite := by
  intro lower comparison
  apply OMA.E1140.finite_of_eventual_centered
  filter_upwards [OMA.E1140.small_soluble_prime lower comparison] with n good
  intro hn
  obtain ⟨p, hp, hsize, hs⟩ := good hn
  have hhalf : p/2 ≤ p := Nat.div_le_self _ _
  exact ⟨p, hp, lt_of_le_of_lt
    (Nat.add_le_add_right (Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left hhalf 2)) p) hsize, hs⟩

end OMA.R_Erdos1140_erdos_1140_R2

/- From merged OMA #8180 (0675effa26d78cdd4eb11a9fd04c6c4ec6f10809), retaining the primitive
Siegel lower-bound dependency closure and original source notices. The two omitted Euler
factors for modulus 8p yield a lower bound of one quarter for the correction. -/
/- Adapted and modified from Whidden (7a1748306e026825ed6a5555516cc2f28989b2ac), PrimeNumberTheoremAnd, Robin1984 and openai/math (3344da59991ed94f9ba711217b29c1d760badfa6, BombieriVinogradov character blocks). Modified for the frozen H1 checker. Sources: kimihiro64/bombieri-vinogradov, kimihiro64/PrimeNumberTheoremAnd@0f15a38c619298b5cd786d39a84dd4bb8997324c, kimihiro64/Robin1984@bfa72aec0c25c8ee29cefe4449d778ff30412bee; openai/math. All four distribute the following Apache-2.0 license.
Authors: James Sundstrom
Authors: Matteo Cipollina
Authors: Michael Stoll
Authors: Robby Sneiderman
Authors: Stefan Kebekus, Matteo Cipollina
Copyright (c) 2024 James Sundstrom. All rights reserved.
Copyright (c) 2024 Michael Stoll. All rights reserved.
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Copyright (c) 2026. All rights reserved.
                                 Apache License
                           Version 2.0, January 2004
                        http://www.apache.org/licenses/

   TERMS AND CONDITIONS FOR USE, REPRODUCTION, AND DISTRIBUTION

   1. Definitions.

      "License" shall mean the terms and conditions for use, reproduction,
      and distribution as defined by Sections 1 through 9 of this document.

      "Licensor" shall mean the copyright owner or entity authorized by
      the copyright owner that is granting the License.

      "Legal Entity" shall mean the union of the acting entity and all
      other entities that control, are controlled by, or are under common
      control with that entity. For the purposes of this definition,
      "control" means (i) the power, direct or indirect, to cause the
      direction or management of such entity, whether by contract or
      otherwise, or (ii) ownership of fifty percent (50%) or more of the
      outstanding shares, or (iii) beneficial ownership of such entity.

      "You" (or "Your") shall mean an individual or Legal Entity
      exercising permissions granted by this License.

      "Source" form shall mean the preferred form for making modifications,
      including but not limited to software source code, documentation
      source, and configuration files.

      "Object" form shall mean any form resulting from mechanical
      transformation or translation of a Source form, including but
      not limited to compiled object code, generated documentation,
      and conversions to other media types.

      "Work" shall mean the work of authorship, whether in Source or
      Object form, made available under the License, as indicated by a
      copyright notice that is included in or attached to the work
      (an example is provided in the Appendix below).

      "Derivative Works" shall mean any work, whether in Source or Object
      form, that is based on (or derived from) the Work and for which the
      editorial revisions, annotations, elaborations, or other modifications
      represent, as a whole, an original work of authorship. For the purposes
      of this License, Derivative Works shall not include works that remain
      separable from, or merely link (or bind by name) to the interfaces of,
      the Work and Derivative Works thereof.

      "Contribution" shall mean any work of authorship, including
      the original version of the Work and any modifications or additions
      to that Work or Derivative Works thereof, that is intentionally
      submitted to Licensor for inclusion in the Work by the copyright owner
      or by an individual or Legal Entity authorized to submit on behalf of
      the copyright owner. For the purposes of this definition, "submitted"
      means any form of electronic, verbal, or written communication sent
      to the Licensor or its representatives, including but not limited to
      communication on electronic mailing lists, source code control systems,
      and issue tracking systems that are managed by, or on behalf of, the
      Licensor for the purpose of discussing and improving the Work, but
      excluding communication that is conspicuously marked or otherwise
      designated in writing by the copyright owner as "Not a Contribution."

      "Contributor" shall mean Licensor and any individual or Legal Entity
      on behalf of whom a Contribution has been received by Licensor and
      subsequently incorporated within the Work.

   2. Grant of Copyright License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      copyright license to reproduce, prepare Derivative Works of,
      publicly display, publicly perform, sublicense, and distribute the
      Work and such Derivative Works in Source or Object form.

   3. Grant of Patent License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      (except as stated in this section) patent license to make, have made,
      use, offer to sell, sell, import, and otherwise transfer the Work,
      where such license applies only to those patent claims licensable
      by such Contributor that are necessarily infringed by their
      Contribution(s) alone or by combination of their Contribution(s)
      with the Work to which such Contribution(s) was submitted. If You
      institute patent litigation against any entity (including a
      cross-claim or counterclaim in a lawsuit) alleging that the Work
      or a Contribution incorporated within the Work constitutes direct
      or contributory patent infringement, then any patent licenses
      granted to You under this License for that Work shall terminate
      as of the date such litigation is filed.

   4. Redistribution. You may reproduce and distribute copies of the
      Work or Derivative Works thereof in any medium, with or without
      modifications, and in Source or Object form, provided that You
      meet the following conditions:

      (a) You must give any other recipients of the Work or
          Derivative Works a copy of this License; and

      (b) You must cause any modified files to carry prominent notices
          stating that You changed the files; and

      (c) You must retain, in the Source form of any Derivative Works
          that You distribute, all copyright, patent, trademark, and
          attribution notices from the Source form of the Work,
          excluding those notices that do not pertain to any part of
          the Derivative Works; and

      (d) If the Work includes a "NOTICE" text file as part of its
          distribution, then any Derivative Works that You distribute must
          include a readable copy of the attribution notices contained
          within such NOTICE file, excluding those notices that do not
          pertain to any part of the Derivative Works, in at least one
          of the following places: within a NOTICE text file distributed
          as part of the Derivative Works; within the Source form or
          documentation, if provided along with the Derivative Works; or,
          within a display generated by the Derivative Works, if and
          wherever such third-party notices normally appear. The contents
          of the NOTICE file are for informational purposes only and
          do not modify the License. You may add Your own attribution
          notices within Derivative Works that You distribute, alongside
          or as an addendum to the NOTICE text from the Work, provided
          that such additional attribution notices cannot be construed
          as modifying the License.

      You may add Your own copyright statement to Your modifications and
      may provide additional or different license terms and conditions
      for use, reproduction, or distribution of Your modifications, or
      for any such Derivative Works as a whole, provided Your use,
      reproduction, and distribution of the Work otherwise complies with
      the conditions stated in this License.

   5. Submission of Contributions. Unless You explicitly state otherwise,
      any Contribution intentionally submitted for inclusion in the Work
      by You to the Licensor shall be under the terms and conditions of
      this License, without any additional terms or conditions.
      Notwithstanding the above, nothing herein shall supersede or modify
      the terms of any separate license agreement you may have executed
      with Licensor regarding such Contributions.

   6. Trademarks. This License does not grant permission to use the trade
      names, trademarks, service marks, or product names of the Licensor,
      except as required for reasonable and customary use in describing the
      origin of the Work and reproducing the content of the NOTICE file.

   7. Disclaimer of Warranty. Unless required by applicable law or
      agreed to in writing, Licensor provides the Work (and each
      Contributor provides its Contributions) on an "AS IS" BASIS,
      WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or
      implied, including, without limitation, any warranties or conditions
      of TITLE, NON-INFRINGEMENT, MERCHANTABILITY, or FITNESS FOR A
      PARTICULAR PURPOSE. You are solely responsible for determining the
      appropriateness of using or redistributing the Work and assume any
      risks associated with Your exercise of permissions under this License.

   8. Limitation of Liability. In no event and under no legal theory,
      whether in tort (including negligence), contract, or otherwise,
      unless required by applicable law (such as deliberate and grossly
      negligent acts) or agreed to in writing, shall any Contributor be
      liable to You for damages, including any direct, indirect, special,
      incidental, or consequential damages of any character arising as a
      result of this License or out of the use or inability to use the
      Work (including but not limited to damages for loss of goodwill,
      work stoppage, computer failure or malfunction, or any and all
      other commercial damages or losses), even if such Contributor
      has been advised of the possibility of such damages.

   9. Accepting Warranty or Additional Liability. While redistributing
      the Work or Derivative Works thereof, You may choose to offer,
      and charge a fee for, acceptance of support, warranty, indemnity,
      or other liability obligations and/or rights consistent with this
      License. However, in accepting such obligations, You may act only
      on Your own behalf and on Your sole responsibility, not on behalf
      of any other Contributor, and only if You agree to indemnify,
      defend, and hold each Contributor harmless for any liability
      incurred by, or claims asserted against, such Contributor by reason
      of your accepting any such warranty or additional liability.

   END OF TERMS AND CONDITIONS

   APPENDIX: How to apply the Apache License to your work.

      To apply the Apache License to your work, attach the following
      boilerplate notice, with the fields enclosed by brackets "[]"
      replaced with your own identifying information. (Don't include
      the brackets!)  The text should be enclosed in the appropriate
      comment syntax for the file format. We also recommend that a
      file or class name and description of purpose be included on the
      same "printed page" as the copyright notice for easier
      identification within third-party archives.

   Copyright [yyyy] [name of copyright owner]

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
 -/

section

section

open Complex Set Topology

open scoped Interval

variable {z w : ℂ} {c : ℝ}

namespace Rectangle

lemma symm : Rectangle z w = Rectangle w z := by
  simp [Rectangle, uIcc_comm]


end Rectangle










































end

section

open Complex BigOperators Nat Classical Real Topology Filter
open Set MeasureTheory intervalIntegral Asymptotics

open scoped Interval

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {f g : ℂ → E} {z w p c A : ℂ}
  {x x₁ x₂ y y₁ y₂ σ : ℝ}

noncomputable def HIntegral (f : ℂ → E) (x₁ x₂ y : ℝ) : E :=
    ∫ x in x₁..x₂, f (x + y * I)

noncomputable def VIntegral (f : ℂ → E) (x y₁ y₂ : ℝ) : E :=
    I • ∫ y in y₁..y₂, f (x + y * I)





noncomputable def RectangleIntegral (f : ℂ → E) (z w : ℂ) : E :=
    HIntegral f z.re w.re z.im - HIntegral f z.re w.re w.im +
    VIntegral f w.re z.im w.im - VIntegral f z.re z.im w.im















def RectangleBorderIntegrable (f : ℂ → E) (z w : ℂ) : Prop :=
    IntervalIntegrable (fun x => f (x + z.im * I)) volume z.re w.re ∧
    IntervalIntegrable (fun x => f (x + w.im * I)) volume z.re w.re ∧
    IntervalIntegrable (fun y => f (w.re + y * I)) volume z.im w.im ∧
    IntervalIntegrable (fun y => f (z.re + y * I)) volume z.im w.im

theorem RectangleBorderIntegrable.add {f g : ℂ → E}
    (hf : RectangleBorderIntegrable f z w) (hg : RectangleBorderIntegrable g z w) :
    RectangleIntegral (f + g) z w = RectangleIntegral f z w + RectangleIntegral g z w := by
  dsimp [RectangleIntegral, HIntegral, VIntegral]
  have h₁ := intervalIntegral.integral_add hf.1 hg.1
  have h₂ := intervalIntegral.integral_add hf.2.1 hg.2.1
  have h₃ := intervalIntegral.integral_add hf.2.2.1 hg.2.2.1
  have h₄ := intervalIntegral.integral_add hf.2.2.2 hg.2.2.2
  rw [h₁, h₂, h₃, h₄]
  module



































def HasSimplePolesOn (f : ℂ → ℂ) (s : Set ℂ) : Prop :=
  ∀ z ∈ s, (-1 : ℤ) ≤ meromorphicOrderAt f z

lemma HasSimplePolesOn.mono {f : ℂ → ℂ} {s t : Set ℂ}
    (h : HasSimplePolesOn f t) (hst : s ⊆ t) : HasSimplePolesOn f s := by
  intro z hz
  exact h z (hst hz)

noncomputable def residue (f : ℂ → ℂ) (z₀ : ℂ) : ℂ :=
  Filter.limUnder (nhdsWithin z₀ {z₀}ᶜ) (fun z ↦ (z - z₀) * f z)

























end

section

open Filter Set Complex Real



end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz


end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz





end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz




end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz




end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz


end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz



end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz



end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz




end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

open Set

namespace BombieriVinogradov.SiegelWalfisz




end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz


end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz


end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz


end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

open Finset
open scoped BigOperators

namespace BombieriVinogradov.SiegelWalfisz



end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz



end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz


end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz



end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz


end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz




end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz


end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz






end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz




end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz



end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz







end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

open Finset
open scoped BigOperators

namespace BombieriVinogradov.SiegelWalfisz



end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

open MeasureTheory Set

namespace BombieriVinogradov.SiegelWalfisz



end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

open Filter MeasureTheory Set Topology

namespace BombieriVinogradov.SiegelWalfisz






end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

open Filter MeasureTheory Set

namespace BombieriVinogradov.SiegelWalfisz


end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz





end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz


end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

open Filter Topology

namespace BombieriVinogradov.SiegelWalfisz




end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

open Filter Topology

namespace BombieriVinogradov.SiegelWalfisz


end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz


end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz


end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz








end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz




end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz





end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz





end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz





end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz




end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz


end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz



end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

open MeasureTheory Set

namespace BombieriVinogradov.SiegelWalfisz



end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

open Filter MeasureTheory Set Topology

namespace BombieriVinogradov.SiegelWalfisz







end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz



end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

open Filter Topology

namespace BombieriVinogradov.SiegelWalfisz





end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

open Filter Topology

namespace BombieriVinogradov.SiegelWalfisz


end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz



end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz


end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz



end BombieriVinogradov.SiegelWalfisz

end
end

section

namespace Real


end Real

end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz





end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz


end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz


end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz


end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz




end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz


end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz


end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

open Set

namespace BombieriVinogradov.SiegelWalfisz


end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz



end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz


end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz






end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz



end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

open Finset
open scoped BigOperators

namespace BombieriVinogradov.SiegelWalfisz



end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz



end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz


end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

open Finset

namespace BombieriVinogradov.SiegelWalfisz







end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

open Finset
open scoped BigOperators

namespace BombieriVinogradov.SiegelWalfisz



end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz


end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz


end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz






end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz



end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz


end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz


end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz


end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz


end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz


end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz


end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz


end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz


end BombieriVinogradov.SiegelWalfisz

end
end

section

namespace BombieriVinogradov.SiegelWalfisz

noncomputable def quadraticCharacterFour : DirichletCharacter ℂ 4 :=
  ZMod.χ₄.ringHomComp (Int.castRingHom ℂ)

theorem quadraticCharacterFour_sq : quadraticCharacterFour ^ 2 = 1 :=
  (ZMod.isQuadratic_χ₄.comp (Int.castRingHom ℂ)).sq_eq_one

theorem quadraticCharacterFour_ne_one : quadraticCharacterFour ≠ 1 := by
  rw [quadraticCharacterFour, MulChar.ringHomComp_ne_one_iff Int.cast_injective]
  intro hone
  have hvalue := congrArg (fun chi : MulChar (ZMod 4) ℤ ↦ chi (3 : ℕ)) hone
  have hthree : ZMod.χ₄ (3 : ℕ) = -1 :=
    ZMod.χ₄_nat_three_mod_four (by norm_num)
  rw [hthree] at hvalue
  have hunit : IsUnit (3 : ZMod 4) := by decide
  have honeValue : (1 : MulChar (ZMod 4) ℤ) ((3 : ℕ) : ZMod 4) = 1 :=
    MulChar.one_apply hunit
  rw [honeValue] at hvalue
  norm_num at hvalue

theorem three_le_level_of_ne_one {N : ℕ} [NeZero N]
    (chi : DirichletCharacter ℂ N) (hchi : chi ≠ 1) : 3 ≤ N := by
  by_contra hN
  have hNle : N ≤ 2 := by omega
  interval_cases N
  · exact (NeZero.ne 0) rfl
  · exact hchi (Subsingleton.elim _ _)
  · apply hchi
    ext x
    have hx : x = 1 := Subsingleton.elim _ _
    subst x
    simp


theorem primitiveCharacter_ne_one {N : ℕ} [NeZero N]
    (chi : DirichletCharacter ℂ N) (hchi : chi ≠ 1) :
    chi.primitiveCharacter ≠ 1 := by
  intro hprimitive
  apply hchi
  rw [← chi.changeLevel_primitiveCharacter, hprimitive]
  simp

theorem primitiveCharacter_sq_eq_one {N : ℕ} [NeZero N]
    (chi : DirichletCharacter ℂ N) (hchi : chi ^ 2 = 1) :
    chi.primitiveCharacter ^ 2 = 1 := by
  apply DirichletCharacter.changeLevel_injective chi.conductor_dvd_level
  rw [map_pow, chi.changeLevel_primitiveCharacter, hchi, map_one]

theorem three_le_conductor_of_ne_one {N : ℕ} [NeZero N]
    (chi : DirichletCharacter ℂ N) (hchi : chi ≠ 1) :
    3 ≤ chi.conductor := by
  let _ : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
  exact three_le_level_of_ne_one chi.primitiveCharacter
    (primitiveCharacter_ne_one chi hchi)

theorem quadraticCharacterFour_isPrimitive :
    DirichletCharacter.IsPrimitive quadraticCharacterFour := by
  rw [DirichletCharacter.IsPrimitive]
  have hlower := three_le_conductor_of_ne_one quadraticCharacterFour
    quadraticCharacterFour_ne_one
  have hdvd := quadraticCharacterFour.conductor_dvd_level
  have hupper : quadraticCharacterFour.conductor ≤ 4 :=
    Nat.le_of_dvd (by norm_num) hdvd
  interval_cases quadraticCharacterFour.conductor
  · norm_num at hdvd
  · rfl

theorem crossLevelMul_sq_eq_one {N M : ℕ}
    [NeZero N] [NeZero M] [NeZero (N.lcm M)]
    (chi : DirichletCharacter ℂ N) (psi : DirichletCharacter ℂ M)
    (hchiSquare : chi ^ 2 = 1) (hpsiSquare : psi ^ 2 = 1) :
    DirichletCharacter.mul chi psi ^ 2 = 1 := by
  change (DirichletCharacter.changeLevel (Nat.dvd_lcm_left N M) chi *
      DirichletCharacter.changeLevel (Nat.dvd_lcm_right N M) psi) ^ 2 = 1
  rw [mul_pow, ← map_pow, hchiSquare, map_one, ← map_pow, hpsiSquare, map_one, one_mul]

theorem crossLevelMul_ne_one_of_primitive_of_ne {N M : ℕ}
    [NeZero N] [NeZero M] [NeZero (N.lcm M)]
    (chi : DirichletCharacter ℂ N) (psi : DirichletCharacter ℂ M)
    (hchi : DirichletCharacter.IsPrimitive chi)
    (hpsi : DirichletCharacter.IsPrimitive psi) (hNM : N ≠ M) :
    DirichletCharacter.mul chi psi ≠ 1 := by
  intro hmul
  change DirichletCharacter.changeLevel (Nat.dvd_lcm_left N M) chi *
      DirichletCharacter.changeLevel (Nat.dvd_lcm_right N M) psi = 1 at hmul
  have hinv : DirichletCharacter.changeLevel (Nat.dvd_lcm_left N M) chi =
      (DirichletCharacter.changeLevel (Nat.dvd_lcm_right N M) psi)⁻¹ :=
    eq_inv_of_mul_eq_one_left hmul
  have hconductor := congrArg DirichletCharacter.conductor hinv
  rw [DirichletCharacter.conductor_changeLevel,
    DirichletCharacter.conductor_inv,
    DirichletCharacter.conductor_changeLevel,
    hchi, hpsi] at hconductor
  exact hNM hconductor

end BombieriVinogradov.SiegelWalfisz

end

section

namespace BombieriVinogradov.SiegelWalfisz

theorem quadraticValue_cases {N : ℕ} (χ : DirichletCharacter ℂ N)
    (hχ : χ ^ 2 = 1) (n : ℕ) :
    χ n = 0 ∨ χ n = 1 ∨ χ n = -1 :=
  MulChar.isQuadratic_iff_sq_eq_one.mpr hχ n

end BombieriVinogradov.SiegelWalfisz

end

section

open scoped ComplexOrder

namespace BombieriVinogradov.SiegelWalfisz

noncomputable def characterLevelCorrection {N : ℕ} [NeZero N]
    (chi : DirichletCharacter ℂ N) (s : ℝ) : ℂ :=
  ∏ p ∈ N.primeFactors,
    (1 - chi.primitiveCharacter p * (p : ℂ) ^ (-(s : ℂ)))

theorem characterLevelCorrection_pos {N : ℕ} [NeZero N]
    (chi : DirichletCharacter ℂ N) (hchiSquare : chi ^ 2 = 1)
    {s : ℝ} (hs : 0 < s) : 0 < characterLevelCorrection chi s := by
  rw [characterLevelCorrection]
  apply Finset.prod_pos
  intro p hp
  have hpPrime : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hpgt : (1 : ℝ) < p := by exact_mod_cast hpPrime.one_lt
  have hpnonneg : (0 : ℝ) ≤ p := by positivity
  have hrpowPos : 0 < (p : ℝ) ^ (-s) := Real.rpow_pos_of_pos (by positivity) _
  have hrpowLt : (p : ℝ) ^ (-s) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg hpgt (neg_neg_of_pos hs)
  rcases quadraticValue_cases chi.primitiveCharacter
      (primitiveCharacter_sq_eq_one chi hchiSquare) p with hzero | hone | hneg
  · simp [hzero]
  · rw [hone, one_mul, show (-(s : ℂ)) = ((-s : ℝ) : ℂ) by norm_num,
      ← Complex.ofReal_natCast p, ← Complex.ofReal_cpow hpnonneg (-s),
      ← Complex.ofReal_one, ← Complex.ofReal_sub]
    exact Complex.zero_lt_real.mpr (sub_pos.mpr hrpowLt)
  · rw [hneg, show (-(s : ℂ)) = ((-s : ℝ) : ℂ) by norm_num,
      ← Complex.ofReal_natCast p, ← Complex.ofReal_cpow hpnonneg (-s)]
    convert Complex.zero_lt_real.mpr (show 0 < 1 + (p : ℝ) ^ (-s) by positivity) using 1
    norm_num [Complex.ofReal_add]

theorem LFunction_eq_primitive_mul_correction {N : ℕ} [NeZero N]
    (chi : DirichletCharacter ℂ N) [NeZero chi.conductor]
    (hchi : chi ≠ 1) {s : ℝ} :
    chi.LFunction s =
      chi.primitiveCharacter.LFunction s * characterLevelCorrection chi s := by
  have hprimitive := primitiveCharacter_ne_one chi hchi
  have hchange := DirichletCharacter.LFunction_changeLevel chi.conductor_dvd_level
    chi.primitiveCharacter (s := (s : ℂ)) (.inl hprimitive)
  rw [chi.changeLevel_primitiveCharacter] at hchange
  exact hchange

end BombieriVinogradov.SiegelWalfisz

end

section

open Filter LSeries Set

namespace BombieriVinogradov.SiegelWalfisz

private theorem quadraticLFunction_im_eq_zero_of_one_lt_bv616 {N : ℕ} [NeZero N]
    (chi : DirichletCharacter ℂ N) (hchi : chi ^ 2 = 1)
    {x : ℝ} (hx : 1 < x) : (chi.LFunction x).im = 0 := by
  rw [DirichletCharacter.LFunction_eq_LSeries chi (by simpa using hx)]
  rw [LSeries, Complex.im_tsum (chi.LSeriesSummable_of_one_lt_re (by simpa using hx))]
  convert tsum_zero with n
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [LSeries.term_of_ne_zero hn]
    rcases quadraticValue_cases chi hchi n with hzero | hone | hneg
    · simp [hzero]
    · rw [hone, ← Complex.ofReal_natCast, ← Complex.ofReal_cpow (Nat.cast_nonneg n)]
      simp
    · rw [hneg, ← Complex.ofReal_natCast, ← Complex.ofReal_cpow (Nat.cast_nonneg n)]
      simp

private theorem quadraticLFunction_im_eq_zero_at_one_bv616 {N : ℕ} [NeZero N]
    (chi : DirichletCharacter ℂ N) (hchi : chi ^ 2 = 1) (hchi_ne : chi ≠ 1) :
    (chi.LFunction 1).im = 0 := by
  let f : ℝ → ℝ := fun x ↦ (chi.LFunction x).im
  have hLcont : ContinuousAt chi.LFunction (1 : ℂ) :=
    (chi.differentiableAt_LFunction 1 (.inr hchi_ne)).continuousAt
  have hLreal : ContinuousAt (fun x : ℝ ↦ chi.LFunction x) 1 :=
    hLcont.comp_of_eq Complex.continuous_ofReal.continuousAt (by simp)
  have hfcont : ContinuousAt f 1 :=
    Complex.continuous_im.continuousAt.comp' hLreal
  have hlimit : Tendsto f (nhdsWithin 1 (Ioi 1)) (nhds (f 1)) :=
    hfcont.mono_left inf_le_left
  have hzero : Tendsto f (nhdsWithin 1 (Ioi 1)) (nhds 0) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact (quadraticLFunction_im_eq_zero_of_one_lt_bv616 chi hchi hx).symm
  exact tendsto_nhds_unique hlimit hzero

theorem quadraticLFunction_one_re_pos {N : ℕ} [NeZero N]
    (chi : DirichletCharacter ℂ N) (hchi : chi ^ 2 = 1) (hchi_ne : chi ≠ 1) :
    0 < (chi.LFunction 1).re := by
  have habs : LSeries.abscissaOfAbsConv (chi ·) < ⊤ := by
    rw [DirichletCharacter.absicssaOfAbsConv_eq_one (NeZero.ne N) chi]
    exact EReal.coe_lt_top 1
  have hseries : Tendsto (fun x : ℝ ↦ LSeries (chi ·) x) atTop (nhds 1) := by
    simpa using LSeries.tendsto_atTop habs
  have hL : Tendsto (fun x : ℝ ↦ chi.LFunction x) atTop (nhds 1) := by
    apply hseries.congr'
    filter_upwards [eventually_gt_atTop 1] with x hx
    exact (DirichletCharacter.LFunction_eq_LSeries chi (by simpa using hx)).symm
  have hre : Tendsto (fun x : ℝ ↦ (chi.LFunction x).re) atTop (nhds 1) := by
    convert Complex.continuous_re.continuousAt.tendsto.comp hL using 1 <;>
      simp [Function.comp_def]
  have heventuallyPos : ∀ᶠ x : ℝ in atTop, 0 < (chi.LFunction x).re :=
    hre (Ioi_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  obtain ⟨X, hXpos, hXone⟩ :=
    (heventuallyPos.and (eventually_gt_atTop (a := (1 : ℝ)))).exists
  by_contra hnot
  have himOne := quadraticLFunction_im_eq_zero_at_one_bv616 chi hchi hchi_ne
  have hreOne_ne : (chi.LFunction 1).re ≠ 0 := by
    intro hreOne
    apply chi.LFunction_apply_one_ne_zero hchi_ne
    apply Complex.ext
    · simpa using hreOne
    · simpa using himOne
  have hreOne_neg : (chi.LFunction 1).re < 0 :=
    lt_of_le_of_ne (le_of_not_gt hnot) hreOne_ne
  let f : ℝ → ℝ := fun x ↦ (chi.LFunction x).re
  have hfcont : Continuous f := by
    apply continuous_iff_continuousAt.mpr
    intro x
    have hLcont : ContinuousAt chi.LFunction (x : ℂ) :=
      (chi.differentiable_LFunction hchi_ne).continuous.continuousAt
    have hLreal : ContinuousAt (fun y : ℝ ↦ chi.LFunction y) x :=
      hLcont.comp_of_eq Complex.continuous_ofReal.continuousAt rfl
    exact Complex.continuous_re.continuousAt.comp' hLreal
  have hzeroMem : 0 ∈ Icc (f 1) (f X) := ⟨hreOne_neg.le, hXpos.le⟩
  obtain ⟨y, hy, hfy⟩ := intermediate_value_Icc hXone.le hfcont.continuousOn hzeroMem
  have himY : (chi.LFunction y).im = 0 := by
    rcases hy.1.eq_or_lt with rfl | hylt
    · exact himOne
    · exact quadraticLFunction_im_eq_zero_of_one_lt_bv616 chi hchi hylt
  have hLy : chi.LFunction y = 0 := by
    apply Complex.ext
    · simpa [f] using hfy
    · simpa using himY
  exact chi.LFunction_ne_zero_of_one_le_re (.inl hchi_ne) (by simpa using hy.1) hLy

theorem norm_quadraticLFunction_one_eq_re {N : ℕ} [NeZero N]
    (chi : DirichletCharacter ℂ N) (hchi : chi ^ 2 = 1) (hchi_ne : chi ≠ 1) :
    ‖chi.LFunction 1‖ = (chi.LFunction 1).re := by
  have him := quadraticLFunction_im_eq_zero_at_one_bv616 chi hchi hchi_ne
  have hre := quadraticLFunction_one_re_pos chi hchi hchi_ne
  rw [Complex.norm_def, Complex.normSq_apply, him]
  norm_num [← pow_two, Real.sqrt_sq_eq_abs, abs_of_pos hre]

end BombieriVinogradov.SiegelWalfisz

end

section

namespace BombieriVinogradov.SiegelWalfisz

abbrev BoundedDirichletCharacter (N : ℕ) :=
  Σ M : Fin (N + 1), DirichletCharacter ℂ M.val

noncomputable def finiteLevelValue (epsilon : ℝ) {N : ℕ}
    (entry : BoundedDirichletCharacter N) : ℝ := by
  classical
  exact if hlevel : 0 < entry.1.val then
      let _ : NeZero entry.1.val := ⟨hlevel.ne'⟩
      if hquadratic : entry.2 ^ 2 = 1 ∧ Ne entry.2 1 then
        (entry.2.LFunction 1).re * (entry.1.val : ℝ) ^ epsilon
      else
        1
    else
      1

theorem finiteLevelValue_pos (epsilon : ℝ) {N : ℕ}
    (entry : BoundedDirichletCharacter N) :
    0 < finiteLevelValue epsilon entry := by
  classical
  rw [finiteLevelValue]
  split
  · next hlevel =>
      let _ : NeZero entry.1.val := ⟨hlevel.ne'⟩
      split
      · next hquadratic =>
          have hlevelReal : (0 : ℝ) < (entry.1.val : ℕ) := by
            exact_mod_cast hlevel
          exact mul_pos
            (quadraticLFunction_one_re_pos entry.2 hquadratic.1 hquadratic.2)
            (Real.rpow_pos_of_pos hlevelReal epsilon)
      · norm_num
  · norm_num

noncomputable def finiteLevelValues (epsilon : ℝ) (N : ℕ) : Finset ℝ := by
  classical
  exact (Finset.univ : Finset (BoundedDirichletCharacter N)).image
    (finiteLevelValue epsilon)

theorem finiteLevelValues_nonempty (epsilon : ℝ) (N : ℕ) :
    (finiteLevelValues epsilon N).Nonempty := by
  classical
  unfold finiteLevelValues
  exact Finset.image_nonempty.mpr Finset.univ_nonempty

noncomputable def finiteLevelConstant (epsilon : ℝ) (N : ℕ) : ℝ :=
  (finiteLevelValues epsilon N).min' (finiteLevelValues_nonempty epsilon N)

theorem finiteLevelConstant_pos (epsilon : ℝ) (N : ℕ) :
    0 < finiteLevelConstant epsilon N := by
  classical
  have hmem := Finset.min'_mem (finiteLevelValues epsilon N)
    (finiteLevelValues_nonempty epsilon N)
  unfold finiteLevelValues at hmem
  obtain ⟨entry, _, hentry⟩ := Finset.mem_image.mp hmem
  unfold finiteLevelConstant
  unfold finiteLevelValues
  rw [← hentry]
  exact finiteLevelValue_pos epsilon entry

theorem finiteLevelConstant_le_value {epsilon : ℝ} {N M : ℕ}
    [NeZero M] (hMN : M ≤ N) (hM : 3 ≤ M)
    (psi : DirichletCharacter ℂ M) (hpsiSquare : psi ^ 2 = 1)
    (hpsi : Ne psi 1) :
    finiteLevelConstant epsilon N * (M : ℝ) ^ (-epsilon) ≤
      (psi.LFunction 1).re := by
  classical
  let level : Fin (N + 1) := ⟨M, Nat.lt_succ_of_le hMN⟩
  let entry : BoundedDirichletCharacter N := ⟨level, psi⟩
  have hlevel : 0 < level.val := by
    dsimp [level]
    omega
  have hentryValue : finiteLevelValue epsilon entry =
      (psi.LFunction 1).re * (M : ℝ) ^ epsilon := by
    rw [finiteLevelValue]
    simp [entry, level, hlevel, hpsiSquare, hpsi]
  have hentryMem : finiteLevelValue epsilon entry ∈ finiteLevelValues epsilon N := by
    rw [finiteLevelValues]
    exact Finset.mem_image.mpr ⟨entry, Finset.mem_univ _, rfl⟩
  have hminimum : finiteLevelConstant epsilon N ≤ finiteLevelValue epsilon entry := by
    exact Finset.min'_le _ _ hentryMem
  rw [hentryValue] at hminimum
  have hMnonneg : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  have hMpos : (0 : ℝ) < M := by exact_mod_cast NeZero.pos M
  have hscaled := mul_le_mul_of_nonneg_right hminimum
    (Real.rpow_nonneg hMnonneg (-epsilon))
  calc
    finiteLevelConstant epsilon N * (M : ℝ) ^ (-epsilon) ≤
        ((psi.LFunction 1).re * (M : ℝ) ^ epsilon) *
          (M : ℝ) ^ (-epsilon) := hscaled
    _ = (psi.LFunction 1).re := by
      rw [mul_assoc, ← Real.rpow_add hMpos]
      norm_num

end BombieriVinogradov.SiegelWalfisz

end

section

namespace BombieriVinogradov.SiegelWalfisz

noncomputable def siegelLowerEndpoint (epsilon : ℝ) (D : ℕ) : ℝ :=
  max (7 / 8) (1 - epsilon / (2 * ((D : ℝ) + 1)))

theorem seven_eighths_le_siegelLowerEndpoint (epsilon : ℝ) (D : ℕ) :
    7 / 8 ≤ siegelLowerEndpoint epsilon D :=
  le_max_left _ _

theorem siegelLowerEndpoint_lt_one {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (D : ℕ) : siegelLowerEndpoint epsilon D < 1 := by
  apply max_lt
  · norm_num
  · have hdenominator : 0 < 2 * ((D : ℝ) + 1) := by positivity
    have : 0 < epsilon / (2 * ((D : ℝ) + 1)) := div_pos hepsilon hdenominator
    linarith

theorem siegel_exponent_control {epsilon s : ℝ} (hepsilon : 0 < epsilon)
    (D : ℕ) (hs : siegelLowerEndpoint epsilon D ≤ s) :
    (D : ℝ) * (1 - s) + epsilon / 2 ≤ epsilon := by
  have hDnonneg : (0 : ℝ) ≤ D := Nat.cast_nonneg D
  have hDplus : 0 < (D : ℝ) + 1 := by positivity
  have hrange : 1 - epsilon / (2 * ((D : ℝ) + 1)) ≤ s :=
    (le_max_right (7 / 8) (1 - epsilon / (2 * ((D : ℝ) + 1)))).trans hs
  have hgap : 1 - s ≤ epsilon / (2 * ((D : ℝ) + 1)) := by linarith
  have hscaled : (D : ℝ) * (1 - s) ≤
      (D : ℝ) * (epsilon / (2 * ((D : ℝ) + 1))) :=
    mul_le_mul_of_nonneg_left hgap hDnonneg
  have hratio : (D : ℝ) / ((D : ℝ) + 1) ≤ 1 :=
    (div_le_one hDplus).2 (by linarith)
  have habsorb : (D : ℝ) * (epsilon / (2 * ((D : ℝ) + 1))) ≤ epsilon / 2 := by
    calc
      (D : ℝ) * (epsilon / (2 * ((D : ℝ) + 1))) =
          (epsilon / 2) * ((D : ℝ) / ((D : ℝ) + 1)) := by
        field_simp
      _ ≤ epsilon / 2 :=
        mul_le_of_le_one_right (div_nonneg hepsilon.le zero_le_two) hratio
  linarith

end BombieriVinogradov.SiegelWalfisz

end

section

open Metric Set

namespace BombieriVinogradov.SiegelWalfisz

def siegelCauchyCircle : Set ℂ := sphere 2 (3 / 2 : ℝ)


theorem siegelCauchyCircle_norm_sub_one_lower {s : ℂ}
    (hs : s ∈ siegelCauchyCircle) : (1 / 2 : ℝ) ≤ ‖s - 1‖ := by
  have hdist : dist s (2 : ℂ) = (3 / 2 : ℝ) := by
    simpa only [siegelCauchyCircle, mem_sphere] using hs
  have htriangle : dist s (2 : ℂ) ≤ dist s (1 : ℂ) + dist (1 : ℂ) (2 : ℂ) :=
    dist_triangle _ _ _
  rw [hdist] at htriangle
  simp only [Complex.dist_eq] at htriangle
  norm_num at htriangle
  have hone : ‖(1 : ℂ)‖ = 1 := by
    simpa only [Nat.cast_one] using Complex.norm_natCast 1
  try rw [hone] at htriangle
  linarith

theorem siegelCauchyCircle_ne_one {s : ℂ} (hs : s ∈ siegelCauchyCircle) : s ≠ 1 := by
  intro h
  subst s
  have hbound := siegelCauchyCircle_norm_sub_one_lower hs
  norm_num at hbound


end BombieriVinogradov.SiegelWalfisz

end

section

open Metric Set

namespace BombieriVinogradov.SiegelWalfisz

def siegelAnalyticDomain : Set ℂ := ball 2 (7 / 4 : ℝ)

theorem siegelCauchyCircle_subset_analyticDomain :
    siegelCauchyCircle ⊆ siegelAnalyticDomain := by
  intro s hs
  rw [siegelCauchyCircle, mem_sphere] at hs
  rw [siegelAnalyticDomain, mem_ball]
  linarith

theorem siegelAnalyticDomain_re_lower {s : ℂ} (hs : s ∈ siegelAnalyticDomain) :
    (1 / 4 : ℝ) < s.re := by
  have hnorm : ‖s - 2‖ < (7 / 4 : ℝ) := by
    simpa [siegelAnalyticDomain, mem_ball, Complex.dist_eq] using hs
  have hre : |s.re - 2| < (7 / 4 : ℝ) :=
    (Complex.abs_re_le_norm (s - 2)).trans_lt (by simpa using hnorm)
  linarith [neg_abs_le (s.re - 2)]

theorem siegelAnalyticDomain_norm_upper {s : ℂ} (hs : s ∈ siegelAnalyticDomain) :
    ‖s‖ < (15 / 4 : ℝ) := by
  have hdist : dist s (2 : ℂ) < (7 / 4 : ℝ) := by
    simpa only [siegelAnalyticDomain, mem_ball] using hs
  have htriangle : dist s (0 : ℂ) ≤ dist s (2 : ℂ) + dist (2 : ℂ) (0 : ℂ) :=
    dist_triangle _ _ _
  rw [Complex.dist_eq] at hdist
  simp only [Complex.dist_eq] at htriangle
  norm_num at htriangle
  linarith

end BombieriVinogradov.SiegelWalfisz

end

section

namespace BombieriVinogradov.SiegelWalfisz

noncomputable def characterLBlock {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (k : ℕ) (s : ℂ) : ℂ :=
  ∑ j : ZMod N, χ j * ((k * N + j.val : ℕ) : ℂ) ^ (-s)

theorem characterLBlock_recenter {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (k : ℕ) (s : ℂ) :
    characterLBlock χ k s =
      ∑ j : ZMod N, χ j *
        (((k * N + j.val : ℕ) : ℂ) ^ (-s) - (((k + 1) * N : ℕ) : ℂ) ^ (-s)) := by
  rw [characterLBlock]
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
  rw [χ.sum_eq_zero_of_ne_one hχ, zero_mul, sub_zero]

theorem characterLBlock_differentiableOn {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (k : ℕ) :
    DifferentiableOn ℂ (characterLBlock χ k) siegelAnalyticDomain := by
  have hN : N ≠ 1 := by
    intro h
    subst N
    exact hχ (Subsingleton.elim _ _)
  rw [show characterLBlock χ k = fun s ↦
      ∑ j : ZMod N, χ j *
        (((k * N + j.val : ℕ) : ℂ) ^ (-s) - (((k + 1) * N : ℕ) : ℂ) ^ (-s)) by
    funext s
    exact characterLBlock_recenter χ hχ k s]
  intro s hs
  apply DifferentiableAt.differentiableWithinAt
  apply DifferentiableAt.fun_sum
  intro j hj
  by_cases hj0 : j = 0
  · subst j
    rw [χ.map_zero' hN]
    simp
  · have hx : ((k * N + j.val : ℕ) : ℂ) ≠ 0 := by
      exact Nat.cast_ne_zero.mpr (by
        have hjv : j.val ≠ 0 := (ZMod.val_ne_zero j).mpr hj0
        omega)
    have hy : ((((k + 1) * N : ℕ) : ℂ)) ≠ 0 := by
      exact Nat.cast_ne_zero.mpr (Nat.mul_ne_zero (by omega) (NeZero.ne N))
    exact (((differentiableAt_id.neg).const_cpow (Or.inl hx)).sub
      ((differentiableAt_id.neg).const_cpow (Or.inl hy))).const_mul (χ j)

end BombieriVinogradov.SiegelWalfisz

end

section

namespace BombieriVinogradov.SiegelWalfisz

private theorem sum_zmod_val_inv_le_harmonic_bv622 (N : ℕ) [NeZero N] :
    ∑ j : ZMod N, ((j.val : ℝ)⁻¹) ≤ 2 * (harmonic N : ℝ) := by
  calc
    ∑ j : ZMod N, ((j.val : ℝ)⁻¹) = ∑ i : Fin N, ((i.val : ℝ)⁻¹) := by
      symm
      apply Fintype.sum_equiv (ZMod.finEquiv N).toEquiv
      intro i
      change ((i.val : ℝ)⁻¹) = ((((ZMod.finEquiv N) i).val : ℝ)⁻¹)
      congr 2
      obtain _ | n := N
      · exact (NeZero.ne 0 rfl).elim
      · rfl
    _ ≤ ∑ i : Fin N, 2 * ((((i.val + 1 : ℕ) : ℝ))⁻¹) := by
      apply Finset.sum_le_sum
      intro i hi
      by_cases hi0 : i.val = 0
      · simp [hi0]
      · have hipos : (0 : ℝ) < i.val := by exact_mod_cast Nat.pos_of_ne_zero hi0
        have hisucc : (0 : ℝ) < i.val + 1 := by positivity
        rw [← one_div, ← div_eq_mul_inv]
        norm_num only [Nat.cast_add, Nat.cast_one]
        rw [div_le_div_iff₀ hipos hisucc]
        norm_num
        have hiNat : i.val + 1 ≤ 2 * i.val := by omega
        exact_mod_cast hiNat
    _ = 2 * (harmonic N : ℝ) := by
      rw [← Finset.mul_sum]
      congr 1
      rw [Finset.sum_fin_eq_sum_range, harmonic, Rat.cast_sum]
      apply Finset.sum_congr rfl
      intro x hx
      simp [Finset.mem_range.mp hx]

theorem norm_characterLBlock_zero_one_le {N : ℕ} [NeZero N]
    (chi : DirichletCharacter ℂ N) (hchi : chi ≠ 1) :
    ‖characterLBlock chi 0 1‖ ≤ 2 * (1 + Real.log N) := by
  have hN : N ≠ 1 := by
    intro h
    subst N
    exact hchi (Subsingleton.elim _ _)
  rw [characterLBlock]
  calc
    ‖∑ j : ZMod N, chi j * (((0 * N + j.val : ℕ) : ℂ) ^ (-(1 : ℂ)))‖ ≤
        ∑ j : ZMod N, ‖chi j * (((0 * N + j.val : ℕ) : ℂ) ^ (-(1 : ℂ)))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ j : ZMod N, ((j.val : ℝ)⁻¹) := by
      apply Finset.sum_le_sum
      intro j hj
      by_cases hj0 : j = 0
      · subst j
        rw [chi.map_zero' hN]
        simp
      · have hjv : j.val ≠ 0 := (ZMod.val_ne_zero j).mpr hj0
        rw [norm_mul]
        calc
          ‖chi j‖ * ‖((0 * N + j.val : ℕ) : ℂ) ^ (-(1 : ℂ))‖ ≤
              1 * ‖((j.val : ℕ) : ℂ) ^ (-(1 : ℂ))‖ := by
            norm_num only [Nat.zero_mul, Nat.zero_add]
            exact mul_le_mul_of_nonneg_right (chi.norm_le_one j) (norm_nonneg _)
          _ = ((j.val : ℝ)⁻¹) := by
            rw [one_mul, show (-(1 : ℂ)) = ((-1 : ℝ) : ℂ) by norm_num,
              ← Complex.ofReal_natCast j.val,
              ← Complex.ofReal_cpow (Nat.cast_nonneg j.val) (-1), Complex.norm_real,
              Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg j.val) _),
              Real.rpow_neg_one]
    _ ≤ 2 * (harmonic N : ℝ) := sum_zmod_val_inv_le_harmonic_bv622 N
    _ ≤ 2 * (1 + Real.log N) := by
      gcongr
      exact harmonic_le_one_add_log N

end BombieriVinogradov.SiegelWalfisz

end

section

namespace BombieriVinogradov.SiegelWalfisz

theorem norm_cpow_neg_one_sub_le {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    ‖(x : ℂ) ^ ((-1 : ℝ) : ℂ) - (y : ℂ) ^ ((-1 : ℝ) : ℂ)‖ ≤
      (y - x) / x ^ 2 := by
  have hy : 0 < y := hx.trans_le hxy
  rw [← Complex.ofReal_cpow hx.le (-1), ← Complex.ofReal_cpow hy.le (-1),
    ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
    Real.rpow_neg_one, Real.rpow_neg_one]
  have hinv : y⁻¹ ≤ x⁻¹ := (inv_le_inv₀ hy hx).mpr hxy
  rw [abs_of_nonneg (sub_nonneg.mpr hinv)]
  have hid : x⁻¹ - y⁻¹ = (y - x) / (x * y) := by
    field_simp
  rw [hid, pow_two]
  exact div_le_div_of_nonneg_left (sub_nonneg.mpr hxy) (mul_pos hx hx)
    (mul_le_mul_of_nonneg_left hxy hx.le)

end BombieriVinogradov.SiegelWalfisz

end

section

namespace BombieriVinogradov.SiegelWalfisz

theorem norm_characterLBlock_one_le {N : ℕ} [NeZero N]
    (chi : DirichletCharacter ℂ N) (hchi : chi ≠ 1) {k : ℕ} (hk : 1 ≤ k) :
    ‖characterLBlock chi k 1‖ ≤ ((k : ℝ) ^ 2)⁻¹ := by
  have hN : N ≠ 1 := by
    intro h
    subst N
    exact hchi (Subsingleton.elim _ _)
  rw [characterLBlock_recenter chi hchi]
  calc
    ‖∑ j : ZMod N, chi j *
        (((k * N + j.val : ℕ) : ℂ) ^ (-(1 : ℂ)) -
          (((k + 1) * N : ℕ) : ℂ) ^ (-(1 : ℂ)))‖ ≤
        ∑ j : ZMod N, ‖chi j *
          (((k * N + j.val : ℕ) : ℂ) ^ (-(1 : ℂ)) -
            (((k + 1) * N : ℕ) : ℂ) ^ (-(1 : ℂ)))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _j : ZMod N, (((k : ℝ) ^ 2) * (N : ℝ))⁻¹ := by
      apply Finset.sum_le_sum
      intro j hj
      by_cases hj0 : j = 0
      · subst j
        rw [chi.map_zero' hN]
        simp
        positivity
      · have hjv : j.val ≠ 0 := (ZMod.val_ne_zero j).mpr hj0
        have hxNat : 0 < k * N + j.val := by omega
        have hxyNat : k * N + j.val ≤ (k + 1) * N := by
          have hjlt := j.val_lt
          rw [Nat.add_mul, one_mul]
          omega
        have hlenNat : (k + 1) * N - (k * N + j.val) ≤ N := by
          have hjlt := j.val_lt
          rw [Nat.add_mul, one_mul]
          omega
        have hkN : k * N ≤ k * N + j.val := Nat.le_add_right _ _
        have hx : (0 : ℝ) < (k * N + j.val : ℕ) := by exact_mod_cast hxNat
        have hxy : ((k * N + j.val : ℕ) : ℝ) ≤ ((k + 1) * N : ℕ) := by
          exact_mod_cast hxyNat
        have hlen : (((k + 1) * N : ℕ) : ℝ) - (k * N + j.val : ℕ) ≤ N := by
          rw [← Nat.cast_sub hxyNat]
          exact_mod_cast hlenNat
        have hkNreal : ((k * N : ℕ) : ℝ) ≤ (k * N + j.val : ℕ) := by
          exact_mod_cast hkN
        have hkpos : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk)
        have hNpos : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N
        have hvar := norm_cpow_neg_one_sub_le hx hxy
        rw [norm_mul]
        calc
          ‖chi j‖ * ‖((k * N + j.val : ℕ) : ℂ) ^ (-(1 : ℂ)) -
              (((k + 1) * N : ℕ) : ℂ) ^ (-(1 : ℂ))‖ ≤
              1 * (((((k + 1) * N : ℕ) : ℝ) - (k * N + j.val : ℕ)) /
                ((k * N + j.val : ℕ) : ℝ) ^ 2) := by
            have hvar' :
                ‖((k * N + j.val : ℕ) : ℂ) ^ (-(1 : ℂ)) -
                  (((k + 1) * N : ℕ) : ℂ) ^ (-(1 : ℂ))‖ ≤
                    ((((k + 1) * N : ℕ) : ℝ) - (k * N + j.val : ℕ)) /
                      ((k * N + j.val : ℕ) : ℝ) ^ 2 := by
              rw [show (-(1 : ℂ)) = ((-1 : ℝ) : ℂ) by norm_num]
              simpa only [Complex.ofReal_natCast] using hvar
            exact mul_le_mul (chi.norm_le_one j) hvar'
              (by positivity) (by positivity)
          _ ≤ (N : ℝ) / ((k * N + j.val : ℕ) : ℝ) ^ 2 := by
            simpa using div_le_div_of_nonneg_right hlen (sq_nonneg _)
          _ ≤ (N : ℝ) / ((k * N : ℕ) : ℝ) ^ 2 := by
            have hkNposNat : 0 < k * N := Nat.mul_pos (lt_of_lt_of_le Nat.zero_lt_one hk) (NeZero.pos N)
            have hdenpos : 0 < (((k * N : ℕ) : ℝ) ^ 2) := by
              exact pow_pos (by exact_mod_cast hkNposNat) 2
            have hsq : (((k * N : ℕ) : ℝ) ^ 2) ≤
                (((k * N + j.val : ℕ) : ℝ) ^ 2) := by
              nlinarith [show (0 : ℝ) ≤ (k * N : ℕ) by positivity]
            exact div_le_div_of_nonneg_left hNpos.le hdenpos hsq
          _ = (((k : ℝ) ^ 2) * (N : ℝ))⁻¹ := by
            norm_num [Nat.cast_mul]
            field_simp
    _ = ((k : ℝ) ^ 2)⁻¹ := by
      simp only [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
      have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hk))
      have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne N
      field_simp

end BombieriVinogradov.SiegelWalfisz

end

section

open Set

namespace BombieriVinogradov.SiegelWalfisz

theorem norm_cpow_neg_sub_le {s : ℂ} {x y : ℝ} (hx : 1 ≤ x) (hxy : x ≤ y)
    (hre : (1 / 4 : ℝ) ≤ s.re) (hs : ‖s‖ ≤ (15 / 4 : ℝ)) :
    ‖(x : ℂ) ^ (-s) - (y : ℂ) ^ (-s)‖ ≤
      (15 / 4 : ℝ) * (y - x) * x ^ (-5 / 4 : ℝ) := by
  have hs0 : -s ≠ 0 := by
    intro h
    have : s = 0 := neg_eq_zero.mp h
    subst s
    norm_num at hre
  have hderiv (t : ℝ) (ht : t ∈ Icc x y) :
      HasDerivWithinAt (fun u : ℝ ↦ (u : ℂ) ^ (-s))
        ((-s) * (t : ℂ) ^ (-s - 1)) (Icc x y) t := by
    exact (hasDerivAt_ofReal_cpow_const (ne_of_gt (lt_of_lt_of_le zero_lt_one (hx.trans ht.1)))
      hs0).hasDerivWithinAt
  have hbound (t : ℝ) (ht : t ∈ Icc x y) :
      ‖(-s) * (t : ℂ) ^ (-s - 1)‖ ≤ (15 / 4 : ℝ) * x ^ (-5 / 4 : ℝ) := by
    have htpos : 0 < t := lt_of_lt_of_le zero_lt_one (hx.trans ht.1)
    have hpow_exp : t ^ (-s.re - 1) ≤ t ^ (-5 / 4 : ℝ) := by
      apply Real.rpow_le_rpow_of_exponent_le
      · exact hx.trans ht.1
      · linarith
    have hpow_base : t ^ (-5 / 4 : ℝ) ≤ x ^ (-5 / 4 : ℝ) := by
      exact Real.rpow_le_rpow_of_nonpos (lt_of_lt_of_le zero_lt_one hx) ht.1 (by norm_num)
    rw [norm_mul, norm_neg, Complex.norm_cpow_eq_rpow_re_of_pos htpos]
    exact mul_le_mul hs (hpow_exp.trans hpow_base) (Real.rpow_nonneg htpos.le _) (by norm_num)
  have hmv := (convex_Icc x y : Convex ℝ (Icc x y)).norm_image_sub_le_of_norm_hasDerivWithin_le
    hderiv hbound (left_mem_Icc.mpr hxy) (right_mem_Icc.mpr hxy)
  rw [norm_sub_rev, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hxy)] at hmv
  calc
    ‖(x : ℂ) ^ (-s) - (y : ℂ) ^ (-s)‖
        ≤ ((15 / 4 : ℝ) * x ^ (-5 / 4 : ℝ)) * (y - x) := hmv
    _ = (15 / 4 : ℝ) * (y - x) * x ^ (-5 / 4 : ℝ) := by ring

end BombieriVinogradov.SiegelWalfisz

end

section

namespace BombieriVinogradov.SiegelWalfisz

noncomputable def characterLBlockMajorant (N k : ℕ) : ℝ :=
  (15 / 4 : ℝ) * (N : ℝ) ^ 2 * ((k + 1 : ℕ) : ℝ) ^ (-5 / 4 : ℝ)

theorem norm_characterLBlock_le {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (k : ℕ) {s : ℂ}
    (hs : s ∈ siegelAnalyticDomain) :
    ‖characterLBlock χ k s‖ ≤ characterLBlockMajorant N k := by
  have hN : N ≠ 1 := by
    intro h
    subst N
    exact hχ (Subsingleton.elim _ _)
  rw [characterLBlock_recenter χ hχ]
  calc
    ‖∑ j : ZMod N, χ j *
        (((k * N + j.val : ℕ) : ℂ) ^ (-s) - (((k + 1) * N : ℕ) : ℂ) ^ (-s))‖
        ≤ ∑ j : ZMod N, ‖χ j *
          (((k * N + j.val : ℕ) : ℂ) ^ (-s) - (((k + 1) * N : ℕ) : ℂ) ^ (-s))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _j : ZMod N,
        (15 / 4 : ℝ) * (N : ℝ) * ((k + 1 : ℕ) : ℝ) ^ (-5 / 4 : ℝ) := by
      apply Finset.sum_le_sum
      intro j hj
      by_cases hj0 : j = 0
      · subst j
        rw [χ.map_zero' hN]
        simp only [zero_mul, norm_zero]
        positivity
      · have hjv : j.val ≠ 0 := (ZMod.val_ne_zero j).mpr hj0
        have hxoneNat : 1 ≤ k * N + j.val := by omega
        have hxyNat : k * N + j.val ≤ (k + 1) * N := by
          have hjlt := j.val_lt
          rw [Nat.add_mul, one_mul]
          omega
        have hlenNat : (k + 1) * N - (k * N + j.val) ≤ N := by
          have hjlt := j.val_lt
          rw [Nat.add_mul, one_mul]
          omega
        have hxkNat : k + 1 ≤ k * N + j.val := by
          have hNp := NeZero.pos N
          have hk : k ≤ k * N := by
            simpa using Nat.mul_le_mul_left k hNp
          omega
        have hxone : (1 : ℝ) ≤ (k * N + j.val : ℕ) := by exact_mod_cast hxoneNat
        have hxy : ((k * N + j.val : ℕ) : ℝ) ≤ ((k + 1) * N : ℕ) := by
          exact_mod_cast hxyNat
        have hlen : (((k + 1) * N : ℕ) : ℝ) - (k * N + j.val : ℕ) ≤ N := by
          rw [← Nat.cast_sub hxyNat]
          exact_mod_cast hlenNat
        have hxk : (((k + 1 : ℕ) : ℝ)) ≤ (k * N + j.val : ℕ) := by
          exact_mod_cast hxkNat
        have hpow : ((k * N + j.val : ℕ) : ℝ) ^ (-5 / 4 : ℝ) ≤
            ((k + 1 : ℕ) : ℝ) ^ (-5 / 4 : ℝ) := by
          exact Real.rpow_le_rpow_of_nonpos (by positivity) hxk (by norm_num)
        have hvar := norm_cpow_neg_sub_le hxone hxy
          (le_of_lt (siegelAnalyticDomain_re_lower hs))
          (le_of_lt (siegelAnalyticDomain_norm_upper hs))
        rw [norm_mul]
        calc
          ‖χ j‖ * ‖((k * N + j.val : ℕ) : ℂ) ^ (-s) -
              (((k + 1) * N : ℕ) : ℂ) ^ (-s)‖
              ≤ ‖χ j‖ * ((15 / 4 : ℝ) *
                ((((k + 1) * N : ℕ) : ℝ) - (k * N + j.val : ℕ)) *
                  ((k * N + j.val : ℕ) : ℝ) ^ (-5 / 4 : ℝ)) :=
            mul_le_mul_of_nonneg_left hvar (norm_nonneg _)
          _ ≤ 1 * ((15 / 4 : ℝ) *
                ((((k + 1) * N : ℕ) : ℝ) - (k * N + j.val : ℕ)) *
                  ((k * N + j.val : ℕ) : ℝ) ^ (-5 / 4 : ℝ)) := by
            gcongr
            exact χ.norm_le_one j
          _ = (15 / 4 : ℝ) *
                ((((k + 1) * N : ℕ) : ℝ) - (k * N + j.val : ℕ)) *
                  ((k * N + j.val : ℕ) : ℝ) ^ (-5 / 4 : ℝ) := by ring
          _ ≤ (15 / 4 : ℝ) * (N : ℝ) *
                ((k * N + j.val : ℕ) : ℝ) ^ (-5 / 4 : ℝ) := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hlen (by norm_num)) (Real.rpow_nonneg (by positivity) _)
          _ ≤ (15 / 4 : ℝ) * (N : ℝ) * ((k + 1 : ℕ) : ℝ) ^ (-5 / 4 : ℝ) := by
            exact mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = characterLBlockMajorant N k := by
      simp only [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
      rw [characterLBlockMajorant]
      ring

end BombieriVinogradov.SiegelWalfisz

end

section

namespace BombieriVinogradov.SiegelWalfisz

noncomputable def characterLBlockSeries {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (s : ℂ) : ℂ :=
  ∑' k : ℕ, characterLBlock χ k s

theorem characterLBlockMajorant_summable (N : ℕ) :
    Summable (characterLBlockMajorant N) := by
  have hp : Summable (fun n : ℕ ↦ (n : ℝ) ^ (-5 / 4 : ℝ)) :=
    Real.summable_nat_rpow.mpr (by norm_num)
  have hshift := (summable_nat_add_iff 1).mpr hp
  change Summable (fun k : ℕ ↦
    (15 / 4 : ℝ) * (N : ℝ) ^ 2 * ((k + 1 : ℕ) : ℝ) ^ (-5 / 4 : ℝ))
  exact hshift.mul_left ((15 / 4 : ℝ) * (N : ℝ) ^ 2)

theorem characterLBlockSeries_differentiableOn {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) :
    DifferentiableOn ℂ (characterLBlockSeries χ) siegelAnalyticDomain := by
  change DifferentiableOn ℂ (fun s ↦ ∑' k : ℕ, characterLBlock χ k s)
    siegelAnalyticDomain
  exact Complex.differentiableOn_tsum_of_summable_norm
    (characterLBlockMajorant_summable N)
    (fun k ↦ characterLBlock_differentiableOn χ hχ k)
    (by exact Metric.isOpen_ball)
    (fun k s hs ↦ norm_characterLBlock_le χ hχ k hs)

theorem norm_characterLBlockSeries_le {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) {s : ℂ}
    (hs : s ∈ siegelAnalyticDomain) :
    ‖characterLBlockSeries χ s‖ ≤ ∑' k : ℕ, characterLBlockMajorant N k := by
  rw [characterLBlockSeries]
  exact tsum_of_norm_bounded (characterLBlockMajorant_summable N).hasSum
    (fun k ↦ norm_characterLBlock_le χ hχ k hs)

end BombieriVinogradov.SiegelWalfisz

end

section

namespace BombieriVinogradov.SiegelWalfisz

noncomputable def characterLTailConstant : ℝ :=
  ∑' k : ℕ, ((((k + 1 : ℕ) : ℝ) ^ 2)⁻¹)

theorem characterLTail_summable :
    Summable (fun k : ℕ ↦ ((((k + 1 : ℕ) : ℝ) ^ 2)⁻¹)) := by
  have hp : Summable (fun k : ℕ ↦ (((k : ℝ) ^ 2)⁻¹)) :=
    Real.summable_nat_pow_inv.mpr (by norm_num)
  exact (summable_nat_add_iff 1).mpr hp

theorem characterLTailConstant_nonneg : 0 ≤ characterLTailConstant := by
  rw [characterLTailConstant]
  exact tsum_nonneg fun k ↦ by positivity

theorem characterLBlock_one_norm_summable {N : ℕ} [NeZero N]
    (chi : DirichletCharacter ℂ N) (hchi : chi ≠ 1) :
    Summable (fun k : ℕ ↦ ‖characterLBlock chi k 1‖) := by
  have hs : (1 : ℂ) ∈ siegelAnalyticDomain := by
    rw [siegelAnalyticDomain, Metric.mem_ball]
    norm_num [Complex.dist_eq]
  exact (characterLBlockMajorant_summable N).of_nonneg_of_le
    (fun k ↦ norm_nonneg _) fun k ↦ norm_characterLBlock_le chi hchi k hs

set_option maxHeartbeats 4000000 in
theorem characterLBlock_tail_norm_le {N : ℕ} [NeZero N]
    (chi : DirichletCharacter ℂ N) (hchi : chi ≠ 1) :
    ∑' k : ℕ, ‖characterLBlock chi (k + 1) 1‖ ≤ characterLTailConstant := by
  have hnorm := characterLBlock_one_norm_summable chi hchi
  have htailNorm : Summable (fun k : ℕ ↦ ‖characterLBlock chi (k + 1) 1‖) :=
    (summable_nat_add_iff 1).mpr hnorm
  rw [characterLTailConstant]
  exact htailNorm.tsum_le_tsum
    (fun k ↦ norm_characterLBlock_one_le chi hchi (Nat.le_add_left 1 k))
    characterLTail_summable

theorem norm_characterLBlockSeries_one_le {N : ℕ} [NeZero N]
    (chi : DirichletCharacter ℂ N) (hchi : chi ≠ 1) :
    ‖characterLBlockSeries chi 1‖ ≤
      2 * (1 + Real.log N) + characterLTailConstant := by
  have hnorm := characterLBlock_one_norm_summable chi hchi
  rw [characterLBlockSeries]
  calc
    ‖∑' k : ℕ, characterLBlock chi k 1‖ ≤
        ∑' k : ℕ, ‖characterLBlock chi k 1‖ :=
      norm_tsum_le_tsum_norm hnorm
    _ = ‖characterLBlock chi 0 1‖ +
        ∑' k : ℕ, ‖characterLBlock chi (k + 1) 1‖ := hnorm.tsum_eq_zero_add
    _ ≤ 2 * (1 + Real.log N) + characterLTailConstant :=
      add_le_add (norm_characterLBlock_zero_one_le chi hchi)
        (characterLBlock_tail_norm_le chi hchi)

end BombieriVinogradov.SiegelWalfisz

end

section

open Complex Filter LSeries Metric Set Topology

namespace BombieriVinogradov.SiegelWalfisz

theorem LFunction_eq_characterLBlockSeries_of_one_lt_re {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) {s : ℂ} (hs : 1 < s.re) :
    χ.LFunction s = characterLBlockSeries χ s := by
  have hN : N ≠ 1 := by
    intro h
    subst N
    exact hχ (Subsingleton.elim _ _)
  have hzero : (fun n : ℕ ↦ χ n) 0 = 0 := by
    simpa using χ.map_zero' hN
  have hsum : Summable (fun n : ℕ ↦ χ n * (n : ℂ) ^ (-s)) := by
    rw [← funext (LSeries.term_def₀ hzero s)]
    exact DirichletCharacter.LSeriesSummable_of_one_lt_re χ hs
  have hterm (j : ZMod N) (k : ℕ) :
      χ ((j.val + N * k : ℕ) : ZMod N) * ((j.val + N * k : ℕ) : ℂ) ^ (-s) =
        χ j * ((k * N + j.val : ℕ) : ℂ) ^ (-s) := by
    have hcast : ((j.val + N * k : ℕ) : ZMod N) = j := by
      simp [Nat.cast_add, Nat.cast_mul]
    rw [hcast]
    congr 2
    simp only [Nat.add_comm, Nat.mul_comm]
  have hsub (j : ZMod N) :
      Summable (fun k : ℕ ↦ χ j * ((k * N + j.val : ℕ) : ℂ) ^ (-s)) := by
    have hinj : Function.Injective (fun k : ℕ ↦ j.val + N * k) := by
      intro a b hab
      exact Nat.mul_left_cancel (NeZero.pos N) (Nat.add_left_cancel hab)
    have h := hsum.comp_injective hinj
    exact h.congr (hterm j)
  have hswap := Summable.tsum_finsetSum (s := Finset.univ)
    (fun j _hj ↦ hsub j)
  calc
    χ.LFunction s = LSeries (χ ·) s := DirichletCharacter.LFunction_eq_LSeries χ hs
    _ = ∑' n : ℕ, χ n * (n : ℂ) ^ (-s) := by
      rw [LSeries_def₀ hzero]
      congr 1
      funext n
      rw [Complex.cpow_neg, div_eq_mul_inv]
    _ = ∑ j : ZMod N, ∑' k : ℕ,
        χ ((j.val + N * k : ℕ) : ZMod N) * ((j.val + N * k : ℕ) : ℂ) ^ (-s) :=
      Nat.sumByResidueClasses hsum N
    _ = ∑ j : ZMod N, ∑' k : ℕ,
        χ j * ((k * N + j.val : ℕ) : ℂ) ^ (-s) := by
      apply Finset.sum_congr rfl
      intro j hj
      exact tsum_congr (hterm j)
    _ = ∑' k : ℕ, ∑ j : ZMod N,
        χ j * ((k * N + j.val : ℕ) : ℂ) ^ (-s) := by
      simpa only [Finset.mem_univ, ↓reduceIte] using hswap.symm
    _ = characterLBlockSeries χ s := rfl

theorem LFunction_eq_characterLBlockSeries {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) {s : ℂ}
    (hs : s ∈ siegelAnalyticDomain) : χ.LFunction s = characterLBlockSeries χ s := by
  have hL : AnalyticOnNhd ℂ (χ.LFunction) siegelAnalyticDomain :=
    (DirichletCharacter.differentiable_LFunction hχ).differentiableOn.analyticOnNhd
      Metric.isOpen_ball
  have hB : AnalyticOnNhd ℂ (characterLBlockSeries χ) siegelAnalyticDomain :=
    (characterLBlockSeries_differentiableOn χ hχ).analyticOnNhd Metric.isOpen_ball
  have h2 : (2 : ℂ) ∈ siegelAnalyticDomain := by
    rw [siegelAnalyticDomain, mem_ball]
    norm_num
  have heq : χ.LFunction =ᶠ[𝓝 (2 : ℂ)] characterLBlockSeries χ := by
    have hV : {z : ℂ | 1 < z.re} ∈ 𝓝 (2 : ℂ) :=
      (continuous_re.isOpen_preimage _ isOpen_Ioi).mem_nhds (by norm_num)
    filter_upwards [hV] with z hz
    exact LFunction_eq_characterLBlockSeries_of_one_lt_re χ hχ hz
  exact hL.eqOn_of_preconnected_of_eventuallyEq hB
    (convex_ball (2 : ℂ) (7 / 4 : ℝ)).isPreconnected h2 heq hs

end BombieriVinogradov.SiegelWalfisz

end

section

open Metric Set

namespace BombieriVinogradov.SiegelWalfisz

noncomputable def characterLLogBoundConstant : ℝ :=
  2 + characterLTailConstant

theorem characterLLogBoundConstant_pos : 0 < characterLLogBoundConstant := by
  rw [characterLLogBoundConstant]
  linarith [characterLTailConstant_nonneg]

theorem norm_LFunction_one_le_log {N : ℕ} [NeZero N]
    (chi : DirichletCharacter ℂ N) (hchi : chi ≠ 1) :
    ‖chi.LFunction 1‖ ≤ characterLLogBoundConstant * (1 + Real.log N) := by
  have hs : (1 : ℂ) ∈ siegelAnalyticDomain := by
    rw [siegelAnalyticDomain, mem_ball]
    norm_num [Complex.dist_eq]
  have hlog : 1 ≤ 1 + Real.log N := by
    have hN : (1 : ℝ) ≤ N := by exact_mod_cast NeZero.pos N
    linarith [Real.log_nonneg hN]
  rw [LFunction_eq_characterLBlockSeries chi hchi hs]
  calc
    ‖characterLBlockSeries chi 1‖ ≤
        2 * (1 + Real.log N) + characterLTailConstant :=
      norm_characterLBlockSeries_one_le chi hchi
    _ ≤ characterLLogBoundConstant * (1 + Real.log N) := by
      rw [characterLLogBoundConstant]
      nlinarith [characterLTailConstant_nonneg]

end BombieriVinogradov.SiegelWalfisz

end

section

open Metric Set

namespace BombieriVinogradov.SiegelWalfisz

noncomputable def characterLAbsoluteMajorant (k : ℕ) : ℝ :=
  (15 / 4 : ℝ) * ((k + 1 : ℕ) : ℝ) ^ (-5 / 4 : ℝ)

noncomputable def characterLBoundConstant : ℝ :=
  1 + ∑' k : ℕ, characterLAbsoluteMajorant k

theorem characterLBoundConstant_pos : 0 < characterLBoundConstant := by
  have hnon : 0 ≤ ∑' k : ℕ, characterLAbsoluteMajorant k := by
    apply tsum_nonneg
    intro k
    rw [characterLAbsoluteMajorant]
    positivity
  rw [characterLBoundConstant]
  linarith

theorem norm_LFunction_le_square_on_analyticDomain {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) {s : ℂ}
    (hs : s ∈ siegelAnalyticDomain) :
    ‖χ.LFunction s‖ ≤ characterLBoundConstant * (N : ℝ) ^ 2 := by
  rw [LFunction_eq_characterLBlockSeries χ hχ hs]
  apply (norm_characterLBlockSeries_le χ hχ hs).trans
  calc
    ∑' k : ℕ, characterLBlockMajorant N k =
        (N : ℝ) ^ 2 * ∑' k : ℕ, characterLAbsoluteMajorant k := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro k
      rw [characterLAbsoluteMajorant, characterLBlockMajorant]
      ring
    _ ≤ characterLBoundConstant * (N : ℝ) ^ 2 := by
      rw [mul_comm characterLBoundConstant]
      apply mul_le_mul_of_nonneg_left
      · rw [characterLBoundConstant]
        linarith
      · positivity


theorem norm_LFunction_one_le_square {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) :
    ‖χ.LFunction 1‖ ≤ characterLBoundConstant * (N : ℝ) ^ 2 := by
  apply norm_LFunction_le_square_on_analyticDomain χ hχ
  rw [siegelAnalyticDomain, mem_ball]
  norm_num [Complex.dist_eq]

end BombieriVinogradov.SiegelWalfisz

end

section

open ArithmeticFunction

namespace BombieriVinogradov.SiegelWalfisz

theorem arithmeticFunction_mul_apply_primePower (f g : ArithmeticFunction ℂ)
    {p r : ℕ} (hp : p.Prime) :
    (f * g) (p ^ r) = ∑ i ∈ Finset.range (r + 1), f (p ^ i) * g (p ^ (r - i)) := by
  rw [ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal (fun x y ↦ f x * g y),
    Nat.sum_divisors_prime_pow hp]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Nat.pow_div (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) hp.pos]

noncomputable def characterPairArithmetic {N M : ℕ} (χ : DirichletCharacter ℂ N)
    (ψ : DirichletCharacter ℂ M) : ArithmeticFunction ℂ :=
  toArithmeticFunction fun n ↦ χ n * ψ n

theorem toArithmeticFunction_apply_of_ne_zero (f : ℕ → ℂ) {n : ℕ} (hn : n ≠ 0) :
    toArithmeticFunction f n = f n := by
  simp [toArithmeticFunction, hn]

theorem characterPairArithmetic_isMultiplicative {N M : ℕ}
    (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ M) :
    (characterPairArithmetic χ ψ).IsMultiplicative := by
  refine ArithmeticFunction.IsMultiplicative.iff_ne_zero.mpr ⟨?_, fun {m n} hm hn _ ↦ ?_⟩
  · simp [characterPairArithmetic, toArithmeticFunction]
  · simp [characterPairArithmetic, toArithmeticFunction, hm, hn, map_mul]
    ring

theorem arithmeticZeta_primePower {p i : ℕ} (hp : p.Prime) :
    (ArithmeticFunction.zeta : ArithmeticFunction ℂ) (p ^ i) = 1 := by
  simp [hp.ne_zero]

theorem characterArithmetic_primePower {N : ℕ} (χ : DirichletCharacter ℂ N)
    {p i : ℕ} (hp : p.Prime) :
    toArithmeticFunction (χ ·) (p ^ i) = (χ p) ^ i := by
  rw [← χ.apply_eq_toArithmeticFunction_apply (pow_ne_zero i hp.ne_zero), Nat.cast_pow,
    map_pow]

theorem characterPairArithmetic_primePower {N M : ℕ}
    (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ M)
    {p i : ℕ} (hp : p.Prime) :
    characterPairArithmetic χ ψ (p ^ i) = (χ p * ψ p) ^ i := by
  have hpPow : p ^ i ≠ 0 := pow_ne_zero i hp.ne_zero
  rw [characterPairArithmetic, toArithmeticFunction_apply_of_ne_zero _ hpPow]
  simp only [Nat.cast_pow, map_pow, mul_pow]

noncomputable def siegelProductCoefficients {N M : ℕ} (χ : DirichletCharacter ℂ N)
    (ψ : DirichletCharacter ℂ M) : ArithmeticFunction ℂ :=
  ArithmeticFunction.zeta * toArithmeticFunction (χ ·) * toArithmeticFunction (ψ ·) *
    characterPairArithmetic χ ψ

theorem siegelProductCoefficients_isMultiplicative {N M : ℕ}
    (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ M) :
    (siegelProductCoefficients χ ψ).IsMultiplicative := by
  exact (((isMultiplicative_zeta.natCast.mul χ.isMultiplicative_toArithmeticFunction).mul
    ψ.isMultiplicative_toArithmeticFunction).mul (characterPairArithmetic_isMultiplicative χ ψ))

theorem siegelProductCoefficients_grouped {N M : ℕ}
    (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ M) :
    siegelProductCoefficients χ ψ =
      ((ArithmeticFunction.zeta : ArithmeticFunction ℂ) * toArithmeticFunction (χ ·)) *
        (toArithmeticFunction (ψ ·) * characterPairArithmetic χ ψ) := by
  rw [siegelProductCoefficients, mul_assoc]

theorem siegelProductCoefficients_grouped_swap {N M : ℕ}
    (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ M) :
    siegelProductCoefficients χ ψ =
      ((ArithmeticFunction.zeta : ArithmeticFunction ℂ) * toArithmeticFunction (ψ ·)) *
        (toArithmeticFunction (χ ·) * characterPairArithmetic χ ψ) := by
  rw [siegelProductCoefficients]
  ring


end BombieriVinogradov.SiegelWalfisz

end

section

open ArithmeticFunction
open scoped ComplexOrder

namespace BombieriVinogradov.SiegelWalfisz

noncomputable def localPairCoefficient (a b : ℂ) (r : ℕ) : ℂ :=
  ∑ i ∈ Finset.range (r + 1), a ^ i * b ^ (r - i)

theorem arithmeticFunction_mul_apply_primePower_eq_localPair
    (f g : ArithmeticFunction ℂ) (a b : ℂ) {p r : ℕ} (hp : p.Prime)
    (hf : ∀ i : ℕ, f (p ^ i) = a ^ i) (hg : ∀ i : ℕ, g (p ^ i) = b ^ i) :
    (f * g) (p ^ r) = localPairCoefficient a b r := by
  rw [arithmeticFunction_mul_apply_primePower f g hp, localPairCoefficient]
  apply Finset.sum_congr rfl
  intro i _
  rw [hf, hg]

theorem localPairCoefficient_comm (a b : ℂ) (r : ℕ) :
    localPairCoefficient a b r = localPairCoefficient b a r := by
  simpa [localPairCoefficient] using (Commute.all a b).geom_sum₂_comm (r + 1)

theorem localPairCoefficient_one_left_eq_geom (b : ℂ) (r : ℕ) :
    localPairCoefficient 1 b r = ∑ i ∈ Finset.range (r + 1), b ^ i := by
  calc
    localPairCoefficient 1 b r = localPairCoefficient b 1 r :=
      localPairCoefficient_comm 1 b r
    _ = ∑ i ∈ Finset.range (r + 1), b ^ i := by
      simp [localPairCoefficient]

theorem localPairCoefficient_one_left_nonneg (b : ℂ)
    (hb : b = 0 ∨ b = 1 ∨ b = -1) (r : ℕ) :
    0 ≤ localPairCoefficient 1 b r := by
  rw [localPairCoefficient_one_left_eq_geom]
  rcases hb with rfl | rfl | rfl
  · simp [zero_geom_sum]
  · simp only [one_geom_sum]
    exact_mod_cast Nat.zero_le (r + 1)
  · rw [neg_one_geom_sum]
    split_ifs <;> simp

theorem localPairCoefficient_one_right_nonneg (a : ℂ)
    (ha : a = 0 ∨ a = 1 ∨ a = -1) (r : ℕ) :
    0 ≤ localPairCoefficient a 1 r := by
  rw [localPairCoefficient_comm]
  exact localPairCoefficient_one_left_nonneg a ha r

theorem localPairCoefficient_zero_zero_nonneg (r : ℕ) :
    0 ≤ localPairCoefficient 0 0 r := by
  cases r with
  | zero => simp [localPairCoefficient]
  | succ r =>
      rw [localPairCoefficient]
      apply Finset.sum_nonneg
      intro i hi
      rcases eq_or_ne i 0 with rfl | hi0
      · simp
      · simp [zero_pow hi0]

theorem zeta_mul_character_primePower {N : ℕ} (χ : DirichletCharacter ℂ N)
    {p r : ℕ} (hp : p.Prime) :
    ((ArithmeticFunction.zeta : ArithmeticFunction ℂ) * toArithmeticFunction (χ ·))
        (p ^ r) = localPairCoefficient 1 (χ p) r :=
  arithmeticFunction_mul_apply_primePower_eq_localPair _ _ _ _ hp
    (fun _ ↦ by simpa using arithmeticZeta_primePower hp)
    (fun _ ↦ characterArithmetic_primePower χ hp)

theorem character_mul_pair_primePower {N M : ℕ}
    (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ M)
    {p r : ℕ} (hp : p.Prime) :
    (toArithmeticFunction (χ ·) * characterPairArithmetic χ ψ) (p ^ r) =
      localPairCoefficient (χ p) (χ p * ψ p) r :=
  arithmeticFunction_mul_apply_primePower_eq_localPair _ _ _ _ hp
    (fun _ ↦ characterArithmetic_primePower χ hp)
    (fun _ ↦ characterPairArithmetic_primePower χ ψ hp)

theorem character_right_mul_pair_primePower {N M : ℕ}
    (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ M)
    {p r : ℕ} (hp : p.Prime) :
    (toArithmeticFunction (ψ ·) * characterPairArithmetic χ ψ) (p ^ r) =
      localPairCoefficient (ψ p) (χ p * ψ p) r :=
  arithmeticFunction_mul_apply_primePower_eq_localPair _ _ _ _ hp
    (fun _ ↦ characterArithmetic_primePower ψ hp)
    (fun _ ↦ characterPairArithmetic_primePower χ ψ hp)

end BombieriVinogradov.SiegelWalfisz

end

section

open ArithmeticFunction
open scoped ComplexOrder

namespace BombieriVinogradov.SiegelWalfisz

theorem siegelProductCoefficients_primePower_nonneg {N M : ℕ}
    (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ M)
    (hχ : χ ^ 2 = 1) (hψ : ψ ^ 2 = 1) {p r : ℕ} (hp : p.Prime) :
    0 ≤ siegelProductCoefficients χ ψ (p ^ r) := by
  rcases quadraticValue_cases χ hχ p with hχp | hχp | hχp
  · rw [siegelProductCoefficients_grouped_swap,
      arithmeticFunction_mul_apply_primePower _ _ hp]
    apply Finset.sum_nonneg
    intro i hi
    apply mul_nonneg
    · rw [zeta_mul_character_primePower ψ hp]
      exact localPairCoefficient_one_left_nonneg _ (quadraticValue_cases ψ hψ p) i
    · rw [character_mul_pair_primePower χ ψ hp, hχp, zero_mul]
      exact localPairCoefficient_zero_zero_nonneg (r - i)
  · rw [siegelProductCoefficients_grouped_swap,
      arithmeticFunction_mul_apply_primePower _ _ hp]
    apply Finset.sum_nonneg
    intro i hi
    apply mul_nonneg
    · rw [zeta_mul_character_primePower ψ hp]
      exact localPairCoefficient_one_left_nonneg _ (quadraticValue_cases ψ hψ p) i
    · rw [character_mul_pair_primePower χ ψ hp, hχp, one_mul]
      exact localPairCoefficient_one_left_nonneg _ (quadraticValue_cases ψ hψ p) (r - i)
  · rw [siegelProductCoefficients_grouped,
      arithmeticFunction_mul_apply_primePower _ _ hp]
    apply Finset.sum_nonneg
    intro i hi
    apply mul_nonneg
    · rw [zeta_mul_character_primePower χ hp, hχp]
      exact localPairCoefficient_one_left_nonneg (-1) (Or.inr (Or.inr rfl)) i
    · rw [character_right_mul_pair_primePower χ ψ hp, hχp]
      rcases quadraticValue_cases ψ hψ p with hψp | hψp | hψp
      · rw [hψp]
        norm_num
        exact localPairCoefficient_zero_zero_nonneg (r - i)
      · rw [hψp]
        norm_num
        exact localPairCoefficient_one_left_nonneg (-1) (Or.inr (Or.inr rfl)) (r - i)
      · rw [hψp]
        norm_num
        exact localPairCoefficient_one_right_nonneg (-1) (Or.inr (Or.inr rfl)) (r - i)

end BombieriVinogradov.SiegelWalfisz

end

section

open scoped ComplexOrder

namespace BombieriVinogradov.SiegelWalfisz

theorem siegelProductCoefficients_nonneg {N M : ℕ}
    (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ M)
    (hχ : χ ^ 2 = 1) (hψ : ψ ^ 2 = 1) (n : ℕ) :
    0 ≤ siegelProductCoefficients χ ψ n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp only [ArithmeticFunction.map_zero, le_refl]
  · simpa only [(siegelProductCoefficients_isMultiplicative χ ψ).multiplicative_factorization
      _ hn] using!
      Finset.prod_nonneg fun p hp ↦
        siegelProductCoefficients_primePower_nonneg χ ψ hχ hψ
          (Nat.prime_of_mem_primeFactors hp)

theorem siegelProductCoefficients_one {N M : ℕ}
    (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ M) :
    siegelProductCoefficients χ ψ 1 = 1 :=
  (siegelProductCoefficients_isMultiplicative χ ψ).map_one

end BombieriVinogradov.SiegelWalfisz

end

section

namespace BombieriVinogradov.SiegelWalfisz

theorem crossLevelMul_apply_nat {N M : ℕ} (χ : DirichletCharacter ℂ N)
    (ψ : DirichletCharacter ℂ M) (n : ℕ) :
    DirichletCharacter.mul χ ψ n = χ n * ψ n := by
  rw [DirichletCharacter.mul, MulChar.mul_apply]
  by_cases hN : n.Coprime N
  · by_cases hM : n.Coprime M
    · have hLcm : n.Coprime (N.lcm M) :=
        Nat.Coprime.of_dvd_right (Nat.lcm_dvd_mul N M) (hN.mul_right hM)
      have hLcmInt : IsCoprime (n : ℤ) (N.lcm M) :=
        Nat.isCoprime_iff_coprime.mpr hLcm
      have hχEval :
          DirichletCharacter.changeLevel (Nat.dvd_lcm_left N M) χ n = χ n := by
        simpa using DirichletCharacter.changeLevel_eq_cast_of_dvd' χ _ hLcmInt
      have hψEval :
          DirichletCharacter.changeLevel (Nat.dvd_lcm_right N M) ψ n = ψ n := by
        simpa using DirichletCharacter.changeLevel_eq_cast_of_dvd' ψ _ hLcmInt
      rw [hχEval, hψEval]
    · have hLcm : ¬n.Coprime (N.lcm M) := fun h ↦
        hM (Nat.Coprime.of_dvd_right (Nat.dvd_lcm_right N M) h)
      have hLcmInt : ¬IsCoprime (n : ℤ) (N.lcm M) := fun h ↦
        hLcm (Nat.isCoprime_iff_coprime.mp h)
      have hMInt : ¬IsCoprime (n : ℤ) M := fun h ↦
        hM (Nat.isCoprime_iff_coprime.mp h)
      have hLiftZero :
          DirichletCharacter.changeLevel (Nat.dvd_lcm_right N M) ψ n = 0 := by
        simpa using (DirichletCharacter.apply_eq_zero_iff _ _).mpr hLcmInt
      have hZero : ψ n = 0 := by
        simpa using (DirichletCharacter.apply_eq_zero_iff _ _).mpr hMInt
      rw [hLiftZero, hZero, mul_zero, mul_zero]
  · have hLcm : ¬n.Coprime (N.lcm M) := fun h ↦
      hN (Nat.Coprime.of_dvd_right (Nat.dvd_lcm_left N M) h)
    have hLcmInt : ¬IsCoprime (n : ℤ) (N.lcm M) := fun h ↦
      hLcm (Nat.isCoprime_iff_coprime.mp h)
    have hNInt : ¬IsCoprime (n : ℤ) N := fun h ↦
      hN (Nat.isCoprime_iff_coprime.mp h)
    have hLiftZero :
        DirichletCharacter.changeLevel (Nat.dvd_lcm_left N M) χ n = 0 := by
      simpa using (DirichletCharacter.apply_eq_zero_iff _ _).mpr hLcmInt
    have hZero : χ n = 0 := by
      simpa using (DirichletCharacter.apply_eq_zero_iff _ _).mpr hNInt
    rw [hLiftZero, hZero, zero_mul, zero_mul]

end BombieriVinogradov.SiegelWalfisz

end

section

open ArithmeticFunction
open LSeries

namespace BombieriVinogradov.SiegelWalfisz

theorem characterPairArithmetic_eq_crossLevel {N M : ℕ}
    (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ M) :
    characterPairArithmetic χ ψ =
      toArithmeticFunction (DirichletCharacter.mul χ ψ ·) := by
  rw [characterPairArithmetic]
  apply toArithmeticFunction_congr
  intro n _
  exact (crossLevelMul_apply_nat χ ψ n).symm

theorem characterArithmetic_LSeriesSummable {N : ℕ}
    (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (toArithmeticFunction (χ ·)) s := by
  exact (LSeriesSummable_congr s fun hn ↦
    (χ.apply_eq_toArithmeticFunction_apply hn).symm).mpr
      (DirichletCharacter.LSeriesSummable_of_one_lt_re χ hs)

theorem characterPairArithmetic_LSeriesSummable {N M : ℕ}
    (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ M)
    {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (characterPairArithmetic χ ψ) s := by
  rw [characterPairArithmetic_eq_crossLevel]
  exact characterArithmetic_LSeriesSummable (DirichletCharacter.mul χ ψ) hs

theorem siegelProductCoefficients_LSeriesSummable {N M : ℕ}
    (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ M)
    {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (siegelProductCoefficients χ ψ) s := by
  rw [siegelProductCoefficients]
  exact ArithmeticFunction.LSeriesSummable_mul
    (ArithmeticFunction.LSeriesSummable_mul
      (ArithmeticFunction.LSeriesSummable_mul
        (ArithmeticFunction.LSeriesSummable_zeta_iff.mpr hs)
        (characterArithmetic_LSeriesSummable χ hs))
      (characterArithmetic_LSeriesSummable ψ hs))
    (characterPairArithmetic_LSeriesSummable χ ψ hs)

end BombieriVinogradov.SiegelWalfisz

end

section

open ArithmeticFunction
open LSeries

namespace BombieriVinogradov.SiegelWalfisz

theorem characterArithmetic_LSeries_eq_LFunction {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 1 < s.re) :
    LSeries (toArithmeticFunction (χ ·)) s = χ.LFunction s := by
  rw [LSeries_congr (fun hn ↦ (χ.apply_eq_toArithmeticFunction_apply hn).symm) s]
  exact (DirichletCharacter.LFunction_eq_LSeries χ hs).symm

theorem characterPairArithmetic_LSeries_eq_LFunction {N M : ℕ} [NeZero N] [NeZero M]
    [NeZero (N.lcm M)]
    (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ M)
    {s : ℂ} (hs : 1 < s.re) :
    LSeries (characterPairArithmetic χ ψ) s =
      (DirichletCharacter.mul χ ψ).LFunction s := by
  rw [characterPairArithmetic_eq_crossLevel]
  exact characterArithmetic_LSeries_eq_LFunction (DirichletCharacter.mul χ ψ) hs

theorem siegelProduct_LSeries_eq {N M : ℕ} [NeZero N] [NeZero M]
    [NeZero (N.lcm M)]
    (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ M)
    {s : ℂ} (hs : 1 < s.re) :
    LSeries (siegelProductCoefficients χ ψ) s =
      riemannZeta s * χ.LFunction s * ψ.LFunction s *
        (DirichletCharacter.mul χ ψ).LFunction s := by
  have hzeta : LSeriesSummable (ArithmeticFunction.zeta : ArithmeticFunction ℂ) s :=
    ArithmeticFunction.LSeriesSummable_zeta_iff.mpr hs
  have hχ := characterArithmetic_LSeriesSummable χ hs
  have hψ := characterArithmetic_LSeriesSummable ψ hs
  have hpair := characterPairArithmetic_LSeriesSummable χ ψ hs
  rw [siegelProductCoefficients,
    ArithmeticFunction.LSeries_mul'
      (ArithmeticFunction.LSeriesSummable_mul
        (ArithmeticFunction.LSeriesSummable_mul hzeta hχ) hψ) hpair,
    ArithmeticFunction.LSeries_mul'
      (ArithmeticFunction.LSeriesSummable_mul hzeta hχ) hψ,
    ArithmeticFunction.LSeries_mul' hzeta hχ,
    characterArithmetic_LSeries_eq_LFunction χ hs,
    characterArithmetic_LSeries_eq_LFunction ψ hs,
    characterPairArithmetic_LSeries_eq_LFunction χ ψ hs]
  simp_rw [← ArithmeticFunction.LSeries_zeta_eq_riemannZeta hs,
    ← ArithmeticFunction.natCoe_apply]

end BombieriVinogradov.SiegelWalfisz

end

section

namespace BombieriVinogradov.SiegelWalfisz

noncomputable def siegelLProduct {N M : ℕ} [NeZero N] [NeZero M] [NeZero (N.lcm M)]
    (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ M) (s : ℂ) : ℂ :=
  χ.LFunction s * ψ.LFunction s * (DirichletCharacter.mul χ ψ).LFunction s

noncomputable def siegelProductResidue {N M : ℕ} [NeZero N] [NeZero M]
    [NeZero (N.lcm M)] (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ M) : ℂ :=
  χ.LFunction 1 * ψ.LFunction 1 * (DirichletCharacter.mul χ ψ).LFunction 1

theorem siegelLProduct_differentiable {N M : ℕ} [NeZero N] [NeZero M]
    [NeZero (N.lcm M)] (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ M)
    (hχ : χ ≠ 1) (hψ : ψ ≠ 1) (hmul : DirichletCharacter.mul χ ψ ≠ 1) :
    Differentiable ℂ (siegelLProduct χ ψ) := by
  exact ((DirichletCharacter.differentiable_LFunction hχ).mul
    (DirichletCharacter.differentiable_LFunction hψ)).mul
      (DirichletCharacter.differentiable_LFunction hmul)

theorem siegelLProduct_one {N M : ℕ} [NeZero N] [NeZero M] [NeZero (N.lcm M)]
    (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ M) :
    siegelLProduct χ ψ 1 = siegelProductResidue χ ψ :=
  rfl

end BombieriVinogradov.SiegelWalfisz

end

section

namespace BombieriVinogradov.SiegelWalfisz

noncomputable def siegelResidueBoundConstant : ℝ := characterLBoundConstant ^ 3

theorem siegelResidueBoundConstant_pos : 0 < siegelResidueBoundConstant := by
  rw [siegelResidueBoundConstant]
  exact pow_pos characterLBoundConstant_pos 3

theorem norm_siegelProductResidue_le {N M : ℕ} [NeZero N] [NeZero M]
    [NeZero (N.lcm M)] (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ M)
    (hχ : χ ≠ 1) (hψ : ψ ≠ 1) (hmul : DirichletCharacter.mul χ ψ ≠ 1) :
    ‖siegelProductResidue χ ψ‖ ≤
      siegelResidueBoundConstant * ((N : ℝ) * (M : ℝ)) ^ 4 := by
  have hχb := norm_LFunction_one_le_square χ hχ
  have hψb := norm_LFunction_one_le_square ψ hψ
  have hmulb := norm_LFunction_one_le_square (DirichletCharacter.mul χ ψ) hmul
  have hC : 0 ≤ characterLBoundConstant := characterLBoundConstant_pos.le
  have hNMpos : 0 < N * M := Nat.mul_pos (NeZero.pos N) (NeZero.pos M)
  have hlcmNat : N.lcm M ≤ N * M := Nat.le_of_dvd hNMpos (Nat.lcm_dvd_mul N M)
  have hlcm : ((N.lcm M : ℕ) : ℝ) ≤ (N : ℝ) * (M : ℝ) := by
    exact_mod_cast hlcmNat
  have hlcmSq : ((N.lcm M : ℕ) : ℝ) ^ 2 ≤ ((N : ℝ) * (M : ℝ)) ^ 2 := by
    gcongr
  rw [siegelProductResidue, norm_mul, norm_mul]
  calc
    ‖χ.LFunction 1‖ * ‖ψ.LFunction 1‖ * ‖(DirichletCharacter.mul χ ψ).LFunction 1‖
        ≤ (characterLBoundConstant * (N : ℝ) ^ 2) *
            (characterLBoundConstant * (M : ℝ) ^ 2) *
              (characterLBoundConstant * ((N.lcm M : ℕ) : ℝ) ^ 2) := by
      have hχψ : ‖χ.LFunction 1‖ * ‖ψ.LFunction 1‖ ≤
          (characterLBoundConstant * (N : ℝ) ^ 2) *
            (characterLBoundConstant * (M : ℝ) ^ 2) := by
        exact mul_le_mul hχb hψb (norm_nonneg _) (mul_nonneg hC (sq_nonneg _))
      exact mul_le_mul hχψ hmulb (norm_nonneg _) (mul_nonneg
        (mul_nonneg hC (sq_nonneg _)) (mul_nonneg hC (sq_nonneg _)))
    _ = characterLBoundConstant ^ 3 * ((N : ℝ) * (M : ℝ)) ^ 2 *
          ((N.lcm M : ℕ) : ℝ) ^ 2 := by ring
    _ ≤ characterLBoundConstant ^ 3 * ((N : ℝ) * (M : ℝ)) ^ 2 *
          ((N : ℝ) * (M : ℝ)) ^ 2 := by
      exact mul_le_mul_of_nonneg_left hlcmSq
        (mul_nonneg (pow_nonneg hC _) (sq_nonneg _))
    _ = siegelResidueBoundConstant * ((N : ℝ) * (M : ℝ)) ^ 4 := by
      rw [siegelResidueBoundConstant]
      ring

end BombieriVinogradov.SiegelWalfisz

end

section

namespace BombieriVinogradov.SiegelWalfisz

theorem norm_siegelLProduct_le {N M : ℕ} [NeZero N] [NeZero M]
    [NeZero (N.lcm M)] (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ M)
    (hχ : χ ≠ 1) (hψ : ψ ≠ 1) (hmul : DirichletCharacter.mul χ ψ ≠ 1)
    {s : ℂ} (hs : s ∈ siegelCauchyCircle) :
    ‖siegelLProduct χ ψ s‖ ≤
      siegelResidueBoundConstant * ((N : ℝ) * (M : ℝ)) ^ 4 := by
  have hsDomain := siegelCauchyCircle_subset_analyticDomain hs
  have hχb := norm_LFunction_le_square_on_analyticDomain χ hχ hsDomain
  have hψb := norm_LFunction_le_square_on_analyticDomain ψ hψ hsDomain
  have hmulb := norm_LFunction_le_square_on_analyticDomain
    (DirichletCharacter.mul χ ψ) hmul hsDomain
  have hC : 0 ≤ characterLBoundConstant := characterLBoundConstant_pos.le
  have hNMpos : 0 < N * M := Nat.mul_pos (NeZero.pos N) (NeZero.pos M)
  have hlcmNat : N.lcm M ≤ N * M := Nat.le_of_dvd hNMpos (Nat.lcm_dvd_mul N M)
  have hlcm : ((N.lcm M : ℕ) : ℝ) ≤ (N : ℝ) * (M : ℝ) := by
    exact_mod_cast hlcmNat
  have hlcmSq : ((N.lcm M : ℕ) : ℝ) ^ 2 ≤ ((N : ℝ) * (M : ℝ)) ^ 2 := by
    gcongr
  rw [siegelLProduct, norm_mul, norm_mul]
  calc
    ‖χ.LFunction s‖ * ‖ψ.LFunction s‖ * ‖(DirichletCharacter.mul χ ψ).LFunction s‖
        ≤ (characterLBoundConstant * (N : ℝ) ^ 2) *
            (characterLBoundConstant * (M : ℝ) ^ 2) *
              (characterLBoundConstant * ((N.lcm M : ℕ) : ℝ) ^ 2) := by
      have hχψ : ‖χ.LFunction s‖ * ‖ψ.LFunction s‖ ≤
          (characterLBoundConstant * (N : ℝ) ^ 2) *
            (characterLBoundConstant * (M : ℝ) ^ 2) := by
        exact mul_le_mul hχb hψb (norm_nonneg _) (mul_nonneg hC (sq_nonneg _))
      exact mul_le_mul hχψ hmulb (norm_nonneg _) (mul_nonneg
        (mul_nonneg hC (sq_nonneg _)) (mul_nonneg hC (sq_nonneg _)))
    _ = characterLBoundConstant ^ 3 * ((N : ℝ) * (M : ℝ)) ^ 2 *
          ((N.lcm M : ℕ) : ℝ) ^ 2 := by ring
    _ ≤ characterLBoundConstant ^ 3 * ((N : ℝ) * (M : ℝ)) ^ 2 *
          ((N : ℝ) * (M : ℝ)) ^ 2 := by
      exact mul_le_mul_of_nonneg_left hlcmSq
        (mul_nonneg (pow_nonneg hC _) (sq_nonneg _))
    _ = siegelResidueBoundConstant * ((N : ℝ) * (M : ℝ)) ^ 4 := by
      rw [siegelResidueBoundConstant]
      ring

end BombieriVinogradov.SiegelWalfisz

end

section

namespace BombieriVinogradov.SiegelWalfisz

theorem zetaRegularized_differentiable : Differentiable ℂ riemannZeta₀ :=
  differentiable_riemannZeta₀

theorem riemannZeta_eq_pole_add_regularized {s : ℂ} (hs : s ≠ 1) :
    riemannZeta s = (s - 1)⁻¹ + riemannZeta₀ s :=
  riemannZeta_eq_inv_sub_add hs

end BombieriVinogradov.SiegelWalfisz

end

section

open Metric Set

namespace BombieriVinogradov.SiegelWalfisz

theorem exists_zetaRegularized_circle_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ s ∈ siegelCauchyCircle, ‖riemannZeta₀ s‖ ≤ C := by
  obtain ⟨M, hM⟩ := (isCompact_sphere (2 : ℂ) (3 / 2 : ℝ)).bddAbove_image
    zetaRegularized_differentiable.continuous.norm.continuousOn
  refine ⟨max 1 M, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro s hs
  exact (hM (mem_image_of_mem _ hs)).trans (le_max_right _ _)

theorem exists_riemannZeta_circle_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ s ∈ siegelCauchyCircle, ‖riemannZeta s‖ ≤ C := by
  obtain ⟨C, hC, hregular⟩ := exists_zetaRegularized_circle_bound
  refine ⟨2 + C, by linarith, ?_⟩
  intro s hs
  have hdist := siegelCauchyCircle_norm_sub_one_lower hs
  have hnormpos : 0 < ‖s - 1‖ := lt_of_lt_of_le (by norm_num) hdist
  have hinv : ‖(s - 1)⁻¹‖ ≤ 2 := by
    rw [norm_inv]
    have : 1 * ‖s - 1‖⁻¹ ≤ 2 := by
      rw [mul_inv_le_iff₀ hnormpos]
      linarith
    simpa using this
  rw [riemannZeta_eq_pole_add_regularized (siegelCauchyCircle_ne_one hs)]
  exact (norm_add_le _ _).trans ((add_le_add hinv (hregular s hs)).trans_eq (by ring))

end BombieriVinogradov.SiegelWalfisz

end

section

namespace BombieriVinogradov.SiegelWalfisz

noncomputable def entireDividedDifference (f : ℂ → ℂ) (c : ℂ) : ℂ → ℂ :=
  Function.update (fun z ↦ (f z - f c) / (z - c)) c (deriv f c)

theorem entireDividedDifference_apply_of_ne (f : ℂ → ℂ) {c z : ℂ} (hz : z ≠ c) :
    entireDividedDifference f c z = (f z - f c) / (z - c) := by
  rw [entireDividedDifference, Function.update_of_ne hz]

theorem entireDividedDifference_differentiableAt_of_ne (f : ℂ → ℂ) {c z : ℂ}
    (hf : Differentiable ℂ f) (hz : z ≠ c) :
    DifferentiableAt ℂ (entireDividedDifference f c) z := by
  apply DifferentiableAt.congr_of_eventuallyEq
  · have hconst : DifferentiableAt ℂ (fun _ : ℂ ↦ f c) z := by fun_prop
    have hden : DifferentiableAt ℂ (fun w : ℂ ↦ w - c) z := by fun_prop
    exact ((hf z).sub hconst).div hden (sub_ne_zero.mpr hz)
  · filter_upwards [eventually_ne_nhds hz] with w hw
    exact entireDividedDifference_apply_of_ne f hw

theorem entireDividedDifference_differentiable (f : ℂ → ℂ) (c : ℂ)
    (hf : Differentiable ℂ f) :
    Differentiable ℂ (entireDividedDifference f c) := by
  intro z
  rcases eq_or_ne z c with rfl | hz
  · refine (Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt ?_ ?_).differentiableAt
    · filter_upwards [self_mem_nhdsWithin] with w hw
      exact entireDividedDifference_differentiableAt_of_ne f hf (by simpa using hw)
    · simpa [entireDividedDifference] using (hf z).hasDerivAt.continuousAt_div
  · exact entireDividedDifference_differentiableAt_of_ne f hf hz

end BombieriVinogradov.SiegelWalfisz

end

section

namespace BombieriVinogradov.SiegelWalfisz

noncomputable def siegelPoleSubtracted {N M : ℕ} [NeZero N] [NeZero M]
    [NeZero (N.lcm M)] (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ M) :
    ℂ → ℂ := fun s ↦
  riemannZeta₀ s * siegelLProduct χ ψ s +
    entireDividedDifference (siegelLProduct χ ψ) 1 s

theorem siegelProduct_sub_pole_entire {N M : ℕ} [NeZero N] [NeZero M]
    [NeZero (N.lcm M)] (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ M)
    (hχ : χ ≠ 1) (hψ : ψ ≠ 1) (hmul : DirichletCharacter.mul χ ψ ≠ 1) :
    Differentiable ℂ (siegelPoleSubtracted χ ψ) := by
  exact zetaRegularized_differentiable.mul (siegelLProduct_differentiable χ ψ hχ hψ hmul) |>.add
    (entireDividedDifference_differentiable _ _
      (siegelLProduct_differentiable χ ψ hχ hψ hmul))

theorem siegelPoleSubtracted_apply_of_ne {N M : ℕ} [NeZero N] [NeZero M]
    [NeZero (N.lcm M)] (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ M)
    {s : ℂ} (hs : s ≠ 1) :
    siegelPoleSubtracted χ ψ s =
      riemannZeta s * siegelLProduct χ ψ s - siegelProductResidue χ ψ / (s - 1) := by
  rw [siegelPoleSubtracted, entireDividedDifference_apply_of_ne _ hs,
    siegelLProduct_one, riemannZeta_eq_pole_add_regularized hs]
  field_simp [sub_ne_zero.mpr hs]
  ring

end BombieriVinogradov.SiegelWalfisz

end

section

namespace BombieriVinogradov.SiegelWalfisz

theorem siegelPoleSubtracted_circle_bound :
    ∃ C : ℝ, 0 < C ∧ ∃ K : ℕ,
      ∀ {N M : ℕ} [NeZero N] [NeZero M] [NeZero (N.lcm M)]
        (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ M),
        χ ≠ 1 → ψ ≠ 1 → DirichletCharacter.mul χ ψ ≠ 1 →
          ∀ {s : ℂ}, s ∈ siegelCauchyCircle →
            ‖siegelPoleSubtracted χ ψ s‖ ≤ C * ((N : ℝ) * (M : ℝ)) ^ K := by
  obtain ⟨CriemannZeta, hCriemannZeta, hzeta⟩ := exists_riemannZeta_circle_bound
  refine ⟨(CriemannZeta + 2) * siegelResidueBoundConstant,
    mul_pos (by linarith) siegelResidueBoundConstant_pos, 4, ?_⟩
  intro N M instN instM instLcm χ ψ hχ hψ hmul s hs
  have hL := norm_siegelLProduct_le χ ψ hχ hψ hmul hs
  have hres := norm_siegelProductResidue_le χ ψ hχ hψ hmul
  have hdist := siegelCauchyCircle_norm_sub_one_lower hs
  have hnormpos : 0 < ‖s - 1‖ := lt_of_lt_of_le (by norm_num) hdist
  have hinv : ‖s - 1‖⁻¹ ≤ 2 := by
    have : 1 * ‖s - 1‖⁻¹ ≤ 2 := by
      rw [mul_inv_le_iff₀ hnormpos]
      linarith
    simpa using this
  rw [siegelPoleSubtracted_apply_of_ne χ ψ (siegelCauchyCircle_ne_one hs)]
  calc
    ‖riemannZeta s * siegelLProduct χ ψ s - siegelProductResidue χ ψ / (s - 1)‖
        ≤ ‖riemannZeta s * siegelLProduct χ ψ s‖ +
          ‖siegelProductResidue χ ψ / (s - 1)‖ := norm_sub_le _ _
    _ = ‖riemannZeta s‖ * ‖siegelLProduct χ ψ s‖ +
          ‖siegelProductResidue χ ψ‖ * ‖s - 1‖⁻¹ := by
      rw [norm_mul, norm_div, div_eq_mul_inv]
    _ ≤ CriemannZeta * (siegelResidueBoundConstant * ((N : ℝ) * (M : ℝ)) ^ 4) +
          (siegelResidueBoundConstant * ((N : ℝ) * (M : ℝ)) ^ 4) * 2 := by
      apply add_le_add
      · exact mul_le_mul (hzeta s hs) hL (norm_nonneg _) hCriemannZeta.le
      · exact mul_le_mul hres hinv (inv_nonneg.mpr (norm_nonneg _))
          (mul_nonneg siegelResidueBoundConstant_pos.le (pow_nonneg (by positivity) _))
    _ = ((CriemannZeta + 2) * siegelResidueBoundConstant) * ((N : ℝ) * (M : ℝ)) ^ 4 := by
      ring

end BombieriVinogradov.SiegelWalfisz

end

section

namespace BombieriVinogradov.ComplexAnalysis

noncomputable def taylorCoefficient (f : ℂ → ℂ) (c : ℂ) (n : ℕ) : ℂ :=
  iteratedDeriv n f c / (n.factorial : ℂ)

theorem norm_taylorCoefficient_le {f : ℂ → ℂ} {c : ℂ} {R C : ℝ}
    (n : ℕ) (hR : 0 < R) (hf : Differentiable ℂ f)
    (hC : ∀ z ∈ Metric.sphere c R, ‖f z‖ ≤ C) :
    ‖taylorCoefficient f c n‖ ≤ C / R ^ n := by
  have hderiv := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le
    n hR hf.diffContOnCl hC
  have hfac : 0 < (n.factorial : ℝ) := by positivity
  rw [taylorCoefficient, norm_div]
  simp only [norm_natCast]
  calc
    ‖iteratedDeriv n f c‖ / n.factorial ≤
        (n.factorial * C / R ^ n) / n.factorial :=
      (div_le_div_iff_of_pos_right hfac).2 hderiv
    _ = C / R ^ n := by
      field_simp [Nat.factorial_ne_zero]

end BombieriVinogradov.ComplexAnalysis

end

section

namespace BombieriVinogradov.SiegelWalfisz

noncomputable def siegelRegularCoefficient {N M : ℕ} [NeZero N] [NeZero M]
    [NeZero (N.lcm M)] (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ M)
    (m : ℕ) : ℂ :=
  (-1 : ℂ) ^ m * BombieriVinogradov.ComplexAnalysis.taylorCoefficient
    (siegelPoleSubtracted χ ψ) 2 m

theorem norm_siegelRegularCoefficient {N M : ℕ} [NeZero N] [NeZero M]
    [NeZero (N.lcm M)] (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ M)
    (m : ℕ) :
    ‖siegelRegularCoefficient χ ψ m‖ =
      ‖BombieriVinogradov.ComplexAnalysis.taylorCoefficient
        (siegelPoleSubtracted χ ψ) 2 m‖ := by
  rw [siegelRegularCoefficient, norm_mul, norm_pow, norm_neg]
  have hone : ‖(1 : ℂ)‖ = 1 := by
    simpa only [Nat.cast_one] using Complex.norm_natCast 1
  rw [hone, one_pow, one_mul]

end BombieriVinogradov.SiegelWalfisz

end

section

namespace BombieriVinogradov.SiegelWalfisz

theorem norm_siegelRegularCoefficient_le_of_circle_bound
    {N M : ℕ} [NeZero N] [NeZero M] [NeZero (N.lcm M)]
    (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ M)
    (hχ : χ ≠ 1) (hψ : ψ ≠ 1) (hmul : DirichletCharacter.mul χ ψ ≠ 1)
    {C : ℝ} {K : ℕ}
    (hcircle : ∀ {s : ℂ}, s ∈ siegelCauchyCircle →
      ‖siegelPoleSubtracted χ ψ s‖ ≤ C * ((N : ℝ) * (M : ℝ)) ^ K)
    (m : ℕ) :
    ‖siegelRegularCoefficient χ ψ m‖ ≤
      C * ((N : ℝ) * (M : ℝ)) ^ K * (2 / 3 : ℝ) ^ m := by
  rw [norm_siegelRegularCoefficient]
  have hcauchy := BombieriVinogradov.ComplexAnalysis.norm_taylorCoefficient_le
    m (by norm_num : (0 : ℝ) < 3 / 2)
    (siegelProduct_sub_pole_entire χ ψ hχ hψ hmul)
    (fun z hz ↦ hcircle hz)
  calc
    ‖BombieriVinogradov.ComplexAnalysis.taylorCoefficient
        (siegelPoleSubtracted χ ψ) 2 m‖
        ≤ (C * ((N : ℝ) * (M : ℝ)) ^ K) / (3 / 2 : ℝ) ^ m := hcauchy
    _ = C * ((N : ℝ) * (M : ℝ)) ^ K * (2 / 3 : ℝ) ^ m := by
      rw [div_eq_mul_inv, ← inv_pow]
      norm_num

end BombieriVinogradov.SiegelWalfisz

end

section

namespace BombieriVinogradov.SiegelWalfisz

theorem siegelProduct_coefficient_bound :
    ∃ C : ℝ, 0 < C ∧ ∃ K : ℕ,
      ∀ {N M : ℕ} [NeZero N] [NeZero M] [NeZero (N.lcm M)]
        (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ M),
        χ ≠ 1 → ψ ≠ 1 → DirichletCharacter.mul χ ψ ≠ 1 →
          ∀ m : ℕ, ‖siegelRegularCoefficient χ ψ m‖ ≤
            C * ((N : ℝ) * (M : ℝ)) ^ K * (2 / 3 : ℝ) ^ m := by
  obtain ⟨C, hC, K, hcircle⟩ := siegelPoleSubtracted_circle_bound
  refine ⟨C, hC, K, ?_⟩
  intro N M instN instM instLcm χ ψ hχ hψ hmul m
  exact norm_siegelRegularCoefficient_le_of_circle_bound χ ψ hχ hψ hmul
    (hcircle χ ψ hχ hψ hmul) m

end BombieriVinogradov.SiegelWalfisz

end

section

namespace BombieriVinogradov.SiegelWalfisz

theorem hasSum_siegelRegularCoefficient {N M : ℕ}
    [NeZero N] [NeZero M] [NeZero (N.lcm M)]
    (chi : DirichletCharacter ℂ N) (psi : DirichletCharacter ℂ M)
    (hchi : chi ≠ 1) (hpsi : psi ≠ 1)
    (hmul : DirichletCharacter.mul chi psi ≠ 1) (s : ℂ) :
    HasSum (fun m : ℕ => siegelRegularCoefficient chi psi m * (2 - s) ^ m)
      (siegelPoleSubtracted chi psi s) := by
  have h := Complex.hasSum_taylorSeries_of_entire
    (siegelProduct_sub_pole_entire chi psi hchi hpsi hmul) 2 s
  refine HasSum.congr_fun h (fun m => ?_)
  unfold siegelRegularCoefficient BombieriVinogradov.ComplexAnalysis.taylorCoefficient
  simp only [smul_eq_mul]
  have hpow : (s - 2) ^ m = (-1 : ℂ) ^ m * (2 - s) ^ m := by
    rw [show s - 2 = -(2 - s) by ring, neg_pow]
  rw [hpow]
  field_simp [Nat.factorial_ne_zero]

end BombieriVinogradov.SiegelWalfisz

end

section

open scoped ComplexOrder

namespace BombieriVinogradov.SiegelWalfisz

noncomputable def siegelSourceCoefficient {N M : ℕ}
    (chi : DirichletCharacter ℂ N) (psi : DirichletCharacter ℂ M) (m : ℕ) : ℂ :=
  (-1 : ℂ) ^ m * BombieriVinogradov.ComplexAnalysis.taylorCoefficient
    (LSeries (siegelProductCoefficients chi psi)) 2 m

theorem siegelSourceCoefficient_nonneg {N M : ℕ}
    (chi : DirichletCharacter ℂ N) (psi : DirichletCharacter ℂ M)
    (hchi : chi ^ 2 = 1) (hpsi : psi ^ 2 = 1) (m : ℕ) :
    0 ≤ siegelSourceCoefficient chi psi m := by
  have hsumm : LSeriesSummable (siegelProductCoefficients chi psi) (3 / 2 : ℂ) :=
    siegelProductCoefficients_LSeriesSummable chi psi (by norm_num)
  have habs : LSeries.abscissaOfAbsConv (siegelProductCoefficients chi psi) < (2 : ℝ) :=
    hsumm.abscissaOfAbsConv_le.trans_lt (by norm_num)
  have hderiv := LSeries.iteratedDeriv_alternating
    (siegelProductCoefficients_nonneg chi psi hchi hpsi) habs m
  have hfactorial : (0 : ℂ) ≤ m.factorial := by positivity
  simpa [siegelSourceCoefficient,
    BombieriVinogradov.ComplexAnalysis.taylorCoefficient, mul_div_assoc] using
      div_nonneg hderiv hfactorial

theorem one_le_siegelSourceCoefficient_zero {N M : ℕ}
    (chi : DirichletCharacter ℂ N) (psi : DirichletCharacter ℂ M)
    (hchi : chi ^ 2 = 1) (hpsi : psi ^ 2 = 1) :
    (1 : ℂ) ≤ siegelSourceCoefficient chi psi 0 := by
  rw [siegelSourceCoefficient,
    BombieriVinogradov.ComplexAnalysis.taylorCoefficient]
  simp only [pow_zero, one_mul, iteratedDeriv_zero, Nat.factorial_zero, Nat.cast_one, div_one]
  rw [LSeries]
  have hsumm : Summable (LSeries.term (siegelProductCoefficients chi psi) 2) :=
    siegelProductCoefficients_LSeriesSummable chi psi (by norm_num)
  calc
    (1 : ℂ) = ∑ n ∈ {1}, LSeries.term (siegelProductCoefficients chi psi) 2 n := by
      simp [LSeries.term_def, siegelProductCoefficients_one]
    _ ≤ ∑' n, LSeries.term (siegelProductCoefficients chi psi) 2 n :=
      hsumm.sum_le_tsum {1} fun n _ =>
        LSeries.term_nonneg (siegelProductCoefficients_nonneg chi psi hchi hpsi n) 2

end BombieriVinogradov.SiegelWalfisz

end

section

namespace BombieriVinogradov.SiegelWalfisz

theorem pole_source_coefficient (residue : ℂ) (m : ℕ) :
    (-1 : ℂ) ^ m * BombieriVinogradov.ComplexAnalysis.taylorCoefficient
      (fun s : ℂ => residue / (s - 1)) 2 m = residue := by
  rw [BombieriVinogradov.ComplexAnalysis.taylorCoefficient,
    show (fun s : ℂ => residue / (s - 1)) = fun s : ℂ => residue * (s - 1)⁻¹ by
      funext s
      rw [div_eq_mul_inv],
    iteratedDeriv_const_mul_field]
  simp only [iteratedDeriv_eq_iterate]
  have hinv : deriv^[m] (fun s : ℂ => (s - 1)⁻¹) 2 =
      (-1 : ℂ) ^ m * m.factorial := by
    have h := congrFun (iter_deriv_inv_linear_sub m (1 : ℂ) 1) 2
    norm_num at h
    simpa using h
  rw [hinv]
  field_simp [Nat.factorial_ne_zero]
  have hsign : (((-1 : ℂ) ^ m) ^ 2) = 1 := by
    rw [← pow_mul]
    simp
  rw [hsign, one_mul]

end BombieriVinogradov.SiegelWalfisz

end

section

namespace BombieriVinogradov.SiegelWalfisz

theorem siegelSourceCoefficient_eq_regular_add_residue {N M : ℕ}
    [NeZero N] [NeZero M] [NeZero (N.lcm M)]
    (chi : DirichletCharacter ℂ N) (psi : DirichletCharacter ℂ M)
    (hchi : chi ≠ 1) (hpsi : psi ≠ 1)
    (hmul : DirichletCharacter.mul chi psi ≠ 1) (m : ℕ) :
    siegelSourceCoefficient chi psi m =
      siegelRegularCoefficient chi psi m + siegelProductResidue chi psi := by
  let halfPlane : Set ℂ := {s | 1 < s.re}
  have hopen : IsOpen halfPlane := isOpen_lt continuous_const Complex.continuous_re
  have htwo : (2 : ℂ) ∈ halfPlane := by norm_num [halfPlane]
  have heq : halfPlane.EqOn (LSeries (siegelProductCoefficients chi psi))
      (fun s => siegelPoleSubtracted chi psi s + siegelProductResidue chi psi / (s - 1)) := by
    intro s hs
    have hsone : s ≠ 1 := by
      intro h
      subst s
      norm_num [halfPlane] at hs
    rw [siegelProduct_LSeries_eq chi psi hs]
    change _ = siegelPoleSubtracted chi psi s + siegelProductResidue chi psi / (s - 1)
    rw [siegelPoleSubtracted_apply_of_ne chi psi hsone]
    rw [siegelLProduct]
    ring
  have hderiv := heq.iteratedDeriv_of_isOpen hopen m htwo
  have hregular : ContDiffAt ℂ m (siegelPoleSubtracted chi psi) 2 :=
    (siegelProduct_sub_pole_entire chi psi hchi hpsi hmul).contDiff.contDiffAt
  have hpole : ContDiffAt ℂ m
      (fun s : ℂ => siegelProductResidue chi psi / (s - 1)) 2 := by
    fun_prop (disch := norm_num)
  change iteratedDeriv m (LSeries (siegelProductCoefficients chi psi)) 2 =
    iteratedDeriv m
      (siegelPoleSubtracted chi psi +
        fun s : ℂ => siegelProductResidue chi psi / (s - 1)) 2 at hderiv
  rw [iteratedDeriv_add hregular hpole] at hderiv
  rw [siegelSourceCoefficient, siegelRegularCoefficient,
    BombieriVinogradov.ComplexAnalysis.taylorCoefficient,
    BombieriVinogradov.ComplexAnalysis.taylorCoefficient, hderiv]
  calc
    (-1 : ℂ) ^ m *
          ((iteratedDeriv m (siegelPoleSubtracted chi psi) 2 +
            iteratedDeriv m (fun s : ℂ => siegelProductResidue chi psi / (s - 1)) 2) /
            (m.factorial : ℂ)) =
        (-1 : ℂ) ^ m *
            (iteratedDeriv m (siegelPoleSubtracted chi psi) 2 / (m.factorial : ℂ)) +
          (-1 : ℂ) ^ m *
            (iteratedDeriv m (fun s : ℂ => siegelProductResidue chi psi / (s - 1)) 2 /
              (m.factorial : ℂ)) := by ring
    _ = (-1 : ℂ) ^ m *
          (iteratedDeriv m (siegelPoleSubtracted chi psi) 2 / (m.factorial : ℂ)) +
        siegelProductResidue chi psi := by
      have hpoleCoefficient := pole_source_coefficient (siegelProductResidue chi psi) m
      rw [BombieriVinogradov.ComplexAnalysis.taylorCoefficient] at hpoleCoefficient
      rw [hpoleCoefficient]

end BombieriVinogradov.SiegelWalfisz

end

section

open scoped ComplexOrder

namespace BombieriVinogradov.SiegelWalfisz

noncomputable def siegelSourcePartialSum {N M : ℕ}
    (chi : DirichletCharacter ℂ N) (psi : DirichletCharacter ℂ M)
    (cutoff : ℕ) (t : ℝ) : ℂ :=
  ∑ m ∈ Finset.range cutoff, siegelSourceCoefficient chi psi m * (t : ℂ) ^ m

theorem one_le_siegelSourcePartialSum {N M : ℕ}
    (chi : DirichletCharacter ℂ N) (psi : DirichletCharacter ℂ M)
    (hchiSquare : chi ^ 2 = 1) (hpsiSquare : psi ^ 2 = 1)
    {cutoff : ℕ} (hcutoff : 0 < cutoff) {t : ℝ} (ht : 0 ≤ t) :
    (1 : ℂ) ≤ siegelSourcePartialSum chi psi cutoff t := by
  calc
    (1 : ℂ) ≤ siegelSourceCoefficient chi psi 0 :=
      one_le_siegelSourceCoefficient_zero chi psi hchiSquare hpsiSquare
    _ = siegelSourceCoefficient chi psi 0 * (t : ℂ) ^ 0 := by simp
    _ ≤ ∑ m ∈ Finset.range cutoff,
        siegelSourceCoefficient chi psi m * (t : ℂ) ^ m := by
      exact Finset.single_le_sum
        (fun m _ => mul_nonneg
          (siegelSourceCoefficient_nonneg chi psi hchiSquare hpsiSquare m)
          (pow_nonneg (by exact_mod_cast ht) m))
        (Finset.mem_range.mpr hcutoff)

theorem regularPartialSum_eq_source_sub_residue {N M : ℕ}
    [NeZero N] [NeZero M] [NeZero (N.lcm M)]
    (chi : DirichletCharacter ℂ N) (psi : DirichletCharacter ℂ M)
    (hchi : chi ≠ 1) (hpsi : psi ≠ 1)
    (hmul : DirichletCharacter.mul chi psi ≠ 1)
    (cutoff : ℕ) (t : ℝ) :
    (∑ m ∈ Finset.range cutoff,
        siegelRegularCoefficient chi psi m * (t : ℂ) ^ m) =
      siegelSourcePartialSum chi psi cutoff t -
        siegelProductResidue chi psi * ∑ m ∈ Finset.range cutoff, (t : ℂ) ^ m := by
  rw [siegelSourcePartialSum]
  simp_rw [siegelSourceCoefficient_eq_regular_add_residue chi psi hchi hpsi hmul]
  simp only [add_mul, Finset.sum_add_distrib, Finset.mul_sum]
  ring

end BombieriVinogradov.SiegelWalfisz

end

section

namespace BombieriVinogradov.SiegelWalfisz

noncomputable def regularCoefficientTail
    (a : ℕ → ℂ) (cutoff : ℕ) (t : ℝ) : ℂ :=
  ∑' k : ℕ, a (cutoff + k) * (t : ℂ) ^ (cutoff + k)

theorem norm_regularCoefficientTail_le
    (a : ℕ → ℂ) {A t : ℝ} (cutoff : ℕ)
    (hA : 0 ≤ A) (ht0 : 0 ≤ t) (ht : t ≤ 9 / 8)
    (ha : ∀ m, ‖a m‖ ≤ A * (2 / 3 : ℝ) ^ m) :
    ‖regularCoefficientTail a cutoff t‖ ≤
      4 * A * (3 / 4 : ℝ) ^ cutoff := by
  have hterm (k : ℕ) :
      ‖a (cutoff + k) * (t : ℂ) ^ (cutoff + k)‖ ≤
        A * (3 / 4 : ℝ) ^ (cutoff + k) := by
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0]
    calc
      ‖a (cutoff + k)‖ * t ^ (cutoff + k) ≤
          (A * (2 / 3 : ℝ) ^ (cutoff + k)) * t ^ (cutoff + k) :=
        mul_le_mul_of_nonneg_right (ha _) (pow_nonneg ht0 _)
      _ = A * ((2 / 3 : ℝ) * t) ^ (cutoff + k) := by
        rw [mul_assoc, mul_pow]
      _ ≤ A * (3 / 4 : ℝ) ^ (cutoff + k) := by
        gcongr
        nlinarith
  have hgeom : HasSum (fun k : ℕ => (3 / 4 : ℝ) ^ k) 4 := by
    have h := hasSum_geometric_of_norm_lt_one (ξ := (3 / 4 : ℝ)) (by norm_num)
    norm_num at h
    exact h
  have hmajor : HasSum (fun k : ℕ => A * (3 / 4 : ℝ) ^ (cutoff + k))
      (4 * A * (3 / 4 : ℝ) ^ cutoff) := by
    have h := hgeom.mul_left (A * (3 / 4 : ℝ) ^ cutoff)
    simpa only [pow_add, mul_assoc, mul_comm, mul_left_comm] using h
  exact tsum_of_norm_bounded hmajor hterm

end BombieriVinogradov.SiegelWalfisz

end

section

namespace BombieriVinogradov.SiegelWalfisz

noncomputable def siegelProductValue {N M : ℕ}
    [NeZero N] [NeZero M] [NeZero (N.lcm M)]
    (chi : DirichletCharacter ℂ N) (psi : DirichletCharacter ℂ M) (s : ℂ) : ℂ :=
  riemannZeta s * siegelLProduct chi psi s

theorem siegelProductValue_eq_regular_add_pole {N M : ℕ}
    [NeZero N] [NeZero M] [NeZero (N.lcm M)]
    (chi : DirichletCharacter ℂ N) (psi : DirichletCharacter ℂ M)
    {s : ℂ} (hs : s ≠ 1) :
    siegelProductValue chi psi s =
      siegelPoleSubtracted chi psi s + siegelProductResidue chi psi / (s - 1) := by
  rw [siegelPoleSubtracted_apply_of_ne chi psi hs]
  unfold siegelProductValue
  ring

end BombieriVinogradov.SiegelWalfisz

end

section

namespace BombieriVinogradov.SiegelWalfisz

theorem siegelProductValue_decomposition {N M : ℕ}
    [NeZero N] [NeZero M] [NeZero (N.lcm M)]
    (chi : DirichletCharacter ℂ N) (psi : DirichletCharacter ℂ M)
    (hchi : chi ≠ 1) (hpsi : psi ≠ 1)
    (hmul : DirichletCharacter.mul chi psi ≠ 1)
    (cutoff : ℕ) {delta : ℝ} (hdelta : 0 < delta) :
    siegelProductValue chi psi (1 - delta) =
      siegelSourcePartialSum chi psi cutoff (1 + delta) +
        regularCoefficientTail (siegelRegularCoefficient chi psi) cutoff (1 + delta) -
          siegelProductResidue chi psi * ((1 + delta : ℝ) : ℂ) ^ cutoff / delta := by
  let s : ℂ := (1 - delta : ℝ)
  let t : ℝ := 1 + delta
  have hs : s ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    dsimp [s] at hre
    norm_num at hre
    linarith
  have hexpansion := hasSum_siegelRegularCoefficient chi psi hchi hpsi hmul s
  have hsplit : siegelPoleSubtracted chi psi s =
      (∑ m ∈ Finset.range cutoff, siegelRegularCoefficient chi psi m * (t : ℂ) ^ m) +
        regularCoefficientTail (siegelRegularCoefficient chi psi) cutoff t := by
    have hsum := hexpansion.summable.sum_add_tsum_nat_add cutoff
    rw [hexpansion.tsum_eq] at hsum
    have hst : (2 - s : ℂ) = t := by
      dsimp [s, t]
      push_cast
      ring
    rw [hst] at hsum
    simpa only [regularCoefficientTail, Nat.add_comm] using hsum.symm
  have hsdef : (1 : ℂ) - delta = s := by
    dsimp [s]
    push_cast
    rfl
  have htdef : 1 + delta = t := rfl
  rw [hsdef, htdef]
  rw [siegelProductValue_eq_regular_add_pole chi psi hs, hsplit]
  rw [regularPartialSum_eq_source_sub_residue chi psi hchi hpsi hmul]
  have ht : (t : ℂ) ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    dsimp [t] at hre
    norm_num at hre
    linarith
  rw [geom_sum_eq ht]
  dsimp [s, t]
  push_cast
  field_simp
  ring

end BombieriVinogradov.SiegelWalfisz

end

section

open scoped ComplexOrder

namespace BombieriVinogradov.SiegelWalfisz

theorem siegelProductValue_re_lower_bound {N M : ℕ}
    [NeZero N] [NeZero M] [NeZero (N.lcm M)]
    (chi : DirichletCharacter ℂ N) (psi : DirichletCharacter ℂ M)
    (hchiSquare : chi ^ 2 = 1) (hpsiSquare : psi ^ 2 = 1)
    (hchi : chi ≠ 1) (hpsi : psi ≠ 1)
    (hmul : DirichletCharacter.mul chi psi ≠ 1)
    {A delta : ℝ} (hA : 0 ≤ A) (hdelta : 0 < delta) (hdeltaUpper : delta ≤ 1 / 8)
    {cutoff : ℕ} (hcutoff : 0 < cutoff)
    (hcoeff : ∀ m, ‖siegelRegularCoefficient chi psi m‖ ≤ A * (2 / 3 : ℝ) ^ m) :
    1 - (siegelProductResidue chi psi).re * (1 + delta) ^ cutoff / delta -
        4 * A * (3 / 4 : ℝ) ^ cutoff ≤
      (siegelProductValue chi psi (1 - delta)).re := by
  let partialSum := siegelSourcePartialSum chi psi cutoff (1 + delta)
  let tail := regularCoefficientTail (siegelRegularCoefficient chi psi) cutoff (1 + delta)
  have hpartialComplex : (1 : ℂ) ≤ partialSum :=
    one_le_siegelSourcePartialSum chi psi hchiSquare hpsiSquare hcutoff (by linarith)
  have hpartial : 1 ≤ partialSum.re := (Complex.le_def.mp hpartialComplex).1
  have htailNorm : ‖tail‖ ≤ 4 * A * (3 / 4 : ℝ) ^ cutoff :=
    norm_regularCoefficientTail_le (siegelRegularCoefficient chi psi) cutoff hA
      (by linarith) (by linarith) hcoeff
  have htailRe : -(4 * A * (3 / 4 : ℝ) ^ cutoff) ≤ tail.re := by
    exact (neg_le_neg htailNorm).trans ((abs_le.mp (Complex.abs_re_le_norm tail)).1)
  have hdecomp := congrArg Complex.re
    (siegelProductValue_decomposition chi psi hchi hpsi hmul cutoff hdelta)
  have hpowcast : (((1 + delta : ℝ) : ℂ) ^ cutoff) =
      (((1 + delta) ^ cutoff : ℝ) : ℂ) := by
    norm_cast
  have hbasecast : (1 : ℂ) + delta = ((1 + delta : ℝ) : ℂ) := by
    push_cast
    rfl
  have hpowRe : ((1 + (delta : ℂ)) ^ cutoff).re = (1 + delta) ^ cutoff := by
    rw [hbasecast, hpowcast]
    rfl
  have hpowIm : ((1 + (delta : ℂ)) ^ cutoff).im = 0 := by
    rw [hbasecast, hpowcast]
    rfl
  have hpoleRe :
      (siegelProductResidue chi psi * (((1 + delta : ℝ) : ℂ) ^ cutoff) / delta).re =
        (siegelProductResidue chi psi).re * (1 + delta) ^ cutoff / delta := by
    simp
    rw [hpowRe, hpowIm]
    ring
  rw [Complex.sub_re, Complex.add_re, hpoleRe] at hdecomp
  change (siegelProductValue chi psi (1 - delta)).re =
      partialSum.re + tail.re -
        (siegelProductResidue chi psi).re * (1 + delta) ^ cutoff / delta at hdecomp
  linarith

end BombieriVinogradov.SiegelWalfisz

end

section

open scoped ComplexOrder

open Filter
open Topology

namespace BombieriVinogradov.SiegelWalfisz

theorem siegelProductResidue_nonneg {N M : ℕ}
    [NeZero N] [NeZero M] [NeZero (N.lcm M)]
    (chi : DirichletCharacter ℂ N) (psi : DirichletCharacter ℂ M)
    (hchiSquare : chi ^ 2 = 1) (hpsiSquare : psi ^ 2 = 1)
    (hchi : chi ≠ 1) (hpsi : psi ≠ 1)
    (hmul : DirichletCharacter.mul chi psi ≠ 1) :
    0 ≤ siegelProductResidue chi psi := by
  obtain ⟨C, _hC, K, hbound⟩ := siegelProduct_coefficient_bound
  let A : ℝ := C * ((N : ℝ) * (M : ℝ)) ^ K
  have hregular : Tendsto (fun m => siegelRegularCoefficient chi psi m)
      atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero (fun m => norm_nonneg (siegelRegularCoefficient chi psi m))
      (fun m => hbound chi psi hchi hpsi hmul m) ?_
    have hpow := tendsto_pow_atTop_nhds_zero_of_norm_lt_one
      (show ‖(2 / 3 : ℝ)‖ < 1 by norm_num)
    have hconst : Tendsto (fun _ : ℕ => A) atTop (𝓝 A) := tendsto_const_nhds
    have hmulZero := hconst.mul hpow
    simpa [A] using hmulZero
  have hsource : Tendsto (fun m => siegelSourceCoefficient chi psi m)
      atTop (𝓝 (siegelProductResidue chi psi)) := by
    have hseq : (fun m => siegelSourceCoefficient chi psi m) =
        fun m => siegelRegularCoefficient chi psi m + siegelProductResidue chi psi := by
      funext m
      exact siegelSourceCoefficient_eq_regular_add_residue chi psi hchi hpsi hmul m
    rw [hseq]
    simpa using hregular.add_const (siegelProductResidue chi psi)
  exact ge_of_tendsto hsource <| Eventually.of_forall fun m =>
    siegelSourceCoefficient_nonneg chi psi hchiSquare hpsiSquare m

end BombieriVinogradov.SiegelWalfisz

end

section

namespace BombieriVinogradov.SiegelWalfisz

noncomputable def siegelTruncationIndex (B Q : ℝ) (K : ℕ) : ℕ :=
  ⌈4 * Real.log (B * Q ^ K)⌉₊ + 1

theorem truncationIndex_lower {B Q : ℝ} {K : ℕ}
    (hB : 1 ≤ B) (hQ : 1 ≤ Q) :
    4 * Real.log (B * Q ^ K) < siegelTruncationIndex B Q K := by
  have hB0 : 0 ≤ B := zero_le_one.trans hB
  have hQpow : 1 ≤ Q ^ K := one_le_pow₀ hQ
  have hX : 1 ≤ B * Q ^ K :=
    hB.trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hQpow hB0)
  have hlog : 0 ≤ 4 * Real.log (B * Q ^ K) :=
    mul_nonneg (by norm_num) (Real.log_nonneg hX)
  unfold siegelTruncationIndex
  rw [Nat.cast_add, Nat.cast_one]
  have hceil := Nat.le_ceil (4 * Real.log (B * Q ^ K))
  exact hceil.trans_lt (lt_add_one _)

theorem truncationIndex_upper {B Q : ℝ} {K : ℕ}
    (hB : 1 ≤ B) (hQ : 1 ≤ Q) :
    (siegelTruncationIndex B Q K : ℝ) <
      4 * Real.log (B * Q ^ K) + 2 := by
  have hB0 : 0 ≤ B := zero_le_one.trans hB
  have hQpow : 1 ≤ Q ^ K := one_le_pow₀ hQ
  have hX : 1 ≤ B * Q ^ K :=
    hB.trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hQpow hB0)
  have hlog : 0 ≤ 4 * Real.log (B * Q ^ K) :=
    mul_nonneg (by norm_num) (Real.log_nonneg hX)
  unfold siegelTruncationIndex
  rw [Nat.cast_add, Nat.cast_one]
  linarith [Nat.ceil_lt_add_one hlog]

end BombieriVinogradov.SiegelWalfisz

end

section

namespace BombieriVinogradov.SiegelWalfisz

theorem truncationPoleGrowth {B Q delta : ℝ} {K : ℕ}
    (hB : 1 ≤ B) (hQ : 1 ≤ Q) (hdelta0 : 0 ≤ delta) (hdelta : delta ≤ 1 / 8) :
    (1 + delta) ^ siegelTruncationIndex B Q K ≤
      Real.exp 2 * B * Q ^ ((4 * K : ℝ) * delta) := by
  let cutoff := siegelTruncationIndex B Q K
  let X := B * Q ^ K
  have hB0 : 0 ≤ B := zero_le_one.trans hB
  have hQ0 : 0 ≤ Q := zero_le_one.trans hQ
  have hQpos : 0 < Q := zero_lt_one.trans_le hQ
  have hXpos : 0 < X := mul_pos (zero_lt_one.trans_le hB) (pow_pos hQpos K)
  have hcutoff := truncationIndex_upper (K := K) hB hQ
  have hmul : (cutoff : ℝ) * delta ≤
      (4 * Real.log X + 2) * delta :=
    mul_le_mul_of_nonneg_right hcutoff.le hdelta0
  have hexponent : (cutoff : ℝ) * delta ≤ 4 * delta * Real.log X + 2 := by
    calc
      (cutoff : ℝ) * delta ≤ (4 * Real.log X + 2) * delta := hmul
      _ ≤ 4 * delta * Real.log X + 2 := by nlinarith
  have hbase : 1 + delta ≤ Real.exp delta := by
    simpa only [add_comm] using Real.add_one_le_exp delta
  have hbase0 : 0 ≤ 1 + delta := by linarith
  have hpow : (1 + delta) ^ cutoff ≤ (Real.exp delta) ^ cutoff := by
    exact pow_le_pow_left₀ hbase0 hbase cutoff
  calc
    (1 + delta) ^ cutoff ≤ (Real.exp delta) ^ cutoff := hpow
    _ = Real.exp ((cutoff : ℝ) * delta) := by
      rw [← Real.exp_nat_mul]
    _ ≤ Real.exp (4 * delta * Real.log X + 2) := Real.exp_le_exp.mpr hexponent
    _ = Real.exp 2 * X ^ (4 * delta) := by
      rw [Real.exp_add, Real.rpow_def_of_pos hXpos]
      have harg : 4 * delta * Real.log X = Real.log X * (4 * delta) := by ring
      rw [harg]
      ring
    _ ≤ Real.exp 2 * B * Q ^ ((4 * K : ℝ) * delta) := by
      have hBrpow : B ^ (4 * delta) ≤ B := by
        simpa only [Real.rpow_one] using
          Real.rpow_le_rpow_of_exponent_le hB (by nlinarith : 4 * delta ≤ 1)
      have hQrpow : (Q ^ K) ^ (4 * delta) = Q ^ ((4 * K : ℝ) * delta) := by
        calc
          (Q ^ K) ^ (4 * delta) = (Q ^ (4 * delta)) ^ K :=
            (Real.rpow_pow_comm hQ0 (4 * delta) K).symm
          _ = Q ^ ((4 * delta) * K) :=
            (Real.rpow_mul_natCast hQ0 (4 * delta) K).symm
          _ = Q ^ ((4 * K : ℝ) * delta) := by
            congr 1
            ring
      dsimp [X]
      rw [Real.mul_rpow hB0 (pow_nonneg hQ0 K), hQrpow]
      have hQnonneg : 0 ≤ Q ^ ((4 * K : ℝ) * delta) := Real.rpow_nonneg hQ0 _
      calc
        Real.exp 2 * (B ^ (4 * delta) * Q ^ ((4 * K : ℝ) * delta)) ≤
            Real.exp 2 * (B * Q ^ ((4 * K : ℝ) * delta)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hBrpow hQnonneg) (Real.exp_nonneg 2)
        _ = Real.exp 2 * B * Q ^ ((4 * K : ℝ) * delta) := by ring

end BombieriVinogradov.SiegelWalfisz

end

section

namespace BombieriVinogradov.SiegelWalfisz

theorem truncationTail_lt_half {A B Q : ℝ} {K : ℕ}
    (hA : 0 ≤ A) (hB : 1 ≤ B) (hAB : 8 * A ≤ B) (hQ : 1 ≤ Q) :
    4 * A * Q ^ K * (3 / 4 : ℝ) ^ siegelTruncationIndex B Q K < 1 / 2 := by
  let cutoff := siegelTruncationIndex B Q K
  let X := B * Q ^ K
  have hBpos : 0 < B := zero_lt_one.trans_le hB
  have hQpos : 0 < Q := zero_lt_one.trans_le hQ
  have hQpowpos : 0 < Q ^ K := pow_pos hQpos K
  have hXpos : 0 < X := mul_pos hBpos hQpowpos
  have hbase : Real.log (3 / 4 : ℝ) ≤ -1 / 4 := by
    have h := Real.log_le_sub_one_of_pos (show 0 < (3 / 4 : ℝ) by norm_num)
    norm_num at h ⊢
    exact h
  have hcutoff : 4 * Real.log X < (cutoff : ℝ) := by
    exact truncationIndex_lower hB hQ
  have hcutoff0 : 0 ≤ (cutoff : ℝ) := by positivity
  have hexponent : Real.log (3 / 4 : ℝ) * (cutoff : ℝ) < -Real.log X := by
    calc
      Real.log (3 / 4 : ℝ) * (cutoff : ℝ) ≤
          (-1 / 4 : ℝ) * (cutoff : ℝ) :=
        mul_le_mul_of_nonneg_right hbase hcutoff0
      _ < -Real.log X := by nlinarith
  have hpow : (3 / 4 : ℝ) ^ cutoff < 1 / X := by
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num)]
    have h := Real.exp_lt_exp.mpr hexponent
    rw [Real.exp_neg, Real.exp_log hXpos] at h
    simpa only [inv_eq_one_div] using h
  rcases hA.eq_or_lt with rfl | hApos
  · norm_num
  · have hpref : 0 < 4 * A * Q ^ K := mul_pos (mul_pos (by norm_num) hApos) hQpowpos
    calc
      4 * A * Q ^ K * (3 / 4 : ℝ) ^ cutoff <
          4 * A * Q ^ K * (1 / X) := mul_lt_mul_of_pos_left hpow hpref
      _ = 4 * A / B := by
        dsimp [X]
        field_simp
      _ ≤ 1 / 2 := by
        rw [div_le_iff₀ hBpos]
        nlinarith

end BombieriVinogradov.SiegelWalfisz

end

section

namespace BombieriVinogradov.SiegelWalfisz

theorem siegelTruncation_spec {A B Q delta : ℝ} {K : ℕ}
    (hA : 0 ≤ A) (hB : 1 ≤ B) (hAB : 8 * A ≤ B) (hQ : 1 ≤ Q)
    (hdelta0 : 0 ≤ delta) (hdelta : delta ≤ 1 / 8) :
    4 * A * Q ^ K * (3 / 4 : ℝ) ^ siegelTruncationIndex B Q K < 1 / 2 ∧
      (1 + delta) ^ siegelTruncationIndex B Q K ≤
        Real.exp 2 * B * Q ^ ((4 * K : ℝ) * delta) :=
  ⟨truncationTail_lt_half hA hB hAB hQ,
    truncationPoleGrowth hB hQ hdelta0 hdelta⟩

end BombieriVinogradov.SiegelWalfisz

end

section

open scoped ComplexOrder

namespace BombieriVinogradov.SiegelWalfisz

theorem siegelProduct_pos_of_coefficient_bound {N M : ℕ}
    [NeZero N] [NeZero M] [NeZero (N.lcm M)]
    (chi : DirichletCharacter ℂ N) (psi : DirichletCharacter ℂ M)
    (hchiSquare : chi ^ 2 = 1) (hpsiSquare : psi ^ 2 = 1)
    (hchi : chi ≠ 1) (hpsi : psi ≠ 1)
    (hmul : DirichletCharacter.mul chi psi ≠ 1)
    {C B Q delta : ℝ} {K : ℕ}
    (hC : 0 < C) (hB : 1 ≤ B) (hCB : 8 * C ≤ B) (hQ : 1 ≤ Q)
    (hdelta : 0 < delta) (hdeltaUpper : delta ≤ 1 / 8)
    (hcoeff : ∀ m, ‖siegelRegularCoefficient chi psi m‖ ≤
      C * Q ^ K * (2 / 3 : ℝ) ^ m)
    (hsmall : 2 * (Real.exp 2 * B) * (siegelProductResidue chi psi).re *
      Q ^ ((4 * K : ℝ) * delta) < delta) :
    0 < (siegelProductValue chi psi (1 - delta)).re := by
  let cutoff := siegelTruncationIndex B Q K
  have hcutoff : 0 < cutoff := by
    dsimp [cutoff, siegelTruncationIndex]
    omega
  have hresidue := siegelProductResidue_nonneg chi psi hchiSquare hpsiSquare hchi hpsi hmul
  have hresidueRe : 0 ≤ (siegelProductResidue chi psi).re :=
    (Complex.le_def.mp hresidue).1
  have htruncation := siegelTruncation_spec (K := K)
    hC.le hB hCB hQ hdelta.le hdeltaUpper
  have htail : 4 * (C * Q ^ K) * (3 / 4 : ℝ) ^ cutoff < 1 / 2 := by
    simpa only [mul_assoc] using htruncation.1
  have hpoleGrowth : (1 + delta) ^ cutoff ≤
      Real.exp 2 * B * Q ^ ((4 * K : ℝ) * delta) := htruncation.2
  have hpoleNumerator :
      (siegelProductResidue chi psi).re * (1 + delta) ^ cutoff ≤
        (siegelProductResidue chi psi).re *
          (Real.exp 2 * B * Q ^ ((4 * K : ℝ) * delta)) :=
    mul_le_mul_of_nonneg_left hpoleGrowth hresidueRe
  have hpole :
      (siegelProductResidue chi psi).re * (1 + delta) ^ cutoff / delta < 1 / 2 := by
    calc
      (siegelProductResidue chi psi).re * (1 + delta) ^ cutoff / delta ≤
          (siegelProductResidue chi psi).re *
            (Real.exp 2 * B * Q ^ ((4 * K : ℝ) * delta)) / delta :=
        div_le_div_of_nonneg_right hpoleNumerator hdelta.le
      _ < 1 / 2 := by
        rw [div_lt_iff₀ hdelta]
        ring_nf at hsmall ⊢
        linarith
  have hlower := siegelProductValue_re_lower_bound chi psi hchiSquare hpsiSquare
    hchi hpsi hmul (mul_nonneg hC.le (pow_nonneg (zero_le_one.trans hQ) K))
    hdelta hdeltaUpper hcutoff hcoeff
  linarith

end BombieriVinogradov.SiegelWalfisz

end

section

open scoped ComplexOrder

namespace BombieriVinogradov.SiegelWalfisz

theorem siegelProduct_pos :
    ∃ C : ℝ, 0 < C ∧ ∃ D : ℕ,
      ∀ {N M : ℕ} [NeZero N] [NeZero M] [NeZero (N.lcm M)]
        (chi : DirichletCharacter ℂ N) (psi : DirichletCharacter ℂ M),
        chi ^ 2 = 1 → psi ^ 2 = 1 → chi ≠ 1 → psi ≠ 1 →
          DirichletCharacter.mul chi psi ≠ 1 →
          ∀ s : ℝ, 7 / 8 ≤ s → s < 1 →
            C * ‖siegelProductResidue chi psi‖ <
              (1 - s) * ((N : ℝ) * (M : ℝ)) ^ (-(D : ℝ) * (1 - s)) →
              0 < (siegelProductValue chi psi s).re := by
  obtain ⟨C0, hC0, K, hcoeff⟩ := siegelProduct_coefficient_bound
  let B : ℝ := max 1 (8 * C0)
  have hB : 1 ≤ B := le_max_left _ _
  have hC0B : 8 * C0 ≤ B := le_max_right _ _
  have hBpos : 0 < B := zero_lt_one.trans_le hB
  refine ⟨2 * (Real.exp 2 * B), mul_pos (by norm_num) (mul_pos (Real.exp_pos 2) hBpos),
    4 * K, ?_⟩
  intro N M instN instM instLcm chi psi hchiSquare hpsiSquare hchi hpsi hmul s hsLower hsUpper hsmall
  let Q : ℝ := (N : ℝ) * (M : ℝ)
  let delta : ℝ := 1 - s
  have hdelta : 0 < delta := sub_pos.mpr hsUpper
  have hdeltaUpper : delta ≤ 1 / 8 := by
    dsimp [delta]
    linarith
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast NeZero.pos N
  have hM : (1 : ℝ) ≤ M := by exact_mod_cast NeZero.pos M
  have hQ : 1 ≤ Q := by
    dsimp [Q]
    nlinarith [mul_le_mul hN hM (by norm_num : (0 : ℝ) ≤ 1) (by linarith : (0 : ℝ) ≤ N)]
  have hQpos : 0 < Q := zero_lt_one.trans_le hQ
  have hQ0 : 0 ≤ Q := hQpos.le
  have hresidue := siegelProductResidue_nonneg chi psi hchiSquare hpsiSquare hchi hpsi hmul
  have hresidueParts := Complex.le_def.mp hresidue
  have hnormResidue : ‖siegelProductResidue chi psi‖ =
      (siegelProductResidue chi psi).re := by
    have habs := Complex.abs_re_eq_norm.mpr hresidueParts.2.symm
    rw [abs_of_nonneg hresidueParts.1] at habs
    exact habs.symm
  have hsourceSmall :
      2 * (Real.exp 2 * B) * (siegelProductResidue chi psi).re *
        Q ^ ((4 * K : ℝ) * delta) < delta := by
    have hsmall' : 2 * (Real.exp 2 * B) * (siegelProductResidue chi psi).re <
        delta * Q ^ (-((4 * K : ℝ) * delta)) := by
      simpa [Q, delta, hnormResidue] using hsmall
    have hpowPos : 0 < Q ^ ((4 * K : ℝ) * delta) := Real.rpow_pos_of_pos hQpos _
    calc
      2 * (Real.exp 2 * B) * (siegelProductResidue chi psi).re *
          Q ^ ((4 * K : ℝ) * delta) <
        (delta * Q ^ (-((4 * K : ℝ) * delta))) *
          Q ^ ((4 * K : ℝ) * delta) :=
        mul_lt_mul_of_pos_right hsmall' hpowPos
      _ = delta := by
        rw [Real.rpow_neg hQ0]
        field_simp
  have hpositive := siegelProduct_pos_of_coefficient_bound chi psi hchiSquare hpsiSquare
    hchi hpsi hmul hC0 hB hC0B hQ hdelta hdeltaUpper
    (fun m => by simpa [Q, mul_assoc] using hcoeff chi psi hchi hpsi hmul m) hsourceSmall
  simpa [delta] using hpositive

end BombieriVinogradov.SiegelWalfisz

end

section

namespace BombieriVinogradov.SiegelWalfisz

def IsSiegelPositivityPair (C : ℝ) (D : ℕ) : Prop :=
  0 < C ∧
    ∀ {N M : ℕ} [NeZero N] [NeZero M] [NeZero (N.lcm M)]
      (chi : DirichletCharacter ℂ N) (psi : DirichletCharacter ℂ M),
      chi ^ 2 = 1 → psi ^ 2 = 1 → chi ≠ 1 → psi ≠ 1 →
        DirichletCharacter.mul chi psi ≠ 1 →
        ∀ s : ℝ, 7 / 8 ≤ s → s < 1 →
          C * ‖siegelProductResidue chi psi‖ <
            (1 - s) * ((N : ℝ) * (M : ℝ)) ^ (-(D : ℝ) * (1 - s)) →
            0 < (siegelProductValue chi psi s).re

theorem exists_siegelPositivityPair :
    ∃ C : ℝ, ∃ D : ℕ, IsSiegelPositivityPair C D := by
  obtain ⟨C, hC, D, hpos⟩ := siegelProduct_pos
  exact ⟨C, D, hC, hpos⟩

end BombieriVinogradov.SiegelWalfisz

end

section

namespace BombieriVinogradov.SiegelWalfisz

theorem siegelProductResidue_lower_of_nonpos {C : ℝ} {D : ℕ}
    (hpair : IsSiegelPositivityPair C D)
    {N M : ℕ} [NeZero N] [NeZero M] [NeZero (N.lcm M)]
    (chi : DirichletCharacter ℂ N) (psi : DirichletCharacter ℂ M)
    (hchiSquare : chi ^ 2 = 1) (hpsiSquare : psi ^ 2 = 1)
    (hchi : chi ≠ 1) (hpsi : psi ≠ 1)
    (hmul : DirichletCharacter.mul chi psi ≠ 1)
    {s : ℝ} (hsLower : 7 / 8 ≤ s) (hsUpper : s < 1)
    (hnonpos : (siegelProductValue chi psi s).re ≤ 0) :
    (1 - s) * ((N : ℝ) * (M : ℝ)) ^ (-(D : ℝ) * (1 - s)) ≤
      C * ‖siegelProductResidue chi psi‖ := by
  apply le_of_not_gt
  intro hsmall
  have hpositive := hpair.2 chi psi hchiSquare hpsiSquare hchi hpsi hmul
    s hsLower hsUpper hsmall
  linarith

end BombieriVinogradov.SiegelWalfisz

end

section

namespace BombieriVinogradov.SiegelWalfisz

theorem norm_siegelProductResidue_le_log {N M : ℕ}
    [NeZero N] [NeZero M] [NeZero (N.lcm M)]
    (chi : DirichletCharacter ℂ N) (psi : DirichletCharacter ℂ M)
    (hchi : chi ≠ 1) (hmul : DirichletCharacter.mul chi psi ≠ 1) :
    ‖siegelProductResidue chi psi‖ ≤
      characterLLogBoundConstant ^ 2 * (1 + Real.log N) *
        (1 + Real.log (N.lcm M)) * ‖psi.LFunction 1‖ := by
  have hchiBound := norm_LFunction_one_le_log chi hchi
  have hmulBound := norm_LFunction_one_le_log (DirichletCharacter.mul chi psi) hmul
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast NeZero.pos N
  have hlogN : 0 ≤ 1 + Real.log N := by linarith [Real.log_nonneg hN]
  have hfirstUpper : 0 ≤
      (characterLLogBoundConstant * (1 + Real.log N)) * ‖psi.LFunction 1‖ :=
    mul_nonneg (mul_nonneg characterLLogBoundConstant_pos.le hlogN) (norm_nonneg _)
  rw [siegelProductResidue, norm_mul, norm_mul]
  calc
    ‖chi.LFunction 1‖ * ‖psi.LFunction 1‖ *
        ‖(DirichletCharacter.mul chi psi).LFunction 1‖ ≤
      (characterLLogBoundConstant * (1 + Real.log N)) *
        ‖psi.LFunction 1‖ *
          (characterLLogBoundConstant * (1 + Real.log (N.lcm M))) := by
      exact mul_le_mul (mul_le_mul_of_nonneg_right hchiBound (norm_nonneg _)) hmulBound
        (norm_nonneg _) hfirstUpper
    _ = characterLLogBoundConstant ^ 2 * (1 + Real.log N) *
        (1 + Real.log (N.lcm M)) * ‖psi.LFunction 1‖ := by ring

theorem targetLValue_transfer {C : ℝ} {D : ℕ}
    (hpair : IsSiegelPositivityPair C D)
    {N M : ℕ} [NeZero N] [NeZero M] [NeZero (N.lcm M)]
    (chi : DirichletCharacter ℂ N) (psi : DirichletCharacter ℂ M)
    (hchiSquare : chi ^ 2 = 1) (hpsiSquare : psi ^ 2 = 1)
    (hchi : chi ≠ 1) (hpsi : psi ≠ 1)
    (hmul : DirichletCharacter.mul chi psi ≠ 1)
    {s : ℝ} (hsLower : 7 / 8 ≤ s) (hsUpper : s < 1)
    (hnonpos : (siegelProductValue chi psi s).re ≤ 0) :
    (1 - s) * ((N : ℝ) * (M : ℝ)) ^ (-(D : ℝ) * (1 - s)) ≤
      C * (characterLLogBoundConstant ^ 2 * (1 + Real.log N) *
        (1 + Real.log (N.lcm M)) * ‖psi.LFunction 1‖) := by
  exact (siegelProductResidue_lower_of_nonpos hpair chi psi hchiSquare hpsiSquare
    hchi hpsi hmul hsLower hsUpper hnonpos).trans
      (mul_le_mul_of_nonneg_left (norm_siegelProductResidue_le_log chi psi hchi hmul)
        hpair.1.le)

end BombieriVinogradov.SiegelWalfisz

end

section

namespace BombieriVinogradov.SiegelWalfisz

noncomputable def siegelLargeLevelDenominator
    (C : ℝ) (N : ℕ) (delta : ℝ) : ℝ :=
  C * characterLLogBoundConstant ^ 2 * (1 + Real.log N) * (1 + delta⁻¹)

theorem siegelLargeLevelDenominator_pos {C delta : ℝ} {N : ℕ}
    (hC : 0 < C) (hN : 0 < N) (hdelta : 0 < delta) :
    0 < siegelLargeLevelDenominator C N delta := by
  have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hlog : 0 < 1 + Real.log N := by
    linarith [Real.log_nonneg hNreal]
  have hinverse : 0 < 1 + delta⁻¹ := by
    have : 0 < delta⁻¹ := inv_pos.mpr hdelta
    linarith
  unfold siegelLargeLevelDenominator
  exact mul_pos (mul_pos (mul_pos hC (pow_pos characterLLogBoundConstant_pos 2)) hlog)
    hinverse

noncomputable def siegelLargeLevelConstant
    (C epsilon s : ℝ) (N : ℕ) : ℝ :=
  ((1 - s) / siegelLargeLevelDenominator C N (epsilon / 2)) *
    (N : ℝ) ^ (-epsilon)

theorem siegelLargeLevelConstant_pos {C epsilon s : ℝ} {N : ℕ}
    (hC : 0 < C) (hepsilon : 0 < epsilon) (hN : 0 < N) (hs : s < 1) :
    0 < siegelLargeLevelConstant C epsilon s N := by
  have hdenominator := siegelLargeLevelDenominator_pos hC hN
    (div_pos hepsilon zero_lt_two)
  unfold siegelLargeLevelConstant
  exact mul_pos (div_pos (sub_pos.mpr hs) hdenominator)
    (Real.rpow_pos_of_pos (by exact_mod_cast hN) (-epsilon))

end BombieriVinogradov.SiegelWalfisz

end

section

namespace BombieriVinogradov.SiegelWalfisz

theorem one_add_log_le_rpow_mul {x delta : ℝ}
    (hx : 1 ≤ x) (hdelta : 0 < delta) :
    1 + Real.log x ≤ (1 + delta⁻¹) * x ^ delta := by
  have hpow : 1 ≤ x ^ delta := by
    simpa using Real.rpow_le_rpow zero_le_one hx hdelta.le
  have hlog := Real.log_le_rpow_div (zero_le_one.trans hx) hdelta
  calc
    1 + Real.log x ≤ x ^ delta + x ^ delta / delta := add_le_add hpow hlog
    _ = (1 + delta⁻¹) * x ^ delta := by
      rw [div_eq_mul_inv]
      ring

theorem one_add_log_lcm_le_rpow_mul {N M : ℕ}
    (hN : 0 < N) (hM : 0 < M) {delta : ℝ} (hdelta : 0 < delta) :
    1 + Real.log (N.lcm M) ≤
      (1 + delta⁻¹) * ((N : ℝ) * (M : ℝ)) ^ delta := by
  have hmul : 0 < N * M := Nat.mul_pos hN hM
  have hlcmNat : N.lcm M ≤ N * M :=
    Nat.le_of_dvd hmul (Nat.lcm_dvd_mul N M)
  have hlcm : (0 : ℝ) < N.lcm M := by
    exact_mod_cast Nat.pos_of_ne_zero (Nat.lcm_ne_zero hN.ne' hM.ne')
  have hlcmMul : (N.lcm M : ℝ) ≤ (N * M : ℕ) := by
    exact_mod_cast hlcmNat
  have hproduct : (1 : ℝ) ≤ (N * M : ℕ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr hmul.ne'
  calc
    1 + Real.log (N.lcm M) ≤ 1 + Real.log (N * M : ℕ) := by
      simpa [add_comm] using add_le_add_left (Real.log_le_log hlcm hlcmMul) 1
    _ ≤ (1 + delta⁻¹) * (N * M : ℕ) ^ delta :=
      one_add_log_le_rpow_mul hproduct hdelta
    _ = (1 + delta⁻¹) * ((N : ℝ) * (M : ℝ)) ^ delta := by
      norm_num

end BombieriVinogradov.SiegelWalfisz

end

section

namespace BombieriVinogradov.SiegelWalfisz

theorem weighted_rpow_transfer {prefactor bound base exponent delta epsilon value : ℝ}
    (hprefactor : 0 < prefactor) (hbound : 0 < bound) (hbase : 1 ≤ base)
    (hsum : exponent + delta ≤ epsilon)
    (hweighted : prefactor * base ^ (-exponent) ≤
      bound * base ^ delta * value) :
    (prefactor / bound) * base ^ (-epsilon) ≤ value := by
  have hbasePos : 0 < base := zero_lt_one.trans_le hbase
  have hpowerDelta : 0 < base ^ delta := Real.rpow_pos_of_pos hbasePos delta
  have hdenominator : 0 < bound * base ^ delta := mul_pos hbound hpowerDelta
  have hdivided :
      (prefactor * base ^ (-exponent)) / (bound * base ^ delta) ≤ value := by
    rw [div_le_iff₀ hdenominator]
    simpa [mul_assoc, mul_comm, mul_left_comm] using hweighted
  have hquotient :
      (prefactor * base ^ (-exponent)) / (bound * base ^ delta) =
        (prefactor / bound) * base ^ (-(exponent + delta)) := by
    rw [show -(exponent + delta) = -exponent + -delta by ring,
      Real.rpow_add hbasePos, Real.rpow_neg hbasePos.le]
    field_simp
    rw [← Real.rpow_add hbasePos]
    norm_num
  have hpower : base ^ (-epsilon) ≤ base ^ (-(exponent + delta)) :=
    Real.rpow_le_rpow_of_exponent_le hbase (by linarith)
  calc
    (prefactor / bound) * base ^ (-epsilon) ≤
        (prefactor / bound) * base ^ (-(exponent + delta)) :=
      mul_le_mul_of_nonneg_left hpower (div_nonneg hprefactor.le hbound.le)
    _ = (prefactor * base ^ (-exponent)) / (bound * base ^ delta) :=
      hquotient.symm
    _ ≤ value := hdivided

end BombieriVinogradov.SiegelWalfisz

end

section

open Filter Metric Set

namespace BombieriVinogradov.SiegelWalfisz

theorem riemannZeta_im_real (s : ℝ) : (riemannZeta s).im = 0 := by
  have hsym := riemannZeta_conj (s : ℂ)
  have him := congrArg Complex.im hsym
  simp at him
  linarith

theorem exists_riemannZeta_neg_left :
    ∃ eta : ℝ, 0 < eta ∧
      ∀ s : ℝ, 1 - eta < s → s < 1 → (riemannZeta s).re < 0 := by
  have hofReal : Tendsto (fun s : ℝ ↦ (s : ℂ))
      (nhdsWithin 1 (Iio 1)) (nhdsWithin 1 ({1}ᶜ : Set ℂ)) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · exact Complex.continuous_ofReal.continuousAt.tendsto.mono_left inf_le_left
    · filter_upwards [self_mem_nhdsWithin] with s hs
      have hsne : s ≠ 1 := ne_of_lt (Set.mem_Iio.mp hs)
      change (s : ℂ) ≠ 1
      exact_mod_cast hsne
  have hresidue : Tendsto
      (fun s : ℝ ↦ (((s : ℂ) - 1) * riemannZeta s).re)
      (nhdsWithin 1 (Iio 1)) (nhds 1) := by
    convert Complex.continuous_re.continuousAt.tendsto.comp
      (riemannZeta_residue_one.comp hofReal) using 1 <;>
        simp [Function.comp_def]
  have heventually : ∀ᶠ s : ℝ in nhdsWithin 1 (Iio 1),
      0 < (((s : ℂ) - 1) * riemannZeta s).re :=
    hresidue (Ioi_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  obtain ⟨eta, heta, hball⟩ := Metric.mem_nhdsWithin_iff.mp heventually
  refine ⟨eta, heta, ?_⟩
  intro s hsLower hsUpper
  have hdist : dist s 1 < eta := by
    rw [Real.dist_eq]
    rw [abs_of_nonpos (sub_nonpos.mpr hsUpper.le)]
    linarith
  have hproduct : 0 < (((s : ℂ) - 1) * riemannZeta s).re :=
    hball ⟨hdist, hsUpper⟩
  have him := riemannZeta_im_real s
  simp only [Complex.mul_re, Complex.sub_re, Complex.ofReal_re, Complex.one_re,
    Complex.sub_im, Complex.ofReal_im, Complex.one_im, zero_mul,
    sub_zero] at hproduct
  nlinarith

end BombieriVinogradov.SiegelWalfisz

end

section

namespace BombieriVinogradov.SiegelWalfisz

theorem exists_siegelComparisonPoint {lower : ℝ}
    (hlower : 7 / 8 ≤ lower) (hupper : lower < 1) :
    ∃ s : ℝ, lower ≤ s ∧ 7 / 8 ≤ s ∧ s < 1 ∧ (riemannZeta s).re < 0 := by
  obtain ⟨eta, heta, hzeta⟩ := exists_riemannZeta_neg_left
  let s := max lower (1 - eta / 2)
  have hlowerS : lower ≤ s := le_max_left _ _
  have hsevenS : 7 / 8 ≤ s := hlower.trans hlowerS
  have hsUpper : s < 1 := by
    apply max_lt hupper
    linarith
  have hetaS : 1 - eta < s := by
    have : 1 - eta < 1 - eta / 2 := by linarith
    exact this.trans_le (le_max_right _ _)
  exact ⟨s, hlowerS, hsevenS, hsUpper, hzeta s hetaS hsUpper⟩

end BombieriVinogradov.SiegelWalfisz

end

section

namespace BombieriVinogradov.SiegelWalfisz

theorem real_mem_siegelAnalyticDomain {s : ℝ} (hsLower : 7 / 8 ≤ s)
    (hsUpper : s ≤ 1) : (s : ℂ) ∈ siegelAnalyticDomain := by
  rw [siegelAnalyticDomain, Metric.mem_ball, Complex.dist_eq]
  have hnonpos : s - 2 ≤ 0 := by linarith
  rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonpos hnonpos]
  norm_num at hsLower ⊢
  linarith

private theorem characterLBlock_im_eq_zero_bv675 {N : ℕ} [NeZero N]
    (chi : DirichletCharacter ℂ N) (hchiSquare : chi ^ 2 = 1)
    (k : ℕ) (s : ℝ) : (characterLBlock chi k s).im = 0 := by
  rw [characterLBlock, Complex.im_sum]
  apply Finset.sum_eq_zero
  intro j hj
  rcases MulChar.isQuadratic_iff_sq_eq_one.mpr hchiSquare j with hzero | hone | hneg
  · simp [hzero]
  · rw [hone, show (-(s : ℂ)) = ((-s : ℝ) : ℂ) by norm_num,
      ← Complex.ofReal_natCast (k * N + j.val),
      ← Complex.ofReal_cpow (Nat.cast_nonneg (k * N + j.val)) (-s)]
    simp
  · rw [hneg, show (-(s : ℂ)) = ((-s : ℝ) : ℂ) by norm_num,
      ← Complex.ofReal_natCast (k * N + j.val),
      ← Complex.ofReal_cpow (Nat.cast_nonneg (k * N + j.val)) (-s)]
    simp

theorem quadraticLFunction_im_eq_zero {N : ℕ} [NeZero N]
    (chi : DirichletCharacter ℂ N) (hchiSquare : chi ^ 2 = 1) (hchi : chi ≠ 1)
    {s : ℝ} (hs : (s : ℂ) ∈ siegelAnalyticDomain) :
    (chi.LFunction s).im = 0 := by
  have hsum : Summable (fun k : ℕ ↦ characterLBlock chi k s) := by
    apply Summable.of_norm
    exact (characterLBlockMajorant_summable N).of_nonneg_of_le
      (fun k ↦ norm_nonneg _) fun k ↦ norm_characterLBlock_le chi hchi k hs
  rw [LFunction_eq_characterLBlockSeries chi hchi hs, characterLBlockSeries,
    Complex.im_tsum hsum]
  convert tsum_zero with k
  exact characterLBlock_im_eq_zero_bv675 chi hchiSquare k s

end BombieriVinogradov.SiegelWalfisz

end

section

open Set

namespace BombieriVinogradov.SiegelWalfisz

theorem quadraticLFunction_re_pos_of_no_zero {N : ℕ} [NeZero N]
    (chi : DirichletCharacter ℂ N) (hchiSquare : chi ^ 2 = 1) (hchi : chi ≠ 1)
    {s : ℝ} (hsLower : 7 / 8 ≤ s) (hsUpper : s < 1)
    (hnozero : ∀ t : ℝ, s ≤ t → t ≤ 1 → chi.LFunction t ≠ 0) :
    0 < (chi.LFunction s).re := by
  let f : ℝ → ℝ := fun t ↦ (chi.LFunction t).re
  have hfcont : Continuous f := by
    exact Complex.continuous_re.comp
      ((chi.differentiable_LFunction hchi).continuous.comp Complex.continuous_ofReal)
  have hone : 0 < f 1 := quadraticLFunction_one_re_pos chi hchiSquare hchi
  by_contra hnot
  have himS := quadraticLFunction_im_eq_zero chi hchiSquare hchi
    (real_mem_siegelAnalyticDomain hsLower hsUpper.le)
  have hfs_ne : f s ≠ 0 := by
    intro hfs
    apply hnozero s le_rfl hsUpper.le
    apply Complex.ext
    · simpa [f] using hfs
    · simpa using himS
  have hfsNeg : f s < 0 := lt_of_le_of_ne (le_of_not_gt hnot) hfs_ne
  have hzeroMem : 0 ∈ Icc (f s) (f 1) := ⟨hfsNeg.le, hone.le⟩
  obtain ⟨t, ht, hft⟩ := intermediate_value_Icc hsUpper.le hfcont.continuousOn hzeroMem
  have himT := quadraticLFunction_im_eq_zero chi hchiSquare hchi
    (real_mem_siegelAnalyticDomain (hsLower.trans ht.1) ht.2)
  apply hnozero t ht.1 ht.2
  apply Complex.ext
  · simpa [f] using hft
  · simpa using himT

end BombieriVinogradov.SiegelWalfisz

end

section

open scoped ComplexOrder

namespace BombieriVinogradov.SiegelWalfisz

theorem quadraticLFunction_re_pos_of_primitive_no_zero {N : ℕ} [NeZero N]
    (chi : DirichletCharacter ℂ N) [NeZero chi.conductor]
    (hchiSquare : chi ^ 2 = 1) (hchi : chi ≠ 1)
    {s : ℝ} (hsLower : 7 / 8 ≤ s) (hsUpper : s < 1)
    (hnozero : ∀ t : ℝ, s ≤ t → t ≤ 1 →
      chi.primitiveCharacter.LFunction t ≠ 0) :
    0 < (chi.LFunction s).re := by
  have hprimitiveNe := primitiveCharacter_ne_one chi hchi
  have hprimitiveSquare := primitiveCharacter_sq_eq_one chi hchiSquare
  have hprimitivePos := quadraticLFunction_re_pos_of_no_zero chi.primitiveCharacter
    hprimitiveSquare hprimitiveNe hsLower hsUpper hnozero
  have hcorrection := characterLevelCorrection_pos chi hchiSquare
    (show 0 < s by linarith)
  have hcorrectionParts := Complex.lt_def.mp hcorrection
  have hprimitiveIm := quadraticLFunction_im_eq_zero chi.primitiveCharacter
    hprimitiveSquare hprimitiveNe
    (real_mem_siegelAnalyticDomain hsLower hsUpper.le)
  rw [LFunction_eq_primitive_mul_correction chi hchi, Complex.mul_re]
  rw [hprimitiveIm]
  norm_num
  exact mul_pos hprimitivePos (by simpa using hcorrectionParts.1)

end BombieriVinogradov.SiegelWalfisz

end

section

namespace BombieriVinogradov.SiegelWalfisz

theorem siegelProductValue_re_eq_product {N M : ℕ}
    [NeZero N] [NeZero M] [NeZero (N.lcm M)]
    (chi : DirichletCharacter ℂ N) (psi : DirichletCharacter ℂ M)
    (hchiSquare : chi ^ 2 = 1) (hpsiSquare : psi ^ 2 = 1)
    (hchi : Ne chi 1) (hpsi : Ne psi 1)
    (hmul : Ne (DirichletCharacter.mul chi psi) 1)
    {s : ℝ} (hsLower : 7 / 8 ≤ s) (hsUpper : s < 1) :
    (siegelProductValue chi psi s).re =
      (riemannZeta s).re * (chi.LFunction s).re * (psi.LFunction s).re *
        ((DirichletCharacter.mul chi psi).LFunction s).re := by
  have hmulSquare := crossLevelMul_sq_eq_one chi psi hchiSquare hpsiSquare
  have hzetaIm := riemannZeta_im_real s
  have hchiIm := quadraticLFunction_im_eq_zero chi hchiSquare hchi
    (real_mem_siegelAnalyticDomain hsLower hsUpper.le)
  have hpsiIm := quadraticLFunction_im_eq_zero psi hpsiSquare hpsi
    (real_mem_siegelAnalyticDomain hsLower hsUpper.le)
  have hmulIm := quadraticLFunction_im_eq_zero (DirichletCharacter.mul chi psi)
    hmulSquare hmul (real_mem_siegelAnalyticDomain hsLower hsUpper.le)
  simp only [siegelProductValue, siegelLProduct, Complex.mul_re, Complex.mul_im,
    hzetaIm, hchiIm, hpsiIm, hmulIm, mul_zero, zero_mul, add_zero, sub_zero]
  ring

end BombieriVinogradov.SiegelWalfisz

end

section

namespace BombieriVinogradov.SiegelWalfisz

def PrimitiveQuadraticZeroFreeFrom (s : ℝ) : Prop :=
  ∀ (N : ℕ) [NeZero N] (chi : DirichletCharacter ℂ N),
    DirichletCharacter.IsPrimitive chi -> chi ^ 2 = 1 -> Ne chi 1 ->
      ∀ t : ℝ, s ≤ t -> t ≤ 1 -> Ne (chi.LFunction t) 0

theorem PrimitiveQuadraticZeroFreeFrom.mono {lower s : ℝ}
    (hzeroFree : PrimitiveQuadraticZeroFreeFrom lower) (h : lower ≤ s) :
    PrimitiveQuadraticZeroFreeFrom s := by
  intro N _ chi hprimitive hsquare hne t hst ht
  exact hzeroFree N chi hprimitive hsquare hne t (h.trans hst) ht

end BombieriVinogradov.SiegelWalfisz

end

section

namespace BombieriVinogradov.SiegelWalfisz

theorem siegelProductValue_nonpos_of_left_zero {N M : ℕ}
    [NeZero N] [NeZero M] [NeZero (N.lcm M)]
    (chi : DirichletCharacter ℂ N) (psi : DirichletCharacter ℂ M)
    {s : ℝ} (hzero : chi.LFunction s = 0) :
    (siegelProductValue chi psi s).re ≤ 0 := by
  simp [siegelProductValue, siegelLProduct, hzero]

theorem quadraticCharacterFour_product_nonpos_of_zeroFree {M : ℕ}
    [NeZero M] [NeZero ((4 : ℕ).lcm M)]
    (psi : DirichletCharacter ℂ M)
    (hpsiPrimitive : DirichletCharacter.IsPrimitive psi)
    (hpsiSquare : psi ^ 2 = 1) (hpsi : Ne psi 1)
    (hM : 4 < M) {s : ℝ} (hsLower : 7 / 8 ≤ s) (hsUpper : s < 1)
    (hzeta : (riemannZeta s).re < 0)
    (hzeroFree : PrimitiveQuadraticZeroFreeFrom s) :
    (siegelProductValue quadraticCharacterFour psi s).re ≤ 0 := by
  have hlevels : Ne 4 M := Ne.symm (Nat.ne_of_gt hM)
  have hmul := crossLevelMul_ne_one_of_primitive_of_ne quadraticCharacterFour psi
    quadraticCharacterFour_isPrimitive hpsiPrimitive hlevels
  have hmulSquare := crossLevelMul_sq_eq_one quadraticCharacterFour psi
    quadraticCharacterFour_sq hpsiSquare
  have hfourNoZero := hzeroFree 4 quadraticCharacterFour
    quadraticCharacterFour_isPrimitive quadraticCharacterFour_sq
      quadraticCharacterFour_ne_one
  have hfourPos := quadraticLFunction_re_pos_of_no_zero quadraticCharacterFour
    quadraticCharacterFour_sq quadraticCharacterFour_ne_one hsLower hsUpper hfourNoZero
  have hpsiNoZero := hzeroFree M psi hpsiPrimitive hpsiSquare hpsi
  have hpsiPos := quadraticLFunction_re_pos_of_no_zero psi hpsiSquare hpsi
    hsLower hsUpper hpsiNoZero
  let _ : NeZero (DirichletCharacter.mul quadraticCharacterFour psi).conductor :=
    ⟨(DirichletCharacter.mul quadraticCharacterFour psi).conductor_ne_zero⟩
  have hmulPrimitiveSquare := primitiveCharacter_sq_eq_one
    (DirichletCharacter.mul quadraticCharacterFour psi) hmulSquare
  have hmulPrimitiveNe := primitiveCharacter_ne_one
    (DirichletCharacter.mul quadraticCharacterFour psi) hmul
  have hmulPrimitiveNoZero := hzeroFree
    (DirichletCharacter.mul quadraticCharacterFour psi).conductor
    (DirichletCharacter.mul quadraticCharacterFour psi).primitiveCharacter
    (DirichletCharacter.mul quadraticCharacterFour psi).primitiveCharacter_isPrimitive
    hmulPrimitiveSquare hmulPrimitiveNe
  have hmulPos := quadraticLFunction_re_pos_of_primitive_no_zero
    (DirichletCharacter.mul quadraticCharacterFour psi) hmulSquare hmul
      hsLower hsUpper hmulPrimitiveNoZero
  rw [siegelProductValue_re_eq_product quadraticCharacterFour psi
    quadraticCharacterFour_sq hpsiSquare quadraticCharacterFour_ne_one hpsi hmul
      hsLower hsUpper]
  exact (mul_neg_of_neg_of_pos
    (mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hzeta hfourPos) hpsiPos)
      hmulPos).le

end BombieriVinogradov.SiegelWalfisz

end

section

namespace BombieriVinogradov.SiegelWalfisz

def IsSiegelSeed (lower : ℝ) (N : ℕ) (chi : DirichletCharacter ℂ N)
    (s : ℝ) : Prop :=
  0 < N ∧ DirichletCharacter.IsPrimitive chi ∧ chi ^ 2 = 1 ∧ Ne chi 1 ∧
    lower ≤ s ∧ 7 / 8 ≤ s ∧ s < 1 ∧
      ∀ (M : ℕ) [NeZero N] [NeZero M] [NeZero (N.lcm M)]
        (psi : DirichletCharacter ℂ M), N < M ->
          DirichletCharacter.IsPrimitive psi -> psi ^ 2 = 1 -> Ne psi 1 ->
            (siegelProductValue chi psi s).re ≤ 0

theorem exists_siegelSeed {lower : ℝ}
    (hlower : 7 / 8 ≤ lower) (hupper : lower < 1) :
    ∃ (N : ℕ) (chi : DirichletCharacter ℂ N) (s : ℝ),
      IsSiegelSeed lower N chi s := by
  by_cases hzeroFree : PrimitiveQuadraticZeroFreeFrom lower
  · obtain ⟨s, hlowerS, hsevenS, hsUpper, hzeta⟩ :=
      exists_siegelComparisonPoint hlower hupper
    have hzeroFreeS := hzeroFree.mono hlowerS
    refine ⟨4, quadraticCharacterFour, s, ?_⟩
    refine ⟨by norm_num, quadraticCharacterFour_isPrimitive,
      quadraticCharacterFour_sq, quadraticCharacterFour_ne_one,
      hlowerS, hsevenS, hsUpper, ?_⟩
    intro M _ _ _ psi hM hpsiPrimitive hpsiSquare hpsi
    exact quadraticCharacterFour_product_nonpos_of_zeroFree psi hpsiPrimitive
      hpsiSquare hpsi hM hsevenS hsUpper hzeta hzeroFreeS
  · rw [PrimitiveQuadraticZeroFreeFrom] at hzeroFree
    push Not at hzeroFree
    obtain ⟨N, hN, chi, hprimitive, hchiSquare, hchi, s,
      hlowerS, hsOne, hzero⟩ := hzeroFree
    let _ : NeZero N := hN
    have hsUpper : s < 1 := by
      apply lt_of_le_of_ne hsOne
      intro hs
      apply chi.LFunction_apply_one_ne_zero hchi
      simpa [hs] using hzero
    refine ⟨N, chi, s, ?_⟩
    refine ⟨NeZero.pos N, hprimitive, hchiSquare, hchi,
      hlowerS, hlower.trans hlowerS, hsUpper, ?_⟩
    intro M _ _ _ psi _ _ _ _
    exact siegelProductValue_nonpos_of_left_zero chi psi hzero

end BombieriVinogradov.SiegelWalfisz

end

section

namespace BombieriVinogradov.SiegelWalfisz

theorem siegelLowerBound_largeLevel {C epsilon : ℝ} {D N : ℕ}
    {chi : DirichletCharacter ℂ N} {s : ℝ}
    (hpair : IsSiegelPositivityPair C D) (hepsilon : 0 < epsilon)
    (hseed : IsSiegelSeed (siegelLowerEndpoint epsilon D) N chi s) :
    ∀ (M : ℕ) [NeZero M] [NeZero (N.lcm M)]
      (psi : DirichletCharacter ℂ M), N < M ->
        DirichletCharacter.IsPrimitive psi -> psi ^ 2 = 1 -> Ne psi 1 ->
          siegelLargeLevelConstant C epsilon s N * (M : ℝ) ^ (-epsilon) ≤
            (psi.LFunction 1).re := by
  obtain ⟨hN, hchiPrimitive, hchiSquare, hchi, hlowerS,
    hsevenS, hsUpper, hseedNonpos⟩ := hseed
  let _ : NeZero N := ⟨hN.ne'⟩
  intro M _ _ psi hNM hpsiPrimitive hpsiSquare hpsi
  have hM : 0 < M := NeZero.pos M
  have hmul := crossLevelMul_ne_one_of_primitive_of_ne chi psi
    hchiPrimitive hpsiPrimitive (Ne.symm (Nat.ne_of_gt hNM))
  have hnonpos := hseedNonpos M psi hNM hpsiPrimitive hpsiSquare hpsi
  have hraw := targetLValue_transfer hpair chi psi hchiSquare hpsiSquare
    hchi hpsi hmul hsevenS hsUpper hnonpos
  have hnorm := norm_quadraticLFunction_one_eq_re psi hpsiSquare hpsi
  rw [hnorm] at hraw
  have hvaluePos := quadraticLFunction_one_re_pos psi hpsiSquare hpsi
  let delta : ℝ := epsilon / 2
  let base : ℝ := (N : ℝ) * (M : ℝ)
  let fixed : ℝ := C * characterLLogBoundConstant ^ 2 * (1 + Real.log N)
  have hdelta : 0 < delta := by
    dsimp [delta]
    positivity
  have hbase : 1 ≤ base := by
    dsimp [base]
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero hN.ne' hM.ne')
  have hfixed : 0 < fixed := by
    have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hlog : 0 < 1 + Real.log N := by
      linarith [Real.log_nonneg hNreal]
    dsimp [fixed]
    exact mul_pos (mul_pos hpair.1 (pow_pos characterLLogBoundConstant_pos 2)) hlog
  have hlogBound : 1 + Real.log (N.lcm M) ≤
      (1 + delta⁻¹) * base ^ delta := by
    simpa [delta, base] using one_add_log_lcm_le_rpow_mul hN hM hdelta
  have hscaled : fixed * (1 + Real.log (N.lcm M)) * (psi.LFunction 1).re ≤
      fixed * ((1 + delta⁻¹) * base ^ delta) * (psi.LFunction 1).re :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hlogBound hfixed.le) hvaluePos.le
  have hweighted :
      (1 - s) * base ^ (-((D : ℝ) * (1 - s))) ≤
        siegelLargeLevelDenominator C N delta * base ^ delta *
          (psi.LFunction 1).re := by
    calc
      (1 - s) * base ^ (-((D : ℝ) * (1 - s))) ≤
          fixed * (1 + Real.log (N.lcm M)) * (psi.LFunction 1).re := by
        simpa [base, fixed, mul_assoc] using hraw
      _ ≤ fixed * ((1 + delta⁻¹) * base ^ delta) *
          (psi.LFunction 1).re := hscaled
      _ = siegelLargeLevelDenominator C N delta * base ^ delta *
          (psi.LFunction 1).re := by
        dsimp [fixed]
        unfold siegelLargeLevelDenominator
        ring
  have hdirect := weighted_rpow_transfer (sub_pos.mpr hsUpper)
    (siegelLargeLevelDenominator_pos hpair.1 hN hdelta) hbase
      (siegel_exponent_control hepsilon D hlowerS) hweighted
  have hbasePower : base ^ (-epsilon) =
      (N : ℝ) ^ (-epsilon) * (M : ℝ) ^ (-epsilon) := by
    dsimp [base]
    exact Real.mul_rpow (by positivity) (by positivity)
  rw [hbasePower] at hdirect
  simpa [siegelLargeLevelConstant, delta, mul_assoc] using hdirect

end BombieriVinogradov.SiegelWalfisz

end

section

namespace BombieriVinogradov.SiegelWalfisz

theorem siegelLowerBound :
    ∀ epsilon > (0 : ℝ), ∃ c > (0 : ℝ),
      ∀ (M : ℕ) [NeZero M] (psi : DirichletCharacter ℂ M), 3 ≤ M ->
        DirichletCharacter.IsPrimitive psi -> psi ^ 2 = 1 -> Ne psi 1 ->
          c * (M : ℝ) ^ (-epsilon) ≤ (psi.LFunction 1).re := by
  intro epsilon hepsilon
  obtain ⟨C, D, hpair⟩ := exists_siegelPositivityPair
  obtain ⟨N, chi, s, hseed⟩ := exists_siegelSeed
    (seven_eighths_le_siegelLowerEndpoint epsilon D)
    (siegelLowerEndpoint_lt_one hepsilon D)
  have hN : 0 < N := hseed.1
  have hsUpper : s < 1 := hseed.2.2.2.2.2.2.1
  let _ : NeZero N := ⟨hN.ne'⟩
  let c := min (finiteLevelConstant epsilon N)
    (siegelLargeLevelConstant C epsilon s N)
  have hcPositive : 0 < c := by
    apply lt_min
    · exact finiteLevelConstant_pos epsilon N
    · exact siegelLargeLevelConstant_pos hpair.1 hepsilon hN hsUpper
  refine ⟨c, hcPositive, ?_⟩
  intro M _ psi hM hpsiPrimitive hpsiSquare hpsi
  have hpowerNonneg : 0 ≤ (M : ℝ) ^ (-epsilon) :=
    Real.rpow_nonneg (Nat.cast_nonneg M) (-epsilon)
  by_cases hMN : M ≤ N
  · have hcoefficient : c ≤ finiteLevelConstant epsilon N := min_le_left _ _
    exact (mul_le_mul_of_nonneg_right hcoefficient hpowerNonneg).trans
      (finiteLevelConstant_le_value hMN hM psi hpsiSquare hpsi)
  · have hNM : N < M := Nat.lt_of_not_ge hMN
    let _ : NeZero (N.lcm M) :=
      ⟨Nat.lcm_ne_zero hN.ne' (NeZero.ne M)⟩
    have hcoefficient : c ≤ siegelLargeLevelConstant C epsilon s N :=
      min_le_right _ _
    exact (mul_le_mul_of_nonneg_right hcoefficient hpowerNonneg).trans
      (siegelLowerBound_largeLevel hpair hepsilon hseed M psi hNM
        hpsiPrimitive hpsiSquare hpsi)

end BombieriVinogradov.SiegelWalfisz

end

open Filter BombieriVinogradov.SiegelWalfisz
namespace OMA.E1140

theorem half_factor {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ^2=1)
    (r : ℕ) (hr : r.Prime) :
    ∃ a : ℝ, 1/2 ≤ a ∧ 1 - χ r * (r:ℂ)^(-(1:ℂ)) = (a:ℂ) := by
  have rr : (2:ℝ) ≤ r := by exact_mod_cast hr.two_le
  have iv : (r:ℝ)⁻¹ ≤ 1/2 := by
    rw [inv_eq_one_div]
    exact one_div_le_one_div_of_le (by norm_num) rr
  have hp : (r:ℂ)^(-(1:ℂ)) = (((r:ℝ)⁻¹):ℂ) := by rw [Complex.cpow_neg_one]; simp
  rw [hp]
  rcases quadraticValue_cases χ hχ r with z|pos|neg
  · exact ⟨1,by norm_num,by simp [z]⟩
  · exact ⟨1 - (r:ℝ)⁻¹,by linarith,by simp [pos]⟩
  · exact ⟨1 + (r:ℝ)⁻¹, by have := inv_nonneg.mpr (Nat.cast_nonneg (α:=ℝ) r); linarith,
      by simp [neg]⟩

theorem siegel_eight_prime :
    ∀ᶠ p : ℕ in atTop, ∀ (_hp:p.Prime) [NeZero (8*p)] (χ : DirichletCharacter ℂ (8*p)),
    χ ≠ 1 → χ^2=1 → ((8*p:ℕ):ℝ)^(-(1/1024:ℝ)) ≤ (χ.LFunction 1).re := by
  obtain ⟨c,hc,sw⟩ := siegelLowerBound (1/2048:ℝ) (by norm_num)
  have htop : Tendsto (fun p : ℕ => ((8*p:ℕ):ℝ)) atTop atTop := by
    simpa only [Nat.cast_mul,Nat.cast_ofNat] using
      tendsto_natCast_atTop_atTop.const_mul_atTop (show (0:ℝ)<8 by norm_num)
  have little := (tendsto_rpow_neg_atTop (show 0<(1/2048:ℝ) by norm_num)).comp htop
  filter_upwards [little.eventually_lt_const (show 0<c/4 by positivity),eventually_ge_atTop 3]
    with p small p3
  intro hp inst χ ne sq
  let Q : ℝ := ((8*p:ℕ):ℝ)
  let u := Q ^ (-(1/2048:ℝ))
  have posQ : 0 < Q := by dsimp [Q]; positivity
  have posu : 0 < u := Real.rpow_pos_of_pos posQ _
  change u < c/4 at small
  let : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hpr := sw χ.conductor χ.primitiveCharacter (three_le_conductor_of_ne_one χ ne)
    χ.primitiveCharacter_isPrimitive (primitiveCharacter_sq_eq_one χ sq) (primitiveCharacter_ne_one χ ne)
  have cond : χ.conductor ≤ 8*p := Nat.le_of_dvd (by positivity) χ.conductor_dvd_level
  have comp : u ≤ (χ.conductor : ℝ)^(-(1/2048:ℝ)) := by
    apply Real.rpow_le_rpow_of_nonpos (by exact_mod_cast Nat.pos_of_ne_zero χ.conductor_ne_zero)
      (by dsimp [Q];exact_mod_cast cond)
    norm_num
  have lower : c*u ≤ (χ.primitiveCharacter.LFunction 1).re :=
    (mul_le_mul_of_nonneg_left comp hc.le).trans hpr
  have pf : (8*p).primeFactors = {2,p} := by
    rw [Nat.primeFactors_mul (by decide) hp.ne_zero, hp.primeFactors,show (8:ℕ).primeFactors={2} by
      rw [show 8 = 2^3 by decide, Nat.primeFactors_pow 2 (by decide : 3≠0), Nat.prime_two.primeFactors]]
    ext n; simp
  obtain ⟨a,ha,hfa⟩ := half_factor χ.primitiveCharacter (primitiveCharacter_sq_eq_one χ sq) 2 Nat.prime_two
  obtain ⟨b,hb,hfb⟩ := half_factor χ.primitiveCharacter (primitiveCharacter_sq_eq_one χ sq) p hp
  have corr : characterLevelCorrection χ 1 = ((a*b:ℝ):ℂ) := by
    rw [characterLevelCorrection,pf,Finset.prod_insert (by simp; omega),Finset.prod_singleton]
    rw [Complex.ofReal_one,hfa,hfb,Complex.ofReal_mul]
  have big : 1/4 ≤ a*b := by nlinarith [mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr hb)]
  have link := LFunction_eq_primitive_mul_correction χ ne (s:=1)
  rw [corr] at link
  have realpart := congrArg Complex.re link
  simp only [Complex.ofReal_one,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero] at realpart
  rw [realpart]
  have ident : Q^(-(1/1024:ℝ)) = u*u := by
    dsimp [u]
    rw [← Real.rpow_add posQ]
    norm_num
  change Q^(-(1/1024:ℝ)) ≤ _
  rw [ident]
  calc
    u * u ≤ (c/4)*u := mul_le_mul_of_nonneg_right small.le posu.le
    _ = (c*u)*(1/4) := by ring
    _ ≤ _ := mul_le_mul lower big (by norm_num) ((mul_pos hc posu).le.trans lower)

end OMA.E1140

/- Linear smoothing for the quadratic Euler convolution at conductor 8p.
The fourth-moment argument uses the project's accepted Burgess development
for Erdős 1141 R1.H1 (#6435). The Pólya–Vinogradov reciprocal tail uses
the accepted Erdős 1141 R1.H2 proof. Both source attribution notices are
preserved with the corresponding declarations. -/

/- Power-saving prefix cancellation for the character of discriminant 8p. -/

/- The squarefree Burgess fourth moment, including the complete Stepanov estimate,
is extracted from the merged open-math-agents contribution #6435,
Erdos1141.erdos_1141.variants.pollack_1_3.R1.H1. Its original authorship notice follows. -/
/-
Burgess-scale divisor-sum estimate for Pollack's Theorem 1.3.
Adapted from the Pollack17 development imported by Boris Alexeev in plby/lean-proofs,
whose enclosing formalization credits GPT-5.4 Pro and Yuta Oriike,
commit 8822f7ddef30fadbd92e1c6ab4ed897af356af5e, and the BoundedGaps
contributors, frenzymath/FormalPantheon (Apache License 2.0), commit ffbb65c21afc8a36ace67720f1b0df1c63d26bd1. The Burgess modules also credit
their amplifier and subpower lemmas to Erdos587.NVDevelopment.
-/

/- ## Elementary collision estimates for Burgess averaging

Source module `ErdosProblems.Erdos1141.BurgessEnergyArithmetic`. -/

noncomputable section

namespace Pollack17.Burgess

open scoped BigOperators

lemma sum_Icc_inv_natCast_le_one_add_log (n : ℕ) :
    (∑ r ∈ Finset.Icc 1 n, ((r : ℝ)⁻¹)) ≤ 1 + Real.log n := by
  simpa only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv,
    Rat.cast_natCast] using harmonic_le_one_add_log n

lemma sum_Icc_natCast_div_le (q n : ℕ) :
    (∑ r ∈ Finset.Icc 1 n, (q : ℝ) / r) ≤
      q * (1 + Real.log n) := by
  simp_rw [div_eq_mul_inv]
  rw [← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left (sum_Icc_inv_natCast_le_one_add_log n)
    (Nat.cast_nonneg q)

lemma card_le_div_add_one_of_pairwise_modEq {s : Finset ℕ} {X h : ℕ}
    (hsX : s ⊆ Finset.Icc 1 X) (_hh : 0 < h)
    (hmod : ∀ a ∈ s, ∀ b ∈ s, a ≡ b [MOD h]) :
    s.card ≤ X / h + 1 := by
  let f : ℕ → ℕ := fun a ↦ a / h
  have hinj : Set.InjOn f s := by
    intro a ha b hb hab
    have hrem : a % h = b % h := hmod a ha b hb
    have hda : h * (a / h) + a % h = a := Nat.div_add_mod a h
    have hdb : h * (b / h) + b % h = b := Nat.div_add_mod b h
    dsimp [f] at hab
    calc
      a = h * (a / h) + a % h := hda.symm
      _ = h * (b / h) + b % h := by rw [hab, hrem]
      _ = b := hdb
  have himage : s.image f ⊆ Finset.range (X / h + 1) := by
    intro y hy
    rw [Finset.mem_image] at hy
    obtain ⟨a, ha, rfl⟩ := hy
    rw [Finset.mem_range]
    have haX : a ≤ X := (Finset.mem_Icc.mp (hsX ha)).2
    exact Nat.lt_succ_of_le (Nat.div_le_div_right haX)
  calc
    s.card = (s.image f).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ (Finset.range (X / h + 1)).card := Finset.card_le_card himage
    _ = X / h + 1 := Finset.card_range _

lemma card_le_div_add_one_of_fst_pairwise_modEq
    {s : Finset (ℕ × ℕ)} {H a : ℕ}
    (hsH : ∀ z ∈ s, z.1 < H) (ha : 0 < a)
    (hinj : Set.InjOn (fun z : ℕ × ℕ ↦ z.1) s)
    (hmod : ∀ z ∈ s, ∀ w ∈ s, z.1 ≡ w.1 [MOD a]) :
    s.card ≤ H / a + 1 := by
  let f : ℕ × ℕ → ℕ := fun z ↦ z.1 + 1
  have hfinj : Set.InjOn f s := by
    intro z hz w hw hzw
    apply hinj hz hw
    change z.1 + 1 = w.1 + 1 at hzw
    exact Nat.add_right_cancel hzw
  have hcard : s.card = (s.image f).card :=
    (Finset.card_image_of_injOn hfinj).symm
  rw [hcard]
  apply card_le_div_add_one_of_pairwise_modEq
  · intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨z, hz, rfl⟩ := hx
    simp only [Finset.mem_Icc]
    exact ⟨Nat.succ_pos _, Nat.succ_le_iff.mpr (hsH z hz)⟩
  · exact ha
  · intro x hx y hy
    rw [Finset.mem_image] at hx hy
    obtain ⟨z, hz, rfl⟩ := hx
    obtain ⟨w, hw, rfl⟩ := hy
    exact (hmod z hz w hw).add_right 1

def burgessIntervalCollision (p M H u₁ u₂ : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range H) ×ˢ (Finset.range H)).filter fun ij ↦
    (M + ij.1) * u₂ ≡ (M + ij.2) * u₁ [MOD p]

def positiveMultiplesUpTo (d U : ℕ) : Finset ℕ :=
  (Finset.Icc 1 U).filter fun u ↦ d ∣ u

lemma positiveMultiplesUpTo_card (d U : ℕ) :
    (positiveMultiplesUpTo d U).card = U / d := by
  have hset : Finset.Icc 1 U = Finset.Ioc 0 U := by
    ext x
    simp
    omega
  rw [positiveMultiplesUpTo, hset]
  exact Nat.Ioc_filter_dvd_card_eq_div U d

lemma sum_positiveMultiplesUpTo_quotient
    {R : Type*} [AddCommMonoid R] (d U : ℕ) (hd : 0 < d)
    (f : ℕ → R) :
    (∑ u ∈ positiveMultiplesUpTo d U, f (u / d)) =
      ∑ a ∈ Finset.Icc 1 (U / d), f a := by
  apply Finset.sum_bij (fun u _ ↦ u / d)
  · intro u hu
    change u ∈ (Finset.Icc 1 U).filter (fun u ↦ d ∣ u) at hu
    rw [Finset.mem_filter] at hu
    rw [Finset.mem_Icc]
    exact ⟨Nat.div_pos (Nat.le_of_dvd (Finset.mem_Icc.mp hu.1).1 hu.2) hd,
      Nat.div_le_div_right (Finset.mem_Icc.mp hu.1).2⟩
  · intro u₁ hu₁ u₂ hu₂ h
    change u₁ ∈ (Finset.Icc 1 U).filter (fun u ↦ d ∣ u) at hu₁
    change u₂ ∈ (Finset.Icc 1 U).filter (fun u ↦ d ∣ u) at hu₂
    have hd₁ := (Finset.mem_filter.mp hu₁).2
    have hd₂ := (Finset.mem_filter.mp hu₂).2
    calc
      u₁ = d * (u₁ / d) := (Nat.mul_div_cancel' hd₁).symm
      _ = d * (u₂ / d) := by rw [h]
      _ = u₂ := Nat.mul_div_cancel' hd₂
  · intro a ha
    refine ⟨d * a, ?_, ?_⟩
    · change d * a ∈ (Finset.Icc 1 U).filter (fun u ↦ d ∣ u)
      rw [Finset.mem_filter]
      constructor
      · rw [Finset.mem_Icc] at ha ⊢
        exact ⟨Nat.mul_pos hd ha.1,
          by simpa [mul_comm] using (Nat.le_div_iff_mul_le hd).mp ha.2⟩
      · exact dvd_mul_right d a
    · rw [Nat.mul_div_cancel_left]
      exact hd
  · intro u hu
    rfl

lemma sum_Icc_natDiv_add_one_cast_le (H n : ℕ) :
    (((∑ a ∈ Finset.Icc 1 n, (H / a + 1)) : ℕ) : ℝ) ≤
      H * (1 + Real.log n) + n := by
  rw [Nat.cast_sum]
  calc
    (∑ a ∈ Finset.Icc 1 n, (((H / a + 1) : ℕ) : ℝ)) ≤
        ∑ a ∈ Finset.Icc 1 n, ((H : ℝ) / a + 1) := by
      apply Finset.sum_le_sum
      intro a ha
      norm_num only [Nat.cast_add, Nat.cast_one]
      exact add_le_add (Nat.cast_div_le (α := ℝ) (m := H) (n := a)) le_rfl
    _ = (∑ a ∈ Finset.Icc 1 n, (H : ℝ) / a) + n := by
      rw [Finset.sum_add_distrib]
      simp
    _ ≤ H * (1 + Real.log n) + n := by
      gcongr
      exact sum_Icc_natCast_div_le H n

lemma reduced_term_le_common_divisor_sum
    {H U u₁ u₂ : ℕ} (hu₁ : u₁ ∈ Finset.Icc 1 U) :
    H / (u₁ / u₁.gcd u₂) + 1 ≤
      ∑ d ∈ Finset.Icc 1 U,
        if d ∣ u₁ ∧ d ∣ u₂ then H / (u₁ / d) + 1 else 0 := by
  let d := u₁.gcd u₂
  have hu₁pos : 0 < u₁ := (Finset.mem_Icc.mp hu₁).1
  have hdpos : 0 < d := Nat.gcd_pos_of_pos_left u₂ hu₁pos
  have hdmem : d ∈ Finset.Icc 1 U := by
    rw [Finset.mem_Icc]
    exact ⟨hdpos, (Nat.gcd_le_left u₂ hu₁pos).trans
      (Finset.mem_Icc.mp hu₁).2⟩
  calc
    H / (u₁ / u₁.gcd u₂) + 1 =
        if d ∣ u₁ ∧ d ∣ u₂ then H / (u₁ / d) + 1 else 0 := by
      simp [d, Nat.gcd_dvd_left, Nat.gcd_dvd_right]
    _ ≤ ∑ d ∈ Finset.Icc 1 U,
        if d ∣ u₁ ∧ d ∣ u₂ then H / (u₁ / d) + 1 else 0 := by
      exact Finset.single_le_sum
        (s := Finset.Icc 1 U)
        (f := fun d ↦ if d ∣ u₁ ∧ d ∣ u₂ then H / (u₁ / d) + 1 else 0)
        (fun _ _ ↦ Nat.zero_le _) hdmem

def burgessDivisorOvercount (H U : ℕ) : ℕ :=
  ∑ u₁ ∈ Finset.Icc 1 U, ∑ u₂ ∈ Finset.Icc 1 U,
    ∑ d ∈ Finset.Icc 1 U,
      if d ∣ u₁ ∧ d ∣ u₂ then H / (u₁ / d) + 1 else 0

lemma burgessDivisorSlice_eq (H U d : ℕ) (hd : 0 < d) :
    (∑ u₁ ∈ Finset.Icc 1 U, ∑ u₂ ∈ Finset.Icc 1 U,
      if d ∣ u₁ ∧ d ∣ u₂ then H / (u₁ / d) + 1 else 0) =
      (U / d) * ∑ a ∈ Finset.Icc 1 (U / d), (H / a + 1) := by
  classical
  simp_rw [ite_and]
  simp_rw [Finset.sum_ite_irrel]
  simp only [Finset.sum_const_zero]
  rw [← Finset.sum_filter]
  change (∑ u₁ ∈ positiveMultiplesUpTo d U,
      ∑ u₂ ∈ Finset.Icc 1 U,
        if d ∣ u₂ then H / (u₁ / d) + 1 else 0) = _
  calc
    (∑ u₁ ∈ positiveMultiplesUpTo d U,
        ∑ u₂ ∈ Finset.Icc 1 U,
          if d ∣ u₂ then H / (u₁ / d) + 1 else 0) =
      ∑ u₁ ∈ positiveMultiplesUpTo d U,
        ∑ _u₂ ∈ positiveMultiplesUpTo d U,
          (H / (u₁ / d) + 1) := by
      apply Finset.sum_congr rfl
      intro u₁ hu₁
      rw [← Finset.sum_filter]
      rfl
    _ = (U / d) * ∑ a ∈ Finset.Icc 1 (U / d), (H / a + 1) := by
      simp_rw [Finset.sum_const]
      rw [positiveMultiplesUpTo_card]
      simp_rw [Nat.nsmul_eq_mul]
      rw [← Finset.mul_sum]
      congr 1
      exact sum_positiveMultiplesUpTo_quotient d U hd
        (fun a ↦ H / a + 1)

lemma burgessDivisorOvercount_eq (H U : ℕ) :
    burgessDivisorOvercount H U =
      ∑ d ∈ Finset.Icc 1 U, (U / d) *
        ∑ a ∈ Finset.Icc 1 (U / d), (H / a + 1) := by
  rw [burgessDivisorOvercount]
  calc
    (∑ u₁ ∈ Finset.Icc 1 U, ∑ u₂ ∈ Finset.Icc 1 U,
        ∑ d ∈ Finset.Icc 1 U,
          if d ∣ u₁ ∧ d ∣ u₂ then H / (u₁ / d) + 1 else 0) =
      ∑ u₁ ∈ Finset.Icc 1 U, ∑ d ∈ Finset.Icc 1 U,
        ∑ u₂ ∈ Finset.Icc 1 U,
          if d ∣ u₁ ∧ d ∣ u₂ then H / (u₁ / d) + 1 else 0 := by
      apply Finset.sum_congr rfl
      intro u₁ hu₁
      rw [Finset.sum_comm]
    _ = ∑ d ∈ Finset.Icc 1 U, ∑ u₁ ∈ Finset.Icc 1 U,
        ∑ u₂ ∈ Finset.Icc 1 U,
          if d ∣ u₁ ∧ d ∣ u₂ then H / (u₁ / d) + 1 else 0 := by
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro d hdmem
      exact burgessDivisorSlice_eq H U d (Finset.mem_Icc.mp hdmem).1

lemma burgessDivisorOvercount_cast_le (H U : ℕ) (hU : 0 < U) :
    (burgessDivisorOvercount H U : ℝ) ≤
      ((H : ℝ) * (1 + Real.log U) + U) *
        ((U : ℝ) * (1 + Real.log U)) := by
  rw [burgessDivisorOvercount_eq, Nat.cast_sum]
  have hlogU : 0 ≤ 1 + Real.log U := by
    have : (1 : ℝ) ≤ U := by exact_mod_cast hU
    linarith [Real.log_nonneg this]
  calc
    (∑ d ∈ Finset.Icc 1 U,
        ((((U / d) * ∑ a ∈ Finset.Icc 1 (U / d), (H / a + 1)) : ℕ) : ℝ)) ≤
      ∑ d ∈ Finset.Icc 1 U,
        ((U : ℝ) / d) * ((H : ℝ) * (1 + Real.log U) + U) := by
      apply Finset.sum_le_sum
      intro d hdmem
      have hdpos : 0 < d := (Finset.mem_Icc.mp hdmem).1
      have hdU : d ≤ U := (Finset.mem_Icc.mp hdmem).2
      have hnpos : 0 < U / d := Nat.div_pos hdU hdpos
      have hnU : U / d ≤ U := Nat.div_le_self U d
      have hlog : Real.log (((U / d : ℕ) : ℝ)) ≤ Real.log U := by
        apply Real.log_le_log
        · exact_mod_cast hnpos
        · exact_mod_cast hnU
      rw [Nat.cast_mul]
      apply mul_le_mul
      · exact Nat.cast_div_le
      · calc
          (((∑ a ∈ Finset.Icc 1 (U / d), (H / a + 1)) : ℕ) : ℝ) ≤
              (H : ℝ) * (1 + Real.log (((U / d : ℕ) : ℝ))) +
                (U / d : ℕ) :=
            sum_Icc_natDiv_add_one_cast_le H (U / d)
          _ ≤ (H : ℝ) * (1 + Real.log U) + U := by
            gcongr
      · positivity
      · positivity
    _ = ((H : ℝ) * (1 + Real.log U) + U) *
        ∑ d ∈ Finset.Icc 1 U, ((U : ℝ) / d) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d hd
      ring
    _ ≤ ((H : ℝ) * (1 + Real.log U) + U) *
        ((U : ℝ) * (1 + Real.log U)) := by
      exact mul_le_mul_of_nonneg_left (sum_Icc_natCast_div_le U U)
        (add_nonneg (mul_nonneg (Nat.cast_nonneg H) hlogU) (Nat.cast_nonneg U))

lemma reduced_denominator_sum_cast_le
    (H U : ℕ) :
    ((∑ u₁ ∈ Finset.Icc 1 U, ∑ u₂ ∈ Finset.Icc 1 U,
      (H / (u₁ / u₁.gcd u₂) + 1) : ℕ) : ℝ) ≤
      (burgessDivisorOvercount H U : ℝ) := by
  exact_mod_cast Finset.sum_le_sum fun u₁ hu₁ ↦
    Finset.sum_le_sum fun u₂ hu₂ ↦
      reduced_term_le_common_divisor_sum hu₁

lemma burgessIntervalCollision_card_le_of_coprime
    {q M H U u₁ u₂ : ℕ}
    (hH : 0 < H) (hU : 0 < U)
    (hu₁ : u₁ ∈ Finset.Icc 1 U) (hu₂ : u₂ ∈ Finset.Icc 1 U)
    (hcop₁ : q.Coprime u₁)
    (hsmall : 2 * (U * H) < q) :
    (burgessIntervalCollision q M H u₁ u₂).card ≤
      H / (u₁ / u₁.gcd u₂) + 1 := by
  let d := u₁.gcd u₂
  let a := u₁ / d
  let b := u₂ / d
  have hu₁pos : 0 < u₁ := (Finset.mem_Icc.mp hu₁).1
  have hu₂pos : 0 < u₂ := (Finset.mem_Icc.mp hu₂).1
  have hu₁U : u₁ ≤ U := (Finset.mem_Icc.mp hu₁).2
  have hu₂U : u₂ ≤ U := (Finset.mem_Icc.mp hu₂).2
  have hdpos : 0 < d := Nat.gcd_pos_of_pos_left u₂ hu₁pos
  have hd₁ : d ∣ u₁ := Nat.gcd_dvd_left u₁ u₂
  have hd₂ : d ∣ u₂ := Nat.gcd_dvd_right u₁ u₂
  have hfac₁ : d * a = u₁ := Nat.mul_div_cancel' hd₁
  have hfac₂ : d * b = u₂ := Nat.mul_div_cancel' hd₂
  have hapos : 0 < a := Nat.div_pos (Nat.le_of_dvd hu₁pos hd₁) hdpos
  have hab : a.Coprime b := Nat.coprime_div_gcd_div_gcd hdpos
  apply card_le_div_add_one_of_fst_pairwise_modEq
  · intro z hz
    exact Finset.mem_range.mp
      (Finset.mem_product.mp (Finset.filter_subset _ _ hz)).1
  · exact hapos
  · intro z hz w hw hzw
    have hz' := (Finset.mem_filter.mp hz).2
    have hw' := (Finset.mem_filter.mp hw).2
    apply Prod.ext hzw
    change z.1 = w.1 at hzw
    rw [hzw] at hz'
    have hjmodM : M + z.2 ≡ M + w.2 [MOD q] := by
      apply Nat.ModEq.cancel_right_of_coprime hcop₁.gcd_eq_one
      exact hz'.symm.trans hw'
    have hjmod : z.2 ≡ w.2 [MOD q] :=
      Nat.ModEq.add_left_cancel' M hjmodM
    have hHq : H < q := by
      have hUHpos : 0 < U * H := Nat.mul_pos hU hH
      have hHle : H ≤ U * H := by
        simpa [mul_comm] using Nat.le_mul_of_pos_right H hU
      omega
    exact hjmod.eq_of_lt_of_lt
      (lt_trans (Finset.mem_range.mp
        (Finset.mem_product.mp (Finset.filter_subset _ _ hz)).2) hHq)
      (lt_trans (Finset.mem_range.mp
        (Finset.mem_product.mp (Finset.filter_subset _ _ hw)).2) hHq)
  · intro z hz w hw
    have hz' := (Finset.mem_filter.mp hz).2
    have hw' := (Finset.mem_filter.mp hw).2
    have hsum := hz'.add hw'.symm
    have hred : u₂ * z.1 + u₁ * w.2 ≡
        u₂ * w.1 + u₁ * z.2 [MOD q] := by
      apply Nat.ModEq.add_left_cancel' (M * (u₁ + u₂))
      simpa [mul_add, add_mul, mul_comm, mul_left_comm, mul_assoc,
        add_comm, add_left_comm, add_assoc] using hsum
    have hzH := Finset.mem_range.mp
      (Finset.mem_product.mp (Finset.filter_subset _ _ hz)).1
    have hzH₂ := Finset.mem_range.mp
      (Finset.mem_product.mp (Finset.filter_subset _ _ hz)).2
    have hwH := Finset.mem_range.mp
      (Finset.mem_product.mp (Finset.filter_subset _ _ hw)).1
    have hwH₂ := Finset.mem_range.mp
      (Finset.mem_product.mp (Finset.filter_subset _ _ hw)).2
    have hterm₁ : u₂ * z.1 < U * H :=
      Nat.mul_lt_mul_of_le_of_lt hu₂U hzH hU
    have hterm₂ : u₁ * w.2 < U * H :=
      Nat.mul_lt_mul_of_le_of_lt hu₁U hwH₂ hU
    have hterm₃ : u₂ * w.1 < U * H :=
      Nat.mul_lt_mul_of_le_of_lt hu₂U hwH hU
    have hterm₄ : u₁ * z.2 < U * H :=
      Nat.mul_lt_mul_of_le_of_lt hu₁U hzH₂ hU
    have heq : u₂ * z.1 + u₁ * w.2 =
        u₂ * w.1 + u₁ * z.2 :=
      hred.eq_of_lt_of_lt (by omega) (by omega)
    have hdeq : d * (b * z.1 + a * w.2) =
        d * (b * w.1 + a * z.2) := by
      calc
        d * (b * z.1 + a * w.2) = u₂ * z.1 + u₁ * w.2 := by
          rw [mul_add, ← mul_assoc, ← mul_assoc, hfac₂, hfac₁]
        _ = u₂ * w.1 + u₁ * z.2 := heq
        _ = d * (b * w.1 + a * z.2) := by
          rw [mul_add, ← mul_assoc, ← mul_assoc, hfac₂, hfac₁]
    have hnorm : b * z.1 + a * w.2 = b * w.1 + a * z.2 :=
      Nat.eq_of_mul_eq_mul_left hdpos hdeq
    have haw : a * w.2 ≡ 0 [MOD a] :=
      (Nat.dvd_mul_right a w.2).modEq_zero_nat
    have haz : a * z.2 ≡ 0 [MOD a] :=
      (Nat.dvd_mul_right a z.2).modEq_zero_nat
    have hfull : b * z.1 + a * w.2 ≡ b * w.1 + a * z.2 [MOD a] := by
      rw [hnorm]
    have hba : b * z.1 ≡ b * w.1 [MOD a] :=
      ((Nat.ModEq.rfl.add haw.symm).trans hfull).trans
        (Nat.ModEq.rfl.add haz)
    exact Nat.ModEq.cancel_left_of_coprime hab.gcd_eq_one hba

end Pollack17.Burgess

end

/- ## Nonvanishing for the quadratic Stepanov construction

Source module `ErdosProblems.Erdos1141.StepanovBox`. -/

noncomputable section

namespace Pollack17.Stepanov

open Polynomial

open scoped BigOperators

variable {K : Type*} [Field K] {p A : ℕ}

def LowResidueSupport (p A : ℕ) (P : K[X]) : Prop :=
  ∀ n : ℕ, P.coeff n ≠ 0 → n % p < A

theorem choose_cast_eq_zero_of_residue_lt [Fact p.Prime] [CharP K p]
    {n k : ℕ} (h : n % p < k % p) :
    (n.choose k : K) = 0 := by
  have hmod := Choose.choose_modEq_choose_mod_mul_choose_div_nat (p := p) (n := n) (k := k)
  rw [Nat.choose_eq_zero_of_lt h, zero_mul] at hmod
  exact (CharP.cast_eq_zero_iff K p _).mpr (Nat.modEq_zero_iff_dvd.mp hmod)

theorem LowResidueSupport.taylor [Fact p.Prime] [CharP K p]
    {P : K[X]} (hP : LowResidueSupport p A P) (x : K) :
    LowResidueSupport p A (taylor x P) := by
  intro k hk
  by_contra hkle
  have hkA : A ≤ k % p := Nat.le_of_not_gt hkle
  apply hk
  rw [taylor_coeff, hasseDeriv_apply, Polynomial.sum_def, eval_finsetSum]
  apply Finset.sum_eq_zero
  intro n hn
  have hnA := hP n (Polynomial.mem_support_iff.mp hn)
  have hchoose : (n.choose k : K) = 0 := choose_cast_eq_zero_of_residue_lt (hnA.trans_le hkA)
  simp [hchoose]

theorem LowResidueSupport.rootMultiplicity_mod_lt [Fact p.Prime] [CharP K p] {P : K[X]}
    (hP : LowResidueSupport p A P) (hP0 : P ≠ 0) (x : K) :
    P.rootMultiplicity x % p < A := by
  have hT : Polynomial.taylor x P ≠ 0 := (Polynomial.taylor_eq_zero x P).not.mpr hP0
  have hcoeff : (Polynomial.taylor x P).coeff (Polynomial.taylor x P).natTrailingDegree ≠ 0 :=
    Polynomial.coeff_natTrailingDegree_ne_zero.mpr hT
  have hres := hP.taylor x _ hcoeff
  rw [Polynomial.rootMultiplicity_eq_natTrailingDegree]
  exact hres

theorem rootMultiplicity_neg_eq (P : K[X]) (x : K) :
    (-P).rootMultiplicity x = P.rootMultiplicity x := by
  simp only [Polynomial.rootMultiplicity_eq_natTrailingDegree, neg_comp,
    Polynomial.natTrailingDegree_neg]

theorem rootMultiplicity_pow_eq {f : K[X]} (hf : f ≠ 0) (x : K) (t : ℕ) :
    (f ^ t).rootMultiplicity x = t * f.rootMultiplicity x := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [pow_succ, Polynomial.rootMultiplicity_mul (mul_ne_zero (pow_ne_zero _ hf) hf), ih]
    ring

theorem add_pow_mul_ne_zero [Fact p.Prime] [CharP K p] {P Q f : K[X]} {x : K} {t : ℕ}
    (hP : LowResidueSupport p A P) (hQ : LowResidueSupport p A Q)
    (hne : P ≠ 0 ∨ Q ≠ 0) (hf : f ≠ 0) (hx : f.rootMultiplicity x = 1)
    (hAt : A ≤ t) (htA : t + A ≤ p) :
    P + f ^ t * Q ≠ 0 := by
  intro hzero
  have hQ0 : Q ≠ 0 := by
    intro hQzero
    have hPzero : P = 0 := by simpa [hQzero] using hzero
    exact hne.elim (fun h => h hPzero) (fun h => h hQzero)
  have hP0 : P ≠ 0 := by
    intro hPzero
    have hprod : f ^ t * Q = 0 := by simpa [hPzero] using hzero
    exact mul_ne_zero (pow_ne_zero _ hf) hQ0 hprod
  have hPmod := hP.rootMultiplicity_mod_lt hP0 x
  have hQmod := hQ.rootMultiplicity_mod_lt hQ0 x
  have hmult : P.rootMultiplicity x = t + Q.rootMultiplicity x := by
    rw [eq_neg_of_add_eq_zero_left hzero, rootMultiplicity_neg_eq,
      Polynomial.rootMultiplicity_mul (mul_ne_zero (pow_ne_zero _ hf) hQ0),
      rootMultiplicity_pow_eq hf x t, hx, mul_one]
  have htlt : t < p := by omega
  have hsumlt : t + Q.rootMultiplicity x % p < p := by omega
  have hmod : P.rootMultiplicity x % p = t + Q.rootMultiplicity x % p := by
    rw [hmult, Nat.add_mod, Nat.mod_eq_of_lt htlt, Nat.mod_eq_of_lt hsumlt]
  omega

def boxExponent (p : ℕ) {A B : ℕ} (i : Fin A × Fin B) : ℕ := i.1 + p * i.2

theorem boxExponent_mod {A B : ℕ} (hA : A ≤ p) (i : Fin A × Fin B) :
    boxExponent p i % p = i.1 := by
  simp [boxExponent, Nat.add_mod, Nat.mod_eq_of_lt (i.1.isLt.trans_le hA)]

theorem boxExponent_injective {A B : ℕ} (hA : A ≤ p) :
    Function.Injective (boxExponent p : Fin A × Fin B → ℕ) := by
  intro i j hij
  have ha : (i.1 : ℕ) = j.1 := by
    simpa only [boxExponent_mod hA] using congrArg (fun n => n % p) hij
  have hp0 : 0 < p := (Nat.zero_le _).trans_lt (i.1.isLt.trans_le hA)
  have hmul : p * (i.2 : ℕ) = p * (j.2 : ℕ) := by
    simpa only [boxExponent, ha, Nat.add_left_cancel_iff] using hij
  exact Prod.ext (Fin.ext ha) (Fin.ext (Nat.eq_of_mul_eq_mul_left hp0 hmul))

noncomputable def boxPolynomial {A B : ℕ} (a : Fin A × Fin B → K) : K[X] :=
  ∑ i : Fin A × Fin B, monomial (boxExponent p i) (a i)

theorem boxPolynomial_coeff {A B : ℕ} (hA : A ≤ p)
    (a : Fin A × Fin B → K) (i : Fin A × Fin B) :
    (boxPolynomial (p := p) a).coeff (boxExponent p i) = a i := by
  classical
  rw [boxPolynomial, finsetSum_coeff, Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    have hne := (boxExponent_injective hA).ne hji
    simp [coeff_monomial, hne]
  · simp

theorem boxPolynomial_injective {A B : ℕ} (hA : A ≤ p) :
    Function.Injective (boxPolynomial (K := K) (p := p) (A := A) (B := B)) := by
  intro a b hab
  funext i
  simpa only [boxPolynomial_coeff hA] using
    congrArg (fun P : K[X] => P.coeff (boxExponent p i)) hab

theorem boxPolynomial_lowResidueSupport {A B : ℕ} (hA : A ≤ p)
    (a : Fin A × Fin B → K) : LowResidueSupport p A (boxPolynomial (p := p) a) := by
  classical
  intro n hn
  by_contra hnot
  apply hn
  rw [boxPolynomial, finsetSum_coeff]
  apply Finset.sum_eq_zero
  intro i _
  have hne : boxExponent p i ≠ n := by
    intro h
    have : n % p = i.1 := h ▸ boxExponent_mod hA i
    exact hnot (this ▸ i.1.isLt)
  simp [coeff_monomial, hne]

theorem boxPolynomial_ne_zero {A B : ℕ} (hA : A ≤ p)
    {a : Fin A × Fin B → K} (ha : a ≠ 0) : boxPolynomial (p := p) a ≠ 0 := by
  intro h
  apply ha
  apply boxPolynomial_injective (K := K) hA
  simpa [boxPolynomial] using h

theorem box_auxiliary_ne_zero [Fact p.Prime] [CharP K p]
    {A B t : ℕ} {a b : Fin A × Fin B → K}
    (hab : a ≠ 0 ∨ b ≠ 0) {f : K[X]} {x : K}
    (hf : f ≠ 0) (hx : f.rootMultiplicity x = 1)
    (hAt : A ≤ t) (htA : t + A ≤ p) :
    boxPolynomial (p := p) a + f ^ t * boxPolynomial (p := p) b ≠ 0 := by
  have hAp : A ≤ p := by omega
  exact add_pow_mul_ne_zero (boxPolynomial_lowResidueSupport hAp a)
    (boxPolynomial_lowResidueSupport hAp b)
    (hab.imp (boxPolynomial_ne_zero hAp) (boxPolynomial_ne_zero hAp))
    hf hx hAt htA

end Pollack17.Stepanov

end

/- ## Reduced derivatives for the quadratic Stepanov polynomial

Source module `ErdosProblems.Erdos1141.StepanovDerivative`. -/

noncomputable section

namespace Pollack17.Stepanov

open Polynomial

variable {K : Type*} [Field K]

noncomputable def reducedDerivative (f : K[X]) (t : K) (g : K[X]) : ℕ → K[X]
  | 0 => g
  | k + 1 => f * (reducedDerivative f t g k).derivative +
      C (t - k) * f.derivative * reducedDerivative f t g k

theorem mul_derivative_pow (f : K[X]) (k : ℕ) :
    f * (f ^ k).derivative = C (k : K) * f ^ k * f.derivative := by
  cases k with
  | zero => simp
  | succ k =>
    rw [derivative_pow_succ, pow_succ]
    push_cast
    ring

theorem mul_derivative_pow_mul (f g : K[X]) (k : ℕ) :
    f * (f ^ k * g).derivative =
      C (k : K) * f ^ k * f.derivative * g + f ^ (k + 1) * g.derivative := by
  rw [derivative_mul, mul_add, ← mul_assoc, mul_derivative_pow]
  rw [pow_succ]
  ring

theorem pow_mul_iterate_derivative (f g : K[X]) (t k : ℕ) :
    f ^ k * derivative^[k] (f ^ t * g) =
      f ^ t * reducedDerivative f (t : K) g k := by
  induction k with
  | zero => simp [reducedDerivative]
  | succ k ih =>
    have hderiv := congrArg (fun P : K[X] => f * P.derivative) ih
    rw [mul_derivative_pow_mul, mul_derivative_pow_mul] at hderiv
    simp only [map_natCast] at hderiv
    rw [Function.iterate_succ_apply', reducedDerivative]
    simp only [map_sub, map_natCast]
    linear_combination hderiv - (k : K[X]) * f.derivative * ih

theorem reducedDerivative_natDegree_le (f g : K[X]) (t : K) (k : ℕ) :
    (reducedDerivative f t g k).natDegree ≤ g.natDegree + k * f.natDegree := by
  induction k with
  | zero => simp [reducedDerivative]
  | succ k ih =>
    rw [reducedDerivative]
    apply (Polynomial.natDegree_add_le _ _).trans
    apply max_le
    · have hderiv := (Polynomial.natDegree_derivative_le
        (reducedDerivative f t g k)).trans (Nat.sub_le _ _)
      have hmul := Polynomial.natDegree_mul_le
        (p := f) (q := (reducedDerivative f t g k).derivative)
      nlinarith
    · have hderiv := (Polynomial.natDegree_derivative_le f).trans (Nat.sub_le _ _)
      have hconst := Polynomial.natDegree_C_mul_le (t - (k : K)) f.derivative
      have hmul := Polynomial.natDegree_mul_le
        (p := C (t - (k : K)) * f.derivative) (q := reducedDerivative f t g k)
      nlinarith

theorem iterate_derivative_mul_of_derivative_zero (g H : K[X])
    (hH : H.derivative = 0) (k : ℕ) :
    derivative^[k] (g * H) = derivative^[k] g * H := by
  induction k with
  | zero => rfl
  | succ k ih => simp [Function.iterate_succ_apply', ih, derivative_mul, hH]

theorem derivative_frobenius_monomial {p : ℕ} [CharP K p] (b : ℕ) :
    (X ^ (p * b) : K[X]).derivative = 0 := by
  rw [derivative_X_pow]
  simp [Nat.cast_mul]

theorem eval_pow_mul_iterate_derivative_frobenius {p : ℕ} [CharP K p]
    (f g : K[X]) (t k b : ℕ) (x : K) (hx : x ^ p = x) :
    f.eval x ^ k * (derivative^[k] ((f ^ t * g) * X ^ (p * b))).eval x =
      f.eval x ^ t * (reducedDerivative f (t : K) g k).eval x * x ^ b := by
  rw [iterate_derivative_mul_of_derivative_zero _ _ (derivative_frobenius_monomial b)]
  simp only [eval_mul, eval_pow, eval_X]
  rw [pow_mul, hx, ← mul_assoc]
  have h := congrArg (fun P : K[X] => P.eval x) (pow_mul_iterate_derivative f g t k)
  simpa only [eval_mul, eval_pow] using congrArg (fun z : K => z * x ^ b) h

end Pollack17.Stepanov

end

/- ## The linear conditions in the quadratic Stepanov argument

Source module `ErdosProblems.Erdos1141.StepanovConditions`. -/

noncomputable section

namespace Pollack17.Stepanov

open Polynomial

open scoped BigOperators

variable {K : Type*} [Field K] {p A B D : ℕ}

abbrev BoxPair (K : Type*) (A B : ℕ) :=
  (Fin A × Fin B → K) × (Fin A × Fin B → K)

noncomputable def conditionHalf (f : K[X]) (t : K) (k : ℕ)
    (a : Fin A × Fin B → K) : K[X] :=
  ∑ i : Fin A × Fin B,
    a i • (reducedDerivative f t (X ^ (i.1 : ℕ)) k * X ^ (i.2 : ℕ))

noncomputable def conditionPolynomial (f : K[X]) (t : K) (k : ℕ)
    (a : BoxPair K A B) : K[X] := conditionHalf f 0 k a.1 + conditionHalf f t k a.2

theorem conditionHalf_natDegree_le (f : K[X]) (t : K) (k : ℕ)
    (a : Fin A × Fin B → K) :
    (conditionHalf f t k a).natDegree ≤ A + B + k * f.natDegree := by
  classical
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i _
  apply (Polynomial.natDegree_smul_le _ _).trans
  have hred := reducedDerivative_natDegree_le f (X ^ (i.1 : ℕ)) t k
  have hmul := Polynomial.natDegree_mul_le
    (p := reducedDerivative f t (X ^ (i.1 : ℕ)) k) (q := X ^ (i.2 : ℕ))
  simp only [natDegree_X_pow] at hred hmul
  have ha := i.1.isLt
  have hb := i.2.isLt
  omega

theorem conditionPolynomial_natDegree_le (f : K[X]) (t : K) (k : ℕ)
    (a : BoxPair K A B) :
    (conditionPolynomial f t k a).natDegree ≤ A + B + k * f.natDegree := by
  exact (Polynomial.natDegree_add_le _ _).trans
    (max_le (conditionHalf_natDegree_le f 0 k a.1) (conditionHalf_natDegree_le f t k a.2))

theorem conditionPolynomial_add (f : K[X]) (t : K) (k : ℕ)
    (a b : BoxPair K A B) :
    conditionPolynomial f t k (a + b) =
      conditionPolynomial f t k a + conditionPolynomial f t k b := by
  simp [conditionPolynomial, conditionHalf, add_smul, Finset.sum_add_distrib,
    add_add_add_comm]

theorem conditionPolynomial_smul (f : K[X]) (t : K) (k : ℕ)
    (c : K) (a : BoxPair K A B) :
    conditionPolynomial f t k (c • a) = c • conditionPolynomial f t k a := by
  simp [conditionPolynomial, conditionHalf, Finset.smul_sum, smul_add, smul_smul]

noncomputable def conditionLinear (f : K[X]) (t : K) (A B D H : ℕ) :
    BoxPair K A B →ₗ[K] (Fin D → Fin H → K) where
  toFun a k j := (conditionPolynomial f t k a).coeff j
  map_add' a b := by
    funext k j
    rw [conditionPolynomial_add, coeff_add]
    rfl
  map_smul' c a := by
    funext k j
    rw [conditionPolynomial_smul, coeff_smul]
    rfl

theorem exists_nonzero_condition_kernel (f : K[X]) (t : K) (A B D H : ℕ)
    (hdim : D * H < 2 * A * B) :
    ∃ a : BoxPair K A B, a ≠ 0 ∧ conditionLinear f t A B D H a = 0 := by
  let T := conditionLinear f t A B D H
  have hker : LinearMap.ker T ≠ ⊥ := by
    intro hbot
    have hle := T.finrank_le_finrank_of_injective (LinearMap.ker_eq_bot.mp hbot)
    have hsource : Module.finrank K (BoxPair K A B) = 2 * A * B := by
      simp [BoxPair, Module.finrank_prod]
      ring
    have htarget : Module.finrank K (Fin D → Fin H → K) = D * H := by
      simp [Module.finrank_pi_fintype]
    rw [hsource, htarget] at hle
    exact (not_le_of_gt hdim) hle
  obtain ⟨a, ha, hane⟩ := (LinearMap.ker T).ne_bot_iff.mp hker
  exact ⟨a, hane, ha⟩

theorem exists_nonzero_vanishing_conditions (f : K[X]) (t : K) (A B D : ℕ)
    (hdim : D * (A + B + D * f.natDegree + 1) < 2 * A * B) :
    ∃ a : BoxPair K A B, a ≠ 0 ∧
      ∀ k : ℕ, k < D → conditionPolynomial f t k a = 0 := by
  let H := A + B + D * f.natDegree + 1
  obtain ⟨a, ha, hkernel⟩ := exists_nonzero_condition_kernel f t A B D H hdim
  refine ⟨a, ha, ?_⟩
  intro k hk
  have hdegree : (conditionPolynomial f t k a).natDegree < H := by
    have hdeg := conditionPolynomial_natDegree_le f t k a
    have hmul := Nat.mul_le_mul_right f.natDegree hk.le
    omega
  ext n
  rw [coeff_zero]
  by_cases hn : n < H
  · exact congrFun (congrFun hkernel ⟨k, hk⟩) ⟨n, hn⟩
  · exact Polynomial.coeff_eq_zero_of_natDegree_lt (hdegree.trans_le (Nat.le_of_not_gt hn))

theorem pow_mul_boxPolynomial_eq_sum (f : K[X]) (t : ℕ)
    (a : Fin A × Fin B → K) :
    f ^ t * boxPolynomial (p := p) a =
      ∑ i : Fin A × Fin B, a i • ((f ^ t * X ^ (i.1 : ℕ)) * X ^ (p * i.2)) := by
  classical
  rw [boxPolynomial, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [← C_mul_X_pow_eq_monomial, boxExponent, pow_add, smul_eq_C_mul]
  ring

theorem eval_conditionHalf {p : ℕ} [CharP K p]
    (f : K[X]) (t k : ℕ) (a : Fin A × Fin B → K) (x : K) (hx : x ^ p = x) :
    f.eval x ^ k * (derivative^[k] (f ^ t * boxPolynomial (p := p) a)).eval x =
      f.eval x ^ t * (conditionHalf f (t : K) k a).eval x := by
  classical
  rw [pow_mul_boxPolynomial_eq_sum, Polynomial.iterate_derivative_sum]
  simp only [Polynomial.iterate_derivative_smul, eval_finsetSum, eval_smul,
    conditionHalf, eval_mul, eval_pow, eval_X]
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have h := eval_pow_mul_iterate_derivative_frobenius f (X ^ (i.1 : ℕ)) t k i.2 x hx
  change f.eval x ^ k * (a i * _) = f.eval x ^ t * (a i * (_ * _))
  linear_combination a i * h

theorem eval_conditionPolynomial {p : ℕ} [CharP K p]
    (f : K[X]) (t k : ℕ) (a : BoxPair K A B) (x : K)
    (hx : x ^ p = x) (hft : f.eval x ^ t = 1) :
    f.eval x ^ k *
        (derivative^[k] (boxPolynomial (p := p) a.1 + f ^ t * boxPolynomial (p := p) a.2)).eval x =
      (conditionPolynomial f (t : K) k a).eval x := by
  have h0 := eval_conditionHalf f 0 k a.1 x hx
  have ht := eval_conditionHalf f t k a.2 x hx
  simp only [pow_zero, one_mul, Nat.cast_zero] at h0
  rw [hft, one_mul] at ht
  have hsum : derivative^[k]
      (boxPolynomial (p := p) a.1 + f ^ t * boxPolynomial (p := p) a.2) =
      derivative^[k] (boxPolynomial (p := p) a.1) +
        derivative^[k] (f ^ t * boxPolynomial (p := p) a.2) :=
    iterate_map_add Polynomial.derivative k _ _
  rw [hsum, eval_add, mul_add, h0, ht, conditionPolynomial, eval_add]

end Pollack17.Stepanov

end

/- ## Root counting for the quadratic Stepanov polynomial

Source module `ErdosProblems.Erdos1141.StepanovRootCount`. -/

noncomputable section

namespace Pollack17.Stepanov

open Polynomial

open scoped BigOperators

variable {K : Type*} [Field K]

theorem le_rootMultiplicity_of_derivatives {p D : ℕ} [Fact p.Prime] [CharP K p]
    {P : K[X]} {x : K} (hP : P ≠ 0) (hDp : D ≤ p)
    (hvanish : ∀ k : ℕ, k < D → (derivative^[k] P).eval x = 0) :
    D ≤ P.rootMultiplicity x := by
  rw [Polynomial.rootMultiplicity_eq_natTrailingDegree]
  apply Polynomial.le_natTrailingDegree
  · exact (Polynomial.taylor_eq_zero x P).not.mpr hP
  · intro k hk
    change (Polynomial.taylor x P).coeff k = 0
    rw [Polynomial.taylor_coeff]
    have hfact : (k.factorial : K) ≠ 0 := by
      rw [ne_eq, CharP.cast_eq_zero_iff K p, (Fact.out : p.Prime).dvd_factorial, not_le]
      exact hk.trans_le hDp
    have hscaled := congrFun (Polynomial.factorial_smul_hasseDeriv (R := K) k) P
    have heval := congrArg (fun Q : K[X] => Q.eval x) hscaled
    simp only [nsmul_eq_mul, Module.End.mul_apply, Module.End.natCast_apply,
      nsmul_eq_mul, eval_mul, eval_natCast] at heval
    rw [hvanish k hk] at heval
    exact (mul_eq_zero.mp heval).resolve_left hfact

theorem mul_card_le_natDegree_of_derivatives {p D : ℕ} [Fact p.Prime] [CharP K p]
    {P : K[X]} (hP : P ≠ 0) (hDp : D ≤ p) (S : Finset K)
    (hvanish : ∀ x ∈ S, ∀ k : ℕ, k < D → (derivative^[k] P).eval x = 0) :
    D * S.card ≤ P.natDegree := by
  classical
  by_cases hD : D = 0
  · simp [hD]
  have hmult (x : K) (hx : x ∈ S) : D ≤ P.rootMultiplicity x :=
    le_rootMultiplicity_of_derivatives hP hDp (hvanish x hx)
  have hsubset : S ⊆ P.roots.toFinset := by
    intro x hx
    rw [Multiset.mem_toFinset, ← Multiset.count_pos, Polynomial.count_roots]
    exact (Nat.pos_of_ne_zero hD).trans_le (hmult x hx)
  calc
    D * S.card = ∑ _x ∈ S, D := by simp [Nat.mul_comm]
    _ ≤ ∑ x ∈ S, P.rootMultiplicity x := Finset.sum_le_sum hmult
    _ = ∑ x ∈ S, P.roots.count x := by simp only [Polynomial.count_roots]
    _ ≤ ∑ x ∈ P.roots.toFinset, P.roots.count x := Finset.sum_le_sum_of_subset hsubset
    _ = P.roots.card := Multiset.toFinset_sum_count_eq P.roots
    _ ≤ P.natDegree := Polynomial.card_roots' P

theorem boxPolynomial_natDegree_le {p A B : ℕ} (a : Fin A × Fin B → K) :
    (boxPolynomial (p := p) a).natDegree ≤ A + p * B := by
  classical
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i _
  apply (Polynomial.natDegree_monomial_le (a i)).trans
  dsimp [boxExponent]
  have hmul := Nat.mul_le_mul_left p i.2.isLt.le
  have ha := i.1.isLt.le
  omega

theorem quadratic_fiber_card_bound {p A B D t : ℕ} [Fact p.Prime] [CharP K p]
    (f : K[X]) {x₀ : K} (hf : f ≠ 0) (hroot : f.rootMultiplicity x₀ = 1)
    (hAt : A ≤ t) (htA : t + A ≤ p) (hDp : D ≤ p)
    (hdim : D * (A + B + D * f.natDegree + 1) < 2 * A * B)
    (S : Finset K)
    (hS : ∀ x ∈ S, x ^ p = x ∧ f.eval x ≠ 0 ∧ f.eval x ^ t = 1) :
    D * S.card ≤ A + p * B + t * f.natDegree := by
  classical
  obtain ⟨a, ha, hcond⟩ := exists_nonzero_vanishing_conditions f (t : K) A B D hdim
  have hpair : a.1 ≠ 0 ∨ a.2 ≠ 0 := by
    by_contra h
    push Not at h
    exact ha (Prod.ext h.1 h.2)
  let F := boxPolynomial (p := p) a.1 + f ^ t * boxPolynomial (p := p) a.2
  have hF : F ≠ 0 := box_auxiliary_ne_zero hpair hf hroot hAt htA
  have hdeg : F.natDegree ≤ A + p * B + t * f.natDegree := by
    apply (Polynomial.natDegree_add_le _ _).trans
    apply max_le
    · exact (boxPolynomial_natDegree_le a.1).trans (Nat.le_add_right _ _)
    · have hmul := Polynomial.natDegree_mul_le
        (p := f ^ t) (q := boxPolynomial (p := p) a.2)
      rw [Polynomial.natDegree_pow] at hmul
      have hb := boxPolynomial_natDegree_le (p := p) a.2
      omega
  apply (mul_card_le_natDegree_of_derivatives hF hDp S ?_).trans hdeg
  intro x hx k hk
  obtain ⟨hxp, hfx, hft⟩ := hS x hx
  have heval := eval_conditionPolynomial f t k a x hxp hft
  rw [hcond k hk, eval_zero] at heval
  exact (mul_eq_zero.mp heval).resolve_left (pow_ne_zero _ hfx)

end Pollack17.Stepanov

end

/- ## Parameters for the quadratic Stepanov construction

Source module `ErdosProblems.Erdos1141.StepanovParameters`. -/

noncomputable section

namespace Pollack17.Stepanov

open Polynomial

theorem constraints_lt_coefficients {A B D d : ℕ}
    (hB : 1 ≤ B) (hD : D + 1 = 2 * B) (hA : 4 * (d + 1) * B ^ 2 < A) :
    D * (A + B + D * d + 1) < 2 * A * B := by
  have hDle : D ≤ 2 * B := by omega
  have hDd : D * d ≤ 2 * B * d := Nat.mul_le_mul_right d hDle
  have hinner : B + D * d + 1 ≤ 2 * B * (d + 1) := by nlinarith
  have hcost : D * (B + D * d + 1) ≤ 4 * (d + 1) * B ^ 2 := by
    calc
      D * (B + D * d + 1) ≤ (2 * B) * (2 * B * (d + 1)) :=
        Nat.mul_le_mul hDle hinner
      _ = _ := by ring
  have hDA : D * A + A = 2 * A * B := by
    calc
      D * A + A = (D + 1) * A := by ring
      _ = 2 * A * B := by rw [hD]; ring
  calc
    D * (A + B + D * d + 1) = D * A + D * (B + D * d + 1) := by ring
    _ < D * A + A := Nat.add_lt_add_left (hcost.trans_lt hA) _
    _ = 2 * A * B := hDA

theorem half_characteristic_parameters {p B d : ℕ} (hp : 0 < p) (hB : 1 ≤ B)
    (hsmall : 16 * (d + 1) * B ^ 2 ≤ p) :
    let A := (p - 1) / 2
    let D := 2 * B - 1
    A + A ≤ p ∧ D ≤ p ∧ D * (A + B + D * d + 1) < 2 * A * B := by
  dsimp only
  let A := (p - 1) / 2
  let D := 2 * B - 1
  have hdiv := Nat.div_mul_le_self (p - 1) 2
  have hmod := Nat.mod_add_div (p - 1) 2
  have hmodlt := Nat.mod_lt (p - 1) (by norm_num : 0 < 2)
  have hAlower : p ≤ 2 * A + 2 := by dsimp [A]; omega
  have hAupper : A + A ≤ p := by dsimp [A]; omega
  have hD : D + 1 = 2 * B := by dsimp [D]; omega
  have hBsq : B ≤ B ^ 2 := by nlinarith
  have hterm : 1 ≤ (d + 1) * B ^ 2 := by
    change 0 < (d + 1) * B ^ 2
    positivity
  have hprod : B ^ 2 ≤ (d + 1) * B ^ 2 := by
    exact Nat.le_mul_of_pos_left _ (by omega)
  have hlarge : 4 * (d + 1) * B ^ 2 < A := by nlinarith
  have hDp : D ≤ p := by nlinarith
  exact ⟨hAupper, hDp, constraints_lt_coefficients hB hD hlarge⟩

theorem quadratic_fiber_card_bound_small_square
    {K : Type*} [Field K] {p B : ℕ} [Fact p.Prime] [CharP K p]
    (f : K[X]) {x₀ : K} (hf : f ≠ 0) (hroot : f.rootMultiplicity x₀ = 1)
    (hB : 1 ≤ B) (hsmall : 16 * (f.natDegree + 1) * B ^ 2 ≤ p)
    (S : Finset K)
    (hS : ∀ x ∈ S, x ^ p = x ∧ f.eval x ≠ 0 ∧ f.eval x ^ ((p - 1) / 2) = 1) :
    2 * (2 * B - 1) * S.card ≤ p * (2 * B - 1) + p * (f.natDegree + 2) := by
  obtain ⟨hA, hDp, hdim⟩ := half_characteristic_parameters
    (Fact.out : p.Prime).pos hB hsmall
  have hcount := quadratic_fiber_card_bound f hf hroot le_rfl hA hDp hdim S hS
  have hD : (2 * B - 1) + 1 = 2 * B := by omega
  have hAd := Nat.mul_le_mul_right f.natDegree hA
  nlinarith

end Pollack17.Stepanov

end

/- ## Quadratic character sums of polynomials with a simple root

Source module `ErdosProblems.Erdos1141.StepanovCharacterSum`. -/

noncomputable section

namespace Pollack17.Stepanov

open Polynomial

open scoped BigOperators

variable {p : ℕ} [Fact p.Prime]

noncomputable def residueFiber (f : (ZMod p)[X]) : Finset (ZMod p) :=
  Finset.univ.filter fun x => quadraticChar (ZMod p) (f.eval x) = 1

noncomputable def zeroFiber (f : (ZMod p)[X]) : Finset (ZMod p) :=
  Finset.univ.filter fun x => f.eval x = 0

noncomputable def polynomialCharacterSum (f : (ZMod p)[X]) : ℝ :=
  ∑ x : ZMod p, (quadraticChar (ZMod p) (f.eval x) : ℝ)

theorem polynomialCharacterSum_eq_fibers (f : (ZMod p)[X]) :
    polynomialCharacterSum f = 2 * (residueFiber f).card + (zeroFiber f).card - p := by
  classical
  have hpoint (x : ZMod p) : (quadraticChar (ZMod p) (f.eval x) : ℝ) =
      2 * (if quadraticChar (ZMod p) (f.eval x) = 1 then (1 : ℝ) else 0) +
        (if f.eval x = 0 then 1 else 0) - 1 := by
    by_cases hx : f.eval x = 0
    · simp [hx]
    · rcases quadraticChar_dichotomy hx with h | h <;> norm_num [h, hx]
  have hres : (∑ x : ZMod p,
      if quadraticChar (ZMod p) (f.eval x) = 1 then (1 : ℝ) else 0) = (residueFiber f).card := by
    simp [residueFiber]
  have hzero : (∑ x : ZMod p, if f.eval x = 0 then (1 : ℝ) else 0) = (zeroFiber f).card := by
    simp [zeroFiber]
  simp only [polynomialCharacterSum, hpoint, Finset.sum_sub_distrib,
    Finset.sum_add_distrib, ← Finset.mul_sum, hres, hzero]
  simp

theorem zeroFiber_card_le {f : (ZMod p)[X]} (hf : f ≠ 0) :
    (zeroFiber f).card ≤ f.natDegree := by
  classical
  have hsubset : zeroFiber f ⊆ f.roots.toFinset := by
    intro x hx
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hf]
    exact (Finset.mem_filter.mp hx).2
  exact ((Finset.card_le_card hsubset).trans (Multiset.toFinset_card_le _)).trans
    (Polynomial.card_roots' f)

theorem residueFiber_spec (f : (ZMod p)[X]) (hp2 : p ≠ 2)
    {x : ZMod p} (hx : x ∈ residueFiber f) :
    x ^ p = x ∧ f.eval x ≠ 0 ∧ f.eval x ^ ((p - 1) / 2) = 1 := by
  have hchar := (Finset.mem_filter.mp hx).2
  have hfx : f.eval x ≠ 0 := by
    intro hzero
    simp [hzero] at hchar
  have hF : ringChar (ZMod p) ≠ 2 := by rwa [ZMod.ringChar_zmod_n]
  have hpow := quadraticChar_eq_pow_of_char_ne_two' hF (f.eval x)
  have hodd := (Fact.out : p.Prime).odd_of_ne_two hp2
  have hhalf : p / 2 = (p - 1) / 2 := by
    have := Nat.odd_iff.mp hodd
    omega
  refine ⟨?_, hfx, ?_⟩
  · simp
  · simpa only [hchar, Int.cast_one, ZMod.card, hhalf] using hpow.symm

theorem polynomialCharacterSum_le_of_small_square {B : ℕ}
    (f : (ZMod p)[X]) {x₀ : ZMod p} (hf : f ≠ 0) (hroot : f.rootMultiplicity x₀ = 1)
    (hp2 : p ≠ 2) (hB : 1 ≤ B) (hsmall : 16 * (f.natDegree + 1) * B ^ 2 ≤ p) :
    polynomialCharacterSum f ≤
      (p : ℝ) * (f.natDegree + 2) / (2 * B - 1 : ℕ) + f.natDegree := by
  have hcount := quadratic_fiber_card_bound_small_square f hf hroot hB hsmall
    (residueFiber f) (fun _ hx => residueFiber_spec f hp2 hx)
  have hcountR : (2 : ℝ) * (2 * B - 1 : ℕ) * (residueFiber f).card ≤
      (p : ℝ) * (2 * B - 1 : ℕ) + (p : ℝ) * (f.natDegree + 2) := by
    exact_mod_cast hcount
  have hzeros : ((zeroFiber f).card : ℝ) ≤ f.natDegree := by exact_mod_cast zeroFiber_card_le hf
  have hDpos : (0 : ℝ) < (2 * B - 1 : ℕ) := by exact_mod_cast (show 0 < 2 * B - 1 by omega)
  have hquot : (2 : ℝ) * (residueFiber f).card - p ≤
      (p : ℝ) * (f.natDegree + 2) / (2 * B - 1 : ℕ) := by
    apply (le_div_iff₀ hDpos).mpr
    nlinarith
  rw [polynomialCharacterSum_eq_fibers]
  linarith

theorem abs_polynomialCharacterSum_le_of_small_square {B : ℕ}
    (f : (ZMod p)[X]) {x₀ : ZMod p} (hf : f ≠ 0) (hroot : f.rootMultiplicity x₀ = 1)
    (hp2 : p ≠ 2) (hB : 1 ≤ B) (hsmall : 16 * (f.natDegree + 1) * B ^ 2 ≤ p) :
    |polynomialCharacterSum f| ≤
      (p : ℝ) * (f.natDegree + 2) / (2 * B - 1 : ℕ) + f.natDegree := by
  have hu := polynomialCharacterSum_le_of_small_square f hf hroot hp2 hB hsmall
  have hF : ringChar (ZMod p) ≠ 2 := by rwa [ZMod.ringChar_zmod_n]
  obtain ⟨a, ha⟩ := quadraticChar_exists_neg_one hF
  have ha0 : a ≠ 0 := by
    intro hzero
    simp [hzero] at ha
  let g := C a * f
  have hg : g ≠ 0 := mul_ne_zero (Polynomial.C_ne_zero.mpr ha0) hf
  have hgroot : g.rootMultiplicity x₀ = 1 := by
    rw [Polynomial.rootMultiplicity_mul hg, Polynomial.rootMultiplicity_C, hroot, zero_add]
  have hgdegree : g.natDegree = f.natDegree := by
    rw [Polynomial.natDegree_mul (Polynomial.C_ne_zero.mpr ha0) hf, natDegree_C, zero_add]
  have hl := polynomialCharacterSum_le_of_small_square g hg hgroot hp2 hB
    (by simpa only [hgdegree] using hsmall)
  have hsum : polynomialCharacterSum g = -polynomialCharacterSum f := by
    simp [polynomialCharacterSum, g, map_mul, ha, Finset.sum_neg_distrib]
  rw [hgdegree, hsum] at hl
  exact abs_le.mpr ⟨by linarith, hu⟩

theorem abs_polynomialCharacterSum_le_card (f : (ZMod p)[X]) :
    |polynomialCharacterSum f| ≤ p := by
  have hpoint (x : ZMod p) : |(quadraticChar (ZMod p) (f.eval x) : ℝ)| ≤ 1 := by
    rcases quadraticChar_isQuadratic (ZMod p) (f.eval x) with h | h | h <;> norm_num [h]
  exact (Finset.abs_sum_le_sum_abs _ _).trans
    ((Finset.sum_le_sum (fun x _ => hpoint x)).trans_eq (by simp))

end Pollack17.Stepanov

end

/- ## A square-root bound with a degree-dependent constant

Source module `ErdosProblems.Erdos1141.StepanovSqrt`. -/

noncomputable section

namespace Pollack17.Stepanov

open Polynomial

def simpleRootConstant (d : ℕ) : ℕ :=
  32 * (d + 1) + 64 * (d + 1) * (d + 2) + d

theorem sqrt_div_square_small (p c : ℕ) (hc : 0 < c) :
    c * (Nat.sqrt p / c) ^ 2 ≤ p := by
  have hdiv : c * (Nat.sqrt p / c) ≤ Nat.sqrt p := by
    simpa only [mul_comm] using Nat.div_mul_le_self (Nat.sqrt p) c
  have hc2 : c ≤ c ^ 2 := by nlinarith
  calc
    c * (Nat.sqrt p / c) ^ 2 ≤ c ^ 2 * (Nat.sqrt p / c) ^ 2 :=
      Nat.mul_le_mul_right _ hc2
    _ = (c * (Nat.sqrt p / c)) ^ 2 := by ring
    _ ≤ (Nat.sqrt p) ^ 2 := Nat.pow_le_pow_left hdiv 2
    _ ≤ p := Nat.sqrt_le' p

theorem modulus_le_sqrt_mul_div {p c : ℕ} (hp : 0 < p) (hc : 0 < c)
    (hB : 1 ≤ Nat.sqrt p / c) :
    (p : ℝ) ≤ 4 * c * ((Nat.sqrt p / c : ℕ) : ℝ) * Real.sqrt p := by
  let B := Nat.sqrt p / c
  have hmod := Nat.mod_add_div (Nat.sqrt p) c
  have hmodlt := Nat.mod_lt (Nat.sqrt p) hc
  have hfloor : Nat.sqrt p + 1 ≤ c * (B + 1) := by dsimp [B]; nlinarith
  have hnext : Nat.sqrt p + 1 ≤ 2 * c * B := by
    calc
      Nat.sqrt p + 1 ≤ c * (B + 1) := hfloor
      _ ≤ c * (2 * B) := Nat.mul_le_mul_left c (by omega)
      _ = _ := by ring
  have hpn : p ≤ 2 * c * B * (Nat.sqrt p + 1) := by
    calc
      p ≤ (Nat.sqrt p + 1) ^ 2 := (Nat.lt_succ_sqrt' p).le
      _ ≤ (2 * c * B) * (Nat.sqrt p + 1) := by
        simpa only [pow_two] using Nat.mul_le_mul_right (Nat.sqrt p + 1) hnext
  have hpr : (p : ℝ) ≤ 2 * c * B * ((Nat.sqrt p : ℝ) + 1) := by exact_mod_cast hpn
  have hs0 : 0 ≤ Real.sqrt (p : ℝ) := Real.sqrt_nonneg _
  have hs2 : Real.sqrt (p : ℝ) ^ 2 = p := Real.sq_sqrt (Nat.cast_nonneg _)
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hs1 : 1 ≤ Real.sqrt (p : ℝ) := by nlinarith
  have hl2 : (Nat.sqrt p : ℝ) ^ 2 ≤ p := by exact_mod_cast Nat.sqrt_le' p
  have hl : (Nat.sqrt p : ℝ) ≤ Real.sqrt p := by
    nlinarith [Nat.cast_nonneg (α := ℝ) (Nat.sqrt p)]
  calc
    (p : ℝ) ≤ 2 * c * B * ((Nat.sqrt p : ℝ) + 1) := hpr
    _ ≤ 2 * c * B * (2 * Real.sqrt p) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ = _ := by ring

theorem abs_polynomialCharacterSum_le_sqrt
    {p : ℕ} [Fact p.Prime] (f : (ZMod p)[X]) {x₀ : ZMod p}
    (hf : f ≠ 0) (hroot : f.rootMultiplicity x₀ = 1) :
    |polynomialCharacterSum f| ≤ (simpleRootConstant f.natDegree : ℝ) * Real.sqrt p := by
  let d := f.natDegree
  let c := 16 * (d + 1)
  let B := Nat.sqrt p / c
  have hc : 0 < c := by dsimp [c]; positivity
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hs0 : 0 ≤ Real.sqrt (p : ℝ) := Real.sqrt_nonneg _
  have hs2 : Real.sqrt (p : ℝ) ^ 2 = p := Real.sq_sqrt (Nat.cast_nonneg _)
  have hs1 : 1 ≤ Real.sqrt (p : ℝ) := by nlinarith
  have hC : (simpleRootConstant d : ℝ) =
      2 * c + 4 * c * (d + 2) + d := by
    simp only [simpleRootConstant, c, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
    ring
  by_cases hlarge : 2 * c ≤ Nat.sqrt p
  · have hB2 : 2 ≤ B := (Nat.le_div_iff_mul_le hc).mpr (by simpa only [mul_comm] using hlarge)
    have hB : 1 ≤ B := by omega
    have hp2 : p ≠ 2 := by
      have hsp := Nat.sqrt_le_self p
      have hc16 : 16 ≤ c := by dsimp [c]; omega
      omega
    have hsmall : 16 * (f.natDegree + 1) * B ^ 2 ≤ p := sqrt_div_square_small p c hc
    have hraw := abs_polynomialCharacterSum_le_of_small_square f hf hroot hp2 hB hsmall
    have hpb : (p : ℝ) ≤ 4 * c * B * Real.sqrt p := modulus_le_sqrt_mul_div hp hc hB
    have hDB : (B : ℝ) ≤ (2 * B - 1 : ℕ) := by exact_mod_cast (show B ≤ 2 * B - 1 by omega)
    have hD0 : (0 : ℝ) < (2 * B - 1 : ℕ) := by exact_mod_cast (show 0 < 2 * B - 1 by omega)
    have hpD : (p : ℝ) ≤ 4 * c * (2 * B - 1 : ℕ) * Real.sqrt p := by
      apply hpb.trans
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hDB (by positivity)) hs0
    have hquot : (p : ℝ) * (d + 2) / (2 * B - 1 : ℕ) ≤
        4 * c * (d + 2) * Real.sqrt p := by
      apply (div_le_iff₀ hD0).mpr
      have h := mul_le_mul_of_nonneg_right hpD (show (0 : ℝ) ≤ d + 2 by positivity)
      nlinarith
    have hd : (d : ℝ) ≤ d * Real.sqrt p := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hs1 (Nat.cast_nonneg d)
    calc
      |polynomialCharacterSum f| ≤ (p : ℝ) * (d + 2) / (2 * B - 1 : ℕ) + d := hraw
      _ ≤ 4 * c * (d + 2) * Real.sqrt p + d * Real.sqrt p := add_le_add hquot hd
      _ ≤ (simpleRootConstant d : ℝ) * Real.sqrt p := by
        rw [hC]
        have : 0 ≤ 2 * (c : ℝ) * Real.sqrt p := by positivity
        nlinarith
  · have hnext : Nat.sqrt p + 1 ≤ 2 * c := by omega
    have hpbound : p ≤ (2 * c) ^ 2 :=
      (Nat.lt_succ_sqrt' p).le.trans (Nat.pow_le_pow_left hnext 2)
    have hpboundR : (p : ℝ) ≤ (2 * c) ^ 2 := by exact_mod_cast hpbound
    have hsr : Real.sqrt (p : ℝ) ≤ 2 * c := by
      nlinarith [Nat.cast_nonneg (α := ℝ) c]
    have hpc : (p : ℝ) ≤ 2 * c * Real.sqrt p := by nlinarith
    calc
      |polynomialCharacterSum f| ≤ p := abs_polynomialCharacterSum_le_card f
      _ ≤ 2 * c * Real.sqrt p := hpc
      _ ≤ (simpleRootConstant d : ℝ) * Real.sqrt p := by
        rw [hC]
        apply mul_le_mul_of_nonneg_right _ hs0
        have : 0 ≤ 4 * (c : ℝ) * (d + 2) + d := by positivity
        linarith

end Pollack17.Stepanov

end

/- ## Arbitrary moments of shifted quadratic character sums

Source module `ErdosProblems.Erdos1141.BurgessMoments`. -/

noncomputable section

namespace Pollack17.Burgess

open Polynomial

open scoped BigOperators

variable {p : ℕ} [Fact p.Prime]

noncomputable def qchar (x : ZMod p) : ℝ := (quadraticChar (ZMod p) x : ℝ)

noncomputable def shiftPolynomial {n : ℕ} (v : Fin n → ZMod p) : (ZMod p)[X] :=
  ∏ i : Fin n, (X + C (v i))

theorem shiftPolynomial_ne_zero {n : ℕ} (v : Fin n → ZMod p) : shiftPolynomial v ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  exact Polynomial.X_add_C_ne_zero (v i)

theorem shiftPolynomial_natDegree {n : ℕ} (v : Fin n → ZMod p) :
    (shiftPolynomial v).natDegree = n := by
  rw [shiftPolynomial, Polynomial.natDegree_prod]
  · simp
  · intro i _
    exact Polynomial.X_add_C_ne_zero (v i)

theorem shiftPolynomial_simple_root {n : ℕ} (v : Fin n → ZMod p) (i : Fin n)
    (hsingle : ∀ j : Fin n, j ≠ i → v j ≠ v i) :
    (shiftPolynomial v).rootMultiplicity (-v i) = 1 := by
  classical
  let Q : (ZMod p)[X] := ∏ j ∈ Finset.univ.erase i, (X + C (v j))
  have hfactor : shiftPolynomial v = (X + C (v i)) * Q := by
    exact (Finset.mul_prod_erase _ _ (Finset.mem_univ i)).symm
  have hQeval : Q.eval (-v i) ≠ 0 := by
    simp only [Q, eval_prod, eval_add, eval_X, eval_C]
    apply Finset.prod_ne_zero_iff.mpr
    intro j hj
    have hne := hsingle j (Finset.mem_erase.mp hj).1
    simpa only [sub_eq_add_neg, add_comm] using sub_ne_zero.mpr hne
  have hQroot : Q.rootMultiplicity (-v i) = 0 := Polynomial.rootMultiplicity_eq_zero hQeval
  have hmul : (X + C (v i)) * Q ≠ 0 := hfactor ▸ shiftPolynomial_ne_zero v
  rw [hfactor, Polynomial.rootMultiplicity_mul hmul, hQroot, add_zero]
  simpa only [map_neg, sub_neg_eq_add] using
    (Polynomial.rootMultiplicity_X_sub_C_self (x := -v i))

theorem correlation_le_of_singleton {n : ℕ} (v : Fin n → ZMod p)
    (hsingle : ∃ i : Fin n, ∀ j : Fin n, j ≠ i → v j ≠ v i) :
    |∑ x : ZMod p, qchar (∏ i : Fin n, (x + v i))| ≤
      (Stepanov.simpleRootConstant n : ℝ) * Real.sqrt p := by
  obtain ⟨i, hi⟩ := hsingle
  have h := Stepanov.abs_polynomialCharacterSum_le_sqrt (shiftPolynomial v)
    (shiftPolynomial_ne_zero v) (shiftPolynomial_simple_root v i hi)
  rw [shiftPolynomial_natDegree] at h
  simpa only [Stepanov.polynomialCharacterSum, shiftPolynomial, eval_prod,
    eval_add, eval_X, eval_C, qchar] using h

end Pollack17.Burgess

end

/- ## Counting tuples with no singleton entry

Source module `ErdosProblems.Erdos1141.RepeatedTuples`. -/

noncomputable section

namespace Pollack17.Burgess

open scoped BigOperators

def RepeatedTuple {α : Type*} {n : ℕ} (v : Fin n → α) : Prop :=
  ∀ i : Fin n, ∃ j : Fin n, j ≠ i ∧ v j = v i

theorem repeatedTuple_image_card {α : Type*} [DecidableEq α] {n : ℕ}
    (v : Fin n → α) (hv : RepeatedTuple v) :
    2 * (Finset.univ.image v).card ≤ n := by
  have hfiber (a : α) (ha : a ∈ Finset.univ.image v) :
      2 ≤ (Finset.univ.filter fun i => v i = a).card := by
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨j, hji, hval⟩ := hv i
    apply Finset.one_lt_card.mpr
    exact ⟨i, by simp, j, by simp [hval], hji.symm⟩
  calc
    2 * (Finset.univ.image v).card = ∑ _a ∈ Finset.univ.image v, 2 := by simp [Nat.mul_comm]
    _ ≤ ∑ a ∈ Finset.univ.image v, (Finset.univ.filter fun i => v i = a).card :=
      Finset.sum_le_sum hfiber
    _ = n := by simpa using (Finset.card_eq_sum_card_image v Finset.univ).symm

theorem exists_tuple_factorization {α : Type*} [DecidableEq α] {n r : ℕ}
    (hn : 0 < n) (v : Fin n → α) (hcard : (Finset.univ.image v).card ≤ r) :
    ∃ a : Fin r → α, ∃ b : Fin n → Fin r, v = a ∘ b := by
  classical
  let S := Finset.univ.image v
  let e : S ≃ Fin S.card := Fintype.equivFinOfCardEq (by simp)
  let z : Fin n → S := fun i => ⟨v i, Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩
  let b : Fin n → Fin r := fun i => ⟨(e (z i)).val, (e (z i)).isLt.trans_le hcard⟩
  let a : Fin r → α := fun j =>
    if h : j.val < S.card then (e.symm ⟨j.val, h⟩).val else v ⟨0, hn⟩
  refine ⟨a, b, ?_⟩
  funext i
  dsimp only [Function.comp_apply, a, b]
  rw [dif_pos (e (z i)).isLt]
  exact (congrArg Subtype.val (e.symm_apply_apply (z i))).symm

noncomputable def repeatedTuples (α : Type*) [Fintype α] (n : ℕ) : Finset (Fin n → α) := by
  classical
  exact Finset.univ.filter RepeatedTuple

theorem repeatedTuples_card_le (α : Type*) [Fintype α] (r : ℕ) :
    (repeatedTuples α (2 * r)).card ≤ (Fintype.card α) ^ r * r ^ (2 * r) := by
  classical
  by_cases hr : r = 0
  · subst r
    simpa [repeatedTuples] using
      (Finset.card_filter_le (Finset.univ : Finset (Fin 0 → α)) RepeatedTuple)
  let T : Finset ((Fin r → α) × (Fin (2 * r) → Fin r)) := Finset.univ
  let compose : ((Fin r → α) × (Fin (2 * r) → Fin r)) → (Fin (2 * r) → α) :=
    fun ab => ab.1 ∘ ab.2
  have hsubset : repeatedTuples α (2 * r) ⊆ T.image compose := by
    intro v hv
    have hrep : RepeatedTuple v := (Finset.mem_filter.mp hv).2
    have htwice := repeatedTuple_image_card v hrep
    have hcard : (Finset.univ.image v).card ≤ r := by omega
    obtain ⟨a, b, hab⟩ := exists_tuple_factorization (by omega : 0 < 2 * r) v hcard
    exact Finset.mem_image.mpr ⟨(a, b), Finset.mem_univ _, hab.symm⟩
  calc
    (repeatedTuples α (2 * r)).card ≤ (T.image compose).card := Finset.card_le_card hsubset
    _ ≤ T.card := Finset.card_image_le
    _ = (Fintype.card α) ^ r * r ^ (2 * r) := by simp [T]

end Pollack17.Burgess

end

/- ## Products of local quadratic characters

Source module `ErdosProblems.Erdos1141.QuadraticCRT`. -/

noncomputable section

namespace Pollack17.Burgess

open scoped BigOperators

def primeModulus (s : Finset ℕ) : ℕ := ∏ p ∈ s, p

theorem primeModulus_pos (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) :
    0 < primeModulus s := Finset.prod_pos (fun p hp => (hs p hp).pos)

theorem primeSet_pairwise (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) :
    Pairwise (fun p r : s => Nat.Coprime (p : ℕ) (r : ℕ)) := by
  intro p r hpr
  exact (hs p p.property).coprime_iff_not_dvd.mpr fun hdvd =>
    hpr (Subtype.ext ((Nat.prime_dvd_prime_iff_eq (hs p p.property)
      (hs r r.property)).mp hdvd))

noncomputable def primeCRT (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) :
    ZMod (primeModulus s) ≃+* (∀ p : s, ZMod (p : ℕ)) := by
  have hprod : primeModulus s = ∏ p : s, (p : ℕ) :=
    (Finset.prod_attach s (fun p : ℕ => p)).symm
  exact (ZMod.ringEquivCongr hprod).trans
    (ZMod.prodEquivPi (fun p : s => (p : ℕ)) (primeSet_pairwise s hs))

theorem primeCRT_natCast (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) (n : ℕ) (p : s) :
    primeCRT s hs (n : ZMod (primeModulus s)) p = (n : ZMod (p : ℕ)) := by
  simp [primeCRT]

noncomputable def localChar (p : ℕ) (hp : p.Prime) (x : ZMod p) : ℝ :=
  @qchar p ⟨hp⟩ x

noncomputable def productChar (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime)
    (x : ZMod (primeModulus s)) : ℝ :=
  ∏ p : s, localChar p (hs p p.property) (primeCRT s hs x p)

theorem productChar_mul (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime)
    (a b : ZMod (primeModulus s)) :
    productChar s hs (a * b) = productChar s hs a * productChar s hs b := by
  simp [productChar, localChar, qchar, map_mul, Finset.prod_mul_distrib]

theorem abs_localChar_le_one (p : ℕ) (hp : p.Prime) (x : ZMod p) :
    |localChar p hp x| ≤ 1 := by
  have : Fact p.Prime := ⟨hp⟩
  rcases quadraticChar_isQuadratic (ZMod p) x with h | h | h <;>
    norm_num [localChar, qchar, h]

theorem abs_productChar_le_one (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime)
    (x : ZMod (primeModulus s)) : |productChar s hs x| ≤ 1 := by
  rw [productChar, Finset.abs_prod]
  exact Finset.prod_le_one (fun _ _ => abs_nonneg _) fun p _ =>
    abs_localChar_le_one p (hs p p.property) _

theorem productChar_complete_correlation (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime)
    [NeZero (primeModulus s)] [(p : s) → NeZero (p : ℕ)] {n : ℕ} (v : Fin n → ℕ) :
    (∑ x : ZMod (primeModulus s),
        productChar s hs (∏ i : Fin n, (x + v i))) =
      ∏ p : s, ∑ y : ZMod (p : ℕ),
        localChar p (hs p p.property) (∏ i : Fin n, (y + v i)) := by
  let e := primeCRT s hs
  calc
    _ = ∑ y : (∀ p : s, ZMod (p : ℕ)),
        ∏ p : s, localChar p (hs p p.property) (∏ i : Fin n, (y p + v i)) := by
      rw [← e.toEquiv.sum_comp]
      apply Finset.sum_congr rfl
      intro x _
      rw [productChar]
      apply Fintype.prod_congr
      intro p
      congr 1
      simp [e]
    _ = _ := by rw [Fintype.prod_sum]

theorem prod_prime_gcd (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) (d : ℕ) :
    (∏ p ∈ s, p.gcd d) = (primeModulus s).gcd d := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [primeModulus]
  | @insert p s hp ih =>
    have hs' : ∀ r ∈ s, r.Prime := fun r hr => hs r (Finset.mem_insert_of_mem hr)
    have hpp : p.Prime := hs p (Finset.mem_insert_self p s)
    have hcop : p.Coprime (primeModulus s) := Nat.Coprime.prod_right fun r hr =>
      hpp.coprime_iff_not_dvd.mpr fun hdvd =>
        hp ((Nat.prime_dvd_prime_iff_eq hpp (hs' r hr)).mp hdvd ▸ hr)
    rw [Finset.prod_insert hp, ih hs']
    rw [show primeModulus (insert p s) = p * primeModulus s from Finset.prod_insert hp]
    rw [Nat.gcd_comm (p * primeModulus s), hcop.gcd_mul d,
      Nat.gcd_comm d p, Nat.gcd_comm d (primeModulus s)]

end Pollack17.Burgess

end

/- ## Averaging the gcd losses in composite-modulus correlations

Source module `ErdosProblems.Erdos1141.BurgessGcdAverage`. -/

noncomputable section

namespace Pollack17.Burgess

open scoped BigOperators

theorem gcd_le_divisor_sum {q : ℕ} (hq : q ≠ 0) (n : ℕ) :
    q.gcd n ≤ ∑ d ∈ q.divisors, if d ∣ n then d else 0 := by
  have hg : q.gcd n ∈ q.divisors := Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_left q n, hq⟩
  calc
    q.gcd n = (if q.gcd n ∣ n then q.gcd n else 0) := by simp [Nat.gcd_dvd_right]
    _ ≤ _ := Finset.single_le_sum (s := q.divisors)
      (f := fun d => if d ∣ n then d else 0) (fun _ _ => Nat.zero_le _) hg

theorem sum_gcd_Icc_le {q : ℕ} (hq : q ≠ 0) (V : ℕ) :
    (∑ n ∈ Finset.Icc 1 V, q.gcd n) ≤ V * q.divisors.card := by
  calc
    _ ≤ ∑ n ∈ Finset.Icc 1 V, ∑ d ∈ q.divisors, if d ∣ n then d else 0 :=
      Finset.sum_le_sum fun n _ => gcd_le_divisor_sum hq n
    _ = ∑ d ∈ q.divisors, ∑ n ∈ Finset.Icc 1 V, if d ∣ n then d else 0 :=
      Finset.sum_comm
    _ = ∑ d ∈ q.divisors, d * (V / d) := by
      apply Finset.sum_congr rfl
      intro d _
      rw [← Finset.sum_filter]
      change (∑ _n ∈ positiveMultiplesUpTo d V, d) = _
      simp [positiveMultiplesUpTo_card, Nat.mul_comm]
    _ ≤ ∑ _d ∈ q.divisors, V :=
      Finset.sum_le_sum fun d _ => Nat.mul_div_le V d
    _ = _ := by simp [Nat.mul_comm]

theorem sum_gcd_dist_one_side_le {q V a : ℕ} (hq : q ≠ 0) (ha : a ≤ V)
    (S : Finset ℕ) (hS : S ⊆ Finset.Icc 1 V)
    (hne : ∀ b ∈ S, b ≠ a)
    (hside : (∀ b ∈ S, b ≤ a) ∨ (∀ b ∈ S, a ≤ b)) :
    (∑ b ∈ S, q.gcd (Nat.dist a b)) ≤ V * q.divisors.card := by
  have hinj : Set.InjOn (Nat.dist a) S := by
    intro b hb c hc hbc
    rcases hside with hl | hr
    · have hb' := hl b hb
      have hc' := hl c hc
      rw [Nat.dist_eq_sub_of_le_right hb', Nat.dist_eq_sub_of_le_right hc'] at hbc
      omega
    · have hb' := hr b hb
      have hc' := hr c hc
      rw [Nat.dist_eq_sub_of_le hb', Nat.dist_eq_sub_of_le hc'] at hbc
      omega
  have hsub : S.image (Nat.dist a) ⊆ Finset.Icc 1 V := by
    intro n hn
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hn
    have hbV := (Finset.mem_Icc.mp (hS hb)).2
    have hbne := hne b hb
    simp only [Finset.mem_Icc, Nat.dist]
    omega
  calc
    _ = ∑ n ∈ S.image (Nat.dist a), q.gcd n := (Finset.sum_image hinj).symm
    _ ≤ ∑ n ∈ Finset.Icc 1 V, q.gcd n := Finset.sum_le_sum_of_subset hsub
    _ ≤ _ := sum_gcd_Icc_le hq V

theorem sum_gcd_dist_erase_le {q V a : ℕ} (hq : q ≠ 0) (ha : a ≤ V) :
    (∑ b ∈ (Finset.Icc 1 V).erase a, q.gcd (Nat.dist a b)) ≤
      2 * V * q.divisors.card := by
  let L := (Finset.Icc 1 V).filter (fun b => b < a)
  let R := (Finset.Icc 1 V).filter (fun b => a < b)
  have heq : (Finset.Icc 1 V).erase a = L ∪ R := by
    ext b
    simp only [Finset.mem_erase, L, R, Finset.mem_union, Finset.mem_filter, Finset.mem_Icc]
    omega
  have hdisj : Disjoint L R := by
    apply Finset.disjoint_left.mpr
    intro b hbL hbR
    have hL := (Finset.mem_filter.mp hbL).2
    have hR := (Finset.mem_filter.mp hbR).2
    omega
  rw [heq, Finset.sum_union hdisj]
  have hL := sum_gcd_dist_one_side_le hq ha L (Finset.filter_subset _ _)
    (fun b hb => ne_of_lt (Finset.mem_filter.mp hb).2)
    (Or.inl (fun b hb => le_of_lt (Finset.mem_filter.mp hb).2))
  have hR := sum_gcd_dist_one_side_le hq ha R (Finset.filter_subset _ _)
    (fun b hb => ne_of_gt (Finset.mem_filter.mp hb).2)
    (Or.inr (fun b hb => le_of_lt (Finset.mem_filter.mp hb).2))
  nlinarith

theorem modEq_iff_dvd_dist (p a b : ℕ) : a ≡ b [MOD p] ↔ p ∣ Nat.dist a b := by
  rcases le_total a b with hab | hba
  · rw [Nat.dist_eq_sub_of_le hab, Nat.modEq_iff_dvd' hab]
  · rw [Nat.dist_eq_sub_of_le_right hba, Nat.ModEq.comm, Nat.modEq_iff_dvd' hba]

end Pollack17.Burgess

end

/- ## Complete composite correlations with gcd losses

Source module `ErdosProblems.Erdos1141.BurgessCompositeCorrelation`. -/

noncomputable section

namespace Pollack17.Burgess

open scoped BigOperators

theorem simpleRootConstant_one_le (n : ℕ) : 1 ≤ Stepanov.simpleRootConstant n := by
  unfold Stepanov.simpleRootConstant
  omega

theorem local_correlation_le_gcd {p : ℕ} (hp : p.Prime) [NeZero p]
    {n : ℕ} (v : Fin n → ℕ) (i : Fin n) :
    |∑ x : ZMod p, localChar p hp (∏ j : Fin n, (x + v j))| ≤
      (Stepanov.simpleRootConstant n : ℝ) * Real.sqrt p *
        ∏ j ∈ Finset.univ.erase i, (p.gcd (Nat.dist (v i) (v j)) : ℝ) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  let g : Fin n → ℕ := fun j => p.gcd (Nat.dist (v i) (v j))
  have hg : ∀ j : Fin n, 1 ≤ g j := fun j => Nat.gcd_pos_of_pos_left _ hp.pos
  have hprod : (1 : ℝ) ≤ ∏ j ∈ Finset.univ.erase i, (g j : ℝ) := by
    exact_mod_cast Finset.one_le_prod' (s := Finset.univ.erase i) (fun j _ => hg j)
  have hbase : (1 : ℝ) ≤ (Stepanov.simpleRootConstant n : ℝ) * Real.sqrt p := by
    have hC : (1 : ℝ) ≤ Stepanov.simpleRootConstant n := by
      exact_mod_cast simpleRootConstant_one_le n
    have hS : (1 : ℝ) ≤ Real.sqrt p :=
      Real.one_le_sqrt.mpr (by exact_mod_cast hp.one_lt.le)
    nlinarith
  by_cases hsingle : ∀ j : Fin n, j ≠ i → (v j : ZMod p) ≠ v i
  · have hcorr := correlation_le_of_singleton (fun j => (v j : ZMod p)) ⟨i, hsingle⟩
    exact hcorr.trans (le_mul_of_one_le_right (le_trans zero_le_one hbase) hprod)
  · push Not at hsingle
    obtain ⟨j, hji, hval⟩ := hsingle
    have hdiv : p ∣ Nat.dist (v i) (v j) :=
      (modEq_iff_dvd_dist p (v i) (v j)).mp
        ((ZMod.natCast_eq_natCast_iff _ _ _).mp hval.symm)
    have hgj : g j = p := Nat.gcd_eq_left_iff_dvd.mpr hdiv
    have hpProd : (p : ℝ) ≤ ∏ j ∈ Finset.univ.erase i, (g j : ℝ) := by
      have h := Finset.single_le_prod' (s := Finset.univ.erase i)
        (fun j _ => hg j) (Finset.mem_erase.mpr ⟨hji, Finset.mem_univ j⟩)
      rw [hgj] at h
      exact_mod_cast h
    have htrivial : |∑ x : ZMod p, localChar p hp (∏ j : Fin n, (x + v j))| ≤ p := by
      calc
        _ ≤ ∑ x : ZMod p, |localChar p hp (∏ j : Fin n, (x + v j))| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _x : ZMod p, (1 : ℝ) :=
          Finset.sum_le_sum fun x _ => abs_localChar_le_one p hp _
        _ = _ := by simp
    exact htrivial.trans (hpProd.trans
      (le_mul_of_one_le_left (le_trans zero_le_one hprod) hbase))

theorem product_correlation_le_gcd (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime)
    [NeZero (primeModulus s)] {n : ℕ} (v : Fin n → ℕ) (i : Fin n) :
    |∑ x : ZMod (primeModulus s), productChar s hs (∏ j : Fin n, (x + v j))| ≤
      (Stepanov.simpleRootConstant n : ℝ) ^ s.card * Real.sqrt (primeModulus s) *
        ∏ j ∈ Finset.univ.erase i, ((primeModulus s).gcd (Nat.dist (v i) (v j)) : ℝ) := by
  classical
  have : (p : s) → NeZero (p : ℕ) := fun p => ⟨(hs p p.property).ne_zero⟩
  rw [productChar_complete_correlation s hs v, Finset.abs_prod]
  refine (Finset.prod_le_prod (s := (Finset.univ : Finset s)) (fun _ _ => abs_nonneg _)
    (fun (p : s) _ => local_correlation_le_gcd (hs p p.property) v i)).trans_eq ?_
  simp only [Finset.prod_mul_distrib]
  have hC : (∏ _p : s, (Stepanov.simpleRootConstant n : ℝ)) =
      (Stepanov.simpleRootConstant n : ℝ) ^ s.card := by simp
  have hsqrt : (∏ p : s, Real.sqrt (p : ℕ)) = Real.sqrt (primeModulus s) := by
    rw [← Real.sqrt_prod _ (fun p _ => Nat.cast_nonneg _), ← Nat.cast_prod]
    congr 2
    exact Finset.prod_attach s (fun p : ℕ => p)
  have hgcd : (∏ p : s, ∏ j ∈ Finset.univ.erase i,
        ((p : ℕ).gcd (Nat.dist (v i) (v j)) : ℝ)) =
      ∏ j ∈ Finset.univ.erase i, ((primeModulus s).gcd (Nat.dist (v i) (v j)) : ℝ) := by
    rw [Finset.prod_comm]
    apply Finset.prod_congr rfl
    intro j _
    rw [← Nat.cast_prod]
    congr 1
    exact (Finset.prod_coe_sort s (fun p : ℕ => p.gcd (Nat.dist (v i) (v j)))).trans
      (prod_prime_gcd s hs _)
  rw [hC, hsqrt, hgcd]

end Pollack17.Burgess

end

/- ## Summing independent difference weights around a distinguished tuple entry

Source module `ErdosProblems.Erdos1141.BurgessStarWeights`. -/

noncomputable section

namespace Pollack17.Burgess

open scoped BigOperators

noncomputable def starWeight {α : Type*} {n : ℕ} (w : α → α → ℝ)
    (v : Fin n → α) (i : Fin n) : ℝ :=
  ∏ j : {j : Fin n // j ≠ i}, w (v i) (v j)

theorem starWeight_nonneg {α : Type*} {n : ℕ} (w : α → α → ℝ)
    (hw : ∀ a b, 0 ≤ w a b) (v : Fin n → α) (i : Fin n) :
    0 ≤ starWeight w v i := Finset.prod_nonneg fun _ _ => hw _ _

theorem starWeight_eq_prod_erase {α : Type*} {n : ℕ} (w : α → α → ℝ)
    (v : Fin n → α) (i : Fin n) :
    starWeight w v i = ∏ j ∈ Finset.univ.erase i, w (v i) (v j) := by
  exact (Finset.prod_subtype (p := fun j => j ≠ i)
    (Finset.univ.erase i) (by simp) (fun j => w (v i) (v j))).symm

theorem sum_starWeight {α : Type*} [Fintype α] {n : ℕ}
    (w : α → α → ℝ) (i : Fin n) :
    (∑ v : Fin n → α, starWeight w v i) =
      ∑ a : α, (∑ b : α, w a b) ^ (n - 1) := by
  classical
  let e := Equiv.funSplitAt i α
  let F : (α × ({j : Fin n // j ≠ i} → α)) → ℝ :=
    fun ab => ∏ j : {j : Fin n // j ≠ i}, w ab.1 (ab.2 j)
  have heq (v : Fin n → α) : starWeight w v i = F (e v) := rfl
  have hcard : Fintype.card {j : Fin n // j ≠ i} = n - 1 := by
    simp [Fintype.card_subtype_compl]
  calc
    _ = ∑ v : Fin n → α, F (e v) := Finset.sum_congr rfl fun v _ => heq v
    _ = ∑ ab, F ab := e.sum_comp F
    _ = ∑ a : α, ∑ b : ({j : Fin n // j ≠ i} → α),
        ∏ j : {j : Fin n // j ≠ i}, w a (b j) := Fintype.sum_prod_type _
    _ = ∑ a : α, ∏ _j : {j : Fin n // j ≠ i}, ∑ b : α, w a b := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Fintype.prod_sum]
    _ = _ := by simp [hcard]

theorem sum_starWeight_le {α : Type*} [Fintype α] {n : ℕ}
    (w : α → α → ℝ) (hw : ∀ a b, 0 ≤ w a b) {B : ℝ}
    (hB : ∀ a : α, ∑ b : α, w a b ≤ B) (i : Fin n) :
    (∑ v : Fin n → α, starWeight w v i) ≤ (Fintype.card α : ℝ) * B ^ (n - 1) := by
  rw [sum_starWeight]
  calc
    _ ≤ ∑ _a : α, B ^ (n - 1) := Finset.sum_le_sum fun a _ =>
      pow_le_pow_left₀ (Finset.sum_nonneg fun b _ => hw a b) (hB a) _
    _ = _ := by simp

end Pollack17.Burgess

end

/- ## An arbitrary-order moment bound from singleton correlation estimates

Source module `ErdosProblems.Erdos1141.BurgessTupleBound`. -/

noncomputable section

namespace Pollack17.Burgess

open scoped BigOperators

theorem sum_tuple_correlations_le {α : Type*} [Fintype α] (r : ℕ)
    (corr : (Fin (2 * r) → α) → ℝ) (w : α → α → ℝ)
    (hw : ∀ a b, 0 ≤ w a b) {B C T : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hrow : ∀ a, ∑ b : α, w a b ≤ T)
    (htrivial : ∀ v, corr v ≤ B)
    (hsingle : ∀ (v : Fin (2 * r) → α) (i : Fin (2 * r)),
      (∀ j, j ≠ i → v j ≠ v i) → corr v ≤ C * starWeight w v i) :
    (∑ v : Fin (2 * r) → α, corr v) ≤
      (Fintype.card α : ℝ) ^ r * (r : ℝ) ^ (2 * r) * B +
        C * (2 * r : ℕ) * (Fintype.card α : ℝ) * T ^ (2 * r - 1) := by
  classical
  have hpoint (v : Fin (2 * r) → α) :
      corr v ≤ (if RepeatedTuple v then B else 0) + C * ∑ i, starWeight w v i := by
    have hweight : 0 ≤ ∑ i, starWeight w v i :=
      Finset.sum_nonneg fun i _ => starWeight_nonneg w hw v i
    by_cases hv : RepeatedTuple v
    · rw [if_pos hv]
      exact (htrivial v).trans (le_add_of_nonneg_right (mul_nonneg hC hweight))
    · rw [if_neg hv, zero_add]
      have hsi : ∃ i : Fin (2 * r), ∀ j, j ≠ i → v j ≠ v i := by
        simpa only [RepeatedTuple, not_forall, not_exists, not_and] using hv
      obtain ⟨i, hi⟩ := hsi
      exact (hsingle v i hi).trans (mul_le_mul_of_nonneg_left
        (Finset.single_le_sum (fun j _ => starWeight_nonneg w hw v j) (Finset.mem_univ i)) hC)
  have hdiag : (∑ v : Fin (2 * r) → α, if RepeatedTuple v then B else 0) ≤
      (Fintype.card α : ℝ) ^ r * (r : ℝ) ^ (2 * r) * B := by
    rw [← Finset.sum_filter]
    change (∑ _v ∈ repeatedTuples α (2 * r), B) ≤ _
    simp only [Finset.sum_const, nsmul_eq_mul]
    apply mul_le_mul_of_nonneg_right _ hB
    exact_mod_cast repeatedTuples_card_le α r
  have hweights : (∑ v : Fin (2 * r) → α, ∑ i, starWeight w v i) ≤
      (2 * r : ℕ) * (Fintype.card α : ℝ) * T ^ (2 * r - 1) := by
    rw [Finset.sum_comm]
    calc
      _ ≤ ∑ _i : Fin (2 * r), (Fintype.card α : ℝ) * T ^ (2 * r - 1) :=
        Finset.sum_le_sum fun i _ => sum_starWeight_le w hw hrow i
      _ = _ := by simp [mul_assoc]
  calc
    _ ≤ ∑ v : Fin (2 * r) → α,
        ((if RepeatedTuple v then B else 0) + C * ∑ i, starWeight w v i) :=
      Finset.sum_le_sum fun v _ => hpoint v
    _ = (∑ v : Fin (2 * r) → α, if RepeatedTuple v then B else 0) +
        C * ∑ v : Fin (2 * r) → α, ∑ i, starWeight w v i := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ _ := by
      have h := add_le_add hdiag (mul_le_mul_of_nonneg_left hweights hC)
      simpa only [mul_assoc] using h

end Pollack17.Burgess

end

/- ## Ratio energy with arbitrary coprime natural denominators

Source module `ErdosProblems.Erdos1141.BurgessEnergy`. -/

noncomputable section

namespace Pollack17.Burgess

open scoped BigOperators

def naturalRatioWeight (q M H : ℕ) (D : Finset ℕ) (x : ZMod q) : ℕ :=
  ((Finset.range H ×ˢ D).filter fun iu =>
    (iu.2 : ZMod q)⁻¹ * (M + iu.1 : ℕ) = x).card

noncomputable def naturalRatioEnergy (q M H : ℕ) [NeZero q] (D : Finset ℕ) : ℝ :=
  ∑ x : ZMod q, (naturalRatioWeight q M H D x : ℝ) ^ 2

theorem sum_naturalRatioWeight (q M H : ℕ) [NeZero q] (D : Finset ℕ) :
    ∑ x : ZMod q, naturalRatioWeight q M H D x = H * D.card := by
  have h := Finset.card_eq_sum_card_fiberwise
    (s := Finset.range H ×ˢ D) (t := Finset.univ)
    (f := fun iu : ℕ × ℕ => (iu.2 : ZMod q)⁻¹ * (M + iu.1 : ℕ)) (by simp)
  simpa only [Finset.card_product, Finset.card_range, naturalRatioWeight] using h.symm

theorem sum_naturalRatioWeight_mul (q M H : ℕ) [NeZero q]
    (D : Finset ℕ) (f : ZMod q → ℝ) :
    (∑ x : ZMod q, (naturalRatioWeight q M H D x : ℝ) * f x) =
      ∑ i ∈ Finset.range H, ∑ u ∈ D, f ((u : ZMod q)⁻¹ * (M + i : ℕ)) := by
  calc
    _ = ∑ iu ∈ Finset.range H ×ˢ D,
        f ((iu.2 : ZMod q)⁻¹ * (M + iu.1 : ℕ)) := by
      rw [← Finset.sum_fiberwise' (Finset.range H ×ˢ D)
        (fun iu : ℕ × ℕ => (iu.2 : ZMod q)⁻¹ * (M + iu.1 : ℕ)) f]
      apply Finset.sum_congr rfl
      intro x _
      simp [naturalRatioWeight, nsmul_eq_mul]
    _ = _ := Finset.sum_product _ _ _

theorem sum_card_fiber_sq_eq_card_collision
    {α β : Type*} [Fintype β] [DecidableEq β]
    (s : Finset α) (f : α → β) :
    (∑ y : β, ((s.filter fun a => f a = y).card) ^ 2) =
      (((s ×ˢ s).filter fun ab => f ab.1 = f ab.2).card) := by
  classical
  let c := (s ×ˢ s).filter fun ab => f ab.1 = f ab.2
  have hmap : (c : Set (α × α)).MapsTo (fun ab => f ab.1)
      (Finset.univ : Finset β) := by
    intro ab _
    exact Finset.mem_univ _
  change (∑ y : β, ((s.filter fun a => f a = y).card) ^ 2) = c.card
  rw [Finset.card_eq_sum_card_fiberwise hmap]
  apply Finset.sum_congr rfl
  intro y _
  rw [pow_two, ← Finset.card_product]
  congr 1
  ext ab
  simp only [c, Finset.mem_product, Finset.mem_filter]
  aesop

theorem natural_inv_ratio_eq_iff {q n₁ n₂ u₁ u₂ : ℕ}
    (h₁ : u₁.Coprime q) (h₂ : u₂.Coprime q) :
    (u₁ : ZMod q)⁻¹ * n₁ = (u₂ : ZMod q)⁻¹ * n₂ ↔
      n₁ * u₂ ≡ n₂ * u₁ [MOD q] := by
  rw [← ZMod.natCast_eq_natCast_iff, Nat.cast_mul, Nat.cast_mul]
  have hmul₁ := ZMod.coe_mul_inv_eq_one u₁ h₁
  have hmul₂ := ZMod.coe_mul_inv_eq_one u₂ h₂
  constructor
  · intro h
    calc
      (n₁ : ZMod q) * u₂ = ((u₁ : ZMod q) * (u₁ : ZMod q)⁻¹) * (n₁ * u₂) := by
        rw [hmul₁, one_mul]
      _ = ((u₁ : ZMod q) * u₂) * ((u₁ : ZMod q)⁻¹ * n₁) := by ring
      _ = ((u₁ : ZMod q) * u₂) * ((u₂ : ZMod q)⁻¹ * n₂) := by rw [h]
      _ = ((u₂ : ZMod q) * (u₂ : ZMod q)⁻¹) * (n₂ * u₁) := by ring
      _ = _ := by rw [hmul₂, one_mul]
  · intro h
    calc
      (u₁ : ZMod q)⁻¹ * n₁ = ((u₂ : ZMod q) * (u₂ : ZMod q)⁻¹) *
          ((u₁ : ZMod q)⁻¹ * n₁) := by rw [hmul₂, one_mul]
      _ = ((u₁ : ZMod q)⁻¹ * (u₂ : ZMod q)⁻¹) * (n₁ * u₂) := by ring
      _ = ((u₁ : ZMod q)⁻¹ * (u₂ : ZMod q)⁻¹) * (n₂ * u₁) := by rw [h]
      _ = ((u₁ : ZMod q) * (u₁ : ZMod q)⁻¹) * ((u₂ : ZMod q)⁻¹ * n₂) := by ring
      _ = _ := by rw [hmul₁, one_mul]

theorem naturalRatioEnergy_eq_sum (q M H : ℕ) [NeZero q] (D : Finset ℕ)
    (hD : ∀ u ∈ D, u.Coprime q) :
    naturalRatioEnergy q M H D =
      ((∑ u ∈ D, ∑ v ∈ D, (burgessIntervalCollision q M H u v).card : ℕ) : ℝ) := by
  let box := Finset.range H ×ˢ D
  have h := sum_card_fiber_sq_eq_card_collision box
    (fun iu : ℕ × ℕ => (iu.2 : ZMod q)⁻¹ * (M + iu.1 : ℕ))
  have heq : ((box ×ˢ box).filter fun ab =>
      (ab.1.2 : ZMod q)⁻¹ * (M + ab.1.1 : ℕ) =
        (ab.2.2 : ZMod q)⁻¹ * (M + ab.2.1 : ℕ)) =
      ((box ×ˢ box).filter fun ab =>
        (M + ab.1.1) * ab.2.2 ≡ (M + ab.2.1) * ab.1.2 [MOD q]) := by
    apply Finset.filter_congr
    intro ab hab
    have hmem := Finset.mem_product.mp hab
    exact natural_inv_ratio_eq_iff
      (hD ab.1.2 (Finset.mem_product.mp hmem.1).2)
      (hD ab.2.2 (Finset.mem_product.mp hmem.2).2)
  rw [heq] at h
  have hcard : (((box ×ˢ box).filter fun ab =>
      (M + ab.1.1) * ab.2.2 ≡ (M + ab.2.1) * ab.1.2 [MOD q]).card) =
      ∑ u ∈ D, ∑ v ∈ D, (burgessIntervalCollision q M H u v).card := by
    simp only [box, burgessIntervalCollision, Finset.card_eq_sum_ones,
      Finset.sum_filter, Finset.sum_product]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro u _
    calc
      _ = ∑ i ∈ Finset.range H, ∑ v ∈ D, ∑ j ∈ Finset.range H,
          if (M + i) * v ≡ (M + j) * u [MOD q] then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.sum_comm]
      _ = _ := Finset.sum_comm
  rw [hcard] at h
  have hcast := congrArg (fun n : ℕ => (n : ℝ)) h
  simpa only [naturalRatioEnergy, naturalRatioWeight, box, Nat.cast_sum,
    Nat.cast_pow] using hcast

theorem naturalRatioEnergy_le {q M H U : ℕ} [NeZero q] (D : Finset ℕ)
    (hD : D ⊆ Finset.Icc 1 U) (hcop : ∀ u ∈ D, u.Coprime q)
    (hH : 0 < H) (hU : 0 < U) (hsmall : 2 * (U * H) < q) :
    naturalRatioEnergy q M H D ≤
      ((H : ℝ) * (1 + Real.log U) + U) * ((U : ℝ) * (1 + Real.log U)) := by
  rw [naturalRatioEnergy_eq_sum q M H D hcop]
  have hfirst : (∑ u ∈ D, ∑ v ∈ D, (burgessIntervalCollision q M H u v).card) ≤
      ∑ u ∈ D, ∑ v ∈ D, (H / (u / u.gcd v) + 1) := by
    apply Finset.sum_le_sum
    intro u hu
    apply Finset.sum_le_sum
    intro v hv
    exact burgessIntervalCollision_card_le_of_coprime hH hU
      (hD hu) (hD hv) (hcop u hu).symm hsmall
  have hsecond : (∑ u ∈ D, ∑ v ∈ D, (H / (u / u.gcd v) + 1)) ≤
      ∑ u ∈ Finset.Icc 1 U, ∑ v ∈ Finset.Icc 1 U, (H / (u / u.gcd v) + 1) := by
    exact (Finset.sum_le_sum fun u _ => Finset.sum_le_sum_of_subset hD).trans
      (Finset.sum_le_sum_of_subset hD)
  calc
    _ ≤ ((∑ u ∈ Finset.Icc 1 U, ∑ v ∈ Finset.Icc 1 U,
        (H / (u / u.gcd v) + 1) : ℕ) : ℝ) := by exact_mod_cast hfirst.trans hsecond
    _ ≤ (burgessDivisorOvercount H U : ℝ) := reduced_denominator_sum_cast_le H U
    _ ≤ _ := burgessDivisorOvercount_cast_le H U hU

end Pollack17.Burgess

end

/- ## Weighted Hölder in the integer-power form for Burgess amplification

Source module `ErdosProblems.Erdos1141.BurgessHolder`. -/

noncomputable section

namespace Pollack17.Burgess

open scoped BigOperators

theorem weighted_power_sum_le {ι : Type*} (S : Finset ι) (w z : ι → ℝ)
    (hw : ∀ i ∈ S, 0 ≤ w i) (hz : ∀ i ∈ S, 0 ≤ z i) (k : ℕ) :
    (∑ i ∈ S, w i * z i) ^ (k + 1) ≤
      (∑ i ∈ S, w i) ^ k * ∑ i ∈ S, w i * z i ^ (k + 1) := by
  let W := ∑ i ∈ S, w i
  have hW0 : 0 ≤ W := Finset.sum_nonneg hw
  by_cases hW : W = 0
  · have hwi : ∀ i ∈ S, w i = 0 := (Finset.sum_eq_zero_iff_of_nonneg hw).mp hW
    have hleft : (∑ i ∈ S, w i * z i) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      rw [hwi i hi, zero_mul]
    have hright : (∑ i ∈ S, w i * z i ^ (k + 1)) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      rw [hwi i hi, zero_mul]
    simp [hleft, hright]
  have hWpos : 0 < W := lt_of_le_of_ne hW0 (Ne.symm hW)
  have hj := Real.pow_arith_mean_le_arith_mean_pow S (fun i => w i / W) z
    (fun i hi => div_nonneg (hw i hi) hW0)
    (by rw [← Finset.sum_div]; exact div_self hW) hz (k + 1)
  have hj' : ((∑ i ∈ S, w i * z i) / W) ^ (k + 1) ≤
      (∑ i ∈ S, w i * z i ^ (k + 1)) / W := by
    simpa only [div_mul_eq_mul_div, ← Finset.sum_div] using hj
  rw [div_pow] at hj'
  have hscaled := (div_le_iff₀ (pow_pos hWpos (k + 1))).mp hj'
  calc
    (∑ i ∈ S, w i * z i) ^ (k + 1) ≤
        ((∑ i ∈ S, w i * z i ^ (k + 1)) / W) * W ^ (k + 1) := hscaled
    _ = W ^ k * ∑ i ∈ S, w i * z i ^ (k + 1) := by
      rw [pow_succ]
      field_simp
    _ = _ := rfl

theorem weighted_even_power_sum_le {ι : Type*} (S : Finset ι) (w z : ι → ℝ)
    (hw : ∀ i ∈ S, 0 ≤ w i) (hz : ∀ i ∈ S, 0 ≤ z i) (k : ℕ) :
    (∑ i ∈ S, w i * z i) ^ (2 * (k + 1)) ≤
      (∑ i ∈ S, w i) ^ (2 * k) * (∑ i ∈ S, w i ^ 2) *
        ∑ i ∈ S, z i ^ (2 * (k + 1)) := by
  have hsum0 : 0 ≤ ∑ i ∈ S, w i * z i :=
    Finset.sum_nonneg fun i hi => mul_nonneg (hw i hi) (hz i hi)
  have hj := weighted_power_sum_le S w z hw hz k
  have hj2 := pow_le_pow_left₀ (pow_nonneg hsum0 _) hj 2
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq S w (fun i => z i ^ (k + 1))
  have hpowers (i : ι) : (z i ^ (k + 1)) ^ 2 = z i ^ (2 * (k + 1)) := by
    rw [← pow_mul]
    congr 1
    omega
  simp_rw [hpowers] at hcs
  calc
    (∑ i ∈ S, w i * z i) ^ (2 * (k + 1)) =
        ((∑ i ∈ S, w i * z i) ^ (k + 1)) ^ 2 := by
      rw [← pow_mul]
      congr 1
      omega
    _ ≤ ((∑ i ∈ S, w i) ^ k * ∑ i ∈ S, w i * z i ^ (k + 1)) ^ 2 := hj2
    _ = (∑ i ∈ S, w i) ^ (2 * k) * (∑ i ∈ S, w i * z i ^ (k + 1)) ^ 2 := by
      rw [mul_pow, ← pow_mul]
      congr 2
      omega
    _ ≤ (∑ i ∈ S, w i) ^ (2 * k) *
        ((∑ i ∈ S, w i ^ 2) * ∑ i ∈ S, z i ^ (2 * (k + 1))) :=
      mul_le_mul_of_nonneg_left hcs (pow_nonneg (Finset.sum_nonneg hw) _)
    _ = _ := by ring

end Pollack17.Burgess

end

/- ## Interval averaging for real multiplicative characters

Source module `ErdosProblems.Erdos1141.BurgessAmplifier`. -/

noncomputable section

namespace Pollack17.Burgess

open scoped BigOperators

lemma abs_sum_range_shift_sub_le (f : ℕ → ℝ)
    (hf : ∀ n, |f n| ≤ 1) (M H h : ℕ) (hh : h ≤ H) :
    |(∑ i ∈ Finset.range H, f (M + i)) -
      ∑ i ∈ Finset.range H, f (M + h + i)| ≤ 2 * h := by
  have hH₁ : h + (H - h) = H := Nat.add_sub_of_le hh
  have hH₂ : (H - h) + h = H := Nat.sub_add_cancel hh
  have hdecomp :
      (∑ i ∈ Finset.range H, f (M + i)) -
          ∑ i ∈ Finset.range H, f (M + h + i) =
        (∑ i ∈ Finset.range h, f (M + i)) -
          ∑ i ∈ Finset.range h, f (M + H + i) := by
    have hleft := Finset.sum_range_add (fun i ↦ f (M + i)) h (H - h)
    have hright := Finset.sum_range_add
      (fun i ↦ f (M + h + i)) (H - h) h
    rw [hH₁] at hleft
    rw [hH₂] at hright
    rw [hleft, hright]
    have hmiddle :
        (∑ x ∈ Finset.range (H - h), f (M + (h + x))) =
          ∑ x ∈ Finset.range (H - h), f (M + h + x) := by
      apply Finset.sum_congr rfl
      intro i _
      congr 1
      omega
    have hsuffix :
        (∑ x ∈ Finset.range h, f (M + h + ((H - h) + x))) =
          ∑ x ∈ Finset.range h, f (M + H + x) := by
      apply Finset.sum_congr rfl
      intro i _
      congr 1
      omega
    rw [hmiddle, hsuffix]
    ring
  rw [hdecomp]
  calc
    |(∑ i ∈ Finset.range h, f (M + i)) -
        ∑ i ∈ Finset.range h, f (M + H + i)| ≤
        |∑ i ∈ Finset.range h, f (M + i)| +
          |∑ i ∈ Finset.range h, f (M + H + i)| := abs_sub _ _
    _ ≤ (∑ i ∈ Finset.range h, |f (M + i)|) +
        ∑ i ∈ Finset.range h, |f (M + H + i)| := by
      gcongr <;> exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ (∑ _i ∈ Finset.range h, (1 : ℝ)) +
        ∑ _i ∈ Finset.range h, (1 : ℝ) := by
      gcongr <;> exact hf _
    _ = 2 * h := by simp; ring

lemma abs_burgess_shift_average_sub_le
    (f : ℕ → ℝ) (hf : ∀ n, |f n| ≤ 1)
    (M H : ℕ) (U V : Finset ℕ) (g : ℕ → ℕ → ℕ)
    (hg : ∀ u ∈ U, ∀ v ∈ V, g u v ≤ H) :
    |((U.card * V.card : ℕ) : ℝ) *
        (∑ i ∈ Finset.range H, f (M + i)) -
      ∑ u ∈ U, ∑ v ∈ V,
        ∑ i ∈ Finset.range H, f (M + g u v + i)| ≤
      ∑ u ∈ U, ∑ v ∈ V, ((2 * g u v : ℕ) : ℝ) := by
  let S : ℕ → ℝ := fun h ↦ ∑ i ∈ Finset.range H, f (M + h + i)
  have hS0 : S 0 = ∑ i ∈ Finset.range H, f (M + i) := by
    simp [S]
  have heq :
      ((U.card * V.card : ℕ) : ℝ) * S 0 -
          ∑ u ∈ U, ∑ v ∈ V, S (g u v) =
        ∑ u ∈ U, ∑ v ∈ V, (S 0 - S (g u v)) := by
    simp only [Finset.sum_sub_distrib]
    simp
    ring
  rw [← hS0, heq]
  calc
    |∑ u ∈ U, ∑ v ∈ V, (S 0 - S (g u v))| ≤
        ∑ u ∈ U, |∑ v ∈ V, (S 0 - S (g u v))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ u ∈ U, ∑ v ∈ V, |S 0 - S (g u v)| := by
      gcongr
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ u ∈ U, ∑ v ∈ V, ((2 * g u v : ℕ) : ℝ) := by
      apply Finset.sum_le_sum
      intro u hu
      apply Finset.sum_le_sum
      intro v hv
      simpa [S] using
        abs_sum_range_shift_sub_le f hf M H (g u v) (hg u hu v hv)

lemma abs_burgess_shifted_triple_sum_le_finset
    (f : ℕ → ℝ) (M H : ℕ) (U V : Finset ℕ) (shift : ℕ → ℕ → ℕ) :
    |∑ u ∈ U, ∑ v ∈ V, ∑ i ∈ Finset.range H,
        f (M + shift u v + i)| ≤
      ∑ i ∈ Finset.range H, ∑ u ∈ U,
        |∑ v ∈ V, f (M + i + shift u v)| := by
  have hreorder :
      (∑ u ∈ U, ∑ v ∈ V, ∑ i ∈ Finset.range H,
          f (M + shift u v + i)) =
        ∑ i ∈ Finset.range H, ∑ u ∈ U,
          ∑ v ∈ V, f (M + i + shift u v) := by
    calc
      (∑ u ∈ U, ∑ v ∈ V, ∑ i ∈ Finset.range H,
          f (M + shift u v + i)) =
        ∑ u ∈ U, ∑ i ∈ Finset.range H,
          ∑ v ∈ V, f (M + shift u v + i) := by
          apply Finset.sum_congr rfl
          intro u hu
          rw [Finset.sum_comm]
      _ = ∑ i ∈ Finset.range H, ∑ u ∈ U,
          ∑ v ∈ V, f (M + shift u v + i) := by
          rw [Finset.sum_comm]
      _ = _ := by
          apply Finset.sum_congr rfl
          intro i hi
          apply Finset.sum_congr rfl
          intro u hu
          apply Finset.sum_congr rfl
          intro v hv
          congr 1
          omega
  rw [hreorder]
  calc
    |∑ i ∈ Finset.range H, ∑ u ∈ U,
        ∑ v ∈ V, f (M + i + shift u v)| ≤
      ∑ i ∈ Finset.range H,
        |∑ u ∈ U, ∑ v ∈ V, f (M + i + shift u v)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range H, ∑ u ∈ U,
        |∑ v ∈ V, f (M + i + shift u v)| := by
      apply Finset.sum_le_sum
      intro i hi
      exact Finset.abs_sum_le_sum_abs _ _

noncomputable def naturalShiftSum {q : ℕ} (f : ZMod q → ℝ) (V : ℕ) (x : ZMod q) : ℝ :=
  ∑ v ∈ Finset.Icc 1 V, f (x + v)

noncomputable def amplifierNumerator {q : ℕ} [NeZero q] (f : ZMod q → ℝ)
    (M H : ℕ) (D : Finset ℕ) (V : ℕ) : ℝ :=
  ∑ x : ZMod q, (naturalRatioWeight q M H D x : ℝ) * |naturalShiftSum f V x|

theorem abs_natural_dilated_sum {q : ℕ} (f : ZMod q → ℝ)
    (hmul : ∀ a b, f (a * b) = f a * f b) (M i u V : ℕ)
    (hu : u.Coprime q) (hfu : |f u| = 1) :
    |∑ v ∈ Finset.Icc 1 V, f (M + i + u * v : ℕ)| =
      |naturalShiftSum f V ((u : ZMod q)⁻¹ * (M + i : ℕ))| := by
  have halg (v : ℕ) : ((M + i + u * v : ℕ) : ZMod q) =
      u * ((u : ZMod q)⁻¹ * (M + i : ℕ) + v) := by
    rw [mul_add, ← mul_assoc, ZMod.coe_mul_inv_eq_one u hu, one_mul]
    push_cast
    ring
  simp_rw [halg, hmul]
  rw [← Finset.mul_sum, abs_mul, hfu, one_mul]
  rfl

theorem amplifierNumerator_eq_natural {q : ℕ} [NeZero q]
    (f : ZMod q → ℝ) (hmul : ∀ a b, f (a * b) = f a * f b)
    (M H : ℕ) (D : Finset ℕ) (V : ℕ)
    (hD : ∀ u ∈ D, u.Coprime q) (hfD : ∀ u ∈ D, |f u| = 1) :
    amplifierNumerator f M H D V =
      ∑ i ∈ Finset.range H, ∑ u ∈ D,
        |∑ v ∈ Finset.Icc 1 V, f (M + i + u * v : ℕ)| := by
  rw [amplifierNumerator, sum_naturalRatioWeight_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro u hu
  exact (abs_natural_dilated_sum f hmul M i u V (hD u hu) (hfD u hu)).symm

theorem amplified_abs_le {q M H U V : ℕ} [NeZero q]
    (f : ZMod q → ℝ) (hmul : ∀ a b, f (a * b) = f a * f b)
    (hf : ∀ x, |f x| ≤ 1) (D : Finset ℕ)
    (hD : D ⊆ Finset.Icc 1 U) (hcop : ∀ u ∈ D, u.Coprime q)
    (hfD : ∀ u ∈ D, |f u| = 1) (hUV : U * V ≤ H) :
    (D.card : ℝ) * V * |∑ i ∈ Finset.range H, f (M + i : ℕ)| ≤
      amplifierNumerator f M H D V + 2 * (D.card : ℝ) * V * (U * V) := by
  let S := ∑ i ∈ Finset.range H, f (M + i : ℕ)
  let T := ∑ u ∈ D, ∑ v ∈ Finset.Icc 1 V,
    ∑ i ∈ Finset.range H, f (M + u * v + i : ℕ)
  have havg := abs_burgess_shift_average_sub_le (fun n => f (n : ZMod q))
    (fun n => hf _) M H D (Finset.Icc 1 V) (fun u v => u * v) (by
      intro u hu v hv
      exact (Nat.mul_le_mul (Finset.mem_Icc.mp (hD hu)).2
        (Finset.mem_Icc.mp hv).2).trans hUV)
  have herror : |(D.card : ℝ) * V * S - T| ≤
      2 * (D.card : ℝ) * V * (U * V) := by
    have havg' : |(D.card : ℝ) * V * S - T| ≤
        ∑ u ∈ D, ∑ v ∈ Finset.Icc 1 V, ((2 * (u * v) : ℕ) : ℝ) := by
      simpa only [Nat.card_Icc, Nat.add_sub_cancel, Nat.cast_mul] using havg
    refine havg'.trans ?_
    calc
      _ ≤ ∑ _u ∈ D, ∑ _v ∈ Finset.Icc 1 V, ((2 * (U * V) : ℕ) : ℝ) := by
        apply Finset.sum_le_sum
        intro u hu
        apply Finset.sum_le_sum
        intro v hv
        exact_mod_cast Nat.mul_le_mul_left 2 (Nat.mul_le_mul
          (Finset.mem_Icc.mp (hD hu)).2 (Finset.mem_Icc.mp hv).2)
      _ = _ := by simp; ring
  have hT : |T| ≤ amplifierNumerator f M H D V := by
    rw [amplifierNumerator_eq_natural f hmul M H D V hcop hfD]
    exact abs_burgess_shifted_triple_sum_le_finset
      (fun n => f (n : ZMod q)) M H D (Finset.Icc 1 V) (fun u v => u * v)
  have htri : |(D.card : ℝ) * V * S| ≤ |(D.card : ℝ) * V * S - T| + |T| := by
    simpa only [sub_add_cancel] using abs_add_le ((D.card : ℝ) * V * S - T) T
  rw [abs_mul, abs_of_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))] at htri
  exact htri.trans ((add_le_add herror hT).trans_eq (add_comm _ _))

theorem amplifierNumerator_even_power_le {q : ℕ} [NeZero q]
    (f : ZMod q → ℝ) (M H : ℕ) (D : Finset ℕ) (V k : ℕ) :
    amplifierNumerator f M H D V ^ (2 * (k + 1)) ≤
      ((H : ℝ) * D.card) ^ (2 * k) * naturalRatioEnergy q M H D *
        ∑ x : ZMod q, naturalShiftSum f V x ^ (2 * (k + 1)) := by
  have hh := weighted_even_power_sum_le (Finset.univ : Finset (ZMod q))
    (fun x => (naturalRatioWeight q M H D x : ℝ))
    (fun x => |naturalShiftSum f V x|)
    (fun x _ => Nat.cast_nonneg _) (fun x _ => abs_nonneg _) k
  have hsum : (∑ x : ZMod q, (naturalRatioWeight q M H D x : ℝ)) =
      (H : ℝ) * D.card := by exact_mod_cast sum_naturalRatioWeight q M H D
  have habs (x : ZMod q) : |naturalShiftSum f V x| ^ (2 * (k + 1)) =
      naturalShiftSum f V x ^ (2 * (k + 1)) := (even_two_mul _).pow_abs _
  simpa only [hsum, habs, amplifierNumerator, naturalRatioEnergy] using hh

end Pollack17.Burgess

end

/- ## The complete Burgess moment for squarefree quadratic characters

Source module `ErdosProblems.Erdos1141.BurgessCompositeMoment`. -/

noncomputable section

namespace Pollack17.Burgess

open scoped BigOperators

theorem productChar_prod (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime)
    {ι : Type*} [Fintype ι] (f : ι → ZMod (primeModulus s)) :
    productChar s hs (∏ i, f i) = ∏ i, productChar s hs (f i) := by
  classical
  simp only [productChar, localChar, qchar, map_prod, Finset.prod_apply, Int.cast_prod]
  rw [Finset.prod_comm]

theorem productChar_moment_expansion (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime)
    [NeZero (primeModulus s)] (V n : ℕ) :
    (∑ x : ZMod (primeModulus s), naturalShiftSum (productChar s hs) V x ^ n) =
      ∑ v : Fin n → (Finset.Icc 1 V), ∑ x : ZMod (primeModulus s),
        productChar s hs (∏ i : Fin n, (x + (v i : ℕ))) := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  rw [naturalShiftSum, ← Finset.sum_attach, Finset.attach_eq_univ, Fintype.sum_pow]
  apply Finset.sum_congr rfl
  intro v _
  exact (productChar_prod s hs (fun i : Fin n => x + (v i : ℕ))).symm

noncomputable def gcdKernel (q a b : ℕ) : ℝ :=
  if b ≠ a then (q.gcd (Nat.dist a b) : ℝ) else 0

theorem gcdKernel_nonneg (q a b : ℕ) : 0 ≤ gcdKernel q a b := by
  unfold gcdKernel
  split_ifs <;> positivity

theorem sum_gcdKernel_le {q : ℕ} (hq : q ≠ 0) (V : ℕ) (a : Finset.Icc 1 V) :
    (∑ b : Finset.Icc 1 V, gcdKernel q a b) ≤ 2 * V * q.divisors.card := by
  rw [Finset.sum_coe_sort (Finset.Icc 1 V) (fun b : ℕ => gcdKernel q a b)]
  simp only [gcdKernel, ← Finset.sum_filter, Finset.filter_ne']
  exact_mod_cast sum_gcd_dist_erase_le hq (Finset.mem_Icc.mp a.property).2

theorem productChar_even_moment_le (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime)
    [NeZero (primeModulus s)] (V r : ℕ) :
    (∑ x : ZMod (primeModulus s), naturalShiftSum (productChar s hs) V x ^ (2 * r)) ≤
      (V : ℝ) ^ r * (r : ℝ) ^ (2 * r) * primeModulus s +
        ((Stepanov.simpleRootConstant (2 * r) : ℝ) ^ s.card * Real.sqrt (primeModulus s)) *
          (2 * r : ℕ) * V * (2 * V * ((primeModulus s).divisors.card : ℝ)) ^ (2 * r - 1) := by
  classical
  let α := Finset.Icc 1 V
  let q := primeModulus s
  let corr : (Fin (2 * r) → α) → ℝ := fun v =>
    ∑ x : ZMod q, productChar s hs (∏ i : Fin (2 * r), (x + (v i : ℕ)))
  let w : α → α → ℝ := fun a b => gcdKernel q a b
  let C : ℝ := (Stepanov.simpleRootConstant (2 * r) : ℝ) ^ s.card * Real.sqrt q
  have hw : ∀ a b : α, 0 ≤ w a b := fun a b => gcdKernel_nonneg q a b
  have hrow : ∀ a : α, (∑ b : α, w a b) ≤ 2 * V * (q.divisors.card : ℝ) :=
    fun a => sum_gcdKernel_le (NeZero.ne q) V a
  have htrivial (v : Fin (2 * r) → α) : corr v ≤ q := by
    calc
      _ ≤ ∑ _x : ZMod q, (1 : ℝ) := Finset.sum_le_sum fun x _ =>
        (le_abs_self _).trans (abs_productChar_le_one s hs _)
      _ = _ := by simp
  have hsingle (v : Fin (2 * r) → α) (i : Fin (2 * r))
      (hi : ∀ j, j ≠ i → v j ≠ v i) : corr v ≤ C * starWeight w v i := by
    have hbound := product_correlation_le_gcd s hs (fun j => (v j : ℕ)) i
    have hwprod : starWeight w v i =
        ∏ j ∈ Finset.univ.erase i, (q.gcd (Nat.dist (v i) (v j)) : ℝ) := by
      rw [starWeight_eq_prod_erase]
      apply Finset.prod_congr rfl
      intro j hj
      have hne : (v j : ℕ) ≠ v i := fun h => hi j (Finset.mem_erase.mp hj).1 (Subtype.ext h)
      exact if_pos hne
    rw [hwprod]
    exact (le_abs_self (corr v)).trans hbound
  rw [productChar_moment_expansion]
  have h := sum_tuple_correlations_le r corr w hw (Nat.cast_nonneg q)
    (by dsimp [C]; positivity) hrow htrivial hsingle
  simpa only [α, corr, C, q, Fintype.card_coe, Nat.card_Icc, Nat.add_sub_cancel] using h

end Pollack17.Burgess

end

/- A singleton specialization of the accepted squarefree fourth moment. -/
namespace OMA.E1140
open Pollack17.Burgess

theorem public_moment_block {p H U V : ℕ} [Fact p.Prime] {δ : ℝ}
    (hH : 0<H) (hU : 0<U) (hV : 0<V) (hUp : U<p)
    (small : 2*(U*H)<p) (fits : U*V≤H) (hδ : 0≤δ)
    (boundary : 2*((U:ℝ)*V)≤δ*H)
    (budget : ((H:ℝ)*U)^2 * (((H:ℝ)*(1+Real.log U)+U)*((U:ℝ)*(1+Real.log U))) *
      ((V:ℝ)^2*16*p+(V:ℝ)^4*(256*(Pollack17.Stepanov.simpleRootConstant 4:ℝ))*Real.sqrt p)
      ≤ (δ*H*U*V)^4)
    (M : ℕ) : |∑ i ∈ Finset.range H, qchar ((M+i:ℕ):ZMod p)| ≤ 2*δ*H := by
  classical
  let s : Finset ℕ := {p}
  have hp : p.Prime := Fact.out
  have hs : ∀ l∈s, Nat.Prime l := by simpa [s] using hp
  have qeq : primeModulus s = p := by simp [s,primeModulus]
  have qcast : (primeModulus s:ℝ) = p := by exact_mod_cast qeq
  let : NeZero (primeModulus s) := ⟨qeq ▸ hp.ne_zero⟩
  let f := productChar s hs
  have eval (n : ℕ) : f n=qchar (n:ZMod p) := by
    simp only [f,productChar,primeCRT_natCast]
    let j : s := ⟨p,by simp [s]⟩
    rw [Finset.prod_eq_single j]
    · rfl
    · intro l _ neq
      exact False.elim (neq (Subtype.ext (Finset.mem_singleton.mp l.2)))
    · intro hj
      exact False.elim (hj (Finset.mem_univ j))
  have cd : (primeModulus s).divisors.card=2 := by
    rw [qeq,hp.divisors,Finset.card_insert_of_notMem (by simpa using hp.ne_one.symm),Finset.card_singleton]
  let D := Finset.Icc 1 U
  let A := amplifierNumerator f M H D V
  have hc : D.card=U := by simp [D]
  have cop (u : ℕ) (hu : u∈D) : u.Coprime (primeModulus s) := by
    rw [qeq]
    have mem := Finset.mem_Icc.mp hu
    exact (hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt mem.1 (mem.2.trans_lt hUp))).symm
  have unit (u : ℕ) (hu : u∈D) : |f (u:ZMod (primeModulus s))|=1 := by
    rw [eval]
    have nz : (u:ZMod p)≠0 := (ZMod.isUnit_iff_coprime u p |>.mpr (by simpa only [qeq] using cop u hu)).ne_zero
    rcases quadraticChar_isQuadratic (ZMod p) (u:ZMod p) with h|h|h
    · exact False.elim (nz (quadraticChar_eq_zero_iff.mp h))
    · simp [qchar,h]
    · simp [qchar,h]
  have moment : (∑ x, naturalShiftSum f V x^4) ≤
      (V:ℝ)^2*16*p+(V:ℝ)^4*(256*(Pollack17.Stepanov.simpleRootConstant 4:ℝ))*Real.sqrt p := by
    have h := productChar_even_moment_le s hs V 2
    norm_num only [Nat.reduceMul,Nat.reduceSub,Nat.cast_ofNat,Nat.reducePow] at h
    apply h.trans_eq
    rw [qcast,cd,show s.card=1 by simp [s]]
    push_cast
    ring
  have energy := naturalRatioEnergy_le (M:=M) D (fun _ a => a) cop hH hU (by rwa [qeq])
  have amp4 := amplifierNumerator_even_power_le f M H D V 1
  norm_num only [Nat.reduceAdd,Nat.reduceMul,hc] at amp4
  have ab : A≤δ*H*U*V := by
    apply le_of_pow_le_pow_left₀ (by decide : 4≠0) (by positivity)
    exact amp4.trans ((mul_le_mul (mul_le_mul_of_nonneg_left energy (by positivity)) moment
      (Finset.sum_nonneg fun _ _ => by positivity) (by
        have : 0≤Real.log U := Real.log_nonneg (by exact_mod_cast hU)
        positivity)).trans budget)
  have amp := amplified_abs_le f (M:=M) (productChar_mul s hs) (abs_productChar_le_one s hs) D
    (fun _ h => h) cop unit fits
  simp only [hc,eval] at amp
  have uv : 0<(U:ℝ)*V := by positivity
  apply le_of_mul_le_mul_left _ uv
  calc
    _ ≤ A+2*(U:ℝ)*V*(U*V) := amp
    _ ≤ δ*H*U*V+((U:ℝ)*V)*(δ*H) := add_le_add ab (by
      calc
        _ = ((U:ℝ)*V)*(2*(U*V)) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left boundary uv.le)
    _ = _ := by ring
end OMA.E1140

/- Rounding three powers of a common real parameter and bounding the Burgess fourth moment. -/
namespace OMA.E1140

set_option maxRecDepth 12000 in
set_option maxHeartbeats 2400000 in
theorem scale_budget {t C : ℝ} (large : 128 ≤ t) (cpos : 0 ≤ C) (hc : C ≤ t)
    (p : ℕ) (scale : (p:ℝ) = t^512) :
    ∃ H U V : ℕ, 0<H ∧ 0<U ∧ 0<V ∧ U<p ∧ V<p ∧
      2*(U*H)<p ∧ U*V≤H ∧ (H:ℝ)≤t^252 ∧
      2*((U:ℝ)*V) ≤ t⁻¹*H ∧
      ((H:ℝ)*U)^2 * (((H:ℝ)*(1+Real.log U)+U)*((U:ℝ)*(1+Real.log U))) *
        ((V:ℝ)^2*16*p+(V:ℝ)^4*C*Real.sqrt p) ≤ (t⁻¹*H*U*V)^4 := by
  have ht1 : 1 ≤ t := by linarith
  have ht : 0<t := by linarith
  have h2 : 2≤t := by linarith
  have rise {i j : ℕ} (h : i≤j) : t^i≤t^j := pow_le_pow_right₀ ht1 h
  have strong {i j : ℕ} (h : i<j) : t^i<t^j := pow_lt_pow_right₀ (by linarith) h
  have lows (j : ℕ) : t^j ≤ (⌊t^(j+1)⌋₊:ℝ) := by
    have fl := Nat.lt_floor_add_one (t^(j+1))
    have o : 1≤t^j := one_le_pow₀ ht1
    have two : t^j*2≤t^(j+1) := by
      rw [pow_succ]
      exact mul_le_mul_of_nonneg_left h2 (by positivity)
    linarith
  let H := ⌊t^252⌋₊
  let U := ⌊t^64⌋₊
  let V := ⌊t^128⌋₊
  have hH : t^251 ≤ (H:ℝ) := lows 251
  have hU : t^63 ≤ (U:ℝ) := lows 63
  have hV : t^127 ≤ (V:ℝ) := lows 127
  have HH : (H:ℝ) ≤ t^252 := Nat.floor_le (by positivity)
  have UU : (U:ℝ) ≤ t^64 := Nat.floor_le (by positivity)
  have VV : (V:ℝ) ≤ t^128 := Nat.floor_le (by positivity)
  have upos : (0:ℝ)<U := (pow_pos ht 63).trans_le hU
  have log : 1+Real.log U ≤ t^4 := by
    have l := Real.log_le_log upos UU
    rw [Real.log_pow] at l
    have l₂ : 1+Real.log U ≤ t^2 := by
      have ltlog := Real.log_le_sub_one_of_pos ht
      norm_num at l
      nlinarith only [l, ltlog, mul_nonneg ht.le (show 0≤t-64 by linarith)]
    exact l₂.trans (rise (by decide))
  have Lpos : 0≤1+Real.log U := by
    have uone : (1:ℝ) ≤ U := (one_le_pow₀ ht1).trans hU
    linarith [Real.log_nonneg uone]
  have sqrt : Real.sqrt p=t^256 := by
    rw [scale,show t^512=(t^256)^2 by ring,Real.sqrt_sq (by positivity)]
  have uv : (U:ℝ)*V≤t^192 := by
    calc
      _ ≤ t^64*t^128 := mul_le_mul UU VV (by positivity) (by positivity)
      _ = _ := by ring
  have hu : (H:ℝ)*U≤t^316 := by
    calc
      _ ≤ t^252*t^64 := mul_le_mul HH UU (by positivity) (by positivity)
      _ = _ := by ring
  have δh : t^250 ≤ t⁻¹*(H:ℝ) := by
    calc
      _ = t⁻¹*t^251 := by rw [show t^251=t*t^250 by ring,←mul_assoc,inv_mul_cancel₀ ht.ne',one_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_left hH (inv_nonneg.mpr ht.le)
  refine ⟨H,U,V,by exact_mod_cast (pow_pos ht 251).trans_le hH,by exact_mod_cast upos,
    by exact_mod_cast (pow_pos ht 127).trans_le hV,?_,?_,?_,?_,HH,?_,?_⟩
  · exact_mod_cast UU.trans_lt (scale.symm ▸ strong (by decide : 64<512))
  · exact_mod_cast VV.trans_lt (scale.symm ▸ strong (by decide : 128<512))
  · have s : 2*((U:ℝ)*H) ≤ t^317 := by
      rw [mul_comm (U:ℝ),show t^317=t*t^316 by ring]
      exact mul_le_mul h2 hu (by positivity) ht.le
    exact_mod_cast s.trans_lt (scale.symm ▸ strong (by decide : 317<512))
  · exact_mod_cast uv.trans ((rise (by decide : 192≤251)).trans hH)
  · calc
      _ ≤ t*t^192 := mul_le_mul h2 uv (by positivity) ht.le
      _ = t^193 := by ring
      _ ≤ _ := (rise (by decide : 193≤250)).trans δh
  · have s1 : ((H:ℝ)*U)^2 ≤ t^632 := by
      calc
        _ ≤ (t^316)^2 := pow_le_pow_left₀ (by positivity) hu _
        _ = _ := by ring
    have hl : (H:ℝ)*(1+Real.log U) ≤ t^256 := by
      calc
        _ ≤ t^252*t^4 := mul_le_mul HH log Lpos (by positivity)
        _ = _ := by ring
    have first : (H:ℝ)*(1+Real.log U)+U ≤ t^257 := by
      calc
        _ ≤ t^256+t^256 := add_le_add hl (UU.trans (rise (by decide)))
        _ = 2*t^256 := by ring
        _ ≤ t*t^256 := mul_le_mul_of_nonneg_right h2 (by positivity)
        _ = _ := by ring
    have second : (U:ℝ)*(1+Real.log U) ≤ t^68 := by
      calc
        _ ≤ t^64*t^4 := mul_le_mul UU log Lpos (by positivity)
        _ = _ := by ring
    have s2 : ((H:ℝ)*(1+Real.log U)+U)*((U:ℝ)*(1+Real.log U)) ≤ t^325 := by
      calc
        _ ≤ t^257*t^68 := mul_le_mul first second (by positivity) (by positivity)
        _ = _ := by ring
    have v2 : (V:ℝ)^2≤(t^128)^2 := pow_le_pow_left₀ (by positivity) VV _
    have v4 : (V:ℝ)^4≤(t^128)^4 := pow_le_pow_left₀ (by positivity) VV _
    have a : (V:ℝ)^2*16*p≤t^769 := by
      rw [scale]
      calc
        _ ≤ ((t^128)^2*t)*t^512 := by gcongr; linarith
        _ = _ := by ring
    have b : (V:ℝ)^4*C*Real.sqrt p≤t^769 := by
      rw [sqrt]
      calc
        _ ≤ ((t^128)^4*t)*t^256 := by gcongr
        _ = _ := by ring
    have s3 : (V:ℝ)^2*16*p+(V:ℝ)^4*C*Real.sqrt p≤t^770 := by
      calc
        _ ≤ t^769+t^769 := add_le_add a b
        _ = 2*t^769 := by ring
        _ ≤ t*t^769 := mul_le_mul_of_nonneg_right h2 (by positivity)
        _ = _ := by ring
    have bot : t^440≤t⁻¹*(H:ℝ)*U*V := by
      calc
        _ = t^250*t^63*t^127 := by ring
        _ ≤ (t⁻¹*(H:ℝ)*U)*V := by gcongr
    calc
      _ ≤ t^632*t^325*t^770 := by gcongr
      _ = t^1727 := by ring
      _ ≤ t^1760 := rise (by decide)
      _ = (t^440)^4 := by ring
      _ ≤ _ := pow_le_pow_left₀ (by positivity) bot _
end OMA.E1140

/- Reduction of the discriminant 8p character to a translate of the Legendre character
on each odd residue class modulo 8. The reciprocity calculation follows plby/lean-proofs,
Erdos1140Analytic, commit 8822f7ddef30fadbd92e1c6ab4ed897af356af5e (Apache-2.0). -/
namespace OMA.E1140

theorem odd_progression {p a : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (χ : DirichletCharacter ℂ (8*p))
    (attached : ∀ n : ℕ, χ n = ((if n.Coprime (8*p) then jacobiSym ((2*p:ℕ):ℤ) n else 0 : ℤ):ℂ))
    (ha : Odd a) (ha8 : a < 8) :
    ∃ (w : ℂ) (t : ℕ), ‖w‖ ≤ 1 ∧ ∀ i : ℕ,
      χ (8*i+a : ℕ) = w * ((quadraticChar (ZMod p) ((t+i:ℕ):ZMod p) : ℤ):ℂ) := by
  have hp : p.Prime := Fact.out
  let d : ℤ := jacobiSym 2 a * (-1)^(p/2*(a/2))
  have raw (i : ℕ) : χ (8*i+a:ℕ) =
      (d : ℂ) * ((quadraticChar (ZMod p) ((8*i+a:ℕ) : ZMod p) : ℤ):ℂ) := by
    let k := 8*i+a
    have ko : Odd k := Even.add_odd (by exact ⟨4*i,by ring⟩) ha
    have km : k%8=a := by dsimp [k]; omega
    have cp8 : k.Coprime 8 := by
      rw [show 8=2^3 by decide,Nat.coprime_pow_right_iff (by decide : 0<3)]
      exact Nat.coprime_two_right.mpr ko
    change χ (k:ℕ)=_
    rw [attached]
    by_cases c : k.Coprime (8*p)
    · rw [if_pos c]
      have j2 : jacobiSym 2 k = jacobiSym 2 a := by
        calc
          _ = jacobiSym 2 (k%(4*2)) := jacobiSym.mod_right' 2 ko
          _ = _ := by norm_num [km]
      have half : k/2=4*i+a/2 := by dsimp [k]; omega
      have sign : (-1:ℤ)^(p/2*(k/2))=(-1:ℤ)^(p/2*(a/2)) := by
        rw [half,Nat.mul_add,pow_add]
        have e : Even (p/2*(4*i)) := ⟨p/2*(2*i),by ring⟩
        rw [e.neg_one_pow,one_mul]
      have qr := jacobiSym.quadratic_reciprocity (a:=p) (b:=k) (hp.odd_of_ne_two hp2) ko
      have leg : jacobiSym (k:ℤ) p = quadraticChar (ZMod p) (k:ZMod p) := by
        rw [← jacobiSym.legendreSym.to_jacobiSym]; simp [legendreSym]
      change ((jacobiSym ((2*p:ℕ):ℤ) k:ℤ):ℂ) = (d:ℂ)*((quadraticChar (ZMod p) (k:ZMod p):ℤ):ℂ)
      rw [show ((2*p:ℕ):ℤ)=2*(p:ℤ) by norm_num,jacobiSym.mul_left,j2,qr,sign,leg]
      dsimp [d]
      push_cast
      ring
    · rw [if_neg c]
      have div : p ∣ k := by
        by_contra nd
        exact c (Nat.coprime_mul_iff_right.mpr ⟨cp8,(hp.coprime_iff_not_dvd.mpr nd).symm⟩)
      have kz : (k:ZMod p)=0 := (ZMod.natCast_eq_zero_iff k p).mpr div
      change ((0:ℤ):ℂ) = (d:ℂ)*((quadraticChar (ZMod p) (k:ZMod p):ℤ):ℂ)
      simp [kz]
  have cop8 : Nat.Coprime 8 p := by
    rw [show 8=2^3 by decide,Nat.coprime_pow_left_iff (by decide : 0<3)]
    exact (Nat.coprime_two_right.mpr (hp.odd_of_ne_two hp2)).symm
  have eight : (8 : ZMod p) ≠ 0 := (ZMod.isUnit_iff_coprime 8 p |>.mpr cop8).ne_zero
  let t := ((8:ZMod p)⁻¹*a).val
  let u : ℤ := quadraticChar (ZMod p) 8
  refine ⟨(d:ℂ)*(u:ℂ),t,?_,?_⟩
  · have hd : ‖(d:ℂ)‖ ≤ 1 := by
      rcases jacobiSym.trichotomy 2 a with h|h|h <;> simp [d,h,norm_pow]
    have hu : ‖(u:ℂ)‖ ≤ 1 := by
      rcases quadraticChar_isQuadratic (ZMod p) 8 with h|h|h <;> simp [u,h]
    rw [norm_mul]
    exact (mul_le_mul hd hu (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
  · intro i
    have shift : ((8*i+a:ℕ):ZMod p) = 8*((t+i:ℕ):ZMod p) := by
      simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,t,ZMod.natCast_zmod_val]
      rw [mul_add,←mul_assoc,mul_inv_cancel₀ eight,one_mul,add_comm]
    rw [raw,shift,map_mul,Int.cast_mul]
    simp [u,mul_assoc]

end OMA.E1140

/- Completion of a prefix by consecutive blocks of a single fixed length. -/
namespace OMA.E1140

theorem prefix_of_equal_blocks {E : Type*} [SeminormedAddCommGroup E] (f : ℕ → E)
    {L : ℕ} (hL : 0 < L) {δ : ℝ} (hδ : 0 ≤ δ) (hf : ∀ n, ‖f n‖ ≤ 1)
    (block : ∀ k : ℕ, ‖∑ i ∈ Finset.range L, f (k*L+i+1)‖ ≤ δ*(L:ℝ))
    (m : ℕ) : ‖∑ i ∈ Finset.range m, f (i+1)‖ ≤ δ*(m:ℝ)+(L:ℝ) := by
  have blocks (k : ℕ) : ‖∑ i ∈ Finset.range (k*L), f (i+1)‖ ≤ δ*((k*L:ℕ):ℝ) := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Nat.succ_mul,Finset.sum_range_add,Nat.cast_add,mul_add]
      exact (norm_add_le _ _).trans (add_le_add ih (block k))
  let k := m/L
  let r := m%L
  have eqm : k*L+r=m := Nat.div_add_mod' _ _
  have rl : r≤L := (Nat.mod_lt _ hL).le
  have tail : ‖∑ i ∈ Finset.range r, f (k*L+i+1)‖ ≤ (r:ℝ) := by
    calc
      _ ≤ ∑ i ∈ Finset.range r, ‖f (k*L+i+1)‖ := norm_sum_le _ _
      _ ≤ ∑ _ ∈ Finset.range r, (1:ℝ) := Finset.sum_le_sum fun i _ => hf _
      _ = _ := by simp
  rw [←eqm,Finset.sum_range_add]
  exact (norm_add_le _ _).trans (add_le_add ((blocks k).trans
    (mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.le_add_right (k*L) r) hδ))
    (tail.trans (by exact_mod_cast rl)))

/-- Separate an interval into its eight residue classes. -/
theorem by_eight {E : Type*} [AddCommMonoid E] (f : ℕ → E) (H : ℕ) :
    (∑ k ∈ Finset.range (8*H), f k) =
        ∑ a ∈ Finset.range 8, ∑ i ∈ Finset.range H, f (8*i+a) := by
  induction H with
  | zero => simp
  | succ H ih =>
    rw [Nat.mul_succ,Finset.sum_range_add,ih]
    simp_rw [Finset.sum_range_succ (n:=H)]
    rw [Finset.sum_add_distrib]

end OMA.E1140

/- Lifting uniform Legendre block cancellation to the character of discriminant 8p. -/
namespace OMA.E1140
open Pollack17.Burgess

theorem attached_of_prime_block {p H : ℕ} [Fact p.Prime] (hp2 : p≠2) (hH : 0<H)
    {δ : ℝ} (hd : 0≤δ) (χ : DirichletCharacter ℂ (8*p))
    (attached : ∀ n : ℕ, χ n = ((if n.Coprime (8*p) then jacobiSym ((2*p:ℕ):ℤ) n else 0 : ℤ):ℂ))
    (prime : ∀ M : ℕ, |∑ j ∈ Finset.range H, qchar ((M+j:ℕ):ZMod p)| ≤ δ*H)
    (m : ℕ) : ‖∑ j ∈ Finset.range m, χ (j+1:ℕ)‖ ≤ δ*m+8*(H:ℝ) := by
  have residue (k a : ℕ) (ha : a<8) :
      ‖∑ i ∈ Finset.range H, χ (k*(8*H)+(8*i+a)+1:ℕ)‖ ≤ δ*(H:ℝ) := by
    by_cases odd : Odd (a+1)
    · have aa : a+1<8 := by rcases odd with ⟨v,hv⟩; omega
      obtain ⟨w,t,hw,tw⟩ := odd_progression hp2 χ attached odd aa
      have eq : (∑ i ∈ Finset.range H, χ (k*(8*H)+(8*i+a)+1:ℕ)) =
          w*((∑ i ∈ Finset.range H, qchar ((t+k*H+i:ℕ):ZMod p)):ℝ) := by
        rw [Complex.ofReal_sum,Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [show k*(8*H)+(8*i+a)+1=8*(k*H+i)+(a+1) by ring, tw, ←Nat.add_assoc]
        simp only [qchar,Complex.ofReal_intCast]
      rw [eq,norm_mul,Complex.norm_real,Real.norm_eq_abs]
      exact (mul_le_mul_of_nonneg_right hw (abs_nonneg _)).trans (by simpa using prime (t+k*H))
    · have ev : Even (a+1) := Nat.not_odd_iff_even.mp odd
      have ez (i : ℕ) : χ (k*(8*H)+(8*i+a)+1:ℕ)=0 := by
        let n := k*(8*H)+(8*i+a)+1
        have e : Even n := by obtain ⟨v,hv⟩ := ev; exact ⟨k*(4*H)+4*i+v,by dsimp [n]; ring_nf at hv ⊢; omega⟩
        have notcop : ¬ n.Coprime (8*p) := by
          intro h
          have ho := Nat.coprime_two_right.mp (h.coprime_dvd_right
            (show 2∣8*p by exact ⟨4*p,by ring⟩))
          exact (Nat.not_even_iff_odd.mpr ho) e
        simpa only [if_neg notcop,Int.cast_zero] using attached n
      simp only [ez,Finset.sum_const_zero,norm_zero]
      positivity
  have blocks (k : ℕ) : ‖∑ i ∈ Finset.range (8*H), χ (k*(8*H)+i+1:ℕ)‖ ≤ δ*((8*H:ℕ):ℝ) := by
    rw [by_eight (fun i => χ (k*(8*H)+i+1:ℕ)) H]
    calc
      _ ≤ _ := norm_sum_le _ _
      _ ≤ ∑ _ ∈ Finset.range 8, δ*(H:ℝ) := Finset.sum_le_sum (fun a ha => residue k a (Finset.mem_range.mp ha))
      _ = _ := by simp; ring
  simpa using prefix_of_equal_blocks (fun n : ℕ => χ n) (Nat.mul_pos (by decide) hH) hd
    (fun n => χ.norm_le_one n) blocks m

end OMA.E1140

/- Power-saving prefix estimate for quadratic characters of discriminant 8p. -/
open Filter
namespace OMA.E1140

theorem attached_prefixes :
    ∀ᶠ p : ℕ in atTop, ∀ (_hp : p.Prime) [NeZero (8*p)] (χ : DirichletCharacter ℂ (8*p)),
    (∀ n : ℕ, χ n = ((if n.Coprime (8*p) then jacobiSym ((2*p:ℕ):ℤ) n else 0 : ℤ):ℂ)) →
    ∀ m : ℕ, ‖∑ i ∈ Finset.range m, χ (i+1:ℕ)‖ ≤
      8*(p:ℝ)^(-(1/512:ℝ))*m + 48*(p:ℝ)^(63/128:ℝ) := by
  let C : ℝ := 256*(Pollack17.Stepanov.simpleRootConstant 4 : ℝ)
  have go := (tendsto_rpow_atTop (show 0<(1/512:ℝ) by norm_num)).comp
    (tendsto_natCast_atTop_atTop (R:=ℝ))
  filter_upwards [go.eventually_ge_atTop (max 128 C),eventually_ge_atTop 3] with p grow p3
  intro hp _ χ att m
  let : Fact p.Prime := ⟨hp⟩
  let t := (p:ℝ)^(1/512:ℝ)
  change max 128 C ≤ t at grow
  have hp0 : (0:ℝ)≤p := Nat.cast_nonneg _
  have growpow (n : ℕ) : t^n = (p:ℝ)^((1/512:ℝ)*n) :=
    (Real.rpow_mul_natCast hp0 _ n).symm
  have s : (p:ℝ)=t^512 := by rw [growpow]; norm_num
  have h252 : t^252 = (p:ℝ)^(63/128:ℝ) := by rw [growpow]; norm_num
  have neg : t⁻¹ = (p:ℝ)^(-(1/512:ℝ)) := (Real.rpow_neg hp0 _).symm
  obtain ⟨H,U,V,hH,hU,hV,hUp,_hVp,small,fits,HH,boundary,budget⟩ :=
    scale_budget ((le_max_left _ _).trans grow) (show 0≤C by dsimp [C];positivity)
      ((le_max_right _ _).trans grow) p s
  have td : 0≤t⁻¹ := inv_nonneg.mpr (Real.rpow_nonneg hp0 _)
  have blocks := public_moment_block hH hU hV hUp small fits td boundary budget
  have hprefix := attached_of_prime_block (by omega : p≠2) hH
    (mul_nonneg (by norm_num : (0:ℝ)≤2) td) χ att blocks m
  calc
    _ ≤ (2*t⁻¹)*(m:ℝ)+8*(H:ℝ) := hprefix
    _ ≤ (8*t⁻¹)*(m:ℝ)+48*t^252 := by gcongr <;> norm_num
    _ = _ := by rw [neg,h252]

end OMA.E1140

/-
Siegel's lower bound for quadratic L-values in Pollack's Theorem 1.3.
Adapted from the Pollack17 development imported by Boris Alexeev in plby/lean-proofs,
whose enclosing formalization credits GPT-5.4 Pro and Yuta Oriike,
commit 8822f7ddef30fadbd92e1c6ab4ed897af356af5e, and the BoundedGaps
contributors, frenzymath/FormalPantheon (Apache License 2.0), commit ffbb65c21afc8a36ace67720f1b0df1c63d26bd1.
-/

/- ## Primitive Gauss sums on `ZMod`

Source module `BoundedGaps.BombieriVinogradov.Analytic.PrimitiveGaussSum`. -/

noncomputable section

namespace BoundedGaps.Maynard

open scoped BigOperators

open AddChar Finset

private theorem PrimitiveGaussSum_sum_star_mul_dft {q : ℕ} [NeZero q] (f : ZMod q → ℂ) :
    (∑ k : ZMod q, star (ZMod.dft f k) * ZMod.dft f k) =
      (q : ℂ) * ∑ j : ZMod q, star (f j) * f j := by
  classical
  have hstar (x : ZMod q) :
      star (ZMod.stdAddChar x) = ZMod.stdAddChar (-x) := by
    simpa only [Complex.star_def] using
      (AddChar.map_neg_eq_conj ZMod.stdAddChar x).symm
  simp only [ZMod.dft_apply, smul_eq_mul, star_sum, star_mul]
  simp_rw [hstar]
  simp only [neg_neg]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_comm]
  have hsummand (i k : ZMod q) :
      star (f j) * ZMod.stdAddChar (j * k) *
          (ZMod.stdAddChar (-(i * k)) * f i) =
        (star (f j) * f i) * ZMod.stdAddChar (k * (j - i)) := by
    calc
      _ = (star (f j) * f i) *
          (ZMod.stdAddChar (j * k) * ZMod.stdAddChar (-(i * k))) := by ring
      _ = (star (f j) * f i) *
          ZMod.stdAddChar (j * k + -(i * k)) := by rw [map_add_eq_mul]
      _ = _ := by
        rw [show j * k + -(i * k) = k * (j - i) by ring]
  simp_rw [hsummand, ← Finset.mul_sum]
  simp_rw [AddChar.sum_mulShift (ψ := ZMod.stdAddChar) _
    (ZMod.isPrimitive_stdAddChar q)]
  simp only [sub_eq_zero, ZMod.card, Nat.cast_ite, Nat.cast_zero,
    mul_ite, mul_zero]
  simp [eq_comm]
  ring

theorem sum_norm_sq_dft {q : ℕ} [NeZero q] (f : ZMod q → ℂ) :
    (∑ k : ZMod q, ‖ZMod.dft f k‖ ^ 2) =
      (q : ℝ) * ∑ j : ZMod q, ‖f j‖ ^ 2 := by
  have h := PrimitiveGaussSum_sum_star_mul_dft f
  rw [Complex.star_def] at h
  simp_rw [← Complex.normSq_eq_conj_mul_self,
    Complex.normSq_eq_norm_sq] at h
  exact_mod_cast h

theorem sum_norm_sq_dirichletCharacter {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) :
    (∑ j : ZMod q, ‖χ j‖ ^ 2) = (Nat.totient q : ℝ) := by
  classical
  calc
    (∑ j : ZMod q, ‖χ j‖ ^ 2) =
        ∑ j : ZMod q, if IsUnit j then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro j _
      by_cases hj : IsUnit j
      · have hnorm : ‖χ j‖ = 1 := by
          rw [← hj.unit_spec]
          exact χ.unit_norm_eq_one hj.unit
        simp [hj, hnorm]
      · simp [hj, χ.map_nonunit hj]
    _ = (((Finset.univ : Finset (ZMod q)).filter IsUnit).card : ℝ) := by
      simp
    _ = ((Fintype.card (ZMod q)ˣ : ℕ) : ℝ) := by
      congr 1
      calc
        ((Finset.univ : Finset (ZMod q)).filter IsUnit).card =
            (Finset.univ.map ⟨((↑) : (ZMod q)ˣ → ZMod q),
              Units.val_injective⟩).card := by
          congr 1
          ext j
          simp [IsUnit]
        _ = Fintype.card (ZMod q)ˣ := by simp
    _ = (Nat.totient q : ℝ) := by rw [ZMod.card_units_eq_totient]

theorem norm_gaussSum_stdAddChar_of_isPrimitive {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) :
    ‖gaussSum χ ZMod.stdAddChar‖ = Real.sqrt q := by
  have hmassNeg :
      (∑ k : ZMod q, ‖χ⁻¹ (-k)‖ ^ 2) = (Nat.totient q : ℝ) := by
    calc
      _ = ∑ k : ZMod q, ‖χ⁻¹ k‖ ^ 2 :=
        Equiv.sum_comp (Equiv.neg (ZMod q)) (fun k ↦ ‖χ⁻¹ k‖ ^ 2)
      _ = (Nat.totient q : ℝ) := sum_norm_sq_dirichletCharacter χ⁻¹
  have hparseval := sum_norm_sq_dft (f := fun j ↦ χ j)
  simp_rw [hχ.fourierTransform_eq_inv_mul_gaussSum, norm_mul, mul_pow] at hparseval
  rw [← Finset.sum_mul, hmassNeg,
    sum_norm_sq_dirichletCharacter χ] at hparseval
  have htotient : (Nat.totient q : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.totient_pos.mpr
      (Nat.pos_of_ne_zero (NeZero.ne q))))
  have hsquare : ‖gaussSum χ ZMod.stdAddChar‖ ^ 2 = (q : ℝ) := by
    apply mul_left_cancel₀ htotient
    calc
      (Nat.totient q : ℝ) * ‖gaussSum χ ZMod.stdAddChar‖ ^ 2 =
          (q : ℝ) * Nat.totient q := hparseval
      _ = (Nat.totient q : ℝ) * q := by ring
  nlinarith [Real.sq_sqrt (Nat.cast_nonneg q),
    norm_nonneg (gaussSum χ ZMod.stdAddChar), Real.sqrt_nonneg (q : ℝ)]

theorem primitive_fourier_expansion {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (n : ZMod q) :
    (∑ a : ZMod q, χ⁻¹ a * ZMod.stdAddChar (a * n)) =
      χ n * gaussSum χ⁻¹ ZMod.stdAddChar := by
  have hχinv : χ⁻¹.IsPrimitive := by
    rw [DirichletCharacter.IsPrimitive, DirichletCharacter.conductor_inv]
    exact hχ
  have hfourier := hχinv.fourierTransform_eq_inv_mul_gaussSum (-n)
  simpa only [ZMod.dft_apply, smul_eq_mul, mul_neg, neg_neg, inv_inv,
    mul_comm] using hfourier

theorem primitive_fourier_expansion_div {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (n : ZMod q) :
    χ n = (∑ a : ZMod q, χ⁻¹ a * ZMod.stdAddChar (a * n)) /
      gaussSum χ⁻¹ ZMod.stdAddChar := by
  have hχinv : χ⁻¹.IsPrimitive := by
    rw [DirichletCharacter.IsPrimitive, DirichletCharacter.conductor_inv]
    exact hχ
  have hnorm := norm_gaussSum_stdAddChar_of_isPrimitive χ⁻¹ hχinv
  have hgauss : gaussSum χ⁻¹ ZMod.stdAddChar ≠ 0 := by
    intro hz
    rw [hz, norm_zero] at hnorm
    have hqpos : (0 : ℝ) < q := by
      exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
    nlinarith [Real.sqrt_pos.2 hqpos]
  rw [primitive_fourier_expansion χ hχ n,
    mul_div_cancel_right₀ _ hgauss]

end BoundedGaps.Maynard

end


/- ## Abel continuation for nonprincipal Dirichlet L-functions

Source module `BoundedGaps.BombieriVinogradov.Analytic.DirichletLFunctionAbelContinuation`. -/

noncomputable section

open Asymptotics Complex Filter MeasureTheory Set

open scoped BigOperators Real Topology

namespace BoundedGaps.Maynard

private noncomputable def DirichletLFunctionAbelContinuation_characterPrefixTail
    {q : ℕ} (chi : DirichletCharacter ℂ q) (y : ℝ) : ℂ :=
  (Ioi (1 : ℝ)).indicator
    (fun u ↦ ∑ k ∈ Finset.Icc 1 ⌊u⌋₊, chi (k : ZMod q)) y

private lemma DirichletLFunctionAbelContinuation_measurable_characterPrefixTail
    {q : ℕ} (chi : DirichletCharacter ℂ q) :
    Measurable (DirichletLFunctionAbelContinuation_characterPrefixTail chi) := by
  apply Measurable.indicator _ measurableSet_Ioi
  exact
    (measurable_of_countable
      (fun n : ℕ ↦ ∑ k ∈ Finset.Icc 1 n, chi (k : ZMod q))).comp
      Nat.measurable_floor

private lemma DirichletLFunctionAbelContinuation_norm_characterPrefixTail_le
    {q : ℕ} (chi : DirichletCharacter ℂ q) (C : ℝ) (hC : 0 ≤ C)
    (hprefix : ∀ n : ℕ,
      ‖∑ k ∈ Finset.Icc 1 n, chi (k : ZMod q)‖ ≤ C)
    (y : ℝ) :
    ‖DirichletLFunctionAbelContinuation_characterPrefixTail chi y‖ ≤ C := by
  by_cases hy : y ∈ Ioi (1 : ℝ)
  · rw [DirichletLFunctionAbelContinuation_characterPrefixTail, indicator_of_mem hy]
    exact hprefix ⌊y⌋₊
  · rw [DirichletLFunctionAbelContinuation_characterPrefixTail, indicator_of_notMem hy, norm_zero]
    exact hC

private lemma DirichletLFunctionAbelContinuation_locallyIntegrable_characterPrefixTail
    {q : ℕ} (chi : DirichletCharacter ℂ q) (C : ℝ) (hC : 0 ≤ C)
    (hprefix : ∀ n : ℕ,
      ‖∑ k ∈ Finset.Icc 1 n, chi (k : ZMod q)‖ ≤ C) :
    LocallyIntegrableOn (DirichletLFunctionAbelContinuation_characterPrefixTail chi) (Ioi 0) := by
  have hnormScale : ‖((C : ℝ) : ℂ)‖ = C := by
    rw [norm_real, Real.norm_eq_abs, abs_of_nonneg hC]
  refine ((locallyIntegrable_const ((C : ℝ) : ℂ)).locallyIntegrableOn
      (Ioi 0)).mono
      (DirichletLFunctionAbelContinuation_measurable_characterPrefixTail chi).aestronglyMeasurable ?_
  filter_upwards with y
  rw [hnormScale]
  exact DirichletLFunctionAbelContinuation_norm_characterPrefixTail_le chi C hC hprefix y

private lemma DirichletLFunctionAbelContinuation_characterPrefixTail_isBigO_atTop
    {q : ℕ} (chi : DirichletCharacter ℂ q) (C : ℝ) (hC : 0 ≤ C)
    (hprefix : ∀ n : ℕ,
      ‖∑ k ∈ Finset.Icc 1 n, chi (k : ZMod q)‖ ≤ C) :
    DirichletLFunctionAbelContinuation_characterPrefixTail chi =O[atTop] (fun y : ℝ ↦ y ^ (-(0 : ℝ))) := by
  refine isBigO_iff.mpr ⟨C, Eventually.of_forall fun y ↦ ?_⟩
  simpa using DirichletLFunctionAbelContinuation_norm_characterPrefixTail_le chi C hC hprefix y

private lemma DirichletLFunctionAbelContinuation_characterPrefixTail_isBigO_nhdsGT_zero
    {q : ℕ} (chi : DirichletCharacter ℂ q) (b : ℝ) :
    DirichletLFunctionAbelContinuation_characterPrefixTail chi =O[𝓝[>] 0] (fun y : ℝ ↦ y ^ (-b)) := by
  have hlt : ∀ᶠ y : ℝ in 𝓝[>] 0, y < 1 :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds (Iio_mem_nhds zero_lt_one)
  refine isBigO_iff.mpr ⟨1, ?_⟩
  filter_upwards [hlt] with y hy
  simp [DirichletLFunctionAbelContinuation_characterPrefixTail, not_lt.mpr hy.le]

private lemma DirichletLFunctionAbelContinuation_differentiableAt_characterPrefixMellin_neg
    {q : ℕ} (chi : DirichletCharacter ℂ q) (C : ℝ) (hC : 0 ≤ C)
    (hprefix : ∀ n : ℕ,
      ‖∑ k ∈ Finset.Icc 1 n, chi (k : ZMod q)‖ ≤ C)
    {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ (fun w ↦ mellin (DirichletLFunctionAbelContinuation_characterPrefixTail chi) (-w)) s := by
  have hm : DifferentiableAt ℂ (mellin (DirichletLFunctionAbelContinuation_characterPrefixTail chi)) (-s) := by
    refine mellin_differentiableAt_of_isBigO_rpow
      (a := 0) (b := (-s).re - 1)
      (DirichletLFunctionAbelContinuation_locallyIntegrable_characterPrefixTail chi C hC hprefix)
      (DirichletLFunctionAbelContinuation_characterPrefixTail_isBigO_atTop chi C hC hprefix) ?_
      (DirichletLFunctionAbelContinuation_characterPrefixTail_isBigO_nhdsGT_zero chi ((-s).re - 1)) ?_
    · simpa using (neg_lt_zero.mpr hs)
    · linarith
  exact hm.comp s differentiableAt_id.neg

private lemma DirichletLFunctionAbelContinuation_characterPrefixMellin_neg_eq_integral
    {q : ℕ} (chi : DirichletCharacter ℂ q) (s : ℂ) :
    mellin (DirichletLFunctionAbelContinuation_characterPrefixTail chi) (-s) =
      ∫ y in Ioi (1 : ℝ),
        (∑ k ∈ Finset.Icc 1 ⌊y⌋₊, chi (k : ZMod q)) *
          (y : ℂ) ^ (-(s + 1)) := by
  rw [mellin]
  simp only [smul_eq_mul]
  calc
    (∫ y : ℝ in Ioi 0,
        (y : ℂ) ^ (-s - 1) * DirichletLFunctionAbelContinuation_characterPrefixTail chi y) =
        ∫ y : ℝ in Ioi 0, (Ioi (1 : ℝ)).indicator
          (fun u ↦ (u : ℂ) ^ (-s - 1) *
            ∑ k ∈ Finset.Icc 1 ⌊u⌋₊, chi (k : ZMod q)) y := by
      refine setIntegral_congr_fun measurableSet_Ioi fun y _ ↦ ?_
      by_cases hy : y ∈ Ioi (1 : ℝ)
      · simp [DirichletLFunctionAbelContinuation_characterPrefixTail, hy]
      · simp [DirichletLFunctionAbelContinuation_characterPrefixTail, hy]
    _ = ∫ y : ℝ in Ioi 0 ∩ Ioi 1,
        (y : ℂ) ^ (-s - 1) *
          (∑ k ∈ Finset.Icc 1 ⌊y⌋₊, chi (k : ZMod q)) := by
      rw [setIntegral_indicator measurableSet_Ioi]
    _ = ∫ y : ℝ in Ioi 1,
        (y : ℂ) ^ (-s - 1) *
          (∑ k ∈ Finset.Icc 1 ⌊y⌋₊, chi (k : ZMod q)) := by
      rw [Ioi_inter_Ioi, max_eq_right zero_le_one]
    _ = ∫ y : ℝ in Ioi 1,
        (∑ k ∈ Finset.Icc 1 ⌊y⌋₊, chi (k : ZMod q)) *
          (y : ℂ) ^ (-(s + 1)) := by
      refine setIntegral_congr_fun measurableSet_Ioi fun y _ ↦ ?_
      rw [show -s - 1 = -(s + 1) by ring, mul_comm]

private lemma DirichletLFunctionAbelContinuation_characterPartialSums_isBigO_atTop
    {q : ℕ} (chi : DirichletCharacter ℂ q) (C : ℝ)
    (hprefix : ∀ n : ℕ,
      ‖∑ k ∈ Finset.Icc 1 n, chi (k : ZMod q)‖ ≤ C) :
    (fun n : ℕ ↦ ∑ k ∈ Finset.Icc 1 n, chi (k : ZMod q)) =O[atTop]
      (fun n : ℕ ↦ (n : ℝ) ^ (0 : ℝ)) := by
  refine isBigO_iff.mpr ⟨C, Eventually.of_forall fun n ↦ ?_⟩
  simpa using hprefix n

private lemma DirichletLFunctionAbelContinuation_LFunction_eq_characterPrefixMellin_of_one_lt_re
    {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (C : ℝ)
    (hprefix : ∀ n : ℕ,
      ‖∑ k ∈ Finset.Icc 1 n, chi (k : ZMod q)‖ ≤ C)
    {s : ℂ} (hs : 1 < s.re) :
    DirichletCharacter.LFunction chi s =
      s * mellin (DirichletLFunctionAbelContinuation_characterPrefixTail chi) (-s) := by
  calc
    DirichletCharacter.LFunction chi s = LSeries (chi ·) s :=
      DirichletCharacter.LFunction_eq_LSeries chi hs
    _ = s * ∫ y in Ioi (1 : ℝ),
        (∑ k ∈ Finset.Icc 1 ⌊y⌋₊, chi (k : ZMod q)) *
          (y : ℂ) ^ (-(s + 1)) :=
      LSeries_eq_mul_integral (chi ·) (r := 0) le_rfl (zero_lt_one.trans hs)
        (DirichletCharacter.LSeriesSummable_of_one_lt_re chi hs)
        (DirichletLFunctionAbelContinuation_characterPartialSums_isBigO_atTop chi C hprefix)
    _ = s * mellin (DirichletLFunctionAbelContinuation_characterPrefixTail chi) (-s) := by
      rw [DirichletLFunctionAbelContinuation_characterPrefixMellin_neg_eq_integral]

theorem LFunction_eq_abelIntegral_of_prefixBound
    {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1)
    (C : ℝ)
    (hprefix : ∀ n : ℕ,
      ‖∑ k ∈ Finset.Icc 1 n, chi (k : ZMod q)‖ ≤ C)
    (s : ℂ) (hs : 0 < s.re) :
    DirichletCharacter.LFunction chi s =
      s * ∫ y in Set.Ioi (1 : ℝ),
        (∑ k ∈ Finset.Icc 1 ⌊y⌋₊, chi (k : ZMod q)) *
          (y : ℂ) ^ (-(s + 1)) := by
  have hC : 0 ≤ C := by
    simpa using hprefix 0
  let U : Set ℂ := {w | 0 < w.re}
  have hUOpen : IsOpen U := isOpen_lt continuous_const continuous_re
  have hUPre : IsPreconnected U := (convex_halfSpace_re_gt 0).isPreconnected
  have hLeft :
      AnalyticOnNhd ℂ (DirichletCharacter.LFunction chi) U :=
    (DirichletCharacter.differentiable_LFunction hchi).differentiableOn.analyticOnNhd hUOpen
  have hRight : AnalyticOnNhd ℂ
      (fun w ↦ w * mellin (DirichletLFunctionAbelContinuation_characterPrefixTail chi) (-w)) U := by
    refine DifferentiableOn.analyticOnNhd (fun w hw ↦ ?_) hUOpen
    exact (differentiableAt_id.mul
      (DirichletLFunctionAbelContinuation_differentiableAt_characterPrefixMellin_neg chi C hC hprefix hw)).differentiableWithinAt
  have hEq : EqOn (DirichletCharacter.LFunction chi)
      (fun w ↦ w * mellin (DirichletLFunctionAbelContinuation_characterPrefixTail chi) (-w)) U := by
    refine hLeft.eqOn_of_preconnected_of_eventuallyEq hRight hUPre
      (show (2 : ℂ) ∈ U by simp [U]) ?_
    refine eventually_of_mem
      ((isOpen_lt continuous_const continuous_re).mem_nhds
        (show 1 < (2 : ℂ).re by norm_num)) ?_
    intro w hw
    exact DirichletLFunctionAbelContinuation_LFunction_eq_characterPrefixMellin_of_one_lt_re chi C hprefix hw
  rw [hEq hs]
  change s * mellin (DirichletLFunctionAbelContinuation_characterPrefixTail chi) (-s) = _
  rw [DirichletLFunctionAbelContinuation_characterPrefixMellin_neg_eq_integral]

end BoundedGaps.Maynard

end


/- ## Standard additive characters on translated integer intervals

Source module `BoundedGaps.BombieriVinogradov.Analytic.StandardAddCharInterval`. -/

noncomputable section

namespace BoundedGaps.Maynard

open scoped BigOperators

open AddChar Finset

private theorem StandardAddCharInterval_sum_Ioc_int_eq_sum_range_add_succ
    {A : Type*} [AddCommMonoid A] (f : ℤ → A) (M : ℤ) (N : ℕ) :
    (∑ m ∈ Finset.Ioc M (M + (N : ℤ)), f m) =
      ∑ n ∈ Finset.range N, f (M + (n + 1 : ℕ)) := by
  rw [Int.Ioc_eq_finset_map, Finset.sum_map]
  simp only [Function.Embedding.trans_apply, Nat.castEmbedding_apply,
    addLeftEmbedding_apply]
  congr 1
  · simp
  · funext n
    congr 1
    push_cast
    ring

private theorem StandardAddCharInterval_stdAddChar_mul_int_add_succ {q : ℕ} [NeZero q]
    (a : ZMod q) (M : ℤ) (n : ℕ) :
    ZMod.stdAddChar (a * ((M + ((n + 1 : ℕ) : ℤ) : ℤ) : ZMod q)) =
      ZMod.stdAddChar (a * ((M + 1 : ℤ) : ZMod q)) *
        ZMod.stdAddChar a ^ n := by
  rw [← AddChar.map_nsmul_eq_pow, ← AddChar.map_add_eq_mul]
  congr 1
  push_cast
  simp only [nsmul_eq_mul]
  ring

private theorem StandardAddCharInterval_stdAddChar_ne_one_of_ne_zero
    {q : ℕ} [NeZero q] {a : ZMod q} (ha : a ≠ 0) :
    ZMod.stdAddChar a ≠ 1 := by
  intro h
  apply ha
  apply ZMod.injective_stdAddChar
  simpa only [AddChar.map_zero_eq_one] using h

private theorem StandardAddCharInterval_norm_stdAddChar_sub_one_eq_two_mul_abs_sin
    {q : ℕ} [NeZero q] (a : ZMod q) :
    ‖ZMod.stdAddChar a - 1‖ =
      2 * |Real.sin (Real.pi * (a.val : ℝ) / (q : ℝ))| := by
  rw [← ZMod.natCast_zmod_val a]
  rw [show (a.val : ZMod q) = ((a.val : ℤ) : ZMod q) by simp,
    ZMod.stdAddChar_coe]
  simp only [Int.cast_natCast]
  rw [show 2 * (Real.pi : ℂ) * Complex.I * (a.val : ℂ) / (q : ℂ) =
      Complex.I * ((2 * Real.pi * (a.val : ℝ) / (q : ℝ) : ℝ) : ℂ) by
        push_cast
        ring]
  rw [Complex.norm_exp_I_mul_ofReal_sub_one]
  simp only [show (2 * Real.pi * (a.val : ℝ) / (q : ℝ)) / 2 =
    Real.pi * (a.val : ℝ) / (q : ℝ) by ring]
  rw [Real.norm_eq_abs, abs_mul]
  norm_num

theorem sum_stdAddChar_Ioc_eq_geometric
    {q : ℕ} [NeZero q] {a : ZMod q} (ha : a ≠ 0)
    (M : ℤ) (N : ℕ) :
    (∑ n ∈ Finset.Ioc M (M + (N : ℤ)),
      ZMod.stdAddChar (a * (n : ZMod q))) =
      ZMod.stdAddChar (a * ((M + 1 : ℤ) : ZMod q)) *
        ((1 - ZMod.stdAddChar (a * (N : ZMod q))) /
          (1 - ZMod.stdAddChar a)) := by
  rw [StandardAddCharInterval_sum_Ioc_int_eq_sum_range_add_succ]
  simp_rw [StandardAddCharInterval_stdAddChar_mul_int_add_succ]
  rw [← Finset.mul_sum, geom_sum_eq (StandardAddCharInterval_stdAddChar_ne_one_of_ne_zero ha)]
  have hpow : ZMod.stdAddChar (a * (N : ZMod q)) =
      ZMod.stdAddChar a ^ N := by
    rw [show a * (N : ZMod q) = N • a by ring,
      AddChar.map_nsmul_eq_pow]
  rw [hpow]
  congr 1
  rw [div_eq_mul_inv, div_eq_mul_inv,
    show ZMod.stdAddChar a - 1 = -(1 - ZMod.stdAddChar a) by ring,
    inv_neg]
  ring

theorem norm_sum_stdAddChar_Ioc_le_inv_sin
    {q : ℕ} [NeZero q] {a : ZMod q} (ha : a ≠ 0)
    (M : ℤ) (N : ℕ) :
    ‖∑ n ∈ Finset.Ioc M (M + (N : ℤ)),
      ZMod.stdAddChar (a * (n : ZMod q))‖ ≤
      (Real.sin (Real.pi * (a.val : ℝ) / (q : ℝ)))⁻¹ := by
  have hqpos : (0 : ℝ) < q := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have havalpos : (0 : ℝ) < a.val := by
    exact_mod_cast Nat.pos_of_ne_zero ((ZMod.val_ne_zero a).mpr ha)
  have hanglepos : 0 < Real.pi * (a.val : ℝ) / (q : ℝ) :=
    div_pos (mul_pos Real.pi_pos havalpos) hqpos
  have hanglelt : Real.pi * (a.val : ℝ) / (q : ℝ) < Real.pi := by
    rw [div_lt_iff₀ hqpos]
    have havallt : (a.val : ℝ) < q := by exact_mod_cast a.val_lt
    nlinarith [Real.pi_pos]
  have hsin : 0 < Real.sin (Real.pi * (a.val : ℝ) / (q : ℝ)) :=
    Real.sin_pos_of_pos_of_lt_pi hanglepos hanglelt
  have hnum : ‖1 - ZMod.stdAddChar (a * (N : ZMod q))‖ ≤ 2 := by
    calc
      _ ≤ ‖(1 : ℂ)‖ + ‖ZMod.stdAddChar (a * (N : ZMod q))‖ :=
        norm_sub_le _ _
      _ = 2 := by rw [AddChar.norm_apply]; norm_num
  have hdenom : ‖1 - ZMod.stdAddChar a‖ =
      2 * Real.sin (Real.pi * (a.val : ℝ) / (q : ℝ)) := by
    rw [show (1 : ℂ) - ZMod.stdAddChar a =
      -(ZMod.stdAddChar a - 1) by ring, norm_neg,
      StandardAddCharInterval_norm_stdAddChar_sub_one_eq_two_mul_abs_sin,
      abs_of_pos hsin]
  rw [sum_stdAddChar_Ioc_eq_geometric ha, norm_mul,
    AddChar.norm_apply, one_mul, norm_div, hdenom]
  calc
    ‖1 - ZMod.stdAddChar (a * (N : ZMod q))‖ /
        (2 * Real.sin (Real.pi * (a.val : ℝ) / (q : ℝ))) ≤
        2 / (2 * Real.sin (Real.pi * (a.val : ℝ) / (q : ℝ))) :=
      div_le_div_of_nonneg_right hnum (by positivity)
    _ = (Real.sin (Real.pi * (a.val : ℝ) / (q : ℝ)))⁻¹ := by
      field_simp

end BoundedGaps.Maynard

end


/- ## Primitive character sums on translated integer intervals

Source module `BoundedGaps.BombieriVinogradov.Analytic.PrimitiveCharacterInterval`. -/

noncomputable section

namespace BoundedGaps.Maynard

open scoped BigOperators

open AddChar Finset

private theorem PrimitiveCharacterInterval_sum_zmod_erase_zero_eq_sum_Ico_val
    {q : ℕ} [NeZero q]
    {A : Type*} [AddCommMonoid A] (f : ZMod q → A) :
    (∑ a ∈ Finset.univ.erase (0 : ZMod q), f a) =
      ∑ a ∈ Finset.Ico 1 q, f (a : ZMod q) := by
  classical
  apply Finset.sum_nbij (fun a : ZMod q => a.val)
  · intro a ha
    have ha0 : a ≠ 0 := (Finset.mem_erase.mp ha).1
    exact Finset.mem_Ico.mpr ⟨ZMod.val_pos.mpr ha0, a.val_lt⟩
  · exact (ZMod.val_injective q).injOn
  · intro b hb
    have hbmem := Finset.mem_Ico.mp hb
    refine ⟨(b : ZMod q), ?_, ?_⟩
    · apply Finset.mem_erase.mpr
      refine ⟨?_, Finset.mem_univ _⟩
      apply (ZMod.val_ne_zero _).mp
      rw [ZMod.val_cast_of_lt hbmem.2]
      exact Nat.ne_of_gt hbmem.1
    · exact ZMod.val_cast_of_lt hbmem.2
  · intro a ha
    rw [ZMod.natCast_zmod_val]

theorem sum_dirichletCharacter_Ioc_eq_fourier
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (hchi : chi.IsPrimitive) (M : ℤ) (N : ℕ) :
    (∑ n ∈ Finset.Ioc M (M + (N : ℤ)), chi (n : ZMod q)) =
      (∑ a : ZMod q, chi⁻¹ a *
        ∑ n ∈ Finset.Ioc M (M + (N : ℤ)),
          ZMod.stdAddChar (a * (n : ZMod q))) /
        gaussSum chi⁻¹ ZMod.stdAddChar := by
  classical
  have hpoint (n : ℤ) :
      chi (n : ZMod q) =
        (∑ a : ZMod q,
          chi⁻¹ a * ZMod.stdAddChar (a * (n : ZMod q))) /
          gaussSum chi⁻¹ ZMod.stdAddChar := by
    exact primitive_fourier_expansion_div chi hchi (n : ZMod q)
  calc
    (∑ n ∈ Finset.Ioc M (M + (N : ℤ)), chi (n : ZMod q)) =
        ∑ n ∈ Finset.Ioc M (M + (N : ℤ)),
          ((∑ a : ZMod q,
            chi⁻¹ a * ZMod.stdAddChar (a * (n : ZMod q))) /
            gaussSum chi⁻¹ ZMod.stdAddChar) := by
      apply Finset.sum_congr rfl
      intro n hn
      exact hpoint n
    _ = (∑ n ∈ Finset.Ioc M (M + (N : ℤ)),
          ∑ a : ZMod q,
            chi⁻¹ a * ZMod.stdAddChar (a * (n : ZMod q))) /
          gaussSum chi⁻¹ ZMod.stdAddChar := by
      rw [Finset.sum_div]
    _ = (∑ a : ZMod q, ∑ n ∈ Finset.Ioc M (M + (N : ℤ)),
          chi⁻¹ a * ZMod.stdAddChar (a * (n : ZMod q))) /
          gaussSum chi⁻¹ ZMod.stdAddChar := by
      congr 1
      rw [Finset.sum_comm]
    _ = (∑ a : ZMod q, chi⁻¹ a *
          ∑ n ∈ Finset.Ioc M (M + (N : ℤ)),
            ZMod.stdAddChar (a * (n : ZMod q))) /
          gaussSum chi⁻¹ ZMod.stdAddChar := by
      congr 1
      apply Finset.sum_congr rfl
      intro a ha
      rw [← Finset.mul_sum]

theorem sum_dirichletCharacter_Ioc_eq_fourier_erase_zero
    {q : ℕ} [NeZero q] (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (hchi : chi.IsPrimitive)
    (M : ℤ) (N : ℕ) :
    (∑ n ∈ Finset.Ioc M (M + (N : ℤ)), chi (n : ZMod q)) =
      (∑ a ∈ Finset.univ.erase (0 : ZMod q), chi⁻¹ a *
        ∑ n ∈ Finset.Ioc M (M + (N : ℤ)),
          ZMod.stdAddChar (a * (n : ZMod q))) /
        gaussSum chi⁻¹ ZMod.stdAddChar := by
  classical
  have hzero : chi⁻¹ (0 : ZMod q) = 0 :=
    DirichletCharacter.map_zero' chi⁻¹ (Nat.ne_of_gt hq)
  calc
    (∑ n ∈ Finset.Ioc M (M + (N : ℤ)), chi (n : ZMod q)) =
        (∑ a : ZMod q, chi⁻¹ a *
          ∑ n ∈ Finset.Ioc M (M + (N : ℤ)),
            ZMod.stdAddChar (a * (n : ZMod q))) /
          gaussSum chi⁻¹ ZMod.stdAddChar :=
      sum_dirichletCharacter_Ioc_eq_fourier chi hchi M N
    _ = (∑ a ∈ Finset.univ.erase (0 : ZMod q), chi⁻¹ a *
          ∑ n ∈ Finset.Ioc M (M + (N : ℤ)),
            ZMod.stdAddChar (a * (n : ZMod q))) /
          gaussSum chi⁻¹ ZMod.stdAddChar := by
      congr 1
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (0 : ZMod q))]
      simp [hzero]

theorem sum_dirichletCharacter_Ioc_eq_nat_fourier
    {q : ℕ} [NeZero q] (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (hchi : chi.IsPrimitive)
    (M : ℤ) (N : ℕ) :
    (∑ n ∈ Finset.Ioc M (M + (N : ℤ)), chi (n : ZMod q)) =
      (∑ a ∈ Finset.Ico 1 q, chi⁻¹ (a : ZMod q) *
        ∑ n ∈ Finset.Ioc M (M + (N : ℤ)),
          ZMod.stdAddChar ((a : ZMod q) * (n : ZMod q))) /
        gaussSum chi⁻¹ ZMod.stdAddChar := by
  classical
  calc
    (∑ n ∈ Finset.Ioc M (M + (N : ℤ)), chi (n : ZMod q)) =
        (∑ a ∈ Finset.univ.erase (0 : ZMod q), chi⁻¹ a *
          ∑ n ∈ Finset.Ioc M (M + (N : ℤ)),
            ZMod.stdAddChar (a * (n : ZMod q))) /
          gaussSum chi⁻¹ ZMod.stdAddChar :=
      sum_dirichletCharacter_Ioc_eq_fourier_erase_zero hq chi hchi M N
    _ = (∑ a ∈ Finset.Ico 1 q, chi⁻¹ (a : ZMod q) *
          ∑ n ∈ Finset.Ioc M (M + (N : ℤ)),
            ZMod.stdAddChar ((a : ZMod q) * (n : ZMod q))) /
          gaussSum chi⁻¹ ZMod.stdAddChar := by
      congr 1
      exact PrimitiveCharacterInterval_sum_zmod_erase_zero_eq_sum_Ico_val
        (f := fun a : ZMod q => chi⁻¹ a *
          ∑ n ∈ Finset.Ioc M (M + (N : ℤ)),
            ZMod.stdAddChar (a * (n : ZMod q)))

theorem norm_sum_dirichletCharacter_Ioc_le_reciprocalSineSum
    {q : ℕ} [NeZero q] (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (hchi : chi.IsPrimitive)
    (M : ℤ) (N : ℕ) :
    ‖∑ n ∈ Finset.Ioc M (M + (N : ℤ)), chi (n : ZMod q)‖ ≤
      (∑ a ∈ Finset.Ico 1 q,
        (Real.sin (Real.pi * (a : ℝ) / (q : ℝ)))⁻¹) /
        Real.sqrt q := by
  classical
  have hchiInv : chi⁻¹.IsPrimitive := by
    rw [DirichletCharacter.IsPrimitive, DirichletCharacter.conductor_inv]
    exact hchi
  have hgaussNorm : ‖gaussSum chi⁻¹ ZMod.stdAddChar‖ = Real.sqrt q :=
    norm_gaussSum_stdAddChar_of_isPrimitive chi⁻¹ hchiInv
  have hnumerator :
      ‖∑ a ∈ Finset.Ico 1 q, chi⁻¹ (a : ZMod q) *
        ∑ n ∈ Finset.Ioc M (M + (N : ℤ)),
          ZMod.stdAddChar ((a : ZMod q) * (n : ZMod q))‖ ≤
        ∑ a ∈ Finset.Ico 1 q,
          (Real.sin (Real.pi * (a : ℝ) / (q : ℝ)))⁻¹ := by
    calc
      _ ≤ ∑ a ∈ Finset.Ico 1 q,
          ‖chi⁻¹ (a : ZMod q) *
            ∑ n ∈ Finset.Ioc M (M + (N : ℤ)),
              ZMod.stdAddChar ((a : ZMod q) * (n : ZMod q))‖ :=
        norm_sum_le _ _
      _ ≤ ∑ a ∈ Finset.Ico 1 q,
          (Real.sin (Real.pi * (a : ℝ) / (q : ℝ)))⁻¹ := by
        apply Finset.sum_le_sum
        intro a ha
        have haIco := Finset.mem_Ico.mp ha
        have ha0 : (a : ZMod q) ≠ 0 := by
          apply (ZMod.val_ne_zero (a : ZMod q)).mp
          rw [ZMod.val_cast_of_lt haIco.2]
          exact Nat.ne_of_gt haIco.1
        have hinterval := norm_sum_stdAddChar_Ioc_le_inv_sin
          (q := q) (a := (a : ZMod q)) ha0 M N
        rw [ZMod.val_cast_of_lt haIco.2] at hinterval
        calc
          ‖chi⁻¹ (a : ZMod q) *
              ∑ n ∈ Finset.Ioc M (M + (N : ℤ)),
                ZMod.stdAddChar ((a : ZMod q) * (n : ZMod q))‖ =
              ‖chi⁻¹ (a : ZMod q)‖ *
                ‖∑ n ∈ Finset.Ioc M (M + (N : ℤ)),
                  ZMod.stdAddChar ((a : ZMod q) * (n : ZMod q))‖ :=
            norm_mul _ _
          _ ≤ 1 * (Real.sin
                (Real.pi * (a : ℝ) / (q : ℝ)))⁻¹ :=
            mul_le_mul (DirichletCharacter.norm_le_one chi⁻¹ (a : ZMod q))
              hinterval (norm_nonneg _) zero_le_one
          _ = (Real.sin (Real.pi * (a : ℝ) / (q : ℝ)))⁻¹ := one_mul _
  rw [sum_dirichletCharacter_Ioc_eq_nat_fourier hq chi hchi M N,
    norm_div, hgaussNorm]
  exact div_le_div_of_nonneg_right hnumerator (Real.sqrt_nonneg q)

end BoundedGaps.Maynard

end


/- ## The sharp reciprocal-sine aggregate

Source module `BoundedGaps.BombieriVinogradov.Analytic.ReciprocalSineAggregate`. -/

noncomputable section

namespace BoundedGaps.Maynard

open scoped BigOperators

open Finset

private theorem ReciprocalSineAggregate_harmonic_cast_le_log_two_mul_add_one (n : ℕ) :
    (harmonic n : ℝ) ≤ Real.log (2 * (n : ℝ) + 1) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      rw [harmonic_succ]
      simp only [Rat.cast_add, Rat.cast_inv, Rat.cast_natCast, Nat.cast_succ]
      have hden : (0 : ℝ) < 2 * (n : ℝ) + 1 := by positivity
      have hlog := Real.le_log_one_add_of_nonneg
        (show (0 : ℝ) ≤ 2 / (2 * (n : ℝ) + 1) by positivity)
      have hincrement :
          ((n : ℝ) + 1)⁻¹ ≤
            Real.log (2 * ((n : ℝ) + 1) + 1) -
              Real.log (2 * (n : ℝ) + 1) := by
        rw [← Real.log_div (by positivity) hden.ne']
        convert hlog using 1 <;> field_simp <;> ring_nf
      linarith

private theorem ReciprocalSineAggregate_harmonic_cast_lt_log_two_mul_add_one {n : ℕ} (hn : 0 < n) :
    (harmonic n : ℝ) < Real.log (2 * (n : ℝ) + 1) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  rw [harmonic_succ]
  simp only [Rat.cast_add, Rat.cast_inv, Rat.cast_natCast, Nat.cast_succ]
  have hbase := ReciprocalSineAggregate_harmonic_cast_le_log_two_mul_add_one n
  have hden : (0 : ℝ) < 2 * (n : ℝ) + 1 := by positivity
  have hlog := Real.lt_log_one_add_of_pos
    (show (0 : ℝ) < 2 / (2 * (n : ℝ) + 1) by positivity)
  have hincrement :
      ((n : ℝ) + 1)⁻¹ <
        Real.log (2 * ((n : ℝ) + 1) + 1) -
          Real.log (2 * (n : ℝ) + 1) := by
    rw [← Real.log_div (by positivity) hden.ne']
    convert hlog using 1 <;> field_simp <;> ring_nf
  linarith

private theorem ReciprocalSineAggregate_harmonic_cast_pred_add_inv_two_mul_lt_log_two_mul
    {m : ℕ} (hm : 0 < m) :
    (harmonic (m - 1) : ℝ) + (((2 * m : ℕ) : ℝ))⁻¹ <
      Real.log (((2 * m : ℕ) : ℝ)) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
  simp only [Nat.succ_sub_one, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_succ]
  have hbase := ReciprocalSineAggregate_harmonic_cast_le_log_two_mul_add_one m
  have hden : (0 : ℝ) < 2 * (m : ℝ) + 1 := by positivity
  have hx : (0 : ℝ) < (2 * (m : ℝ) + 1)⁻¹ := by positivity
  have hlog := Real.lt_log_one_add_of_pos hx
  have hincrement :
      (2 * ((m : ℝ) + 1))⁻¹ <
        Real.log (2 * ((m : ℝ) + 1)) -
          Real.log (2 * (m : ℝ) + 1) := by
    rw [← Real.log_div (by positivity) hden.ne']
    calc
      (2 * ((m : ℝ) + 1))⁻¹ <
          2 * (2 * (m : ℝ) + 1)⁻¹ /
            ((2 * (m : ℝ) + 1)⁻¹ + 2) := by
        field_simp
        linarith
      _ < Real.log (1 + (2 * (m : ℝ) + 1)⁻¹) := hlog
      _ = Real.log (2 * ((m : ℝ) + 1) / (2 * (m : ℝ) + 1)) := by
        congr 1
        field_simp
        ring
  linarith

private noncomputable def ReciprocalSineAggregate_reciprocalSineTerm (q a : ℕ) : ℝ :=
  (Real.sin (Real.pi * (a : ℝ) / (q : ℝ)))⁻¹

private theorem ReciprocalSineAggregate_reciprocalSineTerm_le_div {q a : ℕ} (hq : 0 < q)
    (ha : 0 < a) (haq : 2 * a ≤ q) :
    ReciprocalSineAggregate_reciprocalSineTerm q a ≤ (q : ℝ) / (2 * (a : ℝ)) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hangle0 : 0 ≤ Real.pi * (a : ℝ) / (q : ℝ) := by positivity
  have hanglehalf : Real.pi * (a : ℝ) / (q : ℝ) ≤ Real.pi / 2 := by
    rw [div_le_div_iff₀ hqR zero_lt_two]
    have haqR : (2 : ℝ) * (a : ℝ) ≤ q := by exact_mod_cast haq
    nlinarith [Real.pi_pos]
  have hjordan := Real.mul_le_sin hangle0 hanglehalf
  have hbase : 0 < 2 / Real.pi *
      (Real.pi * (a : ℝ) / (q : ℝ)) := by positivity
  have hinv := inv_anti₀ hbase hjordan
  calc
    ReciprocalSineAggregate_reciprocalSineTerm q a =
        (Real.sin (Real.pi * (a : ℝ) / (q : ℝ)))⁻¹ := rfl
    _ ≤ (2 / Real.pi * (Real.pi * (a : ℝ) / (q : ℝ)))⁻¹ := hinv
    _ = (q : ℝ) / (2 * (a : ℝ)) := by field_simp

private theorem ReciprocalSineAggregate_reciprocalSineTerm_sub {q a : ℕ} (hq : 0 < q) (ha : a ≤ q) :
    ReciprocalSineAggregate_reciprocalSineTerm q (q - a) = ReciprocalSineAggregate_reciprocalSineTerm q a := by
  rw [ReciprocalSineAggregate_reciprocalSineTerm, ReciprocalSineAggregate_reciprocalSineTerm, Nat.cast_sub ha]
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hq)
  rw [show Real.pi * ((q : ℝ) - (a : ℝ)) / (q : ℝ) =
      Real.pi - Real.pi * (a : ℝ) / (q : ℝ) by field_simp,
    Real.sin_pi_sub]

private theorem ReciprocalSineAggregate_reciprocalSineTerm_two_mul_self {m : ℕ} (hm : 0 < m) :
    ReciprocalSineAggregate_reciprocalSineTerm (2 * m) m = 1 := by
  rw [ReciprocalSineAggregate_reciprocalSineTerm]
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  rw [show Real.pi * (m : ℝ) / ((2 * m : ℕ) : ℝ) = Real.pi / 2 by
      push_cast
      field_simp,
    Real.sin_pi_div_two, inv_one]

private theorem ReciprocalSineAggregate_sum_Ico_inv_eq_harmonic (n : ℕ) :
    (∑ a ∈ Finset.Ico 1 (n + 1), ((a : ℝ))⁻¹) = (harmonic n : ℝ) := by
  rw [Finset.Ico_add_one_right_eq_Icc]
  simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]

private theorem ReciprocalSineAggregate_sum_reciprocalSine_Ico_le_half_mul_harmonic
    {q m : ℕ} (hq : 0 < q) (hmq : 2 * m ≤ q) :
    (∑ a ∈ Finset.Ico 1 (m + 1), ReciprocalSineAggregate_reciprocalSineTerm q a) ≤
      (q : ℝ) / 2 * (harmonic m : ℝ) := by
  calc
    (∑ a ∈ Finset.Ico 1 (m + 1), ReciprocalSineAggregate_reciprocalSineTerm q a) ≤
        ∑ a ∈ Finset.Ico 1 (m + 1), (q : ℝ) / (2 * (a : ℝ)) := by
      apply Finset.sum_le_sum
      intro a ha
      exact ReciprocalSineAggregate_reciprocalSineTerm_le_div hq (Finset.mem_Ico.mp ha).1
        ((Nat.mul_le_mul_left 2
          (Nat.le_of_lt_succ (Finset.mem_Ico.mp ha).2)).trans hmq)
    _ = (q : ℝ) / 2 *
        ∑ a ∈ Finset.Ico 1 (m + 1), ((a : ℝ))⁻¹ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a ha
      field_simp
    _ = (q : ℝ) / 2 * (harmonic m : ℝ) := by
      rw [ReciprocalSineAggregate_sum_Ico_inv_eq_harmonic]

private theorem ReciprocalSineAggregate_sum_reciprocalSine_odd_eq_two_mul (m : ℕ) :
    (∑ a ∈ Finset.Ico 1 (2 * m + 1), ReciprocalSineAggregate_reciprocalSineTerm (2 * m + 1) a) =
      2 * ∑ a ∈ Finset.Ico 1 (m + 1), ReciprocalSineAggregate_reciprocalSineTerm (2 * m + 1) a := by
  have hq : 0 < 2 * m + 1 := by omega
  have hreflect := Finset.sum_Ico_reflect
    (ReciprocalSineAggregate_reciprocalSineTerm (2 * m + 1)) 1
    (m := m + 1) (n := 2 * m + 1) (by omega)
  have hb1 : 2 * m + 1 + 1 - (m + 1) = m + 1 := by omega
  have hb2 : 2 * m + 1 + 1 - 1 = 2 * m + 1 := by omega
  rw [hb1, hb2] at hreflect
  have hupper :
      (∑ a ∈ Finset.Ico (m + 1) (2 * m + 1),
        ReciprocalSineAggregate_reciprocalSineTerm (2 * m + 1) a) =
        ∑ a ∈ Finset.Ico 1 (m + 1), ReciprocalSineAggregate_reciprocalSineTerm (2 * m + 1) a := by
    rw [← hreflect]
    apply Finset.sum_congr rfl
    intro a ha
    apply ReciprocalSineAggregate_reciprocalSineTerm_sub hq
    exact (Nat.le_of_lt_succ (Finset.mem_Ico.mp ha).2).trans (by omega)
  calc
    (∑ a ∈ Finset.Ico 1 (2 * m + 1), ReciprocalSineAggregate_reciprocalSineTerm (2 * m + 1) a) =
        (∑ a ∈ Finset.Ico 1 (m + 1), ReciprocalSineAggregate_reciprocalSineTerm (2 * m + 1) a) +
          ∑ a ∈ Finset.Ico (m + 1) (2 * m + 1),
            ReciprocalSineAggregate_reciprocalSineTerm (2 * m + 1) a := by
      rw [Finset.sum_Ico_consecutive (ReciprocalSineAggregate_reciprocalSineTerm (2 * m + 1))
        (by omega) (by omega)]
    _ = 2 * ∑ a ∈ Finset.Ico 1 (m + 1),
        ReciprocalSineAggregate_reciprocalSineTerm (2 * m + 1) a := by rw [hupper]; ring

private theorem ReciprocalSineAggregate_sum_reciprocalSine_even_eq_two_mul_add_one
    {m : ℕ} (hm : 0 < m) :
    (∑ a ∈ Finset.Ico 1 (2 * m), ReciprocalSineAggregate_reciprocalSineTerm (2 * m) a) =
      2 * (∑ a ∈ Finset.Ico 1 m, ReciprocalSineAggregate_reciprocalSineTerm (2 * m) a) + 1 := by
  have hq : 0 < 2 * m := Nat.mul_pos two_pos hm
  have hreflect := Finset.sum_Ico_reflect
    (ReciprocalSineAggregate_reciprocalSineTerm (2 * m)) 1
    (m := m) (n := 2 * m) (by omega)
  have hb1 : 2 * m + 1 - m = m + 1 := by omega
  have hb2 : 2 * m + 1 - 1 = 2 * m := by omega
  rw [hb1, hb2] at hreflect
  have hupper :
      (∑ a ∈ Finset.Ico (m + 1) (2 * m), ReciprocalSineAggregate_reciprocalSineTerm (2 * m) a) =
        ∑ a ∈ Finset.Ico 1 m, ReciprocalSineAggregate_reciprocalSineTerm (2 * m) a := by
    rw [← hreflect]
    apply Finset.sum_congr rfl
    intro a ha
    apply ReciprocalSineAggregate_reciprocalSineTerm_sub hq
    exact (Nat.le_of_lt (Finset.mem_Ico.mp ha).2).trans (by omega)
  have hrest :
      (∑ a ∈ Finset.Ico m (2 * m), ReciprocalSineAggregate_reciprocalSineTerm (2 * m) a) =
        ReciprocalSineAggregate_reciprocalSineTerm (2 * m) m +
          ∑ a ∈ Finset.Ico (m + 1) (2 * m), ReciprocalSineAggregate_reciprocalSineTerm (2 * m) a := by
    calc
      _ = (∑ a ∈ Finset.Ico m (m + 1), ReciprocalSineAggregate_reciprocalSineTerm (2 * m) a) +
          ∑ a ∈ Finset.Ico (m + 1) (2 * m), ReciprocalSineAggregate_reciprocalSineTerm (2 * m) a := by
        rw [Finset.sum_Ico_consecutive (ReciprocalSineAggregate_reciprocalSineTerm (2 * m))
          (by omega) (by omega)]
      _ = _ := by simp
  calc
    (∑ a ∈ Finset.Ico 1 (2 * m), ReciprocalSineAggregate_reciprocalSineTerm (2 * m) a) =
        (∑ a ∈ Finset.Ico 1 m, ReciprocalSineAggregate_reciprocalSineTerm (2 * m) a) +
          ∑ a ∈ Finset.Ico m (2 * m), ReciprocalSineAggregate_reciprocalSineTerm (2 * m) a := by
      rw [Finset.sum_Ico_consecutive (ReciprocalSineAggregate_reciprocalSineTerm (2 * m))
        (by omega) (by omega)]
    _ = 2 * (∑ a ∈ Finset.Ico 1 m, ReciprocalSineAggregate_reciprocalSineTerm (2 * m) a) + 1 := by
      rw [hrest, hupper, ReciprocalSineAggregate_reciprocalSineTerm_two_mul_self hm]
      ring

theorem sum_reciprocalSine_Ico_lt_mul_log {q : ℕ} (hq : 1 < q) :
    (∑ a ∈ Finset.Ico 1 q,
      (Real.sin (Real.pi * (a : ℝ) / (q : ℝ)))⁻¹) <
      (q : ℝ) * Real.log (q : ℝ) := by
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' q
  · have hm : 0 < m := by omega
    change (∑ a ∈ Finset.Ico 1 (2 * m), ReciprocalSineAggregate_reciprocalSineTerm (2 * m) a) < _
    rw [ReciprocalSineAggregate_sum_reciprocalSine_even_eq_two_mul_add_one hm]
    have hhalf := ReciprocalSineAggregate_sum_reciprocalSine_Ico_le_half_mul_harmonic
      (q := 2 * m) (m := m - 1) (by omega) (by omega)
    have htop : m - 1 + 1 = m := Nat.sub_add_cancel hm
    rw [htop] at hhalf
    have hlog := ReciprocalSineAggregate_harmonic_cast_pred_add_inv_two_mul_lt_log_two_mul hm
    calc
      2 * (∑ a ∈ Finset.Ico 1 m, ReciprocalSineAggregate_reciprocalSineTerm (2 * m) a) + 1 ≤
          2 * (((2 * m : ℕ) : ℝ) / 2 * (harmonic (m - 1) : ℝ)) + 1 :=
        by
          simpa only [add_comm] using add_le_add_right
            (mul_le_mul_of_nonneg_left hhalf (show (0 : ℝ) ≤ 2 by norm_num)) 1
      _ = ((2 * m : ℕ) : ℝ) *
          ((harmonic (m - 1) : ℝ) + (((2 * m : ℕ) : ℝ))⁻¹) := by
        have htwoM : (((2 * m : ℕ) : ℝ)) ≠ 0 := by positivity
        field_simp
      _ < ((2 * m : ℕ) : ℝ) * Real.log (((2 * m : ℕ) : ℝ)) :=
        mul_lt_mul_of_pos_left hlog (by positivity)
  · have hm : 0 < m := by omega
    change (∑ a ∈ Finset.Ico 1 (2 * m + 1),
      ReciprocalSineAggregate_reciprocalSineTerm (2 * m + 1) a) < _
    rw [ReciprocalSineAggregate_sum_reciprocalSine_odd_eq_two_mul]
    have hhalf := ReciprocalSineAggregate_sum_reciprocalSine_Ico_le_half_mul_harmonic
      (q := 2 * m + 1) (m := m) (by omega) (by omega)
    have hlog := ReciprocalSineAggregate_harmonic_cast_lt_log_two_mul_add_one hm
    calc
      2 * (∑ a ∈ Finset.Ico 1 (m + 1), ReciprocalSineAggregate_reciprocalSineTerm (2 * m + 1) a) ≤
          2 * (((2 * m + 1 : ℕ) : ℝ) / 2 * (harmonic m : ℝ)) :=
        mul_le_mul_of_nonneg_left hhalf (by norm_num)
      _ = ((2 * m + 1 : ℕ) : ℝ) * (harmonic m : ℝ) := by ring
      _ < ((2 * m + 1 : ℕ) : ℝ) * Real.log (((2 * m + 1 : ℕ) : ℝ)) := by
        apply mul_lt_mul_of_pos_left _ (by positivity)
        simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using hlog

end BoundedGaps.Maynard

end


/- ## Primitive Polya--Vinogradov interval bound

Source module `BoundedGaps.BombieriVinogradov.Analytic.PrimitivePolyaVinogradov`. -/

noncomputable section

namespace BoundedGaps.Maynard

open scoped BigOperators

theorem norm_sum_dirichletCharacter_Ioc_lt_sqrt_mul_log
    {q : ℕ} [NeZero q] (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (hchi : chi.IsPrimitive)
    (M : ℤ) (N : ℕ) :
    ‖∑ n ∈ Finset.Ioc M (M + (N : ℤ)), chi (n : ZMod q)‖ <
      Real.sqrt (q : ℝ) * Real.log (q : ℝ) := by
  have hqpos : (0 : ℝ) < q := by
    exact_mod_cast Nat.zero_lt_of_lt hq
  have hsqrt : 0 < Real.sqrt (q : ℝ) := Real.sqrt_pos.2 hqpos
  calc
    ‖∑ n ∈ Finset.Ioc M (M + (N : ℤ)), chi (n : ZMod q)‖ ≤
        (∑ a ∈ Finset.Ico 1 q,
          (Real.sin (Real.pi * (a : ℝ) / (q : ℝ)))⁻¹) /
          Real.sqrt q :=
      norm_sum_dirichletCharacter_Ioc_le_reciprocalSineSum hq chi hchi M N
    _ < ((q : ℝ) * Real.log (q : ℝ)) / Real.sqrt q :=
      div_lt_div_of_pos_right (sum_reciprocalSine_Ico_lt_mul_log hq) hsqrt
    _ = Real.sqrt (q : ℝ) * Real.log (q : ℝ) := by
      apply (div_eq_iff hsqrt.ne').2
      calc
        (q : ℝ) * Real.log (q : ℝ) =
            (Real.sqrt (q : ℝ)) ^ 2 * Real.log (q : ℝ) := by
          rw [Real.sq_sqrt hqpos.le]
        _ = (Real.sqrt (q : ℝ) * Real.log (q : ℝ)) *
            Real.sqrt (q : ℝ) := by ring

end BoundedGaps.Maynard

end


/- ## Vaughan's second-term finite reduction

Source module `BoundedGaps.BombieriVinogradov.Analytic.VaughanSecondTermReduction`. -/

noncomputable section

namespace BoundedGaps.Maynard

open scoped BigOperators

noncomputable def dirichletCharacterIntervalSum
    (a b q : ℕ) (χ : DirichletCharacter ℂ q) : ℂ :=
  ∑ h ∈ Finset.Icc a b, χ h

end BoundedGaps.Maynard

end


/- ## Polya--Vinogradov bound for Vaughan's second term

Source module `BoundedGaps.BombieriVinogradov.Analytic.VaughanSecondTermPolyaVinogradov`. -/

noncomputable section

namespace BoundedGaps.Maynard

open scoped BigOperators

theorem norm_dirichletCharacterIntervalSum_lt_sqrt_mul_log
    {q : ℕ} (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (hchi : chi.IsPrimitive)
    (a b : ℕ) :
    ‖dirichletCharacterIntervalSum a b q chi‖ <
      Real.sqrt (q : ℝ) * Real.log (q : ℝ) := by
  let : NeZero q := ⟨Nat.ne_zero_of_lt hq⟩
  have hboundPos :
      0 < Real.sqrt (q : ℝ) * Real.log (q : ℝ) := by
    exact mul_pos (Real.sqrt_pos.2 (by exact_mod_cast Nat.zero_lt_of_lt hq))
      (Real.log_pos (by exact_mod_cast hq))
  by_cases hab : a ≤ b
  · have hendpoint :
        (a : ℤ) - 1 + (((b - a) + 1 : ℕ) : ℤ) = (b : ℤ) := by
      rw [Nat.cast_add, Nat.cast_sub hab]
      push_cast
      ring
    have hfinset :
        (Finset.Icc a b).map (Nat.castEmbedding : ℕ ↪ ℤ) =
          Finset.Ioc ((a : ℤ) - 1) (b : ℤ) := by
      ext n
      simp only [Finset.mem_map, Nat.castEmbedding_apply, Finset.mem_Icc,
        Finset.mem_Ioc]
      constructor
      · rintro ⟨m, hm, rfl⟩
        constructor <;> omega
      · intro hn
        have hnnonneg : 0 ≤ n := by
          have : (a : ℤ) ≤ n := by omega
          exact (Int.natCast_nonneg a).trans this
        lift n to ℕ using hnnonneg with m
        refine ⟨m, ?_, rfl⟩
        constructor <;> omega
    rw [dirichletCharacterIntervalSum]
    calc
      ‖∑ n ∈ Finset.Icc a b, chi n‖ =
          ‖∑ n ∈ Finset.Ioc ((a : ℤ) - 1) (b : ℤ),
            chi (n : ZMod q)‖ := by
        rw [← hfinset, Finset.sum_map]
        simp
      _ = ‖∑ n ∈ Finset.Ioc ((a : ℤ) - 1)
            ((a : ℤ) - 1 + (((b - a) + 1 : ℕ) : ℤ)),
            chi (n : ZMod q)‖ := by rw [hendpoint]
      _ < Real.sqrt (q : ℝ) * Real.log (q : ℝ) :=
        norm_sum_dirichletCharacter_Ioc_lt_sqrt_mul_log hq chi hchi
          ((a : ℤ) - 1) ((b - a) + 1)
  · rw [dirichletCharacterIntervalSum, Finset.Icc_eq_empty (by omega),
      Finset.sum_empty, norm_zero]
    exact hboundPos

end BoundedGaps.Maynard

end


/- ## Polya--Vinogradov for imprimitive prefixes

Source module `BoundedGaps.BombieriVinogradov.Analytic.ImprimitivePolyaVinogradovPrefix`. -/

noncomputable section

namespace BoundedGaps.Maynard

open scoped ArithmeticFunction.Moebius BigOperators

private theorem ImprimitivePolyaVinogradovPrefix_card_divisors_le_two_mul_sqrt
    {n : ℕ} (hn : 0 < n) :
    n.divisors.card ≤ 2 * Nat.sqrt n := by
  classical
  let small := n.divisors.filter fun d ↦ d ≤ Nat.sqrt n
  let large := n.divisors.filter fun d ↦ ¬d ≤ Nat.sqrt n
  have hsmall : small.card ≤ (Finset.Icc 1 (Nat.sqrt n)).card := by
    apply Finset.card_le_card
    intro d hd
    simp only [small, Finset.mem_filter] at hd
    exact Finset.mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hd.1, hd.2⟩
  have hlarge : large.card ≤ (Finset.Icc 1 (Nat.sqrt n)).card := by
    refine Finset.card_le_card_of_injOn (fun d ↦ n / d) ?_ ?_
    · intro d hd
      simp only [large, Finset.mem_coe, Finset.mem_filter] at hd
      have hdDvd : d ∣ n := (Nat.mem_divisors.mp hd.1).1
      have hdPos : 0 < d := Nat.pos_of_mem_divisors hd.1
      have hquotPos : 0 < n / d :=
        Nat.div_pos (Nat.le_of_dvd hn hdDvd) hdPos
      have hfactor : n = d * (n / d) := (Nat.mul_div_cancel' hdDvd).symm
      exact Finset.mem_Icc.mpr
        ⟨hquotPos, (Nat.le_sqrt_of_eq_mul hfactor).resolve_left hd.2⟩
    · intro d₁ hd₁ d₂ hd₂ heq
      simp only [large, Finset.mem_coe, Finset.mem_filter] at hd₁ hd₂
      have hd₁Dvd : d₁ ∣ n := (Nat.mem_divisors.mp hd₁.1).1
      have hd₂Dvd : d₂ ∣ n := (Nat.mem_divisors.mp hd₂.1).1
      have hquotPos : 0 < n / d₁ :=
        Nat.div_pos (Nat.le_of_dvd hn hd₁Dvd)
          (Nat.pos_of_mem_divisors hd₁.1)
      change n / d₁ = n / d₂ at heq
      apply Nat.mul_right_cancel hquotPos
      calc
        d₁ * (n / d₁) = n := Nat.mul_div_cancel' hd₁Dvd
        _ = d₂ * (n / d₂) := (Nat.mul_div_cancel' hd₂Dvd).symm
        _ = d₂ * (n / d₁) := by rw [heq]
  have hsmall' : small.card ≤ Nat.sqrt n := by
    calc
      small.card ≤ (Finset.Icc 1 (Nat.sqrt n)).card := hsmall
      _ = Nat.sqrt n := by rw [Nat.card_Icc]; omega
  have hlarge' : large.card ≤ Nat.sqrt n := by
    calc
      large.card ≤ (Finset.Icc 1 (Nat.sqrt n)).card := hlarge
      _ = Nat.sqrt n := by rw [Nat.card_Icc]; omega
  have hpartition : small.card + large.card = n.divisors.card := by
    simpa [small, large] using
      (Finset.card_filter_add_card_filter_not (s := n.divisors)
        (fun d ↦ d ≤ Nat.sqrt n))
  omega

private theorem ImprimitivePolyaVinogradovPrefix_divisors_gcd_eq_filter
    {n r : ℕ} (hn : 0 < n) (hr : 0 < r) :
    (n.gcd r).divisors = r.divisors.filter (fun a ↦ a ∣ n) := by
  ext a
  have hgcd : 0 < n.gcd r := Nat.gcd_pos_of_pos_left r hn
  simp only [Finset.mem_filter, Nat.mem_divisors]
  constructor
  · rintro ⟨ha, _⟩
    exact ⟨⟨ha.trans (Nat.gcd_dvd_right n r), hr.ne'⟩,
      ha.trans (Nat.gcd_dvd_left n r)⟩
  · rintro ⟨⟨har, _⟩, han⟩
    exact ⟨Nat.dvd_gcd han har, hgcd.ne'⟩

private theorem ImprimitivePolyaVinogradovPrefix_sum_moebius_divisors_eq_coprimeIndicator
    {n r : ℕ} (hn : 0 < n) (hr : 0 < r) :
    (∑ a ∈ r.divisors,
      if a ∣ n then
        ((ArithmeticFunction.moebius a : ℤ) : ℂ)
      else 0) =
      if n.Coprime r then 1 else 0 := by
  have hgcd : 0 < n.gcd r := Nat.gcd_pos_of_pos_left r hn
  calc
    (∑ a ∈ r.divisors,
        if a ∣ n then ((ArithmeticFunction.moebius a : ℤ) : ℂ) else 0) =
        ∑ a ∈ r.divisors.filter (fun a ↦ a ∣ n),
          ((ArithmeticFunction.moebius a : ℤ) : ℂ) := by
      rw [Finset.sum_filter]
    _ = ∑ a ∈ (n.gcd r).divisors,
          ((ArithmeticFunction.moebius a : ℤ) : ℂ) := by
      rw [ImprimitivePolyaVinogradovPrefix_divisors_gcd_eq_filter hn hr]
    _ = ∑ a ∈ (n.gcd r).divisors,
          (ArithmeticFunction.moebius : ArithmeticFunction ℂ) a := by
      simp
    _ = (((ArithmeticFunction.moebius : ArithmeticFunction ℂ) *
          (ArithmeticFunction.zeta : ArithmeticFunction ℂ)) (n.gcd r)) := by
      rw [ArithmeticFunction.coe_mul_zeta_apply]
    _ = (1 : ArithmeticFunction ℂ) (n.gcd r) := by
      rw [ArithmeticFunction.coe_moebius_mul_coe_zeta]
    _ = if n.Coprime r then 1 else 0 := by
      by_cases hcop : n.Coprime r <;> simp [hcop]

private theorem ImprimitivePolyaVinogradovPrefix_character_eq_primitive_mul_coprimeIndicator
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q) (n : ℕ) :
    chi n = chi.primitiveCharacter n *
      (if n.Coprime (q / chi.conductor) then 1 else 0) := by
  have hdvd : chi.conductor ∣ q := chi.conductor_dvd_level
  have hfactor : chi.conductor * (q / chi.conductor) = q :=
    Nat.mul_div_cancel' hdvd
  by_cases hnr : n.Coprime (q / chi.conductor)
  · rw [if_pos hnr, mul_one]
    by_cases hnd : n.Coprime chi.conductor
    · have hnq : n.Coprime q := by
        rw [← hfactor, Nat.coprime_mul_iff_right]
        exact ⟨hnd, hnr⟩
      simpa only [Int.cast_natCast] using
        (chi.primitiveCharacter_apply_of_isCoprime
          (Nat.isCoprime_iff_coprime.mpr hnq)).symm
    · have hnq : ¬n.Coprime q := by
        rw [← hfactor, Nat.coprime_mul_iff_right]
        exact fun h ↦ hnd h.1
      have hchiZero : chi (n : ℤ) = 0 :=
        (DirichletCharacter.apply_eq_zero_iff chi (n : ℤ)).2
          (fun h ↦ hnq (Nat.isCoprime_iff_coprime.mp h))
      have hpsiZero : chi.primitiveCharacter (n : ℤ) = 0 :=
        (DirichletCharacter.apply_eq_zero_iff chi.primitiveCharacter (n : ℤ)).2
          (fun h ↦ hnd (Nat.isCoprime_iff_coprime.mp h))
      simpa only [Int.cast_natCast] using hchiZero.trans hpsiZero.symm
  · rw [if_neg hnr, mul_zero]
    have hnq : ¬n.Coprime q := by
      rw [← hfactor, Nat.coprime_mul_iff_right]
      exact fun h ↦ hnr h.2
    simpa only [Int.cast_natCast] using
      (DirichletCharacter.apply_eq_zero_iff chi (n : ℤ)).2
        (fun h ↦ hnq (Nat.isCoprime_iff_coprime.mp h))

private theorem ImprimitivePolyaVinogradovPrefix_sum_multiples_character
    {d a Y : ℕ} (ha : 0 < a) (psi : DirichletCharacter ℂ d) :
    (∑ n ∈ (Finset.Icc 1 Y).filter (fun n ↦ a ∣ n), psi n) =
      ∑ m ∈ Finset.Icc 1 (Y / a), psi (a * m) := by
  classical
  refine Finset.sum_bij'
    (fun n _ ↦ n / a) (fun m _ ↦ a * m) ?_ ?_ ?_ ?_ ?_
  · intro n hn
    simp only [Finset.mem_filter, Finset.mem_Icc] at hn
    have hnPos : 0 < n := zero_lt_one.trans_le hn.1.1
    exact Finset.mem_Icc.mpr
      ⟨Nat.div_pos (Nat.le_of_dvd hnPos hn.2) ha,
        Nat.div_le_div_right hn.1.2⟩
  · intro m hm
    simp only [Finset.mem_Icc] at hm
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨Nat.mul_pos ha hm.1,
        by simpa [Nat.mul_comm] using (Nat.le_div_iff_mul_le ha).mp hm.2⟩,
        Nat.dvd_mul_right a m⟩
  · intro n hn
    simp only [Finset.mem_filter] at hn
    exact Nat.mul_div_cancel' hn.2
  · intro m hm
    exact Nat.mul_div_cancel_left m ha
  · intro n hn
    simp only [Finset.mem_filter] at hn
    congr 1
    simpa only [Nat.cast_mul] using
      congrArg (fun k : ℕ ↦ (k : ZMod d))
        (Nat.mul_div_cancel' hn.2).symm

private theorem ImprimitivePolyaVinogradovPrefix_imprimitivePrefix_eq_divisorSum
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q) (Y : ℕ) :
    dirichletCharacterIntervalSum 1 Y q chi =
      ∑ a ∈ (q / chi.conductor).divisors,
        (((ArithmeticFunction.moebius a : ℤ) : ℂ) *
            chi.primitiveCharacter a) *
          dirichletCharacterIntervalSum 1 (Y / a) chi.conductor
            chi.primitiveCharacter := by
  classical
  have hdPos : 0 < chi.conductor := Nat.pos_of_ne_zero chi.conductor_ne_zero
  have hrPos : 0 < q / chi.conductor :=
    Nat.div_pos
      (Nat.le_of_dvd (NeZero.pos q) chi.conductor_dvd_level) hdPos
  rw [dirichletCharacterIntervalSum]
  calc
    (∑ n ∈ Finset.Icc 1 Y, chi n) =
        ∑ n ∈ Finset.Icc 1 Y,
          chi.primitiveCharacter n *
            (if n.Coprime (q / chi.conductor) then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro n hn
      exact ImprimitivePolyaVinogradovPrefix_character_eq_primitive_mul_coprimeIndicator chi n
    _ = ∑ n ∈ Finset.Icc 1 Y,
          chi.primitiveCharacter n *
            (∑ a ∈ (q / chi.conductor).divisors,
              if a ∣ n then
                ((ArithmeticFunction.moebius a : ℤ) : ℂ)
              else 0) := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [ImprimitivePolyaVinogradovPrefix_sum_moebius_divisors_eq_coprimeIndicator
        (zero_lt_one.trans_le (Finset.mem_Icc.mp hn).1) hrPos]
    _ = ∑ a ∈ (q / chi.conductor).divisors,
          ∑ n ∈ Finset.Icc 1 Y,
            chi.primitiveCharacter n *
              (if a ∣ n then
                ((ArithmeticFunction.moebius a : ℤ) : ℂ)
              else 0) := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
    _ = ∑ a ∈ (q / chi.conductor).divisors,
        (((ArithmeticFunction.moebius a : ℤ) : ℂ) *
            chi.primitiveCharacter a) *
          dirichletCharacterIntervalSum 1 (Y / a) chi.conductor
            chi.primitiveCharacter := by
      apply Finset.sum_congr rfl
      intro a ha
      have haPos : 0 < a := Nat.pos_of_mem_divisors ha
      calc
        (∑ n ∈ Finset.Icc 1 Y,
            chi.primitiveCharacter n *
              (if a ∣ n then
                ((ArithmeticFunction.moebius a : ℤ) : ℂ)
              else 0)) =
            ∑ n ∈ (Finset.Icc 1 Y).filter (fun n ↦ a ∣ n),
              chi.primitiveCharacter n *
                ((ArithmeticFunction.moebius a : ℤ) : ℂ) := by
          rw [Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro n hn
          by_cases han : a ∣ n <;> simp [han]
        _ = ∑ m ∈ Finset.Icc 1 (Y / a),
              chi.primitiveCharacter (a * m) *
                ((ArithmeticFunction.moebius a : ℤ) : ℂ) := by
          rw [← Finset.sum_mul, ImprimitivePolyaVinogradovPrefix_sum_multiples_character haPos,
            Finset.sum_mul]
        _ = (((ArithmeticFunction.moebius a : ℤ) : ℂ) *
              chi.primitiveCharacter a) *
            (∑ m ∈ Finset.Icc 1 (Y / a),
              chi.primitiveCharacter m) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro m hm
          rw [map_mul]
          ring
        _ = (((ArithmeticFunction.moebius a : ℤ) : ℂ) *
              chi.primitiveCharacter a) *
            dirichletCharacterIntervalSum 1 (Y / a) chi.conductor
              chi.primitiveCharacter := by
          rw [dirichletCharacterIntervalSum]

theorem norm_dirichletCharacterPrefixSum_le_two_mul_sqrt_mul_log
    {q : ℕ} [NeZero q] (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1) (Y : ℕ) :
    ‖dirichletCharacterIntervalSum 1 Y q chi‖ ≤
      2 * Real.sqrt (q : ℝ) * Real.log (q : ℝ) := by
  let d := chi.conductor
  let r := q / d
  have hdPos : 0 < d := Nat.pos_of_ne_zero chi.conductor_ne_zero
  have hdDvd : d ∣ q := chi.conductor_dvd_level
  have hfactor : d * r = q := Nat.mul_div_cancel' hdDvd
  have hrPos : 0 < r :=
    Nat.div_pos (Nat.le_of_dvd (NeZero.pos q) hdDvd) hdPos
  have hdNeOne : d ≠ 1 := by
    intro hd
    exact hchi (DirichletCharacter.eq_one_iff_conductor_eq_one.mpr hd)
  have hd : 1 < d := by omega
  have hdLeq : d ≤ q := Nat.le_of_dvd (NeZero.pos q) hdDvd
  let : NeZero d := ⟨hdPos.ne'⟩
  have hscalePos :
      0 < Real.sqrt (d : ℝ) * Real.log (d : ℝ) :=
    mul_pos (Real.sqrt_pos.2 (by exact_mod_cast hdPos))
      (Real.log_pos (by exact_mod_cast hd))
  have hcard : r.divisors.card ≤ 2 * Nat.sqrt r :=
    ImprimitivePolyaVinogradovPrefix_card_divisors_le_two_mul_sqrt hrPos
  have hcardReal :
      (r.divisors.card : ℝ) ≤ 2 * Real.sqrt (r : ℝ) := by
    calc
      (r.divisors.card : ℝ) ≤ ((2 * Nat.sqrt r : ℕ) : ℝ) := by
        exact_mod_cast hcard
      _ = 2 * (Nat.sqrt r : ℝ) := by norm_num
      _ ≤ 2 * Real.sqrt (r : ℝ) := by
        gcongr
        exact Real.nat_sqrt_le_real_sqrt
  have hsqrt :
      Real.sqrt (d : ℝ) * Real.sqrt (r : ℝ) = Real.sqrt (q : ℝ) := by
    calc
      Real.sqrt (d : ℝ) * Real.sqrt (r : ℝ) =
          Real.sqrt ((d : ℝ) * (r : ℝ)) :=
        (Real.sqrt_mul (by positivity) _).symm
      _ = Real.sqrt (q : ℝ) := by rw [← Nat.cast_mul, hfactor]
  have hlog : Real.log (d : ℝ) ≤ Real.log (q : ℝ) :=
    Real.log_le_log (by exact_mod_cast hdPos) (by exact_mod_cast hdLeq)
  rw [ImprimitivePolyaVinogradovPrefix_imprimitivePrefix_eq_divisorSum chi Y]
  calc
    ‖∑ a ∈ r.divisors,
        (((ArithmeticFunction.moebius a : ℤ) : ℂ) *
            chi.primitiveCharacter a) *
          dirichletCharacterIntervalSum 1 (Y / a) d
            chi.primitiveCharacter‖ ≤
        ∑ a ∈ r.divisors,
          ‖(((ArithmeticFunction.moebius a : ℤ) : ℂ) *
              chi.primitiveCharacter a) *
            dirichletCharacterIntervalSum 1 (Y / a) d
              chi.primitiveCharacter‖ := norm_sum_le _ _
    _ ≤ ∑ _a ∈ r.divisors,
        Real.sqrt (d : ℝ) * Real.log (d : ℝ) := by
      apply Finset.sum_le_sum
      intro a ha
      have hmu : ‖((ArithmeticFunction.moebius a : ℤ) : ℂ)‖ ≤ 1 := by
        rcases ArithmeticFunction.moebius_eq_or a with hzero | hone | hneg
        · simp [hzero]
        · simp [hone]
        · simp [hneg]
      have hcoeff :
          ‖((ArithmeticFunction.moebius a : ℤ) : ℂ) *
              chi.primitiveCharacter a‖ ≤ 1 := by
        rw [norm_mul]
        calc
          ‖((ArithmeticFunction.moebius a : ℤ) : ℂ)‖ *
              ‖chi.primitiveCharacter a‖ ≤ 1 * 1 :=
            mul_le_mul hmu (chi.primitiveCharacter.norm_le_one a)
              (norm_nonneg _) zero_le_one
          _ = 1 := one_mul 1
      rw [norm_mul]
      calc
        ‖((ArithmeticFunction.moebius a : ℤ) : ℂ) *
              chi.primitiveCharacter a‖ *
            ‖dirichletCharacterIntervalSum 1 (Y / a) d
              chi.primitiveCharacter‖ ≤
            1 * ‖dirichletCharacterIntervalSum 1 (Y / a) d
              chi.primitiveCharacter‖ :=
          mul_le_mul_of_nonneg_right hcoeff (norm_nonneg _)
        _ ≤ Real.sqrt (d : ℝ) * Real.log (d : ℝ) := by
          simpa using
            (norm_dirichletCharacterIntervalSum_lt_sqrt_mul_log
              hd chi.primitiveCharacter chi.primitiveCharacter_isPrimitive
              1 (Y / a)).le
    _ = (r.divisors.card : ℝ) *
        (Real.sqrt (d : ℝ) * Real.log (d : ℝ)) := by simp
    _ ≤ (2 * Real.sqrt (r : ℝ)) *
        (Real.sqrt (d : ℝ) * Real.log (d : ℝ)) :=
      mul_le_mul_of_nonneg_right hcardReal hscalePos.le
    _ = 2 * Real.sqrt (q : ℝ) * Real.log (d : ℝ) := by
      calc
        (2 * Real.sqrt (r : ℝ)) *
            (Real.sqrt (d : ℝ) * Real.log (d : ℝ)) =
            2 * (Real.sqrt (d : ℝ) * Real.sqrt (r : ℝ)) *
              Real.log (d : ℝ) := by ring
        _ = 2 * Real.sqrt (q : ℝ) * Real.log (d : ℝ) := by rw [hsqrt]
    _ ≤ 2 * Real.sqrt (q : ℝ) * Real.log (q : ℝ) := by
      gcongr

end BoundedGaps.Maynard

end


/- ## Partial summation for nonprincipal character prefixes

Source module `BoundedGaps.BombieriVinogradov.Analytic.CharacterPartialSummation`. -/

noncomputable section

open MeasureTheory Set

open scoped BigOperators

namespace BoundedGaps.Maynard

private noncomputable def CharacterPartialSummation_characterCumulative
    {q : ℕ} (chi : DirichletCharacter ℂ q) (t : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 0 ⌊t⌋₊, chi (n : ZMod q)

private lemma CharacterPartialSummation_characterCumulative_eq_interval
    {q : ℕ} (hq : 1 < q) (chi : DirichletCharacter ℂ q) (t : ℝ) :
    CharacterPartialSummation_characterCumulative chi t =
      dirichletCharacterIntervalSum 1 ⌊t⌋₊ q chi := by
  rw [CharacterPartialSummation_characterCumulative, dirichletCharacterIntervalSum,
    Finset.Icc_eq_cons_Ioc (Nat.zero_le ⌊t⌋₊), Finset.sum_cons]
  have hzero : chi ((0 : ℕ) : ZMod q) = 0 := by
    simpa only [Nat.cast_zero] using chi.map_zero' (Nat.ne_of_gt hq)
  rw [hzero, zero_add, ← Finset.Icc_add_one_left_eq_Ioc 0 ⌊t⌋₊]
  norm_num

private lemma CharacterPartialSummation_norm_characterCumulative_le
    {q : ℕ} [NeZero q] (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1) (t : ℝ) :
    ‖CharacterPartialSummation_characterCumulative chi t‖ ≤
      2 * Real.sqrt (q : ℝ) * Real.log (q : ℝ) := by
  rw [CharacterPartialSummation_characterCumulative_eq_interval hq]
  exact norm_dirichletCharacterPrefixSum_le_two_mul_sqrt_mul_log
    hq chi hchi ⌊t⌋₊

private lemma CharacterPartialSummation_characterScale_nonneg {q : ℕ} (hq : 1 < q) :
    0 ≤ 2 * Real.sqrt (q : ℝ) * Real.log (q : ℝ) := by
  exact mul_nonneg
    (mul_nonneg (by positivity) (Real.sqrt_nonneg _))
    (Real.log_pos (by exact_mod_cast hq)).le

private lemma CharacterPartialSummation_hasDerivAt_complexOfReal_inv {t : ℝ} (ht : t ≠ 0) :
    HasDerivAt (fun u : ℝ ↦ ((u : ℂ)⁻¹))
      (-((t : ℂ) ^ 2)⁻¹) t := by
  have hcomplex : HasDerivAt (fun z : ℂ ↦ z⁻¹)
      (-((t : ℂ) ^ 2)⁻¹) (t : ℂ) :=
    hasDerivAt_inv (by exact_mod_cast ht)
  exact hcomplex.comp_ofReal

private lemma CharacterPartialSummation_integrableOn_deriv_complexOfReal_inv
    {a b : ℝ} (ha : 0 < a) :
    IntegrableOn (deriv (fun u : ℝ ↦ ((u : ℂ)⁻¹))) (Icc a b) := by
  let g : ℝ → ℂ := fun t ↦ -((t : ℂ) ^ 2)⁻¹
  have hgContinuous : ContinuousOn g (Icc a b) := by
    apply ContinuousOn.neg
    apply ContinuousOn.inv₀
    · exact Complex.continuous_ofReal.continuousOn.pow 2
    · intro t ht
      exact pow_ne_zero 2 (by exact_mod_cast (ha.trans_le ht.1).ne')
  apply hgContinuous.integrableOn_Icc.congr_fun _ measurableSet_Icc
  intro t ht
  exact (CharacterPartialSummation_hasDerivAt_complexOfReal_inv (ha.trans_le ht.1).ne').deriv.symm

private lemma CharacterPartialSummation_integral_Ioc_inv_sq
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ t : ℝ in Ioc a b, (t ^ 2)⁻¹) = a⁻¹ - b⁻¹ := by
  have hdiff : ∀ t ∈ Set.uIcc a b,
      DifferentiableAt ℝ (fun u : ℝ ↦ u⁻¹) t := by
    intro t ht
    apply differentiableAt_inv
    have ht' : t ∈ Icc a b := by
      simpa [Set.uIcc_of_le hab] using ht
    exact (ha.trans_le ht'.1).ne'
  have hint : IntervalIntegrable
      (deriv (fun u : ℝ ↦ u⁻¹)) volume a b := by
    rw [show deriv (fun u : ℝ ↦ u⁻¹) = fun u ↦ -(u ^ 2)⁻¹ by
      funext u
      exact deriv_inv]
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.neg
    apply ContinuousOn.inv₀
    · exact continuousOn_id.pow 2
    · intro t ht
      have ht' : t ∈ Icc a b := by
        simpa [Set.uIcc_of_le hab] using ht
      exact pow_ne_zero 2 (ha.trans_le ht'.1).ne'
  have hfund := intervalIntegral.integral_deriv_eq_sub hdiff hint
  rw [intervalIntegral.integral_of_le hab] at hfund
  rw [show deriv (fun u : ℝ ↦ u⁻¹) = fun u ↦ -(u ^ 2)⁻¹ by
    funext u
    exact deriv_inv] at hfund
  rw [integral_neg] at hfund
  linarith

private lemma CharacterPartialSummation_integral_const_Ioc (C a b : ℝ) (hab : a ≤ b) :
    (∫ _t : ℝ in Ioc a b, C) = C * (b - a) := by
  rw [setIntegral_const, Measure.real_def, Real.volume_Ioc,
    ENNReal.toReal_ofReal (sub_nonneg.mpr hab)]
  simp only [smul_eq_mul]
  ring

theorem norm_dirichletCharacterReciprocalIntervalSum_le
    {q : ℕ} [NeZero q] (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1)
    (x y : ℕ) (hx : 0 < x) :
    ‖∑ n ∈ Finset.Ioc x y,
      chi (n : ZMod q) / (n : ℂ)‖ ≤
      4 * Real.sqrt (q : ℝ) * Real.log (q : ℝ) / (x : ℝ) := by
  by_cases hxy : x ≤ y
  · have hxReal : 0 < (x : ℝ) := by exact_mod_cast hx
    have hxyReal : (x : ℝ) ≤ (y : ℝ) := by exact_mod_cast hxy
    have hyReal : 0 < (y : ℝ) := hxReal.trans_le hxyReal
    let C : ℝ := 2 * Real.sqrt (q : ℝ) * Real.log (q : ℝ)
    have hfDiff : ∀ t ∈ Icc (x : ℝ) y,
        DifferentiableAt ℝ (fun u : ℝ ↦ ((u : ℂ)⁻¹)) t := by
      intro t ht
      exact (CharacterPartialSummation_hasDerivAt_complexOfReal_inv
        (hxReal.trans_le ht.1).ne').differentiableAt
    have hfInt : IntegrableOn
        (deriv (fun u : ℝ ↦ ((u : ℂ)⁻¹))) (Icc (x : ℝ) y) :=
      CharacterPartialSummation_integrableOn_deriv_complexOfReal_inv hxReal
    have habel := sum_mul_eq_sub_sub_integral_mul'
      (f := fun t : ℝ ↦ ((t : ℂ)⁻¹))
      (c := fun n : ℕ ↦ chi (n : ZMod q)) hxy hfDiff hfInt
    have hrepresentation :
        (∑ n ∈ Finset.Ioc x y,
          chi (n : ZMod q) / (n : ℂ)) =
          ((y : ℂ)⁻¹ * CharacterPartialSummation_characterCumulative chi (y : ℝ) -
            (x : ℂ)⁻¹ * CharacterPartialSummation_characterCumulative chi (x : ℝ)) -
            ∫ t in Ioc (x : ℝ) y,
              deriv (fun u : ℝ ↦ ((u : ℂ)⁻¹)) t *
                CharacterPartialSummation_characterCumulative chi t := by
      simpa [CharacterPartialSummation_characterCumulative, div_eq_mul_inv, mul_comm] using habel
    have hActual : IntegrableOn
        (fun t : ℝ ↦ deriv (fun u : ℝ ↦ ((u : ℂ)⁻¹)) t *
          CharacterPartialSummation_characterCumulative chi t) (Ioc (x : ℝ) y) := by
      apply (integrableOn_mul_sum_Icc
        (fun n : ℕ ↦ chi (n : ZMod q)) hxReal.le hfInt).mono_set
      exact Ioc_subset_Icc_self
    have hReciprocalContinuous : ContinuousOn
        (fun t : ℝ ↦ (t ^ 2)⁻¹) (Icc (x : ℝ) y) := by
      apply ContinuousOn.inv₀
      · exact continuousOn_id.pow 2
      · intro t ht
        exact pow_ne_zero 2 (hxReal.trans_le ht.1).ne'
    have hMajorant : IntegrableOn
        (fun t : ℝ ↦ C * (t ^ 2)⁻¹) (Ioc (x : ℝ) y) :=
      (continuousOn_const.mul hReciprocalContinuous).integrableOn_Icc.mono_set
        Ioc_subset_Icc_self
    have hPoint : ∀ t ∈ Ioc (x : ℝ) y,
        ‖deriv (fun u : ℝ ↦ ((u : ℂ)⁻¹)) t *
            CharacterPartialSummation_characterCumulative chi t‖ ≤ C * (t ^ 2)⁻¹ := by
      intro t ht
      have htPos : 0 < t := hxReal.trans ht.1
      rw [(CharacterPartialSummation_hasDerivAt_complexOfReal_inv htPos.ne').deriv, norm_mul]
      have hderivNorm : ‖-((t : ℂ) ^ 2)⁻¹‖ = (t ^ 2)⁻¹ := by
        rw [norm_neg, norm_inv, norm_pow, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos htPos]
      rw [hderivNorm]
      calc
        (t ^ 2)⁻¹ * ‖CharacterPartialSummation_characterCumulative chi t‖ =
            ‖CharacterPartialSummation_characterCumulative chi t‖ * (t ^ 2)⁻¹ := mul_comm _ _
        _ ≤ C * (t ^ 2)⁻¹ := mul_le_mul_of_nonneg_right
          (by simpa [C] using
            CharacterPartialSummation_norm_characterCumulative_le hq chi hchi t)
          (inv_nonneg.mpr (sq_nonneg t))
    have hIntegral :
        ‖∫ t in Ioc (x : ℝ) y,
            deriv (fun u : ℝ ↦ ((u : ℂ)⁻¹)) t *
              CharacterPartialSummation_characterCumulative chi t‖ ≤
          C * ((x : ℝ)⁻¹ - (y : ℝ)⁻¹) := by
      calc
        ‖∫ t in Ioc (x : ℝ) y,
            deriv (fun u : ℝ ↦ ((u : ℂ)⁻¹)) t *
              CharacterPartialSummation_characterCumulative chi t‖ ≤
            ∫ t in Ioc (x : ℝ) y,
              ‖deriv (fun u : ℝ ↦ ((u : ℂ)⁻¹)) t *
                CharacterPartialSummation_characterCumulative chi t‖ :=
          norm_integral_le_integral_norm _
        _ ≤ ∫ t in Ioc (x : ℝ) y, C * (t ^ 2)⁻¹ := by
          apply setIntegral_mono_ae_restrict hActual.norm hMajorant
          filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
          exact hPoint t ht
        _ = C * ((x : ℝ)⁻¹ - (y : ℝ)⁻¹) := by
          rw [integral_const_mul, CharacterPartialSummation_integral_Ioc_inv_sq hxReal hxyReal]
    have hUpper :
        ‖(y : ℂ)⁻¹ * CharacterPartialSummation_characterCumulative chi (y : ℝ)‖ ≤
          C * (y : ℝ)⁻¹ := by
      rw [norm_mul, norm_inv, Complex.norm_natCast]
      calc
        (y : ℝ)⁻¹ * ‖CharacterPartialSummation_characterCumulative chi (y : ℝ)‖ ≤
            (y : ℝ)⁻¹ * C := mul_le_mul_of_nonneg_left
          (by simpa [C] using
            CharacterPartialSummation_norm_characterCumulative_le hq chi hchi (y : ℝ))
          (inv_nonneg.mpr hyReal.le)
        _ = C * (y : ℝ)⁻¹ := mul_comm _ _
    have hLower :
        ‖(x : ℂ)⁻¹ * CharacterPartialSummation_characterCumulative chi (x : ℝ)‖ ≤
          C * (x : ℝ)⁻¹ := by
      rw [norm_mul, norm_inv, Complex.norm_natCast]
      calc
        (x : ℝ)⁻¹ * ‖CharacterPartialSummation_characterCumulative chi (x : ℝ)‖ ≤
            (x : ℝ)⁻¹ * C := mul_le_mul_of_nonneg_left
          (by simpa [C] using
            CharacterPartialSummation_norm_characterCumulative_le hq chi hchi (x : ℝ))
          (inv_nonneg.mpr hxReal.le)
        _ = C * (x : ℝ)⁻¹ := mul_comm _ _
    rw [hrepresentation]
    calc
      ‖((y : ℂ)⁻¹ * CharacterPartialSummation_characterCumulative chi (y : ℝ) -
          (x : ℂ)⁻¹ * CharacterPartialSummation_characterCumulative chi (x : ℝ)) -
          ∫ t in Ioc (x : ℝ) y,
            deriv (fun u : ℝ ↦ ((u : ℂ)⁻¹)) t *
              CharacterPartialSummation_characterCumulative chi t‖ ≤
          (‖(y : ℂ)⁻¹ * CharacterPartialSummation_characterCumulative chi (y : ℝ)‖ +
            ‖(x : ℂ)⁻¹ * CharacterPartialSummation_characterCumulative chi (x : ℝ)‖) +
            ‖∫ t in Ioc (x : ℝ) y,
              deriv (fun u : ℝ ↦ ((u : ℂ)⁻¹)) t *
                CharacterPartialSummation_characterCumulative chi t‖ := by
        exact (norm_sub_le _ _).trans
          (add_le_add (norm_sub_le _ _) le_rfl)
      _ ≤ (C * (y : ℝ)⁻¹ + C * (x : ℝ)⁻¹) +
          C * ((x : ℝ)⁻¹ - (y : ℝ)⁻¹) :=
        add_le_add (add_le_add hUpper hLower) hIntegral
      _ = 4 * Real.sqrt (q : ℝ) * Real.log (q : ℝ) / (x : ℝ) := by
        dsimp [C]
        ring
  · have hyx : y ≤ x := Nat.le_of_not_ge hxy
    rw [Finset.Ioc_eq_empty_of_le hyx, Finset.sum_empty, norm_zero]
    have hNumerator :
        0 ≤ 4 * Real.sqrt (q : ℝ) * Real.log (q : ℝ) := by
      nlinarith [CharacterPartialSummation_characterScale_nonneg hq]
    exact div_nonneg hNumerator (by positivity)

theorem norm_dirichletCharacterWeightedPrefixSum_le
    {q : ℕ} [NeZero q] (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1)
    (y : ℕ) :
    ‖∑ n ∈ Finset.Icc 1 y,
      (n : ℂ) * chi (n : ZMod q)‖ ≤
      4 * (y : ℝ) * Real.sqrt (q : ℝ) * Real.log (q : ℝ) := by
  by_cases hy : y = 0
  · subst y
    simp
  · have hyPos : 0 < y := Nat.pos_of_ne_zero hy
    have hyOne : 1 ≤ y := hyPos
    have hyReal : (1 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hyOne
    let C : ℝ := 2 * Real.sqrt (q : ℝ) * Real.log (q : ℝ)
    have hcastDeriv (t : ℝ) :
        HasDerivAt (fun u : ℝ ↦ (u : ℂ)) 1 t := by
      simpa using (hasDerivAt_id (𝕜 := ℂ) (x := (t : ℂ))).comp_ofReal
    have hfDiff : ∀ t ∈ Icc (1 : ℝ) y,
        DifferentiableAt ℝ (fun u : ℝ ↦ (u : ℂ)) t := by
      intro t _
      exact (hcastDeriv t).differentiableAt
    have hfInt : IntegrableOn
        (deriv (fun u : ℝ ↦ (u : ℂ))) (Icc (1 : ℝ) y) := by
      apply (continuousOn_const : ContinuousOn
        (fun _t : ℝ ↦ (1 : ℂ)) (Icc (1 : ℝ) y)).integrableOn_Icc.congr_fun
        _ measurableSet_Icc
      intro t _
      exact (hcastDeriv t).deriv.symm
    have habel := sum_mul_eq_sub_integral_mul₀'
      (f := fun t : ℝ ↦ (t : ℂ))
      (c := fun n : ℕ ↦ chi (n : ZMod q))
      (by simpa only [Nat.cast_zero] using
        chi.map_zero' (Nat.ne_of_gt hq)) y hfDiff hfInt
    have hleft :
        (∑ n ∈ Finset.Icc 0 y,
          (n : ℂ) * chi (n : ZMod q)) =
          ∑ n ∈ Finset.Icc 1 y,
            (n : ℂ) * chi (n : ZMod q) := by
      rw [Finset.Icc_eq_cons_Ioc (Nat.zero_le y), Finset.sum_cons]
      simp only [Nat.cast_zero, zero_mul, zero_add]
      rw [← Finset.Icc_add_one_left_eq_Ioc 0 y]
      norm_num
    have hrepresentation :
        (∑ n ∈ Finset.Icc 1 y,
          (n : ℂ) * chi (n : ZMod q)) =
          (y : ℂ) * CharacterPartialSummation_characterCumulative chi (y : ℝ) -
            ∫ t in Ioc (1 : ℝ) y,
              deriv (fun u : ℝ ↦ (u : ℂ)) t *
                CharacterPartialSummation_characterCumulative chi t := by
      rw [← hleft]
      simpa [CharacterPartialSummation_characterCumulative] using habel
    have hActual : IntegrableOn
        (fun t : ℝ ↦ deriv (fun u : ℝ ↦ (u : ℂ)) t *
          CharacterPartialSummation_characterCumulative chi t) (Ioc (1 : ℝ) y) := by
      apply (integrableOn_mul_sum_Icc
        (fun n : ℕ ↦ chi (n : ZMod q)) zero_le_one hfInt).mono_set
      exact Ioc_subset_Icc_self
    have hMajorant : IntegrableOn
        (fun _t : ℝ ↦ C) (Ioc (1 : ℝ) y) :=
      integrableOn_const measure_Ioc_lt_top.ne
    have hPoint : ∀ t ∈ Ioc (1 : ℝ) y,
        ‖deriv (fun u : ℝ ↦ (u : ℂ)) t *
            CharacterPartialSummation_characterCumulative chi t‖ ≤ C := by
      intro t _
      rw [(hcastDeriv t).deriv, one_mul]
      simpa [C] using CharacterPartialSummation_norm_characterCumulative_le hq chi hchi t
    have hIntegral :
        ‖∫ t in Ioc (1 : ℝ) y,
            deriv (fun u : ℝ ↦ (u : ℂ)) t *
              CharacterPartialSummation_characterCumulative chi t‖ ≤
          C * ((y : ℝ) - 1) := by
      calc
        ‖∫ t in Ioc (1 : ℝ) y,
            deriv (fun u : ℝ ↦ (u : ℂ)) t *
              CharacterPartialSummation_characterCumulative chi t‖ ≤
            ∫ t in Ioc (1 : ℝ) y,
              ‖deriv (fun u : ℝ ↦ (u : ℂ)) t *
                CharacterPartialSummation_characterCumulative chi t‖ :=
          norm_integral_le_integral_norm _
        _ ≤ ∫ _t in Ioc (1 : ℝ) y, C := by
          apply setIntegral_mono_ae_restrict hActual.norm hMajorant
          filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
          exact hPoint t ht
        _ = C * ((y : ℝ) - 1) := CharacterPartialSummation_integral_const_Ioc C 1 y hyReal
    have hEndpoint :
        ‖(y : ℂ) * CharacterPartialSummation_characterCumulative chi (y : ℝ)‖ ≤
          (y : ℝ) * C := by
      rw [norm_mul, Complex.norm_natCast]
      exact mul_le_mul_of_nonneg_left
        (by simpa [C] using
          CharacterPartialSummation_norm_characterCumulative_le hq chi hchi (y : ℝ))
        (by positivity)
    rw [hrepresentation]
    calc
      ‖(y : ℂ) * CharacterPartialSummation_characterCumulative chi (y : ℝ) -
          ∫ t in Ioc (1 : ℝ) y,
            deriv (fun u : ℝ ↦ (u : ℂ)) t *
              CharacterPartialSummation_characterCumulative chi t‖ ≤
          ‖(y : ℂ) * CharacterPartialSummation_characterCumulative chi (y : ℝ)‖ +
            ‖∫ t in Ioc (1 : ℝ) y,
              deriv (fun u : ℝ ↦ (u : ℂ)) t *
                CharacterPartialSummation_characterCumulative chi t‖ := norm_sub_le _ _
      _ ≤ (y : ℝ) * C + C * ((y : ℝ) - 1) :=
        add_le_add hEndpoint hIntegral
      _ ≤ 4 * (y : ℝ) * Real.sqrt (q : ℝ) * Real.log (q : ℝ) := by
        dsimp [C]
        have hscale := CharacterPartialSummation_characterScale_nonneg hq
        nlinarith

end BoundedGaps.Maynard

end


/- ## Abel continuation and the ordered value at one

Source module `BoundedGaps.BombieriVinogradov.Analytic.NonprincipalLFunctionAbel`. -/

noncomputable section

open Asymptotics Complex Filter MeasureTheory Set

open scoped BigOperators Real Topology

namespace BoundedGaps.Maynard

theorem LFunction_eq_abelIntegral_of_ne_one
    {q : ℕ} [NeZero q] (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1)
    (s : ℂ) (hs : 0 < s.re) :
    DirichletCharacter.LFunction chi s =
      s * ∫ y in Set.Ioi (1 : ℝ),
        dirichletCharacterIntervalSum 1 ⌊y⌋₊ q chi *
          (y : ℂ) ^ (-(s + 1)) := by
  simpa [dirichletCharacterIntervalSum] using
    LFunction_eq_abelIntegral_of_prefixBound chi hchi
      (2 * Real.sqrt (q : ℝ) * Real.log (q : ℝ))
      (fun n ↦ by
        simpa [dirichletCharacterIntervalSum] using
          norm_dirichletCharacterPrefixSum_le_two_mul_sqrt_mul_log
            hq chi hchi n)
      s hs

private theorem NonprincipalLFunctionAbel_tendsto_reciprocalPrefix_of_abelIntegral
    {q : ℕ} [NeZero q] (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (C : ℝ)
    (hprefix : ∀ n : ℕ,
      ‖dirichletCharacterIntervalSum 1 n q chi‖ ≤ C)
    (habel : DirichletCharacter.LFunction chi (1 : ℂ) =
      (1 : ℂ) * ∫ y in Ioi (1 : ℝ),
        dirichletCharacterIntervalSum 1 ⌊y⌋₊ q chi *
          (y : ℂ) ^ (-((1 : ℂ) + 1))) :
    Tendsto (fun x : ℕ ↦ ∑ n ∈ Finset.Icc 1 x,
      chi (n : ZMod q) / (n : ℂ)) atTop
      (𝓝 (DirichletCharacter.LFunction chi (1 : ℂ))) := by
  let c : ℕ → ℂ := fun n ↦ chi (n : ZMod q)
  let f : ℝ → ℂ := fun t ↦ (t : ℂ) ^ (-(1 : ℂ))
  have hc0 : c 0 = 0 := by
    simpa [c] using chi.map_zero' (Nat.ne_of_gt hq)
  have hCumulative (n : ℕ) :
      ∑ k ∈ Finset.Icc 0 n, c k =
        dirichletCharacterIntervalSum 1 n q chi := by
    rw [Finset.Icc_eq_cons_Ioc (Nat.zero_le n), Finset.sum_cons, hc0,
      zero_add, ← Finset.Icc_add_one_left_eq_Ioc 0 n]
    norm_num [c, dirichletCharacterIntervalSum]
  have hfDiff : ∀ t ∈ Ici (1 : ℝ), DifferentiableAt ℝ f t := by
    intro t ht
    exact differentiableAt_id.ofReal_cpow_const
      (zero_lt_one.trans_le ht).ne' (by norm_num)
  have hfInt : LocallyIntegrableOn (deriv f) (Ici (1 : ℝ)) := by
    exact (Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi
      (integrableOn_Ioi_deriv_ofReal_cpow zero_lt_one
        (by norm_num))).locallyIntegrableOn
  have hEndpoint : Tendsto
      (fun n : ℕ ↦ f n * ∑ k ∈ Finset.Icc 0 n, c k) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    apply squeeze_zero' (g := fun n : ℕ ↦ C / (n : ℝ))
    · exact Eventually.of_forall fun n ↦ norm_nonneg _
    · filter_upwards [eventually_gt_atTop 0] with n hn
      rw [hCumulative, norm_mul]
      have hfn : ‖f n‖ = (n : ℝ)⁻¹ := by
        change ‖(n : ℂ) ^ (-(1 : ℂ))‖ = (n : ℝ)⁻¹
        rw [Complex.cpow_neg_one, norm_inv, Complex.norm_natCast]
      rw [hfn]
      calc
        (n : ℝ)⁻¹ *
            ‖dirichletCharacterIntervalSum 1 n q chi‖ ≤
            (n : ℝ)⁻¹ * C :=
          mul_le_mul_of_nonneg_left (hprefix n)
            (inv_nonneg.mpr (by positivity))
        _ = C / (n : ℝ) := by ring
    · simpa [div_eq_mul_inv] using
        ((tendsto_const_nhds (x := C)).mul
          (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)))
  have hDom :
      (fun t ↦ deriv f t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k) =O[atTop]
        (fun t : ℝ ↦ t ^ (-2 : ℝ)) := by
    refine isBigO_iff.mpr ⟨C, ?_⟩
    filter_upwards [eventually_gt_atTop 1] with t ht
    rw [norm_mul, hCumulative]
    have ht0 : 0 < t := zero_lt_one.trans ht
    have hderiv : ‖deriv f t‖ = t ^ (-2 : ℝ) := by
      rw [show deriv f t =
          deriv (fun u : ℝ ↦ (u : ℂ) ^ (-(1 : ℂ))) t by rfl,
        deriv_ofReal_cpow_const ht0.ne' (by norm_num), norm_mul,
        norm_neg, norm_one, one_mul,
        Complex.norm_cpow_eq_rpow_re_of_pos ht0]
      norm_num
    rw [hderiv]
    have hgNonneg : 0 ≤ t ^ (-2 : ℝ) := Real.rpow_nonneg ht0.le _
    calc
      t ^ (-2 : ℝ) *
          ‖dirichletCharacterIntervalSum 1 ⌊t⌋₊ q chi‖ ≤
          t ^ (-2 : ℝ) * C :=
        mul_le_mul_of_nonneg_left (hprefix _) hgNonneg
      _ = C * ‖t ^ (-2 : ℝ)‖ := by
        rw [Real.norm_eq_abs, abs_of_nonneg hgNonneg]
        ring
  have hconv := tendsto_sum_mul_atTop_nhds_one_sub_integral₀
    (f := f) (l := 0) c hc0 hfDiff hfInt hEndpoint hDom
      (integrableAtFilter_rpow_atTop_iff.mpr (by norm_num))
  have hleft (n : ℕ) :
      (∑ k ∈ Finset.Icc 0 n, f k * c k) =
        ∑ k ∈ Finset.Icc 1 n,
          chi (k : ZMod q) / (k : ℂ) := by
    rw [Finset.Icc_eq_cons_Ioc (Nat.zero_le n), Finset.sum_cons, hc0,
      mul_zero, zero_add, ← Finset.Icc_add_one_left_eq_Ioc 0 n]
    norm_num [f, c, Complex.cpow_neg_one, div_eq_mul_inv, mul_comm]
  have hright :
      0 - ∫ t in Ioi (1 : ℝ),
          deriv f t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k =
        DirichletCharacter.LFunction chi (1 : ℂ) := by
    rw [habel, one_mul, zero_sub, ← integral_neg]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    change -(deriv f t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k) = _
    rw [show deriv f t =
        deriv (fun u : ℝ ↦ (u : ℂ) ^ (-(1 : ℂ))) t by rfl,
      deriv_ofReal_cpow_const (zero_lt_one.trans ht).ne' (by norm_num),
      hCumulative]
    ring_nf
  rw [← hright]
  exact hconv.congr' (Eventually.of_forall hleft)

theorem tendsto_dirichletCharacterReciprocalPrefix_atTop
    {q : ℕ} [NeZero q] (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1) :
    Tendsto
      (fun x : ℕ ↦ ∑ n ∈ Finset.Icc 1 x,
        chi (n : ZMod q) / (n : ℂ))
      atTop (𝓝 (DirichletCharacter.LFunction chi (1 : ℂ))) := by
  let C : ℝ := 2 * Real.sqrt (q : ℝ) * Real.log (q : ℝ)
  apply NonprincipalLFunctionAbel_tendsto_reciprocalPrefix_of_abelIntegral hq chi C
  · intro n
    simpa [C] using
      norm_dirichletCharacterPrefixSum_le_two_mul_sqrt_mul_log
        hq chi hchi n
  · exact LFunction_eq_abelIntegral_of_ne_one
      hq chi hchi (1 : ℂ) (by norm_num)

theorem norm_LFunction_one_sub_dirichletCharacterReciprocalPrefix_le
    {q : ℕ} [NeZero q] (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1)
    (x : ℕ) (hx : 0 < x) :
    ‖DirichletCharacter.LFunction chi (1 : ℂ) -
        ∑ n ∈ Finset.Icc 1 x,
          chi (n : ZMod q) / (n : ℂ)‖ ≤
      4 * Real.sqrt (q : ℝ) * Real.log (q : ℝ) / (x : ℝ) := by
  let P : ℕ → ℂ := fun y ↦ ∑ n ∈ Finset.Icc 1 y,
    chi (n : ZMod q) / (n : ℂ)
  have htail {y : ℕ} (hxy : x ≤ y) :
      P y - P x = ∑ n ∈ Finset.Ioc x y,
        chi (n : ZMod q) / (n : ℂ) := by
    have hunion : Finset.Icc 1 x ∪ Finset.Ioc x y =
        Finset.Icc 1 y := by
      ext n
      simp only [Finset.mem_union, Finset.mem_Icc, Finset.mem_Ioc]
      constructor
      · rintro (hn | hn) <;> omega
      · intro hn
        by_cases hnx : n ≤ x
        · exact Or.inl ⟨hn.1, hnx⟩
        · exact Or.inr ⟨lt_of_not_ge hnx, hn.2⟩
    have hdis : Disjoint (Finset.Icc 1 x) (Finset.Ioc x y) := by
      rw [Finset.disjoint_left]
      intro n hncc hnoc
      simp only [Finset.mem_Icc] at hncc
      simp only [Finset.mem_Ioc] at hnoc
      omega
    change (∑ n ∈ Finset.Icc 1 y,
        chi (n : ZMod q) / (n : ℂ)) -
      (∑ n ∈ Finset.Icc 1 x,
        chi (n : ZMod q) / (n : ℂ)) = _
    rw [← hunion, Finset.sum_union hdis]
    ring
  have hconv :=
    tendsto_dirichletCharacterReciprocalPrefix_atTop hq chi hchi
  have hlim : Tendsto (fun y ↦ ‖P y - P x‖) atTop
      (𝓝 ‖DirichletCharacter.LFunction chi (1 : ℂ) - P x‖) := by
    exact (hconv.sub_const (P x)).norm
  apply le_of_tendsto hlim
  filter_upwards [eventually_ge_atTop x] with y hxy
  rw [htail hxy]
  exact norm_dirichletCharacterReciprocalIntervalSum_le
    hq chi hchi x y hx

end BoundedGaps.Maynard

end

namespace OMA.E1140

/-- The error in the triangular sum is a periodic quadratic in the fractional part. -/
noncomputable def periodic (u : ℝ) := Int.fract u * (1-Int.fract u)

theorem periodic_nonneg (u : ℝ) : 0 ≤ periodic u :=
  mul_nonneg (Int.fract_nonneg _) (sub_nonneg.mpr (Int.fract_lt_one _).le)

theorem periodic_le (u : ℝ) : periodic u ≤ 1 := by
  have hu := Int.fract_lt_one u
  unfold periodic
  nlinarith [sq_nonneg (Int.fract u)]

private theorem periodic_lipschitz_le {u v : ℝ} (h : u ≤ v) :
    |periodic v-periodic u| ≤ v-u := by
  have up := Int.fract_nonneg u
  have vp := Int.fract_nonneg v
  have uq := Int.fract_lt_one u
  have vq := Int.fract_lt_one v
  have uf := Int.floor_add_fract u
  have vf := Int.floor_add_fract v
  have hf := Int.floor_mono h
  by_cases he : ⌊u⌋ = ⌊v⌋
  · rw [he] at uf
    have hd : Int.fract v-Int.fract u = v-u := by linarith
    have hmul : periodic v-periodic u =
        (v-u)*(1-Int.fract v-Int.fract u) := by
      rw [← hd]
      unfold periodic
      ring
    rw [hmul, abs_mul, abs_of_nonneg (sub_nonneg.mpr h)]
    exact (mul_le_mul_of_nonneg_left (abs_le.mpr ⟨by linarith, by linarith⟩) (sub_nonneg.mpr h)).trans_eq (mul_one _)
  · have hcross : (⌊u⌋ : ℝ)+1 ≤ (⌊v⌋ : ℝ) := by exact_mod_cast (show ⌊u⌋+1 ≤ ⌊v⌋ by omega)
    have lu := periodic_nonneg u
    have lv := periodic_nonneg v
    have eu : periodic u ≤ 1-Int.fract u := by
      unfold periodic
      nlinarith [sq_nonneg (1-Int.fract u)]
    have ev : periodic v ≤ Int.fract v := by
      unfold periodic
      nlinarith [sq_nonneg (Int.fract v)]
    exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem periodic_lipschitz (u v : ℝ) : |periodic v-periodic u| ≤ |v-u| := by
  rcases le_total u v with h | h
  · simpa [abs_of_nonneg (sub_nonneg.mpr h)] using periodic_lipschitz_le h
  · rw [abs_sub_comm (periodic v),abs_sub_comm v,abs_of_nonneg (sub_nonneg.mpr h)]
    exact periodic_lipschitz_le h

/-- The discrepancy between a linearly smoothed divisor sum and its continuous main term. -/
noncomputable def correction (X t : ℝ) := -1/2 + t/(2*X)*periodic (X/t)

theorem triangular_identity (X t : ℝ) (hX : 0 < X) (ht : 0 < t) :
    let k : ℝ := ⌊X/t⌋
    k-t/X*(k*(k+1)/2) = X/(2*t)+correction X t := by
  dsimp [correction, periodic]
  rw [← Int.self_sub_floor]
  field_simp
  ring

theorem correction_step {X t : ℝ} (hX : 0 < X) (ht : 0 < t) :
    |correction X (t+1)-correction X t| ≤ 1/(2*X)+1/(2*t) := by
  have htp : 0 < t+1 := by linarith
  have hd : X/t-X/(t+1) = X/(t*(t+1)) := by field_simp; ring
  have hdpos : 0 ≤ X/t-X/(t+1) := by rw [hd]; positivity
  have hper : |periodic (X/(t+1))-periodic (X/t)| ≤ X/(t*(t+1)) := by
    rw [←hd, ←abs_of_nonneg hdpos, abs_sub_comm (X/t)]
    exact periodic_lipschitz _ _
  have heq : correction X (t+1)-correction X t =
      1/(2*X)*periodic (X/t)+(t+1)/(2*X)*(periodic (X/(t+1))-periodic (X/t)) := by
    unfold correction
    ring
  rw [heq]
  apply (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [abs_mul,abs_of_nonneg (periodic_nonneg _), abs_of_nonneg (by positivity : 0 ≤ 1/(2*X))]
    exact (mul_le_mul_of_nonneg_left (periodic_le _) (by positivity)).trans_eq (mul_one _)
  · rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ (t+1)/(2*X))]
    apply (mul_le_mul_of_nonneg_left hper (by positivity)).trans_eq
    field_simp

end OMA.E1140

namespace OMA.E1140
open Finset

/-- The triangular correction itself is bounded on the full divisor interval. -/
theorem correction_abs {X t : ℝ} (ht : 0 < t) (htX : t ≤ X) :
    |correction X t| ≤ 1/2 := by
  have hX := ht.trans_le htX
  have hr : t/(2*X) ≤ 1/2 := (div_le_iff₀ (by positivity)).mpr (by linarith)
  have hp := mul_nonneg (by positivity : 0 ≤ t/(2*X)) (periodic_nonneg (X/t))
  have hq := mul_le_mul_of_nonneg_left (periodic_le (X/t)) (by positivity : 0 ≤ t/(2*X))
  unfold correction
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Summing a character against the triangular correction costs at most a logarithm of the interval length. -/
theorem correction_sum {X : ℕ} (hX : 0 < X) (g : ℕ → ℂ)
    {B : ℝ} (hB : 0 ≤ B) (hb : ∀ m ≤ X, ‖∑ i ∈ range m, g i‖ ≤ B) :
    ‖∑ i ∈ range X, (correction X (i+1) : ℝ) • g i‖ ≤
      (2+Real.log X)*B := by
  let G : ℕ → ℂ := fun m => ∑ i ∈ range m, g i
  let f : ℕ → ℝ := fun i => correction X ((i:ℝ)+1)
  have hx : (0:ℝ) < X := by exact_mod_cast hX
  have hend : f (X-1) = correction X X := by
    unfold f
    congr 1
    norm_cast
    omega
  have hf0 : ‖f (X-1) • G X‖ ≤ 1/2*B := by
    rw [norm_smul,Real.norm_eq_abs,hend]
    exact mul_le_mul (correction_abs hx le_rfl) (hb _ le_rfl) (norm_nonneg _) (by norm_num)
  have hstep (i : ℕ) (hi : i < X-1) :
      ‖(f (i+1)-f i) • G (i+1)‖ ≤ (1/(2*(X:ℝ)) + 1/(2*((i:ℝ)+1)))*B := by
    rw [norm_smul,Real.norm_eq_abs]
    apply mul_le_mul _ (hb _ (by omega)) (norm_nonneg _) (by positivity)
    simpa [f, Nat.cast_add, Nat.cast_one] using correction_step hx (show 0 < (i:ℝ)+1 by positivity)
  have hsum : ∑ i ∈ range X, (1/(2*(X:ℝ)) + 1/(2*((i:ℝ)+1)))*B =
      (1/2+(harmonic X:ℝ)/2)*B := by
    rw [← Finset.sum_mul, Finset.sum_add_distrib]
    congr 1
    have hreal : ∑ i ∈ range X, 1/(2*((i:ℝ)+1)) = (harmonic X : ℝ)/2 := by
      simp only [harmonic, Rat.cast_sum, Rat.cast_inv, Nat.cast_add, Nat.cast_one]
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i _
      push_cast
      rw [one_div, mul_inv_rev]
      ring
    rw [hreal,Finset.sum_const,Finset.card_range,nsmul_eq_mul]
    field_simp
  have bound : (∑ i ∈ range (X-1), ‖(f (i+1)-f i) • G (i+1)‖) ≤ (1/2+(harmonic X:ℝ)/2)*B := by
    calc
      ∑ i ∈ range (X-1), ‖(f (i+1)-f i) • G (i+1)‖ ≤
          ∑ i ∈ range (X-1), (1/(2*(X:ℝ))+1/(2*((i:ℝ)+1)))*B :=
        Finset.sum_le_sum (fun i hi => hstep i (Finset.mem_range.mp hi))
      _ ≤ ∑ i ∈ range X, (1/(2*(X:ℝ))+1/(2*((i:ℝ)+1)))*B :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega)) (by intros; positivity)
      _ = (1/2+(harmonic X:ℝ)/2)*B := hsum
  change ‖∑ i ∈ range X, f i • g i‖ ≤ _
  rw [Finset.sum_range_by_parts]
  apply (norm_sub_le _ _).trans
  apply (add_le_add hf0 ((norm_sum_le _ _).trans bound)).trans
  have hh := harmonic_le_one_add_log X
  have hl := Real.log_nonneg (show (1:ℝ) ≤ X by exact_mod_cast hX)
  calc
      1/2*B + (1/2+(harmonic X:ℝ)/2)*B = (1+(harmonic X:ℝ)/2)*B := by ring
      _ ≤ (2+Real.log X)*B := mul_le_mul_of_nonneg_right (by linarith) hB

end OMA.E1140

/- Finite divisor-pair reindexing adapted from the FormalPantheon BoundedGaps library,
commit ffbb65c21afc8a36ace67720f1b0df1c63d26bd1 (PositiveDivisorPairReindex and
QuadraticZetaDirectEulerRemainder). The smoothed identity here uses the periodic quadratic
correction to the triangular sum. -/
namespace OMA.E1140
open scoped BigOperators
noncomputable section
def positiveFactorPairs (Q : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.Ioc 0 Q ×ˢ Finset.Ioc 0 Q).filter
    (fun p ↦ p.1 * p.2 ≤ Q)

/-- Reindex positive products and their divisor antidiagonals by ordered
positive factor pairs. -/
theorem sum_divisorsAntidiagonal_up_to_eq_sum_positiveFactorPairs
    {Q : ℕ} {M : Type*} [AddCommMonoid M]
    (f : ℕ → ℕ → M) :
    (∑ q ∈ Finset.Ioc 0 Q,
      ∑ p ∈ q.divisorsAntidiagonal, f p.1 p.2) =
      ∑ p ∈ positiveFactorPairs Q, f p.1 p.2 := by
  let T : Finset ℕ := Finset.Ioc 0 Q
  let g : ℕ × ℕ → ℕ := fun p ↦ p.1 * p.2
  have hmaps : ∀ p ∈ positiveFactorPairs Q, g p ∈ T := by
    intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hp, hprod⟩
    rcases Finset.mem_product.mp hp with ⟨hp₁, hp₂⟩
    rw [Finset.mem_Ioc] at hp₁ hp₂
    exact Finset.mem_Ioc.mpr ⟨Nat.mul_pos hp₁.1 hp₂.1, hprod⟩
  have hfiber := Finset.sum_fiberwise_of_maps_to
    (s := positiveFactorPairs Q) (t := T) hmaps
    (fun p ↦ f p.1 p.2)
  rw [← hfiber]
  apply Finset.sum_congr rfl
  intro q hq
  rw [Nat.divisorsAntidiagonal_eq_prod_filter_of_le (N := Q)]
  · apply Finset.sum_congr
    · ext p
      simp only [positiveFactorPairs, g, Finset.mem_filter]
      constructor
      · rintro ⟨hp, hprod⟩
        exact ⟨⟨hp, hprod.le.trans (Finset.mem_Ioc.mp hq).2⟩, hprod⟩
      · rintro ⟨⟨hp, _⟩, hprod⟩
        exact ⟨hp, hprod⟩
    · intro p _
      rfl
  · exact (Finset.mem_Ioc.mp hq).1.ne'
  · exact (Finset.mem_Ioc.mp hq).2

/-- Reindex a positive modulus and one of its divisors by the divisor and its
positive complementary factor. -/
theorem sum_divisors_up_to_eq_sum_positiveFactorPairs
    {Q : ℕ} {M : Type*} [AddCommMonoid M]
    (f : ℕ → ℕ → M) :
    (∑ q ∈ Finset.Ioc 0 Q,
      ∑ d ∈ q.divisors, f q d) =
      ∑ p ∈ positiveFactorPairs Q,
        f (p.1 * p.2) p.1 := by
  calc
    (∑ q ∈ Finset.Ioc 0 Q, ∑ d ∈ q.divisors, f q d) =
        ∑ q ∈ Finset.Ioc 0 Q,
          ∑ p ∈ q.divisorsAntidiagonal,
            f (p.1 * p.2) p.1 := by
      apply Finset.sum_congr rfl
      intro q hq
      rw [← Nat.sum_divisorsAntidiagonal
        (f := fun d _k ↦ f q d)]
      apply Finset.sum_congr rfl
      intro p hp
      rw [Nat.mem_divisorsAntidiagonal] at hp
      rw [hp.1]
    _ = _ :=
      sum_divisorsAntidiagonal_up_to_eq_sum_positiveFactorPairs
        (fun d k ↦ f (d * k) d)

private theorem mem_positiveFactorPairs_quadratic
    {X : ℕ} (p : ℕ × ℕ) :
    p ∈ positiveFactorPairs X ↔
      p.1 ∈ Finset.Icc 1 X ∧ p.2 ∈ Finset.Icc 1 (X / p.1) := by
  constructor
  · intro hp
    rcases Finset.mem_filter.mp hp with ⟨hp, hprod⟩
    rcases Finset.mem_product.mp hp with ⟨hp₁, hp₂⟩
    rw [Finset.mem_Ioc] at hp₁ hp₂
    exact ⟨Finset.mem_Icc.mpr ⟨hp₁.1, hp₁.2⟩,
      Finset.mem_Icc.mpr ⟨hp₂.1,
        (Nat.le_div_iff_mul_le hp₁.1).mpr (by
          simpa only [Nat.mul_comm] using hprod)⟩⟩
  · rintro ⟨hm, hk⟩
    rw [Finset.mem_Icc] at hm hk
    have hprod : p.1 * p.2 ≤ X := by
      simpa only [Nat.mul_comm] using
        (Nat.le_div_iff_mul_le hm.1).mp hk.2
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr
        ⟨Finset.mem_Ioc.mpr hm,
          Finset.mem_Ioc.mpr
            ⟨hk.1, hk.2.trans (Nat.div_le_self X p.1)⟩⟩,
        hprod⟩

private theorem sum_divisors_cutoff_eq_nested_quadratic
    {X : ℕ} (f : ℕ → ℕ → ℂ) :
    (∑ n ∈ Finset.Icc 1 X, ∑ d ∈ n.divisors, f n d) =
      ∑ a ∈ Finset.Icc 1 X, ∑ b ∈ Finset.Icc 1 (X / a), f (a * b) a := by
  calc
    (∑ n ∈ Finset.Icc 1 X, ∑ d ∈ n.divisors, f n d) =
        ∑ n ∈ Finset.Ioc 0 X, ∑ d ∈ n.divisors, f n d := by
      rw [show Finset.Icc 1 X = Finset.Ioc 0 X by
        simpa using Finset.Icc_succ_left_eq_Ioc 0 X]
    _ = ∑ p ∈ positiveFactorPairs X, f (p.1 * p.2) p.1 :=
      sum_divisors_up_to_eq_sum_positiveFactorPairs f
    _ = ∑ a ∈ Finset.Icc 1 X, ∑ b ∈ Finset.Icc 1 (X / a),
          f (a * b) a := by
      exact Finset.sum_finset_product' (f := fun a b ↦ f (a * b) a)
        (positiveFactorPairs X) (Finset.Icc 1 X)
        (fun a ↦ Finset.Icc 1 (X / a))
        mem_positiveFactorPairs_quadratic

theorem zetaMul_cutoff_eq_nested_quadratic
    {q X : ℕ} (chi : DirichletCharacter ℂ q) (w : ℕ → ℂ) :
    (∑ n ∈ Finset.Icc 1 X, chi.zetaMul n * w n) =
      ∑ a ∈ Finset.Icc 1 X, ∑ b ∈ Finset.Icc 1 (X / a),
        chi (a : ZMod q) * w (a * b) := by
  have hz : (∑ n ∈ Finset.Icc 1 X, chi.zetaMul n * w n) =
      ∑ n ∈ Finset.Icc 1 X,
        (∑ d ∈ n.divisors, chi (d : ZMod q)) * w n := by
    apply Finset.sum_congr rfl
    intro n hn
    congr 1
    rw [DirichletCharacter.zetaMul,
      ArithmeticFunction.coe_zeta_mul_apply]
    apply Finset.sum_congr rfl
    intro d hd
    simp only [toArithmeticFunction, ArithmeticFunction.coe_mk,
      if_neg (Nat.pos_of_mem_divisors hd).ne']
  rw [hz]
  simp_rw [Finset.sum_mul]
  rw [sum_divisors_cutoff_eq_nested_quadratic]


end
end OMA.E1140

namespace OMA.E1140
open Finset

private theorem triangular_sum (k : ℕ) (a X : ℝ) :
    ∑ j ∈ Icc 1 k, (1-a*j/X) = (k:ℝ)-a/X*((k:ℝ)*((k:ℝ)+1)/2) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [sum_Icc_succ_top (by omega : 1 ≤ k+1),ih]
    push_cast
    ring

theorem divisor_weight {a X : ℕ} (hX : 0 < X) (ha : 0 < a) :
    ∑ j ∈ Icc 1 (X/a), (1-(a:ℝ)*j/X) = (X:ℝ)/(2*a)+correction X a := by
  rw [triangular_sum]
  have hi := triangular_identity (X:ℝ) (a:ℝ) (by positivity) (by positivity)
  have hfloor : ((X/a:ℕ):ℝ) = ((⌊(X:ℝ)/a⌋:ℤ):ℝ) := by
    rw [← Nat.floor_div_eq_div (K:=ℝ)]
    exact natCast_floor_eq_intCast_floor (by positivity)
  simpa only [←hfloor] using hi

theorem smooth_discrete {q X : ℕ} (χ : DirichletCharacter ℂ q) (hX : 0 < X) :
    (∑ n ∈ Icc 1 X, χ.zetaMul n * ((1-(n:ℝ)/X : ℝ):ℂ)) =
      ((X:ℂ)/2)*(∑ d ∈ Icc 1 X, χ (d:ZMod q)/(d:ℂ)) +
        ∑ d ∈ Icc 1 X, (correction X d) • χ (d:ZMod q) := by
  rw [zetaMul_cutoff_eq_nested_quadratic, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  rw [← Finset.mul_sum]
  have ht := congrArg Complex.ofReal (divisor_weight hX (Finset.mem_Icc.mp hd).1)
  simp only [Complex.ofReal_sum,Complex.ofReal_add] at ht
  simp only [Nat.cast_mul]
  rw [ht,Complex.real_smul]
  simp only [Complex.ofReal_div,Complex.ofReal_mul,Complex.ofReal_natCast,Complex.ofReal_ofNat]
  ring

end OMA.E1140

namespace OMA.E1140
open Finset

/-- A linear upper bound for character partial sums controls the reciprocal tail. -/
theorem reciprocal_range {X Y : ℕ} (hx : 0 < X) (hxy : X < Y) (g : ℕ → ℂ)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hp : ∀ m ≤ Y, ‖∑ i ∈ range m, g i‖ ≤ a*m+b) :
    ‖∑ i ∈ Ico X Y, (1/((i:ℝ)+1)) • g i‖ ≤
      a*(3+Real.log Y)+3*b/X := by
  let f : ℕ → ℝ := fun i => 1/((i:ℝ)+1)
  let G : ℕ → ℂ := fun m => ∑ i ∈ range m, g i
  have xx : (0:ℝ) < X := by exact_mod_cast hx
  have yy : (X:ℝ) ≤ Y := by exact_mod_cast hxy.le
  have hh : (0:ℝ) < Y := xx.trans_le yy
  have pos (i : ℕ) : 0 < f i := by dsimp [f]; positivity
  have hend : f (Y-1)=1/(Y:ℝ) := by
    unfold f
    congr 1
    norm_cast
    omega
  have last : ‖f (Y-1) • G Y‖ ≤ a+b/X := by
    rw [norm_smul,Real.norm_eq_abs,hend,abs_of_nonneg (by positivity : 0 ≤ 1/(Y:ℝ))]
    calc
      (1/(Y:ℝ))*‖G Y‖ ≤ (1/(Y:ℝ))*(a*Y+b) := mul_le_mul_of_nonneg_left (hp _ le_rfl) (by positivity)
      _ = a+b/Y := by field_simp
      _ ≤ a+b/X := add_le_add_right (div_le_div_of_nonneg_left hb xx yy) _
  have first : ‖f X • G X‖ ≤ a+b/X := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (pos X).le]
    calc
      f X*‖G X‖ ≤ (1/(X:ℝ))*(a*X+b) := by
        apply mul_le_mul _ (hp _ hxy.le) (norm_nonneg _) (by positivity)
        exact one_div_le_one_div_of_le xx (by linarith : (X:ℝ) ≤ X+1)
      _ = a+b/X := by field_simp
  have diff (i : ℕ) : f i - f (i+1) = 1/(((i:ℝ)+1)*((i:ℝ)+2)) := by
    dsimp [f]
    push_cast
    field_simp
    ring
  have each (i : ℕ) (hi : i ∈ Ico X (Y-1)) :
      ‖(f (i+1)-f i) • G (i+1)‖ ≤ a*f i+b*(f i-f (i+1)) := by
    have hpos : 0 ≤ f i-f (i+1) := by rw [diff]; positivity
    rw [norm_smul, Real.norm_eq_abs, abs_sub_comm, abs_of_nonneg hpos]
    apply (mul_le_mul_of_nonneg_left (hp (i+1) (by have := (Finset.mem_Ico.mp hi).2; omega)) hpos).trans
    rw [mul_add]
    apply add_le_add _ (le_of_eq (mul_comm _ _))
    rw [diff]
    dsimp [f]
    push_cast
    have h1 : 0 < (i:ℝ)+1 := by positivity
    have h2 : 0 < (i:ℝ)+2 := by positivity
    calc
      1/(((i:ℝ)+1)*(i+2))*(a*(i+1)) = a*(1/(i+2)) := by field_simp
      _ ≤ a*(1/(i+1)) := mul_le_mul_of_nonneg_left (one_div_le_one_div_of_le h1 (by linarith)) ha
  have hdiff : ∑ i ∈ Ico X (Y-1), (f i-f (i+1)) ≤ 1/(X:ℝ) := by
    rw [Finset.sum_Ico_eq_sub _ (by omega)]
    simp only [Finset.sum_range_sub']
    have hhf : f X ≤ 1/(X:ℝ) := one_div_le_one_div_of_le xx (by linarith)
    linarith [(pos (Y-1))]
  have hH : ∑ i ∈ Ico X (Y-1), f i ≤ 1+Real.log Y := by
    apply (Finset.sum_le_sum_of_subset_of_nonneg (t := Finset.range Y) ?_ (fun i _ _ => (pos i).le)).trans
    · simpa [f,harmonic,Rat.cast_sum,Rat.cast_inv,one_div] using harmonic_le_one_add_log Y
    · intro i hi
      exact Finset.mem_range.mpr (by have := (Finset.mem_Ico.mp hi).2; omega)
  have hsum : (∑ i ∈ Ico X (Y-1), ‖(f (i+1)-f i) • G (i+1)‖) ≤
      a*(1+Real.log Y)+b*(1/(X:ℝ)) := by
    apply (Finset.sum_le_sum each).trans
    rw [Finset.sum_add_distrib, ←Finset.mul_sum, ←Finset.mul_sum]
    exact add_le_add (mul_le_mul_of_nonneg_left hH ha) (mul_le_mul_of_nonneg_left hdiff hb)
  change ‖∑ i ∈ Ico X Y, f i • g i‖ ≤ _
  rw [Finset.sum_Ico_by_parts _ _ hxy]
  apply (norm_sub_le _ _).trans
  calc
    _ ≤ (a+b/X+(a+b/X))+(a*(1+Real.log Y)+b*(1/(X:ℝ))) :=
      add_le_add ((norm_sub_le _ _).trans (add_le_add last first)) ((norm_sum_le _ _).trans hsum)
    _ = _ := by ring
end OMA.E1140

namespace OMA.E1140
open Finset
private theorem sum_one_shift {M : Type*} [AddCommMonoid M] (f : ℕ → M) (n : ℕ) :
    (∑ d ∈ Icc 1 n, f d) = ∑ i ∈ range n, f (i+1) := by
  rw [Finset.range_eq_Ico, Finset.sum_Ico_add' f 0 n (c:=1)]
  simp only [Nat.zero_add,Finset.Ico_add_one_right_eq_Icc]

/-- Character cancellation up to Y and a reciprocal tail at Y suffice for the smoothed estimate at X. -/
theorem smooth_from_prefix {q X Y : ℕ} (χ : DirichletCharacter ℂ q) (hx : 0 < X)
    (hxy : X < Y) {a b δ : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (L : ℂ)
    (hprefix : ∀ m ≤ Y, ‖∑ i ∈ range m, χ ((i+1:ℕ):ZMod q)‖ ≤ a*m+b)
    (tail : ‖(∑ d ∈ Icc 1 Y, χ (d:ZMod q)/(d:ℂ))-L‖ ≤ δ) :
    ‖(∑ n ∈ Icc 1 X, χ.zetaMul n * ((1-(n:ℝ)/X : ℝ):ℂ)) - ((X:ℂ)/2)*L‖ ≤
      (2+Real.log X)*(a*X+b) + ((X:ℝ)/2)*(a*(3+Real.log Y)+3*b/X+δ) := by
  let g := fun i : ℕ => χ ((i+1:ℕ):ZMod q)
  let f := fun i : ℕ => (1/((i:ℝ)+1)) • g i
  let R := fun n : ℕ => ∑ d ∈ Icc 1 n, χ (d:ZMod q)/(d:ℂ)
  have hR (n : ℕ) : R n = ∑ i ∈ range n, f i := by
    dsimp only [R]
    rw [sum_one_shift]
    apply Finset.sum_congr rfl
    intro i _
    dsimp only [f,g]
    rw [Complex.real_smul]
    push_cast
    ring
  have hkernel : ‖∑ d ∈ Icc 1 X, (correction X d) • χ (d:ZMod q)‖ ≤
      (2+Real.log X)*(a*X+b) := by
    rw [sum_one_shift]
    simpa only [Nat.cast_add, Nat.cast_one, g] using correction_sum hx g (by positivity : 0 ≤ a*(X:ℝ)+b)
      (by
        intro m hm
        apply (hprefix m (hm.trans hxy.le)).trans
        exact add_le_add_left (mul_le_mul_of_nonneg_left (show (m:ℝ) ≤ (X:ℝ) by exact_mod_cast hm) ha) b)
  have hrec : ‖R X - R Y‖ ≤ a*(3+Real.log Y)+3*b/X := by
    rw [norm_sub_rev,hR,hR,← Finset.sum_Ico_eq_sub _ hxy.le]
    exact reciprocal_range hx hxy g ha hb hprefix
  have ht : ‖R X-L‖ ≤ a*(3+Real.log Y)+3*b/X+δ :=
    (norm_sub_le_norm_sub_add_norm_sub _ (R Y) _).trans (add_le_add hrec tail)
  rw [smooth_discrete χ hx]
  change ‖((X:ℂ)/2)*R X+_ - ((X:ℂ)/2)*L‖ ≤ _
  rw [show ∀ c : ℂ, ((X:ℂ)/2)*R X+c-((X:ℂ)/2)*L = c+((X:ℂ)/2)*(R X-L) by intro c; ring]
  apply (norm_add_le _ _).trans (add_le_add hkernel ?_)
  rw [norm_mul, norm_div,Complex.norm_natCast,Complex.norm_ofNat]
  exact mul_le_mul_of_nonneg_left ht (by positivity)
end OMA.E1140

namespace OMA.E1140
open Filter
private theorem eventually_log_plus_three : ∀ᶠ p : ℕ in atTop,
    3+Real.log p ≤ (p:ℝ)^(1/4096:ℝ) := by
  have e : (0:ℝ)<1/4096 := by norm_num
  have h := (isLittleO_log_rpow_atTop e).comp_tendsto (tendsto_natCast_atTop_atTop (R:=ℝ))
  have large := ((tendsto_rpow_atTop e).comp (tendsto_natCast_atTop_atTop (R:=ℝ))).eventually (eventually_ge_atTop 6)
  filter_upwards [h.bound (show (0:ℝ)<1/2 by norm_num),large,eventually_ge_atTop 1] with p small hp hp1
  have pp : 0 ≤ (p:ℝ)^(1/4096:ℝ) := by positivity
  have pl := Real.log_nonneg (show (1:ℝ)≤p by exact_mod_cast hp1)
  simp only [Function.comp_apply,Real.norm_eq_abs,abs_of_nonneg pp,abs_of_nonneg pl] at small
  change 6 ≤ (p:ℝ)^(1/4096:ℝ) at hp
  linarith

theorem prefix_error_window : ∀ᶠ p : ℕ in atTop,
    let X := Nat.sqrt p / 4
    let a := 8*(p:ℝ)^(-(1/512:ℝ))
    let b := 48*(p:ℝ)^(63/128:ℝ)
    let δ := (p:ℝ)^(-(1/4:ℝ))
    (2+Real.log X)*(a*X+b) + ((X:ℝ)/2)*(a*(3+Real.log (p-1:ℕ))+3*b/X+δ)
    ≤ 400*(p:ℝ)^(2041/4096:ℝ) := by
  filter_upwards [eventually_log_plus_three,eventually_pollackCutoff_bounds,eventually_ge_atTop 3] with p logs cut p3
  let X := Nat.sqrt p / 4
  let P : ℝ := p
  let K := P^(2040/4096:ℝ)
  let S := P^(1/4096:ℝ)
  let a := 8*P^(-(1/512:ℝ))
  let b := 48*P^(63/128:ℝ)
  let δ := P^(-(1/4:ℝ))
  have pp : 0<P := by dsimp [P]; positivity
  have p1 : 1≤P := by dsimp [P]; exact_mod_cast (show 1≤p by omega)
  have x1 : 1≤X := cut.1
  have xx : (0:ℝ)<X := by exact_mod_cast x1
  have xa : (X:ℝ)≤P^(1/2:ℝ) := cut.2.2.2.2
  have xlep : X≤p := by change Nat.sqrt p / 4 ≤ p; exact (Nat.div_le_self _ _).trans (Nat.sqrt_le_self _)
  have LX : 2+Real.log X ≤ S := by
    have hl := Real.log_le_log xx (show (X:ℝ)≤p by exact_mod_cast xlep)
    dsimp [S,P]
    linarith
  have LY : 3+Real.log (p-1:ℕ) ≤ S := by
    have yy : (0:ℝ)<(p-1:ℕ) := by exact_mod_cast (show 0<p-1 by omega)
    have hl := Real.log_le_log yy (show ((p-1:ℕ):ℝ)≤p by exact_mod_cast Nat.sub_le p 1)
    dsimp [S,P]
    linarith
  have a0 : 0 ≤ a := by dsimp [a]; positivity
  have b0 : 0 ≤ b := by dsimp [b]; positivity
  have d0 : 0 ≤ δ := by dsimp [δ]; positivity
  have K0 : 0 ≤ K := by dsimp [K]; positivity
  have S1 : 1 ≤ S := Real.one_le_rpow p1 (by norm_num)
  have S0 : 0 ≤ S := by linarith
  have ax : a*X≤8*K := by
    apply (mul_le_mul_of_nonneg_left xa a0).trans_eq
    dsimp [a,K]
    rw [mul_assoc, ←Real.rpow_add pp]
    congr 2
    norm_num
  have bb : b≤48*K := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le p1 (by norm_num)) (by norm_num)
  have xδ : (X:ℝ)*δ ≤ K := by
    apply (mul_le_mul_of_nonneg_right xa d0).trans
    dsimp [δ,K]
    rw [←Real.rpow_add pp]
    exact Real.rpow_le_rpow_of_exponent_le p1 (by norm_num)
  have KS : K*S = P^(2041/4096:ℝ) := by
    dsimp [K,S]
    rw [← Real.rpow_add pp]
    congr 1
    norm_num
  have kE : K ≤ K*S := by simpa using mul_le_mul_of_nonneg_left S1 K0
  change (2+Real.log X)*(a*X+b)+((X:ℝ)/2)*(a*(3+Real.log (p-1:ℕ))+3*b/X+δ) ≤ 400*P^(2041/4096:ℝ)
  rw [←KS]
  have h₀ : (2+Real.log X)*(a*X+b) ≤ S*(56*K) := by
    exact mul_le_mul LX (by linarith) (by positivity) S0
  have h₁ : a*X*(3+Real.log (p-1:ℕ)) ≤ 8*K*S :=
    (mul_le_mul_of_nonneg_left LY (by positivity)).trans (mul_le_mul_of_nonneg_right ax S0)
  have id : ((X:ℝ)/2)*(a*(3+Real.log (p-1:ℕ))+3*b/X+δ) =
      (a*X*(3+Real.log (p-1:ℕ))+3*b+X*δ)/2 := by field_simp
  rw [id]
  nlinarith

end OMA.E1140

open Filter
namespace OMA.E1140

theorem reciprocal_tail_window : ∀ᶠ p : ℕ in atTop,
    4 * Real.sqrt ((8*p:ℕ):ℝ) * Real.log ((8*p:ℕ):ℝ) / ((p-1:ℕ):ℝ) ≤
      (p:ℝ)^(-(1/4:ℝ)) := by
  have e : (0:ℝ)<1/4 := by norm_num
  have h := (isLittleO_log_rpow_atTop e).comp_tendsto (tendsto_natCast_atTop_atTop (R:=ℝ))
  filter_upwards [h.bound (show (0:ℝ)<1/48 by norm_num),eventually_ge_atTop 8] with p small p8
  have p8' : (8:ℝ) ≤ p := by exact_mod_cast p8
  have pp : (0:ℝ)<p := by linarith
  have pl := Real.log_nonneg (show (1:ℝ)≤p by linarith)
  have pow0 := Real.rpow_nonneg pp.le (1/4:ℝ)
  simp only [Function.comp_apply,Real.norm_eq_abs,abs_of_nonneg pow0,abs_of_nonneg pl] at small
  have logbound : Real.log (8*(p:ℝ)) ≤ 2*Real.log p := by
    rw [Real.log_mul (by norm_num) (ne_of_gt pp)]
    linarith [Real.log_le_log (by norm_num : (0:ℝ)<8) p8']
  have sqrtbound : Real.sqrt (8*(p:ℝ)) ≤ 3 * Real.sqrt p := by
    rw [Real.sqrt_mul (by norm_num : (0:ℝ)≤8)]
    exact mul_le_mul_of_nonneg_right (by norm_num [Real.sqrt_le_iff]) (by positivity)
  have log0 : 0 ≤ Real.log (8*(p:ℝ)) := Real.log_nonneg (by linarith)
  push_cast [Nat.cast_sub (show 1≤p by omega)] 
  apply (div_le_iff₀ (by linarith : (0:ℝ)<p-1)).mpr
  have scale : Real.sqrt p * (p:ℝ)^(1/4:ℝ) = (p:ℝ)^(-(1/4:ℝ)) * (p:ℝ) := by
    rw [Real.sqrt_eq_rpow,←Real.rpow_add pp]
    conv_rhs => rhs; rw [← Real.rpow_one (p:ℝ)]
    rw [←Real.rpow_add pp]
    norm_num
  have envelope := mul_le_mul sqrtbound logbound log0 (by positivity : 0≤3*Real.sqrt p)
  have absorb := mul_le_mul_of_nonneg_left small (Real.sqrt_nonneg (p:ℝ))
  have hpwr : 0 ≤ (p:ℝ)^(-(1/4:ℝ)) := by positivity
  nlinarith [mul_nonneg hpwr (show 0≤(p:ℝ)-2 by linarith)]

end OMA.E1140

open Filter
namespace OMA.E1140

theorem complete_smoothed : OMA.R_Erdos1140_erdos_1140_R2.H2 := by
  filter_upwards [attached_prefixes, prefix_error_window, reciprocal_tail_window,
    eventually_pollackCutoff_bounds, eventually_ge_atTop 8] with p prefixes window tails cut p8
  intro hp _ χ attached
  let X := Nat.sqrt p / 4
  let Y := p-1
  obtain ⟨χ₀,nontriv,_,att₀⟩ := exists_attached hp (by omega)
  have eq : χ = χ₀ := by
    apply DFunLike.ext
    intro z
    simpa only [ZMod.natCast_zmod_val] using (attached z.val).trans (att₀ z.val).symm
  have hn : χ ≠ 1 := fun h => nontriv (eq.symm.trans h)
  have reciprocalBound := BoundedGaps.Maynard.norm_LFunction_one_sub_dirichletCharacterReciprocalPrefix_le
    (by omega : 1<8*p) χ hn Y (by dsimp [Y]; omega)
  rw [norm_sub_rev] at reciprocalBound
  have xx : 0<X := cut.1
  have xy : X<Y := by
    have hc : X+1<p := cut.2.1
    dsimp [Y]
    omega
  exact (smooth_from_prefix χ xx xy (by positivity : 0≤8*(p:ℝ)^(-(1/512:ℝ)))
    (by positivity : 0≤48*(p:ℝ)^(63/128:ℝ)) (χ.LFunction 1)
    (fun m _ => prefixes hp χ attached m) (reciprocalBound.trans tails)).trans window

end OMA.E1140

theorem OMA.solution : type_of% @Erdos1140.erdos_1140 :=
  OMA.R_Erdos1140_erdos_1140_R2.main OMA.E1140.siegel_eight_prime OMA.E1140.complete_smoothed
