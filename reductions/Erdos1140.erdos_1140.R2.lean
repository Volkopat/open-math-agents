import FormalConjectures.ErdosProblems.«1140»
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Nat.Squarefree
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! For a prime p, the quadratic character of discriminant 8p detects a small
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

theorem main : H1 → H2 → type_of% @Erdos1140.erdos_1140 := by
  intro lower comparison
  apply OMA.E1140.finite_of_eventual_centered
  filter_upwards [OMA.E1140.small_soluble_prime lower comparison] with n good
  intro hn
  obtain ⟨p, hp, hsize, hs⟩ := good hn
  have hhalf : p/2 ≤ p := Nat.div_le_self _ _
  exact ⟨p, hp, lt_of_le_of_lt
    (Nat.add_le_add_right (Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left hhalf 2)) p) hsize, hs⟩

end OMA.R_Erdos1140_erdos_1140_R2
