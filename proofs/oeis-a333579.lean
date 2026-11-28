import OMAStatements.S_oeis_a333579
import Mathlib

/-!
# Proof of OEIS A333579, Conjecture 1 (Peter Bala)

Official OEIS entry [A333579](https://oeis.org/A333579):
$$a(n) = [x^n] \left(\frac{1 + x + x^2}{1 - x + x^2}\right)^n.$$
Conjecture (Peter Bala): For all primes $p \ge 5$,
$$a(p) \equiv 2 \pmod{p^3}.$$

## Proof Overview (100% elementary, zero `sorry`, zero custom axioms)
Let $f(x) = \frac{1 + x + x^2}{1 - x + x^2} \in \mathbb{Z}[[x]]$. Since
$(1 - x)(1 + x^3) f(x) = (1 + x)(1 - x^3)$, raising to the $p$-th power gives
$$(1 - x)^p (1 + x^3)^p f(x)^p = (1 + x)^p (1 - x^3)^p.$$
Writing $P(x) = \sum_{k=1}^{p-1} \frac{\binom{p}{k}}{p} x^k \in \mathbb{Z}[x]$, we have
$(1 + x)^p = 1 + x^p + p P(x)$ and $(1 - x)^p = 1 - x^p + p P(-x)$ (since $p$ is odd).
Working in $(\mathbb{Z}/p^3\mathbb{Z})[[x]]$ (where $p^3 = 0$), let
$$G(x) = (1 + 2 x^p) + p\big(P(x) - P(-x) + P(-x^3) - P(x^3)\big) +
  p^2\big(P(-x)^2 - P(x)P(-x) + P(x^3)^2 - P(-x^3)P(x^3) + (P(x) - P(-x))(P(-x^3) - P(x^3))\big).$$
A direct algebraic expansion shows that $(1 - x)^p (1 + x^3)^p (f(x)^p - G(x))$ has
coefficients $0$ for all degrees $d \le p$. Since $(1 - x)^p (1 + x^3)^p$ has constant term $1$,
induction on $d \le p$ yields $[x^p] f(x)^p = [x^p] G(x)$ in $\mathbb{Z}/p^3\mathbb{Z}$.
Finally, $[x^p] G(x) = 2$ in $\mathbb{Z}/p^3\mathbb{Z}$ because:
- $[x^p](1 + 2 x^p) = 2$,
- $[x^p](P(x) - P(-x)) = 0$ (since $\deg P \le p - 1 < p$),
- $[x^p](P(-x^3) - P(x^3)) = [x^p] P(x^3)^2 = [x^p](P(-x^3) P(x^3)) = 0$ (all exponents are multiples of $3$, and $3 \nmid p$),
- $[x^p](P(x) P(-x)) = 0$ (even power series, odd exponent $p$),
- $[x^p]\big((P(x) - P(-x))(P(-x^3) - P(x^3))\big) = 0$ (product of two odd series is even, odd exponent $p$),
- $[x^p] P(-x)^2 = -\sum_{k=1}^{p-1} (\binom{p}{k}/p)^2 \equiv -\sum_{k=1}^{p-1} k^{-2} \equiv 0 \pmod p$ (since $p \ge 5$), so $p^2 [x^p] P(-x)^2 = 0$ in $\mathbb{Z}/p^3\mathbb{Z}$.
-/

namespace SolvedConjecture06

open Finset BigOperators PowerSeries

/-- The formal power series $f(x) = (1 + x + x^2) \cdot (1 - x + x^2)^{-1}$ in $\mathbb{Z}[[x]]$. -/
noncomputable def fSeries : PowerSeries ℤ :=
  (1 + PowerSeries.X + PowerSeries.X ^ 2) * Ring.inverse (1 - PowerSeries.X + PowerSeries.X ^ 2)

/-- OEIS A333579: $a(n) = [x^n] \left(\frac{1 + x + x^2}{1 - x + x^2}\right)^n$. -/
noncomputable def a (n : ℕ) : ℤ :=
  PowerSeries.coeff n (fSeries ^ n)

private lemma isUnit_denom : IsUnit (1 - PowerSeries.X + PowerSeries.X ^ 2 : PowerSeries ℤ) := by
  rw [PowerSeries.isUnit_iff_constantCoeff]
  simp

private lemma fSeries_mul_denom :
    (1 - PowerSeries.X) * (1 + PowerSeries.X ^ 3) * fSeries =
      (1 + PowerSeries.X) * (1 - PowerSeries.X ^ 3) := by
  unfold fSeries
  have hinv : (1 - PowerSeries.X + PowerSeries.X ^ 2 : PowerSeries ℤ) *
      Ring.inverse (1 - PowerSeries.X + PowerSeries.X ^ 2 : PowerSeries ℤ) = 1 :=
    Ring.mul_inverse_cancel _ isUnit_denom
  have h1 : (1 - PowerSeries.X : PowerSeries ℤ) * (1 + PowerSeries.X ^ 3) =
      (1 - PowerSeries.X ^ 2) * (1 - PowerSeries.X + PowerSeries.X ^ 2) := by ring
  have h2 : (1 - PowerSeries.X ^ 2 : PowerSeries ℤ) * (1 + PowerSeries.X + PowerSeries.X ^ 2) =
      (1 + PowerSeries.X) * (1 - PowerSeries.X ^ 3) := by ring
  calc (1 - PowerSeries.X : PowerSeries ℤ) * (1 + PowerSeries.X ^ 3) *
          ((1 + PowerSeries.X + PowerSeries.X ^ 2) * Ring.inverse (1 - PowerSeries.X + PowerSeries.X ^ 2))
      = (1 - PowerSeries.X ^ 2 : PowerSeries ℤ) * (1 + PowerSeries.X + PowerSeries.X ^ 2) *
          ((1 - PowerSeries.X + PowerSeries.X ^ 2) * Ring.inverse (1 - PowerSeries.X + PowerSeries.X ^ 2)) := by
          rw [h1]; ring
    _ = (1 + PowerSeries.X : PowerSeries ℤ) * (1 - PowerSeries.X ^ 3) := by rw [hinv, mul_one, h2]

/-- If $u$ has constant coefficient $1$ and $u \cdot h$ has zero coefficients for all $d \le N$,
then $h$ has zero coefficients for all $d \le N$. -/
private lemma coeff_eq_zero_of_mul_eq_zero {R : Type*} [CommRing R]
    (u h : PowerSeries R) (hu0 : PowerSeries.constantCoeff u = 1) (N : ℕ)
    (hmul : ∀ d ≤ N, PowerSeries.coeff d (u * h) = 0) :
    ∀ d ≤ N, PowerSeries.coeff d h = 0 := by
  intro d hd
  induction d using Nat.strong_induction_on with
  | h d ih =>
    have h0 := hmul d hd
    rw [PowerSeries.coeff_mul] at h0
    have hmem : (0, d) ∈ Finset.HasAntidiagonal.antidiagonal d :=
      Finset.HasAntidiagonal.mem_antidiagonal.mpr (zero_add d)
    rw [← Finset.add_sum_erase _ _ hmem] at h0
    have hrest : ∑ x ∈ (Finset.HasAntidiagonal.antidiagonal d).erase (0, d),
        PowerSeries.coeff x.1 u * PowerSeries.coeff x.2 h = 0 := by
      refine Finset.sum_eq_zero fun x hx => ?_
      simp only [Finset.mem_erase, Finset.HasAntidiagonal.mem_antidiagonal] at hx
      have hlt : x.2 < d := by
        by_contra hge
        have hx2 : x.2 = d := by omega
        have hx1 : x.1 = 0 := by omega
        exact hx.1 (Prod.ext hx1 hx2)
      rw [ih x.2 hlt (by omega), mul_zero]
    rw [hrest, add_zero, PowerSeries.coeff_zero_eq_constantCoeff, hu0, one_mul] at h0
    exact h0

/-- The quotient polynomial $P_p(x) = \sum_{k=1}^{p-1} (\binom{p}{k}/p) x^k$ in $R[[x]]$. -/
private noncomputable def Pseries {R : Type*} [CommRing R] (p : ℕ) (t : PowerSeries R) : PowerSeries R :=
  ∑ k ∈ Finset.Icc 1 (p - 1), PowerSeries.C (((p.choose k / p : ℕ) : R)) * t ^ k

private lemma one_add_pow_p {R : Type*} [CommRing R] {p : ℕ} (hp : p.Prime) (t : PowerSeries R) :
    (1 + t) ^ p = 1 + t ^ p + (p : PowerSeries R) * Pseries p t := by
  rw [add_comm, add_pow]
  have hp1 : 1 ≤ p := hp.one_le
  have h0 : 0 ∈ Finset.range (p + 1) := Finset.mem_range.mpr (by omega)
  have hp_mem : p ∈ (Finset.range (p + 1)).erase 0 :=
    Finset.mem_erase.mpr ⟨hp.ne_zero, Finset.mem_range.mpr (Nat.lt_succ_self p)⟩
  rw [← Finset.add_sum_erase _ _ h0, ← Finset.add_sum_erase _ _ hp_mem]
  simp only [pow_zero, one_mul, mul_one, Nat.choose_zero_right, Nat.choose_self, Nat.cast_one]
  have hset : ((Finset.range (p + 1)).erase 0).erase p = Finset.Icc 1 (p - 1) := by
    ext k; simp only [Finset.mem_erase, Finset.mem_range, Finset.mem_Icc]; omega
  rw [hset]
  unfold Pseries
  rw [Finset.mul_sum]
  have hterm : ∀ k ∈ Finset.Icc 1 (p - 1),
      t ^ k * (1 : PowerSeries R) ^ (p - k) * (p.choose k : PowerSeries R) =
        (p : PowerSeries R) * (PowerSeries.C (((p.choose k / p : ℕ) : R)) * t ^ k) := by
    intro k hk
    simp only [Finset.mem_Icc] at hk
    have hdvd : p ∣ p.choose k := hp.dvd_choose_self (by omega) (by omega)
    have hdiv := Nat.mul_div_cancel' hdvd
    rw [one_pow, mul_one]
    nth_rw 1 [← hdiv]
    rw [Nat.cast_mul, ← map_natCast PowerSeries.C (p.choose k / p)]
    ring
  rw [Finset.sum_congr rfl hterm]
  ring

private lemma one_sub_pow_p {R : Type*} [CommRing R] {p : ℕ} (hp : p.Prime) (hp_odd : Odd p)
    (t : PowerSeries R) :
    (1 - t) ^ p = 1 - t ^ p + (p : PowerSeries R) * Pseries p (-t) := by
  have h := one_add_pow_p hp (-t)
  rw [show 1 + (-t) = 1 - t by ring] at h
  have hneg : (-t) ^ p = -(t ^ p) := by
    rcases hp_odd with ⟨m, rfl⟩
    rw [neg_pow, show (-1 : PowerSeries R) ^ (2 * m + 1) = -1 by
      rw [pow_succ, pow_mul]; norm_num]
    ring
  rw [hneg] at h
  linear_combination h

private lemma coeff_Pseries_X {R : Type*} [CommRing R] (p d : ℕ) :
    PowerSeries.coeff d (Pseries (R := R) p PowerSeries.X) =
      if 1 ≤ d ∧ d ≤ p - 1 then ((p.choose d / p : ℕ) : R) else 0 := by
  unfold Pseries
  rw [map_sum]
  simp only [PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq]
  simp only [Finset.mem_Icc]

private lemma coeff_Pseries_neg_X {R : Type*} [CommRing R] (p d : ℕ) :
    PowerSeries.coeff d (Pseries (R := R) p (-PowerSeries.X)) =
      if 1 ≤ d ∧ d ≤ p - 1 then (-1 : R) ^ d * ((p.choose d / p : ℕ) : R) else 0 := by
  unfold Pseries
  rw [map_sum]
  have hterm : ∀ k ∈ Finset.Icc 1 (p - 1),
      PowerSeries.coeff d (PowerSeries.C (((p.choose k / p : ℕ) : R)) * (-PowerSeries.X) ^ k) =
        if d = k then (-1 : R) ^ k * ((p.choose k / p : ℕ) : R) else 0 := by
    intro k _
    rw [neg_eq_neg_one_mul, mul_pow, show (-1 : PowerSeries R) ^ k = PowerSeries.C ((-1 : R) ^ k) by
      simp [map_pow], ← mul_assoc, ← map_mul, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow]
    split_ifs <;> ring
  rw [Finset.sum_congr rfl hterm]
  rw [Finset.sum_ite_eq]
  simp only [Finset.mem_Icc]

private lemma coeff_Pseries_X3_eq_zero {R : Type*} [CommRing R] {p d : ℕ} (hd : ¬ 3 ∣ d) (c : R) :
    PowerSeries.coeff d (Pseries (R := R) p (PowerSeries.C c * PowerSeries.X ^ 3)) = 0 := by
  unfold Pseries
  rw [map_sum]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [mul_pow, ← pow_mul, ← map_pow, ← mul_assoc, ← map_mul, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_X_pow]
  have hne : d ≠ 3 * k := fun h => hd ⟨k, h⟩
  simp [hne]

private lemma coeff_mul_eq_zero_of_dvd3 {R : Type*} [CommRing R] (A B : PowerSeries R)
    (hA : ∀ k, ¬ 3 ∣ k → PowerSeries.coeff k A = 0)
    (hB : ∀ k, ¬ 3 ∣ k → PowerSeries.coeff k B = 0)
    {d : ℕ} (hd : ¬ 3 ∣ d) :
    PowerSeries.coeff d (A * B) = 0 := by
  rw [PowerSeries.coeff_mul]
  refine Finset.sum_eq_zero fun x hx => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
  by_cases h1 : 3 ∣ x.1
  · have h2 : ¬ 3 ∣ x.2 := fun h2 => hd (hx ▸ dvd_add h1 h2)
    rw [hB x.2 h2, mul_zero]
  · rw [hA x.1 h1, zero_mul]

private lemma coeff_odd_of_even_prod {R : Type*} [CommRing R] (A B : PowerSeries R)
    (hA : ∀ k, Even k → PowerSeries.coeff k A = 0)
    (hB : ∀ k, Even k → PowerSeries.coeff k B = 0)
    {d : ℕ} (hd : Odd d) :
    PowerSeries.coeff d (A * B) = 0 := by
  rw [PowerSeries.coeff_mul]
  refine Finset.sum_eq_zero fun x hx => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
  by_cases h1 : Even x.1
  · rw [hA x.1 h1, zero_mul]
  · have h2 : Even x.2 := by
      rcases Nat.even_or_odd x.1 with h | ⟨a, ha⟩
      · exact absurd h h1
      · rcases hd with ⟨b, hb⟩
        exact ⟨b - a, by omega⟩
    rw [hB x.2 h2, mul_zero]

private lemma sum_inv_sq_mod_p {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    ∑ k ∈ Finset.Icc 1 (p - 1), ((k : ZMod p)⁻¹) ^ 2 = 0 := by
  have : Fact p.Prime := ⟨hp⟩
  have h2ne : (2 : ZMod p) ≠ 0 := fun h => by
    have hle : p ≤ 2 := Nat.le_of_dvd (by decide) ((ZMod.natCast_eq_zero_iff 2 p).mp h); omega
  have h3ne : (3 : ZMod p) ≠ 0 := fun h => by
    have hle : p ≤ 3 := Nat.le_of_dvd (by decide) ((ZMod.natCast_eq_zero_iff 3 p).mp h); omega
  have hbij : ∑ k ∈ Finset.Icc 1 (p - 1), ((k : ZMod p)⁻¹) ^ 2 = ∑ x : ZMod p, (x⁻¹) ^ 2 := by
    symm
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : ZMod p))]
    simp only [inv_zero, zero_pow (by norm_num : 2 ≠ 0), zero_add]
    refine Finset.sum_nbij (fun x => x.val) ?_ ?_ ?_ ?_
    · intro x hx
      simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hx
      simp only [Finset.mem_Icc]
      have hpos : 0 < x.val := Nat.pos_of_ne_zero fun h => hx ((ZMod.val_eq_zero x).mp h)
      have hlt : x.val < p := x.val_lt
      omega
    · intro a _ b _ h; exact ZMod.val_injective p h
    · intro k hk
      simp only [Finset.mem_coe, Finset.mem_Icc] at hk
      refine ⟨(k : ZMod p), ?_, ZMod.val_natCast_of_lt (by omega)⟩
      simp only [Finset.mem_coe, Finset.mem_erase, Finset.mem_univ, and_true]
      intro h0
      exact Nat.not_dvd_of_pos_of_lt hk.1 (by omega) ((ZMod.natCast_eq_zero_iff k p).mp h0)
    · intro x _; rw [ZMod.natCast_zmod_val]
  rw [hbij]
  have hscale : ∑ x : ZMod p, ((2 * x)⁻¹) ^ 2 = ∑ x : ZMod p, (x⁻¹) ^ 2 :=
    Equiv.sum_comp (Equiv.mulLeft₀ (2 : ZMod p) h2ne) (fun x => (x⁻¹) ^ 2)
  have h4 : ∑ x : ZMod p, ((2 * x)⁻¹) ^ 2 = ((2 : ZMod p)⁻¹) ^ 2 * ∑ x : ZMod p, (x⁻¹) ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => by rw [mul_inv, mul_pow]
  rw [h4] at hscale
  have hmul4 : (4 : ZMod p) * (((2 : ZMod p)⁻¹) ^ 2 * ∑ x : ZMod p, (x⁻¹) ^ 2) =
      ∑ x : ZMod p, (x⁻¹) ^ 2 := by
    have : (4 : ZMod p) * ((2 : ZMod p)⁻¹) ^ 2 = 1 := by
      calc (4 : ZMod p) * ((2 : ZMod p)⁻¹) ^ 2 = ((2 : ZMod p) * (2 : ZMod p)⁻¹) ^ 2 := by ring
        _ = 1 ^ 2 := by rw [mul_inv_cancel₀ h2ne]
        _ = 1 := one_pow 2
    rw [← mul_assoc, this, one_mul]
  have h3s : (3 : ZMod p) * ∑ x : ZMod p, (x⁻¹) ^ 2 = 0 := by
    have := congrArg ((4 : ZMod p) * ·) hscale
    rw [hmul4] at this
    linear_combination -this
  exact (mul_eq_zero.mp h3s).resolve_left h3ne

/--
**OEIS A333579, Conjecture 1 (Peter Bala):**
For all primes $p \ge 5$, $a(p) \equiv 2 \pmod{p^3}$, i.e., $p^3 \mid (a(p) - 2)$.
-/
theorem conjecture_1 (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) :
    ((p : ℤ) ^ 3) ∣ (a p - 2) := by
  have : NeZero (p ^ 3) := ⟨pow_ne_zero 3 hp.ne_zero⟩
  have hp_odd : Odd p := hp.odd_of_ne_two (by omega)
  have hp_ndiv3 : ¬ 3 ∣ p := fun hd =>
    (hp.eq_one_or_self_of_dvd 3 hd).elim (by decide) (by omega)
  rw [show ((p : ℤ) ^ 3) = ((p ^ 3 : ℕ) : ℤ) by push_cast; rfl,
    ← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  apply sub_eq_zero.mpr
  -- Map fSeries_mul_denom^p to PowerSeries (ZMod (p^3))
  let φ := PowerSeries.map (Int.castRingHom (ZMod (p ^ 3)))
  have hrelZ := congrArg (· ^ p) fSeries_mul_denom
  have hrel := congrArg φ hrelZ
  simp only [map_mul, map_pow, map_add, map_sub, map_one, PowerSeries.map_X, φ] at hrel
  let R := ZMod (p ^ 3)
  set F : PowerSeries R := PowerSeries.map (Int.castRingHom R) fSeries
  have ha_eq : (a p : R) = PowerSeries.coeff p (F ^ p) := by
    unfold a
    have := PowerSeries.coeff_map (Int.castRingHom R) p (fSeries ^ p)
    simpa [F, map_pow] using this.symm
  rw [ha_eq]
  -- Expand the four p-th powers in PowerSeries R
  set Px : PowerSeries R := Pseries p PowerSeries.X
  set Pnx : PowerSeries R := Pseries p (-PowerSeries.X)
  set Px3 : PowerSeries R := Pseries p (PowerSeries.X ^ 3)
  set Pnx3 : PowerSeries R := Pseries p (-PowerSeries.X ^ 3)
  have h1p : (1 + PowerSeries.X : PowerSeries R) ^ p = 1 + PowerSeries.X ^ p + (p : PowerSeries R) * Px :=
    one_add_pow_p hp PowerSeries.X
  have h1m : (1 - PowerSeries.X : PowerSeries R) ^ p = 1 - PowerSeries.X ^ p + (p : PowerSeries R) * Pnx :=
    one_sub_pow_p hp hp_odd PowerSeries.X
  have h3p : (1 + PowerSeries.X ^ 3 : PowerSeries R) ^ p = 1 + (PowerSeries.X ^ 3) ^ p + (p : PowerSeries R) * Px3 :=
    one_add_pow_p hp (PowerSeries.X ^ 3)
  have h3m : (1 - PowerSeries.X ^ 3 : PowerSeries R) ^ p = 1 - (PowerSeries.X ^ 3) ^ p + (p : PowerSeries R) * Pnx3 :=
    one_sub_pow_p hp hp_odd (PowerSeries.X ^ 3)
  -- Define G approximating F^p up to degree p
  set G : PowerSeries R :=
    (1 + 2 * PowerSeries.X ^ p) +
    (p : PowerSeries R) * (Px - Pnx + Pnx3 - Px3) +
    (p : PowerSeries R) ^ 2 *
      (Pnx ^ 2 - Px * Pnx + Px3 ^ 2 - Pnx3 * Px3 + (Px - Pnx) * (Pnx3 - Px3))
  have hp3_zero : (p : PowerSeries R) ^ 3 = 0 := by
    rw [← Nat.cast_pow, ← map_natCast PowerSeries.C (p ^ 3), ZMod.natCast_self, map_zero]
  -- Show (1 - X)^p * (1 + X^3)^p * (F^p - G) has zero coeffs for all d ≤ p!
  have hdiff_mul : ∀ d ≤ p,
      PowerSeries.coeff d (((1 - PowerSeries.X : PowerSeries R) ^ p *
        (1 + PowerSeries.X ^ 3 : PowerSeries R) ^ p) * (F ^ p - G)) = 0 := by
    intro d hd
    rw [mul_sub]
    have hFrel : (1 - PowerSeries.X : PowerSeries R) ^ p * (1 + PowerSeries.X ^ 3 : PowerSeries R) ^ p * F ^ p =
        (1 + PowerSeries.X : PowerSeries R) ^ p * (1 - PowerSeries.X ^ 3 : PowerSeries R) ^ p := by
      calc (1 - PowerSeries.X : PowerSeries R) ^ p * (1 + PowerSeries.X ^ 3 : PowerSeries R) ^ p * F ^ p
          = ((1 - PowerSeries.X : PowerSeries R) * (1 + PowerSeries.X ^ 3 : PowerSeries R) * F) ^ p := by
              rw [mul_pow, mul_pow]
        _ = ((1 + PowerSeries.X : PowerSeries R) * (1 - PowerSeries.X ^ 3 : PowerSeries R)) ^ p := hrel
        _ = (1 + PowerSeries.X : PowerSeries R) ^ p * (1 - PowerSeries.X ^ 3 : PowerSeries R) ^ p := by
              rw [mul_pow]
    rw [hFrel, h1p, h1m, h3p, h3m]
    -- Every nonzero term in the difference has a factor of X^(p+1), X^(2p), or p^3!
    -- Helper: coeff d (X^m * A) = 0 whenever d < m
    have hXm : ∀ (m : ℕ) (A : PowerSeries R), d < m → PowerSeries.coeff d (PowerSeries.X ^ m * A) = 0 := by
      intro m A hdm
      rw [PowerSeries.coeff_mul]
      refine Finset.sum_eq_zero fun x hx => ?_
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
      rw [PowerSeries.coeff_X_pow]
      have : x.1 ≠ m := by omega
      simp [this]
    -- Also Px, Pnx, Px3, Pnx3 all have constantCoeff = 0, so X ∣ each of them!
    have hX_dvd_P : ∀ (Q : PowerSeries R), PowerSeries.constantCoeff Q = 0 →
        ∃ Q', Q = PowerSeries.X * Q' := fun Q hQ =>
      PowerSeries.X_dvd_iff.mpr hQ
    have hcPx : PowerSeries.constantCoeff Px = 0 := by
      rw [← PowerSeries.coeff_zero_eq_constantCoeff, coeff_Pseries_X]; simp
    have hcPnx : PowerSeries.constantCoeff Pnx = 0 := by
      rw [← PowerSeries.coeff_zero_eq_constantCoeff, coeff_Pseries_neg_X]; simp
    have hcPx3 : PowerSeries.constantCoeff Px3 = 0 := by
      rw [← PowerSeries.coeff_zero_eq_constantCoeff]
      have h0 : Px3 = Pseries p (PowerSeries.C (1 : R) * PowerSeries.X ^ 3) := by simp [Px3]
      rw [h0]; unfold Pseries; rw [map_sum]
      refine Finset.sum_eq_zero fun k hk => ?_
      simp only [Finset.mem_Icc] at hk
      rw [mul_pow, ← pow_mul, map_one, one_pow, one_mul, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow]
      have : 0 ≠ 3 * k := by omega
      simp [this]
    have hcPnx3 : PowerSeries.constantCoeff Pnx3 = 0 := by
      rw [← PowerSeries.coeff_zero_eq_constantCoeff]
      have h0 : Pnx3 = Pseries p (PowerSeries.C (-1 : R) * PowerSeries.X ^ 3) := by
        dsimp only [Pnx3]; congr 1; simp; ring
      rw [h0]; unfold Pseries; rw [map_sum]
      refine Finset.sum_eq_zero fun k hk => ?_
      simp only [Finset.mem_Icc] at hk
      rw [mul_pow, ← pow_mul, ← map_pow, ← mul_assoc, ← map_mul, PowerSeries.coeff_C_mul,
        PowerSeries.coeff_X_pow]
      have : 0 ≠ 3 * k := by omega
      simp [this]
    obtain ⟨Px', hPx'⟩ := hX_dvd_P Px hcPx
    obtain ⟨Pnx', hPnx'⟩ := hX_dvd_P Pnx hcPnx
    obtain ⟨Px3', hPx3'⟩ := hX_dvd_P Px3 hcPx3
    obtain ⟨Pnx3', hPnx3'⟩ := hX_dvd_P Pnx3 hcPnx3
    -- Work in the quotient ring PowerSeries R ⧸ Ideal.span {X^(p+1)}!
    let I := Ideal.span ({PowerSeries.X ^ (p + 1)} : Set (PowerSeries R))
    let q := Ideal.Quotient.mk I
    have hq_Xp1 : q (PowerSeries.X ^ (p + 1)) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
    have hq_pow : ∀ m, p + 1 ≤ m → q (PowerSeries.X ^ m) = 0 := fun m hm => by
      rw [show m = (p + 1) + (m - (p + 1)) by omega, pow_add, map_mul, hq_Xp1, zero_mul]
    have hq_X2p : q (PowerSeries.X ^ p) ^ 2 = 0 := by
      rw [← map_pow, ← pow_mul]; exact hq_pow (p * 2) (by omega)
    have hq_X3p : (q PowerSeries.X ^ 3) ^ p = 0 := by
      rw [← map_pow, ← map_pow, ← pow_mul]; exact hq_pow (3 * p) (by omega)
    have hq_Xp_mul : ∀ Q Q' : PowerSeries R, Q = PowerSeries.X * Q' →
        q PowerSeries.X ^ p * q Q = 0 := fun Q Q' hQ => by
      rw [hQ, map_mul, ← mul_assoc, ← map_pow, ← map_mul, ← pow_succ, hq_Xp1, zero_mul]
    have hq_p3 : (q (p : PowerSeries R)) ^ 3 = 0 := by rw [← map_pow, hp3_zero, map_zero]
    have hq_X2p' : (q PowerSeries.X ^ p) ^ 2 = 0 := by
      rw [← map_pow]; exact hq_X2p
    have hq_zero : q ((1 + PowerSeries.X ^ p + (p : PowerSeries R) * Px) *
          (1 - (PowerSeries.X ^ 3) ^ p + (p : PowerSeries R) * Pnx3) -
        (1 - PowerSeries.X ^ p + (p : PowerSeries R) * Pnx) *
          (1 + (PowerSeries.X ^ 3) ^ p + (p : PowerSeries R) * Px3) * G) = 0 := by
      simp only [G, map_sub, map_add, map_mul, map_pow, map_one, map_ofNat]
      rw [hq_X3p]
      set x := q PowerSeries.X ^ p
      set P := q (p : PowerSeries R)
      set a := q Px
      set b := q Pnx
      set c := q Px3
      set d := q Pnx3
      have h1 : x * a = 0 := hq_Xp_mul Px Px' hPx'
      have h2 : x * b = 0 := hq_Xp_mul Pnx Pnx' hPnx'
      have h3 : x * c = 0 := hq_Xp_mul Px3 Px3' hPx3'
      have h4 : x * d = 0 := hq_Xp_mul Pnx3 Pnx3' hPnx3'
      have hL : (1 + x + P * a) * (1 - 0 + P * d) = 1 + x + P * (a + d) + P ^ 2 * (a * d) := by
        linear_combination P * h4
      have hR1 : (1 - x + P * b) * (1 + 0 + P * c) = 1 - x + P * (b + c) + P ^ 2 * (b * c) := by
        linear_combination -P * h3
      have hR2 : (1 - x + P * (b + c) + P ^ 2 * (b * c)) *
            (1 + 2 * x + P * (a - b + d - c) +
              P ^ 2 * (b ^ 2 - a * b + c ^ 2 - d * c + (a - b) * (d - c))) =
          1 + x + P * (a + d) + P ^ 2 * (a * d) := by
        have hxG : x * (P * (a - b + d - c) + P ^ 2 * (b ^ 2 - a * b + c ^ 2 - d * c + (a - b) * (d - c))) = 0 := by
          linear_combination P * (h1 - h2 + h4 - h3) +
            P ^ 2 * (b * h2 - a * h2 + c * h3 - d * h3 + (d - c) * h1 - (d - c) * h2)
        have h2xP : (2 * x) * (P * (b + c) + P ^ 2 * (b * c)) = 0 := by
          linear_combination 2 * P * (h2 + h3) + 2 * P ^ 2 * c * h2
        linear_combination -2 * hq_X2p' - hxG + h2xP +
          ((b + c) * (b ^ 2 - a * b + c ^ 2 - d * c + (a - b) * (d - c)) +
           b * c * (a - b + d - c) +
           P * b * c * (b ^ 2 - a * b + c ^ 2 - d * c + (a - b) * (d - c))) * hq_p3
      rw [hL, hR1, hR2, sub_self]
    have hdvd_Xp1 : PowerSeries.X ^ (p + 1) ∣
        ((1 + PowerSeries.X ^ p + (p : PowerSeries R) * Px) *
          (1 - (PowerSeries.X ^ 3) ^ p + (p : PowerSeries R) * Pnx3) -
        (1 - PowerSeries.X ^ p + (p : PowerSeries R) * Pnx) *
          (1 + (PowerSeries.X ^ 3) ^ p + (p : PowerSeries R) * Px3) * G) :=
      Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hq_zero)
    obtain ⟨W, hW⟩ := hdvd_Xp1
    rw [hW]
    exact hXm (p + 1) W (by omega)
  -- Deduce coeff p (F^p) = coeff p G
  have hu0 : PowerSeries.constantCoeff
      ((1 - PowerSeries.X : PowerSeries R) ^ p * (1 + PowerSeries.X ^ 3 : PowerSeries R) ^ p) = 1 := by
    simp
  have hFG : PowerSeries.coeff p (F ^ p - G) = 0 :=
    coeff_eq_zero_of_mul_eq_zero _ _ hu0 p hdiff_mul p le_rfl
  rw [map_sub, sub_eq_zero] at hFG
  rw [hFG]
  -- Evaluate coeff p G = 2 in ZMod (p^3)!
  have hC_p : PowerSeries.coeff p (1 + 2 * PowerSeries.X ^ p : PowerSeries R) = 2 := by
    rw [map_add, PowerSeries.coeff_one, if_neg hp.ne_zero, zero_add,
      show (2 : PowerSeries R) = PowerSeries.C (2 : R) from (map_ofNat PowerSeries.C 2).symm,
      PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow, if_pos rfl, mul_one]
  have hPx_p : PowerSeries.coeff p Px = 0 := by rw [coeff_Pseries_X]; simp; omega
  have hPnx_p : PowerSeries.coeff p Pnx = 0 := by rw [coeff_Pseries_neg_X]; simp; omega
  have hPx3_ndiv : ∀ k, ¬ 3 ∣ k → PowerSeries.coeff k Px3 = 0 := fun k hk => by
    have : Px3 = Pseries p (PowerSeries.C (1 : R) * PowerSeries.X ^ 3) := by simp [Px3]
    rw [this]; exact coeff_Pseries_X3_eq_zero hk 1
  have hPnx3_ndiv : ∀ k, ¬ 3 ∣ k → PowerSeries.coeff k Pnx3 = 0 := fun k hk => by
    have : Pnx3 = Pseries p (PowerSeries.C (-1 : R) * PowerSeries.X ^ 3) := by
      dsimp only [Pnx3]; congr 1; simp; ring
    rw [this]; exact coeff_Pseries_X3_eq_zero hk (-1)
  have hPx3_p : PowerSeries.coeff p Px3 = 0 := hPx3_ndiv p hp_ndiv3
  have hPnx3_p : PowerSeries.coeff p Pnx3 = 0 := hPnx3_ndiv p hp_ndiv3
  have hPx3sq_p : PowerSeries.coeff p (Px3 ^ 2) = 0 := by
    rw [sq]; exact coeff_mul_eq_zero_of_dvd3 Px3 Px3 hPx3_ndiv hPx3_ndiv hp_ndiv3
  have hPnx3Px3_p : PowerSeries.coeff p (Pnx3 * Px3) = 0 :=
    coeff_mul_eq_zero_of_dvd3 Pnx3 Px3 hPnx3_ndiv hPx3_ndiv hp_ndiv3
  -- Px * Pnx is even, so coeff p (Px * Pnx) = 0!
  have hPxPnx_p : PowerSeries.coeff p (Px * Pnx) = 0 := by
    rw [PowerSeries.coeff_mul]
    have hpair : ∑ x ∈ Finset.HasAntidiagonal.antidiagonal p, PowerSeries.coeff x.1 Px * PowerSeries.coeff x.2 Pnx =
        ∑ x ∈ Finset.HasAntidiagonal.antidiagonal p, -(PowerSeries.coeff x.1 Px * PowerSeries.coeff x.2 Pnx) := by
      refine Finset.sum_nbij (fun x => (x.2, x.1)) ?_ ?_ ?_ ?_
      · intro x hx; rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx ⊢; omega
      · intro a _ b _ h; exact Prod.ext (congrArg Prod.snd h) (congrArg Prod.fst h)
      · intro x hx; rw [Finset.mem_coe, Finset.HasAntidiagonal.mem_antidiagonal] at hx
        exact ⟨(x.2, x.1), by rw [Finset.mem_coe, Finset.HasAntidiagonal.mem_antidiagonal]; omega, rfl⟩
      · intro x hx
        rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
        dsimp only [Px, Pnx]
        simp only [coeff_Pseries_X, coeff_Pseries_neg_X]
        by_cases h1 : 1 ≤ x.1 ∧ x.1 ≤ p - 1
        · have h2 : 1 ≤ x.2 ∧ x.2 ≤ p - 1 := by omega
          rw [if_pos h1, if_pos h2, if_pos h2, if_pos h1]
          have hsign : (-1 : R) ^ x.2 = -((-1 : R) ^ x.1) := by
            have hsum : (-1 : R) ^ x.1 * (-1 : R) ^ x.2 = -1 := by
              rw [← pow_add, hx]
              rcases hp_odd with ⟨m, rfl⟩
              rw [pow_succ, pow_mul]; norm_num
            have hsq : ((-1 : R) ^ x.1) ^ 2 = 1 := by
              rw [← pow_mul, mul_comm, pow_mul]; norm_num
            linear_combination ((-1 : R) ^ x.1) * hsum - ((-1 : R) ^ x.2) * hsq
          rw [hsign]; ring
        · have h2 : ¬ (1 ≤ x.2 ∧ x.2 ≤ p - 1) := by omega
          rw [if_neg h1, if_neg h2, if_neg h2, if_neg h1]; ring
    rw [Finset.sum_neg_distrib] at hpair
    have h2unit : IsUnit (2 : R) := by
      rw [show (2 : R) = ((2 : ℕ) : ZMod (p ^ 3)) by rfl, ZMod.isUnit_iff_coprime]
      exact ((hp.coprime_iff_not_dvd.mpr fun hd => by
        have hle : p ≤ 2 := Nat.le_of_dvd (by decide) hd; omega).symm).pow_right 3
    have h2s : (2 : R) * ∑ x ∈ Finset.HasAntidiagonal.antidiagonal p, PowerSeries.coeff x.1 Px * PowerSeries.coeff x.2 Pnx = 0 := by
      linear_combination hpair
    exact h2unit.mul_left_cancel (by rw [h2s, mul_zero])
  -- (Px - Pnx) and (Pnx3 - Px3) are both odd series, so their product has coeff p = 0!
  have hodd1 : ∀ k, Even k → PowerSeries.coeff k (Px - Pnx) = 0 := fun k hk => by
    rw [map_sub, coeff_Pseries_X, coeff_Pseries_neg_X]
    rcases hk with ⟨t, rfl⟩
    have h1 : (-1 : R) ^ (t + t) = 1 := by rw [← two_mul, pow_mul]; norm_num
    rw [h1, one_mul, sub_self]
  have hodd2 : ∀ k, Even k → PowerSeries.coeff k (Pnx3 - Px3) = 0 := fun k hk => by
    rw [map_sub]
    by_cases h3 : 3 ∣ k
    · obtain ⟨m, rfl⟩ := h3
      have hm_even : Even m := by
        rcases Nat.even_or_odd m with h | ⟨t, rfl⟩
        · exact h
        · exfalso; rcases hk with ⟨s, hs⟩; omega
      have h1 : PowerSeries.coeff (3 * m) Pnx3 =
          if 1 ≤ m ∧ m ≤ p - 1 then (-1 : R) ^ m * ((p.choose m / p : ℕ) : R) else 0 := by
        have hP : Pnx3 = Pseries p (PowerSeries.C (-1 : R) * PowerSeries.X ^ 3) := by
          dsimp only [Pnx3]; congr 1; simp; ring
        rw [hP]; unfold Pseries; rw [map_sum]
        have ht : ∀ j ∈ Finset.Icc 1 (p - 1),
            PowerSeries.coeff (3 * m) (PowerSeries.C (((p.choose j / p : ℕ) : R)) *
              (PowerSeries.C (-1 : R) * PowerSeries.X ^ 3) ^ j) =
            if m = j then (-1 : R) ^ j * ((p.choose j / p : ℕ) : R) else 0 := by
          intro j _
          rw [mul_pow, ← pow_mul, ← map_pow, ← mul_assoc, ← map_mul, PowerSeries.coeff_C_mul,
            PowerSeries.coeff_X_pow]
          have hiff : 3 * m = 3 * j ↔ m = j := by omega
          simp only [hiff]
          split_ifs <;> ring
        rw [Finset.sum_congr rfl ht, Finset.sum_ite_eq]; simp only [Finset.mem_Icc]
      have h2 : PowerSeries.coeff (3 * m) Px3 =
          if 1 ≤ m ∧ m ≤ p - 1 then ((p.choose m / p : ℕ) : R) else 0 := by
        have hP : Px3 = Pseries p (PowerSeries.C (1 : R) * PowerSeries.X ^ 3) := by simp [Px3]
        rw [hP]; unfold Pseries; rw [map_sum]
        have ht : ∀ j ∈ Finset.Icc 1 (p - 1),
            PowerSeries.coeff (3 * m) (PowerSeries.C (((p.choose j / p : ℕ) : R)) *
              (PowerSeries.C (1 : R) * PowerSeries.X ^ 3) ^ j) =
            if m = j then ((p.choose j / p : ℕ) : R) else 0 := by
          intro j _
          rw [mul_pow, ← pow_mul, map_one, one_pow, one_mul, PowerSeries.coeff_C_mul,
            PowerSeries.coeff_X_pow]
          have hiff : 3 * m = 3 * j ↔ m = j := by omega
          simp only [hiff]
          split_ifs <;> ring
        rw [Finset.sum_congr rfl ht, Finset.sum_ite_eq]; simp only [Finset.mem_Icc]
      rw [h1, h2]
      rcases hm_even with ⟨t, rfl⟩
      have hpow : (-1 : R) ^ (t + t) = 1 := by rw [← two_mul, pow_mul]; norm_num
      rw [hpow, one_mul, sub_self]
    · rw [hPnx3_ndiv k h3, hPx3_ndiv k h3, sub_self]
  have hcross_p : PowerSeries.coeff p ((Px - Pnx) * (Pnx3 - Px3)) = 0 :=
    coeff_odd_of_even_prod _ _ hodd1 hodd2 hp_odd
  -- Finally: p^2 * coeff p (Pnx^2) = 0 in ZMod (p^3) because coeff p (Pnx^2) ≡ -∑ k⁻² ≡ 0 (mod p)!
  have hp2_Pnxsq : (p : R) ^ 2 * PowerSeries.coeff p (Pnx ^ 2) = 0 := by
    have hcoeff_p : p ∣ ZMod.val (PowerSeries.coeff p (Pnx ^ 2)) := by
      have hcast : ZMod.castHom (dvd_pow_self p (by norm_num : 3 ≠ 0)) (ZMod p)
          (PowerSeries.coeff p (Pnx ^ 2)) = 0 := by
        rw [sq, PowerSeries.coeff_mul, map_sum]
        have hre : ∑ x ∈ Finset.HasAntidiagonal.antidiagonal p,
              ZMod.castHom (dvd_pow_self p (by norm_num : 3 ≠ 0)) (ZMod p)
                (PowerSeries.coeff x.1 Pnx * PowerSeries.coeff x.2 Pnx) =
            ∑ k ∈ Finset.Icc 1 (p - 1), -(((k : ZMod p)⁻¹) ^ 2) := by
          have hzero_out : ∀ x ∈ Finset.HasAntidiagonal.antidiagonal p,
              ¬ (1 ≤ x.1 ∧ x.1 ≤ p - 1) →
              ZMod.castHom (dvd_pow_self p (by norm_num : 3 ≠ 0)) (ZMod p)
                (PowerSeries.coeff x.1 Pnx * PowerSeries.coeff x.2 Pnx) = 0 := by
            intro x _ hx
            rw [coeff_Pseries_neg_X, if_neg hx, zero_mul, map_zero]
          rw [← Finset.sum_filter_of_ne (fun x hx hne => by_contra fun h => hne (hzero_out x hx h))]
          symm
          refine Finset.sum_nbij (fun k => (k, p - k)) ?_ ?_ ?_ ?_
          · intro k hk; simp only [Finset.mem_Icc] at hk
            simp only [Finset.mem_filter, Finset.HasAntidiagonal.mem_antidiagonal]; omega
          · intro a _ b _ h; exact congrArg Prod.fst h
          · intro x hx
            simp only [Finset.mem_coe, Finset.mem_filter, Finset.HasAntidiagonal.mem_antidiagonal] at hx
            exact ⟨x.1, by simp only [Finset.mem_coe, Finset.mem_Icc]; omega,
              Prod.ext rfl (by dsimp only; omega)⟩
          · intro k hk
            simp only [Finset.mem_Icc] at hk
            dsimp only
            rw [map_mul, coeff_Pseries_neg_X, coeff_Pseries_neg_X, if_pos hk,
              if_pos (by omega : 1 ≤ p - k ∧ p - k ≤ p - 1)]
            simp only [map_mul, map_pow, map_neg, map_one, map_natCast]
            -- C(p, k) / p ≡ (-1)^(k-1) / k (mod p), and C(p, p-k) = C(p, k)!
            have hch_symm : p.choose (p - k) = p.choose k := Nat.choose_symm (by omega)
            rw [hch_symm]
            have hck_mod : ((p.choose k / p : ℕ) : ZMod p) = (-1 : ZMod p) ^ (k - 1) * (k : ZMod p)⁻¹ := by
              have hnat : k * (p.choose k / p) = (p - 1).choose (k - 1) := by
                apply Nat.eq_of_mul_eq_mul_left hp.pos
                have h1 : k * p.choose k = p * (p - 1).choose (k - 1) := by
                  have := Nat.add_one_mul_choose_eq (p - 1) (k - 1)
                  rw [Nat.sub_add_cancel hp.one_le, Nat.sub_add_cancel hk.1] at this
                  rw [mul_comm, ← this]
                have hdiv := Nat.mul_div_cancel' (hp.dvd_choose_self (Nat.pos_iff_ne_zero.mp hk.1)
                  (Nat.lt_of_le_pred hp.pos hk.2))
                calc p * (k * (p.choose k / p)) = k * (p * (p.choose k / p)) := by ring
                  _ = k * p.choose k := by rw [hdiv]
                  _ = p * (p - 1).choose (k - 1) := h1
              have hch_pm1 : (((p - 1).choose (k - 1) : ℕ) : ZMod p) = (-1 : ZMod p) ^ (k - 1) := by
                have hfac : ∀ m < p, ((m.factorial : ℕ) : ZMod p) * (((p - 1).choose m : ℕ) : ZMod p) =
                    (-1 : ZMod p) ^ m * ((m.factorial : ℕ) : ZMod p) := by
                  intro m hm
                  induction m with
                  | zero => simp
                  | succ m ih =>
                    have hch : (p - 1).choose (m + 1) * (m + 1) = (p - 1).choose m * (p - 1 - m) :=
                      Nat.choose_succ_right_eq (p - 1) m
                    have hchZ := congrArg (Nat.cast (R := ZMod p)) hch
                    push_cast at hchZ
                    have hsub : ((p - 1 - m : ℕ) : ZMod p) = -((m : ZMod p) + 1) := by
                      rw [show p - 1 - m = p - (m + 1) by omega, Nat.cast_sub (by omega),
                        ZMod.natCast_self, zero_sub]; push_cast; ring
                    rw [hsub] at hchZ
                    rw [Nat.factorial_succ]; push_cast
                    rw [pow_succ]
                    linear_combination (m.factorial : ZMod p) * hchZ - ((m : ZMod p) + 1) * ih (by omega)
                have : Fact p.Prime := ⟨hp⟩
                have hfnz : (((k - 1).factorial : ℕ) : ZMod p) ≠ 0 := fun h => by
                  have hd := (ZMod.natCast_eq_zero_iff _ p).mp h
                  have := hp.dvd_factorial.mp hd; omega
                exact mul_left_cancel₀ hfnz (by rw [hfac (k - 1) (by omega)]; ring)
              have hZ := congrArg (Nat.cast (R := ZMod p)) hnat
              push_cast at hZ
              rw [hch_pm1] at hZ
              have : Fact p.Prime := ⟨hp⟩
              have hkne : (k : ZMod p) ≠ 0 := fun h =>
                Nat.not_dvd_of_pos_of_lt hk.1 (by omega) ((ZMod.natCast_eq_zero_iff k p).mp h)
              apply mul_left_cancel₀ hkne
              rw [hZ]
              calc (-1 : ZMod p) ^ (k - 1)
                  = (k : ZMod p) * (k : ZMod p)⁻¹ * (-1 : ZMod p) ^ (k - 1) := by
                      rw [mul_inv_cancel₀ hkne, one_mul]
                _ = (k : ZMod p) * ((-1 : ZMod p) ^ (k - 1) * (k : ZMod p)⁻¹) := by ring
            rw [hck_mod]
            have hsign1 : (-1 : ZMod p) ^ k * (-1 : ZMod p) ^ (p - k) = -1 := by
              rw [← pow_add, Nat.add_sub_cancel' (by omega)]
              rcases hp_odd with ⟨m, rfl⟩
              rw [pow_succ, pow_mul]; norm_num
            have hsign2 : ((-1 : ZMod p) ^ (k - 1)) ^ 2 = 1 := by
              rw [← pow_mul, mul_comm, pow_mul]; norm_num
            symm
            calc (-1 : ZMod p) ^ k * ((-1 : ZMod p) ^ (k - 1) * (k : ZMod p)⁻¹) *
                    ((-1 : ZMod p) ^ (p - k) * ((-1 : ZMod p) ^ (k - 1) * (k : ZMod p)⁻¹))
                = ((-1 : ZMod p) ^ k * (-1 : ZMod p) ^ (p - k)) *
                    (((-1 : ZMod p) ^ (k - 1)) ^ 2) * ((k : ZMod p)⁻¹) ^ 2 := by ring
              _ = -(((k : ZMod p)⁻¹) ^ 2) := by rw [hsign1, hsign2]; ring
        rw [hre, Finset.sum_neg_distrib, sum_inv_sq_mod_p hp hp5, neg_zero]
      rw [ZMod.castHom_apply, ZMod.cast_eq_val] at hcast
      exact (ZMod.natCast_eq_zero_iff _ _).mp hcast
    rw [← ZMod.natCast_zmod_val (PowerSeries.coeff p (Pnx ^ 2)), ← Nat.cast_pow, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_zero_iff _ _).mpr
    exact dvd_trans (dvd_of_eq (by ring)) (mul_dvd_mul_left (p ^ 2) hcoeff_p)
  -- Put all terms of coeff p G together!
  have hG_p : PowerSeries.coeff p G = 2 := by
    change PowerSeries.coeff p ((1 + 2 * PowerSeries.X ^ p) +
      (p : PowerSeries R) * (Px - Pnx + Pnx3 - Px3) +
      (p : PowerSeries R) ^ 2 *
        (Pnx ^ 2 - Px * Pnx + Px3 ^ 2 - Pnx3 * Px3 + (Px - Pnx) * (Pnx3 - Px3))) = 2
    rw [map_add, map_add, hC_p]
    have hpC : (p : PowerSeries R) = PowerSeries.C (p : R) := by simp
    rw [hpC, ← map_pow, PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul]
    simp only [map_add, map_sub, hPx_p, hPnx_p, hPx3_p, hPnx3_p, hPxPnx_p, hPx3sq_p,
      hPnx3Px3_p, hcross_p, sub_zero, add_zero, mul_zero]
    rw [hp2_Pnxsq, add_zero]
  rw [hG_p]


end SolvedConjecture06

/-!
OEIS A333579, prime power case: for f = (1 + x + x^2)/(1 - x + x^2) and a(n) = [x^n] f^n,
a(p^k) = a(p^(k-1)) modulo p^(2k) for every prime p >= 5 and every k >= 1.

Write N = p^k, Q = p^(k-1). Call an integer power series D small if N divides every coefficient
of D and N^2 divides the coefficients whose index is a multiple of p (`InI`).

1. Binomial part. With X = prod (N - j) and Y = prod j over the j < p*b prime to p one has
   C(N, p*b) * Y = C(Q, b) * X. The reflection j -> p*b - j gives X^2 = Y^2 modulo N * p^(s+1)
   and X = Y modulo p^(s+1) whenever p^s divides b, hence X = Y modulo N * p^(s+1) for odd p.
   Since p^(k-1-s) divides C(Q, b) for s the exact power of p in b, N^2 divides
   C(N, p*b) - C(Q, b). Also N divides C(N, i) when p does not divide i.
2. Hence (1 + c x^e)^N - (1 + c x^(e p))^Q is small for c = 1, -1 and e = 1, 3 (p is odd and
   prime to 3).
3. From (1 - x)(1 + x^3) f = (1 + x)(1 - x^3), raised to the powers N and Q (the latter expanded
   by x -> x^p), the series (f^N - expand_p (f^Q)) * ((1 - x)(1 + x^3))^N is small, and division
   by a series with constant coefficient 1 whose coefficients off the multiples of p are
   divisible by N keeps smallness. The coefficient of x^N gives the claim.
-/

open Finset

namespace A333579H2

/-- One step of the binomial recursion, over `ℤ`, with no side condition. -/
private lemma choose_succ_int (n m : ℕ) :
    ((n.choose (m + 1) : ℕ) : ℤ) * ((m : ℤ) + 1) = (n.choose m : ℤ) * ((n : ℤ) - m) := by
  rcases le_or_gt m n with h | h
  · have h1 := Nat.choose_succ_right_eq n m
    have h2 : ((n - m : ℕ) : ℤ) = (n : ℤ) - m := Nat.cast_sub h
    rw [← h2]
    exact_mod_cast h1
  · rw [Nat.choose_eq_zero_of_lt h, Nat.choose_eq_zero_of_lt (by omega)]
    simp

/-- `r` steps of the binomial recursion. -/
private lemma choose_add_int (n m r : ℕ) :
    ((n.choose (m + r) : ℕ) : ℤ) * ∏ t ∈ range r, ((m : ℤ) + t + 1) =
      (n.choose m : ℤ) * ∏ t ∈ range r, ((n : ℤ) - m - t) := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [prod_range_succ, prod_range_succ, ← add_assoc]
    have h := choose_succ_int n (m + r)
    push_cast at h
    linear_combination (∏ t ∈ range r, ((m : ℤ) + t + 1)) * h + ((n : ℤ) - m - r) * ih

/-- The product of `g j` over the `j = p * i + t + 1` with `i < b`, `t < p - 1`
(these are the `j < p * b` that are not multiples of `p`). -/
private def uprod (p b : ℕ) (g : ℕ → ℤ) : ℤ :=
  ∏ i ∈ range b, ∏ t ∈ range (p - 1), g (p * i + t + 1)

private lemma uprod_succ (p b : ℕ) (g : ℕ → ℤ) :
    uprod p (b + 1) g = uprod p b g * ∏ t ∈ range (p - 1), g (p * b + t + 1) := by
  unfold uprod
  rw [prod_range_succ]

private lemma uprod_mul (p b : ℕ) (g h : ℕ → ℤ) :
    uprod p b g * uprod p b h = uprod p b (fun j => g j * h j) := by
  unfold uprod
  rw [← prod_mul_distrib]
  refine prod_congr rfl fun i _ => ?_
  rw [← prod_mul_distrib]

private lemma uprod_modEq (p b : ℕ) (g h : ℕ → ℤ) (M : ℤ)
    (H : ∀ i < b, ∀ t < p - 1, g (p * i + t + 1) ≡ h (p * i + t + 1) [ZMOD M]) :
    uprod p b g ≡ uprod p b h [ZMOD M] := by
  unfold uprod
  refine Int.ModEq.prod fun i hi => Int.ModEq.prod fun t ht => ?_
  exact H i (mem_range.mp hi) t (mem_range.mp ht)

/-- Reflection `j ↦ p * b - j`. -/
private lemma uprod_reflect (p b : ℕ) (g : ℕ → ℤ) :
    uprod p b g = uprod p b (fun j => g (p * b - j)) := by
  unfold uprod
  have h1 : ∏ i ∈ range b, ∏ t ∈ range (p - 1), g (p * i + t + 1)
      = ∏ i ∈ range b, ∏ t ∈ range (p - 1), g (p * (b - 1 - i) + t + 1) :=
    (prod_range_reflect (fun i => ∏ t ∈ range (p - 1), g (p * i + t + 1)) b).symm
  rw [h1]
  refine prod_congr rfl fun i hi => ?_
  have h2 : ∏ t ∈ range (p - 1), g (p * (b - 1 - i) + t + 1)
      = ∏ t ∈ range (p - 1), g (p * (b - 1 - i) + (p - 1 - 1 - t) + 1) :=
    (prod_range_reflect (fun t => g (p * (b - 1 - i) + t + 1)) (p - 1)).symm
  rw [h2]
  refine prod_congr rfl fun t ht => ?_
  rw [mem_range] at hi ht
  show g (p * (b - 1 - i) + (p - 1 - 1 - t) + 1) = g (p * b - (p * i + t + 1))
  congr 1
  obtain ⟨d, rfl⟩ : ∃ d, b = i + 1 + d := ⟨b - (i + 1), by omega⟩
  have h3 : i + 1 + d - 1 - i = d := by omega
  rw [h3]
  have h4 : p * (i + 1 + d) = p * i + p + p * d := by ring
  rw [h4]
  omega

/-- The units `j < p * b` are at most `p * b`. -/
private lemma unit_le {p b i t : ℕ} (hi : i < b) (ht : t < p - 1) : p * i + t + 1 ≤ p * b := by
  have h1 : p * (i + 1) ≤ p * b := Nat.mul_le_mul_left p hi
  have h2 : p * (i + 1) = p * i + p := by ring
  omega

/-- Product formula: `C(pa, pb) * ∏ j = C(a, b) * ∏ (pa - j)`, the products over the units
`j < p * b`. -/
private lemma choose_mul_uprod (p a b : ℕ) (hp : 0 < p) :
    ((p * a).choose (p * b) : ℤ) * uprod p b (fun j => (j : ℤ)) =
      (a.choose b : ℤ) * uprod p b (fun j => ((p * a : ℕ) : ℤ) - j) := by
  induction b with
  | zero => simp [uprod]
  | succ b ih =>
    rw [uprod_succ, uprod_succ]
    have hstep := choose_add_int (p * a) (p * b) p
    obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
    rw [prod_range_succ, prod_range_succ'] at hstep
    have hc := choose_succ_int a b
    have e1 : ∏ t ∈ range (q + 1 - 1), (((q + 1) * b + t + 1 : ℕ) : ℤ)
        = ∏ t ∈ range q, ((((q + 1) * b : ℕ) : ℤ) + t + 1) := by
      rw [Nat.add_sub_cancel]
      refine prod_congr rfl fun t _ => ?_
      push_cast; ring
    have e2 : ∏ t ∈ range (q + 1 - 1), ((((q + 1) * a : ℕ) : ℤ) - (((q + 1) * b + t + 1 : ℕ) : ℤ))
        = ∏ t ∈ range q, ((((q + 1) * a : ℕ) : ℤ) - (((q + 1) * b : ℕ) : ℤ) - ((t + 1 : ℕ) : ℤ)) := by
      rw [Nat.add_sub_cancel]
      refine prod_congr rfl fun t _ => ?_
      push_cast; ring
    rw [e1, e2]
    have hne : (((q + 1 : ℕ) : ℤ) * ((b : ℤ) + 1)) ≠ 0 := by positivity
    have hmul : ((q + 1 : ℕ) : ℤ) * (b + 1 : ℕ) = (((q + 1) * (b + 1) : ℕ) : ℤ) := by push_cast; ring
    apply mul_left_cancel₀ hne
    have hidx : (q + 1) * (b + 1) = (q + 1) * b + (q + 1) := by ring
    rw [hidx]
    push_cast at hstep ih hc ⊢
    linear_combination (uprod (q + 1) b (fun j => (j : ℤ))) * hstep
      + (∏ t ∈ range q, (((q : ℤ) + 1) * a - ((q : ℤ) + 1) * b - ((t : ℤ) + 1))) * ((q : ℤ) + 1) * ((a : ℤ) - b) * ih
      - (∏ t ∈ range q, (((q : ℤ) + 1) * a - ((q : ℤ) + 1) * b - ((t : ℤ) + 1))) * ((q : ℤ) + 1)
          * (uprod (q + 1) b (fun j => (((q : ℤ) + 1) * a) - j)) * hc

private lemma not_dvd_uprod_id {p : ℕ} (hp : p.Prime) (b : ℕ) :
    ¬ (p : ℤ) ∣ uprod p b (fun j => (j : ℤ)) := by
  unfold uprod
  have hpi : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  intro h
  rw [hpi.dvd_finsetProd_iff] at h
  obtain ⟨i, _, h⟩ := h
  rw [hpi.dvd_finsetProd_iff] at h
  obtain ⟨t, ht, h⟩ := h
  rw [mem_range] at ht
  have h' : p ∣ p * i + (t + 1) := by
    have := Int.natCast_dvd_natCast.mp h
    rwa [add_assoc] at this
  have h'' : p ∣ t + 1 := (Nat.dvd_add_right (dvd_mul_right p i)).mp h'
  have := Nat.le_of_dvd (by omega) h''
  omega

/-- `X ≡ Y` modulo `N * p ^ (s + 1)`, where `X = ∏ (N - j)`, `Y = ∏ j` over the units `j < p * b`,
when `p ^ (s + 1)` divides both `N` and `p * b`, and `N` is a power of the odd prime `p`. -/
private lemma uprod_sub_dvd {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (k b s : ℕ)
    (hN : p ^ (s + 1) ∣ p ^ k) (hb : p ^ (s + 1) ∣ p * b) :
    ((p : ℤ) ^ (k + (s + 1))) ∣
      uprod p b (fun j => ((p ^ k : ℕ) : ℤ) - j) - uprod p b (fun j => (j : ℤ)) := by
  have hpi : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  set N : ℤ := ((p ^ k : ℕ) : ℤ) with hNdef
  set X := uprod p b (fun j => N - j) with hX
  set Y := uprod p b (fun j => (j : ℤ)) with hY
  -- reflected forms
  have hXr : X = uprod p b (fun j => N - ((p * b - j : ℕ) : ℤ)) := uprod_reflect p b _
  have hYr : Y = uprod p b (fun j => ((p * b - j : ℕ) : ℤ)) := uprod_reflect p b _
  have hdN : ((p : ℤ) ^ (s + 1)) ∣ N := by
    rw [hNdef]; exact_mod_cast hN
  have hdb : ((p : ℤ) ^ (s + 1)) ∣ ((p * b : ℕ) : ℤ) := by exact_mod_cast hb
  have hdiff : ((p : ℤ) ^ (s + 1)) ∣ N - ((p * b : ℕ) : ℤ) := dvd_sub hdN hdb
  -- X ≡ Y mod p^(s+1)
  have h1 : X ≡ Y [ZMOD (p : ℤ) ^ (s + 1)] := by
    rw [hXr]
    refine uprod_modEq p b _ _ _ fun i hi t ht => ?_
    have hle := unit_le hi ht
    show N - ((p * b - (p * i + t + 1) : ℕ) : ℤ) ≡ ((p * i + t + 1 : ℕ) : ℤ) [ZMOD (p : ℤ) ^ (s + 1)]
    rw [Nat.cast_sub hle, Int.modEq_iff_dvd]
    have : ((p * i + t + 1 : ℕ) : ℤ) - (N - (((p * b : ℕ) : ℤ) - ((p * i + t + 1 : ℕ) : ℤ)))
        = -(N - ((p * b : ℕ) : ℤ)) := by ring
    rw [this]
    exact (dvd_neg).mpr hdiff
  -- X * X ≡ Y * Y mod N * p^(s+1)
  have h2 : X * X ≡ Y * Y [ZMOD N * (p : ℤ) ^ (s + 1)] := by
    have e1 : X * X = uprod p b (fun j => (N - j) * (N - ((p * b - j : ℕ) : ℤ))) := by
      rw [← uprod_mul, ← hXr]
    have e2 : Y * Y = uprod p b (fun j => (j : ℤ) * ((p * b - j : ℕ) : ℤ)) := by
      rw [← uprod_mul, ← hYr]
    rw [e1, e2]
    refine uprod_modEq p b _ _ _ fun i hi t ht => ?_
    have hle := unit_le hi ht
    show (N - ((p * i + t + 1 : ℕ) : ℤ)) * (N - ((p * b - (p * i + t + 1) : ℕ) : ℤ))
      ≡ ((p * i + t + 1 : ℕ) : ℤ) * ((p * b - (p * i + t + 1) : ℕ) : ℤ) [ZMOD N * (p : ℤ) ^ (s + 1)]
    rw [Nat.cast_sub hle, Int.modEq_iff_dvd]
    have : ((p * i + t + 1 : ℕ) : ℤ) * (((p * b : ℕ) : ℤ) - ((p * i + t + 1 : ℕ) : ℤ))
        - (N - ((p * i + t + 1 : ℕ) : ℤ)) * (N - (((p * b : ℕ) : ℤ) - ((p * i + t + 1 : ℕ) : ℤ)))
        = -(N * (N - ((p * b : ℕ) : ℤ))) := by ring
    rw [this]
    exact (dvd_neg).mpr (mul_dvd_mul_left N hdiff)
  -- p does not divide X + Y
  have hYnd : ¬ (p : ℤ) ∣ Y := not_dvd_uprod_id hp b
  have hsum : ¬ (p : ℤ) ∣ X + Y := by
    intro hd
    have hXY : (p : ℤ) ∣ X - Y := by
      have := (Int.modEq_iff_dvd.mp h1.symm)
      exact dvd_trans (dvd_pow_self (p : ℤ) (Nat.succ_ne_zero s)) this
    have h2Y : (p : ℤ) ∣ 2 * Y := by
      have : 2 * Y = (X + Y) - (X - Y) := by ring
      rw [this]; exact dvd_sub hd hXY
    rcases hpi.dvd_or_dvd h2Y with h | h
    · have h' : p ∣ 2 := by exact_mod_cast h
      have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h'
      exact hp2 this
    · exact hYnd h
  -- conclude
  have hprod : ((p : ℤ) ^ (k + (s + 1))) ∣ (X - Y) * (X + Y) := by
    have h3 := Int.modEq_iff_dvd.mp h2.symm
    have h4 : (X - Y) * (X + Y) = X * X - Y * Y := by ring
    rw [h4]
    have h5 : (p : ℤ) ^ (k + (s + 1)) = N * (p : ℤ) ^ (s + 1) := by
      rw [hNdef, pow_add]; push_cast; ring
    rw [h5]; exact h3
  exact hpi.pow_dvd_of_dvd_mul_right _ hsum hprod

/-- `p ^ (m - s)` divides `C(p ^ m, p ^ s * b')` when `p` does not divide `b'`. -/
private lemma pow_dvd_choose_pow {p : ℕ} (hp : p.Prime) (m s b' : ℕ) (hs : s ≤ m) (hb' : ¬ p ∣ b') :
    p ^ (m - s) ∣ (p ^ m).choose (p ^ s * b') := by
  have hb0 : b' ≠ 0 := fun h => hb' (h ▸ dvd_zero p)
  have hbpos : 0 < p ^ s * b' := Nat.mul_pos (pow_pos hp.pos s) (Nat.pos_of_ne_zero hb0)
  have hQpos : 0 < p ^ m := pow_pos hp.pos m
  have h := Nat.add_one_mul_choose_eq (p ^ m - 1) (p ^ s * b' - 1)
  rw [Nat.sub_add_cancel hQpos, Nat.sub_add_cancel hbpos] at h
  -- h : p^m * C(p^m - 1, b - 1) = C(p^m, b) * b
  have h1 : p ^ s * p ^ (m - s) ∣ p ^ s * ((p ^ m).choose (p ^ s * b') * b') := by
    rw [← pow_add, Nat.add_sub_cancel' hs]
    refine ⟨(p ^ m - 1).choose (p ^ s * b' - 1), ?_⟩
    rw [h]; ring
  have h2 : p ^ (m - s) ∣ (p ^ m).choose (p ^ s * b') * b' :=
    Nat.dvd_of_mul_dvd_mul_left (pow_pos hp.pos s) h1
  have hcop : Nat.Coprime (p ^ (m - s)) b' :=
    Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hp).mpr hb')
  exact hcop.dvd_of_dvd_mul_right h2

/-- Key binomial congruence: `C(p^(m+1), p b) ≡ C(p^m, b)` modulo `p^(2(m+1))` for odd `p`. -/
private lemma choose_pow_congr {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (m b : ℕ) :
    (((p ^ (m + 1) : ℕ) : ℤ) ^ 2) ∣
      (((p ^ (m + 1)).choose (p * b) : ℕ) : ℤ) - (((p ^ m).choose b : ℕ) : ℤ) := by
  have hpi : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  rcases Nat.eq_zero_or_pos b with rfl | hbpos
  · simp
  rcases lt_or_ge (p ^ m) b with hbig | hble
  · have h1 : p ^ (m + 1) < p * b := by
      rw [pow_succ, mul_comm]; exact Nat.mul_lt_mul_of_pos_left hbig hp.pos
    rw [Nat.choose_eq_zero_of_lt h1, Nat.choose_eq_zero_of_lt hbig]
    simp
  obtain ⟨s, b', hb', rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd (Nat.pos_iff_ne_zero.mp hbpos) p hp.ne_one
  have hb0 : b' ≠ 0 := fun h => hb' (h ▸ dvd_zero p)
  have hs : s ≤ m := by
    have h1 : p ^ s ≤ p ^ s * b' := Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hb0)
    exact (Nat.pow_le_pow_iff_right hp.one_lt).mp (le_trans h1 hble)
  have hpa : p * p ^ m = p ^ (m + 1) := by rw [pow_succ, mul_comm]
  have hform := choose_mul_uprod p (p ^ m) (p ^ s * b') hp.pos
  rw [hpa] at hform
  have hsub := uprod_sub_dvd hp hp2 (m + 1) (p ^ s * b') s
    (pow_dvd_pow p (by omega)) ⟨b', by rw [pow_succ]; ring⟩
  have hch : ((p : ℤ) ^ (m - s)) ∣ (((p ^ m).choose (p ^ s * b') : ℕ) : ℤ) := by
    exact_mod_cast pow_dvd_choose_pow hp m s b' hs hb'
  set X := uprod p (p ^ s * b') (fun j => ((p ^ (m + 1) : ℕ) : ℤ) - j) with hX
  set Y := uprod p (p ^ s * b') (fun j => (j : ℤ)) with hY
  have hYnd : ¬ (p : ℤ) ∣ Y := not_dvd_uprod_id hp _
  have hkey : Y * ((((p ^ (m + 1)).choose (p * (p ^ s * b')) : ℕ) : ℤ) - (((p ^ m).choose (p ^ s * b') : ℕ) : ℤ))
      = (((p ^ m).choose (p ^ s * b') : ℕ) : ℤ) * (X - Y) := by
    linear_combination hform
  have hdvd : ((p : ℤ) ^ (2 * (m + 1))) ∣
      Y * ((((p ^ (m + 1)).choose (p * (p ^ s * b')) : ℕ) : ℤ) - (((p ^ m).choose (p ^ s * b') : ℕ) : ℤ)) := by
    rw [hkey]
    have : (p : ℤ) ^ (2 * (m + 1)) = (p : ℤ) ^ (m - s) * (p : ℤ) ^ (m + 1 + (s + 1)) := by
      rw [← pow_add]; congr 1; omega
    rw [this]
    exact mul_dvd_mul hch hsub
  have hfin := hpi.pow_dvd_of_dvd_mul_left _ hYnd hdvd
  have hsq : (((p ^ (m + 1) : ℕ) : ℤ) ^ 2) = (p : ℤ) ^ (2 * (m + 1)) := by
    push_cast; rw [← pow_mul]; congr 1; ring
  rw [hsq]; exact hfin

/-- `p ^ k` divides `C(p ^ k, i)` when `p` does not divide `i`. -/
private lemma pow_dvd_choose_of_not_dvd {p : ℕ} (hp : p.Prime) (k i : ℕ) (hi : ¬ p ∣ i) :
    p ^ k ∣ (p ^ k).choose i := by
  have h := pow_dvd_choose_pow hp k 0 i (Nat.zero_le k) hi
  simpa using h

/-! Power series part. -/

/-- `D` is in the set `N * (series supported off the multiples of p) + N ^ 2 * (any series)`. -/
private def InI (p N : ℕ) (D : PowerSeries ℤ) : Prop :=
  ∀ j, ((N : ℤ) ∣ PowerSeries.coeff j D) ∧ (p ∣ j → ((N : ℤ) ^ 2) ∣ PowerSeries.coeff j D)

/-- `G` is supported on the multiples of `p`. -/
private def PS (p : ℕ) (G : PowerSeries ℤ) : Prop :=
  ∀ j, ¬ p ∣ j → PowerSeries.coeff j G = 0

private lemma InI_add {p N : ℕ} {A B : PowerSeries ℤ} (hA : InI p N A) (hB : InI p N B) :
    InI p N (A + B) := by
  intro j
  rw [map_add]
  exact ⟨dvd_add (hA j).1 (hB j).1, fun h => dvd_add ((hA j).2 h) ((hB j).2 h)⟩

private lemma InI_sub {p N : ℕ} {A B : PowerSeries ℤ} (hA : InI p N A) (hB : InI p N B) :
    InI p N (A - B) := by
  intro j
  rw [map_sub]
  exact ⟨dvd_sub (hA j).1 (hB j).1, fun h => dvd_sub ((hA j).2 h) ((hB j).2 h)⟩

private lemma InI_mul {p N : ℕ} {A B : PowerSeries ℤ} (hA : InI p N A) (hB : InI p N B) :
    InI p N (A * B) := by
  have key : ∀ j, ((N : ℤ) ^ 2) ∣ PowerSeries.coeff j (A * B) := by
    intro j
    rw [PowerSeries.coeff_mul]
    refine Finset.dvd_sum fun x _ => ?_
    rw [sq]
    exact mul_dvd_mul (hA x.1).1 (hB x.2).1
  intro j
  exact ⟨dvd_trans (dvd_pow_self _ two_ne_zero) (key j), fun _ => key j⟩

private lemma InI_mul_PS {p N : ℕ} {A G : PowerSeries ℤ} (hA : InI p N A) (hG : PS p G) :
    InI p N (A * G) := by
  intro j
  rw [PowerSeries.coeff_mul]
  constructor
  · refine Finset.dvd_sum fun x _ => ?_
    exact Dvd.dvd.mul_right (hA x.1).1 _
  · intro hj
    refine Finset.dvd_sum fun x hx => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
    by_cases h2 : p ∣ x.2
    · have h1 : p ∣ x.1 := by
        have h3 : p ∣ x.2 + x.1 := by rw [add_comm, hx]; exact hj
        exact (Nat.dvd_add_right h2).mp h3
      exact Dvd.dvd.mul_right ((hA x.1).2 h1) _
    · rw [hG x.2 h2, mul_zero]; exact dvd_zero _

private lemma PS_mul {p : ℕ} {A B : PowerSeries ℤ} (hA : PS p A) (hB : PS p B) : PS p (A * B) := by
  intro j hj
  rw [PowerSeries.coeff_mul]
  refine Finset.sum_eq_zero fun x hx => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
  by_cases h1 : p ∣ x.1
  · have h2 : ¬ p ∣ x.2 := fun h2 => hj (hx ▸ dvd_add h1 h2)
    rw [hB x.2 h2, mul_zero]
  · rw [hA x.1 h1, zero_mul]

private lemma InI_mul_sub {p N : ℕ} {A A' B B' : PowerSeries ℤ} (hA : InI p N (A - A'))
    (hB : InI p N (B - B')) (hA' : PS p A') (hB' : PS p B') : InI p N (A * B - A' * B') := by
  have h : A * B - A' * B' = (A - A') * (B - B') + (A - A') * B' + (B - B') * A' := by ring
  rw [h]
  exact InI_add (InI_add (InI_mul hA hB) (InI_mul_PS hA hB')) (InI_mul_PS hB hA')

/-- Division by a series `U` with constant coefficient `1` whose coefficients off the multiples of
`p` are divisible by `N`. -/
private lemma InI_of_mul {p N : ℕ} {D U : PowerSeries ℤ} (hU0 : PowerSeries.coeff 0 U = 1)
    (hU : ∀ j, ¬ p ∣ j → (N : ℤ) ∣ PowerSeries.coeff j U) (h : InI p N (D * U)) : InI p N D := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    have hj := h j
    rw [PowerSeries.coeff_mul] at hj
    have hmem : (j, 0) ∈ Finset.HasAntidiagonal.antidiagonal j := Finset.HasAntidiagonal.mem_antidiagonal.mpr (add_zero j)
    rw [← Finset.add_sum_erase _ _ hmem] at hj
    simp only [hU0, mul_one] at hj
    have hlt : ∀ x ∈ (Finset.HasAntidiagonal.antidiagonal j).erase (j, 0), x.1 < j := by
      intro x hx
      rw [Finset.mem_erase, Finset.HasAntidiagonal.mem_antidiagonal] at hx
      by_contra hge
      have hx1 : x.1 = j := by omega
      have hx2 : x.2 = 0 := by omega
      exact hx.1 (Prod.ext hx1 hx2)
    have hrest1 : (N : ℤ) ∣ ∑ x ∈ (Finset.HasAntidiagonal.antidiagonal j).erase (j, 0),
        PowerSeries.coeff x.1 D * PowerSeries.coeff x.2 U := by
      refine Finset.dvd_sum fun x hx => ?_
      exact Dvd.dvd.mul_right (ih x.1 (hlt x hx)).1 _
    have hrest2 : p ∣ j → ((N : ℤ) ^ 2) ∣ ∑ x ∈ (Finset.HasAntidiagonal.antidiagonal j).erase (j, 0),
        PowerSeries.coeff x.1 D * PowerSeries.coeff x.2 U := by
      intro hpj
      refine Finset.dvd_sum fun x hx => ?_
      have hl := hlt x hx
      rw [Finset.mem_erase, Finset.HasAntidiagonal.mem_antidiagonal] at hx
      by_cases h1 : p ∣ x.1
      · exact Dvd.dvd.mul_right ((ih x.1 hl).2 h1) _
      · have h2 : ¬ p ∣ x.2 := by
          intro h2
          have h3 : p ∣ x.2 + x.1 := by rw [add_comm, hx.2]; exact hpj
          exact h1 ((Nat.dvd_add_right h2).mp h3)
        rw [sq]
        exact mul_dvd_mul (ih x.1 hl).1 (hU x.2 h2)
    exact ⟨(dvd_add_left hrest1).mp hj.1, fun hpj => (dvd_add_left (hrest2 hpj)).mp (hj.2 hpj)⟩

/-- The binomial `1 + c * x ^ e`. -/
private noncomputable def B (c : ℤ) (e : ℕ) : PowerSeries ℤ :=
  1 + PowerSeries.C c * PowerSeries.X ^ e

private lemma coeff_B_pow (c : ℤ) (e n j : ℕ) (he : 0 < e) :
    PowerSeries.coeff j (B c e ^ n) =
      if e ∣ j then c ^ (j / e) * ((n.choose (j / e) : ℕ) : ℤ) else 0 := by
  unfold B
  rw [add_comm, add_pow]
  simp only [one_pow, mul_one, map_sum]
  have hterm : ∀ i ∈ Finset.range (n + 1),
      PowerSeries.coeff j ((PowerSeries.C c * PowerSeries.X ^ e : PowerSeries ℤ) ^ i *
          ((n.choose i : ℕ) : PowerSeries ℤ)) =
        if j = e * i then c ^ i * ((n.choose i : ℕ) : ℤ) else 0 := by
    intro i _
    rw [mul_pow, ← pow_mul, ← map_pow, ← map_natCast (PowerSeries.C : ℤ →+* PowerSeries ℤ) (n.choose i),
      mul_right_comm, ← map_mul, PowerSeries.coeff_C_mul_X_pow]
  rw [Finset.sum_congr rfl hterm]
  split_ifs with h
  · obtain ⟨i, rfl⟩ := h
    rw [Nat.mul_div_cancel_left _ he, Finset.sum_eq_single i]
    · simp
    · intro i' _ hne
      rw [if_neg]
      intro h
      exact hne (Nat.eq_of_mul_eq_mul_left he h).symm
    · intro hi
      rw [Finset.mem_range, not_lt] at hi
      rw [Nat.choose_eq_zero_of_lt (by omega)]
      simp
  · refine Finset.sum_eq_zero fun i _ => ?_
    rw [if_neg]
    intro hj
    exact h ⟨i, hj⟩

private lemma B_pow_PS (p : ℕ) (hp : 0 < p) (c : ℤ) (e n : ℕ) (he : 0 < e) :
    PS p (B c (e * p) ^ n) := by
  intro j hj
  rw [coeff_B_pow c (e * p) n j (Nat.mul_pos he hp), if_neg]
  intro h
  exact hj (dvd_trans (dvd_mul_left p e) h)

private lemma B_pow_InI {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (m : ℕ) (c : ℤ)
    (hc : c = 1 ∨ c = -1) (e : ℕ) (he : 0 < e) (hep : Nat.Coprime p e) :
    InI p (p ^ (m + 1)) (B c e ^ (p ^ (m + 1)) - B c (e * p) ^ (p ^ m)) := by
  intro j
  rw [map_sub, coeff_B_pow c e _ j he, coeff_B_pow c (e * p) _ j (Nat.mul_pos he hp.pos)]
  have hcp : c ^ p = c := by
    rcases hc with rfl | rfl
    · simp
    · exact Odd.neg_one_pow (hp.odd_of_ne_two hp2)
  by_cases hej : e ∣ j
  · obtain ⟨i, rfl⟩ := hej
    rw [if_pos (dvd_mul_right e i), Nat.mul_div_cancel_left _ he]
    by_cases hpi : p ∣ i
    · obtain ⟨i', rfl⟩ := hpi
      have h1 : e * p ∣ e * (p * i') := ⟨i', by ring⟩
      have h2 : e * (p * i') / (e * p) = i' := by
        rw [← mul_assoc]
        exact Nat.mul_div_cancel_left _ (Nat.mul_pos he hp.pos)
      rw [if_pos h1, h2, pow_mul, hcp, ← mul_sub]
      have key := choose_pow_congr hp hp2 m i'
      have key' : ((p ^ (m + 1) : ℕ) : ℤ) ^ 2 ∣
          c ^ i' * ((((p ^ (m + 1)).choose (p * i') : ℕ) : ℤ) - (((p ^ m).choose i' : ℕ) : ℤ)) :=
        Dvd.dvd.mul_left key _
      exact ⟨dvd_trans (dvd_pow_self _ two_ne_zero) key', fun _ => key'⟩
    · have h1 : ¬ e * p ∣ e * i := fun h => hpi (Nat.dvd_of_mul_dvd_mul_left he h)
      rw [if_neg h1, sub_zero]
      constructor
      · have h3 : ((p ^ (m + 1) : ℕ) : ℤ) ∣ (((p ^ (m + 1)).choose i : ℕ) : ℤ) := by
          exact_mod_cast pow_dvd_choose_of_not_dvd hp (m + 1) i hpi
        exact Dvd.dvd.mul_left h3 _
      · intro hpj
        exact absurd (hep.dvd_of_dvd_mul_left hpj) hpi
  · have h1 : ¬ e * p ∣ j := fun h => hej (dvd_trans (dvd_mul_right e p) h)
    rw [if_neg hej, if_neg h1, sub_zero]
    exact ⟨dvd_zero _, fun _ => dvd_zero _⟩

private lemma expand_B (p : ℕ) (hp : p ≠ 0) (c : ℤ) (e : ℕ) :
    PowerSeries.expand p hp (B c e) = B c (e * p) := by
  unfold B
  rw [map_add, map_one, map_mul, map_pow, PowerSeries.expand_C, PowerSeries.expand_X, ← pow_mul,
    mul_comm p e]

private lemma isUnit_denom :
    IsUnit (1 - PowerSeries.X + PowerSeries.X ^ 2 : PowerSeries ℤ) := by
  rw [PowerSeries.isUnit_iff_constantCoeff]
  simp

private lemma f_rel :
    B (-1) 1 * B 1 3 * OMA.S_oeis_a333579.f = B 1 1 * B (-1) 3 := by
  unfold OMA.S_oeis_a333579.f B
  have hinv : (1 - PowerSeries.X + PowerSeries.X ^ 2 : PowerSeries ℤ) *
      Ring.inverse (1 - PowerSeries.X + PowerSeries.X ^ 2 : PowerSeries ℤ) = 1 :=
    Ring.mul_inverse_cancel _ isUnit_denom
  simp only [map_neg, map_one, pow_one]
  linear_combination (1 - PowerSeries.X ^ 2) * (1 + PowerSeries.X + PowerSeries.X ^ 2) * hinv

private theorem main_congr {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (m : ℕ) :
    ((p : ℤ) ^ (2 * (m + 1))) ∣
      OMA.S_oeis_a333579.a (p ^ (m + 1)) - OMA.S_oeis_a333579.a (p ^ m) := by
  have hp2 : p ≠ 2 := by omega
  have hp0 : p ≠ 0 := hp.ne_zero
  have hcop1 : Nat.Coprime p 1 := Nat.coprime_one_right p
  have hcop3 : Nat.Coprime p 3 := by
    refine (Nat.Prime.coprime_iff_not_dvd hp).mpr fun h => ?_
    have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h
    omega
  -- the relation at level `N = p ^ (m + 1)`
  have hrelN : B (-1) 1 ^ (p ^ (m + 1)) * B 1 3 ^ (p ^ (m + 1)) *
      OMA.S_oeis_a333579.f ^ (p ^ (m + 1)) = B 1 1 ^ (p ^ (m + 1)) * B (-1) 3 ^ (p ^ (m + 1)) := by
    rw [← mul_pow, ← mul_pow, ← mul_pow, f_rel]
  -- the relation at level `Q = p ^ m`, expanded by `x ↦ x ^ p`
  have hrelQ : B (-1) (1 * p) ^ (p ^ m) * B 1 (3 * p) ^ (p ^ m) *
      PowerSeries.expand p hp0 (OMA.S_oeis_a333579.f ^ (p ^ m)) =
      B 1 (1 * p) ^ (p ^ m) * B (-1) (3 * p) ^ (p ^ m) := by
    have h0 : B (-1) 1 ^ (p ^ m) * B 1 3 ^ (p ^ m) * OMA.S_oeis_a333579.f ^ (p ^ m) =
        B 1 1 ^ (p ^ m) * B (-1) 3 ^ (p ^ m) := by
      rw [← mul_pow, ← mul_pow, ← mul_pow, f_rel]
    have h1 := congrArg (PowerSeries.expand p hp0) h0
    simp only [map_mul, map_pow, expand_B] at h1 ⊢
    exact h1
  -- memberships
  have iA1 := B_pow_InI hp hp2 m (-1) (Or.inr rfl) 1 one_pos hcop1
  have iA3 := B_pow_InI hp hp2 m 1 (Or.inl rfl) 3 (by norm_num) hcop3
  have iB1 := B_pow_InI hp hp2 m 1 (Or.inl rfl) 1 one_pos hcop1
  have iB3 := B_pow_InI hp hp2 m (-1) (Or.inr rfl) 3 (by norm_num) hcop3
  have sA1 := B_pow_PS p hp.pos (-1) 1 (p ^ m) one_pos
  have sA3 := B_pow_PS p hp.pos 1 3 (p ^ m) (by norm_num)
  have sB1 := B_pow_PS p hp.pos 1 1 (p ^ m) one_pos
  have sB3 := B_pow_PS p hp.pos (-1) 3 (p ^ m) (by norm_num)
  have sPhi : PS p (PowerSeries.expand p hp0 (OMA.S_oeis_a333579.f ^ (p ^ m))) :=
    fun j hj => PowerSeries.coeff_expand_of_not_dvd p hp0 _ hj
  have iV := InI_mul_sub iA1 iA3 sA1 sA3
  have iW := InI_mul_sub iB1 iB3 sB1 sB3
  -- the difference times `V ^ N`
  have hprod : InI p (p ^ (m + 1))
      ((OMA.S_oeis_a333579.f ^ (p ^ (m + 1)) -
          PowerSeries.expand p hp0 (OMA.S_oeis_a333579.f ^ (p ^ m))) *
        (B (-1) 1 ^ (p ^ (m + 1)) * B 1 3 ^ (p ^ (m + 1)))) := by
    have h : (OMA.S_oeis_a333579.f ^ (p ^ (m + 1)) -
          PowerSeries.expand p hp0 (OMA.S_oeis_a333579.f ^ (p ^ m))) *
        (B (-1) 1 ^ (p ^ (m + 1)) * B 1 3 ^ (p ^ (m + 1))) =
        (B 1 1 ^ (p ^ (m + 1)) * B (-1) 3 ^ (p ^ (m + 1)) -
            B 1 (1 * p) ^ (p ^ m) * B (-1) (3 * p) ^ (p ^ m)) -
          (B (-1) 1 ^ (p ^ (m + 1)) * B 1 3 ^ (p ^ (m + 1)) -
            B (-1) (1 * p) ^ (p ^ m) * B 1 (3 * p) ^ (p ^ m)) *
          PowerSeries.expand p hp0 (OMA.S_oeis_a333579.f ^ (p ^ m)) := by
      linear_combination hrelN - hrelQ
    rw [h]
    exact InI_sub iW (InI_mul_PS iV sPhi)
  -- divide by `V ^ N`
  have hU0 : PowerSeries.coeff 0 (B (-1) 1 ^ (p ^ (m + 1)) * B 1 3 ^ (p ^ (m + 1))) = 1 := by
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply]
    simp [B]
  have hU : ∀ j, ¬ p ∣ j →
      ((p ^ (m + 1) : ℕ) : ℤ) ∣
        PowerSeries.coeff j (B (-1) 1 ^ (p ^ (m + 1)) * B 1 3 ^ (p ^ (m + 1))) := by
    intro j hj
    have h1 := (iV j).1
    rw [map_sub, PS_mul sA1 sA3 j hj, sub_zero] at h1
    exact h1
  have hD := InI_of_mul hU0 hU hprod
  -- read off the coefficient of `x ^ N`
  have hfin := (hD (p ^ (m + 1))).2 (dvd_pow_self p (Nat.succ_ne_zero m))
  rw [map_sub] at hfin
  have hco : PowerSeries.coeff (p ^ (m + 1))
      (PowerSeries.expand p hp0 (OMA.S_oeis_a333579.f ^ (p ^ m))) =
      PowerSeries.coeff (p ^ m) (OMA.S_oeis_a333579.f ^ (p ^ m)) := by
    rw [pow_succ, mul_comm (p ^ m) p]
    exact PowerSeries.coeff_expand_mul p hp0 _ _
  rw [hco] at hfin
  have hsq : (((p ^ (m + 1) : ℕ) : ℤ) ^ 2) = (p : ℤ) ^ (2 * (m + 1)) := by
    push_cast
    rw [← pow_mul]
    congr 1
    ring
  rw [hsq] at hfin
  exact hfin

end A333579H2

theorem OMA.solution : type_of% @OMA.S_oeis_a333579.main := by
  refine ⟨?_, ?_⟩
  · intro p hp hp5
    exact SolvedConjecture06.conjecture_1 p hp hp5
  · intro p k hp hp5 hk
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    rw [Nat.add_sub_cancel]
    exact A333579H2.main_congr hp hp5 m
