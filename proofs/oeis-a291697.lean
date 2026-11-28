import OMAStatements.S_oeis_a291697
import Mathlib

/-!
# Proof of OEIS A291697, Supercongruence Conjecture (Peter Bala, Apr 18 2023)

Official OEIS entry [A291697](https://oeis.org/A291697):
$$a(n) = [x^n] \prod_{k \ge 0} \left(\frac{1 + x^{2k+1}}{1 - x^{2k+1}}\right)^n
       = [x^n] \prod_{k=0}^{\lfloor (n-1)/2 \rfloor} \left(\frac{1 + x^{2k+1}}{1 - x^{2k+1}}\right)^n.$$
Conjecture (Peter Bala, Apr 18 2023): For all primes $p \ge 5$,
$$a(p) \equiv 2p + 2 \pmod{p^3}.$$

## Proof Overview (100% elementary, zero `sorry`, zero custom axioms)
Work in $(\mathbb{Z}/p^3\mathbb{Z})[[x]]$. Call a power series $F$ **good** for $c \in \mathbb{Z}/p^3\mathbb{Z}$
(`Good3 p F c`) if there exist $Q, R \in (\mathbb{Z}/p^3\mathbb{Z})[[x]]$ such that:
- $Q(0) = 0$, $[x^p] Q = 0$, and $Q$ is an **odd** series ($\forall d,\; \text{Even } d \to [x^d] Q = 0$);
- $R(0) = 0$ and $p^2 \cdot [x^p] R = 0$ in $\mathbb{Z}/p^3\mathbb{Z}$;
- $F$ agrees with $1 + c x^p + p Q + p^2 R$ in all degrees $d \le p$.

1. `Good3` is multiplicative (`Good3 p F c₁ → Good3 p G c₂ → Good3 p (F * G) (c₁ + c₂)`):
   since $p^3 = 0$, $x^{2p} \equiv 0$, $x^p Q_i \equiv 0$, $x^p R_i \equiv 0 \pmod{x^{p+1}}$, and
   $Q_1 Q_2$ is the product of two odd series, hence **even**, so $[x^p](Q_1 Q_2) = 0$ (as $p$ is odd).
2. For $m = 1$: $((1+x)/(1-x))^p \equiv (1 + 2 x^p) + p(P(x) - P(-x)) + p^2(P(-x)^2 - P(x)P(-x)) \pmod{x^{p+1}}$,
   which is `Good3` for $2$ (using $[x^p] P(-x)^2 \equiv -\sum_{k=1}^{p-1} k^{-2} \equiv 0 \pmod p$ for $p \ge 5$,
   and $P(x) P(-x)$ even).
3. For $m = p$: $((1+x^p)/(1-x^p))^p \equiv 1 + 2 p x^p \pmod{x^{p+1}}$, which is `Good3` for $2p$.
4. For every odd $m$ with $3 \le m \le p - 2$: $((1+x^m)/(1-x^m))^p \equiv 1 + p(P(x^m) - P(-x^m)) +
   p^2(P(-x^m)^2 - P(x^m)P(-x^m)) \pmod{x^{p+1}}$, which is `Good3` for $0$ (every term is supported
   on multiples of $m$, and $m \nmid p$, while $P(x^m) - P(-x^m)$ is odd since $m$ is odd).
5. Multiplying all factors $k = 0, \dots, (p-1)/2$ yields `Good3` for $2 + 2p + 0 = 2p + 2$.
   Extracting $[x^p]$ gives $a(p) \equiv 2p + 2 \pmod{p^3}$.
-/

namespace SolvedConjecture09

open Finset BigOperators PowerSeries

/-- The formal power series factor $(1 + x^m)(1 - x^m)^{-1}$ in $\mathbb{Z}[[x]]$. -/
noncomputable def factor (m : ℕ) : PowerSeries ℤ :=
  (1 + PowerSeries.X ^ m) * Ring.inverse (1 - PowerSeries.X ^ m)

/-- OEIS A291697: $a(n) = [x^n] \prod_{k=0}^{\lfloor (n-1)/2 \rfloor} \left(\frac{1 + x^{2k+1}}{1 - x^{2k+1}}\right)^n$. -/
noncomputable def a (n : ℕ) : ℤ :=
  PowerSeries.coeff n (∏ k ∈ Finset.range ((n + 1) / 2), (factor (2 * k + 1)) ^ n)

private lemma isUnit_one_sub_X_pow {m : ℕ} (hm : 1 ≤ m) :
    IsUnit (1 - PowerSeries.X ^ m : PowerSeries ℤ) := by
  rw [PowerSeries.isUnit_iff_constantCoeff]
  simp [show m ≠ 0 by omega]

private lemma one_sub_X_pow_mul_factor {m : ℕ} (hm : 1 ≤ m) :
    (1 - PowerSeries.X ^ m : PowerSeries ℤ) * factor m = 1 + PowerSeries.X ^ m := by
  unfold factor
  have hinv : (1 - PowerSeries.X ^ m : PowerSeries ℤ) *
      Ring.inverse (1 - PowerSeries.X ^ m : PowerSeries ℤ) = 1 :=
    Ring.mul_inverse_cancel _ (isUnit_one_sub_X_pow hm)
  calc (1 - PowerSeries.X ^ m : PowerSeries ℤ) *
          ((1 + PowerSeries.X ^ m) * Ring.inverse (1 - PowerSeries.X ^ m))
      = (1 + PowerSeries.X ^ m : PowerSeries ℤ) *
          ((1 - PowerSeries.X ^ m) * Ring.inverse (1 - PowerSeries.X ^ m)) := by ring
    _ = 1 + PowerSeries.X ^ m := by rw [hinv, mul_one]

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
  unfold Pseries; rw [map_sum]
  simp only [PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq]; simp only [Finset.mem_Icc]

private lemma coeff_Pseries_neg_X {R : Type*} [CommRing R] (p d : ℕ) :
    PowerSeries.coeff d (Pseries (R := R) p (-PowerSeries.X)) =
      if 1 ≤ d ∧ d ≤ p - 1 then (-1 : R) ^ d * ((p.choose d / p : ℕ) : R) else 0 := by
  unfold Pseries; rw [map_sum]
  have hterm : ∀ k ∈ Finset.Icc 1 (p - 1),
      PowerSeries.coeff d (PowerSeries.C (((p.choose k / p : ℕ) : R)) * (-PowerSeries.X) ^ k) =
        if d = k then (-1 : R) ^ k * ((p.choose k / p : ℕ) : R) else 0 := by
    intro k _
    rw [neg_eq_neg_one_mul, mul_pow, show (-1 : PowerSeries R) ^ k = PowerSeries.C ((-1 : R) ^ k) by
      simp [map_pow], ← mul_assoc, ← map_mul, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow]
    split_ifs <;> ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq]; simp only [Finset.mem_Icc]

private lemma coeff_Pseries_Xm_eq_zero {R : Type*} [CommRing R] {p m d : ℕ} (hd : ¬ m ∣ d) (c : R) :
    PowerSeries.coeff d (Pseries (R := R) p (PowerSeries.C c * PowerSeries.X ^ m)) = 0 := by
  unfold Pseries; rw [map_sum]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [mul_pow, ← pow_mul, ← map_pow, ← mul_assoc, ← map_mul, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_X_pow]
  have hne : d ≠ m * k := fun h => hd ⟨k, h⟩
  simp [hne]

private lemma coeff_mul_eq_zero_of_dvdm {R : Type*} [CommRing R] {m : ℕ} (A B : PowerSeries R)
    (hA : ∀ k, ¬ m ∣ k → PowerSeries.coeff k A = 0)
    (hB : ∀ k, ¬ m ∣ k → PowerSeries.coeff k B = 0)
    {d : ℕ} (hd : ¬ m ∣ d) :
    PowerSeries.coeff d (A * B) = 0 := by
  rw [PowerSeries.coeff_mul]
  refine Finset.sum_eq_zero fun x hx => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
  by_cases h1 : m ∣ x.1
  · have h2 : ¬ m ∣ x.2 := fun h2 => hd (hx ▸ dvd_add h1 h2)
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

private lemma coeff_eq_of_eq_le {R : Type*} [CommRing R] {p : ℕ} (A B C D : PowerSeries R)
    (hAB : ∀ d ≤ p, PowerSeries.coeff d A = PowerSeries.coeff d B)
    (hCD : ∀ d ≤ p, PowerSeries.coeff d C = PowerSeries.coeff d D) :
    ∀ d ≤ p, PowerSeries.coeff d (A * C) = PowerSeries.coeff d (B * D) := by
  intro d hd
  rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
  rw [hAB x.1 (by omega), hCD x.2 (by omega)]

private lemma coeff_X_pow_mul_eq_zero {R : Type*} [CommRing R] {p d : ℕ} (hd : d ≤ p)
    (Q : PowerSeries R) (hQ0 : PowerSeries.constantCoeff Q = 0) :
    PowerSeries.coeff d (PowerSeries.X ^ p * Q) = 0 := by
  rw [PowerSeries.coeff_mul]
  refine Finset.sum_eq_zero fun x hx => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
  by_cases h1 : x.1 = p
  · have h2 : x.2 = 0 := by omega
    rw [h2, PowerSeries.coeff_zero_eq_constantCoeff, hQ0, mul_zero]
  · rw [PowerSeries.coeff_X_pow, if_neg h1, zero_mul]

private lemma coeff_X_pow_2p_eq_zero {R : Type*} [CommRing R] {p d : ℕ} (hp : 0 < p) (hd : d ≤ p) :
    PowerSeries.coeff d ((PowerSeries.X : PowerSeries R) ^ p * PowerSeries.X ^ p) = 0 := by
  rw [← pow_add, PowerSeries.coeff_X_pow, if_neg (by omega)]

/-- `Good3 p F c` means $F \equiv 1 + c x^p + p Q + p^2 R \pmod{x^{p+1}}$ in $(\mathbb{Z}/p^3\mathbb{Z})[[x]]$
with $Q$ odd ($[x^0] Q = [x^p] Q = 0$) and $R(0) = 0$, $p^2 [x^p] R = 0$. -/
private def Good3 (p : ℕ) (F : PowerSeries (ZMod (p ^ 3))) (c : ZMod (p ^ 3)) : Prop :=
  ∃ Q R : PowerSeries (ZMod (p ^ 3)),
    PowerSeries.constantCoeff Q = 0 ∧
    PowerSeries.coeff p Q = 0 ∧
    (∀ k, Even k → PowerSeries.coeff k Q = 0) ∧
    PowerSeries.constantCoeff R = 0 ∧
    (p : ZMod (p ^ 3)) ^ 2 * PowerSeries.coeff p R = 0 ∧
    ∀ d ≤ p, PowerSeries.coeff d F =
      PowerSeries.coeff d (1 + PowerSeries.C c * PowerSeries.X ^ p +
        (p : PowerSeries (ZMod (p ^ 3))) * Q + (p : PowerSeries (ZMod (p ^ 3))) ^ 2 * R)

private lemma Good3.one {p : ℕ} : Good3 p 1 0 :=
  ⟨0, 0, by simp, by simp, fun _ _ => by simp, by simp, by simp, fun _ _ => by simp⟩

private lemma Good3.mul {p : ℕ} (hp : 0 < p) (hp_odd : Odd p)
    {F G : PowerSeries (ZMod (p ^ 3))} {c1 c2 : ZMod (p ^ 3)}
    (hF : Good3 p F c1) (hG : Good3 p G c2) :
    Good3 p (F * G) (c1 + c2) := by
  rcases hF with ⟨Q1, R1, hQ10, hQ1p, hQ1odd, hR10, hR1p, hFeq⟩
  rcases hG with ⟨Q2, R2, hQ20, hQ2p, hQ2odd, hR20, hR2p, hGeq⟩
  refine ⟨Q1 + Q2, R1 + R2 + Q1 * Q2, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [hQ10, hQ20]
  · simp [hQ1p, hQ2p]
  · intro k hk; rw [map_add, hQ1odd k hk, hQ2odd k hk, add_zero]
  · simp [hR10, hR20, hQ10]
  · rw [map_add, map_add, coeff_odd_of_even_prod Q1 Q2 hQ1odd hQ2odd hp_odd, add_zero, mul_add,
      hR1p, hR2p, add_zero]
  · intro d hd
    rw [coeff_eq_of_eq_le F _ G _ hFeq hGeq d hd]
    have hp3 : (p : PowerSeries (ZMod (p ^ 3))) ^ 3 = 0 := by
      rw [← Nat.cast_pow, ← map_natCast PowerSeries.C (p ^ 3), ZMod.natCast_self, map_zero]
    have hexp :
        (1 + PowerSeries.C c1 * PowerSeries.X ^ p + (p : PowerSeries (ZMod (p ^ 3))) * Q1 +
          (p : PowerSeries (ZMod (p ^ 3))) ^ 2 * R1) *
        (1 + PowerSeries.C c2 * PowerSeries.X ^ p + (p : PowerSeries (ZMod (p ^ 3))) * Q2 +
          (p : PowerSeries (ZMod (p ^ 3))) ^ 2 * R2) =
        (1 + PowerSeries.C (c1 + c2) * PowerSeries.X ^ p +
          (p : PowerSeries (ZMod (p ^ 3))) * (Q1 + Q2) +
          (p : PowerSeries (ZMod (p ^ 3))) ^ 2 * (R1 + R2 + Q1 * Q2)) +
        PowerSeries.C (c1 * c2) * (PowerSeries.X ^ p * PowerSeries.X ^ p) +
        (PowerSeries.C (c1 * (p : ZMod (p ^ 3))) * (PowerSeries.X ^ p * Q2) +
         PowerSeries.C (c2 * (p : ZMod (p ^ 3))) * (PowerSeries.X ^ p * Q1) +
         PowerSeries.C (c1 * (p : ZMod (p ^ 3)) ^ 2) * (PowerSeries.X ^ p * R2) +
         PowerSeries.C (c2 * (p : ZMod (p ^ 3)) ^ 2) * (PowerSeries.X ^ p * R1)) +
        (p : PowerSeries (ZMod (p ^ 3))) ^ 3 * (Q1 * R2 + Q2 * R1 + (p : PowerSeries (ZMod (p ^ 3))) * (R1 * R2)) := by
      simp only [map_mul, map_add, map_pow, map_natCast]; ring
    rw [hexp, hp3, zero_mul, add_zero]
    simp only [map_add, PowerSeries.coeff_C_mul, coeff_X_pow_2p_eq_zero hp hd,
      coeff_X_pow_mul_eq_zero hd Q2 hQ20, coeff_X_pow_mul_eq_zero hd Q1 hQ10,
      coeff_X_pow_mul_eq_zero hd R2 hR20, coeff_X_pow_mul_eq_zero hd R1 hR10]
    ring

private lemma Good3.prod_zero {ι : Type*} {p : ℕ} (hp : 0 < p) (hp_odd : Odd p) (s : Finset ι)
    (f : ι → PowerSeries (ZMod (p ^ 3))) (hf : ∀ i ∈ s, Good3 p (f i) 0) :
    Good3 p (∏ i ∈ s, f i) 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Good3.one
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    have h := (hf a (Finset.mem_insert_self a s)).mul hp hp_odd
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))
    simpa only [add_zero] using h

/--
**OEIS A291697, Supercongruence Conjecture (Peter Bala, Apr 18 2023):**
For all primes $p \ge 5$, $a(p) \equiv 2p + 2 \pmod{p^3}$, i.e., $p^3 \mid (a(p) - (2p + 2))$.
-/
theorem conjecture_1 (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) :
    ((p : ℤ) ^ 3) ∣ (a p - (2 * p + 2)) := by
  have : NeZero (p ^ 3) := ⟨pow_ne_zero 3 hp.ne_zero⟩
  have hp_odd : Odd p := hp.odd_of_ne_two (by omega)
  let R := ZMod (p ^ 3)
  rw [show ((p : ℤ) ^ 3) = ((p ^ 3 : ℕ) : ℤ) by push_cast; rfl,
    ← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  apply sub_eq_zero.mpr
  let F : ℕ → PowerSeries R := fun m => PowerSeries.map (Int.castRingHom R) (factor m)
  have ha_eq : (a p : R) = PowerSeries.coeff p
      (∏ k ∈ Finset.range ((p + 1) / 2), (F (2 * k + 1)) ^ p) := by
    unfold a
    have h := PowerSeries.coeff_map (Int.castRingHom R) p
      (∏ k ∈ Finset.range ((p + 1) / 2), (factor (2 * k + 1)) ^ p)
    simpa only [F, map_prod, map_pow, eq_intCast] using h.symm
  rw [ha_eq]
  -- Helper: (1 - X^m)^p * (F m)^p = (1 + X^m)^p in PowerSeries R
  have hrel : ∀ m, 1 ≤ m →
      (1 - PowerSeries.X ^ m : PowerSeries R) ^ p * (F m) ^ p = (1 + PowerSeries.X ^ m : PowerSeries R) ^ p := by
    intro m hm
    have hZ := congrArg (· ^ p) (one_sub_X_pow_mul_factor hm)
    have hM := congrArg (PowerSeries.map (Int.castRingHom R)) hZ
    simp only [map_mul, map_pow, map_add, map_sub, map_one, PowerSeries.map_X] at hM
    rw [← mul_pow]; exact hM
  have hp3_zero : (p : PowerSeries R) ^ 3 = 0 := by
    rw [← Nat.cast_pow, ← map_natCast PowerSeries.C (p ^ 3), ZMod.natCast_self, map_zero]
  -- Split range ((p+1)/2) into {0}, {(p-1)/2}, and the rest
  have h0_mem : 0 ∈ Finset.range ((p + 1) / 2) := Finset.mem_range.mpr (by omega)
  have hlast_mem : (p - 1) / 2 ∈ (Finset.range ((p + 1) / 2)).erase 0 :=
    Finset.mem_erase.mpr ⟨by omega, Finset.mem_range.mpr (by omega)⟩
  rw [← Finset.mul_prod_erase _ _ h0_mem, ← Finset.mul_prod_erase _ _ hlast_mem]
  have hlast_val : 2 * ((p - 1) / 2) + 1 = p := by rcases hp_odd with ⟨t, ht⟩; omega
  rw [show 2 * 0 + 1 = 1 by rfl, hlast_val]
  -- 1. Factor m = 1: Good3 p (F 1 ^ p) 2
  have hG1 : Good3 p (F 1 ^ p) 2 := by
    set Px : PowerSeries R := Pseries p PowerSeries.X
    set Pnx : PowerSeries R := Pseries p (-PowerSeries.X)
    set Q1 : PowerSeries R := Px - Pnx
    set R1 : PowerSeries R := Pnx ^ 2 - Px * Pnx
    have hcPx : PowerSeries.constantCoeff Px = 0 := by
      rw [← PowerSeries.coeff_zero_eq_constantCoeff, coeff_Pseries_X]; simp
    have hcPnx : PowerSeries.constantCoeff Pnx = 0 := by
      rw [← PowerSeries.coeff_zero_eq_constantCoeff, coeff_Pseries_neg_X]; simp
    have hQ10 : PowerSeries.constantCoeff Q1 = 0 := by simp [Q1, hcPx, hcPnx]
    have hQ1p : PowerSeries.coeff p Q1 = 0 := by
      dsimp only [Q1]; rw [map_sub, coeff_Pseries_X, coeff_Pseries_neg_X]
      rw [if_neg (by omega), if_neg (by omega), sub_self]
    have hQ1odd : ∀ k, Even k → PowerSeries.coeff k Q1 = 0 := fun k hk => by
      rw [map_sub, coeff_Pseries_X, coeff_Pseries_neg_X]
      rcases hk with ⟨t, rfl⟩
      have h1 : (-1 : R) ^ (t + t) = 1 := by rw [← two_mul, pow_mul]; norm_num
      rw [h1, one_mul, sub_self]
    have hR10 : PowerSeries.constantCoeff R1 = 0 := by simp [R1, hcPx, hcPnx]
    -- Show coeff p (Px * Pnx) = 0 (even series)
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
    -- Show p^2 * coeff p (Pnx^2) = 0 in ZMod (p^3)
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
                      rw [Nat.factorial_succ]; push_cast; rw [pow_succ]
                      linear_combination (m.factorial : ZMod p) * hchZ - ((m : ZMod p) + 1) * ih (by omega)
                  have : Fact p.Prime := ⟨hp⟩
                  have hfnz : (((k - 1).factorial : ℕ) : ZMod p) ≠ 0 := fun h => by
                    have hd := (ZMod.natCast_eq_zero_iff _ p).mp h
                    have := hp.dvd_factorial.mp hd; omega
                  exact mul_left_cancel₀ hfnz (by rw [hfac (k - 1) (by omega)]; ring)
                have hZ := congrArg (Nat.cast (R := ZMod p)) hnat
                push_cast at hZ; rw [hch_pm1] at hZ
                have : Fact p.Prime := ⟨hp⟩
                have hkne : (k : ZMod p) ≠ 0 := fun h =>
                  Nat.not_dvd_of_pos_of_lt hk.1 (by omega) ((ZMod.natCast_eq_zero_iff k p).mp h)
                apply mul_left_cancel₀ hkne; rw [hZ]
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
    have hR1p : (p : R) ^ 2 * PowerSeries.coeff p R1 = 0 := by
      dsimp only [R1]; rw [map_sub, hPxPnx_p, sub_zero]; exact hp2_Pnxsq
    refine ⟨Q1, R1, hQ10, hQ1p, hQ1odd, hR10, hR1p, ?_⟩
    set G1 : PowerSeries R := 1 + PowerSeries.C (2 : R) * PowerSeries.X ^ p +
      (p : PowerSeries R) * Q1 + (p : PowerSeries R) ^ 2 * R1
    have hdiff := coeff_eq_zero_of_mul_eq_zero ((1 - PowerSeries.X : PowerSeries R) ^ p) (F 1 ^ p - G1)
      (by simp) p fun d hd => by
        rw [mul_sub, show (1 - PowerSeries.X : PowerSeries R) ^ p * F 1 ^ p = (1 + PowerSeries.X) ^ p by
          simpa only [pow_one] using hrel 1 le_rfl]
        rw [one_add_pow_p hp PowerSeries.X, one_sub_pow_p hp hp_odd PowerSeries.X]
        have hexp :
            (1 + PowerSeries.X ^ p + (p : PowerSeries R) * Px) -
            (1 - PowerSeries.X ^ p + (p : PowerSeries R) * Pnx) * G1 =
            PowerSeries.C (2 : R) * (PowerSeries.X ^ p * PowerSeries.X ^ p) +
            PowerSeries.C ((p : R)) * (PowerSeries.X ^ p * (Q1 - 2 * Pnx)) +
            PowerSeries.C ((p : R) ^ 2) * (PowerSeries.X ^ p * R1) -
            (p : PowerSeries R) ^ 3 * (Pnx * R1) := by
          dsimp only [G1, Q1, R1]
          simp only [map_ofNat, map_pow, map_natCast]; ring
        rw [hexp, hp3_zero, zero_mul, sub_zero, map_add, map_add,
          PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul,
          coeff_X_pow_2p_eq_zero hp.pos hd,
          coeff_X_pow_mul_eq_zero hd (Q1 - 2 * Pnx) (by simp [hQ10, hcPnx]),
          coeff_X_pow_mul_eq_zero hd R1 hR10]
        ring
    intro d hd
    exact sub_eq_zero.mp (by rw [← map_sub]; exact hdiff d hd)
  -- 2. Factor m = p: Good3 p (F p ^ p) (2 * p)
  have hGp : Good3 p (F p ^ p) (2 * (p : R)) := by
    refine ⟨0, 0, by simp, by simp, fun _ _ => by simp, by simp, by simp, ?_⟩
    set Gp : PowerSeries R := 1 + PowerSeries.C (2 * (p : R)) * PowerSeries.X ^ p +
      (p : PowerSeries R) * 0 + (p : PowerSeries R) ^ 2 * 0
    have hdiff := coeff_eq_zero_of_mul_eq_zero ((1 - PowerSeries.X ^ p : PowerSeries R) ^ p) (F p ^ p - Gp)
      (by simp [hp.ne_zero]) p fun d hd => by
        rw [mul_sub, hrel p hp.one_le]
        have hpow_agree : ∀ (c : R), ∀ k ≤ p,
            PowerSeries.coeff k ((1 + PowerSeries.C c * PowerSeries.X ^ p : PowerSeries R) ^ p) =
            PowerSeries.coeff k (1 + PowerSeries.C ((p : R) * c) * PowerSeries.X ^ p) := by
          intro c k hk
          rw [add_comm, add_pow]
          have h0 : 0 ∈ Finset.range (p + 1) := Finset.mem_range.mpr (by omega)
          have h1 : 1 ∈ (Finset.range (p + 1)).erase 0 :=
            Finset.mem_erase.mpr ⟨one_ne_zero, Finset.mem_range.mpr (by omega)⟩
          rw [← Finset.add_sum_erase _ _ h0, ← Finset.add_sum_erase _ _ h1]
          simp only [pow_zero, pow_one, one_pow, mul_one, Nat.choose_zero_right,
            Nat.choose_one_right, Nat.cast_one]
          rw [map_add, map_add]
          have hrest : PowerSeries.coeff k
              (∑ x ∈ ((Finset.range (p + 1)).erase 0).erase 1,
                (PowerSeries.C c * PowerSeries.X ^ p : PowerSeries R) ^ x * (p.choose x : PowerSeries R)) = 0 := by
            rw [map_sum]
            refine Finset.sum_eq_zero fun x hx => ?_
            simp only [Finset.mem_erase, Finset.mem_range] at hx
            have hx2 : 2 ≤ x := by omega
            have hne : k ≠ p * x := by have := hp.pos; nlinarith
            rw [mul_pow, ← pow_mul, ← map_pow, mul_comm _ (p.choose x : PowerSeries R), ← mul_assoc,
              show (p.choose x : PowerSeries R) = PowerSeries.C ((p.choose x : ℕ) : R) from
                (map_natCast PowerSeries.C (p.choose x)).symm,
              ← map_mul, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow, if_neg hne, mul_zero]
          rw [hrest, add_zero,
            show (PowerSeries.C c * PowerSeries.X ^ p : PowerSeries R) * (p : PowerSeries R) =
              PowerSeries.C ((p : R) * c) * PowerSeries.X ^ p by
                rw [show (p : PowerSeries R) = PowerSeries.C (p : R) from (map_natCast PowerSeries.C p).symm,
                  map_mul]; ring,
            ← map_add]
        have hpos : PowerSeries.coeff d ((1 + PowerSeries.X ^ p : PowerSeries R) ^ p) =
            PowerSeries.coeff d (1 + PowerSeries.C (p : R) * PowerSeries.X ^ p) := by
          have := hpow_agree 1 d hd
          simpa only [map_one, one_mul, mul_one] using this
        have hneg : ∀ k ≤ p, PowerSeries.coeff k ((1 - PowerSeries.X ^ p : PowerSeries R) ^ p) =
            PowerSeries.coeff k (1 + PowerSeries.C (-(p : R)) * PowerSeries.X ^ p) := fun k hk => by
          have := hpow_agree (-1) k hk
          rw [show (1 + PowerSeries.C (-1 : R) * PowerSeries.X ^ p : PowerSeries R) = 1 - PowerSeries.X ^ p by
            simp; ring, mul_neg_one] at this
          exact this
        rw [map_sub, hpos, coeff_eq_of_eq_le _ _ Gp Gp hneg (fun _ _ => rfl) d hd]
        have hexp : (1 + PowerSeries.C (-(p : R)) * PowerSeries.X ^ p) * Gp =
            (1 + PowerSeries.C (p : R) * PowerSeries.X ^ p) +
            PowerSeries.C (-(p : R) * (2 * (p : R))) * (PowerSeries.X ^ p * PowerSeries.X ^ p) := by
          dsimp only [Gp]; simp only [mul_zero, add_zero, map_mul, map_neg, map_ofNat]; ring
        rw [hexp]
        simp only [map_add, PowerSeries.coeff_C_mul, coeff_X_pow_2p_eq_zero hp.pos hd]
        ring
    intro d hd
    exact sub_eq_zero.mp (by rw [← map_sub]; exact hdiff d hd)
  -- 3. Middle factors k ∈ ((range ((p+1)/2)).erase 0).erase ((p-1)/2): Good3 p (F (2k+1) ^ p) 0
  have hGmid : Good3 p
      (∏ k ∈ ((Finset.range ((p + 1) / 2)).erase 0).erase ((p - 1) / 2), (F (2 * k + 1)) ^ p) 0 := by
    refine Good3.prod_zero hp.pos hp_odd _ _ fun k hk => ?_
    simp only [Finset.mem_erase, Finset.mem_range] at hk
    set m : ℕ := 2 * k + 1
    have hm_ge3 : 3 ≤ m := by omega
    have hm_lt : m < p := by omega
    have hm_odd : Odd m := ⟨k, rfl⟩
    have hm_ndiv_p : ¬ m ∣ p := fun hd =>
      (hp.eq_one_or_self_of_dvd m hd).elim (by omega) (by omega)
    set Pm : PowerSeries R := Pseries p (PowerSeries.X ^ m)
    set Pnm : PowerSeries R := Pseries p (-PowerSeries.X ^ m)
    set Qm : PowerSeries R := Pm - Pnm
    set Rm : PowerSeries R := Pnm ^ 2 - Pm * Pnm
    have hPm_ndiv : ∀ d, ¬ m ∣ d → PowerSeries.coeff d Pm = 0 := fun d hd => by
      have : Pm = Pseries p (PowerSeries.C (1 : R) * PowerSeries.X ^ m) := by simp [Pm]
      rw [this]; exact coeff_Pseries_Xm_eq_zero hd 1
    have hPnm_ndiv : ∀ d, ¬ m ∣ d → PowerSeries.coeff d Pnm = 0 := fun d hd => by
      have : Pnm = Pseries p (PowerSeries.C (-1 : R) * PowerSeries.X ^ m) := by
        dsimp only [Pnm]; congr 1; simp; ring
      rw [this]; exact coeff_Pseries_Xm_eq_zero hd (-1)
    have hcPm : PowerSeries.constantCoeff Pm = 0 := by
      rw [← PowerSeries.coeff_zero_eq_constantCoeff]; dsimp only [Pm]; unfold Pseries; rw [map_sum]
      refine Finset.sum_eq_zero fun j hj => ?_
      simp only [Finset.mem_Icc] at hj
      rw [← pow_mul, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow,
        if_neg (by nlinarith : 0 ≠ m * j), mul_zero]
    have hcPnm : PowerSeries.constantCoeff Pnm = 0 := by
      rw [← PowerSeries.coeff_zero_eq_constantCoeff]
      have h0 : Pnm = Pseries p (PowerSeries.C (-1 : R) * PowerSeries.X ^ m) := by
        dsimp only [Pnm]; congr 1; simp; ring
      rw [h0]; unfold Pseries; rw [map_sum]
      refine Finset.sum_eq_zero fun j hj => ?_
      simp only [Finset.mem_Icc] at hj
      rw [mul_pow, ← pow_mul, ← map_pow, ← mul_assoc, ← map_mul, PowerSeries.coeff_C_mul,
        PowerSeries.coeff_X_pow, if_neg (by nlinarith : 0 ≠ m * j), mul_zero]
    have hQm0 : PowerSeries.constantCoeff Qm = 0 := by simp [Qm, hcPm, hcPnm]
    have hQmp : PowerSeries.coeff p Qm = 0 := by
      dsimp only [Qm]; rw [map_sub, hPm_ndiv p hm_ndiv_p, hPnm_ndiv p hm_ndiv_p, sub_self]
    have hQmodd : ∀ d, Even d → PowerSeries.coeff d Qm = 0 := fun d hd => by
      dsimp only [Qm]; rw [map_sub]
      by_cases hmd : m ∣ d
      · obtain ⟨q, rfl⟩ := hmd
        have hq_even : Even q := by
          rcases Nat.even_or_odd q with h | ⟨t, rfl⟩
          · exact h
          · exfalso; rcases hd with ⟨s, hs⟩; rcases hm_odd with ⟨r, hr⟩
            have hodd : m * (2 * t + 1) = 2 * (2 * r * t + r + t) + 1 := by rw [hr]; ring
            omega
        have h1 : PowerSeries.coeff (m * q) Pm =
            if 1 ≤ q ∧ q ≤ p - 1 then ((p.choose q / p : ℕ) : R) else 0 := by
          dsimp only [Pm]; unfold Pseries; rw [map_sum]
          have ht : ∀ j ∈ Finset.Icc 1 (p - 1),
              PowerSeries.coeff (m * q) (PowerSeries.C (((p.choose j / p : ℕ) : R)) * (PowerSeries.X ^ m) ^ j) =
              if q = j then ((p.choose j / p : ℕ) : R) else 0 := by
            intro j _
            rw [← pow_mul, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow]
            have hiff : m * q = m * j ↔ q = j := Nat.mul_right_inj (by omega)
            simp only [hiff]; split_ifs <;> ring
          rw [Finset.sum_congr rfl ht, Finset.sum_ite_eq]; simp only [Finset.mem_Icc]
        have h2 : PowerSeries.coeff (m * q) Pnm =
            if 1 ≤ q ∧ q ≤ p - 1 then (-1 : R) ^ q * ((p.choose q / p : ℕ) : R) else 0 := by
          have h0 : Pnm = Pseries p (PowerSeries.C (-1 : R) * PowerSeries.X ^ m) := by
            dsimp only [Pnm]; congr 1; simp; ring
          rw [h0]; unfold Pseries; rw [map_sum]
          have ht : ∀ j ∈ Finset.Icc 1 (p - 1),
              PowerSeries.coeff (m * q) (PowerSeries.C (((p.choose j / p : ℕ) : R)) *
                (PowerSeries.C (-1 : R) * PowerSeries.X ^ m) ^ j) =
              if q = j then (-1 : R) ^ j * ((p.choose j / p : ℕ) : R) else 0 := by
            intro j _
            rw [mul_pow, ← pow_mul, ← map_pow, ← mul_assoc, ← map_mul, PowerSeries.coeff_C_mul,
              PowerSeries.coeff_X_pow]
            have hiff : m * q = m * j ↔ q = j := Nat.mul_right_inj (by omega)
            simp only [hiff]; split_ifs <;> ring
          rw [Finset.sum_congr rfl ht, Finset.sum_ite_eq]; simp only [Finset.mem_Icc]
        rw [h1, h2]
        rcases hq_even with ⟨t, rfl⟩
        have hpow : (-1 : R) ^ (t + t) = 1 := by rw [← two_mul, pow_mul]; norm_num
        rw [hpow, one_mul, sub_self]
      · rw [hPm_ndiv d hmd, hPnm_ndiv d hmd, sub_self]
    have hRm0 : PowerSeries.constantCoeff Rm = 0 := by simp [Rm, hcPm, hcPnm]
    have hRmp : (p : R) ^ 2 * PowerSeries.coeff p Rm = 0 := by
      dsimp only [Rm]
      rw [map_sub, show Pnm ^ 2 = Pnm * Pnm from sq Pnm,
        coeff_mul_eq_zero_of_dvdm Pnm Pnm hPnm_ndiv hPnm_ndiv hm_ndiv_p,
        coeff_mul_eq_zero_of_dvdm Pm Pnm hPm_ndiv hPnm_ndiv hm_ndiv_p, sub_self, mul_zero]
    refine ⟨Qm, Rm, hQm0, hQmp, hQmodd, hRm0, hRmp, ?_⟩
    set Gm : PowerSeries R := 1 + PowerSeries.C (0 : R) * PowerSeries.X ^ p +
      (p : PowerSeries R) * Qm + (p : PowerSeries R) ^ 2 * Rm
    have hdiff := coeff_eq_zero_of_mul_eq_zero ((1 - PowerSeries.X ^ m : PowerSeries R) ^ p) (F m ^ p - Gm)
      (by simp [show m ≠ 0 by omega]) p fun d hd => by
        rw [mul_sub, hrel m (by omega), one_add_pow_p hp (PowerSeries.X ^ m),
          one_sub_pow_p hp hp_odd (PowerSeries.X ^ m)]
        have hXmp_mul : ∀ A : PowerSeries R, PowerSeries.coeff d ((PowerSeries.X ^ m : PowerSeries R) ^ p * A) = 0 := by
          intro A
          rw [← pow_mul, PowerSeries.coeff_mul]
          refine Finset.sum_eq_zero fun x hx => ?_
          rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
          have hne : x.1 ≠ m * p := by have := hp.pos; nlinarith
          rw [PowerSeries.coeff_X_pow, if_neg hne, zero_mul]
        have hexp :
            (1 + (PowerSeries.X ^ m : PowerSeries R) ^ p + (p : PowerSeries R) * Pm) -
            (1 - (PowerSeries.X ^ m : PowerSeries R) ^ p + (p : PowerSeries R) * Pnm) * Gm =
            (PowerSeries.X ^ m : PowerSeries R) ^ p * (1 + Gm) -
            (p : PowerSeries R) ^ 3 * (Pnm * Rm) := by
          dsimp only [Gm, Qm, Rm]
          simp only [map_zero, zero_mul, add_zero]; ring
        rw [hexp, hp3_zero, zero_mul, sub_zero, hXmp_mul]
    intro d hd
    exact sub_eq_zero.mp (by rw [← map_sub]; exact hdiff d hd)
  -- Combine all factors!
  have hGall := hG1.mul hp.pos hp_odd (hGp.mul hp.pos hp_odd hGmid)
  rcases hGall with ⟨Q, R', _, hQp, _, _, hRp, hQeq⟩
  rw [hQeq p le_rfl, map_add, map_add, map_add, PowerSeries.coeff_one, if_neg hp.ne_zero, zero_add,
    PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow, if_pos rfl, mul_one,
    show (p : PowerSeries R) = PowerSeries.C (p : R) from (map_natCast PowerSeries.C p).symm,
    ← map_pow, PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul, hQp, mul_zero, add_zero, hRp, add_zero]
  ring


end SolvedConjecture09

theorem OMA.solution : type_of% @OMA.S_oeis_a291697.main := by
  intro p hp hp5
  exact SolvedConjecture09.conjecture_1 p hp hp5
