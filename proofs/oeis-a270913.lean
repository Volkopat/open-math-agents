import OMAStatements.S_oeis_a270913
import Mathlib

/-!
# Proof of OEIS A270913, Supercongruence Conjecture (Peter Bala, Apr 18 2023)

Official OEIS entry [A270913](https://oeis.org/A270913):
$$a(n) = [x^n] \prod_{k \ge 1} (1 + x^k)^n = [x^n] \prod_{k=1}^{n} (1 + x^k)^n.$$
Conjecture (Peter Bala, Apr 18 2023): For all primes $p$,
$$a(p) \equiv p + 1 \pmod{p^2}.$$

## Proof Overview (100% elementary, zero `sorry`, zero custom axioms)
Work in $(\mathbb{Z}/p^2\mathbb{Z})[[x]]$. Call a power series $F$ **good** for $c \in \mathbb{Z}/p^2\mathbb{Z}$
if there exists $Q \in (\mathbb{Z}/p^2\mathbb{Z})[[x]]$ with $Q(0) = 0$ and $[x^p] Q = 0$ such that
$F$ agrees with $1 + c x^p + p Q(x)$ in all degrees $d \le p$.
1. The `Good` property is multiplicative: if $F$ is good for $c_1$ and $G$ is good for $c_2$,
   then $F \cdot G$ is good for $c_1 + c_2$ (since $x^{2p} \equiv 0$, $x^p Q \equiv 0 \pmod{x^{p+1}}$,
   and $p^2 = 0$ in $\mathbb{Z}/p^2\mathbb{Z}$).
2. For $k = 1$: $(1 + x)^p = 1 + x^p + p P_p(x)$ is good for $1$ (since $\deg P_p \le p - 1 < p$).
3. For $k = p$: $(1 + x^p)^p = 1 + p x^p + \sum_{j=2}^p \binom{p}{j} x^{pj}$ agrees with $1 + p x^p$
   in all degrees $d \le p$, so it is good for $p$.
4. For $2 \le k \le p - 1$: $(1 + x^k)^p = 1 + x^{kp} + p P_p(x^k)$ agrees with $1 + p P_p(x^k)$
   in all degrees $d \le p$, and $[x^p] P_p(x^k) = 0$ since $k \nmid p$; so it is good for $0$.
5. Multiplying all $k \in \{1, \dots, p\}$ together yields that $\prod_{k=1}^p (1 + x^k)^p$ is good
   for $1 + p + 0 = p + 1$. Extracting $[x^p]$ gives $a(p) \equiv p + 1 \pmod{p^2}$ for all primes $p$.
-/

namespace SolvedConjecture08

open Finset BigOperators PowerSeries

/-- OEIS A270913: $a(n) = [x^n] \prod_{k=1}^{n} (1 + x^k)^n$. -/
noncomputable def a (n : ℕ) : ℤ :=
  PowerSeries.coeff n (∏ k ∈ Finset.Icc 1 n, (1 + PowerSeries.X ^ k : PowerSeries ℤ) ^ n)

/-- The quotient polynomial $P_p(t) = \sum_{j=1}^{p-1} (\binom{p}{j}/p) t^j$ in $R[[x]]$. -/
private noncomputable def Pseries {R : Type*} [CommRing R] (p : ℕ) (t : PowerSeries R) : PowerSeries R :=
  ∑ j ∈ Finset.Icc 1 (p - 1), PowerSeries.C (((p.choose j / p : ℕ) : R)) * t ^ j

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

/-- `Good p F c` means $F \equiv 1 + c x^p + p Q(x) \pmod{x^{p+1}}$ in $(\mathbb{Z}/p^2\mathbb{Z})[[x]]$
for some $Q$ with $Q(0) = 0$ and $[x^p] Q = 0$. -/
private def Good (p : ℕ) (F : PowerSeries (ZMod (p ^ 2))) (c : ZMod (p ^ 2)) : Prop :=
  ∃ Q : PowerSeries (ZMod (p ^ 2)),
    PowerSeries.constantCoeff Q = 0 ∧
    PowerSeries.coeff p Q = 0 ∧
    ∀ d ≤ p, PowerSeries.coeff d F =
      PowerSeries.coeff d (1 + PowerSeries.C c * PowerSeries.X ^ p +
        (p : PowerSeries (ZMod (p ^ 2))) * Q)

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

private lemma Good.one {p : ℕ} : Good p 1 0 :=
  ⟨0, by simp, by simp, fun _ _ => by simp⟩

private lemma Good.mul {p : ℕ} (hp : 0 < p) {F G : PowerSeries (ZMod (p ^ 2))}
    {c1 c2 : ZMod (p ^ 2)} (hF : Good p F c1) (hG : Good p G c2) :
    Good p (F * G) (c1 + c2) := by
  rcases hF with ⟨Q1, hQ10, hQ1p, hFeq⟩
  rcases hG with ⟨Q2, hQ20, hQ2p, hGeq⟩
  refine ⟨Q1 + Q2, by simp [hQ10, hQ20], by simp [hQ1p, hQ2p], fun d hd => ?_⟩
  rw [coeff_eq_of_eq_le F _ G _ hFeq hGeq d hd]
  have hp2 : (p : PowerSeries (ZMod (p ^ 2))) ^ 2 = 0 := by
    rw [← Nat.cast_pow, ← map_natCast PowerSeries.C (p ^ 2), ZMod.natCast_self, map_zero]
  have hexp : (1 + PowerSeries.C c1 * PowerSeries.X ^ p + (p : PowerSeries (ZMod (p ^ 2))) * Q1) *
      (1 + PowerSeries.C c2 * PowerSeries.X ^ p + (p : PowerSeries (ZMod (p ^ 2))) * Q2) =
    (1 + PowerSeries.C (c1 + c2) * PowerSeries.X ^ p + (p : PowerSeries (ZMod (p ^ 2))) * (Q1 + Q2)) +
    PowerSeries.C (c1 * c2) * (PowerSeries.X ^ p * PowerSeries.X ^ p) +
    (PowerSeries.C (c1 * (p : ZMod (p ^ 2))) * (PowerSeries.X ^ p * Q2) +
     PowerSeries.C (c2 * (p : ZMod (p ^ 2))) * (PowerSeries.X ^ p * Q1)) +
    (p : PowerSeries (ZMod (p ^ 2))) ^ 2 * (Q1 * Q2) := by
    simp only [map_mul, map_add, map_natCast]; ring
  rw [hexp, hp2, zero_mul, add_zero]
  simp only [map_add, PowerSeries.coeff_C_mul, coeff_X_pow_2p_eq_zero hp hd,
    coeff_X_pow_mul_eq_zero hd Q2 hQ20, coeff_X_pow_mul_eq_zero hd Q1 hQ10]
  ring

private lemma Good.prod_zero {ι : Type*} {p : ℕ} (hp : 0 < p) (s : Finset ι)
    (f : ι → PowerSeries (ZMod (p ^ 2))) (hf : ∀ i ∈ s, Good p (f i) 0) :
    Good p (∏ i ∈ s, f i) 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Good.one
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    have h := (hf a (Finset.mem_insert_self a s)).mul hp
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))
    simpa only [add_zero] using h

/--
**OEIS A270913, Supercongruence Conjecture (Peter Bala, Apr 18 2023):**
For all primes $p$, $a(p) \equiv p + 1 \pmod{p^2}$, i.e., $p^2 \mid (a(p) - (p + 1))$.
-/
theorem conjecture_1 (p : ℕ) (hp : p.Prime) :
    ((p : ℤ) ^ 2) ∣ (a p - (p + 1)) := by
  let R := ZMod (p ^ 2)
  rw [show ((p : ℤ) ^ 2) = ((p ^ 2 : ℕ) : ℤ) by push_cast; rfl,
    ← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  apply sub_eq_zero.mpr
  have ha_eq : (a p : R) = PowerSeries.coeff p
      (∏ k ∈ Finset.Icc 1 p, (1 + PowerSeries.X ^ k : PowerSeries R) ^ p) := by
    unfold a
    have h := PowerSeries.coeff_map (Int.castRingHom R) p
      (∏ k ∈ Finset.Icc 1 p, (1 + PowerSeries.X ^ k : PowerSeries ℤ) ^ p)
    simpa only [map_prod, map_pow, map_add, map_one, PowerSeries.map_X, eq_intCast] using h.symm
  rw [ha_eq]
  -- Split Icc 1 p into {1}, {p}, and Icc 2 (p - 1)
  have hp2 : 2 ≤ p := hp.two_le
  have h1_mem : 1 ∈ Finset.Icc 1 p := Finset.mem_Icc.mpr ⟨le_rfl, hp.one_le⟩
  have hp_mem : p ∈ (Finset.Icc 1 p).erase 1 :=
    Finset.mem_erase.mpr ⟨by omega, Finset.mem_Icc.mpr ⟨hp.one_le, le_rfl⟩⟩
  have hset : ((Finset.Icc 1 p).erase 1).erase p = Finset.Icc 2 (p - 1) := by
    ext k; simp only [Finset.mem_erase, Finset.mem_Icc]; omega
  rw [← Finset.mul_prod_erase _ _ h1_mem, ← Finset.mul_prod_erase _ _ hp_mem, hset]
  -- Factor 1: (1 + X)^p is Good for 1
  have hG1 : Good p ((1 + PowerSeries.X ^ 1 : PowerSeries R) ^ p) 1 := by
    rw [pow_one, one_add_pow_p hp PowerSeries.X]
    refine ⟨Pseries p PowerSeries.X, ?_, ?_, fun d _ => by simp⟩
    · rw [← PowerSeries.coeff_zero_eq_constantCoeff]; unfold Pseries; rw [map_sum]
      refine Finset.sum_eq_zero fun j hj => ?_
      simp only [Finset.mem_Icc] at hj
      rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow, if_neg (by omega), mul_zero]
    · unfold Pseries; rw [map_sum]
      refine Finset.sum_eq_zero fun j hj => ?_
      simp only [Finset.mem_Icc] at hj
      rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow, if_neg (by omega), mul_zero]
  -- Factor p: (1 + X^p)^p is Good for p
  have hGp : Good p ((1 + PowerSeries.X ^ p : PowerSeries R) ^ p) (p : R) := by
    refine ⟨0, by simp, by simp, fun d hd => ?_⟩
    rw [mul_zero, add_zero, add_comm, add_pow]
    have h0 : 0 ∈ Finset.range (p + 1) := Finset.mem_range.mpr (by omega)
    have h1 : 1 ∈ (Finset.range (p + 1)).erase 0 :=
      Finset.mem_erase.mpr ⟨one_ne_zero, Finset.mem_range.mpr (by omega)⟩
    rw [← Finset.add_sum_erase _ _ h0, ← Finset.add_sum_erase _ _ h1]
    simp only [pow_zero, pow_one, one_pow, mul_one, Nat.choose_zero_right,
      Nat.choose_one_right, Nat.cast_one]
    rw [map_add, map_add]
    have hrest : PowerSeries.coeff d
        (∑ x ∈ ((Finset.range (p + 1)).erase 0).erase 1,
          (PowerSeries.X ^ p : PowerSeries R) ^ x * (p.choose x : PowerSeries R)) = 0 := by
      rw [map_sum]
      refine Finset.sum_eq_zero fun x hx => ?_
      simp only [Finset.mem_erase, Finset.mem_range] at hx
      have hx2 : 2 ≤ x := by omega
      have hne : d ≠ p * x := by have := hp.pos; nlinarith
      rw [← pow_mul, mul_comm,
        show (p.choose x : PowerSeries R) = PowerSeries.C ((p.choose x : ℕ) : R) from
          (map_natCast PowerSeries.C (p.choose x)).symm,
        PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow, if_neg hne, mul_zero]
    rw [hrest, add_zero, show (PowerSeries.X ^ p : PowerSeries R) * (p : PowerSeries R) =
      PowerSeries.C (p : R) * PowerSeries.X ^ p by
        rw [show (p : PowerSeries R) = PowerSeries.C (p : R) from (map_natCast PowerSeries.C p).symm, mul_comm],
      ← map_add]
  -- Middle factors k ∈ Icc 2 (p - 1): (1 + X^k)^p is Good for 0
  have hGmid : Good p (∏ k ∈ Finset.Icc 2 (p - 1), (1 + PowerSeries.X ^ k : PowerSeries R) ^ p) 0 := by
    refine Good.prod_zero hp.pos (Finset.Icc 2 (p - 1)) _ fun k hk => ?_
    simp only [Finset.mem_Icc] at hk
    rw [one_add_pow_p hp (PowerSeries.X ^ k)]
    refine ⟨Pseries p (PowerSeries.X ^ k), ?_, ?_, fun d hd => ?_⟩
    · rw [← PowerSeries.coeff_zero_eq_constantCoeff]; unfold Pseries; rw [map_sum]
      refine Finset.sum_eq_zero fun j hj => ?_
      simp only [Finset.mem_Icc] at hj
      rw [← pow_mul, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow,
        if_neg (by nlinarith : 0 ≠ k * j), mul_zero]
    · unfold Pseries; rw [map_sum]
      refine Finset.sum_eq_zero fun j hj => ?_
      simp only [Finset.mem_Icc] at hj
      rw [← pow_mul, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow]
      have hne : p ≠ k * j := by
        intro heq
        rcases hp.eq_one_or_self_of_dvd k ⟨j, heq⟩ with h | h <;> omega
      rw [if_neg hne, mul_zero]
    · simp only [map_zero, zero_mul, add_zero]
      have hXkp : PowerSeries.coeff d ((PowerSeries.X ^ k : PowerSeries R) ^ p) = 0 := by
        rw [← pow_mul, PowerSeries.coeff_X_pow,
          if_neg (by have := hp.pos; nlinarith : d ≠ k * p)]
      have hrew : (1 : PowerSeries R) + (PowerSeries.X ^ k) ^ p +
          (p : PowerSeries R) * Pseries p (PowerSeries.X ^ k) =
          (1 + (p : PowerSeries R) * Pseries p (PowerSeries.X ^ k)) + (PowerSeries.X ^ k) ^ p := by
        ring
      rw [hrew, map_add, hXkp, add_zero]
  -- Combine all factors!
  have hGall := hG1.mul hp.pos (hGp.mul hp.pos hGmid)
  rcases hGall with ⟨Q, _, hQp, hQeq⟩
  rw [hQeq p le_rfl, map_add, map_add, PowerSeries.coeff_one, if_neg hp.ne_zero, zero_add,
    PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow, if_pos rfl, mul_one,
    show (p : PowerSeries R) = PowerSeries.C (p : R) from (map_natCast PowerSeries.C p).symm,
    PowerSeries.coeff_C_mul, hQp, mul_zero, add_zero]
  ring


end SolvedConjecture08

theorem OMA.solution : type_of% @OMA.S_oeis_a270913.main := by
  intro p hp
  exact SolvedConjecture08.conjecture_1 p hp
