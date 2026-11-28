import OMAStatements.S_oeis_a375180
import Mathlib

/-!
# Proof of OEIS A375180, Generalized Conjecture A (and Conjecture 1)
(Peter Bala, August 2024)

Official OEIS entry [A375180](https://oeis.org/A375180):
$$a(n) = \sum_{k=0}^{n-1} (-1)^{n+k+1} \binom{3n}{k}^3$$
and the generalized family for $m \ge 1$:
$$b_m(n) = \sum_{k=0}^{n-1} (-1)^{n+k+1} \binom{3n}{k}^{2m+1}.$$

- **Conjecture A (Generalized):** For all $m \ge 1$ and all primes $p \ge 2m + 5$,
  $$b_m(p) \equiv 1 \pmod{p^{2m+3}}.$$
- **Conjecture 1 ($m = 1$, A375180):** For all primes $p \ge 7$,
  $$a(p) \equiv 1 \pmod{p^5}.$$

## Proof Overview (100% elementary, zero `sorry`, zero custom axioms)
Since $p \ge 2m + 5 \ge 7$ is odd, $(-1)^{p+k+1} = (-1)^k$. The $k = 0$ term is $1$.
For $1 \le k \le p - 1$, $k \binom{3p}{k} = 3p \binom{3p-1}{k-1}$, so $p \mid \binom{3p}{k}$ and
$C_k := \binom{3p}{k} / p$ satisfies in $\mathbb{Z}/p^2\mathbb{Z}$:
$$C_k \equiv (-1)^{k-1} 3 k^{-1} (1 - 3p H_{k-1}) \pmod{p^2}$$
where $H_{k-1} = \sum_{j=1}^{k-1} j^{-1}$.
Raising to the odd power $2m + 1$ modulo $p^2$ (where $p^2 = 0$) gives:
$$(-1)^k C_k^{2m+1} \equiv -3^{2m+1} k^{-(2m+1)} (1 - 3(2m+1) p H_{k-1}) \pmod{p^2}.$$
Summing over $k = 1, \dots, p - 1$:
1. Pairing $k$ with $p - k$ in $\mathbb{Z}/p^2\mathbb{Z}$ gives
   $2 \sum_{k=1}^{p-1} k^{-(2m+1)} = -(2m+1) p \sum_{k=1}^{p-1} k^{-(2m+2)}$.
2. Pairing $k$ with $p - k$ in $\mathbb{Z}/p\mathbb{Z}$ (using $H_{p-k-1} \equiv H_{k-1} + k^{-1} \pmod p$)
   gives $2 \sum_{k=1}^{p-1} k^{-(2m+1)} H_{k-1} \equiv -\sum_{k=1}^{p-1} k^{-(2m+2)} \pmod p$.
Since $p \ge 2m + 5$, $(\mathbb{Z}/p\mathbb{Z})^\times$ is cyclic of order $p - 1 > 2m + 2$, so
$\sum_{k=1}^{p-1} k^{-(2m+2)} \equiv 0 \pmod p$. Hence both sums vanish modulo $p^2$ (resp. $p$),
so $p^2 \mid \sum_{k=1}^{p-1} (-1)^k C_k^{2m+1}$, and multiplying by $p^{2m+1}$ yields
$p^{2m+3} \mid (b_m(p) - 1)$.
-/

namespace SolvedConjecture05

open Finset BigOperators

/-- Generalized OEIS A375180 family $b_m(n) = \sum_{k=0}^{n-1} (-1)^{n+k+1} \binom{3n}{k}^{2m+1}$. -/
def b (m n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range n, (-1 : ℤ) ^ (n + k + 1) * ((3 * n).choose k : ℤ) ^ (2 * m + 1)

/-- OEIS A375180 sequence $a(n) = b_1(n) = \sum_{k=0}^{n-1} (-1)^{n+k+1} \binom{3n}{k}^3$. -/
def a (n : ℕ) : ℤ := b 1 n

private lemma isUnit_zmod_p2 {p k : ℕ} (hp : p.Prime) (hk0 : 0 < k) (hkp : k < p) :
    IsUnit (k : ZMod (p ^ 2)) := by
  rw [ZMod.isUnit_iff_coprime]
  exact ((hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt hk0 hkp)).symm).pow_right 2

private lemma mul_inv_zmod_p2 {p k : ℕ} (hp : p.Prime) (hk0 : 0 < k) (hkp : k < p) :
    (k : ZMod (p ^ 2)) * (k : ZMod (p ^ 2))⁻¹ = 1 :=
  ZMod.mul_inv_of_unit _ (isUnit_zmod_p2 hp hk0 hkp)

private lemma p_sq_eq_zero (p : ℕ) : ((p : ZMod (p ^ 2)) ^ 2) = 0 := by
  rw [← Nat.cast_pow, ZMod.natCast_self]

/-- Harmonic sum $H_m = \sum_{j=1}^m j^{-1}$ in $\mathbb{Z}/p^2\mathbb{Z}$. -/
private def H (p m : ℕ) : ZMod (p ^ 2) :=
  ∑ j ∈ Finset.Icc 1 m, (j : ZMod (p ^ 2))⁻¹

private lemma prod_one_sub_3p_inv (p m : ℕ) :
    ∏ j ∈ Finset.Icc 1 m, (1 - 3 * (p : ZMod (p ^ 2)) * (j : ZMod (p ^ 2))⁻¹) =
      1 - 3 * (p : ZMod (p ^ 2)) * H p m := by
  induction m with
  | zero => simp [H]
  | succ m ih =>
    rw [show Finset.Icc 1 (m + 1) = insert (m + 1) (Finset.Icc 1 m) by
      ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega]
    rw [Finset.prod_insert (by simp), ih]
    have hH : H p (m + 1) = H p m + ((m + 1 : ℕ) : ZMod (p ^ 2))⁻¹ := by
      unfold H
      rw [show Finset.Icc 1 (m + 1) = insert (m + 1) (Finset.Icc 1 m) by
        ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega]
      rw [Finset.sum_insert (by simp), add_comm]
    rw [hH]
    linear_combination (9 * ((m + 1 : ℕ) : ZMod (p ^ 2))⁻¹ * H p m) * p_sq_eq_zero p

/-- $p \mid \binom{3p}{k}$ for $1 \le k \le p - 1$. -/
private lemma p_dvd_choose_3p {p k : ℕ} (hp : p.Prime) (hk0 : 0 < k) (hkp : k < p) :
    p ∣ (3 * p).choose k := by
  have h1 : k * (3 * p).choose k = (3 * p) * (3 * p - 1).choose (k - 1) := by
    have := Nat.add_one_mul_choose_eq (3 * p - 1) (k - 1)
    rw [Nat.sub_add_cancel (by omega), Nat.sub_add_cancel hk0] at this
    linarith
  have hdvd : p ∣ k * (3 * p).choose k := by
    rw [h1]; exact dvd_mul_of_dvd_left (dvd_mul_left p 3) _
  exact (hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt hk0 hkp)).dvd_of_dvd_mul_left hdvd

/-- Exact formula for $\binom{3p}{k} / p$ in $\mathbb{Z}/p^2\mathbb{Z}$. -/
private lemma choose_3p_div_p_zmod {p k : ℕ} (hp : p.Prime) (hk0 : 0 < k) (hkp : k < p) :
    (((3 * p).choose k / p : ℕ) : ZMod (p ^ 2)) =
      (-1 : ZMod (p ^ 2)) ^ (k - 1) * 3 * (k : ZMod (p ^ 2))⁻¹ *
        (1 - 3 * (p : ZMod (p ^ 2)) * H p (k - 1)) := by
  -- Step 1: (k-1)! * C(3p-1, k-1) = ∏_{j=1}^{k-1} (3p - j) in ℤ
  have hfac : ∀ m < p, ((m.factorial : ℕ) : ZMod (p ^ 2)) * (((3 * p - 1).choose m : ℕ) : ZMod (p ^ 2)) =
      ∏ j ∈ Finset.Icc 1 m, (3 * (p : ZMod (p ^ 2)) - (j : ZMod (p ^ 2))) := by
    intro m hm
    induction m with
    | zero => simp
    | succ m ih =>
      rw [show Finset.Icc 1 (m + 1) = insert (m + 1) (Finset.Icc 1 m) by
        ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega]
      rw [Finset.prod_insert (by simp), ← ih (by omega)]
      have hch : (3 * p - 1).choose (m + 1) * (m + 1) = (3 * p - 1).choose m * (3 * p - 1 - m) :=
        Nat.choose_succ_right_eq (3 * p - 1) m
      have hchZ := congrArg (Nat.cast (R := ZMod (p ^ 2))) hch
      push_cast at hchZ
      have hsub : ((3 * p - 1 - m : ℕ) : ZMod (p ^ 2)) = 3 * (p : ZMod (p ^ 2)) - ((m : ZMod (p ^ 2)) + 1) := by
        have hle : m + 1 ≤ 3 * p := by omega
        rw [show 3 * p - 1 - m = 3 * p - (m + 1) by omega, Nat.cast_sub hle]
        push_cast; ring
      rw [hsub] at hchZ
      rw [Nat.factorial_succ]
      push_cast
      linear_combination (m.factorial : ZMod (p ^ 2)) * hchZ
  -- Step 2: ∏_{j=1}^{k-1} (3p - j) = (-1)^(k-1) * (k-1)! * (1 - 3p H_{k-1})
  have hprod : ∏ j ∈ Finset.Icc 1 (k - 1), (3 * (p : ZMod (p ^ 2)) - (j : ZMod (p ^ 2))) =
      (-1 : ZMod (p ^ 2)) ^ (k - 1) * (((k - 1).factorial : ℕ) : ZMod (p ^ 2)) *
        (1 - 3 * (p : ZMod (p ^ 2)) * H p (k - 1)) := by
    rw [← prod_one_sub_3p_inv]
    have hfac_prod : (((k - 1).factorial : ℕ) : ZMod (p ^ 2)) =
        ∏ j ∈ Finset.Icc 1 (k - 1), (j : ZMod (p ^ 2)) := by
      clear hfac
      induction (k - 1) with
      | zero => simp
      | succ m ih =>
        rw [Nat.factorial_succ, show Finset.Icc 1 (m + 1) = insert (m + 1) (Finset.Icc 1 m) by
          ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega]
        rw [Finset.prod_insert (by simp), ← ih]
        push_cast; ring
    have hneg : (-1 : ZMod (p ^ 2)) ^ (k - 1) = ∏ _j ∈ Finset.Icc 1 (k - 1), (-1 : ZMod (p ^ 2)) := by
      rw [Finset.prod_const, Nat.card_Icc, show k - 1 + 1 - 1 = k - 1 by omega]
    rw [hfac_prod, hneg, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun j hj => ?_
    simp only [Finset.mem_Icc] at hj
    have hjinv := mul_inv_zmod_p2 hp (k := j) (by omega) (by omega)
    linear_combination (-3 * (p : ZMod (p ^ 2))) * hjinv
  -- Step 3: cancel (k-1)! (a unit in ZMod (p^2))
  have hunit_fac : IsUnit (((k - 1).factorial : ℕ) : ZMod (p ^ 2)) := by
    rw [ZMod.isUnit_iff_coprime]
    have hcop : Nat.Coprime (k - 1).factorial p :=
      (hp.coprime_iff_not_dvd.mpr fun hd => by
        have := hp.dvd_factorial.mp hd; omega).symm
    exact hcop.pow_right 2
  have hch_sub : (((3 * p - 1).choose (k - 1) : ℕ) : ZMod (p ^ 2)) =
      (-1 : ZMod (p ^ 2)) ^ (k - 1) * (1 - 3 * (p : ZMod (p ^ 2)) * H p (k - 1)) := by
    apply hunit_fac.mul_left_cancel
    rw [hfac (k - 1) (by omega), hprod]
    ring
  -- Step 4: k * (C(3p, k) / p) = 3 * C(3p-1, k-1)
  have hnat : k * ((3 * p).choose k / p) = 3 * (3 * p - 1).choose (k - 1) := by
    apply Nat.eq_of_mul_eq_mul_left hp.pos
    have h1 : k * (3 * p).choose k = (3 * p) * (3 * p - 1).choose (k - 1) := by
      have := Nat.add_one_mul_choose_eq (3 * p - 1) (k - 1)
      rw [Nat.sub_add_cancel (by omega), Nat.sub_add_cancel hk0] at this
      linarith
    have hdiv := Nat.mul_div_cancel' (p_dvd_choose_3p hp hk0 hkp)
    calc p * (k * ((3 * p).choose k / p)) = k * (p * ((3 * p).choose k / p)) := by ring
      _ = k * (3 * p).choose k := by rw [hdiv]
      _ = (3 * p) * (3 * p - 1).choose (k - 1) := h1
      _ = p * (3 * (3 * p - 1).choose (k - 1)) := by ring
  have hZ := congrArg (Nat.cast (R := ZMod (p ^ 2))) hnat
  push_cast at hZ
  rw [hch_sub] at hZ
  apply (isUnit_zmod_p2 hp hk0 hkp).mul_left_cancel
  calc (k : ZMod (p ^ 2)) * (((3 * p).choose k / p : ℕ) : ZMod (p ^ 2))
      = 3 * ((-1 : ZMod (p ^ 2)) ^ (k - 1) * (1 - 3 * (p : ZMod (p ^ 2)) * H p (k - 1))) := hZ
    _ = ((k : ZMod (p ^ 2)) * (k : ZMod (p ^ 2))⁻¹) *
        (3 * ((-1 : ZMod (p ^ 2)) ^ (k - 1) * (1 - 3 * (p : ZMod (p ^ 2)) * H p (k - 1)))) := by
        rw [mul_inv_zmod_p2 hp hk0 hkp, one_mul]
    _ = (k : ZMod (p ^ 2)) * ((-1 : ZMod (p ^ 2)) ^ (k - 1) * 3 * (k : ZMod (p ^ 2))⁻¹ *
        (1 - 3 * (p : ZMod (p ^ 2)) * H p (k - 1))) := by ring

/-- $(1 - c p)^d = 1 - d c p$ in $\mathbb{Z}/p^2\mathbb{Z}$. -/
private lemma one_sub_p_pow (p d : ℕ) (c : ZMod (p ^ 2)) :
    (1 - (p : ZMod (p ^ 2)) * c) ^ d = 1 - (d : ZMod (p ^ 2)) * (p : ZMod (p ^ 2)) * c := by
  induction d with
  | zero => simp
  | succ d ih =>
    have hstep : (1 - (p : ZMod (p ^ 2)) * c) ^ (d + 1) =
        (1 - (p : ZMod (p ^ 2)) * c) ^ d * (1 - (p : ZMod (p ^ 2)) * c) := pow_succ _ _
    rw [hstep, ih]
    push_cast
    linear_combination ((d : ZMod (p ^ 2)) * c ^ 2) * p_sq_eq_zero p

/-- For any $1 \le d < p - 1$, $\sum_{k=1}^{p-1} k^{-d} = 0$ in $\mathbb{Z}/p\mathbb{Z}$. -/
private lemma sum_inv_pow_mod_p {p d : ℕ} (hp : p.Prime) (hd0 : 0 < d) (hdp : d < p - 1) :
    ∑ k ∈ Finset.Icc 1 (p - 1), ((k : ZMod p)⁻¹) ^ d = 0 := by
  have : Fact p.Prime := ⟨hp⟩
  -- Rewrite as sum over (ZMod p)ˣ
  have hbij : ∑ k ∈ Finset.Icc 1 (p - 1), ((k : ZMod p)⁻¹) ^ d =
      ∑ u : (ZMod p)ˣ, ((u : ZMod p)⁻¹) ^ d := by
    symm
    refine Finset.sum_nbij (fun u => (u : ZMod p).val) ?_ ?_ ?_ ?_
    · intro u _
      simp only [Finset.mem_Icc]
      have hne : (u : ZMod p) ≠ 0 := u.ne_zero
      have hpos : 0 < (u : ZMod p).val := Nat.pos_of_ne_zero fun h => hne ((ZMod.val_eq_zero _).mp h)
      have hlt : (u : ZMod p).val < p := (u : ZMod p).val_lt
      omega
    · intro a _ b _ h
      exact Units.ext (ZMod.val_injective p h)
    · intro k hk
      simp only [Finset.mem_coe, Finset.mem_Icc] at hk
      have hne : (k : ZMod p) ≠ 0 := fun h =>
        Nat.not_dvd_of_pos_of_lt hk.1 (by omega) ((ZMod.natCast_eq_zero_iff k p).mp h)
      exact ⟨Units.mk0 (k : ZMod p) hne, Finset.mem_coe.mpr (Finset.mem_univ _),
        by dsimp only; exact ZMod.val_natCast_of_lt (by omega)⟩
    · intro u _; rw [ZMod.natCast_zmod_val]
  rw [hbij]
  -- Pick generator g of the cyclic group (ZMod p)ˣ of order p - 1
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
  have hord : orderOf g = p - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card, ZMod.card_units]
  have hgd : (g ^ d : (ZMod p)ˣ) ≠ 1 := by
    intro h
    have hdvd := orderOf_dvd_of_pow_eq_one h
    rw [hord] at hdvd
    have := Nat.le_of_dvd hd0 hdvd
    omega
  have hgd_ne : ((g : ZMod p) ^ d) ≠ 1 := fun h => hgd (Units.ext (by simpa using h))
  have hscale : ∑ u : (ZMod p)ˣ, (((g * u : (ZMod p)ˣ) : ZMod p)⁻¹) ^ d =
      ∑ u : (ZMod p)ˣ, ((u : ZMod p)⁻¹) ^ d :=
    Equiv.sum_comp (Equiv.mulLeft g) (fun u => ((u : ZMod p)⁻¹) ^ d)
  have hfac : ∑ u : (ZMod p)ˣ, (((g * u : (ZMod p)ˣ) : ZMod p)⁻¹) ^ d =
      ((g : ZMod p)⁻¹) ^ d * ∑ u : (ZMod p)ˣ, ((u : ZMod p)⁻¹) ^ d := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    simp only [Units.val_mul, mul_inv, mul_pow]
  rw [hfac] at hscale
  have hmul : ((g : ZMod p) ^ d - 1) * ∑ u : (ZMod p)ˣ, ((u : ZMod p)⁻¹) ^ d = 0 := by
    have hginv : (g : ZMod p) ^ d * ((g : ZMod p)⁻¹) ^ d = 1 := by
      rw [← mul_pow, mul_inv_cancel₀ g.ne_zero, one_pow]
    have h1 := congrArg ((g : ZMod p) ^ d * ·) hscale
    rw [← mul_assoc, hginv, one_mul] at h1
    linear_combination -h1
  exact (mul_eq_zero.mp hmul).resolve_left (sub_ne_zero.mpr hgd_ne)

/-- For $d = 2m + 1$ odd and $p \ge 2m + 5$, $\sum_{k=1}^{p-1} k^{-d} = 0$ in $\mathbb{Z}/p^2\mathbb{Z}$. -/
private lemma sum_inv_odd_pow_zmod_p2 {p m : ℕ} (hp : p.Prime) (hp5 : 2 * m + 5 ≤ p) :
    ∑ k ∈ Finset.Icc 1 (p - 1), ((k : ZMod (p ^ 2))⁻¹) ^ (2 * m + 1) = 0 := by
  have : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
  set d := 2 * m + 1
  set S : ZMod (p ^ 2) := ∑ k ∈ Finset.Icc 1 (p - 1), ((k : ZMod (p ^ 2))⁻¹) ^ d
  have h2unit : IsUnit (2 : ZMod (p ^ 2)) :=
    isUnit_zmod_p2 hp (k := 2) (by decide) (by omega)
  suffices h2S : (2 : ZMod (p ^ 2)) * S = 0 from h2unit.mul_left_cancel (by rw [h2S, mul_zero])
  have hpair : S = ∑ k ∈ Finset.Icc 1 (p - 1), (((p - k : ℕ) : ZMod (p ^ 2))⁻¹) ^ d := by
    refine Finset.sum_nbij (fun k => p - k) ?_ ?_ ?_ ?_
    · intro k hk; simp only [Finset.mem_Icc] at hk ⊢; omega
    · intro a ha b hb h; simp only [Finset.mem_coe, Finset.mem_Icc] at ha hb; dsimp only at h; omega
    · intro k hk; simp only [Finset.mem_coe, Finset.mem_Icc] at hk
      exact ⟨p - k, by simp only [Finset.mem_coe, Finset.mem_Icc]; omega, by dsimp only; omega⟩
    · intro k hk; simp only [Finset.mem_Icc] at hk; rw [Nat.sub_sub_self (by omega)]
  have h2eq : (2 : ZMod (p ^ 2)) * S =
      ∑ k ∈ Finset.Icc 1 (p - 1),
        (((k : ZMod (p ^ 2))⁻¹) ^ d + (((p - k : ℕ) : ZMod (p ^ 2))⁻¹) ^ d) := by
    rw [two_mul, Finset.sum_add_distrib]
    congr 1
  rw [h2eq]
  -- For each k, (p - k)⁻¹^d = -(k⁻¹^d) - d * p * k⁻¹^(d+1) in ZMod (p^2)
  have hterm : ∀ k ∈ Finset.Icc 1 (p - 1),
      ((k : ZMod (p ^ 2))⁻¹) ^ d + (((p - k : ℕ) : ZMod (p ^ 2))⁻¹) ^ d =
        -(d : ZMod (p ^ 2)) * (p : ZMod (p ^ 2)) * ((k : ZMod (p ^ 2))⁻¹) ^ (d + 1) := by
    intro k hk
    simp only [Finset.mem_Icc] at hk
    have hkinv := mul_inv_zmod_p2 hp hk.1 (by omega)
    have hpk_inv := mul_inv_zmod_p2 hp (k := p - k) (by omega) (by omega)
    have hcast : ((p - k : ℕ) : ZMod (p ^ 2)) = (p : ZMod (p ^ 2)) - (k : ZMod (p ^ 2)) :=
      Nat.cast_sub (by omega)
    -- First show (p - k)⁻¹ = -k⁻¹ - p * k⁻¹^2
    have hinv1 : ((p - k : ℕ) : ZMod (p ^ 2))⁻¹ =
        -(k : ZMod (p ^ 2))⁻¹ - (p : ZMod (p ^ 2)) * ((k : ZMod (p ^ 2))⁻¹) ^ 2 := by
      apply (isUnit_zmod_p2 hp (k := p - k) (by omega) (by omega)).mul_left_cancel
      rw [hpk_inv, hcast]
      linear_combination -hkinv - ((p : ZMod (p ^ 2)) * (k : ZMod (p ^ 2))⁻¹) * hkinv +
        (((k : ZMod (p ^ 2))⁻¹) ^ 2) * p_sq_eq_zero p
    have hinv_d : (((p - k : ℕ) : ZMod (p ^ 2))⁻¹) ^ d =
        -((k : ZMod (p ^ 2))⁻¹) ^ d - (d : ZMod (p ^ 2)) * (p : ZMod (p ^ 2)) * ((k : ZMod (p ^ 2))⁻¹) ^ (d + 1) := by
      rw [hinv1]
      have hfac : -(k : ZMod (p ^ 2))⁻¹ - (p : ZMod (p ^ 2)) * ((k : ZMod (p ^ 2))⁻¹) ^ 2 =
          (-(k : ZMod (p ^ 2))⁻¹) * (1 - (p : ZMod (p ^ 2)) * (-(k : ZMod (p ^ 2))⁻¹)) := by ring
      rw [hfac, mul_pow, one_sub_p_pow]
      have hneg1 : (-1 : ZMod (p ^ 2)) ^ (2 * m + 1) = -1 := Odd.neg_one_pow ⟨m, rfl⟩
      have hneg_odd : (-(k : ZMod (p ^ 2))⁻¹) ^ d = -((k : ZMod (p ^ 2))⁻¹) ^ d := by
        show (-(k : ZMod (p ^ 2))⁻¹) ^ (2 * m + 1) = -((k : ZMod (p ^ 2))⁻¹) ^ (2 * m + 1)
        rw [neg_pow, hneg1]; ring
      rw [hneg_odd, pow_succ]
      ring
    rw [hinv_d]; ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  -- Now p * ∑ k⁻¹^(d+1) = 0 in ZMod (p^2) since ∑ k⁻¹^(d+1) = 0 in ZMod p!
  set S2 : ZMod (p ^ 2) := ∑ k ∈ Finset.Icc 1 (p - 1), ((k : ZMod (p ^ 2))⁻¹) ^ (d + 1)
  have hS2_p : p ∣ S2.val := by
    have hcast : ZMod.castHom (dvd_pow_self p (by norm_num : 2 ≠ 0)) (ZMod p) S2 = 0 := by
      simp only [S2, map_sum, map_pow]
      have hinv : ∀ k ∈ Finset.Icc 1 (p - 1),
          (ZMod.castHom (dvd_pow_self p (by norm_num : 2 ≠ 0)) (ZMod p) ((k : ZMod (p ^ 2))⁻¹)) ^ (d + 1) =
          ((k : ZMod p)⁻¹) ^ (d + 1) := by
        intro k hk
        simp only [Finset.mem_Icc] at hk
        have hm := congrArg (ZMod.castHom (dvd_pow_self p (by norm_num : 2 ≠ 0)) (ZMod p))
          (mul_inv_zmod_p2 hp hk.1 (by omega))
        simp only [map_mul, map_one, map_natCast] at hm
        have : Fact p.Prime := ⟨hp⟩
        have hkne : (k : ZMod p) ≠ 0 := fun h =>
          Nat.not_dvd_of_pos_of_lt hk.1 (by omega) ((ZMod.natCast_eq_zero_iff k p).mp h)
        have hi : ZMod.castHom (dvd_pow_self p (by norm_num : 2 ≠ 0)) (ZMod p) ((k : ZMod (p ^ 2))⁻¹) =
            (k : ZMod p)⁻¹ := mul_left_cancel₀ hkne (by rw [hm, mul_inv_cancel₀ hkne])
        rw [hi]
      rw [Finset.sum_congr rfl hinv]
      exact sum_inv_pow_mod_p hp (by omega) (by omega)
    rw [ZMod.castHom_apply, ZMod.cast_eq_val] at hcast
    exact (ZMod.natCast_eq_zero_iff _ _).mp hcast
  have hpS2 : (p : ZMod (p ^ 2)) * S2 = 0 := by
    rw [← ZMod.natCast_zmod_val S2, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_zero_iff _ _).mpr
    exact dvd_trans (dvd_of_eq (sq p)) (mul_dvd_mul_left p hS2_p)
  linear_combination -(d : ZMod (p ^ 2)) * hpS2

/-- For $d = 2m + 1$ odd and $p \ge 2m + 5$, $\sum_{k=1}^{p-1} k^{-d} H_{k-1} = 0$ in $\mathbb{Z}/p\mathbb{Z}$. -/
private lemma sum_inv_odd_pow_mul_H_mod_p {p m : ℕ} (hp : p.Prime) (hp5 : 2 * m + 5 ≤ p) :
    ∑ k ∈ Finset.Icc 1 (p - 1),
      ((k : ZMod p)⁻¹) ^ (2 * m + 1) * (∑ j ∈ Finset.Icc 1 (k - 1), (j : ZMod p)⁻¹) = 0 := by
  have : Fact p.Prime := ⟨hp⟩
  set d := 2 * m + 1
  let Hp : ℕ → ZMod p := fun r => ∑ j ∈ Finset.Icc 1 r, (j : ZMod p)⁻¹
  -- H_{p-1} = 0 in ZMod p
  have hH_full : Hp (p - 1) = 0 := by
    have := sum_inv_pow_mod_p hp (d := 1) (by norm_num) (by omega)
    simpa [Hp] using this
  -- H_{p - k - 1} = H_{k - 1} + k⁻¹ in ZMod p for 1 ≤ k ≤ p - 1
  have hH_symm : ∀ k ∈ Finset.Icc 1 (p - 1), Hp (p - k - 1) = Hp (k - 1) + (k : ZMod p)⁻¹ := by
    intro k hk
    simp only [Finset.mem_Icc] at hk
    have hsplit : Finset.Icc 1 (p - 1) = Finset.Icc 1 (p - k - 1) ∪ Finset.Icc (p - k) (p - 1) := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_union]; omega
    have hdisj : Disjoint (Finset.Icc 1 (p - k - 1)) (Finset.Icc (p - k) (p - 1)) := by
      rw [Finset.disjoint_left]; intro x hx1 hx2
      simp only [Finset.mem_Icc] at hx1 hx2; omega
    have h0 : Hp (p - k - 1) + ∑ j ∈ Finset.Icc (p - k) (p - 1), (j : ZMod p)⁻¹ = 0 := by
      rw [← hH_full]
      simp only [Hp]
      rw [hsplit, Finset.sum_union hdisj]
    have htail : ∑ j ∈ Finset.Icc (p - k) (p - 1), (j : ZMod p)⁻¹ = -Hp k := by
      simp only [Hp, ← Finset.sum_neg_distrib]
      refine Finset.sum_nbij (fun j => p - j) ?_ ?_ ?_ ?_
      · intro j hj; simp only [Finset.mem_Icc] at hj ⊢; omega
      · intro a ha b hb h; simp only [Finset.mem_coe, Finset.mem_Icc] at ha hb; dsimp only at h; omega
      · intro i hi; simp only [Finset.mem_coe, Finset.mem_Icc] at hi
        exact ⟨p - i, by simp only [Finset.mem_coe, Finset.mem_Icc]; omega, by dsimp only; omega⟩
      · intro j hj
        simp only [Finset.mem_Icc] at hj
        have hcast : ((p - j : ℕ) : ZMod p) = -(j : ZMod p) := by
          rw [Nat.cast_sub (by omega), ZMod.natCast_self, zero_sub]
        rw [hcast, inv_neg, neg_neg]
    have hHk : Hp k = Hp (k - 1) + (k : ZMod p)⁻¹ := by
      simp only [Hp]
      rw [show Finset.Icc 1 k = insert k (Finset.Icc 1 (k - 1)) by
        ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega]
      rw [Finset.sum_insert (by simp only [Finset.mem_Icc]; omega), add_comm]
    rw [htail, hHk] at h0
    linear_combination h0
  set S : ZMod p := ∑ k ∈ Finset.Icc 1 (p - 1), ((k : ZMod p)⁻¹) ^ d * Hp (k - 1)
  have h2ne : (2 : ZMod p) ≠ 0 := fun h => by
    have hle : p ≤ 2 := Nat.le_of_dvd (by decide) ((ZMod.natCast_eq_zero_iff 2 p).mp h); omega
  suffices h2S : (2 : ZMod p) * S = 0 from (mul_eq_zero.mp h2S).resolve_left h2ne
  have hpair : S = ∑ k ∈ Finset.Icc 1 (p - 1),
      (-(((k : ZMod p)⁻¹) ^ d) * (Hp (k - 1) + (k : ZMod p)⁻¹)) := by
    refine Finset.sum_nbij (fun k => p - k) ?_ ?_ ?_ ?_
    · intro k hk; simp only [Finset.mem_Icc] at hk ⊢; omega
    · intro a ha b hb h; simp only [Finset.mem_coe, Finset.mem_Icc] at ha hb; dsimp only at h; omega
    · intro k hk; simp only [Finset.mem_coe, Finset.mem_Icc] at hk
      exact ⟨p - k, by simp only [Finset.mem_coe, Finset.mem_Icc]; omega, by dsimp only; omega⟩
    · intro k hk
      simp only [Finset.mem_Icc] at hk
      have hcast : ((p - k : ℕ) : ZMod p) = -(k : ZMod p) := by
        rw [Nat.cast_sub (by omega), ZMod.natCast_self, zero_sub]
      rw [hcast, inv_neg, neg_pow, show (-1 : ZMod p) ^ d = -1 by
        show (-1 : ZMod p) ^ (2 * m + 1) = -1; rw [pow_succ, pow_mul]; norm_num]
      rw [hH_symm k (Finset.mem_Icc.mpr hk)]
      ring
  have h2eq : (2 : ZMod p) * S = - ∑ k ∈ Finset.Icc 1 (p - 1), ((k : ZMod p)⁻¹) ^ (d + 1) := by
    rw [two_mul]
    conv_lhs => rhs; rw [hpair]
    rw [← Finset.sum_add_distrib, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [pow_succ]; ring
  rw [h2eq, sum_inv_pow_mod_p hp (by omega) (by omega), neg_zero]

/--
**OEIS A375180, Generalized Conjecture A (Peter Bala, August 2024):**
For all $m \ge 1$ and all primes $p \ge 2m + 5$,
$$b_m(p) \equiv 1 \pmod{p^{2m+3}}.$$
-/
theorem conjecture_general (m p : ℕ) (hm : 1 ≤ m) (hp : p.Prime) (hp_ge : 2 * m + 5 ≤ p) :
    ((p : ℤ) ^ (2 * m + 3)) ∣ (b m p - 1) := by
  have : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
  have hp_odd : Odd p := hp.odd_of_ne_two (by omega)
  -- Split off k = 0 term (= 1) from b m p
  have hb_split : b m p - 1 =
      ∑ k ∈ Finset.Icc 1 (p - 1), (-1 : ℤ) ^ k * ((3 * p).choose k : ℤ) ^ (2 * m + 1) := by
    unfold b
    have h0 : 0 ∈ Finset.range p := Finset.mem_range.mpr hp.pos
    rw [← Finset.add_sum_erase _ _ h0]
    have hterm0 : (-1 : ℤ) ^ (p + 0 + 1) * ((3 * p).choose 0 : ℤ) ^ (2 * m + 1) = 1 := by
      rcases hp_odd with ⟨t, rfl⟩
      rw [Nat.choose_zero_right, Nat.cast_one, one_pow, mul_one]
      have : 2 * t + 1 + 0 + 1 = 2 * (t + 1) := by omega
      rw [this, pow_mul]; norm_num
    rw [hterm0, add_sub_cancel_left]
    refine Finset.sum_congr ?_ fun k _ => ?_
    · ext k; simp only [Finset.mem_erase, Finset.mem_range, Finset.mem_Icc]; omega
    · rcases hp_odd with ⟨t, rfl⟩
      have : 2 * t + 1 + k + 1 = 2 * (t + 1) + k := by omega
      rw [this, pow_add, pow_mul]
      norm_num
  rw [hb_split]
  -- Factor out p^(2m+1) from each term
  have hfac_p : ∀ k ∈ Finset.Icc 1 (p - 1),
      (-1 : ℤ) ^ k * ((3 * p).choose k : ℤ) ^ (2 * m + 1) =
        (p : ℤ) ^ (2 * m + 1) * ((-1 : ℤ) ^ k * (((3 * p).choose k / p : ℕ) : ℤ) ^ (2 * m + 1)) := by
    intro k hk
    simp only [Finset.mem_Icc] at hk
    have hdiv := Nat.mul_div_cancel' (p_dvd_choose_3p hp hk.1 (by omega))
    have hZ : ((3 * p).choose k : ℤ) = (p : ℤ) * (((3 * p).choose k / p : ℕ) : ℤ) := by
      exact_mod_cast hdiv.symm
    rw [hZ, mul_pow]; ring
  rw [Finset.sum_congr rfl hfac_p, ← Finset.mul_sum,
    show 2 * m + 3 = (2 * m + 1) + 2 by omega, pow_add]
  apply mul_dvd_mul_left
  -- Show ∑_{k=1}^{p-1} (-1)^k * C_k^(2m+1) = 0 in ZMod (p^2)
  rw [show ((p : ℤ) ^ 2) = ((p ^ 2 : ℕ) : ℤ) by push_cast; rfl,
    ← ZMod.intCast_zmod_eq_zero_iff_dvd]
  rw [Int.cast_sum]
  simp only [Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one, Int.cast_natCast]
  have hterm : ∀ k ∈ Finset.Icc 1 (p - 1),
      (-1 : ZMod (p ^ 2)) ^ k * ((((3 * p).choose k / p : ℕ) : ZMod (p ^ 2)) ^ (2 * m + 1)) =
        -(3 : ZMod (p ^ 2)) ^ (2 * m + 1) * ((k : ZMod (p ^ 2))⁻¹) ^ (2 * m + 1) +
        (3 : ZMod (p ^ 2)) ^ (2 * m + 2) * ((2 * m + 1 : ℕ) : ZMod (p ^ 2)) * (p : ZMod (p ^ 2)) *
          (((k : ZMod (p ^ 2))⁻¹) ^ (2 * m + 1) * H p (k - 1)) := by
    intro k hk
    simp only [Finset.mem_Icc] at hk
    rw [choose_3p_div_p_zmod hp hk.1 (by omega)]
    have h1 : ((-1 : ZMod (p ^ 2)) ^ (k - 1) * 3 * (k : ZMod (p ^ 2))⁻¹ *
          (1 - 3 * (p : ZMod (p ^ 2)) * H p (k - 1))) ^ (2 * m + 1) =
        ((-1 : ZMod (p ^ 2)) ^ (k - 1)) ^ (2 * m + 1) * (3 : ZMod (p ^ 2)) ^ (2 * m + 1) *
          ((k : ZMod (p ^ 2))⁻¹) ^ (2 * m + 1) *
          (1 - ((2 * m + 1 : ℕ) : ZMod (p ^ 2)) * (p : ZMod (p ^ 2)) * (3 * H p (k - 1))) := by
      have hsub : 1 - 3 * (p : ZMod (p ^ 2)) * H p (k - 1) =
          1 - (p : ZMod (p ^ 2)) * (3 * H p (k - 1)) := by ring
      rw [mul_pow, mul_pow, mul_pow, hsub, one_sub_p_pow]
    rw [h1]
    have hsign : (-1 : ZMod (p ^ 2)) ^ k * ((-1 : ZMod (p ^ 2)) ^ (k - 1)) ^ (2 * m + 1) = -1 := by
      rw [← pow_mul, ← pow_add]
      have hodd_exp : Odd (k + (k - 1) * (2 * m + 1)) := by
        refine ⟨(k - 1) * (m + 1), ?_⟩
        have hk1 : k = (k - 1) + 1 := by omega
        linarith
      exact hodd_exp.neg_one_pow
    have h3pow : (3 : ZMod (p ^ 2)) ^ (2 * m + 2) = (3 : ZMod (p ^ 2)) ^ (2 * m + 1) * 3 := pow_succ _ _
    rw [h3pow]
    linear_combination
      ((3 : ZMod (p ^ 2)) ^ (2 * m + 1) * ((k : ZMod (p ^ 2))⁻¹) ^ (2 * m + 1) *
        (1 - ((2 * m + 1 : ℕ) : ZMod (p ^ 2)) * (p : ZMod (p ^ 2)) * (3 * H p (k - 1)))) * hsign
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  rw [sum_inv_odd_pow_zmod_p2 hp hp_ge, mul_zero, zero_add]
  -- Show p * ∑ k⁻¹^(2m+1) * H_{k-1} = 0 in ZMod (p^2)
  set SH : ZMod (p ^ 2) := ∑ k ∈ Finset.Icc 1 (p - 1), ((k : ZMod (p ^ 2))⁻¹) ^ (2 * m + 1) * H p (k - 1)
  have hSH_p : p ∣ SH.val := by
    have hcast : ZMod.castHom (dvd_pow_self p (by norm_num : 2 ≠ 0)) (ZMod p) SH = 0 := by
      simp only [SH, H, map_sum, map_mul, map_pow]
      have hinv_fn : ∀ j ∈ Finset.Icc 1 (p - 1),
          ZMod.castHom (dvd_pow_self p (by norm_num : 2 ≠ 0)) (ZMod p) ((j : ZMod (p ^ 2))⁻¹) =
            (j : ZMod p)⁻¹ := by
        intro j hj
        simp only [Finset.mem_Icc] at hj
        have h1 := congrArg (ZMod.castHom (dvd_pow_self p (by norm_num : 2 ≠ 0)) (ZMod p))
          (mul_inv_zmod_p2 hp hj.1 (by omega))
        simp only [map_mul, map_one, map_natCast] at h1
        have : Fact p.Prime := ⟨hp⟩
        have hjne : (j : ZMod p) ≠ 0 := fun h =>
          Nat.not_dvd_of_pos_of_lt hj.1 (by omega) ((ZMod.natCast_eq_zero_iff j p).mp h)
        exact mul_left_cancel₀ hjne (by rw [h1, mul_inv_cancel₀ hjne])
      have hterm_c : ∀ k ∈ Finset.Icc 1 (p - 1),
          (ZMod.castHom (dvd_pow_self p (by norm_num : 2 ≠ 0)) (ZMod p) ((k : ZMod (p ^ 2))⁻¹)) ^ (2 * m + 1) *
            ∑ j ∈ Finset.Icc 1 (k - 1),
              ZMod.castHom (dvd_pow_self p (by norm_num : 2 ≠ 0)) (ZMod p) ((j : ZMod (p ^ 2))⁻¹) =
          ((k : ZMod p)⁻¹) ^ (2 * m + 1) * ∑ j ∈ Finset.Icc 1 (k - 1), (j : ZMod p)⁻¹ := by
        intro k hk
        rw [hinv_fn k hk]
        congr 1
        refine Finset.sum_congr rfl fun j hj => ?_
        simp only [Finset.mem_Icc] at hk hj
        exact hinv_fn j (Finset.mem_Icc.mpr ⟨hj.1, by omega⟩)
      rw [Finset.sum_congr rfl hterm_c]
      exact sum_inv_odd_pow_mul_H_mod_p hp hp_ge
    rw [ZMod.castHom_apply, ZMod.cast_eq_val] at hcast
    exact (ZMod.natCast_eq_zero_iff _ _).mp hcast
  have hpSH : (p : ZMod (p ^ 2)) * SH = 0 := by
    rw [← ZMod.natCast_zmod_val SH, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_zero_iff _ _).mpr
    exact dvd_trans (dvd_of_eq (sq p)) (mul_dvd_mul_left p hSH_p)
  linear_combination ((3 : ZMod (p ^ 2)) ^ (2 * m + 2) * ((2 * m + 1 : ℕ) : ZMod (p ^ 2))) * hpSH

/--
**OEIS A375180, Conjecture 1 (Peter Bala, August 2024):**
For all primes $p \ge 7$, $a(p) \equiv 1 \pmod{p^5}$.
-/
theorem conjecture_1 (p : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p) :
    ((p : ℤ) ^ 5) ∣ (a p - 1) :=
  conjecture_general 1 p le_rfl hp hp7


end SolvedConjecture05

/-!
# OEIS A375180, prime-power supercongruences (Peter Bala, 2024)

`b_m(n) = Sum_{k<n} (-1)^(n+k+1) C(3n,k)^(2m+1)` (and `a = b_1`).  For every `m >= 1`, every prime
`p >= 2m+5` and every `r >= 2`: `p^(3r+2m+1)` divides `b_m(p^r) - b_m(p^(r-1))`.
The case `m = 1` is `main_general` (which also covers `p = 5`); the exponents `2k+3 >= 5` are
`main_d`: there only the layer `v_p(k) = r-1` needs a cancellation, obtained from
`Sum_{t<p} t^(-j) = 0 mod p` for `0 < j < p-1` (primitive root), its odd refinement modulo `p^2`
and `H(p-t) = H(t) + 1/t mod p` for the harmonic numbers.

Method (everything in the rationals, with `D p e x` meaning `x` lies in `p^e Z_(p)`):
* `C(3N, pj) = C(3Q, j) * R(pj)` with `R(L) = Prod_{0<i<L, p not| i} (1 - 3N/i)` (`N = p^r`, `Q = N/p`);
* second order expansion of `R(t p^s)` via power sums over the units below `p^s`
  (reflection `u -> p^s - u`, scaling `u -> 2u`, translation by multiples of `p^s`);
* the terms with `p not| k` are handled by the factorisation
  `Prod_{i < A Q + u} = Prod_{i <= A Q} * Prod_{i < u}` modulo `p^3`;
* the terms with `p | k` are grouped by `v_p(k)`; the two top layers cancel by
  Wolstenholme type sums, the other layers vanish term by term;
* the single case `(p, r) = (5, 2)`, where `p - 1` divides `4`, is a finite computation.
-/

namespace A375180H2

open Finset

variable {p : ℕ} [hp : Fact p.Prime]

/-- `D p e x` : the rational `x` lies in `p^e * ℤ_(p)`. -/
private def D (p e : ℕ) (x : ℚ) : Prop :=
  ∃ a : ℤ, ∃ b : ℕ, ¬ p ∣ b ∧ x * (b : ℚ) = (p : ℚ) ^ e * (a : ℚ)

private lemma D.zero (e : ℕ) : D p e 0 := ⟨0, 1, hp.out.not_dvd_one, by simp⟩

omit hp in
private lemma D.neg {e : ℕ} {x : ℚ} (hx : D p e x) : D p e (-x) := by
  obtain ⟨a, b, hb, h⟩ := hx
  exact ⟨-a, b, hb, by push_cast; linear_combination -h⟩

private lemma D.add {e : ℕ} {x y : ℚ} (hx : D p e x) (hy : D p e y) : D p e (x + y) := by
  obtain ⟨a, b, hb, h⟩ := hx
  obtain ⟨a', b', hb', h'⟩ := hy
  refine ⟨a * b' + a' * b, b * b', ?_, ?_⟩
  · intro hd
    rcases (Nat.Prime.dvd_mul hp.out).mp hd with h1 | h1
    · exact hb h1
    · exact hb' h1
  · push_cast
    linear_combination (b' : ℚ) * h + (b : ℚ) * h'

private lemma D.sub {e : ℕ} {x y : ℚ} (hx : D p e x) (hy : D p e y) : D p e (x - y) := by
  rw [sub_eq_add_neg]; exact hx.add hy.neg

private lemma D.mul {e f : ℕ} {x y : ℚ} (hx : D p e x) (hy : D p f y) : D p (e + f) (x * y) := by
  obtain ⟨a, b, hb, h⟩ := hx
  obtain ⟨a', b', hb', h'⟩ := hy
  refine ⟨a * a', b * b', ?_, ?_⟩
  · intro hd
    rcases (Nat.Prime.dvd_mul hp.out).mp hd with h1 | h1
    · exact hb h1
    · exact hb' h1
  · push_cast
    rw [pow_add]
    linear_combination (y * (b' : ℚ)) * h + ((p : ℚ) ^ e * (a : ℚ)) * h'

omit hp in
private lemma D.le {e f : ℕ} {x : ℚ} (hx : D p e x) (hfe : f ≤ e) : D p f x := by
  obtain ⟨a, b, hb, h⟩ := hx
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hfe
  exact ⟨(p : ℤ) ^ c * a, b, hb, by push_cast; rw [h, pow_add]; ring⟩

private lemma D.int (z : ℤ) : D p 0 (z : ℚ) := ⟨z, 1, hp.out.not_dvd_one, by simp⟩

private lemma D.nat (n : ℕ) : D p 0 (n : ℚ) := ⟨(n : ℤ), 1, hp.out.not_dvd_one, by simp⟩

private lemma D.one : D p 0 (1 : ℚ) := ⟨1, 1, hp.out.not_dvd_one, by simp⟩

private lemma D.ppow (e : ℕ) : D p e ((p : ℚ) ^ e) := ⟨1, 1, hp.out.not_dvd_one, by simp⟩

private lemma D.mul0 {e : ℕ} {x y : ℚ} (hx : D p e x) (hy : D p 0 y) : D p e (x * y) :=
  (hx.mul hy).le (by omega)

private lemma D.mul0' {e : ℕ} {x y : ℚ} (hy : D p 0 y) (hx : D p e x) : D p e (y * x) :=
  (hy.mul hx).le (by omega)

omit hp in
private lemma D.inv {u : ℕ} (hu : ¬ p ∣ u) : D p 0 ((u : ℚ)⁻¹) := by
  have hu0 : (u : ℚ) ≠ 0 := by
    intro h
    apply hu
    have h0 : u = 0 := by exact_mod_cast h
    rw [h0]; exact dvd_zero p
  exact ⟨1, u, hu, by rw [inv_mul_cancel₀ hu0]; simp⟩

private lemma D.sum {ι : Type*} {e : ℕ} (s : Finset ι) (f : ι → ℚ) (h : ∀ i ∈ s, D p e (f i)) :
    D p e (∑ i ∈ s, f i) :=
  Finset.sum_induction f (D p e) (fun _ _ ha hb => ha.add hb) (D.zero e) h

private lemma D.prod {ι : Type*} (s : Finset ι) (f : ι → ℚ) (h : ∀ i ∈ s, D p 0 (f i)) :
    D p 0 (∏ i ∈ s, f i) :=
  Finset.prod_induction f (D p 0) (fun _ _ ha hb => (ha.mul hb).le (by omega)) D.one h

private lemma D.pow {e : ℕ} {x : ℚ} (hx : D p e x) (n : ℕ) : D p (e * n) (x ^ n) := by
  induction n with
  | zero => simpa using (D.one (p := p))
  | succ n ih => rw [pow_succ, Nat.mul_succ]; exact ih.mul hx

private lemma D.cancel {e c : ℕ} {x : ℚ} (h : D p (e + c) ((p : ℚ) ^ c * x)) : D p e x := by
  obtain ⟨a, b, hb, h⟩ := h
  refine ⟨a, b, hb, ?_⟩
  have hpc : ((p : ℚ) ^ c) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr hp.out.ne_zero)
  apply mul_left_cancel₀ hpc
  rw [pow_add] at h
  linear_combination h

private lemma D.ucancel {e u : ℕ} {x : ℚ} (hu : ¬ p ∣ u) (h : D p e ((u : ℚ) * x)) : D p e x := by
  obtain ⟨a, b, hb, h⟩ := h
  refine ⟨a, u * b, ?_, by push_cast; linear_combination h⟩
  intro hd
  rcases (Nat.Prime.dvd_mul hp.out).mp hd with h1 | h1
  · exact hu h1
  · exact hb h1

private lemma D.dvd {e : ℕ} {z : ℤ} (h : D p e (z : ℚ)) : (p : ℤ) ^ e ∣ z := by
  obtain ⟨a, b, hb, h⟩ := h
  have h2 : z * (b : ℤ) = (p : ℤ) ^ e * a := by exact_mod_cast h
  have hc : IsCoprime ((p : ℤ) ^ e) (b : ℤ) := by
    have h3 : Nat.Coprime (p ^ e) b :=
      Nat.Coprime.pow_left e ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hb)
    have h4 := Nat.isCoprime_iff_coprime.mpr h3
    simpa using h4
  exact hc.dvd_of_dvd_mul_right ⟨a, h2⟩

/-! ### index sets -/

/-- the integers `0 < i < L` prime to `p` -/
private def U (p L : ℕ) : Finset ℕ := (Finset.range L).filter (fun i => ¬ p ∣ i)

private lemma mem_U {p L i : ℕ} : i ∈ U p L ↔ i < L ∧ ¬ p ∣ i := by
  simp [U]

omit hp in
private lemma sum_U_blocks {q : ℕ} (hpq : p ∣ q) (f : ℕ → ℚ) (t : ℕ) :
    ∑ i ∈ U p (t * q), f i = ∑ h ∈ Finset.range t, ∑ u ∈ U p q, f (h * q + u) := by
  induction t with
  | zero => simp [U]
  | succ t ih =>
    rw [Finset.sum_range_succ, ← ih]
    unfold U
    rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter, add_one_mul,
      Finset.sum_range_add]
    congr 1
    refine Finset.sum_congr rfl fun x _ => ?_
    have h1 : p ∣ t * q + x ↔ p ∣ x := Nat.dvd_add_right (dvd_mul_of_dvd_right hpq t)
    simp only [h1]

private lemma sum_range_mul_split {M : Type*} [AddCommMonoid M] (m n : ℕ) (hm : 0 < m)
    (f : ℕ → M) :
    ∑ k ∈ Finset.range (m * n), f k =
      ∑ k ∈ (Finset.range (m * n)).filter (fun k => ¬ m ∣ k), f k +
        ∑ c ∈ Finset.range n, f (m * c) := by
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.range (m * n)) (fun k => m ∣ k), add_comm]
  congr 1
  have h1 : (Finset.range (m * n)).filter (fun k => m ∣ k) =
      (Finset.range n).image (fun c => m * c) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨hk, c, rfl⟩
      exact ⟨c, lt_of_mul_lt_mul_left hk (Nat.zero_le m), rfl⟩
    · rintro ⟨c, hc, rfl⟩
      exact ⟨by nlinarith, dvd_mul_right m c⟩
  rw [h1, Finset.sum_image]
  intro x _ y _ h
  exact Nat.eq_of_mul_eq_mul_left hm h

private lemma prod_range_mul_split {M : Type*} [CommMonoid M] (m n : ℕ) (hm : 0 < m)
    (f : ℕ → M) :
    ∏ k ∈ Finset.range (m * n), f k =
      (∏ k ∈ (Finset.range (m * n)).filter (fun k => ¬ m ∣ k), f k) *
        ∏ c ∈ Finset.range n, f (m * c) := by
  rw [← Finset.prod_filter_mul_prod_filter_not (Finset.range (m * n)) (fun k => m ∣ k), mul_comm]
  congr 1
  have h1 : (Finset.range (m * n)).filter (fun k => m ∣ k) =
      (Finset.range n).image (fun c => m * c) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨hk, c, rfl⟩
      exact ⟨c, lt_of_mul_lt_mul_left hk (Nat.zero_le m), rfl⟩
    · rintro ⟨c, hc, rfl⟩
      exact ⟨by nlinarith, dvd_mul_right m c⟩
  rw [h1, Finset.prod_image]
  intro x _ y _ h
  exact Nat.eq_of_mul_eq_mul_left hm h

/-! ### binomials as products -/

/-- `Gp n m = ∏_{0 < i < m} (1 - n / i)` (the factor `i = 0` is `1`). -/
private def Gp (n : ℚ) (m : ℕ) : ℚ := ∏ i ∈ Finset.range m, (1 - n / (i : ℚ))

omit hp in
private lemma choose_mul_eq (n k : ℕ) :
    (n.choose (k + 1) : ℚ) * ((k : ℚ) + 1) = (n : ℚ) * (-1) ^ k * Gp n (k + 1) := by
  induction k with
  | zero => simp [Gp]
  | succ k ih =>
    have h1 : (n.choose (k + 1 + 1) : ℚ) * ((k : ℚ) + 1 + 1) =
        (n.choose (k + 1) : ℚ) * ((n : ℚ) - ((k : ℚ) + 1)) := by
      rcases le_or_gt (k + 1) n with h | h
      · have h2 := congrArg (Nat.cast (R := ℚ)) (Nat.choose_succ_right_eq n (k + 1))
        push_cast [Nat.cast_sub h] at h2
        linarith
      · rw [Nat.choose_eq_zero_of_lt (by omega : n < k + 1 + 1), Nat.choose_eq_zero_of_lt h]
        simp
    have hG : Gp n (k + 1 + 1) = Gp n (k + 1) * (1 - (n : ℚ) / ((k : ℚ) + 1)) := by
      unfold Gp
      rw [Finset.prod_range_succ]
      push_cast
      ring
    have hk : ((k : ℚ) + 1) ≠ 0 := by positivity
    have h3 : (n : ℚ) * (-1) ^ (k + 1) * (Gp n (k + 1) * (1 - (n : ℚ) / ((k : ℚ) + 1))) =
        ((n : ℚ) * (-1) ^ k * Gp n (k + 1)) * (((n : ℚ) - ((k : ℚ) + 1)) / ((k : ℚ) + 1)) := by
      field_simp
      ring
    have h4 : ((n.choose (k + 1) : ℚ) * ((k : ℚ) + 1)) * (((n : ℚ) - ((k : ℚ) + 1)) / ((k : ℚ) + 1)) =
        (n.choose (k + 1) : ℚ) * ((n : ℚ) - ((k : ℚ) + 1)) := by
      field_simp
    push_cast
    rw [hG, h3, ← ih, h4, ← h1]

omit hp in
private lemma choose_mul_eq' (n k : ℕ) (hk : 1 ≤ k) :
    (n.choose k : ℚ) * (k : ℚ) = -((n : ℚ) * (-1) ^ k * Gp n k) := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have h := choose_mul_eq n k'
  push_cast
  rw [h, pow_succ]
  ring

/-- `R p x L = ∏_{0 < i < L, p ∤ i} (1 - x / i)` -/
private def R (p : ℕ) (x : ℚ) (L : ℕ) : ℚ := ∏ i ∈ U p L, (1 - x / (i : ℚ))

omit hp in
private lemma Gp_split (hp0 : 0 < p) (x : ℚ) (j : ℕ) :
    Gp x (p * j) = R p x (p * j) * Gp (x / p) j := by
  unfold Gp R U
  rw [prod_range_mul_split p j hp0]
  congr 1
  refine Finset.prod_congr rfl fun c _ => ?_
  push_cast
  rw [div_div]

private lemma choose_ratio (hp2 : p ≠ 2) (n j : ℕ) :
    ((p * n).choose (p * j) : ℚ) = (n.choose j : ℚ) * R p ((p * n : ℕ) : ℚ) (p * j) := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp [R, U]
  have hp0 : 0 < p := hp.out.pos
  have hodd : Odd p := hp.out.odd_of_ne_two hp2
  have h1 := choose_mul_eq' (p * n) (p * j) (by nlinarith)
  have h2 := choose_mul_eq' n j hj
  have h3 := Gp_split hp0 ((p * n : ℕ) : ℚ) j
  have h4 : ((p * n : ℕ) : ℚ) / (p : ℚ) = (n : ℚ) := by
    push_cast
    field_simp
  have h5 : (-1 : ℚ) ^ (p * j) = (-1) ^ j := by
    rw [pow_mul, hodd.neg_one_pow]
  rw [h3, h4, h5] at h1
  have hpj : ((p * j : ℕ) : ℚ) ≠ 0 := by
    have : 0 < p * j := Nat.mul_pos hp0 hj
    positivity
  have hj0 : (j : ℚ) ≠ 0 := by positivity
  have hpq : (p : ℚ) ≠ 0 := by positivity
  apply mul_right_cancel₀ hpj
  rw [h1]
  push_cast
  have h6 : (n : ℚ) * (-1) ^ j * Gp n j = -((n.choose j : ℚ) * (j : ℚ)) := by rw [h2]; ring
  linear_combination (-(p : ℚ) * R p ((p : ℚ) * (n : ℚ)) (p * j)) * h6

/-! ### expansions of `1/(u+a)^j` -/

private lemma D.pow0 {x : ℚ} (hx : D p 0 x) (n : ℕ) : D p 0 (x ^ n) :=
  (hx.pow n).le (Nat.zero_le _)

private lemma D.two : D p 0 (2 : ℚ) := by simpa using D.nat (p := p) 2

private lemma D.three : D p 0 (3 : ℚ) := by simpa using D.nat (p := p) 3

private lemma exp1_D {s : ℕ} {u v a : ℚ} (hu0 : u ≠ 0) (hv0 : v ≠ 0) (h : v = u + a)
    (hu : D p 0 u⁻¹) (hv : D p 0 v⁻¹) (ha : D p s a) :
    D p (4 * s) (v⁻¹ - (u⁻¹ - a * u⁻¹ ^ 2 + a ^ 2 * u⁻¹ ^ 3 - a ^ 3 * u⁻¹ ^ 4)) := by
  have h1 : v⁻¹ - (u⁻¹ - a * u⁻¹ ^ 2 + a ^ 2 * u⁻¹ ^ 3 - a ^ 3 * u⁻¹ ^ 4) =
      a ^ 4 * u⁻¹ ^ 4 * v⁻¹ := by
    subst h
    field_simp
    ring
  rw [h1]
  exact (((ha.pow 4).mul0 (hu.pow0 4)).mul0 hv).le (by omega)

private lemma exp2_D {s : ℕ} {u v a : ℚ} (hu0 : u ≠ 0) (hv0 : v ≠ 0) (h : v = u + a)
    (hu : D p 0 u⁻¹) (hu' : D p 0 u) (hv : D p 0 v⁻¹) (ha : D p s a) :
    D p (2 * s) (v⁻¹ ^ 2 - (u⁻¹ ^ 2 - 2 * a * u⁻¹ ^ 3)) := by
  have h1 : v⁻¹ ^ 2 - (u⁻¹ ^ 2 - 2 * a * u⁻¹ ^ 3) =
      a ^ 2 * ((3 * u + 2 * a) * u⁻¹ ^ 3 * v⁻¹ ^ 2) := by
    subst h
    field_simp
    ring
  rw [h1]
  have ha0 : D p 0 a := ha.le (Nat.zero_le _)
  have h2 : D p 0 (3 * u + 2 * a) := (D.three.mul0 hu').add (D.two.mul0 ha0)
  exact ((ha.pow 2).mul0 ((h2.mul0 (hu.pow0 3)).mul0 (hv.pow0 2))).le (by omega)

private lemma exp3_D {s : ℕ} {u v a : ℚ} (hu0 : u ≠ 0) (hv0 : v ≠ 0) (h : v = u + a)
    (hu : D p 0 u⁻¹) (hu' : D p 0 u) (hv : D p 0 v⁻¹) (ha : D p s a) :
    D p (2 * s) (v⁻¹ ^ 3 - (u⁻¹ ^ 3 - 3 * a * u⁻¹ ^ 4)) := by
  have h1 : v⁻¹ ^ 3 - (u⁻¹ ^ 3 - 3 * a * u⁻¹ ^ 4) =
      a ^ 2 * ((2 * (3 * u ^ 2) + 2 * (2 * (2 * (u * a))) + 3 * a ^ 2) * u⁻¹ ^ 4 * v⁻¹ ^ 3) := by
    subst h
    field_simp
    ring
  rw [h1]
  have ha0 : D p 0 a := ha.le (Nat.zero_le _)
  have h2 : D p 0 (2 * (3 * u ^ 2) + 2 * (2 * (2 * (u * a))) + 3 * a ^ 2) :=
    ((D.two.mul0 (D.three.mul0 (hu'.pow0 2))).add
      (D.two.mul0 (D.two.mul0 (D.two.mul0 (hu'.mul0 ha0))))).add (D.three.mul0 (ha0.pow0 2))
  exact ((ha.pow 2).mul0 ((h2.mul0 (hu.pow0 4)).mul0 (hv.pow0 3))).le (by omega)

/-! ### products -/

private lemma prod_congr_D {ι : Type*} [DecidableEq ι] {e : ℕ} (s : Finset ι) (f g : ι → ℚ)
    (hf : ∀ i ∈ s, D p 0 (f i)) (hg : ∀ i ∈ s, D p 0 (g i)) (h : ∀ i ∈ s, D p e (f i - g i)) :
    D p e (∏ i ∈ s, f i - ∏ i ∈ s, g i) := by
  induction s using Finset.induction_on with
  | empty => simpa using D.zero (p := p) e
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    have h1 : f a * ∏ i ∈ s, f i - g a * ∏ i ∈ s, g i =
        (f a - g a) * ∏ i ∈ s, f i + g a * (∏ i ∈ s, f i - ∏ i ∈ s, g i) := by ring
    rw [h1]
    have hs : ∀ i ∈ s, i ∈ insert a s := fun i hi => Finset.mem_insert_of_mem hi
    exact ((h a (Finset.mem_insert_self a s)).mul0 (D.prod s f fun i hi => hf i (hs i hi))).add
      ((hg a (Finset.mem_insert_self a s)).mul0'
        (ih (fun i hi => hf i (hs i hi)) (fun i hi => hg i (hs i hi)) (fun i hi => h i (hs i hi))))

private lemma prod_expand2 {ι : Type*} [DecidableEq ι] (hp2 : ¬ p ∣ 2) (s : Finset ι)
    (a : ι → ℚ) (x : ℚ) (hx : D p 0 x) (ha : ∀ i ∈ s, D p 0 (a i)) :
    ∃ W : ℚ, D p 0 W ∧ ∏ i ∈ s, (1 - x * a i) =
      1 - x * (∑ i ∈ s, a i) + x ^ 2 * (((∑ i ∈ s, a i) ^ 2 - ∑ i ∈ s, a i ^ 2) / 2) +
        x ^ 3 * W := by
  induction s using Finset.induction_on with
  | empty => exact ⟨0, D.zero 0, by simp⟩
  | insert b s hb ih =>
    obtain ⟨W, hW, hprod⟩ := ih (fun i hi => ha i (Finset.mem_insert_of_mem hi))
    have hab := ha b (Finset.mem_insert_self b s)
    have hS1 : D p 0 (∑ i ∈ s, a i) :=
      D.sum s a fun i hi => ha i (Finset.mem_insert_of_mem hi)
    have hS2 : D p 0 (∑ i ∈ s, a i ^ 2) :=
      D.sum s _ fun i hi => (ha i (Finset.mem_insert_of_mem hi)).pow0 2
    have h2 : D p 0 ((2 : ℚ)⁻¹) := by simpa using D.inv (p := p) hp2
    have hE : D p 0 (((∑ i ∈ s, a i) ^ 2 - ∑ i ∈ s, a i ^ 2) / 2) := by
      rw [div_eq_mul_inv]
      exact ((hS1.pow0 2).sub hS2).mul0 h2
    refine ⟨W - a b * (((∑ i ∈ s, a i) ^ 2 - ∑ i ∈ s, a i ^ 2) / 2) - x * a b * W, ?_, ?_⟩
    · exact (hW.sub (hab.mul0 hE)).sub ((hx.mul0 hab).mul0 hW)
    · rw [Finset.prod_insert hb, Finset.sum_insert hb, Finset.sum_insert hb, hprod]
      ring

/-! ### symmetries of `U p q` -/

omit hp in
private lemma sum_U_reflect {q : ℕ} (hpq : p ∣ q) (f : ℕ → ℚ) :
    ∑ u ∈ U p q, f u = ∑ u ∈ U p q, f (q - u) := by
  symm
  have hmem : ∀ u ∈ U p q, q - u ∈ U p q := by
    intro u hu
    obtain ⟨hlt, hnd⟩ := mem_U.mp hu
    have hu0 : u ≠ 0 := by
      rintro rfl
      exact hnd (dvd_zero p)
    refine mem_U.mpr ⟨by omega, ?_⟩
    intro hd
    have h1 : q - u + u = q := Nat.sub_add_cancel (le_of_lt hlt)
    have h2 : p ∣ q - u + u := by rw [h1]; exact hpq
    exact hnd ((Nat.dvd_add_right hd).mp h2)
  have hinv : ∀ u ∈ U p q, q - (q - u) = u := by
    intro u hu
    obtain ⟨hlt, _⟩ := mem_U.mp hu
    omega
  exact Finset.sum_nbij' (fun u => q - u) (fun u => q - u) hmem hmem hinv hinv
    (fun u _ => rfl)

omit hp in
private lemma sum_U_double {q : ℕ} (hp' : p.Prime) (hp2 : ¬ p ∣ 2) (hpq : p ∣ q)
    (hq : Nat.Coprime q 2) (f : ℕ → ℚ) :
    ∑ u ∈ U p q, f (2 * u % q) = ∑ u ∈ U p q, f u := by
  have hinj : Set.InjOn (fun u => 2 * u % q) (U p q : Set ℕ) := by
    intro u hu v hv h
    have hu' := mem_U.mp (Finset.mem_coe.mp hu)
    have hv' := mem_U.mp (Finset.mem_coe.mp hv)
    have h1 : 2 * u ≡ 2 * v [MOD q] := h
    have h2 : u ≡ v [MOD q] := Nat.ModEq.cancel_left_of_coprime hq h1
    exact Nat.ModEq.eq_of_lt_of_lt h2 hu'.1 hv'.1
  have himg : (U p q).image (fun u => 2 * u % q) = U p q := by
    apply Finset.eq_of_subset_of_card_le
    · intro w hw
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hw
      have hu' := mem_U.mp hu
      have hq0 : 0 < q := by omega
      refine mem_U.mpr ⟨Nat.mod_lt _ hq0, ?_⟩
      intro hd
      have h3 : p ∣ 2 * u := (Nat.dvd_mod_iff hpq).mp hd
      rcases (Nat.Prime.dvd_mul hp').mp h3 with h4 | h4
      · exact hp2 h4
      · exact hu'.2 h4
    · rw [Finset.card_image_of_injOn hinj]
  calc ∑ u ∈ U p q, f (2 * u % q)
      = ∑ w ∈ (U p q).image (fun u => 2 * u % q), f w := by
        rw [Finset.sum_image hinj]
    _ = ∑ u ∈ U p q, f u := by rw [himg]

private lemma D_inv_pow_congr {s x y : ℕ} (hx : ¬ p ∣ x) (hy : ¬ p ∣ y)
    (h : D p s ((x : ℚ) - (y : ℚ))) (j : ℕ) :
    D p s (((x : ℚ)⁻¹) ^ j - ((y : ℚ)⁻¹) ^ j) := by
  have hx0 : (x : ℚ) ≠ 0 := by
    intro h0
    apply hx
    have h1 : x = 0 := by exact_mod_cast h0
    rw [h1]; exact dvd_zero p
  have hy0 : (y : ℚ) ≠ 0 := by
    intro h0
    apply hy
    have h1 : y = 0 := by exact_mod_cast h0
    rw [h1]; exact dvd_zero p
  have hxx : (x : ℚ) * (x : ℚ)⁻¹ = 1 := mul_inv_cancel₀ hx0
  have hyy : (y : ℚ) * (y : ℚ)⁻¹ = 1 := mul_inv_cancel₀ hy0
  have h1 : D p s ((x : ℚ)⁻¹ - (y : ℚ)⁻¹) := by
    have h2 : (x : ℚ)⁻¹ - (y : ℚ)⁻¹ = -(((x : ℚ) - (y : ℚ)) * ((x : ℚ)⁻¹ * (y : ℚ)⁻¹)) := by
      linear_combination (y : ℚ)⁻¹ * hxx - (x : ℚ)⁻¹ * hyy
    rw [h2]
    exact (h.mul0 (((D.inv hx).mul (D.inv hy)).le (by omega))).neg
  induction j with
  | zero => simpa using D.zero (p := p) s
  | succ j ih =>
    have h3 : ((x : ℚ)⁻¹) ^ (j + 1) - ((y : ℚ)⁻¹) ^ (j + 1) =
        (x : ℚ)⁻¹ * (((x : ℚ)⁻¹) ^ j - ((y : ℚ)⁻¹) ^ j) +
          ((x : ℚ)⁻¹ - (y : ℚ)⁻¹) * ((y : ℚ)⁻¹) ^ j := by ring
    rw [h3]
    exact ((D.inv hx).mul0' ih).add (h1.mul0 ((D.inv hy).pow0 j))

/-! ### power sums over the units below `p^s` -/

/-- `sg p q j = ∑_{0<u<q, p ∤ u} u^(-j)` -/
private def sg (p q j : ℕ) : ℚ := ∑ u ∈ U p q, ((u : ℚ)⁻¹) ^ j

private lemma sg_scale (hp2 : ¬ p ∣ 2) {s : ℕ} (hs : 1 ≤ s) (j : ℕ) :
    D p s (((2 : ℚ) ^ j - 1) * sg p (p ^ s) j) := by
  have hpq : p ∣ p ^ s := dvd_pow_self p (by omega)
  have hq2 : Nat.Coprime (p ^ s) 2 :=
    Nat.Coprime.pow_left s ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hp2)
  have h1 : sg p (p ^ s) j = ∑ u ∈ U p (p ^ s), (((2 * u % p ^ s : ℕ) : ℚ)⁻¹) ^ j := by
    unfold sg
    exact (sum_U_double hp.out hp2 hpq hq2 (fun w => ((w : ℚ)⁻¹) ^ j)).symm
  have h2 : D p s (∑ u ∈ U p (p ^ s),
      ((((2 * u % p ^ s : ℕ) : ℚ)⁻¹) ^ j - (((2 * u : ℕ) : ℚ)⁻¹) ^ j)) := by
    apply D.sum
    intro u hu
    have hu' := mem_U.mp hu
    have h2u : ¬ p ∣ 2 * u := by
      intro hd
      rcases (Nat.Prime.dvd_mul hp.out).mp hd with h4 | h4
      · exact hp2 h4
      · exact hu'.2 h4
    have hmod : ¬ p ∣ 2 * u % p ^ s := fun hd => h2u ((Nat.dvd_mod_iff hpq).mp hd)
    apply D_inv_pow_congr hmod h2u
    have h5 : ((2 * u % p ^ s : ℕ) : ℚ) - ((2 * u : ℕ) : ℚ) =
        -((p : ℚ) ^ s * ((2 * u / p ^ s : ℕ) : ℚ)) := by
      have h6 := Nat.div_add_mod (2 * u) (p ^ s)
      have h7 : ((p ^ s * (2 * u / p ^ s) + 2 * u % p ^ s : ℕ) : ℚ) = ((2 * u : ℕ) : ℚ) := by
        rw [h6]
      push_cast at h7 ⊢
      linarith
    rw [h5]
    exact ((D.ppow s).mul0 (D.nat _)).neg
  rw [Finset.sum_sub_distrib, ← h1] at h2
  have h3 : ∑ u ∈ U p (p ^ s), (((2 * u : ℕ) : ℚ)⁻¹) ^ j = ((2 : ℚ)⁻¹) ^ j * sg p (p ^ s) j := by
    unfold sg
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    push_cast
    rw [mul_inv, mul_pow]
  rw [h3] at h2
  have h4 : ((2 : ℚ) ^ j - 1) * sg p (p ^ s) j =
      (2 : ℚ) ^ j * (sg p (p ^ s) j - ((2 : ℚ)⁻¹) ^ j * sg p (p ^ s) j) := by
    have h5 : (2 : ℚ) ^ j * ((2 : ℚ)⁻¹) ^ j = 1 := by
      rw [← mul_pow]; norm_num
    linear_combination (sg p (p ^ s) j) * h5
  rw [h4]
  exact (D.two.pow0 j).mul0' h2

/-- generic shifted sums: `v = u + a` with `a ∈ p^s ℤ_(p)` -/
private lemma shift_sums {s : ℕ} (a : ℚ) (ha : D p s a) (v : ℕ → ℚ)
    (hv : ∀ u ∈ U p (p ^ s), v u = (u : ℚ) + a ∧ v u ≠ 0 ∧ D p 0 (v u)⁻¹) :
    D p (4 * s) (∑ u ∈ U p (p ^ s), (v u)⁻¹ -
      (sg p (p ^ s) 1 - a * sg p (p ^ s) 2 + a ^ 2 * sg p (p ^ s) 3 - a ^ 3 * sg p (p ^ s) 4)) ∧
    D p (2 * s) (∑ u ∈ U p (p ^ s), (v u)⁻¹ ^ 2 -
      (sg p (p ^ s) 2 - 2 * a * sg p (p ^ s) 3)) ∧
    D p (2 * s) (∑ u ∈ U p (p ^ s), (v u)⁻¹ ^ 3 -
      (sg p (p ^ s) 3 - 3 * a * sg p (p ^ s) 4)) := by
  have hu : ∀ u ∈ U p (p ^ s), (u : ℚ) ≠ 0 ∧ D p 0 ((u : ℚ)⁻¹) := by
    intro u hu
    obtain ⟨_, hnd⟩ := mem_U.mp hu
    refine ⟨?_, D.inv hnd⟩
    intro h0
    apply hnd
    have h1 : u = 0 := by exact_mod_cast h0
    rw [h1]; exact dvd_zero p
  refine ⟨?_, ?_, ?_⟩
  · have h1 : ∑ u ∈ U p (p ^ s), (v u)⁻¹ -
        (sg p (p ^ s) 1 - a * sg p (p ^ s) 2 + a ^ 2 * sg p (p ^ s) 3 - a ^ 3 * sg p (p ^ s) 4) =
        ∑ u ∈ U p (p ^ s), ((v u)⁻¹ - ((u : ℚ)⁻¹ - a * (u : ℚ)⁻¹ ^ 2 + a ^ 2 * (u : ℚ)⁻¹ ^ 3 -
          a ^ 3 * (u : ℚ)⁻¹ ^ 4)) := by
      simp only [sg, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum, pow_one]
    rw [h1]
    apply D.sum
    intro u hmem
    obtain ⟨h2, h3, h4⟩ := hv u hmem
    exact exp1_D (hu u hmem).1 h3 h2 (hu u hmem).2 h4 ha
  · have h1 : ∑ u ∈ U p (p ^ s), (v u)⁻¹ ^ 2 - (sg p (p ^ s) 2 - 2 * a * sg p (p ^ s) 3) =
        ∑ u ∈ U p (p ^ s), ((v u)⁻¹ ^ 2 - ((u : ℚ)⁻¹ ^ 2 - 2 * a * (u : ℚ)⁻¹ ^ 3)) := by
      simp only [sg, Finset.sum_sub_distrib, Finset.mul_sum]
    rw [h1]
    apply D.sum
    intro u hmem
    obtain ⟨h2, h3, h4⟩ := hv u hmem
    exact exp2_D (hu u hmem).1 h3 h2 (hu u hmem).2 (D.nat u) h4 ha
  · have h1 : ∑ u ∈ U p (p ^ s), (v u)⁻¹ ^ 3 - (sg p (p ^ s) 3 - 3 * a * sg p (p ^ s) 4) =
        ∑ u ∈ U p (p ^ s), ((v u)⁻¹ ^ 3 - ((u : ℚ)⁻¹ ^ 3 - 3 * a * (u : ℚ)⁻¹ ^ 4)) := by
      simp only [sg, Finset.sum_sub_distrib, Finset.mul_sum]
    rw [h1]
    apply D.sum
    intro u hmem
    obtain ⟨h2, h3, h4⟩ := hv u hmem
    exact exp3_D (hu u hmem).1 h3 h2 (hu u hmem).2 (D.nat u) h4 ha
/-! ### derived power sum facts -/

omit hp in
private lemma D.congr {e : ℕ} {x y : ℚ} (h : D p e x) (hxy : x = y) : D p e y := hxy ▸ h

private lemma sg_D0 (q j : ℕ) : D p 0 (sg p q j) :=
  D.sum _ _ fun _ hu => (D.inv (mem_U.mp hu).2).pow0 j

/-- `Eps p ε`: `ε = 0` and `p ∤ 15`, or `ε = 1` and `p = 5`. -/
private def Eps (p ε : ℕ) : Prop := (ε = 0 ∧ ¬ p ∣ 15) ∨ (ε = 1 ∧ p = 5)

omit hp in
private lemma Eps.le_one {ε : ℕ} (h : Eps p ε) : ε ≤ 1 := by
  rcases h with ⟨h, _⟩ | ⟨h, _⟩ <;> omega

private lemma sg2 (h5 : 5 ≤ p) {s : ℕ} (hs : 1 ≤ s) : D p s (sg p (p ^ s) 2) := by
  have hp2 : ¬ p ∣ 2 := Nat.not_dvd_of_pos_of_lt (by norm_num) (by omega)
  have hp3 : ¬ p ∣ 3 := Nat.not_dvd_of_pos_of_lt (by norm_num) (by omega)
  have h := sg_scale hp2 hs 2
  exact D.ucancel hp3 (h.congr (by push_cast; ring))

private lemma sg4 (h5 : 5 ≤ p) {ε : ℕ} (hε : Eps p ε) {s : ℕ} (hs : 1 ≤ s) :
    D p s ((p : ℚ) ^ ε * sg p (p ^ s) 4) := by
  have hp2 : ¬ p ∣ 2 := Nat.not_dvd_of_pos_of_lt (by norm_num) (by omega)
  have hp3 : ¬ p ∣ 3 := Nat.not_dvd_of_pos_of_lt (by norm_num) (by omega)
  have h := sg_scale hp2 hs 4
  rcases hε with ⟨rfl, h15⟩ | ⟨rfl, h55⟩
  · have h6 : D p s (sg p (p ^ s) 4) := D.ucancel h15 (h.congr (by push_cast; ring))
    exact h6.congr (by ring)
  · have h6 : D p s (((3 : ℕ) : ℚ) * ((p : ℚ) ^ 1 * sg p (p ^ s) 4)) := by
      refine h.congr ?_
      rw [h55]
      push_cast
      ring
    exact D.ucancel hp3 h6

private lemma refl_sums {s : ℕ} (hs : 1 ≤ s) :
    D p (4 * s) (2 * sg p (p ^ s) 1 + (p : ℚ) ^ s * sg p (p ^ s) 2 +
      ((p : ℚ) ^ s) ^ 2 * sg p (p ^ s) 3 + ((p : ℚ) ^ s) ^ 3 * sg p (p ^ s) 4) ∧
    D p (2 * s) (2 * sg p (p ^ s) 3 + 3 * (p : ℚ) ^ s * sg p (p ^ s) 4) := by
  have hpq : p ∣ p ^ s := dvd_pow_self p (by omega)
  have hv : ∀ u ∈ U p (p ^ s), (-(((p ^ s - u : ℕ) : ℚ))) = (u : ℚ) + (-(p : ℚ) ^ s) ∧
      (-(((p ^ s - u : ℕ) : ℚ))) ≠ 0 ∧ D p 0 (-(((p ^ s - u : ℕ) : ℚ)))⁻¹ := by
    intro u hu
    obtain ⟨hlt, hnd⟩ := mem_U.mp hu
    have hw : ¬ p ∣ p ^ s - u := by
      intro hd
      have h1 : p ^ s - u + u = p ^ s := Nat.sub_add_cancel (le_of_lt hlt)
      have h2 : p ∣ p ^ s - u + u := by rw [h1]; exact hpq
      exact hnd ((Nat.dvd_add_right hd).mp h2)
    have hw0 : ((p ^ s - u : ℕ) : ℚ) ≠ 0 := by
      have h1 : p ^ s - u ≠ 0 := by omega
      exact_mod_cast h1
    refine ⟨?_, neg_ne_zero.mpr hw0, ?_⟩
    · rw [Nat.cast_sub (le_of_lt hlt)]
      push_cast
      ring
    · rw [inv_neg]
      exact (D.inv hw).neg
  obtain ⟨h1, _, h3⟩ :=
    shift_sums (-(p : ℚ) ^ s) (D.ppow s).neg (fun u => -(((p ^ s - u : ℕ) : ℚ))) hv
  have hr1 : ∑ u ∈ U p (p ^ s), (-(((p ^ s - u : ℕ) : ℚ)))⁻¹ = -sg p (p ^ s) 1 := by
    have h := sum_U_reflect hpq (fun w => (w : ℚ)⁻¹ ^ 1)
    simp only [sg]
    rw [h, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [inv_neg, pow_one]
  have hr3 : ∑ u ∈ U p (p ^ s), (-(((p ^ s - u : ℕ) : ℚ)))⁻¹ ^ 3 = -sg p (p ^ s) 3 := by
    have h := sum_U_reflect hpq (fun w => (w : ℚ)⁻¹ ^ 3)
    simp only [sg]
    rw [h, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [inv_neg]
    ring
  rw [hr1] at h1
  rw [hr3] at h3
  exact ⟨h1.neg.congr (by ring), h3.neg.congr (by ring)⟩

private lemma sg3 (h5 : 5 ≤ p) {ε : ℕ} (hε : Eps p ε) {s : ℕ} (hs : 1 ≤ s) :
    D p s (sg p (p ^ s) 3) ∧ D p (2 * s) ((p : ℚ) ^ ε * sg p (p ^ s) 3) := by
  have hp2 : ¬ p ∣ 2 := Nat.not_dvd_of_pos_of_lt (by norm_num) (by omega)
  obtain ⟨_, h3⟩ := refl_sums (p := p) hs
  have h4 := sg4 h5 hε hs
  have hσ4 : D p 0 (sg p (p ^ s) 4) := sg_D0 _ _
  constructor
  · have h6 : D p s (((2 : ℕ) : ℚ) * sg p (p ^ s) 3) := by
      have h7 := (h3.le (by omega : s ≤ 2 * s)).sub (D.three.mul0' ((D.ppow s).mul0 hσ4))
      exact h7.congr (by push_cast; ring)
    exact D.ucancel hp2 h6
  · have h6 : D p (2 * s) (((2 : ℕ) : ℚ) * ((p : ℚ) ^ ε * sg p (p ^ s) 3)) := by
      have h7 := (((D.ppow (p := p) ε).le (Nat.zero_le _)).mul0' h3).sub
        (D.three.mul0' (((D.ppow s).mul h4).le (by omega : 2 * s ≤ s + s)))
      exact h7.congr (by push_cast; ring)
    exact D.ucancel hp2 h6

private lemma sg1 (h5 : 5 ≤ p) {ε : ℕ} (hε : Eps p ε) {s : ℕ} (hs : 1 ≤ s) :
    D p (4 * s) ((p : ℚ) ^ ε * (2 * sg p (p ^ s) 1 + (p : ℚ) ^ s * sg p (p ^ s) 2)) := by
  obtain ⟨h1, _⟩ := refl_sums (p := p) hs
  obtain ⟨_, h3⟩ := sg3 h5 hε hs
  have h4 := sg4 h5 hε hs
  have h7 := ((((D.ppow (p := p) ε).le (Nat.zero_le _)).mul0' h1).sub
    ((((D.ppow s).pow 2).mul h3).le (by omega : 4 * s ≤ s * 2 + 2 * s))).sub
    ((((D.ppow s).pow 3).mul h4).le (by omega : 4 * s ≤ s * 3 + s))
  exact h7.congr (by ring)

private lemma trans_sums {s : ℕ} (hs : 1 ≤ s) (h : ℕ) :
    D p (4 * s) (∑ u ∈ U p (p ^ s), (((h * p ^ s + u : ℕ) : ℚ))⁻¹ -
      (sg p (p ^ s) 1 - ((h : ℚ) * (p : ℚ) ^ s) * sg p (p ^ s) 2 +
        ((h : ℚ) * (p : ℚ) ^ s) ^ 2 * sg p (p ^ s) 3 -
        ((h : ℚ) * (p : ℚ) ^ s) ^ 3 * sg p (p ^ s) 4)) ∧
    D p (2 * s) (∑ u ∈ U p (p ^ s), (((h * p ^ s + u : ℕ) : ℚ))⁻¹ ^ 2 -
      (sg p (p ^ s) 2 - 2 * ((h : ℚ) * (p : ℚ) ^ s) * sg p (p ^ s) 3)) ∧
    D p (2 * s) (∑ u ∈ U p (p ^ s), (((h * p ^ s + u : ℕ) : ℚ))⁻¹ ^ 3 -
      (sg p (p ^ s) 3 - 3 * ((h : ℚ) * (p : ℚ) ^ s) * sg p (p ^ s) 4)) := by
  have hpq : p ∣ p ^ s := dvd_pow_self p (by omega)
  apply shift_sums ((h : ℚ) * (p : ℚ) ^ s) ((D.nat h).mul0' (D.ppow s))
    (fun u => ((h * p ^ s + u : ℕ) : ℚ))
  intro u hu
  obtain ⟨hlt, hnd⟩ := mem_U.mp hu
  have hw : ¬ p ∣ h * p ^ s + u :=
    fun hd => hnd ((Nat.dvd_add_right (dvd_mul_of_dvd_right hpq h)).mp hd)
  refine ⟨by push_cast; ring, ?_, D.inv hw⟩
  intro h0
  have h1 : h * p ^ s + u = 0 := by exact_mod_cast h0
  apply hw
  rw [h1]
  exact dvd_zero p

/-- `h_1(t q) = -(q t^2 / 2) H_2(q)` to precision `4s - ε` -/
private lemma hs1_blocks (h5 : 5 ≤ p) {ε : ℕ} (hε : Eps p ε) {s : ℕ} (hs : 1 ≤ s) (t : ℕ) :
    D p (4 * s) ((p : ℚ) ^ ε *
      (2 * sg p (t * p ^ s) 1 + (p : ℚ) ^ s * (t : ℚ) ^ 2 * sg p (p ^ s) 2)) := by
  have hpq : p ∣ p ^ s := dvd_pow_self p (by omega)
  have h1 := sg1 h5 hε hs
  obtain ⟨_, h3⟩ := sg3 h5 hε hs
  have h4 := sg4 h5 hε hs
  have hb : sg p (t * p ^ s) 1 =
      ∑ h ∈ Finset.range t, ∑ u ∈ U p (p ^ s), (((h * p ^ s + u : ℕ) : ℚ))⁻¹ := by
    unfold sg
    rw [sum_U_blocks hpq]
    simp only [pow_one]
  rw [hb]
  clear hb
  induction t with
  | zero => exact (D.zero _).congr (by simp)
  | succ t ih =>
    obtain ⟨hT, _, _⟩ := trans_sums (p := p) hs t
    have hpe : D p 0 ((p : ℚ) ^ ε) := (D.ppow ε).le (Nat.zero_le _)
    have htq : D p s ((t : ℚ) * (p : ℚ) ^ s) := (D.nat t).mul0' (D.ppow s)
    have h7 := ih.add ((((D.two.mul0' (hpe.mul0' hT)).add h1).add
      (D.two.mul0' (((htq.pow 2).mul h3).le (by omega : 4 * s ≤ s * 2 + 2 * s)))).sub
      (D.two.mul0' (((htq.pow 3).mul h4).le (by omega : 4 * s ≤ s * 3 + s))))
    refine h7.congr ?_
    rw [Finset.sum_range_succ]
    push_cast
    ring

/-- `h_2(t q) = t H_2(q)` to precision `2s` -/
private lemma hs2_blocks (h5 : 5 ≤ p) {s : ℕ} (hs : 1 ≤ s) (t : ℕ) :
    D p (2 * s) (sg p (t * p ^ s) 2 - (t : ℚ) * sg p (p ^ s) 2) := by
  have hpq : p ∣ p ^ s := dvd_pow_self p (by omega)
  have hε : Eps p (if p = 5 then 1 else 0) := by
    by_cases h : p = 5
    · right; simp [h]
    · left
      refine ⟨by simp [h], ?_⟩
      intro hd
      have h15 : (15 : ℕ) = 3 * 5 := by norm_num
      rw [h15] at hd
      rcases (Nat.Prime.dvd_mul hp.out).mp hd with h1 | h1
      · have := Nat.le_of_dvd (by norm_num) h1; omega
      · have := Nat.le_of_dvd (by norm_num) h1; omega
  obtain ⟨h3, _⟩ := sg3 h5 hε hs
  have hb : sg p (t * p ^ s) 2 =
      ∑ h ∈ Finset.range t, ∑ u ∈ U p (p ^ s), (((h * p ^ s + u : ℕ) : ℚ))⁻¹ ^ 2 := by
    unfold sg
    rw [sum_U_blocks hpq]
  rw [hb]
  clear hb
  induction t with
  | zero => exact (D.zero _).congr (by simp)
  | succ t ih =>
    obtain ⟨_, hT, _⟩ := trans_sums (p := p) hs t
    have h7 := ih.add (hT.sub (D.two.mul0' (((D.nat t).mul0' ((D.ppow s).mul h3)).le
      (by omega : 2 * s ≤ s + s))))
    refine h7.congr ?_
    rw [Finset.sum_range_succ]
    push_cast
    ring

/-- `∑_u (A q + u)^(-3)` to precision `2s - ε` -/
private lemma cube_block (h5 : 5 ≤ p) {ε : ℕ} (hε : Eps p ε) {s : ℕ} (hs : 1 ≤ s) (A : ℕ) :
    D p (2 * s) ((p : ℚ) ^ ε * ∑ u ∈ U p (p ^ s), (((A * p ^ s + u : ℕ) : ℚ))⁻¹ ^ 3) := by
  obtain ⟨_, _, hT⟩ := trans_sums (p := p) hs A
  obtain ⟨_, h3⟩ := sg3 h5 hε hs
  have h4 := sg4 h5 hε hs
  have hpe : D p 0 ((p : ℚ) ^ ε) := (D.ppow ε).le (Nat.zero_le _)
  have h7 := ((hpe.mul0' hT).add h3).sub
    (D.three.mul0' (((D.nat A).mul0' ((D.ppow s).mul h4)).le (by omega : 2 * s ≤ s + s)))
  exact h7.congr (by ring)

/-- the main expansion of `R(t p^s) = ∏_{0<i<t p^s, p ∤ i} (1 - 3 p^r / i)` -/
private lemma R_lemma (h5 : 5 ≤ p) {ε : ℕ} (hε : Eps p ε) {r s : ℕ} (hs : 1 ≤ s) (t E : ℕ)
    (hE1 : E + ε ≤ r + 4 * s) (hE2 : E ≤ 2 * r + 2 * s) (hE3 : E ≤ 3 * r) :
    D p E (R p (3 * (p : ℚ) ^ r) (t * p ^ s) - 1 -
      3 / 2 * (p : ℚ) ^ r * (t : ℚ) * sg p (p ^ s) 2 *
        ((t : ℚ) * (p : ℚ) ^ s - 3 * (p : ℚ) ^ r)) := by
  have hp2 : ¬ p ∣ 2 := Nat.not_dvd_of_pos_of_lt (by norm_num) (by omega)
  have hε1 := hε.le_one
  have hx : D p r (3 * (p : ℚ) ^ r) := D.three.mul0' (D.ppow r)
  have hx0 : D p 0 (3 * (p : ℚ) ^ r) := hx.le (Nat.zero_le _)
  have h2i : D p 0 ((2 : ℚ)⁻¹) := by simpa using D.inv (p := p) hp2
  obtain ⟨W, hW, hprod⟩ := prod_expand2 hp2 (U p (t * p ^ s)) (fun i => (i : ℚ)⁻¹)
    (3 * (p : ℚ) ^ r) hx0 (fun i hi => D.inv (mem_U.mp hi).2)
  have hR : R p (3 * (p : ℚ) ^ r) (t * p ^ s) =
      ∏ i ∈ U p (t * p ^ s), (1 - 3 * (p : ℚ) ^ r * (i : ℚ)⁻¹) := by
    unfold R
    simp only [div_eq_mul_inv]
  have hS1 : ∑ i ∈ U p (t * p ^ s), (i : ℚ)⁻¹ = sg p (t * p ^ s) 1 := by
    simp only [sg, pow_one]
  have hS2 : ∑ i ∈ U p (t * p ^ s), (i : ℚ)⁻¹ ^ 2 = sg p (t * p ^ s) 2 := rfl
  rw [hS1, hS2] at hprod
  -- the three small quantities
  have hA' := hs1_blocks h5 hε hs t
  have hA : D p (4 * s - ε) (2 * sg p (t * p ^ s) 1 + (p : ℚ) ^ s * (t : ℚ) ^ 2 * sg p (p ^ s) 2) := by
    apply D.cancel (c := ε)
    rw [show 4 * s - ε + ε = 4 * s by omega]
    exact hA'
  have hσ := sg2 h5 hs
  have hh1 : D p (2 * s) (sg p (t * p ^ s) 1) := by
    have h6 : D p (2 * s) (((2 : ℕ) : ℚ) * sg p (t * p ^ s) 1) := by
      have h7 := (hA.le (by omega : 2 * s ≤ 4 * s - ε)).sub
        ((((D.ppow s).mul0 ((D.nat t).pow0 2)).mul hσ).le (by omega : 2 * s ≤ s + s))
      exact h7.congr (by push_cast; ring)
    exact D.ucancel hp2 h6
  have hB := hs2_blocks h5 hs t
  have h7 := (((h2i.mul0' (hx.mul hA)).le (by omega : E ≤ r + (4 * s - ε))).neg.add
    ((h2i.mul0' ((hx.pow 2).mul (hh1.pow 2))).le (by omega : E ≤ r * 2 + 2 * s * 2))).sub
    ((h2i.mul0' ((hx.pow 2).mul hB)).le (by omega : E ≤ r * 2 + 2 * s))
  have h8 := h7.add (((hx.pow 3).mul0 hW).le (by omega : E ≤ r * 3))
  refine h8.congr ?_
  rw [hR, hprod]
  ring
/-! ### the unit part -/

private lemma D_cube_sub {e : ℕ} {a b : ℚ} (ha : D p 0 a) (hb : D p 0 b) (h : D p e (a - b)) :
    D p e (a ^ 3 - b ^ 3) :=
  (h.mul0 (((ha.pow0 2).add (ha.mul0 hb)).add (hb.pow0 2))).congr (by ring)

private lemma D_of_sub_one {e : ℕ} {a : ℚ} (h : D p e (a - 1)) : D p 0 a :=
  ((h.le (Nat.zero_le _)).add D.one).congr (by ring)

private lemma D_cube_one {e : ℕ} {a : ℚ} (h : D p e (a - 1)) : D p e (a ^ 3 - 1) :=
  (D_cube_sub (D_of_sub_one h) D.one h).congr (by ring)

omit hp in
private lemma exists_decomp (hp' : p.Prime) {c i : ℕ} (hi0 : i ≠ 0) (hic : i < p ^ c) :
    ∃ e u, e < c ∧ ¬ p ∣ u ∧ i = p ^ e * u := by
  obtain ⟨e, u, hu, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hi0 p hp'.ne_one
  refine ⟨e, u, ?_, hu, rfl⟩
  have hu0 : 0 < u := Nat.pos_of_ne_zero (by rintro rfl; exact hu (dvd_zero p))
  have h1 : p ^ e ≤ p ^ e * u := Nat.le_mul_of_pos_right _ hu0
  exact (Nat.pow_lt_pow_iff_right hp'.one_lt).mp (lt_of_le_of_lt h1 hic)

private lemma D_ppow_div {m e u : ℕ} (hem : e ≤ m) (hu : ¬ p ∣ u) :
    D p (m - e) ((p : ℚ) ^ m / ((p ^ e * u : ℕ) : ℚ)) := by
  have hp0 : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
  have hu0 : (u : ℚ) ≠ 0 := by
    intro h0
    apply hu
    have h1 : u = 0 := by exact_mod_cast h0
    rw [h1]; exact dvd_zero p
  have e1 : (p : ℚ) ^ (m - e) * (u : ℚ)⁻¹ = (p : ℚ) ^ m / ((p ^ e * u : ℕ) : ℚ) := by
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hem
    rw [Nat.add_sub_cancel_left, pow_add]
    push_cast
    field_simp
  exact ((D.ppow (m - e)).mul0 (D.inv hu)).congr e1

private lemma D_x_div {m c i : ℕ} (hc : c ≤ m + 1) (hi : i < p ^ c) :
    D p (m + 1 - c) (3 * (p : ℚ) ^ m / (i : ℚ)) := by
  rcases Nat.eq_zero_or_pos i with rfl | hi0
  · exact (D.zero _).congr (by simp)
  obtain ⟨e, u, he, hu, rfl⟩ := exists_decomp hp.out (Nat.pos_iff_ne_zero.mp hi0) hi
  have h1 := D.three.mul0' (D_ppow_div (m := m) (e := e) (by omega) hu)
  exact (h1.le (by omega)).congr (by ring)

private lemma Gp_sub_one {m c n : ℕ} (hc : c ≤ m + 1) (hn : n ≤ p ^ c) :
    D p (m + 1 - c) (Gp (3 * (p : ℚ) ^ m) n - 1) := by
  have hf : ∀ i ∈ Finset.range n, D p 0 (1 - 3 * (p : ℚ) ^ m / (i : ℚ)) := by
    intro i hi
    exact D.one.sub ((D_x_div hc (lt_of_lt_of_le (Finset.mem_range.mp hi) hn)).le (Nat.zero_le _))
  have hd : ∀ i ∈ Finset.range n, D p (m + 1 - c) ((1 - 3 * (p : ℚ) ^ m / (i : ℚ)) - 1) := by
    intro i hi
    exact ((D_x_div hc (lt_of_lt_of_le (Finset.mem_range.mp hi) hn)).neg).congr (by ring)
  have h := prod_congr_D (Finset.range n) (fun i => 1 - 3 * (p : ℚ) ^ m / (i : ℚ)) (fun _ => 1)
    hf (fun _ _ => D.one) hd
  exact h.congr (by unfold Gp; rw [Finset.prod_const_one])

private lemma D_div_shift {s A i : ℕ} (hi0 : 0 < i) (hi : i < p ^ s) :
    D p 3 (3 * (p : ℚ) ^ (s + 1) / ((A * p ^ s + i : ℕ) : ℚ) - 3 * (p : ℚ) ^ (s + 1) / (i : ℚ)) := by
  obtain ⟨e, u, he, hu, rfl⟩ := exists_decomp hp.out (Nat.pos_iff_ne_zero.mp hi0) hi
  obtain ⟨d, rfl⟩ : ∃ d, s = e + (d + 1) := ⟨s - e - 1, by omega⟩
  have hP : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
  have hu0 : (u : ℚ) ≠ 0 := by
    intro h0
    apply hu
    have h1 : u = 0 := by exact_mod_cast h0
    rw [h1]; exact dvd_zero p
  have hu' : ¬ p ∣ A * p ^ (d + 1) + u := fun hd =>
    hu ((Nat.dvd_add_right (dvd_mul_of_dvd_right (dvd_pow_self p (Nat.succ_ne_zero d)) A)).mp hd)
  have hw0 : (A : ℚ) * (p : ℚ) ^ (d + 1) + (u : ℚ) ≠ 0 := by
    have h1 : ((A * p ^ (d + 1) + u : ℕ) : ℚ) ≠ 0 := by
      intro h0
      apply hu'
      have h2 : A * p ^ (d + 1) + u = 0 := by exact_mod_cast h0
      rw [h2]; exact dvd_zero p
    push_cast at h1
    exact h1
  have e1 : -(3 * ((p : ℚ) ^ (d + 2) * ((A : ℚ) * (p : ℚ) ^ (d + 1))) *
        ((u : ℚ)⁻¹ * (((A * p ^ (d + 1) + u : ℕ) : ℚ))⁻¹)) =
      3 * (p : ℚ) ^ (e + (d + 1) + 1) / ((A * p ^ (e + (d + 1)) + p ^ e * u : ℕ) : ℚ) -
        3 * (p : ℚ) ^ (e + (d + 1) + 1) / ((p ^ e * u : ℕ) : ℚ) := by
    push_cast
    have h1 : (A : ℚ) * (p : ℚ) ^ (e + (d + 1)) + (p : ℚ) ^ e * (u : ℚ) =
        (p : ℚ) ^ e * ((A : ℚ) * (p : ℚ) ^ (d + 1) + (u : ℚ)) := by ring
    have h2 : (p : ℚ) ^ (e + (d + 1) + 1) = (p : ℚ) ^ e * (p : ℚ) ^ (d + 2) := by ring
    rw [h1, h2]
    field_simp
    ring
  have h3 := ((D.three.mul0' ((D.ppow (d + 2)).mul ((D.nat A).mul0' (D.ppow (d + 1))))).mul0
    (((D.inv hu).mul (D.inv hu')).le (Nat.zero_le _))).neg
  exact (h3.le (by omega)).congr e1

private lemma Gp_block {s A u : ℕ} (hA : A < p) (hu0 : 0 < u) (hu : u < p ^ s) :
    D p 3 (Gp (3 * (p : ℚ) ^ (s + 1)) (A * p ^ s + u) -
      Gp (3 * (p : ℚ) ^ (s + 1)) (A * p ^ s + 1) * Gp (3 * (p : ℚ) ^ (s + 1)) u) := by
  obtain ⟨m, rfl⟩ : ∃ m, u = m + 1 := ⟨u - 1, by omega⟩
  have hAn : A * p ^ s + 1 ≤ p ^ (s + 1) := by
    have h1 : (A + 1) * p ^ s ≤ p * p ^ s := Nat.mul_le_mul_right _ (by omega)
    have h2 : 1 ≤ p ^ s := Nat.one_le_pow _ _ hp.out.pos
    rw [pow_succ']
    nlinarith
  have hα0 : D p 0 (Gp (3 * (p : ℚ) ^ (s + 1)) (A * p ^ s + 1)) :=
    D_of_sub_one (Gp_sub_one (m := s + 1) (c := s + 1) (by omega) hAn)
  have e1 : Gp (3 * (p : ℚ) ^ (s + 1)) (A * p ^ s + (m + 1)) =
      Gp (3 * (p : ℚ) ^ (s + 1)) (A * p ^ s + 1) *
        ∏ i ∈ Finset.range m, (1 - 3 * (p : ℚ) ^ (s + 1) / ((A * p ^ s + (i + 1) : ℕ) : ℚ)) := by
    unfold Gp
    rw [show A * p ^ s + (m + 1) = (A * p ^ s + 1) + m by ring, Finset.prod_range_add]
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [show A * p ^ s + 1 + i = A * p ^ s + (i + 1) by ring]
  have e2 : Gp (3 * (p : ℚ) ^ (s + 1)) (m + 1) =
      ∏ i ∈ Finset.range m, (1 - 3 * (p : ℚ) ^ (s + 1) / ((i + 1 : ℕ) : ℚ)) := by
    unfold Gp
    rw [Finset.prod_range_succ', Nat.cast_zero, div_zero, sub_zero, mul_one]
  have hg : ∀ i ∈ Finset.range m, D p 0 (1 - 3 * (p : ℚ) ^ (s + 1) / ((i + 1 : ℕ) : ℚ)) := by
    intro i hi
    have h1 : i + 1 < p ^ s := by have := Finset.mem_range.mp hi; omega
    exact D.one.sub ((D_x_div (m := s + 1) (c := s) (by omega) h1).le (Nat.zero_le _))
  have hd : ∀ i ∈ Finset.range m, D p 3
      ((1 - 3 * (p : ℚ) ^ (s + 1) / ((A * p ^ s + (i + 1) : ℕ) : ℚ)) -
        (1 - 3 * (p : ℚ) ^ (s + 1) / ((i + 1 : ℕ) : ℚ))) := by
    intro i hi
    have h1 : i + 1 < p ^ s := by have := Finset.mem_range.mp hi; omega
    exact (D_div_shift (A := A) (Nat.succ_pos i) h1).neg.congr (by ring)
  have hf : ∀ i ∈ Finset.range m,
      D p 0 (1 - 3 * (p : ℚ) ^ (s + 1) / ((A * p ^ s + (i + 1) : ℕ) : ℚ)) := by
    intro i hi
    exact (((hd i hi).le (Nat.zero_le _)).add (hg i hi)).congr (by ring)
  have h := prod_congr_D (Finset.range m) _ _ hf hg hd
  rw [e1, e2]
  exact (hα0.mul0' h).congr (by ring)

omit hp in
private lemma block_identity (S : Finset ℕ) (g B x y : ℕ → ℚ) (α : ℚ) :
    (α ^ 3 - 1) * ∑ u ∈ S, x u +
        ∑ u ∈ S, ((g u ^ 3 - α ^ 3 * B u) * x u + (B u - 1) * (α ^ 3 * x u - y u)) =
      ∑ u ∈ S, g u ^ 3 * x u - ∑ u ∈ S, x u - ∑ u ∈ S, (B u - 1) * y u := by
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun u _ => by ring

omit hp in
private lemma sum_three (S : Finset ℕ) (T X : ℕ → ℚ) (Z : ℚ) :
    ∑ A ∈ S, (T A - X A - Z) + ∑ A ∈ S, X A + (S.card : ℚ) * Z = ∑ A ∈ S, T A := by
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
  ring

private lemma unit_part (h5 : 5 ≤ p) {ε : ℕ} (hε : Eps p ε) {s : ℕ} (hs : 1 + ε ≤ s) :
    D p 3 (∑ k ∈ U p (p ^ (s + 1)), Gp (3 * (p : ℚ) ^ (s + 1)) k ^ 3 * ((k : ℚ)⁻¹) ^ 3) := by
  have hs1 : 1 ≤ s := by omega
  have hε1 := hε.le_one
  have hpq : p ∣ p ^ s := dvd_pow_self p (by omega)
  have hB : ∀ u ∈ U p (p ^ s), D p 2 (Gp (3 * (p : ℚ) ^ (s + 1)) u - 1) := by
    intro u hu
    exact (Gp_sub_one (m := s + 1) (c := s) (by omega) (le_of_lt (mem_U.mp hu).1)).le (by omega)
  have hZ2 : D p 2
      (∑ u ∈ U p (p ^ s), (Gp (3 * (p : ℚ) ^ (s + 1)) u ^ 3 - 1) * ((u : ℚ)⁻¹) ^ 3) :=
    D.sum _ _ fun u hu => (D_cube_one (hB u hu)).mul0 ((D.inv (mem_U.mp hu).2).pow0 3)
  have hblock : ∀ A ∈ Finset.range p, D p 3
      (∑ u ∈ U p (p ^ s), Gp (3 * (p : ℚ) ^ (s + 1)) (A * p ^ s + u) ^ 3 *
          (((A * p ^ s + u : ℕ) : ℚ))⁻¹ ^ 3 -
        ∑ u ∈ U p (p ^ s), (((A * p ^ s + u : ℕ) : ℚ))⁻¹ ^ 3 -
        ∑ u ∈ U p (p ^ s), (Gp (3 * (p : ℚ) ^ (s + 1)) u ^ 3 - 1) * ((u : ℚ)⁻¹) ^ 3) := by
    intro A hA
    have hA' := Finset.mem_range.mp hA
    have hAn : A * p ^ s + 1 ≤ p ^ (s + 1) := by
      have h1 : (A + 1) * p ^ s ≤ p * p ^ s := Nat.mul_le_mul_right _ (by omega)
      have h2 : 1 ≤ p ^ s := Nat.one_le_pow _ _ hp.out.pos
      rw [pow_succ']
      nlinarith
    have hα : D p 1 (Gp (3 * (p : ℚ) ^ (s + 1)) (A * p ^ s + 1) - 1) :=
      (Gp_sub_one (m := s + 1) (c := s + 1) (by omega) hAn).le (by omega)
    have hα0 := D_of_sub_one hα
    have hα3 := D_cube_one hα
    have hα30 := D_of_sub_one hα3
    have hX : D p 2 (∑ u ∈ U p (p ^ s), (((A * p ^ s + u : ℕ) : ℚ))⁻¹ ^ 3) := by
      have h1 := cube_block h5 hε hs1 A
      exact D.cancel (c := ε) (h1.le (by omega))
    have hterm : ∀ u ∈ U p (p ^ s), D p 3
        ((Gp (3 * (p : ℚ) ^ (s + 1)) (A * p ^ s + u) ^ 3 -
            Gp (3 * (p : ℚ) ^ (s + 1)) (A * p ^ s + 1) ^ 3 *
              Gp (3 * (p : ℚ) ^ (s + 1)) u ^ 3) * (((A * p ^ s + u : ℕ) : ℚ))⁻¹ ^ 3 +
          (Gp (3 * (p : ℚ) ^ (s + 1)) u ^ 3 - 1) *
            (Gp (3 * (p : ℚ) ^ (s + 1)) (A * p ^ s + 1) ^ 3 *
              (((A * p ^ s + u : ℕ) : ℚ))⁻¹ ^ 3 - ((u : ℚ)⁻¹) ^ 3)) := by
      intro u hu
      obtain ⟨hlt, hnd⟩ := mem_U.mp hu
      have hu0 : 0 < u := Nat.pos_of_ne_zero (by rintro rfl; exact hnd (dvd_zero p))
      have hw : ¬ p ∣ A * p ^ s + u :=
        fun hd => hnd ((Nat.dvd_add_right (dvd_mul_of_dvd_right hpq A)).mp hd)
      have hg := Gp_block (s := s) hA' hu0 hlt
      have hβ := hB u hu
      have hβ0 := D_of_sub_one hβ
      have hg0 : D p 0 (Gp (3 * (p : ℚ) ^ (s + 1)) (A * p ^ s + u)) :=
        ((hg.le (Nat.zero_le _)).add (hα0.mul0 hβ0)).congr (by ring)
      have hg3 : D p 3 (Gp (3 * (p : ℚ) ^ (s + 1)) (A * p ^ s + u) ^ 3 -
          Gp (3 * (p : ℚ) ^ (s + 1)) (A * p ^ s + 1) ^ 3 * Gp (3 * (p : ℚ) ^ (s + 1)) u ^ 3) :=
        (D_cube_sub hg0 (hα0.mul0 hβ0) hg).congr (by ring)
      have hxi : D p 0 ((((A * p ^ s + u : ℕ) : ℚ))⁻¹ ^ 3) := (D.inv hw).pow0 3
      have hxy : D p s ((((A * p ^ s + u : ℕ) : ℚ))⁻¹ ^ 3 - ((u : ℚ)⁻¹) ^ 3) := by
        apply D_inv_pow_congr hw hnd
        exact ((D.nat A).mul0' (D.ppow s)).congr (by push_cast; ring)
      have h1 : D p 1 (Gp (3 * (p : ℚ) ^ (s + 1)) (A * p ^ s + 1) ^ 3 *
          (((A * p ^ s + u : ℕ) : ℚ))⁻¹ ^ 3 - ((u : ℚ)⁻¹) ^ 3) :=
        ((hα3.mul0 hxi).add (hxy.le (by omega))).congr (by ring)
      exact (hg3.mul0 hxi).add (((D_cube_one hβ).mul h1).le (by omega))
    have h2 := ((hα3.mul hX).le (by omega : 3 ≤ 1 + 2)).add (D.sum _ _ hterm)
    exact h2.congr (block_identity (U p (p ^ s))
      (fun u => Gp (3 * (p : ℚ) ^ (s + 1)) (A * p ^ s + u))
      (fun u => Gp (3 * (p : ℚ) ^ (s + 1)) u ^ 3)
      (fun u => (((A * p ^ s + u : ℕ) : ℚ))⁻¹ ^ 3) (fun u => ((u : ℚ)⁻¹) ^ 3)
      (Gp (3 * (p : ℚ) ^ (s + 1)) (A * p ^ s + 1)))
  have hsum1 := D.sum _ _ hblock
  have hsg : D p 3 (sg p (p * p ^ s) 3) := by
    obtain ⟨_, h3⟩ := sg3 h5 hε (s := s + 1) (by omega)
    rw [← pow_succ']
    exact D.cancel (c := ε) (h3.le (by omega))
  have hsgb : sg p (p * p ^ s) 3 =
      ∑ A ∈ Finset.range p, ∑ u ∈ U p (p ^ s), (((A * p ^ s + u : ℕ) : ℚ))⁻¹ ^ 3 := by
    unfold sg
    rw [sum_U_blocks hpq]
  rw [hsgb] at hsg
  have hpZ : D p 3 (((Finset.range p).card : ℚ) *
      ∑ u ∈ U p (p ^ s), (Gp (3 * (p : ℚ) ^ (s + 1)) u ^ 3 - 1) * ((u : ℚ)⁻¹) ^ 3) := by
    rw [Finset.card_range]
    exact (((D.ppow 1).mul hZ2).le (by omega)).congr (by ring)
  have htot := (hsum1.add hsg).add hpZ
  rw [show p ^ (s + 1) = p * p ^ s from pow_succ' p s, sum_U_blocks hpq]
  exact htot.congr (sum_three (Finset.range p) _ _ _)
/-! ### the non-unit part: auxiliary sums -/

private lemma exists_eps (h5 : 5 ≤ p) : ∃ ε, Eps p ε := by
  by_cases h : p = 5
  · exact ⟨1, Or.inr ⟨rfl, h⟩⟩
  · refine ⟨0, Or.inl ⟨rfl, ?_⟩⟩
    intro hd
    have h15 : (15 : ℕ) = 3 * 5 := by norm_num
    rw [h15] at hd
    rcases (Nat.Prime.dvd_mul hp.out).mp hd with h1 | h1
    · have := Nat.le_of_dvd (by norm_num) h1
      omega
    · have := Nat.le_of_dvd (by norm_num) h1
      omega

private lemma sg1' (h5 : 5 ≤ p) {s : ℕ} (hs : 1 ≤ s) : D p (2 * s) (sg p (p ^ s) 1) := by
  have hp2 : ¬ p ∣ 2 := Nat.not_dvd_of_pos_of_lt (by norm_num) (by omega)
  obtain ⟨ε, hε⟩ := exists_eps (p := p) h5
  have hε1 := hε.le_one
  have h1 := sg1 h5 hε hs
  have h2 : D p (4 * s - ε) (2 * sg p (p ^ s) 1 + (p : ℚ) ^ s * sg p (p ^ s) 2) := by
    apply D.cancel (c := ε)
    rw [show 4 * s - ε + ε = 4 * s by omega]
    exact h1
  have h6 : D p (2 * s) (((2 : ℕ) : ℚ) * sg p (p ^ s) 1) := by
    have h7 := (h2.le (by omega : 2 * s ≤ 4 * s - ε)).sub
      (((D.ppow s).mul (sg2 h5 hs)).le (by omega : 2 * s ≤ s + s))
    exact h7.congr (by push_cast; ring)
  exact D.ucancel hp2 h6

omit hp in
private lemma sum_layers (hp0 : 0 < p) (n : ℕ) (f : ℕ → ℚ) :
    ∑ j ∈ Finset.range (p ^ n), f j =
      f 0 + ∑ e ∈ Finset.range n, ∑ u ∈ U p (p ^ (n - e)), f (u * p ^ e) := by
  induction n generalizing f with
  | zero => simp
  | succ n ih =>
    have h1 : ∑ j ∈ Finset.range (p ^ (n + 1)), f j =
        ∑ k ∈ U p (p ^ (n + 1)), f k + ∑ c ∈ Finset.range (p ^ n), f (p * c) := by
      rw [pow_succ']
      exact sum_range_mul_split p (p ^ n) hp0 f
    have h2 : ∀ e ∈ Finset.range n, ∑ u ∈ U p (p ^ (n - e)), f (p * (u * p ^ e)) =
        ∑ u ∈ U p (p ^ (n + 1 - (e + 1))), f (u * p ^ (e + 1)) := by
      intro e _
      rw [Nat.add_sub_add_right]
      refine Finset.sum_congr rfl fun u _ => ?_
      congr 1
      rw [pow_succ]
      ring
    have h3 := ih (fun j => f (p * j))
    rw [h1, h3, Finset.sum_range_succ', Finset.sum_congr rfl h2]
    simp only [mul_zero, pow_zero, mul_one, Nat.sub_zero]
    ring

omit hp in
private lemma sum_range_prime (hp0 : 0 < p) (f : ℕ → ℚ) :
    ∑ t ∈ Finset.range p, f t = f 0 + ∑ t ∈ U p (p ^ 1), f t := by
  have h := sum_range_mul_split p 1 hp0 f
  rw [Finset.sum_range_one, mul_one, mul_zero] at h
  unfold U
  rw [pow_one, h, add_comm]

/-- `Hh t = ∑_{0 < c < t} 1/c` -/
private def Hh (t : ℕ) : ℚ := ∑ c ∈ Finset.range t, (c : ℚ)⁻¹

private lemma Hh_e2 (n : ℕ) :
    ∑ t ∈ Finset.range n, Hh t * (t : ℚ)⁻¹ =
      (Hh n ^ 2 - ∑ t ∈ Finset.range n, (t : ℚ)⁻¹ ^ 2) / 2 := by
  induction n with
  | zero => simp [Hh]
  | succ n ih =>
    have h1 : Hh (n + 1) = Hh n + (n : ℚ)⁻¹ := by
      unfold Hh
      rw [Finset.sum_range_succ]
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ih, h1]
    ring

private lemma inv_D0_of_lt {c : ℕ} (hc : c < p) : D p 0 ((c : ℚ)⁻¹) := by
  rcases Nat.eq_zero_or_pos c with rfl | h0
  · exact (D.zero 0).congr (by simp)
  · exact D.inv (Nat.not_dvd_of_pos_of_lt h0 hc)

private lemma Hh_D0 {t : ℕ} (ht : t ≤ p) : D p 0 (Hh t) :=
  D.sum _ _ fun _ hc => inv_D0_of_lt (lt_of_lt_of_le (Finset.mem_range.mp hc) ht)

private lemma Gp_first (h5 : 5 ≤ p) {t : ℕ} (ht : t ≤ p) :
    D p 2 (Gp (3 * (p : ℚ) ^ 1) t - (1 - 3 * (p : ℚ) ^ 1 * Hh t)) := by
  have hp2 : ¬ p ∣ 2 := Nat.not_dvd_of_pos_of_lt (by norm_num) (by omega)
  have hx : D p 1 (3 * (p : ℚ) ^ 1) := D.three.mul0' (D.ppow 1)
  have hinv : ∀ c ∈ Finset.range t, D p 0 ((c : ℚ)⁻¹) :=
    fun c hc => inv_D0_of_lt (lt_of_lt_of_le (Finset.mem_range.mp hc) ht)
  obtain ⟨W, hW, hprod⟩ := prod_expand2 hp2 (Finset.range t) (fun c => (c : ℚ)⁻¹)
    (3 * (p : ℚ) ^ 1) (hx.le (Nat.zero_le _)) hinv
  have hG : Gp (3 * (p : ℚ) ^ 1) t =
      ∏ c ∈ Finset.range t, (1 - 3 * (p : ℚ) ^ 1 * (c : ℚ)⁻¹) := by
    unfold Gp
    simp only [div_eq_mul_inv]
  have h2i : D p 0 ((2 : ℚ)⁻¹) := by simpa using D.inv (p := p) hp2
  have hS1 : D p 0 (∑ c ∈ Finset.range t, (c : ℚ)⁻¹) := D.sum _ _ hinv
  have hS2 : D p 0 (∑ c ∈ Finset.range t, (c : ℚ)⁻¹ ^ 2) :=
    D.sum _ _ fun c hc => (hinv c hc).pow0 2
  have h7 := ((hx.pow 2).mul0 (((hS1.pow0 2).sub hS2).mul0 h2i)).add
    (((hx.pow 3).mul0 hW).le (by omega : 1 * 2 ≤ 1 * 3))
  refine h7.congr ?_
  rw [hG, hprod]
  unfold Hh
  ring

private lemma Gp_level (h5 : 5 ≤ p) {t : ℕ} (ht : t ≤ p) (n : ℕ) :
    D p 2 (Gp (3 * (p : ℚ) ^ (n + 1)) (t * p ^ n) - Gp (3 * (p : ℚ) ^ 1) t) := by
  have hp2 : ¬ p ∣ 2 := Nat.not_dvd_of_pos_of_lt (by norm_num) (by omega)
  obtain ⟨ε, hε⟩ := exists_eps (p := p) h5
  have hε1 := hε.le_one
  have h2i : D p 0 ((2 : ℚ)⁻¹) := by simpa using D.inv (p := p) hp2
  have hb0 : D p 0 (Gp (3 * (p : ℚ) ^ 1) t) :=
    D_of_sub_one (Gp_sub_one (m := 1) (c := 1) (by omega) (by rw [pow_one]; exact ht))
  induction n with
  | zero => exact (D.zero 2).congr (by simp)
  | succ n ih =>
    have hp0 : 0 < p := hp.out.pos
    have hP : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
    have e1 : Gp (3 * (p : ℚ) ^ (n + 1 + 1)) (t * p ^ (n + 1)) =
        R p (3 * (p : ℚ) ^ (n + 1 + 1)) (t * p ^ (n + 1)) *
          Gp (3 * (p : ℚ) ^ (n + 1)) (t * p ^ n) := by
      have h1 := Gp_split hp0 (3 * (p : ℚ) ^ (n + 1 + 1)) (t * p ^ n)
      have h2 : p * (t * p ^ n) = t * p ^ (n + 1) := by
        rw [pow_succ]
        ring
      have h3 : 3 * (p : ℚ) ^ (n + 1 + 1) / (p : ℚ) = 3 * (p : ℚ) ^ (n + 1) := by
        field_simp
        ring
      rw [h2, h3] at h1
      exact h1
    have hR := R_lemma h5 hε (r := n + 1 + 1) (s := n + 1) (by omega) t 2
      (by omega) (by omega) (by omega)
    have hM : D p 2 (3 / 2 * (p : ℚ) ^ (n + 1 + 1) * (t : ℚ) * sg p (p ^ (n + 1)) 2 *
        ((t : ℚ) * (p : ℚ) ^ (n + 1) - 3 * (p : ℚ) ^ (n + 1 + 1))) := by
      have h7 := ((((D.three.mul0 h2i).mul0' (D.ppow (n + 1 + 1))).mul0 (D.nat t)).mul0
        (sg_D0 (p ^ (n + 1)) 2)).mul0
        (((D.nat t).mul0 ((D.ppow (n + 1)).le (Nat.zero_le _))).sub
          (D.three.mul0 ((D.ppow (n + 1 + 1)).le (Nat.zero_le _))))
      exact (h7.le (by omega)).congr (by ring)
    have hR1 : D p 2 (R p (3 * (p : ℚ) ^ (n + 1 + 1)) (t * p ^ (n + 1)) - 1) :=
      (hR.add hM).congr (by ring)
    have hG0 : D p 0 (Gp (3 * (p : ℚ) ^ (n + 1)) (t * p ^ n)) :=
      ((ih.le (Nat.zero_le _)).add hb0).congr (by ring)
    rw [e1]
    exact ((hR1.mul0 hG0).add ih).congr (by ring)

/-- the layer `a = 1` sum -/
private lemma W_one (h5 : 5 ≤ p) (n : ℕ) :
    D p 2 (∑ t ∈ U p (p ^ 1), Gp (3 * (p : ℚ) ^ (n + 1)) (t * p ^ n) ^ 3 *
      ((t : ℚ)⁻¹ - 3 * (p : ℚ) ^ 1 * (t : ℚ)⁻¹ ^ 2)) := by
  have hp0 : 0 < p := hp.out.pos
  have hp2 : ¬ p ∣ 2 := Nat.not_dvd_of_pos_of_lt (by norm_num) (by omega)
  have h2i : D p 0 ((2 : ℚ)⁻¹) := by simpa using D.inv (p := p) hp2
  have hpp : D p 1 ((p : ℚ) ^ 1) := D.ppow 1
  have hpp0 : D p 0 ((p : ℚ) ^ 1) := hpp.le (Nat.zero_le _)
  have hterm : ∀ t ∈ U p (p ^ 1), D p 2
      (Gp (3 * (p : ℚ) ^ (n + 1)) (t * p ^ n) ^ 3 *
          ((t : ℚ)⁻¹ - 3 * (p : ℚ) ^ 1 * (t : ℚ)⁻¹ ^ 2) -
        ((t : ℚ)⁻¹ - 3 * (p : ℚ) ^ 1 * (t : ℚ)⁻¹ ^ 2 -
          9 * (p : ℚ) ^ 1 * (Hh t * (t : ℚ)⁻¹))) := by
    intro t ht
    obtain ⟨hlt, hnd⟩ := mem_U.mp ht
    rw [pow_one] at hlt
    have htp : t ≤ p := le_of_lt hlt
    have hti : D p 0 ((t : ℚ)⁻¹) := D.inv hnd
    have hH : D p 0 (Hh t) := Hh_D0 htp
    have hG : D p 2 (Gp (3 * (p : ℚ) ^ (n + 1)) (t * p ^ n) - (1 - 3 * (p : ℚ) ^ 1 * Hh t)) :=
      ((Gp_level h5 htp n).add (Gp_first h5 htp)).congr (by ring)
    have hL0 : D p 0 (1 - 3 * (p : ℚ) ^ 1 * Hh t) :=
      D.one.sub ((D.three.mul0 hpp0).mul0 hH)
    have hG0 : D p 0 (Gp (3 * (p : ℚ) ^ (n + 1)) (t * p ^ n)) :=
      ((hG.le (Nat.zero_le _)).add hL0).congr (by ring)
    have hG3 := D_cube_sub hG0 hL0 hG
    have hw : D p 0 ((t : ℚ)⁻¹ - 3 * (p : ℚ) ^ 1 * (t : ℚ)⁻¹ ^ 2) :=
      hti.sub ((D.three.mul0 hpp0).mul0 (hti.pow0 2))
    have h27 : D p 0 (27 : ℚ) := (D.nat (p := p) 27).congr (by norm_num)
    have hrem : D p 2 (((p : ℚ) ^ 1) ^ 2 * (27 * (Hh t * (t : ℚ)⁻¹ ^ 2 +
        (Hh t ^ 2 - (p : ℚ) ^ 1 * Hh t ^ 3) *
          ((t : ℚ)⁻¹ - 3 * (p : ℚ) ^ 1 * (t : ℚ)⁻¹ ^ 2)))) :=
      ((hpp.pow 2).mul0 (h27.mul0 ((hH.mul0 (hti.pow0 2)).add
        (((hH.pow0 2).sub (hpp0.mul0 (hH.pow0 3))).mul0 hw)))).le (by omega)
    exact ((hG3.mul0 hw).add hrem).congr (by ring)
  have hsum := D.sum _ _ hterm
  have hS : D p 2 (∑ t ∈ U p (p ^ 1), ((t : ℚ)⁻¹ - 3 * (p : ℚ) ^ 1 * (t : ℚ)⁻¹ ^ 2 -
      9 * (p : ℚ) ^ 1 * (Hh t * (t : ℚ)⁻¹))) := by
    have e : sg p (p ^ 1) 1 - 3 * (p : ℚ) ^ 1 * sg p (p ^ 1) 2 -
        ((9 : ℕ) : ℚ) * (p : ℚ) ^ 1 * ∑ t ∈ U p (p ^ 1), Hh t * (t : ℚ)⁻¹ =
        ∑ t ∈ U p (p ^ 1), ((t : ℚ)⁻¹ - 3 * (p : ℚ) ^ 1 * (t : ℚ)⁻¹ ^ 2 -
          9 * (p : ℚ) ^ 1 * (Hh t * (t : ℚ)⁻¹)) := by
      simp only [sg, Finset.sum_sub_distrib, Finset.mul_sum, pow_one, Nat.cast_ofNat]
    have hσ1 : D p 2 (sg p (p ^ 1) 1) := (sg1' h5 (le_refl 1)).le (by omega)
    have hσ2 : D p 1 (sg p (p ^ 1) 2) := sg2 h5 (le_refl 1)
    have hHt : D p 1 (∑ t ∈ U p (p ^ 1), Hh t * (t : ℚ)⁻¹) := by
      have h1 : ∑ t ∈ Finset.range p, Hh t * (t : ℚ)⁻¹ =
          ∑ t ∈ U p (p ^ 1), Hh t * (t : ℚ)⁻¹ := by
        rw [sum_range_prime hp0]
        simp
      have h2 : Hh p = sg p (p ^ 1) 1 := by
        unfold Hh sg
        rw [sum_range_prime hp0]
        simp
      have h3 : ∑ t ∈ Finset.range p, (t : ℚ)⁻¹ ^ 2 = sg p (p ^ 1) 2 := by
        unfold sg
        rw [sum_range_prime hp0]
        simp
      have h4 := Hh_e2 p
      rw [h1, h2, h3] at h4
      rw [h4]
      exact ((((hσ1.pow 2).le (by omega : 1 ≤ 2 * 2)).sub hσ2).mul0 h2i).congr (by ring)
    have h8 := (hσ1.sub (((D.three.mul0' hpp).mul hσ2).le (by omega : 2 ≤ 1 + 1))).sub
      ((((D.nat 9).mul0' hpp).mul hHt).le (by omega : 2 ≤ 1 + 1))
    exact h8.congr e
  refine (hsum.add hS).congr ?_
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun t _ => by ring
/-! ### the non-unit part: layers -/

private lemma choose_cube {a e u : ℕ} (hu : ¬ p ∣ u) :
    (-1 : ℚ) ^ (u * p ^ e) * ((3 * p ^ (e + a)).choose (u * p ^ e) : ℚ) ^ 3 =
      -(27 * ((p : ℚ) ^ a) ^ 3 * ((u : ℚ)⁻¹) ^ 3 *
        Gp (3 * (p : ℚ) ^ (e + a)) (u * p ^ e) ^ 3) := by
  have hu0 : (u : ℚ) ≠ 0 := by
    intro h0
    apply hu
    have h1 : u = 0 := by exact_mod_cast h0
    rw [h1]; exact dvd_zero p
  have hP : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
  have hj : 1 ≤ u * p ^ e :=
    Nat.mul_pos (Nat.pos_of_ne_zero (by rintro rfl; exact hu (dvd_zero p))) (pow_pos hp.out.pos e)
  have h1 := choose_mul_eq' (3 * p ^ (e + a)) (u * p ^ e) hj
  push_cast at h1
  have hs2 : ((-1 : ℚ) ^ (u * p ^ e)) ^ 2 = 1 := by
    rw [← pow_mul]
    exact Even.neg_one_pow ⟨u * p ^ e, by ring⟩
  have huu : (u : ℚ)⁻¹ * (u : ℚ) = 1 := inv_mul_cancel₀ hu0
  have hCe : ((3 * p ^ (e + a)).choose (u * p ^ e) : ℚ) =
      -(3 * (p : ℚ) ^ a * (u : ℚ)⁻¹ * (-1 : ℚ) ^ (u * p ^ e) *
        Gp (3 * (p : ℚ) ^ (e + a)) (u * p ^ e)) := by
    have hJ : ((u : ℚ) * (p : ℚ) ^ e) ≠ 0 := mul_ne_zero hu0 (pow_ne_zero _ hP)
    apply mul_right_cancel₀ hJ
    rw [h1]
    linear_combination (3 * (p : ℚ) ^ a * (p : ℚ) ^ e * (-1 : ℚ) ^ (u * p ^ e) *
      Gp (3 * (p : ℚ) ^ (e + a)) (u * p ^ e)) * huu
  rw [hCe]
  linear_combination (-27 * (((p : ℚ) ^ a) ^ 3 * ((u : ℚ)⁻¹) ^ 3 *
    Gp (3 * (p : ℚ) ^ (e + a)) (u * p ^ e) ^ 3) * (((-1 : ℚ) ^ (u * p ^ e)) ^ 2 + 1)) * hs2

/-- the weighted sum of a layer: in `D (3 - a)` -/
private lemma W_layer (h5 : 5 ≤ p) {a : ℕ} (ha : 1 ≤ a) (e : ℕ) :
    D p (3 - a) (∑ u ∈ U p (p ^ a), Gp (3 * (p : ℚ) ^ (e + a)) (u * p ^ e) ^ 3 *
      ((u : ℚ)⁻¹ - 3 * (p : ℚ) ^ a * (u : ℚ)⁻¹ ^ 2)) := by
  have hG1 : ∀ u ∈ U p (p ^ a), D p 1 (Gp (3 * (p : ℚ) ^ (e + a)) (u * p ^ e) - 1) := by
    intro u hu
    obtain ⟨hlt, _⟩ := mem_U.mp hu
    have hn : u * p ^ e ≤ p ^ (e + a) := by
      calc u * p ^ e ≤ p ^ a * p ^ e := Nat.mul_le_mul_right _ (le_of_lt hlt)
        _ = p ^ (e + a) := by rw [pow_add]; ring
    exact (Gp_sub_one (m := e + a) (c := e + a) (by omega) hn).le (by omega)
  have hw : ∀ u ∈ U p (p ^ a), D p 0 ((u : ℚ)⁻¹ - 3 * (p : ℚ) ^ a * (u : ℚ)⁻¹ ^ 2) := by
    intro u hu
    have hui : D p 0 ((u : ℚ)⁻¹) := D.inv (mem_U.mp hu).2
    exact hui.sub ((D.three.mul0 ((D.ppow a).le (Nat.zero_le _))).mul0 (hui.pow0 2))
  rcases Nat.lt_or_ge a 2 with h | h
  · obtain rfl : a = 1 := by omega
    exact (W_one h5 e).le (by omega)
  rcases Nat.lt_or_ge a 3 with h' | h'
  · obtain rfl : a = 2 := by omega
    have hterm : ∀ u ∈ U p (p ^ 2), D p 1
        (Gp (3 * (p : ℚ) ^ (e + 2)) (u * p ^ e) ^ 3 *
            ((u : ℚ)⁻¹ - 3 * (p : ℚ) ^ 2 * (u : ℚ)⁻¹ ^ 2) - (u : ℚ)⁻¹ ^ 1) := by
      intro u hu
      have hui : D p 0 ((u : ℚ)⁻¹) := D.inv (mem_U.mp hu).2
      have h7 := ((D_cube_one (hG1 u hu)).mul0 (hw u hu)).sub
        (((D.three.mul0' (D.ppow 2)).mul0 (hui.pow0 2)).le (by omega : 1 ≤ 2))
      exact h7.congr (by ring)
    have hσ1 : D p 1 (sg p (p ^ 2) 1) := (sg1' h5 (by omega : 1 ≤ 2)).le (by omega)
    refine (((D.sum _ _ hterm).add hσ1).le (by omega)).congr ?_
    unfold sg
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun u _ => by ring
  · refine (D.sum _ _ fun u hu => ?_).le (by omega : 3 - a ≤ 0)
    exact ((D_cube_one (hG1 u hu)).le (Nat.zero_le _) |> D_of_sub_one).mul0 (hw u hu)

private lemma layer (h5 : 5 ≤ p) {ε : ℕ} (hε : Eps p ε) {a e : ℕ} (ha : 1 ≤ a)
    (hρ : 1 + ε ≤ e + a) :
    D p (3 * (e + a) + 6) (∑ u ∈ U p (p ^ a),
      (-1 : ℚ) ^ (u * p ^ e) * ((3 * p ^ (e + a)).choose (u * p ^ e) : ℚ) ^ 3 *
        (R p (3 * (p : ℚ) ^ (e + a + 1)) (p * (u * p ^ e)) ^ 3 - 1)) := by
  have hp2 : ¬ p ∣ 2 := Nat.not_dvd_of_pos_of_lt (by norm_num) (by omega)
  have hε1 := hε.le_one
  have h2i : D p 0 ((2 : ℚ)⁻¹) := by simpa using D.inv (p := p) hp2
  have h27 : D p 0 (27 : ℚ) := (D.nat (p := p) 27).congr (by norm_num)
  have h243 : D p 0 ((243 : ℚ) * (2 : ℚ)⁻¹) :=
    ((D.nat (p := p) 243).congr (by norm_num)).mul0 h2i
  have hσ := sg2 h5 (s := e + 1) (by omega)
  have hW := W_layer h5 ha e
  have hterm : ∀ u ∈ U p (p ^ a), D p (3 * (e + a) + 6)
      ((-1 : ℚ) ^ (u * p ^ e) * ((3 * p ^ (e + a)).choose (u * p ^ e) : ℚ) ^ 3 *
          (R p (3 * (p : ℚ) ^ (e + a + 1)) (p * (u * p ^ e)) ^ 3 - 1) +
        (243 : ℚ) * (2 : ℚ)⁻¹ * (((p : ℚ) ^ a) ^ 3 * (p : ℚ) ^ (e + a + 1) * (p : ℚ) ^ (e + 1) *
            sg p (p ^ (e + 1)) 2) *
          (Gp (3 * (p : ℚ) ^ (e + a)) (u * p ^ e) ^ 3 *
            ((u : ℚ)⁻¹ - 3 * (p : ℚ) ^ a * (u : ℚ)⁻¹ ^ 2))) := by
    intro u hu
    obtain ⟨hlt, hnd⟩ := mem_U.mp hu
    have hu0 : (u : ℚ) ≠ 0 := by
      intro h0
      apply hnd
      have h1 : u = 0 := by exact_mod_cast h0
      rw [h1]; exact dvd_zero p
    have huu : (u : ℚ)⁻¹ * (u : ℚ) = 1 := inv_mul_cancel₀ hu0
    have hui : D p 0 ((u : ℚ)⁻¹) := D.inv hnd
    have hn : u * p ^ e ≤ p ^ (e + a) := by
      calc u * p ^ e ≤ p ^ a * p ^ e := Nat.mul_le_mul_right _ (le_of_lt hlt)
        _ = p ^ (e + a) := by rw [pow_add]; ring
    have hG0 : D p 0 (Gp (3 * (p : ℚ) ^ (e + a)) (u * p ^ e)) :=
      D_of_sub_one (Gp_sub_one (m := e + a) (c := e + a) (by omega) hn)
    rw [choose_cube (a := a) (e := e) hnd,
      show p * (u * p ^ e) = u * p ^ (e + 1) by rw [pow_succ]; ring]
    have hRl := R_lemma h5 hε (r := e + a + 1) (s := e + 1) (by omega) u (3 * e + 6)
      (by omega) (by omega) (by omega)
    have hd : D p (e + 1) ((u : ℚ) * (p : ℚ) ^ (e + 1) - 3 * (p : ℚ) ^ (e + a + 1)) :=
      ((D.nat u).mul0' (D.ppow (e + 1))).sub
        ((D.three.mul0' (D.ppow (e + a + 1))).le (by omega))
    have hM : D p (3 * e + 4) (3 / 2 * (p : ℚ) ^ (e + a + 1) * (u : ℚ) * sg p (p ^ (e + 1)) 2 *
        ((u : ℚ) * (p : ℚ) ^ (e + 1) - 3 * (p : ℚ) ^ (e + a + 1))) := by
      have h7 := ((((D.three.mul0 h2i).mul0' (D.ppow (e + a + 1))).mul0 (D.nat u)).mul hσ).mul hd
      exact (h7.le (by omega)).congr (by ring)
    have hX : D p (3 * e + 4) (R p (3 * (p : ℚ) ^ (e + a + 1)) (u * p ^ (e + 1)) - 1) :=
      ((hRl.le (by omega)).add hM).congr (by ring)
    have hX0 : D p 0 (R p (3 * (p : ℚ) ^ (e + a + 1)) (u * p ^ (e + 1)) - 1) :=
      hX.le (Nat.zero_le _)
    have hcube : D p (3 * e + 6) (R p (3 * (p : ℚ) ^ (e + a + 1)) (u * p ^ (e + 1)) ^ 3 - 1 -
        3 * (3 / 2 * (p : ℚ) ^ (e + a + 1) * (u : ℚ) * sg p (p ^ (e + 1)) 2 *
          ((u : ℚ) * (p : ℚ) ^ (e + 1) - 3 * (p : ℚ) ^ (e + a + 1)))) := by
      have h7 := (D.three.mul0' hRl).add
        (((hX.pow 2).mul0 (D.three.add hX0)).le (by omega : 3 * e + 6 ≤ (3 * e + 4) * 2))
      exact h7.congr (by ring)
    have hCf : D p (3 * a) (27 * ((p : ℚ) ^ a) ^ 3 * ((u : ℚ)⁻¹) ^ 3 *
        Gp (3 * (p : ℚ) ^ (e + a)) (u * p ^ e) ^ 3) :=
      (((h27.mul0' ((D.ppow a).pow 3)).mul0 (hui.pow0 3)).mul0 (hG0.pow0 3)).le (by omega)
    have h9 := (hCf.mul hcube).neg
    refine (h9.le (by omega)).congr ?_
    linear_combination (243 / 2 * ((p : ℚ) ^ a) ^ 3 *
      Gp (3 * (p : ℚ) ^ (e + a)) (u * p ^ e) ^ 3 * (p : ℚ) ^ (e + a + 1) * sg p (p ^ (e + 1)) 2 *
      ((p : ℚ) ^ (e + 1) * (u : ℚ)⁻¹ * ((u : ℚ)⁻¹ * (u : ℚ) + 1) -
        3 * (p : ℚ) ^ (e + 1) * (p : ℚ) ^ a * ((u : ℚ)⁻¹) ^ 2)) * huu
  have hK : D p (4 * a + 3 * e + 3) (((p : ℚ) ^ a) ^ 3 * (p : ℚ) ^ (e + a + 1) *
      (p : ℚ) ^ (e + 1) * sg p (p ^ (e + 1)) 2) :=
    (((((D.ppow a).pow 3).mul (D.ppow (e + a + 1))).mul (D.ppow (e + 1))).mul hσ).le (by omega)
  have h8 := (D.sum _ _ hterm).sub ((h243.mul0' (hK.mul hW)).le (by omega))
  refine h8.congr ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

private lemma nonunit_part (h5 : 5 ≤ p) {ε : ℕ} (hε : Eps p ε) {ρ : ℕ} (hρ : 1 + ε ≤ ρ) :
    D p (3 * ρ + 6) (∑ j ∈ Finset.range (p ^ ρ),
      (-1 : ℚ) ^ j * ((3 * p ^ ρ).choose j : ℚ) ^ 3 *
        (R p (3 * (p : ℚ) ^ (ρ + 1)) (p * j) ^ 3 - 1)) := by
  rw [sum_layers hp.out.pos]
  have h0 : (-1 : ℚ) ^ 0 * ((3 * p ^ ρ).choose 0 : ℚ) ^ 3 *
      (R p (3 * (p : ℚ) ^ (ρ + 1)) (p * 0) ^ 3 - 1) = 0 := by
    simp [R, U]
  rw [h0, zero_add]
  apply D.sum
  intro e he
  have he' := Finset.mem_range.mp he
  obtain ⟨a, rfl⟩ : ∃ a, ρ = e + a := ⟨ρ - e, by omega⟩
  rw [Nat.add_sub_cancel_left]
  exact layer h5 hε (by omega) hρ

/-! ### assembly -/

private lemma main_general (h5 : 5 ≤ p) {ε : ℕ} (hε : Eps p ε) {r : ℕ} (hr : 2 + ε ≤ r) :
    ((p : ℤ) ^ (3 * r + 3)) ∣
      (OMA.S_oeis_a375180.a (p ^ r) - OMA.S_oeis_a375180.a (p ^ (r - 1))) := by
  obtain ⟨ρ, rfl⟩ : ∃ ρ, r = ρ + 1 := ⟨r - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  have hp0 : 0 < p := hp.out.pos
  have hp2 : p ≠ 2 := by omega
  have hodd : Odd p := hp.out.odd_of_ne_two hp2
  have ha : ∀ n : ℕ, Odd n → ((OMA.S_oeis_a375180.a n : ℤ) : ℚ) =
      ∑ k ∈ Finset.range n, (-1 : ℚ) ^ k * ((3 * n).choose k : ℚ) ^ 3 := by
    intro n hn
    unfold OMA.S_oeis_a375180.a
    push_cast
    refine Finset.sum_congr rfl fun k _ => ?_
    have he : Even (n + 1) := hn.add_one
    rw [show n + k + 1 = (n + 1) + k by ring, pow_add, he.neg_one_pow, one_mul]
  apply D.dvd
  push_cast
  rw [ha _ hodd.pow, ha _ hodd.pow]
  have hsplit := sum_range_mul_split p (p ^ ρ) hp0
    (fun k => (-1 : ℚ) ^ k * ((3 * p ^ (ρ + 1)).choose k : ℚ) ^ 3)
  rw [← pow_succ'] at hsplit
  rw [hsplit]
  have hunit : D p (3 * ρ + 6) (∑ k ∈ (Finset.range (p ^ (ρ + 1))).filter (fun k => ¬ p ∣ k),
      (-1 : ℚ) ^ k * ((3 * p ^ (ρ + 1)).choose k : ℚ) ^ 3) := by
    have h1 := unit_part h5 hε (s := ρ) (by omega)
    have h27 : D p 0 (27 : ℚ) := (D.nat (p := p) 27).congr (by norm_num)
    have h2 := ((h27.mul0' ((D.ppow (ρ + 1)).pow 3)).mul h1).neg
    refine (h2.le (by omega)).congr ?_
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' := (mem_U.mp hk).2
    have h3 := choose_cube (p := p) (a := ρ + 1) (e := 0) hk'
    simp only [pow_zero, mul_one, zero_add] at h3
    rw [h3]
    ring
  have hnon := nonunit_part h5 hε (ρ := ρ) (by omega)
  have htot := hunit.add hnon
  refine (htot.le (by omega)).congr ?_
  rw [add_sub_assoc, ← Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  have h4 := choose_ratio (p := p) hp2 (3 * p ^ ρ) j
  have h5' : p * (3 * p ^ ρ) = 3 * p ^ (ρ + 1) := by
    rw [pow_succ]
    ring
  rw [h5'] at h4
  have h6 : (-1 : ℚ) ^ (p * j) = (-1) ^ j := by
    rw [pow_mul, hodd.neg_one_pow]
  rw [h4, h6]
  push_cast
  ring

private lemma case_5_2 : (((5 : ℕ) : ℤ) ^ (3 * 2 + 3)) ∣
    (OMA.S_oeis_a375180.a (5 ^ 2) - OMA.S_oeis_a375180.a (5 ^ (2 - 1))) := by
  unfold OMA.S_oeis_a375180.a
  simp only [Nat.choose_eq_descFactorial_div_factorial]
  decide +kernel

/-! ### general odd exponent: more power sums -/

private lemma D_pow_sub {e : ℕ} {x y : ℚ} (hx : D p 0 x) (hy : D p 0 y) (h : D p e (x - y))
    (j : ℕ) : D p e (x ^ j - y ^ j) := by
  induction j with
  | zero => exact (D.zero e).congr (by simp)
  | succ j ih => exact ((hx.mul0' ih).add (h.mul0 (hy.pow0 j))).congr (by ring)

private lemma binom1 {k : ℕ} {Y : ℚ} (h : D p k (Y - 1)) (d : ℕ) :
    D p (2 * k) (Y ^ d - 1 - (d : ℚ) * (Y - 1)) := by
  have hY0 : D p 0 Y := D_of_sub_one h
  induction d with
  | zero => exact (D.zero _).congr (by simp)
  | succ d ih =>
    have h7 := (hY0.mul0' ih).add (((D.nat d).mul0' (h.pow 2)).le (by omega : 2 * k ≤ k * 2))
    exact h7.congr (by push_cast; ring)

private lemma exp_gen {s : ℕ} {u v a : ℚ} (hu0 : u ≠ 0) (hv0 : v ≠ 0) (h : v = u + a)
    (hu : D p 0 u⁻¹) (hv : D p 0 v⁻¹) (ha : D p s a) (j : ℕ) :
    D p (2 * s) (v⁻¹ ^ j - u⁻¹ ^ j + (j : ℚ) * a * u⁻¹ ^ (j + 1)) := by
  have hr : v⁻¹ - u⁻¹ + a * u⁻¹ * v⁻¹ = 0 := by
    subst h
    field_simp
    ring
  have hVU : D p s (v⁻¹ - u⁻¹) :=
    ((ha.mul0 hu).mul0 hv).neg.congr (by linear_combination (-1 : ℚ) * hr)
  induction j with
  | zero => exact (D.zero _).congr (by simp)
  | succ j ih =>
    have h7 := (hv.mul0' ih).sub
      (((((D.nat (j + 1)).mul0' ha).mul0 (hu.pow0 (j + 1))).mul hVU).le
        (by omega : 2 * s ≤ s + s))
    refine h7.congr ?_
    push_cast
    linear_combination (-(u⁻¹ ^ j)) * hr

private lemma sg_refl2 {s : ℕ} (hs : 1 ≤ s) {j : ℕ} (hj : Odd j) :
    D p (2 * s) (2 * sg p (p ^ s) j + (j : ℚ) * (p : ℚ) ^ s * sg p (p ^ s) (j + 1)) := by
  have hpq : p ∣ p ^ s := dvd_pow_self p (by omega)
  have hterm : ∀ u ∈ U p (p ^ s), D p (2 * s)
      ((((p ^ s - u : ℕ) : ℚ)⁻¹) ^ j + ((u : ℚ)⁻¹) ^ j +
        (j : ℚ) * (p : ℚ) ^ s * ((u : ℚ)⁻¹) ^ (j + 1)) := by
    intro u hu
    obtain ⟨hlt, hnd⟩ := mem_U.mp hu
    have hw : ¬ p ∣ p ^ s - u := by
      intro hd
      have h1 : p ^ s - u + u = p ^ s := Nat.sub_add_cancel (le_of_lt hlt)
      have h2 : p ∣ p ^ s - u + u := by rw [h1]; exact hpq
      exact hnd ((Nat.dvd_add_right hd).mp h2)
    have hw0 : ((p ^ s - u : ℕ) : ℚ) ≠ 0 := by
      have h1 : p ^ s - u ≠ 0 := by omega
      exact_mod_cast h1
    have hu0 : (u : ℚ) ≠ 0 := by
      intro h0
      apply hnd
      have h1 : u = 0 := by exact_mod_cast h0
      rw [h1]; exact dvd_zero p
    have hv : (-(((p ^ s - u : ℕ) : ℚ))) = (u : ℚ) + (-(p : ℚ) ^ s) := by
      rw [Nat.cast_sub (le_of_lt hlt)]
      push_cast
      ring
    have hvi : D p 0 (-(((p ^ s - u : ℕ) : ℚ)))⁻¹ := by
      rw [inv_neg]
      exact (D.inv hw).neg
    have hE := exp_gen hu0 (neg_ne_zero.mpr hw0) hv (D.inv hnd) hvi (D.ppow s).neg j
    refine hE.neg.congr ?_
    rw [inv_neg, Odd.neg_pow hj]
    ring
  have h := D.sum _ _ hterm
  refine h.congr ?_
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  have hr := sum_U_reflect hpq (fun w => (w : ℚ)⁻¹ ^ j)
  simp only [sg]
  rw [← hr]
  ring

private lemma sg_odd (h5 : 5 ≤ p) {s : ℕ} (hs : 1 ≤ s) {j : ℕ} (hj : Odd j) :
    D p s (sg p (p ^ s) j) := by
  have hp2 : ¬ p ∣ 2 := Nat.not_dvd_of_pos_of_lt (by norm_num) (by omega)
  have h1 := sg_refl2 (p := p) hs hj
  have h6 : D p s (((2 : ℕ) : ℚ) * sg p (p ^ s) j) := by
    have h7 := (h1.le (by omega : s ≤ 2 * s)).sub
      (((D.nat j).mul0' (D.ppow s)).mul0 (sg_D0 (p ^ s) (j + 1)))
    exact h7.congr (by push_cast; ring)
  exact D.ucancel hp2 h6

omit hp in
private lemma sum_U_scale {q g : ℕ} (hp' : p.Prime) (hg : ¬ p ∣ g) (hpq : p ∣ q)
    (hq : Nat.Coprime q g) (f : ℕ → ℚ) :
    ∑ u ∈ U p q, f (g * u % q) = ∑ u ∈ U p q, f u := by
  have hinj : Set.InjOn (fun u => g * u % q) (U p q : Set ℕ) := by
    intro u hu v hv h
    have hu' := mem_U.mp (Finset.mem_coe.mp hu)
    have hv' := mem_U.mp (Finset.mem_coe.mp hv)
    have h1 : g * u ≡ g * v [MOD q] := h
    have h2 : u ≡ v [MOD q] := Nat.ModEq.cancel_left_of_coprime hq h1
    exact Nat.ModEq.eq_of_lt_of_lt h2 hu'.1 hv'.1
  have himg : (U p q).image (fun u => g * u % q) = U p q := by
    apply Finset.eq_of_subset_of_card_le
    · intro w hw
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hw
      have hu' := mem_U.mp hu
      have hq0 : 0 < q := by omega
      refine mem_U.mpr ⟨Nat.mod_lt _ hq0, ?_⟩
      intro hd
      have h3 : p ∣ g * u := (Nat.dvd_mod_iff hpq).mp hd
      rcases (Nat.Prime.dvd_mul hp').mp h3 with h4 | h4
      · exact hg h4
      · exact hu'.2 h4
    · rw [Finset.card_image_of_injOn hinj]
  calc ∑ u ∈ U p q, f (g * u % q)
      = ∑ w ∈ (U p q).image (fun u => g * u % q), f w := by
        rw [Finset.sum_image hinj]
    _ = ∑ u ∈ U p q, f u := by rw [himg]

private lemma sg_scale_g {g : ℕ} (hg : ¬ p ∣ g) {s : ℕ} (hs : 1 ≤ s) (j : ℕ) :
    D p s (((g : ℚ) ^ j - 1) * sg p (p ^ s) j) := by
  have hpq : p ∣ p ^ s := dvd_pow_self p (by omega)
  have hqg : Nat.Coprime (p ^ s) g :=
    Nat.Coprime.pow_left s ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hg)
  have hg0 : (g : ℚ) ≠ 0 := by
    intro h0
    apply hg
    have h1 : g = 0 := by exact_mod_cast h0
    rw [h1]; exact dvd_zero p
  have h1 : sg p (p ^ s) j = ∑ u ∈ U p (p ^ s), (((g * u % p ^ s : ℕ) : ℚ)⁻¹) ^ j := by
    unfold sg
    exact (sum_U_scale hp.out hg hpq hqg (fun w => ((w : ℚ)⁻¹) ^ j)).symm
  have h2 : D p s (∑ u ∈ U p (p ^ s),
      ((((g * u % p ^ s : ℕ) : ℚ)⁻¹) ^ j - (((g * u : ℕ) : ℚ)⁻¹) ^ j)) := by
    apply D.sum
    intro u hu
    have hu' := mem_U.mp hu
    have h2u : ¬ p ∣ g * u := by
      intro hd
      rcases (Nat.Prime.dvd_mul hp.out).mp hd with h4 | h4
      · exact hg h4
      · exact hu'.2 h4
    have hmod : ¬ p ∣ g * u % p ^ s := fun hd => h2u ((Nat.dvd_mod_iff hpq).mp hd)
    apply D_inv_pow_congr hmod h2u
    have h5 : ((g * u % p ^ s : ℕ) : ℚ) - ((g * u : ℕ) : ℚ) =
        -((p : ℚ) ^ s * ((g * u / p ^ s : ℕ) : ℚ)) := by
      have h6 := Nat.div_add_mod (g * u) (p ^ s)
      have h7 : ((p ^ s * (g * u / p ^ s) + g * u % p ^ s : ℕ) : ℚ) = ((g * u : ℕ) : ℚ) := by
        rw [h6]
      push_cast at h7 ⊢
      linarith
    rw [h5]
    exact ((D.ppow s).mul0 (D.nat _)).neg
  rw [Finset.sum_sub_distrib, ← h1] at h2
  have h3 : ∑ u ∈ U p (p ^ s), (((g * u : ℕ) : ℚ)⁻¹) ^ j = ((g : ℚ)⁻¹) ^ j * sg p (p ^ s) j := by
    unfold sg
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    push_cast
    rw [mul_inv, mul_pow]
  rw [h3] at h2
  have h4 : (g : ℚ) ^ j * (sg p (p ^ s) j - ((g : ℚ)⁻¹) ^ j * sg p (p ^ s) j) =
      ((g : ℚ) ^ j - 1) * sg p (p ^ s) j := by
    have h5 : (g : ℚ) ^ j * ((g : ℚ)⁻¹) ^ j = 1 := by
      rw [← mul_pow, mul_inv_cancel₀ hg0, one_pow]
    linear_combination (-sg p (p ^ s) j) * h5
  exact (((D.nat g).pow0 j).mul0' h2).congr h4

private lemma exists_prim {j : ℕ} (hj0 : 0 < j) (hj : j < p - 1) :
    ∃ g : ℕ, ¬ p ∣ g ∧ ¬ p ∣ (g ^ j - 1) := by
  obtain ⟨γ, hγ⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
  have hord : orderOf γ = p - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hγ, Nat.card_eq_fintype_card, ZMod.card_units]
  have hγj : (γ ^ j : (ZMod p)ˣ) ≠ 1 := by
    intro h
    have hdvd := orderOf_dvd_of_pow_eq_one h
    rw [hord] at hdvd
    have := Nat.le_of_dvd hj0 hdvd
    omega
  refine ⟨(γ : ZMod p).val, ?_, ?_⟩
  · intro hd
    have h0 : (((γ : ZMod p).val : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hd
    rw [ZMod.natCast_zmod_val] at h0
    exact γ.ne_zero h0
  · intro hd
    have hpos : 1 ≤ (γ : ZMod p).val ^ j :=
      Nat.one_le_pow _ _ (Nat.pos_of_ne_zero (by
        intro h0
        exact γ.ne_zero ((ZMod.val_eq_zero _).mp h0)))
    have h0 : (((γ : ZMod p).val ^ j - 1 : ℕ) : ZMod p) = 0 :=
      (ZMod.natCast_eq_zero_iff _ _).mpr hd
    rw [Nat.cast_sub hpos] at h0
    push_cast at h0
    rw [ZMod.natCast_zmod_val] at h0
    apply hγj
    apply Units.ext
    push_cast
    exact sub_eq_zero.mp h0

private lemma sg_small {j : ℕ} (hj0 : 0 < j) (hj : j < p - 1) : D p 1 (sg p (p ^ 1) j) := by
  obtain ⟨g, hg, hgj⟩ := exists_prim (p := p) hj0 hj
  have h := sg_scale_g hg (le_refl 1) j
  have hpos : 1 ≤ g ^ j :=
    Nat.one_le_pow _ _ (Nat.pos_of_ne_zero (by rintro rfl; exact hg (dvd_zero p)))
  have hc : (g : ℚ) ^ j - 1 = ((g ^ j - 1 : ℕ) : ℚ) := by
    rw [Nat.cast_sub hpos]
    push_cast
    ring
  rw [hc] at h
  exact D.ucancel hgj h

private lemma inv_refl {c : ℕ} (hc0 : 0 < c) (hc : c < p) :
    D p 1 (((p - c : ℕ) : ℚ)⁻¹ + (c : ℚ)⁻¹) := by
  have hX : (c : ℚ) ≠ 0 := by positivity
  have hY : ((p - c : ℕ) : ℚ) ≠ 0 := by
    have h1 : p - c ≠ 0 := by omega
    exact_mod_cast h1
  have hXX := mul_inv_cancel₀ hX
  have hYY := mul_inv_cancel₀ hY
  have hsum : (c : ℚ) + ((p - c : ℕ) : ℚ) = (p : ℚ) := by
    rw [Nat.cast_sub (le_of_lt hc)]
    ring
  have e : (p : ℚ) ^ 1 * ((c : ℚ)⁻¹ * ((p - c : ℕ) : ℚ)⁻¹) =
      ((p - c : ℕ) : ℚ)⁻¹ + (c : ℚ)⁻¹ := by
    rw [pow_one, ← hsum]
    linear_combination ((p - c : ℕ) : ℚ)⁻¹ * hXX + (c : ℚ)⁻¹ * hYY
  exact ((D.ppow 1).mul0 (((D.inv (Nat.not_dvd_of_pos_of_lt hc0 hc)).mul
    (D.inv (Nat.not_dvd_of_pos_of_lt (by omega : 0 < p - c) (by omega : p - c < p)))).le
      (Nat.zero_le _))).congr e

private lemma Hh_succ (n : ℕ) : Hh (n + 1) = Hh n + (n : ℚ)⁻¹ := by
  unfold Hh
  rw [Finset.sum_range_succ]

private lemma Hh_pair (h5 : 5 ≤ p) {t : ℕ} (ht : t < p) :
    D p 1 (Hh (p - t) - Hh t - (t : ℚ)⁻¹) := by
  induction t with
  | zero =>
    have h2 : Hh p = sg p (p ^ 1) 1 := by
      unfold Hh sg
      rw [sum_range_prime hp.out.pos]
      simp
    have h1 : D p 1 (Hh p) := by
      rw [h2]
      exact (sg1' h5 (le_refl 1)).le (by omega)
    exact h1.congr (by simp [Hh])
  | succ t ih =>
    have ih' := ih (by omega)
    have e1 : Hh (p - t) = Hh (p - (t + 1)) + ((p - (t + 1) : ℕ) : ℚ)⁻¹ := by
      rw [← Hh_succ]
      congr 1
      omega
    have h7 := ih'.sub (inv_refl (c := t + 1) (by omega) ht)
    refine h7.congr ?_
    rw [e1, Hh_succ t]
    push_cast
    ring

private lemma Hh_sum_odd (h5 : 5 ≤ p) {j : ℕ} (hj : Odd j) (hj1 : j + 1 < p - 1) :
    D p 1 (∑ t ∈ U p (p ^ 1), Hh t * ((t : ℚ)⁻¹) ^ j) := by
  have hp2 : ¬ p ∣ 2 := Nat.not_dvd_of_pos_of_lt (by norm_num) (by omega)
  have hpq : p ∣ p ^ 1 := dvd_pow_self p (by norm_num)
  have hσ := sg_small (p := p) (j := j + 1) (by omega) hj1
  have hr := sum_U_reflect hpq (fun t => Hh t * ((t : ℚ)⁻¹) ^ j)
  have hterm : ∀ t ∈ U p (p ^ 1), D p 1
      (Hh (p ^ 1 - t) * (((p ^ 1 - t : ℕ) : ℚ)⁻¹) ^ j + Hh t * ((t : ℚ)⁻¹) ^ j +
        ((t : ℚ)⁻¹) ^ (j + 1)) := by
    intro t ht
    obtain ⟨hlt, hnd⟩ := mem_U.mp ht
    rw [pow_one] at hlt ⊢
    have ht0 : 0 < t := Nat.pos_of_ne_zero (by rintro rfl; exact hnd (dvd_zero p))
    have hW : D p 0 (((p - t : ℕ) : ℚ)⁻¹) :=
      D.inv (Nat.not_dvd_of_pos_of_lt (by omega : 0 < p - t) (by omega : p - t < p))
    have hT : D p 0 ((t : ℚ)⁻¹) := D.inv hnd
    have hH := Hh_pair h5 hlt
    have hHt : D p 0 (Hh t) := Hh_D0 (le_of_lt hlt)
    have hWT := inv_refl ht0 hlt
    have hWj : D p 1 (((p - t : ℕ) : ℚ)⁻¹ ^ j + ((t : ℚ)⁻¹) ^ j) := by
      have h1 := D_pow_sub hW hT.neg (hWT.congr (by ring)) j
      refine h1.congr ?_
      rw [Odd.neg_pow hj]
      ring
    have h7 := (hH.mul0 (hW.pow0 j)).add ((hHt.add hT).mul0' hWj)
    exact h7.congr (by ring)
  have h := D.sum _ _ hterm
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← hr] at h
  have h6 : D p 1 (((2 : ℕ) : ℚ) * ∑ t ∈ U p (p ^ 1), Hh t * ((t : ℚ)⁻¹) ^ j) := by
    refine (h.sub hσ).congr ?_
    unfold sg
    push_cast
    ring
  exact D.ucancel hp2 h6
/-! ### general odd exponent `2k+3`: layers, units, assembly -/

private lemma eps_zero (h7 : 7 ≤ p) : Eps p 0 := by
  refine Or.inl ⟨rfl, ?_⟩
  intro hd
  have h15 : (15 : ℕ) = 3 * 5 := by norm_num
  rw [h15] at hd
  rcases (Nat.Prime.dvd_mul hp.out).mp hd with h1 | h1
  · have := Nat.le_of_dvd (by norm_num) h1
    omega
  · have := Nat.le_of_dvd (by norm_num) h1
    omega

/-- the layer `a = 1` sum for the exponent `2k+3` -/
private lemma W_one_d (k : ℕ) (hp7 : 2 * k + 7 ≤ p) (n : ℕ) :
    D p 2 (∑ t ∈ U p (p ^ 1), Gp (3 * (p : ℚ) ^ (n + 1)) (t * p ^ n) ^ (2 * k + 3) *
      (((t : ℚ)⁻¹) ^ (2 * k + 1) - 3 * (p : ℚ) ^ 1 * ((t : ℚ)⁻¹) ^ (2 * k + 2))) := by
  have h5 : 5 ≤ p := by omega
  have hp2 : ¬ p ∣ 2 := Nat.not_dvd_of_pos_of_lt (by norm_num) (by omega)
  have hpp : D p 1 ((p : ℚ) ^ 1) := D.ppow 1
  have hpp0 : D p 0 ((p : ℚ) ^ 1) := hpp.le (Nat.zero_le _)
  have hodd : Odd (2 * k + 1) := ⟨k, rfl⟩
  have h9 : D p 0 (9 : ℚ) := (D.nat (p := p) 9).congr (by norm_num)
  have hterm : ∀ t ∈ U p (p ^ 1), D p 2
      (Gp (3 * (p : ℚ) ^ (n + 1)) (t * p ^ n) ^ (2 * k + 3) *
          (((t : ℚ)⁻¹) ^ (2 * k + 1) - 3 * (p : ℚ) ^ 1 * ((t : ℚ)⁻¹) ^ (2 * k + 2)) -
        (((t : ℚ)⁻¹) ^ (2 * k + 1) - 3 * (p : ℚ) ^ 1 * ((t : ℚ)⁻¹) ^ (2 * k + 2) -
          3 * ((2 * k + 3 : ℕ) : ℚ) * (p : ℚ) ^ 1 * (Hh t * ((t : ℚ)⁻¹) ^ (2 * k + 1)))) := by
    intro t ht
    obtain ⟨hlt, hnd⟩ := mem_U.mp ht
    rw [pow_one] at hlt
    have htp : t ≤ p := le_of_lt hlt
    have hti : D p 0 ((t : ℚ)⁻¹) := D.inv hnd
    have hH : D p 0 (Hh t) := Hh_D0 htp
    have hG : D p 2 (Gp (3 * (p : ℚ) ^ (n + 1)) (t * p ^ n) - (1 - 3 * (p : ℚ) ^ 1 * Hh t)) :=
      ((Gp_level h5 htp n).add (Gp_first h5 htp)).congr (by ring)
    have hL0 : D p 0 (1 - 3 * (p : ℚ) ^ 1 * Hh t) :=
      D.one.sub ((D.three.mul0 hpp0).mul0 hH)
    have hG0 : D p 0 (Gp (3 * (p : ℚ) ^ (n + 1)) (t * p ^ n)) :=
      ((hG.le (Nat.zero_le _)).add hL0).congr (by ring)
    have hGd := D_pow_sub hG0 hL0 hG (2 * k + 3)
    have hL1 : D p 1 ((1 - 3 * (p : ℚ) ^ 1 * Hh t) - 1) :=
      ((D.three.mul0' hpp).mul0 hH).neg.congr (by ring)
    have hLd := binom1 hL1 (2 * k + 3)
    have hw : D p 0 (((t : ℚ)⁻¹) ^ (2 * k + 1) -
        3 * (p : ℚ) ^ 1 * ((t : ℚ)⁻¹) ^ (2 * k + 2)) :=
      (hti.pow0 _).sub ((D.three.mul0 hpp0).mul0 (hti.pow0 _))
    have hrem : D p 2 (((p : ℚ) ^ 1) ^ 2 * (9 * ((2 * k + 3 : ℕ) : ℚ) *
        (Hh t * ((t : ℚ)⁻¹) ^ (2 * k + 2)))) :=
      ((hpp.pow 2).mul0 ((h9.mul0 (D.nat _)).mul0 (hH.mul0 (hti.pow0 _)))).le (by omega)
    have h7 := ((hGd.add (hLd.le (by omega))).mul0 hw).add hrem
    exact h7.congr (by ring)
  have hsum := D.sum _ _ hterm
  have hS : D p 2 (∑ t ∈ U p (p ^ 1), (((t : ℚ)⁻¹) ^ (2 * k + 1) -
      3 * (p : ℚ) ^ 1 * ((t : ℚ)⁻¹) ^ (2 * k + 2) -
      3 * ((2 * k + 3 : ℕ) : ℚ) * (p : ℚ) ^ 1 * (Hh t * ((t : ℚ)⁻¹) ^ (2 * k + 1)))) := by
    have e : sg p (p ^ 1) (2 * k + 1) - 3 * (p : ℚ) ^ 1 * sg p (p ^ 1) (2 * k + 2) -
        3 * ((2 * k + 3 : ℕ) : ℚ) * (p : ℚ) ^ 1 *
          ∑ t ∈ U p (p ^ 1), Hh t * ((t : ℚ)⁻¹) ^ (2 * k + 1) =
        ∑ t ∈ U p (p ^ 1), (((t : ℚ)⁻¹) ^ (2 * k + 1) -
          3 * (p : ℚ) ^ 1 * ((t : ℚ)⁻¹) ^ (2 * k + 2) -
          3 * ((2 * k + 3 : ℕ) : ℚ) * (p : ℚ) ^ 1 * (Hh t * ((t : ℚ)⁻¹) ^ (2 * k + 1))) := by
      simp only [sg, Finset.sum_sub_distrib, Finset.mul_sum]
    have hσ2 : D p 1 (sg p (p ^ 1) (2 * k + 2)) := sg_small (by omega) (by omega)
    have hσ1 : D p 2 (sg p (p ^ 1) (2 * k + 1)) := by
      have h1 := sg_refl2 (p := p) (le_refl 1) hodd
      have h6 : D p 2 (((2 : ℕ) : ℚ) * sg p (p ^ 1) (2 * k + 1)) := by
        have h7 := (h1.le (by omega : 2 ≤ 2 * 1)).sub
          ((((D.nat (2 * k + 1)).mul0' hpp).mul hσ2).le (by omega : 2 ≤ 1 + 1))
        exact h7.congr (by push_cast; ring)
      exact D.ucancel hp2 h6
    have hHt : D p 1 (∑ t ∈ U p (p ^ 1), Hh t * ((t : ℚ)⁻¹) ^ (2 * k + 1)) :=
      Hh_sum_odd h5 hodd (by omega)
    have h8 := (hσ1.sub (((D.three.mul0' hpp).mul hσ2).le (by omega : 2 ≤ 1 + 1))).sub
      ((((D.three.mul0 (D.nat (2 * k + 3))).mul0' hpp).mul hHt).le (by omega : 2 ≤ 1 + 1))
    exact h8.congr e
  refine (hsum.add hS).congr ?_
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun t _ => by ring

private lemma choose_eq {a e u : ℕ} (hu : ¬ p ∣ u) :
    ((3 * p ^ (e + a)).choose (u * p ^ e) : ℚ) =
      -(3 * (p : ℚ) ^ a * (u : ℚ)⁻¹ * (-1 : ℚ) ^ (u * p ^ e) *
        Gp (3 * (p : ℚ) ^ (e + a)) (u * p ^ e)) := by
  have hu0 : (u : ℚ) ≠ 0 := by
    intro h0
    apply hu
    have h1 : u = 0 := by exact_mod_cast h0
    rw [h1]; exact dvd_zero p
  have hP : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
  have hj : 1 ≤ u * p ^ e :=
    Nat.mul_pos (Nat.pos_of_ne_zero (by rintro rfl; exact hu (dvd_zero p))) (pow_pos hp.out.pos e)
  have h1 := choose_mul_eq' (3 * p ^ (e + a)) (u * p ^ e) hj
  push_cast at h1
  have huu : (u : ℚ)⁻¹ * (u : ℚ) = 1 := inv_mul_cancel₀ hu0
  have hJ : ((u : ℚ) * (p : ℚ) ^ e) ≠ 0 := mul_ne_zero hu0 (pow_ne_zero _ hP)
  apply mul_right_cancel₀ hJ
  rw [h1]
  linear_combination (3 * (p : ℚ) ^ a * (p : ℚ) ^ e * (-1 : ℚ) ^ (u * p ^ e) *
    Gp (3 * (p : ℚ) ^ (e + a)) (u * p ^ e)) * huu

private lemma choose_pow_d {a e u : ℕ} (hu : ¬ p ∣ u) (k : ℕ) :
    (-1 : ℚ) ^ (u * p ^ e) * ((3 * p ^ (e + a)).choose (u * p ^ e) : ℚ) ^ (2 * k + 3) =
      -((3 : ℚ) ^ (2 * k + 3) * ((p : ℚ) ^ a) ^ (2 * k + 3) * ((u : ℚ)⁻¹) ^ (2 * k + 3) *
        Gp (3 * (p : ℚ) ^ (e + a)) (u * p ^ e) ^ (2 * k + 3)) := by
  rw [choose_eq (a := a) (e := e) hu]
  have hs : (-1 : ℚ) ^ (u * p ^ e) * ((-1 : ℚ) ^ (u * p ^ e)) ^ (2 * k + 3) = 1 := by
    rw [← pow_succ', ← pow_mul]
    exact Even.neg_one_pow ⟨u * p ^ e * (k + 2), by ring⟩
  have hodd : Odd (2 * k + 3) := ⟨k + 1, by ring⟩
  rw [Odd.neg_pow hodd]
  have hY : (3 * (p : ℚ) ^ a * (u : ℚ)⁻¹ * (-1 : ℚ) ^ (u * p ^ e) *
        Gp (3 * (p : ℚ) ^ (e + a)) (u * p ^ e)) ^ (2 * k + 3) =
      (3 : ℚ) ^ (2 * k + 3) * ((p : ℚ) ^ a) ^ (2 * k + 3) * ((u : ℚ)⁻¹) ^ (2 * k + 3) *
        ((-1 : ℚ) ^ (u * p ^ e)) ^ (2 * k + 3) *
        Gp (3 * (p : ℚ) ^ (e + a)) (u * p ^ e) ^ (2 * k + 3) := by
    simp only [mul_pow]
  rw [hY]
  linear_combination (-((3 : ℚ) ^ (2 * k + 3) * ((p : ℚ) ^ a) ^ (2 * k + 3) *
    ((u : ℚ)⁻¹) ^ (2 * k + 3) * Gp (3 * (p : ℚ) ^ (e + a)) (u * p ^ e) ^ (2 * k + 3))) * hs

private lemma layer_d (k : ℕ) (hk : 1 ≤ k) (hp7 : 2 * k + 7 ≤ p) {a e : ℕ} (ha : 1 ≤ a) :
    D p (3 * (e + a) + 3 + (2 * k + 3)) (∑ u ∈ U p (p ^ a),
      (-1 : ℚ) ^ (u * p ^ e) * ((3 * p ^ (e + a)).choose (u * p ^ e) : ℚ) ^ (2 * k + 3) *
        (R p (3 * (p : ℚ) ^ (e + a + 1)) (p * (u * p ^ e)) ^ (2 * k + 3) - 1)) := by
  have h5 : 5 ≤ p := by omega
  have hp2 : ¬ p ∣ 2 := Nat.not_dvd_of_pos_of_lt (by norm_num) (by omega)
  have hε : Eps p 0 := eps_zero (by omega)
  have h2i : D p 0 ((2 : ℚ)⁻¹) := by simpa using D.inv (p := p) hp2
  have hc : D p 0 (((2 * k + 3 : ℕ) : ℚ) * (3 : ℚ) ^ (2 * k + 4) * (2 : ℚ)⁻¹) :=
    ((D.nat (2 * k + 3)).mul0 (D.three.pow0 _)).mul0 h2i
  have hσ := sg2 h5 (s := e + 1) (by omega)
  obtain ⟨a1, ha1⟩ : ∃ a1, a = a1 + 1 := ⟨a - 1, by omega⟩
  have hmul : a * (2 * k + 3) = 2 * (a1 * k) + 3 * a1 + 2 * k + 3 := by
    rw [ha1]
    ring
  have hterm : ∀ u ∈ U p (p ^ a), D p (3 * (e + a) + 3 + (2 * k + 3))
      ((-1 : ℚ) ^ (u * p ^ e) * ((3 * p ^ (e + a)).choose (u * p ^ e) : ℚ) ^ (2 * k + 3) *
          (R p (3 * (p : ℚ) ^ (e + a + 1)) (p * (u * p ^ e)) ^ (2 * k + 3) - 1) +
        ((2 * k + 3 : ℕ) : ℚ) * (3 : ℚ) ^ (2 * k + 4) * (2 : ℚ)⁻¹ *
          (((p : ℚ) ^ a) ^ (2 * k + 3) * (p : ℚ) ^ (e + a + 1) * (p : ℚ) ^ (e + 1) *
            sg p (p ^ (e + 1)) 2) *
          (Gp (3 * (p : ℚ) ^ (e + a)) (u * p ^ e) ^ (2 * k + 3) *
            (((u : ℚ)⁻¹) ^ (2 * k + 1) - 3 * (p : ℚ) ^ a * ((u : ℚ)⁻¹) ^ (2 * k + 2)))) := by
    intro u hu
    obtain ⟨hlt, hnd⟩ := mem_U.mp hu
    have hu0 : (u : ℚ) ≠ 0 := by
      intro h0
      apply hnd
      have h1 : u = 0 := by exact_mod_cast h0
      rw [h1]; exact dvd_zero p
    have huu : (u : ℚ)⁻¹ * (u : ℚ) = 1 := inv_mul_cancel₀ hu0
    have hui : D p 0 ((u : ℚ)⁻¹) := D.inv hnd
    have hn : u * p ^ e ≤ p ^ (e + a) := by
      calc u * p ^ e ≤ p ^ a * p ^ e := Nat.mul_le_mul_right _ (le_of_lt hlt)
        _ = p ^ (e + a) := by rw [pow_add]; ring
    have hG0 : D p 0 (Gp (3 * (p : ℚ) ^ (e + a)) (u * p ^ e)) :=
      D_of_sub_one (Gp_sub_one (m := e + a) (c := e + a) (by omega) hn)
    rw [choose_pow_d (a := a) (e := e) hnd k,
      show p * (u * p ^ e) = u * p ^ (e + 1) by rw [pow_succ]; ring]
    have hRl := R_lemma h5 hε (r := e + a + 1) (s := e + 1) (by omega) u (3 * e + 6)
      (by omega) (by omega) (by omega)
    have hd : D p (e + 1) ((u : ℚ) * (p : ℚ) ^ (e + 1) - 3 * (p : ℚ) ^ (e + a + 1)) :=
      ((D.nat u).mul0' (D.ppow (e + 1))).sub
        ((D.three.mul0' (D.ppow (e + a + 1))).le (by omega))
    have hM : D p (3 * e + 4) (3 / 2 * (p : ℚ) ^ (e + a + 1) * (u : ℚ) * sg p (p ^ (e + 1)) 2 *
        ((u : ℚ) * (p : ℚ) ^ (e + 1) - 3 * (p : ℚ) ^ (e + a + 1))) := by
      have h7 := ((((D.three.mul0 h2i).mul0' (D.ppow (e + a + 1))).mul0 (D.nat u)).mul hσ).mul hd
      exact (h7.le (by omega)).congr (by ring)
    have hX : D p (3 * e + 4) (R p (3 * (p : ℚ) ^ (e + a + 1)) (u * p ^ (e + 1)) - 1) :=
      ((hRl.le (by omega)).add hM).congr (by ring)
    have hbin := binom1 hX (2 * k + 3)
    have hcube : D p (3 * e + 6)
        (R p (3 * (p : ℚ) ^ (e + a + 1)) (u * p ^ (e + 1)) ^ (2 * k + 3) - 1 -
        ((2 * k + 3 : ℕ) : ℚ) * (3 / 2 * (p : ℚ) ^ (e + a + 1) * (u : ℚ) * sg p (p ^ (e + 1)) 2 *
          ((u : ℚ) * (p : ℚ) ^ (e + 1) - 3 * (p : ℚ) ^ (e + a + 1)))) := by
      have h7 := (hbin.le (by omega : 3 * e + 6 ≤ 2 * (3 * e + 4))).add
        ((D.nat (2 * k + 3)).mul0' hRl)
      exact h7.congr (by ring)
    have hCf : D p (a * (2 * k + 3)) ((3 : ℚ) ^ (2 * k + 3) * ((p : ℚ) ^ a) ^ (2 * k + 3) *
        ((u : ℚ)⁻¹) ^ (2 * k + 3) * Gp (3 * (p : ℚ) ^ (e + a)) (u * p ^ e) ^ (2 * k + 3)) :=
      (((D.three.pow0 (2 * k + 3)).mul0' ((D.ppow a).pow (2 * k + 3))).mul0
        (hui.pow0 _)).mul0 (hG0.pow0 _)
    have h9 := (hCf.mul hcube).neg
    refine (h9.le (by omega)).congr ?_
    linear_combination (((2 * k + 3 : ℕ) : ℚ) * (3 : ℚ) ^ (2 * k + 4) / 2 *
      ((p : ℚ) ^ a) ^ (2 * k + 3) * (p : ℚ) ^ (e + a + 1) * (p : ℚ) ^ (e + 1) *
      sg p (p ^ (e + 1)) 2 * Gp (3 * (p : ℚ) ^ (e + a)) (u * p ^ e) ^ (2 * k + 3) *
      (((u : ℚ)⁻¹) ^ (2 * k + 1) * ((u : ℚ)⁻¹ * (u : ℚ) + 1) -
        3 * (p : ℚ) ^ a * ((u : ℚ)⁻¹) ^ (2 * k + 2))) * huu
  have hK : D p (a * (2 * k + 3) + (e + a + 1) + (e + 1) + (e + 1))
      (((p : ℚ) ^ a) ^ (2 * k + 3) * (p : ℚ) ^ (e + a + 1) * (p : ℚ) ^ (e + 1) *
        sg p (p ^ (e + 1)) 2) :=
    ((((D.ppow a).pow (2 * k + 3)).mul (D.ppow (e + a + 1))).mul (D.ppow (e + 1))).mul hσ
  have hKW : D p (3 * (e + a) + 3 + (2 * k + 3))
      ((((p : ℚ) ^ a) ^ (2 * k + 3) * (p : ℚ) ^ (e + a + 1) * (p : ℚ) ^ (e + 1) *
        sg p (p ^ (e + 1)) 2) *
        ∑ u ∈ U p (p ^ a), Gp (3 * (p : ℚ) ^ (e + a)) (u * p ^ e) ^ (2 * k + 3) *
          (((u : ℚ)⁻¹) ^ (2 * k + 1) - 3 * (p : ℚ) ^ a * ((u : ℚ)⁻¹) ^ (2 * k + 2))) := by
    rcases Nat.lt_or_ge a 2 with h | h
    · obtain rfl : a = 1 := by omega
      exact (hK.mul (W_one_d k hp7 e)).le (by omega)
    · have hW0 : D p 0 (∑ u ∈ U p (p ^ a), Gp (3 * (p : ℚ) ^ (e + a)) (u * p ^ e) ^ (2 * k + 3) *
          (((u : ℚ)⁻¹) ^ (2 * k + 1) - 3 * (p : ℚ) ^ a * ((u : ℚ)⁻¹) ^ (2 * k + 2))) := by
        apply D.sum
        intro u hu
        obtain ⟨hlt, hnd⟩ := mem_U.mp hu
        have hui : D p 0 ((u : ℚ)⁻¹) := D.inv hnd
        have hn : u * p ^ e ≤ p ^ (e + a) := by
          calc u * p ^ e ≤ p ^ a * p ^ e := Nat.mul_le_mul_right _ (le_of_lt hlt)
            _ = p ^ (e + a) := by rw [pow_add]; ring
        have hG0 : D p 0 (Gp (3 * (p : ℚ) ^ (e + a)) (u * p ^ e)) :=
          D_of_sub_one (Gp_sub_one (m := e + a) (c := e + a) (by omega) hn)
        exact (hG0.pow0 _).mul0 ((hui.pow0 _).sub
          ((D.three.mul0 ((D.ppow a).le (Nat.zero_le _))).mul0 (hui.pow0 _)))
      have ha1k : a1 ≤ a1 * k := Nat.le_mul_of_pos_right a1 hk
      exact (hK.mul hW0).le (by omega)
  have h8 := (D.sum _ _ hterm).sub (hc.mul0' hKW)
  refine h8.congr ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

private lemma nonunit_d (k : ℕ) (hk : 1 ≤ k) (hp7 : 2 * k + 7 ≤ p) {ρ : ℕ} (hρ : 1 ≤ ρ) :
    D p (3 * ρ + 3 + (2 * k + 3)) (∑ j ∈ Finset.range (p ^ ρ),
      (-1 : ℚ) ^ j * ((3 * p ^ ρ).choose j : ℚ) ^ (2 * k + 3) *
        (R p (3 * (p : ℚ) ^ (ρ + 1)) (p * j) ^ (2 * k + 3) - 1)) := by
  rw [sum_layers hp.out.pos]
  have h0 : (-1 : ℚ) ^ 0 * ((3 * p ^ ρ).choose 0 : ℚ) ^ (2 * k + 3) *
      (R p (3 * (p : ℚ) ^ (ρ + 1)) (p * 0) ^ (2 * k + 3) - 1) = 0 := by
    simp [R, U]
  rw [h0, zero_add]
  apply D.sum
  intro e he
  have he' := Finset.mem_range.mp he
  obtain ⟨a, rfl⟩ : ∃ a, ρ = e + a := ⟨ρ - e, by omega⟩
  rw [Nat.add_sub_cancel_left]
  exact layer_d k hk hp7 (by omega)

private lemma unit_d (k : ℕ) (hp7 : 2 * k + 7 ≤ p) (ρ : ℕ) :
    D p 1 (∑ x ∈ U p (p ^ (ρ + 1)), Gp (3 * (p : ℚ) ^ (ρ + 1)) x ^ (2 * k + 3) *
      ((x : ℚ)⁻¹) ^ (2 * k + 3)) := by
  have h5 : 5 ≤ p := by omega
  have hodd : Odd (2 * k + 3) := ⟨k + 1, by ring⟩
  have hterm : ∀ x ∈ U p (p ^ (ρ + 1)), D p 1
      (Gp (3 * (p : ℚ) ^ (ρ + 1)) x ^ (2 * k + 3) * ((x : ℚ)⁻¹) ^ (2 * k + 3) -
        ((x : ℚ)⁻¹) ^ (2 * k + 3)) := by
    intro x hx
    obtain ⟨hlt, hnd⟩ := mem_U.mp hx
    have hG1 : D p 1 (Gp (3 * (p : ℚ) ^ (ρ + 1)) x - 1) :=
      (Gp_sub_one (m := ρ + 1) (c := ρ + 1) (by omega) (le_of_lt hlt)).le (by omega)
    have hGd := D_pow_sub (D_of_sub_one hG1) D.one hG1 (2 * k + 3)
    exact (hGd.mul0 ((D.inv hnd).pow0 (2 * k + 3))).congr (by ring)
  have hσ : D p 1 (sg p (p ^ (ρ + 1)) (2 * k + 3)) :=
    (sg_odd h5 (by omega) hodd).le (by omega)
  refine ((D.sum _ _ hterm).add hσ).congr ?_
  unfold sg
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun x _ => by ring

private lemma main_d (k : ℕ) (hk : 1 ≤ k) (hp7 : 2 * k + 7 ≤ p) {r : ℕ} (hr : 2 ≤ r) :
    ((p : ℤ) ^ (3 * r + (2 * k + 3))) ∣
      (OMA.S_oeis_a375180.b (k + 1) (p ^ r) - OMA.S_oeis_a375180.b (k + 1) (p ^ (r - 1))) := by
  obtain ⟨ρ, rfl⟩ : ∃ ρ, r = ρ + 1 := ⟨r - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  have hp0 : 0 < p := hp.out.pos
  have hp2 : p ≠ 2 := by omega
  have hodd : Odd p := hp.out.odd_of_ne_two hp2
  have hb : ∀ n : ℕ, Odd n → ((OMA.S_oeis_a375180.b (k + 1) n : ℤ) : ℚ) =
      ∑ x ∈ Finset.range n, (-1 : ℚ) ^ x * ((3 * n).choose x : ℚ) ^ (2 * k + 3) := by
    intro n hn
    unfold OMA.S_oeis_a375180.b
    push_cast
    refine Finset.sum_congr rfl fun x _ => ?_
    have he : Even (n + 1) := hn.add_one
    rw [show n + x + 1 = (n + 1) + x by ring, pow_add, he.neg_one_pow, one_mul,
      show 2 * (k + 1) + 1 = 2 * k + 3 by ring]
  apply D.dvd
  push_cast
  rw [hb _ hodd.pow, hb _ hodd.pow]
  have hsplit := sum_range_mul_split p (p ^ ρ) hp0
    (fun x => (-1 : ℚ) ^ x * ((3 * p ^ (ρ + 1)).choose x : ℚ) ^ (2 * k + 3))
  rw [← pow_succ'] at hsplit
  rw [hsplit]
  have hunit : D p (3 * (ρ + 1) + (2 * k + 3))
      (∑ x ∈ (Finset.range (p ^ (ρ + 1))).filter (fun x => ¬ p ∣ x),
        (-1 : ℚ) ^ x * ((3 * p ^ (ρ + 1)).choose x : ℚ) ^ (2 * k + 3)) := by
    have h1 := unit_d k hp7 ρ
    have h2 := (((D.three.pow0 (2 * k + 3)).mul0'
      ((D.ppow (ρ + 1)).pow (2 * k + 3))).mul h1).neg
    have hmul : (ρ + 1) * (2 * k + 3) = 2 * (ρ * k) + 3 * ρ + 2 * k + 3 := by ring
    have hρk : 1 ≤ ρ * k := Nat.mul_pos (by omega) hk
    refine (h2.le (by omega)).congr ?_
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun x hx => ?_
    have hx' := (mem_U.mp hx).2
    have h3 := choose_pow_d (p := p) (a := ρ + 1) (e := 0) hx' k
    simp only [pow_zero, mul_one, zero_add] at h3
    rw [h3]
    ring
  have hnon := nonunit_d k hk hp7 (ρ := ρ) (by omega)
  have htot := hunit.add (hnon.le (by omega))
  refine htot.congr ?_
  rw [add_sub_assoc, ← Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  have h4 := choose_ratio (p := p) hp2 (3 * p ^ ρ) j
  have h5' : p * (3 * p ^ ρ) = 3 * p ^ (ρ + 1) := by
    rw [pow_succ]
    ring
  rw [h5'] at h4
  have h6 : (-1 : ℚ) ^ (p * j) = (-1) ^ j := by
    rw [pow_mul, hodd.neg_one_pow]
  rw [h4, h6]
  push_cast
  ring

end A375180H2

theorem OMA.solution : type_of% @OMA.S_oeis_a375180.main := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro p hp hp7
    exact SolvedConjecture05.conjecture_1 p hp hp7
  ·
    intro p r hp h5 hr
    by_cases h52 : p = 5 ∧ r = 2
    · obtain ⟨rfl, rfl⟩ := h52
      exact A375180H2.case_5_2
    · have : Fact p.Prime := ⟨hp⟩
      obtain ⟨ε, hε⟩ := A375180H2.exists_eps (p := p) h5
      have hrε : 2 + ε ≤ r := by
        rcases hε with ⟨h0, _⟩ | ⟨h1, h5e⟩
        · omega
        · have hr2 : r ≠ 2 := fun h2 => h52 ⟨h5e, h2⟩
          omega
      exact A375180H2.main_general h5 hε hrε
  · intro m p hm hp hpge
    exact SolvedConjecture05.conjecture_general m p hm hp hpge
  ·
    intro m p r hm hp h5 hr
    have : Fact p.Prime := ⟨hp⟩
    rcases Nat.lt_or_ge m 2 with h | h
    · obtain rfl : m = 1 := by omega
      have hε : A375180H2.Eps p 0 := A375180H2.eps_zero (p := p) (by omega)
      have h1 := A375180H2.main_general (p := p) (by omega) hε (r := r) (by omega)
      have hba : ∀ n, OMA.S_oeis_a375180.b 1 n = OMA.S_oeis_a375180.a n := fun n => rfl
      have he : 3 * r + 2 * 1 + 1 = 3 * r + 3 := by ring
      rw [he, hba, hba]
      exact h1
    · obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      have h1 := A375180H2.main_d (p := p) k (by omega) (by omega) hr
      have he : 3 * r + 2 * (k + 1) + 1 = 3 * r + (2 * k + 3) := by ring
      rw [he]
      exact h1
