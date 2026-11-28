import OMAStatements.S_oeis_a008705
import Mathlib

/-!
# Proof of the two supercongruences of OEIS A008705 (Peter Bala, Apr 18 2023)

`a(n) = [x^n] (Product_{m=1..n} (1 - x^m))^n`; for every prime `p >= 3`,
`a(p) == -1 - p (mod p^2)` and `a(2p) == p - 1 (mod p^2)`.

Work in `R[X]`, `R = ZMod (p^2)`, where `p * p = 0`. Call `F` *good* for `(a, b)` if
`F_0 = 1`, `F_p = a`, `F_{2p} = b` and `p ∣ F_d` whenever `p ∤ d`. Good polynomials multiply by
`(a1, b1) * (a2, b2) = (a1 + a2, b1 + a1 * a2 + b2)`, because every cross term is `p * p = 0`.
Each factor `(1 - x^m)^p` is good, with `[x^d] = (-1)^(d/m) * C(p, d/m)` for `m ∣ d` and `0`
otherwise; the data are `(-1, 0)` for `m = 1`, `(0, -1)` for `m = 2`, `(-p, C(p,2))` for `m = p`,
`(0, -p)` for `m = 2p` and `(0, 0)` for every other `m`. Hence `Product_{m=1..p} (1 - x^m)^p` has
`[x^p] = -1 - p`, and `H = Product_{m=1..2p} (1 - x^m)^p` is good for `(-1 - p, -1 + C(p,2))`, so
`[x^(2p)] H^2 = 2 * (-1 + C(p,2)) + (1 + p)^2 = p - 1` (using `2 * C(p,2) = p * (p - 1)`).
-/

namespace OMA.P_oeis_a008705

open Polynomial Finset

/-- `F_0 = 1`, `F_p = a`, `F_{2p} = b`, and `p ∣ F_d` for every `d` not divisible by `p`. -/
private def Good (p : ℕ) (F : Polynomial (ZMod (p ^ 2))) (a b : ZMod (p ^ 2)) : Prop :=
  F.coeff 0 = 1 ∧ F.coeff p = a ∧ F.coeff (2 * p) = b ∧
    ∀ d, ¬ p ∣ d → (p : ZMod (p ^ 2)) ∣ F.coeff d

private lemma p_mul_p (p : ℕ) : (p : ZMod (p ^ 2)) * (p : ZMod (p ^ 2)) = 0 := by
  rw [← Nat.cast_mul, ← pow_two, ZMod.natCast_self]

private lemma mul_eq_zero_of_dvd {p : ℕ} {x y : ZMod (p ^ 2)}
    (hx : (p : ZMod (p ^ 2)) ∣ x) (hy : (p : ZMod (p ^ 2)) ∣ y) : x * y = 0 := by
  obtain ⟨r, rfl⟩ := hx
  obtain ⟨s, rfl⟩ := hy
  calc (p : ZMod (p ^ 2)) * r * ((p : ZMod (p ^ 2)) * s)
      = ((p : ZMod (p ^ 2)) * (p : ZMod (p ^ 2))) * (r * s) := by ring
    _ = 0 := by rw [p_mul_p, zero_mul]

private lemma Good.one {p : ℕ} (hp : 0 < p) : Good p 1 0 0 := by
  refine ⟨by simp, ?_, ?_, fun d hd => ?_⟩
  · rw [Polynomial.coeff_one, if_neg (by omega)]
  · rw [Polynomial.coeff_one, if_neg (by omega)]
  · have hd0 : d ≠ 0 := by
      rintro rfl
      exact hd (dvd_zero p)
    rw [Polynomial.coeff_one, if_neg hd0]
    exact dvd_zero _

private lemma Good.mul {p : ℕ} (hp : 0 < p) {F G : Polynomial (ZMod (p ^ 2))}
    {a1 b1 a2 b2 : ZMod (p ^ 2)} (hF : Good p F a1 b1) (hG : Good p G a2 b2) :
    Good p (F * G) (a1 + a2) (b1 + a1 * a2 + b2) := by
  obtain ⟨hF0, hFp, hF2, hFd⟩ := hF
  obtain ⟨hG0, hGp, hG2, hGd⟩ := hG
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Polynomial.mul_coeff_zero, hF0, hG0, mul_one]
  · rw [Polynomial.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => F.coeff i * G.coeff j) p]
    have hterm : ∀ k ∈ Finset.range p.succ, F.coeff k * G.coeff (p - k) =
        (if k = 0 then a2 else 0) + (if k = p then a1 else 0) := by
      intro k hk
      have hk' : k ≤ p := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      by_cases h0 : k = 0
      · subst h0
        rw [if_pos rfl, if_neg (by omega), Nat.sub_zero, hF0, hGp, one_mul, add_zero]
      · by_cases h1 : k = p
        · subst h1
          rw [if_neg h0, if_pos rfl, Nat.sub_self, hFp, hG0, mul_one, zero_add]
        · have hk1 : ¬ p ∣ k := fun h => by
            have := Nat.le_of_dvd (by omega) h
            omega
          have hk2 : ¬ p ∣ (p - k) := fun h => by
            have := Nat.le_of_dvd (by omega) h
            omega
          rw [if_neg h0, if_neg h1, add_zero]
          exact mul_eq_zero_of_dvd (hFd k hk1) (hGd _ hk2)
    rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, Finset.sum_ite_eq',
      Finset.sum_ite_eq', if_pos (Finset.mem_range.mpr (by omega)),
      if_pos (Finset.mem_range.mpr (by omega))]
    ring
  · rw [Polynomial.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => F.coeff i * G.coeff j) (2 * p)]
    have hterm : ∀ k ∈ Finset.range (2 * p).succ, F.coeff k * G.coeff (2 * p - k) =
        (if k = 0 then b2 else 0) + (if k = p then a1 * a2 else 0) +
          (if k = 2 * p then b1 else 0) := by
      intro k hk
      have hk' : k ≤ 2 * p := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      by_cases h0 : k = 0
      · subst h0
        rw [if_pos rfl, if_neg (by omega), if_neg (by omega), Nat.sub_zero, hF0, hG2, one_mul,
          add_zero, add_zero]
      · by_cases h1 : k = p
        · subst h1
          rw [if_neg h0, if_pos rfl, if_neg (by omega), show 2 * k - k = k by omega, hFp, hGp,
            zero_add, add_zero]
        · by_cases h2 : k = 2 * p
          · subst h2
            rw [if_neg h0, if_neg h1, if_pos rfl, Nat.sub_self, hF2, hG0, mul_one, zero_add,
              zero_add]
          · have hk1 : ¬ p ∣ k := by
              rintro ⟨t, ht⟩
              rcases Nat.lt_or_ge t 3 with h | h
              · interval_cases t <;> omega
              · have := Nat.mul_le_mul_left p h
                omega
            have hk2 : ¬ p ∣ (2 * p - k) := fun h =>
              hk1 ((Nat.dvd_add_right h).mp
                (by rw [Nat.sub_add_cancel hk']; exact Dvd.intro_left 2 rfl))
            rw [if_neg h0, if_neg h1, if_neg h2, add_zero, add_zero]
            exact mul_eq_zero_of_dvd (hFd k hk1) (hGd _ hk2)
    rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, Finset.sum_add_distrib,
      Finset.sum_ite_eq', Finset.sum_ite_eq', Finset.sum_ite_eq',
      if_pos (Finset.mem_range.mpr (by omega)), if_pos (Finset.mem_range.mpr (by omega)),
      if_pos (Finset.mem_range.mpr (by omega))]
    ring
  · intro d hd
    rw [Polynomial.coeff_mul]
    refine Finset.dvd_sum fun x hx => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
    by_cases h1 : p ∣ x.1
    · have h2 : ¬ p ∣ x.2 := fun h => hd (hx ▸ dvd_add h1 h)
      exact dvd_mul_of_dvd_right (hGd _ h2) _
    · exact dvd_mul_of_dvd_left (hFd _ h1) _

private lemma Good.prod_zero {ι : Type*} {p : ℕ} (hp : 0 < p) (s : Finset ι)
    (f : ι → Polynomial (ZMod (p ^ 2))) (hf : ∀ i ∈ s, Good p (f i) 0 0) :
    Good p (∏ i ∈ s, f i) 0 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Good.one hp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    have h := (hf a (Finset.mem_insert_self a s)).mul hp
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))
    simpa using h

/-- The coefficients of `(1 - x^m)^p`. -/
private lemma coeff_factor {R : Type*} [CommRing R] (p m d : ℕ) (hm : 0 < m) :
    ((1 - X ^ m : Polynomial R) ^ p).coeff d =
      if m ∣ d then (-1) ^ (d / m) * (p.choose (d / m) : R) else 0 := by
  have hterm : ∀ j : ℕ, (-(X ^ m : Polynomial R)) ^ j * 1 ^ (p - j) * (p.choose j : Polynomial R) =
      C ((-1) ^ j * (p.choose j : R)) * X ^ (m * j) := by
    intro j
    rw [one_pow, mul_one, neg_pow, ← pow_mul, map_mul, map_pow, map_neg, map_one, map_natCast]
    ring
  rw [sub_eq_neg_add, add_pow, Polynomial.finsetSum_coeff]
  simp_rw [hterm, Polynomial.coeff_C_mul_X_pow]
  by_cases hmd : m ∣ d
  · obtain ⟨k, rfl⟩ := hmd
    rw [if_pos (dvd_mul_right m k), Nat.mul_div_cancel_left k hm]
    have hiff : ∀ j : ℕ, (m * k = m * j) ↔ (j = k) := fun j =>
      ⟨fun h => (Nat.eq_of_mul_eq_mul_left hm h).symm, fun h => by rw [h]⟩
    simp_rw [hiff, Finset.sum_ite_eq']
    by_cases hk : k ∈ Finset.range (p + 1)
    · rw [if_pos hk]
    · rw [if_neg hk, Nat.choose_eq_zero_of_lt (by simpa using hk)]
      simp
  · rw [if_neg hmd]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [if_neg]
    rintro rfl
    exact hmd (dvd_mul_right m j)

/-- The factor `(1 - x^m)^p` over `ZMod (p^2)`. -/
private noncomputable def fac (p m : ℕ) : Polynomial (ZMod (p ^ 2)) :=
  (1 - X ^ m : Polynomial (ZMod (p ^ 2))) ^ p

private lemma good_fac {p : ℕ} (hp : p.Prime) {m : ℕ} (hm : 0 < m) :
    Good p (fac p m)
      (if m ∣ p then (-1) ^ (p / m) * (p.choose (p / m) : ZMod (p ^ 2)) else 0)
      (if m ∣ 2 * p then (-1) ^ (2 * p / m) * (p.choose (2 * p / m) : ZMod (p ^ 2)) else 0) := by
  refine ⟨?_, coeff_factor p m p hm, coeff_factor p m (2 * p) hm, fun d hd => ?_⟩
  · unfold fac
    rw [coeff_factor p m 0 hm, if_pos (dvd_zero m)]
    simp
  · unfold fac
    rw [coeff_factor p m d hm]
    by_cases hmd : m ∣ d
    · obtain ⟨k, rfl⟩ := hmd
      rw [if_pos (dvd_mul_right m k), Nat.mul_div_cancel_left k hm]
      have hk0 : k ≠ 0 := by
        rintro rfl
        exact hd (by simp)
      have hkp : k ≠ p := by
        rintro rfl
        exact hd (dvd_mul_left k m)
      rcases lt_or_gt_of_ne hkp with h | h
      · exact dvd_mul_of_dvd_right (Nat.cast_dvd_cast (hp.dvd_choose_self hk0 h)) _
      · rw [Nat.choose_eq_zero_of_lt h]
        simp
    · rw [if_neg hmd]
      exact dvd_zero _

private lemma good_fac_one {p : ℕ} (hp : p.Prime) (hodd : Odd p) : Good p (fac p 1) (-1) 0 := by
  have h := good_fac hp (m := 1) Nat.one_pos
  rw [if_pos (one_dvd _), if_pos (one_dvd _), Nat.div_one, Nat.div_one, hodd.neg_one_pow,
    Nat.choose_self, Nat.choose_eq_zero_of_lt (by have := hp.pos; omega)] at h
  simpa using h

private lemma good_fac_two {p : ℕ} (hp : p.Prime) (hodd : Odd p) : Good p (fac p 2) 0 (-1) := by
  have h := good_fac hp (m := 2) (by norm_num)
  have h2 : ¬ 2 ∣ p := by
    have := Nat.odd_iff.mp hodd
    omega
  rw [if_neg h2, if_pos (dvd_mul_right 2 p), Nat.mul_div_cancel_left p (by norm_num),
    hodd.neg_one_pow, Nat.choose_self] at h
  simpa using h

private lemma good_fac_p {p : ℕ} (hp : p.Prime) :
    Good p (fac p p) (-(p : ZMod (p ^ 2))) (p.choose 2 : ZMod (p ^ 2)) := by
  have h := good_fac hp (m := p) hp.pos
  rw [if_pos (dvd_refl p), if_pos (dvd_mul_left p 2), Nat.div_self hp.pos,
    Nat.mul_div_cancel 2 hp.pos, Nat.choose_one_right] at h
  simpa using h

private lemma good_fac_two_p {p : ℕ} (hp : p.Prime) :
    Good p (fac p (2 * p)) 0 (-(p : ZMod (p ^ 2))) := by
  have hpos := hp.pos
  have h := good_fac hp (m := 2 * p) (by omega)
  have h2 : ¬ 2 * p ∣ p := fun hd => by
    have := Nat.le_of_dvd hpos hd
    omega
  rw [if_neg h2, if_pos (dvd_refl _), Nat.div_self (by omega), Nat.choose_one_right] at h
  simpa using h

private lemma good_fac_other {p : ℕ} (hp : p.Prime) {m : ℕ} (hm : 0 < m) (h1 : m ≠ 1)
    (h2 : m ≠ 2) (hmp : m ≠ p) (hm2p : m ≠ 2 * p) : Good p (fac p m) 0 0 := by
  have h := good_fac hp hm
  have hnp : ¬ m ∣ p := fun hd => by
    rcases (Nat.dvd_prime hp).mp hd with h | h
    · exact h1 h
    · exact hmp h
  have hn2p : ¬ m ∣ 2 * p := fun hd => by
    by_cases hpm : p ∣ m
    · obtain ⟨t, rfl⟩ := hpm
      have ht : t ∣ 2 := Nat.dvd_of_mul_dvd_mul_left hp.pos (by rwa [mul_comm 2 p] at hd)
      have ht2 : t ≤ 2 := Nat.le_of_dvd (by norm_num) ht
      interval_cases t
      · omega
      · exact hmp (mul_one p)
      · exact hm2p (mul_comm p 2)
    · have hcop : Nat.Coprime m p := ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpm).symm
      have hm2 : m ∣ 2 := hcop.dvd_of_dvd_mul_right hd
      have hle : m ≤ 2 := Nat.le_of_dvd (by norm_num) hm2
      omega
  rwa [if_neg hnp, if_neg hn2p] at h

/-- `[x^p] Product_{m=1..p} (1 - x^m)^p = -1 - p` in `ZMod (p^2)`. -/
private lemma coeff_prod_p {p : ℕ} (hp : p.Prime) (h3 : 3 ≤ p) :
    (∏ m ∈ Finset.Icc 1 p, fac p m).coeff p = -1 - (p : ZMod (p ^ 2)) := by
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  have m1 : 1 ∈ Finset.Icc 1 p := Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩
  have m2 : 2 ∈ (Finset.Icc 1 p).erase 1 :=
    Finset.mem_erase.mpr ⟨by omega, Finset.mem_Icc.mpr ⟨by omega, by omega⟩⟩
  have m3 : p ∈ ((Finset.Icc 1 p).erase 1).erase 2 :=
    Finset.mem_erase.mpr ⟨by omega, Finset.mem_erase.mpr
      ⟨by omega, Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩⟩⟩
  have hrest : Good p (∏ m ∈ (((Finset.Icc 1 p).erase 1).erase 2).erase p, fac p m) 0 0 := by
    refine Good.prod_zero hp.pos _ _ fun m hm => ?_
    simp only [Finset.mem_erase, Finset.mem_Icc] at hm
    exact good_fac_other hp (by omega) (by omega) (by omega) (by omega) (by omega)
  have hall := (good_fac_one hp hodd).mul hp.pos
    ((good_fac_two hp hodd).mul hp.pos ((good_fac_p hp).mul hp.pos hrest))
  rw [Finset.mul_prod_erase _ _ m3, Finset.mul_prod_erase _ _ m2,
    Finset.mul_prod_erase _ _ m1] at hall
  rw [hall.2.1]
  ring

/-- `Product_{m=1..2p} (1 - x^m)^p` is good for `(-1 - p, -1 + C(p,2))`. -/
private lemma good_prod_two_p {p : ℕ} (hp : p.Prime) (h3 : 3 ≤ p) :
    Good p (∏ m ∈ Finset.Icc 1 (2 * p), fac p m) (-1 - (p : ZMod (p ^ 2)))
      (-1 + (p.choose 2 : ZMod (p ^ 2))) := by
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  have m1 : 1 ∈ Finset.Icc 1 (2 * p) := Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩
  have m2 : 2 ∈ (Finset.Icc 1 (2 * p)).erase 1 :=
    Finset.mem_erase.mpr ⟨by omega, Finset.mem_Icc.mpr ⟨by omega, by omega⟩⟩
  have m3 : p ∈ ((Finset.Icc 1 (2 * p)).erase 1).erase 2 :=
    Finset.mem_erase.mpr ⟨by omega, Finset.mem_erase.mpr
      ⟨by omega, Finset.mem_Icc.mpr ⟨by omega, by omega⟩⟩⟩
  have m4 : 2 * p ∈ (((Finset.Icc 1 (2 * p)).erase 1).erase 2).erase p :=
    Finset.mem_erase.mpr ⟨by omega, Finset.mem_erase.mpr ⟨by omega, Finset.mem_erase.mpr
      ⟨by omega, Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩⟩⟩⟩
  have hrest : Good p
      (∏ m ∈ ((((Finset.Icc 1 (2 * p)).erase 1).erase 2).erase p).erase (2 * p), fac p m) 0 0 := by
    refine Good.prod_zero hp.pos _ _ fun m hm => ?_
    simp only [Finset.mem_erase, Finset.mem_Icc] at hm
    exact good_fac_other hp (by omega) (by omega) (by omega) (by omega) (by omega)
  have hall := (good_fac_one hp hodd).mul hp.pos
    ((good_fac_two hp hodd).mul hp.pos
      ((good_fac_p hp).mul hp.pos ((good_fac_two_p hp).mul hp.pos hrest)))
  rw [Finset.mul_prod_erase _ _ m4, Finset.mul_prod_erase _ _ m3, Finset.mul_prod_erase _ _ m2,
    Finset.mul_prod_erase _ _ m1] at hall
  obtain ⟨h0, ha, hb, hd⟩ := hall
  refine ⟨h0, ?_, ?_, hd⟩
  · rw [ha]
    ring
  · rw [hb]
    ring

/-- `2 * C(p,2) = p * (p - 1)` in `ZMod (p^2)`. -/
private lemma two_mul_choose_two (p : ℕ) (hp : 0 < p) :
    (2 : ZMod (p ^ 2)) * (p.choose 2 : ZMod (p ^ 2)) =
      (p : ZMod (p ^ 2)) * ((p : ZMod (p ^ 2)) - 1) := by
  have hnat : 2 * p.choose 2 = p * (p - 1) := by
    rw [Nat.choose_two_right]
    exact Nat.mul_div_cancel' (Nat.even_mul_pred_self p).two_dvd
  have hcast := congrArg (Nat.cast : ℕ → ZMod (p ^ 2)) hnat
  rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_pred hp] at hcast
  simpa using hcast

/-- Reduction of `a n` modulo `p^2`. -/
private lemma cast_a (p n : ℕ) :
    ((OMA.S_oeis_a008705.a n : ℤ) : ZMod (p ^ 2)) =
      ((∏ m ∈ Finset.Icc 1 n, (1 - X ^ m : Polynomial (ZMod (p ^ 2)))) ^ n).coeff n := by
  have h : ((∏ m ∈ Finset.Icc 1 n, (1 - X ^ m : Polynomial ℤ)) ^ n).map
      (Int.castRingHom (ZMod (p ^ 2))) =
      (∏ m ∈ Finset.Icc 1 n, (1 - X ^ m : Polynomial (ZMod (p ^ 2)))) ^ n := by
    simp [Polynomial.map_prod]
  rw [← h, Polynomial.coeff_map]
  rfl

private theorem part1 (p : ℕ) (hp : p.Prime) (h3 : 3 ≤ p) :
    ((p : ℤ) ^ 2) ∣ (OMA.S_oeis_a008705.a p - (-1 - (p : ℤ))) := by
  rw [show ((p : ℤ) ^ 2) = ((p ^ 2 : ℕ) : ℤ) by push_cast; rfl,
    ← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  rw [cast_a p p, ← Finset.prod_pow]
  have h := coeff_prod_p hp h3
  unfold fac at h
  rw [h]
  ring

private theorem part2 (p : ℕ) (hp : p.Prime) (h3 : 3 ≤ p) :
    ((p : ℤ) ^ 2) ∣ (OMA.S_oeis_a008705.a (2 * p) - ((p : ℤ) - 1)) := by
  rw [show ((p : ℤ) ^ 2) = ((p ^ 2 : ℕ) : ℤ) by push_cast; rfl,
    ← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  rw [cast_a p (2 * p), pow_mul', ← Finset.prod_pow,
    pow_two (∏ m ∈ Finset.Icc 1 (2 * p), (1 - X ^ m : Polynomial (ZMod (p ^ 2))) ^ p)]
  have hG := good_prod_two_p hp h3
  have hsq := hG.mul hp.pos hG
  unfold fac at hsq
  rw [hsq.2.2.1]
  linear_combination two_mul_choose_two p hp.pos + 2 * p_mul_p p

end OMA.P_oeis_a008705

theorem OMA.solution : type_of% @OMA.S_oeis_a008705.main := by
  intro p hp h3
  have h1 := OMA.P_oeis_a008705.part1 p hp h3
  have h2 := OMA.P_oeis_a008705.part2 p hp h3
  refine ⟨?_, ?_⟩
  · rw [Int.modEq_iff_dvd]
    exact (dvd_sub_comm).mp h1
  · rw [Int.modEq_iff_dvd]
    exact (dvd_sub_comm).mp h2
