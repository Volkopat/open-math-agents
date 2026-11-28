import OMAStatements.S_oeis_a091258

/-!
The denominator conjecture of Michel Marcus, recorded in OEIS A091258,
with comparison sequence A004611.
https://oeis.org/A091258
https://oeis.org/A004611
Formal statement credited to @senamakel. Proof by @grp06.
-/

open scoped ArithmeticFunction.sigma
open ArithmeticFunction

namespace A091258Proof

private def phi (x : ℕ) : ℕ := x ^ 2 + x + 1

private def psi (x : ℕ) : ℕ := x ^ 2 + 1 - x

private def ratio (n : ℕ) : ℚ := (σ 3 n : ℚ) / (σ 1 n : ℚ)

private theorem phi_pos (x : ℕ) : 0 < phi x := by
  unfold phi
  omega

private theorem cast_phi {R : Type*} [Semiring R] (x : ℕ) :
    (phi x : R) = (x : R) ^ 2 + x + 1 := by
  simp [phi]

private theorem cast_psi {R : Type*} [CommRing R] {x : ℕ} (hx : 1 ≤ x) :
    (psi x : R) = (x : R) ^ 2 - x + 1 := by
  have hle : x ≤ x ^ 2 + 1 := by
    have hh : x ≤ x * x := by simpa using Nat.mul_le_mul_left x hx
    simpa [pow_two] using hh.trans (Nat.le_succ (x * x))
  rw [psi, Nat.cast_sub hle]
  push_cast
  ring

private theorem cubic {R : Type*} [CommRing R] (x : R) :
    (x ^ 2 + x + 1) * (x - 1) = x ^ 3 - 1 := by ring

private theorem ratio_primePow {p : ℕ} (hp : p.Prime) (k : ℕ) :
    ratio (p ^ k) = (phi (p ^ (k + 1)) : ℚ) / phi p := by
  let x : ℚ := p
  let m : ℕ := k + 1
  have hx : x - 1 ≠ 0 := sub_ne_zero.mpr (by
    change (p : ℚ) ≠ 1
    exact_mod_cast hp.ne_one)
  have hd : (σ 1 (p ^ k) : ℚ) ≠ 0 := by
    exact_mod_cast (sigma_pos 1 _ (pow_ne_zero _ hp.ne_zero)).ne'
  have hphi : (phi p : ℚ) ≠ 0 := by
    exact_mod_cast (phi_pos p).ne'
  unfold ratio
  apply (div_eq_div_iff hd hphi).2
  have h₁ : (σ 1 (p ^ k) : ℚ) = ∑ j ∈ Finset.range m, x ^ j := by
    simp [sigma_one_apply_prime_pow hp, x, m]
  have h₃ : (σ 3 (p ^ k) : ℚ) = ∑ j ∈ Finset.range m, (x ^ 3) ^ j := by
    simp only [sigma_apply_prime_pow hp, Nat.cast_sum, Nat.cast_pow, m, x]
    apply Finset.sum_congr rfl
    intro j _
    rw [Nat.mul_comm j 3, pow_mul]
  rw [h₁, h₃, cast_phi, cast_phi, Nat.cast_pow]
  change (∑ j ∈ Finset.range m, (x ^ 3) ^ j) * (x ^ 2 + x + 1) =
    ( (x ^ m) ^ 2 + x ^ m + 1) * (∑ j ∈ Finset.range m, x ^ j)
  apply mul_right_cancel₀ hx
  calc
    _ = (∑ j ∈ Finset.range m, (x ^ 3) ^ j) * (x ^ 3 - 1) := by
      rw [mul_assoc, cubic]
    _ = (x ^ 3) ^ m - 1 := geom_sum_mul _ _
    _ = (x ^ m) ^ 3 - 1 := by rw [← pow_mul, ← pow_mul, Nat.mul_comm 3 m]
    _ = ((x ^ m) ^ 2 + x ^ m + 1) * (x ^ m - 1) := (cubic _).symm
    _ = _ := by rw [mul_assoc, geom_sum_mul]

private theorem ratio_mul {a b : ℕ} (h : a.Coprime b) :
    ratio (a * b) = ratio a * ratio b := by
  simp only [ratio, isMultiplicative_sigma.map_mul_of_coprime h, Nat.cast_mul]
  simp [div_eq_mul_inv, mul_inv_rev, mul_assoc, mul_comm, mul_left_comm]

private theorem ratio_prime {p : ℕ} (hp : p.Prime) :
    ratio p = (psi p : ℚ) := by
  have h := ratio_primePow hp 1
  rw [pow_one] at h
  rw [h]
  rw [cast_phi, cast_phi, Nat.cast_pow, cast_psi hp.one_lt.le]
  apply (div_eq_iff (by positivity)).2
  ring

private theorem den_dvd_nat (a b : ℕ) : ((a : ℚ) / b).den ∣ b := by
  have h := Rat.den_dvd (a : ℤ) (b : ℤ)
  rw [Rat.divInt_eq_div, Int.cast_natCast, Int.cast_natCast] at h
  exact Int.natCast_dvd_natCast.mp h

private theorem phi_zero {m x : ℕ} :
    ((x : ZMod m) ^ 2 + x + 1 = 0) ↔ m ∣ phi x := by
  rw [← cast_phi, ZMod.natCast_eq_zero_iff]

private theorem phi_coprime (x : ℕ) : x.Coprime (phi x) := by
  apply (ZMod.isUnit_iff_coprime _ _).mp
  have h := (phi_zero (m := phi x) (x := x)).2 dvd_rfl
  apply isUnit_iff_exists_inv.mpr
  refine ⟨-((x : ZMod (phi x)) + 1), ?_⟩
  linear_combination -h

private theorem not_nine_dvd_phi (x : ℕ) : ¬9 ∣ phi x := by
  intro h
  have hn : ∀ y : ZMod 9, y ^ 2 + y + 1 ≠ 0 := by decide
  exact hn _ (phi_zero.mpr h)

private theorem three_dvd_phi_iff (x : ℕ) :
    3 ∣ phi x ↔ (x : ZMod 3) = 1 := by
  have hh : ∀ y : ZMod 3, y ^ 2 + y + 1 = 0 ↔ y = 1 := by decide
  exact phi_zero.symm.trans (hh _)

private theorem prime_of_phi {p x : ℕ} (hp : p.Prime) (h3 : p ≠ 3)
    (hx : p ∣ phi x) : p % 3 = 1 := by
  letI : Fact p.Prime := ⟨hp⟩
  have hzero : (x : ZMod p) ^ 2 + x + 1 = 0 := phi_zero.mpr hx
  have hn : (x : ZMod p) ≠ 0 := by
    intro he
    simp [he] at hzero
  have ho : (x : ZMod p) ≠ 1 := by
    intro he
    have hc : (3 : ZMod p) = 0 := by
      rw [he] at hzero
      linear_combination hzero
    have hd : p ∣ 3 := (ZMod.natCast_eq_zero_iff 3 p).mp (by simpa using hc)
    exact h3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp hd)
  have hc : (x : ZMod p) ^ 3 = 1 := by
    have he := cubic (x : ZMod p)
    rw [hzero, zero_mul] at he
    exact sub_eq_zero.mp he.symm
  have hord : orderOf (x : ZMod p) = 3 :=
    ((Nat.dvd_prime Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hc)).resolve_left
      (fun he => ho (orderOf_eq_one_iff.mp he))
  have hd := ZMod.orderOf_dvd_card_sub_one hn
  rw [hord] at hd
  obtain ⟨t, ht⟩ := hd
  have := hp.two_le
  omega

private theorem local_den {p : ℕ} (hp : p.Prime) (k l : ℕ)
    (hl : l.Prime) (hd : l ∣ (ratio (p ^ k)).den) : l % 3 = 1 := by
  rw [ratio_primePow hp] at hd
  have hphi := hd.trans (den_dvd_nat (phi (p ^ (k + 1))) (phi p))
  by_cases he : l = 3
  · subst l
    have hn : 3 ∣ phi (p ^ (k + 1)) := by
      apply (three_dvd_phi_iff _).2
      rw [Nat.cast_pow, (three_dvd_phi_iff p).1 hphi, one_pow]
    obtain ⟨a, ha⟩ := hn
    obtain ⟨b, hb⟩ := hphi
    rw [ha, hb, Nat.cast_mul, Nat.cast_mul] at hd
    rw [mul_div_mul_left _ _ (by norm_num : ((3 : ℕ) : ℚ) ≠ 0)] at hd
    have hb3 := hd.trans (den_dvd_nat a b)
    obtain ⟨c, hc⟩ := hb3
    exact (not_nine_dvd_phi p ⟨c, by rw [hb, hc]; ring⟩).elim
  · exact prime_of_phi hl he hphi

private theorem all_den (n : ℕ) :
    ∀ l : ℕ, l.Prime → l ∣ (ratio n).den → l % 3 = 1 := by
  refine Nat.recOnPrimeCoprime (motive := fun a =>
    ∀ l : ℕ, l.Prime → l ∣ (ratio a).den → l % 3 = 1) ?_ ?_ ?_ n
  · intro l hl hd
    have hzero : ratio 0 = 0 := by
      simp [ratio, show σ 3 0 = 0 from sigma_eq_zero.mpr rfl]
    rw [hzero] at hd
    exact (hl.not_dvd_one (by simpa only [Rat.den_zero] using hd)).elim
  · intro p k hp l hl hd
    exact local_den hp k l hl hd
  · intro a b _ _ hab ha hb l hl hd
    rw [ratio_mul hab] at hd
    rcases hl.dvd_mul.mp (hd.trans (Rat.mul_den_dvd (ratio a) (ratio b))) with h | h
    · exact ha l hl h
    · exact hb l hl h


private theorem coprime_mod {a b m : ℕ} (h : a ≡ b [MOD m]) (hb : b.Coprime m) :
    a.Coprime m := by
  rw [Nat.coprime_iff_gcd_eq_one, h.gcd_eq]
  exact hb

private theorem phi_mod {a b m : ℕ} (h : a ≡ b [MOD m]) :
    phi a ≡ phi b [MOD m] :=
  ((Nat.ModEq.pow 2 h).add h).add Nat.ModEq.rfl

private theorem derivative_coprime {x m : ℕ} (hx : m ∣ phi x) (h3 : ¬3 ∣ m) :
    (2 * x + 1).Coprime m := by
  apply Nat.coprime_of_dvd
  intro p hp hpd hpm
  let y : ZMod p := x
  have hz : y ^ 2 + y + 1 = 0 := phi_zero.mpr (hpm.trans hx)
  have hy : 2 * y + 1 = 0 := by
    have hh := (ZMod.natCast_eq_zero_iff (2 * x + 1) p).mpr hpd
    simpa [y] using hh
  have hc : (3 : ZMod p) = 0 := by
    calc
      (3 : ZMod p) = 4 * (y ^ 2 + y + 1) - (2 * y + 1) ^ 2 := by ring
      _ = 0 := by rw [hz, hy]; ring
  have hp3 : p ∣ 3 := (ZMod.natCast_eq_zero_iff 3 p).mp (by simpa using hc)
  have he := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp hp3
  subst p
  exact h3 hpm

/-- A lift with prescribed quotient modulo a divisor of the previous modulus. -/
private theorem lift_phi {M m r w : ℕ} (hm : m ≠ 0) (hmM : m ∣ M)
    (hr : phi r = M * w) (hu : (2 * r + 1).Coprime m) (b : ℕ) :
    ∃ t u : ℕ, phi (r + M * t) = M * u ∧ u ≡ b [MOD m] := by
  letI : NeZero m := ⟨hm⟩
  let U := ZMod.unitOfCoprime (2 * r + 1) hu
  let T : ZMod m := ((b : ZMod m) - w) * ((U⁻¹ : (ZMod m)ˣ) : ZMod m)
  let t := T.val
  let u := w + t * (2 * r + 1) + M * t ^ 2
  refine ⟨t, u, ?_, ?_⟩
  · dsimp [u]
    simp only [phi] at hr ⊢
    calc
      _ = (r ^ 2 + r + 1) + M * (t * (2 * r + 1) + M * t ^ 2) := by ring
      _ = _ := by rw [hr]; ring
  · apply (ZMod.natCast_eq_natCast_iff u b m).mp
    have hM : (M : ZMod m) = 0 := (ZMod.natCast_eq_zero_iff M m).2 hmM
    have hT : (t : ZMod m) = T := ZMod.natCast_zmod_val T
    have hU : (((U⁻¹ : (ZMod m)ˣ) : ZMod m) * (↑(2 * r + 1) : ZMod m)) = 1 := by
      rw [← ZMod.coe_unitOfCoprime (2 * r + 1) hu]
      change (((U⁻¹ : (ZMod m)ˣ) : ZMod m) * (U : ZMod m)) = 1
      exact U.inv_mul
    change ((w + t * (2 * r + 1) + M * t ^ 2 : ℕ) : ZMod m) = b
    rw [Nat.cast_add, Nat.cast_add, Nat.cast_mul, Nat.cast_mul, hM, zero_mul, add_zero, hT]
    dsimp only [T]
    rw [mul_assoc, hU, mul_one]
    ring

private theorem prime_root {p : ℕ} (hp : p.Prime) (hp3 : p % 3 = 1) :
    ∃ r : ℕ, p ∣ phi r := by
  letI : Fact p.Prime := ⟨hp⟩
  letI : NeZero p := ⟨hp.ne_zero⟩
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hd : 3 ∣ p - 1 := by
    refine ⟨p / 3, ?_⟩
    omega
  have hc : 3 ∣ Fintype.card (ZMod p)ˣ := by
    rwa [ZMod.card_units_eq_totient, Nat.totient_prime hp]
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card (G := (ZMod p)ˣ) 3 hc
  let x : ZMod p := u
  have hne : x ≠ 1 := by
    intro he
    have he' : u = 1 := Units.ext (by simpa [x] using he)
    rw [he', orderOf_one] at hu
    omega
  have hpow : x ^ 3 = 1 := by
    have h := pow_orderOf_eq_one u
    rw [hu] at h
    simpa [x] using congrArg (fun a : (ZMod p)ˣ => (a : ZMod p)) h
  have hz := cubic x
  rw [hpow, sub_self] at hz
  have hroot : x ^ 2 + x + 1 = 0 := (mul_eq_zero.mp hz).resolve_right (sub_ne_zero.mpr hne)
  refine ⟨x.val, phi_zero.mp ?_⟩
  rwa [ZMod.natCast_zmod_val]

private theorem prime_power_root {p : ℕ} (hp : p.Prime) (hp3 : p % 3 = 1) :
    ∀ k : ℕ, ∃ r : ℕ, p ^ k ∣ phi r := by
  have hn3 : ¬3 ∣ p := by
    intro h
    have hh := Nat.mod_eq_zero_of_dvd h
    omega
  intro k
  induction k with
  | zero => exact ⟨0, by simp⟩
  | succ k ih =>
    cases k with
    | zero => simpa using prime_root hp hp3
    | succ k =>
      obtain ⟨r, w, hw⟩ := ih
      have hd : p ∣ p ^ (k + 1) := dvd_pow_self p (Nat.succ_ne_zero _)
      have hc := derivative_coprime (hd.trans (show p ^ (k + 1) ∣ phi r from ⟨w, hw⟩)) hn3
      obtain ⟨t, u, he, hu⟩ := lift_phi hp.ne_zero hd hw hc 0
      obtain ⟨v, hv⟩ := Nat.modEq_zero_iff_dvd.mp hu
      refine ⟨r + p ^ (k + 1) * t, v, ?_⟩
      rw [he, hv, pow_succ (p : ℕ) (k + 1), mul_assoc]

private theorem root_of_good (d : ℕ) :
    (∀ p : ℕ, p.Prime → p ∣ d → p % 3 = 1) → ∃ r : ℕ, d ∣ phi r := by
  refine Nat.recOnPrimeCoprime (motive := fun m =>
    (∀ p : ℕ, p.Prime → p ∣ m → p % 3 = 1) → ∃ r : ℕ, m ∣ phi r) ?_ ?_ ?_ d
  · intro h
    have := h 3 Nat.prime_three (dvd_zero _)
    omega
  · intro p k hp h
    cases k with
    | zero => exact ⟨0, by simp⟩
    | succ k =>
      exact prime_power_root hp (h p hp (dvd_pow_self p (Nat.succ_ne_zero _))) (k + 1)
  · intro a b _ _ hab ha hb h
    obtain ⟨r, hr⟩ := ha (fun p hp hd => h p hp (hd.trans (dvd_mul_right a b)))
    obtain ⟨s, hs⟩ := hb (fun p hp hd => h p hp (hd.trans (dvd_mul_left b a)))
    obtain ⟨t, ht, ht'⟩ := Nat.chineseRemainder hab r s
    refine ⟨t, hab.mul_dvd_of_dvd_of_dvd ?_ ?_⟩
    · exact ((phi_mod ht).dvd_iff dvd_rfl).mpr hr
    · exact ((phi_mod ht').dvd_iff dvd_rfl).mpr hs

private theorem realize {d : ℕ} (hd : 0 < d)
    (good : ∀ p : ℕ, p.Prime → p ∣ d → p % 3 = 1) :
    ∃ n : ℕ, 0 < n ∧ (ratio n).den = d := by
  by_cases h1 : d = 1
  · subst d
    exact ⟨1, by decide, by simp [ratio]⟩
  have h3 : ¬3 ∣ d := by
    intro h
    have := good 3 Nat.prime_three h
    omega
  have c3 : (3 : ℕ).Coprime d := Nat.prime_three.coprime_iff_not_dvd.mpr h3
  obtain ⟨r, w, hw⟩ := root_of_good d good
  obtain ⟨t, u, hru, hu⟩ :=
    lift_phi hd.ne' dvd_rfl hw (derivative_coprime ⟨w, hw⟩ h3) 1
  let a := r + d * t
  have ha : a.Coprime (d * d) := by
    have h : a.Coprime d := (phi_coprime a).coprime_dvd_right (show d ∣ phi a from ⟨u, hru⟩)
    exact Nat.coprime_mul_iff_right.mpr ⟨h, h⟩
  have c33 : (d * d).Coprime 3 := (Nat.coprime_mul_iff_right.mpr ⟨c3, c3⟩).symm
  obtain ⟨a₀, ha₀, ha₃⟩ := Nat.chineseRemainder c33 a 2
  have ca₀ : a₀.Coprime ((d * d) * 3) :=
    Nat.coprime_mul_iff_right.mpr
      ⟨coprime_mod ha₀ ha, coprime_mod ha₃ (by decide : Nat.Coprime 2 3)⟩
  obtain ⟨q, _, hq, hqa₀⟩ :=
    Nat.forall_exists_prime_gt_and_modEq 0 (mul_ne_zero (mul_ne_zero hd.ne' hd.ne') (by decide)) ca₀
  have hqa : q ≡ a [MOD d * d] := (hqa₀.of_dvd (dvd_mul_right _ _)).trans ha₀
  have hq₃ : q ≡ 2 [MOD 3] := (hqa₀.of_dvd (dvd_mul_left _ _)).trans ha₃
  have hnq₃ : ¬3 ∣ phi q := by
    intro h
    have he := (three_dvd_phi_iff q).mp h
    have hqz := (ZMod.natCast_eq_natCast_iff q 2 3).mpr hq₃
    rw [he] at hqz
    exact (by decide : (1 : ZMod 3) ≠ (2 : ZMod 3)) hqz
  have hqq : d ∣ phi q := ((phi_mod hqa).dvd_iff (dvd_mul_right d d)).mpr ⟨u, hru⟩
  obtain ⟨v, hv⟩ := hqq
  have hv_pos : 0 < v := by
    by_contra! h
    have he : v = 0 := by omega
    have hh := phi_pos q
    simp [hv, he] at hh
  have cv : v.Coprime d := by
    have hh := phi_mod hqa
    change phi q ≡ phi a [MOD d * d] at hh
    rw [hv, show phi a = d * u from hru] at hh
    exact coprime_mod ((Nat.ModEq.mul_left_cancel' hd.ne' hh).trans hu) (by simp)
  have hv_dvd : v ∣ phi q := by rw [hv]; exact dvd_mul_left v d
  letI : NeZero v := ⟨hv_pos.ne'⟩
  let b := (-(q : ZMod v)).val
  have hbz : (b : ZMod v) = -(q : ZMod v) := ZMod.natCast_zmod_val _
  have cb : b.Coprime v := by
    have cq : q.Coprime v := (phi_coprime q).coprime_dvd_right hv_dvd
    apply (ZMod.isUnit_iff_coprime _ _).mp
    rw [hbz]
    exact ((ZMod.isUnit_iff_coprime q v).mpr cq).neg
  obtain ⟨b₀, hb₀, hbv⟩ := Nat.chineseRemainder cv.symm 1 b
  have cb₀ : b₀.Coprime (d * v) :=
    Nat.coprime_mul_iff_right.mpr ⟨coprime_mod hb₀ (by simp), coprime_mod hbv cb⟩
  obtain ⟨p, hpq, hp, hpb₀⟩ :=
    Nat.forall_exists_prime_gt_and_modEq q (mul_ne_zero hd.ne' hv_pos.ne') cb₀
  have hpd : p ≡ 1 [MOD d] := (hpb₀.of_dvd (dvd_mul_right _ _)).trans hb₀
  have hpv : p ≡ b [MOD v] := (hpb₀.of_dvd (dvd_mul_left _ _)).trans hbv
  have hpsi_v : v ∣ psi p := by
    apply (ZMod.natCast_eq_zero_iff _ _).mp
    rw [cast_psi hp.one_lt.le, (ZMod.natCast_eq_natCast_iff _ _ _).mpr hpv, hbz]
    have hz : (q : ZMod v) ^ 2 + q + 1 = 0 := phi_zero.mpr hv_dvd
    linear_combination hz
  have cpsi : (psi p).Coprime d := by
    apply coprime_mod (b := 1) _ (by simp)
    apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
    rw [cast_psi hp.one_lt.le, (ZMod.natCast_eq_natCast_iff _ _ _).mpr hpd]
    simp
  obtain ⟨s, hs⟩ := hpsi_v
  have cs : s.Coprime d := cpsi.coprime_dvd_left (by rw [hs]; exact dvd_mul_left s v)
  have cphi : (phi (q ^ 3)).Coprime d := by
    apply coprime_mod (b := 3) _ c3
    apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
    have hz : (q : ZMod d) ^ 2 + q + 1 = 0 := phi_zero.mpr ⟨v, hv⟩
    have hc := cubic (q : ZMod d)
    rw [hz, zero_mul] at hc
    have hcube := sub_eq_zero.mp hc.symm
    rw [cast_phi, Nat.cast_pow, hcube]
    norm_num
  have hcop : (q ^ 2).Coprime p := ((Nat.coprime_primes hq hp).mpr (ne_of_lt hpq)).pow_left _
  refine ⟨q ^ 2 * p, Nat.mul_pos (pow_pos hq.pos _) hp.pos, ?_⟩
  have hr : ratio (q ^ 2 * p) = ((phi (q ^ 3) * s : ℕ) : ℚ) / d := by
    rw [ratio_mul hcop, ratio_primePow hq, ratio_prime hp]
    change (phi (q ^ 3) : ℚ) / phi q * (psi p : ℚ) = _
    rw [hv, hs]
    simp only [Nat.cast_mul]
    have hvq : (v : ℚ) ≠ 0 := by exact_mod_cast hv_pos.ne'
    have hdq : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
    field_simp <;> ring
  rw [hr]
  have hc := Nat.coprime_mul_iff_left.mpr ⟨cphi, cs⟩
  have hd_int : (0 : ℤ) < (d : ℤ) := by exact_mod_cast hd
  have hc_int : Nat.Coprime ((↑(phi (q ^ 3) * s) : ℤ).natAbs) (↑d : ℤ).natAbs := by
    simpa only [Int.natAbs_natCast] using hc
  have he := Rat.den_div_eq_of_coprime hd_int hc_int
  simp only [Int.cast_natCast] at he
  exact_mod_cast he

end A091258Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a091258.main := by
  apply Set.ext
  intro d
  change (∃ n : ℕ, 0 < n ∧ (A091258Proof.ratio n).den = d) ↔
    (0 < d ∧ ∀ q : ℕ, q.Prime → q ∣ d → q % 3 = 1)
  constructor
  · rintro ⟨n, _, rfl⟩
    exact ⟨(A091258Proof.ratio n).den_pos, A091258Proof.all_den n⟩
  · rintro ⟨hd, h⟩
    exact A091258Proof.realize hd h
