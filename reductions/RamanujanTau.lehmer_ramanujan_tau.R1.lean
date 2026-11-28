import FormalConjectures.Wikipedia.RamanujanTau
import Mathlib.Combinatorics.Enumerative.Pentagonal.PowerSeries
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.NumberTheory.LSeries.PrimesInAP

/-!
Lehmer's prime reduction, with Ramanujan's congruences modulo 691 and 23.
The coefficient calculation modulo 23 is proved directly from the defining Euler product.
-/

namespace OMA.R_RamanujanTau_lehmer_ramanujan_tau_R1

open PowerSeries PowerSeries.WithPiTopology RamanujanTau

/-- Coprime multiplicativity of the Euler product coefficients. -/
def H1 : Prop := ∀ a b : ℕ, a.Coprime b → τ (a*b) = τ a * τ b

/-- The Hecke recurrence away from 23. The powers of 23 are handled directly. -/
def H2 : Prop := ∀ p : ℕ, p.Prime → p ≠ 23 → ∀ n : ℕ,
  τ (p^(n+2)) = τ p * τ (p^(n+1)) - (p : ℤ)^11 * τ (p^n)

/-- Ramanujan's congruence at primes, using the least nonnegative residues. -/
def H3 : Prop := ∀ p : ℕ, p.Prime →
  τ p % 691 = (((1 + (p % 691)^11) % 691 : ℕ) : ℤ)

/-- The remaining primes pass two congruence tests. The second is a signed
pentagonal-number sum that can be evaluated with integer arithmetic. -/
def H4 : Prop :=
  let w := fun m : ℕ =>
      let t := (Nat.sqrt (24*m+1)+1)/6
      if pentagonal (t : ℤ) = m ∨ pentagonal (-(t : ℤ)) = m then (-1 : ZMod 23)^t else 0
  ∀ p : ℕ, p.Prime → 5527 ≤ p → p % 691 = 690 →
    (∑ j ∈ Finset.range ((p-1)/23+1), w j * w (p-1-23*j)) = 0 → τ p ≠ 0

lemma euler_product : Δ = X * pentagonalSeries ℤ ^ 24 := by
  unfold Δ
  congr 1
  rw [tprod_pnat_eq_tprod_succ (f := fun n => ((1 : PowerSeries ℤ) - X ^ n)^24)]
  rw [(multipliable_one_sub_X_pow ℤ).tprod_pow, tprod_one_sub_X_pow]

lemma euler_mod : map (Int.castRingHom (ZMod 23)) (pentagonalSeries ℤ) =
    pentagonalSeries (ZMod 23) := by
  ext n
  by_cases hn : n ∈ Set.range pentagonal
  · obtain ⟨k, rfl⟩ := hn
    simp [coeff_map]
  · simp [coeff_map, coeff_pentagonalSeries_eq_zero _ hn]

lemma delta_mod : map (Int.castRingHom (ZMod 23)) Δ =
    X * (expand 23 (by decide) (pentagonalSeries (ZMod 23)) * pentagonalSeries (ZMod 23)) := by
  rw [euler_product, map_mul, map_pow, map_X, euler_mod, show 24 = 23+1 by rfl, pow_succ]
  congr 2
  let _ : Fact (Nat.Prime 23) := ⟨by decide⟩
  have h := MvPowerSeries.map_frobenius_expand (f := pentagonalSeries (ZMod 23)) 23 (by decide)
  rw [ZMod.frobenius_zmod, MvPowerSeries.map_id] at h
  exact h.symm

lemma pentagonal_shift (j : ℤ) : pentagonal (4-23*j) = 529*pentagonal j+22 := by
  have h := two_mul_natCast_pentagonal (4-23*j)
  have h' := two_mul_natCast_pentagonal j
  zify
  nlinarith

lemma pentagonal_index {i : ℤ} {n : ℕ} (hi : pentagonal i = 23*n+22) :
    ∃ j : ℤ, i = 4-23*j := by
  have hi' := two_mul_natCast_pentagonal i
  rw [hi] at hi'
  push_cast at hi'
  have hz : (23 : ℤ) ∣ (6*i-1)^2 := ⟨24*n+23, by nlinarith⟩
  have hp : Prime (23 : ℤ) := by norm_num
  obtain ⟨k, hk⟩ := hp.dvd_of_dvd_pow hz
  exact ⟨(4-i)/23, by omega⟩

lemma pentagonal_section (n : ℕ) :
    coeff (23*n+22) (pentagonalSeries (ZMod 23)) =
    coeff n (expand 23 (by decide) (pentagonalSeries (ZMod 23))) := by
  by_cases hm : 23*n+22 ∈ Set.range pentagonal
  · obtain ⟨i, hi⟩ := hm
    obtain ⟨j, rfl⟩ := pentagonal_index hi
    have h : n = 23*pentagonal j := by rw [pentagonal_shift] at hi; omega
    rw [← hi, h, coeff_expand_mul, coeff_pentagonalSeries_pentagonal,
      coeff_pentagonalSeries_pentagonal]
    have hh : (4-23*j).negOnePow = j.negOnePow :=
      (Int.negOnePow_eq_iff _ _).mpr ⟨2-12*j, by ring⟩
    rw [hh]
  · rw [coeff_pentagonalSeries_eq_zero _ hm, coeff_expand]
    split_ifs with hd
    · apply Eq.symm
      apply coeff_pentagonalSeries_eq_zero
      rintro ⟨j, hj⟩
      apply hm
      refine ⟨4-23*j, ?_⟩
      rw [pentagonal_shift, hj]
      obtain ⟨v,rfl⟩ := hd
      omega
    · rfl

/-- Coefficient formula for multiplication by a series in X to the power 23. -/
lemma coeff_expand_product (f g : PowerSeries (ZMod 23)) (n : ℕ) :
    coeff n (expand 23 (by decide) g * f) =
    ∑ j ∈ Finset.range (n/23+1), coeff j g * coeff (n-23*j) f := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  let S := (Finset.range (n/23+1)).image (fun j => 23*j)
  have hsub : S ⊆ Finset.range (n+1) := by
    intro x hx
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hx
    simp only [Finset.mem_range] at hj ⊢
    omega
  rw [← Finset.sum_subset hsub]
  · rw [Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro j _
      simp only [coeff_expand_mul]
    · intro x hx y hy h; dsimp at h; omega
  · intro x hx hmiss
    have hd : ¬ 23 ∣ x := by
      rintro ⟨j,rfl⟩
      apply hmiss
      exact Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr (by have := Finset.mem_range.mp hx; omega), rfl⟩
    simp [coeff_expand_of_not_dvd _ _ _ hd]

lemma section_product (f g : PowerSeries (ZMod 23)) (n : ℕ) :
    coeff (23*n+22) (expand 23 (by decide) g * f) =
    coeff n (g * PowerSeries.mk (fun j => coeff (23*j+22) f)) := by
  rw [coeff_expand_product, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  rw [show (23*n+22)/23 = n by omega]
  apply Finset.sum_congr rfl
  intro j hj
  have hj' := Finset.mem_range.mp hj
  simp only [coeff_mk]
  rw [show 23*n+22-23*j = 23*(n-j)+22 by omega]

lemma tau_mul_23 (n : ℕ) : (τ (23*n) : ZMod 23) = (τ n : ZMod 23) := by
  cases n with
  | zero => rfl
  | succ n =>
    change (Int.castRingHom (ZMod 23)) (coeff _ Δ) = (Int.castRingHom (ZMod 23)) (coeff _ Δ)
    rw [← coeff_map, ← coeff_map, delta_mod]
    rw [show 23*(n+1) = (23*n+22)+1 by omega, coeff_succ_X_mul, coeff_succ_X_mul, section_product]
    have h : PowerSeries.mk (fun j => coeff (23*j+22) (pentagonalSeries (ZMod 23))) =
        expand 23 (by decide) (pentagonalSeries (ZMod 23)) := by
      ext j
      simpa only [coeff_mk] using pentagonal_section j
    rw [h, mul_comm]

theorem tau_pow_23 (n : ℕ) : (τ (23^n) : ZMod 23) = 1 := by
  induction n with
  | zero => simp [τ_one]
  | succ n ih => simpa only [pow_succ', tau_mul_23] using ih

lemma pentagonal_weight (m : ℕ) :
    coeff m (pentagonalSeries (ZMod 23)) =
      let t := (Nat.sqrt (24*m+1)+1)/6
      if pentagonal (t : ℤ) = m ∨ pentagonal (-(t : ℤ)) = m then (-1 : ZMod 23)^t else 0 := by
  dsimp only
  let t := (Nat.sqrt (24*m+1)+1)/6
  change _ = if pentagonal (t : ℤ) = m ∨ pentagonal (-(t : ℤ)) = m then (-1 : ZMod 23)^t else 0
  by_cases hm : m ∈ Set.range pentagonal
  · obtain ⟨i, hi⟩ := hm
    have hs : 24*m+1 = (6*i-1).natAbs^2 := by
      have h := two_mul_natCast_pentagonal i
      rw [hi] at h
      zify
      rw [sq_abs]
      nlinarith
    have ht : t = i.natAbs := by
      dsimp [t]
      rw [hs, Nat.sqrt_eq']
      omega
    have hor : i = (t : ℤ) ∨ i = -(t : ℤ) := by rw [ht]; omega
    have hmem : pentagonal (t : ℤ) = m ∨ pentagonal (-(t : ℤ)) = m := by
      rcases hor with h | h
      · exact Or.inl (h ▸ hi)
      · exact Or.inr (h ▸ hi)
    rw [if_pos hmem, ← hi, coeff_pentagonalSeries_pentagonal]
    rcases hor with h | h <;> rw [h] <;> simp [Int.negOnePow]
  · have hno : ¬ (pentagonal (t : ℤ) = m ∨ pentagonal (-(t : ℤ)) = m) := by
      rintro (h | h)
      · exact hm ⟨_, h⟩
      · exact hm ⟨_, h⟩
    rw [if_neg hno, coeff_pentagonalSeries_eq_zero _ hm]

/-- Compute tau modulo 23 with a finite sum and integer square roots. -/
lemma tau_mod23_compute (n : ℕ) : (τ (n+1) : ZMod 23) =
    let w := fun m : ℕ =>
      let t := (Nat.sqrt (24*m+1)+1)/6
      if pentagonal (t : ℤ) = m ∨ pentagonal (-(t : ℤ)) = m then (-1 : ZMod 23)^t else 0
    ∑ j ∈ Finset.range (n/23+1), w j * w (n-23*j) := by
  change (Int.castRingHom (ZMod 23)) (coeff (n+1) Δ) = _
  rw [← coeff_map, delta_mod, coeff_succ_X_mul, coeff_expand_product]
  simp only [pentagonal_weight]

lemma tau_1381 : (τ 1381 : ZMod 23) = -1 := by
  rw [show 1381 = 1380+1 by rfl, tau_mod23_compute]
  decide +kernel

lemma nonsquare_mod23 {n : ℕ} (hn : ∀ r : ZMod 23, r^2 ≠ (n : ZMod 23)) :
    (τ n : ZMod 23) = 0 := by
  cases n with
  | zero => simp [τ_zero]
  | succ n =>
    change (Int.castRingHom (ZMod 23)) (coeff (n+1) Δ) = 0
    rw [← coeff_map, delta_mod, coeff_succ_X_mul, coeff_expand_product]
    apply Finset.sum_eq_zero
    intro j hj
    apply mul_eq_zero_of_right
    apply coeff_pentagonalSeries_eq_zero
    rintro ⟨i, hi⟩
    have hle := Finset.mem_range.mp hj
    have hh := two_mul_natCast_pentagonal i
    rw [hi] at hh
    have ha : (n : ℤ) = ((n-23*j : ℕ) : ℤ) + 23*j := by omega
    have he : (6*i-1)^2 = (n+1 : ℤ) + 23*(((n-23*j : ℕ) : ℤ)-j) := by nlinarith
    have hcast := congrArg (Int.castRingHom (ZMod 23)) he
    apply hn (6*(i : ZMod 23)-1)
    push_cast at hcast ⊢
    have h23 : (23 : ZMod 23) = 0 := by decide
    simpa [h23] using hcast

lemma published_endpoint_mod23 : (τ 816212624008487344127999 : ZMod 23) = 0 := by
  apply nonsquare_mod23
  decide +kernel

/-- Any fixed lower cutoff still leaves primes passing both tests in the reduction. -/
lemma arbitrarily_large_survivors (N : ℕ) :
    ∃ p > N, p.Prime ∧ p % 691 = 690 ∧ (τ p : ZMod 23) = 0 := by
  obtain ⟨p, hs, hp, he⟩ := Nat.forall_exists_prime_gt_and_modEq N
    (q := 15893) (a := 15892) (by decide) (by decide)
  have h691 : p ≡ 15892 [MOD 691] := he.of_dvd (by decide)
  have h23 : p ≡ 15892 [MOD 23] := he.of_dvd (by decide)
  change p % 691 = 690 at h691
  change p % 23 = 22 at h23
  refine ⟨p, hs, hp, h691, nonsquare_mod23 ?_⟩
  rw [← ZMod.natCast_mod p 23, h23]
  decide +kernel

lemma first_candidate {p : ℕ} (hp : p.Prime) (hr : p % 691 = 690) (hz : τ p = 0) :
    5527 ≤ p := by
  by_contra! h
  let k : Fin 8 := ⟨p/691, by omega⟩
  have hval : 691*k.val+690 = p := by dsimp [k]; omega
  have tab : ∀ j : Fin 8, (691*j.val+690).Prime →
      691*j.val+690 = 1381 ∨ 691*j.val+690 = 5527 := by
    intro j
    fin_cases j <;> norm_num
  have hc := tab k (hval ▸ hp)
  rw [hval] at hc
  obtain rfl : p = 1381 := by omega
  have hh := tau_1381
  rw [hz, Int.cast_zero] at hh
  exact (by decide : (0 : ZMod 23) ≠ -1) hh

lemma remove_prime_factors (p a : ℤ) (m : ℕ) (h : ¬ p^m ∣ a) :
    ∃ k < m, ∃ u : ℤ, a = p^k*u ∧ ¬ p ∣ u := by
  induction m with
  | zero => simp at h
  | succ m ih =>
    by_cases hm : p^m ∣ a
    · obtain ⟨u, hu⟩ := hm
      refine ⟨m, by omega, u, hu, ?_⟩
      rintro ⟨v, hv⟩
      exact h ⟨v, by rw [hu, hv, pow_succ]; ring⟩
    · obtain ⟨k, hk, u, hu⟩ := ih hm
      exact ⟨k, by omega, u, hu⟩

/-- When the normalized second recurrence coefficient is divisible by p,
every normalized term is a unit modulo p. -/
lemma scaled_terms (f : ℕ → ℤ) (p d u v : ℤ) (hp : Prime p) (hu : ¬ p ∣ u)
    (h0 : f 0 = 1) (h1 : f 1 = d*u)
    (rec : ∀ n, f (n+2) = d*u*f (n+1) - (d^2*(p*v))*f n)
    (n : ℕ) : ∃ t, f n = d^n*t ∧ ¬ p ∣ t := by
  induction n using Nat.twoStepInduction with
  | zero => exact ⟨1, by simp [h0], hp.not_dvd_one⟩
  | one => exact ⟨u, by simpa using h1, hu⟩
  | more n ih0 ih1 =>
    obtain ⟨s, hs, hps⟩ := ih0
    obtain ⟨t, ht, hpt⟩ := ih1
    refine ⟨u*t - p*v*s, ?_, ?_⟩
    · rw [rec, hs, ht, pow_succ, pow_succ]; ring
    · intro h
      have h' : p ∣ p*v*s := ⟨v*s, by ring⟩
      have hm : p ∣ u*t := by simpa using dvd_add h h'
      exact (hp.dvd_mul.mp hm).elim hu hpt

/-- With a nonnegative discriminant the signed terms grow away from zero. -/
lemma large_trace (f : ℕ → ℤ) (a b : ℤ) (hb : 0 < b) (hbig : 4*b ≤ a^2)
    (h0 : f 0 = 1) (h1 : f 1 = a) (rec : ∀ n, f (n+2) = a*f (n+1) - b*f n)
    (n : ℕ) : f n ≠ 0 := by
  let g (k : ℕ) := f k * a^k
  have gr (k : ℕ) : g (k+2) = a^2*(g (k+1) - b*g k) := by
    dsimp [g]
    rw [rec, pow_succ, pow_succ]
    ring
  have grow (k : ℕ) : 0 < g k ∧ 2*b*g k ≤ g (k+1) := by
    induction k with
    | zero =>
      dsimp [g]
      simp only [h0, h1, pow_zero, pow_one, mul_one]
      constructor <;> nlinarith
    | succ k ih =>
      obtain ⟨hpos, hstep⟩ := ih
      have hbpos := mul_pos hb hpos
      have hd : 0 ≤ g (k+1) - b*g k := by linarith
      have hmul := mul_le_mul_of_nonneg_right hbig hd
      have hs := mul_nonneg hb.le (sub_nonneg.mpr hstep)
      refine ⟨by linarith, ?_⟩
      rw [gr]
      nlinarith
  intro hz
  have h := (grow n).1
  simp [g, hz] at h

lemma residue_of_zero (cong : H3) {p : ℕ} (hp : p.Prime) (hz : τ p = 0) :
    p % 691 = 690 := by
  have h := cong p hp
  rw [hz] at h
  have table : ∀ r : Fin 691, (1+r.val^11)%691 = 0 → r.val = 690 := by decide +kernel
  exact table ⟨p%691, Nat.mod_lt _ (by decide)⟩ (by dsimp; omega)

lemma high_valuation {p : ℕ} (hp : p.Prime)
    (hcong : τ p % 691 = (((1 + (p % 691)^11) % 691 : ℕ) : ℤ))
    (hn : τ p ≠ 0) (h : (p : ℤ)^6 ∣ τ p) : 4*(p : ℤ)^11 ≤ (τ p)^2 := by
  obtain ⟨v, hv⟩ := h
  by_cases h2 : p = 2
  · subst p
    norm_num at hcong hv ⊢
    have hs : τ 2 ≤ -128 ∨ 128 ≤ τ 2 := by omega
    rcases hs with hs | hs
    · nlinarith [sq_nonneg (τ 2 + 128)]
    · nlinarith [sq_nonneg (τ 2 - 128)]
  by_cases h3 : p = 3
  · subst p
    norm_num at hcong hv ⊢
    have hs : τ 3 ≤ -1458 ∨ 1458 ≤ τ 3 := by omega
    rcases hs with hs | hs
    · nlinarith [sq_nonneg (τ 3 + 1458)]
    · nlinarith [sq_nonneg (τ 3 - 1458)]
  have h4 : (4 : ℤ) ≤ p := by have := hp.two_le; omega
  have hv0 : v ≠ 0 := fun hz => hn (by simp [hv, hz])
  have hv2 : 1 ≤ v^2 := by have := sq_pos_of_ne_zero hv0; omega
  calc
    4*(p : ℤ)^11 ≤ (p : ℤ)*p^11 := mul_le_mul_of_nonneg_right h4 (by positivity)
    _ = ((p : ℤ)^6)^2 := by ring
    _ ≤ (τ p)^2 := by rw [hv, mul_pow]; exact le_mul_of_one_le_right (sq_nonneg _) hv2

lemma nonzero_prime_power (rec : H2) (cong : H3) {p : ℕ} (hp : p.Prime)
    (hn : τ p ≠ 0) (n : ℕ) : τ (p^n) ≠ 0 := by
  by_cases h23 : p = 23
  · subst p
    intro hz
    have h := tau_pow_23 n
    rw [hz] at h
    exact (by decide : (0 : ZMod 23) ≠ 1) (by simpa only [Int.cast_zero] using h)
  let f (k : ℕ) := τ (p^k)
  have h0 : f 0 = 1 := by simp [f, τ_one]
  have h1 : f 1 = τ p := by simp [f]
  by_cases h6 : (p : ℤ)^6 ∣ τ p
  · exact large_trace f (τ p) ((p : ℤ)^11) (by exact_mod_cast pow_pos hp.pos 11)
      (high_valuation hp (cong p hp) hn h6) h0 h1 (rec p hp h23) n
  obtain ⟨k, hk, u, ha, hu⟩ := remove_prime_factors p (τ p) 6 h6
  have hsplit : (p : ℤ)^11 = ((p : ℤ)^k)^2 * (p * (p : ℤ)^(10-2*k)) := by
    rw [← pow_succ', ← pow_mul, ← pow_add]
    congr 1
    omega
  have hprime : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  obtain ⟨t, ht, hpt⟩ := scaled_terms f p ((p : ℤ)^k) u ((p : ℤ)^(10-2*k)) hprime hu h0
    (h1.trans ha) (fun m => by simpa only [f, ← ha, ← hsplit] using rec p hp h23 m) n
  change f n ≠ 0
  rw [ht]
  exact mul_ne_zero (pow_ne_zero _ (pow_ne_zero _ (by exact_mod_cast hp.ne_zero)))
    (fun hz => hpt (hz ▸ dvd_zero _))

theorem main : H1 → H2 → H3 → H4 → type_of% @RamanujanTau.lehmer_ramanujan_tau := by
  intro mult rec cong residual n
  induction n using Nat.recOnPrimeCoprime with
  | zero => omega
  | prime_pow p k hp =>
    intro _
    apply nonzero_prime_power rec cong hp _ k
    intro h
    have hr := residue_of_zero cong hp h
    apply residual p hp (first_candidate hp hr h) hr _ h
    have htest := tau_mod23_compute (p-1)
    rw [Nat.sub_add_cancel hp.one_lt.le, h, Int.cast_zero] at htest
    exact htest.symm
  | coprime a b ha hb hab ia ib =>
    intro _
    rw [mult a b hab]
    exact mul_ne_zero (ia (by omega)) (ib (by omega))

end OMA.R_RamanujanTau_lehmer_ramanujan_tau_R1
