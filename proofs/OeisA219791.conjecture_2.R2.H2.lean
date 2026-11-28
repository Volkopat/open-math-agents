import OMAReductions.R_OeisA219791_conjecture_2_R2
import Mathlib

/-!
Lebesgue (1850): `x ^ 2 + 1 = y ^ q` has no solution with `x > 0` when `q` is prime.

For `q = 2` this is elementary. For odd `q`, `x` is even, and `x + i`, `x - i` are coprime in the
Gaussian integers, so `x + i = γ ^ q` (units are `q`-th powers). Writing `γ = r + s i`, `s` divides
the imaginary part `1`, so `s = ±1`, and the norm gives `r ^ 2 + 1 = y`, so `r` is even and nonzero.
Then `(1 - z) ^ q + (1 + z) ^ q = ±2` for `z = s r i`, i.e. `∑ C(q, 2j) (-r²)^j = ±1`, which is
impossible: modulo 4 the sum is 1, and the 2-adic valuation of the term `C(q,2) r²` is smaller
than that of every later term.
-/

namespace OMA.Lebesgue
open Finset

lemma two_sum {R : Type*} [CommRing R] (z : R) (q : ℕ) :
    (1 - z) ^ q + (1 + z) ^ q =
      2 * ∑ k ∈ range (q + 1), if Even k then (q.choose k : R) * (z ^ 2) ^ (k / 2) else 0 := by
  rw [sub_eq_add_neg, add_comm 1 (-z), add_comm 1 z, add_pow, add_pow, ← sum_add_distrib, mul_sum]
  refine sum_congr rfl fun k _ => ?_
  simp only [one_pow, mul_one]
  split_ifs with hk
  · rw [hk.neg_pow, ← pow_mul, Nat.mul_div_cancel' (even_iff_two_dvd.mp hk)]; ring
  · rw [(Nat.not_even_iff_odd.mp hk).neg_pow]; ring

lemma term_dvd (q k u e : ℕ) (hu4 : 4 ∣ u) (hu : 0 < u) (hk : 4 ≤ k) (hkq : k ≤ q)
    (he : 2 ^ e ∣ q.choose 2 * u) (heven : Even k) : 2 ^ (e + 1) ∣ q.choose k * u ^ (k / 2) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨j, rfl⟩ := heven
  have hj : (j + j) / 2 = j := by omega
  rw [hj]
  have hj2 : 2 ≤ j := by omega
  have hX : q.choose (j + j) * u ^ j ≠ 0 :=
    mul_ne_zero (Nat.choose_pos hkq).ne' (pow_ne_zero _ hu.ne')
  have hc : (j + j).choose 2 = j * (2 * j - 1) := by
    rw [Nat.choose_two_right]
    have : (j + j) * (j + j - 1) = 2 * (j * (2 * j - 1)) := by
      rcases j with _ | j
      · simp
      · rw [show j + 1 + (j + 1) - 1 = 2 * (j + 1) - 1 by omega]; ring
    rw [this, Nat.mul_div_cancel_left _ (by norm_num)]
  have hid : q.choose (j + j) * u ^ j * (j + j).choose 2 =
      (q.choose 2 * u) * ((q - 2).choose (j + j - 2) * u ^ (j - 1)) := by
    have h1 := Nat.choose_mul (n := q) (k := j + j) (s := 2) (by omega)
    have h2 : u ^ j = u * u ^ (j - 1) := by
      rw [← pow_succ']; congr 1; omega
    rw [h2]
    calc q.choose (j + j) * (u * u ^ (j - 1)) * (j + j).choose 2
        = (q.choose (j + j) * (j + j).choose 2) * (u * u ^ (j - 1)) := by ring
      _ = _ := by rw [h1]; ring
  have hdvd : 2 ^ (e + 2 * (j - 1)) ∣ q.choose (j + j) * u ^ j * (j + j).choose 2 := by
    rw [hid, pow_add]
    refine mul_dvd_mul he (Dvd.dvd.mul_left ?_ _)
    rw [pow_mul]
    exact pow_dvd_pow_of_dvd (by simpa using hu4) _
  have hcne : (j + j).choose 2 ≠ 0 := (Nat.choose_pos (by omega)).ne'
  rw [padicValNat_dvd_iff_le (mul_ne_zero hX hcne), padicValNat.mul hX hcne] at hdvd
  rw [padicValNat_dvd_iff_le hX]
  have hvj : padicValNat 2 ((j + j).choose 2) ≤ j - 1 := by
    rw [hc, padicValNat.mul (by omega) (by omega)]
    have hodd : padicValNat 2 (2 * j - 1) = 0 :=
      padicValNat.eq_zero_of_not_dvd (by omega)
    rw [hodd, add_zero]
    have h1 : 2 ^ padicValNat 2 j ≤ j := Nat.le_of_dvd (by omega) pow_padicValNat_dvd
    have h2 : j < 2 ^ j := Nat.lt_two_pow_self
    have : padicValNat 2 j < j := (Nat.pow_lt_pow_iff_right (by norm_num)).mp (h1.trans_lt h2)
    omega
  omega

lemma core (q n : ℕ) (hq : 3 ≤ q) (hn : 0 < n) (hn2 : Even n) :
    let F : ℤ := ∑ k ∈ range (q + 1),
      if Even k then (q.choose k : ℤ) * (-((n ^ 2 : ℕ) : ℤ)) ^ (k / 2) else 0
    F ≠ 1 ∧ F ≠ -1 := by
  intro F
  set u := n ^ 2 with hu
  have hu0 : 0 < u := by positivity
  have hu4 : 4 ∣ u := by
    obtain ⟨m, rfl⟩ := hn2; exact ⟨m * m, by rw [hu]; ring⟩
  -- terms with k ≥ 2 are divisible by u
  have mod4 : (4 : ℤ) ∣ F - 1 := by
    have hF : F - 1 = ∑ k ∈ range (q + 1),
        ((if Even k then (q.choose k : ℤ) * (-(u : ℤ)) ^ (k / 2) else 0) - if k = 0 then 1 else 0) := by
      rw [sum_sub_distrib, sum_ite_eq' (range (q + 1)) 0 (fun _ => (1 : ℤ))]
      simp only [mem_range, show 0 < q + 1 by omega, if_true]
      rfl
    rw [hF]
    refine dvd_sum fun k _ => ?_
    by_cases hk0 : k = 0
    · subst hk0; simp
    · rw [if_neg hk0, sub_zero]
      split_ifs with hk
      · have : 1 ≤ k / 2 := by obtain ⟨j, rfl⟩ := hk; omega
        refine Dvd.dvd.mul_left ?_ _
        rw [← Nat.sub_add_cancel this, pow_succ]
        refine Dvd.dvd.mul_left ?_ _
        exact (dvd_neg).mpr (by exact_mod_cast hu4)
      · simp
  set e := padicValNat 2 (q.choose 2 * u) with he
  have hne : q.choose 2 * u ≠ 0 := mul_ne_zero (Nat.choose_pos (by omega)).ne' hu0.ne'
  have he1 : 2 ^ e ∣ q.choose 2 * u := pow_padicValNat_dvd
  have he2 : ¬ 2 ^ (e + 1) ∣ q.choose 2 * u := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact pow_succ_padicValNat_not_dvd hne
  have big : (2 : ℤ) ^ (e + 1) ∣ F - 1 + (q.choose 2 : ℤ) * u := by
    have hF : F - 1 + (q.choose 2 : ℤ) * u = ∑ k ∈ range (q + 1),
        ((if Even k then (q.choose k : ℤ) * (-(u : ℤ)) ^ (k / 2) else 0) - (if k = 0 then 1 else 0)
          + if k = 2 then (q.choose 2 : ℤ) * u else 0) := by
      rw [sum_add_distrib, sum_sub_distrib, sum_ite_eq' (range (q + 1)) 0 (fun _ => (1 : ℤ)),
        sum_ite_eq' (range (q + 1)) 2 (fun _ => (q.choose 2 : ℤ) * u)]
      simp only [mem_range, show 0 < q + 1 by omega, show 2 < q + 1 by omega, if_true]
      rfl
    rw [hF]
    refine dvd_sum fun k hk => ?_
    rw [mem_range] at hk
    by_cases hk0 : k = 0
    · subst hk0; simp
    by_cases hk2 : k = 2
    · subst hk2; simp
    rw [if_neg hk0, if_neg hk2, sub_zero, add_zero]
    split_ifs with hke
    · have h4 : 4 ≤ k := by obtain ⟨j, rfl⟩ := hke; omega
      have := term_dvd q k u e hu4 hu0 h4 (by omega) he1 hke
      rw [neg_pow, mul_comm ((-1 : ℤ) ^ _), ← mul_assoc]
      refine Dvd.dvd.mul_right ?_ _
      exact_mod_cast this
    · simp
  constructor
  · intro h1
    rw [h1, sub_self, zero_add] at big
    exact he2 (by exact_mod_cast big)
  · intro h1
    rw [h1] at mod4
    norm_num at mod4

lemma unit_pow_four (u : GaussianIntˣ) : (u : GaussianInt) ^ 4 = 1 := by
  have hn : (u : GaussianInt).norm = 1 := by
    have h := (Zsqrtd.norm_eq_one_iff' (by norm_num) (u : GaussianInt)).mpr u.isUnit
    exact h
  set x := (u : GaussianInt) with hx
  have hn' : x.re * x.re + x.im * x.im = 1 := by
    have := hn; simp [Zsqrtd.norm] at this; linarith
  have hre : x.re ≤ 1 ∧ -1 ≤ x.re := by constructor <;> nlinarith [mul_self_nonneg x.im]
  have him : x.im ≤ 1 ∧ -1 ≤ x.im := by constructor <;> nlinarith [mul_self_nonneg x.re]
  obtain ⟨a, b⟩ := x
  simp only at hre him hn'
  have : (⟨a, b⟩ : GaussianInt) ^ 4 = ⟨a, b⟩ * ⟨a, b⟩ * (⟨a, b⟩ * ⟨a, b⟩) := by ring
  rw [this]
  obtain ⟨h1, h2⟩ := hre
  obtain ⟨h3, h4⟩ := him
  interval_cases a <;> interval_cases b <;> simp at hn' <;> decide

theorem lebesgue (a b q : ℕ) (ha : 0 < a) (hq : q.Prime) : b ^ q ≠ a ^ 2 + 1 := by
  intro h
  rcases hq.eq_two_or_odd' with rfl | hodd
  · rcases Nat.lt_or_ge a b with hab | hab
    · nlinarith
    · have : b ^ 2 ≤ a ^ 2 := Nat.pow_le_pow_left hab 2
      omega
  have hq3 : 3 ≤ q := by
    have := hq.two_le
    rcases hodd with ⟨m, rfl⟩; omega
  -- a is even
  have haeven : Even a := by
    by_contra hao
    rw [Nat.not_even_iff_odd] at hao
    obtain ⟨c, rfl⟩ := hao
    have hmod : (b ^ q) % 4 = 2 := by
      rw [h]; ring_nf; omega
    rcases Nat.even_or_odd b with ⟨d, rfl⟩ | hbo
    · have : 4 ∣ (d + d) ^ q := by
        have : (d + d) ^ q = (d + d) ^ 2 * (d + d) ^ (q - 2) := by
          rw [← pow_add]; congr 1; omega
        rw [this]; exact Dvd.dvd.mul_right ⟨d * d, by ring⟩ _
      omega
    · have := hbo.pow (n := q)
      rw [Nat.odd_iff] at this
      omega
  have hbodd : Odd b := by
    rcases Nat.even_or_odd b with hb | hb
    · have : Even (a ^ 2 + 1) := h ▸ Even.pow_of_ne_zero (show Even b from hb) (by omega)
      rw [Nat.even_add_one] at this
      exact absurd (Even.pow_of_ne_zero haeven two_ne_zero) this
    · exact hb
  obtain ⟨c, hc⟩ := haeven
  set A : GaussianInt := ⟨a, 1⟩ with hA
  set B : GaussianInt := ⟨a, -1⟩ with hB
  have hbq : ((b : ℤ)) ^ q = (a : ℤ) ^ 2 + 1 := by exact_mod_cast h
  have hAB : A * B = (b : GaussianInt) ^ q := by
    have : (b : GaussianInt) ^ q = (((b : ℤ) ^ q : ℤ) : GaussianInt) := by push_cast; rfl
    rw [this, hbq]
    ext
    · rw [Zsqrtd.re_intCast]; simp [A, B]; ring
    · rw [Zsqrtd.im_intCast]; simp [A, B]
  have hcop : IsCoprime A B := by
    refine ⟨B + ⟨0, 2 * c ^ 2⟩, -⟨0, 2 * c ^ 2⟩, ?_⟩
    ext <;> simp [A, B, hc] <;> ring
  obtain ⟨d, hd⟩ := exists_associated_pow_of_mul_eq_pow' hcop hAB
  obtain ⟨u, hu⟩ := hd
  set γ : GaussianInt := d * (u : GaussianInt) ^ q with hγdef
  have hγ : γ ^ q = A := by
    obtain ⟨m, rfl⟩ := hodd
    have hu4 := unit_pow_four u
    rw [hγdef, mul_pow, ← pow_mul, ← hu]
    congr 1
    have : (2 * m + 1) * (2 * m + 1) = 4 * (m * m + m) + 1 := by ring
    rw [this, pow_succ, pow_mul, hu4, one_pow, one_mul]
  set r := γ.re with hr
  set s := γ.im with hs
  -- s = ±1
  have hs1 : s * s = 1 := by
    have hdvd := sub_dvd_pow_sub_pow γ (r : GaussianInt) q
    have h1 : γ - (r : GaussianInt) = ⟨0, s⟩ := by ext <;> simp [r, s]
    rw [h1, hγ] at hdvd
    obtain ⟨w, hw⟩ := hdvd
    have h2 := congrArg Zsqrtd.im hw
    have h3 : ((r : GaussianInt) ^ q).im = 0 := by
      rw [← Int.cast_pow, Zsqrtd.im_intCast]
    rw [Zsqrtd.im_sub, h3] at h2
    simp [A] at h2
    rcases Int.eq_one_or_neg_one_of_mul_eq_one h2.symm with h | h <;> rw [h] <;> norm_num
  -- the norm
  have hnorm : r * r + s * s = b := by
    have h1 := congrArg (Zsqrtd.normMonoidHom (d := -1)) hγ
    rw [map_pow] at h1
    simp [Zsqrtd.normMonoidHom, Zsqrtd.norm, A] at h1
    have hb' : ((b : ℤ)) ^ q = (r * r + s * s) ^ q := by
      rw [hbq]; rw [show r * r + s * s = γ.re * γ.re + γ.im * γ.im from rfl]; linarith
    exact ((pow_left_inj₀ (by positivity) (by nlinarith [mul_self_nonneg r, mul_self_nonneg s]) (by omega)).1 hb').symm
  have hrev : Even r := by
    by_contra hro
    rw [Int.not_even_iff_odd] at hro
    have h1 : Even (r * r + s * s) := by rw [hs1]; exact (hro.mul hro).add_odd odd_one
    rw [hnorm] at h1
    have h2 : Odd (b : ℤ) := hbodd.natCast
    exact (Int.not_even_iff_odd.mpr h2) h1
  have hr0 : r ≠ 0 := by
    intro h0
    rw [h0, hs1] at hnorm
    have hb1 : b = 1 := by omega
    rw [hb1, one_pow] at h
    nlinarith
  set z : GaussianInt := ⟨0, s * r⟩ with hz
  have hγz : γ = ⟨0, s⟩ * (1 - z) := by
    ext
    · simp [z]; linear_combination (-r) * hs1
    · simp [z, hs]
  have hstar : star γ = -⟨0, s⟩ * (1 + z) := by
    ext
    · simp [z]; linear_combination (-r) * hs1
    · simp [z, hs]
  have hBq : (star γ) ^ q = B := by
    rw [← star_pow, hγ]; rfl
  have key : (⟨0, s⟩ : GaussianInt) ^ q * ((1 - z) ^ q + (1 + z) ^ q) = ⟨0, 2⟩ := by
    have hAB2 : A - B = ⟨0, 2⟩ := by ext <;> simp [A, B]
    rw [← hAB2, ← hγ, ← hBq, hstar, hγz, mul_pow, mul_pow, hodd.neg_pow]
    ring
  rw [two_sum] at key
  set n := r.natAbs with hn
  set F : ℤ := ∑ k ∈ Finset.range (q + 1),
      if Even k then (q.choose k : ℤ) * (-((n ^ 2 : ℕ) : ℤ)) ^ (k / 2) else 0 with hF
  have hz2 : z ^ 2 = (((-((n ^ 2 : ℕ) : ℤ)) : ℤ) : GaussianInt) := by
    ext
    · rw [Zsqrtd.re_intCast]; simp [z, sq, hn]
      linear_combination (r * r) * hs1
    · rw [Zsqrtd.im_intCast]; simp [z, sq]
  have hFc : (∑ k ∈ Finset.range (q + 1),
      if Even k then (q.choose k : GaussianInt) * (z ^ 2) ^ (k / 2) else 0) = (F : GaussianInt) := by
    rw [hF, Int.cast_sum, hz2]
    refine Finset.sum_congr rfl fun k _ => ?_
    split_ifs <;> push_cast <;> rfl
  rw [hFc] at key
  have hFF : F * F = 1 := by
    have h1 := congrArg (Zsqrtd.normMonoidHom (d := -1)) key
    simp only [map_mul, map_pow] at h1
    have h2 : Zsqrtd.normMonoidHom (⟨0, s⟩ : GaussianInt) = 1 := by
      simp [Zsqrtd.normMonoidHom, Zsqrtd.norm, hs1]
    have h3 : Zsqrtd.normMonoidHom (2 : GaussianInt) = 4 := by
      simp [Zsqrtd.normMonoidHom, Zsqrtd.norm]
    have h4 : Zsqrtd.normMonoidHom (F : GaussianInt) = F * F := by
      simp [Zsqrtd.normMonoidHom, Zsqrtd.norm]
    have h5 : Zsqrtd.normMonoidHom (⟨0, 2⟩ : GaussianInt) = 4 := by
      simp [Zsqrtd.normMonoidHom, Zsqrtd.norm]
    rw [h2, h3, h4, h5, one_pow, one_mul] at h1
    linarith
  have hnpos : 0 < n := Int.natAbs_pos.mpr hr0
  have hneven : Even n := Int.natAbs_even.mpr hrev
  obtain ⟨c1, c2⟩ := core q n hq3 hnpos hneven
  rcases Int.eq_one_or_neg_one_of_mul_eq_one hFF with h1 | h1
  · exact c1 h1
  · exact c2 h1

end OMA.Lebesgue

theorem OMA.solution : OMA.R_OeisA219791_conjecture_2_R2.H2 :=
  fun a b q ha hq => OMA.Lebesgue.lebesgue a b q ha hq
