import OMAStatements.S_oeis_a278415
import Mathlib

/-!
# A278415: Sun's supercongruence a(pn) = a(n) mod (pn)^2

Original proof. With r = v_p(p n), write 2 a(n) = b(n) + D(n), where
- b(n) = [u^n] Phi(u)^n with Phi = (1+u+u^2)/(1+u^2) = (1+u)(1-u^3)/(1-u^4), so b(n) is a sum
  over index triples of products of C(n,i), C(n,j) and C(n+k-1,k);
- D(n) = Sum_k (-1)^k C(n,2k) m(n,k) with the cyclic factor m(n,k) = (n/(n-k)) C(n-k,k).
In both sums every term whose index is not a multiple of p carries two factors divisible by p^r,
and the multiples are handled by the elementary congruence C(pn,pk) = C(n,k) mod p^(2+2v_p(n))
(and its negative-binomial twin), proved through the symmetric product of (y+i) over 0<i<pk,
p not dividing i.
-/

open OMA.S_oeis_a278415

open Finset

namespace OMA.A278415Proof

/-! ## Part 1: a Jacobsthal-type congruence `C(pn,pk) = C(n,k) mod p^(2+2v(n))` -/

/-- The indices `0 < i < p*k` with `p` not dividing `i`. -/
def S (p k : ℕ) : Finset ℕ := (range (p * k)).filter (fun i => ¬ p ∣ i)

/-- `g(y) = prod over S of (y + i)`. -/
def g (p k : ℕ) (y : ℤ) : ℤ := ∏ i ∈ S p k, (y + (i : ℤ))

noncomputable def G (p k : ℕ) : Polynomial ℤ :=
  ∏ i ∈ S p k, (Polynomial.X + Polynomial.C (i : ℤ))

lemma eval_G (p k : ℕ) (y : ℤ) : (G p k).eval y = g p k y := by
  simp [G, g, Polynomial.eval_prod]

lemma filter_dvd_range (p k : ℕ) (hp : 0 < p) :
    (range (p * k)).filter (fun i => p ∣ i) = (range k).image (fun j => p * j) := by
  ext x
  simp only [mem_filter, mem_range, mem_image]
  constructor
  · rintro ⟨hx, j, rfl⟩
    exact ⟨j, (Nat.mul_lt_mul_left hp).mp hx, rfl⟩
  · rintro ⟨j, hj, rfl⟩
    exact ⟨(Nat.mul_lt_mul_left hp).mpr hj, dvd_mul_right p j⟩

lemma card_S (p k : ℕ) (hp : 0 < p) : (S p k).card = p * k - k := by
  have h := Finset.card_filter_add_card_filter_not (s := range (p * k)) (fun i => p ∣ i)
  rw [filter_dvd_range p k hp, card_image_of_injective _ (fun a b h => Nat.eq_of_mul_eq_mul_left hp h),
    card_range, card_range] at h
  unfold S
  omega

lemma even_card_S (p k : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) : Even (S p k).card := by
  rw [card_S p k hp.pos, ← Nat.sub_one_mul]
  exact (hp.even_sub_one hp2).mul_right k

lemma prod_split (p k : ℕ) (hp : 0 < p) (f : ℕ → ℤ) :
    ∏ i ∈ range (p * k), f i = (∏ j ∈ range k, f (p * j)) * ∏ i ∈ S p k, f i := by
  rw [← prod_filter_mul_prod_filter_not (range (p * k)) (fun i => p ∣ i), filter_dvd_range p k hp,
    prod_image (fun a _ b _ h => Nat.eq_of_mul_eq_mul_left hp h)]
  rfl

lemma prod_sub_eq (p k : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (x : ℤ) :
    ∏ i ∈ S p k, (x - (i : ℤ)) = g p k (-x) := by
  unfold g
  rw [show (∏ i ∈ S p k, (x - (i : ℤ))) = ∏ i ∈ S p k, ((-1) * (-x + i)) from
    prod_congr rfl (fun i _ => by ring), prod_mul_distrib, prod_const,
    (even_card_S p k hp hp2).neg_one_pow, one_mul]

lemma g_sym (p k : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) : g p k (-((p : ℤ) * k)) = g p k 0 := by
  have h : ∏ i ∈ S p k, (-((p : ℤ) * k) + i) = ∏ i ∈ S p k, (-((p : ℤ) * k) + ((p * k - i : ℕ) : ℤ)) := by
    apply prod_nbij' (fun i => p * k - i) (fun i => p * k - i)
    · intro a ha
      simp only [S, mem_filter, mem_range] at ha ⊢
      have ha0 : a ≠ 0 := by rintro rfl; exact ha.2 (dvd_zero p)
      refine ⟨by omega, fun h => ha.2 ?_⟩
      have := Nat.dvd_sub (dvd_mul_right p k) h
      rwa [Nat.sub_sub_self ha.1.le] at this
    · intro a ha
      simp only [S, mem_filter, mem_range] at ha ⊢
      have ha0 : a ≠ 0 := by rintro rfl; exact ha.2 (dvd_zero p)
      refine ⟨by omega, fun h => ha.2 ?_⟩
      have := Nat.dvd_sub (dvd_mul_right p k) h
      rwa [Nat.sub_sub_self ha.1.le] at this
    · intro a ha
      simp only [S, mem_filter, mem_range] at ha
      omega
    · intro a ha
      simp only [S, mem_filter, mem_range] at ha
      omega
    · intro a ha
      simp only [S, mem_filter, mem_range] at ha
      rw [Nat.sub_sub_self ha.1.le]
  unfold g
  rw [h, show (∏ i ∈ S p k, (-((p : ℤ) * k) + ((p * k - i : ℕ) : ℤ)))
      = ∏ i ∈ S p k, ((-1) * (0 + (i : ℤ))) from prod_congr rfl (fun i hi => by
        simp only [S, mem_filter, mem_range] at hi
        push_cast [Nat.cast_sub hi.1.le]
        ring),
    prod_mul_distrib, prod_const, (even_card_S p k hp hp2).neg_one_pow, one_mul]

lemma desc_eq_prod (n k : ℕ) : (n.descFactorial k : ℤ) = ∏ i ∈ range k, ((n : ℤ) - i) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.descFactorial_succ, prod_range_succ, ← ih]
    rcases le_or_gt k n with h | h
    · push_cast [Nat.cast_sub h]; ring
    · rw [Nat.descFactorial_eq_zero_iff_lt.mpr h]; simp

lemma asc_eq_prod (n k : ℕ) : (n.ascFactorial k : ℤ) = ∏ i ∈ range k, ((n : ℤ) + i) := by
  induction k with
  | zero => simp
  | succ k ih => rw [Nat.ascFactorial_succ, prod_range_succ, ← ih]; push_cast; ring

lemma desc_split (p n k : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    (((p * n).descFactorial (p * k) : ℕ) : ℤ)
      = (p : ℤ) ^ k * (n.descFactorial k : ℤ) * g p k (-((p : ℤ) * n)) := by
  rw [desc_eq_prod, prod_split p k hp.pos, desc_eq_prod, ← prod_sub_eq p k hp hp2]
  congr 1
  · rw [show ∏ j ∈ range k, (((p * n : ℕ) : ℤ) - ((p * j : ℕ) : ℤ))
        = ∏ j ∈ range k, ((p : ℤ) * ((n : ℤ) - j)) from prod_congr rfl (fun j _ => by push_cast; ring),
      prod_mul_distrib, prod_const, card_range]

lemma asc_split (p n k : ℕ) (hp : p.Prime) :
    (((p * n).ascFactorial (p * k) : ℕ) : ℤ)
      = (p : ℤ) ^ k * (n.ascFactorial k : ℤ) * g p k ((p : ℤ) * n) := by
  rw [asc_eq_prod, prod_split p k hp.pos, asc_eq_prod]
  unfold g
  congr 1
  · rw [show ∏ j ∈ range k, (((p * n : ℕ) : ℤ) + ((p * j : ℕ) : ℤ))
        = ∏ j ∈ range k, ((p : ℤ) * ((n : ℤ) + j)) from prod_congr rfl (fun j _ => by push_cast; ring),
      prod_mul_distrib, prod_const, card_range]

lemma fact_split (p k : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    (((p * k).factorial : ℕ) : ℤ) = (p : ℤ) ^ k * (k.factorial : ℤ) * g p k 0 := by
  have h := desc_split p k k hp hp2
  rwa [Nat.descFactorial_self, Nat.descFactorial_self, g_sym p k hp hp2] at h

lemma choose_mul_g (p n k : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    ((p * n).choose (p * k) : ℤ) * g p k 0 = (n.choose k : ℤ) * g p k (-((p : ℤ) * n)) := by
  have h1 := desc_split p n k hp hp2
  have h2 := fact_split p k hp hp2
  rw [Nat.descFactorial_eq_factorial_mul_choose, Nat.descFactorial_eq_factorial_mul_choose] at h1
  push_cast at h1 h2
  rw [h2] at h1
  have hne : (p : ℤ) ^ k * (k.factorial : ℤ) ≠ 0 := by
    have := hp.pos; have := Nat.factorial_pos k; positivity
  apply mul_left_cancel₀ hne
  linear_combination h1

lemma choose_mul_g' (p n k : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hn : 0 < n) :
    ((p * n + p * k - 1).choose (p * k) : ℤ) * g p k 0
      = ((n + k - 1).choose k : ℤ) * g p k ((p : ℤ) * n) := by
  have h1 := asc_split p n k hp
  have h2 := fact_split p k hp hp2
  have hpn : 0 < p * n := Nat.mul_pos hp.pos hn
  have e1 : (p * n - 1 + 1).ascFactorial (p * k) = (p * k).factorial * (p * n - 1 + p * k).choose (p * k) :=
    Nat.ascFactorial_eq_factorial_mul_choose _ _
  have e2 : (n - 1 + 1).ascFactorial k = k.factorial * (n - 1 + k).choose k :=
    Nat.ascFactorial_eq_factorial_mul_choose _ _
  rw [Nat.sub_add_cancel hpn] at e1
  rw [Nat.sub_add_cancel hn] at e2
  rw [e1, e2] at h1
  rw [show p * n + p * k - 1 = p * n - 1 + p * k by omega, show n + k - 1 = n - 1 + k by omega]
  push_cast at h1 h2
  rw [h2] at h1
  have hne : (p : ℤ) ^ k * (k.factorial : ℤ) ≠ 0 := by
    have := hp.pos; have := Nat.factorial_pos k; positivity
  apply mul_left_cancel₀ hne
  linear_combination h1

/-- Coprime cancellation. -/
lemma cop_dvd (p : ℕ) (hp : p.Prime) (t : ℕ) (ht : ¬ p ∣ t) (e : ℕ) (x : ℤ)
    (h : (p : ℤ) ^ e ∣ (t : ℤ) * x) : (p : ℤ) ^ e ∣ x := by
  have hc : IsCoprime ((p : ℤ) ^ e) (t : ℤ) := by
    have h1 : Nat.Coprime (p ^ e) t :=
      Nat.Coprime.pow_left e ((Nat.Prime.coprime_iff_not_dvd hp).mpr ht)
    have h2 := Nat.isCoprime_iff_coprime.mpr h1
    push_cast at h2
    exact h2
  exact hc.dvd_of_dvd_mul_left h

lemma g_zero (p k : ℕ) : g p k 0 = ((∏ i ∈ S p k, i : ℕ) : ℤ) := by
  simp [g]

lemma not_dvd_g0 (p k : ℕ) (hp : p.Prime) : ¬ p ∣ ∏ i ∈ S p k, i := by
  apply Prime.not_dvd_finsetProd hp.prime
  intro a ha
  exact (mem_filter.mp ha).2

/-- The core estimate. -/
lemma core (p k s : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hk : 0 < k) (A e c X : ℤ)
    (hX : X * g p k 0 = c * g p k ((p : ℤ) * A))
    (h1 : (p : ℤ) ^ (2 * s) ∣ e * c * k * A) (h2 : (p : ℤ) ^ (2 * s) ∣ e * c * A ^ 2) :
    (p : ℤ) ^ (2 * s + 2) ∣ e * (X - c) := by
  obtain ⟨T1, hT1⟩ := Polynomial.binomExpansion (G p k) 0 (-((p : ℤ) * k))
  obtain ⟨T2, hT2⟩ := Polynomial.binomExpansion (G p k) 0 ((p : ℤ) * A)
  simp only [zero_add, eval_G] at hT1 hT2
  rw [g_sym p k hp hp2] at hT1
  set D := (Polynomial.derivative (G p k)).eval 0
  have hpk : ((p : ℤ) * k) ≠ 0 := by have := hp.pos; positivity
  have hD : D = T1 * (p * k) := by
    have : D * (p * k) = T1 * (p * k) * (p * k) := by linear_combination hT1
    exact mul_right_cancel₀ hpk this
  have key : g p k 0 * (e * (X - c))
      = (p : ℤ) ^ 2 * (T1 * (e * c * k * A) + T2 * (e * c * A ^ 2)) := by
    linear_combination e * hX + e * c * hT2 + e * c * p * A * hD
  have hdvd : (p : ℤ) ^ (2 * s + 2) ∣ g p k 0 * (e * (X - c)) := by
    rw [key, pow_add, mul_comm ((p : ℤ) ^ (2 * s))]
    exact mul_dvd_mul_left _ (dvd_add (dvd_mul_of_dvd_right h1 _) (dvd_mul_of_dvd_right h2 _))
  rw [g_zero] at hdvd
  exact cop_dvd p hp _ (not_dvd_g0 p k hp) _ _ hdvd

lemma k_mul_choose (n k : ℕ) (hk : 0 < k) : n ∣ k * n.choose k := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [Nat.choose_eq_zero_of_lt hk]
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  exact ⟨n'.choose k', by rw [Nat.add_one_mul_choose_eq]; ring⟩

lemma k_mul_choose' (n k : ℕ) (hk : 0 < k) : n ∣ k * (n + k - 1).choose k := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [Nat.choose_eq_zero_of_lt (by omega : 0 + k - 1 < k)]; simp
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  refine ⟨(n' + k' + 1).choose k', ?_⟩
  rw [show n' + 1 + (k' + 1) - 1 = n' + k' + 1 by omega, mul_comm, Nat.choose_succ_right_eq,
    show n' + k' + 1 - k' = n' + 1 by omega, mul_comm]

lemma dvd_pow2 (p s : ℕ) {x y z : ℤ} (w : ℤ) (hx : (p : ℤ) ^ s ∣ x) (hy : (p : ℤ) ^ s ∣ y)
    (h : z = x * y * w) : (p : ℤ) ^ (2 * s) ∣ z := by
  rw [h, two_mul, pow_add]; exact dvd_mul_of_dvd_left (mul_dvd_mul hx hy) w

lemma natdvd {p s n : ℕ} (h : p ^ s ∣ n) : (p : ℤ) ^ s ∣ (n : ℤ) := by
  exact_mod_cast Int.natCast_dvd_natCast.mpr h

lemma JL1 (p n k s : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hn : p ^ s ∣ n) :
    (p : ℤ) ^ (2 * s + 2) ∣ ((p * n).choose (p * k) : ℤ) - (n.choose k : ℤ) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  have hkc : (p : ℤ) ^ s ∣ (k : ℤ) * (n.choose k : ℤ) := by
    exact_mod_cast natdvd (hn.trans (k_mul_choose n k hk))
  have := core p k s hp hp2 hk (-(n : ℤ)) 1 (n.choose k) ((p * n).choose (p * k)) ?_ ?_ ?_
  · simpa using this
  · rw [choose_mul_g p n k hp hp2]; ring_nf
  · exact dvd_pow2 p s (-1) hkc (natdvd hn) (by ring)
  · exact dvd_pow2 p s (n.choose k) (natdvd hn) (natdvd hn) (by ring)

lemma JL2 (p n k s : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hn0 : 0 < n) (hn : p ^ s ∣ n) :
    (p : ℤ) ^ (2 * s + 2) ∣ ((p * n + p * k - 1).choose (p * k) : ℤ) - ((n + k - 1).choose k : ℤ) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  have hkc : (p : ℤ) ^ s ∣ (k : ℤ) * ((n + k - 1).choose k : ℤ) := by
    exact_mod_cast natdvd (hn.trans (k_mul_choose' n k hk))
  have := core p k s hp hp2 hk (n : ℤ) 1 ((n + k - 1).choose k) ((p * n + p * k - 1).choose (p * k)) ?_ ?_ ?_
  · simpa using this
  · rw [choose_mul_g' p n k hp hp2 hn0]
  · exact dvd_pow2 p s 1 hkc (natdvd hn) (by ring)
  · exact dvd_pow2 p s ((n + k - 1).choose k) (natdvd hn) (natdvd hn) (by ring)

/-! ## Part 2: power series with sparse binomial coefficients -/

open PowerSeries

/-- `(1 + c X^d)^N`. -/
noncomputable def Ps (c : ℤ) (d N : ℕ) : PowerSeries ℤ :=
  PowerSeries.mk fun m => if d ∣ m then c ^ (m / d) * (N.choose (m / d) : ℤ) else 0

/-- `(1 - c X^d)^(-N)`. -/
noncomputable def Ng (c : ℤ) (d N : ℕ) : PowerSeries ℤ :=
  PowerSeries.mk fun m => if d ∣ m then c ^ (m / d) * ((N + m / d - 1).choose (m / d) : ℤ) else 0

lemma coeff_mul_shift (f : PowerSeries ℤ) (c : ℤ) (d m : ℕ) :
    coeff m (f * (C c * X ^ d)) = c * (if d ≤ m then coeff (m - d) f else 0) := by
  rw [mul_left_comm, coeff_C_mul, coeff_mul_X_pow']

lemma not_dvd_sub {d m : ℕ} (hm : ¬ d ∣ m) (h1 : d ≤ m) : ¬ d ∣ m - d := by
  intro h2
  have := Nat.dvd_add h2 (dvd_refl d)
  rw [Nat.sub_add_cancel h1] at this
  exact hm this

lemma Ps_succ (c : ℤ) (d N : ℕ) (hd : 0 < d) : Ps c d (N + 1) = Ps c d N * (1 + C c * X ^ d) := by
  ext m
  rw [mul_add, mul_one, map_add, coeff_mul_shift]
  simp only [Ps, coeff_mk]
  by_cases hm : d ∣ m
  · obtain ⟨t, rfl⟩ := hm
    rw [if_pos (dvd_mul_right d t), if_pos (dvd_mul_right d t), Nat.mul_div_cancel_left t hd]
    cases t with
    | zero => simp [hd.ne']
    | succ t =>
      rw [if_pos (Nat.le_mul_of_pos_right _ (Nat.succ_pos t)),
        show d * (t + 1) - d = d * t by rw [Nat.mul_succ]; omega, if_pos (dvd_mul_right d t),
        Nat.mul_div_cancel_left t hd, Nat.choose_succ_succ']
      push_cast; ring
  · rw [if_neg hm, if_neg hm]
    split_ifs with h1 h2
    · exact absurd h2 (not_dvd_sub hm h1)
    · simp
    · simp

lemma Ps_zero (c : ℤ) (d : ℕ) (hd : 0 < d) : Ps c d 0 = 1 := by
  ext m
  simp only [Ps, coeff_mk, coeff_one]
  by_cases hm : d ∣ m
  · obtain ⟨t, rfl⟩ := hm
    rw [if_pos (dvd_mul_right d t), Nat.mul_div_cancel_left t hd]
    cases t with
    | zero => simp
    | succ t => simp [hd.ne']
  · rw [if_neg hm, if_neg (by rintro rfl; exact hm (dvd_zero d))]

lemma Ng_succ (c : ℤ) (d N : ℕ) (hd : 0 < d) : Ng c d (N + 1) * (1 - C c * X ^ d) = Ng c d N := by
  ext m
  rw [mul_sub, mul_one, map_sub, coeff_mul_shift]
  simp only [Ng, coeff_mk]
  by_cases hm : d ∣ m
  · obtain ⟨t, rfl⟩ := hm
    rw [if_pos (dvd_mul_right d t), if_pos (dvd_mul_right d t), Nat.mul_div_cancel_left t hd]
    cases t with
    | zero => simp [hd.ne']
    | succ t =>
      rw [if_pos (Nat.le_mul_of_pos_right _ (Nat.succ_pos t)),
        show d * (t + 1) - d = d * t by rw [Nat.mul_succ]; omega, if_pos (dvd_mul_right d t),
        Nat.mul_div_cancel_left t hd,
        show N + 1 + (t + 1) - 1 = (N + t) + 1 by omega, show N + 1 + t - 1 = N + t by omega,
        show N + (t + 1) - 1 = N + t by omega, Nat.choose_succ_succ']
      push_cast; ring
  · rw [if_neg hm, if_neg hm]
    split_ifs with h1 h2
    · exact absurd h2 (not_dvd_sub hm h1)
    · simp
    · simp

lemma Ng_zero (c : ℤ) (d : ℕ) (hd : 0 < d) : Ng c d 0 = 1 := by
  ext m
  simp only [Ng, coeff_mk, coeff_one]
  by_cases hm : d ∣ m
  · obtain ⟨t, rfl⟩ := hm
    rw [if_pos (dvd_mul_right d t), Nat.mul_div_cancel_left t hd]
    cases t with
    | zero => simp
    | succ t => simp [hd.ne']
  · rw [if_neg hm, if_neg (by rintro rfl; exact hm (dvd_zero d))]

lemma Ps_eq (c : ℤ) (d N : ℕ) (hd : 0 < d) : Ps c d N = (1 + C c * X ^ d) ^ N := by
  induction N with
  | zero => rw [Ps_zero c d hd, pow_zero]
  | succ N ih => rw [Ps_succ c d N hd, ih, pow_succ]

lemma Ng_one (c : ℤ) (d : ℕ) (hd : 0 < d) : Ng c d 1 * (1 - C c * X ^ d) = 1 := by
  have := Ng_succ c d 0 hd
  rwa [Ng_zero c d hd] at this

lemma Ng_pow (c : ℤ) (d N : ℕ) (hd : 0 < d) : Ng c d N = (Ng c d 1) ^ N := by
  induction N with
  | zero => rw [Ng_zero c d hd, pow_zero]
  | succ N ih =>
    calc Ng c d (N + 1) = Ng c d (N + 1) * (Ng c d 1 * (1 - C c * X ^ d)) := by
          rw [Ng_one c d hd, mul_one]
      _ = (Ng c d (N + 1) * (1 - C c * X ^ d)) * Ng c d 1 := by ring
      _ = Ng c d 1 ^ (N + 1) := by rw [Ng_succ c d N hd, ih, pow_succ]

/-- `Phi = 1 + X / (1 + X^2) = (1 + X + X^2) / (1 + X^2)`. -/
noncomputable def Phi : PowerSeries ℤ := 1 + X * Ng (-1) 2 1

lemma Phi_eq : Ps 1 1 1 * Ps (-1) 3 1 * Ng 1 4 1 = Phi := by
  have hu := Ng_one 1 4 (by norm_num)
  have hw := Ng_one (-1) 2 (by norm_num)
  rw [Ps_eq 1 1 1 (by norm_num), Ps_eq (-1) 3 1 (by norm_num)]
  simp only [map_one, map_neg, pow_one, one_mul] at hu hw ⊢
  unfold Phi
  linear_combination (1 + X * Ng (-1) 2 1) * hu - Ng 1 4 1 * X * (1 - X ^ 2) * hw

lemma Phi_pow (N : ℕ) : Phi ^ N = Ps 1 1 N * Ps (-1) 3 N * Ng 1 4 N := by
  rw [← Phi_eq, mul_pow, mul_pow, ← Ng_pow 1 4 N (by norm_num), Ps_eq 1 1 1 (by norm_num),
    Ps_eq (-1) 3 1 (by norm_num), Ps_eq 1 1 N (by norm_num), Ps_eq (-1) 3 N (by norm_num)]
  simp only [pow_one]

/-- The coefficient relation: `f` has coefficients divisible by `p^r` away from multiples of `p`,
and `f_(p m) = f'_m mod p^(2r)`. -/
def Rel (p r : ℕ) (f f' : PowerSeries ℤ) : Prop :=
  (∀ m, ¬ p ∣ m → (p : ℤ) ^ r ∣ coeff m f) ∧ (∀ m, (p : ℤ) ^ (2 * r) ∣ coeff (p * m) f - coeff m f')

lemma sum_split (p n : ℕ) (hp : 0 < p) (F : ℕ → ℤ) :
    ∑ k ∈ range (p * n + 1), F k
      = ∑ j ∈ range (n + 1), F (p * j) + ∑ k ∈ (range (p * n + 1)).filter (fun k => ¬ p ∣ k), F k := by
  rw [← sum_filter_add_sum_filter_not (range (p * n + 1)) (fun k => p ∣ k)]
  congr 1
  have : (range (p * n + 1)).filter (fun k => p ∣ k) = (range (n + 1)).image (fun j => p * j) := by
    ext x
    simp only [mem_filter, mem_range, mem_image]
    constructor
    · rintro ⟨hx, j, rfl⟩
      refine ⟨j, ?_, rfl⟩
      by_contra h
      push Not at h
      nlinarith
    · rintro ⟨j, hj, rfl⟩
      exact ⟨by nlinarith, dvd_mul_right p j⟩
  rw [this, sum_image (fun a _ b _ h => Nat.eq_of_mul_eq_mul_left hp h)]

lemma Rel.mul {p r : ℕ} (hp : p.Prime) {f f' h h' : PowerSeries ℤ} (hf : Rel p r f f')
    (hh : Rel p r h h') : Rel p r (f * h) (f' * h') := by
  constructor
  · intro m hm
    rw [coeff_mul]
    apply Finset.dvd_sum
    intro x hx
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
    by_cases h1 : p ∣ x.1
    · have h2 : ¬ p ∣ x.2 := fun h2 => hm (hx ▸ dvd_add h1 h2)
      exact dvd_mul_of_dvd_right (hh.1 _ h2) _
    · exact dvd_mul_of_dvd_left (hf.1 _ h1) _
  · intro m
    rw [coeff_mul, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Nat.succ_eq_add_one, Nat.succ_eq_add_one,
      sum_split p m hp.pos, add_sub_right_comm, ← sum_sub_distrib]
    apply dvd_add
    · apply Finset.dvd_sum
      intro j hj
      rw [← Nat.mul_sub]
      have e : coeff (p * j) f * coeff (p * (m - j)) h - coeff j f' * coeff (m - j) h'
          = (coeff (p * j) f - coeff j f') * coeff (p * (m - j)) h
            + coeff j f' * (coeff (p * (m - j)) h - coeff (m - j) h') := by ring
      rw [e]
      exact dvd_add (dvd_mul_of_dvd_left (hf.2 j) _) (dvd_mul_of_dvd_right (hh.2 _) _)
    · apply Finset.dvd_sum
      intro k hk
      rw [mem_filter, mem_range] at hk
      have h2 : ¬ p ∣ p * m - k := fun h2 => hk.2 (by
        have := Nat.dvd_sub (dvd_mul_right p m) h2
        rwa [Nat.sub_sub_self (by omega)] at this)
      rw [two_mul, pow_add]
      exact mul_dvd_mul (hf.1 _ hk.2) (hh.1 _ h2)

lemma kum (p r N t : ℕ) (hp : p.Prime) (hN : p ^ r ∣ N) (ht : ¬ p ∣ t) :
    (p : ℤ) ^ r ∣ (N.choose t : ℤ) := by
  have h0 : 0 < t := Nat.pos_of_ne_zero (by rintro rfl; exact ht (dvd_zero p))
  apply cop_dvd p hp t ht
  exact_mod_cast natdvd (hN.trans (k_mul_choose N t h0))

lemma kum' (p r N t : ℕ) (hp : p.Prime) (hN : p ^ r ∣ N) (ht : ¬ p ∣ t) :
    (p : ℤ) ^ r ∣ ((N + t - 1).choose t : ℤ) := by
  have h0 : 0 < t := Nat.pos_of_ne_zero (by rintro rfl; exact ht (dvd_zero p))
  apply cop_dvd p hp t ht
  exact_mod_cast natdvd (hN.trans (k_mul_choose' N t h0))

lemma pdvd (p s n : ℕ) (hn : p ^ s ∣ n) : p ^ (s + 1) ∣ p * n := by
  rw [pow_succ']; exact mul_dvd_mul_left p hn

lemma rel_Ps (p n s : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hn : p ^ s ∣ n) (c : ℤ) (hc : c ^ p = c)
    (d : ℕ) (hd : 0 < d) (hdp : Nat.Coprime d p) :
    Rel p (s + 1) (Ps c d (p * n)) (Ps c d n) := by
  constructor
  · intro m hm
    simp only [Ps, coeff_mk]
    split_ifs with h
    · obtain ⟨t, rfl⟩ := h
      rw [Nat.mul_div_cancel_left t hd]
      exact dvd_mul_of_dvd_right (kum p (s + 1) (p * n) t hp (pdvd p s n hn)
        (fun ht => hm (dvd_mul_of_dvd_right ht d))) _
    · exact dvd_zero _
  · intro m
    simp only [Ps, coeff_mk]
    by_cases h : d ∣ m
    · obtain ⟨t, rfl⟩ := h
      rw [if_pos (Dvd.dvd.mul_left (dvd_mul_right d t) p), if_pos (dvd_mul_right d t),
        show p * (d * t) / d = p * t by rw [mul_left_comm, Nat.mul_div_cancel_left _ hd],
        Nat.mul_div_cancel_left t hd, pow_mul c p t, hc, ← mul_sub, show 2 * (s + 1) = 2 * s + 2 by ring]
      exact dvd_mul_of_dvd_right (JL1 p n t s hp hp2 hn) _
    · have h' : ¬ d ∣ p * m := fun h' => h (hdp.dvd_of_dvd_mul_left h')
      rw [if_neg h', if_neg h, sub_zero]
      exact dvd_zero _

lemma rel_Ng (p n s : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hn0 : 0 < n) (hn : p ^ s ∣ n) (c : ℤ)
    (hc : c ^ p = c) (d : ℕ) (hd : 0 < d) (hdp : Nat.Coprime d p) :
    Rel p (s + 1) (Ng c d (p * n)) (Ng c d n) := by
  constructor
  · intro m hm
    simp only [Ng, coeff_mk]
    split_ifs with h
    · obtain ⟨t, rfl⟩ := h
      rw [Nat.mul_div_cancel_left t hd]
      exact dvd_mul_of_dvd_right (kum' p (s + 1) (p * n) t hp (pdvd p s n hn)
        (fun ht => hm (dvd_mul_of_dvd_right ht d))) _
    · exact dvd_zero _
  · intro m
    simp only [Ng, coeff_mk]
    by_cases h : d ∣ m
    · obtain ⟨t, rfl⟩ := h
      rw [if_pos (Dvd.dvd.mul_left (dvd_mul_right d t) p), if_pos (dvd_mul_right d t),
        show p * (d * t) / d = p * t by rw [mul_left_comm, Nat.mul_div_cancel_left _ hd],
        Nat.mul_div_cancel_left t hd, pow_mul c p t, hc, ← mul_sub, show 2 * (s + 1) = 2 * s + 2 by ring]
      exact dvd_mul_of_dvd_right (JL2 p n t s hp hp2 hn0 hn) _
    · have h' : ¬ d ∣ p * m := fun h' => h (hdp.dvd_of_dvd_mul_left h')
      rw [if_neg h', if_neg h, sub_zero]
      exact dvd_zero _

lemma cop_small (p d : ℕ) (hp : p.Prime) (hp3 : 3 < p) (hd : d ≤ 4) (hd0 : 0 < d) :
    Nat.Coprime d p := by
  apply Nat.Coprime.symm
  apply (Nat.Prime.coprime_iff_not_dvd hp).mpr
  intro h
  have := Nat.le_of_dvd hd0 h
  have hp4 : p ≤ 4 := by omega
  interval_cases p
  norm_num at hp

lemma B_part (p n s : ℕ) (hp : p.Prime) (hp3 : 3 < p) (hn0 : 0 < n) (hn : p ^ s ∣ n) :
    (p : ℤ) ^ (2 * s + 2) ∣ coeff (p * n) (Phi ^ (p * n)) - coeff n (Phi ^ n) := by
  have hp2 : p ≠ 2 := by omega
  have hodd : Odd p := hp.odd_of_ne_two hp2
  rw [Phi_pow, Phi_pow]
  have R := ((rel_Ps p n s hp hp2 hn 1 (one_pow p) 1 (by norm_num) (cop_small p 1 hp hp3 (by norm_num) (by norm_num))).mul hp
    (rel_Ps p n s hp hp2 hn (-1) hodd.neg_one_pow 3 (by norm_num) (cop_small p 3 hp hp3 (by norm_num) (by norm_num)))).mul hp
    (rel_Ng p n s hp hp2 hn0 hn 1 (one_pow p) 4 (by norm_num) (cop_small p 4 hp hp3 (by norm_num) (by norm_num)))
  have := R.2 n
  rwa [show 2 * (s + 1) = 2 * s + 2 by ring] at this

/-- The coefficient of `Phi^n` as a binomial sum. -/
lemma sum_range_two_mul (F : ℕ → ℤ) (N : ℕ) :
    ∑ m ∈ range (2 * N), F m = ∑ k ∈ range N, (F (2 * k) + F (2 * k + 1)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [show 2 * (N + 1) = 2 * N + 1 + 1 by ring, sum_range_succ, sum_range_succ, ih, sum_range_succ]
    ring

lemma coeff_Phi_pow (n : ℕ) :
    coeff n (Phi ^ n) = ∑ k ∈ range (n + 1),
      (-1 : ℤ) ^ k * (n.choose (2 * k) : ℤ) * ((n - k - 1).choose k : ℤ) := by
  have hw : ∀ j, (Ng (-1) 2 1) ^ j = Ng (-1) 2 j := fun j => (Ng_pow (-1) 2 j (by norm_num)).symm
  set F : ℕ → ℤ := fun m => (n.choose m : ℤ) *
    (if 2 ∣ m then (-1 : ℤ) ^ (m / 2) * ((n - m + m / 2 - 1).choose (m / 2) : ℤ) else 0) with hF
  have h1 : coeff n (Phi ^ n) = ∑ m ∈ range (n + 1), F m := by
    rw [Phi, add_pow, map_sum]
    apply sum_congr rfl
    intro m hm
    rw [mem_range] at hm
    rw [one_pow, one_mul, mul_pow, hw, ← map_natCast (C : ℤ →+* PowerSeries ℤ) (n.choose m),
      mul_comm, coeff_C_mul, coeff_X_pow_mul', if_pos (Nat.sub_le n m), Nat.sub_sub_self (by omega)]
    simp only [Ng, coeff_mk, hF]
  have h2 : ∑ m ∈ range (n + 1), F m = ∑ m ∈ range (2 * (n + 1)), F m := by
    apply sum_subset
    · intro x hx
      rw [mem_range] at *
      omega
    · intro x _ hx
      rw [mem_range] at hx
      simp only [hF]
      rw [Nat.choose_eq_zero_of_lt (by omega)]
      simp
  rw [h1, h2, sum_range_two_mul]
  apply sum_congr rfl
  intro k _
  have h3 : F (2 * k + 1) = 0 := by
    simp only [hF]
    rw [if_neg (by omega)]
    ring
  rw [h3, add_zero]
  simp only [hF]
  rw [if_pos (dvd_mul_right 2 k), Nat.mul_div_cancel_left k (by norm_num)]
  by_cases hk : 2 * k ≤ n
  · rw [show n - 2 * k + k - 1 = n - k - 1 by omega]
    ring
  · rw [Nat.choose_eq_zero_of_lt (by omega : n < 2 * k)]
    simp

/-! ## Part 3: the cyclic half `Dd` -/

def mm (n k : ℕ) : ℤ := 2 * ((n - k).choose k : ℤ) - ((n - k - 1).choose k : ℤ)

def Dd (n : ℕ) : ℤ := ∑ k ∈ range (n + 1), (-1 : ℤ) ^ k * (n.choose (2 * k) : ℤ) * mm n k

lemma mm_ids (n k : ℕ) (hk : 0 < k) (hkn : 2 * k ≤ n) :
    ((n - k : ℕ) : ℤ) * mm n k = n * ((n - k).choose k : ℤ) ∧
    (k : ℤ) * mm n k = n * ((n - k - 1).choose (k - 1) : ℤ) := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  obtain ⟨A, rfl⟩ : ∃ A, n = A + k' + 2 := ⟨n - k' - 2, by omega⟩
  have hP' : ((A + 1).choose (k' + 1) : ℤ) = (A.choose k' : ℤ) + (A.choose (k' + 1) : ℤ) := by
    exact_mod_cast Nat.choose_succ_succ' A k'
  have hM' : ((A : ℤ) + 1) * (A.choose k' : ℤ) = ((A + 1).choose (k' + 1) : ℤ) * ((k' : ℤ) + 1) := by
    exact_mod_cast Nat.add_one_mul_choose_eq A k'
  unfold mm
  rw [show A + k' + 2 - (k' + 1) = A + 1 by omega, show A + 1 - 1 = A by omega,
    show k' + 1 - 1 = k' by omega]
  push_cast
  constructor
  · linear_combination ((A : ℤ) + 1) * hP' + hM'
  · linear_combination ((k' : ℤ) + 1) * hP' - hM'

lemma D_part (p n s : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hn : p ^ s ∣ n) :
    (p : ℤ) ^ (2 * s + 2) ∣ Dd (p * n) - Dd n := by
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have h2p : ¬ p ∣ 2 := fun h => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h)
  unfold Dd
  rw [sum_split p n hp.pos, add_sub_right_comm, ← sum_sub_distrib]
  apply dvd_add
  · apply Finset.dvd_sum
    intro j _
    have hsign : (-1 : ℤ) ^ (p * j) = (-1) ^ j := by rw [pow_mul, hodd.neg_one_pow]
    rw [hsign, mul_assoc, mul_assoc, ← mul_sub]
    apply dvd_mul_of_dvd_right
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · simp [mm]
    by_cases hjn : 2 * j ≤ n
    · rw [show 2 * (p * j) = p * (2 * j) by ring]
      obtain ⟨hc1, hc2⟩ := mm_ids n j hj0 hjn
      obtain ⟨hX1, -⟩ := mm_ids (p * n) (p * j) (Nat.mul_pos hp.pos hj0) (by nlinarith)
      rw [(Nat.mul_sub p n j).symm] at hX1
      have hb := choose_mul_g p (n - j) j hp hp2
      have hnj : 0 < n - j := by omega
      have hXg : mm (p * n) (p * j) * g p j 0
          = mm n j * g p j ((p : ℤ) * (-((n - j : ℕ) : ℤ))) := by
        have hne : ((n - j : ℕ) : ℤ) * (p : ℤ) ≠ 0 := by have := hp.pos; positivity
        apply mul_left_cancel₀ hne
        rw [mul_neg]
        push_cast at hX1
        linear_combination g p j 0 * hX1 + (p : ℤ) * n * hb
          - (p : ℤ) * g p j (-((p : ℤ) * ((n - j : ℕ) : ℤ))) * hc1
      have hE : (p : ℤ) ^ s ∣ ((n - j : ℕ) : ℤ) * (n.choose (2 * j) : ℤ) := by
        apply cop_dvd p hp 2 h2p
        have h3 : (p : ℤ) ^ s ∣ ((2 * j : ℕ) : ℤ) * (n.choose (2 * j) : ℤ) :=
          natdvd (hn.trans (k_mul_choose n (2 * j) (by omega)))
        have h4 : ((2 : ℕ) : ℤ) * (((n - j : ℕ) : ℤ) * (n.choose (2 * j) : ℤ))
            = 2 * (n : ℤ) * (n.choose (2 * j) : ℤ) - ((2 * j : ℕ) : ℤ) * (n.choose (2 * j) : ℤ) := by
          push_cast [Nat.cast_sub (by omega : j ≤ n)]
          ring
        rw [h4]
        exact dvd_sub (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right (natdvd hn) _) _) h3
      have key := core p j s hp hp2 hj0 (-((n - j : ℕ) : ℤ)) (n.choose (2 * j) : ℤ) (mm n j)
        (mm (p * n) (p * j)) hXg ?_ ?_
      · have e : ((p * n).choose (p * (2 * j)) : ℤ) * mm (p * n) (p * j) - (n.choose (2 * j) : ℤ) * mm n j
            = (((p * n).choose (p * (2 * j)) : ℤ) - n.choose (2 * j)) * mm (p * n) (p * j)
              + (n.choose (2 * j) : ℤ) * (mm (p * n) (p * j) - mm n j) := by ring
        rw [e]
        exact dvd_add (dvd_mul_of_dvd_left (JL1 p n (2 * j) s hp hp2 hn) _) key
      · have hjc : (p : ℤ) ^ s ∣ (j : ℤ) * mm n j := by
          rw [hc2]; exact dvd_mul_of_dvd_left (natdvd hn) _
        exact dvd_pow2 p s (-1) hjc hE (by ring)
      · have hAc : (p : ℤ) ^ s ∣ ((n - j : ℕ) : ℤ) * mm n j := by
          rw [hc1]; exact dvd_mul_of_dvd_left (natdvd hn) _
        exact dvd_pow2 p s 1 hAc hE (by ring)
    · rw [Nat.choose_eq_zero_of_lt (by omega : n < 2 * j),
        Nat.choose_eq_zero_of_lt (show p * n < 2 * (p * j) from
          calc p * n < p * (2 * j) := (Nat.mul_lt_mul_left hp.pos).mpr (by omega)
            _ = 2 * (p * j) := by ring)]
      simp
  · apply Finset.dvd_sum
    intro k hk
    rw [mem_filter, mem_range] at hk
    have hk0 : 0 < k := Nat.pos_of_ne_zero (by rintro rfl; exact hk.2 (dvd_zero p))
    by_cases hkn : 2 * k ≤ p * n
    · have hC : (p : ℤ) ^ (s + 1) ∣ ((p * n).choose (2 * k) : ℤ) :=
        kum p (s + 1) (p * n) (2 * k) hp (pdvd p s n hn)
          (fun h => ((Nat.Prime.dvd_mul hp).mp h).elim h2p hk.2)
      have hm : (p : ℤ) ^ (s + 1) ∣ mm (p * n) k := by
        apply cop_dvd p hp k hk.2
        rw [(mm_ids (p * n) k hk0 hkn).2]
        exact dvd_mul_of_dvd_left (natdvd (pdvd p s n hn)) _
      rw [show 2 * s + 2 = (s + 1) + (s + 1) by ring, pow_add]
      exact mul_dvd_mul (dvd_mul_of_dvd_right hC _) hm
    · rw [Nat.choose_eq_zero_of_lt (by omega : p * n < 2 * k)]
      simp

/-! ## Part 4: assembly -/

lemma two_a (n : ℕ) : 2 * a n = coeff n (Phi ^ n) + Dd n := by
  rw [coeff_Phi_pow, a, Dd, mul_sum, ← sum_add_distrib]
  apply sum_congr rfl
  intro k _
  unfold mm
  ring

lemma key (p n s : ℕ) (hp : p.Prime) (hp3 : 3 < p) (hn0 : 0 < n) (hn : p ^ s ∣ n) :
    (p : ℤ) ^ (2 * s + 2) ∣ a (p * n) - a n := by
  have hp2 : p ≠ 2 := by omega
  have h2p : ¬ p ∣ 2 := fun h => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h)
  apply cop_dvd p hp 2 h2p
  have e : ((2 : ℕ) : ℤ) * (a (p * n) - a n)
      = (coeff (p * n) (Phi ^ (p * n)) - coeff n (Phi ^ n)) + (Dd (p * n) - Dd n) := by
    push_cast
    rw [mul_sub, two_a, two_a]
    ring
  rw [e]
  exact dvd_add (B_part p n s hp hp3 hn0 hn) (D_part p n s hp hp2 hn)

theorem final : ∀ p n : ℕ, p.Prime → 3 < p → 0 < n →
      ¬ p ∣ (((a (p * n) : ℚ) - (a n : ℚ)) / ((p : ℚ) * (n : ℚ)) ^ 2).den := by
  intro p n hp hp3 hn
  obtain ⟨s, u, hu, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn.ne' p hp.one_lt.ne'
  obtain ⟨q, hq⟩ := key p (p ^ s * u) s hp hp3 hn (dvd_mul_right _ _)
  have hu0 : (u : ℚ) ≠ 0 := by
    have : u ≠ 0 := by rintro rfl; exact hu (dvd_zero p)
    exact_mod_cast this
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hq' : ((a (p * (p ^ s * u)) : ℚ) - (a (p ^ s * u) : ℚ)) = (p : ℚ) ^ (2 * s + 2) * (q : ℚ) := by
    exact_mod_cast hq
  have hval : ((a (p * (p ^ s * u)) : ℚ) - (a (p ^ s * u) : ℚ)) / ((p : ℚ) * ((p ^ s * u : ℕ) : ℚ)) ^ 2
      = Rat.divInt q ((u : ℤ) ^ 2) := by
    rw [Rat.divInt_eq_div, hq']
    push_cast
    field_simp
    ring
  rw [hval]
  intro hdvd
  have h1 := Rat.den_dvd q ((u : ℤ) ^ 2)
  have h2 : (p : ℤ) ∣ (u : ℤ) ^ 2 := (Int.natCast_dvd_natCast.mpr hdvd).trans h1
  have h3 : (p : ℤ) ∣ (u : ℤ) := (Nat.prime_iff_prime_int.mp hp).dvd_of_dvd_pow h2
  exact hu (Int.natCast_dvd_natCast.mp h3)

end OMA.A278415Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a278415.main := OMA.A278415Proof.final
