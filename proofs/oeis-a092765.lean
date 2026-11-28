import OMAStatements.S_oeis_a092765

-- Problem: A092765 stronger Gauss congruences (conjecture of Peter Bala), statement by @sntntHb.
-- The congruence already holds term by term for a(n) = sum over j of choose(n,j) * choose(n,2n-3j).
-- Terms with p not dividing j vanish modulo p^(2k). For j = p*b, write
-- choose(pM,pb) * P(b) = choose(M,b) * Q(b), where P(b) is the product of the t < pb prime to p and
-- Q(b) the product of the pM - t; then expand Q to first order and pair t with pb - t.

open Polynomial Finset

namespace OMA.A092765

def f (n j : ℕ) : ℕ := if 3 * j ≤ 2 * n then n.choose j * n.choose (2 * n - 3 * j) else 0

lemma a_eq_sum (n : ℕ) : OMA.S_oeis_a092765.a n = ∑ j ∈ range (n + 1), f n j := by
  have hfac : (1 + X + X ^ 3 + X ^ 4 : ℕ[X]) = (X ^ 3 + 1) * (1 + X) := by ring
  unfold OMA.S_oeis_a092765.a
  rw [hfac, mul_pow, add_pow, sum_mul, finsetSum_coeff]
  refine sum_congr rfl fun j _ => ?_
  have hterm : (X ^ 3) ^ j * 1 ^ (n - j) * (n.choose j : ℕ[X]) * (1 + X) ^ n
      = X ^ (3 * j) * ((1 + X) ^ n * (n.choose j : ℕ[X])) := by
    rw [one_pow, mul_one, pow_mul]
    ring
  rw [hterm, coeff_X_pow_mul', coeff_mul_natCast, coeff_one_add_X_pow]
  unfold f
  split
  · rw [Nat.cast_id, Nat.cast_id, mul_comm]
  · rfl

lemma pow_dvd_choose {p m v M b : ℕ} (hp : p.Prime) (hM : p ^ m ∣ M) (hb : p ^ v ∣ b)
    (hb' : ¬ p ^ (v + 1) ∣ b) (hv : v ≤ m) : p ^ (m - v) ∣ M.choose b := by
  have hb0 : b ≠ 0 := by
    rintro rfl
    exact hb' (dvd_zero _)
  obtain ⟨b', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hb0
  rcases Nat.eq_zero_or_pos M with hM0 | hM0
  · subst hM0
    rw [Nat.choose_zero_succ]
    exact dvd_zero _
  obtain ⟨M', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hM0)
  have hkey : (M' + 1) * M'.choose b' = (M' + 1).choose (b' + 1) * (b' + 1) :=
    Nat.add_one_mul_choose_eq M' b'
  have h1 : p ^ m ∣ (M' + 1).choose (b' + 1) * (b' + 1) := by
    rw [← hkey]
    exact dvd_mul_of_dvd_left hM _
  obtain ⟨u, hu⟩ := hb
  have hpu : ¬ p ∣ u := by
    rintro ⟨w, hw⟩
    apply hb'
    refine ⟨w, ?_⟩
    rw [Nat.succ_eq_add_one] at hu ⊢
    rw [hu, hw, pow_succ, mul_assoc]
  have h2 : p ^ v * p ^ (m - v) ∣ p ^ v * ((M' + 1).choose (b' + 1) * u) := by
    rw [← pow_add, Nat.add_sub_cancel' hv]
    rw [Nat.succ_eq_add_one] at hu
    rw [hu] at h1
    rw [hu]
    have : (M' + 1).choose (p ^ v * u) * (p ^ v * u)
        = p ^ v * ((M' + 1).choose (p ^ v * u) * u) := by ring
    rwa [this] at h1
  have h3 := Nat.dvd_of_mul_dvd_mul_left (pow_pos hp.pos v) h2
  have hcop : Nat.Coprime (p ^ (m - v)) u :=
    Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpu)
  exact hcop.dvd_of_dvd_mul_right h3

def T (p b : ℕ) : Finset ℕ := (range (p * b)).filter fun t => ¬ p ∣ t

def P (p b : ℕ) : ℕ := ∏ t ∈ T p b, t

def S (p b : ℕ) : ℕ := ∑ t ∈ T p b, ∏ u ∈ (T p b).erase t, u

lemma mem_T {p b t : ℕ} : t ∈ T p b ↔ t < p * b ∧ ¬ p ∣ t := by
  simp [T]

lemma filter_dvd_range {p b : ℕ} (hp : 0 < p) :
    (range (p * b)).filter (fun t => p ∣ t) = (range b).image fun r => p * r := by
  ext t
  simp only [mem_filter, mem_range, mem_image]
  constructor
  · rintro ⟨hlt, r, rfl⟩
    exact ⟨r, Nat.lt_of_mul_lt_mul_left hlt, rfl⟩
  · rintro ⟨r, hr, rfl⟩
    exact ⟨Nat.mul_lt_mul_of_pos_left hr hp, dvd_mul_right _ _⟩

lemma prod_range_split {p b : ℕ} (hp : 0 < p) (g : ℕ → ℕ) :
    ∏ s ∈ range (p * b), g s = (∏ r ∈ range b, g (p * r)) * ∏ s ∈ T p b, g s := by
  rw [← prod_filter_mul_prod_filter_not (range (p * b)) (fun t => p ∣ t), filter_dvd_range hp,
    prod_image]
  · rfl
  · intro x _ y _ h
    exact Nat.eq_of_mul_eq_mul_left hp h

lemma descFactorial_split {p b M : ℕ} (hp : 0 < p) :
    (p * M).descFactorial (p * b) = p ^ b * M.descFactorial b * ∏ s ∈ T p b, (p * M - s) := by
  rw [Nat.descFactorial_eq_prod_range, prod_range_split hp, Nat.descFactorial_eq_prod_range]
  congr 1
  have : ∀ r ∈ range b, p * M - p * r = p * (M - r) := fun r _ => (Nat.mul_sub _ _ _).symm
  rw [prod_congr rfl this, prod_mul_distrib, prod_const, card_range]

lemma reflect_mem {p b t : ℕ} (ht : t ∈ T p b) : p * b - t ∈ T p b := by
  rw [mem_T] at ht ⊢
  obtain ⟨hlt, hnd⟩ := ht
  have ht0 : t ≠ 0 := by
    rintro rfl
    exact hnd (dvd_zero _)
  refine ⟨by omega, fun h => hnd ?_⟩
  have h2 := Nat.dvd_sub (dvd_mul_right p b) h
  rwa [Nat.sub_sub_self hlt.le] at h2

lemma prod_reflect {p b : ℕ} : ∏ s ∈ T p b, (p * b - s) = P p b := by
  unfold P
  have hinv : ∀ t ∈ T p b, p * b - (p * b - t) = t := fun t ht =>
    Nat.sub_sub_self (mem_T.mp ht).1.le
  exact prod_nbij' (fun t => p * b - t) (fun t => p * b - t) (fun t ht => reflect_mem ht)
    (fun t ht => reflect_mem ht) hinv hinv (fun t _ => rfl)

lemma choose_identity {p b M : ℕ} (hp : 0 < p) :
    (p * M).choose (p * b) * P p b = M.choose b * ∏ s ∈ T p b, (p * M - s) := by
  have h1 := descFactorial_split (b := b) (M := M) hp
  have h2 := descFactorial_split (b := b) (M := b) hp
  rw [prod_reflect, Nat.descFactorial_self, Nat.descFactorial_self] at h2
  rw [Nat.descFactorial_eq_factorial_mul_choose, h2,
    Nat.descFactorial_eq_factorial_mul_choose M b] at h1
  have hpos : 0 < p ^ b * b.factorial := Nat.mul_pos (pow_pos hp b) (Nat.factorial_pos b)
  apply Nat.eq_of_mul_eq_mul_left hpos
  calc p ^ b * b.factorial * ((p * M).choose (p * b) * P p b)
      = p ^ b * b.factorial * P p b * (p * M).choose (p * b) := by ring
    _ = p ^ b * (b.factorial * M.choose b) * ∏ s ∈ T p b, (p * M - s) := h1
    _ = p ^ b * b.factorial * (M.choose b * ∏ s ∈ T p b, (p * M - s)) := by ring

lemma card_T {p b : ℕ} (hp : 0 < p) : (T p b).card = (p - 1) * b := by
  have h := card_filter_add_card_filter_not (s := range (p * b)) (fun t => p ∣ t)
  rw [filter_dvd_range hp, card_image_of_injective, card_range, card_range] at h
  · unfold T
    rw [Nat.sub_mul, one_mul]
    omega
  · intro x y hxy
    exact Nat.eq_of_mul_eq_mul_left hp hxy

lemma prod_sub_sq_zero {R : Type*} [CommRing R] (x : R) (hx : x * x = 0) (g : ℕ → R)
    (s : Finset ℕ) :
    ∏ t ∈ s, (x - g t)
      = (-1) ^ s.card * (∏ t ∈ s, g t - x * ∑ t ∈ s, ∏ u ∈ s.erase t, g u) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have hS : ∑ t ∈ insert a s, ∏ u ∈ (insert a s).erase t, g u
        = ∏ u ∈ s, g u + g a * ∑ t ∈ s, ∏ u ∈ s.erase t, g u := by
      rw [sum_insert ha, erase_insert ha, mul_sum]
      congr 1
      refine sum_congr rfl fun t ht => ?_
      have hat : a ≠ t := fun h => ha (h ▸ ht)
      rw [erase_insert_of_ne hat, prod_insert]
      exact fun h => ha (mem_of_mem_erase h)
    rw [prod_insert ha, prod_insert ha, card_insert_of_notMem ha, ih, hS, pow_succ]
    linear_combination (-((-1 : R) ^ s.card * (∑ t ∈ s, ∏ u ∈ s.erase t, g u))) * hx

lemma coprime_of_mem {p b e t : ℕ} (hp : p.Prime) (ht : t ∈ T p b) : t.Coprime (p ^ e) :=
  Nat.Coprime.pow_right _ ((Nat.Prime.coprime_iff_not_dvd hp).mpr (mem_T.mp ht).2).symm

lemma pow_dvd_S {p b e : ℕ} (hp : p.Prime) (he : p ^ e ∣ p * b) (h2 : p ≠ 2 ∨ 2 ∣ b) :
    p ^ e ∣ S p b := by
  rw [← ZMod.natCast_eq_zero_iff]
  have hunit : ∀ t ∈ T p b, IsUnit ((t : ℕ) : ZMod (p ^ e)) := fun t ht =>
    (ZMod.isUnit_iff_coprime _ _).mpr (coprime_of_mem hp ht)
  have hpb : ((p * b : ℕ) : ZMod (p ^ e)) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr he
  have hrefl : ∀ t ∈ T p b, ((p * b - t : ℕ) : ZMod (p ^ e)) = -(t : ZMod (p ^ e)) := by
    intro t ht
    rw [Nat.cast_sub (mem_T.mp ht).1.le, hpb, zero_sub]
  have hsum : ∑ t ∈ T p b, Ring.inverse (t : ZMod (p ^ e)) = 0 := by
    refine sum_involution (fun t _ => p * b - t) ?_ ?_ (fun t ht => reflect_mem ht)
      (fun t ht => Nat.sub_sub_self (mem_T.mp ht).1.le)
    · intro t ht
      have h3 := Ring.mul_inverse_cancel _ (hunit t ht)
      have h4 := Ring.mul_inverse_cancel _ (hunit _ (reflect_mem ht))
      rw [hrefl t ht] at h4 ⊢
      apply (hunit t ht).mul_left_cancel
      rw [mul_zero]
      linear_combination h3 - h4
    · intro t ht _ heq
      have hlt := (mem_T.mp ht).1
      have htwo : 2 * t = p * b := by omega
      apply (mem_T.mp ht).2
      rcases h2 with h2 | ⟨c, hc⟩
      · have hdvd : p ∣ 2 * t := htwo ▸ dvd_mul_right p b
        rcases (Nat.Prime.dvd_mul hp).mp hdvd with h | h
        · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h) h2
        · exact h
      · refine ⟨c, Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 2) ?_⟩
        rw [htwo, hc]
        ring
  have hS : ((S p b : ℕ) : ZMod (p ^ e))
      = (∏ u ∈ T p b, (u : ZMod (p ^ e))) * ∑ t ∈ T p b, Ring.inverse (t : ZMod (p ^ e)) := by
    unfold S
    push_cast
    rw [mul_sum]
    refine sum_congr rfl fun t ht => ?_
    rw [← mul_prod_erase (T p b) (fun u => (u : ZMod (p ^ e))) ht]
    have h3 := Ring.mul_inverse_cancel _ (hunit t ht)
    linear_combination (-(∏ u ∈ (T p b).erase t, (u : ZMod (p ^ e)))) * h3
  rw [hS, hsum, mul_zero]

lemma two_cases {b c : ℕ} (hbc : 2 ∣ b + c) : 2 ∣ S 2 b * P 2 c + S 2 c * P 2 b := by
  have hodd : ∀ d, ∀ t ∈ T 2 d, ((t : ℕ) : ZMod 2) = 1 := by
    intro d t ht
    have h := (mem_T.mp ht).2
    rw [ZMod.natCast_eq_one_iff_odd, Nat.odd_iff]
    omega
  have hP : ∀ d, ((P 2 d : ℕ) : ZMod 2) = 1 := by
    intro d
    unfold P
    push_cast
    exact prod_eq_one (hodd d)
  have hS : ∀ d, ((S 2 d : ℕ) : ZMod 2) = (d : ZMod 2) := by
    intro d
    unfold S
    push_cast
    have : ∀ t ∈ T 2 d, ∏ u ∈ (T 2 d).erase t, (u : ZMod 2) = 1 := fun t _ =>
      prod_eq_one fun u hu => hodd d u (mem_of_mem_erase hu)
    rw [sum_congr rfl this, sum_const, card_T (by norm_num)]
    simp
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_add, Nat.cast_mul, Nat.cast_mul, hP, hP, hS, hS,
    mul_one, mul_one, ← Nat.cast_add, ZMod.natCast_eq_zero_iff]
  exact hbc

lemma key_dvd {p m M b c : ℕ} (hp : p.Prime) (hp3 : p ≠ 3) (hM : p ^ m ∣ M)
    (hbc : c + 3 * b = 2 * M) :
    p ^ (m + 1) ∣ M.choose b * M.choose c * (S p b * P p c + S p c * P p b) := by
  classical
  obtain ⟨v, hvm, hvb, hmax⟩ : ∃ v, v ≤ m ∧ p ^ v ∣ b ∧ (v < m → ¬ p ^ (v + 1) ∣ b) := by
    refine ⟨Nat.findGreatest (fun e => p ^ e ∣ b) m, Nat.findGreatest_le m, ?_, ?_⟩
    · exact Nat.findGreatest_spec (P := fun e => p ^ e ∣ b) (m := 0) (Nat.zero_le m) (by simp)
    · intro h
      exact Nat.findGreatest_is_greatest (P := fun e => p ^ e ∣ b) (Nat.lt_succ_self _) h
  have hvM : p ^ v ∣ M := (pow_dvd_pow p hvm).trans hM
  have hc : c = 2 * M - 3 * b := by omega
  have hvc : p ^ v ∣ c := by
    rw [hc]
    exact Nat.dvd_sub (dvd_mul_of_dvd_right hvM 2) (dvd_mul_of_dvd_right hvb 3)
  have hcop3 : ∀ e, Nat.Coprime (p ^ e) 3 := fun e =>
    Nat.Coprime.pow_left _ ((Nat.coprime_primes hp Nat.prime_three).mpr hp3)
  have hC : p ^ (m - v) ∣ M.choose b ∧ p ^ (m - v) ∣ M.choose c := by
    rcases hvm.eq_or_lt with h | h
    · rw [h, Nat.sub_self, pow_zero]
      exact ⟨one_dvd _, one_dvd _⟩
    · refine ⟨pow_dvd_choose hp hM hvb (hmax h) hvm, pow_dvd_choose hp hM hvc ?_ hvm⟩
      intro hcdvd
      apply hmax h
      have hM1 : p ^ (v + 1) ∣ 2 * M := dvd_mul_of_dvd_right ((pow_dvd_pow p h).trans hM) 2
      have h3b : p ^ (v + 1) ∣ 3 * b := by
        have : 3 * b = 2 * M - c := by omega
        rw [this]
        exact Nat.dvd_sub hM1 hcdvd
      exact (hcop3 _).dvd_of_dvd_mul_left h3b
  have hE : p ^ (2 * v + 1 - m) ∣ S p b * P p c + S p c * P p b := by
    by_cases hcase : p ≠ 2 ∨ 1 ≤ v
    · have hparity : ∀ d, p ^ v ∣ d → p ≠ 2 ∨ 2 ∣ d := by
        intro d hd
        rcases eq_or_ne p 2 with h2 | h2
        · right
          have h1v : 1 ≤ v := hcase.resolve_left (not_not_intro h2)
          have := (pow_dvd_pow p h1v).trans hd
          rwa [pow_one, h2] at this
        · exact Or.inl h2
      have hSd : ∀ d, p ^ v ∣ d → p ^ (2 * v + 1 - m) ∣ S p d := by
        intro d hd
        have hpd : p ^ (v + 1) ∣ p * d := by
          rw [pow_succ']
          exact mul_dvd_mul_left p hd
        exact (pow_dvd_pow p (by omega)).trans (pow_dvd_S hp hpd (hparity d hd))
      exact dvd_add (dvd_mul_of_dvd_left (hSd b hvb) _) (dvd_mul_of_dvd_left (hSd c hvc) _)
    · have h2 : p = 2 := by
        by_contra h
        exact hcase (Or.inl h)
      have hv0 : v = 0 := by
        by_contra h
        exact hcase (Or.inr (by omega))
      rcases Nat.eq_zero_or_pos m with hm | hm
      · have : 2 * v + 1 - m = 1 := by omega
        rw [this, pow_one, h2]
        exact two_cases ⟨M - b, by omega⟩
      · have : 2 * v + 1 - m = 0 := by omega
        rw [this, pow_zero]
        exact one_dvd _
  have htot : p ^ (m - v) * p ^ (m - v) * p ^ (2 * v + 1 - m)
      ∣ M.choose b * M.choose c * (S p b * P p c + S p c * P p b) :=
    mul_dvd_mul (mul_dvd_mul hC.1 hC.2) hE
  rw [← pow_add, ← pow_add] at htot
  exact (pow_dvd_pow p (by omega)).trans htot

lemma ring_step {R : Type*} [CommRing R] {x A B C D Pb Pc Sb Sc sb sc : R} (hx : x * x = 0)
    (h1 : A * Pb = C * (sb * (Pb - x * Sb))) (h2 : B * Pc = D * (sc * (Pc - x * Sc)))
    (hsign : sb * sc = 1) (hE : C * D * x * (Sb * Pc + Sc * Pb) = 0) :
    A * B * (Pb * Pc) = C * D * (Pb * Pc) := by
  calc A * B * (Pb * Pc) = (A * Pb) * (B * Pc) := by ring
    _ = (C * (sb * (Pb - x * Sb))) * (D * (sc * (Pc - x * Sc))) := by rw [h1, h2]
    _ = (sb * sc) * (C * D * ((Pb - x * Sb) * (Pc - x * Sc))) := by ring
    _ = C * D * ((Pb - x * Sb) * (Pc - x * Sc)) := by rw [hsign, one_mul]
    _ = C * D * (Pb * Pc) := by linear_combination (-1 : R) * hE + C * D * Sb * Sc * hx

lemma choose_pair {p m M b c : ℕ} (hp : p.Prime) (hp3 : p ≠ 3) (hM : p ^ m ∣ M)
    (hbc : c + 3 * b = 2 * M) (hbM : b ≤ M) (hcM : c ≤ M) :
    (((p * M).choose (p * b) * (p * M).choose (p * c) : ℕ) : ZMod (p ^ (2 * (m + 1))))
      = ((M.choose b * M.choose c : ℕ) : ZMod (p ^ (2 * (m + 1)))) := by
  have hpM : p ^ (m + 1) ∣ p * M := by
    rw [pow_succ']
    exact mul_dvd_mul_left p hM
  have hx : ((p * M : ℕ) : ZMod (p ^ (2 * (m + 1)))) * ((p * M : ℕ) : ZMod (p ^ (2 * (m + 1))))
      = 0 := by
    rw [← Nat.cast_mul, ZMod.natCast_eq_zero_iff, two_mul, pow_add]
    exact mul_dvd_mul hpM hpM
  have hQ : ∀ d, d ≤ M →
      (((p * M).choose (p * d) : ℕ) : ZMod (p ^ (2 * (m + 1)))) * (P p d : ZMod _)
        = (M.choose d : ZMod _) * ((-1) ^ (T p d).card
          * ((P p d : ZMod _) - ((p * M : ℕ) : ZMod _) * (S p d : ZMod _))) := by
    intro d hd
    have h := congrArg (fun z : ℕ => (z : ZMod (p ^ (2 * (m + 1))))) (choose_identity
      (p := p) (b := d) (M := M) hp.pos)
    simp only [Nat.cast_mul] at h
    rw [h]
    congr 1
    have hprod : ((∏ s ∈ T p d, (p * M - s) : ℕ) : ZMod (p ^ (2 * (m + 1))))
        = ∏ s ∈ T p d, (((p * M : ℕ) : ZMod (p ^ (2 * (m + 1)))) - (s : ZMod _)) := by
      rw [Nat.cast_prod]
      refine prod_congr rfl fun s hs => ?_
      rw [Nat.cast_sub]
      exact (mem_T.mp hs).1.le.trans (Nat.mul_le_mul_left p hd)
    rw [hprod, prod_sub_sq_zero _ hx]
    unfold P S
    simp only [Nat.cast_prod, Nat.cast_sum]
  have hsign : (-1 : ZMod (p ^ (2 * (m + 1)))) ^ (T p b).card * (-1) ^ (T p c).card = 1 := by
    rw [← pow_add, card_T hp.pos, card_T hp.pos, ← mul_add]
    have hev : Even (b + c) := ⟨M - b, by omega⟩
    exact (hev.mul_left _).neg_one_pow
  have hE : ((M.choose b * M.choose c : ℕ) : ZMod (p ^ (2 * (m + 1))))
      * ((p * M : ℕ) : ZMod _)
      * ((S p b : ZMod _) * (P p c : ZMod _) + (S p c : ZMod _) * (P p b : ZMod _)) = 0 := by
    have hdvd : p ^ (2 * (m + 1))
        ∣ M.choose b * M.choose c * (p * M) * (S p b * P p c + S p c * P p b) := by
      have h := mul_dvd_mul hpM (key_dvd hp hp3 hM hbc)
      rw [← pow_add, ← two_mul] at h
      have e : M.choose b * M.choose c * (p * M) * (S p b * P p c + S p c * P p b)
          = p * M * (M.choose b * M.choose c * (S p b * P p c + S p c * P p b)) := by ring
      rw [e]
      exact h
    have h := (ZMod.natCast_eq_zero_iff _ _).mpr hdvd
    simpa only [Nat.cast_mul, Nat.cast_add] using h
  have hunit : IsUnit ((P p b : ZMod (p ^ (2 * (m + 1)))) * (P p c : ZMod _)) := by
    rw [← Nat.cast_mul, ZMod.isUnit_iff_coprime]
    refine Nat.Coprime.mul_left ?_ ?_
    · unfold P
      exact Nat.Coprime.prod_left fun t ht => coprime_of_mem hp ht
    · unfold P
      exact Nat.Coprime.prod_left fun t ht => coprime_of_mem hp ht
  apply hunit.mul_right_cancel
  have h1 := hQ b hbM
  have h2 := hQ c hcM
  rw [Nat.cast_mul] at hE
  rw [Nat.cast_mul, Nat.cast_mul]
  exact ring_step hx h1 h2 hsign hE

lemma f_mul {p m M i : ℕ} (hp : p.Prime) (hp3 : p ≠ 3) (hM : p ^ m ∣ M) :
    (f (p * M) (p * i) : ZMod (p ^ (2 * (m + 1)))) = (f M i : ZMod (p ^ (2 * (m + 1)))) := by
  have hcond : 3 * (p * i) ≤ 2 * (p * M) ↔ 3 * i ≤ 2 * M := by
    rw [show 3 * (p * i) = p * (3 * i) by ring, show 2 * (p * M) = p * (2 * M) by ring]
    exact Nat.mul_le_mul_left_iff hp.pos
  have hsub : 2 * (p * M) - 3 * (p * i) = p * (2 * M - 3 * i) := by
    rw [Nat.mul_sub, show 3 * (p * i) = p * (3 * i) by ring,
      show 2 * (p * M) = p * (2 * M) by ring]
  unfold f
  by_cases h : 3 * i ≤ 2 * M
  · rw [if_pos (hcond.mpr h), if_pos h, hsub]
    by_cases hiM : i ≤ M
    · by_cases hcM : 2 * M - 3 * i ≤ M
      · exact choose_pair hp hp3 hM (by omega) hiM hcM
      · have hcM' : M < 2 * M - 3 * i := by omega
        rw [Nat.choose_eq_zero_of_lt hcM',
          Nat.choose_eq_zero_of_lt (Nat.mul_lt_mul_of_pos_left hcM' hp.pos)]
        simp
    · have hiM' : M < i := by omega
      rw [Nat.choose_eq_zero_of_lt hiM',
        Nat.choose_eq_zero_of_lt (Nat.mul_lt_mul_of_pos_left hiM' hp.pos)]
      simp
  · rw [if_neg (fun h' => h (hcond.mp h')), if_neg h]

lemma f_of_not_dvd {p k N j : ℕ} (hp : p.Prime) (hp3 : p ≠ 3) (hk : 0 < k) (hN : p ^ k ∣ N)
    (hj : ¬ p ∣ j) : p ^ (2 * k) ∣ f N j := by
  unfold f
  split
  · rename_i h
    have hpN : p ∣ N := (dvd_pow_self p hk.ne').trans hN
    have hc : ¬ p ∣ 2 * N - 3 * j := by
      intro hc
      apply hj
      have h3 : p ∣ 3 * j := by
        have h4 := Nat.dvd_sub (dvd_mul_of_dvd_right hpN 2) hc
        rwa [Nat.sub_sub_self h] at h4
      rcases (Nat.Prime.dvd_mul hp).mp h3 with h5 | h5
      · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h5) hp3
      · exact h5
    have h1 := pow_dvd_choose (v := 0) (b := j) hp hN (by simp) (by simpa using hj)
      (Nat.zero_le k)
    have h2 := pow_dvd_choose (v := 0) (b := 2 * N - 3 * j) hp hN (by simp) (by simpa using hc)
      (Nat.zero_le k)
    rw [Nat.sub_zero] at h1 h2
    rw [two_mul, pow_add]
    exact mul_dvd_mul h1 h2
  · exact dvd_zero _

end OMA.A092765

open OMA.A092765 in
theorem OMA.solution : type_of% @OMA.S_oeis_a092765.main := by
  intro p n k hp hp3 _ hk
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
  rw [Nat.succ_eq_add_one, Nat.add_sub_cancel]
  have hN : n * p ^ (m + 1) = p * (n * p ^ m) := by ring
  rw [hN]
  have hM : p ^ m ∣ n * p ^ m := dvd_mul_left _ _
  have hNd : p ^ (m + 1) ∣ p * (n * p ^ m) := by
    rw [← hN]
    exact dvd_mul_left _ _
  generalize n * p ^ m = M at hM hNd ⊢
  apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
  rw [a_eq_sum, a_eq_sum, Nat.cast_sum, Nat.cast_sum]
  have hzero : ∀ j ∈ range (p * M + 1),
      (f (p * M) j : ZMod (p ^ (2 * (m + 1)))) ≠ 0 → p ∣ j := by
    intro j _ hne
    by_contra hj
    exact hne ((ZMod.natCast_eq_zero_iff _ _).mpr
      (f_of_not_dvd hp hp3 (Nat.succ_pos m) hNd hj))
  have himg : (range (p * M + 1)).filter (fun j => p ∣ j)
      = (range (M + 1)).image fun i => p * i := by
    ext t
    simp only [mem_filter, mem_range, mem_image, Nat.lt_succ_iff]
    constructor
    · rintro ⟨hle, r, rfl⟩
      exact ⟨r, Nat.le_of_mul_le_mul_left hle hp.pos, rfl⟩
    · rintro ⟨r, hr, rfl⟩
      exact ⟨Nat.mul_le_mul_left p hr, dvd_mul_right _ _⟩
  rw [← sum_filter_of_ne hzero, himg, sum_image]
  · exact sum_congr rfl fun i _ => f_mul hp hp3 hM
  · intro x _ y _ h
    exact Nat.eq_of_mul_eq_mul_left hp.pos h
