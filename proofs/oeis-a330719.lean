import OMAStatements.S_oeis_a330719
import Mathlib

-- Problem: OEIS A330719, conjecture of Eldar and Ordowski: for each odd prime p, p divides
-- A330718(p+1) - A330719(p+1), where A330718(n) is the numerator of Sum_{k=1..n} (2^k - 2)/k
-- and A330719(n) is the denominator of S(n) = Sum_{k=1..n} (2^(k-1) - 1)/k.
-- Statement: statements/oeis-a330719.lean (declaration OMA.S_oeis_a330719.main)
-- Credit: @schulzee (agent: Claude Code, model claude-fable-5-2)
--
-- Proof. Let q = (2^(p-1) - 1)/p, an integer by Fermat. We have
-- S(p+1) = Sum_{k=1..p-1} (2^(k-1) - 1)/k + q + (2^p - 1)/(p + 1).
-- Step 1 (modulo p). C(p,k)/p = C(p-1,k-1)/k == (-1)^(k-1)/k (mod p) for 0 < k < p. The
-- binomial theorem for (1 - 2)^p gives Sum_{k=1..p-1} C(p,k) (-2)^k = 2^p - 2 = 2 p q, thus
-- Sum_{k=1..p-1} 2^(k-1)/k == -q (mod p). The map k -> p - k gives Sum_{k=1..p-1} 1/k == 0.
-- Step 2. Multiply S(p+1) by B = (p-1)! (p+1), which p does not divide. The product is an
-- integer Z, and Wilson's theorem with step 1 gives Z == q - q - 1 == B (mod p). Thus p divides
-- num(S(p+1)) - den(S(p+1)).
-- Step 3 (parity). Sum_{k=1..n} 2^(k-1)/k has an odd denominator, and the harmonic number H(n)
-- has a negative 2-adic valuation for n >= 2. Thus the denominator of S(n) is even, and the
-- numerator of 2 S(n) (this is A330718(n)) is equal to the numerator of S(n).

namespace OMA.A330719

open Finset OMA.S_oeis_a330719

lemma sum_Icc_eq_range {M : Type*} [AddCommMonoid M] (f : ℕ → M) (n : ℕ) :
    ∑ k ∈ Icc 1 n, f k = ∑ j ∈ range n, f (j + 1) := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_Icc_succ_top (by omega), ih, sum_range_succ]

/-- The sum Sum_{k=1..n} (2^(k-1) - 1)/k, with the index k = j + 1. -/
def S (n : ℕ) : ℚ := ∑ j ∈ range n, ((2 : ℚ) ^ j - 1) / ((j + 1 : ℕ) : ℚ)

lemma two_ne (p : ℕ) [Fact p.Prime] (hodd : Odd p) : (2 : ZMod p) ≠ 0 := by
  intro h
  have h2 : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff] at h2
  have hp : p.Prime := Fact.out
  have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h2
  subst this
  exact absurd hodd (by decide)

lemma cast_ne (p : ℕ) [Fact p.Prime] (j : ℕ) (hj : j < p - 1) : ((j + 1 : ℕ) : ZMod p) ≠ 0 := by
  intro h
  rw [ZMod.natCast_eq_zero_iff] at h
  have := Nat.le_of_dvd (by omega) h
  omega

lemma choose_pred (p : ℕ) [Fact p.Prime] (j : ℕ) (hj : j < p) :
    (((p - 1).choose j : ℕ) : ZMod p) = (-1) ^ j := by
  have hp : p.Prime := Fact.out
  induction j with
  | zero => simp
  | succ j ih =>
    have h1 : (p - 1).choose j + (p - 1).choose (j + 1) = p.choose (j + 1) := by
      have e : p = (p - 1) + 1 := by have := hp.pos; omega
      conv_rhs => rw [e]
      rw [Nat.choose_succ_succ]
    have h2 : ((p.choose (j + 1) : ℕ) : ZMod p) = 0 := by
      rw [ZMod.natCast_eq_zero_iff]
      exact hp.dvd_choose_self (by omega) hj
    have h3 := congrArg (fun x : ℕ => (x : ZMod p)) h1
    simp only [Nat.cast_add, h2, ih (by omega)] at h3
    rw [pow_succ]; linear_combination h3

lemma binom_sum (n : ℕ) (hodd : Odd (n + 1)) :
    ∑ j ∈ range n, (-2 : ℤ) ^ (j + 1) * ((n + 1).choose (j + 1) : ℤ) = 2 ^ (n + 1) - 2 := by
  have h := add_pow (-2 : ℤ) 1 (n + 1)
  rw [sum_range_succ, sum_range_succ'] at h
  simp only [one_pow, mul_one, Nat.choose_self, Nat.cast_one, pow_zero, Nat.choose_zero_right] at h
  have h1 : (-2 + 1 : ℤ) ^ (n + 1) = -1 := by
    have : (-2 + 1 : ℤ) = -1 := by norm_num
    rw [this]; exact hodd.neg_one_pow
  have h2 : (-2 : ℤ) ^ (n + 1) = -2 ^ (n + 1) := hodd.neg_pow 2
  rw [h1, h2] at h
  linarith

lemma key (p : ℕ) [Fact p.Prime] (hodd : Odd p) (q : ℕ) (hq : 2 ^ (p - 1) = p * q + 1) :
    ∑ j ∈ range (p - 1), (2 : ZMod p) ^ j * (((j + 1 : ℕ) : ZMod p))⁻¹ = -(q : ZMod p) := by
  have hp : p.Prime := Fact.out
  have hp1 : p - 1 + 1 = p := by have := hp.pos; omega
  -- the integer identity
  have hI : ∑ j ∈ range (p - 1), (-2 : ℤ) ^ (j + 1) * ((p.choose (j + 1) / p : ℕ) : ℤ)
      = 2 * q := by
    have hb := binom_sum (p - 1) (by rw [hp1]; exact hodd)
    rw [hp1] at hb
    have hpz : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
    apply mul_left_cancel₀ hpz
    rw [mul_sum]
    have e2 : (2 : ℤ) ^ p = 2 * (p * q + 1) := by
      have : (2 : ℕ) ^ p = 2 * (p * q + 1) := by
        rw [← hq, ← pow_succ', hp1]
      exact_mod_cast this
    have : ∑ j ∈ range (p - 1), (p : ℤ) * ((-2 : ℤ) ^ (j + 1) * ((p.choose (j + 1) / p : ℕ) : ℤ))
        = ∑ j ∈ range (p - 1), (-2 : ℤ) ^ (j + 1) * (p.choose (j + 1) : ℤ) := by
      apply sum_congr rfl
      intro j hj
      have hj' : j < p - 1 := mem_range.1 hj
      have hd : p ∣ p.choose (j + 1) := hp.dvd_choose_self (by omega) (by omega)
      have : (p.choose (j + 1) : ℤ) = (p : ℤ) * ((p.choose (j + 1) / p : ℕ) : ℤ) := by
        exact_mod_cast (Nat.mul_div_cancel' hd).symm
      rw [this]; ring
    rw [this, hb, e2]; ring
  have hZ := congrArg (fun x : ℤ => (x : ZMod p)) hI
  simp only [Int.cast_sum, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_ofNat,
    Int.cast_natCast] at hZ
  have hc : ∀ j ∈ range (p - 1), (-2 : ZMod p) ^ (j + 1) * ((p.choose (j + 1) / p : ℕ) : ZMod p)
      = -2 * ((2 : ZMod p) ^ j * (((j + 1 : ℕ) : ZMod p))⁻¹) := by
    intro j hj
    have hj' : j < p - 1 := mem_range.1 hj
    have hd : p ∣ p.choose (j + 1) := hp.dvd_choose_self (by omega) (by omega)
    have hne := cast_ne p j hj'
    have h1 : (j + 1) * (p.choose (j + 1) / p) = (p - 1).choose j := by
      have h := Nat.add_one_mul_choose_eq (p - 1) j
      rw [hp1] at h
      apply Nat.eq_of_mul_eq_mul_left hp.pos
      rw [h, ← Nat.mul_div_cancel' hd]
      have := Nat.mul_div_cancel' hd
      rw [Nat.mul_div_cancel_left _ hp.pos]
      ring
    have h2 : ((j + 1 : ℕ) : ZMod p) * ((p.choose (j + 1) / p : ℕ) : ZMod p) = (-1) ^ j := by
      rw [← choose_pred p j (by omega), ← h1]; push_cast; ring
    have h3 : ((p.choose (j + 1) / p : ℕ) : ZMod p) = (-1) ^ j * (((j + 1 : ℕ) : ZMod p))⁻¹ := by
      rw [← h2]; field_simp
    have hsq : ((-1 : ZMod p) ^ j) ^ 2 = 1 := by
      rw [← pow_mul, mul_comm, pow_mul]; simp
    have hm : (-2 : ZMod p) ^ j = (-1) ^ j * 2 ^ j := by
      rw [← mul_pow]; norm_num
    rw [h3, pow_succ, hm]
    linear_combination (-2 * (2 : ZMod p) ^ j * (((j + 1 : ℕ) : ZMod p))⁻¹) * hsq
  rw [sum_congr rfl hc, ← mul_sum] at hZ
  have h2 := two_ne p hodd
  apply mul_left_cancel₀ h2
  linear_combination -hZ

lemma sum_inv (p : ℕ) [Fact p.Prime] (hodd : Odd p) :
    ∑ j ∈ range (p - 1), (((j + 1 : ℕ) : ZMod p))⁻¹ = 0 := by
  have h := sum_range_reflect (fun j => (((j + 1 : ℕ) : ZMod p))⁻¹) (p - 1)
  have h2 : ∀ j ∈ range (p - 1), (((p - 1 - 1 - j + 1 : ℕ) : ZMod p))⁻¹
      = -(((j + 1 : ℕ) : ZMod p))⁻¹ := by
    intro j hj
    have hj' : j < p - 1 := mem_range.1 hj
    have e : p - 1 - 1 - j + 1 = p - (j + 1) := by omega
    rw [e, Nat.cast_sub (by omega), ZMod.natCast_self, zero_sub, inv_neg]
  rw [sum_congr rfl h2, sum_neg_distrib] at h
  apply mul_left_cancel₀ (two_ne p hodd)
  linear_combination -h

lemma rat_dvd (p : ℕ) [Fact p.Prime] (r : ℚ) (Z B : ℤ) (h : r * B = Z) (hB : ¬ (p : ℤ) ∣ B)
    (hZB : (Z : ZMod p) = (B : ZMod p)) : (p : ℤ) ∣ r.num - r.den := by
  have hp : p.Prime := Fact.out
  have h1 : r.num * B = Z * r.den := by
    have : (r.num : ℚ) * B = Z * r.den := by
      rw [← h, ← Rat.mul_den_eq_num r]; ring
    exact_mod_cast this
  have h3 : (p : ℤ) ∣ Z - B := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).1
    push_cast; rw [hZB]; ring
  have h2 : (p : ℤ) ∣ (r.num - r.den) * B := by
    have : (r.num - r.den) * B = r.den * (Z - B) := by linear_combination h1
    rw [this]; exact Dvd.dvd.mul_left h3 _
  exact ((Nat.prime_iff_prime_int.1 hp).dvd_or_dvd h2).resolve_right hB

lemma S_split (m : ℕ) : S (m + 2) = (∑ j ∈ range m, ((2 : ℚ) ^ j - 1) / ((j + 1 : ℕ) : ℚ))
    + ((2 : ℚ) ^ m - 1) / ((m + 1 : ℕ) : ℚ) + ((2 : ℚ) ^ (m + 1) - 1) / ((m + 2 : ℕ) : ℚ) := by
  unfold S; rw [sum_range_succ, sum_range_succ]

lemma main_dvd (p : ℕ) [Fact p.Prime] (hodd : Odd p) :
    (p : ℤ) ∣ (S (p + 1)).num - (S (p + 1)).den := by
  have hp : p.Prime := Fact.out
  obtain ⟨m, hm⟩ : ∃ m, p = m + 1 := ⟨p - 1, by have := hp.pos; omega⟩
  have hm1 : p - 1 = m := by omega
  -- Fermat quotient
  obtain ⟨q, hq⟩ : ∃ q : ℕ, 2 ^ (p - 1) = p * q + 1 := by
    have h2 := two_ne p hodd
    have hf : (2 : ZMod p) ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one h2
    have hd : p ∣ 2 ^ (p - 1) - 1 := by
      rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub Nat.one_le_two_pow]
      push_cast; rw [hf]; ring
    obtain ⟨q, hq⟩ := hd
    exact ⟨q, by have : 1 ≤ 2 ^ (p - 1) := Nat.one_le_two_pow; omega⟩
  have hkey := key p hodd q hq
  have hinv := sum_inv p hodd
  rw [hm1] at hkey hinv hq
  have hw : ((Nat.factorial m : ℕ) : ZMod p) = -1 := by
    have := ZMod.wilsons_lemma (p := p); rwa [hm1] at this
  set F : ℕ := Nat.factorial m with hF
  set e : ℕ → ℕ := fun j => F / (j + 1) with he
  have hdiv : ∀ j ∈ range m, (j + 1) ∣ F := by
    intro j hj
    exact Nat.dvd_factorial (by omega) (by have := mem_range.1 hj; omega)
  apply rat_dvd p (S (p + 1))
    ((∑ j ∈ range m, ((2 : ℤ) ^ j - 1) * (e j : ℤ)) * (p + 1) + q * F * (p + 1)
      + (2 ^ p - 1) * F) (F * (p + 1))
  · -- the equation over the rationals
    have hS : S (p + 1) = S (m + 2) := by rw [hm]
    rw [hS, S_split]
    have hqq : ((2 : ℚ) ^ m - 1) / ((m + 1 : ℕ) : ℚ) = q := by
      have : ((2 : ℚ) ^ m) = p * q + 1 := by exact_mod_cast hq
      rw [this, ← hm]
      have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
      field_simp
      ring
    have ht : (∑ j ∈ range m, ((2 : ℚ) ^ j - 1) / ((j + 1 : ℕ) : ℚ)) * F
        = ∑ j ∈ range m, ((2 : ℚ) ^ j - 1) * (e j : ℚ) := by
      rw [sum_mul]
      apply sum_congr rfl
      intro j hj
      have hne : ((j + 1 : ℕ) : ℚ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero j
      rw [he]
      simp only
      rw [Nat.cast_div (hdiv j hj) hne]
      field_simp
    have hm2 : ((m + 2 : ℕ) : ℚ) = (p : ℚ) + 1 := by rw [hm]; push_cast; ring
    have hpp : (2 : ℚ) ^ (m + 1) = 2 ^ p := by rw [hm]
    rw [hqq, hm2, hpp]
    push_cast
    push_cast at ht
    rw [← ht]
    have hp1 : (p : ℚ) + 1 ≠ 0 := by positivity
    field_simp
  · -- p does not divide (p - 1)! (p + 1)
    intro hd
    have hd' : p ∣ F * (p + 1) := by exact_mod_cast hd
    rcases hp.dvd_mul.1 hd' with h | h
    · have := (hp.dvd_factorial).1 h; omega
    · have := (Nat.dvd_add_right (dvd_refl p)).1 h
      have := Nat.le_of_dvd (by norm_num) this
      have := hp.two_le; omega
  · -- the congruence
    have hej : ∀ j ∈ range m, (e j : ZMod p) = -(((j + 1 : ℕ) : ZMod p))⁻¹ := by
      intro j hj
      have hne := cast_ne p j (by have := mem_range.1 hj; omega)
      have h1 : e j * (j + 1) = F := Nat.div_mul_cancel (hdiv j hj)
      have h2 : (e j : ZMod p) * ((j + 1 : ℕ) : ZMod p) = -1 := by
        rw [← hw, ← h1]; push_cast; ring
      rw [eq_neg_iff_add_eq_zero]
      field_simp
      linear_combination h2
    have hsum : ∑ j ∈ range m, ((2 : ZMod p) ^ j - 1) * (e j : ZMod p) = q := by
      have : ∑ j ∈ range m, ((2 : ZMod p) ^ j - 1) * (e j : ZMod p)
          = ∑ j ∈ range m, (((((j + 1 : ℕ) : ZMod p))⁻¹)
            - (2 : ZMod p) ^ j * (((j + 1 : ℕ) : ZMod p))⁻¹) := by
        apply sum_congr rfl
        intro j hj
        rw [hej j hj]; ring
      rw [this, sum_sub_distrib, hkey, hinv]; ring
    have h2p : (2 : ZMod p) ^ p = 2 := ZMod.pow_card 2
    push_cast
    rw [hsum, hw, h2p, ZMod.natCast_self]
    ring

lemma odd_den_term (j : ℕ) : Odd (((2 : ℚ) ^ j / ((j + 1 : ℕ) : ℚ)).den) := by
  obtain ⟨v, u, hu, hvu⟩ := Nat.exists_eq_two_pow_mul_odd (n := j + 1) (by omega)
  have hv : v ≤ j := by
    by_contra hlt
    rw [not_le] at hlt
    have h1 : 2 ^ (j + 1) ≤ 2 ^ v := Nat.pow_le_pow_right (by norm_num) hlt
    have h2 : j + 1 < 2 ^ (j + 1) := Nat.lt_two_pow_self
    have h3 : 2 ^ v ≤ j + 1 := by rw [hvu]; exact Nat.le_mul_of_pos_right _ hu.pos
    omega
  have hu0 : (u : ℚ) ≠ 0 := by exact_mod_cast hu.pos.ne'
  have e : (2 : ℚ) ^ j / ((j + 1 : ℕ) : ℚ) = (((2 ^ (j - v) : ℕ) : ℤ) : ℚ) / ((u : ℤ) : ℚ) := by
    rw [hvu]
    have : (2 : ℚ) ^ j = 2 ^ (j - v) * 2 ^ v := by rw [← pow_add]; congr 1; omega
    rw [this]; push_cast; field_simp
  rw [e]
  have hdvd := Rat.den_dvd ((2 ^ (j - v) : ℕ) : ℤ) (u : ℤ)
  rw [Rat.divInt_eq_div] at hdvd
  exact hu.of_dvd_nat (Int.natCast_dvd_natCast.1 hdvd)

lemma odd_den_sum (f : ℕ → ℚ) (n : ℕ) (h : ∀ j, Odd (f j).den) :
    Odd (∑ j ∈ range n, f j).den := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_range_succ]; exact (ih.mul (h n)).of_dvd_nat (Rat.add_den_dvd _ _)

lemma even_den (n : ℕ) (hn : 2 ≤ n) : Even (S n).den := by
  by_contra hne
  have hodd : Odd (S n).den := Nat.not_even_iff_odd.1 hne
  have hA := odd_den_sum (fun j => (2 : ℚ) ^ j / ((j + 1 : ℕ) : ℚ)) n odd_den_term
  have hH : harmonic n = (∑ j ∈ range n, (2 : ℚ) ^ j / ((j + 1 : ℕ) : ℚ)) - S n := by
    unfold S harmonic
    rw [← sum_sub_distrib]
    apply sum_congr rfl
    intro j _
    rw [sub_div]; simp
  have hHodd : Odd (harmonic n).den := by
    rw [hH]; exact (hA.mul hodd).of_dvd_nat (Rat.sub_den_dvd _ _)
  have hv := padicValRat_two_harmonic n
  have hlog : 0 < Nat.log 2 n := Nat.log_pos (by norm_num) hn
  have h0 : 0 ≤ padicValRat 2 (harmonic n) := by
    unfold padicValRat
    have : padicValNat 2 (harmonic n).den = 0 :=
      padicValNat.eq_zero_of_not_dvd hHodd.not_two_dvd_nat
    rw [this]; simp
  rw [hv] at h0
  have : (0 : ℤ) < (Nat.log 2 n : ℤ) := by exact_mod_cast hlog
  omega

theorem main' (p : ℕ) (hp : p.Prime) (hodd : Odd p) :
    (p : ℤ) ∣ b (p + 1) - (a (p + 1) : ℤ) := by
  have : Fact p.Prime := Fact.mk hp
  have ha : (∑ k ∈ Icc 1 (p + 1), ((2 : ℚ) ^ (k - 1) - 1) / k) = S (p + 1) := by
    rw [sum_Icc_eq_range]; unfold S
    apply sum_congr rfl
    intro j _
    simp
  have hb : (∑ k ∈ Icc 1 (p + 1), ((2 : ℚ) ^ k - 2) / k) = 2 * S (p + 1) := by
    rw [sum_Icc_eq_range]; unfold S
    rw [mul_sum]
    apply sum_congr rfl
    intro j _
    rw [pow_succ]; ring
  unfold a b
  rw [ha, hb]
  obtain ⟨d', hd'⟩ := even_den (p + 1) (by have := hp.two_le; omega)
  have hd0 : d' ≠ 0 := by
    intro h0; rw [h0] at hd'; exact (S (p + 1)).den_nz hd'
  have hnum : (2 * S (p + 1)).num = (S (p + 1)).num := by
    have hS : 2 * S (p + 1) = ((S (p + 1)).num : ℚ) / ((d' : ℤ) : ℚ) := by
      have hq0 : (d' : ℚ) ≠ 0 := by exact_mod_cast hd0
      conv_lhs => rw [← Rat.num_div_den (S (p + 1))]
      rw [hd']; push_cast; field_simp; ring
    rw [hS]
    apply Rat.num_div_eq_of_coprime (by exact_mod_cast Nat.pos_of_ne_zero hd0)
    have hred := (S (p + 1)).reduced
    rw [hd'] at hred
    simpa using Nat.Coprime.coprime_dvd_right (⟨2, by ring⟩ : d' ∣ d' + d') hred
  rw [hnum]
  exact main_dvd p hodd

end OMA.A330719

theorem OMA.solution : type_of% @OMA.S_oeis_a330719.main :=
  fun p hp hodd => OMA.A330719.main' p hp hodd
