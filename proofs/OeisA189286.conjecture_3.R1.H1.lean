import OMAReductions.R_OeisA189286_conjecture_3_R1
import Mathlib

/-!
# Step H1 of reduction OeisA189286.conjecture_3.R1: 8 divides a(n)

The divisibility half of Zhi-Wei Sun's conjecture (ii) for OEIS A189286:
for every positive n, a(n) is divisible by 8.

The proof combines two already-formalized arguments:
- Yuto Nakahara's integrality of the normalized convolution (that
  `(2n-1) * choose(3n,n)` divides the convolution numerator), adapted from
  https://github.com/YutoNakahara/oeis-a189286-lean (Apache-2.0);
- the 2-adic digit-sum valuation lemmas used for step H3 of this reduction.

The new ingredient is `weak_convolution_bound`, a uniform statement that
`2^(2 * s2 n + 1)` divides the convolution numerator for every positive n,
obtained by summing the per-term comparison against the binomial row.
-/

namespace OeisA189286

private def tNat (k : ℕ) : ℕ := (6 * k).choose (3 * k) * (3 * k).choose k

private def sNat (n : ℕ) : ℕ := ∑ k ∈ Finset.range (n + 1), tNat k * tNat (n - k)

private lemma tNat_pos (k : ℕ) : 0 < tNat k :=
  Nat.mul_pos (Nat.choose_pos (by omega)) (Nat.choose_pos (by omega))

private lemma sNat_pos (n : ℕ) : 0 < sNat n :=
  Finset.sum_pos (fun k _ => Nat.mul_pos (tNat_pos k) (tNat_pos (n - k)))
    ⟨0, Finset.mem_range.mpr (Nat.succ_pos n)⟩

private lemma denom_pos {n : ℕ} (hn : 0 < n) : 0 < (2 * n - 1) * (3 * n).choose n :=
  Nat.mul_pos (by omega) (Nat.choose_pos (by omega))

private lemma a_eq_div_nat {n : ℕ} (hn : 0 < n) :
    a n = (sNat n : ℚ) / (((2 * n - 1) * (3 * n).choose n : ℕ) : ℚ) := by
  unfold a sNat tTerm
  have hsub : ((2 * n - 1 : ℕ) : ℚ) = 2 * (n : ℚ) - 1 := by
    rw [Nat.cast_sub (by omega)]
    push_cast
    rfl
  simp only [tNat, Nat.cast_sum, Nat.cast_mul, hsub]

private lemma tNat_mul_factorials (k : ℕ) :
    tNat k * (3 * k).factorial * (2 * k).factorial * k.factorial = (6 * k).factorial := by
  have h1 : (6 * k).choose (3 * k) * (3 * k).factorial * (3 * k).factorial = (6 * k).factorial := by
    have := Nat.choose_mul_factorial_mul_factorial (n := 6 * k) (k := 3 * k) (by omega)
    rwa [show 6 * k - 3 * k = 3 * k by omega] at this
  have h2 : (3 * k).choose k * k.factorial * (2 * k).factorial = (3 * k).factorial := by
    have := Nat.choose_mul_factorial_mul_factorial (n := 3 * k) (k := k) (by omega)
    rwa [show 3 * k - k = 2 * k by omega] at this
  calc
    tNat k * (3 * k).factorial * (2 * k).factorial * k.factorial
        = (6 * k).choose (3 * k) * (3 * k).factorial *
            ((3 * k).choose k * k.factorial * (2 * k).factorial) := by
            unfold tNat; ring
    _ = (6 * k).choose (3 * k) * (3 * k).factorial * (3 * k).factorial := by rw [h2]
    _ = (6 * k).factorial := h1

private lemma choose_3n_mul_factorials (n : ℕ) :
    (3 * n).choose n * n.factorial * (2 * n).factorial = (3 * n).factorial := by
  have := Nat.choose_mul_factorial_mul_factorial (n := 3 * n) (k := n) (by omega)
  rwa [show 3 * n - n = 2 * n by omega] at this

private def fStep (q r : ℕ) : ℕ := 6 * r / q - 3 * r / q - 2 * r / q

private def gStep (q r : ℕ) : ℕ := 3 * r / q - 2 * r / q

private lemma nat_div_eq_of_le_lt {q m j : ℕ} (hq : 0 < q)
    (h1 : j * q ≤ m) (h2 : m < (j + 1) * q) : m / q = j :=
  le_antisymm (Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul hq).mpr h2))
    ((Nat.le_div_iff_mul_le hq).mpr h1)

private lemma fStep_spec {q r : ℕ} (hq : 0 < q) (hr : r < q) :
    3 * r / q + 2 * r / q ≤ 6 * r / q ∧
    fStep q r = if 6 * r < q then 0 else if 6 * r < 5 * q then 1 else 2 := by
  unfold fStep
  by_cases h1 : 6 * r < q
  · have h6 : 6 * r / q = 0 := nat_div_eq_of_le_lt hq (by omega) (by omega)
    have h3 : 3 * r / q = 0 := nat_div_eq_of_le_lt hq (by omega) (by omega)
    have h2 : 2 * r / q = 0 := nat_div_eq_of_le_lt hq (by omega) (by omega)
    simp [h1, h6, h3, h2]
  · by_cases h2 : 6 * r < 2 * q
    · have h6 : 6 * r / q = 1 := nat_div_eq_of_le_lt hq (by omega) (by omega)
      have h3 : 3 * r / q = 0 := nat_div_eq_of_le_lt hq (by omega) (by omega)
      have h2' : 2 * r / q = 0 := nat_div_eq_of_le_lt hq (by omega) (by omega)
      rw [if_neg h1, if_pos (by omega)]
      omega
    · by_cases h3 : 6 * r < 3 * q
      · have h6 : 6 * r / q = 2 := nat_div_eq_of_le_lt hq (by omega) (by omega)
        have h3' : 3 * r / q = 1 := nat_div_eq_of_le_lt hq (by omega) (by omega)
        have h2' : 2 * r / q = 0 := nat_div_eq_of_le_lt hq (by omega) (by omega)
        rw [if_neg h1, if_pos (by omega)]
        omega
      · by_cases h4 : 6 * r < 4 * q
        · have h6 : 6 * r / q = 3 := nat_div_eq_of_le_lt hq (by omega) (by omega)
          have h3' : 3 * r / q = 1 := nat_div_eq_of_le_lt hq (by omega) (by omega)
          have h2' : 2 * r / q = 1 := nat_div_eq_of_le_lt hq (by omega) (by omega)
          rw [if_neg h1, if_pos (by omega)]
          omega
        · by_cases h5 : 6 * r < 5 * q
          · have h6 : 6 * r / q = 4 := nat_div_eq_of_le_lt hq (by omega) (by omega)
            have h3' : 3 * r / q = 2 := nat_div_eq_of_le_lt hq (by omega) (by omega)
            have h2' : 2 * r / q = 1 := nat_div_eq_of_le_lt hq (by omega) (by omega)
            rw [if_neg h1, if_pos h5]
            omega
          · have h6 : 6 * r / q = 5 := nat_div_eq_of_le_lt hq (by omega) (by omega)
            have h3' : 3 * r / q = 2 := nat_div_eq_of_le_lt hq (by omega) (by omega)
            have h2' : 2 * r / q = 1 := nat_div_eq_of_le_lt hq (by omega) (by omega)
            rw [if_neg h1, if_neg h5]
            omega

private lemma gStep_spec {q r : ℕ} (hq : 0 < q) (hr : r < q) :
    2 * r / q ≤ 3 * r / q ∧
    gStep q r = if (2 * q ≤ 6 * r ∧ 6 * r < 3 * q) ∨ 4 * q ≤ 6 * r then 1 else 0 := by
  unfold gStep
  by_cases h1 : 6 * r < 2 * q
  · have h3 : 3 * r / q = 0 := nat_div_eq_of_le_lt hq (by omega) (by omega)
    have h2 : 2 * r / q = 0 := nat_div_eq_of_le_lt hq (by omega) (by omega)
    rw [if_neg (by omega)]
    omega
  · by_cases h2 : 6 * r < 3 * q
    · have h3 : 3 * r / q = 1 := nat_div_eq_of_le_lt hq (by omega) (by omega)
      have h2' : 2 * r / q = 0 := nat_div_eq_of_le_lt hq (by omega) (by omega)
      rw [if_pos (by omega)]
      omega
    · by_cases h3 : 6 * r < 4 * q
      · have h3' : 3 * r / q = 1 := nat_div_eq_of_le_lt hq (by omega) (by omega)
        have h2' : 2 * r / q = 1 := nat_div_eq_of_le_lt hq (by omega) (by omega)
        rw [if_neg (by omega)]
        omega
      · have h3' : 3 * r / q = 2 := nat_div_eq_of_le_lt hq (by omega) (by omega)
        have h2' : 2 * r / q = 1 := nat_div_eq_of_le_lt hq (by omega) (by omega)
        rw [if_pos (by omega)]
        omega

private lemma div_six_eq {q a : ℕ} (hq : 0 < q) :
    6 * a / q = 3 * a / q + 2 * a / q + a / q + fStep q (a % q) := by
  have hmul : ∀ c : ℕ, c * a / q = c * (a / q) + c * (a % q) / q := by
    intro c
    have hda : q * (a / q) + a % q = a := Nat.div_add_mod a q
    have heq : c * a = c * (a % q) + q * (c * (a / q)) := by
      calc c * a = c * (q * (a / q) + a % q) := by rw [hda]
        _ = c * (a % q) + q * (c * (a / q)) := by ring
    rw [heq, Nat.add_mul_div_left _ _ hq]
    omega
  have hle := (fStep_spec hq (Nat.mod_lt a hq)).1
  have h6 := hmul 6
  have h3 := hmul 3
  have h2 := hmul 2
  unfold fStep
  omega

private lemma div_three_eq {q a : ℕ} (hq : 0 < q) :
    3 * a / q = 2 * a / q + a / q + gStep q (a % q) := by
  have hmul : ∀ c : ℕ, c * a / q = c * (a / q) + c * (a % q) / q := by
    intro c
    have hda : q * (a / q) + a % q = a := Nat.div_add_mod a q
    have heq : c * a = c * (a % q) + q * (c * (a / q)) := by
      calc c * a = c * (q * (a / q) + a % q) := by rw [hda]
        _ = c * (a % q) + q * (c * (a / q)) := by ring
    rw [heq, Nat.add_mul_div_left _ _ hq]
    omega
  have hle := (gStep_spec hq (Nat.mod_lt a hq)).1
  have h3 := hmul 3
  have h2 := hmul 2
  unfold gStep
  omega

private lemma padicValNat_tNat_eq_sum {p k b : ℕ} [hp : Fact p.Prime]
    (hb : Nat.log p (6 * k) < b) :
    padicValNat p (tNat k) = ∑ i ∈ Finset.Ico 1 b, fStep (p ^ i) (k % p ^ i) := by
  have hfac := congrArg (padicValNat p) (tNat_mul_factorials k)
  rw [padicValNat.mul
        (mul_ne_zero (mul_ne_zero (tNat_pos k).ne' (Nat.factorial_ne_zero _))
          (Nat.factorial_ne_zero _))
        (Nat.factorial_ne_zero _),
      padicValNat.mul (mul_ne_zero (tNat_pos k).ne' (Nat.factorial_ne_zero _))
        (Nat.factorial_ne_zero _),
      padicValNat.mul (tNat_pos k).ne' (Nat.factorial_ne_zero _)] at hfac
  rw [padicValNat_factorial hb,
      padicValNat_factorial (lt_of_le_of_lt (Nat.log_mono_right (by omega)) hb),
      padicValNat_factorial (lt_of_le_of_lt (Nat.log_mono_right (by omega)) hb),
      padicValNat_factorial (lt_of_le_of_lt (Nat.log_mono_right (by omega)) hb)] at hfac
  have hsum : ∑ i ∈ Finset.Ico 1 b, 6 * k / p ^ i =
      ∑ i ∈ Finset.Ico 1 b, (3 * k / p ^ i + 2 * k / p ^ i + k / p ^ i +
        fStep (p ^ i) (k % p ^ i)) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    exact div_six_eq (pow_pos hp.out.pos i)
  rw [hsum, Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib] at hfac
  omega

private lemma padicValNat_choose_3n_eq_sum {p n b : ℕ} [hp : Fact p.Prime]
    (hb : Nat.log p (3 * n) < b) :
    padicValNat p ((3 * n).choose n) = ∑ i ∈ Finset.Ico 1 b, gStep (p ^ i) (n % p ^ i) := by
  have hfac := congrArg (padicValNat p) (choose_3n_mul_factorials n)
  rw [padicValNat.mul (mul_ne_zero (Nat.choose_pos (by omega)).ne' (Nat.factorial_ne_zero _))
        (Nat.factorial_ne_zero _),
      padicValNat.mul (Nat.choose_pos (by omega)).ne' (Nat.factorial_ne_zero _)] at hfac
  rw [padicValNat_factorial hb,
      padicValNat_factorial (lt_of_le_of_lt (Nat.log_mono_right (by omega)) hb),
      padicValNat_factorial (lt_of_le_of_lt (Nat.log_mono_right (by omega)) hb)] at hfac
  have hsum : ∑ i ∈ Finset.Ico 1 b, 3 * n / p ^ i =
      ∑ i ∈ Finset.Ico 1 b, (2 * n / p ^ i + n / p ^ i + gStep (p ^ i) (n % p ^ i)) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    exact div_three_eq (pow_pos hp.out.pos i)
  rw [hsum, Finset.sum_add_distrib, Finset.sum_add_distrib] at hfac
  omega

private lemma padicValNat_eq_sum_ite_dvd {p x b : ℕ} [hp : Fact p.Prime]
    (hx : 0 < x) (hb : Nat.log p x < b) :
    padicValNat p x = ∑ i ∈ Finset.Ico 1 b, if p ^ i ∣ x then 1 else 0 := by
  have hr : padicValNat p x < b := lt_of_le_of_lt (padicValNat_le_nat_log x) hb
  have hfilt : (Finset.Ico 1 b).filter (fun i => p ^ i ∣ x) =
      Finset.Ico 1 (padicValNat p x + 1) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_Ico, padicValNat_dvd_iff_le hx.ne']
    omega
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul, mul_one,
      hfilt, Nat.card_Ico]
  omega

private lemma gStep_le_fStep_add {q k m : ℕ} (hq : 0 < q) :
    gStep q ((k + m) % q) ≤ fStep q (k % q) + fStep q (m % q) := by
  have hfk := (fStep_spec hq (Nat.mod_lt k hq)).2
  have hfm := (fStep_spec hq (Nat.mod_lt m hq)).2
  have hgn := (gStep_spec hq (Nat.mod_lt (k + m) hq)).2
  have hmod : (k + m) % q = (k % q + m % q) % q := Nat.add_mod k m q
  by_cases hkm : k % q + m % q < q
  · rw [Nat.mod_eq_of_lt hkm] at hmod
    rw [hmod] at hgn ⊢
    split_ifs at hfk hfm hgn <;> omega
  · have hsub : (k + m) % q = k % q + m % q - q := by
      have hklt := Nat.mod_lt k hq
      have hmlt := Nat.mod_lt m hq
      rw [hmod, Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    rw [hsub] at hgn ⊢
    have hklt := Nat.mod_lt k hq
    have hmlt := Nat.mod_lt m hq
    split_ifs at hfk hfm hgn <;> omega

private lemma two_mul_mod_of_dvd {q n : ℕ} (hn : 0 < n) (hq : 2 ≤ q) (hdiv : q ∣ 2 * n - 1) :
    2 * (n % q) = q + 1 := by
  rcases hdiv with ⟨c, hc⟩
  have hr : n % q < q := Nat.mod_lt n (by omega)
  have hdivmod : q * (n / q) + n % q = n := Nat.div_add_mod n q
  have h2n : 2 * n = q * c + 1 := by omega
  have heq : q * c + 1 = 2 * (q * (n / q)) + 2 * (n % q) := by linarith
  have h1 : c < 2 * (n / q) + 2 := by nlinarith
  have h2 : 2 * (n / q) ≤ c := by
    by_contra hlt
    have hle : c + 1 ≤ 2 * (n / q) := by omega
    have hmul : q * c + q ≤ 2 * (q * (n / q)) := by
      calc q * c + q = q * (c + 1) := by ring
        _ ≤ q * (2 * (n / q)) := Nat.mul_le_mul_left q hle
        _ = 2 * (q * (n / q)) := by ring
    omega
  have hne : c ≠ 2 * (n / q) := by
    intro h
    rw [h] at heq
    have : 2 * (n % q) = 1 := by linarith
    omega
  have hc_eq : c = 2 * (n / q) + 1 := by omega
  rw [hc_eq] at heq
  linarith

private lemma dvd_of_two_mul_mod {q n : ℕ} (hn : 0 < n) (hmod : 2 * (n % q) = q + 1) :
    q ∣ 2 * n - 1 := by
  refine ⟨2 * (n / q) + 1, ?_⟩
  have hdivmod : q * (n / q) + n % q = n := Nat.div_add_mod n q
  have : 2 * n = q * (2 * (n / q) + 1) + 1 := by linarith
  omega

private lemma gStep_add_one_le_fStep_add {q k m : ℕ} (hq : 5 ≤ q) (hn : 0 < k + m)
    (hdiv : q ∣ 2 * (k + m) - 1) :
    1 + gStep q ((k + m) % q) ≤ fStep q (k % q) + fStep q (m % q) := by
  have hqpos : 0 < q := by omega
  have h2 := two_mul_mod_of_dvd hn (by omega) hdiv
  have hgn := (gStep_spec hqpos (Nat.mod_lt (k + m) hqpos)).2
  have hg0 : gStep q ((k + m) % q) = 0 := by
    rw [hgn, if_neg (by omega)]
  rw [hg0, add_zero]
  have hfk := (fStep_spec hqpos (Nat.mod_lt k hqpos)).2
  have hfm := (fStep_spec hqpos (Nat.mod_lt m hqpos)).2
  by_contra hlt
  have hfk0 : fStep q (k % q) = 0 := by omega
  have hfm0 : fStep q (m % q) = 0 := by omega
  have hksmall : 6 * (k % q) < q := by
    by_contra h
    rw [hfk, if_neg h] at hfk0
    by_cases h5 : 6 * (k % q) < 5 * q
    · rw [if_pos h5] at hfk0; omega
    · rw [if_neg h5] at hfk0; omega
  have hmsmall : 6 * (m % q) < q := by
    by_contra h
    rw [hfm, if_neg h] at hfm0
    by_cases h5 : 6 * (m % q) < 5 * q
    · rw [if_pos h5] at hfm0; omega
    · rw [if_neg h5] at hfm0; omega
  have hmod : (k + m) % q = k % q + m % q := by
    rw [Nat.add_mod, Nat.mod_eq_of_lt (by omega)]
  omega

private lemma mod_three_mul {q a : ℕ} (hq : 0 < q) :
    a % (3 * q) = ((a / q) % 3) * q + a % q := by
  have h1 : q * (a / q) + a % q = a := Nat.div_add_mod a q
  have h2 : 3 * ((a / q) / 3) + (a / q) % 3 = a / q := Nat.div_add_mod (a / q) 3
  have h3 : (a / q) % 3 < 3 := Nat.mod_lt _ (by omega)
  have h4 : a % q < q := Nat.mod_lt _ hq
  have hlt : ((a / q) % 3) * q + a % q < 3 * q := by nlinarith
  have heq : a = ((a / q) % 3 * q + a % q) + (3 * q) * ((a / q) / 3) := by nlinarith
  conv_lhs => rw [heq]
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]

private lemma exists_surplus_base3_aux {k m : ℕ} (hn : 0 < k + m)
    (hk3 : k % 3 = 0) (hm3 : m % 3 = 2) :
    ∃ j ∈ Finset.Ico 2 (padicValNat 3 (2 * (k + m) - 1) + 2),
      (if 3 ^ j ∣ 2 * (k + m) - 1 then 1 else 0) + gStep (3 ^ j) ((k + m) % 3 ^ j) + 1 ≤
        fStep (3 ^ j) (k % 3 ^ j) + fStep (3 ^ j) (m % 3 ^ j) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set n := k + m
  set r := padicValNat 3 (2 * n - 1)
  have h3dvd : 3 ∣ 2 * n - 1 := by
    refine dvd_of_two_mul_mod hn ?_
    have : n % 3 = (k % 3 + m % 3) % 3 := Nat.add_mod k m 3
    omega
  have hr1 : 1 ≤ r := one_le_padicValNat_of_dvd (by omega) h3dvd
  by_contra hnone
  push Not at hnone
  have hstep : ∀ j, 1 ≤ j → j ≤ r → k % 3 ^ j = 0 ∧ 2 * (m % 3 ^ j) = 3 ^ j + 1 := by
    intro j hj1 hjr
    induction j with
    | zero => omega
    | succ j ih =>
      by_cases hj0 : j = 0
      · subst hj0
        simpa using ⟨hk3, by omega⟩
      · have ⟨hkj, hmj⟩ := ih (by omega) (by omega)
        set q := 3 ^ j
        have hqpos : 0 < q := pow_pos (by omega : 0 < 3) j
        have h3q : 3 ^ (j + 1) = 3 * q := by rw [pow_succ']
        have h3q_pos : 0 < 3 ^ (j + 1) := pow_pos (by omega : 0 < 3) (j + 1)
        have h3q_ge : 5 ≤ 3 ^ (j + 1) := by
          have : 3 ^ 2 ≤ 3 ^ (j + 1) := Nat.pow_le_pow_right (by omega) (by omega)
          omega
        have hdvd_next : 3 ^ (j + 1) ∣ 2 * n - 1 :=
          (padicValNat_dvd_iff_le (p := 3) (by omega)).mpr hjr
        have hgn0 : gStep (3 ^ (j + 1)) (n % 3 ^ (j + 1)) = 0 := by
          have h2n := two_mul_mod_of_dvd hn (by omega) hdvd_next
          have hgs := (gStep_spec h3q_pos (Nat.mod_lt n h3q_pos)).2
          rw [hgs, if_neg (by omega)]
        have hbound := hnone (j + 1) (Finset.mem_Ico.mpr ⟨by omega, by omega⟩)
        rw [if_pos hdvd_next, hgn0, add_zero] at hbound
        have hk_next : k % (3 * q) = ((k / q) % 3) * q := by
          rw [mod_three_mul hqpos, hkj, add_zero]
        have hm_next : m % (3 * q) = ((m / q) % 3) * q + m % q := mod_three_mul hqpos
        have hfm_ge : 1 ≤ fStep (3 ^ (j + 1)) (m % 3 ^ (j + 1)) := by
          have hfs := (fStep_spec h3q_pos (Nat.mod_lt m h3q_pos)).2
          rw [h3q, hm_next] at hfs ⊢
          have h6m : 3 * q ≤ 6 * (((m / q) % 3) * q + m % q) := by
            have : 0 ≤ ((m / q) % 3) * q := Nat.zero_le _
            omega
          rw [hfs, if_neg (by omega)]
          split_ifs <;> omega
        have hfk_eq0 : fStep (3 ^ (j + 1)) (k % 3 ^ (j + 1)) = 0 := by omega
        have hdk0 : (k / q) % 3 = 0 := by
          have hfs := (fStep_spec h3q_pos (Nat.mod_lt k h3q_pos)).2
          rw [h3q, hk_next] at hfs hfk_eq0
          have hlt : 6 * (((k / q) % 3) * q) < 3 * q := by
            by_contra hge
            rw [hfs, if_neg hge] at hfk_eq0
            by_cases h5 : 6 * (((k / q) % 3) * q) < 5 * (3 * q)
            · rw [if_pos h5] at hfk_eq0; omega
            · rw [if_neg h5] at hfk_eq0; omega
          by_contra hne
          have h1 : 1 ≤ (k / q) % 3 := by omega
          have hmul : 1 * q ≤ ((k / q) % 3) * q := Nat.mul_le_mul_right q h1
          omega
        have hk_zero : k % 3 ^ (j + 1) = 0 := by rw [h3q, hk_next, hdk0, zero_mul]
        have hm_eq : m % 3 ^ (j + 1) = n % 3 ^ (j + 1) := by
          have hmod : n % 3 ^ (j + 1) = (k % 3 ^ (j + 1) + m % 3 ^ (j + 1)) % 3 ^ (j + 1) :=
            Nat.add_mod k m _
          rw [hk_zero, zero_add, Nat.mod_mod] at hmod
          exact hmod.symm
        exact ⟨hk_zero, hm_eq.symm ▸ two_mul_mod_of_dvd hn (by omega) hdvd_next⟩
  have ⟨hkr, hmr⟩ := hstep r hr1 le_rfl
  set q := 3 ^ r
  have hq3 : 3 ≤ q := by
    calc 3 = 3 ^ 1 := by norm_num
      _ ≤ 3 ^ r := Nat.pow_le_pow_right (by omega) hr1
  have hqpos : 0 < q := by omega
  have h3q : 3 ^ (r + 1) = 3 * q := by rw [pow_succ']
  have hndvd : ¬ 3 ^ (r + 1) ∣ 2 * n - 1 := pow_succ_padicValNat_not_dvd (p := 3) (by omega)
  have hbound := hnone (r + 1) (Finset.mem_Ico.mpr ⟨by omega, by omega⟩)
  rw [if_neg hndvd, zero_add, h3q] at hbound
  set dk := (k / q) % 3
  set dm := (m / q) % 3
  have hdk_lt : dk < 3 := Nat.mod_lt _ (by omega)
  have hdm_lt : dm < 3 := Nat.mod_lt _ (by omega)
  have hk_next : k % (3 * q) = dk * q := by rw [mod_three_mul hqpos, hkr, add_zero]
  have hm_next : m % (3 * q) = dm * q + m % q := mod_three_mul hqpos
  have hn_next : n % (3 * q) = ((dk + dm) % 3) * q + m % q := by
    have hmq_lt : m % q < q := Nat.mod_lt m hqpos
    have h1 : n % (3 * q) = (k % (3 * q) + m % (3 * q)) % (3 * q) := Nat.add_mod k m _
    rw [hk_next, hm_next] at h1
    have h2 : dk * q + (dm * q + m % q) =
        (((dk + dm) % 3) * q + m % q) + (3 * q) * ((dk + dm) / 3) := by
      have := Nat.div_add_mod (dk + dm) 3
      nlinarith
    have h3 : ((dk + dm) % 3) * q + m % q < 3 * q := by
      have : (dk + dm) % 3 < 3 := Nat.mod_lt _ (by omega)
      nlinarith
    rw [h1, h2, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h3]
  have hneq1 : (dk + dm) % 3 ≠ 1 := by
    intro h1
    apply hndvd
    rw [h3q]
    refine dvd_of_two_mul_mod hn ?_
    rw [hn_next, h1]
    omega
  have hfk := (fStep_spec (by omega : 0 < 3 * q) (Nat.mod_lt k (by omega))).2
  have hfm := (fStep_spec (by omega : 0 < 3 * q) (Nat.mod_lt m (by omega))).2
  have hgn := (gStep_spec (by omega : 0 < 3 * q) (Nat.mod_lt n (by omega))).2
  rw [hk_next, hm_next, hn_next] at hbound
  rw [hk_next] at hfk
  rw [hm_next] at hfm
  rw [hn_next] at hgn
  interval_cases dk <;> interval_cases dm <;>
    simp only [Nat.reduceAdd, Nat.reduceMod, zero_mul, one_mul, zero_add] at hneq1 hbound hfk hfm hgn ⊢
  all_goals
    try exact absurd rfl hneq1
  all_goals
    split_ifs at hfk hfm hgn <;> omega

private lemma padicValNat_denom_le_tNat_mul {p n k m : ℕ} (hp : p.Prime)
    (hn : 0 < n) (hkm : k + m = n) :
    padicValNat p ((2 * n - 1) * (3 * n).choose n) ≤ padicValNat p (tNat k * tNat m) := by
  have : Fact p.Prime := ⟨hp⟩
  set b := Nat.log p (6 * n) + 1
  have hb6n : Nat.log p (6 * n) < b := Nat.lt_succ_self _
  have hb6k : Nat.log p (6 * k) < b := lt_of_le_of_lt (Nat.log_mono_right (by omega)) hb6n
  have hb6m : Nat.log p (6 * m) < b := lt_of_le_of_lt (Nat.log_mono_right (by omega)) hb6n
  have hb3n : Nat.log p (3 * n) < b := lt_of_le_of_lt (Nat.log_mono_right (by omega)) hb6n
  have hb2n : Nat.log p (2 * n - 1) < b := lt_of_le_of_lt (Nat.log_mono_right (by omega)) hb6n
  rw [padicValNat.mul (by omega) (Nat.choose_pos (by omega)).ne',
      padicValNat.mul (tNat_pos k).ne' (tNat_pos m).ne',
      padicValNat_eq_sum_ite_dvd (by omega) hb2n,
      padicValNat_choose_3n_eq_sum hb3n,
      padicValNat_tNat_eq_sum hb6k,
      padicValNat_tNat_eq_sum hb6m,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  by_cases h3 : p = 3 ∧ 3 ∣ 2 * n - 1
  · rcases h3 with ⟨rfl, h3dvd⟩
    set L : ℕ → ℕ := fun i => (if 3 ^ i ∣ 2 * n - 1 then 1 else 0) + gStep (3 ^ i) (n % 3 ^ i)
    set R : ℕ → ℕ := fun i => fStep (3 ^ i) (k % 3 ^ i) + fStep (3 ^ i) (m % 3 ^ i)
    change ∑ i ∈ Finset.Ico 1 b, L i ≤ ∑ i ∈ Finset.Ico 1 b, R i
    have hge2 : ∀ i ∈ Finset.Ico 2 b, L i ≤ R i := by
      intro i hi
      rw [Finset.mem_Ico] at hi
      dsimp only [L, R]
      by_cases hd : 3 ^ i ∣ 2 * n - 1
      · rw [if_pos hd, ← hkm]
        have h3i_ge : 5 ≤ 3 ^ i := by
          have : 3 ^ 2 ≤ 3 ^ i := Nat.pow_le_pow_right (by omega) hi.1
          omega
        exact gStep_add_one_le_fStep_add h3i_ge (by omega) (hkm ▸ hd)
      · rw [if_neg hd, zero_add, ← hkm]
        exact gStep_le_fStep_add (pow_pos (by omega : 0 < 3) i)
    by_cases hL1 : L 1 ≤ R 1
    · refine Finset.sum_le_sum fun i hi => ?_
      rw [Finset.mem_Ico] at hi
      by_cases hi1 : i = 1
      · subst hi1; exact hL1
      · exact hge2 i (Finset.mem_Ico.mpr ⟨by omega, hi.2⟩)
    · have h2n3 : n % 3 = 2 := by
        have := two_mul_mod_of_dvd hn (by omega) h3dvd
        omega
      have hL1_val : L 1 = 2 := by
        dsimp only [L]
        rw [pow_one, if_pos h3dvd, h2n3]
        decide
      have hk3_lt : k % 3 < 3 := Nat.mod_lt k (by omega)
      have hm3_lt : m % 3 < 3 := Nat.mod_lt m (by omega)
      have hkm3 : (k % 3 + m % 3) % 3 = 2 := by
        rw [← Nat.add_mod, hkm, h2n3]
      have hfk1 := (fStep_spec (q := 3) (r := k % 3) (by omega) hk3_lt).2
      have hfm1 := (fStep_spec (q := 3) (r := m % 3) (by omega) hm3_lt).2
      have hcases : (k % 3 = 0 ∧ m % 3 = 2) ∨ (k % 3 = 2 ∧ m % 3 = 0) := by
        have hR1 : R 1 < 2 := by omega
        dsimp only [R] at hR1
        rw [pow_one] at hR1
        split_ifs at hfk1 hfm1 <;> omega
      have hR1_val : R 1 = 1 := by
        dsimp only [R]
        rw [pow_one]
        rcases hcases with ⟨hk0, hm2⟩ | ⟨hk2, hm0⟩
        · rw [hk0, hm2]; decide
        · rw [hk2, hm0]; decide
      have hsurplus : ∃ j ∈ Finset.Ico 2 (padicValNat 3 (2 * n - 1) + 2), L j + 1 ≤ R j := by
        rcases hcases with ⟨hk0, hm2⟩ | ⟨hk2, hm0⟩
        · obtain ⟨j, hj, hle⟩ := exists_surplus_base3_aux (k := k) (m := m) (by omega) hk0 hm2
          exact ⟨j, by rwa [hkm] at hj, by simpa only [L, R, hkm] using hle⟩
        · obtain ⟨j, hj, hle⟩ := exists_surplus_base3_aux (k := m) (m := k) (by omega) hm0 hk2
          refine ⟨j, by rwa [add_comm m k, hkm] at hj, ?_⟩
          dsimp only [L, R]
          rw [add_comm m k, hkm] at hle
          omega
      obtain ⟨j, hj_mem, hj_surp⟩ := hsurplus
      rw [Finset.mem_Ico] at hj_mem
      have hr_pow : 3 ^ (padicValNat 3 (2 * n - 1) + 1) ≤ 6 * n := by
        have hpow_dvd : 3 ^ padicValNat 3 (2 * n - 1) ∣ 2 * n - 1 := pow_padicValNat_dvd
        have hle : 3 ^ padicValNat 3 (2 * n - 1) ≤ 2 * n - 1 := Nat.le_of_dvd (by omega) hpow_dvd
        rw [pow_succ']
        omega
      have hr_lt_b : padicValNat 3 (2 * n - 1) + 1 < b :=
        Nat.lt_succ_of_le (Nat.le_log_of_pow_le (by omega) hr_pow)
      have hj_in : j ∈ Finset.Ico 2 b := Finset.mem_Ico.mpr ⟨hj_mem.1, by omega⟩
      have h1b : 1 < b := by omega
      rw [Finset.sum_eq_sum_Ico_succ_bot h1b, Finset.sum_eq_sum_Ico_succ_bot h1b]
      rw [← Finset.add_sum_erase _ _ hj_in, ← Finset.add_sum_erase _ _ hj_in]
      have hrest : ∑ i ∈ (Finset.Ico 2 b).erase j, L i ≤ ∑ i ∈ (Finset.Ico 2 b).erase j, R i :=
        Finset.sum_le_sum fun i hi => hge2 i (Finset.mem_of_mem_erase hi)
      omega
  · refine Finset.sum_le_sum fun i hi => ?_
    rw [Finset.mem_Ico] at hi
    by_cases hd : p ^ i ∣ 2 * n - 1
    · rw [if_pos hd, ← hkm]
      have hp_dvd : p ∣ 2 * n - 1 := dvd_trans (dvd_pow_self p (by omega)) hd
      have hp2 : p ≠ 2 := by
        intro h2
        rw [h2] at hp_dvd
        omega
      have hp3 : p ≠ 3 := fun h3' => h3 ⟨h3', h3' ▸ hp_dvd⟩
      have hp5 : 5 ≤ p := by
        have := hp.two_le
        have hne4 : p ≠ 4 := by intro h4; rw [h4] at hp; exact absurd hp (by decide)
        omega
      have hpi5 : 5 ≤ p ^ i :=
        le_trans hp5 (by simpa only [pow_one] using Nat.pow_le_pow_right hp.pos hi.1)
      exact gStep_add_one_le_fStep_add hpi5 (by omega) (hkm ▸ hd)
    · rw [if_neg hd, zero_add, ← hkm]
      exact gStep_le_fStep_add (pow_pos hp.pos i)

private lemma denom_dvd_tNat_mul {n k m : ℕ} (hn : 0 < n) (hkm : k + m = n) :
    (2 * n - 1) * (3 * n).choose n ∣ tNat k * tNat m := by
  rw [← Nat.factorization_le_iff_dvd (denom_pos hn).ne'
      (Nat.mul_pos (tNat_pos k) (tNat_pos m)).ne']
  intro p
  by_cases hp : p.Prime
  · rw [Nat.factorization_def _ hp, Nat.factorization_def _ hp]
    exact padicValNat_denom_le_tNat_mul hp hn hkm
  · simp [Nat.factorization_eq_zero_of_not_prime _ hp]

private lemma denom_dvd_sNat {n : ℕ} (hn : 0 < n) :
    (2 * n - 1) * (3 * n).choose n ∣ sNat n := by
  unfold sNat
  refine Finset.dvd_sum fun k hk => ?_
  have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  exact denom_dvd_tNat_mul hn (Nat.add_sub_of_le hkn)

-- 2-adic digit-sum machinery

private def s2 (n : ℕ) : ℕ := (Nat.digits 2 n).sum

private lemma padicValNat_two_fac (n : ℕ) : padicValNat 2 n.factorial = n - s2 n := by
  have := sub_one_mul_padicValNat_factorial (p := 2) n
  simpa [s2] using this

private lemma s2_le_self (n : ℕ) : s2 n ≤ n := by
  exact Nat.digit_sum_le 2 n

private lemma s2_mul_two (n : ℕ) : s2 (2 * n) = s2 n := by
  by_cases hn : n = 0
  · subst hn; simp [s2]
  · unfold s2
    rw [Nat.digits_def' (by norm_num : 1 < 2) (by omega : 0 < 2 * n)]
    have h1 : (2 * n) % 2 = 0 := by omega
    have h2 : (2 * n) / 2 = n := by omega
    simp [h1, h2]

private lemma s2_pow_two (k : ℕ) : s2 (2 ^ k) = 1 := by
  induction k with
  | zero => decide
  | succ k ih =>
    rw [pow_succ', s2_mul_two, ih]

private lemma s2_eq_zero_iff (n : ℕ) : s2 n = 0 ↔ n = 0 := by
  constructor
  · intro h
    by_contra hne
    have hnil : Nat.digits 2 n ≠ [] := Nat.digits_ne_nil_iff_ne_zero.mpr hne
    have hpos : 0 < (Nat.digits 2 n).sum := by
      have hlast : (Nat.digits 2 n).getLast hnil ≠ 0 := Nat.getLast_digit_ne_zero 2 hne
      have hmem : (Nat.digits 2 n).getLast hnil ∈ Nat.digits 2 n := List.getLast_mem hnil
      exact List.sum_pos_iff_exists_pos_nat.mpr ⟨_, hmem, Nat.pos_of_ne_zero hlast⟩
    unfold s2 at h
    omega
  · rintro rfl; simp [s2]

private lemma s2_eq_one_iff (n : ℕ) : s2 n = 1 ↔ ∃ k : ℕ, n = 2 ^ k := by
  constructor
  · induction n using Nat.strong_induction_on with
    | h n ih =>
      intro hs1
      have hn0 : n ≠ 0 := fun h => by subst h; simp [s2] at hs1
      have hdef : Nat.digits 2 n = n % 2 :: Nat.digits 2 (n / 2) :=
        Nat.digits_def' (by norm_num) (Nat.pos_of_ne_zero hn0)
      unfold s2 at hs1
      rw [hdef, List.sum_cons] at hs1
      by_cases hpar : n % 2 = 0
      · have hhalf : s2 (n / 2) = 1 := by unfold s2; omega
        obtain ⟨k, hk⟩ := ih (n / 2) (Nat.div_lt_self (Nat.pos_of_ne_zero hn0) (by norm_num)) hhalf
        refine ⟨k + 1, ?_⟩
        rw [pow_succ']
        omega
      · have hmod1 : n % 2 = 1 := by omega
        have hhalf0 : s2 (n / 2) = 0 := by unfold s2; omega
        have hdiv0 : n / 2 = 0 := (s2_eq_zero_iff _).mp hhalf0
        refine ⟨0, ?_⟩
        omega
  · rintro ⟨k, rfl⟩
    exact s2_pow_two k

private lemma s2_three_mul_ge_two {n : ℕ} (hn : 0 < n) : 2 ≤ s2 (3 * n) := by
  by_contra hlt
  have hcases : s2 (3 * n) = 0 ∨ s2 (3 * n) = 1 := by omega
  rcases hcases with h0 | h1
  · have := (s2_eq_zero_iff (3 * n)).mp h0
    omega
  · obtain ⟨k, hk⟩ := (s2_eq_one_iff (3 * n)).mp h1
    have h3dvd : 3 ∣ 2 ^ k := ⟨n, hk.symm⟩
    have h3_dvd_2 : 3 ∣ 2 := Nat.Prime.dvd_of_dvd_pow (by decide : Nat.Prime 3) h3dvd
    omega

private lemma padicValNat_two_T (k : ℕ) : padicValNat 2 (tNat k) = 2 * s2 k := by
  have hfac := tNat_mul_factorials k
  have hT_pos : 0 < tNat k := mul_pos (Nat.choose_pos (by omega)) (Nat.choose_pos (by omega))
  have hv := congrArg (padicValNat 2) hfac
  simp only [padicValNat.mul, hT_pos.ne', Nat.factorial_ne_zero, mul_ne_zero_iff, ne_eq,
    not_false_eq_true, and_self, padicValNat_two_fac] at hv
  have h6 : s2 (6 * k) = s2 (3 * k) := by rw [show 6 * k = 2 * (3 * k) by ring, s2_mul_two]
  have h2 : s2 (2 * k) = s2 k := s2_mul_two k
  have hle6 := s2_le_self (6 * k)
  have hle3 := s2_le_self (3 * k)
  have hle2 := s2_le_self (2 * k)
  have hle1 := s2_le_self k
  omega

private lemma padicValNat_two_choose3 (n : ℕ) :
    padicValNat 2 ((3 * n).choose n) = 2 * s2 n - s2 (3 * n) := by
  have hfac : (3 * n).choose n * n.factorial * (2 * n).factorial = (3 * n).factorial := by
    have := Nat.choose_mul_factorial_mul_factorial (show n ≤ 3 * n by omega)
    simpa [show 3 * n - n = 2 * n by omega] using this
  have hc_pos : 0 < (3 * n).choose n := Nat.choose_pos (by omega)
  have hv := congrArg (padicValNat 2) hfac
  simp only [padicValNat.mul, hc_pos.ne', Nat.factorial_ne_zero, mul_ne_zero_iff, ne_eq,
    not_false_eq_true, and_self, padicValNat_two_fac, s2_mul_two] at hv
  have hle3 := s2_le_self (3 * n)
  have hle2 := s2_le_self (2 * n)
  have hle1 := s2_le_self n
  omega

private lemma choose_digits {n k : ℕ} (hk : k ≤ n) :
    padicValNat 2 (n.choose k) + s2 n = s2 k + s2 (n-k) := by
  have hv := congrArg (padicValNat 2) (Nat.choose_mul_factorial_mul_factorial hk)
  have hc := (Nat.choose_pos hk).ne'
  simp only [padicValNat.mul, hc, Nat.factorial_ne_zero, mul_ne_zero_iff, ne_eq,
    not_false_eq_true, and_self, padicValNat_two_fac] at hv
  have := s2_le_self n
  have := s2_le_self k
  have := s2_le_self (n-k)
  omega

private lemma term_comparison {n k : ℕ} (hk : k ≤ n) :
    2 ^ (2*s2 n+1) ∣ tNat k * tNat (n-k) + 2^(2*s2 n) * n.choose k := by
  let x := tNat k * tNat (n-k)
  have hx : x ≠ 0 := mul_ne_zero (tNat_pos _).ne' (tNat_pos _).ne'
  have hval : padicValNat 2 x = 2*s2 n + 2*padicValNat 2 (n.choose k) := by
    dsimp [x]
    rw [padicValNat.mul (tNat_pos _).ne' (tNat_pos _).ne', padicValNat_two_T,
      padicValNat_two_T]
    have := choose_digits hk
    omega
  obtain ⟨q, hq⟩ := (padicValNat_dvd_iff_le (p := 2) hx).2
    (show 2*s2 n ≤ padicValNat 2 x by omega)
  have hq0 : q ≠ 0 := by rintro rfl; simp [hq] at hx
  have hqv : padicValNat 2 q = 2 * padicValNat 2 (n.choose k) := by
    rw [hq, padicValNat.mul (by positivity) hq0, padicValNat.prime_pow] at hval
    omega
  have hpar : 2 ∣ q ↔ 2 ∣ n.choose k := by
    rw [dvd_iff_padicValNat_ne_zero hq0, dvd_iff_padicValNat_ne_zero (Nat.choose_pos hk).ne']
    omega
  have hsum : 2 ∣ q + n.choose k := by omega
  change 2^(2*s2 n+1) ∣ x + _
  rw [hq, ← Nat.mul_add, pow_succ]
  exact Nat.mul_dvd_mul_left _ hsum

/-- Uniform weak bound: `2^(2 * s2 n + 1)` divides the convolution numerator, for every positive n. -/
private lemma weak_convolution_bound {n : ℕ} (hn : 0 < n) :
    2 ^ (2 * s2 n + 1) ∣ sNat n := by
  have hsum : 2 ^ (2 * s2 n + 1) ∣
      ∑ k ∈ Finset.range (n + 1), (tNat k * tNat (n - k) + 2 ^ (2 * s2 n) * n.choose k) := by
    refine Finset.dvd_sum fun k hk => ?_
    have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    exact term_comparison hkn
  have hsum' : (∑ k ∈ Finset.range (n + 1),
        (tNat k * tNat (n - k) + 2 ^ (2 * s2 n) * n.choose k))
      = sNat n + 2 ^ (2 * s2 n) * 2 ^ n := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Nat.sum_range_choose]
    rfl
  rw [hsum'] at hsum
  have hcancel : 2 ^ (2 * s2 n + 1) ∣ 2 ^ (2 * s2 n) * 2 ^ n := by
    rw [pow_add]
    exact Nat.mul_dvd_mul_left _ (pow_dvd_pow 2 (by omega))
  exact (Nat.dvd_add_iff_left hcancel).mpr hsum

end OeisA189286

open OeisA189286 in
theorem OMA.solution : OMA.R_OeisA189286_conjecture_3_R1.H1 := by
  intro n hn
  obtain ⟨q, hq⟩ := denom_dvd_sNat hn
  have hq0 : q ≠ 0 := by
    intro hz
    have := sNat_pos n
    rw [hq, hz, mul_zero] at this
    omega
  have hvq : padicValNat 2 (sNat n) =
      padicValNat 2 ((2 * n - 1) * (3 * n).choose n) + padicValNat 2 q := by
    rw [hq, padicValNat.mul (denom_pos hn).ne' hq0]
  have hb : 2 ^ (2 * s2 n + 1) ∣ sNat n := weak_convolution_bound hn
  have hv : 2 * s2 n + 1 ≤ padicValNat 2 (sNat n) :=
    (padicValNat_dvd_iff_le (p := 2) (sNat_pos n).ne').1 hb
  have hq3 : 3 ≤ padicValNat 2 q := by
    have hs3 : 2 ≤ s2 (3 * n) := s2_three_mul_ge_two hn
    have hDrel : padicValNat 2 ((2 * n - 1) * (3 * n).choose n) + s2 (3 * n) = 2 * s2 n := by
      have hodd : padicValNat 2 (2 * n - 1) = 0 := padicValNat.eq_zero_of_not_dvd (by omega)
      have hc := choose_digits (n := 3 * n) (k := n) (by omega)
      rw [show 3 * n - n = 2 * n by omega, s2_mul_two] at hc
      rw [padicValNat.mul (by omega) (Nat.choose_pos (by omega)).ne', hodd, zero_add]
      rw [hc]
      ring
    have hv' : 2 * s2 n + 1 ≤ padicValNat 2 ((2 * n - 1) * (3 * n).choose n) + padicValNat 2 q := by
      rw [hvq] at hv
      exact hv
    omega
  have h8q : 8 ∣ q := (padicValNat_dvd_iff_le (p := 2) hq0).2 hq3
  obtain ⟨r, hr⟩ := h8q
  refine ⟨(r : ℤ), ?_⟩
  rw [a_eq_div_nat hn, hq]
  have hden : (((2 * n - 1) * (3 * n).choose n : ℕ) : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (denom_pos hn).ne'
  rw [div_eq_iff hden, hr]
  push_cast
  ring
