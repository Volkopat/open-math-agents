import OMAStatements.S_oeis_a334886
import Mathlib

/-!
# Proof of Peter Bala's conjecture in OEIS A334886

`a(n)` is the numerator of `S(n) = 2 * Sum_{k=0..n} C(n,k)^2 * C(n+k,k)^2 * (H(n+k) - H(n-k))`.
Claim: `p^2` divides `a(p-1)` for every prime `p >= 5`.

Write `p = m + 1`. All sums below are over `1 <= k <= m`; the term `k = 0` of `S(m)` is zero.

1. `C(m+k,k) * k = C(m+k,k-1) * p` and `gcd(p,k) = 1`, so `C(m+k,k) = p * e(k)` with an integer `e(k)`,
   and `e(k) * k = C(p+(k-1),k-1) = 1` modulo `p` (Lucas).
2. `H(m+k) - H(m-k) = Sum_{m-k <= i < m+k} 1/(i+1)`, and exactly one term, `i = m`, has the denominator
   `p`. With `L = Prod_{i < 2m, i != m} (i+1)` (prime to `p`) this gives
   `p * L * (H(m+k) - H(m-k)) = L + p * LR(k)` for an integer `LR(k)`.
3. Hence `L * S(m) = 2p * (L*W + p*V)` with the integers `W = Sum C(m,k)^2 e(k)^2` and
   `V = Sum C(m,k)^2 e(k)^2 LR(k)`.
4. Modulo `p`: `C(m,k)^2 = 1` and `e(k)^2 = e(k)^2 k^(p-1) = (e(k) k)^2 k^(p-3) = k^(p-3)`, so
   `W = Sum_{k=1..p-1} k^(p-3) = 0` because `0 < p - 3 < p - 1` (this is where `p >= 5` is used).
5. So `L * S(m)` is an integer divisible by `p^2` with `p` not dividing `L`; therefore `p^2` divides
   the numerator of `S(m)`.
-/

/-- L1: if `D * q = Z` with integers `D`, `Z`, `p ∤ D` and `p^2 ∣ Z`, then `p^2 ∣ q.num`. -/
private lemma a334886_num_dvd {p : ℕ} (hp : p.Prime) (q : ℚ) (D Z : ℤ)
    (hD : ¬ (p : ℤ) ∣ D) (hZ : (p : ℤ) ^ 2 ∣ Z) (h : (D : ℚ) * q = (Z : ℚ)) :
    (p : ℤ) ^ 2 ∣ q.num := by
  have h1 : (D : ℚ) * (q.num : ℚ) = (Z : ℚ) * (q.den : ℚ) := by
    rw [← Rat.mul_den_eq_num q, ← mul_assoc, h]
  have h2 : D * q.num = Z * (q.den : ℤ) := by exact_mod_cast h1
  have h3 : (p : ℤ) ^ 2 ∣ D * q.num := by
    rw [h2]
    exact Dvd.dvd.mul_right hZ _
  have hpi : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hcop : IsCoprime ((p : ℤ) ^ 2) D :=
    IsCoprime.pow_left ((Prime.coprime_iff_not_dvd hpi).mpr hD)
  exact hcop.dvd_of_dvd_mul_left h3

/-- L2: `H(b) - H(a) = Sum_{a <= i < b} 1/(i+1)`. -/
private lemma a334886_harmonic_sub {a b : ℕ} (hab : a ≤ b) :
    harmonic b - harmonic a = ∑ i ∈ Finset.Ico a b, ((i : ℚ) + 1)⁻¹ := by
  rw [Finset.sum_Ico_eq_sub _ hab]
  unfold harmonic
  push_cast
  rfl

/-- The indices `i < 2m`, `i ≠ m` (the numbers `i + 1` in `[1, 2m]` other than `p = m + 1`). -/
private def a334886_J (m : ℕ) : Finset ℕ := (Finset.range (2 * m)).erase m

/-- `L = (2m)!/(m+1)`. -/
private def a334886_L (m : ℕ) : ℕ := ∏ i ∈ a334886_J m, (i + 1)

/-- `L/(i+1)`. -/
private def a334886_Lq (m i : ℕ) : ℕ := ∏ j ∈ (a334886_J m).erase i, (j + 1)

/-- `L * Sum_{m-k <= i < m+k, i ≠ m} 1/(i+1)`. -/
private def a334886_LR (m k : ℕ) : ℕ :=
  ∑ i ∈ (Finset.Ico (m - k) (m + k)).erase m, a334886_Lq m i

/-- L3: `p * L * (H(m+k) - H(m-k)) = L + p * LR(k)` with `p = m + 1`, `1 <= k <= m`. -/
private lemma a334886_L_harm {m k : ℕ} (hk1 : 1 ≤ k) (hkm : k ≤ m) :
    ((m : ℚ) + 1) * (a334886_L m : ℚ) * (harmonic (m + k) - harmonic (m - k)) =
      (a334886_L m : ℚ) + ((m : ℚ) + 1) * (a334886_LR m k : ℚ) := by
  rw [a334886_harmonic_sub (by omega : m - k ≤ m + k)]
  have hmem : m ∈ Finset.Ico (m - k) (m + k) := Finset.mem_Ico.mpr ⟨by omega, by omega⟩
  rw [← Finset.add_sum_erase _ _ hmem]
  have hterm : ∀ i ∈ (Finset.Ico (m - k) (m + k)).erase m,
      (a334886_L m : ℚ) * ((i : ℚ) + 1)⁻¹ = (a334886_Lq m i : ℚ) := by
    intro i hi
    rw [Finset.mem_erase, Finset.mem_Ico] at hi
    have hiJ : i ∈ a334886_J m := by
      unfold a334886_J
      rw [Finset.mem_erase, Finset.mem_range]
      exact ⟨hi.1, by omega⟩
    have h := Finset.mul_prod_erase (a334886_J m) (fun j => j + 1) hiJ
    have h' : ((i : ℚ) + 1) * (a334886_Lq m i : ℚ) = (a334886_L m : ℚ) := by
      have h2 := congrArg (Nat.cast : ℕ → ℚ) h
      unfold a334886_Lq a334886_L
      push_cast at h2 ⊢
      exact h2
    have hne : ((i : ℚ) + 1) ≠ 0 := by positivity
    rw [← h']
    field_simp
  have hsum : (a334886_L m : ℚ) * ∑ i ∈ (Finset.Ico (m - k) (m + k)).erase m, ((i : ℚ) + 1)⁻¹
      = (a334886_LR m k : ℚ) := by
    rw [Finset.mul_sum, Finset.sum_congr rfl hterm]
    unfold a334886_LR
    push_cast
    rfl
  have hne : ((m : ℚ) + 1) ≠ 0 := by positivity
  rw [← hsum]
  field_simp

/-- `e(k) = C(m+k,k)/(m+1)`. -/
private def a334886_e (m k : ℕ) : ℕ := (m + k).choose k / (m + 1)

/-- L4: for `p = m + 1` prime and `1 <= k <= m`: `p * e(k) = C(m+k,k)` and `e(k) * k = C(m+k,k-1)`. -/
private lemma a334886_e_spec {m k : ℕ} (hp : (m + 1).Prime) (hk1 : 1 ≤ k) (hkm : k ≤ m) :
    (m + 1) * a334886_e m k = (m + k).choose k ∧
      a334886_e m k * k = (m + k).choose (k - 1) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hrec := Nat.choose_succ_right_eq (m + (j + 1)) j
  have hsub : m + (j + 1) - j = m + 1 := by omega
  rw [hsub] at hrec
  have hcop : (m + 1).Coprime (j + 1) :=
    Nat.coprime_of_lt_prime (by omega) (by omega) hp
  have hdvd : (m + 1) ∣ (m + (j + 1)).choose (j + 1) :=
    hcop.dvd_of_dvd_mul_right ⟨_, hrec.trans (mul_comm _ _)⟩
  have h1 : (m + 1) * a334886_e m (j + 1) = (m + (j + 1)).choose (j + 1) :=
    Nat.mul_div_cancel' hdvd
  refine ⟨h1, ?_⟩
  rw [Nat.add_sub_cancel]
  have h2 : (m + 1) * (a334886_e m (j + 1) * (j + 1)) = (m + 1) * (m + (j + 1)).choose j := by
    rw [← mul_assoc, h1, hrec, mul_comm]
  exact Nat.eq_of_mul_eq_mul_left (by omega) h2

/-- L5: `C(p + j, j) = 1` in `ZMod p` for `j < p`. -/
private lemma a334886_choose_add {p j : ℕ} [Fact p.Prime] (hj : j < p) :
    (((p + j).choose j : ℕ) : ZMod p) = 1 := by
  have hp : p.Prime := Fact.out
  have h := @Choose.choose_modEq_choose_mod_mul_choose_div_nat (p + j) j p _
  rw [Nat.add_mod_left, Nat.mod_eq_of_lt hj, Nat.add_div_left _ hp.pos, Nat.div_eq_of_lt hj,
    Nat.choose_self, Nat.choose_zero_right, mul_one] at h
  have h2 := (ZMod.natCast_eq_natCast_iff _ _ p).mpr h
  rw [h2, Nat.cast_one]

/-- L6: `C(p-1,k)^2 = 1` in `ZMod p`. -/
private lemma a334886_choose_pred_sq {p m : ℕ} [Fact p.Prime] (hpm : p = m + 1) (k : ℕ) (hk : k ≤ m) :
    ((m.choose k : ℕ) : ZMod p) ^ 2 = 1 := by
  have hp : p.Prime := Fact.out
  induction k with
  | zero => simp
  | succ k ih =>
    have ih' := ih (by omega)
    have hsum : m.choose k + m.choose (k + 1) = p.choose (k + 1) := by
      rw [hpm, Nat.choose_succ_succ]
    have hdvd : p ∣ p.choose (k + 1) := hp.dvd_choose_self (by omega) (by omega)
    have hz : ((p.choose (k + 1) : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hdvd
    have hcast := congrArg (Nat.cast : ℕ → ZMod p) hsum
    rw [hz, Nat.cast_add] at hcast
    have hneg : ((m.choose (k + 1) : ℕ) : ZMod p) = -((m.choose k : ℕ) : ZMod p) := by
      linear_combination hcast
    rw [hneg, neg_sq, ih']

/-- L7: `Sum_{k=1..p-1} k^(p-3) = 0` in `ZMod p` for a prime `p >= 5`. -/
private lemma a334886_sum_pow {p m : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) (hpm : p = m + 1) :
    ∑ k ∈ Finset.Icc 1 m, ((k : ℕ) : ZMod p) ^ (p - 3) = 0 := by
  have hbij : ∑ k ∈ Finset.Icc 1 m, ((k : ℕ) : ZMod p) ^ (p - 3) = ∑ x : ZMod p, x ^ (p - 3) := by
    symm
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : ZMod p))]
    rw [zero_pow (by omega : p - 3 ≠ 0), zero_add]
    refine Finset.sum_nbij (fun x => x.val) ?_ ?_ ?_ ?_
    · intro x hx
      simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hx
      simp only [Finset.mem_Icc]
      have hpos : 0 < x.val := Nat.pos_of_ne_zero fun h => hx ((ZMod.val_eq_zero x).mp h)
      have hlt : x.val < p := x.val_lt
      omega
    · intro a _ b _ h; exact ZMod.val_injective p h
    · intro k hk
      simp only [Finset.mem_coe, Finset.mem_Icc] at hk
      refine ⟨(k : ZMod p), ?_, ZMod.val_natCast_of_lt (by omega)⟩
      simp only [Finset.mem_coe, Finset.mem_erase, Finset.mem_univ, and_true]
      intro h0
      exact Nat.not_dvd_of_pos_of_lt hk.1 (by omega) ((ZMod.natCast_eq_zero_iff k p).mp h0)
    · intro x _; rw [ZMod.natCast_zmod_val]
  rw [hbij]
  apply FiniteField.sum_pow_lt_card_sub_one
  rw [ZMod.card]
  omega

/-- `W = Sum_{k=1..m} C(m,k)^2 e(k)^2`. -/
private def a334886_W (m : ℕ) : ℕ :=
  ∑ k ∈ Finset.Icc 1 m, (m.choose k) ^ 2 * (a334886_e m k) ^ 2

/-- `V = Sum_{k=1..m} C(m,k)^2 e(k)^2 LR(k)`. -/
private def a334886_V (m : ℕ) : ℕ :=
  ∑ k ∈ Finset.Icc 1 m, (m.choose k) ^ 2 * (a334886_e m k) ^ 2 * a334886_LR m k

/-- L8: `p ∣ W`. -/
private lemma a334886_W_zero {p m : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) (hpm : p = m + 1) :
    ((a334886_W m : ℕ) : ZMod p) = 0 := by
  have hp : p.Prime := Fact.out
  unfold a334886_W
  rw [Nat.cast_sum, ← a334886_sum_pow hp5 hpm]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.mem_Icc] at hk
  have hspec := a334886_e_spec (hpm ▸ hp) hk.1 hk.2
  have hek : ((a334886_e m k : ℕ) : ZMod p) * ((k : ℕ) : ZMod p) = 1 := by
    have h1 : m + k = p + (k - 1) := by omega
    have h2 := a334886_choose_add (p := p) (j := k - 1) (by omega)
    rw [← h1, ← hspec.2, Nat.cast_mul] at h2
    exact h2
  have hk0 : ((k : ℕ) : ZMod p) ≠ 0 := by
    intro h0
    exact Nat.not_dvd_of_pos_of_lt hk.1 (by omega) ((ZMod.natCast_eq_zero_iff k p).mp h0)
  have hfer : ((k : ℕ) : ZMod p) ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one hk0
  have hsplit : p - 1 = 2 + (p - 3) := by omega
  rw [hsplit, pow_add] at hfer
  push_cast
  rw [a334886_choose_pred_sq hpm k hk.2, one_mul]
  calc ((a334886_e m k : ℕ) : ZMod p) ^ 2
      = ((a334886_e m k : ℕ) : ZMod p) ^ 2 * (((k : ℕ) : ZMod p) ^ 2 * ((k : ℕ) : ZMod p) ^ (p - 3)) := by
        rw [hfer, mul_one]
    _ = (((a334886_e m k : ℕ) : ZMod p) * ((k : ℕ) : ZMod p)) ^ 2 * ((k : ℕ) : ZMod p) ^ (p - 3) := by
        ring
    _ = ((k : ℕ) : ZMod p) ^ (p - 3) := by rw [hek, one_pow, one_mul]

/-- L9: the `k`-th term of `L * S / 2`. -/
private lemma a334886_term {m k : ℕ} (hp : (m + 1).Prime) (hk1 : 1 ≤ k) (hkm : k ≤ m) :
    (a334886_L m : ℚ) *
        ((m.choose k : ℚ) ^ 2 * ((m + k).choose k : ℚ) ^ 2 * (harmonic (m + k) - harmonic (m - k))) =
      ((m : ℚ) + 1) *
        ((((m.choose k) ^ 2 * (a334886_e m k) ^ 2 : ℕ) : ℚ) * (a334886_L m : ℚ) +
          ((m : ℚ) + 1) * (((m.choose k) ^ 2 * (a334886_e m k) ^ 2 * a334886_LR m k : ℕ) : ℚ)) := by
  have hspec := (a334886_e_spec hp hk1 hkm).1
  have hC : (((m + k).choose k : ℕ) : ℚ) = ((m : ℚ) + 1) * (a334886_e m k : ℚ) := by
    rw [← hspec]
    push_cast
    ring
  have hH := a334886_L_harm hk1 hkm
  rw [hC]
  push_cast
  linear_combination ((m.choose k : ℚ) ^ 2 * (a334886_e m k : ℚ) ^ 2 * ((m : ℚ) + 1)) * hH

/-- L10: `L * S = 2 p (L W + p V)`. -/
private lemma a334886_sum_identity {m : ℕ} (hp : (m + 1).Prime) :
    (a334886_L m : ℚ) *
        (2 * ∑ k ∈ Finset.range (m + 1),
          ((m.choose k : ℚ) ^ 2 * ((m + k).choose k : ℚ) ^ 2 *
            (harmonic (m + k) - harmonic (m - k)))) =
      2 * ((m : ℚ) + 1) *
        ((a334886_W m : ℚ) * (a334886_L m : ℚ) + ((m : ℚ) + 1) * (a334886_V m : ℚ)) := by
  have hsub : ∑ k ∈ Finset.range (m + 1),
        ((m.choose k : ℚ) ^ 2 * ((m + k).choose k : ℚ) ^ 2 *
          (harmonic (m + k) - harmonic (m - k))) =
      ∑ k ∈ Finset.Icc 1 m,
        ((m.choose k : ℚ) ^ 2 * ((m + k).choose k : ℚ) ^ 2 *
          (harmonic (m + k) - harmonic (m - k))) := by
    symm
    apply Finset.sum_subset
    · intro k hk
      rw [Finset.mem_Icc] at hk
      rw [Finset.mem_range]
      omega
    · intro k hk hk'
      rw [Finset.mem_range] at hk
      rw [Finset.mem_Icc] at hk'
      have hk0 : k = 0 := by omega
      subst hk0
      simp
  rw [hsub, mul_left_comm, Finset.mul_sum]
  rw [Finset.sum_congr rfl fun k hk =>
    a334886_term hp (Finset.mem_Icc.mp hk).1 (Finset.mem_Icc.mp hk).2]
  rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum]
  unfold a334886_W a334886_V
  push_cast
  ring

/-- `p ∤ L`. -/
private lemma a334886_L_not_dvd {m : ℕ} (hp : (m + 1).Prime) : ¬ (m + 1) ∣ a334886_L m := by
  intro h
  unfold a334886_L at h
  obtain ⟨i, hi, hdvd⟩ := (Prime.dvd_finsetProd_iff (Nat.Prime.prime hp) _).mp h
  unfold a334886_J at hi
  rw [Finset.mem_erase, Finset.mem_range] at hi
  obtain ⟨c, hc⟩ := hdvd
  rcases c with _ | _ | c
  · omega
  · omega
  · have : (m + 1) * (c + 1 + 1) = (m + 1) * c + 2 * (m + 1) := by ring
    omega

theorem OMA.solution : type_of% @OMA.S_oeis_a334886.main := by
  intro p hp hp5
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨m, hpm⟩ : ∃ m, p = m + 1 := ⟨p - 1, by omega⟩
  have hm : p - 1 = m := by omega
  rw [hm]
  unfold OMA.S_oeis_a334886.a
  have hp' : (m + 1).Prime := hpm ▸ hp
  have hW : (p : ℤ) ∣ (a334886_W m : ℤ) := by
    rw [Int.natCast_dvd_natCast, ← ZMod.natCast_eq_zero_iff]
    exact a334886_W_zero hp5 hpm
  obtain ⟨w, hw⟩ := hW
  refine a334886_num_dvd hp _ (a334886_L m : ℤ)
    (2 * (p : ℤ) * ((a334886_W m : ℤ) * (a334886_L m : ℤ) + (p : ℤ) * (a334886_V m : ℤ))) ?_ ?_ ?_
  · rw [Int.natCast_dvd_natCast, hpm]
    exact a334886_L_not_dvd hp'
  · rw [hw]
    exact ⟨2 * (w * (a334886_L m : ℤ) + (a334886_V m : ℤ)), by ring⟩
  · have h := a334886_sum_identity hp'
    rw [hpm]
    push_cast
    rw [h]
