import OMAStatements.S_oeis_a035378

open Polynomial

namespace ProofA035378

abbrev F5 := ZMod 5

lemma five_eq_zero_F5 : (5 : F5) = 0 := by decide
lemma two_mul_three_F5 : (2 : F5) * 3 = 1 := by decide
lemma four_mul_two_F5 : (4 : F5) * 2 = 3 := by decide
lemma twentyfour_eq_four_F5 : (24 : F5) = 4 := by decide

lemma sub_pow_five {A : Type*} [CommRing A] (h5 : (5 : A) = 0) (a b : A) :
    (a - b) ^ 5 = a ^ 5 - b ^ 5 := by
  have h : (a - b) ^ 5 = a ^ 5 - b ^ 5 -
      5 * (a ^ 4 * b - 2 * a ^ 3 * b ^ 2 + 2 * a ^ 2 * b ^ 3 - a * b ^ 4) := by ring
  rw [h, h5, zero_mul, sub_zero]

lemma sub_pow_five_pow {A : Type*} [CommRing A] (h5 : (5 : A) = 0) (a b : A) :
    ∀ k : ℕ, (a - b) ^ (5 ^ k) = a ^ (5 ^ k) - b ^ (5 ^ k)
  | 0 => by simp
  | k + 1 => by
    rw [pow_succ, pow_mul, sub_pow_five_pow h5 a b k, sub_pow_five h5, ← pow_mul, ← pow_mul]

/-! ### Part 1: Modulo-5 coefficient structure `Good` in `(ZMod 5)[X]` -/

def Good (f : F5[X]) : Prop :=
  ∀ k : ℕ, f.coeff (5 * k + 3) = 0 ∧ f.coeff (5 * k + 4) = 0 ∧
    f.coeff (5 * k + 2) = 2 * f.coeff (5 * k + 1)

lemma good_zero : Good 0 := by
  intro k; simp

lemma good_add {f g : F5[X]} (hf : Good f) (hg : Good g) : Good (f + g) := by
  intro k
  obtain ⟨hf3, hf4, hf2⟩ := hf k
  obtain ⟨hg3, hg4, hg2⟩ := hg k
  refine ⟨?_, ?_, ?_⟩
  · simp [hf3, hg3]
  · simp [hf4, hg4]
  · simp [hf2, hg2, mul_add]

lemma good_sub {f g : F5[X]} (hf : Good f) (hg : Good g) : Good (f - g) := by
  intro k
  obtain ⟨hf3, hf4, hf2⟩ := hf k
  obtain ⟨hg3, hg4, hg2⟩ := hg k
  refine ⟨?_, ?_, ?_⟩
  · simp [hf3, hg3]
  · simp [hf4, hg4]
  · simp [hf2, hg2, mul_sub]

lemma good_C_mul (c : F5) {f : F5[X]} (hf : Good f) : Good (C c * f) := by
  intro k
  obtain ⟨hf3, hf4, hf2⟩ := hf k
  refine ⟨?_, ?_, ?_⟩
  · simp [hf3]
  · simp [hf4]
  · simp only [coeff_C_mul, hf2]; ring

lemma good_sum {ι : Type*} (s : Finset ι) (f : ι → F5[X]) (hf : ∀ i ∈ s, Good (f i)) :
    Good (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using good_zero
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact good_add (hf a (Finset.mem_insert_self a s))
      (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)))

lemma good_X5_mul {f : F5[X]} (hf : Good f) : Good (X ^ 5 * f) := by
  intro k
  cases k with
  | zero =>
    simp [coeff_X_pow_mul']
  | succ m =>
    obtain ⟨h3, h4, h2⟩ := hf m
    have e3 : 5 * (m + 1) + 3 = 5 * m + 3 + 5 := by omega
    have e4 : 5 * (m + 1) + 4 = 5 * m + 4 + 5 := by omega
    have e2 : 5 * (m + 1) + 2 = 5 * m + 2 + 5 := by omega
    have e1 : 5 * (m + 1) + 1 = 5 * m + 1 + 5 := by omega
    rw [e3, e4, e2, e1, coeff_X_pow_mul, coeff_X_pow_mul, coeff_X_pow_mul, coeff_X_pow_mul]
    exact ⟨h3, h4, h2⟩

lemma good_X5m1_pow_mul {f : F5[X]} (hf : Good f) :
    ∀ m : ℕ, Good ((X ^ 5 - 1) ^ m * f)
  | 0 => by simpa using hf
  | m + 1 => by
    have ih := good_X5m1_pow_mul hf m
    have hsplit : (X ^ 5 - 1) ^ (m + 1) * f =
        X ^ 5 * ((X ^ 5 - 1) ^ m * f) - (X ^ 5 - 1) ^ m * f := by ring
    rw [hsplit]
    exact good_sub (good_X5_mul ih) ih

lemma good_one : Good 1 := by
  intro k
  have h3 : (1 : F5[X]).coeff (5 * k + 3) = 0 := by
    rw [coeff_one, if_neg (by omega)]
  have h4 : (1 : F5[X]).coeff (5 * k + 4) = 0 := by
    rw [coeff_one, if_neg (by omega)]
  have h2 : (1 : F5[X]).coeff (5 * k + 2) = 0 := by
    rw [coeff_one, if_neg (by omega)]
  have h1 : (1 : F5[X]).coeff (5 * k + 1) = 0 := by
    rw [coeff_one, if_neg (by omega)]
  rw [h3, h4, h2, h1, mul_zero]
  exact ⟨rfl, rfl, rfl⟩

lemma coeff_C_mul_X_pow_F5 (c : F5) (p m : ℕ) :
    (C c * (X : F5[X]) ^ p).coeff m = if m = p then c else 0 := by
  rw [coeff_C_mul, coeff_X_pow]
  split_ifs <;> simp

lemma good_Xm1_sq : Good ((X - 1 : F5[X]) ^ 2) := by
  intro k
  have hexp : (X - 1 : F5[X]) ^ 2 = C 1 * X ^ 2 + C 3 * X ^ 1 + C 1 * X ^ 0 := by
    have h3 : (-2 : F5[X]) = C 3 := by
      have : (-2 : F5) = 3 := by decide
      rw [← this, map_neg, map_ofNat]
    calc (X - 1 : F5[X]) ^ 2 = X ^ 2 + (-2 : F5[X]) * X + 1 := by ring
      _ = C 1 * X ^ 2 + C 3 * X ^ 1 + C 1 * X ^ 0 := by rw [h3]; simp
  rw [hexp]
  cases k with
  | zero =>
    simp only [Nat.mul_zero, Nat.zero_add, coeff_add, coeff_C_mul_X_pow_F5]
    decide
  | succ m =>
    simp only [coeff_add, coeff_C_mul_X_pow_F5,
      if_neg (by omega : 5 * (m + 1) + 3 ≠ 2), if_neg (by omega : 5 * (m + 1) + 3 ≠ 1),
      if_neg (by omega : 5 * (m + 1) + 3 ≠ 0), if_neg (by omega : 5 * (m + 1) + 4 ≠ 2),
      if_neg (by omega : 5 * (m + 1) + 4 ≠ 1), if_neg (by omega : 5 * (m + 1) + 4 ≠ 0),
      if_neg (by omega : 5 * (m + 1) + 2 ≠ 2), if_neg (by omega : 5 * (m + 1) + 2 ≠ 1),
      if_neg (by omega : 5 * (m + 1) + 2 ≠ 0), if_neg (by omega : 5 * (m + 1) + 1 ≠ 2),
      if_neg (by omega : 5 * (m + 1) + 1 ≠ 1), if_neg (by omega : 5 * (m + 1) + 1 ≠ 0)]
    simp

lemma good_Xm1_pow {e : ℕ} (he : e % 5 = 0 ∨ e % 5 = 2) : Good ((X - 1 : F5[X]) ^ e) := by
  have h5p : (5 : F5[X]) = 0 := by
    have := congr_arg (C : F5 →+* F5[X]) five_eq_zero_F5
    simpa [map_ofNat] using this
  have hxm1_5 : (X - 1 : F5[X]) ^ 5 = X ^ 5 - 1 := by
    simpa using sub_pow_five h5p (X : F5[X]) 1
  have hdiv : e = 5 * (e / 5) + e % 5 := (Nat.div_add_mod e 5).symm
  rw [hdiv, pow_add, pow_mul, hxm1_5]
  rcases he with h0 | h2
  · rw [h0, pow_zero]
    exact good_X5m1_pow_mul good_one (e / 5)
  · rw [h2]
    exact good_X5m1_pow_mul good_Xm1_sq (e / 5)

/-! ### Part 2: Exponent arithmetic for the two pentagonal families -/

lemma exp1_shift (r D : ℕ) :
    (r + 2 * D) * (3 * (r + 2 * D) + 1) / 2 =
      r * (3 * r + 1) / 2 + D * (6 * r + 6 * D + 1) := by
  have hpar : 2 ∣ r * (3 * r + 1) := by
    rcases Nat.even_or_odd r with ⟨k, rfl⟩ | ⟨k, rfl⟩
    · exact ⟨k * (3 * (k + k) + 1), by ring⟩
    · exact ⟨(2 * k + 1) * (3 * k + 2), by ring⟩
  obtain ⟨m, hm⟩ := hpar
  have htot : (r + 2 * D) * (3 * (r + 2 * D) + 1) =
      2 * (m + D * (6 * r + 6 * D + 1)) := by
    calc (r + 2 * D) * (3 * (r + 2 * D) + 1)
      _ = r * (3 * r + 1) + 2 * D * (6 * r + 6 * D + 1) := by ring
      _ = 2 * m + 2 * D * (6 * r + 6 * D + 1) := by rw [hm]
      _ = 2 * (m + D * (6 * r + 6 * D + 1)) := by ring
  rw [htot, hm, Nat.mul_div_right _ (by omega), Nat.mul_div_right _ (by omega)]

lemma exp2_shift (r D : ℕ) :
    (r + 2 * D + 1) * (3 * (r + 2 * D) + 2) / 2 =
      (r + 1) * (3 * r + 2) / 2 + D * (6 * r + 6 * D + 5) := by
  have hpar : 2 ∣ (r + 1) * (3 * r + 2) := by
    rcases Nat.even_or_odd r with ⟨k, rfl⟩ | ⟨k, rfl⟩
    · exact ⟨(2 * k + 1) * (3 * k + 1), by ring⟩
    · exact ⟨(k + 1) * (3 * (2 * k + 1) + 2), by ring⟩
  obtain ⟨m, hm⟩ := hpar
  have htot : (r + 2 * D + 1) * (3 * (r + 2 * D) + 2) =
      2 * (m + D * (6 * r + 6 * D + 5)) := by
    calc (r + 2 * D + 1) * (3 * (r + 2 * D) + 2)
      _ = (r + 1) * (3 * r + 2) + 2 * D * (6 * r + 6 * D + 5) := by ring
      _ = 2 * m + 2 * D * (6 * r + 6 * D + 5) := by rw [hm]
      _ = 2 * (m + D * (6 * r + 6 * D + 5)) := by ring
  rw [htot, hm, Nat.mul_div_right _ (by omega), Nat.mul_div_right _ (by omega)]

lemma exp1_mod5 (r : ℕ) :
    (6 * r + 1) % 5 = 0 ∨ (r * (3 * r + 1) / 2) % 5 = 0 ∨ (r * (3 * r + 1) / 2) % 5 = 2 := by
  obtain ⟨s, hs, hr⟩ : ∃ s < 10, r = 10 * (r / 10) + s :=
    ⟨r % 10, Nat.mod_lt r (by omega), (Nat.div_add_mod r 10).symm⟩
  set k := r / 10
  obtain ⟨Q, hQ⟩ : ∃ Q, 30 * k * k + k * (6 * s + 1) = Q := ⟨_, rfl⟩
  have hmul : r * (3 * r + 1) = 2 * (5 * Q) + s * (3 * s + 1) := by
    rw [← hQ, hr]; ring
  have hdiv : r * (3 * r + 1) / 2 = 5 * Q + s * (3 * s + 1) / 2 := by
    rw [hmul, Nat.mul_add_div (by omega)]
  have hr5 : (6 * r + 1) % 5 = (6 * s + 1) % 5 := by rw [hr]; omega
  have h5Q : (5 * Q + s * (3 * s + 1) / 2) % 5 = (s * (3 * s + 1) / 2) % 5 := by omega
  rw [hr5, hdiv, h5Q]
  interval_cases s <;> decide

lemma exp2_mod5 (r : ℕ) :
    (6 * r + 5) % 5 = 0 ∨ ((r + 1) * (3 * r + 2) / 2) % 5 = 0 ∨
      ((r + 1) * (3 * r + 2) / 2) % 5 = 2 := by
  obtain ⟨s, hs, hr⟩ : ∃ s < 10, r = 10 * (r / 10) + s :=
    ⟨r % 10, Nat.mod_lt r (by omega), (Nat.div_add_mod r 10).symm⟩
  set k := r / 10
  obtain ⟨Q, hQ⟩ : ∃ Q, 30 * k * k + k * (6 * s + 5) = Q := ⟨_, rfl⟩
  have hmul : (r + 1) * (3 * r + 2) = 2 * (5 * Q) + (s + 1) * (3 * s + 2) := by
    rw [← hQ, hr]; ring
  have hdiv : (r + 1) * (3 * r + 2) / 2 = 5 * Q + (s + 1) * (3 * s + 2) / 2 := by
    rw [hmul, Nat.mul_add_div (by omega)]
  have hr5 : (6 * r + 5) % 5 = (6 * s + 5) % 5 := by rw [hr]; omega
  have h5Q : (5 * Q + (s + 1) * (3 * s + 2) / 2) % 5 = ((s + 1) * (3 * s + 2) / 2) % 5 := by omega
  rw [hr5, hdiv, h5Q]
  interval_cases s <;> decide

/-! ### Part 3: Rogers-Fine polynomial recurrence over any commutative ring -/

section RogersFine

variable {R : Type*} [CommRing R]

noncomputable def poch (q : R) (u : R[X]) (k : ℕ) : R[X] :=
  ∏ j ∈ Finset.range k, (1 - C (q ^ j) * u)

@[simp] lemma poch_zero (q : R) (u : R[X]) : poch q u 0 = 1 := rfl

lemma poch_succ_right (q : R) (u : R[X]) (k : ℕ) :
    poch q u (k + 1) = poch q u k * (1 - C (q ^ k) * u) :=
  Finset.prod_range_succ _ k

lemma poch_succ_left (q : R) (u : R[X]) (k : ℕ) :
    poch q u (k + 1) = (1 - u) * poch q (C q * u) k := by
  unfold poch
  rw [Finset.prod_range_succ']
  have h0 : (1 - C (q ^ 0) * u) = 1 - u := by simp
  have hstep : (∏ x ∈ Finset.range k, (1 - C (q ^ (x + 1)) * u)) =
      ∏ x ∈ Finset.range k, (1 - C (q ^ x) * (C q * u)) := by
    refine Finset.prod_congr rfl fun x _ => ?_
    rw [pow_succ, map_mul, mul_assoc]
  rw [h0, hstep, mul_comm]

noncomputable def rfH (q : R) (u v : R[X]) (N : ℕ) : R[X] :=
  ∑ r ∈ Finset.range (N + 1), poch q (C q * u) r * v ^ r

noncomputable def rfS (q : R) (u : R[X]) (N : ℕ) : R[X] :=
  ∑ r ∈ Finset.range (N + 1), poch q u (r + 1) * u ^ r

lemma rfS_eq_mul_rfH (q : R) (u : R[X]) (N : ℕ) :
    rfS q u N = (1 - u) * rfH q u u N := by
  unfold rfS rfH
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [poch_succ_left, mul_assoc]

lemma rfH_left (q : R) (u v : R[X]) (N : ℕ) :
    rfH q u v (N + 1) = 1 + (1 - C q * u) * v * rfH q (C q * u) v N := by
  unfold rfH
  rw [Finset.sum_range_succ']
  simp only [poch_zero, pow_zero, mul_one]
  rw [add_comm _ 1, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [poch_succ_left, pow_succ]
  ring

lemma rfH_right (q : R) (u v : R[X]) (N : ℕ) :
    (1 - v) * rfH q u v (N + 1) =
      1 - poch q (C q * u) (N + 1) * v ^ (N + 2) - C q * u * v * rfH q u (C q * v) N := by
  have hexp : rfH q u v (N + 1) =
      1 + v * rfH q u v N - C q * u * v * rfH q u (C q * v) N := by
    have lhs_eq : rfH q u v (N + 1) =
        1 + ∑ r ∈ Finset.range (N + 1), poch q (C q * u) (r + 1) * v ^ (r + 1) := by
      unfold rfH
      rw [Finset.sum_range_succ']
      simp [add_comm]
    rw [lhs_eq]
    have hsum : (∑ r ∈ Finset.range (N + 1), poch q (C q * u) (r + 1) * v ^ (r + 1)) =
        v * rfH q u v N - C q * u * v * rfH q u (C q * v) N := by
      unfold rfH
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [poch_succ_right, pow_succ, mul_pow, map_pow]
      ring
    rw [hsum]
    ring
  have htop : rfH q u v (N + 1) = rfH q u v N + poch q (C q * u) (N + 1) * v ^ (N + 1) :=
    Finset.sum_range_succ _ (N + 1)
  have hvpow : v * v ^ (N + 1) = v ^ (N + 2) := by rw [← pow_succ']
  linear_combination hexp - v * htop - poch q (C q * u) (N + 1) * hvpow

lemma rfS_step (q : R) (u : R[X]) (N : ℕ) :
    rfS q u (N + 2) = 1 - C q * u ^ 2 - C (q ^ 2) * u ^ 3 * rfS q (C q * u) N -
      poch q (C q * u) (N + 2) * u ^ (N + 3) := by
  rw [rfS_eq_mul_rfH q u (N + 2), rfH_right q u u (N + 1),
      rfH_left q u (C q * u) N, rfS_eq_mul_rfH q (C q * u) N]
  rw [map_pow]
  ring

def eqModPow (P Q : R[X]) (B : ℕ) : Prop :=
  ∀ d < B, P.coeff d = Q.coeff d

lemma eqModPow_refl (P : R[X]) (B : ℕ) : eqModPow P P B := fun _ _ => rfl

lemma eqModPow_symm {P Q : R[X]} {B : ℕ} (h : eqModPow P Q B) : eqModPow Q P B :=
  fun d hd => (h d hd).symm

lemma eqModPow_trans {P Q S : R[X]} {B : ℕ} (h1 : eqModPow P Q B) (h2 : eqModPow Q S B) :
    eqModPow P S B := fun d hd => (h1 d hd).trans (h2 d hd)

lemma eqModPow_mono {P Q : R[X]} {B1 B2 : ℕ} (hB : B1 ≤ B2) (h : eqModPow P Q B2) :
    eqModPow P Q B1 := fun d hd => h d (lt_of_lt_of_le hd hB)

lemma eqModPow_add {P1 Q1 P2 Q2 : R[X]} {B : ℕ}
    (h1 : eqModPow P1 Q1 B) (h2 : eqModPow P2 Q2 B) :
    eqModPow (P1 + P2) (Q1 + Q2) B := by
  intro d hd; simp [h1 d hd, h2 d hd]

lemma eqModPow_mul_left (A : R[X]) {P Q : R[X]} {B : ℕ} (h : eqModPow P Q B) :
    eqModPow (A * P) (A * Q) B := by
  intro d hd
  rw [coeff_mul, coeff_mul]
  refine Finset.sum_congr rfl fun ij hij => ?_
  have hsum := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
  rw [h ij.2 (by omega)]

lemma eqModPow_zero_of_X_pow_mul (P : R[X]) {B K : ℕ} (hBK : B ≤ K) :
    eqModPow (X ^ K * P) 0 B := by
  intro d hd
  rw [coeff_zero, coeff_X_pow_mul', if_neg (by omega)]

lemma poly_eq_of_eqModPow {P Q : R[X]} {B : ℕ}
    (hP : ∀ d ≥ B, P.coeff d = 0) (hQ : ∀ d ≥ B, Q.coeff d = 0)
    (hmod : eqModPow P Q B) : P = Q := by
  ext d
  by_cases hd : d < B
  · exact hmod d hd
  · rw [hP d (by omega), hQ d (by omega)]

noncomputable def thetaTerm (q : R) (r : ℕ) : R[X] :=
  C ((-1 : R) ^ r * q ^ (r * (3 * r + 1) / 2)) * X ^ (6 * r + 1) +
    C ((-1 : R) ^ (r + 1) * q ^ ((r + 1) * (3 * r + 2) / 2)) * X ^ (6 * r + 5)

noncomputable def rfRem (q : R) (j M : ℕ) : R[X] :=
  C ((-1 : R) ^ j * q ^ (j * (3 * j + 1) / 2)) * X ^ (6 * j + 1) *
    rfS q (C (q ^ j) * X ^ 2) M

lemma rfRem_step (q : R) (j M : ℕ) :
    eqModPow (rfRem q j (M + 2)) (thetaTerm q j + rfRem q (j + 1) M) (2 * M + 6 * j + 7) := by
  unfold rfRem thetaTerm
  rw [rfS_step q (C (q ^ j) * X ^ 2) M]
  have e1 : j * (3 * j + 1) / 2 + (2 * j + 1) = (j + 1) * (3 * j + 2) / 2 := by
    have hpar : 2 ∣ j * (3 * j + 1) := by
      rcases Nat.even_or_odd j with ⟨k, rfl⟩ | ⟨k, rfl⟩
      · exact ⟨k * (3 * (k + k) + 1), by ring⟩
      · exact ⟨(2 * k + 1) * (3 * k + 2), by ring⟩
    obtain ⟨m, hm⟩ := hpar
    have h2 : (j + 1) * (3 * j + 2) = 2 * (m + (2 * j + 1)) := by
      calc (j + 1) * (3 * j + 2) = j * (3 * j + 1) + 2 * (2 * j + 1) := by ring
        _ = 2 * (m + (2 * j + 1)) := by rw [hm]; ring
    rw [hm, h2, Nat.mul_div_right _ (by omega), Nat.mul_div_right _ (by omega)]
  have e2 : j * (3 * j + 1) / 2 + (3 * j + 2) = (j + 1) * (3 * (j + 1) + 1) / 2 := by
    have hpar : 2 ∣ j * (3 * j + 1) := by
      rcases Nat.even_or_odd j with ⟨k, rfl⟩ | ⟨k, rfl⟩
      · exact ⟨k * (3 * (k + k) + 1), by ring⟩
      · exact ⟨(2 * k + 1) * (3 * k + 2), by ring⟩
    obtain ⟨m, hm⟩ := hpar
    have h2 : (j + 1) * (3 * (j + 1) + 1) = 2 * (m + (3 * j + 2)) := by
      calc (j + 1) * (3 * (j + 1) + 1) = j * (3 * j + 1) + 2 * (3 * j + 2) := by ring
        _ = 2 * (m + (3 * j + 2)) := by rw [hm]; ring
    rw [hm, h2, Nat.mul_div_right _ (by omega), Nat.mul_div_right _ (by omega)]
  set c0 : R := (-1 : R) ^ j * q ^ (j * (3 * j + 1) / 2)
  have hc1 : C c0 * (C q * (C (q ^ j) * X ^ 2) ^ 2) * X ^ (6 * j + 1) =
      - (C ((-1 : R) ^ (j + 1) * q ^ ((j + 1) * (3 * j + 2) / 2)) * X ^ (6 * j + 5)) := by
    dsimp [c0]
    rw [← e1, pow_succ (-1 : R), pow_add q, pow_add q, pow_one]
    simp only [map_mul, map_neg, map_one, map_pow]
    ring
  have hc2 : - (C c0 * (C (q ^ 2) * (C (q ^ j) * X ^ 2) ^ 3) * X ^ (6 * j + 1)) =
      C ((-1 : R) ^ (j + 1) * q ^ ((j + 1) * (3 * (j + 1) + 1) / 2)) * X ^ (6 * (j + 1) + 1) := by
    dsimp [c0]
    rw [← e2, pow_succ (-1 : R), pow_add q _ (3 * j + 2), pow_add q (3 * j) 2, pow_mul' q 3 j,
        show 6 * (j + 1) + 1 = (6 * j + 1) + 6 by ring, pow_add X (6 * j + 1) 6]
    simp only [map_mul, map_neg, map_one, map_pow]
    ring
  have hq_next : C q * (C (q ^ j) * X ^ 2) = C (q ^ (j + 1)) * X ^ 2 := by
    rw [pow_succ' q j, map_mul, mul_assoc]
  set errP : R[X] := - C c0 * poch q (C (q ^ (j + 1)) * X ^ 2) (M + 2) * C ((q ^ j) ^ (M + 3))
  have halg : C c0 * X ^ (6 * j + 1) *
      (1 - C q * (C (q ^ j) * X ^ 2) ^ 2 -
        C (q ^ 2) * (C (q ^ j) * X ^ 2) ^ 3 * rfS q (C q * (C (q ^ j) * X ^ 2)) M -
        poch q (C q * (C (q ^ j) * X ^ 2)) (M + 2) * (C (q ^ j) * X ^ 2) ^ (M + 3)) =
      (C c0 * X ^ (6 * j + 1) +
        C ((-1 : R) ^ (j + 1) * q ^ ((j + 1) * (3 * j + 2) / 2)) * X ^ (6 * j + 5) +
        C ((-1 : R) ^ (j + 1) * q ^ ((j + 1) * (3 * (j + 1) + 1) / 2)) * X ^ (6 * (j + 1) + 1) *
          rfS q (C (q ^ (j + 1)) * X ^ 2) M) +
      X ^ (2 * M + 6 * j + 7) * errP := by
    rw [hq_next]
    dsimp [errP]
    have hpowX : (C (q ^ j) * (X : R[X]) ^ 2) ^ (M + 3) =
        C ((q ^ j) ^ (M + 3)) * X ^ (2 * M + 6) := by
      rw [mul_pow, ← map_pow, ← pow_mul X 2 (M + 3)]
      congr 2
    have hXcomb : (X : R[X]) ^ (6 * j + 1) * X ^ (2 * M + 6) = X ^ (2 * M + 6 * j + 7) := by
      rw [← pow_add]; congr 1; omega
    linear_combination
      - hc1 + hc2 * rfS q (C (q ^ (j + 1)) * X ^ 2) M -
        C c0 * X ^ (6 * j + 1) * poch q (C (q ^ (j + 1)) * X ^ 2) (M + 2) * hpowX -
        C c0 * poch q (C (q ^ (j + 1)) * X ^ 2) (M + 2) * C ((q ^ j) ^ (M + 3)) * hXcomb
  rw [halg]
  intro d hd
  rw [coeff_add, coeff_X_pow_mul', if_neg (by omega), add_zero]

lemma rfRem_iter (q : R) (B : ℕ) :
    ∀ K : ℕ, eqModPow (rfRem q 0 (2 * K + B))
      ((∑ j ∈ Finset.range K, thetaTerm q j) + rfRem q K B) (2 * B + 2 * K + 3)
  | 0 => by
    simp only [Nat.mul_zero, Finset.range_zero, Finset.sum_empty, zero_add]
    exact eqModPow_refl _ _
  | K + 1 => by
    have ih := rfRem_iter q (B + 2) K
    have hcut1 : 2 * B + 2 * (K + 1) + 3 ≤ 2 * (B + 2) + 2 * K + 3 := by omega
    have ih' : eqModPow (rfRem q 0 (2 * (K + 1) + B))
        ((∑ j ∈ Finset.range K, thetaTerm q j) + rfRem q K (B + 2)) (2 * B + 2 * (K + 1) + 3) := by
      have heq : 2 * (K + 1) + B = 2 * K + (B + 2) := by omega
      rw [heq]
      exact eqModPow_mono hcut1 ih
    have hstep := rfRem_step q K B
    have hcut2 : 2 * B + 2 * (K + 1) + 3 ≤ 2 * B + 6 * K + 7 := by omega
    have hstep' := eqModPow_mono hcut2 hstep
    have hcomb := eqModPow_add (eqModPow_refl (∑ j ∈ Finset.range K, thetaTerm q j) _) hstep'
    have hsum : (∑ j ∈ Finset.range K, thetaTerm q j) + (thetaTerm q K + rfRem q (K + 1) B) =
        (∑ j ∈ Finset.range (K + 1), thetaTerm q j) + rfRem q (K + 1) B := by
      rw [Finset.sum_range_succ, add_assoc]
    rw [hsum] at hcomb
    exact eqModPow_trans ih' hcomb

lemma rf_trunc_eqModPow (q : R) (K B : ℕ) :
    eqModPow (X * rfS q (X ^ 2) (2 * K + B))
      (∑ j ∈ Finset.range K, thetaTerm q j) (min (2 * B + 2 * K + 3) (6 * K + 1)) := by
  have h0 : X * rfS q (X ^ 2) (2 * K + B) = rfRem q 0 (2 * K + B) := by
    unfold rfRem; simp
  rw [h0]
  have h1 := eqModPow_mono (Nat.min_le_left (2 * B + 2 * K + 3) (6 * K + 1)) (rfRem_iter q B K)
  have h2 : eqModPow (rfRem q K B) 0 (min (2 * B + 2 * K + 3) (6 * K + 1)) := by
    unfold rfRem
    rw [mul_assoc]
    have hcomm : C ((-1 : R) ^ K * q ^ (K * (3 * K + 1) / 2)) *
        (X ^ (6 * K + 1) * rfS q (C (q ^ K) * X ^ 2) B) =
        X ^ (6 * K + 1) * (C ((-1 : R) ^ K * q ^ (K * (3 * K + 1) / 2)) *
          rfS q (C (q ^ K) * X ^ 2) B) := by ring
    rw [hcomm]
    exact eqModPow_zero_of_X_pow_mul _ (Nat.min_le_right _ _)
  have h3 := eqModPow_add (eqModPow_refl (∑ j ∈ Finset.range K, thetaTerm q j) _) h2
  rw [add_zero] at h3
  exact eqModPow_trans h1 h3

/-! ### Part 4: Periodic collapse when `q ^ D = 1` (`E = 3 * D`) -/

lemma poch_periodic {q : R} {E : ℕ} (hqE : q ^ E = 1) (u : R[X]) (m s : ℕ) :
    poch q u (m * E + s) = poch q u E ^ m * poch q u s := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hshift : poch q u ((m + 1) * E + s) = poch q u (E + (m * E + s)) := by
      congr 1; ring
    rw [hshift]
    unfold poch at *
    rw [Finset.prod_range_add]
    have htail : (∏ x ∈ Finset.range (m * E + s), (1 - C (q ^ (E + x)) * u)) =
        ∏ x ∈ Finset.range (m * E + s), (1 - C (q ^ x) * u) := by
      refine Finset.prod_congr rfl fun x _ => ?_
      rw [pow_add, hqE, one_mul]
    rw [htail, ih, pow_succ']
    ring

lemma geom_sum_one_sub (Z : R[X]) :
    ∀ k : ℕ, (1 - Z) * (∑ i ∈ Finset.range k, Z ^ i) = 1 - Z ^ k
  | 0 => by simp
  | k + 1 => by
    rw [Finset.sum_range_succ, mul_add, geom_sum_one_sub Z k, pow_succ]
    ring

lemma lhs_periodic_id {q : R} {E : ℕ} (hqE : q ^ E = 1) (m : ℕ) :
    (1 - X ^ (2 * E) * poch q (X ^ 2) E) *
      (∑ r ∈ Finset.range (m * E), X ^ (2 * r + 1) * poch q (X ^ 2) (r + 1)) =
      (1 - (X ^ (2 * E) * poch q (X ^ 2) E) ^ m) *
        (∑ s ∈ Finset.range E, X ^ (2 * s + 1) * poch q (X ^ 2) (s + 1)) := by
  set W : R[X] := X ^ (2 * E) * poch q (X ^ 2) E
  set A : R[X] := ∑ s ∈ Finset.range E, X ^ (2 * s + 1) * poch q (X ^ 2) (s + 1)
  have hsplit : (∑ r ∈ Finset.range (m * E), X ^ (2 * r + 1) * poch q (X ^ 2) (r + 1)) =
      (∑ k ∈ Finset.range m, W ^ k) * A := by
    induction m with
    | zero => simp
    | succ m ih =>
      have hmulE : (m + 1) * E = m * E + E := Nat.succ_mul m E
      rw [hmulE, Finset.sum_range_add, ih, Finset.sum_range_succ, add_mul]
      congr 1
      dsimp [W, A]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun s _ => ?_
      have hr : m * E + s + 1 = m * E + (s + 1) := by omega
      rw [hr, poch_periodic hqE (X ^ 2) m (s + 1), mul_pow, ← pow_mul]
      have hexp : 2 * (m * E + s) + 1 = 2 * E * m + (2 * s + 1) := by ring
      rw [hexp, pow_add]
      ring
  rw [hsplit, ← mul_assoc, geom_sum_one_sub W m]

lemma theta_periodic_id {q : R} {D : ℕ} (hqD : q ^ D = 1) (m : ℕ) :
    (1 - X ^ (12 * D)) * (∑ r ∈ Finset.range (m * (2 * D)), thetaTerm q r) =
      (1 - X ^ (12 * D * m)) * (∑ s ∈ Finset.range (2 * D), thetaTerm q s) := by
  set B : R[X] := ∑ s ∈ Finset.range (2 * D), thetaTerm q s
  have hterm : ∀ k s : ℕ, thetaTerm q (k * (2 * D) + s) = X ^ (12 * D * k) * thetaTerm q s := by
    intro k s
    unfold thetaTerm
    have h1 := exp1_shift s (k * D)
    have h2 := exp2_shift s (k * D)
    have hkD : q ^ (k * D) = 1 := by rw [pow_mul', hqD, one_pow]
    have hsgn1 : (-1 : R) ^ (k * (2 * D) + s) = (-1 : R) ^ s := by
      rw [pow_add, show k * (2 * D) = 2 * (k * D) by ring, pow_mul]; simp
    have hsgn2 : (-1 : R) ^ (k * (2 * D) + s + 1) = (-1 : R) ^ (s + 1) := by
      rw [show k * (2 * D) + s + 1 = 2 * (k * D) + (s + 1) by ring, pow_add, pow_mul]; simp
    have he1 : q ^ ((k * (2 * D) + s) * (3 * (k * (2 * D) + s) + 1) / 2) =
        q ^ (s * (3 * s + 1) / 2) := by
      rw [show k * (2 * D) + s = s + 2 * (k * D) by ring, h1, pow_add, pow_mul, hkD, one_pow, mul_one]
    have he2 : q ^ ((k * (2 * D) + s + 1) * (3 * (k * (2 * D) + s) + 2) / 2) =
        q ^ ((s + 1) * (3 * s + 2) / 2) := by
      rw [show k * (2 * D) + s + 1 = s + 2 * (k * D) + 1 by ring,
          show 3 * (k * (2 * D) + s) + 2 = 3 * (s + 2 * (k * D)) + 2 by ring,
          h2, pow_add, pow_mul, hkD, one_pow, mul_one]
    rw [hsgn1, hsgn2, he1, he2]
    have hx1 : 6 * (k * (2 * D) + s) + 1 = 12 * D * k + (6 * s + 1) := by ring
    have hx2 : 6 * (k * (2 * D) + s) + 5 = 12 * D * k + (6 * s + 5) := by ring
    rw [hx1, hx2, pow_add, pow_add]
    ring
  have hsplit : (∑ r ∈ Finset.range (m * (2 * D)), thetaTerm q r) =
      (∑ k ∈ Finset.range m, (X ^ (12 * D)) ^ k) * B := by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Nat.succ_mul, Finset.sum_range_add, ih, Finset.sum_range_succ, add_mul]
      congr 1
      dsimp [B]
      rw [Finset.mul_sum, ← pow_mul]
      refine Finset.sum_congr rfl fun s _ => hterm m s
  rw [hsplit, ← mul_assoc, geom_sum_one_sub (X ^ (12 * D)) m, ← pow_mul]

lemma coeff_eq_zero_of_poch_deg (q : R) (s d : ℕ) (hd : 2 * s < d) :
    (poch q (X ^ 2) s).coeff d = 0 := by
  induction s generalizing d with
  | zero =>
    rw [poch_zero, coeff_one, if_neg (by omega)]
  | succ s ih =>
    rw [poch_succ_right, mul_sub, mul_one, coeff_sub]
    have h1 : (poch q (X ^ 2) s).coeff d = 0 := ih d (by omega)
    have h2 : (poch q (X ^ 2) s * (C (q ^ s) * X ^ 2)).coeff d = 0 := by
      have hcomm : poch q (X ^ 2) s * (C (q ^ s) * X ^ 2) =
          X ^ 2 * (C (q ^ s) * poch q (X ^ 2) s) := by ring
      rw [hcomm, coeff_X_pow_mul']
      split_ifs with hle
      · rw [coeff_C_mul, ih (d - 2) (by omega), mul_zero]
      · rfl
    rw [h1, h2, sub_zero]

lemma cross_mul_poly_id {q : R} {D : ℕ} (hD : 1 ≤ D) (hqD : q ^ D = 1) :
    (1 - X ^ (12 * D)) *
      (∑ s ∈ Finset.range (3 * D), X ^ (2 * s + 1) * poch q (X ^ 2) (s + 1)) =
      (1 - X ^ (6 * D) * poch q (X ^ 2) (3 * D)) *
        (∑ s ∈ Finset.range (2 * D), thetaTerm q s) := by
  set E := 3 * D
  have hqE : q ^ E = 1 := by dsimp [E]; rw [mul_comm, pow_mul, hqD, one_pow]
  set A : R[X] := ∑ s ∈ Finset.range E, X ^ (2 * s + 1) * poch q (X ^ 2) (s + 1)
  set B : R[X] := ∑ s ∈ Finset.range (2 * D), thetaTerm q s
  set W : R[X] := X ^ (2 * E) * poch q (X ^ 2) E
  -- Use K = 12 * D (which is 6 * (2 * D)) and M_len = 30 * D = 10 * E
  have hrf : eqModPow (X * rfS q (X ^ 2) (30 * D - 1))
      (∑ j ∈ Finset.range (12 * D), thetaTerm q j) (24 * D + 1) := by
    have harg : 30 * D - 1 = 2 * (12 * D) + (6 * D - 1) := by omega
    rw [harg]
    refine eqModPow_mono ?_ (rf_trunc_eqModPow q (12 * D) (6 * D - 1))
    omega
  have hlhs_sum : X * rfS q (X ^ 2) (30 * D - 1) =
      ∑ r ∈ Finset.range (10 * E), X ^ (2 * r + 1) * poch q (X ^ 2) (r + 1) := by
    have hlen : 30 * D - 1 + 1 = 10 * E := by dsimp [E]; omega
    unfold rfS
    rw [hlen, Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [← pow_mul X 2 r]
    have hx : (X : R[X]) * X ^ (2 * r) = X ^ (2 * r + 1) := by rw [← pow_succ' X (2 * r)]
    linear_combination poch q (X ^ 2) (r + 1) * hx
  rw [hlhs_sum] at hrf
  have hmod1 := eqModPow_mul_left ((1 - X ^ (12 * D)) * (1 - W)) hrf
  have halgL : (1 - X ^ (12 * D)) * (1 - W) *
      (∑ r ∈ Finset.range (10 * E), X ^ (2 * r + 1) * poch q (X ^ 2) (r + 1)) =
      (1 - X ^ (12 * D)) * ((1 - W ^ 10) * A) := by
    have hl := lhs_periodic_id hqE 10
    dsimp [W, A] at hl ⊢
    linear_combination (1 - X ^ (12 * D)) * hl
  have halgR : (1 - X ^ (12 * D)) * (1 - W) *
      (∑ j ∈ Finset.range (12 * D), thetaTerm q j) =
      (1 - W) * ((1 - X ^ (12 * D * 6)) * B) := by
    have hr := theta_periodic_id hqD 6
    have h6 : 6 * (2 * D) = 12 * D := by ring
    rw [h6] at hr
    dsimp [B] at hr ⊢
    linear_combination (1 - W) * hr
  rw [halgL, halgR] at hmod1
  have hW10 : eqModPow ((1 - X ^ (12 * D)) * ((1 - W ^ 10) * A))
      ((1 - X ^ (12 * D)) * A) (24 * D + 1) := by
    have hsplit : (1 - X ^ (12 * D)) * ((1 - W ^ 10) * A) =
        (1 - X ^ (12 * D)) * A + X ^ (20 * E) * (- (1 - X ^ (12 * D)) * poch q (X ^ 2) E ^ 10 * A) := by
      dsimp [W]
      rw [mul_pow, ← pow_mul, show 2 * E * 10 = 20 * E by ring]
      ring
    rw [hsplit]
    have hz := eqModPow_zero_of_X_pow_mul (- (1 - X ^ (12 * D)) * poch q (X ^ 2) E ^ 10 * A)
      (by dsimp [E]; omega : 24 * D + 1 ≤ 20 * E)
    simpa using eqModPow_add (eqModPow_refl ((1 - X ^ (12 * D)) * A) _) hz
  have hX72 : eqModPow ((1 - W) * ((1 - X ^ (12 * D * 6)) * B))
      ((1 - W) * B) (24 * D + 1) := by
    have hsplit : (1 - W) * ((1 - X ^ (12 * D * 6)) * B) =
        (1 - W) * B + X ^ (72 * D) * (- (1 - W) * B) := by
      rw [show 12 * D * 6 = 72 * D by ring]; ring
    rw [hsplit]
    have hz := eqModPow_zero_of_X_pow_mul (- (1 - W) * B) (by omega : 24 * D + 1 ≤ 72 * D)
    simpa using eqModPow_add (eqModPow_refl ((1 - W) * B) _) hz
  have hmod_final : eqModPow ((1 - X ^ (12 * D)) * A) ((1 - W) * B) (24 * D + 1) :=
    eqModPow_trans (eqModPow_symm hW10) (eqModPow_trans hmod1 hX72)
  have h6D_eq : 6 * D = 2 * E := by dsimp [E]; ring
  rw [h6D_eq]
  change (1 - X ^ (12 * D)) * A = (1 - W) * B
  refine poly_eq_of_eqModPow ?_ ?_ hmod_final
  · intro d hd
    have hA_deg : ∀ m ≥ 12 * D, A.coeff m = 0 := by
      intro m hm
      dsimp [A]
      rw [finsetSum_coeff]
      refine Finset.sum_eq_zero fun s hs => ?_
      have hsE : s < 3 * D := Finset.mem_range.mp hs
      rw [coeff_X_pow_mul']
      split_ifs with hle
      · exact coeff_eq_zero_of_poch_deg q (s + 1) (m - (2 * s + 1)) (by omega)
      · rfl
    rw [sub_mul, one_mul, coeff_sub, hA_deg d (by omega), coeff_X_pow_mul']
    split_ifs with hle
    · rw [hA_deg (d - 12 * D) (by omega), sub_zero]
    · simp
  · intro d hd
    have hB_deg : ∀ m ≥ 12 * D, B.coeff m = 0 := by
      intro m hm
      dsimp [B]
      rw [finsetSum_coeff]
      refine Finset.sum_eq_zero fun s hs => ?_
      have hsD : s < 2 * D := Finset.mem_range.mp hs
      unfold thetaTerm
      rw [coeff_add, coeff_C_mul, coeff_X_pow, if_neg (by omega), mul_zero,
          coeff_C_mul, coeff_X_pow, if_neg (by omega), mul_zero, add_zero]
    have h1mW_deg : ∀ m > 12 * D, (1 - W).coeff m = 0 := by
      intro m hm
      dsimp [W, E]
      rw [coeff_sub, coeff_one, if_neg (by omega), coeff_X_pow_mul']
      split_ifs with hle
      · rw [coeff_eq_zero_of_poch_deg q (3 * D) _ (by omega), sub_zero]
      · simp
    rw [coeff_mul]
    refine Finset.sum_eq_zero fun ij hij => ?_
    have hsum := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
    by_cases h2 : ij.2 ≥ 12 * D
    · rw [hB_deg ij.2 h2, mul_zero]
    · rw [h1mW_deg ij.1 (by omega), zero_mul]

end RogersFine

/-! ### Part 5: Evaluation at `T = 1 - X` in `R = (ZMod 5)[X] ⧸ (X ^ (5 ^ K))` -/

section EvalAtOneMinusX

lemma one_sub_pow_24 {A : Type*} [CommRing A] (u : A) :
    ∃ p : A, 1 - (1 - u) ^ 24 = 24 * u + u ^ 2 * p := by
  have sq_step : ∀ (z : A) (c p : A), z = 1 - c * u + u ^ 2 * p →
      ∃ p' : A, z ^ 2 = 1 - (2 * c) * u + u ^ 2 * p' := by
    intro z c p hz
    refine ⟨c ^ 2 + 2 * p - 2 * c * u * p + u ^ 2 * p ^ 2, ?_⟩
    rw [hz]; ring
  have h3 : (1 - u) ^ 3 = 1 - 3 * u + u ^ 2 * (3 - u) := by ring
  obtain ⟨p6, h6⟩ := sq_step ((1 - u) ^ 3) 3 (3 - u) h3
  rw [← pow_mul] at h6
  obtain ⟨p12, h12⟩ := sq_step ((1 - u) ^ 6) (2 * 3) p6 h6
  rw [← pow_mul] at h12
  obtain ⟨p24, h24⟩ := sq_step ((1 - u) ^ 12) (2 * (2 * 3)) p12 h12
  rw [← pow_mul] at h24
  refine ⟨-p24, ?_⟩
  rw [h24]; ring

lemma coeff_one_one_sub_X_pow {A : Type*} [CommRing A] :
    ∀ b : ℕ, ((1 - X : A[X]) ^ b).coeff 1 = - (b : A)
  | 0 => by simp [coeff_one]
  | b + 1 => by
    rw [pow_succ, mul_sub, mul_one, coeff_sub, coeff_one_one_sub_X_pow b, coeff_mul_X]
    have h0 : ((1 - X : A[X]) ^ b).coeff 0 = 1 := by
      rw [coeff_zero_eq_eval_zero]; simp
    rw [h0, Nat.cast_add, Nat.cast_one]
    ring

lemma coeff_eq_zero_one_sub_X_pow {A : Type*} [CommRing A] :
    ∀ (b d : ℕ), b < d → ((1 - X : A[X]) ^ b).coeff d = 0
  | 0, d, hd => by rw [pow_zero, coeff_one, if_neg (by omega)]
  | b + 1, d, hd => by
    cases d with
    | zero => omega
    | succ d =>
      rw [pow_succ, mul_sub, mul_one, coeff_sub,
          coeff_eq_zero_one_sub_X_pow b (d + 1) (by omega),
          coeff_mul_X, coeff_eq_zero_one_sub_X_pow b d (by omega), sub_zero]

lemma coeff_Mp1_one_sub_X_pow {A : Type*} [CommRing A] (h5 : (5 : A) = 0)
    {K : ℕ} (hK : 1 ≤ K) (μ : ℕ) :
    ((1 - X : A[X]) ^ μ).coeff (5 ^ K + 1) =
      ((μ / 5 ^ K : ℕ) : A) * ((μ % 5 : ℕ) : A) := by
  set M := 5 ^ K
  have hM_ge : 5 ≤ M := by
    have : 5 ^ 1 ≤ 5 ^ K := Nat.pow_le_pow_right (by omega) hK
    simpa [M] using this
  set a := μ / M
  set b := μ % M
  have hμ : μ = M * a + b := (Nat.div_add_mod μ M).symm
  have hbM : b < M := Nat.mod_lt μ (by omega)
  have h5poly : (5 : A[X]) = 0 := by
    have := congr_arg (C : A →+* A[X]) h5
    simpa [map_ofNat] using this
  have hMpow : (1 - X : A[X]) ^ M = 1 - X ^ M := by
    simpa [M] using sub_pow_five_pow h5poly (1 : A[X]) X K
  rw [hμ, pow_add, pow_mul, hMpow]
  have ha_exp : ∀ m : ℕ, ∃ Q : A[X],
      (1 - X ^ M : A[X]) ^ m = 1 - C (m : A) * X ^ M + X ^ (2 * M) * Q := by
    intro m
    induction m with
    | zero => exact ⟨0, by simp⟩
    | succ m ih =>
      obtain ⟨Q, hQ⟩ := ih
      refine ⟨C (m : A) + Q - X ^ M * Q, ?_⟩
      rw [pow_succ, hQ, Nat.cast_add, Nat.cast_one, map_add, map_one]
      have h2M : (X : A[X]) ^ M * X ^ M = X ^ (2 * M) := by rw [← pow_add, two_mul]
      linear_combination (C (m : A) * X ^ M - X ^ (2 * M) * Q) * h2M
  obtain ⟨Q, hQ⟩ := ha_exp a
  rw [hQ, add_mul, sub_mul, one_mul, coeff_add, coeff_sub]
  have hdeg_b : ((1 - X : A[X]) ^ b).coeff (M + 1) = 0 :=
    coeff_eq_zero_one_sub_X_pow b (M + 1) (by omega)
  have hhigh : (X ^ (2 * M) * Q * (1 - X) ^ b).coeff (M + 1) = 0 := by
    rw [mul_assoc, coeff_X_pow_mul', if_neg (by omega)]
  have hmid : (C (a : A) * X ^ M * (1 - X) ^ b).coeff (M + 1) =
      (a : A) * ((1 - X : A[X]) ^ b).coeff 1 := by
    rw [mul_assoc, coeff_C_mul, coeff_X_pow_mul', if_pos (by omega),
        show M + 1 - M = 1 by omega]
  rw [hdeg_b, hmid, hhigh, coeff_one_one_sub_X_pow]
  have hring : (0 : A) - (a : A) * -(b : A) + 0 = (a : A) * (b : A) := by ring
  rw [hring]
  congr 1
  have h5divM : 5 ∣ M := dvd_pow_self 5 (by omega)
  have hmod_eq : b % 5 = (M * a + b) % 5 := by
    rw [← hμ]
    exact Nat.mod_mod_of_dvd μ h5divM
  have hb_div : b = 5 * (b / 5) + b % 5 := (Nat.div_add_mod b 5).symm
  rw [← hmod_eq]
  conv_lhs => rw [hb_div]
  push_cast
  rw [h5, zero_mul, zero_add]

def Fil {R : Type*} [CommRing R] (y : R) (m : ℕ) (P : R[X]) : Prop :=
  ∀ d < m, ∃ c : R, P.coeff d = y ^ (m - d) * c

lemma fil_one {R : Type*} [CommRing R] (y : R) : Fil y 0 1 :=
  fun _ hd => absurd hd (Nat.not_lt_zero _)

lemma fil_mul_right {R : Type*} [CommRing R] {y : R} {m : ℕ} {P : R[X]}
    (hP : Fil y m P) (Q : R[X]) : Fil y m (P * Q) := by
  intro d hd
  rw [coeff_mul]
  have hterm : ∀ ij : ℕ × ℕ,
      ∃ c : R, ij ∈ Finset.HasAntidiagonal.antidiagonal d →
        P.coeff ij.1 * Q.coeff ij.2 = y ^ (m - d) * c := by
    intro ij
    by_cases hij : ij ∈ Finset.HasAntidiagonal.antidiagonal d
    · have hsum := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
      obtain ⟨c, hc⟩ := hP ij.1 (by omega)
      refine ⟨y ^ ij.2 * c * Q.coeff ij.2, fun _ => ?_⟩
      rw [hc]
      have hexp : m - ij.1 = (m - d) + ij.2 := by omega
      rw [hexp, pow_add]
      ring
    · exact ⟨0, fun h => absurd h hij⟩
  choose fc hfc using hterm
  refine ⟨∑ ij ∈ Finset.HasAntidiagonal.antidiagonal d, fc ij, ?_⟩
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun ij hij => hfc ij hij

lemma fil_mul_step {R : Type*} [CommRing R] {y : R} {m : ℕ} {P Q : R[X]}
    (hP : Fil y m P) {r : R} (hQ0 : Q.coeff 0 = y * r) : Fil y (m + 1) (P * Q) := by
  intro d hd
  rw [coeff_mul]
  have hterm : ∀ ij : ℕ × ℕ,
      ∃ c : R, ij ∈ Finset.HasAntidiagonal.antidiagonal d →
        P.coeff ij.1 * Q.coeff ij.2 = y ^ (m + 1 - d) * c := by
    intro ij
    by_cases hij : ij ∈ Finset.HasAntidiagonal.antidiagonal d
    · have hsum := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
      by_cases hb : ij.2 = 0
      · have ha : ij.1 = d := by omega
        by_cases hdm : d < m
        · obtain ⟨c, hc⟩ := hP d hdm
          refine ⟨c * r, fun _ => ?_⟩
          rw [hb, ha, hQ0, hc]
          have hexp : m + 1 - d = (m - d) + 1 := by omega
          rw [hexp, pow_succ]
          ring
        · have hdeq : d = m := by omega
          refine ⟨P.coeff d * r, fun _ => ?_⟩
          rw [hb, ha, hQ0, hdeq, show m + 1 - m = 1 by omega, pow_one]
          ring
      · obtain ⟨c, hc⟩ := hP ij.1 (by omega)
        refine ⟨y ^ (ij.2 - 1) * c * Q.coeff ij.2, fun _ => ?_⟩
        rw [hc]
        have hexp : m - ij.1 = (m + 1 - d) + (ij.2 - 1) := by omega
        rw [hexp, pow_add]
        ring
    · exact ⟨0, fun h => absurd h hij⟩
  choose fc hfc using hterm
  refine ⟨∑ ij ∈ Finset.HasAntidiagonal.antidiagonal d, fc ij, ?_⟩
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun ij hij => hfc ij hij

end EvalAtOneMinusX

/-! ### Part 6: Putting everything together in `R = F5[X] ⧸ Ideal.span {X ^ (5 ^ K)}` -/

lemma x_dvd_one_sub_xm1_even (i : ℕ) : ∃ g : F5[X], 1 - (X - 1 : F5[X]) ^ (2 * i) = X * g := by
  have heval : (1 - (X - 1 : F5[X]) ^ (2 * i)).IsRoot 0 := by
    rw [IsRoot.def, eval_sub, eval_one, eval_pow, eval_sub, eval_X, eval_one, zero_sub,
        pow_mul, neg_one_sq, one_pow, sub_self]
  obtain ⟨g, hg⟩ := dvd_iff_isRoot.mpr heval
  exact ⟨g, by simpa using hg⟩

lemma x_half_dvd_prod_ic :
    ∀ s : ℕ, ∃ G : F5[X], (∏ j ∈ Finset.Icc 1 s, (1 - (X - 1 : F5[X]) ^ j)) = X ^ (s / 2) * G
  | 0 => ⟨1, by simp⟩
  | s + 1 => by
    obtain ⟨G, hG⟩ := x_half_dvd_prod_ic s
    rw [Finset.prod_Icc_succ_top (by omega : 1 ≤ s + 1), hG]
    rcases Nat.even_or_odd (s + 1) with ⟨i, hi⟩ | ⟨i, hi⟩
    · obtain ⟨g, hg⟩ := x_dvd_one_sub_xm1_even i
      have hdiv : (s + 1) / 2 = s / 2 + 1 := by omega
      have hfac : 1 - (X - 1 : F5[X]) ^ (s + 1) = X * g := by
        rw [show s + 1 = 2 * i by omega, hg]
      rw [hfac, hdiv, pow_succ]
      exact ⟨G * g, by ring⟩
    · have hdiv : (s + 1) / 2 = s / 2 := by omega
      rw [hdiv]
      exact ⟨G * (1 - (X - 1 : F5[X]) ^ (s + 1)), by ring⟩

lemma x_pow_dvd_prod_ic (m s : ℕ) (hs : 2 * m + 2 ≤ s) :
    (∏ j ∈ Finset.Icc 1 s, (1 - (X - 1 : F5[X]) ^ j)).coeff m = 0 := by
  obtain ⟨G, hG⟩ := x_half_dvd_prod_ic s
  rw [hG, coeff_X_pow_mul', if_neg (by omega)]

lemma coeff_eq_of_quot_eq {M m : ℕ} (hm : m < M) {f g : F5[X]}
    (h : Ideal.Quotient.mk (Ideal.span {(X : F5[X]) ^ M}) f =
         Ideal.Quotient.mk (Ideal.span {(X : F5[X]) ^ M}) g) :
    f.coeff m = g.coeff m := by
  have hmem : f - g ∈ Ideal.span {(X : F5[X]) ^ M} := Ideal.Quotient.eq.mp h
  obtain ⟨p, hp⟩ := Ideal.mem_span_singleton.mp hmem
  have hdiff : (f - g).coeff m = 0 := by
    rw [hp, coeff_X_pow_mul', if_neg (by omega)]
  rw [coeff_sub, sub_eq_zero] at hdiff
  exact hdiff

lemma five_pow_gt (n : ℕ) : 5 * n + 4 < 5 ^ (n + 2) ∧ 10 * n + 10 ≤ 6 * 5 ^ (n + 2) := by
  induction n with
  | zero => decide
  | succ n ih =>
    rw [show n + 1 + 2 = (n + 2) + 1 by omega, pow_succ]
    omega

lemma main_proof (n : ℕ) :
    OMA.S_oeis_a035378.a (5 * n + 3) ≡ 0 [ZMOD 5] ∧
      OMA.S_oeis_a035378.a (5 * n + 4) ≡ 0 [ZMOD 5] ∧
      OMA.S_oeis_a035378.a (5 * n + 2) - 2 * OMA.S_oeis_a035378.a (5 * n + 1) ≡ 0 [ZMOD 5] := by
  set K := n + 2
  set M := 5 ^ K
  set D := 2 * M
  set E := 6 * M
  have hK1 : 1 ≤ K := by omega
  have hM25 : 25 ≤ M := by
    have : 5 ^ 2 ≤ 5 ^ (n + 2) := Nat.pow_le_pow_right (by omega) (by omega)
    simpa [M, K] using this
  obtain ⟨hm_lt_M, hlen_le_E⟩ := five_pow_gt n
  change 5 * n + 4 < M at hm_lt_M
  change 10 * n + 10 ≤ E at hlen_le_E
  set I : Ideal F5[X] := Ideal.span {(X : F5[X]) ^ M}
  let π : F5[X] →+* (F5[X] ⧸ I) := Ideal.Quotient.mk I
  set y : F5[X] ⧸ I := π X
  set q : F5[X] ⧸ I := y - 1
  have h5R : (5 : F5[X] ⧸ I) = 0 := by
    have := congr_arg (π.comp C) five_eq_zero_F5
    simpa [map_ofNat] using this
  have hyM : y ^ M = 0 := by
    dsimp [y, π]
    rw [← map_pow]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl)
  have hqM : q ^ M = -1 := by
    dsimp [q]
    have h := sub_pow_five_pow h5R y 1 K
    change (y - 1) ^ M = y ^ M - 1 ^ M at h
    rw [h, hyM, one_pow, zero_sub]
  have hqD : q ^ D = 1 := by
    dsimp [D]
    rw [mul_comm, pow_mul, hqM]
    norm_num
  -- Apply `cross_mul_poly_id` in `(F5[X] ⧸ I)[X]`
  have hcross := cross_mul_poly_id (R := F5[X] ⧸ I) (D := D) (by omega) hqD
  have h3D : 3 * D = E := by dsimp [D, E]; ring
  have h6D : 6 * D = 2 * E := by dsimp [D, E]; ring
  have h12D : 12 * D = 24 * M := by dsimp [D]; ring
  rw [h3D, h6D, h12D] at hcross
  -- Substitute `X ↦ 1 - X` via `sub1mX`
  let sub1mX : (F5[X] ⧸ I)[X] →+* (F5[X] ⧸ I)[X] :=
    eval₂RingHom (C : (F5[X] ⧸ I) →+* (F5[X] ⧸ I)[X]) (1 - (X : (F5[X] ⧸ I)[X]))
  have hsub_X : sub1mX X = 1 - X := by simp [sub1mX]
  have hsub_C : ∀ c : F5[X] ⧸ I, sub1mX (C c) = C c := fun c => by simp [sub1mX]
  have hsub_id := congr_arg (fun P => (sub1mX P).coeff (M + 1)) hcross
  -- Evaluate LHS `.coeff (M + 1)`
  set A_sub : (F5[X] ⧸ I)[X] :=
    sub1mX (∑ s ∈ Finset.range E, X ^ (2 * s + 1) * poch q (X ^ 2) (s + 1))
  have hlhs_coeff : (sub1mX ((1 - X ^ (24 * M)) *
      (∑ s ∈ Finset.range E, X ^ (2 * s + 1) * poch q (X ^ 2) (s + 1)))).coeff (M + 1) =
      (3 : F5[X] ⧸ I) * ∑ s ∈ Finset.range E, ∏ j ∈ Finset.Icc 1 s, (1 - q ^ j) := by
    rw [map_mul]
    change (sub1mX (1 - X ^ (24 * M)) * A_sub).coeff (M + 1) = _
    rw [map_sub, map_one, map_pow, hsub_X]
    have h5poly : (5 : (F5[X] ⧸ I)[X]) = 0 := by
      have := congr_arg (C : (F5[X] ⧸ I) →+* (F5[X] ⧸ I)[X]) h5R
      simpa [map_ofNat] using this
    have h1mXM : (1 - X : (F5[X] ⧸ I)[X]) ^ M = 1 - X ^ M := by
      simpa [M] using sub_pow_five_pow h5poly (1 : (F5[X] ⧸ I)[X]) X K
    rw [show 24 * M = M * 24 by ring, pow_mul, h1mXM]
    obtain ⟨p24, hp24⟩ := one_sub_pow_24 ((X : (F5[X] ⧸ I)[X]) ^ M)
    have h24R : (24 : (F5[X] ⧸ I)[X]) = C 4 := by
      have h24q : (24 : F5[X] ⧸ I) = 4 := by
        have := congr_arg (π.comp C) twentyfour_eq_four_F5
        simpa [map_ofNat] using this
      have := congr_arg (C : (F5[X] ⧸ I) →+* (F5[X] ⧸ I)[X]) h24q
      simpa [map_ofNat] using this
    rw [hp24, h24R, ← pow_mul, show M * 2 = 2 * M by ring, add_mul, coeff_add]
    have htail0 : (X ^ (2 * M) * p24 * A_sub).coeff (M + 1) = 0 := by
      rw [mul_assoc, coeff_X_pow_mul', if_neg (by omega)]
    have hlead : (C (4 : F5[X] ⧸ I) * X ^ M * A_sub).coeff (M + 1) = 4 * A_sub.coeff 1 := by
      rw [mul_assoc, coeff_C_mul, coeff_X_pow_mul', if_pos (by omega),
          show M + 1 - M = 1 by omega]
    rw [htail0, add_zero, hlead]
    -- Compute `A_sub.coeff 1`
    have hA1 : A_sub.coeff 1 =
        (2 : F5[X] ⧸ I) * ∑ s ∈ Finset.range E, ∏ j ∈ Finset.Icc 1 s, (1 - q ^ j) := by
      dsimp [A_sub]
      rw [map_sum, finsetSum_coeff, Finset.mul_sum]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [poch_succ_left, map_mul, map_mul, map_sub, map_one, map_pow, map_pow, hsub_X]
      have hfac0 : (1 - (1 - X : (F5[X] ⧸ I)[X]) ^ 2) = X * (2 - X) := by ring
      set rest : (F5[X] ⧸ I)[X] :=
        (1 - X) ^ (2 * s + 1) * (2 - X) * sub1mX (poch q (C q * X ^ 2) s)
      have harr : (1 - X) ^ (2 * s + 1) * ((1 - (1 - X) ^ 2) * sub1mX (poch q (C q * X ^ 2) s)) =
          X * rest := by rw [hfac0]; dsimp [rest]; ring
      rw [harr, coeff_X_mul, ← constantCoeff_apply]
      dsimp [rest]
      rw [map_mul, map_mul, map_pow]
      have hc1 : constantCoeff (1 - X : (F5[X] ⧸ I)[X]) = 1 := by simp
      have hc2 : constantCoeff (2 - X : (F5[X] ⧸ I)[X]) = 2 := by simp
      rw [hc1, hc2, one_pow, one_mul]
      congr 1
      unfold poch
      rw [map_prod, map_prod]
      have hbij : (∏ j ∈ Finset.range s,
          constantCoeff (sub1mX (1 - C (q ^ j) * (C q * X ^ 2)))) =
          ∏ j ∈ Finset.Icc 1 s, (1 - q ^ j) := by
        have hIcc : Finset.Icc 1 s = (Finset.range s).image (fun j => j + 1) := by
          ext x
          simp only [Finset.mem_Icc, Finset.mem_image, Finset.mem_range]
          constructor
          · intro hx; exact ⟨x - 1, by omega, by omega⟩
          · rintro ⟨j, hj, rfl⟩; omega
        rw [hIcc, Finset.prod_image (fun a _ b _ h => by omega)]
        refine Finset.prod_congr rfl fun j _ => ?_
        have hc_step : ∀ a : F5[X] ⧸ I, constantCoeff (C a) = a := fun a => by simp
        have hc_qj : constantCoeff (C (q ^ j)) = q ^ j := hc_step (q ^ j)
        have hc_q : constantCoeff (C q) = q := hc_step q
        rw [map_sub, map_one, map_mul, map_mul, hsub_C, hsub_C, map_pow sub1mX, hsub_X,
            map_sub constantCoeff, map_one constantCoeff, map_mul constantCoeff,
            map_mul constantCoeff, map_pow constantCoeff,
            hc_qj, hc_q, hc1, one_pow, mul_one, pow_succ]
      exact hbij
    rw [hA1, ← mul_assoc]
    have h42 : (4 : F5[X] ⧸ I) * 2 = 3 := by
      have := congr_arg (π.comp C) four_mul_two_F5
      simpa [map_ofNat] using this
    rw [h42]
  -- Evaluate RHS `.coeff (M + 1)` using `Fil y (3 * M)` on `sub1mX (poch q (X ^ 2) E)`
  set P_poch : (F5[X] ⧸ I)[X] := sub1mX (poch q (X ^ 2) E)
  have hP_fil : Fil y (3 * M) P_poch := by
    dsimp [P_poch]
    unfold poch
    rw [map_prod]
    have hpair : ∀ k : ℕ, ∏ j ∈ Finset.range (2 * k),
        sub1mX (1 - C (q ^ j) * X ^ 2) =
        ∏ i ∈ Finset.range k,
          (sub1mX (1 - C (q ^ (2 * i)) * X ^ 2) *
           sub1mX (1 - C (q ^ (2 * i + 1)) * X ^ 2)) := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        rw [show 2 * (k + 1) = 2 * k + 1 + 1 by omega,
            Finset.prod_range_succ, Finset.prod_range_succ, ih, Finset.prod_range_succ]
        ring
    rw [show E = 2 * (3 * M) by dsimp [E]; ring, hpair (3 * M)]
    suffices ∀ k : ℕ, Fil y k (∏ i ∈ Finset.range k,
        (sub1mX (1 - C (q ^ (2 * i)) * X ^ 2) *
         sub1mX (1 - C (q ^ (2 * i + 1)) * X ^ 2))) from this (3 * M)
    intro k
    induction k with
    | zero => simpa using fil_one y
    | succ k ih =>
      rw [Finset.prod_range_succ, ← mul_assoc]
      obtain ⟨g, hg⟩ := x_dvd_one_sub_xm1_even k
      refine fil_mul_right (fil_mul_step ih (r := π g) ?_) _
      have hc_all : ∀ a : F5[X] ⧸ I, constantCoeff (C a) = a := fun a => by simp
      have hc_step : constantCoeff (C (q ^ (2 * k))) = q ^ (2 * k) := hc_all (q ^ (2 * k))
      have hx_step : constantCoeff (X : (F5[X] ⧸ I)[X]) = 0 := by simp
      rw [← constantCoeff_apply, map_sub sub1mX, map_one sub1mX, map_mul sub1mX,
          hsub_C, map_pow sub1mX, hsub_X,
          map_sub constantCoeff, map_one constantCoeff, map_mul constantCoeff,
          map_pow constantCoeff, map_sub constantCoeff, map_one constantCoeff,
          hc_step, hx_step, sub_zero, one_pow, mul_one]
      have hmap := congr_arg π hg
      simpa only [q, y, map_sub, map_one, map_pow, map_mul] using hmap
  have hW_vanish : ∀ d ≤ M + 1,
      (sub1mX (X ^ (2 * E) * poch q (X ^ 2) E)).coeff d = 0 := by
    intro d hd
    rw [map_mul, coeff_mul]
    refine Finset.sum_eq_zero fun ij hij => ?_
    have hsum := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
    obtain ⟨c, hc⟩ := hP_fil ij.2 (by omega)
    have hy0 : y ^ (3 * M - ij.2) = 0 := by
      have hexp : 3 * M - ij.2 = M + (3 * M - ij.2 - M) := by omega
      rw [hexp, pow_add, hyM, zero_mul]
    change (sub1mX (X ^ (2 * E))).coeff ij.1 * P_poch.coeff ij.2 = 0
    rw [hc, hy0, zero_mul, mul_zero]
  set B_sub : (F5[X] ⧸ I)[X] := sub1mX (∑ s ∈ Finset.range (2 * D), thetaTerm q s)
  have hrhs_coeff : (sub1mX ((1 - X ^ (2 * E) * poch q (X ^ 2) E) *
      (∑ s ∈ Finset.range (2 * D), thetaTerm q s))).coeff (M + 1) = B_sub.coeff (M + 1) := by
    rw [map_mul]
    change (sub1mX (1 - X ^ (2 * E) * poch q (X ^ 2) E) * B_sub).coeff (M + 1) = B_sub.coeff (M + 1)
    rw [map_sub, map_one, sub_mul, one_mul, coeff_sub]
    have h0 : (sub1mX (X ^ (2 * E) * poch q (X ^ 2) E) * B_sub).coeff (M + 1) = 0 := by
      rw [coeff_mul]
      refine Finset.sum_eq_zero fun ij hij => ?_
      have hsum := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
      rw [hW_vanish ij.1 (by omega), zero_mul]
    rw [h0, sub_zero]
  -- Lift `B_sub.coeff (M + 1)` to an explicit `Good` polynomial in `F5[X]`
  set termLift : ℕ → F5[X] := fun s =>
    C ((-1 : F5) ^ s * (((6 * s + 1) / M : ℕ) : F5) * (((6 * s + 1) % 5 : ℕ) : F5)) *
      (X - 1) ^ (s * (3 * s + 1) / 2) +
    C ((-1 : F5) ^ (s + 1) * (((6 * s + 5) / M : ℕ) : F5) * (((6 * s + 5) % 5 : ℕ) : F5)) *
      (X - 1) ^ ((s + 1) * (3 * s + 2) / 2)
  set RHS_poly : F5[X] := ∑ s ∈ Finset.range (2 * D), termLift s
  have hB_eq_π : B_sub.coeff (M + 1) = π RHS_poly := by
    dsimp [B_sub, RHS_poly]
    rw [map_sum, map_sum, finsetSum_coeff]
    refine Finset.sum_congr rfl fun s _ => ?_
    unfold thetaTerm
    dsimp [termLift]
    rw [map_add sub1mX, coeff_add,
        map_mul sub1mX, map_mul sub1mX, map_pow sub1mX, map_pow sub1mX,
        hsub_C, hsub_C, hsub_X, coeff_C_mul, coeff_C_mul,
        coeff_Mp1_one_sub_X_pow h5R hK1 (6 * s + 1),
        coeff_Mp1_one_sub_X_pow h5R hK1 (6 * s + 5)]
    simp only [M, q, y, map_add, map_mul, map_pow, map_neg, map_one, map_sub, map_natCast]
    ring
  have hRHS_good : Good RHS_poly := by
    refine good_sum _ _ fun s _ => ?_
    dsimp [termLift]
    refine good_add ?_ ?_
    · rcases exp1_mod5 s with h0 | he
      · rw [h0, Nat.cast_zero, mul_zero, map_zero, zero_mul]; exact good_zero
      · exact good_C_mul _ (good_Xm1_pow he)
    · rcases exp2_mod5 s with h0 | he
      · rw [h0, Nat.cast_zero, mul_zero, map_zero, zero_mul]; exact good_zero
      · exact good_C_mul _ (good_Xm1_pow he)
  -- Connect `LHS_poly` to `C 2 * RHS_poly` via `π`
  set LHS_poly : F5[X] := ∑ s ∈ Finset.range E, ∏ j ∈ Finset.Icc 1 s, (1 - (X - 1) ^ j)
  have hLHS_π : π LHS_poly = ∑ s ∈ Finset.range E, ∏ j ∈ Finset.Icc 1 s, (1 - q ^ j) := by
    dsimp [LHS_poly, q, y]
    simp only [map_sum, map_prod, map_sub, map_one, map_pow]
  rw [hlhs_coeff, hrhs_coeff, hB_eq_π, ← hLHS_π] at hsub_id
  have h23R : (2 : F5[X] ⧸ I) * 3 = 1 := by
    have := congr_arg (π.comp C) two_mul_three_F5
    simpa [map_ofNat] using this
  have hπ_eq : π LHS_poly = π (C 2 * RHS_poly) := by
    have hmul := congr_arg (fun z => (2 : F5[X] ⧸ I) * z) hsub_id
    rw [← mul_assoc, h23R, one_mul] at hmul
    have hC2 : π (C 2) = (2 : F5[X] ⧸ I) := by simp [map_ofNat]
    rw [map_mul, hC2]
    exact hmul
  have hLHS_good_at_n : LHS_poly.coeff (5 * n + 3) = 0 ∧
      LHS_poly.coeff (5 * n + 4) = 0 ∧
      LHS_poly.coeff (5 * n + 2) = 2 * LHS_poly.coeff (5 * n + 1) := by
    obtain ⟨g3, g4, g2⟩ := good_C_mul 2 hRHS_good n
    have c3 := coeff_eq_of_quot_eq (M := M) (m := 5 * n + 3) (by omega) hπ_eq
    have c4 := coeff_eq_of_quot_eq (M := M) (m := 5 * n + 4) (by omega) hπ_eq
    have c2 := coeff_eq_of_quot_eq (M := M) (m := 5 * n + 2) (by omega) hπ_eq
    have c1 := coeff_eq_of_quot_eq (M := M) (m := 5 * n + 1) (by omega) hπ_eq
    rw [c3, c4, c2, c1]
    exact ⟨g3, g4, g2⟩
  -- Relate `(OMA.S_oeis_a035378.a m : F5)` to `LHS_poly.coeff m` for `m ≤ 5 * n + 4`
  have ha_eq : ∀ m ≤ 5 * n + 4, (OMA.S_oeis_a035378.a m : F5) = LHS_poly.coeff m := by
    intro m hm
    unfold OMA.S_oeis_a035378.a
    have hcast_coeff : ∀ P : ℤ[X], ((P.coeff m : ℤ) : F5) =
        (P.map (Int.castRingHom F5)).coeff m := by
      intro P; rw [coeff_map]; rfl
    rw [hcast_coeff]
    simp only [Polynomial.map_sum, Polynomial.map_prod, Polynomial.map_sub,
      Polynomial.map_one, Polynomial.map_pow, Polynomial.map_X]
    dsimp [LHS_poly]
    have hleE : 2 * m + 2 ≤ E := by omega
    rw [← Finset.sum_range_add_sum_Ico _ hleE, coeff_add]
    have htail : (∑ x ∈ Finset.Ico (2 * m + 2) E,
        ∏ j ∈ Finset.Icc 1 x, (1 - (X - 1 : F5[X]) ^ j)).coeff m = 0 := by
      rw [finsetSum_coeff]
      exact Finset.sum_eq_zero fun x hx => x_pow_dvd_prod_ic m x (Finset.mem_Ico.mp hx).1
    rw [htail, add_zero]
  obtain ⟨hL3, hL4, hL2⟩ := hLHS_good_at_n
  refine ⟨(ZMod.intCast_eq_intCast_iff _ _ 5).mp ?_,
          (ZMod.intCast_eq_intCast_iff _ _ 5).mp ?_,
          (ZMod.intCast_eq_intCast_iff _ _ 5).mp ?_⟩
  · rw [ha_eq (5 * n + 3) (by omega), Int.cast_zero, hL3]
  · rw [ha_eq (5 * n + 4) (by omega), Int.cast_zero, hL4]
  · push_cast
    rw [ha_eq (5 * n + 2) (by omega), ha_eq (5 * n + 1) (by omega), hL2, sub_self]

end ProofA035378

theorem OMA.solution : type_of% @OMA.S_oeis_a035378.main :=
  ProofA035378.main_proof
