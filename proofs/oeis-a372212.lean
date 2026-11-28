import OMAStatements.S_oeis_a372212

/- Copyright 2026 The Formal Conjectures Authors and Wentao Li.
Adapted under the Apache License 2.0. See ATTRIBUTION_Li.txt and LICENSE_Li_Apache2.txt. -/

section

namespace OeisA372211

open PowerSeries

noncomputable def zpowSeries (F : PowerSeries ℤ) (k : ℤ) : PowerSeries ℤ :=
  if 0 ≤ k then F ^ k.toNat else invOfUnit F 1 ^ k.natAbs

noncomputable def f (a b : ℕ) : PowerSeries ℤ :=
  (1 - X ^ (a + b)) ^ (a + b) * invOfUnit (1 - X ^ a) 1 ^ a * invOfUnit (1 - X ^ b) 1 ^ b

noncomputable def u (a b r : ℕ) (s : ℤ) (n : ℕ) : ℤ := coeff (r * n) (zpowSeries (f a b) (s * n))

noncomputable def fm (a b : ℕ) : PowerSeries ℤ :=
  (1 - X ^ (a + b)) ^ (a + b) * invOfUnit (1 + X ^ a) 1 ^ a * invOfUnit (1 + X ^ b) 1 ^ b

noncomputable def um (a b r : ℕ) (s : ℤ) (n : ℕ) : ℤ :=
  coeff (r * n) (zpowSeries (fm a b) (s * n))

noncomputable def f372211 : PowerSeries ℤ :=
  (1 - X ^ 5) ^ 5 * invOfUnit (1 - X ^ 2) 1 ^ 2 * invOfUnit (1 - X ^ 3) 1 ^ 3

noncomputable def A372211 (n : ℕ) : ℤ := coeff n (f372211 ^ n)

noncomputable def u372211 (r : ℕ) (s : ℤ) (n : ℕ) : ℤ :=
  coeff (r * n) (zpowSeries f372211 (s * n))

noncomputable def f372212 : PowerSeries ℤ :=
  (1 - X ^ 7) ^ 7 * invOfUnit (1 - X ^ 2) 1 ^ 2 * invOfUnit (1 - X ^ 5) 1 ^ 5

noncomputable def A372212 (n : ℕ) : ℤ := coeff n (f372212 ^ n)

noncomputable def u372212 (r : ℕ) (s : ℤ) (n : ℕ) : ℤ :=
  coeff (r * n) (zpowSeries f372212 (s * n))

noncomputable def f372213 : PowerSeries ℤ :=
  (1 - X ^ 7) ^ 7 * invOfUnit (1 - X ^ 3) 1 ^ 3 * invOfUnit (1 - X ^ 4) 1 ^ 4

noncomputable def A372213 (n : ℕ) : ℤ := coeff n (f372213 ^ n)

noncomputable def u372213 (r : ℕ) (s : ℤ) (n : ℕ) : ℤ :=
  coeff (r * n) (zpowSeries f372213 (s * n))

noncomputable def G3 : PowerSeries ℤ :=
  (1 + X + X ^ 2 + X ^ 3) ^ 4 * invOfUnit (1 + X + X ^ 2) 1 ^ 3

noncomputable def A351859 (n : ℕ) : ℤ :=
  coeff n ((1 + X + X ^ 2 + X ^ 3) ^ (4 * n) * invOfUnit (1 + X + X ^ 2) 1 ^ (3 * n))

noncomputable def a351859 (r : ℕ) (s : ℤ) (n : ℕ) : ℤ := coeff (r * n) (zpowSeries G3 (s * n))

end OeisA372211

namespace OeisA372211

open PowerSeries Finset

section

section Theta

variable {R : Type*} [CommRing R]

noncomputable def theta (A : R⟦X⟧) : R⟦X⟧ := mk fun n => (n : R) * coeff n A

@[simp] theorem coeff_theta (A : R⟦X⟧) (n : ℕ) : coeff n (theta A) = n * coeff n A := by
  simp [theta]

theorem theta_add (A B : R⟦X⟧) : theta (A + B) = theta A + theta B := by
  ext n; simp [mul_add]

theorem theta_sub (A B : R⟦X⟧) : theta (A - B) = theta A - theta B := by
  ext n; simp [mul_sub]

theorem theta_smul (c : R) (A : R⟦X⟧) : theta (c • A) = c • theta A := by
  ext n; simp; ring

theorem theta_sum {ι : Type*} (s : Finset ι) (f : ι → R⟦X⟧) :
    theta (∑ i ∈ s, f i) = ∑ i ∈ s, theta (f i) := by
  ext n; simp [Finset.mul_sum]

theorem theta_C (c : R) : theta (C c) = 0 := by
  ext n; simp only [coeff_theta, coeff_C, map_zero]; split_ifs with h <;> simp [h]

theorem theta_one : theta (1 : R⟦X⟧) = 0 := by
  simpa using theta_C (R := R) 1

theorem theta_X : theta (X : R⟦X⟧) = X := by
  ext n; simp only [coeff_theta, coeff_X]; split_ifs with h <;> simp [h]

theorem theta_mul (A B : R⟦X⟧) : theta (A * B) = theta A * B + A * theta B := by
  ext n
  simp only [coeff_theta, map_add, coeff_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
  rw [← hx]; push_cast; ring

theorem theta_pow (A : R⟦X⟧) (n : ℕ) :
    theta (A ^ (n + 1)) = ((n + 1 : ℕ) : R⟦X⟧) * A ^ n * theta A := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, theta_mul, ih]; push_cast; ring

theorem X_dvd_theta (A : R⟦X⟧) : X ∣ theta A := by
  rw [← pow_one X, X_pow_dvd_iff]
  intro m hm
  obtain rfl : m = 0 := by omega
  simp

theorem coeff_mul_eq_of_X_pow_dvd {n : ℕ} (A : R⟦X⟧) {B B' : R⟦X⟧}
    (h : X ^ (n + 1) ∣ B - B') : coeff n (A * B) = coeff n (A * B') := by
  have h2 : X ^ (n + 1) ∣ A * B - A * B' := by
    rw [← mul_sub]; exact Dvd.dvd.mul_left h A
  have := (X_pow_dvd_iff.mp h2) n (by omega)
  rwa [map_sub, sub_eq_zero] at this

theorem coeff_eq_zero_of_X_pow_dvd {n k : ℕ} {A : R⟦X⟧} (h : X ^ k ∣ A) (hn : n < k) :
    coeff n A = 0 :=
  X_pow_dvd_iff.mp h n hn

theorem X_pow_succ_dvd_of {n : ℕ} {A : R⟦X⟧} (h : X ^ n ∣ A) (h0 : coeff n A = 0) :
    X ^ (n + 1) ∣ A := by
  rw [X_pow_dvd_iff] at h ⊢
  intro m hm
  rcases Nat.lt_succ_iff_lt_or_eq.mp hm with hm | rfl
  · exact h m hm
  · exact h0

end Theta

theorem X_pow_dvd_of_theta {D K Rr : ℚ⟦X⟧} {T : ℕ} (hD : theta D = K * D + Rr) (hK : X ∣ K)
    (hR : X ^ (T + 1) ∣ Rr) (h0 : constantCoeff D = 0) : X ^ (T + 1) ∣ D := by
  suffices ∀ n, n ≤ T + 1 → X ^ n ∣ D from this _ le_rfl
  intro n
  induction n with
  | zero => intro _; simp
  | succ n ih =>
    intro hn
    have IH := ih (by omega)
    refine X_pow_succ_dvd_of IH ?_
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · simpa using h0
    · have h1 : X ^ (n + 1) ∣ K * D := by
        rw [pow_succ']; exact mul_dvd_mul hK IH
      have h2 : X ^ (n + 1) ∣ Rr := (pow_dvd_pow X hn).trans hR
      have h3 : X ^ (n + 1) ∣ theta D := hD ▸ dvd_add h1 h2
      have h4 := coeff_eq_zero_of_X_pow_dvd h3 (Nat.lt_succ_self n)
      rw [coeff_theta] at h4
      rcases mul_eq_zero.mp h4 with h | h
      · exact absurd h (by exact_mod_cast hpos.ne')
      · exact h

end

section

section Frob

variable (p : ℕ) (hp : p ≠ 0)

theorem theta_expand {R : Type*} [CommRing R] (A : R⟦X⟧) :
    theta (expand p hp A) = (p : R⟦X⟧) * expand p hp (theta A) := by
  ext n
  rw [← map_natCast (C (R := R)), coeff_C_mul]
  simp only [coeff_theta, coeff_expand]
  split_ifs with h
  · obtain ⟨m, rfl⟩ := h
    rw [Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hp)]
    push_cast; ring
  · simp

theorem coeff_p_mul_expand_mul {R : Type*} [CommRing R] (A B : R⟦X⟧) (N : ℕ) :
    coeff (p * N) (expand p hp A * B) =
      ∑ x ∈ antidiagonal N, coeff x.1 A * coeff (p * x.2) B := by
  rw [coeff_mul]
  let e : ℕ × ℕ ↪ ℕ × ℕ := ⟨fun x => (p * x.1, p * x.2), fun x y h => by
    simp only [Prod.mk.injEq] at h
    exact Prod.ext (Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hp) h.1)
      (Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hp) h.2)⟩
  have hsub : (antidiagonal N).map e ⊆ antidiagonal (p * N) := by
    intro x hx
    simp only [Finset.mem_map, Finset.HasAntidiagonal.mem_antidiagonal] at hx ⊢
    obtain ⟨y, hy, rfl⟩ := hx
    show p * y.1 + p * y.2 = p * N
    rw [← mul_add, hy]
  rw [← Finset.sum_subset hsub, Finset.sum_map]
  · refine Finset.sum_congr rfl fun x _ => ?_
    show coeff (p * x.1) (expand p hp A) * coeff (p * x.2) B = _
    rw [coeff_expand_mul]
  · intro x hx hnot
    have hx' := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
    have hnd : ¬ p ∣ x.1 := by
      rintro ⟨a, ha⟩
      apply hnot
      rw [Finset.mem_map]
      have hb : x.2 = p * (N - a) := by
        rw [Nat.mul_sub]
        have : p * a ≤ p * N := by rw [← ha]; omega
        omega
      refine ⟨(a, N - a), ?_, ?_⟩
      · rw [Finset.HasAntidiagonal.mem_antidiagonal]
        have : p * a ≤ p * N := by rw [← ha]; omega
        have := Nat.le_of_mul_le_mul_left this (Nat.pos_of_ne_zero hp)
        simp only; omega
      · exact Prod.ext ha.symm hb.symm
    rw [coeff_expand_of_not_dvd p hp _ hnd, zero_mul]

def HasLD (u : ℚ⟦X⟧ˣ) (L : ℚ⟦X⟧) : Prop := theta (u : ℚ⟦X⟧) = L * u

theorem HasLD.mul {u v : ℚ⟦X⟧ˣ} {L M : ℚ⟦X⟧} (hu : HasLD u L) (hv : HasLD v M) :
    HasLD (u * v) (L + M) := by
  unfold HasLD at *
  rw [Units.val_mul, theta_mul, hu, hv]; ring

theorem HasLD.inv {u : ℚ⟦X⟧ˣ} {L : ℚ⟦X⟧} (hu : HasLD u L) : HasLD u⁻¹ (-L) := by
  unfold HasLD at *
  set i : ℚ⟦X⟧ := ↑u⁻¹ with hi_def
  have hu1 : (u : ℚ⟦X⟧) * i = 1 := Units.mul_inv u
  have hi : i * (u : ℚ⟦X⟧) = 1 := Units.inv_mul u
  have h1 : theta ((u : ℚ⟦X⟧) * i) = 0 := by rw [hu1, theta_one]
  rw [theta_mul, hu] at h1
  linear_combination i * h1 - theta i * hi - L * i * hu1

theorem HasLD.pow {u : ℚ⟦X⟧ˣ} {L : ℚ⟦X⟧} (hu : HasLD u L) (n : ℕ) :
    HasLD (u ^ n) ((n : ℚ⟦X⟧) * L) := by
  induction n with
  | zero =>
    unfold HasLD; simp [theta_one]
  | succ n ih =>
    have := ih.mul hu
    rw [← pow_succ] at this
    unfold HasLD at *
    rw [this]; push_cast; ring

theorem HasLD.zpow {u : ℚ⟦X⟧ˣ} {L : ℚ⟦X⟧} (hu : HasLD u L) (k : ℤ) :
    HasLD (u ^ k) ((k : ℚ⟦X⟧) * L) := by
  rcases k with n | n
  · simpa using hu.pow n
  · rw [zpow_negSucc]
    have := (hu.pow (n + 1)).inv
    unfold HasLD at *
    rw [this, Int.cast_negSucc]; push_cast; ring

theorem HasLD.congr {u : ℚ⟦X⟧ˣ} {L M : ℚ⟦X⟧} (hu : HasLD u L) (h : L = M) : HasLD u M :=
  h ▸ hu

noncomputable def exU : ℚ⟦X⟧ˣ →* ℚ⟦X⟧ˣ := Units.map (expand p hp).toRingHom.toMonoidHom

@[simp] theorem val_exU (u : ℚ⟦X⟧ˣ) : ((exU p hp u : ℚ⟦X⟧ˣ) : ℚ⟦X⟧) = expand p hp u := rfl

theorem HasLD.expand {u : ℚ⟦X⟧ˣ} {L : ℚ⟦X⟧} (hu : HasLD u L) :
    HasLD (exU p hp u) ((p : ℚ⟦X⟧) * PowerSeries.expand p hp L) := by
  unfold HasLD at *
  rw [val_exU, theta_expand, hu, map_mul]; ring

noncomputable def Vof (L : ℚ⟦X⟧) : ℚ⟦X⟧ := mk fun n => if p ∣ n then 0 else coeff n L / n

theorem coeff_Vof (L : ℚ⟦X⟧) (n : ℕ) :
    coeff n (Vof p L) = if p ∣ n then 0 else coeff n L / n := by
  simp [Vof]

theorem theta_Vof (L : ℚ⟦X⟧) (hper : ∀ m, coeff (p * m) L = coeff m L) :
    theta (Vof p L) = L - expand p hp L := by
  ext n
  rw [coeff_theta, coeff_Vof, map_sub, coeff_expand]
  split_ifs with h
  · obtain ⟨m, rfl⟩ := h
    rw [Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hp), hper]; ring
  · have hn : (n : ℚ) ≠ 0 := by
      have : n ≠ 0 := by rintro rfl; exact h (dvd_zero p)
      exact_mod_cast this
    field_simp; ring

theorem Vof_add (L M : ℚ⟦X⟧) : Vof p (L + M) = Vof p L + Vof p M := by
  ext n; simp only [coeff_Vof, map_add]; split_ifs <;> ring

theorem Vof_C_mul (a : ℚ) (L : ℚ⟦X⟧) : Vof p (C a * L) = C a * Vof p L := by
  ext n; simp only [coeff_Vof, coeff_C_mul]; split_ifs <;> ring

theorem X_dvd_Vof (L : ℚ⟦X⟧) : X ∣ Vof p L := by
  rw [← pow_one X, X_pow_dvd_iff]
  intro m hm
  obtain rfl : m = 0 := by omega
  simp [coeff_Vof]

theorem coeff_p_mul_Vof (L : ℚ⟦X⟧) (j : ℕ) : coeff (p * j) (Vof p L) = 0 := by
  simp [coeff_Vof]

theorem coeff_p_mul_expand_mul_Vof (A L : ℚ⟦X⟧) (j : ℕ) :
    coeff (p * j) (expand p hp A * Vof p L) = 0 := by
  rw [coeff_p_mul_expand_mul]
  exact Finset.sum_eq_zero fun x _ => by rw [coeff_p_mul_Vof, mul_zero]

end Frob

noncomputable def expTrunc (c : ℚ) (Z : ℚ⟦X⟧) (T : ℕ) : ℚ⟦X⟧ :=
  ∑ t ∈ range (T + 1), C (c ^ t / t.factorial) * Z ^ t

theorem theta_C_mul (a : ℚ) (A : ℚ⟦X⟧) : theta (C a * A) = C a * theta A := by
  ext n; simp [coeff_C_mul]; ring

theorem theta_expTrunc (c : ℚ) (Z : ℚ⟦X⟧) (T : ℕ) :
    theta (expTrunc c Z T) =
      C c * theta Z * expTrunc c Z T - C (c ^ (T + 1) / T.factorial) * (theta Z * Z ^ T) := by
  induction T with
  | zero =>
    simp [expTrunc, theta_one]
  | succ T ih =>
    have hsplit : expTrunc c Z (T + 1) =
        expTrunc c Z T + C (c ^ (T + 1) / (T + 1).factorial) * Z ^ (T + 1) := by
      simp only [expTrunc]; rw [Finset.sum_range_succ _ (T + 1)]
    rw [hsplit, theta_add, ih, theta_C_mul, theta_pow]
    have e1 : C (c ^ (T + 1) / (T + 1).factorial) * ((T + 1 : ℕ) : ℚ⟦X⟧) =
        C (c ^ (T + 1) / T.factorial) := by
      rw [← map_natCast (C (R := ℚ)), ← map_mul]
      congr 1
      rw [Nat.factorial_succ]; push_cast
      field_simp
    have e2 : C c * C (c ^ (T + 1) / (T + 1).factorial) = C (c ^ (T + 1 + 1) / (T + 1).factorial) := by
      rw [← map_mul]; congr 1; ring
    linear_combination (Z ^ T * theta Z) * e1 - (theta Z * Z ^ (T + 1)) * e2

theorem constantCoeff_expTrunc (c : ℚ) {Z : ℚ⟦X⟧} (hZ : X ∣ Z) (T : ℕ) :
    constantCoeff (expTrunc c Z T) = 1 := by
  have hZ0 : constantCoeff Z = 0 := by
    obtain ⟨W, rfl⟩ := hZ; simp
  simp only [expTrunc, map_sum, map_mul, constantCoeff_C, map_pow, hZ0]
  rw [Finset.sum_eq_single 0]
  · simp
  · intro t _ ht; simp [ht]
  · simp

theorem X_pow_dvd_sub_expTrunc {c : ℚ} {Z E : ℚ⟦X⟧} (T : ℕ) (hZ : X ∣ Z)
    (hE : theta E = C c * theta Z * E) (hE0 : constantCoeff E = 1) :
    X ^ (T + 1) ∣ E - expTrunc c Z T := by
  apply X_pow_dvd_of_theta (K := C c * theta Z)
    (Rr := C (c ^ (T + 1) / T.factorial) * (theta Z * Z ^ T))
  · rw [theta_sub, hE, theta_expTrunc]; ring
  · exact Dvd.dvd.mul_left (X_dvd_theta Z) _
  · apply Dvd.dvd.mul_left
    rw [pow_succ']
    exact mul_dvd_mul (X_dvd_theta Z) (pow_dvd_pow_of_dvd hZ T)
  · rw [map_sub, hE0, constantCoeff_expTrunc c hZ, sub_self]

end

section

section Norm

variable {p : ℕ} [hp : Fact p.Prime]

theorem mul_le_one_of_le {a b : ℚ} (ha : a ≤ 1) (hb0 : 0 ≤ b) (hb : b ≤ 1) : a * b ≤ 1 := by
  nlinarith

def PI (p : ℕ) (A : ℚ⟦X⟧) : Prop := ∀ n, padicNorm p (coeff n A) ≤ 1

theorem PI.add {A B : ℚ⟦X⟧} (hA : PI p A) (hB : PI p B) : PI p (A + B) := fun n => by
  rw [map_add]; exact padicNorm.nonarchimedean.trans (max_le (hA n) (hB n))

theorem PI.neg {p : ℕ} {A : ℚ⟦X⟧} (hA : PI p A) : PI p (-A) := fun n => by
  rw [map_neg, padicNorm.neg]; exact hA n

theorem PI.sub {A B : ℚ⟦X⟧} (hA : PI p A) (hB : PI p B) : PI p (A - B) := by
  rw [sub_eq_add_neg]; exact hA.add hB.neg

theorem PI.mul {A B : ℚ⟦X⟧} (hA : PI p A) (hB : PI p B) : PI p (A * B) := fun n => by
  rw [coeff_mul]
  refine padicNorm.sum_le' (fun x _ => ?_) zero_le_one
  rw [padicNorm.mul]
  exact mul_le_one_of_le (hA _) (padicNorm.nonneg _) (hB _)

theorem PI.one {p : ℕ} : PI p (1 : ℚ⟦X⟧) := fun n => by
  rw [coeff_one]; split_ifs <;> simp

theorem PI.pow {A : ℚ⟦X⟧} (hA : PI p A) (n : ℕ) : PI p (A ^ n) := by
  induction n with
  | zero => simpa using PI.one
  | succ n ih => rw [pow_succ]; exact ih.mul hA

theorem PI.C_mul {a : ℚ} (ha : padicNorm p a ≤ 1) {A : ℚ⟦X⟧} (hA : PI p A) :
    PI p (C a * A) := fun n => by
  rw [coeff_C_mul, padicNorm.mul]
  exact mul_le_one_of_le ha (padicNorm.nonneg _) (hA n)

theorem PI.map_int (A : ℤ⟦X⟧) : PI p (map (Int.castRingHom ℚ) A) := fun n => by
  rw [coeff_map]; exact padicNorm.of_int _

theorem PI.expand {p : ℕ} {q : ℕ} (hq : q ≠ 0) {A : ℚ⟦X⟧} (hA : PI p A) :
    PI p (expand q hq A) := fun n => by
  rw [coeff_expand]; split_ifs
  · exact hA _
  · simp

theorem PI.X {p : ℕ} : PI p (X : ℚ⟦X⟧) := fun n => by
  rw [coeff_X]; split_ifs <;> simp

theorem PI.sum {ι : Type*} (s : Finset ι) {f : ι → ℚ⟦X⟧} (hf : ∀ i ∈ s, PI p (f i)) :
    PI p (∑ i ∈ s, f i) := fun n => by
  rw [map_sum]
  exact padicNorm.sum_le' (fun i hi => hf i hi n) zero_le_one

theorem padicNorm_inv_nat_of_not_dvd {n : ℕ} (hn : ¬ p ∣ n) : padicNorm p ((n : ℚ)⁻¹) = 1 := by
  have h1 := (padicNorm.nat_eq_one_iff (p := p) n).mpr hn
  have hn0 : (n : ℚ) ≠ 0 := by
    have : n ≠ 0 := by rintro rfl; exact hn (dvd_zero p)
    exact_mod_cast this
  have h2 : padicNorm p ((n : ℚ) * (n : ℚ)⁻¹) = 1 := by rw [mul_inv_cancel₀ hn0, padicNorm.one]
  rw [padicNorm.mul, h1, one_mul] at h2
  exact h2

theorem PI.Vof {L : ℚ⟦X⟧} (hL : PI p L) : PI p (Vof p L) := fun n => by
  rw [coeff_Vof]; split_ifs with h
  · simp
  · rw [div_eq_mul_inv, padicNorm.mul, padicNorm_inv_nat_of_not_dvd h, mul_one]; exact hL n

theorem padicNorm_p_pos : 0 < padicNorm p (p : ℚ) := by
  rw [padicNorm.padicNorm_p_of_prime]; exact inv_pos.mpr (by exact_mod_cast hp.out.pos)

theorem padicNorm_p_le_one : padicNorm p (p : ℚ) ≤ 1 := by
  exact_mod_cast padicNorm.of_nat (p := p) p

theorem padicNorm_pow (x : ℚ) (n : ℕ) : padicNorm p (x ^ n) = padicNorm p x ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, padicNorm.mul, ih, pow_succ]

theorem padicNorm_nat_eq (n : ℕ) (hn : n ≠ 0) :
    padicNorm p (n : ℚ) = padicNorm p (p : ℚ) ^ padicValNat p n := by
  have h := Nat.ordProj_mul_ordCompl_eq_self n p
  rw [Nat.factorization_def n hp.out] at h
  have hc : ¬ p ∣ n / p ^ padicValNat p n := by
    have := Nat.not_dvd_ordCompl hp.out hn
    rwa [Nat.factorization_def n hp.out] at this
  conv_lhs => rw [← h]
  push_cast
  rw [padicNorm.mul, padicNorm_pow, (padicNorm.nat_eq_one_iff _).mpr hc, mul_one]

theorem padicValNat_factorial_le_sub_two (h5 : 5 ≤ p) {t : ℕ} (ht : 2 ≤ t) :
    padicValNat p t.factorial ≤ t - 2 := by
  have h := sub_one_mul_padicValNat_factorial_lt_of_ne_zero p (n := t) (by omega)
  have h4 : 4 * padicValNat p t.factorial ≤ (p - 1) * padicValNat p t.factorial :=
    Nat.mul_le_mul_right _ (by omega)
  omega

theorem norm_p_pow_le_norm_factorial (h5 : 5 ≤ p) {t : ℕ} (ht : 2 ≤ t) :
    padicNorm p (p : ℚ) ^ (t - 2) ≤ padicNorm p (t.factorial : ℚ) := by
  rw [padicNorm_nat_eq _ (Nat.factorial_ne_zero t)]
  exact pow_le_pow_of_le_one (padicNorm.nonneg _) padicNorm_p_le_one
    (padicValNat_factorial_le_sub_two h5 ht)

end Norm

end

section

noncomputable section

def ιU : ℤ⟦X⟧ˣ →* ℚ⟦X⟧ˣ := Units.map (PowerSeries.map (Int.castRingHom ℚ)).toMonoidHom

@[simp] theorem val_ιU (u : ℤ⟦X⟧ˣ) : ((ιU u : ℚ⟦X⟧ˣ) : ℚ⟦X⟧) = (PowerSeries.map (Int.castRingHom ℚ)) u := rfl

theorem constantCoeff_f (a b : ℕ) : constantCoeff (f a b) = 1 := by
  unfold f
  simp only [map_mul, map_pow, constantCoeff_invOfUnit, map_sub, map_one, constantCoeff_X,
    inv_one, Units.val_one, one_pow, mul_one]
  rcases Nat.eq_zero_or_pos (a + b) with h | h
  · rw [h]; simp
  · rw [zero_pow h.ne']; simp

def fU (a b : ℕ) : ℤ⟦X⟧ˣ :=
  ⟨f a b, invOfUnit (f a b) 1, mul_invOfUnit _ 1 (by simp [constantCoeff_f]),
    invOfUnit_mul _ 1 (by simp [constantCoeff_f])⟩

theorem zpowSeries_eq (U : ℤ⟦X⟧ˣ) (hinv : invOfUnit (U : ℤ⟦X⟧) 1 = ((U⁻¹ : ℤ⟦X⟧ˣ) : ℤ⟦X⟧))
    (k : ℤ) : zpowSeries (U : ℤ⟦X⟧) k = ((U ^ k : ℤ⟦X⟧ˣ) : ℤ⟦X⟧) := by
  unfold zpowSeries
  split_ifs with h
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le h
    simp
  · have hk : k = -((k.natAbs : ℕ) : ℤ) := by omega
    rw [hk, zpow_neg, zpow_natCast, Int.natAbs_neg, Int.natAbs_natCast, hinv, ← inv_pow,
      Units.val_pow_eq_pow_val]

theorem zpowSeries_f (a b : ℕ) (k : ℤ) :
    zpowSeries (f a b) k = ((fU a b ^ k : ℤ⟦X⟧ˣ) : ℤ⟦X⟧) :=
  zpowSeries_eq (fU a b) rfl k

def oneSubU (e : ℕ) (he : 0 < e) : ℤ⟦X⟧ˣ :=
  ⟨1 - X ^ e, invOfUnit (1 - X ^ e) 1, mul_invOfUnit _ 1 (by simp [zero_pow he.ne']),
    invOfUnit_mul _ 1 (by simp [zero_pow he.ne'])⟩

theorem fU_eq {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    fU a b = oneSubU (a + b) (by omega) ^ (a + b) * (oneSubU a ha)⁻¹ ^ a *
      (oneSubU b hb)⁻¹ ^ b := by
  apply Units.ext
  simp [fU, oneSubU, f]

def Le (e : ℕ) : ℚ⟦X⟧ := mk fun n => if n ≠ 0 ∧ e ∣ n then -(e : ℚ) else 0

theorem theta_one_sub_X_pow {e : ℕ} (he : 0 < e) :
    theta (1 - X ^ e : ℚ⟦X⟧) = Le e * (1 - X ^ e) := by
  ext n
  rw [coeff_theta, mul_sub, mul_one, map_sub, map_sub, coeff_one, coeff_X_pow,
    coeff_mul_X_pow', Le, coeff_mk]
  by_cases h0 : n = 0
  · subst h0; simp [show ¬ e ≤ 0 by omega]
  by_cases hne : n = e
  · subst hne
    rw [if_neg h0, if_pos rfl, if_pos ⟨h0, dvd_refl n⟩, if_pos le_rfl,
      Nat.sub_self, coeff_mk, if_neg (fun h => h.1 rfl)]
    ring
  by_cases hlt : n < e
  · have hnd : ¬ e ∣ n := fun hd => absurd (Nat.le_of_dvd (Nat.pos_of_ne_zero h0) hd) (by omega)
    simp [hnd, show ¬ e ≤ n by omega, hne, h0]
  · have hdv : e ∣ n ↔ e ∣ n - e := by
      conv_lhs => rw [show n = n - e + e by omega]
      exact Nat.dvd_add_self_right
    rw [if_neg h0, if_neg hne, if_pos (show e ≤ n by omega), coeff_mk]
    by_cases hd : e ∣ n
    · rw [if_pos ⟨h0, hd⟩, if_pos ⟨by omega, hdv.1 hd⟩]; ring
    · rw [if_neg (fun h => hd h.2), if_neg (fun h => hd (hdv.2 h.2))]; ring

theorem hasLD_oneSubU {e : ℕ} (he : 0 < e) : HasLD (ιU (oneSubU e he)) (Le e) := by
  unfold HasLD
  rw [val_ιU]
  have : (PowerSeries.map (Int.castRingHom ℚ)) ((oneSubU e he : ℤ⟦X⟧ˣ) : ℤ⟦X⟧) = 1 - X ^ e := by simp [oneSubU]
  rw [this]; exact theta_one_sub_X_pow he

def cf (a b n : ℕ) : ℤ :=
  if n = 0 then 0 else
    (if a ∣ n then (a : ℤ) ^ 2 else 0) + (if b ∣ n then (b : ℤ) ^ 2 else 0) -
      (if a + b ∣ n then ((a + b : ℕ) : ℤ) ^ 2 else 0)

def Λq (a b : ℕ) : ℚ⟦X⟧ := mk fun n => (cf a b n : ℚ)

theorem coeff_natCast_mul (k : ℕ) (L : ℚ⟦X⟧) (n : ℕ) :
    coeff n ((k : ℚ⟦X⟧) * L) = k * coeff n L := by
  rw [← map_natCast (C (R := ℚ)), coeff_C_mul]

theorem hasLD_fU {a b : ℕ} (ha : 0 < a) (hb : 0 < b) : HasLD (ιU (fU a b)) (Λq a b) := by
  rw [fU_eq ha hb, map_mul, map_mul, map_pow, map_pow, map_pow, map_inv, map_inv]
  refine ((((hasLD_oneSubU (by omega : 0 < a + b)).pow (a + b)).mul
    (((hasLD_oneSubU ha).inv).pow a)).mul (((hasLD_oneSubU hb).inv).pow b)).congr ?_
  ext n
  simp only [map_add, coeff_natCast_mul, map_neg, Le, coeff_mk, Λq, cf]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · simp only [hn.ne', ne_eq, not_false_eq_true, true_and, ite_false]
    split_ifs <;> push_cast <;> ring

def cU : ℚ⟦X⟧ˣ →* ℚˣ := Units.map (constantCoeff (R := ℚ)).toMonoidHom

@[simp] theorem val_cU (u : ℚ⟦X⟧ˣ) : ((cU u : ℚˣ) : ℚ) = constantCoeff (u : ℚ⟦X⟧) := rfl

end

end

section

noncomputable section

variable {p : ℕ} [hp : Fact p.Prime]

theorem hp0 : p ≠ 0 := hp.out.ne_zero

theorem dvd_mul_iff_of_not_dvd {e : ℕ} (he : ¬ p ∣ e) (m : ℕ) : e ∣ p * m ↔ e ∣ m :=
  Nat.Coprime.dvd_mul_left (Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hp.out).2 he))

theorem cf_mul {a b : ℕ} (hpa : ¬ p ∣ a) (hpb : ¬ p ∣ b) (hpm : ¬ p ∣ a + b) (m : ℕ) :
    cf a b (p * m) = cf a b m := by
  unfold cf
  simp only [mul_eq_zero, hp0, false_or, dvd_mul_iff_of_not_dvd hpa,
    dvd_mul_iff_of_not_dvd hpb, dvd_mul_iff_of_not_dvd hpm]

theorem coeff_Λq_mul {a b : ℕ} (hpa : ¬ p ∣ a) (hpb : ¬ p ∣ b) (hpm : ¬ p ∣ a + b) (m : ℕ) :
    coeff (p * m) (Λq a b) = coeff m (Λq a b) := by
  simp only [Λq, coeff_mk, cf_mul hpa hpb hpm]

theorem PI_Λq (a b : ℕ) : PI p (Λq a b) := fun n => by
  simp only [Λq, coeff_mk]; exact padicNorm.of_int _

def Mred (p : ℕ) (a b : ℕ) : ℚ⟦X⟧ := Vof p (Λq a b)

theorem PI_Mred (a b : ℕ) : PI p (Mred p a b) := (PI_Λq a b).Vof

end

end

section

noncomputable section

def uF (F : ℤ⟦X⟧ˣ) (r : ℕ) (s : ℤ) (N : ℕ) : ℤ := coeff (r * N) ((F ^ (s * N) : ℤ⟦X⟧ˣ) : ℤ⟦X⟧)

def GF (F : ℤ⟦X⟧ˣ) (s : ℤ) : ℚ⟦X⟧ˣ := ιU (F ^ s)

theorem uF_eq_coeff_GF (F : ℤ⟦X⟧ˣ) (r : ℕ) (s : ℤ) (N : ℕ) :
    (uF F r s N : ℚ) = coeff (r * N) ((GF F s ^ N : ℚ⟦X⟧ˣ) : ℚ⟦X⟧) := by
  rw [uF, GF, ← map_pow, ← zpow_natCast, ← zpow_mul, val_ιU, coeff_map]
  rfl

theorem cU_GF {F : ℤ⟦X⟧ˣ} (hF : constantCoeff (F : ℤ⟦X⟧) = 1) (s : ℤ) : cU (GF F s) = 1 := by
  have h1 : cU (ιU F) = 1 := Units.ext (by
    rw [val_cU, val_ιU, ← coeff_zero_eq_constantCoeff_apply, coeff_map,
      coeff_zero_eq_constantCoeff_apply, hF]
    simp)
  rw [GF, map_zpow, map_zpow, h1, one_zpow]

def CubicHyp (p : ℕ) (F : ℤ⟦X⟧ˣ) (Λ : ℚ⟦X⟧) : Prop :=
  constantCoeff (F : ℤ⟦X⟧) = 1 ∧
  HasLD (ιU F) Λ ∧
  PI p Λ ∧
  (∀ m, coeff (p * m) Λ = coeff m Λ) ∧
  ∀ j, padicNorm p (coeff (p * j) (Vof p Λ ^ 2)) ≤ padicNorm p p * padicNorm p j

theorem CubicHyp.const {p : ℕ} {F : ℤ⟦X⟧ˣ} {Λ : ℚ⟦X⟧}
    (H : CubicHyp p F Λ) : constantCoeff (F : ℤ⟦X⟧) = 1 := H.1

theorem CubicHyp.hasLD {p : ℕ} {F : ℤ⟦X⟧ˣ} {Λ : ℚ⟦X⟧}
    (H : CubicHyp p F Λ) : HasLD (ιU F) Λ := H.2.1

theorem CubicHyp.pint {p : ℕ} {F : ℤ⟦X⟧ˣ} {Λ : ℚ⟦X⟧}
    (H : CubicHyp p F Λ) : PI p Λ := H.2.2.1

theorem CubicHyp.per {p : ℕ} {F : ℤ⟦X⟧ˣ} {Λ : ℚ⟦X⟧}
    (H : CubicHyp p F Λ) : ∀ m, coeff (p * m) Λ = coeff m Λ := H.2.2.2.1

theorem CubicHyp.quad {p : ℕ} {F : ℤ⟦X⟧ˣ} {Λ : ℚ⟦X⟧}
    (H : CubicHyp p F Λ) :
    ∀ j, padicNorm p (coeff (p * j) (Vof p Λ ^ 2)) ≤ padicNorm p p * padicNorm p j :=
  H.2.2.2.2

variable {p : ℕ} [hp : Fact p.Prime] {F : ℤ⟦X⟧ˣ} {Λ : ℚ⟦X⟧}

theorem hasLD_GF {p : ℕ} (H : CubicHyp p F Λ) (s : ℤ) : HasLD (GF F s) (C (s : ℚ) * Λ) := by
  rw [GF, map_zpow]
  exact (H.hasLD.zpow s).congr (by rw [map_intCast])

theorem PI_GF_pow (F : ℤ⟦X⟧ˣ) (s : ℤ) (N : ℕ) : PI p ((GF F s ^ N : ℚ⟦X⟧ˣ) : ℚ⟦X⟧) := by
  rw [GF, ← map_pow, val_ιU]; exact PI.map_int _

def ZF (p : ℕ) (Λ : ℚ⟦X⟧) (s : ℤ) : ℚ⟦X⟧ := Vof p (C (s : ℚ) * Λ)

theorem ZF_eq {p : ℕ} (Λ : ℚ⟦X⟧) (s : ℤ) : ZF p Λ s = C (s : ℚ) * Vof p Λ := by
  rw [ZF, Vof_C_mul]

theorem theta_ZF (H : CubicHyp p F Λ) (s : ℤ) :
    theta (ZF p Λ s) = C (s : ℚ) * Λ - expand p hp0 (C (s : ℚ) * Λ) :=
  theta_Vof p hp0 _ (fun m => by simp only [coeff_C_mul, H.per])

theorem PI_ZF (H : CubicHyp p F Λ) (s : ℤ) : PI p (ZF p Λ s) :=
  (PI.C_mul (padicNorm.of_int s) H.pint).Vof

def Eu (p : ℕ) [Fact p.Prime] (F : ℤ⟦X⟧ˣ) (s : ℤ) (M : ℕ) : ℚ⟦X⟧ˣ :=
  GF F s ^ (p * M) * (exU p hp0 (GF F s))⁻¹ ^ M

theorem GF_pow_eq (F : ℤ⟦X⟧ˣ) (s : ℤ) (M : ℕ) :
    GF F s ^ (p * M) = exU p hp0 (GF F s ^ M) * Eu p F s M := by
  rw [Eu, map_pow, inv_pow, mul_left_comm, mul_inv_cancel, mul_one]

theorem hasLD_Eu (H : CubicHyp p F Λ) (s : ℤ) (M : ℕ) :
    HasLD (Eu p F s M) (C ((p : ℚ) * M) * theta (ZF p Λ s)) := by
  refine ((((hasLD_GF H s).pow (p * M)).mul
    (((hasLD_GF H s).expand p hp0).inv.pow M))).congr ?_
  rw [theta_ZF H, map_mul (C (R := ℚ)), map_natCast (C (R := ℚ)), map_natCast (C (R := ℚ)),
    Nat.cast_mul]
  ring

theorem constantCoeff_Eu (H : CubicHyp p F Λ) (s : ℤ) (M : ℕ) :
    constantCoeff ((Eu p F s M : ℚ⟦X⟧ˣ) : ℚ⟦X⟧) = 1 := by
  have h1 : cU (exU p hp0 (GF F s)) = 1 := by
    apply Units.ext
    rw [val_cU, val_exU, constantCoeff_expand, ← val_cU, cU_GF H.const]
  have : cU (Eu p F s M) = 1 := by
    rw [Eu, map_mul, map_pow, map_pow, map_inv, cU_GF H.const, h1]; simp
  rw [← val_cU, this]; rfl

def Sx (p : ℕ) (F : ℤ⟦X⟧ˣ) (Λ : ℚ⟦X⟧) (r : ℕ) (s : ℤ) (M t : ℕ) : ℚ :=
  ∑ x ∈ antidiagonal (r * M),
    coeff x.1 ((GF F s ^ M : ℚ⟦X⟧ˣ) : ℚ⟦X⟧) * coeff (p * x.2) (ZF p Λ s ^ t)

theorem expansion (H : CubicHyp p F Λ) (r : ℕ) (s : ℤ) (M : ℕ) :
    (uF F r s (p * M) : ℚ) = ∑ t ∈ range (p * (r * M) + 1),
      ((p : ℚ) * M) ^ t / t.factorial * Sx p F Λ r s M t := by
  rw [uF_eq_coeff_GF, GF_pow_eq, Units.val_mul, val_exU, show r * (p * M) = p * (r * M) by ring]
  have hdvd := X_pow_dvd_sub_expTrunc (p * (r * M)) (X_dvd_Vof p (C (s : ℚ) * Λ))
    (hasLD_Eu H s M) (constantCoeff_Eu H s M)
  rw [coeff_mul_eq_of_X_pow_dvd _ hdvd, expTrunc, Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [show expand p hp0 ((GF F s ^ M : ℚ⟦X⟧ˣ) : ℚ⟦X⟧) * (C (((p : ℚ) * M) ^ t / t.factorial) *
      Vof p (C (s : ℚ) * Λ) ^ t) = C (((p : ℚ) * M) ^ t / t.factorial) *
      (expand p hp0 ((GF F s ^ M : ℚ⟦X⟧ˣ) : ℚ⟦X⟧) * ZF p Λ s ^ t) by rw [ZF]; ring,
    coeff_C_mul, coeff_p_mul_expand_mul]
  rfl

theorem Sx_zero (F : ℤ⟦X⟧ˣ) (Λ : ℚ⟦X⟧) (r : ℕ) (s : ℤ) (M : ℕ) :
    Sx p F Λ r s M 0 = uF F r s M := by
  rw [uF_eq_coeff_GF, Sx, ← mul_one ((GF F s ^ M : ℚ⟦X⟧ˣ) : ℚ⟦X⟧), coeff_mul, mul_one]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [pow_zero, coeff_one, coeff_one]
  simp [hp0]

theorem Sx_one {p : ℕ} (F : ℤ⟦X⟧ˣ) (Λ : ℚ⟦X⟧) (r : ℕ) (s : ℤ) (M : ℕ) : Sx p F Λ r s M 1 = 0 := by
  refine Finset.sum_eq_zero fun x _ => ?_
  rw [pow_one, ZF, coeff_p_mul_Vof, mul_zero]

theorem norm_coeff_GF_pow (H : CubicHyp p F Λ) (s : ℤ) (M i : ℕ) :
    padicNorm p (coeff i ((GF F s ^ M : ℚ⟦X⟧ˣ) : ℚ⟦X⟧)) * padicNorm p i ≤ padicNorm p M := by
  have h := congrArg (coeff i) ((hasLD_GF H s).pow M)
  rw [coeff_theta, mul_assoc, ← map_natCast (C (R := ℚ)), coeff_C_mul] at h
  have h2 := congrArg (padicNorm p) h
  rw [padicNorm.mul, padicNorm.mul] at h2
  have h3 : padicNorm p (coeff i (C (s : ℚ) * Λ * ((GF F s ^ M : ℚ⟦X⟧ˣ) : ℚ⟦X⟧))) ≤ 1 :=
    ((PI.C_mul (padicNorm.of_int s) H.pint).mul (PI_GF_pow F s M)) i
  rw [mul_comm, h2]
  calc padicNorm p M * padicNorm p (coeff i (C (s : ℚ) * Λ * ((GF F s ^ M : ℚ⟦X⟧ˣ) : ℚ⟦X⟧)))
      ≤ padicNorm p M * 1 := mul_le_mul_of_nonneg_left h3 (padicNorm.nonneg _)
    _ = _ := mul_one _

theorem norm_coeff_ZF_sq (H : CubicHyp p F Λ) (s : ℤ) (j : ℕ) :
    padicNorm p (coeff (p * j) (ZF p Λ s ^ 2)) ≤ padicNorm p p * padicNorm p j := by
  rw [ZF_eq, mul_pow, ← map_pow, coeff_C_mul, padicNorm.mul]
  calc padicNorm p ((s : ℚ) ^ 2) * padicNorm p (coeff (p * j) (Vof p Λ ^ 2))
      ≤ 1 * (padicNorm p p * padicNorm p j) :=
        mul_le_mul (by rw [padicNorm_pow]; exact pow_le_one₀ (padicNorm.nonneg _) (padicNorm.of_int s))
          (H.quad j) (padicNorm.nonneg _) zero_le_one
    _ = _ := one_mul _

theorem norm_Sx_two (H : CubicHyp p F Λ) (r : ℕ) (s : ℤ) (M : ℕ) :
    padicNorm p (Sx p F Λ r s M 2) ≤ padicNorm p p * padicNorm p M := by
  refine padicNorm.sum_le' (fun x hx => ?_) (mul_nonneg (padicNorm.nonneg _) (padicNorm.nonneg _))
  have hx' := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
  rw [padicNorm.mul]
  have hc := norm_coeff_ZF_sq H s x.2
  have hg := norm_coeff_GF_pow H s M x.1
  have hg1 : padicNorm p (coeff x.1 ((GF F s ^ M : ℚ⟦X⟧ˣ) : ℚ⟦X⟧)) ≤ 1 := PI_GF_pow F s M x.1
  have hpp := padicNorm.nonneg (p := p) (p : ℚ)
  by_cases hj : padicNorm p (x.2 : ℚ) ≤ padicNorm p M
  · calc padicNorm p (coeff x.1 ((GF F s ^ M : ℚ⟦X⟧ˣ) : ℚ⟦X⟧)) *
          padicNorm p (coeff (p * x.2) (ZF p Λ s ^ 2))
        ≤ 1 * (padicNorm p p * padicNorm p x.2) :=
          mul_le_mul hg1 hc (padicNorm.nonneg _) zero_le_one
      _ ≤ padicNorm p p * padicNorm p M := by
          rw [one_mul]; exact mul_le_mul_of_nonneg_left hj hpp
  · replace hj := lt_of_not_ge hj
    have hrM : padicNorm p ((r : ℚ) * M) < padicNorm p (x.2 : ℚ) := by
      rw [padicNorm.mul]
      calc padicNorm p (r : ℚ) * padicNorm p M ≤ 1 * padicNorm p M :=
            mul_le_mul_of_nonneg_right (padicNorm.of_nat r) (padicNorm.nonneg _)
        _ < _ := by rw [one_mul]; exact hj
    have hi : padicNorm p (x.1 : ℚ) = padicNorm p (x.2 : ℚ) := by
      have e : (x.1 : ℚ) = (r : ℚ) * M + -(x.2 : ℚ) := by
        have : ((x.1 + x.2 : ℕ) : ℚ) = ((r * M : ℕ) : ℚ) := by rw [hx']
        push_cast at this; linarith
      rw [e, padicNorm.add_eq_max_of_ne (by rw [padicNorm.neg]; exact hrM.ne), padicNorm.neg,
        max_eq_right hrM.le]
    calc padicNorm p (coeff x.1 ((GF F s ^ M : ℚ⟦X⟧ˣ) : ℚ⟦X⟧)) *
          padicNorm p (coeff (p * x.2) (ZF p Λ s ^ 2))
        ≤ padicNorm p (coeff x.1 ((GF F s ^ M : ℚ⟦X⟧ˣ) : ℚ⟦X⟧)) *
            (padicNorm p p * padicNorm p x.2) :=
          mul_le_mul_of_nonneg_left hc (padicNorm.nonneg _)
      _ = padicNorm p p *
            (padicNorm p (coeff x.1 ((GF F s ^ M : ℚ⟦X⟧ˣ) : ℚ⟦X⟧)) * padicNorm p x.1) := by
          rw [hi]; ring
      _ ≤ padicNorm p p * padicNorm p M := mul_le_mul_of_nonneg_left hg hpp

theorem norm_Sx_le_one (H : CubicHyp p F Λ) (r : ℕ) (s : ℤ) (M t : ℕ) :
    padicNorm p (Sx p F Λ r s M t) ≤ 1 := by
  refine padicNorm.sum_le' (fun x _ => ?_) zero_le_one
  rw [padicNorm.mul]
  exact mul_le_one_of_le (PI_GF_pow F s M x.1) (padicNorm.nonneg _) (((PI_ZF H s).pow t) _)

theorem padicValNat_factorial_add_three_le (h5 : 5 ≤ p) (t : ℕ) :
    padicValNat p (t + 3).factorial ≤ t := by
  have h := sub_one_mul_padicValNat_factorial_lt_of_ne_zero p (n := t + 3) (by omega)
  have h4 : 4 * padicValNat p (t + 3).factorial ≤ (p - 1) * padicValNat p (t + 3).factorial :=
    Nat.mul_le_mul_right _ (by omega)
  omega

theorem norm_pow_div_factorial_three (h5 : 5 ≤ p) {c : ℚ} (hc : padicNorm p c ≤ padicNorm p p)
    (t : ℕ) : padicNorm p (c ^ (t + 3) / (t + 3).factorial) ≤ padicNorm p c ^ 3 := by
  have hf : padicNorm p (p : ℚ) ^ t ≤ padicNorm p ((t + 3).factorial : ℚ) := by
    rw [padicNorm_nat_eq _ (Nat.factorial_ne_zero _)]
    exact pow_le_pow_of_le_one (padicNorm.nonneg _) padicNorm_p_le_one
      (padicValNat_factorial_add_three_le h5 t)
  have hfpos : 0 < padicNorm p ((t + 3).factorial : ℚ) := by
    have : ((t + 3).factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    exact lt_of_le_of_ne (padicNorm.nonneg _) (padicNorm.nonzero this).symm
  rw [padicNorm.div, padicNorm_pow, div_le_iff₀ hfpos, pow_add]
  have h1 : padicNorm p c ^ t ≤ padicNorm p p ^ t :=
    pow_le_pow_left₀ (padicNorm.nonneg _) hc t
  calc padicNorm p c ^ t * padicNorm p c ^ 3 ≤ padicNorm p p ^ t * padicNorm p c ^ 3 :=
        mul_le_mul_of_nonneg_right h1 (pow_nonneg (padicNorm.nonneg _) 3)
    _ ≤ padicNorm p ((t + 3).factorial : ℚ) * padicNorm p c ^ 3 :=
        mul_le_mul_of_nonneg_right hf (pow_nonneg (padicNorm.nonneg _) 3)
    _ = _ := by ring

theorem padicNorm_two (h5 : 5 ≤ p) : padicNorm p (2 : ℚ) = 1 := by
  have := (padicNorm.nat_eq_one_iff (p := p) 2).2 (fun h => by
    have := Nat.le_of_dvd (by norm_num) h; omega)
  simpa using this

theorem main_estimate (h5 : 5 ≤ p) (H : CubicHyp p F Λ) (r : ℕ) (s : ℤ) (M : ℕ) :
    padicNorm p (((uF F r s (p * M) - uF F r s M : ℤ)) : ℚ) ≤ padicNorm p ((p : ℚ) * M) ^ 3 := by
  push_cast
  rw [expansion H r s M, Finset.sum_range_succ', Sx_zero]
  simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, one_mul, add_sub_cancel_right]
  have hc : padicNorm p ((p : ℚ) * M) ≤ padicNorm p p := by
    rw [padicNorm.mul]
    calc padicNorm p (p : ℚ) * padicNorm p (M : ℚ) ≤ padicNorm p p * 1 :=
          mul_le_mul_of_nonneg_left (padicNorm.of_nat M) (padicNorm.nonneg _)
      _ = _ := mul_one _
  refine padicNorm.sum_le' (fun t _ => ?_) (pow_nonneg (padicNorm.nonneg _) 3)
  rcases t with _ | _ | t
  · rw [zero_add, Sx_one, mul_zero, padicNorm.zero]; exact pow_nonneg (padicNorm.nonneg _) 3
  · rw [show 0 + 1 + 1 = 2 by rfl, Nat.factorial_two, Nat.cast_ofNat, padicNorm.mul, padicNorm.div,
      padicNorm_two h5, div_one, padicNorm_pow]
    have h2 := norm_Sx_two H r s M
    rw [← padicNorm.mul] at h2
    calc padicNorm p ((p : ℚ) * M) ^ 2 * padicNorm p (Sx p F Λ r s M 2)
        ≤ padicNorm p ((p : ℚ) * M) ^ 2 * padicNorm p ((p : ℚ) * M) :=
          mul_le_mul_of_nonneg_left h2 (pow_nonneg (padicNorm.nonneg _) 2)
      _ = _ := by ring
  · rw [padicNorm.mul, show t + 1 + 1 + 1 = t + 3 by ring]
    calc padicNorm p (((p : ℚ) * M) ^ (t + 3) / ((t + 3).factorial : ℚ)) *
          padicNorm p (Sx p F Λ r s M (t + 3))
        ≤ padicNorm p ((p : ℚ) * M) ^ 3 * 1 :=
          mul_le_mul (norm_pow_div_factorial_three h5 hc t) (norm_Sx_le_one H r s M _)
            (padicNorm.nonneg _) (pow_nonneg (padicNorm.nonneg _) 3)
      _ = _ := mul_one _

theorem uF_tower (h5 : 5 ≤ p) (H : CubicHyp p F Λ) (r : ℕ) (s : ℤ) (n k : ℕ) (hk : 0 < k) :
    (p : ℤ) ^ (3 * k) ∣ uF F r s (n * p ^ k) - uF F r s (n * p ^ (k - 1)) := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  set M := n * p ^ k'
  have hNk : n * p ^ (k' + 1) = p * M := by simp only [M]; ring
  rw [hNk, show k' + 1 - 1 = k' by omega]
  have h := main_estimate h5 H r s M
  have hM' : padicNorm p (M : ℚ) ≤ padicNorm p p ^ k' := by
    simp only [M]; push_cast
    rw [padicNorm.mul, padicNorm_pow]
    exact mul_le_of_le_one_left (pow_nonneg (padicNorm.nonneg _) _) (padicNorm.of_nat n)
  have hle : padicNorm p ((uF F r s (p * M) - uF F r s M : ℤ) : ℚ) ≤
      (p : ℚ) ^ (-((3 * (k' + 1) : ℕ) : ℤ)) := by
    calc _ ≤ padicNorm p ((p : ℚ) * M) ^ 3 := h
      _ = (padicNorm p p * padicNorm p M) ^ 3 := by rw [padicNorm.mul]
      _ ≤ (padicNorm p p * padicNorm p p ^ k') ^ 3 := by
          have h0 : 0 ≤ padicNorm p (p : ℚ) * padicNorm p (M : ℚ) :=
            mul_nonneg (padicNorm.nonneg _) (padicNorm.nonneg _)
          exact pow_le_pow_left₀ h0 (mul_le_mul_of_nonneg_left hM' (padicNorm.nonneg _)) 3
      _ = padicNorm p p ^ (3 * (k' + 1)) := by rw [← pow_succ', ← pow_mul]; ring_nf
      _ = (p : ℚ) ^ (-((3 * (k' + 1) : ℕ) : ℤ)) := by
          rw [padicNorm.padicNorm_p_of_prime, zpow_neg, zpow_natCast, inv_pow]
  have := (padicNorm.dvd_iff_norm_le (p := p) (n := 3 * (k' + 1))).mpr hle
  exact_mod_cast this

end

end

section Core

variable {P : ℕ} [NeZero P]

noncomputable def zeta (x : ZMod P) : ZMod P :=
  ∑ t ∈ range x.val, Ring.inverse (t : ZMod P) ^ 2

theorem sum_range_natCast {M : Type*} [AddCommMonoid M] (H : ZMod P → M) :
    ∑ x ∈ range P, H (x : ZMod P) = ∑ z : ZMod P, H z := by
  refine Finset.sum_nbij' (fun x => (x : ZMod P)) (fun z => z.val) ?_ ?_ ?_ ?_ ?_
  · intro a _; exact mem_univ _
  · intro a _; exact mem_range.2 (ZMod.val_lt a)
  · intro a ha; rw [ZMod.val_natCast, Nat.mod_eq_of_lt (mem_range.1 ha)]
  · intro a _; exact ZMod.natCast_zmod_val a
  · intro a _; rfl

theorem inverse_neg_sq {M : Type*} [CommRing M] (x : M) :
    Ring.inverse (-x) ^ 2 = Ring.inverse x ^ 2 := by
  rw [Ring.inverse_pow, Ring.inverse_pow, neg_sq]

theorem sum_inverse_sq (h2 : IsUnit (2 : ZMod P)) (h3 : IsUnit (3 : ZMod P)) :
    ∑ z : ZMod P, Ring.inverse z ^ 2 = 0 := by
  obtain ⟨t, ht⟩ := h2
  have key : ∀ z : ZMod P, Ring.inverse ((t : ZMod P) * z) ^ 2 =
      Ring.inverse (2 : ZMod P) ^ 2 * Ring.inverse z ^ 2 := by
    intro z; rw [ht, Ring.mul_inverse_rev]; ring
  have h4 : ∑ z : ZMod P, Ring.inverse z ^ 2 =
      Ring.inverse (2 : ZMod P) ^ 2 * ∑ z : ZMod P, Ring.inverse z ^ 2 := by
    calc ∑ z : ZMod P, Ring.inverse z ^ 2
        = ∑ z : ZMod P, Ring.inverse ((t : ZMod P) * z) ^ 2 :=
          (Equiv.sum_comp (Units.mulLeft t) (fun z => Ring.inverse z ^ 2)).symm
      _ = _ := by rw [mul_sum]; exact sum_congr rfl (fun z _ => key z)
  have h22 : (2 : ZMod P) * Ring.inverse 2 = 1 := Ring.mul_inverse_cancel _ (ht ▸ t.isUnit)
  have h3S : (3 : ZMod P) * ∑ z : ZMod P, Ring.inverse z ^ 2 = 0 := by
    linear_combination 4 * h4 +
      (∑ z : ZMod P, Ring.inverse z ^ 2) * (2 * Ring.inverse (2 : ZMod P) + 1) * h22
  exact h3.mul_right_eq_zero.1 h3S

variable (h2 : IsUnit (2 : ZMod P)) (h3 : IsUnit (3 : ZMod P))

theorem zeta_succ (h2 : IsUnit (2 : ZMod P)) (h3 : IsUnit (3 : ZMod P)) (x : ZMod P) : zeta (x + 1) = zeta x + Ring.inverse x ^ 2 := by
  obtain rfl | hP1 := eq_or_ne P 1
  · exact Subsingleton.elim _ _
  by_cases hx : x.val + 1 < P
  · have hv : (x + 1).val = x.val + 1 := by
      rw [ZMod.val_add, ZMod.val_one'' hP1, Nat.mod_eq_of_lt hx]
    unfold zeta; rw [hv, sum_range_succ, ZMod.natCast_zmod_val]
  · have hx' : x.val + 1 = P := by have := ZMod.val_lt x; omega
    have hx1 : x + 1 = 0 := by
      have : ((x.val + 1 : ℕ) : ZMod P) = 0 := by rw [hx']; exact ZMod.natCast_self P
      rwa [Nat.cast_add, ZMod.natCast_zmod_val, Nat.cast_one] at this
    have : zeta x + Ring.inverse x ^ 2 = ∑ t ∈ range P, Ring.inverse (t : ZMod P) ^ 2 := by
      unfold zeta
      rw [show range P = range (x.val + 1) from congrArg range hx'.symm, sum_range_succ,
        ZMod.natCast_zmod_val]
    rw [this, sum_range_natCast (fun z => Ring.inverse z ^ 2), sum_inverse_sq h2 h3, hx1]
    simp [zeta]

theorem zeta_zero {P : ℕ} : zeta (0 : ZMod P) = 0 := by simp [zeta]

theorem zeta_one (h2 : IsUnit (2 : ZMod P)) (h3 : IsUnit (3 : ZMod P)) : zeta (1 : ZMod P) = 0 := by
  have := zeta_succ h2 h3 0
  rw [zero_add] at this; rw [this, zeta_zero]; simp

theorem zeta_one_sub (h2 : IsUnit (2 : ZMod P)) (h3 : IsUnit (3 : ZMod P)) (x : ZMod P) : zeta (1 - x) = -zeta x := by
  suffices h : ∀ n : ℕ, zeta (1 - (n : ZMod P)) + zeta (n : ZMod P) = 0 by
    have := h x.val
    rw [ZMod.natCast_zmod_val] at this
    linear_combination this
  intro n
  induction n with
  | zero => simp [zeta_one h2 h3, zeta_zero]
  | succ n ih =>
    have e1 := zeta_succ h2 h3 (-(n : ZMod P))
    have e2 := zeta_succ h2 h3 (n : ZMod P)
    rw [inverse_neg_sq] at e1
    rw [show (1 : ZMod P) - (n : ZMod P) = -(n : ZMod P) + 1 by ring] at ih
    rw [show (1 : ZMod P) - ((n + 1 : ℕ) : ZMod P) = -(n : ZMod P) by push_cast; ring,
      show ((n + 1 : ℕ) : ZMod P) = (n : ZMod P) + 1 by push_cast; ring, e2]
    linear_combination ih - e1

theorem sum_class (h2 : IsUnit (2 : ZMod P)) (h3 : IsUnit (3 : ZMod P)) {d : ZMod P} (hd : IsUnit d) (β : ZMod P) (K : ℕ) :
    ∑ k ∈ range K, Ring.inverse (β + d * (k : ZMod P)) ^ 2 =
      Ring.inverse d ^ 2 *
        (zeta ((β + d * (K : ZMod P)) * Ring.inverse d) - zeta (β * Ring.inverse d)) := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [sum_range_succ, ih]
    have hdd : d * Ring.inverse d = 1 := Ring.mul_inverse_cancel _ hd
    have e : (β + d * ((K + 1 : ℕ) : ZMod P)) * Ring.inverse d =
        (β + d * (K : ZMod P)) * Ring.inverse d + 1 := by
      push_cast; linear_combination hdd
    rw [e, zeta_succ h2 h3, Ring.mul_inverse_rev, Ring.inverse_inverse hd]
    linear_combination (-(Ring.inverse d * d + 1) * Ring.inverse (β + d * (K : ZMod P)) ^ 2) * hdd

end Core

section Reindex

variable {M : Type*} [AddCommMonoid M]

theorem not_mod_eq_of_lt {D β j E : ℕ} (hE : E % D = β) (hj : j < E) (hjE : E < j + D)
    (h : j % D = β) : False := by
  have h1 : j ≡ E [MOD D] := by unfold Nat.ModEq; rw [h, hE]
  have h2 : D ∣ E - j := (Nat.modEq_iff_dvd' hj.le).1 h1
  have h3 : E - j ≠ 0 := by omega
  have := Nat.le_of_dvd (by omega) h2
  omega

theorem sum_range_ite_mod (F : ℕ → M) {D β : ℕ} (hβ : β < D) (K : ℕ) :
    ∑ j ∈ range (β + D * K), (if j % D = β then F j else 0) =
      ∑ k ∈ range K, F (β + D * k) := by
  induction K with
  | zero =>
    simp only [mul_zero, add_zero, range_zero, sum_empty]
    refine sum_eq_zero fun j hj => ?_
    rw [mem_range] at hj
    rw [if_neg (by rw [Nat.mod_eq_of_lt (by omega)]; omega)]
  | succ K ih =>
    rw [show β + D * (K + 1) = (β + D * K) + D by ring, sum_range_add, ih, sum_range_succ]
    congr 1
    rw [sum_eq_single 0]
    · rw [add_zero, if_pos (by rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hβ])]
    · intro x hx hx0
      rw [mem_range] at hx
      have hm : D * (K + 1) = D * K + D := by ring
      refine if_neg fun h => ?_
      exact not_mod_eq_of_lt (D := D) (E := β + D * (K + 1)) (j := β + D * K + x)
        (by rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hβ]) (by omega) (by omega) h
    · intro h; exact absurd (mem_range.2 (by omega)) h

theorem sum_range_ite_mod_ext (F : ℕ → M) {D β U E : ℕ} (hUE : U ≤ E) (hEU : E < U + D)
    (hE : E % D = β) :
    ∑ j ∈ range U, (if j % D = β then F j else 0) =
      ∑ j ∈ range E, (if j % D = β then F j else 0) := by
  obtain ⟨c, rfl⟩ : ∃ c, E = U + c := ⟨E - U, by omega⟩
  rw [sum_range_add]
  have : ∑ x ∈ range c, (if (U + x) % D = β then F (U + x) else 0) = 0 := by
    refine sum_eq_zero fun x hx => ?_
    rw [mem_range] at hx
    exact if_neg fun h => not_mod_eq_of_lt hE (by omega) (by omega) h
  rw [this, add_zero]

end Reindex

section Class

variable {P : ℕ} [NeZero P] (h2 : IsUnit (2 : ZMod P)) (h3 : IsUnit (3 : ZMod P))

theorem sum_class_nat (h2 : IsUnit (2 : ZMod P)) (h3 : IsUnit (3 : ZMod P)) {D β U E : ℕ} (hD : IsUnit (D : ZMod P)) (hβ : β < D) (hUE : U ≤ E)
    (hEU : E < U + D) (hE : E % D = β) :
    ∑ j ∈ range U, (if j % D = β then Ring.inverse (j : ZMod P) ^ 2 else 0) =
      Ring.inverse (D : ZMod P) ^ 2 *
        (zeta ((E : ZMod P) * Ring.inverse (D : ZMod P)) -
          zeta ((β : ZMod P) * Ring.inverse (D : ZMod P))) := by
  rw [sum_range_ite_mod_ext _ hUE hEU hE]
  have hE' : E = β + D * (E / D) := by rw [← hE, Nat.mod_add_div]
  rw [hE', sum_range_ite_mod _ hβ]
  push_cast
  exact sum_class h2 h3 hD _ _

end Class

section Pair

theorem inverse_neg {M : Type*} [CommRing M] (x : M) : Ring.inverse (-x) = -Ring.inverse x := by
  by_cases hx : IsUnit x
  · have h1 : Ring.inverse (-x) * (-x) = 1 := Ring.inverse_mul_cancel _ hx.neg
    have h2 : x * Ring.inverse x = 1 := Ring.mul_inverse_cancel _ hx
    linear_combination (-Ring.inverse x) * h1 + (-Ring.inverse (-x)) * h2
  · rw [Ring.inverse_non_unit _ hx, Ring.inverse_non_unit _ (fun h => hx (by simpa using h.neg)),
      neg_zero]

variable {P : ℕ} [NeZero P] (h2 : IsUnit (2 : ZMod P)) (h3 : IsUnit (3 : ZMod P))

noncomputable def Zf (P d : ℕ) (z : ZMod d) : ZMod P :=
  zeta ((z.val : ZMod P) * Ring.inverse (d : ZMod P))

theorem Zf_neg (h2 : IsUnit (2 : ZMod P)) (h3 : IsUnit (3 : ZMod P)) {d : ℕ} [NeZero d] (hd : IsUnit (d : ZMod P)) (z : ZMod d) :
    Zf P d (-z) = -Zf P d z := by
  unfold Zf
  rw [ZMod.neg_val]
  split_ifs with hz
  · subst hz; simp [zeta_zero]
  · rw [Nat.cast_sub (ZMod.val_lt z).le, sub_mul, Ring.mul_inverse_cancel _ hd,
      zeta_one_sub h2 h3]

noncomputable def pt (T e d : ℕ) : ZMod d := (T : ZMod d) * (e : ZMod d)⁻¹

theorem mul_pt {T e d : ℕ} (h : Nat.Coprime e d) : (e : ZMod d) * pt T e d = T := by
  unfold pt; rw [mul_left_comm, ZMod.coe_mul_inv_eq_one e h, mul_one]

noncomputable def Ysum (P T e e' : ℕ) : ZMod P :=
  ∑ i ∈ range T, (if e ∣ i ∧ e' ∣ T - i then Ring.inverse (i : ZMod P) ^ 2 else 0)

theorem pair_sum (h2 : IsUnit (2 : ZMod P)) (h3 : IsUnit (3 : ZMod P)) {e e' T : ℕ} (he : 0 < e) (he' : 0 < e') (hcop : Nat.Coprime e e')
    (hue : IsUnit (e : ZMod P)) (hue' : IsUnit (e' : ZMod P)) (hT : (T : ZMod P) = 0) :
    (e : ZMod P) ^ 2 * (e' : ZMod P) ^ 2 * Ysum P T e e' =
      -(Zf P e (pt T e' e) + Zf P e' (pt T e e')) := by
  have : NeZero e := ⟨he.ne'⟩
  have : NeZero e' := ⟨he'.ne'⟩
  set t := pt T e e' with ht
  set t' := pt T e' e with ht'
  have htt : (e : ZMod e') * t = T := mul_pt hcop
  have htt' : (e' : ZMod e) * t' = T := mul_pt hcop.symm
  set α := e * t.val with hα
  set s₀ := (-t').val with hs₀
  set E := T + e' * s₀ with hE
  have hαD : α < e * e' := by
    have := ZMod.val_lt t
    rw [hα]; exact Nat.mul_lt_mul_of_pos_left this he
  have hαe : (α : ZMod e) = 0 := by
    rw [hα]; push_cast; rw [ZMod.natCast_self, zero_mul]
  have hαe' : (α : ZMod e') = T := by
    rw [hα]; push_cast; rw [ZMod.natCast_zmod_val, htt]
  have hcond : ∀ i, i < T → ((e ∣ i ∧ e' ∣ T - i) ↔ i % (e * e') = α) := by
    intro i hi
    have h1 : i % (e * e') = α ↔ i ≡ α [MOD e * e'] := by
      unfold Nat.ModEq; rw [Nat.mod_eq_of_lt hαD]
    rw [h1, ← Nat.modEq_and_modEq_iff_modEq_mul hcop, ← ZMod.natCast_eq_natCast_iff,
      ← ZMod.natCast_eq_natCast_iff, hαe, hαe', ← ZMod.natCast_eq_zero_iff i e,
      ← ZMod.natCast_eq_zero_iff (T - i) e', Nat.cast_sub hi.le, sub_eq_zero, eq_comm (a := (T : ZMod e'))]
  have hsum : Ysum P T e e' =
      ∑ i ∈ range T, (if i % (e * e') = α then Ring.inverse (i : ZMod P) ^ 2 else 0) := by
    refine sum_congr rfl fun i hi => ?_
    simp only [hcond i (mem_range.1 hi)]
  have hEe : (E : ZMod e) = (α : ZMod e) := by
    rw [hαe, hE]; push_cast; rw [hs₀, ZMod.natCast_zmod_val]; linear_combination -htt'
  have hEe' : (E : ZMod e') = (α : ZMod e') := by
    rw [hαe', hE]; push_cast; rw [ZMod.natCast_self]; ring
  have hEmod : E % (e * e') = α := by
    have : E ≡ α [MOD e * e'] := (Nat.modEq_and_modEq_iff_modEq_mul hcop).1
      ⟨(ZMod.natCast_eq_natCast_iff _ _ _).1 hEe, (ZMod.natCast_eq_natCast_iff _ _ _).1 hEe'⟩
    unfold Nat.ModEq at this; rw [this, Nat.mod_eq_of_lt hαD]
  have hEU : E < T + e * e' := by
    have : s₀ < e := ZMod.val_lt _
    have : e' * s₀ < e' * e := Nat.mul_lt_mul_of_pos_left this he'
    rw [hE]; rw [mul_comm e e']; omega
  have hD : IsUnit ((e * e' : ℕ) : ZMod P) := by rw [Nat.cast_mul]; exact hue.mul hue'
  rw [hsum, sum_class_nat h2 h3 hD hαD (by omega) hEU hEmod]
  have hee : (e : ZMod P) * Ring.inverse (e : ZMod P) = 1 := Ring.mul_inverse_cancel _ hue
  have hee' : (e' : ZMod P) * Ring.inverse (e' : ZMod P) = 1 := Ring.mul_inverse_cancel _ hue'
  have hinv : Ring.inverse (((e * e' : ℕ) : ZMod P)) =
      Ring.inverse (e' : ZMod P) * Ring.inverse (e : ZMod P) := by
    rw [Nat.cast_mul, Ring.mul_inverse_rev]
  have hEv : (E : ZMod P) * Ring.inverse ((e * e' : ℕ) : ZMod P) =
      (s₀ : ZMod P) * Ring.inverse (e : ZMod P) := by
    rw [hinv, hE]; push_cast; rw [hT]
    linear_combination ((s₀ : ZMod P) * Ring.inverse (e : ZMod P)) * hee'
  have hαv : (α : ZMod P) * Ring.inverse ((e * e' : ℕ) : ZMod P) =
      (t.val : ZMod P) * Ring.inverse (e' : ZMod P) := by
    rw [hinv, hα]; push_cast
    linear_combination ((t.val : ZMod P) * Ring.inverse (e' : ZMod P)) * hee
  rw [hEv, hαv, hinv]
  have hZ1 : zeta ((s₀ : ZMod P) * Ring.inverse (e : ZMod P)) = -Zf P e t' := by
    rw [← Zf_neg h2 h3 hue t']; rfl
  have hZ2 : zeta ((t.val : ZMod P) * Ring.inverse (e' : ZMod P)) = Zf P e' t := rfl
  rw [hZ1, hZ2]
  linear_combination (-(Zf P e t' + Zf P e' t) * ((e : ZMod P) * Ring.inverse (e : ZMod P) + 1) *
      ((e' : ZMod P) * Ring.inverse (e' : ZMod P)) ^ 2) * hee +
    (-(Zf P e t' + Zf P e' t) * ((e' : ZMod P) * Ring.inverse (e' : ZMod P) + 1)) * hee'

theorem diag_sum (h2 : IsUnit (2 : ZMod P)) (h3 : IsUnit (3 : ZMod P)) {e T : ℕ} (he : 0 < e) (hue : IsUnit (e : ZMod P)) (hT : (T : ZMod P) = 0) :
    Ysum P T e e = 0 := by
  unfold Ysum
  by_cases heT : e ∣ T
  · have hsum : ∑ i ∈ range T, (if e ∣ i ∧ e ∣ T - i then Ring.inverse (i : ZMod P) ^ 2 else 0) =
        ∑ i ∈ range T, (if i % e = 0 then Ring.inverse (i : ZMod P) ^ 2 else 0) := by
      refine sum_congr rfl fun i hi => ?_
      have : (e ∣ i ∧ e ∣ T - i) ↔ i % e = 0 := by
        rw [← Nat.dvd_iff_mod_eq_zero]
        exact ⟨fun h => h.1, fun h => ⟨h, Nat.dvd_sub heT h⟩⟩
      simp only [this]
    rw [hsum, sum_class_nat h2 h3 hue he le_rfl (by omega) (Nat.mod_eq_zero_of_dvd heT), hT]
    simp [zeta_zero]
  · refine sum_eq_zero fun i hi => ?_
    refine if_neg fun ⟨h1, h2'⟩ => ?_
    exact heT (by have := Nat.dvd_add h1 h2'; rwa [Nat.add_sub_cancel' (mem_range.1 hi).le] at this)

end Pair

section CoreSum

variable {P : ℕ} [NeZero P] (h2 : IsUnit (2 : ZMod P)) (h3 : IsUnit (3 : ZMod P))

noncomputable def cZ (P a b n : ℕ) : ZMod P :=
  (if a ∣ n then (a : ZMod P) ^ 2 else 0) + (if b ∣ n then (b : ZMod P) ^ 2 else 0) -
    (if a + b ∣ n then ((a + b : ℕ) : ZMod P) ^ 2 else 0)

theorem ite_mul_ite_mul {R : Type*} [CommRing R] (c c' : Prop) [Decidable c] [Decidable c']
    (x y z : R) :
    (if c then x else 0) * (if c' then y else 0) * z = x * y * (if c ∧ c' then z else 0) := by
  by_cases hc : c <;> by_cases hc' : c' <;> simp [hc, hc']

theorem cZ_mul {P : ℕ} (a b T i : ℕ) :
    cZ P a b i * cZ P a b (T - i) * Ring.inverse (i : ZMod P) ^ 2 =
      (a : ZMod P) ^ 2 * (a : ZMod P) ^ 2 *
          (if a ∣ i ∧ a ∣ T - i then Ring.inverse (i : ZMod P) ^ 2 else 0) +
        (a : ZMod P) ^ 2 * (b : ZMod P) ^ 2 *
          (if a ∣ i ∧ b ∣ T - i then Ring.inverse (i : ZMod P) ^ 2 else 0) -
        (a : ZMod P) ^ 2 * ((a + b : ℕ) : ZMod P) ^ 2 *
          (if a ∣ i ∧ a + b ∣ T - i then Ring.inverse (i : ZMod P) ^ 2 else 0) +
        (b : ZMod P) ^ 2 * (a : ZMod P) ^ 2 *
          (if b ∣ i ∧ a ∣ T - i then Ring.inverse (i : ZMod P) ^ 2 else 0) +
        (b : ZMod P) ^ 2 * (b : ZMod P) ^ 2 *
          (if b ∣ i ∧ b ∣ T - i then Ring.inverse (i : ZMod P) ^ 2 else 0) -
        (b : ZMod P) ^ 2 * ((a + b : ℕ) : ZMod P) ^ 2 *
          (if b ∣ i ∧ a + b ∣ T - i then Ring.inverse (i : ZMod P) ^ 2 else 0) -
        ((a + b : ℕ) : ZMod P) ^ 2 * (a : ZMod P) ^ 2 *
          (if a + b ∣ i ∧ a ∣ T - i then Ring.inverse (i : ZMod P) ^ 2 else 0) -
        ((a + b : ℕ) : ZMod P) ^ 2 * (b : ZMod P) ^ 2 *
          (if a + b ∣ i ∧ b ∣ T - i then Ring.inverse (i : ZMod P) ^ 2 else 0) +
        ((a + b : ℕ) : ZMod P) ^ 2 * ((a + b : ℕ) : ZMod P) ^ 2 *
          (if a + b ∣ i ∧ a + b ∣ T - i then Ring.inverse (i : ZMod P) ^ 2 else 0) := by
  simp only [← ite_mul_ite_mul]
  unfold cZ
  ring

noncomputable def Ycomb (P a b T : ℕ) : ZMod P :=
  (a : ZMod P) ^ 2 * (a : ZMod P) ^ 2 * Ysum P T a a +
    (a : ZMod P) ^ 2 * (b : ZMod P) ^ 2 * Ysum P T a b -
    (a : ZMod P) ^ 2 * ((a + b : ℕ) : ZMod P) ^ 2 * Ysum P T a (a + b) +
    (b : ZMod P) ^ 2 * (a : ZMod P) ^ 2 * Ysum P T b a +
    (b : ZMod P) ^ 2 * (b : ZMod P) ^ 2 * Ysum P T b b -
    (b : ZMod P) ^ 2 * ((a + b : ℕ) : ZMod P) ^ 2 * Ysum P T b (a + b) -
    ((a + b : ℕ) : ZMod P) ^ 2 * (a : ZMod P) ^ 2 * Ysum P T (a + b) a -
    ((a + b : ℕ) : ZMod P) ^ 2 * (b : ZMod P) ^ 2 * Ysum P T (a + b) b +
    ((a + b : ℕ) : ZMod P) ^ 2 * ((a + b : ℕ) : ZMod P) ^ 2 * Ysum P T (a + b) (a + b)

theorem sum_cZ_mul {P : ℕ} (a b T : ℕ) :
    ∑ i ∈ range T, cZ P a b i * cZ P a b (T - i) * Ring.inverse (i : ZMod P) ^ 2 =
      Ycomb P a b T := by
  simp only [cZ_mul, sum_add_distrib, sum_sub_distrib, ← mul_sum, Ycomb, Ysum]

theorem pt_add_left (T a b : ℕ) : pt T (a + b) a = pt T b a := by
  unfold pt; push_cast; rw [ZMod.natCast_self, zero_add]

theorem pt_add_right (T a b : ℕ) : pt T (a + b) b = pt T a b := by
  unfold pt; push_cast; rw [ZMod.natCast_self, add_zero]

theorem pt_neg {T a b : ℕ} (h : Nat.Coprime a (a + b)) :
    pt T b (a + b) = -pt T a (a + b) := by
  have hb : (b : ZMod (a + b)) = -(a : ZMod (a + b)) := by
    have : ((a + b : ℕ) : ZMod (a + b)) = 0 := ZMod.natCast_self _
    push_cast at this; linear_combination this
  unfold pt
  rw [hb]
  have hinv : (-(a : ZMod (a + b)))⁻¹ = -(a : ZMod (a + b))⁻¹ := by
    apply ZMod.inv_eq_of_mul_eq_one
    rw [neg_mul_neg]; exact ZMod.coe_mul_inv_eq_one a h
  rw [hinv]; ring

theorem Ycomb_eq_zero (h2 : IsUnit (2 : ZMod P)) (h3 : IsUnit (3 : ZMod P)) {a b T : ℕ} (ha : 0 < a) (hb : 0 < b) (hab : Nat.Coprime a b)
    (hua : IsUnit (a : ZMod P)) (hub : IsUnit (b : ZMod P))
    (hum : IsUnit ((a + b : ℕ) : ZMod P)) (hT : (T : ZMod P) = 0) :
    Ycomb P a b T = 0 := by
  have hm : 0 < a + b := by omega
  have ham : Nat.Coprime a (a + b) := Nat.coprime_self_add_right.2 hab
  have hbm : Nat.Coprime b (a + b) := Nat.coprime_add_self_right.2 hab.symm
  have : NeZero (a + b) := ⟨hm.ne'⟩
  unfold Ycomb
  rw [diag_sum h2 h3 ha hua hT, diag_sum h2 h3 hb hub hT, diag_sum h2 h3 hm hum hT,
    pair_sum h2 h3 ha hb hab hua hub hT, pair_sum h2 h3 hb ha hab.symm hub hua hT,
    pair_sum h2 h3 ha hm ham hua hum hT, pair_sum h2 h3 hm ha ham.symm hum hua hT,
    pair_sum h2 h3 hb hm hbm hub hum hT, pair_sum h2 h3 hm hb hbm.symm hum hub hT,
    pt_add_left, pt_add_right, pt_neg ham, Zf_neg h2 h3 hum]
  ring

theorem core_sum (h2 : IsUnit (2 : ZMod P)) (h3 : IsUnit (3 : ZMod P)) {a b T : ℕ} (ha : 0 < a) (hb : 0 < b) (hab : Nat.Coprime a b)
    (hua : IsUnit (a : ZMod P)) (hub : IsUnit (b : ZMod P))
    (hum : IsUnit ((a + b : ℕ) : ZMod P)) (hT : (T : ZMod P) = 0) :
    ∑ x ∈ antidiagonal T, (cZ P a b x.1 * Ring.inverse (x.1 : ZMod P)) *
      (cZ P a b x.2 * Ring.inverse (x.2 : ZMod P)) = 0 := by
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, sum_range_succ]
  simp only [hT, Ring.inverse_zero, mul_zero, zero_mul, add_zero]
  have e : ∀ i ∈ range T, cZ P a b i * Ring.inverse (i : ZMod P) *
      (cZ P a b (T - i) * Ring.inverse ((T - i : ℕ) : ZMod P)) =
      -(cZ P a b i * cZ P a b (T - i) * Ring.inverse (i : ZMod P) ^ 2) := by
    intro i hi
    rw [Nat.cast_sub (mem_range.1 hi).le, hT, zero_sub, inverse_neg]; ring
  rw [sum_congr rfl e, sum_neg_distrib, sum_cZ_mul, Ycomb_eq_zero h2 h3 ha hb hab hua hub hum hT,
    neg_zero]

end CoreSum

section

noncomputable section

variable {p : ℕ} [hp : Fact p.Prime]

theorem isUnit_natCast_padicInt_iff (i : ℕ) : IsUnit (i : ℤ_[p]) ↔ ¬ p ∣ i := by
  rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff,
    Nat.Prime.coprime_iff_not_dvd hp.out]

theorem isUnit_natCast_zmod_iff {e : ℕ} (he : 0 < e) (i : ℕ) :
    IsUnit (i : ZMod (p ^ e)) ↔ ¬ p ∣ i := by
  rw [ZMod.isUnit_iff_coprime, Nat.coprime_pow_right_iff he, Nat.coprime_comm,
    Nat.Prime.coprime_iff_not_dvd hp.out]

theorem inverse_eq_of_mul_eq_one {M : Type*} [CommMonoidWithZero M] {x y : M} (h : x * y = 1) :
    Ring.inverse x = y := by
  have hx : IsUnit x := IsUnit.of_mul_eq_one y h
  calc Ring.inverse x = Ring.inverse x * (x * y) := by rw [h, mul_one]
    _ = Ring.inverse x * x * y := by rw [mul_assoc]
    _ = y := by rw [Ring.inverse_mul_cancel _ hx, one_mul]

theorem toZModPow_inverse {e : ℕ} (he : 0 < e) (i : ℕ) :
    PadicInt.toZModPow e (Ring.inverse (i : ℤ_[p])) = Ring.inverse (i : ZMod (p ^ e)) := by
  by_cases h : p ∣ i
  · rw [Ring.inverse_non_unit _ (fun hu => (isUnit_natCast_padicInt_iff i).1 hu h),
      Ring.inverse_non_unit _ (fun hu => (isUnit_natCast_zmod_iff he i).1 hu h), map_zero]
  · have h1 : (i : ℤ_[p]) * Ring.inverse (i : ℤ_[p]) = 1 :=
      Ring.mul_inverse_cancel _ ((isUnit_natCast_padicInt_iff i).2 h)
    symm
    apply inverse_eq_of_mul_eq_one
    rw [← map_natCast (PadicInt.toZModPow e : ℤ_[p] →+* ZMod (p ^ e)) i, ← map_mul, h1, map_one]

theorem coe_inverse {i : ℕ} (h : ¬ p ∣ i) :
    ((Ring.inverse (i : ℤ_[p]) : ℤ_[p]) : ℚ_[p]) = (i : ℚ_[p])⁻¹ := by
  have h1 : (i : ℤ_[p]) * Ring.inverse (i : ℤ_[p]) = 1 :=
    Ring.mul_inverse_cancel _ ((isUnit_natCast_padicInt_iff i).2 h)
  apply eq_inv_of_mul_eq_one_right
  rw [← PadicInt.coe_natCast, ← PadicInt.coe_mul, h1, PadicInt.coe_one]

theorem coeff_Vof_mk {p : ℕ} (c : ℕ → ℤ) (n : ℕ) :
    coeff n (Vof p (mk fun n => (c n : ℚ))) = if p ∣ n then 0 else (c n : ℚ) / n := by
  rw [coeff_Vof]; simp

theorem PI_mk_int (c : ℕ → ℤ) : PI p (mk fun n => (c n : ℚ)) := fun n => by
  rw [coeff_mk]; exact padicNorm.of_int _

def μP (p : ℕ) [Fact p.Prime] (c : ℕ → ℤ) (i : ℕ) : ℤ_[p] :=
  (c i : ℤ_[p]) * Ring.inverse (i : ℤ_[p])

theorem coe_μP (c : ℕ → ℤ) (i : ℕ) :
    ((μP p c i : ℤ_[p]) : ℚ_[p]) = ((coeff i (Vof p (mk fun n => (c n : ℚ))) : ℚ) : ℚ_[p]) := by
  rw [coeff_Vof_mk, μP]
  by_cases h : p ∣ i
  · rw [Ring.inverse_non_unit _ (fun hu => (isUnit_natCast_padicInt_iff i).1 hu h)]
    simp [h]
  · rw [PadicInt.coe_mul, coe_inverse h]
    simp [h, div_eq_mul_inv]

theorem toZModPow_μP {e : ℕ} (he : 0 < e) (c : ℕ → ℤ) (i : ℕ) :
    PadicInt.toZModPow e (μP p c i) = (c i : ZMod (p ^ e)) * Ring.inverse (i : ZMod (p ^ e)) := by
  rw [μP, map_mul, toZModPow_inverse he, map_intCast]

theorem norm_coeff_Vof_sq_of_core (h5 : 5 ≤ p) (c : ℕ → ℤ) {T : ℕ} (hT0 : T ≠ 0)
    (hcore : ∀ e : ℕ, 0 < e → IsUnit (2 : ZMod (p ^ e)) → IsUnit (3 : ZMod (p ^ e)) →
      (T : ZMod (p ^ e)) = 0 →
      ∑ x ∈ antidiagonal T, ((c x.1 : ZMod (p ^ e)) * Ring.inverse (x.1 : ZMod (p ^ e))) *
        ((c x.2 : ZMod (p ^ e)) * Ring.inverse (x.2 : ZMod (p ^ e))) = 0) :
    padicNorm p (coeff T (Vof p (mk fun n => (c n : ℚ)) ^ 2)) ≤ padicNorm p (T : ℚ) := by
  set e := padicValNat p T with he_def
  rcases Nat.eq_zero_or_pos e with he0 | hepos
  · have hT1 : ¬ p ∣ T := by
      intro h
      have := one_le_padicValNat_of_dvd hT0 h
      omega
    rw [(padicNorm.nat_eq_one_iff T).2 hT1]
    exact (((PI_mk_int c).Vof).pow 2) T
  have hu : ∀ x : ℕ, ¬ p ∣ x → IsUnit (x : ZMod (p ^ e)) := fun x hx =>
    (isUnit_natCast_zmod_iff hepos x).2 hx
  have h2 : IsUnit (2 : ZMod (p ^ e)) := by
    have := hu 2 (fun h => by have := Nat.le_of_dvd (by norm_num) h; omega)
    rwa [Nat.cast_ofNat] at this
  have h3 : IsUnit (3 : ZMod (p ^ e)) := by
    have := hu 3 (fun h => by have := Nat.le_of_dvd (by norm_num) h; omega)
    rwa [Nat.cast_ofNat] at this
  have hT : (T : ZMod (p ^ e)) = 0 := by
    rw [ZMod.natCast_eq_zero_iff]; exact pow_padicValNat_dvd
  set S : ℤ_[p] := ∑ x ∈ antidiagonal T, μP p c x.1 * μP p c x.2 with hS
  have hS1 : PadicInt.toZModPow e S = 0 := by
    rw [hS, map_sum]
    simp only [map_mul, toZModPow_μP hepos]
    exact hcore e hepos h2 h3 hT
  have hS2 : (S : ℚ_[p]) = ((coeff T (Vof p (mk fun n => (c n : ℚ)) ^ 2) : ℚ) : ℚ_[p]) := by
    rw [hS, sq, coeff_mul, Rat.cast_sum]
    rw [show ((∑ x ∈ antidiagonal T, μP p c x.1 * μP p c x.2 : ℤ_[p]) : ℚ_[p]) =
      PadicInt.Coe.ringHom (∑ x ∈ antidiagonal T, μP p c x.1 * μP p c x.2) from rfl,
      map_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [map_mul, Rat.cast_mul]
    exact congrArg₂ _ (coe_μP c x.1) (coe_μP c x.2)
  have hmem : S ∈ Ideal.span {(p : ℤ_[p]) ^ e} := by
    rw [← PadicInt.ker_toZModPow]; exact hS1
  have hnorm := (PadicInt.norm_le_pow_iff_mem_span_pow S e).2 hmem
  rw [PadicInt.norm_def, hS2, Padic.eq_padicNorm] at hnorm
  have hTn : padicNorm p (T : ℚ) = (p : ℚ) ^ (-(e : ℤ)) := by
    rw [padicNorm.eq_zpow_of_nonzero (by exact_mod_cast hT0), padicValRat.of_nat]
  rw [hTn]
  have h' : ((padicNorm p (coeff T (Vof p (mk fun n => (c n : ℚ)) ^ 2)) : ℚ) : ℝ) ≤
      (((p : ℚ) ^ (-(e : ℤ)) : ℚ) : ℝ) := by
    rw [Rat.cast_zpow, Rat.cast_natCast]; exact hnorm
  exact_mod_cast h'

theorem Vof_gmul {g : ℕ} (hg : 0 < g) (hpg : ¬ p ∣ g) (c c' : ℕ → ℤ)
    (h1 : ∀ n, c (g * n) = (g : ℤ) ^ 2 * c' n) (h0 : ∀ n, ¬ g ∣ n → c n = 0) :
    Vof p (mk fun n => (c n : ℚ)) = C (g : ℚ) * expand g hg.ne' (Vof p (mk fun n => (c' n : ℚ))) := by
  ext n
  rw [coeff_C_mul, coeff_expand, coeff_Vof_mk]
  split_ifs with hn hgn hgn
  · obtain ⟨m, rfl⟩ := hgn
    rw [Nat.mul_div_cancel_left _ hg, coeff_Vof_mk]
    have : p ∣ m := ((Nat.Prime.dvd_mul hp.out).1 hn).resolve_left hpg
    simp [this]
  · simp
  · obtain ⟨m, rfl⟩ := hgn
    rw [Nat.mul_div_cancel_left _ hg, coeff_Vof_mk]
    have hm : ¬ p ∣ m := fun h => hn (dvd_mul_of_dvd_right h g)
    rw [if_neg hm, h1]
    have hm0 : (m : ℚ) ≠ 0 := by
      have : m ≠ 0 := by rintro rfl; exact hm (dvd_zero p)
      exact_mod_cast this
    have hg' : (g : ℚ) ≠ 0 := by exact_mod_cast hg.ne'
    push_cast
    field_simp
  · rw [h0 n hgn]; simp

theorem norm_coeff_Vof_sq_gmul {g : ℕ} (hg : 0 < g) (hpg : ¬ p ∣ g) (c c' : ℕ → ℤ)
    (h1 : ∀ n, c (g * n) = (g : ℤ) ^ 2 * c' n) (h0 : ∀ n, ¬ g ∣ n → c n = 0)
    (h' : ∀ T, T ≠ 0 →
      padicNorm p (coeff T (Vof p (mk fun n => (c' n : ℚ)) ^ 2)) ≤ padicNorm p (T : ℚ))
    {T : ℕ} (hT0 : T ≠ 0) :
    padicNorm p (coeff T (Vof p (mk fun n => (c n : ℚ)) ^ 2)) ≤ padicNorm p (T : ℚ) := by
  rw [Vof_gmul hg hpg c c' h1 h0, mul_pow, ← map_pow, ← map_pow, coeff_C_mul, coeff_expand]
  split_ifs with hgT
  · obtain ⟨T', rfl⟩ := hgT
    rw [Nat.mul_div_cancel_left _ hg]
    have hT' : T' ≠ 0 := by rintro rfl; simp at hT0
    have hgn : padicNorm p (g : ℚ) = 1 := (padicNorm.nat_eq_one_iff g).2 hpg
    rw [padicNorm.mul, padicNorm_pow, hgn, one_pow, one_mul]
    push_cast
    rw [padicNorm.mul, hgn, one_mul]
    exact h' T' hT'
  · rw [mul_zero, padicNorm.zero]; exact padicNorm.nonneg _

theorem quad_of_norm {V : ℚ⟦X⟧} (hV : X ∣ V)
    (h : ∀ T, T ≠ 0 → padicNorm p (coeff T (V ^ 2)) ≤ padicNorm p (T : ℚ)) (j : ℕ) :
    padicNorm p (coeff (p * j) (V ^ 2)) ≤ padicNorm p p * padicNorm p j := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · have : coeff (p * 0) (V ^ 2) = 0 := by
      rw [mul_zero]; obtain ⟨W, hW⟩ := hV; rw [hW]; simp
    rw [this]; simp
  · have := h (p * j) (Nat.mul_ne_zero hp0 hj.ne')
    rwa [Nat.cast_mul, padicNorm.mul] at this

theorem cf_cast {p : ℕ} {e : ℕ} (a b i : ℕ) :
    ((cf a b i : ℤ) : ZMod (p ^ e)) * Ring.inverse (i : ZMod (p ^ e)) =
      cZ (p ^ e) a b i * Ring.inverse (i : ZMod (p ^ e)) := by
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · simp
  · congr 1
    simp only [cf, cZ, hi.ne', ite_false]
    split_ifs <;> push_cast <;> ring

theorem norm_coeff_Mred_sq_coprime (h5 : 5 ≤ p) {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hab : Nat.Coprime a b) (hpa : ¬ p ∣ a) (hpb : ¬ p ∣ b) (hpm : ¬ p ∣ a + b) {T : ℕ}
    (hT0 : T ≠ 0) :
    padicNorm p (coeff T (Mred p a b ^ 2)) ≤ padicNorm p (T : ℚ) := by
  refine norm_coeff_Vof_sq_of_core h5 (cf a b) hT0 fun e he h2 h3 hT => ?_
  have hu : ∀ x : ℕ, ¬ p ∣ x → IsUnit (x : ZMod (p ^ e)) := fun x hx =>
    (isUnit_natCast_zmod_iff he x).2 hx
  simp only [cf_cast]
  exact core_sum h2 h3 ha hb hab (hu a hpa) (hu b hpb) (hu (a + b) hpm) hT

theorem cf_gmul {g : ℕ} (hg : 0 < g) (a b n : ℕ) :
    cf (g * a) (g * b) (g * n) = (g : ℤ) ^ 2 * cf a b n := by
  unfold cf
  simp only [mul_eq_zero, hg.ne', false_or, Nat.mul_dvd_mul_iff_left hg,
    show g * a + g * b = g * (a + b) by ring]
  split_ifs <;> push_cast <;> ring

theorem cf_gmul_of_not_dvd {g a b n : ℕ} (h : ¬ g ∣ n) : cf (g * a) (g * b) n = 0 := by
  unfold cf
  have h1 : ¬ g * a ∣ n := fun h' => h (dvd_trans (dvd_mul_right g a) h')
  have h2 : ¬ g * b ∣ n := fun h' => h (dvd_trans (dvd_mul_right g b) h')
  have h3 : ¬ g * a + g * b ∣ n := fun h' => h (dvd_trans (by
    rw [show g * a + g * b = g * (a + b) by ring]; exact dvd_mul_right g _) h')
  simp [h1, h2, h3]

theorem norm_coeff_Mred_sq (h5 : 5 ≤ p) {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hpa : ¬ p ∣ a)
    (hpb : ¬ p ∣ b) (hpm : ¬ p ∣ a + b) {T : ℕ} (hT0 : T ≠ 0) :
    padicNorm p (coeff T (Mred p a b ^ 2)) ≤ padicNorm p (T : ℚ) := by
  set g := Nat.gcd a b with hg_def
  have hg : 0 < g := Nat.gcd_pos_of_pos_left b ha
  have hga : a = g * (a / g) := (Nat.mul_div_cancel' (Nat.gcd_dvd_left a b)).symm
  have hgb : b = g * (b / g) := (Nat.mul_div_cancel' (Nat.gcd_dvd_right a b)).symm
  have hpg : ¬ p ∣ g := fun h => hpa (dvd_trans h (Nat.gcd_dvd_left a b))
  have ha0 : 0 < a / g := Nat.div_pos (Nat.le_of_dvd ha (Nat.gcd_dvd_left a b)) hg
  have hb0 : 0 < b / g := Nat.div_pos (Nat.le_of_dvd hb (Nat.gcd_dvd_right a b)) hg
  have hcop : Nat.Coprime (a / g) (b / g) := Nat.coprime_div_gcd_div_gcd hg
  have hpa0 : ¬ p ∣ a / g := fun h => hpa (hga ▸ dvd_mul_of_dvd_right h g)
  have hpb0 : ¬ p ∣ b / g := fun h => hpb (hgb ▸ dvd_mul_of_dvd_right h g)
  have hpm0 : ¬ p ∣ a / g + b / g := fun h => hpm (by
    rw [hga, hgb, show g * (a / g) + g * (b / g) = g * (a / g + b / g) by ring]
    exact dvd_mul_of_dvd_right h g)
  rw [Mred, hga, hgb]
  exact norm_coeff_Vof_sq_gmul hg hpg _ _ (cf_gmul hg (a / g) (b / g))
    (fun n hn => cf_gmul_of_not_dvd hn)
    (fun T' hT' => norm_coeff_Mred_sq_coprime h5 ha0 hb0 hcop hpa0 hpb0 hpm0 hT') hT0

end

end

section

variable {p : ℕ} [hp : Fact p.Prime]

theorem cubicHyp_f (h5 : 5 ≤ p) {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hpa : ¬ p ∣ a)
    (hpb : ¬ p ∣ b) (hpm : ¬ p ∣ a + b) : CubicHyp p (fU a b) (Λq a b) := by
  exact ⟨constantCoeff_f a b, hasLD_fU ha hb, PI_Λq a b, coeff_Λq_mul hpa hpb hpm,
    quad_of_norm (X_dvd_Vof p _) (fun _ hT => norm_coeff_Mred_sq h5 ha hb hpa hpb hpm hT)⟩

end

theorem u_eq_uF (a b r : ℕ) (s : ℤ) (N : ℕ) : u a b r s N = uF (fU a b) r s N := by
  rw [u, zpowSeries_f]; rfl

theorem u_tower (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (p : ℕ) (hp : p.Prime) (h5 : 5 ≤ p)
    (hpab : ¬ p ∣ a * b * (a + b)) (r : ℕ) (hr : 0 < r) (s : ℤ) (n k : ℕ) (hn : 0 < n)
    (hk : 0 < k) :
    (p : ℤ) ^ (3 * k) ∣ u a b r s (n * p ^ k) - u a b r s (n * p ^ (k - 1)) := by
  have := Fact.mk hp
  have _ := hr
  have _ := hn
  have hpa : ¬ p ∣ a := fun h => hpab (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left h b) _)
  have hpb : ¬ p ∣ b := fun h => hpab (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right h a) _)
  have hpm : ¬ p ∣ a + b := fun h => hpab (dvd_mul_of_dvd_right h _)
  rw [u_eq_uF, u_eq_uF]
  exact uF_tower h5 (cubicHyp_f h5 ha hb hpa hpb hpm) r s n k hk

theorem not_dvd_of_pos_lt {p c : ℕ} (hc : 0 < c) (h : c < p) : ¬ p ∣ c :=
  Nat.not_dvd_of_pos_of_lt hc h

theorem f372211_eq : f372211 = f 2 3 := rfl

theorem f372212_eq : f372212 = f 2 5 := rfl

theorem f372213_eq : f372213 = f 3 4 := rfl

theorem A_eq (F : PowerSeries ℤ) (n : ℕ) :
    coeff n (F ^ n) = coeff (1 * n) (zpowSeries F (1 * (n : ℤ))) := by
  simp [zpowSeries]

theorem A372211_eq (n : ℕ) : A372211 n = u372211 1 1 n := by rw [u372211, ← A_eq]; rfl

theorem A372212_eq (n : ℕ) : A372212 n = u372212 1 1 n := by rw [u372212, ← A_eq]; rfl

theorem A372213_eq (n : ℕ) : A372213 n = u372213 1 1 n := by rw [u372213, ← A_eq]; rfl

theorem not_dvd_prod {p a b : ℕ} (hp : p.Prime) (ha : ¬ p ∣ a) (hb : ¬ p ∣ b)
    (hm : ¬ p ∣ a + b) : ¬ p ∣ a * b * (a + b) := by
  intro h
  rcases (Nat.Prime.dvd_mul hp).1 h with h | h
  · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
    · exact ha h
    · exact hb h
  · exact hm h

theorem u372211_tower (p : ℕ) (hp : p.Prime) (h7 : 7 ≤ p) (r : ℕ) (hr : 0 < r) (s : ℤ)
    (n k : ℕ) (hn : 0 < n) (hk : 0 < k) :
    (p : ℤ) ^ (3 * k) ∣ u372211 r s (n * p ^ k) - u372211 r s (n * p ^ (k - 1)) :=
  u_tower 2 3 (by norm_num) (by norm_num) p hp (by omega)
    (not_dvd_prod hp (not_dvd_of_pos_lt (by norm_num) (by omega))
      (not_dvd_of_pos_lt (by norm_num) (by omega)) (not_dvd_of_pos_lt (by norm_num) (by omega)))
    r hr s n k hn hk

theorem a372211_tower (p : ℕ) (hp : p.Prime) (h7 : 7 ≤ p) (n k : ℕ) (hn : 0 < n) (hk : 0 < k) :
    (p : ℤ) ^ (3 * k) ∣ A372211 (n * p ^ k) - A372211 (n * p ^ (k - 1)) := by
  rw [A372211_eq, A372211_eq]
  exact u372211_tower p hp h7 1 one_pos 1 n k hn hk

theorem u372212_tower (p : ℕ) (hp : p.Prime) (h11 : 11 ≤ p) (r : ℕ) (hr : 0 < r) (s : ℤ)
    (n k : ℕ) (hn : 0 < n) (hk : 0 < k) :
    (p : ℤ) ^ (3 * k) ∣ u372212 r s (n * p ^ k) - u372212 r s (n * p ^ (k - 1)) :=
  u_tower 2 5 (by norm_num) (by norm_num) p hp (by omega)
    (not_dvd_prod hp (not_dvd_of_pos_lt (by norm_num) (by omega))
      (not_dvd_of_pos_lt (by norm_num) (by omega)) (not_dvd_of_pos_lt (by norm_num) (by omega)))
    r hr s n k hn hk

theorem a372212_tower (p : ℕ) (hp : p.Prime) (h11 : 11 ≤ p) (n k : ℕ) (hn : 0 < n)
    (hk : 0 < k) :
    (p : ℤ) ^ (3 * k) ∣ A372212 (n * p ^ k) - A372212 (n * p ^ (k - 1)) := by
  rw [A372212_eq, A372212_eq]
  exact u372212_tower p hp h11 1 one_pos 1 n k hn hk

theorem not_dvd_seven {p : ℕ} (hp : p.Prime) (h7 : p ≠ 7) : ¬ p ∣ 3 + 4 := fun h =>
  h7 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_seven).1 h)

theorem u372213_tower (p : ℕ) (hp : p.Prime) (h5 : 5 ≤ p) (h7 : p ≠ 7) (r : ℕ) (hr : 0 < r)
    (s : ℤ) (n k : ℕ) (hn : 0 < n) (hk : 0 < k) :
    (p : ℤ) ^ (3 * k) ∣ u372213 r s (n * p ^ k) - u372213 r s (n * p ^ (k - 1)) :=
  u_tower 3 4 (by norm_num) (by norm_num) p hp h5
    (not_dvd_prod hp (not_dvd_of_pos_lt (by norm_num) (by omega))
      (not_dvd_of_pos_lt (by norm_num) (by omega)) (not_dvd_seven hp h7))
    r hr s n k hn hk

theorem a372213_tower (p : ℕ) (hp : p.Prime) (h5 : 5 ≤ p) (h7 : p ≠ 7) (n k : ℕ) (hn : 0 < n)
    (hk : 0 < k) :
    (p : ℤ) ^ (3 * k) ∣ A372213 (n * p ^ k) - A372213 (n * p ^ (k - 1)) := by
  rw [A372213_eq, A372213_eq]
  exact u372213_tower p hp h5 h7 1 one_pos 1 n k hn hk

end OeisA372211

end

open PowerSeries

lemma f08_map_invOfUnit (F : PowerSeries ℤ)
    (hF : constantCoeff F = 1) :
    map (Int.castRingHom ℚ) (invOfUnit F 1) =
      (map (Int.castRingHom ℚ) F)⁻¹ := by
  apply (eq_inv_iff_mul_eq_one (by
    change ((constantCoeff F : ℤ) : ℚ) ≠ 0
    rw [hF]
    norm_num :
    constantCoeff (map (Int.castRingHom ℚ) F) ≠ 0)).2
  rw [← map_mul, invOfUnit_mul F 1 (by simpa using hF), map_one]

lemma f08_map_f372212 :
    map (Int.castRingHom ℚ) OeisA372211.f372212 = OMA.S_oeis_a372212.f := by
  unfold OeisA372211.f372212 OMA.S_oeis_a372212.f
  rw [map_mul, map_mul, map_pow, map_pow, map_pow,
    f08_map_invOfUnit (1 - X ^ 2) (by simp),
    f08_map_invOfUnit (1 - X ^ 5) (by simp)]
  simp only [map_sub, map_one, map_pow, map_X]
  apply (eq_mul_inv_iff_mul_eq (by simp)).2
  have h2 : (1 - X ^ 2 : PowerSeries ℚ)⁻¹ * (1 - X ^ 2) = 1 :=
    PowerSeries.inv_mul_cancel _ (by simp)
  have h5 : (1 - X ^ 5 : PowerSeries ℚ)⁻¹ * (1 - X ^ 5) = 1 :=
    PowerSeries.inv_mul_cancel _ (by simp)
  calc
    _ = (1 - X ^ 7 : PowerSeries ℚ) ^ 7 *
        (((1 - X ^ 2)⁻¹ * (1 - X ^ 2)) ^ 2) *
        (((1 - X ^ 5)⁻¹ * (1 - X ^ 5)) ^ 5) := by simp only [mul_pow]; ac_rfl
    _ = _ := by rw [h2, h5]; simp

lemma f08_coeff_a372212 (n : ℕ) :
    (OeisA372211.A372212 n : ℚ) = OMA.S_oeis_a372212.a n := by
  unfold OeisA372211.A372212 OMA.S_oeis_a372212.a
  rw [← f08_map_f372212, ← map_pow, coeff_map]
  rfl

theorem OMA.solution : type_of% @OMA.S_oeis_a372212.main := by
  intro p hp h11 n r hn hr
  obtain ⟨z, hz⟩ := OeisA372211.a372212_tower p hp h11 n r hn hr
  refine ⟨z, ?_⟩
  rw [← f08_coeff_a372212, ← f08_coeff_a372212]
  exact_mod_cast hz
