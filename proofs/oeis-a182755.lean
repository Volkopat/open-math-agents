import OMAStatements.S_oeis_a182755

-- Problem: A182755: Expansion of (1+35*x)/(1-90*x^2).
-- Upstream: formal-conjectures statements/oeis-a182755.lean:0 (declaration OMA.S_oeis_a182755.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: a(2k+1) = 90^k and a(2k+2) = 35*90^k. Put c = 90^k. For n odd the claim is about
-- c*(35c)*h | (36c)(c+h)(35c+h) with 35c < h < 90c; write h = pg, c = qg with p, q coprime: then
-- 35qp | 36(q+p)(35q+p), so q | 36 and p | 1260, and a kernel check of these finitely many
-- pairs finds none. For n even (35c, 90c, 35c < 90c < h < 3150c) the same gives
-- 126qp | 5(35q+p)(90q+p), q | 5, p | 15750, and again no pair. At h = a(n) the quotient is 130.

open OMA.S_oeis_a182755 in
theorem rec182755 (n : ℕ) : a (n + 3) = 90 * a (n + 1) := rfl

open OMA.S_oeis_a182755 in
theorem odd182755 (k : ℕ) : a (2 * k + 1) = 90 ^ k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) + 1 = 2 * k + 3 by ring, rec182755, ih]
    ring

open OMA.S_oeis_a182755 in
theorem even182755 (k : ℕ) : a (2 * k + 2) = 35 * 90 ^ k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) + 2 = 2 * k + 1 + 3 by ring, rec182755,
      show 2 * k + 1 + 1 = 2 * k + 2 by ring, ih]
    ring

theorem finA182755 : ∀ q ∈ Nat.divisors 36, ∀ p ∈ Nat.divisors 1260,
    35 * q < p → p < 90 * q → ¬ (35 * q * p ∣ 36 * (q + p) * (35 * q + p)) := by
  decide +kernel

theorem finB182755 : ∀ q ∈ Nat.divisors 5, ∀ p ∈ Nat.divisors 15750,
    90 * q < p → p < 3150 * q → ¬ (126 * q * p ∣ 5 * (35 * q + p) * (90 * q + p)) := by
  decide +kernel

theorem keyA182755 (c h : ℕ) (hc : 0 < c) (h1 : 35 * c < h) (h2 : h < 90 * c)
    (hd : c * (35 * c) * h ∣ (c + 35 * c) * (c + h) * (35 * c + h)) : False := by
  obtain ⟨g, p, q, hg, hcop, rfl, rfl⟩ :
      ∃ g p q : ℕ, 0 < g ∧ Nat.Coprime p q ∧ h = p * g ∧ c = q * g :=
    ⟨Nat.gcd h c, h / Nat.gcd h c, c / Nat.gcd h c, Nat.gcd_pos_of_pos_right h hc,
      Nat.coprime_div_gcd_div_gcd (Nat.gcd_pos_of_pos_right h hc),
      (Nat.div_mul_cancel (Nat.gcd_dvd_left h c)).symm,
      (Nat.div_mul_cancel (Nat.gcd_dvd_right h c)).symm⟩
  have hq0 : 0 < q := Nat.pos_of_ne_zero (fun h0 => by simp [h0] at hc)
  have hl1 : 35 * q < p := by
    by_contra hh
    have h5 := Nat.mul_le_mul (not_lt.mp hh) (le_refl g)
    linarith
  have hl2 : p < 90 * q := by
    by_contra hh
    have h5 := Nat.mul_le_mul (not_lt.mp hh) (le_refl g)
    linarith
  have e1 : q * g * (35 * (q * g)) * (p * g) = (35 * q * p) * (q * g ^ 3) := by ring
  have e2 : (q * g + 35 * (q * g)) * (q * g + p * g) * (35 * (q * g) + p * g) =
      (36 * (q + p) * (35 * q + p)) * (q * g ^ 3) := by ring
  rw [e1, e2] at hd
  have hd' : 35 * q * p ∣ 36 * (q + p) * (35 * q + p) :=
    Nat.dvd_of_mul_dvd_mul_right (Nat.mul_pos hq0 (pow_pos hg 3)) hd
  have hq1 : q ∣ 36 * p ^ 2 := by
    have hq35 : q ∣ 35 * q * p := ⟨35 * p, by ring⟩
    have h3 : q ∣ 36 * (q + p) * (35 * q + p) := dvd_trans hq35 hd'
    rw [show 36 * (q + p) * (35 * q + p) = q * (1260 * q + 1296 * p) + 36 * p ^ 2 by ring] at h3
    exact (Nat.dvd_add_right (dvd_mul_right q _)).mp h3
  have hp1 : p ∣ 1260 * q ^ 2 := by
    have hp35 : p ∣ 35 * q * p := ⟨35 * q, by ring⟩
    have h3 : p ∣ 36 * (q + p) * (35 * q + p) := dvd_trans hp35 hd'
    rw [show 36 * (q + p) * (35 * q + p) = p * (1296 * q + 36 * p) + 1260 * q ^ 2 by ring] at h3
    exact (Nat.dvd_add_right (dvd_mul_right p _)).mp h3
  have hq36 : q ∣ 36 := (Nat.Coprime.pow_right 2 hcop.symm).dvd_of_dvd_mul_right hq1
  have hp1260 : p ∣ 1260 := (Nat.Coprime.pow_right 2 hcop).dvd_of_dvd_mul_right hp1
  exact finA182755 q (Nat.mem_divisors.mpr ⟨hq36, by norm_num⟩) p
    (Nat.mem_divisors.mpr ⟨hp1260, by norm_num⟩) hl1 hl2 hd'

theorem keyB182755 (c h : ℕ) (hc : 0 < c) (h1 : 90 * c < h) (h2 : h < 90 * (35 * c))
    (hd : 35 * c * (90 * c) * h ∣ (35 * c + 90 * c) * (35 * c + h) * (90 * c + h)) : False := by
  obtain ⟨g, p, q, hg, hcop, rfl, rfl⟩ :
      ∃ g p q : ℕ, 0 < g ∧ Nat.Coprime p q ∧ h = p * g ∧ c = q * g :=
    ⟨Nat.gcd h c, h / Nat.gcd h c, c / Nat.gcd h c, Nat.gcd_pos_of_pos_right h hc,
      Nat.coprime_div_gcd_div_gcd (Nat.gcd_pos_of_pos_right h hc),
      (Nat.div_mul_cancel (Nat.gcd_dvd_left h c)).symm,
      (Nat.div_mul_cancel (Nat.gcd_dvd_right h c)).symm⟩
  have hq0 : 0 < q := Nat.pos_of_ne_zero (fun h0 => by simp [h0] at hc)
  have hl1 : 90 * q < p := by
    by_contra hh
    have h5 := Nat.mul_le_mul (not_lt.mp hh) (le_refl g)
    linarith
  have hl2 : p < 3150 * q := by
    by_contra hh
    have h5 := Nat.mul_le_mul (not_lt.mp hh) (le_refl g)
    linarith
  have e1 : 35 * (q * g) * (90 * (q * g)) * (p * g) = (126 * q * p) * (25 * q * g ^ 3) := by ring
  have e2 : (35 * (q * g) + 90 * (q * g)) * (35 * (q * g) + p * g) * (90 * (q * g) + p * g) =
      (5 * (35 * q + p) * (90 * q + p)) * (25 * q * g ^ 3) := by ring
  rw [e1, e2] at hd
  have hd' : 126 * q * p ∣ 5 * (35 * q + p) * (90 * q + p) :=
    Nat.dvd_of_mul_dvd_mul_right (Nat.mul_pos (Nat.mul_pos (by norm_num) hq0) (pow_pos hg 3)) hd
  have hq1 : q ∣ 5 * p ^ 2 := by
    have hq35 : q ∣ 126 * q * p := ⟨126 * p, by ring⟩
    have h3 : q ∣ 5 * (35 * q + p) * (90 * q + p) := dvd_trans hq35 hd'
    rw [show 5 * (35 * q + p) * (90 * q + p) = q * (15750 * q + 625 * p) + 5 * p ^ 2 by ring] at h3
    exact (Nat.dvd_add_right (dvd_mul_right q _)).mp h3
  have hp1 : p ∣ 15750 * q ^ 2 := by
    have hp35 : p ∣ 126 * q * p := ⟨126 * q, by ring⟩
    have h3 : p ∣ 5 * (35 * q + p) * (90 * q + p) := dvd_trans hp35 hd'
    rw [show 5 * (35 * q + p) * (90 * q + p) = p * (625 * q + 5 * p) + 15750 * q ^ 2 by ring] at h3
    exact (Nat.dvd_add_right (dvd_mul_right p _)).mp h3
  have hq5 : q ∣ 5 := (Nat.Coprime.pow_right 2 hcop.symm).dvd_of_dvd_mul_right hq1
  have hp15750 : p ∣ 15750 := (Nat.Coprime.pow_right 2 hcop).dvd_of_dvd_mul_right hp1
  exact finB182755 q (Nat.mem_divisors.mpr ⟨hq5, by norm_num⟩) p
    (Nat.mem_divisors.mpr ⟨hp15750, by norm_num⟩) hl1 hl2 hd'

theorem caseA182755 (c : ℕ) (hc : 0 < c) :
    IsLeast {h : ℕ | 35 * c < h ∧
        c * (35 * c) * h ∣ (c + 35 * c) * (c + h) * (35 * c + h)} (90 * c) ∧
    (c + 35 * c) * (c + 90 * c) * (35 * c + 90 * c) = 130 * (c * (35 * c) * (90 * c)) := by
  refine ⟨⟨⟨by omega, 130, by ring⟩, ?_⟩, by ring⟩
  intro h hh
  obtain ⟨hlt, hdvd⟩ := hh
  by_contra hcon
  exact keyA182755 c h hc hlt (not_le.mp hcon) hdvd

theorem caseB182755 (c : ℕ) (hc : 0 < c) :
    IsLeast {h : ℕ | 90 * c < h ∧
        35 * c * (90 * c) * h ∣ (35 * c + 90 * c) * (35 * c + h) * (90 * c + h)} (90 * (35 * c)) ∧
    (35 * c + 90 * c) * (35 * c + 90 * (35 * c)) * (90 * c + 90 * (35 * c)) =
      130 * (35 * c * (90 * c) * (90 * (35 * c))) := by
  refine ⟨⟨⟨by omega, 130, by ring⟩, ?_⟩, by ring⟩
  intro h hh
  obtain ⟨hlt, hdvd⟩ := hh
  by_contra hcon
  exact keyB182755 c h hc hlt (not_le.mp hcon) hdvd

open OMA.S_oeis_a182755 in
theorem OMA.solution : type_of% @OMA.S_oeis_a182755.main := by
  intro n hn
  obtain ⟨k, rfl | rfl⟩ : ∃ k, n = 2 * k + 3 ∨ n = 2 * k + 4 := ⟨(n - 3) / 2, by omega⟩
  · have e3 : a (2 * k + 3) = 90 * 90 ^ k := by rw [rec182755, odd182755]
    rw [show 2 * k + 3 - 1 = 2 * k + 2 by omega, show 2 * k + 3 - 2 = 2 * k + 1 by omega, e3,
      even182755, odd182755]
    exact caseA182755 (90 ^ k) (pow_pos (by norm_num) k)
  · have e3 : a (2 * k + 3) = 90 * 90 ^ k := by rw [rec182755, odd182755]
    have e4 : a (2 * k + 4) = 90 * (35 * 90 ^ k) := by
      rw [show 2 * k + 4 = 2 * k + 1 + 3 by ring, rec182755,
        show 2 * k + 1 + 1 = 2 * k + 2 by ring, even182755]
    rw [show 2 * k + 4 - 1 = 2 * k + 3 by omega, show 2 * k + 4 - 2 = 2 * k + 2 by omega, e3, e4,
      even182755]
    exact caseB182755 (90 ^ k) (pow_pos (by norm_num) k)
