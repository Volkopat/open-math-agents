import OMAStatements.S_oeis_a256481

namespace OMA.S_oeis_a256481




def n0 : ℕ := 48030541312027842367346989018029079247911647283793344377427646539978957958940781

def Cs : List ℕ := [3, 7, 11, 13, 19, 31, 37, 41, 61, 73, 101, 137, 211, 241, 271, 2161, 3541, 9091,
  9901, 27961, 52579, 238681, 333667, 2906161, 3762091, 39526741]

theorem R_add (i L : ℕ) : R (i + L) = 10 ^ L * R i + R L := by
  induction L with
  | zero => simp [R]
  | succ L ih =>
    rw [show i + (L + 1) = (i + L) + 1 by ring, R, ih, R, pow_succ]
    ring

set_option maxRecDepth 100000 in
theorem period_facts : ∀ C ∈ Cs, 10 ^ 360 % C = 1 ∧ R 360 % C = 0 := by
  decide +kernel

theorem Cs_bounds : ∀ C ∈ Cs, 1 < C ∧ C < 10 * n0 := by
  decide +kernel

theorem periodic (d i C : ℕ) (hC : C ∈ Cs) : app n0 d (i + 360) % C = app n0 d i % C := by
  obtain ⟨h1, h2⟩ := period_facts C hC
  have h10 : 10 ^ 360 ≡ 1 [MOD C] := by
    unfold Nat.ModEq
    rw [h1]
    exact (Nat.mod_eq_of_lt (Cs_bounds C hC).1).symm
  have hR : R 360 ≡ 0 [MOD C] := by
    unfold Nat.ModEq
    rw [h2, Nat.zero_mod]
  have e : app n0 d (i + 360) = n0 * 10 ^ i * 10 ^ 360 + d * (10 ^ 360 * R i + R 360) := by
    unfold app
    rw [R_add, pow_add]
    ring
  have key : n0 * 10 ^ i * 10 ^ 360 + d * (10 ^ 360 * R i + R 360) ≡
      n0 * 10 ^ i * 1 + d * (1 * R i + 0) [MOD C] :=
    (h10.mul_left _).add (((h10.mul_right _).add hR).mul_left _)
  have back : n0 * 10 ^ i * 1 + d * (1 * R i + 0) = app n0 d i := by
    unfold app
    ring
  rw [e]
  unfold Nat.ModEq at key
  rw [key, back]

set_option maxRecDepth 100000 in
/-- The kernel checks the first period. -/
theorem base : ∀ i < 360, ∀ d ∈ [1, 3, 7, 9], ∃ C ∈ Cs, app n0 d (i + 1) % C = 0 := by
  decide +kernel

theorem cover (d : ℕ) (hd : d ∈ [1, 3, 7, 9]) (i : ℕ) (hi : 1 ≤ i) :
    ∃ C ∈ Cs, app n0 d i % C = 0 := by
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    by_cases h : i ≤ 360
    · have := base (i - 1) (by omega) d hd
      rwa [show i - 1 + 1 = i by omega] at this
    · obtain ⟨C, hC, h0⟩ := ih (i - 360) (by omega) (by omega)
      refine ⟨C, hC, ?_⟩
      have := periodic d (i - 360) C hC
      rw [show i - 360 + 360 = i by omega] at this
      rw [this, h0]

/-- a(n0) = 0. -/
theorem zero_term : ZeroTerm n0 := by
  intro d hd i hi hp
  have hbig : 10 * n0 ≤ app n0 d i := by
    unfold app
    have h10 : 10 ≤ 10 ^ i := by
      calc 10 = 10 ^ 1 := by norm_num
        _ ≤ 10 ^ i := Nat.pow_le_pow_right (by norm_num) hi
    have : n0 * 10 ≤ n0 * 10 ^ i := Nat.mul_le_mul_left _ h10
    omega
  have h2pow : 2 ∣ 10 ^ i := dvd_pow (by norm_num : 2 ∣ 10) (by omega)
  have h5pow : 5 ∣ 10 ^ i := dvd_pow (by norm_num : 5 ∣ 10) (by omega)
  have hn0 : 0 < n0 := by decide
  -- a divisor q of app with 1 < q < app contradicts primality
  have finish : ∀ q, q ∣ app n0 d i → 1 < q → q < app n0 d i → False := by
    intro q hq h1 h2
    rcases hp.eq_one_or_self_of_dvd q hq with h | h <;> omega
  have hlarge : 10 < app n0 d i := by
    have : 10 < 10 * n0 := by decide
    omega
  interval_cases d
  · exact finish 2 (Dvd.dvd.add (Dvd.dvd.mul_left h2pow _) (by simp)) (by norm_num) (by omega)
  · obtain ⟨C, hC, h0⟩ := cover 1 (by simp) i hi
    obtain ⟨hC1, hC2⟩ := Cs_bounds C hC
    exact finish C (Nat.dvd_of_mod_eq_zero h0) hC1 (by omega)
  · exact finish 2 (Dvd.dvd.add (Dvd.dvd.mul_left h2pow _) (Dvd.dvd.mul_right (by norm_num) _))
      (by norm_num) (by omega)
  · obtain ⟨C, hC, h0⟩ := cover 3 (by simp) i hi
    obtain ⟨hC1, hC2⟩ := Cs_bounds C hC
    exact finish C (Nat.dvd_of_mod_eq_zero h0) hC1 (by omega)
  · exact finish 2 (Dvd.dvd.add (Dvd.dvd.mul_left h2pow _) (Dvd.dvd.mul_right (by norm_num) _))
      (by norm_num) (by omega)
  · exact finish 5 (Dvd.dvd.add (Dvd.dvd.mul_left h5pow _) (Dvd.dvd.mul_right (by norm_num) _))
      (by norm_num) (by omega)
  · exact finish 2 (Dvd.dvd.add (Dvd.dvd.mul_left h2pow _) (Dvd.dvd.mul_right (by norm_num) _))
      (by norm_num) (by omega)
  · obtain ⟨C, hC, h0⟩ := cover 7 (by simp) i hi
    obtain ⟨hC1, hC2⟩ := Cs_bounds C hC
    exact finish C (Nat.dvd_of_mod_eq_zero h0) hC1 (by omega)
  · exact finish 2 (Dvd.dvd.add (Dvd.dvd.mul_left h2pow _) (Dvd.dvd.mul_right (by norm_num) _))
      (by norm_num) (by omega)
  · obtain ⟨C, hC, h0⟩ := cover 9 (by simp) i hi
    obtain ⟨hC1, hC2⟩ := Cs_bounds C hC
    exact finish C (Nat.dvd_of_mod_eq_zero h0) hC1 (by omega)

/-- The conjecture "if a(n) = 0, then n is divisible by 3" is false. -/
theorem disproof : ¬ ∀ n : ℕ, ZeroTerm n → 3 ∣ n := by
  intro h
  have := h n0 zero_term
  revert this
  decide

end OMA.S_oeis_a256481

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a256481.main) :=
  OMA.S_oeis_a256481.disproof
