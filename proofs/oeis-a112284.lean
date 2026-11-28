import OMAStatements.S_oeis_a112284
import Mathlib

namespace OMA.P_oeis_a112284

open OMA.S_oeis_a112284

private def bVals : List ℤ := [1, 1, -12, 204, -3925, 80809, -1736180, 38414234, -868406239, 19956190101, -464567682162, 10928553125816, -259313913949783, 6197786859789615, -149048459953356926, 3603527201302414744, -87526367874505524046, 2134600311518510544578, -52246658500293413007118, 1282907539361047856979186, -31592485018990774460974744, 780012432817452339783549018, -19303824976625704222239898280, 478760351546448784353102069104, -11897246109309746508569837365612, 296181839634846933794279638378418, -7385715679643404465685286234854518, 184456669126508575935534331463286226]
private def cVals : List ℤ := [1, 27, 27, 9, 27, 27, 9, 27, 27, 3, 27, 27, 9, 27, 27, 9, 27, 27, 21, 27, 27, 9, 27, 27, 9, 27, 27, 1]

private def b0 (m : ℕ) : ℤ := bVals.getD m 0
private def c0 (m : ℕ) : ℤ := cVals.getD m 0

/-- Given a power series `B` with `B(0) = 1`, for any `n ≥ 1` and `m ≥ 1`,
`coeff m (B ^ n) = n * coeff m B + R`, where `R` depends only on `coeff k B` for `k < m`. -/
private lemma coeff_pow_eq_linear (n : ℕ) :
    ∀ B1 B2 : PowerSeries ℤ,
      PowerSeries.constantCoeff B1 = 1 → PowerSeries.constantCoeff B2 = 1 →
      ∀ m : ℕ, (∀ k < m, PowerSeries.coeff k B1 = PowerSeries.coeff k B2) →
        PowerSeries.coeff m (B1 ^ n) - (n : ℤ) * PowerSeries.coeff m B1 =
        PowerSeries.coeff m (B2 ^ n) - (n : ℤ) * PowerSeries.coeff m B2 := by
  induction n with
  | zero =>
    intro B1 B2 _ _ m _
    simp
  | succ n ih =>
    intro B1 B2 h1 h2 m hlt
    rw [pow_succ, pow_succ]
    by_cases hm : m = 0
    · subst hm
      simp [h1, h2]
    · have hsplit : ∀ (P Q : PowerSeries ℤ), PowerSeries.constantCoeff P = 1 → PowerSeries.constantCoeff Q = 1 →
          PowerSeries.coeff m (P * Q) =
          PowerSeries.coeff m P + PowerSeries.coeff m Q +
          ∑ j ∈ Finset.Icc 1 (m - 1),
            PowerSeries.coeff j P * PowerSeries.coeff (m - j) Q := by
        intro P Q hP hQ
        rw [PowerSeries.coeff_mul]
        rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun x y => PowerSeries.coeff x P * PowerSeries.coeff y Q)]
        rw [Finset.sum_range_succ, Nat.sub_self]
        have hP0 : PowerSeries.coeff 0 P = 1 := by simpa using hP
        have hQ0 : PowerSeries.coeff 0 Q = 1 := by simpa using hQ
        rw [hQ0, mul_one]
        obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm
        rw [Finset.sum_range_succ', Nat.sub_zero, hP0, one_mul]
        have hmid_eq : ∑ x ∈ Finset.range k, PowerSeries.coeff (x + 1) P * PowerSeries.coeff (k + 1 - (x + 1)) Q =
            ∑ j ∈ Finset.Icc 1 k, PowerSeries.coeff j P * PowerSeries.coeff (k + 1 - j) Q := by
          refine Finset.sum_bij (fun x _ => x + 1) ?_ ?_ ?_ ?_
          · intro x hx; simp only [Finset.mem_range, Finset.mem_Icc] at hx ⊢; omega
          · intro _ _ _ _ h; omega
          · intro j hj; simp only [Finset.mem_Icc, Finset.mem_range] at hj ⊢; exact ⟨j - 1, by omega, by omega⟩
          · intro _ _; rfl
        rw [Nat.succ_eq_add_one, Nat.add_sub_cancel, hmid_eq]; ring
      have hc1 : PowerSeries.constantCoeff (B1 ^ n) = 1 := by simp [h1]
      have hc2 : PowerSeries.constantCoeff (B2 ^ n) = 1 := by simp [h2]
      rw [hsplit (B1 ^ n) B1 hc1 h1, hsplit (B2 ^ n) B2 hc2 h2]
      have hmid : ∑ j ∈ Finset.Icc 1 (m - 1),
            PowerSeries.coeff j (B1 ^ n) * PowerSeries.coeff (m - j) B1 =
          ∑ j ∈ Finset.Icc 1 (m - 1),
            PowerSeries.coeff j (B2 ^ n) * PowerSeries.coeff (m - j) B2 := by
        refine Finset.sum_congr rfl (fun j hj => ?_)
        simp only [Finset.mem_Icc] at hj
        have hB : PowerSeries.coeff (m - j) B1 = PowerSeries.coeff (m - j) B2 := hlt (m - j) (by omega)
        have hpow : PowerSeries.coeff j (B1 ^ n) = PowerSeries.coeff j (B2 ^ n) := by
          have := ih B1 B2 h1 h2 j (fun k hk => hlt k (by omega))
          have hBp1 := hlt j (by omega)
          rw [hBp1] at this
          linarith
        rw [hB, hpow]
      have hih := ih B1 B2 h1 h2 m hlt
      push_cast
      linarith

/-- Recursive construction of the full integer sequence `b : ℕ → ℤ` for any `n ≥ 1` such that
`B(x)^n` has all positive-degree coefficients in `[1, n]`. -/
private noncomputable def buildB (n : ℕ) (hn : 1 ≤ n) : ℕ → ℤ
  | 0 => 1
  | m + 1 =>
    let Bprev : PowerSeries ℤ := PowerSeries.mk (fun k => if k ≤ m then buildB n hn k else 0)
    let rem : ℤ := PowerSeries.coeff (m + 1) (Bprev ^ n)
    let cm : ℤ := ((rem - 1) % (n : ℤ)) + 1
    (cm - rem) / (n : ℤ)

private lemma buildB_zero (n : ℕ) (hn : 1 ≤ n) : buildB n hn 0 = 1 := by
  simp [buildB]

private lemma isRow_buildB (n : ℕ) (hn : 1 ≤ n) :
    IsRowA112283 n (fun m => PowerSeries.coeff m ((PowerSeries.mk (buildB n hn)) ^ n)) := by
  set B : PowerSeries ℤ := PowerSeries.mk (buildB n hn)
  have hB0 : PowerSeries.constantCoeff B = 1 := by
    simp [B, buildB_zero]
  refine ⟨by simp [hB0], ?_, ⟨B, hB0, fun _ => rfl⟩⟩
  intro m hm
  rcases Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0) with ⟨k, rfl⟩
  set Bprev : PowerSeries ℤ := PowerSeries.mk (fun j => if j ≤ k then buildB n hn j else 0)
  have hBp0 : PowerSeries.constantCoeff Bprev = 1 := by
    simp [Bprev, buildB_zero]
  have hlt : ∀ j < k + 1, PowerSeries.coeff j B = PowerSeries.coeff j Bprev := by
    intro j hj
    simp [B, Bprev, show j ≤ k by omega]
  have hlin := coeff_pow_eq_linear n B Bprev hB0 hBp0 (k + 1) hlt
  have hBp_k1 : PowerSeries.coeff (k + 1) Bprev = 0 := by
    simp [Bprev]
  rw [hBp_k1, mul_zero, sub_zero] at hlin
  set rem : ℤ := PowerSeries.coeff (k + 1) (Bprev ^ n)
  set cm : ℤ := ((rem - 1) % (n : ℤ)) + 1
  have hBk1 : PowerSeries.coeff (k + 1) B = (cm - rem) / (n : ℤ) := by
    simp [B, buildB, Bprev, rem, cm]
  have hn_pos : (0 : ℤ) < (n : ℤ) := by omega
  have hdvd : (n : ℤ) ∣ (cm - rem) := by
    have h1 : cm - rem = ((rem - 1) % (n : ℤ)) - (rem - 1) := by dsimp [cm]; ring
    rw [h1]
    have hmod := Int.emod_add_mul_ediv (rem - 1) (n : ℤ)
    refine ⟨-((rem - 1) / (n : ℤ)), ?_⟩
    linarith
  have hmul_div : (n : ℤ) * ((cm - rem) / (n : ℤ)) = cm - rem := Int.mul_ediv_cancel' hdvd
  have hcoeff : PowerSeries.coeff (k + 1) (B ^ n) = cm := by
    rw [hBk1, hmul_div] at hlin
    linarith
  change 1 ≤ PowerSeries.coeff (k + 1) (B ^ n) ∧ PowerSeries.coeff (k + 1) (B ^ n) ≤ (n : ℤ)
  rw [hcoeff]
  have hmod_ge : 0 ≤ (rem - 1) % (n : ℤ) := Int.emod_nonneg (rem - 1) (by omega)
  have hmod_lt : (rem - 1) % (n : ℤ) < (n : ℤ) := Int.emod_lt_of_pos (rem - 1) hn_pos
  dsimp [cm]
  omega

/-- Power-series differential identity: `B * (B^n)' = n * B' * B^n` over `ℤ`. -/
private lemma mul_deriv_pow (B : PowerSeries ℤ) (n : ℕ) :
    ∀ r : ℕ,
      ∑ j ∈ Finset.range (r + 1),
        PowerSeries.coeff j B * ((r + 1 - j : ℕ) : ℤ) * PowerSeries.coeff (r + 1 - j) (B ^ n) =
      (n : ℤ) * ∑ j ∈ Finset.range (r + 1),
        ((j + 1 : ℕ) : ℤ) * PowerSeries.coeff (j + 1) B * PowerSeries.coeff (r - j) (B ^ n) := by
  intro r
  have hderiv : B * PowerSeries.derivative ℤ (B ^ n) = (n : ℤ) • (PowerSeries.derivative ℤ B * B ^ n) := by
    induction n with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, Derivation.leibniz, smul_eq_mul, smul_eq_mul, mul_add]
      have h1 : B * (B ^ k * PowerSeries.derivative ℤ B) = PowerSeries.derivative ℤ B * (B ^ k * B) := by ring
      have h3 : B * (B * PowerSeries.derivative ℤ (B ^ k)) = (B * PowerSeries.derivative ℤ (B ^ k)) * B := by ring
      rw [h1, h3, ih]
      push_cast
      simp only [zsmul_eq_mul, Int.cast_add, Int.cast_one]
      ring
  have hc := congr_arg (PowerSeries.coeff r) hderiv
  rw [PowerSeries.coeff_mul, map_zsmul, zsmul_eq_mul, PowerSeries.coeff_mul] at hc
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun x y =>
      PowerSeries.coeff x B * PowerSeries.coeff y (PowerSeries.derivative ℤ (B ^ n))),
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun x y =>
      PowerSeries.coeff x (PowerSeries.derivative ℤ B) * PowerSeries.coeff y (B ^ n))] at hc
  have hlhs : ∑ j ∈ Finset.range (r + 1),
      PowerSeries.coeff j B * PowerSeries.coeff (r - j) (PowerSeries.derivative ℤ (B ^ n)) =
      ∑ j ∈ Finset.range (r + 1),
        PowerSeries.coeff j B * ((r + 1 - j : ℕ) : ℤ) * PowerSeries.coeff (r + 1 - j) (B ^ n) := by
    refine Finset.sum_congr rfl (fun j hj => ?_)
    have hjr : j ≤ r := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    rw [PowerSeries.coeff_derivative]
    have hsub : r - j + 1 = r + 1 - j := by omega
    rw [← hsub]; push_cast; ring
  have hrhs : ∑ j ∈ Finset.range (r + 1),
      PowerSeries.coeff j (PowerSeries.derivative ℤ B) * PowerSeries.coeff (r - j) (B ^ n) =
      ∑ j ∈ Finset.range (r + 1),
        ((j + 1 : ℕ) : ℤ) * PowerSeries.coeff (j + 1) B * PowerSeries.coeff (r - j) (B ^ n) := by
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [PowerSeries.coeff_derivative]; push_cast; ring
  rw [hlhs, hrhs] at hc
  exact hc

/-- Exact verification of the differential recurrence for `b0, c0` at `n = 27`, `r ≤ 26`. -/
private lemma diff_rec_27 : ∀ r : ℕ, r ≤ 26 →
    ∑ j ∈ Finset.range (r + 1), b0 j * ((r + 1 - j : ℕ) : ℤ) * c0 (r + 1 - j) =
    27 * ∑ j ∈ Finset.range (r + 1), ((j + 1 : ℕ) : ℤ) * b0 (j + 1) * c0 (r - j) := by
  intro r hr
  interval_cases r <;> decide

/-- For `n = 27`, the constructed `B = PowerSeries.mk (buildB 27 _)` matches `b0` and `B^27` matches `c0` up to degree 27! -/
private lemma buildB_27_eq :
    ∀ m : ℕ, m ≤ 27 →
      buildB 27 (by omega) m = b0 m ∧
      PowerSeries.coeff m ((PowerSeries.mk (buildB 27 (by omega))) ^ 27) = c0 m := by
  set B : PowerSeries ℤ := PowerSeries.mk (buildB 27 (by omega))
  have hB0 : PowerSeries.constantCoeff B = 1 := by simp [B, buildB_zero]
  have hrow := isRow_buildB 27 (by omega)
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro hm
    cases m with
    | zero =>
      refine ⟨by simp [buildB_zero, b0, bVals], by simp [hB0, c0, cVals]⟩
    | succ r =>
      have hmd := mul_deriv_pow B 27 r
      have hrec := diff_rec_27 r (by omega)
      -- Split `j = 0` from LHS of both `hmd` and `hrec`, and `j = r` from RHS!
      have hsplitL : ∀ (f g : ℕ → ℤ), f 0 = 1 →
          ∑ j ∈ Finset.range (r + 1), f j * ((r + 1 - j : ℕ) : ℤ) * g (r + 1 - j) =
          ((r + 1 : ℕ) : ℤ) * g (r + 1) +
          ∑ j ∈ Finset.Icc 1 r, f j * ((r + 1 - j : ℕ) : ℤ) * g (r + 1 - j) := by
        intro f g hf0
        rw [Finset.sum_range_succ']
        have h0 : f 0 * ((r + 1 - 0 : ℕ) : ℤ) * g (r + 1 - 0) = ((r + 1 : ℕ) : ℤ) * g (r + 1) := by
          simp [hf0]
        rw [add_comm, h0]
        congr 1
        refine Finset.sum_bij (fun j _ => j + 1) ?_ ?_ ?_ ?_
        · intro j hj; simp only [Finset.mem_range, Finset.mem_Icc] at hj ⊢; omega
        · intro _ _ _ _ h; omega
        · intro k hk; simp only [Finset.mem_Icc, Finset.mem_range] at hk ⊢; exact ⟨k - 1, by omega, by omega⟩
        · intro _ _; rfl
      have hsplitR : ∀ (f g : ℕ → ℤ), g 0 = 1 →
          ∑ j ∈ Finset.range (r + 1), ((j + 1 : ℕ) : ℤ) * f (j + 1) * g (r - j) =
          ((r + 1 : ℕ) : ℤ) * f (r + 1) +
          ∑ j ∈ Finset.range r, ((j + 1 : ℕ) : ℤ) * f (j + 1) * g (r - j) := by
        intro f g hg0
        rw [Finset.sum_range_succ, Nat.sub_self, hg0, mul_one, add_comm]
      have hB0' : PowerSeries.coeff 0 B = 1 := by simpa using hB0
      have hA0' : PowerSeries.coeff 0 (B ^ 27) = 1 := by simp [hB0]
      have hb00 : b0 0 = 1 := by decide
      have hc00 : c0 0 = 1 := by decide
      rw [hsplitL (fun j => PowerSeries.coeff j B) (fun j => PowerSeries.coeff j (B ^ 27)) hB0',
        hsplitR (fun j => PowerSeries.coeff j B) (fun j => PowerSeries.coeff j (B ^ 27)) hA0'] at hmd
      rw [hsplitL b0 c0 hb00, hsplitR b0 c0 hc00] at hrec
      have hL_eq : ∑ j ∈ Finset.Icc 1 r, PowerSeries.coeff j B * ((r + 1 - j : ℕ) : ℤ) * PowerSeries.coeff (r + 1 - j) (B ^ 27) =
          ∑ j ∈ Finset.Icc 1 r, b0 j * ((r + 1 - j : ℕ) : ℤ) * c0 (r + 1 - j) := by
        refine Finset.sum_congr rfl (fun j hj => ?_)
        simp only [Finset.mem_Icc] at hj
        have h1 := (ih j (by omega) (by omega)).1
        have h2 := (ih (r + 1 - j) (by omega) (by omega)).2
        simp only [B, PowerSeries.coeff_mk] at *
        rw [h1, h2]
      have hR_eq : ∑ j ∈ Finset.range r, ((j + 1 : ℕ) : ℤ) * PowerSeries.coeff (j + 1) B * PowerSeries.coeff (r - j) (B ^ 27) =
          ∑ j ∈ Finset.range r, ((j + 1 : ℕ) : ℤ) * b0 (j + 1) * c0 (r - j) := by
        refine Finset.sum_congr rfl (fun j hj => ?_)
        simp only [Finset.mem_range] at hj
        have h1 := (ih (j + 1) (by omega) (by omega)).1
        have h2 := (ih (r - j) (by omega) (by omega)).2
        simp only [B, PowerSeries.coeff_mk] at *
        rw [h1, h2]
      rw [hL_eq, hR_eq] at hmd
      have hdiff : ((r + 1 : ℕ) : ℤ) * (PowerSeries.coeff (r + 1) (B ^ 27) - c0 (r + 1)) =
          ((r + 1 : ℕ) : ℤ) * (27 * (PowerSeries.coeff (r + 1) B - b0 (r + 1))) := by
        push_cast at hmd hrec ⊢
        linear_combination hmd - hrec
      have hr1_ne : ((r + 1 : ℕ) : ℤ) ≠ 0 := by positivity
      have hdiff' : PowerSeries.coeff (r + 1) (B ^ 27) - c0 (r + 1) =
          27 * (PowerSeries.coeff (r + 1) B - b0 (r + 1)) :=
        mul_left_cancel₀ hr1_ne hdiff
      have hc_bounds : 1 ≤ PowerSeries.coeff (r + 1) (B ^ 27) ∧ PowerSeries.coeff (r + 1) (B ^ 27) ≤ 27 :=
        hrow.2.1 (r + 1) (by omega)
      have hc0_bounds : 1 ≤ c0 (r + 1) ∧ c0 (r + 1) ≤ 27 := by
        have hr26 : r ≤ 26 := by omega
        interval_cases r <;> decide
      have hceq : PowerSeries.coeff (r + 1) (B ^ 27) = c0 (r + 1) := by omega
      have hbeq : buildB 27 (by omega) (r + 1) = b0 (r + 1) := by
        have : PowerSeries.coeff (r + 1) B = b0 (r + 1) := by omega
        simpa [B] using this
      exact ⟨hbeq, hceq⟩

lemma disprove_a112284 :
    ¬ (∀ n : ℕ, 1 ≤ n →
        ∀ a : ℕ → ℤ, IsRowA112283 n a →
          ((a n = 1 ∧ ∀ m : ℕ, 1 ≤ m → m < n → a m ≠ 1) ↔
            (n = 1 ∨ Nat.Prime n ∨ ∃ p : ℕ, Nat.Prime p ∧ Odd p ∧ n = p ^ 2))) := by
  intro h
  set a : ℕ → ℤ := fun m => PowerSeries.coeff m ((PowerSeries.mk (buildB 27 (by omega))) ^ 27)
  have hrow : IsRowA112283 27 a := isRow_buildB 27 (by omega)
  have hiff := h 27 (by omega) a hrow
  have hlhs : a 27 = 1 ∧ ∀ m : ℕ, 1 ≤ m → m < 27 → a m ≠ 1 := by
    refine ⟨?_, ?_⟩
    · exact (buildB_27_eq 27 le_rfl).2.trans (by decide)
    · intro m hm1 hm27
      dsimp only [a]
      rw [(buildB_27_eq m (by omega)).2]
      interval_cases m <;> decide
  have hrhs := hiff.mp hlhs
  rcases hrhs with h1 | hp | ⟨p, hp, _, hp2⟩
  · omega
  · norm_num at hp
  · have hp_le : p ≤ 5 := by nlinarith
    have hp_ge : 2 ≤ p := hp.two_le
    interval_cases p <;> omega

end OMA.P_oeis_a112284

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a112284.main) :=
  OMA.P_oeis_a112284.disprove_a112284
