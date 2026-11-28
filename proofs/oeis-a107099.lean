import OMAStatements.S_oeis_a107099
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace OeisA107099Proof

open Classical
open OMA.S_oeis_a107099

private noncomputable def psComp3 (F G : PowerSeries (ZMod 3)) : PowerSeries (ZMod 3) :=
  PowerSeries.mk fun n =>
    ∑ k ∈ Finset.range (n + 1), PowerSeries.coeff k F * PowerSeries.coeff n (G ^ k)

private def seqC : ℕ → ZMod 3
  | 0 => 1
  | 1 => 2
  | m + 2 =>
    ∑ j : Fin (m + 1), seqC (j.1 + 1) * seqC (m + 1 - j.1)
termination_by n => n
decreasing_by
  all_goals omega

private lemma seqC_zero : seqC 0 = 1 := by rw [seqC]
private lemma seqC_one : seqC 1 = 2 := by rw [seqC]

private lemma seqC_succ_succ (m : ℕ) :
    seqC (m + 2) = ∑ j ∈ Finset.range (m + 1), seqC (j + 1) * seqC (m + 1 - j) := by
  rw [seqC, Fin.sum_univ_eq_sum_range (fun j => seqC (j + 1) * seqC (m + 1 - j))]

private lemma seqC_conv (r : ℕ) :
    ∑ k ∈ Finset.range (r + 1), seqC k * seqC (r - k) =
      if r = 0 then 1 else if r = 1 then 1 else 0 := by
  match r with
  | 0 =>
    simp [seqC_zero]
  | 1 =>
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add,
      Nat.sub_zero, Nat.sub_self, seqC_zero, seqC_one, one_mul, mul_one,
      show (1 : ℕ) ≠ 0 by decide, ↓reduceIte]
    decide
  | m + 2 =>
    simp only [show m + 2 ≠ 0 by omega, show m + 2 ≠ 1 by omega, ↓reduceIte]
    rw [Finset.sum_range_succ, Finset.sum_range_succ']
    simp only [Nat.sub_self, Nat.sub_zero, seqC_zero, one_mul, mul_one]
    have hmid :
        ∑ k ∈ Finset.range (m + 1), seqC (k + 1) * seqC (m + 2 - (k + 1)) =
        ∑ j ∈ Finset.range (m + 1), seqC (j + 1) * seqC (m + 1 - j) := by
      apply Finset.sum_congr rfl
      intro k _
      rw [show m + 2 - (k + 1) = m + 1 - k by omega]
    rw [hmid, seqC_succ_succ]
    set S : ZMod 3 := ∑ j ∈ Finset.range (m + 1), seqC (j + 1) * seqC (m + 1 - j)
    have h3 : ∀ x : ZMod 3, x + x + x = 0 := by decide
    exact h3 S

private noncomputable def seriesB : PowerSeries (ZMod 3) :=
  PowerSeries.mk fun n => if h : ∃ k : ℕ, n = 3 ^ k then seqC (Nat.find h) else 0

private lemma coeff_seriesB_pow3 (k : ℕ) :
    PowerSeries.coeff (3 ^ k) seriesB = seqC k := by
  unfold seriesB
  rw [PowerSeries.coeff_mk, dif_pos ⟨k, rfl⟩]
  congr 1
  have hspec : 3 ^ k = 3 ^ Nat.find (⟨k, rfl⟩ : ∃ j : ℕ, 3 ^ k = 3 ^ j) :=
    Nat.find_spec (⟨k, rfl⟩ : ∃ j : ℕ, 3 ^ k = 3 ^ j)
  exact (Nat.pow_right_injective (by decide : 2 ≤ 3) hspec).symm

private lemma coeff_seriesB_of_not_pow3 {n : ℕ} (h : ¬ ∃ k : ℕ, n = 3 ^ k) :
    PowerSeries.coeff n seriesB = 0 := by
  unfold seriesB
  rw [PowerSeries.coeff_mk, dif_neg h]

private lemma three_eq_zero_ps3 : (3 : PowerSeries (ZMod 3)) = 0 := by
  ext k; rw [show (3 : PowerSeries (ZMod 3)) = PowerSeries.C 3 from rfl, PowerSeries.coeff_C]
  split_ifs <;> simp [show (3 : ZMod 3) = 0 by decide]

private lemma add_pow3_ps3 (u v : PowerSeries (ZMod 3)) :
    (u + v) ^ 3 = u ^ 3 + v ^ 3 := by
  calc (u + v) ^ 3 = u ^ 3 + v ^ 3 + 3 * (u ^ 2 * v + u * v ^ 2) := by ring
    _ = u ^ 3 + v ^ 3 := by rw [three_eq_zero_ps3, zero_mul, add_zero]

private lemma finset_sum_pow3_ps3 {ι : Type*} (s : Finset ι) (f : ι → PowerSeries (ZMod 3)) :
    (∑ i ∈ s, f i) ^ 3 = ∑ i ∈ s, (f i) ^ 3 := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, add_pow3_ps3, ih, Finset.sum_insert ha]

private lemma coeff_cube_mod3 (f : PowerSeries (ZMod 3)) (n : ℕ) :
    PowerSeries.coeff n (f ^ 3) =
      if 3 ∣ n then PowerSeries.coeff (n / 3) f else 0 := by
  let P : PowerSeries (ZMod 3) :=
    ∑ i ∈ Finset.range (n + 1), PowerSeries.C (PowerSeries.coeff i f) * PowerSeries.X ^ i
  let R : PowerSeries (ZMod 3) := f - P
  have hP_coeff : ∀ j ≤ n, PowerSeries.coeff j P = PowerSeries.coeff j f := by
    intro j hj
    dsimp only [P]
    rw [map_sum]
    simp only [PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow]
    rw [Finset.sum_eq_single j]
    · simp
    · intro i _ hne; simp [Ne.symm hne]
    · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h
  have hR_zero : ∀ j ≤ n, PowerSeries.coeff j R = 0 := by
    intro j hj
    dsimp only [R]
    rw [map_sub, hP_coeff j hj, sub_self]
  have hR_mul_zero : ∀ g : PowerSeries (ZMod 3), PowerSeries.coeff n (R * g) = 0 := by
    intro g
    rw [PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun i j => PowerSeries.coeff i R * PowerSeries.coeff j g)]
    apply Finset.sum_eq_zero
    intro i hi
    rw [Finset.mem_range] at hi
    rw [hR_zero i (by omega), zero_mul]
  have hf_eq : f = P + R := by dsimp only [R]; ring
  have hf3 : PowerSeries.coeff n (f ^ 3) = PowerSeries.coeff n (P ^ 3) := by
    rw [hf_eq, add_pow3_ps3, map_add, show R ^ 3 = R * R ^ 2 by ring, hR_mul_zero, add_zero]
  rw [hf3]
  dsimp only [P]
  rw [finset_sum_pow3_ps3, map_sum]
  have hterm : ∀ i : ℕ,
      PowerSeries.coeff n ((PowerSeries.C (PowerSeries.coeff i f) * PowerSeries.X ^ i) ^ 3) =
        if n = 3 * i then PowerSeries.coeff i f else 0 := by
    intro i
    rw [mul_pow, ← map_pow, ← pow_mul, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow,
      show i * 3 = 3 * i by ring]
    have hcube3 : ∀ x : ZMod 3, x ^ 3 = x := by decide
    rw [hcube3]
    split_ifs <;> simp
  simp_rw [hterm]
  by_cases h3 : 3 ∣ n
  · rw [if_pos h3]
    rw [Finset.sum_eq_single (n / 3)]
    · rw [if_pos (by omega)]
    · intro i _ hne; rw [if_neg (by omega)]
    · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h
  · rw [if_neg h3]
    apply Finset.sum_eq_zero
    intro i _
    rw [if_neg]
    intro heq
    exact h3 ⟨i, heq⟩

private lemma coeff_pow_three_pow_mod3 (f : PowerSeries (ZMod 3)) :
    ∀ k n : ℕ, PowerSeries.coeff n (f ^ (3 ^ k)) =
      if 3 ^ k ∣ n then PowerSeries.coeff (n / 3 ^ k) f else 0 := by
  intro k
  induction k with
  | zero =>
    intro n; simp
  | succ k ih =>
    intro n
    rw [pow_succ, pow_mul, coeff_cube_mod3]
    by_cases h3 : 3 ∣ n
    · rw [if_pos h3, ih (n / 3)]
      by_cases hk : 3 ^ k ∣ n / 3
      · have hsucc : 3 ^ k * 3 ∣ n := by
          rcases h3 with ⟨q, rfl⟩
          rw [Nat.mul_div_cancel_left q (by decide : 0 < 3)] at hk
          rcases hk with ⟨r, rfl⟩
          exact ⟨r, by ring⟩
        rw [if_pos hk, if_pos hsucc, Nat.div_div_eq_div_mul, mul_comm 3 (3 ^ k)]
      · have hnsucc : ¬ (3 ^ k * 3 ∣ n) := by
          intro h; apply hk
          rcases h with ⟨r, hr⟩
          exact ⟨r, by rw [hr, show 3 ^ k * 3 * r = 3 * (3 ^ k * r) by ring,
            Nat.mul_div_cancel_left _ (by decide : 0 < 3)]⟩
        rw [if_neg hk, if_neg hnsucc]
    · have hnsucc : ¬ (3 ^ k * 3 ∣ n) := by
        intro h; apply h3
        rcases h with ⟨r, hr⟩
        exact ⟨3 ^ k * r, by rw [hr]; ring⟩
      rw [if_neg h3, if_neg hnsucc]

private lemma seriesB_comp_self :
    psComp3 seriesB seriesB = PowerSeries.X + PowerSeries.X ^ 3 := by
  ext n
  unfold psComp3
  rw [PowerSeries.coeff_mk, map_add, PowerSeries.coeff_X, PowerSeries.coeff_X_pow]
  by_cases hpow : ∃ r : ℕ, n = 3 ^ r
  · rcases hpow with ⟨r, rfl⟩
    have hsum :
        ∑ m ∈ Finset.range (3 ^ r + 1),
          PowerSeries.coeff m seriesB * PowerSeries.coeff (3 ^ r) (seriesB ^ m) =
        ∑ k ∈ Finset.range (r + 1), seqC k * seqC (r - k) := by
      have hsub :
          ∑ m ∈ Finset.range (3 ^ r + 1),
            PowerSeries.coeff m seriesB * PowerSeries.coeff (3 ^ r) (seriesB ^ m) =
          ∑ m ∈ (Finset.range (r + 1)).image (fun k => 3 ^ k),
            PowerSeries.coeff m seriesB * PowerSeries.coeff (3 ^ r) (seriesB ^ m) := by
        symm
        apply Finset.sum_subset
        · intro m hm
          rcases Finset.mem_image.mp hm with ⟨k, hk, rfl⟩
          rw [Finset.mem_range] at hk ⊢
          have := Nat.pow_le_pow_right (by decide : 0 < 3) (by omega : k ≤ r)
          omega
        · intro m hm hnot
          rw [Finset.mem_range] at hm
          by_cases hex : ∃ k : ℕ, m = 3 ^ k
          · rcases hex with ⟨k, rfl⟩
            exfalso; apply hnot
            refine Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr ?_, rfl⟩
            by_contra hlt
            have hle : r + 1 ≤ k := by omega
            have hpow_lt : 3 ^ r < 3 ^ k :=
              Nat.pow_lt_pow_right (by decide : 1 < 3) (by omega)
            omega
          · rw [coeff_seriesB_of_not_pow3 hex, zero_mul]
      rw [hsub, Finset.sum_image (fun a _ b _ h => Nat.pow_right_injective (by decide : 2 ≤ 3) h)]
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.mem_range] at hk
      rw [coeff_seriesB_pow3 k, coeff_pow_three_pow_mod3]
      have hdvd : 3 ^ k ∣ 3 ^ r := Nat.pow_dvd_pow 3 (by omega)
      have hdiv : 3 ^ r / 3 ^ k = 3 ^ (r - k) := by
        conv_lhs => rw [show r = k + (r - k) by omega, pow_add]
        rw [Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero (by positivity))]
      rw [if_pos hdvd, hdiv, coeff_seriesB_pow3]
    rw [hsum, seqC_conv r]
    match r with
    | 0 => simp
    | 1 => simp
    | m + 2 =>
      have hge9 : 9 ≤ 3 ^ (m + 2) := by
        calc 9 = 3 ^ 2 := by norm_num
          _ ≤ 3 ^ (m + 2) := Nat.pow_le_pow_right (by decide) (by omega)
      simp [show 3 ^ (m + 2) ≠ 3 by omega]
  · have hne1 : n ≠ 1 := fun h => hpow ⟨0, by rw [h]; norm_num⟩
    have hne3 : n ≠ 3 := fun h => hpow ⟨1, by rw [h]; norm_num⟩
    rw [if_neg hne1, if_neg hne3, add_zero]
    apply Finset.sum_eq_zero
    intro m _
    by_cases hex : ∃ k : ℕ, m = 3 ^ k
    · rcases hex with ⟨k, rfl⟩
      rw [coeff_pow_three_pow_mod3]
      by_cases hdvd : 3 ^ k ∣ n
      · rw [if_pos hdvd]
        have hnotj : ¬ ∃ j : ℕ, n / 3 ^ k = 3 ^ j := by
          rintro ⟨j, hj⟩
          apply hpow
          refine ⟨k + j, ?_⟩
          rw [pow_add, ← hj, Nat.mul_div_cancel' hdvd]
        rw [coeff_seriesB_of_not_pow3 hnotj, mul_zero]
      · rw [if_neg hdvd, mul_zero]
    · rw [coeff_seriesB_of_not_pow3 hex, zero_mul]

private lemma map_psComp (F G : PowerSeries ℤ) :
    PowerSeries.map (Int.castRingHom (ZMod 3)) (psComp F G) =
      psComp3 (PowerSeries.map (Int.castRingHom (ZMod 3)) F)
              (PowerSeries.map (Int.castRingHom (ZMod 3)) G) := by
  ext n
  simp only [PowerSeries.coeff_map, psComp, psComp3, PowerSeries.coeff_mk, map_sum, map_mul,
    ← map_pow]

private lemma coeff_pow_diag (G : PowerSeries (ZMod 3))
    (hG0 : PowerSeries.coeff 0 G = 0) (hG1 : PowerSeries.coeff 1 G = 1) :
    ∀ k : ℕ, (∀ m < k, PowerSeries.coeff m (G ^ k) = 0) ∧ PowerSeries.coeff k (G ^ k) = 1 := by
  intro k
  induction k with
  | zero => exact ⟨fun m hm => by omega, by simp⟩
  | succ k ih =>
    constructor
    · intro m hm
      rw [pow_succ, PowerSeries.coeff_mul,
        Finset.Nat.sum_antidiagonal_eq_sum_range_succ
          (fun i j => PowerSeries.coeff i (G ^ k) * PowerSeries.coeff j G)]
      apply Finset.sum_eq_zero
      intro i hi
      rw [Finset.mem_range] at hi
      by_cases hik : i < k
      · rw [ih.1 i hik, zero_mul]
      · rw [show m - i = 0 by omega, hG0, mul_zero]
    · rw [pow_succ, PowerSeries.coeff_mul,
        Finset.Nat.sum_antidiagonal_eq_sum_range_succ
          (fun i j => PowerSeries.coeff i (G ^ k) * PowerSeries.coeff j G)]
      rw [Finset.sum_eq_single k]
      · rw [show k + 1 - k = 1 by omega, ih.2, hG1, mul_one]
      · intro i hi hne
        rw [Finset.mem_range] at hi
        by_cases hik : i < k
        · rw [ih.1 i hik, zero_mul]
        · rw [show k + 1 - i = 0 by omega, hG0, mul_zero]
      · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h

private lemma coeff_pow_congr (G1 G2 : PowerSeries (ZMod 3))
    (hG10 : PowerSeries.coeff 0 G1 = 0) (hG20 : PowerSeries.coeff 0 G2 = 0)
    {M : ℕ} (hagree : ∀ j < M, PowerSeries.coeff j G1 = PowerSeries.coeff j G2) :
    ∀ k : ℕ, 2 ≤ k → ∀ m ≤ M, PowerSeries.coeff m (G1 ^ k) = PowerSeries.coeff m (G2 ^ k) := by
  intro k hk
  induction k with
  | zero => omega
  | succ k ih =>
    intro m hm
    rw [pow_succ, pow_succ, PowerSeries.coeff_mul, PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun i j => PowerSeries.coeff i (G1 ^ k) * PowerSeries.coeff j G1),
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun i j => PowerSeries.coeff i (G2 ^ k) * PowerSeries.coeff j G2)]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_range] at hi
    by_cases hi0 : i = 0
    · subst hi0
      have h10 : PowerSeries.coeff 0 (G1 ^ k) = 0 := by
        rw [PowerSeries.coeff_zero_eq_constantCoeff, map_pow, ← PowerSeries.coeff_zero_eq_constantCoeff,
          hG10, zero_pow (by omega)]
      have h20 : PowerSeries.coeff 0 (G2 ^ k) = 0 := by
        rw [PowerSeries.coeff_zero_eq_constantCoeff, map_pow, ← PowerSeries.coeff_zero_eq_constantCoeff,
          hG20, zero_pow (by omega)]
      rw [h10, h20, zero_mul, zero_mul]
    · by_cases him : i = m
      · subst him; rw [Nat.sub_self, hG10, hG20, mul_zero, mul_zero]
      · rw [hagree (m - i) (by omega)]
        congr 1
        by_cases hk1 : k = 1
        · subst hk1; simp only [pow_one]; exact hagree i (by omega)
        · exact ih (by omega) i (by omega)

private lemma unique_A3_eq_B (A3 : PowerSeries (ZMod 3))
    (hA30 : PowerSeries.coeff 0 A3 = 0) (hA31 : PowerSeries.coeff 1 A3 = 1)
    (hA3eq : psComp3 A3 A3 = PowerSeries.X + PowerSeries.X ^ 3) : A3 = seriesB := by
  have hB0 : PowerSeries.coeff 0 seriesB = 0 :=
    coeff_seriesB_of_not_pow3 (by rintro ⟨k, hk⟩; have := Nat.one_le_pow k 3 (by decide); omega)
  have hB1 : PowerSeries.coeff 1 seriesB = 1 := by
    simpa [seqC_zero] using coeff_seriesB_pow3 0
  ext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    match n with
    | 0 => rw [hA30, hB0]
    | 1 => rw [hA31, hB1]
    | m + 2 =>
      have heq := congrArg (PowerSeries.coeff (m + 2)) (hA3eq.trans seriesB_comp_self.symm)
      simp only [psComp3, PowerSeries.coeff_mk] at heq
      conv at heq => lhs; rw [Finset.sum_range_succ, Finset.sum_range_succ', Finset.sum_range_succ']
      conv at heq => rhs; rw [Finset.sum_range_succ, Finset.sum_range_succ', Finset.sum_range_succ']
      rw [(coeff_pow_diag A3 hA30 hA31 (m + 2)).2, (coeff_pow_diag seriesB hB0 hB1 (m + 2)).2] at heq
      simp only [hA30, hB0, zero_mul, add_zero, hA31, hB1, one_mul, mul_one, Nat.zero_add,
        pow_one] at heq
      have hmid :
          ∑ k ∈ Finset.range m,
            PowerSeries.coeff (k + 1 + 1) A3 * PowerSeries.coeff (m + 2) (A3 ^ (k + 1 + 1)) =
          ∑ k ∈ Finset.range m,
            PowerSeries.coeff (k + 1 + 1) seriesB * PowerSeries.coeff (m + 2) (seriesB ^ (k + 1 + 1)) := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [Finset.mem_range] at hk
        rw [ih (k + 1 + 1) (by omega),
          coeff_pow_congr A3 seriesB hA30 hB0 ih (k + 1 + 1) (by omega) (m + 2) (le_refl _)]
      rw [hmid] at heq
      have h2eq : PowerSeries.coeff (m + 2) A3 + PowerSeries.coeff (m + 2) A3 =
          PowerSeries.coeff (m + 2) seriesB + PowerSeries.coeff (m + 2) seriesB := by
        have h1 :
            ∑ k ∈ Finset.range m,
              PowerSeries.coeff (k + 1 + 1) seriesB * PowerSeries.coeff (m + 2) (seriesB ^ (k + 1 + 1)) +
              (PowerSeries.coeff (m + 2) A3 + PowerSeries.coeff (m + 2) A3) =
            ∑ k ∈ Finset.range m,
              PowerSeries.coeff (k + 1 + 1) seriesB * PowerSeries.coeff (m + 2) (seriesB ^ (k + 1 + 1)) +
              (PowerSeries.coeff (m + 2) seriesB + PowerSeries.coeff (m + 2) seriesB) := by
          linear_combination heq
        exact add_left_cancel h1
      have h2cancel : ∀ a b : ZMod 3, a + a = b + b → a = b := by decide
      exact h2cancel _ _ h2eq

private lemma map_A_eq_seriesB {A : PowerSeries ℤ} (hA : IsA107099 A) :
    PowerSeries.map (Int.castRingHom (ZMod 3)) A = seriesB := by
  let phi : PowerSeries ℤ →+* PowerSeries (ZMod 3) := PowerSeries.map (Int.castRingHom (ZMod 3))
  have hA30 : PowerSeries.coeff 0 (phi A) = 0 := by simp [phi, hA.1]
  have hA31 : PowerSeries.coeff 1 (phi A) = 1 := by simp [phi, hA.2.1]
  have h4 : (4 : PowerSeries (ZMod 3)) = 1 := by
    ext k; rw [show (4 : PowerSeries (ZMod 3)) = PowerSeries.C 4 from rfl, PowerSeries.coeff_C,
      PowerSeries.coeff_one]
    split_ifs <;> simp [show (4 : ZMod 3) = 1 by decide]
  have hA3eq : psComp3 (phi A) (phi A) = PowerSeries.X + PowerSeries.X ^ 3 := by
    have h := congrArg phi hA.2.2
    rw [map_psComp, map_add, map_mul, map_ofNat, map_pow, h4, one_mul] at h
    dsimp only [phi] at h
    rw [PowerSeries.map_X] at h
    exact h
  exact unique_A3_eq_B (phi A) hA30 hA31 hA3eq

end OeisA107099Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a107099.main := by
  intro A hA n hnot
  change PowerSeries.coeff n A ≡ 0 [ZMOD ((3 : ℕ) : ℤ)]
  rw [← ZMod.intCast_eq_intCast_iff, Int.cast_zero]
  have h := congrArg (PowerSeries.coeff n) (OeisA107099Proof.map_A_eq_seriesB hA)
  simp only [PowerSeries.coeff_map, Int.coe_castRingHom] at h
  rw [h, OeisA107099Proof.coeff_seriesB_of_not_pow3 hnot]
