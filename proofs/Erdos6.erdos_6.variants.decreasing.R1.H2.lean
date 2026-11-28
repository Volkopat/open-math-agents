import OMAReductions.R_Erdos6_erdos_6_variants_decreasing_R1

-- Step Erdos6.erdos_6.variants.decreasing.R1.H2: hypothesis H2 of reduction Erdos6.erdos_6.variants.decreasing.R1
-- Credit: @<handle>
-- H2 := (∀ A : ℝ, 0 < A → ∃ B C : ℝ, ∀ x : ℝ, 2 ≤ x → ∀ a : ℕ → ℕ, (∀ q, Nat.Coprime (a q) q) →     ∑ q ∈ Finset.Icc 1 ⌊Real.sqrt x / Real.log x ^ B⌋₊,       |∑ p ∈ (Finset.range (⌊x⌋₊ + 1)).filter (fun p => p.Prime ∧ p % q = a q % q),           Real.log p - x / (Nat.totient q : ℝ)| ≤ C * x / Real.log x ^ A) →   ∀ r : ℕ, ∃ k : ℕ, ∀ (H : Finset ℕ) (M b : ℕ), k ≤ H.card → 0 < M →     (∀ p, p.Prime → ∃ x, ∀ a ∈ H, ¬ p ∣ M * x + b + a) →     ∀ N : ℕ, ∃ x, N < x ∧ r ≤ (H.filter fun a => (M * x + b + a).Prime).card

namespace MaynardH2

open scoped BigOperators

/-! ### Module 1: Discrete Variational Construction -/

private lemma harmonic_pow_two_ge (n : ℕ) :
    1 + (n : ℝ) / 2 ≤ ∑ j ∈ Finset.range (2 ^ n), (1 : ℝ) / ((j + 1 : ℕ) : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hpow : 2 ^ (n + 1) = 2 ^ n + 2 ^ n := by ring
    rw [hpow, Finset.sum_range_add]
    have htail : (1 : ℝ) / 2 ≤ ∑ j ∈ Finset.range (2 ^ n), (1 : ℝ) / ((2 ^ n + j + 1 : ℕ) : ℝ) := by
      have hterm : ∀ j ∈ Finset.range (2 ^ n),
          (1 : ℝ) / (2 * (2 ^ n : ℝ)) ≤ (1 : ℝ) / ((2 ^ n + j + 1 : ℕ) : ℝ) := by
        intro j hj
        have hjlt : j < 2 ^ n := Finset.mem_range.mp hj
        have hpos : (0 : ℝ) < ((2 ^ n + j + 1 : ℕ) : ℝ) := by positivity
        rw [one_div_le_one_div (by positivity) hpos]
        have hle : 2 ^ n + j + 1 ≤ 2 * 2 ^ n := by omega
        exact_mod_cast hle
      calc (1 : ℝ) / 2
          = (2 ^ n : ℝ) * ((1 : ℝ) / (2 * (2 ^ n : ℝ))) := by
              have hne : (2 ^ n : ℝ) ≠ 0 := by positivity
              field_simp
        _ = ∑ _j ∈ Finset.range (2 ^ n), (1 : ℝ) / (2 * (2 ^ n : ℝ)) := by
              simp [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ∑ j ∈ Finset.range (2 ^ n), (1 : ℝ) / ((2 ^ n + j + 1 : ℕ) : ℝ) :=
              Finset.sum_le_sum hterm
    have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
    rw [hcast]
    linarith

private lemma sum_inv_sq_bounds (B : ℕ) (hB : 1 ≤ B) :
    1 ≤ ∑ j ∈ Finset.range B, (1 : ℝ) / ((j + 1 : ℕ) : ℝ) ^ 2 ∧
    ∑ j ∈ Finset.range B, (1 : ℝ) / ((j + 1 : ℕ) : ℝ) ^ 2 ≤ 2 - 1 / (B : ℝ) := by
  induction B with
  | zero => omega
  | succ n ih =>
    cases n with
    | zero =>
      norm_num
    | succ m =>
      have hm : 1 ≤ m + 1 := by omega
      obtain ⟨hlo, hhi⟩ := ih hm
      rw [Finset.sum_range_succ]
      constructor
      · have hnn : (0 : ℝ) ≤ (1 : ℝ) / ((m + 1 + 1 : ℕ) : ℝ) ^ 2 := by positivity
        linarith
      · have hstep : (1 : ℝ) / ((m + 1 + 1 : ℕ) : ℝ) ^ 2 ≤
            1 / ((m + 1 : ℕ) : ℝ) - 1 / ((m + 1 + 1 : ℕ) : ℝ) := by
          have h1 : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
          have h2 : (0 : ℝ) < ((m + 1 + 1 : ℕ) : ℝ) := by positivity
          have hdiff : 1 / ((m + 1 : ℕ) : ℝ) - 1 / ((m + 1 + 1 : ℕ) : ℝ) =
              1 / (((m + 1 : ℕ) : ℝ) * ((m + 1 + 1 : ℕ) : ℝ)) := by
            field_simp
            push_cast
            ring
          rw [hdiff, one_div_le_one_div (by positivity) (by positivity)]
          have hle : ((m + 1 : ℕ) : ℝ) ≤ ((m + 1 + 1 : ℕ) : ℝ) := by
            exact_mod_cast Nat.le_succ (m + 1)
          nlinarith
        linarith

private lemma pi_sum_weight_factor {k L : ℕ} (hL : 1 ≤ L) (m : Fin k)
    (w : Fin k → Fin L → ℝ) :
    ∑ a ∈ (Finset.univ : Finset (Fin k → Fin L)).filter (fun a => a m = ⟨0, hL⟩),
      ∏ i ∈ Finset.univ.erase m, w i (a i) =
    ∏ i ∈ Finset.univ.erase m, ∑ b : Fin L, w i b := by
  let S : Finset (Fin k) := Finset.univ.erase m
  have hprod : ∏ i ∈ S, ∑ b : Fin L, w i b =
      ∑ f ∈ (Finset.univ : Finset (Fin k → Fin L)).filter (fun f => f m = ⟨0, hL⟩),
        ∏ i ∈ S, w i (f i) := by
    rw [Finset.prod_sum]
    symm
    refine Finset.sum_nbij'
      (fun f => fun i _ => f i)
      (fun g => fun i => if hi : i ∈ S then g i hi else ⟨0, hL⟩)
      ?_ ?_ ?_ ?_ ?_
    · intro f _
      exact Finset.mem_pi.mpr (fun i _ => Finset.mem_univ (f i))
    · intro g _
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by simp [S]⟩
    · intro f hf
      rw [Finset.mem_filter] at hf
      funext i
      by_cases hi : i ∈ S
      · simp [hi]
      · have him : i = m := by
          by_contra hne
          exact hi (Finset.mem_erase.mpr ⟨hne, Finset.mem_univ i⟩)
        subst him
        simp [hi, hf.2]
    · intro g _
      funext i hi
      simp [hi]
    · intro f _
      exact (Finset.prod_attach S (fun i => w i (f i))).symm
  exact hprod.symm

private lemma maynard_weights_from_params (M_target : ℝ) (B k L : ℕ)
    (hB4 : 4 ≤ B) (hkB : k = 4 * B)
    (hS1_gt : 8 * max M_target 0 + 16 < ∑ j ∈ Finset.range B, (1 : ℝ) / ((j + 1 : ℕ) : ℝ))
    (hL_def : L = Nat.ceil (2 * (k : ℝ) *
      ((∑ j ∈ Finset.range B, (1 : ℝ) / ((j + 1 : ℕ) : ℝ)) /
       (∑ j ∈ Finset.range B, (1 : ℝ) / ((j + 1 : ℕ) : ℝ) ^ 2))) + B) :
    ∃ (_ : 1 ≤ k) (hL : 1 ≤ L) (c : (Fin k → Fin L) → ℝ),
      (∀ a, 0 ≤ c a) ∧
      (∀ a, L < ∑ i : Fin k, ((a i).val + 1) → c a = 0) ∧
      0 < ∑ a : Fin k → Fin L, (c a) ^ 2 ∧
      M_target * (∑ a : Fin k → Fin L, (c a) ^ 2) <
        (1 / (L : ℝ)) * ∑ m : Fin k,
          ∑ a ∈ (Finset.univ : Finset (Fin k → Fin L)).filter (fun a => a m = ⟨0, hL⟩),
            (∑ b : Fin L, c (Function.update a m b)) ^ 2 := by
  have hB1 : 1 ≤ B := by omega
  set S0 : ℝ := ∑ j ∈ Finset.range B, (1 : ℝ) / ((j + 1 : ℕ) : ℝ) ^ 2 with hS0_def
  set S1 : ℝ := ∑ j ∈ Finset.range B, (1 : ℝ) / ((j + 1 : ℕ) : ℝ) with hS1_def
  have hS0_bounds := sum_inv_sq_bounds B hB1
  have hS0_ge : 1 ≤ S0 := hS0_bounds.1
  have hS0_lt : S0 < 2 := by
    have hpos : (0 : ℝ) < 1 / (B : ℝ) := by positivity
    linarith [hS0_bounds.2]
  have hS1_gt16 : 16 < S1 := by
    have : 0 ≤ max M_target 0 := le_max_right _ _
    linarith
  set mu : ℝ := S1 / S0 with hmu_def
  have hmu_gt8 : 8 < mu := by
    rw [hmu_def, lt_div_iff₀ (by linarith)]
    linarith
  have hmu_ge1 : 1 ≤ mu := by linarith
  have hk1 : 1 ≤ k := by omega
  have hL_eq : L = Nat.ceil (2 * (k : ℝ) * mu) + B := hL_def
  have hL_ge_2kmu : 2 * (k : ℝ) * mu ≤ ((L - B : ℕ) : ℝ) := by
    have hsub : L - B = Nat.ceil (2 * (k : ℝ) * mu) := by omega
    rw [hsub]
    exact Nat.le_ceil _
  have hL_gt_k : k < L := by
    have h1 : (k : ℝ) < 2 * (k : ℝ) * mu := by
      have hkpos : (0 : ℝ) < (k : ℝ) := by positivity
      nlinarith
    have h2 : 2 * (k : ℝ) * mu ≤ (L : ℝ) := by
      calc 2 * (k : ℝ) * mu ≤ (Nat.ceil (2 * (k : ℝ) * mu) : ℝ) := Nat.le_ceil _
        _ ≤ (L : ℝ) := by
          have hle : Nat.ceil (2 * (k : ℝ) * mu) ≤ L := by omega
          exact_mod_cast hle
    exact_mod_cast lt_of_lt_of_le h1 h2
  have hL1 : 1 ≤ L := by omega
  have hBL : B ≤ L := by omega
  have hL_le : (L : ℝ) ≤ 4 * (k : ℝ) * mu := by
    have hceil : (Nat.ceil (2 * (k : ℝ) * mu) : ℝ) < 2 * (k : ℝ) * mu + 1 :=
      Nat.ceil_lt_add_one (by positivity)
    have hLcast : (L : ℝ) = (Nat.ceil (2 * (k : ℝ) * mu) : ℝ) + (B : ℝ) := by
      rw [hL_eq]; push_cast; ring
    have hkB_r : (k : ℝ) = 4 * (B : ℝ) := by rw [hkB]; push_cast; ring
    have hBpos : (4 : ℝ) ≤ (B : ℝ) := by exact_mod_cast hB4
    nlinarith
  let g : Fin L → ℝ := fun a => if a.val < B then (1 : ℝ) / ((a.val + 1 : ℕ) : ℝ) else 0
  have hg_nonneg : ∀ a, 0 ≤ g a := by
    intro a; dsimp [g]; split_ifs <;> positivity
  have hg_sum_sq : ∑ b : Fin L, (g b) ^ 2 = S0 := by
    calc ∑ b : Fin L, (g b) ^ 2
        = ∑ j ∈ Finset.range L, if j < B then (1 : ℝ) / ((j + 1 : ℕ) : ℝ) ^ 2 else 0 := by
            rw [Fin.sum_univ_eq_sum_range (fun j => (if j < B then (1 : ℝ) / ((j + 1 : ℕ) : ℝ) else 0) ^ 2) L]
            refine Finset.sum_congr rfl (fun j _ => ?_)
            split_ifs <;> ring
      _ = ∑ j ∈ (Finset.range L).filter (· < B), (1 : ℝ) / ((j + 1 : ℕ) : ℝ) ^ 2 := by
            rw [Finset.sum_filter]
      _ = S0 := by
            rw [hS0_def]; congr 1; ext j; simp only [Finset.mem_filter, Finset.mem_range]; omega
  have hg_sum : ∑ b : Fin L, g b = S1 := by
    calc ∑ b : Fin L, g b
        = ∑ j ∈ Finset.range L, if j < B then (1 : ℝ) / ((j + 1 : ℕ) : ℝ) else 0 :=
            Fin.sum_univ_eq_sum_range (fun j => if j < B then (1 : ℝ) / ((j + 1 : ℕ) : ℝ) else 0) L
      _ = ∑ j ∈ (Finset.range L).filter (· < B), (1 : ℝ) / ((j + 1 : ℕ) : ℝ) := by
            rw [Finset.sum_filter]
      _ = S1 := by
            rw [hS1_def]; congr 1; ext j; simp only [Finset.mem_filter, Finset.mem_range]; omega
  have hg_mean : ∑ b : Fin L, ((b.val + 1 : ℕ) : ℝ) * (g b) ^ 2 = S1 := by
    have h1 : ∀ b : Fin L, ((b.val + 1 : ℕ) : ℝ) * (g b) ^ 2 = g b := by
      intro b; dsimp [g]; split_ifs
      · have hne : ((b.val + 1 : ℕ) : ℝ) ≠ 0 := by positivity
        field_simp
      · ring
    simp_rw [h1]
    exact hg_sum
  have hS0_ne : S0 ≠ 0 := by linarith
  have hS1_eq_mu_S0 : S1 = mu * S0 := by
    rw [hmu_def, div_mul_cancel₀ _ hS0_ne]
  have hg_centered : ∑ b : Fin L, (((b.val + 1 : ℕ) : ℝ) - mu) * (g b) ^ 2 = 0 := by
    have h1 : ∑ b : Fin L, (((b.val + 1 : ℕ) : ℝ) - mu) * (g b) ^ 2 =
        (∑ b : Fin L, ((b.val + 1 : ℕ) : ℝ) * (g b) ^ 2) -
        mu * (∑ b : Fin L, (g b) ^ 2) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun b _ => by ring)
    rw [h1, hg_mean, hg_sum_sq, hS1_eq_mu_S0]
    ring
  have hg_var : ∑ b : Fin L, (((b.val + 1 : ℕ) : ℝ) - mu) ^ 2 * (g b) ^ 2 ≤ (B : ℝ) := by
    have h1 : ∑ b : Fin L, (((b.val + 1 : ℕ) : ℝ) - mu) ^ 2 * (g b) ^ 2 =
        (∑ b : Fin L, ((b.val + 1 : ℕ) : ℝ) ^ 2 * (g b) ^ 2) -
        2 * mu * (∑ b : Fin L, ((b.val + 1 : ℕ) : ℝ) * (g b) ^ 2) +
        mu ^ 2 * (∑ b : Fin L, (g b) ^ 2) := by
      simp_rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun b _ => by ring)
    have hsq : ∑ b : Fin L, ((b.val + 1 : ℕ) : ℝ) ^ 2 * (g b) ^ 2 = (B : ℝ) := by
      have hterm : ∀ b : Fin L, ((b.val + 1 : ℕ) : ℝ) ^ 2 * (g b) ^ 2 =
          if b.val < B then (1 : ℝ) else 0 := by
        intro b; dsimp [g]; split_ifs
        · have hne : ((b.val + 1 : ℕ) : ℝ) ≠ 0 := by positivity
          field_simp
        · ring
      simp_rw [hterm]
      rw [Fin.sum_univ_eq_sum_range (fun j => if j < B then (1 : ℝ) else 0) L]
      rw [← Finset.sum_filter]
      have heq : (Finset.range L).filter (· < B) = Finset.range B := by
        ext j; simp only [Finset.mem_filter, Finset.mem_range]; omega
      rw [heq]
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    rw [h1, hsq, hg_mean, hg_sum_sq, hS1_eq_mu_S0]
    have hnn : 0 ≤ mu ^ 2 * S0 := mul_nonneg (sq_nonneg _) (by linarith)
    linarith
  let c : (Fin k → Fin L) → ℝ := fun a =>
    if ∑ i : Fin k, ((a i).val + 1) ≤ L then ∏ i : Fin k, g (a i) else 0
  refine ⟨hk1, hL1, c, ?_, ?_, ?_, ?_⟩
  · intro a; dsimp [c]; split_ifs
    · exact Finset.prod_nonneg (fun i _ => hg_nonneg (a i))
    · linarith
  · intro a hgt
    dsimp [c]
    rw [if_neg (not_le.mpr hgt)]
  · let a0 : Fin k → Fin L := fun _ => ⟨0, hL1⟩
    have ha0 : c a0 = 1 := by
      dsimp [c, a0]
      have hsum : ∑ _i : Fin k, (0 + 1) = k := by simp
      rw [hsum, if_pos (by omega)]
      refine Finset.prod_eq_one (fun i _ => ?_)
      dsimp [g]; rw [if_pos (by omega)]; norm_num
    have hge : (c a0) ^ 2 ≤ ∑ a : Fin k → Fin L, (c a) ^ 2 :=
      Finset.single_le_sum (f := fun a => (c a) ^ 2) (fun a _ => sq_nonneg _) (Finset.mem_univ a0)
    rw [ha0] at hge
    linarith
  · have hI_le : ∑ a : Fin k → Fin L, (c a) ^ 2 ≤ S0 ^ k := by
      calc ∑ a : Fin k → Fin L, (c a) ^ 2
          ≤ ∑ a : Fin k → Fin L, ∏ i : Fin k, (g (a i)) ^ 2 := by
              refine Finset.sum_le_sum (fun a _ => ?_)
              dsimp [c]; split_ifs
              · rw [Finset.prod_pow]
              · rw [zero_pow (by norm_num : 2 ≠ 0)]
                exact Finset.prod_nonneg (fun i _ => sq_nonneg _)
        _ = ∏ _i : Fin k, ∑ b : Fin L, (g b) ^ 2 := by
              rw [Fintype.prod_sum]
        _ = S0 ^ k := by
              simp [hg_sum_sq]
    have hJm_ge : ∀ m : Fin k,
        (1 / 2 : ℝ) * S1 ^ 2 * S0 ^ (k - 1) ≤
        ∑ a ∈ (Finset.univ : Finset (Fin k → Fin L)).filter (fun a => a m = ⟨0, hL1⟩),
          (∑ b : Fin L, c (Function.update a m b)) ^ 2 := by
      intro m
      let Um : Finset (Fin k → Fin L) :=
        (Finset.univ : Finset (Fin k → Fin L)).filter (fun a => a m = ⟨0, hL1⟩)
      let Sm : Finset (Fin k) := Finset.univ.erase m
      have hSm_card : Sm.card = k - 1 := by simp [Sm]
      let W : (Fin k → Fin L) → ℝ := fun a => ∏ i ∈ Sm, (g (a i)) ^ 2
      have hW_nonneg : ∀ a, 0 ≤ W a := fun a => Finset.prod_nonneg (fun i _ => sq_nonneg _)
      have hW_sum : ∑ a ∈ Um, W a = S0 ^ (k - 1) := by
        calc ∑ a ∈ Um, W a
            = ∏ _i ∈ Sm, ∑ b : Fin L, (g b) ^ 2 := pi_sum_weight_factor hL1 m (fun _ b => (g b) ^ 2)
          _ = S0 ^ (k - 1) := by simp [hg_sum_sq, hSm_card]
      let Y : (Fin k → Fin L) → ℕ := fun a => ∑ i ∈ Sm, ((a i).val + 1)
      have hgood : ∀ a ∈ Um, Y a ≤ L - B →
          (∑ b : Fin L, c (Function.update a m b)) ^ 2 = S1 ^ 2 * W a := by
        intro a _ hYa
        have hterm : ∀ b : Fin L, c (Function.update a m b) =
            g b * ∏ i ∈ Sm, g (a i) := by
          intro b
          by_cases hb : b.val < B
          · have hsum_le : ∑ i : Fin k, ((Function.update a m b i).val + 1) ≤ L := by
              rw [← Finset.add_sum_erase _ _ (Finset.mem_univ m)]
              have heq : ∑ i ∈ Sm, ((Function.update a m b i).val + 1) = Y a := by
                refine Finset.sum_congr rfl (fun i hi => ?_)
                have hne : i ≠ m := (Finset.mem_erase.mp hi).1
                simp [Function.update_of_ne hne]
              simp only [Function.update_self]
              rw [heq]
              omega
            dsimp [c]
            rw [if_pos hsum_le, ← Finset.mul_prod_erase _ _ (Finset.mem_univ m)]
            simp only [Function.update_self]
            congr 1
            refine Finset.prod_congr rfl (fun i hi => ?_)
            have hne : i ≠ m := (Finset.mem_erase.mp hi).1
            simp [Function.update_of_ne hne]
          · have hgb : g b = 0 := by dsimp [g]; rw [if_neg hb]
            rw [hgb, zero_mul]
            dsimp [c]
            split_ifs with hle
            · rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ m)]
              simp [Function.update_self, hgb]
            · rfl
        simp_rw [hterm]
        rw [← Finset.sum_mul, hg_sum, mul_pow, ← Finset.prod_pow]
      have hJm_good : S1 ^ 2 * ∑ a ∈ Um.filter (fun a => Y a ≤ L - B), W a ≤
          ∑ a ∈ Um, (∑ b : Fin L, c (Function.update a m b)) ^ 2 := by
        rw [Finset.mul_sum]
        calc ∑ a ∈ Um.filter (fun a => Y a ≤ L - B), S1 ^ 2 * W a
            = ∑ a ∈ Um.filter (fun a => Y a ≤ L - B),
                (∑ b : Fin L, c (Function.update a m b)) ^ 2 := by
              refine Finset.sum_congr rfl (fun a ha => ?_)
              rw [Finset.mem_filter] at ha
              exact (hgood a ha.1 ha.2).symm
          _ ≤ ∑ a ∈ Um, (∑ b : Fin L, c (Function.update a m b)) ^ 2 :=
              Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
                (fun _ _ _ => sq_nonneg _)
      have hvar_sum : ∑ a ∈ Um, ((Y a : ℝ) - ((k - 1 : ℕ) : ℝ) * mu) ^ 2 * W a ≤
          (k : ℝ) * (B : ℝ) * S0 ^ (k - 1) := by
        have hY_rewrite : ∀ a, (Y a : ℝ) - ((k - 1 : ℕ) : ℝ) * mu =
            ∑ i ∈ Sm, ((((a i).val + 1 : ℕ) : ℝ) - mu) := by
          intro a
          dsimp [Y]
          rw [Nat.cast_sum, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, hSm_card]
        simp_rw [hY_rewrite, sq, Finset.sum_mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        have hinner : ∀ i ∈ Sm,
            ∑ a ∈ Um, ∑ j ∈ Sm,
              ((((a i).val + 1 : ℕ) : ℝ) - mu) * ((((a j).val + 1 : ℕ) : ℝ) - mu) * W a ≤
            (B : ℝ) * S0 ^ (k - 2) := by
          intro i hi
          rw [Finset.sum_comm]
          have hpair : ∀ j ∈ Sm,
              ∑ a ∈ Um,
                ((((a i).val + 1 : ℕ) : ℝ) - mu) * ((((a j).val + 1 : ℕ) : ℝ) - mu) * W a =
              if j = i then
                (∑ b : Fin L, (((b.val + 1 : ℕ) : ℝ) - mu) ^ 2 * (g b) ^ 2) * S0 ^ (k - 2)
              else 0 := by
            intro j hj
            by_cases hji : j = i
            · subst j
              rw [if_pos rfl]
              let w : Fin k → Fin L → ℝ := fun r b =>
                if r = i then (((b.val + 1 : ℕ) : ℝ) - mu) ^ 2 * (g b) ^ 2 else (g b) ^ 2
              have hrew : ∀ a,
                  ((((a i).val + 1 : ℕ) : ℝ) - mu) * ((((a i).val + 1 : ℕ) : ℝ) - mu) * W a =
                  ∏ r ∈ Sm, w r (a r) := by
                intro a
                dsimp [W]
                rw [← Finset.mul_prod_erase Sm (fun r => (g (a r)) ^ 2) hi]
                rw [← Finset.mul_prod_erase Sm (fun r => w r (a r)) hi]
                have h1 : w i (a i) = ((((a i).val + 1 : ℕ) : ℝ) - mu) ^ 2 * (g (a i)) ^ 2 := by
                  simp [w]
                have h2 : ∏ r ∈ Sm.erase i, w r (a r) = ∏ r ∈ Sm.erase i, (g (a r)) ^ 2 := by
                  refine Finset.prod_congr rfl (fun r hr => ?_)
                  have hne : r ≠ i := (Finset.mem_erase.mp hr).1
                  simp [w, hne]
                rw [h1, h2]; ring
              simp_rw [hrew]
              rw [pi_sum_weight_factor hL1 m w]
              rw [← Finset.mul_prod_erase Sm _ hi]
              have h1 : ∑ b : Fin L, w i b =
                  ∑ b : Fin L, (((b.val + 1 : ℕ) : ℝ) - mu) ^ 2 * (g b) ^ 2 := by
                simp only [w, ↓reduceIte]
              have h2 : ∏ r ∈ Sm.erase i, ∑ b : Fin L, w r b = S0 ^ (k - 2) := by
                have heq : ∀ r ∈ Sm.erase i, ∑ b : Fin L, w r b = S0 := by
                  intro r hr
                  have hne : r ≠ i := (Finset.mem_erase.mp hr).1
                  simp only [w, hne, ↓reduceIte, hg_sum_sq]
                rw [Finset.prod_congr rfl heq, Finset.prod_const]
                have hcard2 : (Sm.erase i).card = k - 2 := by
                  rw [Finset.card_erase_of_mem hi, hSm_card]; omega
                rw [hcard2]
              rw [h1, h2]
            · rw [if_neg hji]
              let w : Fin k → Fin L → ℝ := fun r b =>
                if r = i ∨ r = j then (((b.val + 1 : ℕ) : ℝ) - mu) * (g b) ^ 2 else (g b) ^ 2
              have hrew : ∀ a,
                  ((((a i).val + 1 : ℕ) : ℝ) - mu) * ((((a j).val + 1 : ℕ) : ℝ) - mu) * W a =
                  ∏ r ∈ Sm, w r (a r) := by
                intro a
                dsimp [W]
                rw [← Finset.mul_prod_erase Sm (fun r => (g (a r)) ^ 2) hi]
                rw [← Finset.mul_prod_erase Sm (fun r => w r (a r)) hi]
                have hj' : j ∈ Sm.erase i := Finset.mem_erase.mpr ⟨hji, hj⟩
                rw [← Finset.mul_prod_erase (Sm.erase i) (fun r => (g (a r)) ^ 2) hj']
                rw [← Finset.mul_prod_erase (Sm.erase i) (fun r => w r (a r)) hj']
                have h1 : w i (a i) = ((((a i).val + 1 : ℕ) : ℝ) - mu) * (g (a i)) ^ 2 := by
                  simp [w]
                have h2 : w j (a j) = ((((a j).val + 1 : ℕ) : ℝ) - mu) * (g (a j)) ^ 2 := by
                  simp [w]
                have h3 : ∏ r ∈ (Sm.erase i).erase j, w r (a r) =
                    ∏ r ∈ (Sm.erase i).erase j, (g (a r)) ^ 2 := by
                  refine Finset.prod_congr rfl (fun r hr => ?_)
                  have hnej : r ≠ j := (Finset.mem_erase.mp hr).1
                  have hnei : r ≠ i := (Finset.mem_erase.mp (Finset.mem_erase.mp hr).2).1
                  simp [w, hnei, hnej]
                rw [h1, h2, h3]; ring
              simp_rw [hrew]
              rw [pi_sum_weight_factor hL1 m w]
              refine Finset.prod_eq_zero hi ?_
              simp only [w, true_or, ↓reduceIte]
              exact hg_centered
          rw [Finset.sum_congr rfl hpair]
          simp only [Finset.sum_ite_eq', hi, ↓reduceIte]
          exact mul_le_mul_of_nonneg_right hg_var (pow_nonneg (by linarith) _)
        calc ∑ i ∈ Sm, ∑ a ∈ Um, ∑ j ∈ Sm,
              ((((a i).val + 1 : ℕ) : ℝ) - mu) * ((((a j).val + 1 : ℕ) : ℝ) - mu) * W a
            ≤ ∑ _i ∈ Sm, (B : ℝ) * S0 ^ (k - 2) := Finset.sum_le_sum hinner
          _ = ((k - 1 : ℕ) : ℝ) * ((B : ℝ) * S0 ^ (k - 2)) := by
              rw [Finset.sum_const, hSm_card, nsmul_eq_mul]
          _ ≤ (k : ℝ) * ((B : ℝ) * S0 ^ (k - 1)) := by
              have hk_le : ((k - 1 : ℕ) : ℝ) ≤ (k : ℝ) := by exact_mod_cast Nat.sub_le k 1
              have hpow_le : S0 ^ (k - 2) ≤ S0 ^ (k - 1) :=
                pow_le_pow_right₀ hS0_ge (by omega)
              have hBnn : (0 : ℝ) ≤ (B : ℝ) := Nat.cast_nonneg B
              have hpnn : 0 ≤ S0 ^ (k - 2) := pow_nonneg (by linarith) (k - 2)
              exact mul_le_mul hk_le (mul_le_mul_of_nonneg_left hpow_le hBnn)
                (mul_nonneg hBnn hpnn) (Nat.cast_nonneg k)
          _ = (k : ℝ) * (B : ℝ) * S0 ^ (k - 1) := by ring
      have hbad : ∑ a ∈ Um.filter (fun a => ¬ Y a ≤ L - B), W a ≤ (1 / 2 : ℝ) * S0 ^ (k - 1) := by
        have hkpos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr hk1
        have hBpos : (0 : ℝ) < (B : ℝ) := Nat.cast_pos.mpr hB1
        have hkmu_pos : 0 < (k : ℝ) * mu := mul_pos hkpos (by linarith)
        have hmarkov : ((k : ℝ) * mu) ^ 2 * ∑ a ∈ Um.filter (fun a => ¬ Y a ≤ L - B), W a ≤
            ∑ a ∈ Um, ((Y a : ℝ) - ((k - 1 : ℕ) : ℝ) * mu) ^ 2 * W a := by
          rw [Finset.mul_sum]
          calc ∑ a ∈ Um.filter (fun a => ¬ Y a ≤ L - B), ((k : ℝ) * mu) ^ 2 * W a
              ≤ ∑ a ∈ Um.filter (fun a => ¬ Y a ≤ L - B),
                  ((Y a : ℝ) - ((k - 1 : ℕ) : ℝ) * mu) ^ 2 * W a := by
                refine Finset.sum_le_sum (fun a ha => ?_)
                rw [Finset.mem_filter] at ha
                have hYgt : ((L - B : ℕ) : ℝ) < (Y a : ℝ) := by exact_mod_cast not_le.mp ha.2
                have hdiff : (k : ℝ) * mu ≤ (Y a : ℝ) - ((k - 1 : ℕ) : ℝ) * mu := by
                  have hksub : ((k - 1 : ℕ) : ℝ) ≤ (k : ℝ) := by exact_mod_cast Nat.sub_le k 1
                  have hmul : ((k - 1 : ℕ) : ℝ) * mu ≤ (k : ℝ) * mu :=
                    mul_le_mul_of_nonneg_right hksub (by linarith)
                  linarith
                have hsq : ((k : ℝ) * mu) ^ 2 ≤ ((Y a : ℝ) - ((k - 1 : ℕ) : ℝ) * mu) ^ 2 := by
                  rw [sq, sq]
                  exact mul_self_le_mul_self (le_of_lt hkmu_pos) hdiff
                exact mul_le_mul_of_nonneg_right hsq (hW_nonneg a)
            _ ≤ ∑ a ∈ Um, ((Y a : ℝ) - ((k - 1 : ℕ) : ℝ) * mu) ^ 2 * W a :=
                Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
                  (fun a _ _ => mul_nonneg (sq_nonneg _) (hW_nonneg a))
        have hcomb : ((k : ℝ) * mu) ^ 2 * ∑ a ∈ Um.filter (fun a => ¬ Y a ≤ L - B), W a ≤
            (k : ℝ) * (B : ℝ) * S0 ^ (k - 1) := hmarkov.trans hvar_sum
        have hkB_r : (k : ℝ) = 4 * (B : ℝ) := by rw [hkB]; push_cast; ring
        have hden : (0 : ℝ) < ((k : ℝ) * mu) ^ 2 := sq_pos_of_pos hkmu_pos
        have hle1 : (k : ℝ) * (B : ℝ) ≤ (1 / 2 : ℝ) * ((k : ℝ) * mu) ^ 2 := by
          have hmu2 : 1 ≤ mu ^ 2 := by
            rw [sq]; exact one_le_mul_of_one_le_of_one_le hmu_ge1 hmu_ge1
          have hk2 : (k : ℝ) * (B : ℝ) = (1 / 4 : ℝ) * (k : ℝ) ^ 2 := by rw [hkB_r]; ring
          have h1 : (1 / 4 : ℝ) * (k : ℝ) ^ 2 ≤ (1 / 2 : ℝ) * (k : ℝ) ^ 2 := by
            have := sq_nonneg (k : ℝ); linarith
          have h2 : (1 / 2 : ℝ) * (k : ℝ) ^ 2 ≤ (1 / 2 : ℝ) * ((k : ℝ) * mu) ^ 2 := by
            rw [mul_pow]
            have h3 : (k : ℝ) ^ 2 * 1 ≤ (k : ℝ) ^ 2 * mu ^ 2 :=
              mul_le_mul_of_nonneg_left hmu2 (sq_nonneg _)
            linarith
          linarith
        have hcomb2 : ((k : ℝ) * mu) ^ 2 * ∑ a ∈ Um.filter (fun a => ¬ Y a ≤ L - B), W a ≤
            ((k : ℝ) * mu) ^ 2 * ((1 / 2 : ℝ) * S0 ^ (k - 1)) := by
          calc ((k : ℝ) * mu) ^ 2 * ∑ a ∈ Um.filter (fun a => ¬ Y a ≤ L - B), W a
              ≤ (k : ℝ) * (B : ℝ) * S0 ^ (k - 1) := hcomb
            _ ≤ (1 / 2 : ℝ) * ((k : ℝ) * mu) ^ 2 * S0 ^ (k - 1) :=
                mul_le_mul_of_nonneg_right hle1 (pow_nonneg (by linarith) _)
            _ = ((k : ℝ) * mu) ^ 2 * ((1 / 2 : ℝ) * S0 ^ (k - 1)) := by ring
        exact le_of_mul_le_mul_left hcomb2 hden
      have hsplit : ∑ a ∈ Um.filter (fun a => Y a ≤ L - B), W a +
          ∑ a ∈ Um.filter (fun a => ¬ Y a ≤ L - B), W a = S0 ^ (k - 1) := by
        rw [Finset.sum_filter_add_sum_filter_not, hW_sum]
      have hgood_ge : (1 / 2 : ℝ) * S0 ^ (k - 1) ≤
          ∑ a ∈ Um.filter (fun a => Y a ≤ L - B), W a := by linarith
      calc (1 / 2 : ℝ) * S1 ^ 2 * S0 ^ (k - 1)
          = S1 ^ 2 * ((1 / 2 : ℝ) * S0 ^ (k - 1)) := by ring
        _ ≤ S1 ^ 2 * ∑ a ∈ Um.filter (fun a => Y a ≤ L - B), W a :=
            mul_le_mul_of_nonneg_left hgood_ge (sq_nonneg S1)
        _ ≤ ∑ a ∈ Um, (∑ b : Fin L, c (Function.update a m b)) ^ 2 := hJm_good
    have hsum_Jm : (k : ℝ) * ((1 / 2 : ℝ) * S1 ^ 2 * S0 ^ (k - 1)) ≤
        ∑ m : Fin k,
          ∑ a ∈ (Finset.univ : Finset (Fin k → Fin L)).filter (fun a => a m = ⟨0, hL1⟩),
            (∑ b : Fin L, c (Function.update a m b)) ^ 2 := by
      calc (k : ℝ) * ((1 / 2 : ℝ) * S1 ^ 2 * S0 ^ (k - 1))
          = ∑ _m : Fin k, ((1 / 2 : ℝ) * S1 ^ 2 * S0 ^ (k - 1)) := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        _ ≤ _ := Finset.sum_le_sum (fun m _ => hJm_ge m)
    have hS0_pow : S0 ^ k = S0 * S0 ^ (k - 1) := by
      conv_lhs => rw [show k = (k - 1) + 1 by omega, pow_succ, mul_comm]
    have hLHS : M_target * (∑ a : Fin k → Fin L, (c a) ^ 2) ≤ (max M_target 0) * S0 ^ k := by
      have hInn : 0 ≤ ∑ a : Fin k → Fin L, (c a) ^ 2 :=
        Finset.sum_nonneg (fun a _ => sq_nonneg _)
      calc M_target * (∑ a : Fin k → Fin L, (c a) ^ 2)
          ≤ (max M_target 0) * (∑ a : Fin k → Fin L, (c a) ^ 2) :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) hInn
        _ ≤ (max M_target 0) * S0 ^ k :=
            mul_le_mul_of_nonneg_left hI_le (le_max_right _ _)
    have hmid : (max M_target 0) * S0 ^ k <
        (1 / (L : ℝ)) * ((k : ℝ) * ((1 / 2 : ℝ) * S1 ^ 2 * S0 ^ (k - 1))) := by
      have hLpos : (0 : ℝ) < (L : ℝ) := Nat.cast_pos.mpr hL1
      rw [one_div_mul_eq_div, lt_div_iff₀' hLpos]
      have hS0pos : 0 < S0 ^ (k - 1) := pow_pos (by linarith) (k - 1)
      have hkpos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr hk1
      have hfac : 0 < (k : ℝ) * mu * S0 * S0 ^ (k - 1) :=
        mul_pos (mul_pos (mul_pos hkpos (by linarith)) (by linarith)) hS0pos
      have hkey : (L : ℝ) * ((max M_target 0) * S0 ^ k) <
          (k : ℝ) * ((1 / 2 : ℝ) * S1 ^ 2 * S0 ^ (k - 1)) := by
        calc (L : ℝ) * ((max M_target 0) * S0 ^ k)
            ≤ (4 * (k : ℝ) * mu) * ((max M_target 0) * S0 ^ k) :=
              mul_le_mul_of_nonneg_right hL_le
                (mul_nonneg (le_max_right _ _) (pow_nonneg (by linarith) k))
          _ = ((k : ℝ) * mu * S0 * S0 ^ (k - 1)) * (4 * max M_target 0) := by
              rw [hS0_pow]; ring
          _ < ((k : ℝ) * mu * S0 * S0 ^ (k - 1)) * ((1 / 2 : ℝ) * S1) :=
              mul_lt_mul_of_pos_left (by linarith) hfac
          _ = (k : ℝ) * ((1 / 2 : ℝ) * S1 ^ 2 * S0 ^ (k - 1)) := by
              rw [hS1_eq_mu_S0]; ring
      exact hkey
    have hRHS : (1 / (L : ℝ)) * ((k : ℝ) * ((1 / 2 : ℝ) * S1 ^ 2 * S0 ^ (k - 1))) ≤
        (1 / (L : ℝ)) * ∑ m : Fin k,
          ∑ a ∈ (Finset.univ : Finset (Fin k → Fin L)).filter (fun a => a m = ⟨0, hL1⟩),
            (∑ b : Fin L, c (Function.update a m b)) ^ 2 :=
      mul_le_mul_of_nonneg_left hsum_Jm (one_div_nonneg.mpr (Nat.cast_nonneg L))
    linarith

private lemma exists_maynard_weights (M_target : ℝ) :
    ∃ (k L : ℕ) (_ : 1 ≤ k) (hL : 1 ≤ L) (c : (Fin k → Fin L) → ℝ),
      (∀ a, 0 ≤ c a) ∧
      (∀ a, L < ∑ i : Fin k, ((a i).val + 1) → c a = 0) ∧
      0 < ∑ a : Fin k → Fin L, (c a) ^ 2 ∧
      M_target * (∑ a : Fin k → Fin L, (c a) ^ 2) <
        (1 / (L : ℝ)) * ∑ m : Fin k,
          ∑ a ∈ (Finset.univ : Finset (Fin k → Fin L)).filter (fun a => a m = ⟨0, hL⟩),
            (∑ b : Fin L, c (Function.update a m b)) ^ 2 := by
  let n : ℕ := max 2 (Nat.ceil (16 * max M_target 0 + 32))
  let B : ℕ := 2 ^ n
  have hn2 : 2 ≤ n := le_max_left _ _
  have hB4 : 4 ≤ B := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
  have hS1_gt : 8 * max M_target 0 + 16 < ∑ j ∈ Finset.range B, (1 : ℝ) / ((j + 1 : ℕ) : ℝ) := by
    have h1 := harmonic_pow_two_ge n
    have h2 : 16 * max M_target 0 + 32 ≤ (n : ℝ) := by
      calc 16 * max M_target 0 + 32
          ≤ (Nat.ceil (16 * max M_target 0 + 32) : ℝ) := Nat.le_ceil _
        _ ≤ (n : ℝ) := by exact_mod_cast le_max_right 2 _
    linarith
  let k : ℕ := 4 * B
  let L : ℕ := Nat.ceil (2 * (k : ℝ) *
    ((∑ j ∈ Finset.range B, (1 : ℝ) / ((j + 1 : ℕ) : ℝ)) /
     (∑ j ∈ Finset.range B, (1 : ℝ) / ((j + 1 : ℕ) : ℝ) ^ 2))) + B
  obtain ⟨hk1, hL1, c, hc⟩ := maynard_weights_from_params M_target B k L hB4 rfl hS1_gt rfl
  exact ⟨k, L, hk1, hL1, c, hc⟩

/-! ### Module 2: Harmonic convolution for the reciprocal totient weights -/

open scoped BigOperators ArithmeticFunction.Moebius ArithmeticFunction.zeta
open ArithmeticFunction

private noncomputable def reciprocal : ArithmeticFunction ℝ :=
  ⟨fun n => (n : ℝ)⁻¹, by simp⟩

private lemma reciprocal_mul (a b : ℕ) :
    reciprocal (a * b) = reciprocal a * reciprocal b := by
  change ((↑(a * b) : ℝ))⁻¹ = (a : ℝ)⁻¹ * (b : ℝ)⁻¹
  rw [Nat.cast_mul, mul_inv]

private lemma reciprocal_mult : reciprocal.IsMultiplicative :=
  ⟨by simp [reciprocal], fun {_ _} _ => reciprocal_mul _ _⟩

private lemma reciprocal_pmul_convolution (f g : ArithmeticFunction ℝ) :
    (f * g).pmul reciprocal = f.pmul reciprocal * g.pmul reciprocal := by
  ext n
  simp only [pmul_apply, mul_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun x hx => ?_)
  rw [← (Nat.mem_divisorsAntidiagonal.mp hx).1, reciprocal_mul]
  ring

private noncomputable def sqfreeTotient (W : ℕ) : ArithmeticFunction ℝ := by
  classical
  exact ⟨fun n => if Squarefree n ∧ n.Coprime W then ((n.totient : ℝ))⁻¹ else 0, by simp⟩

private lemma sqfreeTotient_mult (W : ℕ) : (sqfreeTotient W).IsMultiplicative := by
  classical
  refine ⟨by simp [sqfreeTotient], ?_⟩
  intro a b hab
  change (if Squarefree (a * b) ∧ (a * b).Coprime W
      then (↑(a * b).totient : ℝ)⁻¹ else 0) =
    (if Squarefree a ∧ a.Coprime W then (↑a.totient : ℝ)⁻¹ else 0) *
    (if Squarefree b ∧ b.Coprime W then (↑b.totient : ℝ)⁻¹ else 0)
  have hc : (Squarefree (a * b) ∧ (a * b).Coprime W) ↔
      (Squarefree a ∧ a.Coprime W) ∧ (Squarefree b ∧ b.Coprime W) := by
    rw [Nat.squarefree_mul hab, Nat.coprime_mul_iff_left]
    tauto
  rw [Nat.totient_mul hab, Nat.cast_mul, mul_inv]
  by_cases ha : Squarefree a ∧ a.Coprime W
  · by_cases hb : Squarefree b ∧ b.Coprime W
    · rw [if_pos (hc.mpr ⟨ha, hb⟩), if_pos ha, if_pos hb]
    · rw [if_neg (fun h => hb (hc.mp h).2), if_pos ha, if_neg hb, mul_zero]
  · rw [if_neg (fun h => ha (hc.mp h).1), if_neg ha, zero_mul]

private noncomputable def totientCorrection (W : ℕ) : ArithmeticFunction ℝ :=
  ((μ : ArithmeticFunction ℝ).pmul reciprocal) * sqfreeTotient W

private lemma totientCorrection_mult (W : ℕ) : (totientCorrection W).IsMultiplicative :=
  (isMultiplicative_moebius.intCast.pmul reciprocal_mult).mul (sqfreeTotient_mult W)

private lemma totientCorrection_convolution (W : ℕ) :
    totientCorrection W * reciprocal = sqfreeTotient W := by
  have hzeta : (ζ : ArithmeticFunction ℝ).pmul reciprocal = reciprocal := zeta_pmul _
  have hone : (1 : ArithmeticFunction ℝ).pmul reciprocal = 1 := by
    ext n
    rw [pmul_apply]
    by_cases hn : n = 1 <;> simp [hn, one_apply, reciprocal]
  have hinv : (μ : ArithmeticFunction ℝ).pmul reciprocal * reciprocal = 1 := by
    calc
      _ = (μ : ArithmeticFunction ℝ).pmul reciprocal * (ζ : ArithmeticFunction ℝ).pmul reciprocal := by
        rw [hzeta]
      _ = 1 := by rw [← reciprocal_pmul_convolution, coe_moebius_mul_coe_zeta, hone]
  rw [totientCorrection, mul_right_comm, hinv, one_mul]

private lemma convolution_prime_pow_succ (f g : ArithmeticFunction ℝ) {p : ℕ}
    (hp : p.Prime) (k : ℕ)
    (hf₁ : f 1 = 1) (hf : ∀ j : ℕ, 2 ≤ j → f (p ^ j) = 0) :
    (f * g) (p ^ (k + 1)) = g (p ^ (k + 1)) + f p * g (p ^ k) := by
  rw [mul_apply, Nat.sum_divisorsAntidiagonal (fun a b => f a * g b), Nat.sum_divisors_prime_pow hp,
    Finset.sum_range_succ', Finset.sum_range_succ']
  simp only [pow_zero, hf₁, one_mul, Nat.div_one, zero_add]
  have hzero : ∑ j ∈ Finset.range k, f (p ^ (j + 1 + 1)) * g (p ^ (k + 1) / p ^ (j + 1 + 1)) = 0 := by
    exact Finset.sum_eq_zero (fun j _ => by rw [hf _ (by omega), zero_mul])
  rw [hzero, zero_add, pow_one, pow_succ, Nat.mul_div_cancel _ hp.pos]
  ac_rfl

private lemma totientCorrection_prime_pow_succ (W : ℕ) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    totientCorrection W (p ^ (k + 1)) =
      sqfreeTotient W (p ^ (k + 1)) - reciprocal p * sqfreeTotient W (p ^ k) := by
  unfold totientCorrection
  rw [convolution_prime_pow_succ _ _ hp k]
  · rw [pmul_apply, intCoe_apply, moebius_apply_prime hp, Int.cast_neg, Int.cast_one]
    ring
  · rw [pmul_apply]
    simp [reciprocal]
  · intro j hj
    rw [pmul_apply, intCoe_apply, moebius_apply_prime_pow hp (by omega), if_neg (by omega),
      Int.cast_zero, zero_mul]

private lemma sqfreeTotient_one (W : ℕ) : sqfreeTotient W 1 = 1 :=
  (sqfreeTotient_mult W).1

private lemma sqfreeTotient_prime (W : ℕ) {p : ℕ} (hp : p.Prime) :
    sqfreeTotient W p = if p ∣ W then 0 else ((p : ℝ) - 1)⁻¹ := by
  classical
  unfold sqfreeTotient
  change (if Squarefree p ∧ p.Coprime W then (↑p.totient : ℝ)⁻¹ else 0) = _
  rw [Nat.totient_prime hp, Nat.cast_sub hp.one_le, Nat.cast_one]
  by_cases h : p ∣ W
  · simp only [if_pos h, if_neg (fun hc : Squarefree p ∧ p.Coprime W =>
      (hp.coprime_iff_not_dvd.mp hc.2) h)]
  · rw [if_neg h, if_pos ⟨hp.squarefree, hp.coprime_iff_not_dvd.mpr h⟩]

private lemma sqfreeTotient_prime_pow (W : ℕ) {p k : ℕ} (hp : p.Prime) (hk : 2 ≤ k) :
    sqfreeTotient W (p ^ k) = 0 := by
  have hsf : ¬ Squarefree (p ^ k) := by
    rw [Nat.squarefree_pow_iff hp.ne_one (by omega)]
    exact fun h => by omega
  simp [sqfreeTotient, hsf]

private lemma totientCorrection_prime (W : ℕ) {p : ℕ} (hp : p.Prime) :
    totientCorrection W p =
      if p ∣ W then - (p : ℝ)⁻¹ else ((p : ℝ) * ((p : ℝ) - 1))⁻¹ := by
  have h := totientCorrection_prime_pow_succ W hp 0
  simp only [pow_zero, zero_add, pow_one] at h
  rw [h, sqfreeTotient_one, mul_one, sqfreeTotient_prime W hp]
  change (if p ∣ W then 0 else ((p : ℝ) - 1)⁻¹) - (p : ℝ)⁻¹ = _
  by_cases hd : p ∣ W
  · simp [hd]
  · rw [if_neg hd, if_neg hd]
    have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    have ha : (p : ℝ) ≠ 0 := by linarith
    have hb : (p : ℝ) - 1 ≠ 0 := by linarith
    field_simp
    ring

private lemma totientCorrection_prime_sq (W : ℕ) {p : ℕ} (hp : p.Prime) :
    totientCorrection W (p ^ 2) =
      if p ∣ W then 0 else - ((p : ℝ) * ((p : ℝ) - 1))⁻¹ := by
  rw [show (2 : ℕ) = 1 + 1 by rfl, totientCorrection_prime_pow_succ W hp,
    sqfreeTotient_prime_pow W hp (by decide), pow_one, sqfreeTotient_prime W hp]
  change 0 - (p : ℝ)⁻¹ * (if p ∣ W then 0 else ((p : ℝ) - 1)⁻¹) = _
  by_cases hd : p ∣ W <;> simp [hd, mul_comm]

private lemma totientCorrection_prime_pow_ge_three (W : ℕ) {p k : ℕ}
    (hp : p.Prime) (hk : 3 ≤ k) : totientCorrection W (p ^ k) = 0 := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  rw [totientCorrection_prime_pow_succ W hp, sqfreeTotient_prime_pow W hp (by omega),
    sqfreeTotient_prime_pow W hp (by omega), mul_zero, sub_zero]

private lemma tsum_prime_pow_of_vanish {f : ℕ → ℝ} {p : ℕ}
    (hf : ∀ k, 3 ≤ k → f (p ^ k) = 0) :
    Summable (fun k : ℕ => f (p ^ k)) ∧
    (∑' k : ℕ, f (p ^ k)) = f 1 + f p + f (p ^ 2) := by
  have hzero : ∀ k ∉ Finset.range 3, f (p ^ k) = 0 :=
    fun k hk => hf k (by simpa using hk)
  refine ⟨summable_of_ne_finset_zero hzero, ?_⟩
  rw [tsum_eq_sum hzero]
  simp [Finset.sum_range_succ]

private lemma totientCorrection_local_mass (W : ℕ) {p : ℕ} (hp : p.Prime) :
    (∑' k : ℕ, totientCorrection W (p ^ k)) =
      if p ∣ W then 1 - (p : ℝ)⁻¹ else 1 := by
  rw [(tsum_prime_pow_of_vanish (fun _ hk => totientCorrection_prime_pow_ge_three W hp hk)).2,
    (totientCorrection_mult W).1, totientCorrection_prime W hp, totientCorrection_prime_sq W hp]
  by_cases hd : p ∣ W <;> simp [hd, sub_eq_add_neg]

private lemma summable_of_local_mass_bound {f : ℕ → ℝ} (hf₀ : f 0 = 0) (hf₁ : f 1 = 1)
    (hf : ∀ n, 0 ≤ f n) (hmul : ∀ {m n}, m.Coprime n → f (m * n) = f m * f n)
    {b : ℕ → ℝ} (hb : ∀ n, 0 ≤ b n) (hbs : Summable b)
    (hs : ∀ p : ℕ, p.Prime → Summable (fun k : ℕ => f (p ^ k)))
    (hle : ∀ p : ℕ, p.Prime → (∑' k : ℕ, f (p ^ k)) ≤ 1 + b p) :
    Summable f := by
  classical
  refine summable_of_sum_range_le hf (c := Real.exp (∑' p, b p)) fun N => ?_
  obtain ⟨hsm, hsum⟩ := EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_tsum
    hf₁ (fun {m n} h => hmul h) (fun {p} hp => by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (hf _)] using hs p hp) N
  have hsub : Summable (fun n : N.smoothNumbers => f n) := hsm.of_norm
  let S := (Finset.range N).erase 0
  let e : {n // n ∈ S} ↪ N.smoothNumbers :=
    ⟨fun n => ⟨n, Nat.mem_smoothNumbers_of_lt
      (Nat.pos_of_ne_zero (Finset.mem_erase.mp n.2).1)
      (Finset.mem_range.mp (Finset.mem_of_mem_erase n.2))⟩,
      fun _ _ h => Subtype.ext (congrArg (fun z : N.smoothNumbers => (z : ℕ)) h)⟩
  have hS : ∑ n ∈ S, f n = ∑ n ∈ S.attach.map e, f n := by
    rw [Finset.sum_map]
    exact (Finset.sum_attach S f).symm
  have he : ∑ n ∈ Finset.range N, f n = ∑ n ∈ S, f n := by
    change _ = ∑ n ∈ (Finset.range N).erase 0, f n
    by_cases hN : 0 ∈ Finset.range N
    · rw [← Finset.sum_erase_add _ f hN, hf₀, add_zero]
    · rw [Finset.erase_eq_of_notMem hN]
  rw [he, hS]
  calc
    ∑ n ∈ S.attach.map e, f n ≤ ∑' n : N.smoothNumbers, f n :=
      hsub.sum_le_tsum _ (fun n _ => hf n)
    _ = ∏ p ∈ N.primesBelow, ∑' k : ℕ, f (p ^ k) := hsum.tsum_eq
    _ ≤ ∏ p ∈ N.primesBelow, Real.exp (b p) := by
      refine Finset.prod_le_prod (fun p _ => tsum_nonneg (fun _ => hf _)) (fun p hp => ?_)
      exact (hle p (Nat.prime_of_mem_primesBelow hp)).trans (by simpa [add_comm] using Real.add_one_le_exp (b p))
    _ = Real.exp (∑ p ∈ N.primesBelow, b p) := by rw [Real.exp_sum]
    _ ≤ Real.exp (∑' p, b p) := Real.exp_le_exp.mpr (hbs.sum_le_tsum _ fun p _ => hb p)

private noncomputable def weightedCorrection (W n : ℕ) : ℝ :=
  |totientCorrection W n| * (n : ℝ) ^ (1 / 4 : ℝ)

private lemma weightedCorrection_nonneg (W n : ℕ) : 0 ≤ weightedCorrection W n :=
  mul_nonneg (abs_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg n) _)

private lemma weightedCorrection_one (W : ℕ) : weightedCorrection W 1 = 1 := by
  simp [weightedCorrection, (totientCorrection_mult W).1]

private lemma weightedCorrection_mul (W : ℕ) {a b : ℕ} (h : a.Coprime b) :
    weightedCorrection W (a * b) = weightedCorrection W a * weightedCorrection W b := by
  rw [weightedCorrection, weightedCorrection, weightedCorrection,
    (totientCorrection_mult W).2 h, abs_mul, Nat.cast_mul,
    Real.mul_rpow (Nat.cast_nonneg a) (Nat.cast_nonneg b)]
  ring

private lemma weightedCorrection_pow_ge_three (W : ℕ) {p k : ℕ} (hp : p.Prime) (hk : 3 ≤ k) :
    weightedCorrection W (p ^ k) = 0 := by
  simp [weightedCorrection, totientCorrection_prime_pow_ge_three W hp hk]

private lemma weightedCorrection_local_mass_le {W : ℕ} (hW : 0 < W) {p : ℕ} (hp : p.Prime) :
    (∑' k : ℕ, weightedCorrection W (p ^ k)) ≤
      1 + max 4 (W : ℝ) * (p : ℝ) ^ (-3 / 2 : ℝ) := by
  rw [(tsum_prime_pow_of_vanish (fun _ hk => weightedCorrection_pow_ge_three W hp hk)).2,
    weightedCorrection_one]
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ) < p := by linarith
  have hp1 : (1 : ℝ) ≤ p := by linarith
  have ha : (0 : ℝ) < p - 1 := by linarith
  have hpow : (p : ℝ) ^ (1 / 4 : ℝ) ≤ (p : ℝ) ^ (1 / 2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hp1 (by norm_num)
  have hsq : (((p ^ 2 : ℕ) : ℝ)) ^ (1 / 4 : ℝ) = (p : ℝ) ^ (1 / 2 : ℝ) := by
    rw [Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_mul hp0.le]
    norm_num
  have hnn : 0 ≤ (p : ℝ) ^ (-3 / 2 : ℝ) := Real.rpow_nonneg hp0.le _
  by_cases hd : p ∣ W
  · simp only [weightedCorrection, totientCorrection_prime W hp, totientCorrection_prime_sq W hp,
      if_pos hd, abs_neg, abs_of_pos (inv_pos.mpr hp0), abs_zero, zero_mul, add_zero]
    have hpW : (p : ℝ) ≤ W := by exact_mod_cast Nat.le_of_dvd hW hd
    have he : (p : ℝ)⁻¹ * (p : ℝ) ^ (1 / 2 : ℝ) = (p : ℝ) * (p : ℝ) ^ (-3 / 2 : ℝ) := by
      conv_lhs => rw [← Real.rpow_neg_one, ← Real.rpow_add hp0]
      rw [show (-1 : ℝ) + 1 / 2 = 1 + -3 / 2 by norm_num, Real.rpow_add hp0, Real.rpow_one]
    have h := (mul_le_mul_of_nonneg_left hpow (inv_nonneg.mpr hp0.le)).trans
      (he.trans_le (mul_le_mul_of_nonneg_right (hpW.trans (le_max_right (4 : ℝ) _)) hnn))
    linarith
  · rw [show weightedCorrection W p =
        ((p : ℝ) * ((p : ℝ) - 1))⁻¹ * (p : ℝ) ^ (1 / 4 : ℝ) by
      rw [weightedCorrection, totientCorrection_prime W hp, if_neg hd,
        abs_of_pos (inv_pos.mpr (mul_pos hp0 ha))]]
    rw [show weightedCorrection W (p ^ 2) =
        ((p : ℝ) * ((p : ℝ) - 1))⁻¹ * (p : ℝ) ^ (1 / 2 : ℝ) by
      rw [weightedCorrection, totientCorrection_prime_sq W hp, if_neg hd, abs_neg,
        abs_of_pos (inv_pos.mpr (mul_pos hp0 ha)), hsq]]
    have hden : ((p : ℝ) * ((p : ℝ) - 1))⁻¹ ≤ 2 * ((p : ℝ) ^ 2)⁻¹ := by
      rw [inv_eq_one_div, inv_eq_one_div, mul_one_div, div_le_div_iff₀ (mul_pos hp0 ha) (sq_pos_of_pos hp0)]
      nlinarith [mul_nonneg hp0.le (show 0 ≤ (p : ℝ) - 2 by linarith)]
    have he : ((p : ℝ) ^ 2)⁻¹ * (p : ℝ) ^ (1 / 2 : ℝ) = (p : ℝ) ^ (-3 / 2 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_neg hp0.le, ← Real.rpow_add hp0]
      norm_num
    have key := mul_le_mul_of_nonneg_right hden (Real.rpow_nonneg hp0.le (1 / 2 : ℝ))
    rw [mul_assoc, he] at key
    have hsmall := mul_le_mul_of_nonneg_left hpow (inv_nonneg.mpr (mul_nonneg hp0.le ha.le))
    have hmax := mul_le_mul_of_nonneg_right (le_max_left (4 : ℝ) (W : ℝ)) hnn
    linarith

private lemma weightedCorrection_summable {W : ℕ} (hW : 0 < W) :
    Summable (weightedCorrection W) := by
  apply summable_of_local_mass_bound (by simp [weightedCorrection]) (weightedCorrection_one W)
    (weightedCorrection_nonneg W) (fun h => weightedCorrection_mul W h)
    (b := fun p : ℕ => max 4 (W : ℝ) * (p : ℝ) ^ (-3 / 2 : ℝ))
  · exact fun n => mul_nonneg (le_trans (by norm_num) (le_max_left _ _))
      (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  · exact (Real.summable_nat_rpow.mpr (by norm_num)).mul_left _
  · exact fun _ hp => (tsum_prime_pow_of_vanish
      (fun _ hk => weightedCorrection_pow_ge_three W hp hk)).1
  · exact fun _ hp => weightedCorrection_local_mass_le hW hp

private lemma totientCorrection_norm_moment {W : ℕ} (hW : 0 < W) :
    Summable (fun n : ℕ => |totientCorrection W n| * (1 + Real.log n)) := by
  refine ((weightedCorrection_summable hW).mul_left 5).of_nonneg_of_le
    (fun n => mul_nonneg (abs_nonneg _) (by linarith [Real.log_natCast_nonneg n])) ?_
  intro n
  by_cases hn : n = 0
  · subst n
    simp [weightedCorrection]
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
  have hr := Real.rpow_le_rpow_of_exponent_le hn1 (show (0 : ℝ) ≤ 1 / 4 by norm_num)
  rw [Real.rpow_zero] at hr
  have hl := Real.log_natCast_le_rpow_div n (show (0 : ℝ) < 1 / 4 by norm_num)
  unfold weightedCorrection
  rw [mul_left_comm]
  exact mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)

private lemma totientCorrection_norm_summable {W : ℕ} (hW : 0 < W) :
    Summable (fun n : ℕ => ‖totientCorrection W n‖) := by
  refine (totientCorrection_norm_moment hW).of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
  rw [Real.norm_eq_abs]
  conv_lhs => rw [← mul_one |totientCorrection W n|]
  exact mul_le_mul_of_nonneg_left (by linarith [Real.log_natCast_nonneg n]) (abs_nonneg _)

private lemma totient_prime_factor_product {W : ℕ} (hW : 0 < W) :
    ∏ p ∈ W.primeFactors, (1 - (p : ℝ)⁻¹) = (W.totient : ℝ) / W := by
  have hprod : (0 : ℝ) < ∏ p ∈ W.primeFactors, (p : ℝ) :=
    Finset.prod_pos (fun p hp => Nat.cast_pos.mpr (Nat.pos_of_mem_primeFactors hp))
  have hcast : (W.totient : ℝ) * (∏ p ∈ W.primeFactors, (p : ℝ)) =
      W * ∏ p ∈ W.primeFactors, ((p - 1 : ℕ) : ℝ) := by
    rw [← Nat.cast_prod, ← Nat.cast_prod, ← Nat.cast_mul, ← Nat.cast_mul,
      Nat.totient_mul_prod_primeFactors]
  calc
    ∏ p ∈ W.primeFactors, (1 - (p : ℝ)⁻¹) =
        ∏ p ∈ W.primeFactors, ((p - 1 : ℕ) : ℝ) / (p : ℝ) := by
      refine Finset.prod_congr rfl (fun p hp => ?_)
      rw [Nat.cast_sub (Nat.prime_of_mem_primeFactors hp).one_le, Nat.cast_one]
      have hp0 : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.prime_of_mem_primeFactors hp).ne_zero
      field_simp
    _ = (W.totient : ℝ) / W := by
      rw [Finset.prod_div_distrib]
      exact (div_eq_div_iff hprod.ne' (Nat.cast_ne_zero.mpr hW.ne')).mpr (by linarith only [hcast])

open Filter
open scoped Topology

private lemma totientCorrection_mass {W : ℕ} (hW : 0 < W) :
    (∑' n : ℕ, totientCorrection W n) = (W.totient : ℝ) / W := by
  have ht := (totientCorrection_mult W).eulerProduct (totientCorrection_norm_summable hW)
  have he : (fun N : ℕ => ∏ p ∈ N.primesBelow, ∑' k : ℕ, totientCorrection W (p ^ k))
      =ᶠ[atTop] (fun _ => (W.totient : ℝ) / W) := by
    filter_upwards [eventually_gt_atTop W] with N hN
    rw [← totient_prime_factor_product hW]
    have hsub : W.primeFactors ⊆ N.primesBelow := by
      intro p hp
      obtain ⟨hpp, hd, _⟩ := Nat.mem_primeFactors.mp hp
      exact Nat.mem_primesBelow.mpr ⟨(Nat.le_of_dvd hW hd).trans_lt hN, hpp⟩
    calc
      ∏ p ∈ N.primesBelow, ∑' k : ℕ, totientCorrection W (p ^ k) =
          ∏ p ∈ W.primeFactors, ∑' k : ℕ, totientCorrection W (p ^ k) := by
        symm
        refine Finset.prod_subset hsub (fun p hp hpW => ?_)
        have hpp := Nat.prime_of_mem_primesBelow hp
        rw [totientCorrection_local_mass W hpp,
          if_neg (fun hd => hpW (Nat.mem_primeFactors.mpr ⟨hpp, hd, hW.ne'⟩))]
      _ = _ := Finset.prod_congr rfl (fun p hp => by
        obtain ⟨hpp, hd, _⟩ := Nat.mem_primeFactors.mp hp
        rw [totientCorrection_local_mass W hpp, if_pos hd])
  exact tendsto_nhds_unique ht (tendsto_const_nhds.congr' he.symm)

private lemma harmonic_reciprocal (N : ℕ) :
    ∑ n ∈ Finset.Ioc 0 N, reciprocal n = (harmonic N : ℝ) := by
  rw [harmonic_eq_sum_Icc]
  simp only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
  rfl

private lemma harmonic_div_log_error {x : ℝ} (hx : 1 ≤ x) {n : ℕ} (hn : 0 < n) :
    |(harmonic ⌊x / (n : ℝ)⌋₊ : ℝ) - Real.log x| ≤ 1 + Real.log n := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  by_cases h : 1 ≤ x / (n : ℝ)
  · have hlo := log_le_harmonic_floor (x / (n : ℝ)) (by positivity)
    have hhi := harmonic_floor_le_one_add_log (x / (n : ℝ)) h
    rw [Real.log_div (show x ≠ 0 by positivity) hn'.ne'] at hlo hhi
    rw [abs_le]
    constructor <;> linarith [Real.log_natCast_nonneg n]
  · have hdiv : x / (n : ℝ) < 1 := lt_of_not_ge h
    have hfloor : ⌊x / (n : ℝ)⌋₊ = 0 := Nat.floor_eq_zero.mpr hdiv
    have hle : x ≤ (n : ℝ) := by
      have := (div_lt_iff₀ hn').mp hdiv
      linarith
    simp only [hfloor, harmonic_zero, Rat.cast_zero, zero_sub, abs_neg]
    rw [abs_of_nonneg (Real.log_nonneg hx)]
    linarith [Real.log_le_log (by positivity : 0 < x) hle]

private lemma sum_inv_totient_asymp {W : ℕ} (hW : 0 < W) :
    ∃ C : ℝ, ∀ x : ℝ, 1 ≤ x →
      |(∑ d ∈ Finset.Ioc 0 ⌊x⌋₊, sqfreeTotient W d) -
        (W.totient : ℝ) / W * Real.log x| ≤ C := by
  let g := totientCorrection W
  have hg := totientCorrection_norm_moment hW
  refine ⟨∑' n : ℕ, |g n| * (1 + Real.log n), fun x hx => ?_⟩
  let F : ℕ → ℝ := fun n => g n * (harmonic ⌊x / (n : ℝ)⌋₊ : ℝ)
  have hz : ∀ n ∉ Finset.Ioc 0 ⌊x⌋₊, F n = 0 := by
    intro n hn
    by_cases hn₀ : n = 0
    · simp [F, g, hn₀]
    · have hgt : ⌊x⌋₊ < n := by
        have := Nat.pos_of_ne_zero hn₀
        simp only [Finset.mem_Ioc] at hn
        omega
      have hlt := (Nat.floor_lt (by positivity : 0 ≤ x)).mp hgt
      have hdiv : x / (n : ℝ) < 1 := by
        rw [div_lt_iff₀ (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn₀)), one_mul]
        exact hlt
      simp [F, Nat.floor_eq_zero.mpr hdiv]
  have he : (∑ d ∈ Finset.Ioc 0 ⌊x⌋₊, sqfreeTotient W d) = ∑' n, F n := by
    rw [tsum_eq_sum hz, ← totientCorrection_convolution W, sum_Ioc_mul_eq_sum_sum]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    change _ = g n * (harmonic ⌊x / (n : ℝ)⌋₊ : ℝ)
    rw [harmonic_reciprocal, Nat.floor_div_natCast]
  have hsum := (totientCorrection_norm_summable hW).of_norm.mul_right (Real.log x)
  rw [he, ← totientCorrection_mass hW, ← tsum_mul_right]
  rw [← (summable_of_ne_finset_zero hz).tsum_sub hsum]
  have hpoint : ∀ n : ℕ,
      ‖F n - g n * Real.log x‖ ≤ |g n| * (1 + Real.log n) := by
    intro n
    rw [Real.norm_eq_abs]
    change |g n * (harmonic ⌊x / (n : ℝ)⌋₊ : ℝ) - g n * Real.log x| ≤ _
    rw [← mul_sub, abs_mul]
    by_cases hn : n = 0
    · simp [g, hn]
    exact mul_le_mul_of_nonneg_left (harmonic_div_log_error hx (Nat.pos_of_ne_zero hn)) (abs_nonneg _)
  have hn := hg.of_nonneg_of_le (fun n => norm_nonneg _) hpoint
  rw [← Real.norm_eq_abs]
  exact (norm_tsum_le_tsum_norm hn).trans (hn.tsum_le_tsum hpoint hg)

/- ### Module 3: Uniform bounds for the local sieve factors -/

private lemma cast_div_lower_bound {N d : ℕ} (hd : 0 < d) (hdN : d ≤ N) :
    (N : ℝ) / (d : ℝ) ≤ 2 * ((N / d : ℕ) : ℝ) := by
  have hd' : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  rw [div_le_iff₀ hd']
  have hq : 1 ≤ N / d := (Nat.le_div_iff_mul_le hd).mpr (by simpa using hdN)
  have hdq : d ≤ N / d * d := by simpa using Nat.mul_le_mul_right d hq
  have hmod := Nat.mod_lt N hd
  have hdecomp := Nat.div_add_mod N d
  have hle : N ≤ 2 * (N / d * d) := by
    rw [mul_comm d (N / d)] at hdecomp
    omega
  exact_mod_cast (show N ≤ 2 * (N / d) * d by rwa [mul_assoc])

private lemma sum_prime_log_over_prime_le (N : ℕ) (hN : 0 < N) :
    ∑ p ∈ (Finset.Ioc 0 N).filter Nat.Prime, Real.log p / (p : ℝ) ≤ 2 * Real.log N := by
  classical
  have he : ∑ d ∈ Finset.Ioc 0 N, vonMangoldt d * ((N / d : ℕ) : ℝ) =
      ∑ n ∈ Finset.Ioc 0 N, Real.log n := by
    rw [← sum_Ioc_mul_zeta_eq_sum, vonMangoldt_mul_zeta]
    rfl
  have hN' : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  apply le_of_mul_le_mul_left (a := (N : ℝ)) _ hN'
  rw [Finset.mul_sum]
  calc
    ∑ p ∈ (Finset.Ioc 0 N).filter Nat.Prime, (N : ℝ) * (Real.log p / (p : ℝ)) ≤
        ∑ d ∈ Finset.Ioc 0 N, 2 * (vonMangoldt d * ((N / d : ℕ) : ℝ)) := by
      refine (Finset.sum_le_sum (fun p hp => ?_)).trans
        (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun d _ _ =>
          mul_nonneg (by norm_num) (mul_nonneg vonMangoldt_nonneg (Nat.cast_nonneg _))))
      obtain ⟨hpd, hprime⟩ := Finset.mem_filter.mp hp
      rw [← mul_div_assoc, mul_comm (N : ℝ), mul_div_assoc, ← vonMangoldt_apply_prime hprime]
      have h := mul_le_mul_of_nonneg_left
        (cast_div_lower_bound hprime.pos (Finset.mem_Ioc.mp hpd).2) (vonMangoldt_nonneg (n := p))
      simpa only [mul_left_comm (vonMangoldt p) 2] using h
    _ = 2 * ∑ n ∈ Finset.Ioc 0 N, Real.log n := by rw [← Finset.mul_sum, he]
    _ ≤ (N : ℝ) * (2 * Real.log N) := by
      have h := Finset.sum_le_sum (s := Finset.Ioc 0 N) (g := fun _ => Real.log N)
        (fun n hn => Real.log_le_log (Nat.cast_pos.mpr (Finset.mem_Ioc.mp hn).1)
          (Nat.cast_le.mpr (Finset.mem_Ioc.mp hn).2))
      simp only [Finset.sum_const, Nat.card_Ioc, Nat.sub_zero, nsmul_eq_mul] at h
      linarith

private lemma powerset_weighted_sum {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (w L : ι → ℝ) (hw : ∀ i ∈ S, 0 ≤ w i) :
    ∑ t ∈ S.powerset, (∏ i ∈ t, w i) * (∑ i ∈ t, L i) =
      (∏ i ∈ S, (1 + w i)) * ∑ i ∈ S, w i * L i / (1 + w i) := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih =>
    rw [Finset.sum_powerset_insert ha, Finset.prod_insert ha, Finset.sum_insert ha]
    have hins : ∀ t ∈ S.powerset,
        (∏ i ∈ insert a t, w i) * (∑ i ∈ insert a t, L i) =
          w a * ((∏ i ∈ t, w i) * (∑ i ∈ t, L i)) + w a * L a * (∏ i ∈ t, w i) := by
      intro t ht
      have hat : a ∉ t := fun h => ha (Finset.mem_powerset.mp ht h)
      rw [Finset.prod_insert hat, Finset.sum_insert hat]
      ring
    rw [Finset.sum_congr rfl hins, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      ih (fun i hi => hw i (Finset.mem_insert_of_mem hi)), ← Finset.prod_one_add]
    have hn : 1 + w a ≠ 0 := by linarith [hw a (Finset.mem_insert_self a S)]
    have hcancel : (1 + w a) * (w a * L a / (1 + w a)) = w a * L a := by
      field_simp
    conv_rhs =>
      rw [mul_comm (1 + w a) (∏ i ∈ S, (1 + w i)), mul_assoc, mul_add, hcancel]
    ring

private lemma sqfreeTotient_prod_primes {W : ℕ} {s : Finset ℕ}
    (hprime : ∀ p ∈ s, p.Prime) (hW : ∀ p ∈ s, ¬ p ∣ W) :
    sqfreeTotient W (∏ p ∈ s, p) = ∏ p ∈ s, ((p : ℝ) - 1)⁻¹ := by
  rw [(sqfreeTotient_mult W).map_prod_of_prime s hprime]
  exact Finset.prod_congr rfl (fun p hp => by
    rw [sqfreeTotient_prime W (hprime p hp), if_neg (hW p hp)])

private lemma sum_small_products_le {W : ℕ} {T : Finset ℕ}
    (hp : ∀ p ∈ T, p.Prime) (hc : ∀ p ∈ T, ¬ p ∣ W) {x : ℝ} :
    ∑ s ∈ T.powerset.filter (fun s : Finset ℕ => (∏ p ∈ s, (p : ℝ)) ≤ x),
        ∏ p ∈ s, ((p : ℝ) - 1)⁻¹ ≤
      ∑ d ∈ Finset.Ioc 0 ⌊x⌋₊, sqfreeTotient W d := by
  classical
  let S := T.powerset.filter (fun s : Finset ℕ => (∏ p ∈ s, (p : ℝ)) ≤ x)
  let g : Finset ℕ → ℕ := fun s => ∏ p ∈ s, p
  have hprime : ∀ s ∈ S, ∀ p ∈ s, p.Prime :=
    fun s hs p hps => hp p (Finset.mem_powerset.mp (Finset.mem_filter.mp hs).1 hps)
  have hg : Set.InjOn g S := by
    intro s hs t ht he
    simpa only [g, Nat.primeFactors_prod (hprime s hs), Nat.primeFactors_prod (hprime t ht)]
      using congrArg Nat.primeFactors he
  have hsub : S.image g ⊆ Finset.Ioc 0 ⌊x⌋₊ := by
    intro a ha
    rcases Finset.mem_image.mp ha with ⟨s, hs, rfl⟩
    refine Finset.mem_Ioc.mpr ⟨Finset.prod_pos (fun p hp => (hprime s hs p hp).pos), Nat.le_floor ?_⟩
    rw [show g s = ∏ p ∈ s, p from rfl, Nat.cast_prod]
    exact (Finset.mem_filter.mp hs).2
  calc
    _ = ∑ s ∈ S, sqfreeTotient W (g s) := by
      refine Finset.sum_congr rfl (fun s hs => ?_)
      exact (sqfreeTotient_prod_primes (hprime s hs) (fun p hp =>
        hc p (Finset.mem_powerset.mp (Finset.mem_filter.mp hs).1 hp))).symm
    _ = ∑ a ∈ S.image g, sqfreeTotient W a := (Finset.sum_image hg).symm
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => by
      change 0 ≤ if Squarefree n ∧ n.Coprime W then (n.totient : ℝ)⁻¹ else 0
      split <;> positivity)

private lemma sifted_euler_product_le {W : ℕ} (hW : 0 < W) :
    ∃ C : ℝ, ∀ R : ℝ, 2 ≤ R →
      ∏ p ∈ ((Finset.Ioc 0 ⌊R⌋₊).filter fun p => p.Prime ∧ ¬ p ∣ W),
          (1 + ((p : ℝ) - 1)⁻¹) ≤
        8 * ((W.totient : ℝ) / W) * Real.log R + C := by
  classical
  obtain ⟨C, hC⟩ := sum_inv_totient_asymp hW
  refine ⟨2 * C, fun R hR => ?_⟩
  let T := (Finset.Ioc 0 ⌊R⌋₊).filter fun p => p.Prime ∧ ¬ p ∣ W
  let w : ℕ → ℝ := fun p => ((p : ℝ) - 1)⁻¹
  let A := ∏ p ∈ T, (1 + w p)
  let weight : Finset ℕ → ℝ := fun s => ∏ p ∈ s, w p
  let value : Finset ℕ → ℝ := fun s => ∏ p ∈ s, (p : ℝ)
  have hp : ∀ p ∈ T, p.Prime := fun p hp => (Finset.mem_filter.mp hp).2.1
  have hc : ∀ p ∈ T, ¬ p ∣ W := fun p hp => (Finset.mem_filter.mp hp).2.2
  have hw : ∀ p ∈ T, 0 ≤ w p := by
    intro p h
    have h' : (2 : ℝ) ≤ p := by exact_mod_cast (hp p h).two_le
    exact inv_nonneg.mpr (by linarith)
  have hA : 0 ≤ A := Finset.prod_nonneg (fun p h => by linarith [hw p h])
  have hAeq : ∑ s ∈ T.powerset, weight s = A := (Finset.prod_one_add T).symm
  have hm : ∑ s ∈ T.powerset, weight s * Real.log (value s) =
      A * ∑ p ∈ T, Real.log p / (p : ℝ) := by
    calc
      _ = ∑ s ∈ T.powerset, weight s * (∑ p ∈ s, Real.log p) := by
        refine Finset.sum_congr rfl (fun s hs => ?_)
        rw [Real.log_prod (fun p h => Nat.cast_ne_zero.mpr
          (hp p (Finset.mem_powerset.mp hs h)).ne_zero)]
      _ = A * ∑ p ∈ T, w p * Real.log p / (1 + w p) :=
        powerset_weighted_sum T w (fun p => Real.log p) hw
      _ = _ := by
        congr 1
        refine Finset.sum_congr rfl (fun p h => ?_)
        have h2 : (2 : ℝ) ≤ p := by exact_mod_cast (hp p h).two_le
        change ((p : ℝ) - 1)⁻¹ * Real.log p / (1 + ((p : ℝ) - 1)⁻¹) = _
        have he : 1 + ((p : ℝ) - 1)⁻¹ = p / ((p : ℝ) - 1) := by
          field_simp [show (p : ℝ) - 1 ≠ 0 by linarith]
          ring
        rw [he]
        field_simp [show (p : ℝ) ≠ 0 by linarith, show (p : ℝ) - 1 ≠ 0 by linarith]
  have hlog : 0 < Real.log R := Real.log_pos (by linarith)
  have hprimeSum : ∑ p ∈ T, Real.log p / (p : ℝ) ≤ 2 * Real.log R := by
    have hN1 : 1 ≤ ⌊R⌋₊ := Nat.le_floor (by norm_num; linarith)
    have hs : T ⊆ (Finset.Ioc 0 ⌊R⌋₊).filter Nat.Prime :=
      fun p h => Finset.mem_filter.mpr ⟨Finset.mem_of_mem_filter p h, hp p h⟩
    exact (Finset.sum_le_sum_of_subset_of_nonneg hs (fun p _ _ =>
      div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg _))).trans
      ((sum_prime_log_over_prime_le ⌊R⌋₊ hN1).trans (mul_le_mul_of_nonneg_left
        (Real.log_le_log (Nat.cast_pos.mpr hN1) (Nat.floor_le (by linarith))) (by norm_num)))
  let bad := T.powerset.filter (fun s => ¬ value s ≤ R ^ 4)
  have hbad : ∑ s ∈ bad, weight s ≤ A / 2 := by
    have hh : (4 * Real.log R) * ∑ s ∈ bad, weight s ≤ A * (2 * Real.log R) := by
      rw [Finset.mul_sum]
      calc
        _ ≤ ∑ s ∈ bad, weight s * Real.log (value s) := by
          refine Finset.sum_le_sum (fun s hs => ?_)
          obtain ⟨hS, hlt⟩ := Finset.mem_filter.mp hs
          have hlt' := lt_of_not_ge hlt
          have hpow : 0 < R ^ (4 : ℕ) := by positivity
          have hle := Real.log_le_log hpow hlt'.le
          rw [Real.log_pow] at hle
          rw [mul_comm (4 * Real.log R)]
          exact mul_le_mul_of_nonneg_left hle
            (Finset.prod_nonneg (fun p hp => hw p (Finset.mem_powerset.mp hS hp)))
        _ ≤ ∑ s ∈ T.powerset, weight s * Real.log (value s) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun s hs _ => ?_)
          have hsT := Finset.mem_powerset.mp hs
          refine mul_nonneg (Finset.prod_nonneg (fun p hp => hw p (hsT hp))) (Real.log_nonneg ?_)
          exact Finset.one_le_prod (fun p h => by exact_mod_cast (hp p (hsT h)).one_le)
        _ ≤ _ := hm.trans_le (mul_le_mul_of_nonneg_left hprimeSum hA)
    apply le_of_mul_le_mul_left (a := 4 * Real.log R) _ (by positivity)
    calc _ ≤ _ := hh
         _ = _ := by ring
  have hsplit : (∑ s ∈ T.powerset.filter (fun s => value s ≤ R ^ 4), weight s) +
      (∑ s ∈ bad, weight s) = A := by
    rw [show bad = T.powerset.filter (fun s => ¬ value s ≤ R ^ 4) from rfl,
      Finset.sum_filter_add_sum_filter_not, hAeq]
  have hpow : (1 : ℝ) ≤ R ^ (4 : ℕ) := one_le_pow₀ (by linarith)
  have hsmall := sum_small_products_le (W := W) (x := R ^ 4) hp hc
  change (∑ s ∈ T.powerset.filter (fun s => value s ≤ R ^ 4), weight s) ≤ _ at hsmall
  have hmain := (abs_le.mp (hC (R ^ (4 : ℕ)) hpow)).2
  rw [Real.log_pow] at hmain
  change A ≤ _
  linarith only [hbad, hsplit, hsmall, hmain]

/- ### Module 4: Comparing local sieve kernels -/

private lemma abs_prod_sub_prod_le {ι : Type*} (s : Finset ι) (f g : ι → ℝ) :
    |(∏ i ∈ s, f i) - ∏ i ∈ s, g i| ≤
      (∏ i ∈ s, (|g i| + |f i - g i|)) - ∏ i ∈ s, |g i| := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.prod_insert ha, Finset.prod_insert ha]
    let D := (∏ i ∈ s, (|g i| + |f i - g i|)) - ∏ i ∈ s, |g i|
    have hD : 0 ≤ D := (abs_nonneg _).trans ih
    have ha' : |f a| ≤ |g a| + |f a - g a| := by
      have h := abs_add_le (g a) (f a - g a)
      rwa [show g a + (f a - g a) = f a by ring] at h
    have hcalc : f a * (∏ i ∈ s, f i) - g a * (∏ i ∈ s, g i) =
        f a * ((∏ i ∈ s, f i) - ∏ i ∈ s, g i) + (f a - g a) * (∏ i ∈ s, g i) := by ring
    rw [hcalc]
    calc
      _ ≤ |f a * ((∏ i ∈ s, f i) - ∏ i ∈ s, g i)| +
          |(f a - g a) * (∏ i ∈ s, g i)| := abs_add_le _ _
      _ ≤ (|g a| + |f a - g a|) * D + |f a - g a| * (∏ i ∈ s, |g i|) := by
        rw [abs_mul, abs_mul, Finset.abs_prod]
        exact add_le_add (mul_le_mul ha' ih (abs_nonneg _) (add_nonneg (abs_nonneg _) (abs_nonneg _))) le_rfl
      _ = _ := by unfold D; ring

private lemma prod_add_sub_prod_le {ι : Type*} (s : Finset ι) (b δ : ι → ℝ)
    (hb : ∀ i ∈ s, 1 ≤ b i) (hδ : ∀ i ∈ s, 0 ≤ δ i) :
    (∏ i ∈ s, (b i + δ i)) - ∏ i ∈ s, b i ≤
      (∏ i ∈ s, b i) * (Real.exp (∑ i ∈ s, δ i) - 1) := by
  apply sub_le_iff_le_add.mpr
  rw [mul_sub, mul_one, sub_add_cancel, Real.exp_sum, ← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod (fun i hi => by linarith [hb i hi, hδ i hi]) (fun i hi => ?_)
  calc
    b i + δ i ≤ b i * (1 + δ i) := by nlinarith [mul_nonneg (sub_nonneg.mpr (hb i hi)) (hδ i hi)]
    _ ≤ b i * Real.exp (δ i) := mul_le_mul_of_nonneg_left
      (by simpa [add_comm] using Real.add_one_le_exp (δ i)) (by linarith [hb i hi])

private lemma abs_sum_kernel_difference_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α : ι → Type*} [∀ i, Fintype (α i)] (f g : ∀ i, α i → ℝ)
    (w : (∀ i, α i) → ℝ) (C : ℝ) (hC₀ : 0 ≤ C) (hC : ∀ a, |w a| ≤ C)
    (b δ : ι → ℝ) (hb : ∀ i, b i = ∑ a : α i, |g i a|)
    (hδ : ∀ i, δ i = ∑ a : α i, |f i a - g i a|) (hb₁ : ∀ i, 1 ≤ b i) :
    |(∑ a : ∀ i, α i, w a * ∏ i, f i (a i)) -
      ∑ a : ∀ i, α i, w a * ∏ i, g i (a i)| ≤
      C * (∏ i, b i) * (Real.exp (∑ i, δ i) - 1) := by
  classical
  let u : (∀ i, α i) → ℝ := fun a =>
    (∏ i, (|g i (a i)| + |f i (a i) - g i (a i)|)) - ∏ i, |g i (a i)|
  have hu : ∀ a, |(∏ i, f i (a i)) - ∏ i, g i (a i)| ≤ u a :=
    fun a => abs_prod_sub_prod_le Finset.univ (fun i => f i (a i)) (fun i => g i (a i))
  have htail : ∑ a : ∀ i, α i, u a ≤ (∏ i, b i) * (Real.exp (∑ i, δ i) - 1) := by
    simp only [u, Finset.sum_sub_distrib]
    rw [← Fintype.prod_sum (fun i (a : α i) => |g i a| + |f i a - g i a|),
      ← Fintype.prod_sum (fun i (a : α i) => |g i a|)]
    simp only [Finset.sum_add_distrib, ← hb, ← hδ]
    exact prod_add_sub_prod_le _ _ _ (fun i _ => hb₁ i)
      (fun i _ => hδ i ▸ Finset.sum_nonneg (fun _ _ => abs_nonneg _))
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ a : ∀ i, α i, |w a * (∏ i, f i (a i)) - w a * (∏ i, g i (a i))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a : ∀ i, α i, C * u a := by
      refine Finset.sum_le_sum (fun a _ => ?_)
      rw [← mul_sub, abs_mul]
      exact mul_le_mul (hC a) (hu a) (abs_nonneg _) hC₀
    _ ≤ _ := by rw [← Finset.mul_sum, mul_assoc]; exact mul_le_mul_of_nonneg_left htail hC₀

private lemma inv_square_tail_le (D n : ℕ) (hD : 0 < D) :
    ∑ j ∈ Finset.range n, ((D + j + 1 : ℕ) : ℝ)⁻¹ ^ 2 ≤ (D : ℝ)⁻¹ := by
  have hstrong : ∑ j ∈ Finset.range n, ((D + j + 1 : ℕ) : ℝ)⁻¹ ^ 2 ≤
      (D : ℝ)⁻¹ - ((D + n : ℕ) : ℝ)⁻¹ := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ]
      have ha : (0 : ℝ) < ((D + n : ℕ) : ℝ) := by positivity
      have hb : (0 : ℝ) < ((D + n + 1 : ℕ) : ℝ) := by positivity
      have he : ((D + n : ℕ) : ℝ)⁻¹ - ((D + n + 1 : ℕ) : ℝ)⁻¹ =
          ((D + n : ℕ) : ℝ)⁻¹ * ((D + n + 1 : ℕ) : ℝ)⁻¹ := by
        field_simp
        push_cast
        ring
      have hmono : ((D + n + 1 : ℕ) : ℝ)⁻¹ ≤ ((D + n : ℕ) : ℝ)⁻¹ :=
        inv_anti₀ ha (Nat.cast_le.mpr (Nat.le_succ _))
      have hstep := mul_le_mul_of_nonneg_right hmono (inv_nonneg.mpr hb.le)
      rw [← he, ← sq] at hstep
      rw [show D + (n + 1) = D + n + 1 by omega]
      exact (add_le_add ih hstep).trans_eq (by ring)
  exact hstrong.trans (sub_le_self _ (inv_nonneg.mpr (Nat.cast_nonneg _)))

private def sieveMask {ι : Type*} [DecidableEq ι] (m : Option ι) (a : Finset ι) : Finset ι :=
  m.elim a (fun i => a.erase i)

private lemma sieveMask_subset {ι : Type*} [DecidableEq ι] (m : Option ι) (a : Finset ι) :
    sieveMask m a ⊆ a := by
  cases m with
  | none => exact Finset.Subset.rfl
  | some i => exact Finset.erase_subset _ _

private noncomputable def sieveKernel {ι : Type*} [DecidableEq ι]
    (p : ℝ) (m : Option ι) (ab : Finset ι × Finset ι) : ℝ :=
  if ab.1.card ≤ 1 ∧ ab.2.card ≤ 1 then
    let a := sieveMask m ab.1
    let b := sieveMask m ab.2
    let q := m.elim p (fun _ => p - 1)
    ((p - 1)⁻¹) ^ (ab.1.card + ab.2.card) *
      (1 + (p ^ 2 * (a ∩ b).card - p * (a.card + b.card : ℕ)) / q)
  else 0

private noncomputable def sieveDiagonal {ι : Type*} [DecidableEq ι]
    (w : ℝ) (m : Option ι) (ab : Finset ι × Finset ι) : ℝ :=
  if sieveMask m ab.1 = sieveMask m ab.2 then
    w ^ (ab.1.card + ab.2.card - (sieveMask m ab.1).card)
  else 0

private lemma sieveKernel_sub_diagonal_le {ι : Type*} [DecidableEq ι]
    {p : ℝ} (hp : 3 ≤ p) (m : Option ι) (ab : Finset ι × Finset ι) :
    |sieveKernel p m ab - sieveDiagonal ((p - 1)⁻¹) m ab| ≤
      2 * (((p - 1)⁻¹) ^ (2 : ℕ)) := by
  obtain ⟨a, b⟩ := ab
  let w := (p - 1)⁻¹
  let a' := sieveMask m a
  let b' := sieveMask m b
  let q := m.elim p (fun _ => p - 1)
  have hq : 0 < q := by cases m <;> dsimp [q] <;> linarith
  have hw₀ : 0 < w := inv_pos.mpr (by linarith)
  have hw₁ : w ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
  have ha : a'.card ≤ a.card := Finset.card_le_card (sieveMask_subset _ _)
  have hb : b'.card ≤ b.card := Finset.card_le_card (sieveMask_subset _ _)
  have hia : (a' ∩ b').card ≤ a'.card := Finset.card_le_card Finset.inter_subset_left
  have hib : (a' ∩ b').card ≤ b'.card := Finset.card_le_card Finset.inter_subset_right
  have hsquare : 0 ≤ w ^ 2 := sq_nonneg w
  change |(if a.card ≤ 1 ∧ b.card ≤ 1 then
      w ^ (a.card + b.card) *
        (1 + (p ^ 2 * (a' ∩ b').card - p * (a'.card + b'.card : ℕ)) / q)
      else 0) -
    (if a' = b' then w ^ (a.card + b.card - a'.card) else 0)| ≤ 2 * w ^ 2
  by_cases hvalid : a.card ≤ 1 ∧ b.card ≤ 1
  · rw [if_pos hvalid]
    obtain hzero | hone | htwo : a'.card + b'.card = 0 ∨ a'.card + b'.card = 1 ∨
        a'.card + b'.card = 2 := by omega
    · have ha₀ : a'.card = 0 := by omega
      have hb₀ : b'.card = 0 := by omega
      have he : a' = b' := (Finset.card_eq_zero.mp ha₀).trans (Finset.card_eq_zero.mp hb₀).symm
      have hi : (a' ∩ b').card = 0 := by omega
      rw [hzero, hi, if_pos he, ha₀]
      simp only [Nat.cast_zero, mul_zero, sub_self, zero_div, add_zero, mul_one, Nat.sub_zero, abs_zero]
      linarith only [hsquare]
    · have hi : (a' ∩ b').card = 0 := by omega
      have he : a' ≠ b' := by intro he; rw [he] at hone; omega
      simp only [hone, hi, Nat.cast_one, Nat.cast_zero, mul_zero, mul_one, zero_sub,
        if_neg he, sub_zero, abs_mul, abs_of_pos (pow_pos hw₀ _)]
      have hcoef : |1 + -p / q| ≤ w := by
        cases m with
        | none => dsimp [q]; rw [neg_div, div_self (by linarith), add_neg_cancel, abs_zero]; exact hw₀.le
        | some i =>
          change |1 + -p / (p - 1)| ≤ (p - 1)⁻¹
          have heq : 1 + -p / (p - 1) = - (p - 1)⁻¹ := by
            field_simp [show p - 1 ≠ 0 by linarith]
            ring
          rw [heq, abs_neg, abs_of_pos hw₀]
      have hexp : 2 ≤ a.card + b.card + 1 := by omega
      calc
        _ ≤ w ^ (a.card + b.card) * w := mul_le_mul_of_nonneg_left hcoef (by positivity)
        _ = w ^ (a.card + b.card + 1) := (pow_succ _ _).symm
        _ ≤ w ^ 2 := pow_le_pow_of_le_one hw₀.le hw₁ hexp
        _ ≤ _ := by linarith
    · have ha₁ : a'.card = 1 := by omega
      have hb₁ : b'.card = 1 := by omega
      have hab : a.card + b.card = 2 := by omega
      rw [htwo, hab, ha₁]
      norm_num only [Nat.reduceSubDiff, pow_one, Nat.cast_ofNat]
      by_cases he : a' = b'
      · have hi : (a' ∩ b').card = 1 := by rw [he, Finset.inter_self, hb₁]
        rw [if_pos he, hi, Nat.cast_one, mul_one]
        have hwi : w ^ 2 * (p - 1) = w := by
          unfold w
          field_simp [show p - 1 ≠ 0 by linarith]
        have heq : w ^ 2 * (1 + (p ^ 2 - p * 2) / q) - w =
            w ^ 2 * (1 + (p ^ 2 - p * 2) / q - (p - 1)) := by
          rw [mul_sub, hwi]
        rw [heq, abs_mul, abs_of_nonneg hsquare]
        have hcoef : |1 + (p ^ 2 - p * 2) / q - (p - 1)| ≤ 1 := by
          cases m with
          | none =>
            have heq : 1 + (p ^ 2 - p * 2) / p - (p - 1) = 0 := by
              field_simp [show p ≠ 0 by linarith]
              ring
            rw [show q = p by rfl, heq, abs_zero]; norm_num
          | some i =>
            have heq : 1 + (p ^ 2 - p * 2) / (p - 1) - (p - 1) = (p - 2) / (p - 1) := by
              field_simp [show p - 1 ≠ 0 by linarith]
              ring
            rw [show q = p - 1 by rfl, heq, abs_of_nonneg (div_nonneg (by linarith) (by linarith))]
            exact (div_le_one₀ (by linarith)).mpr (by linarith)
        exact (mul_le_mul_of_nonneg_left hcoef hsquare).trans (by linarith)
      · have hi : (a' ∩ b').card = 0 := by
          by_contra h
          have hi₁ : (a' ∩ b').card = 1 := by omega
          exact he ((Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by omega :
            a'.card ≤ (a' ∩ b').card)).symm.trans
            (Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by omega :
              b'.card ≤ (a' ∩ b').card)))
        rw [if_neg he, hi, Nat.cast_zero, mul_zero, zero_sub, sub_zero, abs_mul, abs_of_nonneg hsquare]
        have hratio : 1 ≤ p / q ∧ p / q ≤ 3 / 2 := by
          have hlo : q ≤ p := by cases m <;> dsimp [q] <;> linarith
          have hhi : p ≤ 3 / 2 * q := by cases m <;> dsimp [q] <;> linarith
          exact ⟨(le_div_iff₀ hq).mpr (by simpa using hlo), (div_le_iff₀ hq).mpr hhi⟩
        have hcoef : |1 + -(p * 2) / q| ≤ 2 := by
          rw [neg_div, mul_comm p (2 : ℝ), mul_div_assoc, abs_le]
          constructor <;> linarith [hratio.1, hratio.2]
        simpa only [mul_comm (w ^ 2)] using mul_le_mul_of_nonneg_left hcoef hsquare
  · rw [if_neg hvalid]
    by_cases he : a' = b'
    · have hexp : 2 ≤ a.card + b.card - a'.card := by
        rw [← he] at hb
        omega
      rw [if_pos he, zero_sub, abs_neg, abs_of_pos (pow_pos hw₀ _)]
      exact (pow_le_pow_of_le_one hw₀.le hw₁ hexp).trans (by linarith)
    · rw [if_neg he, sub_zero, abs_zero]
      positivity

private lemma sieveDiagonal_nonneg {ι : Type*} [DecidableEq ι] {w : ℝ} (hw : 0 ≤ w)
    (m : Option ι) (ab : Finset ι × Finset ι) : 0 ≤ sieveDiagonal w m ab := by
  unfold sieveDiagonal
  split
  · exact pow_nonneg hw _
  · exact le_rfl

private lemma sum_pow_card_finset {ι : Type*} [Fintype ι] [DecidableEq ι] (w : ℝ) :
    (∑ a : Finset ι, w ^ a.card) = (1 + w) ^ Fintype.card ι := by
  calc
    _ = ∑ a ∈ (Finset.univ : Finset ι).powerset, ∏ _i ∈ a, w := by
      simp only [Finset.powerset_univ, Finset.prod_const]
    _ = ∏ _i : ι, (1 + w) := (Finset.prod_one_add _).symm
    _ = _ := by rw [Finset.prod_const, Finset.card_univ]

private lemma erased_eq_iff {ι : Type*} [DecidableEq ι] (i : ι) (a b : Finset ι) :
    b.erase i = a.erase i ↔ b = a.erase i ∨ b = insert i (a.erase i) := by
  constructor
  · intro h
    by_cases hi : i ∈ b
    · right
      rw [← h, Finset.insert_erase hi]
    · left
      simpa only [Finset.erase_eq_of_notMem hi] using h
  · rintro (h | h)
    · rw [h, Finset.erase_idem]
    · rw [h, Finset.erase_insert (Finset.notMem_erase _ _)]

private lemma sieveDiagonal_inner {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w : ℝ) (m : Option ι) (a : Finset ι) :
    (∑ b : Finset ι, sieveDiagonal w m (a, b)) =
      w ^ a.card * m.elim 1 (fun _ => 1 + w) := by
  classical
  cases m with
  | none =>
    simp only [Option.elim_none, mul_one]
    rw [Finset.sum_eq_single a]
    · simp [sieveDiagonal, sieveMask]
    · intro b _ hb
      exact if_neg (Ne.symm hb)
    · simp
  | some i =>
    let a₀ := a.erase i
    let a₁ := insert i a₀
    have h₀ : i ∉ a₀ := Finset.notMem_erase _ _
    have h₁ : i ∈ a₁ := Finset.mem_insert_self _ _
    have hne : a₀ ≠ a₁ := fun he => h₀ (he.symm ▸ h₁)
    have he₀ : a₀.erase i = a₀ := Finset.erase_eq_of_notMem h₀
    have he₁ : a₁.erase i = a₀ := Finset.erase_insert h₀
    have hcard : a₁.card = a₀.card + 1 := Finset.card_insert_of_notMem h₀
    rw [← Finset.sum_subset (s₁ := {a₀, a₁}) (s₂ := Finset.univ) (Finset.subset_univ _)]
    · rw [Finset.sum_insert (by simpa using hne), Finset.sum_singleton]
      change (if a₀ = a₀.erase i then w ^ (a.card + a₀.card - a₀.card) else 0) +
        (if a₀ = a₁.erase i then w ^ (a.card + a₁.card - a₀.card) else 0) =
        w ^ a.card * (1 + w)
      rw [if_pos he₀.symm, if_pos he₁.symm, hcard,
        show a.card + (a₀.card + 1) - a₀.card = a.card + 1 by omega,
        Nat.add_sub_cancel, pow_succ, mul_add, mul_one]
    · intro b _ hb
      apply if_neg
      intro h
      have he : b.erase i = a.erase i := h.symm
      exact hb (by simpa [a₀, a₁] using (erased_eq_iff i a b).mp he)

private lemma sieveDiagonal_mass {ι : Type*} [Fintype ι] [DecidableEq ι] {w : ℝ} (hw : 0 ≤ w)
    (m : Option ι) :
    (∑ ab : Finset ι × Finset ι, |sieveDiagonal w m ab|) =
      (1 + w) ^ (Fintype.card ι + m.elim 0 (fun _ => 1)) := by
  simp only [abs_of_nonneg (sieveDiagonal_nonneg hw _ _), Fintype.sum_prod_type,
    sieveDiagonal_inner, ← Finset.sum_mul, sum_pow_card_finset]
  cases m <;> simp [pow_succ]

private lemma sieveKernel_local_mass_bound {ι : Type*} [Fintype ι] [DecidableEq ι] {p : ℝ} (hp : 3 ≤ p)
    (m : Option ι) :
    (∑ ab : Finset ι × Finset ι, |sieveKernel p m ab - sieveDiagonal ((p - 1)⁻¹) m ab|) ≤
      2 * ((Fintype.card (Finset ι × Finset ι) : ℕ) : ℝ) * ((p - 1)⁻¹) ^ (2 : ℕ) := by
  calc
    _ ≤ ∑ _ab : Finset ι × Finset ι, 2 * ((p - 1)⁻¹) ^ (2 : ℕ) :=
      Finset.sum_le_sum (fun ab _ => sieveKernel_sub_diagonal_le hp m ab)
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

private lemma sum_inv_square_Ioc_le (D N : ℕ) (hD : 0 < D) :
    (∑ j ∈ Finset.Ioc D N, ((j : ℝ)⁻¹) ^ 2) ≤ (D : ℝ)⁻¹ := by
  have he : (∑ j ∈ Finset.Ioc D N, ((j : ℝ)⁻¹) ^ 2) =
      ∑ j ∈ Finset.range (N - D), (((D + j + 1 : ℕ) : ℝ)⁻¹) ^ 2 := by
    symm
    refine Finset.sum_nbij' (fun j => D + j + 1) (fun j => j - (D + 1)) ?_ ?_ ?_ ?_ ?_
    · intro j hj
      have hj' := Finset.mem_range.mp hj
      exact Finset.mem_Ioc.mpr ⟨by omega, by omega⟩
    · intro j hj
      obtain ⟨hl, hu⟩ := Finset.mem_Ioc.mp hj
      exact Finset.mem_range.mpr (by omega)
    · intro j _
      omega
    · intro j hj
      obtain ⟨hl, _⟩ := Finset.mem_Ioc.mp hj
      omega
    · intro _ _
      rfl
  rw [he]
  exact inv_square_tail_le D (N - D) hD

private noncomputable def siftedPrimes (W : ℕ) (R : ℝ) : Finset ℕ :=
  (Finset.Ioc 0 ⌊R⌋₊).filter (fun p => p.Prime ∧ ¬ p ∣ W)

private lemma siftedPrimes_prime {W : ℕ} {R : ℝ} {p : ℕ} (hp : p ∈ siftedPrimes W R) :
    p.Prime := (Finset.mem_filter.mp hp).2.1

private lemma siftedPrimes_not_dvd {W : ℕ} {R : ℝ} {p : ℕ} (hp : p ∈ siftedPrimes W R) :
    ¬ p ∣ W := (Finset.mem_filter.mp hp).2.2

private noncomputable def localPrimeWeight (p : ℕ) : ℝ := ((p : ℝ) - 1)⁻¹

private lemma localPrimeWeight_nonneg {p : ℕ} (hp : p.Prime) : 0 ≤ localPrimeWeight p := by
  have hp₂ : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  exact inv_nonneg.mpr (by linarith)

private lemma siftedPrime_square_tail {D W : ℕ} (hD : 0 < D)
    (hW : ∀ p ≤ D, p.Prime → p ∣ W) (R : ℝ) :
    ∑ p ∈ siftedPrimes W R, (localPrimeWeight p) ^ 2 ≤ 4 / (D : ℝ) := by
  have hsub : siftedPrimes W R ⊆ Finset.Ioc D ⌊R⌋₊ := by
    intro p hp
    have hbound : D < p := lt_of_not_ge (fun h => siftedPrimes_not_dvd hp (hW p h (siftedPrimes_prime hp)))
    exact Finset.mem_Ioc.mpr ⟨hbound, (Finset.mem_Ioc.mp (Finset.mem_of_mem_filter p hp)).2⟩
  have hpoint : ∀ p ∈ siftedPrimes W R, (localPrimeWeight p) ^ 2 ≤ 4 * ((p : ℝ)⁻¹) ^ 2 := by
    intro p hp
    have hp₂ : (2 : ℝ) ≤ p := by exact_mod_cast (siftedPrimes_prime hp).two_le
    have hp₀ : (0 : ℝ) < p := by linarith
    have hle : localPrimeWeight p ≤ 2 * (p : ℝ)⁻¹ := by
      unfold localPrimeWeight
      rw [inv_eq_one_div, inv_eq_one_div, mul_one_div, div_le_div_iff₀ (by linarith) hp₀, one_mul]
      linarith
    have hs := pow_le_pow_left₀ (localPrimeWeight_nonneg (siftedPrimes_prime hp)) hle 2
    exact hs.trans_eq (by ring)
  calc
    _ ≤ ∑ p ∈ siftedPrimes W R, 4 * ((p : ℝ)⁻¹) ^ 2 := Finset.sum_le_sum hpoint
    _ ≤ ∑ p ∈ Finset.Ioc D ⌊R⌋₊, 4 * ((p : ℝ)⁻¹) ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ ≤ _ := by
      rw [← Finset.mul_sum, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_left (sum_inv_square_Ioc_le D ⌊R⌋₊ hD) (by norm_num)

private lemma global_sieve_kernel_difference {ι : Type*} [Fintype ι] [DecidableEq ι]
    {D W : ℕ} (hD : 2 ≤ D) (hW : ∀ p ≤ D, p.Prime → p ∣ W) (R : ℝ) (m : Option ι)
    (v : (siftedPrimes W R → Finset ι × Finset ι) → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hv : ∀ a, |v a| ≤ C) :
    |(∑ a : siftedPrimes W R → Finset ι × Finset ι, v a * ∏ p : siftedPrimes W R, sieveKernel p m (a p)) -
      ∑ a : siftedPrimes W R → Finset ι × Finset ι,
        v a * ∏ p : siftedPrimes W R, sieveDiagonal (localPrimeWeight p) m (a p)| ≤
    C * (∏ p ∈ siftedPrimes W R, (1 + localPrimeWeight p)) ^ (Fintype.card ι + m.elim 0 (fun _ => 1)) *
      (Real.exp (8 * (Fintype.card (Finset ι × Finset ι) : ℝ) / D) - 1) := by
  classical
  let T := siftedPrimes W R
  let K : ℝ := Fintype.card (Finset ι × Finset ι)
  let n := Fintype.card ι + m.elim 0 (fun _ => 1)
  let b : T → ℝ := fun p => (1 + localPrimeWeight p) ^ n
  let δ : T → ℝ := fun p => ∑ ab : Finset ι × Finset ι,
    |sieveKernel (p : ℕ) m ab - sieveDiagonal (localPrimeWeight p) m ab|
  have hb : ∀ p : T, 1 ≤ b p := fun p => one_le_pow₀
    (by linarith [localPrimeWeight_nonneg (siftedPrimes_prime p.2)])
  have h := abs_sum_kernel_difference_le (ι := T) (α := fun _ => Finset ι × Finset ι)
    (fun p => sieveKernel (p : ℕ) m) (fun p => sieveDiagonal (localPrimeWeight p) m)
    v C hC hv b δ (fun p => (sieveDiagonal_mass
      (localPrimeWeight_nonneg (siftedPrimes_prime p.2)) m).symm) (fun _ => rfl) hb
  have hδ : ∑ p : T, δ p ≤ 8 * K / (D : ℝ) := by
    calc
      _ ≤ ∑ p : T, (2 * K) * (localPrimeWeight p) ^ 2 := by
        refine Finset.sum_le_sum (fun p _ => ?_)
        have hprime := siftedPrimes_prime p.2
        have hdvd := siftedPrimes_not_dvd p.2
        have hgt : D < (p : ℕ) := lt_of_not_ge (fun he => hdvd (hW p he hprime))
        have hp3 : 3 ≤ (p : ℕ) := by omega
        exact sieveKernel_local_mass_bound (by exact_mod_cast hp3) m
      _ = 2 * K * ∑ p ∈ T, (localPrimeWeight p) ^ 2 := by
        rw [← Finset.mul_sum]
        exact congrArg (fun x : ℝ => 2 * K * x)
          (Finset.sum_subtype T (fun _ => Iff.rfl) (fun p => (localPrimeWeight p) ^ 2)).symm
      _ ≤ 2 * K * (4 / (D : ℝ)) := mul_le_mul_of_nonneg_left
        (siftedPrime_square_tail (by omega) hW R) (mul_nonneg (by norm_num) (Nat.cast_nonneg _))
      _ = _ := by ring
  have he : (∏ p : T, b p) = (∏ p ∈ T, (1 + localPrimeWeight p)) ^ n := by
    rw [← Finset.prod_pow]
    exact (Finset.prod_subtype T (fun _ => Iff.rfl) (fun p => (1 + localPrimeWeight p) ^ n)).symm
  rw [he] at h
  exact h.trans (mul_le_mul_of_nonneg_left
    (sub_le_sub_right (Real.exp_le_exp.mpr hδ) 1)
    (mul_nonneg hC (pow_nonneg (Finset.prod_nonneg (fun p hp =>
      by linarith [localPrimeWeight_nonneg (siftedPrimes_prime hp)])) _)))

/- ### Affine progressions and the prime-count conclusion -/

private lemma exists_sifted_affine_progression {ι : Type*} [Fintype ι] [DecidableEq ι]
    (h : ι → ℕ) (hh : Function.Injective h) {M b : ℕ} (hM : 0 < M)
    (hadm : ∀ p, p.Prime → ∃ x, ∀ i, ¬ p ∣ M * x + b + h i) (D : ℕ) :
    ∃ W ν : ℕ, 0 < W ∧ M ∣ W ∧ ν < W ∧ ν ≡ b [MOD M] ∧
      (∀ p ≤ D, p.Prime → p ∣ W) ∧
      (∀ i, (ν + h i).Coprime W) ∧
      (∀ p, p.Prime → ¬ p ∣ W → Function.Injective (fun i => h i % p)) := by
  classical
  let δ : ι × ι → ℕ := fun ij => if ij.1 = ij.2 then 1 else Nat.dist (h ij.1) (h ij.2)
  let W := M * (D.factorial * ∏ ij : ι × ι, δ ij)
  have hδ : ∀ ij, 0 < δ ij := by
    intro ij
    unfold δ
    split_ifs with hi
    · exact Nat.one_pos
    · exact Nat.dist_pos_of_ne (hh.ne hi)
  have hW : 0 < W := Nat.mul_pos hM (Nat.mul_pos (Nat.factorial_pos D)
    (Finset.prod_pos (fun ij _ => hδ ij)))
  have hMW : M ∣ W := dvd_mul_right _ _
  have hpW : ∀ p ≤ D, p.Prime → p ∣ W := by
    intro p hp hp'
    exact ((hp'.dvd_factorial.mpr hp).trans (dvd_mul_right _ _)).trans (dvd_mul_left _ _)
  let a : ℕ → ℕ := fun p => if hp : p.Prime then Classical.choose (hadm p hp) else 0
  have ha : ∀ p, p.Prime → ∀ i, ¬ p ∣ M * a p + b + h i := by
    intro p hp i
    rw [show a p = Classical.choose (hadm p hp) by exact dif_pos hp]
    exact Classical.choose_spec (hadm p hp) i
  let z := Nat.chineseRemainderOfFinset a id W.primeFactors
    (fun p hp => (Nat.prime_of_mem_primeFactors hp).ne_zero)
    (fun p hp q hq hpq => (Nat.coprime_primes (Nat.prime_of_mem_primeFactors hp)
      (Nat.prime_of_mem_primeFactors hq)).mpr hpq)
  let ν := (M * (z : ℕ) + b) % W
  refine ⟨W, ν, hW, hMW, Nat.mod_lt _ hW, ?_, hpW, ?_, ?_⟩
  · exact ((Nat.mod_modEq _ _).of_dvd hMW).trans (Nat.modEq_modulus_mul_add_iff.mp (Nat.ModEq.refl _))
  · intro i
    by_contra hc
    obtain ⟨p, hp, hdiv, hdW⟩ := Nat.Prime.not_coprime_iff_dvd.mp hc
    have hz : (z : ℕ) ≡ a p [MOD p] := z.2 p (Nat.mem_primeFactors.mpr ⟨hp, hdW, hW.ne'⟩)
    have hmod : ν + h i ≡ M * a p + b + h i [MOD p] :=
      (((Nat.mod_modEq _ _).of_dvd hdW).add_right (h i)).trans
        (((hz.mul_left M).add_right b).add_right (h i))
    exact ha p hp i (Nat.modEq_zero_iff_dvd.mp (hmod.symm.trans (Nat.modEq_zero_iff_dvd.mpr hdiv)))
  · intro p hp hnp i j hij
    by_contra hne
    have hdist : p ∣ Nat.dist (h i) (h j) := by
      obtain hle | hle := le_total (h i) (h j)
      · rw [Nat.dist_eq_sub_of_le hle]
        exact (Nat.modEq_iff_dvd' hle).mp hij
      · rw [Nat.dist_eq_sub_of_le_right hle]
        exact (Nat.modEq_iff_dvd' hle).mp (Eq.symm hij)
    have hd : δ (i, j) ∣ ∏ ij : ι × ι, δ ij :=
      Finset.dvd_prod_of_mem δ (Finset.mem_univ (i, j))
    have hv : δ (i, j) = Nat.dist (h i) (h j) := if_neg hne
    exact hnp (((hv ▸ hdist : p ∣ δ (i, j)).trans hd).trans
      ((dvd_mul_left _ _).trans (dvd_mul_left _ _)))

private noncomputable def primeLog (n : ℕ) : ℝ := if n.Prime then Real.log n else 0

private lemma primeLog_sum_le_card {ι : Type*} [Fintype ι] (n : ι → ℕ) {L : ℝ}
    (hL : ∀ i, (n i).Prime → Real.log (n i) ≤ L) :
    ∑ i : ι, primeLog (n i) ≤
      (((Finset.univ : Finset ι).filter fun i => (n i).Prime).card : ℝ) * L := by
  unfold primeLog
  rw [← Finset.sum_filter]
  calc
    _ ≤ ∑ _i ∈ (Finset.univ : Finset ι).filter (fun i => (n i).Prime), L :=
      Finset.sum_le_sum (fun i hi => hL i (Finset.mem_filter.mp hi).2)
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]

private lemma exists_prime_count_of_moments {ι : Type*} [Fintype ι] (r : ℕ) (S : Finset ℕ)
    (f : ℕ → ι → ℕ) (u : ℕ → ℝ) {L : ℝ} (hL : 0 ≤ L)
    (hlog : ∀ n ∈ S, ∀ i, (f n i).Prime → Real.log (f n i) ≤ L)
    (h : (r : ℝ) * L * (∑ n ∈ S, u n ^ 2) <
      ∑ n ∈ S, u n ^ 2 * ∑ i : ι, primeLog (f n i)) :
    ∃ n ∈ S, r ≤ ((Finset.univ : Finset ι).filter fun i => (f n i).Prime).card := by
  by_contra! hn
  apply (not_le_of_gt h)
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum (fun n hnS => ?_)
  have hcard : (((Finset.univ : Finset ι).filter fun i => (f n i).Prime).card : ℝ) ≤ r :=
    Nat.cast_le.mpr (hn n hnS).le
  rw [mul_comm ((r : ℝ) * L)]
  exact mul_le_mul_of_nonneg_left ((primeLog_sum_le_card (f n) (hlog n hnS)).trans
    (mul_le_mul_of_nonneg_right hcard hL)) (sq_nonneg _)

private lemma exists_affine_parameter {M b n N : ℕ} (h : M * N + b < n)
    (hmod : n ≡ b [MOD M]) :
    ∃ x, N < x ∧ n = M * x + b := by
  have hbn : b ≤ n := by omega
  obtain ⟨x, hx⟩ := (Nat.modEq_iff_dvd' hbn).mp hmod.symm
  have hnx : n = M * x + b := by omega
  refine ⟨x, ?_, hnx⟩
  by_contra! hle
  exact (not_le_of_gt h) (hnx ▸ Nat.add_le_add_right (Nat.mul_le_mul_left _ hle) _)

/- ### Logarithmic boxes for the discrete variational weights -/

private noncomputable def boxUpper {L : ℕ} (R : ℝ) (j : Fin L) : ℝ :=
  R ^ (((j.val + 1 : ℕ) : ℝ) / L)

private noncomputable def boxLower {L : ℕ} (R : ℝ) (j : Fin L) : ℝ :=
  R ^ ((j.val : ℝ) / L)

private noncomputable def logBox {L : ℕ} (R : ℝ) (j : Fin L) : Finset ℕ :=
  Finset.Ioc (if j.val = 0 then 0 else ⌊boxLower R j⌋₊) ⌊boxUpper R j⌋₊

private lemma boxLower_le_upper {L : ℕ} {R : ℝ} (hR : 1 ≤ R) (j : Fin L) :
    boxLower R j ≤ boxUpper R j := by
  unfold boxLower boxUpper
  exact Real.rpow_le_rpow_of_exponent_le hR (div_le_div_of_nonneg_right
    (by exact_mod_cast Nat.le_succ j.val) (Nat.cast_nonneg L))

private lemma boxUpper_le_R {L : ℕ} {R : ℝ} (hR : 1 ≤ R) (j : Fin L) :
    boxUpper R j ≤ R := by
  unfold boxUpper
  conv_rhs => rw [← Real.rpow_one R]
  exact Real.rpow_le_rpow_of_exponent_le hR ((div_le_one₀ (Nat.cast_pos.mpr
    (Nat.zero_lt_of_lt j.isLt))).mpr (by exact_mod_cast Nat.succ_le_of_lt j.isLt))

private lemma logBox_subset {L : ℕ} {R : ℝ} (hR : 1 ≤ R) (j : Fin L) :
    logBox R j ⊆ Finset.Ioc 0 ⌊R⌋₊ := by
  intro n hn
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ioc.mp hn
  exact Finset.mem_Ioc.mpr ⟨(Nat.zero_le _).trans_lt hlo,
    hhi.trans (Nat.floor_mono (boxUpper_le_R hR j))⟩

private lemma logBox_disjoint {L : ℕ} {R : ℝ} (hR : 1 ≤ R) {i j : Fin L} (hij : i ≠ j) :
    Disjoint (logBox R i) (logBox R j) := by
  suffices H : ∀ a b : Fin L, a < b → Disjoint (logBox R a) (logBox R b) by
    obtain h | h := lt_or_gt_of_ne hij
    · exact H _ _ h
    · exact (H _ _ h).symm
  intro a b h
  have hab : a.val < b.val := h
  have hb : b.val ≠ 0 := by omega
  unfold logBox
  rw [if_neg hb]
  apply Finset.Ioc_disjoint_Ioc_of_le
  apply Nat.floor_mono
  exact Real.rpow_le_rpow_of_exponent_le hR (div_le_div_of_nonneg_right
    (by exact_mod_cast Nat.succ_le_of_lt hab) (Nat.cast_nonneg L))

private lemma logBox_product_le {ι : Type*} [Fintype ι] {L : ℕ} (hL : 0 < L)
    {R : ℝ} (hR : 1 ≤ R) {a : ι → Fin L} {n : ι → ℕ}
    (ha : ∑ i, ((a i).val + 1) ≤ L) (hn : ∀ i, n i ∈ logBox R (a i)) :
    (∏ i, (n i : ℝ)) ≤ R := by
  have hR₀ : 0 < R := by linarith
  have hexp : (∑ i, (((a i).val + 1 : ℕ) : ℝ) / (L : ℝ)) ≤ 1 := by
    rw [← Finset.sum_div, div_le_one₀ (Nat.cast_pos.mpr hL), ← Nat.cast_sum]
    exact_mod_cast ha
  calc
    _ ≤ ∏ i, boxUpper R (a i) := by
      refine Finset.prod_le_prod (fun i _ => Nat.cast_nonneg _) (fun i _ => ?_)
      exact (Nat.cast_le.mpr (Finset.mem_Ioc.mp (hn i)).2).trans
        (Nat.floor_le (Real.rpow_nonneg hR₀.le _))
    _ = R ^ (∑ i, (((a i).val + 1 : ℕ) : ℝ) / (L : ℝ)) := (Real.rpow_sum_of_pos hR₀ _ _).symm
    _ ≤ R := (Real.rpow_le_rpow_of_exponent_le hR hexp).trans_eq (Real.rpow_one _)

private lemma logBox_mass_asymp {W : ℕ} (hW : 0 < W) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {L : ℕ} (R : ℝ), 1 ≤ R → ∀ j : Fin L,
      |(∑ d ∈ logBox R j, sqfreeTotient W d) -
        (W.totient : ℝ) / (W : ℝ) * Real.log R / (L : ℝ)| ≤ C := by
  obtain ⟨C, hC⟩ := sum_inv_totient_asymp hW
  have hC₀ : 0 ≤ C := (abs_nonneg _).trans (hC 1 le_rfl)
  refine ⟨2 * C, by linarith, fun {L} R hR j => ?_⟩
  have hR₀ : 0 < R := by linarith
  have hL : (0 : ℝ) < L := Nat.cast_pos.mpr (Nat.zero_lt_of_lt j.isLt)
  have hlo : 1 ≤ boxLower R j :=
    Real.one_le_rpow hR (div_nonneg (Nat.cast_nonneg _) hL.le)
  have hhi : 1 ≤ boxUpper R j := hlo.trans (boxLower_le_upper hR j)
  let f : ℝ → ℝ := fun x => ∑ d ∈ Finset.Ioc 0 ⌊x⌋₊, sqfreeTotient W d
  let ρ : ℝ := (W.totient : ℝ) / W
  have hh : |f (boxUpper R j) - ρ * Real.log (boxUpper R j)| ≤ C := hC _ hhi
  have hl : |f (boxLower R j) - ρ * Real.log (boxLower R j)| ≤ C := hC _ hlo
  have hlog : Real.log (boxUpper R j) - Real.log (boxLower R j) = Real.log R / (L : ℝ) := by
    unfold boxUpper boxLower
    rw [Real.log_rpow hR₀, Real.log_rpow hR₀, Nat.cast_add, Nat.cast_one]
    field_simp
    ring
  by_cases hj : j.val = 0
  · have he : Real.log (boxUpper R j) = Real.log R / (L : ℝ) := by
      unfold boxUpper
      rw [Real.log_rpow hR₀, hj]
      push_cast
      ring
    rw [logBox, if_pos hj]
    change |f (boxUpper R j) - ρ * Real.log R / (L : ℝ)| ≤ _
    rw [mul_div_assoc, ← he]
    exact hh.trans (by linarith)
  · rw [logBox, if_neg hj]
    have he : ∑ d ∈ Finset.Ioc ⌊boxLower R j⌋₊ ⌊boxUpper R j⌋₊, sqfreeTotient W d =
        f (boxUpper R j) - f (boxLower R j) := by
      unfold f
      rw [← Finset.Ioc_union_Ioc_eq_Ioc (Nat.zero_le _)
        (Nat.floor_mono (boxLower_le_upper hR j)), Finset.sum_union
          (Finset.Ioc_disjoint_Ioc_of_le le_rfl), add_sub_cancel_left]
    rw [he]
    change |f (boxUpper R j) - f (boxLower R j) - ρ * Real.log R / (L : ℝ)| ≤ _
    rw [mul_div_assoc, ← hlog, mul_sub]
    have he' : f (boxUpper R j) - f (boxLower R j) -
        (ρ * Real.log (boxUpper R j) - ρ * Real.log (boxLower R j)) =
        (f (boxUpper R j) - ρ * Real.log (boxUpper R j)) -
        (f (boxLower R j) - ρ * Real.log (boxLower R j)) := by ring
    rw [he']
    have htri := abs_sub_le (f (boxUpper R j) - ρ * Real.log (boxUpper R j)) 0
      (f (boxLower R j) - ρ * Real.log (boxLower R j))
    simp only [sub_zero, zero_sub, abs_neg] at htri
    exact htri.trans (by linarith only [hh, hl])

private def primeSubsetValue {T : Finset ℕ} (s : Finset T) : ℕ :=
  ∏ p ∈ s, (p : ℕ)

private noncomputable def primeSubsetWeight {T : Finset ℕ} (s : Finset T) : ℝ :=
  ∏ p ∈ s, localPrimeWeight p

private lemma sum_sifted_subsets_eq (W : ℕ) (R : ℝ) (A : Finset ℕ)
    (hA : A ⊆ Finset.Ioc 0 ⌊R⌋₊) :
    (∑ s ∈ (Finset.univ : Finset (Finset (siftedPrimes W R))).filter
      (fun s => primeSubsetValue s ∈ A), primeSubsetWeight s) =
        ∑ n ∈ A, sqfreeTotient W n := by
  classical
  let T := siftedPrimes W R
  let e : T ↪ ℕ := ⟨Subtype.val, Subtype.val_injective⟩
  let S := (Finset.univ : Finset (Finset T)).filter (fun s => primeSubsetValue s ∈ A)
  have hprime : ∀ s : Finset T, ∀ p ∈ s.map e, p.Prime := by
    intro s p hp
    obtain ⟨p, _, rfl⟩ := Finset.mem_map.mp hp
    exact siftedPrimes_prime p.2
  have hndvd : ∀ s : Finset T, ∀ p ∈ s.map e, ¬ p ∣ W := by
    intro s p hp
    obtain ⟨p, _, rfl⟩ := Finset.mem_map.mp hp
    exact siftedPrimes_not_dvd p.2
  have hval (s : Finset T) : (∏ p ∈ s.map e, p) = primeSubsetValue s := by
    rw [Finset.prod_map]; rfl
  have hinj : Function.Injective (primeSubsetValue (T := T)) := by
    intro s t hst
    apply Finset.map_injective e
    rw [← Nat.primeFactors_prod (hprime s), ← Nat.primeFactors_prod (hprime t), hval, hval, hst]
  have hweight (s : Finset T) : sqfreeTotient W (primeSubsetValue s) = primeSubsetWeight s := by
    rw [← hval s, sqfreeTotient_prod_primes (hprime s) (hndvd s), Finset.prod_map]
    rfl
  change (∑ s ∈ S, primeSubsetWeight s) = _
  calc
    _ = ∑ s ∈ S, sqfreeTotient W (primeSubsetValue s) :=
      Finset.sum_congr rfl (fun s _ => (hweight s).symm)
    _ = ∑ n ∈ S.image primeSubsetValue, sqfreeTotient W n := (Finset.sum_image hinj.injOn).symm
    _ = _ := by
      refine Finset.sum_subset (fun n hn => ?_) (fun n hn hnS => ?_)
      · obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hn
        exact (Finset.mem_filter.mp hs).2
      · by_contra hne
        have hgood : Squarefree n ∧ n.Coprime W := by
          by_contra h
          exact hne (by simp [sqfreeTotient, h])
        have hsub : n.primeFactors ⊆ T := by
          intro p hp
          obtain ⟨hp', hpd, hn₀⟩ := Nat.mem_primeFactors.mp hp
          exact Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hp'.pos,
            (Nat.le_of_dvd (Nat.pos_of_ne_zero hn₀) hpd).trans (Finset.mem_Ioc.mp (hA hn)).2⟩,
            hp', hp'.coprime_iff_not_dvd.mp (hgood.2.coprime_dvd_left hpd)⟩
        let s : Finset T := T.attach.filter (fun p => (p : ℕ) ∈ n.primeFactors)
        have hs : s.map e = n.primeFactors := by
          ext p
          constructor
          · intro hx
            obtain ⟨p, hp, rfl⟩ := Finset.mem_map.mp hx
            exact (Finset.mem_filter.mp hp).2
          · intro hp
            exact Finset.mem_map.mpr ⟨⟨p, hsub hp⟩, Finset.mem_filter.mpr
              ⟨Finset.mem_attach _ _, hp⟩, rfl⟩
        have hsn : primeSubsetValue s = n := by
          rw [← hval s, hs, Nat.prod_primeFactors_of_squarefree hgood.1]
        exact hnS (Finset.mem_image.mpr ⟨s, Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, hsn.symm ▸ hn⟩, hsn⟩)

/- ### Reindexing the diagonal by coordinates -/

private def transposeSievePair {β ι : Type*} [Fintype β] [Fintype ι]
    [DecidableEq β] [DecidableEq ι] :
    (β → Finset ι × Finset ι) ≃ (ι → Finset β × Finset β) where
  toFun a i := (Finset.univ.filter (fun p => i ∈ (a p).1),
    Finset.univ.filter (fun p => i ∈ (a p).2))
  invFun b p := (Finset.univ.filter (fun i => p ∈ (b i).1),
    Finset.univ.filter (fun i => p ∈ (b i).2))
  left_inv a := by
    funext p
    apply Prod.ext <;> ext i <;> simp
  right_inv a := by
    funext i
    apply Prod.ext <;> ext p <;> simp

private noncomputable def sieveDiagonalCell {ι : Type*} [DecidableEq ι]
    (w : ℝ) (m : Option ι) (i : ι) (a b : Finset ι) : ℝ :=
  if some i = m then
    (if i ∈ a then w else 1) * (if i ∈ b then w else 1)
  else if (i ∈ a ↔ i ∈ b) then (if i ∈ a then w else 1) else 0

private lemma sieveMask_mem {ι : Type*} [DecidableEq ι]
    (m : Option ι) (a : Finset ι) (i : ι) :
    i ∈ sieveMask m a ↔ some i ≠ m ∧ i ∈ a := by
  cases m <;> simp [sieveMask]

private lemma sieveDiagonal_eq_cells {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w : ℝ) (m : Option ι) (a b : Finset ι) :
    sieveDiagonal w m (a, b) = ∏ i : ι, sieveDiagonalCell w m i a b := by
  classical
  have he : sieveMask m a = sieveMask m b ↔
      ∀ i, some i ≠ m → (i ∈ a ↔ i ∈ b) := by
    rw [Finset.ext_iff]
    simp only [sieveMask_mem]
    constructor
    · intro h i hi
      simpa [hi] using h i
    · intro h i
      by_cases hi : some i = m
      · simp [hi]
      · simp [hi, h i hi]
  by_cases h : sieveMask m a = sieveMask m b
  · unfold sieveDiagonal
    rw [if_pos h]
    have hpoint : ∀ i : ι, sieveDiagonalCell w m i a b =
        (if i ∈ a then w else 1) * (if some i = m ∧ i ∈ b then w else 1) := by
      intro i
      by_cases hi : some i = m
      · simp [sieveDiagonalCell, hi]
      · simp [sieveDiagonalCell, hi, (he.mp h) i hi]
    simp only [hpoint, Finset.prod_mul_distrib]
    rw [← Finset.prod_filter, ← Finset.prod_filter]
    simp only [Finset.filter_mem_eq_inter, Finset.univ_inter, Finset.prod_const]
    have hcard : (Finset.univ.filter (fun i : ι => some i = m ∧ i ∈ b)).card =
        b.card - (sieveMask m b).card := by
      have heq : Finset.univ.filter (fun i : ι => some i = m ∧ i ∈ b) =
          b.filter (fun i => some i = m) := by ext i; simp [and_comm]
      rw [heq]
      have herase : b.filter (fun i => some i ≠ m) = sieveMask m b := by
        ext i
        simp [sieveMask_mem, and_comm]
      have hsplit := Finset.card_filter_add_card_filter_not
        (s := b) (p := fun i => some i = m)
      rw [herase] at hsplit
      omega
    rw [hcard, ← pow_add, ← h]
    have hle : (sieveMask m a).card ≤ b.card := h ▸ Finset.card_le_card (sieveMask_subset m b)
    congr 1
    omega
  · unfold sieveDiagonal
    rw [if_neg h]
    obtain ⟨i, hn⟩ := not_forall.mp (he.not.mp h)
    have hi : some i ≠ m := fun hi => hn (fun hh => (hh hi).elim)
    have hab : ¬ (i ∈ a ↔ i ∈ b) := fun hh => hn (fun _ => hh)
    symm
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [sieveDiagonalCell, hi, hab])

private noncomputable def coordinateDiagonal {β ι : Type*} [DecidableEq β] [DecidableEq ι]
    (w : β → ℝ) (m : Option ι) (i : ι) (st : Finset β × Finset β) : ℝ :=
  if some i = m then (∏ p ∈ st.1, w p) * (∏ p ∈ st.2, w p)
  else if st.1 = st.2 then ∏ p ∈ st.1, w p else 0

private lemma prod_sieveDiagonal_transpose {β ι : Type*} [Fintype β] [Fintype ι]
    [DecidableEq β] [DecidableEq ι] (w : β → ℝ) (m : Option ι)
    (a : β → Finset ι × Finset ι) :
    (∏ p : β, sieveDiagonal (w p) m (a p)) =
      ∏ i : ι, coordinateDiagonal w m i (transposeSievePair a i) := by
  classical
  have hc : (∏ p : β, sieveDiagonal (w p) m (a p)) =
      ∏ p : β, ∏ i : ι, sieveDiagonalCell (w p) m i (a p).1 (a p).2 := by
    exact Finset.prod_congr rfl (fun p _ => sieveDiagonal_eq_cells _ _ _ _)
  rw [hc, Finset.prod_comm]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  let s : Finset β := Finset.univ.filter (fun p => i ∈ (a p).1)
  let t : Finset β := Finset.univ.filter (fun p => i ∈ (a p).2)
  change (∏ p : β, sieveDiagonalCell (w p) m i (a p).1 (a p).2) =
    coordinateDiagonal w m i (s, t)
  by_cases hi : some i = m
  · simp only [sieveDiagonalCell, coordinateDiagonal, if_pos hi, Finset.prod_mul_distrib]
    rw [← Finset.prod_filter, ← Finset.prod_filter]
  · simp only [sieveDiagonalCell, coordinateDiagonal, if_neg hi]
    have he : s = t ↔ ∀ p : β, i ∈ (a p).1 ↔ i ∈ (a p).2 := by
      rw [Finset.ext_iff]
      simp [s, t]
    by_cases h : s = t
    · rw [if_pos h]
      simp only [if_pos (he.mp h _)]
      rw [← Finset.prod_filter]
    · rw [if_neg h]
      obtain ⟨p, hp⟩ := not_forall.mp (he.not.mp h)
      exact Finset.prod_eq_zero (Finset.mem_univ p) (if_neg hp)

private lemma sum_sieveDiagonal_transpose {β ι : Type*} [Fintype β] [Fintype ι]
    [DecidableEq β] [DecidableEq ι] (w : β → ℝ) (m : Option ι)
    (v : (ι → Finset β × Finset β) → ℝ) :
    (∑ a : β → Finset ι × Finset ι, v (transposeSievePair a) * ∏ p : β, sieveDiagonal (w p) m (a p)) =
      ∑ b : ι → Finset β × Finset β, v b * ∏ i : ι, coordinateDiagonal w m i (b i) := by
  apply Fintype.sum_equiv transposeSievePair
  intro a
  rw [prod_sieveDiagonal_transpose]

/- ### Prime progression errors -/

private def residueRange (N q a : ℕ) : Finset ℕ :=
  (Finset.range (N + 1)).filter (fun n => n ≡ a [MOD q])

private lemma residueRange_card_bounds {N q a : ℕ} (hq : 0 < q) :
    N / q ≤ (residueRange N q a).card ∧ (residueRange N q a).card ≤ N / q + 1 := by
  constructor
  · rw [← Finset.card_range (N / q)]
    refine Finset.card_le_card_of_injOn (fun j => q * j + a % q) (fun j hj => ?_) ?_
    · change q * j + a % q ∈ residueRange N q a
      have hj' := Finset.mem_range.mp hj
      have hm := Nat.mod_lt a hq
      have hmul : q * (j + 1) ≤ q * (N / q) := Nat.mul_le_mul_left q (by omega)
      have hle := Nat.div_add_mod N q
      refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, ?_⟩
      · rw [Nat.mul_succ] at hmul
        omega
      · exact (Nat.modEq_modulus_mul_add_iff.mpr (Nat.mod_modEq _ _).symm).symm
    · intro i _ j _ h
      change q * i + a % q = q * j + a % q at h
      have hmul : q * i = q * j := by omega
      exact Nat.eq_of_mul_eq_mul_left hq hmul
  · rw [← Finset.card_range (N / q + 1)]
    refine Finset.card_le_card_of_injOn (fun n => n / q) (fun n hn => ?_) ?_
    · have hn' := Finset.mem_range.mp (Finset.mem_filter.mp hn).1
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right (by omega)))
    · intro m hm n hn h
      change m / q = n / q at h
      have he : m % q = n % q :=
        (Finset.mem_filter.mp hm).2.trans (Finset.mem_filter.mp hn).2.symm
      rw [← Nat.div_add_mod m q, ← Nat.div_add_mod n q, h, he]

private lemma residueRange_error {x : ℝ} (hx : 0 ≤ x) {q a : ℕ} (hq : 0 < q) :
    |((residueRange ⌊x⌋₊ q a).card : ℝ) - x / (q : ℝ)| ≤ 1 := by
  obtain ⟨hl, hu⟩ := residueRange_card_bounds (N := ⌊x⌋₊) (a := a) hq
  have hnn : 0 ≤ x / (q : ℝ) := div_nonneg hx (Nat.cast_nonneg q)
  have hf : (⌊x⌋₊ / q : ℕ) = ⌊x / (q : ℝ)⌋₊ := (Nat.floor_div_natCast _ _).symm
  rw [hf] at hl hu
  have hrl : (↑⌊x / (q : ℝ)⌋₊ : ℝ) ≤ (residueRange ⌊x⌋₊ q a).card := by exact_mod_cast hl
  have hru : ((residueRange ⌊x⌋₊ q a).card : ℝ) ≤ ↑⌊x / (q : ℝ)⌋₊ + 1 := by exact_mod_cast hu
  rw [abs_le]
  constructor
  · linarith [Nat.lt_floor_add_one (x / (q : ℝ))]
  · linarith [Nat.floor_le hnn]

private lemma residueInterval_error {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) {q a : ℕ} (hq : 0 < q) :
    |(((Finset.Ioc ⌊x⌋₊ ⌊y⌋₊).filter (fun n => n ≡ a [MOD q])).card : ℝ) -
      (y - x) / (q : ℝ)| ≤ 2 := by
  have he : residueRange ⌊x⌋₊ q a ∪
      ((Finset.Ioc ⌊x⌋₊ ⌊y⌋₊).filter (fun n => n ≡ a [MOD q])) = residueRange ⌊y⌋₊ q a := by
    ext n
    simp only [residueRange, Finset.mem_union, Finset.mem_filter, Finset.mem_range, Finset.mem_Ioc]
    have hh := Nat.floor_mono hxy
    constructor
    · rintro (⟨h, hr⟩ | ⟨⟨_, h⟩, hr⟩)
      · exact ⟨by omega, hr⟩
      · exact ⟨by omega, hr⟩
    · rintro ⟨hn, hr⟩
      by_cases hn' : n ≤ ⌊x⌋₊
      · exact Or.inl ⟨by omega, hr⟩
      · exact Or.inr ⟨⟨by omega, by omega⟩, hr⟩
  have hdis : Disjoint (residueRange ⌊x⌋₊ q a)
      ((Finset.Ioc ⌊x⌋₊ ⌊y⌋₊).filter (fun n => n ≡ a [MOD q])) := by
    refine Finset.disjoint_left.mpr (fun n hn hn' => ?_)
    have hl := Finset.mem_range.mp (Finset.mem_filter.mp hn).1
    have hh := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hn').1).1
    omega
  have heq := Finset.card_union_of_disjoint hdis
  rw [he] at heq
  have hcast := congrArg (fun n : ℕ => (n : ℝ)) heq
  push_cast at hcast
  have hdiff : (((Finset.Ioc ⌊x⌋₊ ⌊y⌋₊).filter (fun n => n ≡ a [MOD q])).card : ℝ) -
      (y - x) / (q : ℝ) =
    (((residueRange ⌊y⌋₊ q a).card : ℝ) - y / (q : ℝ)) -
      (((residueRange ⌊x⌋₊ q a).card : ℝ) - x / (q : ℝ)) := by
    rw [sub_div]
    linarith only [hcast]
  rw [hdiff]
  have htri := abs_sub_le (((residueRange ⌊y⌋₊ q a).card : ℝ) - y / (q : ℝ)) 0
    (((residueRange ⌊x⌋₊ q a).card : ℝ) - x / (q : ℝ))
  simp only [sub_zero, zero_sub, abs_neg] at htri
  exact htri.trans (by
    have h := add_le_add (residueRange_error (hx.trans hxy) (a := a) hq)
      (residueRange_error hx (a := a) hq)
    norm_num at h ⊢
    exact h)

private noncomputable def thetaProgression (x : ℝ) (q a : ℕ) : ℝ :=
  ∑ p ∈ (Finset.range (⌊x⌋₊ + 1)).filter (fun p => p.Prime ∧ p ≡ a [MOD q]), Real.log p

private noncomputable def progressionError (x : ℝ) (q a : ℕ) : ℝ :=
  |thetaProgression x q a - x / (q.totient : ℝ)|

private def coprimeResidues (q : ℕ) : Finset ℕ :=
  (Finset.range (q + 2)).filter (fun a => a.Coprime q)

private lemma coprimeResidues_nonempty (q : ℕ) : (coprimeResidues q).Nonempty :=
  ⟨1, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), Nat.coprime_one_left _⟩⟩

private noncomputable def worstProgressionError (x : ℝ) (q : ℕ) : ℝ :=
  ((coprimeResidues q).image (progressionError x q)).max'
    ((coprimeResidues_nonempty q).image _)

private lemma exists_worst_progression_residue (x : ℝ) (q : ℕ) :
    ∃ a : ℕ, a.Coprime q ∧ worstProgressionError x q = progressionError x q a := by
  have h := Finset.max'_mem ((coprimeResidues q).image (progressionError x q))
    ((coprimeResidues_nonempty q).image _)
  obtain ⟨a, ha, he⟩ := Finset.mem_image.mp h
  exact ⟨a, (Finset.mem_filter.mp ha).2, he.symm⟩

private lemma worstProgressionError_nonneg (x : ℝ) (q : ℕ) : 0 ≤ worstProgressionError x q := by
  obtain ⟨a, -, ha⟩ := exists_worst_progression_residue x q
  exact ha ▸ abs_nonneg _

private lemma progressionError_le_worst {x : ℝ} {q a : ℕ} (hq : 0 < q) (ha : a.Coprime q) :
    progressionError x q a ≤ worstProgressionError x q := by
  have hcop : (a % q).Coprime q := by
    change Nat.gcd (a % q) q = 1
    rw [← Nat.gcd_rec, Nat.gcd_comm]
    exact ha
  have hamem : a % q ∈ coprimeResidues q :=
    Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ((Nat.mod_lt _ hq).trans (by omega)), hcop⟩
  have he : progressionError x q (a % q) = progressionError x q a := by
    unfold progressionError thetaProgression
    have hsets : ((Finset.range (⌊x⌋₊ + 1)).filter (fun p => p.Prime ∧ p ≡ a % q [MOD q])) =
        (Finset.range (⌊x⌋₊ + 1)).filter (fun p => p.Prime ∧ p ≡ a [MOD q]) := by
      ext p
      simp only [Finset.mem_filter]
      change (_ ∧ _ ∧ p % q = (a % q) % q) ↔ (_ ∧ _ ∧ p % q = a % q)
      rw [Nat.mod_mod]
    rw [hsets]
  rw [← he]
  exact Finset.le_max' _ _ (Finset.mem_image_of_mem _ hamem)

private lemma progressionError_crude {x : ℝ} (hx : 2 ≤ x) {q a : ℕ} (hq : 0 < q)
    (hqx : (q : ℝ) ≤ x) :
    progressionError x q a ≤ (2 * Real.log x + 1) * (x / (q.totient : ℝ)) := by
  have hq' : (0 : ℝ) < q := Nat.cast_pos.mpr hq
  have hφ : (0 : ℝ) < q.totient := Nat.cast_pos.mpr (Nat.totient_pos.mpr hq)
  have hlog : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hpos : 0 ≤ thetaProgression x q a := Finset.sum_nonneg (fun p _ => Real.log_natCast_nonneg p)
  have hsize := (abs_le.mp (residueRange_error (by linarith : 0 ≤ x) (a := a) hq)).2
  have hsz : ((residueRange ⌊x⌋₊ q a).card : ℝ) ≤ 2 * (x / (q.totient : ℝ)) := by
    have h₁ : 1 ≤ x / (q : ℝ) := (le_div_iff₀ hq').mpr (by simpa using hqx)
    have h₂ : x / (q : ℝ) ≤ x / (q.totient : ℝ) :=
      div_le_div_of_nonneg_left (by linarith) hφ (Nat.cast_le.mpr (Nat.totient_le q))
    linarith
  have ht : thetaProgression x q a ≤ (2 * (x / (q.totient : ℝ))) * Real.log x := by
    have hsub : (Finset.range (⌊x⌋₊ + 1)).filter (fun p => p.Prime ∧ p ≡ a [MOD q]) ⊆
        residueRange ⌊x⌋₊ q a := fun p hp =>
      Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hp).1, (Finset.mem_filter.mp hp).2.2⟩
    apply (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => Real.log_natCast_nonneg p)).trans
    have hterm : ∀ p ∈ residueRange ⌊x⌋₊ q a, Real.log p ≤ Real.log x := by
      intro p hp
      by_cases hp₀ : p = 0
      · simpa [hp₀] using hlog
      · have hp' := Finset.mem_range.mp (Finset.mem_filter.mp hp).1
        exact Real.log_le_log (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hp₀))
          ((Nat.cast_le.mpr (Nat.le_of_lt_succ hp')).trans (Nat.floor_le (by linarith)))
    calc
      _ ≤ ∑ _p ∈ residueRange ⌊x⌋₊ q a, Real.log x := Finset.sum_le_sum hterm
      _ = ((residueRange ⌊x⌋₊ q a).card : ℝ) * Real.log x := by simp [nsmul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right hsz hlog
  unfold progressionError
  rw [abs_le]
  constructor <;> nlinarith only [hpos, ht, div_nonneg (show 0 ≤ x by linarith) hφ.le,
    mul_nonneg (div_nonneg (show 0 ≤ x by linarith) hφ.le) hlog]

private lemma worstProgressionError_crude {x : ℝ} (hx : 2 ≤ x) {q : ℕ} (hq : 0 < q)
    (hqx : (q : ℝ) ≤ x) :
    worstProgressionError x q ≤ (2 * Real.log x + 1) * (x / (q.totient : ℝ)) := by
  obtain ⟨a, -, ha⟩ := exists_worst_progression_residue x q
  rw [ha]
  exact progressionError_crude hx hq hqx

private def HasBombieriVinogradov : Prop :=
  ∀ A : ℝ, 0 < A → ∃ B C : ℝ, ∀ x : ℝ, 2 ≤ x →
    ∀ a : ℕ → ℕ, (∀ q, (a q).Coprime q) →
      ∑ q ∈ Finset.Icc 1 ⌊Real.sqrt x / Real.log x ^ B⌋₊, progressionError x q (a q)
        ≤ C * x / Real.log x ^ A

private lemma sum_worstProgressionError {hbv : HasBombieriVinogradov} {A : ℝ} (hA : 0 < A) :
    ∃ B C : ℝ, ∀ x : ℝ, 2 ≤ x → ∀ Q : ℕ, Q ≤ ⌊Real.sqrt x / Real.log x ^ B⌋₊ →
      ∑ q ∈ Finset.Icc 1 Q, worstProgressionError x q ≤ C * x / Real.log x ^ A := by
  obtain ⟨B, C, h⟩ := hbv A hA
  refine ⟨B, C, fun x hx Q hQ => ?_⟩
  choose a ha he using (exists_worst_progression_residue x)
  have hsum := h x hx a ha
  calc
    _ ≤ ∑ q ∈ Finset.Icc 1 ⌊Real.sqrt x / Real.log x ^ B⌋₊, worstProgressionError x q :=
      Finset.sum_le_sum_of_subset_of_nonneg
        (fun q hq => Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hq).1, (Finset.mem_Icc.mp hq).2.trans hQ⟩)
        (fun q _ _ => worstProgressionError_nonneg x q)
    _ ≤ _ := by simp_rw [he]; exact hsum

private lemma weighted_worstProgressionError_sq {x : ℝ} (hx : 2 ≤ x) {Q : ℕ}
    (hQ : (Q : ℝ) ≤ x) (w : ℕ → ℝ) :
    (∑ q ∈ Finset.Icc 1 Q, w q * worstProgressionError x q) ^ 2 ≤
      (∑ q ∈ Finset.Icc 1 Q, worstProgressionError x q) * ((2 * Real.log x + 1) * x) *
        ∑ q ∈ Finset.Icc 1 Q, (w q) ^ 2 / (q.totient : ℝ) := by
  let I := Finset.Icc 1 Q
  let E := worstProgressionError x
  have hE : ∀ q, 0 ≤ E q := worstProgressionError_nonneg x
  calc
    _ ≤ (∑ q ∈ I, E q) * ∑ q ∈ I, (w q) ^ 2 * E q := by
      exact Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul I (fun q _ => hE q)
        (fun q _ => mul_nonneg (sq_nonneg _) (hE q))
        (fun q _ => by ring_nf; exact le_rfl)
    _ ≤ _ := by
      rw [mul_assoc]
      apply mul_le_mul_of_nonneg_left _ (Finset.sum_nonneg (fun q _ => hE q))
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum (fun q hq => ?_)
      obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp hq
      have he := worstProgressionError_crude hx hlo ((Nat.cast_le.mpr hhi).trans hQ)
      exact (mul_le_mul_of_nonneg_left he (sq_nonneg _)).trans_eq (by ring)

private noncomputable def tupleBoxWeight {ι : Type*} [Fintype ι] [DecidableEq ι] {L : ℕ}
    (R : ℝ) (c : (ι → Fin L) → ℝ) (n : ι → ℕ) : ℝ :=
  ∑ a : ι → Fin L, c a * ∏ i : ι, (if n i ∈ logBox R (a i) then 1 else 0)

private lemma tupleBoxWeight_eq_sum_filter {ι : Type*} [Fintype ι] [DecidableEq ι] {L : ℕ}
    (R : ℝ) (c : (ι → Fin L) → ℝ) (n : ι → ℕ) :
    tupleBoxWeight R c n = ∑ a ∈ Finset.univ.filter (fun a => ∀ i, n i ∈ logBox R (a i)), c a := by
  classical
  unfold tupleBoxWeight
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  by_cases ha : ∀ i, n i ∈ logBox R (a i)
  · simp [ha]
  · obtain ⟨i, hi⟩ := not_forall.mp ha
    have he : (∏ j : ι, (if n j ∈ logBox R (a j) then (1 : ℝ) else 0)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)
    rw [he, mul_zero]
    exact (if_neg ha).symm

private lemma abs_tupleBoxWeight_le {ι : Type*} [Fintype ι] [DecidableEq ι] {L : ℕ}
    {R : ℝ} (hR : 1 ≤ R) (c : (ι → Fin L) → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hc : ∀ a, |c a| ≤ C) (n : ι → ℕ) :
    |tupleBoxWeight R c n| ≤ C := by
  classical
  rw [tupleBoxWeight_eq_sum_filter]
  let S : Finset (ι → Fin L) := Finset.univ.filter (fun a => ∀ i, n i ∈ logBox R (a i))
  have hsub : S.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro a ha b hb
    funext i
    by_contra hn
    exact Finset.disjoint_left.mp (logBox_disjoint hR hn) ((Finset.mem_filter.mp ha).2 i)
      ((Finset.mem_filter.mp hb).2 i)
  change |∑ a ∈ S, c a| ≤ C
  calc
    _ ≤ ∑ a ∈ S, |c a| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _a ∈ S, C := Finset.sum_le_sum (fun a _ => hc a)
    _ ≤ C := by
      rw [Finset.sum_const, nsmul_eq_mul]
      exact (mul_le_mul_of_nonneg_right (by exact_mod_cast hsub) hC).trans_eq (one_mul _)

private lemma tupleBoxWeight_support {ι : Type*} [Fintype ι] [DecidableEq ι] {L : ℕ}
    (hL : 0 < L) {R : ℝ} (hR : 1 ≤ R) (c : (ι → Fin L) → ℝ)
    (hc : ∀ a, L < ∑ i, ((a i).val + 1) → c a = 0) (n : ι → ℕ)
    (hn : R < ∏ i, (n i : ℝ)) : tupleBoxWeight R c n = 0 := by
  classical
  rw [tupleBoxWeight_eq_sum_filter]
  refine Finset.sum_eq_zero (fun a ha => ?_)
  apply hc
  by_contra! h
  exact (not_le_of_gt hn) (logBox_product_le hL hR h (Finset.mem_filter.mp ha).2)

private lemma integrate_two_product_weights {ι : Type*} [Fintype ι] [DecidableEq ι]
    {σ δ : Type*} [Fintype σ] [Fintype δ]
    (a b : (ι → σ) → ℝ) (f g : ι → σ → δ → ℝ) (K : ι → δ → ℝ) :
    ∑ z : ι → δ,
      (∑ x : ι → σ, a x * ∏ i, f i (x i) (z i)) *
        (∑ y : ι → σ, b y * ∏ i, g i (y i) (z i)) * ∏ i, K i (z i) =
      ∑ x : ι → σ, ∑ y : ι → σ, a x * b y *
        ∏ i, ∑ t : δ, f i (x i) t * g i (y i) t * K i t := by
  calc
    _ = ∑ z : ι → δ, ∑ x : ι → σ, ∑ y : ι → σ,
        a x * b y * ∏ i, (f i (x i) (z i) * g i (y i) (z i) * K i (z i)) := by
      refine Finset.sum_congr rfl (fun z _ => ?_)
      rw [Finset.sum_mul, Finset.sum_mul]
      simp only [Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => ?_))
      simp only [Finset.prod_mul_distrib]
      ring
    _ = _ := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun x _ => ?_)
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun y _ => ?_)
      rw [← Finset.mul_sum, ← Fintype.prod_sum (fun i t => f i (x i) t * g i (y i) t * K i t)]

private noncomputable def boxMass {L : ℕ} (W : ℕ) (R : ℝ) (j : Fin L) : ℝ :=
  ∑ n ∈ logBox R j, sqfreeTotient W n

private lemma sifted_box_mass {L W : ℕ} {R : ℝ} (hR : 1 ≤ R) (j : Fin L) :
    (∑ s : Finset (siftedPrimes W R),
      (if primeSubsetValue s ∈ logBox R j then 1 else 0) * primeSubsetWeight s) =
      boxMass W R j := by
  simp only [ite_mul, one_mul, zero_mul]
  rw [← Finset.sum_filter]
  exact sum_sifted_subsets_eq W R (logBox R j) (logBox_subset hR j)

private lemma coordinateDiagonal_box_integral {ι : Type*} [DecidableEq ι]
    {W L : ℕ} {R : ℝ} (hR : 1 ≤ R) (m : Option ι) (i : ι) (a b : Fin L) :
    (∑ s : Finset (siftedPrimes W R) × Finset (siftedPrimes W R),
      (if primeSubsetValue s.1 ∈ logBox R a then 1 else 0) *
        (if primeSubsetValue s.2 ∈ logBox R b then 1 else 0) *
        coordinateDiagonal (fun p : siftedPrimes W R => localPrimeWeight p) m i s) =
      if some i = m then boxMass W R a * boxMass W R b
      else if a = b then boxMass W R a else 0 := by
  classical
  let T := siftedPrimes W R
  let f : Finset T → ℝ := fun s => if primeSubsetValue s ∈ logBox R a then 1 else 0
  let g : Finset T → ℝ := fun s => if primeSubsetValue s ∈ logBox R b then 1 else 0
  change (∑ s : Finset T × Finset T, f s.1 * g s.2 *
    coordinateDiagonal (fun p : T => localPrimeWeight p) m i s) = _
  rw [Fintype.sum_prod_type]
  by_cases hi : some i = m
  · simp only [coordinateDiagonal, if_pos hi]
    have hp : ∀ s t : Finset T,
        f s * g t * (primeSubsetWeight s * primeSubsetWeight t) =
        (f s * primeSubsetWeight s) * (g t * primeSubsetWeight t) := fun _ _ => by ring
    change (∑ s : Finset T, ∑ t : Finset T,
      f s * g t * (primeSubsetWeight s * primeSubsetWeight t)) = _
    simp_rw [hp]
    rw [← Finset.sum_mul_sum, sifted_box_mass hR a, sifted_box_mass hR b]
  · simp only [coordinateDiagonal, if_neg hi]
    have hs : ∀ s : Finset T,
         (∑ t : Finset T, f s * g t * (if s = t then primeSubsetWeight s else 0)) =
           f s * g s * primeSubsetWeight s := by
      intro s
      rw [Finset.sum_eq_single s]
      · rw [if_pos rfl]
      · intro t _ ht
        rw [if_neg ht.symm, mul_zero]
      · simp
    change (∑ s : Finset T, ∑ t : Finset T,
      f s * g t * (if s = t then primeSubsetWeight s else 0)) = _
    simp_rw [hs]
    by_cases hab : a = b
    · subst b
      rw [if_pos rfl, ← sifted_box_mass hR a]
      refine Finset.sum_congr rfl (fun s _ => ?_)
      change (if primeSubsetValue s ∈ logBox R a then (1 : ℝ) else 0) *
          (if primeSubsetValue s ∈ logBox R a then (1 : ℝ) else 0) * primeSubsetWeight s =
        (if primeSubsetValue s ∈ logBox R a then (1 : ℝ) else 0) * primeSubsetWeight s
      split <;> simp
    · rw [if_neg hab]
      refine Finset.sum_eq_zero (fun s _ => ?_)
      by_cases ha : primeSubsetValue s ∈ logBox R a
      · have hb : primeSubsetValue s ∉ logBox R b := fun hb =>
          Finset.disjoint_left.mp (logBox_disjoint hR hab) ha hb
        simp [f, g, ha, hb]
      · simp [f, g, ha]

private noncomputable def boxMomentPolynomial {ι : Type*} [Fintype ι] [DecidableEq ι] {L : ℕ}
    (c : (ι → Fin L) → ℝ) (m : Option ι) (x : Fin L → ℝ) : ℝ :=
  ∑ a : ι → Fin L, ∑ b : ι → Fin L, c a * c b *
    ∏ i : ι, (if some i = m then x (a i) * x (b i) else if a i = b i then x (a i) else 0)

private lemma diagonal_eq_boxMomentPolynomial {ι : Type*} [Fintype ι] [DecidableEq ι]
    {W L : ℕ} {R : ℝ} (hR : 1 ≤ R) (c : (ι → Fin L) → ℝ) (m : Option ι) :
    (∑ z : siftedPrimes W R → Finset ι × Finset ι,
      (let z' := transposeSievePair z
       tupleBoxWeight R c (fun i => primeSubsetValue (z' i).1) *
       tupleBoxWeight R c (fun i => primeSubsetValue (z' i).2)) *
         ∏ p : siftedPrimes W R, sieveDiagonal (localPrimeWeight p) m (z p)) =
      boxMomentPolynomial c m (boxMass W R) := by
  rw [sum_sieveDiagonal_transpose (v := fun z =>
    tupleBoxWeight R c (fun i => primeSubsetValue (z i).1) *
    tupleBoxWeight R c (fun i => primeSubsetValue (z i).2))]
  unfold tupleBoxWeight boxMomentPolynomial
  let T := siftedPrimes W R
  rw [integrate_two_product_weights c c
    (fun _ j (s : Finset T × Finset T) => if primeSubsetValue s.1 ∈ logBox R j then 1 else 0)
    (fun _ j (s : Finset T × Finset T) => if primeSubsetValue s.2 ∈ logBox R j then 1 else 0)
    (fun i => coordinateDiagonal (fun p : T => localPrimeWeight p) m i)]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
  congr 1
  exact Finset.prod_congr rfl (fun i _ => coordinateDiagonal_box_integral hR m i (a i) (b i))

private lemma modEq_prod_iff {ι : Type*} [DecidableEq ι] (S : Finset ι) (q : ι → ℕ)
    (hcop : Set.Pairwise (S : Set ι) (fun i j => (q i).Coprime (q j))) (a b : ℕ) :
    a ≡ b [MOD ∏ i ∈ S, q i] ↔ ∀ i ∈ S, a ≡ b [MOD q i] := by
  induction S using Finset.induction with
  | empty => simp [Nat.ModEq, Nat.mod_one]
  | insert i S hi ih =>
    have hsub : Set.Pairwise (S : Set ι) (fun i j => (q i).Coprime (q j)) :=
      hcop.mono (Finset.coe_subset.mpr (Finset.subset_insert i S))
    have hcop' : (q i).Coprime (∏ j ∈ S, q j) :=
      Nat.Coprime.prod_right (fun j hj => hcop (Finset.mem_insert_self i S)
        (Finset.mem_insert_of_mem hj) (by
          intro h
          exact hi (h ▸ hj)))
    rw [Finset.prod_insert hi, ← Nat.modEq_and_modEq_iff_modEq_mul hcop', ih hsub]
    simp

private lemma exists_sieve_residue {W ν : ℕ} (hW : 0 < W) (S : Finset ℕ)
    (hp : ∀ p ∈ S, p.Prime) (hndvd : ∀ p ∈ S, ¬ p ∣ W) (a : ℕ → ℕ) :
    ∃ z : ℕ, (∀ n, n ≡ z [MOD W * (∏ p ∈ S, p)] ↔
      n ≡ ν [MOD W] ∧ ∀ p ∈ S, p ∣ n + a p) := by
  classical
  let L := insert 0 S
  let q : ℕ → ℕ := fun p => if p = 0 then W else p
  let r : ℕ → ℕ := fun p => if p = 0 then ν else p * (a p + 1) - a p
  have hzero : 0 ∉ S := fun h => (hp 0 h).ne_zero rfl
  have hq : ∀ p ∈ L, q p ≠ 0 := by
    intro p h
    rcases Finset.mem_insert.mp h with (rfl | h)
    · simpa [q] using hW.ne'
    · have hp₀ := (hp p h).ne_zero
      simpa [q, hp₀] using hp₀
  have hcop : Set.Pairwise (L : Set ℕ) (fun p s => (q p).Coprime (q s)) := by
    intro p hpl s hsl hne
    rcases Finset.mem_insert.mp hpl with (rfl | hps) <;>
      rcases Finset.mem_insert.mp hsl with (rfl | hss)
    · exact (hne rfl).elim
    · simpa [q, (hp s hss).ne_zero] using ((hp s hss).coprime_iff_not_dvd.mpr (hndvd s hss)).symm
    · simpa [q, (hp p hps).ne_zero] using (hp p hps).coprime_iff_not_dvd.mpr (hndvd p hps)
    · simpa [q, (hp p hps).ne_zero, (hp s hss).ne_zero] using
        (Nat.coprime_primes (hp p hps) (hp s hss)).mpr hne
  let z := Nat.chineseRemainderOfFinset r q L hq hcop
  refine ⟨z, fun n => ?_⟩
  have hprod : ∏ p ∈ L, q p = W * (∏ p ∈ S, p) := by
    rw [show L = insert 0 S from rfl, Finset.prod_insert hzero]
    simp only [q, if_pos rfl]
    congr 1
    exact Finset.prod_congr rfl (fun p h => if_neg (hp p h).ne_zero)
  rw [← hprod, modEq_prod_iff L q hcop]
  have hpoint : (∀ p ∈ L, n ≡ (z : ℕ) [MOD q p]) ↔ ∀ p ∈ L, n ≡ r p [MOD q p] :=
    ⟨fun h p hp => (h p hp).trans (z.2 p hp), fun h p hp => (h p hp).trans (z.2 p hp).symm⟩
  rw [hpoint]
  have hroot : ∀ p ∈ S, (n ≡ r p [MOD q p]) ↔ p ∣ n + a p := by
    intro p hps
    have pp := hp p hps
    have hle : a p ≤ p * (a p + 1) := by
      have := Nat.mul_le_mul_right (a p + 1) pp.one_le
      omega
    have hdiv : p ∣ r p + a p := by
      rw [show r p = p * (a p + 1) - a p from if_neg pp.ne_zero, Nat.sub_add_cancel hle]
      exact dvd_mul_right _ _
    have hz := Nat.modEq_zero_iff_dvd.mpr hdiv
    change (n ≡ r p [MOD if p = 0 then W else p]) ↔ _
    rw [if_neg pp.ne_zero, ← Nat.modEq_zero_iff_dvd]
    exact ⟨fun h => (h.add_right _).trans hz,
      fun h => Nat.ModEq.add_right_cancel' _ (h.trans hz.symm)⟩
  constructor
  · intro h
    refine ⟨?_, fun p hp => (hroot p hp).mp (h p (Finset.mem_insert_of_mem hp))⟩
    simpa [q, r] using h 0 (Finset.mem_insert_self _ _)
  · rintro ⟨hn, hs⟩ p hp
    rcases Finset.mem_insert.mp hp with (rfl | hp)
    · simpa [q, r] using hn
    · exact (hroot p hp).mpr (hs p hp)

private lemma sieve_residue_shift_coprime {W ν : ℕ} (S : Finset ℕ)
    (hp : ∀ p ∈ S, p.Prime) (hn : ∀ p ∈ S, ¬ p ∣ W) (a : ℕ → ℕ)
    {z c : ℕ} (hz : z ≡ ν [MOD W] ∧ ∀ p ∈ S, p ∣ z + a p)
    (hc : (ν + c).Coprime W)
    (hsep : ∀ p ∈ S, a p % p ≠ c % p) :
    (z + c).Coprime (W * ∏ p ∈ S, p) := by
  apply (Nat.coprime_mul_iff_right).mpr
  constructor
  · by_contra h
    obtain ⟨p, hpp, hdc, hdW⟩ := Nat.Prime.not_coprime_iff_dvd.mp h
    have hmod := ((hz.1.of_dvd hdW).add_right c).symm.trans (Nat.modEq_zero_iff_dvd.mpr hdc)
    exact hpp.not_dvd_one (Nat.dvd_gcd (Nat.modEq_zero_iff_dvd.mp hmod) hdW |>.trans (by
      rw [hc.gcd_eq_one]))
  · apply Nat.Coprime.prod_right
    intro p hpS
    rw [Nat.coprime_comm, (hp p hpS).coprime_iff_not_dvd]
    intro hdc
    have h₁ := Nat.modEq_zero_iff_dvd.mpr (hz.2 p hpS)
    have h₂ := Nat.modEq_zero_iff_dvd.mpr hdc
    exact hsep p hpS (Nat.ModEq.add_left_cancel' z (h₁.trans h₂.symm))

private lemma thetaProgression_interval {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y)
    (q a c : ℕ) :
    (∑ n ∈ (Finset.Ioc ⌊x⌋₊ ⌊y⌋₊).filter (fun n => n ≡ a [MOD q]), primeLog (n + c)) =
      thetaProgression (y + c) q (a + c) - thetaProgression (x + c) q (a + c) := by
  classical
  let P : ℕ → Prop := fun p => p.Prime ∧ p ≡ a + c [MOD q]
  let I := (Finset.Ioc (⌊x⌋₊ + c) (⌊y⌋₊ + c)).filter P
  let S := ((Finset.Ioc ⌊x⌋₊ ⌊y⌋₊).filter (fun n => n ≡ a [MOD q])).filter
    (fun n => (n + c).Prime)
  have he : (∑ n ∈ (Finset.Ioc ⌊x⌋₊ ⌊y⌋₊).filter (fun n => n ≡ a [MOD q]), primeLog (n + c)) =
      ∑ n ∈ S, Real.log ((n + c : ℕ) : ℝ) := by simp only [S, Finset.sum_filter, primeLog]
  rw [he]
  have hbij : (∑ n ∈ S, Real.log ((n + c : ℕ) : ℝ)) = ∑ p ∈ I, Real.log p := by
    refine Finset.sum_nbij' (fun n => n + c) (fun p => p - c) ?_ ?_ ?_ ?_ ?_
    · intro n hn
      rcases Finset.mem_filter.mp hn with ⟨hn, hprime⟩
      rcases Finset.mem_filter.mp hn with ⟨hn, ha⟩
      rcases Finset.mem_Ioc.mp hn with ⟨hl, hu⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨by omega, by omega⟩,
        hprime, ha.add_right c⟩
    · intro p hp
      obtain ⟨hi, hprime, ha⟩ := Finset.mem_filter.mp hp
      obtain ⟨hl, hu⟩ := Finset.mem_Ioc.mp hi
      have hpc : p - c + c = p := by omega
      have hmod : p - c ≡ a [MOD q] := Nat.ModEq.add_right_cancel' c (hpc.symm ▸ ha)
      exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
        ⟨Finset.mem_Ioc.mpr ⟨by omega, by omega⟩, hmod⟩, hpc.symm ▸ hprime⟩
    · intro n _
      omega
    · intro p hp
      have hl := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1).1
      omega
    · intro _ _
      rfl
  rw [hbij, thetaProgression, thetaProgression, Nat.floor_add_natCast hx,
    Nat.floor_add_natCast (hx.trans hxy)]
  let B := (Finset.range (⌊x⌋₊ + c + 1)).filter P
  let A := (Finset.range (⌊y⌋₊ + c + 1)).filter P
  change _ = (∑ p ∈ A, Real.log p) - ∑ p ∈ B, Real.log p
  have huu := Nat.floor_mono hxy
  have hu : B ∪ I = A := by
    ext n
    simp only [B, I, A, Finset.mem_union, Finset.mem_filter, Finset.mem_range, Finset.mem_Ioc]
    constructor
    · rintro (⟨hl, hp⟩ | ⟨⟨_, hr⟩, hp⟩)
      · exact ⟨by omega, hp⟩
      · exact ⟨by omega, hp⟩
    · rintro ⟨hh, hp⟩
      by_cases h : n ≤ ⌊x⌋₊ + c
      · exact Or.inl ⟨by omega, hp⟩
      · exact Or.inr ⟨⟨by omega, by omega⟩, hp⟩
  have hd : Disjoint B I := by
    apply Finset.disjoint_left.mpr
    intro p hp hp'
    have hl := Finset.mem_range.mp (Finset.mem_filter.mp hp).1
    have hr := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hp').1).1
    omega
  rw [← hu, Finset.sum_union hd, add_sub_cancel_left]

private lemma primeResidueInterval_error {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y)
    {q a c : ℕ} (hq : 0 < q) (ha : (a + c).Coprime q) :
    |(∑ n ∈ (Finset.Ioc ⌊x⌋₊ ⌊y⌋₊).filter (fun n => n ≡ a [MOD q]), primeLog (n + c)) -
      (y - x) / (q.totient : ℝ)| ≤
      worstProgressionError (y + c) q + worstProgressionError (x + c) q := by
  rw [thetaProgression_interval hx hxy]
  have he : thetaProgression (y + c) q (a + c) - thetaProgression (x + c) q (a + c) -
      (y - x) / (q.totient : ℝ) =
    (thetaProgression (y + c) q (a + c) - (y + c) / (q.totient : ℝ)) -
    (thetaProgression (x + c) q (a + c) - (x + c) / (q.totient : ℝ)) := by
    rw [sub_div, add_div, add_div]
    ring
  rw [he]
  have htri := abs_sub_le
    (thetaProgression (y + c) q (a + c) - (y + c) / (q.totient : ℝ)) 0
    (thetaProgression (x + c) q (a + c) - (x + c) / (q.totient : ℝ))
  simp only [sub_zero, zero_sub, abs_neg] at htri
  exact htri.trans (add_le_add (progressionError_le_worst hq ha) (progressionError_le_worst hq ha))

/- ### Expanding the sieve weights into congruence conditions -/

private lemma card_le_one_cases {ι : Type*} [DecidableEq ι] {s : Finset ι} (h : s.card ≤ 1) :
    s = ∅ ∨ ∃ i, s = {i} := by
  rcases s.eq_empty_or_nonempty with he | ⟨i, hi⟩
  · exact Or.inl he
  · exact Or.inr ⟨i, Finset.Subset.antisymm (fun j hj => Finset.mem_singleton.mpr
      (Finset.card_le_one.mp h j hj i hi)) (Finset.singleton_subset_iff.mpr hi)⟩

private noncomputable def localSieveCoeff {ι : Type*} [DecidableEq ι]
    (p : ℝ) (r d : Finset ι) : ℝ :=
  if r.card ≤ 1 ∧ d ⊆ r then ((p - 1)⁻¹) ^ r.card * (-p) ^ d.card else 0

private noncomputable def localPairMean {ι : Type*} [DecidableEq ι]
    (p : ℝ) (m : Option ι) (d e : Finset ι) : ℝ :=
  if d ∪ e = ∅ then 1
  else if (d ∪ e).card = 1 ∧ sieveMask m (d ∪ e) = d ∪ e
    then (m.elim p (fun _ => p - 1))⁻¹ else 0

private lemma localSieveCoeff_empty {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ℝ) (f : Finset ι → ℝ) :
    (∑ d : Finset ι, localSieveCoeff p ∅ d * f d) = f ∅ := by
  rw [Finset.sum_eq_single ∅]
  · simp [localSieveCoeff]
  · intro d _ hd
    have hn : ¬d ⊆ ∅ := fun h => hd (Finset.subset_empty.mp h)
    simp [localSieveCoeff, hn]
  · simp

private lemma localSieveCoeff_singleton {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ℝ) (i : ι) (f : Finset ι → ℝ) :
    (∑ d : Finset ι, localSieveCoeff p {i} d * f d) = (p - 1)⁻¹ * (f ∅ - p * f {i}) := by
  classical
  rw [← Finset.sum_subset (s₁ := (Finset.univ.filter (fun d : Finset ι => d ⊆ {i})))
    (Finset.filter_subset _ _)]
  · have he : (Finset.univ.filter (fun d : Finset ι => d ⊆ {i})) = {∅, {i}} := by
      ext d
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · intro hd
        by_cases hi : i ∈ d
        · exact Or.inr (Finset.Subset.antisymm hd (Finset.singleton_subset_iff.mpr hi))
        · exact Or.inl (Finset.eq_empty_iff_forall_notMem.mpr
            (fun j hj => hi ((Finset.mem_singleton.mp (hd hj)) ▸ hj)))
      · rintro (rfl | rfl) <;> simp
    rw [he, Finset.sum_insert (by simp), Finset.sum_singleton]
    simp [localSieveCoeff]
    ring
  · intro d _ hd
    have hn : ¬ d ⊆ {i} := fun h => hd (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
    simp [localSieveCoeff, hn]

private lemma sieveMask_singleton {ι : Type*} [DecidableEq ι] (m : Option ι) (i : ι) :
    sieveMask m {i} = if some i = m then ∅ else {i} := by
  by_cases h : some i = m
  · subst m
    simp [sieveMask]
  · cases m with
    | none => simp [sieveMask]
    | some j =>
      rw [if_neg h]
      ext a
      have hij : i ≠ j := fun he => h (congrArg some he)
      simp [sieveMask, Finset.mem_erase, Finset.mem_singleton, and_iff_right_of_imp
        (fun ha : a = i => ha ▸ hij)]

private lemma localPairMean_empty {ι : Type*} [DecidableEq ι] (p : ℝ) (m : Option ι) :
    localPairMean p m (∅ : Finset ι) ∅ = 1 := by simp [localPairMean]

private lemma localPairMean_union_singleton {ι : Type*} [DecidableEq ι] (p : ℝ) (m : Option ι)
    {d e : Finset ι} {i : ι} (h : d ∪ e = {i}) :
    localPairMean p m d e = if some i = m then 0 else (m.elim p (fun _ => p - 1))⁻¹ := by
  unfold localPairMean
  rw [h, sieveMask_singleton]
  by_cases hi : some i = m <;> simp [hi]

private lemma localPairMean_two {ι : Type*} [DecidableEq ι] (p : ℝ) (m : Option ι)
    {i j : ι} (hij : i ≠ j) :
    localPairMean p m {i} {j} = 0 := by
  have htwo : ({i} ∪ {j} : Finset ι).card = 2 := by
    rw [Finset.singleton_union, Finset.card_insert_of_notMem (by simpa using hij)]
    simp
  have he : ({i} ∪ {j} : Finset ι) ≠ ∅ := fun h => by simp [h] at htwo
  unfold localPairMean
  rw [if_neg he, if_neg (fun h => by have := h.1; omega)]

private lemma localPairMean_comm {ι : Type*} [DecidableEq ι] (p : ℝ) (m : Option ι)
    (d e : Finset ι) :
    localPairMean p m d e = localPairMean p m e d := by
  unfold localPairMean
  rw [Finset.union_comm]

private lemma local_kernel_as_coefficient_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ℝ) (m : Option ι) (a b : Finset ι) :
    (∑ d : Finset ι, ∑ e : Finset ι, localSieveCoeff p a d * localSieveCoeff p b e *
      localPairMean p m d e) = sieveKernel p m (a, b) := by
  classical
  by_cases ha : a.card ≤ 1
  · by_cases hb : b.card ≤ 1
    · let q := m.elim p (fun _ => p - 1)
      let M := localPairMean p m
      let C := localSieveCoeff (ι := ι) p
      have hsum : (∑ d : Finset ι, ∑ e : Finset ι, C a d * C b e * M d e) =
          ∑ d : Finset ι, C a d * (∑ e : Finset ι, C b e * M d e) := by
        refine Finset.sum_congr rfl (fun d _ => ?_)
        simp only [Finset.mul_sum, mul_assoc]
      change (∑ d : Finset ι, ∑ e : Finset ι, C a d * C b e * M d e) = _
      rw [hsum]
      rcases card_le_one_cases ha with (rfl | ⟨i, rfl⟩) <;>
        rcases card_le_one_cases hb with (rfl | ⟨j, rfl⟩)
      · cases m <;> simp [C, M, localSieveCoeff_empty, localPairMean_empty, sieveKernel, sieveMask]
      · dsimp only [C, M]
        rw [localSieveCoeff_empty, localSieveCoeff_singleton, localPairMean_empty,
          localPairMean_union_singleton p m (by simp : (∅ : Finset ι) ∪ {j} = {j})]
        by_cases h : some j = m <;>
          simp [sieveKernel, sieveMask_singleton, h, show sieveMask m (∅ : Finset ι) = ∅ by cases m <;> simp [sieveMask],
            div_eq_mul_inv] <;> ring_nf <;> simp
      · dsimp only [C, M]
        rw [localSieveCoeff_singleton]
        simp_rw [localSieveCoeff_empty]
        rw [localPairMean_empty, localPairMean_union_singleton p m (by simp : ({i} : Finset ι) ∪ ∅ = {i})]
        by_cases h : some i = m <;>
          simp [sieveKernel, sieveMask_singleton, h, show sieveMask m (∅ : Finset ι) = ∅ by cases m <;> simp [sieveMask],
            div_eq_mul_inv] <;> ring_nf <;> simp
      · dsimp only [C, M]
        rw [localSieveCoeff_singleton]
        simp_rw [localSieveCoeff_singleton]
        rw [localPairMean_empty,
          localPairMean_union_singleton p m (by simp : (∅ : Finset ι) ∪ {j} = {j}),
          localPairMean_union_singleton p m (by simp : ({i} : Finset ι) ∪ ∅ = {i})]
        by_cases hij : i = j
        · subst j
          rw [localPairMean_union_singleton p m (by simp : ({i} : Finset ι) ∪ {i} = {i})]
          by_cases hi : some i = m <;>
            simp [sieveKernel, sieveMask_singleton, hi, div_eq_mul_inv, pow_succ] <;> ring
        · rw [localPairMean_two p m hij]
          by_cases hi : some i = m <;> by_cases hj : some j = m
          · exact (hij (Option.some.inj (hi.trans hj.symm))).elim
          all_goals simp [sieveKernel, sieveMask_singleton, hi, hj, Ne.symm hij, Finset.inter_singleton,
            div_eq_mul_inv, pow_succ] <;> ring
    · simp [localSieveCoeff, sieveKernel, hb]
  · simp [localSieveCoeff, sieveKernel, ha]

private noncomputable def expandedSieveWeight {β ι : Type*} [Fintype β] [DecidableEq β]
    [Fintype ι] [DecidableEq ι] (p : β → ℝ) (y : (β → Finset ι) → ℝ)
    (d : β → Finset ι) : ℝ :=
  ∑ r : β → Finset ι, y r * ∏ j : β, localSieveCoeff (p j) (r j) (d j)

private def sievePairEquiv (β ι : Type*) :
    ((β → Finset ι) × (β → Finset ι)) ≃ (β → Finset ι × Finset ι) where
  toFun d j := (d.1 j, d.2 j)
  invFun z := (fun j => (z j).1, fun j => (z j).2)
  left_inv d := Prod.ext rfl rfl
  right_inv z := funext (fun _ => Prod.eta _)

private lemma expanded_modelMoment_eq_kernel {β ι : Type*} [Fintype β] [DecidableEq β]
    [Fintype ι] [DecidableEq ι] (p : β → ℝ) (y : (β → Finset ι) → ℝ) (m : Option ι) :
    (∑ d : β → Finset ι, ∑ e : β → Finset ι,
      expandedSieveWeight p y d * expandedSieveWeight p y e *
        ∏ j : β, localPairMean (p j) m (d j) (e j)) =
      ∑ a : β → Finset ι × Finset ι, y (fun j => (a j).1) * y (fun j => (a j).2) *
        ∏ j : β, sieveKernel (p j) m (a j) := by
  classical
  rw [← Fintype.sum_prod_type' (fun (d e : β → Finset ι) =>
    expandedSieveWeight p y d * expandedSieveWeight p y e *
      ∏ j : β, localPairMean (p j) m (d j) (e j))]
  calc
    (∑ d : (β → Finset ι) × (β → Finset ι), expandedSieveWeight p y d.1 *
      expandedSieveWeight p y d.2 * ∏ j : β, localPairMean (p j) m (d.1 j) (d.2 j)) =
        ∑ z : β → Finset ι × Finset ι,
          expandedSieveWeight p y (fun j => (z j).1) * expandedSieveWeight p y (fun j => (z j).2) *
            ∏ j : β, localPairMean (p j) m (z j).1 (z j).2 := by
      exact Fintype.sum_equiv (sievePairEquiv β ι) _ _ (fun _ => rfl)
    _ = ∑ r : β → Finset ι, ∑ s : β → Finset ι, y r * y s *
        ∏ j : β, sieveKernel (p j) m (r j, s j) := by
      unfold expandedSieveWeight
      rw [integrate_two_product_weights y y
        (fun j r (z : Finset ι × Finset ι) => localSieveCoeff (p j) r z.1)
        (fun j s (z : Finset ι × Finset ι) => localSieveCoeff (p j) s z.2)
        (fun j z => localPairMean (p j) m z.1 z.2)]
      refine Finset.sum_congr rfl (fun r _ => Finset.sum_congr rfl (fun s _ => ?_))
      congr 1
      refine Finset.prod_congr rfl (fun j _ => ?_)
      rw [Fintype.sum_prod_type]
      exact local_kernel_as_coefficient_sum (p j) m (r j) (s j)
    _ = _ := by
      rw [← Fintype.sum_prod_type' (fun (r s : β → Finset ι) =>
        y r * y s * ∏ j : β, sieveKernel (p j) m (r j, s j))]
      exact Fintype.sum_equiv (sievePairEquiv β ι) _ _ (fun _ => rfl)

private def transposeSieveSets {β ι : Type*} [Fintype β] [DecidableEq ι]
    (a : β → Finset ι) (i : ι) : Finset β :=
  Finset.univ.filter (fun p => i ∈ a p)

private def selectorPrimes {T : Finset ℕ} {ι : Type*} [DecidableEq ι]
    (a : T → Finset ι) : Finset T :=
  Finset.univ.filter (fun p => a p ≠ ∅)

private lemma primeSubsetValue_mono {T : Finset ℕ}
    (hT : ∀ p ∈ T, 0 < p) {s t : Finset T} (hst : s ⊆ t) :
    primeSubsetValue s ≤ primeSubsetValue t :=
  Finset.prod_le_prod_of_subset_of_one_le' hst (fun p _ _ => hT p p.2)

private lemma selectorPrimes_le_product {ι : Type*} [Fintype ι] [DecidableEq ι]
    {T : Finset ℕ} (hT : ∀ p ∈ T, 0 < p) (a : T → Finset ι) :
    primeSubsetValue (selectorPrimes a) ≤
      ∏ i : ι, primeSubsetValue (transposeSieveSets a i) := by
  classical
  unfold primeSubsetValue selectorPrimes transposeSieveSets
  simp only [Finset.prod_filter]
  rw [Finset.prod_comm]
  refine Finset.prod_le_prod' (fun p _ => ?_)
  rw [← Finset.prod_filter, Finset.filter_mem_eq_inter, Finset.univ_inter, Finset.prod_const]
  by_cases h : a p = ∅
  · simp [h]
  · rw [if_pos h]
    have hc : 1 ≤ (a p).card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr h)
    exact (pow_one (p : ℕ)).symm.trans_le
      (Nat.pow_le_pow_right (hT p p.2) hc)

private noncomputable def boxArrayWeight {T : Finset ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    {L : ℕ} (R : ℝ) (c : (ι → Fin L) → ℝ) (a : T → Finset ι) : ℝ :=
  tupleBoxWeight R c (fun i => primeSubsetValue (transposeSieveSets a i))

private lemma boxArrayWeight_support {ι : Type*} [Fintype ι] [DecidableEq ι] {T : Finset ℕ}
    (hT : ∀ p ∈ T, 0 < p) {L : ℕ} (hL : 0 < L) {R : ℝ} (hR : 1 ≤ R)
    (c : (ι → Fin L) → ℝ) (hc : ∀ a, L < ∑ i, ((a i).val + 1) → c a = 0)
    {r : T → Finset ι} (hr : boxArrayWeight R c r ≠ 0) :
    (primeSubsetValue (selectorPrimes r) : ℝ) ≤ R := by
  by_contra! h
  apply hr
  unfold boxArrayWeight
  apply tupleBoxWeight_support hL hR c hc
  apply h.trans_le
  rw [← Nat.cast_prod]
  exact_mod_cast selectorPrimes_le_product hT r

private lemma expandedSieveWeight_support {ι : Type*} [Fintype ι] [DecidableEq ι] {T : Finset ℕ}
    (hT : ∀ p ∈ T, 0 < p) (y : (T → Finset ι) → ℝ) (R : ℝ)
    (hy : ∀ r, y r ≠ 0 → (primeSubsetValue (selectorPrimes r) : ℝ) ≤ R)
    {d : T → Finset ι} (hd : expandedSieveWeight (fun p : T => (p : ℕ)) y d ≠ 0) :
    (∀ p, (d p).card ≤ 1) ∧ (primeSubsetValue (selectorPrimes d) : ℝ) ≤ R := by
  classical
  obtain ⟨r, hr⟩ : ∃ r : T → Finset ι, y r * ∏ p : T,
      localSieveCoeff (p : ℕ) (r p) (d p) ≠ 0 := by
    by_contra! hh
    exact hd (Finset.sum_eq_zero (fun r _ => hh r))
  have hr₁ : ∀ p : T, (r p).card ≤ 1 ∧ d p ⊆ r p := by
    intro p
    by_contra h
    have hzero : localSieveCoeff (p : ℕ) (r p) (d p) = 0 := if_neg h
    exact hr (by rw [Finset.prod_eq_zero (Finset.mem_univ p) hzero, mul_zero])
  have hr₂ : y r ≠ 0 := fun h => hr (by rw [h, zero_mul])
  have hsub : selectorPrimes d ⊆ selectorPrimes r := by
    intro p hp
    have hd' := (Finset.mem_filter.mp hp).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, fun he => ?_⟩
    exact hd' (Finset.subset_empty.mp (he ▸ (hr₁ p).2))
  exact ⟨fun p => (Finset.card_le_card (hr₁ p).2).trans (hr₁ p).1,
    (Nat.cast_le.mpr (primeSubsetValue_mono hT hsub)).trans (hy r hr₂)⟩

private noncomputable def boxScale (W L : ℕ) (R : ℝ) : ℝ :=
  ((W.totient : ℝ) / (W : ℝ)) * Real.log R / (L : ℝ)

private lemma boxScale_pos {W L : ℕ} (hW : 0 < W) (hL : 0 < L) {R : ℝ} (hR : 1 < R) :
    0 < boxScale W L R :=
  div_pos (mul_pos (div_pos (Nat.cast_pos.mpr (Nat.totient_pos.mpr hW)) (Nat.cast_pos.mpr hW))
    (Real.log_pos hR)) (Nat.cast_pos.mpr hL)

private lemma tendsto_boxScale_atTop {W L : ℕ} (hW : 0 < W) (hL : 0 < L) :
    Tendsto (boxScale W L) atTop atTop := by
  have hρ : (0 : ℝ) < W.totient / (W : ℝ) :=
    div_pos (Nat.cast_pos.mpr (Nat.totient_pos.mpr hW)) (Nat.cast_pos.mpr hW)
  have ht := Real.tendsto_log_atTop.const_mul_atTop hρ
  exact ht.atTop_div_const (Nat.cast_pos.mpr hL)

private lemma tendsto_boxMass_div_scale {W L : ℕ} (hW : 0 < W) (j : Fin L) :
    Tendsto (fun R : ℝ => boxMass W R j / boxScale W L R) atTop (𝓝 1) := by
  obtain ⟨C, _, hC⟩ := logBox_mass_asymp hW
  have hL : 0 < L := Nat.zero_lt_of_lt j.isLt
  have habs : ∀ᶠ R : ℝ in atTop, |boxMass W R j - boxScale W L R| ≤ C := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR
    exact hC R hR j
  have ht : Tendsto (fun R : ℝ =>
      (boxMass W R j - boxScale W L R) / boxScale W L R) atTop (𝓝 0) :=
    tendsto_bdd_div_atTop_nhds_zero
      (habs.mono (fun t h => (abs_le.mp h).1))
      (habs.mono (fun t h => (abs_le.mp h).2))
      (tendsto_boxScale_atTop hW hL)
  have ht' := ht.add (tendsto_const_nhds (x := (1 : ℝ)) (f := (atTop : Filter ℝ)))
  have he : (fun R : ℝ => (boxMass W R j - boxScale W L R) / boxScale W L R + 1)
      =ᶠ[atTop] (fun R : ℝ => boxMass W R j / boxScale W L R) := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with R hR
    rw [sub_div, div_self (boxScale_pos hW hL hR).ne', sub_add_cancel]
  simpa only [zero_add] using ht'.congr' he

private def sieveDegree {ι : Type*} [Fintype ι] (m : Option ι) : ℕ :=
  Fintype.card ι + m.elim 0 (fun _ => 1)

private lemma boxMomentPolynomial_scale {ι : Type*} [Fintype ι] [DecidableEq ι] {L : ℕ}
    (c : (ι → Fin L) → ℝ) (m : Option ι) (u : ℝ) (x : Fin L → ℝ) :
    boxMomentPolynomial c m (fun j => u * x j) =
      u ^ sieveDegree m * boxMomentPolynomial c m x := by
  classical
  have hprod : (∏ i : ι, u * (if some i = m then u else 1)) = u ^ sieveDegree m := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
    cases m with
    | none => simp [sieveDegree]
    | some j =>
      rw [show (∏ i : ι, if some i = some j then u else 1) = u by
        rw [Finset.prod_eq_single j]
        · simp
        · intro i _ h
          simp [h]
        · simp]
      simp [sieveDegree, pow_succ]
  unfold boxMomentPolynomial
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
  have hpoint : ∀ i : ι,
      (if some i = m then (u * x (a i)) * (u * x (b i))
        else if a i = b i then u * x (a i) else 0) =
      (u * (if some i = m then u else 1)) *
        (if some i = m then x (a i) * x (b i) else if a i = b i then x (a i) else 0) := by
    intro i
    by_cases hi : some i = m
    · simp only [hi, if_true]
      ring
    · by_cases hab : a i = b i <;> simp [hi, hab]
  simp only [hpoint, Finset.prod_mul_distrib, hprod]
  ring

private lemma tendsto_normalized_boxMoment {ι : Type*} [Fintype ι] [DecidableEq ι]
    {W L : ℕ} (hW : 0 < W) (c : (ι → Fin L) → ℝ) (m : Option ι) :
    Tendsto (fun R : ℝ => boxMomentPolynomial c m (fun j => boxMass W R j / boxScale W L R))
      atTop (𝓝 (boxMomentPolynomial c m (fun _ => 1))) := by
  unfold boxMomentPolynomial
  apply tendsto_finsetSum _ (fun a _ => ?_)
  apply tendsto_finsetSum _ (fun b _ => ?_)
  apply Tendsto.const_mul
  apply tendsto_finsetProd _ (fun i _ => ?_)
  have h₁ := tendsto_boxMass_div_scale hW (a i)
  have h₂ := tendsto_boxMass_div_scale hW (b i)
  by_cases hi : some i = m
  · simpa only [hi, if_true] using h₁.mul h₂
  · by_cases hab : a i = b i
    · simpa only [hi, if_false, hab, if_true] using h₁
    · simpa only [hi, if_false, hab] using
        (tendsto_const_nhds (x := (0 : ℝ)) (f := (atTop : Filter ℝ)))

private lemma boxMomentPolynomial_one_none {ι : Type*} [Fintype ι] [DecidableEq ι] {L : ℕ}
    (c : (ι → Fin L) → ℝ) :
    boxMomentPolynomial c (none : Option ι) (fun _ => 1) = ∑ a : ι → Fin L, (c a) ^ 2 := by
  classical
  unfold boxMomentPolynomial
  simp only [Option.some_ne_none, if_false]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Finset.sum_eq_single a]
  · simp [pow_two]
  · intro b _ hb
    have hne : ¬ ∀ i, a i = b i := fun h => hb (funext h).symm
    obtain ⟨i, hi⟩ := not_forall.mp hne
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi), mul_zero]
  · simp

private lemma sum_agree_off_coordinate {ι σ : Type*} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
    (a : ι → σ) (m : ι) (c : (ι → σ) → ℝ) :
    (∑ b ∈ (Finset.univ : Finset (ι → σ)).filter (fun b => ∀ i, i ≠ m → a i = b i), c b) =
      ∑ j : σ, c (Function.update a m j) := by
  classical
  refine Finset.sum_nbij' (fun b : ι → σ => b m) (Function.update a m) ?_ ?_ ?_ ?_ ?_
  · simp
  · intro j _
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun i hi => (Function.update_of_ne hi j a).symm⟩
  · intro b hb
    funext i
    by_cases hi : i = m
    · subst i
      simp
    · rw [Function.update_of_ne hi]
      exact (Finset.mem_filter.mp hb).2 i hi
  · simp
  · intro b hb
    congr
    funext i
    by_cases hi : i = m
    · subst i
      simp
    · rw [Function.update_of_ne hi]
      exact ((Finset.mem_filter.mp hb).2 i hi).symm

private lemma boxMomentPolynomial_one_some {ι : Type*} [Fintype ι] [DecidableEq ι] {L : ℕ}
    (c : (ι → Fin L) → ℝ) (m : ι) (j₀ : Fin L) :
    boxMomentPolynomial c (some m) (fun _ => 1) =
      ∑ a ∈ (Finset.univ : Finset (ι → Fin L)).filter (fun a => a m = j₀),
        (∑ j : Fin L, c (Function.update a m j)) ^ 2 := by
  classical
  unfold boxMomentPolynomial
  have hprod (a b : ι → Fin L) :
      (∏ i : ι, (if some i = some m then (1 : ℝ) * 1 else if a i = b i then 1 else 0)) =
        if ∀ i, i ≠ m → a i = b i then 1 else 0 := by
    by_cases h : ∀ i, i ≠ m → a i = b i
    · rw [if_pos h]
      apply Finset.prod_eq_one
      intro i _
      by_cases hi : i = m
      · simp [hi]
      · simp [hi, h i hi]
    · rw [if_neg h]
      obtain ⟨i, hh⟩ := not_forall.mp h
      have hi : i ≠ m := fun he => hh (fun hn => (hn he).elim)
      have hab : a i ≠ b i := fun he => hh (fun _ => he)
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi, hab])
  change (∑ a : ι → Fin L, ∑ b : ι → Fin L, c a * c b *
    ∏ i : ι, (if some i = some m then (1 : ℝ) * 1 else if a i = b i then 1 else 0)) = _
  simp_rw [hprod, mul_assoc, ← Finset.mul_sum]
  have hinner (a : ι → Fin L) :
      (∑ b : ι → Fin L, c b * (if ∀ i, i ≠ m → a i = b i then 1 else 0)) =
        ∑ j : Fin L, c (Function.update a m j) := by
    simp only [mul_ite, mul_one, mul_zero]
    rw [← Finset.sum_filter]
    exact sum_agree_off_coordinate a m c
  simp_rw [hinner]
  let U := (Finset.univ : Finset (ι → Fin L)).filter (fun a => a m = j₀)
  let e : (ι → Fin L) ≃ U × Fin L :=
    { toFun := fun a => (⟨Function.update a m j₀, by simp [U]⟩, a m)
      invFun := fun af => Function.update af.1 m af.2
      left_inv := fun a => by
        funext i
        by_cases hi : i = m <;> simp [hi, Function.update_of_ne]
      right_inv := fun af => by
        apply Prod.ext
        · apply Subtype.ext
          funext i
          have ha : (af.1 : ι → Fin L) m = j₀ := (Finset.mem_filter.mp af.1.2).2
          by_cases hi : i = m <;> simp [hi, ha, Function.update_of_ne]
        · simp }
  have heq : (∑ a : ι → Fin L, c a * ∑ j : Fin L, c (Function.update a m j)) =
      ∑ af : U × Fin L, c (Function.update af.1 m af.2) *
        ∑ j : Fin L, c (Function.update af.1 m j) := by
    apply Fintype.sum_equiv e
    intro a
    change c a * (∑ j : Fin L, c (Function.update a m j)) =
      c (Function.update (Function.update a m j₀) m (a m)) *
        ∑ j : Fin L, c (Function.update (Function.update a m j₀) m j)
    simp [Function.update_idem]
  rw [heq, Fintype.sum_prod_type]
  change _ = ∑ a ∈ U, _
  rw [Finset.sum_subtype U (fun _ => Iff.rfl)]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  change (∑ y : Fin L, c (Function.update (a : ι → Fin L) m y) *
    ∑ j : Fin L, c (Function.update (a : ι → Fin L) m j)) = _
  rw [← Finset.sum_mul, pow_two]

private lemma localSieveCoeff_sum_abs_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : ℝ} (hp : 2 ≤ p) (d : Finset ι) :
    (∑ r : Finset ι, |localSieveCoeff p r d|) ≤ (1 + (p - 1)⁻¹) ^ Fintype.card ι := by
  classical
  let w := (p - 1)⁻¹
  have hw : 0 ≤ w := inv_nonneg.mpr (by linarith)
  by_cases hd : d.card ≤ 1
  · rcases card_le_one_cases hd with (rfl | ⟨i, rfl⟩)
    · rw [← sum_pow_card_finset w]
      refine Finset.sum_le_sum (fun r _ => ?_)
      unfold localSieveCoeff
      split
      · rw [Finset.card_empty, pow_zero, mul_one, abs_of_nonneg (pow_nonneg hw _)]
      · rw [abs_zero]
        exact pow_nonneg hw _
    · rw [Finset.sum_eq_single ({i} : Finset ι)]
      · have he : w * p = 1 + w := by
          unfold w
          field_simp [show p - 1 ≠ 0 by linarith]
          ring
        simp only [localSieveCoeff, Finset.card_singleton, le_refl, Finset.Subset.rfl, and_self,
          if_true, pow_one, abs_mul, abs_neg, abs_of_nonneg (show 0 ≤ (p - 1)⁻¹ from hw), abs_of_nonneg (show 0 ≤ p by linarith)]
        change w * p ≤ (1 + w) ^ Fintype.card ι
        rw [he]
        apply le_self_pow₀ (by linarith)
        exact Nat.ne_of_gt (Fintype.card_pos_iff.mpr ⟨i⟩)
      · intro r _ hr
        have h : ¬ (r.card ≤ 1 ∧ ({i} : Finset ι) ⊆ r) := by
          rintro ⟨hc, hsub⟩
          exact hr (Finset.eq_of_subset_of_card_le hsub (by simpa using hc)).symm
        rw [localSieveCoeff, if_neg h, abs_zero]
      · simp
  · have hz : ∀ r : Finset ι, localSieveCoeff p r d = 0 := by
      intro r
      unfold localSieveCoeff
      rw [if_neg (fun h => hd ((Finset.card_le_card h.2).trans h.1))]
    simp only [hz, abs_zero, Finset.sum_const_zero]
    exact pow_nonneg (by linarith) _

private lemma expandedSieveWeight_abs_le {ι : Type*} [Fintype ι] [DecidableEq ι] {T : Finset ℕ}
    (hT : ∀ p ∈ T, 2 ≤ p) (y : (T → Finset ι) → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hy : ∀ r, |y r| ≤ C) (d : T → Finset ι) :
    |expandedSieveWeight (fun p : T => (p : ℕ)) y d| ≤
      C * (∏ p : T, (1 + localPrimeWeight p)) ^ Fintype.card ι := by
  classical
  unfold expandedSieveWeight
  calc
      _ ≤ ∑ r : T → Finset ι, |y r * ∏ p : T, localSieveCoeff (p : ℕ) (r p) (d p)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ r : T → Finset ι, C * ∏ p : T, |localSieveCoeff (p : ℕ) (r p) (d p)| := by
        refine Finset.sum_le_sum (fun r _ => ?_)
        rw [abs_mul, Finset.abs_prod]
        exact mul_le_mul_of_nonneg_right (hy r) (Finset.prod_nonneg (fun _ _ => abs_nonneg _))
      _ = C * ∏ p : T, (∑ a : Finset ι, |localSieveCoeff (p : ℕ) a (d p)|) := by
        rw [← Finset.mul_sum, ← Fintype.prod_sum (fun (p : T) (r : Finset ι) =>
          |localSieveCoeff (p : ℕ) r (d p)|)]
      _ ≤ _ := by
        rw [← Finset.prod_pow]
        apply mul_le_mul_of_nonneg_left _ hC
        refine Finset.prod_le_prod (fun p _ => Finset.sum_nonneg (fun _ _ => abs_nonneg _)) (fun p _ => ?_)
        exact localSieveCoeff_sum_abs_le (by exact_mod_cast hT p p.2) (d p)

private lemma selectorPrimes_union_value_le {T : Finset ℕ} (hT : ∀ p ∈ T, 0 < p)
    (s t : Finset T) :
    primeSubsetValue (s ∪ t) ≤ primeSubsetValue s * primeSubsetValue t := by
  classical
  have he := Finset.prod_union_inter (s₁ := s) (s₂ := t) (f := fun p : T => (p : ℕ))
  change primeSubsetValue (s ∪ t) * primeSubsetValue (s ∩ t) =
    primeSubsetValue s * primeSubsetValue t at he
  rw [← he]
  exact Nat.le_mul_of_pos_right _ (Finset.prod_pos (fun p _ => hT p p.2))

private lemma count_supported_selectors {ι : Type*} [Fintype ι] [DecidableEq ι] {T : Finset ℕ}
    (hT : ∀ p ∈ T, 2 ≤ p) {R : ℝ} (hR : 0 ≤ R) (S : Finset (T → Finset ι))
    (hS : ∀ d ∈ S, (∀ p, (d p).card ≤ 1) ∧ (primeSubsetValue (selectorPrimes d) : ℝ) ≤ R) :
    (S.card : ℝ) ≤ R * (∏ p : T, (1 + localPrimeWeight p)) ^ Fintype.card ι := by
  classical
  let g : T → Finset ι → ℝ := fun p d => (localPrimeWeight p) ^ d.card
  have hlocal : ∀ p : T, 0 ≤ localPrimeWeight p := by
    intro p
    have h : (2 : ℝ) ≤ (p : ℕ) := by exact_mod_cast hT p p.2
    exact inv_nonneg.mpr (by linarith)
  calc
    _ = ∑ _d ∈ S, (1 : ℝ) := by simp
    _ ≤ ∑ d ∈ S, R * ∏ p : T, g p (d p) := by
      refine Finset.sum_le_sum (fun d hd => ?_)
      obtain ⟨hvalid, hR'⟩ := hS d hd
      have hpos : (0 : ℝ) < primeSubsetValue (selectorPrimes d) := by
        exact Nat.cast_pos.mpr (Finset.prod_pos (fun p _ => by have := hT p p.2; omega))
      have hprod : ((primeSubsetValue (selectorPrimes d) : ℕ) : ℝ)⁻¹ ≤ ∏ p : T, g p (d p) := by
        rw [primeSubsetValue, Nat.cast_prod, ← Finset.prod_inv_distrib, selectorPrimes, Finset.prod_filter]
        refine Finset.prod_le_prod (fun p _ => by split <;> positivity) (fun p _ => ?_)
        by_cases hp : d p = ∅
        · simp [hp, g]
        · have hc : (d p).card = 1 := le_antisymm (hvalid p)
            (Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hp))
          simp only [if_pos hp, g, hc, pow_one]
          have h : (2 : ℝ) ≤ (p : ℕ) := by exact_mod_cast hT p p.2
          exact inv_anti₀ (by linarith) (by linarith)
      calc
        1 = (primeSubsetValue (selectorPrimes d) : ℝ) *
            (primeSubsetValue (selectorPrimes d) : ℝ)⁻¹ := (mul_inv_cancel₀ hpos.ne').symm
        _ ≤ R * (∏ p : T, g p (d p)) := mul_le_mul hR' hprod (inv_nonneg.mpr hpos.le) hR
    _ ≤ ∑ d : T → Finset ι, R * ∏ p : T, g p (d p) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun d _ _ =>
        mul_nonneg hR (Finset.prod_nonneg (fun p _ => pow_nonneg (hlocal p) _)))
    _ = _ := by
      rw [← Finset.mul_sum, ← Fintype.prod_sum g, ← Finset.prod_pow]
      simp only [g, sum_pow_card_finset]

private noncomputable def selectorRootWeight {ι : Type*} {T : Finset ℕ}
    (h : ι → ℕ) (n : ℕ) (d : T → Finset ι) : ℝ := by
  classical
  exact if ∀ p : T, ∀ i ∈ d p, (p : ℕ) ∣ n + h i then 1 else 0

private lemma selectorRootWeight_mul {ι : Type*} [DecidableEq ι] {T : Finset ℕ}
    (h : ι → ℕ) (n : ℕ) (d e : T → Finset ι) :
    selectorRootWeight h n d * selectorRootWeight h n e =
      selectorRootWeight h n (fun p => d p ∪ e p) := by
  classical
  have he : (∀ p : T, ∀ i ∈ d p ∪ e p, (p : ℕ) ∣ n + h i) ↔
      (∀ p : T, ∀ i ∈ d p, (p : ℕ) ∣ n + h i) ∧ (∀ p : T, ∀ i ∈ e p, (p : ℕ) ∣ n + h i) := by
    constructor
    · exact fun hh => ⟨fun p i hi => hh p i (Finset.mem_union_left _ hi),
        fun p i hi => hh p i (Finset.mem_union_right _ hi)⟩
    · rintro ⟨hd, he⟩ p i hi
      exact (Finset.mem_union.mp hi).elim (hd p i) (he p i)
  unfold selectorRootWeight
  by_cases hd : ∀ p : T, ∀ i ∈ d p, (p : ℕ) ∣ n + h i
  · by_cases he' : ∀ p : T, ∀ i ∈ e p, (p : ℕ) ∣ n + h i
    · rw [if_pos hd, if_pos he', if_pos (he.mpr ⟨hd, he'⟩), one_mul]
    · rw [if_pos hd, if_neg he', if_neg (fun h => he' (he.mp h).2), mul_zero]
  · rw [if_neg hd, if_neg (fun h => hd (he.mp h).1), zero_mul]

private noncomputable def sieveObservable {ι : Type*} (h : ι → ℕ) (m : Option ι) (n : ℕ) : ℝ :=
  m.elim 1 (fun i => primeLog (n + h i))

private noncomputable def sieveObservedWeight {ι : Type*} [Fintype ι] [DecidableEq ι] {T : Finset ℕ}
    (h : ι → ℕ) (coeff : (T → Finset ι) → ℝ) (n : ℕ) : ℝ :=
  ∑ d : T → Finset ι, coeff d * selectorRootWeight h n d

private lemma sum_observedMoment_expanded {ι : Type*} [Fintype ι] [DecidableEq ι]
    {T : Finset ℕ} (h : ι → ℕ) (coeff : (T → Finset ι) → ℝ) (S : Finset ℕ) (m : Option ι) :
    (∑ n ∈ S, sieveObservedWeight h coeff n ^ 2 * sieveObservable h m n) =
      ∑ d : T → Finset ι, ∑ e : T → Finset ι, coeff d * coeff e *
        ∑ n ∈ S, selectorRootWeight h n (fun p => d p ∪ e p) * sieveObservable h m n := by
  classical
  calc
    _ = ∑ n ∈ S, ∑ d : T → Finset ι, ∑ e : T → Finset ι, coeff d * coeff e *
          (selectorRootWeight h n (fun p => d p ∪ e p) * sieveObservable h m n) := by
      refine Finset.sum_congr rfl (fun n _ => ?_)
      rw [pow_two, sieveObservedWeight, Finset.sum_mul_sum, Finset.sum_mul]
      simp only [Finset.sum_mul]
      refine Finset.sum_congr rfl (fun d _ => Finset.sum_congr rfl (fun e _ => ?_))
      rw [← selectorRootWeight_mul]
      ring
    _ = _ := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun d _ => ?_)
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun e _ => ?_)
      rw [Finset.mul_sum]

private def selectorModulus {ι : Type*} [DecidableEq ι] {T : Finset ℕ}
    (W : ℕ) (d : T → Finset ι) : ℕ :=
  W * primeSubsetValue (selectorPrimes d)

private lemma totient_selectorModulus {W : ℕ} {T : Finset ℕ}
    (hp : ∀ p ∈ T, p.Prime) (hndvd : ∀ p ∈ T, ¬ p ∣ W) (s : Finset T) :
    (W * primeSubsetValue s).totient = W.totient * ∏ p ∈ s, ((p : ℕ) - 1) := by
  let e : T ↪ ℕ := ⟨Subtype.val, Subtype.val_injective⟩
  have hmap : primeSubsetValue s = ∏ p ∈ s.map e, p := by rw [Finset.prod_map]; rfl
  have hprime : ∀ p ∈ s.map e, p.Prime := by
    intro p pp
    obtain ⟨p, _, rfl⟩ := Finset.mem_map.mp pp
    exact hp p p.2
  have hcop : W.Coprime (primeSubsetValue s) :=
    Nat.Coprime.prod_right (fun p _ => ((hp p p.2).coprime_iff_not_dvd.mpr (hndvd p p.2)).symm)
  rw [Nat.totient_mul hcop, hmap, Nat.totient_eq_div_primeFactors_mul (∏ p ∈ s.map e, p),
    Nat.primeFactors_prod hprime, Nat.div_self (Finset.prod_pos (fun p hp => (hprime p hp).pos)),
    one_mul, Finset.prod_map]
  rfl

private lemma selectorModulus_pos {ι : Type*} [DecidableEq ι] {W : ℕ} {T : Finset ℕ}
    (hW : 0 < W) (hp : ∀ p ∈ T, p.Prime) (d : T → Finset ι) :
    0 < selectorModulus W d :=
  Nat.mul_pos hW (Finset.prod_pos (fun p _ => (hp p p.2).pos))

private noncomputable def sieveTermError {ι : Type*} (h : ι → ℕ) (m : Option ι)
    (x y : ℝ) (q : ℕ) : ℝ :=
  m.elim 2 (fun i => worstProgressionError (y + h i) q + worstProgressionError (x + h i) q)

private lemma sieveTermError_nonneg {ι : Type*} (h : ι → ℕ) (m : Option ι)
    (x y : ℝ) (q : ℕ) : 0 ≤ sieveTermError h m x y q := by
  cases m with
  | none => norm_num [sieveTermError]
  | some i => exact add_nonneg (worstProgressionError_nonneg _ _) (worstProgressionError_nonneg _ _)

private lemma sieve_single_term_estimate {ι : Type*} [DecidableEq ι] {W ν : ℕ}
    (hW : 0 < W) (h : ι → ℕ) (hcop : ∀ i, (ν + h i).Coprime W)
    {R x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (hRx : R ≤ x)
    (hsep : ∀ p ∈ siftedPrimes W R, Function.Injective (fun i => h i % p))
    (m : Option ι) (d : siftedPrimes W R → Finset ι) :
    |(∑ n ∈ (Finset.Ioc ⌊x⌋₊ ⌊y⌋₊).filter (fun n => n ≡ ν [MOD W]),
      selectorRootWeight h n d * sieveObservable h m n) -
      ((y - x) / (m.elim (W : ℝ) (fun _ => (W.totient : ℝ)))) *
      (∏ p : siftedPrimes W R, localPairMean (p : ℕ) m (d p) ∅)| ≤
      sieveTermError h m x y (selectorModulus W d) := by
  classical
  let T := siftedPrimes W R
  let P := selectorPrimes d
  let Q := selectorModulus W d
  let I := (Finset.Ioc ⌊x⌋₊ ⌊y⌋₊).filter (fun n => n ≡ ν [MOD W])
  let e : T ↪ ℕ := ⟨Subtype.val, Subtype.val_injective⟩
  have hp : ∀ p ∈ T, p.Prime := fun p hp => siftedPrimes_prime hp
  have hn : ∀ p ∈ T, ¬ p ∣ W := fun p hp => siftedPrimes_not_dvd hp
  by_cases hg : ∀ p : T, (d p).card ≤ 1 ∧ sieveMask m (d p) = d p
  · let iₚ : (p : T) → p ∈ P → ι := fun p hp =>
      (Finset.nonempty_iff_ne_empty.mpr (Finset.mem_filter.mp hp).2).choose
    have hip (p : T) (hp : p ∈ P) : iₚ p hp ∈ d p :=
      (Finset.nonempty_iff_ne_empty.mpr (Finset.mem_filter.mp hp).2).choose_spec
    let a : ℕ → ℕ := fun p =>
      if hp : p ∈ T then if hs : (⟨p, hp⟩ : T) ∈ P then h (iₚ _ hs) else 0 else 0
    have ha (p : T) (hs : p ∈ P) : a p = h (iₚ p hs) := by
      unfold a
      rw [dif_pos p.2, dif_pos hs]
    have hQ : Q = W * ∏ p ∈ P.map e, p := by
      rw [Finset.prod_map]
      rfl
    obtain ⟨z, hz⟩ := exists_sieve_residue (ν := ν) hW (P.map e)
      (fun p hp' => by obtain ⟨p, _, rfl⟩ := Finset.mem_map.mp hp'; exact hp p p.2)
      (fun p hp' => by obtain ⟨p, _, rfl⟩ := Finset.mem_map.mp hp'; exact hn p p.2) a
    rw [← hQ] at hz
    have hroot : ∀ n : ℕ,
        (∀ p : T, ∀ j ∈ d p, (p : ℕ) ∣ n + h j) ↔
          ∀ p ∈ P.map e, p ∣ n + a p := by
      intro n
      constructor
      · intro hh p hp'
        obtain ⟨p, hs, rfl⟩ := Finset.mem_map.mp hp'
        change (p : ℕ) ∣ n + a p
        rw [ha p hs]
        exact hh p _ (hip p hs)
      · intro hh p j hj
        have hs : p ∈ P := Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          fun h => by simpa [h] using hj⟩
        have hdiv := hh p (Finset.mem_map_of_mem _ hs)
        rw [ha p hs] at hdiv
        rwa [Finset.card_le_one.mp (hg p).1 _ (hip p hs) _ hj] at hdiv
    have hsum : (∑ n ∈ I, selectorRootWeight h n d * sieveObservable h m n) =
        ∑ n ∈ (Finset.Ioc ⌊x⌋₊ ⌊y⌋₊).filter (fun n => n ≡ z [MOD Q]), sieveObservable h m n := by
      have heq : I.filter (fun n => ∀ p : T, ∀ j ∈ d p, (p : ℕ) ∣ n + h j) =
          (Finset.Ioc ⌊x⌋₊ ⌊y⌋₊).filter (fun n => n ≡ z [MOD Q]) := by
        ext n
        simp only [I, Finset.mem_filter, hroot, hz, and_assoc]
      simp only [selectorRootWeight, ite_mul, one_mul, zero_mul]
      rw [← Finset.sum_filter, heq]
    have hmean : (∏ p : T, localPairMean (p : ℕ) m (d p) ∅) =
        ∏ p ∈ P, (m.elim (p : ℝ) (fun _ => (p : ℝ) - 1))⁻¹ := by
      rw [show P = Finset.univ.filter (fun p => d p ≠ ∅) from rfl, Finset.prod_filter]
      refine Finset.prod_congr rfl (fun p _ => ?_)
      by_cases hu : d p = ∅
      · simp [hu, localPairMean_empty]
      · have hc : (d p).card = 1 := le_antisymm (hg p).1
          (Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hu))
        simp [localPairMean, hu, hc, (hg p).2]
    rw [hsum, hmean]
    have hQpos := selectorModulus_pos hW hp d
    cases m with
    | none =>
      simp only [sieveObservable, sieveTermError, Option.elim_none, Finset.sum_const, nsmul_eq_mul, mul_one]
      have hscale : (y - x) / (W : ℝ) * ∏ p ∈ P, (↑(p : ℕ) : ℝ)⁻¹ = (y - x) / (Q : ℝ) := by
        rw [Finset.prod_inv_distrib, div_eq_mul_inv, mul_assoc, ← mul_inv]
        congr 1
        simp only [Q, selectorModulus, primeSubsetValue, P, Nat.cast_mul, Nat.cast_prod]
      rw [hscale]
      exact residueInterval_error hx hxy hQpos
    | some j =>
      simp only [sieveObservable, sieveTermError, Option.elim_some]
      have hscale : (y - x) / (W.totient : ℝ) * ∏ p ∈ P, ((↑(p : ℕ) : ℝ) - 1)⁻¹ =
          (y - x) / (Q.totient : ℝ) := by
        rw [Finset.prod_inv_distrib, div_eq_mul_inv, mul_assoc, ← mul_inv]
        congr 1
        rw [show Q = W * primeSubsetValue P from rfl, totient_selectorModulus hp hn,
          Nat.cast_mul, Nat.cast_prod]
        congr 1
        apply congrArg (fun x : ℝ => (W.totient : ℝ) * x)
        exact Finset.prod_congr rfl (fun p _ => by rw [Nat.cast_sub (hp p p.2).one_le, Nat.cast_one])
      rw [hscale]
      apply primeResidueInterval_error hx hxy hQpos
      change (z + h j).Coprime Q
      rw [hQ]
      have hzm := (hz z).mp (Nat.ModEq.refl _)
      apply sieve_residue_shift_coprime _ (fun p hp' => by
        obtain ⟨p, _, rfl⟩ := Finset.mem_map.mp hp'
        exact hp p p.2) (fun p hp' => by
        obtain ⟨p, _, rfl⟩ := Finset.mem_map.mp hp'
        exact hn p p.2) a hzm (hcop j)
      intro p hs
      obtain ⟨p, hp', rfl⟩ := Finset.mem_map.mp hs
      change a p % (p : ℕ) ≠ h j % (p : ℕ)
      rw [ha p hp']
      intro he
      have hj : iₚ p hp' = j := hsep p p.2 he
      have hi := hip p hp'
      rw [hj, ← (hg p).2, sieveMask_mem] at hi
      exact hi.1 rfl
  · obtain ⟨p, hpbad⟩ := not_forall.mp hg
    have hne : d p ≠ ∅ := by
      intro h
      apply hpbad
      rw [h]
      cases m <;> simp [sieveMask]
    have hpzero : localPairMean (p : ℕ) m (d p) ∅ = 0 := by
      simp only [localPairMean, Finset.union_empty, if_neg hne]
      rw [if_neg (fun hh => hpbad ⟨hh.1.le, hh.2⟩)]
    have hzero : ∑ n ∈ I, selectorRootWeight h n d * sieveObservable h m n = 0 := by
      refine Finset.sum_eq_zero (fun n hnI => ?_)
      by_cases hs : ∀ q : T, ∀ i ∈ d q, (q : ℕ) ∣ n + h i
      · rw [selectorRootWeight, if_pos hs, one_mul]
        have hc : (d p).card ≤ 1 := Finset.card_le_one.mpr (fun i hi j hj => by
          apply hsep p p.2
          exact Nat.ModEq.add_left_cancel' n ((Nat.modEq_zero_iff_dvd.mpr (hs p i hi)).trans
            (Nat.modEq_zero_iff_dvd.mpr (hs p j hj)).symm))
        have hmask : sieveMask m (d p) ≠ d p := fun he => hpbad ⟨hc, he⟩
        cases m with
        | none => exact (hmask rfl).elim
        | some j =>
          have hj : j ∈ d p := by
            by_contra h
            exact hmask (Finset.erase_eq_of_notMem h)
          have hdvd := hs p j hj
          have hnlarge : x < (n : ℝ) :=
            (Nat.floor_lt hx).mp (Finset.mem_Ioc.mp (Finset.mem_filter.mp hnI).1).1
          have hpR : ((p : ℕ) : ℝ) ≤ R :=
            (Nat.cast_le.mpr (Finset.mem_Ioc.mp (Finset.mem_of_mem_filter _ p.2)).2).trans
              (Nat.floor_le (by
                by_contra! hneg
                have h0 := Nat.floor_eq_zero.mpr (show R < 1 by linarith)
                have hmem := (Finset.mem_Ioc.mp (Finset.mem_of_mem_filter _ p.2)).2
                have hpos := (hp p p.2).pos
                omega))
          have hlt : (p : ℕ) < n + h j := by
            have hpn : (p : ℕ) < n := by exact_mod_cast hpR.trans_lt (hRx.trans_lt hnlarge)
            omega
          have hnprime : ¬ (n + h j).Prime := by
            intro hprime
            rcases (Nat.dvd_prime hprime).mp hdvd with h1 | he
            · exact (hp p p.2).ne_one h1
            · omega
          exact if_neg hnprime
      · rw [selectorRootWeight, if_neg hs, zero_mul]
    rw [hzero, Finset.prod_eq_zero (Finset.mem_univ p) hpzero, mul_zero, sub_zero, abs_zero]
    exact sieveTermError_nonneg _ _ _ _ _

private lemma weighted_pair_discrepancy {α : Type*} [Fintype α] (coeff : α → ℝ)
    (obs pred err : α × α → ℝ) {B : ℝ} (hB : 0 ≤ B) (hc : ∀ d, |coeff d| ≤ B)
    (he : ∀ d, |obs d - pred d| ≤ err d) :
    |(∑ d : α × α, coeff d.1 * coeff d.2 * obs d) -
      ∑ d : α × α, coeff d.1 * coeff d.2 * pred d| ≤
      B ^ 2 * ∑ d ∈ (Finset.univ.filter (fun d => coeff d ≠ 0)) ×ˢ
        (Finset.univ.filter (fun d => coeff d ≠ 0)), err d := by
  classical
  let S := (Finset.univ : Finset α).filter (fun d => coeff d ≠ 0)
  let f : α × α → ℝ := fun d => coeff d.1 * coeff d.2 * (obs d - pred d)
  have hdiff : (∑ d : α × α, coeff d.1 * coeff d.2 * obs d) -
      (∑ d : α × α, coeff d.1 * coeff d.2 * pred d) = ∑ d : α × α, f d := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun _ _ => (mul_sub ..).symm)
  rw [hdiff, ← Finset.sum_subset (s₁ := S ×ˢ S) (s₂ := Finset.univ) (Finset.subset_univ _)]
  · calc
      _ ≤ ∑ d ∈ S ×ˢ S, |f d| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ d ∈ S ×ˢ S, B ^ 2 * err d := by
        refine Finset.sum_le_sum (fun d _ => ?_)
        simp only [f, abs_mul, pow_two]
        exact mul_le_mul (mul_le_mul (hc _) (hc _) (abs_nonneg _) hB) (he d) (abs_nonneg _)
          (mul_nonneg hB hB)
      _ = _ := (Finset.mul_sum ..).symm
  · intro d _ hd
    have hzero : coeff d.1 = 0 ∨ coeff d.2 = 0 := by
      by_contra! hn
      exact hd (Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hn.1⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hn.2⟩⟩)
    rcases hzero with h | h <;> simp [f, h]

private lemma localPairMean_union {ι : Type*} [DecidableEq ι]
    (p : ℝ) (m : Option ι) (d e : Finset ι) :
    localPairMean p m d e = localPairMean p m (d ∪ e) ∅ := by
  simp only [localPairMean, Finset.union_empty]

private noncomputable def sieveModelMoment {ι : Type*} [Fintype ι] [DecidableEq ι]
    (W : ℕ) (R : ℝ) (y : (siftedPrimes W R → Finset ι) → ℝ) (m : Option ι) : ℝ :=
  ∑ a : siftedPrimes W R → Finset ι × Finset ι, y (fun p => (a p).1) * y (fun p => (a p).2) *
    ∏ p : siftedPrimes W R, sieveKernel (p : ℕ) m (a p)

set_option maxHeartbeats 1500000 in
private lemma sieve_observed_difference_le {ι : Type*} [Fintype ι] [DecidableEq ι] {W ν : ℕ}
    (hW : 0 < W) (h : ι → ℕ) (hcop : ∀ i, (ν + h i).Coprime W)
    {R x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (hRx : R ≤ x)
    (hsep : ∀ p ∈ siftedPrimes W R, Function.Injective (fun i => h i % p))
    (a : (siftedPrimes W R → Finset ι) → ℝ)
    (m : Option ι) {B : ℝ} (hB : 0 ≤ B)
    (hcoeff : ∀ d, |expandedSieveWeight (fun p : siftedPrimes W R => (p : ℕ)) a d| ≤ B) :
    let T := siftedPrimes W R;
    let coeff := expandedSieveWeight (fun p : T => (p : ℕ)) a;
    let S : Finset (T → Finset ι) := Finset.univ.filter (fun d => coeff d ≠ 0);
    let I := (Finset.Ioc ⌊x⌋₊ ⌊y⌋₊).filter (fun n => n ≡ ν [MOD W]);
    |(∑ n ∈ I, sieveObservedWeight h coeff n ^ 2 * sieveObservable h m n) -
      ((y - x) / m.elim (W : ℝ) (fun _ => (W.totient : ℝ))) * sieveModelMoment W R a m| ≤
      B ^ 2 * (∑ de ∈ S ×ˢ S, sieveTermError h m x y (selectorModulus W (fun p => de.1 p ∪ de.2 p))) := by
  classical
  dsimp only
  let T := siftedPrimes W R
  let coeff := expandedSieveWeight (fun p : T => (p : ℕ)) a
  let I := (Finset.Ioc ⌊x⌋₊ ⌊y⌋₊).filter (fun n => n ≡ ν [MOD W])
  let F := (y - x) / m.elim (W : ℝ) (fun _ => (W.totient : ℝ))
  let obs : (T → Finset ι) × (T → Finset ι) → ℝ := fun de =>
    ∑ n ∈ I, selectorRootWeight h n (fun p => de.1 p ∪ de.2 p) * sieveObservable h m n
  let pred : (T → Finset ι) × (T → Finset ι) → ℝ := fun de =>
    F * ∏ p : T, localPairMean (p : ℕ) m (de.1 p) (de.2 p)
  let err : (T → Finset ι) × (T → Finset ι) → ℝ := fun de =>
    sieveTermError h m x y (selectorModulus W (fun p => de.1 p ∪ de.2 p))
  have he : ∀ de, |obs de - pred de| ≤ err de := by
    intro de
    unfold obs pred err
    have he' : (∏ p : T, localPairMean (p : ℕ) m (de.1 p) (de.2 p)) =
        ∏ p : T, localPairMean (p : ℕ) m (de.1 p ∪ de.2 p) ∅ :=
      Finset.prod_congr rfl (fun p _ => localPairMean_union _ _ _ _)
    rw [he']
    exact sieve_single_term_estimate hW h hcop hx hxy hRx hsep m _
  change |(∑ n ∈ I, sieveObservedWeight h coeff n ^ 2 * sieveObservable h m n) -
    F * sieveModelMoment W R a m| ≤ _
  rw [sum_observedMoment_expanded, sieveModelMoment, ← expanded_modelMoment_eq_kernel]
  have hobs : (∑ d : T → Finset ι, ∑ e : T → Finset ι, coeff d * coeff e * obs (d, e)) =
      ∑ de : (T → Finset ι) × (T → Finset ι), coeff de.1 * coeff de.2 * obs de :=
    (Fintype.sum_prod_type' (fun (d e : T → Finset ι) => coeff d * coeff e * obs (d, e))).symm
  have hpred : F * (∑ d : T → Finset ι, ∑ e : T → Finset ι, coeff d * coeff e *
      ∏ p : T, localPairMean (p : ℕ) m (d p) (e p)) =
      ∑ de : (T → Finset ι) × (T → Finset ι), coeff de.1 * coeff de.2 * pred de := by
    rw [Fintype.sum_prod_type]
    simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun d _ => Finset.sum_congr rfl (fun e _ => by unfold pred; ring))
  change |(∑ d : T → Finset ι, ∑ e : T → Finset ι, coeff d * coeff e * obs (d, e)) -
    F * (∑ d : T → Finset ι, ∑ e : T → Finset ι, coeff d * coeff e *
      ∏ p : T, localPairMean (p : ℕ) m (d p) (e p))| ≤ _
  rw [hobs, hpred]
  exact weighted_pair_discrepancy coeff obs pred err hB hcoeff he

private lemma selectorPrimes_of_union {ι : Type*} [DecidableEq ι] {T : Finset ℕ}
    (d e : T → Finset ι) :
    selectorPrimes (fun p => d p ∪ e p) = selectorPrimes d ∪ selectorPrimes e := by
  classical
  ext p
  simp [selectorPrimes, Finset.union_eq_empty]
  tauto

private lemma selector_pair_sum_by_modulus {ι : Type*} [Fintype ι] [DecidableEq ι] {T : Finset ℕ}
    (hT : ∀ p ∈ T, 0 < p) (S : Finset (T → Finset ι)) (W : ℕ) {R : ℝ}
    (hS : ∀ d ∈ S, (primeSubsetValue (selectorPrimes d) : ℝ) ≤ R)
    (E : ℕ → ℝ) (hE : ∀ q, 0 ≤ E q) :
    (∑ de ∈ S ×ˢ S, E (selectorModulus W (fun p => de.1 p ∪ de.2 p))) ≤
      ∑ s ∈ (Finset.univ : Finset (Finset T)).filter (fun s => (primeSubsetValue s : ℝ) ≤ R ^ 2),
        ((Fintype.card (Finset ι × Finset ι) : ℝ) ^ s.card) * E (W * primeSubsetValue s) := by
  classical
  let P : ((T → Finset ι) × (T → Finset ι)) → Finset T :=
    fun de => selectorPrimes de.1 ∪ selectorPrimes de.2
  let Z := (Finset.univ : Finset (Finset T)).filter (fun s => (primeSubsetValue s : ℝ) ≤ R ^ 2)
  have hmap : ∀ de ∈ S ×ˢ S, P de ∈ Z := by
    intro de hde
    obtain ⟨hd, he⟩ := Finset.mem_product.mp hde
    have hna := Nat.cast_nonneg (α := ℝ) (primeSubsetValue (selectorPrimes de.2))
    have hR : 0 ≤ R := hna.trans (hS _ he)
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    have hu := (Nat.cast_le.mpr (selectorPrimes_union_value_le hT _ _) :
      ((primeSubsetValue (P de) : ℕ) : ℝ) ≤
        ↑(primeSubsetValue (selectorPrimes de.1) * primeSubsetValue (selectorPrimes de.2)))
    rw [Nat.cast_mul] at hu
    exact hu.trans ((mul_le_mul (hS _ hd) (hS _ he) hna hR).trans_eq ((pow_two R).symm))
  simp only [selectorModulus, selectorPrimes_of_union]
  change (∑ de ∈ S ×ˢ S, E (W * primeSubsetValue (P de))) ≤ _
  rw [← Finset.sum_fiberwise_of_maps_to' hmap (fun s => E (W * primeSubsetValue s))]
  refine Finset.sum_le_sum (fun s _ => ?_)
  let F := (S ×ˢ S).filter (fun de => P de = s)
  change (∑ _de ∈ F, E (W * primeSubsetValue s)) ≤ _
  rw [Finset.sum_const, nsmul_eq_mul]
  apply mul_le_mul_of_nonneg_right _ (hE _)
  have hinj : Function.Injective (fun de : F =>
      fun p : s => ((de.val.1 p, de.val.2 p) : Finset ι × Finset ι)) := by
    intro de de' h
    apply Subtype.ext
    have hs : P de.val = s := (Finset.mem_filter.mp de.2).2
    have hs' : P de'.val = s := (Finset.mem_filter.mp de'.2).2
    have hzero (de : (T → Finset ι) × (T → Finset ι)) (he : P de = s) {p : T}
        (hp : p ∉ s) : de.1 p = ∅ ∧ de.2 p = ∅ := by
      have hh : p ∉ P de := he.symm ▸ hp
      constructor
      · by_contra hd
        exact hh (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hd⟩))
      · by_contra hd
        exact hh (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hd⟩))
    have hpt (p : T) : (de.val.1 p, de.val.2 p) = (de'.val.1 p, de'.val.2 p) := by
      by_cases hp : p ∈ s
      · exact congrFun h ⟨p, hp⟩
      · obtain ⟨h₁, h₂⟩ := hzero _ hs hp
        obtain ⟨h₃, h₄⟩ := hzero _ hs' hp
        rw [h₁, h₂, h₃, h₄]
    exact Prod.ext (funext (fun p => congrArg Prod.fst (hpt p)))
      (funext (fun p => congrArg Prod.snd (hpt p)))
  have hcard := Fintype.card_le_of_injective _ hinj
  rw [Fintype.card_fun, Fintype.card_coe, Fintype.card_coe] at hcard
  exact_mod_cast hcard

private lemma primeSubsetValue_injective {T : Finset ℕ} (hp : ∀ p ∈ T, p.Prime) :
    Function.Injective (primeSubsetValue (T := T)) := by
  let e : T ↪ ℕ := ⟨Subtype.val, Subtype.val_injective⟩
  have hprime (s : Finset T) : ∀ p ∈ s.map e, p.Prime := by
    intro p pp
    obtain ⟨p, _, rfl⟩ := Finset.mem_map.mp pp
    exact hp p p.2
  have he (s : Finset T) : (primeSubsetValue s).primeFactors = s.map e := by
    rw [show primeSubsetValue s = ∏ p ∈ s.map e, p by rw [Finset.prod_map]; rfl,
      Nat.primeFactors_prod (hprime s)]
  intro s t h
  apply Finset.map_injective e
  rw [← he, ← he, h]

private lemma totient_moment_subsets_le {W : ℕ} {T : Finset ℕ}
    (hW : 0 < W) (hp : ∀ p ∈ T, p.Prime) (hndvd : ∀ p ∈ T, ¬ p ∣ W)
    (K : ℕ) (Z : Finset (Finset T)) :
    (∑ s ∈ Z, ((K : ℝ) ^ s.card) ^ 2 / ((W * primeSubsetValue s).totient : ℝ)) ≤
      (1 / (W.totient : ℝ)) * (∏ p : T, (1 + localPrimeWeight p)) ^ (K ^ 2) := by
  let w : T → ℝ := fun p => localPrimeWeight p
  let z : T → ℝ := fun p => (K : ℝ) ^ 2 * w p
  have hφ : (0 : ℝ) < W.totient := Nat.cast_pos.mpr (Nat.totient_pos.mpr hW)
  have hw : ∀ p : T, 0 ≤ w p := fun p => localPrimeWeight_nonneg (hp p p.2)
  have he (s : Finset T) : ((K : ℝ) ^ s.card) ^ 2 / ((W * primeSubsetValue s).totient : ℝ) =
      (1 / (W.totient : ℝ)) * ∏ p ∈ s, z p := by
    rw [totient_selectorModulus hp hndvd, Nat.cast_mul, Nat.cast_prod]
    have hprod : (∏ p ∈ s, (((p : ℕ) - 1 : ℕ) : ℝ)) = (∏ p ∈ s, (((p : ℕ) : ℝ) - 1)) := by
      refine Finset.prod_congr (rfl : s = s) (fun (p : T) _ => ?_)
      rw [Nat.cast_sub (hp p p.2).one_le, Nat.cast_one]
    rw [hprod]
    unfold z w localPrimeWeight
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_inv_distrib,
      ← pow_mul, mul_comm s.card 2, pow_mul, div_eq_mul_inv, mul_inv, one_div]
    ring
  simp_rw [he, ← Finset.mul_sum]
  apply mul_le_mul_of_nonneg_left _ (one_div_nonneg.mpr hφ.le)
  calc
    _ ≤ ∑ s : Finset T, ∏ p ∈ s, z p :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun s _ _ => Finset.prod_nonneg (fun p _ => mul_nonneg (sq_nonneg _) (hw p)))
    _ = ∏ p : T, (1 + z p) := by
      simpa only [Finset.powerset_univ] using (Finset.prod_one_add (f := z) Finset.univ).symm
    _ ≤ _ := by
      rw [← Finset.prod_pow]
      refine Finset.prod_le_prod (fun p _ => add_nonneg zero_le_one (mul_nonneg (sq_nonneg _) (hw p))) (fun p _ => ?_)
      have h := one_add_mul_le_pow (a := w p) (show -2 ≤ w p by linarith [hw p]) (K ^ 2)
      simpa [z, Nat.cast_pow] using h

private lemma weighted_progression_sq_of_injection {α : Type*} (S : Finset α)
    (q : α → ℕ) (hq : Set.InjOn q S) (w : α → ℝ) {x : ℝ} (hx : 2 ≤ x) {Q : ℕ}
    (hQ : (Q : ℝ) ≤ x) (hmap : ∀ s ∈ S, q s ∈ Finset.Icc 1 Q) :
    (∑ s ∈ S, w s * worstProgressionError x (q s)) ^ 2 ≤
      (∑ q ∈ Finset.Icc 1 Q, worstProgressionError x q) * ((2 * Real.log x + 1) * x) *
      ∑ s ∈ S, (w s) ^ 2 / ((q s).totient : ℝ) := by
  classical
  let E := worstProgressionError x
  have hE : ∀ j, 0 ≤ E j := worstProgressionError_nonneg x
  have hs : ∑ s ∈ S, E (q s) ≤ ∑ j ∈ Finset.Icc 1 Q, E j := by
    rw [← Finset.sum_image hq]
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (fun j hj => by obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hj; exact hmap s hs)
      (fun j _ _ => hE j)
  have hg : ∑ s ∈ S, (w s) ^ 2 * E (q s) ≤
      ((2 * Real.log x + 1) * x) * ∑ s ∈ S, (w s) ^ 2 / ((q s).totient : ℝ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun s hs => ?_)
    obtain ⟨hl, hu⟩ := Finset.mem_Icc.mp (hmap s hs)
    have h := worstProgressionError_crude hx hl ((Nat.cast_le.mpr hu).trans hQ)
    exact (mul_le_mul_of_nonneg_left h (sq_nonneg _)).trans_eq (by ring)
  have hlog : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  calc
    _ ≤ (∑ s ∈ S, E (q s)) * ∑ s ∈ S, (w s) ^ 2 * E (q s) := by
      exact Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul S (fun s _ => hE (q s))
        (fun s _ => mul_nonneg (sq_nonneg _) (hE (q s))) (fun s _ => by ring_nf; exact le_rfl)
    _ ≤ _ := by
      rw [mul_assoc]
      exact mul_le_mul hs hg (Finset.sum_nonneg (fun s _ => mul_nonneg (sq_nonneg _) (hE (q s))))
        (Finset.sum_nonneg (fun j _ => hE j))

private lemma weighted_bv_algebra {x z C D l A B : ℝ} {d j : ℕ}
    (hx : 0 ≤ x) (hl : 1 ≤ l) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (ha : A ≤ C * x / l ^ (d + 2 * j + 1)) (hb : B ≤ D * l ^ d)
    (hz : z ^ 2 ≤ A * ((2 * l + 1) * x) * B) :
    z ≤ Real.sqrt (3 * C * D) * (x / l ^ j) := by
  have hl₀ : 0 < l := by linarith
  have hcl : 0 ≤ C * x / l ^ (d + 2 * j + 1) := div_nonneg (mul_nonneg hC hx) (by positivity)
  have hdl : 0 ≤ D * l ^ d := mul_nonneg hD (pow_nonneg hl₀.le _)
  have hm : (2 * l + 1) * x ≤ 3 * l * x := mul_le_mul_of_nonneg_right (by linarith) hx
  have hbound : z ^ 2 ≤ (C * x / l ^ (d + 2 * j + 1)) * (3 * l * x) * (D * l ^ d) := by
    apply hz.trans
    exact mul_le_mul (mul_le_mul ha hm (by positivity) hcl) hb hB
      (mul_nonneg hcl (by positivity))
  have he : (C * x / l ^ (d + 2 * j + 1)) * (3 * l * x) * (D * l ^ d) =
      (3 * C * D) * (x / l ^ j) ^ 2 := by
    have hlp : l ^ (2 * j) = (l ^ j) ^ 2 := by rw [← pow_mul, Nat.mul_comm]
    rw [pow_add, pow_add, hlp, pow_one, div_pow]
    field_simp
  rw [he] at hbound
  have hnn : 0 ≤ 3 * C * D := by positivity
  have hright : 0 ≤ Real.sqrt (3 * C * D) * (x / l ^ j) := by positivity
  apply le_of_abs_le
  rw [← abs_of_nonneg hright, ← sq_le_sq]
  rw [mul_pow, Real.sq_sqrt hnn]
  exact hbound

private lemma weighted_progression_from_bv (hbv : HasBombieriVinogradov) (d j : ℕ) :
    ∃ B C : ℝ, 0 ≤ C ∧ ∀ {α : Type} (S : Finset α) (q : α → ℕ) (w : α → ℝ)
      {t D : ℝ} {Q : ℕ}, 2 ≤ t → 1 ≤ Real.log t → (Q : ℝ) ≤ t →
      Q ≤ ⌊Real.sqrt t / Real.log t ^ B⌋₊ →
      Set.InjOn q S → (∀ s ∈ S, q s ∈ Finset.Icc 1 Q) → 0 ≤ D →
      (∑ s ∈ S, (w s) ^ 2 / ((q s).totient : ℝ)) ≤ D * (Real.log t) ^ d →
      ∑ s ∈ S, w s * worstProgressionError t (q s) ≤
        Real.sqrt (3 * C * D) * (t / (Real.log t) ^ j) := by
  have hA : (0 : ℝ) < ((d + 2 * j + 1 : ℕ) : ℝ) := by positivity
  obtain ⟨B, C, h⟩ := sum_worstProgressionError (hbv := hbv) hA
  refine ⟨B, max C 0, le_max_right _ _, ?_⟩
  intro α S q w t D Q ht hlog hQt hQ hinj hmap hD htot
  have ha := h t ht Q hQ
  rw [Real.rpow_natCast] at ha
  have ham : ∑ q ∈ Finset.Icc 1 Q, worstProgressionError _ q ≤
      max C 0 * t / (Real.log t) ^ (d + 2 * j + 1) := ha.trans
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith)) (by positivity))
  exact weighted_bv_algebra (show 0 ≤ t by linarith) hlog (le_max_right _ _) hD
    (Finset.sum_nonneg (fun _ _ => worstProgressionError_nonneg _ _))
    (Finset.sum_nonneg (fun s _ => div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)))
    ham htot (weighted_progression_sq_of_injection S q hinj w ht hQt hmap)

private noncomputable def coefficientBound {α : Type*} [Fintype α] (c : α → ℝ) : ℝ :=
  1 + ∑ a : α, |c a|

private lemma coefficientBound_pos {α : Type*} [Fintype α] (c : α → ℝ) :
    0 < coefficientBound c := by
  unfold coefficientBound
  linarith [Finset.sum_nonneg (s := (Finset.univ : Finset α)) (fun a _ => abs_nonneg (c a))]

private lemma abs_coeff_le_bound {α : Type*} [Fintype α] (c : α → ℝ) (a : α) :
    |c a| ≤ coefficientBound c :=
  (Finset.single_le_sum (fun a _ => abs_nonneg (c a)) (Finset.mem_univ a)).trans
    (by unfold coefficientBound; linarith)

private noncomputable def sieveEulerProduct (W : ℕ) (R : ℝ) : ℝ :=
  ∏ p ∈ siftedPrimes W R, (1 + localPrimeWeight p)

private lemma sieveEulerProduct_ge_one (W : ℕ) (R : ℝ) : 1 ≤ sieveEulerProduct W R :=
  Finset.one_le_prod (fun p hp => by linarith [localPrimeWeight_nonneg (siftedPrimes_prime hp)])

private lemma sieveEulerProduct_subtype (W : ℕ) (R : ℝ) :
    (∏ p : siftedPrimes W R, (1 + localPrimeWeight p)) = sieveEulerProduct W R :=
  (Finset.prod_subtype (siftedPrimes W R) (fun _ => Iff.rfl) (fun p => 1 + localPrimeWeight p)).symm

private lemma exists_sieveEulerProduct_log_bound {W : ℕ} (hW : 0 < W) :
    ∃ A : ℝ, 0 < A ∧ ∀ R : ℝ, 2 ≤ R → sieveEulerProduct W R ≤ A * Real.log R := by
  obtain ⟨C, hC⟩ := sifted_euler_product_le hW
  let ρ := (W.totient : ℝ) / W
  have hρ : 0 ≤ ρ := by positivity
  let A := 8 * ρ + max C 0 / Real.log 2 + 1
  have hl₂ : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨A, by dsimp [A]; positivity, fun R hR => ?_⟩
  have hl : 0 ≤ Real.log R := Real.log_nonneg (by linarith)
  have hc : max C 0 ≤ max C 0 / Real.log 2 * Real.log R := by
    calc
      _ = max C 0 / Real.log 2 * Real.log 2 := (div_mul_cancel₀ _ hl₂.ne').symm
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.log_le_log (by norm_num) hR)
        (div_nonneg (le_max_right _ _) hl₂.le)
  have hh : sieveEulerProduct W R ≤ 8 * ρ * Real.log R + C := hC R hR
  dsimp [A]
  linarith [le_max_left C 0]

private lemma eventual_sieveEulerProduct_le_scale {W L : ℕ} (hW : 0 < W) (hL : 0 < L) :
    ∀ᶠ R : ℝ in atTop, sieveEulerProduct W R ≤ (9 * (L : ℝ)) * boxScale W L R := by
  obtain ⟨C, hC⟩ := sifted_euler_product_le hW
  have hg := (tendsto_boxScale_atTop (L := 1) hW Nat.one_pos).eventually_ge_atTop C
  filter_upwards [eventually_ge_atTop (2 : ℝ), hg] with R hR hc
  have hmain : sieveEulerProduct W R ≤ 8 * ((W.totient : ℝ) / W) * Real.log R + C := hC R hR
  simp only [boxScale, Nat.cast_one, div_one] at hc
  have hl : (L : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hL.ne'
  have he : 9 * (L : ℝ) * boxScale W L R = 9 * ((W.totient : ℝ) / W) * Real.log R := by
    unfold boxScale
    calc
      _ = 9 * ((((W.totient : ℝ) / W) * Real.log R / L) * L) := by ring
      _ = _ := by rw [div_mul_cancel₀ _ hl]; ring
  rw [he]
  linarith only [hc, hmain]

private lemma normalized_error_bound {a b A U K C ε : ℝ} {n : ℕ}
    (hU : 0 < U) (hA : 0 ≤ A) (hK : 0 ≤ K) (hC : 0 ≤ C) (hε : 0 ≤ ε)
    (h : |a - b| ≤ C * A ^ n * ε) (hAK : A ≤ K * U) :
    |a / U ^ n - b / U ^ n| ≤ C * K ^ n * ε := by
  rw [← sub_div, abs_div, abs_of_pos (pow_pos hU _), div_le_iff₀ (pow_pos hU _)]
  calc
    _ ≤ C * A ^ n * ε := h
    _ ≤ C * (K * U) ^ n * ε :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hA hAK _) hC) hε
    _ = _ := by rw [mul_pow]; ring

private lemma exists_sieve_model_approximation {ι : Type*} [Fintype ι] [DecidableEq ι]
    {L : ℕ} (hL : 0 < L) (c : (ι → Fin L) → ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ D : ℕ, 2 ≤ D ∧ ∀ W : ℕ, 0 < W → (∀ p ≤ D, p.Prime → p ∣ W) →
      ∀ᶠ R : ℝ in atTop, ∀ m : Option ι,
        |sieveModelMoment W R (boxArrayWeight R c) m / boxScale W L R ^ sieveDegree m -
          boxMomentPolynomial c m (fun _ => 1)| ≤ ε := by
  classical
  let C := coefficientBound c
  let K : ℝ := 8 * Fintype.card (Finset ι × Finset ι)
  let B : ℝ := C ^ 2 * (9 * (L : ℝ)) ^ (Fintype.card ι + 1)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have ht : Tendsto (fun D : ℕ => K / (D : ℝ)) atTop (𝓝 0) :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).const_div_atTop K
  have ht' : Tendsto (fun D : ℕ => B * (Real.exp (K / (D : ℝ)) - 1)) atTop (𝓝 0) := by
    have he := Real.tendsto_exp_nhds_zero_nhds_one.comp ht
    simpa only [Function.comp_def, sub_self, mul_zero] using (he.sub (tendsto_const_nhds (x := (1 : ℝ)))).const_mul B
  obtain ⟨D, hD, hsmall⟩ := ((eventually_ge_atTop (2 : ℕ)).and
    (ht'.eventually (eventually_lt_nhds (show (0 : ℝ) < ε / 2 by linarith)))).exists
  refine ⟨D, hD, fun W hW hWD => ?_⟩
  apply eventually_all.mpr
  intro m
  let n := sieveDegree m
  let U := boxScale W L
  let Tail := Real.exp (K / (D : ℝ)) - 1
  have hTail : 0 ≤ Tail := sub_nonneg.mpr (Real.one_le_exp_iff.mpr (by dsimp [K]; positivity))
  have hK : (1 : ℝ) ≤ 9 * (L : ℝ) := by
    have hh : (1 : ℝ) ≤ L := by exact_mod_cast hL
    linarith
  have hn : n ≤ Fintype.card ι + 1 := by cases m <;> simp [n, sieveDegree]
  have hlim := tendsto_normalized_boxMoment hW c m
  have herr : ∀ᶠ R : ℝ in atTop,
      |boxMomentPolynomial c m (fun j => boxMass W R j / U R) -
        boxMomentPolynomial c m (fun _ => 1)| < ε / 2 := by
    simpa only [Real.dist_eq] using Metric.tendsto_nhds.mp hlim _ (show (0 : ℝ) < ε / 2 by linarith)
  filter_upwards [eventually_gt_atTop (1 : ℝ), eventual_sieveEulerProduct_le_scale hW hL, herr]
    with R hR hA hlimR
  have hU : 0 < U R := boxScale_pos hW hL hR
  have hUn : 0 < U R ^ n := pow_pos hU _
  have hC : 0 ≤ C := (coefficientBound_pos c).le
  let T := siftedPrimes W R
  let v : (T → Finset ι × Finset ι) → ℝ := fun z =>
    boxArrayWeight R c (fun p => (z p).1) * boxArrayWeight R c (fun p => (z p).2)
  have hv : ∀ z, |v z| ≤ C ^ 2 := by
    intro z
    dsimp only [v]
    rw [abs_mul, pow_two]
    exact mul_le_mul
      (abs_tupleBoxWeight_le hR.le c hC (abs_coeff_le_bound c) _)
      (abs_tupleBoxWeight_le hR.le c hC (abs_coeff_le_bound c) _) (abs_nonneg _) hC
  have h := global_sieve_kernel_difference hD hWD R m v (sq_nonneg C) hv
  have hd : (∑ z : T → Finset ι × Finset ι, v z *
      ∏ p : T, sieveDiagonal (localPrimeWeight p) m (z p)) = boxMomentPolynomial c m (boxMass W R) :=
    diagonal_eq_boxMomentPolynomial hR.le c m
  rw [hd] at h
  have hlhs : |sieveModelMoment W R (boxArrayWeight R c) m -
      boxMomentPolynomial c m (boxMass W R)| ≤ C ^ 2 * sieveEulerProduct W R ^ n * Tail := h
  have hpoly : boxMomentPolynomial c m (fun j => boxMass W R j / U R) =
      boxMomentPolynomial c m (boxMass W R) / U R ^ n := by
    have he : boxMass W R = fun j : Fin L => U R * (boxMass W R j / U R) := by
      funext j
      rw [mul_div_left_comm, div_self hU.ne', mul_one]
    have hm := boxMomentPolynomial_scale c m (U R) (fun j => boxMass W R j / U R)
    rw [← he] at hm
    exact (eq_div_iff hUn.ne').mpr (by rw [mul_comm]; exact hm.symm)
  have hnorm := normalized_error_bound hU (le_trans zero_le_one (sieveEulerProduct_ge_one W R))
    (zero_le_one.trans hK) (sq_nonneg C) hTail hlhs hA
  rw [← hpoly] at hnorm
  have hnorm' : _ ≤ B * Tail := hnorm.trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hK hn) (sq_nonneg C)) hTail)
  have htri := abs_sub_le
    (sieveModelMoment W R (boxArrayWeight R c) m / U R ^ n)
    (boxMomentPolynomial c m (fun j => boxMass W R j / U R))
    (boxMomentPolynomial c m (fun _ => 1))
  exact htri.trans (by linarith only [hnorm', hlimR, hsmall])

private noncomputable def sieveRadius (X : ℝ) : ℝ := X ^ (1 / 8 : ℝ)

private lemma tendsto_sieveRadius : Tendsto sieveRadius atTop atTop :=
  tendsto_rpow_atTop (by norm_num)

private lemma sieveRadius_sq {X : ℝ} (hX : 0 ≤ X) :
    sieveRadius X ^ (2 : ℕ) = X ^ (1 / 4 : ℝ) := by
  unfold sieveRadius
  rw [← Real.rpow_natCast, ← Real.rpow_mul hX]
  norm_num

private lemma eventually_sieveRadius_geometry :
    ∀ᶠ X : ℝ in atTop, 2 ≤ sieveRadius X ∧ sieveRadius X ≤ X / 2 := by
  have hlarge := (tendsto_rpow_atTop (y := 7 / 8) (by norm_num)).eventually_ge_atTop 2
  filter_upwards [tendsto_sieveRadius.eventually_ge_atTop 2, hlarge, eventually_ge_atTop (0 : ℝ)]
    with X hX hpow hX₀
  refine ⟨hX, (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr ?_⟩
  calc
    sieveRadius X * 2 ≤ X ^ (1 / 8 : ℝ) * X ^ (7 / 8 : ℝ) :=
      mul_le_mul_of_nonneg_left hpow (by exact zero_le_two.trans hX)
    _ = X := by rw [← Real.rpow_add_of_nonneg hX₀ (by norm_num) (by norm_num)]; norm_num

private lemma eventually_log_power_le_rpow (a : ℝ) {b c : ℝ} (hb : 0 < b) (hc : 0 < c) :
    ∀ᶠ t : ℝ in atTop, Real.log t ^ a ≤ c * t ^ b := by
  have ht := (isLittleO_log_rpow_rpow_atTop a hb).bound hc
  filter_upwards [ht, eventually_ge_atTop (1 : ℝ)] with t h ht₁
  have hn : 0 ≤ Real.log t := Real.log_nonneg ht₁
  simpa only [Real.norm_of_nonneg (Real.rpow_nonneg hn _),
    Real.norm_of_nonneg (Real.rpow_nonneg (zero_le_one.trans ht₁) _)] using h

private lemma eventually_rpow_quarter_bv_range {A B : ℝ} (hA : 0 < A) :
    ∀ᶠ t : ℝ in atTop,
      A * t ^ (1 / 4 : ℝ) ≤ t ∧ A * t ^ (1 / 4 : ℝ) ≤ Real.sqrt t / Real.log t ^ B := by
  have h₁ := (tendsto_rpow_atTop (y := 3 / 4) (by norm_num)).eventually_ge_atTop A
  have h₂ := eventually_log_power_le_rpow B (b := 1 / 4) (by norm_num) (inv_pos.mpr hA)
  filter_upwards [h₁, h₂, eventually_gt_atTop (1 : ℝ)] with t ht₁ ht₂ ht
  have ht₀ : 0 < t := by linarith
  have hpow : 0 ≤ t ^ (1 / 4 : ℝ) := Real.rpow_nonneg ht₀.le _
  constructor
  · calc
      A * t ^ (1 / 4 : ℝ) ≤ t ^ (3 / 4 : ℝ) * t ^ (1 / 4 : ℝ) :=
        mul_le_mul_of_nonneg_right ht₁ hpow
      _ = t := by rw [← Real.rpow_add ht₀]; norm_num
  · rw [le_div_iff₀ (Real.rpow_pos_of_pos (Real.log_pos ht) _), Real.sqrt_eq_rpow]
    calc
      A * t ^ (1 / 4 : ℝ) * Real.log t ^ B ≤
          A * t ^ (1 / 4 : ℝ) * (A⁻¹ * t ^ (1 / 4 : ℝ)) :=
        mul_le_mul_of_nonneg_left ht₂ (mul_nonneg hA.le hpow)
      _ = t ^ (1 / 4 : ℝ) * t ^ (1 / 4 : ℝ) := by
        rw [mul_mul_mul_comm, mul_inv_cancel₀ hA.ne', one_mul]
      _ = t ^ (1 / 2 : ℝ) := by rw [← Real.rpow_add ht₀]; norm_num

private lemma quarter_growth_of_endpoint {X t : ℝ} (hX : 0 ≤ X) (ht : X / 2 ≤ t) :
    sieveRadius X ^ (2 : ℕ) ≤ 2 * t ^ (1 / 4 : ℝ) := by
  have ht' : 0 ≤ t := by linarith
  rw [sieveRadius_sq hX]
  calc
    X ^ (1 / 4 : ℝ) ≤ (2 * t) ^ (1 / 4 : ℝ) :=
      Real.rpow_le_rpow hX (by linarith) (by norm_num)
    _ = (2 : ℝ) ^ (1 / 4 : ℝ) * t ^ (1 / 4 : ℝ) := Real.mul_rpow (by norm_num) ht'
    _ ≤ _ := by
      refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg ht' _)
      conv_rhs => rw [← Real.rpow_one (2 : ℝ)]
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)

private lemma tendsto_endpoint {η : ℝ} (hη : 0 < η) (c : ℕ) :
    Tendsto (fun X : ℝ => η * X + (c : ℝ)) atTop atTop :=
  (tendsto_id.const_mul_atTop hη).atTop_add tendsto_const_nhds

private lemma eventual_bv_sieve_cutoff {W : ℕ} (hW : 0 < W) (B : ℝ) {η : ℝ}
    (hη : (1 / 2 : ℝ) ≤ η) (c : ℕ) :
    ∀ᶠ X : ℝ in atTop,
      let t := η * X + (c : ℝ)
      (⌊(W : ℝ) * sieveRadius X ^ (2 : ℕ)⌋₊ : ℝ) ≤ t ∧
      ⌊(W : ℝ) * sieveRadius X ^ (2 : ℕ)⌋₊ ≤ ⌊Real.sqrt t / Real.log t ^ B⌋₊ := by
  have hη' : 0 < η := by linarith
  have hW' : (0 : ℝ) < W := Nat.cast_pos.mpr hW
  have h := (tendsto_endpoint hη' c).eventually
    (eventually_rpow_quarter_bv_range (B := B) (show 0 < 2 * (W : ℝ) by positivity))
  filter_upwards [h, eventually_ge_atTop (0 : ℝ)] with X hQ hX
  let t := η * X + (c : ℝ)
  have ht : X / 2 ≤ t := by
    dsimp [t]
    nlinarith [mul_nonneg (sub_nonneg.mpr hη) hX, Nat.cast_nonneg (α := ℝ) c]
  have hbound : (W : ℝ) * sieveRadius X ^ (2 : ℕ) ≤ (2 * (W : ℝ)) * t ^ (1 / 4 : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_left (quarter_growth_of_endpoint hX ht) hW'.le
    simpa only [← mul_assoc, mul_comm (W : ℝ) 2] using hmul
  have hf : (⌊(W : ℝ) * sieveRadius X ^ (2 : ℕ)⌋₊ : ℝ) ≤ (W : ℝ) * sieveRadius X ^ (2 : ℕ) :=
    Nat.floor_le (by positivity)
  exact ⟨hf.trans (hbound.trans hQ.1), Nat.le_floor (hf.trans (hbound.trans hQ.2))⟩

private noncomputable def sieveWeightAt {ι : Type*} [Fintype ι] [DecidableEq ι] {L : ℕ}
    (W : ℕ) (R : ℝ) (c : (ι → Fin L) → ℝ) (h : ι → ℕ) : ℕ → ℝ :=
  sieveObservedWeight h (expandedSieveWeight (fun p : siftedPrimes W R => (p : ℕ)) (boxArrayWeight R c))

private noncomputable def sieveInterval (W ν : ℕ) (X : ℝ) : Finset ℕ :=
  (Finset.Ioc ⌊X / 2⌋₊ ⌊X⌋₊).filter (fun n => n ≡ ν [MOD W])

private noncomputable def observedMomentAt {ι : Type*} [Fintype ι] [DecidableEq ι] {L : ℕ}
    (W ν : ℕ) (X : ℝ) (c : (ι → Fin L) → ℝ) (h : ι → ℕ) (m : Option ι) : ℝ :=
  ∑ n ∈ sieveInterval W ν X, sieveWeightAt W (sieveRadius X) c h n ^ 2 * sieveObservable h m n

private lemma apply_observed_error {ι : Type*} [Fintype ι] [DecidableEq ι] {L W ν : ℕ}
    (hW : 0 < W) (h : ι → ℕ) (hcop : ∀ i, (ν + h i).Coprime W) {X : ℝ}
    (hX : 0 ≤ X) (hR : 1 ≤ sieveRadius X) (hRX : sieveRadius X ≤ X / 2)
    (hsep : ∀ p, p.Prime → ¬ p ∣ W → Function.Injective (fun i => h i % p))
    (c : (ι → Fin L) → ℝ) (m : Option ι) :
    let R := sieveRadius X;
    let T := siftedPrimes W R;
    let coeff := expandedSieveWeight (fun p : T => (p : ℕ)) (boxArrayWeight R c);
    let S : Finset (T → Finset ι) := Finset.univ.filter (fun d => coeff d ≠ 0);
    |observedMomentAt W ν X c h m -
        ((X / 2) / m.elim (W : ℝ) (fun _ => (W.totient : ℝ))) *
        sieveModelMoment W R (boxArrayWeight R c) m| ≤
      (coefficientBound c * sieveEulerProduct W R ^ Fintype.card ι) ^ 2 *
        (∑ de ∈ S ×ˢ S, sieveTermError h m (X / 2) X (selectorModulus W (fun p => de.1 p ∪ de.2 p))) := by
  classical
  dsimp only
  let R := sieveRadius X
  let T := siftedPrimes W R
  let C := coefficientBound c
  let A := sieveEulerProduct W R
  have hC := (coefficientBound_pos c).le
  have hA := (sieveEulerProduct_ge_one W R).trans' zero_le_one
  have ha : ∀ d, |expandedSieveWeight (fun p : T => (p : ℕ)) (boxArrayWeight R c) d| ≤ C * A ^ Fintype.card ι := by
    intro d
    change _ ≤ C * sieveEulerProduct W R ^ Fintype.card ι
    rw [← sieveEulerProduct_subtype W R]
    exact expandedSieveWeight_abs_le (fun p hp => (siftedPrimes_prime hp).two_le)
      (boxArrayWeight R c) hC (fun a => abs_tupleBoxWeight_le hR c hC (abs_coeff_le_bound c) _) d
  have he := sieve_observed_difference_le hW h hcop (show 0 ≤ X / 2 by linarith)
    (show X / 2 ≤ X by linarith) hRX
    (fun p hp => hsep p (siftedPrimes_prime hp) (siftedPrimes_not_dvd hp))
    (boxArrayWeight R c) m (mul_nonneg hC (pow_nonneg hA _)) ha
  dsimp only at he
  rw [show X - X / 2 = X / 2 by ring] at he
  exact he

private lemma eventually_observed_none_error {ι : Type*} [Fintype ι] [DecidableEq ι] {W ν L : ℕ}
    (hW : 0 < W) (hL : 0 < L) (h : ι → ℕ) (hcop : ∀ i, (ν + h i).Coprime W)
    (hsep : ∀ p, p.Prime → ¬ p ∣ W → Function.Injective (fun i => h i % p))
    (c : (ι → Fin L) → ℝ) (hc : ∀ a, L < ∑ i, ((a i).val + 1) → c a = 0) :
    ∀ᶠ X : ℝ in atTop,
      |observedMomentAt W ν X c h none -
        (X / 2 / (W : ℝ)) *
        sieveModelMoment W (sieveRadius X) (boxArrayWeight (sieveRadius X) c) none| ≤ X := by
  classical
  obtain ⟨A₀, hA₀, hA⟩ := exists_sieveEulerProduct_log_bound hW
  let k := Fintype.card ι
  let C := coefficientBound c
  let K := 2 * C ^ 2 * A₀ ^ (4 * k)
  have hK : 0 < K := by
    have hC : 0 < C := coefficientBound_pos c
    dsimp [K]
    positivity
  have hlog := eventually_log_power_le_rpow (↑(4 * k : ℕ)) (b := 1 / 2) (by norm_num) (inv_pos.mpr hK)
  filter_upwards [eventually_sieveRadius_geometry, eventually_ge_atTop (1 : ℝ), hlog] with X hgeom hX hlogX
  let R := sieveRadius X
  let A := sieveEulerProduct W R
  let T := siftedPrimes W R
  let coeff := expandedSieveWeight (fun p : T => (p : ℕ)) (boxArrayWeight R c)
  let S : Finset (T → Finset ι) := Finset.univ.filter (fun d => coeff d ≠ 0)
  have hR1 : 1 ≤ R := one_le_two.trans hgeom.1
  have hR0 : 0 ≤ R := zero_le_one.trans hR1
  have hA' : 0 ≤ A := zero_le_one.trans (sieveEulerProduct_ge_one W R)
  have hp : ∀ p ∈ T, Nat.Prime p := fun p hp => siftedPrimes_prime hp
  have hcount := count_supported_selectors (T := T) (fun p hp' => (hp p hp').two_le) hR0 S
    (fun d hd => expandedSieveWeight_support (fun p hp' => (hp p hp').pos)
      (boxArrayWeight R c) R (fun _ hr => boxArrayWeight_support (fun p hp' => (hp p hp').pos)
        hL hR1 c hc hr) (Finset.mem_filter.mp hd).2)
  rw [sieveEulerProduct_subtype] at hcount
  have herror := apply_observed_error hW h hcop (zero_le_one.trans hX) hR1 hgeom.2 hsep c none
  dsimp only at herror
  have hsum : (∑ de ∈ S ×ˢ S, sieveTermError h none (X / 2) X
      (selectorModulus W (fun p => de.1 p ∪ de.2 p))) = 2 * (S.card : ℝ) ^ 2 := by
    simp only [sieveTermError, Option.elim_none, Finset.sum_const, nsmul_eq_mul,
      Finset.card_product, Nat.cast_mul]
    ring
  have h₁ := herror.trans (show (C * A ^ k) ^ 2 *
      (∑ de ∈ S ×ˢ S, sieveTermError h none (X / 2) X
        (selectorModulus W (fun p => de.1 p ∪ de.2 p))) ≤
      2 * C ^ 2 * R ^ 2 * A ^ (4 * k) by
      rw [hsum]
      calc
        _ ≤ (C * A ^ k) ^ 2 * (2 * (R * A ^ k) ^ 2) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (Nat.cast_nonneg _) hcount 2) (by norm_num)) (sq_nonneg _)
        _ = _ := by rw [pow_mul]; ring)
  have hlogR : Real.log R ≤ Real.log X := Real.log_le_log (by linarith) (by linarith only [hgeom.2, hX])
  have hAx : A ≤ A₀ * Real.log X := (hA R hgeom.1).trans (mul_le_mul_of_nonneg_left hlogR hA₀.le)
  rw [Real.rpow_natCast] at hlogX
  apply h₁.trans
  calc
    _ ≤ 2 * C ^ 2 * R ^ 2 * (A₀ * Real.log X) ^ (4 * k) :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hA' hAx _) (by positivity)
    _ = K * (R ^ 2 * Real.log X ^ (4 * k)) := by unfold K; rw [mul_pow]; ring
    _ ≤ K * (R ^ 2 * (K⁻¹ * X ^ (1 / 2 : ℝ))) := by
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlogX (sq_nonneg _)) hK.le
    _ = X ^ (3 / 4 : ℝ) := by
      rw [show R ^ 2 = X ^ (1 / 4 : ℝ) from sieveRadius_sq (by linarith)]
      calc
        _ = (K * K⁻¹) * (X ^ (1 / 4 : ℝ) * X ^ (1 / 2 : ℝ)) := by ring
        _ = _ := by rw [mul_inv_cancel₀ hK.ne', one_mul, ← Real.rpow_add (by linarith)]; norm_num
    _ ≤ X := (Real.rpow_le_rpow_of_exponent_le hX (by norm_num : (3 / 4 : ℝ) ≤ 1)).trans_eq (Real.rpow_one _)

private lemma bv_coefficient_cancellation {C A D t l : ℝ} (hl : 0 < l) (k : ℕ) :
    (C * (A * l) ^ k) ^ 2 * (D * (t / l ^ (2 * k + 2))) =
      ((C * A ^ k) ^ 2 * D) * (t / l ^ 2) := by
  have he : l ^ (2 * k) = (l ^ k) ^ 2 := by rw [← pow_mul, Nat.mul_comm]
  rw [mul_pow, pow_add, he]
  field_simp
  ring

private lemma endpoint_error_arithmetic {X t l K : ℝ} (hX : 0 ≤ X) (ht : 0 ≤ t) (htX : t ≤ 2 * X)
    (hl : 1 ≤ l) (hK : 0 ≤ K) (hKl : 4 * K ≤ l) : K * (t / l ^ 2) ≤ X / 2 := by
  have hl₀ : 0 < l := by linarith
  have hl' : l ≤ l ^ 2 := by nlinarith [mul_nonneg hl₀.le (sub_nonneg.mpr hl)]
  rw [← mul_div_assoc, div_le_iff₀ (sq_pos_of_pos hl₀)]
  have h₁ := mul_le_mul_of_nonneg_left htX hK
  have h₂ := mul_le_mul_of_nonneg_right (hKl.trans hl') (show 0 ≤ X / 2 by linarith)
  nlinarith only [h₁, h₂]

private lemma eventually_endpoint_weighted_error {ι : Type*} [Fintype ι] [DecidableEq ι] {W L : ℕ}
    (hW : 0 < W) (hbv : HasBombieriVinogradov) (c : (ι → Fin L) → ℝ)
    {η : ℝ} (hη₀ : (1 / 2 : ℝ) ≤ η) (hη₁ : η ≤ 1) (v : ℕ) :
    ∀ᶠ X : ℝ in atTop,
      let R := sieveRadius X;
      let t := η * X + (v : ℝ);
      (coefficientBound c * sieveEulerProduct W R ^ Fintype.card ι) ^ 2 *
        (∑ s ∈ (Finset.univ : Finset (Finset (siftedPrimes W R))).filter
          (fun s => (primeSubsetValue s : ℝ) ≤ R ^ 2),
          (Fintype.card (Finset ι × Finset ι) : ℝ) ^ s.card *
          worstProgressionError t (W * primeSubsetValue s)) ≤ X / 2 := by
  classical
  let k := Fintype.card ι
  let K := Fintype.card (Finset ι × Finset ι)
  let j := 2 * k + 2
  let d := K ^ 2
  let C := coefficientBound c
  have hC : 0 ≤ C := (coefficientBound_pos c).le
  obtain ⟨A₀, hA₀, hEuler⟩ := exists_sieveEulerProduct_log_bound hW
  obtain ⟨B, Cbv, hCbv, hbound⟩ := weighted_progression_from_bv hbv d j
  let D := (1 / (W.totient : ℝ)) * A₀ ^ d
  have hD : 0 ≤ D := by dsimp [D]; positivity
  let N := Real.sqrt (3 * Cbv * D)
  let Tail := (C * A₀ ^ k) ^ 2 * N
  have hTail : 0 ≤ Tail := by dsimp [Tail, N]; positivity
  have hη : 0 < η := by linarith
  have ht := tendsto_endpoint hη v
  have hlog := Real.tendsto_log_atTop.comp ht
  filter_upwards [eventually_sieveRadius_geometry, eventually_ge_atTop ((v : ℝ) + 1),
    eventual_bv_sieve_cutoff hW B hη₀ v, ht.eventually_ge_atTop 2,
    hlog.eventually_ge_atTop 1, hlog.eventually_ge_atTop (4 * Tail)] with X hgeom hX hcut ht₂ hlog₁ hlogTail
  dsimp only [Function.comp_apply] at ht₂ hlog₁ hlogTail
  dsimp only
  let R := sieveRadius X
  let T := siftedPrimes W R
  let A := sieveEulerProduct W R
  let t : ℝ := η * X + v
  let Z := (Finset.univ : Finset (Finset T)).filter (fun s => (primeSubsetValue s : ℝ) ≤ R ^ 2)
  let Q := ⌊(W : ℝ) * R ^ (2 : ℕ)⌋₊
  let q : Finset T → ℕ := fun s => W * primeSubsetValue s
  let w : Finset T → ℝ := fun s => (K : ℝ) ^ s.card
  have hX₀ : 0 ≤ X := by linarith [Nat.cast_nonneg (α := ℝ) v]
  have ht₀ : 0 ≤ t := by linarith only [ht₂]
  have htX : t ≤ 2 * X := by
    dsimp only [t]
    have hmul := mul_le_mul_of_nonneg_right hη₁ hX₀
    linarith only [hmul, hX]
  have hRt : R ≤ t := hgeom.2.trans (by
    dsimp [t]
    nlinarith [mul_nonneg (sub_nonneg.mpr hη₀) hX₀, Nat.cast_nonneg (α := ℝ) v])
  have hA : 0 ≤ A := zero_le_one.trans (sieveEulerProduct_ge_one W R)
  have hAbound : A ≤ A₀ * Real.log t := (hEuler R hgeom.1).trans
    (mul_le_mul_of_nonneg_left (Real.log_le_log (by linarith only [hgeom.1]) hRt) hA₀.le)
  have hp : ∀ p ∈ T, p.Prime := fun p hp => siftedPrimes_prime hp
  have hnot : ∀ p ∈ T, ¬ p ∣ W := fun p hp => siftedPrimes_not_dvd hp
  have hinj : Function.Injective q := fun s t he =>
    primeSubsetValue_injective hp (Nat.eq_of_mul_eq_mul_left hW he)
  have hmap : ∀ s ∈ Z, q s ∈ Finset.Icc 1 Q := by
    intro s hs
    have hp₀ : 0 < primeSubsetValue s := Finset.prod_pos (fun p _ => (hp p p.2).pos)
    refine Finset.mem_Icc.mpr ⟨Nat.mul_pos hW hp₀, Nat.le_floor ?_⟩
    change (↑(W * primeSubsetValue s) : ℝ) ≤ _
    rw [Nat.cast_mul]
    exact mul_le_mul_of_nonneg_left (Finset.mem_filter.mp hs).2 (Nat.cast_nonneg W)
  have htot := totient_moment_subsets_le hW hp hnot K Z
  rw [sieveEulerProduct_subtype] at htot
  have htotal : ∑ s ∈ Z, (w s) ^ 2 / ((q s).totient : ℝ) ≤ D * Real.log t ^ d :=
    htot.trans (by
      calc
        _ ≤ (1 / (W.totient : ℝ)) * (A₀ * Real.log t) ^ d :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hA hAbound _) (by positivity)
        _ = _ := by dsimp [D]; rw [mul_pow]; ring)
  have hBV : ∑ s ∈ Z, w s * worstProgressionError t (q s) ≤ N * (t / (Real.log t) ^ j) :=
    hbound Z q w ht₂ hlog₁ hcut.1 hcut.2 hinj.injOn hmap hD htotal
  have hE : 0 ≤ ∑ s ∈ Z, w s * worstProgressionError t (q s) :=
    Finset.sum_nonneg (fun s _ => mul_nonneg (pow_nonneg (Nat.cast_nonneg K) _) (worstProgressionError_nonneg _ _))
  have hcoef : (C * A ^ k) ^ 2 ≤ (C * (A₀ * Real.log t) ^ k) ^ 2 :=
    pow_le_pow_left₀ (mul_nonneg hC (pow_nonneg hA _))
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hA hAbound _) hC) 2
  change (C * A ^ k) ^ 2 * (∑ s ∈ Z, w s * worstProgressionError t (q s)) ≤ X / 2
  calc
    _ ≤ (C * (A₀ * Real.log t) ^ k) ^ 2 * (N * (t / (Real.log t) ^ j)) :=
      mul_le_mul hcoef hBV hE (sq_nonneg _)
    _ = Tail * (t / Real.log t ^ 2) := bv_coefficient_cancellation (by linarith) k
    _ ≤ _ := endpoint_error_arithmetic hX₀ ht₀ htX hlog₁ hTail hlogTail

private lemma eventually_observed_some_error {ι : Type*} [Fintype ι] [DecidableEq ι] {W ν L : ℕ}
    (hW : 0 < W) (hL : 0 < L) (hbv : HasBombieriVinogradov)
    (h : ι → ℕ) (hcop : ∀ i, (ν + h i).Coprime W)
    (hsep : ∀ p, p.Prime → ¬ p ∣ W → Function.Injective (fun i => h i % p))
    (c : (ι → Fin L) → ℝ) (hc : ∀ a, L < ∑ i, ((a i).val + 1) → c a = 0) (m : ι) :
    ∀ᶠ X : ℝ in atTop,
      |observedMomentAt W ν X c h (some m) -
        (X / 2 / (W.totient : ℝ)) *
        sieveModelMoment W (sieveRadius X) (boxArrayWeight (sieveRadius X) c) (some m)| ≤ X := by
  classical
  have he₁ := eventually_endpoint_weighted_error hW hbv c (η := 1) (by norm_num) le_rfl (h m)
  have he₂ := eventually_endpoint_weighted_error hW hbv c (η := 1 / 2) le_rfl (by norm_num) (h m)
  filter_upwards [eventually_sieveRadius_geometry, eventually_ge_atTop (0 : ℝ), he₁, he₂]
    with X hgeom hX he₁ he₂
  dsimp only at he₁ he₂
  let R := sieveRadius X
  let T := siftedPrimes W R
  let coeff := expandedSieveWeight (fun p : T => (p : ℕ)) (boxArrayWeight R c)
  let S : Finset (T → Finset ι) := Finset.univ.filter (fun d => coeff d ≠ 0)
  let F := (coefficientBound c * sieveEulerProduct W R ^ Fintype.card ι) ^ 2
  have hR1 : 1 ≤ R := one_le_two.trans hgeom.1
  have hp : ∀ p ∈ T, Nat.Prime p := fun p hp => siftedPrimes_prime hp
  have hs : ∀ d ∈ S, (primeSubsetValue (selectorPrimes d) : ℝ) ≤ R := fun d hd =>
    (expandedSieveWeight_support (fun p hp' => (hp p hp').pos)
      (boxArrayWeight R c) R (fun _ hr => boxArrayWeight_support (fun p hp' => (hp p hp').pos)
        hL hR1 c hc hr) (Finset.mem_filter.mp hd).2).2
  have hs₁ := selector_pair_sum_by_modulus (fun p hp' => (hp p hp').pos) S W hs
    (worstProgressionError (X + h m)) (worstProgressionError_nonneg _)
  have hs₂ := selector_pair_sum_by_modulus (fun p hp' => (hp p hp').pos) S W hs
    (worstProgressionError (X / 2 + h m)) (worstProgressionError_nonneg _)
  have herror := apply_observed_error hW h hcop hX hR1 hgeom.2 hsep c (some m)
  dsimp only at herror
  refine herror.trans ?_
  change F * (∑ de ∈ S ×ˢ S,
    (worstProgressionError (X + h m) (selectorModulus W (fun p => de.1 p ∪ de.2 p)) +
    worstProgressionError (X / 2 + h m) (selectorModulus W (fun p => de.1 p ∪ de.2 p)))) ≤ X
  rw [Finset.sum_add_distrib, mul_add]
  rw [one_mul] at he₁
  rw [show (1 / 2 : ℝ) * X = X / 2 by ring] at he₂
  have hF : 0 ≤ F := sq_nonneg _
  have hb₁ := (mul_le_mul_of_nonneg_left hs₁ hF).trans he₁
  have hb₂ := (mul_le_mul_of_nonneg_left hs₂ hF).trans he₂
  linarith only [hb₁, hb₂]

private noncomputable def sieveMomentScale {ι : Type*} [Fintype ι] (W L : ℕ) (X : ℝ)
    (m : Option ι) : ℝ :=
  (X / 2 / m.elim (W : ℝ) (fun _ => (W.totient : ℝ))) *
    boxScale W L (sieveRadius X) ^ sieveDegree m

private lemma sieveMomentScale_ratio {ι : Type*} [Fintype ι] {W L : ℕ}
    (hW : 0 < W) (hL : 0 < L) {X : ℝ} (hX : 0 < X) (m : ι) :
    sieveMomentScale W L X (some m) =
    sieveMomentScale W L X (none : Option ι) * (Real.log X / (8 * (L : ℝ))) := by
  have hW' : (W : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hW.ne'
  have hφ : (W.totient : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.totient_pos.mpr hW).ne'
  have hL' : (L : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hL.ne'
  simp only [sieveMomentScale, sieveDegree, Option.elim_some, Option.elim_none, Nat.add_zero, pow_succ]
  have he : boxScale W L (sieveRadius X) =
      ((W.totient : ℝ) / W) * (Real.log X / (8 * (L : ℝ))) := by
    unfold boxScale sieveRadius
    rw [Real.log_rpow hX]
    field_simp
  rw [he]
  field_simp

private lemma combine_model_and_observed {e X α U a b c : ℝ} {d : ℕ}
    (hα : 0 ≤ α) (hU : 0 < U) (hX : X ≤ e * (α * U ^ d))
    (hab : |a - α * b| ≤ X) (hbc : |b / U ^ d - c| ≤ e) :
    (c - 2 * e) * (α * U ^ d) ≤ a ∧ a ≤ (c + 2 * e) * (α * U ^ d) := by
  have hU' : 0 < U ^ d := pow_pos hU _
  obtain ⟨hl, hu⟩ := abs_le.mp hbc
  have hlo : (c - e) * U ^ d ≤ b := (le_div_iff₀ hU').mp (by linarith)
  have hhi : b ≤ (c + e) * U ^ d := (div_le_iff₀ hU').mp (by linarith)
  have hlo' := mul_le_mul_of_nonneg_left hlo hα
  have hhi' := mul_le_mul_of_nonneg_left hhi hα
  obtain ⟨hal, hau⟩ := abs_le.mp hab
  constructor <;> nlinarith only [hlo', hhi', hal, hau, hX]

private lemma eventually_sieve_moment_between {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {W ν L : ℕ} (hW : 0 < W) (hL : 0 < L) (hbv : HasBombieriVinogradov)
    (h : ι → ℕ) (hcop : ∀ i, (ν + h i).Coprime W)
    (hsep : ∀ p, p.Prime → ¬ p ∣ W → Function.Injective (fun i => h i % p))
    (c : (ι → Fin L) → ℝ) (hc : ∀ a, L < ∑ i, ((a i).val + 1) → c a = 0) {ε : ℝ} (hε : 0 < ε)
    (hmodel : ∀ᶠ R : ℝ in atTop, ∀ m : Option ι,
      |sieveModelMoment W R (boxArrayWeight R c) m / boxScale W L R ^ sieveDegree m -
        boxMomentPolynomial c m (fun _ => 1)| ≤ ε) :
    ∀ᶠ X : ℝ in atTop, ∀ m : Option ι,
      (boxMomentPolynomial c m (fun _ => 1) - 2 * ε) * sieveMomentScale W L X m
        ≤ observedMomentAt W ν X c h m ∧
      observedMomentAt W ν X c h m
        ≤ (boxMomentPolynomial c m (fun _ => 1) + 2 * ε) * sieveMomentScale W L X m := by
  let U : ℝ → ℝ := fun X => boxScale W L (sieveRadius X)
  have hU := (tendsto_boxScale_atTop hW hL).comp tendsto_sieveRadius
  have hobs : ∀ᶠ X : ℝ in atTop, ∀ m : Option ι,
      |observedMomentAt W ν X c h m -
        (X / 2 / m.elim (W : ℝ) (fun _ => (W.totient : ℝ))) *
          sieveModelMoment W (sieveRadius X) (boxArrayWeight (sieveRadius X) c) m| ≤ X := by
    apply eventually_all.mpr
    intro m
    cases m with
    | none => exact eventually_observed_none_error hW hL h hcop hsep c hc
    | some m => exact eventually_observed_some_error hW hL hbv h hcop hsep c hc m
  filter_upwards [eventually_gt_atTop (0 : ℝ), tendsto_sieveRadius.eventually hmodel,
    hU.eventually_ge_atTop (1 : ℝ), hU.eventually_ge_atTop (2 * (W : ℝ) / ε), hobs]
    with X hX hb hU₁ hU₂ ha
  intro m
  let P := m.elim (W : ℝ) (fun _ => (W.totient : ℝ))
  have hP : 0 < P := by
    cases m
    · exact Nat.cast_pos.mpr hW
    · exact Nat.cast_pos.mpr (Nat.totient_pos.mpr hW)
  have hPW : P ≤ (W : ℝ) := by
    cases m
    · exact le_rfl
    · exact Nat.cast_le.mpr (Nat.totient_le W)
  have hdeg : 1 ≤ sieveDegree m := by
    have hk := Fintype.card_pos_iff.mpr (inferInstance : Nonempty ι)
    unfold sieveDegree
    omega
  have hUpos : 0 < U X := lt_of_lt_of_le zero_lt_one hU₁
  have hpow : U X ≤ U X ^ sieveDegree m :=
    (pow_one (U X)).symm.trans_le (pow_le_pow_right₀ hU₁ hdeg)
  have hεpow : 2 * P ≤ ε * U X ^ sieveDegree m := by
    have h₁ : 2 * (W : ℝ) ≤ U X * ε := (div_le_iff₀ hε).mp hU₂
    have h₂ := mul_le_mul_of_nonneg_right hpow hε.le
    have h₃ := mul_le_mul_of_nonneg_left hPW (by norm_num : (0 : ℝ) ≤ 2)
    linarith only [h₁, h₂, h₃]
  have hα : 0 ≤ X / 2 / P := div_nonneg
    (div_nonneg hX.le (show (0 : ℝ) ≤ 2 by norm_num)) hP.le
  have hXs : X ≤ ε * (X / 2 / P * U X ^ sieveDegree m) := by
    have hh := mul_le_mul_of_nonneg_left hεpow hα
    have he : X / 2 / P * (2 * P) = X := by
      calc
        _ = (X / 2 * 2 / P) * P := by ring
        _ = X / 2 * 2 := div_mul_cancel₀ _ hP.ne'
        _ = X := by ring
    rw [he] at hh
    exact hh.trans_eq (by ring)
  exact combine_model_and_observed hα hUpos hXs (ha m) (hb m)

private lemma maynard_moment_gap_algebra {r I J L s ℓ b c : ℝ}
    (hr : 0 ≤ r) (hI : 0 < I) (hL : 0 < L) (hs : 0 < s) (hℓ : 0 < ℓ)
    (hJ : 128 * (r + 1) * I < J / L) (hb : b ≤ 2 * I * s)
    (hc : (J / 2) * (s * (ℓ / (8 * L))) ≤ c) :
    r * (2 * ℓ) * b < c := by
  have hfac : 0 < s * ℓ := mul_pos hs hℓ
  have hj : 4 * r * I < (J / L) / 16 := by
    nlinarith only [hJ, hI, mul_nonneg hr hI.le]
  have hh := mul_lt_mul_of_pos_right hj hfac
  have he : (J / L) / 16 * (s * ℓ) = (J / 2) * (s * (ℓ / (8 * L))) := by ring
  calc
    _ ≤ (r * (2 * ℓ)) * (2 * I * s) :=
      mul_le_mul_of_nonneg_left hb (mul_nonneg hr (by positivity))
    _ = (4 * r * I) * (s * ℓ) := by ring
    _ < (J / 2) * (s * (ℓ / (8 * L))) := hh.trans_eq he
    _ ≤ _ := hc

private lemma small_error_budget {k : ℕ} {I : ℝ} (hI : 0 < I) :
    ∃ ε : ℝ, 0 < ε ∧ 2 * ε ≤ I ∧ (k : ℝ) * (2 * ε) ≤ I / 2 := by
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  let ε := I / (4 * ((k : ℝ) + 1))
  have hden : (0 : ℝ) < 4 * ((k : ℝ) + 1) := by linarith
  refine ⟨ε, div_pos hI hden, ?_, ?_⟩
  · change 2 * (I / (4 * ((k : ℝ) + 1))) ≤ I
    rw [← mul_div_assoc, div_le_iff₀ hden]
    nlinarith [mul_nonneg hk hI.le]
  · change (k : ℝ) * (2 * (I / (4 * ((k : ℝ) + 1)))) ≤ I / 2
    rw [← mul_div_assoc, ← mul_div_assoc, div_le_iff₀ hden]
    ring_nf
    linarith

private lemma maynard_affine_for_weight {r k L : ℕ} (hk : 0 < k) (hL : 0 < L)
    (c : (Fin k → Fin L) → ℝ)
    (hc : ∀ a, L < ∑ i : Fin k, ((a i).val + 1) → c a = 0)
    (hI : 0 < ∑ a : Fin k → Fin L, (c a) ^ 2)
    (hvar : 128 * ((r : ℝ) + 1) * (∑ a : Fin k → Fin L, (c a) ^ 2) <
      (1 / (L : ℝ)) * ∑ m : Fin k,
        ∑ a ∈ (Finset.univ : Finset (Fin k → Fin L)).filter (fun a => a m = ⟨0, hL⟩),
          (∑ j : Fin L, c (Function.update a m j)) ^ 2)
    (hbv : HasBombieriVinogradov) (h : Fin k → ℕ) (hinj : Function.Injective h)
    {M b : ℕ} (hM : 0 < M)
    (hadm : ∀ p, p.Prime → ∃ x, ∀ i, ¬ p ∣ M * x + b + h i) (N : ℕ) :
    ∃ x, N < x ∧ r ≤ ((Finset.univ : Finset (Fin k)).filter
      (fun i => (M * x + b + h i).Prime)).card := by
  classical
  letI : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  let I := ∑ a : Fin k → Fin L, (c a) ^ 2
  let Jm : Fin k → ℝ := fun m => ∑ a ∈
    (Finset.univ : Finset (Fin k → Fin L)).filter (fun a => a m = ⟨0, hL⟩),
    (∑ j : Fin L, c (Function.update a m j)) ^ 2
  let J := ∑ m : Fin k, Jm m
  have hIJ : 128 * ((r : ℝ) + 1) * I < J / (L : ℝ) := by
    change _ < (1 / (L : ℝ)) * J at hvar
    rwa [one_div_mul_eq_div] at hvar
  have hL' : (0 : ℝ) < L := Nat.cast_pos.mpr hL
  have hI' : 0 < I := hI
  have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hI_J : I ≤ J := by
    have h₁ := (lt_div_iff₀ hL').mp hIJ
    have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hL
    have h₂ : (1 : ℝ) ≤ 128 * ((r : ℝ) + 1) * L := by
      have h₃ := one_le_mul_of_one_le_of_one_le (show (1 : ℝ) ≤ 128 * ((r : ℝ) + 1) by linarith) hL1
      exact h₃
    have hh := mul_le_mul_of_nonneg_right h₂ hI'.le
    nlinarith only [h₁, hh]
  obtain ⟨ε, hε, hεI, hεJ⟩ := small_error_budget (k := k) hI'
  obtain ⟨D, _, hmodel⟩ := exists_sieve_model_approximation hL c hε
  obtain ⟨W, ν, hW, hMW, _, hν, hWD, hcop, hsep⟩ :=
    exists_sifted_affine_progression h hinj hM hadm D
  have he := eventually_sieve_moment_between hW hL hbv h hcop hsep c hc hε (hmodel W hW hWD)
  let B : ℕ := Finset.univ.sup h
  have hB : ∀ i, h i ≤ B := fun i => Finset.le_sup (f := h) (Finset.mem_univ i)
  have hall : ∀ᶠ X : ℝ in atTop,
      (∀ m : Option (Fin k),
        (boxMomentPolynomial c m (fun _ => 1) - 2 * ε) * sieveMomentScale W L X m
          ≤ observedMomentAt W ν X c h m ∧
        observedMomentAt W ν X c h m
          ≤ (boxMomentPolynomial c m (fun _ => 1) + 2 * ε) * sieveMomentScale W L X m) ∧
      2 ≤ sieveRadius X ∧ 2 ≤ X ∧ (B : ℝ) ≤ X ∧ 2 * ((M * N + b : ℕ) : ℝ) ≤ X := by
    filter_upwards [he, eventually_sieveRadius_geometry, eventually_ge_atTop (2 : ℝ),
      eventually_ge_atTop (B : ℝ), eventually_ge_atTop (2 * ((M * N + b : ℕ) : ℝ))]
      with X hmom hR hX hBX hXN
    exact ⟨hmom, hR.1, hX, hBX, hXN⟩
  obtain ⟨X, hmom, hR, hX, hBX, hXN⟩ := hall.exists
  have hX₀ : 0 < X := by linarith
  have hℓ : 0 < Real.log X := Real.log_pos (by linarith)
  let s := sieveMomentScale W L X (none : Option (Fin k))
  have hs : 0 < s := by
    unfold s sieveMomentScale
    simp only [Option.elim_none]
    exact mul_pos (div_pos (div_pos hX₀ (by norm_num)) (Nat.cast_pos.mpr hW))
      (pow_pos (boxScale_pos hW hL (by linarith)) _)
  let v := s * (Real.log X / (8 * (L : ℝ)))
  have hv : 0 ≤ v := mul_nonneg hs.le (div_nonneg hℓ.le (by positivity))
  have hs1 : observedMomentAt W ν X c h none ≤ 2 * I * s := by
    have hh := (hmom (none : Option (Fin k))).2
    rw [boxMomentPolynomial_one_none] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right (by linarith only [hεI]) hs.le)
  have hpoint (m : Fin k) : (Jm m - 2 * ε) * v ≤ observedMomentAt W ν X c h (some m) := by
    have hh := (hmom (some m)).1
    rw [boxMomentPolynomial_one_some c m ⟨0, hL⟩, sieveMomentScale_ratio hW hL hX₀] at hh
    exact hh
  have hs2 : (J / 2) * v ≤ ∑ m : Fin k, observedMomentAt W ν X c h (some m) := by
    have hh := Finset.sum_le_sum (fun m (_ : m ∈ (Finset.univ : Finset (Fin k))) => hpoint m)
    rw [← Finset.sum_mul, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hh
    exact (mul_le_mul_of_nonneg_right
      (show J / 2 ≤ J - (k : ℝ) * (2 * ε) by linarith only [hI_J, hεJ]) hv).trans hh
  have hgap := maynard_moment_gap_algebra hr hI' hL' hs hℓ hIJ hs1 hs2
  let S := sieveInterval W ν X
  let u := sieveWeightAt W (sieveRadius X) c h
  have hnone : observedMomentAt W ν X c h none = ∑ n ∈ S, u n ^ 2 := by
    simp only [observedMomentAt, sieveObservable, Option.elim_none, mul_one, S, u]
  have hsome : (∑ m : Fin k, observedMomentAt W ν X c h (some m)) =
      ∑ n ∈ S, u n ^ 2 * ∑ i : Fin k, primeLog (n + h i) := by
    simp only [observedMomentAt, sieveObservable, Option.elim_some, S, u]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun n _ => (Finset.mul_sum ..).symm)
  rw [hnone, hsome] at hgap
  have hlog : ∀ n ∈ S, ∀ i, (n + h i).Prime → Real.log ((n + h i : ℕ) : ℝ) ≤ 2 * Real.log X := by
    intro n hn i hp
    have hnX : (n : ℝ) ≤ X := (Nat.cast_le.mpr (Finset.mem_Ioc.mp (Finset.mem_filter.mp hn).1).2).trans
      (Nat.floor_le hX₀.le)
    have hiX : (h i : ℝ) ≤ X := (Nat.cast_le.mpr (hB i)).trans hBX
    have hsum : ((n + h i : ℕ) : ℝ) ≤ X ^ (2 : ℕ) := by
      rw [Nat.cast_add]
      nlinarith [mul_nonneg hX₀.le (sub_nonneg.mpr hX)]
    have hh := Real.log_le_log (Nat.cast_pos.mpr hp.pos) hsum
    rw [Real.log_pow] at hh
    exact hh
  obtain ⟨n, hn, hrn⟩ := exists_prime_count_of_moments r S (fun n i => n + h i) u
    (show 0 ≤ 2 * Real.log X by positivity) hlog hgap
  have hmod : n ≡ b [MOD M] := ((Finset.mem_filter.mp hn).2.of_dvd hMW).trans hν
  have hbig : M * N + b < n := by
    have hlt := (Nat.floor_lt (show 0 ≤ X / 2 by positivity)).mp
      (Finset.mem_Ioc.mp (Finset.mem_filter.mp hn).1).1
    exact_mod_cast (show ((M * N + b : ℕ) : ℝ) < n by linarith)
  obtain ⟨x, hx, rfl⟩ := exists_affine_parameter hbig hmod
  exact ⟨x, hx, hrn⟩

end MaynardH2

theorem OMA.solution : OMA.R_Erdos6_erdos_6_variants_decreasing_R1.H2 := by
  classical
  change MaynardH2.HasBombieriVinogradov → _
  intro hbv r
  obtain ⟨k, L, hk, hL, c, _, hc, hI, hvar⟩ :=
    MaynardH2.exists_maynard_weights (128 * ((r : ℝ) + 1))
  refine ⟨k, fun H M b hcard hM hAdmissible N => ?_⟩
  obtain ⟨H', hsub, hcard'⟩ := Finset.exists_subset_card_eq hcard
  let e : Fin k ≃ H' := (H'.equivFinOfCardEq hcard').symm
  let h : Fin k → ℕ := fun i => (e i : ℕ)
  have hinj : Function.Injective h := Subtype.val_injective.comp e.injective
  have hmem : ∀ i, h i ∈ H := fun i => hsub (e i).2
  have hadm : ∀ p, p.Prime → ∃ x, ∀ i, ¬ p ∣ M * x + b + h i := by
    intro p hp
    obtain ⟨x, hx⟩ := hAdmissible p hp
    exact ⟨x, fun i => hx (h i) (hmem i)⟩
  obtain ⟨x, hx, hr⟩ := MaynardH2.maynard_affine_for_weight hk hL c hc hI hvar hbv h hinj hM hadm N
  let I := (Finset.univ : Finset (Fin k)).filter (fun i => (M * x + b + h i).Prime)
  let f : Fin k ↪ ℕ := ⟨h, hinj⟩
  have hmap : I.map f ⊆ H.filter (fun a => (M * x + b + a).Prime) := by
    intro a ha
    obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp ha
    exact Finset.mem_filter.mpr ⟨hmem i, (Finset.mem_filter.mp hi).2⟩
  refine ⟨x, hx, hr.trans ?_⟩
  simpa only [Finset.card_map] using Finset.card_le_card hmap
