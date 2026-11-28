import OMAReductions.R_Erdos968_erdos_968_variants_infinite_increasingTriples_R2

/-!
# Isolated Reduced Residue Class (`Erdos968.R2.H1`)

Elementary Rankin–Westzynthius CRT covering on `q = primorial x` with `r = 2 * K' * x`.
Credit: @yhay81
-/

namespace Erdos968R2H1

open Filter Finset Nat Chebyshev
open scoped BigOperators

/- ### Part 1: Elementary analytic inequalities -/

private lemma log_le_four_mul_rpow_quarter {t : ℝ} (ht : 0 < t) :
    Real.log t ≤ 4 * t ^ (1 / 4 : ℝ) := by
  have h1 : Real.log (t ^ (1 / 4 : ℝ)) ≤ t ^ (1 / 4 : ℝ) - 1 :=
    Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos ht _)
  rw [Real.log_rpow ht] at h1
  linarith

private lemma pow_four_div_24_le_exp {u : ℝ} (hu : 0 ≤ u) :
    u ^ 4 / 24 ≤ Real.exp u := by
  have h := Real.sum_le_exp_of_nonneg hu 5
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial,
    Nat.cast_one, Nat.cast_mul] at h
  have h2 : 0 ≤ u ^ 2 / (2 * 1) := by positivity
  have h3 : 0 ≤ u ^ 3 / (3 * (2 * 1)) := by positivity
  nlinarith

private lemma nat_log2_le_two_mul_log {n : ℕ} (hn : 1 ≤ n) :
    (Nat.log 2 n : ℝ) ≤ 2 * Real.log n := by
  have hpow : (2 : ℝ) ^ (Nat.log 2 n) ≤ (n : ℝ) := by
    exact_mod_cast Nat.pow_log_le_self 2 (by omega)
  have hlog := Real.log_le_log (by positivity) hpow
  rw [Real.log_pow] at hlog
  have h2 : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hnn : (0 : ℝ) ≤ Nat.log 2 n := Nat.cast_nonneg _
  nlinarith

private lemma log_le_nat_log2_add_one {n : ℕ} (hn : 1 ≤ n) :
    Real.log n ≤ (Nat.log 2 n : ℝ) + 1 := by
  have hlt : (n : ℝ) < (2 : ℝ) ^ (Nat.log 2 n + 1) := by
    exact_mod_cast Nat.lt_pow_succ_log_self (by decide : 1 < 2) n
  have hlog := Real.log_le_log (by exact_mod_cast hn) hlt.le
  rw [Real.log_pow] at hlog
  push_cast at hlog
  have h2 : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
  have hnn : (0 : ℝ) ≤ (Nat.log 2 n : ℝ) + 1 := by positivity
  nlinarith

private lemma rpow_quarter_ge_of_ge {x a : ℝ} (ha : 0 ≤ a) (hx : a ^ 4 ≤ x) :
    a ≤ x ^ (1 / 4 : ℝ) := by
  have h1 : (a ^ 4) ^ (1 / 4 : ℝ) ≤ x ^ (1 / 4 : ℝ) :=
    Real.rpow_le_rpow (by positivity) hx (by norm_num)
  rw [← Real.rpow_natCast a 4, ← Real.rpow_mul ha] at h1
  norm_num at h1
  exact h1

private lemma sum_biUnion_le_sum {ι α : Type*} [DecidableEq ι] [DecidableEq α]
    (s : Finset ι) (t : ι → Finset α) (f : α → ℝ) (hf : ∀ a, 0 ≤ f a) :
    ∑ a ∈ s.biUnion t, f a ≤ ∑ i ∈ s, ∑ a ∈ t i, f a := by
  induction s using Finset.induction with
  | empty => simp
  | @insert i s his ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert his]
    have hunion : ∑ a ∈ t i ∪ s.biUnion t, f a ≤
        (∑ a ∈ t i, f a) + ∑ a ∈ s.biUnion t, f a := by
      have h := Finset.sum_union_inter (s₁ := t i) (s₂ := s.biUnion t) (f := f)
      have hinter : 0 ≤ ∑ a ∈ t i ∩ s.biUnion t, f a :=
        Finset.sum_nonneg (fun a _ => hf a)
      linarith
    linarith

/- ### Part 2: Explicit Chebyshev bounds and dyadic sums of 1/p -/

private lemma theta_lower {x : ℕ} (hx : 10 ^ 10 ≤ x) :
    (0.6 : ℝ) * x ≤ theta x := by
  have hxR : (200 : ℝ) ^ 4 ≤ (x : ℝ) := by
    have : (10 ^ 10 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
    linarith
  have hx1 : (1 : ℝ) ≤ x := by linarith
  have hxpos : (0 : ℝ) < x := by linarith
  have hpsi := Chebyshev.psi_ge x
  have hdiff := Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log hx1
  have hsub : psi x - theta x ≤ 2 * Real.sqrt x * Real.log x := (le_abs_self _).trans hdiff
  have hxq : (200 : ℝ) ≤ (x : ℝ) ^ (1 / 4 : ℝ) := rpow_quarter_ge_of_ge (by norm_num) hxR
  have hlogx : Real.log x ≤ 4 * (x : ℝ) ^ (1 / 4 : ℝ) := log_le_four_mul_rpow_quarter hxpos
  have h34 : (x : ℝ) ^ (3 / 4 : ℝ) * (x : ℝ) ^ (1 / 4 : ℝ) = (x : ℝ) := by
    rw [← Real.rpow_add hxpos]; norm_num
  have hsqrt : Real.sqrt x * (x : ℝ) ^ (1 / 4 : ℝ) = (x : ℝ) ^ (3 / 4 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hxpos]; norm_num
  have h34pos : 0 ≤ (x : ℝ) ^ (3 / 4 : ℝ) := Real.rpow_nonneg hxpos.le _
  have hterm1 : 2 * Real.sqrt x * Real.log x ≤ 0.04 * x := by
    have h1 : 2 * Real.sqrt x * Real.log x ≤ 8 * (x : ℝ) ^ (3 / 4 : ℝ) := by
      calc 2 * Real.sqrt x * Real.log x
          ≤ 2 * Real.sqrt x * (4 * (x : ℝ) ^ (1 / 4 : ℝ)) :=
            mul_le_mul_of_nonneg_left hlogx (by positivity)
        _ = 8 * (Real.sqrt x * (x : ℝ) ^ (1 / 4 : ℝ)) := by ring
        _ = 8 * (x : ℝ) ^ (3 / 4 : ℝ) := by rw [hsqrt]
    nlinarith
  have hterm2 : Real.log ((x : ℝ) + 1) ≤ 0.05 * x := by
    have hle : Real.log ((x : ℝ) + 1) ≤ Real.log (2 * (x : ℝ)) :=
      Real.log_le_log (by linarith) (by linarith)
    rw [Real.log_mul (by norm_num) hxpos.ne'] at hle
    have hq_le : (x : ℝ) ^ (1 / 4 : ℝ) ≤ (x : ℝ) ^ (3 / 4 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
    have h2 : Real.log 2 < 1 := by linarith [Real.log_two_lt_d9]
    nlinarith
  have hlog2 : (0.693 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  nlinarith

private lemma theta_sub_eq_sum_filter {a b : ℕ} (hab : a ≤ b) :
    theta b - theta a = ∑ p ∈ (primesLE b).filter (fun p => a < p), Real.log p := by
  rw [theta_eq_sum_primesLE_log, theta_eq_sum_primesLE_log]
  have hsub : primesLE a ⊆ primesLE b := fun p hp => by
    rw [mem_primesLE] at hp ⊢
    exact ⟨hp.1.trans hab, hp.2⟩
  have hsdiff : primesLE b \ primesLE a = (primesLE b).filter (fun p => a < p) := by
    ext p
    simp only [Finset.mem_sdiff, Finset.mem_filter, mem_primesLE]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      refine ⟨⟨h1, h2⟩, ?_⟩
      by_contra hle
      exact h3 ⟨by omega, h2⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨⟨h1, h2⟩, fun h => by omega⟩
  rw [← hsdiff, Finset.sum_sdiff_eq_sub hsub]

private lemma card_P4_ge {x : ℕ} (hx : 10 ^ 10 ≤ x) :
    (0.4 : ℝ) * x / Real.log x ≤ (((primesLE x).filter (fun p => x / 10 < p)).card : ℝ) := by
  have hlogx : 0 < Real.log x := Real.log_pos (by exact_mod_cast (show 1 < x by omega))
  rw [div_le_iff₀ hlogx]
  have hth : (0.6 : ℝ) * x ≤ theta x := theta_lower hx
  have hth10 : theta (x / 10 : ℕ) ≤ 0.2 * x := by
    have h1 := Chebyshev.theta_le_log4_mul_x (show (0 : ℝ) ≤ (x / 10 : ℕ) by positivity)
    have h2 : ((x / 10 : ℕ) : ℝ) ≤ (x : ℝ) / 10 := by
      have : (x / 10) * 10 ≤ x := Nat.div_mul_le_self x 10
      have : ((x / 10 : ℕ) : ℝ) * 10 ≤ (x : ℝ) := by exact_mod_cast this
      linarith
    have hlog4 : Real.log 4 ≤ 2 := by
      have : Real.log 4 = 2 * Real.log 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
      linarith [Real.log_two_lt_d9]
    have hnn : (0 : ℝ) ≤ (x / 10 : ℕ) := Nat.cast_nonneg _
    nlinarith
  have hsum : theta x - theta (x / 10 : ℕ) ≤
      (((primesLE x).filter (fun p => x / 10 < p)).card : ℝ) * Real.log x := by
    rw [theta_sub_eq_sum_filter (Nat.div_le_self x 10)]
    calc ∑ p ∈ (primesLE x).filter (fun p => x / 10 < p), Real.log p
        ≤ ∑ _p ∈ (primesLE x).filter (fun p => x / 10 < p), Real.log x := by
          apply Finset.sum_le_sum
          intro p hp
          have hmem := (Finset.mem_filter.mp hp).1
          exact Real.log_le_log (by exact_mod_cast (prime_of_mem_primesLE hmem).pos)
            (by exact_mod_cast le_of_mem_primesLE hmem)
      _ = (((primesLE x).filter (fun p => x / 10 < p)).card : ℝ) * Real.log x := by
          simp
  linarith

private lemma sum_inv_Icc_le (J : ℕ) (hJ : 1 ≤ J) :
    ∑ j ∈ Finset.Icc 1 J, (1 / (j : ℝ)) ≤ 1 + Real.log J := by
  induction J, hJ using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    have hIcc : Finset.Icc 1 (n + 1) = insert (n + 1) (Finset.Icc 1 n) := by
      ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    rw [hIcc, Finset.sum_insert (by simp)]
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hpos : (0 : ℝ) < (n : ℝ) / ((n : ℝ) + 1) := by positivity
    have hlog := Real.log_le_sub_one_of_pos hpos
    rw [Real.log_div (by linarith) (by linarith)] at hlog
    have hcalc : (n : ℝ) / ((n : ℝ) + 1) - 1 = -(1 / ((n : ℝ) + 1)) := by
      field_simp; ring
    rw [hcalc] at hlog
    push_cast
    linarith

private lemma sum_inv_Ico_ge (m₀ m₁ : ℕ) (h : m₀ ≤ m₁) :
    Real.log ((m₁ + 1 : ℝ) / (m₀ + 1 : ℝ)) ≤ ∑ m ∈ Finset.Ico m₀ m₁, (1 / ((m : ℝ) + 1)) := by
  induction m₁, h using Nat.le_induction with
  | base => simp [div_self (by positivity : (m₀ : ℝ) + 1 ≠ 0)]
  | succ n hn ih =>
    rw [Finset.sum_Ico_succ_top hn]
    have hpos : (0 : ℝ) < ((n : ℝ) + 2) / ((n : ℝ) + 1) := by positivity
    have hlog := Real.log_le_sub_one_of_pos hpos
    rw [Real.log_div (by positivity) (by positivity)] at hlog
    have hcalc : ((n : ℝ) + 2) / ((n : ℝ) + 1) - 1 = 1 / ((n : ℝ) + 1) := by
      field_simp; ring
    rw [hcalc] at hlog
    have hsplit : Real.log (((n + 1 : ℕ) + 1 : ℝ) / (m₀ + 1 : ℝ)) =
        Real.log ((n + 1 : ℝ) / (m₀ + 1 : ℝ)) + (Real.log ((n : ℝ) + 2) - Real.log ((n : ℝ) + 1)) := by
      rw [Real.log_div (by positivity) (by positivity),
          Real.log_div (by positivity) (by positivity)]
      push_cast; ring
    rw [hsplit]
    linarith

private lemma sum_inv_primes_le {y : ℕ} (hy : 2 ≤ y) :
    ∑ p ∈ primesLE y, (1 / (p : ℝ)) ≤ 5 + 4 * Real.log (Nat.log 2 y + 1 : ℝ) := by
  set J := Nat.log 2 y
  have hJ : 1 ≤ J := by
    have : 1 = Nat.log 2 2 := by decide
    rw [this]; exact Nat.log_mono_right hy
  let B : ℕ → Finset ℕ := fun j => (primesLE (2 ^ (j + 1))).filter (fun p => 2 ^ j < p)
  have hsub : primesLE y ⊆ insert 2 ((Finset.Icc 1 J).biUnion B) := by
    intro p hp
    have hpp := prime_of_mem_primesLE hp
    have hpy := le_of_mem_primesLE hp
    rcases eq_or_lt_of_le hpp.two_le with rfl | hp3
    · exact Finset.mem_insert_self 2 _
    · apply Finset.mem_insert_of_mem
      rw [Finset.mem_biUnion]
      let j := Nat.log 2 (p - 1)
      refine ⟨j, ?_, ?_⟩
      · rw [Finset.mem_Icc]
        constructor
        · have : 1 = Nat.log 2 2 := by decide
          rw [this]; exact Nat.log_mono_right (by omega)
        · exact Nat.log_mono_right (by omega)
      · rw [Finset.mem_filter, mem_primesLE]
        refine ⟨⟨?_, hpp⟩, ?_⟩
        · have h1 := Nat.lt_pow_succ_log_self (by decide : 1 < 2) (p - 1)
          have h2 : p - 1 + 1 = p := by omega
          exact h2 ▸ h1
        · have h1 := Nat.pow_log_le_self 2 (show p - 1 ≠ 0 by omega)
          have h2 : p - 1 < p := by omega
          exact lt_of_le_of_lt h1 h2
  have hsum1 : ∑ p ∈ primesLE y, (1 / (p : ℝ)) ≤
      (1 / 2 : ℝ) + ∑ j ∈ Finset.Icc 1 J, ∑ p ∈ B j, (1 / (p : ℝ)) := by
    calc ∑ p ∈ primesLE y, (1 / (p : ℝ))
        ≤ ∑ p ∈ insert 2 ((Finset.Icc 1 J).biUnion B), (1 / (p : ℝ)) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
      _ ≤ (1 / 2 : ℝ) + ∑ p ∈ (Finset.Icc 1 J).biUnion B, (1 / (p : ℝ)) := by
          by_cases h2 : 2 ∈ (Finset.Icc 1 J).biUnion B
          · rw [Finset.insert_eq_of_mem h2]; linarith
          · rw [Finset.sum_insert h2]; norm_num
      _ ≤ (1 / 2 : ℝ) + ∑ j ∈ Finset.Icc 1 J, ∑ p ∈ B j, (1 / (p : ℝ)) := by
          gcongr
          exact sum_biUnion_le_sum _ _ _ (fun _ => by positivity)
  have hblock : ∀ j ∈ Finset.Icc 1 J, ∑ p ∈ B j, (1 / (p : ℝ)) ≤ 4 / (j : ℝ) := by
    intro j hj
    have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
    have hjpos : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    rw [le_div_iff₀ hjpos]
    have h1 : (∑ p ∈ B j, (1 / (p : ℝ))) * ((j : ℝ) * Real.log 2) ≤
        (∑ p ∈ B j, Real.log p) / (2 : ℝ) ^ j := by
      rw [Finset.sum_mul, Finset.sum_div]
      apply Finset.sum_le_sum
      intro p hp
      have hpgt : 2 ^ j < p := (Finset.mem_filter.mp hp).2
      have hpgtR : (2 : ℝ) ^ j ≤ (p : ℝ) := by exact_mod_cast hpgt.le
      have hlogp : (j : ℝ) * Real.log 2 ≤ Real.log p := by
        rw [← Real.log_pow]
        exact Real.log_le_log (by positivity) hpgtR
      calc (1 / (p : ℝ)) * ((j : ℝ) * Real.log 2)
          ≤ (1 / (p : ℝ)) * Real.log p := mul_le_mul_of_nonneg_left hlogp (by positivity)
        _ = Real.log p / (p : ℝ) := by ring
        _ ≤ Real.log p / (2 : ℝ) ^ j :=
            div_le_div_of_nonneg_left
              (Real.log_nonneg (by exact_mod_cast (prime_of_mem_primesLE (Finset.mem_filter.mp hp).1).one_le))
              (by positivity) hpgtR
    have h2 : ∑ p ∈ B j, Real.log p ≤ theta (2 ^ (j + 1) : ℕ) := by
      rw [theta_eq_sum_primesLE_log]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun p hp _ => Real.log_nonneg (by exact_mod_cast (prime_of_mem_primesLE hp).one_le))
    have h3 : theta (2 ^ (j + 1) : ℕ) ≤ Real.log 4 * ((2 ^ (j + 1) : ℕ) : ℝ) :=
      Chebyshev.theta_le_log4_mul_x (by positivity)
    have hlog4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    have h4 : (Real.log 4 * ((2 ^ (j + 1) : ℕ) : ℝ)) / (2 : ℝ) ^ j = 4 * Real.log 2 := by
      rw [hlog4]; push_cast; rw [pow_succ]; field_simp; norm_num
    have h5 : (∑ p ∈ B j, (1 / (p : ℝ))) * ((j : ℝ) * Real.log 2) ≤ 4 * Real.log 2 :=
      h1.trans ((div_le_div_of_nonneg_right (h2.trans h3) (by positivity)).trans_eq h4)
    have h6 : (∑ p ∈ B j, (1 / (p : ℝ))) * (j : ℝ) * Real.log 2 ≤ 4 * Real.log 2 := by linarith
    exact le_of_mul_le_mul_right h6 hlog2
  have hsum2 : ∑ j ∈ Finset.Icc 1 J, ∑ p ∈ B j, (1 / (p : ℝ)) ≤
      4 * ∑ j ∈ Finset.Icc 1 J, (1 / (j : ℝ)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    calc ∑ p ∈ B j, (1 / (p : ℝ)) ≤ 4 / (j : ℝ) := hblock j hj
      _ = 4 * (1 / (j : ℝ)) := by ring
  have hharm := sum_inv_Icc_le J hJ
  have hloginc : Real.log J ≤ Real.log (J + 1 : ℝ) :=
    Real.log_le_log (by exact_mod_cast (show 0 < J by omega)) (by linarith)
  linarith

private lemma sum_inv_primes_ge {m₀ m₁ : ℕ} (hm₀ : 9 ≤ m₀) (hle : m₀ ≤ m₁) :
    (1 / 8 : ℝ) * Real.log ((m₁ + 1 : ℝ) / (m₀ + 1 : ℝ)) ≤
      ∑ p ∈ (primesLE (2 ^ (4 * m₁))).filter (fun p => 2 ^ (4 * m₀) < p), (1 / (p : ℝ)) := by
  let C : ℕ → Finset ℕ := fun m =>
    (primesLE (2 ^ (4 * (m + 1)))).filter (fun p => 2 ^ (4 * m) < p)
  have hdisj : Set.PairwiseDisjoint (Finset.Ico m₀ m₁ : Set ℕ) C := by
    intro a _ b _ hab
    dsimp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro p hpa hpb
    have ha1 := le_of_mem_primesLE (Finset.mem_filter.mp hpa).1
    have ha2 := (Finset.mem_filter.mp hpa).2
    have hb1 := le_of_mem_primesLE (Finset.mem_filter.mp hpb).1
    have hb2 := (Finset.mem_filter.mp hpb).2
    rcases lt_or_gt_of_ne hab with hlt | hgt
    · have : 2 ^ (4 * (a + 1)) ≤ 2 ^ (4 * b) := Nat.pow_le_pow_right (by decide) (by omega)
      omega
    · have : 2 ^ (4 * (b + 1)) ≤ 2 ^ (4 * a) := Nat.pow_le_pow_right (by decide) (by omega)
      omega
  have hsub : (Finset.Ico m₀ m₁).biUnion C ⊆
      (primesLE (2 ^ (4 * m₁))).filter (fun p => 2 ^ (4 * m₀) < p) := by
    intro p hp
    rw [Finset.mem_biUnion] at hp
    rcases hp with ⟨m, hm, hpm⟩
    have hm1 := (Finset.mem_Ico.mp hm).1
    have hm2 := (Finset.mem_Ico.mp hm).2
    rw [Finset.mem_filter, mem_primesLE] at hpm ⊢
    refine ⟨⟨hpm.1.1.trans (Nat.pow_le_pow_right (by decide) (by omega)), hpm.1.2⟩, ?_⟩
    exact lt_of_le_of_lt (Nat.pow_le_pow_right (by decide) (by omega)) hpm.2
  have hblock : ∀ m ∈ Finset.Ico m₀ m₁,
      (1 / (8 * ((m : ℝ) + 1))) ≤ ∑ p ∈ C m, (1 / (p : ℝ)) := by
    intro m hm
    have hm9 : 9 ≤ m := hm₀.trans (Finset.mem_Ico.mp hm).1
    have hpow_ge : 10 ^ 10 ≤ 2 ^ (4 * (m + 1)) := by
      have h1 : 10 ^ 10 ≤ 2 ^ 36 := by decide
      exact h1.trans (Nat.pow_le_pow_right (by decide) (by omega))
    have hth1 : (0.6 : ℝ) * (2 ^ (4 * (m + 1)) : ℕ) ≤ theta (2 ^ (4 * (m + 1)) : ℕ) :=
      theta_lower hpow_ge
    have hth2 : theta (2 ^ (4 * m) : ℕ) ≤ 1.4 * (2 ^ (4 * m) : ℕ) := by
      have h1 := Chebyshev.theta_le_log4_mul_x (show (0 : ℝ) ≤ (2 ^ (4 * m) : ℕ) by positivity)
      have hlog4 : Real.log 4 ≤ 1.4 := by
        have : Real.log 4 = 2 * Real.log 2 := by
          rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
        linarith [Real.log_two_lt_d9]
      have hnn : (0 : ℝ) ≤ (2 ^ (4 * m) : ℕ) := Nat.cast_nonneg _
      nlinarith
    have hdiff : 8 * (2 : ℝ) ^ (4 * m) ≤ ∑ p ∈ C m, Real.log p := by
      rw [← theta_sub_eq_sum_filter (Nat.pow_le_pow_right (by decide) (by omega))]
      have h16 : ((2 ^ (4 * (m + 1)) : ℕ) : ℝ) = 16 * (2 : ℝ) ^ (4 * m) := by
        push_cast; rw [show 4 * (m + 1) = 4 * m + 4 by ring, pow_add]; ring
      have h0 : ((2 ^ (4 * m) : ℕ) : ℝ) = (2 : ℝ) ^ (4 * m) := by push_cast; rfl
      linarith
    have hup : ∑ p ∈ C m, Real.log p ≤
        (∑ p ∈ C m, (1 / (p : ℝ))) * (64 * ((m : ℝ) + 1) * (2 : ℝ) ^ (4 * m)) := by
      rw [Finset.sum_mul]
      apply Finset.sum_le_sum
      intro p hp
      have hpmem := (Finset.mem_filter.mp hp).1
      have hppos : (0 : ℝ) < p := by exact_mod_cast (prime_of_mem_primesLE hpmem).pos
      have hple : (p : ℝ) ≤ 16 * (2 : ℝ) ^ (4 * m) := by
        have h1 : p ≤ 2 ^ (4 * (m + 1)) := le_of_mem_primesLE hpmem
        have hR : (p : ℝ) ≤ (2 : ℝ) ^ (4 * (m + 1)) := by exact_mod_cast h1
        rw [show 4 * (m + 1) = 4 * m + 4 by ring, pow_add] at hR
        have h16 : (2 : ℝ) ^ (4 * m) * (2 : ℝ) ^ 4 = 16 * (2 : ℝ) ^ (4 * m) := by ring
        linarith
      have hlogp : Real.log p ≤ 4 * ((m : ℝ) + 1) := by
        have h1 : Real.log p ≤ Real.log ((2 : ℝ) ^ (4 * (m + 1))) :=
          Real.log_le_log hppos (by exact_mod_cast le_of_mem_primesLE hpmem)
        rw [Real.log_pow] at h1
        push_cast at h1
        have h2 : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
        nlinarith
      have hmul : Real.log p * (p : ℝ) ≤ 64 * ((m : ℝ) + 1) * (2 : ℝ) ^ (4 * m) := by
        have hnn : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast (prime_of_mem_primesLE hpmem).one_le)
        calc Real.log p * (p : ℝ)
            ≤ (4 * ((m : ℝ) + 1)) * (16 * (2 : ℝ) ^ (4 * m)) :=
              mul_le_mul hlogp hple hppos.le (by positivity)
          _ = 64 * ((m : ℝ) + 1) * (2 : ℝ) ^ (4 * m) := by ring
      rw [one_div_mul_eq_div, le_div_iff₀ hppos]
      exact hmul
    have hden_pos : 0 < 64 * ((m : ℝ) + 1) * (2 : ℝ) ^ (4 * m) := by positivity
    have hle' : 8 * (2 : ℝ) ^ (4 * m) / (64 * ((m : ℝ) + 1) * (2 : ℝ) ^ (4 * m)) ≤
        ∑ p ∈ C m, (1 / (p : ℝ)) := by
      rw [div_le_iff₀ hden_pos]; linarith
    have heq : 8 * (2 : ℝ) ^ (4 * m) / (64 * ((m : ℝ) + 1) * (2 : ℝ) ^ (4 * m)) =
        1 / (8 * ((m : ℝ) + 1)) := by
      have h2pos : (2 : ℝ) ^ (4 * m) ≠ 0 := by positivity
      field_simp; ring
    rwa [heq] at hle'
  calc (1 / 8 : ℝ) * Real.log ((m₁ + 1 : ℝ) / (m₀ + 1 : ℝ))
      ≤ (1 / 8 : ℝ) * ∑ m ∈ Finset.Ico m₀ m₁, (1 / ((m : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_left (sum_inv_Ico_ge m₀ m₁ hle) (by norm_num)
    _ = ∑ m ∈ Finset.Ico m₀ m₁, (1 / (8 * ((m : ℝ) + 1))) := by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro m _; field_simp
    _ ≤ ∑ m ∈ Finset.Ico m₀ m₁, ∑ p ∈ C m, (1 / (p : ℝ)) := Finset.sum_le_sum hblock
    _ = ∑ p ∈ (Finset.Ico m₀ m₁).biUnion C, (1 / (p : ℝ)) := (Finset.sum_biUnion hdisj).symm
    _ ≤ ∑ p ∈ (primesLE (2 ^ (4 * m₁))).filter (fun p => 2 ^ (4 * m₀) < p), (1 / (p : ℝ)) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)

/- ### Part 3: Finite-sum Rankin smooth-number bound -/

private lemma card_smooth_le {y R : ℕ} (hR : 1 ≤ R) {σ : ℝ} (hσ : 0 < σ) :
    (((Finset.Icc 1 R).filter (fun m => ∀ p ∈ m.primeFactors, p ≤ y)).card : ℝ) ≤
      (R : ℝ) ^ σ * ∏ p ∈ primesLE y, (1 - (p : ℝ) ^ (-σ))⁻¹ := by
  classical
  set Sm := (Finset.Icc 1 R).filter (fun m => ∀ p ∈ m.primeFactors, p ≤ y)
  set P := primesLE y
  set E := Nat.log 2 R + 1
  have hRpos : (0 : ℝ) < R := by exact_mod_cast hR
  have hE : ∀ m ∈ Sm, ∀ p : P, m.factorization p.1 < E := by
    intro m hm p
    have hm1 : 1 ≤ m := (Finset.mem_Icc.mp (Finset.mem_filter.mp hm).1).1
    have hmR : m ≤ R := (Finset.mem_Icc.mp (Finset.mem_filter.mp hm).1).2
    have hp2 : 2 ≤ p.1 := (prime_of_mem_primesLE p.2).two_le
    have hpow : 2 ^ (m.factorization p.1) ≤ R := by
      calc 2 ^ (m.factorization p.1)
          ≤ p.1 ^ (m.factorization p.1) := Nat.pow_le_pow_left hp2 _
        _ ≤ m := Nat.le_of_dvd (by omega) (Nat.ordProj_dvd m p.1)
        _ ≤ R := hmR
    have hlt : 2 ^ (m.factorization p.1) < 2 ^ E :=
      lt_of_le_of_lt hpow (Nat.lt_pow_succ_log_self (by decide : 1 < 2) R)
    exact (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp hlt
  have hprod_eq : ∀ m ∈ Sm, m = ∏ p ∈ P, p ^ (m.factorization p) := by
    intro m hm
    have hm0 : m ≠ 0 := by
      have := (Finset.mem_Icc.mp (Finset.mem_filter.mp hm).1).1; omega
    have hsub : m.factorization.support ⊆ P := by
      rw [Nat.support_factorization]
      intro p hp
      rw [mem_primesLE]
      exact ⟨(Finset.mem_filter.mp hm).2 p hp, Nat.prime_of_mem_primeFactors hp⟩
    conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hm0]
    rw [Finsupp.prod]
    apply Finset.prod_subset hsub
    intro p _ hp
    have h0 : m.factorization p = 0 := by
      by_contra hne
      exact hp (Finsupp.mem_support_iff.mpr hne)
    rw [h0, pow_zero]
  let enc : ℕ → (P → Fin E) := fun m p =>
    if h : m.factorization p.1 < E then ⟨m.factorization p.1, h⟩ else ⟨0, Nat.succ_pos _⟩
  have henc_inj : Set.InjOn enc (Sm : Set ℕ) := by
    intro m₁ hm₁ m₂ hm₂ heq
    rw [hprod_eq m₁ hm₁, hprod_eq m₂ hm₂]
    apply Finset.prod_congr rfl
    intro p hp
    have h1 := congr_fun heq ⟨p, hp⟩
    dsimp only [enc] at h1
    rw [dif_pos (hE m₁ hm₁ ⟨p, hp⟩), dif_pos (hE m₂ hm₂ ⟨p, hp⟩)] at h1
    have hval := congr_arg Fin.val h1
    dsimp only at hval
    rw [hval]
  have hrpow_eq : ∀ m ∈ Sm, (m : ℝ) ^ (-σ) = ∏ p : P, ((p.1 : ℝ) ^ (-σ)) ^ (enc m p).1 := by
    intro m hm
    have hm_eq := hprod_eq m hm
    have hcast : (m : ℝ) = ∏ p : P, (p.1 : ℝ) ^ (enc m p).1 := by
      conv_lhs => rw [hm_eq]
      rw [Nat.cast_prod, ← Finset.prod_attach P]
      apply Finset.prod_congr rfl
      intro p _
      dsimp only [enc]
      rw [dif_pos (hE m hm p), Nat.cast_pow]
    rw [hcast, ← Real.finsetProd_rpow Finset.univ (fun p : P => (p.1 : ℝ) ^ (enc m p).1)
      (fun p _ => by positivity)]
    apply Finset.prod_congr rfl
    intro p _
    rw [← Real.rpow_natCast (p.1 : ℝ), ← Real.rpow_mul (Nat.cast_nonneg _),
      ← Real.rpow_natCast ((p.1 : ℝ) ^ (-σ)), ← Real.rpow_mul (Nat.cast_nonneg _), mul_comm]
  have hstep1 : (Sm.card : ℝ) * (R : ℝ) ^ (-σ) ≤ ∑ m ∈ Sm, (m : ℝ) ^ (-σ) := by
    have : (Sm.card : ℝ) * (R : ℝ) ^ (-σ) = ∑ _m ∈ Sm, (R : ℝ) ^ (-σ) := by simp
    rw [this]
    apply Finset.sum_le_sum
    intro m hm
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (Finset.mem_Icc.mp (Finset.mem_filter.mp hm).1).1
    have hmR : (m : ℝ) ≤ R := by exact_mod_cast (Finset.mem_Icc.mp (Finset.mem_filter.mp hm).1).2
    exact Real.rpow_le_rpow_of_nonpos (by linarith) hmR (by linarith)
  have hstep2 : ∑ m ∈ Sm, (m : ℝ) ^ (-σ) ≤
      ∑ e : (P → Fin E), ∏ p : P, ((p.1 : ℝ) ^ (-σ)) ^ (e p).1 := by
    let emb : Sm ↪ (P → Fin E) :=
      ⟨fun m => enc m.1, fun m₁ m₂ h => Subtype.ext (henc_inj m₁.2 m₂.2 h)⟩
    calc ∑ m ∈ Sm, (m : ℝ) ^ (-σ)
        = ∑ m ∈ Sm, ∏ p : P, ((p.1 : ℝ) ^ (-σ)) ^ (enc m p).1 :=
          Finset.sum_congr rfl hrpow_eq
      _ = ∑ m : Sm, ∏ p : P, ((p.1 : ℝ) ^ (-σ)) ^ (emb m p).1 :=
          (Finset.sum_attach Sm (fun m => ∏ p : P, ((p.1 : ℝ) ^ (-σ)) ^ (enc m p).1)).symm
      _ = ∑ e ∈ (Finset.univ : Finset Sm).map emb, ∏ p : P, ((p.1 : ℝ) ^ (-σ)) ^ (e p).1 :=
          (Finset.sum_map Finset.univ emb (fun e => ∏ p : P, ((p.1 : ℝ) ^ (-σ)) ^ (e p).1)).symm
      _ ≤ ∑ e : (P → Fin E), ∏ p : P, ((p.1 : ℝ) ^ (-σ)) ^ (e p).1 :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            (fun e _ _ => Finset.prod_nonneg (fun p _ => by positivity))
  have hstep3 : (∑ e : (P → Fin E), ∏ p : P, ((p.1 : ℝ) ^ (-σ)) ^ (e p).1) =
      ∏ p : P, ∑ k : Fin E, ((p.1 : ℝ) ^ (-σ)) ^ k.1 :=
    (Fintype.prod_sum (fun (p : P) (k : Fin E) => ((p.1 : ℝ) ^ (-σ)) ^ k.1)).symm
  have hstep4 : (∏ p : P, ∑ k : Fin E, ((p.1 : ℝ) ^ (-σ)) ^ k.1) ≤
      ∏ p ∈ P, (1 - (p : ℝ) ^ (-σ))⁻¹ := by
    rw [← Finset.prod_attach P]
    apply Finset.prod_le_prod (fun p _ => Finset.sum_nonneg (fun k _ => by positivity))
    intro p _
    set r : ℝ := (p.1 : ℝ) ^ (-σ)
    have hr0 : 0 ≤ r := Real.rpow_nonneg (Nat.cast_nonneg _) _
    have hr1 : r < 1 := by
      have hp1 : (1 : ℝ) < p.1 := by exact_mod_cast (prime_of_mem_primesLE p.2).one_lt
      exact Real.rpow_lt_one_of_one_lt_of_neg hp1 (by linarith)
    rw [Fin.sum_univ_eq_sum_range (fun k => r ^ k), geom_sum_eq hr1.ne]
    rw [div_eq_mul_inv]
    have hnum : r ^ E - 1 = -(1 - r ^ E) := by ring
    have hden : r - 1 = -(1 - r) := by ring
    rw [hnum, hden, neg_mul, inv_neg, mul_neg, neg_neg]
    calc (1 - r ^ E) * (1 - r)⁻¹ ≤ 1 * (1 - r)⁻¹ := by
          gcongr; linarith [pow_nonneg hr0 E]
      _ = (1 - r)⁻¹ := one_mul _
  have hcomb : (Sm.card : ℝ) * (R : ℝ) ^ (-σ) ≤ ∏ p ∈ P, (1 - (p : ℝ) ^ (-σ))⁻¹ :=
    hstep1.trans (hstep2.trans (hstep3.le.trans hstep4))
  calc (Sm.card : ℝ)
      = ((Sm.card : ℝ) * (R : ℝ) ^ (-σ)) * (R : ℝ) ^ σ := by
        rw [mul_assoc, ← Real.rpow_add hRpos]; simp
    _ ≤ (∏ p ∈ P, (1 - (p : ℝ) ^ (-σ))⁻¹) * (R : ℝ) ^ σ :=
        mul_le_mul_of_nonneg_right hcomb (by positivity)
    _ = (R : ℝ) ^ σ * ∏ p ∈ P, (1 - (p : ℝ) ^ (-σ))⁻¹ := mul_comm _ _

private lemma prod_inv_one_sub_rpow_le {y : ℕ} {u : ℝ} (hu : 2 ≤ u) (hyu : (y : ℝ) ≤ Real.exp u) :
    ∏ p ∈ primesLE y, (1 - (p : ℝ) ^ (-(1 - 1 / u)))⁻¹ ≤
      Real.exp (12 * ∑ p ∈ primesLE y, (1 / (p : ℝ))) := by
  set σ : ℝ := 1 - 1 / u
  have hσ_ge : (1 / 2 : ℝ) ≤ σ := by
    have : 1 / u ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hu
    linarith
  rw [Finset.mul_sum, Real.exp_sum]
  apply Finset.prod_le_prod
  · intro p hp
    have hp1 : (1 : ℝ) < p := by exact_mod_cast (prime_of_mem_primesLE hp).one_lt
    have hlt : (p : ℝ) ^ (-σ) < 1 := Real.rpow_lt_one_of_one_lt_of_neg hp1 (by linarith)
    exact inv_nonneg.mpr (by linarith)
  · intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (prime_of_mem_primesLE hp).two_le
    have hppos : (0 : ℝ) < p := by linarith
    have hpy : (p : ℝ) ≤ Real.exp u :=
      le_trans (by exact_mod_cast le_of_mem_primesLE hp) hyu
    set t : ℝ := (p : ℝ) ^ (-σ)
    have ht0 : 0 ≤ t := by positivity
    have ht34 : t ≤ 3 / 4 := by
      have h1 : t ≤ (2 : ℝ) ^ (-σ) := Real.rpow_le_rpow_of_nonpos (by norm_num) hp2 (by linarith)
      have h2 : (2 : ℝ) ^ (-σ) ≤ (2 : ℝ) ^ (-(1 / 2 : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      have h3 : (2 : ℝ) ^ (-(1 / 2 : ℝ)) ≤ 3 / 4 := by
        rw [Real.rpow_neg (by norm_num), ← Real.sqrt_eq_rpow]
        rw [inv_le_comm₀ (Real.sqrt_pos.mpr (by norm_num)) (by norm_num)]
        have hsq : ((4 / 3 : ℝ) ^ 2) ≤ (Real.sqrt 2) ^ 2 := by
          rw [Real.sq_sqrt (by norm_num)]; norm_num
        nlinarith [Real.sqrt_nonneg 2]
      linarith
    have htp : t ≤ 3 / (p : ℝ) := by
      have hpow : (p : ℝ) ^ (1 / u) ≤ Real.exp 1 := by
        calc (p : ℝ) ^ (1 / u)
            ≤ (Real.exp u) ^ (1 / u) := Real.rpow_le_rpow hppos.le hpy (by positivity)
          _ = Real.exp (u * (1 / u)) := (Real.exp_mul u (1 / u)).symm
          _ = Real.exp 1 := by congr 1; field_simp
      have heq : t = (p : ℝ) ^ (1 / u) / (p : ℝ) := by
        dsimp only [t]
        rw [show -σ = 1 / u - 1 by dsimp [σ]; ring, Real.rpow_sub hppos, Real.rpow_one]
      rw [heq]
      have he3 : Real.exp 1 ≤ 3 := by linarith [Real.exp_one_lt_d9]
      exact div_le_div_of_nonneg_right (hpow.trans he3) hppos.le
    have h1t : (1 / 4 : ℝ) ≤ 1 - t := by linarith
    have hinv : (1 - t)⁻¹ = 1 + t / (1 - t) := by
      have hne : 1 - t ≠ 0 := by linarith
      field_simp; ring
    have hexp : 1 + t / (1 - t) ≤ Real.exp (t / (1 - t)) := by
      linarith [Real.add_one_le_exp (t / (1 - t))]
    have h4t : t / (1 - t) ≤ 12 * (1 / (p : ℝ)) := by
      have h1 : t / (1 - t) ≤ 4 * t := by
        rw [div_le_iff₀ (by linarith)]
        nlinarith
      have h2 : 4 * t ≤ 4 * (3 / (p : ℝ)) := by linarith
      have h3 : 4 * (3 / (p : ℝ)) = 12 * (1 / (p : ℝ)) := by ring
      linarith
    rw [hinv]
    exact hexp.trans (Real.exp_le_exp.mpr h4t)

/- ### Part 4: Greedy residue selection and P₄ matching -/

private lemma exists_nonzero_mod_kill {p : ℕ} (hp : p.Prime) {t : ℤ} (hndvd : ¬ (p : ℤ) ∣ t) :
    ∃ c ∈ Finset.Ico 1 p, (p : ℤ) ∣ (c : ℤ) + t := by
  have : NeZero p := ⟨hp.ne_zero⟩
  let z : ZMod p := -(t : ZMod p)
  have hz : z ≠ 0 := by
    intro h0
    have ht0 : (t : ZMod p) = 0 := neg_eq_zero.mp h0
    exact hndvd ((ZMod.intCast_zmod_eq_zero_iff_dvd t p).mp ht0)
  refine ⟨z.val, ?_, ?_⟩
  · rw [Finset.mem_Ico]
    refine ⟨?_, ZMod.val_lt z⟩
    have hval0 : z.val ≠ 0 := fun h => hz ((ZMod.val_eq_zero z).mp h)
    omega
  · rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    simp [z]

private lemma card_filter_dvd_D0_le {r p : ℕ} (hp : 0 < p) :
    (((Finset.Icc (-(r : ℤ)) (r : ℤ)).erase 0).filter (fun t => (p : ℤ) ∣ t)).card ≤
      2 * (r / p) := by
  let Spos := (Finset.Icc 1 (r / p)).image (fun k : ℕ => ((k * p : ℕ) : ℤ))
  let Sneg := (Finset.Icc 1 (r / p)).image (fun k : ℕ => -((k * p : ℕ) : ℤ))
  have hsub : (((Finset.Icc (-(r : ℤ)) (r : ℤ)).erase 0).filter (fun t => (p : ℤ) ∣ t)) ⊆
      Spos ∪ Sneg := by
    intro t ht
    rw [Finset.mem_filter, Finset.mem_erase, Finset.mem_Icc] at ht
    rcases ht with ⟨⟨ht0, hlo, hhi⟩, ⟨m, hm⟩⟩
    have hm0 : m ≠ 0 := by intro h; rw [h, mul_zero] at hm; exact ht0 hm
    have habs : t.natAbs = p * m.natAbs := by
      rw [hm, Int.natAbs_mul, Int.natAbs_natCast]
    have htr : t.natAbs ≤ r := by omega
    have hmr : m.natAbs ≤ r / p := by
      rw [Nat.le_div_iff_mul_le hp]
      rw [mul_comm] at habs; omega
    have hm1 : 1 ≤ m.natAbs := Nat.pos_of_ne_zero (Int.natAbs_ne_zero.mpr hm0)
    rw [Finset.mem_union]
    rcases lt_or_gt_of_ne hm0 with hlt | hgt
    · right
      rw [Finset.mem_image]
      refine ⟨m.natAbs, Finset.mem_Icc.mpr ⟨hm1, hmr⟩, ?_⟩
      set k := m.natAbs
      have hm_eq : m = -(k : ℤ) := by omega
      calc -((k * p : ℕ) : ℤ) = (p : ℤ) * -(k : ℤ) := by push_cast; ring
        _ = (p : ℤ) * m := by rw [hm_eq]
        _ = t := hm.symm
    · left
      rw [Finset.mem_image]
      refine ⟨m.natAbs, Finset.mem_Icc.mpr ⟨hm1, hmr⟩, ?_⟩
      set k := m.natAbs
      have hm_eq : m = (k : ℤ) := by omega
      calc ((k * p : ℕ) : ℤ) = (p : ℤ) * (k : ℤ) := by push_cast; ring
        _ = (p : ℤ) * m := by rw [hm_eq]
        _ = t := hm.symm
  calc (((Finset.Icc (-(r : ℤ)) (r : ℤ)).erase 0).filter (fun t => (p : ℤ) ∣ t)).card
      ≤ (Spos ∪ Sneg).card := Finset.card_le_card hsub
    _ ≤ Spos.card + Sneg.card := Finset.card_union_le _ _
    _ ≤ (Finset.Icc 1 (r / p)).card + (Finset.Icc 1 (r / p)).card :=
        Nat.add_le_add Finset.card_image_le Finset.card_image_le
    _ = 2 * (r / p) := by simp; omega

private lemma greedy_step (S : Finset ℤ) {p : ℕ} (hp : p.Prime) :
    ∃ c ∈ Finset.Ico 1 p,
      ((S.filter (fun t => ¬ (p : ℤ) ∣ (c : ℤ) + t)).card : ℝ) ≤
        (S.card : ℝ) - ((S.filter (fun t => ¬ (p : ℤ) ∣ t)).card : ℝ) / ((p : ℝ) - 1) := by
  classical
  set S' := S.filter (fun t => ¬ (p : ℤ) ∣ t)
  have hsum_ge : S'.card ≤
      ∑ c ∈ Finset.Ico 1 p, (S.filter (fun t => (p : ℤ) ∣ (c : ℤ) + t)).card := by
    have hswap :
        ∑ c ∈ Finset.Ico 1 p, (S.filter (fun t => (p : ℤ) ∣ (c : ℤ) + t)).card =
          ∑ t ∈ S, ((Finset.Ico 1 p).filter (fun c : ℕ => (p : ℤ) ∣ (c : ℤ) + t)).card := by
      calc ∑ c ∈ Finset.Ico 1 p, (S.filter (fun t => (p : ℤ) ∣ (c : ℤ) + t)).card
          = ∑ c ∈ Finset.Ico 1 p, ∑ t ∈ S, (if (p : ℤ) ∣ (c : ℤ) + t then (1 : ℕ) else 0) := by
            apply Finset.sum_congr rfl; intro c _; rw [Finset.card_filter]
        _ = ∑ t ∈ S, ∑ c ∈ Finset.Ico 1 p, (if (p : ℤ) ∣ (c : ℤ) + t then (1 : ℕ) else 0) :=
            Finset.sum_comm
        _ = ∑ t ∈ S, ((Finset.Ico 1 p).filter (fun c : ℕ => (p : ℤ) ∣ (c : ℤ) + t)).card := by
            apply Finset.sum_congr rfl; intro t _; rw [Finset.card_filter]
    rw [hswap]
    calc S'.card
        = ∑ _t ∈ S', (1 : ℕ) := by simp
      _ ≤ ∑ t ∈ S', ((Finset.Ico 1 p).filter (fun c : ℕ => (p : ℤ) ∣ (c : ℤ) + t)).card := by
          apply Finset.sum_le_sum
          intro t ht
          obtain ⟨c, hc, hdvd⟩ := exists_nonzero_mod_kill hp (Finset.mem_filter.mp ht).2
          have hmem : c ∈ (Finset.Ico 1 p).filter (fun c : ℕ => (p : ℤ) ∣ (c : ℤ) + t) :=
            Finset.mem_filter.mpr ⟨hc, hdvd⟩
          exact Finset.card_pos.mpr ⟨c, hmem⟩
      _ ≤ ∑ t ∈ S, ((Finset.Ico 1 p).filter (fun c : ℕ => (p : ℤ) ∣ (c : ℤ) + t)).card :=
          Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
  have hne : (Finset.Ico 1 p).Nonempty := ⟨1, Finset.mem_Ico.mpr ⟨le_rfl, hp.one_lt⟩⟩
  have hcard : ((Finset.Ico 1 p).card : ℝ) = (p : ℝ) - 1 := by
    rw [Nat.card_Ico, Nat.cast_sub hp.one_le, Nat.cast_one]
  have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by
    have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    linarith
  have hsumR : (S'.card : ℝ) ≤
      ∑ c ∈ Finset.Ico 1 p, ((S.filter (fun t => (p : ℤ) ∣ (c : ℤ) + t)).card : ℝ) := by
    exact_mod_cast hsum_ge
  have hex : ∃ c ∈ Finset.Ico 1 p,
      (S'.card : ℝ) / ((p : ℝ) - 1) ≤ ((S.filter (fun t => (p : ℤ) ∣ (c : ℤ) + t)).card : ℝ) := by
    by_contra! hall
    have hlt : ∑ c ∈ Finset.Ico 1 p, ((S.filter (fun t => (p : ℤ) ∣ (c : ℤ) + t)).card : ℝ) <
        ∑ _c ∈ Finset.Ico 1 p, ((S'.card : ℝ) / ((p : ℝ) - 1)) :=
      Finset.sum_lt_sum_of_nonempty hne hall
    simp only [Finset.sum_const, nsmul_eq_mul, hcard] at hlt
    rw [mul_div_cancel₀ _ hp1.ne'] at hlt
    linarith
  obtain ⟨c, hc, hge⟩ := hex
  refine ⟨c, hc, ?_⟩
  have hpart : (S.filter (fun t => (p : ℤ) ∣ (c : ℤ) + t)).card +
      (S.filter (fun t => ¬ (p : ℤ) ∣ (c : ℤ) + t)).card = S.card :=
    Finset.card_filter_add_card_filter_not (fun t => (p : ℤ) ∣ (c : ℤ) + t)
  have hpartR : ((S.filter (fun t => (p : ℤ) ∣ (c : ℤ) + t)).card : ℝ) +
      ((S.filter (fun t => ¬ (p : ℤ) ∣ (c : ℤ) + t)).card : ℝ) = (S.card : ℝ) := by
    exact_mod_cast hpart
  linarith

private lemma greedy_sieve {S₁ D₀ : Finset ℤ} (hS₁ : S₁ ⊆ D₀) {T : ℝ} (_hT : 0 ≤ T)
    (Q : Finset ℕ) (hQp : ∀ p ∈ Q, p.Prime)
    (hdiv : ∀ p ∈ Q, ((D₀.filter (fun t => (p : ℤ) ∣ t)).card : ℝ) ≤ T / 2) :
    ∃ f : ℕ → ℕ, (∀ p ∈ Q, 1 ≤ f p ∧ f p < p) ∧
      ((S₁.filter (fun t => ∀ p ∈ Q, ¬ (p : ℤ) ∣ (f p : ℤ) + t)).card : ℝ) ≤
        max T ((S₁.card : ℝ) * Real.exp (-(1 / 2 : ℝ) * ∑ p ∈ Q, (1 / (p : ℝ)))) := by
  classical
  induction Q using Finset.induction with
  | empty =>
    refine ⟨fun _ => 1, by simp, ?_⟩
    simp only [Finset.notMem_empty, IsEmpty.forall_iff, implies_true, Finset.filter_true,
      Finset.sum_empty, mul_zero, Real.exp_zero, mul_one]
    exact le_max_right _ _
  | @insert p Q hpQ ih =>
    have hpp : p.Prime := hQp p (Finset.mem_insert_self p Q)
    obtain ⟨f, hf, hcard⟩ := ih
      (fun q hq => hQp q (Finset.mem_insert_of_mem hq))
      (fun q hq => hdiv q (Finset.mem_insert_of_mem hq))
    set SQ := S₁.filter (fun t => ∀ q ∈ Q, ¬ (q : ℤ) ∣ (f q : ℤ) + t)
    by_cases hleT : (SQ.card : ℝ) ≤ T
    · refine ⟨Function.update f p 1, ?_, ?_⟩
      · intro q hq
        rcases Finset.mem_insert.mp hq with rfl | hqQ
        · simp [hpp.one_lt]
        · rw [Function.update_of_ne (by rintro rfl; exact hpQ hqQ)]
          exact hf q hqQ
      · have hsub : S₁.filter (fun t => ∀ q ∈ insert p Q,
            ¬ (q : ℤ) ∣ (Function.update f p 1 q : ℤ) + t) ⊆ SQ := by
          intro t ht
          rw [Finset.mem_filter] at ht ⊢
          refine ⟨ht.1, fun q hqQ => ?_⟩
          have h := ht.2 q (Finset.mem_insert_of_mem hqQ)
          rwa [Function.update_of_ne (by rintro rfl; exact hpQ hqQ)] at h
        have hcle : ((S₁.filter (fun t => ∀ q ∈ insert p Q,
            ¬ (q : ℤ) ∣ (Function.update f p 1 q : ℤ) + t)).card : ℝ) ≤ (SQ.card : ℝ) := by
          exact_mod_cast Finset.card_le_card hsub
        exact (hcle.trans hleT).trans (le_max_left _ _)
    · push Not at hleT
      have hSQ_le : (SQ.card : ℝ) ≤
          (S₁.card : ℝ) * Real.exp (-(1 / 2 : ℝ) * ∑ q ∈ Q, (1 / (q : ℝ))) := by
        rcases max_cases T ((S₁.card : ℝ) * Real.exp (-(1 / 2 : ℝ) * ∑ q ∈ Q, (1 / (q : ℝ)))) with
          ⟨h1, _⟩ | ⟨h2, _⟩
        · linarith
        · linarith
      obtain ⟨c, hc, hstep⟩ := greedy_step SQ hpp
      have hc1 : 1 ≤ c := (Finset.mem_Ico.mp hc).1
      have hcp : c < p := (Finset.mem_Ico.mp hc).2
      have hbad : ((SQ.filter (fun t => (p : ℤ) ∣ t)).card : ℝ) ≤ (SQ.card : ℝ) / 2 := by
        have h1 : SQ.filter (fun t => (p : ℤ) ∣ t) ⊆ D₀.filter (fun t => (p : ℤ) ∣ t) :=
          Finset.filter_subset_filter _ ((Finset.filter_subset _ _).trans hS₁)
        have h2 : ((SQ.filter (fun t => (p : ℤ) ∣ t)).card : ℝ) ≤
            ((D₀.filter (fun t => (p : ℤ) ∣ t)).card : ℝ) := by exact_mod_cast Finset.card_le_card h1
        have h3 := hdiv p (Finset.mem_insert_self p Q)
        linarith
      have hgood : (SQ.card : ℝ) / 2 ≤ ((SQ.filter (fun t => ¬ (p : ℤ) ∣ t)).card : ℝ) := by
        have hpart := Finset.card_filter_add_card_filter_not (s := SQ) (fun t => (p : ℤ) ∣ t)
        have hpartR : ((SQ.filter (fun t => (p : ℤ) ∣ t)).card : ℝ) +
            ((SQ.filter (fun t => ¬ (p : ℤ) ∣ t)).card : ℝ) = (SQ.card : ℝ) := by exact_mod_cast hpart
        linarith
      have hppos : (0 : ℝ) < p := by exact_mod_cast hpp.pos
      have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by
        have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hpp.two_le
        linarith
      have hfrac : (SQ.card : ℝ) / (2 * (p : ℝ)) ≤
          ((SQ.filter (fun t => ¬ (p : ℤ) ∣ t)).card : ℝ) / ((p : ℝ) - 1) := by
        calc (SQ.card : ℝ) / (2 * (p : ℝ))
            = ((SQ.card : ℝ) / 2) / (p : ℝ) := by ring
          _ ≤ ((SQ.card : ℝ) / 2) / ((p : ℝ) - 1) := by
              gcongr; linarith
          _ ≤ ((SQ.filter (fun t => ¬ (p : ℤ) ∣ t)).card : ℝ) / ((p : ℝ) - 1) := by
              gcongr
      have hshrink : ((SQ.filter (fun t => ¬ (p : ℤ) ∣ (c : ℤ) + t)).card : ℝ) ≤
          (SQ.card : ℝ) * Real.exp (-(1 / 2 : ℝ) * (1 / (p : ℝ))) := by
        have hexp : 1 - (1 / 2 : ℝ) * (1 / (p : ℝ)) ≤ Real.exp (-(1 / 2 : ℝ) * (1 / (p : ℝ))) := by
          linarith [Real.add_one_le_exp (-(1 / 2 : ℝ) * (1 / (p : ℝ)))]
        have h1 : (SQ.card : ℝ) - (SQ.card : ℝ) / (2 * (p : ℝ)) =
            (SQ.card : ℝ) * (1 - (1 / 2 : ℝ) * (1 / (p : ℝ))) := by ring
        calc ((SQ.filter (fun t => ¬ (p : ℤ) ∣ (c : ℤ) + t)).card : ℝ)
            ≤ (SQ.card : ℝ) - (SQ.card : ℝ) / (2 * (p : ℝ)) := by linarith
          _ = (SQ.card : ℝ) * (1 - (1 / 2 : ℝ) * (1 / (p : ℝ))) := h1
          _ ≤ (SQ.card : ℝ) * Real.exp (-(1 / 2 : ℝ) * (1 / (p : ℝ))) :=
              mul_le_mul_of_nonneg_left hexp (Nat.cast_nonneg _)
      refine ⟨Function.update f p c, ?_, ?_⟩
      · intro q hq
        rcases Finset.mem_insert.mp hq with rfl | hqQ
        · simp [hc1, hcp]
        · rw [Function.update_of_ne (by rintro rfl; exact hpQ hqQ)]
          exact hf q hqQ
      · have heq_set : S₁.filter (fun t => ∀ q ∈ insert p Q,
            ¬ (q : ℤ) ∣ (Function.update f p c q : ℤ) + t) =
            SQ.filter (fun t => ¬ (p : ℤ) ∣ (c : ℤ) + t) := by
          ext t
          simp only [SQ, Finset.mem_filter]
          constructor
          · rintro ⟨ht1, hall⟩
            refine ⟨⟨ht1, fun q hqQ => ?_⟩, ?_⟩
            · have h := hall q (Finset.mem_insert_of_mem hqQ)
              rwa [Function.update_of_ne (by rintro rfl; exact hpQ hqQ)] at h
            · have h := hall p (Finset.mem_insert_self p Q)
              rwa [Function.update_self] at h
          · rintro ⟨⟨ht1, hQ⟩, hp'⟩
            refine ⟨ht1, fun q hq => ?_⟩
            rcases Finset.mem_insert.mp hq with rfl | hqQ
            · rwa [Function.update_self]
            · rw [Function.update_of_ne (by rintro rfl; exact hpQ hqQ)]
              exact hQ q hqQ
        rw [heq_set]
        refine le_trans ?_ (le_max_right _ _)
        calc ((SQ.filter (fun t => ¬ (p : ℤ) ∣ (c : ℤ) + t)).card : ℝ)
            ≤ (SQ.card : ℝ) * Real.exp (-(1 / 2 : ℝ) * (1 / (p : ℝ))) := hshrink
          _ ≤ ((S₁.card : ℝ) * Real.exp (-(1 / 2 : ℝ) * ∑ q ∈ Q, (1 / (q : ℝ)))) *
                Real.exp (-(1 / 2 : ℝ) * (1 / (p : ℝ))) :=
              mul_le_mul_of_nonneg_right hSQ_le (Real.exp_pos _).le
          _ = (S₁.card : ℝ) * Real.exp (-(1 / 2 : ℝ) * ∑ q ∈ insert p Q, (1 / (q : ℝ))) := by
              rw [mul_assoc, ← Real.exp_add, Finset.sum_insert hpQ]; congr 2; ring

private lemma match_P4 (P₄ : Finset ℕ) (hP₄ : ∀ p ∈ P₄, p.Prime)
    (S : Finset ℤ) (hcard : S.card + 1 ≤ P₄.card)
    (hdiv1 : ∀ t ∈ S, (P₄.filter (fun p : ℕ => (p : ℤ) ∣ t)).card ≤ 1) :
    ∃ used : Finset ℕ, used ⊆ P₄ ∧ used.card ≤ S.card ∧
      ∃ f : ℕ → ℕ, (∀ p ∈ used, 1 ≤ f p ∧ f p < p) ∧
        (∀ t ∈ S, ∃ p ∈ used, (p : ℤ) ∣ (f p : ℤ) + t) := by
  classical
  induction S using Finset.induction with
  | empty =>
    exact ⟨∅, Finset.empty_subset _, by simp, fun _ => 1, by simp, by simp⟩
  | @insert t S htS ih =>
    have hcard_ins : (insert t S).card = S.card + 1 := Finset.card_insert_of_notMem htS
    obtain ⟨used, hused_sub, hused_card, f, hf, hcov⟩ := ih
      (by omega)
      (fun s hs => hdiv1 s (Finset.mem_insert_of_mem hs))
    set avail := (P₄ \ used).filter (fun p : ℕ => ¬ (p : ℤ) ∣ t)
    have havail_pos : 0 < avail.card := by
      have hsdiff : (P₄ \ used).card = P₄.card - used.card := by
        rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hused_sub]
      have hbad : ((P₄ \ used).filter (fun p : ℕ => (p : ℤ) ∣ t)).card ≤ 1 := by
        calc ((P₄ \ used).filter (fun p : ℕ => (p : ℤ) ∣ t)).card
            ≤ (P₄.filter (fun p : ℕ => (p : ℤ) ∣ t)).card :=
              Finset.card_le_card (Finset.filter_subset_filter _ Finset.sdiff_subset)
          _ ≤ 1 := hdiv1 t (Finset.mem_insert_self t S)
      have hpart := Finset.card_filter_add_card_filter_not (s := P₄ \ used)
        (fun p : ℕ => (p : ℤ) ∣ t)
      have hav : avail.card = ((P₄ \ used).filter (fun p : ℕ => ¬ (p : ℤ) ∣ t)).card := rfl
      omega
    obtain ⟨p, hp_avail⟩ := Finset.card_pos.mp havail_pos
    have hp_sdiff := (Finset.mem_filter.mp hp_avail).1
    have hp_P₄ : p ∈ P₄ := (Finset.mem_sdiff.mp hp_sdiff).1
    have hp_not_used : p ∉ used := (Finset.mem_sdiff.mp hp_sdiff).2
    have hp_ndvd : ¬ (p : ℤ) ∣ t := (Finset.mem_filter.mp hp_avail).2
    obtain ⟨c, hc, hdvd⟩ := exists_nonzero_mod_kill (hP₄ p hp_P₄) hp_ndvd
    refine ⟨insert p used, Finset.insert_subset hp_P₄ hused_sub, ?_, Function.update f p c, ?_, ?_⟩
    · rw [Finset.card_insert_of_notMem hp_not_used, hcard_ins]; omega
    · intro q hq
      rcases Finset.mem_insert.mp hq with rfl | hq_u
      · rw [Function.update_self]; exact ⟨(Finset.mem_Ico.mp hc).1, (Finset.mem_Ico.mp hc).2⟩
      · rw [Function.update_of_ne (by rintro rfl; exact hp_not_used hq_u)]
        exact hf q hq_u
    · intro s hs
      rcases Finset.mem_insert.mp hs with rfl | hsS
      · exact ⟨p, Finset.mem_insert_self p used, by rwa [Function.update_self]⟩
      · obtain ⟨q, hq_u, hqdvd⟩ := hcov s hsS
        refine ⟨q, Finset.mem_insert_of_mem hq_u, ?_⟩
        rwa [Function.update_of_ne (by rintro rfl; exact hp_not_used hq_u)]

/- ### Part 5: Classifying S₁ survivors -/

private lemma card_natAbs_shift_le {S : Finset ℤ} {M : Finset ℕ}
    (h : ∀ t ∈ S, (1 + t).natAbs ∈ M) : S.card ≤ 2 * M.card := by
  classical
  let Mpos := M.image (fun m : ℕ => (m : ℤ) - 1)
  let Mneg := M.image (fun m : ℕ => -(m : ℤ) - 1)
  have hsub : S ⊆ Mpos ∪ Mneg := by
    intro t ht
    have hm : (1 + t).natAbs ∈ M := h t ht
    rw [Finset.mem_union]
    rcases le_or_gt 0 (1 + t) with hnn | hneg
    · left
      rw [Finset.mem_image]
      refine ⟨(1 + t).natAbs, hm, ?_⟩
      omega
    · right
      rw [Finset.mem_image]
      refine ⟨(1 + t).natAbs, hm, ?_⟩
      omega
  calc S.card
      ≤ (Mpos ∪ Mneg).card := Finset.card_le_card hsub
    _ ≤ Mpos.card + Mneg.card := Finset.card_union_le _ _
    _ ≤ M.card + M.card := Nat.add_le_add Finset.card_image_le Finset.card_image_le
    _ = 2 * M.card := by omega

private lemma S1_card_le {x K' w₂ y : ℕ} (hK' : 1 ≤ K') (hx : 100 ≤ x)
    (hw₁ : 30 * K' ≤ w₂) (hw₂y : w₂ ≤ y) (hyx : y ≤ x / 10) :
    let r := 2 * K' * x
    let D₀ := (Finset.Icc (-(r : ℤ)) (r : ℤ)).erase 0
    let P₁ := (primesLE x).filter (fun p => p ≤ w₂)
    let P₃ := (primesLE x).filter (fun p => y < p ∧ p ≤ x / 10)
    let S₁ := D₀.filter (fun t => ∀ p ∈ P₁ ∪ P₃, ¬ (p : ℤ) ∣ 1 + t)
    S₁.card ≤
      2 * ((Finset.Icc 1 (r + 1)).filter (fun m => ∀ p ∈ m.primeFactors, p ≤ y)).card +
      2 * (primesLE (r + 1)).card := by
  classical
  intro r D₀ P₁ P₃ S₁
  set Sm := (Finset.Icc 1 (r + 1)).filter (fun m => ∀ p ∈ m.primeFactors, p ≤ y)
  have h2_le_w2 : 2 ≤ w₂ := by omega
  have h2P₁ : 2 ∈ P₁ := by
    rw [Finset.mem_filter, mem_primesLE]
    exact ⟨⟨by omega, Nat.prime_two⟩, h2_le_w2⟩
  have hmem : ∀ t ∈ S₁, (1 + t).natAbs ∈ Sm ∪ primesLE (r + 1) := by
    intro t ht
    have htD := (Finset.mem_filter.mp ht).1
    have htndvd := (Finset.mem_filter.mp ht).2
    have htIcc := (Finset.mem_erase.mp htD).2
    have hlo := (Finset.mem_Icc.mp htIcc).1
    have hhi := (Finset.mem_Icc.mp htIcc).2
    set m := (1 + t).natAbs
    have hm0 : m ≠ 0 := by
      intro h0
      have ht1 : 1 + t = 0 := Int.natAbs_eq_zero.mp h0
      have hdvd2 : (2 : ℤ) ∣ 1 + t := by rw [ht1]; exact dvd_zero _
      exact htndvd 2 (Finset.mem_union_left _ h2P₁) hdvd2
    have hm1 : 1 ≤ m := Nat.pos_of_ne_zero hm0
    have hmr : m ≤ r + 1 := by omega
    have hpf_ndvd : ∀ p ∈ m.primeFactors, p ∉ P₁ ∪ P₃ := by
      intro p hp hmemP
      have hdvd_m : p ∣ m := Nat.dvd_of_mem_primeFactors hp
      have hdvd_z : (p : ℤ) ∣ 1 + t := Int.natCast_dvd.mpr hdvd_m
      exact htndvd p hmemP hdvd_z
    rw [Finset.mem_union]
    by_cases hsm : ∀ p ∈ m.primeFactors, p ≤ y
    · left
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hm1, hmr⟩, hsm⟩
    · right
      push Not at hsm
      obtain ⟨p, hp_pf, hpy⟩ := hsm
      have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp_pf
      have hpm : p ∣ m := Nat.dvd_of_mem_primeFactors hp_pf
      have hpgt : x / 10 < p := by
        by_contra! hple
        have hpP₃ : p ∈ P₃ := by
          rw [Finset.mem_filter, mem_primesLE]
          exact ⟨⟨hple.trans (Nat.div_le_self x 10), hpp⟩, hpy, hple⟩
        exact hpf_ndvd p hp_pf (Finset.mem_union_right _ hpP₃)
      obtain ⟨s, hms⟩ := hpm
      have hspos : 1 ≤ s := by
        by_contra! hs0; interval_cases s; simp at hms; omega
      have h10p : x < 10 * p := by omega
      have h10m : 10 * m ≤ 30 * K' * x := by
        have h1 : r + 1 ≤ 3 * K' * x := by dsimp [r]; nlinarith
        nlinarith
      have hs_lt : s < 30 * K' := by
        have : x * s < 10 * p * s := Nat.mul_lt_mul_of_pos_right h10p hspos
        rw [mul_assoc, ← hms] at this
        nlinarith
      have hs1 : s = 1 := by
        by_contra hsne
        let q := s.minFac
        have hqp : q.Prime := Nat.minFac_prime hsne
        have hqs : q ∣ s := Nat.minFac_dvd s
        have hqm : q ∣ m := hqs.trans ⟨p, by rw [hms, mul_comm]⟩
        have hqle : q ≤ s := Nat.minFac_le (by omega)
        have hqw2 : q ≤ w₂ := by omega
        have hqx : q ≤ x := by omega
        have hqP₁ : q ∈ P₁ := by
          rw [Finset.mem_filter, mem_primesLE]
          exact ⟨⟨hqx, hqp⟩, hqw2⟩
        exact hpf_ndvd q (Nat.mem_primeFactors.mpr ⟨hqp, hqm, hm0⟩) (Finset.mem_union_left _ hqP₁)
      have hmp : m = p := by rw [hms, hs1, mul_one]
      rw [hmp, mem_primesLE]
      exact ⟨hmp ▸ hmr, hpp⟩
  calc S₁.card
      ≤ 2 * (Sm ∪ primesLE (r + 1)).card := card_natAbs_shift_le hmem
    _ ≤ 2 * (Sm.card + (primesLE (r + 1)).card) := Nat.mul_le_mul_left 2 (Finset.card_union_le _ _)
    _ = 2 * Sm.card + 2 * (primesLE (r + 1)).card := by ring

/- ### Part 6: Modular parameter bounds and CRT assembly -/

private lemma smooth_bound_of_large {x K' : ℕ} (hK' : 1 ≤ K') (hx : 10 ^ 10 ≤ x)
    (hu_ge : (Real.log (6 * (K' : ℝ)) + 61 + 500) ^ 4 + 100 ≤ Real.sqrt (Real.log (x : ℝ)))
    (hu1000 : (1000 : ℝ) ^ 4 ≤ Real.sqrt (Real.log (x : ℝ))) :
    let r := 2 * K' * x
    let y := ⌊Real.exp (Real.sqrt (Real.log (x : ℝ)))⌋₊
    2 * (((Finset.Icc 1 (r + 1)).filter (fun m => ∀ p ∈ m.primeFactors, p ≤ y)).card : ℝ) ≤
      (x : ℝ) / Real.log x := by
  intro r y
  set u : ℝ := Real.sqrt (Real.log (x : ℝ))
  have hxpos : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
  have hu_pos : 0 < u := by
    have : (1000 : ℝ) ^ 4 ≤ u := hu1000
    linarith [show (0 : ℝ) < (1000 : ℝ) ^ 4 by norm_num]
  have hu_gt2 : 2 ≤ u := by
    have : (1000 : ℝ) ^ 4 ≤ u := hu1000
    linarith [show (2 : ℝ) ≤ (1000 : ℝ) ^ 4 by norm_num]
  have hlogx_eq : Real.log (x : ℝ) = u ^ 2 :=
    (Real.sq_sqrt (Real.log_nonneg (by exact_mod_cast (show 1 ≤ x by omega)))).symm
  have hlogx_pos : 0 < Real.log (x : ℝ) := by rw [hlogx_eq]; positivity
  have hy_le : (y : ℝ) ≤ Real.exp u := Nat.floor_le (Real.exp_pos u).le
  have hy_ge2 : 2 ≤ y := by
    have h1 : (3 : ℝ) ≤ Real.exp u := by
      have := pow_four_div_24_le_exp hu_pos.le
      have : (10 : ℝ) ≤ u := by linarith [show (10 : ℝ) ≤ (1000 : ℝ) ^ 4 by norm_num]
      have h4 : (10 : ℝ) ^ 4 ≤ u ^ 4 := pow_le_pow_left₀ (by norm_num) this 4
      linarith
    have h2 : (2 : ℝ) ≤ (y : ℝ) := by linarith [Nat.lt_floor_add_one (Real.exp u)]
    exact_mod_cast h2
  set Sm := (Finset.Icc 1 (r + 1)).filter (fun m => ∀ p ∈ m.primeFactors, p ≤ y)
  set σ : ℝ := 1 - 1 / u
  have hσ_pos : 0 < σ := by
    have : 1 / u < 1 := by rw [div_lt_one hu_pos]; linarith
    linarith
  have hrankin := card_smooth_le (y := y) (R := r + 1) (Nat.succ_pos r) hσ_pos
  have hprod := prod_inv_one_sub_rpow_le hu_gt2 hy_le
  have hsum_inv := sum_inv_primes_le hy_ge2
  have hlog2y : (Nat.log 2 y : ℝ) + 1 ≤ 2 * u + 1 := by
    have h1 := nat_log2_le_two_mul_log (show 1 ≤ y by omega)
    have h2 : Real.log y ≤ u := by
      calc Real.log y ≤ Real.log (Real.exp u) :=
            Real.log_le_log (by exact_mod_cast (show 0 < y by omega)) hy_le
        _ = u := Real.log_exp u
    linarith
  have hlog_log2y : Real.log (Nat.log 2 y + 1 : ℝ) ≤ 4 * (3 * u) ^ (1 / 4 : ℝ) := by
    calc Real.log (Nat.log 2 y + 1 : ℝ)
        ≤ Real.log (3 * u) := Real.log_le_log (by positivity) (by linarith)
      _ ≤ 4 * (3 * u) ^ (1 / 4 : ℝ) := log_le_four_mul_rpow_quarter (by positivity)
  have hprod_le : ∏ p ∈ primesLE y, (1 - (p : ℝ) ^ (-σ))⁻¹ ≤
      Real.exp (60 + 192 * (3 * u) ^ (1 / 4 : ℝ)) := by
    calc ∏ p ∈ primesLE y, (1 - (p : ℝ) ^ (-σ))⁻¹
        ≤ Real.exp (12 * ∑ p ∈ primesLE y, (1 / (p : ℝ))) := hprod
      _ ≤ Real.exp (12 * (5 + 4 * Real.log (Nat.log 2 y + 1 : ℝ))) :=
          Real.exp_le_exp.mpr (by linarith)
      _ ≤ Real.exp (60 + 192 * (3 * u) ^ (1 / 4 : ℝ)) :=
          Real.exp_le_exp.mpr (by linarith)
  have hr1_pos : (0 : ℝ) < (r + 1 : ℕ) := by positivity
  have hr1_ge_x : (x : ℝ) ≤ ((r + 1 : ℕ) : ℝ) := by
    have : x ≤ r + 1 := by dsimp [r]; nlinarith
    exact_mod_cast this
  have hr1_le : ((r + 1 : ℕ) : ℝ) ≤ 3 * (K' : ℝ) * x := by
    have : r + 1 ≤ 3 * K' * x := by dsimp [r]; nlinarith
    exact_mod_cast this
  have hpow_le : ((r + 1 : ℕ) : ℝ) ^ σ ≤ 3 * (K' : ℝ) * x * Real.exp (-u) := by
    rw [Real.rpow_def_of_pos hr1_pos]
    have hlog_ge : u ^ 2 ≤ Real.log ((r + 1 : ℕ) : ℝ) := by
      rw [← hlogx_eq]; exact Real.log_le_log hxpos hr1_ge_x
    have hdiv_ge : u ≤ Real.log ((r + 1 : ℕ) : ℝ) / u := by
      rw [le_div_iff₀ hu_pos]; linarith
    have hexp_eq : Real.log ((r + 1 : ℕ) : ℝ) * σ =
        Real.log ((r + 1 : ℕ) : ℝ) - Real.log ((r + 1 : ℕ) : ℝ) / u := by
      dsimp [σ]; ring
    rw [hexp_eq]
    calc Real.exp (Real.log ((r + 1 : ℕ) : ℝ) - Real.log ((r + 1 : ℕ) : ℝ) / u)
        ≤ Real.exp (Real.log ((r + 1 : ℕ) : ℝ) - u) := Real.exp_le_exp.mpr (by linarith)
      _ = Real.exp (Real.log ((r + 1 : ℕ) : ℝ)) * Real.exp (-u) := by
          rw [sub_eq_add_neg, Real.exp_add]
      _ = ((r + 1 : ℕ) : ℝ) * Real.exp (-u) := by rw [Real.exp_log hr1_pos]
      _ ≤ 3 * (K' : ℝ) * x * Real.exp (-u) :=
          mul_le_mul_of_nonneg_right hr1_le (Real.exp_pos _).le
  have hmain_exp : 6 * (K' : ℝ) * Real.log x * Real.exp (60 + 192 * (3 * u) ^ (1 / 4 : ℝ) - u) ≤ 1 := by
    have hKpos : (0 : ℝ) < K' := by exact_mod_cast (show 0 < K' by omega)
    have h6K : 6 * (K' : ℝ) * Real.log x = Real.exp (Real.log (6 * (K' : ℝ)) + 2 * Real.log u) := by
      rw [Real.exp_add, Real.exp_log (by positivity),
          show (2 : ℝ) * Real.log u = Real.log (u ^ 2) by rw [Real.log_pow]; norm_num,
          Real.exp_log (by positivity), hlogx_eq]
    rw [h6K, ← Real.exp_add]
    apply Real.exp_le_one_iff.mpr
    have h3u : (3 * u) ^ (1 / 4 : ℝ) ≤ 2 * u ^ (1 / 4 : ℝ) := by
      rw [Real.mul_rpow (by norm_num) hu_pos.le]
      have h3 : (3 : ℝ) ^ (1 / 4 : ℝ) ≤ 2 := by
        have h1 : (3 : ℝ) ≤ (2 : ℝ) ^ 4 := by norm_num
        have h2 := Real.rpow_le_rpow (by norm_num) h1 (by norm_num : (0 : ℝ) ≤ 1 / 4)
        rw [← Real.rpow_natCast (2 : ℝ) 4, ← Real.rpow_mul (by norm_num)] at h2
        norm_num at h2; exact h2
      exact mul_le_mul_of_nonneg_right h3 (Real.rpow_nonneg hu_pos.le _)
    have hlogu : Real.log u ≤ 4 * u ^ (1 / 4 : ℝ) := log_le_four_mul_rpow_quarter hu_pos
    have hu14 : u ^ (1 / 4 : ℝ) ≤ u / 1000 := by
      have hq : (1000 : ℝ) ≤ u ^ (1 / 4 : ℝ) := rpow_quarter_ge_of_ge (by norm_num) hu1000
      have h34 : u ^ (1 / 4 : ℝ) * u ^ (3 / 4 : ℝ) = u := by
        rw [← Real.rpow_add hu_pos]; norm_num
      have hle34 : (1000 : ℝ) ≤ u ^ (3 / 4 : ℝ) :=
        hq.trans (Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num))
      have h14nn : 0 ≤ u ^ (1 / 4 : ℝ) := Real.rpow_nonneg hu_pos.le _
      nlinarith only [h34, hle34, h14nn]
    have hC_le_u : Real.log (6 * (K' : ℝ)) + 61 + 500 ≤ u / 2 := by
      set A := Real.log (6 * (K' : ℝ)) + 61 + 500
      have hA_ge : (10 : ℝ) ≤ A := by
        have hK1 : (1 : ℝ) ≤ K' := by exact_mod_cast hK'
        have : (0 : ℝ) ≤ Real.log (6 * (K' : ℝ)) := Real.log_nonneg (by linarith)
        dsimp [A]; linarith
      have hA4 : 2 * A ≤ A ^ 4 := by
        have hA2 : 100 ≤ A ^ 2 := by nlinarith only [hA_ge]
        have hA3 : 1000 ≤ A ^ 3 := by nlinarith only [hA_ge, hA2]
        nlinarith only [hA_ge, hA2, hA3]
      linarith only [hu_ge, hA4]
    linarith only [h3u, hlogu, hu14, hC_le_u, hu_pos]
  have hprod_nn : 0 ≤ ∏ p ∈ primesLE y, (1 - (p : ℝ) ^ (-σ))⁻¹ := by
    apply Finset.prod_nonneg
    intro p hp
    have hp1 : (1 : ℝ) < p := by exact_mod_cast (prime_of_mem_primesLE hp).one_lt
    have hlt : (p : ℝ) ^ (-σ) < 1 := Real.rpow_lt_one_of_one_lt_of_neg hp1 (by linarith)
    exact inv_nonneg.mpr (by linarith)
  calc 2 * (Sm.card : ℝ)
      ≤ 2 * (((r + 1 : ℕ) : ℝ) ^ σ * ∏ p ∈ primesLE y, (1 - (p : ℝ) ^ (-σ))⁻¹) :=
        mul_le_mul_of_nonneg_left hrankin (by norm_num)
    _ ≤ 2 * ((3 * (K' : ℝ) * x * Real.exp (-u)) * Real.exp (60 + 192 * (3 * u) ^ (1 / 4 : ℝ))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul hpow_le hprod_le hprod_nn (by positivity)) (by norm_num)
    _ = (6 * (K' : ℝ) * Real.log x * Real.exp (60 + 192 * (3 * u) ^ (1 / 4 : ℝ) - u)) *
          ((x : ℝ) / Real.log x) := by
        have hne : Real.log (x : ℝ) ≠ 0 := hlogx_pos.ne'
        have hexp : Real.exp (-u) * Real.exp (60 + 192 * (3 * u) ^ (1 / 4 : ℝ)) =
            Real.exp (60 + 192 * (3 * u) ^ (1 / 4 : ℝ) - u) := by
          rw [← Real.exp_add]; congr 1; ring
        calc 2 * (3 * (K' : ℝ) * x * Real.exp (-u) * Real.exp (60 + 192 * (3 * u) ^ (1 / 4 : ℝ)))
            = 6 * (K' : ℝ) * x * (Real.exp (-u) * Real.exp (60 + 192 * (3 * u) ^ (1 / 4 : ℝ))) := by ring
          _ = 6 * (K' : ℝ) * x * Real.exp (60 + 192 * (3 * u) ^ (1 / 4 : ℝ) - u) := by rw [hexp]
          _ = (6 * (K' : ℝ) * Real.log x * Real.exp (60 + 192 * (3 * u) ^ (1 / 4 : ℝ) - u)) *
                ((x : ℝ) / Real.log x) := by field_simp [hne]
    _ ≤ 1 * ((x : ℝ) / Real.log x) :=
        mul_le_mul_of_nonneg_right hmain_exp (by positivity)
    _ = (x : ℝ) / Real.log x := one_mul _

private lemma sum_P2_ge_of_large {x K' : ℕ} (hK' : 1 ≤ K') (hx : 10 ^ 10 ≤ x)
    (U₀ : ℝ) (hU₀_ge : 1000 ≤ U₀)
    (hU1 : Real.exp (8 * (2 * Real.log (200 * (K' : ℝ) + 1)) + 10) ≤ U₀)
    (hU2 : (3000 * (K' : ℝ) + 100) * Real.exp (8 * (2 * Real.log (200 * (K' : ℝ) + 1)) + 10) ≤ U₀)
    (hu_ge : U₀ ^ 4 + 100 ≤ Real.sqrt (Real.log (x : ℝ))) :
    let w₂ := 1000 * K' * (Nat.log 2 x + 1)
    let y := ⌊Real.exp (Real.sqrt (Real.log (x : ℝ)))⌋₊
    2 * Real.log (200 * (K' : ℝ) + 1) ≤
      ∑ p ∈ (primesLE x).filter (fun p => w₂ < p ∧ p ≤ y), (1 / (p : ℝ)) := by
  intro w₂ y
  set C_gr : ℝ := 2 * Real.log (200 * (K' : ℝ) + 1)
  set u : ℝ := Real.sqrt (Real.log (x : ℝ))
  have hxpos : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
  have hlogx_eq : Real.log (x : ℝ) = u ^ 2 :=
    (Real.sq_sqrt (Real.log_nonneg (by exact_mod_cast (show 1 ≤ x by omega)))).symm
  have hU₀_2 : (1000000 : ℝ) ≤ U₀ ^ 2 := by nlinarith
  have hU₀_4 : (1000 : ℝ) ^ 4 ≤ U₀ ^ 4 := pow_le_pow_left₀ (by norm_num) hU₀_ge 4
  have hu_pos : 0 < u := by linarith [show (0 : ℝ) < (1000 : ℝ) ^ 4 by norm_num]
  have hu1000 : (1000 : ℝ) ≤ u := by linarith [show (1000 : ℝ) ≤ (1000 : ℝ) ^ 4 by norm_num]
  have hC_nn : 0 ≤ C_gr := by
    have hK1 : (1 : ℝ) ≤ K' := by exact_mod_cast hK'
    exact mul_nonneg (by norm_num) (Real.log_nonneg (by linarith))
  have hE_ge1 : (1 : ℝ) ≤ Real.exp (8 * C_gr) := Real.one_le_exp (by linarith)
  have hy_le : (y : ℝ) ≤ Real.exp u := Nat.floor_le (Real.exp_pos u).le
  have hy_ge_exp : Real.exp (u - 1) ≤ (y : ℝ) := by
    have h1 : Real.exp (u - 1) = Real.exp u / Real.exp 1 := Real.exp_sub u 1
    have he2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have hexp2 : (2 : ℝ) ≤ Real.exp u := by
      have h4 := pow_four_div_24_le_exp hu_pos.le
      have : (10 : ℝ) ^ 4 ≤ u ^ 4 := pow_le_pow_left₀ (by norm_num) (by linarith) 4
      linarith
    have h2 : Real.exp u / Real.exp 1 ≤ Real.exp u / 2 :=
      div_le_div_of_nonneg_left (Real.exp_pos u).le (by norm_num) he2
    linarith [Nat.lt_floor_add_one (Real.exp u)]
  have hy_ge1 : 1 ≤ y := by
    have : (1 : ℝ) ≤ (y : ℝ) := le_trans (Real.one_le_exp (by linarith)) hy_ge_exp
    exact_mod_cast this
  have hw₂_le_u2 : (w₂ : ℝ) ≤ 3000 * (K' : ℝ) * u ^ 2 := by
    have h1 : (Nat.log 2 x : ℝ) ≤ 2 * u ^ 2 := by
      rw [← hlogx_eq]; exact nat_log2_le_two_mul_log (by omega)
    have h2 : (w₂ : ℝ) = 1000 * (K' : ℝ) * ((Nat.log 2 x : ℝ) + 1) := by push_cast [w₂]; ring
    rw [h2]
    have hu2_ge1 : (1 : ℝ) ≤ u ^ 2 := by nlinarith only [hu1000]
    have hKnn : (0 : ℝ) ≤ K' := Nat.cast_nonneg _
    nlinarith only [h1, hu2_ge1, hKnn]
  have hy_le_x : y ≤ x := by
    have hleR : (y : ℝ) ≤ (x : ℝ) := by
      calc (y : ℝ) ≤ Real.exp u := hy_le
        _ ≤ Real.exp (u ^ 2) := Real.exp_le_exp.mpr (by nlinarith only [hu1000])
        _ = (x : ℝ) := by rw [← hlogx_eq, Real.exp_log hxpos]
    exact_mod_cast hleR
  set m₀ := max 9 (Nat.log 2 w₂ / 4 + 1)
  set m₁ := Nat.log 2 y / 4
  have hw2_lt_pow : w₂ < 2 ^ (4 * m₀) := by
    have h1 : w₂ < 2 ^ (Nat.log 2 w₂ + 1) := Nat.lt_pow_succ_log_self (by decide : 1 < 2) w₂
    have h2 : Nat.log 2 w₂ + 1 ≤ 4 * m₀ := by omega
    exact lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by decide) h2)
  have hpow_le_y : 2 ^ (4 * m₁) ≤ y := by
    have h1 : 2 ^ (Nat.log 2 y) ≤ y := Nat.pow_log_le_self 2 (by omega)
    have h2 : 4 * m₁ ≤ Nat.log 2 y := Nat.mul_div_le _ _
    exact (Nat.pow_le_pow_right (by decide) h2).trans h1
  have hlogK_nn : 0 ≤ Real.log (3000 * (K' : ℝ) + 100) :=
    Real.log_nonneg (by have : (0 : ℝ) ≤ K' := Nat.cast_nonneg _; linarith)
  have hm₀_le : (m₀ : ℝ) + 1 ≤ 12 + (1 / 2 : ℝ) * Real.log (3000 * (K' : ℝ) + 100) + 4 * u ^ (1 / 4 : ℝ) := by
    have hw2_pos : 1 ≤ w₂ := by dsimp [w₂]; nlinarith
    have h1 : (Nat.log 2 w₂ : ℝ) ≤ 2 * Real.log (w₂ : ℝ) := nat_log2_le_two_mul_log hw2_pos
    have h2 : Real.log (w₂ : ℝ) ≤ Real.log ((3000 * (K' : ℝ) + 100) * u ^ 2) :=
      Real.log_le_log (by exact_mod_cast hw2_pos) (by nlinarith only [hw₂_le_u2, hu1000])
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow] at h2
    push_cast at h2
    have hlogu : Real.log u ≤ 4 * u ^ (1 / 4 : ℝ) := log_le_four_mul_rpow_quarter hu_pos
    have hdiv : ((Nat.log 2 w₂ / 4 : ℕ) : ℝ) ≤ (Nat.log 2 w₂ : ℝ) / 4 := by
      have : (Nat.log 2 w₂ / 4) * 4 ≤ Nat.log 2 w₂ := Nat.div_mul_le_self _ 4
      have : ((Nat.log 2 w₂ / 4 : ℕ) : ℝ) * 4 ≤ (Nat.log 2 w₂ : ℝ) := by exact_mod_cast this
      linarith
    rcases le_max_iff.mp (le_rfl : m₀ ≤ max 9 (Nat.log 2 w₂ / 4 + 1)) with h9 | hlog
    · have h9R : (m₀ : ℝ) ≤ 9 := by exact_mod_cast h9
      have hnn2 : 0 ≤ u ^ (1 / 4 : ℝ) := Real.rpow_nonneg hu_pos.le _
      linarith only [h9R, hlogK_nn, hnn2]
    · have hR : (m₀ : ℝ) ≤ ((Nat.log 2 w₂ / 4 : ℕ) : ℝ) + 1 := by exact_mod_cast hlog
      linarith only [hR, hdiv, h1, h2, hlogu]
  have hm₁_ge : u / 4 - 2 ≤ (m₁ : ℝ) + 1 := by
    have hlog_y_ge : u - 1 ≤ Real.log (y : ℝ) := by
      calc u - 1 = Real.log (Real.exp (u - 1)) := (Real.log_exp _).symm
        _ ≤ Real.log (y : ℝ) := Real.log_le_log (Real.exp_pos _) hy_ge_exp
    have hnatlog : u - 2 ≤ (Nat.log 2 y : ℝ) := by
      have := log_le_nat_log2_add_one hy_ge1; linarith
    have hdiv : (Nat.log 2 y : ℝ) / 4 - 1 ≤ ((Nat.log 2 y / 4 : ℕ) : ℝ) := by
      have : Nat.log 2 y < 4 * (Nat.log 2 y / 4 + 1) := by omega
      have : (Nat.log 2 y : ℝ) < 4 * (((Nat.log 2 y / 4 : ℕ) : ℝ) + 1) := by exact_mod_cast this
      linarith
    linarith
  have hratio_ge : Real.exp (8 * C_gr) ≤ ((m₁ : ℝ) + 1) / ((m₀ : ℝ) + 1) := by
    rw [le_div_iff₀ (by positivity)]
    have hlogK : Real.log (3000 * (K' : ℝ) + 100) ≤ 3000 * (K' : ℝ) + 100 := by
      linarith [Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < 3000 * (K' : ℝ) + 100)]
    have hE10 : Real.exp (8 * C_gr) * 1000 ≤ Real.exp (8 * C_gr + 10) := by
      rw [Real.exp_add]
      have h10 : (1000 : ℝ) ≤ Real.exp 10 := by
        have h5 := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 10) 6
        simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h5
        norm_num at h5; linarith
      exact mul_le_mul_of_nonneg_left h10 (Real.exp_pos _).le
    have hE_le_U₀ : Real.exp (8 * C_gr) * 1000 ≤ U₀ := hE10.trans hU1
    have hu14_le : u ^ (1 / 4 : ℝ) ≤ u / (U₀ ^ 3) := by
      have hq : U₀ ≤ u ^ (1 / 4 : ℝ) := rpow_quarter_ge_of_ge (by linarith only [hU₀_ge]) (by linarith only [hu_ge])
      have h34 : u ^ (1 / 4 : ℝ) * u ^ (3 / 4 : ℝ) = u := by
        rw [← Real.rpow_add hu_pos]; norm_num
      have hpow3 : U₀ ^ 3 ≤ u ^ (3 / 4 : ℝ) := by
        calc U₀ ^ 3 = (U₀ ^ 1) ^ 3 := by ring
          _ ≤ (u ^ (1 / 4 : ℝ)) ^ 3 := by rw [pow_one]; exact pow_le_pow_left₀ (by linarith only [hU₀_ge]) hq 3
          _ = u ^ (3 / 4 : ℝ) := by
              rw [← Real.rpow_natCast (u ^ (1 / 4 : ℝ)) 3, ← Real.rpow_mul hu_pos.le]; norm_num
      rw [le_div_iff₀ (by positivity)]
      have hnn : 0 ≤ u ^ (1 / 4 : ℝ) := Real.rpow_nonneg hu_pos.le _
      nlinarith only [h34, hpow3, hnn]
    have hterm1 : Real.exp (8 * C_gr) * 12 ≤ U₀ := by linarith only [hE_le_U₀, hE_ge1]
    have hterm2 : Real.exp (8 * C_gr) * ((1 / 2 : ℝ) * Real.log (3000 * (K' : ℝ) + 100)) ≤ U₀ := by
      have h1 : Real.exp (8 * C_gr) ≤ Real.exp (8 * C_gr + 10) := Real.exp_le_exp.mpr (by linarith)
      have h2 : Real.exp (8 * C_gr) * ((1 / 2 : ℝ) * Real.log (3000 * (K' : ℝ) + 100)) ≤
          Real.exp (8 * C_gr + 10) * (3000 * (K' : ℝ) + 100) := by
        nlinarith only [h1, hlogK, hlogK_nn, hE_ge1]
      linarith only [h2, hU2]
    have hterm3 : Real.exp (8 * C_gr) * (4 * u ^ (1 / 4 : ℝ)) ≤ u / 10 := by
      have h1 : Real.exp (8 * C_gr) ≤ U₀ := by linarith only [hE_le_U₀, hE_ge1]
      have h2 : 4 * Real.exp (8 * C_gr) * (u / U₀ ^ 3) = (4 * Real.exp (8 * C_gr) / U₀ ^ 3) * u := by ring
      have h3 : 4 * Real.exp (8 * C_gr) / U₀ ^ 3 ≤ 1 / 10 := by
        rw [div_le_iff₀ (by positivity)]
        have hU3 : 40 * U₀ ≤ U₀ ^ 3 := by nlinarith only [hU₀_ge, hU₀_2]
        linarith only [h1, hU3]
      have h4 : Real.exp (8 * C_gr) * (4 * u ^ (1 / 4 : ℝ)) ≤ 4 * Real.exp (8 * C_gr) * (u / U₀ ^ 3) := by
        have := mul_le_mul_of_nonneg_left hu14_le (show 0 ≤ 4 * Real.exp (8 * C_gr) by positivity)
        linarith only [this]
      nlinarith only [h2, h3, h4, hu_pos]
    have hU₀_le_u : 100 * U₀ ≤ u := by
      have h2 : 1000 * U₀ ≤ U₀ ^ 2 := by nlinarith only [hU₀_ge]
      have h3 : U₀ ^ 2 ≤ U₀ ^ 4 := by nlinarith only [hU₀_2]
      linarith only [h2, h3, hu_ge, hU₀_ge]
    have hexp_mul := mul_le_mul_of_nonneg_left hm₀_le (Real.exp_pos (8 * C_gr)).le
    linarith only [hexp_mul, hterm1, hterm2, hterm3, hU₀_le_u, hm₁_ge, hu1000]
  have hm_le : m₀ ≤ m₁ := by
    have h2 := (le_div_iff₀ (by positivity : (0 : ℝ) < (m₀ : ℝ) + 1)).mp hratio_ge
    have hm0_pos : (0 : ℝ) < (m₀ : ℝ) + 1 := by positivity
    have h3 : (m₀ : ℝ) ≤ (m₁ : ℝ) := by nlinarith only [h2, hE_ge1, hm0_pos]
    exact_mod_cast h3
  have hsub : (primesLE (2 ^ (4 * m₁))).filter (fun p => 2 ^ (4 * m₀) < p) ⊆
      (primesLE x).filter (fun p => w₂ < p ∧ p ≤ y) := by
    intro p hp
    rw [Finset.mem_filter, mem_primesLE] at hp ⊢
    refine ⟨⟨hp.1.1.trans (hpow_le_y.trans hy_le_x), hp.1.2⟩,
      lt_trans hw2_lt_pow hp.2, hp.1.1.trans hpow_le_y⟩
  have hdyad := sum_inv_primes_ge (le_max_left 9 _) hm_le
  have hlog_ge : 8 * C_gr ≤ Real.log (((m₁ : ℝ) + 1) / ((m₀ : ℝ) + 1)) := by
    calc 8 * C_gr = Real.log (Real.exp (8 * C_gr)) := (Real.log_exp _).symm
      _ ≤ Real.log (((m₁ : ℝ) + 1) / ((m₀ : ℝ) + 1)) :=
          Real.log_le_log (Real.exp_pos _) hratio_ge
  calc C_gr = (1 / 8 : ℝ) * (8 * C_gr) := by ring
    _ ≤ (1 / 8 : ℝ) * Real.log (((m₁ : ℝ) + 1) / ((m₀ : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_left hlog_ge (by norm_num)
    _ ≤ ∑ p ∈ (primesLE (2 ^ (4 * m₁))).filter (fun p => 2 ^ (4 * m₀) < p), (1 / (p : ℝ)) := hdyad
    _ ≤ ∑ p ∈ (primesLE x).filter (fun p => w₂ < p ∧ p ≤ y), (1 / (p : ℝ)) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)

private lemma exists_covering_of_bounds {x K' w₂ y : ℕ}
    (hK' : 1 ≤ K') (hx : 10 ^ 10 ≤ x) (hxK : 200 * K' + 100 ≤ x)
    (hw₁ : 30 * K' ≤ w₂) (hw₂y : w₂ < y) (hyx : y ≤ x / 10)
    (hSm_bound : 2 * (((Finset.Icc 1 (2 * K' * x + 1)).filter
      (fun m => ∀ p ∈ m.primeFactors, p ≤ y)).card : ℝ) ≤ (x : ℝ) / Real.log x)
    (hpi_x : (Nat.primeCounting (2 * K' * x + 1) : ℝ) ≤
      (Real.log 4 + 1) * ((2 * K' * x + 1 : ℕ) : ℝ) / Real.log ((2 * K' * x + 1 : ℕ) : ℝ))
    (hsum_P2 : 2 * Real.log (200 * (K' : ℝ) + 1) ≤
      ∑ p ∈ (primesLE x).filter (fun p => w₂ < p ∧ p ≤ y), (1 / (p : ℝ)))
    (hw₂_eq : w₂ = 1000 * K' * (Nat.log 2 x + 1)) :
    let q := primorial x
    let r := 2 * K' * x
    r ≤ q →
    ∃ a < q, a.Coprime q ∧
      ∀ d, 0 < d → d ≤ r → ¬ (a + d).Coprime q ∧ ¬ (a + (q - d)).Coprime q := by
  intro q r hrq
  have hxpos : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
  have hlogx_pos : 0 < Real.log (x : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < x by omega))
  set P₁ := (primesLE x).filter (fun p => p ≤ w₂)
  set P₂ := (primesLE x).filter (fun p => w₂ < p ∧ p ≤ y)
  set P₃ := (primesLE x).filter (fun p => y < p ∧ p ≤ x / 10)
  set P₄ := (primesLE x).filter (fun p => x / 10 < p)
  set D₀ : Finset ℤ := (Finset.Icc (-(r : ℤ)) (r : ℤ)).erase 0
  set S₁ := D₀.filter (fun t => ∀ p ∈ P₁ ∪ P₃, ¬ (p : ℤ) ∣ 1 + t)
  have hS1_bound : (S₁.card : ℝ) ≤ 20 * (K' : ℝ) * x / Real.log x := by
    have hsplit := S1_card_le hK' (by omega) hw₁ hw₂y.le hyx
    have hPi_bound : 2 * ((primesLE (r + 1)).card : ℝ) ≤ 19 * (K' : ℝ) * x / Real.log x := by
      rw [primesLE_card_eq_primeCounting]
      have hlog4 : Real.log 4 + 1 ≤ 3 := by
        have : Real.log 4 = 2 * Real.log 2 := by
          rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
        linarith [Real.log_two_lt_d9]
      have hr1_le : ((2 * K' * x + 1 : ℕ) : ℝ) ≤ 3 * (K' : ℝ) * x := by
        have : 2 * K' * x + 1 ≤ 3 * K' * x := by nlinarith
        exact_mod_cast this
      have hlog_ge : Real.log (x : ℝ) ≤ Real.log ((2 * K' * x + 1 : ℕ) : ℝ) := by
        apply Real.log_le_log hxpos
        have : x ≤ 2 * K' * x + 1 := by nlinarith
        exact_mod_cast this
      calc 2 * (Nat.primeCounting (r + 1) : ℝ)
          ≤ 2 * ((Real.log 4 + 1) * ((2 * K' * x + 1 : ℕ) : ℝ) / Real.log ((2 * K' * x + 1 : ℕ) : ℝ)) :=
            mul_le_mul_of_nonneg_left hpi_x (by norm_num)
        _ ≤ 2 * (3 * (3 * (K' : ℝ) * x) / Real.log (x : ℝ)) := by gcongr
        _ = 18 * (K' : ℝ) * x / Real.log (x : ℝ) := by ring
        _ ≤ 19 * (K' : ℝ) * x / Real.log (x : ℝ) := by gcongr; norm_num
    have hsplitR : (S₁.card : ℝ) ≤
        2 * (((Finset.Icc 1 (r + 1)).filter (fun m => ∀ p ∈ m.primeFactors, p ≤ y)).card : ℝ) +
        2 * ((primesLE (r + 1)).card : ℝ) := by exact_mod_cast hsplit
    have hK1 : (1 : ℝ) ≤ K' := by exact_mod_cast hK'
    have hdiv1 : (x : ℝ) / Real.log x ≤ (K' : ℝ) * x / Real.log x := by gcongr; nlinarith
    have hsum_eq : (K' : ℝ) * x / Real.log x + 19 * (K' : ℝ) * x / Real.log x =
        20 * (K' : ℝ) * x / Real.log x := by ring
    linarith only [hsplitR, hSm_bound, hPi_bound, hdiv1, hsum_eq]
  set T : ℝ := 0.1 * x / Real.log x
  have hT_pos : 0 < T := by positivity
  have hdiv_P2 : ∀ p ∈ P₂, ((D₀.filter (fun t => (p : ℤ) ∣ t)).card : ℝ) ≤ T / 2 := by
    intro p hp
    have hpp := prime_of_mem_primesLE (Finset.mem_filter.mp hp).1
    have hpgt : w₂ < p := (Finset.mem_filter.mp hp).2.1
    have h1 := card_filter_dvd_D0_le (r := r) hpp.pos
    have h2 : ((2 * (r / p) : ℕ) : ℝ) ≤ 2 * (r : ℝ) / (p : ℝ) := by
      have : (r / p) * p ≤ r := Nat.div_mul_le_self r p
      have hR : ((r / p : ℕ) : ℝ) * (p : ℝ) ≤ (r : ℝ) := by exact_mod_cast this
      push_cast
      rw [le_div_iff₀ (by exact_mod_cast hpp.pos)]
      linarith
    have h1R : ((D₀.filter (fun t => (p : ℤ) ∣ t)).card : ℝ) ≤ 2 * (r : ℝ) / (p : ℝ) :=
      le_trans (by exact_mod_cast h1) h2
    have hpw : 1000 * (K' : ℝ) * Real.log (x : ℝ) ≤ (p : ℝ) := by
      have hlogx_le := log_le_nat_log2_add_one (show 1 ≤ x by omega)
      have hwR : (w₂ : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpgt.le
      have hw_eq : (w₂ : ℝ) = 1000 * (K' : ℝ) * ((Nat.log 2 x : ℝ) + 1) := by
        rw [hw₂_eq]; push_cast; ring
      have hKnn : (0 : ℝ) ≤ K' := Nat.cast_nonneg _
      nlinarith
    have hrR : (r : ℝ) = 2 * (K' : ℝ) * x := by push_cast [r]; ring
    calc ((D₀.filter (fun t => (p : ℤ) ∣ t)).card : ℝ)
        ≤ 2 * (2 * (K' : ℝ) * x) / (p : ℝ) := by rw [← hrR]; exact h1R
      _ ≤ 2 * (2 * (K' : ℝ) * x) / (1000 * (K' : ℝ) * Real.log x) := by gcongr
      _ = 0.004 * (x / Real.log x) := by
          have hKne : (K' : ℝ) ≠ 0 := by exact_mod_cast (show K' ≠ 0 by omega)
          field_simp [hKne]; ring
      _ ≤ T / 2 := by
          have hT2 : T / 2 = 0.05 * ((x : ℝ) / Real.log x) := by dsimp [T]; ring
          have hpos : (0 : ℝ) < (x : ℝ) / Real.log x := by positivity
          linarith only [hT2, hpos]
  obtain ⟨f₂, hf₂, hS2_max⟩ := greedy_sieve
    (Finset.filter_subset (fun t => ∀ p ∈ P₁ ∪ P₃, ¬ (p : ℤ) ∣ 1 + t) D₀) hT_pos.le P₂
    (fun p hp => prime_of_mem_primesLE (Finset.mem_filter.mp hp).1) hdiv_P2
  set S₂ := S₁.filter (fun t => ∀ p ∈ P₂, ¬ (p : ℤ) ∣ (f₂ p : ℤ) + t)
  have hS2_le_T : (S₂.card : ℝ) ≤ T := by
    have hright : (S₁.card : ℝ) * Real.exp (-(1 / 2 : ℝ) * ∑ p ∈ P₂, (1 / (p : ℝ))) ≤ T := by
      have hexp : Real.exp (-(1 / 2 : ℝ) * ∑ p ∈ P₂, (1 / (p : ℝ))) ≤ (200 * (K' : ℝ) + 1)⁻¹ := by
        calc Real.exp (-(1 / 2 : ℝ) * ∑ p ∈ P₂, (1 / (p : ℝ)))
            ≤ Real.exp (-(1 / 2 : ℝ) * (2 * Real.log (200 * (K' : ℝ) + 1))) :=
              Real.exp_le_exp.mpr (by linarith)
          _ = Real.exp (-Real.log (200 * (K' : ℝ) + 1)) := by congr 1; ring
          _ = (200 * (K' : ℝ) + 1)⁻¹ := by rw [Real.exp_neg, Real.exp_log (by positivity)]
      have hS1_T : (S₁.card : ℝ) ≤ (200 * (K' : ℝ) + 1) * T := by
        have : 20 * (K' : ℝ) * x / Real.log x = 200 * (K' : ℝ) * T := by dsimp [T]; ring
        linarith
      calc (S₁.card : ℝ) * Real.exp (-(1 / 2 : ℝ) * ∑ p ∈ P₂, (1 / (p : ℝ)))
          ≤ ((200 * (K' : ℝ) + 1) * T) * (200 * (K' : ℝ) + 1)⁻¹ :=
            mul_le_mul hS1_T hexp (Real.exp_pos _).le (by positivity)
        _ = T := by
            have hne : (200 * (K' : ℝ) + 1) ≠ 0 := by positivity
            field_simp [hne]
    exact hS2_max.trans (max_le le_rfl hright)
  have hP4_card := card_P4_ge hx
  have hS2_lt_P4 : S₂.card + 1 ≤ P₄.card := by
    have hR : (S₂.card : ℝ) + 1 ≤ (P₄.card : ℝ) := by
      have h1 : (1 : ℝ) ≤ 0.3 * x / Real.log x := by
        rw [le_div_iff₀ hlogx_pos]
        have hlog := log_le_four_mul_rpow_quarter hxpos
        have hq : (200 : ℝ) ≤ (x : ℝ) ^ (1 / 4 : ℝ) :=
          rpow_quarter_ge_of_ge (by norm_num) (by
            have : (10 ^ 10 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
            linarith)
        have h34 : (x : ℝ) ^ (1 / 4 : ℝ) * (x : ℝ) ^ (3 / 4 : ℝ) = (x : ℝ) := by
          rw [← Real.rpow_add hxpos]; norm_num
        have h34ge : (200 : ℝ) ≤ (x : ℝ) ^ (3 / 4 : ℝ) :=
          hq.trans (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1 ≤ x by omega)) (by norm_num))
        have h14nn : 0 ≤ (x : ℝ) ^ (1 / 4 : ℝ) := Real.rpow_nonneg hxpos.le _
        nlinarith only [hlog, h34, h34ge, h14nn]
      have hT_eq : T + 0.3 * x / Real.log x = 0.4 * x / Real.log x := by dsimp [T]; ring
      linarith only [hS2_le_T, h1, hT_eq, hP4_card]
    exact_mod_cast hR
  have hdiv1_P4 : ∀ t ∈ S₂, (P₄.filter (fun p : ℕ => (p : ℤ) ∣ t)).card ≤ 1 := by
    intro t ht
    have htD : t ∈ D₀ := (Finset.filter_subset _ _) ((Finset.filter_subset _ _) ht)
    have ht0 : t ≠ 0 := (Finset.mem_erase.mp htD).1
    have hIcc := Finset.mem_Icc.mp (Finset.mem_erase.mp htD).2
    have htr : t.natAbs ≤ r := by omega
    refine Finset.card_le_one.mpr ?_
    intro p₁ hp₁ p₂ hp₂
    by_contra hne
    have hp₁m := (Finset.mem_filter.mp hp₁).1
    have hp₂m := (Finset.mem_filter.mp hp₂).1
    have hp₁p := prime_of_mem_primesLE (Finset.mem_filter.mp hp₁m).1
    have hp₂p := prime_of_mem_primesLE (Finset.mem_filter.mp hp₂m).1
    have hp₁gt : x / 10 < p₁ := (Finset.mem_filter.mp hp₁m).2
    have hp₂gt : x / 10 < p₂ := (Finset.mem_filter.mp hp₂m).2
    have hd₁ : p₁ ∣ t.natAbs := Int.natCast_dvd.mp (Finset.mem_filter.mp hp₁).2
    have hd₂ : p₂ ∣ t.natAbs := Int.natCast_dvd.mp (Finset.mem_filter.mp hp₂).2
    have hcop : p₁.Coprime p₂ := (Nat.coprime_primes hp₁p hp₂p).mpr hne
    have hmul_dvd : p₁ * p₂ ∣ t.natAbs := hcop.mul_dvd_of_dvd_of_dvd hd₁ hd₂
    have hmul_le : p₁ * p₂ ≤ r :=
      (Nat.le_of_dvd (Int.natAbs_pos.mpr ht0) hmul_dvd).trans htr
    have h10p₁ : x < 10 * p₁ := by omega
    have h10p₂ : x < 10 * p₂ := by omega
    have h1 : x * x < 100 * (p₁ * p₂) := by nlinarith
    have h2 : 100 * r ≤ x * x := by dsimp [r]; nlinarith
    omega
  obtain ⟨used, hused_sub, _, f₄, hf₄, hcov₄⟩ := match_P4 P₄
    (fun p hp => prime_of_mem_primesLE (Finset.mem_filter.mp hp).1) S₂ hS2_lt_P4 hdiv1_P4
  let res : ℕ → ℕ := fun p =>
    if p ∈ P₂ then f₂ p else if p ∈ used then f₄ p else 1
  have hres_bounds : ∀ p ∈ primesLE x, 1 ≤ res p ∧ res p < p := by
    intro p hp
    have hpp := prime_of_mem_primesLE hp
    dsimp only [res]
    split_ifs with h1 h2
    · exact hf₂ p h1
    · exact hf₄ p h2
    · exact ⟨le_rfl, hpp.one_lt⟩
  have hpp_nz : ∀ p ∈ primesLE x, p ≠ 0 := fun p hp => (prime_of_mem_primesLE hp).ne_zero
  have hpp_cop : Set.Pairwise (primesLE x : Set ℕ) (Function.onFun Nat.Coprime id) := by
    intro p hp q hq hpq
    exact (Nat.coprime_primes (prime_of_mem_primesLE hp) (prime_of_mem_primesLE hq)).mpr hpq
  let crt := Nat.chineseRemainderOfFinset res id (primesLE x) hpp_nz hpp_cop
  let a : ℕ := crt.val
  have ha_lt : a < q := by
    have := Nat.chineseRemainderOfFinset_lt_prod (a := res) (s := id) hpp_nz hpp_cop
    simpa [a, crt, q, primorial_eq_prod_primesLE] using this
  have ha_mod : ∀ p ∈ primesLE x, a ≡ res p [MOD p] := crt.property
  have ha_cop : a.Coprime q := by
    dsimp only [q]
    rw [primorial_eq_prod_primesLE, Nat.coprime_prod_right_iff]
    intro p hp
    have hpp := prime_of_mem_primesLE hp
    have hb := hres_bounds p hp
    have hrcop : (res p).Coprime p :=
      (hpp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt hb.1 hb.2)).symm
    exact (ha_mod p hp).gcd_eq.trans hrcop
  have hcover_D0 : ∀ t ∈ D₀, ∃ p ∈ primesLE x, (p : ℤ) ∣ (a : ℤ) + t := by
    intro t ht
    have h_res_to_a : ∀ p ∈ primesLE x, (p : ℤ) ∣ (res p : ℤ) + t → (p : ℤ) ∣ (a : ℤ) + t := by
      intro p hp hdvd
      have hmod : (p : ℤ) ∣ (a : ℤ) - (res p : ℤ) :=
        Int.modEq_iff_dvd.mp (Int.natCast_modEq_iff.mpr (ha_mod p hp).symm)
      have heq : (a : ℤ) + t = ((a : ℤ) - (res p : ℤ)) + ((res p : ℤ) + t) := by ring
      rw [heq]
      exact dvd_add hmod hdvd
    by_cases h1 : t ∈ S₁
    · by_cases h2 : t ∈ S₂
      · obtain ⟨p, hp_u, hdvd⟩ := hcov₄ t h2
        have hp_P4 : p ∈ P₄ := hused_sub hp_u
        have hp_le : p ∈ primesLE x := (Finset.mem_filter.mp hp_P4).1
        have hp_not_P2 : p ∉ P₂ := by
          intro hP2
          have hgt : x / 10 < p := (Finset.mem_filter.mp hp_P4).2
          have hle : p ≤ y := (Finset.mem_filter.mp hP2).2.2
          omega
        have hres_eq : res p = f₄ p := by dsimp [res]; rw [if_neg hp_not_P2, if_pos hp_u]
        exact ⟨p, hp_le, h_res_to_a p hp_le (by rwa [hres_eq])⟩
      · have hnot : ¬ (∀ p ∈ P₂, ¬ (p : ℤ) ∣ (f₂ p : ℤ) + t) := fun hall =>
          h2 (Finset.mem_filter.mpr ⟨h1, hall⟩)
        push Not at hnot
        obtain ⟨p, hp_P2, hdvd⟩ := hnot
        have hp_le : p ∈ primesLE x := (Finset.mem_filter.mp hp_P2).1
        have hres_eq : res p = f₂ p := by dsimp [res]; rw [if_pos hp_P2]
        exact ⟨p, hp_le, h_res_to_a p hp_le (by rwa [hres_eq])⟩
    · have hnot : ¬ (∀ p ∈ P₁ ∪ P₃, ¬ (p : ℤ) ∣ 1 + t) := fun hall =>
        h1 (Finset.mem_filter.mpr ⟨ht, hall⟩)
      push Not at hnot
      obtain ⟨p, hp_13, hdvd⟩ := hnot
      have hp_le : p ∈ primesLE x := by
        rcases Finset.mem_union.mp hp_13 with hP1 | hP3
        · exact (Finset.mem_filter.mp hP1).1
        · exact (Finset.mem_filter.mp hP3).1
      have hp_not_P2 : p ∉ P₂ := by
        intro hP2
        have hgt := (Finset.mem_filter.mp hP2).2.1
        have hle := (Finset.mem_filter.mp hP2).2.2
        rcases Finset.mem_union.mp hp_13 with hP1 | hP3
        · have := (Finset.mem_filter.mp hP1).2; omega
        · have := (Finset.mem_filter.mp hP3).2.1; omega
      have hp_not_used : p ∉ used := by
        intro hu
        have hgt : x / 10 < p := (Finset.mem_filter.mp (hused_sub hu)).2
        rcases Finset.mem_union.mp hp_13 with hP1 | hP3
        · have := (Finset.mem_filter.mp hP1).2; omega
        · have := (Finset.mem_filter.mp hP3).2.2; omega
      have hres_eq : res p = 1 := by dsimp [res]; rw [if_neg hp_not_P2, if_neg hp_not_used]
      exact ⟨p, hp_le, h_res_to_a p hp_le (by simpa [hres_eq] using hdvd)⟩
  refine ⟨a, ha_lt, ha_cop, ?_⟩
  intro d hd0 hdr
  constructor
  · have ht : (d : ℤ) ∈ D₀ := by
      rw [Finset.mem_erase, Finset.mem_Icc]; omega
    obtain ⟨p, hp, hdvd⟩ := hcover_D0 (d : ℤ) ht
    have hpp := prime_of_mem_primesLE hp
    have hdvdN : p ∣ a + d := by exact_mod_cast hdvd
    have hpq : p ∣ q := hpp.dvd_primorial_iff.mpr (le_of_mem_primesLE hp)
    intro hcop
    exact hpp.not_dvd_one (hcop ▸ Nat.dvd_gcd hdvdN hpq)
  · have ht : -(d : ℤ) ∈ D₀ := by
      rw [Finset.mem_erase, Finset.mem_Icc]; omega
    obtain ⟨p, hp, hdvd⟩ := hcover_D0 (-(d : ℤ)) ht
    have hpp := prime_of_mem_primesLE hp
    have hpq : p ∣ q := hpp.dvd_primorial_iff.mpr (le_of_mem_primesLE hp)
    have hdvd_shift : (p : ℤ) ∣ ((a + (q - d) : ℕ) : ℤ) := by
      have heq : ((a + (q - d) : ℕ) : ℤ) = ((a : ℤ) + -(d : ℤ)) + (q : ℤ) := by omega
      rw [heq]
      exact dvd_add hdvd (Int.natCast_dvd_natCast.mpr hpq)
    have hdvdN : p ∣ a + (q - d) := Int.natCast_dvd_natCast.mp hdvd_shift
    intro hcop
    exact hpp.not_dvd_one (hcop ▸ Nat.dvd_gcd hdvdN hpq)

private lemma eventually_H1_witness (K' Q : ℕ) (hK' : 1 ≤ K') :
    ∀ᶠ x : ℕ in atTop,
      let q := primorial x
      let r := 2 * K' * x
      Q ≤ q ∧ r ≤ q ∧ (K' : ℝ) * Real.log q ≤ r ∧
      ∃ a < q, a.Coprime q ∧
        ∀ d, 0 < d → d ≤ r → ¬ (a + d).Coprime q ∧ ¬ (a + (q - d)).Coprime q := by
  have hpi := Chebyshev.eventually_primeCounting_le (by norm_num : (0 : ℝ) < 1)
  have hpi_nat : ∀ᶠ x : ℕ in atTop,
      (Nat.primeCounting (2 * K' * x + 1) : ℝ) ≤
        (Real.log 4 + 1) * ((2 * K' * x + 1 : ℕ) : ℝ) / Real.log ((2 * K' * x + 1 : ℕ) : ℝ) := by
    have htend : Tendsto (fun x : ℕ => ((2 * K' * x + 1 : ℕ) : ℝ)) atTop atTop := by
      refine tendsto_atTop_atTop.mpr (fun b => ?_)
      refine ⟨Nat.ceil (max b 0), fun n hn => ?_⟩
      have hb : b ≤ (Nat.ceil (max b 0) : ℝ) := (le_max_left b 0).trans (Nat.le_ceil _)
      have hnR : (Nat.ceil (max b 0) : ℝ) ≤ n := by exact_mod_cast hn
      push_cast
      have hK1 : (1 : ℝ) ≤ K' := by exact_mod_cast hK'
      nlinarith
    filter_upwards [htend.eventually hpi] with x hx
    rwa [Nat.floor_natCast] at hx
  have hu_tend : Tendsto (fun x : ℕ => Real.sqrt (Real.log (x : ℝ))) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  let C_sm : ℝ := Real.log (6 * (K' : ℝ)) + 61
  let C_gr : ℝ := 2 * Real.log (200 * (K' : ℝ) + 1)
  let U₀ : ℝ := max 1000 (max (C_sm + 500) (max (Real.exp (8 * C_gr + 10))
    ((3000 * (K' : ℝ) + 100) * Real.exp (8 * C_gr + 10))))
  filter_upwards [hpi_nat,
    eventually_ge_atTop (max (10 ^ 10) (max (16 * K' + 8 * Q + 100) (200 * K' + 100))),
    hu_tend.eventually (eventually_ge_atTop (U₀ ^ 4 + 100))] with x hpi_x hx_ge hu_ge
  have hx10 : 10 ^ 10 ≤ x := (le_max_left _ _).trans hx_ge
  have hxQ : 16 * K' + 8 * Q + 100 ≤ x :=
    ((le_max_left _ _).trans (le_max_right _ _)).trans hx_ge
  have hxK : 200 * K' + 100 ≤ x :=
    ((le_max_right _ _).trans (le_max_right _ _)).trans hx_ge
  have hxpos : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
  set u : ℝ := Real.sqrt (Real.log (x : ℝ))
  have hU₀_ge : (1000 : ℝ) ≤ U₀ := le_max_left _ _
  have hU_Csm : C_sm + 500 ≤ U₀ := le_trans (le_max_left _ _) (le_max_right _ _)
  have hU1 : Real.exp (8 * C_gr + 10) ≤ U₀ :=
    le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
  have hU2 : (3000 * (K' : ℝ) + 100) * Real.exp (8 * C_gr + 10) ≤ U₀ :=
    le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
  have hCsm_nn : 0 ≤ C_sm + 500 := by
    have hK1 : (1 : ℝ) ≤ K' := by exact_mod_cast hK'
    have : 0 ≤ Real.log (6 * (K' : ℝ)) := Real.log_nonneg (by linarith)
    dsimp [C_sm]; linarith
  have hu_Csm : (C_sm + 500) ^ 4 + 100 ≤ u := by
    have h4 := pow_le_pow_left₀ hCsm_nn hU_Csm 4
    linarith only [h4, hu_ge]
  have hu1000_4 : (1000 : ℝ) ^ 4 ≤ u := by
    have h4 := pow_le_pow_left₀ (by norm_num) hU₀_ge 4
    linarith only [h4, hu_ge]
  have hu_pos : 0 < u := by linarith only [hu1000_4, show (0 : ℝ) < (1000 : ℝ) ^ 4 by norm_num]
  have hu1000 : (1000 : ℝ) ≤ u := by linarith only [hu1000_4, show (1000 : ℝ) ≤ (1000 : ℝ) ^ 4 by norm_num]
  have hlogx_eq : Real.log (x : ℝ) = u ^ 2 :=
    (Real.sq_sqrt (Real.log_nonneg (by exact_mod_cast (show 1 ≤ x by omega)))).symm
  set q := primorial x
  set r := 2 * K' * x
  have hlogq : Real.log q = theta x := by
    have := Chebyshev.theta_eq_log_primorial (x : ℝ)
    simpa [q, Nat.floor_natCast] using this.symm
  have hth_lo : (0.6 : ℝ) * x ≤ theta x := theta_lower hx10
  have hq_ge_quad : (x : ℝ) ^ 2 / 8 ≤ (q : ℝ) := by
    have hqpos : (0 : ℝ) < q := by exact_mod_cast primorial_pos x
    have h1 : (x : ℝ) / 2 ≤ Real.log q := by rw [hlogq]; linarith only [hth_lo, hxpos]
    have h2 : Real.exp ((x : ℝ) / 2) ≤ q := by
      calc Real.exp ((x : ℝ) / 2) ≤ Real.exp (Real.log q) := Real.exp_le_exp.mpr h1
        _ = q := Real.exp_log hqpos
    have hquad := Real.quadratic_le_exp_of_nonneg (show (0 : ℝ) ≤ (x : ℝ) / 2 by positivity)
    linarith only [h2, hquad, hxpos]
  have hQq : Q ≤ q := by
    have hR : (Q : ℝ) ≤ (q : ℝ) := by
      have h1 : (8 * (Q : ℝ) + 16) ≤ (x : ℝ) := by exact_mod_cast (show 8 * Q + 16 ≤ x by omega)
      have hQnn : (0 : ℝ) ≤ Q := Nat.cast_nonneg _
      nlinarith only [h1, hq_ge_quad, hQnn]
    exact_mod_cast hR
  have hrq : r ≤ q := by
    have hR : (r : ℝ) ≤ (q : ℝ) := by
      have h1 : (16 * (K' : ℝ)) ≤ (x : ℝ) := by exact_mod_cast (show 16 * K' ≤ x by omega)
      have hrR : (r : ℝ) = 2 * (K' : ℝ) * x := by push_cast [r]; ring
      have hKnn : (0 : ℝ) ≤ K' := Nat.cast_nonneg _
      nlinarith only [h1, hrR, hq_ge_quad, hxpos, hKnn]
    exact_mod_cast hR
  have hKr : (K' : ℝ) * Real.log q ≤ r := by
    rw [hlogq]
    have h1 := Chebyshev.theta_le_log4_mul_x (show (0 : ℝ) ≤ x by positivity)
    have hlog4 : Real.log 4 ≤ 2 := by
      have : Real.log 4 = 2 * Real.log 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
      linarith [Real.log_two_lt_d9]
    have hrR : (r : ℝ) = 2 * (K' : ℝ) * x := by push_cast [r]; ring
    rw [hrR]
    have hth2 : theta x ≤ 2 * (x : ℝ) := by nlinarith only [h1, hlog4, hxpos]
    have hKnn : (0 : ℝ) ≤ K' := Nat.cast_nonneg _
    nlinarith only [hth2, hKnn]
  set w₂ : ℕ := 1000 * K' * (Nat.log 2 x + 1)
  set y : ℕ := ⌊Real.exp u⌋₊
  have hw₁_le : 30 * K' ≤ w₂ := by
    have : 1 ≤ Nat.log 2 x + 1 := Nat.succ_pos _
    dsimp [w₂]; nlinarith
  have hw₂_lt_y : w₂ < y := by
    have hw₂_le : (w₂ : ℝ) ≤ 3000 * (K' : ℝ) * u ^ 2 := by
      have h1 : (Nat.log 2 x : ℝ) ≤ 2 * u ^ 2 := by
        rw [← hlogx_eq]; exact nat_log2_le_two_mul_log (by omega)
      have h2 : (w₂ : ℝ) = 1000 * (K' : ℝ) * ((Nat.log 2 x : ℝ) + 1) := by push_cast [w₂]; ring
      rw [h2]
      have hu2_1 : (1 : ℝ) ≤ u ^ 2 := by nlinarith only [hu1000]
      have hKnn : (0 : ℝ) ≤ K' := Nat.cast_nonneg _
      nlinarith only [h1, hu2_1, hKnn]
    have hK_le_U₀ : 3000 * (K' : ℝ) + 100 ≤ U₀ := by
      have hK1 : (1 : ℝ) ≤ K' := by exact_mod_cast hK'
      have hE1 : (1 : ℝ) ≤ Real.exp (8 * C_gr + 10) := by
        apply Real.one_le_exp
        have hCnn : 0 ≤ C_gr := mul_nonneg (by norm_num) (Real.log_nonneg (by linarith only [hK1]))
        linarith only [hCnn]
      nlinarith only [hU2, hE1, hK1]
    have hy_u4 : u ^ 4 / 24 - 1 ≤ (y : ℝ) := by
      have h1 := pow_four_div_24_le_exp hu_pos.le
      have h2 := Nat.lt_floor_add_one (Real.exp u)
      linarith only [h1, h2]
    have hU₀_le_u : U₀ ≤ u := by
      have hU2' : 1000 * U₀ ≤ U₀ ^ 2 := by nlinarith only [hU₀_ge]
      have hU4' : U₀ ^ 2 ≤ U₀ ^ 4 := by nlinarith only [hU₀_ge, hU2']
      linarith only [hU₀_ge, hU2', hU4', hu_ge]
    have hU2_u : 100000 * U₀ < u ^ 2 := by
      have hU₀_2 : 100000 < u := by
        linarith only [hu1000_4, show (100000 : ℝ) < (1000 : ℝ) ^ 4 by norm_num]
      nlinarith only [hU₀_le_u, hU₀_ge, hU₀_2]
    have hltR : (w₂ : ℝ) < (y : ℝ) := by
      have hu4_eq : u ^ 4 = u ^ 2 * u ^ 2 := by ring
      have hmid : 3000 * (K' : ℝ) * 24 + 24 < u ^ 2 := by linarith only [hK_le_U₀, hU2_u]
      have hu2_pos : 0 < u ^ 2 := by positivity
      have hmul : (3000 * (K' : ℝ) * 24 + 24) * u ^ 2 < u ^ 2 * u ^ 2 :=
        mul_lt_mul_of_pos_right hmid hu2_pos
      have hu2_gt1 : 1 < u ^ 2 := by nlinarith only [hu1000]
      linarith only [hw₂_le, hy_u4, hu4_eq, hmul, hu2_gt1]
    exact_mod_cast hltR
  have hy_le_x10 : y ≤ x / 10 := by
    have hy_le_R : (y : ℝ) ≤ (x : ℝ) / 11 := by
      have h11 : Real.log 11 < 11 := by
        linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 11)]
      have h1 : Real.exp u ≤ Real.exp (u ^ 2 - Real.log 11) :=
        Real.exp_le_exp.mpr (by nlinarith only [hu1000, h11])
      rw [Real.exp_sub, ← hlogx_eq, Real.exp_log hxpos, Real.exp_log (by norm_num)] at h1
      exact (Nat.floor_le (Real.exp_pos u).le).trans h1
    by_contra! hgt
    have hR : ((x / 10 : ℕ) : ℝ) + 1 ≤ (y : ℝ) := by exact_mod_cast hgt
    have hdiv : (x : ℝ) / 10 < ((x / 10 : ℕ) : ℝ) + 1 := by
      have : x < 10 * (x / 10 + 1) := by omega
      have : (x : ℝ) < 10 * (((x / 10 : ℕ) : ℝ) + 1) := by exact_mod_cast this
      linarith
    linarith only [hy_le_R, hR, hdiv, hxpos]
  have hSm := smooth_bound_of_large hK' hx10 hu_Csm hu1000_4
  have hP2 := sum_P2_ge_of_large hK' hx10 U₀ hU₀_ge hU1 hU2 hu_ge
  exact ⟨hQq, hrq, hKr,
    exists_covering_of_bounds hK' hx10 hxK hw₁_le hw₂_lt_y hy_le_x10 hSm hpi_x hP2 rfl hrq⟩

end Erdos968R2H1

theorem OMA.solution : OMA.R_Erdos968_erdos_968_variants_infinite_increasingTriples_R2.H1 := by
  intro K Q
  let K' := max K 1
  have hK' : 1 ≤ K' := le_max_right K 1
  obtain ⟨x, hQq, hrq, hKr, a, ha_lt, ha_cop, hcov⟩ :=
    (Erdos968R2H1.eventually_H1_witness K' Q hK').exists
  refine ⟨primorial x, hQq, a, 2 * K' * x, ha_lt, ha_cop, hrq, ?_, hcov⟩
  have hKK' : (K : ℝ) ≤ K' := by exact_mod_cast le_max_left K 1
  have hlog_nn : 0 ≤ Real.log (primorial x : ℝ) :=
    Real.log_nonneg (by exact_mod_cast primorial_pos x)
  exact le_trans (mul_le_mul_of_nonneg_right hKK' hlog_nn) hKr
