import OMAReductions.R_Green86_green_86_R1
import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

-- Step Green86.green_86.R1.H1: hypothesis H1 of reduction Green86.green_86.R1
-- Credit: @keiichisince1986-bot
-- H1 := ∀ c : ℝ, 1 / 2 < c → ∃ n₀ : ℕ, ∀ A : Finset ℤ, n₀ ≤ A.card →     ∃ θ : ℝ, ∀ t : ℝ, (numInInterval A θ t : ℝ) ≤ (A.card : ℝ) ^ c

private lemma fract_diff_lt {θ t δ : ℝ} (hδ1 : δ ≤ 1) {a b : ℤ}
    (ha : Int.fract (θ * (a : ℝ) - t) < δ)
    (_hb : Int.fract (θ * (b : ℝ) - t) < δ)
    (hle : Int.fract (θ * (b : ℝ) - t) ≤ Int.fract (θ * (a : ℝ) - t)) :
    Int.fract (θ * ((a - b : ℤ) : ℝ)) < δ := by
  set ua := Int.fract (θ * (a : ℝ) - t)
  set ub := Int.fract (θ * (b : ℝ) - t)
  have h0 : 0 ≤ ub := Int.fract_nonneg _
  have heq : Int.fract (θ * ((a - b : ℤ) : ℝ)) = ua - ub := by
    rw [Int.fract_eq_iff]
    refine ⟨by linarith, by linarith, ⟨⌊θ * (a : ℝ) - t⌋ - ⌊θ * (b : ℝ) - t⌋, ?_⟩⟩
    simp only [ua, ub, Int.fract]
    push_cast
    ring
  linarith

private lemma sq_sub_le_two_mul_closePairs (A : Finset ℤ) (θ t : ℝ) (hn : 1 ≤ A.card) :
    Green86.numInInterval A θ t * (Green86.numInInterval A θ t - 1) ≤
      2 * (A.offDiag.filter (fun p =>
        Int.fract (θ * ((p.1 - p.2 : ℤ) : ℝ)) < 1 / (A.card : ℝ))).card := by
  set δ : ℝ := 1 / (A.card : ℝ)
  have hδ1 : δ ≤ 1 := div_le_one_of_le₀ (by exact_mod_cast hn) (by positivity)
  set S : Finset ℤ := A.filter (fun a => Int.fract (θ * (a : ℝ) - t) < δ)
  have hScard : S.card = Green86.numInInterval A θ t := rfl
  have hoff : S.offDiag.card = S.card * (S.card - 1) := by
    rw [Finset.offDiag_card]
    cases S.card with
    | zero => simp
    | succ m =>
      simp only [Nat.add_sub_cancel]
      have hm : (m + 1) * (m + 1) = (m + 1) * m + (m + 1) := by ring
      omega
  set W := A.offDiag.filter (fun p => Int.fract (θ * ((p.1 - p.2 : ℤ) : ℝ)) < δ)
  set B : Finset Bool := {false, true}
  have hB : B.card = 2 := by decide
  let φ : ℤ × ℤ → (ℤ × ℤ) × Bool := fun p =>
    if Int.fract (θ * (p.2 : ℝ) - t) ≤ Int.fract (θ * (p.1 : ℝ) - t) then
      (p, false)
    else
      ((p.2, p.1), true)
  have hle : S.offDiag.card ≤ (W ×ˢ B).card := by
    refine Finset.card_le_card_of_injOn φ (fun p hp => ?_) (fun p _ q _ hpq => ?_)
    · simp only [Finset.mem_coe, Finset.mem_offDiag, S, Finset.mem_filter] at hp
      rcases hp with ⟨⟨hp1A, hp1⟩, ⟨hp2A, hp2⟩, hne⟩
      dsimp only [φ]
      split_ifs with hcmp
      · exact Finset.mem_coe.mpr (Finset.mem_product.mpr ⟨Finset.mem_filter.mpr
          ⟨Finset.mem_offDiag.mpr ⟨hp1A, hp2A, hne⟩,
            fract_diff_lt hδ1 hp1 hp2 hcmp⟩, by simp [B]⟩)
      · exact Finset.mem_coe.mpr (Finset.mem_product.mpr ⟨Finset.mem_filter.mpr
          ⟨Finset.mem_offDiag.mpr ⟨hp2A, hp1A, hne.symm⟩,
            fract_diff_lt hδ1 hp2 hp1 (le_of_not_ge hcmp)⟩, by simp [B]⟩)
    · dsimp only [φ] at hpq
      split_ifs at hpq with h1 h2
      · exact (Prod.ext_iff.mp hpq).1
      · cases (Prod.ext_iff.mp hpq).2
      · cases (Prod.ext_iff.mp hpq).2
      · have hswap := (Prod.ext_iff.mp hpq).1
        ext
        · exact (Prod.ext_iff.mp hswap).2
        · exact (Prod.ext_iff.mp hswap).1
  calc
    Green86.numInInterval A θ t * (Green86.numInInterval A θ t - 1)
      = S.card * (S.card - 1) := by rw [hScard]
    _ = S.offDiag.card := hoff.symm
    _ ≤ (W ×ˢ B).card := hle
    _ = 2 * W.card := by rw [Finset.card_product, hB, mul_comm]

private lemma fract_div_mul_int {P : ℕ} (hP : 0 < P) (j : ℕ) (d : ℤ) :
    Int.fract (((j : ℝ) / (P : ℝ)) * (d : ℝ)) =
      ((((j : ℤ) * d) % (P : ℤ)).toNat : ℝ) / (P : ℝ) := by
  let P' : ℤ := (P : ℤ)
  have hP' : 0 < P' := by omega
  set m : ℤ := ((j : ℤ) * d) % P'
  set q : ℤ := ((j : ℤ) * d) / P'
  have hm0 : 0 ≤ m := Int.emod_nonneg _ hP'.ne'
  have hmP : m < P' := Int.emod_lt_of_pos _ hP'
  have hr : (m.toNat : ℤ) = m := Int.toNat_of_nonneg hm0
  have hrP : (m.toNat : ℝ) < (P : ℝ) := by
    have hltZ : (m.toNat : ℤ) < (P : ℤ) := by omega
    exact_mod_cast hltZ
  have hPos : (0 : ℝ) < P := by exact_mod_cast hP
  rw [Int.fract_eq_iff]
  refine ⟨by positivity, (div_lt_one hPos).mpr hrP, ⟨q, ?_⟩⟩
  have hdivZ : (P : ℤ) * q + (m.toNat : ℤ) = (j : ℤ) * d := by
    rw [hr]
    linarith [Int.mul_ediv_add_emod ((j : ℤ) * d) P']
  have hdivR : (P : ℝ) * (q : ℝ) + (m.toNat : ℝ) = (j : ℝ) * (d : ℝ) := by
    exact_mod_cast hdivZ
  field_simp [hPos.ne']
  linarith

private lemma card_good_dilations_le {P n : ℕ} (hP : P.Prime) (hn : 1 ≤ n) {d : ℤ}
    (hd0 : d ≠ 0) (hdP : d.natAbs < P) :
    ((Finset.range P).filter (fun (j : ℕ) =>
      Int.fract (((j : ℝ) / (P : ℝ)) * (d : ℝ)) < 1 / (n : ℝ))).card ≤ P / n + 1 := by
  let f : ℕ → ℕ := fun j => (((j : ℤ) * d) % (P : ℤ)).toNat
  calc
    ((Finset.range P).filter (fun (j : ℕ) =>
        Int.fract (((j : ℝ) / (P : ℝ)) * (d : ℝ)) < 1 / (n : ℝ))).card
      ≤ (Finset.range (P / n + 1)).card := by
        refine Finset.card_le_card_of_injOn f (fun j hj => ?_) (fun j₁ hj₁ j₂ hj₂ hfj => ?_)
        · simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hj ⊢
          have hlt := hj.2
          rw [fract_div_mul_int hP.pos j d] at hlt
          have hP0 : (0 : ℝ) < P := by exact_mod_cast hP.pos
          have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
          rw [div_lt_div_iff₀ hP0 hn0, one_mul] at hlt
          have hltN : f j * n < P := by exact_mod_cast hlt
          have hlediv : f j ≤ P / n := (Nat.le_div_iff_mul_le hn).mpr (by omega)
          omega
        · simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hj₁ hj₂
          have hP' : (0 : ℤ) < P := by exact_mod_cast hP.pos
          have hm1 : 0 ≤ ((j₁ : ℤ) * d) % (P : ℤ) := Int.emod_nonneg _ hP'.ne'
          have hm2 : 0 ≤ ((j₂ : ℤ) * d) % (P : ℤ) := Int.emod_nonneg _ hP'.ne'
          have heq_mod : ((j₁ : ℤ) * d) % (P : ℤ) = ((j₂ : ℤ) * d) % (P : ℤ) := by
            have := congrArg (fun x : ℕ => (x : ℤ)) hfj
            dsimp only [f] at this
            rw [Int.toNat_of_nonneg hm1, Int.toNat_of_nonneg hm2] at this
            exact this
          set k : ℤ := ((j₁ : ℤ) * d) / (P : ℤ) - ((j₂ : ℤ) * d) / (P : ℤ)
          have hmul : ((j₁ : ℤ) - (j₂ : ℤ)) * d = (P : ℤ) * k := by
            have e1 := Int.mul_ediv_add_emod ((j₁ : ℤ) * d) (P : ℤ)
            have e2 := Int.mul_ediv_add_emod ((j₂ : ℤ) * d) (P : ℤ)
            have hk : (P : ℤ) * k =
                (P : ℤ) * (((j₁ : ℤ) * d) / (P : ℤ)) -
                (P : ℤ) * (((j₂ : ℤ) * d) / (P : ℤ)) := by ring
            have hsub : ((j₁ : ℤ) - (j₂ : ℤ)) * d = (j₁ : ℤ) * d - (j₂ : ℤ) * d := by ring
            linarith
          have habs : ((j₁ : ℤ) - (j₂ : ℤ)).natAbs * d.natAbs = P * k.natAbs := by
            have := congrArg Int.natAbs hmul
            rw [Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_natCast] at this
            exact this
          have hdvd : P ∣ ((j₁ : ℤ) - (j₂ : ℤ)).natAbs * d.natAbs := ⟨k.natAbs, habs⟩
          rcases hP.dvd_mul.mp hdvd with h1 | h2
          · by_contra hne
            have hpos : 0 < ((j₁ : ℤ) - (j₂ : ℤ)).natAbs :=
              Int.natAbs_pos.mpr (by omega)
            have hle := Nat.le_of_dvd hpos h1
            omega
          · exfalso
            have hle := Nat.le_of_dvd (Int.natAbs_pos.mpr hd0) h2
            omega
    _ = P / n + 1 := Finset.card_range _

private lemma exists_dilation_lt_two_sqrt_add_one (A : Finset ℤ) (hn2 : 2 ≤ A.card) :
    ∃ θ : ℝ, ∀ t : ℝ, (Green86.numInInterval A θ t : ℝ) ≤ 3 * Real.sqrt (A.card : ℝ) := by
  set n := A.card
  set Bsup : ℕ := A.sup Int.natAbs
  obtain ⟨P, hPM, hP⟩ := Nat.exists_infinite_primes (n + 1 + 2 * Bsup)
  have hnP : n < P := by omega
  have hn1 : 1 ≤ n := by omega
  let close : ℕ → ℤ × ℤ → Prop := fun j p =>
    Int.fract (((j : ℝ) / (P : ℝ)) * ((p.1 - p.2 : ℤ) : ℝ)) < 1 / (n : ℝ)
  have hsum : ∑ j ∈ Finset.range P, (A.offDiag.filter (fun p => close j p)).card =
      ∑ p ∈ A.offDiag, ((Finset.range P).filter (fun j => close j p)).card := by
    simp only [Finset.card_filter]
    exact Finset.sum_comm
  have hterm : ∀ p ∈ A.offDiag,
      ((Finset.range P).filter (fun j => close j p)).card ≤ P / n + 1 := by
    intro p hp
    simp only [Finset.mem_offDiag] at hp
    rcases hp with ⟨hp1, hp2, hne⟩
    have hd0 : p.1 - p.2 ≠ 0 := sub_ne_zero.mpr hne
    have h1 : p.1.natAbs ≤ Bsup := Finset.le_sup (f := Int.natAbs) hp1
    have h2 : p.2.natAbs ≤ Bsup := Finset.le_sup (f := Int.natAbs) hp2
    have htri : (p.1 - p.2).natAbs ≤ p.1.natAbs + p.2.natAbs := Int.natAbs_sub_le p.1 p.2
    exact card_good_dilations_le hP hn1 hd0 (by omega)
  have hsum_le : ∑ j ∈ Finset.range P, (A.offDiag.filter (fun p => close j p)).card ≤
      A.offDiag.card * (P / n + 1) := by
    rw [hsum]
    calc
      ∑ p ∈ A.offDiag, ((Finset.range P).filter (fun j => close j p)).card
        ≤ ∑ _p ∈ A.offDiag, (P / n + 1) := Finset.sum_le_sum hterm
      _ = A.offDiag.card * (P / n + 1) := by simp
  have hoff_le : A.offDiag.card ≤ n * (n - 1) := by
    rw [Finset.offDiag_card]
    change n * n - n ≤ n * (n - 1)
    cases n with
    | zero => simp
    | succ k =>
      simp only [Nat.add_sub_cancel]
      have hmulk : (k + 1) * (k + 1) = (k + 1) * k + (k + 1) := by ring
      omega
  have hstrict : A.offDiag.card * (P / n + 1) < P * (2 * n) := by
    have hdiv : n * (P / n) ≤ P := Nat.mul_div_le P n
    have hmul : A.offDiag.card * (P / n + 1) ≤ (n - 1) * (n * (P / n) + n) := by
      calc
        A.offDiag.card * (P / n + 1) ≤ (n * (n - 1)) * (P / n + 1) :=
          Nat.mul_le_mul_right _ hoff_le
        _ = (n - 1) * (n * (P / n) + n) := by ring
    have hsub : n - 1 + 1 = n := by omega
    nlinarith
  have hex : ∃ j ∈ Finset.range P, (A.offDiag.filter (fun p => close j p)).card < 2 * n := by
    by_contra! hall
    have hge : P * (2 * n) ≤
        ∑ j ∈ Finset.range P, (A.offDiag.filter (fun p => close j p)).card := by
      calc
        P * (2 * n) = ∑ _j ∈ Finset.range P, (2 * n) := by simp
        _ ≤ ∑ j ∈ Finset.range P, (A.offDiag.filter (fun p => close j p)).card :=
          Finset.sum_le_sum hall
    omega
  rcases hex with ⟨j, -, hj⟩
  refine ⟨(j : ℝ) / (P : ℝ), fun t => ?_⟩
  set m := Green86.numInInterval A ((j : ℝ) / (P : ℝ)) t
  have hpair : m * (m - 1) < 4 * n := by
    have hle := sq_sub_le_two_mul_closePairs A ((j : ℝ) / (P : ℝ)) t hn1
    change m * (m - 1) ≤ 2 * (A.offDiag.filter (fun p => close j p)).card at hle
    omega
  have hsqR : ((m : ℝ) - 1) ^ 2 < 4 * (n : ℝ) := by
    rcases Nat.eq_zero_or_pos m with hm0 | hmpos
    · rw [hm0]
      have : (2 : ℝ) ≤ n := by exact_mod_cast hn2
      norm_num
      linarith
    · have hnat : (m - 1) * (m - 1) < 4 * n := by
        have : (m - 1) * (m - 1) ≤ m * (m - 1) := Nat.mul_le_mul_right (m - 1) (by omega)
        omega
      have hcast : (((m - 1 : ℕ) : ℝ)) * (((m - 1 : ℕ) : ℝ)) < 4 * (n : ℝ) := by
        exact_mod_cast hnat
      rw [Nat.cast_sub hmpos] at hcast
      push_cast at hcast
      nlinarith
  have hsqrt_sq : Real.sqrt (n : ℝ) ^ 2 = (n : ℝ) := Real.sq_sqrt (by positivity)
  have hsqrt_nn : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
  have hm_le : (m : ℝ) - 1 ≤ 2 * Real.sqrt (n : ℝ) := by
    by_contra! hgt
    nlinarith
  have h1_le : 1 ≤ Real.sqrt (n : ℝ) := by
    by_contra! hlt1
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn2
    nlinarith
  linarith

theorem OMA.solution : OMA.R_Green86_green_86_R1.H1 := by
  intro c hc
  have hε : 0 < c - 1 / 2 := by linarith
  have htend : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ (c - 1 / 2)) Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop hε).comp tendsto_natCast_atTop_atTop
  rcases Filter.eventually_atTop.mp (htend.eventually_ge_atTop (3 : ℝ)) with ⟨N, hN⟩
  refine ⟨max N 2, fun A hA => ?_⟩
  have hn2 : 2 ≤ A.card := le_trans (le_max_right N 2) hA
  have hnN : N ≤ A.card := le_trans (le_max_left N 2) hA
  obtain ⟨θ, hθ⟩ := exists_dilation_lt_two_sqrt_add_one A hn2
  refine ⟨θ, fun t => ?_⟩
  have h1 := hθ t
  have h3 : (3 : ℝ) ≤ (A.card : ℝ) ^ (c - 1 / 2) := hN A.card hnN
  have hpos : (0 : ℝ) < A.card := by
    have : 0 < A.card := by omega
    exact_mod_cast this
  calc
    (Green86.numInInterval A θ t : ℝ)
      ≤ 3 * Real.sqrt (A.card : ℝ) := h1
    _ = 3 * (A.card : ℝ) ^ ((1 : ℝ) / 2) := by rw [Real.sqrt_eq_rpow]
    _ ≤ (A.card : ℝ) ^ (c - 1 / 2) * (A.card : ℝ) ^ ((1 : ℝ) / 2) := by
        exact mul_le_mul_of_nonneg_right h3 (Real.rpow_nonneg hpos.le _)
    _ = (A.card : ℝ) ^ c := by
        rw [← Real.rpow_add hpos]
        ring_nf


