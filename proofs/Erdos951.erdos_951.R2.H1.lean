import OMAReductions.R_Erdos951_erdos_951_R2

-- Proof of Erdos951.erdos_951.R2.H1
-- Every 1-separated positive multiplicative submonoid containing 1 + d*ℕ
-- consists solely of natural numbers (rational case via Bezout on powers,
-- irrational case via pigeonhole / Kronecker step density).
-- Credit: @DPS0340

theorem OMA.solution : OMA.R_Erdos951_erdos_951_R2.H1 := by
  classical
  intro S hpos hsep d hd hprog x hxS
  have h1S : (1 : ℝ) ∈ S := by
    have h0 := hprog 0; rw [Nat.cast_zero, mul_zero, add_zero] at h0; exact h0
  have hx_ge1 : 1 ≤ x := by
    by_contra hlt
    push Not at hlt
    have hne : x ≠ 1 := ne_of_lt hlt
    have h1 := hsep x hxS 1 h1S hne
    have hx0 := hpos x hxS
    rw [abs_of_neg (sub_neg.mpr hlt)] at h1
    linarith
  by_contra hnotnat
  push Not at hnotnat
  have hnotint : ∀ z : ℤ, x ≠ (z : ℝ) := by
    intro z hz
    have hz_nonneg : 0 ≤ z := by
      have : (0 : ℝ) < (z : ℝ) := hz ▸ hpos x hxS
      exact_mod_cast this.le
    exact hnotnat z.toNat (by rw [hz, ← Int.cast_natCast, Int.toNat_of_nonneg hz_nonneg])
  by_cases hrat : ∃ q : ℚ, (q : ℝ) = x
  · -- Rational non-integer case: write q = a / b with b ≥ 2, gcd(a, b) = 1
    obtain ⟨q, hq⟩ := hrat
    have hq_pos : 0 < q := by exact_mod_cast (hq.symm ▸ hpos x hxS : (0 : ℝ) < (q : ℝ))
    let a : ℕ := q.num.toNat
    let b : ℕ := q.den
    have hb_pos : 0 < b := q.pos
    have ha_cast : (a : ℤ) = q.num := Int.toNat_of_nonneg (Rat.num_nonneg.mpr hq_pos.le)
    have hq_eq : (q : ℝ) = (a : ℝ) / (b : ℝ) := by
      rw [Rat.cast_def, ← ha_cast]; push_cast; rfl
    have hb_ge2 : 2 ≤ b := by
      by_contra hb1
      have hbeq : b = 1 := by omega
      have : x = (a : ℝ) := by rw [← hq, hq_eq, hbeq]; simp
      exact hnotnat a this
    have hcop : Nat.Coprime a b := by
      have hred := q.reduced
      have habs : q.num.natAbs = a := by
        have hnn : 0 ≤ q.num := Rat.num_nonneg.mpr hq_pos.le
        omega
      rwa [habs] at hred
    -- Choose m so that d < b ^ m
    have hbm_exists : ∃ m : ℕ, d < b ^ m := by
      refine ⟨d + 1, ?_⟩
      have h1 : d + 1 < 2 ^ (d + 1) := Nat.lt_two_pow_self
      have h2 : 2 ^ (d + 1) ≤ b ^ (d + 1) := Nat.pow_le_pow_left hb_ge2 _
      omega
    obtain ⟨m, hbm⟩ := hbm_exists
    have hcopm : Nat.Coprime (a ^ m) (b ^ m) := hcop.pow m m
    -- Pick s' ∈ {1, ..., d} congruent to a^m - b^m (mod d), so a^m - b^m + d*t = s' for some t : ℤ
    let diff : ℤ := (a ^ m : ℕ) - (b ^ m : ℕ)
    let rem : ℤ := diff % (d : ℤ)
    let s' : ℤ := if rem = 0 then (d : ℤ) else rem
    have hdZ : (0 : ℤ) < (d : ℤ) := by exact_mod_cast hd
    have hrem_nn : 0 ≤ rem := Int.emod_nonneg diff hdZ.ne'
    have hrem_lt : rem < (d : ℤ) := Int.emod_lt_of_pos diff hdZ
    have hs'_lo : 1 ≤ s' := by
      dsimp [s']; split_ifs with h0 <;> omega
    have hs'_hi : s' ≤ (d : ℤ) := by
      dsimp [s']; split_ifs with h0 <;> omega
    have hd_dvd : (d : ℤ) ∣ (s' - diff) := by
      have hmod : (d : ℤ) ∣ (diff - rem) := by
        refine ⟨diff / (d : ℤ), ?_⟩
        have := Int.mul_ediv_add_emod diff (d : ℤ)
        dsimp [rem]; linarith
      dsimp [s']; split_ifs with h0
      · rw [h0, sub_zero] at hmod
        obtain ⟨c, hc⟩ := hmod
        exact ⟨1 - c, by linarith⟩
      · obtain ⟨c, hc⟩ := hmod
        exact ⟨-c, by linarith⟩
    obtain ⟨t, ht⟩ := hd_dvd
    -- Use Bezout on coprime (a^m, b^m) to find k, r : ℕ with a^m * k - b^m * r = t
    have hbez : (a ^ m : ℤ) * Nat.gcdA (a ^ m) (b ^ m) +
        (b ^ m : ℤ) * Nat.gcdB (a ^ m) (b ^ m) = 1 := by
      have := Nat.gcd_eq_gcd_ab (a ^ m) (b ^ m)
      rw [hcopm.gcd_eq_one] at this
      exact_mod_cast this.symm
    let u0 : ℤ := t * Nat.gcdA (a ^ m) (b ^ m)
    let v0 : ℤ := -(t * Nat.gcdB (a ^ m) (b ^ m))
    have huv0 : (a ^ m : ℤ) * u0 - (b ^ m : ℤ) * v0 = t := by
      dsimp [u0, v0]
      linear_combination t * hbez
    have ha_pos : 0 < a := by
      have h0 : (0 : ℝ) < (a : ℝ) / (b : ℝ) := hq_eq ▸ hq.symm ▸ hpos x hxS
      have h1 : (0 : ℝ) < (a : ℝ) := by
        have hbR : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb_pos
        exact (div_pos_iff_of_pos_right hbR).mp h0
      exact_mod_cast h1
    have ham_pos : (0 : ℤ) < (a ^ m : ℕ) := by exact_mod_cast Nat.pow_pos ha_pos
    have hbm_pos : (0 : ℤ) < (b ^ m : ℕ) := by exact_mod_cast Nat.pow_pos hb_pos
    let c : ℤ := max 0 (max (-u0) (-v0))
    have hc_nn : 0 ≤ c := le_max_left _ _
    let u : ℤ := u0 + c * (b ^ m : ℕ)
    let v : ℤ := v0 + c * (a ^ m : ℕ)
    have hu_nn : 0 ≤ u := by
      have h1 : -u0 ≤ c := (le_max_left _ _).trans (le_max_right _ _)
      have h2 : c ≤ c * (b ^ m : ℕ) := le_mul_of_one_le_right hc_nn (by omega)
      dsimp [u]; push_cast at h2 ⊢; linarith
    have hv_nn : 0 ≤ v := by
      have h1 : -v0 ≤ c := (le_max_right _ _).trans (le_max_right _ _)
      have h2 : c ≤ c * (a ^ m : ℕ) := le_mul_of_one_le_right hc_nn (by omega)
      dsimp [v]; push_cast at h2 ⊢; linarith
    let k : ℕ := u.toNat
    let r : ℕ := v.toNat
    have hk_cast : (k : ℤ) = u := Int.toNat_of_nonneg hu_nn
    have hr_cast : (r : ℤ) = v := Int.toNat_of_nonneg hv_nn
    have hkr_eq : (a ^ m : ℤ) * (1 + (d : ℤ) * (k : ℤ)) -
        (b ^ m : ℤ) * (1 + (d : ℤ) * (r : ℤ)) = s' := by
      have hkr : (a ^ m : ℤ) * (k : ℤ) - (b ^ m : ℤ) * (r : ℤ) = t := by
        rw [hk_cast, hr_cast]
        dsimp [u, v]
        linear_combination huv0
      dsimp [diff] at ht
      linear_combination (d : ℤ) * hkr - ht
    have hxmS : x ^ m * (1 + (d : ℝ) * (k : ℝ)) ∈ S :=
      S.mul_mem (S.pow_mem hxS m) (hprog k)
    have hrS : 1 + (d : ℝ) * (r : ℝ) ∈ S := hprog r
    have hdiff_real : x ^ m * (1 + (d : ℝ) * (k : ℝ)) - (1 + (d : ℝ) * (r : ℝ)) =
        (s' : ℝ) / ((b ^ m : ℕ) : ℝ) := by
      have hxm_eq : x ^ m = ((a ^ m : ℕ) : ℝ) / ((b ^ m : ℕ) : ℝ) := by
        rw [← hq, hq_eq, div_pow, Nat.cast_pow, Nat.cast_pow]
      have hbmR : ((b ^ m : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (Nat.pow_pos hb_pos).ne'
      rw [hxm_eq]
      field_simp [hbmR]
      have hkr_R : ((a ^ m : ℕ) : ℝ) * (1 + (d : ℝ) * (k : ℝ)) -
          ((b ^ m : ℕ) : ℝ) * (1 + (d : ℝ) * (r : ℝ)) = (s' : ℝ) := by
        exact_mod_cast hkr_eq
      linarith
    have hbmR_pos : (0 : ℝ) < ((b ^ m : ℕ) : ℝ) := by exact_mod_cast Nat.pow_pos hb_pos
    have hs'_pos : (0 : ℝ) < (s' : ℝ) := by exact_mod_cast (show (0 : ℤ) < s' by omega)
    have hs'_lt : (s' : ℝ) < ((b ^ m : ℕ) : ℝ) := by
      have : s' < (b ^ m : ℕ) := by omega
      exact_mod_cast this
    have hdiv_pos : 0 < (s' : ℝ) / ((b ^ m : ℕ) : ℝ) := div_pos hs'_pos hbmR_pos
    have hdiv_lt1 : (s' : ℝ) / ((b ^ m : ℕ) : ℝ) < 1 := (div_lt_one hbmR_pos).mpr hs'_lt
    have hne : x ^ m * (1 + (d : ℝ) * (k : ℝ)) ≠ 1 + (d : ℝ) * (r : ℝ) := by
      intro heq; rw [heq, sub_self] at hdiff_real; linarith
    have h1 := hsep _ hxmS _ hrS hne
    rw [hdiff_real, abs_of_pos hdiv_pos] at h1
    linarith
  · -- Irrational case: pigeonhole on fractional parts of k * x gives small step δ ∈ (0, 1/(2d))
    push Not at hrat
    have hirr_mul : ∀ m : ℕ, 0 < m → ∀ z : ℤ, (m : ℝ) * x ≠ (z : ℝ) := by
      intro m hm z h
      apply hrat ((z : ℚ) / (m : ℚ))
      have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
      push_cast; rw [div_eq_iff hmR, mul_comm]; exact h.symm
    -- Pigeonhole on {0*x}, {1*x}, ..., {(2d)*x} into 2d bins of width 1/(2d)
    let N : ℕ := 2 * d
    have hNpos : 0 < N := by omega
    have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hNpos
    let bin : Fin (N + 1) → Fin N := fun i =>
      ⟨⌊(N : ℝ) * Int.fract ((i.val : ℝ) * x)⌋₊, by
        have hlt : (N : ℝ) * Int.fract ((i.val : ℝ) * x) < (N : ℝ) := by
          have := Int.fract_lt_one ((i.val : ℝ) * x)
          nlinarith
        exact (Nat.floor_lt (by positivity)).mpr hlt⟩
    have hnotinj : ¬ Function.Injective bin := by
      intro hinj
      have := Fintype.card_le_of_injective bin hinj
      simp at this
    rw [Function.Injective] at hnotinj
    push Not at hnotinj
    obtain ⟨i, j, hbin, hij⟩ := hnotinj
    -- WLOG i < j
    have hex_step : ∃ m : ℕ, 0 < m ∧
        (Int.fract ((m : ℝ) * x) < 1 / (N : ℝ) ∨ 1 - 1 / (N : ℝ) < Int.fract ((m : ℝ) * x)) := by
      have hclose : |Int.fract ((i.val : ℝ) * x) - Int.fract ((j.val : ℝ) * x)| < 1 / (N : ℝ) := by
        have hfl : ⌊(N : ℝ) * Int.fract ((i.val : ℝ) * x)⌋₊ =
            ⌊(N : ℝ) * Int.fract ((j.val : ℝ) * x)⌋₊ := congrArg Fin.val hbin
        have hi1 := Nat.floor_le (show 0 ≤ (N : ℝ) * Int.fract ((i.val : ℝ) * x) by positivity)
        have hi2 := Nat.lt_floor_add_one ((N : ℝ) * Int.fract ((i.val : ℝ) * x))
        have hj1 := Nat.floor_le (show 0 ≤ (N : ℝ) * Int.fract ((j.val : ℝ) * x) by positivity)
        have hj2 := Nat.lt_floor_add_one ((N : ℝ) * Int.fract ((j.val : ℝ) * x))
        rw [hfl] at hi1 hi2
        rw [abs_lt]
        constructor
        · rw [← neg_div, div_lt_iff₀ hNR]; nlinarith
        · rw [lt_div_iff₀ hNR]; nlinarith
      rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with hlt | hgt
      · refine ⟨j.val - i.val, by omega, ?_⟩
        have hsub : ((j.val - i.val : ℕ) : ℝ) * x = (j.val : ℝ) * x - (i.val : ℝ) * x := by
          rw [Nat.cast_sub hlt.le]; ring
        have hdiff_eq : ((j.val - i.val : ℕ) : ℝ) * x -
            ((⌊(j.val : ℝ) * x⌋ - ⌊(i.val : ℝ) * x⌋ : ℤ) : ℝ) =
            Int.fract ((j.val : ℝ) * x) - Int.fract ((i.val : ℝ) * x) := by
          rw [hsub]; simp only [Int.fract, Int.cast_sub]; ring
        have hfd := abs_lt.mp hclose
        have hfi0 := Int.fract_nonneg ((i.val : ℝ) * x)
        have hfi1 := Int.fract_lt_one ((i.val : ℝ) * x)
        have hfj0 := Int.fract_nonneg ((j.val : ℝ) * x)
        have hfj1 := Int.fract_lt_one ((j.val : ℝ) * x)
        by_cases hsign : 0 ≤ Int.fract ((j.val : ℝ) * x) - Int.fract ((i.val : ℝ) * x)
        · left
          have hfr : Int.fract (((j.val - i.val : ℕ) : ℝ) * x) =
              Int.fract ((j.val : ℝ) * x) - Int.fract ((i.val : ℝ) * x) :=
            Int.fract_eq_iff.mpr ⟨hsign, by linarith,
              ⟨⌊(j.val : ℝ) * x⌋ - ⌊(i.val : ℝ) * x⌋, by linarith⟩⟩
          linarith
        · right
          push Not at hsign
          have hfr : Int.fract (((j.val - i.val : ℕ) : ℝ) * x) =
              1 + (Int.fract ((j.val : ℝ) * x) - Int.fract ((i.val : ℝ) * x)) :=
            Int.fract_eq_iff.mpr ⟨by linarith, by linarith,
              ⟨⌊(j.val : ℝ) * x⌋ - ⌊(i.val : ℝ) * x⌋ - 1, by push_cast at hdiff_eq ⊢; linarith⟩⟩
          linarith
      · refine ⟨i.val - j.val, by omega, ?_⟩
        have hsub : ((i.val - j.val : ℕ) : ℝ) * x = (i.val : ℝ) * x - (j.val : ℝ) * x := by
          rw [Nat.cast_sub hgt.le]; ring
        have hdiff_eq : ((i.val - j.val : ℕ) : ℝ) * x -
            ((⌊(i.val : ℝ) * x⌋ - ⌊(j.val : ℝ) * x⌋ : ℤ) : ℝ) =
            Int.fract ((i.val : ℝ) * x) - Int.fract ((j.val : ℝ) * x) := by
          rw [hsub]; simp only [Int.fract, Int.cast_sub]; ring
        have hfd := abs_lt.mp hclose
        have hfi0 := Int.fract_nonneg ((i.val : ℝ) * x)
        have hfi1 := Int.fract_lt_one ((i.val : ℝ) * x)
        have hfj0 := Int.fract_nonneg ((j.val : ℝ) * x)
        have hfj1 := Int.fract_lt_one ((j.val : ℝ) * x)
        by_cases hsign : 0 ≤ Int.fract ((i.val : ℝ) * x) - Int.fract ((j.val : ℝ) * x)
        · left
          have hfr : Int.fract (((i.val - j.val : ℕ) : ℝ) * x) =
              Int.fract ((i.val : ℝ) * x) - Int.fract ((j.val : ℝ) * x) :=
            Int.fract_eq_iff.mpr ⟨hsign, by linarith,
              ⟨⌊(i.val : ℝ) * x⌋ - ⌊(j.val : ℝ) * x⌋, by linarith⟩⟩
          linarith
        · right
          push Not at hsign
          have hfr : Int.fract (((i.val - j.val : ℕ) : ℝ) * x) =
              1 + (Int.fract ((i.val : ℝ) * x) - Int.fract ((j.val : ℝ) * x)) :=
            Int.fract_eq_iff.mpr ⟨by linarith, by linarith,
              ⟨⌊(i.val : ℝ) * x⌋ - ⌊(j.val : ℝ) * x⌋ - 1, by push_cast at hdiff_eq ⊢; linarith⟩⟩
          linarith
    obtain ⟨m, hmpos, hstep⟩ := hex_step
    have hfr_ne0 : Int.fract ((m : ℝ) * x) ≠ 0 := by
      intro h0
      exact hirr_mul m hmpos ⌊(m : ℝ) * x⌋ (by linarith [Int.fract_add_floor ((m : ℝ) * x)])
    have hfr_pos : 0 < Int.fract ((m : ℝ) * x) := lt_of_le_of_ne (Int.fract_nonneg _) hfr_ne0.symm
    -- Target fractional part α = Int.fract ((1 - x) / d) ∈ [0, 1)
    let α : ℝ := Int.fract ((1 - x) / (d : ℝ))
    have hα0 : 0 ≤ α := Int.fract_nonneg _
    have hα1 : α < 1 := Int.fract_lt_one _
    -- Find t : ℕ such that (t * m) * x + (x - 1) / d is within 1 / N of an integer
    have hex_k : ∃ k : ℕ, ∃ z : ℤ,
        |(k : ℝ) * x + (x - 1) / (d : ℝ) - (z : ℝ)| < 1 / (N : ℝ) := by
      rcases hstep with hsmall | hbig
      · let δ : ℝ := Int.fract ((m : ℝ) * x)
        have hδpos : 0 < δ := hfr_pos
        let t : ℕ := ⌊α / δ⌋₊
        have ht1 : (t : ℝ) * δ ≤ α := by
          have := Nat.floor_le (show 0 ≤ α / δ by positivity)
          exact (le_div_iff₀ hδpos).mp this
        have ht2 : α < ((t : ℝ) + 1) * δ := by
          have := Nat.lt_floor_add_one (α / δ)
          exact (div_lt_iff₀ hδpos).mp this
        let z : ℤ := (t : ℤ) * ⌊(m : ℝ) * x⌋ - ⌊(1 - x) / (d : ℝ)⌋
        refine ⟨t * m, z, ?_⟩
        have hrew : ((t * m : ℕ) : ℝ) * x + (x - 1) / (d : ℝ) - (z : ℝ) =
            (t : ℝ) * δ - α := by
          dsimp [z, δ, α]
          rw [Nat.cast_mul, mul_assoc, Int.cast_sub, Int.cast_mul, Int.cast_natCast]
          have h1 := Int.fract_add_floor ((m : ℝ) * x)
          have h2 := Int.fract_add_floor ((1 - x) / (d : ℝ))
          have h3 : (x - 1) / (d : ℝ) = -((1 - x) / (d : ℝ)) := by ring
          linear_combination -(t : ℝ) * h1 + h2 + h3
        rw [hrew, abs_lt]
        constructor <;> linarith
      · let δ : ℝ := 1 - Int.fract ((m : ℝ) * x)
        have hδpos : 0 < δ := by linarith [Int.fract_lt_one ((m : ℝ) * x)]
        have hδsmall : δ < 1 / (N : ℝ) := by dsimp [δ]; linarith
        let t : ℕ := ⌊(1 - α) / δ⌋₊
        have ht1 : (t : ℝ) * δ ≤ 1 - α := by
          have := Nat.floor_le (div_nonneg (show 0 ≤ 1 - α by linarith) hδpos.le)
          exact (le_div_iff₀ hδpos).mp this
        have ht2 : 1 - α < ((t : ℝ) + 1) * δ := by
          have := Nat.lt_floor_add_one ((1 - α) / δ)
          exact (div_lt_iff₀ hδpos).mp this
        let z : ℤ := (t : ℤ) * (⌊(m : ℝ) * x⌋ + 1) - (⌊(1 - x) / (d : ℝ)⌋ + 1)
        refine ⟨t * m, z, ?_⟩
        have hrew : ((t * m : ℕ) : ℝ) * x + (x - 1) / (d : ℝ) - (z : ℝ) =
            (1 - α) - (t : ℝ) * δ := by
          dsimp [z, δ, α]
          rw [Nat.cast_mul, mul_assoc, Int.cast_sub, Int.cast_mul, Int.cast_add,
            Int.cast_add, Int.cast_natCast, Int.cast_one]
          have h1 := Int.fract_add_floor ((m : ℝ) * x)
          have h2 := Int.fract_add_floor ((1 - x) / (d : ℝ))
          have h3 : (x - 1) / (d : ℝ) = -((1 - x) / (d : ℝ)) := by ring
          linear_combination -(t : ℝ) * h1 + h2 + h3
        rw [hrew, abs_lt]
        constructor <;> linarith
    obtain ⟨k, z, hkz⟩ := hex_k
    have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
    have hmul : |(1 + (d : ℝ) * (k : ℝ)) * x - (1 + (d : ℝ) * (z : ℝ))| < 1 / 2 := by
      have hrew : (1 + (d : ℝ) * (k : ℝ)) * x - (1 + (d : ℝ) * (z : ℝ)) =
          (d : ℝ) * ((k : ℝ) * x + (x - 1) / (d : ℝ) - (z : ℝ)) := by
        field_simp [hdR.ne']; ring
      rw [hrew, abs_mul, abs_of_pos hdR]
      have h1 : (d : ℝ) * |(k : ℝ) * x + (x - 1) / (d : ℝ) - (z : ℝ)| < (d : ℝ) * (1 / (N : ℝ)) :=
        mul_lt_mul_of_pos_left hkz hdR
      have h2 : (d : ℝ) * (1 / (N : ℝ)) = 1 / 2 := by
        dsimp [N]; push_cast; field_simp [hdR.ne']
      linarith
    have hz_nonneg : 0 ≤ z := by
      have hkx_ge0 : 0 ≤ (k : ℝ) * x + (x - 1) / (d : ℝ) := by
        have h1 : 0 ≤ (k : ℝ) * x := mul_nonneg (Nat.cast_nonneg _) (hpos x hxS).le
        have h2 : 0 ≤ (x - 1) / (d : ℝ) := div_nonneg (by linarith) hdR.le
        linarith
      have hlt : -(1 : ℝ) < (z : ℝ) := by
        have := (abs_lt.mp hkz).2
        have hNge : (1 : ℝ) / (N : ℝ) ≤ 1 := by
          rw [div_le_one hNR]; exact_mod_cast hNpos
        linarith
      have : (-1 : ℤ) < z := by exact_mod_cast hlt
      omega
    let r : ℕ := z.toNat
    have hr_cast : (r : ℝ) = (z : ℝ) := by
      have : (r : ℤ) = z := Int.toNat_of_nonneg hz_nonneg
      exact_mod_cast this
    have hkxS : (1 + (d : ℝ) * (k : ℝ)) * x ∈ S := S.mul_mem (hprog k) hxS
    have hrS : 1 + (d : ℝ) * (r : ℝ) ∈ S := hprog r
    have hne : (1 + (d : ℝ) * (k : ℝ)) * x ≠ 1 + (d : ℝ) * (r : ℝ) := by
      intro heq
      have h1 : ((1 + d * k : ℕ) : ℝ) * x = ((1 + d * r : ℕ) : ℤ) := by
        push_cast; linarith
      exact hirr_mul (1 + d * k) (by omega) ((1 + d * r : ℕ) : ℤ) h1
    have hsep1 := hsep _ hkxS _ hrS hne
    rw [hr_cast] at hsep1
    linarith
