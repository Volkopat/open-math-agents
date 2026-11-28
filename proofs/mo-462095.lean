import OMAStatements.S_mo_462095

namespace OMA.S_mo_462095

private noncomputable def scaled (n : ℕ) : ℝ := (n : ℝ) / Real.sqrt 2

private theorem bucket_nonneg (n : ℕ) : 0 ≤ ⌊12 * Int.fract (scaled n)⌋ :=
  Int.floor_nonneg.mpr (mul_nonneg (by norm_num) (Int.fract_nonneg _))

private noncomputable def colour (n : ℕ) : Fin 12 :=
  ⟨(⌊12 * Int.fract (scaled n)⌋ : ℤ).toNat, by
    have h : ⌊12 * Int.fract (scaled n)⌋ < (12 : ℤ) := by
      apply Int.floor_lt.mpr
      have := Int.fract_lt_one (scaled n)
      norm_num
      linarith
    omega⟩

private theorem same_colour {u v : ℕ} (h : colour u = colour v) :
    |Int.fract (scaled v) - Int.fract (scaled u)| < 1 / 12 := by
  have he := congrArg Fin.val h
  change (⌊12 * Int.fract (scaled u)⌋ : ℤ).toNat =
    (⌊12 * Int.fract (scaled v)⌋ : ℤ).toNat at he
  have hf : ⌊12 * Int.fract (scaled u)⌋ = ⌊12 * Int.fract (scaled v)⌋ := by
    have := bucket_nonneg u
    have := bucket_nonneg v
    omega
  have hu₁ := Int.floor_le (12 * Int.fract (scaled u))
  have hu₂ := Int.lt_floor_add_one (12 * Int.fract (scaled u))
  have hv₁ := Int.floor_le (12 * Int.fract (scaled v))
  have hv₂ := Int.lt_floor_add_one (12 * Int.fract (scaled v))
  rw [hf] at hu₁ hu₂
  exact abs_lt.mpr ⟨by linarith, by linarith⟩

private theorem no_approximation (l : ℕ) (hl : 2 ≤ l) (z : ℤ)
    (hclose : |Real.sqrt 2 * (l : ℝ) - (z : ℝ)| < 1 / 6)
    (hsmall : |Real.sqrt 2 * (l : ℝ) - (z : ℝ)| * (l : ℝ) < 1 / 3) : False := by
  have hlR : (2 : ℝ) ≤ l := by exact_mod_cast hl
  have hlpos : (0 : ℝ) < l := by linarith
  have hs₁ : 1 < Real.sqrt 2 := by
    apply (Real.lt_sqrt (by norm_num)).mpr
    norm_num
  have hs₂ : Real.sqrt 2 < 17 / 12 := by
    apply (Real.sqrt_lt' (by norm_num)).mpr
    norm_num
  have hsSq : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hx : 0 < Real.sqrt 2 * (l : ℝ) := by positivity
  have hgt : (l : ℝ) < Real.sqrt 2 * (l : ℝ) := by
    simpa only [one_mul] using mul_lt_mul_of_pos_right hs₁ hlpos
  have hlt : Real.sqrt 2 * (l : ℝ) < (17 / 12) * (l : ℝ) :=
    mul_lt_mul_of_pos_right hs₂ hlpos
  have hz : 0 < (z : ℝ) := by linarith [(abs_lt.mp hclose).2]
  have hsum : Real.sqrt 2 * (l : ℝ) + (z : ℝ) < 3 * (l : ℝ) := by
    linarith [(abs_lt.mp hclose).1]
  have hprod : |Real.sqrt 2 * (l : ℝ) - (z : ℝ)| *
      (Real.sqrt 2 * (l : ℝ) + (z : ℝ)) < 1 := calc
    _ ≤ |Real.sqrt 2 * (l : ℝ) - (z : ℝ)| * (3 * (l : ℝ)) :=
      mul_le_mul_of_nonneg_left hsum.le (abs_nonneg _)
    _ < 1 := by nlinarith only [hsmall]
  let D : ℤ := 2 * (l : ℤ) ^ 2 - z ^ 2
  have hD : (D : ℝ) = (Real.sqrt 2 * (l : ℝ) - (z : ℝ)) *
      (Real.sqrt 2 * (l : ℝ) + (z : ℝ)) := by
    push_cast [D]
    linear_combination -((l : ℝ) ^ 2) * hsSq
  have hDlt : |(D : ℝ)| < 1 := by
    rw [hD, abs_mul, abs_of_pos (by linarith : 0 < Real.sqrt 2 * (l : ℝ) + (z : ℝ))]
    exact hprod
  have hDint : |D| < (1 : ℤ) := by exact_mod_cast hDlt
  have hDzero : D = 0 := by
    obtain ⟨hlo, hhi⟩ := abs_lt.mp hDint
    omega
  have he : Real.sqrt 2 * (l : ℝ) = (z : ℝ) := by
    have hzero : (D : ℝ) = 0 := by exact_mod_cast hDzero
    rw [hzero] at hD
    rcases mul_eq_zero.mp hD.symm with hdiff | hsum'
    · exact sub_eq_zero.mp hdiff
    · linarith
  exact (irrational_sqrt_two.ne_rational z (l : ℤ))
    (by push_cast; exact (eq_div_iff hlpos.ne').mpr he)

private theorem no_repetition (l : ℕ) (hl : 2 ≤ l) (a : ℕ → ℕ)
    (hstep : ∀ i, i + 2 < 2 * l → a i + a (i + 2) = 2 * a (i + 1) + 2)
    (hcol : ∀ i < l, colour (a i) = colour (a (i + l))) : False := by
  let jump : ℕ → ℝ := fun i => (a (i + 1) : ℝ) - a i
  have jump_law (i : ℕ) (hi : i + 1 < 2 * l) : jump i = jump 0 + 2 * (i : ℝ) := by
    induction i with
    | zero => simp
    | succ i ih =>
      have hs : (a i : ℝ) + a (i + 2) = 2 * (a (i + 1) : ℝ) + 2 := by
        exact_mod_cast hstep i hi
      have hprev := ih (by omega)
      dsimp [jump] at hprev ⊢
      push_cast
      linarith
  let err : ℕ → ℝ := fun i => Int.fract (scaled (a (i + l))) - Int.fract (scaled (a i))
  let Z : ℕ → ℤ := fun i => ⌊scaled (a (i + l))⌋ - ⌊scaled (a i)⌋
  have err_bound (i : ℕ) (hi : i < l) : |err i| < 1 / 12 := same_colour (hcol i hi)
  have err_step (i : ℕ) (hi : i + 1 < l) :
      err (i + 1) - err i = Real.sqrt 2 * (l : ℝ) - ((Z (i + 1) - Z i : ℤ) : ℝ) := by
    have h₁ := jump_law (i + l) (by omega)
    have h₂ := jump_law i (by omega)
    have hd : ((a (i + 1 + l) : ℝ) - a (i + l)) - ((a (i + 1) : ℝ) - a i) = 2 * (l : ℝ) := by
      rw [show i + 1 + l = i + l + 1 by omega]
      change jump (i + l) - jump i = _
      rw [h₁, h₂, Nat.cast_add]
      ring
    have hscale : (2 * (l : ℝ)) / Real.sqrt 2 = Real.sqrt 2 * (l : ℝ) := by
      have hpos : 0 < Real.sqrt (2 : ℝ) := by positivity
      apply (div_eq_iff hpos.ne').mpr
      have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
      linear_combination -((l : ℝ)) * hs
    calc
      err (i + 1) - err i =
        (((a (i+1+l) : ℝ) - a (i+l)) - ((a (i+1) : ℝ) - a i)) / Real.sqrt 2 -
          ((Z (i + 1) - Z i : ℤ) : ℝ) := by
        simp only [err, Z, Int.fract, scaled, Int.cast_sub, sub_div]
        ring
      _ = _ := by rw [hd, hscale]
  have step_bound (i : ℕ) (hi : i + 1 < l) :
      |Real.sqrt 2 * (l : ℝ) - ((Z (i + 1) - Z i : ℤ) : ℝ)| < 1 / 6 := by
    rw [← err_step i hi]
    have h₁ := abs_lt.mp (err_bound i (by omega))
    have h₂ := abs_lt.mp (err_bound (i + 1) hi)
    exact abs_lt.mpr ⟨by linarith, by linarith⟩
  let z := Z 1 - Z 0
  have hz : |Real.sqrt 2 * (l : ℝ) - (z : ℝ)| < 1 / 6 := step_bound 0 (by omega)
  have steps_eq (i : ℕ) (hi : i + 1 < l) : Z (i + 1) - Z i = z := by
    have h₁ := abs_lt.mp hz
    have h₂ := abs_lt.mp (step_bound i hi)
    have hR : |(((Z (i + 1) - Z i) - z : ℤ) : ℝ)| < 1 := by
      rw [Int.cast_sub]
      exact abs_lt.mpr ⟨by linarith, by linarith⟩
    have hZ : |(Z (i + 1) - Z i) - z| < (1 : ℤ) := by exact_mod_cast hR
    obtain ⟨hlo, hhi⟩ := abs_lt.mp hZ
    omega
  have telescoping (i : ℕ) (hi : i < l) :
      err i - err 0 = (i : ℝ) * (Real.sqrt 2 * (l : ℝ) - (z : ℝ)) := by
    induction i with
    | zero => simp
    | succ i ih =>
      have h := err_step i hi
      rw [steps_eq i hi] at h
      rw [Nat.cast_succ]
      linear_combination h + ih (by omega)
  have hlast := telescoping (l - 1) (by omega)
  rw [Nat.cast_sub (by omega : 1 ≤ l), Nat.cast_one] at hlast
  have hlR : (2 : ℝ) ≤ l := by exact_mod_cast hl
  have hscaled : |Real.sqrt 2 * (l : ℝ) - (z : ℝ)| * ((l : ℝ) - 1) < 1 / 6 := by
    rw [mul_comm, ← abs_of_pos (by linarith : 0 < (l : ℝ) - 1), ← abs_mul, ← hlast]
    have h₁ := abs_lt.mp (err_bound 0 (by omega))
    have h₂ := abs_lt.mp (err_bound (l - 1) (by omega))
    exact abs_lt.mpr ⟨by linarith, by linarith⟩
  apply no_approximation l hl z hz
  calc
    _ ≤ |Real.sqrt 2 * (l : ℝ) - (z : ℝ)| * (2 * ((l : ℝ) - 1)) :=
      mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
    _ < _ := by nlinarith only [hscaled]

end OMA.S_mo_462095

open OMA.S_mo_462095 in
theorem OMA.solution : type_of% @OMA.S_mo_462095.main := by
  intro h
  obtain ⟨l, hl, a, hstep, hcol⟩ := h 12 colour
  exact no_repetition l hl a hstep hcol
