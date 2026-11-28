import OMAReductions.R_OeisA249609_conjecture_R1_H2_R1_H1_R1

/-! A column-three digit-sum test for odd Pascal rows with small defects. -/

namespace OMA.R_OeisA249609_conjecture_R1_H2_R1_H1_R1_H2_R1

open OMA.R_OeisA249609_conjecture_R1_H2_R1_H1_R1

private lemma pow_mod_three (a : ℕ) : 2^a % 3 = 1 ∨ 2^a % 3 = 2 := by
  induction a with
  | zero => exact Or.inl (by decide)
  | succ a ih =>
    rw [pow_succ, Nat.mul_mod]
    rcases ih with h | h <;> simp [h]

private lemma cubic_mod_three (c : ℕ) : c*(c+1)*(c+2)%3 = 0 := by
  have h : c%3 = 0 ∨ c%3 = 1 ∨ c%3 = 2 := by omega
  rw [Nat.mul_mod, Nat.mul_mod c, Nat.add_mod c 1, Nat.add_mod c 2]
  rcases h with h | h | h <;> simp [h]

private lemma cubic_scaled (a c : ℕ) (hc : c + 2 ≤ 2^a) :
    let B := 2^a
    let t := c*(c+1)*(c+2)/3
    let m := (B^2-1)/3+(c+1)^2
    2 * (B-c).choose 3 + ((c+1)*B)*B + t = m*B := by
  dsimp only
  let B := 2^a
  have hB : 0 < B := by dsimp [B]; positivity
  change c+2 ≤ B at hc
  change 2 * (B-c).choose 3 + ((c+1)*B)*B + c*(c+1)*(c+2)/3 =
    ((B^2-1)/3 + (c+1)^2)*B
  have hfac := Nat.descFactorial_eq_factorial_mul_choose (B-c) 3
  norm_num [Nat.descFactorial] at hfac
  have hprod : 3*(2*(B-c).choose 3) = (B-c)*(B-c-1)*(B-c-2) := by
    calc
      _ = 6*(B-c).choose 3 := by ring
      _ = _ := by simpa only [mul_assoc, mul_comm, mul_left_comm] using hfac.symm
  have ht : 3*(c*(c+1)*(c+2)/3) = c*(c+1)*(c+2) := by
    have h := Nat.mod_add_div (c*(c+1)*(c+2)) 3
    rwa [cubic_mod_three, zero_add] at h
  have hB2 : (B^2-1)%3 = 0 := by
    have h : B^2 % 3 = 1 := by
      rw [pow_two, Nat.mul_mod]
      rcases pow_mod_three a with h | h <;> change B%3 = _ at h <;> simp [h]
    omega
  have hm : 3*((B^2-1)/3) = B^2-1 := by
    have h := Nat.mod_add_div (B^2-1) 3
    rwa [hB2, zero_add] at h
  have hidentity :
      (B-c)*(B-c-1)*(B-c-2) + 3*((c+1)*B*B) + c*(c+1)*(c+2) =
        ((B^2-1)+3*(c+1)^2)*B := by
    apply Int.ofNat_inj.mp
    have hBsq : 0 < B^2 := by positivity
    push_cast [Nat.cast_sub (show c ≤ B by omega), Nat.cast_sub (show 1 ≤ B-c by omega),
      Nat.cast_sub (show 2 ≤ B-c by omega), Nat.cast_sub (show 1 ≤ B^2 by omega)]
    ring
  apply Nat.eq_of_mul_eq_mul_left (show 0 < 3 by decide)
  calc
    _ = (B-c)*(B-c-1)*(B-c-2) + 3*((c+1)*B*B) + c*(c+1)*(c+2) := by
      rw [Nat.mul_add, Nat.mul_add, hprod, ht]
    _ = ((B^2-1)+3*(c+1)^2)*B := hidentity
    _ = _ := by rw [← Nat.mul_assoc, Nat.mul_add, hm]

private lemma cubic_blocks (a c : ℕ) (hc : c+2 ≤ 2^a) :
    let B := 2^a
    let t := c*(c+1)*(c+2)/3
    let q := (t+B-1)/B
    let r := B-1-(t+B-1)%B
    let h := ((B^2-1)/3+(c+1)^2)-((c+1)*B+q)
    (Nat.digits 2 ((B-c).choose 3)).count 1 =
      (Nat.digits 2 (h/B)).count 1 + (Nat.digits 2 (h%B)).count 1 + (Nat.digits 2 r).count 1 := by
  dsimp only
  let B := 2^a
  let t := c*(c+1)*(c+2)/3
  let q := (t+B-1)/B
  let r := B-1-(t+B-1)%B
  let m := (B^2-1)/3+(c+1)^2
  let h := m-((c+1)*B+q)
  have hB : 0 < B := by dsimp [B]; positivity
  have hr : r < B := by dsimp [r]; omega
  have hqr : q*B = t+r := by
    have hd := Nat.mod_add_div (t+B-1) B
    have hl := Nat.mod_lt (t+B-1) hB
    rw [Nat.mul_comm B] at hd
    dsimp [q,r]
    omega
  let C := (B-c).choose 3
  have hs : 2*C + (c+1)*B*B + t = m*B := cubic_scaled a c hc
  have he : 2*C + ((c+1)*B+q)*B = m*B+r := by
    rw [Nat.add_mul, hqr]
    omega
  have hl : (c+1)*B+q ≤ m := by
    by_contra! hn
    have hh := Nat.mul_le_mul_right B hn
    rw [Nat.succ_mul] at hh
    omega
  have hdecomp : 2*C = h*B+r := by
    have hh : m*B = h*B + ((c+1)*B+q)*B := by
      rw [← Nat.add_mul, Nat.sub_add_cancel hl]
    omega
  change (Nat.digits 2 C).count 1 = (Nat.digits 2 (h/B)).count 1 + (Nat.digits 2 (h%B)).count 1 + (Nat.digits 2 r).count 1
  have hh := Nat.div_add_mod' h B
  calc
    (Nat.digits 2 C).count 1 = (Nat.digits 2 (2*C)).count 1 := (even_digits_double C).symm
    _ = (Nat.digits 2 (h*B+r)).count 1 := congrArg (fun n => (Nat.digits 2 n).count 1) hdecomp
    _ = (Nat.digits 2 h).count 1 + (Nat.digits 2 r).count 1 := count_ones_append h a r hr
    _ = (Nat.digits 2 (h/B)).count 1 + (Nat.digits 2 (h%B)).count 1 + (Nat.digits 2 r).count 1 := by
      congr 1
      conv_lhs => rw [← hh]
      exact count_ones_append (h/B) a (h%B) (Nat.mod_lt h hB)

private lemma separated_bounds (a c : ℕ)
    (h : c*(c+1)*(c+2)+3*(c+1)^2 ≤ 2^a) :
    let B := 2^a
    let U := B/3
    let V := ((B%3)*B-1)/3
    let t := c*(c+1)*(c+2)/3
    c+1 ≤ U ∧ V+(c+1)^2-1 < B ∧ t ≤ B := by
  dsimp only
  let B := 2^a
  change _ ≤ B at h
  change c+1 ≤ B/3 ∧ ((B%3)*B-1)/3+(c+1)^2-1 < B ∧ _ ≤ B
  have hB : 0 < B := by dsimp [B]; positivity
  have hpow : c+1 ≤ (c+1)^2 := by nlinarith
  have hv := Nat.mul_le_mul_right B (show B%3 ≤ 2 by omega)
  omega

private lemma cubic_separated (a c : ℕ)
    (hcpos : 1 < c) (h : c*(c+1)*(c+2)+3*(c+1)^2 ≤ 2^a) :
    let B := 2^a
    let U := B/3
    let V := ((B%3)*B-1)/3
    let t := c*(c+1)*(c+2)/3
    (Nat.digits 2 ((B-c).choose 3)).count 1 = (Nat.digits 2 (U-(c+1))).count 1 + (Nat.digits 2 (V+(c+1)^2-1)).count 1 + (Nat.digits 2 (B-t)).count 1 := by
  dsimp only
  let B := 2^a
  let U := B/3
  let V := ((B%3)*B-1)/3
  let s := c+1
  let t := c*s*(c+2)/3
  change _ ≤ B at h
  change (Nat.digits 2 ((B-c).choose 3)).count 1 = (Nat.digits 2 (U-s)).count 1 + (Nat.digits 2 (V+s^2-1)).count 1 + (Nat.digits 2 (B-t)).count 1
  obtain ⟨hu, hv, ht⟩ := separated_bounds a c h
  change s ≤ U at hu
  change V+s^2-1 < B at hv
  change t ≤ B at ht
  have hB : 0 < B := by dsimp [B]; positivity
  have hf : B%3 * B > 0 := by
    rcases pow_mod_three a with h₁ | h₂
    · change B%3 = 1 at h₁
      simpa [h₁] using hB
    · change B%3 = 2 at h₂
      rw [h₂]; omega
  have hUV : (B^2-1)/3 = U*B+V := by
    have hf' := Nat.mod_add_div B 3
    have he : B^2-1 = (B%3*B-1)+3*(U*B) := by
      have hm := congrArg (· * B) hf'
      simp only [Nat.add_mul, Nat.mul_assoc, ← pow_two] at hm
      change B%3*B+3*(U*B) = B^2 at hm
      omega
    rw [he, Nat.add_mul_div_left _ _ (by decide : 0 < 3)]
    exact Nat.add_comm _ _
  have hpow : c+1 ≤ (c+1)^2 := by nlinarith
  have hc : c+2 ≤ B := by omega
  have hsc : 2*(B-c).choose 3+s*B*B+t = ((B^2-1)/3+s^2)*B :=
    cubic_scaled a c hc
  have hdecomp : 2*(B-c).choose 3 = ((U-s)*B+(V+s^2-1))*B+(B-t) := by
    have hu' : U*B = (U-s)*B+s*B := by rw [← Nat.add_mul, Nat.sub_add_cancel hu]
    have h' : (B^2-1)/3+s^2 = ((U-s)*B+(V+s^2-1))+(s*B+1) := by
      rw [hUV, hu']
      have hs : 1 ≤ s^2 := by dsimp [s]; omega
      omega
    have hh : ((B^2-1)/3+s^2)*B =
      ((U-s)*B+(V+s^2-1))*B+(s*B*B+B) := by
      calc
        _ = (((U-s)*B+(V+s^2-1))+(s*B+1))*B := congrArg (· * B) h'
        _ = _ := by rw [add_mul _ (s*B+1), add_mul (s*B) 1, one_mul]
    rw [hh] at hsc
    omega
  have htpos : 0 < t := by
    have hp := cubic_mod_three c
    have he := Nat.mod_add_div (c*(c+1)*(c+2)) 3
    have hn : 0 < c*(c+1)*(c+2) := by positivity
    change _ < c*(c+1)*(c+2)/3
    omega
  calc
    _ = (Nat.digits 2 (2*(B-c).choose 3)).count 1 := (even_digits_double _).symm
    _ = (Nat.digits 2 (((U-s)*B+(V+s^2-1))*B+(B-t))).count 1 := congrArg (fun n => (Nat.digits 2 n).count 1) hdecomp
    _ = _ := by
        rw [show (Nat.digits 2 (((U-s)*B+(V+s^2-1))*B+(B-t))).count 1 =
          (Nat.digits 2 ((U-s)*B+(V+s^2-1))).count 1 + (Nat.digits 2 (B-t)).count 1 from
          count_ones_append _ a _ (show B-t < B by omega),
          show (Nat.digits 2 ((U-s)*B+(V+s^2-1))).count 1 = (Nat.digits 2 (U-s)).count 1+(Nat.digits 2 (V+s^2-1)).count 1 from
          count_ones_append _ a _ hv]

private lemma cubic_period_two (a c : ℕ) (hc : 1 < c)
    (h : c*(c+1)*(c+2)+3*(c+1)^2 ≤ 2^a) :
    (Nat.digits 2 ((2^(a+2)-c).choose 3)).count 1 % 2 = (Nat.digits 2 ((2^a-c).choose 3)).count 1 % 2 := by
  let B := 2^a
  let U := B/3
  let V := ((B%3)*B-1)/3
  let s := c+1
  let t := c*s*(c+2)/3
  have hB : 0 < B := by dsimp [B]; positivity
  have hb : 2^(a+2) = 4*B := by rw [pow_add]; change B*4=4*B; omega
  have h' : c*(c+1)*(c+2)+3*(c+1)^2 ≤ 2^(a+2) := by
    rw [hb]
    change _ ≤ B at h
    omega
  obtain ⟨hu, hv, ht⟩ := separated_bounds a c h
  change s ≤ U at hu
  change V+s^2-1 < B at hv
  change t ≤ B at ht
  have hU : (4*B)/3 = B+U := by dsimp [U]; omega
  have hV : (((4*B)%3)*(4*B)-1)/3 = (B%3)*B+V := by
    rw [show (4*B)%3 = B%3 by omega]
    rcases pow_mod_three a with h₁ | h₂
    · change B%3 = 1 at h₁
      simp only [V, h₁, one_mul]
      omega
    · change B%3 = 2 at h₂
      simp only [V, h₂]
      omega
  have hlow : B-t < B := by
    have hp := cubic_mod_three c
    have he := Nat.mod_add_div (c*(c+1)*(c+2)) 3
    have hn : 0 < c*(c+1)*(c+2) := by positivity
    dsimp [t,s]
    omega
  have hhigh : U-s < B := by dsimp [U]; omega
  have h1 : (Nat.digits 2 ((2^(a+2)-c).choose 3)).count 1 =
      (Nat.digits 2 ((B+U)-s)).count 1 + (Nat.digits 2 ((B%3)*B+V+s^2-1)).count 1 + (Nat.digits 2 (4*B-t)).count 1 := by
    have hh := cubic_separated (a+2) c hc h'
    dsimp only at hh
    rw [hb, hU, hV] at hh
    simpa only [hb] using hh
  have h2 : (Nat.digits 2 ((2^a-c).choose 3)).count 1 = (Nat.digits 2 (U-s)).count 1 + (Nat.digits 2 (V+s^2-1)).count 1 + (Nat.digits 2 (B-t)).count 1 :=
    cubic_separated a c hc h
  have hH : (Nat.digits 2 ((B+U)-s)).count 1 = 1 + (Nat.digits 2 (U-s)).count 1 := by
    have hh := count_ones_append 1 a (U-s) hhigh
    change (Nat.digits 2 (1*B+(U-s))).count 1 = 1 + (Nat.digits 2 (U-s)).count 1 at hh
    rwa [one_mul, ← Nat.add_sub_assoc hu] at hh
  have hM : (Nat.digits 2 ((B%3)*B+V+s^2-1)).count 1 = 1 + (Nat.digits 2 (V+s^2-1)).count 1 := by
    have hh := count_ones_append (B%3) a (V+s^2-1) hv
    have hpos : 0 < s^2 := by dsimp [s]; positivity
    have he : (B%3)*B+(V+s^2-1) = (B%3)*B+V+s^2-1 := by omega
    change (Nat.digits 2 ((B%3)*B+(V+s^2-1))).count 1 = (Nat.digits 2 (B%3)).count 1 + (Nat.digits 2 (V+s^2-1)).count 1 at hh
    have hon : (Nat.digits 2 (B%3)).count 1 = 1 := by
      rcases pow_mod_three a with h₁ | h₂
      · change B%3 = 1 at h₁
        rw [h₁]; decide
      · change B%3 = 2 at h₂
        rw [h₂]; decide
    -- Rewrite the two arguments to the digit count, without expanding the digits.
    simpa only [he, hon] using hh
  have hL : (Nat.digits 2 (4*B-t)).count 1 = 2 + (Nat.digits 2 (B-t)).count 1 := by
    have hh := count_ones_append 3 a (B-t) hlow
    change (Nat.digits 2 (3*B+(B-t))).count 1 = 2 + (Nat.digits 2 (B-t)).count 1 at hh
    rwa [show 3*B+(B-t)=4*B-t by omega] at hh
  have eq : (Nat.digits 2 ((2^(a+2)-c).choose 3)).count 1 = (Nat.digits 2 ((2^a-c).choose 3)).count 1 + 4 := by
    calc
      _ = _ := h1
      _ = _ := by
        rw [h2]
        -- The three extra blocks contain one, one, and two one-bits.
        omega
  omega

private lemma threshold_rep (a T : ℕ) (ht : 0 < T) (h : T ≤ 2^a) :
    ∃ b j : ℕ, a = b+2*j ∧ T ≤ 2^b ∧ 2^b < 4*T := by
  induction a using Nat.strong_induction_on with
  | h a ih =>
    by_cases hl : 2^a < 4*T
    · exact ⟨a, 0, by simp, h, hl⟩
    have ha : 2 ≤ a := by
      by_contra! ha
      interval_cases a <;> norm_num at hl <;> omega
    let d := a-2
    have he : 2^a = 4*2^d := by
      have hd : a = d+2 := by dsimp [d]; omega
      calc
        _ = 2^(d+2) := congrArg (2^·) hd
        _ = _ := by rw [pow_add]; ring
    have hd : T ≤ 2^d := by omega
    obtain ⟨b,j,hb,hb₁,hb₂⟩ := ih d (by dsimp [d]; omega) hd
    exact ⟨b,j+1,by dsimp [d] at hb; omega,hb₁,hb₂⟩

private lemma periodic_rep (b j c : ℕ) (hc : 1 < c)
    (h : c*(c+1)*(c+2)+3*(c+1)^2 ≤ 2^b) :
    (Nat.digits 2 ((2^(b+2*j)-c).choose 3)).count 1 % 2 = (Nat.digits 2 ((2^b-c).choose 3)).count 1 % 2 := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hle : c*(c+1)*(c+2)+3*(c+1)^2 ≤ 2^(b+2*j) :=
      h.trans (Nat.pow_le_pow_right (by decide) (by omega))
    rw [show b+2*(j+1) = (b+2*j)+2 by omega]
    exact (cubic_period_two (b+2*j) c hc hle).trans ih

private lemma row_parity (a c : ℕ) (hc : Odd c) (hle : c ≤ 2^a)
    (hrow : OeisA249609.isEvil (2^a-c) = false) :
    a % 2 = (Nat.digits 2 c).count 1 % 2 := by
  have hh := complement a (2^a-c) (c-1) (by have := Nat.odd_iff.mp hc; omega)
  have hpos := Nat.odd_iff.mp hc
  have h₁ := half c
  have h₂ := half (c-1)
  rw [show (c-1)/2=c/2 by omega] at h₂
  have hr : (Nat.digits 2 (2^a-c)).count 1 % 2 = 1 := by
    simp only [OeisA249609.isEvil, beq_eq_false_iff_ne] at hrow
    omega
  omega

/-- Between the quadratic and cubic bounds, carries can cross the blocks.
Only odd values of the displayed three-block sum still need a witness. -/
def H1 : Prop :=
  ∀ a c : ℕ, 1 < c → Odd c → a % 2 = (Nat.digits 2 c).count 1 % 2 →
    c*(c+1) < 2^a → 2^a < c*(c+1)*(c+2)+3*(c+1)^2 →
    OeisA249609.isEvil (c*(c+1)) = false →
    let B := 2^a
    let t := c*(c+1)*(c+2)/3
    let q := (t+B-1)/B
    let r := B-1-(t+B-1)%B
    let h := ((B^2-1)/3+(c+1)^2)-((c+1)*B+q)
    ((Nat.digits 2 (h/B)).count 1 + (Nat.digits 2 (h%B)).count 1 + (Nat.digits 2 r).count 1) % 2 = 1 →
    ∃ k ∈ List.range' 1 (B-c), OeisA249609.isEvil ((B-c).choose k) = true

/-- Above the cubic bound, test the least width of the required parity.
The exceptional defects are selected once for the entire progression. -/
def H2 : Prop :=
  ∀ b c : ℕ, 1 < c → Odd c → b % 2 = (Nat.digits 2 c).count 1 % 2 →
    c*(c+1)*(c+2)+3*(c+1)^2 ≤ 2^b →
    2^b < 4*(c*(c+1)*(c+2)+3*(c+1)^2) →
    OeisA249609.isEvil (c*(c+1)) = false →
    let B := 2^b
    let U := B/3
    let V := ((B%3)*B-1)/3
    let t := c*(c+1)*(c+2)/3
    ((Nat.digits 2 (U-(c+1))).count 1 + (Nat.digits 2 (V+(c+1)^2-1)).count 1 + (Nat.digits 2 (B-t)).count 1) % 2 = 1 →
    ∀ j : ℕ, ∃ k ∈ List.range' 1 (2^(b+2*j)-c),
      OeisA249609.isEvil ((2^(b+2*j)-c).choose k) = true

theorem main : H1 → H2 → OMA.R_OeisA249609_conjecture_R1_H2_R1_H1_R1.H2 := by
  intro near far e c hc _ hodd hquad hprod hrow
  let a := e+1
  let T := c*(c+1)*(c+2)+3*(c+1)^2
  change c*(c+1) < 2^a at hquad
  change OeisA249609.isEvil (2^a-c) = false at hrow
  have hs : c+3 ≤ 2^a := by
    have hp : c*2 ≤ c*(c+1) := Nat.mul_le_mul_left c (by omega)
    omega
  have hpar := row_parity a c hodd (by omega) hrow
  have h3 (h : (Nat.digits 2 ((2^a-c).choose 3)).count 1 % 2 = 0) :
      ∃ k ∈ List.range' 1 (2^a-c), OeisA249609.isEvil ((2^a-c).choose k) = true := by
    refine ⟨3, List.mem_range'_1.mpr ⟨by decide, by omega⟩, ?_⟩
    simpa only [OeisA249609.isEvil, beq_iff_eq] using h
  by_cases hb : T ≤ 2^a
  · have ht : 0 < T := by dsimp [T]; positivity
    obtain ⟨b,j,he,hb₁,hb₂⟩ := threshold_rep a T ht hb
    have hbp : b%2 = (Nat.digits 2 c).count 1%2 := by omega
    by_cases heven : (Nat.digits 2 ((2^b-c).choose 3)).count 1 % 2 = 0
    · apply h3
      rw [he]
      exact (periodic_rep b j c hc hb₁).trans heven
    · rw [show e+1 = b+2*j from he]
      apply far b c hc hodd hbp hb₁ hb₂ hprod _ j
      have hn : (Nat.digits 2 ((2^b-c).choose 3)).count 1 % 2 = 1 := by omega
      rw [cubic_separated b c hc hb₁] at hn
      exact hn
  · by_cases heven : (Nat.digits 2 ((2^a-c).choose 3)).count 1 % 2 = 0
    · exact h3 heven
    · apply near a c hc hodd hpar hquad (by omega : 2^a < T) hprod
      have hn : (Nat.digits 2 ((2^a-c).choose 3)).count 1 % 2 = 1 := by omega
      rw [cubic_blocks a c (by omega)] at hn
      exact hn

end OMA.R_OeisA249609_conjecture_R1_H2_R1_H1_R1_H2_R1
