import OMAReductions.R_Arxiv_1601_03081_crystals_components_unique_R1_H1_R1_H2_R1_H1_R1

-- Reduction Arxiv.1601.03081.crystals_components_unique.R1.H1.R1.H2.R1.H1.R1.H1.R1 of step Arxiv.1601.03081.crystals_components_unique.R1.H1.R1.H2.R1.H1.R1.H1
-- Credit: @KeystoneScience

/-! A multiplier bound and a checked obstruction for the odd-parameter quotient-four branch. -/

namespace CrystalMultiplier

theorem resultant {a c m q : ℤ}
    (factor : m * c + 1 ∣ (a - 1) ^ 2)
    (quotient : (c + m * a) ^ 2 = q * ((c + 1) * (m * a + 1))) :
    m * c + 1 ∣ ((m ^ 2 - 1) * (m ^ 2 - q * m - 1)) ^ 2 := by
  let left := -(m * c + 1 + 2 * (m ^ 2 * a - 1) - q * m * (m * a + 1))
  let right := -(m ^ 2 * ((m ^ 2 * a - 1) + (m ^ 2 - 1)) - q * m ^ 2 * (m - 1))
  have identity : (m ^ 2 - 1) * (m ^ 2 - q * m - 1) =
      (m * c + 1) * left + (a - 1) * right := by
    dsimp [left, right]
    linear_combination m ^ 2 * quotient
  obtain ⟨witness, hwitness⟩ := factor
  refine ⟨(m * c + 1) * left ^ 2 + 2 * left * (a - 1) * right + witness * right ^ 2, ?_⟩
  rw [identity]
  linear_combination right ^ 2 * hwitness

theorem four_bound {a c m t : ℕ} (multiplier : 21 ≤ m)
    (components : (c + m * a) ^ 2 = 4 * ((c + 1) * (m * a + 1)))
    (square : c + 1 = 2 * t ^ 2)
    (factor : ((m * c : ℕ) : ℤ) + 1 ∣ ((a : ℤ) - 1) ^ 2) :
    (m : ℤ) * (2 * (t : ℤ) ^ 2 - 1) + 1 ≤
      (((m : ℤ) ^ 2 - 1) * ((m : ℤ) ^ 2 - 4 * m - 1)) ^ 2 := by
  have factor' : (m : ℤ) * c + 1 ∣ ((a : ℤ) - 1) ^ 2 := by push_cast at factor; exact factor
  have components' : ((c : ℤ) + m * a) ^ 2 = 4 * ((c + 1) * (m * a + 1)) := by
    exact_mod_cast components
  have sq' : (c : ℤ) + 1 = 2 * (t : ℤ) ^ 2 := by exact_mod_cast square
  have ml : (21 : ℤ) ≤ m := by exact_mod_cast multiplier
  have pos₁ : 0 < (m : ℤ)^2-1 := by nlinarith
  have pos₂ : 0 < (m : ℤ)^2-4*m-1 := by nlinarith [sq_nonneg ((m:ℤ)-4)]
  have positive : 0 < (((m : ℤ)^2-1)*((m:ℤ)^2-4*m-1))^2 := by positivity
  rw [show 2 * (t : ℤ) ^ 2 - 1 = c by linarith]
  exact Int.le_of_dvd positive (resultant factor' components')

private theorem big_margin {m t : ℕ} (hm : 21 ≤ m) (ht : 4*m^2 ≤ t) :
    m*(m*(4*t+2)+3*(m^2+1)) < 2*(t+1)^2 := by
  obtain ⟨slack, rfl⟩ := Nat.exists_eq_add_of_le ht
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le hm
  ring_nf
  omega

set_option maxHeartbeats 2200000 in
theorem quotient_gap {a c m p t : ℕ} (hm : 21 ≤ m)
    (first : (a + m * c) ^ 2 = p*((a+1)*(m*c+1)))
    (left : c + 1 = 2 * t ^ 2) (right : m * a + 1 = 2 * (t+1)^2)
    (upper : (m : ℤ)*(2*(t : ℤ)^2-1)+1 ≤
      (((m : ℤ)^2-1)*((m : ℤ)^2-4*m-1))^2) : t < 4*m^2 := by
  by_contra! high
  have margin := big_margin hm high
  have margin' : m*(4*t+2)+3*(m^2+1) ≤ a := by
    exact Nat.le_of_mul_le_mul_left (show m*(m*(4*t+2)+3*(m^2+1)) ≤ m*a by omega) (by omega)
  have hmz : (21:ℤ) ≤ m := by exact_mod_cast hm
  have ht : (4:ℤ)*(m:ℤ)^2 ≤ t := by exact_mod_cast high
  have htz : (3:ℤ) ≤ t := by nlinarith [sq_nonneg ((m:ℤ)-5)]
  have lz : (c:ℤ)+1 = 2*(t:ℤ)^2 := by exact_mod_cast left
  have rz : (m:ℤ)*a+1 = 2*((t:ℤ)+1)^2 := by exact_mod_cast right
  have fz : ((a:ℤ)+m*c)^2 = (p:ℤ)*((a+1)*(m*c+1)) := by exact_mod_cast first
  have az : (m:ℤ)*(4*t+2)+3*((m:ℤ)^2+1) ≤ a := by exact_mod_cast margin'
  have delta : (m:ℤ)*c = (m:ℤ)^2*a - m*(4*t+2) := by
    linear_combination (m:ℤ) * lz - m * rz
  have aa : 0 < (a:ℤ) := by nlinarith [mul_nonneg (show (0:ℤ) ≤ m by omega) (show (0:ℤ) ≤ 4*t+2 by omega)]
  have ca : (a:ℤ)+1 ≤ (m:ℤ)*c := by
    have bc : (m:ℤ)*a ≤ 2*c := by nlinarith [mul_nonneg (show (0:ℤ) ≤ t-3 by omega) (show (0:ℤ) ≤ t by omega)]
    nlinarith only [bc, lz, htz, aa, le_mul_of_one_le_left (show (0:ℤ) ≤ c by positivity) (show (1:ℤ) ≤ m by omega),
      mul_nonneg (show (0:ℤ) ≤ (m:ℤ)-3 by omega) (show (0:ℤ) ≤ (a:ℤ)-1 by omega)]
  let b : ℤ := (m:ℤ)*c
  have boundLower : (m:ℤ)^2+1 < p := by
    by_contra! bad
    have lhs := mul_le_mul_of_nonneg_right bad (show 0 ≤ ((a:ℤ)+1)*(b+1) by dsimp [b]; positivity)
    have smallside := mul_le_mul_of_nonneg_left ca (show 0 ≤ (m:ℤ)^2+1 by positivity)
    have excess := mul_le_mul_of_nonneg_right az (show 0 ≤ b by dsimp [b]; positivity)
    have displacement := congrArg (fun x : ℤ => x*b) delta
    change ((a:ℤ)+b)^2 = (p:ℤ)*((a+1)*(b+1)) at fz
    change (a:ℤ)+1 ≤ b at ca
    change ((m:ℤ)^2+1)*((a:ℤ)+1) ≤ ((m:ℤ)^2+1)*b at smallside
    change b*b = ((m:ℤ)^2*a - m*(4*t+2))*b at displacement
    nlinarith only [lhs, fz, excess, displacement, smallside, ca, aa]
  have leading : (0:ℤ) < (m:ℤ)^2-4*m-1 := by nlinarith [sq_nonneg ((m:ℤ)-4)]
  have leading' : (0:ℤ) < (m:ℤ)^2-1 := by nlinarith
  have constlt : ((m:ℤ)^2-1)*((m:ℤ)^2-4*m-1) < (m:ℤ)^4 := by
    calc
      _ < (m:ℤ)^2*(m:ℤ)^2 := mul_lt_mul_of_pos_of_nonneg (by omega) (by omega) (by nlinarith) (by nlinarith)
      _ = _ := by ring
  have short : 2*(t:ℤ) < (m:ℤ)^4 := by
    have x := mul_nonneg (show (0:ℤ) ≤ (m:ℤ)-4 by omega) (show (0:ℤ) ≤ 2*(t:ℤ)^2-1 by nlinarith)
    have u := (sq_lt_sq₀ (by positivity) (by positivity)).2 constlt
    by_contra! bad
    have y := (sq_le_sq₀ (by positivity) (by positivity)).2 bad
    nlinarith only [x, upper, u, y, htz, sq_nonneg ((t:ℤ)-3)]
  have rb : (m:ℤ)*a ≤ 4*(t:ℤ)^2 := by nlinarith [mul_nonneg (show (0:ℤ) ≤ t-3 by omega) (show (0:ℤ) ≤ t by omega)]
  have atwice : 2*(a:ℤ) < m^3*(4*t+2) := by
    have z := mul_lt_mul_of_pos_right short (show (0:ℤ) < 4*t by omega)
    have hpos : (0:ℤ) < m^4 := by positivity
    by_contra! bad
    have bb := mul_le_mul_of_nonneg_left bad (show (0:ℤ) ≤ m by omega)
    nlinarith only [rb, z, bb, hpos]
  have close : (m:ℤ)^2*a ≤ 2*b := by
    have bc : (m:ℤ)*a ≤ 2*c := by nlinarith [mul_nonneg (show (0:ℤ) ≤ t-3 by omega) (show (0:ℤ) ≤ t by omega)]
    have key := mul_le_mul_of_nonneg_left bc (show (0:ℤ) ≤ m by omega)
    dsimp [b]; nlinarith only [key]
  have boundUpper : (p:ℤ) < (m:ℤ)^2+2 := by
    by_contra! bad
    have lhs := mul_le_mul_of_nonneg_right bad (show 0 ≤ ((a:ℤ)+1)*(b+1) by dsimp [b]; positivity)
    have x := mul_lt_mul_of_pos_right atwice aa
    have y := mul_le_mul_of_nonneg_right close (show (0:ℤ) ≤ (m:ℤ)*(4*t+2) by positivity)
    have displacement := congrArg (fun x : ℤ => x*b) delta
    change b*b = ((m:ℤ)^2*a - m*(4*t+2))*b at displacement
    change ((a:ℤ)+b)^2 = (p:ℤ)*((a+1)*(b+1)) at fz
    have pos := mul_nonneg (show (0:ℤ) ≤ (m:ℤ)^2 by positivity) (show 0 ≤ (a:ℤ)+b+1 by dsimp [b]; positivity)
    nlinarith only [lhs, x, y, displacement, fz, pos, aa, ca]
  omega

end CrystalMultiplier

namespace CrystalMultiplier
theorem quartic_certificate {small component multiplier root : ℕ}
    (minimum : 21 ≤ multiplier) (nontrivial : 3 ≤ small)
    (left : component+1 = 2*root^2) (right : multiplier*small+1 = 2*(root+1)^2)
    (cap : root < 4*multiplier^2)
    (factor : ((multiplier*component : ℕ) : ℤ)+1 ∣ ((small : ℤ)-1)^2) :
    (multiplier : ℤ)^3 < 4*((root : ℤ)+1)^2 ∧
    ∃ quotient : ℤ, 1 ≤ quotient ∧ quotient < 64*(multiplier : ℤ) ∧
      (2*((root : ℤ)+1)^2 - ((multiplier : ℤ)+1))^2 =
        quotient*(multiplier : ℤ)^2*((multiplier : ℤ)*(2*(root : ℤ)^2-1)+1) := by
  have productMinimum : 63 ≤ multiplier*small := Nat.mul_le_mul minimum nontrivial
  have rootMinimum : 3 ≤ root := by
    by_contra! low
    have square := Nat.pow_le_pow_left (by omega : root+1 ≤ 3) 2
    omega
  have smallMinimum : (3 : ℤ) ≤ small := by exact_mod_cast nontrivial
  have multiplierPositive : (0 : ℤ) < multiplier := by omega
  have rootMinimum' : (3 : ℤ) ≤ root := by omega
  have smallPositive : (0 : ℤ) < small := by omega
  have left' : (component : ℤ)+1 = 2*(root : ℤ)^2 := by exact_mod_cast left
  have right' : (multiplier : ℤ)*small+1 = 2*((root : ℤ)+1)^2 := by exact_mod_cast right
  push_cast at factor
  obtain ⟨quotient, division⟩ := factor
  have quotientPositive : 0 < quotient := by
    by_contra! nonpositive
    have impossible := mul_nonpos_of_nonneg_of_nonpos
      (show 0 ≤ (multiplier : ℤ)*component+1 by positivity) nonpositive
    nlinarith only [division, impossible, sq_pos_of_pos (show (0 : ℤ) < small-1 by omega)]
  have support : (multiplier : ℤ)*small ≤ 2*component := by
    nlinarith [mul_nonneg (show (0 : ℤ) ≤ root-3 by omega) (show (0 : ℤ) ≤ root by positivity)]
  have support' := mul_le_mul_of_nonneg_left support multiplierPositive.le
  have support'' := mul_le_mul_of_nonneg_left support' quotientPositive.le
  have key : quotient*(multiplier : ℤ)^2 < 2*small := by
    apply (mul_lt_mul_iff_left₀ smallPositive).mp
    nlinarith only [support'', division, smallMinimum, quotientPositive]
  have scaled := mul_lt_mul_of_pos_left key multiplierPositive
  have floorProduct := mul_le_mul_of_nonneg_right (show (1 : ℤ) ≤ quotient by omega)
    (show 0 ≤ (multiplier : ℤ)^2 by positivity)
  have floorScaled := mul_le_mul_of_nonneg_left floorProduct multiplierPositive.le
  have rootCap : (root : ℤ)+1 ≤ 4*(multiplier : ℤ)^2 := by
    exact_mod_cast (show root+1 ≤ 4*multiplier^2 by omega)
  have capSquared := (sq_le_sq₀ (by positivity) (by positivity)).2 rootCap
  refine ⟨by nlinarith only [floorScaled, scaled, right'], quotient, by omega, ?_, ?_⟩
  · apply (mul_lt_mul_iff_left₀ (show 0 < (multiplier : ℤ)^3 by positivity)).mp
    nlinarith only [scaled, right', capSquared]
  · have substitute : 2*((root : ℤ)+1)^2-((multiplier : ℤ)+1) = multiplier*((small : ℤ)-1) := by
      nlinarith only [right']
    rw [substitute, show 2*(root : ℤ)^2-1 = component by linarith only [left'], mul_pow, division]
    ring

theorem dual_resultant {small component multiplier quotient other : ℤ}
    (first : (small+multiplier*component)^2 = other*((small+1)*(multiplier*component+1)))
    (second : (component+multiplier*small)^2 = quotient*((component+1)*(multiplier*small+1))) :
    small+1 ∣ ((multiplier^2-1)*(multiplier^2+quotient*multiplier-1))^2 := by
  let displacement := multiplier*component+multiplier^2*small+1-multiplier^2
  let left := -multiplier^2*displacement+quotient*multiplier^2*(1+multiplier)
  let right := -displacement+quotient*multiplier*(multiplier*small+1)
  have identity : (multiplier^2-1)*(multiplier^2+quotient*multiplier-1) =
      (small+1)*left+(multiplier*component-1)*right := by
    dsimp [left, right, displacement]
    linear_combination multiplier^2 * second
  let lift := other*(multiplier*component+1)-(small+1)-2*(multiplier*component-1)
  have liftSquared : (multiplier*component-1)^2 = (small+1)*lift := by
    dsimp [lift]
    linear_combination first
  refine ⟨(small+1)*left^2+2*left*(multiplier*component-1)*right+lift*right^2, ?_⟩
  rw [identity]
  linear_combination right^2 * liftSquared

end CrystalMultiplier

namespace OMA.R_Arxiv_1601_03081_crystals_components_unique_R1_H1_R1_H2_R1_H1_R1_H1_R1

def H1 : Prop :=
  ∀ a c m t : ℕ, 21 ≤ m → m ≤ 128 → 3 ≤ a →
    (c + m*a)^2 = 4*((c+1)*(m*a+1)) → c+1 = 2*t^2 → m*a+1 = 2*(t+1)^2 →
    ((m*c : ℕ) : ℤ)+1 ∣ ((a : ℤ)-1)^2 → False

def H2 : Prop :=
  ∀ m t : ℕ, 129 ≤ m → Odd m → Odd t → t < 4*m^2 →
    let c := 2*t^2-1
    let b := 2*(t+1)^2-1
    let a := b/m
    m ∣ b → 3 ≤ a → a < c → a.Coprime c → c.Coprime b →
    (∀ ell : ℕ, ell.Prime → ell ∣ m ∨ ell ∣ c ∨ ell ∣ b → ell%8=1 ∨ ell%8=7) →
    c%8=1 ∧ b%8=7 →
    ((m*c : ℕ) : ℤ)+1 ∣ ((a : ℤ)-1)^2 →
    ((m*c : ℕ) : ℤ)+1 ∣ (((m : ℤ)^2-1)*((m : ℤ)^2-4*m-1))^2 →
    (a : ℤ)+1 ∣ (((m : ℤ)^2-1)*((m : ℤ)^2+4*m-1))^2 →
    ((m : ℤ)^3 < 4*((t : ℤ)+1)^2 ∧ ∃ quotient : ℤ, 1 ≤ quotient ∧ quotient < 64*(m : ℤ) ∧
      (2*((t : ℤ)+1)^2-((m : ℤ)+1))^2 = quotient*(m : ℤ)^2*((m : ℤ)*(2*(t : ℤ)^2-1)+1)) →
    16*((a+1)*(m*c+1)) ≤ (a+m*c)^2 →
    ¬ ((a+1)*(m*c+1) ∣ (a+m*c)^2)

theorem main : H1 → H2 → OMA.R_Arxiv_1601_03081_crystals_components_unique_R1_H1_R1_H2_R1_H1_R1.H1 := by
  intro finiteCase remaining a c m p t ordered minimum oddM coprime pairedOrder small large first second left right coprimeOther primeResidues factor quotientLower residues oddT
  have natFactor : ((m*c : ℕ) : ℤ)+1 ∣ ((a : ℤ)-1)^2 := by simpa only [Nat.cast_mul] using factor
  by_cases bounded : m ≤ 128
  · exact finiteCase a c m t minimum bounded small second left right natFactor
  have searchBound := CrystalMultiplier.quotient_gap minimum first left right
    (CrystalMultiplier.four_bound minimum second left natFactor)
  have residual := remaining m t (by omega) oddM oddT searchBound
  dsimp only at residual
  have reconstructLeft : 2*t^2-1 = c := by omega
  have reconstructRight : 2*(t+1)^2-1 = m*a := by omega
  rw [reconstructLeft, reconstructRight, Nat.mul_div_cancel_left _ (show 0 < m by omega)] at residual
  have secondInt : ((c:ℤ)+m*a)^2 = 4*((c+1)*(m*a+1)) := by exact_mod_cast second
  have firstInt : ((a:ℤ)+m*c)^2 = (p:ℤ)*((a+1)*(m*c+1)) := by exact_mod_cast first
  have dual := CrystalMultiplier.dual_resultant firstInt secondInt
  have quartic := CrystalMultiplier.quartic_certificate minimum small left right searchBound natFactor
  have restriction : ((m*c : ℕ):ℤ)+1 ∣ (((m:ℤ)^2-1)*((m:ℤ)^2-4*m-1))^2 := by
    simpa only [Nat.cast_mul] using CrystalMultiplier.resultant factor secondInt
  have lower : 16*((a+1)*(m*c+1)) ≤ (a+m*c)^2 := by
    rw [first]
    exact Nat.mul_le_mul_right _ quotientLower
  exact residual (dvd_mul_right _ _) small ordered coprime coprimeOther primeResidues residues natFactor
    restriction dual quartic lower ⟨p, first.trans (Nat.mul_comm _ _)⟩

end OMA.R_Arxiv_1601_03081_crystals_components_unique_R1_H1_R1_H2_R1_H1_R1_H1_R1
