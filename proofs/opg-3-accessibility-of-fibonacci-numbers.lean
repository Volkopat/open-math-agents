import OMAStatements.S_opg_3_accessibility_of_fibonacci_numbers

-- Problem: 3-accessibility of Fibonacci numbers
-- Credit: @Ciphore (the owner of the agent is credited as the solver)

noncomputable section

namespace FibonacciAccessibility


def phi : ℝ := (1 + Real.sqrt 5) / 2
def psi : ℝ := (1 - Real.sqrt 5) / 2
def alpha : ℝ := 184 + 8 * phi

lemma psi_sq : psi ^ 2 = psi + 1 := by
  rw [psi]
  have hs : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  ring_nf at hs ⊢
  nlinarith

lemma phi_fib (n : ℕ) : phi * (Nat.fib n : ℝ) = Nat.fib (n+1) - psi ^ n := by
  induction n using Nat.twoStepInduction with
  | zero => simp [phi, psi]
  | one =>
      simp [phi, psi]
      ring
  | more n ih0 ih1 =>
      rw [Nat.fib_add_two]
      push_cast
      rw [show (n+1+1:ℕ) = n+2 by omega]
      rw [show (n+2:ℕ)+1 = n+3 by omega]
      have hps : psi ^ (n+2) = psi ^ (n+1) + psi ^ n := by
        rw [pow_add, pow_add, psi_sq]
        ring
      calc
        phi * ((Nat.fib n : ℝ) + Nat.fib (n+1)) = phi * (Nat.fib n : ℝ) + phi * (Nat.fib (n+1) : ℝ) := by ring
        _ = (Nat.fib (n+1) - psi ^ n) + (Nat.fib (n+2) - psi ^ (n+1)) := by rw [ih0, ih1]
        _ = Nat.fib (n+3) - psi ^ (n+2) := by
          rw [show Nat.fib (n+3) = Nat.fib (n+1) + Nat.fib (n+2) by
            rw [show n+3 = n+1+2 by omega, Nat.fib_add_two]]
          rw [hps]
          push_cast
          ring

lemma alpha_fib (n : ℕ) : alpha * (Nat.fib n : ℝ) =
    184 * (Nat.fib n : ℝ) + 8 * (Nat.fib (n+1) : ℝ) - 8 * psi ^ n := by
  rw [alpha]
  ring_nf
  rw [phi_fib n]
  ring_nf


lemma sqrt5_lt_nine_quarters : Real.sqrt 5 < (9 / 4 : ℝ) := by
  rw [Real.sqrt_lt' (by norm_num)]
  norm_num

lemma one_lt_sqrt5 : (1 : ℝ) < Real.sqrt 5 := by
  rw [Real.lt_sqrt (by norm_num)]
  norm_num

lemma psi_abs_le_five_eighths : |psi| ≤ (5 / 8 : ℝ) := by
  have hneg : psi < 0 := by
    rw [psi]
    have h1 := one_lt_sqrt5
    linarith
  rw [abs_of_neg hneg, psi]
  have h9 := sqrt5_lt_nine_quarters
  linarith

lemma eight_psi_pow_abs_lt_one (n : ℕ) (hn : 5 ≤ n) : |8 * psi ^ n| < (1 : ℝ) := by
  have hpowle : |psi| ^ n ≤ (5 / 8 : ℝ) ^ n :=
    pow_le_pow_left₀ (abs_nonneg _) psi_abs_le_five_eighths n
  have hpow5 : (5 / 8 : ℝ) ^ n ≤ (5 / 8 : ℝ) ^ 5 :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hn
  rw [abs_mul, abs_pow]
  norm_num
  nlinarith [hpowle, hpow5]


def Afib (n : ℕ) : ℤ := 184 * Nat.fib n + 8 * Nat.fib (n+1)

lemma floor_alpha_fib_large (n : ℕ) (hn : 5 ≤ n) :
    ⌊alpha * (Nat.fib n : ℝ)⌋ = Afib n - 1 ∨ ⌊alpha * (Nat.fib n : ℝ)⌋ = Afib n := by
  have hid := alpha_fib n
  have hb := abs_lt.mp (eight_psi_pow_abs_lt_one n hn)
  have hupper : alpha * (Nat.fib n : ℝ) < (Afib n : ℝ) + 1 := by
    rw [hid]
    simp [Afib]
    linarith
  have hlower : (Afib n : ℝ) - 1 < alpha * (Nat.fib n : ℝ) := by
    rw [hid]
    simp [Afib]
    linarith
  have hle : ⌊alpha * (Nat.fib n : ℝ)⌋ ≤ Afib n := by
    have hh : ⌊alpha * (Nat.fib n : ℝ)⌋ < Afib n + 1 := by
      rw [Int.floor_lt]
      simpa using hupper
    omega
  have hge : Afib n - 1 ≤ ⌊alpha * (Nat.fib n : ℝ)⌋ := by
    have hhreal : (Afib n : ℝ) - 1 < (⌊alpha * (Nat.fib n : ℝ)⌋ : ℝ) + 1 := by
      have hfloor := Int.lt_floor_add_one (alpha * (Nat.fib n : ℝ))
      linarith
    have hh : Afib n - 1 < ⌊alpha * (Nat.fib n : ℝ)⌋ + 1 := by
      exact_mod_cast hhreal
    omega
  omega

lemma floor_add_cases (x y : ℝ) :
    ⌊x + y⌋ - ⌊x⌋ = ⌊y⌋ ∨ ⌊x + y⌋ - ⌊x⌋ = ⌊y⌋ + 1 := by
  have h1 := Int.le_floor_add x y
  have h2 := Int.le_floor_add_floor x y
  omega


lemma Afib_add_two (n : ℕ) : Afib (n+2) = Afib (n+1) + Afib n := by
  simp [Afib, Nat.fib_add_two]
  ring

lemma Afib_period_pair (n : ℕ) :
    (Afib (n+7) : ZMod 232) = Afib n ∧ (Afib (n+8) : ZMod 232) = Afib (n+1) := by
  induction n with
  | zero =>
      decide +kernel
  | succ n ih =>
      constructor
      · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih.2
      · have h1 : Afib (n+9) = Afib (n+8) + Afib (n+7) := by
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using Afib_add_two (n+7)
        have h2 : Afib (n+2) = Afib (n+1) + Afib n := Afib_add_two n
        calc
          (Afib ((n+1)+8) : ZMod 232) = Afib (n+9) := by congr 1
          _ = Afib (n+8) + Afib (n+7) := by simp [h1]
          _ = Afib (n+1) + Afib n := by rw [ih.2, ih.1]
          _ = Afib ((n+1)+1) := by
            rw [show (n+1)+1 = n+2 by omega, h2]
            simp

lemma Afib_period_mul (n q : ℕ) : (Afib (n + 7*q) : ZMod 232) = Afib n := by
  induction q with
  | zero => simp
  | succ q ih =>
      calc
        (Afib (n + 7*(q+1)) : ZMod 232) = Afib ((n + 7*q)+7) := by congr 1
        _ = Afib (n + 7*q) := (Afib_period_pair (n+7*q)).1
        _ = Afib n := ih

lemma Afib_zmod_mem_orbit (n : ℕ) :
    (Afib n : ZMod 232) ∈ ({8,56,128,160,184,192,200} : Finset (ZMod 232)) := by
  have hn : n % 7 + 7 * (n / 7) = n := Nat.mod_add_div n 7
  have hr : n % 7 < 7 := Nat.mod_lt n (by norm_num)
  rw [← hn]
  rw [Afib_period_mul]
  interval_cases n % 7 <;> decide +kernel


lemma alpha_eq : alpha = 188 + 4 * Real.sqrt 5 := by
  rw [alpha, phi]
  ring

lemma sqrt5_lower : (223 / 100 : ℝ) < Real.sqrt 5 := by
  rw [Real.lt_sqrt (by norm_num)]
  norm_num

lemma sqrt5_upper : Real.sqrt 5 < (9 / 4 : ℝ) := sqrt5_lt_nine_quarters

lemma floor_alpha_one : ⌊alpha⌋ = 196 := by
  rw [Int.floor_eq_iff]
  constructor
  · change (196 : ℝ) ≤ alpha
    rw [alpha_eq]
    linarith [sqrt5_lower]
  · have hb : alpha < (197 : ℝ) := by
      rw [alpha_eq]
      linarith [sqrt5_upper]
    norm_num
    exact hb

lemma floor_two_alpha : ⌊2 * alpha⌋ = 393 := by
  rw [Int.floor_eq_iff]
  constructor
  · change (393 : ℝ) ≤ 2 * alpha
    rw [alpha_eq]
    linarith [sqrt5_lower]
  · have hb : 2 * alpha < (394 : ℝ) := by
      rw [alpha_eq]
      linarith [sqrt5_upper]
    norm_num
    exact hb

lemma floor_three_alpha : ⌊3 * alpha⌋ = 590 := by
  rw [Int.floor_eq_iff]
  constructor
  · change (590 : ℝ) ≤ 3 * alpha
    rw [alpha_eq]
    linarith [sqrt5_lower]
  · have hb : 3 * alpha < (591 : ℝ) := by
      rw [alpha_eq]
      linarith [sqrt5_upper]
    norm_num
    exact hb


def orbitZ : Finset (ZMod 232) := {8,56,128,160,184,192,200}
def shiftZ : Finset (ZMod 232) := {7,8,9,55,56,57,126,127,128,129,159,160,161,162,183,184,185,191,192,193,196,197,199,200,201}

lemma orbit_mem_shift {z : ZMod 232} (hz : z ∈ orbitZ) : z ∈ shiftZ := by
  fin_cases hz <;> decide +kernel
lemma orbit_sub_one_mem_shift {z : ZMod 232} (hz : z ∈ orbitZ) : z - 1 ∈ shiftZ := by
  fin_cases hz <;> decide +kernel
lemma orbit_add_one_mem_shift {z : ZMod 232} (hz : z ∈ orbitZ) : z + 1 ∈ shiftZ := by
  fin_cases hz <;> decide +kernel

lemma floor_alpha_fib_large_zmod (n : ℕ) (hn : 5 ≤ n) :
    ((⌊alpha * (Nat.fib n : ℝ)⌋ : ZMod 232) ∈ shiftZ) ∧
    ((⌊alpha * (Nat.fib n : ℝ)⌋ + 1 : ZMod 232) ∈ shiftZ) := by
  have ho := orbit_mem_shift (Afib_zmod_mem_orbit n)
  have hosub := orbit_sub_one_mem_shift (Afib_zmod_mem_orbit n)
  have hoadd := orbit_add_one_mem_shift (Afib_zmod_mem_orbit n)
  rcases floor_alpha_fib_large n hn with hf | hf
  · constructor
    · have hz : (⌊alpha * (Nat.fib n : ℝ)⌋ : ZMod 232) = (Afib n : ZMod 232) - 1 := by
        have hzi : ((⌊alpha * (Nat.fib n : ℝ)⌋ : ℤ) : ZMod 232) = ((Afib n - 1 : ℤ) : ZMod 232) := by rw [hf]
        simpa using hzi
      rw [hz]
      exact hosub
    · have h : ⌊alpha * (Nat.fib n : ℝ)⌋ + 1 = Afib n := by omega
      have hz : (⌊alpha * (Nat.fib n : ℝ)⌋ : ZMod 232) + 1 = (Afib n : ZMod 232) := by
        have hzi : ((⌊alpha * (Nat.fib n : ℝ)⌋ + 1 : ℤ) : ZMod 232) = ((Afib n : ℤ) : ZMod 232) := by rw [h]
        simpa using hzi
      rw [hz]
      exact ho
  · constructor
    · rw [hf]
      exact ho
    · have h : ⌊alpha * (Nat.fib n : ℝ)⌋ + 1 = Afib n + 1 := by omega
      have hz : (⌊alpha * (Nat.fib n : ℝ)⌋ : ZMod 232) + 1 = (Afib n : ZMod 232) + 1 := by
        have hzi : ((⌊alpha * (Nat.fib n : ℝ)⌋ + 1 : ℤ) : ZMod 232) = ((Afib n + 1 : ℤ) : ZMod 232) := by rw [h]
        simpa using hzi
      rw [hz]
      exact hoadd

lemma floor_alpha_fib_small_zmod (n : ℕ) (h1 : 1 ≤ n) (h4 : n ≤ 4) :
    ((⌊alpha * (Nat.fib n : ℝ)⌋ : ZMod 232) ∈ shiftZ) ∧
    ((⌊alpha * (Nat.fib n : ℝ)⌋ + 1 : ZMod 232) ∈ shiftZ) := by
  interval_cases n
  · have hf : ⌊alpha * (Nat.fib 1 : ℝ)⌋ = 196 := by
      simpa using floor_alpha_one
    constructor <;> rw [hf] <;> decide +kernel
  · have hf : ⌊alpha * (Nat.fib 2 : ℝ)⌋ = 196 := by
      simpa using floor_alpha_one
    constructor <;> rw [hf] <;> decide +kernel
  · have hf : ⌊alpha * (Nat.fib 3 : ℝ)⌋ = 393 := by
      have h : alpha * (Nat.fib 3 : ℝ) = 2 * alpha := by norm_num [Nat.fib]; ring
      rw [h]
      exact floor_two_alpha
    constructor <;> rw [hf] <;> decide +kernel
  · have hf : ⌊alpha * (Nat.fib 4 : ℝ)⌋ = 590 := by
      have h : alpha * (Nat.fib 4 : ℝ) = 3 * alpha := by norm_num [Nat.fib]; ring
      rw [h]
      exact floor_three_alpha
    constructor <;> rw [hf] <;> decide +kernel

lemma floor_alpha_fib_zmod (n : ℕ) (hn : 1 ≤ n) :
    ((⌊alpha * (Nat.fib n : ℝ)⌋ : ZMod 232) ∈ shiftZ) ∧
    ((⌊alpha * (Nat.fib n : ℝ)⌋ + 1 : ZMod 232) ∈ shiftZ) := by
  by_cases h4 : n ≤ 4
  · exact floor_alpha_fib_small_zmod n hn h4
  · exact floor_alpha_fib_large_zmod n (by omega)


def shiftN : Finset ℕ := {7,8,9,55,56,57,126,127,128,129,159,160,161,162,183,184,185,191,192,193,196,197,199,200,201}

noncomputable def rhoZ (n : ℕ) : ZMod 232 := ⌊alpha * (n : ℝ)⌋

def rhoVal (n : ℕ) : ℕ := (rhoZ n).val

lemma rhoZ_lt (n : ℕ) : rhoVal n < 232 := ZMod.val_lt _

lemma rhoVal_lt (n : ℕ) : rhoVal n < 232 := rhoZ_lt n

lemma rho_step_zmod (x n : ℕ) (hn : 1 ≤ n) :
    rhoZ (x + Nat.fib n) - rhoZ x ∈ shiftZ := by
  have hf := floor_alpha_fib_zmod n hn
  have hadd : alpha * ((x + Nat.fib n : ℕ) : ℝ) = alpha * (x : ℝ) + alpha * (Nat.fib n : ℝ) := by
    push_cast
    ring
  have hcases := floor_add_cases (alpha * (x : ℝ)) (alpha * (Nat.fib n : ℝ))
  dsimp [rhoZ]
  rw [hadd]
  rcases hcases with h | h
  · have hz : ((⌊alpha * (x : ℝ) + alpha * (Nat.fib n : ℝ)⌋ : ZMod 232) -
        (⌊alpha * (x : ℝ)⌋ : ZMod 232)) = (⌊alpha * (Nat.fib n : ℝ)⌋ : ZMod 232) := by
      have hzi : (((⌊alpha * (x : ℝ) + alpha * (Nat.fib n : ℝ)⌋ - ⌊alpha * (x : ℝ)⌋) : ℤ) : ZMod 232) =
          ((⌊alpha * (Nat.fib n : ℝ)⌋ : ℤ) : ZMod 232) := by rw [h]
      simpa using hzi
    rw [hz]
    exact hf.1
  · have hz : ((⌊alpha * (x : ℝ) + alpha * (Nat.fib n : ℝ)⌋ : ZMod 232) -
        (⌊alpha * (x : ℝ)⌋ : ZMod 232)) = (⌊alpha * (Nat.fib n : ℝ)⌋ : ZMod 232) + 1 := by
      have hzi : (((⌊alpha * (x : ℝ) + alpha * (Nat.fib n : ℝ)⌋ - ⌊alpha * (x : ℝ)⌋) : ℤ) : ZMod 232) =
          ((⌊alpha * (Nat.fib n : ℝ)⌋ + 1 : ℤ) : ZMod 232) := by rw [h]
      simpa using hzi
    rw [hz]
    exact hf.2

lemma shiftZ_mem_cases {z : ZMod 232} (hz : z ∈ shiftZ) :
    ∃ s ∈ shiftN, (s : ZMod 232) = z := by
  refine ⟨z.val, ?_, ?_⟩
  · fin_cases hz <;> decide +kernel
  · fin_cases hz <;> decide +kernel

lemma shiftN_lt_232 : ∀ s : shiftN, s.val < 232 := by
  decide +kernel

lemma rho_step_nat (x n : ℕ) (hn : 1 ≤ n) :
    ∃ s ∈ shiftN, rhoVal (x + Nat.fib n) = (rhoVal x + s) % 232 := by
  let z := rhoZ (x + Nat.fib n) - rhoZ x
  have hzmem : z ∈ shiftZ := rho_step_zmod x n hn
  rcases shiftZ_mem_cases hzmem with ⟨s, hsS, hsz⟩
  refine ⟨s, hsS, ?_⟩
  have hdiff : rhoZ (x + Nat.fib n) - rhoZ x = (s : ZMod 232) := hsz.symm
  have hadd : rhoZ (x + Nat.fib n) = rhoZ x + (s : ZMod 232) := by
    rw [← hdiff]
    ring
  have hsval : ((s : ZMod 232).val) = s := ZMod.val_cast_of_lt (shiftN_lt_232 ⟨s, hsS⟩)
  calc
    rhoVal (x + Nat.fib n) = (rhoZ x + (s : ZMod 232)).val := by rw [rhoVal, hadd]
    _ = ((rhoZ x).val + (s : ZMod 232).val) % 232 := ZMod.val_add _ _
    _ = (rhoVal x + s) % 232 := by rw [hsval, rhoVal]

def colorOfVal (v : ℕ) : Fin 3 :=
  if v ≤ 24 then (0 : Fin 3) else if v ≤ 40 then (2 : Fin 3) else if v ≤ 55 then (1 : Fin 3) else if v ≤ 67 then (2 : Fin 3) else if v ≤ 68 then (0 : Fin 3) else if v ≤ 86 then (2 : Fin 3) else if v ≤ 98 then (0 : Fin 3) else if v ≤ 116 then (2 : Fin 3) else if v ≤ 124 then (1 : Fin 3) else if v ≤ 126 then (0 : Fin 3) else if v ≤ 143 then (1 : Fin 3) else if v ≤ 147 then (2 : Fin 3) else if v ≤ 155 then (0 : Fin 3) else if v ≤ 186 then (1 : Fin 3) else if v ≤ 196 then (0 : Fin 3) else if v ≤ 199 then (2 : Fin 3) else if v ≤ 217 then (0 : Fin 3) else if v ≤ 224 then (1 : Fin 3) else if v ≤ 230 then (2 : Fin 3) else (0 : Fin 3)

def rankList : List ℕ := [18,15,17,17,17,17,17,17,13,13,14,15,15,15,8,10,10,10,10,9,7,7,7,6,3,6,5,4,4,4,4,4,3,2,2,2,2,2,2,2,1,14,14,14,10,10,10,9,7,7,7,6,5,5,4,3,10,10,10,10,10,10,7,8,8,8,8,8,14,6,6,6,7,7,7,6,5,5,5,5,5,4,3,3,3,3,3,11,11,11,11,11,10,8,8,8,7,4,3,12,12,12,12,12,11,11,11,11,11,11,11,9,9,9,9,9,9,11,11,11,10,8,8,8,7,12,12,5,4,3,3,2,1,1,1,1,1,0,0,0,0,0,0,0,13,12,13,13,6,5,2,2,2,2,2,2,17,17,17,14,14,16,16,16,16,16,13,13,13,13,9,9,9,8,6,6,6,5,4,4,3,2,2,2,2,2,1,16,16,16,16,12,12,12,12,13,13,0,0,0,9,9,8,5,4,1,1,1,1,1,1,0,0,0,0,0,0,0,15,15,15,12,12,12,12,0,0,0,1,1,1,18]

def rankOfVal (v : ℕ) : ℕ := rankList.getD v 0

theorem rank_drop_all :
    ∀ v : Fin 232, ∀ s : shiftN,
      colorOfVal ((v.val + s.val) % 232) = colorOfVal v.val →
      rankOfVal ((v.val + s.val) % 232) < rankOfVal v.val := by
  decide +kernel

theorem rank_bound_all : ∀ v : Fin 232, rankOfVal v.val ≤ 18 := by
  decide +kernel



lemma chain20_false (r0 : ℕ) (r1 : ℕ) (r2 : ℕ) (r3 : ℕ) (r4 : ℕ) (r5 : ℕ) (r6 : ℕ) (r7 : ℕ) (r8 : ℕ) (r9 : ℕ) (r10 : ℕ) (r11 : ℕ) (r12 : ℕ) (r13 : ℕ) (r14 : ℕ) (r15 : ℕ) (r16 : ℕ) (r17 : ℕ) (r18 : ℕ) (r19 : ℕ) (hb : r0 ≤ 18) (hr0 : r1 < r0) (hr1 : r2 < r1) (hr2 : r3 < r2) (hr3 : r4 < r3) (hr4 : r5 < r4) (hr5 : r6 < r5) (hr6 : r7 < r6) (hr7 : r8 < r7) (hr8 : r9 < r8) (hr9 : r10 < r9) (hr10 : r11 < r10) (hr11 : r12 < r11) (hr12 : r13 < r12) (hr13 : r14 < r13) (hr14 : r15 < r14) (hr15 : r16 < r15) (hr16 : r17 < r16) (hr17 : r18 < r17) (hr18 : r19 < r18) : False := by
  omega


def chi (n : ℕ) : Fin 3 := colorOfVal (rhoVal n)

end FibonacciAccessibility

open FibonacciAccessibility

theorem OMA.disproof : ¬ (type_of% @OMA.S_opg_3_accessibility_of_fibonacci_numbers.main) := by
  intro hmain
  rcases hmain chi 20 (by norm_num) with ⟨x, hxpos, hcol, hstep⟩
  have ht0 := hstep ⟨0, by norm_num⟩ (by norm_num)
  rcases ht0.2 with ⟨n0, hn0ge, hn0eq⟩
  rcases rho_step_nat (x ⟨0, by norm_num⟩) n0 hn0ge with ⟨s0, hs0S, hs0eq⟩
  have hxnext0 : x ⟨1, by norm_num⟩ = x ⟨0, by norm_num⟩ + Nat.fib n0 := by
    have hlt := ht0.1
    rw [hn0eq, Nat.add_comm]
    exact (Nat.sub_add_cancel hlt.le).symm
  rw [← hxnext0] at hs0eq
  have hc0 : colorOfVal ((rhoVal (x ⟨0, by norm_num⟩) + s0) % 232) = colorOfVal (rhoVal (x ⟨0, by norm_num⟩)) := by
    rw [← hs0eq]
    exact (hcol ⟨0, by norm_num⟩ ⟨1, by norm_num⟩).symm
  have hdrop0 := rank_drop_all ⟨rhoVal (x ⟨0, by norm_num⟩), rhoVal_lt _⟩ ⟨s0, hs0S⟩ hc0
  rw [← hs0eq] at hdrop0
  have ht1 := hstep ⟨1, by norm_num⟩ (by norm_num)
  rcases ht1.2 with ⟨n1, hn1ge, hn1eq⟩
  rcases rho_step_nat (x ⟨1, by norm_num⟩) n1 hn1ge with ⟨s1, hs1S, hs1eq⟩
  have hxnext1 : x ⟨2, by norm_num⟩ = x ⟨1, by norm_num⟩ + Nat.fib n1 := by
    have hlt := ht1.1
    rw [hn1eq, Nat.add_comm]
    exact (Nat.sub_add_cancel hlt.le).symm
  rw [← hxnext1] at hs1eq
  have hc1 : colorOfVal ((rhoVal (x ⟨1, by norm_num⟩) + s1) % 232) = colorOfVal (rhoVal (x ⟨1, by norm_num⟩)) := by
    rw [← hs1eq]
    exact (hcol ⟨1, by norm_num⟩ ⟨2, by norm_num⟩).symm
  have hdrop1 := rank_drop_all ⟨rhoVal (x ⟨1, by norm_num⟩), rhoVal_lt _⟩ ⟨s1, hs1S⟩ hc1
  rw [← hs1eq] at hdrop1
  have ht2 := hstep ⟨2, by norm_num⟩ (by norm_num)
  rcases ht2.2 with ⟨n2, hn2ge, hn2eq⟩
  rcases rho_step_nat (x ⟨2, by norm_num⟩) n2 hn2ge with ⟨s2, hs2S, hs2eq⟩
  have hxnext2 : x ⟨3, by norm_num⟩ = x ⟨2, by norm_num⟩ + Nat.fib n2 := by
    have hlt := ht2.1
    rw [hn2eq, Nat.add_comm]
    exact (Nat.sub_add_cancel hlt.le).symm
  rw [← hxnext2] at hs2eq
  have hc2 : colorOfVal ((rhoVal (x ⟨2, by norm_num⟩) + s2) % 232) = colorOfVal (rhoVal (x ⟨2, by norm_num⟩)) := by
    rw [← hs2eq]
    exact (hcol ⟨2, by norm_num⟩ ⟨3, by norm_num⟩).symm
  have hdrop2 := rank_drop_all ⟨rhoVal (x ⟨2, by norm_num⟩), rhoVal_lt _⟩ ⟨s2, hs2S⟩ hc2
  rw [← hs2eq] at hdrop2
  have ht3 := hstep ⟨3, by norm_num⟩ (by norm_num)
  rcases ht3.2 with ⟨n3, hn3ge, hn3eq⟩
  rcases rho_step_nat (x ⟨3, by norm_num⟩) n3 hn3ge with ⟨s3, hs3S, hs3eq⟩
  have hxnext3 : x ⟨4, by norm_num⟩ = x ⟨3, by norm_num⟩ + Nat.fib n3 := by
    have hlt := ht3.1
    rw [hn3eq, Nat.add_comm]
    exact (Nat.sub_add_cancel hlt.le).symm
  rw [← hxnext3] at hs3eq
  have hc3 : colorOfVal ((rhoVal (x ⟨3, by norm_num⟩) + s3) % 232) = colorOfVal (rhoVal (x ⟨3, by norm_num⟩)) := by
    rw [← hs3eq]
    exact (hcol ⟨3, by norm_num⟩ ⟨4, by norm_num⟩).symm
  have hdrop3 := rank_drop_all ⟨rhoVal (x ⟨3, by norm_num⟩), rhoVal_lt _⟩ ⟨s3, hs3S⟩ hc3
  rw [← hs3eq] at hdrop3
  have ht4 := hstep ⟨4, by norm_num⟩ (by norm_num)
  rcases ht4.2 with ⟨n4, hn4ge, hn4eq⟩
  rcases rho_step_nat (x ⟨4, by norm_num⟩) n4 hn4ge with ⟨s4, hs4S, hs4eq⟩
  have hxnext4 : x ⟨5, by norm_num⟩ = x ⟨4, by norm_num⟩ + Nat.fib n4 := by
    have hlt := ht4.1
    rw [hn4eq, Nat.add_comm]
    exact (Nat.sub_add_cancel hlt.le).symm
  rw [← hxnext4] at hs4eq
  have hc4 : colorOfVal ((rhoVal (x ⟨4, by norm_num⟩) + s4) % 232) = colorOfVal (rhoVal (x ⟨4, by norm_num⟩)) := by
    rw [← hs4eq]
    exact (hcol ⟨4, by norm_num⟩ ⟨5, by norm_num⟩).symm
  have hdrop4 := rank_drop_all ⟨rhoVal (x ⟨4, by norm_num⟩), rhoVal_lt _⟩ ⟨s4, hs4S⟩ hc4
  rw [← hs4eq] at hdrop4
  have ht5 := hstep ⟨5, by norm_num⟩ (by norm_num)
  rcases ht5.2 with ⟨n5, hn5ge, hn5eq⟩
  rcases rho_step_nat (x ⟨5, by norm_num⟩) n5 hn5ge with ⟨s5, hs5S, hs5eq⟩
  have hxnext5 : x ⟨6, by norm_num⟩ = x ⟨5, by norm_num⟩ + Nat.fib n5 := by
    have hlt := ht5.1
    rw [hn5eq, Nat.add_comm]
    exact (Nat.sub_add_cancel hlt.le).symm
  rw [← hxnext5] at hs5eq
  have hc5 : colorOfVal ((rhoVal (x ⟨5, by norm_num⟩) + s5) % 232) = colorOfVal (rhoVal (x ⟨5, by norm_num⟩)) := by
    rw [← hs5eq]
    exact (hcol ⟨5, by norm_num⟩ ⟨6, by norm_num⟩).symm
  have hdrop5 := rank_drop_all ⟨rhoVal (x ⟨5, by norm_num⟩), rhoVal_lt _⟩ ⟨s5, hs5S⟩ hc5
  rw [← hs5eq] at hdrop5
  have ht6 := hstep ⟨6, by norm_num⟩ (by norm_num)
  rcases ht6.2 with ⟨n6, hn6ge, hn6eq⟩
  rcases rho_step_nat (x ⟨6, by norm_num⟩) n6 hn6ge with ⟨s6, hs6S, hs6eq⟩
  have hxnext6 : x ⟨7, by norm_num⟩ = x ⟨6, by norm_num⟩ + Nat.fib n6 := by
    have hlt := ht6.1
    rw [hn6eq, Nat.add_comm]
    exact (Nat.sub_add_cancel hlt.le).symm
  rw [← hxnext6] at hs6eq
  have hc6 : colorOfVal ((rhoVal (x ⟨6, by norm_num⟩) + s6) % 232) = colorOfVal (rhoVal (x ⟨6, by norm_num⟩)) := by
    rw [← hs6eq]
    exact (hcol ⟨6, by norm_num⟩ ⟨7, by norm_num⟩).symm
  have hdrop6 := rank_drop_all ⟨rhoVal (x ⟨6, by norm_num⟩), rhoVal_lt _⟩ ⟨s6, hs6S⟩ hc6
  rw [← hs6eq] at hdrop6
  have ht7 := hstep ⟨7, by norm_num⟩ (by norm_num)
  rcases ht7.2 with ⟨n7, hn7ge, hn7eq⟩
  rcases rho_step_nat (x ⟨7, by norm_num⟩) n7 hn7ge with ⟨s7, hs7S, hs7eq⟩
  have hxnext7 : x ⟨8, by norm_num⟩ = x ⟨7, by norm_num⟩ + Nat.fib n7 := by
    have hlt := ht7.1
    rw [hn7eq, Nat.add_comm]
    exact (Nat.sub_add_cancel hlt.le).symm
  rw [← hxnext7] at hs7eq
  have hc7 : colorOfVal ((rhoVal (x ⟨7, by norm_num⟩) + s7) % 232) = colorOfVal (rhoVal (x ⟨7, by norm_num⟩)) := by
    rw [← hs7eq]
    exact (hcol ⟨7, by norm_num⟩ ⟨8, by norm_num⟩).symm
  have hdrop7 := rank_drop_all ⟨rhoVal (x ⟨7, by norm_num⟩), rhoVal_lt _⟩ ⟨s7, hs7S⟩ hc7
  rw [← hs7eq] at hdrop7
  have ht8 := hstep ⟨8, by norm_num⟩ (by norm_num)
  rcases ht8.2 with ⟨n8, hn8ge, hn8eq⟩
  rcases rho_step_nat (x ⟨8, by norm_num⟩) n8 hn8ge with ⟨s8, hs8S, hs8eq⟩
  have hxnext8 : x ⟨9, by norm_num⟩ = x ⟨8, by norm_num⟩ + Nat.fib n8 := by
    have hlt := ht8.1
    rw [hn8eq, Nat.add_comm]
    exact (Nat.sub_add_cancel hlt.le).symm
  rw [← hxnext8] at hs8eq
  have hc8 : colorOfVal ((rhoVal (x ⟨8, by norm_num⟩) + s8) % 232) = colorOfVal (rhoVal (x ⟨8, by norm_num⟩)) := by
    rw [← hs8eq]
    exact (hcol ⟨8, by norm_num⟩ ⟨9, by norm_num⟩).symm
  have hdrop8 := rank_drop_all ⟨rhoVal (x ⟨8, by norm_num⟩), rhoVal_lt _⟩ ⟨s8, hs8S⟩ hc8
  rw [← hs8eq] at hdrop8
  have ht9 := hstep ⟨9, by norm_num⟩ (by norm_num)
  rcases ht9.2 with ⟨n9, hn9ge, hn9eq⟩
  rcases rho_step_nat (x ⟨9, by norm_num⟩) n9 hn9ge with ⟨s9, hs9S, hs9eq⟩
  have hxnext9 : x ⟨10, by norm_num⟩ = x ⟨9, by norm_num⟩ + Nat.fib n9 := by
    have hlt := ht9.1
    rw [hn9eq, Nat.add_comm]
    exact (Nat.sub_add_cancel hlt.le).symm
  rw [← hxnext9] at hs9eq
  have hc9 : colorOfVal ((rhoVal (x ⟨9, by norm_num⟩) + s9) % 232) = colorOfVal (rhoVal (x ⟨9, by norm_num⟩)) := by
    rw [← hs9eq]
    exact (hcol ⟨9, by norm_num⟩ ⟨10, by norm_num⟩).symm
  have hdrop9 := rank_drop_all ⟨rhoVal (x ⟨9, by norm_num⟩), rhoVal_lt _⟩ ⟨s9, hs9S⟩ hc9
  rw [← hs9eq] at hdrop9
  have ht10 := hstep ⟨10, by norm_num⟩ (by norm_num)
  rcases ht10.2 with ⟨n10, hn10ge, hn10eq⟩
  rcases rho_step_nat (x ⟨10, by norm_num⟩) n10 hn10ge with ⟨s10, hs10S, hs10eq⟩
  have hxnext10 : x ⟨11, by norm_num⟩ = x ⟨10, by norm_num⟩ + Nat.fib n10 := by
    have hlt := ht10.1
    rw [hn10eq, Nat.add_comm]
    exact (Nat.sub_add_cancel hlt.le).symm
  rw [← hxnext10] at hs10eq
  have hc10 : colorOfVal ((rhoVal (x ⟨10, by norm_num⟩) + s10) % 232) = colorOfVal (rhoVal (x ⟨10, by norm_num⟩)) := by
    rw [← hs10eq]
    exact (hcol ⟨10, by norm_num⟩ ⟨11, by norm_num⟩).symm
  have hdrop10 := rank_drop_all ⟨rhoVal (x ⟨10, by norm_num⟩), rhoVal_lt _⟩ ⟨s10, hs10S⟩ hc10
  rw [← hs10eq] at hdrop10
  have ht11 := hstep ⟨11, by norm_num⟩ (by norm_num)
  rcases ht11.2 with ⟨n11, hn11ge, hn11eq⟩
  rcases rho_step_nat (x ⟨11, by norm_num⟩) n11 hn11ge with ⟨s11, hs11S, hs11eq⟩
  have hxnext11 : x ⟨12, by norm_num⟩ = x ⟨11, by norm_num⟩ + Nat.fib n11 := by
    have hlt := ht11.1
    rw [hn11eq, Nat.add_comm]
    exact (Nat.sub_add_cancel hlt.le).symm
  rw [← hxnext11] at hs11eq
  have hc11 : colorOfVal ((rhoVal (x ⟨11, by norm_num⟩) + s11) % 232) = colorOfVal (rhoVal (x ⟨11, by norm_num⟩)) := by
    rw [← hs11eq]
    exact (hcol ⟨11, by norm_num⟩ ⟨12, by norm_num⟩).symm
  have hdrop11 := rank_drop_all ⟨rhoVal (x ⟨11, by norm_num⟩), rhoVal_lt _⟩ ⟨s11, hs11S⟩ hc11
  rw [← hs11eq] at hdrop11
  have ht12 := hstep ⟨12, by norm_num⟩ (by norm_num)
  rcases ht12.2 with ⟨n12, hn12ge, hn12eq⟩
  rcases rho_step_nat (x ⟨12, by norm_num⟩) n12 hn12ge with ⟨s12, hs12S, hs12eq⟩
  have hxnext12 : x ⟨13, by norm_num⟩ = x ⟨12, by norm_num⟩ + Nat.fib n12 := by
    have hlt := ht12.1
    rw [hn12eq, Nat.add_comm]
    exact (Nat.sub_add_cancel hlt.le).symm
  rw [← hxnext12] at hs12eq
  have hc12 : colorOfVal ((rhoVal (x ⟨12, by norm_num⟩) + s12) % 232) = colorOfVal (rhoVal (x ⟨12, by norm_num⟩)) := by
    rw [← hs12eq]
    exact (hcol ⟨12, by norm_num⟩ ⟨13, by norm_num⟩).symm
  have hdrop12 := rank_drop_all ⟨rhoVal (x ⟨12, by norm_num⟩), rhoVal_lt _⟩ ⟨s12, hs12S⟩ hc12
  rw [← hs12eq] at hdrop12
  have ht13 := hstep ⟨13, by norm_num⟩ (by norm_num)
  rcases ht13.2 with ⟨n13, hn13ge, hn13eq⟩
  rcases rho_step_nat (x ⟨13, by norm_num⟩) n13 hn13ge with ⟨s13, hs13S, hs13eq⟩
  have hxnext13 : x ⟨14, by norm_num⟩ = x ⟨13, by norm_num⟩ + Nat.fib n13 := by
    have hlt := ht13.1
    rw [hn13eq, Nat.add_comm]
    exact (Nat.sub_add_cancel hlt.le).symm
  rw [← hxnext13] at hs13eq
  have hc13 : colorOfVal ((rhoVal (x ⟨13, by norm_num⟩) + s13) % 232) = colorOfVal (rhoVal (x ⟨13, by norm_num⟩)) := by
    rw [← hs13eq]
    exact (hcol ⟨13, by norm_num⟩ ⟨14, by norm_num⟩).symm
  have hdrop13 := rank_drop_all ⟨rhoVal (x ⟨13, by norm_num⟩), rhoVal_lt _⟩ ⟨s13, hs13S⟩ hc13
  rw [← hs13eq] at hdrop13
  have ht14 := hstep ⟨14, by norm_num⟩ (by norm_num)
  rcases ht14.2 with ⟨n14, hn14ge, hn14eq⟩
  rcases rho_step_nat (x ⟨14, by norm_num⟩) n14 hn14ge with ⟨s14, hs14S, hs14eq⟩
  have hxnext14 : x ⟨15, by norm_num⟩ = x ⟨14, by norm_num⟩ + Nat.fib n14 := by
    have hlt := ht14.1
    rw [hn14eq, Nat.add_comm]
    exact (Nat.sub_add_cancel hlt.le).symm
  rw [← hxnext14] at hs14eq
  have hc14 : colorOfVal ((rhoVal (x ⟨14, by norm_num⟩) + s14) % 232) = colorOfVal (rhoVal (x ⟨14, by norm_num⟩)) := by
    rw [← hs14eq]
    exact (hcol ⟨14, by norm_num⟩ ⟨15, by norm_num⟩).symm
  have hdrop14 := rank_drop_all ⟨rhoVal (x ⟨14, by norm_num⟩), rhoVal_lt _⟩ ⟨s14, hs14S⟩ hc14
  rw [← hs14eq] at hdrop14
  have ht15 := hstep ⟨15, by norm_num⟩ (by norm_num)
  rcases ht15.2 with ⟨n15, hn15ge, hn15eq⟩
  rcases rho_step_nat (x ⟨15, by norm_num⟩) n15 hn15ge with ⟨s15, hs15S, hs15eq⟩
  have hxnext15 : x ⟨16, by norm_num⟩ = x ⟨15, by norm_num⟩ + Nat.fib n15 := by
    have hlt := ht15.1
    rw [hn15eq, Nat.add_comm]
    exact (Nat.sub_add_cancel hlt.le).symm
  rw [← hxnext15] at hs15eq
  have hc15 : colorOfVal ((rhoVal (x ⟨15, by norm_num⟩) + s15) % 232) = colorOfVal (rhoVal (x ⟨15, by norm_num⟩)) := by
    rw [← hs15eq]
    exact (hcol ⟨15, by norm_num⟩ ⟨16, by norm_num⟩).symm
  have hdrop15 := rank_drop_all ⟨rhoVal (x ⟨15, by norm_num⟩), rhoVal_lt _⟩ ⟨s15, hs15S⟩ hc15
  rw [← hs15eq] at hdrop15
  have ht16 := hstep ⟨16, by norm_num⟩ (by norm_num)
  rcases ht16.2 with ⟨n16, hn16ge, hn16eq⟩
  rcases rho_step_nat (x ⟨16, by norm_num⟩) n16 hn16ge with ⟨s16, hs16S, hs16eq⟩
  have hxnext16 : x ⟨17, by norm_num⟩ = x ⟨16, by norm_num⟩ + Nat.fib n16 := by
    have hlt := ht16.1
    rw [hn16eq, Nat.add_comm]
    exact (Nat.sub_add_cancel hlt.le).symm
  rw [← hxnext16] at hs16eq
  have hc16 : colorOfVal ((rhoVal (x ⟨16, by norm_num⟩) + s16) % 232) = colorOfVal (rhoVal (x ⟨16, by norm_num⟩)) := by
    rw [← hs16eq]
    exact (hcol ⟨16, by norm_num⟩ ⟨17, by norm_num⟩).symm
  have hdrop16 := rank_drop_all ⟨rhoVal (x ⟨16, by norm_num⟩), rhoVal_lt _⟩ ⟨s16, hs16S⟩ hc16
  rw [← hs16eq] at hdrop16
  have ht17 := hstep ⟨17, by norm_num⟩ (by norm_num)
  rcases ht17.2 with ⟨n17, hn17ge, hn17eq⟩
  rcases rho_step_nat (x ⟨17, by norm_num⟩) n17 hn17ge with ⟨s17, hs17S, hs17eq⟩
  have hxnext17 : x ⟨18, by norm_num⟩ = x ⟨17, by norm_num⟩ + Nat.fib n17 := by
    have hlt := ht17.1
    rw [hn17eq, Nat.add_comm]
    exact (Nat.sub_add_cancel hlt.le).symm
  rw [← hxnext17] at hs17eq
  have hc17 : colorOfVal ((rhoVal (x ⟨17, by norm_num⟩) + s17) % 232) = colorOfVal (rhoVal (x ⟨17, by norm_num⟩)) := by
    rw [← hs17eq]
    exact (hcol ⟨17, by norm_num⟩ ⟨18, by norm_num⟩).symm
  have hdrop17 := rank_drop_all ⟨rhoVal (x ⟨17, by norm_num⟩), rhoVal_lt _⟩ ⟨s17, hs17S⟩ hc17
  rw [← hs17eq] at hdrop17
  have ht18 := hstep ⟨18, by norm_num⟩ (by norm_num)
  rcases ht18.2 with ⟨n18, hn18ge, hn18eq⟩
  rcases rho_step_nat (x ⟨18, by norm_num⟩) n18 hn18ge with ⟨s18, hs18S, hs18eq⟩
  have hxnext18 : x ⟨19, by norm_num⟩ = x ⟨18, by norm_num⟩ + Nat.fib n18 := by
    have hlt := ht18.1
    rw [hn18eq, Nat.add_comm]
    exact (Nat.sub_add_cancel hlt.le).symm
  rw [← hxnext18] at hs18eq
  have hc18 : colorOfVal ((rhoVal (x ⟨18, by norm_num⟩) + s18) % 232) = colorOfVal (rhoVal (x ⟨18, by norm_num⟩)) := by
    rw [← hs18eq]
    exact (hcol ⟨18, by norm_num⟩ ⟨19, by norm_num⟩).symm
  have hdrop18 := rank_drop_all ⟨rhoVal (x ⟨18, by norm_num⟩), rhoVal_lt _⟩ ⟨s18, hs18S⟩ hc18
  rw [← hs18eq] at hdrop18
  clear hxpos hcol hstep ht0 n0 hn0ge hn0eq s0 hs0S hs0eq hxnext0 hc0 ht1 n1 hn1ge hn1eq s1 hs1S hs1eq hxnext1 hc1 ht2 n2 hn2ge hn2eq s2 hs2S hs2eq hxnext2 hc2 ht3 n3 hn3ge hn3eq s3 hs3S hs3eq hxnext3 hc3 ht4 n4 hn4ge hn4eq s4 hs4S hs4eq hxnext4 hc4 ht5 n5 hn5ge hn5eq s5 hs5S hs5eq hxnext5 hc5 ht6 n6 hn6ge hn6eq s6 hs6S hs6eq hxnext6 hc6 ht7 n7 hn7ge hn7eq s7 hs7S hs7eq hxnext7 hc7 ht8 n8 hn8ge hn8eq s8 hs8S hs8eq hxnext8 hc8 ht9 n9 hn9ge hn9eq s9 hs9S hs9eq hxnext9 hc9 ht10 n10 hn10ge hn10eq s10 hs10S hs10eq hxnext10 hc10 ht11 n11 hn11ge hn11eq s11 hs11S hs11eq hxnext11 hc11 ht12 n12 hn12ge hn12eq s12 hs12S hs12eq hxnext12 hc12 ht13 n13 hn13ge hn13eq s13 hs13S hs13eq hxnext13 hc13 ht14 n14 hn14ge hn14eq s14 hs14S hs14eq hxnext14 hc14 ht15 n15 hn15ge hn15eq s15 hs15S hs15eq hxnext15 hc15 ht16 n16 hn16ge hn16eq s16 hs16S hs16eq hxnext16 hc16 ht17 n17 hn17ge hn17eq s17 hs17S hs17eq hxnext17 hc17 ht18 n18 hn18ge hn18eq s18 hs18S hs18eq hxnext18 hc18
  have hb0 := rank_bound_all ⟨rhoVal (x ⟨0, by norm_num⟩), rhoVal_lt _⟩
  exact chain20_false (rankOfVal (rhoVal (x ⟨0, by norm_num⟩))) (rankOfVal (rhoVal (x ⟨1, by norm_num⟩))) (rankOfVal (rhoVal (x ⟨2, by norm_num⟩))) (rankOfVal (rhoVal (x ⟨3, by norm_num⟩))) (rankOfVal (rhoVal (x ⟨4, by norm_num⟩))) (rankOfVal (rhoVal (x ⟨5, by norm_num⟩))) (rankOfVal (rhoVal (x ⟨6, by norm_num⟩))) (rankOfVal (rhoVal (x ⟨7, by norm_num⟩))) (rankOfVal (rhoVal (x ⟨8, by norm_num⟩))) (rankOfVal (rhoVal (x ⟨9, by norm_num⟩))) (rankOfVal (rhoVal (x ⟨10, by norm_num⟩))) (rankOfVal (rhoVal (x ⟨11, by norm_num⟩))) (rankOfVal (rhoVal (x ⟨12, by norm_num⟩))) (rankOfVal (rhoVal (x ⟨13, by norm_num⟩))) (rankOfVal (rhoVal (x ⟨14, by norm_num⟩))) (rankOfVal (rhoVal (x ⟨15, by norm_num⟩))) (rankOfVal (rhoVal (x ⟨16, by norm_num⟩))) (rankOfVal (rhoVal (x ⟨17, by norm_num⟩))) (rankOfVal (rhoVal (x ⟨18, by norm_num⟩))) (rankOfVal (rhoVal (x ⟨19, by norm_num⟩))) hb0 hdrop0 hdrop1 hdrop2 hdrop3 hdrop4 hdrop5 hdrop6 hdrop7 hdrop8 hdrop9 hdrop10 hdrop11 hdrop12 hdrop13 hdrop14 hdrop15 hdrop16 hdrop17 hdrop18



