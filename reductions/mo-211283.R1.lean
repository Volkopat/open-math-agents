import OMAStatements.S_mo_211283
import Mathlib

/-!
# Decimal digit sums of powers

A drop in a subsequence of exponents forces a drop in the full sequence.
After stripping trailing zeros, taking the twelfth power reduces the problem
to the six possible residues 1, 36, 45, 46, 55 and 81 modulo 90.

For bases twice a power of ten, Erick Wong’s six-step residue argument for base two
(https://math.stackexchange.com/questions/560624) gives the explicit interval
bound in two_drop_in_interval below.
-/

namespace OMA.R_mo_211283_R1

/-- The normalized twelfth-power bases congruent to one modulo nine. -/
def H1 : Prop :=
  ∀ b : ℕ, (∃ a : ℕ, 3 ≤ a ∧ b = a^12) →
    (b%10 = 1 ∨ b%10 = 5 ∨ b%10 = 6) → b%9 = 1 →
    Set.Infinite {k : ℕ | (Nat.digits 10 (b^(k+1))).sum < (Nat.digits 10 (b^k)).sum}

/-- The normalized twelfth-power bases divisible by nine. -/
def H2 : Prop :=
  ∀ b : ℕ, (∃ a : ℕ, 3 ≤ a ∧ b = a^12) →
    (b%10 = 1 ∨ b%10 = 5 ∨ b%10 = 6) → b%9 = 0 →
    Set.Infinite {k : ℕ | (Nat.digits 10 (b^(k+1))).sum < (Nat.digits 10 (b^k)).sum}

lemma power_two_block_gain (j : ℕ)
    (h : ∀ i, i < 6 → (Nat.digits 10 (2^(6*j+i))).sum ≤
      (Nat.digits 10 (2^(6*j+i+1))).sum) :
    (Nat.digits 10 (2^(6*j))).sum + 27 ≤ (Nat.digits 10 (2^(6*(j+1)))).sum := by
  let d (i : ℕ) := (Nat.digits 10 (2^(6*j+i))).sum
  have base : (2 : ℕ)^(6*j) ≡ 1 [MOD 9] := by
    rw [pow_mul]
    simpa using (show (2 : ℕ)^6 ≡ 1 [MOD 9] by decide).pow j
  have residue (i : ℕ) : d i % 9 = (2^i) % 9 := by
    have eq := (Nat.modEq_nine_digits_sum (2^(6*j+i))).symm
    change d i ≡ 2^i [MOD 9]
    apply eq.trans
    rw [pow_add]
    simpa using base.mul (Nat.ModEq.refl (2^i))
  have step (i : ℕ) (hi : i < 6) : d i ≤ d (i+1) := h i hi
  have r0 := residue 0
  have r1 := residue 1
  have r2 := residue 2
  have r3 := residue 3
  have r4 := residue 4
  have r5 := residue 5
  have r6 := residue 6
  norm_num at r0 r1 r2 r3 r4 r5 r6
  have g0 : d 0 + 1 ≤ d 1 := by have hstep : d 0 ≤ d 1 := step 0 (by decide); omega
  have g1 : d 1 + 2 ≤ d 2 := by have hstep : d 1 ≤ d 2 := step 1 (by decide); omega
  have g2 : d 2 + 4 ≤ d 3 := by have hstep : d 2 ≤ d 3 := step 2 (by decide); omega
  have g3 : d 3 + 8 ≤ d 4 := by have hstep : d 3 ≤ d 4 := step 3 (by decide); omega
  have g4 : d 4 + 7 ≤ d 5 := by have hstep : d 4 ≤ d 5 := step 4 (by decide); omega
  have g5 : d 5 + 5 ≤ d 6 := by have hstep : d 5 ≤ d 6 := step 5 (by decide); omega
  have result : d 0 + 27 ≤ d 6 := by omega
  simpa [d,Nat.mul_add] using result

lemma digit_sum_le_of_lt_pow {n l : ℕ} (h : n < 10^l) :
    (Nat.digits 10 n).sum ≤ 9*l := by
  induction l generalizing n with
  | zero =>
    have hz : n = 0 := by simpa using h
    simp [hz]
  | succ l ih =>
    by_cases hz : n = 0
    · simp [hz]
    · have hq : n / 10 < 10^l := (Nat.div_lt_iff_lt_mul (by decide)).mpr (by simpa [pow_succ] using h)
      have bound := ih hq
      rw [Nat.digits_eq_cons_digits_div (by decide : 1 < 10) hz, List.sum_cons]
      omega

lemma two_power_envelope (j : ℕ) :
    (Nat.digits 10 (2^(6*j))).sum ≤ 18*j+9 := by
  have bounds : (2:ℕ)^(6*j) ≤ 10^(2*j) := by
    rw [pow_mul, pow_mul]
    exact Nat.pow_le_pow_left (by decide) j
  have strict : (2:ℕ)^(6*j) < 10^(2*j+1) := by
    rw [pow_succ]
    have h : 0 < (10:ℕ)^(2*j) := by positivity
    omega
  have b := digit_sum_le_of_lt_pow strict
  omega

lemma decimal_scale_sum (m t : ℕ) :
    (Nat.digits 10 (m*10^t)).sum = (Nat.digits 10 m).sum := by
  by_cases h : m = 0
  · simp [h]
  · rw [Nat.mul_comm, Nat.digits_base_pow_mul (by decide : 1 < 10) (Nat.pos_of_ne_zero h)]
    simp

/-- In the base-two sequence, a drop occurs in each interval [6j, 18j+12). -/
lemma two_drop_in_interval (j : ℕ) :
    ∃ k : ℕ, 6*j ≤ k ∧ k < 18*j+12 ∧
      (Nat.digits 10 (2^(k+1))).sum < (Nat.digits 10 (2^k)).sum := by
  by_contra! nodrop
  have gain (m : ℕ) (hm : m ≤ 2*j+2) :
      (Nat.digits 10 (2^(6*j))).sum + 27*m ≤ (Nat.digits 10 (2^(6*(j+m)))).sum := by
    induction m with
    | zero => simp
    | succ m ih =>
      have prev := ih (by omega)
      have step := power_two_block_gain (j+m) (fun i hi =>
        nodrop (6*(j+m)+i) (by omega) (by omega))
      have e : j+(m+1) = (j+m)+1 := by omega
      rw [e]
      omega
  have h := gain (2*j+2) (le_refl _)
  have e := two_power_envelope (j+(2*j+2))
  omega

lemma two_drops : Set.Infinite {k : ℕ |
    (Nat.digits 10 (2^(k+1))).sum < (Nat.digits 10 (2^k)).sum} := by
  apply Set.infinite_iff_exists_gt.mpr
  intro N
  obtain ⟨k,lo,_,hk⟩ := two_drop_in_interval (N+1)
  exact ⟨k,hk,by omega⟩

/-- A descent in the subsequence at multiples of d needs a descent between
successive exponents of the original sequence. -/
lemma drops_from_power (a d : ℕ) (hd : 0 < d)
    (drops : Set.Infinite {k : ℕ | (Nat.digits 10 ((a^d)^(k+1))).sum <
      (Nat.digits 10 ((a^d)^k)).sum}) :
    Set.Infinite {k : ℕ | (Nat.digits 10 (a^(k+1))).sum < (Nat.digits 10 (a^k)).sum} := by
  apply Set.infinite_iff_exists_gt.mpr
  intro N
  by_contra! no
  obtain ⟨k,hk,hN⟩ := Set.infinite_iff_exists_gt.mp drops N
  have mono : MonotoneOn (fun k : ℕ => (Nat.digits 10 (a^k)).sum) (Set.Ici (N+1)) := by
    apply monotoneOn_nat_Ici_of_le_succ
    intro x hx
    by_contra! h
    exact (Nat.not_lt_of_ge (no x h)) hx
  have hdk : N+1 ≤ d*k := hN.trans_le (Nat.le_mul_of_pos_left k hd)
  have inc := mono hdk (show N+1 ≤ d*(k+1) by rw [Nat.mul_succ]; omega)
    (Nat.mul_le_mul_left d (Nat.le_succ k))
  change (Nat.digits 10 ((a^d)^(k+1))).sum < (Nat.digits 10 ((a^d)^k)).sum at hk
  simp only [← pow_mul] at hk
  exact (not_lt_of_ge inc) hk

lemma stripped_power_digits (a t k : ℕ) :
    (Nat.digits 10 ((10^t*a)^k)).sum = (Nat.digits 10 (a^k)).sum := by
  rw [mul_pow, ← pow_mul, mul_comm, decimal_scale_sum]

theorem main : H1 → H2 → type_of% @OMA.S_mo_211283.main := by
  intro coprime3 multiple3 n hn hpower
  obtain ⟨t,a,clean,hn'⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn.ne' 10 (by decide)
  have apos : 0 < a := by by_contra! h; simp [show a = 0 by omega] at hn'; omega
  have ne1 : a ≠ 1 := fun he => hpower t (by simpa [he] using hn')
  rw [hn']
  simp only [stripped_power_digits]
  by_cases ha : a = 2
  · simpa only [ha] using two_drops
  have ha3 : 3 ≤ a := by omega
  have mod9 : (a^12)%9 = 0 ∨ (a^12)%9 = 1 := by
    rw [Nat.pow_mod]
    have h := Nat.mod_lt a (by decide : 0 < 9)
    interval_cases a % 9 <;> decide
  have last : (a^12)%10 = 1 ∨ (a^12)%10 = 5 ∨ (a^12)%10 = 6 := by
    rw [Nat.pow_mod]
    have h := Nat.mod_lt a (by decide : 0 < 10)
    have nz : a % 10 ≠ 0 := fun e => clean (Nat.dvd_of_mod_eq_zero e)
    interval_cases a % 10 <;> first | contradiction | decide
  apply drops_from_power a 12 (by decide)
  rcases mod9 with h | h
  · exact multiple3 (a^12) ⟨a,ha3,rfl⟩ last h
  · exact coprime3 (a^12) ⟨a,ha3,rfl⟩ last h

end OMA.R_mo_211283_R1
