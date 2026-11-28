import OMAStatements.S_mse_1803721
import Mathlib

/-!
Fermat's little theorem rules out prime-power bases other than two and
three. A congruence modulo four rules out every even input. Lifting the
exponent at three excludes every input divisible by nine, including all
higher powers of three.
The modular certificate also excludes primes from 5 to 127.
-/

namespace OMA.R_mse_1803721_R1

private theorem odd_of_solution {n : ℕ} (hn : 1 < n)
    (hd : n ^ 2 ∣ 3 ^ n + 2 ^ n + 1) : Odd n := by
  by_contra hodd
  have he : Even n := Nat.not_odd_iff_even.mp hodd
  obtain ⟨k, hk⟩ := he
  have hnk : n = 2 * k := by omega
  have h3 : (3 : ℕ) ^ n ≡ 1 [MOD 4] := by
    rw [hnk, pow_mul]
    simpa using (show (3 : ℕ) ^ 2 ≡ 1 [MOD 4] by decide).pow k
  have h2 : 4 ∣ (2 : ℕ) ^ n := Nat.pow_dvd_pow 2 (show 2 ≤ n by omega)
  have h4 : 4 ∣ n ^ 2 := by
    rw [hnk, mul_pow]
    exact dvd_mul_right _ _
  have hsum : (3 : ℕ) ^ n + 2 ^ n + 1 ≡ 2 [MOD 4] :=
    (h3.add (Nat.modEq_zero_iff_dvd.mpr h2)).add_right 1
  exact (by decide : ¬ (0 : ℕ) ≡ 2 [MOD 4])
    ((Nat.modEq_zero_iff_dvd.mpr (h4.trans hd)).symm.trans hsum)

private theorem not_nine_dvd {n : ℕ} (hn : 1 < n) (hodd : Odd n)
    (hd : n ^ 2 ∣ 3 ^ n + 2 ^ n + 1) : ¬ 9 ∣ n := by
  intro h9
  have hfin : FiniteMultiplicity (3 : ℕ) n :=
    Nat.finiteMultiplicity_iff.mpr ⟨by decide, by omega⟩
  let e := multiplicity (3 : ℕ) n
  have he : 2 ≤ e := hfin.pow_dvd_iff_le_multiplicity.mp
    (show (3 : ℕ) ^ 2 ∣ n from h9)
  have hpe : 3 ^ e ∣ n := hfin.pow_dvd_iff_le_multiplicity.mpr (le_refl e)
  have haux (i : ℕ) : i + 3 ≤ (3 : ℕ) ^ (i + 1) := by
    induction i with
    | zero => decide
    | succ i ih =>
      rw [show i.succ + 1 = (i + 1) + 1 by omega, pow_succ]
      omega
  have hne : e + 2 ≤ n := by
    have h := haux (e - 1)
    rw [show e - 1 + 1 = e by omega] at h
    exact (by omega : e + 2 ≤ 3 ^ e).trans (Nat.le_of_dvd (by omega) hpe)
  have hsq : 3 ^ (e * 2) ∣ n ^ 2 := by
    rw [pow_mul]
    exact pow_dvd_pow_of_dvd hpe 2
  have hsum : 3 ^ (e + 2) ∣ 3 ^ n + (2 ^ n + 1) := by
    rw [← add_assoc]
    exact (Nat.pow_dvd_pow 3 (by omega : e + 2 ≤ e * 2)).trans (hsq.trans hd)
  have h3n : 3 ^ (e + 2) ∣ 3 ^ n := Nat.pow_dvd_pow 3 hne
  have htwo : 3 ^ (e + 2) ∣ 2 ^ n + 1 := (Nat.dvd_add_iff_right h3n).mpr hsum
  have hp3 : Nat.Prime 3 := by decide
  have hself : emultiplicity (3 : ℕ) (2 + 1) = 1 := hp3.emultiplicity_self
  have hnval : emultiplicity (3 : ℕ) n = (e : ℕ∞) := hfin.emultiplicity_eq_multiplicity
  have hval : emultiplicity (3 : ℕ) (2 ^ n + 1) = ((e + 1 : ℕ) : ℕ∞) := by
    have h := Nat.emultiplicity_pow_add_pow hp3 (by decide) (x := 2) (y := 1)
      (by decide) (by decide) hodd
    simpa only [one_pow, hself, hnval, Nat.cast_add, Nat.cast_one, add_comm] using h
  have hbound := pow_dvd_iff_le_emultiplicity.mp htwo
  rw [hval] at hbound
  have hle : e + 2 ≤ e + 1 := by exact_mod_cast hbound
  omega

-- Repeated squaring as in the A078680 Proth certificate verifier.
private def modPower (a n m : ℕ) : ℕ :=
  Nat.binaryRec (motive := fun _ => ℕ) (1 % m)
    (fun b _ t => (if b then a * (t * t) else t * t) % m) n

private theorem cast_modPower (a n m : ℕ) :
    (modPower a n m : ZMod m) = (a : ZMod m) ^ n := by
  induction n using Nat.binaryRec with
  | zero => simp [modPower, ZMod.natCast_mod]
  | bit b n ih =>
    unfold modPower
    rw [Nat.binaryRec_eq b n (Or.inl (by
      change ((1 % m) * (1 % m)) % m = 1 % m
      simpa only [one_mul] using (Nat.mul_mod 1 1 m).symm))]
    change (((if b then a * (modPower a n m * modPower a n m)
      else modPower a n m * modPower a n m) % m : ℕ) : ZMod m) =
      (a : ZMod m) ^ (n.bit b)
    rw [ZMod.natCast_mod]
    cases b
    · simp [Nat.bit, two_mul, pow_add, ih]
    · simp [Nat.bit, pow_add, ih, mul_comm, pow_mul, pow_two]

private theorem modPower_congr (a n m : ℕ) : modPower a n m ≡ a ^ n [MOD m] :=
  (ZMod.natCast_eq_natCast_iff _ _ _).mp (by rw [cast_modPower, Nat.cast_pow])

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
/-- The first two tests establish the period `p - 1` for the exponent quotient.
The last test checks its odd representatives. -/
private theorem small_prime_certificate :
    ∀ p : Fin 128, 5 ≤ p.val → p.val.Prime →
      modPower 3 (p.val * (p.val - 1)) (p.val ^ 2) = 1 ∧
      modPower 2 (p.val * (p.val - 1)) (p.val ^ 2) = 1 ∧
      ∀ r : Fin p.val, r.val % 2 = 1 →
        (modPower 3 (p.val * r.val) (p.val ^ 2) +
          modPower 2 (p.val * r.val) (p.val ^ 2) + 1) % p.val ^ 2 ≠ 0 := by
  decide

private theorem pow_quotient_residue {a p k : ℕ}
    (hperiod : a ^ (p * (p - 1)) ≡ 1 [MOD p ^ 2]) :
    a ^ (p * k) ≡ a ^ (p * (k % (p - 1))) [MOD p ^ 2] := by
  have hperiod' : (a ^ p) ^ (p - 1) ≡ 1 [MOD p ^ 2] := by
    simpa only [pow_mul] using hperiod
  have h : k % (p - 1) + (p - 1) * (k / (p - 1)) = k := Nat.mod_add_div _ _
  rw [pow_mul, pow_mul]
  calc
    (a ^ p) ^ k = (a ^ p) ^ (k % (p - 1) + (p - 1) * (k / (p - 1))) :=
      congrArg (fun e : ℕ => (a ^ p) ^ e) h.symm
    _ ≡ (a ^ p) ^ (k % (p - 1)) [MOD p ^ 2] := by
      rw [pow_add, pow_mul]
      simpa only [one_pow, mul_one] using
        (Nat.ModEq.refl ((a ^ p) ^ (k % (p - 1)))).mul (hperiod'.pow (k / (p - 1)))

/-- No prime from 5 to 127 can divide an odd solution. -/
theorem excludes_small_prime {n p : ℕ} (hn : Odd n) (hp : p.Prime)
    (hp5 : 5 ≤ p) (hpl : p < 128) (hd : n ^ 2 ∣ 3 ^ n + 2 ^ n + 1) : ¬ p ∣ n := by
  intro hpdiv
  obtain ⟨k, rfl⟩ := hpdiv
  have hpodd : p % 2 = 1 := hp.eq_two_or_odd.resolve_left (by omega)
  have hkodd : k % 2 = 1 := by
    have h := Nat.odd_iff.mp hn
    rwa [Nat.mul_mod, hpodd, one_mul, Nat.mod_mod] at h
  have hr : k % (p - 1) % 2 = 1 := by
    have h := congrArg (fun x : ℕ => x % 2) (Nat.mod_add_div k (p - 1))
    have he : (p - 1) % 2 = 0 := by omega
    simp only [Nat.add_mod, Nat.mul_mod, he, zero_mul, Nat.zero_mod, Nat.mod_mod,
      add_zero, hkodd] at h
    exact h
  have hrp : k % (p - 1) < p := (Nat.mod_lt _ (by omega : 0 < p - 1)).trans (by omega)
  obtain ⟨h3, h2, hnot⟩ := small_prime_certificate ⟨p, hpl⟩ hp5 hp
  have hp3 := (modPower_congr 3 (p * (p - 1)) (p ^ 2)).symm.trans
    (show _ ≡ 1 [MOD p ^ 2] by rw [h3])
  have hp2 := (modPower_congr 2 (p * (p - 1)) (p ^ 2)).symm.trans
    (show _ ≡ 1 [MOD p ^ 2] by rw [h2])
  let r := k % (p - 1)
  have hsum := ((pow_quotient_residue (k := k) hp3).add
    (pow_quotient_residue (k := k) hp2)).add_right 1
  have hcheck := ((modPower_congr 3 (p * r) (p ^ 2)).add
    (modPower_congr 2 (p * r) (p ^ 2))).add_right 1
  have hdiv : p ^ 2 ∣ 3 ^ (p * k) + 2 ^ (p * k) + 1 :=
    (show p ^ 2 ∣ (p * k) ^ 2 by rw [mul_pow]; exact dvd_mul_right _ _).trans hd
  exact hnot ⟨k % (p - 1), hrp⟩ hr
    ((hcheck.trans hsum.symm).trans (Nat.modEq_zero_iff_dvd.mpr hdiv))

/-- Every solution is odd, is not divisible by nine, and can be a prime power only at three. -/
def H1 : Prop := ∀ n : ℕ, 1 < n → n ^ 2 ∣ 3 ^ n + 2 ^ n + 1 →
  Odd n ∧ ¬ 9 ∣ n ∧ (IsPrimePow n → n = 3)

/-- The odd inputs with at least two distinct prime factors that survive the elementary obstructions. -/
def H2 : Prop := ∀ n : ℕ, 1 < n → Odd n → ¬ 9 ∣ n → ¬ IsPrimePow n →
  (∀ p : ℕ, p.Prime → 5 ≤ p → p < 128 → ¬ p ∣ n) →
  ¬ n ^ 2 ∣ 3 ^ n + 2 ^ n + 1

theorem elementary_cases : H1 := by
  intro n hn hd
  have hodd := odd_of_solution hn hd
  have h9 := not_nine_dvd hn hodd hd
  refine ⟨hodd, h9, ?_⟩
  intro hpw
  obtain ⟨p, e, hp, he, rfl⟩ := (isPrimePow_nat_iff n).mp hpw
  let _ : Fact p.Prime := ⟨hp⟩
  have hpN : p ∣ p ^ e := by
    simpa only [pow_one] using Nat.pow_dvd_pow p (show 1 ≤ e from he)
  have hN2 : p ^ e ∣ (p ^ e) ^ 2 := by
    simpa only [pow_one] using Nat.pow_dvd_pow (p ^ e) (by decide : 1 ≤ 2)
  have hdv : p ∣ 3 ^ (p ^ e) + 2 ^ (p ^ e) + 1 := hpN.trans (hN2.trans hd)
  have hcast : ((3 ^ (p ^ e) + 2 ^ (p ^ e) + 1 : ℕ) : ZMod p) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).mpr hdv
  push_cast at hcast
  rw [ZMod.pow_card_pow, ZMod.pow_card_pow] at hcast
  have hp6 : p ∣ 6 := (ZMod.natCast_eq_zero_iff _ _).mp (by
    convert hcast using 1
    norm_num)
  have hp23 : p = 2 ∨ p = 3 := by
    have hp' : p ∣ 2 * 3 := hp6
    rcases hp.dvd_mul.mp hp' with hp2 | hp3
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp (by decide)).mp hp2)
    · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hp (by decide)).mp hp3)
  rcases hp23 with rfl | rfl
  · exact (hodd.not_two_dvd_nat hpN).elim
  · have he2 : ¬ 2 ≤ e := fun h => h9 (Nat.pow_dvd_pow 3 h)
    have he1 : e = 1 := by omega
    simp [he1]

theorem main : H1 → H2 → type_of% @OMA.S_mse_1803721.main := by
  intro elementary remaining n hn hd
  obtain ⟨hodd, h9, hprime⟩ := elementary n hn hd
  by_cases hp : IsPrimePow n
  · exact hprime hp
  · exact (remaining n hn hodd h9 hp (fun p hp' hp5 hpl =>
      excludes_small_prime hodd hp' hp5 hpl hd) hd).elim

end OMA.R_mse_1803721_R1
