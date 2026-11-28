import OMAStatements.S_oeis_a257839
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

namespace OMA.P_oeis_a257839

open OMA.S_oeis_a257839

/-- Every divisor of `p^a * q^b` with `p, q` primes `≡ 1 (mod 3)` is `≡ 1 (mod 3)`. -/
private lemma dvd_mod3_eq_one {d p q a b : ℕ}
    (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hp3 : p % 3 = 1) (hq3 : q % 3 = 1)
    (hd : d ∣ p ^ a * q ^ b) : d % 3 = 1 := by
  have hd_pos : 0 < d := Nat.pos_of_dvd_of_pos hd (mul_pos (pow_pos hp.pos a) (pow_pos hq.pos b))
  have haux : ∀ n : ℕ, 0 < n → (∀ r : ℕ, Nat.Prime r → r ∣ n → r % 3 = 1) → n % 3 = 1 := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro hn hpr
      by_cases hn1 : n = 1
      · subst hn1; rfl
      · obtain ⟨r, hrp, hrd⟩ := Nat.exists_prime_and_dvd hn1
        obtain ⟨m, rfl⟩ := hrd
        have hmpos : 0 < m := Nat.pos_of_mul_pos_left hn
        have hmlt : m < r * m := lt_mul_of_one_lt_left hmpos hrp.one_lt
        have hm3 : m % 3 = 1 := ih m hmlt hmpos (fun s hs hsm => hpr s hs (dvd_mul_of_dvd_right hsm r))
        have hr3 : r % 3 = 1 := hpr r hrp (dvd_mul_right r m)
        rw [Nat.mul_mod, hr3, hm3]
  apply haux d hd_pos
  intro r hrp hrd
  have hr_dvd : r ∣ p ^ a * q ^ b := dvd_trans hrd hd
  rcases hrp.dvd_mul.mp hr_dvd with h1 | h2
  · have := (Nat.prime_dvd_prime_iff_eq hrp hp).mp (hrp.dvd_of_dvd_pow h1)
    subst this; exact hp3
  · have := (Nat.prime_dvd_prime_iff_eq hrp hq).mp (hrp.dvd_of_dvd_pow h2)
    subst this; exact hq3

/-- Every divisor of a product of powers of primes whose residues mod 7 lie in `{1, 2, 4}`
also has residue mod 7 in `{1, 2, 4}`. -/
private lemma dvd_mod7_mem {d : ℕ} (hd : d ∣ 2 ^ 4 * 71 ^ 2 * 1129 ^ 2) :
    d % 7 = 1 ∨ d % 7 = 2 ∨ d % 7 = 4 := by
  have hd_pos : 0 < d := Nat.pos_of_dvd_of_pos hd (by norm_num)
  have haux : ∀ n : ℕ, 0 < n →
      (∀ r : ℕ, Nat.Prime r → r ∣ n → r % 7 = 1 ∨ r % 7 = 2 ∨ r % 7 = 4) →
      n % 7 = 1 ∨ n % 7 = 2 ∨ n % 7 = 4 := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro hn hpr
      by_cases hn1 : n = 1
      · subst hn1; left; rfl
      · obtain ⟨r, hrp, hrd⟩ := Nat.exists_prime_and_dvd hn1
        obtain ⟨m, rfl⟩ := hrd
        have hmpos : 0 < m := Nat.pos_of_mul_pos_left hn
        have hmlt : m < r * m := lt_mul_of_one_lt_left hmpos hrp.one_lt
        have hm7 := ih m hmlt hmpos (fun s hs hsm => hpr s hs (dvd_mul_of_dvd_right hsm r))
        have hr7 := hpr r hrp (dvd_mul_right r m)
        rw [Nat.mul_mod]
        rcases hr7 with h1 | h1 | h1 <;> rcases hm7 with h2 | h2 | h2 <;>
          simp [h1, h2]
  apply haux d hd_pos
  intro r hrp hrd
  have hr_dvd : r ∣ 2 ^ 4 * 71 ^ 2 * 1129 ^ 2 := dvd_trans hrd hd
  rcases hrp.dvd_mul.mp hr_dvd with h12 | h3
  · rcases hrp.dvd_mul.mp h12 with h1 | h2
    · have := (Nat.prime_dvd_prime_iff_eq hrp (by norm_num : Nat.Prime 2)).mp (hrp.dvd_of_dvd_pow h1)
      subst this; right; left; rfl
    · have := (Nat.prime_dvd_prime_iff_eq hrp (by norm_num : Nat.Prime 71)).mp (hrp.dvd_of_dvd_pow h2)
      subst this; left; rfl
  · have := (Nat.prime_dvd_prime_iff_eq hrp (by norm_num : Nat.Prime 1129)).mp (hrp.dvd_of_dvd_pow h3)
    subst this; right; left; rfl

private lemma not_hasES_1129_283 : ¬ HasESWithX 1129 283 := by
  rintro ⟨_, y, z, hxy, hyz, heq⟩
  have hy_big : 319507 < 3 * y := by nlinarith
  have hz_big : 319507 < 3 * z := by nlinarith
  have hprod : (3 * y - 319507) * (3 * z - 319507) = 283 ^ 2 * 1129 ^ 2 := by
    zify [le_of_lt hy_big, le_of_lt hz_big] at heq ⊢
    nlinarith
  have hdvd : (3 * y - 319507) ∣ 283 ^ 2 * 1129 ^ 2 := ⟨3 * z - 319507, hprod.symm⟩
  have hmod := dvd_mod3_eq_one (by norm_num : Nat.Prime 283) (by norm_num : Nat.Prime 1129)
    (by norm_num) (by norm_num) hdvd
  omega

private lemma not_hasES_1129_284 : ¬ HasESWithX 1129 284 := by
  rintro ⟨_, y, z, hxy, hyz, heq⟩
  have hy_big : 320636 < 7 * y := by nlinarith
  have hz_big : 320636 < 7 * z := by nlinarith
  have hprod : (7 * y - 320636) * (7 * z - 320636) = 2 ^ 4 * 71 ^ 2 * 1129 ^ 2 := by
    zify [le_of_lt hy_big, le_of_lt hz_big] at heq ⊢
    nlinarith
  have hdvd : (7 * y - 320636) ∣ 2 ^ 4 * 71 ^ 2 * 1129 ^ 2 := ⟨7 * z - 320636, hprod.symm⟩
  have hmod := dvd_mod7_mem hdvd
  omega

private lemma hasES_1129_285 : HasESWithX 1129 285 := by
  refine ⟨by norm_num, 29260, 99103620, by norm_num, by norm_num, ?_⟩
  norm_num

private theorem prove_disproof : ¬ (type_of% @OMA.S_oeis_a257839.main) := by
  intro hmain
  have hne : { x : ℕ | HasESWithX 1129 x }.Nonempty := ⟨285, hasES_1129_285⟩
  have hmem : HasESWithX 1129 (A257839 1129) := Nat.sInf_mem hne
  have hcase := hmain 1129 (by norm_num)
  have hdiv : 1129 / 4 = 282 := by norm_num
  rw [hdiv] at hcase
  rcases hcase with h283 | h284
  · rw [h283] at hmem
    exact not_hasES_1129_283 hmem
  · rw [h284] at hmem
    exact not_hasES_1129_284 hmem

end OMA.P_oeis_a257839

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a257839.main) :=
  OMA.P_oeis_a257839.prove_disproof
