import OMAStatements.S_oeis_a217501
import Mathlib.NumberTheory.LucasLehmer

-- Reduction oeis-a217501.R1
-- Credit: @Pixelstorm44

/-!
Every prime exponent in this quadratic family occurs at an index divisible by three.
Writing that index as 3m, we identify both possible penultimate Lucas–Lehmer
residues of a Mersenne prime. Each residue is also sufficient for primality.
The two open steps exclude the positive and negative residues for m ≥ 34.

Below that cutoff we use proper divisors (from trial factoring and the GIMPS
exponent reports at https://www.mersenne.org/report_exponent/) and one direct
Lucas–Lehmer calculation, for exponent 8389. All certificates are checked here.
-/

namespace OMA.R_oeis_a217501_R1

open OMA.S_oeis_a217501 (f)
open LucasLehmer (sZMod)

theorem index_multiple_of_three (n : ℕ) (hp : (f n).Prime) : 3 ∣ n := by
  by_contra hn
  have hmod : n % 3 = 1 ∨ n % 3 = 2 := by omega
  have hd : 3 ∣ f n := by
    unfold f
    rcases hmod with h | h
    · obtain ⟨k, hk⟩ : ∃ k, n = 3 * k + 1 := ⟨n / 3, by omega⟩
      rw [hk]
      ring_nf
      omega
    · obtain ⟨k, hk⟩ : ∃ k, n = 3 * k + 2 := ⟨n / 3, by omega⟩
      rw [hk]
      ring_nf
      omega
  have he := hp.eq_one_or_self_of_dvd 3 hd
  unfold f at he
  omega

theorem root_sq (p k : ℕ) (he : k * 2 = p + 1) :
    ((2 : ZMod (mersenne p)) ^ k) ^ 2 = 2 := by
  have hc := congrArg (fun t : ℕ => (t : ZMod (mersenne p))) (succ_mersenne p)
  simp only [Nat.cast_add, ZMod.natCast_self, zero_add, Nat.cast_one, Nat.cast_pow,
    Nat.cast_ofNat] at hc
  rw [← pow_mul, he, pow_succ, ← hc, one_mul]

theorem signed_test (p k : ℕ) (hp : 3 ≤ p) (he : k * 2 = p + 1) :
    let r := (2 : ZMod (2 ^ p - 1)) ^ k
    (mersenne p).Prime ↔ sZMod p (p - 3) = r ∨ sZMod p (p - 3) = -r := by
  intro r
  have step : LucasLehmerTest p ↔ sZMod p (p - 3) ^ 2 = 2 := by
    change sZMod p (p - 2) = 0 ↔ sZMod p (p - 3) ^ 2 = 2
    rw [show p - 2 = (p - 3) + 1 by omega, sZMod, sub_eq_zero]
  constructor
  · intro h
    let : Fact (2 ^ p - 1).Prime := ⟨h⟩
    exact sq_eq_sq_iff_eq_or_eq_neg.mp
      ((step.mp (lucas_lehmer_necessity p hp h)).trans (root_sq p k he).symm)
  · intro h
    apply lucas_lehmer_sufficiency p (by omega)
    apply step.mpr
    have hr : r ^ 2 = 2 := root_sq p k he
    rcases h with h | h <;> rw [h] <;> simp [hr]

set_option maxRecDepth 100000 in
private theorem certificates (m : Fin 34) :
    let p := f (3 * m.val)
    m.val = 16 ∨ ∃ q, 1 < q ∧ ((q < p ∧ q ∣ p) ∨ (q < mersenne p ∧ q ∣ mersenne p)) := by
  -- Each entry factors either the exponent or its Mersenne number.
  -- The zero entry marks the separate Lucas–Lehmer calculation.
  let divisors : List ℕ :=
    [223, 17, 3463, 17, 13, 10788426156438350117334292343137689257142387557947087583,
     16673027617, 92006001376648044276967530077499930523710420381051263551, 39770030257, 13,
     467039490551109991900169555492443530235814719, 6854888399, 2087809, 81237913, 41047, 71, 0,
     13, 17, 79, 17, 203826647, 13, 67, 37, 86342631243959, 3212289470281, 3070058984012574271,
     127, 10014217, 13, 67, 101, 8226831003359]
  have checked : ∀ i : Fin 34, i.val = 16 ∨
      let p := f (3 * i.val)
      let q := divisors[i.val]!
      1 < q ∧ ((q < p ∧ p % q = 0) ∨ (q < mersenne p ∧ mersenne p % q = 0)) := by
    dsimp only [divisors]
    decide +kernel
  rcases checked m with he | ⟨hq, h | h⟩
  · exact Or.inl he
  · exact Or.inr ⟨_, hq, Or.inl ⟨h.1, Nat.dvd_of_mod_eq_zero h.2⟩⟩
  · exact Or.inr ⟨_, hq, Or.inr ⟨h.1, Nat.dvd_of_mod_eq_zero h.2⟩⟩

set_option maxRecDepth 100000 in
private theorem exception : ¬ LucasLehmerTest 8389 := by norm_num

theorem initial_range (m : ℕ) (hm : m < 34) : ¬ (mersenne (f (3 * m))).Prime := by
  intro h
  rcases certificates ⟨m, hm⟩ with he | ⟨q, hq, ⟨hlt, hd⟩ | ⟨hlt, hd⟩⟩
  · change m = 16 at he
    subst m
    exact exception (lucas_lehmer_necessity 8389 (by decide) h)
  · have he := h.of_mersenne.eq_one_or_self_of_dvd q hd
    change q < f (3 * m) at hlt
    omega
  · have he := h.eq_one_or_self_of_dvd q hd
    change q < mersenne (f (3 * m)) at hlt
    omega

/-- Exclude the positive square root at the penultimate iterate. -/
def H1 : Prop := ∀ m p : ℕ, 34 ≤ m → p = f (3 * m) →
  sZMod p (p - 3) ≠ (2 : ZMod (mersenne p)) ^ (9 * m ^ 2 + 117 * m + 19)

/-- Exclude the negative square root at the penultimate iterate. -/
def H2 : Prop := ∀ m p : ℕ, 34 ≤ m → p = f (3 * m) →
  sZMod p (p - 3) ≠ -((2 : ZMod (mersenne p)) ^ (9 * m ^ 2 + 117 * m + 19))

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a217501.main := by
  intro hpos hneg n hp
  obtain ⟨m, rfl⟩ := index_multiple_of_three n hp
  by_cases hm : m < 34
  · exact initial_range m hm
  · intro h
    generalize hmp : f (3 * m) = p at h
    have hp3 : 3 ≤ p := by rw [← hmp]; unfold f; omega
    have he : (9 * m ^ 2 + 117 * m + 19) * 2 = p + 1 := by rw [← hmp]; unfold f; ring
    exact ((signed_test p _ hp3 he).mp h).elim
      (hpos m p (by omega) hmp.symm) (hneg m p (by omega) hmp.symm)

end OMA.R_oeis_a217501_R1
