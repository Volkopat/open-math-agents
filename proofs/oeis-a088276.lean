import OMAStatements.S_oeis_a088276
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic

/-!
The admissible suffix 162207 is zero modulo three. For every exponent,
one of 11, 101, 73 and 137 divides 10^k+162207. These are also the
four divisors in Pierre Cami's 2014 covering for the related
162207*10^k+1, published in OEIS A244348.
-/

open OMA.S_oeis_a088276

namespace DecimalCover

def factor (j : ℕ) : ℕ :=
  if j % 2 = 1 then 11 else if j % 4 = 2 then 101 else if j % 8 = 4 then 73 else 137

lemma residue_table : ∀ j : Fin 8, factor j.val ∣ 10^j.val+162207 ∧
    10^8 ≡ 1 [MOD factor j.val] ∧ 1 < factor j.val ∧ factor j.val ≤ 137 := by
  decide +kernel

lemma reduce_exponent (k p : ℕ) (h : 10^8 ≡ 1 [MOD p]) :
    10^k ≡ 10^(k%8) [MOD p] := by
  calc
    10^k = (10^8)^(k/8) * 10^(k%8) := by
      rw [← pow_mul, ← pow_add, Nat.div_add_mod]
    _ ≡ 1^(k/8) * 10^(k%8) [MOD p] := (h.pow (k/8)).mul_right _
    _ = _ := by simp

lemma composite (k : ℕ) : ¬ Nat.Prime (10^k+162207) := by
  let j : Fin 8 := ⟨k%8, Nat.mod_lt _ (by decide)⟩
  obtain ⟨hd, hp, hlo, hhi⟩ := residue_table j
  have congruence := (reduce_exponent k (factor j.val) hp).add_right 162207
  change (10^k+162207) % factor j.val = (10^j.val+162207) % factor j.val at congruence
  have divisor : factor j.val ∣ 10^k+162207 :=
    Nat.dvd_of_mod_eq_zero (Eq.trans congruence (Nat.mod_eq_zero_of_dvd hd))
  have strict : factor j.val < 10^k + 162207 := hhi.trans_lt
    ((show 137 < 162207 by decide).trans_le (Nat.le_add_left _ _))
  intro h
  rcases (Nat.dvd_prime h).mp divisor with h1 | hall
  · exact hlo.ne' h1
  · exact strict.ne hall

lemma witness_allowed : allowed 162207 := by
  refine ⟨by decide, ⟨81103, by decide⟩, by decide⟩

lemma both_fail : entry 162207 = 0 ∧
    {k : ℕ | Nat.Prime (10^k+162207)} = ∅ := by
  have hempty : ¬ ∃ k, eligible 162207 k := by
    rintro ⟨k, prime, _⟩
    exact composite k prime
  constructor
  · simp [entry, hempty]
  · ext k
    simp [composite k]

end DecimalCover

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a088276.main) := by
  rintro ⟨first, second⟩
  have hres : 162207 % 3 ≠ 2 := by decide
  have hfirst := first 162207 DecimalCover.witness_allowed DecimalCover.both_fail.1
  exact hres hfirst
