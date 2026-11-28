import OMAStatements.S_oeis_a130091

open Nat OMA.S_oeis_a130091

private theorem excluded {m : ℕ} (h : m % 36 = 6 ∨ m % 36 = 30) : ¬ InSeq m := by
  rintro ⟨hm, hinj⟩
  have mem {p : ℕ} (hp : p.Prime) (hd : p ∣ m) : p ∈ m.primeFactors :=
    mem_primeFactors.mpr ⟨hp, hd, hm.ne'⟩
  have exponent {p : ℕ} (hp : p.Prime) (hd : p ∣ m) (hs : ¬ p * p ∣ m) :
      m.factorization p = 1 := by
    have lower := (hp.dvd_iff_one_le_factorization hm.ne').mp hd
    have upper := mt (hp.pow_dvd_iff_le_factorization (k := 2) hm.ne').mpr
      (by simpa only [pow_two] using hs)
    omega
  have e₂ := exponent prime_two (by omega) (by omega)
  have e₃ := exponent prime_three (by omega) (by omega)
  have eq := hinj (mem prime_two (by omega)) (mem prime_three (by omega)) (e₂.trans e₃.symm)
  omega

theorem OMA.solution : type_of% @OMA.S_oeis_a130091.main := by
  refine ⟨fun n hn => excluded (by omega), fun n => excluded (by omega), ?_⟩
  rintro ⟨m, hm⟩
  let r := m % 36
  let next := if r ≤ 6 then 6 - r else if r ≤ 30 then 30 - r else 42 - r
  have bounds : next < 24 ∧ ((m + next) % 36 = 6 ∨ (m + next) % 36 = 30) := by
    dsimp [next, r]
    split
    · omega
    · split <;> omega
  exact excluded bounds.2 (hm next bounds.1)
