import OMAStatements.S_oeis_a346659
import Mathlib

open OMA.S_oeis_a346659

private lemma oma_prime_square_obstruction {q p r : ℕ} (hq : q.Prime) (hp : p.Prime)
    (hr : r.Prime) (h : q ^ 2 ∣ p * r) : p * r = q ^ 2 := by
  rw [pow_two] at h ⊢
  have hd : q ∣ p * r := (dvd_mul_right q q).trans h
  rcases hq.dvd_mul.mp hd with hqp | hqr
  · have eq := (Nat.prime_dvd_prime_iff_eq hq hp).mp hqp
    subst p
    have hqr := Nat.dvd_of_mul_dvd_mul_left hq.pos h
    rw [(Nat.prime_dvd_prime_iff_eq hq hr).mp hqr]
  · have eq := (Nat.prime_dvd_prime_iff_eq hq hr).mp hqr
    subst r
    rw [mul_comm p q] at h
    have hqp := Nat.dvd_of_mul_dvd_mul_left hq.pos h
    rw [(Nat.prime_dvd_prime_iff_eq hq hp).mp hqp]

/-- Every prime in this progression has a repeated prime factor on either side. -/
private lemma progression_included {r : ℕ} (hr : r.Prime)
    (hclass : r ≡ 173 [MOD 225]) : r ∈ S := by
  refine ⟨hr, ?_⟩
  rintro ⟨p,q,hp,hq,h | h⟩
  · change r % 225 = 173 % 225 at hclass
    have hd : 3^2 ∣ p*q := by omega
    have he := oma_prime_square_obstruction (by decide : Nat.Prime 3) hp hq hd
    omega
  · change r % 225 = 173 % 225 at hclass
    have hd : 5^2 ∣ p*q := by omega
    have he := oma_prime_square_obstruction (by decide : Nat.Prime 5) hp hq hd
    omega

theorem OMA.solution : type_of% @OMA.S_oeis_a346659.main := by
  apply Set.infinite_of_forall_exists_gt
  intro N
  obtain ⟨r,hr,hp,hmod⟩ := Nat.forall_exists_prime_gt_and_modEq N
    (q:=225) (a:=173) (by decide) (by decide)
  exact ⟨r, progression_included hp hmod, hr⟩
