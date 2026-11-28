import OMAStatements.S_oeis_a082871
import Mathlib
namespace OMA.R_oeis_a082871_R1

lemma once_dvd {p x : ℕ} (hp : p.Prime) (hlo : p ≤ x) (hhi : x < 2*p) :
    x.factorial.factorization p = 1 := by
  have s : x < p ^ 2 := by nlinarith [hp.two_le, Nat.mul_le_mul_right p hp.two_le]
  rw [Nat.factorization_factorial hp (Nat.log_lt_of_lt_pow (by omega : x ≠ 0) s)]
  simp only [show Finset.Ico 1 2 = {1} by decide, Finset.sum_singleton, pow_one]
  exact Nat.div_eq_of_lt_le (by simpa using hlo) (by simpa [Nat.mul_comm] using hhi)

lemma not_large {x y p : ℕ} (hp : p.Prime) (hlo : p ≤ x) (hhi : x < 2*p)
    (hxy : x ≤ y) (sq : IsSquare (x.factorial+y.factorial)) : y < 2*p := by
  by_contra! hy
  have divx : p ∣ x.factorial := Nat.dvd_factorial hp.pos hlo
  have divy : p ∣ y.factorial := Nat.dvd_factorial hp.pos (hlo.trans hxy)
  obtain ⟨z,hz⟩ := sq
  have dp : p ∣ z*z := hz ▸ dvd_add divx divy
  have dz : p ∣ z := (hp.dvd_mul.mp dp).elim id id
  have dd : p^2 ∣ x.factorial+y.factorial := by simpa [hz,pow_two] using mul_dvd_mul dz dz
  have yy : p^2 ∣ y.factorial := by
    have hp' : p ∣ p.factorial := Nat.dvd_factorial hp.pos le_rfl
    exact (show p^2 ∣ p.factorial * p.factorial by simpa [pow_two] using mul_dvd_mul hp' hp').trans
      ((Nat.factorial_mul_factorial_dvd_factorial_add p p).trans (Nat.factorial_dvd_factorial (by omega)))
  have ddx : p^2 ∣ x.factorial := (Nat.dvd_add_iff_left yy).mpr dd
  have v := (hp.pow_dvd_iff_le_factorization x.factorial_ne_zero).mp ddx
  rw [once_dvd hp hlo hhi] at v
  omega

lemma bertrand_bound {x y : ℕ} (hx : 2 ≤ x) (hxy : x ≤ y) (sq : IsSquare (x.factorial+y.factorial)) : y < 2*x := by
  obtain ⟨p,hp,ha,hb⟩ := Nat.exists_prime_lt_and_le_two_mul (x/2) (by omega)
  have t := not_large hp (by omega : p ≤ x) (by omega : x < 2*p) hxy sq
  omega

lemma prime_filter {x y p : ℕ} (hp : p.Prime) (lo : p ≤ x) (hi : x < 2*p) (le : x ≤ y)
    (sq : IsSquare (x.factorial+y.factorial)) :
    p ∣ 1+(x+1).ascFactorial (y-x) := by
  let q := (x+1).ascFactorial (y-x)
  have fac : x.factorial*q = y.factorial := by
    simpa [q,Nat.add_sub_of_le le] using Nat.factorial_mul_ascFactorial x (y-x)
  obtain ⟨z,hz⟩ := sq
  have hz' : x.factorial*(1+q)=z^2 := by simpa [Nat.mul_add,fac,pow_two] using hz
  have hpos : z ≠ 0 := by
    intro h
    rw [h,pow_two,Nat.zero_mul] at hz'
    exact (Nat.mul_ne_zero x.factorial_ne_zero (by omega)) hz'
  have v := congrArg (fun k : ℕ => k.factorization p) hz'
  simp only [Nat.factorization_mul x.factorial_ne_zero (by omega : 1+q≠0),Nat.factorization_pow,
    Finsupp.add_apply,Finsupp.smul_apply,smul_eq_mul,once_dvd hp lo hi] at v
  apply (hp.dvd_iff_one_le_factorization (by omega : 1+q≠0)).mpr
  omega

def H1 : Prop := ∀ y : ℕ, IsSquare (1+y.factorial) → y=4 ∨ y=5 ∨ y=7

def H2 : Prop := ∀ x y : ℕ, 11 ≤ x → x ≤ y → y < 2*x →
    ∃ p : ℕ, p.Prime ∧ p ≤ x ∧ x < 2*p ∧ ¬ p ∣ 1+(x+1).ascFactorial (y-x)

lemma small {x y : ℕ} (lo : 2 ≤ x) (hi : x ≤ 10) (le : x ≤ y)
    (sq : IsSquare (x.factorial+y.factorial)) : (x=2 ∧ y=2) ∨ (x=4 ∧ y=5) := by
  have b := bertrand_bound lo le sq
  have lim : y < 20 := by omega
  have checked : ∀ a : Fin 11, ∀ b : Fin 20, 2 ≤ a.val → a.val ≤ b.val →
      IsSquare (a.val.factorial+b.val.factorial) → (a.val=2 ∧ b.val=2) ∨ (a.val=4 ∧ b.val=5) := by
    decide +kernel
  exact checked ⟨x,by omega⟩ ⟨y,lim⟩ lo le sq

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a082871.main := by
  intro edge interior
  ext ⟨x,y⟩
  change (x ≤ y ∧ IsSquare (x.factorial+y.factorial)) ↔ _
  constructor
  · rintro ⟨le,sq⟩
    by_cases hx : x ≤ 1
    · interval_cases x <;> simp only [Nat.factorial_zero,Nat.factorial_one] at sq <;>
        rcases edge y sq with rfl|rfl|rfl <;> decide
    by_cases hs : x ≤ 10
    · rcases small (by omega) hs le sq with ⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> decide
    obtain ⟨p,hp,lo,hi,fail⟩ := interior x y (by omega) le (bertrand_bound (by omega) le sq)
    exact (fail (prime_filter hp lo hi le sq)).elim
  · simp only [Set.mem_insert_iff,Set.mem_singleton_iff,Prod.mk.injEq]
    rintro (⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩) <;> decide +kernel
end OMA.R_oeis_a082871_R1
