import OMAStatements.S_oeis_a334337
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.Tactic

/-!
Following @KoaOkano (#10671), retain the factorial-totient construction.
Use the prime-factor union API and direct positivity of a product factor.

Write F=n!. Every prime dividing φ(F) already divides F. Multiplication
of F by φ(F)^j therefore preserves its set of prime factors, multiplying
the totient by exactly φ(F)^j. This gives any positive power of φ(F),
including both the cube and the square in the problem.
-/

open Finset
open OMA.S_oeis_a334337

namespace FactorialTotients

lemma primes_closed (n q : ℕ) (hq : q.Prime) (hdiv : q ∣ n.factorial.totient) :
    q ∣ n.factorial := by
  let F := n.factorial
  have h := Nat.totient_mul_prod_primeFactors F
  have hd : q ∣ F * ∏ p ∈ F.primeFactors, (p-1) := by
    rw [← h]
    exact dvd_mul_of_dvd_left hdiv _
  rcases hq.dvd_mul.mp hd with done | inproduct
  · exact done
  obtain ⟨p, hp, hqp⟩ := (hq.prime.dvd_finsetProd_iff (fun t : ℕ => t-1)).mp inproduct
  have pp := Nat.prime_of_mem_primeFactors hp
  have pn : p ≤ n := pp.dvd_factorial.mp (Nat.dvd_of_mem_primeFactors hp)
  have hp1 : 0 < p-1 := by have := pp.two_le; omega
  exact hq.dvd_factorial.mpr ((Nat.le_of_dvd hp1 hqp).trans ((Nat.sub_le p 1).trans pn))

lemma totient_power (n j : ℕ) :
    (n.factorial * n.factorial.totient^j).totient = n.factorial.totient^(j+1) := by
  let F := n.factorial
  let h := F.totient
  have hF : F ≠ 0 := Nat.factorial_ne_zero _
  have ht : h ≠ 0 := Nat.totient_eq_zero.not.mpr hF
  have same : (F*h^j).primeFactors = F.primeFactors := by
    rw [Nat.primeFactors_mul hF (pow_ne_zero _ ht)]
    apply Finset.union_eq_left.mpr
    intro q hq
    have hp := Nat.prime_of_mem_primeFactors hq
    exact Nat.mem_primeFactors.mpr ⟨hp,
      primes_closed n q hp (hp.dvd_of_dvd_pow (Nat.dvd_of_mem_primeFactors hq)), hF⟩
  have left := Nat.totient_mul_prod_primeFactors (F*h^j)
  have right := Nat.totient_mul_prod_primeFactors F
  rw [same] at left
  have pos : 0 < ∏ p ∈ F.primeFactors, p :=
    Finset.prod_pos fun _ hp => Nat.pos_of_mem_primeFactors hp
  change (F*h^j).totient = h^(j+1)
  apply Nat.eq_of_mul_eq_mul_right pos
  calc
    _ = (F*h^j) * ∏ p ∈ F.primeFactors, (p-1) := left
    _ = h^j * (F * ∏ p ∈ F.primeFactors, (p-1)) := by ring
    _ = _ := by rw [← right, pow_succ]; change _ = h^j*h*_; ring

lemma multiplier (n j : ℕ) (hn : 0 < n) :
    ∃ m : ℕ, 0 < m ∧ (m*n).totient = n.factorial.totient^(j+1) := by
  obtain ⟨v, hv⟩ := Nat.dvd_factorial hn (le_refl n)
  have hvpos : 0 < v := Nat.pos_of_mul_pos_left (hv ▸ Nat.factorial_pos n)
  have hφ := Nat.totient_pos.mpr (Nat.factorial_pos n)
  refine ⟨v*n.factorial.totient^j, by positivity, ?_⟩
  have he : v*n.factorial.totient^j*n = n.factorial*n.factorial.totient^j := by
    conv_rhs => lhs; rw [hv]
    ring
  rw [he, totient_power]

end FactorialTotients

theorem OMA.solution : type_of% @OMA.S_oeis_a334337.main := by
  constructor
  · intro n hn
    obtain ⟨m, hm, he⟩ := FactorialTotients.multiplier n 2 hn
    exact ⟨m, hm, n.factorial.totient, he⟩
  · intro _ n hn
    obtain ⟨m, hm, he⟩ := FactorialTotients.multiplier n 1 hn
    exact ⟨m, hm, n.factorial.totient, by simpa [pow_two] using he⟩
