import OMAReductions.R_CarmichaelTotient_charmichaelTotient_R1
import Mathlib

/-! The prime exchange of Carmichael and Klee forces additional prime
squares, according to whether the 3-adic exponent is two or at least three. -/
open CarmichaelTotient Nat
namespace CarmichaelExchange

theorem totient_mul_retaining_primes (a b : ℕ)
    (support : ∀ q, q.Prime → q ∣ a → q ∣ b) :
    (a*b).totient = a*b.totient := by
  revert b support
  induction a using induction_on_primes with
  | zero => simp
  | one => simp
  | prime_mul p a hp ih =>
    intro b support
    have hb : p ∣ b := support p hp (dvd_mul_right p a)
    have hab : p ∣ a*b := dvd_mul_of_dvd_right hb a
    have hs : ∀ q, q.Prime → q ∣ a → q ∣ b :=
      fun q hq hqa ↦ support q hq (dvd_mul_of_dvd_right hqa p)
    simp only [Nat.mul_assoc,totient_mul_of_prime_of_dvd hp hab,ih b hs]

theorem forced_square {n d e r p : ℕ} (hn : 0 < n) (prime : p.Prime)
    (split : n = d*(e*r)) (cop : d.Coprime (e*r))
    (suppE : ∀ q, q.Prime → q ∣ e → q ∣ r) (factor : p-1 = e*d.totient)
    (suppP : ∀ q, q.Prime → q ∣ p-1 → q ∣ n) :
    CarmichaelTotientFor n ∨ p^2 ∣ n := by
  by_cases sq : p^2 ∣ n
  · exact Or.inr sq
  left
  have two := prime.two_le
  by_cases divides : p ∣ n
  · obtain ⟨k,hnk⟩ := divides
    have notDiv : ¬ p ∣ k := by
      rintro ⟨t,ht⟩
      exact sq ⟨t,by rw [hnk,ht]; ring⟩
    have kp : 0 < k := by
      rcases Nat.eq_zero_or_pos k with h | h
      · rw [hnk,h,Nat.mul_zero] at hn
        omega
      · exact h
    have support (q : ℕ) (hq : q.Prime) (hd : q ∣ p-1) : q ∣ k := by
      have qlt : q < p := by
        have := Nat.le_of_dvd (by omega : 0 < p-1) hd
        omega
      have qNot : ¬ q ∣ p := fun h ↦ (Nat.ne_of_lt qlt) ((Nat.dvd_prime_two_le prime hq.two_le).mp h)
      have div := suppP q hq hd
      rw [hnk] at div
      exact (hq.dvd_mul.mp div).resolve_left qNot
    refine ⟨(p-1)*k,Nat.ne_of_lt ?_,?_⟩
    · rw [hnk]
      exact Nat.mul_lt_mul_of_pos_right (by omega) kp
    · rw [hnk,totient_mul_retaining_primes _ _ support,
        totient_mul_of_prime_of_not_dvd prime notDiv]
  · have notDiv : ¬ p ∣ r :=
      fun hr ↦ divides (split ▸ dvd_mul_of_dvd_right (dvd_mul_of_dvd_right hr e) d)
    refine ⟨p*r,?_ ,?_⟩
    · intro eq
      exact divides (eq ▸ dvd_mul_right p r)
    · calc
        (p*r).totient = (p-1)*r.totient := totient_mul_of_prime_of_not_dvd prime notDiv
        _ = (d*(e*r)).totient := by
          rw [factor,totient_mul cop,totient_mul_retaining_primes _ _ suppE]
          ring
        _ = n.totient := congrArg Nat.totient split.symm

theorem low_three {n e p : ℕ} (hn : 0 < n) (h6 : 6 ∣ n) (low : ¬ 27 ∣ n)
    (hd : 9*e^2 ∣ n) (prime : p.Prime) (pval : p-1=e*6) :
    CarmichaelTotientFor n ∨ p^2 ∣ n := by
  obtain ⟨a,ha⟩ := hd
  have fullSplit : n=9*(e*(e*a)) := by rw [ha]; ring
  have no3 : ¬ 3 ∣ e*(e*a) := by
    rintro ⟨t,ht⟩
    exact low ⟨t,by rw [fullSplit,ht]; ring⟩
  have cop : (9 : ℕ).Coprime (e*(e*a)) :=
    ((prime_three.coprime_iff_not_dvd).mpr no3).pow_left 2
  apply forced_square hn prime fullSplit cop
  · intro q _ hq
    exact dvd_trans hq (dvd_mul_right e a)
  · have v : (9 : ℕ).totient = 6 := by decide
    rwa [v]
  · intro q hq hdiv
    rw [pval] at hdiv
    rcases hq.dvd_mul.mp hdiv with x | x
    · exact dvd_trans x ⟨9*e*a,by rw [fullSplit]; ring⟩
    · exact dvd_trans x h6

theorem unit_factor {n e f p : ℕ} (hn : 0 < n) (hd : e*f ∣ n)
    (prime : p.Prime) (val : p-1=e) (cover : ∀ q, q.Prime → q ∣ e → q ∣ f) :
    CarmichaelTotientFor n ∨ p^2 ∣ n := by
  obtain ⟨a,ha⟩ := hd
  have fullSplit : n=1*(e*(f*a)) := by rw [ha]; ring
  apply forced_square hn prime fullSplit (coprime_one_left _)
  · intro q hq hq'
    exact dvd_trans (cover q hq hq') (dvd_mul_right f a)
  · simpa only [totient_one,Nat.mul_one] using val
  · intro q _ hq
    rw [val] at hq
    exact dvd_trans hq ⟨f*a,by simpa using fullSplit⟩

theorem high_three {n e p : ℕ} (hn : 0 < n) (hd : (3*e)*e ∣ n)
    (prime : p.Prime) (val : p-1=3*e) (e3 : 3 ∣ e) :
    CarmichaelTotientFor n ∨ p^2 ∣ n :=
  unit_factor hn hd prime val (fun _q hq hq' ↦
    (hq.dvd_mul.mp hq').elim (fun x ↦ dvd_trans x e3) id)

end CarmichaelExchange

namespace OMA.R_CarmichaelTotient_charmichaelTotient_R1_H4_R1
open CarmichaelExchange

/-- The remaining case when the exponent of three is exactly two. -/
def H1 : Prop := ∀ n : ℕ, 0 < n → 36 ∣ n → 49 ∣ n → 1849 ∣ n → ¬ 27 ∣ n →
  169 ∣ n → 6241 ∣ n → 24649 ∣ n → CarmichaelTotientFor n

/-- The remaining case when the exponent of three is at least three. -/
def H2 : Prop := ∀ n : ℕ, 0 < n → 108 ∣ n → 49 ∣ n → 1849 ∣ n →
  361 ∣ n → 16129 ∣ n → CarmichaelTotientFor n

theorem main : H1 → H2 → OMA.R_CarmichaelTotient_charmichaelTotient_R1.H4 := by
  intro low high n hn h36 h49 h43
  by_cases h27 : 27 ∣ n
  · have h4 : 4 ∣ n := dvd_trans (by decide : 4 ∣ 36) h36
    have h108 : 108 ∣ n := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by decide : Coprime 4 27) h4 h27
    have h5292 : 5292 ∣ n := Nat.Coprime.mul_dvd_of_dvd_of_dvd
      (by decide : Coprime 108 49) h108 h49
    rcases high_three (e:=6) (p:=19) hn h108 (by decide) (by decide) (by decide) with h | h19
    · exact h
    rcases high_three (e:=42) (p:=127) hn h5292 (by decide) (by decide) (by decide) with h | h127
    · exact h
    exact high n hn h108 h49 h43 h19 h127
  · have h6 : 6 ∣ n := dvd_trans (by decide : 6 ∣ 36) h36
    rcases low_three (e:=2) (p:=13) hn h6 h27 h36 (by decide) (by decide) with h | h13
    · exact h
    have h6084 : 6084 ∣ n := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by decide : Coprime 36 169) h36 h13
    rcases unit_factor (e:=78) (f:=78) (p:=79) hn h6084 (by decide) (by decide)
      (fun _ _ hq ↦ hq) with h | h79
    · exact h
    rcases low_three (e:=26) (p:=157) hn h6 h27 h6084 (by decide) (by decide) with h | h157
    · exact h
    exact low n hn h36 h49 h43 h27 h13 h79 h157

end OMA.R_CarmichaelTotient_charmichaelTotient_R1_H4_R1
