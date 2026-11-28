import FormalConjectures.Wikipedia.BrocardConjecture

-- Credit: @menelikbaye-digitalmethod
namespace OMA.R_Brocard_brocard_conjecture_R1

open Finset

-- The two halves of the interval between consecutive squares.
def H1 : Prop := ∀ x : ℕ, 2 ≤ x → ∃ p : ℕ, p.Prime ∧ x^2 < p ∧ p < x*(x+1)

def H2 : Prop := ∀ x : ℕ, 2 ≤ x → ∃ p : ℕ, p.Prime ∧ x*(x+1) < p ∧ p < (x+1)^2

theorem main : H1 → H2 → type_of% @Brocard.brocard_conjecture := by
  intro lower upper n hn
  let p := Nat.nth Nat.Prime n
  let q := Nat.nth Nat.Prime (n+1)
  have mono := Nat.nth_strictMono Nat.infinite_setOf_prime
  have hp : 3 ≤ p := Nat.nth_prime_one_eq_three ▸ mono.monotone hn
  have hpq : p < q := mono (Nat.lt_succ_self n)
  have pp : p.Prime := Nat.nth_mem_of_infinite Nat.infinite_setOf_prime n
  have qp : q.Prime := Nat.nth_mem_of_infinite Nat.infinite_setOf_prime (n+1)
  have po := pp.odd_of_ne_two (by omega)
  have qo := qp.odd_of_ne_two (by omega)
  obtain ⟨i, hi⟩ := po
  obtain ⟨j, hj⟩ := qo
  have gap : p+2 ≤ q := by omega
  have bound : ((p+1)+1)^2 ≤ q^2 := Nat.pow_le_pow_left (by omega) 2
  obtain ⟨a, ha, la, ua⟩ := lower p (by omega)
  obtain ⟨b, hb, lb, ub⟩ := upper p (by omega)
  obtain ⟨c, hc, lc, uc⟩ := lower (p+1) (by omega)
  obtain ⟨d, hd, ld, ud⟩ := upper (p+1) (by omega)
  have ab : a < b := ua.trans lb
  have bc : b < c := ub.trans lc
  have cd : c < d := uc.trans ld
  have subset : ({a,b,c,d} : Finset ℕ) ⊆ (Ioo (p^2) (q^2)).filter Nat.Prime := by
    intro x hx
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> simp only [mem_filter, mem_Ioo] <;> exact ⟨⟨by omega, by omega⟩, by assumption⟩
  have four : ({a,b,c,d} : Finset ℕ).card = 4 := by
    simp [ab.ne, (ab.trans bc).ne, ((ab.trans bc).trans cd).ne, bc.ne, (bc.trans cd).ne, cd.ne]
  exact four ▸ Finset.card_le_card subset

end OMA.R_Brocard_brocard_conjecture_R1
