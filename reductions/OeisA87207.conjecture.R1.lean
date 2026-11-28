import FormalConjectures.OEIS.«87207»

/-!
Karttunen's iteration encodes the prime support as a binary integer.
Every singleton support terminates. So does every two-prime support whose
prime indices differ by at most four, independently of both exponents and
of the position of the first prime. The remaining question needs only the
squarefree products of the other supports.
-/

namespace OMA.R_OeisA87207_conjecture_R1

open OeisA87207

def H1 : Prop := ∀ e c : ℕ, c ∈ ({1,2,3,5,9,17} : Finset ℕ) →
    ∃ k : ℕ, (a^[k]) (2^e*c) = 0

def H2 : Prop := ∀ s : Finset ℕ, (∀ p ∈ s, p.Prime) → 2 ≤ s.card →
    (∀ p q, p < q → s = {p,q} → 4 < q.primeCounting - p.primeCounting) →
    ∃ k : ℕ, (a^[k]) (∏ p ∈ s, p) = 0

section

private theorem backwards {n : ℕ} (h : ∃ k : ℕ, (a^[k]) (a n) = 0) :
    ∃ k : ℕ, (a^[k]) n = 0 := by
  obtain ⟨k,hk⟩ := h
  exact ⟨k+1, by simpa only [Function.iterate_succ_apply] using hk⟩

private theorem encode_pair {p q n : ℕ} (hpq : p < q) (hs : n.primeFactors = {p,q})
    (hg : q.primeCounting - p.primeCounting ≤ 4) (h : H1) :
    ∃ k : ℕ, (a^[k]) n = 0 := by
  have hp : p.Prime := Nat.prime_of_mem_primeFactors (n:=n) (by simp [hs])
  have hlow : 1 ≤ p.primeCounting := by
    have hh := Nat.monotone_primeCounting hp.two_le
    exact hh
  have hmono := Nat.monotone_primeCounting hpq.le
  let g := q.primeCounting - p.primeCounting
  have hindex : q.primeCounting-1 = p.primeCounting-1 + g := by dsimp [g]; omega
  have hc : 1 + 2^g ∈ ({1,2,3,5,9,17} : Finset ℕ) := by
    have hg' : g ≤ 4 := hg
    interval_cases g <;> decide
  have he : a n = 2^(p.primeCounting-1)*(1+2^g) := by
    simp [a,Nat.support_factorization,hs,hpq.ne,hindex,pow_add,Nat.mul_add]
  apply backwards
  rw [he]
  exact h _ _ hc

private theorem radical_transfer {n : ℕ}
    (h : ∃ k : ℕ, (a^[k]) (∏ p ∈ n.primeFactors, p) = 0) :
    ∃ k : ℕ, (a^[k]) n = 0 := by
  obtain ⟨k,hk⟩ := h
  cases k with
  | zero =>
    have hpos : 0 < ∏ p ∈ n.primeFactors, p :=
      Finset.prod_pos (fun p hp => (Nat.prime_of_mem_primeFactors hp).pos)
    change (∏ p ∈ n.primeFactors, p) = 0 at hk
    omega
  | succ k =>
    apply backwards
    use k
    simpa only [Function.iterate_succ_apply, a, Nat.support_factorization,
      Nat.primeFactors_prod_primeFactors] using hk

end

theorem main : H1 → H2 → type_of% @OeisA87207.conjecture := by
  intro small wide n
  by_cases hc : 2 ≤ n.primeFactors.card
  · by_cases hg : ∀ p q, p < q → n.primeFactors = {p,q} →
        4 < q.primeCounting - p.primeCounting
    · exact radical_transfer (wide _ (fun _ => Nat.prime_of_mem_primeFactors) hc hg)
    push Not at hg
    obtain ⟨p,q,hpq,hs,hg⟩ := hg
    exact encode_pair hpq hs hg small
  apply backwards
  by_cases hz : n.primeFactors.card = 0
  · have hs := Finset.card_eq_zero.mp hz
    exact ⟨0, by simp [a,hs]⟩
  have hs : n.primeFactors.card = 1 := by omega
  obtain ⟨p,hp⟩ := Finset.card_eq_one.mp hs
  have hx := small (p.primeCounting-1) 1 (by decide)
  simpa [a,hp] using hx

end OMA.R_OeisA87207_conjecture_R1
