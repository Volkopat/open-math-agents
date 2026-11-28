import OMAStatements.S_oeis_a389789

/-! Use the prime immediately above half the residual sum to recognize consecutive pairs. -/

namespace OMA.R_oeis_a389789_R1

open OMA.S_oeis_a389789

/-- For odd inputs beyond the three explicit pairs, the two primes
straddling the residual midpoint must have the required sum. -/
def H1 : Prop := ∀ n : ℕ, 4 < n →
  ¬ (2*n-7).Prime → ¬ (2*n-11).Prime → ¬ (2*n-17).Prime →
  ∃ p : ℕ, p.Prime ∧
    let t := (2*n+1-p)/2
    0 < Nat.count Nat.Prime (t+1) ∧
    2*n+1 = p + prime (Nat.count Nat.Prime (t+1)) + sInf {r : ℕ | r.Prime ∧ t+1 ≤ r}

/-- For even inputs the three fixed pairs test the offsets four, six and nine. -/
def H2 : Prop := ∀ n : ℕ, 426 < n →
  ¬ (n-4).Prime → ¬ (n-6).Prime → ¬ (n-9).Prime →
  ∃ p : ℕ, p.Prime ∧
    let t := n-p
    0 < Nat.count Nat.Prime (t+1) ∧
    2*n = 2*p + prime (Nat.count Nat.Prime (t+1)) + sInf {r : ℕ | r.Prime ∧ t+1 ≤ r}

lemma successor (t : ℕ) :
    prime (Nat.count Nat.Prime (t+1) + 1) = sInf {r : ℕ | r.Prime ∧ t+1 ≤ r} := by
  simp only [prime, Nat.add_sub_cancel]
  exact Nat.nth_count_eq_sInf Nat.Prime _

lemma small_pairs : prime 2 + prime 3 = 8 ∧ prime 3 + prime 4 = 12 ∧
    prime 4 + prime 5 = 18 := by
  norm_num [prime,Nat.nth_prime_one_eq_three,Nat.nth_prime_two_eq_five,
    Nat.nth_prime_three_eq_seven,Nat.nth_prime_four_eq_eleven]

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a389789.main := by
  intro oddCase evenCase
  obtain ⟨h8,h12,h18⟩ := small_pairs
  constructor
  · intro n hn
    by_cases a : (2*n-7).Prime
    · exact ⟨_,2,a,by decide,by change _ = _ + prime 2 + prime 3; omega⟩
    by_cases b : (2*n-11).Prime
    · have := b.two_le
      exact ⟨_,3,b,by decide,by change _ = _ + prime 3 + prime 4; omega⟩
    by_cases c : (2*n-17).Prime
    · have := c.two_le
      exact ⟨_,4,c,by decide,by change _ = _ + prime 4 + prime 5; omega⟩
    obtain ⟨p,hp,ht,he⟩ := oddCase n hn a b c
    exact ⟨p,_,hp,ht,by rwa [successor]⟩
  · intro n hn
    by_cases a : (n-4).Prime
    · exact ⟨_,2,a,by decide,by change _ = _ + prime 2 + prime 3; omega⟩
    by_cases b : (n-6).Prime
    · exact ⟨_,3,b,by decide,by change _ = _ + prime 3 + prime 4; omega⟩
    by_cases c : (n-9).Prime
    · exact ⟨_,4,c,by decide,by change _ = _ + prime 4 + prime 5; omega⟩
    obtain ⟨p,hp,ht,he⟩ := evenCase n hn a b c
    exact ⟨p,_,hp,ht,by rwa [successor]⟩

end OMA.R_oeis_a389789_R1
