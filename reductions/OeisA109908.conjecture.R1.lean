import FormalConjectures.OEIS.«109908»

/-!
For n > 3 the two outside factors k=1,2 cover the shifted primes
n=p+2 and n=(p+5)/2. The first step turns each square discriminant n²−4(p+1)
with the required parity into a lower bound p on the maximum.
For the remaining inputs the even case needs only numbers 3 modulo 4
of the form 4j(t−j)−1; the odd case is a triangular-offset search below
the central product t(t+1).
-/

namespace OMA.R_OeisA109908_conjecture_R1

open OeisA109908

def H1 : Prop := ∀ n p : ℕ, 3 < n → p.Prime →
    (∃ d : ℕ, d < n ∧ d%2 = n%2 ∧ n^2 = d^2+4*(p+1)) →
    p ≤ a n

def H2 : Prop := ∀ t : ℕ, 3 < 2*t → ¬(2*t-2).Prime → ¬(4*t-5).Prime →
    ∃ j p : ℕ, 0 < j ∧ 2*j ≤ t ∧ p.Prime ∧ p+1 = 4*j*(t-j)

def H3 : Prop := ∀ t : ℕ, 3 < 2*t+1 → ¬(2*t-1).Prime → ¬(4*t-3).Prime →
    ∃ u p : ℕ, u < t ∧ p.Prime ∧ p+1+u*(u+1) = t*(t+1)

section

private theorem factor_witness (h : H1) (n k p : ℕ) (hn : 3 < n)
    (hk : 0 < k) (hb : 2*k ≤ n) (hp : p.Prime) (he : p+1 = k*(n-k)) :
    0 < a n := by
  have hdisc : n^2 = (n-2*k)^2+4*(p+1) := by
    obtain ⟨v,hv⟩ := Nat.exists_eq_add_of_le hb
    rw [he,hv]
    simp only [Nat.add_sub_cancel_left]
    rw [show 2*k+v-k = k+v by omega]
    ring
  exact hp.pos.trans_le (h n p hn hp ⟨n-2*k,by omega,by omega,hdisc⟩)

private theorem outer_one (h : H1) (n : ℕ) (hn : 3 < n) (hp : (n-2).Prime) :
    0 < a n := by
  apply factor_witness h n 1 (n-2) hn (by decide) (by omega) hp
  omega

private theorem outer_two (h : H1) (n : ℕ) (hn : 3 < n) (hp : (2*n-5).Prime) :
    0 < a n := by
  apply factor_witness h n 2 (2*n-5) hn (by decide) (by omega) hp
  omega

private theorem even_interior (h : H1) (t j p : ℕ) (ht : 3 < 2*t)
    (hj : 0 < j) (hb : 2*j ≤ t) (hp : p.Prime) (he : p+1 = 4*j*(t-j)) :
    0 < a (2*t) := by
  apply factor_witness h (2*t) (2*j) p ht (by omega) (by omega) hp
  rw [he,show 2*t-2*j = 2*(t-j) by omega]
  ring

private theorem odd_interior (h : H1) (t u p : ℕ) (ht : 3 < 2*t+1)
    (hu : u < t) (hp : p.Prime) (he : p+1+u*(u+1) = t*(t+1)) :
    0 < a (2*t+1) := by
  apply factor_witness h (2*t+1) (t-u) p ht (by omega) (by omega) hp
  have h₁ : t-u+u = t := by omega
  have h₂ : 2*t+1-(t-u) = t+u+1 := by omega
  rw [h₂]
  nlinarith [congrArg (fun v : ℕ => v*(t+u+1)) h₁]

end

theorem main : H1 → H2 → H3 → type_of% @OeisA109908.conjecture := by
  intro hd evenCase oddCase n hn
  by_cases h₁ : (n-2).Prime
  · exact outer_one hd n hn h₁
  by_cases h₂ : (2*n-5).Prime
  · exact outer_two hd n hn h₂
  let t := n/2
  rcases (show n=2*t ∨ n=2*t+1 by dsimp [t]; omega) with he|he
  · have ht : 3 < 2*t := by omega
    obtain ⟨j,p,hj,hb,hp,hh⟩ := evenCase t ht (by simpa only [← he] using h₁)
      (by rwa [show 4*t-5 = 2*n-5 by omega])
    exact he ▸ even_interior hd t j p ht hj hb hp hh
  · have ht : 3 < 2*t+1 := by omega
    obtain ⟨u,p,hu,hp,hh⟩ := oddCase t ht
      (by rwa [show 2*t-1 = n-2 by omega]) (by rwa [show 4*t-3 = 2*n-5 by omega])
    exact he ▸ odd_interior hd t u p ht hu hp hh

end OMA.R_OeisA109908_conjecture_R1
