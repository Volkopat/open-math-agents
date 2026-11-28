import FormalConjectures.OEIS.«240088»

/-!
Triangular, square and pentagonal sums. The slice with pentagonal index
zero follows from composition of the norm x²+2y²: it suffices that each
prime in 8n+1 occurring to odd order is itself such a norm. For the other
inputs the remaining question asks for a pentagonal shift satisfying a
binary norm equation. Reduction modulo eight recovers the correct parities
of the two coordinates, as well as the triangular and square witnesses.
-/

namespace OMA.R_OeisA240088_conjecture_R1

open OeisA240088

def H1 : Prop := ∀ m : ℕ, 0 < m →
    (∀ p ∈ m.primeFactors, Odd (m.factorization p) →
      ∃ u v : ℕ, p = u^2 + 2*v^2) →
    ∃ x y : ℕ, m = x^2 + 2*y^2

def H2 : Prop := ∀ n : ℕ, (∃ p ∈ (8*n+1).primeFactors,
    Odd ((8*n+1).factorization p) ∧ ¬ ∃ u v : ℕ, p = u^2 + 2*v^2) →
    ∃ k : ℕ, k ≤ n+1 ∧ Nat.polygonalNumber 5 k ≤ n ∧
    ∃ x y : ℕ, 8*(n-Nat.polygonalNumber 5 k)+1 = x^2 + 2*y^2

section

private theorem norm_parity (m x y : ℕ) (he : 8*m+1 = x^2+2*y^2) :
    x%2=1 ∧ y%2=0 := by
  have hm := congrArg (fun a : ℕ => a%8) he
  have hx := Nat.mod_lt x (by decide : 0<8)
  have hy := Nat.mod_lt y (by decide : 0<8)
  simp only [Nat.add_mod,Nat.mul_mod,Nat.pow_mod x,Nat.pow_mod y,Nat.mod_self,
    zero_mul,Nat.zero_mod,zero_add,Nat.one_mod,Nat.mod_mod] at hm
  generalize ha : x%8=a at hm hx
  generalize hb : y%8=b at hm hy
  have good : a%2=1 ∧ b%2=0 := by
    interval_cases a <;> interval_cases b <;> first | decide | norm_num at hm
  omega

private theorem split_norm (m x y : ℕ) (he : 8*m+1 = x^2+2*y^2) :
    ∃ i j : ℕ, i ≤ m ∧ j ≤ m ∧ Nat.triangular i + j^2 = m := by
  obtain ⟨hx,hy⟩ := norm_parity m x y he
  let i := x/2
  let j := y/2
  have h₁ : x = 2*i+1 := by dsimp [i]; omega
  have h₂ : y = 2*j := by dsimp [j]; omega
  rw [h₁,h₂] at he
  have heven : 2 ∣ i*(i+1) := by
    rcases Nat.even_or_odd i with ⟨v,hv⟩|⟨v,hv⟩
    · exact dvd_mul_of_dvd_left ⟨v,by omega⟩ _
    · exact dvd_mul_of_dvd_right ⟨v+1,by omega⟩ _
  have hhalf := Nat.div_mul_cancel heven
  have hval : Nat.triangular i+j^2=m := by
    unfold Nat.triangular
    nlinarith only [he,hhalf]
  refine ⟨i,j,?_,?_,hval⟩
  · nlinarith only [he,Nat.le_self_pow (by decide : 2≠0) i]
  · nlinarith only [he,Nat.le_self_pow (by decide : 2≠0) j]

private theorem insert_witness (n k x y : ℕ) (hk : k ≤ n+1)
    (hkn : Nat.polygonalNumber 5 k ≤ n)
    (he : 8*(n-Nat.polygonalNumber 5 k)+1 = x^2 + 2*y^2) : 0 < a n := by
  obtain ⟨i,j,hi,hj,hij⟩ := split_norm _ _ _ he
  have heq : Nat.triangular i+j^2+Nat.polygonalNumber 5 k=n := by omega
  simp only [a,Finset.sum_pos_iff,Finset.mem_range]
  refine ⟨i,by omega,j,by omega,k,by omega,?_⟩
  simp [heq]

end

theorem main : H1 → H2 → type_of% @OeisA240088.conjecture := by
  intro norm shift n
  by_cases h : ∀ p ∈ (8*n+1).primeFactors, Odd ((8*n+1).factorization p) →
      ∃ u v : ℕ, p = u^2 + 2*v^2
  · obtain ⟨x,y,he⟩ := norm (8*n+1) (by omega) h
    exact insert_witness n 0 x y (by omega) (by simp) (by simpa using he)
  push Not at h
  obtain ⟨p,hp,hodd,hbad⟩ := h
  obtain ⟨k,hk,hkn,x,y,he⟩ := shift n ⟨p,hp,hodd,by simpa using hbad⟩
  exact insert_witness n k x y hk hkn he

end OMA.R_OeisA240088_conjecture_R1
