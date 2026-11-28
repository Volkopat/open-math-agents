import OMAStatements.S_oeis_a107587

-- Credit: @CubeJerry (the owner of the agent is credited as the solver)

/-!
A proof of both Mathar recurrences for A107587.

The parity factor in the defining sum selects the terms with k = 2j.
We reindex this finite sum to the hypergeometric summand
F(n,j) = binomial(n,4j) Catalan(2j). A rational telescoping certificate
R(n,j) = -64 j^2 (2j-1)(2j+1)/n proves the recurrence of order four;
the support of the binomial coefficient makes both telescope endpoints zero.
The difference of two consecutive instances of this recurrence is n-2 times
the recurrence of order five. Both universal identities follow over integers.

The OEIS entry attributes the conjectures to R. J. Mathar (February 20, 2015)
and records Gennady Eremin's computational verification through n = 800.
-/

namespace OMA.T107587

def back (n k : ℚ) : ℚ := (n-4*k)/n

def right (n k : ℚ) : ℚ :=
  (n-4*k)*(n-4*k-1)*(n-4*k-2)*(n-4*k-3)/
    ((2*k+1)*(2*k+2)^2*(2*k+3))

def R (n k : ℚ) : ℚ := -64*k^2*(2*k-1)*(2*k+1)/n

def p0 (n : ℚ) : ℚ := n*(n-2)*(n+2)
def p1 (n : ℚ) : ℚ := -(2*n-1)*(2*n^2-2*n-3)
def p2 (n : ℚ) : ℚ := 3*(n-1)*(2*n^2-4*n+1)
def p3 (n : ℚ) : ℚ := -2*(n-1)*(n-2)*(2*n-3)
def p4 (n : ℚ) : ℚ := -15*(n-1)*(n-2)*(n-3)

lemma R_zero (n : ℚ) : R n 0 = 0 := by simp [R]

lemma certQ (n k : ℚ) (hn : 4 ≤ n) (hk : 0 ≤ k) :
    right n k*R n (k+1)-R n k =
      p0 n+p1 n*back n k+p2 n*back n k*back (n-1) k+
      p3 n*back n k*back (n-1) k*back (n-2) k+
      p4 n*back n k*back (n-1) k*back (n-2) k*back (n-3) k := by
  have hn0 : n ≠ 0 := by linarith
  have hn1 : n-1 ≠ 0 := by linarith
  have hn2 : n-2 ≠ 0 := by linarith
  have hn3 : n-3 ≠ 0 := by linarith
  have hk1 : 2*k+1 ≠ 0 := by linarith
  have hk2 : 2*k+2 ≠ 0 := by linarith
  have hk3 : 2*k+3 ≠ 0 := by linarith
  unfold right R back p0 p1 p2 p3 p4
  field_simp
  ring

end OMA.T107587

namespace OMA.T107587

noncomputable def F (n k : ℕ) : ℚ :=
  (n.choose (4*k) : ℚ) * (catalan (2*k) : ℚ)


lemma F_zero4 (n k : ℕ) (h : n < 4*k) : F n k = 0 := by
  simp [F, Nat.choose_eq_zero_of_lt h]

lemma F_zero (n k : ℕ) (h : n < k) : F n k = 0 := F_zero4 n k (by omega)

lemma choose_rat (n k : ℕ) (hk : k ≤ n) :
    (n.choose k : ℚ) = (n.factorial : ℚ) /
      ((k.factorial : ℚ) * ((n-k).factorial : ℚ)) := by
  apply (eq_div_iff (by positivity)).2
  have h := Nat.choose_mul_factorial_mul_factorial hk
  exact_mod_cast (by simpa [mul_assoc] using h)

lemma catalan_rat (m : ℕ) :
    (catalan m : ℚ) = ((2*m).factorial : ℚ) /
      ((m.factorial : ℚ) * ((m+1).factorial : ℚ)) := by
  apply (eq_div_iff (by positivity)).2
  have h := Nat.choose_mul_factorial_mul_factorial (n := 2*m) (k := m) (by omega)
  rw [show 2*m-m=m by omega] at h
  change m.centralBinom * m.factorial * m.factorial = (2*m).factorial at h
  rw [← succ_mul_catalan_eq_centralBinom] at h
  have hq := congrArg (fun t : ℕ => (t:ℚ)) h
  rw [Nat.factorial_succ]
  push_cast at hq ⊢
  linear_combination hq

lemma F_factorial (n k : ℕ) (hk : 4*k ≤ n) :
    F n k = (n.factorial : ℚ) /
      (((2*k).factorial : ℚ) * ((2*k+1).factorial : ℚ) * ((n-4*k).factorial : ℚ)) := by
  rw [F, choose_rat n (4*k) hk, catalan_rat]
  rw [show 2*(2*k)=4*k by omega]
  field_simp

lemma backF_succ (n k : ℕ) : F n k = F (n+1) k * back ((n:ℚ)+1) k := by
  by_cases hk : 4*k ≤ n+1
  · have hc : (n.choose (4*k) : ℚ) =
        ((n+1).choose (4*k) : ℚ) * (((n:ℚ)+1)-4*k) / ((n:ℚ)+1) := by
      apply (eq_div_iff (by positivity)).2
      have h := congrArg (fun t : ℕ => (t : ℚ)) (Nat.choose_mul_succ_eq n (4*k))
      push_cast [Nat.cast_sub hk] at h
      exact h
    rw [F, F, hc]
    unfold back
    ring
  · rw [F_zero4 n k (by omega), F_zero4 (n+1) k (by omega)]
    simp

lemma backF (n k : ℕ) (hn : 1 ≤ n) : F (n-1) k = F n k * back n k := by
  have hc : ((n-1 : ℕ) : ℚ)+1 = (n:ℚ) := by exact_mod_cast Nat.sub_add_cancel hn
  simpa only [Nat.sub_add_cancel hn, hc] using backF_succ (n-1) k

lemma fact_step (m : ℕ) (hm : 1 ≤ m) :
    (m.factorial : ℚ) = (m : ℚ) * ((m-1).factorial : ℚ) := by
  conv_lhs => rw [show m = m-1+1 by omega]
  rw [Nat.factorial_succ]
  push_cast [Nat.cast_sub hm]
  ring

lemma fact_two_step (m : ℕ) (hm : 2 ≤ m) :
    (m.factorial : ℚ) = (m:ℚ)*((m:ℚ)-1)*((m-2).factorial : ℚ) := by
  rw [fact_step m (by omega), fact_step (m-1) (by omega)]
  rw [show m-1-1=m-2 by omega]
  push_cast [Nat.cast_sub (show 1 ≤ m by omega)]
  ring

lemma fact_four_step (m : ℕ) (hm : 4 ≤ m) :
    (m.factorial : ℚ) = (m:ℚ)*((m:ℚ)-1)*((m:ℚ)-2)*((m:ℚ)-3)*
      ((m-4).factorial : ℚ) := by
  rw [fact_two_step m (by omega), fact_two_step (m-2) (by omega)]
  rw [show m-2-2=m-4 by omega]
  push_cast [Nat.cast_sub (show 2 ≤ m by omega)]
  ring

lemma rightF (n k : ℕ) : F n (k+1) = F n k * right n k := by
  by_cases hk : 4*(k+1) ≤ n
  · rw [F_factorial n (k+1) hk, F_factorial n k (by omega)]
    rw [show 2*(k+1)=2*k+2 by omega, show 2*k+2+1=2*k+3 by omega,
      show n-4*(k+1)=n-4*k-4 by omega]
    rw [fact_two_step (2*k+2) (by omega), fact_two_step (2*k+3) (by omega),
      fact_four_step (n-4*k) (by omega)]
    rw [show 2*k+2-2=2*k by omega, show 2*k+3-2=2*k+1 by omega,
      Nat.factorial_succ (2*k)]
    unfold right
    push_cast [Nat.cast_sub (show 4*k ≤ n by omega)]
    have hnq : 4*((k:ℚ)+1) ≤ n := by exact_mod_cast hk
    have hkq : (0:ℚ) ≤ k := by positivity
    field_simp (disch := first | positivity | linarith)
    ring
  · rw [F_zero4 n (k+1) (by omega)]
    by_cases hk' : n < 4*k
    · rw [F_zero4 n k hk']
      simp
    · have hcases : n=4*k ∨ n=4*k+1 ∨ n=4*k+2 ∨ n=4*k+3 := by omega
      have hr : right (n:ℚ) k = 0 := by
        rcases hcases with h | h | h | h
        · have he : (n:ℚ)-4*k=0 := by exact_mod_cast (show (n:ℤ)-4*k=0 by omega)
          simp [right,he]
        · have he : (n:ℚ)-4*k=1 := by exact_mod_cast (show (n:ℤ)-4*k=1 by omega)
          simp [right,he]
        · have he : (n:ℚ)-4*k=2 := by exact_mod_cast (show (n:ℤ)-4*k=2 by omega)
          simp [right,he]
        · have he : (n:ℚ)-4*k=3 := by exact_mod_cast (show (n:ℤ)-4*k=3 by omega)
          simp [right,he]
      rw [hr,mul_zero]

end OMA.T107587

namespace OMA.T107587

lemma repr (n : ℕ) : (OMA.S_oeis_a107587.a n : ℚ) =
    ∑ j ∈ Finset.range (n+1), F n j := by
  unfold OMA.S_oeis_a107587.a
  rw [Nat.cast_sum]
  simp only [Nat.cast_mul]
  apply Finset.sum_bij_ne_zero (fun k _ _ => k/2)
  · intro k hk hk0
    simp only [Finset.mem_range] at hk ⊢
    omega
  · intro k hk hk0 l hl hl0 hkl
    have hkp : (k+1)%2 ≠ 0 := by intro h; simp [h] at hk0
    have hlp : (l+1)%2 ≠ 0 := by intro h; simp [h] at hl0
    omega
  · intro j hj hj0
    have h4j : 4*j ≤ n := by
      by_contra hn
      exact hj0 (F_zero4 n j (by omega))
    refine ⟨2*j, Finset.mem_range.mpr (by omega), ?_, by omega⟩
    simpa only [show 2*(2*j)=4*j by omega, show (2*j+1)%2=1 by omega,
      Nat.cast_one, mul_one, F] using hj0
  · intro k hk hk0
    have hkp : (k+1)%2 ≠ 0 := by intro h; simp [h] at hk0
    have hkdiv : 2*(k/2)=k := by omega
    have hkmod : (k+1)%2=1 := by omega
    unfold F
    rw [show 4*(k/2)=2*k by omega, hkdiv, hkmod, Nat.cast_one, mul_one]

end OMA.T107587

namespace OMA.T107587

open scoped BigOperators

lemma sum_extend_zero (t : ℕ → ℕ → ℚ)
    (hz : ∀ m k : ℕ, m < k → t m k = 0)
    (m N : ℕ) (hm : m ≤ N) :
    (∑ k ∈ Finset.range (N + 1), t m k) =
      ∑ k ∈ Finset.range (m + 1), t m k := by
  symm
  apply Finset.sum_subset (Finset.range_mono (by omega))
  intro k hk hkm
  apply hz
  simp only [Finset.mem_range, not_lt] at hkm
  omega

lemma sum_certificate5 (t : ℕ → ℕ → ℚ)
    (hz : ∀ m k : ℕ, m < k → t m k = 0)
    (n : ℕ) (c0 c1 c2 c3 c4 : ℚ) (G : ℕ → ℚ)
    (hG0 : G 0 = 0) (hG1 : G (n + 1) = 0)
    (hcert : ∀ k : ℕ, k ≤ n →
      c0 * t n k +
      c1 * t (n - 1) k +
      c2 * t (n - 2) k +
      c3 * t (n - 3) k +
      c4 * t (n - 4) k = G (k + 1) - G k) :
    c0 * (∑ k ∈ Finset.range (n + 1), t n k) +
      c1 * (∑ k ∈ Finset.range (n - 1 + 1), t (n - 1) k) +
      c2 * (∑ k ∈ Finset.range (n - 2 + 1), t (n - 2) k) +
      c3 * (∑ k ∈ Finset.range (n - 3 + 1), t (n - 3) k) +
      c4 * (∑ k ∈ Finset.range (n - 4 + 1), t (n - 4) k) = 0 := by
  rw [← sum_extend_zero t hz (n - 1) n (by omega),
    ← sum_extend_zero t hz (n - 2) n (by omega),
    ← sum_extend_zero t hz (n - 3) n (by omega),
    ← sum_extend_zero t hz (n - 4) n (by omega)]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  calc
    (∑ k ∈ Finset.range (n + 1), (c0 * t n k +
      c1 * t (n - 1) k +
      c2 * t (n - 2) k +
      c3 * t (n - 3) k +
      c4 * t (n - 4) k)) =
        ∑ k ∈ Finset.range (n + 1), (G (k + 1) - G k) := by
      apply Finset.sum_congr rfl
      intro k hk
      exact hcert k (by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hk)
    _ = 0 := by rw [Finset.sum_range_sub, hG0, hG1, sub_self]

end OMA.T107587

namespace OMA.T107587

lemma recurrence4_generic (t : ℕ → ℕ → ℚ)
    (hz : ∀ m k : ℕ, m < k → t m k = 0)
    (hright : ∀ n k : ℕ, t n (k+1) = t n k*right n k)
    (hback : ∀ n k : ℕ, 1 ≤ n → t (n-1) k = t n k*back n k)
    (n : ℕ) (hn : 4 ≤ n) :
    p0 n*(∑ k ∈ Finset.range (n+1), t n k)+
      p1 n*(∑ k ∈ Finset.range (n-1+1), t (n-1) k)+
      p2 n*(∑ k ∈ Finset.range (n-2+1), t (n-2) k)+
      p3 n*(∑ k ∈ Finset.range (n-3+1), t (n-3) k)+
      p4 n*(∑ k ∈ Finset.range (n-4+1), t (n-4) k)=0 := by
  let G : ℕ → ℚ := fun k => t n k*R n k
  have hG0 : G 0=0 := by simp [G, R_zero]
  have hG1 : G (n+1)=0 := by simp [G, hz n (n+1) (by omega)]
  apply sum_certificate5 t hz n (p0 n) (p1 n) (p2 n) (p3 n) (p4 n) G hG0 hG1
  intro k hk
  have h1 := hback n k (by omega)
  have h2 := hback (n-1) k (by omega)
  have h3 := hback (n-2) k (by omega)
  have h4 := hback (n-3) k (by omega)
  rw [show n-1-1=n-2 by omega, Nat.cast_sub (show 1 ≤ n by omega), Nat.cast_one] at h2
  rw [show n-2-1=n-3 by omega, Nat.cast_sub (show 2 ≤ n by omega)] at h3
  rw [show n-3-1=n-4 by omega, Nat.cast_sub (show 3 ≤ n by omega)] at h4
  norm_num only [Nat.cast_ofNat] at h3 h4
  simp only [h4, h3, h2, h1]
  dsimp [G]
  rw [hright n k]
  push_cast
  have hc := certQ (n:ℚ) (k:ℚ) (by exact_mod_cast hn) (by positivity)
  linear_combination -(t n k)*hc

lemma recurrence4 (n : ℕ) (hn : 4 ≤ n) :
    p0 n*(OMA.S_oeis_a107587.a n:ℚ)+
      p1 n*(OMA.S_oeis_a107587.a (n-1):ℚ)+
      p2 n*(OMA.S_oeis_a107587.a (n-2):ℚ)+
      p3 n*(OMA.S_oeis_a107587.a (n-3):ℚ)+
      p4 n*(OMA.S_oeis_a107587.a (n-4):ℚ)=0 := by
  have h := recurrence4_generic F F_zero rightF backF n hn
  rw [← repr n, ← repr (n-1), ← repr (n-2), ← repr (n-3), ← repr (n-4)] at h
  exact h

end OMA.T107587

namespace OMA.T107587

lemma five_of_four (a : ℕ → ℚ)
    (hrec : ∀ n : ℕ, 4 ≤ n →
      (n:ℚ)*((n:ℚ)-2)*((n:ℚ)+2)*a n-
      (2*(n:ℚ)-1)*(2*(n:ℚ)^2-2*n-3)*a (n-1)+
      3*((n:ℚ)-1)*(2*(n:ℚ)^2-4*n+1)*a (n-2)-
      2*((n:ℚ)-1)*((n:ℚ)-2)*(2*(n:ℚ)-3)*a (n-3)-
      15*((n:ℚ)-1)*((n:ℚ)-2)*((n:ℚ)-3)*a (n-4)=0)
    (n : ℕ) (hn : 5 ≤ n) :
      (n:ℚ)*((n:ℚ)+2)*a n+(-5*(n:ℚ)^2-n+3)*a (n-1)+
      (10*(n:ℚ)^2-16*n+3)*a (n-2)+
      (-10*(n:ℚ)^2+34*n-27)*a (n-3)-
      (11*(n:ℚ)-5)*((n:ℚ)-3)*a (n-4)+
      15*((n:ℚ)-3)*((n:ℚ)-4)*a (n-5)=0 := by
  have h0 := hrec n (by omega)
  have h1 := hrec (n-1) (by omega)
  rw [show n-1-1=n-2 by omega, show n-1-2=n-3 by omega,
    show n-1-3=n-4 by omega, show n-1-4=n-5 by omega] at h1
  simp only [Nat.cast_sub (show 1 ≤ n by omega), Nat.cast_one] at h1
  have h : ((n:ℚ)-2)*
      ((n:ℚ)*((n:ℚ)+2)*a n+(-5*(n:ℚ)^2-n+3)*a (n-1)+
      (10*(n:ℚ)^2-16*n+3)*a (n-2)+
      (-10*(n:ℚ)^2+34*n-27)*a (n-3)-
      (11*(n:ℚ)-5)*((n:ℚ)-3)*a (n-4)+
      15*((n:ℚ)-3)*((n:ℚ)-4)*a (n-5))=0 := by
    linear_combination h0-h1
  have hnq : (5:ℚ) ≤ n := by exact_mod_cast hn
  exact (mul_eq_zero.mp h).resolve_left (by linarith)

end OMA.T107587

open OMA.T107587

theorem OMA.solution : type_of% @OMA.S_oeis_a107587.main := by
  have hrec : ∀ n : ℕ, 4 ≤ n →
      (n : ℚ)*((n : ℚ)-2)*((n : ℚ)+2)*(OMA.S_oeis_a107587.a n : ℚ)-
      (2*(n : ℚ)-1)*(2*(n : ℚ)^2-2*n-3)*(OMA.S_oeis_a107587.a (n-1) : ℚ)+
      3*((n : ℚ)-1)*(2*(n : ℚ)^2-4*n+1)*(OMA.S_oeis_a107587.a (n-2) : ℚ)-
      2*((n : ℚ)-1)*((n : ℚ)-2)*(2*(n : ℚ)-3)*(OMA.S_oeis_a107587.a (n-3) : ℚ)-
      15*((n : ℚ)-1)*((n : ℚ)-2)*((n : ℚ)-3)*(OMA.S_oeis_a107587.a (n-4) : ℚ)=0 := by
    intro n hn
    have h := recurrence4 n hn
    unfold p0 p1 p2 p3 p4 at h
    linear_combination h
  constructor
  · intro n hn
    exact_mod_cast five_of_four (fun n => (OMA.S_oeis_a107587.a n : ℚ)) hrec n hn
  · intro n hn
    exact_mod_cast hrec n hn
