import OMAStatements.S_oeis_a133306

open Finset

namespace NarayanaFinite

private def b (p : ℚ) (n k : ℕ) : ℚ :=
  (n.choose k : ℚ) * (n.choose (k+1) : ℚ) * p^k * (p+1)^(n-k)

private def B (p : ℚ) (n : ℕ) : ℚ := ∑ k ∈ range n, b p n k

private def A (p : ℚ) (n : ℕ) : ℚ := if n = 0 then 1 else B p n / n

private theorem b_zero (p : ℚ) {n k : ℕ} (h : n ≤ k) : b p n k = 0 := by
  simp [b, Nat.choose_eq_zero_of_lt (Nat.lt_succ_of_le h)]

private theorem choose_lower (n k : ℕ) :
    ((n : ℚ)+1)*(n.choose k : ℚ) = ((n : ℚ)+1-k)*((n+1).choose k : ℚ) := by
  cases k with
  | zero => simp
  | succ k =>
    have h := congrArg (fun t : ℕ => (t:ℚ)) (Nat.add_one_mul_choose_eq n k)
    have h' := congrArg (fun t : ℕ => (t:ℚ)) (Nat.choose_succ_succ n k)
    push_cast at h h' ⊢
    linear_combination ((n : ℚ)+1)*(-h') - h

private def q1 (n k : ℕ) : ℚ := ((n : ℚ)-k)*((n : ℚ)-k-1)

private def q2 (n k : ℕ) : ℚ := q1 n k*q1 (n-1) k

private theorem b_lower (p : ℚ) (n k : ℕ) :
    ((n:ℚ)+1)^2*(p+1)*b p n k = q1 (n+1) k*b p (n+1) k := by
  by_cases hk : k ≤ n
  · have h0 := choose_lower n k
    have h1 := choose_lower n (k+1)
    push_cast at h1
    unfold b q1
    rw [show n+1-k=(n-k)+1 by omega, pow_succ]
    push_cast
    calc
      _ = (((n:ℚ)+1)*(n.choose k:ℚ))*(((n:ℚ)+1)*(n.choose (k+1):ℚ))*p^k*((p+1)^(n-k)*(p+1)) := by ring
      _ = _ := by rw [h0,h1]; ring
  · rw [b_zero p (by omega : n ≤ k), b_zero p (by omega : n+1 ≤ k), mul_zero, mul_zero]

private theorem b_forward (p : ℚ) (n k : ℕ) :
    (p+1)*((k:ℚ)+1)*((k:ℚ)+2)*b p n (k+1) = p*q1 n k*b p n k := by
  by_cases hk : k < n
  · have h0 := congrArg (fun t:ℕ => (t:ℚ)) (Nat.choose_succ_right_eq n k)
    have h1 := congrArg (fun t:ℕ => (t:ℚ)) (Nat.choose_succ_right_eq n (k+1))
    push_cast [Nat.cast_sub (by omega : k ≤ n), Nat.cast_sub (by omega : k+1 ≤ n)] at h0 h1
    unfold b q1
    rw [show n-k=(n-(k+1))+1 by omega, pow_succ p k, pow_succ (p+1)]
    calc
      _ = (((k:ℚ)+1)*(n.choose (k+1):ℚ))*(((k:ℚ)+1+1)*(n.choose (k+1+1):ℚ)) * p^k*p*(p+1)^(n-(k+1))*(p+1) := by ring
      _ = _ := by rw [mul_comm ((k:ℚ)+1), h0, mul_comm ((k:ℚ)+1+1), h1]; ring
  · rw [b_zero p (by omega : n ≤ k+1), b_zero p (by omega : n ≤ k), mul_zero, mul_zero]

private theorem extendB (p : ℚ) {m n : ℕ} (h : m ≤ n) :
    (∑ k ∈ range n, b p m k) = B p m := by
  symm
  exact sum_subset (range_mono h) fun k _ hk => b_zero p (by simpa using hk)

private theorem lowerSum (p : ℚ) (n : ℕ) :
    (∑ k ∈ range (n+1), q1 (n+1) k*b p (n+1) k) = ((n:ℚ)+1)^2*(p+1)*B p n := by
  simp_rw [← b_lower]
  rw [← Finset.mul_sum, extendB p (Nat.le_succ n)]

private theorem lowerSum2 (p : ℚ) (n : ℕ) :
    (∑ k ∈ range (n+2), q2 (n+2) k*b p (n+2) k) = ((n:ℚ)+2)^2*((n:ℚ)+1)^2*(p+1)^2*B p n := by
  have h (k : ℕ) : q2 (n+2) k*b p (n+2) k = (((n:ℚ)+2)^2*((n:ℚ)+1)^2*(p+1)^2)*b p n k := by
    have h0 := b_lower p (n+1) k
    have h1 := b_lower p n k
    unfold q2
    rw [show n+2-1=n+1 by omega]
    calc
      _ = q1 (n+1) k*(q1 (n+2) k*b p (n+2) k) := by ring
      _ = ((n:ℚ)+2)^2*(p+1)*(q1 (n+1) k*b p (n+1) k) := by rw [← h0]; push_cast; ring
      _ = _ := by rw [← h1]; ring
  simp_rw [h]
  rw [← Finset.mul_sum, extendB p (by omega : n ≤ n+2)]

private def poly (p N K : ℚ) : ℚ :=
  -K^2+(2*N*p+4*N-2*p-3)*K-(N-1)*(3*N*p+4*N-p-1)

private def witness (p : ℚ) (n k : ℕ) : ℚ :=
  (p+1)*(k:ℚ)*((k:ℚ)+1)*poly p n k*b p n k

private def weight (p : ℚ) (n k : ℕ) : ℚ :=
  ((n:ℚ)+1)*(n:ℚ)*((n:ℚ)-1)^2*(p+1)^2 +
  (2*p+1)*(1-2*(n:ℚ))*((n:ℚ)-1)*(p+1)*q1 n k + q2 n k

private theorem difference (p : ℚ) (n k : ℕ) (hn : 1 ≤ n) :
    witness p n (k+1)-witness p n k = weight p n k*b p n k := by
  have h := congrArg (fun z : ℚ => poly p n ((k:ℚ)+1)*z) (b_forward p n k)
  unfold witness weight q2 q1 poly
  unfold q1 poly at h
  push_cast [Nat.cast_sub hn] at h ⊢
  linear_combination h

private theorem telescope (p : ℚ) (n : ℕ) (hn : 1 ≤ n) :
    (∑ k ∈ range n, weight p n k*b p n k) = 0 := by
  simp_rw [← difference p n _ hn]
  rw [sum_range_sub]
  simp [witness, b_zero p (le_refl n)]

private theorem check (p : ℚ) (hp : 0 ≤ p) (n : ℕ) (hn : 2 ≤ n) :
    ((n : ℚ)+1)*A p n+(2*p+1)*(-2*(n:ℚ)+1)*A p (n-1)+((n:ℚ)-2)*A p (n-2)=0 := by
  obtain ⟨m,rfl⟩ : ∃ m, n=m+2 := ⟨n-2, by omega⟩
  rw [show m+2-1=m+1 by omega, show m+2-2=m by omega]
  by_cases hm : m=0
  · subst m
    norm_num [A,B,b,Finset.sum_range_succ,Nat.choose] <;> ring
  · let N : ℚ := (m:ℚ)+2
    let u : ℚ := p+1
    have hS := telescope p (m+2) (by omega)
    have hc (k : ℕ) : weight p (m+2) k*b p (m+2) k =
        (N+1)*N*(N-1)^2*u^2*b p (m+2) k +
        ((2*p+1)*(1-2*N)*(N-1)*u)*(q1 (m+2) k*b p (m+2) k) +
        q2 (m+2) k*b p (m+2) k := by
      dsimp [weight,N,u]
      push_cast
      ring
    simp_rw [hc] at hS
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      lowerSum p (m+1), lowerSum2 p m] at hS
    change _*B p (m+2)+_+_=0 at hS
    have hN : N ≠ 0 := by dsimp [N]; positivity
    have hN1 : N-1 ≠ 0 := by dsimp [N]; linarith [(Nat.cast_nonneg m : 0 ≤ (m:ℚ))]
    have hu : u ≠ 0 := by dsimp [u]; positivity
    have hNZ : N^2*(N-1)^2*u^2 ≠ 0 :=
      mul_ne_zero (mul_ne_zero (pow_ne_zero _ hN) (pow_ne_zero _ hN1)) (pow_ne_zero _ hu)
    have hm0 : (m:ℚ) ≠ 0 := by exact_mod_cast hm
    have hN2 : N-2 ≠ 0 := by
      have he : N-2=(m:ℚ) := by dsimp [N]; ring
      rw [he]
      exact hm0
    have hS' :
        (N+1)*N*(N-1)^2*u^2*B p (m+2) +
        (2*p+1)*(1-2*N)*(N-1)*N^2*u^2*B p (m+1) +
        N^2*(N-1)^2*u^2*B p m = 0 := by
      dsimp [N,u] at hS ⊢
      push_cast at hS
      linear_combination hS
    have hrewrite : N^2*(N-1)^2*u^2 *
          ((N+1)*(B p (m+2)/N) + (2*p+1)*(-2*N+1)*(B p (m+1)/(N-1)) +
            (N-2)*(B p m/(N-2))) =
        (N+1)*N*(N-1)^2*u^2*B p (m+2) +
        (2*p+1)*(1-2*N)*(N-1)*N^2*u^2*B p (m+1) +
        N^2*(N-1)^2*u^2*B p m := by
      field_simp [hN,hN1,hN2] <;> ring
    apply mul_left_cancel₀ hNZ
    rw [mul_zero]
    simp only [A, if_neg hm, if_neg (by omega : m+1 ≠ 0), if_neg (by omega : m+2 ≠ 0)]
    have hc0 : (m:ℚ)=N-2 := by dsimp [N]; ring
    have hc1 : ((m+1:ℕ):ℚ)=N-1 := by dsimp [N]; push_cast; ring
    have hc2 : ((m+2:ℕ):ℚ)=N := by simp [N]
    simp only [hc2, hc1, hc0]
    exact hrewrite.trans hS'

end NarayanaFinite

theorem OMA.solution : type_of% @OMA.S_oeis_a133306.main := by
  intro n hn
  have h := NarayanaFinite.check (5 : ℚ) (by norm_num) n hn
  norm_num [NarayanaFinite.A, NarayanaFinite.B, NarayanaFinite.b, OMA.S_oeis_a133306.a] at h ⊢
  exact h
