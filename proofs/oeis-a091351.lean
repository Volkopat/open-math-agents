import OMAStatements.S_oeis_a091351

/-!
Let u₀=X and uᵢ₊₁=uᵢ(1+uᵢ). A matrix entry at offset n in power p
and column q-1 is the nth coefficient, in the basis defined below, of
the product of (1+uᵢ₊ⱼ) over a p by q rectangle. Transposition preserves
this product. The coefficient rule is derived directly from multiplication
of the lower triangular matrices.
-/

namespace HannaRectangle

open Polynomial Finset OMA.S_oeis_a091351

private noncomputable def u : ℕ → ℕ[X]
  | 0 => X
  | n+1 => u n * (1 + u n)

private noncomputable def v (n : ℕ) : ℕ[X] := 1 + u n
private noncomputable def strip (p j : ℕ) : ℕ[X] := ∏ i ∈ range p, v (j+i)
private noncomputable def rect (p q : ℕ) : ℕ[X] := ∏ j ∈ range q, strip p j

private theorem u_comp (a b : ℕ) : (u a).comp (u b) = u (a+b) := by
  induction a with
  | zero => simp [u]
  | succ a ih => simp only [u, mul_comp, add_comp, one_comp, ih, Nat.succ_add]

private theorem v_comp (a b : ℕ) : (v a).comp (u b) = v (a+b) := by
  simp [v, add_comp, u_comp]

private theorem strip_comp (p j b : ℕ) : (strip p j).comp (u b) = strip p (j+b) := by
  simp only [strip, Polynomial.prod_comp, v_comp]
  apply prod_congr rfl
  intro i _
  rw [show j+i+b=j+b+i by omega]

private theorem u_factor (p : ℕ) : u p = X * strip p 0 := by
  induction p with
  | zero => simp [u, strip]
  | succ p ih =>
    change u p * v p = _
    rw [show strip (p+1) 0 = strip p 0 * v p by simp [strip, prod_range_succ]]
    rw [← mul_assoc, ← ih]

private theorem strip_shift (p : ℕ) :
    (1+X) * (strip p 0).comp (u 1) = strip p 0 * v p := by
  rw [strip_comp]
  calc
    _ = strip (p+1) 0 := by
      unfold strip
      rw [prod_range_succ']
      simp [v, u, Nat.add_comm, mul_comm]
    _ = strip p 0 * v p := by simp [strip, prod_range_succ]

private theorem rect_symmetric (p q : ℕ) : rect p q = rect q p := by
  unfold rect strip
  rw [prod_comm]
  simp only [Nat.add_comm]

private theorem rect_col (p q : ℕ) : rect p (q+1) = strip p 0 * (rect p q).comp (u 1) := by
  unfold rect
  rw [prod_range_succ']
  simp only [Polynomial.prod_comp, strip_comp, mul_comm]

private theorem rect_row (p q : ℕ) :
    rect (p+1) q = rect p q * (rect 1 q).comp (u p) := by
  unfold rect strip
  simp only [prod_range_succ, range_one, prod_singleton, Nat.add_zero, prod_mul_distrib,
    Polynomial.prod_comp, v_comp]

private noncomputable def drop (P : ℕ[X]) : ℕ[X] := (1+X) * P.divX.comp (u 1)

private noncomputable def entry : ℕ → ℕ[X] → ℕ
  | 0, P => P.coeff 0
  | n+1, P => entry n (drop P)

private theorem entry_add (n : ℕ) (P Q : ℕ[X]) : entry n (P+Q) = entry n P + entry n Q := by
  induction n generalizing P Q with
  | zero => simp [entry]
  | succ n ih => simp [entry, drop, divX_add, add_comp, mul_add, ih]

private theorem entry_scale (n d : ℕ) (P : ℕ[X]) : entry n (C d * P) = d * entry n P := by
  induction n generalizing P with
  | zero => simp [entry]
  | succ n ih =>
    change entry n (drop (C d*P)) = _
    rw [show drop (C d*P) = C d * drop P by simp only [drop, divX_C_mul, mul_comp, C_comp]; ring]
    exact ih _

private theorem drop_X (P : ℕ[X]) : drop (X*P) = (1+X) * P.comp (u 1) := by
  have h : (X*P).divX = P := by ext k; simp [coeff_divX]
  rw [drop, h]

private theorem decompose (p q : ℕ) (Q : ℕ[X]) :
    rect p q * Q.comp (u p) = C (Q.coeff 0) * rect p q +
      X * (rect p q * strip p 0 * Q.divX.comp (u p)) := by
  calc
    _ = rect p q * ((X * Q.divX + C (Q.coeff 0)).comp (u p)) := by rw [X_mul_divX_add]
    _ = _ := by
      simp only [add_comp, mul_comp, X_comp, C_comp]
      rw [u_factor p]
      ring

private theorem remainder (p q : ℕ) (Q : ℕ[X]) :
    drop (X * (rect p q * strip p 0 * Q.divX.comp (u p))) = rect p (q+1) * (drop Q).comp (u p) := by
  calc
    _ = ((1+X)*(strip p 0).comp (u 1)) * (rect p q).comp (u 1) *
        Q.divX.comp (u (p+1)) := by
      simp only [drop_X, mul_comp, comp_assoc, u_comp]
      ring
    _ = _ := by
      rw [strip_shift, rect_col]
      simp only [drop, mul_comp, add_comp, one_comp, X_comp, comp_assoc, u_comp, v,
        show 1+p=p+1 by omega]
      ring

private theorem convolution (p q n : ℕ) (Q : ℕ[X]) :
    entry n (rect p q * Q.comp (u p)) =
      ∑ i ∈ range (n+1), entry i Q * entry (n-i) (rect p (q+i)) := by
  induction n generalizing q Q with
  | zero =>
    rw [decompose]
    simp [entry, mul_coeff_zero]
  | succ n ih =>
    rw [decompose, entry_add, entry_scale]
    change Q.coeff 0 * entry (n+1) (rect p q) +
      entry n (drop (X * (rect p q * strip p 0 * Q.divX.comp (u p)))) = _
    rw [remainder, ih]
    rw [sum_range_succ' (fun i => entry i Q * entry (n+1-i) (rect p (q+i))) (n+1)]
    simp only [entry, Nat.add_zero, Nat.sub_zero, Nat.succ_sub_succ_eq_sub]
    rw [add_comm]
    congr 1
    apply sum_congr rfl
    intro i _
    rw [show q+1+i=q+(i+1) by omega]

private theorem entry_zero (n : ℕ) : entry n 0 = 0 := by
  induction n with
  | zero => simp [entry]
  | succ n ih => simpa [entry, drop] using ih

private theorem entry_one (n : ℕ) : entry n 1 = if n=0 then 1 else 0 := by
  cases n <;> simp [entry, drop, entry_zero]

private theorem first_column (n : ℕ) : entry n (rect 1 1) = 1 := by
  have v₀ : rect 1 1 = 1+X := by simp [rect, strip, v, u]
  have d : (1+X : ℕ[X]).divX = 1 := by
    ext k
    cases k <;> simp [coeff_divX, coeff_one, coeff_X]
  rw [v₀]
  induction n with
  | zero => simp [entry]
  | succ n ih => simpa [entry, drop, d] using ih

private noncomputable def triangle (r c : ℕ) : ℕ :=
  if c ≤ r then entry (r-c) (rect 1 (c+1)) else 0

private theorem triangle_at (c n : ℕ) : triangle (c+n) c = entry n (rect 1 (c+1)) := by
  simp [triangle]

private theorem triangle_zero (j : ℕ) : triangle j 0 = 1 := by simp [triangle, first_column]

private theorem power_entry (p c n : ℕ) :
    matPow triangle p (c+n) c = entry n (rect p (c+1)) := by
  induction p generalizing c n with
  | zero =>
    have e : rect 0 (c+1) = 1 := by simp [rect, strip]
    rw [e, entry_one, matPow]
    simp
  | succ p ih =>
    rw [matPow, show c+n+1 = c+(n+1) by omega, sum_range_add]
    have zero : (∑ j ∈ range c, matPow triangle p (c+n) j * triangle j c) = 0 := by
      apply sum_eq_zero
      intro j hj
      simp [triangle, Nat.not_le.mpr (mem_range.mp hj)]
    rw [zero, zero_add, rect_row, convolution]
    apply sum_congr rfl
    intro i hi
    have bound : i ≤ n := by simpa using mem_range.mp hi
    have e : matPow triangle p (c+n) (c+i) = entry (n-i) (rect p ((c+i)+1)) := by
      rw [show c+n = (c+i)+(n-i) by omega]
      exact ih _ _
    rw [e, triangle_at, show c+i+1=c+1+i by omega, Nat.mul_comm]

private theorem triangle_rule : IsA091351 triangle := by
  refine ⟨fun n k h => by simp [triangle, Nat.not_le.mpr h], ?_⟩
  intro r c h
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [triangle_at, rect_symmetric]
  have v := power_entry (c+1) 0 n
  simpa [matPow, triangle_zero] using v.symm

private theorem agree_power {T U : ℕ → ℕ → ℕ} (r : ℕ)
    (h : ∀ i ≤ r, ∀ c, T i c = U i c) (p c : ℕ) :
    matPow T p r c = matPow U p r c := by
  induction p generalizing c with
  | zero => rfl
  | succ p ih =>
    simp only [matPow]
    apply sum_congr rfl
    intro j hj
    rw [ih, h j (by simpa using mem_range.mp hj)]

private theorem unique_triangle (T : ℕ → ℕ → ℕ) (hT : IsA091351 T) : T = triangle := by
  funext r
  induction r using Nat.strong_induction_on with
  | h r ih =>
    funext c
    by_cases hc : c ≤ r
    · rw [hT.2 r c hc, triangle_rule.2 r c hc]
      cases c with
      | zero => rfl
      | succ c =>
        apply sum_congr rfl
        intro j _
        apply agree_power
        intro i hi k
        exact congrFun (ih i (by omega)) k
    · rw [hT.1 r c (by omega), triangle_rule.1 r c (by omega)]

end HannaRectangle

open HannaRectangle OMA.S_oeis_a091351

theorem OMA.solution : type_of% @OMA.S_oeis_a091351.main := by
  intro T hT p q n hp hq
  rw [unique_triangle T hT]
  obtain ⟨p, rfl⟩ : ∃ d, p = d+1 := ⟨p-1, by omega⟩
  obtain ⟨q, rfl⟩ : ∃ d, q = d+1 := ⟨q-1, by omega⟩
  rw [show n+(q+1)-1=q+n by omega, show n+(p+1)-1=p+n by omega]
  change matPow triangle (p+1) (q+n) q = matPow triangle (q+1) (p+n) p
  rw [power_entry, power_entry, rect_symmetric]
