import OMAStatements.S_oeis_a294172

-- Credit: @oh-meh
open Finset OMA.S_oeis_a294172

private def moment (n t : ℕ) : ℚ :=
  ∑ j ∈ range n, ((n:ℚ)-j)*(1+(((j+t)%n : ℕ):ℚ))

private theorem conv_eq (n k : ℕ) : (conv n k : ℚ) = moment n ((k+1)%n) := by
  unfold conv moment
  push_cast
  rw [show Icc 1 n = (range n).map ⟨(·+1), by intro a b h; exact Nat.add_right_cancel h⟩ by
    ext i
    simp only [mem_Icc, mem_map, mem_range]
    constructor
    · intro h; exact ⟨i-1, by omega, by change i-1+1=i; omega⟩
    · rintro ⟨j,hj,rfl⟩; change 1 ≤ j+1 ∧ j+1 ≤ n; omega, sum_map]
  apply sum_congr rfl
  intro j hj
  change (((n-(j+1):ℕ):ℚ)+1)*(1+(((j+1+k)%n:ℕ):ℚ)) = _
  rw [Nat.cast_sub (by simpa using hj : j+1≤n)]
  rw [show j+1+k=j+(k+1) by omega, Nat.add_mod_mod]
  push_cast
  ring

private theorem sum_weights (n : ℕ) :
    ∑ j ∈ range n, ((n:ℚ)-j) = n*(n+1)/2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ]
    push_cast
    simp_rw [show ∀ j : ℕ, (n:ℚ)+1-j = (n-j)+1 by intro; ring]
    rw [sum_add_distrib, ih]
    simp
    ring

private theorem base_moment (n : ℕ) :
    (∑ j ∈ range n, ((n:ℚ)-j)*(1+j)) = n*(n+1)*(n+2)/6 := by
  have tri (k : ℕ) : ∑ j ∈ range k, (1+(j:ℚ)) = k*(k+1)/2 := by
    induction k with
    | zero => simp
    | succ k ih => rw [sum_range_succ, ih]; push_cast; ring
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ]
    push_cast
    simp_rw [show ∀ j : ℕ, ((n:ℚ)+1-j)*(1+j) = (n-j)*(1+j)+(1+j) by intro; ring]
    rw [sum_add_distrib, ih, tri]
    ring

private theorem residue_step {i n t : ℕ} (hi : i<n) (ht : t+1<n) :
    ((((i+(t+1))%n:ℕ):ℚ)) = ((i+t)%n:ℕ)+1-(if i=n-1-t then (n:ℚ) else 0) := by
  by_cases h : i+t+1<n
  · rw [if_neg (by omega), Nat.mod_eq_of_lt (by omega),Nat.mod_eq_of_lt (by omega)]
    push_cast
    ring
  by_cases he : i+t+1=n
  · rw [if_pos (by omega), show i+(t+1)=n by omega, Nat.mod_self, Nat.mod_eq_of_lt (by omega)]
    exact_mod_cast (by omega : (0:ℤ) = (i:ℤ)+t+1-n)
  · rw [if_neg (by omega), Nat.mod_eq_sub_mod (by omega : n ≤ i+(t+1)),
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_sub_mod (by omega : n ≤ i+t), Nat.mod_eq_of_lt (by omega)]
    push_cast [Nat.cast_sub (by omega : n ≤ i+t), Nat.cast_sub (by omega : n ≤ i+(t+1))]
    ring

private theorem moment_step {n t : ℕ} (ht : t+1<n) :
    moment n (t+1) = moment n t + n*(n+1)/2 - (t+1)*n := by
  have hspecial : n-1-t < n := by omega
  unfold moment
  calc
    _ = ∑ j ∈ range n, ((((n:ℚ)-j)*(1+(((j+t)%n:ℕ):ℚ)) + (n-j)) -
        (if j=n-1-t then ((n:ℚ)-j)*n else 0)) := by
      apply sum_congr rfl
      intro j hj
      rw [residue_step (mem_range.mp hj) ht]
      split_ifs <;> ring
    _ = _ := by
      rw [sum_sub_distrib, sum_add_distrib, sum_weights]
      simp [Finset.sum_ite_eq', hspecial, Nat.cast_sub (by omega : t≤n-1),
        Nat.cast_sub (by omega : 1≤n)]
      left; ring

private theorem moment_formula {n t : ℕ} (ht : t<n) :
    moment n t = (n:ℚ)*(n+1)*(n+2)/6 + n*t*(n-t)/2 := by
  induction t with
  | zero =>
    simp only [moment, Nat.cast_zero, mul_zero, zero_mul, zero_div, add_zero]
    convert base_moment n using 1
    apply sum_congr rfl; intro j hj
    rw [Nat.mod_eq_of_lt (mem_range.mp hj)]
  | succ t ih =>
    rw [moment_step ht, ih (by omega)]
    push_cast
    ring

private def closed (n : ℕ) : ℚ :=
  n*(13+3*(-1)^n+24*n+14*(n:ℚ)^2)/48

private theorem at_midpoint {n : ℕ} (hn : 0<n) :
    moment n (n/2) = closed n := by
  rw [moment_formula (by omega : n/2 < n)]
  unfold closed
  rcases Nat.even_or_odd n with ⟨k,h⟩ | ⟨k,h⟩
  · rw [show n=2*k by omega, show 2*k/2=k by omega, pow_mul]
    push_cast
    norm_num
    ring
  · rw [show n=2*k+1 by omega, show (2*k+1)/2=k by omega, pow_succ, pow_mul]
    push_cast
    norm_num
    ring

private theorem below_midpoint {n t : ℕ} (ht : t<n) : moment n t ≤ moment n (n/2) := by
  rw [moment_formula ht, moment_formula (by omega : n/2<n)]
  suffices h : (t:ℚ)*(n-t) ≤ (n/2:ℕ)*((n:ℚ)-(n/2:ℕ)) by
    nlinarith [mul_le_mul_of_nonneg_left h (show (0:ℚ) ≤ n by positivity)]
  have split : n=n/2+(n+1)/2 := by omega
  have hsum : (n:ℚ)=(n/2:ℕ)+((n+1)/2:ℕ) := by exact_mod_cast split
  rcases le_or_gt t (n/2) with hlo | hhi
  · have h₁ : (t:ℚ) ≤ (n/2:ℕ) := by exact_mod_cast hlo
    have h₂ : (t:ℚ) ≤ ((n+1)/2:ℕ) := by exact_mod_cast (by omega : t≤(n+1)/2)
    rw [hsum]
    nlinarith [mul_nonneg (sub_nonneg.mpr h₁) (sub_nonneg.mpr h₂)]
  · have h₁ : (n/2:ℕ) ≤ (t:ℚ) := by exact_mod_cast hhi.le
    have h₂ : ((n+1)/2:ℕ) ≤ (t:ℚ) := by exact_mod_cast (by omega : (n+1)/2≤t)
    rw [hsum]
    nlinarith [mul_nonneg (sub_nonneg.mpr h₁) (sub_nonneg.mpr h₂)]

private theorem formula (n : ℕ) : (a n : ℚ) = closed n := by
  rcases n.eq_zero_or_pos with rfl | hn
  · simp [a,closed]
  have witness : ∃ k ∈ Icc 1 n, (k+1)%n=n/2 := by
    by_cases h : n/2<2
    · refine ⟨n, mem_Icc.mpr ⟨hn,le_rfl⟩,?_⟩
      have h₃ : n≤3 := by omega
      interval_cases n <;> decide
    · refine ⟨n/2-1, mem_Icc.mpr ⟨by omega,by omega⟩,?_⟩
      rw [show n/2-1+1 = n/2 by omega, Nat.mod_eq_of_lt (by omega)]
  obtain ⟨k,hk,he⟩ := witness
  have attain : (conv n k : ℚ)=closed n := by rw [conv_eq,he,at_midpoint hn]
  rw [← attain]
  exact_mod_cast (show a n = conv n k by
    apply le_antisymm _ (le_sup (f:=conv n) hk)
    apply Finset.sup_le
    intro i _
    exact_mod_cast (show (conv n i:ℚ) ≤ conv n k by rw [conv_eq, attain, ← at_midpoint hn]; exact below_midpoint (Nat.mod_lt _ hn)))

private theorem recurrence (k : ℕ) :
    (a (k+6):ℚ) = 2*a (k+5)+a (k+4)-4*a (k+3)+a (k+2)+2*a (k+1)-a k := by
  simp only [formula, closed, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one, pow_add]
  ring

private theorem limit_value : Filter.Tendsto (fun n : ℕ => (a n:ℝ)/(n:ℝ)^3)
    Filter.atTop (nhds (7/24)) := by
  have hlow : Filter.Tendsto (fun _ : ℕ => (7/24:ℝ)) Filter.atTop (nhds (7/24)) := tendsto_const_nhds
  have hhigh : Filter.Tendsto (fun n : ℕ => 7/24 + 1/(n:ℝ)) Filter.atTop (nhds (7/24)) := by
    simpa using hlow.add (tendsto_one_div_atTop_nhds_zero_nat (𝕜:=ℝ))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hhigh
  all_goals
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    have hpos : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
    have h1 : (1:ℝ)≤n := by exact_mod_cast hn
    have hformula : (a n:ℝ) = n*(13+3*(-1:ℝ)^n+24*n+14*(n:ℝ)^2)/48 := by
      simpa [closed] using congrArg (fun x : ℚ => (x:ℝ)) (formula n)
    rw [hformula]
    rcases neg_one_pow_eq_or ℝ n with h | h <;> rw [h] <;>
      field_simp <;> nlinarith [sq_nonneg ((n:ℝ)-1), sq_nonneg (n:ℝ)]

open PowerSeries in
private theorem generating :
    mk (fun n => (a n:ℚ)) * ((1-X)^4*(1+X)^2) = X*(1+3*X+2*X^2+X^3) := by
  let F := mk (fun n => (a n:ℚ))
  change F * _ = _
  rw [show F*((1-X)^4*(1+X)^2) = F - 2*(F*X) - F*X^2 + 4*(F*X^3) -
    F*X^4 - 2*(F*X^5) + F*X^6 by ring,
    show (X:ℚ⟦X⟧)*(1+3*X+2*X^2+X^3) = X+3*X^2+2*X^3+X^4 by ring]
  ext n
  simp only [map_add,map_sub,show (3:ℚ⟦X⟧)=1+1+1 by norm_num,
    show (4:ℚ⟦X⟧)=2+2 by norm_num, two_mul, add_mul, one_mul, coeff_X, coeff_X_pow,
    show F * X = F * X^1 by rw [pow_one], coeff_mul_X_pow', F, coeff_mk]
  by_cases hl : n<6
  · interval_cases n <;> norm_num [formula,closed, coeff_X, coeff_X_pow]
  · obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le' (show 6≤n by omega)
    have h := recurrence k
    simp [show 1 ≤ k+6 by omega, show 2 ≤ k+6 by omega, show 3 ≤ k+6 by omega,
      show 4 ≤ k+6 by omega, show 5 ≤ k+6 by omega, show 6 ≤ k+6 by omega] <;>
      simpa using (by linarith : (a (k+6):ℚ) - (a (k+5)+a (k+5)) - a (k+4) +
        (a (k+3)+a (k+3)+(a (k+3)+a (k+3))) - a (k+2) - (a (k+1)+a (k+1)) + a k=0)

theorem OMA.solution : type_of% @OMA.S_oeis_a294172.main := by
  refine ⟨fun n _ => formula n, limit_value, generating, ?_⟩
  intro n hn
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le' (show 6≤n by omega)
  simpa using (show (a (k+6):ℤ) = 2*a (k+5)+a (k+4)-4*a (k+3)+a (k+2)+2*a (k+1)-a k by
    exact_mod_cast recurrence k)
