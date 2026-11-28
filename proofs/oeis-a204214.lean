import OMAStatements.S_oeis_a204214

-- Credit: @Aryan-Poonacha
namespace BarkerPaths
open OMA.S_oeis_a204214 Finset

-- Fix the endpoint neighbors av and d, then the third entry b. The next
-- entry runs from b-n (truncated at zero) through min (n+d) (n+b).
private def width (n d b : ℕ) := min (n+d) (n+b) + 1 - (b-n)

private abbrev Codes (n : ℕ) :=
  (a : Fin (n+1)) × (d : Fin (n+1)) × (b : Fin (n+a.val+1)) × Fin (width n d.val b.val)

private lemma edges (n : ℕ) (x : Fin 6 → ℕ) : x ∈ arrays n ↔
    x 0 = 0 ∧ x 5 = 0 ∧ x 1 ≤ n ∧ x 4 ≤ n ∧
    x 2 ≤ n + x 1 ∧ x 3 ≤ n + x 4 ∧ x 2 ≤ n + x 3 ∧ x 3 ≤ n + x 2 := by
  constructor
  · rintro ⟨h0,h5,h⟩
    have h01 := abs_le.mp (h 0 1 (by decide))
    have h12 := abs_le.mp (h 1 2 (by decide))
    have h23 := abs_le.mp (h 2 3 (by decide))
    have h34 := abs_le.mp (h 3 4 (by decide))
    have h45 := abs_le.mp (h 4 5 (by decide))
    exact ⟨h0,h5,by omega,by omega,by omega,by omega,by omega,by omega⟩
  · rintro ⟨h0,h5,ha,hd,hb,hc,hbc,hcb⟩
    refine ⟨h0,h5,?_⟩
    intro i j e
    fin_cases i <;> fin_cases j <;> norm_num at e
    · change |(x 0 : ℤ) - x 1| ≤ n
      exact abs_le.mpr ⟨by omega,by omega⟩
    · change |(x 1 : ℤ) - x 2| ≤ n
      exact abs_le.mpr ⟨by omega,by omega⟩
    · change |(x 2 : ℤ) - x 3| ≤ n
      exact abs_le.mpr ⟨by omega,by omega⟩
    · change |(x 3 : ℤ) - x 4| ≤ n
      exact abs_le.mpr ⟨by omega,by omega⟩
    · change |(x 4 : ℤ) - x 5| ≤ n
      exact abs_le.mpr ⟨by omega,by omega⟩

private def decode {n : ℕ} (v : Codes n) : arrays n := by
  obtain ⟨a,d,b,c⟩ := v
  let x : Fin 6 → ℕ := ![0,a.val,b.val,c.val+(b.val-n),d.val,0]
  refine ⟨x,(edges n x).mpr ?_⟩
  have hc := c.isLt
  have hb := b.isLt
  have ha := a.isLt
  have hd := d.isLt
  simp only [width] at hc
  change 0 = 0 ∧ 0 = 0 ∧ _ ≤ _ ∧ _ ≤ _ ∧ _ ≤ _ ∧ _ ≤ _ ∧ _ ≤ _ ∧ _ ≤ _
  dsimp [x]
  omega

private lemma count (n : ℕ) : a n =
    ∑ av ∈ range (n+1), ∑ d ∈ range (n+1), ∑ b ∈ range (n+av+1), width n d b := by
  have hj : Function.Bijective (@decode n) := by
    constructor
    · rintro ⟨⟨av,ha⟩,⟨d,hd⟩,⟨b,hb⟩,⟨c,hc⟩⟩ ⟨⟨av',ha'⟩,⟨d',hd'⟩,⟨b',hb'⟩,⟨c',hc'⟩⟩ eq
      have h1 := congrArg (fun z : arrays n => z.val 1) eq
      have h2 := congrArg (fun z : arrays n => z.val 2) eq
      have h3 := congrArg (fun z : arrays n => z.val 3) eq
      have h4 := congrArg (fun z : arrays n => z.val 4) eq
      change av = av' at h1
      change b = b' at h2
      change c+(b-n) = c'+(b'-n) at h3
      change d = d' at h4
      subst av'; subst b'; subst d'
      have : c = c' := by omega
      subst c'
      rfl
    · rintro ⟨x,hx⟩
      obtain ⟨h0,h5,ha,hd,hb,hc,hbc,hcb⟩ := (edges n x).mp hx
      refine ⟨⟨⟨x 1,by omega⟩,⟨x 4,by omega⟩,⟨x 2,by change x 2 < n + x 1 + 1; omega⟩,
        ⟨x 3 - (x 2-n),by change x 3 - (x 2-n) < min (n+x 4) (n+x 2) + 1 - (x 2-n); omega⟩⟩, ?_⟩
      apply Subtype.ext
      funext i
      fin_cases i <;> dsimp [decode] <;> omega
  change Nat.card (arrays n) = _
  rw [← Nat.card_congr (Equiv.ofBijective _ hj), Nat.card_eq_fintype_card]
  simp only [Codes, Fintype.card_sigma, Fintype.card_fin]
  simp_rw [← Fin.sum_univ_eq_sum_range]

private lemma descending_sum (d M : ℕ) (hd : d ≤ M) :
    (∑ i ∈ range (M+1), ((d-i : ℕ) : ℚ)) = d*(d+1)/2 := by
  induction d generalizing M with
  | zero => simp
  | succ d ih =>
    obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show M ≠ 0 by omega)
    rw [sum_range_succ']
    simp only [Nat.succ_sub_succ_eq_sub, Nat.sub_zero, Nat.cast_succ]
    rw [ih k (by omega)]
    ring

private lemma ascending_sum (n a : ℕ) :
    (∑ i ∈ range (n+a+1), ((i-n : ℕ) : ℚ)) = a*(a+1)/2 := by
  induction a with
  | zero =>
    simp only [Nat.add_zero, Nat.cast_zero, zero_mul, zero_div]
    apply sum_eq_zero
    intro i hi
    have := mem_range.mp hi
    simp [Nat.sub_eq_zero_of_le (show i ≤ n by omega)]
  | succ a ih =>
    rw [show n+(a+1)+1=(n+a+1)+1 by omega, sum_range_succ, ih]
    rw [show n+a+1-n=a+1 by omega]
    push_cast
    ring

-- The two corners missing from the rectangle have triangular sizes.
private lemma middle_count (n av d : ℕ) (ha : av ≤ n) (hd : d ≤ n) :
    (∑ b ∈ range (n+av+1), (width n d b : ℚ)) =
      (n+av+1 : ℚ)*(n+d+1) - (d*(d+1) + av*(av+1))/2 := by
  have w (b : ℕ) (hb : b ∈ range (n+av+1)) : (width n d b : ℚ) =
      (n+d+1 : ℚ) - ((d-b : ℕ) : ℚ) - ((b-n : ℕ) : ℚ) := by
    have hb' := mem_range.mp hb
    have e : width n d b + (d-b) + (b-n) = n+d+1 := by unfold width; omega
    have ec := congrArg (fun u : ℕ => (u : ℚ)) e
    push_cast at ec
    linarith
  rw [sum_congr rfl w]
  simp only [sum_sub_distrib, sum_const, card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one,
    descending_sum d (n+av) (by omega), ascending_sum]
  ring

private lemma sum_quad (n : ℕ) (A B C : ℚ) :
    (∑ i ∈ range (n+1), (A + B*i + C*(i:ℚ)^2)) =
    (n+1 : ℚ)*A + n*(n+1)/2*B + n*(n+1)*(2*n+1)/6*C := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_range_succ, ih]; push_cast; ring

-- This is Hardin's empirical quartic, obtained from the rectangle count.
private theorem formula (n : ℕ) : (a n : ℚ) = (n+1 : ℚ)^2*(23*n^2+28*n+12)/12 := by
  rw [count]
  push_cast
  have row (av : ℕ) (ha : av ∈ range (n+1)) :
      (∑ d ∈ range (n+1), ∑ b ∈ range (n+av+1), (width n d b : ℚ)) =
      (n+1 : ℚ)*((n+av+1)*(n+1)-av*(av+1)/2) +
      n*(n+1)/2*(n+av+1-1/2) + n*(n+1)*(2*n+1)/6*(-1/2) := by
    rw [← sum_quad n ((n+av+1 : ℚ)*(n+1)-av*(av+1)/2) (n+av+1-1/2 : ℚ) (-1/2)]
    apply sum_congr rfl
    intro d hd
    rw [middle_count n av d (by have := mem_range.mp ha; omega) (by have := mem_range.mp hd; omega)]
    ring
  rw [sum_congr rfl row]
  let A : ℚ := (n+1 : ℚ)^3 + n*(n+1)/2*(n+1-1/2) - n*(n+1)*(2*n+1)/12
  let B : ℚ := (n+1 : ℚ)*(n+1-1/2) + n*(n+1)/2
  let C : ℚ := -(n+1 : ℚ)/2
  calc
    _ = ∑ i ∈ range (n+1), (A+B*i+C*(i:ℚ)^2) := by apply sum_congr rfl; intro i hi; dsimp [A,B,C]; ring
    _ = _ := by rw [sum_quad]; dsimp [A,B,C]; ring

private lemma recurrence (n : ℕ) (h : 5 < n) :
    (a n : ℚ) = 5*a (n-1) - 10*a (n-2) + 10*a (n-3) - 5*a (n-4) + a (n-5) := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le (show 6 ≤ n by omega)
  have sub (j : ℕ) (hj : j ≤ 5) : 6+k-j = k+(6-j) := by omega
  simp only [sub 1 (by decide),sub 2 (by decide),sub 3 (by decide),sub 4 (by decide),sub 5 (by decide),formula]
  push_cast
  ring

open PowerSeries
private noncomputable def seq : PowerSeries ℚ := mk fun n => if n=0 then 0 else (a n : ℚ)

private lemma shifted (n k : ℕ) : coeff n (seq * X^k) =
    if k ≤ n then (if n-k=0 then 0 else (a (n-k) : ℚ)) else 0 := by
  simp only [coeff_mul_X_pow',seq,coeff_mk]

private lemma generating :
    seq * (1-X)^5 = X * (21+15*X+14*X^2-5*X^3+X^4) := by
  have lhs : seq * (1-X)^5 = seq - C 5*(seq * X^1) + C 10*(seq * X^2) -
      C 10*(seq * X^3) + C 5*(seq * X^4) - seq * X^5 := by simp only [map_ofNat]; ring
  have rhs : X * (21+15*X+14*X^2-5*X^3+X^4 : PowerSeries ℚ) =
      C 21*X^1 + C 15*X^2 + C 14*X^3 - C 5*X^4 + X^5 := by simp only [map_ofNat]; ring
  rw [lhs,rhs]
  apply PowerSeries.ext
  intro n
  simp only [map_add,map_sub,coeff_C_mul,shifted,coeff_X_pow]
  simp only [seq,coeff_mk]
  by_cases h : n ≤ 5
  · interval_cases n <;> norm_num [formula]
  · have relation := recurrence n (by omega)
    simp only [if_pos (show 1≤n by omega),if_pos (show 2≤n by omega),if_pos (show 3≤n by omega),
      if_pos (show 4≤n by omega),if_pos (show 5≤n by omega),
      if_neg (show n≠0 by omega),if_neg (show n-1≠0 by omega),if_neg (show n-2≠0 by omega),
      if_neg (show n-3≠0 by omega),if_neg (show n-4≠0 by omega),if_neg (show n-5≠0 by omega),
      if_neg (show n≠1 by omega),if_neg (show n≠2 by omega),if_neg (show n≠3 by omega),
      if_neg (show n≠4 by omega),if_neg (show n≠5 by omega)]
    linarith

end BarkerPaths

theorem OMA.solution : type_of% @OMA.S_oeis_a204214.main := by
  refine ⟨BarkerPaths.generating,?_⟩
  intro n hn
  exact_mod_cast BarkerPaths.recurrence n hn
