import OMAStatements.S_oeis_a049473
import Mathlib.Tactic

open OMA.S_oeis_a049473 Filter Topology Finset

namespace ZetaTailCrossings

private noncomputable def lo (j : ℕ) : ℝ := 1/(2*(j:ℝ)*(j+1)+1)
private noncomputable def hi (j : ℕ) : ℝ := 1/(2*(j:ℝ)*(j+1))
private noncomputable def cubeTerm (m j : ℕ) : ℝ := 1/((m:ℝ)+j+1)^3

private lemma lowerStep (m : ℕ) : lo m - lo (m+1) < cubeTerm m 0 := by
  unfold lo cubeTerm
  push_cast
  simp only [add_zero]
  have h₁ : 0 < 2*(m:ℝ)*(m+1)+1 := by positivity
  have h₂ : 0 < 2*((m:ℝ)+1)*(m+1+1)+1 := by positivity
  have h₃ : 0 < ((m:ℝ)+1)^3 := by positivity
  field_simp
  <;> nlinarith

private lemma upperStep (m : ℕ) (hm : 0 < m) : cubeTerm m 0 < hi m - hi (m+1) := by
  have hmp : (0:ℝ) < m := by exact_mod_cast hm
  unfold hi cubeTerm
  push_cast
  simp only [add_zero]
  have h₁ : 0 < 2*(m:ℝ)*(m+1) := by positivity
  have h₂ : 0 < 2*((m:ℝ)+1)*(m+1+1) := by positivity
  have h₃ : 0 < ((m:ℝ)+1)^3 := by positivity
  field_simp
  <;> nlinarith [sq_nonneg (m:ℝ)]

private lemma sumTerm (m : ℕ) : Summable (cubeTerm m) := by
  have h := (summable_nat_add_iff (f:=fun k : ℕ => 1/(k:ℝ)^3) (m+1)).mpr
    (Real.summable_one_div_nat_pow.mpr (by decide : 1<3))
  change Summable (fun j : ℕ => 1/((m:ℝ)+j+1)^3)
  simpa [add_assoc,add_comm,add_left_comm] using h

private lemma splitTail (m : ℕ) : tail m = cubeTerm m 0 + tail (m+1) := by
  simpa [tail,cubeTerm,add_assoc,add_comm,add_left_comm] using (sumTerm m).tsum_eq_zero_add

private lemma vanish (m : ℕ) :
    Tendsto (fun N : ℕ => lo (m+N)) atTop (𝓝 0) ∧
    Tendsto (fun N : ℕ => hi (m+N)) atTop (𝓝 0) := by
  have inv : Tendsto (fun k : ℕ => 1/(k:ℝ)) atTop (𝓝 0) := tendsto_one_div_atTop_nhds_zero_nat
  have h (N : ℕ) (hN : 0<N) : hi (m+N) ≤ 1/(N:ℝ) := by
    have hP : (0:ℝ)<N := by exact_mod_cast hN
    apply one_div_le_one_div_of_le hP
    push_cast
    nlinarith only [Nat.cast_nonneg (α:=ℝ) m,hP.le,sq_nonneg ((m:ℝ)+N)]
  have hl (j : ℕ) (hj : 0<j) : lo j ≤ hi j := by
    have p : (0:ℝ)<j := by exact_mod_cast hj
    unfold lo hi
    exact one_div_le_one_div_of_le (by positivity) (by linarith)
  constructor
  · apply squeeze_zero' (Eventually.of_forall (fun N => by unfold lo; positivity)) _ inv
    filter_upwards [eventually_gt_atTop 0] with N hN
    exact (hl _ (by omega)).trans (h N hN)
  · apply squeeze_zero' (Eventually.of_forall (fun N => by unfold hi; positivity)) _ inv
    filter_upwards [eventually_gt_atTop 0] with N hN
    exact h N hN

private lemma weakLower (m : ℕ) : lo m ≤ tail m := by
  have part (N : ℕ) : lo m-lo (m+N) ≤ ∑ j ∈ range N, cubeTerm m j := by
    induction N with
    | zero => simp
    | succ N ih =>
      rw [sum_range_succ]
      have st := (lowerStep (m+N)).le
      have eqv : cubeTerm (m+N) 0 = cubeTerm m N := by simp [cubeTerm]
      rw [eqv] at st
      change lo m - lo (m+N+1) ≤ _
      linarith
  have limit := (tendsto_const_nhds (x:=lo m)).sub (vanish m).1
  simpa [tail,cubeTerm] using le_of_tendsto_of_tendsto' limit (sumTerm m).hasSum.tendsto_sum_nat part

private lemma weakUpper (m : ℕ) (hm : 0 < m) : tail m ≤ hi m := by
  have part (N : ℕ) : (∑ j ∈ range N, cubeTerm m j) ≤ hi m-hi (m+N) := by
    induction N with
    | zero => simp
    | succ N ih =>
      rw [sum_range_succ]
      have st := (upperStep (m+N) (by omega)).le
      have eqv : cubeTerm (m+N) 0 = cubeTerm m N := by simp [cubeTerm]
      rw [eqv] at st
      change _ ≤ hi m-hi (m+N+1)
      linarith
  have limit := (tendsto_const_nhds (x:=hi m)).sub (vanish m).2
  simpa [tail,cubeTerm] using le_of_tendsto_of_tendsto' (sumTerm m).hasSum.tendsto_sum_nat limit part

private lemma lower (m : ℕ) : lo m < tail m := by
  rw [splitTail]
  linarith [lowerStep m,weakLower (m+1)]

private lemma upper (m : ℕ) (hm : 0 < m) : tail m < hi m := by
  rw [splitTail]
  linarith [upperStep m hm,weakUpper (m+1) (by omega)]

private noncomputable def rounded (s : ℝ) (n : ℕ) : ℕ := ⌊(n:ℝ)/s+1/2⌋₊

private lemma roundedSpec {s : ℝ} (hs : 0<s) (n : ℕ) :
    (rounded s n:ℝ) ≤ (n:ℝ)/s+1/2 ∧ (n:ℝ)/s+1/2 < (rounded s n:ℝ)+1 :=
  ⟨Nat.floor_le (by positivity),Nat.lt_floor_add_one _⟩

private lemma noCut {s : ℝ} (h : Irrational s) (k n : ℕ) : ((k:ℝ)+1/2)*s ≠ n := by
  intro e
  apply h.ne_rational (2*(n:ℤ)) (2*(k:ℤ)+1)
  push_cast
  apply (eq_div_iff (by positivity : 2*(k:ℝ)+1≠0)).mpr
  linarith only [e]

private lemma increments {s : ℝ} (hs : 1<s) (n : ℕ) :
    rounded s n ≤ rounded s (n+1) ∧ rounded s (n+1) ≤ rounded s n+1 := by
  have pos : 0<s := by linarith
  have A := roundedSpec pos n
  have B := roundedSpec pos (n+1)
  push_cast at B
  have step : 1/s ≤ (1:ℝ) := (div_le_iff₀ pos).mpr (by linarith)
  constructor
  · apply Nat.le_floor
    push_cast
    rw [add_div]
    linarith [A.1,show (0:ℝ) ≤ 1/s by positivity]
  · have C : (rounded s (n+1):ℝ) < (rounded s n:ℝ)+2 := by
      rw [add_div] at B
      linarith [A.2,B.1]
    have D : rounded s (n+1)<rounded s n+2 := by exact_mod_cast C
    omega

private lemma jumpIff {s : ℝ} (hs : 1<s) (irr : Irrational s) (n : ℕ) :
    rounded s (n+1) = rounded s n+1 ↔ ∃ k : ℕ, beatty s k = n := by
  have pos : 0<s := by linarith
  have A := roundedSpec pos n
  have B := roundedSpec pos (n+1)
  push_cast at B
  constructor
  · intro jump
    refine ⟨rounded s n, (Nat.floor_eq_iff (by positivity)).mpr ⟨?_,?_⟩⟩
    · exact ((div_lt_iff₀ pos).mp (show (n:ℝ)/s < (rounded s n:ℝ)+1/2 by linarith [A.2])).le
    · rw [jump] at B
      push_cast at B
      have b := (le_div_iff₀ pos).mp (show (rounded s n:ℝ)+1/2 ≤ ((n:ℝ)+1)/s by linarith [B.1])
      exact b.lt_of_ne (by simpa using noCut irr (rounded s n) (n+1))
  · rintro ⟨k,hk⟩
    have C := (Nat.floor_eq_iff (by positivity : 0≤((k:ℝ)+1/2)*s)).mp hk
    have a := (div_lt_iff₀ pos).mpr (C.1.lt_of_ne (noCut irr k n).symm)
    have b := (lt_div_iff₀ pos).mpr C.2
    have al : (rounded s n:ℝ) < (k:ℝ)+1 := by linarith [A.1]
    have hi : k+1 ≤ rounded s (n+1) := by
      apply Nat.le_floor
      push_cast
      linarith
    have an : rounded s n < k+1 := by exact_mod_cast al
    have step := increments hs n
    omega

private lemma complement (n : ℕ) :
    rounded (Real.sqrt 2) n + rounded (2+Real.sqrt 2) n = n := by
  let p := Real.sqrt 2
  let q := 2+p
  have hp : 0<p := by dsimp [p]; positivity
  have hq : 0<q := by dsimp [q]; linarith
  have irr : Irrational p := irrational_sqrt_two
  have relation : (n:ℝ)/p+1/2 + ((n:ℝ)/q+1/2) = (n:ℝ)+1 := by
    have psq : p^2=2 := Real.sq_sqrt (by norm_num)
    dsimp [q]
    field_simp
    nlinarith only [congrArg (fun x : ℝ => n*x) psq]
  have A := roundedSpec hp n
  have B := roundedSpec hq n
  have strict : (rounded p n:ℝ) < (n:ℝ)/p+1/2 := by
    apply A.1.lt_of_ne
    generalize rounded p n = a
    cases a with
    | zero => simp; positivity
    | succ k =>
      push_cast
      intro e
      apply noCut irr k n
      exact (eq_div_iff hp.ne').mp (show (k:ℝ)+1/2=(n:ℝ)/p by linarith)
  have h₁ : (rounded p n:ℝ)+(rounded q n:ℝ) < (n:ℝ)+1 := by linarith [B.1]
  have h₂ : (n:ℝ)+1 < (rounded p n:ℝ)+(rounded q n:ℝ)+2 := by linarith [A.2,B.2]
  have n₁ : rounded p n + rounded q n < n+1 := by exact_mod_cast h₁
  have n₂ : n+1 < rounded p n + rounded q n + 2 := by exact_mod_cast h₂
  change rounded p n + rounded q n = n
  omega

private lemma differences (n : ℕ) :
    (nearest (n+1) = nearest n ∨ nearest (n+1) = nearest n+1) ∧
      (nearest (n+1) = nearest n ↔ ∃ k : ℕ, beatty (2+Real.sqrt 2) k = n) ∧
      (nearest (n+1) = nearest n+1 ↔ ∃ k : ℕ, beatty (Real.sqrt 2) k = n) := by
  let p := Real.sqrt 2
  let q := 2+p
  have h₀ : p^2=2 := Real.sq_sqrt (by norm_num)
  have hp : 1<p := by nlinarith [Real.sqrt_nonneg (2:ℝ)]
  have hq : 1<q := by dsimp [q]; linarith
  have iq : Irrational q := by simpa [q,p] using irrational_sqrt_two.ratCast_add (2:ℚ)
  have S := increments hp n
  have C : rounded p n + rounded q n = n := complement n
  have D : rounded p (n+1) + rounded q (n+1) = n+1 := complement (n+1)
  change (_ ∨ _) ∧ (rounded p (n+1)=rounded p n ↔ _) ∧ (rounded p (n+1)=rounded p n+1 ↔ _)
  refine ⟨?_,?_,jumpIff hp irrational_sqrt_two n⟩
  · change rounded p (n+1)=rounded p n ∨ rounded p (n+1)=rounded p n+1
    omega
  · rw [←jumpIff hq iq]
    omega

private lemma crossing (n : ℕ) (hn : 0<n) :
    tail (nearest n) < 1/(n:ℝ)^2 ∧ 1/(n:ℝ)^2 < tail (nearest n-1) := by
  let p := Real.sqrt 2
  have pos : 0<p := by dsimp [p]; positivity
  have p2 : p^2=2 := Real.sq_sqrt (by norm_num)
  have hnR : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hnear : 1 ≤ nearest n := by
    apply Nat.le_floor
    have pLe : p ≤ 2 := by nlinarith
    have half : (1:ℝ)/2 ≤ n/p := (le_div_iff₀ pos).mpr (by linarith)
    simp only [Nat.cast_one]
    change (1:ℝ) ≤ n/p+1/2
    linarith
  obtain ⟨t,ht⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hnear)
  have A : ((nearest n:ℕ):ℝ) ≤ (n:ℝ)/p+1/2 ∧ (n:ℝ)/p+1/2 < (nearest n:ℝ)+1 :=
    roundedSpec pos n
  rw [ht] at A
  push_cast at A
  have left := (le_div_iff₀ pos).mp (show (t:ℝ)+1/2 ≤ n/p by linarith [A.1])
  have right := (div_lt_iff₀ pos).mp (show (n:ℝ)/p < t+3/2 by linarith [A.2])
  have L := pow_le_pow_left₀ (by positivity : 0 ≤ ((t:ℝ)+1/2)*p) left 2
  have U := pow_lt_pow_left₀ right (by positivity : 0≤(n:ℝ)) (by decide : (2:ℕ)≠0)
  rw [mul_pow,p2] at L U
  have loNat : 2*(2*t*(t+1))+1 ≤ 2*n^2 := by
    exact_mod_cast (show 2*(2*(t:ℝ)*(t+1))+1 ≤ 2*(n:ℝ)^2 by nlinarith only [L])
  have hiNat : 2*n^2 < 2*(2*(t+1)*(t+2))+1 := by
    exact_mod_cast (show 2*(n:ℝ)^2 < 2*(2*((t:ℝ)+1)*(t+2))+1 by nlinarith only [U])
  have lowN : 2*t*(t+1)+1 ≤ n^2 := by omega
  have highN : n^2 ≤ 2*(t+1)*(t+2) := by omega
  rw [ht]
  constructor
  · apply (upper (t+1) (by omega)).trans_le
    apply one_div_le_one_div_of_le (by positivity : 0 < (n:ℝ)^2)
    push_cast
    exact_mod_cast highN
  · apply lt_of_le_of_lt _ (lower t)
    apply one_div_le_one_div_of_le (by positivity : 0 < 2*(t:ℝ)*(t+1)+1)
    exact_mod_cast lowN

end ZetaTailCrossings

theorem OMA.solution : type_of% @OMA.S_oeis_a049473.main :=
  ⟨ZetaTailCrossings.crossing,ZetaTailCrossings.differences⟩
