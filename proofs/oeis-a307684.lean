import OMAStatements.S_oeis_a307684

-- Original proof: @AlfredMelson. Quasipolynomial simplification: @rgoldman73-dev.

section
open OMA.S_oeis_a307684

private def prismRow (n k : ℕ) : ℕ :=
  ∑ i ∈ Finset.Icc k ((n-k)/2), i*k*(n-i-k)

private def prismBlock (n k u : ℚ) : ℚ :=
  k * ((n-k)*(u*(u+1) - (k-1)*k)/2 -
    (u*(u+1)*(2*u+1) - (k-1)*k*(2*k-1))/6)

private def prismPair (v b j : ℚ) : ℚ :=
  prismBlock (2*v+b) (2*j+1) (v-j-1+b) + prismBlock (2*v+b) (2*j+2) (v-j-1)

private def prismPairs (v b j : ℚ) : ℚ :=
  let f := prismPair v b
  j*f 0 + j*(j-1)/2*(f 1-f 0) + j*(j-1)*(j-2)/6*(f 2-2*f 1+f 0) +
    j*(j-1)*(j-2)*(j-3)/24*(f 3-3*f 2+3*f 1-f 0) +
    j*(j-1)*(j-2)*(j-3)*(j-4)/120*(f 4-4*f 3+6*f 2-4*f 1+f 0)

-- Weighted orbit count: all ordered triples, transposition-fixed triples, and
-- equal triples give the three summands of this quasipolynomial.
private def prismPoly (s : ℕ) (t : ℚ) : ℚ :=
  let n := 6*t + s
  let m := 3*t + (s/2 : ℕ)
  n*(n^2-1)*(n^2-4)/720 +
    (if s%2=0 then m^2*(m^2-1) else m*(m+1)*(m^2+m+1))/12 +
    if s%3=0 then n^3/81 else 0

end

section
open Finset

private lemma prism_inner_sum (N : ℚ) (k u : ℕ) (hu : k ≤ u) :
    (∑ i ∈ Icc k u, (i : ℚ)*k*(N-i-k)) = prismBlock N k u := by
  induction u, hu using Nat.le_induction with
  | base =>
    simp only [Icc_self, sum_singleton, prismBlock]
    ring
  | succ u hu ih =>
    rw [sum_Icc_succ_top (by omega) _, ih]
    simp only [Nat.cast_add, Nat.cast_one, prismBlock]
    ring

private theorem prism_inner (n k : ℕ) (hk : 1 ≤ k) (hn : 3*k ≤ n) :
    (prismRow n k : ℚ) = prismBlock n k ((n-k)/2 : ℕ) := by
  unfold prismRow
  rw [Nat.cast_sum]
  refine (sum_congr rfl (fun i hi => ?_)).trans (prism_inner_sum n k _ (by omega))
  have hu := (mem_Icc.mp hi).2
  rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub (by omega : k ≤ n-i), Nat.cast_sub (by omega : i ≤ n)]
end

section
private lemma prism_pairs_succ (v b j : ℚ) :
    prismPairs v b (j+1) = prismPairs v b j + prismPair v b j := by
  unfold prismPairs prismPair prismBlock
  ring

private theorem prism_prefix
    (inner : ∀ n k : ℕ, 1 ≤ k → 3*k ≤ n →
      (prismRow n k : ℚ) = prismBlock n k ((n-k)/2 : ℕ))
    (n j : ℕ) (hj : 6*j ≤ n) :
    (∑ k ∈ Finset.Icc 1 (2*j), (prismRow n k : ℚ)) =
      prismPairs (n/2 : ℕ) (n%2 : ℕ) j := by
  induction j with
  | zero => simp [prismPairs]
  | succ j ih =>
    rw [show 2*(j+1) = 2*j+1+1 by omega,
      Finset.sum_Icc_succ_top (by omega : 1 ≤ 2*j+1+1),
      Finset.sum_Icc_succ_top (by omega : 1 ≤ 2*j+1),
      ih (by omega), inner n (2*j+1) (by omega) (by omega),
      inner n (2*j+1+1) (by omega) (by omega),
      Nat.cast_succ j, prism_pairs_succ, prismPair, add_assoc]
    congr 1
    have hnq : (n : ℚ) = 2 * ((n/2 : ℕ) : ℚ) + (n%2 : ℕ) := by
      exact_mod_cast (show n = 2*(n/2)+n%2 by omega)
    have ho : (((n-(2*j+1))/2 : ℕ) : ℚ) + j + 1 = ((n/2 : ℕ) : ℚ) + (n%2 : ℕ) := by
      exact_mod_cast (show (n-(2*j+1))/2 + j + 1 = n/2 + n%2 by omega)
    have he : (((n-(2*j+1+1))/2 : ℕ) : ℚ) + j + 1 = (n/2 : ℕ) := by
      exact_mod_cast (show (n-(2*j+1+1))/2 + j + 1 = n/2 by omega)
    rw [hnq, show (((n-(2*j+1))/2 : ℕ) : ℚ) = ((n/2 : ℕ) : ℚ) - j - 1 + (n%2 : ℕ) by linarith,
      show (((n-(2*j+1+1))/2 : ℕ) : ℚ) = ((n/2 : ℕ) : ℚ) - j - 1 by linarith]
    push_cast
    ring_nf
end

section
open Finset OMA.S_oeis_a307684

private theorem prism_formula
    (inner : ∀ n k : ℕ, 1 ≤ k → 3*k ≤ n → (prismRow n k : ℚ) = prismBlock n k ((n-k)/2 : ℕ))
    (prefixSum : ∀ n j : ℕ, 6*j ≤ n → (∑ k ∈ Finset.Icc 1 (2*j), (prismRow n k : ℚ)) =
      prismPairs (n/2 : ℕ) (n%2 : ℕ) j) (n : ℕ) :
    (a n : ℚ) = prismPoly (n%6) (n/6 : ℕ) := by
  let t := n/6
  have lt6 := Nat.mod_lt n (by decide : 0 < 6)
  have splitN : n = 6*t + n%6 := by dsimp [t]; omega
  have hpairs := prefixSum n t (by omega)
  have hsum : (a n : ℚ) = ∑ k ∈ Icc 1 (n/3), (prismRow n k : ℚ) := by simp [a, prismRow]
  rw [hsum]
  change _ = prismPoly (n%6) t
  generalize hr : n%6 = s at *
  interval_cases s
  all_goals
    first
    | rw [show n/3=2*t by omega, hpairs]
    | rw [show n/3=2*t+1 by omega, sum_Icc_succ_top (by omega), hpairs,
          inner n (2*t+1) (by omega) (by omega)]
  all_goals
    first | rw [show n/2=3*t by omega] | rw [show n/2=3*t+1 by omega] | rw [show n/2=3*t+2 by omega]
    first | rw [show n%2=0 by omega] | rw [show n%2=1 by omega]
    try first | rw [show (n-(2*t+1))/2=2*t+1 by omega] | rw [show (n-(2*t+1))/2=2*t+2 by omega]
    try rw [splitN]
    push_cast
    norm_num [prismPoly, prismPairs, prismPair, prismBlock]
    ring
end

section
open OMA.S_oeis_a307684 PowerSeries

private def prismRec (w : ℕ → ℚ) : ℚ :=
  w 0 + w 1 - 2*w 2 - 6*w 3 - 3*w 4 + 9*w 5 + 14*w 6 + 2*w 7 - 16*w 8 - 16*w 9 + 2*w 10 + 14*w 11 + 9*w 12
  - 3*w 13 - 6*w 14 - 2*w 15 + w 16 + w 17

set_option maxHeartbeats 2400000 in
private lemma prism_poly_recurrence (s : ℕ) (hs : s < 6) (q : ℚ) :
    prismRec (fun r => prismPoly ((s+18-r)%6) (q + (((s+18-r)/6 : ℕ) : ℚ))) = 0 := by
  interval_cases s <;> norm_num [prismRec, prismPoly] <;> ring

private theorem prism_conclusion (formula : ∀ n : ℕ, (a n : ℚ) = prismPoly (n%6) (n/6 : ℕ)) :
    type_of% @OMA.S_oeis_a307684.main := by
  have hrec (n : ℕ) (hn : 17 < n) : prismRec (fun r => (a (n-r) : ℚ)) = 0 := by
    let q := (n-18)/6
    let s := (n-18)%6
    have hn' : n = 6*q + s + 18 := by dsimp [q,s]; omega
    have hs : s < 6 := Nat.mod_lt _ (by decide)
    have term (r : ℕ) (hr : r ≤ 17) :
        (a (n-r) : ℚ) = prismPoly ((s+18-r)%6) ((q : ℚ) + (((s+18-r)/6 : ℕ) : ℚ)) := by
      rw [formula, show (n-r)%6 = (s+18-r)%6 by omega,
        show (n-r)/6 = q + (s+18-r)/6 by omega, Nat.cast_add]
    have h := prism_poly_recurrence s hs q
    simpa (disch := decide) only [prismRec, term] using h
  constructor
  · let A := mk (fun n => (a n : ℚ))
    have lhs : A * ((1-X)^6 * (1+X)^3 * (1+X+X^2)^4) =
        A + (A*X^1) - C 2*(A*X^2) - C 6*(A*X^3) - C 3*(A*X^4) + C 9*(A*X^5) + C 14*(A*X^6) + C 2*(A*X^7) - C
        16*(A*X^8) - C 16*(A*X^9) + C 2*(A*X^10) + C 14*(A*X^11) + C 9*(A*X^12) - C 3*(A*X^13) - C 6*(A*X^14) -
        C 2*(A*X^15) + (A*X^16) + (A*X^17) := by
      norm_num [map_ofNat]
      ring
    have rhs : X^3 * (1 + 3*X + 7*X^2 + 15*X^3 + 23*X^4 + 21*X^5 + 18*X^6
        + 14*X^7 + 6*X^8) =
        X^3 + C (3 : ℚ)*X^4 + C (7 : ℚ)*X^5 + C (15 : ℚ)*X^6 + C (23 : ℚ)*X^7 + C (21 : ℚ)*X^8 + C (18 : ℚ)*X^9
        + C (14 : ℚ)*X^10 + C (6 : ℚ)*X^11 := by
      norm_num [map_ofNat]
      ring
    change A * ((1-X)^6 * (1+X)^3 * (1+X+X^2)^4) = _
    rw [lhs, rhs]
    ext n
    simp only [map_sub, map_add, coeff_C_mul, coeff_mul_X_pow', A, coeff_mk, coeff_C, coeff_X_pow]
    by_cases large : 17 < n
    · simp (disch := omega) only [if_neg, if_pos]
      have h := hrec n large
      simp only [prismRec, Nat.sub_zero] at h
      linarith
    · interval_cases n <;> norm_num [formula, prismPoly]
  · intro n hn
    have h := hrec n hn
    simp only [prismRec, Nat.sub_zero] at h
    apply Int.cast_injective (α := ℚ)
    push_cast
    linarith
end

theorem OMA.solution : type_of% @OMA.S_oeis_a307684.main :=
  prism_conclusion (prism_formula prism_inner (prism_prefix prism_inner))

