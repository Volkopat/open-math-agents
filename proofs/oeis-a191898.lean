import OMAStatements.S_oeis_a191898

/-! Each entry depends only on the gcd of its two indices. The diagonal
is the Dirichlet inverse of Euler's totient and has a nonzero product formula. -/

namespace A191898Proof

open OMA.S_oeis_a191898 Finset ArithmeticFunction

private def diagonal : ArithmeticFunction ℤ :=
  prodPrimeFactors (fun p => 1 - (p : ℤ))

private def phi : ArithmeticFunction ℤ :=
  ⟨fun n => n.totient, by simp⟩

private theorem diagonal_one : diagonal 1 = 1 := by
  simp [diagonal, prodPrimeFactors_apply]

private theorem diagonal_pow {p e : ℕ} (hp : p.Prime) (he : e ≠ 0) :
    diagonal (p^e) = 1 - (p : ℤ) := by
  rw [diagonal, prodPrimeFactors_apply (pow_ne_zero _ hp.ne_zero),
    Nat.primeFactors_prime_pow he hp, prod_singleton]

private theorem diagonal_ne_zero {n : ℕ} (hn : 0 < n) : diagonal n ≠ 0 := by
  rw [diagonal, prodPrimeFactors_apply hn.ne']
  apply prod_ne_zero_iff.mpr
  intro p hp
  have hl := (Nat.prime_of_mem_primeFactors hp).two_le
  omega

private theorem phi_apply (n : ℕ) : phi n = (n.totient : ℤ) := rfl

private theorem convolution : phi * diagonal = 1 := by
  have hphi : phi.IsMultiplicative := by
    refine ⟨by simp [phi_apply], ?_⟩
    intro m n hmn
    simp [phi_apply, Nat.totient_mul hmn]
  have hdiag : diagonal.IsMultiplicative := IsMultiplicative.prodPrimeFactors _
  apply (IsMultiplicative.eq_iff_eq_on_prime_powers _ (hphi.mul hdiag) _
    isMultiplicative_one).mpr
  intro p e hp
  cases e with
  | zero => simp [phi_apply, diagonal_one]
  | succ e =>
    have hpnot : p^(e+1) ≠ 1 := by
      have h := Nat.le_self_pow (by omega : e+1 ≠ 0) p
      have hp2 := hp.two_le
      omega
    have hsum : (∑ i ∈ range (e+1), phi (p^i)) = ((p^e : ℕ) : ℤ) := by
      have h := Nat.sum_totient (p^e)
      rw [Nat.sum_divisors_prime_pow hp] at h
      simp_rw [phi_apply]
      exact_mod_cast h
    rw [one_apply_ne hpnot, mul_apply,
      Nat.sum_divisorsAntidiagonal (fun x y => phi x * diagonal y),
      Nat.sum_divisors_prime_pow hp, sum_range_succ]
    have hlast : phi (p^(e+1)) * diagonal (p^(e+1)/p^(e+1)) =
        ((p^e : ℕ) : ℤ) * ((p : ℤ)-1) := by
      rw [Nat.div_self (pow_pos hp.pos _), diagonal_one, mul_one, phi_apply,
        Nat.totient_prime_pow_succ hp, Nat.cast_mul, Nat.cast_sub hp.one_lt.le, Nat.cast_one]
    rw [hlast, ← hsum, sum_mul, ← sum_add_distrib]
    apply sum_eq_zero
    intro i hi
    have hi' := mem_range.mp hi
    rw [Nat.pow_div (by omega : i ≤ e+1) hp.pos,
      diagonal_pow hp (by omega : e+1-i ≠ 0)]
    ring

private theorem baseSum (k : ℕ) (hk : 1 < k) :
    (∑ j ∈ range k, diagonal (k.gcd j)) = 0 := by
  classical
  have hm : ∀ j ∈ range k, k.gcd j ∈ k.divisors :=
    fun j _ => Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_left k j, by omega⟩
  rw [← sum_fiberwise_of_maps_to hm (fun j => diagonal (k.gcd j))]
  have h := congrArg (fun f : ArithmeticFunction ℤ => f k) convolution
  change (phi * diagonal) k = (1 : ArithmeticFunction ℤ) k at h
  rw [one_apply_ne (by omega : k ≠ 1), mul_apply,
    Nat.sum_divisorsAntidiagonal' (fun x y => phi x * diagonal y)] at h
  rw [← h]
  apply sum_congr rfl
  intro d hd
  have hconst : (∑ j ∈ (range k).filter (fun j => k.gcd j = d), diagonal (k.gcd j)) =
      ∑ j ∈ (range k).filter (fun j => k.gcd j = d), diagonal d := by
    apply sum_congr rfl
    intro j hj
    rw [(mem_filter.mp hj).2]
  rw [hconst, sum_const, nsmul_eq_mul, ← Nat.totient_div_of_dvd (Nat.dvd_of_mem_divisors hd)]
  rfl

private theorem slidingSum (k : ℕ) (hk : 1 < k) (s : ℕ) :
    (∑ j ∈ range k, diagonal (k.gcd (s+j))) = 0 := by
  induction s with
  | zero => simpa using baseSum k hk
  | succ s ih =>
    let l := k-1
    have hl : l+1 = k := by dsimp [l]; omega
    have hb : (∑ j ∈ range (l+1), diagonal (k.gcd (s+j))) = 0 := by
      simpa only [hl] using ih
    rw [sum_range_succ'] at hb
    rw [← hl] at ⊢
    rw [sum_range_succ]
    have hlast : k.gcd (s+(1+l)) = k.gcd s := by
      rw [show s+(1+l) = s+k by omega, Nat.gcd_add_self_right]
    simpa only [hl, Nat.succ_eq_add_one, hlast, Nat.add_zero, Nat.add_left_comm,
      Nat.add_assoc, Nat.add_comm] using hb

private theorem diagonalRec (k m : ℕ) (hk : 1 < k) (hm : k ≤ m+1) :
    diagonal (k.gcd (m+1)) = -(∑ j ∈ range (k-1), diagonal (k.gcd (m-j))) := by
  let s := m+2-k
  let l := k-1
  have hl : l+1 = k := by dsimp [l]; omega
  have hwindow : (∑ j ∈ range (l+1), diagonal (k.gcd (s+j))) = 0 := by
    simpa only [hl] using slidingSum k hk s
  rw [sum_range_succ, show s+l=m+1 by dsimp [s,l]; omega] at hwindow
  have hprefix : (∑ j ∈ range l, diagonal (k.gcd (s+j))) =
      ∑ j ∈ range l, diagonal (k.gcd (m-j)) := by
    rw [← sum_range_reflect (fun j => diagonal (k.gcd (s+j))) l]
    apply sum_congr rfl
    intro j hj
    have hj' := mem_range.mp hj
    rw [show s+(l-1-j) = m-j by dsimp [s,l] at *; omega]
  rw [hprefix] at hwindow
  linarith

private theorem auxLength (k : ℕ) (init : ℕ → ℤ) : ∀ m,
    (tColAux k init m).length = m+1
  | 0 => rfl
  | m+1 => by simp [tColAux, auxLength k init m, Nat.add_assoc]

private theorem auxGet (k : ℕ) (init : ℕ → ℤ) (m i : ℕ) (hi : i ≤ m) :
    (tColAux k init m).getD i 0 = (tColAux k init i).getD i 0 := by
  induction m with
  | zero => have hh : i = 0 := by omega
            subst i
            rfl
  | succ m ih =>
    by_cases he : i = m+1
    · subst i
      rfl
    · rw [tColAux, List.getD_append]
      · exact ih (by omega)
      · rw [auxLength]
        omega

private theorem auxCorrect (k : ℕ) (hk : 1 < k) (init : ℕ → ℤ)
    (hinit : ∀ i, 0 < i → i < k → init i = diagonal (k.gcd i)) :
    ∀ m, 0 < m → (tColAux k init m).getD m 0 = diagonal (k.gcd m) := by
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro hm
    cases m with
    | zero => omega
    | succ m =>
      rw [tColAux, List.getD_append_right]
      · rw [auxLength, Nat.sub_self]
        change (if m+1 < k then init (m+1) else
          -(∑ j ∈ range (k-1), (tColAux k init m).getD (m-j) 0)) = _
        split_ifs with ht
        · exact hinit _ hm ht
        · rw [diagonalRec k m hk (by omega)]
          congr 1
          apply sum_congr rfl
          intro j hj
          have hj' := mem_range.mp hj
          rw [auxGet k init m (m-j) (by omega)]
          exact ih (m-j) (by omega) (by omega)
      · rw [auxLength]

private theorem colsLength : ∀ k, (tCols k).length = k+1
  | 0 => rfl
  | 1 => rfl
  | k+2 => by simp [tCols, colsLength (k+1), Nat.add_assoc]

private theorem colsGet (k i : ℕ) (hi : i ≤ k) :
    (tCols k).getD i (fun _ => 0) = (tCols i).getD i (fun _ => 0) := by
  induction k with
  | zero => have hh : i = 0 := by omega
            subst i
            rfl
  | succ k ih =>
    by_cases he : i = k+1
    · subst i
      rfl
    · cases k with
      | zero => have hh : i = 0 := by omega
                subst i
                rfl
      | succ k =>
        rw [show k+1+1 = k+2 by omega, tCols, List.getD_append]
        · exact ih (by omega)
        · rw [colsLength]
          omega

private theorem columnCorrect (k : ℕ) : ∀ n, 0 < k → 0 < n →
    ((tCols k).getD k (fun _ => 0)) n = diagonal (k.gcd n) := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro n hk hn
    rcases k with _ | _ | k
    · omega
    · simp [tCols, diagonal_one]
    · rw [show k+1+1 = k+2 by omega, tCols, List.getD_append_right]
      · rw [colsLength, show k+2-(k+1+1)=0 by omega]
        change (tColAux (k+2) (fun j => ((tCols (k+1)).getD j (fun _ => 0)) (k+2)) n).getD n 0 = _
        apply auxCorrect _ (by omega) _ _ n hn
        intro i hi hi'
        rw [colsGet (k+1) i (by omega), Nat.gcd_comm (k+2) i]
        exact ih i hi' (k+2) hi (by omega)
      · rw [colsLength]

theorem gcdFormula (n k : ℕ) (hn : 0 < n) (hk : 0 < k) :
    T n k = diagonal (n.gcd k) := by
  unfold T
  split
  · rw [Nat.gcd_comm]
    exact columnCorrect k n hk hn
  · exact columnCorrect n k hn hk

theorem nonzero (n k : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k) : T n k ≠ 0 := by
  rw [gcdFormula n k (by omega) (by omega)]
  exact diagonal_ne_zero (Nat.gcd_pos_of_pos_left k (by omega))

end A191898Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a191898.main :=
  A191898Proof.nonzero
