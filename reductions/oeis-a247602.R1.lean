import OMAStatements.S_oeis_a247602

/-!
Zhi-Wei Sun, *A new theorem on the prime-counting function*, Conjecture 4.2,
https://arxiv.org/abs/1409.5685. Also OEIS A247602, https://oeis.org/A247602.

A totient estimate from the ordered prime divisors, together with the two explicit
Chebyshev bounds in Mathlib, restricts the partners of every positive index. The
smaller possible partner is logarithmically bounded. A larger partner lies between
an exponential lower bound and an explicit exponential upper bound. Thus the need
for the larger search can be decided with only logarithmically many equality tests.
-/

namespace A247602
open Finset

/-- If k different odd integers at least 3 precede p, their spacing gives p ≥ 2k+3. -/
private theorem odd_rank (S : Finset ℕ) (p : ℕ) (hp : 3 ≤ p) (hp' : p%2 = 1)
    (hs : ∀ q ∈ S, 3 ≤ q ∧ q%2 = 1 ∧ q < p) : 2*S.card+3 ≤ p := by
  have hc : S.card ≤ (range ((p-3)/2)).card := by
    apply card_le_card_of_injOn (fun q => (q-3)/2)
    · intro q hq
      obtain ⟨hq1,hq2,hq3⟩ := hs q hq
      apply mem_range.mpr
      change (q-3)/2 < (p-3)/2
      omega
    · intro q hq r hr eq
      obtain ⟨hq1,hq2,_⟩ := hs q hq
      obtain ⟨hr1,hr2,_⟩ := hs r hr
      dsimp at eq
      omega
  rw [card_range] at hc
  omega

/-- Squaring makes the bound on consecutive odd Euler factors telescope. -/
private theorem odd_product (S : Finset ℕ) (hs : ∀ q ∈ S, 3 ≤ q ∧ q%2 = 1) :
    (∏ q ∈ S, q)^2 ≤ (2*S.card+1)*(∏ q ∈ S, (q-1))^2 := by
  induction S using Finset.induction_on_max with
  | empty => simp
  | insert p S lp ih =>
    have hp0 : p ∉ S := fun h => (lp p h).false
    obtain ⟨hp,hp'⟩ := hs p (mem_insert_self ..)
    have hS (q) (hq : q ∈ S) := hs q (mem_insert_of_mem hq)
    have rank := odd_rank S p hp hp' (fun q hq => ⟨(hS q hq).1,(hS q hq).2,lp q hq⟩)
    have step : (2*S.card+1)*p^2 ≤ (2*(S.card+1)+1)*(p-1)^2 := by
      obtain ⟨d,he⟩ := Nat.exists_eq_add_of_le rank
      rw [he,show 2*S.card+3+d-1 = 2*S.card+2+d by omega]
      nlinarith only [Nat.zero_le S.card, Nat.zero_le d, Nat.zero_le (d^2),
        Nat.zero_le (S.card*d)]
    rw [prod_insert hp0,prod_insert hp0,card_insert_of_notMem hp0,mul_pow,mul_pow]
    calc
      p^2 * (∏ q ∈ S, q)^2 ≤ p^2*((2*S.card+1)*(∏ q ∈ S, (q-1))^2) :=
        Nat.mul_le_mul_left _ (ih hS)
      _ = ((2*S.card+1)*p^2)*(∏ q ∈ S, (q-1))^2 := by ring
      _ ≤ ((2*(S.card+1)+1)*(p-1)^2)*(∏ q ∈ S, (q-1))^2 :=
        Nat.mul_le_mul_right _ step
      _ = _ := by ring

theorem totient_card_bound (t : ℕ) :
    t^2 ≤ 4*(2*t.primeFactors.card+1)*t.totient^2 := by
  let S := t.primeFactors.erase 2
  have allOdd (p) (hp : p ∈ S) : 3 ≤ p ∧ p%2=1 := by
    obtain ⟨hne,hin⟩ := mem_erase.mp hp
    have h := Nat.prime_of_mem_primeFactors hin
    exact ⟨by have := h.two_le; omega,h.eq_two_or_odd.resolve_left hne⟩
  have hOdd := odd_product S allOdd
  have hc : S.card ≤ t.primeFactors.card := card_erase_le
  have full : (∏ p ∈ t.primeFactors, p)^2 ≤
      4*(2*t.primeFactors.card+1)*(∏ p ∈ t.primeFactors, (p-1))^2 := by
    by_cases h2 : 2 ∈ t.primeFactors
    · have hprod := mul_prod_erase t.primeFactors (fun p => p) h2
      have hsub := mul_prod_erase t.primeFactors (fun p => p-1) h2
      change 2*(∏ p ∈ S, p) = _ at hprod
      change (2-1:ℕ)*(∏ p ∈ S, (p-1)) = _ at hsub
      rw [← hprod,← hsub]
      simp only [Nat.reduceSub,one_mul,mul_pow]
      have lifted := Nat.mul_le_mul_right ((∏ p ∈ S, (p-1))^2)
        (show 2*S.card+1 ≤ 2*t.primeFactors.card+1 by omega)
      calc
        2^2*(∏ p ∈ S,p)^2 ≤ 4*((2*t.primeFactors.card+1)*(∏ p ∈ S,(p-1))^2) :=
          Nat.mul_le_mul_left _ (hOdd.trans lifted)
        _ = _ := by ring
    · have eq : S = t.primeFactors := erase_eq_of_notMem h2
      rw [eq] at hOdd
      exact hOdd.trans (by nlinarith only [Nat.zero_le ((2*t.primeFactors.card+1)*(∏ p ∈ t.primeFactors,(p-1))^2)])
  have hp : 0 < (∏ p ∈ t.primeFactors,(p-1))^2 := by
    apply Nat.pow_pos
    apply prod_pos
    intro p hin
    have := (Nat.prime_of_mem_primeFactors hin).two_le
    omega
  apply Nat.le_of_mul_le_mul_right _ hp
  calc
    t^2*(∏ p ∈ t.primeFactors,(p-1))^2 = (t*(∏ p ∈ t.primeFactors,(p-1)))^2 := (mul_pow ..).symm
    _ = (t.totient*(∏ p ∈ t.primeFactors,p))^2 := by rw [Nat.totient_mul_prod_primeFactors]
    _ ≤ t.totient^2*(4*(2*t.primeFactors.card+1)*(∏ p ∈ t.primeFactors,(p-1))^2) := by
      rw [mul_pow]
      exact Nat.mul_le_mul_left _ full
    _ = _ := by ring

theorem totient_log_bound (t : ℕ) (ht : 0 < t) :
    t^2 ≤ 4*(2*Nat.log 2 t+1)*t.totient^2 := by
  have card : t.primeFactors.card ≤ Nat.log 2 t := by
    apply Nat.le_log_of_pow_le (by decide)
    calc
      2^t.primeFactors.card = ∏ _p ∈ t.primeFactors, 2 := by simp
      _ ≤ ∏ p ∈ t.primeFactors, p := prod_le_prod' (fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le)
      _ ≤ t := Nat.le_of_dvd ht t.prod_primeFactors_dvd
  apply (totient_card_bound t).trans
  exact Nat.mul_le_mul_right _ (by omega)

end A247602

namespace A247602

open Real

/-- An explicit Chebyshev bound with the integer base-two logarithm. -/
theorem pi_mul_natLog_le (x : ℕ) : x.primeCounting * Nat.log 2 x ≤ 8*x := by
  by_cases hx : 1 < x
  · have hxr : (1 : ℝ) < x := by exact_mod_cast hx
    have hpos := Real.log_pos hxr
    have htwo : (1/2 : ℝ) ≤ log 2 := by linarith [Real.log_two_gt_d9]
    have hlog4 : log 4 = 2*log 2 := by
      rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]
      norm_num
    have hsqrt := Real.sqrt_nonneg (x:ℝ)
    have hspos := Real.sqrt_pos.2 (lt_trans zero_lt_one hxr)
    have hsq := Real.sq_sqrt (Nat.cast_nonneg x : (0:ℝ) ≤ x)
    have hl := Real.log_le_sub_one_of_pos hspos
    rw [Real.log_sqrt (Nat.cast_nonneg x)] at hl
    have hs : log x * √(x:ℝ) ≤ 2*x := by
      nlinarith [mul_le_mul_of_nonneg_right hl hsqrt]
    have h := Chebyshev.pi_le_log4_mul_div (x := (x:ℝ)) hxr
    rw [Nat.floor_natCast, Real.log_sqrt (Nat.cast_nonneg x), hlog4] at h
    have h' := (le_div_iff₀ (half_pos hpos)).mp
      (by linarith : (x.primeCounting : ℝ) - √(x:ℝ) ≤ 2*log 2*x/(log x/2))
    have hp : (x.primeCounting : ℝ) * log x ≤ (8*x) * log 2 := by
      nlinarith [mul_le_mul_of_nonneg_left htwo (Nat.cast_nonneg x : (0:ℝ) ≤ x)]
    have hlog := Real.natLog_le_logb x 2
    rw [Real.logb, Nat.cast_ofNat] at hlog
    have hlog' := (le_div_iff₀ (Real.log_pos (by norm_num : (1:ℝ) < 2))).mp hlog
    have hfinal : (x.primeCounting : ℝ) * (Nat.log 2 x : ℝ) ≤ 8*x := by
      apply le_of_mul_le_mul_right _ (Real.log_pos (by norm_num : (1:ℝ) < 2))
      calc
        (x.primeCounting : ℝ) * (Nat.log 2 x : ℝ) * log 2 =
            x.primeCounting * ((Nat.log 2 x : ℝ) * log 2) := by ring
        _ ≤ x.primeCounting * log x := mul_le_mul_of_nonneg_left hlog' (Nat.cast_nonneg _)
        _ ≤ _ := hp
    exact_mod_cast hfinal
  · interval_cases x <;> decide

/-- Every solution at a fixed positive index must lie inside an explicit finite search. -/
theorem witness_sum_lt (totBound : ∀ t : ℕ, 0 < t →
      t^2 ≤ 4*(2*Nat.log 2 t+1)*t.totient^2)
    (n m : ℕ) (hn : 0 < n) (hm : 0 < m)
    (hw : (m*n).primeCounting = (m+n).totient) : m+n < 2^(648*n^2+1) := by
  let t := m+n
  let x := m*n
  let L := Nat.log 2 t
  have ht : 0 < t := by dsimp [t]; omega
  have hx : 0 < x := Nat.mul_pos hm hn
  have htx : t ≤ x*2 := by
    have hm' : m ≤ m*n := by simpa using (Nat.mul_le_mul_left m hn)
    have hn' : n ≤ m*n := by simpa using (Nat.mul_le_mul_right n hm)
    dsimp [t,x]
    omega
  have hxn : x ≤ n*t := by dsimp [x,t]; nlinarith [Nat.zero_le (n*n)]
  have hlog : L ≤ Nat.log 2 x + 1 := by
    exact (Nat.log_monotone htx).trans_eq (Nat.log_mul_base (by decide) hx.ne')
  have hpx : x.primeCounting ≤ x := by
    rw [← Nat.primesLE_card_eq_primeCounting, Nat.primesLE_eq_filter_Icc_one]
    simpa using Finset.card_filter_le (s := Finset.Icc 1 x) Nat.Prime
  have hprod : t.totient * L ≤ 9*n*t := by
    change x.primeCounting = t.totient at hw
    calc
      t.totient * L = x.primeCounting * L := by rw [hw]
      _ ≤ x.primeCounting * (Nat.log 2 x + 1) := Nat.mul_le_mul_left _ hlog
      _ = x.primeCounting * Nat.log 2 x + x.primeCounting := by ring
      _ ≤ 9*x := by have := pi_mul_natLog_le x; omega
      _ ≤ 9*n*t := by nlinarith [hxn]
  have ht2 := totBound t ht
  change t^2 ≤ 4*(2*L+1)*t.totient^2 at ht2
  have hcancel : L^2 * t^2 ≤ (324*n^2*(2*L+1)) * t^2 := by
    calc
      L^2 * t^2 ≤ L^2 * (4*(2*L+1)*t.totient^2) := Nat.mul_le_mul_left _ ht2
      _ = 4*(2*L+1)*(t.totient*L)^2 := by ring
      _ ≤ 4*(2*L+1)*(9*n*t)^2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hprod _)
      _ = _ := by ring
  have hL2 := Nat.le_of_mul_le_mul_right hcancel (pow_pos ht 2)
  have hL : L ≤ 648*n^2 := by
    by_contra! h
    have h' : 648*n^2+1 ≤ L := h
    nlinarith [Nat.mul_le_mul_right L h', Nat.zero_le (n^2)]
  exact (Nat.lt_pow_succ_log_self (by decide : 1 < 2) t).trans_le
    (Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.succ_le_succ hL))

end A247602

namespace A247602

private theorem square_succ_le_two_pow (m : ℕ) (hm : 5 ≤ m) : m^2+1 ≤ 2^m := by
  induction m, hm using Nat.le_induction with
  | base => decide
  | succ m hm ih =>
    rw [pow_succ 2 m]
    nlinarith [Nat.mul_le_mul_left m (show 2 ≤ m by omega)]

/-- Among two partners the smaller cannot exceed four times the base-two
logarithm of the larger, up to one unit. -/
theorem witness_diagonal (n m : ℕ) (hn : 1 ≤ n) (hle : n ≤ m)
    (he : Nat.primeCounting (m*n) = Nat.totient (m+n)) : 2^n ≤ 2*m^4 := by
  by_cases hsmall : m < 5
  · interval_cases m <;> interval_cases n <;> decide
  have hm : 5 ≤ m := by omega
  have hmR : (0:ℝ) < m := by positivity
  have hmn : 1 < m*n := by nlinarith [Nat.mul_le_mul_left m hn]
  have hmnR : 1 < ((m*n:ℕ):ℝ) := by exact_mod_cast hmn
  have hπ := (div_le_iff₀ (Real.log_pos hmnR)).mp (Chebyshev.pi_ge (m*n))
  have hπ' : ((m*n).primeCounting:ℝ) ≤ 2*m := by
    exact_mod_cast (show (m*n).primeCounting ≤ 2*m by rw [he]; have := Nat.totient_le (m+n); omega)
  have ht : m*n+1 ≤ 2^m :=
    (Nat.add_le_add_right (by simpa [sq] using Nat.mul_le_mul_left m hle) 1).trans
      (square_succ_le_two_pow m hm)
  have hl₁ : Real.log (((m*n:ℕ):ℝ)+1) ≤ (m:ℝ)*Real.log 2 := by
    rw [← Real.log_pow]
    apply Real.log_le_log (by positivity)
    exact_mod_cast ht
  have hl₂ : Real.log ((m*n:ℕ):ℝ) ≤ 2*Real.log m := by
    rw [show (2:ℝ)=((2:ℕ):ℝ) by norm_num,← Real.log_pow]
    apply Real.log_le_log (by positivity)
    exact_mod_cast (show m*n ≤ m^2 by simpa [sq] using Nat.mul_le_mul_left m hle)
  have hv : (m:ℝ) * ((n:ℝ)*Real.log 2) ≤ (m:ℝ)*(4*Real.log m + Real.log 2) := by
    have ht₁ := mul_le_mul_of_nonneg_right hπ' (Real.log_nonneg hmnR.le)
    have ht₂ := mul_le_mul_of_nonneg_left hl₂ (show (0:ℝ) ≤ 2*m by positivity)
    push_cast at hπ
    push_cast at ht₁ ht₂ hl₁
    nlinarith only [hπ,ht₁,ht₂,hl₁]
  have hv' := (mul_le_mul_iff_right₀ hmR).mp hv
  have hp : (2:ℝ)^n ≤ 2*(m:ℝ)^4 := by
    rw [← Real.log_le_log_iff (by positivity) (by positivity),
      Real.log_mul (by norm_num) (by positivity), Real.log_pow,Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith only [hv']
  exact_mod_cast hp

end A247602

namespace A247602

theorem small_partner_le (n m : ℕ) (hn : 0 < n) (hle : n ≤ m)
    (hw : (m*n).primeCounting = (m+n).totient) : n ≤ 4*(Nat.log 2 m+1) := by
  have h := witness_diagonal n m hn hle hw
  let L := Nat.log 2 m + 1
  have hm : m < 2^L := Nat.lt_pow_succ_log_self (by decide : 1 < 2) m
  have hp : (2:ℕ)^n < 2^(4*L+1) := calc
    (2:ℕ)^n ≤ 2*m^4 := h
    _ < 2*(2^L)^4 := Nat.mul_lt_mul_of_pos_left
      (Nat.pow_lt_pow_left hm (by decide : 4 ≠ 0)) (by decide)
    _ = 2^(4*L+1) := by rw [pow_succ (2:ℕ) (4*L), mul_comm 4 L, pow_mul, mul_comm]
  change n ≤ 4*L
  by_contra! hlarge
  exact hp.not_ge (Nat.pow_le_pow_right (by decide : 0 < 2) hlarge)

/-- The two possible size ranges for a solution at index `n`: a logarithmically
bounded smaller partner or an exponentially large partner below the finite cutoff. -/
theorem witness_iff_in_intervals (n : ℕ) (hn : 0 < n) :
    (∃ m : ℕ, 0 < m ∧ (m*n).primeCounting = (m+n).totient) ↔
    (∃ m ∈ Finset.Icc 1 (min (n-1) (4*(Nat.log 2 n+1))),
        (m*n).primeCounting = (m+n).totient) ∨
    (∃ m ∈ Finset.Ico (max n (2^((n-1)/4))) (2^(648*n^2+1)),
        (m*n).primeCounting = (m+n).totient) := by
  constructor
  · rintro ⟨m, hm, hw⟩
    by_cases hmn : m < n
    · left
      have hsym : (n*m).primeCounting = (n+m).totient := by
        simpa only [mul_comm n m, add_comm n m] using hw
      have hu := small_partner_le m n hm hmn.le hsym
      exact ⟨m, Finset.mem_Icc.mpr ⟨hm, le_min (by omega) hu⟩, hw⟩
    · right
      have hlog := small_partner_le n m hn (by omega) hw
      have hexp : 2^((n-1)/4) ≤ m := Nat.pow_le_of_le_log hm.ne' (by omega)
      have hupper := witness_sum_lt totient_log_bound n m hn hm hw
      exact ⟨m, Finset.mem_Ico.mpr ⟨max_le (by omega) hexp, by omega⟩, hw⟩
  · rintro (⟨m, hmem, hw⟩ | ⟨m, hmem, hw⟩)
    · exact ⟨m, (Finset.mem_Icc.mp hmem).1, hw⟩
    · exact ⟨m, hn.trans_le ((le_max_left _ _).trans (Finset.mem_Ico.mp hmem).1), hw⟩

private theorem fourth_lt_two_pow (n : ℕ) (hn : 18 ≤ n) : 2*n^4 < 2^n := by
  induction n, hn using Nat.le_induction with
  | base => decide
  | succ n hn ih =>
    have h : 2*(n+1)^4 ≤ 2*(2*n^4) := by
      obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hn
      nlinarith only [Nat.zero_le d, Nat.zero_le (d^2), Nat.zero_le (d^3), Nat.zero_le (d^4)]
    rw [pow_succ (2:ℕ) n, mul_comm (2^n) 2]
    exact h.trans_lt (Nat.mul_lt_mul_of_pos_left ih (by decide))

/-- The sole positive index which is its own partner is two. -/
theorem equal_partners_iff (n : ℕ) (hn : 0 < n) :
    (n*n).primeCounting = (n+n).totient ↔ n = 2 := by
  constructor
  · intro hw
    have h := witness_diagonal n n hn le_rfl hw
    have hsmall : n < 18 := by
      by_contra! hlarge
      exact (fourth_lt_two_pow n hlarge).not_ge h
    revert hw
    interval_cases n <;> decide +kernel
  · rintro rfl
    decide +kernel

end A247602

namespace OMA.R_oeis_a247602_R1

/-- The first eleven indices, including the first two larger-partner cases. -/
def H1 : Prop :=
  ∀ n : ℕ, 1 ≤ n → n ≤ 11 → ∃ m : ℕ, 0 < m ∧ (m*n).primeCounting = (m+n).totient

/-- If the logarithmically bounded search fails, find a witness in the larger finite interval. -/
def H2 : Prop :=
  ∀ n : ℕ, 12 ≤ n →
    (∀ m ∈ Finset.Icc 1 (min (n-1) (4*(Nat.log 2 n+1))),
      (m*n).primeCounting ≠ (m+n).totient) →
    ∃ m ∈ Finset.Ico (max n (2^((n-1)/4))) (2^(648*n^2+1)),
      (m*n).primeCounting = (m+n).totient

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a247602.main := by
  classical
  intro small large n hn
  by_cases hn₁ : n ≤ 11
  · exact small n hn hn₁
  · apply (A247602.witness_iff_in_intervals n hn).mpr
    by_cases short : ∃ m ∈ Finset.Icc 1 (min (n-1) (4*(Nat.log 2 n+1))),
        (m*n).primeCounting = (m+n).totient
    · exact Or.inl short
    · exact Or.inr (large n (by omega) (by
        intro m hmem he
        exact short ⟨m,hmem,he⟩))

end OMA.R_oeis_a247602_R1
