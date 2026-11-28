import OMAStatements.S_oeis_a372420
import Mathlib

/-!
# Proof of the two conjectures of OEIS A372420 (Mélika Tebni, Apr 30 2024)

`a(n) = [x^n] (1 + x)/((1 - 2x) sqrt(1 - 4x))`. For a prime `p`:
`a(p) == 5 (mod p)` if `p = 4k + 1`, and `a(p) == -1 (mod p)` if `p = 4k + 3`.

Write `c(k) = C(2k,k)`, `S = Sum c(k) x^k` and `B = (1 - 2x)^(-1) * S`, `b(n) = [x^n] B`.

1. `(1 - 2x) B = S` gives `b(0) = 1`, `b(n+1) = c(n+1) + 2 b(n)`, hence
   `b(n) = Sum_{k<=n} 2^(n-k) c(k)`.
2. `a(n+1) = b(n+1) + b(n) = c(n+1) + 3 b(n)`.
3. For the odd prime `p = 2m + 1` and `k < p`: `c(k) = (-4)^k C(m,k)` modulo `p`. Both sides satisfy
   `(k+1) u(k+1) = 2(2k+1) u(k)` modulo `p` (for the right side: `(k+1) C(m,k+1) = (m-k) C(m,k)` and
   `-4(m-k) = 2(2k+1) - 2p`), and `k + 1 < p` is invertible.
4. `c(p) = 2` modulo `p` (Lucas).
5. Modulo `p`: `b(p-1) = Sum_{k<p} 2^(p-1-k) (-4)^k C(m,k) = 2^(p-1) Sum_{k<=m} C(m,k) (-2)^k
   = (1 - 2)^m = (-1)^m` by Fermat and the binomial theorem.
6. So `a(p) = 2 + 3 (-1)^m` modulo `p`: this is `5` for `m` even (`p = 4k + 1`) and `-1` for `m` odd
   (`p = 4k + 3`).
-/


/-- `B = (1 - 2x)^(-1) * S`, where `S = Sum C(2k,k) x^k`. -/
private noncomputable def a372420_B : PowerSeries ℤ :=
  Ring.inverse (1 - 2 * PowerSeries.X) * OMA.S_oeis_a372420.invSqrt

private lemma a372420_isUnit_den : IsUnit (1 - 2 * PowerSeries.X : PowerSeries ℤ) := by
  rw [PowerSeries.isUnit_iff_constantCoeff]
  simp

/-- `B = S + 2 x B`. -/
private lemma a372420_B_eq :
    a372420_B = OMA.S_oeis_a372420.invSqrt +
      (PowerSeries.X * a372420_B + PowerSeries.X * a372420_B) := by
  have h : (1 - 2 * PowerSeries.X : PowerSeries ℤ) * a372420_B = OMA.S_oeis_a372420.invSqrt := by
    unfold a372420_B
    exact Ring.mul_inverse_cancel_left _ _ a372420_isUnit_den
  linear_combination h

private lemma a372420_coeff_B_zero : PowerSeries.coeff 0 a372420_B = 1 := by
  have h := congrArg (PowerSeries.coeff 0) a372420_B_eq
  rw [map_add, map_add, PowerSeries.coeff_zero_X_mul, add_zero, add_zero] at h
  rw [h, OMA.S_oeis_a372420.invSqrt, PowerSeries.coeff_mk, Nat.centralBinom_zero, Nat.cast_one]

private lemma a372420_coeff_B_succ (n : ℕ) :
    PowerSeries.coeff (n + 1) a372420_B =
      ((n + 1).centralBinom : ℤ) + 2 * PowerSeries.coeff n a372420_B := by
  have h := congrArg (PowerSeries.coeff (n + 1)) a372420_B_eq
  rw [map_add, map_add, PowerSeries.coeff_succ_X_mul] at h
  rw [h, OMA.S_oeis_a372420.invSqrt, PowerSeries.coeff_mk]
  ring

/-- `[x^n] B = Sum_{k<=n} 2^(n-k) C(2k,k)`. -/
private lemma a372420_coeff_B (n : ℕ) :
    PowerSeries.coeff n a372420_B =
      ∑ k ∈ Finset.range (n + 1), (2 : ℤ) ^ (n - k) * (k.centralBinom : ℤ) := by
  induction n with
  | zero => simp [a372420_coeff_B_zero]
  | succ n ih =>
    have hsum : ∑ k ∈ Finset.range (n + 1), 2 * ((2 : ℤ) ^ (n - k) * (k.centralBinom : ℤ)) =
        ∑ k ∈ Finset.range (n + 1), (2 : ℤ) ^ (n + 1 - k) * (k.centralBinom : ℤ) := by
      apply Finset.sum_congr rfl
      intro k hk
      have hk' : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      rw [show n + 1 - k = (n - k) + 1 by omega, pow_succ]
      ring
    rw [a372420_coeff_B_succ, ih, Finset.sum_range_succ _ (n + 1), Finset.mul_sum, hsum,
      Nat.sub_self, pow_zero, one_mul]
    ring

/-- `a(n+1) = C(2n+2,n+1) + 3 [x^n] B`. -/
private lemma a372420_a_succ (n : ℕ) :
    OMA.S_oeis_a372420.a (n + 1) =
      ((n + 1).centralBinom : ℤ) + 3 * PowerSeries.coeff n a372420_B := by
  have hf : OMA.S_oeis_a372420.f = a372420_B + PowerSeries.X * a372420_B := by
    unfold OMA.S_oeis_a372420.f a372420_B
    ring
  unfold OMA.S_oeis_a372420.a
  rw [hf, map_add, PowerSeries.coeff_succ_X_mul, a372420_coeff_B_succ]
  ring

/-- `(k+1) C(m,k+1) = (m-k) C(m,k)` in the integers, for every `k` (both sides vanish for `k > m`). -/
private lemma a372420_choose_rec (m k : ℕ) :
    ((k : ℤ) + 1) * (m.choose (k + 1) : ℤ) = ((m : ℤ) - k) * (m.choose k : ℤ) := by
  rcases le_or_gt k m with h | h
  · have h1 := Nat.choose_succ_right_eq m k
    have h2 : ((m.choose (k + 1) * (k + 1) : ℕ) : ℤ) = ((m.choose k * (m - k) : ℕ) : ℤ) := by
      rw [h1]
    push_cast [Nat.cast_sub h] at h2
    linarith
  · rw [Nat.choose_eq_zero_of_lt (by omega : m < k + 1), Nat.choose_eq_zero_of_lt h]
    simp

/-- `C(2k,k) = (-4)^k C(m,k)` modulo the prime `p = 2m+1`, for `k < p`. -/
private lemma a372420_centralBinom_zmod (p m : ℕ) [Fact p.Prime] (hpm : p = 2 * m + 1) :
    ∀ k : ℕ, k < p → (k.centralBinom : ZMod p) = (-4) ^ k * (m.choose k : ZMod p) := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
    intro hk
    have ih' := ih (by omega)
    have h1 : ((k : ZMod p) + 1) * ((k + 1).centralBinom : ZMod p) =
        2 * (2 * (k : ZMod p) + 1) * (k.centralBinom : ZMod p) := by
      have h := congrArg (Nat.cast : ℕ → ZMod p) (Nat.succ_mul_centralBinom_succ k)
      push_cast at h
      exact h
    have h2 : ((k : ZMod p) + 1) * (m.choose (k + 1) : ZMod p) =
        ((m : ZMod p) - k) * (m.choose k : ZMod p) := by
      have h := congrArg (Int.cast : ℤ → ZMod p) (a372420_choose_rec m k)
      push_cast at h
      exact h
    have hm : (2 : ZMod p) * (m : ZMod p) = -1 := by
      have h : ((2 * m + 1 : ℕ) : ZMod p) = 0 := by
        rw [← hpm]
        exact ZMod.natCast_self p
      push_cast at h
      linear_combination h
    have hne : ((k : ZMod p) + 1) ≠ 0 := by
      have h : ((k + 1 : ℕ) : ZMod p) ≠ 0 := by
        rw [Ne, ZMod.natCast_eq_zero_iff]
        intro hdvd
        have := Nat.le_of_dvd (Nat.succ_pos k) hdvd
        omega
      simpa using h
    apply mul_left_cancel₀ hne
    rw [h1, ih']
    calc 2 * (2 * (k : ZMod p) + 1) * ((-4) ^ k * (m.choose k : ZMod p))
        = (-4) ^ (k + 1) * (((m : ZMod p) - k) * (m.choose k : ZMod p)) := by
          rw [pow_succ]
          linear_combination (2 * (-4) ^ k * (m.choose k : ZMod p)) * hm
      _ = ((k : ZMod p) + 1) * ((-4) ^ (k + 1) * (m.choose (k + 1) : ZMod p)) := by
          rw [← h2]
          ring

/-- `C(2p,p) = 2` modulo the prime `p` (Lucas). -/
private lemma a372420_centralBinom_self_zmod (p : ℕ) [Fact p.Prime] :
    (p.centralBinom : ZMod p) = 2 := by
  have hp := (Fact.out : p.Prime)
  have h := Choose.choose_modEq_choose_mod_mul_choose_div_nat (n := 2 * p) (k := p) (p := p)
  have h1 : 2 * p % p = 0 := Nat.mul_mod_left 2 p
  have h2 : 2 * p / p = 2 := Nat.mul_div_cancel 2 hp.pos
  have h3 : p % p = 0 := Nat.mod_self p
  have h4 : p / p = 1 := Nat.div_self hp.pos
  rw [h1, h2, h3, h4] at h
  rw [Nat.centralBinom_eq_two_mul_choose, (ZMod.natCast_eq_natCast_iff _ _ _).mpr h]
  norm_num [Nat.choose]

/-- `a(p) = 2 + 3 (-1)^m` modulo the prime `p = 2m+1`. -/
private lemma a372420_key (p m : ℕ) [Fact p.Prime] (hpm : p = 2 * m + 1) :
    ((OMA.S_oeis_a372420.a p : ℤ) : ZMod p) = 2 + 3 * (-1) ^ m := by
  have hp := (Fact.out : p.Prime)
  have ha : OMA.S_oeis_a372420.a p =
      (p.centralBinom : ℤ) + 3 * PowerSeries.coeff (p - 1) a372420_B := by
    have h := a372420_a_succ (p - 1)
    rwa [Nat.sub_add_cancel hp.one_le] at h
  have h2 : (2 : ZMod p) ^ (p - 1) = 1 := by
    apply ZMod.pow_card_sub_one_eq_one
    intro h
    have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at h'
    have := Nat.le_of_dvd (by norm_num) h'
    have := hp.two_le
    omega
  have hsum : (∑ k ∈ Finset.range p, (2 : ZMod p) ^ (p - 1 - k) * (k.centralBinom : ZMod p)) =
      (-1) ^ m := by
    calc ∑ k ∈ Finset.range p, (2 : ZMod p) ^ (p - 1 - k) * (k.centralBinom : ZMod p)
        = ∑ k ∈ Finset.range p, (-2 : ZMod p) ^ k * 1 ^ (m - k) * (m.choose k : ZMod p) := by
          apply Finset.sum_congr rfl
          intro k hk
          have hk' : k < p := Finset.mem_range.mp hk
          have e1 : (2 : ZMod p) ^ (p - 1 - k) * 2 ^ k = 1 := by
            rw [← pow_add, Nat.sub_add_cancel (by omega), h2]
          have e : (2 : ZMod p) ^ (p - 1 - k) * (-4) ^ k = (-2) ^ k := by
            calc (2 : ZMod p) ^ (p - 1 - k) * (-4) ^ k
                = ((2 : ZMod p) ^ (p - 1 - k) * 2 ^ k) * (-2) ^ k := by
                  rw [show (-4 : ZMod p) = 2 * (-2) by norm_num, mul_pow]
                  ring
              _ = (-2) ^ k := by rw [e1, one_mul]
          rw [a372420_centralBinom_zmod p m hpm k hk', one_pow, mul_one, ← mul_assoc, e]
      _ = ∑ k ∈ Finset.range (m + 1), (-2 : ZMod p) ^ k * 1 ^ (m - k) * (m.choose k : ZMod p) := by
          symm
          apply Finset.sum_subset
          · intro x hx
            rw [Finset.mem_range] at hx
            rw [Finset.mem_range]
            omega
          · intro x _ hx
            have hx' : m < x := by
              rw [Finset.mem_range] at hx
              omega
            rw [Nat.choose_eq_zero_of_lt hx']
            simp
      _ = ((-2 : ZMod p) + 1) ^ m := (add_pow (-2 : ZMod p) 1 m).symm
      _ = (-1) ^ m := by norm_num
  rw [ha, a372420_coeff_B]
  push_cast
  rw [a372420_centralBinom_self_zmod p, Nat.sub_add_cancel hp.one_le, hsum]

theorem OMA.solution : type_of% @OMA.S_oeis_a372420.main := by
  refine ⟨?_, ?_⟩
  · intro p hp h4
    have : Fact p.Prime := ⟨hp⟩
    obtain ⟨m, hm⟩ : ∃ m, p = 2 * m + 1 := ⟨p / 2, by omega⟩
    have hk := a372420_key p m hm
    have hev : Even m := by
      rw [Nat.even_iff]
      omega
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [hk, hev.neg_one_pow]
    norm_num
  · intro p hp h4
    have : Fact p.Prime := ⟨hp⟩
    obtain ⟨m, hm⟩ : ∃ m, p = 2 * m + 1 := ⟨p / 2, by omega⟩
    have hk := a372420_key p m hm
    have hodd : Odd m := by
      rw [Nat.odd_iff]
      omega
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [hk, hodd.neg_one_pow]
    norm_num
