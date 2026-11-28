import OMAStatements.S_oeis_a257743
import Mathlib

namespace OMA.A257743Proof

open OMA.S_oeis_a257743

/-- The odd part of `2 ^ f * y` for odd `y` is `y`. -/
theorem oddPart_two_pow_mul {f y : ℕ} (hy : y % 2 = 1) : oddPart (2 ^ f * y) = y := by
  have hy0 : y ≠ 0 := by omega
  have h2 : ¬ 2 ∣ y := by omega
  unfold oddPart
  rw [Nat.factorization_mul (pow_ne_zero f (by norm_num : (2 : ℕ) ≠ 0)) hy0, Finsupp.add_apply,
    Nat.factorization_pow_self Nat.prime_two, Nat.factorization_eq_zero_of_not_dvd h2, add_zero,
    Nat.mul_div_cancel_left y (pow_pos (by norm_num : (0 : ℕ) < 2) f)]

/-- An odd number is its own odd part. -/
theorem oddPart_of_odd {n : ℕ} (hn : n % 2 = 1) : oddPart n = n := by
  have h := oddPart_two_pow_mul (f := 0) hn
  rwa [pow_zero, one_mul] at h

/-- Every odd `y` with `3 ∤ y` has an odd composite preimage `x` under `T` with `3 ∤ x`. -/
theorem exists_pre (y : ℕ) (hy2 : y % 2 = 1) (hy3 : y % 3 ≠ 0) :
    ∃ x : ℕ, x % 2 = 1 ∧ x % 3 ≠ 0 ∧ x ≠ 1 ∧ ¬ x.Prime ∧ T x = y := by
  -- an exponent `e ≥ 1` with `2 ^ e * y ≡ 7 (mod 9)`
  obtain ⟨e, he1, he⟩ : ∃ e : ℕ, 1 ≤ e ∧ 2 ^ e * y % 9 = 7 := by
    have h9 : y % 9 = 1 ∨ y % 9 = 2 ∨ y % 9 = 4 ∨ y % 9 = 5 ∨ y % 9 = 7 ∨ y % 9 = 8 := by omega
    rcases h9 with h | h | h | h | h | h
    · exact ⟨4, by norm_num, by rw [show (2 : ℕ) ^ 4 = 16 by norm_num]; omega⟩
    · exact ⟨3, by norm_num, by rw [show (2 : ℕ) ^ 3 = 8 by norm_num]; omega⟩
    · exact ⟨2, by norm_num, by rw [show (2 : ℕ) ^ 2 = 4 by norm_num]; omega⟩
    · exact ⟨5, by norm_num, by rw [show (2 : ℕ) ^ 5 = 32 by norm_num]; omega⟩
    · exact ⟨6, by norm_num, by rw [show (2 : ℕ) ^ 6 = 64 by norm_num]; omega⟩
    · exact ⟨1, by norm_num, by rw [show (2 : ℕ) ^ 1 = 2 by norm_num]; omega⟩
  have hP2 : 2 ∣ 2 ^ e * y := Dvd.dvd.mul_right (dvd_pow_self 2 (by omega)) y
  -- the first preimage `m = (2 ^ e * y - 1) / 3`, used as a modulus
  obtain ⟨m, hm⟩ : ∃ m : ℕ, 3 * m + 1 = 2 ^ e * y := ⟨2 ^ e * y / 3, by omega⟩
  have hm3 : m % 3 = 2 := by omega
  have hm0 : 0 < m := by omega
  have hcop : Nat.Coprime 2 m := (Nat.prime_two.coprime_iff_not_dvd).mpr (by omega)
  have hgcd : Nat.gcd m 3 = 1 :=
    Nat.Coprime.symm ((Nat.prime_three.coprime_iff_not_dvd).mpr (by omega))
  -- `W = 2 ^ (6 * φ m)` is `1` modulo `m` and modulo `9`
  have hWm : Nat.ModEq m (2 ^ (Nat.totient m * 6)) 1 := by
    have h := (Nat.ModEq.pow_totient hcop).pow 6
    rwa [one_pow, ← pow_mul] at h
  have hW9 : Nat.ModEq 9 (2 ^ (Nat.totient m * 6)) 1 := by
    have h64 : Nat.ModEq 9 (2 ^ 6) 1 := by unfold Nat.ModEq; norm_num
    have h := h64.pow (Nat.totient m)
    rwa [one_pow, ← pow_mul, Nat.mul_comm 6 (Nat.totient m)] at h
  have htot : 0 < Nat.totient m := Nat.totient_pos.mpr hm0
  have hW2 : 2 ≤ 2 ^ (Nat.totient m * 6) := by
    have h := Nat.pow_le_pow_right (show 0 < 2 by norm_num) (show 1 ≤ Nat.totient m * 6 by omega)
    rwa [pow_one] at h
  have hQ : 2 ^ (e + Nat.totient m * 6) * y = (2 ^ e * y) * 2 ^ (Nat.totient m * 6) := by
    rw [pow_add]; ring
  have hA9 : Nat.ModEq 9 (2 ^ e * y) 7 := he
  have hQ9 : (2 ^ e * y) * 2 ^ (Nat.totient m * 6) % 9 = 7 := hA9.mul hW9
  have hQ2 : 2 ∣ (2 ^ e * y) * 2 ^ (Nat.totient m * 6) := Dvd.dvd.mul_right hP2 _
  -- the preimage `x = (2 ^ e * y * W - 1) / 3`
  obtain ⟨x, hx⟩ : ∃ x : ℕ, 3 * x + 1 = (2 ^ e * y) * 2 ^ (Nat.totient m * 6) :=
    ⟨(2 ^ e * y) * 2 ^ (Nat.totient m * 6) / 3, by omega⟩
  have hx3 : x % 3 = 2 := by omega
  have hx2 : x % 2 = 1 := by omega
  have hxm : m < x := by
    have h1 : (2 ^ e * y) * 2 ≤ (2 ^ e * y) * 2 ^ (Nat.totient m * 6) := Nat.mul_le_mul le_rfl hW2
    omega
  -- `m ∣ x`
  have hQm : Nat.ModEq m ((2 ^ e * y) * 2 ^ (Nat.totient m * 6)) ((2 ^ e * y) * 1) :=
    Nat.ModEq.mul_left _ hWm
  rw [← hx, mul_one, ← hm] at hQm
  have h3 : Nat.ModEq m (3 * x) (3 * m) := Nat.ModEq.add_right_cancel' 1 hQm
  have h4 : Nat.ModEq m x m := Nat.ModEq.cancel_left_of_coprime hgcd h3
  have hdvd : m ∣ x := by
    have h5 : x % m = m % m := h4
    rw [Nat.mod_self] at h5
    exact Nat.dvd_of_mod_eq_zero h5
  have hxp : ¬ x.Prime := by
    intro hp
    rcases hp.eq_one_or_self_of_dvd m hdvd with h | h <;> omega
  have hT : T x = y := by
    unfold T
    rw [hx, ← hQ]
    exact oddPart_two_pow_mul hy2
  exact ⟨x, hx2, by omega, by omega, hxp, hT⟩

/-- For every `N` there is an odd `n` with `3 ∤ n` whose first `N` iterates under `T` are neither 1 nor prime and
whose `N`-th iterate is the prime 5. -/
theorem chain (N : ℕ) : ∃ n : ℕ, n % 2 = 1 ∧ n % 3 ≠ 0 ∧
    (∀ k < N, T^[k] n ≠ 1 ∧ ¬ (T^[k] n).Prime) ∧ T^[N] n = 5 := by
  induction N with
  | zero => exact ⟨5, by norm_num, by norm_num, fun k hk => absurd hk (Nat.not_lt_zero k), rfl⟩
  | succ N ih =>
    obtain ⟨n, hn2, hn3, hk, hN⟩ := ih
    obtain ⟨x, hx2, hx3, hx1, hxp, hTx⟩ := exists_pre n hn2 hn3
    refine ⟨x, hx2, hx3, ?_, ?_⟩
    · intro k hk'
      cases k with
      | zero => exact ⟨hx1, hxp⟩
      | succ j =>
        show T^[j] (T x) ≠ 1 ∧ ¬ (T^[j] (T x)).Prime
        rw [hTx]
        exact hk j (by omega)
    · show T^[N] (T x) = 5
      rw [hTx]
      exact hN

end OMA.A257743Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a257743.main := by
  intro N _hN
  obtain ⟨n, hn2, _hn3, hk, hN5⟩ := OMA.A257743Proof.chain N
  refine ⟨n, by omega, ?_⟩
  unfold OMA.S_oeis_a257743.a
  rw [OMA.A257743Proof.oddPart_of_odd hn2]
  have hmem : N ∈ {k : ℕ | OMA.S_oeis_a257743.T^[k] n = 1 ∨ (OMA.S_oeis_a257743.T^[k] n).Prime} := by
    show OMA.S_oeis_a257743.T^[N] n = 1 ∨ (OMA.S_oeis_a257743.T^[N] n).Prime
    right
    rw [hN5]
    norm_num
  have hle : N ≤ sInf {k : ℕ | OMA.S_oeis_a257743.T^[k] n = 1 ∨ (OMA.S_oeis_a257743.T^[k] n).Prime} := by
    apply le_csInf ⟨N, hmem⟩
    intro b hb
    have hb' : OMA.S_oeis_a257743.T^[b] n = 1 ∨ (OMA.S_oeis_a257743.T^[b] n).Prime := hb
    rcases Nat.lt_or_ge b N with hlt | hge
    · rcases hb' with h | h
      · exact absurd h (hk b hlt).1
      · exact absurd h (hk b hlt).2
    · exact hge
  omega
