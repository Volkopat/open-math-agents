import OMAStatements.S_oeis_a249938
import Mathlib

/-!
# Proof of OEIS A249938 Conjectures

1. Using `k! * S(m, k) = ∑_{r=0..k} (-1)^(k-r) C(k, r) r^m`:
   - Modulo `9`, terms `k >= 6` vanish (`9 ∣ k!`), `a(n + 3) ≡ a(n) [MOD 9]` for `n >= 1`,
     and checking `n = 1, 2, 3` gives `a(n) ≡ 3 [MOD 9]` for all `n >= 1`.
   - Modulo `32`, terms `k >= 8` vanish (`32 ∣ k!`), `a(n + 4) ≡ a(n) [MOD 32]` for `n >= 3`,
     and checking `n = 2, 3, 4, 5, 6` gives `a(n) ≡ 11 [MOD 32]` for all `n >= 2`.
   - By CRT, `a(n) ≡ 75 [MOD 288]` for all `n >= 2`, so `288 ∣ a(n + 1) - a(n)`.
   - Conversely, `gcd(a(3) - a(2), a(4) - a(3)) = gcd(4608, 541152) = 288`, so any modulus `m`
     with `a(n + 1) ≡ a(n) [MOD m]` for all `n > 1` divides `288`.

2. Modulo an odd prime `p >= 5` with `t = (p - 1) / 2`:
   - Swapping the Stirling sum gives `(a n : ZMod p) = ∑_{r=1..p-1} c_r r^(2n)`, where
     `c_r = ∑_{k=r..p-1} (-1)^(k-r) C(k, r) = 2^(p - 1 - r)` in `ZMod p`.
   - Pairing `r` and `p - r` expresses `a(n) = ∑_{r=1..t} (2^(p-1-r) + 2^(r-1)) * (r^2)^n`,
     giving period dividing `t`.
   - Any period `d >= 1` reduces to `g = gcd(d, t) ∣ t`. If `g < t`, Vandermonde invertibility
     forces `(2^(p-1-r) + 2^(r-1)) * ((r^2)^g - 1) = 0` for all `1 <= r <= t`.
     At most `g <= t / 2` values satisfy `(r^2)^g = 1`, while for `p >= 11` any two solutions to
     `2^(2r - 1) = -1` are spaced by at least `3` (since `2^2 - 1 = 3` and `2^4 - 1 = 15`),
     leaving at most `(t + 2) / 3` solutions, contradicting `g + (t + 2) / 3 < t` for `t >= 5`.
     Primes `p = 2, 3, 5, 7` are checked directly.
-/

namespace OeisA249938Proof

open Finset OMA.S_oeis_a249938

private lemma stirling2_eq_zero_of_lt : ∀ n j : ℕ, n < j → stirling2 n j = 0 := by
  intro n
  induction n with
  | zero =>
    intro j hj
    cases j with
    | zero => omega
    | succ j => rfl
  | succ n ih =>
    intro j hj
    cases j with
    | zero => omega
    | succ j =>
      simp only [stirling2]
      rw [ih (j + 1) (by omega), ih j (by omega)]
      ring

private lemma mul_choose_eq_sub_mul_choose (j r : ℕ) (hr : r ≤ j) :
    ((j : ℤ) + 1) * (Nat.choose j r : ℤ) =
      ((j : ℤ) + 1 - (r : ℤ)) * (Nat.choose (j + 1) r : ℤ) := by
  have hnat : (j + 1) * Nat.choose j r = (j + 1 - r) * Nat.choose (j + 1) r := by
    have h1 := Nat.choose_mul_factorial_mul_factorial hr
    have h2 := Nat.choose_mul_factorial_mul_factorial (by omega : r ≤ j + 1)
    have hsub : j + 1 - r = (j - r) + 1 := by omega
    have hfac1 : (j + 1).factorial = (j + 1) * j.factorial := Nat.factorial_succ j
    have hfac2 : (j + 1 - r).factorial = (j + 1 - r) * (j - r).factorial := by
      rw [hsub, Nat.factorial_succ, ← hsub]
    have hpos : 0 < r.factorial * (j - r).factorial :=
      Nat.mul_pos (Nat.factorial_pos r) (Nat.factorial_pos (j - r))
    apply Nat.eq_of_mul_eq_mul_right hpos
    calc
      (j + 1) * Nat.choose j r * (r.factorial * (j - r).factorial)
          = (j + 1) * (Nat.choose j r * r.factorial * (j - r).factorial) := by ring
      _ = (j + 1) * j.factorial := by rw [h1]
      _ = (j + 1).factorial := hfac1.symm
      _ = Nat.choose (j + 1) r * r.factorial * (j + 1 - r).factorial := h2.symm
      _ = Nat.choose (j + 1) r * r.factorial * ((j + 1 - r) * (j - r).factorial) := by rw [hfac2]
      _ = (j + 1 - r) * Nat.choose (j + 1) r * (r.factorial * (j - r).factorial) := by ring
  have h1z : (((j + 1) * Nat.choose j r : ℕ) : ℤ) = (((j + 1 - r) * Nat.choose (j + 1) r : ℕ) : ℤ) :=
    congrArg (Nat.cast (R := ℤ)) hnat
  push_cast at h1z
  rw [Nat.cast_sub (by omega : r ≤ j + 1)] at h1z
  push_cast at h1z
  exact h1z

private lemma stirling2_mul_factorial_eq : ∀ n j : ℕ,
    (stirling2 n j : ℤ) * (j.factorial : ℤ) =
      ∑ r ∈ Finset.range (j + 1), (-1 : ℤ) ^ (j - r) * (Nat.choose j r : ℤ) * (r : ℤ) ^ n := by
  intro n
  induction n with
  | zero =>
    intro j
    cases j with
    | zero => simp [stirling2]
    | succ j =>
      simp only [stirling2, Nat.cast_zero, zero_mul, pow_zero, mul_one]
      have h := add_pow (1 : ℤ) (-1 : ℤ) (j + 1)
      simp only [add_neg_cancel, zero_pow (Nat.succ_ne_zero j)] at h
      symm
      rw [h]
      apply Finset.sum_congr rfl
      intro r _
      rw [one_pow, one_mul]
  | succ n ih =>
    intro j
    cases j with
    | zero => simp [stirling2]
    | succ j =>
      simp only [stirling2, Nat.cast_add, Nat.cast_mul, Nat.cast_succ]
      have hfac : ((j + 1).factorial : ℤ) = ((j : ℤ) + 1) * (j.factorial : ℤ) := by
        rw [Nat.factorial_succ]; push_cast; ring
      have hstep :
          (((j : ℤ) + 1) * (stirling2 n (j + 1) : ℤ) +
            (stirling2 n j : ℤ)) * ((j + 1).factorial : ℤ) =
          ((j : ℤ) + 1) * ((stirling2 n (j + 1) : ℤ) * ((j + 1).factorial : ℤ)) +
          ((j : ℤ) + 1) * ((stirling2 n j : ℤ) * (j.factorial : ℤ)) := by
        rw [hfac]; ring
      rw [hstep, ih (j + 1), ih j, Finset.mul_sum, Finset.mul_sum]
      rw [Finset.sum_range_succ (f := fun r => ((j : ℤ) + 1) * ((-1 : ℤ) ^ (j + 1 - r) * (Nat.choose (j + 1) r : ℤ) * (r : ℤ) ^ n))]
      rw [Finset.sum_range_succ (f := fun r => (-1 : ℤ) ^ (j + 1 - r) * (Nat.choose (j + 1) r : ℤ) * (r : ℤ) ^ (n + 1))]
      have hlast :
          ((j : ℤ) + 1) * ((-1 : ℤ) ^ (j + 1 - (j + 1)) * (Nat.choose (j + 1) (j + 1) : ℤ) * ((j + 1 : ℕ) : ℤ) ^ n) =
          (-1 : ℤ) ^ (j + 1 - (j + 1)) * (Nat.choose (j + 1) (j + 1) : ℤ) * ((j + 1 : ℕ) : ℤ) ^ (n + 1) := by
        simp [pow_succ]; ring
      rw [add_right_comm, ← Finset.sum_add_distrib, hlast]
      congr 1
      apply Finset.sum_congr rfl
      intro r hr
      simp only [Finset.mem_range] at hr
      have hpow : (-1 : ℤ) ^ (j + 1 - r) = -((-1 : ℤ) ^ (j - r)) := by
        have heq : j + 1 - r = (j - r) + 1 := by omega
        rw [heq, pow_succ]; ring
      have hch := mul_choose_eq_sub_mul_choose j r (by omega)
      rw [hpow, pow_succ]
      calc
        ((j : ℤ) + 1) * (-(-1 : ℤ) ^ (j - r) * (Nat.choose (j + 1) r : ℤ) * (r : ℤ) ^ n) +
            ((j : ℤ) + 1) * ((-1 : ℤ) ^ (j - r) * (Nat.choose j r : ℤ) * (r : ℤ) ^ n)
          = (-1 : ℤ) ^ (j - r) * (r : ℤ) ^ n *
              (((j : ℤ) + 1) * (Nat.choose j r : ℤ) - ((j : ℤ) + 1) * (Nat.choose (j + 1) r : ℤ)) := by
            ring
        _ = (-1 : ℤ) ^ (j - r) * (r : ℤ) ^ n *
              (((j : ℤ) + 1 - (r : ℤ)) * (Nat.choose (j + 1) r : ℤ) - ((j : ℤ) + 1) * (Nat.choose (j + 1) r : ℤ)) := by
            rw [hch]
        _ = -(-1 : ℤ) ^ (j - r) * (Nat.choose (j + 1) r : ℤ) * ((r : ℤ) ^ n * (r : ℤ)) := by
            ring

private lemma a_zmod_trunc (M K n : ℕ) (hK : ∀ k : ℕ, K ≤ k → M ∣ k.factorial) :
    (a n : ZMod M) =
      ∑ k ∈ Finset.range K,
        ∑ r ∈ Finset.range (k + 1),
          (-1 : ZMod M) ^ (k - r) * (Nat.choose k r : ZMod M) * (r : ZMod M) ^ (2 * n) := by
  have htr : (a n : ZMod M) = ∑ k ∈ Finset.range K, ((k.factorial * stirling2 (2 * n) k : ℕ) : ZMod M) := by
    unfold a
    push_cast
    by_cases hle : 2 * n + 1 ≤ K
    · have hsplit : Finset.range K = Finset.range (2 * n + 1) ∪ (Finset.range K \ Finset.range (2 * n + 1)) := by
        ext x; simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_range]; omega
      rw [hsplit, Finset.sum_union disjoint_sdiff_self_right]
      have htail : ∑ k ∈ Finset.range K \ Finset.range (2 * n + 1),
          ((k.factorial : ZMod M) * (stirling2 (2 * n) k : ZMod M)) = 0 := by
        apply Finset.sum_eq_zero
        intro k hk
        simp only [Finset.mem_sdiff, Finset.mem_range] at hk
        rw [stirling2_eq_zero_of_lt (2 * n) k (by omega), Nat.cast_zero, mul_zero]
      rw [htail, add_zero]
    · have hsplit : Finset.range (2 * n + 1) = Finset.range K ∪ (Finset.range (2 * n + 1) \ Finset.range K) := by
        ext x; simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_range]; omega
      rw [hsplit, Finset.sum_union disjoint_sdiff_self_right]
      have htail : ∑ k ∈ Finset.range (2 * n + 1) \ Finset.range K,
          ((k.factorial : ZMod M) * (stirling2 (2 * n) k : ZMod M)) = 0 := by
        apply Finset.sum_eq_zero
        intro k hk
        simp only [Finset.mem_sdiff, Finset.mem_range] at hk
        have h0 : (k.factorial : ZMod M) = 0 :=
          (ZMod.natCast_eq_zero_iff _ M).mpr (hK k (by omega))
        rw [h0, zero_mul]
      rw [htail, add_zero]
  rw [htr]
  apply Finset.sum_congr rfl
  intro k _
  have h := congrArg (Int.cast (R := ZMod M)) (stirling2_mul_factorial_eq (2 * n) k)
  push_cast at h ⊢
  rw [mul_comm, h]

private lemma a_mod_nine (n : ℕ) (hn : 1 ≤ n) : a n ≡ 3 [MOD 9] := by
  have hK : ∀ k : ℕ, 6 ≤ k → 9 ∣ k.factorial := by
    intro k hk
    exact dvd_trans (by decide : 9 ∣ (6 : ℕ).factorial) (Nat.factorial_dvd_factorial hk)
  have hper : ∀ m : ℕ, 1 ≤ m → (a (m + 3) : ZMod 9) = (a m : ZMod 9) := by
    intro m hm
    rw [a_zmod_trunc 9 6 (m + 3) hK, a_zmod_trunc 9 6 m hK]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro r _
    congr 1
    have hpow : ∀ x : ZMod 9, x ^ (2 * (m + 3)) = x ^ (2 * m) := by
      intro x
      have hx : x ^ 2 * x ^ 6 = x ^ 2 := by
        revert x; decide
      have hm2 : 2 * m = 2 + (2 * m - 2) := by omega
      calc x ^ (2 * (m + 3)) = x ^ (2 * m + 6) := by ring_nf
        _ = x ^ (2 + (2 * m - 2) + 6) := by rw [← hm2]
        _ = (x ^ 2 * x ^ 6) * x ^ (2 * m - 2) := by ring
        _ = x ^ 2 * x ^ (2 * m - 2) := by rw [hx]
        _ = x ^ (2 + (2 * m - 2)) := by rw [← pow_add]
        _ = x ^ (2 * m) := by rw [← hm2]
    exact hpow (r : ZMod 9)
  have hbase : ∀ m : ℕ, 1 ≤ m → m ≤ 3 → (a m : ZMod 9) = 3 := by
    intro m hm1 hm3
    rw [a_zmod_trunc 9 6 m hK]
    interval_cases m <;> decide
  rw [← ZMod.natCast_eq_natCast_iff]
  change (a n : ZMod 9) = 3
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hle : n ≤ 3
    · exact hbase n hn hle
    · have h1 := hper (n - 3) (by omega)
      have h2 : n - 3 + 3 = n := by omega
      rw [h2] at h1
      rw [h1]
      exact ih (n - 3) (by omega) (by omega)

private lemma a_mod_32 (n : ℕ) (hn : 2 ≤ n) : a n ≡ 11 [MOD 32] := by
  have hK : ∀ k : ℕ, 8 ≤ k → 32 ∣ k.factorial := by
    intro k hk
    exact dvd_trans (by decide : 32 ∣ (8 : ℕ).factorial) (Nat.factorial_dvd_factorial hk)
  have hper : ∀ m : ℕ, 3 ≤ m → (a (m + 4) : ZMod 32) = (a m : ZMod 32) := by
    intro m hm
    rw [a_zmod_trunc 32 8 (m + 4) hK, a_zmod_trunc 32 8 m hK]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro r _
    congr 1
    have hpow : ∀ x : ZMod 32, x ^ (2 * (m + 4)) = x ^ (2 * m) := by
      intro x
      have hx : x ^ 6 * x ^ 8 = x ^ 6 := by
        revert x; decide
      have hm6 : 2 * m = 6 + (2 * m - 6) := by omega
      calc x ^ (2 * (m + 4)) = x ^ (2 * m + 8) := by ring_nf
        _ = x ^ (6 + (2 * m - 6) + 8) := by rw [← hm6]
        _ = (x ^ 6 * x ^ 8) * x ^ (2 * m - 6) := by ring
        _ = x ^ 6 * x ^ (2 * m - 6) := by rw [hx]
        _ = x ^ (6 + (2 * m - 6)) := by rw [← pow_add]
        _ = x ^ (2 * m) := by rw [← hm6]
    exact hpow (r : ZMod 32)
  have hbase : ∀ m : ℕ, 2 ≤ m → m ≤ 6 → (a m : ZMod 32) = 11 := by
    intro m hm2 hm6
    rw [a_zmod_trunc 32 8 m hK]
    interval_cases m <;> decide
  rw [← ZMod.natCast_eq_natCast_iff]
  change (a n : ZMod 32) = 11
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hle : n ≤ 6
    · exact hbase n hn hle
    · have h1 := hper (n - 4) (by omega)
      have h2 : n - 4 + 4 = n := by omega
      rw [h2] at h1
      rw [h1]
      exact ih (n - 4) (by omega) (by omega)

private lemma a_mod_288 (n : ℕ) (hn : 2 ≤ n) : a n ≡ 75 [MOD 288] := by
  have h9 : a n ≡ 75 [MOD 9] := by
    calc a n ≡ 3 [MOD 9] := a_mod_nine n (by omega)
      _ ≡ 75 [MOD 9] := by decide
  have h32 : a n ≡ 75 [MOD 32] := by
    calc a n ≡ 11 [MOD 32] := a_mod_32 n hn
      _ ≡ 75 [MOD 32] := by decide
  have hcop : Nat.Coprime 9 32 := by decide
  have := (Nat.modEq_and_modEq_iff_modEq_mul hcop).mp ⟨h9, h32⟩
  simpa using this

private lemma part1 (m : ℕ) :
    (∀ n : ℕ, 1 < n → a (n + 1) ≡ a n [MOD m]) ↔ m ∣ 288 := by
  constructor
  · intro h
    have h23 : a 3 ≡ a 2 [MOD m] := h 2 (by omega)
    have h34 : a 4 ≡ a 3 [MOD m] := h 3 (by omega)
    have ha2 : a 2 = 75 := by decide
    have ha3 : a 3 = 4683 := by decide
    have ha4 : a 4 = 545835 := by decide
    rw [ha2, ha3] at h23
    rw [ha3, ha4] at h34
    have hd1 : m ∣ 4608 := by
      have := (Nat.modEq_iff_dvd' (by omega : 75 ≤ 4683)).mp h23.symm
      simpa using this
    have hd2 : m ∣ 541152 := by
      have := (Nat.modEq_iff_dvd' (by omega : 4683 ≤ 545835)).mp h34.symm
      simpa using this
    have hgcd := Nat.dvd_gcd hd1 hd2
    have hg : Nat.gcd 4608 541152 = 288 := by decide
    rwa [hg] at hgcd
  · intro hm n hn
    have h1 := a_mod_288 (n + 1) (by omega)
    have h2 := a_mod_288 n (by omega)
    exact (h1.trans h2.symm).of_dvd hm

private lemma numNonzeroQR_eq (p : ℕ) (hp : p.Prime) :
    numNonzeroQR p = if p = 2 then 1 else (p - 1) / 2 := by
  have : Fact p.Prime := ⟨hp⟩
  unfold numNonzeroQR
  by_cases hp2 : p = 2
  · subst hp2; decide
  · simp only [hp2, ↓reduceIte]
    set t := (p - 1) / 2
    have hp_odd : p % 2 = 1 := by
      have := hp.eq_two_or_odd; omega
    have h2t : 2 * t = p - 1 := by omega
    have heq : ((Finset.range p).image (fun x => x ^ 2 % p) \ {0}) =
        (Finset.Icc 1 t).image (fun r : ℕ => r ^ 2 % p) := by
      ext y
      simp only [Finset.mem_sdiff, Finset.mem_image, Finset.mem_range,
        Finset.mem_singleton, Finset.mem_Icc]
      constructor
      · rintro ⟨⟨x, hxp, rfl⟩, hne⟩
        have hx0 : x ≠ 0 := by
          intro h0; subst h0; simp at hne
        by_cases hle : x ≤ t
        · exact ⟨x, ⟨by omega, hle⟩, rfl⟩
        · refine ⟨p - x, ⟨by omega, by omega⟩, ?_⟩
          rw [← Nat.ModEq, ← ZMod.natCast_eq_natCast_iff]
          push_cast
          have hcast : ((p - x : ℕ) : ZMod p) = -(x : ZMod p) := by
            rw [Nat.cast_sub (by omega : x ≤ p), ZMod.natCast_self, zero_sub]
          rw [hcast, neg_sq]
      · rintro ⟨r, ⟨hr1, hrt⟩, rfl⟩
        refine ⟨⟨r, by omega, rfl⟩, ?_⟩
        intro h0
        have hd : p ∣ r ^ 2 := Nat.dvd_of_mod_eq_zero h0
        have hd' : p ∣ r := hp.dvd_of_dvd_pow hd
        have := Nat.le_of_dvd (by omega) hd'
        omega
    rw [heq, Finset.card_image_of_injOn]
    · simp
    · intro a ha b hb hab
      simp only [Finset.coe_Icc, Set.mem_Icc] at ha hb
      have habz : (a : ZMod p) ^ 2 = (b : ZMod p) ^ 2 := by
        have hmod : a ^ 2 ≡ b ^ 2 [MOD p] := hab
        have := (ZMod.natCast_eq_natCast_iff (a ^ 2) (b ^ 2) p).mpr hmod
        push_cast at this; exact this
      have hfac : ((a : ZMod p) - (b : ZMod p)) * ((a : ZMod p) + (b : ZMod p)) = 0 := by
        calc ((a : ZMod p) - (b : ZMod p)) * ((a : ZMod p) + (b : ZMod p))
            = (a : ZMod p) ^ 2 - (b : ZMod p) ^ 2 := by ring
          _ = 0 := sub_eq_zero.mpr habz
      rcases mul_eq_zero.mp hfac with h1 | h2
      · have heq' : (a : ZMod p) = (b : ZMod p) := sub_eq_zero.mp h1
        have hmod : a % p = b % p := (ZMod.natCast_eq_natCast_iff a b p).mp heq'
        rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hmod
        exact hmod
      · have hsum0 : ((a + b : ℕ) : ZMod p) = 0 := by push_cast; exact h2
        have hdvd := (ZMod.natCast_eq_zero_iff (a + b) p).mp hsum0
        have := Nat.le_of_dvd (by omega) hdvd
        omega

private lemma coeff_sum_eq_pow_two (p : ℕ) (hp : p.Prime) (_hp2 : p ≠ 2) :
    ∀ r : ℕ, 1 ≤ r → r < p →
      (∑ k ∈ Finset.Ico r p, (-1 : ZMod p) ^ (k - r) * (Nat.choose k r : ZMod p)) =
        (2 : ZMod p) ^ (p - 1 - r) := by
  have : Fact p.Prime := ⟨hp⟩
  intro r hr1 hrp
  -- Downward induction on `d = p - 1 - r`
  have hdown : ∀ d : ℕ, d ≤ p - 2 →
      (∑ k ∈ Finset.Ico (p - 1 - d) p,
        (-1 : ZMod p) ^ (k - (p - 1 - d)) * (Nat.choose k (p - 1 - d) : ZMod p)) =
        (2 : ZMod p) ^ d := by
    intro d
    induction d with
    | zero =>
      intro _
      have hIco : Finset.Ico (p - 1 - 0) p = {p - 1} := by
        ext x; simp only [Finset.mem_Ico, Finset.mem_singleton]; omega
      rw [hIco]
      simp
    | succ d ih =>
      intro hd
      set s := p - 1 - (d + 1)
      have hs1 : s + 1 = p - 1 - d := by omega
      have hsp : s + 1 < p := by omega
      have hstep :
          (∑ k ∈ Finset.Ico s p, (-1 : ZMod p) ^ (k - s) * (Nat.choose k s : ZMod p)) -
          2 * (∑ k ∈ Finset.Ico (s + 1) p, (-1 : ZMod p) ^ (k - (s + 1)) * (Nat.choose k (s + 1) : ZMod p)) =
          (-1 : ZMod p) ^ (p - 1 - s) * (Nat.choose p (s + 1) : ZMod p) := by
        have hIco1 : Finset.Ico s p = insert s (Finset.Ico (s + 1) p) := by
          ext x; simp only [Finset.mem_Ico, Finset.mem_insert]; omega
        rw [hIco1, Finset.sum_insert (by simp)]
        simp only [Nat.sub_self, pow_zero, Nat.choose_self, Nat.cast_one, mul_one]
        have hdiff :
            (∑ k ∈ Finset.Ico (s + 1) p, (-1 : ZMod p) ^ (k - s) * (Nat.choose k s : ZMod p)) -
            (∑ k ∈ Finset.Ico (s + 1) p, (-1 : ZMod p) ^ (k - (s + 1)) * (Nat.choose k (s + 1) : ZMod p)) =
            ∑ k ∈ Finset.Ico (s + 1) p, (-1 : ZMod p) ^ (k - s) * (Nat.choose (k + 1) (s + 1) : ZMod p) := by
          rw [← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro k hk
          rw [Finset.mem_Ico] at hk
          have hpow : (-1 : ZMod p) ^ (k - s) = -((-1 : ZMod p) ^ (k - (s + 1))) := by
            have heq : k - s = (k - (s + 1)) + 1 := by omega
            rw [heq, pow_succ]; ring
          rw [Nat.choose_succ_succ, Nat.cast_add, hpow]
          ring
        have hshift :
            1 + ∑ k ∈ Finset.Ico (s + 1) p, (-1 : ZMod p) ^ (k - s) * (Nat.choose (k + 1) (s + 1) : ZMod p) =
            (∑ m ∈ Finset.Ico (s + 1) p, (-1 : ZMod p) ^ (m - (s + 1)) * (Nat.choose m (s + 1) : ZMod p)) +
            (-1 : ZMod p) ^ (p - 1 - s) * (Nat.choose p (s + 1) : ZMod p) := by
          have hbij :
              ∑ k ∈ Finset.Ico (s + 1) p, (-1 : ZMod p) ^ (k - s) * (Nat.choose (k + 1) (s + 1) : ZMod p) =
              ∑ m ∈ Finset.Ico (s + 2) (p + 1), (-1 : ZMod p) ^ (m - (s + 1)) * (Nat.choose m (s + 1) : ZMod p) := by
            apply Finset.sum_bij (fun k _ => k + 1)
            · intro k hk; simp only [Finset.mem_Ico] at hk ⊢; omega
            · intro a _ b _ h; omega
            · intro m hm; simp only [Finset.mem_Ico] at hm; refine ⟨m - 1, ?_, by omega⟩
              simp only [Finset.mem_Ico]; omega
            · intro k hk; simp only [Finset.mem_Ico] at hk
              have : k + 1 - (s + 1) = k - s := by omega
              rw [this]
          rw [hbij]
          have hIco_ins : Finset.Ico (s + 1) (p + 1) = insert (s + 1) (Finset.Ico (s + 2) (p + 1)) := by
            ext x; simp only [Finset.mem_Ico, Finset.mem_insert]; omega
          have hIco_end : Finset.Ico (s + 1) (p + 1) = insert p (Finset.Ico (s + 1) p) := by
            ext x; simp only [Finset.mem_Ico, Finset.mem_insert]; omega
          have h1 :
              ∑ m ∈ Finset.Ico (s + 1) (p + 1), (-1 : ZMod p) ^ (m - (s + 1)) * (Nat.choose m (s + 1) : ZMod p) =
              1 + ∑ m ∈ Finset.Ico (s + 2) (p + 1), (-1 : ZMod p) ^ (m - (s + 1)) * (Nat.choose m (s + 1) : ZMod p) := by
            rw [hIco_ins, Finset.sum_insert (by simp)]
            simp
          have h2 :
              ∑ m ∈ Finset.Ico (s + 1) (p + 1), (-1 : ZMod p) ^ (m - (s + 1)) * (Nat.choose m (s + 1) : ZMod p) =
              (-1 : ZMod p) ^ (p - (s + 1)) * (Nat.choose p (s + 1) : ZMod p) +
              ∑ m ∈ Finset.Ico (s + 1) p, (-1 : ZMod p) ^ (m - (s + 1)) * (Nat.choose m (s + 1) : ZMod p) := by
            rw [hIco_end, Finset.sum_insert (by simp)]
          have hsub : p - (s + 1) = p - 1 - s := by omega
          rw [← h1, h2, hsub, add_comm]
        calc 1 + (∑ k ∈ Finset.Ico (s + 1) p, (-1 : ZMod p) ^ (k - s) * (Nat.choose k s : ZMod p)) -
              2 * (∑ k ∈ Finset.Ico (s + 1) p, (-1 : ZMod p) ^ (k - (s + 1)) * (Nat.choose k (s + 1) : ZMod p))
            = (1 + ((∑ k ∈ Finset.Ico (s + 1) p, (-1 : ZMod p) ^ (k - s) * (Nat.choose k s : ZMod p)) -
                (∑ k ∈ Finset.Ico (s + 1) p, (-1 : ZMod p) ^ (k - (s + 1)) * (Nat.choose k (s + 1) : ZMod p)))) -
              (∑ k ∈ Finset.Ico (s + 1) p, (-1 : ZMod p) ^ (k - (s + 1)) * (Nat.choose k (s + 1) : ZMod p)) := by
                ring
          _ = (1 + ∑ k ∈ Finset.Ico (s + 1) p, (-1 : ZMod p) ^ (k - s) * (Nat.choose (k + 1) (s + 1) : ZMod p)) -
              (∑ k ∈ Finset.Ico (s + 1) p, (-1 : ZMod p) ^ (k - (s + 1)) * (Nat.choose k (s + 1) : ZMod p)) := by
                rw [hdiff]
          _ = (-1 : ZMod p) ^ (p - 1 - s) * (Nat.choose p (s + 1) : ZMod p) := by
                rw [hshift]; ring
      have hch0 : (Nat.choose p (s + 1) : ZMod p) = 0 :=
        (ZMod.natCast_eq_zero_iff _ p).mpr (hp.dvd_choose_self (by omega) hsp)
      rw [hch0, mul_zero, sub_eq_zero] at hstep
      have hih := ih (by omega)
      rw [← hs1] at hih
      rw [hstep, hih, pow_succ, mul_comm]
  have hr_eq : p - 1 - (p - 1 - r) = r := by omega
  have h := hdown (p - 1 - r) (by omega)
  rwa [hr_eq] at h

private lemma a_zmod_prime_formula (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (n : ℕ) (hn : 1 ≤ n) :
    (a n : ZMod p) =
      ∑ r ∈ Finset.Icc 1 ((p - 1) / 2),
        ((2 : ZMod p) ^ (p - 1 - r) + (2 : ZMod p) ^ (r - 1)) * ((r : ZMod p) ^ 2) ^ n := by
  have : Fact p.Prime := ⟨hp⟩
  have hp_odd : p % 2 = 1 := by have := hp.eq_two_or_odd; omega
  have hK : ∀ k : ℕ, p ≤ k → p ∣ k.factorial := fun k hk => Nat.dvd_factorial hp.pos hk
  rw [a_zmod_trunc p p n hK]
  have hswap :
      ∑ k ∈ Finset.range p, ∑ r ∈ Finset.range (k + 1),
        (-1 : ZMod p) ^ (k - r) * (Nat.choose k r : ZMod p) * (r : ZMod p) ^ (2 * n) =
      ∑ r ∈ Finset.range p,
        (∑ k ∈ Finset.Ico r p, (-1 : ZMod p) ^ (k - r) * (Nat.choose k r : ZMod p)) * (r : ZMod p) ^ (2 * n) := by
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_sigma', Finset.sum_sigma']
    apply Finset.sum_bij (fun x _ => ⟨x.2, x.1⟩)
    · intro x hx; simp only [Finset.mem_sigma, Finset.mem_range, Finset.mem_Ico] at hx ⊢; omega
    · intro x _ y _ h; cases x; cases y; simp only [Sigma.mk.inj_iff, heq_eq_eq] at h; rcases h with ⟨rfl, rfl⟩; rfl
    · intro y hy; simp only [Finset.mem_sigma, Finset.mem_range, Finset.mem_Ico] at hy
      refine ⟨⟨y.2, y.1⟩, ?_, rfl⟩
      simp only [Finset.mem_sigma, Finset.mem_range]; omega
    · intro x _; rfl
  rw [hswap]
  have hp_sub : p = (p - 1) + 1 := by omega
  have h1 :
      ∑ r ∈ Finset.range p,
        (∑ k ∈ Finset.Ico r p, (-1 : ZMod p) ^ (k - r) * (Nat.choose k r : ZMod p)) * (r : ZMod p) ^ (2 * n) =
      ∑ r ∈ Finset.Icc 1 (p - 1), (2 : ZMod p) ^ (p - 1 - r) * (r : ZMod p) ^ (2 * n) := by
    rw [show Finset.range p = Finset.range ((p - 1) + 1) by rw [← hp_sub], Finset.sum_range_succ']
    simp only [Nat.cast_zero, zero_pow (by omega : 2 * n ≠ 0), mul_zero, add_zero]
    apply Finset.sum_bij (fun r _ => r + 1)
    · intro r hr; simp only [Finset.mem_range, Finset.mem_Icc] at hr ⊢; omega
    · intro a _ b _ h; omega
    · intro r hr; simp only [Finset.mem_Icc] at hr
      refine ⟨r - 1, Finset.mem_range.mpr (by omega), by omega⟩
    · intro r hr
      simp only [Finset.mem_range] at hr
      rw [coeff_sum_eq_pow_two p hp hp2 (r + 1) (by omega) (by omega)]
  rw [h1]
  set t := (p - 1) / 2
  have h2t : 2 * t = p - 1 := by omega
  have hsplit : Finset.Icc 1 (p - 1) = Finset.Icc 1 t ∪ Finset.Icc (t + 1) (p - 1) := by
    ext r; simp only [Finset.mem_Icc, Finset.mem_union]; omega
  have hdisj : Disjoint (Finset.Icc 1 t) (Finset.Icc (t + 1) (p - 1)) := by
    rw [Finset.disjoint_left]
    intro r hr1 hr2
    simp only [Finset.mem_Icc] at hr1 hr2; omega
  rw [hsplit, Finset.sum_union hdisj]
  have hpair :
      ∑ r ∈ Finset.Icc (t + 1) (p - 1), (2 : ZMod p) ^ (p - 1 - r) * (r : ZMod p) ^ (2 * n) =
      ∑ r ∈ Finset.Icc 1 t, (2 : ZMod p) ^ (r - 1) * (r : ZMod p) ^ (2 * n) := by
    apply Finset.sum_bij (fun r _ => p - r)
    · intro r hr; simp only [Finset.mem_Icc] at hr ⊢; omega
    · intro a ha b hb hab; simp only [Finset.mem_Icc] at ha hb; omega
    · intro r hr; simp only [Finset.mem_Icc] at hr
      refine ⟨p - r, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩
    · intro r hr
      simp only [Finset.mem_Icc] at hr
      have hsub1 : p - 1 - r = p - r - 1 := by omega
      have hcast : ((p - r : ℕ) : ZMod p) = -(r : ZMod p) := by
        rw [Nat.cast_sub (by omega : r ≤ p), ZMod.natCast_self, zero_sub]
      rw [hsub1, hcast, pow_mul, pow_mul, neg_sq]
  rw [hpair, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r _
  rw [pow_mul]
  ring

private lemma period_gcd_aux (p : ℕ) (a_fn : ℕ → ZMod p) :
    ∀ s d1 d2 : ℕ, d1 + d2 ≤ s → 1 ≤ d1 → 1 ≤ d2 →
      (∀ n : ℕ, 1 ≤ n → a_fn (n + d1) = a_fn n) →
      (∀ n : ℕ, 1 ≤ n → a_fn (n + d2) = a_fn n) →
      ∀ n : ℕ, 1 ≤ n → a_fn (n + Nat.gcd d1 d2) = a_fn n := by
  intro s
  induction s with
  | zero => intro d1 d2 hs h1 _; omega
  | succ s ih =>
    intro d1 d2 hs h1 h2 hp1 hp2
    by_cases heq : d1 = d2
    · subst heq; simpa using hp1
    · by_cases hlt : d1 < d2
      · have hdiff : ∀ n : ℕ, 1 ≤ n → a_fn (n + (d2 - d1)) = a_fn n := by
          intro n hn
          have hA := hp1 (n + (d2 - d1)) (by omega)
          have hB := hp2 n hn
          have hadd : n + (d2 - d1) + d1 = n + d2 := by omega
          rw [hadd, hB] at hA
          exact hA.symm
        have hgcd : Nat.gcd d1 d2 = Nat.gcd d1 (d2 - d1) := by
          have : d2 = (d2 - d1) + d1 := by omega
          conv_lhs => rw [this]
          exact Nat.gcd_add_self_right d1 (d2 - d1)
        rw [hgcd]
        exact ih d1 (d2 - d1) (by omega) h1 (by omega) hp1 hdiff
      · have hdiff : ∀ n : ℕ, 1 ≤ n → a_fn (n + (d1 - d2)) = a_fn n := by
          intro n hn
          have hA := hp2 (n + (d1 - d2)) (by omega)
          have hB := hp1 n hn
          have hadd : n + (d1 - d2) + d2 = n + d1 := by omega
          rw [hadd, hB] at hA
          exact hA.symm
        have hgcd : Nat.gcd d1 d2 = Nat.gcd (d1 - d2) d2 := by
          have : d1 = (d1 - d2) + d2 := by omega
          conv_lhs => rw [this]
          rw [Nat.gcd_comm, Nat.gcd_add_self_right, Nat.gcd_comm]
        rw [hgcd]
        exact ih (d1 - d2) d2 (by omega) (by omega) h2 hdiff hp2

private lemma card_le_of_gap_three {t : ℕ} (S : Finset (Fin t))
    (hgap : ∀ a ∈ S, ∀ b ∈ S, a.1 < b.1 → a.1 + 3 ≤ b.1) :
    3 * S.card ≤ t + 2 := by
  let f : Fin t × Fin 3 → ℕ := fun p => p.1.1 + p.2.1
  have himg : (S ×ˢ (Finset.univ : Finset (Fin 3))).image f ⊆ Finset.range (t + 2) := by
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨p, _, rfl⟩
    rw [Finset.mem_range]
    simp only [f]
    have h1 := p.1.2
    have h2 := p.2.2
    omega
  have hinj : Set.InjOn f ↑(S ×ˢ (Finset.univ : Finset (Fin 3))) := by
    intro p hp q hq hpq
    simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_univ, and_true] at hp hq
    simp only [f] at hpq
    have hp2 := p.2.2
    have hq2 := q.2.2
    have h1eq : p.1 = q.1 := by
      rcases lt_trichotomy p.1.1 q.1.1 with hlt | heq | hgt
      · have := hgap p.1 hp q.1 hq hlt; omega
      · exact Fin.ext heq
      · have := hgap q.1 hq p.1 hp hgt; omega
    have h2eq : p.2 = q.2 := Fin.ext (by rw [h1eq] at hpq; omega)
    exact Prod.ext h1eq h2eq
  have hcard := Finset.card_le_card himg
  rw [Finset.card_image_of_injOn hinj, Finset.card_product, Finset.card_univ, Fintype.card_fin,
    Finset.card_range] at hcard
  linarith

private lemma zmod5_2_pow1_ne : (2 : ZMod 5) ^ (2 * 0 + 1) ≠ -1 := by decide
private lemma zmod5_2_pow3_ne : (2 : ZMod 5) ^ (2 * 1 + 1) ≠ -1 := by decide
private lemma zmod7_2_pow1_ne : (2 : ZMod 7) ^ (2 * 0 + 1) ≠ -1 := by decide
private lemma zmod7_2_pow3_ne : (2 : ZMod 7) ^ (2 * 1 + 1) ≠ -1 := by decide
private lemma zmod7_2_pow5_ne : (2 : ZMod 7) ^ (2 * 2 + 1) ≠ -1 := by decide

private lemma part2_odd_ge_five (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) :
    let t := (p - 1) / 2
    (∀ n : ℕ, 1 ≤ n → a (n + t) ≡ a n [MOD p]) ∧
    (∀ d : ℕ, 1 ≤ d → (∀ n : ℕ, 1 ≤ n → a (n + d) ≡ a n [MOD p]) → t ∣ d) := by
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  have hp_odd : p % 2 = 1 := by have := hp.eq_two_or_odd; omega
  intro t
  have h2t : 2 * t = p - 1 := by omega
  have htpos : 1 ≤ t := by omega
  have hper_t : ∀ n : ℕ, 1 ≤ n → a (n + t) ≡ a n [MOD p] := by
    intro n hn
    rw [← ZMod.natCast_eq_natCast_iff]
    rw [a_zmod_prime_formula p hp hp2 (n + t) (by omega),
      a_zmod_prime_formula p hp hp2 n hn]
    apply Finset.sum_congr rfl
    intro r hr
    rw [Finset.mem_Icc] at hr
    congr 1
    have hr0 : (r : ZMod p) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      intro hd; have := Nat.le_of_dvd (by omega) hd; omega
    rw [pow_add, ← pow_mul, ← pow_mul, h2t, ZMod.pow_card_sub_one_eq_one hr0, mul_one]
  refine ⟨hper_t, ?_⟩
  intro d hd hper_d
  set g := Nat.gcd d t
  have hg1 : 1 ≤ g := Nat.gcd_pos_of_pos_left t (by omega)
  have hgt : g ∣ t := Nat.gcd_dvd_right d t
  have hgd : g ∣ d := Nat.gcd_dvd_left d t
  have hper_g : ∀ n : ℕ, 1 ≤ n → (a (n + g) : ZMod p) = (a n : ZMod p) := by
    exact period_gcd_aux p (fun n => (a n : ZMod p)) (d + t) d t (le_refl _) hd htpos
      (fun n hn => (ZMod.natCast_eq_natCast_iff _ _ p).mpr (hper_d n hn))
      (fun n hn => (ZMod.natCast_eq_natCast_iff _ _ p).mpr (hper_t n hn))
  by_contra hnot
  have hglt : g < t := by
    have hle := Nat.le_of_dvd htpos hgt
    rcases lt_or_eq_of_le hle with hlt | heq
    · exact hlt
    · exact absurd (heq ▸ hgd) hnot
  have h2g : 2 * g ≤ t := by
    rcases hgt with ⟨q, hq⟩
    have hq2 : 2 ≤ q := by nlinarith
    nlinarith
  -- Vandermonde system on x_j = ((j + 1 : ZMod p)^2) for j : Fin t
  let x : Fin t → ZMod p := fun j => ((j.1 + 1 : ℕ) : ZMod p) ^ 2
  let c : Fin t → ZMod p := fun j => (2 : ZMod p) ^ (p - 1 - (j.1 + 1)) + (2 : ZMod p) ^ j.1
  let v : Fin t → ZMod p := fun j => c j * (x j ^ g - 1) * x j
  have hx_inj : Function.Injective x := by
    intro j1 j2 h12
    have hfac : (((j1.1 + 1 : ℕ) : ZMod p) - ((j2.1 + 1 : ℕ) : ZMod p)) *
        (((j1.1 + 1 : ℕ) : ZMod p) + ((j2.1 + 1 : ℕ) : ZMod p)) = 0 := by
      calc (((j1.1 + 1 : ℕ) : ZMod p) - ((j2.1 + 1 : ℕ) : ZMod p)) *
            (((j1.1 + 1 : ℕ) : ZMod p) + ((j2.1 + 1 : ℕ) : ZMod p))
          = x j1 - x j2 := by simp [x]; ring
        _ = 0 := sub_eq_zero.mpr h12
    rcases mul_eq_zero.mp hfac with h1 | h2
    · have heq' : ((j1.1 + 1 : ℕ) : ZMod p) = ((j2.1 + 1 : ℕ) : ZMod p) := sub_eq_zero.mp h1
      have hmod := (ZMod.natCast_eq_natCast_iff (j1.1 + 1) (j2.1 + 1) p).mp heq'
      have hlt1 : j1.1 + 1 < p := by have := j1.2; omega
      have hlt2 : j2.1 + 1 < p := by have := j2.2; omega
      rw [Nat.ModEq, Nat.mod_eq_of_lt hlt1, Nat.mod_eq_of_lt hlt2] at hmod
      exact Fin.ext (by omega)
    · have hsum0 : ((j1.1 + 1 + (j2.1 + 1) : ℕ) : ZMod p) = 0 := by rw [Nat.cast_add]; exact h2
      have hdvd := (ZMod.natCast_eq_zero_iff _ p).mp hsum0
      have hle := Nat.le_of_dvd (by omega) hdvd
      have := j1.2; have := j2.2; omega
  have hmulVec : (Matrix.vandermonde x).transpose.mulVec v = 0 := by
    ext i
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Matrix.vandermonde_apply,
      Pi.zero_apply]
    have hsum : ∑ j : Fin t, x j ^ i.1 * v j =
        (a (i.1 + 1 + g) : ZMod p) - (a (i.1 + 1) : ZMod p) := by
      rw [a_zmod_prime_formula p hp hp2 (i.1 + 1 + g) (by omega),
        a_zmod_prime_formula p hp hp2 (i.1 + 1) (by omega), ← Finset.sum_sub_distrib]
      symm
      apply Finset.sum_bij (fun r hr => ⟨r - 1, by rw [Finset.mem_Icc] at hr; omega⟩)
      · intro r _; exact Finset.mem_univ _
      · intro r1 hr1 r2 hr2 h
        rw [Finset.mem_Icc] at hr1 hr2
        have := congrArg Fin.val h; dsimp at this; omega
      · intro j _
        refine ⟨j.1 + 1, Finset.mem_Icc.mpr ⟨by omega, by have := j.2; omega⟩, ?_⟩
        exact Fin.ext (by simp)
      · intro r hr
        rw [Finset.mem_Icc] at hr
        have hsub : r - 1 + 1 = r := by omega
        simp only [x, c, v, hsub]
        rw [pow_add, pow_succ, pow_succ]
        ring
    rw [hsum, hper_g (i.1 + 1) (by omega), sub_self]
  have hdet_ne : (Matrix.vandermonde x).transpose.det ≠ 0 := by
    rw [Matrix.det_transpose, Matrix.det_vandermonde]
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    apply Finset.prod_ne_zero_iff.mpr
    intro j hj
    rw [Finset.mem_Ioi] at hj
    exact sub_ne_zero.mpr (fun h => ne_of_gt hj (hx_inj h))
  have hv0 : v = 0 := by
    let M := (Matrix.vandermonde x).transpose
    have hadj := Matrix.adjugate_mul M
    have hmv : (M.adjugate * M).mulVec v = 0 := by
      rw [← Matrix.mulVec_mulVec, hmulVec, Matrix.mulVec_zero]
    rw [hadj, Matrix.smul_mulVec, Matrix.one_mulVec] at hmv
    ext j
    have hj := congrFun hmv j
    simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hj
    exact (mul_eq_zero.mp hj).resolve_left hdet_ne
  have hzero_each : ∀ j : Fin t, x j ^ g = 1 ∨ c j = 0 := by
    intro j
    have hvj : c j * (x j ^ g - 1) * x j = 0 := congrFun hv0 j
    have hxj0 : x j ≠ 0 := by
      apply pow_ne_zero 2
      rw [Ne, ZMod.natCast_eq_zero_iff]
      intro hd; have := Nat.le_of_dvd (by omega) hd; have := j.2; omega
    rcases mul_eq_zero.mp hvj with h1 | h2
    · rcases mul_eq_zero.mp h1 with hc | hxg
      · exact Or.inr hc
      · exact Or.inl (sub_eq_zero.mp hxg)
    · exact absurd h2 hxj0
  -- Partition Fin t into A = {j | x j ^ g = 1} and B = {j | c j = 0}
  let A : Finset (Fin t) := Finset.univ.filter (fun j => x j ^ g = 1)
  let B : Finset (Fin t) := Finset.univ.filter (fun j => c j = 0)
  have hcover : t ≤ A.card + B.card := by
    have hsub : (Finset.univ : Finset (Fin t)) ⊆ A ∪ B := by
      intro j _
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, A, B]
      exact hzero_each j
    calc t = (Finset.univ : Finset (Fin t)).card := by simp
      _ ≤ (A ∪ B).card := Finset.card_le_card hsub
      _ ≤ A.card + B.card := Finset.card_union_le A B
  have hA_le : A.card ≤ g := by
    let P : Polynomial (ZMod p) := Polynomial.X ^ g - 1
    have hPne : P ≠ 0 := by
      intro h0
      have := congrArg (fun q : Polynomial (ZMod p) => q.coeff g) h0
      simp [P, Polynomial.coeff_X_pow, Polynomial.coeff_one, show g ≠ 0 by omega] at this
    have himg : A.image x ⊆ P.roots.toFinset := by
      intro y hy
      rcases Finset.mem_image.mp hy with ⟨j, hj, rfl⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, A] at hj
      rw [Multiset.mem_toFinset, Polynomial.mem_roots hPne, Polynomial.IsRoot.def]
      simp [P, hj]
    calc A.card = (A.image x).card := (Finset.card_image_of_injective A hx_inj).symm
      _ ≤ P.roots.toFinset.card := Finset.card_le_card himg
      _ ≤ P.roots.card := Multiset.toFinset_card_le _
      _ ≤ P.natDegree := Polynomial.card_roots' P
      _ ≤ g := by
        calc (Polynomial.X ^ g - (1 : Polynomial (ZMod p))).natDegree
            ≤ max (Polynomial.X ^ g : Polynomial (ZMod p)).natDegree (1 : Polynomial (ZMod p)).natDegree :=
              Polynomial.natDegree_sub_le _ _
          _ ≤ g := by simp
  -- Every j ∈ B satisfies (2 : ZMod p)^(2*j + 1) = -1
  have h2ne : (2 : ZMod p) ≠ 0 := by
    change ((2 : ℕ) : ZMod p) ≠ 0
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro hd; have := Nat.le_of_dvd (by omega) hd; omega
  have hB_pow : ∀ j ∈ B, (2 : ZMod p) ^ (2 * j.1 + 1) = -1 := by
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, B, c] at hj
    have hmul : (2 : ZMod p) ^ (j.1 + 1) * ((2 : ZMod p) ^ (p - 1 - (j.1 + 1)) + (2 : ZMod p) ^ j.1) = 0 := by
      rw [hj, mul_zero]
    rw [mul_add, ← pow_add, ← pow_add] at hmul
    have he1 : j.1 + 1 + (p - 1 - (j.1 + 1)) = p - 1 := by have := j.2; omega
    have he2 : j.1 + 1 + j.1 = 2 * j.1 + 1 := by omega
    rw [he1, he2, ZMod.pow_card_sub_one_eq_one h2ne] at hmul
    exact eq_neg_of_add_eq_zero_right hmul
  by_cases hp11 : 11 ≤ p
  · have hgap : ∀ a ∈ B, ∀ b ∈ B, a.1 < b.1 → a.1 + 3 ≤ b.1 := by
      intro a ha b hb hab
      have hpa := hB_pow a ha
      have hpb := hB_pow b hb
      have hpow_eq : (2 : ZMod p) ^ (2 * (b.1 - a.1)) = 1 := by
        have hmul : (2 : ZMod p) ^ (2 * a.1 + 1) * (2 : ZMod p) ^ (2 * (b.1 - a.1)) =
            (2 : ZMod p) ^ (2 * b.1 + 1) := by
          rw [← pow_add]; congr 1; omega
        rw [hpa, hpb] at hmul
        have hneg : (-1 : ZMod p) * (2 : ZMod p) ^ (2 * (b.1 - a.1)) = (-1 : ZMod p) * 1 := by
          simpa using hmul
        exact mul_left_cancel₀ (by norm_num : (-1 : ZMod p) ≠ 0) hneg
      by_contra hlt3
      have hcase : b.1 - a.1 = 1 ∨ b.1 - a.1 = 2 := by omega
      rcases hcase with h1 | h2
      · rw [h1] at hpow_eq
        have h3 : ((3 : ℕ) : ZMod p) = 0 := by
          have : (2 : ZMod p) ^ 2 - 1 = 0 := sub_eq_zero.mpr (by simpa using hpow_eq)
          convert this using 1; norm_num
        have hd := (ZMod.natCast_eq_zero_iff 3 p).mp h3
        have := Nat.le_of_dvd (by omega) hd; omega
      · rw [h2] at hpow_eq
        have h15 : ((15 : ℕ) : ZMod p) = 0 := by
          have : (2 : ZMod p) ^ 4 - 1 = 0 := sub_eq_zero.mpr (by simpa using hpow_eq)
          convert this using 1; norm_num
        have hd := (ZMod.natCast_eq_zero_iff 15 p).mp h15
        have := Nat.le_of_dvd (by omega) hd
        -- p divides 15 and p >= 11, prime => impossible (only 3, 5 divide 15)
        have hle15 : p ≤ 15 := this
        have hp_cases : p = 11 ∨ p = 12 ∨ p = 13 ∨ p = 14 ∨ p = 15 := by omega
        rcases hp_cases with h | h | h | h | h <;> (rw [h] at hp hd; revert hp hd; decide)
    have hB3 := card_le_of_gap_three B hgap
    have ht5 : 5 ≤ t := by omega
    omega
  · -- Small primes 5 <= p < 11, i.e., p = 5 or p = 7
    have hp57 : p = 5 ∨ p = 7 := by
      have h6 : p = 5 ∨ p = 6 ∨ p = 7 ∨ p = 8 ∨ p = 9 ∨ p = 10 := by omega
      rcases h6 with h | h | h | h | h | h
      · exact Or.inl h
      · rw [h] at hp; exact absurd hp (by decide)
      · exact Or.inr h
      · rw [h] at hp; exact absurd hp (by decide)
      · rw [h] at hp; exact absurd hp (by decide)
      · rw [h] at hp; exact absurd hp (by decide)
    rcases hp57 with rfl | rfl
    · have hB0 : B.card = 0 := by
        rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
        intro j hj
        have hjp := hB_pow j hj
        have hjlt : j.1 < 2 := j.2
        have hjc : j.1 = 0 ∨ j.1 = 1 := by omega
        rcases hjc with hv | hv
        · rw [hv] at hjp; exact zmod5_2_pow1_ne hjp
        · rw [hv] at hjp; exact zmod5_2_pow3_ne hjp
      omega
    · have hB0 : B.card = 0 := by
        rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
        intro j hj
        have hjp := hB_pow j hj
        have hjlt : j.1 < 3 := j.2
        have hjc : j.1 = 0 ∨ j.1 = 1 ∨ j.1 = 2 := by omega
        rcases hjc with hv | hv | hv
        · rw [hv] at hjp; exact zmod7_2_pow1_ne hjp
        · rw [hv] at hjp; exact zmod7_2_pow3_ne hjp
        · rw [hv] at hjp; exact zmod7_2_pow5_ne hjp
      omega

end OeisA249938Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a249938.main := by
  refine ⟨OeisA249938Proof.part1, ?_⟩
  intro p hp
  rw [OeisA249938Proof.numNonzeroQR_eq p hp]
  by_cases hp2 : p = 2
  · subst hp2
    simp only [↓reduceIte]
    refine ⟨?_, fun d _ _ => one_dvd d⟩
    intro n hn
    have h1 := OeisA249938Proof.a_mod_32 (n + 1) (by omega)
    have h2 : OMA.S_oeis_a249938.a n ≡ 11 [MOD 2] := by
      by_cases hn1 : n = 1
      · subst hn1; decide
      · exact (OeisA249938Proof.a_mod_32 n (by omega)).of_dvd (by decide : 2 ∣ 32)
    exact (h1.of_dvd (by decide : 2 ∣ 32)).trans h2.symm
  · simp only [hp2, ↓reduceIte]
    by_cases hp3 : p = 3
    · subst hp3
      rw [show (3 - 1) / 2 = 1 from rfl]
      refine ⟨?_, fun d _ _ => one_dvd d⟩
      intro n hn
      have h1 := (OeisA249938Proof.a_mod_nine (n + 1) (by omega)).of_dvd (by decide : 3 ∣ 9)
      have h2 := (OeisA249938Proof.a_mod_nine n hn).of_dvd (by decide : 3 ∣ 9)
      exact h1.trans h2.symm
    · have hp5 : 5 ≤ p := by
        have := hp.two_le
        have hodd := hp.eq_two_or_odd
        omega
      exact OeisA249938Proof.part2_odd_ge_five p hp hp5
