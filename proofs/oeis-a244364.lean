import OMAStatements.S_oeis_a244364
import Mathlib

namespace OMA.P_oeis_a244364

open OMA.S_oeis_a244364

private def repunit (n : ℕ) : ℕ := (10 ^ n - 1) / 9

private lemma nine_mul_repunit (n : ℕ) : 9 * repunit n + 1 = 10 ^ n := by
  unfold repunit
  have h1 : 1 ≤ 10 ^ n := Nat.one_le_pow n 10 (by omega)
  have h9 : 9 ∣ 10 ^ n - 1 := by
    have hmod : 10 ^ n % 9 = 1 := by
      have : (10 : ℕ) ≡ 1 [MOD 9] := by decide
      have hp := this.pow n
      simpa [Nat.ModEq] using hp
    omega
  have := Nat.mul_div_cancel' h9
  omega

private lemma repunit_ge_ten_pow (n : ℕ) (hn : 1 ≤ n) : 10 ^ (n - 1) ≤ repunit n := by
  have h9 := nine_mul_repunit n
  have hpow : 10 ^ n = 10 * 10 ^ (n - 1) := by
    cases n with
    | zero => omega
    | succ k => simp [pow_succ']
  omega

private lemma repunit_mod_of_dvd_ten_pow (n M0 r0 : ℕ) (hdvd : M0 ∣ 10 ^ n)
    (hcop9 : Nat.Coprime 9 M0) (hr0lt : r0 < M0) (h9r0 : (9 * r0 + 1) % M0 = 0) :
    repunit n % M0 = r0 := by
  have h9eq : 9 * repunit n + 1 ≡ 9 * r0 + 1 [MOD M0] := by
    rw [Nat.ModEq, nine_mul_repunit, Nat.mod_eq_zero_of_dvd hdvd, h9r0]
  have h9eq' : 9 * repunit n ≡ 9 * r0 [MOD M0] := Nat.ModEq.add_right_cancel' 1 h9eq
  have heq : repunit n ≡ r0 [MOD M0] := h9eq'.cancel_left_of_coprime hcop9.symm
  rw [Nat.ModEq, Nat.mod_eq_of_lt hr0lt] at heq
  exact heq

/-! ### Elementary 2-adic and 5-adic Lifting Lemmas -/

private lemma odd_pow_add_one_factor (m k : ℕ) (hk : Odd k) :
    ∃ S : ℤ, Odd S ∧ (m : ℤ) ^ k + 1 = ((m : ℤ) + 1) * S := by
  rcases hk with ⟨t, rfl⟩
  induction t with
  | zero =>
    exact ⟨1, ⟨0, rfl⟩, by ring⟩
  | succ t ih =>
    obtain ⟨S, ⟨u, rfl⟩, hS⟩ := ih
    refine ⟨(m : ℤ) ^ (2 * t + 2) - (m : ℤ) ^ (2 * t + 1) + (2 * u + 1), ?_, ?_⟩
    · have hev : Even ((m : ℤ) ^ (2 * t + 2) - (m : ℤ) ^ (2 * t + 1)) := by
        have hfac : (m : ℤ) ^ (2 * t + 2) - (m : ℤ) ^ (2 * t + 1) =
            (m : ℤ) ^ (2 * t + 1) * ((m : ℤ) - 1) := by
          rw [show 2 * t + 2 = (2 * t + 1) + 1 by omega, pow_succ]; ring
        rw [hfac]
        rcases Int.even_or_odd (m : ℤ) with hm | hm
        · exact Even.mul_right (hm.pow_of_ne_zero (by omega)) _
        · rcases hm with ⟨v, hv⟩
          exact Even.mul_left ⟨v, by omega⟩ _
      rcases hev with ⟨w, hw⟩
      exact ⟨w + u, by omega⟩
    · have hpow : (m : ℤ) ^ (2 * (t + 1) + 1) = (m : ℤ) ^ (2 * t + 1) * (m : ℤ) ^ 2 := by
        rw [show 2 * (t + 1) + 1 = (2 * t + 1) + 2 by omega, pow_add]
      have hpow2 : (m : ℤ) ^ (2 * t + 2) = (m : ℤ) ^ (2 * t + 1) * (m : ℤ) := by
        rw [show 2 * t + 2 = (2 * t + 1) + 1 by omega, pow_succ]
      rw [hpow]
      rw [hpow2]; linear_combination hS

private lemma odd_pow_sub_one_factor (m k : ℕ) (hk : Odd k) (hm : Odd m) :
    ∃ S : ℕ, Odd S ∧ m ^ k - 1 = (m - 1) * S := by
  have hm1 : 1 ≤ m := by rcases hm with ⟨v, rfl⟩; omega
  have hmk1 : 1 ≤ m ^ k := Nat.one_le_pow k m (by omega)
  have hsum : (m - 1) * (∑ i ∈ Finset.range k, m ^ i) = m ^ k - 1 := by
    zify [hm1, hmk1]
    rw [mul_comm]
    exact geom_sum_mul (m : ℤ) k
  refine ⟨∑ i ∈ Finset.range k, m ^ i, ?_, hsum.symm⟩
  have hmod : ∀ t : ℕ, (∑ i ∈ Finset.range t, m ^ i) % 2 = t % 2 := by
    intro t
    induction t with
    | zero => simp
    | succ j ih =>
      rw [Finset.sum_range_succ, Nat.add_mod, ih]
      have hpow_odd : m ^ j % 2 = 1 := by
        rcases hm with ⟨v, rfl⟩
        have : (2 * v + 1) ≡ 1 [MOD 2] := by
          show (2 * v + 1) % 2 = 1 % 2; omega
        simpa [Nat.ModEq] using this.pow j
      omega
  have hmodk := hmod k
  rw [Nat.odd_iff] at hk ⊢
  omega

private lemma two_pow_dvd_pow_add_one_iff (m k e : ℕ) (hk : Odd k) :
    2 ^ e ∣ m ^ k + 1 ↔ 2 ^ e ∣ m + 1 := by
  obtain ⟨S, hSodd, hfac⟩ := odd_pow_add_one_factor m k hk
  have hcop : IsCoprime ((2 : ℤ) ^ e) S := by
    have hcop2 : IsCoprime (2 : ℤ) S := by
      rcases hSodd with ⟨u, rfl⟩
      exact ⟨-u, 1, by ring⟩
    exact hcop2.pow_left
  constructor
  · intro h
    have hz : ((2 : ℤ) ^ e) ∣ (m : ℤ) ^ k + 1 := by exact_mod_cast h
    rw [hfac] at hz
    have hd : ((2 : ℤ) ^ e) ∣ (m : ℤ) + 1 := hcop.dvd_of_dvd_mul_right hz
    exact_mod_cast hd
  · intro h
    have hz : ((2 : ℤ) ^ e) ∣ (m : ℤ) + 1 := by exact_mod_cast h
    have hd : ((2 : ℤ) ^ e) ∣ (m : ℤ) ^ k + 1 := by
      rw [hfac]; exact dvd_mul_of_dvd_left hz S
    exact_mod_cast hd

private lemma two_pow_dvd_pow_sub_one_iff (m k e : ℕ) (hk : Odd k) (hm : Odd m) :
    2 ^ e ∣ m ^ k - 1 ↔ 2 ^ e ∣ m - 1 := by
  obtain ⟨S, hSodd, hfac⟩ := odd_pow_sub_one_factor m k hk hm
  have hcop : Nat.Coprime (2 ^ e) S := by
    apply Nat.Coprime.pow_left
    rw [Nat.coprime_two_left]
    exact hSodd
  rw [hfac]
  exact ⟨fun h => hcop.dvd_of_dvd_mul_right h, fun h => dvd_mul_of_dvd_left h S⟩

/-- If `5 ∣ m + 1`, then `5 ^ (d + 1) ∣ m ^ (5 ^ d) + 1`. -/
private lemma five_pow_dvd_pow_five_pow_add_one (m d : ℕ) (h5 : 5 ∣ m + 1) :
    5 ^ (d + 1) ∣ m ^ (5 ^ d) + 1 := by
  induction d with
  | zero => simpa using h5
  | succ d ih =>
    obtain ⟨c, hc⟩ := ih
    have hpow : m ^ (5 ^ (d + 1)) = (m ^ (5 ^ d)) ^ 5 := by
      rw [← pow_mul, pow_succ]
    have hz : ((5 : ℤ) ^ (d + 1 + 1)) ∣ ((m : ℤ) ^ (5 ^ (d + 1))) + 1 := by
      rw [show (m : ℤ) ^ (5 ^ (d + 1)) = ((m : ℤ) ^ (5 ^ d)) ^ 5 by exact_mod_cast hpow]
      have hcz : (m : ℤ) ^ (5 ^ d) = (5 : ℤ) ^ (d + 1) * (c : ℤ) - 1 := by
        have : ((m ^ (5 ^ d) + 1 : ℕ) : ℤ) = ((5 ^ (d + 1) * c : ℕ) : ℤ) := by exact_mod_cast hc
        push_cast at this; linarith
      rw [hcz]
      refine ⟨(c : ℤ) - 2 * (5 : ℤ) ^ (d + 1) * (c : ℤ) ^ 2 + 2 * (5 : ℤ) ^ (2 * d + 2) * (c : ℤ) ^ 3
        - (5 : ℤ) ^ (3 * d + 3) * (c : ℤ) ^ 4 + (5 : ℤ) ^ (4 * d + 3) * (c : ℤ) ^ 5, ?_⟩
      have h1 : (5 : ℤ) ^ (d + 1 + 1) = 5 * (5 : ℤ) ^ (d + 1) := by rw [pow_succ']
      have h2 : (5 : ℤ) ^ (2 * d + 2) = ((5 : ℤ) ^ (d + 1)) ^ 2 := by rw [← pow_mul]; congr 1; omega
      have h3 : (5 : ℤ) ^ (3 * d + 3) = ((5 : ℤ) ^ (d + 1)) ^ 3 := by rw [← pow_mul]; congr 1; omega
      have h4 : (5 : ℤ) ^ (4 * d + 3) * 5 = ((5 : ℤ) ^ (d + 1)) ^ 4 := by
        rw [← pow_succ, ← pow_mul]; congr 1; omega
      rw [h1, h2, h3]
      linear_combination (5 : ℤ) ^ (d + 1) * (c : ℤ) ^ 5 * (-h4)
    exact_mod_cast hz

/-- 2-adic valuation step: if `a ≡ 1 (mod 2^s)` and `a ≢ 1 (mod 2^(s+1))` with `s ≥ 2`,
then `a^(2^d) = 1 + 2^(s+d) * c` with `Odd c`. -/
private lemma two_adic_pow_two (a s : ℕ) (hs : 2 ≤ s)
    (h1 : 2 ^ s ∣ a - 1) (h2 : ¬ 2 ^ (s + 1) ∣ a - 1) (ha : 1 ≤ a) :
    ∀ d : ℕ, ∃ c : ℕ, Odd c ∧ a ^ (2 ^ d) = 1 + 2 ^ (s + d) * c := by
  intro d
  induction d with
  | zero =>
    obtain ⟨c, hc⟩ := h1
    refine ⟨c, ?_, by simp; omega⟩
    rw [Nat.odd_iff]
    by_contra hev
    have h2c : 2 ∣ c := by omega
    obtain ⟨c', rfl⟩ := h2c
    apply h2
    refine ⟨c', ?_⟩
    rw [hc, pow_succ]; ring
  | succ d ih =>
    obtain ⟨c, ⟨u, rfl⟩, hc⟩ := ih
    have hpow : a ^ (2 ^ (d + 1)) = (a ^ (2 ^ d)) ^ 2 := by
      rw [← pow_mul, pow_succ]
    rw [hpow, hc]
    have h2pow : 2 ^ (s + d) = 2 * 2 ^ (s + d - 1) := by
      cases hsd_eq : s + d with
      | zero => omega
      | succ k => simp [pow_succ']
    refine ⟨(2 * u + 1) + 2 ^ (s + d - 1) * (2 * u + 1) ^ 2, ?_, ?_⟩
    · have hev : 2 ∣ 2 ^ (s + d - 1) := dvd_pow_self 2 (by omega)
      obtain ⟨w, hw⟩ := hev
      refine ⟨u + w * (2 * u + 1) ^ 2, ?_⟩
      rw [hw]; ring
    · have hsucc : 2 ^ (s + (d + 1)) = 2 * 2 ^ (s + d) := by
        rw [show s + (d + 1) = (s + d) + 1 by omega, pow_succ']
      have hsq : 2 ^ (s + d) * 2 ^ (s + d) = 2 ^ (s + (d + 1)) * 2 ^ (s + d - 1) := by
        rw [hsucc, h2pow]; ring
      nlinarith [hsq, hsucc]

/-- 2-adic surjectivity onto `1 + 2^s Z / 2^(s+d) Z`. -/
private lemma two_adic_surj (a s : ℕ) (hs : 2 ≤ s)
    (h1 : 2 ^ s ∣ a - 1) (h2 : ¬ 2 ^ (s + 1) ∣ a - 1) (ha : 1 ≤ a) :
    ∀ d t : ℕ, t ≡ 1 [MOD 2 ^ s] → ∃ j : ℕ, a ^ j ≡ t [MOD 2 ^ (s + d)] := by
  intro d
  induction d with
  | zero =>
    intro t ht
    exact ⟨0, by simpa [Nat.ModEq] using ht.symm⟩
  | succ d ih =>
    intro t ht
    obtain ⟨j, hj⟩ := ih t ht
    by_cases hdone : a ^ j ≡ t [MOD 2 ^ (s + (d + 1))]
    · exact ⟨j, hdone⟩
    · refine ⟨j + 2 ^ d, ?_⟩
      obtain ⟨c, hc_odd, hc_eq⟩ := two_adic_pow_two a s hs h1 h2 ha d
      have ha_odd : Odd a := by
        have h2a : 2 ∣ a - 1 := dvd_trans (dvd_pow_self 2 (by omega)) h1
        rw [Nat.odd_iff]; omega
      have hprod_odd : Odd (a ^ j * c) := (ha_odd.pow).mul hc_odd
      have hmod_step : a ^ (j + 2 ^ d) ≡ a ^ j + 2 ^ (s + d) [MOD 2 ^ (s + (d + 1))] := by
        conv_lhs => rw [pow_add, hc_eq, mul_add, mul_one]
        rcases hprod_odd with ⟨w, hw⟩
        have heq : a ^ j * (2 ^ (s + d) * c) = 2 ^ (s + d) + 2 ^ (s + (d + 1)) * w := by
          have : 2 ^ (s + (d + 1)) = 2 ^ (s + d) * 2 := by
            rw [show s + (d + 1) = (s + d) + 1 by omega, pow_succ]
          calc
            a ^ j * (2 ^ (s + d) * c) = 2 ^ (s + d) * (a ^ j * c) := by ring
            _ = 2 ^ (s + d) * (2 * w + 1) := by rw [hw]
            _ = 2 ^ (s + d) + 2 ^ (s + (d + 1)) * w := by rw [this]; ring
        rw [Nat.ModEq, heq, ← add_assoc, Nat.add_mul_mod_self_left]
      have hmod_t : a ^ j + 2 ^ (s + d) ≡ t [MOD 2 ^ (s + (d + 1))] := by
        have hpow2 : 2 ^ (s + (d + 1)) = 2 * 2 ^ (s + d) := by
          rw [show s + (d + 1) = (s + d) + 1 by omega, pow_succ']
        rw [Nat.ModEq] at hj hdone ⊢
        have hpos : 0 < 2 ^ (s + d) := by positivity
        have hrem : ∀ x : ℕ, x % (2 * 2 ^ (s + d)) = x % 2 ^ (s + d) ∨
            x % (2 * 2 ^ (s + d)) = x % 2 ^ (s + d) + 2 ^ (s + d) := by
          intro x
          have hdiv := Nat.mod_mul_left_mod x 2 (2 ^ (s + d))
          have hlt := Nat.mod_lt x (show 0 < 2 * 2 ^ (s + d) by omega)
          have hq : x % (2 * 2 ^ (s + d)) / 2 ^ (s + d) < 2 :=
            Nat.div_lt_of_lt_mul (by linarith)
          have hdm := Nat.div_add_mod (x % (2 * 2 ^ (s + d))) (2 ^ (s + d))
          rw [hdiv] at hdm
          set q := x % (2 * 2 ^ (s + d)) / 2 ^ (s + d)
          have hq_lt : q < 2 := hq
          have hq01 : q = 0 ∨ q = 1 := by
            rcases Nat.eq_zero_or_pos q with h0 | hpos
            · exact Or.inl h0
            · exact Or.inr (by linarith)
          rcases hq01 with h0 | h1'
          · left; rw [h0, mul_zero, zero_add] at hdm; exact hdm.symm
          · right; rw [h1', mul_one] at hdm; omega
        rw [hpow2] at hdone ⊢
        have hadd : (a ^ j + 2 ^ (s + d)) % (2 * 2 ^ (s + d)) =
            (a ^ j % (2 * 2 ^ (s + d)) + 2 ^ (s + d)) % (2 * 2 ^ (s + d)) :=
          ((Nat.mod_modEq (a ^ j) (2 * 2 ^ (s + d))).symm.add_right (2 ^ (s + d)))
        rw [hadd]
        have hlt1 := Nat.mod_lt (a ^ j) hpos
        rcases hrem (a ^ j) with hr1 | hr1 <;> rcases hrem t with hr2 | hr2
        · exfalso; exact hdone (by omega)
        · rw [hr1, hr2, ← hj, Nat.mod_eq_of_lt (by omega)]
        · rw [hr1, hr2, ← hj]
          have : a ^ j % 2 ^ (s + d) + 2 ^ (s + d) + 2 ^ (s + d) =
              a ^ j % 2 ^ (s + d) + 2 * 2 ^ (s + d) := by ring
          rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
        · exfalso; exact hdone (by omega)
      exact hmod_step.trans hmod_t

/-- 5-adic valuation step: if `5 ∣ a - 1` and `¬ 25 ∣ a - 1`, then
`a^(5^d) = 1 + 5^(d+1) * c` with `¬ 5 ∣ c`. -/
private lemma five_adic_pow_five (a : ℕ) (h1 : 5 ∣ a - 1) (h2 : ¬ 25 ∣ a - 1) (ha : 1 ≤ a) :
    ∀ d : ℕ, ∃ c : ℕ, ¬ 5 ∣ c ∧ a ^ (5 ^ d) = 1 + 5 ^ (d + 1) * c := by
  intro d
  induction d with
  | zero =>
    obtain ⟨c, hc⟩ := h1
    refine ⟨c, ?_, by simp; omega⟩
    intro h5c
    obtain ⟨c', rfl⟩ := h5c
    apply h2
    exact ⟨c', by omega⟩
  | succ d ih =>
    obtain ⟨c, hc5, hc_eq⟩ := ih
    have hpow : a ^ (5 ^ (d + 1)) = (a ^ (5 ^ d)) ^ 5 := by
      rw [← pow_mul, pow_succ]
    rw [hpow, hc_eq]
    refine ⟨c + 2 * 5 ^ (d + 1) * c ^ 2 + 2 * 5 ^ (2 * d + 2) * c ^ 3 +
      5 ^ (3 * d + 3) * c ^ 4 + 5 ^ (4 * d + 3) * c ^ 5, ?_, ?_⟩
    · intro hdvd
      have h5p1 : 5 ∣ 5 ^ (d + 1) := dvd_pow_self 5 (by omega)
      have h5p2 : 5 ∣ 5 ^ (2 * d + 2) := dvd_pow_self 5 (by omega)
      have h5p3 : 5 ∣ 5 ^ (3 * d + 3) := dvd_pow_self 5 (by omega)
      have h5p4 : 5 ∣ 5 ^ (4 * d + 3) := dvd_pow_self 5 (by omega)
      have hrest : 5 ∣ 2 * 5 ^ (d + 1) * c ^ 2 + 2 * 5 ^ (2 * d + 2) * c ^ 3 +
          5 ^ (3 * d + 3) * c ^ 4 + 5 ^ (4 * d + 3) * c ^ 5 := by
        refine dvd_add (dvd_add (dvd_add ?_ ?_) ?_) ?_
        · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right h5p1 2) _
        · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right h5p2 2) _
        · exact dvd_mul_of_dvd_left h5p3 _
        · exact dvd_mul_of_dvd_left h5p4 _
      have hadd : c + (2 * 5 ^ (d + 1) * c ^ 2 + 2 * 5 ^ (2 * d + 2) * c ^ 3 +
          5 ^ (3 * d + 3) * c ^ 4 + 5 ^ (4 * d + 3) * c ^ 5) =
          c + 2 * 5 ^ (d + 1) * c ^ 2 + 2 * 5 ^ (2 * d + 2) * c ^ 3 +
          5 ^ (3 * d + 3) * c ^ 4 + 5 ^ (4 * d + 3) * c ^ 5 := by ring
      rw [← hadd] at hdvd
      exact hc5 ((Nat.dvd_add_left hrest).mp hdvd)
    · have h1p : 5 ^ (d + 1 + 1) = 5 * 5 ^ (d + 1) := by rw [pow_succ']
      have h2p : 5 ^ (2 * d + 2) = (5 ^ (d + 1)) ^ 2 := by rw [← pow_mul]; congr 1; omega
      have h3p : 5 ^ (3 * d + 3) = (5 ^ (d + 1)) ^ 3 := by rw [← pow_mul]; congr 1; omega
      have h4p : 5 ^ (4 * d + 3) * 5 = (5 ^ (d + 1)) ^ 4 := by
        rw [← pow_succ, ← pow_mul]; congr 1; omega
      rw [h1p, h2p, h3p]
      zify
      have h4pz : ((5 : ℤ) ^ (4 * d + 3)) * 5 = ((5 : ℤ) ^ (d + 1)) ^ 4 := by exact_mod_cast h4p
      linear_combination ((5 : ℤ) ^ (d + 1)) * (c : ℤ) ^ 5 * (-h4pz)

/-- 5-adic surjectivity onto `1 + 5 Z / 5^(d+1) Z`. -/
private lemma five_adic_surj (a : ℕ) (h1 : 5 ∣ a - 1) (h2 : ¬ 25 ∣ a - 1) (ha : 1 ≤ a) :
    ∀ d t : ℕ, t ≡ 1 [MOD 5] → ∃ j : ℕ, a ^ j ≡ t [MOD 5 ^ (d + 1)] := by
  intro d
  induction d with
  | zero =>
    intro t ht
    exact ⟨0, by simpa [Nat.ModEq] using ht.symm⟩
  | succ d ih =>
    intro t ht
    obtain ⟨j, hj⟩ := ih t ht
    obtain ⟨c, hc5, hc_eq⟩ := five_adic_pow_five a h1 h2 ha d
    have ha5 : a ≡ 1 [MOD 5] := by
      obtain ⟨w, hw⟩ := h1
      rw [Nat.ModEq]; omega
    have haj5 : a ^ j ≡ 1 [MOD 5] := by
      simpa using ha5.pow j
    have hstep : ∀ r : ℕ, a ^ (j + r * 5 ^ d) ≡ a ^ j + r * c * 5 ^ (d + 1) [MOD 5 ^ (d + 2)] := by
      intro r
      have hpow_r : (1 + 5 ^ (d + 1) * c) ^ r ≡ 1 + r * c * 5 ^ (d + 1) [MOD 5 ^ (d + 2)] := by
        induction r with
        | zero => simp [Nat.ModEq]
        | succ r ihr =>
          rw [pow_succ]
          have hm := ihr.mul_right (1 + 5 ^ (d + 1) * c)
          refine hm.trans ?_
          have hdiv : 5 ^ (d + 2) ∣ r * c ^ 2 * (5 ^ (d + 1) * 5 ^ (d + 1)) := by
            have hd2 : 5 ^ (d + 2) ∣ 5 ^ (d + 1) * 5 ^ (d + 1) := by
              rw [← pow_add]
              exact Nat.pow_dvd_pow 5 (by omega)
            exact dvd_mul_of_dvd_right hd2 _
          obtain ⟨q, hq⟩ := hdiv
          have heq : (1 + r * c * 5 ^ (d + 1)) * (1 + 5 ^ (d + 1) * c) =
              (1 + (r + 1) * c * 5 ^ (d + 1)) + 5 ^ (d + 2) * q := by
            linarith [show (1 + r * c * 5 ^ (d + 1)) * (1 + 5 ^ (d + 1) * c) =
              (1 + (r + 1) * c * 5 ^ (d + 1)) + r * c ^ 2 * (5 ^ (d + 1) * 5 ^ (d + 1)) by ring, hq]
          rw [Nat.ModEq, heq, Nat.add_mul_mod_self_left]
      have hmul : a ^ (j + r * 5 ^ d) = a ^ j * (1 + 5 ^ (d + 1) * c) ^ r := by
        rw [pow_add, mul_comm r (5 ^ d), pow_mul, hc_eq]
      rw [hmul]
      refine (hpow_r.mul_left (a ^ j)).trans ?_
      have h1aj : 1 ≤ a ^ j := Nat.one_le_pow j a (by omega)
      have h5aj : 5 ∣ a ^ j - 1 := by
        rw [Nat.ModEq] at haj5
        omega
      obtain ⟨w, hw⟩ := h5aj
      have heq : a ^ j * (1 + r * c * 5 ^ (d + 1)) =
          (a ^ j + r * c * 5 ^ (d + 1)) + 5 ^ (d + 2) * (w * r * c) := by
        have hp5 : 5 ^ (d + 2) = 5 * 5 ^ (d + 1) := by rw [pow_succ']
        have haj_eq : a ^ j = 1 + 5 * w := by omega
        calc
          a ^ j * (1 + r * c * 5 ^ (d + 1))
            = a ^ j + a ^ j * (r * c * 5 ^ (d + 1)) := by ring
          _ = a ^ j + (1 + 5 * w) * (r * c * 5 ^ (d + 1)) := by
                conv_lhs => arg 2; arg 1; rw [haj_eq]
          _ = (a ^ j + r * c * 5 ^ (d + 1)) + (5 * 5 ^ (d + 1)) * (w * r * c) := by ring
          _ = (a ^ j + r * c * 5 ^ (d + 1)) + 5 ^ (d + 2) * (w * r * c) := by rw [← hp5]
      rw [Nat.ModEq, heq, Nat.add_mul_mod_self_left]
    have hpow5 : 5 ^ (d + 2) = 5 * 5 ^ (d + 1) := by rw [pow_succ']
    set qa := (a ^ j % 5 ^ (d + 2)) / 5 ^ (d + 1)
    set qt := (t % 5 ^ (d + 2)) / 5 ^ (d + 1)
    have hrem_a : a ^ j % 5 ^ (d + 2) = qa * 5 ^ (d + 1) + a ^ j % 5 ^ (d + 1) := by
      have hdm := Nat.div_add_mod (a ^ j % 5 ^ (d + 2)) (5 ^ (d + 1))
      have hm := Nat.mod_mul_left_mod (a ^ j) 5 (5 ^ (d + 1))
      rw [← hpow5] at hm
      rw [hm, mul_comm] at hdm
      exact hdm.symm
    have hrem_t : t % 5 ^ (d + 2) = qt * 5 ^ (d + 1) + t % 5 ^ (d + 1) := by
      have hdm := Nat.div_add_mod (t % 5 ^ (d + 2)) (5 ^ (d + 1))
      have hm := Nat.mod_mul_left_mod t 5 (5 ^ (d + 1))
      rw [← hpow5] at hm
      rw [hm, mul_comm] at hdm
      exact hdm.symm
    have hex_r : ∃ r < 5, (qa + r * c) % 5 = qt % 5 := by
      have haux : ∀ x y z : ℕ, z % 5 ≠ 0 → ∃ r < 5, (x + r * z) % 5 = y % 5 := by
        intro x y z hz
        have hx : x % 5 = 0 ∨ x % 5 = 1 ∨ x % 5 = 2 ∨ x % 5 = 3 ∨ x % 5 = 4 := by omega
        have hy : y % 5 = 0 ∨ y % 5 = 1 ∨ y % 5 = 2 ∨ y % 5 = 3 ∨ y % 5 = 4 := by omega
        have hzc : z % 5 = 1 ∨ z % 5 = 2 ∨ z % 5 = 3 ∨ z % 5 = 4 := by omega
        rcases hzc with h | h | h | h
        · refine ⟨(y % 5 + 5 - x % 5) % 5, Nat.mod_lt _ (by omega), ?_⟩
          rw [Nat.add_mod, Nat.mul_mod, h, Nat.mod_mod]; omega
        · refine ⟨(3 * (y % 5 + 5 - x % 5)) % 5, Nat.mod_lt _ (by omega), ?_⟩
          rw [Nat.add_mod, Nat.mul_mod, h, Nat.mod_mod]; omega
        · refine ⟨(2 * (y % 5 + 5 - x % 5)) % 5, Nat.mod_lt _ (by omega), ?_⟩
          rw [Nat.add_mod, Nat.mul_mod, h, Nat.mod_mod]; omega
        · refine ⟨(4 * (y % 5 + 5 - x % 5)) % 5, Nat.mod_lt _ (by omega), ?_⟩
          rw [Nat.add_mod, Nat.mul_mod, h, Nat.mod_mod]; omega
      exact haux qa qt c (by omega)
    obtain ⟨r, _, hr⟩ := hex_r
    refine ⟨j + r * 5 ^ d, (hstep r).trans ?_⟩
    rw [Nat.ModEq] at hj ⊢
    have hmod_add : (a ^ j + r * c * 5 ^ (d + 1)) % 5 ^ (d + 2) =
        ((a ^ j % 5 ^ (d + 2)) + r * c * 5 ^ (d + 1)) % 5 ^ (d + 2) :=
      ((Nat.mod_modEq (a ^ j) (5 ^ (d + 2))).symm.add_right (r * c * 5 ^ (d + 1)))
    rw [hmod_add, hrem_a, hj]
    have hlhs : (qa * 5 ^ (d + 1) + t % 5 ^ (d + 1) + r * c * 5 ^ (d + 1)) =
        (qa + r * c) * 5 ^ (d + 1) + t % 5 ^ (d + 1) := by ring
    rw [hlhs]
    have h5mod : (qa + r * c) * 5 ^ (d + 1) ≡ qt * 5 ^ (d + 1) [MOD 5 ^ (d + 2)] := by
      rw [Nat.ModEq, hpow5, Nat.mul_mod_mul_right, Nat.mul_mod_mul_right, hr]
    have htot := h5mod.add_right (t % 5 ^ (d + 1))
    rw [Nat.ModEq] at htot
    rw [htot, ← hrem_t, Nat.mod_mod]

/-- Master lifting theorem: given `m` coprime to 10, `r ≥ 1`, `s ≥ 2`, `N ≥ s`,
if `2^s ∣ m^r - 1`, `¬ 2^(s+1) ∣ m^r - 1`, `5 ∣ m^r - 1`, `¬ 25 ∣ m^r - 1`,
and `m ^ k0 ≡ target (mod 2^s)` and `m ^ k0 ≡ target (mod 5)`,
then there exists `K ≥ 1` with `10 ^ (N - 1) ≤ m ^ K` and `m ^ K ≡ target (mod 10 ^ N)`. -/
private lemma lift_mod_ten_pow (m r k0 s N target : ℕ)
    (hm1 : 1 < m) (hcop10 : Nat.Coprime m 10) (hr : 1 ≤ r) (hs : 2 ≤ s) (hN : s ≤ N)
    (h2a : 2 ^ s ∣ m ^ r - 1) (h2a' : ¬ 2 ^ (s + 1) ∣ m ^ r - 1)
    (h5a : 5 ∣ m ^ r - 1) (h5a' : ¬ 25 ∣ m ^ r - 1)
    (hinit2 : m ^ k0 ≡ target [MOD 2 ^ s]) (hinit5 : m ^ k0 ≡ target [MOD 5]) :
    ∃ K : ℕ, 1 ≤ K ∧ 10 ^ (N - 1) ≤ m ^ K ∧ m ^ K ≡ target [MOD 10 ^ N] := by
  have ha1 : 1 ≤ m ^ r := Nat.one_le_pow r m (by omega)
  have hcop25 : Nat.Coprime m 2 ∧ Nat.Coprime m 5 :=
    Nat.coprime_mul_iff_right.mp (show Nat.Coprime m (2 * 5) from hcop10)
  have hcop2 : Nat.Coprime (m ^ k0) (2 ^ N) := hcop25.1.pow k0 N
  have hcop5 : Nat.Coprime (m ^ k0) (5 ^ N) := hcop25.2.pow k0 N
  let inv2 := ((m ^ k0 : ZMod (2 ^ N))⁻¹).val
  let inv5 := ((m ^ k0 : ZMod (5 ^ N))⁻¹).val
  have hinv2 : m ^ k0 * inv2 ≡ 1 [MOD 2 ^ N] := by
    have : NeZero (2 ^ N) := ⟨by positivity⟩
    rw [← ZMod.natCast_eq_natCast_iff]
    push_cast
    change ((m ^ k0 : ZMod (2 ^ N)) * ((m ^ k0 : ZMod (2 ^ N))⁻¹).val : ZMod (2 ^ N)) = 1
    rw [ZMod.natCast_zmod_val]
    have hu : IsUnit ((m : ZMod (2 ^ N)) ^ k0) := by
      simpa only [Nat.cast_pow] using (ZMod.isUnit_iff_coprime (m ^ k0) (2 ^ N)).mpr hcop2
    exact ZMod.mul_inv_of_unit _ hu
  have hinv5 : m ^ k0 * inv5 ≡ 1 [MOD 5 ^ N] := by
    have : NeZero (5 ^ N) := ⟨by positivity⟩
    rw [← ZMod.natCast_eq_natCast_iff]
    push_cast
    change ((m ^ k0 : ZMod (5 ^ N)) * ((m ^ k0 : ZMod (5 ^ N))⁻¹).val : ZMod (5 ^ N)) = 1
    rw [ZMod.natCast_zmod_val]
    have hu : IsUnit ((m : ZMod (5 ^ N)) ^ k0) := by
      simpa only [Nat.cast_pow] using (ZMod.isUnit_iff_coprime (m ^ k0) (5 ^ N)).mpr hcop5
    exact ZMod.mul_inv_of_unit _ hu
  have ht2_init : inv2 * target ≡ 1 [MOD 2 ^ s] := by
    have h1 := hinit2.symm.mul_left inv2
    have h2 : inv2 * m ^ k0 ≡ 1 [MOD 2 ^ s] := by
      have hdvd : 2 ^ s ∣ 2 ^ N := Nat.pow_dvd_pow 2 hN
      have := hinv2.of_dvd hdvd
      rwa [mul_comm] at this
    exact h1.trans h2
  have ht5_init : inv5 * target ≡ 1 [MOD 5] := by
    have h1 := hinit5.symm.mul_left inv5
    have h2 : inv5 * m ^ k0 ≡ 1 [MOD 5] := by
      have hdvd : 5 ∣ 5 ^ N := dvd_pow_self 5 (by omega)
      have := hinv5.of_dvd hdvd
      rwa [mul_comm] at this
    exact h1.trans h2
  obtain ⟨j2, hj2⟩ := two_adic_surj (m ^ r) s hs h2a h2a' ha1 (N - s) (inv2 * target) ht2_init
  obtain ⟨j5, hj5⟩ := five_adic_surj (m ^ r) h5a h5a' ha1 (N - 1) (inv5 * target) ht5_init
  have hNs : s + (N - s) = N := by omega
  have hN1 : (N - 1) + 1 = N := by omega
  rw [hNs] at hj2
  rw [hN1] at hj5
  have hper2 : (m ^ r) ^ (2 ^ (N - s)) ≡ 1 [MOD 2 ^ N] := by
    obtain ⟨c, _, hc⟩ := two_adic_pow_two (m ^ r) s hs h2a h2a' ha1 (N - s)
    rw [hNs] at hc
    rw [Nat.ModEq, hc, add_comm, Nat.mul_add_mod_self_left]
  have hper5 : (m ^ r) ^ (5 ^ (N - 1)) ≡ 1 [MOD 5 ^ N] := by
    obtain ⟨c, _, hc⟩ := five_adic_pow_five (m ^ r) h5a h5a' ha1 (N - 1)
    rw [hN1] at hc
    rw [Nat.ModEq, hc, add_comm, Nat.mul_add_mod_self_left]
  have hcop_per : Nat.Coprime (2 ^ (N - s)) (5 ^ (N - 1)) :=
    (by decide : Nat.Coprime 2 5).pow (N - s) (N - 1)
  let J0 := (Nat.chineseRemainder hcop_per j2 j5).val
  have hJ0_2 : J0 ≡ j2 [MOD 2 ^ (N - s)] := (Nat.chineseRemainder hcop_per j2 j5).property.1
  have hJ0_5 : J0 ≡ j5 [MOD 5 ^ (N - 1)] := (Nat.chineseRemainder hcop_per j2 j5).property.2
  let L := 2 ^ (N - s) * 5 ^ (N - 1)
  let J := J0 + (4 * N + 1) * L
  refine ⟨k0 + r * J, ?_, ?_, ?_⟩
  · have hL : 0 < L := by dsimp [L]; positivity
    have hJ : 1 ≤ J := by dsimp [J]; nlinarith
    nlinarith
  · have hL : 0 < L := by dsimp [L]; positivity
    have hJ : 4 * N ≤ J := by dsimp [J]; nlinarith
    have hK_ge : 4 * N ≤ k0 + r * J := by nlinarith
    calc
      10 ^ (N - 1) ≤ 10 ^ N := Nat.pow_le_pow_right (by omega) (by omega)
      _ ≤ 16 ^ N := Nat.pow_le_pow_left (by omega) N
      _ = 2 ^ (4 * N) := by rw [pow_mul]; norm_num
      _ ≤ m ^ (4 * N) := Nat.pow_le_pow_left (by omega) (4 * N)
      _ ≤ m ^ (k0 + r * J) := Nat.pow_le_pow_right (by omega) hK_ge
  · have hmod_pow : ∀ (base per mod x y : ℕ), base ^ per ≡ 1 [MOD mod] → x ≡ y [MOD per] →
        base ^ x ≡ base ^ y [MOD mod] := by
      intro base per mod x y hbp hxy
      wlog hle : y ≤ x generalizing x y
      · exact (this y x hxy.symm (by omega)).symm
      obtain ⟨q, hq⟩ : per ∣ x - y := (Nat.modEq_iff_dvd' hle).mp hxy.symm
      have hxe : x = y + per * q := by omega
      rw [hxe, pow_add, pow_mul]
      have h1 : (base ^ per) ^ q ≡ 1 ^ q [MOD mod] := hbp.pow q
      rw [one_pow] at h1
      simpa using h1.mul_left (base ^ y)
    have hJ2 : J ≡ j2 [MOD 2 ^ (N - s)] := by
      have : J = J0 + 2 ^ (N - s) * ((4 * N + 1) * 5 ^ (N - 1)) := by dsimp [J, L]; ring
      rw [Nat.ModEq, this, Nat.add_mul_mod_self_left]
      exact hJ0_2
    have hJ5 : J ≡ j5 [MOD 5 ^ (N - 1)] := by
      have : J = J0 + 5 ^ (N - 1) * ((4 * N + 1) * 2 ^ (N - s)) := by dsimp [J, L]; ring
      rw [Nat.ModEq, this, Nat.add_mul_mod_self_left]
      exact hJ0_5
    have h2 : m ^ (k0 + r * J) ≡ target [MOD 2 ^ N] := by
      rw [pow_add, pow_mul]
      have hpowJ := (hmod_pow (m ^ r) (2 ^ (N - s)) (2 ^ N) J j2 hper2 hJ2).trans hj2
      have hmul := hpowJ.mul_left (m ^ k0)
      have hleft : m ^ k0 * (inv2 * target) ≡ target [MOD 2 ^ N] := by
        rw [← mul_assoc]
        simpa using hinv2.mul_right target
      exact hmul.trans hleft
    have h5 : m ^ (k0 + r * J) ≡ target [MOD 5 ^ N] := by
      rw [pow_add, pow_mul]
      have hpowJ := (hmod_pow (m ^ r) (5 ^ (N - 1)) (5 ^ N) J j5 hper5 hJ5).trans hj5
      have hmul := hpowJ.mul_left (m ^ k0)
      have hleft : m ^ k0 * (inv5 * target) ≡ target [MOD 5 ^ N] := by
        rw [← mul_assoc]
        simpa using hinv5.mul_right target
      exact hmul.trans hleft
    have hcop_25 : Nat.Coprime (2 ^ N) (5 ^ N) := (by decide : Nat.Coprime 2 5).pow N N
    have h10 : 10 ^ N = 2 ^ N * 5 ^ N := by rw [show (10 : ℕ) = 2 * 5 by norm_num, mul_pow]
    rw [h10]
    exact (Nat.modEq_and_modEq_iff_modEq_mul hcop_25).mp ⟨h2, h5⟩

/-! ### Part 1: `m = 10 * 2^(n-1) - 1` achieves exact max `n` for `n > 5` -/

private lemma target_achieves_max (n : ℕ) (hn : 5 < n) :
    maxIdenticalTrailingDigits (10 * 2 ^ (n - 1) - 1) n := by
  have hm_eq : 10 * 2 ^ (n - 1) - 1 = 5 * 2 ^ n - 1 := by
    have : 2 ^ n = 2 * 2 ^ (n - 1) := by
      cases n with
      | zero => omega
      | succ k => simp [pow_succ']
    omega
  rw [hm_eq]
  set m := 5 * 2 ^ n - 1
  have h2n_ge : 64 ≤ 2 ^ n := by
    calc 64 = 2 ^ 6 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) (by omega)
  have hm_ge : 319 ≤ m := by omega
  have hm_add : m + 1 = 5 * 2 ^ n := by omega
  constructor
  · refine ⟨5 ^ (n - 1), Nat.one_le_pow _ _ (by omega), 9, by omega, ?_, ?_⟩
    · have hk_ge : n ≤ 5 ^ (n - 1) := by
        have haux : ∀ k : ℕ, k + 1 ≤ 5 ^ k := by
          intro k
          induction k with
          | zero => norm_num
          | succ j ihj =>
            have : 5 ^ (j + 1) = 5 * 5 ^ j := pow_succ' 5 j
            omega
        simpa [show n - 1 + 1 = n by omega] using haux (n - 1)
      calc
        10 ^ (n - 1) ≤ 10 ^ n := Nat.pow_le_pow_right (by omega) (by omega)
        _ ≤ m ^ n := Nat.pow_le_pow_left (by omega) n
        _ ≤ m ^ (5 ^ (n - 1)) := Nat.pow_le_pow_right (by omega) hk_ge
    · have hk_odd : Odd (5 ^ (n - 1)) := (by decide : Odd 5).pow
      have h2dvd : 2 ^ n ∣ m ^ (5 ^ (n - 1)) + 1 := by
        rw [two_pow_dvd_pow_add_one_iff m (5 ^ (n - 1)) n hk_odd, hm_add]
        exact dvd_mul_left (2 ^ n) 5
      have h5dvd : 5 ^ n ∣ m ^ (5 ^ (n - 1)) + 1 := by
        have h := five_pow_dvd_pow_five_pow_add_one m (n - 1) (by rw [hm_add]; exact dvd_mul_right 5 _)
        rwa [show n - 1 + 1 = n by omega] at h
      have hcop : Nat.Coprime (2 ^ n) (5 ^ n) := (by decide : Nat.Coprime 2 5).pow n n
      have h10dvd : 10 ^ n ∣ m ^ (5 ^ (n - 1)) + 1 := by
        rw [show 10 ^ n = 2 ^ n * 5 ^ n by rw [show (10 : ℕ) = 2 * 5 by norm_num, mul_pow]]
        exact hcop.mul_dvd_of_dvd_of_dvd h2dvd h5dvd
      have h9r := nine_mul_repunit n
      have hpos : 1 ≤ 10 ^ n := Nat.one_le_pow n 10 (by omega)
      have hmod : m ^ (5 ^ (n - 1)) % 10 ^ n = 10 ^ n - 1 := by
        obtain ⟨q, hq⟩ := h10dvd
        have hq1 : 1 ≤ q := by
          by_contra h0
          have : q = 0 := by omega
          rw [this, mul_zero] at hq
          omega
        have heq : m ^ (5 ^ (n - 1)) = (10 ^ n - 1) + 10 ^ n * (q - 1) := by
          have : 10 ^ n * q = 10 ^ n + 10 ^ n * (q - 1) := by
            cases q with
            | zero => omega
            | succ q' => simp [mul_add, add_comm]
          omega
        rw [heq, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
      rw [hmod]
      change 10 ^ n - 1 = 9 * repunit n
      omega
  · rintro t ⟨k, hk1, d, hd10, _, hmod⟩
    by_contra hgt
    have ht : n + 1 ≤ t := by omega
    have hm10 : m % 10 = 9 := by
      have h2dvd : 2 ∣ 2 ^ n := dvd_pow_self 2 (by omega)
      obtain ⟨w, hw⟩ := h2dvd
      omega
    have h10dvd_t : 10 ∣ 10 ^ t := dvd_pow_self 10 (by omega)
    have hmk10 : m ^ k % 10 = d := by
      have h1 : (m ^ k % 10 ^ t) % 10 = m ^ k % 10 := Nat.mod_mod_of_dvd (m ^ k) h10dvd_t
      rw [hmod] at h1
      have hr10 : repunit t % 10 = 1 := by
        have h9 := nine_mul_repunit t
        omega
      have h2 : (d * repunit t) % 10 = d := by
        rw [Nat.mul_mod, hr10, mul_one, Nat.mod_mod, Nat.mod_eq_of_lt hd10]
      exact h1.symm.trans h2
    have hmk10_19 : m ^ k % 10 = 1 ∨ m ^ k % 10 = 9 := by
      have hm9 : m ≡ 9 [MOD 10] := by show m % 10 = 9 % 10; omega
      have hpow := hm9.pow k
      rw [Nat.ModEq] at hpow
      rw [hpow]
      rcases Nat.even_or_odd k with ⟨j, rfl⟩ | ⟨j, rfl⟩
      · left
        have : 9 ^ (j + j) = 81 ^ j := by rw [← two_mul, pow_mul]; norm_num
        rw [this]
        have : (81 : ℕ) ≡ 1 [MOD 10] := by decide
        simpa [Nat.ModEq] using this.pow j
      · right
        have : 9 ^ (2 * j + 1) = 81 ^ j * 9 := by rw [pow_succ, pow_mul]; norm_num
        rw [this, Nat.mul_mod]
        have : (81 : ℕ) ≡ 1 [MOD 10] := by decide
        have hp : 81 ^ j % 10 = 1 := by simpa [Nat.ModEq] using this.pow j
        rw [hp]
    have hd19 : d = 1 ∨ d = 9 := by omega
    rcases hd19 with rfl | rfl
    · have h16dvd_t : 16 ∣ 10 ^ t := by
        have : 16 ∣ 10 ^ 4 := by norm_num
        exact dvd_trans this (Nat.pow_dvd_pow 10 (by omega))
      have hm16 : m % 16 = 15 := by
        have : 16 ∣ 2 ^ n := by
          have : 16 = 2 ^ 4 := by norm_num
          rw [this]; exact Nat.pow_dvd_pow 2 (by omega)
        obtain ⟨w, hw⟩ := this
        omega
      have hmk16 : m ^ k % 16 = 1 ∨ m ^ k % 16 = 15 := by
        have h15 : m ≡ 15 [MOD 16] := by show m % 16 = 15 % 16; omega
        have hp := h15.pow k
        rw [Nat.ModEq] at hp; rw [hp]
        rcases Nat.even_or_odd k with ⟨j, rfl⟩ | ⟨j, rfl⟩
        · left
          have : 15 ^ (j + j) = 225 ^ j := by rw [← two_mul, pow_mul]; norm_num
          rw [this]
          have : (225 : ℕ) ≡ 1 [MOD 16] := by decide
          simpa [Nat.ModEq] using this.pow j
        · right
          have : 15 ^ (2 * j + 1) = 225 ^ j * 15 := by rw [pow_succ, pow_mul]; norm_num
          rw [this, Nat.mul_mod]
          have : (225 : ℕ) ≡ 1 [MOD 16] := by decide
          have hp2 : 225 ^ j % 16 = 1 := by simpa [Nat.ModEq] using this.pow j
          rw [hp2]
      have h1 : m ^ k % 16 = repunit t % 16 := by
        have := Nat.mod_mod_of_dvd (m ^ k) h16dvd_t
        rw [hmod, one_mul] at this
        exact this.symm
      have hr16 : repunit t % 16 = 7 := by
        have h9 := nine_mul_repunit t
        omega
      omega
    · have h2dvd_t : 2 ^ (n + 1) ∣ 10 ^ t := by
        have h1 : 2 ^ (n + 1) ∣ 10 ^ (n + 1) := by
          rw [show 10 ^ (n + 1) = 2 ^ (n + 1) * 5 ^ (n + 1) by rw [show (10 : ℕ) = 2 * 5 by norm_num, mul_pow]]
          exact dvd_mul_right _ _
        exact dvd_trans h1 (Nat.pow_dvd_pow 10 ht)
      have h9r := nine_mul_repunit t
      have hdvd_mk : 2 ^ (n + 1) ∣ m ^ k + 1 := by
        have h10 : 10 ^ t ∣ m ^ k + 1 := by
          have hmod1 : m ^ k % 10 ^ t = 10 ^ t - 1 := by
            change m ^ k % 10 ^ t = 9 * repunit t at hmod
            omega
          have hpos : 1 ≤ 10 ^ t := Nat.one_le_pow t 10 (by omega)
          have hdiv := Nat.div_add_mod (m ^ k) (10 ^ t)
          refine ⟨m ^ k / 10 ^ t + 1, ?_⟩
          rw [mul_add, mul_one]; omega
        exact dvd_trans h2dvd_t h10
      have hk_odd : Odd k := by
        rw [Nat.odd_iff]
        by_contra hev
        have h2k : 2 ∣ k := by omega
        obtain ⟨j, rfl⟩ := h2k
        have h4 : 4 ∣ m ^ (2 * j) + 1 := dvd_trans (by
          show 2 ^ 2 ∣ 2 ^ (n + 1); exact Nat.pow_dvd_pow 2 (by omega)) hdvd_mk
        have hsq : (m ^ j) ^ 2 % 4 = 1 := by
          have hmj_odd : m ^ j % 2 = 1 := by
            have : m ≡ 1 [MOD 2] := by show m % 2 = 1 % 2; omega
            simpa [Nat.ModEq] using this.pow j
          have : (m ^ j % 4) = 1 ∨ (m ^ j % 4) = 3 := by omega
          rw [sq, Nat.mul_mod]
          rcases this with h | h <;> rw [h]
        rw [mul_comm 2 j, pow_mul] at h4
        omega
      have h2m : 2 ^ (n + 1) ∣ m + 1 := (two_pow_dvd_pow_add_one_iff m k (n + 1) hk_odd).mp hdvd_mk
      rw [hm_add] at h2m
      have hcop : Nat.Coprime (2 ^ (n + 1)) 5 := (by decide : Nat.Coprime 2 5).pow_left (n + 1)
      have hbad : 2 ^ (n + 1) ∣ 2 ^ n := by
        rw [mul_comm] at h2m
        exact hcop.dvd_of_dvd_mul_right h2m
      have hle : 2 ^ (n + 1) ≤ 2 ^ n := Nat.le_of_dvd (by positivity) hbad
      have hlt : 2 ^ n < 2 ^ (n + 1) := by
        rw [pow_succ]; linarith [show 0 < 2 ^ n by positivity]
      omega

/-! ### Part 2: Minimality — every `m > 1` with max `n > 5` satisfies `10 * 2^(n-1) - 1 ≤ m` -/

private lemma mod_of_mod_ten_pow {a b n M : ℕ} (hM : M ∣ 10 ^ n) (h : a % 10 ^ n = b) :
    a ≡ b [MOD M] := by
  rw [Nat.ModEq]
  have h1 := Nat.mod_mod_of_dvd a hM
  rw [h] at h1
  exact h1.symm

private lemma ten_pow_ge_bound (n : ℕ) (hn : 5 < n) : 5 * 2 ^ n ≤ 2 * repunit n := by
  have h1 : 5 * 2 ^ n ≤ 2 * 10 ^ (n - 1) := by
    have h5 : 5 ≤ 5 ^ (n - 1) := by
      calc 5 = 5 ^ 1 := by norm_num
        _ ≤ 5 ^ (n - 1) := Nat.pow_le_pow_right (by omega) (by omega)
    have h2 : 2 ^ n = 2 * 2 ^ (n - 1) := by
      cases n with | zero => omega | succ k => simp [pow_succ']
    have h10 : 10 ^ (n - 1) = 2 ^ (n - 1) * 5 ^ (n - 1) := by
      rw [show (10 : ℕ) = 2 * 5 by norm_num, mul_pow]
    rw [h2, h10]
    nlinarith [show 0 < 2 ^ (n - 1) by positivity]
  have h2 := repunit_ge_ten_pow n (by omega)
  omega

/-- Uniqueness of cube roots modulo `M0` when `3 * e3 = 1 + q * totient M0`. -/
private lemma cube_root_lower_bound (n u M0 u0 e3 q : ℕ)
    (hmod_u : u ^ 3 ≡ repunit n [MOD 2 ^ (n - 3) * 5 ^ n])
    (hM0dvd : M0 ∣ 2 ^ (n - 3) * 5 ^ n)
    (hcopM : Nat.Coprime u M0) (hcop0 : Nat.Coprime u0 M0)
    (he3 : 3 * e3 = 1 + q * Nat.totient M0)
    (hu0lt : u0 < M0) (hcube : u0 ^ 3 % M0 = repunit n % M0) :
    u0 ≤ u := by
  have hu3 : u ^ 3 ≡ u0 ^ 3 [MOD M0] := by
    have h1 := hmod_u.of_dvd hM0dvd
    rw [Nat.ModEq] at h1 ⊢
    rw [h1, hcube]
  have heuler_u : u ^ (q * Nat.totient M0) ≡ 1 [MOD M0] := by
    rw [mul_comm, pow_mul]
    simpa using (Nat.ModEq.pow_totient hcopM).pow q
  have heuler_0 : u0 ^ (q * Nat.totient M0) ≡ 1 [MOD M0] := by
    rw [mul_comm, pow_mul]
    simpa using (Nat.ModEq.pow_totient hcop0).pow q
  have hu_eq : u ≡ (u ^ 3) ^ e3 [MOD M0] := by
    rw [← pow_mul, he3, pow_add, pow_one]
    simpa using (heuler_u.mul_left u).symm
  have h0_eq : (u0 ^ 3) ^ e3 ≡ u0 [MOD M0] := by
    rw [← pow_mul, he3, pow_add, pow_one]
    simpa using heuler_0.mul_left u0
  have htot : u ≡ u0 [MOD M0] := (hu_eq.trans (hu3.pow e3)).trans h0_eq
  rw [Nat.ModEq, Nat.mod_eq_of_lt hu0lt] at htot
  have hle : u % M0 ≤ u := Nat.mod_le u M0
  omega

private lemma cube_case_13 (n u : ℕ) (hn : 5 < n) (hn13 : n ≤ 13)
    (h10_8 : 10 ^ n = 8 * (2 ^ (n - 3) * 5 ^ n))
    (hmod_u : u ^ 3 ≡ repunit n [MOD 2 ^ (n - 3) * 5 ^ n])
    (hcop2 : Nat.Coprime u 2) (hcop5 : Nat.Coprime u 5) :
    5 * 2 ^ n - 1 ≤ 2 * u := by
  have hM0eq : (125000 : ℕ) = 2 ^ 3 * 5 ^ 6 := by norm_num
  have hM0dvd : 125000 ∣ 2 ^ (n - 3) * 5 ^ n := by
    rw [hM0eq]; exact mul_dvd_mul (Nat.pow_dvd_pow 2 (by omega)) (Nat.pow_dvd_pow 5 (by omega))
  have hcopM : Nat.Coprime u 125000 := by
    rw [hM0eq]; exact Nat.Coprime.mul_right (hcop2.pow_right 3) (hcop5.pow_right 6)
  have hcop0 : Nat.Coprime 38471 125000 := by
    rw [hM0eq]
    exact Nat.Coprime.mul_right
      ((Nat.coprime_two_right.mpr (Nat.odd_iff.mpr (by norm_num))).pow_right 3)
      (((Nat.Prime.coprime_iff_not_dvd (by decide)).mpr (by norm_num)).symm.pow_right 6)
  have hcop9 : Nat.Coprime 9 125000 := by
    rw [hM0eq]
    exact Nat.Coprime.mul_right ((by decide : Nat.Coprime 9 2).pow_right 3)
      ((by decide : Nat.Coprime 9 5).pow_right 6)
  have hphi : Nat.totient 125000 = 50000 := by
    calc Nat.totient 125000
        = Nat.totient (2 ^ 3 * 5 ^ 6) := congrArg Nat.totient hM0eq
      _ = Nat.totient (2 ^ 3) * Nat.totient (5 ^ 6) :=
          Nat.totient_mul ((by decide : Nat.Coprime 2 5).pow 3 6)
      _ = (2 ^ (3 - 1) * (2 - 1)) * (5 ^ (6 - 1) * (5 - 1)) := by
          rw [Nat.totient_prime_pow (by decide) (by omega),
              Nat.totient_prime_pow (by decide) (by omega)]
      _ = 50000 := by norm_num
  have hr : repunit n % 125000 = 111111 :=
    repunit_mod_of_dvd_ten_pow n 125000 111111
      (dvd_trans hM0dvd (by rw [h10_8]; exact dvd_mul_left _ _))
      hcop9 (by norm_num) (by norm_num)
  have he3 : 3 * 16667 = 1 + 1 * Nat.totient 125000 :=
    Eq.trans (by norm_num) (congrArg (fun x => 1 + 1 * x) hphi.symm)
  have hcube : 38471 ^ 3 % 125000 = repunit n % 125000 :=
    Eq.trans (by norm_num) hr.symm
  have hle := cube_root_lower_bound n u 125000 38471 16667 1 hmod_u hM0dvd hcopM hcop0 he3
    (by norm_num) hcube
  have h2n : 2 ^ n ≤ 8192 := le_trans (Nat.pow_le_pow_right (by omega) hn13) (by norm_num)
  exact le_trans (Nat.sub_le _ _) (by linarith)

private lemma cube_case_16 (n u : ℕ) (hn : 13 < n) (hn16 : n ≤ 16)
    (h10_8 : 10 ^ n = 8 * (2 ^ (n - 3) * 5 ^ n))
    (hmod_u : u ^ 3 ≡ repunit n [MOD 2 ^ (n - 3) * 5 ^ n])
    (hcop2 : Nat.Coprime u 2) (hcop5 : Nat.Coprime u 5) :
    5 * 2 ^ n - 1 ≤ 2 * u := by
  have hM0eq : (1250000 : ℕ) = 2 ^ 4 * 5 ^ 7 := by norm_num
  have hM0dvd : 1250000 ∣ 2 ^ (n - 3) * 5 ^ n := by
    rw [hM0eq]; exact mul_dvd_mul (Nat.pow_dvd_pow 2 (by omega)) (Nat.pow_dvd_pow 5 (by omega))
  have hcopM : Nat.Coprime u 1250000 := by
    rw [hM0eq]; exact Nat.Coprime.mul_right (hcop2.pow_right 4) (hcop5.pow_right 7)
  have hcop0 : Nat.Coprime 788471 1250000 := by
    rw [hM0eq]
    exact Nat.Coprime.mul_right
      ((Nat.coprime_two_right.mpr (Nat.odd_iff.mpr (by norm_num))).pow_right 4)
      (((Nat.Prime.coprime_iff_not_dvd (by decide)).mpr (by norm_num)).symm.pow_right 7)
  have hcop9 : Nat.Coprime 9 1250000 := by
    rw [hM0eq]
    exact Nat.Coprime.mul_right ((by decide : Nat.Coprime 9 2).pow_right 4)
      ((by decide : Nat.Coprime 9 5).pow_right 7)
  have hphi : Nat.totient 1250000 = 500000 := by
    calc Nat.totient 1250000
        = Nat.totient (2 ^ 4 * 5 ^ 7) := congrArg Nat.totient hM0eq
      _ = Nat.totient (2 ^ 4) * Nat.totient (5 ^ 7) :=
          Nat.totient_mul ((by decide : Nat.Coprime 2 5).pow 4 7)
      _ = (2 ^ (4 - 1) * (2 - 1)) * (5 ^ (7 - 1) * (5 - 1)) := by
          rw [Nat.totient_prime_pow (by decide) (by omega),
              Nat.totient_prime_pow (by decide) (by omega)]
      _ = 500000 := by norm_num
  have hr : repunit n % 1250000 = 1111111 :=
    repunit_mod_of_dvd_ten_pow n 1250000 1111111
      (dvd_trans hM0dvd (by rw [h10_8]; exact dvd_mul_left _ _))
      hcop9 (by norm_num) (by norm_num)
  have he3 : 3 * 166667 = 1 + 1 * Nat.totient 1250000 :=
    Eq.trans (by norm_num) (congrArg (fun x => 1 + 1 * x) hphi.symm)
  have hcube : 788471 ^ 3 % 1250000 = repunit n % 1250000 :=
    Eq.trans (by norm_num) hr.symm
  have hle := cube_root_lower_bound n u 1250000 788471 166667 1 hmod_u hM0dvd hcopM hcop0 he3
    (by norm_num) hcube
  have h2n : 2 ^ n ≤ 65536 := le_trans (Nat.pow_le_pow_right (by omega) hn16) (by norm_num)
  exact le_trans (Nat.sub_le _ _) (by linarith)

private lemma cube_case_31 (n u : ℕ) (hn : 16 < n) (hn31 : n ≤ 31)
    (h10_8 : 10 ^ n = 8 * (2 ^ (n - 3) * 5 ^ n))
    (hmod_u : u ^ 3 ≡ repunit n [MOD 2 ^ (n - 3) * 5 ^ n])
    (hcop2 : Nat.Coprime u 2) (hcop5 : Nat.Coprime u 5) :
    5 * 2 ^ n - 1 ≤ 2 * u := by
  have hM0eq : (12500000000 : ℕ) = 2 ^ 8 * 5 ^ 11 := by norm_num
  have hM0dvd : 12500000000 ∣ 2 ^ (n - 3) * 5 ^ n := by
    rw [hM0eq]; exact mul_dvd_mul (Nat.pow_dvd_pow 2 (by omega)) (Nat.pow_dvd_pow 5 (by omega))
  have hcopM : Nat.Coprime u 12500000000 := by
    rw [hM0eq]; exact Nat.Coprime.mul_right (hcop2.pow_right 8) (hcop5.pow_right 11)
  have hcop0 : Nat.Coprime 12368288471 12500000000 := by
    rw [hM0eq]
    exact Nat.Coprime.mul_right
      ((Nat.coprime_two_right.mpr (Nat.odd_iff.mpr (by norm_num))).pow_right 8)
      (((Nat.Prime.coprime_iff_not_dvd (by decide)).mpr (by norm_num)).symm.pow_right 11)
  have hcop9 : Nat.Coprime 9 12500000000 := by
    rw [hM0eq]
    exact Nat.Coprime.mul_right ((by decide : Nat.Coprime 9 2).pow_right 8)
      ((by decide : Nat.Coprime 9 5).pow_right 11)
  have hphi : Nat.totient 12500000000 = 5000000000 := by
    calc Nat.totient 12500000000
        = Nat.totient (2 ^ 8 * 5 ^ 11) := congrArg Nat.totient hM0eq
      _ = Nat.totient (2 ^ 8) * Nat.totient (5 ^ 11) :=
          Nat.totient_mul ((by decide : Nat.Coprime 2 5).pow 8 11)
      _ = (2 ^ (8 - 1) * (2 - 1)) * (5 ^ (11 - 1) * (5 - 1)) := by
          rw [Nat.totient_prime_pow (by decide) (by omega),
              Nat.totient_prime_pow (by decide) (by omega)]
      _ = 5000000000 := by norm_num
  have hr : repunit n % 12500000000 = 11111111111 :=
    repunit_mod_of_dvd_ten_pow n 12500000000 11111111111
      (dvd_trans hM0dvd (by rw [h10_8]; exact dvd_mul_left _ _))
      hcop9 (by norm_num) (by norm_num)
  have he3 : 3 * 1666666667 = 1 + 1 * Nat.totient 12500000000 :=
    Eq.trans (by norm_num) (congrArg (fun x => 1 + 1 * x) hphi.symm)
  have hcube : 12368288471 ^ 3 % 12500000000 = repunit n % 12500000000 :=
    Eq.trans (by norm_num) hr.symm
  have hle := cube_root_lower_bound n u 12500000000 12368288471 1666666667 1 hmod_u hM0dvd hcopM hcop0
    he3 (by norm_num) hcube
  have h2n : 2 ^ n ≤ 2147483648 := le_trans (Nat.pow_le_pow_right (by omega) hn31) (by norm_num)
  exact le_trans (Nat.sub_le _ _) (by linarith)

private lemma cube_case_ge32 (n u : ℕ) (hn32 : 32 ≤ n)
    (h10_8 : 10 ^ n = 8 * (2 ^ (n - 3) * 5 ^ n))
    (hmod_u : u ^ 3 ≡ repunit n [MOD 2 ^ (n - 3) * 5 ^ n]) :
    5 * 2 ^ n - 1 ≤ 2 * u := by
  have hdvd : 2 ^ (n - 3) * 5 ^ n ∣ 9 * u ^ 3 + 1 := by
    have h9 := nine_mul_repunit n
    have h1 := hmod_u.mul_left 9
    have h2 := h1.add_right 1
    rw [h9] at h2
    rw [Nat.ModEq] at h2
    have hz : 10 ^ n % (2 ^ (n - 3) * 5 ^ n) = 0 := by
      rw [h10_8]; exact Nat.mul_mod_left 8 _
    rw [hz] at h2
    exact Nat.dvd_of_mod_eq_zero h2
  have hge : 2 ^ (n - 3) * 5 ^ n ≤ 9 * u ^ 3 + 1 := Nat.le_of_dvd (by positivity) hdvd
  have h54 : 1125 * 4 ^ n < 5 ^ n := by
    have haux : ∀ d : ℕ, 1125 * 4 ^ (32 + d) < 5 ^ (32 + d) := by
      intro d
      induction d with
      | zero => norm_num
      | succ d ih =>
        have h4s : 4 ^ (32 + (d + 1)) = 4 * 4 ^ (32 + d) := by
          rw [show 32 + (d + 1) = (32 + d) + 1 by omega, pow_succ']
        have h5s : 5 ^ (32 + (d + 1)) = 5 * 5 ^ (32 + d) := by
          rw [show 32 + (d + 1) = (32 + d) + 1 by omega, pow_succ']
        rw [h4s, h5s]
        have hassoc : 1125 * (4 * 4 ^ (32 + d)) = 4 * (1125 * 4 ^ (32 + d)) := by ring
        omega
    simpa only [Nat.add_sub_cancel' hn32] using haux (n - 32)
  have h2n3 : 8 * 2 ^ (n - 3) = 2 ^ n := by
    rw [show (8 : ℕ) = 2 ^ 3 by norm_num, ← pow_add, show 3 + (n - 3) = n by omega]
  have h4n : 4 ^ n = 2 ^ n * 2 ^ n := by rw [show (4 : ℕ) = 2 * 2 by norm_num, mul_pow]
  have hcube : 9 * (5 * 2 ^ n) ^ 3 = 1125 * 4 ^ n * 2 ^ n := by rw [h4n]; ring
  have hbig : 9 * (5 * 2 ^ n) ^ 3 < 8 * (2 ^ (n - 3) * 5 ^ n) := by
    rw [hcube, ← mul_assoc, h2n3, mul_comm (2 ^ n) (5 ^ n)]
    exact Nat.mul_lt_mul_of_pos_right h54 (by positivity)
  have h8u : 9 * (2 * u) ^ 3 + 8 = 8 * (9 * u ^ 3 + 1) := by ring
  have hlt : (5 * 2 ^ n - 1) ^ 3 < (2 * u) ^ 3 := by
    have h1 : 9 * (5 * 2 ^ n) ^ 3 < 9 * (2 * u) ^ 3 + 8 := by linarith
    have h2 : (5 * 2 ^ n) ^ 3 ≤ (2 * u) ^ 3 := by omega
    have hpos5 : 1 ≤ 5 * 2 ^ n := Nat.one_le_iff_ne_zero.mpr (by positivity)
    have h3 : (5 * 2 ^ n - 1) ^ 3 < (5 * 2 ^ n) ^ 3 :=
      Nat.pow_lt_pow_left (by omega) (by omega)
    exact lt_of_lt_of_le h3 h2
  by_contra hcontr
  have hle2 : 2 * u ≤ 5 * 2 ^ n - 1 := by omega
  have hpowle : (2 * u) ^ 3 ≤ (5 * 2 ^ n - 1) ^ 3 := Nat.pow_le_pow_left hle2 3
  omega

private lemma cube_eight_lower_bound (n u : ℕ) (hn : 5 < n) (hu_odd : Odd u)
    (hmod : 8 * u ^ 3 ≡ 8 * repunit n [MOD 10 ^ n]) :
    5 * 2 ^ n - 1 ≤ 2 * u := by
  have h10_8 : 10 ^ n = 8 * (2 ^ (n - 3) * 5 ^ n) := by
    have h2 : 2 ^ n = 8 * 2 ^ (n - 3) := by
      rw [show (8 : ℕ) = 2 ^ 3 by norm_num, ← pow_add, show 3 + (n - 3) = n by omega]
    rw [show 10 ^ n = 2 ^ n * 5 ^ n by rw [show (10 : ℕ) = 2 * 5 by norm_num, mul_pow], h2, mul_assoc]
  have hmod_u : u ^ 3 ≡ repunit n [MOD 2 ^ (n - 3) * 5 ^ n] := by
    rw [Nat.ModEq, h10_8, Nat.mul_mod_mul_left, Nat.mul_mod_mul_left] at hmod
    rw [Nat.ModEq]; omega
  have hu5 : ¬ 5 ∣ u := by
    intro h5u
    have h5dvd : 5 ∣ 2 ^ (n - 3) * 5 ^ n := dvd_mul_of_dvd_right (dvd_pow_self 5 (by omega)) _
    have h := hmod_u.of_dvd h5dvd
    have hr5 : repunit n % 5 = 1 :=
      repunit_mod_of_dvd_ten_pow n 5 1
        (dvd_trans (by norm_num : 5 ∣ 10) (dvd_pow_self 10 (by omega)))
        (by decide) (by omega) (by norm_num)
    have hu35 : u ^ 3 % 5 = 0 := Nat.mod_eq_zero_of_dvd (dvd_pow h5u (by omega))
    rw [Nat.ModEq] at h; omega
  have hcop2 : Nat.Coprime u 2 := Nat.coprime_two_right.mpr hu_odd
  have hcop5 : Nat.Coprime u 5 := ((Nat.Prime.coprime_iff_not_dvd (by decide)).mpr hu5).symm
  by_cases hn13 : n ≤ 13
  · exact cube_case_13 n u hn hn13 h10_8 hmod_u hcop2 hcop5
  · by_cases hn16 : n ≤ 16
    · exact cube_case_16 n u (by omega) hn16 h10_8 hmod_u hcop2 hcop5
    · by_cases hn31 : n ≤ 31
      · exact cube_case_31 n u (by omega) hn31 h10_8 hmod_u hcop2 hcop5
      · exact cube_case_ge32 n u (by omega) h10_8 hmod_u

/-! ### Separated digit cases for `minimal_bound` (keeps each proof compact and fast) -/

private lemma pow4_mod5_cases (j : ℕ) : 4 ^ j % 5 = 1 ∨ 4 ^ j % 5 = 4 := by
  rcases Nat.even_or_odd j with ⟨u, rfl⟩ | ⟨u, rfl⟩
  · left
    have : 4 ^ (u + u) = 16 ^ u := by rw [← two_mul, pow_mul]; norm_num
    rw [this]
    have : (16 : ℕ) ≡ 1 [MOD 5] := by decide
    simpa [Nat.ModEq] using this.pow u
  · right
    have : 4 ^ (2 * u + 1) = 16 ^ u * 4 := by rw [pow_succ, pow_mul]; norm_num
    rw [this, Nat.mul_mod]
    have : (16 : ℕ) ≡ 1 [MOD 5] := by decide
    have hp : 16 ^ u % 5 = 1 := by simpa [Nat.ModEq] using this.pow u
    rw [hp]

private lemma pow9_mod16_cases (j : ℕ) : 9 ^ j % 16 = 1 ∨ 9 ^ j % 16 = 9 := by
  rcases Nat.even_or_odd j with ⟨u, rfl⟩ | ⟨u, rfl⟩
  · left
    have : 9 ^ (u + u) = 81 ^ u := by rw [← two_mul, pow_mul]; norm_num
    rw [this]
    have : (81 : ℕ) ≡ 1 [MOD 16] := by decide
    simpa [Nat.ModEq] using this.pow u
  · right
    have : 9 ^ (2 * u + 1) = 81 ^ u * 9 := by rw [pow_succ, pow_mul]; norm_num
    rw [this, Nat.mul_mod]
    have : (81 : ℕ) ≡ 1 [MOD 16] := by decide
    have hp : 81 ^ u % 16 = 1 := by simpa [Nat.ModEq] using this.pow u
    rw [hp]

private lemma odd_pow_mod_decomp (m t M : ℕ) :
    m ^ (2 * t + 1) % M = (m % M * ((m % M * (m % M)) % M) ^ t) % M := by
  have h1 : m ^ (2 * t + 1) = m * (m * m) ^ t := by rw [pow_succ', pow_mul, sq]
  rw [h1]
  have hm' : m ≡ m % M [MOD M] := (Nat.mod_modEq m M).symm
  have hsq' : m * m ≡ (m % M * (m % M)) % M [MOD M] :=
    (hm'.mul hm').trans (Nat.mod_modEq _ M).symm
  exact hm'.mul (hsq'.pow t)

private lemma dvd_sub_one_of_mod_eq_one (x M : ℕ) (_hM : 1 < M) (hx : x % M = 1) : M ∣ x - 1 := by
  have hdiv := Nat.div_add_mod x M
  refine ⟨x / M, ?_⟩
  omega

private lemma not_dvd_sub_one_of_mod_ne_one (x M : ℕ) (hx1 : 1 ≤ x) (hM : 1 < M) (hx : x % M ≠ 1) :
    ¬ M ∣ x - 1 := by
  rintro ⟨q, hq⟩
  have hx' : x = M * q + 1 := by omega
  rw [hx', Nat.mul_add_mod, Nat.mod_eq_of_lt hM] at hx
  exact hx rfl

private lemma mod_eq_one_of_dvd_sub_one (x M : ℕ) (hx1 : 1 ≤ x) (hM : 1 < M) (hdvd : M ∣ x - 1) :
    x % M = 1 := by
  obtain ⟨q, hq⟩ := hdvd
  have hx' : x = M * q + 1 := by omega
  rw [hx', Nat.mul_add_mod, Nat.mod_eq_of_lt hM]

private lemma case_d1 (n m k : ℕ) (hn : 5 < n) (hm1 : 1 < m) (hk1 : 1 ≤ k)
    (hmk16 : m ^ k % 16 = 7) (hmk25 : m ^ k % 25 = 11)
    (hr_succ16 : repunit (n + 1) % 16 = 7) (hr_succ5 : repunit (n + 1) % 5 = 1) :
    ∃ K : ℕ, 1 ≤ K ∧ endsWithIdenticalDigits (m ^ K) (n + 1) := by
  have hm_odd : Odd m := by
    rw [Nat.odd_iff]
    by_contra hev
    have : 2 ∣ m ^ k := dvd_pow (show 2 ∣ m by omega) (by omega)
    omega
  have hk_odd : Odd k := by
    rw [Nat.odd_iff]
    by_contra hev
    obtain ⟨j, rfl⟩ : ∃ j, k = 2 * j := ⟨k / 2, by omega⟩
    have hmj : Odd (m ^ j) := hm_odd.pow
    rw [Nat.odd_iff] at hmj
    have hsq : (m ^ j) ^ 2 % 4 = 1 := by
      have : m ^ j % 4 = 1 ∨ m ^ j % 4 = 3 := by omega
      rw [sq, Nat.mul_mod]; rcases this with h | h <;> rw [h]
    rw [mul_comm 2 j, pow_mul] at hmk16; omega
  have hm16 : m % 16 = 7 := by
    rcases hk_odd with ⟨t, rfl⟩
    rw [odd_pow_mod_decomp m t 16] at hmk16
    have hodd16 : m % 16 = 1 ∨ m % 16 = 3 ∨ m % 16 = 5 ∨ m % 16 = 7 ∨
        m % 16 = 9 ∨ m % 16 = 11 ∨ m % 16 = 13 ∨ m % 16 = 15 := by
      rw [Nat.odd_iff] at hm_odd; omega
    rcases hodd16 with h | h | h | h | h | h | h | h
    · rw [h] at hmk16; norm_num at hmk16
    · rw [h] at hmk16; norm_num at hmk16
      rw [Nat.mul_mod] at hmk16; rcases pow9_mod16_cases t with ht | ht <;> (rw [ht] at hmk16; omega)
    · rw [h] at hmk16; norm_num at hmk16
      rw [Nat.mul_mod] at hmk16; rcases pow9_mod16_cases t with ht | ht <;> (rw [ht] at hmk16; omega)
    · exact h
    · rw [h] at hmk16; norm_num at hmk16
    · rw [h] at hmk16; norm_num at hmk16
      rw [Nat.mul_mod] at hmk16; rcases pow9_mod16_cases t with ht | ht <;> (rw [ht] at hmk16; omega)
    · rw [h] at hmk16; norm_num at hmk16
      rw [Nat.mul_mod] at hmk16; rcases pow9_mod16_cases t with ht | ht <;> (rw [ht] at hmk16; omega)
    · rw [h] at hmk16; norm_num at hmk16
  have hm5 : m % 5 = 1 := by
    have hmk5 : m ^ k % 5 = 1 := by omega
    rcases hk_odd with ⟨t, rfl⟩
    rw [odd_pow_mod_decomp m t 5] at hmk5
    have hm5c : m % 5 = 0 ∨ m % 5 = 1 ∨ m % 5 = 2 ∨ m % 5 = 3 ∨ m % 5 = 4 := by omega
    rcases hm5c with h | h | h | h | h
    · rw [h] at hmk5; norm_num at hmk5
    · exact h
    · rw [h] at hmk5; norm_num at hmk5
      rw [Nat.mul_mod] at hmk5; rcases pow4_mod5_cases t with ht | ht <;> (rw [ht] at hmk5; omega)
    · rw [h] at hmk5; norm_num at hmk5
      rw [Nat.mul_mod] at hmk5; rcases pow4_mod5_cases t with ht | ht <;> (rw [ht] at hmk5; omega)
    · rw [h] at hmk5; norm_num at hmk5
  have hm25 : m % 25 ≠ 1 := by
    intro h1
    have h : m ≡ 1 [MOD 25] := by show m % 25 = 1 % 25; omega
    have hp := h.pow k; rw [Nat.ModEq, one_pow] at hp; omega
  have hcop10 : Nat.Coprime m 10 := by
    show Nat.Coprime m (2 * 5)
    rw [Nat.coprime_mul_iff_right]
    exact ⟨Nat.coprime_two_right.mpr hm_odd,
      ((Nat.Prime.coprime_iff_not_dvd (by decide)).mpr (by omega)).symm⟩
  have h2a : 2 ^ 4 ∣ m ^ 2 - 1 := by
    have hm' : m ≡ 7 [MOD 16] := by rw [Nat.ModEq]; omega
    exact dvd_sub_one_of_mod_eq_one (m ^ 2) 16 (by omega) (Eq.trans (hm'.pow 2) (by norm_num))
  have h2a' : ¬ 2 ^ 5 ∣ m ^ 2 - 1 := by
    have hm32 : m ≡ 7 [MOD 32] ∨ m ≡ 23 [MOD 32] := by simp only [Nat.ModEq]; omega
    have h32 : m ^ 2 % 32 = 17 := by
      rcases hm32 with h | h
      · exact Eq.trans (h.pow 2) (by norm_num)
      · exact Eq.trans (h.pow 2) (by norm_num)
    exact not_dvd_sub_one_of_mod_ne_one (m ^ 2) 32 (Nat.one_le_pow 2 m (by omega)) (by omega) (by omega)
  have h5a : 5 ∣ m ^ 2 - 1 := by
    have hm' : m ≡ 1 [MOD 5] := by rw [Nat.ModEq]; omega
    exact dvd_sub_one_of_mod_eq_one (m ^ 2) 5 (by omega) (Eq.trans (hm'.pow 2) (by norm_num))
  have h5a' : ¬ 25 ∣ m ^ 2 - 1 := by
    have hm25c : m ≡ 6 [MOD 25] ∨ m ≡ 11 [MOD 25] ∨ m ≡ 16 [MOD 25] ∨ m ≡ 21 [MOD 25] := by
      simp only [Nat.ModEq]; omega
    have hne : m ^ 2 % 25 ≠ 1 := by
      rcases hm25c with h | h | h | h
      · have : m ^ 2 % 25 = 11 := Eq.trans (h.pow 2) (by norm_num); omega
      · have : m ^ 2 % 25 = 21 := Eq.trans (h.pow 2) (by norm_num); omega
      · have : m ^ 2 % 25 = 6 := Eq.trans (h.pow 2) (by norm_num); omega
      · have : m ^ 2 % 25 = 16 := Eq.trans (h.pow 2) (by norm_num); omega
    exact not_dvd_sub_one_of_mod_ne_one (m ^ 2) 25 (Nat.one_le_pow 2 m (by omega)) (by omega) hne
  have hinit2 : m ^ 1 ≡ repunit (n + 1) [MOD 2 ^ 4] := by rw [pow_one, Nat.ModEq]; omega
  have hinit5 : m ^ 1 ≡ repunit (n + 1) [MOD 5] := by rw [pow_one, Nat.ModEq]; omega
  obtain ⟨K, hK1, hKge, hKmod⟩ := lift_mod_ten_pow m 2 1 4 (n + 1) (repunit (n + 1))
    hm1 hcop10 (by omega) (by omega) (by omega) h2a h2a' h5a h5a' hinit2 hinit5
  refine ⟨K, hK1, 1, by omega, hKge, ?_⟩
  rw [one_mul]; rw [Nat.ModEq] at hKmod
  have hrlt : repunit (n + 1) < 10 ^ (n + 1) := by have := nine_mul_repunit (n + 1); omega
  rwa [Nat.mod_eq_of_lt hrlt] at hKmod

private lemma mod5_23_and_odd (m k r : ℕ) (hk1 : 1 ≤ k) (hr : r = 2 ∨ r = 3)
    (hmk5 : m ^ k % 5 = r) : (m % 5 = 2 ∨ m % 5 = 3) ∧ Odd k := by
  have hm5_23 : m % 5 = 2 ∨ m % 5 = 3 := by
    have h1 : m % 5 = 0 ∨ m % 5 = 1 ∨ m % 5 = 2 ∨ m % 5 = 3 ∨ m % 5 = 4 := by omega
    rcases h1 with h | h | h | h | h
    · have : 5 ∣ m ^ k := dvd_pow (show 5 ∣ m by omega) (by omega)
      omega
    · have hm1' : m ≡ 1 [MOD 5] := by show m % 5 = 1 % 5; omega
      have hp := hm1'.pow k; rw [Nat.ModEq, one_pow] at hp; omega
    · exact Or.inl h
    · exact Or.inr h
    · have hm4' : m ≡ 4 [MOD 5] := by show m % 5 = 4 % 5; omega
      have hp := hm4'.pow k; rw [Nat.ModEq] at hp; rw [hp] at hmk5
      rcases pow4_mod5_cases k with h4 | h4 <;> omega
  refine ⟨hm5_23, ?_⟩
  rw [Nat.odd_iff]
  by_contra hev
  obtain ⟨j, rfl⟩ : ∃ j, k = 2 * j := ⟨k / 2, by omega⟩
  have hm25' : m ^ 2 % 5 = 4 := by
    rw [sq, Nat.mul_mod]; rcases hm5_23 with h | h <;> rw [h]
  have h1 : m ^ 2 ≡ 4 [MOD 5] := by show m ^ 2 % 5 = 4 % 5; omega
  have hp := h1.pow j; rw [Nat.ModEq] at hp
  rw [pow_mul] at hmk5
  rcases pow4_mod5_cases j with h4 | h4 <;> omega

private lemma case_d3 (n m k : ℕ) (hn : 5 < n) (hm1 : 1 < m) (hk1 : 1 ≤ k)
    (hmk16 : m ^ k % 16 = 5) (hmk25 : m ^ k % 25 = 8)
    (hr_succ16 : repunit (n + 1) % 16 = 7) (hr_succ5 : repunit (n + 1) % 5 = 1) :
    ∃ K : ℕ, 1 ≤ K ∧ endsWithIdenticalDigits (m ^ K) (n + 1) := by
  have hm_odd : Odd m := by
    rw [Nat.odd_iff]
    by_contra hev
    have : 2 ∣ m ^ k := dvd_pow (show 2 ∣ m by omega) (by omega)
    omega
  obtain ⟨hm5_23, hk_odd⟩ := mod5_23_and_odd m k 3 hk1 (Or.inr rfl) (by omega)
  have hm8 : m % 8 = 5 := by
    have h4d : 2 ^ 2 ∣ m ^ k - 1 := by omega
    have h8nd : ¬ 2 ^ 3 ∣ m ^ k - 1 := by omega
    rw [two_pow_dvd_pow_sub_one_iff m k 2 hk_odd hm_odd] at h4d
    rw [two_pow_dvd_pow_sub_one_iff m k 3 hk_odd hm_odd] at h8nd
    omega
  have hcop10 : Nat.Coprime m 10 := by
    show Nat.Coprime m (2 * 5)
    rw [Nat.coprime_mul_iff_right]
    exact ⟨Nat.coprime_two_right.mpr hm_odd,
      ((Nat.Prime.coprime_iff_not_dvd (by decide)).mpr (by omega)).symm⟩
  have h2a_mod : m ^ 4 % 16 = 1 := by
    have hm16' : m ≡ 5 [MOD 16] ∨ m ≡ 13 [MOD 16] := by simp only [Nat.ModEq]; omega
    rcases hm16' with h | h
    · exact Eq.trans (h.pow 4) (by norm_num)
    · exact Eq.trans (h.pow 4) (by norm_num)
  have h2a : 2 ^ 4 ∣ m ^ 4 - 1 := dvd_sub_one_of_mod_eq_one (m ^ 4) 16 (by omega) h2a_mod
  have h2a' : ¬ 2 ^ 5 ∣ m ^ 4 - 1 := by
    have hm32' : m ≡ 5 [MOD 32] ∨ m ≡ 13 [MOD 32] ∨ m ≡ 21 [MOD 32] ∨ m ≡ 29 [MOD 32] := by
      simp only [Nat.ModEq]; omega
    have h32 : m ^ 4 % 32 = 17 := by
      rcases hm32' with h | h | h | h
      · exact Eq.trans (h.pow 4) (by norm_num)
      · exact Eq.trans (h.pow 4) (by norm_num)
      · exact Eq.trans (h.pow 4) (by norm_num)
      · exact Eq.trans (h.pow 4) (by norm_num)
    exact not_dvd_sub_one_of_mod_ne_one (m ^ 4) 32 (Nat.one_le_pow 4 m (by omega)) (by omega) (by omega)
  have h5a_mod : m ^ 4 % 5 = 1 := by
    have hm5' : m ≡ 2 [MOD 5] ∨ m ≡ 3 [MOD 5] := by simp only [Nat.ModEq]; omega
    rcases hm5' with h | h
    · exact Eq.trans (h.pow 4) (by norm_num)
    · exact Eq.trans (h.pow 4) (by norm_num)
  have h5a : 5 ∣ m ^ 4 - 1 := dvd_sub_one_of_mod_eq_one (m ^ 4) 5 (by omega) h5a_mod
  have h5a' : ¬ 25 ∣ m ^ 4 - 1 := by
    intro h25
    have hm4 : m ^ 4 ≡ 1 [MOD 25] := by
      rw [Nat.ModEq, mod_eq_one_of_dvd_sub_one (m ^ 4) 25 (Nat.one_le_pow 4 m (by omega)) (by omega) h25]
    have hmk4 : (m ^ k) ^ 4 ≡ 1 [MOD 25] := by
      rw [← pow_mul, mul_comm k 4, pow_mul]; simpa using hm4.pow k
    have hmk_mod : m ^ k ≡ 8 [MOD 25] := by rw [Nat.ModEq]; omega
    have h8 : (m ^ k) ^ 4 % 25 = 21 := Eq.trans (hmk_mod.pow 4) (by norm_num)
    rw [Nat.ModEq] at hmk4; omega
  have hmk_k0_16 : m ^ (k % 4) ≡ m ^ k [MOD 16] := by
    have hdiv : k = k % 4 + 4 * (k / 4) := by omega
    have hm4_16 : m ^ 4 ≡ 1 [MOD 16] := by rw [Nat.ModEq, h2a_mod]
    conv_rhs => rw [hdiv, pow_add, pow_mul]
    simpa using (hm4_16.pow (k / 4)).mul_left (m ^ (k % 4)) |>.symm
  have hmk_k0_5 : m ^ (k % 4) ≡ m ^ k [MOD 5] := by
    have hdiv : k = k % 4 + 4 * (k / 4) := by omega
    have hm4_5 : m ^ 4 ≡ 1 [MOD 5] := by rw [Nat.ModEq, h5a_mod]
    conv_rhs => rw [hdiv, pow_add, pow_mul]
    simpa using (hm4_5.pow (k / 4)).mul_left (m ^ (k % 4)) |>.symm
  have hinit2 : m ^ (k % 4) ≡ 3 * repunit (n + 1) [MOD 2 ^ 4] := by
    refine hmk_k0_16.trans ?_
    rw [Nat.ModEq, hmk16, Nat.mul_mod, hr_succ16]
  have hinit5 : m ^ (k % 4) ≡ 3 * repunit (n + 1) [MOD 5] := by
    refine hmk_k0_5.trans ?_
    rw [Nat.ModEq, Nat.mul_mod, hr_succ5]; omega
  obtain ⟨K, hK1, hKge, hKmod⟩ := lift_mod_ten_pow m 4 (k % 4) 4 (n + 1) (3 * repunit (n + 1))
    hm1 hcop10 (by omega) (by omega) (by omega) h2a h2a' h5a h5a' hinit2 hinit5
  refine ⟨K, hK1, 3, by omega, hKge, ?_⟩
  rw [Nat.ModEq] at hKmod
  have hrlt : 3 * repunit (n + 1) < 10 ^ (n + 1) := by have := nine_mul_repunit (n + 1); omega
  rwa [Nat.mod_eq_of_lt hrlt] at hKmod

private lemma mod32_17_pow4 (m : ℕ) (hm1 : 1 < m) (hm32 : m % 32 = 17) :
    m ^ 4 % 64 = 1 ∧ 2 ^ 6 ∣ m ^ 4 - 1 ∧ ¬ 2 ^ 7 ∣ m ^ 4 - 1 := by
  have h128 : m ^ 4 % 128 = 65 := by
    have hm_eq : m = 17 + 32 * (m / 32) := by
      have hdm := Nat.div_add_mod m 32; omega
    set q := m / 32
    have hexp : m ^ 4 = 128 * (652 + 4913 * q + 13872 * q ^ 2 + 17408 * q ^ 3 + 8192 * q ^ 4) + 65 := by
      rw [hm_eq]; ring
    rw [hexp, Nat.mul_add_mod]
  have h2a_mod : m ^ 4 % 64 = 1 := by
    have h64 : (m ^ 4 % 128) % 64 = m ^ 4 % 64 := Nat.mod_mod_of_dvd (m ^ 4) (by decide)
    rw [h128] at h64
    exact h64.symm
  refine ⟨h2a_mod, dvd_sub_one_of_mod_eq_one (m ^ 4) 64 (by decide) h2a_mod,
    not_dvd_sub_one_of_mod_ne_one (m ^ 4) 128 (Nat.one_le_pow 4 m (Nat.zero_lt_of_lt hm1)) (by decide)
      (by rw [h128]; decide)⟩

private lemma mod5_23_pow4_not25 (m k : ℕ) (hm1 : 1 < m) (hm5_23 : m % 5 = 2 ∨ m % 5 = 3)
    (hmk25 : m ^ k % 25 = 2) :
    m ^ 4 % 5 = 1 ∧ 5 ∣ m ^ 4 - 1 ∧ ¬ 25 ∣ m ^ 4 - 1 := by
  have h5a_mod : m ^ 4 % 5 = 1 := by
    rcases hm5_23 with h | h
    · exact Eq.trans ((show m ≡ 2 [MOD 5] from h).pow 4) (by norm_num)
    · exact Eq.trans ((show m ≡ 3 [MOD 5] from h).pow 4) (by norm_num)
  refine ⟨h5a_mod, dvd_sub_one_of_mod_eq_one (m ^ 4) 5 (by decide) h5a_mod, ?_⟩
  intro h25
  have hm4 : m ^ 4 ≡ 1 [MOD 25] := by
    rw [Nat.ModEq, mod_eq_one_of_dvd_sub_one (m ^ 4) 25
      (Nat.one_le_pow 4 m (Nat.zero_lt_of_lt hm1)) (by decide) h25]
  have hmk4 : (m ^ k) ^ 4 ≡ 1 [MOD 25] := by
    rw [← pow_mul, mul_comm k 4, pow_mul]; simpa using hm4.pow k
  have hmk_mod : m ^ k ≡ 2 [MOD 25] := hmk25
  have h16 : (m ^ k) ^ 4 % 25 = 16 := Eq.trans (hmk_mod.pow 4) (by norm_num)
  rw [Nat.ModEq, h16] at hmk4
  exact absurd hmk4 (by decide)

private lemma case_d7 (n m k : ℕ) (hn : 5 < n) (hm1 : 1 < m) (hk1 : 1 ≤ k)
    (hmk64 : m ^ k % 64 = 49) (hmk25 : m ^ k % 25 = 2)
    (hr_succ64 : repunit (n + 1) % 64 = 7) (hr_succ5 : repunit (n + 1) % 5 = 1) :
    ∃ K : ℕ, 1 ≤ K ∧ endsWithIdenticalDigits (m ^ K) (n + 1) := by
  have hm_odd : Odd m := by
    rw [Nat.odd_iff]
    by_contra hev
    have : 2 ∣ m ^ k := dvd_pow (show 2 ∣ m by omega) (by omega)
    omega
  obtain ⟨hm5_23, hk_odd⟩ := mod5_23_and_odd m k 2 hk1 (Or.inl rfl) (by omega)
  have hm32 : m % 32 = 17 := by
    have h16d : 2 ^ 4 ∣ m ^ k - 1 := by omega
    have h32nd : ¬ 2 ^ 5 ∣ m ^ k - 1 := by omega
    rw [two_pow_dvd_pow_sub_one_iff m k 4 hk_odd hm_odd] at h16d
    rw [two_pow_dvd_pow_sub_one_iff m k 5 hk_odd hm_odd] at h32nd
    omega
  have hcop10 : Nat.Coprime m 10 := by
    show Nat.Coprime m (2 * 5)
    rw [Nat.coprime_mul_iff_right]
    exact ⟨Nat.coprime_two_right.mpr hm_odd,
      ((Nat.Prime.coprime_iff_not_dvd (by decide)).mpr (by omega)).symm⟩
  obtain ⟨h2a_mod, h2a, h2a'⟩ := mod32_17_pow4 m hm1 hm32
  obtain ⟨h5a_mod, h5a, h5a'⟩ := mod5_23_pow4_not25 m k hm1 hm5_23 hmk25
  have hmk_k0_64 : m ^ (k % 4) ≡ m ^ k [MOD 64] := by
    have hdiv : k = k % 4 + 4 * (k / 4) := by omega
    have hm4_64 : m ^ 4 ≡ 1 [MOD 64] := by rw [Nat.ModEq, h2a_mod]
    conv_rhs => rw [hdiv, pow_add, pow_mul]
    simpa using (hm4_64.pow (k / 4)).mul_left (m ^ (k % 4)) |>.symm
  have hmk_k0_5 : m ^ (k % 4) ≡ m ^ k [MOD 5] := by
    have hdiv : k = k % 4 + 4 * (k / 4) := by omega
    have hm4_5 : m ^ 4 ≡ 1 [MOD 5] := by rw [Nat.ModEq, h5a_mod]
    conv_rhs => rw [hdiv, pow_add, pow_mul]
    simpa using (hm4_5.pow (k / 4)).mul_left (m ^ (k % 4)) |>.symm
  have hinit2 : m ^ (k % 4) ≡ 7 * repunit (n + 1) [MOD 2 ^ 6] := by
    refine hmk_k0_64.trans ?_
    rw [Nat.ModEq, hmk64, Nat.mul_mod, hr_succ64]
  have hinit5 : m ^ (k % 4) ≡ 7 * repunit (n + 1) [MOD 5] := by
    refine hmk_k0_5.trans ?_
    rw [Nat.ModEq, Nat.mul_mod, hr_succ5]; omega
  obtain ⟨K, hK1, hKge, hKmod⟩ := lift_mod_ten_pow m 4 (k % 4) 6 (n + 1) (7 * repunit (n + 1))
    hm1 hcop10 (by omega) (by omega) (by omega) h2a h2a' h5a h5a' hinit2 hinit5
  refine ⟨K, hK1, 7, by omega, hKge, ?_⟩
  rw [Nat.ModEq] at hKmod
  have hrlt : 7 * repunit (n + 1) < 10 ^ (n + 1) := by have := nine_mul_repunit (n + 1); omega
  rwa [Nat.mod_eq_of_lt hrlt] at hKmod

private lemma case_d9 (n m k : ℕ) (hn : 5 < n) (hk1 : 1 ≤ k)
    (hmod : m ^ k % 10 ^ n = 9 * repunit n) :
    5 * 2 ^ n - 1 ≤ m := by
  have h9r := nine_mul_repunit n
  have h10dvd : 10 ^ n ∣ m ^ k + 1 := by
    have hmod1 : m ^ k % 10 ^ n = 10 ^ n - 1 := by omega
    have hpos : 1 ≤ 10 ^ n := Nat.one_le_pow n 10 (by omega)
    have hdiv := Nat.div_add_mod (m ^ k) (10 ^ n)
    refine ⟨m ^ k / 10 ^ n + 1, ?_⟩
    rw [mul_add, mul_one]; omega
  have h2ndvd : 2 ^ n ∣ m ^ k + 1 :=
    dvd_trans (by rw [show 10 ^ n = 2 ^ n * 5 ^ n by rw [show (10 : ℕ) = 2 * 5 by norm_num, mul_pow]]; exact dvd_mul_right _ _) h10dvd
  have h5dvd_mk : 5 ∣ m ^ k + 1 :=
    dvd_trans (dvd_trans (by decide : 5 ∣ 10) (dvd_pow_self 10 (by omega))) h10dvd
  have h4dvd_mk : 4 ∣ m ^ k + 1 :=
    dvd_trans (show 2 ^ 2 ∣ 2 ^ n from Nat.pow_dvd_pow 2 (by omega)) h2ndvd
  have hm_odd : Odd m := by
    rw [Nat.odd_iff]
    have h2mk : 2 ∣ m ^ k + 1 := dvd_trans (by decide : 2 ∣ 4) h4dvd_mk
    by_contra hev
    have : 2 ∣ m ^ k := dvd_pow (show 2 ∣ m by omega) (by omega)
    omega
  have hk_odd : Odd k := by
    rw [Nat.odd_iff]
    by_contra hev
    obtain ⟨j, rfl⟩ : ∃ j, k = 2 * j := ⟨k / 2, by omega⟩
    have hmj := hm_odd.pow (n := j)
    rw [Nat.odd_iff] at hmj
    have hsq : (m ^ j) ^ 2 % 4 = 1 := by
      have : m ^ j % 4 = 1 ∨ m ^ j % 4 = 3 := by omega
      rw [sq, Nat.mul_mod]; rcases this with h | h <;> rw [h]
    rw [mul_comm 2 j, pow_mul] at h4dvd_mk; omega
  have h2m : 2 ^ n ∣ m + 1 := (two_pow_dvd_pow_add_one_iff m k n hk_odd).mp h2ndvd
  have h5m : 5 ∣ m + 1 := by
    have hmk5 : m ^ k % 5 = 4 := by omega
    rcases hk_odd with ⟨t, rfl⟩
    rw [odd_pow_mod_decomp m t 5] at hmk5
    have hm5c : m % 5 = 0 ∨ m % 5 = 1 ∨ m % 5 = 2 ∨ m % 5 = 3 ∨ m % 5 = 4 := by omega
    rcases hm5c with h | h | h | h | h
    · rw [h] at hmk5; norm_num at hmk5
    · rw [h] at hmk5; norm_num at hmk5
    · rw [h] at hmk5; norm_num at hmk5
      rw [Nat.mul_mod] at hmk5; rcases pow4_mod5_cases t with ht | ht <;> (rw [ht] at hmk5; omega)
    · rw [h] at hmk5; norm_num at hmk5
      rw [Nat.mul_mod] at hmk5; rcases pow4_mod5_cases t with ht | ht <;> (rw [ht] at hmk5; omega)
    · omega
  have hcop : Nat.Coprime 5 (2 ^ n) := (by decide : Nat.Coprime 5 2).pow_right n
  have h52 : 5 * 2 ^ n ∣ m + 1 := hcop.mul_dvd_of_dvd_of_dvd h5m h2m
  have hle : 5 * 2 ^ n ≤ m + 1 := Nat.le_of_dvd (by omega) h52
  omega

private lemma minimal_bound (n m : ℕ) (hn : 5 < n) (hm1 : 1 < m)
    (hmax : maxIdenticalTrailingDigits m n) :
    10 * 2 ^ (n - 1) - 1 ≤ m := by
  have hm_eq : 10 * 2 ^ (n - 1) - 1 = 5 * 2 ^ n - 1 := by
    have : 2 ^ n = 2 * 2 ^ (n - 1) := by
      cases n with | zero => omega | succ k => simp [pow_succ']
    omega
  rw [hm_eq]
  obtain ⟨⟨k, hk1, d, hd10, _, hmod⟩, hupper⟩ := hmax
  change m ^ k % 10 ^ n = d * repunit n at hmod
  have hno_succ : ¬ ∃ K : ℕ, 1 ≤ K ∧ endsWithIdenticalDigits (m ^ K) (n + 1) := fun h => by
    have := hupper (n + 1) h; omega
  have h10_dvd : 10 ∣ 10 ^ n := dvd_pow_self 10 (by omega)
  have h25_dvd : 25 ∣ 10 ^ n := dvd_trans (by norm_num : 25 ∣ 10 ^ 2) (Nat.pow_dvd_pow 10 (by omega))
  have h64_dvd : 64 ∣ 10 ^ n := dvd_trans (by norm_num : 64 ∣ 10 ^ 6) (Nat.pow_dvd_pow 10 (by omega))
  have h16_dvd : 16 ∣ 10 ^ n := dvd_trans (by decide : 16 ∣ 64) h64_dvd
  have h4_dvd : 4 ∣ 10 ^ n := dvd_trans (by decide : 4 ∣ 64) h64_dvd
  have hr64 : repunit n % 64 = 7 :=
    repunit_mod_of_dvd_ten_pow n 64 7 h64_dvd (by decide) (by omega) (by norm_num)
  have hr16 : repunit n % 16 = 7 :=
    repunit_mod_of_dvd_ten_pow n 16 7 h16_dvd (by decide) (by omega) (by norm_num)
  have hr4 : repunit n % 4 = 3 :=
    repunit_mod_of_dvd_ten_pow n 4 3 h4_dvd (by decide) (by omega) (by norm_num)
  have hr25 : repunit n % 25 = 11 :=
    repunit_mod_of_dvd_ten_pow n 25 11 h25_dvd (by decide) (by omega) (by norm_num)
  have hr_succ64 : repunit (n + 1) % 64 = 7 :=
    repunit_mod_of_dvd_ten_pow (n + 1) 64 7
      (dvd_trans h64_dvd (Nat.pow_dvd_pow 10 (by omega))) (by decide) (by omega) (by norm_num)
  have hr_succ16 : repunit (n + 1) % 16 = 7 :=
    repunit_mod_of_dvd_ten_pow (n + 1) 16 7
      (dvd_trans h16_dvd (Nat.pow_dvd_pow 10 (by omega))) (by decide) (by omega) (by norm_num)
  have hr_succ5 : repunit (n + 1) % 5 = 1 :=
    repunit_mod_of_dvd_ten_pow (n + 1) 5 1
      (dvd_trans (dvd_trans (by decide : 5 ∣ 10) h10_dvd) (Nat.pow_dvd_pow 10 (by omega)))
      (by decide) (by omega) (by norm_num)
  interval_cases d
  · simp only [zero_mul] at hmod
    have h10m : 10 ∣ m := by
      have h10mk : 10 ∣ m ^ k := dvd_trans h10_dvd (Nat.dvd_of_mod_eq_zero hmod)
      have h2m : 2 ∣ m := (Nat.Prime.dvd_of_dvd_pow (by decide)) (dvd_trans (by decide : 2 ∣ 10) h10mk)
      have h5m : 5 ∣ m := (Nat.Prime.dvd_of_dvd_pow (by decide)) (dvd_trans (by decide : 5 ∣ 10) h10mk)
      exact (by decide : Nat.Coprime 2 5).mul_dvd_of_dvd_of_dvd h2m h5m
    exfalso; apply hno_succ
    refine ⟨n + 1, by omega, 0, by omega, ?_, ?_⟩
    · calc 10 ^ (n + 1 - 1) = 10 ^ n := by simp
        _ ≤ 10 ^ (n + 1) := Nat.pow_le_pow_right (by omega) (by omega)
        _ ≤ m ^ (n + 1) := Nat.pow_le_pow_left (Nat.le_of_dvd (by omega) h10m) (n + 1)
    · simp only [zero_mul]
      exact Nat.mod_eq_zero_of_dvd (pow_dvd_pow_of_dvd h10m (n + 1))
  · exfalso; apply hno_succ
    have hmk16 : m ^ k % 16 = 7 := by
      have h := mod_of_mod_ten_pow h16_dvd hmod
      rw [Nat.ModEq, one_mul, hr16] at h; exact h
    have hmk25 : m ^ k % 25 = 11 := by
      have h := mod_of_mod_ten_pow h25_dvd hmod
      rw [Nat.ModEq, one_mul, hr25] at h; exact h
    exact case_d1 n m k hn hm1 hk1 hmk16 hmk25 hr_succ16 hr_succ5
  · have hmk4 : m ^ k % 4 = 2 := by
      have h := mod_of_mod_ten_pow h4_dvd hmod
      rw [Nat.ModEq, Nat.mul_mod, hr4] at h; omega
    have h2m : 2 ∣ m := (Nat.Prime.dvd_of_dvd_pow (by decide)) (show 2 ∣ m ^ k by omega)
    have hk_eq : k = 1 := by
      by_contra hne
      have : 4 ∣ m ^ k := dvd_trans (show 4 ∣ m ^ 2 by rw [sq]; exact mul_dvd_mul h2m h2m)
        (pow_dvd_pow m (by omega))
      omega
    subst hk_eq; rw [pow_one] at hmod
    have hle : m % 10 ^ n ≤ m := Nat.mod_le m (10 ^ n)
    have hb := ten_pow_ge_bound n hn; omega
  · exfalso; apply hno_succ
    have hmk16 : m ^ k % 16 = 5 := by
      have h := mod_of_mod_ten_pow h16_dvd hmod
      rw [Nat.ModEq, Nat.mul_mod, hr16] at h; omega
    have hmk25 : m ^ k % 25 = 8 := by
      have h := mod_of_mod_ten_pow h25_dvd hmod
      rw [Nat.ModEq, Nat.mul_mod, hr25] at h; omega
    exact case_d3 n m k hn hm1 hk1 hmk16 hmk25 hr_succ16 hr_succ5
  · have hmk16 : m ^ k % 16 = 12 := by
      have h := mod_of_mod_ten_pow h16_dvd hmod
      rw [Nat.ModEq, Nat.mul_mod, hr16] at h; omega
    have h2m : 2 ∣ m := (Nat.Prime.dvd_of_dvd_pow (by decide)) (show 2 ∣ m ^ k by omega)
    have hk_lt3 : k < 3 := by
      by_contra hge3
      have : 8 ∣ m ^ k := dvd_trans (show 8 ∣ m ^ 3 by
        obtain ⟨u, rfl⟩ := h2m; refine ⟨u ^ 3, by ring⟩) (pow_dvd_pow m (by omega))
      omega
    rcases (show k = 1 ∨ k = 2 by omega) with rfl | rfl
    · rw [pow_one] at hmod
      have hle : m % 10 ^ n ≤ m := Nat.mod_le m (10 ^ n)
      have hb := ten_pow_ge_bound n hn; omega
    · obtain ⟨u, rfl⟩ := h2m
      rcases Nat.even_or_odd u with ⟨v, rfl⟩ | ⟨v, rfl⟩
      · have : (2 * (v + v)) ^ 2 = 16 * v ^ 2 := by ring
        rw [this] at hmk16; omega
      · have : (2 * (2 * v + 1)) ^ 2 = 16 * (v ^ 2 + v) + 4 := by ring
        rw [this] at hmk16; omega
  · have hmk25 : m ^ k % 25 = 5 := by
      have h := mod_of_mod_ten_pow h25_dvd hmod
      rw [Nat.ModEq, Nat.mul_mod, hr25] at h; omega
    have h5m : 5 ∣ m := (Nat.Prime.dvd_of_dvd_pow (by decide)) (show 5 ∣ m ^ k by omega)
    have hk_eq : k = 1 := by
      by_contra hne
      have : 25 ∣ m ^ k := dvd_trans (show 25 ∣ m ^ 2 by rw [sq]; exact mul_dvd_mul h5m h5m)
        (pow_dvd_pow m (by omega))
      omega
    subst hk_eq; rw [pow_one] at hmod
    have hle : m % 10 ^ n ≤ m := Nat.mod_le m (10 ^ n)
    have hb := ten_pow_ge_bound n hn; omega
  · have hmk4 : m ^ k % 4 = 2 := by
      have h := mod_of_mod_ten_pow h4_dvd hmod
      rw [Nat.ModEq, Nat.mul_mod, hr4] at h; omega
    have h2m : 2 ∣ m := (Nat.Prime.dvd_of_dvd_pow (by decide)) (show 2 ∣ m ^ k by omega)
    have hk_eq : k = 1 := by
      by_contra hne
      have : 4 ∣ m ^ k := dvd_trans (show 4 ∣ m ^ 2 by rw [sq]; exact mul_dvd_mul h2m h2m)
        (pow_dvd_pow m (by omega))
      omega
    subst hk_eq; rw [pow_one] at hmod
    have hle : m % 10 ^ n ≤ m := Nat.mod_le m (10 ^ n)
    have hb := ten_pow_ge_bound n hn; omega
  · exfalso; apply hno_succ
    have hmk64 : m ^ k % 64 = 49 := by
      have h := mod_of_mod_ten_pow h64_dvd hmod
      rw [Nat.ModEq, Nat.mul_mod, hr64] at h; omega
    have hmk25 : m ^ k % 25 = 2 := by
      have h := mod_of_mod_ten_pow h25_dvd hmod
      rw [Nat.ModEq, Nat.mul_mod, hr25] at h; omega
    exact case_d7 n m k hn hm1 hk1 hmk64 hmk25 hr_succ64 hr_succ5
  · have hmk16 : m ^ k % 16 = 8 := by
      have h := mod_of_mod_ten_pow h16_dvd hmod
      rw [Nat.ModEq, Nat.mul_mod, hr16] at h; omega
    have h2m : 2 ∣ m := (Nat.Prime.dvd_of_dvd_pow (by decide)) (show 2 ∣ m ^ k by omega)
    have hk_lt4 : k < 4 := by
      by_contra hge4
      have : 16 ∣ m ^ k := dvd_trans (show 16 ∣ m ^ 4 by
        obtain ⟨u, rfl⟩ := h2m; refine ⟨u ^ 4, by ring⟩) (pow_dvd_pow m (by omega))
      omega
    rcases (show k = 1 ∨ k = 2 ∨ k = 3 by omega) with rfl | rfl | rfl
    · rw [pow_one] at hmod
      have hle : m % 10 ^ n ≤ m := Nat.mod_le m (10 ^ n)
      have hb := ten_pow_ge_bound n hn; omega
    · obtain ⟨u, rfl⟩ := h2m
      rcases Nat.even_or_odd u with ⟨v, rfl⟩ | ⟨v, rfl⟩
      · have : (2 * (v + v)) ^ 2 = 16 * v ^ 2 := by ring
        rw [this] at hmk16; omega
      · have : (2 * (2 * v + 1)) ^ 2 = 16 * (v ^ 2 + v) + 4 := by ring
        rw [this] at hmk16; omega
    · obtain ⟨u, rfl⟩ := h2m
      have hu_odd : Odd u := by
        rw [Nat.odd_iff]
        by_contra hev
        obtain ⟨v, rfl⟩ : ∃ v, u = 2 * v := ⟨u / 2, by omega⟩
        have : (2 * (2 * v)) ^ 3 = 16 * (4 * v ^ 3) := by ring
        rw [this] at hmk16; omega
      have hmod8 : 8 * u ^ 3 ≡ 8 * repunit n [MOD 10 ^ n] := by
        have h1 : (2 * u) ^ 3 = 8 * u ^ 3 := by ring
        rw [h1] at hmod; rw [Nat.ModEq, hmod]
        have hrlt : 8 * repunit n < 10 ^ n := by have := nine_mul_repunit n; omega
        exact (Nat.mod_eq_of_lt hrlt).symm
      exact cube_eight_lower_bound n u hn hu_odd hmod8
  · exact case_d9 n m k hn hk1 hmod

lemma solve_a244364 :
    ∀ n : ℕ, 5 < n →
      maxIdenticalTrailingDigits (10 * 2 ^ (n - 1) - 1) n ∧
      (∀ m : ℕ, 1 < m → maxIdenticalTrailingDigits m n → 10 * 2 ^ (n - 1) - 1 ≤ m) :=
  fun n hn => ⟨target_achieves_max n hn, fun m hm1 hmax => minimal_bound n m hn hm1 hmax⟩

end OMA.P_oeis_a244364

theorem OMA.solution : type_of% @OMA.S_oeis_a244364.main :=
  OMA.P_oeis_a244364.solve_a244364
