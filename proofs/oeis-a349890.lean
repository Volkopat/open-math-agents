import OMAStatements.S_oeis_a349890
import Mathlib

/-
Proof outline. Write tri j = j(j+1)/2, D E = (4^E - 1)/3 and, for a level E,
V E j m = 4^E - D E - tri j - m * 2^E.
A row n with 2^E ≤ n < 2^(E+1) has T n (j+1) = V (E+1) j m with m = 2^(E+1) - n (T_block).
into: every term of a row n < 2^E is V E i m with i < 2^E and m ≥ 1.
onto: every V E i m ≥ 1 with i < 2^E and m ≥ 1 is a term of a row n < 2^E.
Both go by induction on E; level E goes to level E+1 by lift_even (m even, same column) and lift_odd
(m odd, the partner column 2^(E+1) - 1 - i). Distinct i < 2^E give distinct tri i modulo 2^E (tri_inj),
and every residue modulo 2^E is some tri i with i < 2^E (tri_surj).
-/

namespace OMA.A349890Proof

open OMA.S_oeis_a349890

/-- The triangular number `j (j + 1) / 2`. -/
def tri (j : ℕ) : ℤ := (j : ℤ) * ((j : ℤ) + 1) / 2

/-- `(4 ^ E - 1) / 3`. -/
def D (E : ℕ) : ℤ := ((4 : ℤ) ^ E - 1) / 3

/-- The value of class `j` at depth `m` on level `E`. -/
def V (E j m : ℕ) : ℤ := (4 : ℤ) ^ E - D E - tri j - (m : ℤ) * 2 ^ E

theorem two_tri (j : ℕ) : 2 * tri j = (j : ℤ) * ((j : ℤ) + 1) := by
  unfold tri
  exact Int.mul_ediv_cancel' (Int.even_mul_succ_self (j : ℤ)).two_dvd

theorem tri_eq (j : ℕ) : ((j + 1 : ℕ) : ℤ) * (((j + 1 : ℕ) : ℤ) - 1) / 2 = tri j := by
  unfold tri
  have h : ((j + 1 : ℕ) : ℤ) * (((j + 1 : ℕ) : ℤ) - 1) = (j : ℤ) * ((j : ℤ) + 1) := by
    push_cast
    ring
  rw [h]

theorem four_pow_mod (E : ℕ) : (4 : ℤ) ^ E % 3 = 1 := by
  induction E with
  | zero => norm_num
  | succ n ih =>
    rw [pow_succ]
    omega

theorem three_D (E : ℕ) : 3 * D E = (4 : ℤ) ^ E - 1 := by
  unfold D
  have h := four_pow_mod E
  generalize (4 : ℤ) ^ E = X at *
  omega

theorem D_succ (E : ℕ) : D (E + 1) = 4 * D E + 1 := by
  unfold D
  have h := four_pow_mod E
  rw [pow_succ]
  generalize (4 : ℤ) ^ E = X at *
  omega

theorem four_pow (E : ℕ) : (4 : ℤ) ^ E = 2 ^ E * 2 ^ E := by
  rw [← mul_pow]
  norm_num

theorem lt_two_pow' (n : ℕ) : n < 2 ^ n := by
  induction n with
  | zero => norm_num
  | succ k ih =>
    rw [pow_succ]
    omega

theorem e_block (E n : ℕ) (h1 : 2 ^ E ≤ n) (h2 : n < 2 ^ (E + 1)) : e n = E + 1 := by
  unfold e
  rw [Nat.log_eq_of_pow_le_of_lt_pow h1 h2]
  omega

theorem exists_block (n : ℕ) (hn : n ≠ 0) : ∃ E, 2 ^ E ≤ n ∧ n < 2 ^ (E + 1) :=
  ⟨Nat.log 2 n, Nat.pow_log_le_self 2 hn, Nat.lt_pow_succ_log_self (by norm_num) n⟩

theorem T_eq (n j : ℕ) : T n (j + 1) = (n : ℤ) * 2 ^ (e n) - D (e n) - tri j := by
  rw [← tri_eq j]
  rfl

theorem T_block (E n j m : ℕ) (hnm : n + m = 2 ^ (E + 1)) (hm1 : 1 ≤ m) (hm2 : m ≤ 2 ^ E) :
    T n (j + 1) = V (E + 1) j m := by
  have hp : 2 ^ (E + 1) = 2 * 2 ^ E := by ring
  rw [T_eq, e_block E n (by omega) (by omega)]
  unfold V
  have hc : (n : ℤ) + m = 2 ^ (E + 1) := by exact_mod_cast hnm
  rw [four_pow (E + 1)]
  linear_combination (2 : ℤ) ^ (E + 1) * hc

theorem tri_star (E j i : ℕ) (h : j + i + 1 = 2 ^ (E + 1)) :
    tri i = tri j + 2 * (2 : ℤ) ^ E * 2 ^ E - 2 * 2 ^ E * j - 2 ^ E := by
  have hc : (j : ℤ) + i + 1 = 2 ^ E * 2 := by
    rw [← pow_succ]
    exact_mod_cast h
  have hi : (i : ℤ) = 2 * 2 ^ E - 1 - j := by linarith
  have ti := two_tri i
  have tj := two_tri j
  rw [hi] at ti
  have key : 2 * tri i = 2 * (tri j + 2 * (2 : ℤ) ^ E * 2 ^ E - 2 * 2 ^ E * j - 2 ^ E) := by
    linear_combination ti - tj
  exact mul_left_cancel₀ (by norm_num : (2 : ℤ) ≠ 0) key

theorem lift_even (E j m : ℕ) : V (E + 1) j (2 ^ E + m) = V E j (2 * m) := by
  unfold V
  rw [D_succ]
  have h3 := three_D E
  rw [four_pow E] at h3
  push_cast
  rw [pow_succ (4 : ℤ) E, pow_succ (2 : ℤ) E, four_pow E]
  linarith

theorem lift_odd (E i m j : ℕ) (hij : i + j + 1 = 2 ^ (E + 1)) :
    V (E + 1) j (i + m + 1) = V E i (2 * m + 1) := by
  have hs := tri_star E i j hij
  unfold V
  rw [D_succ, hs]
  have h3 := three_D E
  rw [four_pow E] at h3
  push_cast
  rw [pow_succ (4 : ℤ) E, pow_succ (2 : ℤ) E, four_pow E]
  linarith

theorem small_mul (A y w : ℤ) (hA : 0 < A) (hy : y = A * w) (h1 : -A < y) (h2 : y < A) :
    y = 0 := by
  rcases lt_trichotomy w 0 with h0 | h0 | h0
  · exfalso
    have h0' : w ≤ -1 := by omega
    nlinarith
  · rw [hy, h0, mul_zero]
  · exfalso
    have h0' : 1 ≤ w := by omega
    nlinarith

theorem tri_inj (E i j : ℕ) (hi : i < 2 ^ E) (hj : j < 2 ^ E) (h : (2 : ℤ) ^ E ∣ tri i - tri j) :
    i = j := by
  obtain ⟨c, hc⟩ := h
  have ti := two_tri i
  have tj := two_tri j
  have key : ((i : ℤ) - j) * ((i : ℤ) + j + 1) = 2 ^ (E + 1) * c := by
    rw [pow_succ]
    linear_combination (-1 : ℤ) * ti + tj + 2 * hc
  have hA2 : (2 : ℤ) ^ (E + 1) = 2 * 2 ^ E := by ring
  have hA : (0 : ℤ) < 2 ^ E := by positivity
  have hi' : (i : ℤ) < 2 ^ E := by exact_mod_cast hi
  have hj' : (j : ℤ) < 2 ^ E := by exact_mod_cast hj
  have hi0 : (0 : ℤ) ≤ i := Nat.cast_nonneg i
  have hj0 : (0 : ℤ) ≤ j := Nat.cast_nonneg j
  rcases Int.even_or_odd ((i : ℤ) - j) with ⟨r, hr⟩ | ⟨r, hr⟩
  · have h2 : IsCoprime (2 : ℤ) ((i : ℤ) + j + 1) := ⟨-(r + j), 1, by linarith⟩
    have hcop : IsCoprime ((2 : ℤ) ^ (E + 1)) ((i : ℤ) + j + 1) := IsCoprime.pow_left h2
    obtain ⟨u, v, huv⟩ := hcop
    have hy : (i : ℤ) - j = 2 ^ (E + 1) * (u * ((i : ℤ) - j) + v * c) := by
      linear_combination (-((i : ℤ) - j)) * huv + v * key
    have h0 := small_mul (2 ^ (E + 1)) ((i : ℤ) - j) _ (by positivity) hy (by linarith)
      (by linarith)
    omega
  · have h2 : IsCoprime (2 : ℤ) ((i : ℤ) - j) := ⟨-r, 1, by linarith⟩
    have hcop : IsCoprime ((2 : ℤ) ^ (E + 1)) ((i : ℤ) - j) := IsCoprime.pow_left h2
    obtain ⟨u, v, huv⟩ := hcop
    have hy : (i : ℤ) + j + 1 = 2 ^ (E + 1) * (u * ((i : ℤ) + j + 1) + v * c) := by
      linear_combination (-((i : ℤ) + j + 1)) * huv + v * key
    have h0 := small_mul (2 ^ (E + 1)) ((i : ℤ) + j + 1) _ (by positivity) hy (by linarith)
      (by linarith)
    omega

theorem tri_surj (E : ℕ) (x : ℤ) : ∃ j, j < 2 ^ E ∧ (2 : ℤ) ^ E ∣ x - tri j := by
  induction E with
  | zero => exact ⟨0, by norm_num, by simp⟩
  | succ E ih =>
    obtain ⟨j, hj, q, hq⟩ := ih
    have hp : 2 ^ (E + 1) = 2 * 2 ^ E := by ring
    rcases Int.even_or_odd q with ⟨r, hr⟩ | ⟨r, hr⟩
    · refine ⟨j, by omega, r, ?_⟩
      rw [pow_succ]
      linear_combination hq + (2 : ℤ) ^ E * hr
    · obtain ⟨i, hi⟩ : ∃ i, j + i + 1 = 2 ^ (E + 1) := ⟨2 ^ (E + 1) - 1 - j, by omega⟩
      refine ⟨i, by omega, r + 1 - 2 ^ E + j, ?_⟩
      have hs := tri_star E j i hi
      rw [pow_succ]
      linear_combination hq - hs + (2 : ℤ) ^ E * hr

theorem V_inj (E i m i' m' : ℕ) (hi : i < 2 ^ E) (hi' : i' < 2 ^ E) (h : V E i m = V E i' m') :
    i = i' ∧ m = m' := by
  unfold V at h
  have hd : (2 : ℤ) ^ E ∣ tri i - tri i' := ⟨(m' : ℤ) - m, by linarith⟩
  have hii := tri_inj E i i' hi hi' hd
  subst hii
  refine ⟨rfl, ?_⟩
  have h2 : ((m : ℤ) - m') * 2 ^ E = 0 := by linarith
  rcases mul_eq_zero.mp h2 with h3 | h3
  · omega
  · exact absurd h3 (pow_ne_zero E (by norm_num))

theorem into (E : ℕ) : ∀ n j : ℕ, j < n → n < 2 ^ E →
    ∃ i m : ℕ, i < 2 ^ E ∧ 1 ≤ m ∧ T n (j + 1) = V E i m := by
  induction E with
  | zero =>
    intro n j hjn hn
    rw [pow_zero] at hn
    omega
  | succ E ih =>
    intro n j hjn hn
    have hp : 2 ^ (E + 1) = 2 * 2 ^ E := by ring
    by_cases hlt : n < 2 ^ E
    · obtain ⟨i, m, hi, hm, h⟩ := ih n j hjn hlt
      rcases Nat.even_or_odd m with ⟨c, hc⟩ | ⟨c, hc⟩
      · refine ⟨i, 2 ^ E + c, by omega, by omega, ?_⟩
        rw [h, lift_even, hc, two_mul]
      · refine ⟨2 ^ (E + 1) - 1 - i, i + c + 1, by omega, by omega, ?_⟩
        rw [h, hc, lift_odd E i c (2 ^ (E + 1) - 1 - i) (by omega)]
    · refine ⟨j, 2 ^ (E + 1) - n, by omega, by omega, ?_⟩
      exact T_block E n j (2 ^ (E + 1) - n) (by omega) (by omega) (by omega)

theorem onto (E : ℕ) : ∀ i m : ℕ, i < 2 ^ E → 1 ≤ m → 1 ≤ V E i m →
    ∃ n j : ℕ, j < n ∧ n < 2 ^ E ∧ T n (j + 1) = V E i m := by
  induction E with
  | zero =>
    intro i m hi hm hV
    have hi0 : i = 0 := by
      rw [pow_zero] at hi
      omega
    subst hi0
    have h0 : V 0 0 m = 1 - (m : ℤ) := by simp [V, D, tri]
    rw [h0] at hV
    omega
  | succ E ih =>
    intro i m hi hm hV
    have hp : 2 ^ (E + 1) = 2 * 2 ^ E := by ring
    by_cases hnew : m ≤ 2 ^ E ∧ i + m < 2 ^ (E + 1)
    · exact ⟨2 ^ (E + 1) - m, i, by omega, by omega,
        T_block E (2 ^ (E + 1) - m) i m (by omega) hm hnew.1⟩
    · by_cases hi2 : i < 2 ^ E
      · obtain ⟨c, rfl⟩ : ∃ c, m = 2 ^ E + c := ⟨m - 2 ^ E, by omega⟩
        rw [lift_even] at hV ⊢
        obtain ⟨n, j, h1, h2, h3⟩ := ih i (2 * c) hi2 (by omega) hV
        exact ⟨n, j, h1, by omega, h3⟩
      · obtain ⟨i', hi'⟩ : ∃ i', i' + i + 1 = 2 ^ (E + 1) := ⟨2 ^ (E + 1) - 1 - i, by omega⟩
        obtain ⟨c, rfl⟩ : ∃ c, m = i' + c + 1 := ⟨m - i' - 1, by omega⟩
        rw [lift_odd E i' c i hi'] at hV ⊢
        obtain ⟨n, j, h1, h2, h3⟩ := ih i' (2 * c + 1) (by omega) (by omega) hV
        exact ⟨n, j, h1, by omega, h3⟩

theorem T_pos (n k : ℕ) (hk1 : 1 ≤ k) (hkn : k ≤ n) : 1 ≤ T n k := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  obtain ⟨E, h1, h2⟩ := exists_block n (by omega)
  rw [T_eq, e_block E n h1 h2]
  have h3 := three_D (E + 1)
  have ht := two_tri j
  rw [four_pow (E + 1)] at h3
  have hp : (2 : ℤ) ^ (E + 1) = 2 * 2 ^ E := by ring
  have h2' : (n : ℤ) < 2 ^ (E + 1) := by exact_mod_cast h2
  rw [hp] at h3 h2' ⊢
  have h1' : (2 : ℤ) ^ E ≤ n := by exact_mod_cast h1
  have h2'' : (n : ℤ) + 1 ≤ 2 * 2 ^ E := by omega
  have hj : (j : ℤ) + 1 ≤ n := by exact_mod_cast hkn
  have hj0 : (0 : ℤ) ≤ j := Nat.cast_nonneg j
  have ha0 : (0 : ℤ) < 2 ^ E := by positivity
  have ha : (1 : ℤ) ≤ 2 ^ E := by omega
  nlinarith [mul_nonneg (sub_nonneg.mpr h1') (by linarith : (0 : ℤ) ≤ 2 * 2 ^ E - 1 - n),
    mul_nonneg ha0.le (sub_nonneg.mpr h1'),
    mul_nonneg (by linarith : (0 : ℤ) ≤ (n : ℤ) - 1 - j) (by linarith : (0 : ℤ) ≤ (n : ℤ) + j),
    mul_nonneg (by linarith : (0 : ℤ) ≤ 2 ^ E - 1) (by linarith : (0 : ℤ) ≤ 2 ^ E + 4)]

theorem inj_aux (E n k n' k' : ℕ) (hk1 : 1 ≤ k) (hkn : k ≤ n) (hk1' : 1 ≤ k') (hkn' : k' ≤ n')
    (hn : n < 2 ^ (E + 1)) (h1 : 2 ^ E ≤ n') (h2 : n' < 2 ^ (E + 1)) (h : T n k = T n' k') :
    n = n' ∧ k = k' := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  obtain ⟨j', rfl⟩ : ∃ j', k' = j' + 1 := ⟨k' - 1, by omega⟩
  have hp : 2 ^ (E + 1) = 2 * 2 ^ E := by ring
  obtain ⟨m', hm'⟩ : ∃ m', n' + m' = 2 ^ (E + 1) := ⟨2 ^ (E + 1) - n', by omega⟩
  rw [T_block E n' j' m' hm' (by omega) (by omega)] at h
  by_cases hlt : n < 2 ^ E
  · exfalso
    obtain ⟨i, m, hi, hm, hT⟩ := into E n j (by omega) hlt
    rw [hT] at h
    rcases Nat.even_or_odd m with ⟨c, rfl⟩ | ⟨c, rfl⟩
    · rw [← two_mul, ← lift_even] at h
      obtain ⟨h3, h4⟩ := V_inj (E + 1) i (2 ^ E + c) j' m' (by omega) (by omega) h
      omega
    · rw [← lift_odd E i c (2 ^ (E + 1) - 1 - i) (by omega)] at h
      obtain ⟨h3, h4⟩ :=
        V_inj (E + 1) (2 ^ (E + 1) - 1 - i) (i + c + 1) j' m' (by omega) (by omega) h
      omega
  · obtain ⟨m, hm⟩ : ∃ m, n + m = 2 ^ (E + 1) := ⟨2 ^ (E + 1) - n, by omega⟩
    rw [T_block E n j m hm (by omega) (by omega)] at h
    obtain ⟨h3, h4⟩ := V_inj (E + 1) j m j' m' (by omega) (by omega) h
    omega

theorem surj_aux (x : ℤ) (hx : 1 ≤ x) : ∃ n j : ℕ, j < n ∧ T n (j + 1) = x := by
  obtain ⟨E, hE⟩ : ∃ E : ℕ, (E : ℤ) = x := ⟨x.toNat, Int.toNat_of_nonneg (by omega)⟩
  obtain ⟨j, hj, q, hq⟩ := tri_surj E ((4 : ℤ) ^ E - D E - x)
  have h3 := three_D E
  have ht := two_tri j
  have hj' : (j : ℤ) + 1 ≤ 2 ^ E := by
    have hj2 : (j : ℤ) < 2 ^ E := by exact_mod_cast hj
    omega
  have hEa : (E : ℤ) + 1 ≤ 2 ^ E := by
    have hE2 : (E : ℤ) < 2 ^ E := by exact_mod_cast lt_two_pow' E
    omega
  have hj0 : (0 : ℤ) ≤ j := Nat.cast_nonneg j
  have hA : (0 : ℤ) < 2 ^ E := by positivity
  have hpos : 0 < (2 : ℤ) ^ E * q := by
    rw [← hq]
    rw [four_pow E] at h3 ⊢
    nlinarith [mul_nonneg (by linarith : (0 : ℤ) ≤ 2 ^ E - 1 - j)
      (by linarith : (0 : ℤ) ≤ 2 ^ E + j), sq_nonneg ((2 : ℤ) ^ E - 2)]
  have hq0 : 0 < q := by
    by_contra hcon
    have hcon' : q ≤ 0 := not_lt.mp hcon
    nlinarith
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, (m : ℤ) = q := ⟨q.toNat, Int.toNat_of_nonneg hq0.le⟩
  have hm1 : 1 ≤ m := by omega
  have hV : V E j m = x := by
    unfold V
    linarith
  obtain ⟨n, j', h1, -, h4⟩ := onto E j m hj hm1 (by rw [hV]; exact hx)
  exact ⟨n, j', h1, by rw [h4, hV]⟩

end OMA.A349890Proof

open OMA.S_oeis_a349890 OMA.A349890Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a349890.main := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨n, k⟩ ⟨hk1, hkn⟩
    exact T_pos n k hk1 hkn
  · rintro ⟨n, k⟩ ⟨hk1, hkn⟩ ⟨n', k'⟩ ⟨hk1', hkn'⟩ h
    have h' : T n k = T n' k' := h
    have hk1 : 1 ≤ k := hk1
    have hkn : k ≤ n := hkn
    have hk1' : 1 ≤ k' := hk1'
    have hkn' : k' ≤ n' := hkn'
    rcases le_total n n' with hle | hle
    · obtain ⟨E, h1, h2⟩ := exists_block n' (by omega)
      obtain ⟨hn, hk⟩ := inj_aux E n k n' k' hk1 hkn hk1' hkn' (by omega) h1 h2 h'
      rw [hn, hk]
    · obtain ⟨E, h1, h2⟩ := exists_block n (by omega)
      obtain ⟨hn, hk⟩ := inj_aux E n' k' n k hk1' hkn' hk1 hkn (by omega) h1 h2 h'.symm
      rw [hn, hk]
  · intro x hx
    have hx' : (1 : ℤ) ≤ x := hx
    obtain ⟨n, j, hjn, hT⟩ := surj_aux x hx'
    exact ⟨(n, j + 1), ⟨show 1 ≤ j + 1 by omega, show j + 1 ≤ n by omega⟩, hT⟩
