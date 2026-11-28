import OMAStatements.S_oeis_a024399

-- Problem: OEIS A024399 (statement with S(n) in ℤ and the floor taken in ℚ), Mathar's recurrence and g.f. for floor(e_3(S(n)) / e_1(S(n))), where S(n) is
-- the first N = n + 2 numbers 3i + 2. By induction on N (e_k(c :: s) = e_k(s) + c e_(k-1)(s)):
-- 2 e_1 = N (3N + 1), 8 e_2 = N (N - 1)(3N - 1)(3N + 2), 48 e_3 = N (N - 1)(N - 2)(3N + 1)(9N^2 - 3N - 8).
-- Hence 24 e_3 = e_1 T with T = n (n + 1)(9N^2 - 3N - 8), and T = 8 [n = 1 mod 3] (mod 24), so
-- 24 a(n) = T - 8 [n = 1 mod 3]. This quasi-polynomial satisfies the recurrence, and the g.f. follows.

namespace OMA.A024399

open OMA.S_oeis_a024399

lemma esymm_cons {R : Type*} [CommSemiring R] (c : R) (s : Multiset R) (k : ℕ) :
    (c ::ₘ s).esymm (k + 1) = s.esymm (k + 1) + c * s.esymm k := by
  simp [Multiset.esymm, Multiset.powersetCard_cons, Multiset.sum_map_mul_left]

def s (N : ℕ) : Multiset ℤ := (Multiset.range N).map (fun i : ℕ => 3 * (i : ℤ) + 2)

lemma s_succ (N : ℕ) : s (N + 1) = (3 * (N : ℤ) + 2) ::ₘ s N := by
  simp [s, Multiset.range_succ]

lemma closed (N : ℕ) :
    2 * ((s N).esymm 1 : ℤ) = N * (3 * N + 1) ∧
    8 * ((s N).esymm 2 : ℤ) = N * (N - 1) * (3 * N - 1) * (3 * N + 2) ∧
    48 * ((s N).esymm 3 : ℤ) = N * (N - 1) * (N - 2) * (3 * N + 1) * (9 * N ^ 2 - 3 * N - 8) := by
  induction N with
  | zero =>
    have z1 : (s 0).esymm 1 = 0 := by decide
    have z2 : (s 0).esymm 2 = 0 := by decide
    have z3 : (s 0).esymm 3 = 0 := by decide
    simp [z1, z2, z3]
  | succ N ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    have e0 : (s N).esymm 0 = 1 := by simp [Multiset.esymm]
    rw [s_succ, esymm_cons, esymm_cons, esymm_cons, e0]
    push_cast
    refine ⟨by linear_combination h1, by linear_combination h2 + 4 * (3 * (N : ℤ) + 2) * h1,
      by linear_combination h3 + 6 * (3 * (N : ℤ) + 2) * h2⟩

def ind (n : ℕ) : ℤ := if n % 3 = 1 then 1 else 0

def T (n : ℕ) : ℤ := (n : ℤ) * (n + 1) * (9 * (n + 2) ^ 2 - 3 * (n + 2) - 8)

lemma T_mod (n : ℕ) : (24 : ℤ) ∣ T n - 8 * ind n := by
  have key : ∀ x : ZMod 24, x * (x + 1) * (9 * (x + 2) ^ 2 - 3 * (x + 2) - 8) -
      8 * (if x.val % 3 = 1 then 1 else 0) = 0 := by decide
  have h := key (n : ZMod 24)
  rw [ZMod.val_natCast, Nat.mod_mod_of_dvd n (by norm_num : 3 ∣ 24)] at h
  have h' := (ZMod.intCast_zmod_eq_zero_iff_dvd (T n - 8 * ind n) 24).mp (by
    simp only [T, ind]
    push_cast
    split_ifs at h ⊢ <;> push_cast at h ⊢ <;> exact h)
  exact_mod_cast h'

lemma floor_lemma_q (E1 E3 Tn k r : ℤ) (hE : 0 < E1) (h : 24 * E3 = E1 * Tn) (hk : Tn = 24 * k + r)
    (hr0 : 0 ≤ r) (hr1 : r < 24) : ⌊(E3 : ℚ) / (E1 : ℚ)⌋ = k := by
  have hEq : (0 : ℚ) < E1 := by exact_mod_cast hE
  rw [Int.floor_eq_iff, le_div_iff₀ hEq, div_lt_iff₀ hEq]
  constructor
  · have : k * E1 ≤ E3 := by nlinarith [mul_nonneg hr0 hE.le]
    exact_mod_cast this
  · have : E3 < (k + 1) * E1 := by nlinarith [mul_lt_mul_of_pos_right hr1 hE]
    exact_mod_cast this

lemma floor_lemma (E1 E3 Tn k r : ℤ) (hE : 0 < E1) (h : 24 * E3 = E1 * Tn) (hk : Tn = 24 * k + r)
    (hr0 : 0 ≤ r) (hr1 : r < 24) : E3 / E1 = k := by
  have h1 : k ≤ E3 / E1 := by
    rw [Int.le_ediv_iff_mul_le hE]; nlinarith [mul_nonneg hr0 hE.le]
  have h2 : E3 / E1 < k + 1 := by
    rw [Int.ediv_lt_iff_lt_mul hE]; nlinarith [mul_lt_mul_of_pos_right hr1 hE]
  omega

lemma a_closed (n : ℕ) : 24 * (a n : ℤ) = T n - 8 * ind n := by
  obtain ⟨h1, -, h3⟩ := closed (n + 2)
  obtain ⟨k, hk⟩ := T_mod n
  have hS : S n = s (n + 2) := rfl
  have hE : (0 : ℤ) < ((s (n + 2)).esymm 1 : ℤ) := by push_cast at h1; nlinarith
  have hind : 0 ≤ ind n ∧ ind n ≤ 1 := by unfold ind; split_ifs <;> norm_num
  rw [show a n = ⌊(((s (n + 2)).esymm 3 : ℤ) : ℚ) / (((s (n + 2)).esymm 1 : ℤ) : ℚ)⌋ from rfl,
    floor_lemma_q _ _ (T n) k (8 * ind n) hE ?_ (by linarith) (by linarith) (by linarith)]
  · linarith
  · simp only [T]; push_cast at h1 h3 ⊢
    have h48 : 48 * ((s (n + 2)).esymm 3 : ℤ) = 2 * ((s (n + 2)).esymm 1 : ℤ) *
        ((n : ℤ) * (n + 1) * (9 * (n + 2) ^ 2 - 3 * (n + 2) - 8)) := by
      linear_combination h3 - ((n : ℤ) + 1) * n * (9 * ((n : ℤ) + 2) ^ 2 - 3 * ((n : ℤ) + 2) - 8) * h1
    linarith

lemma ind_rec (m : ℕ) : ind (m + 7) - 4 * ind (m + 6) + 6 * ind (m + 5) - 5 * ind (m + 4) +
    5 * ind (m + 3) - 6 * ind (m + 2) + 4 * ind (m + 1) - ind m = 0 := by
  unfold ind
  have h : m % 3 = 0 ∨ m % 3 = 1 ∨ m % 3 = 2 := by omega
  rcases h with h | h | h <;>
  simp only [show (m + 7) % 3 = (m + 1) % 3 by omega, show (m + 6) % 3 = m % 3 by omega,
    show (m + 5) % 3 = (m + 2) % 3 by omega, show (m + 4) % 3 = (m + 1) % 3 by omega,
    show (m + 3) % 3 = m % 3 by omega] <;>
  simp [h, show (m + 1) % 3 = (m % 3 + 1) % 3 by omega, show (m + 2) % 3 = (m % 3 + 2) % 3 by omega]

lemma rec (m : ℕ) : (a (m + 7) : ℤ) = 4 * a (m + 6) - 6 * a (m + 5) + 5 * a (m + 4) - 5 * a (m + 3) +
    6 * a (m + 2) - 4 * a (m + 1) + a m := by
  have h7 := a_closed (m + 7); have h6 := a_closed (m + 6); have h5 := a_closed (m + 5)
  have h4 := a_closed (m + 4); have h3 := a_closed (m + 3); have h2 := a_closed (m + 2)
  have h1 := a_closed (m + 1); have h0 := a_closed m
  have hi := ind_rec m
  simp only [T] at h7 h6 h5 h4 h3 h2 h1 h0
  push_cast at h7 h6 h5 h4 h3 h2 h1 h0
  have h24 : 24 * ((a (m + 7) : ℤ) - (4 * a (m + 6) - 6 * a (m + 5) + 5 * a (m + 4) - 5 * a (m + 3) +
      6 * a (m + 2) - 4 * a (m + 1) + a m)) = 0 := by
    linear_combination h7 - 4 * h6 + 6 * h5 - 5 * h4 + 5 * h3 - 6 * h2 + 4 * h1 - h0 - 8 * hi
  linarith

lemma val (n : ℕ) : (a n : ℤ) = (T n - 8 * ind n) / 24 := by
  rw [← a_closed n]; omega

end OMA.A024399

open PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a024399.main := by
  have hrec : ∀ n : ℕ, 7 < n → (OMA.S_oeis_a024399.a n : ℤ) = 4 * OMA.S_oeis_a024399.a (n - 1) -
      6 * OMA.S_oeis_a024399.a (n - 2) + 5 * OMA.S_oeis_a024399.a (n - 3) -
      5 * OMA.S_oeis_a024399.a (n - 4) + 6 * OMA.S_oeis_a024399.a (n - 5) -
      4 * OMA.S_oeis_a024399.a (n - 6) + OMA.S_oeis_a024399.a (n - 7) := by
    intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 7 := ⟨n - 7, by omega⟩
    simp only [show m + 7 - 1 = m + 6 by omega, show m + 7 - 2 = m + 5 by omega,
      show m + 7 - 3 = m + 4 by omega, show m + 7 - 4 = m + 3 by omega, show m + 7 - 5 = m + 2 by omega,
      show m + 7 - 6 = m + 1 by omega, show m + 7 - 7 = m by omega]
    exact OMA.A024399.rec m
  refine ⟨hrec, ?_⟩
  have hco : ∀ (f : PowerSeries ℤ) (c : ℤ) (k n : ℕ),
      coeff n (f * (C c * X ^ k)) = if k ≤ n then c * coeff (n - k) f else 0 := by
    intro f c k n
    rw [show f * (C c * X ^ k) = f * X ^ k * C c by ring, coeff_mul_C, coeff_mul_X_pow']
    split_ifs <;> simp [mul_comm]
  have hpoly : ((1 : PowerSeries ℤ) + X + X ^ 2) * (X - 1) ^ 5 =
      C 1 * X ^ 7 + C (-4) * X ^ 6 + C 6 * X ^ 5 + C (-5) * X ^ 4 + C 5 * X ^ 3 + C (-6) * X ^ 2 +
        C 4 * X ^ 1 + C (-1) * X ^ 0 := by
    simp only [map_ofNat, map_neg, map_one]; ring
  have hrhs : (X : PowerSeries ℤ) * (-5 - 11 * X - 7 * X ^ 2 - 5 * X ^ 3 + X ^ 4) =
      C (-5) * X ^ 1 + C (-11) * X ^ 2 + C (-7) * X ^ 3 + C (-5) * X ^ 4 + C 1 * X ^ 5 := by
    simp only [map_ofNat, map_neg, map_one]; ring
  have v : ∀ n, (OMA.S_oeis_a024399.a n : ℤ) = (OMA.A024399.T n - 8 * OMA.A024399.ind n) / 24 :=
    OMA.A024399.val
  rw [hpoly, hrhs]
  ext n
  simp only [mul_add, map_add, coeff_mk, coeff_C_mul_X_pow, hco]
  rcases n with _ | _ | _ | _ | _ | _ | _ | m
  all_goals try (simp [v, OMA.A024399.T, OMA.A024399.ind]; done)
  have h := OMA.A024399.rec m
  have hz : ∀ k, (if k = 0 then (0 : ℤ) else (OMA.S_oeis_a024399.a k : ℤ)) = OMA.S_oeis_a024399.a k := by
    intro k; split_ifs with hk
    · subst hk; simp [v, OMA.A024399.T, OMA.A024399.ind]
    · rfl
  try simp only [hz]
  simp only [show 7 ≤ m + 7 by omega, show 6 ≤ m + 7 by omega, show 5 ≤ m + 7 by omega,
    show 4 ≤ m + 7 by omega, show 3 ≤ m + 7 by omega, show 2 ≤ m + 7 by omega, show 1 ≤ m + 7 by omega,
    show 0 ≤ m + 7 by omega, if_true, show m + 7 - 7 = m by omega, show m + 7 - 6 = m + 1 by omega,
    show m + 7 - 5 = m + 2 by omega, show m + 7 - 4 = m + 3 by omega, show m + 7 - 3 = m + 4 by omega,
    show m + 7 - 2 = m + 5 by omega, show m + 7 - 1 = m + 6 by omega, Nat.sub_zero,
    show m + 7 ≠ 1 by omega, show m + 7 ≠ 2 by omega, show m + 7 ≠ 3 by omega, show m + 7 ≠ 4 by omega,
    show m + 7 ≠ 5 by omega, if_false]
  linear_combination -h
