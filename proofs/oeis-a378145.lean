import OMAStatements.S_oeis_a378145

-- Problem: A378145: Riordan triangle (1 + x * C(x), x * C(x)), where C(x) is g.f. of A000108.
-- Upstream: formal-conjectures statements/oeis-a378145.lean:0 (declaration OMA.S_oeis_a378145.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: C = 1 + X C^2. For a prefactor g let V(g,m,n,k) = [x^n] g (X C)^k C^m. Then
-- V(g,m+1,n,k) = V(g,m,n,k) + V(g,m+1,n,k+1) and V(g,m,n,k) = 0 for k > n, so a downward induction
-- and Pascal's rule give V(g,m+1,n,k) = Sum_i binomial(i+m,i) V(g,0,n,i+k). With g = 1 + X C,
-- V(g,0,n,k) = T(n,k) and V(g,m,n,k) = T(n+m,m+k): the first conjecture. With g = 1 the case
-- m = 1, k = 0 is [x^n] C^2 = catalan(n+1) = Sum_k (k+1) [x^n] (X C)^k, and
-- T(n,k) = [x^n] (X C)^k + [x^n] (X C)^(k+1) turns this into the second conjecture.

namespace G12A378145

open OMA.S_oeis_a378145

theorem l_hC : Cx = 1 + PowerSeries.X * Cx ^ 2 := by
  ext n
  rcases n with _ | n
  · rw [map_add, PowerSeries.coeff_one, if_pos rfl, PowerSeries.coeff_zero_X_mul, add_zero]
    simp only [Cx, PowerSeries.coeff_mk, catalan_zero, Nat.cast_one]
  · rw [map_add, PowerSeries.coeff_one, if_neg (show n + 1 ≠ 0 by omega), zero_add,
      PowerSeries.coeff_succ_X_mul, sq, PowerSeries.coeff_mul]
    simp only [Cx, PowerSeries.coeff_mk]
    exact_mod_cast catalan_succ' n

theorem l_h1 (n : ℕ) : PowerSeries.coeff (n + 1) Cx = (catalan (n + 1) : ℤ) := by
  simp only [Cx, PowerSeries.coeff_mk]

theorem l_h2 (n : ℕ) : PowerSeries.coeff (n + 1) Cx = PowerSeries.coeff n (Cx ^ 2) := by
  conv_lhs => rw [l_hC]
  rw [map_add, PowerSeries.coeff_one, if_neg (show n + 1 ≠ 0 by omega), zero_add,
    PowerSeries.coeff_succ_X_mul]

theorem l_DI (A B : ℕ → ℤ) (n : ℕ) (hz : B (n + 1) = 0)
    (hr : ∀ k, k ≤ n → B k = A k + B (k + 1)) :
    ∀ k, k ≤ n → B k = ∑ i ∈ Finset.range (n - k + 1), A (i + k) := by
  have key : ∀ d k, k + d = n → B k = ∑ i ∈ Finset.range (d + 1), A (i + k) := by
    intro d
    induction d with
    | zero =>
      intro k hk
      rw [hr k (by omega), show k + 1 = n + 1 by omega, hz, Finset.sum_range_succ,
        Finset.sum_range_zero, zero_add, zero_add, add_zero]
    | succ d ih =>
      intro k hk
      rw [hr k (by omega), ih (k + 1) (by omega),
        Finset.sum_range_succ' (fun i => A (i + k)) (d + 1)]
      have e : ∀ i, i + (k + 1) = i + 1 + k := fun i => by ring
      simp only [e, zero_add]
      ring
  intro k hk
  exact key (n - k) k (by omega)

theorem l_sumid (a : ℕ → ℤ) (ha0 : a 0 = 1) (ha2 : ∀ N : ℕ, a N + a (N + 1) = (N : ℤ) + 2)
    (c : ℕ → ℤ) (N : ℕ) : ∑ k ∈ Finset.range (N + 1), a k * (c k + c (k + 1)) =
      ∑ k ∈ Finset.range (N + 1), ((k : ℤ) + 1) * c k + a N * c (N + 1) := by
  induction N with
  | zero =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero,
      Finset.sum_range_zero, ha0]
    push_cast
    ring
  | succ N ih =>
    rw [Finset.sum_range_succ (fun k => a k * (c k + c (k + 1))) (N + 1),
      Finset.sum_range_succ (fun k => ((k : ℤ) + 1) * c k) (N + 1), ih]
    push_cast
    linear_combination c (N + 1) * ha2 N

theorem l_Vz (V : PowerSeries ℤ → ℕ → ℕ → ℕ → ℤ)
    (hV : ∀ g m n k, V g m n k = PowerSeries.coeff n (g * (PowerSeries.X * Cx) ^ k * Cx ^ m))
    (g : PowerSeries ℤ) (m n k : ℕ) (hnk : n < k) : V g m n k = 0 := by
  rw [hV, show g * (PowerSeries.X * Cx) ^ k * Cx ^ m =
      PowerSeries.X ^ k * (g * Cx ^ k * Cx ^ m) by ring,
    PowerSeries.coeff_X_pow_mul', if_neg (show ¬ (k ≤ n) by omega)]

theorem l_Vrec (V : PowerSeries ℤ → ℕ → ℕ → ℕ → ℤ)
    (hV : ∀ g m n k, V g m n k = PowerSeries.coeff n (g * (PowerSeries.X * Cx) ^ k * Cx ^ m))
    (g : PowerSeries ℤ) (m n k : ℕ) : V g (m + 1) n k = V g m n k + V g (m + 1) n (k + 1) := by
  have e : g * (PowerSeries.X * Cx) ^ k * Cx ^ (m + 1) =
      g * (PowerSeries.X * Cx) ^ k * Cx ^ m +
        g * (PowerSeries.X * Cx) ^ (k + 1) * Cx ^ (m + 1) := by
    linear_combination (g * (PowerSeries.X * Cx) ^ k * Cx ^ m) * l_hC
  rw [hV, hV, hV, e, map_add]

theorem l_V0T (V : PowerSeries ℤ → ℕ → ℕ → ℕ → ℤ)
    (hV : ∀ g m n k, V g m n k = PowerSeries.coeff n (g * (PowerSeries.X * Cx) ^ k * Cx ^ m))
    (n k : ℕ) : V (1 + PowerSeries.X * Cx) 0 n k = T n k := by
  unfold T
  rw [hV, pow_zero, mul_one]

theorem l_VT (V : PowerSeries ℤ → ℕ → ℕ → ℕ → ℤ)
    (hV : ∀ g m n k, V g m n k = PowerSeries.coeff n (g * (PowerSeries.X * Cx) ^ k * Cx ^ m))
    (m n k : ℕ) : V (1 + PowerSeries.X * Cx) m n k = T (n + m) (m + k) := by
  unfold T
  rw [hV, show (1 + PowerSeries.X * Cx) * (PowerSeries.X * Cx) ^ (m + k) =
      PowerSeries.X ^ m * ((1 + PowerSeries.X * Cx) * (PowerSeries.X * Cx) ^ k * Cx ^ m) by ring,
    PowerSeries.coeff_X_pow_mul]

theorem l_Tc (V : PowerSeries ℤ → ℕ → ℕ → ℕ → ℤ)
    (hV : ∀ g m n k, V g m n k = PowerSeries.coeff n (g * (PowerSeries.X * Cx) ^ k * Cx ^ m))
    (n k : ℕ) : T n k = V 1 0 n k + V 1 0 n (k + 1) := by
  have e : (1 + PowerSeries.X * Cx) * (PowerSeries.X * Cx) ^ k =
      1 * (PowerSeries.X * Cx) ^ k * Cx ^ 0 + 1 * (PowerSeries.X * Cx) ^ (k + 1) * Cx ^ 0 := by
    ring
  unfold T
  rw [e, map_add, hV, hV]

theorem l_cat (V : PowerSeries ℤ → ℕ → ℕ → ℕ → ℤ)
    (hV : ∀ g m n k, V g m n k = PowerSeries.coeff n (g * (PowerSeries.X * Cx) ^ k * Cx ^ m))
    (n : ℕ) : V 1 2 n 0 = (catalan (n + 1) : ℤ) := by
  rw [hV, pow_zero, mul_one, one_mul, ← l_h2 n, l_h1 n]

theorem l_Wz (V W : PowerSeries ℤ → ℕ → ℕ → ℕ → ℤ)
    (hV : ∀ g m n k, V g m n k = PowerSeries.coeff n (g * (PowerSeries.X * Cx) ^ k * Cx ^ m))
    (hW : ∀ g m n k,
      W g m n k = ∑ i ∈ Finset.range (n - k + 1), ((i + m).choose i : ℤ) * V g 0 n (i + k))
    (g : PowerSeries ℤ) (m n : ℕ) : W g m n (n + 1) = 0 := by
  rw [hW, show n - (n + 1) + 1 = 0 + 1 by omega, Finset.sum_range_succ, Finset.sum_range_zero,
    l_Vz V hV g 0 n (0 + (n + 1)) (by omega), mul_zero, zero_add]

theorem l_Wrec (V W : PowerSeries ℤ → ℕ → ℕ → ℕ → ℤ)
    (hV : ∀ g m n k, V g m n k = PowerSeries.coeff n (g * (PowerSeries.X * Cx) ^ k * Cx ^ m))
    (hW : ∀ g m n k,
      W g m n k = ∑ i ∈ Finset.range (n - k + 1), ((i + m).choose i : ℤ) * V g 0 n (i + k))
    (g : PowerSeries ℤ) (m n k : ℕ) (hk : k ≤ n) :
    W g (m + 1) n k = W g m n k + W g (m + 1) n (k + 1) := by
  rcases Nat.lt_or_ge k n with hlt | hge
  swap
  · rw [show k + 1 = n + 1 by omega, l_Wz V W hV hW g (m + 1) n, add_zero, hW, hW,
      show n - k + 1 = 0 + 1 by omega, Finset.sum_range_succ, Finset.sum_range_zero,
      Finset.sum_range_succ, Finset.sum_range_zero]
    simp only [Nat.choose_zero_right]
  obtain ⟨d, hd⟩ : ∃ d, n - k = d := ⟨_, rfl⟩
  rw [hW, hW, hW, show n - (k + 1) + 1 = d by omega, hd,
    Finset.sum_range_succ' (fun i => ((i + (m + 1)).choose i : ℤ) * V g 0 n (i + k)) d,
    Finset.sum_range_succ' (fun i => ((i + m).choose i : ℤ) * V g 0 n (i + k)) d]
  have e : ∀ i, ((i + 1 + (m + 1)).choose (i + 1) : ℤ) * V g 0 n (i + 1 + k) =
      ((i + 1 + m).choose (i + 1) : ℤ) * V g 0 n (i + 1 + k) +
        ((i + (m + 1)).choose i : ℤ) * V g 0 n (i + (k + 1)) := by
    intro i
    rw [show i + 1 + (m + 1) = i + m + 1 + 1 by ring, Nat.choose_succ_succ',
      show i + 1 + m = i + m + 1 by ring, show i + (m + 1) = i + m + 1 by ring,
      show i + (k + 1) = i + 1 + k by ring]
    push_cast
    ring
  rw [Finset.sum_congr rfl (fun i _ => e i), Finset.sum_add_distrib]
  simp only [Nat.choose_zero_right, Nat.cast_one]
  ring

theorem l_Q (V W : PowerSeries ℤ → ℕ → ℕ → ℕ → ℤ)
    (hV : ∀ g m n k, V g m n k = PowerSeries.coeff n (g * (PowerSeries.X * Cx) ^ k * Cx ^ m))
    (hW : ∀ g m n k,
      W g m n k = ∑ i ∈ Finset.range (n - k + 1), ((i + m).choose i : ℤ) * V g 0 n (i + k)) :
    ∀ m g n k, k ≤ n → V g (m + 1) n k = W g m n k := by
  intro m
  induction m with
  | zero =>
    intro g n k hk
    rw [l_DI (V g 0 n) (V g (0 + 1) n) n (l_Vz V hV g (0 + 1) n (n + 1) (by omega))
      (fun j _ => l_Vrec V hV g 0 n j) k hk, hW]
    apply Finset.sum_congr rfl
    intro i _
    rw [Nat.add_zero, Nat.choose_self, Nat.cast_one, one_mul]
  | succ m ih =>
    intro g n k hk
    rw [l_DI (V g (m + 1) n) (V g (m + 1 + 1) n) n
        (l_Vz V hV g (m + 1 + 1) n (n + 1) (by omega)) (fun j _ => l_Vrec V hV g (m + 1) n j) k hk,
      l_DI (W g m n) (W g (m + 1) n) n (l_Wz V W hV hW g (m + 1) n)
        (fun j hj => l_Wrec V W hV hW g m n j hj) k hk]
    apply Finset.sum_congr rfl
    intro i hi
    have hi' := Finset.mem_range.mp hi
    exact ih g n (i + k) (by omega)

end G12A378145

open OMA.S_oeis_a378145 G12A378145 in
theorem OMA.solution : type_of% @OMA.S_oeis_a378145.main := by
  obtain ⟨V, hV⟩ : ∃ V : PowerSeries ℤ → ℕ → ℕ → ℕ → ℤ, ∀ g m n k,
      V g m n k = PowerSeries.coeff n (g * (PowerSeries.X * Cx) ^ k * Cx ^ m) :=
    ⟨_, fun _ _ _ _ => rfl⟩
  obtain ⟨W, hW⟩ : ∃ W : PowerSeries ℤ → ℕ → ℕ → ℕ → ℤ, ∀ g m n k,
      W g m n k = ∑ i ∈ Finset.range (n - k + 1), ((i + m).choose i : ℤ) * V g 0 n (i + k) :=
    ⟨_, fun _ _ _ _ => rfl⟩
  obtain ⟨a, ha⟩ : ∃ a : ℕ → ℤ, ∀ k, a k = ((1 + k / 2 : ℕ) : ℤ) := ⟨_, fun _ => rfl⟩
  have ha0 : a 0 = 1 := by
    rw [ha]
    norm_num
  have ha2 : ∀ N : ℕ, a N + a (N + 1) = (N : ℤ) + 2 := by
    intro N
    rw [ha, ha]
    omega
  refine ⟨fun n k m hk hm => ?_, fun n => ?_⟩
  · obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    rw [← l_VT V hV, l_Q V W hV hW m (1 + PowerSeries.X * Cx) n k hk, hW]
    apply Finset.sum_congr rfl
    intro i _
    rw [show i + (m + 1) - 1 = i + m by omega, l_V0T V hV]
  · have e1 : ∑ k ∈ Finset.range (n + 1), ((1 + k / 2 : ℕ) : ℤ) * T n k =
        ∑ k ∈ Finset.range (n + 1), a k * (V 1 0 n k + V 1 0 n (k + 1)) := by
      apply Finset.sum_congr rfl
      intro k _
      rw [ha k, l_Tc V hV n k]
    have e2 := l_Q V W hV hW 1 1 n 0 (Nat.zero_le n)
    rw [show (1 : ℕ) + 1 = 2 from rfl, hW, Nat.sub_zero] at e2
    rw [e1, l_sumid a ha0 ha2 (V 1 0 n) n, l_Vz V hV 1 0 n (n + 1) (by omega), mul_zero, add_zero,
      ← l_cat V hV n, e2]
    apply Finset.sum_congr rfl
    intro i _
    rw [Nat.choose_succ_self_right, Nat.cast_add_one, Nat.add_zero i]
