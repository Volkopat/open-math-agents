import OMAStatements.S_oeis_a267632

-- Problem: A267632: Triangle T(n, k) read by rows: the k-th column of the n-th row lists the number of ways to select k distinct numbers (k >= 1) from [1..n] so that their sum is divisible by n.
-- Upstream: formal-conjectures statements/oeis-a267632.lean:0 (declaration OMA.S_oeis_a267632.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: let N(k, c) be the number of k-subsets S of I = [1, n] with n | sum(S) - c (in Z),
-- so T(n, k) = N(k, 0), and N(k, c) depends only on c mod n. Complement in I gives
-- N(k, c) = N(n - k, G - c) with G = sum(I) = n(n+1)/2, so T(n, n - k) = N(k, G). For odd n,
-- n | G. For n = 2^(m+1), the rotation x -> (x + t - 1) mod n + 1 of I adds k*t to the sum mod n,
-- so N(k, 0) = N(k, k*t); with k = 2^a*b, b odd, a <= m and t = 2^(m-a), k*t = 2^m*b and
-- k*t - G is divisible by n.

namespace P1A267632

open OMA.S_oeis_a267632

/-- Rotation of [1, n] by t. -/
def R (n t x : ℕ) : ℕ := (x + t - 1) % n + 1

/-- Rotation of a set. -/
def rot (n t : ℕ) (S : Finset ℕ) : Finset ℕ := S.image (R n t)

/-- Complement in [1, n]. -/
def cpl (n : ℕ) (S : Finset ℕ) : Finset ℕ := Finset.Icc 1 n \ S

/-- N n k c: the number of k-subsets S of [1, n] such that n divides (sum of S) - c. -/
def N (n k : ℕ) (c : ℤ) : ℕ :=
  (((Finset.Icc 1 n).powersetCard k).filter
    (fun S : Finset ℕ => (n : ℤ) ∣ (∑ x ∈ S, (x : ℤ)) - c)).card

theorem R_mem {n : ℕ} (t x : ℕ) (hn : 0 < n) : R n t x ∈ Finset.Icc 1 n := by
  have h := Nat.mod_lt (x + t - 1) hn
  rw [Finset.mem_Icc]
  unfold R
  omega

theorem R_inv {n t x : ℕ} (ht : t ≤ n) (hx : x ∈ Finset.Icc 1 n) :
    R n (n - t) (R n t x) = x := by
  rw [Finset.mem_Icc] at hx
  unfold R
  have e1 : (x + t - 1) % n + 1 + (n - t) - 1 = (x + t - 1) % n + (n - t) := by omega
  have e2 : x + t - 1 + (n - t) = x - 1 + n := by omega
  rw [e1, Nat.mod_add_mod, e2, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : x - 1 < n)]
  omega

theorem R_mod {n t x : ℕ} (hx : 1 ≤ x) : (n : ℤ) ∣ (R n t x : ℤ) - (x : ℤ) - (t : ℤ) := by
  have h := Nat.mod_add_div (x + t - 1) n
  obtain ⟨a, ha⟩ : ∃ a, a = (x + t - 1) % n := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q, q = (x + t - 1) / n := ⟨_, rfl⟩
  rw [← ha, ← hq] at h
  have hR : R n t x = a + 1 := by
    unfold R
    rw [← ha]
  have h1 : a + n * q + 1 = x + t := by omega
  have h2 : (a : ℤ) + (n : ℤ) * (q : ℤ) + 1 = (x : ℤ) + (t : ℤ) := by exact_mod_cast h1
  refine ⟨-(q : ℤ), ?_⟩
  rw [hR]
  push_cast
  linear_combination h2

theorem R_injOn {n t : ℕ} (ht : t ≤ n) : Set.InjOn (R n t) ↑(Finset.Icc 1 n) := by
  intro x hx y hy hxy
  have hx' := R_inv ht (Finset.mem_coe.mp hx)
  have hy' := R_inv ht (Finset.mem_coe.mp hy)
  rw [hxy] at hx'
  rw [hx'] at hy'
  exact hy'

theorem rot_sub {n : ℕ} (t : ℕ) (hn : 0 < n) (S : Finset ℕ) : rot n t S ⊆ Finset.Icc 1 n := by
  intro y hy
  unfold rot at hy
  obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hy
  exact R_mem t x hn

theorem rot_card {n t : ℕ} (ht : t ≤ n) {S : Finset ℕ} (hS : S ⊆ Finset.Icc 1 n) :
    (rot n t S).card = S.card := by
  unfold rot
  exact Finset.card_image_of_injOn ((R_injOn ht).mono (Finset.coe_subset.mpr hS))

theorem rot_rot {n t : ℕ} (ht : t ≤ n) {S : Finset ℕ} (hS : S ⊆ Finset.Icc 1 n) :
    rot n (n - t) (rot n t S) = S := by
  unfold rot
  rw [Finset.image_image]
  have h : Set.EqOn (R n (n - t) ∘ R n t) id ↑S := fun x hx =>
    R_inv ht (hS (Finset.mem_coe.mp hx))
  rw [Finset.image_congr h, Finset.image_id]

theorem rot_sum {n t : ℕ} (ht : t ≤ n) {S : Finset ℕ} (hS : S ⊆ Finset.Icc 1 n) :
    (n : ℤ) ∣ (∑ y ∈ rot n t S, (y : ℤ)) - (∑ x ∈ S, (x : ℤ)) - (S.card : ℤ) * (t : ℤ) := by
  unfold rot
  rw [Finset.sum_image ((R_injOn ht).mono (Finset.coe_subset.mpr hS))]
  have e : (∑ x ∈ S, ((R n t x : ℕ) : ℤ)) - (∑ x ∈ S, (x : ℤ)) - (S.card : ℤ) * (t : ℤ) =
      ∑ x ∈ S, (((R n t x : ℕ) : ℤ) - (x : ℤ) - (t : ℤ)) := by
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
  rw [e]
  exact Finset.dvd_sum (fun x hx => R_mod (Finset.mem_Icc.mp (hS hx)).1)

theorem dvd_shift {n c c' s : ℤ} (h : n ∣ c - c') : n ∣ s - c ↔ n ∣ s - c' := by
  constructor
  · intro h1
    have e : s - c' = (s - c) + (c - c') := by ring
    rw [e]
    exact dvd_add h1 h
  · intro h1
    have e : s - c = (s - c') - (c - c') := by ring
    rw [e]
    exact dvd_sub h1 h

theorem N_congr {n k : ℕ} {c c' : ℤ} (h : (n : ℤ) ∣ c - c') : N n k c = N n k c' := by
  unfold N
  have e : ((Finset.Icc 1 n).powersetCard k).filter
        (fun S : Finset ℕ => (n : ℤ) ∣ (∑ x ∈ S, (x : ℤ)) - c) =
      ((Finset.Icc 1 n).powersetCard k).filter
        (fun S : Finset ℕ => (n : ℤ) ∣ (∑ x ∈ S, (x : ℤ)) - c') := by
    ext S
    simp only [Finset.mem_filter]
    rw [dvd_shift h]
  rw [e]

theorem N_rot {n k t : ℕ} (hn : 0 < n) (ht : t ≤ n) (c : ℤ) :
    N n k c = N n k (c + (k : ℤ) * (t : ℤ)) := by
  unfold N
  apply Finset.card_nbij' (rot n t) (rot n (n - t))
  · intro S hS
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_powersetCard] at hS
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_powersetCard]
    obtain ⟨⟨hsub, hcard⟩, hdvd⟩ := hS
    refine ⟨⟨rot_sub t hn S, ?_⟩, ?_⟩
    · rw [rot_card ht hsub, hcard]
    · have h1 := rot_sum ht hsub
      rw [hcard] at h1
      have e : (∑ y ∈ rot n t S, (y : ℤ)) - (c + (k : ℤ) * (t : ℤ)) =
          ((∑ y ∈ rot n t S, (y : ℤ)) - (∑ x ∈ S, (x : ℤ)) - (k : ℤ) * (t : ℤ)) +
            ((∑ x ∈ S, (x : ℤ)) - c) := by ring
      rw [e]
      exact dvd_add h1 hdvd
  · intro S hS
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_powersetCard] at hS
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_powersetCard]
    obtain ⟨⟨hsub, hcard⟩, hdvd⟩ := hS
    refine ⟨⟨rot_sub (n - t) hn S, ?_⟩, ?_⟩
    · rw [rot_card (Nat.sub_le n t) hsub, hcard]
    · have h1 := rot_sum (Nat.sub_le n t) hsub
      rw [hcard] at h1
      have e : (∑ y ∈ rot n (n - t) S, (y : ℤ)) - c =
          ((∑ y ∈ rot n (n - t) S, (y : ℤ)) - (∑ x ∈ S, (x : ℤ)) -
            (k : ℤ) * ((n - t : ℕ) : ℤ)) + ((∑ x ∈ S, (x : ℤ)) - (c + (k : ℤ) * (t : ℤ))) +
            (k : ℤ) * (n : ℤ) := by
        rw [Nat.cast_sub ht]
        ring
      rw [e]
      exact dvd_add (dvd_add h1 hdvd) (dvd_mul_left (n : ℤ) (k : ℤ))
  · intro S hS
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_powersetCard] at hS
    exact rot_rot ht hS.1.1
  · intro S hS
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_powersetCard] at hS
    have h := rot_rot (Nat.sub_le n t) hS.1.1
    rw [Nat.sub_sub_self ht] at h
    exact h

theorem N_compl {n k : ℕ} (hk : k ≤ n) (c : ℤ) :
    N n k c = N n (n - k) ((∑ x ∈ Finset.Icc 1 n, (x : ℤ)) - c) := by
  unfold N
  apply Finset.card_nbij' (cpl n) (cpl n)
  · intro S hS
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_powersetCard] at hS
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_powersetCard]
    obtain ⟨⟨hsub, hcard⟩, hdvd⟩ := hS
    refine ⟨⟨Finset.sdiff_subset, ?_⟩, ?_⟩
    · have h1 : (cpl n S).card = (Finset.Icc 1 n).card - S.card :=
        Finset.card_sdiff_of_subset hsub
      rw [Nat.card_Icc] at h1
      omega
    · have hs : (∑ x ∈ Finset.Icc 1 n \ S, (x : ℤ)) + (∑ x ∈ S, (x : ℤ)) =
          ∑ x ∈ Finset.Icc 1 n, (x : ℤ) := Finset.sum_sdiff hsub
      have e : (∑ x ∈ cpl n S, (x : ℤ)) - ((∑ x ∈ Finset.Icc 1 n, (x : ℤ)) - c) =
          -((∑ x ∈ S, (x : ℤ)) - c) := by
        unfold cpl
        linear_combination hs
      rw [e]
      exact dvd_neg.mpr hdvd
  · intro S hS
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_powersetCard] at hS
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_powersetCard]
    obtain ⟨⟨hsub, hcard⟩, hdvd⟩ := hS
    refine ⟨⟨Finset.sdiff_subset, ?_⟩, ?_⟩
    · have h1 : (cpl n S).card = (Finset.Icc 1 n).card - S.card :=
        Finset.card_sdiff_of_subset hsub
      rw [Nat.card_Icc] at h1
      omega
    · have hs : (∑ x ∈ Finset.Icc 1 n \ S, (x : ℤ)) + (∑ x ∈ S, (x : ℤ)) =
          ∑ x ∈ Finset.Icc 1 n, (x : ℤ) := Finset.sum_sdiff hsub
      have e : (∑ x ∈ cpl n S, (x : ℤ)) - c =
          -((∑ x ∈ S, (x : ℤ)) - ((∑ x ∈ Finset.Icc 1 n, (x : ℤ)) - c)) := by
        unfold cpl
        linear_combination hs
      rw [e]
      exact dvd_neg.mpr hdvd
  · intro S hS
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_powersetCard] at hS
    unfold cpl
    exact Finset.sdiff_sdiff_eq_self hS.1.1
  · intro S hS
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_powersetCard] at hS
    unfold cpl
    exact Finset.sdiff_sdiff_eq_self hS.1.1

theorem T_eq_N (n k : ℕ) : T n k = N n k 0 := by
  unfold T N
  have e : ((Finset.Icc 1 n).powersetCard k).filter (fun S => n ∣ ∑ x ∈ S, x) =
      ((Finset.Icc 1 n).powersetCard k).filter
        (fun S : Finset ℕ => (n : ℤ) ∣ (∑ x ∈ S, (x : ℤ)) - 0) := by
    ext S
    simp only [Finset.mem_filter, sub_zero]
    rw [← Nat.cast_sum, Int.natCast_dvd_natCast]
  rw [e]

theorem G_two (n : ℕ) : (∑ x ∈ Finset.Icc 1 n, (x : ℤ)) * 2 = (n : ℤ) * ((n : ℤ) + 1) := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ m + 1), add_mul, ih]
    push_cast
    ring

end P1A267632

open OMA.S_oeis_a267632 P1A267632 in
theorem OMA.solution : type_of% @OMA.S_oeis_a267632.main := by
  intro n _hn hcase k hk1 hk2
  have hkn : k ≤ n := by omega
  have hpos : 0 < n := by omega
  have hc : T n (n - k) = N n k ((∑ x ∈ Finset.Icc 1 n, (x : ℤ)) - 0) := by
    rw [T_eq_N, N_compl (Nat.sub_le n k) 0, Nat.sub_sub_self hkn]
  rw [hc, T_eq_N]
  rcases hcase with ⟨c, hc2⟩ | ⟨m, hm⟩
  · apply N_congr
    have hG := G_two n
    have hn' : (n : ℤ) = 2 * (c : ℤ) + 1 := by exact_mod_cast hc2
    rw [hn'] at hG
    have h3 : (∑ x ∈ Finset.Icc 1 n, (x : ℤ)) * 2 =
        ((2 * (c : ℤ) + 1) * ((c : ℤ) + 1)) * 2 := by
      rw [hG]
      ring
    have h4 := mul_right_cancel₀ (by norm_num : (2 : ℤ) ≠ 0) h3
    refine ⟨-((c : ℤ) + 1), ?_⟩
    rw [h4, hn']
    ring
  · subst hm
    cases m with
    | zero =>
      rw [pow_zero] at hk2
      omega
    | succ m =>
      obtain ⟨a, b, hb, hkab⟩ := Nat.exists_eq_two_pow_mul_odd (by omega : k ≠ 0)
      obtain ⟨d, hd⟩ := hb
      have ha : a ≤ m := by
        by_contra hcon
        have h1 : 2 ^ (m + 1) ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) (by omega)
        have h2 : 2 ^ a ≤ 2 ^ a * b := Nat.le_mul_of_pos_right _ (by omega)
        omega
      have ht : 2 ^ (m - a) ≤ 2 ^ (m + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      rw [N_rot hpos ht 0]
      apply N_congr
      have hpow : (2 : ℕ) ^ a * 2 ^ (m - a) = 2 ^ m := by
        rw [← pow_add, Nat.add_sub_of_le ha]
      have hk' : k * 2 ^ (m - a) = 2 ^ m * (2 * d + 1) := by
        rw [hkab, hd, ← hpow]
        ring
      have hkt : (k : ℤ) * ((2 ^ (m - a) : ℕ) : ℤ) = (2 : ℤ) ^ m * (2 * (d : ℤ) + 1) := by
        exact_mod_cast hk'
      have hn2 : ((2 ^ (m + 1) : ℕ) : ℤ) = 2 * (2 : ℤ) ^ m := by
        push_cast
        ring
      have hG := G_two (2 ^ (m + 1))
      rw [hn2] at hG
      have h3 : (∑ x ∈ Finset.Icc 1 (2 ^ (m + 1) : ℕ), (x : ℤ)) * 2 =
          ((2 : ℤ) ^ m * (2 * (2 : ℤ) ^ m + 1)) * 2 := by
        rw [hG]
        ring
      have h4 := mul_right_cancel₀ (by norm_num : (2 : ℤ) ≠ 0) h3
      refine ⟨(d : ℤ) - (2 : ℤ) ^ m, ?_⟩
      rw [hkt, h4, hn2]
      ring
