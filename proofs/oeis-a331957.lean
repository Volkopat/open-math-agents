import OMAStatements.S_oeis_a331957
import Mathlib

namespace OMA.P_oeis_a331957

open OMA.S_oeis_a331957

-- Complete homogeneous symmetric polynomial H(d, a, b) = h_d(a, a+1, ..., b)
-- Defined by recursion on (d, b + 1 - a):
private def homSym : ℕ → ℕ → ℕ → ℕ
  | 0, a, b => if a ≤ b then 1 else 0
  | d + 1, a, b =>
    if a ≤ b then
      homSym (d + 1) (a + 1) b + a * homSym d a b
    else 0
termination_by d a b => (d, b + 1 - a)
decreasing_by
  all_goals simp_wf
  · right; omega
  · left; omega

private lemma homSym_gt (d a b : ℕ) (h : b < a) : homSym d a b = 0 := by
  cases d with
  | zero => rw [homSym]; simp [show ¬(a ≤ b) by omega]
  | succ d => rw [homSym]; simp [show ¬(a ≤ b) by omega]

private lemma homSym_zero (a b : ℕ) (h : a ≤ b) : homSym 0 a b = 1 := by
  rw [homSym]; simp [h]

private lemma homSym_step_left (d a b : ℕ) (h : a ≤ b) :
    homSym (d + 1) a b = homSym (d + 1) (a + 1) b + a * homSym d a b := by
  rw [homSym]; simp [h]

-- Dual recurrence on the right endpoint b: H(d+1, a, b+1) = H(d+1, a, b) + (b+1) * H(d, a, b+1)
private lemma homSym_step_right :
    ∀ s : ℕ, ∀ d a b : ℕ, d + (b + 1 - a) = s → a ≤ b + 1 →
      homSym (d + 1) a (b + 1) = homSym (d + 1) a b + (b + 1) * homSym d a (b + 1) := by
  intro s
  induction s using Nat.strong_induction_on with
  | h s ih =>
    intro d a b hs hab
    by_cases heq : a = b + 1
    · subst heq
      rw [homSym_step_left d (b + 1) (b + 1) (le_refl _),
        homSym_gt (d + 1) (b + 2) (b + 1) (by omega),
        homSym_gt (d + 1) (b + 1) b (by omega), zero_add]
    · have hab' : a ≤ b := by omega
      cases d with
      | zero =>
        rw [homSym_step_left 0 a (b + 1) (by omega), homSym_step_left 0 a b hab',
          homSym_zero a (b + 1) (by omega), homSym_zero a b hab']
        have hrec := ih (0 + (b + 1 - (a + 1))) (by omega) 0 (a + 1) b rfl (by omega)
        rw [homSym_zero (a + 1) (b + 1) (by omega)] at hrec
        omega
      | succ d' =>
        rw [homSym_step_left (d' + 1) a (b + 1) (by omega), homSym_step_left (d' + 1) a b hab']
        have h1 := ih (d' + 1 + (b + 1 - (a + 1))) (by omega) (d' + 1) (a + 1) b rfl (by omega)
        have h2 := ih (d' + (b + 1 - a)) (by omega) d' a b rfl (by omega)
        rw [h1]
        conv_lhs => rw [h2]
        conv_rhs => rw [homSym_step_left d' a (b + 1) (by omega)]
        ring

private lemma homSym_eq_stirling2 :
    ∀ n m : ℕ, 1 ≤ m → m ≤ n → homSym (n - m) 1 m = stirling2 n m := by
  intro n
  induction n with
  | zero => intro m hm hmn; omega
  | succ n ih =>
    intro m hm hmn
    cases m with
    | zero => omega
    | succ m' =>
      by_cases hm'0 : m' = 0
      · subst hm'0
        -- homSym n 1 1 = 1 = stirling2 (n + 1) 1
        have h11 : ∀ d : ℕ, homSym d 1 1 = 1 := by
          intro d; induction d with
          | zero => exact homSym_zero 1 1 (le_refl 1)
          | succ d ihd =>
            rw [homSym_step_left d 1 1 (le_refl 1), homSym_gt (d + 1) 2 1 (by omega),
              zero_add, one_mul, ihd]
        have hs1 : ∀ k : ℕ, stirling2 (k + 1) 1 = 1 := by
          intro k; induction k with
          | zero => rfl
          | succ k ihk => rw [stirling2, ihk]; rfl
        simpa [Nat.succ_sub_succ] using (h11 n).trans (hs1 n).symm
      · by_cases htop : m' = n
        · subst htop
          rw [Nat.sub_self, homSym_zero 1 (m' + 1) (by omega)]
          have hdiag : ∀ k : ℕ, stirling2 k k = 1 := by
            intro k; induction k with
            | zero => rfl
            | succ k ihk =>
              have hgt : ∀ a b : ℕ, a < b → stirling2 a b = 0 := by
                intro a; induction a with
                | zero => intro b hb; cases b with | zero => omega | succ b => rfl
                | succ a iha =>
                  intro b hb; cases b with
                  | zero => omega
                  | succ b => simp [stirling2, iha (b + 1) (by omega), iha b (by omega)]
              simp [stirling2, hgt k (k + 1) (by omega), ihk]
          exact (hdiag (m' + 1)).symm
        · -- 1 ≤ m' < n: use homSym_step_right!
          have hd : n + 1 - (m' + 1) = (n - (m' + 1)) + 1 := by omega
          rw [hd, homSym_step_right ((n - (m' + 1)) + (m' + 1 - 1)) (n - (m' + 1)) 1 m' rfl (by omega)]
          have h1 : homSym (n - (m' + 1) + 1) 1 m' = stirling2 n m' := by
            rw [show n - (m' + 1) + 1 = n - m' by omega]
            exact ih m' (by omega) (by omega)
          have h2 : homSym (n - (m' + 1)) 1 (m' + 1) = stirling2 n (m' + 1) :=
            ih (m' + 1) (by omega) (by omega)
          rw [h1, h2, stirling2, add_comm]

-- Now connect Q(n, k) = ∑_{j=k}^{n-1} R(n-1, j) (so R(n, k) = (k + 1) * Q(n, k) for k < n)!
private def Q (n k : ℕ) : ℕ :=
  match n with
  | 0 => 0
  | n' + 1 => ∑ j ∈ Finset.Ico k (n' + 1), kurkovR n' j

private lemma kurkovR_eq_mul_Q (n k : ℕ) (hk : k < n) :
    kurkovR n k = (k + 1) * Q n k := by
  cases n with
  | zero => omega
  | succ n' => rw [kurkovR]; simp [hk, Q]

private lemma Q_step (n k : ℕ) (hk : k + 1 < n) :
    Q n k = Q n (k + 1) + (k + 1) * Q (n - 1) k := by
  cases n with
  | zero => omega
  | succ n' =>
    rw [Nat.add_sub_cancel]
    conv_lhs => rw [Q]
    conv_rhs => rw [Q]
    have hIco : ∑ j ∈ Finset.Ico k (n' + 1), kurkovR n' j =
        kurkovR n' k + ∑ j ∈ Finset.Ico (k + 1) (n' + 1), kurkovR n' j := by
      rw [← Finset.sum_Ico_consecutive (f := fun j => kurkovR n' j) (show k ≤ k + 1 by omega)
        (show k + 1 ≤ n' + 1 by omega)]
      have h1 : Finset.Ico k (k + 1) = {k} := by
        ext j; simp only [Finset.mem_Ico, Finset.mem_singleton]; omega
      rw [h1, Finset.sum_singleton]
    rw [hIco, kurkovR_eq_mul_Q n' k (by omega), add_comm]

private lemma Q_diag_eq_R_diag (n : ℕ) : Q (n + 1) n = kurkovR n n := by
  simp only [Q]
  have h1 : Finset.Ico n (n + 1) = {n} := by
    ext j; simp only [Finset.mem_Ico, Finset.mem_singleton]; omega
  rw [h1, Finset.sum_singleton]

private lemma kurkovR_zero_eq_two_mul_diag (n : ℕ) (hn : 1 ≤ n) :
    kurkovR (n + 1) 0 = 2 * kurkovR n n := by
  have h0 : kurkovR (n + 1) 0 = ∑ j ∈ Finset.Ico 0 (n + 1), kurkovR n j := by
    rw [kurkovR]; simp
  have hd : kurkovR n n = ∑ j ∈ Finset.Ico 0 n, kurkovR n j := by
    cases n with
    | zero => omega
    | succ n' =>
      rw [kurkovR]; simp [Fin.sum_univ_eq_sum_range, Nat.Ico_zero_eq_range]
  rw [h0, ← Finset.sum_Ico_consecutive (f := fun j => kurkovR n j) (Nat.zero_le n) (by omega),
    ← hd]
  have h1 : Finset.Ico n (n + 1) = {n} := by
    ext j; simp only [Finset.mem_Ico, Finset.mem_singleton]; omega
  rw [h1, Finset.sum_singleton]; omega

-- Key identity: Q(n, k) = ∑_{m ∈ Ico (k + 1) (n + 1)} homSym (n - m) (k + 1) m * kurkovR (m - 1) (m - 1)
private lemma Q_eq_sum_homSym :
    ∀ n : ℕ, ∀ k : ℕ, k < n →
      Q n k = ∑ m ∈ Finset.Ico (k + 1) (n + 1),
        homSym (n - m) (k + 1) m * kurkovR (m - 1) (m - 1) := by
  intro n
  induction n with
  | zero => intro k hk; omega
  | succ n ih =>
    -- Induction on d = n - k from 0 up to n!
    have aux : ∀ d : ℕ, ∀ k : ℕ, k + d = n →
        Q (n + 1) k = ∑ m ∈ Finset.Ico (k + 1) (n + 2),
          homSym (n + 1 - m) (k + 1) m * kurkovR (m - 1) (m - 1) := by
      intro d
      induction d with
      | zero =>
        intro k hk
        have hkn : k = n := by omega
        subst hkn
        rw [Q_diag_eq_R_diag]
        have h1 : Finset.Ico (k + 1) (k + 2) = {k + 1} := by
          ext m; simp only [Finset.mem_Ico, Finset.mem_singleton]; omega
        rw [h1, Finset.sum_singleton, Nat.sub_self, homSym_zero (k + 1) (k + 1) (le_refl _),
          one_mul, Nat.add_sub_cancel]
      | succ d ihd =>
        intro k hk
        rw [Q_step (n + 1) k (by omega), Nat.add_sub_cancel,
          ihd (k + 1) (by omega), ih k (by omega)]
        -- Split m = k + 1 out of the RHS sum!
        have hsplit :
            ∑ m ∈ Finset.Ico (k + 1) (n + 2),
              homSym (n + 1 - m) (k + 1) m * kurkovR (m - 1) (m - 1) =
            homSym (n + 1 - (k + 1)) (k + 1) (k + 1) * kurkovR k k +
            ∑ m ∈ Finset.Ico (k + 2) (n + 2),
              homSym (n + 1 - m) (k + 1) m * kurkovR (m - 1) (m - 1) := by
          rw [← Finset.sum_Ico_consecutive (f := fun m => homSym (n + 1 - m) (k + 1) m * kurkovR (m - 1) (m - 1))
            (show k + 1 ≤ k + 2 by omega) (show k + 2 ≤ n + 2 by omega)]
          have h1 : Finset.Ico (k + 1) (k + 2) = {k + 1} := by
            ext m; simp only [Finset.mem_Ico, Finset.mem_singleton]; omega
          rw [h1, Finset.sum_singleton, Nat.add_sub_cancel]
        rw [hsplit]
        -- Also split m = n + 1 out of the Ico (k+2) (n+2) sum, and m = k+1 out of the ih sum!
        have hsplit_ih :
            ∑ m ∈ Finset.Ico (k + 1) (n + 1),
              homSym (n - m) (k + 1) m * kurkovR (m - 1) (m - 1) =
            homSym (n - (k + 1)) (k + 1) (k + 1) * kurkovR k k +
            ∑ m ∈ Finset.Ico (k + 2) (n + 1),
              homSym (n - m) (k + 1) m * kurkovR (m - 1) (m - 1) := by
          rw [← Finset.sum_Ico_consecutive (f := fun m => homSym (n - m) (k + 1) m * kurkovR (m - 1) (m - 1))
            (show k + 1 ≤ k + 2 by omega) (show k + 2 ≤ n + 1 by omega)]
          have h1 : Finset.Ico (k + 1) (k + 2) = {k + 1} := by
            ext m; simp only [Finset.mem_Ico, Finset.mem_singleton]; omega
          rw [h1, Finset.sum_singleton, Nat.add_sub_cancel]
        have hsplit_ihd :
            ∑ m ∈ Finset.Ico (k + 2) (n + 2),
              homSym (n + 1 - m) (k + 2) m * kurkovR (m - 1) (m - 1) =
            (∑ m ∈ Finset.Ico (k + 2) (n + 1),
              homSym (n + 1 - m) (k + 2) m * kurkovR (m - 1) (m - 1)) +
            homSym 0 (k + 2) (n + 1) * kurkovR n n := by
          rw [← Finset.sum_Ico_consecutive (f := fun m => homSym (n + 1 - m) (k + 2) m * kurkovR (m - 1) (m - 1))
            (show k + 2 ≤ n + 1 by omega) (show n + 1 ≤ n + 2 by omega)]
          have h1 : Finset.Ico (n + 1) (n + 2) = {n + 1} := by
            ext m; simp only [Finset.mem_Ico, Finset.mem_singleton]; omega
          rw [h1, Finset.sum_singleton, Nat.sub_self, Nat.add_sub_cancel]
        have hsplit_rhs2 :
            ∑ m ∈ Finset.Ico (k + 2) (n + 2),
              homSym (n + 1 - m) (k + 1) m * kurkovR (m - 1) (m - 1) =
            (∑ m ∈ Finset.Ico (k + 2) (n + 1),
              homSym (n + 1 - m) (k + 1) m * kurkovR (m - 1) (m - 1)) +
            homSym 0 (k + 1) (n + 1) * kurkovR n n := by
          rw [← Finset.sum_Ico_consecutive (f := fun m => homSym (n + 1 - m) (k + 1) m * kurkovR (m - 1) (m - 1))
            (show k + 2 ≤ n + 1 by omega) (show n + 1 ≤ n + 2 by omega)]
          have h1 : Finset.Ico (n + 1) (n + 2) = {n + 1} := by
            ext m; simp only [Finset.mem_Ico, Finset.mem_singleton]; omega
          rw [h1, Finset.sum_singleton, Nat.sub_self, Nat.add_sub_cancel]
        rw [hsplit_ih, hsplit_ihd, hsplit_rhs2,
          homSym_zero (k + 2) (n + 1) (by omega), homSym_zero (k + 1) (n + 1) (by omega)]
        -- Check m = k + 1 term: homSym (n + 1 - (k + 1)) (k+1) (k+1) = (k+1) * homSym (n - (k+1)) (k+1) (k+1)
        have hbase : homSym (n + 1 - (k + 1)) (k + 1) (k + 1) =
            (k + 1) * homSym (n - (k + 1)) (k + 1) (k + 1) := by
          rw [show n + 1 - (k + 1) = (n - (k + 1)) + 1 by omega,
            homSym_step_left (n - (k + 1)) (k + 1) (k + 1) (le_refl _),
            homSym_gt _ (k + 2) (k + 1) (by omega), zero_add]
        -- Check middle terms m ∈ Ico (k+2) (n+1)
        have hmid :
            (∑ m ∈ Finset.Ico (k + 2) (n + 1),
              homSym (n + 1 - m) (k + 2) m * kurkovR (m - 1) (m - 1)) +
            (k + 1) * (∑ m ∈ Finset.Ico (k + 2) (n + 1),
              homSym (n - m) (k + 1) m * kurkovR (m - 1) (m - 1)) =
            ∑ m ∈ Finset.Ico (k + 2) (n + 1),
              homSym (n + 1 - m) (k + 1) m * kurkovR (m - 1) (m - 1) := by
          rw [Finset.mul_sum, ← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro m hm
          have hm1 : k + 2 ≤ m := (Finset.mem_Ico.mp hm).1
          have hm2 : m < n + 1 := (Finset.mem_Ico.mp hm).2
          rw [show n + 1 - m = (n - m) + 1 by omega,
            homSym_step_left (n - m) (k + 1) m (by omega)]
          ring
        rw [hbase, mul_add]
        linarith
    intro k hk
    exact aux (n - k) k (by omega)

private theorem main_proved : ∀ n : ℕ, a331957 n = kurkovR n 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => rw [a331957, kurkovR]
    | succ m =>
      cases m with
      | zero =>
        rw [a331957, kurkovR]; simp [kurkovR]
      | succ m' =>
        -- n = m' + 2 >= 2!
        -- From Q_eq_sum_homSym (m' + 2) 0:
        -- kurkovR (m' + 2) 0 = Q (m' + 2) 0 = ∑_{j=1}^{m'+2} S2(m'+2, j) * kurkovR (j-1) (j-1)!
        have hQ := Q_eq_sum_homSym (m' + 2) 0 (by omega)
        have hR0 : kurkovR (m' + 2) 0 = Q (m' + 2) 0 := by
          rw [kurkovR_eq_mul_Q (m' + 2) 0 (by omega), Nat.zero_add, one_mul]
        rw [← hR0] at hQ
        -- Multiply hQ by 2:
        -- 2 * R(m'+2, 0) = 2 * S2(m'+2, 1) * R(0, 0) + ∑_{j=2}^{m'+1} S2(m'+2, j) * (2 * R(j-1, j-1)) + S2(m'+2, m'+2) * (2 * R(m'+1, m'+1))
        -- And 2 * R(j-1, j-1) = R(j, 0) for j >= 2!
        have hsum_split :
            ∑ j ∈ Finset.Ico 1 (m' + 3), homSym (m' + 2 - j) 1 j * kurkovR (j - 1) (j - 1) =
            homSym (m' + 1) 1 1 * kurkovR 0 0 +
            (∑ j ∈ Finset.Ico 2 (m' + 2), homSym (m' + 2 - j) 1 j * kurkovR (j - 1) (j - 1)) +
            homSym 0 1 (m' + 2) * kurkovR (m' + 1) (m' + 1) := by
          rw [← Finset.sum_Ico_consecutive (f := fun j => homSym (m' + 2 - j) 1 j * kurkovR (j - 1) (j - 1))
            (show 1 ≤ m' + 2 by omega) (show m' + 2 ≤ m' + 3 by omega)]
          rw [← Finset.sum_Ico_consecutive (f := fun j => homSym (m' + 2 - j) 1 j * kurkovR (j - 1) (j - 1))
            (show 1 ≤ 2 by omega) (show 2 ≤ m' + 2 by omega)]
          have h1 : Finset.Ico 1 2 = {1} := by ext j; simp only [Finset.mem_Ico, Finset.mem_singleton]; omega
          have h2 : Finset.Ico (m' + 2) (m' + 3) = {m' + 2} := by ext j; simp only [Finset.mem_Ico, Finset.mem_singleton]; omega
          rw [h1, h2, Finset.sum_singleton, Finset.sum_singleton]
          simp
        rw [hsum_split] at hQ
        have hS1 : homSym (m' + 1) 1 1 = stirling2 (m' + 2) 1 :=
          homSym_eq_stirling2 (m' + 2) 1 (le_refl 1) (by omega)
        have hs1_val : stirling2 (m' + 2) 1 = 1 := by
          have hs1 : ∀ k : ℕ, stirling2 (k + 1) 1 = 1 := by
            intro k; induction k with | zero => rfl | succ k ihk => rw [stirling2, ihk]; rfl
          exact hs1 (m' + 1)
        have hR00 : kurkovR 0 0 = 1 := by rw [kurkovR]
        have htop0 : homSym 0 1 (m' + 2) = 1 := homSym_zero 1 (m' + 2) (by omega)
        rw [hS1, hs1_val, hR00, htop0, one_mul, one_mul] at hQ
        have h2 := congr_arg (2 * ·) hQ
        rw [mul_add, mul_add, kurkovR_zero_eq_two_mul_diag (m' + 1) (by omega)] at h2
        -- Simplify the middle sum: 2 * ∑_{j=2}^{m'+1} S2(m'+2, j) * R(j-1, j-1) = ∑_{j=2}^{m'+1} S2(m'+2, j) * a331957 j
        have hmid :
            2 * ∑ j ∈ Finset.Ico 2 (m' + 2), homSym (m' + 2 - j) 1 j * kurkovR (j - 1) (j - 1) =
            ∑ j ∈ Finset.Ico 2 (m' + 2), stirling2 (m' + 2) j * a331957 j := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j hj
          have hj1 : 2 ≤ j := (Finset.mem_Ico.mp hj).1
          have hj2 : j < m' + 2 := (Finset.mem_Ico.mp hj).2
          rw [homSym_eq_stirling2 (m' + 2) j (by omega) (by omega)]
          have hdiag := kurkovR_zero_eq_two_mul_diag (j - 1) (by omega)
          rw [show j - 1 + 1 = j by omega] at hdiag
          rw [ih j (by omega), hdiag]; ring
        rw [hmid] at h2
        -- Now compute a331957 (m' + 2) = 1 + S2(m'+2, 1) * a331957 1 + ∑_{j=2}^{m'+1} S2(m'+2, j) * a331957 j!
        have ha_def : a331957 (m' + 2) =
            1 + ∑ k ∈ Finset.range (m' + 1), stirling2 (m' + 2) (k + 1) * a331957 (k + 1) := by
          rw [a331957,
            Fin.sum_univ_eq_sum_range (fun k => stirling2 (m' + 2) (k + 1) * a331957 (k + 1))]
        rw [Finset.sum_range_succ'] at ha_def
        have ha1 : a331957 1 = 1 := by rw [a331957]; simp
        simp only [Nat.zero_add, hs1_val, ha1, mul_one] at ha_def
        have hshift :
            ∑ k ∈ Finset.range m', stirling2 (m' + 2) (k + 1 + 1) * a331957 (k + 1 + 1) =
            ∑ j ∈ Finset.Ico 2 (m' + 2), stirling2 (m' + 2) j * a331957 j := by
          apply Finset.sum_nbij (fun k => k + 2)
          · intro k hk; simp only [Finset.mem_range] at hk; simp only [Finset.mem_Ico]; omega
          · intro a _ b _ h; dsimp only at h; omega
          · intro j hj; simp only [Finset.mem_coe, Finset.mem_Ico] at hj
            exact ⟨j - 2, by simp only [Finset.mem_coe, Finset.mem_range]; omega, by dsimp only; omega⟩
          · intro k _; rfl
        rw [hshift] at ha_def
        have hR2 := kurkovR_zero_eq_two_mul_diag (m' + 1) (by omega)
        change a331957 (m' + 2) = kurkovR (m' + 2) 0
        omega

end OMA.P_oeis_a331957

theorem OMA.solution : type_of% @OMA.S_oeis_a331957.main :=
  OMA.P_oeis_a331957.main_proved
