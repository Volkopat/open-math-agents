import OMAStatements.S_oeis_a287448

namespace OMA.S_oeis_a287448

open Filter Topology





/-! ### One pass -/

/-- A word is closed when the pass over it followed by any word is the pass over it followed by
the pass over that word. -/
def Closed (u : List ℕ) : Prop := ∀ y, step (u ++ y) = step u ++ step y

lemma closed_append {u v : List ℕ} (hu : Closed u) (hv : Closed v) : Closed (u ++ v) := by
  intro y
  rw [List.append_assoc, hu (v ++ y), hv y, hu v, List.append_assoc]

/-! ### Tokens -/

/-- The tokens T0 = 00, T1 = 1000, T2 = 11000, T3 = 10011000, T4 = 1010011000,
T5 = 1001010011000. -/
def tok : ℕ → List ℕ
  | 0 => [0, 0]
  | 1 => [1, 0, 0, 0]
  | 2 => [1, 1, 0, 0, 0]
  | 3 => [1, 0, 0, 1, 1, 0, 0, 0]
  | 4 => [1, 0, 1, 0, 0, 1, 1, 0, 0, 0]
  | _ => [1, 0, 0, 1, 0, 1, 0, 0, 1, 1, 0, 0, 0]

/-- All tokens are at most 5. -/
def Valid (s : List ℕ) : Prop := ∀ k ∈ s, k ≤ 5

lemma tok_closed (k : ℕ) (hk : k ≤ 5) : Closed (tok k) := by
  interval_cases k <;> exact fun _ => rfl

/-- The word of a list of tokens. -/
def flat (s : List ℕ) : List ℕ := s.flatMap tok

/-- The images of the tokens under one pass: T0 -> T1, T1 -> T0 T2, T2 -> T3, T3 -> T0 T4,
T4 -> T0 T5, T5 -> T0 T1 T5. -/
def tauT : ℕ → List ℕ
  | 0 => [1]
  | 1 => [0, 2]
  | 2 => [3]
  | 3 => [0, 4]
  | 4 => [0, 5]
  | _ => [0, 1, 5]

/-- The token morphism. -/
def tau (s : List ℕ) : List ℕ := s.flatMap tauT

lemma flat_cons (k : ℕ) (s : List ℕ) : flat (k :: s) = tok k ++ flat s := by
  simp [flat]

lemma flat_append (u v : List ℕ) : flat (u ++ v) = flat u ++ flat v := by
  simp [flat]

lemma tau_cons (k : ℕ) (s : List ℕ) : tau (k :: s) = tauT k ++ tau s := by
  simp [tau]

lemma tau_append (u v : List ℕ) : tau (u ++ v) = tau u ++ tau v := by
  simp [tau]

lemma tau_single (k : ℕ) : tau [k] = tauT k := by
  simp [tau]

lemma tauT_valid (k : ℕ) : Valid (tauT k) := by
  intro x hx
  rcases k with _ | _ | _ | _ | _ | k <;> simp [tauT] at hx <;> omega

lemma tau_valid (s : List ℕ) : Valid (tau s) := by
  intro x hx
  simp only [tau, List.mem_flatMap] at hx
  obtain ⟨k, -, hk⟩ := hx
  exact tauT_valid k x hk

lemma valid_cons {k : ℕ} {s : List ℕ} (h : Valid (k :: s)) : k ≤ 5 ∧ Valid s :=
  ⟨h k (by simp), fun x hx => h x (by simp [hx])⟩

lemma valid_single {x : ℕ} (hx : x ≤ 5) : Valid [x] := by
  intro y hy
  simp at hy
  omega

lemma step_tok (k : ℕ) (hk : k ≤ 5) : step (tok k) = flat (tauT k) := by
  interval_cases k <;> rfl

lemma step_flat (s : List ℕ) (hs : Valid s) : step (flat s) = flat (tau s) := by
  induction s with
  | nil => rfl
  | cons k s ih =>
    obtain ⟨hk, hs'⟩ := valid_cons hs
    rw [flat_cons, tok_closed k hk, step_tok k hk, ih hs', tau_cons, flat_append]

lemma tauIter_append (n : ℕ) (u v : List ℕ) : tau^[n] (u ++ v) = tau^[n] u ++ tau^[n] v := by
  induction n generalizing u v with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply, Function.iterate_succ_apply,
      Function.iterate_succ_apply, tau_append, ih]

lemma tauIter_nil (n : ℕ) : tau^[n] [] = [] :=
  Function.iterate_fixed (show tau [] = [] from rfl) n

lemma tauIter_valid (n : ℕ) (s : List ℕ) (hs : Valid s) : Valid (tau^[n] s) := by
  cases n with
  | zero => exact hs
  | succ n =>
    rw [Function.iterate_succ_apply']
    exact tau_valid _

lemma tauT_ne_nil (k : ℕ) : tauT k ≠ [] := by
  rcases k with _ | _ | _ | _ | _ | k <;> simp [tauT]

lemma tau_ne_nil (s : List ℕ) (hs : s ≠ []) : tau s ≠ [] := by
  rcases s with _ | ⟨k, s⟩
  · exact absurd rfl hs
  · rw [tau_cons]
    intro h
    exact tauT_ne_nil k (List.append_eq_nil_iff.mp h).1

lemma tauIter_ne_nil (n : ℕ) (s : List ℕ) (hs : s ≠ []) : tau^[n] s ≠ [] := by
  induction n generalizing s with
  | zero => exact hs
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    exact ih _ (tau_ne_nil s hs)

lemma flat_length_ge (s : List ℕ) (hs : Valid s) : 2 * s.length ≤ (flat s).length := by
  induction s with
  | nil => simp [flat]
  | cons k s ih =>
    obtain ⟨hk, hs'⟩ := valid_cons hs
    rw [flat_cons, List.length_append, List.length_cons]
    have := ih hs'
    interval_cases k <;> simp [tok] <;> omega

/-! ### The iterates -/

lemma iter_eq (n : ℕ) : iter n = flat (tau^[n] [0]) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [show iter (n + 1) = step (iter n) from rfl, ih,
      step_flat _ (tauIter_valid n _ (valid_single (by norm_num))),
      ← Function.iterate_succ_apply' tau n]

/-- Iterate n + 2 is iterate n followed by the word of tau^n(T2). -/
lemma iter_two (n : ℕ) : iter (n + 2) = iter n ++ flat (tau^[n] [2]) := by
  rw [iter_eq, iter_eq, Function.iterate_add_apply, show tau^[2] [0] = [0] ++ [2] from rfl,
    tauIter_append, flat_append]

lemma iter_prefix_two (n : ℕ) : iter n <+: iter (n + 2) := by
  rw [iter_two]
  exact List.prefix_append _ _

lemma iter_length_lin (n : ℕ) : n + 2 ≤ (iter n).length ∧ n + 3 ≤ (iter (n + 1)).length := by
  induction n with
  | zero => decide
  | succ n ih =>
    obtain ⟨h0, h1⟩ := ih
    refine ⟨h1, ?_⟩
    rw [show n + 1 + 1 = n + 2 from rfl, iter_two, List.length_append]
    have h2 := flat_length_ge (tau^[n] [2]) (tauIter_valid _ _ (valid_single (by norm_num)))
    have h3 := List.length_pos_of_ne_nil (tauIter_ne_nil n [2] (by simp))
    omega

lemma iter_length (n : ℕ) : n + 2 ≤ (iter n).length := (iter_length_lin n).1

lemma iter_letters (n : ℕ) : ∀ x ∈ iter n, x ≤ 1 := by
  intro x hx
  rw [iter_eq] at hx
  simp only [flat, List.mem_flatMap] at hx
  obtain ⟨k, -, hk⟩ := hx
  rcases k with _ | _ | _ | _ | _ | k <;> simp [tok] at hk <;> omega

lemma getD_prefix {l₁ l₂ : List ℕ} (h : l₁ <+: l₂) {i : ℕ} (hi : i < l₁.length) :
    l₁.getD i 0 = l₂.getD i 0 := by
  obtain ⟨s, rfl⟩ := h
  rw [List.getD_append _ _ _ _ hi]

/-! ### The limiting word -/

/-- The residue mod 2 of the iterates whose limit is W. -/
def res : ℕ := 0

/-- V k: iterate 2k + res. -/
def V (k : ℕ) : List ℕ := iter (2 * k + res)

lemma V_prefix_succ (k : ℕ) : V k <+: V (k + 1) := by
  unfold V
  rw [show 2 * (k + 1) + res = 2 * k + res + 2 by ring]
  exact iter_prefix_two _

lemma V_prefix {k k' : ℕ} (h : k ≤ k') : V k <+: V k' := by
  induction k', h using Nat.le_induction with
  | base => exact List.prefix_refl _
  | succ k' _ ih => exact ih.trans (V_prefix_succ k')

lemma V_length (k : ℕ) : k + 2 ≤ (V k).length := by
  unfold V
  have := iter_length (2 * k + res)
  omega

lemma W_eq (k i : ℕ) (hi : i < (V k).length) : W i = (V k).getD i 0 := by
  have hW : W i = (V (i + 1)).getD i 0 := rfl
  have hi' : i < (V (i + 1)).length := by have := V_length (i + 1); omega
  rw [hW]
  rcases le_total (i + 1) k with h | h
  · exact getD_prefix (V_prefix h) hi'
  · exact (getD_prefix (V_prefix h) hi).symm

/-! ### The golden ratio -/

/-- The Perron root of the token matrix, the golden ratio. -/
noncomputable def phi : ℝ := (1 + Real.sqrt 5) / 2

lemma phi_sq : phi ^ 2 = phi + 1 := by
  have h := Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
  unfold phi
  linear_combination h / 4

lemma phi_bounds : 1.6180339 < phi ∧ phi < 1.618034 := by
  have h0 : (0 : ℝ) ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  have h := Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
  unfold phi
  constructor <;> nlinarith

/-- The other root of x^2 - x - 1, -0.61803... -/
noncomputable def psi : ℝ := 1 - phi

/-- The limiting number of letters 0 per letter 1, 2.19821... -/
noncomputable def cc : ℝ := (8 + 10 * phi) / 11

lemma cc_bounds : 2.198211 ≤ cc ∧ cc ≤ 2.198213 := by
  obtain ⟨h1, h2⟩ := phi_bounds
  unfold cc
  constructor <;> linarith

/-! ### Deviation of words and token lists -/

/-- For a word, the number of letters 0 minus c times the number of letters 1. -/
noncomputable def gL (L : List ℕ) : ℝ := (L.count 0 : ℝ) - cc * (L.count 1 : ℝ)

lemma gL_append (u v : List ℕ) : gL (u ++ v) = gL u + gL v := by
  simp only [gL, List.count_append]
  push_cast
  ring

/-- The deviation of a token list: the deviation of its word. -/
noncomputable def g (s : List ℕ) : ℝ := gL (flat s)

lemma g_append (u v : List ℕ) : g (u ++ v) = g u + g v := by
  unfold g
  rw [flat_append, gL_append]

lemma g_eq (s : List ℕ) (z o : ℕ) (hz : (flat s).count 0 = z) (ho : (flat s).count 1 = o) :
    g s = z - cc * o := by
  unfold g gL
  rw [hz, ho]

/-- The combination of the deviations of tau^j(s) that removes the roots phi and 0. -/
noncomputable def R (s : List ℕ) : ℝ :=
  g (tau^[5] s) - psi * g (tau^[4] s) + g (tau^[2] s) - psi * g (tau^[1] s)

lemma R_append (u v : List ℕ) : R (u ++ v) = R u + R v := by
  unfold R
  simp only [tauIter_append, g_append]
  ring

lemma R_tok (k : ℕ) (hk : k ≤ 5) : R [k] = 0 := by
  have hf := phi_sq
  unfold R
  interval_cases k
  · rw [g_eq _ 21 10 (by decide +kernel) (by decide +kernel),
      g_eq _ 13 6 (by decide +kernel) (by decide +kernel),
      g_eq _ 5 2 (by decide +kernel) (by decide +kernel),
      g_eq _ 3 1 (by decide +kernel) (by decide +kernel)]
    unfold cc psi
    push_cast
    linear_combination (-70 / 11 : ℝ) * hf
  · rw [g_eq _ 34 15 (by decide +kernel) (by decide +kernel),
      g_eq _ 21 10 (by decide +kernel) (by decide +kernel),
      g_eq _ 8 4 (by decide +kernel) (by decide +kernel),
      g_eq _ 5 2 (by decide +kernel) (by decide +kernel)]
    unfold cc psi
    push_cast
    linear_combination (-120 / 11 : ℝ) * hf
  · rw [g_eq _ 34 15 (by decide +kernel) (by decide +kernel),
      g_eq _ 21 9 (by decide +kernel) (by decide +kernel),
      g_eq _ 8 4 (by decide +kernel) (by decide +kernel),
      g_eq _ 5 3 (by decide +kernel) (by decide +kernel)]
    unfold cc psi
    push_cast
    linear_combination (-120 / 11 : ℝ) * hf
  · rw [g_eq _ 55 25 (by decide +kernel) (by decide +kernel),
      g_eq _ 34 15 (by decide +kernel) (by decide +kernel),
      g_eq _ 13 6 (by decide +kernel) (by decide +kernel),
      g_eq _ 8 4 (by decide +kernel) (by decide +kernel)]
    unfold cc psi
    push_cast
    linear_combination (-190 / 11 : ℝ) * hf
  · rw [g_eq _ 68 31 (by decide +kernel) (by decide +kernel),
      g_eq _ 42 19 (by decide +kernel) (by decide +kernel),
      g_eq _ 16 7 (by decide +kernel) (by decide +kernel),
      g_eq _ 10 5 (by decide +kernel) (by decide +kernel)]
    unfold cc psi
    push_cast
    linear_combination (-240 / 11 : ℝ) * hf
  · rw [g_eq _ 89 41 (by decide +kernel) (by decide +kernel),
      g_eq _ 55 25 (by decide +kernel) (by decide +kernel),
      g_eq _ 21 9 (by decide +kernel) (by decide +kernel),
      g_eq _ 13 6 (by decide +kernel) (by decide +kernel)]
    unfold cc psi
    push_cast
    linear_combination (-310 / 11 : ℝ) * hf

/-- The deviation has no component along phi or 0: it follows the factor
(x - psi)(x^3 + 1) x of the characteristic polynomial. -/
lemma R_zero (s : List ℕ) (hs : Valid s) : R s = 0 := by
  induction s with
  | nil => simp [R, tauIter_nil, tau, g, gL, flat]
  | cons k s ih =>
    obtain ⟨hk, hs'⟩ := valid_cons hs
    rw [show k :: s = [k] ++ s from rfl, R_append, R_tok k hk, ih hs', add_zero]

/-! ### The deviations of the iterates -/

/-- u x j: the deviation of tau^j(x). -/
noncomputable def u (x j : ℕ) : ℝ := g (tau^[j] [x])

lemma u_shift (x j m : ℕ) : g (tau^[m] (tau^[j] [x])) = u x (j + m) := by
  unfold u
  rw [show j + m = m + j from Nat.add_comm j m, Function.iterate_add_apply]

lemma u_one (J : ℕ) : g (tau^[J] [1]) = u 0 (J + 1) := by
  unfold u
  rw [Function.iterate_succ_apply]
  rfl

/-- v j: the deviation of iterate j + 1 minus psi times that of iterate j. -/
noncomputable def v (j : ℕ) : ℝ := u 0 (j + 1) - psi * u 0 j

lemma v_rec (j : ℕ) : v (j + 4) = -v (j + 1) := by
  have h := R_zero (tau^[j] [0]) (tauIter_valid j _ (valid_single (by norm_num)))
  unfold R at h
  rw [u_shift, u_shift, u_shift, u_shift] at h
  unfold v
  rw [show j + 4 + 1 = j + 5 from rfl, show j + 1 + 1 = j + 2 from rfl]
  linarith

lemma u0_val (j z o : ℕ) (hz : (flat (tau^[j] [0])).count 0 = z)
    (ho : (flat (tau^[j] [0])).count 1 = o) : u 0 j = z - cc * o :=
  g_eq _ z o hz ho

lemma v_base : |v 1| ≤ 1.1 ∧ |v 2| ≤ 1.1 ∧ |v 3| ≤ 1.1 := by
  have hf := phi_sq
  obtain ⟨hp1, hp2⟩ := phi_bounds
  have e1 : v 1 = (4 + 5 * phi) / 11 := by
    rw [show v 1 = u 0 2 - psi * u 0 1 from rfl, u0_val 2 5 2 (by decide) (by decide),
      u0_val 1 3 1 (by decide) (by decide)]
    unfold cc psi
    push_cast
    linear_combination (-10 / 11 : ℝ) * hf
  have e2 : v 2 = (-3 - phi) / 11 := by
    rw [show v 2 = u 0 3 - psi * u 0 2 from rfl, u0_val 3 8 4 (by decide) (by decide),
      u0_val 2 5 2 (by decide) (by decide)]
    unfold cc psi
    push_cast
    linear_combination (-20 / 11 : ℝ) * hf
  have e3 : v 3 = (-1 - 4 * phi) / 11 := by
    rw [show v 3 = u 0 4 - psi * u 0 3 from rfl, u0_val 4 13 6 (by decide) (by decide),
      u0_val 3 8 4 (by decide) (by decide)]
    unfold cc psi
    push_cast
    linear_combination (-40 / 11 : ℝ) * hf
  rw [e1, e2, e3, abs_le, abs_le, abs_le]
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> linarith

/-- From j = 1 on, v changes sign every three steps, so it stays within 1.1. -/
lemma v_bound (j : ℕ) : |v (j + 1)| ≤ 1.1 ∧ |v (j + 2)| ≤ 1.1 ∧ |v (j + 3)| ≤ 1.1 := by
  induction j with
  | zero => exact v_base
  | succ j ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    refine ⟨h2, h3, ?_⟩
    rw [show j + 1 + 3 = j + 4 by ring, v_rec, abs_neg]
    exact h1

/-- The deviation of every iterate is at most 2.9 in absolute value. -/
lemma a_bound (j : ℕ) : |u 0 j| ≤ 2.9 := by
  obtain ⟨hp1, hp2⟩ := phi_bounds
  obtain ⟨hc1, hc2⟩ := cc_bounds
  rcases j with _ | j
  · rw [u0_val 0 2 0 (by decide) (by decide)]
    norm_num
  · induction j with
    | zero =>
      rw [u0_val 1 3 1 (by decide) (by decide), abs_le]
      push_cast
      constructor <;> linarith
    | succ j ih =>
      have hv := (v_bound j).1
      have e : u 0 (j + 1 + 1) = v (j + 1) + psi * u 0 (j + 1) := by
        unfold v
        ring
      rw [e]
      have h1 := abs_add_le (v (j + 1)) (psi * u 0 (j + 1))
      rw [abs_mul] at h1
      have hpsi : |psi| ≤ 0.618034 := by
        unfold psi
        rw [abs_le]
        constructor <;> linarith
      have h2 := mul_le_mul hpsi ih (abs_nonneg _) (by norm_num)
      linarith

/-! ### Prefixes of token lists -/

lemma take_append_le (A B : List ℕ) (bA bB : ℝ) (hA : ∀ i, |g (A.take i)| ≤ bA)
    (hB : ∀ i, |g (B.take i)| ≤ bB) (i : ℕ) : |g ((A ++ B).take i)| ≤ max bA (|g A| + bB) := by
  rw [List.take_append]
  rcases le_or_gt i A.length with h | h
  · rw [show i - A.length = 0 by omega, List.take_zero, List.append_nil]
    exact le_trans (hA i) (le_max_left _ _)
  · rw [List.take_of_length_le h.le, g_append]
    have h1 := hB (i - A.length)
    have h2 := abs_add_le (g A) (g (B.take (i - A.length)))
    exact le_trans (by linarith) (le_max_right _ _)

lemma gtok_bound (x : ℕ) (hx : x ≤ 5) : |g [x]| ≤ 3 := by
  obtain ⟨hc1, hc2⟩ := cc_bounds
  interval_cases x
  · rw [g_eq [0] 2 0 (by decide) (by decide), abs_le]; constructor <;> norm_num
  · rw [g_eq [1] 3 1 (by decide) (by decide), abs_le]; constructor <;> norm_num <;> linarith
  · rw [g_eq [2] 3 2 (by decide) (by decide), abs_le]; constructor <;> norm_num <;> linarith
  · rw [g_eq [3] 5 3 (by decide) (by decide), abs_le]; constructor <;> norm_num <;> linarith
  · rw [g_eq [4] 6 4 (by decide) (by decide), abs_le]; constructor <;> norm_num <;> linarith
  · rw [g_eq [5] 8 5 (by decide) (by decide), abs_le]; constructor <;> norm_num <;> linarith

/-- |g| over the prefixes of tau^J(x). -/
lemma prefix_bound (J : ℕ) : ∀ x, x ≤ 5 → ∀ i, |g ((tau^[J] [x]).take i)| ≤ 3 + 6 * (J : ℝ) := by
  induction J with
  | zero =>
    intro x hx i
    simp only [Function.iterate_zero, id, Nat.cast_zero, mul_zero, add_zero]
    rcases i with _ | i
    · norm_num [g, flat, gL]
    · rw [show [x].take (i + 1) = [x] by simp]
      exact gtok_bound x hx
  | succ J ih =>
    intro x hx i
    have hA := a_bound J
    have hB : |g (tau^[J] [1])| ≤ 2.9 := by rw [u_one]; exact a_bound (J + 1)
    rw [Function.iterate_succ_apply, tau_single]
    push_cast
    interval_cases x
    · exact le_trans (ih 1 (by norm_num) i) (by linarith)
    · rw [show tauT 1 = [0] ++ [2] from rfl, tauIter_append]
      have h := take_append_le _ _ _ _ (ih 0 (by norm_num)) (ih 2 (by norm_num)) i
      refine le_trans h (max_le (by linarith) ?_)
      show |u 0 J| + (3 + 6 * (J : ℝ)) ≤ 3 + 6 * ((J : ℝ) + 1)
      linarith
    · exact le_trans (ih 3 (by norm_num) i) (by linarith)
    · rw [show tauT 3 = [0] ++ [4] from rfl, tauIter_append]
      have h := take_append_le _ _ _ _ (ih 0 (by norm_num)) (ih 4 (by norm_num)) i
      refine le_trans h (max_le (by linarith) ?_)
      show |u 0 J| + (3 + 6 * (J : ℝ)) ≤ 3 + 6 * ((J : ℝ) + 1)
      linarith
    · rw [show tauT 4 = [0] ++ [5] from rfl, tauIter_append]
      have h := take_append_le _ _ _ _ (ih 0 (by norm_num)) (ih 5 (by norm_num)) i
      refine le_trans h (max_le (by linarith) ?_)
      show |u 0 J| + (3 + 6 * (J : ℝ)) ≤ 3 + 6 * ((J : ℝ) + 1)
      linarith
    · rw [show tauT 5 = [0] ++ ([1] ++ [5]) from rfl, tauIter_append, tauIter_append]
      have h1 := take_append_le _ _ _ _ (ih 1 (by norm_num)) (ih 5 (by norm_num))
      have h2 := take_append_le _ _ _ _ (ih 0 (by norm_num)) h1 i
      refine le_trans h2 (max_le (by linarith) ?_)
      show |u 0 J| + max (3 + 6 * (J : ℝ)) (|g (tau^[J] [1])| + (3 + 6 * (J : ℝ))) ≤
        3 + 6 * ((J : ℝ) + 1)
      have hm : max (3 + 6 * (J : ℝ)) (|g (tau^[J] [1])| + (3 + 6 * (J : ℝ))) ≤
          |g (tau^[J] [1])| + (3 + 6 * (J : ℝ)) :=
        max_le (by linarith [abs_nonneg (g (tau^[J] [1]))]) le_rfl
      linarith

/-! ### Letters -/

lemma gL_tok_take (k : ℕ) (hk : k ≤ 5) (r : ℕ) : |gL ((tok k).take r)| ≤ 11 := by
  obtain ⟨hc1, hc2⟩ := cc_bounds
  have hz : ((tok k).take r).count 0 ≤ 8 := by
    calc ((tok k).take r).count 0 ≤ (tok k).count 0 := List.Sublist.count_le _ (List.take_sublist _ _)
      _ ≤ 8 := by interval_cases k <;> decide
  have ho : ((tok k).take r).count 1 ≤ 5 := by
    calc ((tok k).take r).count 1 ≤ (tok k).count 1 := List.Sublist.count_le _ (List.take_sublist _ _)
      _ ≤ 5 := by interval_cases k <;> decide
  have hz' : (((tok k).take r).count 0 : ℝ) ≤ 8 := by exact_mod_cast hz
  have ho' : (((tok k).take r).count 1 : ℝ) ≤ 5 := by exact_mod_cast ho
  have hz0 : (0 : ℝ) ≤ ((tok k).take r).count 0 := Nat.cast_nonneg _
  have ho0 : (0 : ℝ) ≤ ((tok k).take r).count 1 := Nat.cast_nonneg _
  unfold gL
  rw [abs_le]
  constructor <;> nlinarith

lemma flat_split : ∀ S : List ℕ, Valid S → ∀ t,
    ∃ i, |gL ((flat S).take t) - g (S.take i)| ≤ 11 := by
  intro S
  induction S with
  | nil =>
    intro _ t
    refine ⟨0, ?_⟩
    norm_num [flat, g, gL]
  | cons k S ih =>
    intro hv t
    obtain ⟨hk, hv'⟩ := valid_cons hv
    rw [flat_cons]
    rcases le_or_gt t (tok k).length with h | h
    · refine ⟨0, ?_⟩
      rw [List.take_append_of_le_length h]
      simpa [g, flat, gL] using gL_tok_take k hk t
    · obtain ⟨i, hi⟩ := ih hv' (t - (tok k).length)
      refine ⟨i + 1, ?_⟩
      rw [List.take_append, List.take_of_length_le h.le, gL_append,
        show (k :: S).take (i + 1) = [k] ++ S.take i from rfl, g_append]
      have e : g [k] = gL (tok k) := by simp [g, flat]
      rw [e]
      have : gL (tok k) + gL ((flat S).take (t - (tok k).length)) - (gL (tok k) + g (S.take i)) =
          gL ((flat S).take (t - (tok k).length)) - g (S.take i) := by ring
      rw [this]
      exact hi

/-! ### The length of the iterates -/

/-- The Perron weight of a token: 1, phi, phi, 1 + phi, 2 phi, 1 + 2 phi. -/
noncomputable def wt : ℕ → ℝ
  | 0 => 1
  | 1 => phi
  | 2 => phi
  | 3 => 1 + phi
  | 4 => 2 * phi
  | _ => 1 + 2 * phi

/-- The weight of a token list; tau multiplies it by phi. -/
noncomputable def Phi (s : List ℕ) : ℝ := (s.map wt).sum

lemma Phi_append (u v : List ℕ) : Phi (u ++ v) = Phi u + Phi v := by
  simp [Phi]

lemma Phi_tau (s : List ℕ) (hs : Valid s) : Phi (tau s) = phi * Phi s := by
  have hf := phi_sq
  induction s with
  | nil => simp [Phi, tau]
  | cons k s ih =>
    obtain ⟨hk, hs'⟩ := valid_cons hs
    rw [tau_cons, Phi_append, ih hs', show k :: s = [k] ++ s from rfl, Phi_append, mul_add]
    congr 1
    interval_cases k <;> simp [Phi, tauT, wt] <;>
      first | ring1 | linear_combination (-1 : ℝ) * hf | linear_combination (-2 : ℝ) * hf

lemma Phi_iter (J : ℕ) : Phi (tau^[J] [0]) = phi ^ J := by
  induction J with
  | zero => simp [Phi, wt]
  | succ J ih =>
    rw [Function.iterate_succ_apply', Phi_tau _ (tauIter_valid J _ (valid_single (by norm_num))),
      ih, pow_succ]
    ring

lemma length_ge_Phi (s : List ℕ) (hs : Valid s) : 2 * Phi s ≤ ((flat s).length : ℝ) := by
  obtain ⟨hp1, hp2⟩ := phi_bounds
  induction s with
  | nil => simp [Phi, flat]
  | cons k s ih =>
    obtain ⟨hk, hs'⟩ := valid_cons hs
    rw [flat_cons, List.length_append, show k :: s = [k] ++ s from rfl, Phi_append]
    push_cast
    have := ih hs'
    have hk' : 2 * Phi [k] ≤ ((tok k).length : ℝ) := by
      interval_cases k <;> simp [Phi, wt, tok] <;> linarith
    linarith

lemma iter_length_ge (J : ℕ) : 2 * phi ^ J ≤ ((iter J).length : ℝ) := by
  have h := length_ge_Phi _ (tauIter_valid J _ (valid_single (show 0 ≤ 5 by norm_num)))
  rw [Phi_iter] at h
  rw [iter_eq]
  exact h

/-! ### Counting along the limiting word -/

lemma W_le (i : ℕ) : W i ≤ 1 := by
  have hi : i < (V (i + 1)).length := by have := V_length (i + 1); omega
  rw [W_eq (i + 1) i hi, List.getD_eq_getElem _ _ hi]
  exact iter_letters _ _ (List.getElem_mem hi)

/-- Z(N): the number of letters 0 among the first N letters of W. -/
noncomputable def Z (N : ℕ) : ℕ := Nat.count (fun i => W i = 0) N

/-- O(N): the number of letters 1 among the first N letters of W. -/
noncomputable def O (N : ℕ) : ℕ := Nat.count (fun i => W i = 1) N

lemma Z_succ (N : ℕ) : Z (N + 1) = Z N + if W N = 0 then 1 else 0 := Nat.count_succ _ _

lemma O_succ (N : ℕ) : O (N + 1) = O N + if W N = 1 then 1 else 0 := Nat.count_succ _ _

lemma counts_eq (k N : ℕ) (hN : N ≤ (V k).length) :
    Z N = ((V k).take N).count 0 ∧ O N = ((V k).take N).count 1 := by
  induction N with
  | zero => simp [Z, O]
  | succ N ih =>
    have hN' : N < (V k).length := by omega
    have hW : W N = (V k)[N] := by rw [W_eq k N hN', List.getD_eq_getElem _ _ hN']
    obtain ⟨h1, h2⟩ := ih (by omega)
    rw [Z_succ, O_succ, h1, h2, List.take_add_one, List.getElem?_eq_getElem hN',
      List.count_append, List.count_append, hW]
    constructor <;> simp [List.count_singleton]

/-- D(N) = Z(N) - c O(N) is the deviation over the first N letters of W. -/
noncomputable def D (N : ℕ) : ℝ := (Z N : ℝ) - cc * (O N : ℝ)

lemma D_eq (k N : ℕ) (hN : N ≤ (V k).length) : D N = gL ((V k).take N) := by
  obtain ⟨h1, h2⟩ := counts_eq k N hN
  simp [D, gL, h1, h2]

lemma O_add_Z (N : ℕ) : O N + Z N = N := by
  induction N with
  | zero => simp [O, Z]
  | succ N ih =>
    rw [O_succ, Z_succ]
    have := W_le N
    split_ifs <;> omega

lemma D_triv (N : ℕ) : |D N| ≤ cc * N := by
  obtain ⟨hc1, hc2⟩ := cc_bounds
  have hs : ((O N : ℕ) : ℝ) + (Z N : ℝ) = N := by exact_mod_cast O_add_Z N
  have hz : (0 : ℝ) ≤ Z N := Nat.cast_nonneg _
  have ho : (0 : ℝ) ≤ O N := Nat.cast_nonneg _
  unfold D
  rw [abs_le]
  constructor <;> nlinarith

/-! ### Level of a prefix -/

lemma pow_bound (J : ℕ) (hJ : 11 ≤ J) : 17 + 6 * (J : ℝ) < 0.46 * phi ^ J := by
  obtain ⟨hp1, hp2⟩ := phi_bounds
  induction J, hJ using Nat.le_induction with
  | base =>
    have : (1.6180339 : ℝ) ^ 11 ≤ phi ^ 11 := pow_le_pow_left₀ (by norm_num) hp1.le 11
    norm_num at this ⊢
    linarith
  | succ J hJ ih =>
    rw [pow_succ phi J]
    push_cast
    have hp : 0 ≤ phi ^ J := by positivity
    have hJ' : (11 : ℝ) ≤ J := by exact_mod_cast hJ
    nlinarith

lemma sq_bound (J : ℕ) (hJ : 11 ≤ J) : (17 + 6 * (J : ℝ)) ^ 2 ≤ 40 * phi ^ J := by
  obtain ⟨hp1, hp2⟩ := phi_bounds
  induction J, hJ using Nat.le_induction with
  | base =>
    have : (1.6180339 : ℝ) ^ 11 ≤ phi ^ 11 := pow_le_pow_left₀ (by norm_num) hp1.le 11
    norm_num at this ⊢
    linarith
  | succ J hJ ih =>
    rw [pow_succ phi J]
    push_cast
    have hp : 0 ≤ phi ^ J := by positivity
    have hJ' : (11 : ℝ) ≤ J := by exact_mod_cast hJ
    have h1 := mul_le_mul_of_nonneg_right ih (show (0 : ℝ) ≤ phi by linarith)
    have h2 := mul_le_mul_of_nonneg_right hp1.le (sq_nonneg (17 + 6 * (J : ℝ)))
    nlinarith

lemma V6_length : (V 6).length = 887 := by decide +kernel

/-- For N > 887 there is a level J >= 11 with 2 phi^J < N and |D(N)| <= 17 + 6J. -/
lemma level (N : ℕ) (hN : 887 < N) :
    ∃ J : ℕ, 11 ≤ J ∧ 2 * phi ^ J < (N : ℝ) ∧ |D N| ≤ 17 + 6 * (J : ℝ) := by
  have hex : ∃ k, N ≤ (V k).length := ⟨N, by have := V_length N; omega⟩
  classical
  have hk : N ≤ (V (Nat.find hex)).length := Nat.find_spec hex
  have h6 := V6_length
  have hk7 : 7 ≤ Nat.find hex := by
    by_contra h
    have := (V_prefix (show Nat.find hex ≤ 6 by omega)).length_le
    omega
  have hmin : (V (Nat.find hex - 1)).length < N := by
    have := Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega)
    omega
  have h2 : 2 * Nat.find hex + res = 2 * (Nat.find hex - 1) + res + 2 := by omega
  have e : V (Nat.find hex) = iter (2 * (Nat.find hex - 1) + res) ++
      flat (tau^[2 * (Nat.find hex - 1) + res] [2]) := by
    rw [← iter_two, ← h2]
    rfl
  have e' : V (Nat.find hex - 1) = iter (2 * (Nat.find hex - 1) + res) := rfl
  set J := 2 * (Nat.find hex - 1) + res with hJ
  refine ⟨J, by omega, ?_, ?_⟩
  · have hl := iter_length_ge J
    rw [e'] at hmin
    have : ((iter J).length : ℝ) < N := by exact_mod_cast hmin
    linarith
  · rw [D_eq (Nat.find hex) N hk, e]
    rw [e'] at hmin
    rw [List.take_append, List.take_of_length_le hmin.le, gL_append]
    obtain ⟨i, hi⟩ := flat_split (tau^[J] [2]) (tauIter_valid J _ (valid_single (by norm_num)))
      (N - (iter J).length)
    have hpre := prefix_bound J 2 (by norm_num) i
    have hA := a_bound J
    have hu : gL (iter J) = u 0 J := by rw [iter_eq]; rfl
    rw [hu]
    have h1 := abs_add_le (u 0 J) (gL ((flat (tau^[J] [2])).take (N - (iter J).length)))
    have h3 := abs_sub_abs_le_abs_sub (gL ((flat (tau^[J] [2])).take (N - (iter J).length)))
      (g ((tau^[J] [2]).take i))
    linarith

/-- Over every prefix of W longer than 887 letters, |D| < 0.23 N. -/
lemma D_small (N : ℕ) (hN : 887 < N) : |D N| < 0.23 * (N : ℝ) := by
  obtain ⟨J, hJ, hNr, hD⟩ := level N hN
  have hp := pow_bound J hJ
  linarith

/-- D(N)^2 <= 8000 N for every N. -/
lemma D_sq (N : ℕ) : D N ^ 2 ≤ 8000 * (N : ℝ) := by
  obtain ⟨hc1, hc2⟩ := cc_bounds
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  rcases le_or_gt N 887 with h | h
  · have h1 := D_triv N
    have hN1 : (N : ℝ) ≤ 887 := by exact_mod_cast h
    have h2 : D N ^ 2 ≤ (cc * N) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) h1 2
    have h3 : cc ^ 2 ≤ 4.84 := by nlinarith
    have h4 : (cc * (N : ℝ)) ^ 2 ≤ 4.84 * 887 * N := by
      have : (cc * (N : ℝ)) ^ 2 = cc ^ 2 * N * N := by ring
      rw [this]
      have hc2' : 0 ≤ cc ^ 2 := sq_nonneg _
      have := mul_le_mul h3 hN1 hN0 (by norm_num)
      nlinarith
    linarith
  · obtain ⟨J, hJ, hNr, hD⟩ := level N h
    have h1 : D N ^ 2 ≤ (17 + 6 * (J : ℝ)) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) hD 2
    have h2 := sq_bound J hJ
    linarith

/-! ### The positions of 1 -/

/-- The limit, 1 + c = 3.19821... -/
noncomputable def m1 : ℝ := 1 + cc

lemma m1_bounds : 3.198211 ≤ m1 ∧ m1 ≤ 3.198213 := by
  obtain ⟨hc1, hc2⟩ := cc_bounds
  unfold m1
  constructor <;> linarith

lemma ones_infinite : (setOf (fun i => W i = 1)).Infinite := by
  obtain ⟨hc1, hc2⟩ := cc_bounds
  apply Set.infinite_of_not_bddAbove
  rintro ⟨B, hB⟩
  have hconst : ∀ j, O (B + 1 + j) = O (B + 1) := by
    intro j
    induction j with
    | zero => rfl
    | succ j ih =>
      have hno : ¬ W (B + 1 + j) = 1 := fun h => by
        have := hB h
        omega
      rw [show B + 1 + (j + 1) = B + 1 + j + 1 by ring, O_succ, if_neg hno, ih, add_zero]
  have h := D_small (B + 1 + (5 * O (B + 1) + 1500)) (by omega)
  have hs := O_add_Z (B + 1 + (5 * O (B + 1) + 1500))
  rw [hconst] at hs
  unfold D at h
  rw [hconst, abs_lt] at h
  obtain ⟨-, h2⟩ := h
  have hZ : (Z (B + 1 + (5 * O (B + 1) + 1500)) : ℝ) =
      ((B + 1 + (5 * O (B + 1) + 1500) : ℕ) : ℝ) - O (B + 1) := by
    have : (O (B + 1) : ℝ) + Z (B + 1 + (5 * O (B + 1) + 1500)) =
        ((B + 1 + (5 * O (B + 1) + 1500) : ℕ) : ℝ) := by exact_mod_cast hs
    linarith
  rw [hZ] at h2
  generalize ho : (O (B + 1) : ℝ) = z at h2
  have hz0 : 0 ≤ z := by rw [← ho]; exact Nat.cast_nonneg _
  have hz' : ((B + 1 + (5 * O (B + 1) + 1500) : ℕ) : ℝ) = (B : ℝ) + 1 + (5 * z + 1500) := by
    rw [← ho]; push_cast; ring
  rw [hz'] at h2
  have hB0 : (0 : ℝ) ≤ B := Nat.cast_nonneg _
  have hP := mul_le_mul_of_nonneg_right hc2 hz0
  clear hconst hs hZ ho hz' hB
  nlinarith [hP]

lemma a_spec (n : ℕ) (hn : 1 ≤ n) : O (a n) = n ∧ Z (a n) = a n - n := by
  have hinf := ones_infinite
  have hOp : O (Nat.nth (fun i => W i = 1) (n - 1)) = n - 1 :=
    Nat.count_nth_of_infinite hinf (n - 1)
  have hWp : W (Nat.nth (fun i => W i = 1) (n - 1)) = 1 := Nat.nth_mem_of_infinite hinf (n - 1)
  have hO1 : O (a n) = n := by
    unfold a
    rw [O_succ, if_pos hWp, hOp]
    omega
  refine ⟨hO1, ?_⟩
  have := O_add_Z (a n)
  omega

/-- At the n-th 1, m n - a(n) = -D. -/
lemma a_dev (n : ℕ) (hn : 1 ≤ n) : m1 * n - a n = -D (a n) := by
  obtain ⟨hO, hZ⟩ := a_spec n hn
  have hle : n ≤ a n := by have := O_add_Z (a n); omega
  unfold D m1
  rw [hZ, hO]
  push_cast [hle]
  ring

/-- A linear scan of a word, checking 15 n < 10 (t + 1) < 40 n at the n-th letter 1, with
t + 1 its position. -/
def chk : List ℕ → ℕ → ℕ → Bool
  | [], _, _ => true
  | x :: l, t, o =>
    if x = 1 then decide (15 * (o + 1) < 10 * (t + 1) ∧
      10 * (t + 1) < 40 * (o + 1)) && chk l (t + 1) (o + 1)
    else chk l (t + 1) o

lemma chk_spec : ∀ (L : List ℕ) (t o : ℕ), chk L t o = true →
    ∀ i < L.length, L.getD i 0 = 1 →
      15 * (o + (L.take (i + 1)).count 1) < 10 * (t + i + 1) ∧
        10 * (t + i + 1) < 40 * (o + (L.take (i + 1)).count 1) := by
  intro L
  induction L with
  | nil =>
    intro t o _ i hi
    simp at hi
  | cons x l ih =>
    intro t o h i hi hx
    by_cases h1 : x = 1
    · subst h1
      have h' : (15 * (o + 1) < 10 * (t + 1) ∧ 10 * (t + 1) < 40 * (o + 1)) ∧
          chk l (t + 1) (o + 1) = true := by
        simpa [chk] using h
      rcases i with _ | i
      · simpa using h'.1
      · have := ih (t + 1) (o + 1) h'.2 i (by simp at hi; omega) (by simpa using hx)
        have e : ((1 :: l).take (i + 1 + 1)).count 1 = (l.take (i + 1)).count 1 + 1 := by
          simp [List.take_succ_cons]
        rw [e]
        constructor <;> omega
    · have h' : chk l (t + 1) o = true := by simpa [chk, h1] using h
      rcases i with _ | i
      · simp at hx
        exact absurd hx h1
      · have := ih (t + 1) o h' i (by simp at hi; omega) (by simpa using hx)
        have e : ((x :: l).take (i + 1 + 1)).count 1 = (l.take (i + 1)).count 1 := by
          simp [List.take_succ_cons, h1]
        rw [e]
        constructor <;> omega

lemma chk_word : chk (V 6) 0 0 = true := by decide +kernel

lemma bound_small (n : ℕ) (hn : 1 ≤ n) (ha : a n ≤ 887) :
    -1 < m1 - (a n : ℝ) / n ∧ m1 - (a n : ℝ) / n < 2 := by
  obtain ⟨hm1, hm2⟩ := m1_bounds
  obtain ⟨hO, hZ⟩ := a_spec n hn
  have hinf := ones_infinite
  have hWp : W (Nat.nth (fun i => W i = 1) (n - 1)) = 1 := Nat.nth_mem_of_infinite hinf (n - 1)
  have ha' : a n = Nat.nth (fun i => W i = 1) (n - 1) + 1 := rfl
  set t := Nat.nth (fun i => W i = 1) (n - 1) with ht
  have hlen := V6_length
  have hW : (V 6).getD t 0 = 1 := by rw [← W_eq 6 t (by omega)]; exact hWp
  have hc := chk_spec (V 6) 0 0 chk_word t (by omega) hW
  have hO' : ((V 6).take (t + 1)).count 1 = n := by
    rw [← (counts_eq 6 (t + 1) (by omega)).2, ← ha', hO]
  rw [hO'] at hc
  simp only [zero_add] at hc
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hc1 : (15 : ℝ) * n < 10 * (a n) := by
    rw [ha']
    exact_mod_cast hc.1
  have hc2 : (10 : ℝ) * (a n) < 40 * n := by
    rw [ha']
    exact_mod_cast hc.2
  have h1 : (a n : ℝ) / n < 4 := by
    rw [div_lt_iff₀ hnpos]
    linarith
  have h2 : 1.5 < (a n : ℝ) / n := by
    rw [lt_div_iff₀ hnpos]
    linarith
  constructor <;> linarith

lemma bound_large (n : ℕ) (hn : 1 ≤ n) (ha : 887 < a n) :
    -1 < m1 - (a n : ℝ) / n ∧ m1 - (a n : ℝ) / n < 2 := by
  obtain ⟨hc1, hc2⟩ := cc_bounds
  have hD := D_small (a n) ha
  obtain ⟨hO, hZ⟩ := a_spec n hn
  have hle : n ≤ a n := by have := O_add_Z (a n); omega
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hdev := a_dev n hn
  have hDdef : D (a n) = ((a n : ℝ) - n) - cc * n := by
    unfold D
    rw [hZ, hO]
    push_cast [hle]
    ring
  rw [abs_lt, hDdef] at hD
  obtain ⟨hD1, hD2⟩ := hD
  have e : m1 - (a n : ℝ) / n = (m1 * n - a n) / n := by field_simp
  rw [e, hdev, hDdef]
  have hQ1 : 2.198211 * (n : ℝ) ≤ cc * n := mul_le_mul_of_nonneg_right hc1 hnpos.le
  have hQ2 : cc * (n : ℝ) ≤ 2.198213 * n := mul_le_mul_of_nonneg_right hc2 hnpos.le
  constructor
  · rw [lt_div_iff₀ hnpos]
    linarith
  · rw [div_lt_iff₀ hnpos]
    linarith

/-- Kimberling's conjecture: a(n)/n tends to a number m = 3.19..., and -1 < m - a(n)/n < 2
for n >= 1. -/
theorem conjecture : ∃ m : ℝ, (3.19 ≤ m ∧ m < 3.20) ∧
    Tendsto (fun n : ℕ => (a n : ℝ) / n) atTop (𝓝 m) ∧
    ∀ n : ℕ, 1 ≤ n → -1 < m - (a n : ℝ) / n ∧ m - (a n : ℝ) / n < 2 := by
  obtain ⟨hm1, hm2⟩ := m1_bounds
  have hbound : ∀ n : ℕ, 1 ≤ n → -1 < m1 - (a n : ℝ) / n ∧ m1 - (a n : ℝ) / n < 2 := by
    intro n hn
    rcases le_or_gt (a n) 887 with h | h
    · exact bound_small n hn h
    · exact bound_large n hn h
  refine ⟨m1, ⟨by linarith, by linarith⟩, ?_, hbound⟩
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hlim : Tendsto (fun n : ℕ => Real.sqrt (40000 / n)) atTop (𝓝 0) := by
    have := (tendsto_const_div_atTop_nhds_zero_nat (40000 : ℝ)).sqrt
    simpa using this
  refine squeeze_zero' (Eventually.of_forall fun n => norm_nonneg _) ?_ hlim
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hb := hbound n hn
  have ha5 : (a n : ℝ) ≤ 5 * n := by
    have h1 : (a n : ℝ) / n < 4.198213 := by linarith [hb.1]
    rw [div_lt_iff₀ hnpos] at h1
    linarith
  have hsq := D_sq (a n)
  have hdev := a_dev n hn
  rw [Real.norm_eq_abs]
  apply Real.abs_le_sqrt
  have e : (a n : ℝ) / n - m1 = D (a n) / n := by
    have : (a n : ℝ) = m1 * n + D (a n) := by linarith
    rw [this]
    field_simp
    ring
  have key : ((a n : ℝ) / n - m1) ^ 2 = D (a n) ^ 2 / n ^ 2 := by
    rw [e]
    field_simp
  rw [key, div_le_div_iff₀ (by positivity) hnpos]
  have hD5 : D (a n) ^ 2 ≤ 8000 * (5 * n) := by
    have : (8000 : ℝ) * (a n) ≤ 8000 * (5 * n) := by linarith
    linarith
  nlinarith [hD5, hnpos]

end OMA.S_oeis_a287448

theorem OMA.solution : type_of% @OMA.S_oeis_a287448.main :=
  OMA.S_oeis_a287448.conjecture
