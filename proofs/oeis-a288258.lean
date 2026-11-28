import OMAStatements.S_oeis_a288258

namespace OMA.S_oeis_a288258

open Filter Topology





/-! ### One pass -/

/-- Induction along the cases of `step`. -/
theorem step_rec {P : List ℕ → Prop} (h0 : P []) (h00 : ∀ l, P l → P (0 :: 0 :: l))
    (h1 : ∀ l, P l → P (1 :: l)) (hz : P [0])
    (hzy : ∀ y l, P ((y + 1) :: l) → P (0 :: (y + 1) :: l))
    (hx : ∀ x l, P l → P ((x + 2) :: l)) : ∀ u, P u := by
  have key : ∀ n, ∀ u : List ℕ, u.length ≤ n → P u := by
    intro n
    induction n with
    | zero =>
      intro u hu
      cases u with
      | nil => exact h0
      | cons x l => simp at hu
    | succ n ih =>
      intro u hu
      rcases u with _ | ⟨x, l⟩
      · exact h0
      · simp only [List.length_cons] at hu
        rcases x with _ | _ | x
        · rcases l with _ | ⟨y, l⟩
          · exact hz
          · rcases y with _ | y
            · exact h00 l (ih l (by simp at hu; omega))
            · exact hzy y l (ih _ (by simpa using hu))
        · exact h1 l (ih l (by omega))
        · exact hx x l (ih l (by omega))
  exact fun u => key u.length u le_rfl

/-- The rule 1 -> 100 reads its letter alone, so the pass restarts at every letter 1. -/
lemma step_cut (u : List ℕ) : ∀ w, step (u ++ 1 :: w) = step u ++ step (1 :: w) := by
  refine step_rec (P := fun u => ∀ w, step (u ++ 1 :: w) = step u ++ step (1 :: w))
    ?_ ?_ ?_ ?_ ?_ ?_ u
  · intro w
    rfl
  · intro l ih w
    show 0 :: 0 :: 1 :: 0 :: step (l ++ 1 :: w) = 0 :: 0 :: 1 :: 0 :: step l ++ step (1 :: w)
    rw [ih]
    rfl
  · intro l ih w
    show 1 :: 0 :: 0 :: step (l ++ 1 :: w) = 1 :: 0 :: 0 :: step l ++ step (1 :: w)
    rw [ih]
    rfl
  · intro w
    rfl
  · intro y l ih w
    show 0 :: step ((y + 1) :: l ++ 1 :: w) = 0 :: step ((y + 1) :: l) ++ step (1 :: w)
    rw [ih]
    rfl
  · intro x l ih w
    show (x + 2) :: step (l ++ 1 :: w) = (x + 2) :: step l ++ step (1 :: w)
    rw [ih]
    rfl

/-! ### Tokens -/

/-- The token k is the word 1 0^k. -/
def tok (k : ℕ) : List ℕ := 1 :: List.replicate k 0

/-- The word of a list of tokens. -/
def flat (s : List ℕ) : List ℕ := s.flatMap tok

/-- The images of the tokens: 10 -> 1000, 100 -> 10000.10, 1000 -> 10000.100,
10000 -> 10000.1000.10. -/
def tauT : ℕ → List ℕ
  | 1 => [3]
  | 2 => [4, 1]
  | 3 => [4, 2]
  | _ => [4, 3, 1]

/-- The token morphism. -/
def tau (s : List ℕ) : List ℕ := s.flatMap tauT

/-- All tokens are 1, 2, 3 or 4. -/
def Valid (s : List ℕ) : Prop := ∀ k ∈ s, 1 ≤ k ∧ k ≤ 4

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
  rcases k with _ | _ | _ | _ | k <;> simp [tauT] at hx <;> omega

lemma tau_valid (s : List ℕ) : Valid (tau s) := by
  intro x hx
  simp only [tau, List.mem_flatMap] at hx
  obtain ⟨k, -, hk⟩ := hx
  exact tauT_valid k x hk

lemma valid_cons {k : ℕ} {s : List ℕ} (h : Valid (k :: s)) : (1 ≤ k ∧ k ≤ 4) ∧ Valid s :=
  ⟨h k (by simp), fun x hx => h x (by simp [hx])⟩

lemma valid_single {x : ℕ} (hx : 1 ≤ x ∧ x ≤ 4) : Valid [x] := by
  intro y hy
  simp at hy
  subst hy
  exact hx

lemma step_append_flat (u s : List ℕ) : step (u ++ flat s) = step u ++ step (flat s) := by
  rcases s with _ | ⟨j, s⟩
  · rw [show flat [] = [] from rfl, List.append_nil, show step [] = [] from rfl,
      List.append_nil]
  · rw [flat_cons, show tok j ++ flat s = 1 :: (List.replicate j 0 ++ flat s) from rfl,
      step_cut]

lemma step_tok (k : ℕ) (hk : 1 ≤ k ∧ k ≤ 4) : step (tok k) = flat (tauT k) := by
  obtain ⟨h1, h4⟩ := hk
  interval_cases k <;> rfl

lemma step_flat (s : List ℕ) (hs : Valid s) : step (flat s) = flat (tau s) := by
  induction s with
  | nil => rfl
  | cons k s ih =>
    obtain ⟨hk, hs'⟩ := valid_cons hs
    rw [flat_cons, tau_cons, flat_append, step_append_flat, step_tok k hk, ih hs']

lemma tauIter_append (n : ℕ) (u v : List ℕ) : tau^[n] (u ++ v) = tau^[n] u ++ tau^[n] v := by
  induction n generalizing u v with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply, Function.iterate_succ_apply,
      Function.iterate_succ_apply, tau_append, ih]

lemma tauIter_valid (n : ℕ) (s : List ℕ) (hs : Valid s) : Valid (tau^[n] s) := by
  cases n with
  | zero => exact hs
  | succ n =>
    rw [Function.iterate_succ_apply']
    exact tau_valid _

lemma tauIter_nil (n : ℕ) : tau^[n] [] = [] := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply]; exact ih

lemma flat_length_pos (s : List ℕ) (hs : s ≠ []) : 1 ≤ (flat s).length := by
  rcases s with _ | ⟨k, s⟩
  · exact absurd rfl hs
  · rw [flat_cons, List.length_append]
    simp [tok]
    omega

lemma tauT_ne_nil (k : ℕ) : tauT k ≠ [] := by
  rcases k with _ | _ | _ | _ | k <;> simp [tauT]

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

/-! ### The iterates -/

/-- T n: the tokens of iterate n after its first two letters. -/
def T : ℕ → List ℕ
  | 0 => []
  | n + 1 => 1 :: tau (T n)

lemma T_valid (n : ℕ) : Valid (T n) := by
  cases n with
  | zero => intro x hx; simp [T] at hx
  | succ n =>
    intro x hx
    simp only [T, List.mem_cons] at hx
    rcases hx with hx | hx
    · omega
    · exact tau_valid _ x hx

/-- Iterate n is 00 followed by the tokens T n. -/
lemma iter_eq (n : ℕ) : iter n = [0, 0] ++ flat (T n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [show iter (n + 1) = step (iter n) from rfl, ih, step_append_flat,
      step_flat _ (T_valid n)]
    rfl

lemma T_succ (n : ℕ) : T (n + 1) = T n ++ tau^[n] [1] := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have h1 : T (n + 1 + 1) = 1 :: tau (T (n + 1)) := rfl
    rw [h1]
    conv_lhs => rw [ih]
    rw [tau_append, Function.iterate_succ_apply']
    rfl

lemma iter_prefix_succ (n : ℕ) : iter n <+: iter (n + 1) := by
  rw [iter_eq, iter_eq, T_succ, flat_append, ← List.append_assoc]
  exact List.prefix_append _ _

lemma iter_prefix {m n : ℕ} (h : m ≤ n) : iter m <+: iter n := by
  induction n, h using Nat.le_induction with
  | base => exact List.prefix_refl _
  | succ n _ ih => exact ih.trans (iter_prefix_succ n)

lemma iter_length (n : ℕ) : n + 2 ≤ (iter n).length := by
  induction n with
  | zero => simp [iter]
  | succ n ih =>
    have h : (iter (n + 1)).length = (iter n).length + (flat (tau^[n] [1])).length := by
      rw [iter_eq, iter_eq, T_succ, flat_append, List.length_append, List.length_append,
        List.length_append]
      ring
    have := flat_length_pos _ (tauIter_ne_nil n [1] (by simp))
    omega

lemma getD_prefix {l₁ l₂ : List ℕ} (h : l₁ <+: l₂) {i : ℕ} (hi : i < l₁.length) :
    l₁.getD i 0 = l₂.getD i 0 := by
  obtain ⟨s, rfl⟩ := h
  rw [List.getD_append _ _ _ _ hi]

lemma W_eq (m i : ℕ) (hi : i < (iter m).length) : W i = (iter m).getD i 0 := by
  unfold W
  rcases le_total (i + 1) m with h | h
  · exact getD_prefix (iter_prefix h) (by have := iter_length (i + 1); omega)
  · exact (getD_prefix (iter_prefix h) hi).symm

/-! ### The Perron root -/

lemma lam_exists : ∃ x : ℝ, 2.1303 ≤ x ∧ x ≤ 2.1304 ∧ x ^ 3 - x ^ 2 - x - 3 = 0 := by
  have hc : ContinuousOn (fun x : ℝ => x ^ 3 - x ^ 2 - x - 3) (Set.Icc 2.1303 2.1304) := by
    fun_prop
  have h := intermediate_value_Icc (show (2.1303 : ℝ) ≤ 2.1304 by norm_num) hc
  have h0 : (0 : ℝ) ∈ Set.Icc ((fun x : ℝ => x ^ 3 - x ^ 2 - x - 3) 2.1303)
      ((fun x : ℝ => x ^ 3 - x ^ 2 - x - 3) 2.1304) := by
    constructor <;> norm_num
  obtain ⟨x, ⟨hx1, hx2⟩, hx⟩ := h h0
  exact ⟨x, hx1, hx2, hx⟩

/-- The Perron root of the token morphism, 2.13039... -/
noncomputable def lam : ℝ := Classical.choose lam_exists

lemma lam_spec : 2.1303 ≤ lam ∧ lam ≤ 2.1304 ∧ lam ^ 3 - lam ^ 2 - lam - 3 = 0 :=
  Classical.choose_spec lam_exists

/-- The limiting number of letters 0 per letter 1. -/
noncomputable def cc : ℝ := (lam ^ 2 + 1) / 2

lemma cc_bounds : 2.76908 ≤ cc ∧ cc ≤ 2.76931 := by
  obtain ⟨h1, h2, -⟩ := lam_spec
  unfold cc
  constructor <;> nlinarith

/-- The coefficients of the quadratic form. -/
noncomputable def pp : ℝ := lam - 1

/-- The squared modulus of the two complex eigenvalues. -/
noncomputable def qq : ℝ := lam ^ 2 - lam - 1

lemma pq_bounds : 1.1303 ≤ pp ∧ pp ≤ 1.1304 ∧ 1.4077 ≤ qq ∧ qq ≤ 1.4084 := by
  obtain ⟨h1, h2, -⟩ := lam_spec
  unfold pp qq
  refine ⟨by linarith, by linarith, by nlinarith, by nlinarith⟩

/-! ### Deviation of token lists -/

/-- For a list of tokens, the number of letters 0 minus c times the number of letters 1. -/
noncomputable def g (s : List ℕ) : ℝ := (s.sum : ℝ) - cc * (s.length : ℝ)

lemma g_append (u v : List ℕ) : g (u ++ v) = g u + g v := by
  simp only [g, List.sum_append, List.length_append]
  push_cast
  ring

lemma g_single (k : ℕ) : g [k] = k - cc := by
  simp [g]

lemma counts (s : List ℕ) (hs : Valid s) :
    s.sum = s.count 1 + 2 * s.count 2 + 3 * s.count 3 + 4 * s.count 4 ∧
      s.length = s.count 1 + s.count 2 + s.count 3 + s.count 4 := by
  induction s with
  | nil => simp
  | cons k s ih =>
    obtain ⟨⟨hk1, hk4⟩, hs'⟩ := valid_cons hs
    obtain ⟨h1, h2⟩ := ih hs'
    interval_cases k <;> simp [List.count_cons] <;> omega

lemma tau_counts (s : List ℕ) (hs : Valid s) :
    (tau s).count 1 = s.count 2 + s.count 4 ∧ (tau s).count 2 = s.count 3 ∧
      (tau s).count 3 = s.count 1 + s.count 4 ∧
      (tau s).count 4 = s.count 2 + s.count 3 + s.count 4 := by
  induction s with
  | nil => simp [tau]
  | cons k s ih =>
    obtain ⟨⟨hk1, hk4⟩, hs'⟩ := valid_cons hs
    obtain ⟨h1, h2, h3, h4⟩ := ih hs'
    rw [tau_cons, List.count_append, List.count_append, List.count_append, List.count_append]
    interval_cases k <;> simp [tauT, List.count_cons] <;> omega

lemma g_counts (s : List ℕ) (hs : Valid s) :
    g s = (1 - cc) * (s.count 1 : ℝ) + (2 - cc) * (s.count 2 : ℝ) + (3 - cc) * (s.count 3 : ℝ) +
      (4 - cc) * (s.count 4 : ℝ) := by
  obtain ⟨h1, h2⟩ := counts s hs
  unfold g
  rw [h1, h2]
  push_cast
  ring

/-- After one step the deviation follows the recurrence of the two complex eigenvalues. -/
lemma g_rec (s : List ℕ) (hs : Valid s) :
    g (tau (tau (tau s))) = -pp * g (tau (tau s)) - qq * g (tau s) := by
  obtain ⟨-, -, hp⟩ := lam_spec
  have hv1 := tau_valid s
  have hv2 := tau_valid (tau s)
  obtain ⟨a1, a2, a3, a4⟩ := tau_counts s hs
  obtain ⟨b1, b2, b3, b4⟩ := tau_counts (tau s) hv1
  obtain ⟨d1, d2, d3, d4⟩ := tau_counts (tau (tau s)) hv2
  rw [g_counts _ (tau_valid _), g_counts _ hv2, g_counts _ hv1, d1, d2, d3, d4, b1, b2, b3, b4,
    a1, a2, a3, a4]
  unfold cc pp qq
  push_cast
  linear_combination ((s.count 1 : ℝ) * (-1 - lam / 2) + (s.count 2 : ℝ) * (-2 - lam) +
    (s.count 3 : ℝ) * (-5 / 2 - lam) + (s.count 4 : ℝ) * (-3 - 3 * lam / 2)) * hp

/-! ### The quadratic form -/

/-- u x j: the deviation of tau^(j+1)(x). -/
noncomputable def u (x j : ℕ) : ℝ := g (tau^[j + 1] [x])

/-- The quadratic form along the deviations. -/
noncomputable def E (x j : ℕ) : ℝ := u x (j + 1) ^ 2 + pp * u x (j + 1) * u x j + qq * u x j ^ 2

lemma u_rec (x j : ℕ) (hx : 1 ≤ x ∧ x ≤ 4) :
    u x (j + 2) = -pp * u x (j + 1) - qq * u x j := by
  have hv : Valid (tau^[j] [x]) := tauIter_valid j _ (valid_single hx)
  have e3 : tau^[j + 2 + 1] [x] = tau (tau (tau (tau^[j] [x]))) := by
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
      Function.iterate_succ_apply']
  have e2 : tau^[j + 1 + 1] [x] = tau (tau (tau^[j] [x])) := by
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
  have e1 : tau^[j + 1] [x] = tau (tau^[j] [x]) := Function.iterate_succ_apply' _ _ _
  unfold u
  rw [e3, e2, e1, g_rec _ hv]

lemma E_succ (x j : ℕ) (hx : 1 ≤ x ∧ x ≤ 4) : E x (j + 1) = qq * E x j := by
  unfold E
  rw [show j + 1 + 1 = j + 2 from rfl, u_rec x j hx]
  ring

/-- The form is positive definite: it bounds the square of its second argument. -/
lemma E_ge (x j : ℕ) : 1.088 * u x j ^ 2 ≤ E x j := by
  obtain ⟨hp1, hp2, hq1, hq2⟩ := pq_bounds
  unfold E
  have h : u x (j + 1) ^ 2 + pp * u x (j + 1) * u x j + qq * u x j ^ 2 =
      (u x (j + 1) + pp / 2 * u x j) ^ 2 + (qq - pp ^ 2 / 4) * u x j ^ 2 := by ring
  rw [h]
  have h2 : 1.088 ≤ qq - pp ^ 2 / 4 := by nlinarith
  have h3 : 0 ≤ u x j ^ 2 := sq_nonneg _
  nlinarith [sq_nonneg (u x (j + 1) + pp / 2 * u x j)]

lemma E_nonneg (x j : ℕ) : 0 ≤ E x j := by
  have := E_ge x j
  have h3 : 0 ≤ u x j ^ 2 := sq_nonneg _
  linarith

lemma E_zero (x : ℕ) (hx : 1 ≤ x ∧ x ≤ 4) : E x 0 ≤ 1.66 := by
  obtain ⟨hc1, hc2⟩ := cc_bounds
  obtain ⟨hp1, hp2, hq1, hq2⟩ := pq_bounds
  obtain ⟨h1, h4⟩ := hx
  have hab : |u x 0| ≤ 0.54 ∧ |u x 1| ≤ 0.85 := by
    unfold u
    have e10 : g [3] = 3 - cc := by simp [g]
    have e11 : g [4, 1] = 5 - 2 * cc := by simp [g] <;> ring
    have e20 : g [4, 2] = 6 - 2 * cc := by simp [g] <;> ring
    have e21 : g [4, 3, 1, 3] = 11 - 4 * cc := by simp [g] <;> ring
    have e30 : g [4, 3, 1, 4, 1] = 13 - 5 * cc := by simp [g] <;> ring
    have e31 : g [4, 3, 1, 4, 2, 3] = 17 - 6 * cc := by simp [g] <;> ring
    have e40 : g [4, 3, 1, 3] = 11 - 4 * cc := e21
    have e41 : g [4, 3, 1, 4, 2, 3] = 17 - 6 * cc := e31
    have e00 : g [6] = 6 - cc := by simp [g]
    interval_cases x
    · rw [show tau^[0 + 1] [1] = [3] from rfl, show tau^[1 + 1] [1] = [4, 2] from rfl, e10, e20,
        abs_le, abs_le]
      constructor <;> constructor <;> linarith
    · rw [show tau^[0 + 1] [2] = [4, 1] from rfl, show tau^[1 + 1] [2] = [4, 3, 1, 3] from rfl,
        e11, e21, abs_le, abs_le]
      constructor <;> constructor <;> linarith
    · rw [show tau^[0 + 1] [3] = [4, 2] from rfl, show tau^[1 + 1] [3] = [4, 3, 1, 4, 1] from rfl,
        e20, e30, abs_le, abs_le]
      constructor <;> constructor <;> linarith
    · rw [show tau^[0 + 1] [4] = [4, 3, 1] from rfl,
        show tau^[1 + 1] [4] = [4, 3, 1, 4, 2, 3] from rfl, abs_le, abs_le]
      have e4a : g [4, 3, 1] = 8 - 3 * cc := by simp [g] <;> ring
      rw [e4a, e31]
      constructor <;> constructor <;> linarith
  obtain ⟨ha, hb⟩ := hab
  unfold E
  have hsq0 : u x 0 ^ 2 ≤ 0.54 ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) ha 2
  have hsq1 : u x (0 + 1) ^ 2 ≤ 0.85 ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hb 2
  have hprod : pp * u x (0 + 1) * u x 0 ≤ 1.1304 * (0.85 * 0.54) := by
    have h1' : |pp * u x (0 + 1) * u x 0| ≤ 1.1304 * (0.85 * 0.54) := by
      rw [abs_mul, abs_mul, abs_of_pos (by linarith : (0 : ℝ) < pp)]
      have := mul_le_mul hb ha (abs_nonneg _) (by norm_num)
      nlinarith [abs_nonneg (u x (0 + 1)), abs_nonneg (u x 0)]
    exact le_trans (le_abs_self _) h1'
  have hqt : qq * u x 0 ^ 2 ≤ 1.4084 * 0.54 ^ 2 := by
    have := sq_nonneg (u x 0)
    nlinarith
  norm_num at hsq0 hsq1 hprod hqt ⊢
  linarith

lemma E_le (x j : ℕ) (hx : 1 ≤ x ∧ x ≤ 4) : E x j ≤ 1.66 * 1.69 ^ j := by
  obtain ⟨hp1, hp2, hq1, hq2⟩ := pq_bounds
  induction j with
  | zero => simpa using E_zero x hx
  | succ j ih =>
    rw [E_succ x j hx, pow_succ]
    have h0 := E_nonneg x j
    have hp : 0 ≤ (1.69 : ℝ) ^ j := by positivity
    nlinarith

lemma u_bound (x j : ℕ) (hx : 1 ≤ x ∧ x ≤ 4) : |u x j| ≤ 1.25 * 1.3 ^ j := by
  apply abs_le_of_sq_le_sq _ (by positivity)
  have h1 := E_ge x j
  have h2 := E_le x j hx
  have e : (1.25 * (1.3 : ℝ) ^ j) ^ 2 = 1.5625 * 1.69 ^ j := by
    rw [mul_pow, ← pow_mul, mul_comm j 2, pow_mul]
    norm_num
  rw [e]
  have hp : 0 ≤ (1.69 : ℝ) ^ j := by positivity
  nlinarith

/-- The deviation of tau^J(x) grows by at most 1.3 per level. -/
lemma g_growth (J x : ℕ) (hx : 1 ≤ x ∧ x ≤ 4) : |g (tau^[J] [x])| ≤ 1.8 * 1.3 ^ J := by
  obtain ⟨hc1, hc2⟩ := cc_bounds
  rcases J with _ | J
  · simp only [Function.iterate_zero, id, g_single, pow_zero, mul_one]
    obtain ⟨h1, h4⟩ := hx
    have : (x : ℝ) ≤ 4 := by exact_mod_cast h4
    have h1' : (1 : ℝ) ≤ x := by exact_mod_cast h1
    rw [abs_le]
    constructor <;> linarith
  · have h := u_bound x J hx
    unfold u at h
    have hp : 0 ≤ (1.3 : ℝ) ^ J := by positivity
    rw [pow_succ]
    nlinarith

/-! ### Prefixes of token lists -/

lemma tauIter_morph (j : ℕ) : ∀ u v, tau^[j] (u ++ v) = tau^[j] u ++ tau^[j] v :=
  tauIter_append j

/-- Splitting a prefix of the image of a token list along its tokens. -/
lemma pref_split (T' : List ℕ → List ℕ) (hT : ∀ u v, T' (u ++ v) = T' u ++ T' v) (b : ℝ)
    (hb0 : 0 ≤ b)
    (hb : ∀ y, 1 ≤ y ∧ y ≤ 4 → ∀ i ≤ (T' [y]).length, |g ((T' [y]).take i)| ≤ b) :
    ∀ ys : List ℕ, Valid ys → ∀ i ≤ (T' ys).length,
      ∃ q ≤ ys.length, |g ((T' ys).take i) - g (T' (ys.take q))| ≤ b := by
  have hnil : T' [] = [] := by
    have h := hT [] []
    simp only [List.append_nil] at h
    have hl := congrArg List.length h
    rw [List.length_append] at hl
    exact List.eq_nil_of_length_eq_zero (by omega)
  intro ys
  induction ys with
  | nil =>
    intro _ i hi
    rw [hnil] at hi ⊢
    simp at hi
    subst hi
    exact ⟨0, le_rfl, by simp [hnil, g, hb0]⟩
  | cons y ys ih =>
    intro hv i hi
    obtain ⟨hy, hv'⟩ := valid_cons hv
    have e : T' (y :: ys) = T' [y] ++ T' ys := by rw [← hT]; rfl
    rw [e] at hi ⊢
    rw [List.length_append] at hi
    rcases le_or_gt i (T' [y]).length with h | h
    · refine ⟨0, by omega, ?_⟩
      rw [List.take_append_of_le_length h, List.take_zero, hnil]
      simpa [g] using hb y hy i h
    · obtain ⟨q, hq, hq'⟩ := ih hv' (i - (T' [y]).length) (by omega)
      refine ⟨q + 1, by simp; omega, ?_⟩
      rw [List.take_append, List.take_of_length_le h.le, g_append,
        show (y :: ys).take (q + 1) = [y] ++ ys.take q from rfl, hT, g_append]
      have : g (T' [y]) + g ((T' ys).take (i - (T' [y]).length)) -
          (g (T' [y]) + g (T' (ys.take q))) =
          g ((T' ys).take (i - (T' [y]).length)) - g (T' (ys.take q)) := by ring
      rw [this]
      exact hq'

lemma g_list (J : ℕ) : ∀ v : List ℕ, Valid v →
    |g (tau^[J] v)| ≤ v.length * (1.8 * 1.3 ^ J) := by
  intro v
  induction v with
  | nil =>
    intro _
    rw [tauIter_nil]
    simp [g]
  | cons y v ih =>
    intro hv
    obtain ⟨hy, hv'⟩ := valid_cons hv
    rw [show y :: v = [y] ++ v from rfl, tauIter_append, g_append, List.length_append]
    have a1 := g_growth J y hy
    have a2 := ih hv'
    have a3 := abs_add_le (g (tau^[J] [y])) (g (tau^[J] v))
    push_cast
    simp only [List.length_singleton, Nat.cast_one]
    linarith

/-- |g| over the prefixes of tau^J(x). -/
lemma prefix_bound (J : ℕ) : ∀ x, 1 ≤ x ∧ x ≤ 4 → ∀ i ≤ (tau^[J] [x]).length,
    |g ((tau^[J] [x]).take i)| ≤ 18 * 1.3 ^ J := by
  obtain ⟨hc1, hc2⟩ := cc_bounds
  induction J with
  | zero =>
    intro x hx i hi
    obtain ⟨h1, h4⟩ := hx
    simp only [Function.iterate_zero, id, List.length_cons, List.length_nil] at hi ⊢
    interval_cases i
    · simp [g]
    · simp only [List.take_succ_cons, List.take_zero, g_single]
      have : (x : ℝ) ≤ 4 := by exact_mod_cast h4
      have h1' : (1 : ℝ) ≤ x := by exact_mod_cast h1
      rw [abs_le]
      constructor <;> norm_num <;> linarith
  | succ J ih =>
    intro x hx i hi
    have hp : 0 ≤ (1.3 : ℝ) ^ J := by positivity
    have e : tau^[J + 1] [x] = tau^[J] (tauT x) := by
      rw [Function.iterate_succ_apply, tau_single]
    rw [e] at hi ⊢
    obtain ⟨q, hq, hq'⟩ := pref_split (tau^[J]) (tauIter_morph J) _ (by positivity) ih (tauT x)
      (tauT_valid x) i hi
    have hlen : (tauT x).length ≤ 3 := by
      rcases x with _ | _ | _ | _ | x <;> simp [tauT]
    have hvq : Valid ((tauT x).take q) := by
      intro y hy
      exact tauT_valid x y (List.mem_of_mem_take hy)
    have hfirst : |g (tau^[J] ((tauT x).take q))| ≤ 3 * (1.8 * 1.3 ^ J) := by
      have h := g_list J _ hvq
      have hl : (((tauT x).take q).length : ℝ) ≤ 3 := by
        have : ((tauT x).take q).length ≤ 3 := by rw [List.length_take]; omega
        exact_mod_cast this
      have hpos : 0 ≤ 1.8 * (1.3 : ℝ) ^ J := by positivity
      nlinarith
    have htri : |g ((tau^[J] (tauT x)).take i)| ≤
        |g (tau^[J] ((tauT x).take q))| + 18 * 1.3 ^ J := by
      have := abs_sub_abs_le_abs_sub (g ((tau^[J] (tauT x)).take i))
        (g (tau^[J] ((tauT x).take q)))
      linarith
    rw [pow_succ]
    linarith

lemma g_T (J : ℕ) : |g (T J)| ≤ 6 * (1.3 ^ J - 1) := by
  induction J with
  | zero => simp [T, g]
  | succ J ih =>
    rw [T_succ, g_append]
    have h := g_growth J 1 (by norm_num)
    have := abs_add_le (g (T J)) (g (tau^[J] [1]))
    rw [pow_succ]
    linarith

/-- |g| over the prefixes of T J. -/
lemma T_prefix_bound (J : ℕ) : ∀ i ≤ (T J).length, |g ((T J).take i)| ≤ 24 * 1.3 ^ J := by
  induction J with
  | zero =>
    intro i hi
    simp [T] at hi
    subst hi
    simp [T, g]
  | succ J ih =>
    intro i hi
    have hp : (1 : ℝ) ≤ 1.3 ^ J := one_le_pow₀ (by norm_num)
    rw [T_succ] at hi ⊢
    rw [List.length_append] at hi
    rcases le_or_gt i (T J).length with h | h
    · rw [List.take_append_of_le_length h]
      have := ih i h
      rw [pow_succ]
      nlinarith
    · rw [List.take_append, List.take_of_length_le h.le, g_append]
      have h1 := g_T J
      have h2 := prefix_bound J 1 (by norm_num) (i - (T J).length) (by omega)
      have := abs_add_le (g (T J)) (g ((tau^[J] [1]).take (i - (T J).length)))
      rw [pow_succ]
      nlinarith

/-! ### Letters -/

/-- For a word, the number of letters 0 minus c times the number of letters 1. -/
noncomputable def gL (L : List ℕ) : ℝ := (L.count 0 : ℝ) - cc * (L.count 1 : ℝ)

lemma gL_append (u v : List ℕ) : gL (u ++ v) = gL u + gL v := by
  simp only [gL, List.count_append]
  push_cast
  ring

lemma gL_tok (k : ℕ) : gL (tok k) = g [k] := by
  simp [gL, g, tok, List.count_replicate, List.count_cons]

lemma gL_tok_take (k : ℕ) (hk : k ≤ 4) (r : ℕ) : |gL ((tok k).take r)| ≤ 4 := by
  obtain ⟨hc1, hc2⟩ := cc_bounds
  rcases r with _ | r
  · simp [gL]
  · obtain ⟨m, hm, e⟩ : ∃ m, m ≤ 4 ∧ (tok k).take (r + 1) = 1 :: List.replicate m 0 :=
      ⟨min r k, by omega, by simp [tok, List.take_replicate]⟩
    have hg : gL (1 :: List.replicate m 0) = m - cc := by
      simp [gL, List.count_replicate, List.count_cons]
    rw [e, hg, abs_le]
    have h2 : (m : ℝ) ≤ 4 := by exact_mod_cast hm
    have h0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    constructor <;> linarith

lemma flat_split : ∀ S : List ℕ, Valid S → ∀ t ≤ (flat S).length,
    ∃ i ≤ S.length, |gL ((flat S).take t) - g (S.take i)| ≤ 4 := by
  intro S
  induction S with
  | nil =>
    intro _ t ht
    simp [flat] at ht
    subst ht
    exact ⟨0, le_rfl, by simp [gL, g]⟩
  | cons k S ih =>
    intro hv t ht
    obtain ⟨hk, hv'⟩ := valid_cons hv
    rw [flat_cons] at ht ⊢
    rw [List.length_append] at ht
    rcases le_or_gt t (tok k).length with h | h
    · refine ⟨0, by omega, ?_⟩
      rw [List.take_append_of_le_length h]
      simpa [g] using gL_tok_take k hk.2 t
    · obtain ⟨i, hi, hi'⟩ := ih hv' (t - (tok k).length) (by omega)
      refine ⟨i + 1, by simp; omega, ?_⟩
      rw [List.take_append, List.take_of_length_le h.le, gL_append, gL_tok,
        show (k :: S).take (i + 1) = [k] ++ S.take i from rfl, g_append]
      have : g [k] + gL ((flat S).take (t - (tok k).length)) - (g [k] + g (S.take i)) =
          gL ((flat S).take (t - (tok k).length)) - g (S.take i) := by ring
      rw [this]
      exact hi'

/-- Over the prefixes of iterate J, |g| <= 24 1.3^J + 6. -/
lemma word_prefix_bound (J N : ℕ) (hN : N ≤ (iter J).length) :
    |gL ((iter J).take N)| ≤ 24 * 1.3 ^ J + 6 := by
  obtain ⟨hc1, hc2⟩ := cc_bounds
  have hp : 0 ≤ (1.3 : ℝ) ^ J := by positivity
  rw [iter_eq] at hN ⊢
  rw [List.length_append] at hN
  rcases le_or_gt N 2 with h | h
  · rw [List.take_append_of_le_length (by simpa using h)]
    interval_cases N <;> simp [gL] <;> linarith
  · rw [List.take_append, List.take_of_length_le (by simp; omega), gL_append,
      show ([0, 0] : List ℕ).length = 2 from rfl]
    have h0 : gL [0, 0] = 2 := by simp [gL] <;> norm_num
    obtain ⟨i, hi, hi'⟩ := flat_split _ (T_valid J) (N - 2) (by simp at hN; omega)
    have h1 := T_prefix_bound J i hi
    have h2 := abs_sub_abs_le_abs_sub (gL ((flat (T J)).take (N - 2))) (g ((T J).take i))
    have h3 := abs_add_le (gL [0, 0]) (gL ((flat (T J)).take (N - 2)))
    rw [h0] at h3 ⊢
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 2)] at h3
    linarith

/-! ### The length of the iterates -/

/-- The weight of a token: 1, (lam^2 - 1)/2, lam, (lam^2 + 1)/2 for the tokens 1, 2, 3, 4. -/
noncomputable def wt (k : ℕ) : ℝ :=
  if k = 1 then 1 else if k = 2 then (lam ^ 2 - 1) / 2 else if k = 3 then lam else (lam ^ 2 + 1) / 2

/-- The weight of a token list; tau multiplies it by lam. -/
noncomputable def Phi (s : List ℕ) : ℝ := (s.map wt).sum

lemma Phi_append (u v : List ℕ) : Phi (u ++ v) = Phi u + Phi v := by
  simp [Phi]

lemma Phi_tau (s : List ℕ) (hs : Valid s) : Phi (tau s) = lam * Phi s := by
  obtain ⟨-, -, hp⟩ := lam_spec
  induction s with
  | nil => simp [Phi, tau]
  | cons k s ih =>
    obtain ⟨⟨hk1, hk4⟩, hs'⟩ := valid_cons hs
    rw [tau_cons, Phi_append, ih hs', show k :: s = [k] ++ s from rfl, Phi_append, mul_add]
    congr 1
    interval_cases k <;> simp [Phi, tauT, wt] <;>
      first | ring1 | linear_combination (-1 / 2 : ℝ) * hp | linear_combination (1 / 2 : ℝ) * hp

lemma Phi_iter (J : ℕ) : Phi (tau^[J] [1]) = lam ^ J := by
  induction J with
  | zero => simp [Phi, wt]
  | succ J ih =>
    rw [Function.iterate_succ_apply', Phi_tau _ (tauIter_valid J _ (valid_single (by norm_num))),
      ih, pow_succ]
    ring

lemma length_ge_Phi (s : List ℕ) (hs : Valid s) : 1.69 * Phi s ≤ ((flat s).length : ℝ) := by
  obtain ⟨hl1, hl2, -⟩ := lam_spec
  induction s with
  | nil => simp [Phi, flat]
  | cons k s ih =>
    obtain ⟨⟨hk1, hk4⟩, hs'⟩ := valid_cons hs
    rw [flat_cons, List.length_append, show k :: s = [k] ++ s from rfl, Phi_append]
    push_cast
    have := ih hs'
    have hk' : 1.69 * Phi [k] ≤ ((tok k).length : ℝ) := by
      interval_cases k <;> simp [Phi, wt, tok] <;> norm_num <;> nlinarith
    linarith

lemma iter_length_ge (J : ℕ) : 1.69 * lam ^ J ≤ ((iter (J + 1)).length : ℝ) := by
  have h := length_ge_Phi _ (tauIter_valid J _ (valid_single (show 1 ≤ 1 ∧ 1 ≤ 4 by norm_num)))
  rw [Phi_iter] at h
  have e : (iter (J + 1)).length = 2 + (flat (T J)).length + (flat (tau^[J] [1])).length := by
    rw [iter_eq, T_succ, flat_append, List.length_append, List.length_append]
    simp
    ring
  rw [e]
  push_cast
  have : (0 : ℝ) ≤ (flat (T J)).length := Nat.cast_nonneg _
  linarith

lemma iter_length_mono {m n : ℕ} (h : m ≤ n) : (iter m).length ≤ (iter n).length :=
  (iter_prefix h).length_le

/-! ### Counting along the fixed point -/

lemma iter_letters (n : ℕ) : ∀ x ∈ iter n, x ≤ 1 := by
  intro x hx
  rw [iter_eq] at hx
  simp only [List.mem_append, flat, List.mem_flatMap, tok] at hx
  rcases hx with hx | ⟨k, -, hk⟩
  · simp at hx; omega
  · simp at hk; omega

lemma W_le (i : ℕ) : W i ≤ 1 := by
  have hi : i < (iter (i + 1)).length := by have := iter_length (i + 1); omega
  rw [W_eq (i + 1) i hi, List.getD_eq_getElem _ _ hi]
  exact iter_letters _ _ (List.getElem_mem hi)

/-- Z(N): the number of letters 0 among the first N letters of W. -/
noncomputable def Z (N : ℕ) : ℕ := Nat.count (fun i => W i = 0) N

/-- O(N): the number of letters 1 among the first N letters of W. -/
noncomputable def O (N : ℕ) : ℕ := Nat.count (fun i => W i = 1) N

lemma Z_succ (N : ℕ) : Z (N + 1) = Z N + if W N = 0 then 1 else 0 := Nat.count_succ _ _

lemma O_succ (N : ℕ) : O (N + 1) = O N + if W N = 1 then 1 else 0 := Nat.count_succ _ _

lemma counts_eq (m N : ℕ) (hN : N ≤ (iter m).length) :
    Z N = ((iter m).take N).count 0 ∧ O N = ((iter m).take N).count 1 := by
  induction N with
  | zero => simp [Z, O]
  | succ N ih =>
    have hN' : N < (iter m).length := by omega
    have hW : W N = (iter m)[N] := by rw [W_eq m N hN', List.getD_eq_getElem _ _ hN']
    obtain ⟨h1, h2⟩ := ih (by omega)
    rw [Z_succ, O_succ, h1, h2, List.take_add_one, List.getElem?_eq_getElem hN',
      List.count_append, List.count_append, hW]
    constructor <;> simp [List.count_singleton]

/-- D(N) = Z(N) - c O(N) is the deviation over the first N letters of W. -/
noncomputable def D (N : ℕ) : ℝ := (Z N : ℝ) - cc * (O N : ℝ)

lemma D_eq (m N : ℕ) (hN : N ≤ (iter m).length) : D N = gL ((iter m).take N) := by
  obtain ⟨h1, h2⟩ := counts_eq m N hN
  simp [D, gL, h1, h2]

lemma O_add_Z (N : ℕ) : O N + Z N = N := by
  induction N with
  | zero => simp [O, Z]
  | succ N ih =>
    rw [O_succ, Z_succ]
    have := W_le N
    split_ifs <;> omega

lemma pow_bound (J : ℕ) (hJ : 11 ≤ J) : 197 * 1.3 ^ J + 38 < lam ^ J := by
  obtain ⟨hl1, hl2, -⟩ := lam_spec
  induction J, hJ using Nat.le_induction with
  | base =>
    have : (2.1303 : ℝ) ^ 11 ≤ lam ^ 11 := pow_le_pow_left₀ (by norm_num) hl1 11
    norm_num at this ⊢
    linarith
  | succ J hJ ih =>
    rw [pow_succ, pow_succ]
    have hp : 0 ≤ lam ^ J := by positivity
    nlinarith

lemma iter11_length : (iter 11).length = 6664 := by decide +kernel

lemma level_real (J : ℕ) (L N : ℝ) (hL : 1.69 * lam ^ (J - 1) ≤ L) (hLN : L < N)
    (hJ : 1 ≤ J) : 0.7932 * lam ^ J < N := by
  obtain ⟨hl1, hl2, -⟩ := lam_spec
  have hp : 0 ≤ lam ^ (J - 1) := by positivity
  have e : lam ^ J = lam ^ (J - 1) * lam := by
    rw [← pow_succ]
    congr 1
    omega
  rw [e]
  nlinarith

/-- For N > 6664 there is a level J >= 11 with 0.7932 lam^J < N and |D(N)| <= 31.2 1.3^J + 6. -/
lemma level (N : ℕ) (hN : 6664 < N) :
    ∃ J, 11 ≤ J ∧ 0.7932 * lam ^ J < (N : ℝ) ∧ |D N| ≤ 31.2 * 1.3 ^ J + 6 := by
  have hex : ∃ J, N ≤ (iter (J + 1)).length := ⟨N, by have := iter_length (N + 1); omega⟩
  classical
  have hJN : N ≤ (iter (Nat.find hex + 1)).length := Nat.find_spec hex
  have h11 := iter11_length
  have hJ11 : 11 ≤ Nat.find hex := by
    by_contra h
    have := iter_length_mono (show Nat.find hex + 1 ≤ 11 by omega)
    omega
  have hmin : (iter (Nat.find hex)).length < N := by
    have := Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega)
    rw [show Nat.find hex - 1 + 1 = Nat.find hex by omega] at this
    omega
  have hlen := iter_length_ge (Nat.find hex - 1)
  rw [show Nat.find hex - 1 + 1 = Nat.find hex by omega] at hlen
  refine ⟨Nat.find hex, hJ11, ?_, ?_⟩
  · exact level_real _ _ _ hlen (by exact_mod_cast hmin) (by omega)
  · rw [D_eq (Nat.find hex + 1) N hJN]
    have h := word_prefix_bound _ N hJN
    have e : (24 : ℝ) * 1.3 ^ (Nat.find hex + 1) + 6 = 31.2 * 1.3 ^ Nat.find hex + 6 := by
      rw [pow_succ]
      ring
    linarith

/-- Over every prefix of W longer than 6664 letters, |D| < N / 5. -/
lemma D_small (N : ℕ) (hN : 6664 < N) : |D N| < (N : ℝ) / 5 := by
  obtain ⟨J, hJ, hNr, hD⟩ := level N hN
  have hp := pow_bound J hJ
  have hq : 0 ≤ (1.3 : ℝ) ^ J := by positivity
  linarith

/-- |D(N)|^2 <= 200000 N for every N >= 1. -/
lemma D_sq (N : ℕ) (hN : 1 ≤ N) : D N ^ 2 ≤ 200000 * N := by
  obtain ⟨hl1, hl2, -⟩ := lam_spec
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  rcases le_or_gt N 6664 with h | h
  · have h11 := iter11_length
    have hb : |gL ((iter 11).take N)| ≤ 24 * 1.3 ^ 11 + 6 := word_prefix_bound 11 N (by omega)
    rw [D_eq 11 N (by omega)]
    have h1 : |gL ((iter 11).take N)| ≤ 437 := by
      have : (24 : ℝ) * 1.3 ^ 11 + 6 ≤ 437 := by norm_num
      exact le_trans hb this
    have h2 : gL ((iter 11).take N) ^ 2 ≤ 437 ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) h1 2
    clear hb h1 h11
    generalize gL ((iter 11).take N) = x at h2 ⊢
    nlinarith
  · obtain ⟨J, hJ, hNr, hD⟩ := level N h
    have hp : 0 ≤ (1.3 : ℝ) ^ J := by positivity
    have h1 : D N ^ 2 ≤ (31.2 * 1.3 ^ J + 6) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) hD 2
    have h2 : ((1.3 : ℝ) ^ J) ^ 2 ≤ lam ^ J := by
      rw [← pow_mul, mul_comm, pow_mul]
      exact pow_le_pow_left₀ (by norm_num) (by norm_num; linarith) J
    have h3 : (1 : ℝ) ≤ 1.3 ^ J := one_le_pow₀ (by norm_num)
    have h4 : (31.2 * 1.3 ^ J + 6) ^ 2 ≤ 1384 * ((1.3 : ℝ) ^ J) ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr h3) (by positivity : (0 : ℝ) ≤ 410 * 1.3 ^ J + 36)]
    have hlp : 0 ≤ lam ^ J := by positivity
    clear hD
    linarith

/-! ### The positions of 0 -/

/-- The limit, (1 + c)/c = 1.36110... -/
noncomputable def m0 : ℝ := (1 + cc) / cc

lemma m0_bounds : 1.3611 ≤ m0 ∧ m0 ≤ 1.3612 := by
  obtain ⟨hc1, hc2⟩ := cc_bounds
  have hc : 0 < cc := by linarith
  unfold m0
  constructor
  · rw [le_div_iff₀ hc]
    linarith
  · rw [div_le_iff₀ hc]
    linarith

lemma zeros_infinite : (setOf (fun i => W i = 0)).Infinite := by
  obtain ⟨hc1, hc2⟩ := cc_bounds
  apply Set.infinite_of_not_bddAbove
  rintro ⟨B, hB⟩
  have hconst : ∀ j, Z (B + 1 + j) = Z (B + 1) := by
    intro j
    induction j with
    | zero => rfl
    | succ j ih =>
      have hno : ¬ W (B + 1 + j) = 0 := fun h => by
        have := hB h
        omega
      rw [show B + 1 + (j + 1) = B + 1 + j + 1 by ring, Z_succ, if_neg hno, ih, add_zero]
  have h := D_small (B + 1 + (4 * Z (B + 1) + 6700)) (by omega)
  have hs := O_add_Z (B + 1 + (4 * Z (B + 1) + 6700))
  rw [hconst] at hs
  unfold D at h
  rw [hconst, abs_lt] at h
  obtain ⟨h1, -⟩ := h
  have hO : (O (B + 1 + (4 * Z (B + 1) + 6700)) : ℝ) =
      ((B + 1 + (4 * Z (B + 1) + 6700) : ℕ) : ℝ) - Z (B + 1) := by
    have : (O (B + 1 + (4 * Z (B + 1) + 6700)) : ℝ) + Z (B + 1) =
        ((B + 1 + (4 * Z (B + 1) + 6700) : ℕ) : ℝ) := by exact_mod_cast hs
    linarith
  rw [hO] at h1
  generalize hz : (Z (B + 1) : ℝ) = z at h1
  have hz0 : 0 ≤ z := by rw [← hz]; exact Nat.cast_nonneg _
  have hz' : ((B + 1 + (4 * Z (B + 1) + 6700) : ℕ) : ℝ) = (B : ℝ) + 1 + (4 * z + 6700) := by
    rw [← hz]; push_cast; ring
  rw [hz'] at h1
  have hB0 : (0 : ℝ) ≤ B := Nat.cast_nonneg _
  have hP := mul_le_mul_of_nonneg_right hc1 hz0
  have hQ := mul_le_mul_of_nonneg_right hc1 hB0
  clear hconst hs hO hz hz' hB
  nlinarith [hP, hQ]

lemma a_spec (n : ℕ) (hn : 1 ≤ n) : Z (a n) = n ∧ O (a n) = a n - n := by
  have hinf := zeros_infinite
  have hZp : Z (Nat.nth (fun i => W i = 0) (n - 1)) = n - 1 :=
    Nat.count_nth_of_infinite hinf (n - 1)
  have hWp : W (Nat.nth (fun i => W i = 0) (n - 1)) = 0 := Nat.nth_mem_of_infinite hinf (n - 1)
  have hZ1 : Z (a n) = n := by
    unfold a
    rw [Z_succ, if_pos hWp, hZp]
    omega
  refine ⟨hZ1, ?_⟩
  have := O_add_Z (a n)
  omega

/-- At the n-th 0, m n - a(n) = D/c. -/
lemma a_dev (n : ℕ) (hn : 1 ≤ n) : m0 * n - a n = D (a n) / cc := by
  obtain ⟨hc1, -⟩ := cc_bounds
  have hc : cc ≠ 0 := by linarith
  obtain ⟨hZ, hO⟩ := a_spec n hn
  have hle : n ≤ a n := by have := O_add_Z (a n); omega
  unfold D m0
  rw [hZ, hO]
  push_cast [hle]
  field_simp
  ring

/-- A linear scan of a word, checking 10000 (t + 1) < 23611 Z(t + 1) at each letter 0. -/
def chk : List ℕ → ℕ → ℕ → Bool
  | [], _, _ => true
  | x :: l, t, z =>
    if x = 0 then decide (10000 * (t + 1) < 23611 * (z + 1)) && chk l (t + 1) (z + 1)
    else chk l (t + 1) z

lemma chk_spec : ∀ (L : List ℕ) (t z : ℕ), chk L t z = true →
    ∀ i < L.length, L.getD i 0 = 0 →
      10000 * (t + i + 1) < 23611 * (z + (L.take (i + 1)).count 0) := by
  intro L
  induction L with
  | nil =>
    intro t z _ i hi
    simp at hi
  | cons x l ih =>
    intro t z h i hi hx
    by_cases h0 : x = 0
    · subst h0
      have h' : 10000 * (t + 1) < 23611 * (z + 1) ∧ chk l (t + 1) (z + 1) = true := by
        simpa [chk] using h
      rcases i with _ | i
      · simpa using h'.1
      · have := ih (t + 1) (z + 1) h'.2 i (by simp at hi; omega) (by simpa using hx)
        have e : ((0 :: l).take (i + 1 + 1)).count 0 = (l.take (i + 1)).count 0 + 1 := by
          simp [List.take_succ_cons, List.count_cons]
        rw [e]
        omega
    · have h' : chk l (t + 1) z = true := by simpa [chk, h0] using h
      rcases i with _ | i
      · simp at hx
        exact absurd hx h0
      · have := ih (t + 1) z h' i (by simp at hi; omega) (by simpa using hx)
        have e : ((x :: l).take (i + 1 + 1)).count 0 = (l.take (i + 1)).count 0 := by
          simp [List.take_succ_cons, List.count_cons, h0]
        rw [e]
        omega

lemma chk_iter : chk (iter 11) 0 0 = true := by decide +kernel

lemma bound_small (n : ℕ) (hn : 1 ≤ n) (ha : a n ≤ 6664) :
    -1 < m0 - (a n : ℝ) / n ∧ m0 - (a n : ℝ) / n < 1 := by
  obtain ⟨hm1, hm2⟩ := m0_bounds
  obtain ⟨hZ, hO⟩ := a_spec n hn
  have hinf := zeros_infinite
  have hWp : W (Nat.nth (fun i => W i = 0) (n - 1)) = 0 := Nat.nth_mem_of_infinite hinf (n - 1)
  have ha' : a n = Nat.nth (fun i => W i = 0) (n - 1) + 1 := rfl
  set t := Nat.nth (fun i => W i = 0) (n - 1) with ht
  have hlen := iter11_length
  have hW : (iter 11).getD t 0 = 0 := by rw [← W_eq 11 t (by omega)]; exact hWp
  have hc := chk_spec (iter 11) 0 0 chk_iter t (by omega) hW
  have hZ' : ((iter 11).take (t + 1)).count 0 = n := by
    rw [← (counts_eq 11 (t + 1) (by omega)).1, ← ha', hZ]
  rw [hZ'] at hc
  simp only [zero_add] at hc
  have hle : n ≤ a n := by have := O_add_Z (a n); omega
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hc' : (10000 : ℝ) * (a n) < 23611 * n := by
    rw [ha']
    exact_mod_cast hc
  have hle' : (n : ℝ) ≤ a n := by exact_mod_cast hle
  have h1 : (a n : ℝ) / n < 2.3611 := by
    rw [div_lt_iff₀ hnpos]
    linarith
  have h2 : 1 ≤ (a n : ℝ) / n := by
    rw [le_div_iff₀ hnpos]
    linarith
  constructor <;> linarith

lemma bound_large (n : ℕ) (hn : 1 ≤ n) (ha : 6664 < a n) :
    -1 < m0 - (a n : ℝ) / n ∧ m0 - (a n : ℝ) / n < 1 := by
  obtain ⟨hc1, hc2⟩ := cc_bounds
  have hc : 0 < cc := by linarith
  have hD := D_small (a n) ha
  obtain ⟨hZ, hO⟩ := a_spec n hn
  have hle : n ≤ a n := by have := O_add_Z (a n); omega
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hdev := a_dev n hn
  have hDdef : D (a n) = (n : ℝ) - cc * ((a n : ℝ) - n) := by
    unfold D
    rw [hZ, hO]
    push_cast [hle]
    ring
  rw [abs_lt, hDdef] at hD
  obtain ⟨hD1, hD2⟩ := hD
  have e : m0 - (a n : ℝ) / n = (m0 * n - a n) / n := by field_simp
  rw [e, hdev, hDdef]
  have hA0 : (0 : ℝ) ≤ a n := Nat.cast_nonneg _
  have hle' : (n : ℝ) ≤ a n := by exact_mod_cast hle
  have hP : 2.76908 * (a n : ℝ) ≤ cc * a n := mul_le_mul_of_nonneg_right hc1 hA0
  have hQ1 : 2.76908 * (n : ℝ) ≤ cc * n := mul_le_mul_of_nonneg_right hc1 hnpos.le
  have hQ2 : cc * (n : ℝ) ≤ 2.76931 * n := mul_le_mul_of_nonneg_right hc2 hnpos.le
  have hE : cc * ((a n : ℝ) - n) = cc * a n - cc * n := by ring
  rw [hE] at hD1 hD2 ⊢
  constructor
  · rw [lt_div_iff₀ hnpos, lt_div_iff₀ hc]
    linarith
  · rw [div_lt_iff₀ hnpos, div_lt_iff₀ hc]
    linarith

/-- Kimberling's conjecture: a(n)/n tends to a number m = 1.36..., and -1 < m - a(n)/n < 1
for n >= 1. -/
theorem conjecture : ∃ m : ℝ, (1.36 ≤ m ∧ m < 1.37) ∧
    Tendsto (fun n : ℕ => (a n : ℝ) / n) atTop (𝓝 m) ∧
    ∀ n : ℕ, 1 ≤ n → -1 < m - (a n : ℝ) / n ∧ m - (a n : ℝ) / n < 1 := by
  obtain ⟨hm1, hm2⟩ := m0_bounds
  obtain ⟨hc1, hc2⟩ := cc_bounds
  have hc : 0 < cc := by linarith
  have hbound : ∀ n : ℕ, 1 ≤ n → -1 < m0 - (a n : ℝ) / n ∧ m0 - (a n : ℝ) / n < 1 := by
    intro n hn
    rcases le_or_gt (a n) 6664 with h | h
    · exact bound_small n hn h
    · exact bound_large n hn h
  refine ⟨m0, ⟨by linarith, by linarith⟩, ?_, hbound⟩
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hlim : Tendsto (fun n : ℕ => Real.sqrt (200000 * 3 / cc ^ 2 / n)) atTop (𝓝 0) := by
    have := (tendsto_const_div_atTop_nhds_zero_nat (200000 * 3 / cc ^ 2)).sqrt
    simpa using this
  refine squeeze_zero' (Eventually.of_forall fun n => norm_nonneg _) ?_ hlim
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  obtain ⟨hZ, hO⟩ := a_spec n hn
  have hle : n ≤ a n := by have := O_add_Z (a n); omega
  have hsq := D_sq (a n) (le_trans hn hle)
  have hb := hbound n hn
  have ha3 : (a n : ℝ) ≤ 3 * n := by
    have h1 : (a n : ℝ) / n < 2.3613 := by linarith [hb.1]
    rw [div_lt_iff₀ hnpos] at h1
    linarith
  have hdev := a_dev n hn
  rw [Real.norm_eq_abs]
  apply Real.abs_le_sqrt
  have e : (a n : ℝ) / n - m0 = -(D (a n) / cc) / n := by
    rw [← hdev]
    field_simp
    ring
  have key : ((a n : ℝ) / n - m0) ^ 2 = D (a n) ^ 2 / (cc ^ 2 * n ^ 2) := by
    rw [e]
    field_simp
  rw [key, div_le_div_iff₀ (by positivity) hnpos]
  have hD3 : D (a n) ^ 2 ≤ 200000 * (3 * n) := by
    have : (200000 : ℝ) * (a n) ≤ 200000 * (3 * n) := by linarith
    linarith
  have e2 : 200000 * 3 / cc ^ 2 * (cc ^ 2 * (n : ℝ) ^ 2) = 200000 * 3 * n ^ 2 := by
    field_simp
  rw [e2]
  nlinarith [hD3, hnpos]

end OMA.S_oeis_a288258

theorem OMA.solution : type_of% @OMA.S_oeis_a288258.main :=
  OMA.S_oeis_a288258.conjecture
