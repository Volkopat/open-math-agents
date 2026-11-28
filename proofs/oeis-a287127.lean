import OMAStatements.S_oeis_a287127

namespace OMA.S_oeis_a287127

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

/-- The rule 1 -> 110 reads its letter alone, so the pass restarts at every letter 1. -/
lemma step_cut (u : List ℕ) : ∀ w, step (u ++ 1 :: w) = step u ++ step (1 :: w) := by
  refine step_rec (P := fun u => ∀ w, step (u ++ 1 :: w) = step u ++ step (1 :: w))
    ?_ ?_ ?_ ?_ ?_ ?_ u
  · intro w
    rfl
  · intro l ih w
    show 0 :: 0 :: 1 :: step (l ++ 1 :: w) = 0 :: 0 :: 1 :: step l ++ step (1 :: w)
    rw [ih]
    rfl
  · intro l ih w
    show 1 :: 1 :: 0 :: step (l ++ 1 :: w) = 1 :: 1 :: 0 :: step l ++ step (1 :: w)
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

/-- The images of the tokens: 1 -> 1.10, 10 -> 1.100, 100 -> 1.1000.1, 1000 -> 1.1000.10. -/
def tauT : ℕ → List ℕ
  | 0 => [0, 1]
  | 1 => [0, 2]
  | 2 => [0, 3, 0]
  | _ => [0, 3, 1]

/-- The token morphism. -/
def tau (s : List ℕ) : List ℕ := s.flatMap tauT

/-- All tokens are 0, 1, 2 or 3. -/
def Valid (s : List ℕ) : Prop := ∀ k ∈ s, k ≤ 3

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
  rcases k with _ | _ | _ | k <;> simp [tauT] at hx <;> omega

lemma tau_valid (s : List ℕ) : Valid (tau s) := by
  intro x hx
  simp only [tau, List.mem_flatMap] at hx
  obtain ⟨k, -, hk⟩ := hx
  exact tauT_valid k x hk

lemma valid_cons {k : ℕ} {s : List ℕ} (h : Valid (k :: s)) : k ≤ 3 ∧ Valid s :=
  ⟨h k (by simp), fun x hx => h x (by simp [hx])⟩

lemma valid_single {x : ℕ} (hx : x ≤ 3) : Valid [x] := by
  intro y hy
  simp at hy
  omega

lemma step_append_flat (u s : List ℕ) : step (u ++ flat s) = step u ++ step (flat s) := by
  rcases s with _ | ⟨j, s⟩
  · rw [show flat [] = [] from rfl, List.append_nil, show step [] = [] from rfl,
      List.append_nil]
  · rw [flat_cons, show tok j ++ flat s = 1 :: (List.replicate j 0 ++ flat s) from rfl,
      step_cut]

lemma step_tok (k : ℕ) (hk : k ≤ 3) : step (tok k) = flat (tauT k) := by
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
  rcases k with _ | _ | _ | k <;> simp [tauT]

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
  | n + 1 => 0 :: tau (T n)

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

lemma T_succ (n : ℕ) : T (n + 1) = T n ++ tau^[n] [0] := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have h1 : T (n + 1 + 1) = 0 :: tau (T (n + 1)) := rfl
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
    have h : (iter (n + 1)).length = (iter n).length + (flat (tau^[n] [0])).length := by
      rw [iter_eq, iter_eq, T_succ, flat_append, List.length_append, List.length_append,
        List.length_append]
      ring
    have := flat_length_pos _ (tauIter_ne_nil n [0] (by simp))
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

lemma lam_exists : ∃ x : ℝ, 2.22269 ≤ x ∧ x ≤ 2.2227 ∧ x ^ 4 - 2 * x ^ 3 - 2 * x + 2 = 0 := by
  have hc : ContinuousOn (fun x : ℝ => x ^ 4 - 2 * x ^ 3 - 2 * x + 2) (Set.Icc 2.22269 2.2227) := by
    fun_prop
  have h := intermediate_value_Icc (show (2.22269 : ℝ) ≤ 2.2227 by norm_num) hc
  have h0 : (0 : ℝ) ∈ Set.Icc ((fun x : ℝ => x ^ 4 - 2 * x ^ 3 - 2 * x + 2) 2.22269)
      ((fun x : ℝ => x ^ 4 - 2 * x ^ 3 - 2 * x + 2) 2.2227) := by
    constructor <;> norm_num
  obtain ⟨x, ⟨hx1, hx2⟩, hx⟩ := h h0
  exact ⟨x, hx1, hx2, hx⟩

/-- The Perron root of the token morphism, 2.22269... -/
noncomputable def lam : ℝ := Classical.choose lam_exists

lemma lam_spec : 2.22269 ≤ lam ∧ lam ≤ 2.2227 ∧ lam ^ 4 - 2 * lam ^ 3 - 2 * lam + 2 = 0 :=
  Classical.choose_spec lam_exists

/-- The limiting number of letters 0 per letter 1, 1/(lam - 1) = 0.81786... -/
noncomputable def cc : ℝ := lam ^ 3 - lam ^ 2 - lam - 3

lemma cc_inv : (lam - 1) * cc = 1 := by
  obtain ⟨-, -, hf⟩ := lam_spec
  unfold cc
  linear_combination hf

lemma cc_bounds : 0.81786 ≤ cc ∧ cc ≤ 0.81787 := by
  obtain ⟨h1, h2, -⟩ := lam_spec
  have h := cc_inv
  constructor <;> nlinarith

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
    s.sum = s.count 1 + 2 * s.count 2 + 3 * s.count 3 ∧
      s.length = s.count 0 + s.count 1 + s.count 2 + s.count 3 := by
  induction s with
  | nil => simp
  | cons k s ih =>
    obtain ⟨hk, hs'⟩ := valid_cons hs
    obtain ⟨h1, h2⟩ := ih hs'
    interval_cases k <;> simp <;> omega

lemma tau_counts (s : List ℕ) (hs : Valid s) :
    (tau s).count 0 = s.count 0 + s.count 1 + 2 * s.count 2 + s.count 3 ∧
      (tau s).count 1 = s.count 0 + s.count 3 ∧ (tau s).count 2 = s.count 1 ∧
      (tau s).count 3 = s.count 2 + s.count 3 := by
  induction s with
  | nil => simp [tau]
  | cons k s ih =>
    obtain ⟨hk, hs'⟩ := valid_cons hs
    obtain ⟨h0, h1, h2, h3⟩ := ih hs'
    rw [tau_cons, List.count_append, List.count_append, List.count_append, List.count_append]
    interval_cases k <;> simp [tauT, List.count_cons] <;> omega

lemma g_counts (s : List ℕ) (hs : Valid s) :
    g s = (0 - cc) * (s.count 0 : ℝ) + (1 - cc) * (s.count 1 : ℝ) + (2 - cc) * (s.count 2 : ℝ) +
      (3 - cc) * (s.count 3 : ℝ) := by
  obtain ⟨h1, h2⟩ := counts s hs
  unfold g
  rw [h1, h2]
  push_cast
  ring

/-- The deviation has no component along the Perron root: it follows the cubic f(x)/(x - lam). -/
lemma g_rec (s : List ℕ) (hs : Valid s) :
    g (tau (tau (tau s))) + (lam - 2) * g (tau (tau s)) + (lam ^ 2 - 2 * lam) * g (tau s) +
      (lam ^ 3 - 2 * lam ^ 2 - 2) * g s = 0 := by
  obtain ⟨-, -, hf⟩ := lam_spec
  have v1 := tau_valid s
  have v2 := tau_valid (tau s)
  have v3 := tau_valid (tau (tau s))
  obtain ⟨a0, a1, a2, a3⟩ := tau_counts s hs
  obtain ⟨b0, b1, b2, b3⟩ := tau_counts (tau s) v1
  obtain ⟨d0, d1, d2, d3⟩ := tau_counts (tau (tau s)) v2
  rw [g_counts _ v3, g_counts _ v2, g_counts _ v1, g_counts _ hs, d0, d1, d2, d3, b0, b1, b2, b3,
    a0, a1, a2, a3]
  unfold cc
  push_cast
  linear_combination ((s.count 0 : ℝ) * (-1 - lam - lam ^ 2) +
    (s.count 1 : ℝ) * (-2 - lam - lam ^ 2) + (s.count 2 : ℝ) * (-3 - 2 * lam - lam ^ 2) +
    (s.count 3 : ℝ) * (-3 - 2 * lam - lam ^ 2)) * hf

/-- The deviation of tau^j(x). -/
noncomputable def u (x j : ℕ) : ℝ := g (tau^[j] [x])

lemma u_rec (x j : ℕ) (hx : x ≤ 3) :
    u x (j + 3) + (lam - 2) * u x (j + 2) + (lam ^ 2 - 2 * lam) * u x (j + 1) +
      (lam ^ 3 - 2 * lam ^ 2 - 2) * u x j = 0 := by
  have hv : Valid (tau^[j] [x]) := tauIter_valid j _ (valid_single hx)
  have e1 : tau^[j + 1] [x] = tau (tau^[j] [x]) := Function.iterate_succ_apply' _ _ _
  have e2 : tau^[j + 2] [x] = tau (tau (tau^[j] [x])) := by
    rw [show j + 2 = j + 1 + 1 from rfl, Function.iterate_succ_apply', e1]
  have e3 : tau^[j + 3] [x] = tau (tau (tau (tau^[j] [x]))) := by
    rw [show j + 3 = j + 2 + 1 from rfl, Function.iterate_succ_apply', e2]
  unfold u
  rw [e3, e2, e1]
  exact g_rec _ hv

lemma coeff_bounds : |lam - 2| ≤ 0.2227 ∧ |lam ^ 2 - 2 * lam| ≤ 0.495 ∧
    |lam ^ 3 - 2 * lam ^ 2 - 2| ≤ 0.9 := by
  obtain ⟨h1, h2, -⟩ := lam_spec
  have a2 := pow_le_pow_left₀ (by norm_num) h1 2
  have b2 := pow_le_pow_left₀ (by linarith) h2 2
  have a3 := pow_le_pow_left₀ (by norm_num) h1 3
  have b3 := pow_le_pow_left₀ (by linarith) h2 3
  norm_num at a2 b2 a3 b3
  refine ⟨?_, ?_, ?_⟩ <;> rw [abs_le] <;> constructor <;> nlinarith

lemma u_start (x : ℕ) (hx : x ≤ 3) :
    |u x 0| ≤ 2.19 ∧ |u x 1| ≤ 2.19 * 1.25 ∧ |u x 2| ≤ 2.19 * 1.25 ^ 2 := by
  obtain ⟨hc1, hc2⟩ := cc_bounds
  have k : ∀ s : List ℕ, ∀ z o : ℕ, s.sum = z → s.length = o → g s = z - cc * o := by
    intro s z o hz ho
    unfold g
    rw [hz, ho]
  interval_cases x
  · refine ⟨?_, ?_, ?_⟩
    · rw [show u 0 0 = g [0] from rfl, k _ 0 1 rfl rfl, abs_le]; norm_num; constructor <;> linarith
    · rw [show u 0 1 = g [0, 1] from rfl, k _ 1 2 rfl rfl, abs_le]; norm_num; constructor <;> linarith
    · rw [show u 0 2 = g [0, 1, 0, 2] from rfl, k _ 3 4 rfl rfl, abs_le]; norm_num
      constructor <;> linarith
  · refine ⟨?_, ?_, ?_⟩
    · rw [show u 1 0 = g [1] from rfl, k _ 1 1 rfl rfl, abs_le]; norm_num; constructor <;> linarith
    · rw [show u 1 1 = g [0, 2] from rfl, k _ 2 2 rfl rfl, abs_le]; norm_num; constructor <;> linarith
    · rw [show u 1 2 = g [0, 1, 0, 3, 0] from rfl, k _ 4 5 rfl rfl, abs_le]; norm_num
      constructor <;> linarith
  · refine ⟨?_, ?_, ?_⟩
    · rw [show u 2 0 = g [2] from rfl, k _ 2 1 rfl rfl, abs_le]; norm_num; constructor <;> linarith
    · rw [show u 2 1 = g [0, 3, 0] from rfl, k _ 3 3 rfl rfl, abs_le]; norm_num
      constructor <;> linarith
    · rw [show u 2 2 = g [0, 1, 0, 3, 1, 0, 1] from rfl, k _ 6 7 rfl rfl, abs_le]; norm_num
      constructor <;> linarith
  · refine ⟨?_, ?_, ?_⟩
    · rw [show u 3 0 = g [3] from rfl, k _ 3 1 rfl rfl, abs_le]; norm_num; constructor <;> linarith
    · rw [show u 3 1 = g [0, 3, 1] from rfl, k _ 4 3 rfl rfl, abs_le]; norm_num
      constructor <;> linarith
    · rw [show u 3 2 = g [0, 1, 0, 3, 1, 0, 2] from rfl, k _ 7 7 rfl rfl, abs_le]; norm_num
      constructor <;> linarith

/-- The deviation of tau^J(x) grows by at most 1.25 per level. -/
lemma u_bound (x : ℕ) (hx : x ≤ 3) (j : ℕ) : |u x j| ≤ 2.19 * 1.25 ^ j ∧
    |u x (j + 1)| ≤ 2.19 * 1.25 ^ (j + 1) ∧ |u x (j + 2)| ≤ 2.19 * 1.25 ^ (j + 2) := by
  obtain ⟨q2, q1, q0⟩ := coeff_bounds
  induction j with
  | zero => simpa using u_start x hx
  | succ j ih =>
    obtain ⟨h0, h1, h2⟩ := ih
    refine ⟨h1, h2, ?_⟩
    have hr := u_rec x j hx
    have e : u x (j + 3) = -((lam - 2) * u x (j + 2) + (lam ^ 2 - 2 * lam) * u x (j + 1) +
        (lam ^ 3 - 2 * lam ^ 2 - 2) * u x j) := by linarith
    show |u x (j + 3)| ≤ 2.19 * 1.25 ^ (j + 3)
    rw [e, abs_neg]
    have t1 := abs_add_le ((lam - 2) * u x (j + 2) + (lam ^ 2 - 2 * lam) * u x (j + 1))
      ((lam ^ 3 - 2 * lam ^ 2 - 2) * u x j)
    have t2 := abs_add_le ((lam - 2) * u x (j + 2)) ((lam ^ 2 - 2 * lam) * u x (j + 1))
    rw [abs_mul, abs_mul] at t2
    rw [abs_mul] at t1
    have p0 : (0 : ℝ) ≤ 1.25 ^ j := by positivity
    have m2 := mul_le_mul q2 h2 (abs_nonneg _) (by norm_num)
    have m1 := mul_le_mul q1 h1 (abs_nonneg _) (by norm_num)
    have m0 := mul_le_mul q0 h0 (abs_nonneg _) (by norm_num)
    have e2 : (1.25 : ℝ) ^ (j + 2) = 1.25 ^ j * 1.5625 := by rw [pow_add]; norm_num
    have e1 : (1.25 : ℝ) ^ (j + 1) = 1.25 ^ j * 1.25 := pow_succ _ _
    have e3 : (1.25 : ℝ) ^ (j + 3) = 1.25 ^ j * 1.953125 := by rw [pow_add]; norm_num
    rw [e2] at m2
    rw [e1] at m1
    rw [e3]
    nlinarith

lemma g_growth (J x : ℕ) (hx : x ≤ 3) : |g (tau^[J] [x])| ≤ 2.19 * 1.25 ^ J :=
  (u_bound x hx J).1

/-! ### Prefixes of token lists -/

lemma tauIter_morph (j : ℕ) : ∀ u v, tau^[j] (u ++ v) = tau^[j] u ++ tau^[j] v :=
  tauIter_append j

/-- Splitting a prefix of the image of a token list along its tokens. -/
lemma pref_split (T' : List ℕ → List ℕ) (hT : ∀ u v, T' (u ++ v) = T' u ++ T' v) (b : ℝ)
    (hb0 : 0 ≤ b)
    (hb : ∀ y, y ≤ 3 → ∀ i ≤ (T' [y]).length, |g ((T' [y]).take i)| ≤ b) :
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
    |g (tau^[J] v)| ≤ v.length * (2.19 * 1.25 ^ J) := by
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
lemma prefix_bound (J : ℕ) : ∀ x, x ≤ 3 → ∀ i ≤ (tau^[J] [x]).length,
    |g ((tau^[J] [x]).take i)| ≤ 26.3 * 1.25 ^ J := by
  obtain ⟨hc1, hc2⟩ := cc_bounds
  induction J with
  | zero =>
    intro x hx i hi
    simp only [Function.iterate_zero, id, List.length_cons, List.length_nil] at hi ⊢
    interval_cases i
    · norm_num [g]
    · simp only [List.take_succ_cons, List.take_zero, g_single]
      have : (x : ℝ) ≤ 3 := by exact_mod_cast hx
      have h0 : (0 : ℝ) ≤ x := Nat.cast_nonneg x
      rw [abs_le]
      constructor <;> norm_num <;> linarith
  | succ J ih =>
    intro x hx i hi
    have hp : 0 ≤ (1.25 : ℝ) ^ J := by positivity
    have e : tau^[J + 1] [x] = tau^[J] (tauT x) := by
      rw [Function.iterate_succ_apply, tau_single]
    rw [e] at hi ⊢
    obtain ⟨q, hq, hq'⟩ := pref_split (tau^[J]) (tauIter_morph J) _ (by positivity) ih (tauT x)
      (tauT_valid x) i hi
    have hlen : (tauT x).length ≤ 3 := by
      rcases x with _ | _ | _ | x <;> simp [tauT]
    have hvq : Valid ((tauT x).take q) := by
      intro y hy
      exact tauT_valid x y (List.mem_of_mem_take hy)
    have hfirst : |g (tau^[J] ((tauT x).take q))| ≤ 3 * (2.19 * 1.25 ^ J) := by
      have h := g_list J _ hvq
      have hl : (((tauT x).take q).length : ℝ) ≤ 3 := by
        have : ((tauT x).take q).length ≤ 3 := by rw [List.length_take]; omega
        exact_mod_cast this
      have hpos : 0 ≤ 2.19 * (1.25 : ℝ) ^ J := by positivity
      nlinarith
    have htri : |g ((tau^[J] (tauT x)).take i)| ≤
        |g (tau^[J] ((tauT x).take q))| + 26.3 * 1.25 ^ J := by
      have := abs_sub_abs_le_abs_sub (g ((tau^[J] (tauT x)).take i))
        (g (tau^[J] ((tauT x).take q)))
      linarith
    rw [pow_succ]
    linarith

lemma g_T (J : ℕ) : |g (T J)| ≤ 8.76 * (1.25 ^ J - 1) := by
  induction J with
  | zero => simp [T, g]
  | succ J ih =>
    rw [T_succ, g_append]
    have h := g_growth J 0 (by norm_num)
    have := abs_add_le (g (T J)) (g (tau^[J] [0]))
    rw [pow_succ]
    linarith

/-- |g| over the prefixes of T J. -/
lemma T_prefix_bound (J : ℕ) : ∀ i ≤ (T J).length, |g ((T J).take i)| ≤ 35.1 * 1.25 ^ J := by
  induction J with
  | zero =>
    intro i hi
    simp [T] at hi
    subst hi
    norm_num [T, g]
  | succ J ih =>
    intro i hi
    have hp : (1 : ℝ) ≤ 1.25 ^ J := one_le_pow₀ (by norm_num)
    rw [T_succ] at hi ⊢
    rw [List.length_append] at hi
    rcases le_or_gt i (T J).length with h | h
    · rw [List.take_append_of_le_length h]
      have := ih i h
      rw [pow_succ]
      nlinarith
    · rw [List.take_append, List.take_of_length_le h.le, g_append]
      have h1 := g_T J
      have h2 := prefix_bound J 0 (by norm_num) (i - (T J).length) (by omega)
      have := abs_add_le (g (T J)) (g ((tau^[J] [0]).take (i - (T J).length)))
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
  simp [gL, g, tok, List.count_replicate]

lemma gL_tok_take (k : ℕ) (hk : k ≤ 3) (r : ℕ) : |gL ((tok k).take r)| ≤ 3 := by
  obtain ⟨hc1, hc2⟩ := cc_bounds
  rcases r with _ | r
  · simp [gL]
  · obtain ⟨m, hm, e⟩ : ∃ m, m ≤ 3 ∧ (tok k).take (r + 1) = 1 :: List.replicate m 0 :=
      ⟨min r k, by omega, by simp [tok, List.take_replicate]⟩
    have hg : gL (1 :: List.replicate m 0) = m - cc := by
      simp [gL, List.count_replicate]
    rw [e, hg, abs_le]
    have h2 : (m : ℝ) ≤ 3 := by exact_mod_cast hm
    have h0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    constructor <;> linarith

lemma flat_split : ∀ S : List ℕ, Valid S → ∀ t ≤ (flat S).length,
    ∃ i ≤ S.length, |gL ((flat S).take t) - g (S.take i)| ≤ 3 := by
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
      simpa [g] using gL_tok_take k hk t
    · obtain ⟨i, hi, hi'⟩ := ih hv' (t - (tok k).length) (by omega)
      refine ⟨i + 1, by simp; omega, ?_⟩
      rw [List.take_append, List.take_of_length_le h.le, gL_append, gL_tok,
        show (k :: S).take (i + 1) = [k] ++ S.take i from rfl, g_append]
      have : g [k] + gL ((flat S).take (t - (tok k).length)) - (g [k] + g (S.take i)) =
          gL ((flat S).take (t - (tok k).length)) - g (S.take i) := by ring
      rw [this]
      exact hi'

/-- Over the prefixes of iterate J, |g| <= 35.1 * 1.25^J + 5. -/
lemma word_prefix_bound (J N : ℕ) (hN : N ≤ (iter J).length) :
    |gL ((iter J).take N)| ≤ 35.1 * 1.25 ^ J + 5 := by
  obtain ⟨hc1, hc2⟩ := cc_bounds
  have hp : 0 ≤ (1.25 : ℝ) ^ J := by positivity
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

/-- The weight of a token: 1, lam - 1, lam^2 - lam - 1, lam^3 - lam^2 - lam - 2. -/
noncomputable def wt (k : ℕ) : ℝ :=
  if k = 0 then 1 else if k = 1 then lam - 1 else if k = 2 then lam ^ 2 - lam - 1
  else lam ^ 3 - lam ^ 2 - lam - 2

/-- The weight of a token list; tau multiplies it by lam. -/
noncomputable def Phi (s : List ℕ) : ℝ := (s.map wt).sum

lemma Phi_append (u v : List ℕ) : Phi (u ++ v) = Phi u + Phi v := by
  simp [Phi]

lemma Phi_tau (s : List ℕ) (hs : Valid s) : Phi (tau s) = lam * Phi s := by
  obtain ⟨-, -, hf⟩ := lam_spec
  induction s with
  | nil => simp [Phi, tau]
  | cons k s ih =>
    obtain ⟨hk, hs'⟩ := valid_cons hs
    rw [tau_cons, Phi_append, ih hs', show k :: s = [k] ++ s from rfl, Phi_append, mul_add]
    congr 1
    interval_cases k <;> simp [Phi, tauT, wt] <;>
      first | ring1 | linear_combination (-1 : ℝ) * hf | linear_combination hf

lemma Phi_iter (J : ℕ) : Phi (tau^[J] [0]) = lam ^ J := by
  induction J with
  | zero => simp [Phi, wt]
  | succ J ih =>
    rw [Function.iterate_succ_apply', Phi_tau _ (tauIter_valid J _ (valid_single (by norm_num))),
      ih, pow_succ]
    ring

lemma length_ge_Phi (s : List ℕ) (hs : Valid s) : Phi s ≤ ((flat s).length : ℝ) := by
  obtain ⟨hl1, hl2, -⟩ := lam_spec
  have a2 := pow_le_pow_left₀ (by norm_num) hl1 2
  have b2 := pow_le_pow_left₀ (by linarith) hl2 2
  have a3 := pow_le_pow_left₀ (by norm_num) hl1 3
  have b3 := pow_le_pow_left₀ (by linarith) hl2 3
  norm_num at a2 b2 a3 b3
  induction s with
  | nil => simp [Phi, flat]
  | cons k s ih =>
    obtain ⟨hk, hs'⟩ := valid_cons hs
    rw [flat_cons, List.length_append, show k :: s = [k] ++ s from rfl, Phi_append]
    push_cast
    have := ih hs'
    have hk' : Phi [k] ≤ ((tok k).length : ℝ) := by
      interval_cases k <;> simp [Phi, wt, tok] <;> linarith
    linarith

lemma iter_length_ge (J : ℕ) : lam ^ J ≤ ((iter (J + 1)).length : ℝ) := by
  have h := length_ge_Phi _ (tauIter_valid J _ (valid_single (show 0 ≤ 3 by norm_num)))
  rw [Phi_iter] at h
  have e : (iter (J + 1)).length = 2 + (flat (T J)).length + (flat (tau^[J] [0])).length := by
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

lemma pow_bound (J : ℕ) (hJ : 10 ≤ J) : 293 * 1.25 ^ J + 34 < lam ^ J := by
  obtain ⟨hl1, hl2, -⟩ := lam_spec
  induction J, hJ using Nat.le_induction with
  | base =>
    have : (2.22269 : ℝ) ^ 10 ≤ lam ^ 10 := pow_le_pow_left₀ (by norm_num) hl1 10
    norm_num at this ⊢
    linarith
  | succ J hJ ih =>
    rw [pow_succ, pow_succ]
    have hp : 0 ≤ lam ^ J := by positivity
    nlinarith

lemma iter10_length : (iter 10).length = 3555 := by decide +kernel

lemma level_real (J : ℕ) (L N : ℝ) (hL : lam ^ (J - 1) ≤ L) (hLN : L < N)
    (hJ : 1 ≤ J) : 0.4499 * lam ^ J < N := by
  obtain ⟨hl1, hl2, -⟩ := lam_spec
  have hp : 0 ≤ lam ^ (J - 1) := by positivity
  have e : lam ^ J = lam ^ (J - 1) * lam := by
    rw [← pow_succ]
    congr 1
    omega
  rw [e]
  nlinarith

/-- For N > 3555 there is a level J >= 10 with 0.4499 lam^J < N and
|D(N)| <= 43.875 * 1.25^J + 5. -/
lemma level (N : ℕ) (hN : 3555 < N) :
    ∃ J, 10 ≤ J ∧ 0.4499 * lam ^ J < (N : ℝ) ∧ |D N| ≤ 43.875 * 1.25 ^ J + 5 := by
  have hex : ∃ J, N ≤ (iter (J + 1)).length := ⟨N, by have := iter_length (N + 1); omega⟩
  classical
  have hJN : N ≤ (iter (Nat.find hex + 1)).length := Nat.find_spec hex
  have h10 := iter10_length
  have hJ10 : 10 ≤ Nat.find hex := by
    by_contra h
    have := iter_length_mono (show Nat.find hex + 1 ≤ 10 by omega)
    omega
  have hmin : (iter (Nat.find hex)).length < N := by
    have := Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega)
    rw [show Nat.find hex - 1 + 1 = Nat.find hex by omega] at this
    omega
  have hlen := iter_length_ge (Nat.find hex - 1)
  rw [show Nat.find hex - 1 + 1 = Nat.find hex by omega] at hlen
  refine ⟨Nat.find hex, hJ10, ?_, ?_⟩
  · exact level_real _ _ _ hlen (by exact_mod_cast hmin) (by omega)
  · rw [D_eq (Nat.find hex + 1) N hJN]
    have h := word_prefix_bound _ N hJN
    have e : (35.1 : ℝ) * 1.25 ^ (Nat.find hex + 1) + 5 = 43.875 * 1.25 ^ Nat.find hex + 5 := by
      rw [pow_succ]
      ring
    linarith

/-- Over every prefix of W longer than 3555 letters, |D| < N / 3. -/
lemma D_small (N : ℕ) (hN : 3555 < N) : |D N| < (N : ℝ) / 3 := by
  obtain ⟨J, hJ, hNr, hD⟩ := level N hN
  have hp := pow_bound J hJ
  have hq : 0 ≤ (1.25 : ℝ) ^ J := by positivity
  linarith

/-- |D(N)|^2 <= 200000 N for every N >= 1. -/
lemma D_sq (N : ℕ) (hN : 1 ≤ N) : D N ^ 2 ≤ 200000 * N := by
  obtain ⟨hl1, hl2, -⟩ := lam_spec
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  rcases le_or_gt N 3555 with h | h
  · have h10 := iter10_length
    have hb : |gL ((iter 10).take N)| ≤ 35.1 * 1.25 ^ 10 + 5 := word_prefix_bound 10 N (by omega)
    rw [D_eq 10 N (by omega)]
    have h1 : |gL ((iter 10).take N)| ≤ 332 := by
      have : (35.1 : ℝ) * 1.25 ^ 10 + 5 ≤ 332 := by norm_num
      exact le_trans hb this
    have h2 : gL ((iter 10).take N) ^ 2 ≤ 332 ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) h1 2
    clear hb h1 h10
    generalize gL ((iter 10).take N) = x at h2 ⊢
    nlinarith
  · obtain ⟨J, hJ, hNr, hD⟩ := level N h
    have hp : 0 ≤ (1.25 : ℝ) ^ J := by positivity
    have h1 : D N ^ 2 ≤ (43.875 * 1.25 ^ J + 5) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) hD 2
    have h2 : ((1.25 : ℝ) ^ J) ^ 2 ≤ lam ^ J := by
      rw [← pow_mul, mul_comm, pow_mul]
      exact pow_le_pow_left₀ (by norm_num) (by norm_num; linarith) J
    have h3 : (1 : ℝ) ≤ 1.25 ^ J := one_le_pow₀ (by norm_num)
    have h4 : (43.875 * 1.25 ^ J + 5) ^ 2 ≤ 2400 * ((1.25 : ℝ) ^ J) ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr h3) (by positivity : (0 : ℝ) ≤ 450 * 1.25 ^ J + 30)]
    have hlp : 0 ≤ lam ^ J := by positivity
    clear hD
    nlinarith

/-! ### The positions of 1 -/

/-- The limit, 1 + c = 1.81786... -/
noncomputable def m1 : ℝ := 1 + cc

lemma m1_bounds : 1.81786 ≤ m1 ∧ m1 ≤ 1.81787 := by
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
  have h := D_small (B + 1 + (6 * O (B + 1) + 3600)) (by omega)
  have hs := O_add_Z (B + 1 + (6 * O (B + 1) + 3600))
  rw [hconst] at hs
  unfold D at h
  rw [hconst, abs_lt] at h
  obtain ⟨-, h2⟩ := h
  have hZ : (Z (B + 1 + (6 * O (B + 1) + 3600)) : ℝ) =
      ((B + 1 + (6 * O (B + 1) + 3600) : ℕ) : ℝ) - O (B + 1) := by
    have : (O (B + 1) : ℝ) + Z (B + 1 + (6 * O (B + 1) + 3600)) =
        ((B + 1 + (6 * O (B + 1) + 3600) : ℕ) : ℝ) := by exact_mod_cast hs
    linarith
  rw [hZ] at h2
  generalize ho : (O (B + 1) : ℝ) = z at h2
  have hz0 : 0 ≤ z := by rw [← ho]; exact Nat.cast_nonneg _
  have hz' : ((B + 1 + (6 * O (B + 1) + 3600) : ℕ) : ℝ) = (B : ℝ) + 1 + (6 * z + 3600) := by
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

/-- A linear scan of a word, checking 100 (t + 1) < 380 n at the n-th letter 1, with t + 1 its
position. -/
def chk : List ℕ → ℕ → ℕ → Bool
  | [], _, _ => true
  | x :: l, t, o =>
    if x = 1 then decide (100 * (t + 1) < 380 * (o + 1)) && chk l (t + 1) (o + 1)
    else chk l (t + 1) o

lemma chk_spec : ∀ (L : List ℕ) (t o : ℕ), chk L t o = true →
    ∀ i < L.length, L.getD i 0 = 1 →
      100 * (t + i + 1) < 380 * (o + (L.take (i + 1)).count 1) := by
  intro L
  induction L with
  | nil =>
    intro t o _ i hi
    simp at hi
  | cons x l ih =>
    intro t o h i hi hx
    by_cases h1 : x = 1
    · subst h1
      have h' : 100 * (t + 1) < 380 * (o + 1) ∧ chk l (t + 1) (o + 1) = true := by
        simpa [chk] using h
      rcases i with _ | i
      · simpa using h'.1
      · have := ih (t + 1) (o + 1) h'.2 i (by simp at hi; omega) (by simpa using hx)
        have e : ((1 :: l).take (i + 1 + 1)).count 1 = (l.take (i + 1)).count 1 + 1 := by
          simp [List.take_succ_cons]
        rw [e]
        omega
    · have h' : chk l (t + 1) o = true := by simpa [chk, h1] using h
      rcases i with _ | i
      · simp at hx
        exact absurd hx h1
      · have := ih (t + 1) o h' i (by simp at hi; omega) (by simpa using hx)
        have e : ((x :: l).take (i + 1 + 1)).count 1 = (l.take (i + 1)).count 1 := by
          simp [List.take_succ_cons, h1]
        rw [e]
        omega

lemma chk_iter : chk (iter 10) 0 0 = true := by decide +kernel

lemma bound_small (n : ℕ) (hn : 1 ≤ n) (ha : a n ≤ 3555) :
    -2 < m1 - (a n : ℝ) / n ∧ m1 - (a n : ℝ) / n < 1 := by
  obtain ⟨hm1, hm2⟩ := m1_bounds
  obtain ⟨hO, hZ⟩ := a_spec n hn
  have hinf := ones_infinite
  have hWp : W (Nat.nth (fun i => W i = 1) (n - 1)) = 1 := Nat.nth_mem_of_infinite hinf (n - 1)
  have ha' : a n = Nat.nth (fun i => W i = 1) (n - 1) + 1 := rfl
  set t := Nat.nth (fun i => W i = 1) (n - 1) with ht
  have hlen := iter10_length
  have hW : (iter 10).getD t 0 = 1 := by rw [← W_eq 10 t (by omega)]; exact hWp
  have hc := chk_spec (iter 10) 0 0 chk_iter t (by omega) hW
  have hO' : ((iter 10).take (t + 1)).count 1 = n := by
    rw [← (counts_eq 10 (t + 1) (by omega)).2, ← ha', hO]
  rw [hO'] at hc
  simp only [zero_add] at hc
  have hle : n ≤ a n := by have := O_add_Z (a n); omega
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hc' : (100 : ℝ) * (a n) < 380 * n := by
    rw [ha']
    exact_mod_cast hc
  have hle' : (n : ℝ) ≤ a n := by exact_mod_cast hle
  have h1 : (a n : ℝ) / n < 3.8 := by
    rw [div_lt_iff₀ hnpos]
    linarith
  have h2 : 1 ≤ (a n : ℝ) / n := by
    rw [le_div_iff₀ hnpos]
    linarith
  constructor <;> linarith

lemma bound_large (n : ℕ) (hn : 1 ≤ n) (ha : 3555 < a n) :
    -2 < m1 - (a n : ℝ) / n ∧ m1 - (a n : ℝ) / n < 1 := by
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
  have hQ1 : 0.81786 * (n : ℝ) ≤ cc * n := mul_le_mul_of_nonneg_right hc1 hnpos.le
  have hQ2 : cc * (n : ℝ) ≤ 0.81787 * n := mul_le_mul_of_nonneg_right hc2 hnpos.le
  constructor
  · rw [lt_div_iff₀ hnpos]
    linarith
  · rw [div_lt_iff₀ hnpos]
    linarith

/-- Kimberling's conjecture: a(n)/n tends to a number m = 1.81..., and -2 < m - a(n)/n < 1
for n >= 1. -/
theorem conjecture : ∃ m : ℝ, (1.81 ≤ m ∧ m < 1.82) ∧
    Tendsto (fun n : ℕ => (a n : ℝ) / n) atTop (𝓝 m) ∧
    ∀ n : ℕ, 1 ≤ n → -2 < m - (a n : ℝ) / n ∧ m - (a n : ℝ) / n < 1 := by
  obtain ⟨hm1, hm2⟩ := m1_bounds
  have hbound : ∀ n : ℕ, 1 ≤ n → -2 < m1 - (a n : ℝ) / n ∧ m1 - (a n : ℝ) / n < 1 := by
    intro n hn
    rcases le_or_gt (a n) 3555 with h | h
    · exact bound_small n hn h
    · exact bound_large n hn h
  refine ⟨m1, ⟨by linarith, by linarith⟩, ?_, hbound⟩
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hlim : Tendsto (fun n : ℕ => Real.sqrt (200000 * 4 / n)) atTop (𝓝 0) := by
    have := (tendsto_const_div_atTop_nhds_zero_nat (200000 * 4)).sqrt
    simpa using this
  refine squeeze_zero' (Eventually.of_forall fun n => norm_nonneg _) ?_ hlim
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  obtain ⟨hO, hZ⟩ := a_spec n hn
  have hle : n ≤ a n := by have := O_add_Z (a n); omega
  have hsq := D_sq (a n) (le_trans hn hle)
  have hb := hbound n hn
  have ha4 : (a n : ℝ) ≤ 4 * n := by
    have h1 : (a n : ℝ) / n < 3.8179 := by linarith [hb.1]
    rw [div_lt_iff₀ hnpos] at h1
    linarith
  have hdev := a_dev n hn
  rw [Real.norm_eq_abs]
  apply Real.abs_le_sqrt
  have e : (a n : ℝ) / n - m1 = D (a n) / n := by
    have : (a n : ℝ) = m1 * n + D (a n) := by linarith
    rw [this]
    field_simp
    ring
  have key : ((a n : ℝ) / n - m1) ^ 2 = D (a n) ^ 2 / (n : ℝ) ^ 2 := by
    rw [e, div_pow]
  rw [key, div_le_div_iff₀ (by positivity) hnpos]
  have hD3 : D (a n) ^ 2 ≤ 200000 * (4 * n) := by
    have : (200000 : ℝ) * (a n) ≤ 200000 * (4 * n) := by linarith
    linarith
  nlinarith [hD3, hnpos]

end OMA.S_oeis_a287127

theorem OMA.solution : type_of% @OMA.S_oeis_a287127.main :=
  OMA.S_oeis_a287127.conjecture
