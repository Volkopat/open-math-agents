import OMAStatements.S_oeis_a287183

namespace OMA.S_oeis_a287183

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

lemma step_zero_cons (t : List ℕ) : ∃ r, step (0 :: t) = 0 :: r := by
  rcases t with _ | ⟨y, t⟩
  · exact ⟨[], rfl⟩
  · rcases y with _ | _ | y
    · exact ⟨0 :: 1 :: 0 :: step t, rfl⟩
    · exact ⟨step (1 :: t), rfl⟩
    · exact ⟨step ((y + 2) :: t), rfl⟩

/-- A pass maps a prefix of a word to a prefix of its image: a lone final 0 is copied, and
00 -> 0010 begins with 0. -/
lemma step_mono (u : List ℕ) : ∀ t, step u <+: step (u ++ t) := by
  refine step_rec (P := fun u => ∀ t, step u <+: step (u ++ t)) ?_ ?_ ?_ ?_ ?_ ?_ u
  · intro t
    exact List.nil_prefix
  · intro l ih t
    obtain ⟨r, hr⟩ := ih t
    exact ⟨r, by
      show 0 :: 0 :: 1 :: 0 :: (step l ++ r) = 0 :: 0 :: 1 :: 0 :: step (l ++ t)
      rw [hr]⟩
  · intro l ih t
    obtain ⟨r, hr⟩ := ih t
    exact ⟨r, by
      show 0 :: 0 :: (step l ++ r) = 0 :: 0 :: step (l ++ t)
      rw [hr]⟩
  · intro t
    obtain ⟨r, hr⟩ := step_zero_cons t
    exact ⟨r, by
      show 0 :: r = step (0 :: t)
      rw [hr]⟩
  · intro y l ih t
    obtain ⟨r, hr⟩ := ih t
    exact ⟨r, by
      show 0 :: (step ((y + 1) :: l) ++ r) = 0 :: step ((y + 1) :: l ++ t)
      rw [hr]⟩
  · intro x l ih t
    obtain ⟨r, hr⟩ := ih t
    exact ⟨r, by
      show (x + 2) :: (step l ++ r) = (x + 2) :: step (l ++ t)
      rw [hr]⟩

/-- A pass does not shorten a word. -/
lemma step_length (u : List ℕ) : u.length ≤ (step u).length := by
  refine step_rec (P := fun u => u.length ≤ (step u).length) ?_ ?_ ?_ ?_ ?_ ?_ u
  · exact le_rfl
  · intro l ih
    show l.length + 2 ≤ (step l).length + 4
    omega
  · intro l ih
    show l.length + 1 ≤ (step l).length + 2
    omega
  · exact le_rfl
  · intro y l ih
    show ((y + 1) :: l).length + 1 ≤ (step ((y + 1) :: l)).length + 1
    omega
  · intro x l ih
    show l.length + 1 ≤ (step l).length + 1
    omega

/-- A word is closed when the pass over it followed by any word is the pass over it followed by
the pass over that word. -/
def Closed (u : List ℕ) : Prop := ∀ y, step (u ++ y) = step u ++ step y

lemma closed_append {u v : List ℕ} (hu : Closed u) (hv : Closed v) : Closed (u ++ v) := by
  intro y
  rw [List.append_assoc, hu (v ++ y), hv y, hu v, List.append_assoc]

/-! ### Tokens -/

/-- The tokens T0 = 00, T1 = 100, T2 = 0100. -/
def tok : ℕ → List ℕ
  | 0 => [0, 0]
  | 1 => [1, 0, 0]
  | _ => [0, 1, 0, 0]

/-- All tokens are 0, 1 or 2. -/
def Valid (s : List ℕ) : Prop := ∀ k ∈ s, k ≤ 2

lemma tok_closed (k : ℕ) (hk : k ≤ 2) : Closed (tok k) := by
  interval_cases k <;> exact fun _ => rfl

/-- The word of a list of tokens. -/
def flat (s : List ℕ) : List ℕ := s.flatMap tok

/-- The shifted images of the tokens: the pass over a token followed by 0 is 0 followed by the
word of T0 -> T2, T1 -> T0 T2, T2 -> T0 T0 T1. -/
def tauT : ℕ → List ℕ
  | 0 => [2]
  | 1 => [0, 2]
  | _ => [0, 0, 1]

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
  rcases k with _ | _ | k <;> simp [tauT] at hx <;> omega

lemma tau_valid (s : List ℕ) : Valid (tau s) := by
  intro x hx
  simp only [tau, List.mem_flatMap] at hx
  obtain ⟨k, -, hk⟩ := hx
  exact tauT_valid k x hk

lemma valid_cons {k : ℕ} {s : List ℕ} (h : Valid (k :: s)) : k ≤ 2 ∧ Valid s :=
  ⟨h k (by simp), fun x hx => h x (by simp [hx])⟩

lemma valid_single {x : ℕ} (hx : x ≤ 2) : Valid [x] := by
  intro y hy
  simp at hy
  omega

lemma valid_append {u v : List ℕ} (hu : Valid u) (hv : Valid v) : Valid (u ++ v) := by
  intro y hy
  rcases List.mem_append.mp hy with h | h
  · exact hu y h
  · exact hv y h

/-- The pass over a token, followed by 0, is 0 followed by the word of its shifted image. -/
lemma step_tok (k : ℕ) (hk : k ≤ 2) : step (tok k) ++ [0] = [0] ++ flat (tauT k) := by
  interval_cases k <;> rfl

lemma step_flat (s : List ℕ) (hs : Valid s) : step (flat s) ++ [0] = [0] ++ flat (tau s) := by
  induction s with
  | nil => rfl
  | cons k s ih =>
    obtain ⟨hk, hs'⟩ := valid_cons hs
    rw [flat_cons, tok_closed k hk, List.append_assoc, ih hs', ← List.append_assoc, step_tok k hk,
      tau_cons, flat_append, List.append_assoc]

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

lemma tau_length_ge (s : List ℕ) : s.length ≤ (tau s).length := by
  induction s with
  | nil => simp [tau]
  | cons k s ih =>
    rw [tau_cons, List.length_append, List.length_cons]
    have : 1 ≤ (tauT k).length := by rcases k with _ | _ | k <;> simp [tauT]
    omega

lemma tauIter_length_ge (n : ℕ) (s : List ℕ) : s.length ≤ (tau^[n] s).length := by
  induction n generalizing s with
  | zero => exact le_rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    exact (tau_length_ge s).trans (ih _)

lemma flat_length_ge (s : List ℕ) (hs : Valid s) : s.length ≤ (flat s).length := by
  induction s with
  | nil => simp [flat]
  | cons k s ih =>
    obtain ⟨hk, hs'⟩ := valid_cons hs
    rw [flat_cons, List.length_append, List.length_cons]
    have := ih hs'
    interval_cases k <;> simp [tok] <;> omega

lemma flat_letters (s : List ℕ) : ∀ x ∈ flat s, x ≤ 1 := by
  intro x hx
  simp only [flat, List.mem_flatMap] at hx
  obtain ⟨k, -, hk⟩ := hx
  rcases k with _ | _ | k <;> simp [tok] at hk <;> omega

/-! ### The iterates -/

/-- R k: the tokens T1 tau(T1) ... tau^(k-1)(T1). -/
def R : ℕ → List ℕ
  | 0 => []
  | k + 1 => 1 :: tau (R k)

lemma R_valid (k : ℕ) : Valid (R k) := by
  induction k with
  | zero => intro y hy; simp [R] at hy
  | succ k ih =>
    intro y hy
    simp only [R, List.mem_cons] at hy
    rcases hy with rfl | hy
    · norm_num
    · exact tau_valid _ y hy

lemma R_succ' (k : ℕ) : R (k + 1) = R k ++ tau^[k] [1] := by
  induction k with
  | zero => rfl
  | succ k ih =>
    calc R (k + 1 + 1) = 1 :: tau (R k ++ tau^[k] [1]) := by rw [← ih]; rfl
      _ = (1 :: tau (R k)) ++ tau^[k + 1] [1] := by
        rw [tau_append, Function.iterate_succ_apply' tau k, List.cons_append]
      _ = R (k + 1) ++ tau^[k + 1] [1] := rfl

/-- V k: the word of the tokens T0 R k. -/
def V (k : ℕ) : List ℕ := flat (0 :: R k)

lemma V_succ (k : ℕ) : step (V k) ++ [0] = V (k + 1) := by
  have hv : Valid (0 :: R k) := by
    intro y hy
    simp only [List.mem_cons] at hy
    rcases hy with rfl | hy
    · norm_num
    · exact R_valid k y hy
  unfold V
  rw [step_flat _ hv, tau_cons]
  rfl

lemma iter_prefix_V (k : ℕ) : iter k <+: V k := by
  induction k with
  | zero => exact List.prefix_refl _
  | succ k ih =>
    obtain ⟨t, ht⟩ := ih
    show step (iter k) <+: V (k + 1)
    rw [← V_succ, ← ht]
    exact (step_mono _ t).trans (List.prefix_append _ _)

lemma V_prefix_succ (k : ℕ) : V k <+: V (k + 1) := by
  unfold V
  rw [R_succ', show (0 :: (R k ++ tau^[k] [1])) = (0 :: R k) ++ tau^[k] [1] from rfl, flat_append]
  exact List.prefix_append _ _

lemma V_prefix {k k' : ℕ} (h : k ≤ k') : V k <+: V k' := by
  induction k', h using Nat.le_induction with
  | base => exact List.prefix_refl _
  | succ k' _ ih => exact ih.trans (V_prefix_succ k')

lemma V_length (k : ℕ) : k + 2 ≤ (V k).length := by
  induction k with
  | zero => decide
  | succ k ih =>
    unfold V at ih ⊢
    rw [R_succ', show (0 :: (R k ++ tau^[k] [1])) = (0 :: R k) ++ tau^[k] [1] from rfl, flat_append,
      List.length_append]
    have h2 := flat_length_ge (tau^[k] [1]) (tauIter_valid _ _ (valid_single (by norm_num)))
    have h3 := tauIter_length_ge k [1]
    simp only [List.length_cons, List.length_nil] at h3
    omega

lemma iter_head (n : ℕ) : ∃ l, iter n = 0 :: 0 :: l := by
  induction n with
  | zero => exact ⟨[], rfl⟩
  | succ n ih =>
    obtain ⟨l, hl⟩ := ih
    exact ⟨1 :: 0 :: step l, by rw [show iter (n + 1) = step (iter n) from rfl, hl]; rfl⟩

lemma iter_length (n : ℕ) : n + 2 ≤ (iter n).length := by
  induction n with
  | zero => decide
  | succ n ih =>
    obtain ⟨l, hl⟩ := iter_head n
    rw [show iter (n + 1) = step (iter n) from rfl, hl]
    rw [hl] at ih
    have := step_length l
    show n + 1 + 2 ≤ (step l).length + 4
    simp only [List.length_cons] at ih
    omega

/-- Each iterate is a prefix of the next. -/
lemma iter_prefix (n : ℕ) : iter n <+: iter (n + 1) := by
  induction n with
  | zero => exact ⟨[1, 0], rfl⟩
  | succ n ih =>
    obtain ⟨t, ht⟩ := ih
    show step (iter n) <+: step (iter (n + 1))
    rw [← ht]
    exact step_mono _ t

lemma getD_prefix {l₁ l₂ : List ℕ} (h : l₁ <+: l₂) {i : ℕ} (hi : i < l₁.length) :
    l₁.getD i 0 = l₂.getD i 0 := by
  obtain ⟨s, rfl⟩ := h
  rw [List.getD_append _ _ _ _ hi]

lemma W_eq (k i : ℕ) (hi : i < (V k).length) : W i = (V k).getD i 0 := by
  have hl : i < (iter (i + 1)).length := by have := iter_length (i + 1); omega
  have hp := iter_prefix_V (i + 1)
  have hl' : i < (V (i + 1)).length := lt_of_lt_of_le hl hp.length_le
  unfold W
  rw [getD_prefix hp hl]
  rcases le_total (i + 1) k with h | h
  · exact getD_prefix (V_prefix h) hl'
  · exact (getD_prefix (V_prefix h) hi).symm

/-! ### The roots -/

lemma lam_exists : ∃ x : ℝ, 1.879385 ≤ x ∧ x ≤ 1.879386 ∧ x ^ 3 - 3 * x - 1 = 0 := by
  have hc : ContinuousOn (fun x : ℝ => x ^ 3 - 3 * x - 1) (Set.Icc 1.879385 1.879386) := by
    fun_prop
  have h := intermediate_value_Icc (show (1.879385 : ℝ) ≤ 1.879386 by norm_num) hc
  have h0 : (0 : ℝ) ∈ Set.Icc ((fun x : ℝ => x ^ 3 - 3 * x - 1) 1.879385)
      ((fun x : ℝ => x ^ 3 - 3 * x - 1) 1.879386) := by
    constructor <;> norm_num
  obtain ⟨x, ⟨hx1, hx2⟩, hx⟩ := h h0
  exact ⟨x, hx1, hx2, hx⟩

/-- The Perron root, 1.87938..., the growth rate of the iterates. -/
noncomputable def lam : ℝ := Classical.choose lam_exists

lemma lam_spec : 1.879385 ≤ lam ∧ lam ≤ 1.879386 ∧ lam ^ 3 - 3 * lam - 1 = 0 :=
  Classical.choose_spec lam_exists

lemma nu_exists : ∃ x : ℝ, -0.3473 ≤ x ∧ x ≤ -0.34729 ∧ x ^ 2 + lam * x + (lam ^ 2 - 3) = 0 := by
  obtain ⟨hl1, hl2, -⟩ := lam_spec
  have hc : ContinuousOn (fun x : ℝ => x ^ 2 + lam * x + (lam ^ 2 - 3)) (Set.Icc (-0.3473) (-0.34729)) := by
    fun_prop
  have h := intermediate_value_Icc (show (-0.3473 : ℝ) ≤ -0.34729 by norm_num) hc
  have h0 : (0 : ℝ) ∈ Set.Icc ((fun x : ℝ => x ^ 2 + lam * x + (lam ^ 2 - 3)) (-0.3473))
      ((fun x : ℝ => x ^ 2 + lam * x + (lam ^ 2 - 3)) (-0.34729)) := by
    constructor <;> simp only <;> nlinarith
  obtain ⟨x, ⟨hx1, hx2⟩, hx⟩ := h h0
  exact ⟨x, hx1, hx2, hx⟩

/-- The root -0.34729... of x^2 + lam x + lam^2 - 3. -/
noncomputable def nu : ℝ := Classical.choose nu_exists

lemma nu_spec : -0.3473 ≤ nu ∧ nu ≤ -0.34729 ∧ nu ^ 2 + lam * nu + (lam ^ 2 - 3) = 0 :=
  Classical.choose_spec nu_exists

/-- The other root, -lam - nu = -1.53208... -/
noncomputable def mu : ℝ := -lam - nu

lemma mu_nu : mu * nu = lam ^ 2 - 3 := by
  obtain ⟨-, -, hn⟩ := nu_spec
  unfold mu
  linear_combination (-1 : ℝ) * hn

lemma mu_bounds : -1.5321 ≤ mu ∧ mu ≤ -1.53208 := by
  obtain ⟨hl1, hl2, -⟩ := lam_spec
  obtain ⟨hn1, hn2, -⟩ := nu_spec
  unfold mu
  constructor <;> linarith

/-- The limiting number of letters 0 per letter 1, lam^2 + lam - 1 = 4.41147... -/
noncomputable def cc : ℝ := lam ^ 2 + lam - 1

lemma cc_bounds : 4.41147 ≤ cc ∧ cc ≤ 4.41148 := by
  obtain ⟨h1, h2, -⟩ := lam_spec
  unfold cc
  constructor <;> nlinarith

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

lemma g_tok (k : ℕ) (hk : k ≤ 2) :
    g (tau (tau [k])) + lam * g (tau [k]) + (lam ^ 2 - 3) * g [k] = 0 := by
  obtain ⟨-, -, hf⟩ := lam_spec
  interval_cases k
  · rw [g_eq _ 6 1 (by decide) (by decide), g_eq _ 3 1 (by decide) (by decide),
      g_eq _ 2 0 (by decide) (by decide)]
    unfold cc
    push_cast
    linear_combination (-1 : ℝ) * hf
  · rw [g_eq _ 9 2 (by decide) (by decide), g_eq _ 5 1 (by decide) (by decide),
      g_eq _ 2 1 (by decide) (by decide)]
    unfold cc
    push_cast
    linear_combination (-2 - lam) * hf
  · rw [g_eq _ 11 3 (by decide) (by decide), g_eq _ 6 1 (by decide) (by decide),
      g_eq _ 3 1 (by decide) (by decide)]
    unfold cc
    push_cast
    linear_combination (-2 - lam) * hf

/-- The deviation has no component along the Perron root: it follows (x - mu)(x - nu). -/
lemma g_rec (s : List ℕ) (hs : Valid s) :
    g (tau (tau s)) + lam * g (tau s) + (lam ^ 2 - 3) * g s = 0 := by
  induction s with
  | nil => simp [g, gL, flat, tau]
  | cons k s ih =>
    obtain ⟨hk, hs'⟩ := valid_cons hs
    rw [show k :: s = [k] ++ s from rfl, tau_append, tau_append, g_append, g_append, g_append]
    linarith [g_tok k hk, ih hs']

/-! ### The two filters -/

/-- u x j: the deviation of tau^j(x). -/
noncomputable def u (x j : ℕ) : ℝ := g (tau^[j] [x])

lemma u_rec (x j : ℕ) (hx : x ≤ 2) :
    u x (j + 2) = -lam * u x (j + 1) - (lam ^ 2 - 3) * u x j := by
  have hv : Valid (tau^[j] [x]) := tauIter_valid j _ (valid_single hx)
  have e2 : tau^[j + 2] [x] = tau (tau (tau^[j] [x])) := by
    rw [show j + 2 = j + 1 + 1 from rfl, Function.iterate_succ_apply',
      Function.iterate_succ_apply']
  have e1 : tau^[j + 1] [x] = tau (tau^[j] [x]) := Function.iterate_succ_apply' _ _ _
  have h := g_rec _ hv
  unfold u
  rw [e2, e1]
  linarith

/-- v x j = u x (j + 1) - nu u x j removes the nu-mode. -/
noncomputable def v (x j : ℕ) : ℝ := u x (j + 1) - nu * u x j

/-- w x j = u x (j + 1) - mu u x j removes the mu-mode. -/
noncomputable def w (x j : ℕ) : ℝ := u x (j + 1) - mu * u x j

lemma v_succ (x j : ℕ) (hx : x ≤ 2) : v x (j + 1) = mu * v x j := by
  have hm : mu = -lam - nu := rfl
  have hmn := mu_nu
  unfold v
  rw [show j + 1 + 1 = j + 2 from rfl, u_rec x j hx]
  linear_combination (-(u x (j + 1))) * hm + (u x j) * hmn

lemma w_succ (x j : ℕ) (hx : x ≤ 2) : w x (j + 1) = nu * w x j := by
  have hm : mu = -lam - nu := rfl
  have hmn := mu_nu
  unfold w
  rw [show j + 1 + 1 = j + 2 from rfl, u_rec x j hx]
  linear_combination (-(u x (j + 1))) * hm + (u x j) * hmn

lemma v_eq (x j : ℕ) (hx : x ≤ 2) : v x j = mu ^ j * v x 0 := by
  induction j with
  | zero => simp
  | succ j ih => rw [v_succ x j hx, ih, pow_succ]; ring

lemma w_eq (x j : ℕ) (hx : x ≤ 2) : w x j = nu ^ j * w x 0 := by
  induction j with
  | zero => simp
  | succ j ih => rw [w_succ x j hx, ih, pow_succ]; ring

/-- The coefficient of the mu-mode in the bound for token x. -/
noncomputable def ua : ℕ → ℝ
  | 0 => 0.6055
  | 1 => 0.2105
  | _ => 0.9275

/-- The coefficient of the nu-mode in the bound for token x. -/
noncomputable def ub : ℕ → ℝ
  | 0 => 1.3955
  | 1 => 2.6222
  | _ => 0.485

lemma vw_zero (x : ℕ) (hx : x ≤ 2) : |v x 0| ≤ ua x * 1.1847 ∧ |w x 0| ≤ ub x * 1.1847 := by
  obtain ⟨hc1, hc2⟩ := cc_bounds
  obtain ⟨hn1, hn2, -⟩ := nu_spec
  obtain ⟨hm1, hm2⟩ := mu_bounds
  have hP1 : -0.3473 * 4.41148 ≤ nu * cc := by nlinarith
  have hP2 : nu * cc ≤ -0.34729 * 4.41147 := by nlinarith
  have hQ1 : -1.5321 * 4.41148 ≤ mu * cc := by nlinarith
  have hQ2 : mu * cc ≤ -1.53208 * 4.41147 := by nlinarith
  have k : ∀ s : List ℕ, ∀ z o : ℕ, (flat s).count 0 = z → (flat s).count 1 = o →
      g s = z - cc * o := fun s z o hz ho => g_eq s z o hz ho
  have e : ∀ y, v y 0 = u y 1 - nu * u y 0 ∧ w y 0 = u y 1 - mu * u y 0 := fun y => ⟨rfl, rfl⟩
  interval_cases x
  · rw [(e 0).1, (e 0).2, show u 0 1 = g [2] from rfl, show u 0 0 = g [0] from rfl,
      k [2] 3 1 (by decide) (by decide), k [0] 2 0 (by decide) (by decide)]
    simp only [ua, ub]
    push_cast
    constructor <;> rw [abs_le] <;> constructor <;> nlinarith
  · rw [(e 1).1, (e 1).2, show u 1 1 = g [0, 2] from rfl, show u 1 0 = g [1] from rfl,
      k [0, 2] 5 1 (by decide) (by decide), k [1] 2 1 (by decide) (by decide)]
    simp only [ua, ub]
    push_cast
    constructor <;> rw [abs_le] <;> constructor <;> nlinarith
  · rw [(e 2).1, (e 2).2, show u 2 1 = g [0, 0, 1] from rfl, show u 2 0 = g [2] from rfl,
      k [0, 0, 1] 6 1 (by decide) (by decide), k [2] 3 1 (by decide) (by decide)]
    simp only [ua, ub]
    push_cast
    constructor <;> rw [abs_le] <;> constructor <;> nlinarith

lemma ua_nonneg (x : ℕ) : 0 ≤ ua x := by
  rcases x with _ | _ | x <;> simp [ua] <;> norm_num

lemma ub_nonneg (x : ℕ) : 0 ≤ ub x := by
  rcases x with _ | _ | x <;> simp [ub] <;> norm_num

/-- The bound for the deviation of tau^j(x). -/
noncomputable def UB (x j : ℕ) : ℝ := ua x * 1.5321 ^ j + ub x * 0.3473 ^ j

lemma UB_nonneg (x j : ℕ) : 0 ≤ UB x j := by
  have := ua_nonneg x
  have := ub_nonneg x
  unfold UB
  positivity

lemma u_bound (x j : ℕ) (hx : x ≤ 2) : |u x j| ≤ UB x j := by
  obtain ⟨hl1, hl2, -⟩ := lam_spec
  obtain ⟨hn1, hn2, -⟩ := nu_spec
  obtain ⟨hm1, hm2⟩ := mu_bounds
  obtain ⟨hv0, hw0⟩ := vw_zero x hx
  have hd : 1.1847 ≤ nu - mu := by unfold mu; linarith
  have hu : u x j = (w x j - v x j) / (nu - mu) := by
    have h : w x j - v x j = (nu - mu) * u x j := by unfold v w; ring
    rw [h]
    field_simp
  rw [hu, v_eq x j hx, w_eq x j hx, abs_div, abs_of_pos (by linarith : (0 : ℝ) < nu - mu),
    div_le_iff₀ (by linarith)]
  have h1 : |nu ^ j * w x 0 - mu ^ j * v x 0| ≤ |nu| ^ j * |w x 0| + |mu| ^ j * |v x 0| := by
    calc |nu ^ j * w x 0 - mu ^ j * v x 0| ≤ |nu ^ j * w x 0| + |mu ^ j * v x 0| := abs_sub _ _
      _ = |nu| ^ j * |w x 0| + |mu| ^ j * |v x 0| := by
        rw [abs_mul, abs_mul, abs_pow, abs_pow]
  have hmu : |mu| ≤ 1.5321 := by rw [abs_le]; constructor <;> linarith
  have hnu : |nu| ≤ 0.3473 := by rw [abs_le]; constructor <;> linarith
  have h2 : |mu| ^ j ≤ 1.5321 ^ j := pow_le_pow_left₀ (abs_nonneg _) hmu j
  have h3 : |nu| ^ j ≤ 0.3473 ^ j := pow_le_pow_left₀ (abs_nonneg _) hnu j
  have hn0 : 0 ≤ |nu| ^ j := pow_nonneg (abs_nonneg _) j
  have hm0 : 0 ≤ |mu| ^ j := pow_nonneg (abs_nonneg _) j
  have ha := ua_nonneg x
  have hb := ub_nonneg x
  have h4 : |nu| ^ j * |w x 0| ≤ 0.3473 ^ j * (ub x * 1.1847) :=
    mul_le_mul h3 hw0 (abs_nonneg _) (by positivity)
  have h5 : |mu| ^ j * |v x 0| ≤ 1.5321 ^ j * (ua x * 1.1847) :=
    mul_le_mul h2 hv0 (abs_nonneg _) (by positivity)
  have h6 : (ua x * 1.5321 ^ j + ub x * 0.3473 ^ j) * 1.1847 ≤
      (ua x * 1.5321 ^ j + ub x * 0.3473 ^ j) * (nu - mu) :=
    mul_le_mul_of_nonneg_left hd (by positivity)
  unfold UB
  nlinarith

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

/-- The bound for |g| over the prefixes of tau^J(x). -/
noncomputable def PB (J : ℕ) : ℝ := 2.89 * 1.5321 ^ J + 7.83 - 8.3 * 0.3473 ^ J

lemma PB_ge (J : ℕ) : 2.42 ≤ PB J := by
  have h1 : (1 : ℝ) ≤ 1.5321 ^ J := one_le_pow₀ (by norm_num)
  have h2 : (0.3473 : ℝ) ^ J ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  unfold PB
  linarith

lemma list_bound (J : ℕ) (hP : ∀ x, x ≤ 2 → ∀ i, |g ((tau^[J] [x]).take i)| ≤ PB J) :
    ∀ r : List ℕ, Valid r → ∀ i, |g ((tau^[J] r).take i)| ≤ (r.map (fun k => UB k J)).sum + PB J := by
  intro r
  induction r with
  | nil =>
    intro _ i
    rw [tauIter_nil]
    have := PB_ge J
    simp [g, gL, flat]
    linarith
  | cons k r ih =>
    intro hv i
    obtain ⟨hk, hv'⟩ := valid_cons hv
    have e : tau^[J] (k :: r) = tau^[J] [k] ++ tau^[J] r := by
      rw [show k :: r = [k] ++ r from rfl, tauIter_append]
    rw [e]
    have h := take_append_le _ _ _ _ (hP k hk) (ih hv') i
    have hu := u_bound k J hk
    have hs : 0 ≤ (r.map (fun k => UB k J)).sum :=
      List.sum_nonneg (fun y hy => by
        obtain ⟨z, -, rfl⟩ := List.mem_map.mp hy
        exact UB_nonneg z J)
    have hU := UB_nonneg k J
    refine le_trans h (max_le ?_ ?_)
    · simp only [List.map_cons, List.sum_cons]
      linarith
    · simp only [List.map_cons, List.sum_cons]
      have : |g (tau^[J] [k])| = |u k J| := rfl
      linarith

lemma gtok_bound (x : ℕ) (hx : x ≤ 2) : |g [x]| ≤ 2.42 := by
  obtain ⟨hc1, hc2⟩ := cc_bounds
  interval_cases x
  · rw [g_eq [0] 2 0 (by decide) (by decide), abs_le]; constructor <;> norm_num
  · rw [g_eq [1] 2 1 (by decide) (by decide), abs_le]; constructor <;> norm_num <;> linarith
  · rw [g_eq [2] 3 1 (by decide) (by decide), abs_le]; constructor <;> norm_num <;> linarith

/-- |g| over the prefixes of tau^J(x). -/
lemma prefix_bound (J : ℕ) : ∀ x, x ≤ 2 → ∀ i, |g ((tau^[J] [x]).take i)| ≤ PB J := by
  induction J with
  | zero =>
    intro x hx i
    simp only [Function.iterate_zero, id]
    have h0 : PB 0 = 2.42 := by norm_num [PB]
    rw [h0]
    rcases i with _ | i
    · norm_num [g, flat, gL]
    · rw [show [x].take (i + 1) = [x] by simp]
      exact gtok_bound x hx
  | succ J ih =>
    intro x hx i
    rw [Function.iterate_succ_apply, tau_single]
    have h := list_bound J ih (tauT x) (tauT_valid x) i
    refine le_trans h ?_
    have hp : 0 ≤ (1.5321 : ℝ) ^ J := by positivity
    have hq : 0 ≤ (0.3473 : ℝ) ^ J := by positivity
    unfold PB
    rw [pow_succ (1.5321 : ℝ) J, pow_succ (0.3473 : ℝ) J]
    interval_cases x <;> simp [tauT, UB, ua, ub] <;> nlinarith

/-- The deviation of R J, the sum of the deviations of the blocks tau^j(T1), j < J. -/
lemma R_dev (J : ℕ) : |g (R J)| ≤ 0.396 * 1.5321 ^ J + 3.63 - 4.02 * 0.3473 ^ J := by
  induction J with
  | zero => norm_num [R, g, gL, flat]
  | succ J ih =>
    rw [R_succ', g_append]
    have hu := u_bound 1 J (by norm_num)
    have hp : 0 ≤ (1.5321 : ℝ) ^ J := by positivity
    have hq : 0 ≤ (0.3473 : ℝ) ^ J := by positivity
    have h := abs_add_le (g (R J)) (g (tau^[J] [1]))
    have e : g (tau^[J] [1]) = u 1 J := rfl
    rw [e] at h ⊢
    simp only [UB, ua, ub] at hu
    rw [pow_succ (1.5321 : ℝ) J, pow_succ (0.3473 : ℝ) J]
    nlinarith

/-! ### Letters -/

lemma gL_tok_take (k : ℕ) (hk : k ≤ 2) (r : ℕ) : |gL ((tok k).take r)| ≤ 4.42 := by
  obtain ⟨hc1, hc2⟩ := cc_bounds
  have hz : ((tok k).take r).count 0 ≤ 3 := by
    calc ((tok k).take r).count 0 ≤ (tok k).count 0 := List.Sublist.count_le _ (List.take_sublist _ _)
      _ ≤ 3 := by interval_cases k <;> decide
  have ho : ((tok k).take r).count 1 ≤ 1 := by
    calc ((tok k).take r).count 1 ≤ (tok k).count 1 := List.Sublist.count_le _ (List.take_sublist _ _)
      _ ≤ 1 := by interval_cases k <;> decide
  have hz' : (((tok k).take r).count 0 : ℝ) ≤ 3 := by exact_mod_cast hz
  have ho' : (((tok k).take r).count 1 : ℝ) ≤ 1 := by exact_mod_cast ho
  have hz0 : (0 : ℝ) ≤ ((tok k).take r).count 0 := Nat.cast_nonneg _
  have ho0 : (0 : ℝ) ≤ ((tok k).take r).count 1 := Nat.cast_nonneg _
  unfold gL
  rw [abs_le]
  constructor <;> nlinarith

lemma flat_split : ∀ S : List ℕ, Valid S → ∀ t,
    ∃ i, |gL ((flat S).take t) - g (S.take i)| ≤ 4.42 := by
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

/-! ### The length of the words V k -/

/-- The Perron weight of a token: 1, lam^2 - 2, lam. -/
noncomputable def wt : ℕ → ℝ
  | 0 => 1
  | 1 => lam ^ 2 - 2
  | _ => lam

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
      first | ring1 | linear_combination (-1 : ℝ) * hf

lemma Phi_iter (J : ℕ) : Phi (tau^[J] [1]) = (lam ^ 2 - 2) * lam ^ J := by
  induction J with
  | zero => simp [Phi, wt]
  | succ J ih =>
    rw [Function.iterate_succ_apply', Phi_tau _ (tauIter_valid J _ (valid_single (by norm_num))),
      ih, pow_succ]
    ring

lemma length_ge_Phi (s : List ℕ) (hs : Valid s) : 1.95 * Phi s ≤ ((flat s).length : ℝ) := by
  obtain ⟨hl1, hl2, -⟩ := lam_spec
  induction s with
  | nil => simp [Phi, flat]
  | cons k s ih =>
    obtain ⟨hk, hs'⟩ := valid_cons hs
    rw [flat_cons, List.length_append, show k :: s = [k] ++ s from rfl, Phi_append]
    push_cast
    have := ih hs'
    have hk' : 1.95 * Phi [k] ≤ ((tok k).length : ℝ) := by
      interval_cases k <;> simp [Phi, wt, tok] <;> nlinarith
    linarith

lemma V_length_ge (J : ℕ) : 1.95 * ((lam ^ 2 - 2) * lam ^ J) ≤ ((V (J + 1)).length : ℝ) := by
  have h := length_ge_Phi _ (tauIter_valid J _ (valid_single (show 1 ≤ 2 by norm_num)))
  rw [Phi_iter] at h
  have e : V (J + 1) = V J ++ flat (tau^[J] [1]) := by
    unfold V
    rw [R_succ', show (0 :: (R J ++ tau^[J] [1])) = (0 :: R J) ++ tau^[J] [1] from rfl, flat_append]
  rw [e, List.length_append]
  push_cast
  have : (0 : ℝ) ≤ (V J).length := Nat.cast_nonneg _
  linarith

/-! ### Counting along the fixed point -/

lemma W_le (i : ℕ) : W i ≤ 1 := by
  have hi : i < (V i).length := by have := V_length i; omega
  rw [W_eq i i hi, List.getD_eq_getElem _ _ hi]
  exact flat_letters _ _ (List.getElem_mem hi)

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

lemma pow_bound (J : ℕ) (hJ : 5 ≤ J) :
    3.286 * 1.5321 ^ (J + 1) + 17.88 < 1.95 * ((lam ^ 2 - 2) * lam ^ J) := by
  obtain ⟨hl1, hl2, -⟩ := lam_spec
  have hq : (1.532087 : ℝ) ≤ lam ^ 2 - 2 := by nlinarith
  induction J, hJ using Nat.le_induction with
  | base =>
    have : (1.879385 : ℝ) ^ 5 ≤ lam ^ 5 := pow_le_pow_left₀ (by norm_num) hl1 5
    have hl5 : 0 ≤ lam ^ 5 := by positivity
    norm_num at this ⊢
    nlinarith
  | succ J hJ ih =>
    rw [pow_succ lam J, pow_succ (1.5321 : ℝ) (J + 1)]
    have hp : 0 ≤ lam ^ J := by positivity
    have hr : 0 ≤ (1.5321 : ℝ) ^ (J + 1) := by positivity
    have h := mul_le_mul_of_nonneg_left (show (1.5321 : ℝ) ≤ lam by linarith) hr
    have hq0 : 0 ≤ (lam ^ 2 - 2) * lam ^ J := by positivity
    nlinarith

lemma V6_length : (V 6).length = 156 := by decide +kernel

/-- For N > 156 there is a level J >= 5 with 1.95 (lam^2 - 2) lam^J < N and
|D(N)| <= 3.286 * 1.5321^(J+1) + 17.88. -/
lemma level (N : ℕ) (hN : 156 < N) :
    ∃ J : ℕ, 5 ≤ J ∧ 1.95 * ((lam ^ 2 - 2) * lam ^ J) < (N : ℝ) ∧
      |D N| ≤ 3.286 * 1.5321 ^ (J + 1) + 17.88 := by
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
  set J := Nat.find hex - 2 with hJ
  have hJ1 : Nat.find hex - 1 = J + 1 := by omega
  have hJ2 : Nat.find hex = J + 1 + 1 := by omega
  rw [hJ1] at hmin
  have e : V (Nat.find hex) = V (J + 1) ++ flat (tau^[J + 1] [1]) := by
    rw [hJ2]
    unfold V
    rw [R_succ' (J + 1), show (0 :: (R (J + 1) ++ tau^[J + 1] [1])) = (0 :: R (J + 1)) ++ tau^[J + 1] [1]
      from rfl, flat_append]
  refine ⟨J, by omega, ?_, ?_⟩
  · have hl := V_length_ge J
    have : ((V (J + 1)).length : ℝ) < N := by exact_mod_cast hmin
    linarith
  · rw [D_eq (Nat.find hex) N hk, e, List.take_append, List.take_of_length_le hmin.le, gL_append]
    obtain ⟨i, hi⟩ := flat_split (tau^[J + 1] [1]) (tauIter_valid _ _ (valid_single (by norm_num)))
      (N - (V (J + 1)).length)
    have hpre := prefix_bound (J + 1) 1 (by norm_num) i
    have hR := R_dev (J + 1)
    have hV : gL (V (J + 1)) = g [0] + g (R (J + 1)) := by
      unfold V
      rw [show (0 :: R (J + 1)) = [0] ++ R (J + 1) from rfl, ← g_append]
      rfl
    have h0 : g [0] = 2 := by rw [g_eq [0] 2 0 (by decide) (by decide)]; norm_num
    rw [hV, h0]
    have hq : 0 ≤ (0.3473 : ℝ) ^ (J + 1) := by positivity
    have h1 := abs_add_le (2 + g (R (J + 1))) (gL ((flat (tau^[J + 1] [1])).take (N - (V (J + 1)).length)))
    have h2 := abs_add_le (2 : ℝ) (g (R (J + 1)))
    have h3 := abs_sub_abs_le_abs_sub (gL ((flat (tau^[J + 1] [1])).take (N - (V (J + 1)).length)))
      (g ((tau^[J + 1] [1]).take i))
    simp only [PB] at hpre
    norm_num at h2
    linarith

/-- Over every prefix of W longer than 156 letters, |D| < N. -/
lemma D_small (N : ℕ) (hN : 156 < N) : |D N| < (N : ℝ) := by
  obtain ⟨J, hJ, hNr, hD⟩ := level N hN
  have hp := pow_bound J hJ
  linarith

/-- D(N)^4 <= 60000 N^3 for every N. -/
lemma D_pow4 (N : ℕ) : D N ^ 4 ≤ 60000 * (N : ℝ) ^ 3 := by
  obtain ⟨hc1, hc2⟩ := cc_bounds
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have e4 : D N ^ 4 = (|D N| ^ 2) ^ 2 := by rw [sq_abs]; ring
  rcases le_or_gt N 156 with h | h
  · have h1 := D_triv N
    have hN1 : (N : ℝ) ≤ 156 := by exact_mod_cast h
    have h2 : |D N| ^ 2 ≤ (cc * N) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
    have h3 : (|D N| ^ 2) ^ 2 ≤ ((cc * N) ^ 2) ^ 2 := pow_le_pow_left₀ (sq_nonneg _) h2 2
    have h4 : ((cc * N) ^ 2) ^ 2 = cc ^ 4 * N * N ^ 3 := by ring
    have h5 : cc ^ 4 ≤ 379 := by
      have := pow_le_pow_left₀ (by linarith) hc2 4
      norm_num at this
      linarith
    have h6 : cc ^ 4 * (N : ℝ) * N ^ 3 ≤ 379 * 156 * N ^ 3 := by
      have hc4 : 0 ≤ cc ^ 4 := by positivity
      have hN3 : (0 : ℝ) ≤ N ^ 3 := by positivity
      have := mul_le_mul h5 hN1 hN0 (by norm_num)
      nlinarith
    rw [e4]
    nlinarith
  · obtain ⟨J, hJ, hNr, hD⟩ := level N h
    obtain ⟨hl1, hl2, -⟩ := lam_spec
    have hp : (1 : ℝ) ≤ 1.5321 ^ J := one_le_pow₀ (by norm_num)
    have hD' : |D N| ≤ 22.92 * 1.5321 ^ J := by
      rw [pow_succ] at hD
      nlinarith
    have h2 : |D N| ^ 2 ≤ (22.92 * 1.5321 ^ J) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hD' 2
    have h3 : (|D N| ^ 2) ^ 2 ≤ ((22.92 * 1.5321 ^ J) ^ 2) ^ 2 :=
      pow_le_pow_left₀ (sq_nonneg _) h2 2
    have h4 : ((22.92 * (1.5321 : ℝ) ^ J) ^ 2) ^ 2 = 22.92 ^ 4 * (1.5321 ^ 4) ^ J := by
      rw [← pow_mul, mul_pow, ← pow_mul, ← pow_mul, mul_comm J (2 * 2)]
    have hb : (1.5321 : ℝ) ^ 4 ≤ lam ^ 3 := by
      have := pow_le_pow_left₀ (by norm_num) hl1 3
      norm_num at this ⊢
      linarith
    have h5 : ((1.5321 : ℝ) ^ 4) ^ J ≤ (lam ^ J) ^ 3 := by
      rw [← pow_mul lam J 3, mul_comm J 3, pow_mul lam 3 J]
      exact pow_le_pow_left₀ (by norm_num) hb J
    have hq : (2.9875 : ℝ) ≤ 1.95 * (lam ^ 2 - 2) := by nlinarith
    have hlJ : 0 ≤ lam ^ J := by positivity
    have h6 : (2.9875 * lam ^ J) ^ 3 ≤ (N : ℝ) ^ 3 :=
      pow_le_pow_left₀ (by positivity) (by nlinarith) 3
    have h7 : (0 : ℝ) ≤ (lam ^ J) ^ 3 := by positivity
    rw [e4]
    nlinarith

/-! ### The positions of 0 -/

/-- The limit, (1 + c)/c = 1.22668... -/
noncomputable def m0 : ℝ := (1 + cc) / cc

lemma m0_bounds : 1.22668 ≤ m0 ∧ m0 ≤ 1.22669 := by
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
  have h := D_small (B + 1 + (2 * Z (B + 1) + 200)) (by omega)
  have hs := O_add_Z (B + 1 + (2 * Z (B + 1) + 200))
  rw [hconst] at hs
  unfold D at h
  rw [hconst, abs_lt] at h
  obtain ⟨h1, -⟩ := h
  have hO : (O (B + 1 + (2 * Z (B + 1) + 200)) : ℝ) =
      ((B + 1 + (2 * Z (B + 1) + 200) : ℕ) : ℝ) - Z (B + 1) := by
    have : (O (B + 1 + (2 * Z (B + 1) + 200)) : ℝ) + Z (B + 1) =
        ((B + 1 + (2 * Z (B + 1) + 200) : ℕ) : ℝ) := by exact_mod_cast hs
    linarith
  rw [hO] at h1
  generalize hz : (Z (B + 1) : ℝ) = z at h1
  have hz0 : 0 ≤ z := by rw [← hz]; exact Nat.cast_nonneg _
  have hz' : ((B + 1 + (2 * Z (B + 1) + 200) : ℕ) : ℝ) = (B : ℝ) + 1 + (2 * z + 200) := by
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

/-- A linear scan of a word, checking 10 (t + 1) < 32 Z(t + 1) at each letter 0. -/
def chk : List ℕ → ℕ → ℕ → Bool
  | [], _, _ => true
  | x :: l, t, z =>
    if x = 0 then decide (10 * (t + 1) < 32 * (z + 1)) && chk l (t + 1) (z + 1)
    else chk l (t + 1) z

lemma chk_spec : ∀ (L : List ℕ) (t z : ℕ), chk L t z = true →
    ∀ i < L.length, L.getD i 0 = 0 →
      10 * (t + i + 1) < 32 * (z + (L.take (i + 1)).count 0) := by
  intro L
  induction L with
  | nil =>
    intro t z _ i hi
    simp at hi
  | cons x l ih =>
    intro t z h i hi hx
    by_cases h0 : x = 0
    · subst h0
      have h' : 10 * (t + 1) < 32 * (z + 1) ∧ chk l (t + 1) (z + 1) = true := by
        simpa [chk] using h
      rcases i with _ | i
      · simpa using h'.1
      · have := ih (t + 1) (z + 1) h'.2 i (by simp at hi; omega) (by simpa using hx)
        have e : ((0 :: l).take (i + 1 + 1)).count 0 = (l.take (i + 1)).count 0 + 1 := by
          simp [List.take_succ_cons]
        rw [e]
        omega
    · have h' : chk l (t + 1) z = true := by simpa [chk, h0] using h
      rcases i with _ | i
      · simp at hx
        exact absurd hx h0
      · have := ih (t + 1) z h' i (by simp at hi; omega) (by simpa using hx)
        have e : ((x :: l).take (i + 1 + 1)).count 0 = (l.take (i + 1)).count 0 := by
          simp [List.take_succ_cons, h0]
        rw [e]
        omega

lemma chk_word : chk (V 6) 0 0 = true := by decide +kernel

lemma bound_small (n : ℕ) (hn : 1 ≤ n) (ha : a n ≤ 156) :
    -2 < m0 - (a n : ℝ) / n ∧ m0 - (a n : ℝ) / n < 1 := by
  obtain ⟨hm1, hm2⟩ := m0_bounds
  obtain ⟨hZ, hO⟩ := a_spec n hn
  have hinf := zeros_infinite
  have hWp : W (Nat.nth (fun i => W i = 0) (n - 1)) = 0 := Nat.nth_mem_of_infinite hinf (n - 1)
  have ha' : a n = Nat.nth (fun i => W i = 0) (n - 1) + 1 := rfl
  set t := Nat.nth (fun i => W i = 0) (n - 1) with ht
  have hlen := V6_length
  have hW : (V 6).getD t 0 = 0 := by rw [← W_eq 6 t (by omega)]; exact hWp
  have hc := chk_spec (V 6) 0 0 chk_word t (by omega) hW
  have hZ' : ((V 6).take (t + 1)).count 0 = n := by
    rw [← (counts_eq 6 (t + 1) (by omega)).1, ← ha', hZ]
  rw [hZ'] at hc
  simp only [zero_add] at hc
  have hle : n ≤ a n := by have := O_add_Z (a n); omega
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hc' : (10 : ℝ) * (a n) < 32 * n := by
    rw [ha']
    exact_mod_cast hc
  have hle' : (n : ℝ) ≤ a n := by exact_mod_cast hle
  have h1 : (a n : ℝ) / n < 3.2 := by
    rw [div_lt_iff₀ hnpos]
    linarith
  have h2 : 1 ≤ (a n : ℝ) / n := by
    rw [le_div_iff₀ hnpos]
    linarith
  constructor <;> linarith

lemma bound_large (n : ℕ) (hn : 1 ≤ n) (ha : 156 < a n) :
    -2 < m0 - (a n : ℝ) / n ∧ m0 - (a n : ℝ) / n < 1 := by
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
  have hP : 4.41147 * (a n : ℝ) ≤ cc * a n := mul_le_mul_of_nonneg_right hc1 hA0
  have hQ1 : 4.41147 * (n : ℝ) ≤ cc * n := mul_le_mul_of_nonneg_right hc1 hnpos.le
  have hQ2 : cc * (n : ℝ) ≤ 4.41148 * n := mul_le_mul_of_nonneg_right hc2 hnpos.le
  have hE : cc * ((a n : ℝ) - n) = cc * a n - cc * n := by ring
  rw [hE] at hD1 hD2 ⊢
  constructor
  · rw [lt_div_iff₀ hnpos, lt_div_iff₀ hc]
    linarith
  · rw [div_lt_iff₀ hnpos, div_lt_iff₀ hc]
    linarith

/-- Kimberling's conjecture: a(n)/n tends to a number m = 1.22..., and -2 < m - a(n)/n < 1
for n >= 1. -/
theorem conjecture : ∃ m : ℝ, (1.22 ≤ m ∧ m < 1.23) ∧
    Tendsto (fun n : ℕ => (a n : ℝ) / n) atTop (𝓝 m) ∧
    ∀ n : ℕ, 1 ≤ n → -2 < m - (a n : ℝ) / n ∧ m - (a n : ℝ) / n < 1 := by
  obtain ⟨hm1, hm2⟩ := m0_bounds
  obtain ⟨hc1, hc2⟩ := cc_bounds
  have hc : 0 < cc := by linarith
  have hbound : ∀ n : ℕ, 1 ≤ n → -2 < m0 - (a n : ℝ) / n ∧ m0 - (a n : ℝ) / n < 1 := by
    intro n hn
    rcases le_or_gt (a n) 156 with h | h
    · exact bound_small n hn h
    · exact bound_large n hn h
  refine ⟨m0, ⟨by linarith, by linarith⟩, ?_, hbound⟩
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hlim : Tendsto (fun n : ℕ => Real.sqrt (Real.sqrt (11000 / n))) atTop (𝓝 0) := by
    have := ((tendsto_const_div_atTop_nhds_zero_nat (11000 : ℝ)).sqrt).sqrt
    simpa using this
  refine squeeze_zero' (Eventually.of_forall fun n => norm_nonneg _) ?_ hlim
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hb := hbound n hn
  have ha4 : (a n : ℝ) ≤ 4 * n := by
    have h1 : (a n : ℝ) / n < 3.23 := by linarith [hb.1]
    rw [div_lt_iff₀ hnpos] at h1
    linarith
  have hA0 : (0 : ℝ) ≤ a n := Nat.cast_nonneg _
  have hsq := D_pow4 (a n)
  have hdev := a_dev n hn
  rw [Real.norm_eq_abs]
  apply Real.abs_le_sqrt
  have h4 : (((a n : ℝ) / n - m0) ^ 2) ^ 2 ≤ 11000 / n := by
    have e : (a n : ℝ) / n - m0 = -(D (a n) / cc) / n := by
      rw [← hdev]
      field_simp
      ring
    have key : (((a n : ℝ) / n - m0) ^ 2) ^ 2 = D (a n) ^ 4 / (cc ^ 4 * n ^ 4) := by
      rw [e]
      field_simp
    rw [key, div_le_div_iff₀ (by positivity) hnpos]
    have hc4 : 378 ≤ cc ^ 4 := by
      have := pow_le_pow_left₀ (by norm_num) hc1 4
      norm_num at this
      linarith
    have hA3 : (a n : ℝ) ^ 3 ≤ (4 * n) ^ 3 := pow_le_pow_left₀ hA0 ha4 3
    have hn4 : (0 : ℝ) ≤ (n : ℝ) ^ 4 := by positivity
    have h5 : D (a n) ^ 4 ≤ 60000 * (4 * n) ^ 3 := by nlinarith
    have h6 : 11000 * 378 * (n : ℝ) ^ 4 ≤ 11000 * (cc ^ 4 * n ^ 4) := by nlinarith
    nlinarith
  have h2 : |((a n : ℝ) / n - m0) ^ 2| ≤ Real.sqrt (11000 / n) := Real.abs_le_sqrt h4
  rwa [abs_of_nonneg (sq_nonneg _)] at h2

end OMA.S_oeis_a287183

theorem OMA.solution : type_of% @OMA.S_oeis_a287183.main :=
  OMA.S_oeis_a287183.conjecture
