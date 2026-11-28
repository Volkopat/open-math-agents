import OMAStatements.S_oeis_a288480

namespace OMA.S_oeis_a288480

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

/-- A letter 1 is a cut point: no rule takes a 1 as its second letter. -/
lemma step_cut (u : List ℕ) : ∀ v, step (u ++ 1 :: v) = step u ++ step (1 :: v) := by
  refine step_rec (P := fun u => ∀ v, step (u ++ 1 :: v) = step u ++ step (1 :: v))
    ?_ ?_ ?_ ?_ ?_ ?_ u
  · intro v
    rfl
  · intro l ih v
    show 0 :: 1 :: 0 :: 1 :: step (l ++ 1 :: v) = 0 :: 1 :: 0 :: 1 :: step l ++ step (1 :: v)
    rw [ih]
    rfl
  · intro l ih v
    show 1 :: 1 :: 0 :: step (l ++ 1 :: v) = 1 :: 1 :: 0 :: step l ++ step (1 :: v)
    rw [ih]
    rfl
  · intro v
    rfl
  · intro y l ih v
    show 0 :: step ((y + 1) :: l ++ 1 :: v) = 0 :: step ((y + 1) :: l) ++ step (1 :: v)
    rw [ih]
    rfl
  · intro x l ih v
    show (x + 2) :: step (l ++ 1 :: v) = (x + 2) :: step l ++ step (1 :: v)
    rw [ih]
    rfl

/-! ### Tokens -/

/-- The token k is the word 1 0^k. -/
def tok (k : ℕ) : List ℕ := 1 :: List.replicate k 0

/-- The word of a list of tokens. -/
def flat (s : List ℕ) : List ℕ := s.flatMap tok

/-- The images of the tokens: 1 -> 1.10, 10 -> 1.100, 100 -> 1.100.10.1. -/
def tauT : ℕ → List ℕ
  | 0 => [0, 1]
  | 1 => [0, 2]
  | _ => [0, 2, 1, 0]

/-- The token morphism. -/
def tau (s : List ℕ) : List ℕ := s.flatMap tauT

/-- All tokens are at most 2. -/
def Valid (s : List ℕ) : Prop := ∀ k ∈ s, k ≤ 2

lemma flat_cons (k : ℕ) (s : List ℕ) : flat (k :: s) = tok k ++ flat s := by
  simp [flat]

lemma flat_append (u v : List ℕ) : flat (u ++ v) = flat u ++ flat v := by
  simp [flat]

lemma tau_cons (k : ℕ) (s : List ℕ) : tau (k :: s) = tauT k ++ tau s := by
  simp [tau]

lemma tau_append (u v : List ℕ) : tau (u ++ v) = tau u ++ tau v := by
  simp [tau]

lemma tauT_valid (k : ℕ) : Valid (tauT k) := by
  intro x hx
  rcases k with _ | _ | k <;> simp [tauT] at hx <;> omega

lemma tau_valid (s : List ℕ) : Valid (tau s) := by
  intro x hx
  simp only [tau, List.mem_flatMap] at hx
  obtain ⟨k, -, hk⟩ := hx
  exact tauT_valid k x hk

lemma step_tok (k : ℕ) (hk : k ≤ 2) : step (tok k) = flat (tauT k) := by
  interval_cases k <;> rfl

lemma step_flat (s : List ℕ) (hs : Valid s) : step (flat s) = flat (tau s) := by
  induction s with
  | nil => rfl
  | cons k s ih =>
    have hk : k ≤ 2 := hs k (by simp)
    have hs' : Valid s := fun x hx => hs x (by simp [hx])
    rw [flat_cons, tau_cons, flat_append]
    rcases s with _ | ⟨k', s'⟩
    · have h0 : flat [] = [] := rfl
      have h1 : tau [] = [] := rfl
      simp only [h0, h1, List.append_nil]
      exact step_tok k hk
    · have e : flat (k' :: s') = 1 :: (List.replicate k' 0 ++ flat s') := by
        rw [flat_cons]
        rfl
      rw [e, step_cut, ← e, ih hs', step_tok k hk]

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

lemma iter_eq (n : ℕ) : iter (n + 1) = 0 :: flat (tau^[n] [1, 0]) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [show iter (n + 1 + 1) = step (iter (n + 1)) from rfl, ih]
    have hv : Valid (tau^[n] [1, 0]) := tauIter_valid n _ (by intro x hx; simp at hx; omega)
    have hne : tau^[n] [1, 0] ≠ [] := by
      intro h
      have : (tau^[n] [1, 0]).length = 0 := by rw [h]; rfl
      have hl : ∀ m (s : List ℕ), s ≠ [] → tau^[m] s ≠ [] := by
        intro m
        induction m with
        | zero => intro s hs; exact hs
        | succ m ihm =>
          intro s hs
          rw [Function.iterate_succ_apply]
          apply ihm
          rcases s with _ | ⟨k, s⟩
          · exact absurd rfl hs
          · rw [tau_cons]
            rcases k with _ | _ | k <;> simp [tauT]
      exact hl n [1, 0] (by simp) h
    obtain ⟨k, s, hks⟩ : ∃ k s, tau^[n] [1, 0] = k :: s := by
      rcases h : tau^[n] [1, 0] with _ | ⟨k, s⟩
      · exact absurd h hne
      · exact ⟨k, s, rfl⟩
    have e : flat (tau^[n] [1, 0]) = 1 :: (List.replicate k 0 ++ flat s) := by
      rw [hks, flat_cons]
      rfl
    rw [show (0 :: flat (tau^[n] [1, 0])) = [0] ++ flat (tau^[n] [1, 0]) from rfl, e, step_cut,
      ← e, step_flat _ hv, Function.iterate_succ_apply']
    rfl

/-! ### The fixed point -/

/-- The stable prefix: 0 followed by the tokens tau^n(1). -/
def P (n : ℕ) : List ℕ := 0 :: flat (tau^[n] [0])

lemma P_prefix_succ (n : ℕ) : P n <+: P (n + 1) := by
  have e : tau^[n + 1] [0] = tau^[n] [0] ++ tau^[n] [1] := by
    rw [Function.iterate_succ_apply, show tau [0] = [0] ++ [1] from rfl, tauIter_append]
  refine ⟨flat (tau^[n] [1]), ?_⟩
  rw [P, P, e, flat_append]
  rfl

lemma P_prefix {m n : ℕ} (h : m ≤ n) : P m <+: P n := by
  induction n, h using Nat.le_induction with
  | base => exact List.prefix_refl _
  | succ n _ ih => exact ih.trans (P_prefix_succ n)

lemma P_prefix_iter (n : ℕ) : P n <+: iter (n + 2) := by
  rw [iter_eq (n + 1)]
  have e : tau^[n + 1] [1, 0] = tau^[n] [0] ++ tau^[n] [2, 0, 1] := by
    rw [Function.iterate_succ_apply, show tau [1, 0] = [0] ++ [2, 0, 1] from rfl,
      tauIter_append]
  refine ⟨flat (tau^[n] [2, 0, 1]), ?_⟩
  rw [P, e, flat_append]
  rfl

lemma flat_length_ge (s : List ℕ) : s.length ≤ (flat s).length := by
  induction s with
  | nil => simp [flat]
  | cons k s ih =>
    rw [flat_cons, List.length_append]
    simp only [tok, List.length_cons, List.length_replicate]
    omega

lemma tau_length_ge (s : List ℕ) : s.length ≤ (tau s).length := by
  induction s with
  | nil => simp [tau]
  | cons k s ih =>
    rw [tau_cons, List.length_append, List.length_cons]
    rcases k with _ | _ | k <;> simp [tauT] <;> omega

lemma tauIter_length (n : ℕ) : n + 1 ≤ (tau^[n] [0]).length := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    have hne : tau^[n] [0] ≠ [] := by
      intro h
      rw [h] at ih
      simp at ih
    obtain ⟨k, s, hks⟩ : ∃ k s, tau^[n] [0] = k :: s := by
      rcases h : tau^[n] [0] with _ | ⟨k, s⟩
      · exact absurd h hne
      · exact ⟨k, s, rfl⟩
    rw [hks] at ih ⊢
    rw [tau_cons, List.length_append]
    have := tau_length_ge s
    simp only [List.length_cons] at ih
    rcases k with _ | _ | k <;> simp [tauT] <;> omega

lemma P_length (n : ℕ) : n + 2 ≤ (P n).length := by
  rw [P, List.length_cons]
  have := tauIter_length n
  have := flat_length_ge (tau^[n] [0])
  omega

lemma getD_prefix {l₁ l₂ : List ℕ} (h : l₁ <+: l₂) {i : ℕ} (hi : i < l₁.length) :
    l₁.getD i 0 = l₂.getD i 0 := by
  obtain ⟨s, rfl⟩ := h
  rw [List.getD_append _ _ _ _ hi]

lemma W_eq (m i : ℕ) (hi : i < (P m).length) : W i = (P m).getD i 0 := by
  have hi' : i < (P i).length := by have := P_length i; omega
  have hW : W i = (P i).getD i 0 := (getD_prefix (P_prefix_iter i) hi').symm
  rw [hW]
  rcases le_total i m with h | h
  · exact getD_prefix (P_prefix h) hi'
  · exact (getD_prefix (P_prefix h) hi).symm

/-- Letter i is the same in every iterate from iterate i + 2 on. -/
lemma iter_stable (m i : ℕ) (h : i + 2 ≤ m) : (iter m).getD i 0 = W i := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
  have hi : i < (P k).length := by have := P_length k; omega
  rw [W_eq k i hi]
  exact (getD_prefix (P_prefix_iter k) hi).symm

/-! ### The deviation of token lists -/

/-- For a list of tokens, sqrt 2 times the number of letters 0 minus the number of letters 1. -/
noncomputable def F (s : List ℕ) : ℝ := Real.sqrt 2 * (s.sum : ℝ) - (s.length : ℝ)

lemma F_append (u v : List ℕ) : F (u ++ v) = F u + F v := by
  simp only [F, List.sum_append, List.length_append]
  push_cast
  ring

lemma tau_length (s : List ℕ) (hs : Valid s) :
    (tau s).length = 2 * s.length + 2 * s.count 2 := by
  induction s with
  | nil => simp [tau]
  | cons k s ih =>
    have hk : k ≤ 2 := hs k (by simp)
    rw [tau_cons, List.length_append, ih (fun x hx => hs x (by simp [hx]))]
    interval_cases k <;> simp [tauT, List.count_cons] <;> omega

lemma tau_sum (s : List ℕ) (hs : Valid s) : (tau s).sum = s.length + s.sum := by
  induction s with
  | nil => simp [tau]
  | cons k s ih =>
    have hk : k ≤ 2 := hs k (by simp)
    rw [tau_cons, List.sum_append, ih (fun x hx => hs x (by simp [hx]))]
    interval_cases k <;> simp [tauT] <;> omega

lemma tau_count (s : List ℕ) (hs : Valid s) : (tau s).count 2 + s.count 2 = s.sum := by
  induction s with
  | nil => simp [tau]
  | cons k s ih =>
    have hk : k ≤ 2 := hs k (by simp)
    rw [tau_cons, List.count_append, List.sum_cons]
    have := ih (fun x hx => hs x (by simp [hx]))
    interval_cases k <;> simp [tauT, List.count_cons] <;> omega

/-- On images of tau, F is multiplied by 1 - sqrt 2 under tau. -/
lemma F_tau_tau (s : List ℕ) (hs : Valid s) :
    F (tau (tau s)) = (1 - Real.sqrt 2) * F (tau s) := by
  have hv := tau_valid s
  have h1 := tau_length (tau s) hv
  have h2 := tau_sum (tau s) hv
  have h3 := tau_count (tau s) hv
  have h4 := tau_length s hs
  have h5 := tau_sum s hs
  have h6 := tau_count s hs
  have himg : (tau s).length + 2 * (tau s).count 2 = 2 * (tau s).sum := by omega
  have himg' : ((tau s).length : ℝ) + 2 * ((tau s).count 2 : ℝ) = 2 * ((tau s).sum : ℝ) := by
    exact_mod_cast himg
  have e1 : ((tau (tau s)).sum : ℝ) = ((tau s).length : ℝ) + ((tau s).sum : ℝ) := by
    rw [h2, Nat.cast_add]
  have e2 : ((tau (tau s)).length : ℝ) = 2 * ((tau s).length : ℝ) + 2 * ((tau s).count 2 : ℝ) := by
    rw [h1, Nat.cast_add, Nat.cast_mul, Nat.cast_mul]
    norm_num
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  unfold F
  rw [e1, e2]
  linear_combination ((tau s).sum : ℝ) * hs2 - himg'

lemma F_iter (j : ℕ) : ∀ u : List ℕ, Valid u →
    F (tau^[j] (tau u)) = (1 - Real.sqrt 2) ^ j * F (tau u) := by
  induction j with
  | zero => intro u _; simp
  | succ j ih =>
    intro u hu
    rw [Function.iterate_succ_apply, ih (tau u) (tau_valid u), F_tau_tau u hu, pow_succ]
    ring

lemma sqrt2_bounds : 1.4142 < Real.sqrt 2 ∧ Real.sqrt 2 < 1.4143 := by
  constructor
  · rw [Real.lt_sqrt (by norm_num)]
    norm_num
  · rw [Real.sqrt_lt' (by norm_num)]
    norm_num

/-- The values of F on the images of the prefixes of the token images. -/
lemma level_one (x : ℕ) (hx : x ≤ 2) (q : ℕ) (hq : q ≤ (tauT x).length) :
    |F (tau ((tauT x).take q))| ≤ 2 - Real.sqrt 2 := by
  have hb := sqrt2_bounds
  rw [abs_le]
  interval_cases x <;> simp only [tauT, List.length_cons, List.length_nil] at hq <;>
    interval_cases q <;> norm_num [tau, tauT, F] <;> (try constructor) <;> linarith [hb.1, hb.2]

/-- The values of F on the prefixes of the token images. -/
lemma level_zero (x : ℕ) (hx : x ≤ 2) (i : ℕ) (hi : i ≤ (tauT x).length) :
    |F ((tauT x).take i)| ≤ 2.3 - 1.05 := by
  have hb := sqrt2_bounds
  rw [abs_le]
  interval_cases x <;> simp only [tauT, List.length_cons, List.length_nil] at hi <;>
    interval_cases i <;> norm_num [tauT, F] <;> (try constructor) <;> linarith [hb.1, hb.2]

/-- Splitting a prefix of the image of a token list along its tokens. -/
lemma pref_split (T : List ℕ → List ℕ) (hT : ∀ u v, T (u ++ v) = T u ++ T v) (b : ℝ)
    (hb0 : 0 ≤ b)
    (hb : ∀ y ≤ 2, ∀ i ≤ (T [y]).length, |F ((T [y]).take i)| ≤ b) :
    ∀ ys : List ℕ, Valid ys → ∀ i ≤ (T ys).length,
      ∃ q ≤ ys.length, |F ((T ys).take i) - F (T (ys.take q))| ≤ b := by
  have hnil : T [] = [] := by
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
    exact ⟨0, le_rfl, by simp [hnil, F, hb0]⟩
  | cons y ys ih =>
    intro hv i hi
    have hy : y ≤ 2 := hv y (by simp)
    have hv' : Valid ys := fun x hx => hv x (by simp [hx])
    have e : T (y :: ys) = T [y] ++ T ys := by rw [← hT]; rfl
    rw [e] at hi ⊢
    rw [List.length_append] at hi
    rcases le_or_gt i (T [y]).length with h | h
    · refine ⟨0, by omega, ?_⟩
      rw [List.take_append_of_le_length h, List.take_zero, hnil]
      simpa [F] using hb y hy i h
    · obtain ⟨q, hq, hq'⟩ := ih hv' (i - (T [y]).length) (by omega)
      refine ⟨q + 1, by simp; omega, ?_⟩
      rw [List.take_append, List.take_of_length_le h.le, F_append,
        show (y :: ys).take (q + 1) = [y] ++ ys.take q from rfl, hT, F_append]
      have : F (T [y]) + F ((T ys).take (i - (T [y]).length)) - (F (T [y]) + F (T (ys.take q)))
          = F ((T ys).take (i - (T [y]).length)) - F (T (ys.take q)) := by ring
      rw [this]
      exact hq'

lemma tauIter_morph (j : ℕ) : ∀ u v, tau^[j] (u ++ v) = tau^[j] u ++ tau^[j] v :=
  tauIter_append j

/-- |F| over the prefixes of tau^(j+1)(x). -/
lemma prefix_bound (j : ℕ) : ∀ x ≤ 2, ∀ i ≤ (tau^[j + 1] [x]).length,
    |F ((tau^[j + 1] [x]).take i)| ≤ 2.3 - 1.05 * (Real.sqrt 2 - 1) ^ j := by
  have hb := sqrt2_bounds
  have hsing : ∀ x, tau [x] = tauT x := fun x => by simp [tau]
  induction j with
  | zero =>
    intro x hx i hi
    have e : tau^[0 + 1] [x] = tauT x := by
      rw [Function.iterate_succ_apply, Function.iterate_zero_apply, hsing]
    rw [e] at hi ⊢
    simpa using level_zero x hx i hi
  | succ j ih =>
    intro x hx i hi
    have hr0 : 0 ≤ Real.sqrt 2 - 1 := by linarith [hb.1]
    have hpow : 0 ≤ (Real.sqrt 2 - 1) ^ j := pow_nonneg hr0 j
    have hb0 : 0 ≤ 2.3 - 1.05 * (Real.sqrt 2 - 1) ^ j := by
      have : (Real.sqrt 2 - 1) ^ j ≤ 1 := pow_le_one₀ hr0 (by linarith [hb.2])
      linarith
    have e : tau^[j + 1 + 1] [x] = tau^[j + 1] (tauT x) := by
      rw [Function.iterate_succ_apply, hsing]
    rw [e] at hi ⊢
    obtain ⟨q, hq, hq'⟩ := pref_split (tau^[j + 1]) (tauIter_morph (j + 1)) _ hb0 ih (tauT x)
      (tauT_valid x) i hi
    have hlev := level_one x hx q hq
    have hF : F (tau^[j + 1] ((tauT x).take q)) =
        (1 - Real.sqrt 2) ^ j * F (tau ((tauT x).take q)) := by
      rw [Function.iterate_succ_apply]
      exact F_iter j _ (fun y hy => tauT_valid x y (List.mem_of_mem_take hy))
    have habs : |F (tau^[j + 1] ((tauT x).take q))| ≤ (Real.sqrt 2 - 1) ^ j * (2 - Real.sqrt 2) := by
      rw [hF, abs_mul, abs_pow, show |1 - Real.sqrt 2| = Real.sqrt 2 - 1 by
        rw [abs_of_neg (by linarith [hb.1])]; ring]
      exact mul_le_mul_of_nonneg_left hlev hpow
    have htri : |F ((tau^[j + 1] (tauT x)).take i)| ≤
        |F (tau^[j + 1] ((tauT x).take q))| + (2.3 - 1.05 * (Real.sqrt 2 - 1) ^ j) := by
      have := abs_sub_abs_le_abs_sub (F ((tau^[j + 1] (tauT x)).take i))
        (F (tau^[j + 1] ((tauT x).take q)))
      linarith
    rw [pow_succ]
    have : (Real.sqrt 2 - 1) ^ j * (2 - Real.sqrt 2) + (2.3 - 1.05 * (Real.sqrt 2 - 1) ^ j) ≤
        2.3 - 1.05 * ((Real.sqrt 2 - 1) ^ j * (Real.sqrt 2 - 1)) := by
      nlinarith [hpow, hb.1, hb.2]
    linarith

/-- |F| over the prefixes of the token list tau^n(1) is at most 2.3. -/
lemma token_prefix (n i : ℕ) (hi : i ≤ (tau^[n] [0]).length) :
    |F ((tau^[n] [0]).take i)| ≤ 2.3 := by
  have hb := sqrt2_bounds
  cases n with
  | zero =>
    rw [Function.iterate_zero_apply] at hi ⊢
    simp only [List.length_cons, List.length_nil] at hi
    interval_cases i <;> norm_num [F]
  | succ n =>
    have h := prefix_bound n 0 (by norm_num) i hi
    have : 0 ≤ (Real.sqrt 2 - 1) ^ n := pow_nonneg (by linarith [hb.1]) n
    linarith

/-! ### Counting letters 0 -/

/-- For a word, sqrt 2 times the number of letters 0 minus the number of letters 1. -/
noncomputable def FL (L : List ℕ) : ℝ := Real.sqrt 2 * (L.count 0 : ℝ) - (L.count 1 : ℝ)

lemma FL_append (u v : List ℕ) : FL (u ++ v) = FL u + FL v := by
  simp only [FL, List.count_append]
  push_cast
  ring

lemma FL_tok (k : ℕ) : FL (tok k) = F [k] := by
  simp [FL, F, tok, List.count_replicate]

lemma FL_flat (s : List ℕ) : FL (flat s) = F s := by
  induction s with
  | nil => simp [FL, F, flat]
  | cons k s ih =>
    rw [flat_cons, FL_append, FL_tok, ih, show k :: s = [k] ++ s from rfl, F_append]

lemma FL_tok_take (k : ℕ) (hk : k ≤ 2) (r : ℕ) : |FL ((tok k).take r)| ≤ 2 := by
  have hb := sqrt2_bounds
  rcases r with _ | r
  · simp [FL]
  · have e : (tok k).take (r + 1) = 1 :: List.replicate (min r k) 0 := by
      simp [tok, List.take_replicate]
    rw [e]
    generalize hj : min r k = j
    have hj2 : j ≤ 2 := by omega
    have hFL : FL (1 :: List.replicate j 0) = Real.sqrt 2 * (j : ℝ) - 1 := by
      simp [FL, List.count_replicate]
    rw [hFL, abs_le]
    have h0 : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg _
    have h2 : (j : ℝ) ≤ 2 := by exact_mod_cast hj2
    have h3 := mul_le_mul_of_nonneg_left h2 (Real.sqrt_nonneg 2)
    have h4 := mul_nonneg (Real.sqrt_nonneg 2) h0
    constructor <;> linarith [hb.1, hb.2]

lemma flat_split : ∀ S : List ℕ, Valid S → ∀ t ≤ (flat S).length,
    ∃ i ≤ S.length, |FL ((flat S).take t) - F (S.take i)| ≤ 2 := by
  intro S
  induction S with
  | nil =>
    intro _ t ht
    simp [flat] at ht
    subst ht
    exact ⟨0, le_rfl, by simp [FL, F]⟩
  | cons k S ih =>
    intro hv t ht
    have hk : k ≤ 2 := hv k (by simp)
    have hv' : Valid S := fun x hx => hv x (by simp [hx])
    rw [flat_cons] at ht ⊢
    rw [List.length_append] at ht
    rcases le_or_gt t (tok k).length with h | h
    · refine ⟨0, by omega, ?_⟩
      rw [List.take_append_of_le_length h]
      simpa [F] using FL_tok_take k hk t
    · obtain ⟨i, hi, hi'⟩ := ih hv' (t - (tok k).length) (by omega)
      refine ⟨i + 1, by simp; omega, ?_⟩
      rw [List.take_append, List.take_of_length_le h.le, FL_append, FL_tok,
        show (k :: S).take (i + 1) = [k] ++ S.take i from rfl, F_append]
      have : F [k] + FL ((flat S).take (t - (tok k).length)) - (F [k] + F (S.take i)) =
          FL ((flat S).take (t - (tok k).length)) - F (S.take i) := by ring
      rw [this]
      exact hi'

/-- Over every prefix of P n, |sqrt 2 (number of 0s) - (number of 1s)| <= 6. -/
lemma P_bound (n t : ℕ) (ht : t ≤ (P n).length) : |FL ((P n).take t)| ≤ 6 := by
  have hb := sqrt2_bounds
  rcases t with _ | t
  · simp [FL]
  · rw [P, List.take_succ_cons, show 0 :: (flat (tau^[n] [0])).take t =
      [0] ++ (flat (tau^[n] [0])).take t from rfl, FL_append]
    rw [P, List.length_cons] at ht
    obtain ⟨i, hi, hi'⟩ := flat_split (tau^[n] [0]) (tauIter_valid n _ (by
      intro x hx; simp at hx; omega)) t (by omega)
    have h1 := token_prefix n i hi
    have h0 : FL [0] = Real.sqrt 2 := by simp [FL]
    rw [h0]
    rw [abs_le] at hi' h1 ⊢
    constructor <;> linarith [hb.1, hb.2]

lemma P_letters (n : ℕ) : ∀ x ∈ P n, x ≤ 1 := by
  intro x hx
  rw [P, List.mem_cons] at hx
  rcases hx with rfl | hx
  · norm_num
  · simp only [flat, List.mem_flatMap, tok, List.mem_cons, List.mem_replicate] at hx
    obtain ⟨k, -, hk⟩ := hx
    omega

/-- Z(N): the number of letters 0 among the first N letters of W. -/
noncomputable def Z (N : ℕ) : ℕ := Nat.count (fun i => W i = 0) N

lemma Z_succ (N : ℕ) : Z (N + 1) = Z N + if W N = 0 then 1 else 0 := Nat.count_succ _ _

lemma Z_eq (m N : ℕ) (hN : N ≤ (P m).length) : Z N = ((P m).take N).count 0 := by
  induction N with
  | zero => simp [Z]
  | succ N ih =>
    have hN' : N < (P m).length := by omega
    have hW : W N = (P m)[N] := by rw [W_eq m N hN', List.getD_eq_getElem _ _ hN']
    rw [Z_succ, ih (by omega), List.take_add_one, List.getElem?_eq_getElem hN',
      List.count_append, hW]
    simp [List.count_singleton]

/-- |(1 + sqrt 2) Z(N) - N| <= 6. -/
lemma Z_bound (N : ℕ) : |(1 + Real.sqrt 2) * (Z N : ℝ) - N| ≤ 6 := by
  have hN : N ≤ (P N).length := by have := P_length N; omega
  have h := P_bound N N hN
  have hc : ((P N).take N).count 0 + ((P N).take N).count 1 = N := by
    have hl : ((P N).take N).length = N := by rw [List.length_take]; omega
    have hlet : ∀ x ∈ (P N).take N, x ≤ 1 := fun x hx => P_letters N x (List.mem_of_mem_take hx)
    have key : ∀ L : List ℕ, (∀ x ∈ L, x ≤ 1) → L.count 0 + L.count 1 = L.length := by
      intro L hL
      induction L with
      | nil => simp
      | cons y L ihL =>
        have hy := hL y (by simp)
        have := ihL (fun x hx => hL x (by simp [hx]))
        rcases (show y = 0 ∨ y = 1 by omega) with rfl | rfl <;> simp [List.count_cons] <;> omega
    rw [key _ hlet, hl]
  rw [Z_eq N N hN]
  have hc' : (((P N).take N).count 1 : ℝ) = N - ((P N).take N).count 0 := by
    have : (((P N).take N).count 0 : ℝ) + ((P N).take N).count 1 = N := by exact_mod_cast hc
    linarith
  simp only [FL] at h
  rw [hc'] at h
  have e : (1 + Real.sqrt 2) * (((P N).take N).count 0 : ℝ) - N =
      Real.sqrt 2 * (((P N).take N).count 0 : ℝ) - (N - ((P N).take N).count 0) := by ring
  rw [e]
  exact h


/-! ### The positions of 1 -/

lemma W_le (i : ℕ) : W i ≤ 1 := by
  have hi : i < (P i).length := by have := P_length i; omega
  rw [W_eq i i hi, List.getD_eq_getElem _ _ hi]
  exact P_letters i _ (List.getElem_mem hi)

/-- O(N): the number of letters 1 among the first N letters of W. -/
noncomputable def O (N : ℕ) : ℕ := Nat.count (fun i => W i = 1) N

lemma O_succ (N : ℕ) : O (N + 1) = O N + if W N = 1 then 1 else 0 := Nat.count_succ _ _

lemma O_add_Z (N : ℕ) : O N + Z N = N := by
  induction N with
  | zero => simp [O, Z]
  | succ N ih =>
    rw [O_succ, Z_succ]
    have := W_le N
    split_ifs <;> omega

lemma sqrt_half : Real.sqrt (1 / 2) = Real.sqrt 2 / 2 := by
  rw [← Real.sqrt_sq (show (0 : ℝ) ≤ Real.sqrt 2 / 2 by positivity)]
  congr 1
  rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

/-- |N - (1 + sqrt(1/2)) O(N)| <= 4.25. -/
lemma O_bound (N : ℕ) : |(N : ℝ) - (1 + Real.sqrt (1 / 2)) * (O N : ℝ)| ≤ 4.25 := by
  have hb := sqrt2_bounds
  have h := Z_bound N
  have hs := O_add_Z N
  have hZ : (Z N : ℝ) = N - O N := by
    have : (O N : ℝ) + Z N = N := by exact_mod_cast hs
    linarith
  rw [hZ] at h
  rw [sqrt_half]
  have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have e : (1 + Real.sqrt 2) * ((N : ℝ) - O N) - N =
      Real.sqrt 2 * ((N : ℝ) - (1 + Real.sqrt 2 / 2) * O N) := by
    linear_combination ((O N : ℝ) / 2) * hs2
  rw [e, abs_mul, abs_of_pos (by linarith [hb.1])] at h
  have hX := abs_nonneg ((N : ℝ) - (1 + Real.sqrt 2 / 2) * O N)
  nlinarith [mul_nonneg (sub_nonneg.mpr hb.1.le) hX]

lemma ones_infinite : (setOf (fun i => W i = 1)).Infinite := by
  have hb := sqrt2_bounds
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
  have h := O_bound (B + 1 + (2 * O (B + 1) + 6))
  rw [hconst, sqrt_half, abs_le] at h
  push_cast at h
  have : (0 : ℝ) ≤ O (B + 1) := by positivity
  nlinarith [hb.1, hb.2]

lemma a_bound (n : ℕ) (hn : 1 ≤ n) : |(a n : ℝ) - (1 + Real.sqrt (1 / 2)) * n| ≤ 4.25 := by
  have hinf := ones_infinite
  set p := Nat.nth (fun i => W i = 1) (n - 1) with hp
  have hOp : O p = n - 1 := Nat.count_nth_of_infinite hinf (n - 1)
  have hWp : W p = 1 := Nat.nth_mem_of_infinite hinf (n - 1)
  have hO1 : O (p + 1) = n := by
    rw [O_succ, if_pos hWp, hOp]
    omega
  have h := O_bound (p + 1)
  rw [hO1] at h
  have ha : a n = p + 1 := rfl
  rw [ha]
  push_cast at h ⊢
  exact h

lemma a_of (k n : ℕ) (hW : W k = 1) (hO : O k = n - 1) (hn : 1 ≤ n) : a n = k + 1 := by
  unfold a
  rw [← hO]
  unfold O
  rw [Nat.nth_count (p := fun i => W i = 1) hW]

lemma small_values : a 1 = 2 ∧ a 2 = 3 ∧ a 3 = 5 ∧ a 4 = 6 := by
  have hP : (P 4).length = 42 := by decide
  have hw : ∀ k, k < 42 → W k = (P 4).getD k 0 := fun k hk => W_eq 4 k (by rw [hP]; exact hk)
  have ho : ∀ k, k ≤ 42 → O k = k - ((P 4).take k).count 0 := fun k hk => by
    have h1 := O_add_Z k
    rw [Z_eq 4 k (by rw [hP]; exact hk)] at h1
    omega
  refine ⟨a_of 1 1 ?_ ?_ (by norm_num), a_of 2 2 ?_ ?_ (by norm_num), a_of 4 3 ?_ ?_ (by norm_num),
    a_of 5 4 ?_ ?_ (by norm_num)⟩
  all_goals first
    | (rw [hw _ (by norm_num)]; decide)
    | (rw [ho _ (by norm_num)]; decide)

/-- Kimberling's conjecture: a(n)/n -> 1 + sqrt(1/2), and -1 < 1 + sqrt(1/2) - a(n)/n < 1. -/
theorem conjecture : Tendsto (fun n : ℕ => (a n : ℝ) / n) atTop (𝓝 (1 + Real.sqrt (1 / 2))) ∧
    ∀ n : ℕ, 1 ≤ n → -1 < 1 + Real.sqrt (1 / 2) - (a n : ℝ) / n ∧
      1 + Real.sqrt (1 / 2) - (a n : ℝ) / n < 1 := by
  have hb := sqrt2_bounds
  refine ⟨?_, fun n hn => ?_⟩
  · rw [tendsto_iff_norm_sub_tendsto_zero]
    have hlim : Tendsto (fun n : ℕ => (4.25 : ℝ) / n) atTop (𝓝 0) :=
      tendsto_const_div_atTop_nhds_zero_nat 4.25
    refine squeeze_zero' (Eventually.of_forall fun n => norm_nonneg _) ?_ hlim
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    have h := a_bound n hn
    rw [Real.norm_eq_abs, show (a n : ℝ) / n - (1 + Real.sqrt (1 / 2)) =
      ((a n : ℝ) - (1 + Real.sqrt (1 / 2)) * n) / n by field_simp, abs_div,
      abs_of_pos hnpos]
    exact div_le_div_of_nonneg_right h hnpos.le
  · have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    rw [sqrt_half]
    rcases (show n ≤ 4 ∨ 5 ≤ n by omega) with h | h
    · obtain ⟨h1, h2, h3, h4⟩ := small_values
      interval_cases n <;> simp only [h1, h2, h3, h4] <;> norm_num <;>
        (try constructor) <;> linarith [hb.1, hb.2]
    · have hab := a_bound n hn
      rw [sqrt_half, abs_le] at hab
      have h5 : (5 : ℝ) ≤ n := by exact_mod_cast h
      have e : 1 + Real.sqrt 2 / 2 - (a n : ℝ) / n = ((1 + Real.sqrt 2 / 2) * n - a n) / n := by
        field_simp
      rw [e]
      constructor
      · rw [lt_div_iff₀ hnpos]
        linarith
      · rw [div_lt_iff₀ hnpos]
        linarith

end OMA.S_oeis_a288480

theorem OMA.solution : type_of% @OMA.S_oeis_a288480.main :=
  OMA.S_oeis_a288480.conjecture
