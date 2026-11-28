import OMAStatements.S_oeis_a288513

namespace OMA.S_oeis_a288513

open Filter Topology





/-! ### One pass -/

/-- Induction along the cases of `step`. -/
theorem step_rec {P : List ℕ → Prop} (h0 : P []) (h00 : ∀ l, P l → P (0 :: 0 :: l))
    (h10 : ∀ l, P l → P (1 :: 0 :: l)) (hz : P [0]) (ho : P [1])
    (hzy : ∀ y l, P ((y + 1) :: l) → P (0 :: (y + 1) :: l))
    (hoy : ∀ y l, P ((y + 1) :: l) → P (1 :: (y + 1) :: l))
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
        · rcases l with _ | ⟨y, l⟩
          · exact ho
          · rcases y with _ | y
            · exact h10 l (ih l (by simp at hu; omega))
            · exact hoy y l (ih _ (by simpa using hu))
        · exact hx x l (ih l (by omega))
  exact fun u => key u.length u le_rfl

/-- Both rules read a pair that ends in 0 and a letter 1 before a 1 is copied, so the pass
restarts at every letter 1. -/
lemma step_cut (u : List ℕ) : ∀ w, step (u ++ 1 :: w) = step u ++ step (1 :: w) := by
  refine step_rec (P := fun u => ∀ w, step (u ++ 1 :: w) = step u ++ step (1 :: w))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ u
  · intro w
    rfl
  · intro l ih w
    show 0 :: 1 :: 0 :: 1 :: step (l ++ 1 :: w) = 0 :: 1 :: 0 :: 1 :: step l ++ step (1 :: w)
    rw [ih]
    rfl
  · intro l ih w
    show 0 :: 0 :: 1 :: step (l ++ 1 :: w) = 0 :: 0 :: 1 :: step l ++ step (1 :: w)
    rw [ih]
    rfl
  · intro w
    rfl
  · intro w
    rfl
  · intro y l ih w
    show 0 :: step ((y + 1) :: l ++ 1 :: w) = 0 :: step ((y + 1) :: l) ++ step (1 :: w)
    rw [ih]
    rfl
  · intro y l ih w
    show 1 :: step ((y + 1) :: l ++ 1 :: w) = 1 :: step ((y + 1) :: l) ++ step (1 :: w)
    rw [ih]
    rfl
  · intro x l ih w
    show (x + 2) :: step (l ++ 1 :: w) = (x + 2) :: step l ++ step (1 :: w)
    rw [ih]
    rfl

/-- A run of letters 1 is copied. -/
lemma step_ones (r : ℕ) : step (List.replicate r 1) = List.replicate r 1 := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [List.replicate_succ]
    rcases r with _ | r
    · rfl
    · rw [List.replicate_succ] at ih ⊢
      show 1 :: step (1 :: List.replicate r 1) = 1 :: 1 :: List.replicate r 1
      rw [ih]

lemma step_append_ones (u : List ℕ) (r : ℕ) :
    step (u ++ List.replicate r 1) = step u ++ List.replicate r 1 := by
  rcases r with _ | r
  · simp only [List.replicate_zero, List.append_nil]
  · rw [List.replicate_succ, step_cut, ← List.replicate_succ, step_ones]

lemma step_zero_cons (t : List ℕ) : ∃ r, step (0 :: t) = 0 :: r := by
  rcases t with _ | ⟨y, t⟩
  · exact ⟨[], rfl⟩
  · rcases y with _ | y
    · exact ⟨1 :: 0 :: 1 :: step t, rfl⟩
    · exact ⟨step ((y + 1) :: t), rfl⟩

/-- A pass maps a prefix that ends with 0 to a prefix of the image: a lone final 0 is copied,
and 00 -> 0101 begins with 0. -/
lemma step_mono0 (v : List ℕ) : ∀ t, step (v ++ [0]) <+: step (v ++ [0] ++ t) := by
  refine step_rec (P := fun v => ∀ t, step (v ++ [0]) <+: step (v ++ [0] ++ t))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ v
  · intro t
    obtain ⟨r, hr⟩ := step_zero_cons t
    exact ⟨r, by
      show 0 :: r = step (0 :: t)
      rw [hr]⟩
  · intro l ih t
    obtain ⟨r, hr⟩ := ih t
    exact ⟨r, by
      show 0 :: 1 :: 0 :: 1 :: (step (l ++ [0]) ++ r) = 0 :: 1 :: 0 :: 1 :: step (l ++ [0] ++ t)
      rw [hr]⟩
  · intro l ih t
    obtain ⟨r, hr⟩ := ih t
    exact ⟨r, by
      show 0 :: 0 :: 1 :: (step (l ++ [0]) ++ r) = 0 :: 0 :: 1 :: step (l ++ [0] ++ t)
      rw [hr]⟩
  · intro t
    exact ⟨step t, rfl⟩
  · intro t
    exact ⟨step t, rfl⟩
  · intro y l ih t
    obtain ⟨r, hr⟩ := ih t
    exact ⟨r, by
      show 0 :: (step ((y + 1) :: l ++ [0]) ++ r) = 0 :: step ((y + 1) :: l ++ [0] ++ t)
      rw [hr]⟩
  · intro y l ih t
    obtain ⟨r, hr⟩ := ih t
    exact ⟨r, by
      show 1 :: (step ((y + 1) :: l ++ [0]) ++ r) = 1 :: step ((y + 1) :: l ++ [0] ++ t)
      rw [hr]⟩
  · intro x l ih t
    obtain ⟨r, hr⟩ := ih t
    exact ⟨r, by
      show (x + 2) :: (step (l ++ [0]) ++ r) = (x + 2) :: step (l ++ [0] ++ t)
      rw [hr]⟩

lemma step_prefix0 {A B : List ℕ} (hA : ∃ v, A = v ++ [0]) (h : A <+: B) : step A <+: step B := by
  obtain ⟨v, rfl⟩ := hA
  obtain ⟨t, rfl⟩ := h
  exact step_mono0 v t

/-! ### Blocks -/

/-- The blocks T0 = 10, T1 = 100, T2 = 1000. -/
def tok : ℕ → List ℕ
  | 0 => [1, 0]
  | 1 => [1, 0, 0]
  | _ => [1, 0, 0, 0]

/-- All blocks are 0, 1 or 2. -/
def Valid (s : List ℕ) : Prop := ∀ k ∈ s, k ≤ 2

/-- The word of a list of blocks. -/
def flat (s : List ℕ) : List ℕ := s.flatMap tok

/-- The shifted images of the blocks: the pass over a block followed by 00 is 00 followed by the
word of T0 -> T1, T1 -> T2, T2 -> T0 T0 T1. -/
def tauT : ℕ → List ℕ
  | 0 => [1]
  | 1 => [2]
  | _ => [0, 0, 1]

/-- The block morphism. -/
def tau (s : List ℕ) : List ℕ := s.flatMap tauT

/-- The cut image of a last block: the pass over T0, T1, T2 at the end of a word is 00 followed
by the word of nothing, T0, T0 T0 and the letters 1 counted by `exT`. -/
def trT : ℕ → List ℕ
  | 0 => []
  | 1 => [0]
  | _ => [0, 0]

/-- The number of letters 1 that the pass over a last block adds to the final run. -/
def exT : ℕ → ℕ
  | 1 => 0
  | _ => 1

/-- tau with the image of the last block cut. -/
def tr : List ℕ → List ℕ
  | [] => []
  | [k] => trT k
  | k :: k' :: s => tauT k ++ tr (k' :: s)

/-- The number of letters 1 that the pass over a block list adds to the final run. -/
def ex : List ℕ → ℕ
  | [] => 0
  | [k] => exT k
  | _ :: k' :: s => ex (k' :: s)

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

lemma valid02 : Valid [0, 2] := by
  intro y hy
  simp at hy
  omega

lemma trT_valid (k : ℕ) : Valid (trT k) := by
  intro x hx
  rcases k with _ | _ | k <;> simp [trT] at hx <;> omega

lemma tr_valid : ∀ X : List ℕ, Valid X → Valid (tr X)
  | [], _ => fun _ h => absurd h (List.not_mem_nil)
  | [k], _ => trT_valid k
  | k :: k' :: s, hX => by
    obtain ⟨-, hX'⟩ := valid_cons hX
    exact valid_append (tauT_valid k) (tr_valid (k' :: s) hX')

lemma tok_head (k : ℕ) : ∃ r, tok k = 1 :: r := by
  rcases k with _ | _ | k <;> exact ⟨_, rfl⟩

lemma step_append_flat (u s : List ℕ) : step (u ++ flat s) = step u ++ step (flat s) := by
  rcases s with _ | ⟨j, s⟩
  · rw [show flat [] = [] from rfl, List.append_nil, show step [] = [] from rfl,
      List.append_nil]
  · obtain ⟨r, hr⟩ := tok_head j
    rw [flat_cons, hr, List.cons_append, step_cut]

/-- The pass over a block, followed by 00, is 00 followed by the word of its shifted image. -/
lemma step_tok (k : ℕ) (hk : k ≤ 2) : step (tok k) ++ [0, 0] = [0, 0] ++ flat (tauT k) := by
  interval_cases k <;> rfl

lemma step_last (k : ℕ) (hk : k ≤ 2) :
    step (tok k) = [0, 0] ++ flat (trT k) ++ List.replicate (exT k) 1 := by
  interval_cases k <;> rfl

lemma step_flat (s : List ℕ) (hs : Valid s) :
    step (flat s) ++ [0, 0] = [0, 0] ++ flat (tau s) := by
  induction s with
  | nil => rfl
  | cons k s ih =>
    obtain ⟨hk, hs'⟩ := valid_cons hs
    rw [flat_cons, step_append_flat, List.append_assoc, ih hs', ← List.append_assoc,
      step_tok k hk, tau_cons, flat_append, List.append_assoc]

/-- The pass over the word of a nonempty block list. -/
lemma step_flat_exact : ∀ s : List ℕ, Valid s → s ≠ [] →
    step (flat s) = [0, 0] ++ flat (tr s) ++ List.replicate (ex s) 1
  | [], _, h => absurd rfl h
  | [k], hs, _ => by
    have hk := hs k (by simp)
    rw [show flat [k] = tok k by simp [flat], step_last k hk]
    rfl
  | k :: k' :: s, hs, _ => by
    obtain ⟨hk, hs'⟩ := valid_cons hs
    rw [flat_cons, step_append_flat, step_flat_exact (k' :: s) hs' (List.cons_ne_nil _ _)]
    show step (tok k) ++ ([0, 0] ++ flat (tr (k' :: s)) ++ List.replicate (ex (k' :: s)) 1) =
      [0, 0] ++ flat (tauT k ++ tr (k' :: s)) ++ List.replicate (ex (k' :: s)) 1
    rw [flat_append, ← List.append_assoc [0, 0], ← step_tok k hk]
    simp only [List.append_assoc]

lemma flat_end : ∀ X : List ℕ, X ≠ [] → ∃ v, flat X = v ++ [0]
  | [], h => absurd rfl h
  | [k], _ => by
    rcases k with _ | _ | k
    · exact ⟨[1], rfl⟩
    · exact ⟨[1, 0], rfl⟩
    · exact ⟨[1, 0, 0], rfl⟩
  | k :: k' :: s, _ => by
    obtain ⟨v, hv⟩ := flat_end (k' :: s) (List.cons_ne_nil _ _)
    exact ⟨tok k ++ v, by rw [flat_cons, hv, List.append_assoc]⟩

/-- If the word of X is a prefix of the word of Y, then the word of tr X is a prefix of the word
of tau Y. -/
lemma tr_mono (X Y : List ℕ) (hX : Valid X) (hY : Valid Y) (hne : X ≠ [])
    (h : flat X <+: flat Y) : flat (tr X) <+: flat (tau Y) := by
  have h1 := step_prefix0 (flat_end X hne) h
  rw [step_flat_exact X hX hne] at h1
  have h2 : step (flat Y) <+: [0, 0] ++ flat (tau Y) := by
    rw [← step_flat Y hY]
    exact List.prefix_append _ _
  have h3 := h1.trans h2
  rw [List.append_assoc] at h3
  have h4 := (List.prefix_append_right_inj [0, 0]).mp h3
  exact (List.prefix_append _ _).trans h4

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

/-- The blocks of the odd iterates: iterate 2k + 3 is 0, the word of bo k and a run of 1s. -/
def bo : ℕ → List ℕ
  | 0 => [0, 0]
  | k + 1 => [0, 2] ++ tr (tr (bo k))

/-- The blocks of the even iterates: iterate 2k + 4 is 000, the word of be k and a run of 1s. -/
def be (k : ℕ) : List ℕ := tr (bo k)

/-- The length of the final run of 1s of iterate 2k + 3. -/
def ro : ℕ → ℕ
  | 0 => 2
  | k + 1 => ex (tr (bo k)) + (ex (bo k) + ro k)

/-- The length of the final run of 1s of iterate 2k + 4. -/
def re (k : ℕ) : ℕ := ex (bo k) + ro k

lemma bo_valid (k : ℕ) : Valid (bo k) := by
  cases k with
  | zero =>
    intro y hy
    simp [bo] at hy
    omega
  | succ k => exact valid_append valid02 (tr_valid _ (tr_valid _ (bo_valid k)))

lemma be_valid (k : ℕ) : Valid (be k) := tr_valid _ (bo_valid k)

lemma bo_head (k : ℕ) : ∃ y s, bo k = 0 :: y :: s := by
  cases k with
  | zero => exact ⟨0, [], rfl⟩
  | succ k => exact ⟨2, tr (tr (bo k)), rfl⟩

lemma bo_ne_nil (k : ℕ) : bo k ≠ [] := by
  obtain ⟨y, s, h⟩ := bo_head k
  rw [h]
  exact List.cons_ne_nil _ _

lemma be_ne_nil (k : ℕ) : be k ≠ [] := by
  obtain ⟨y, s, h⟩ := bo_head k
  unfold be
  rw [h]
  show [1] ++ tr (y :: s) ≠ []
  exact List.append_ne_nil_of_left_ne_nil (List.cons_ne_nil _ _) _

lemma step_odd (X : List ℕ) (hX : Valid X) (hne : X ≠ []) (r : ℕ) :
    step ([0] ++ flat X ++ List.replicate r 1) =
      [0, 0, 0] ++ flat (tr X) ++ List.replicate (ex X + r) 1 := by
  obtain ⟨k, X', rfl⟩ := List.exists_cons_of_ne_nil hne
  obtain ⟨t, ht⟩ := tok_head k
  have e : step ([0] ++ flat (k :: X') ++ List.replicate r 1) =
      0 :: step (flat (k :: X') ++ List.replicate r 1) := by
    rw [flat_cons, ht]
    rfl
  rw [e, step_append_ones, step_flat_exact _ hX (List.cons_ne_nil _ _), List.replicate_add]
  simp only [List.append_assoc, List.cons_append, List.nil_append]

lemma step_even (X : List ℕ) (hX : Valid X) (hne : X ≠ []) (r : ℕ) :
    step ([0, 0, 0] ++ flat X ++ List.replicate r 1) =
      [0, 1, 0, 1, 0, 0, 0] ++ flat (tr X) ++ List.replicate (ex X + r) 1 := by
  obtain ⟨k, X', rfl⟩ := List.exists_cons_of_ne_nil hne
  obtain ⟨t, ht⟩ := tok_head k
  have e : step ([0, 0, 0] ++ flat (k :: X') ++ List.replicate r 1) =
      0 :: 1 :: 0 :: 1 :: 0 :: step (flat (k :: X') ++ List.replicate r 1) := by
    rw [flat_cons, ht]
    rfl
  rw [e, step_append_ones, step_flat_exact _ hX (List.cons_ne_nil _ _), List.replicate_add]
  simp only [List.append_assoc, List.cons_append, List.nil_append]

/-- The exact iterates from iterate 3 on. -/
lemma iter_odd_even (k : ℕ) :
    iter (2 * k + 3) = [0] ++ flat (bo k) ++ List.replicate (ro k) 1 ∧
      iter (2 * k + 4) = [0, 0, 0] ++ flat (be k) ++ List.replicate (re k) 1 := by
  have h_even : ∀ k, iter (2 * k + 3) = [0] ++ flat (bo k) ++ List.replicate (ro k) 1 →
      iter (2 * k + 4) = [0, 0, 0] ++ flat (be k) ++ List.replicate (re k) 1 := by
    intro k h
    rw [show 2 * k + 4 = 2 * k + 3 + 1 by ring, show iter (2 * k + 3 + 1) = step (iter (2 * k + 3))
      from rfl, h, step_odd _ (bo_valid k) (bo_ne_nil k)]
    rfl
  induction k with
  | zero =>
    have h3 : iter (2 * 0 + 3) = [0] ++ flat (bo 0) ++ List.replicate (ro 0) 1 := by decide
    exact ⟨h3, h_even 0 h3⟩
  | succ k ih =>
    have h : iter (2 * (k + 1) + 3) = [0] ++ flat (bo (k + 1)) ++ List.replicate (ro (k + 1)) 1 := by
      rw [show 2 * (k + 1) + 3 = 2 * k + 4 + 1 by ring,
        show iter (2 * k + 4 + 1) = step (iter (2 * k + 4)) from rfl, ih.2,
        step_even _ (be_valid k) (be_ne_nil k)]
      rfl
    exact ⟨h, h_even _ h⟩

/-! ### The limiting words -/

/-- The blocks of the limit of the odd iterates up to level k. -/
def So : ℕ → List ℕ
  | 0 => [0, 2]
  | k + 1 => [0, 2] ++ tau (tau (So k))

/-- The blocks of the limit of the even iterates up to level k. -/
def Se (k : ℕ) : List ℕ := tau (So k)

lemma So_valid (k : ℕ) : Valid (So k) := by
  cases k with
  | zero => exact valid02
  | succ k => exact valid_append valid02 (tau_valid _)

lemma Se_valid (k : ℕ) : Valid (Se k) := tau_valid _

lemma So_succ' (k : ℕ) : So (k + 1) = So k ++ tau^[2 * (k + 1)] [0, 2] := by
  induction k with
  | zero => rfl
  | succ k ih =>
    calc So (k + 1 + 1) = [0, 2] ++ tau (tau (So k ++ tau^[2 * (k + 1)] [0, 2])) := by
          rw [← ih]; rfl
      _ = ([0, 2] ++ tau (tau (So k))) ++ tau^[2 * (k + 1 + 1)] [0, 2] := by
        rw [tau_append, tau_append, show 2 * (k + 1 + 1) = 2 * (k + 1) + 1 + 1 by ring,
          Function.iterate_succ_apply', Function.iterate_succ_apply', List.append_assoc]
      _ = So (k + 1) ++ tau^[2 * (k + 1 + 1)] [0, 2] := rfl

lemma Se_succ' (k : ℕ) : Se (k + 1) = Se k ++ tau^[2 * (k + 1) + 1] [0, 2] := by
  unfold Se
  rw [So_succ', tau_append, Function.iterate_succ_apply']

/-- The letters of the iterates before the final run are prefixes of the limiting words. -/
lemma core_prefix (k : ℕ) : flat (bo k) <+: flat (So k) ∧ flat (be k) <+: flat (Se k) := by
  have h2 : ∀ k, flat (bo k) <+: flat (So k) → flat (be k) <+: flat (Se k) := fun k h =>
    tr_mono _ _ (bo_valid k) (So_valid k) (bo_ne_nil k) h
  induction k with
  | zero =>
    have h : flat (bo 0) <+: flat (So 0) := ⟨[0, 0], rfl⟩
    exact ⟨h, h2 0 h⟩
  | succ k ih =>
    have h : flat (bo (k + 1)) <+: flat (So (k + 1)) := by
      show flat ([0, 2] ++ tr (be k)) <+: flat ([0, 2] ++ tau (Se k))
      rw [flat_append, flat_append]
      exact (List.prefix_append_right_inj _).mpr
        (tr_mono _ _ (be_valid k) (Se_valid k) (be_ne_nil k) ih.2)
    exact ⟨h, h2 _ h⟩

/-! ### The Perron root -/

lemma lam_exists : ∃ x : ℝ, 1.521379 ≤ x ∧ x ≤ 1.52138 ∧ x ^ 3 - x - 2 = 0 := by
  have hc : ContinuousOn (fun x : ℝ => x ^ 3 - x - 2) (Set.Icc 1.521379 1.52138) := by
    fun_prop
  have h := intermediate_value_Icc (show (1.521379 : ℝ) ≤ 1.52138 by norm_num) hc
  have h0 : (0 : ℝ) ∈ Set.Icc ((fun x : ℝ => x ^ 3 - x - 2) 1.521379)
      ((fun x : ℝ => x ^ 3 - x - 2) 1.52138) := by
    constructor <;> norm_num
  obtain ⟨x, ⟨hx1, hx2⟩, hx⟩ := h h0
  exact ⟨x, hx1, hx2, hx⟩

/-- The Perron root, 1.52137..., the growth rate of the iterates. -/
noncomputable def lam : ℝ := Classical.choose lam_exists

lemma lam_spec : 1.521379 ≤ lam ∧ lam ≤ 1.52138 ∧ lam ^ 3 - lam - 2 = 0 :=
  Classical.choose_spec lam_exists

/-- The limiting number of letters 0 per letter 1, (lam^2 + lam)/2 = 1/(lam - 1) = 1.91798... -/
noncomputable def cc : ℝ := (lam ^ 2 + lam) / 2

lemma cc_bounds : 1.917986 ≤ cc ∧ cc ≤ 1.917989 := by
  obtain ⟨h1, h2, -⟩ := lam_spec
  unfold cc
  constructor <;> nlinarith

/-! ### Lengths -/

/-- The Perron weight of a block: 1, lam, lam^2. -/
noncomputable def wt : ℕ → ℝ
  | 0 => 1
  | 1 => lam
  | _ => lam ^ 2

/-- The weight of a block list; tau multiplies it by lam. -/
noncomputable def Phi (s : List ℕ) : ℝ := (s.map wt).sum

lemma Phi_append (u v : List ℕ) : Phi (u ++ v) = Phi u + Phi v := by
  simp [Phi]

lemma Phi_nonneg (s : List ℕ) : 0 ≤ Phi s := by
  obtain ⟨hl1, -, -⟩ := lam_spec
  unfold Phi
  apply List.sum_nonneg
  intro y hy
  obtain ⟨k, -, rfl⟩ := List.mem_map.mp hy
  rcases k with _ | _ | k <;> simp [wt] <;> positivity

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

lemma Phi_tr : ∀ X : List ℕ, Valid X → X ≠ [] → lam * Phi X - lam ≤ Phi (tr X)
  | [], _, h => absurd rfl h
  | [k], hX, _ => by
    obtain ⟨hl1, hl2, hf⟩ := lam_spec
    have hk := hX k (by simp)
    interval_cases k <;> simp [tr, trT, Phi, wt] <;> nlinarith
  | k :: k' :: s, hX, _ => by
    obtain ⟨hk, hX'⟩ := valid_cons hX
    have ih := Phi_tr (k' :: s) hX' (List.cons_ne_nil _ _)
    have e : tr (k :: k' :: s) = tauT k ++ tr (k' :: s) := rfl
    have h1 : Phi (tauT k) = lam * Phi [k] := by
      have := Phi_tau [k] (valid_single hk)
      rwa [tau_single] at this
    rw [e, Phi_append, show k :: k' :: s = [k] ++ (k' :: s) from rfl, Phi_append, h1]
    linarith

lemma length_ge_Phi (s : List ℕ) (hs : Valid s) : 1.72 * Phi s ≤ ((flat s).length : ℝ) := by
  obtain ⟨hl1, hl2, -⟩ := lam_spec
  induction s with
  | nil => simp [Phi, flat]
  | cons k s ih =>
    obtain ⟨hk, hs'⟩ := valid_cons hs
    rw [flat_cons, List.length_append, show k :: s = [k] ++ s from rfl, Phi_append]
    push_cast
    have := ih hs'
    have hk' : 1.72 * Phi [k] ≤ ((tok k).length : ℝ) := by
      interval_cases k <;> simp [Phi, wt, tok] <;> nlinarith
    linarith

lemma Phi_bo_be (k : ℕ) : (k : ℝ) + 2 ≤ Phi (bo k) ∧ (k : ℝ) + 1 ≤ Phi (be k) := by
  obtain ⟨hl1, hl2, hf⟩ := lam_spec
  have hbe : ∀ k : ℕ, (k : ℝ) + 2 ≤ Phi (bo k) → (k : ℝ) + 1 ≤ Phi (be k) := by
    intro k h
    have h1 := Phi_tr (bo k) (bo_valid k) (bo_ne_nil k)
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg _
    have h2 : lam * ((k : ℝ) + 2) ≤ lam * Phi (bo k) := mul_le_mul_of_nonneg_left h (by linarith)
    have h3 : (k : ℝ) + 1 ≤ lam * ((k : ℝ) + 1) := by nlinarith
    unfold be
    nlinarith
  induction k with
  | zero =>
    have h : ((0 : ℕ) : ℝ) + 2 ≤ Phi (bo 0) := by norm_num [bo, Phi, wt]
    exact ⟨h, hbe 0 h⟩
  | succ k ih =>
    have h1 := Phi_tr (be k) (be_valid k) (be_ne_nil k)
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg _
    have h2 : lam * ((k : ℝ) + 1) ≤ lam * Phi (be k) := mul_le_mul_of_nonneg_left ih.2 (by linarith)
    have e : Phi (bo (k + 1)) = 1 + lam ^ 2 + Phi (tr (be k)) := by
      have h02 : Phi [0, 2] = 1 + lam ^ 2 := by simp [Phi, wt]
      show Phi ([0, 2] ++ tr (be k)) = _
      rw [Phi_append, h02]
    have h : ((k + 1 : ℕ) : ℝ) + 2 ≤ Phi (bo (k + 1)) := by
      rw [e]
      push_cast
      nlinarith
    exact ⟨h, hbe _ h⟩

lemma bo_length (k : ℕ) : k + 2 ≤ (flat (bo k)).length := by
  have h1 := (Phi_bo_be k).1
  have h2 := length_ge_Phi (bo k) (bo_valid k)
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  have : ((k + 2 : ℕ) : ℝ) ≤ ((flat (bo k)).length : ℝ) := by push_cast; nlinarith
  exact_mod_cast this

lemma be_length (k : ℕ) : k + 1 ≤ (flat (be k)).length := by
  have h1 := (Phi_bo_be k).2
  have h2 := length_ge_Phi (be k) (be_valid k)
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  have : ((k + 1 : ℕ) : ℝ) ≤ ((flat (be k)).length : ℝ) := by push_cast; nlinarith
  exact_mod_cast this

lemma Phi_iter02 (n : ℕ) : Phi (tau^[n] [0, 2]) = (1 + lam ^ 2) * lam ^ n := by
  induction n with
  | zero => simp [Phi, wt]
  | succ n ih =>
    rw [Function.iterate_succ_apply', Phi_tau _ (tauIter_valid n _ valid02), ih, pow_succ]
    ring

/-! ### The limiting word -/

/-- The parity of the limit: W is the limit of the iterates 2k + 3 + res. -/
def res : ℕ := 0

/-- The letters before the blocks in the limiting word. -/
def head : List ℕ := [0]

/-- The blocks of the limiting word up to level k. -/
def C (k : ℕ) : List ℕ := So k

lemma C_valid (k : ℕ) : Valid (C k) := So_valid k

lemma C_zero : C 0 = tau^[res] [0, 2] := rfl

lemma C_succ (k : ℕ) : C (k + 1) = C k ++ tau^[2 * (k + 1) + res] [0, 2] := So_succ' k

/-- The letters of iterate 2k + 3 + res before its final run of 1s. -/
def core (k : ℕ) : List ℕ := head ++ flat (bo k)

/-- The length of the final run of 1s of iterate 2k + 3 + res. -/
def ones (k : ℕ) : ℕ := ro k

lemma iter_core (k : ℕ) : iter (2 * k + 3) = core k ++ List.replicate (ones k) 1 :=
  (iter_odd_even k).1

lemma core_length (k : ℕ) : k < (core k).length := by
  have := bo_length k
  simp only [core, head, List.length_append, List.length_cons, List.length_nil]
  omega

/-- V k: the letters before the blocks followed by the word of C k. -/
def V (k : ℕ) : List ℕ := head ++ flat (C k)

lemma core_prefix_V (k : ℕ) : core k <+: V k :=
  (List.prefix_append_right_inj head).mpr (core_prefix k).1

lemma V_succ' (k : ℕ) : V (k + 1) = V k ++ flat (tau^[2 * (k + 1) + res] [0, 2]) := by
  unfold V
  rw [C_succ, flat_append, List.append_assoc]

lemma V_prefix_succ (k : ℕ) : V k <+: V (k + 1) := by
  rw [V_succ']
  exact List.prefix_append _ _

lemma V_prefix {k k' : ℕ} (h : k ≤ k') : V k <+: V k' := by
  induction k', h using Nat.le_induction with
  | base => exact List.prefix_refl _
  | succ k' _ ih => exact ih.trans (V_prefix_succ k')

lemma V_length (k : ℕ) : k ≤ (V k).length := by
  induction k with
  | zero => exact Nat.zero_le _
  | succ k ih =>
    rw [V_succ', List.length_append]
    have h2 := flat_length_ge (tau^[2 * (k + 1) + res] [0, 2]) (tauIter_valid _ _ valid02)
    have h3 := tauIter_length_ge (2 * (k + 1) + res) [0, 2]
    simp only [List.length_cons, List.length_nil] at h3
    omega

lemma V_letters (k : ℕ) : ∀ x ∈ V k, x ≤ 1 := by
  intro x hx
  rcases List.mem_append.mp hx with h | h
  · simp [head] at h
    omega
  · exact flat_letters _ x h

lemma getD_prefix {l₁ l₂ : List ℕ} (h : l₁ <+: l₂) {i : ℕ} (hi : i < l₁.length) :
    l₁.getD i 0 = l₂.getD i 0 := by
  obtain ⟨s, rfl⟩ := h
  rw [List.getD_append _ _ _ _ hi]

lemma iter_letter (k i : ℕ) (hi : i < (core k).length) :
    (iter (2 * k + 3)).getD i 0 = (V k).getD i 0 := by
  rw [iter_core, List.getD_append _ _ _ _ hi]
  exact getD_prefix (core_prefix_V k) hi

lemma W_eq (k i : ℕ) (hi : i < (V k).length) : W i = (V k).getD i 0 := by
  have hc := core_length i
  have hl' : i < (V i).length := lt_of_lt_of_le hc (core_prefix_V i).length_le
  unfold W
  rw [iter_letter i i hc]
  rcases le_total i k with h | h
  · exact getD_prefix (V_prefix h) hl'
  · exact (getD_prefix (V_prefix h) hi).symm

/-- Letter i is the same in every iterate 2k + 3 with k >= i. -/
lemma W_odd (k i : ℕ) (hk : i ≤ k) : W i = (iter (2 * k + 3)).getD i 0 := by
  have hc : i < (core k).length := lt_of_le_of_lt hk (core_length k)
  rw [iter_letter k i hc]
  exact W_eq k i (lt_of_lt_of_le hc (core_prefix_V k).length_le)

lemma V_length_ge (J : ℕ) : 5.7 * lam ^ (2 * J) ≤ ((V J).length : ℝ) := by
  obtain ⟨hl1, hl2, -⟩ := lam_spec
  have hlast : ∃ P, C J = P ++ tau^[2 * J + res] [0, 2] := by
    cases J with
    | zero => exact ⟨[], by rw [C_zero, List.nil_append]; rfl⟩
    | succ J => exact ⟨C J, C_succ J⟩
  obtain ⟨P, hP⟩ := hlast
  have h := length_ge_Phi _ (tauIter_valid (2 * J + res) _ valid02)
  rw [Phi_iter02] at h
  have hV : (V J).length = head.length + (flat P).length +
      (flat (tau^[2 * J + res] [0, 2])).length := by
    unfold V
    rw [hP, flat_append, List.length_append, List.length_append, Nat.add_assoc]
  rw [hV]
  push_cast
  have hr : lam ^ (2 * J) ≤ lam ^ (2 * J + res) :=
    pow_le_pow_right₀ (by linarith) (Nat.le_add_right _ _)
  have hq : (3.3145 : ℝ) ≤ 1 + lam ^ 2 := by nlinarith
  have hp : 0 ≤ lam ^ (2 * J) := by positivity
  have h0 : (0 : ℝ) ≤ head.length := Nat.cast_nonneg _
  have h1 : (0 : ℝ) ≤ (flat P).length := Nat.cast_nonneg _
  have h2 : 5.7 * lam ^ (2 * J) ≤ 1.72 * ((1 + lam ^ 2) * lam ^ (2 * J + res)) := by
    have := mul_le_mul hq hr hp (by linarith)
    nlinarith
  linarith

/-! ### Deviation of words and block lists -/

/-- For a word, the number of letters 0 minus c times the number of letters 1. -/
noncomputable def gL (L : List ℕ) : ℝ := (L.count 0 : ℝ) - cc * (L.count 1 : ℝ)

lemma gL_append (u v : List ℕ) : gL (u ++ v) = gL u + gL v := by
  simp only [gL, List.count_append]
  push_cast
  ring

lemma gL_eq (L : List ℕ) (z o : ℕ) (hz : L.count 0 = z) (ho : L.count 1 = o) :
    gL L = z - cc * o := by
  unfold gL
  rw [hz, ho]

/-- The deviation of a block list: the deviation of its word. -/
noncomputable def g (s : List ℕ) : ℝ := gL (flat s)

lemma g_append (u v : List ℕ) : g (u ++ v) = g u + g v := by
  unfold g
  rw [flat_append, gL_append]

lemma g_eq (s : List ℕ) (z o : ℕ) (hz : (flat s).count 0 = z) (ho : (flat s).count 1 = o) :
    g s = z - cc * o :=
  gL_eq (flat s) z o hz ho

lemma g_tok (k : ℕ) (hk : k ≤ 2) :
    g (tau (tau [k])) + lam * g (tau [k]) + (lam ^ 2 - 1) * g [k] = 0 := by
  obtain ⟨-, -, hf⟩ := lam_spec
  interval_cases k
  · rw [g_eq _ 3 1 (by decide) (by decide), g_eq _ 2 1 (by decide) (by decide),
      g_eq _ 1 1 (by decide) (by decide)]
    unfold cc
    push_cast
    linear_combination (-1 - 1 / 2 * lam) * hf
  · rw [g_eq _ 4 3 (by decide) (by decide), g_eq _ 3 1 (by decide) (by decide),
      g_eq _ 2 1 (by decide) (by decide)]
    unfold cc
    push_cast
    linear_combination (-1 - 1 / 2 * lam) * hf
  · rw [g_eq _ 7 3 (by decide) (by decide), g_eq _ 4 3 (by decide) (by decide),
      g_eq _ 3 1 (by decide) (by decide)]
    unfold cc
    push_cast
    linear_combination (-2 - 1 / 2 * lam) * hf

/-- The deviation has no component along the Perron root: it follows f(x)/(x - lam). -/
lemma g_rec (s : List ℕ) (hs : Valid s) :
    g (tau (tau s)) + lam * g (tau s) + (lam ^ 2 - 1) * g s = 0 := by
  induction s with
  | nil => simp [g, gL, flat, tau]
  | cons k s ih =>
    obtain ⟨hk, hs'⟩ := valid_cons hs
    rw [show k :: s = [k] ++ s from rfl, tau_append, tau_append, g_append, g_append, g_append]
    linarith [g_tok k hk, ih hs']

/-! ### The quadratic form -/

/-- u x j: the deviation of tau^j(x). -/
noncomputable def u (x j : ℕ) : ℝ := g (tau^[j] [x])

/-- The quadratic form along the deviations. -/
noncomputable def E (x j : ℕ) : ℝ :=
  u x (j + 1) ^ 2 + lam * u x (j + 1) * u x j + (lam ^ 2 - 1) * u x j ^ 2

lemma u_rec (x j : ℕ) (hx : x ≤ 2) :
    u x (j + 2) = -lam * u x (j + 1) - (lam ^ 2 - 1) * u x j := by
  have hv : Valid (tau^[j] [x]) := tauIter_valid j _ (valid_single hx)
  have e2 : tau^[j + 2] [x] = tau (tau (tau^[j] [x])) := by
    rw [show j + 2 = j + 1 + 1 from rfl, Function.iterate_succ_apply',
      Function.iterate_succ_apply']
  have e1 : tau^[j + 1] [x] = tau (tau^[j] [x]) := Function.iterate_succ_apply' _ _ _
  have h := g_rec _ hv
  unfold u
  rw [e2, e1]
  linarith

lemma E_succ (x j : ℕ) (hx : x ≤ 2) : E x (j + 1) = (lam ^ 2 - 1) * E x j := by
  unfold E
  rw [show j + 1 + 1 = j + 2 from rfl, u_rec x j hx]
  ring

/-- The form is positive definite: it bounds the square of its second argument. -/
lemma E_ge (x j : ℕ) : 0.7359 * u x j ^ 2 ≤ E x j := by
  obtain ⟨hl1, hl2, -⟩ := lam_spec
  unfold E
  have h : u x (j + 1) ^ 2 + lam * u x (j + 1) * u x j + (lam ^ 2 - 1) * u x j ^ 2 =
      (u x (j + 1) + lam / 2 * u x j) ^ 2 + (3 / 4 * lam ^ 2 - 1) * u x j ^ 2 := by ring
  rw [h]
  have h2 : 0.7359 ≤ 3 / 4 * lam ^ 2 - 1 := by nlinarith
  have h3 : 0 ≤ u x j ^ 2 := sq_nonneg _
  nlinarith [sq_nonneg (u x (j + 1) + lam / 2 * u x j)]

lemma E_nonneg (x j : ℕ) : 0 ≤ E x j := by
  have := E_ge x j
  have h3 : 0 ≤ u x j ^ 2 := sq_nonneg _
  linarith

lemma E_zero : E 0 0 = 1 := by
  obtain ⟨-, -, hf⟩ := lam_spec
  have e : E 0 0 = u 0 1 ^ 2 + lam * u 0 1 * u 0 0 + (lam ^ 2 - 1) * u 0 0 ^ 2 := rfl
  rw [e, show u 0 1 = g [1] from rfl, show u 0 0 = g [0] from rfl,
    g_eq [1] 2 1 (by decide) (by decide), g_eq [0] 1 1 (by decide) (by decide)]
  unfold cc
  push_cast
  linear_combination (-1 + 3 / 4 * lam ^ 2 + 1 / 4 * lam ^ 3) * hf

lemma E_le (j : ℕ) : E 0 j ≤ 1.3225 ^ j := by
  obtain ⟨hl1, hl2, -⟩ := lam_spec
  induction j with
  | zero => simp [E_zero]
  | succ j ih =>
    rw [E_succ 0 j (by norm_num), pow_succ (1.3225 : ℝ) j]
    have h0 := E_nonneg 0 j
    have hq : lam ^ 2 - 1 ≤ 1.3225 := by nlinarith
    have hq0 : 0 ≤ lam ^ 2 - 1 := by nlinarith
    have h1 := mul_le_mul hq ih h0 (by norm_num)
    linarith

lemma u_bound (j : ℕ) : |u 0 j| ≤ 1.17 * 1.15 ^ j := by
  apply abs_le_of_sq_le_sq _ (by positivity)
  have h1 := E_ge 0 j
  have h2 := E_le j
  have e : (1.17 * (1.15 : ℝ) ^ j) ^ 2 = 1.3689 * 1.3225 ^ j := by
    rw [mul_pow, ← pow_mul, mul_comm j 2, pow_mul]
    norm_num
  rw [e]
  have hp : 0 ≤ (1.3225 : ℝ) ^ j := by positivity
  nlinarith

lemma u_one (J : ℕ) : g (tau^[J] [1]) = u 0 (J + 1) := by
  unfold u
  rw [Function.iterate_succ_apply]
  rfl

lemma u_two (J : ℕ) : g (tau^[J] [2]) = u 0 (J + 2) := by
  unfold u
  rw [show J + 2 = J + 1 + 1 from rfl, Function.iterate_succ_apply, Function.iterate_succ_apply]
  rfl

lemma g_pair (n : ℕ) : g (tau^[n] [0, 2]) = u 0 n + u 0 (n + 2) := by
  rw [show ([0, 2] : List ℕ) = [0] ++ [2] from rfl, tauIter_append, g_append, u_two]
  rfl

lemma pow_split (J : ℕ) : (1.15 : ℝ) ^ (2 * (J + 1) + res) = 1.15 ^ res * 1.3225 ^ (J + 1) := by
  rw [pow_add, pow_mul, show (1.15 : ℝ) ^ 2 = 1.3225 by norm_num, mul_comm]

lemma res_bound : (1 : ℝ) ≤ 1.15 ^ res ∧ (1.15 : ℝ) ^ res ≤ 1.15 := by
  constructor <;> norm_num [res]

/-! ### Prefixes of block lists -/

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

lemma gtok_bound (x : ℕ) (hx : x ≤ 2) : |g [x]| ≤ 1.1 := by
  obtain ⟨hc1, hc2⟩ := cc_bounds
  interval_cases x
  · rw [g_eq [0] 1 1 (by decide) (by decide), abs_le]; constructor <;> norm_num <;> linarith
  · rw [g_eq [1] 2 1 (by decide) (by decide), abs_le]; constructor <;> norm_num <;> linarith
  · rw [g_eq [2] 3 1 (by decide) (by decide), abs_le]; constructor <;> norm_num <;> linarith

/-- The bound for |g| over the prefixes of tau^J(x). -/
noncomputable def PB (J : ℕ) : ℝ := 15.61 * 1.15 ^ J - 14.5

/-- |g| over the prefixes of tau^J(x). -/
lemma prefix_bound (J : ℕ) : ∀ x, x ≤ 2 → ∀ i, |g ((tau^[J] [x]).take i)| ≤ PB J := by
  induction J with
  | zero =>
    intro x hx i
    simp only [Function.iterate_zero, id]
    have h0 : PB 0 = 1.11 := by norm_num [PB]
    rw [h0]
    rcases i with _ | i
    · norm_num [g, flat, gL]
    · rw [show [x].take (i + 1) = [x] by simp]
      have := gtok_bound x hx
      linarith
  | succ J ih =>
    intro x hx i
    rw [Function.iterate_succ_apply, tau_single]
    have hp : 0 ≤ (1.15 : ℝ) ^ J := by positivity
    have hPB : PB J ≤ PB (J + 1) := by
      unfold PB
      rw [pow_succ]
      nlinarith
    have hu0 := u_bound J
    have ha0 := abs_nonneg (u 0 J)
    have hsum : |u 0 J| + |u 0 J| + PB J ≤ PB (J + 1) := by
      unfold PB
      rw [pow_succ]
      nlinarith
    have hP0 := ih 0 (by norm_num)
    have hP1 := ih 1 (by norm_num)
    have hP2 := ih 2 (by norm_num)
    interval_cases x
    · exact le_trans (hP1 i) hPB
    · exact le_trans (hP2 i) hPB
    · have e : tau^[J] (tauT 2) = tau^[J] [0] ++ (tau^[J] [0] ++ tau^[J] [1]) := by
        rw [show tauT 2 = [0] ++ ([0] ++ [1]) from rfl, tauIter_append, tauIter_append]
      rw [e]
      have h1 : ∀ i, |g ((tau^[J] [0] ++ tau^[J] [1]).take i)| ≤ |u 0 J| + PB J := by
        intro i
        refine le_trans (take_append_le _ _ _ _ hP0 hP1 i) (max_le ?_ le_rfl)
        linarith
      refine le_trans (take_append_le _ _ _ _ hP0 h1 i) (max_le ?_ ?_)
      · linarith
      · show |u 0 J| + (|u 0 J| + PB J) ≤ PB (J + 1)
        linarith

/-- The deviation of C J, the sum of the deviations of its blocks tau^(2j+res)(T0 T2). -/
lemma C_dev (J : ℕ) : |g (C J)| ≤ 9.7 * 1.3225 ^ (J + 1) - 9.7 := by
  obtain ⟨hr1, hr2⟩ := res_bound
  have hpair : ∀ n, |g (tau^[n] [0, 2])| ≤ 1.17 * 1.15 ^ n * 2.3225 := by
    intro n
    rw [g_pair]
    have h1 := u_bound n
    have h2 := u_bound (n + 2)
    have h3 := abs_add_le (u 0 n) (u 0 (n + 2))
    have hp : 0 ≤ (1.15 : ℝ) ^ n := by positivity
    rw [pow_add] at h2
    nlinarith
  induction J with
  | zero =>
    rw [C_zero]
    have h := hpair res
    norm_num at h ⊢
    nlinarith
  | succ J ih =>
    rw [C_succ, g_append]
    have h := hpair (2 * (J + 1) + res)
    rw [pow_split] at h
    have hq : 0 ≤ (1.3225 : ℝ) ^ (J + 1) := by positivity
    have h1 := abs_add_le (g (C J)) (g (tau^[2 * (J + 1) + res] [0, 2]))
    have h2 : 1.17 * (1.15 ^ res * 1.3225 ^ (J + 1)) * 2.3225 ≤ 3.125 * (1.3225 : ℝ) ^ (J + 1) := by
      nlinarith
    rw [pow_succ (1.3225 : ℝ) (J + 1)]
    nlinarith

/-! ### Letters -/

lemma gL_tok_take (k : ℕ) (hk : k ≤ 2) (r : ℕ) : |gL ((tok k).take r)| ≤ 3 := by
  obtain ⟨hc1, hc2⟩ := cc_bounds
  have hz : ((tok k).take r).count 0 ≤ 3 := by
    calc ((tok k).take r).count 0 ≤ (tok k).count 0 :=
          List.Sublist.count_le _ (List.take_sublist _ _)
      _ ≤ 3 := by interval_cases k <;> decide
  have ho : ((tok k).take r).count 1 ≤ 1 := by
    calc ((tok k).take r).count 1 ≤ (tok k).count 1 :=
          List.Sublist.count_le _ (List.take_sublist _ _)
      _ ≤ 1 := by interval_cases k <;> decide
  have hz' : (((tok k).take r).count 0 : ℝ) ≤ 3 := by exact_mod_cast hz
  have ho' : (((tok k).take r).count 1 : ℝ) ≤ 1 := by exact_mod_cast ho
  have hz0 : (0 : ℝ) ≤ ((tok k).take r).count 0 := Nat.cast_nonneg _
  have ho0 : (0 : ℝ) ≤ ((tok k).take r).count 1 := Nat.cast_nonneg _
  unfold gL
  rw [abs_le]
  constructor <;> nlinarith

lemma flat_split : ∀ S : List ℕ, Valid S → ∀ t,
    ∃ i, |gL ((flat S).take t) - g (S.take i)| ≤ 3 := by
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

/-! ### Counting along the limiting word -/

lemma W_le (i : ℕ) : W i ≤ 1 := by
  have hi : i < (V i).length := lt_of_lt_of_le (core_length i) (core_prefix_V i).length_le
  rw [W_eq i i hi, List.getD_eq_getElem _ _ hi]
  exact V_letters _ _ (List.getElem_mem hi)

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

lemma gL_head : |gL head| ≤ 3 := by
  rw [gL_eq head head.length 0 (by decide) (by decide)]
  norm_num [head]

/-- For N > |V 0| there is a level J with |V J| < N <= |V (J + 1)|, 5.7 lam^(2J) < N and
|D(N)| <= 29 * 1.3225^(J+1) - 18.2. -/
lemma level (N : ℕ) (hN : (V 0).length < N) :
    ∃ J : ℕ, (V J).length < N ∧ N ≤ (V (J + 1)).length ∧ 5.7 * lam ^ (2 * J) < (N : ℝ) ∧
      |D N| ≤ 29 * 1.3225 ^ (J + 1) - 18.2 := by
  have hex : ∃ k, N ≤ (V k).length := ⟨N, V_length N⟩
  classical
  have hk : N ≤ (V (Nat.find hex)).length := Nat.find_spec hex
  have hk1 : 1 ≤ Nat.find hex := by
    by_contra h
    rw [show Nat.find hex = 0 by omega] at hk
    omega
  have hmin : (V (Nat.find hex - 1)).length < N := by
    have := Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega)
    omega
  set J := Nat.find hex - 1 with hJ
  have hJ1 : Nat.find hex = J + 1 := by omega
  rw [hJ1] at hk
  refine ⟨J, hmin, hk, ?_, ?_⟩
  · have hl := V_length_ge J
    have : ((V J).length : ℝ) < N := by exact_mod_cast hmin
    linarith
  · rw [D_eq (J + 1) N hk, V_succ', List.take_append, List.take_of_length_le hmin.le, gL_append]
    obtain ⟨i, hi⟩ := flat_split (tau^[2 * (J + 1) + res] [0, 2]) (tauIter_valid _ _ valid02)
      (N - (V J).length)
    have hpre : |g ((tau^[2 * (J + 1) + res] [0, 2]).take i)| ≤
        |u 0 (2 * (J + 1) + res)| + PB (2 * (J + 1) + res) := by
      rw [show ([0, 2] : List ℕ) = [0] ++ [2] from rfl, tauIter_append]
      refine le_trans (take_append_le _ _ _ _ (prefix_bound _ 0 (by norm_num))
        (prefix_bound _ 2 (by norm_num)) i) (max_le ?_ le_rfl)
      have := abs_nonneg (u 0 (2 * (J + 1) + res))
      linarith
    have hC := C_dev J
    have hV : gL (V J) = gL head + g (C J) := by
      unfold V
      rw [gL_append]
      rfl
    have hu := u_bound (2 * (J + 1) + res)
    have hPB : PB (2 * (J + 1) + res) = 15.61 * 1.15 ^ (2 * (J + 1) + res) - 14.5 := rfl
    rw [hPB, pow_split] at hpre
    rw [pow_split] at hu
    rw [hV]
    obtain ⟨hr1, hr2⟩ := res_bound
    have hq : 0 ≤ (1.3225 : ℝ) ^ (J + 1) := by positivity
    have hm : (1.15 : ℝ) ^ res * 1.3225 ^ (J + 1) ≤ 1.15 * 1.3225 ^ (J + 1) :=
      mul_le_mul_of_nonneg_right hr2 hq
    have hh := gL_head
    have h1 := abs_add_le (gL head + g (C J))
      (gL ((flat (tau^[2 * (J + 1) + res] [0, 2])).take (N - (V J).length)))
    have h2 := abs_add_le (gL head) (g (C J))
    have h3 := abs_sub_abs_le_abs_sub
      (gL ((flat (tau^[2 * (J + 1) + res] [0, 2])).take (N - (V J).length)))
      (g ((tau^[2 * (J + 1) + res] [0, 2]).take i))
    nlinarith

lemma pow_bound (J : ℕ) (hJ : 6 ≤ J) :
    29 * 1.3225 ^ (J + 1) - 18.2 < 0.24 * (5.7 * lam ^ (2 * J)) := by
  obtain ⟨hl1, hl2, -⟩ := lam_spec
  have hq : (2.3145 : ℝ) ≤ lam ^ 2 := by nlinarith
  induction J, hJ using Nat.le_induction with
  | base =>
    have h12 : (1.521379 : ℝ) ^ 12 ≤ lam ^ 12 := pow_le_pow_left₀ (by norm_num) hl1 12
    norm_num at h12 ⊢
    linarith
  | succ J hJ ih =>
    rw [pow_succ (1.3225 : ℝ) (J + 1), show 2 * (J + 1) = 2 * J + 2 by ring, pow_add lam (2 * J) 2]
    have hp : 0 ≤ lam ^ (2 * J) := by positivity
    have hr1 : (1 : ℝ) ≤ 1.3225 ^ (J + 1) := one_le_pow₀ (by norm_num)
    have hm := mul_le_mul_of_nonneg_left hq hp
    nlinarith

lemma V6_length : (V 6).length = 1687 := by decide +kernel

lemma V0_length : (V 0).length ≤ 13 := by decide

/-- Over every prefix of W longer than 1687 letters, |D| < 0.24 N. -/
lemma D_small (N : ℕ) (hN : 1687 < N) : |D N| < 0.24 * (N : ℝ) := by
  have h6 := V6_length
  have h0 := (V_prefix (show 0 ≤ 6 by norm_num)).length_le
  obtain ⟨J, hJ1, hJ2, hNr, hD⟩ := level N (by omega)
  have hJ : 6 ≤ J := by
    by_contra h
    have := (V_prefix (show J + 1 ≤ 6 by omega)).length_le
    omega
  have hp := pow_bound J hJ
  linarith

/-- D(N)^2 <= 300 N for every N. -/
lemma D_sq (N : ℕ) : D N ^ 2 ≤ 300 * (N : ℝ) := by
  obtain ⟨hc1, hc2⟩ := cc_bounds
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have h0 := V0_length
  rcases le_or_gt N (V 0).length with h | h
  · have h1 := D_triv N
    have hN1 : (N : ℝ) ≤ 13 := by exact_mod_cast le_trans h h0
    have h2 : D N ^ 2 ≤ (cc * N) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) h1 2
    have h3 : cc ^ 2 ≤ 3.68 := by nlinarith
    have h4 : (cc * (N : ℝ)) ^ 2 ≤ 3.68 * 13 * N := by
      have : (cc * (N : ℝ)) ^ 2 = cc ^ 2 * N * N := by ring
      rw [this]
      have hc2' : 0 ≤ cc ^ 2 := sq_nonneg _
      have := mul_le_mul h3 hN1 hN0 (by norm_num)
      nlinarith
    linarith
  · obtain ⟨J, -, -, hNr, hD⟩ := level N h
    obtain ⟨hl1, hl2, -⟩ := lam_spec
    have hq1 : (1 : ℝ) ≤ 1.3225 ^ J := one_le_pow₀ (by norm_num)
    have hD' : |D N| ≤ 38.36 * 1.3225 ^ J := by
      rw [pow_succ] at hD
      nlinarith
    have h1 : D N ^ 2 ≤ (38.36 * 1.3225 ^ J) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) hD' 2
    have h2 : (38.36 * (1.3225 : ℝ) ^ J) ^ 2 = 38.36 ^ 2 * ((1.3225 : ℝ) ^ 2) ^ J := by
      rw [mul_pow, ← pow_mul, mul_comm J 2, pow_mul]
    have h3 : ((1.3225 : ℝ) ^ 2) ^ J ≤ lam ^ (2 * J) := by
      rw [pow_mul]
      exact pow_le_pow_left₀ (by norm_num) (by nlinarith) J
    rw [h2] at h1
    norm_num at h1
    linarith

/-! ### The positions of 0 -/

/-- The limit, (1 + c)/c = lam = 1.52137... -/
noncomputable def m0 : ℝ := (1 + cc) / cc

lemma m0_bounds : 1.52137 ≤ m0 ∧ m0 ≤ 1.52139 := by
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
  have h := D_small (B + 1 + (4 * Z (B + 1) + 2600)) (by omega)
  have hs := O_add_Z (B + 1 + (4 * Z (B + 1) + 2600))
  rw [hconst] at hs
  unfold D at h
  rw [hconst, abs_lt] at h
  obtain ⟨h1, -⟩ := h
  have hO : (O (B + 1 + (4 * Z (B + 1) + 2600)) : ℝ) =
      ((B + 1 + (4 * Z (B + 1) + 2600) : ℕ) : ℝ) - Z (B + 1) := by
    have : (O (B + 1 + (4 * Z (B + 1) + 2600)) : ℝ) + Z (B + 1) =
        ((B + 1 + (4 * Z (B + 1) + 2600) : ℕ) : ℝ) := by exact_mod_cast hs
    linarith
  rw [hO] at h1
  generalize hz : (Z (B + 1) : ℝ) = z at h1
  have hz0 : 0 ≤ z := by rw [← hz]; exact Nat.cast_nonneg _
  have hz' : ((B + 1 + (4 * Z (B + 1) + 2600) : ℕ) : ℝ) = (B : ℝ) + 1 + (4 * z + 2600) := by
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

/-- A linear scan of a word, checking 10 (t + 1) < 25 Z(t + 1) at each letter 0. -/
def chk : List ℕ → ℕ → ℕ → Bool
  | [], _, _ => true
  | x :: l, t, z =>
    if x = 0 then decide (10 * (t + 1) < 25 * (z + 1)) && chk l (t + 1) (z + 1)
    else chk l (t + 1) z

lemma chk_spec : ∀ (L : List ℕ) (t z : ℕ), chk L t z = true →
    ∀ i < L.length, L.getD i 0 = 0 →
      10 * (t + i + 1) < 25 * (z + (L.take (i + 1)).count 0) := by
  intro L
  induction L with
  | nil =>
    intro t z _ i hi
    simp at hi
  | cons x l ih =>
    intro t z h i hi hx
    by_cases h0 : x = 0
    · subst h0
      have h' : 10 * (t + 1) < 25 * (z + 1) ∧ chk l (t + 1) (z + 1) = true := by
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

lemma bound_small (n : ℕ) (hn : 1 ≤ n) (ha : a n ≤ 1687) :
    -1 < m0 - (a n : ℝ) / n ∧ m0 - (a n : ℝ) / n < 1 := by
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
  have hc' : (10 : ℝ) * (a n) < 25 * n := by
    rw [ha']
    exact_mod_cast hc
  have hle' : (n : ℝ) ≤ a n := by exact_mod_cast hle
  have h1 : (a n : ℝ) / n < 2.5 := by
    rw [div_lt_iff₀ hnpos]
    linarith
  have h2 : 1 ≤ (a n : ℝ) / n := by
    rw [le_div_iff₀ hnpos]
    linarith
  constructor <;> linarith

lemma bound_large (n : ℕ) (hn : 1 ≤ n) (ha : 1687 < a n) :
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
  have hP : 1.917986 * (a n : ℝ) ≤ cc * a n := mul_le_mul_of_nonneg_right hc1 hA0
  have hQ1 : 1.917986 * (n : ℝ) ≤ cc * n := mul_le_mul_of_nonneg_right hc1 hnpos.le
  have hQ2 : cc * (n : ℝ) ≤ 1.917989 * n := mul_le_mul_of_nonneg_right hc2 hnpos.le
  have hE : cc * ((a n : ℝ) - n) = cc * a n - cc * n := by ring
  rw [hE] at hD1 hD2 ⊢
  constructor
  · rw [lt_div_iff₀ hnpos, lt_div_iff₀ hc]
    linarith
  · rw [div_lt_iff₀ hnpos, div_lt_iff₀ hc]
    linarith

/-- Kimberling's conjecture: a(n)/n tends to a number m = 1.52..., and -1 < m - a(n)/n < 1
for n >= 1. -/
theorem conjecture : ∃ m : ℝ, (1.52 ≤ m ∧ m < 1.53) ∧
    Tendsto (fun n : ℕ => (a n : ℝ) / n) atTop (𝓝 m) ∧
    ∀ n : ℕ, 1 ≤ n → -1 < m - (a n : ℝ) / n ∧ m - (a n : ℝ) / n < 1 := by
  obtain ⟨hm1, hm2⟩ := m0_bounds
  obtain ⟨hc1, hc2⟩ := cc_bounds
  have hc : 0 < cc := by linarith
  have hbound : ∀ n : ℕ, 1 ≤ n → -1 < m0 - (a n : ℝ) / n ∧ m0 - (a n : ℝ) / n < 1 := by
    intro n hn
    rcases le_or_gt (a n) 1687 with h | h
    · exact bound_small n hn h
    · exact bound_large n hn h
  refine ⟨m0, ⟨by linarith, by linarith⟩, ?_, hbound⟩
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hlim : Tendsto (fun n : ℕ => Real.sqrt (300 * 3 / cc ^ 2 / n)) atTop (𝓝 0) := by
    have := (tendsto_const_div_atTop_nhds_zero_nat (300 * 3 / cc ^ 2)).sqrt
    simpa using this
  refine squeeze_zero' (Eventually.of_forall fun n => norm_nonneg _) ?_ hlim
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hsq := D_sq (a n)
  have hb := hbound n hn
  have ha3 : (a n : ℝ) ≤ 3 * n := by
    have h1 : (a n : ℝ) / n < 2.5214 := by linarith [hb.1]
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
  have hD3 : D (a n) ^ 2 ≤ 300 * (3 * n) := by
    have : (300 : ℝ) * (a n) ≤ 300 * (3 * n) := by linarith
    linarith
  have e2 : 300 * 3 / cc ^ 2 * (cc ^ 2 * (n : ℝ) ^ 2) = 300 * 3 * n ^ 2 := by
    field_simp
  rw [e2]
  nlinarith [hD3, hnpos]

end OMA.S_oeis_a288513

theorem OMA.solution : type_of% @OMA.S_oeis_a288513.main :=
  OMA.S_oeis_a288513.conjecture
