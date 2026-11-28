import OMAStatements.S_oeis_a288511

-- Problem: oeis-a288511
-- Credit: @Aryan-Poonacha

namespace BinaryRewriteLength
open OMA.S_oeis_a288511


inductive Block where | one | two | three deriving DecidableEq
inductive Phase where
  | s0 | s1 | s2 | s3 | s4 | s5 | s6 | s7 | s8 | s9
  deriving DecidableEq

def digits : Block → List Bool
  | .one => [true, false]
  | .two => [true, false, false]
  | .three => [true, false, false, false]

/-- Moving the leading 00 of each rewritten block to the preceding block gives this substitution. -/
def subst : Block → List Block
  | .one => [.two]
  | .two => [.three]
  | .three => [.one, .one, .two]

def nextPhase : Phase → Phase
  | .s0 => .s1
  | .s1 => .s2
  | .s2 => .s3
  | .s3 => .s4
  | .s4 => .s5
  | .s5 => .s6
  | .s6 => .s7
  | .s7 => .s8
  | .s8 => .s9
  | .s9 => .s0

def suffix : Phase → List Block
  | .s0 => [.one, .one, .two]
  | .s1 => [.two, .two, .one]
  | .s2 => [.three, .three]
  | .s3 => [.two, .one, .one]
  | .s4 => [.three, .two]
  | .s5 => [.one, .two, .one]
  | .s6 => [.two, .three]
  | .s7 => [.three, .one, .one]
  | .s8 => [.one, .two, .two]
  | .s9 => [.two, .three, .one]

def emitted : Phase → List Block
  | .s0 => []
  | .s1 => []
  | .s2 => [.one, .one]
  | .s3 => []
  | .s4 => [.one]
  | .s5 => []
  | .s6 => []
  | .s7 => [.one]
  | .s8 => []
  | .s9 => [.three]

def extra : Phase → ℕ
  | .s0 => 0
  | .s1 => 1
  | .s2 => 1
  | .s3 => 1
  | .s4 => 0
  | .s5 => 1
  | .s6 => 1
  | .s7 => 1
  | .s8 => 0
  | .s9 => 1

def longFront : Phase → Bool
  | .s0 | .s2 | .s4 | .s6 | .s8 => true
  | _ => false

def front (p : Phase) : List Bool :=
  if longFront p then [false, false, false] else [false]

def emittedFront (p : Phase) : List Block :=
  if longFront p then [.one, .three] else []

def encode (w : List Block) := w.flatMap digits

structure State where
  phase : Phase
  blocks : List Block
  ones : ℕ

def State.bits (s : State) :=
  front s.phase ++ encode s.blocks ++ encode (suffix s.phase) ++ List.replicate s.ones true

def State.step (s : State) : State :=
  ⟨nextPhase s.phase, emittedFront s.phase ++ s.blocks.flatMap subst ++ emitted s.phase,
    extra s.phase + s.ones⟩

/-- A word boundary with a 1 on its right never creates a new replacement. -/
private theorem append_one (a z : List Bool) :
    rewrite (a ++ true :: z) = rewrite a ++ rewrite (true :: z) := by
  induction a using rewrite.induct with
  | case1 => simp [rewrite]
  | case2 b => cases b <;> simp [rewrite]
  | case3 w ih => simp [rewrite, ih]
  | case4 w ih => simp [rewrite, ih]
  | case5 w ih => simpa [rewrite] using congrArg (false :: ·) ih
  | case6 w ih => simpa [rewrite] using congrArg (true :: ·) ih

private lemma ones_rewrite (t : ℕ) : rewrite (List.replicate t true) = List.replicate t true := by
  induction t with
  | zero => simp [rewrite]
  | succ t ih =>
    cases t with
    | zero => simp [rewrite]
    | succ t => simpa [List.replicate_succ, rewrite] using congrArg (true :: ·) ih

private lemma append_ones (a : List Bool) (t : ℕ) :
    rewrite (a ++ List.replicate t true) = rewrite a ++ List.replicate t true := by
  cases t with
  | zero => simp
  | succ t =>
    rw [List.replicate_succ, append_one]
    exact congrArg (rewrite a ++ ·) (ones_rewrite (t+1))

private lemma suffix_head (p : Phase) : ∃ t, encode (suffix p) = true :: t := by
  cases p <;> exact ⟨_, rfl⟩

private lemma start_head (bs : List Block) (p : Phase) :
    ∃ t, encode bs ++ encode (suffix p) = true :: t := by
  cases bs with
  | nil => exact suffix_head p
  | cons k ks => cases k <;> exact ⟨_, rfl⟩

private lemma block_shift (k : Block) :
    rewrite (digits k) ++ [false,false] = [false,false] ++ encode (subst k) := by
  cases k <;> simp [digits, subst, encode, rewrite]

private lemma suffix_shift (p : Phase) : rewrite (encode (suffix p)) =
    [false,false] ++ encode (emitted p) ++ encode (suffix (nextPhase p)) ++
    List.replicate (extra p) true := by
  cases p <;> simp [encode, suffix, emitted, nextPhase, digits, extra, rewrite]

private lemma front_shift (p : Phase) : rewrite (front p) ++ [false,false] =
    front (nextPhase p) ++ encode (emittedFront p) := by
  cases p <;> simp [front, longFront, nextPhase, emittedFront, encode, digits, rewrite]

private lemma inner_shift (bs : List Block) (p : Phase) :
    rewrite (encode bs ++ encode (suffix p)) =
    [false,false] ++ encode (bs.flatMap subst) ++ encode (emitted p) ++
    encode (suffix (nextPhase p)) ++ List.replicate (extra p) true := by
  induction bs with
  | nil => simpa [encode] using suffix_shift p
  | cons k ks ih =>
    change rewrite ((digits k ++ encode ks) ++ encode (suffix p)) = _
    obtain ⟨t, ht⟩ := start_head ks p
    rw [List.append_assoc, ht, append_one, ← ht, ih]
    simp only [encode, List.flatMap_cons, List.flatMap_append, List.append_assoc] at *
    simpa only [encode, List.append_assoc, List.replicate_append_replicate] using congrArg
      (· ++ (encode (ks.flatMap subst) ++ encode (emitted p) ++
        encode (suffix (nextPhase p)) ++ List.replicate (extra p) true)) (block_shift k)

private lemma step_correct (s : State) : rewrite s.bits = s.step.bits := by
  obtain ⟨p, bs, t⟩ := s
  obtain ⟨z, hz⟩ := start_head bs p
  simp only [State.bits, State.step]
  rw [append_ones, List.append_assoc (front p), hz, append_one, ← hz, inner_shift]
  simp only [encode, List.flatMap_append, List.replicate_append_replicate, List.append_assoc] at *
  simpa only [encode, List.append_assoc, List.replicate_append_replicate] using congrArg
    (· ++ (encode (bs.flatMap subst) ++ encode (emitted p) ++
      encode (suffix (nextPhase p)) ++ List.replicate (extra p) true ++ List.replicate t true))
    (front_shift p)

def states : ℕ → State
  | 0 => ⟨.s0, [.two], 4⟩
  | n+1 => (states n).step

private theorem represents (n : ℕ) : word (n+6) = (states n).bits := by
  induction n with
  | zero => simp [word, rewrite, states, State.bits, front, longFront, encode, digits, suffix]
  | succ n ih => exact (congrArg rewrite ih).trans (step_correct _)

/-- The total weight of an ordered list of internal blocks. -/
def total (f : Block → ℤ) : List Block → ℤ
  | [] => 0
  | k :: ks => f k + total f ks

private lemma total_append (f : Block → ℤ) (a b : List Block) :
    total f (a ++ b) = total f a + total f b := by
  induction a with
  | nil => simp [total]
  | cons k ks ih => simp [total, ih, Int.add_assoc]

private lemma total_subst (f : Block → ℤ) (a : List Block) :
    total f (a.flatMap subst) = total (fun k => total f (subst k)) a := by
  induction a with
  | nil => rfl
  | cons k ks ih => simp [total, total_append, ih]

/-- Contribution of one internal block after n rewrites. -/
def blockWeight : ℕ → Block → ℤ
  | 0, k => (digits k).length
  | n+1, k => total (blockWeight n) (subst k)

/-- Combined contribution from the left and right boundaries after n rewrites. -/
def boundaryWeight : ℕ → Phase → ℤ
  | 0, p => (front p).length + (encode (suffix p)).length
  | n+1, p => boundaryWeight n (nextPhase p) + total (blockWeight n) (emittedFront p) +
      total (blockWeight n) (emitted p) + extra p

def future (n : ℕ) (s : State) : ℤ :=
  boundaryWeight n s.phase + total (blockWeight n) s.blocks + s.ones

private lemma encode_length (ks : List Block) :
    ((encode ks).length : ℤ) = total (blockWeight 0) ks := by
  induction ks with
  | nil => rfl
  | cons k ks ih =>
    change ((digits k ++ encode ks).length : ℤ) = blockWeight 0 k + total (blockWeight 0) ks
    simp [ih, blockWeight]

private lemma future_zero (s : State) : (s.bits.length : ℤ) = future 0 s := by
  simp only [State.bits, future, boundaryWeight, List.length_append,
    List.length_replicate, Int.natCast_add]
  rw [encode_length s.blocks]
  omega

private lemma future_succ (n : ℕ) (s : State) : future n s.step = future (n+1) s := by
  simp only [future, State.step, total_append, total_subst, Int.natCast_add, boundaryWeight]
  change _ = _ + total (fun k => total (blockWeight n) (subst k)) s.blocks + _
  omega

private lemma future_word (m t : ℕ) :
    ((word (m+t+6)).length : ℤ) = future t (states m) := by
  induction t generalizing m with
  | zero => simpa [represents] using future_zero (states m)
  | succ t ih =>
    rw [show m + (t+1) + 6 = (m+1) + t + 6 by omega, ih]
    exact future_succ _ _

/-- The characteristic identity on fourteen weights (three internal, ten boundary,
and one invariant trailing letter). -/
def recurrence (f : ℕ → ℤ) :=
  2*f 12 - f 11 + 2*f 10 - 4*f 9 + 4*f 8 - 4*f 7 +
  4*f 6 - 4*f 5 + 4*f 4 - 3*f 3 + 2*f 2 - 3*f 1 + 2*f 0

def satisfies (f : ℕ → ℤ) : Prop := f 13 = recurrence f

private lemma add_satisfies {f g : ℕ → ℤ} (hf : satisfies f) (hg : satisfies g) :
    satisfies (fun i => f i + g i) := by
  simp only [satisfies, recurrence] at *
  omega

private lemma const_satisfies (z : ℤ) : satisfies (fun _ => z) := by
  dsimp [satisfies, recurrence]
  omega

private lemma block_satisfies (k : Block) : satisfies (fun i => blockWeight i k) := by
  cases k <;> unfold satisfies <;> decide

private lemma boundary_satisfies (p : Phase) : satisfies (fun i => boundaryWeight i p) := by
  cases p <;> unfold satisfies <;> decide

private lemma list_satisfies (ks : List Block) :
    satisfies (fun i => total (blockWeight i) ks) := by
  induction ks with
  | nil => exact const_satisfies 0
  | cons k ks ih => exact add_satisfies (block_satisfies k) ih

private lemma state_satisfies (s : State) : satisfies (fun i => future i s) :=
  add_satisfies (add_satisfies (boundary_satisfies _) (list_satisfies _)) (const_satisfies _)

private lemma word_rec (m : ℕ) : ((word (m+6+13)).length : ℤ) =
    recurrence (fun i => (word (m+6+i)).length) := by
  have h (i : ℕ) : ((word (m+6+i)).length : ℤ) = future i (states m) := by
    rw [show m+6+i=m+i+6 by omega, future_word]
  simpa only [satisfies, h, recurrence] using (state_satisfies (states m))

private lemma source_rec (m : ℕ) : source (m+6+13) = recurrence (fun i => source (m+6+i)) := by
  change source ((m+3)+16) = _
  rw [source.eq_17]
  rfl

private lemma initial (n : ℕ) (hn : n < 19) : ((word n).length : ℤ) = source n := by
  match n with
  | 0 | 1 | 2 | 3 | 4 | 5 => simp [word, rewrite, source]
  | j+6 =>
    have h : ((word (j+6)).length : ℤ) = future j (states 0) := by
      simpa using future_word 0 j
    rw [h]
    have hj : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨
        j=9 ∨ j=10 ∨ j=11 ∨ j=12 := by omega
    rcases hj with h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst j <;> decide

private theorem all_lengths (n : ℕ) : ((word n).length : ℤ) = source n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n < 19
    · exact initial n hn
    · let m := n-19
      have hn' : n=m+6+13 := by dsimp [m]; omega
      have hi (i : ℕ) (hi : i < 13) : ((word (m+6+i)).length : ℤ) = source (m+6+i) :=
        ih _ (by omega)
      rw [hn', word_rec, source_rec]
      simp (disch := decide) only [recurrence, hi]

end BinaryRewriteLength

theorem OMA.solution : type_of% @OMA.S_oeis_a288511.main :=
  BinaryRewriteLength.all_lengths
