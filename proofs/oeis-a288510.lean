import OMAStatements.S_oeis_a288510
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic

/-!
# The positions of ones in Kimberling's limiting binary word

Clark Kimberling posed this conjecture in OEIS A288510, June 12, 2017.
The three internal zero-run blocks follow 1→2, 2→3, 3→112.
Starting with the exact boundary calculation in the A288511 proof, I first
construct nested prefixes of the actual even iterates. The length discrepancy
of a substituted block decays relative to its size by a quadratic energy identity.
The limit of the one positions divided by their indices is β/(β−1), where
β is the real root between 1.5213 and 1.5214 of β³=β+2.

Related length proof: https://github.com/lefttosolve2/open-math-agents/pull/27303
Credit: @Aryan-Poonacha
-/

open OMA.S_oeis_a288510 Filter Topology
namespace EvenRewrite

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
theorem append_one (a z : List Bool) :
    rewrite (a ++ true :: z) = rewrite a ++ rewrite (true :: z) := by
  induction a using rewrite.induct with
  | case1 => simp [rewrite]
  | case2 b => cases b <;> simp [rewrite]
  | case3 w ih => simp [rewrite, ih]
  | case4 w ih => simp [rewrite, ih]
  | case5 w ih => simpa [rewrite] using congrArg (false :: ·) ih
  | case6 w ih => simpa [rewrite] using congrArg (true :: ·) ih

lemma ones_rewrite (t : ℕ) : rewrite (List.replicate t true) = List.replicate t true := by
  induction t with
  | zero => simp [rewrite]
  | succ t ih =>
    cases t with
    | zero => simp [rewrite]
    | succ t => simpa [List.replicate_succ, rewrite] using congrArg (true :: ·) ih

lemma append_ones (a : List Bool) (t : ℕ) :
    rewrite (a ++ List.replicate t true) = rewrite a ++ List.replicate t true := by
  cases t with
  | zero => simp
  | succ t =>
    rw [List.replicate_succ, append_one]
    exact congrArg (rewrite a ++ ·) (ones_rewrite (t+1))

lemma suffix_head (p : Phase) : ∃ t, encode (suffix p) = true :: t := by
  cases p <;> exact ⟨_, rfl⟩

lemma start_head (bs : List Block) (p : Phase) :
    ∃ t, encode bs ++ encode (suffix p) = true :: t := by
  cases bs with
  | nil => exact suffix_head p
  | cons k ks => cases k <;> exact ⟨_, rfl⟩

lemma block_shift (k : Block) :
    rewrite (digits k) ++ [false,false] = [false,false] ++ encode (subst k) := by
  cases k <;> simp [digits, subst, encode, rewrite]

lemma suffix_shift (p : Phase) : rewrite (encode (suffix p)) =
    [false,false] ++ encode (emitted p) ++ encode (suffix (nextPhase p)) ++
    List.replicate (extra p) true := by
  cases p <;> simp [encode, suffix, emitted, nextPhase, digits, extra, rewrite]

lemma front_shift (p : Phase) : rewrite (front p) ++ [false,false] =
    front (nextPhase p) ++ encode (emittedFront p) := by
  cases p <;> simp [front, longFront, nextPhase, emittedFront, encode, digits, rewrite]

lemma inner_shift (bs : List Block) (p : Phase) :
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

lemma step_correct (s : State) : rewrite s.bits = s.step.bits := by
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

theorem represents (n : ℕ) : word (n+6) = (states n).bits := by
  induction n with
  | zero => simp [word, rewrite, states, State.bits, front, longFront, encode, digits, suffix]
  | succ n ih => exact (congrArg rewrite ih).trans (step_correct _)


def sigma (v : List Block) := v.flatMap subst

def tile : ℕ → List Block → List Block
  | 0, v => v
  | n+1, v => sigma (tile n v)

def seed : List Block := [.two,.one,.one,.two]

def blockPrefix : ℕ → List Block
  | 0 => []
  | n+1 => seed ++ tile 2 (blockPrefix n)

lemma tile_append (k : ℕ) (u v : List Block) :
    tile k (u++v) = tile k u ++ tile k v := by
  induction k with
  | zero => rfl
  | succ k ih => simp [tile, sigma, ih]

lemma tile_nil (k : ℕ) : tile k [] = [] := by
  induction k <;> simp [tile, sigma, *]

lemma tile_add (a b : ℕ) (w : List Block) : tile (a+b) w = tile b (tile a w) := by
  induction b with
  | zero => rfl
  | succ b ih => exact congrArg sigma ih

lemma prefix_more (k : ℕ) : blockPrefix (k+1) = blockPrefix k ++ tile (2*k) seed := by
  induction k with
  | zero => simp [blockPrefix, tile, sigma]
  | succ k ih =>
    rw [blockPrefix, ih, tile_append, ← tile_add, ← List.append_assoc]
    rw [← ih, Nat.mul_succ]
    rfl

lemma sigma_length (v : List Block) : v.length ≤ (sigma v).length := by
  induction v with
  | nil => decide
  | cons k ks ih =>
    cases k <;> simp [sigma, subst] at * <;> omega

lemma tile_length (k : ℕ) (v : List Block) : v.length ≤ (tile k v).length := by
  induction k with
  | zero => exact Nat.le_refl _
  | succ k ih => exact ih.trans (sigma_length _)

lemma prefix_length (k : ℕ) : k ≤ (blockPrefix k).length := by
  induction k with
  | zero => omega
  | succ k ih =>
    rw [prefix_more, List.length_append]
    have h := tile_length (2*k) seed
    have : seed.length = 4 := rfl
    omega

lemma prefix_monotone {m n : ℕ} (h : m ≤ n) : ∃ tail, blockPrefix n = blockPrefix m ++ tail := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le h
  clear h
  induction k with
  | zero => exact ⟨[], (List.append_nil _).symm⟩
  | succ k ih =>
    obtain ⟨t,ht⟩ := ih
    exact ⟨t ++ _, by rw [Nat.add_succ, prefix_more, ht, List.append_assoc]⟩

lemma long_flip (p : Phase) : longFront (nextPhase p) = !(longFront p) := by
  cases p <;> rfl

lemma even_front (k : ℕ) : longFront (states (2*k)).phase = true := by
  induction k with
  | zero => rfl
  | succ k ih => simpa only [Nat.mul_succ, states, State.step, long_flip, Bool.not_not] using ih

lemma state_prefix (k : ℕ) : ∃ t, (states (2*k)).blocks = blockPrefix k ++ t := by
  induction k with
  | zero => exact ⟨_,rfl⟩
  | succ k ih =>
    obtain ⟨t,ht⟩ := ih
    have hf := even_front k
    let s := states (2*k)
    change s.blocks = blockPrefix k ++ t at ht
    change longFront s.phase = true at hf
    rw [Nat.mul_succ]
    change ∃ _, s.step.step.blocks = blockPrefix (k+1) ++ _
    simp only [State.step, emittedFront, long_flip, hf, Bool.not_true, Bool.false_eq_true,
      if_false, if_true, List.nil_append, ht, List.flatMap_append, blockPrefix]
    refine ⟨tile 2 t ++ sigma (emitted s.phase) ++ emitted (nextPhase s.phase), ?_⟩
    simp only [tile, sigma, seed, subst, List.flatMap_cons, List.flatMap_nil,
                              List.append_assoc, List.cons_append, List.nil_append, List.append_nil]

/-- Every sufficiently late even iterate begins with these three zeros and all
the bits from any prescribed finite blockPrefix of the infinite block word. -/
lemma bits_prefix (k m : ℕ) (h : k ≤ m) :
    ∃ t, word (2*m+6) = [false,false,false] ++ encode (blockPrefix k) ++ t := by
  obtain ⟨v,hv⟩ := prefix_monotone h
  obtain ⟨s,hs⟩ := state_prefix m
  rw [represents, State.bits, front, even_front, if_pos rfl, hs, hv]
  refine ⟨encode v ++ encode s ++ encode (suffix (states (2*m)).phase) ++ List.replicate (states (2*m)).ones true, ?_⟩
  simp only [encode,List.flatMap_append,List.append_assoc]

/-- The first n blocks, read once their nested prefixes have at least n blocks. -/
def initial (n : ℕ) := (blockPrefix n).take n

lemma initial_length (n : ℕ) : (initial n).length = n := by
  simp [initial, min_eq_left (prefix_length n)]

lemma initial_take {n m : ℕ} (h : n ≤ m) : (blockPrefix m).take n = initial n := by
  obtain ⟨t,ht⟩ := prefix_monotone h
  rw [ht, List.take_append_of_le_length (prefix_length n)]
  rfl


def onePos (n : ℕ) := 4 + (encode (initial (n-1))).length

lemma encode_count (v : List Block) : (encode v).count true = v.length := by
  induction v with
  | nil => rfl
  | cons k t ih => cases k <;> simp [encode, digits] at * <;> omega

lemma immediate (u z : List Bool) : IsPosition true (u ++ true :: z) (u.count true+1) (u.length+1) := by
  refine ⟨by omega, ?_, ?_⟩
  · simp
  · rw [List.take_append, List.take_of_length_le (Nat.le_succ _)]
    simp

lemma tail_after_initial (n : ℕ) : ∃ k t, blockPrefix (n+1) = initial n ++ k :: t := by
  have h := List.take_append_drop n (blockPrefix (n+1))
  rw [initial_take (Nat.le_succ n)] at h
  generalize ht : (blockPrefix (n+1)).drop n = remaining at h
  cases remaining with
  | nil =>
    have hh := congrArg List.length h
    simp only [List.append_nil, initial_length] at hh
    have := prefix_length (n+1)
    omega
  | cons k t => exact ⟨k,t,h.symm⟩

lemma position_eventually (n : ℕ) (hn : 1 ≤ n) :
    ∀ᶠ t : ℕ in atTop, IsPosition true (word (2*t)) n (onePos n) := by
  obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  rw [Filter.eventually_atTop]
  refine ⟨j+4,fun t ht => ?_⟩
  have ha : 2*t = 2*(t-3)+6 := by omega
  rw [ha]
  obtain ⟨tail,hword⟩ := bits_prefix (j+1) (t-3) (by omega)
  obtain ⟨k,t',hb⟩ := tail_after_initial j
  have hk : ∃ s, digits k = true :: s := by cases k <;> exact ⟨_,rfl⟩
  obtain ⟨s,hs⟩ := hk
  let u := [false,false,false] ++ encode (initial j)
  have hu : u.count true = j := by simp [u, encode_count, initial_length]
  have hp : u.length+1 = onePos (j+1) := by simp [onePos,u]; omega
  have hex : word (2*(t-3)+6) = u ++ true :: (s ++ encode t' ++ tail) := by
    rw [hword,hb]
    simp [u, encode, List.flatMap_append, hs, List.append_assoc]
  rw [hex, ← hp, ← hu]
  exact immediate _ _


lemma root_exists : ∃ b : ℝ, 15213/10000 ≤ b ∧ b ≤ 15214/10000 ∧ b^3=b+2 := by
  let f (x : ℝ) := x^3-x-2
  have h : (0:ℝ) ∈ f '' Set.Icc (15213/10000) (15214/10000) :=
    intermediate_value_Icc (by norm_num) (show ContinuousOn f _ from by fun_prop)
      (by constructor <;> norm_num [f])
  obtain ⟨b,hb,he⟩ := h
  exact ⟨b,hb.1,hb.2,by dsimp [f] at he; linarith⟩

def discrepancy (L : ℝ) (v : List Block) : ℝ :=
  (encode v).length - L*v.length

lemma discrepancy_append (L : ℝ) (u v : List Block) :
    discrepancy L (u++v) = discrepancy L u + discrepancy L v := by
  simp [discrepancy, encode, List.flatMap_append]
  ring

def g (L : ℝ) (n : ℕ) := discrepancy L (tile n [.one])

lemma shiftTile (n m : ℕ) (k : Block) :
    tile (n+m) [k] = tile n (tile m [k]) := by rw [Nat.add_comm, tile_add]

lemma g_recurrence (L : ℝ) (n : ℕ) : g L (n+3) = g L (n+1) + 2*g L n := by
  simp only [g, shiftTile n 3, shiftTile n 1]
  change discrepancy L (tile n ([.one] ++ [.one] ++ [.two])) =
    discrepancy L (tile n [.two]) + 2*discrepancy L (tile n [.one])
  rw [tile_append, tile_append, discrepancy_append, discrepancy_append]
  ring

def E (b a c : ℝ) := c^2 + b*a*c+(b^2-1)*a^2

lemma g_decay {b L : ℝ} (hb : b^3=b+2) (hL : L*(b-1)=b) (hb0 : 3/2 < b) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, |g L n| ≤ C*(4/3)^n := by
  have hbhi : b < 8/5 := by nlinarith [sq_nonneg (b-3/2)]
  have base : g L 2 + b*g L 1 + (b^2-1)*g L 0 = 0 := by
    norm_num [g, discrepancy, tile, sigma, subst, encode, digits]
    apply (mul_eq_zero.mp (show ((4-L)+b*(3-L)+(b^2-1)*(2-L))*(b-1)=0 by
      linear_combination hb - (b+b^2)*hL)).resolve_right (by linarith)

  have recur (n : ℕ) : g L (n+2) + b*g L (n+1) + (b^2-1)*g L n = 0 := by
    induction n with
    | zero => exact base
    | succ n ih =>
      change g L (n+3) + b*g L (n+2) + (b^2-1)*g L (n+1) = 0
      rw [g_recurrence]
      linear_combination b*ih - (g L n)*hb
  have energy (n : ℕ) : E b (g L n) (g L (n+1)) = (b^2-1)^n * E b (g L 0) (g L 1) := by
    induction n with
    | zero => simp
    | succ n ih =>
      have h : g L (n+2) = -b*g L (n+1)-(b^2-1)*g L n := by linarith [recur n]
      change E b (g L (n+1)) (g L (n+2)) = _
      rw [h, pow_succ (b^2-1) n, mul_right_comm ((b^2-1)^n), ← ih]
      simp only [E]
      ring
  have positive (a c : ℝ) : a^2/2 ≤ E b a c := by
    dsimp [E]
    nlinarith [sq_nonneg (c+b*a/2),
      mul_nonneg (sq_nonneg a) (show 0 ≤ 3*b^2/4-3/2 by nlinarith [sq_nonneg (b-3/2)])]
  let C := 2*(E b (g L 0) (g L 1))+1
  have h0 := positive (g L 0) (g L 1)
  have hE0 : 0 ≤ E b (g L 0) (g L 1) := by nlinarith [sq_nonneg (g L 0)]
  refine ⟨C, by dsimp [C]; positivity, fun n => ?_⟩
  have hg := positive (g L n) (g L (n+1))
  rw [energy] at hg
  have hh : (b^2-1)^n ≤ ((4/3:ℝ)^2)^n :=
    pow_le_pow_left₀ (by nlinarith [sq_nonneg (b-3/2)]) (by nlinarith [sq_nonneg (b-8/5)]) _
  have hc : 2*E b (g L 0) (g L 1) ≤ C^2 := by dsimp [C]; nlinarith [sq_nonneg (E b (g L 0) (g L 1))]
  have hm := mul_le_mul_of_nonneg_right hh hE0
  have hm2 := mul_le_mul_of_nonneg_left hc (show 0 ≤ ((4/3:ℝ)^2)^n by positivity)
  rw [← pow_mul, Nat.mul_comm, pow_mul] at hm hm2
  have habs := sq_abs (g L n)
  nlinarith [mul_pow C ((4/3)^n) 2, abs_nonneg (g L n), show 0 ≤ C*(4/3)^n by dsimp [C]; positivity]


def weight (b : ℝ) : Block → ℝ
  | .one => 1
  | .two => b
  | .three => b^2

def mass (b : ℝ) (v : List Block) := (v.map (weight b)).sum

lemma mass_append (b : ℝ) (u v : List Block) : mass b (u++v) = mass b u + mass b v := by
  simp [mass,List.map_append,List.sum_append]

lemma mass_sigma {b : ℝ} (h : b^3=b+2) (v : List Block) : mass b (sigma v)=b*mass b v := by
  induction v with
  | nil => simp [sigma,mass]
  | cons k t ih =>
    change mass b (subst k ++ sigma t) = _
    rw [mass_append,ih]
    cases k <;> simp [mass,weight,subst] <;> nlinarith

lemma mass_tile {b : ℝ} (h : b^3=b+2) (n : ℕ) (v : List Block) :
    mass b (tile n v) = b^n * mass b v := by
  induction n with
  | zero => simp [tile]
  | succ n ih => rw [tile,mass_sigma h,ih,pow_succ]; ring

lemma mass_bound {b : ℝ} (hb : 3/2 ≤ b) (hu : b ≤ 8/5) (v : List Block) :
    mass b v ≤ 3*v.length := by
  have hb2 : b^2 ≤ 3 := by nlinarith [mul_nonneg (by linarith : 0 ≤ 8/5-b) (by linarith : 0 ≤ 8/5+b)]
  induction v with
  | nil => simp [mass]
  | cons k t ih => cases k <;> simp [mass,weight] at * <;> linarith

lemma tile_lower {b : ℝ} (h : b^3=b+2) (hb : 3/2 ≤ b) (hu : b ≤ 8/5) (n : ℕ) (k : Block) :
    (3/2 : ℝ)^n ≤ 3*(tile n [k]).length := by
  have h0 : 1 ≤ mass b [k] := by cases k <;> simp [mass,weight] <;> nlinarith [sq_nonneg (b-1), le_abs_self b]
  have h1 := mass_bound hb hu (tile n [k])
  rw [mass_tile h] at h1
  have h2 : 0 ≤ b^n := pow_nonneg (by linarith) _
  exact (pow_le_pow_left₀ (by norm_num) hb n).trans
    ((le_mul_of_one_le_right h2 h0).trans h1)

lemma tile_error {b L C : ℝ} (h : b^3=b+2) (hb : 3/2 ≤ b) (hu : b ≤ 8/5) (hc : 0 < C)
    (hg : ∀ n : ℕ, |g L n| ≤ C*(4/3)^n) (n : ℕ) (k : Block) :
    |discrepancy L (tile n [k])| ≤ (6*C*(8/9)^n) * (tile n [k]).length := by
  have hh : |discrepancy L (tile n [k])| ≤ 2*C*(4/3)^n := by
    cases k with
    | one => exact (hg n).trans (by nlinarith [show 0 < (4/3:ℝ)^n by positivity])
    | two =>
      have t := hg (n+1)
      rw [g,shiftTile,pow_add] at t
      change |discrepancy L (tile n [.two])| ≤ _ at t
      norm_num at t
      nlinarith [show 0 < C*(4/3:ℝ)^n by positivity]
    | three =>
      have t := hg (n+2)
      rw [g,shiftTile,pow_add] at t
      change |discrepancy L (tile n [.three])| ≤ _ at t
      norm_num at t
      nlinarith [show 0 < C*(4/3:ℝ)^n by positivity]
  have low := tile_lower h hb hu n k
  have hf := mul_le_mul_of_nonneg_left low (show 0 ≤ 2*C*(8/9:ℝ)^n by positivity)
  have hp : ((8/9:ℝ)^n)*(3/2)^n = (4/3)^n := by rw [← mul_pow]; norm_num
  calc
    _ ≤ 2*C*(4/3)^n := hh
    _ = 2*C*(8/9)^n*(3/2)^n := by linear_combination -(2*C)*hp
    _ ≤ _ := by linarith


lemma blockPrefix_split (m k : ℕ) :
    blockPrefix (m+k) = blockPrefix k ++ tile (2*k) (blockPrefix m) := by
  induction k with
  | zero => simp [blockPrefix,tile]
  | succ k ih =>
    change seed ++ tile 2 (blockPrefix (m+k)) =
      (seed ++ tile 2 (blockPrefix k)) ++ tile (2*(k+1)) (blockPrefix m)
    rw [ih,tile_append,← tile_add, Nat.mul_succ,List.append_assoc]

lemma encode_length_bound (v : List Block) : (encode v).length ≤ 4*v.length := by
  induction v with
  | nil => decide
  | cons k t ih => cases k <;> simp [digits,encode] at * <;> omega

lemma discrepancy_bound {L : ℝ} (hl : 0 ≤ L) (hu : L ≤ 4) (v : List Block) :
    |discrepancy L v| ≤ 4*v.length := by
  have h : ((encode v).length : ℝ) ≤ 4*v.length := by exact_mod_cast encode_length_bound v
  rw [abs_le]
  simp only [discrepancy]
  constructor <;> nlinarith [mul_nonneg (show 0 ≤ 4-L by linarith) (Nat.cast_nonneg v.length),
    mul_nonneg hl (Nat.cast_nonneg v.length), (show 0 ≤ ((encode v).length:ℝ) by positivity)]

def maxTile (k : ℕ) :=
  (tile k [.one]).length + (tile k [.two]).length + (tile k [.three]).length

lemma tile_length_bound (k : ℕ) (a : Block) : (tile k [a]).length ≤ maxTile k := by
  cases a <;> dsimp [maxTile] <;> omega

lemma take_tiles {k : ℕ} {e L : ℝ} (he : 0 ≤ e) (hL : 0 ≤ L) (hLu : L ≤ 4)
    (h : ∀ a : Block, |discrepancy L (tile k [a])| ≤ e*(tile k [a]).length)
    (v : List Block) (n : ℕ) :
    |discrepancy L ((tile k v).take n)| ≤ e*((tile k v).take n).length + 4*maxTile k := by
  induction v generalizing n with
  | nil => simp [tile_nil,discrepancy,encode]
  | cons a t ih =>
    have ha : tile k (a::t) = tile k [a] ++ tile k t := tile_append k [a] t
    rw [ha]
    by_cases hn : n ≤ (tile k [a]).length
    · rw [List.take_append_of_le_length hn]
      have hlen : ((tile k [a]).take n).length ≤ maxTile k :=
        (by simp : ((tile k [a]).take n).length ≤ (tile k [a]).length).trans (tile_length_bound _ _)
      have hs := discrepancy_bound hL hLu ((tile k [a]).take n)
      have hh : (((tile k [a]).take n).length : ℝ) ≤ maxTile k := by exact_mod_cast hlen
      nlinarith [mul_nonneg he (Nat.cast_nonneg ((tile k [a]).take n).length)]
    · rw [List.take_append,List.take_of_length_le (Nat.le_of_not_ge hn)]
      rw [discrepancy_append,List.length_append,Nat.cast_add]
      have hb := abs_add_le (discrepancy L (tile k [a])) (discrepancy L ((tile k t).take (n-(tile k [a]).length)))
      linarith [ih (n-(tile k [a]).length),h a]

lemma prefix_error {e L : ℝ} (he : 0 ≤ e) (hL : 0 ≤ L) (hLu : L ≤ 4) (k : ℕ)
    (h : ∀ a : Block, |discrepancy L (tile (2*k) [a])| ≤ e*(tile (2*k) [a]).length) :
    ∃ D : ℝ, ∀ n : ℕ, (blockPrefix k).length ≤ n → |discrepancy L (initial n)| ≤ e*n+D := by
  refine ⟨4*(blockPrefix k).length + 4*maxTile (2*k), fun n hn => ?_⟩
  have hkn : k ≤ n := (prefix_length k).trans hn
  have hs : initial n = blockPrefix k ++ (tile (2*k) (blockPrefix (n-k))).take (n-(blockPrefix k).length) := by
    rw [initial, show n = (n-k)+k from by omega, blockPrefix_split, List.take_append]
    simp only [Nat.sub_add_cancel hkn, List.take_of_length_le hn]
  have hh := congrArg List.length hs
  simp only [initial_length,List.length_append] at hh
  rw [hs,discrepancy_append]
  have hlen : (((tile (2*k) (blockPrefix (n-k))).take (n-(blockPrefix k).length)).length : ℝ) ≤ n := by
    exact_mod_cast (by omega : ((tile (2*k) (blockPrefix (n-k))).take (n-(blockPrefix k).length)).length ≤ n)
  have b := take_tiles he hL hLu h (blockPrefix (n-k)) (n-(blockPrefix k).length)
  have c := discrepancy_bound hL hLu (blockPrefix k)
  have ab := abs_add_le (discrepancy L (blockPrefix k))
    (discrepancy L ((tile (2*k) (blockPrefix (n-k))).take (n-(blockPrefix k).length)))
  linarith [mul_le_mul_of_nonneg_left hlen he]


def charge (w : List Block) : ℤ := 10*(encode w).length - 39*w.length

lemma charge_append (v w : List Block) : charge (v++w) = charge v + charge w := by
  simp [charge,encode,List.flatMap_append]
  ring

private lemma charge_take_all (w : List Block) (b : ℤ)
    (h : ∀ i : Fin (w.length+1), charge (w.take i.val) ≤ b) (n : ℕ) :
    charge (w.take n) ≤ b := by
  by_cases ht : n ≤ w.length
  · exact h ⟨n,by omega⟩
  · simpa [List.take_of_length_le (Nat.le_of_not_ge ht)] using h ⟨w.length,by omega⟩

private lemma right_tile_charge (k : Block) (n : ℕ) :
    charge ((tile 4 [k]).take n) ≤ 3 := by
  apply charge_take_all
  cases k <;> decide

private lemma complete_tile_charge (k : Block) : charge (tile 4 [k]) ≤ 0 := by
  cases k <;> decide

private lemma right_charge (w : List Block) (n : ℕ) : charge ((tile 4 w).take n) ≤ 3 := by
  induction w generalizing n with
  | nil => simp [tile_nil,charge,encode]
  | cons k w ih =>
    change charge ((tile 4 ([k]++w)).take n) ≤ 3
    rw [tile_append]
    by_cases h : n ≤ (tile 4 [k]).length
    · rw [List.take_append_of_le_length h]
      exact right_tile_charge _ _
    · rw [List.take_append,List.take_of_length_le (Nat.le_of_not_ge h),charge_append]
      linarith [ih (n-(tile 4 [k]).length),complete_tile_charge k]

lemma initial_charge (n : ℕ) (hn : 0 < n) : charge (initial n) ≤ -1 := by
  rw [← initial_take (show n ≤ n+2 by omega),blockPrefix_split]
  by_cases h : n ≤ (blockPrefix 2).length
  · rw [List.take_append_of_le_length h]
    have hc : ∀ i : Fin ((blockPrefix 2).length+1), 0 < i.val → charge ((blockPrefix 2).take i.val) ≤ -1 := by
      decide
    exact hc ⟨_,by omega⟩ hn
  · rw [List.take_append,List.take_of_length_le (Nat.le_of_not_ge h),charge_append]
    have hc : charge (blockPrefix 2) ≤ -4 := by decide
    have h' := right_charge (blockPrefix n) (n-(blockPrefix 2).length)
    linarith

lemma encode_length_lower (w : List Block) : 2*w.length ≤ (encode w).length := by
  induction w with
  | nil => decide
  | cons k t ih => cases k <;> simp [encode,digits] at * <;> omega

lemma onePos_bounds (n : ℕ) (hn : 2 ≤ n) :
    2*n ≤ onePos n ∧ 10*onePos n ≤ 39*n := by
  have hc := initial_charge (n-1) (by omega)
  have hl := encode_length_lower (initial (n-1))
  simp only [charge,initial_length] at hc
  simp only [initial_length] at hl
  unfold onePos
  omega


theorem one_limit {b L : ℝ} (hb : b^3=b+2) (hL : L*(b-1)=b)
    (hblo : 3/2 < b) (hbhi : b ≤ 8/5) (hlo : 0 ≤ L) (hhi : L ≤ 4) :
    Tendsto (fun n : ℕ => (onePos n : ℝ)/n) atTop (𝓝 L) := by
  obtain ⟨C,hC,hg⟩ := g_decay hb hL hblo
  apply Metric.tendsto_atTop.mpr
  intro eps heps
  have ht : Tendsto (fun k : ℕ => 6*C*(8/9:ℝ)^k) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 8/9)
      (by norm_num : (8/9:ℝ) < 1)).const_mul (6*C)
  obtain ⟨k,hk⟩ := eventually_atTop.mp (ht.eventually_lt_const (by linarith : 0 < eps/2))
  have tiles (a : Block) : |discrepancy L (tile (2*k) [a])| ≤ eps/2 * (tile (2*k) [a]).length := by
    exact (tile_error hb hblo.le hbhi hC hg (2*k) a).trans <|
      mul_le_mul_of_nonneg_right (hk _ (by omega : k ≤ 2*k)).le (Nat.cast_nonneg _)
  obtain ⟨D,hD⟩ := prefix_error (by positivity) hlo hhi k tiles
  obtain ⟨M,hM⟩ := exists_nat_gt ((D+4+|L|)/(eps/2))
  refine ⟨max (M+1) ((blockPrefix k).length+1), fun n hn => ?_⟩
  have hn0 : 0 < n := by omega
  have hnr : 0 < (n:ℝ) := by exact_mod_cast hn0
  have hMle : (M:ℝ) ≤ n := by exact_mod_cast (by omega : M ≤ n)
  have hc : D+4+|L| < (eps/2)*(n:ℝ) := by
    have hh := (div_lt_iff₀ (by positivity : 0 < eps/2)).mp hM
    nlinarith [mul_le_mul_of_nonneg_left hMle (by positivity : 0 ≤ eps/2)]
  have err := hD (n-1) (by omega)
  simp only [discrepancy, initial_length] at err
  have hn1 : (((n-1:ℕ):ℝ)) = (n:ℝ)-1 := by rw [Nat.cast_sub (by omega : 1 ≤ n)]; norm_num
  rw [hn1] at err
  rw [Real.dist_eq, abs_lt]
  change -eps < (onePos n : ℝ)/n-L ∧ (onePos n : ℝ)/n-L < eps
  have he : ((onePos n : ℕ):ℝ) = 4 + (encode (initial (n-1))).length := by
    simp only [onePos,Nat.cast_add,Nat.cast_ofNat]
  rw [he]
  have hneg := (abs_le.mp err).1
  have hpos := (abs_le.mp err).2
  constructor
  · rw [lt_sub_iff_add_lt,lt_div_iff₀ hnr]
    nlinarith [neg_abs_le L]
  · rw [sub_lt_iff_lt_add,div_lt_iff₀ hnr]
    nlinarith [le_abs_self L]

theorem full_one :
    ∃ a : ℕ → ℕ, (∀ n : ℕ, 1 ≤ n →
      ∀ᶠ t : ℕ in atTop, IsPosition true (word (2*t)) n (a n)) ∧
    ∃ m : ℝ, 291/100 ≤ m ∧ m < 292/100 ∧
      Tendsto (fun n : ℕ => (a n : ℝ)/n) atTop (𝓝 m) ∧
      ∀ n : ℕ, 2 ≤ n → -1 < m - (a n : ℝ)/n ∧ m - (a n : ℝ)/n < 1 := by
  obtain ⟨b,h1,h2,hb⟩ := root_exists
  let L := b/(b-1)
  have hpos : 0 < b-1 := by linarith
  have hL : L*(b-1)=b := div_mul_cancel₀ _ hpos.ne'
  have hL1 : 291/100 < L := by apply (lt_div_iff₀ hpos).mpr; linarith
  have hL2 : L < 292/100 := by apply (div_lt_iff₀ hpos).mpr; linarith
  refine ⟨onePos,position_eventually,L,hL1.le,hL2,one_limit hb hL (by linarith) (by linarith)
    (by linarith) (by linarith),?_⟩
  intro n hn
  have hn0 : 0 < (n:ℝ) := by exact_mod_cast (by omega : 0 < n)
  obtain ⟨lo,hi⟩ := onePos_bounds n hn
  have hlo : (2:ℝ)*n ≤ onePos n := by exact_mod_cast lo
  have hhi : (10:ℝ)*onePos n ≤ 39*n := by exact_mod_cast hi
  have hlo' : (2:ℝ) ≤ onePos n / (n:ℝ) := (le_div_iff₀ hn0).mpr hlo
  have hhi' : (onePos n : ℝ)/n ≤ 39/10 := (div_le_iff₀ hn0).mpr (by linarith)
  constructor <;> linarith

end EvenRewrite

theorem OMA.solution : type_of% @OMA.S_oeis_a288510.main :=
  EvenRewrite.full_one
