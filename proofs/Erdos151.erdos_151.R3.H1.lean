import OMAReductions.R_Erdos151_erdos_151_R3

/-!
# The seven-vertex link extension in Erdős problem 151

The finite criterion and the earlier exhaustive C++ verification are due to
ellisjr in the parent reduction (PR 17956). Here the Lean kernel checks a
finite certificate, including all graph relabellings and exceptional cases.
-/

/-! ## Finite classification of seven-vertex graph masks -/

namespace SevenMasks

/-- The edge (i,j), i<j, occupies bit j*(j-1)/2 + i. -/
def inside (s : Nat) : Nat :=
  (#[0, 0, 0, 1, 0, 2, 4, 7, 0, 8, 16, 25, 32, 42, 52, 63, 0, 64, 128, 193, 256, 322, 388, 455, 512, 584, 656, 729, 800, 874, 948, 1023, 0, 1024, 2048, 3073, 4096, 5122, 6148, 7175, 8192, 9224, 10256, 11289, 12320, 13354, 14388, 15423, 16384, 17472, 18560, 19649, 20736, 21826, 22916, 24007, 25088, 26184, 27280, 28377, 29472, 30570, 31668, 32767, 0, 32768, 65536, 98305, 131072, 163842, 196612, 229383, 262144, 294920, 327696, 360473, 393248, 426026, 458804, 491583, 524288, 557120, 589952, 622785, 655616, 688450, 721284, 754119, 786944, 819784, 852624, 885465, 918304, 951146, 983988, 1016831, 1048576, 1082368, 1116160, 1149953, 1183744, 1217538, 1251332, 1285127, 1318912, 1352712, 1386512, 1420313, 1454112, 1487914, 1521716, 1555519, 1589248, 1623104, 1656960, 1690817, 1724672, 1758530, 1792388, 1826247, 1860096, 1893960, 1927824, 1961689, 1995552, 2029418, 2063284, 2097151] : Array Nat)[s]?.getD 0

def MaxClique (g q : Nat) : Prop :=
  q ≠ 0 ∧ inside q &&& g = inside q ∧
    ∀ v : Fin 7, q.testBit v.val = false →
      inside (q ||| 2^v.val) &&& g ≠ inside (q ||| 2^v.val)

def Indep (r s : Nat) : Prop := inside s &&& r = 0

def Stable (g s : Nat) : Prop :=
  Indep g s ∧ ∀ q < 128, MaxClique g q → s &&& q ≠ 0



/-- Pull back the candidate graph along each of these vertex permutations. -/
def permutations : List (List Nat) := [[1, 0, 2, 3, 4, 5, 6],
  [2, 1, 0, 3, 4, 5, 6],
  [0, 2, 1, 3, 4, 5, 6],
  [3, 1, 2, 0, 4, 5, 6],
  [0, 3, 2, 1, 4, 5, 6],
  [0, 1, 3, 2, 4, 5, 6],
  [4, 1, 2, 3, 0, 5, 6],
  [0, 4, 2, 3, 1, 5, 6],
  [0, 1, 4, 3, 2, 5, 6],
  [0, 1, 2, 4, 3, 5, 6],
  [5, 1, 2, 3, 4, 0, 6],
  [0, 5, 2, 3, 4, 1, 6],
  [0, 1, 5, 3, 4, 2, 6],
  [0, 1, 2, 5, 4, 3, 6],
  [0, 1, 2, 3, 5, 4, 6],
  [6, 1, 2, 3, 4, 5, 0],
  [0, 6, 2, 3, 4, 5, 1],
  [0, 1, 6, 3, 4, 5, 2],
  [0, 1, 2, 6, 4, 5, 3],
  [0, 1, 2, 3, 6, 5, 4],
  [0, 1, 2, 3, 4, 6, 5],
  [0, 3, 4, 1, 2, 6, 5],
  [0, 1, 3, 2, 5, 4, 6],
  [0, 2, 1, 3, 4, 6, 5],
  [0, 2, 1, 3, 5, 4, 6],
  [0, 2, 1, 4, 3, 5, 6],
  [2, 0, 4, 1, 6, 3, 5],
  [3, 1, 6, 0, 4, 5, 2],
  [1, 0, 2, 4, 3, 5, 6],
  [2, 3, 0, 1, 4, 6, 5],
  [6, 3, 5, 4, 2, 0, 1],
  [0, 2, 1, 4, 3, 6, 5],
  [0, 1, 3, 2, 4, 6, 5],
  [0, 1, 4, 5, 2, 3, 6],
  [0, 2, 1, 3, 6, 4, 5],
  [1, 0, 2, 3, 5, 4, 6]]
def permutationsE : List (List Nat) := [[0, 2, 1, 4, 3, 5, 7, 6, 8, 9, 11, 10, 12, 13, 14, 16, 15, 17, 18, 19, 20],
  [2, 1, 0, 5, 4, 3, 8, 7, 6, 9, 12, 11, 10, 13, 14, 17, 16, 15, 18, 19, 20],
  [1, 0, 2, 3, 5, 4, 6, 8, 7, 9, 10, 12, 11, 13, 14, 15, 17, 16, 18, 19, 20],
  [4, 5, 2, 3, 0, 1, 9, 7, 8, 6, 13, 11, 12, 10, 14, 18, 16, 17, 15, 19, 20],
  [3, 1, 5, 0, 4, 2, 6, 9, 8, 7, 10, 13, 12, 11, 14, 15, 18, 17, 16, 19, 20],
  [0, 3, 4, 1, 2, 5, 6, 7, 9, 8, 10, 11, 13, 12, 14, 15, 16, 18, 17, 19, 20],
  [7, 8, 2, 9, 4, 5, 6, 0, 1, 3, 14, 11, 12, 13, 10, 19, 16, 17, 18, 15, 20],
  [6, 1, 8, 3, 9, 5, 0, 7, 2, 4, 10, 14, 12, 13, 11, 15, 19, 17, 18, 16, 20],
  [0, 6, 7, 3, 4, 9, 1, 2, 8, 5, 10, 11, 14, 13, 12, 15, 16, 19, 18, 17, 20],
  [0, 1, 2, 6, 7, 8, 3, 4, 5, 9, 10, 11, 12, 14, 13, 15, 16, 17, 19, 18, 20],
  [11, 12, 2, 13, 4, 5, 14, 7, 8, 9, 10, 0, 1, 3, 6, 20, 16, 17, 18, 19, 15],
  [10, 1, 12, 3, 13, 5, 6, 14, 8, 9, 0, 11, 2, 4, 7, 15, 20, 17, 18, 19, 16],
  [0, 10, 11, 3, 4, 13, 6, 7, 14, 9, 1, 2, 12, 5, 8, 15, 16, 20, 18, 19, 17],
  [0, 1, 2, 10, 11, 12, 6, 7, 8, 14, 3, 4, 5, 13, 9, 15, 16, 17, 20, 19, 18],
  [0, 1, 2, 3, 4, 5, 10, 11, 12, 13, 6, 7, 8, 9, 14, 15, 16, 17, 18, 20, 19],
  [16, 17, 2, 18, 4, 5, 19, 7, 8, 9, 20, 11, 12, 13, 14, 15, 0, 1, 3, 6, 10],
  [15, 1, 17, 3, 18, 5, 6, 19, 8, 9, 10, 20, 12, 13, 14, 0, 16, 2, 4, 7, 11],
  [0, 15, 16, 3, 4, 18, 6, 7, 19, 9, 10, 11, 20, 13, 14, 1, 2, 17, 5, 8, 12],
  [0, 1, 2, 15, 16, 17, 6, 7, 8, 19, 10, 11, 12, 20, 14, 3, 4, 5, 18, 9, 13],
  [0, 1, 2, 3, 4, 5, 15, 16, 17, 18, 10, 11, 12, 13, 20, 6, 7, 8, 9, 19, 14],
  [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 15, 16, 17, 18, 19, 10, 11, 12, 13, 14, 20],
  [3, 6, 9, 0, 4, 7, 1, 5, 8, 2, 15, 18, 19, 16, 17, 10, 13, 14, 11, 12, 20],
  [0, 3, 4, 1, 2, 5, 10, 11, 13, 12, 6, 7, 9, 8, 14, 15, 16, 18, 17, 20, 19],
  [1, 0, 2, 3, 5, 4, 6, 8, 7, 9, 15, 17, 16, 18, 19, 10, 12, 11, 13, 14, 20],
  [1, 0, 2, 3, 5, 4, 10, 12, 11, 13, 6, 8, 7, 9, 14, 15, 17, 16, 18, 20, 19],
  [1, 0, 2, 6, 8, 7, 3, 5, 4, 9, 10, 12, 11, 14, 13, 15, 17, 16, 19, 18, 20],
  [4, 0, 3, 11, 13, 10, 2, 5, 1, 12, 16, 18, 15, 20, 17, 7, 9, 6, 14, 8, 19],
  [4, 18, 16, 3, 0, 15, 9, 7, 19, 6, 13, 11, 20, 10, 14, 5, 2, 17, 1, 8, 12],
  [0, 2, 1, 7, 6, 8, 4, 3, 5, 9, 11, 10, 12, 14, 13, 16, 15, 17, 19, 18, 20],
  [5, 1, 3, 2, 4, 0, 8, 9, 6, 7, 17, 18, 15, 16, 19, 12, 13, 10, 11, 14, 20],
  [20, 14, 19, 11, 16, 7, 13, 18, 9, 4, 12, 17, 8, 2, 5, 10, 15, 6, 0, 3, 1],
  [1, 0, 2, 6, 8, 7, 3, 5, 4, 9, 15, 17, 16, 19, 18, 10, 12, 11, 14, 13, 20],
  [0, 3, 4, 1, 2, 5, 6, 7, 9, 8, 15, 16, 18, 17, 19, 10, 11, 13, 12, 14, 20],
  [0, 6, 7, 10, 11, 14, 1, 2, 8, 12, 3, 4, 9, 13, 5, 15, 16, 19, 20, 17, 18],
  [1, 0, 2, 3, 5, 4, 10, 12, 11, 13, 15, 17, 16, 18, 20, 6, 8, 7, 9, 14, 19],
  [0, 2, 1, 4, 3, 5, 11, 10, 12, 13, 7, 6, 8, 9, 14, 16, 15, 17, 18, 20, 19]]
def exceptions : List Nat := [236, 1260, 3308, 3948, 7916, 34028, 35052, 35185, 36076, 36274, 36716, 36724, 39584, 39585, 39587, 39657, 40684, 101612, 101740, 102252, 104012, 104020, 104022, 104052, 104096, 104100, 104108, 104156, 104172, 104177, 104180, 106208, 106209, 106220, 106353, 106354, 112468, 112492, 112500, 128876, 128884, 237292, 241524, 255574, 255655, 255662, 257772, 257905, 515820]

-- Each integer represents a column of a truth table; each row represents a graph.
def top (width : Nat) := 2^(2^width)-1
def col (width hi j : Nat) :=
  if j < width then (top width / (2^(2^j)+1)) <<< 2^j
  else if hi.testBit (j-width) then top width else 0
def allOf (U : Nat) (xs : List Nat) (f : Nat → Nat) :=
  xs.foldl (fun acc x => acc &&& f x) U
def anyOf (xs : List Nat) (f : Nat → Nat) :=
  xs.foldl (fun acc x => acc ||| f x) 0
def present (m : Nat) := (List.range 21).filter m.testBit

def cliqueWord (w p s : Nat) := allOf (top w) (present (inside s)) (col w p)
def indepWord (w p s : Nat) := top w ^^^ anyOf (present (inside s)) (col w p)
def maxWord (w p s : Nat) :=
  cliqueWord w p s &&&
    (top w ^^^ anyOf ((List.range 7).filter fun v => !s.testBit v)
      (fun v => cliqueWord w p (s ||| 2^v)))
def stableWord (w p s : Nat) :=
  indepWord w p s &&&
    (top w ^^^ anyOf ((List.range 127).map Nat.succ |>.filter fun q => s &&& q == 0)
      (maxWord w p))
def dropWord (w p : Nat) (perm : List Nat) :=
  (List.range 21).foldl (fun acc j =>
    let x := col w p j
    let y := col w p (perm[j]?.getD 21)
    (x &&& (top w ^^^ y)) ||| ((top w ^^^ (x ^^^ y)) &&& acc)) 0

def knownWord (w p : Nat) :=
  anyOf (exceptions.filter fun g => g >>> w == p) (fun g => 2^(g % (2^w)))
def coveredWord (w p : Nat) :=
  (permutationsE.foldl (fun acc e => acc ||| dropWord w p e) 0) |||
    anyOf (List.range 128) (stableWord w p) ||| knownWord w p


private def rawCol : Nat → Nat → Nat
  | 0, _ => 0
  | w+1, j => if w=j then top w <<< 2^w else
      rawCol w j * (1 + 2^(2^w))

private theorem rawCol_bound (w j : Nat) : rawCol w j < 2^(2^w) := by
  induction w with
  | zero => simp [rawCol]
  | succ w ih =>
    have hp : 0 < 2^(2^w) := by positivity
    rw [rawCol, pow_succ 2 w, show 2^w * 2 = 2^w + 2^w by omega, pow_add]
    split
    · rw [Nat.shiftLeft_eq, top]; exact Nat.mul_lt_mul_of_pos_right (by omega) hp
    · have h : rawCol w j ≤ 2^(2^w)-1 := by omega
      calc rawCol w j * (1+2^(2^w)) ≤ (2^(2^w)-1) * (1+2^(2^w)) := Nat.mul_le_mul_right _ h
           _ < _ := by nlinarith [Nat.sub_add_cancel (by omega : 1 ≤ 2^(2^w))]

private theorem raw_fold (w j i : Nat) :
    (rawCol w j * (1+2^(2^w))).testBit i =
      if i < 2^w then (rawCol w j).testBit i else (rawCol w j).testBit (i-2^w) := by
  rw [show rawCol w j * (1+2^(2^w)) = 2^(2^w)*rawCol w j + rawCol w j by ring,
    Nat.testBit_two_pow_mul_add _ (rawCol_bound w j)]

private theorem rawCol_at (w j i : Nat) (hj : j < w) (hi : i < 2^w) :
    (rawCol w j).testBit i = i.testBit j := by
  induction w generalizing i with
  | zero => omega
  | succ w ih =>
    rw [rawCol]
    by_cases h : i < 2^w
    · by_cases k : w=j
      · subst j
        simp [Nat.testBit_shiftLeft, Nat.not_le.mpr h, Nat.testBit_lt_two_pow h]
      · have hjw : j < w := by omega
        simp [k, raw_fold, h, ih i hjw h]
    · have le : 2^w ≤ i := by omega
      have small : i-2^w < 2^w := by rw [pow_succ] at hi; omega
      have hform : i = 2^w + (i-2^w) := by omega
      by_cases k : w=j
      · subst j
        simp only [if_true, Nat.testBit_shiftLeft, decide_eq_true le, Bool.true_and,
          top, Nat.testBit_two_pow_sub_one, decide_eq_true small]
        conv_rhs => rw [hform, Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow small]
        rfl
      · have hjw : j < w := by omega
        simp only [if_neg k, raw_fold, if_neg h]
        rw [ih _ hjw small]
        conv_rhs => rw [hform, Nat.testBit_two_pow_add_gt hjw]

private theorem columns_match : ∀ j : Fin 21, col 21 0 j = rawCol 21 j := by decide +kernel

private theorem col_at {i j : Nat} (hi : i < 2^21) (hj : j < 21) :
    (col 21 0 j).testBit i = i.testBit j := by
  rw [columns_match ⟨j,hj⟩, rawCol_at _ _ _ hj hi]

private theorem all_at_aux (xs : List Nat) (f : Nat → Nat) (u i : Nat) :
    (xs.foldl (fun acc x => acc &&& f x) u).testBit i = true ↔
      u.testBit i = true ∧ ∀ x ∈ xs, (f x).testBit i = true := by
  induction xs generalizing u with
  | nil => simp
  | cons x xs ih => simp [ih, and_assoc]

private theorem any_at_aux {α : Type} (xs : List α) (f : α → Nat) (u i : Nat) :
    (xs.foldl (fun acc x => acc ||| f x) u).testBit i = true ↔
      u.testBit i = true ∨ ∃ x ∈ xs, (f x).testBit i = true := by
  induction xs generalizing u with
  | nil => simp
  | cons x xs ih => simp [ih, or_assoc]

private theorem top_at {w i : Nat} (hi : i < 2^w) : (top w).testBit i = true :=
  (Nat.testBit_two_pow_sub_one (2^w) i).trans (decide_eq_true hi)

private theorem all_at (xs : List Nat) (f : Nat → Nat) {i : Nat} (hi : i<2^21) :
    (allOf (top 21) xs f).testBit i = true ↔ ∀ x ∈ xs, (f x).testBit i = true := by
  simp only [allOf, all_at_aux, top_at hi, true_and]

private theorem any_at (xs : List Nat) (f : Nat → Nat) (i : Nat) :
    (anyOf xs f).testBit i = true ↔ ∃ x ∈ xs, (f x).testBit i = true := by
  simp only [anyOf, any_at_aux, Nat.zero_testBit, Bool.false_eq_true, false_or]
private theorem inside_small_fin : ∀ q : Fin 128, inside q < 2^21 := by decide +kernel

private theorem inside_small (q : Nat) : inside q < 2^21 := by
  by_cases h : q < 128
  · exact inside_small_fin ⟨q,h⟩
  · unfold inside
    rw [getElem?_neg]
    · decide
    · exact h

private theorem incl_bits {m g : Nat} (hm : m < 2^21) :
    (∀ j ∈ present m, g.testBit j = true) ↔ m &&& g = m := by
  constructor
  · intro h
    apply Nat.eq_of_testBit_eq
    intro j
    by_cases hmj : m.testBit j = true
    · have hj : j < 21 := by
        by_contra! fail
        have : m < 2^j := lt_of_lt_of_le hm (Nat.pow_le_pow_right (by decide) fail)
        simp [Nat.testBit_lt_two_pow this] at hmj
      have := h j (by simp [present,hj,hmj])
      simp [hmj,this]
    · simp [hmj]
  · intro eqn j hj
    have hjm : m.testBit j = true := by simpa [present] using (List.mem_filter.mp hj).2
    have := congrArg (fun a : Nat => a.testBit j) eqn
    simpa [hjm] using this

private theorem disj_bits {m g : Nat} (hm : m < 2^21) :
    (¬ ∃ j ∈ present m, g.testBit j = true) ↔ m &&& g = 0 := by
  constructor
  · intro h
    apply Nat.eq_of_testBit_eq
    intro j
    by_cases hmj : m.testBit j = true
    · have hj : j < 21 := by
        by_contra! fail
        have : m < 2^j := lt_of_lt_of_le hm (Nat.pow_le_pow_right (by decide) fail)
        simp [Nat.testBit_lt_two_pow this] at hmj
      have ng : ¬g.testBit j = true := fun hg => h ⟨j,by simp [present,hj,hmj],hg⟩
      simp [hmj,ng]
    · simp [hmj]
  · intro eqn ⟨j,hj,hg⟩
    have hjm : m.testBit j = true := (List.mem_filter.mp hj).2
    have := congrArg (fun a : Nat => a.testBit j) eqn
    simp [hjm,hg] at this

private theorem clique_at {g : Nat} (hg : g<2^21) (q : Nat) :
    (cliqueWord 21 0 q).testBit g = true ↔ inside q &&& g = inside q := by
  rw [cliqueWord, all_at _ _ hg, ← incl_bits (inside_small q)]
  apply forall_congr'; intro j
  apply forall_congr'; intro hj
  rw [col_at hg (List.mem_range.mp (List.mem_filter.mp hj).1)]

private theorem indep_at {g : Nat} (hg : g<2^21) (s : Nat) :
    (indepWord 21 0 s).testBit g = true ↔ Indep g s := by
  rw [indepWord, Nat.testBit_xor]
  simp only [top_at hg, Bool.true_xor,
    Bool.not_eq_true']
  rw [← Bool.not_eq_true, any_at, Indep, ← disj_bits (inside_small s)]
  apply not_congr; apply exists_congr; intro j
  constructor <;> rintro ⟨hj,H⟩ <;> refine ⟨hj,?_⟩
  · rwa [col_at hg (List.mem_range.mp (List.mem_filter.mp hj).1)] at H
  · rwa [col_at hg (List.mem_range.mp (List.mem_filter.mp hj).1)]

private theorem max_at {g : Nat} (hg : g<2^21) (q : Nat) (hpos : q≠0) :
    (maxWord 21 0 q).testBit g = true ↔ MaxClique g q := by
  simp only [maxWord, Nat.testBit_and, Bool.and_eq_true, clique_at hg, Nat.testBit_xor,
    top_at hg, Bool.true_xor,
    Bool.not_eq_true', ← Bool.not_eq_true, any_at, MaxClique]
  constructor
  · rintro ⟨hc,hn⟩
    refine ⟨hpos,hc,?_⟩
    intro v hv hcl
    exact hn ⟨v.val, by simp [hv], hcl⟩
  · rintro ⟨_,hc,hn⟩
    refine ⟨hc,?_⟩
    rintro ⟨v,hv,hcl⟩
    simp only [List.mem_filter,List.mem_range,Bool.not_eq_true'] at hv
    exact hn ⟨v,hv.1⟩ (by simpa using hv.2) hcl

private theorem stable_at {g : Nat} (hg : g<2^21) (s : Nat) :
    (stableWord 21 0 s).testBit g = true ↔ Stable g s := by
  simp only [stableWord, Nat.testBit_and, Bool.and_eq_true, indep_at hg, Nat.testBit_xor,
    top_at hg, Bool.true_xor,
    Bool.not_eq_true', ← Bool.not_eq_true, any_at, Stable]
  refine and_congr_right (fun _ => ?_)
  constructor
  · intro h q hq hmax hdisj
    have h0 := hmax.1
    have hmem : q ∈ (List.range 127).map Nat.succ := by
      exact List.mem_map.mpr ⟨q-1,List.mem_range.mpr (by omega), by omega⟩
    exact h ⟨q, List.mem_filter.mpr ⟨hmem,by simp [hdisj]⟩, (max_at hg q h0).2 hmax⟩
  · rintro h ⟨q,hq,hmax⟩
    rcases List.mem_filter.mp hq with ⟨hmem,hd⟩
    rcases List.mem_map.mp hmem with ⟨k,hk,rfl⟩
    exact h _ (by have := List.mem_range.mp hk; omega) ((max_at hg _ (by omega)).1 hmax)
      (beq_iff_eq.mp hd)
private theorem mod_next_bit (x j : Nat) :
    x % 2^(j+1) = x % 2^j + (if x.testBit j then 2^j else 0) := by
  rw [Nat.mod_pow_succ, Nat.testBit_eq_decide_div_mod_eq]
  have h := Nat.mod_lt (x / 2^j) (by decide : 0 < 2)
  by_cases b : x / 2^j % 2 = 1
  · simp [b]
  · simp [show x / 2^j % 2 = 0 by omega]

private theorem next_lt_bit (g h j : Nat) :
    ((g.testBit j && !h.testBit j) ||
     (!(g.testBit j ^^ h.testBit j) && decide (h % 2^j < g % 2^j))) =
        decide (h % 2^(j+1) < g % 2^(j+1)) := by
  rw [mod_next_bit, mod_next_bit]
  have hg := Nat.mod_lt g (by positivity : 0 < 2^j)
  have hh := Nat.mod_lt h (by positivity : 0 < 2^j)
  cases g.testBit j <;> cases h.testBit j <;> simp <;> omega

private theorem perm_index_bound :
    ∀ e ∈ permutationsE, ∀ k : Fin 21, e[k.val]?.getD 21 < 21 := by
  intro e he
  have h : permutationsE.all (fun el =>
      (List.range 21).all (fun k => decide (el[k]?.getD 21 < 21))) = true := by decide +kernel
  intro k
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp h e he) k.val
    (List.mem_range.mpr k.isLt))

theorem no_drop (g h : Nat) (hg : g<2^21) (hh : h<2^21) (hle : g≤h)
    (e : List Nat) (he : e ∈ permutationsE)
    (bits : ∀ k : Fin 21, h.testBit k.val = g.testBit (e[k.val]?.getD 21)) :
    (dropWord 21 0 e).testBit g = false := by
  let step := fun (acc j : Nat) =>
    let x := col 21 0 j
    let y := col 21 0 (e[j]?.getD 21)
    (x &&& (top 21 ^^^ y)) ||| ((top 21 ^^^ (x ^^^ y)) &&& acc)
  have comp (j : Nat) (hj : j ≤ 21) :
      ((List.range j).foldl step 0).testBit g = decide (h % 2^j < g % 2^j) := by
    induction j with
    | zero => simp [Nat.mod_one]
    | succ j ih =>
      have hj' : j < 21 := by omega
      rw [List.range_succ, List.foldl_append]
      have bc : g.testBit (e[j]?.getD 21) = h.testBit j := (bits ⟨j,hj'⟩).symm
      have hb : e[j]?.getD 21 < 21 := perm_index_bound e he ⟨j,hj'⟩
      simp only [List.foldl_cons, List.foldl_nil, step, Nat.testBit_or, Nat.testBit_and,
        Nat.testBit_xor, col_at hg hj', col_at hg hb, bc, ih (by omega)]
      have ht : (top 21).testBit g = true := by
        simpa only [top, Nat.testBit_two_pow_sub_one, decide_eq_true_eq] using hg
      simpa only [ht, Bool.true_xor, Fin.val_mk] using next_lt_bit g h j
  change ((List.range 21).foldl step 0).testBit g = false
  simpa only [Nat.mod_eq_of_lt hg, Nat.mod_eq_of_lt hh, Nat.not_lt.mpr hle, decide_false]
    using comp 21 (by decide)
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
private theorem sieve_all : coveredWord 21 0 = top 21 := by decide +kernel

theorem classified (g : Nat) (hg : g < 2^21)
    (hc : ∀ e ∈ permutationsE, ∃ h, g ≤ h ∧ h < 2^21 ∧
      ∀ k : Fin 21, h.testBit k.val = g.testBit (e[k.val]?.getD 21)) :
    (∃ s < 128, Stable g s) ∨ g ∈ exceptions := by
  have H : (coveredWord 21 0).testBit g = true := by
    rw [sieve_all]
    exact top_at hg
  simp only [coveredWord, Nat.testBit_or, Bool.or_eq_true] at H
  rcases H with (hD | hA) | hK
  · have dropped := (any_at_aux permutationsE (dropWord 21 0) 0 g).mp hD
    obtain ⟨e, he, hd⟩ := dropped.resolve_left (by simp)
    obtain ⟨h, hle, hh, bits⟩ := hc e he
    rw [no_drop g h hg hh hle e he bits] at hd
    contradiction
  · obtain ⟨s, hs, ha⟩ := (any_at (List.range 128) (stableWord 21 0) g).mp hA
    exact Or.inl ⟨s, List.mem_range.mp hs, (stable_at hg s).1 ha⟩
  · right
    change (anyOf (exceptions.filter fun x => x >>> 21 == 0)
      (fun x => 2 ^ (x % 2^21))).testBit g = true at hK
    obtain ⟨x, hx, xe⟩ := (any_at _ _ g).mp hK
    have hxmem := (List.mem_filter.mp hx).1
    have hquot := beq_iff_eq.mp (List.mem_filter.mp hx).2
    rw [Nat.shiftRight_eq_div_pow] at hquot
    have hlt : x < 2^21 := (Nat.div_eq_zero_iff.mp hquot).resolve_left (by decide)
    have xeq : x % 2^21 = g := of_decide_eq_true ((Nat.testBit_two_pow).symm.trans xe)
    have xg : x = g := (Nat.mod_eq_of_lt hlt).symm.trans xeq
    exact xg ▸ hxmem

end SevenMasks

/-! ## Decision trees for the exceptional graphs -/

namespace SevenMasks

/-- Vertex masks of triples of distinct vertices. -/
def triples : List Nat := [7,11,13,14,19,21,22,25,26,28,35,37,38,41,42,44,49,50,52,56,67,69,70,73,74,76,81,82,84,88,97,98,100,104,112]

def Extends (g r : Nat) : Prop :=
  ∃ s < 128, Indep r s ∧
    ∀ q < 128, MaxClique g q → s &&& q ≠ 0 ∨ inside q &&& r ≠ 0

private inductive RedTree where
  | pick (s : Nat)
  | triangle (q : Nat)
  | split (i : Nat) (blue red : RedTree)

private def testMax (g q : Nat) : Bool :=
  q != 0 && (inside q &&& g == inside q) &&
    (List.range 7).all (fun i => q.testBit i || (inside (q ||| 2^i) &&& g != inside (q ||| 2^i)))

private theorem testMax_of {g q : Nat} (h : MaxClique g q) : testMax g q = true := by
  simp only [testMax, Bool.and_eq_true, bne_iff_ne, beq_iff_eq, List.all_eq_true,
    List.mem_range, Bool.or_eq_true]
  refine ⟨⟨h.1, h.2.1⟩, fun i hi => ?_⟩
  cases hb : q.testBit i with
  | false => exact Or.inr (h.2.2 ⟨i,hi⟩ hb)
  | true => exact Or.inl rfl

/-- The two masks store the edges that have already been found red and blue.
At a leaf the same vertex set works for every completion of those colors. -/
private def testTree (g : Nat) (qs : List Nat) : RedTree → Nat → Nat → Bool
  | .pick s, lo, blue =>
    decide (s < 128) && (inside s &&& g &&& blue == inside s &&& g) &&
      qs.all (fun q => (s &&& q != 0) || (inside q &&& lo != 0))
  | .triangle q, lo, _ => triples.contains q && (inside q &&& lo == inside q)
  | .split i off on, lo, blue =>
    testTree g qs off lo (blue ||| 2^i) && testTree g qs on (lo ||| 2^i) blue

private def verifies (g : Nat) (t : RedTree) : Bool :=
  testTree g ((List.range 128).filter (testMax g)) t 0 0

private theorem trim_blue {x g r blue : Nat} (h : x &&& g &&& blue = x &&& g)
    (hg : r &&& g = r) (hb : blue &&& r = 0) : x &&& r = 0 := by
  calc
    x &&& r = (x &&& g) &&& r := by rw [Nat.and_assoc, Nat.and_comm g r, hg]
    _ = (x &&& g &&& blue) &&& r := by rw [h]
    _ = 0 := by rw [Nat.and_assoc (x &&& g), hb, Nat.and_zero]

private theorem trim_red {x lo r : Nat} (hr : lo &&& r = lo) :
    x &&& lo &&& r = x &&& lo := by rw [Nat.and_assoc, hr]

private theorem tree_sound {g r : Nat} (hg : r &&& g = r)
    (ht : ∀ q ∈ triples, inside q &&& r ≠ inside q)
    {qs : List Nat} (hq : ∀ q < 128, MaxClique g q → q ∈ qs)
    (t : RedTree) (lo blue : Nat) (hl : lo &&& r = lo) (hb : blue &&& r = 0)
    (h : testTree g qs t lo blue = true) : Extends g r := by
  induction t generalizing lo blue with
  | pick s =>
    simp only [testTree, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true,
      Bool.or_eq_true, bne_iff_ne] at h
    refine ⟨s,h.1.1,trim_blue h.1.2 hg hb,?_⟩
    intro q hq' hm
    rcases h.2 q (hq q hq' hm) with hit | red
    · exact Or.inl hit
    · right
      intro hz
      apply red
      rw [← trim_red (x := inside q) hl, Nat.and_right_comm (inside q), hz, Nat.zero_and]
  | triangle q =>
    simp only [testTree, Bool.and_eq_true, List.contains_iff_mem, beq_iff_eq] at h
    apply (ht q h.1 ?_).elim
    simpa only [h.2] using (trim_red (x := inside q) hl)
  | split i off on ih₀ ih₁ =>
    simp only [testTree, Bool.and_eq_true] at h
    obtain ⟨h₀,h₁⟩ := h
    cases hi : r.testBit i with
    | false =>
      apply ih₀ lo (blue ||| 2^i) hl _ h₀
      simp [Nat.and_or_distrib_right, hb, Nat.two_pow_and, hi]
    | true =>
      apply ih₁ (lo ||| 2^i) blue _ hb h₁
      simp [Nat.and_or_distrib_right, hl, Nat.two_pow_and, hi]

private theorem verifies_sound {g r : Nat} (hg : r &&& g = r)
    (ht : ∀ q ∈ triples, inside q &&& r ≠ inside q) {t : RedTree}
    (hv : verifies g t = true) : Extends g r := by
  apply tree_sound hg ht (qs := (List.range 128).filter (testMax g)) _ t 0 0 (by simp) (by simp) hv
  exact fun q hq hm => List.mem_filter.mpr ⟨List.mem_range.mpr hq,testMax_of hm⟩

end SevenMasks

namespace SevenMasks

/-- The 49 seven-vertex graph representatives without a stable transversal. -/
def exceptionalMasks : List Nat := [236, 1260, 3308, 3948, 7916, 34028, 35052, 35185, 36076, 36274, 36716, 36724, 39584, 39585, 39587, 39657, 40684, 101612, 101740, 102252, 104012, 104020, 104022, 104052, 104096, 104100, 104108, 104156, 104172, 104177, 104180, 106208, 106209, 106220, 106353, 106354, 112468, 112492, 112500, 128876, 128884, 237292, 241524, 255574, 255655, 255662, 257772, 257905, 515820]

private def redCertificates : List (Nat × RedTree) := [
  (236, (.split 2 (.pick 103) (.pick 120))),
  (1260, (.split 2 (.pick 71) (.pick 120))),
  (3308, (.split 2 (.pick 71) (.pick 120))),
  (3948, (.split 2 (.pick 71) (.pick 104))),
  (7916, (.split 2 (.pick 71) (.split 3 (.pick 75) (.split 6 (.pick 85) (.split 11 (.pick 106) (.split 12 (.pick 116) (.triangle 38))))))),
  (34028, (.split 2 (.pick 7) (.pick 120))),
  (35052, (.split 2 (.pick 7) (.pick 120))),
  (35185, (.split 0 (.pick 7) (.pick 120))),
  (36076, (.split 2 (.pick 7) (.pick 120))),
  (36274, (.split 1 (.pick 7) (.pick 120))),
  (36716, (.split 2 (.pick 7) (.pick 104))),
  (36724, (.split 2 (.pick 7) (.pick 112))),
  (39584, (.split 5 (.pick 15) (.pick 49))),
  (39585, (.split 12 (.pick 53) (.pick 74))),
  (39587, (.split 9 (.pick 57) (.pick 70))),
  (39657, (.split 0 (.pick 7) (.pick 104))),
  (40684, (.split 2 (.pick 7) (.split 3 (.pick 11) (.split 6 (.pick 21) (.split 11 (.pick 106) (.split 12 (.pick 116) (.triangle 38))))))),
  (101612, (.split 2 (.pick 7) (.pick 120))),
  (101740, (.split 2 (.pick 7) (.pick 120))),
  (102252, (.split 2 (.pick 7) (.pick 104))),
  (104012, (.split 2 (.pick 7) (.pick 104))),
  (104020, (.split 15 (.pick 77) (.pick 50))),
  (104022, (.split 4 (.pick 11) (.pick 84))),
  (104052, (.split 16 (.pick 114) (.split 5 (.pick 13) (.pick 112)))),
  (104096, (.split 5 (.pick 15) (.pick 112))),
  (104100, (.split 10 (.pick 43) (.pick 84))),
  (104108, (.split 15 (.pick 85) (.pick 42))),
  (104156, (.split 2 (.pick 7) (.pick 104))),
  (104172, (.split 2 (.pick 7) (.split 16 (.pick 106) (.split 6 (.pick 21) (.split 12 (.pick 116) (.split 3 (.pick 11) (.split 9 (.pick 120) (.triangle 25)))))))),
  (104177, (.split 0 (.pick 7) (.pick 40))),
  (104180, (.split 2 (.pick 7) (.pick 112))),
  (106208, (.split 5 (.pick 15) (.pick 112))),
  (106209, (.split 5 (.pick 13) (.pick 112))),
  (106220, (.split 2 (.pick 7) (.split 3 (.pick 11) (.split 12 (.pick 116) (.split 9 (.pick 120) (.split 5 (.split 10 (.split 7 (.split 15 (.split 6 (.pick 85) (.triangle 25)) (.split 11 (.pick 42) (.triangle 38))) (.pick 104)) (.pick 84)) (.pick 3))))))),
  (106353, (.split 0 (.pick 7) (.split 5 (.pick 13) (.split 8 (.pick 22) (.split 10 (.pick 41) (.split 11 (.pick 50) (.triangle 35))))))),
  (106354, (.split 1 (.pick 7) (.pick 104))),
  (112468, (.split 15 (.pick 77) (.pick 50))),
  (112492, (.split 2 (.pick 7) (.pick 72))),
  (112500, (.split 2 (.pick 7) (.pick 112))),
  (128876, (.split 2 (.pick 7) (.pick 72))),
  (128884, (.split 2 (.pick 7) (.pick 80))),
  (237292, (.split 2 (.pick 7) (.split 3 (.pick 11) (.split 6 (.pick 21) (.split 9 (.pick 120) (.triangle 25)))))),
  (241524, (.split 2 (.pick 7) (.pick 9))),
  (255574, (.split 4 (.pick 11) (.pick 20))),
  (255655, (.split 0 (.pick 11) (.split 1 (.pick 21) (.split 9 (.pick 25) (.split 2 (.pick 38) (.triangle 7)))))),
  (255662, (.split 3 (.pick 11) (.pick 20))),
  (257772, (.split 2 (.pick 7) (.split 3 (.pick 11) (.split 6 (.pick 21) (.split 10 (.pick 37) (.split 16 (.pick 74) (.split 17 (.pick 84) (.triangle 70)))))))),
  (257905, (.split 5 (.pick 13) (.pick 96))),
  (515820, (.split 2 (.pick 7) (.pick 40)))]

private theorem all_verified :
    redCertificates.all (fun pair => verifies pair.1 pair.2) = true := by decide +kernel

/-- Local extension for the exceptional graph representatives. -/
theorem exceptional_extends {g r : Nat} (he : g ∈ exceptionalMasks) (hg : r &&& g = r)
    (ht : ∀ q ∈ triples, inside q &&& r ≠ inside q) : Extends g r := by
  have hk : redCertificates.map Prod.fst = exceptionalMasks := by decide
  rw [← hk] at he
  obtain ⟨pair,hpair,hg'⟩ := List.mem_map.mp he
  cases pair with
  | mk g' t =>
    change g' = g at hg'
    subst g'
    exact verifies_sound hg ht (List.all_eq_true.mp all_verified (g,t) hpair)

end SevenMasks

/-! ## Vertex masks and finite sets -/

namespace SevenMasks

open Finset

def vset (s : ℕ) : Finset (Fin 7) :=
  univ.filter (fun i => s.testBit i.val)

@[simp] theorem mem_vset (s : ℕ) (i : Fin 7) :
    i ∈ vset s ↔ s.testBit i.val = true := by
  simp [vset]

theorem vset_or_single (s : ℕ) (v : Fin 7) :
    vset (s ||| 2 ^ v.val) = insert v (vset s) := by
  ext i
  by_cases h : i = v
  · subst i
    simp [Nat.testBit_or]
  · have hv : v.val ≠ i.val := fun e => h (Fin.ext e.symm)
    simp [Nat.testBit_or, h, hv]

theorem exists_vset (q : Finset (Fin 7)) : ∃ s < 128, q = vset s := by
  induction q using Finset.induction_on with
  | empty => exact ⟨0, by decide, by simp [vset]⟩
  | insert v q _ ih =>
      obtain ⟨s, hs, rfl⟩ := ih
      exact ⟨s ||| 2 ^ v.val, show s ||| 2 ^ v.val < 2 ^ 7 from
        Nat.or_lt_two_pow hs (Nat.pow_lt_pow_right (by decide : 1 < 2) v.isLt),
        (vset_or_single s v).symm⟩

theorem vset_inter_nonempty_iff (s t : ℕ) (hs : s < 128) (_ht : t < 128) :
    (vset s ∩ vset t).Nonempty ↔ s &&& t ≠ 0 := by
  constructor
  · rintro ⟨i, hi⟩ h
    obtain ⟨hsi, hti⟩ := Finset.mem_inter.mp hi
    have hbit := congrArg (fun n : ℕ => n.testBit i.val) h
    simp [Nat.testBit_and, (mem_vset _ _).mp hsi, (mem_vset _ _).mp hti] at hbit
  · intro h
    by_contra he
    apply h
    apply Nat.eq_of_testBit_eq
    intro i
    by_cases hi : i < 7
    · by_cases hb : s.testBit i = true
      · have ht : t.testBit i ≠ true := fun hti =>
          he ⟨⟨i, hi⟩, Finset.mem_inter.mpr ⟨(mem_vset _ _).mpr hb, (mem_vset _ _).mpr hti⟩⟩
        simp [Nat.testBit_and, hb, Bool.eq_false_iff.mpr ht]
      · simp [Nat.testBit_and, Bool.eq_false_iff.mpr hb]
    · have hsi : s < 2 ^ i :=
        hs.trans_le (show 2 ^ 7 ≤ 2 ^ i from Nat.pow_le_pow_right (by decide) (by omega))
      simp [Nat.testBit_and, Nat.testBit_lt_two_pow hsi]

theorem maximal_clique_iff_insert (G : SimpleGraph (Fin 7)) (q : Finset (Fin 7)) :
    Maximal (fun t : Finset (Fin 7) => G.IsClique (t : Set (Fin 7))) q ↔
      G.IsClique (q : Set (Fin 7)) ∧
        ∀ v ∉ q, ¬ G.IsClique ((insert v q : Finset (Fin 7)) : Set (Fin 7)) := by
  constructor
  · intro h
    refine ⟨h.1, ?_⟩
    intro v hv hcl
    exact hv (h.2 hcl (Finset.subset_insert _ _) (Finset.mem_insert_self ..))
  · rintro ⟨hq, hno⟩
    refine ⟨hq, ?_⟩
    intro t hcl hqt v hvt
    by_contra hv
    exact hno v hv (hcl.subset (Finset.insert_subset hvt hqt))

end SevenMasks

/-! ## Encoding the edges of a simple graph -/

namespace SevenGraphs
open SimpleGraph

private def pack : ℕ → (ℕ → Bool) → ℕ
  | 0, _ => 0
  | n+1, f => Nat.bit (f 0) (pack n (fun k => f (k+1)))

private theorem pack_test (n i : ℕ) (f : ℕ → Bool) :
    (pack n f).testBit i = (decide (i < n) && f i) := by
  induction n generalizing i f with
  | zero => simp [pack]
  | succ n ih =>
    cases i with
    | zero => simp [pack]
    | succ j => simpa [pack, Nat.testBit_bit_succ] using ih j (fun k => f (k+1))

private theorem pack_bound (n : ℕ) (f : ℕ → Bool) : pack n f < 2 ^ n := by
  induction n generalizing f with
  | zero => simp [pack]
  | succ n ih =>
    have h := ih (fun k => f (k+1))
    rw [pack, pow_succ]
    cases f 0 <;> simp only [Nat.bit_false, Nat.bit_true] <;> omega

def edgeNo (i j : Fin 7) : ℕ := j.val * (j.val - 1) / 2 + i.val

def lo : Fin 21 → Fin 7 := ![0,0,1,0,1,2,0,1,2,3,0,1,2,3,4,0,1,2,3,4,5]
def hi : Fin 21 → Fin 7 := ![1,2,2,3,3,3,4,4,4,4,5,5,5,5,5,6,6,6,6,6,6]

private theorem pair_ok : ∀ k : Fin 21,
    lo k < hi k ∧ edgeNo (lo k) (hi k) = k.val := by decide
private theorem edge_ok : ∀ i j : Fin 7, i < j →
    ∃ k : Fin 21, edgeNo i j = k.val ∧ lo k = i ∧ hi k = j := by decide

noncomputable def graphMask (G : SimpleGraph (Fin 7)) : ℕ := by
  classical
  exact pack 21 fun k => if h : k < 21 then decide (G.Adj (lo ⟨k,h⟩) (hi ⟨k,h⟩)) else false

theorem maskBound (G : SimpleGraph (Fin 7)) : graphMask G < 2^21 := pack_bound _ _

theorem adjBit (G : SimpleGraph (Fin 7)) (i j : Fin 7) (hij : i < j) :
    (graphMask G).testBit (edgeNo i j) = true ↔ G.Adj i j := by
  obtain ⟨k,h,hi',hj'⟩ := edge_ok i j hij
  simp [graphMask, pack_test, h, k.isLt, hi', hj']

theorem subMask {R G : SimpleGraph (Fin 7)} (hRG : R ≤ G) :
    graphMask R &&& graphMask G = graphMask R := by
  apply Nat.eq_of_testBit_eq
  intro k
  rw [Nat.testBit_and]
  by_cases hk : k < 21
  · let e : Fin 21 := ⟨k,hk⟩
    have he := pair_ok e
    by_cases h : (graphMask R).testBit k = true
    · have hr := (adjBit R (lo e) (hi e) he.1).mp (he.2.symm ▸ h)
      have hg := (adjBit G (lo e) (hi e) he.1).mpr (hRG hr)
      rw [he.2] at hg
      change (graphMask G).testBit k = true at hg
      simp [h,hg]
    · simp_all
  · simp [graphMask, pack_test, hk]

end SevenGraphs

/-! ## Cliques and independent sets in the graph encoding -/

namespace SevenGraphs
open SevenMasks SimpleGraph Finset

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem inside_table : ∀ q : Fin 128, inside q.val < 2^21 ∧
    ∀ k : Fin 21, (inside q.val).testBit k.val =
      (q.val.testBit (lo k).val && q.val.testBit (hi k).val) := by decide

private theorem and_all (m n : ℕ) :
    m &&& n = m ↔ ∀ k, m.testBit k = true → n.testBit k = true := by
  constructor
  · intro h k hm
    simpa [Nat.testBit_and, hm] using congrArg (fun a : ℕ => a.testBit k) h
  · intro h
    apply Nat.eq_of_testBit_eq
    intro k
    cases hm : m.testBit k <;> simp_all [Nat.testBit_and]

private theorem and_none (m n : ℕ) :
    m &&& n = 0 ↔ ∀ k, m.testBit k = true → n.testBit k = false := by
  constructor
  · intro h k hm
    simpa [Nat.testBit_and, hm] using congrArg (fun a : ℕ => a.testBit k) h
  · intro h
    apply Nat.eq_of_testBit_eq
    intro k
    cases hm : m.testBit k <;> simp_all [Nat.testBit_and]

private theorem bitPair {q k : ℕ} (hq : q < 128) (h : (inside q).testBit k = true) :
    ∃ i j : Fin 7, i < j ∧ i ∈ vset q ∧ j ∈ vset q ∧ edgeNo i j = k := by
  have ht := inside_table ⟨q,hq⟩
  have hk : k < 21 := by
    by_contra! hn
    have hb : inside q < 2^k := ht.1.trans_le (Nat.pow_le_pow_right (by decide) hn)
    exact Bool.noConfusion (h.symm.trans (Nat.testBit_lt_two_pow hb))
  let e : Fin 21 := ⟨k,hk⟩
  have hh := ht.2 e
  have hm := Bool.and_eq_true_iff.mp (hh.symm.trans h)
  exact ⟨lo e, hi e, (pair_ok e).1, (mem_vset ..).mpr hm.1,
      (mem_vset ..).mpr hm.2, (pair_ok e).2⟩

private theorem pairBit {q : ℕ} (hq : q < 128) {i j : Fin 7}
    (hij : i < j) (hi' : i ∈ vset q) (hj' : j ∈ vset q) :
    (inside q).testBit (edgeNo i j) = true := by
  obtain ⟨e,he,hl,hh⟩ := edge_ok i j hij
  simpa [he, hl, hh, (mem_vset ..).mp hi', (mem_vset ..).mp hj'] using (inside_table ⟨q,hq⟩).2 e

theorem clique_mask (G : SimpleGraph (Fin 7)) {q : ℕ} (hq : q < 128) :
    inside q &&& graphMask G = inside q ↔ G.IsClique (vset q : Set (Fin 7)) := by
  rw [and_all]
  constructor
  · intro h i hi' j hj' hn
    rcases lt_or_gt_of_ne hn with hlt | hgt
    · exact (adjBit G i j hlt).mp (h _ (pairBit hq hlt hi' hj'))
    · exact ((adjBit G j i hgt).mp (h _ (pairBit hq hgt hj' hi'))).symm
  · intro h k hk
    obtain ⟨i,j,hij,hi',hj',rfl⟩ := bitPair hq hk
    exact (adjBit G i j hij).mpr (h hi' hj' hij.ne)

theorem indep_mask (R : SimpleGraph (Fin 7)) {q : ℕ} (hq : q < 128) :
    Indep (graphMask R) q ↔ R.IsIndepSet (vset q : Set (Fin 7)) := by
  unfold Indep
  rw [and_none]
  constructor
  · intro h i hi' j hj' hn hadj
    rcases lt_or_gt_of_ne hn with hlt | hgt
    · exact Bool.noConfusion (((adjBit R i j hlt).mpr hadj).symm.trans
          (h _ (pairBit hq hlt hi' hj')))
    · exact Bool.noConfusion (((adjBit R j i hgt).mpr hadj.symm).symm.trans
          (h _ (pairBit hq hgt hj' hi')))
  · intro h k hk
    obtain ⟨i,j,hij,hi',hj',rfl⟩ := bitPair hq hk
    exact Bool.eq_false_iff.mpr (fun hb => h hi' hj' hij.ne ((adjBit R i j hij).mp hb))

end SevenGraphs

/-! ## Interpreting a transversal certificate -/

namespace SevenGraphs
open SevenMasks SimpleGraph Finset

private theorem triple_valid : ∀ q ∈ triples, q < 128 ∧ (vset q).card = 3 := by decide

theorem noTriangle (R : SimpleGraph (Fin 7)) (ht : R.CliqueFree 3) :
    ∀ q ∈ triples, inside q &&& graphMask R ≠ inside q := by
  intro q hq h
  obtain ⟨hb,hc⟩ := triple_valid q hq
  exact ht _ ⟨(clique_mask R hb).mp h, hc⟩

theorem realize (G R : SimpleGraph (Fin 7)) (h : Extends (graphMask G) (graphMask R)) :
    ∃ A : Finset (Fin 7), R.IsIndepSet (A : Set (Fin 7)) ∧
      ∀ q : Finset (Fin 7), q.Nonempty →
        Maximal (fun t : Finset (Fin 7) => G.IsClique (t : Set (Fin 7))) q →
        (∃ x ∈ q, x ∈ A) ∨ ∃ x ∈ q, ∃ y ∈ q, R.Adj x y := by
  classical
  obtain ⟨s,hs,hI,hcover⟩ := h
  refine ⟨vset s, (indep_mask R hs).mp hI, ?_⟩
  intro t ht hmax
  obtain ⟨q,hq,rfl⟩ := exists_vset t
  have hM := (maximal_clique_iff_insert G _).mp hmax
  have hq0 : q ≠ 0 := by rintro rfl; simp [vset] at ht
  have hmc : MaxClique (graphMask G) q := by
    refine ⟨hq0,(clique_mask G hq).mpr hM.1,?_⟩
    intro v hv hbad
    have bound : q ||| 2^v.val < 2^7 :=
      Nat.or_lt_two_pow hq (Nat.pow_lt_pow_right (by decide : 1 < 2) v.isLt)
    have hx := (clique_mask G bound).mp hbad
    rw [vset_or_single] at hx
    exact hM.2 v (by simp [hv]) hx
  rcases hcover q hq hmc with hit | red
  · obtain ⟨v,hv⟩ := (vset_inter_nonempty_iff s q hs hq).mpr hit
    exact Or.inl ⟨v,(mem_inter.mp hv).2,(mem_inter.mp hv).1⟩
  · right
    by_contra! hn
    apply red
    apply (indep_mask R hq).mpr
    intro i hi j hj _
    exact hn i hi j hj
end SevenGraphs

/-! ## Vertex permutations and the canonical graph encoding -/

namespace SevenGraphs
open SevenMasks SimpleGraph

private def edgeRow (m : Fin 36) := permutationsE[m.val]?.getD []
private def inverseVertex (m : Fin 36) (i : Fin 7) : Fin 7 :=
  let p := permutations[m.val]?.getD []
  ⟨p.idxOf i.val % 7, Nat.mod_lt _ (by decide)⟩

set_option maxRecDepth 16384 in
set_option maxHeartbeats 1200000 in
private theorem perm_data :
    permutationsE = (List.finRange 36).map edgeRow ∧
    (∀ (m : Fin 36) (i j : Fin 7), inverseVertex m i = inverseVertex m j → i = j) ∧
    (∀ (m : Fin 36) (k : Fin 21),
       ((edgeRow m)[k.val]?.getD 21) =
         edgeNo (min (inverseVertex m (lo k)) (inverseVertex m (hi k)))
                (max (inverseVertex m (lo k)) (inverseVertex m (hi k)))) := by decide

private theorem unsortedBit (G : SimpleGraph (Fin 7)) (i j : Fin 7) (hne : i ≠ j) :
    (graphMask G).testBit (edgeNo (min i j) (max i j)) = true ↔ G.Adj i j := by
  rcases lt_or_gt_of_ne hne with h | h
  · simpa [min_eq_left h.le, max_eq_right h.le] using adjBit G i j h
  · simpa [min_eq_right h.le, max_eq_left h.le, G.adj_comm] using adjBit G j i h

theorem perm_not_smaller (G : SimpleGraph (Fin 7))
    (hmin : ∀ σ : Equiv.Perm (Fin 7), graphMask G ≤ graphMask (G.comap σ))
    (e : List ℕ) (he : e ∈ permutationsE) :
    ∃ h : ℕ, graphMask G ≤ h ∧ h < 2^21 ∧ ∀ k : Fin 21,
        h.testBit k.val = (graphMask G).testBit (e[k.val]?.getD 21) := by
  rw [perm_data.1] at he
  obtain ⟨m,_,rfl⟩ := List.mem_map.mp he
  have inj : Function.Injective (inverseVertex m) := fun _ _ h => perm_data.2.1 m _ _ h
  let σ := Equiv.ofBijective (inverseVertex m) ⟨inj,Finite.injective_iff_surjective.mp inj⟩
  refine ⟨graphMask (G.comap σ),hmin σ,maskBound _,?_⟩
  intro k
  have hlt := (pair_ok k).1
  have a := adjBit (G.comap σ) (lo k) (hi k) hlt
  rw [(pair_ok k).2] at a
  have b := unsortedBit G (inverseVertex m (lo k)) (inverseVertex m (hi k)) (inj.ne hlt.ne)
  rw [perm_data.2.2 m k]
  apply Bool.eq_iff_iff.mpr
  exact a.trans b.symm
end SevenGraphs

/-! ## Reduction to a minimum representative under relabelling -/

namespace SevenCanonical

open SimpleGraph Finset

def colorable (G R : SimpleGraph (Fin 7)) : Prop :=
  ∃ A : Finset (Fin 7), R.IsIndepSet (A : Set (Fin 7)) ∧
    ∀ q : Finset (Fin 7), q.Nonempty →
      Maximal (fun t : Finset (Fin 7) => G.IsClique (t : Set (Fin 7))) q →
      (∃ x ∈ q, x ∈ A) ∨ ∃ x ∈ q, ∃ y ∈ q, R.Adj x y

private theorem of_comap (G R : SimpleGraph (Fin 7)) (σ : Equiv.Perm (Fin 7))
    (h : colorable (G.comap σ) (R.comap σ)) : colorable G R := by
  obtain ⟨B, hind, hit⟩ := h
  refine ⟨B.map σ.toEmbedding, ?_, ?_⟩
  · rw [SimpleGraph.isIndepSet_iff] at hind ⊢
    intro x hx y hy hn hadj
    obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hy
    exact hind hi hj (ne_of_apply_ne σ hn) hadj
  · intro q hq hmax
    let p := q.map σ.symm.toEmbedding
    have memP {i : Fin 7} : i ∈ p ↔ σ i ∈ q := Finset.mem_map_equiv
    have maxP : Maximal (fun t : Finset (Fin 7) =>
        (G.comap σ).IsClique (t : Set (Fin 7))) p := by
      constructor
      · intro i hi j hj hne
        exact hmax.1 (memP.mp hi) (memP.mp hj) (σ.injective.ne hne)
      · intro t hcl hpt i hit'
        have projected : G.IsClique ((t.map σ.toEmbedding : Finset (Fin 7)) : Set (Fin 7)) := by
          intro x hx y hy hne
          obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hx
          obtain ⟨b, hb, rfl⟩ := Finset.mem_map.mp hy
          exact hcl ha hb (ne_of_apply_ne σ hne)
        have covers : q ⊆ t.map σ.toEmbedding := by
          intro x hx
          apply Finset.mem_map_equiv.mpr
          apply hpt
          exact Finset.mem_map.mpr ⟨x, hx, rfl⟩
        exact memP.mpr (hmax.2 projected covers (Finset.mem_map.mpr ⟨i, hit', rfl⟩))
    rcases hit p hq.map maxP with ⟨i, hi, hb⟩ | ⟨i, hi, j, hj, hij⟩
    · exact Or.inl ⟨σ i, memP.mp hi, Finset.mem_map.mpr ⟨i, hb, rfl⟩⟩
    · exact Or.inr ⟨σ i, memP.mp hi, σ j, memP.mp hj, hij⟩

theorem of_minimal (encode : SimpleGraph (Fin 7) → ℕ)
    (finiteCase : ∀ G R : SimpleGraph (Fin 7),
      (∀ σ : Equiv.Perm (Fin 7), encode G ≤ encode (G.comap σ)) →
      R ≤ G → R.CliqueFree 3 → colorable G R) :
    ∀ G R : SimpleGraph (Fin 7), R ≤ G → R.CliqueFree 3 → colorable G R := by
  classical
  intro G R hRG htri
  obtain ⟨σ, _, hmin⟩ := Finset.exists_min_image Finset.univ
    (fun π : Equiv.Perm (Fin 7) => encode (G.comap π)) Finset.univ_nonempty
  apply of_comap G R σ
  apply finiteCase
  · intro τ
    exact hmin (τ.trans σ) (Finset.mem_univ _)
  · exact fun _ _ h => hRG h
  · exact htri.comap (SimpleGraph.Iso.comap σ R).isContained

end SevenCanonical

/-! ## Restoring the original link and its isolated vertices -/

open SimpleGraph Finset

private theorem imageClique {U V : Type*} [DecidableEq V] (G : SimpleGraph V) (f : U → V)
    {s : Finset U} (hs : (G.comap f).IsClique (s : Set U)) :
    G.IsClique (s.image f : Set V) := by
  rintro _ hx _ hy hne
  obtain ⟨x, hsx, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨y, hsy, rfl⟩ := Finset.mem_image.mp hy
  exact hs hsx hsy (ne_of_apply_ne f hne)

private theorem transferSeven (finiteCase :
    ∀ (G R : SimpleGraph (Fin 7)), R ≤ G → R.CliqueFree 3 →
      ∃ A : Finset (Fin 7), R.IsIndepSet (A : Set (Fin 7)) ∧
        ∀ q : Finset (Fin 7), q.Nonempty →
          Maximal (fun t : Finset (Fin 7) => G.IsClique (t : Set (Fin 7))) q →
          (∃ x ∈ q, x ∈ A) ∨ ∃ x ∈ q, ∃ y ∈ q, R.Adj x y) : OMA.R_Erdos151_erdos_151_R3.H1 := by
  classical
  intro n G R N hRG htri hbound
  let S := N.filter fun x => ∃ y ∈ N, G.Adj x y
  have subN : S ⊆ N := Finset.filter_subset _ _
  have active {x y} (hx : x ∈ N) (hy : y ∈ N) (h : R.Adj x y) : x ∈ S :=
    Finset.mem_filter.mpr ⟨hx, y, hy, hRG h⟩
  by_cases hS : S.Nonempty
  · obtain ⟨s, hs⟩ := hS
    let : Nonempty (↥S) := ⟨⟨s, hs⟩⟩
    let e : S ↪ Fin 7 := (Fintype.equivFin S).toEmbedding.trans
      (Fin.castLEEmb (by rw [Fintype.card_coe]; exact hbound))
    let f (i : Fin 7) : Fin n := (Function.invFun e i).val
    let g (z : Fin n) : Fin 7 := if hz : z ∈ S then e ⟨z, hz⟩ else 0
    have inverse {z} (hz : z ∈ S) : f (g z) = z := by
      simp only [g, dif_pos hz, f]
      exact congrArg Subtype.val (Function.leftInverse_invFun e.injective ⟨z, hz⟩)
    have lands (i) : f i ∈ N := subN (Function.invFun e i).property
    have noTri : (R.comap f).CliqueFree 3 := by
      intro c hc
      have inj : Set.InjOn f (c : Set (Fin 7)) := by
        intro x hx y hy he
        by_contra hn
        have bad : R.Adj (f x) (f y) := hc.isClique hx hy hn
        exact bad.ne he
      exact htri (c.image f) ⟨imageClique R f hc.isClique,
        (Finset.card_image_of_injOn inj).trans hc.card_eq⟩
    obtain ⟨B, hind, hit⟩ := finiteCase (G.comap f) (R.comap f) (fun _ _ h => hRG h) noTri
    let A := B.image f ∪ (N \ S)
    have inN : A ⊆ N := by
      intro z hz
      rcases Finset.mem_union.mp hz with h | h
      · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp h
        exact lands i
      · exact (Finset.mem_sdiff.mp h).1
    refine ⟨A, inN, ?_, ?_⟩
    · rw [SimpleGraph.isIndepSet_iff] at hind ⊢
      intro x hx y hy hne hadj
      have lift_mem {v} (hv : v ∈ A) (ht : v ∈ S) : v ∈ B.image f :=
        (Finset.mem_union.mp hv).resolve_right (fun h => (Finset.mem_sdiff.mp h).2 ht)
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp (lift_mem hx (active (inN hx) (inN hy) hadj))
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp (lift_mem hy (active (inN hy) (inN hx) hadj.symm))
      exact hind hi hj (ne_of_apply_ne f hne) hadj
    · intro q hq hmax
      by_cases hqs : q ⊆ S
      · have start : (G.comap f).IsClique ((q.image g : Finset (Fin 7)) : Set (Fin 7)) := by
          intro i hi j hj hne
          obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hi
          obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hj
          change G.Adj (f (g u)) (f (g v))
          rw [inverse (hqs hu), inverse (hqs hv)]
          exact hmax.1.2 hu hv (ne_of_apply_ne g hne)
        obtain ⟨Q, extended, maximal⟩ := Finite.exists_le_maximal
          (p := fun t : Finset (Fin 7) => (G.comap f).IsClique (t : Set (Fin 7))) start
        have qsub : q ⊆ Q.image f := by
          intro z hz
          exact Finset.mem_image.mpr ⟨g z, extended (Finset.mem_image_of_mem g hz), inverse (hqs hz)⟩
        have Qin : Q.image f ⊆ N := by
          intro z hz
          obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hz
          exact lands i
        have back : Q.image f ⊆ q := hmax.2 ⟨Qin, imageClique G f maximal.1⟩ qsub
        have proj {i} (hi : i ∈ Q) : f i ∈ q := back (Finset.mem_image_of_mem f hi)
        rcases hit Q ((hq.image g).mono extended) maximal with ⟨i, hi, hiB⟩ | ⟨i, hi, j, hj, hij⟩
        · exact Or.inl ⟨f i, proj hi, Finset.mem_union_left _ (Finset.mem_image_of_mem f hiB)⟩
        · exact Or.inr ⟨f i, proj hi, f j, proj hj, hij⟩
      · obtain ⟨z, hz, hnot⟩ := Finset.not_subset.mp hqs
        exact Or.inl ⟨z, hz, Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hmax.1.1 hz, hnot⟩)⟩
  · refine ⟨N, Subset.rfl, ?_, ?_⟩
    · rw [SimpleGraph.isIndepSet_iff]
      intro x hx y hy _ hxy
      exact hS ⟨x, active hx hy hxy⟩
    · intro q hq hmax
      obtain ⟨x, hx⟩ := hq
      exact Or.inl ⟨x, hx, hmax.1.1 hx⟩

theorem OMA.solution : OMA.R_Erdos151_erdos_151_R3.H1 := by
  apply transferSeven (SevenCanonical.of_minimal SevenGraphs.graphMask ?_)
  intro G R hmin hRG htri
  apply SevenGraphs.realize
  have hsub := SevenGraphs.subMask hRG
  rcases SevenMasks.classified _ (SevenGraphs.maskBound G)
      (SevenGraphs.perm_not_smaller G hmin) with ⟨s,hs,hstable⟩ | he
  · refine ⟨s,hs,?_,fun q hq hm => Or.inl (hstable.2 q hq hm)⟩
    apply (SevenGraphs.indep_mask R hs).mpr
    have hG := (SevenGraphs.indep_mask G hs).mp hstable.1
    intro x hx y hy hne hr
    exact hG hx hy hne (hRG hr)
  · exact SevenMasks.exceptional_extends he hsub (SevenGraphs.noTriangle R htri)
