import OMAStatements.S_oeis_a345483

namespace OMA.S_oeis_a345483

open PowerSeries




/-! ### Lower bounds from explicit lists -/

/-- The sum of the squares of a list. -/
def sqs (l : List ℕ) : ℕ := (l.map (· ^ 2)).sum

/-- The entries do not increase. -/
def noninc : List ℕ → Bool
  | a :: b :: t => Nat.ble b a && noninc (b :: t)
  | _ => true

lemma noninc_spec : ∀ l : List ℕ, noninc l = true → l.Pairwise (· ≥ ·)
  | [], _ => List.Pairwise.nil
  | [a], _ => List.pairwise_singleton _ a
  | a :: b :: t, h => by
    simp only [noninc, Bool.and_eq_true, Nat.ble_eq] at h
    have ih := noninc_spec (b :: t) h.2
    rw [List.pairwise_cons]
    refine ⟨fun x hx => ?_, ih⟩
    rcases List.mem_cons.mp hx with rfl | hx
    · exact h.1
    · exact le_trans ((List.pairwise_cons.mp ih).1 x hx) h.1

/-- Any two lists of the list differ. -/
def allDiffer : List (List ℕ) → Bool
  | [] => true
  | l :: ls => ls.all (fun m => !(l == m)) && allDiffer ls

lemma allDiffer_spec : ∀ ls : List (List ℕ), allDiffer ls = true → ls.Nodup
  | [], _ => List.nodup_nil
  | l :: ls, h => by
    simp only [allDiffer, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true',
      beq_eq_false_iff_ne] at h
    rw [List.nodup_cons]
    exact ⟨fun hl => h.1 l hl rfl, allDiffer_spec ls h.2⟩

/-- A witness for n: 7 positive entries, nonincreasing, squares summing to n. -/
def valid (n : ℕ) (l : List ℕ) : Bool :=
  l.length == 7 && l.all (fun x => Nat.ble 1 x) && sqs l == n && noninc l

/-- 6 distinct witnesses for n. -/
def okGroup (n : ℕ) (ls : List (List ℕ)) : Bool :=
  ls.length == 6 && ls.all (valid n) && allDiffer ls

lemma le_sqs {l : List ℕ} {x : ℕ} (hx : x ∈ l) : x ^ 2 ≤ sqs l := by
  unfold sqs
  exact List.le_sum_of_mem (List.mem_map_of_mem hx)

/-- The multiset of a list of length 7, as an element of `Sym ℕ 7`. -/
def toSym (l : List ℕ) : Sym ℕ 7 :=
  if h : l.length = 7 then Sym.mk (l : Multiset ℕ) (by simpa using h)
  else Sym.replicate 7 0

lemma toSym_val {l : List ℕ} (h : l.length = 7) :
    ((toSym l : Sym ℕ 7) : Multiset ℕ) = (l : Multiset ℕ) := by
  unfold toSym
  rw [dif_pos h]
  rfl

lemma valid_spec {n : ℕ} {l : List ℕ} (h : valid n l = true) :
    l.length = 7 ∧ (∀ x ∈ l, 1 ≤ x) ∧ sqs l = n ∧ l.Pairwise (· ≥ ·) := by
  simp only [valid, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, Nat.ble_eq] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, noninc_spec l h.2⟩

/-- A list of 7 positive entries with squares summing to n gives a point of the count. -/
lemma toSym_mem {n : ℕ} {l : List ℕ} (h9 : l.length = 7) (hpos : ∀ x ∈ l, 1 ≤ x)
    (hsum : sqs l = n) :
    toSym l ∈ ((Finset.Icc 1 n).sym 7).filter
      (fun s : Sym ℕ 7 => ((s : Multiset ℕ).map (· ^ 2)).sum = n) := by
  rw [Finset.mem_filter]
  refine ⟨?_, ?_⟩
  · rw [Finset.mem_sym_iff]
    intro x hx
    have hx' : x ∈ ((toSym l : Sym ℕ 7) : Multiset ℕ) := hx
    rw [toSym_val h9, Multiset.mem_coe] at hx'
    refine Finset.mem_Icc.mpr ⟨hpos x hx', ?_⟩
    have := le_sqs hx'
    have : x ≤ x ^ 2 := Nat.le_self_pow (by norm_num) x
    omega
  · rw [toSym_val h9, Multiset.map_coe, Multiset.sum_coe]
    exact hsum

lemma ways_ge_of_okGroup {n : ℕ} {ls : List (List ℕ)} (h : okGroup n ls = true) :
    6 ≤ ways n := by
  simp only [okGroup, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨⟨hlen, hall⟩, hnd'⟩ := h
  have hnd := allDiffer_spec ls hnd'
  have hcard : ls.toFinset.card = 6 := by rw [List.toFinset_card_of_nodup hnd, hlen]
  rw [← hcard]
  unfold ways
  apply Finset.card_le_card_of_injOn toSym
  · intro l hl
    have hl' : l ∈ ls := List.mem_toFinset.mp hl
    obtain ⟨h9, hpos, hsum, -⟩ := valid_spec (hall l hl')
    exact toSym_mem h9 hpos hsum
  · intro l1 hl1 l2 hl2 heq
    have hl1' : l1 ∈ ls := List.mem_toFinset.mp hl1
    have hl2' : l2 ∈ ls := List.mem_toFinset.mp hl2
    obtain ⟨h91, -, -, hp1⟩ := valid_spec (hall l1 hl1')
    obtain ⟨h92, -, -, hp2⟩ := valid_spec (hall l2 hl2')
    have hm : (l1 : Multiset ℕ) = (l2 : Multiset ℕ) := by
      rw [← toSym_val h91, ← toSym_val h92]
      exact congrArg Subtype.val heq
    exact List.Perm.eq_of_pairwise (fun a b _ _ h1 h2 => le_antisymm h2 h1) hp1 hp2
      (Multiset.coe_eq_coe.mp hm)

/-! ### Witnesses for 69 <= n < 1942, found by search -/

/-- Adds to `c`, while it has fewer than 6 lists, the lists `p ++ l` where `l` is nonincreasing with
`k` entries in `[1, a]` whose squares sum to `r`. -/
def sr : ℕ → ℕ → ℕ → ℕ → List ℕ → List (List ℕ) → List (List ℕ)
  | f + 1, k + 1, a + 1, r, p, c =>
    sr f (k + 1) a r p (if c.length < 6 ∧ (a + 1) ^ 2 + k ≤ r ∧ r ≤ (k + 1) * (a + 1) ^ 2 then
      sr f k (a + 1) (r - (a + 1) ^ 2) (p ++ [a + 1]) c else c)
  | _, 0, _, r, p, c => if r = 0 then p :: c else c
  | _, _, _, _, _, c => c

/-- Checks the searched witnesses for n, n + 1, ..., n + t - 1. -/
def chk : ℕ → ℕ → Bool
  | _, 0 => true
  | n, t + 1 => okGroup n (sr 99 7 44 n [] []) && chk (n + 1) t

lemma chk_spec : ∀ t n, chk n t = true → ∀ m, n ≤ m → m < n + t → 6 ≤ ways m := by
  intro t
  induction t with
  | zero => intro n _ m h1 h2; omega
  | succ t ih =>
    intro n h m h1 h2
    simp only [chk, Bool.and_eq_true] at h
    rcases Nat.eq_or_lt_of_le h1 with rfl | h1'
    · exact ways_ge_of_okGroup h.1
    · exact ih (n + 1) h.2 m h1' (by omega)

theorem c0 : chk 69 200 = true := by decide +kernel
theorem c1 : chk 269 200 = true := by decide +kernel
theorem c2 : chk 469 200 = true := by decide +kernel
theorem c3 : chk 669 200 = true := by decide +kernel
theorem c4 : chk 869 200 = true := by decide +kernel
theorem c5 : chk 1069 200 = true := by decide +kernel
theorem c6 : chk 1269 200 = true := by decide +kernel
theorem c7 : chk 1469 200 = true := by decide +kernel
theorem c8 : chk 1669 200 = true := by decide +kernel
theorem c9 : chk 1869 73 = true := by decide +kernel

lemma mid (n : ℕ) (h1 : 69 ≤ n) (h2 : n < 1942) : 6 ≤ ways n := by
  by_cases h : n < 269
  · exact chk_spec 200 69 c0 n (by omega) h
  by_cases h : n < 469
  · exact chk_spec 200 269 c1 n (by omega) h
  by_cases h : n < 669
  · exact chk_spec 200 469 c2 n (by omega) h
  by_cases h : n < 869
  · exact chk_spec 200 669 c3 n (by omega) h
  by_cases h : n < 1069
  · exact chk_spec 200 869 c4 n (by omega) h
  by_cases h : n < 1269
  · exact chk_spec 200 1069 c5 n (by omega) h
  by_cases h : n < 1469
  · exact chk_spec 200 1269 c6 n (by omega) h
  by_cases h : n < 1669
  · exact chk_spec 200 1469 c7 n (by omega) h
  by_cases h : n < 1869
  · exact chk_spec 200 1669 c8 n (by omega) h
  exact chk_spec 73 1869 c9 n (by omega) h2

/-! ### Complete lists below 69 -/

/-- The nonincreasing lists of p positive integers, each at most M, whose squares sum to n. -/
def gen : ℕ → ℕ → ℕ → List (List ℕ)
  | 0, _, n => if n = 0 then [[]] else []
  | p + 1, M, n => (List.range M).flatMap (fun i =>
      if (i + 1) ^ 2 ≤ n then (gen p (i + 1) (n - (i + 1) ^ 2)).map (fun l => (i + 1) :: l)
      else [])

lemma mem_gen : ∀ (p M n : ℕ) (l : List ℕ), l.length = p → l.Pairwise (· ≥ ·) →
    (∀ x ∈ l, 1 ≤ x ∧ x ≤ M) → sqs l = n → l ∈ gen p M n := by
  intro p
  induction p with
  | zero =>
    intro M n l hl _ _ hs
    have : l = [] := List.eq_nil_of_length_eq_zero hl
    subst this
    simp only [sqs, List.map_nil, List.sum_nil] at hs
    subst hs
    simp [gen]
  | succ p ih =>
    intro M n l hl hpw hb hs
    match l, hl with
    | x :: rest, hl =>
      have hlen : rest.length = p := by simpa using hl
      rw [List.pairwise_cons] at hpw
      have hx := hb x (List.mem_cons_self ..)
      have hrest : ∀ y ∈ rest, 1 ≤ y ∧ y ≤ x := fun y hy =>
        ⟨(hb y (List.mem_cons_of_mem _ hy)).1, hpw.1 y hy⟩
      have hs' : x ^ 2 + sqs rest = n := by simpa [sqs] using hs
      have hmem := ih x (n - x ^ 2) rest hlen hpw.2 hrest (by omega)
      simp only [gen, List.mem_flatMap, List.mem_range]
      refine ⟨x - 1, by omega, ?_⟩
      rw [show x - 1 + 1 = x by omega, if_pos (by omega)]
      exact List.mem_map.mpr ⟨rest, hmem, rfl⟩

lemma card_le_sum_sq (t : Multiset ℕ) (hpos : ∀ y ∈ t, 1 ≤ y) :
    Multiset.card t ≤ (t.map (· ^ 2)).sum := by
  induction t using Multiset.induction_on with
  | empty => simp
  | cons x t ih =>
    simp only [Multiset.card_cons, Multiset.map_cons, Multiset.sum_cons]
    have hx := hpos x (Multiset.mem_cons_self x t)
    have := ih (fun y hy => hpos y (Multiset.mem_cons_of_mem hy))
    nlinarith

lemma sq_add_le {s : Multiset ℕ} (hpos : ∀ y ∈ s, 1 ≤ y) {x : ℕ} (hx : x ∈ s) :
    x ^ 2 + (Multiset.card s - 1) ≤ (s.map (· ^ 2)).sum := by
  obtain ⟨t, rfl⟩ := Multiset.exists_cons_of_mem hx
  simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons, Nat.add_sub_cancel]
  have := card_le_sum_sq t (fun y hy => hpos y (Multiset.mem_cons_of_mem hy))
  omega

lemma ways_le_gen {n : ℕ} (hn : n < 69) : ways n ≤ (gen 7 7 n).length := by
  unfold ways
  calc _ ≤ (gen 7 7 n).toFinset.card := by
        apply Finset.card_le_card_of_injOn
          (fun s : Sym ℕ 7 => (s : Multiset ℕ).sort (· ≥ ·))
        · intro s hs
          rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_sym_iff] at hs
          rw [Finset.mem_coe, List.mem_toFinset]
          have hpos : ∀ y ∈ (s : Multiset ℕ), 1 ≤ y := fun y hy =>
            (Finset.mem_Icc.mp (hs.1 y hy)).1
          apply mem_gen
          · rw [Multiset.length_sort]
            exact Sym.card_coe
          · exact Multiset.pairwise_sort _ _
          · intro x hx
            rw [Multiset.mem_sort] at hx
            refine ⟨hpos x hx, ?_⟩
            have h1 := sq_add_le hpos hx
            rw [Sym.card_coe, hs.2] at h1
            nlinarith
          · unfold sqs
            rw [← Multiset.sum_coe, ← Multiset.map_coe, Multiset.sort_eq]
            exact hs.2
        · intro s1 _ s2 _ h
          apply Sym.coe_injective
          rw [← Multiset.sort_eq (s1 : Multiset ℕ) (· ≥ ·),
            ← Multiset.sort_eq (s2 : Multiset ℕ) (· ≥ ·)]
          exact congrArg (fun l : List ℕ => (l : Multiset ℕ)) h
    _ ≤ (gen 7 7 n).length := List.toFinset_card_le _

/-! ### Every n >= 1942 -/

/-- Fillers with squares summing to r mod 8, for a remainder 7 mod 8 (empty: none). -/
def fillA (r : ℕ) : List ℕ :=
  match r with
  | 0 => [2, 2]
  | 1 => [4, 1]
  | 2 => [1, 1]
  | 4 => [4, 2]
  | 5 => [2, 1]
  | _ => []

/-- Fillers with squares summing to r mod 32, for a remainder 28 mod 32 (empty: none). -/
def fillB (r : ℕ) : List ℕ :=
  match r with
  | 1 => [8, 1]
  | 2 => [1, 1]
  | 9 => [5, 4]
  | 10 => [3, 1]
  | 17 => [4, 1]
  | 18 => [3, 3]
  | 25 => [4, 3]
  | 26 => [5, 1]
  | _ => []

/-- The type (false: remainder 7 mod 8, true: remainder 28 mod 32) and the filler, from
n mod 32 and the largest part mod 16. -/
def choice (a b : ℕ) : Option (Bool × List ℕ) :=
  if fillA ((a + 1 + 7 * (b * b)) % 8) ≠ [] then some (false, fillA ((a + 1 + 7 * (b * b)) % 8))
  else if fillB ((a + 4 + 31 * (b * b)) % 32) ≠ [] then
    some (true, fillB ((a + 4 + 31 * (b * b)) % 32))
  else none

/-- What a choice guarantees, for all residues. -/
def choiceOk (a b : ℕ) : Bool :=
  match choice a b with
  | some (t, F) => F.length == 7 - 5 && F.all (fun x => decide (1 ≤ x ∧ x ≤ 8)) &&
      decide (2 ≤ sqs F ∧ sqs F ≤ 65) &&
      (if t then (a + 1280 - b * b % 32 - sqs F) % 32 == 28
        else (a + 1280 - b * b % 32 - sqs F) % 8 == 7)
  | none => true

theorem choiceOk_all : ∀ a < 32, ∀ b < 16, choiceOk a b = true := by decide +kernel

/-- In every window of 12 consecutive largest parts at least 6 have a choice. -/
theorem window_all : ∀ a < 32, ∀ b < 16,
    6 ≤ ((List.range 12).filter
      (fun j => (choice a ((b + 16 * 12 - j) % 16)).isSome)).length := by
  decide +kernel

lemma sq_mod32 (B : ℕ) : B ^ 2 % 32 = (B % 16) * (B % 16) % 32 := by
  obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < 16 ∧ B = 16 * q + r :=
    ⟨B / 16, B % 16, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod B 16).symm⟩
  have h1 : (16 * q + r) % 16 = r := by omega
  rw [h1]
  have e : (16 * q + r) ^ 2 = 32 * (8 * q * q + q * r) + r * r := by ring
  rw [e]
  generalize 8 * q * q + q * r = x
  generalize r * r = y
  omega

lemma three_sq8 (x y z : ℕ) : (x ^ 2 + y ^ 2 + z ^ 2) % 8 ≠ 7 := by
  intro h
  have key : ∀ a b c : ZMod 8, a ^ 2 + b ^ 2 + c ^ 2 ≠ 7 := by decide
  apply key x y z
  have : ((x ^ 2 + y ^ 2 + z ^ 2 : ℕ) : ZMod 8) = ((7 : ℕ) : ZMod 8) :=
    (ZMod.natCast_eq_natCast_iff' _ _ 8).mpr (by rw [h])
  push_cast at this
  exact this

lemma sq_mod4 (x : ℕ) : x ^ 2 % 4 = x % 2 := by
  obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < 2 ∧ x = 2 * q + r :=
    ⟨x / 2, x % 2, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod x 2).symm⟩
  have e : (2 * q + r) ^ 2 = 4 * (q * q + q * r) + r * r := by ring
  rw [e]
  have h1 : (2 * q + r) % 2 = r := by omega
  rw [h1]
  generalize q * q + q * r = w
  interval_cases r <;> omega

lemma three_sq32 (x y z : ℕ) : (x ^ 2 + y ^ 2 + z ^ 2) % 32 ≠ 28 := by
  intro h
  have h2 : x % 2 = 0 ∧ y % 2 = 0 ∧ z % 2 = 0 := by
    have hx := sq_mod4 x
    have hy := sq_mod4 y
    have hz := sq_mod4 z
    generalize x ^ 2 = X at h hx
    generalize y ^ 2 = Y at h hy
    generalize z ^ 2 = Z at h hz
    omega
  obtain ⟨x', rfl⟩ : ∃ x', x = 2 * x' := ⟨x / 2, by omega⟩
  obtain ⟨y', rfl⟩ : ∃ y', y = 2 * y' := ⟨y / 2, by omega⟩
  obtain ⟨z', rfl⟩ : ∃ z', z = 2 * z' := ⟨z / 2, by omega⟩
  apply three_sq8 x' y' z'
  have e : (2 * x') ^ 2 + (2 * y') ^ 2 + (2 * z') ^ 2 = 4 * (x' ^ 2 + y' ^ 2 + z' ^ 2) := by
    ring
  rw [e] at h
  generalize x' ^ 2 + y' ^ 2 + z' ^ 2 = S at h ⊢
  omega

lemma not_three {Q : ℕ} (hQ : Q % 8 = 7 ∨ Q % 32 = 28) (x y z : ℕ) :
    x ^ 2 + y ^ 2 + z ^ 2 ≠ Q := by
  intro h
  rcases hQ with hQ | hQ
  · exact three_sq8 x y z (h ▸ hQ)
  · exact three_sq32 x y z (h ▸ hQ)

lemma four_pos {a b c d Q : ℕ} (h : a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = Q)
    (hQ : Q % 8 = 7 ∨ Q % 32 = 28) : 1 ≤ a ∧ 1 ≤ b ∧ 1 ≤ c ∧ 1 ≤ d := by
  refine ⟨Nat.one_le_iff_ne_zero.mpr ?_, Nat.one_le_iff_ne_zero.mpr ?_,
    Nat.one_le_iff_ne_zero.mpr ?_, Nat.one_le_iff_ne_zero.mpr ?_⟩ <;> rintro rfl
  · exact not_three hQ b c d (by rw [← h]; ring)
  · exact not_three hQ a c d (by rw [← h]; ring)
  · exact not_three hQ a b d (by rw [← h]; ring)
  · exact not_three hQ a b c (by rw [← h]; ring)

lemma lag_exists (Q : ℕ) :
    ∃ v : ℕ × ℕ × ℕ × ℕ, v.1 ^ 2 + v.2.1 ^ 2 + v.2.2.1 ^ 2 + v.2.2.2 ^ 2 = Q := by
  obtain ⟨a, b, c, d, h⟩ := Nat.sum_four_squares Q
  exact ⟨(a, b, c, d), h⟩

/-- A four-square representation of Q (Lagrange). -/
noncomputable def lag (Q : ℕ) : ℕ × ℕ × ℕ × ℕ := Classical.choose (lag_exists Q)

lemma lag_spec (Q : ℕ) :
    (lag Q).1 ^ 2 + (lag Q).2.1 ^ 2 + (lag Q).2.2.1 ^ 2 + (lag Q).2.2.2 ^ 2 = Q :=
  Classical.choose_spec (lag_exists Q)

/-- The largest part of the j-th partition of n. -/
def bv (n j : ℕ) : ℕ := Nat.sqrt (n - 93) - j

/-- The filler of the j-th partition of n. -/
def fv (n j : ℕ) : List ℕ := ((choice (n % 32) (bv n j % 16)).getD (false, [])).2

/-- The part that Lagrange writes as four squares. -/
def qv (n j : ℕ) : ℕ := n - bv n j ^ 2 - sqs (fv n j)

/-- The j-th partition of n, as a list. -/
noncomputable def lv (n j : ℕ) : List ℕ :=
  [(lag (qv n j)).1, (lag (qv n j)).2.1, (lag (qv n j)).2.2.1, (lag (qv n j)).2.2.2, bv n j] ++
    fv n j

lemma sqrt_lt_of_sq_lt {v B : ℕ} (h : v ^ 2 < B ^ 2) : v < B := by
  by_contra hc
  push_neg at hc
  have := Nat.pow_le_pow_left hc 2
  omega

lemma arith {n b2 f q a β : ℕ} (t : Bool) (hn : 1942 ≤ n) (hB2 : b2 ≤ n - 93)
    (ha : n % 32 = a) (hβ : b2 % 32 = β) (hf1 : 2 ≤ f) (hf2 : f ≤ 65)
    (hQ : q = n - b2 - f) (hn2 : n < 2 * b2 + 2)
    (hm : if t then (a + 1280 - β - f) % 32 = 28 else (a + 1280 - β - f) % 8 = 7) :
    q + b2 + f = n ∧ q < b2 ∧ (q % 8 = 7 ∨ q % 32 = 28) := by
  cases t <;> simp at hm <;> omega

lemma construct (n j : ℕ) (hn : 1942 ≤ n) (hj : j < 12)
    (hg : (choice (n % 32) (bv n j % 16)).isSome) :
    (lv n j).length = 7 ∧ (∀ x ∈ lv n j, 1 ≤ x ∧ x ≤ bv n j) ∧ bv n j ∈ lv n j ∧
      sqs (lv n j) = n ∧ bv n j ≤ n ∧ 43 ≤ Nat.sqrt (n - 93) := by
  have hs1 : Nat.sqrt (n - 93) ^ 2 ≤ n - 93 := Nat.sqrt_le' _
  have hs2 : n - 93 < (Nat.sqrt (n - 93) + 1) ^ 2 := Nat.lt_succ_sqrt' _
  have hs3 : 43 ≤ Nat.sqrt (n - 93) := Nat.le_sqrt'.mpr (by norm_num; omega)
  have hB : bv n j = Nat.sqrt (n - 93) - j := rfl
  generalize hsdef : Nat.sqrt (n - 93) = s at hs1 hs2 hs3 hB
  have hB0 : 32 ≤ bv n j := by omega
  have hBs : bv n j ≤ s := by omega
  have hB2 : bv n j ^ 2 ≤ n - 93 := le_trans (Nat.pow_le_pow_left hBs 2) hs1
  obtain ⟨⟨t, F⟩, hch⟩ := Option.isSome_iff_exists.mp hg
  have hok := choiceOk_all (n % 32) (Nat.mod_lt _ (by norm_num)) (bv n j % 16)
    (Nat.mod_lt _ (by norm_num))
  simp only [choiceOk, hch, Bool.and_eq_true, beq_iff_eq, List.all_eq_true,
    decide_eq_true_eq] at hok
  obtain ⟨⟨⟨hFl, hFb⟩, hF1, hF2⟩, hmod⟩ := hok
  have hfv : fv n j = F := by simp [fv, hch]
  have hn2 : n < 2 * bv n j ^ 2 + 2 := by
    have h1 : n < (s + 1) ^ 2 + 93 := by omega
    have h2 : (s + 1) ^ 2 ≤ (bv n j + 12) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have h3 : 32 * bv n j ≤ bv n j * bv n j := Nat.mul_le_mul_right _ hB0
    nlinarith
  have hβ := sq_mod32 (bv n j)
  have hm : if t then (n % 32 + 1280 - bv n j % 16 * (bv n j % 16) % 32 - sqs F) % 32 = 28
      else (n % 32 + 1280 - bv n j % 16 * (bv n j % 16) % 32 - sqs F) % 8 = 7 := by
    cases t <;> simpa using hmod
  obtain ⟨hsum, hdom, hQmod⟩ := arith t hn hB2 rfl hβ hF1 hF2
    (show qv n j = n - bv n j ^ 2 - sqs F by rw [← hfv]; rfl) hn2 hm
  have hl := lag_spec (qv n j)
  obtain ⟨ha, hb, hc, hd⟩ := four_pos hl hQmod
  have hlt : ∀ v, v ^ 2 ≤ qv n j → v < bv n j := fun v hv =>
    sqrt_lt_of_sq_lt (lt_of_le_of_lt hv hdom)
  have z1 := Nat.zero_le ((lag (qv n j)).1 ^ 2)
  have z2 := Nat.zero_le ((lag (qv n j)).2.1 ^ 2)
  have z3 := Nat.zero_le ((lag (qv n j)).2.2.1 ^ 2)
  have z4 := Nat.zero_le ((lag (qv n j)).2.2.2 ^ 2)
  have ha' := hlt (lag (qv n j)).1 (by linarith)
  have hb' := hlt (lag (qv n j)).2.1 (by linarith)
  have hc' := hlt (lag (qv n j)).2.2.1 (by linarith)
  have hd' := hlt (lag (qv n j)).2.2.2 (by linarith)
  have hsq : sqs (lv n j) = (lag (qv n j)).1 ^ 2 + (lag (qv n j)).2.1 ^ 2 +
      (lag (qv n j)).2.2.1 ^ 2 + (lag (qv n j)).2.2.2 ^ 2 + bv n j ^ 2 + sqs (fv n j) := by
    simp only [lv, sqs, List.map_append, List.sum_append, List.map_cons, List.sum_cons,
      List.map_nil, List.sum_nil]
    ring
  refine ⟨?_, ?_, ?_, ?_, ?_, hs3⟩
  · simp [lv, hfv, hFl]
  · intro x hx
    simp only [lv, List.cons_append, List.mem_cons, List.nil_append] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | hx
    · exact ⟨ha, ha'.le⟩
    · exact ⟨hb, hb'.le⟩
    · exact ⟨hc, hc'.le⟩
    · exact ⟨hd, hd'.le⟩
    · exact ⟨by omega, le_refl _⟩
    · rw [hfv] at hx
      exact ⟨(hFb x hx).1, le_trans (hFb x hx).2 (by omega)⟩
  · simp [lv]
  · rw [hsq, hfv]
    linarith
  · exact le_trans (Nat.le_self_pow (by norm_num) _) (le_trans hB2 (Nat.sub_le _ _))

/-- Every n >= 1942 has 6 partitions into seven positive squares with different largest
parts. -/
lemma big (n : ℕ) (hn : 1942 ≤ n) : 6 ≤ ways n := by
  have hs3 : 43 ≤ Nat.sqrt (n - 93) := Nat.le_sqrt'.mpr (by norm_num; omega)
  set L := (List.range 12).filter (fun j => (choice (n % 32) (bv n j % 16)).isSome)
    with hL
  have hLlen : 6 ≤ L.length := by
    have hw := window_all (n % 32) (Nat.mod_lt _ (by norm_num)) (Nat.sqrt (n - 93) % 16)
      (Nat.mod_lt _ (by norm_num))
    have e : L = (List.range 12).filter (fun j =>
        (choice (n % 32) ((Nat.sqrt (n - 93) % 16 + 16 * 12 - j) % 16)).isSome) := by
      rw [hL]
      apply List.filter_congr
      intro j hj
      have := List.mem_range.mp hj
      have h16 : bv n j % 16 = (Nat.sqrt (n - 93) % 16 + 16 * 12 - j) % 16 := by
        unfold bv
        omega
      rw [h16]
    rw [e]
    exact hw
  have hnd : L.Nodup := (List.nodup_range).filter _
  have hcard : L.toFinset.card = L.length := List.toFinset_card_of_nodup hnd
  calc 6 ≤ L.toFinset.card := by omega
    _ ≤ ways n := by
      unfold ways
      apply Finset.card_le_card_of_injOn (fun j => toSym (lv n j))
      · intro j hj
        have hj' : j ∈ L := List.mem_toFinset.mp hj
        rw [hL, List.mem_filter, List.mem_range] at hj'
        obtain ⟨h9, hb, -, hsum, -, -⟩ := construct n j hn hj'.1 hj'.2
        exact toSym_mem h9 (fun x hx => (hb x hx).1) hsum
      · intro j hj j' hj' h
        have hj1 : j ∈ L := List.mem_toFinset.mp hj
        have hj2 : j' ∈ L := List.mem_toFinset.mp hj'
        rw [hL, List.mem_filter, List.mem_range] at hj1 hj2
        obtain ⟨h91, hb1, hm1, -, -, -⟩ := construct n j hn hj1.1 hj1.2
        obtain ⟨h92, hb2, hm2, -, -, -⟩ := construct n j' hn hj2.1 hj2.2
        have hm : (lv n j : Multiset ℕ) = (lv n j' : Multiset ℕ) := by
          rw [← toSym_val h91, ← toSym_val h92]
          exact congrArg Subtype.val h
        by_contra hne
        rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
        · have hmem : bv n j ∈ lv n j' := by
            rw [← Multiset.mem_coe, ← hm, Multiset.mem_coe]
            exact hm1
          have := (hb2 _ hmem).2
          unfold bv at this
          omega
        · have hmem : bv n j' ∈ lv n j := by
            rw [← Multiset.mem_coe, hm, Multiset.mem_coe]
            exact hm2
          have := (hb1 _ hmem).2
          unfold bv at this
          omega

/-! ### The terms -/

/-- The terms below 69, and every n >= 69. -/
def pb (n : ℕ) : Bool :=
  n == 55 || n == 58 || n == 61 || n == 63 || n == 64 || n == 66 || n == 67 || decide (69 ≤ n)

theorem small_check : ∀ n < 69,
    (pb n = true → okGroup n ((gen 7 7 n).take 6) = true) ∧
      (pb n = false → (gen 7 7 n).length < 6) := by
  decide +kernel

theorem mem_S_iff (n : ℕ) : n ∈ S ↔ pb n = true := by
  show 6 ≤ ways n ↔ _
  rcases Nat.lt_or_ge n 69 with h | h
  · obtain ⟨h1, h2⟩ := small_check n h
    cases hp : pb n
    · have := (ways_le_gen h).trans_lt (h2 hp)
      constructor
      · intro h6
        omega
      · intro h'
        exact absurd h' (by simp)
    · exact ⟨fun _ => rfl, fun _ => ways_ge_of_okGroup (h1 hp)⟩
  · have hp : pb n = true := by simp [pb, h]
    refine ⟨fun _ => hp, fun _ => ?_⟩
    rcases Nat.lt_or_ge n 1942 with h2 | h2
    · exact mid n h h2
    · exact big n h2

lemma count_pb (t : ℕ) : Nat.count (fun n => pb n = true) (69 + t) = 7 + t := by
  induction t with
  | zero => decide
  | succ t ih =>
    rw [show 69 + (t + 1) = 69 + t + 1 by ring, Nat.count_succ, ih]
    have : pb (69 + t) = true := by simp [pb]
    rw [if_pos this]
    ring

lemma nth_S : Nat.nth (fun m => m ∈ S) = Nat.nth (fun n => pb n = true) := by
  congr 1
  funext n
  exact propext (mem_S_iff n)

lemma a_ge (n : ℕ) (hn : 8 ≤ n) : a n = n + 61 := by
  unfold a
  rw [nth_S]
  have h := Nat.nth_count (p := fun n => pb n = true) (n := 69 + (n - 8)) (by simp [pb])
  rw [count_pb] at h
  rw [show n - 1 = 7 + (n - 8) by omega, h]
  omega

lemma a_small : a 1 = 55 ∧ a 2 = 58 ∧ a 3 = 61 ∧ a 4 = 63 ∧ a 5 = 64 ∧ a 6 = 66 ∧ a 7 = 67 := by
  unfold a
  rw [nth_S]
  have c : ∀ m k : ℕ, pb m = true → Nat.count (fun n => pb n = true) m = k →
      Nat.nth (fun n => pb n = true) k = m := fun m k hm hk => hk ▸ Nat.nth_count hm
  exact ⟨c 55 0 rfl (by decide), c 58 1 rfl (by decide), c 61 2 rfl (by decide), c 63 3 rfl (by decide), c 64 4 rfl (by decide), c 66 5 rfl (by decide), c 67 6 rfl (by decide)⟩

/-- Controls: the first 9 terms, as in the entry's data. -/
theorem controls : a 1 = 55 ∧ a 2 = 58 ∧ a 3 = 61 ∧ a 4 = 63 ∧ a 5 = 64 ∧ a 6 = 66 ∧ a 7 = 67 ∧ a 8 = 69 ∧ a 9 = 70 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := a_small
  exact ⟨h1, h2, h3, h4, h5, h6, h7, a_ge 8 le_rfl, a_ge 9 (by norm_num)⟩

theorem recurrence (n : ℕ) (hn : 9 < n) : (a n : ℤ) = 2 * a (n - 1) - a (n - 2) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 10 := ⟨n - 10, by omega⟩
  rw [show m + 10 - 1 = m + 9 by omega, show m + 10 - 2 = m + 8 by omega,
    a_ge (m + 10) (by omega), a_ge (m + 9) (by omega), a_ge (m + 8) (by omega)]
  push_cast
  ring

theorem gf : PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * (X - 1) ^ 2 =
    X * (-X ^ 8 + X ^ 7 - X ^ 6 + X ^ 5 - X ^ 4 - X ^ 3 - 52 * X + 55) := by
  set A : ℤ⟦X⟧ := PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) with hA
  have e1 : A * (X - 1) ^ 2 = A - A * X ^ 1 - A * X ^ 1 + A * X ^ 2 := by ring
  have e2 : (X : ℤ⟦X⟧) * (-X ^ 8 + X ^ 7 - X ^ 6 + X ^ 5 - X ^ 4 - X ^ 3 - 52 * X + 55) =
      -X ^ 9 + X ^ 8 - X ^ 7 + X ^ 6 - X ^ 5 - X ^ 4 - C 52 * X ^ 2 + C 55 * X ^ 1 := by
    simp only [map_ofNat]
    ring
  rw [e1, e2]
  ext n
  have hc : ∀ k, coeff k A = if k = 0 then (0 : ℤ) else a k := fun k => by rw [hA, coeff_mk]
  simp only [map_add, map_sub, map_neg, coeff_C_mul, coeff_X_pow, coeff_mul_X_pow', hc, coeff_C]
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := controls
  rcases Nat.lt_or_ge n 10 with hn | hn
  · interval_cases n <;> simp [h1, h2, h3, h4, h5, h6, h7, h8, h9]
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 10 := ⟨n - 10, by omega⟩
    have e : ∀ k, 8 ≤ k → (a k : ℤ) = k + 61 := fun k hk => by
      rw [a_ge k hk]
      push_cast
      ring
    simp only [show m + 10 - 1 = m + 9 by omega, show m + 10 - 2 = m + 8 by omega,
      show ¬ m + 10 = 0 by omega, show ¬ m + 9 = 0 by omega, show ¬ m + 8 = 0 by omega,
      show 1 ≤ m + 10 by omega, show 2 ≤ m + 10 by omega, if_true, if_false,
      show ¬ m + 10 = 1 by omega, show ¬ m + 10 = 2 by omega, show ¬ m + 10 = 3 by omega, show ¬ m + 10 = 4 by omega, show ¬ m + 10 = 5 by omega, show ¬ m + 10 = 6 by omega, show ¬ m + 10 = 7 by omega, show ¬ m + 10 = 8 by omega, show ¬ m + 10 = 9 by omega]
    rw [e (m + 10) (by omega), e (m + 9) (by omega), e (m + 8) (by omega)]
    push_cast
    ring

/-- Wu's conjectures: the recurrence for n > 9 and the generating function. -/
theorem conjecture :
    (∀ n : ℕ, 9 < n → (a n : ℤ) = 2 * a (n - 1) - a (n - 2)) ∧
      PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * (X - 1) ^ 2 =
        X * (-X ^ 8 + X ^ 7 - X ^ 6 + X ^ 5 - X ^ 4 - X ^ 3 - 52 * X + 55) :=
  ⟨recurrence, gf⟩


end OMA.S_oeis_a345483

theorem OMA.solution : type_of% @OMA.S_oeis_a345483.main :=
  OMA.S_oeis_a345483.conjecture
