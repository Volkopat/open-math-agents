import OMAStatements.S_oeis_a345503

namespace OMA.S_oeis_a345503

open PowerSeries




/-! ### Lower bounds from explicit lists -/

/-- The sum of the squares of a list. -/
def sqs (l : List ℕ) : ℕ := (l.map (· ^ 2)).sum

/-- A witness for n: nine positive entries, nonincreasing, squares summing to n. -/
def valid (n : ℕ) (l : List ℕ) : Bool :=
  l.length == 9 && l.all (fun x => decide (1 ≤ x)) && sqs l == n &&
    decide (l.Pairwise (· ≥ ·))

/-- Six distinct witnesses for n. -/
def okGroup (n : ℕ) (ls : List (List ℕ)) : Bool :=
  ls.length == 6 && ls.all (valid n) && decide ls.Nodup

lemma le_sqs {l : List ℕ} {x : ℕ} (hx : x ∈ l) : x ^ 2 ≤ sqs l := by
  unfold sqs
  exact List.le_sum_of_mem (List.mem_map_of_mem hx)

/-- The multiset of a list of length nine, as an element of `Sym ℕ 9`. -/
def toSym (l : List ℕ) : Sym ℕ 9 :=
  if h : l.length = 9 then Sym.mk (l : Multiset ℕ) (by simpa using h) else Sym.replicate 9 0

lemma toSym_val {l : List ℕ} (h : l.length = 9) :
    ((toSym l : Sym ℕ 9) : Multiset ℕ) = (l : Multiset ℕ) := by
  unfold toSym
  rw [dif_pos h]
  rfl

lemma valid_spec {n : ℕ} {l : List ℕ} (h : valid n l = true) :
    l.length = 9 ∧ (∀ x ∈ l, 1 ≤ x) ∧ sqs l = n ∧ l.Pairwise (· ≥ ·) := by
  simp only [valid, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

/-- A list of nine positive entries with squares summing to n gives a point of the count. -/
lemma toSym_mem {n : ℕ} {l : List ℕ} (h9 : l.length = 9) (hpos : ∀ x ∈ l, 1 ≤ x)
    (hsum : sqs l = n) :
    toSym l ∈ ((Finset.Icc 1 n).sym 9).filter
      (fun s : Sym ℕ 9 => ((s : Multiset ℕ).map (· ^ 2)).sum = n) := by
  rw [Finset.mem_filter]
  refine ⟨?_, ?_⟩
  · rw [Finset.mem_sym_iff]
    intro x hx
    have hx' : x ∈ ((toSym l : Sym ℕ 9) : Multiset ℕ) := hx
    rw [toSym_val h9, Multiset.mem_coe] at hx'
    refine Finset.mem_Icc.mpr ⟨hpos x hx', ?_⟩
    have := le_sqs hx'
    have : x ≤ x ^ 2 := Nat.le_self_pow (by norm_num) x
    omega
  · rw [toSym_val h9, Multiset.map_coe, Multiset.sum_coe]
    exact hsum

lemma ways_ge_of_okGroup {n : ℕ} {ls : List (List ℕ)} (h : okGroup n ls = true) :
    6 ≤ ways n := by
  simp only [okGroup, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hlen, hall⟩, hnd⟩ := h
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

/-! ### Witnesses for 65 <= n < 473, found by search -/

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
  | n, t + 1 => okGroup n (sr 99 9 21 n [] []) && chk (n + 1) t

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

lemma mid (n : ℕ) (h1 : 65 ≤ n) (h2 : n < 473) : 6 ≤ ways n :=
  chk_spec 408 65 (by decide +kernel) n h1 h2

/-! ### Complete lists below 65 -/

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

lemma ways_le_gen {n : ℕ} (hn : n < 65) : ways n ≤ (gen 9 7 n).length := by
  unfold ways
  calc _ ≤ (gen 9 7 n).toFinset.card := by
        apply Finset.card_le_card_of_injOn
          (fun s : Sym ℕ 9 => (s : Multiset ℕ).sort (· ≥ ·))
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
    _ ≤ (gen 9 7 n).length := List.toFinset_card_le _

/-! ### Every n >= 473 -/

/-- Four positive integers whose squares sum to r mod 8, for r < 8. -/
def fill (r : ℕ) : List ℕ :=
  match r with
  | 0 => [2, 2, 2, 2]
  | 1 => [4, 2, 2, 1]
  | 2 => [2, 2, 1, 1]
  | 3 => [4, 1, 1, 1]
  | 4 => [1, 1, 1, 1]
  | 5 => [2, 2, 2, 1]
  | 6 => [4, 2, 1, 1]
  | _ => [2, 1, 1, 1]

lemma fill_spec (r : ℕ) (hr : r < 8) :
    (fill r).length = 4 ∧ (∀ x ∈ fill r, 1 ≤ x ∧ x ≤ 4) ∧ sqs (fill r) % 8 = r ∧
      4 ≤ sqs (fill r) ∧ sqs (fill r) ≤ 25 := by
  interval_cases r <;> decide

lemma three_sq (x y z : ℕ) : (x ^ 2 + y ^ 2 + z ^ 2) % 8 ≠ 7 := by
  intro h
  have key : ∀ a b c : ZMod 8, a ^ 2 + b ^ 2 + c ^ 2 ≠ 7 := by decide
  apply key x y z
  have : ((x ^ 2 + y ^ 2 + z ^ 2 : ℕ) : ZMod 8) = ((7 : ℕ) : ZMod 8) :=
    (ZMod.natCast_eq_natCast_iff' _ _ 8).mpr (by rw [h])
  push_cast at this
  exact this

lemma four_pos {a b c d Q : ℕ} (h : a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = Q) (hQ : Q % 8 = 7) :
    1 ≤ a ∧ 1 ≤ b ∧ 1 ≤ c ∧ 1 ≤ d := by
  refine ⟨Nat.one_le_iff_ne_zero.mpr ?_, Nat.one_le_iff_ne_zero.mpr ?_,
    Nat.one_le_iff_ne_zero.mpr ?_, Nat.one_le_iff_ne_zero.mpr ?_⟩ <;> rintro rfl
  · exact three_sq b c d (by rw [← hQ, ← h]; simp)
  · exact three_sq a c d (by rw [← hQ, ← h]; simp)
  · exact three_sq a b d (by rw [← hQ, ← h]; simp)
  · exact three_sq a b c (by rw [← hQ, ← h]; simp)

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
def bv (n j : ℕ) : ℕ := Nat.sqrt (n - 32) - j

/-- The residue class of the filler. -/
def rv (n j : ℕ) : ℕ := (n + 1 + 7 * bv n j ^ 2) % 8

/-- The part that Lagrange writes as four squares. -/
def qv (n j : ℕ) : ℕ := n - bv n j ^ 2 - sqs (fill (rv n j))

/-- The j-th partition of n, as a list. -/
noncomputable def lv (n j : ℕ) : List ℕ :=
  [(lag (qv n j)).1, (lag (qv n j)).2.1, (lag (qv n j)).2.2.1, (lag (qv n j)).2.2.2, bv n j] ++
    fill (rv n j)

lemma sqrt_lt_of_sq_lt {v B : ℕ} (h : v ^ 2 < B ^ 2) : v < B := by
  by_contra hc
  push_neg at hc
  have := Nat.pow_le_pow_left hc 2
  omega

lemma arith {n b2 f r q : ℕ} (hn : 473 ≤ n) (hB2 : b2 ≤ n - 32) (hr : r = (n + 1 + 7 * b2) % 8)
    (hfm : f % 8 = r) (hf4 : 4 ≤ f) (hf25 : f ≤ 25) (hQ : q = n - b2 - f)
    (hn2 : n < 2 * b2 + 4) : 7 ≤ q ∧ q % 8 = 7 ∧ q < b2 ∧ q + b2 + f = n := by
  omega

lemma construct (n j : ℕ) (hn : 473 ≤ n) (hj : j < 6) :
    (lv n j).length = 9 ∧ (∀ x ∈ lv n j, 1 ≤ x ∧ x ≤ bv n j) ∧ bv n j ∈ lv n j ∧
      sqs (lv n j) = n ∧ bv n j ≤ n ∧ 21 ≤ Nat.sqrt (n - 32) := by
  obtain ⟨hfl, hfb, hfm, hf4, hf25⟩ := fill_spec (rv n j) (Nat.mod_lt _ (by norm_num))
  have hs1 : Nat.sqrt (n - 32) ^ 2 ≤ n - 32 := Nat.sqrt_le' _
  have hs2 : n - 32 < (Nat.sqrt (n - 32) + 1) ^ 2 := Nat.lt_succ_sqrt' _
  have hs3 : 21 ≤ Nat.sqrt (n - 32) := Nat.le_sqrt'.mpr (by norm_num; omega)
  have hB : bv n j = Nat.sqrt (n - 32) - j := rfl
  generalize hsdef : Nat.sqrt (n - 32) = s at hs1 hs2 hs3 hB
  have hB16 : 16 ≤ bv n j := by omega
  have hBs : bv n j ≤ s := by omega
  have hB2 : bv n j ^ 2 ≤ n - 32 := le_trans (Nat.pow_le_pow_left hBs 2) hs1
  have hn2 : n < 2 * bv n j ^ 2 + 4 := by
    have h1 : n < (s + 1) ^ 2 + 32 := by omega
    have h2 : (s + 1) ^ 2 ≤ (bv n j + 6) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have h3 : 16 * bv n j ≤ bv n j * bv n j := Nat.mul_le_mul_right _ hB16
    nlinarith
  obtain ⟨hQ7, hQmod, hdom, hsum⟩ := arith hn hB2 rfl hfm hf4 hf25 (rfl : qv n j = _) hn2
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
      (lag (qv n j)).2.2.1 ^ 2 + (lag (qv n j)).2.2.2 ^ 2 + bv n j ^ 2 + sqs (fill (rv n j)) := by
    simp only [lv, sqs, List.map_append, List.sum_append, List.map_cons, List.sum_cons,
      List.map_nil, List.sum_nil]
    ring
  refine ⟨?_, ?_, ?_, ?_, ?_, hs3⟩
  · simp [lv, hfl]
  · intro x hx
    simp only [lv, List.cons_append, List.mem_cons, List.nil_append] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | hx
    · exact ⟨ha, ha'.le⟩
    · exact ⟨hb, hb'.le⟩
    · exact ⟨hc, hc'.le⟩
    · exact ⟨hd, hd'.le⟩
    · exact ⟨by omega, le_refl _⟩
    · exact ⟨(hfb x hx).1, le_trans (hfb x hx).2 (by omega)⟩
  · simp [lv]
  · rw [hsq]
    linarith
  · exact le_trans (Nat.le_self_pow (by norm_num) _) (le_trans hB2 (Nat.sub_le _ _))

/-- Every n >= 473 has six partitions into nine positive squares, with six different largest
parts. -/
lemma big (n : ℕ) (hn : 473 ≤ n) : 6 ≤ ways n := by
  unfold ways
  rw [← Finset.card_range 6]
  apply Finset.card_le_card_of_injOn (fun j => toSym (lv n j))
  · intro j hj
    have hj' : j < 6 := by simpa using hj
    obtain ⟨h9, hb, -, hsum, -, -⟩ := construct n j hn hj'
    exact toSym_mem h9 (fun x hx => (hb x hx).1) hsum
  · intro j hj j' hj' h
    have hj1 : j < 6 := by simpa using hj
    have hj2 : j' < 6 := by simpa using hj'
    obtain ⟨h91, hb1, hm1, -, -, hs1⟩ := construct n j hn hj1
    obtain ⟨h92, hb2, hm2, -, -, -⟩ := construct n j' hn hj2
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

/-- The terms below 65, and every n >= 65. -/
def pb (n : ℕ) : Bool :=
  n == 48 || n == 56 || n == 57 || n == 59 || n == 60 || n == 62 || n == 63 || decide (65 ≤ n)

theorem small_check : ∀ n < 65,
    (pb n = true → okGroup n ((gen 9 7 n).take 6) = true) ∧
      (pb n = false → (gen 9 7 n).length < 6) := by
  decide +kernel

theorem mem_S_iff (n : ℕ) : n ∈ S ↔ pb n = true := by
  show 6 ≤ ways n ↔ _
  rcases Nat.lt_or_ge n 65 with h | h
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
    rcases Nat.lt_or_ge n 473 with h2 | h2
    · exact mid n h h2
    · exact big n h2

lemma count_pb (t : ℕ) : Nat.count (fun n => pb n = true) (65 + t) = 7 + t := by
  induction t with
  | zero => decide
  | succ t ih =>
    rw [show 65 + (t + 1) = 65 + t + 1 by ring, Nat.count_succ, ih]
    have : pb (65 + t) = true := by simp [pb]
    rw [if_pos this]
    ring

lemma nth_S : Nat.nth (fun m => m ∈ S) = Nat.nth (fun n => pb n = true) := by
  congr 1
  funext n
  exact propext (mem_S_iff n)

lemma a_ge (n : ℕ) (hn : 8 ≤ n) : a n = n + 57 := by
  unfold a
  rw [nth_S]
  have h := Nat.nth_count (p := fun n => pb n = true) (n := 65 + (n - 8)) (by simp [pb])
  rw [count_pb] at h
  rw [show n - 1 = 7 + (n - 8) by omega, h]
  omega

lemma a_small : a 1 = 48 ∧ a 2 = 56 ∧ a 3 = 57 ∧ a 4 = 59 ∧ a 5 = 60 ∧ a 6 = 62 ∧ a 7 = 63 := by
  unfold a
  rw [nth_S]
  have c : ∀ m k : ℕ, pb m = true → Nat.count (fun n => pb n = true) m = k →
      Nat.nth (fun n => pb n = true) k = m := fun m k hm hk => hk ▸ Nat.nth_count hm
  exact ⟨c 48 0 rfl (by decide), c 56 1 rfl (by decide), c 57 2 rfl (by decide),
    c 59 3 rfl (by decide), c 60 4 rfl (by decide), c 62 5 rfl (by decide),
    c 63 6 rfl (by decide)⟩

/-- Controls: the first nine terms 48, 56, 57, 59, 60, 62, 63, 65, 66, as in the entry. -/
theorem controls : a 1 = 48 ∧ a 2 = 56 ∧ a 3 = 57 ∧ a 4 = 59 ∧ a 5 = 60 ∧ a 6 = 62 ∧
    a 7 = 63 ∧ a 8 = 65 ∧ a 9 = 66 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := a_small
  exact ⟨h1, h2, h3, h4, h5, h6, h7, a_ge 8 le_rfl, a_ge 9 (by norm_num)⟩

theorem recurrence (n : ℕ) (hn : 9 < n) : (a n : ℤ) = 2 * a (n - 1) - a (n - 2) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 10 := ⟨n - 10, by omega⟩
  rw [show m + 10 - 1 = m + 9 by omega, show m + 10 - 2 = m + 8 by omega,
    a_ge (m + 10) (by omega), a_ge (m + 9) (by omega), a_ge (m + 8) (by omega)]
  push_cast
  ring

theorem gf : PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * (X - 1) ^ 2 =
    X * (-X ^ 8 + X ^ 7 - X ^ 6 + X ^ 5 - X ^ 4 + X ^ 3 - 7 * X ^ 2 - 40 * X + 48) := by
  set A : ℤ⟦X⟧ := PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) with hA
  have e1 : A * (X - 1) ^ 2 = A - A * X ^ 1 - A * X ^ 1 + A * X ^ 2 := by ring
  have e2 : (X : ℤ⟦X⟧) * (-X ^ 8 + X ^ 7 - X ^ 6 + X ^ 5 - X ^ 4 + X ^ 3 - 7 * X ^ 2 -
      40 * X + 48) = -X ^ 9 + X ^ 8 - X ^ 7 + X ^ 6 - X ^ 5 + X ^ 4 - C 7 * X ^ 3 -
      C 40 * X ^ 2 + C 48 * X ^ 1 := by
    rw [map_ofNat, map_ofNat, map_ofNat]
    ring
  rw [e1, e2]
  ext n
  have hc : ∀ k, coeff k A = if k = 0 then (0 : ℤ) else a k := fun k => by rw [hA, coeff_mk]
  simp only [map_add, map_sub, map_neg, coeff_C_mul, coeff_X_pow, coeff_mul_X_pow', hc, coeff_C]
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := controls
  rcases Nat.lt_or_ge n 10 with hn | hn
  · interval_cases n <;> simp [h1, h2, h3, h4, h5, h6, h7, h8, h9]
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 10 := ⟨n - 10, by omega⟩
    have e : ∀ k, 8 ≤ k → (a k : ℤ) = k + 57 := fun k hk => by
      rw [a_ge k hk]
      push_cast
      ring
    simp only [show m + 10 - 1 = m + 9 by omega, show m + 10 - 2 = m + 8 by omega,
      show ¬ m + 10 = 0 by omega, show ¬ m + 9 = 0 by omega, show ¬ m + 8 = 0 by omega,
      show 1 ≤ m + 10 by omega, show 2 ≤ m + 10 by omega, if_true, if_false,
      show ¬ m + 10 = 9 by omega, show ¬ m + 10 = 8 by omega, show ¬ m + 10 = 7 by omega,
      show ¬ m + 10 = 6 by omega, show ¬ m + 10 = 5 by omega, show ¬ m + 10 = 4 by omega,
      show ¬ m + 10 = 3 by omega, show ¬ m + 10 = 2 by omega, show ¬ m + 10 = 1 by omega]
    rw [e (m + 10) (by omega), e (m + 9) (by omega), e (m + 8) (by omega)]
    push_cast
    ring

/-- Wu's conjectures: the recurrence for n > 9 and the generating function. -/
theorem conjecture :
    (∀ n : ℕ, 9 < n → (a n : ℤ) = 2 * a (n - 1) - a (n - 2)) ∧
      PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * (X - 1) ^ 2 =
        X * (-X ^ 8 + X ^ 7 - X ^ 6 + X ^ 5 - X ^ 4 + X ^ 3 - 7 * X ^ 2 - 40 * X + 48) :=
  ⟨recurrence, gf⟩

end OMA.S_oeis_a345503

theorem OMA.solution : type_of% @OMA.S_oeis_a345503.main :=
  OMA.S_oeis_a345503.conjecture
