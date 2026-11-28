import OMAStatements.S_oeis_a084015
import Mathlib

/-!
# OEIS A084015 : largest n-digit palindromic multiple of n, no entry is zero

Port of the kernel-verified proof (0 sorry) from the DemosMathNT project
(`CIBLES\OEIS\11-PUBLIES\A084015\github-ready\`), inlined because a
submission may only import Mathlib besides OMAStatements. Sections, in
dependency order :
  - section A084013src : the palindromic-multiple toolkit of
    A084013.lean, cut right after its capstone `theorem A084013`
    (existence of an n-digit palindromic multiple of `n`, leading zeros
    ignored - the fragment the bound below needs). The trailing
    strict-suffix machinery of the source file is not needed here and
    is dropped ; its `import A077727` was already dead.
  - section A084015src : A084015.lean itself - existence of the
    maximum of the filtered finset (kernel-verified body verbatim).

Adaptations vs the kernel sources (same recipe as the sibling port
oeis-a084017, whose A084013src covers this dependency cone) :
  - local `import`s and file-scope `set_option autoImplicit` /
    `relaxedAutoImplicit` dropped (not allowed at top level) ;
  - `end DeadCount` relocated to just after `theorem A084013` to close
    the section that the source leaves open at file end (no `variable`
    inside, a pure marker).

The bridge is one `Finset.sup` bound : the corpus witness `N0` is an
n-digit palindromic multiple of `n` with `0 < N0` and `N0 < 10 ^ n`,
so it sits in the filtered finset that `a_val n` ranges over, and
`Finset.le_sup` gives `0 < N0 <= a_val n`.
-/

namespace OMA.A084015Port

section A084013src





theorem ofDigits_replicate_nine (t : ℕ) :
    Nat.ofDigits 10 (List.replicate t 9) = 10 ^ t - 1 := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [List.replicate_succ, Nat.ofDigits_cons, ih, pow_succ]
    have h : 1 ≤ 10 ^ t := Nat.one_le_pow t 10 (by norm_num)
    omega

theorem digits_ten_pow_sub_one (t : ℕ) (_ht : 0 < t) :
    Nat.digits 10 (10 ^ t - 1) = List.replicate t 9 := by
  rw [← ofDigits_replicate_nine t]
  apply Nat.digits_ofDigits 10 (by norm_num) _
  · intro l hl
    have : l = 9 := List.eq_of_mem_replicate hl
    omega
  · intro hne
    have h9 : (List.replicate t 9).getLast hne = 9 := by
      have := List.getLast_mem hne
      exact List.eq_of_mem_replicate this
    rw [h9]; norm_num


theorem dropWhile_self_of_head?_nine {l : List ℕ}
    (h : l.head? = some 9) : l.dropWhile (· = 0) = l := by
  cases l with
  | nil => simp at h
  | cons x xs =>
    simp only [List.head?_cons, Option.some.injEq] at h; subst h
    rw [List.dropWhile_cons_of_neg (by norm_num)]


theorem dropWhile_zero_prefix (z : ℕ) {l : List ℕ}
    (h : l.head? = some 9) :
    (List.replicate z 0 ++ l).dropWhile (· = 0) = l := by
  rw [List.dropWhile_append_of_pos
      (fun a ha => by simp [List.mem_replicate.mp ha])]
  exact dropWhile_self_of_head?_nine h


theorem pal_digits_large (m L t : ℕ) (hdvd : m ∣ 10 ^ t - 1) (ht : 0 < t)
    (hL : 2 * t ≤ L) :
    ∃ P : ℕ, m ∣ P ∧ Nat.digits 10 P =
      List.replicate t 9 ++ List.replicate (L - 2 * t) 0 ++
        List.replicate t 9 := by
  obtain ⟨k, rfl⟩ : ∃ k, L = 2 * t + k := ⟨L - 2 * t, by omega⟩
  have h2tk : 2 * t + k - 2 * t = k := by omega
  set X := 10 ^ t - 1 with hX
  have hXpos : 0 < X := by
    have : 1 < 10 ^ t := one_lt_pow₀ (by norm_num) ht.ne'
    omega
  have hdX : Nat.digits 10 X = List.replicate t 9 := digits_ten_pow_sub_one t ht
  have hP : X * (10 ^ (t + k) + 1) = X + 10 ^ (t + k) * X := by ring
  refine ⟨X * (10 ^ (t + k) + 1), hdvd.mul_right _, ?_⟩
  rw [h2tk]
  have h := Nat.digits_append_zeroes_append_digits (b := 10) (k := k)
      (m := X) (n := X) (by norm_num) hXpos
  rw [hdX, List.length_replicate] at h
  rw [hP, ← h]


theorem dropWhile_self_of_head_ne_zero {l : List ℕ} {x : ℕ}
    (h : l.head? = some x) (hx : x ≠ 0) :
    l.dropWhile (· = 0) = l := by
  cases l with
  | nil => simp at h
  | cons y ys =>
    simp only [List.head?_cons, Option.some.injEq] at h; subst h
    rw [List.dropWhile_cons_of_neg (by simp [hx])]


theorem dropWhile_zero_prefix' (z : ℕ) {l : List ℕ} {x : ℕ}
    (h : l.head? = some x) (hx : x ≠ 0) :
    (List.replicate z 0 ++ l).dropWhile (· = 0) = l := by
  rw [List.dropWhile_append_of_pos
      (fun a ha => by simp [List.mem_replicate.mp ha])]
  exact dropWhile_self_of_head_ne_zero h hx


theorem pal_head?_ne_zero {l : List ℕ} (hp : List.Palindrome l)
    (hgl : l.getLast? ≠ some 0) : l.head? ≠ some 0 := by
  rw [List.Palindrome.iff_reverse_eq] at hp
  have h : l.head? = l.getLast? := by
    conv_lhs => rw [← hp]
    exact List.head?_reverse
  rw [h]; exact hgl


theorem digits_getLast?_ne_zero (P : ℕ) (hP : 0 < P) :
    (Nat.digits 10 P).getLast? ≠ some 0 := by
  have hne : Nat.digits 10 P ≠ [] := Nat.digits_ne_nil_iff_ne_zero.mpr hP.ne'
  have hg := Nat.getLast_digit_ne_zero 10 hP.ne'
  rw [List.getLast?_eq_some_getLast hne]
  simp [hg]


theorem strict_to_relaxed (N : ℕ) (hN : 0 < N)
    (hpal : List.Palindrome (Nat.digits 10 N)) :
    List.Palindrome ((Nat.digits 10 N).dropWhile (· = 0)) := by
  have hgl : (Nat.digits 10 N).getLast? ≠ some 0 :=
    digits_getLast?_ne_zero N hN
  have hh : (Nat.digits 10 N).head? ≠ some 0 := pal_head?_ne_zero hpal hgl
  cases hx : (Nat.digits 10 N).head? with
  | none =>
    exfalso
    rw [List.head?_eq_none_iff] at hx
    exact (Nat.digits_ne_nil_iff_ne_zero.mpr hN.ne') hx
  | some x =>
    have hd : (Nat.digits 10 N).dropWhile (· = 0) = Nat.digits 10 N :=
      dropWhile_self_of_head_ne_zero hx (by
        intro h0; rw [h0] at hx; exact hh hx)
    rwa [hd]

open scoped Pointwise


theorem mem_finset_sum {ι α : Type*} [DecidableEq ι] [DecidableEq α]
    [AddCommMonoid α] {s : Finset ι} {f : ι → Finset α} {x : α} :
    x ∈ s.sum f ↔ ∃ g : ι → α, (∀ i ∈ s, g i ∈ f i) ∧ s.sum g = x := by
  induction s using Finset.induction generalizing x with
  | empty =>
    rw [Finset.sum_empty]
    constructor
    · intro hx
      have hx0 : x = 0 := Finset.mem_singleton.mp hx
      subst hx0
      exact ⟨0, by simp, by simp⟩
    · rintro ⟨g, -, hx⟩
      exact Finset.mem_singleton.mpr hx.symm
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    constructor
    · intro hx
      rw [Finset.mem_add] at hx
      obtain ⟨y, hy, z, hz, rfl⟩ := hx
      obtain ⟨g, hg, hzsum⟩ := ih.mp hz
      subst hzsum
      refine ⟨fun i => if i = a then y else g i, ?_, ?_⟩
      · intro i hi
        rw [Finset.mem_insert] at hi
        rcases hi with rfl | hi
        · simpa using hy
        · have hia : i ≠ a := fun h => ha (h ▸ hi)
          simpa [hia] using hg i hi
      · rw [Finset.sum_insert ha]
        simp only [ite_true]
        congr 1
        apply Finset.sum_congr rfl
        intro i hi
        have hia : i ≠ a := fun h => ha (h ▸ hi)
        simp [hia]
    · rintro ⟨g, hg, rfl⟩
      rw [Finset.sum_insert ha]
      apply Finset.add_mem_add (hg a (Finset.mem_insert_self a s))
      exact ih.mpr ⟨g, fun i hi => hg i (Finset.mem_insert_of_mem hi), rfl⟩


theorem exists_nsmul_eq_of_isUnit {m : ℕ} [NeZero m] {w : ZMod m}
    (hw : IsUnit w) (c : ZMod m) : ∃ k : ℕ, k • w = c := by
  obtain ⟨u, hu⟩ := hw
  refine ⟨(c * (u⁻¹ : (ZMod m)ˣ)).val, ?_⟩
  have hvw : ((u⁻¹ : (ZMod m)ˣ) : ZMod m) * w = 1 := by
    rw [← hu]; exact Units.inv_mul u
  rw [nsmul_eq_mul]
  have hcast : (((c * (u⁻¹ : (ZMod m)ˣ)).val : ℕ) : ZMod m) =
      c * (u⁻¹ : (ZMod m)ˣ) := by
    rw [ZMod.natCast_val]; exact ZMod.cast_id _ _
  rw [hcast, mul_assoc, hvw, mul_one]


theorem eq_univ_of_add_unit_closed {m : ℕ} [NeZero m] {w : ZMod m}
    (hw : IsUnit w) {B : Finset (ZMod m)} (hB : B.Nonempty)
    (hcl : ∀ b ∈ B, b + w ∈ B) : B = Finset.univ := by
  obtain ⟨b₀, hb₀⟩ := hB
  apply Finset.eq_univ_of_forall
  intro c
  obtain ⟨k, hk⟩ := exists_nsmul_eq_of_isUnit hw (c - b₀)
  have hstep : ∀ j : ℕ, b₀ + j • w ∈ B := by
    intro j
    induction j with
    | zero => simpa using hb₀
    | succ j ihj =>
      have h : b₀ + (j + 1) • w = (b₀ + j • w) + w := by
        rw [add_nsmul, one_nsmul]; abel
      rw [h]; exact hcl _ ihj
  have : c = b₀ + k • w := by rw [hk]; abel
  rw [this]; exact hstep k


theorem card_add_pair_unit {m : ℕ} [NeZero m] {w : ZMod m}
    (hw : IsUnit w) {B : Finset (ZMod m)} (hB : B.Nonempty) :
    min m (B.card + 1) ≤ (B + {0, w}).card := by
  have hBw : B + ({0, w} : Finset (ZMod m)) =
      B ∪ (Finset.image (· + w) B) := by
    ext x
    rw [Finset.mem_add, Finset.mem_union]
    constructor
    · rintro ⟨y, hy, z, hz, rfl⟩
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact Or.inl (by simpa using hy)
      · exact Or.inr (Finset.mem_image.mpr ⟨y, hy, rfl⟩)
    · rintro (hx | hx)
      · exact ⟨x, hx, 0, by simp, by simp⟩
      · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
        exact ⟨y, hy, w, by simp, rfl⟩
  rw [hBw]
  by_cases hsub : Finset.image (· + w) B ⊆ B
  · 
    have hcl : ∀ b ∈ B, b + w ∈ B := by
      intro b hb
      exact hsub (Finset.mem_image.mpr ⟨b, hb, rfl⟩)
    have huniv := eq_univ_of_add_unit_closed hw hB hcl
    rw [Finset.union_eq_left.mpr hsub, huniv, Finset.card_univ, ZMod.card]
    exact min_le_left _ _
  · 
    rw [Finset.not_subset] at hsub
    obtain ⟨y, hy, hyB⟩ := hsub
    have hy' : y ∈ B ∪ Finset.image (· + w) B :=
      Finset.mem_union_right _ hy
    have hcard : B.card + 1 ≤ (B ∪ Finset.image (· + w) B).card := by
      have h1 : Finset.card (insert y B) = B.card + 1 :=
        Finset.card_insert_of_notMem hyB
      have h2 : insert y B ⊆ B ∪ Finset.image (· + w) B :=
        Finset.insert_subset hy' (Finset.subset_union_left)
      rw [← h1]; exact Finset.card_le_card h2
    rcases lt_or_ge m (B.card + 1) with h | h
    · 
      exact le_trans (min_le_left _ _) (le_trans (le_of_lt h) hcard)
    · 
      exact le_trans (min_le_right _ _) hcard


theorem add_singleton_zero {m : ℕ} {B : Finset (ZMod m)} :
    B + ({0} : Finset (ZMod m)) = B := by
  ext x
  rw [Finset.mem_add]
  constructor
  · rintro ⟨y, hy, z, hz, rfl⟩
    simp only [Finset.mem_singleton] at hz
    rw [hz]; simpa using hy
  · intro hx
    exact ⟨x, hx, 0, Finset.mem_singleton_self 0, by simp⟩


theorem smul_range_succ {m : ℕ} {w : ZMod m} (r : ℕ) :
    (Finset.range (r + 2)).image (· • w) =
      (Finset.range (r + 1)).image (· • w) + ({0, w} : Finset (ZMod m)) := by
  ext x
  simp only [Finset.mem_image, Finset.mem_range, Finset.mem_add,
    Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨i, hi, rfl⟩
    rcases Nat.eq_zero_or_pos i with hi0 | hi1
    · exact ⟨0, ⟨0, by simp, by simp⟩, 0, Or.inl rfl,
        by simp [hi0]⟩
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi1.ne'
      refine ⟨j • w, ⟨j, by omega, rfl⟩, w, Or.inr rfl, ?_⟩
      rw [succ_nsmul]
  · rintro ⟨y, ⟨j, hj, rfl⟩, z, hz, rfl⟩
    rcases hz with rfl | rfl
    · exact ⟨j, by omega, by simp⟩
    · exact ⟨j + 1, by omega, by rw [succ_nsmul]⟩


theorem card_add_smul_range {m : ℕ} [NeZero m] {w : ZMod m}
    (hw : IsUnit w) {B : Finset (ZMod m)} (hB : B.Nonempty) (r : ℕ) :
    min m (B.card + r) ≤
      (B + (Finset.range (r + 1)).image (· • w)).card := by
  induction r with
  | zero =>
    have h1 : (Finset.range 1).image (· • w) = ({0} : Finset (ZMod m)) := by
      ext x
      simp only [Finset.mem_image, Finset.mem_range, Finset.mem_singleton]
      constructor
      · rintro ⟨i, hi, rfl⟩
        interval_cases i; simp
      · intro hx
        exact ⟨0, by simp, by simpa using hx.symm⟩
    rw [h1, add_singleton_zero]
    exact min_le_right _ _
  | succ r ih =>
    have hBr : (B + (Finset.range (r + 1)).image (· • w)).Nonempty := by
      obtain ⟨b, hb⟩ := hB
      refine ⟨b + 0 • w, Finset.mem_add.mpr ?_⟩
      exact ⟨b, hb, 0 • w,
        Finset.mem_image.mpr
          ⟨0, Finset.mem_range.mpr (Nat.succ_pos r), rfl⟩, rfl⟩
    rw [smul_range_succ]
    have hassoc : B + ((Finset.range (r + 1)).image (· • w) +
        ({0, w} : Finset (ZMod m))) =
        (B + (Finset.range (r + 1)).image (· • w)) + {0, w} :=
      (add_assoc _ _ _).symm
    rw [hassoc]
    have hstep := card_add_pair_unit hw hBr
    have hmin : min m (B.card + (r + 1)) ≤
        min m ((B + (Finset.range (r + 1)).image (· • w)).card + 1) := by
      by_cases hge : m ≤ (B + (Finset.range (r + 1)).image (· • w)).card + 1
      · rw [min_eq_left hge]; exact min_le_left _ _
      · have hlt : (B + (Finset.range (r + 1)).image (· • w)).card + 1 < m :=
          by omega
        rw [min_eq_right hlt.le]
        rcases lt_or_ge (B.card + r) m with h2 | h2
        · have hBT : B.card + r ≤
              (B + (Finset.range (r + 1)).image (· • w)).card := by
            have h := ih; rwa [min_eq_right h2.le] at h
          rw [min_eq_right (by omega)]
          omega
        · have hBT : m ≤
              (B + (Finset.range (r + 1)).image (· • w)).card := by
            have h := ih; rwa [min_eq_left h2] at h
          omega
    refine le_trans hmin ?_
    exact hstep


theorem card_add_smul_range' {m : ℕ} [NeZero m] {w : ZMod m}
    (hw : IsUnit w) {B : Finset (ZMod m)} (hB : B.Nonempty)
    {r : ℕ} (hr : 1 ≤ r) :
    min m (B.card + r - 1) ≤
      (B + (Finset.range r).image (· • w)).card := by
  have h := card_add_smul_range hw hB (r - 1)
  rw [Nat.sub_add_cancel hr] at h
  rwa [Nat.add_sub_assoc hr]


theorem zero_mem_interval {m : ℕ} (w : ZMod m) :
    (0 : ZMod m) ∈ (Finset.range 10).image (· • w) :=
  Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr (by norm_num), by simp⟩


theorem card_sum_intervals {m : ℕ} [NeZero m] {w : ℕ → ZMod m}
    {U : Finset ℕ} (hw : ∀ i ∈ U, IsUnit (w i)) :
    min m (1 + 9 * U.card) ≤
      (U.sum fun i => (Finset.range 10).image (· • w i)).card := by
  induction U using Finset.induction with
  | empty =>
    rw [Finset.sum_empty]
    have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr (NeZero.ne m)
    simp [hm1]
  | insert a U ha ih =>
    set S := U.sum fun i => (Finset.range 10).image (· • w i)
      with hS_def
    have hS : S.Nonempty := by
      refine ⟨0, ?_⟩
      rw [hS_def, mem_finset_sum]
      exact ⟨0, fun i _ => zero_mem_interval _, by simp⟩
    have hstep : min m (S.card + 9) ≤
        (S + (Finset.range 10).image (· • w a)).card := by
      have h := card_add_smul_range'
        (hw a (Finset.mem_insert_self a U)) hS (r := 10) (by norm_num)
      have h9 : S.card + 10 - 1 = S.card + 9 := by omega
      rwa [h9] at h
    have hih : min m (1 + 9 * U.card) ≤ S.card := by
      have h := ih (fun i hi => hw i (Finset.mem_insert_of_mem hi))
      rwa [hS_def]
    rw [Finset.card_insert_of_notMem ha, Finset.sum_insert ha,
      show (Finset.range 10).image (· • w a) + S =
        S + (Finset.range 10).image (· • w a) from add_comm _ _]
    have hmin : min m (1 + 9 * (U.card + 1)) ≤ min m (S.card + 9) := by
      by_cases hge : m ≤ S.card + 9
      · rw [min_eq_left hge]; exact min_le_left _ _
      · have hlt : S.card + 1 ≤ m := by omega
        rcases lt_or_ge (1 + 9 * U.card) m with h2 | h2
        · have hS2 : 1 + 9 * U.card ≤ S.card := by
            rwa [min_eq_right h2.le] at hih
          rw [min_eq_right (by omega)]; omega
        · have hS2 : m ≤ S.card := by
            rwa [min_eq_left h2] at hih
          omega
    exact le_trans hmin hstep

section DeadCount


theorem coprime_10_of_prime_pow {m p k : ℕ} (hp : p.Prime) (hk : 0 < k)
    (hm : m = p ^ k) (h10 : Nat.Coprime m 10) : Nat.Coprime 10 p := by
  have hpm : p ∣ m := by rw [hm]; exact dvd_pow_self p (by omega)
  exact Nat.coprime_comm.mp (h10.coprime_dvd_left hpm)



theorem dead_weight_eq_neg_one {m p k : ℕ} (hp : p.Prime) (hk : 0 < k)
    (hm : m = p ^ k) (h10 : Nat.Coprime m 10)
    {i : ℕ} (hi : i < (m - 1) / 2)
    (hpdvd : p ∣ 10 ^ i + 10 ^ (m - 1 - i)) :
    (10 : ZMod p) ^ (m - 1 - 2 * i) = -1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hcop_p : Nat.Coprime 10 p := coprime_10_of_prime_pow hp hk hm h10
  subst hm
  
  have hcast : ((10 ^ i + 10 ^ (p ^ k - 1 - i) : ℕ) : ZMod p) = 0 :=
    (CharP.cast_eq_zero_iff (ZMod p) p _).mpr hpdvd
  
  have hsplit : i + (p ^ k - 1 - 2 * i) = p ^ k - 1 - i := by omega
  have hnat : 10 ^ i * (1 + 10 ^ (p ^ k - 1 - 2 * i)) =
      10 ^ i + 10 ^ (p ^ k - 1 - i) := by
    rw [mul_add, mul_one, ← pow_add, hsplit]
  rw [← hnat] at hcast
  push_cast at hcast
  
  have h10ne : (10 : ZMod p) ≠ 0 := by
    have hpd : ¬ p ∣ 10 :=
      (hp.coprime_iff_not_dvd).mp (Nat.coprime_comm.mp hcop_p)
    exact fun h =>
      hpd ((CharP.cast_eq_zero_iff (ZMod p) p 10).mp (by exact_mod_cast h))
  have h1e : (10 : ZMod p) ^ (p ^ k - 1 - 2 * i) + 1 = 0 := by
    rw [add_comm]
    exact (mul_eq_zero.mp hcast).resolve_left (pow_ne_zero i h10ne)
  exact eq_neg_of_add_eq_zero_left h1e


theorem four_dvd_orderOf {p e : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {u : (ZMod p)ˣ} (he : 2 ∣ e) (hu : u ^ e = -1) : 4 ∣ orderOf u := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hne1 : (-1 : (ZMod p)ˣ) ≠ 1 := by
    intro h
    have h1 : (-1 : ZMod p) = 1 := by simpa using congrArg Units.val h
    have hr2 : ringChar (ZMod p) = 2 := neg_one_eq_one_iff.mp h1
    exact hp2 ((ZMod.ringChar_zmod_n p) ▸ hr2)
  have hpow1 : u ^ (2 * e) = 1 := by rw [pow_mul', hu]; simp
  have h2e : orderOf u ∣ 2 * e := orderOf_dvd_of_pow_eq_one hpow1
  have hne : ¬ orderOf u ∣ e :=
    mt orderOf_dvd_iff_pow_eq_one.mp (fun heq => hne1 ((heq ▸ hu).symm))
  set g := Nat.gcd (orderOf u) e with hg
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_left e (orderOf_pos u)
  have hs : orderOf u = g * (orderOf u / g) := by
    rw [mul_comm]; exact (Nat.div_mul_cancel (Nat.gcd_dvd_left _ _)).symm
  have ht : e = g * (e / g) := by
    rw [mul_comm]; exact (Nat.div_mul_cancel (Nat.gcd_dvd_right _ _)).symm
  have hcop : Nat.Coprime (orderOf u / g) (e / g) :=
    Nat.coprime_div_gcd_div_gcd hgpos
  have hs2 : orderOf u / g ∣ 2 := by
    have h1 : g * (orderOf u / g) ∣ 2 * (g * (e / g)) := by
      rw [← hs, ← ht]; exact h2e
    rcases h1 with ⟨c, hc⟩
    have h2 : orderOf u / g ∣ 2 * (e / g) := by
      refine ⟨c, Nat.eq_of_mul_eq_mul_left hgpos ?_⟩
      calc g * (2 * (e / g)) = 2 * (g * (e / g)) := by ring
        _ = g * (orderOf u / g) * c := hc
        _ = g * ((orderOf u / g) * c) := by ring
    exact hcop.dvd_of_dvd_mul_right h2
  have hs_eq : orderOf u / g = 2 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hs2 with h1 | h2
    · exfalso
      exact hne ⟨e / g, by rw [hs, h1, mul_one]; exact ht⟩
    · exact h2
  have htodd : Odd (e / g) := Nat.coprime_two_left.mp (hs_eq ▸ hcop)
  have hge : 2 ∣ g := by
    rcases Nat.even_or_odd g with hgE | hgO
    · exact even_iff_two_dvd.mp hgE
    · exfalso
      have hte : Odd e := ht.symm ▸ (hgO.mul htodd)
      exact (Nat.not_even_iff_odd.mpr hte) (even_iff_two_dvd.mpr he)
  obtain ⟨c, hc⟩ := hge
  exact ⟨c, by rw [hs, hs_eq, hc]; ring⟩


theorem dead_count {m p k : ℕ} (hp : p.Prime) (hk : 0 < k)
    (hm : m = p ^ k) (h10 : Nat.Coprime m 10) :
    ((Finset.range ((m - 1) / 2)).filter fun i =>
        p ∣ 10 ^ i + 10 ^ (m - 1 - i)).card
      ≤ (m - 1) / 4 + 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hcop_p : Nat.Coprime 10 p := coprime_10_of_prime_pow hp hk hm h10
  have hmodd : Odd m := Nat.coprime_two_right.mp (h10.coprime_dvd_right ⟨5, rfl⟩)
  have hp2 : p ≠ 2 := by
    intro h2
    have h2m : 2 ∣ m := by rw [hm, h2]; exact dvd_pow_self 2 (by omega)
    exact (Nat.not_even_iff_odd.mpr hmodd) (even_iff_two_dvd.mpr h2m)
  set u : (ZMod p)ˣ := ZMod.unitOfCoprime 10 hcop_p with hu
  set ord := orderOf u with hord
  set dead := (Finset.range ((m - 1) / 2)).filter (fun i =>
    p ∣ 10 ^ i + 10 ^ (m - 1 - i)) with hdead_def
  have hval : ∀ i ∈ dead, u ^ (m - 1 - 2 * i) = -1 := fun i hi => by
    have him := Finset.mem_filter.mp hi
    have h10e := dead_weight_eq_neg_one hp hk hm h10
      (Finset.mem_range.mp him.1) him.2
    rw [← Units.val_eq_neg_one, Units.val_pow_eq_pow_val, hu,
      ZMod.coe_unitOfCoprime]
    exact h10e
  by_cases hde : dead.Nonempty
  · 
    have hdiff : ∀ i₁ ∈ dead, ∀ i₂ ∈ dead, i₁ ≤ i₂ →
        ord ∣ 2 * (i₂ - i₁) := by
      intro i₁ h₁ i₂ h₂ hle
      have hb1 : 2 * i₁ ≤ m - 1 := by
        have := Finset.mem_range.mp (Finset.mem_filter.mp h₁).1; omega
      have hb2 : 2 * i₂ ≤ m - 1 := by
        have := Finset.mem_range.mp (Finset.mem_filter.mp h₂).1; omega
      have hpow : u ^ (m - 1 - 2 * i₁ - (m - 1 - 2 * i₂)) = 1 := by
        rw [pow_sub u (by omega : m - 1 - 2 * i₂ ≤ m - 1 - 2 * i₁),
          hval i₁ h₁, hval i₂ h₂]
        exact mul_inv_cancel (-1)
      have hd : ord ∣ m - 1 - 2 * i₁ - (m - 1 - 2 * i₂) :=
        orderOf_dvd_of_pow_eq_one hpow
      have heq : m - 1 - 2 * i₁ - (m - 1 - 2 * i₂) = 2 * (i₂ - i₁) := by omega
      rwa [heq] at hd
    have halve : ∀ x, ord ∣ 2 * x → ord / 2 ∣ x := by
      intro x ⟨c, hc⟩
      have h2o : 2 ∣ ord := dvd_trans ⟨2, rfl⟩ (by
        obtain ⟨i₀, hi₀⟩ := hde
        have he₀ : 2 ∣ m - 1 - 2 * i₀ := by
          rcases hmodd with ⟨a, ha⟩; exact ⟨a - i₀, by omega⟩
        exact four_dvd_orderOf hp hp2 he₀ (hval i₀ hi₀))
      refine ⟨c, Nat.eq_of_mul_eq_mul_left two_pos ?_⟩
      calc 2 * x = ord * c := hc
        _ = (2 * (ord / 2)) * c := by rw [Nat.mul_div_cancel' h2o]
        _ = 2 * (ord / 2 * c) := by ring
    have h4 : 4 ∣ ord := by
      obtain ⟨i₀, hi₀⟩ := hde
      have he₀ : 2 ∣ m - 1 - 2 * i₀ := by
        rcases hmodd with ⟨a, ha⟩; exact ⟨a - i₀, by omega⟩
      exact four_dvd_orderOf hp hp2 he₀ (hval i₀ hi₀)
    
    have hcong : ∀ {a b : ℕ}, a ∈ dead → b ∈ dead → a ≤ b →
        a / (ord / 2) = b / (ord / 2) → a = b := by
      intro a b ha hb hle hq
      have hd : ord / 2 ∣ b - a := halve _ (hdiff a ha b hb hle)
      have hm1 : a % (ord / 2) = b % (ord / 2) :=
        (Nat.modEq_iff_dvd' hle).mpr hd
      have h1e := Nat.div_add_mod a (ord / 2)
      have h2e := Nat.div_add_mod b (ord / 2)
      rw [hq, hm1] at h1e
      exact h1e.symm.trans h2e
    have hinj : (↑dead : Set ℕ).InjOn (fun i => i / (ord / 2)) := by
      intro i₁ h₁ i₂ h₂ hq
      rcases le_total i₁ i₂ with hle | hle
      · exact hcong (Finset.mem_coe.mp h₁) (Finset.mem_coe.mp h₂) hle hq
      · exact (hcong (Finset.mem_coe.mp h₂) (Finset.mem_coe.mp h₁) hle
          hq.symm).symm
    have hsub : Set.MapsTo (fun i => i / (ord / 2)) ↑dead
        ↑(Finset.range (((m - 1) / 2) / (ord / 2) + 1)) := by
      intro i hi
      have hi2 : i < (m - 1) / 2 :=
        Finset.mem_range.mp (Finset.mem_filter.mp (Finset.mem_coe.mp hi)).1
      have hord2 : 0 < ord / 2 := by
        have : 4 ≤ ord := Nat.le_of_dvd (orderOf_pos u) h4; omega
      have : i / (ord / 2) ≤ ((m - 1) / 2) / (ord / 2) :=
        Nat.div_le_div_right hi2.le
      simpa using Nat.lt_succ_of_le this
    have hcard := Finset.card_le_card_of_injOn _ hsub hinj
    rw [Finset.card_range] at hcard
    
    have hdiv : (m - 1) / 2 / (ord / 2) = (m - 1) / ord := by
      rw [Nat.div_div_eq_div_mul]
      congr 1
      exact Nat.mul_div_cancel' (dvd_trans ⟨2, rfl⟩ h4)
    rw [hdiv] at hcard
    have hle4 : (m - 1) / ord ≤ (m - 1) / 4 :=
      Nat.div_le_div_left (Nat.le_of_dvd (orderOf_pos u) h4) (by norm_num)
    omega
  · rw [Finset.not_nonempty_iff_eq_empty.mp hde, Finset.card_empty]
    exact Nat.zero_le _


section PalDiag


theorem pal_diag_extract {m p k : ℕ} (hp : p.Prime) (hk : 0 < k)
    (hm : m = p ^ k) (h10 : Nat.Coprime m 10) (hm21 : 21 ≤ m) :
    ∃ U : Finset ℕ, ∃ d : ℕ → ℕ,
      (∀ i ∈ U, d i < 10) ∧ U ⊆ Finset.range ((m - 1) / 2) ∧
      (0 : ℕ) ∉ U ∧
      ((U.sum fun i => d i • ((10 ^ i + 10 ^ (m - 1 - i) : ℕ) : ZMod m))
        = -((10 ^ 0 + 10 ^ (m - 1 - 0) : ℕ) : ZMod m)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hmpos : 0 < m := by omega
  haveI : NeZero m := ⟨hmpos.ne'⟩
  have hcop_p : Nat.Coprime 10 p := coprime_10_of_prime_pow hp hk hm h10
  have hmodd : Odd m := Nat.coprime_two_right.mp (h10.coprime_dvd_right ⟨5, rfl⟩)
  have hp2 : p ≠ 2 := by
    intro h2
    have h2m : 2 ∣ m := by rw [hm, h2]; exact dvd_pow_self 2 (by omega)
    exact (Nat.not_even_iff_odd.mpr hmodd) (even_iff_two_dvd.mpr h2m)
  set j := (m - 1) / 2 with hj
  set w : ℕ → ZMod m := fun i =>
    ((10 ^ i + 10 ^ (m - 1 - i) : ℕ) : ZMod m) with hw
  set dead := (Finset.range j).filter (fun i =>
    p ∣ 10 ^ i + 10 ^ (m - 1 - i)) with hdead_def
  set Ufull := (Finset.range j).filter (fun i =>
    ¬ p ∣ 10 ^ i + 10 ^ (m - 1 - i)) with hU_def
  have hcards : dead.card + Ufull.card = j := by
    rw [hdead_def, hU_def,
      Finset.card_filter_add_card_filter_not (s := Finset.range j)
        (p := fun i => p ∣ 10 ^ i + 10 ^ (m - 1 - i))]
    exact Finset.card_range j
  have hdead_bound : dead.card ≤ (m - 1) / 4 + 1 := by
    rw [hdead_def, hj]
    exact dead_count hp hk hm h10
  
  have hpow : (10 : ZMod p) ^ (m - 1) = 1 := by
    have hpm1 : p - 1 ∣ m - 1 := by
      have hmod : p ≡ 1 [MOD p - 1] :=
        ((Nat.modEq_iff_dvd' hp.one_lt.le).mpr (dvd_refl _)).symm
      have h := hmod.pow k
      rw [← hm, one_pow] at h
      exact (Nat.modEq_iff_dvd' (by omega : 1 ≤ m)).mp h.symm
    rcases hpm1 with ⟨t, ht⟩
    have hfermat : (10 : ZMod p) ^ (p - 1) = 1 := by
      have hmeq : 10 ^ Nat.totient p ≡ 1 [MOD p] :=
        Nat.ModEq.pow_totient hcop_p
      rw [Nat.totient_prime hp] at hmeq
      have hcast : ((10 ^ (p - 1) : ℕ) : ZMod p) = ((1 : ℕ) : ZMod p) :=
        (ZMod.natCast_eq_natCast_iff _ _ _).mpr hmeq
      push_cast at hcast
      exact hcast
    calc (10 : ZMod p) ^ (m - 1) = (10 : ZMod p) ^ ((p - 1) * t) := by
          rw [ht]
      _ = ((10 : ZMod p) ^ (p - 1)) ^ t := pow_mul _ _ _
      _ = 1 := by rw [hfermat, one_pow]
  
  have h0U : (0 : ℕ) ∈ Ufull := by
    rw [hU_def, Finset.mem_filter, Finset.mem_range]
    refine ⟨by omega, ?_⟩
    intro hpd
    have hcast : ((10 ^ 0 + 10 ^ (m - 1 - 0) : ℕ) : ZMod p) = 0 :=
      (CharP.cast_eq_zero_iff (ZMod p) p _).mpr hpd
    push_cast at hcast
    rw [Nat.sub_zero] at hcast
    rw [hpow] at hcast
    
    have h2d : p ∣ 2 := by
      have : ((2 : ℕ) : ZMod p) = 0 := by
        rw [← hcast]; push_cast; ring
      exact (CharP.cast_eq_zero_iff (ZMod p) p _).mp this
    exact hp2 ((Nat.dvd_prime Nat.prime_two).mp h2d |>.resolve_left hp.ne_one)
  
  set U := Ufull.erase 0 with hU'
  have hUcard : U.card = Ufull.card - 1 := Finset.card_erase_of_mem h0U
  have hUnit : ∀ i ∈ U, IsUnit (w i) := by
    intro i hi
    have hif := Finset.mem_filter.mp
      (Finset.mem_of_mem_erase hi)
    have hnp := hif.2
    have hc_p : (10 ^ i + 10 ^ (m - 1 - i)).Coprime p := by
      rw [Nat.coprime_comm, hp.coprime_iff_not_dvd]
      exact hnp
    have hc_m : (10 ^ i + 10 ^ (m - 1 - i)).Coprime (p ^ k) :=
      (Nat.coprime_pow_right_iff hk _ _).mpr hc_p
    rw [ZMod.isUnit_iff_coprime]
    exact hm.symm ▸ hc_m
  
  set S := U.sum fun i => (Finset.range 10).image (· • w i) with hS
  have hgrow : min m (1 + 9 * U.card) ≤ S.card := card_sum_intervals hUnit
  have hcover : 1 + 9 * U.card ≥ m := by
      omega
  have hmin : min m (1 + 9 * U.card) = m := min_eq_left hcover
  have hSm : m ≤ S.card := by
    rw [hmin] at hgrow
    exact hgrow
  have hS_univ : S = Finset.univ := by
    have hcard : S.card = Fintype.card (ZMod m) := by
      have hz : Fintype.card (ZMod m) = m := ZMod.card m
      have hle : S.card ≤ Fintype.card (ZMod m) :=
        Finset.card_le_univ S
      rw [hz] at hle
      omega
    exact Finset.eq_univ_of_card S hcard
  
  have hmem : (-(w 0)) ∈ S := hS_univ ▸ Finset.mem_univ _
  rw [hS] at hmem
  rw [mem_finset_sum] at hmem
  rcases hmem with ⟨g, hgmem, hgsum⟩
  have hd_ex : ∀ i, ∃ d : ℕ, d < 10 ∧
      (i ∈ U → d • w i = g i) := by
    intro i
    by_cases hi : i ∈ U
    · have h := hgmem i hi
      rw [Finset.mem_image] at h
      rcases h with ⟨d0, hd0, hd0eq⟩
      exact ⟨d0, Finset.mem_range.mp hd0, fun _ => hd0eq⟩
    · exact ⟨0, by norm_num, fun h' => absurd h' hi⟩
  choose d hd1 hd2 using hd_ex
  refine ⟨U, d, fun i hi => hd1 i, fun i hi =>
    Finset.mem_of_mem_erase hi |>
      (Finset.mem_filter.mp · |>.1), by
        rw [hU', Finset.mem_erase]; exact fun h => h.1 rfl, ?_⟩
  have hcongr : (U.sum fun i => d i • w i) = U.sum g :=
    Finset.sum_congr rfl (fun i hi => hd2 i hi)
  rw [hcongr]
  exact hgsum

end PalDiag


theorem ofDigits_append' {α : Type*} [Semiring α] (b : α) (l1 l2 : List ℕ) :
    Nat.ofDigits b (l1 ++ l2) =
      Nat.ofDigits b l1 + b ^ l1.length * Nat.ofDigits b l2 := by
  induction l1 with
  | nil =>
    show Nat.ofDigits b l2 =
        Nat.ofDigits b [] + b ^ (0 : ℕ) * Nat.ofDigits b l2
    rw [show Nat.ofDigits b [] = (0 : α) from rfl, pow_zero, one_mul,
      zero_add]
  | cons d t ih =>
    rw [List.cons_append]
    show (d : α) + b * Nat.ofDigits b (t ++ l2) =
      (d : α) + b * Nat.ofDigits b t
        + b ^ (t.length + 1) * Nat.ofDigits b l2
    rw [ih, mul_add, ← mul_assoc, ← pow_succ', ← add_assoc]

theorem ofDigits_singleton' {α : Type*} [Semiring α] (b : α) (d : ℕ) :
    Nat.ofDigits b [d] = (d : α) := by simp [Nat.ofDigits]


theorem ofDigits_zmod_range (m : ℕ) (g : ℕ → ℕ) (j : ℕ) :
    Nat.ofDigits (10 : ZMod m) ((List.range j).map g) =
      ∑ i ∈ Finset.range j, (g i : ZMod m) * (10 : ZMod m) ^ i := by
  induction j with
  | zero => simp [Nat.ofDigits]
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.map_singleton,
      ofDigits_append', ofDigits_singleton', List.length_map,
      List.length_range, Finset.sum_range_succ, ih]
    ring


theorem ofDigits_zmod_rev (m : ℕ) (g : ℕ → ℕ) (j : ℕ) :
    Nat.ofDigits (10 : ZMod m) ((List.range j).map g).reverse =
      ∑ i ∈ Finset.range j, (g i : ZMod m) * (10 : ZMod m) ^ (j - 1 - i) := by
  have hrw : ((List.range j).map g).reverse =
      (List.range j).map (fun i => g (j - 1 - i)) := by
    apply List.ext_getElem (by simp)
    intro i h1 h2
    simp only [List.getElem_reverse, List.length_map, List.length_range,
      List.getElem_map, List.getElem_range]
  rw [hrw, ofDigits_zmod_range m (fun i => g (j - 1 - i)) j]
  have hr : ∑ i ∈ Finset.range j,
      (g (j - 1 - i) : ZMod m) * (10 : ZMod m) ^ i =
      ∑ i ∈ Finset.range j,
        (g i : ZMod m) * (10 : ZMod m) ^ (j - 1 - i) := by
    rw [← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [Finset.mem_range] at hi
    rw [show j - 1 - (j - 1 - i) = i by omega]
  exact hr


theorem pal_diag {m p k : ℕ} (hp : p.Prime) (hk : 0 < k)
    (hm : m = p ^ k) (h10 : Nat.Coprime m 10) (hm21 : 21 ≤ m) :
    ∃ P : ℕ, m ∣ P ∧ (Nat.digits 10 P).length = m ∧
      List.Palindrome (Nat.digits 10 P) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hmodd : Odd m := Nat.coprime_two_right.mp (h10.coprime_dvd_right ⟨5, rfl⟩)
  obtain ⟨U, d, hd_lt, hUsub, h0U, hsum⟩ :=
    pal_diag_extract hp hk hm h10 hm21
  set j := (m - 1) / 2 with hj
  set g : ℕ → ℕ := fun i =>
    if i = 0 then 1 else if i ∈ U then d i else 0 with hg
  set Llo := (List.range j).map g with hLlo
  set L := Llo ++ [0] ++ Llo.reverse with hL
  have hg_lt : ∀ i, g i < 10 := by
    intro i
    by_cases h0 : i = 0
    · subst h0; simp [hg]
    · by_cases hiU : i ∈ U
      · have hgi : g i = d i := by simp [hg, h0, hiU]
        rw [hgi]; exact hd_lt i hiU
      · have hgi : g i = 0 := by simp [hg, h0, hiU]
        rw [hgi]; norm_num
  have hLlen : L.length = m := by
    rw [hL, List.length_append, List.length_append, List.length_singleton,
      List.length_reverse, hLlo, List.length_map, List.length_range]
    rcases hmodd with ⟨a, ha⟩; omega
  have hLlo_mem : ∀ x ∈ Llo, x < 10 := by
    intro x hx
    have hx2 : x ∈ (List.range j).map g := hx
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx2
    exact hg_lt i
  have hLlt : ∀ l ∈ L, l < 10 := by
    intro l hl
    have hl' : l ∈ (Llo ++ [0]) ++ Llo.reverse := hL ▸ hl
    rcases List.mem_append.mp hl' with hl | hl
    · rcases List.mem_append.mp hl with hl | hl
      · exact hLlo_mem l hl
      · have h0 : l = 0 := List.mem_singleton.mp hl
        subst h0; norm_num
    · exact hLlo_mem l (List.mem_reverse.mp hl)
  have hLlast : ∀ h : L ≠ [], L.getLast h ≠ 0 := by
    intro h
    show (Llo ++ [0] ++ Llo.reverse).getLast h ≠ 0
    have hrev_ne : Llo.reverse ≠ [] := by
      intro hcon
      have h0 : (Llo.reverse).length = 0 :=
        List.length_eq_zero_iff.mpr hcon
      rw [List.length_reverse, hLlo, List.length_map,
        List.length_range] at h0
      rcases hmodd with ⟨a, ha⟩; omega
    rw [List.getLast_append_of_right_ne_nil _ _ hrev_ne,
      List.getLast_reverse, List.head_eq_getElem]
    have hjpos : 0 < j := by rcases hmodd with ⟨a, ha⟩; omega
    show ((List.range j).map g)[0]'(
        by rw [List.length_map, List.length_range]; exact hjpos) ≠ 0
    rw [List.getElem_map, List.getElem_range]
    simp [hg]
  set P := Nat.ofDigits 10 L with hP
  have hdig : Nat.digits 10 P = L :=
    Nat.digits_ofDigits 10 (by norm_num) L hLlt hLlast
  refine ⟨P, ?_, by rw [hdig, hLlen], ?_⟩
  · have hPdec : Nat.ofDigits 10 L =
        Nat.ofDigits 10 Llo +
          10 ^ (j + 1) * Nat.ofDigits 10 Llo.reverse := by
      rw [hL, Nat.ofDigits_append, Nat.ofDigits_append_zero]
      have hlen' : (Llo ++ [0]).length = j + 1 := by
        rw [List.length_append, hLlo, List.length_map, List.length_range,
          List.length_singleton]
      rw [hlen']
    have hPz : ((Nat.ofDigits 10 L : ℕ) : ZMod m) = 0 := by
      rw [hPdec, hLlo]
      push_cast
      rw [ofDigits_zmod_range m g j, ofDigits_zmod_rev m g j]
      have hjoin : (∑ i ∈ Finset.range j, (g i : ZMod m) * (10 : ZMod m)^i)
          + (10 : ZMod m)^(j+1) *
            (∑ i ∈ Finset.range j, (g i : ZMod m) * (10 : ZMod m)^(j-1-i))
          = ∑ i ∈ Finset.range j,
              (g i : ZMod m) * ((10 : ZMod m)^i + (10 : ZMod m)^(m-1-i)) := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun i hi => ?_)
        rw [Finset.mem_range] at hi
        have hexp : j + 1 + (j - 1 - i) = m - 1 - i := by
          rcases hmodd with ⟨a, ha⟩; omega
        calc (g i : ZMod m) * (10 : ZMod m) ^ i
            + (10 : ZMod m) ^ (j + 1)
              * ((g i : ZMod m) * (10 : ZMod m) ^ (j - 1 - i))
            = (g i : ZMod m) * (10 : ZMod m) ^ i
              + (g i : ZMod m)
                * (10 : ZMod m) ^ (j + 1 + (j - 1 - i)) := by
              rw [pow_add]; ring
          _ = (g i : ZMod m)
              * ((10 : ZMod m) ^ i + (10 : ZMod m) ^ (m - 1 - i)) := by
              rw [hexp, ← mul_add]
      rw [hjoin]
      have hsplit : ∑ i ∈ Finset.range j,
          (g i : ZMod m) * ((10 : ZMod m)^i + (10 : ZMod m)^(m-1-i))
          = ∑ i ∈ (insert 0 U : Finset ℕ),
              (g i : ZMod m) * ((10 : ZMod m)^i + (10 : ZMod m)^(m-1-i)) := by
        symm
        apply Finset.sum_subset
        · apply Finset.insert_subset
          · rw [Finset.mem_range]
            rcases hmodd with ⟨a, ha⟩; omega
          · intro i hi
            exact hUsub hi
        · intro i _ hi
          have hne0 : i ≠ 0 := by
            intro h0; subst h0; exact hi (Finset.mem_insert_self 0 U)
          have hniU : i ∉ U := fun h' => hi (Finset.mem_insert_of_mem h')
          have hgi : g i = 0 := by simp [hg, hne0, hniU]
          rw [hgi]; simp
      rw [hsplit, Finset.sum_insert h0U]
      have hg0 : (g 0 : ZMod m) = 1 := by simp [hg]
      rw [hg0, one_mul]
      have hcongr : ∑ i ∈ U,
          (g i : ZMod m) * ((10 : ZMod m)^i + (10 : ZMod m)^(m-1-i))
          = U.sum fun i => d i • ((10 ^ i + 10 ^ (m - 1 - i) : ℕ) : ZMod m) := by
        refine Finset.sum_congr rfl (fun i hi => ?_)
        have hne : i ≠ 0 := fun h0 => h0U (h0 ▸ hi)
        have hgi : g i = d i := by simp [hg, hne, hi]
        rw [hgi, nsmul_eq_mul]
        push_cast
        ring
      rw [hcongr, hsum]
      push_cast
      ring
    haveI : NeZero m := ⟨by omega⟩
    exact (CharP.cast_eq_zero_iff (ZMod m) m _).mp hPz
  · rw [hdig, hL, List.Palindrome.iff_reverse_eq, List.reverse_append,
      List.reverse_append, List.reverse_reverse, List.reverse_singleton,
      List.append_assoc]


theorem exists_coprime_split {m : ℕ} (h10 : Nat.Coprime m 10)
    (hpp : ¬ IsPrimePow m) (hm : 2 ≤ m) :
    ∃ u v : ℕ, 3 ≤ u ∧ 3 ≤ v ∧ Nat.Coprime u v ∧ u * v = m := by
  have hn0 : m ≠ 0 := by omega
  have hnt : m.primeFactors.Nontrivial :=
    (Nat.not_isPrimePow_iff_nontrivial_of_two_le hm).mp hpp
  obtain ⟨p, hpm, q, hqm, hpq⟩ := hnt
  simp only [Finset.mem_coe, Nat.mem_primeFactors] at hpm hqm
  obtain ⟨hpp', hpd, -⟩ := hpm
  obtain ⟨hpq', hqd, -⟩ := hqm
  haveI : Fact p.Prime := ⟨hpp'⟩
  haveI : Fact q.Prime := ⟨hpq'⟩
  have hc10m : Nat.Coprime 10 m := h10.symm
  have hp_ne2 : p ≠ 2 := by
    intro h; subst h
    have h210 : (2 : ℕ) ∣ 10 := by norm_num
    have hc2 : Nat.Coprime m 2 :=
      (Nat.Coprime.coprime_dvd_left h210 hc10m).symm
    have hg : (2 : ℕ) ∣ Nat.gcd m 2 := Nat.dvd_gcd hpd (dvd_refl 2)
    have hc2' : Nat.gcd m 2 = 1 := hc2
    rw [hc2'] at hg; norm_num at hg
  have hq_ne2 : q ≠ 2 := by
    intro h; subst h
    have h210 : (2 : ℕ) ∣ 10 := by norm_num
    have hc2 : Nat.Coprime m 2 :=
      (Nat.Coprime.coprime_dvd_left h210 hc10m).symm
    have hg : (2 : ℕ) ∣ Nat.gcd m 2 := Nat.dvd_gcd hqd (dvd_refl 2)
    have hc2' : Nat.gcd m 2 = 1 := hc2
    rw [hc2'] at hg; norm_num at hg
  set a := padicValNat p m with ha_def
  set u := p ^ a with hu_def
  set v := m.divMaxPow p with hv_def
  have huv : v * u = m := Nat.divMaxPow_mul_pow_padicValNat p m
  have ha : 1 ≤ a := one_le_padicValNat_of_dvd hn0 hpd
  have hu3 : 3 ≤ u := by
    calc u = p ^ a := rfl
      _ ≥ p ^ 1 := pow_le_pow_right₀ (by have := hpp'.two_le; omega) ha
      _ = p := pow_one p
      _ ≥ 3 := by have := hpp'.two_le; omega
  have hqu : ¬ q ∣ u := by
    intro h
    have hqp : q ∣ p := hpq'.dvd_of_dvd_pow h
    have : q = p := (Nat.prime_dvd_prime_iff_eq hpq' hpp').mp hqp
    exact hpq this.symm
  have hqdvd : q ∣ v := by
    have h : q ∣ v * u := by rwa [huv]
    exact ((Nat.Prime.dvd_mul hpq').mp h).resolve_right hqu
  have hvpos : 0 < v := by
    rcases Nat.eq_zero_or_pos v with h | h
    · rw [h, zero_mul] at huv; exact absurd huv.symm hn0
    · exact h
  have hv3 : 3 ≤ v := le_trans
      (by have := hpq'.two_le; omega : 3 ≤ q) (Nat.le_of_dvd hvpos hqdvd)
  have hpcv : Nat.Coprime p v :=
    (hpp'.coprime_iff_not_dvd).mpr (Nat.not_dvd_divMaxPow hpp'.one_lt hn0)
  exact ⟨u, v, hu3, hv3, Nat.Coprime.pow_left a hpcv, by rw [mul_comm]; exact huv⟩


theorem totient_half_dvd_sub_one {m : ℕ} (h10 : Nat.Coprime m 10)
    (hpp : ¬ IsPrimePow m) (hm : 2 ≤ m) :
    m ∣ 10 ^ (m.totient / 2) - 1 := by
  obtain ⟨u, v, hu3, hv3, hcop, huv⟩ := exists_coprime_split h10 hpp hm
  have hudm : u ∣ m := ⟨v, huv.symm⟩
  have hvdm : v ∣ m := ⟨u, by rw [mul_comm]; exact huv.symm⟩
  have hc10u : Nat.Coprime 10 u :=
    (Nat.Coprime.coprime_dvd_left hudm h10).symm
  have hc10v : Nat.Coprime 10 v :=
    (Nat.Coprime.coprime_dvd_left hvdm h10).symm
  have hφm : m.totient = u.totient * v.totient := by
    rw [← huv]; exact Nat.totient_mul hcop
  obtain ⟨cv, hcv⟩ := Nat.totient_even (by omega : 2 < v)
  obtain ⟨cu, hcu⟩ := Nat.totient_even (by omega : 2 < u)
  set φu := u.totient
  set φv := v.totient
  have hφhalf : m.totient / 2 = φu * cv := by
    rw [hφm, hcv]
    have h1 : φu * (cv + cv) / 2 = φu * cv := by
      rw [show cv + cv = cv * 2 from by ring, ← mul_assoc,
        Nat.mul_div_cancel _ (by norm_num : 0 < 2)]
    exact h1
  have hφhalf' : m.totient / 2 = φv * cu := by
    rw [hφm, hcv, hcu]
    have h1 : (cu + cu) * (cv + cv) / 2 = (cv + cv) * cu := by
      have : (cu + cu) * (cv + cv) = ((cv + cv) * cu) * 2 := by ring
      rw [this, Nat.mul_div_cancel _ (by norm_num : 0 < 2)]
    exact h1
  have hMu : (10 : ℕ) ^ (m.totient / 2) ≡ 1 [MOD u] := by
    have h1 : (10 : ℕ) ^ φu ≡ 1 [MOD u] := Nat.ModEq.pow_totient hc10u
    rw [hφhalf, pow_mul]
    have := h1.pow cv
    simpa using this
  have hMv : (10 : ℕ) ^ (m.totient / 2) ≡ 1 [MOD v] := by
    have h1 : (10 : ℕ) ^ φv ≡ 1 [MOD v] := Nat.ModEq.pow_totient hc10v
    rw [hφhalf', pow_mul]
    have := h1.pow cu
    simpa using this
  have hle : 1 ≤ 10 ^ (m.totient / 2) := Nat.one_le_pow _ _ (by norm_num)
  have hdu : u ∣ 10 ^ (m.totient / 2) - 1 := (Nat.modEq_iff_dvd' hle).mp hMu.symm
  have hdv : v ∣ 10 ^ (m.totient / 2) - 1 := (Nat.modEq_iff_dvd' hle).mp hMv.symm
  have h := hcop.mul_dvd_of_dvd_of_dvd hdu hdv
  rwa [huv] at h



theorem wit013_spec (n : ℕ) (h1 : 1 ≤ n) (h23 : n ≤ 23)
    (h10 : ¬ 10 ∣ n) :
    ∃ N : ℕ, 0 < N ∧ n ∣ N ∧ (Nat.digits 10 N).length = n ∧
      List.Palindrome (Nat.digits 10 N) := by
  interval_cases n
  · exact ⟨1, by norm_num, by norm_num, by decide,
      List.Palindrome.iff_reverse_eq.mpr (by decide)⟩
  · exact ⟨22, by norm_num, by norm_num, by decide,
      List.Palindrome.iff_reverse_eq.mpr (by decide)⟩
  · exact ⟨111, by norm_num, by norm_num, by decide,
      List.Palindrome.iff_reverse_eq.mpr (by decide)⟩
  · exact ⟨2112, by norm_num, by norm_num, by decide,
      List.Palindrome.iff_reverse_eq.mpr (by decide)⟩
  · exact ⟨50005, by norm_num, by norm_num, by decide,
      List.Palindrome.iff_reverse_eq.mpr (by decide)⟩
  · exact ⟨201102, by norm_num, by norm_num, by decide,
      List.Palindrome.iff_reverse_eq.mpr (by decide)⟩
  · exact ⟨1002001, by norm_num, by norm_num, by decide,
      List.Palindrome.iff_reverse_eq.mpr (by decide)⟩
  · exact ⟨21100112, by norm_num, by norm_num, by decide,
      List.Palindrome.iff_reverse_eq.mpr (by decide)⟩
  · exact ⟨100070001, by norm_num, by norm_num, by decide,
      List.Palindrome.iff_reverse_eq.mpr (by decide)⟩
  · exact absurd (by decide : 10 ∣ 10) h10
  · exact ⟨10000200001, by norm_num, by norm_num, by decide,
      List.Palindrome.iff_reverse_eq.mpr (by decide)⟩
  · exact ⟨210000000012, by norm_num, by norm_num, by decide,
      List.Palindrome.iff_reverse_eq.mpr (by decide)⟩
  · exact ⟨1000029200001, by norm_num, by norm_num, by decide,
      List.Palindrome.iff_reverse_eq.mpr (by decide)⟩
  · exact ⟨20000055000002, by norm_num, by norm_num, by decide,
      List.Palindrome.iff_reverse_eq.mpr (by decide)⟩
  · exact ⟨500000020000005, by norm_num, by norm_num, by decide,
      List.Palindrome.iff_reverse_eq.mpr (by decide)⟩
  · exact ⟨2110000000000112, by norm_num, by norm_num, by decide,
      List.Palindrome.iff_reverse_eq.mpr (by decide)⟩
  · exact ⟨10000000200000001, by norm_num, by norm_num, by decide,
      List.Palindrome.iff_reverse_eq.mpr (by decide)⟩
  · exact ⟨200000007700000002, by norm_num, by norm_num, by decide,
      List.Palindrome.iff_reverse_eq.mpr (by decide)⟩
  · exact ⟨1000000002000000001, by norm_num, by norm_num, by decide,
      List.Palindrome.iff_reverse_eq.mpr (by decide)⟩
  · exact absurd (by decide : 10 ∣ 20) h10
  · exact ⟨100000000010000000001, by norm_num, by norm_num, by decide,
      List.Palindrome.iff_reverse_eq.mpr (by decide)⟩
  · exact ⟨2000000000000000000002, by norm_num, by norm_num, by decide,
      List.Palindrome.iff_reverse_eq.mpr (by decide)⟩
  · exact ⟨10000000000200000000001, by norm_num, by norm_num, by decide,
      List.Palindrome.iff_reverse_eq.mpr (by decide)⟩


theorem A084013_relaxed (n : ℕ) (hn : 1 ≤ n) (h10 : 10 ∣ n) :
    ∃ N : ℕ, 0 < N ∧ n ∣ N ∧ (Nat.digits 10 N).length = n ∧
      List.Palindrome ((Nat.digits 10 N).dropWhile (· = 0)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  set a := padicValNat 2 n
  set q1 := Nat.divMaxPow n 2
  set b := padicValNat 5 q1
  set m := Nat.divMaxPow q1 5
  have hn0 : n ≠ 0 := by omega
  have hq1 : q1 * 2 ^ a = n := Nat.divMaxPow_mul_pow_padicValNat 2 n
  have hmq : m * 5 ^ b = q1 := Nat.divMaxPow_mul_pow_padicValNat 5 q1
  have hq10 : q1 ≠ 0 := by
    intro h; rw [h, zero_mul] at hq1; exact hn0 hq1.symm
  have hdecomp : n = 2 ^ a * 5 ^ b * m := by
    rw [← hmq] at hq1; rw [← hq1]; ring
  have h2q1 : ¬ 2 ∣ q1 := Nat.not_dvd_divMaxPow (by norm_num) hn0
  have h5m : ¬ 5 ∣ m := Nat.not_dvd_divMaxPow (by norm_num) hq10
  have hmq1 : m ∣ q1 := ⟨5 ^ b, hmq.symm⟩
  have h2m : ¬ 2 ∣ m := fun h => h2q1 (h.trans hmq1)
  have h2 : Nat.Coprime m 2 :=
    ((Nat.prime_two.coprime_iff_not_dvd).mpr h2m).symm
  have h5 : Nat.Coprime m 5 :=
    ((Nat.prime_five.coprime_iff_not_dvd).mpr h5m).symm
  have hc10 : Nat.Coprime m 10 := by
    have hc : Nat.Coprime m (2 * 5) := Nat.Coprime.mul_right h2 h5
    rwa [show (2 : ℕ) * 5 = 10 from rfl] at hc
  have hm0 : m ≠ 0 := by
    intro hmz; rw [hmz, zero_mul] at hmq; exact hq10 hmq.symm
  have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
  have h2n : 2 ∣ n := (show 2 ∣ 10 from by norm_num).trans h10
  have h5n : 5 ∣ n := (show 5 ∣ 10 from by norm_num).trans h10
  have ha1 : 1 ≤ a := one_le_padicValNat_of_dvd hn0 h2n
  have hcop52 : Nat.Coprime 5 (2 ^ a) :=
    Nat.Coprime.pow_right a (by norm_num : Nat.Coprime 5 2)
  have h5q1 : 5 ∣ q1 := by
    have h5nq : 5 ∣ q1 * 2 ^ a := by rwa [hq1]
    exact hcop52.dvd_of_dvd_mul_right h5nq
  have hb1 : 1 ≤ b := one_le_padicValNat_of_dvd hq10 h5q1
  have hpa : a + 1 ≤ 2 ^ a := a.lt_two_pow_self
  have hpb : b + 1 ≤ 2 ^ b := b.lt_two_pow_self
  have h2a5 : 2 ^ a * 5 ≤ n := by
    have h1 : (5 : ℕ) ≤ 5 ^ b := by
      rw [← pow_one 5]; exact pow_le_pow_right₀ (by norm_num) hb1
    have h2 : 5 ≤ 5 ^ b * m := le_trans h1 (Nat.le_mul_of_pos_right _ hmpos)
    calc 2 ^ a * 5 ≤ 2 ^ a * (5 ^ b * m) := Nat.mul_le_mul_left _ h2
      _ = n := by rw [hdecomp]; ring
  have h5b2 : 5 ^ b * 2 ≤ n := by
    have h1 : (2 : ℕ) ≤ 2 ^ a := by
      rw [← pow_one 2]; exact pow_le_pow_right₀ (by norm_num) ha1
    have h2 : 2 ≤ 2 ^ a * m := le_trans h1 (Nat.le_mul_of_pos_right _ hmpos)
    calc 5 ^ b * 2 ≤ 5 ^ b * (2 ^ a * m) := Nat.mul_le_mul_left _ h2
      _ = n := by rw [hdecomp]; ring
  have h10m : 10 * m ≤ n := by
    calc 10 * m = (2 * 5) * m := by ring
      _ ≤ (2 ^ a * 5 ^ b) * m :=
          Nat.mul_le_mul_right _
            (Nat.mul_le_mul (pow_le_pow_right₀ (by norm_num : (1:ℕ) ≤ 2) ha1)
              (pow_le_pow_right₀ (by norm_num : (1:ℕ) ≤ 5) hb1))
      _ = n := by rw [hdecomp]
  have htpos : 0 < m.totient := Nat.totient_pos.mpr hmpos
  have hT : m ∣ 10 ^ m.totient - 1 := by
    have h1 : 1 ≤ 10 ^ m.totient := Nat.one_le_pow _ _ (by norm_num)
    exact (Nat.modEq_iff_dvd' h1).mp (Nat.ModEq.pow_totient hc10.symm).symm
  have htot : m.totient ≤ m := Nat.totient_le m
  have hbound : 2 * m.totient ≤ n - max a b := by
    have ha : (a + 1) * 5 ≤ n := le_trans (Nat.mul_le_mul_right _ hpa) h2a5
    have hb : (b + 1) * 2 ≤ n := le_trans
      (Nat.mul_le_mul_right _
        (le_trans hpb (Nat.pow_le_pow_left (by norm_num) b))) h5b2
    have hm10 : m * 10 ≤ n := by rw [mul_comm]; exact h10m
    omega
  obtain ⟨P, hmP, hdigP⟩ :=
    pal_digits_large m (n - max a b) m.totient hT htpos hbound
  have hPpos : 0 < P := by
    rcases Nat.eq_zero_or_pos P with h | h
    · rw [h] at hdigP; simp at hdigP; omega
    · exact h
  have hhead : (Nat.digits 10 P).head? = some 9 := by
    rw [hdigP]
    rw [show List.replicate m.totient 9 = 9 :: List.replicate (m.totient - 1) 9
        from by
          nth_rewrite 1 [(Nat.sub_add_cancel htpos).symm]
          rw [List.replicate_succ],
        List.cons_append]
    simp
  refine ⟨P * 10 ^ max a b, by positivity, ?_, ?_, ?_⟩
  · rw [hdecomp]
    have h2a : 2 ^ a ∣ 10 ^ max a b := by
      rw [show (10 : ℕ) = 2 * 5 from rfl, Nat.mul_pow]
      exact dvd_mul_of_dvd_left (pow_dvd_pow 2 (le_max_left a b)) _
    have h5b : 5 ^ b ∣ 10 ^ max a b := by
      rw [show (10 : ℕ) = 2 * 5 from rfl, Nat.mul_pow]
      exact dvd_mul_of_dvd_right (pow_dvd_pow 5 (le_max_right a b)) _
    have hc25 : Nat.Coprime (2 ^ a) (5 ^ b) :=
      Nat.Coprime.pow_right b (Nat.Coprime.pow_left a (by norm_num))
    have h25 : 2 ^ a * 5 ^ b ∣ P * 10 ^ max a b :=
      hc25.mul_dvd_of_dvd_of_dvd (dvd_mul_of_dvd_right h2a P)
        (dvd_mul_of_dvd_right h5b P)
    have hcR : Nat.Coprime (2 ^ a * 5 ^ b) m :=
      (Nat.Coprime.mul_right (Nat.Coprime.pow_right a h2)
        (Nat.Coprime.pow_right b h5)).symm
    exact hcR.mul_dvd_of_dvd_of_dvd h25 (dvd_mul_of_dvd_left hmP _)
  · rw [mul_comm, Nat.digits_base_pow_mul (by norm_num) hPpos,
        List.length_append, List.length_replicate, hdigP,
        List.length_append, List.length_append, List.length_replicate,
        List.length_replicate]
    omega
  · have hdN : Nat.digits 10 (P * 10 ^ max a b) =
        List.replicate (max a b) 0 ++ Nat.digits 10 P := by
      rw [mul_comm]; exact Nat.digits_base_pow_mul (by norm_num) hPpos
    rw [hdN, dropWhile_zero_prefix _ hhead, hdigP,
        List.Palindrome.iff_reverse_eq, List.reverse_append,
        List.reverse_append, List.reverse_replicate, List.reverse_replicate,
        List.append_assoc]


theorem A084013_strict (n : ℕ) (hn : 1 ≤ n) (h10 : ¬ 10 ∣ n) :
    ∃ N : ℕ, 0 < N ∧ n ∣ N ∧ (Nat.digits 10 N).length = n ∧
      List.Palindrome ((Nat.digits 10 N).dropWhile (· = 0)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  set a := padicValNat 2 n
  set q1 := Nat.divMaxPow n 2
  set b := padicValNat 5 q1
  set m := Nat.divMaxPow q1 5
  have hn0 : n ≠ 0 := by omega
  have hq1 : q1 * 2 ^ a = n := Nat.divMaxPow_mul_pow_padicValNat 2 n
  have hmq : m * 5 ^ b = q1 := Nat.divMaxPow_mul_pow_padicValNat 5 q1
  have hq10 : q1 ≠ 0 := by
    intro h; rw [h, zero_mul] at hq1; exact hn0 hq1.symm
  have hdecomp : n = 2 ^ a * 5 ^ b * m := by
    rw [← hmq] at hq1; rw [← hq1]; ring
  have h2q1 : ¬ 2 ∣ q1 := Nat.not_dvd_divMaxPow (by norm_num) hn0
  have h5m : ¬ 5 ∣ m := Nat.not_dvd_divMaxPow (by norm_num) hq10
  have hmq1 : m ∣ q1 := ⟨5 ^ b, hmq.symm⟩
  have hq1n : q1 ∣ n := ⟨2 ^ a, hq1.symm⟩
  have h2m : ¬ 2 ∣ m := fun h => h2q1 (h.trans hmq1)
  have h2 : Nat.Coprime m 2 :=
    ((Nat.prime_two.coprime_iff_not_dvd).mpr h2m).symm
  have h5 : Nat.Coprime m 5 :=
    ((Nat.prime_five.coprime_iff_not_dvd).mpr h5m).symm
  have hc10 : Nat.Coprime m 10 := by
    have hc : Nat.Coprime m (2 * 5) := Nat.Coprime.mul_right h2 h5
    rwa [show (2 : ℕ) * 5 = 10 from rfl] at hc
  have hm0 : m ≠ 0 := by
    intro hmz; rw [hmz, zero_mul] at hmq; exact hq10 hmq.symm
  have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
  have h2or5 : ¬ 2 ∣ n ∨ ¬ 5 ∣ n := by
    by_contra h
    push_neg at h
    have hcop : Nat.Coprime 2 5 := by decide
    have hd : (2 : ℕ) * 5 ∣ n :=
      Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop h.1 h.2
    rw [show (2 : ℕ) * 5 = 10 from rfl] at hd
    exact h10 hd
  have hab : max a b = a + b := by
    rcases h2or5 with h | h
    · have ha0 : a = 0 := padicValNat.eq_zero_of_not_dvd h
      simp [ha0]
    · have hb0 : b = 0 :=
        padicValNat.eq_zero_of_not_dvd (fun hd => h (hd.trans hq1n))
      simp [hb0]
  set z := a + b with hz
  set L := n - z with hL
  have h5b2b : 2 ^ b ≤ 5 ^ b := Nat.pow_le_pow_left (by norm_num) b
  have hpow : 2 ^ (a + b) ≤ n := by
    calc 2 ^ (a + b) = 2 ^ a * 2 ^ b := by rw [pow_add]
      _ ≤ 2 ^ a * 5 ^ b := Nat.mul_le_mul_left _ h5b2b
      _ ≤ 2 ^ a * (5 ^ b * m) :=
          Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_right _ hmpos)
      _ = n := by rw [hdecomp]; ring
  have hzpos : a + b < 2 ^ (a + b) := (a + b).lt_two_pow_self
  have hzn : z ≤ n := by
    have : a + b ≤ n := le_trans (Nat.le_of_lt hzpos) hpow
    omega
  have hL1 : 1 ≤ L := by omega
  by_cases hbig : 20 ≤ L
  · rcases Nat.eq_zero_or_pos (a + b) with hab0 | hab1
    · 
      have ha0 : a = 0 := by omega
      have hb0 : b = 0 := by omega
      have hnm : n = m := by
        have := hdecomp; rw [ha0, hb0] at this; simpa using this
      have hLm : L = m := by
        have hz0 : z = 0 := by omega
        omega
      have hm20 : m ≠ 20 := by
        intro h; rw [h] at hc10; norm_num [Nat.Coprime] at hc10
      have hm21 : 21 ≤ m := by omega
      by_cases hpp : IsPrimePow m
      · 
        obtain ⟨p, k, hp, hk, hpk⟩ := (isPrimePow_nat_iff m).mp hpp
        obtain ⟨P, hmP, hdlen, hpal⟩ :=
          pal_diag hp hk hpk.symm hc10 hm21
        have hPpos : 0 < P := by
          rcases Nat.eq_zero_or_pos P with h0 | hp
          · rw [h0, Nat.digits_zero, List.length_nil] at hdlen; omega
          · exact hp
        rw [← hnm] at hmP
        refine ⟨P, hPpos, hmP, ?_, strict_to_relaxed P hPpos hpal⟩
        rw [hnm]; exact hdlen
      · 
        have hT2 : m ∣ 10 ^ (m.totient / 2) - 1 :=
          totient_half_dvd_sub_one hc10 hpp (by omega)
        obtain ⟨c2, hc2⟩ := Nat.totient_even (by omega : 2 < m)
        have htp : 0 < m.totient := Nat.totient_pos.mpr hmpos
        have ht2pos : 0 < m.totient / 2 := by omega
        have hb2' : 2 * (m.totient / 2) ≤ m := by
          have htl : m.totient < m := Nat.totient_lt _ (by omega)
          omega
        obtain ⟨P, hmP, hdigP⟩ :=
          pal_digits_large m m (m.totient / 2) hT2 ht2pos hb2'
        have hPpos : 0 < P := by
          rcases Nat.eq_zero_or_pos P with h0 | hp
          · rw [h0] at hdigP; simp at hdigP; omega
          · exact hp
        have hhead : (Nat.digits 10 P).head? = some 9 := by
          rw [hdigP]
          rw [show List.replicate (m.totient / 2) 9 =
              9 :: List.replicate (m.totient / 2 - 1) 9 from by
                nth_rewrite 1 [(Nat.sub_add_cancel ht2pos).symm]
                rw [List.replicate_succ],
              List.cons_append]
          simp
        rw [← hnm] at hmP
        refine ⟨P, hPpos, hmP, ?_, ?_⟩
        · rw [hnm, hdigP, List.length_append, List.length_append,
            List.length_replicate, List.length_replicate]
          omega
        · rw [dropWhile_self_of_head?_nine hhead, hdigP,
            List.Palindrome.iff_reverse_eq, List.reverse_append,
            List.reverse_append, List.reverse_replicate,
            List.reverse_replicate, List.append_assoc]
    · 
      have hT : m ∣ 10 ^ m.totient - 1 := by
        have h1 : 1 ≤ 10 ^ m.totient := Nat.one_le_pow _ _ (by norm_num)
        exact (Nat.modEq_iff_dvd' h1).mp (Nat.ModEq.pow_totient hc10.symm).symm
      have htpos : 0 < m.totient := Nat.totient_pos.mpr hmpos
      have hb2 : 2 * m.totient ≤ L := by
        rcases Nat.eq_or_lt_of_le hmpos with hm1 | hm2ge
        · rw [← hm1, Nat.totient_one]; omega
        · have htm1 : m.totient ≤ m - 1 := by
            have h := Nat.totient_lt _ hm2ge; omega
          have hge : a + b + 2 * m ≤ 2 ^ a * 5 ^ b * m + 2 := by
            rcases h2or5 with h2n | h5n
            · have ha0 : a = 0 := padicValNat.eq_zero_of_not_dvd h2n
              rw [ha0]; simp only [pow_zero, one_mul]
              have hb1 : 1 ≤ b := by omega
              have h5ge : b + 1 ≤ 5 ^ b := le_trans b.lt_two_pow_self
                (Nat.pow_le_pow_left (by norm_num) b)
              have hbm : b + m ≤ b * m + 2 := by
                rcases Nat.eq_or_lt_of_le hb1 with hb1e | hb2e
                · rw [← hb1e]; omega
                · nlinarith
              have h5m : (b + 1) * m ≤ 5 ^ b * m :=
                Nat.mul_le_mul_right m h5ge
              nlinarith
            · have hb0 : b = 0 :=
                padicValNat.eq_zero_of_not_dvd (fun hd => h5n (hd.trans hq1n))
              rw [hb0]; simp only [pow_zero, mul_one]
              have ha1 : 1 ≤ a := by omega
              have h2ge : a + 1 ≤ 2 ^ a := a.lt_two_pow_self
              have ham : a + m ≤ a * m + 2 := by
                rcases Nat.eq_or_lt_of_le ha1 with ha1e | ha2e
                · rw [← ha1e]; omega
                · nlinarith
              have h2m : (a + 1) * m ≤ 2 ^ a * m :=
                Nat.mul_le_mul_right m h2ge
              nlinarith
          omega
      obtain ⟨P, hmP, hdigP⟩ :=
        pal_digits_large m L m.totient hT htpos hb2
      have hPpos : 0 < P := by
        rcases Nat.eq_zero_or_pos P with h0 | hp
        · rw [h0] at hdigP; simp at hdigP; omega
        · exact hp
      have hhead : (Nat.digits 10 P).head? = some 9 := by
        rw [hdigP]
        rw [show List.replicate m.totient 9 = 9 :: List.replicate (m.totient - 1) 9
            from by
              nth_rewrite 1 [(Nat.sub_add_cancel htpos).symm]
              rw [List.replicate_succ],
            List.cons_append]
        simp
      refine ⟨P * 10 ^ z, by positivity, ?_, ?_, ?_⟩
      · rw [hdecomp]
        have h2a : 2 ^ a ∣ 10 ^ z := by
          rw [hz, show (10 : ℕ) = 2 * 5 from rfl, Nat.mul_pow]
          exact dvd_mul_of_dvd_left (pow_dvd_pow 2 (Nat.le_add_right a b)) _
        have h5b : 5 ^ b ∣ 10 ^ z := by
          rw [hz, show (10 : ℕ) = 2 * 5 from rfl, Nat.mul_pow]
          exact dvd_mul_of_dvd_right (pow_dvd_pow 5 (Nat.le_add_left b a)) _
        have hc25 : Nat.Coprime (2 ^ a) (5 ^ b) :=
          Nat.Coprime.pow_right b (Nat.Coprime.pow_left a (by norm_num))
        have h25 : 2 ^ a * 5 ^ b ∣ P * 10 ^ z :=
          hc25.mul_dvd_of_dvd_of_dvd (dvd_mul_of_dvd_right h2a P)
            (dvd_mul_of_dvd_right h5b P)
        have hcR : Nat.Coprime (2 ^ a * 5 ^ b) m :=
          (Nat.Coprime.mul_right (Nat.Coprime.pow_right a h2)
            (Nat.Coprime.pow_right b h5)).symm
        exact hcR.mul_dvd_of_dvd_of_dvd h25 (dvd_mul_of_dvd_left hmP _)
      · rw [mul_comm, Nat.digits_base_pow_mul (by norm_num) hPpos,
            List.length_append, List.length_replicate, hdigP,
            List.length_append, List.length_append, List.length_replicate,
            List.length_replicate]
        omega
      · have hdN : Nat.digits 10 (P * 10 ^ z) =
            List.replicate z 0 ++ Nat.digits 10 P := by
          rw [mul_comm]; exact Nat.digits_base_pow_mul (by norm_num) hPpos
        rw [hdN, dropWhile_zero_prefix _ hhead, hdigP,
            List.Palindrome.iff_reverse_eq, List.reverse_append,
            List.reverse_append, List.reverse_replicate, List.reverse_replicate,
            List.append_assoc]
  · have hk : ∀ k : ℕ, 5 ≤ k → k + 20 ≤ 2 ^ k := by
      intro k hk5
      induction' k, hk5 using Nat.le_induction with k' hk' ih
      · norm_num
      · calc k' + 1 + 20 ≤ 2 * (k' + 20) := by omega
          _ ≤ 2 * 2 ^ k' := Nat.mul_le_mul_left _ ih
          _ = 2 ^ (k' + 1) := (pow_succ' 2 k').symm
    have hab4 : a + b ≤ 4 := by
      by_contra h4
      push_neg at h4
      have := hk (a + b) (by omega)
      omega
    have hn23 : n ≤ 23 := by omega
    obtain ⟨N, hNpos, hdvN, hlenN, hpalN⟩ := wit013_spec n hn hn23 h10
    exact ⟨N, hNpos, hdvN, hlenN, strict_to_relaxed N hNpos hpalN⟩


theorem A084013 (n : ℕ) (hn : 1 ≤ n) :
    ∃ N : ℕ, 0 < N ∧ n ∣ N ∧
      (Nat.digits 10 N).length = n ∧
      List.Palindrome ((Nat.digits 10 N).dropWhile (· = 0)) := by
  by_cases h10 : 10 ∣ n
  · exact A084013_relaxed n hn h10
  · exact A084013_strict n hn h10


end DeadCount

end A084013src

section A084015src

/-- A084015 : "Largest n-digit palindromic multiple of n. For n = 10k it
    is sufficient that the multiple is palindromic with leading zeros
    ignored. 0 if no such number exists." - the largest element exists
    for every `n >= 1` (OEIS conjecture "no entry is zero", strong
    form : the filtered finset has a maximum).
    Kernel-verified body verbatim from A084015.lean. -/
theorem A084015 (n : ℕ) (hn : 1 ≤ n) :
    ∃ N : ℕ, 0 < N ∧ n ∣ N ∧ (Nat.digits 10 N).length = n
      ∧ List.Palindrome ((Nat.digits 10 N).dropWhile (· = 0))
      ∧ ∀ M : ℕ, n ∣ M → (Nat.digits 10 M).length = n
        → List.Palindrome ((Nat.digits 10 M).dropWhile (· = 0)) → M ≤ N := by
  classical
  let S : Finset ℕ := (Finset.range (10 ^ n)).filter
    (fun N => n ∣ N ∧ (Nat.digits 10 N).length = n
      ∧ List.Palindrome ((Nat.digits 10 N).dropWhile (· = 0)))
  obtain ⟨N0, hN0, hdvd, hlen, hpal⟩ := A084013 n hn
  have hlt : ∀ M : ℕ, (Nat.digits 10 M).length = n → M < 10 ^ n := by
    intro M hM
    rw [← hM]
    exact Nat.lt_base_pow_length_digits (b := 10) (m := M) (by norm_num)
  have hN0S : N0 ∈ S := by
    simp only [S, Finset.mem_filter, Finset.mem_range]
    exact ⟨hlt N0 hlen, hdvd, hlen, hpal⟩
  have hSne : S.Nonempty := ⟨N0, hN0S⟩
  have hmem := Finset.mem_filter.1 (Finset.max'_mem S hSne)
  refine ⟨S.max' hSne, ?_, hmem.2.1, hmem.2.2.1, hmem.2.2.2, ?_⟩
  · rcases Nat.eq_zero_or_pos (S.max' hSne) with h0 | hpos
    · rw [h0] at hmem
      have hlen0 := hmem.2.2.1
      rw [Nat.digits_zero] at hlen0
      simp at hlen0
      omega
    · exact hpos
  · intro M hM hlenM hpalM
    exact Finset.le_max' S M
      (Finset.mem_filter.2 ⟨Finset.mem_range.2 (hlt M hlenM), hM, hlenM, hpalM⟩)

end A084015src

end OMA.A084015Port

/-- Bridge : the corpus gives an `N0` that is a positive n-digit
    palindromic multiple of `n` with `N0 < 10 ^ n`, hence a member of
    the filtered finset `a_val n` maximises over; `Finset.le_sup` then
    bounds `a_val n` below by `N0 > 0`. -/
theorem OMA.solution : type_of% @OMA.S_oeis_a084015.main := by
  intro n hn
  obtain ⟨N0, hN0, hdvd, hlen, hpal, -⟩ := OMA.A084015Port.A084015 n hn
  have hlt : N0 < 10 ^ n := by
    rw [← hlen]
    exact Nat.lt_base_pow_length_digits (b := 10) (m := N0) (by norm_num)
  have hmem : N0 ∈ (Finset.range (10 ^ n)).filter
      (fun N => n ∣ N ∧ (Nat.digits 10 N).length = n ∧
        OMA.S_oeis_a084015.isPal N) := by
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨hlt, hdvd, hlen, hpal⟩
  unfold OMA.S_oeis_a084015.a_val
  exact lt_of_lt_of_le hN0 (Finset.le_sup (f := id) hmem)
