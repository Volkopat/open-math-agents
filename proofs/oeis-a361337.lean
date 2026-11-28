import OMAStatements.S_oeis_a361337
import Mathlib

/-!
Proof of Hasler's conjecture for A361337.
1. Every split product is smaller than the number split, so `Reaches0 N` iff `N = 0` or some split product of
   `N` reaches 0.
2. `tbl` is a bitset for `0, ..., 3111`. The kernel checks that it is a fixed point of that recursion, so its
   bits are exactly the terms below 3112 (`table_ok`); it has 219 zero bits there, so 2893 terms lie below 3112.
3. Every `N ≥ 3112` is a term: for `N < 31120` the kernel finds a split whose product is either at least 3112
   (and smaller than `N`) or a term below 3112; for `N ≥ 31120` cutting off the last digit gives `0` or a
   product between 3112 and `N`. Strong induction finishes.
4. `Nat.nth` then gives `a (2894 + k) = 3112 + k`.
-/

namespace OMA.A361337Proof

open OMA.S_oeis_a361337

theorem splitProd_lt {N P : ℕ} (h : SplitProd N P) : P < N := by
  unfold SplitProd at h
  obtain ⟨j, -, hjN, -, rfl⟩ := h
  have hpos : 0 < 10 ^ j := by positivity
  have hA : 0 < N / 10 ^ j := Nat.div_pos hjN hpos
  calc N / 10 ^ j * (N % 10 ^ j) < N / 10 ^ j * 10 ^ j :=
        Nat.mul_lt_mul_of_pos_left (Nat.mod_lt _ hpos) hA
    _ ≤ N := Nat.div_mul_le_self N (10 ^ j)

theorem reaches0_iff (N : ℕ) : Reaches0 N ↔ N = 0 ∨ ∃ P, SplitProd N P ∧ Reaches0 P := by
  unfold Reaches0
  exact Relation.ReflTransGen.cases_head_iff

/-- The split with a suffix of `j` digits is legal (Bool form). -/
def legal (N j : ℕ) : Bool :=
  decide (10 ^ j ≤ N) && (decide (j = 1) || decide (10 ^ (j - 1) ≤ N % 10 ^ j))

/-- The product of the split with a suffix of `j` digits. -/
def prodAt (N j : ℕ) : ℕ := N / 10 ^ j * (N % 10 ^ j)

theorem splitProd_iff_legal {N P : ℕ} :
    SplitProd N P ↔ ∃ j, 1 ≤ j ∧ legal N j = true ∧ P = prodAt N j := by
  simp only [SplitProd, legal, prodAt, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨j, hj1, hjN, hl, rfl⟩
    exact ⟨j, hj1, ⟨hjN, hl⟩, rfl⟩
  · rintro ⟨j, hj1, ⟨hjN, hl⟩, rfl⟩
    exact ⟨j, hj1, hjN, hl, rfl⟩

theorem legal_le {N j : ℕ} (hN : N < 100000) (h : legal N j = true) : j ≤ 4 := by
  unfold legal at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨h1, -⟩ := h
  by_contra hj
  have h5 : 10 ^ 5 ≤ 10 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h6 : (10 : ℕ) ^ 5 = 100000 := by norm_num
  rw [h6] at h5
  omega

/-- Some legal split of `N` with a suffix of at most 4 digits has a product `P` with `f P`. -/
def anySplit (f : ℕ → Bool) (N : ℕ) : Bool :=
  (legal N 1 && f (prodAt N 1)) || ((legal N 2 && f (prodAt N 2)) ||
    ((legal N 3 && f (prodAt N 3)) || (legal N 4 && f (prodAt N 4))))

theorem anySplit_iff (f : ℕ → Bool) {N : ℕ} (hN : N < 100000) :
    anySplit f N = true ↔ ∃ P, SplitProd N P ∧ f P = true := by
  constructor
  · intro h
    unfold anySplit at h
    simp only [Bool.or_eq_true, Bool.and_eq_true] at h
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨_, splitProd_iff_legal.2 ⟨1, le_refl _, h1, rfl⟩, h2⟩
    · exact ⟨_, splitProd_iff_legal.2 ⟨2, by norm_num, h1, rfl⟩, h2⟩
    · exact ⟨_, splitProd_iff_legal.2 ⟨3, by norm_num, h1, rfl⟩, h2⟩
    · exact ⟨_, splitProd_iff_legal.2 ⟨4, by norm_num, h1, rfl⟩, h2⟩
  · rintro ⟨P, hP, hf⟩
    obtain ⟨j, hj1, hl, rfl⟩ := splitProd_iff_legal.1 hP
    have hj4 := legal_le hN hl
    unfold anySplit
    interval_cases j <;> simp [hl, hf]

/-- `f m` holds for every `m < n`. -/
def allBelow (f : ℕ → Bool) : ℕ → Bool
  | 0 => true
  | n + 1 => f n && allBelow f n

theorem allBelow_spec {f : ℕ → Bool} {n : ℕ} (h : allBelow f n = true) : ∀ m < n, f m = true := by
  induction n with
  | zero => intro m hm; omega
  | succ n ih =>
    intro m hm
    simp only [allBelow, Bool.and_eq_true] at h
    by_cases hmn : m < n
    · exact ih h.2 m hmn
    · have hmn' : m = n := by omega
      subst hmn'
      exact h.1

theorem allBelow_shift {f : ℕ → Bool} {lo len : ℕ} (h : allBelow (fun i => f (lo + i)) len = true) :
    ∀ m, lo ≤ m → m < lo + len → f m = true := by
  intro m h1 h2
  have h3 := allBelow_spec h (m - lo) (by omega)
  have h4 : lo + (m - lo) = m := by omega
  simp only [h4] at h3
  exact h3

/-- Bit `N` of `tbl` says whether `N < 3112` is a term. -/
def tbl : ℕ := 0x7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7fffffffffffffffffffffdff7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdff7fffffffffffdfffffff7ffff7fffffffffffffffffff7f9fc7ffffffffffffffffffffffffffffffffffffffffffffffdfd7ffffffffffffffffffffffff7ffff7fffffffffffffc7f5fc7fffffffffffbfffffceff9fe7ffffffffffffffffffffffffffffdffffffffffff5ff5f1fe7ffdf7f5387fffff79dd779d87ffef7fdfd7fdffdf19a7e1487ff585e9d8761ff4315c721087ff184a140621dd4210042100401

/-- `tbl` satisfies the recursion of `reaches0_iff` at `N`. -/
def fixOK (N : ℕ) : Bool :=
  decide (Nat.testBit tbl N = (decide (N = 0) || anySplit (Nat.testBit tbl) N))

theorem fix_check : allBelow fixOK 3112 = true := by decide +kernel

theorem table_ok : ∀ N < 3112, (Nat.testBit tbl N = true ↔ Reaches0 N) := by
  intro N
  refine Nat.strong_induction_on N ?_
  intro N ih hN
  have hfix := allBelow_spec fix_check N hN
  unfold fixOK at hfix
  rw [decide_eq_true_eq] at hfix
  rw [hfix, reaches0_iff N, Bool.or_eq_true, decide_eq_true_eq, anySplit_iff (N := N) _ (by omega)]
  refine or_congr Iff.rfl ⟨?_, ?_⟩
  · rintro ⟨P, hP, hb⟩
    have hlt := splitProd_lt hP
    exact ⟨P, hP, (ih P hlt (by omega)).1 hb⟩
  · rintro ⟨P, hP, hr⟩
    have hlt := splitProd_lt hP
    exact ⟨P, hP, (ih P hlt (by omega)).2 hr⟩

/-- A split product `P < N` that is known to be a term, for `N ≥ 3112`. -/
def good (P : ℕ) : Bool := decide (3112 ≤ P) || Nat.testBit tbl P

def tailOK (N : ℕ) : Bool := anySplit good N

theorem tail0 : allBelow (fun i => tailOK (3112 + i)) 7002 = true := by decide +kernel

theorem tail1 : allBelow (fun i => tailOK (10114 + i)) 7002 = true := by decide +kernel

theorem tail2 : allBelow (fun i => tailOK (17116 + i)) 7002 = true := by decide +kernel

theorem tail3 : allBelow (fun i => tailOK (24118 + i)) 7002 = true := by decide +kernel

theorem tail_check (N : ℕ) (h1 : 3112 ≤ N) (h2 : N < 31120) : tailOK N = true := by
  by_cases ha : N < 10114
  · exact allBelow_shift (f := tailOK) (lo := 3112) (len := 7002) tail0 N h1 (by omega)
  by_cases hb : N < 17116
  · exact allBelow_shift (f := tailOK) (lo := 10114) (len := 7002) tail1 N (by omega) (by omega)
  by_cases hc : N < 24118
  · exact allBelow_shift (f := tailOK) (lo := 17116) (len := 7002) tail2 N (by omega) (by omega)
  · exact allBelow_shift (f := tailOK) (lo := 24118) (len := 7002) tail3 N (by omega) (by omega)

theorem tail_ok : ∀ N, 3112 ≤ N → Reaches0 N := by
  intro N
  refine Nat.strong_induction_on N ?_
  intro N ih hN
  rw [reaches0_iff N]
  right
  by_cases hbig : N < 31120
  · have h := tail_check N hN hbig
    unfold tailOK at h
    rw [anySplit_iff (N := N) _ (by omega)] at h
    obtain ⟨P, hP, hf⟩ := h
    refine ⟨P, hP, ?_⟩
    have hlt := splitProd_lt hP
    by_cases hP3 : 3112 ≤ P
    · exact ih P hlt hP3
    · unfold good at hf
      rw [Bool.or_eq_true, decide_eq_true_eq] at hf
      rcases hf with hf | hf
      · exact absurd hf hP3
      · exact (table_ok P (by omega)).1 hf
  · have hsplit : SplitProd N (N / 10 * (N % 10)) := by
      unfold SplitProd
      exact ⟨1, le_refl _, by rw [pow_one]; omega, Or.inl rfl, by rw [pow_one]⟩
    refine ⟨_, hsplit, ?_⟩
    by_cases h0 : N % 10 = 0
    · rw [h0, Nat.mul_zero]
      exact Relation.ReflTransGen.refl
    · apply ih _ (splitProd_lt hsplit)
      have h1 : 1 ≤ N % 10 := Nat.one_le_iff_ne_zero.2 h0
      have h3 : 3112 ≤ N / 10 := by omega
      calc 3112 ≤ N / 10 := h3
        _ = N / 10 * 1 := (Nat.mul_one _).symm
        _ ≤ N / 10 * (N % 10) := Nat.mul_le_mul_left _ h1

theorem count_congr_lt {p q : ℕ → Prop} [DecidablePred p] [DecidablePred q] (n : ℕ)
    (h : ∀ m < n, (p m ↔ q m)) : Nat.count p n = Nat.count q n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.count_succ p n, Nat.count_succ q n, ih (fun m hm => h m (by omega))]
    by_cases hp : p n
    · rw [if_pos hp, if_pos ((h n (by omega)).1 hp)]
    · rw [if_neg hp, if_neg (fun hq => hp ((h n (by omega)).2 hq))]

theorem count_compl (p : ℕ → Prop) [DecidablePred p] (n : ℕ) :
    Nat.count p n + Nat.count (fun x => ¬ p x) n = n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.count_succ p n, Nat.count_succ (fun x => ¬ p x) n]
    by_cases h : p n
    · rw [if_pos h, if_neg (not_not.2 h)]
      omega
    · rw [if_neg h, if_pos h]
      omega

theorem cnt_nm : Nat.count (fun N => Nat.testBit tbl N = false) 3112 = 219 := by decide +kernel

theorem count_eq [DecidablePred Reaches0] : Nat.count Reaches0 3112 = 2893 := by
  have h2 : Nat.count (fun x => ¬ Reaches0 x) 3112 = 219 := by
    rw [count_congr_lt (p := fun x => ¬ Reaches0 x) (q := fun N => Nat.testBit tbl N = false) 3112
      (fun m hm => by
        show ¬ Reaches0 m ↔ Nat.testBit tbl m = false
        rw [← table_ok m hm, Bool.not_eq_true])]
    exact cnt_nm
  have h1 := count_compl Reaches0 3112
  rw [h2] at h1
  omega

end OMA.A361337Proof

open OMA.S_oeis_a361337 in
theorem OMA.solution : type_of% @OMA.S_oeis_a361337.main := by
  classical
  intro k
  have htail := OMA.A361337Proof.tail_ok
  have hcnt : Nat.count Reaches0 3112 = 2893 := OMA.A361337Proof.count_eq
  have hk : Nat.count (fun i => Reaches0 (3112 + i)) k = k :=
    Nat.count_of_forall (fun i _ => htail (3112 + i) (by omega))
  have hc2 : Nat.count Reaches0 (3112 + k) = 2893 + k := by
    rw [Nat.count_add, hcnt, hk]
  show Nat.nth Reaches0 (2894 + k - 1) = 3112 + k
  rw [show 2894 + k - 1 = 2893 + k by omega, ← hc2]
  exact Nat.nth_count (htail _ (by omega))
