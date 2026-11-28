import OMAStatements.S_oeis_a209724
import Mathlib

/-!
Proof of the conjectures of Reverter i Bigas and Barker for A209724 ((n+1) X 6 arrays over 0..2
whose 2 X 2 subblocks have distinct clockwise edge differences).

Counting. Only 8 of the 81 blocks (p, q upper, r, s lower) are valid, and in each of them s is a
function of p, q, r (blk_det724). Hence a row compatible with u is determined by its first entry
(compat_G724), and the sum over compatible successors is a sum over three first entries
(sum_succ724). T724 n u counts the valid arrays with n + 1 rows and top row u. Every row gets a
type (no successor; one successor which is not of type 2; two successors; one successor of type
2), and a kernel check over the 3^6 rows shows that the successors of a row of each type have the
types the closed form needs (check724_all). Hence T724 n u = hv724 n (type u), and with 24, 2 and
4 rows of the three nonzero types, N n = 24 + 2 * 2^((n+1)/2) + 4 * 2^(n/2) for n ≥ 1. So
a (2k+1) = 2^(k+1) + 6 and a (2k+2) = 3 * 2^k + 6, which are Barker's formulas, and
a (n + 2) = 2 a n - 6 gives the generating function.

Reverter i Bigas. If m = 2 x A / (x + 1) - x with x dividing m and 1 < x < m, write m = x y; then
(x + 1)(y + 1) = 2 A with x, y ≥ 2 (rev_nat724). For A = 2^(i+1) + 6, 3 does not divide 2 A, so
x, y ≥ 3 and (x - 3)(y - 3) ≥ 0 gives m ≥ 3 * 2^i + 6, attained at x = 3. For A = 3 * 2^i + 6,
(x - 2)(y - 2) ≥ 0 gives m ≥ 2^(i+2) + 6, attained at x = 2. These are the next terms.
-/

namespace OMA.Helpers

open OMA.S_oeis_a209724 Finset

/-- A row of the array. -/
abbrev Row724 := Fin 6 → Fin 3

/-- The block condition as a Boolean table: the eight valid blocks (p, q, r, s), with p, q the
upper row and r, s the lower row. -/
def blkC724 (p q r s : Fin 3) : Bool :=
  decide ((p.val, q.val, r.val, s.val) ∈
    [(0, 1, 2, 0), (0, 2, 1, 0), (0, 2, 2, 1), (1, 0, 0, 2), (1, 2, 2, 0), (2, 0, 0, 1),
      (2, 0, 1, 2), (2, 1, 0, 2)])

theorem blk_iff724 : ∀ p q r s : Fin 3, CW p q r s ↔ blkC724 p q r s = true := by
  unfold CW
  decide +kernel

/-- The lower right entry of a valid block is determined by the other three. -/
def fT724 : Fin 3 → Fin 3 → Fin 3 → Fin 3 :=
  ![![![0, 0, 0], ![0, 0, 0], ![0, 0, 1]], ![![2, 0, 0], ![0, 0, 0], ![0, 0, 0]],
    ![![1, 2, 0], ![2, 0, 0], ![0, 0, 0]]]

theorem blk_det724 : ∀ p q r s : Fin 3, blkC724 p q r s = true → s = fT724 p q r := by
  decide +kernel

/-- Two consecutive rows u (upper) and v (lower) are compatible. -/
def compat724 (u v : Row724) : Prop :=
  ∀ j : Fin 5, CW (u j.castSucc) (u j.succ) (v j.castSucc) (v j.succ)

/-- The Boolean version of compat724. -/
def compatC724 (u v : Row724) : Bool :=
  (List.finRange 5).all fun j => blkC724 (u j.castSucc) (u j.succ) (v j.castSucc) (v j.succ)

theorem compat_iff724 (u v : Row724) : compat724 u v ↔ compatC724 u v = true := by
  unfold compat724 compatC724
  simp only [List.all_eq_true, List.mem_finRange, true_implies, blk_iff724]

instance (u v : Row724) : Decidable (compat724 u v) :=
  decidable_of_iff _ (compat_iff724 u v).symm

/-- The entries of u, extended by 0. -/
def ue724 (u : Row724) (j : ℕ) : Fin 3 := if h : j < 6 then u ⟨j, h⟩ else 0

/-- The forced lower row with first entry c. -/
def Gn724 (u : Row724) (c : Fin 3) : ℕ → Fin 3
  | 0 => c
  | j + 1 => fT724 (ue724 u j) (ue724 u (j + 1)) (Gn724 u c j)

def G724 (u : Row724) (c : Fin 3) : Row724 := fun j => Gn724 u c j.val

theorem compat_G724 {u v : Row724} (h : compat724 u v) : G724 u (v 0) = v := by
  have key : ∀ j (hj : j < 6), Gn724 u (v 0) j = v ⟨j, hj⟩ := by
    intro j
    induction j with
    | zero => intro _; rfl
    | succ j ih =>
      intro hj
      have hb := (blk_iff724 _ _ _ _).mp (h ⟨j, by omega⟩)
      have hd : v ⟨j + 1, hj⟩ = fT724 (u ⟨j, by omega⟩) (u ⟨j + 1, hj⟩) (v ⟨j, by omega⟩) :=
        blk_det724 _ _ _ _ hb
      show fT724 (ue724 u j) (ue724 u (j + 1)) (Gn724 u (v 0) j) = v ⟨j + 1, hj⟩
      rw [ih (by omega), hd]
      unfold ue724
      rw [dif_pos (by omega), dif_pos hj]
  funext j
  exact key j.val j.isLt

theorem sum_succ724 (u : Row724) (F : Row724 → ℕ) :
    ∑ v : Row724, (if compat724 u v then F v else 0) =
      ∑ c : Fin 3, (if compat724 u (G724 u c) then F (G724 u c) else 0) := by
  have h1 : ∀ c : Fin 3, (if compat724 u (G724 u c) then F (G724 u c) else 0) =
      ∑ v : Row724, (if G724 u c = v then (if compat724 u v then F v else 0) else 0) := by
    intro c
    rw [Finset.sum_ite_eq]
    simp
  rw [Finset.sum_congr rfl (fun c _ => h1 c), Finset.sum_comm]
  refine Finset.sum_congr rfl fun v _ => ?_
  by_cases hv : compat724 u v
  · rw [Finset.sum_eq_single (v 0)]
    · rw [if_pos (compat_G724 hv)]
    · intro c _ hc
      rw [if_neg]
      intro h
      apply hc
      rw [← h]
      rfl
    · simp
  · rw [if_neg hv]
    simp

/-- The valid arrays: consecutive rows are compatible. -/
def valid724 {n : ℕ} (x : Fin (n + 1) → Row724) : Prop :=
  ∀ i : Fin n, compat724 (x i.castSucc) (x i.succ)

instance {n : ℕ} (x : Fin (n + 1) → Row724) : Decidable (valid724 x) := by
  unfold valid724
  infer_instance

theorem valid_cons724 {m : ℕ} (u : Row724) (w : Fin (m + 1) → Row724) :
    valid724 (Fin.cons u w : Fin (m + 2) → Row724) ↔ compat724 u (w 0) ∧ valid724 w := by
  unfold valid724
  rw [Fin.forall_fin_succ]
  apply and_congr
  · rfl
  · apply forall_congr'
    intro i
    rw [← Fin.succ_castSucc, Fin.cons_succ, Fin.cons_succ]

/-- The number of valid arrays with n + 1 rows and top row u. -/
def T724 (n : ℕ) (u : Row724) : ℕ :=
  ∑ y : Fin n → Row724, if valid724 (Fin.cons u y : Fin (n + 1) → Row724) then 1 else 0

theorem T724_zero (u : Row724) : T724 0 u = 1 := by
  unfold T724
  rw [Fintype.sum_unique, if_pos]
  intro i
  exact Fin.elim0 i

theorem T724_succ (m : ℕ) (u : Row724) :
    T724 (m + 1) u = ∑ v : Row724, if compat724 u v then T724 m v else 0 := by
  unfold T724
  rw [Fintype.sum_equiv (Fin.consEquiv fun _ => Row724).symm _
    (fun p => if valid724 (Fin.cons u (Fin.cons p.1 p.2 : Fin (m + 1) → Row724) :
      Fin (m + 2) → Row724) then 1 else 0) (fun y => by simp),
    Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun v _ => ?_
  simp only [valid_cons724, Fin.cons_zero]
  by_cases hv : compat724 u v
  · simp [hv]
  · simp [hv]

theorem card_eq724 (n : ℕ) :
    Nat.card {x : Fin (n + 1) → Fin 6 → Fin 3 // ∀ i : Fin n, BlockOK (x i.castSucc) (x i.succ)} = ∑ u : Row724, T724 n u := by
  show Nat.card {x : Fin (n + 1) → Row724 // valid724 x} = _
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter]
  rw [Fintype.sum_equiv (Fin.consEquiv fun _ => Row724).symm _
    (fun p => if valid724 (Fin.cons p.1 p.2 : Fin (n + 1) → Row724) then 1 else 0)
    (fun y => by simp), Fintype.sum_prod_type]
  rfl

/-- The successor rows (by their first entries). -/
def scs724 (u : Row724) : List (Fin 3) := (List.finRange 3).filter fun c => compatC724 u (G724 u c)

/-- The type of a row: 0 no successor, 2 two successors, 3 one successor which has two
successors, 1 one successor which has not. -/
def ty724 (u : Row724) : ℕ :=
  match scs724 u with
  | [] => 0
  | [c] => if (scs724 (G724 u c)).length = 2 then 3 else 1
  | [_, _] => 2
  | _ => 9

/-- The types of the successors of u, as required by the type of u. -/
def allowed724 (k : ℕ) : List ℕ :=
  if k = 0 then [] else if k = 1 then [1] else if k = 2 then [3, 3] else [2]

def check724 (u : Row724) : Bool :=
  decide (ty724 u ≤ 3) && decide ((scs724 u).map (fun c => ty724 (G724 u c)) = allowed724 (ty724 u))

/-- The row with code t. -/
def rowOf724 (t : Fin (3 ^ 6)) : Row724 := fun j => ⟨t.val / 3 ^ j.val % 3, Nat.mod_lt _ (by norm_num)⟩

theorem rowOf_eq724 (t : Fin (3 ^ 6)) : rowOf724 t = finFunctionFinEquiv.symm t := by
  funext j
  apply Fin.ext
  rfl

theorem sum_rows724 (F : Row724 → ℕ) : ∑ u : Row724, F u = ∑ t : Fin (3 ^ 6), F (rowOf724 t) := by
  rw [← Equiv.sum_comp finFunctionFinEquiv.symm F]
  exact Finset.sum_congr rfl fun t _ => by rw [rowOf_eq724]

theorem check_all724 : ∀ t : Fin (3 ^ 6), check724 (rowOf724 t) = true := by
  decide +kernel

theorem check724_all (u : Row724) : check724 u = true := by
  have h := check_all724 (finFunctionFinEquiv u)
  rwa [rowOf_eq724, Equiv.symm_apply_apply] at h

/-- The closed form of the number of valid arrays with n + 1 rows and top row of type k. -/
def hv724 (n k : ℕ) : ℕ :=
  if n = 0 then 1 else if k = 1 then 1 else if k = 2 then 2 ^ ((n + 1) / 2)
    else if k = 3 then 2 ^ (n / 2) else 0

theorem hv724_step (n k : ℕ) (hk : k ≤ 3) :
    hv724 (n + 1) k = ((allowed724 k).map (hv724 n)).sum := by
  unfold allowed724 hv724
  interval_cases k
  · simp
  · by_cases hn : n = 0 <;> simp [hn]
  · by_cases hn : n = 0
    · subst hn; simp
    · simp only [show (2 : ℕ) ≠ 0 by norm_num, show (2 : ℕ) ≠ 1 by norm_num,
        show (3 : ℕ) ≠ 1 by norm_num, show (3 : ℕ) ≠ 2 by norm_num,
        if_false, if_true, hn, Nat.add_one_ne_zero, List.map_cons, List.map_nil, List.sum_cons,
        List.sum_nil]
      rw [show (n + 1 + 1) / 2 = n / 2 + 1 by omega, pow_succ]
      ring
  · by_cases hn : n = 0
    · subst hn; simp
    · simp [hn]

theorem sum_fin3_724 (b : Fin 3 → Bool) (g : Fin 3 → ℕ) :
    (((List.finRange 3).filter fun c => b c).map g).sum = ∑ c : Fin 3, if b c = true then g c else 0 := by
  rw [Fin.sum_univ_three]
  have e : List.finRange 3 = [0, 1, 2] := rfl
  rw [e]
  cases h0 : b 0 <;> cases h1 : b 1 <;> cases h2 : b 2 <;> simp [List.filter, h0, h1, h2, add_assoc]

theorem T724_closed (n : ℕ) : ∀ u : Row724, T724 n u = hv724 n (ty724 u) := by
  induction n with
  | zero => intro u; rw [T724_zero]; rfl
  | succ n ih =>
    intro u
    rw [T724_succ, Finset.sum_congr rfl (fun v _ => by rw [ih v]), sum_succ724]
    have hc := check724_all u
    unfold check724 at hc
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨hk, he⟩ := hc
    rw [hv724_step n _ hk, ← he, List.map_map]
    unfold scs724
    rw [sum_fin3_724]
    refine Finset.sum_congr rfl fun c _ => ?_
    simp only [compat_iff724, Function.comp]

theorem counts724 :
    (∑ t : Fin (3 ^ 6), if ty724 (rowOf724 t) = 1 then 1 else 0) = 24 ∧
    (∑ t : Fin (3 ^ 6), if ty724 (rowOf724 t) = 2 then 1 else 0) = 2 ∧
    (∑ t : Fin (3 ^ 6), if ty724 (rowOf724 t) = 3 then 1 else 0) = 4 := by
  decide +kernel

theorem hv724_split (n k : ℕ) (hn : n ≠ 0) :
    hv724 n k = (if k = 1 then 1 else 0) + (if k = 2 then 1 else 0) * 2 ^ ((n + 1) / 2) +
      (if k = 3 then 1 else 0) * 2 ^ (n / 2) := by
  unfold hv724
  rw [if_neg hn]
  by_cases h1 : k = 1
  · subst h1; simp
  · by_cases h2 : k = 2
    · subst h2; simp
    · by_cases h3 : k = 3
      · subst h3; simp
      · simp [h1, h2, h3]

theorem card724 (n : ℕ) (hn : n ≠ 0) :
    Nat.card {x : Fin (n + 1) → Fin 6 → Fin 3 // ∀ i : Fin n, BlockOK (x i.castSucc) (x i.succ)} =
      24 + 2 * 2 ^ ((n + 1) / 2) + 4 * 2 ^ (n / 2) := by
  rw [card_eq724, sum_rows724]
  simp only [T724_closed n, hv724_split n _ hn]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul]
  obtain ⟨c1, c2, c3⟩ := counts724
  rw [c1, c2, c3]

theorem a724_closed (n : ℕ) (hn : n ≠ 0) :
    a n = (24 + 2 * 2 ^ ((n + 1) / 2) + 4 * 2 ^ (n / 2) : ℚ) / 4 := by
  unfold a N
  rw [card724 n hn]
  push_cast
  ring

theorem a724_odd (k : ℕ) : a (2 * k + 1) = 2 ^ (k + 1) + 6 := by
  rw [a724_closed _ (by omega), show (2 * k + 1 + 1) / 2 = k + 1 by omega,
    show (2 * k + 1) / 2 = k by omega, pow_succ]
  ring

theorem a724_even (k : ℕ) : a (2 * k + 2) = 3 * 2 ^ k + 6 := by
  rw [a724_closed _ (by omega), show (2 * k + 2 + 1) / 2 = k + 1 by omega,
    show (2 * k + 2) / 2 = k + 1 by omega, pow_succ]
  ring

theorem a724_step (n : ℕ) (hn : n ≠ 0) : a (n + 2) = 2 * a n - 6 := by
  rw [a724_closed _ (by omega), a724_closed _ hn, show (n + 2 + 1) / 2 = (n + 1) / 2 + 1 by omega,
    show (n + 2) / 2 = n / 2 + 1 by omega, pow_succ, pow_succ]
  ring

theorem not3_724 (i : ℕ) : ¬ 3 ∣ 2 ^ i := by
  intro h
  have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
  norm_num at this

/-- The equation of Reverter i Bigas in natural numbers: k = x y with (x + 1) (y + 1) = 2 A. -/
theorem rev_nat724 (A k : ℕ) (h : Rev (A : ℚ) k) :
    ∃ x y : ℕ, k = x * y ∧ 2 ≤ x ∧ 2 ≤ y ∧ (x + 1) * (y + 1) = 2 * A := by
  obtain ⟨x, hdvd, h1, h2, heq⟩ := h
  obtain ⟨y, rfl⟩ := hdvd
  have hx1 : (x : ℚ) + 1 ≠ 0 := by positivity
  have hq : (((x * y : ℕ) : ℚ) + x) * (x + 1) = 2 * x * A := by
    rw [heq]
    field_simp
    ring
  have hn : (x * y + x) * (x + 1) = 2 * x * A := by exact_mod_cast hq
  have hy : 2 ≤ y := by
    by_contra hy
    push Not at hy
    interval_cases y <;> simp at h2
  refine ⟨x, y, rfl, h1, hy, ?_⟩
  have hx0 : 0 < x := by omega
  apply Nat.eq_of_mul_eq_mul_left hx0
  have e : x * ((x + 1) * (y + 1)) = (x * y + x) * (x + 1) := by ring
  rw [e, hn]
  ring

theorem rev_main724 :
    a 1 = 8 ∧ ∀ n : ℕ, 1 < n → ∃ m : ℕ, a n = m ∧ IsLeast {k : ℕ | Rev (a (n - 1)) k} m := by
  refine ⟨by rw [show (1 : ℕ) = 2 * 0 + 1 by rfl, a724_odd]; norm_num, ?_⟩
  intro n hn
  obtain ⟨p, rfl⟩ : ∃ p, n = p + 2 := ⟨n - 2, by omega⟩
  rw [show p + 2 - 1 = p + 1 by omega]
  rcases Nat.even_or_odd p with ⟨i, hi⟩ | ⟨i, hi⟩
  · -- p = 2 i: the previous term is 2^(i+1) + 6, the term is 3 * 2^i + 6
    subst hi
    have hA : a (i + i + 1) = ((2 ^ (i + 1) + 6 : ℕ) : ℚ) := by
      rw [show i + i + 1 = 2 * i + 1 by omega, a724_odd]
      push_cast
      ring
    refine ⟨3 * 2 ^ i + 6, ?_, ?_, ?_⟩
    · rw [show i + i + 2 = 2 * i + 2 by omega, a724_even]
      push_cast
      ring
    · show Rev (a (i + i + 1)) (3 * 2 ^ i + 6)
      refine ⟨3, ⟨2 ^ i + 2, by ring⟩, by norm_num, ?_, ?_⟩
      · have : 0 < 2 ^ i := by positivity
        omega
      · rw [hA]
        push_cast
        rw [pow_succ]
        ring
    · intro k hk
      rw [Set.mem_ofPred_eq, hA] at hk
      obtain ⟨x, y, rfl, hx, hy, he⟩ := rev_nat724 _ _ hk
      have h3 := not3_724 (i + 2)
      have hp : 2 ^ (i + 2) = 4 * 2 ^ i := by rw [pow_add]; ring
      have he' : (x + 1) * (y + 1) = 4 * 2 ^ i + 12 := by rw [he, pow_succ]; ring
      have hx3 : 3 ≤ x := by
        by_contra hc
        have hx2 : x = 2 := by omega
        subst hx2
        apply h3
        rw [hp]
        omega
      have hy3 : 3 ≤ y := by
        by_contra hc
        have hy2 : y = 2 := by omega
        subst hy2
        apply h3
        rw [hp]
        omega
      have hxy : 3 * x + 3 * y ≤ x * y + 9 := by nlinarith
      nlinarith
  · -- p = 2 i + 1: the previous term is 3 * 2^i + 6, the term is 2^(i+2) + 6
    subst hi
    have hA : a (2 * i + 1 + 1) = ((3 * 2 ^ i + 6 : ℕ) : ℚ) := by
      rw [show 2 * i + 1 + 1 = 2 * i + 2 by omega, a724_even]
      push_cast
      ring
    refine ⟨2 ^ (i + 2) + 6, ?_, ?_, ?_⟩
    · rw [show 2 * i + 1 + 2 = 2 * (i + 1) + 1 by omega, a724_odd]
      push_cast
      ring
    · show Rev (a (2 * i + 1 + 1)) (2 ^ (i + 2) + 6)
      refine ⟨2, ⟨2 ^ (i + 1) + 3, by ring⟩, by norm_num, ?_, ?_⟩
      · have : 0 < 2 ^ (i + 2) := by positivity
        omega
      · rw [hA]
        push_cast
        rw [pow_succ, pow_succ]
        ring
    · intro k hk
      rw [Set.mem_ofPred_eq, hA] at hk
      obtain ⟨x, y, rfl, hx, hy, he⟩ := rev_nat724 _ _ hk
      have hp : 2 ^ (i + 2) = 4 * 2 ^ i := by rw [pow_add]; ring
      rw [hp]
      have hxy : 2 * x + 2 * y ≤ x * y + 4 := by nlinarith
      nlinarith

/-- The sequence with the constant term 0, as in the generating function. -/
noncomputable def bs724 (n : ℕ) : ℚ := if n = 0 then 0 else a n

theorem bs724_rec (j : ℕ) : bs724 (j + 4) - bs724 (j + 3) - 2 * bs724 (j + 2) + 2 * bs724 (j + 1) = 0 := by
  unfold bs724
  simp only [show j + 4 ≠ 0 by omega, show j + 3 ≠ 0 by omega, show j + 2 ≠ 0 by omega,
    show j + 1 ≠ 0 by omega, if_false]
  rw [show j + 4 = (j + 2) + 2 by omega, a724_step (j + 2) (by omega),
    show j + 3 = (j + 1) + 2 by omega, a724_step (j + 1) (by omega)]
  ring

theorem bs724_vals : bs724 0 = 0 ∧ bs724 1 = 8 ∧ bs724 2 = 9 ∧ bs724 3 = 10 := by
  unfold bs724
  refine ⟨by simp, ?_, ?_, ?_⟩
  · rw [if_neg (by norm_num), show (1 : ℕ) = 2 * 0 + 1 by rfl, a724_odd]; norm_num
  · rw [if_neg (by norm_num), show (2 : ℕ) = 2 * 0 + 2 by rfl, a724_even]; norm_num
  · rw [if_neg (by norm_num), show (3 : ℕ) = 2 * 1 + 1 by rfl, a724_odd]; norm_num

open PowerSeries in
theorem gen_fun724 :
    PowerSeries.mk bs724 * ((1 - X) * (1 - 2 * X ^ 2)) = X * (8 + X - 15 * X ^ 2) := by
  have key : PowerSeries.mk bs724 * ((1 - X) * (1 - 2 * X ^ 2)) =
      C 1 * (PowerSeries.mk bs724 * X ^ 0) - C 1 * (PowerSeries.mk bs724 * X ^ 1) -
        C 2 * (PowerSeries.mk bs724 * X ^ 2) + C 2 * (PowerSeries.mk bs724 * X ^ 3) := by
    simp only [map_one, map_ofNat]
    ring
  have hrhs : (X : ℚ⟦X⟧) * (8 + X - 15 * X ^ 2) = C 8 * X ^ 1 + C 1 * X ^ 2 - C 15 * X ^ 3 := by
    simp only [map_ofNat, map_one]
    ring
  rw [key, hrhs]
  ext k
  simp only [map_sub, map_add, coeff_C_mul_X_pow]
  simp only [coeff_C_mul, coeff_mul_X_pow', coeff_mk]
  obtain ⟨v0, v1, v2, v3⟩ := bs724_vals
  by_cases hk : k < 4
  · interval_cases k <;> norm_num [v0, v1, v2, v3]
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 4 := ⟨k - 4, by omega⟩
    have hr := bs724_rec j
    simp only [show 0 ≤ j + 4 by omega, show 1 ≤ j + 4 by omega, show 2 ≤ j + 4 by omega,
      show 3 ≤ j + 4 by omega,
      show j + 4 - 0 = j + 4 by omega, show j + 4 - 1 = j + 3 by omega,
      show j + 4 - 2 = j + 2 by omega, show j + 4 - 3 = j + 1 by omega,
      show ¬ (j + 4 = 1) by omega, show ¬ (j + 4 = 2) by omega, show ¬ (j + 4 = 3) by omega,
      if_true, if_false]
    linarith

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a209724.main := by
  refine ⟨OMA.Helpers.rev_main724, OMA.Helpers.gen_fun724, ?_, ?_⟩
  · intro n hn he
    obtain ⟨k, rfl⟩ := he
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [show j + 1 + (j + 1) = 2 * j + 2 by omega, OMA.Helpers.a724_even,
      show (2 * j + 2) / 2 - 1 = j by omega]
  · intro n hn ho
    obtain ⟨k, rfl⟩ := ho
    rw [OMA.Helpers.a724_odd, show (2 * k + 1 + 1) / 2 = k + 1 by omega]
