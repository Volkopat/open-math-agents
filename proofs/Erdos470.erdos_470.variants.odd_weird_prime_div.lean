import FormalConjectures.ErdosProblems.«470»
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.Forall2
import Mathlib.Data.Nat.Factorization.Induction
import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.Data.Nat.Log
import Mathlib.Data.Set.Card
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.FactorisationProperties
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace OddWeirdSubproblems

open Finset

abbrev Coordinates := List (ℕ × ℕ)

def powerSum (p : ℕ) : ℕ → ℕ
  | 0 => 1
  | e + 1 => powerSum p e + p ^ (e + 1)

theorem powerSum_eq_sum (p e : ℕ) : powerSum p e = ∑ i ∈ range (e + 1), p ^ i := by
  induction e with
  | zero => simp [powerSum]
  | succ e ih => rw [powerSum, sum_range_succ, ih]

def number (fs : Coordinates) : ℕ := (fs.map fun (p, e) => p ^ e).prod

def divisorSum (fs : Coordinates) : ℕ := (fs.map fun (p, e) => powerSum p e).prod

def index (p e : ℕ) : ℚ := (powerSum p e : ℚ) / (p : ℚ) ^ e

def limitingIndex (p : ℕ) : ℚ := (p : ℚ) / ((p : ℚ) - 1)

structure Slot where
  prime : ℕ
  exponent : ℕ
  fixed : Bool

def Slot.Fits (s : Slot) (x : ℕ × ℕ) : Prop :=
  x.1.Prime ∧ s.prime = x.1 ∧ s.exponent ≤ x.2 ∧ (s.fixed = true → s.exponent = x.2)

def Slot.upper (s : Slot) : ℚ :=
  if s.fixed then index s.prime s.exponent else limitingIndex s.prime

def Slot.minimum (s : Slot) : ℕ × ℕ := (s.prime, s.exponent)

def TailFits : ℕ → Coordinates → Prop
  | _, [] => True
  | p, (q, e) :: qs => p ≤ q ∧ 2 < q ∧ q.Prime ∧ Odd q ∧ 0 < e ∧ TailFits (q + 2) qs

def tailUpper : ℕ → ℕ → ℚ
  | _, 0 => 1
  | p, r + 1 => limitingIndex p * tailUpper (p + 2) r

theorem index_le_limitingIndex {p e : ℕ} (hp : 1 < p) :
    index p e ≤ limitingIndex p := by
  have hpq : (1 : ℚ) < p := by exact_mod_cast hp
  have hpow : (0 : ℚ) < (p : ℚ) ^ e := pow_pos (by linarith) _
  unfold index limitingIndex
  rw [powerSum_eq_sum]
  push_cast
  rw [div_le_div_iff₀ hpow (sub_pos.mpr hpq), geom_sum_mul, pow_succ]
  linarith

theorem limitingIndex_antitone {p q : ℕ} (hp : 1 < p) (hpq : p ≤ q) :
    limitingIndex q ≤ limitingIndex p := by
  have hp' : (1 : ℚ) < p := by exact_mod_cast hp
  have hpq' : (p : ℚ) ≤ q := by exact_mod_cast hpq
  unfold limitingIndex
  rw [div_le_div_iff₀ (sub_pos.mpr (hp'.trans_le hpq')) (sub_pos.mpr hp')]
  nlinarith

theorem slot_index_le {s : Slot} {x : ℕ × ℕ} (h : s.Fits x) :
    index x.1 x.2 ≤ s.upper := by
  obtain ⟨hp, hs, _, he⟩ := h
  cases hf : s.fixed
  · simpa [Slot.upper, hf, hs] using (index_le_limitingIndex (e := x.2) hp.one_lt)
  · simp [Slot.upper, hf, hs, he hf]

theorem index_nonneg (p e : ℕ) : 0 ≤ index p e := by unfold index; positivity

theorem limitingIndex_nonneg {p : ℕ} (hp : 1 < p) : 0 ≤ limitingIndex p := by
  have hp' : (1 : ℚ) < p := by exact_mod_cast hp
  exact div_nonneg (by positivity) (sub_nonneg.mpr hp'.le)

theorem coordinate_index_eq (xs : Coordinates) :
    (xs.map fun x => index x.1 x.2).prod = (divisorSum xs : ℚ) / (number xs : ℚ) := by
  induction xs with
  | nil => simp [divisorSum, number]
  | cons x xs ih =>
    rcases x with ⟨p, e⟩
    simp only [List.map_cons, List.prod_cons, ih]
    simp only [index, divisorSum, number, List.map_cons, List.prod_cons, Nat.cast_mul,
      Nat.cast_pow, div_mul_div_comm]

theorem coordinate_prod_nonneg (xs : Coordinates) :
    0 ≤ (xs.map fun x => index x.1 x.2).prod := by
  induction xs with
  | nil => norm_num
  | cons x xs ih => exact mul_nonneg (index_nonneg _ _) ih

theorem slot_prod_upper {ss : List Slot} {xs : Coordinates}
    (h : List.Forall₂ Slot.Fits ss xs) :
    (xs.map fun x => index x.1 x.2).prod ≤ (ss.map Slot.upper).prod := by
  induction h with
  | nil => simp
  | cons h₁ _ ih =>
    simp only [List.map_cons, List.prod_cons]
    refine mul_le_mul (slot_index_le h₁) ih ?_ ((index_nonneg _ _).trans (slot_index_le h₁))
    exact coordinate_prod_nonneg _

theorem tailUpper_nonneg {p : ℕ} (hp : 1 < p) (r : ℕ) : 0 ≤ tailUpper p r := by
  induction r generalizing p with
  | zero => simp [tailUpper]
  | succ r ih => exact mul_nonneg (limitingIndex_nonneg hp) (ih (by omega))

theorem tailUpper_antitone {p q : ℕ} (hp : 1 < p) (hpq : p ≤ q) (r : ℕ) :
    tailUpper q r ≤ tailUpper p r := by
  induction r generalizing p q with
  | zero => simp [tailUpper]
  | succ r ih =>
    exact mul_le_mul (limitingIndex_antitone hp hpq) (ih (by omega) (by omega))
      (tailUpper_nonneg (show 1 < q + 2 by omega) r) (limitingIndex_nonneg hp)

theorem tail_prod_upper {p : ℕ} {xs : Coordinates} (hp : 1 < p) (h : TailFits p xs) :
    (xs.map fun x => index x.1 x.2).prod ≤ tailUpper p xs.length := by
  induction xs generalizing p with
  | nil => simp [tailUpper]
  | cons x xs ih =>
    rcases x with ⟨q, e⟩
    obtain ⟨hpq, _, hq, _, _, ht⟩ := h
    simp only [List.map_cons, List.prod_cons, List.length_cons, tailUpper]
    exact mul_le_mul ((index_le_limitingIndex hq.one_lt).trans (limitingIndex_antitone hp hpq))
      ((ih (show 1 < q + 2 by omega) ht).trans
        (tailUpper_antitone (show 1 < p + 2 by omega) (by omega) xs.length))
      (coordinate_prod_nonneg xs) (limitingIndex_nonneg hp)

theorem tailFits_of_sorted {xs : Coordinates} {p : ℕ}
    (hp : 2 < p)
    (hlo : ∀ x ∈ xs, p ≤ x.1)
    (hlocal : ∀ x ∈ xs, x.1.Prime ∧ Odd x.1 ∧ 0 < x.2)
    (horder : xs.Pairwise (fun x y => x.1 < y.1)) : TailFits p xs := by
  induction xs generalizing p with
  | nil => trivial
  | cons x xs ih =>
    obtain ⟨q, e⟩ := x
    have hq := hlo (q, e) (by simp)
    obtain ⟨hprime, hodd, he⟩ := hlocal (q, e) (by simp)
    change p ≤ q at hq
    obtain ⟨horder, htail⟩ := List.pairwise_cons.mp horder
    refine ⟨hq, by omega, hprime, hodd, he, ih (by omega) ?_ ?_ htail⟩
    · intro z hz
      have hlt := horder z hz
      have hzodd := (hlocal z (List.mem_cons_of_mem _ hz)).2.1
      obtain ⟨a, ha⟩ := hodd
      obtain ⟨b, hb⟩ := hzodd
      change q < z.1 at hlt
      omega
    · intro z hz
      exact hlocal z (List.mem_cons_of_mem _ hz)

def PrimeCoordinates (xs : Coordinates) : Prop :=
  (∀ x ∈ xs, x.1.Prime) ∧ xs.Pairwise (fun x y => x.1 < y.1)

theorem number_cons (x : ℕ × ℕ) (xs : Coordinates) :
    number (x :: xs) = x.1 ^ x.2 * number xs := rfl

theorem number_append (xs ys : Coordinates) : number (xs ++ ys) = number xs * number ys := by
  simp [number, List.prod_append]

theorem divisorSum_append (xs ys : Coordinates) :
    divisorSum (xs ++ ys) = divisorSum xs * divisorSum ys := by
  simp [divisorSum, List.prod_append]

theorem number_pos {xs : Coordinates} (h : ∀ x ∈ xs, Nat.Prime x.1) : 0 < number xs := by
  induction xs with
  | nil => decide
  | cons x xs ih =>
    rw [number_cons]
    exact Nat.mul_pos (pow_pos (h x (by simp)).pos _)
      (ih (fun y hy => h y (List.mem_cons_of_mem _ hy)))

theorem divisorSum_eq {xs : Coordinates} (hs : PrimeCoordinates xs) :
    divisorSum xs = ∑ d ∈ (number xs).divisors, d := by
  induction xs with
  | nil => decide
  | cons x xs ih =>
    obtain ⟨hp, hlt⟩ := hs
    obtain ⟨horder, htail⟩ := List.pairwise_cons.mp hlt
    have hp' : ∀ y ∈ xs, Nat.Prime y.1 := fun y hy => hp y (List.mem_cons_of_mem _ hy)
    have hcop : (x.1 ^ x.2).Coprime (number xs) := by
      apply Nat.coprime_list_prod_right_iff.mpr
      intro m hm
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hm
      exact Nat.coprime_pow_primes _ _ (hp x (by simp)) (hp' y hy) (horder y hy).ne
    rw [number_cons, hcop.sum_divisors_mul, ← ih ⟨hp', htail⟩,
      ← ArithmeticFunction.sigma_one_apply, ArithmeticFunction.sigma_one_apply_prime_pow (hp x (by simp))]
    change powerSum x.1 x.2 * divisorSum xs = _
    rw [powerSum_eq_sum]

theorem deficient_iff_divisorSum_lt {xs : Coordinates} (hs : PrimeCoordinates xs) :
    (number xs).Deficient ↔ divisorSum xs < 2 * number xs := by
  rw [divisorSum_eq hs, Nat.sum_divisors_eq_sum_properDivisors_add_self]
  unfold Nat.Deficient
  omega

theorem slot_fits_split {s : Slot} {x : ℕ × ℕ} (h : s.Fits x) (hf : s.fixed = false) :
    ({s with fixed := true} : Slot).Fits x ∨ ({s with exponent := s.exponent + 1} : Slot).Fits x := by
  obtain ⟨hp, hq, he, _⟩ := h
  by_cases eq : s.exponent = x.2
  · exact Or.inl ⟨hp, hq, he, fun _ => eq⟩
  · exact Or.inr ⟨hp, hq, by dsimp; omega, by simp [hf]⟩

theorem minimum_dvd {ss : List Slot} {xs : Coordinates} (h : List.Forall₂ Slot.Fits ss xs) :
    number (ss.map Slot.minimum) ∣ number xs := by
  induction h with
  | nil => exact dvd_rfl
  | @cons s x ss xs hfit _ ih =>
    simp only [List.map_cons, number_cons, Slot.minimum, hfit.2.1]
    exact Nat.mul_dvd_mul (pow_dvd_pow _ hfit.2.2.1) ih

theorem exists_fit_of_mem {s : Slot} {ss : List Slot} {xs : Coordinates}
    (h : List.Forall₂ Slot.Fits ss xs) (hm : s ∈ ss) : ∃ x ∈ xs, s.Fits x := by
  induction h with
  | nil => simp at hm
  | @cons t x ts xs hfit ht ih =>
    rcases List.mem_cons.mp hm with rfl | hm
    · exact ⟨x, by simp, hfit⟩
    · obtain ⟨y, hy, hsy⟩ := ih hm
      exact ⟨y, List.mem_cons_of_mem _ hy, hsy⟩

theorem minimum_valid {ss : List Slot} {xs : Coordinates}
    (h : List.Forall₂ Slot.Fits ss xs) (hxs : PrimeCoordinates xs) :
    PrimeCoordinates (ss.map Slot.minimum) := by
  induction h with
  | nil => simp [PrimeCoordinates]
  | @cons s x ss xs hfit ht ih =>
    obtain ⟨hp, hpw⟩ := hxs
    obtain ⟨horder, htail⟩ := List.pairwise_cons.mp hpw
    obtain ⟨htp, htw⟩ := ih ⟨fun y hy => hp y (List.mem_cons_of_mem _ hy), htail⟩
    constructor
    · simp only [List.map_cons, List.mem_cons, forall_eq_or_imp]
      exact ⟨by simpa only [Slot.minimum, hfit.2.1] using hfit.1, htp⟩
    · simp only [List.map_cons, List.pairwise_cons]
      refine ⟨?_, htw⟩
      intro y hy
      obtain ⟨t, htmem, rfl⟩ := List.mem_map.mp hy
      obtain ⟨z, hzmem, hzfit⟩ := exists_fit_of_mem ht htmem
      simpa only [Slot.minimum, hfit.2.1, hzfit.2.1] using horder z hzmem

end OddWeirdSubproblems

namespace OddWeirdSubproblems

open Finset

structure Box where
  slots : List Slot
  next : ℕ
  remaining : ℕ

def Box.Matches (b : Box) (xs ys : Coordinates) : Prop :=
  List.Forall₂ Slot.Fits b.slots xs ∧ TailFits b.next ys ∧ ys.length = b.remaining

def Box.Closed (b : Box) : Prop :=
  ∀ xs ys, b.Matches xs ys → PrimeCoordinates (xs ++ ys) →
    (number (xs ++ ys)).Weird →
    (∀ d ∈ (number (xs ++ ys)).properDivisors, d.Deficient) → False

def Box.minimum (b : Box) : Coordinates := b.slots.map Slot.minimum

def Box.upper (b : Box) : ℚ := (b.slots.map Slot.upper).prod * tailUpper b.next b.remaining

def Slot.upperNum (s : Slot) : ℕ :=
  if s.fixed then powerSum s.prime s.exponent else s.prime

def Slot.upperDen (s : Slot) : ℕ :=
  if s.fixed then s.prime ^ s.exponent else s.prime - 1

def tailNum : ℕ → ℕ → ℕ
  | _, 0 => 1
  | p, r + 1 => p * tailNum (p + 2) r

def tailDen : ℕ → ℕ → ℕ
  | _, 0 => 1
  | p, r + 1 => (p - 1) * tailDen (p + 2) r

def Box.upperNum (b : Box) : ℕ := (b.slots.map Slot.upperNum).prod * tailNum b.next b.remaining

def Box.upperDen (b : Box) : ℕ := (b.slots.map Slot.upperDen).prod * tailDen b.next b.remaining

theorem Slot.upper_eq (s : Slot) (hp : 1 < s.prime) :
    s.upper = (s.upperNum : ℚ) / (s.upperDen : ℚ) := by
  cases hs : s.fixed
  · have h : 1 ≤ s.prime := by omega
    simp [Slot.upper, Slot.upperNum, Slot.upperDen, hs, limitingIndex, Nat.cast_sub h]
  · simp [Slot.upper, Slot.upperNum, Slot.upperDen, hs, index]

theorem slot_upper_eq {ss : List Slot} (h : ∀ s ∈ ss, 1 < s.prime) :
    (ss.map Slot.upper).prod = ((ss.map Slot.upperNum).prod : ℚ) /
      ((ss.map Slot.upperDen).prod : ℚ) := by
  induction ss with
  | nil => simp
  | cons s ss ih =>
    simp only [List.map_cons, List.prod_cons, Nat.cast_mul]
    rw [s.upper_eq (h s (by simp)), ih (fun t ht => h t (by simp [ht])), div_mul_div_comm]

theorem tailUpper_eq {p : ℕ} (hp : 1 < p) (r : ℕ) :
    tailUpper p r = (tailNum p r : ℚ) / (tailDen p r : ℚ) := by
  induction r generalizing p with
  | zero => simp [tailUpper, tailNum, tailDen]
  | succ r ih =>
    simp only [tailUpper, tailNum, tailDen, Nat.cast_mul, limitingIndex]
    rw [ih (by omega), div_mul_div_comm, Nat.cast_sub (show 1 ≤ p by omega)]
    simp

theorem Slot.upperDen_pos (s : Slot) (hp : 1 < s.prime) : 0 < s.upperDen := by
  unfold Slot.upperDen
  split
  · exact pow_pos (by omega) _
  · omega

theorem slot_den_pos {ss : List Slot} (h : ∀ s ∈ ss, 1 < s.prime) :
    0 < (ss.map Slot.upperDen).prod := by
  induction ss with
  | nil => decide
  | cons s ss ih =>
    exact Nat.mul_pos (s.upperDen_pos (h s (by simp))) (ih (fun t ht => h t (by simp [ht])))

theorem tail_den_pos {p : ℕ} (hp : 1 < p) (r : ℕ) : 0 < tailDen p r := by
  induction r generalizing p with
  | zero => simp [tailDen]
  | succ r ih => exact Nat.mul_pos (by omega) (ih (by omega))

theorem close_of_upper_le_two {b : Box} (hnext : 1 < b.next) (hbound : b.upper ≤ 2) :
    b.Closed := by
  intro xs ys ⟨hxs, hys, hylen⟩ hvalid hw _
  have hprod :
      ((xs ++ ys).map fun x => index x.1 x.2).prod ≤ b.upper := by
    rw [List.map_append, List.prod_append, Box.upper, ← hylen]
    have h := slot_prod_upper hxs
    exact mul_le_mul h (tail_prod_upper hnext hys) (coordinate_prod_nonneg _)
      ((coordinate_prod_nonneg _).trans h)
  rw [coordinate_index_eq, divisorSum_eq hvalid, ← Nat.abundancyIndex] at hprod
  exact (Nat.abundant_iff_two_lt_abundancyIndex.mp hw.1).not_ge (hprod.trans hbound)

theorem close_of_upperNum_le {b : Box} (hnext : 1 < b.next)
    (hbound : b.upperNum ≤ 2 * b.upperDen) : b.Closed := by
  intro xs ys hmatch hcoord hw hprim
  have hslot (s : Slot) (hs : s ∈ b.slots) : 1 < s.prime := by
    obtain ⟨x, _, hfit⟩ := exists_fit_of_mem hmatch.1 hs
    rw [hfit.2.1]
    exact hfit.1.one_lt
  have hden : 0 < b.upperDen := Nat.mul_pos (slot_den_pos hslot) (tail_den_pos hnext _)
  have h : b.upper ≤ 2 := by
    rw [Box.upper, slot_upper_eq hslot, tailUpper_eq hnext, div_mul_div_comm, ← Nat.cast_mul, ← Nat.cast_mul]
    change (b.upperNum : ℚ) / (b.upperDen : ℚ) ≤ 2
    rw [div_le_iff₀ (by exact_mod_cast hden)]
    exact_mod_cast hbound
  exact close_of_upper_le_two hnext h xs ys hmatch hcoord hw hprim

theorem primeCoordinates_left {xs ys : Coordinates} (h : PrimeCoordinates (xs ++ ys)) :
    PrimeCoordinates xs :=
  ⟨fun x hx => h.1 x (List.mem_append_left _ hx), (List.pairwise_append.mp h.2).1⟩

theorem close_at_nondeficient_minimum {b : Box}
    (hnondef : 2 * number b.minimum ≤ divisorSum b.minimum)
    (hpoint : ¬ (number b.minimum).Abundant ∨ (number b.minimum).Pseudoperfect ∨
      ∃ d ∈ (number b.minimum).properDivisors, ¬ d.Deficient) :
    b.Closed := by
  intro xs ys ⟨hfit, _, _⟩ hvalid hw hprimitive
  have hdvd : number b.minimum ∣ number (xs ++ ys) := by
    rw [number_append]
    exact dvd_mul_of_dvd_left (minimum_dvd hfit) _
  have hmin : PrimeCoordinates b.minimum := minimum_valid hfit (primeCoordinates_left hvalid)
  have hnd : ¬ (number b.minimum).Deficient :=
    fun h => (deficient_iff_divisorSum_lt hmin).mp h |>.not_ge hnondef
  obtain hlt | heq := lt_or_eq_of_le (Nat.le_of_dvd hw.1.pos hdvd)
  · exact hnd (hprimitive _ (Nat.mem_properDivisors.mpr ⟨hdvd, hlt⟩))
  · rw [heq] at hpoint
    rcases hpoint with h | h | ⟨d, hd, h⟩
    · exact h hw.1
    · exact hw.2 h
    · exact h (hprimitive d hd)

def tightlySorted : List ℕ → Bool
  | [] => true
  | [_] => true
  | a :: b :: as => decide (a < b) && tightlySorted (b :: as)

theorem tightlySorted_pairwise {ds : List ℕ} (h : tightlySorted ds = true) :
    ds.Pairwise (· < ·) := by
  induction ds with
  | nil => exact .nil
  | cons a ds ih =>
    cases ds with
    | nil => exact .cons (by simp) .nil
    | cons b ds =>
      simp only [tightlySorted, Bool.and_eq_true, decide_eq_true_eq] at h
      have hpw := ih h.2
      refine .cons ?_ hpw
      intro c hc
      rcases List.mem_cons.mp hc with rfl | hc
      · exact h.1
      · exact h.1.trans ((List.pairwise_cons.mp hpw).1 c hc)

theorem tightlySorted_nodup {ds : List ℕ} (h : tightlySorted ds = true) : ds.Nodup :=
  (tightlySorted_pairwise h).imp Nat.ne_of_lt

theorem pseudoperfect_of_excess_list {n : ℕ} {ds : List ℕ}
    (hn : 0 < n) (hnodup : ds.Nodup) (hdivs : ∀ d ∈ ds, d ∣ n ∧ d < n)
    (hsum : ∑ d ∈ n.divisors, d = 2 * n + ds.sum) : n.Pseudoperfect := by
  have hds : ∑ d ∈ ds.toFinset, d = ds.sum := by
    clear hsum hdivs
    induction ds with
    | nil => simp
    | cons d ds ih =>
      obtain ⟨hd, hnd⟩ := List.nodup_cons.mp hnodup
      have hd' : d ∉ ds.toFinset := by simpa using hd
      rw [List.toFinset_cons, sum_insert hd', List.sum_cons, ih hnd]
  have hsub : ds.toFinset ⊆ n.properDivisors := by
    intro d hd
    exact Nat.mem_properDivisors.mpr (hdivs d (List.mem_toFinset.mp hd))
  refine ⟨hn, n.properDivisors \ ds.toFinset, sdiff_subset, ?_⟩
  have hdiff := sum_sdiff (f := fun d : ℕ => d) hsub
  rw [Nat.sum_divisors_eq_sum_properDivisors_add_self] at hsum
  omega

theorem close_minimum_eq_two {b : Box}
    (h : divisorSum b.minimum = 2 * number b.minimum) : b.Closed := by
  intro xs ys hmatch hvalid hw hproper
  have hv : PrimeCoordinates b.minimum := minimum_valid hmatch.1 (primeCoordinates_left hvalid)
  have hp : ¬ (number b.minimum).Abundant := by
    rw [Nat.abundant_iff_sum_divisors, ← divisorSum_eq hv, h]
    exact lt_irrefl _
  exact close_at_nondeficient_minimum h.ge (Or.inl hp) xs ys hmatch hvalid hw hproper

theorem close_minimum_witness {b : Box} {ds : List ℕ}
    (hnodup : ds.Nodup) (hdivs : ∀ d ∈ ds, d ∣ number b.minimum ∧ d < number b.minimum)
    (hsum : divisorSum b.minimum = 2 * number b.minimum + ds.sum) : b.Closed := by
  intro xs ys hmatch hvalid hw hproper
  have hv : PrimeCoordinates b.minimum := minimum_valid hmatch.1 (primeCoordinates_left hvalid)
  have hnondef : 2 * number b.minimum ≤ divisorSum b.minimum := by omega
  have h : (number b.minimum).Pseudoperfect := pseudoperfect_of_excess_list
    (number_pos hv.1) hnodup hdivs (divisorSum_eq hv ▸ hsum)
  exact close_at_nondeficient_minimum hnondef (Or.inr (Or.inl h)) xs ys hmatch hvalid hw hproper

theorem close_minimum_has_nondeficient_divisor {b : Box} {d : ℕ}
    (hnondef : 2 * number b.minimum ≤ divisorSum b.minimum)
    (hdvd : d ∣ number b.minimum) (hdlt : d < number b.minimum) (hd : ¬ d.Deficient) :
    b.Closed :=
  close_at_nondeficient_minimum hnondef (Or.inr (Or.inr
    ⟨d, Nat.mem_properDivisors.mpr ⟨hdvd, hdlt⟩, hd⟩))

theorem forall₂_slot_split {ss : List Slot} {xs : Coordinates} {i : ℕ} {s : Slot}
    (h : List.Forall₂ Slot.Fits ss xs) (hi : ss[i]? = some s) (hf : s.fixed = false) :
    List.Forall₂ Slot.Fits (ss.set i {s with fixed := true}) xs ∨
    List.Forall₂ Slot.Fits (ss.set i {s with exponent := s.exponent + 1}) xs := by
  induction h generalizing i with
  | nil => simp at hi
  | @cons t x ss xs hfit _ ih =>
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
      subst t
      rcases slot_fits_split hfit hf with h | h
      · exact Or.inl (.cons h (by assumption))
      · exact Or.inr (.cons h (by assumption))
    | succ i =>
      simp only [List.getElem?_cons_succ] at hi
      rcases ih hi with h | h
      · exact Or.inl (.cons hfit h)
      · exact Or.inr (.cons hfit h)

theorem close_split_slot {b : Box} {i : ℕ} {s : Slot}
    (hi : b.slots[i]? = some s) (hf : s.fixed = false)
    (h₁ : ({b with slots := b.slots.set i {s with fixed := true}} : Box).Closed)
    (h₂ : ({b with slots := b.slots.set i {s with exponent := s.exponent + 1}} : Box).Closed) :
    b.Closed := by
  intro xs ys ⟨hf₂, ht, hr⟩ hp hw hprim
  rcases forall₂_slot_split hf₂ hi hf with h | h
  · exact h₁ xs ys ⟨h, ht, hr⟩ hp hw hprim
  · exact h₂ xs ys ⟨h, ht, hr⟩ hp hw hprim

theorem close_split_next {ss : List Slot} {p r : ℕ} (hodd : Odd p)
    (hskip : (⟨ss, p + 2, r + 1⟩ : Box).Closed)
    (htake : p.Prime → (⟨ss ++ [⟨p, 1, false⟩], p + 2, r⟩ : Box).Closed) :
    (⟨ss, p, r + 1⟩ : Box).Closed := by
  intro xs ys ⟨hx, hy, hlen⟩ hcoord hw hprim
  cases ys with
  | nil => simp at hlen
  | cons y ys =>
    obtain ⟨q, e⟩ := y
    obtain ⟨hpq, hqlo, hq, hqodd, he, ht⟩ := hy
    change p ≤ q at hpq
    by_cases heq : q = p
    · subst q
      have hfit : Slot.Fits ⟨p, 1, false⟩ (p, e) :=
        ⟨hq, rfl, he, by simp⟩
      have eq : xs ++ (p, e) :: ys = (xs ++ [(p, e)]) ++ ys := by
        simp [List.append_assoc]
      rw [eq] at hcoord hw hprim
      exact htake hq (xs ++ [(p, e)]) ys
        ⟨List.rel_append hx (.cons hfit .nil), ht, by simpa using hlen⟩ hcoord hw hprim
    · have hlt : p + 2 ≤ q := by
        obtain ⟨a, ha⟩ := hodd
        obtain ⟨b, hb⟩ := hqodd
        omega
      exact hskip xs ((q, e) :: ys) ⟨hx, ⟨hlt, hqlo, hq, hqodd, he, ht⟩, hlen⟩ hcoord hw hprim

theorem number_gt_one_of_tail {p : ℕ} {ys : Coordinates} (h : TailFits p ys)
    (hne : ys ≠ []) : 1 < number ys := by
  induction ys generalizing p with
  | nil => contradiction
  | cons y ys ih =>
    obtain ⟨q, e⟩ := y
    obtain ⟨_, hq, hprime, _, he, ht⟩ := h
    have hpow : 1 < q ^ e := one_lt_pow₀ (by omega) he.ne'
    rw [number_cons]
    change 1 < q ^ e * number ys
    by_cases hnil : ys = []
    · simpa [hnil, number] using hpow
    · exact hpow.trans_le (Nat.le_mul_of_pos_right _ (ih ht hnil).pos)

theorem close_minimum_with_tail {b : Box} (hr : 0 < b.remaining)
    (hnondef : 2 * number b.minimum ≤ divisorSum b.minimum) : b.Closed := by
  intro xs ys ⟨hfit, htail, hylen⟩ hvalid hw hprimitive
  have hne : ys ≠ [] := by
    rintro rfl
    simp at hylen
    omega
  have hlarge := number_gt_one_of_tail htail hne
  have hxs : 0 < number xs := number_pos (primeCoordinates_left hvalid).1
  have hdvd := minimum_dvd hfit
  have hlt : number b.minimum < number (xs ++ ys) := by
    rw [number_append]
    exact (Nat.le_of_dvd hxs hdvd).trans_lt (by
      simpa using (Nat.mul_lt_mul_of_pos_left hlarge hxs))
  have hmem : number b.minimum ∈ (number (xs ++ ys)).properDivisors :=
    Nat.mem_properDivisors.mpr ⟨by
      rw [number_append]
      exact dvd_mul_of_dvd_left hdvd _, hlt⟩
  have hv : PrimeCoordinates b.minimum := minimum_valid hfit (primeCoordinates_left hvalid)
  exact (deficient_iff_divisorSum_lt hv).mp (hprimitive _ hmem) |>.not_ge hnondef

def decrement : Coordinates → ℕ → Coordinates
  | [], _ => []
  | (p, e) :: xs, 0 => (p, e - 1) :: xs
  | x :: xs, i + 1 => x :: decrement xs i

theorem decrement_primes (xs : Coordinates) (i : ℕ) :
    (decrement xs i).map Prod.fst = xs.map Prod.fst := by
  induction xs generalizing i with
  | nil => simp [decrement]
  | cons x xs ih =>
    rcases x with ⟨p, e⟩
    cases i with
    | zero => rfl
    | succ i => simp [decrement, ih i]

theorem decrement_coordinates {xs : Coordinates} (h : PrimeCoordinates xs) (i : ℕ) :
    PrimeCoordinates (decrement xs i) := by
  have hprime (ls : Coordinates) :
      (∀ x ∈ ls, Nat.Prime x.1) ↔ ∀ p ∈ ls.map Prod.fst, Nat.Prime p := by simp
  have hordered (ls : Coordinates) :
      ls.Pairwise (fun x y => x.1 < y.1) ↔ (ls.map Prod.fst).Pairwise (· < ·) :=
    List.pairwise_map.symm
  rw [PrimeCoordinates, hprime, hordered, decrement_primes]
  exact ⟨(hprime xs).mp h.1, (hordered xs).mp h.2⟩

theorem decrement_dvd (xs : Coordinates) (i : ℕ) :
    number (decrement xs i) ∣ number xs := by
  induction xs generalizing i with
  | nil => simp [decrement]
  | cons x xs ih =>
    rcases x with ⟨p, e⟩
    cases i with
    | zero =>
      simp only [decrement, number_cons]
      exact Nat.mul_dvd_mul (pow_dvd_pow p (Nat.sub_le e 1)) dvd_rfl
    | succ i =>
      exact Nat.mul_dvd_mul dvd_rfl (ih i)

theorem close_minimum_decrement {b : Box} {i : ℕ}
    (hnondef : 2 * number b.minimum ≤ divisorSum b.minimum)
    (hlt : number (decrement b.minimum i) < number b.minimum)
    (hdec : 2 * number (decrement b.minimum i) ≤ divisorSum (decrement b.minimum i)) :
    b.Closed := by
  intro xs ys hfit hvalid hw hprim
  have hv : PrimeCoordinates b.minimum := minimum_valid hfit.1 (primeCoordinates_left hvalid)
  have hd : ¬ (number (decrement b.minimum i)).Deficient :=
    fun h => (deficient_iff_divisorSum_lt (decrement_coordinates hv i)).mp h |>.not_ge hdec
  exact close_minimum_has_nondeficient_divisor hnondef (decrement_dvd b.minimum i)
    hlt hd xs ys hfit hvalid hw hprim

end OddWeirdSubproblems

namespace OddWeirdSubproblems

open scoped BigOperators

def primeCoordinates (n : ℕ) : List (ℕ × ℕ) :=
  n.primeFactors.sort.map (fun p => (p, n.factorization p))

theorem mem_primeCoordinates {n p a : ℕ} :
    (p, a) ∈ primeCoordinates n ↔ p ∈ n.primeFactors ∧ a = n.factorization p := by
  simp only [primeCoordinates, List.mem_map, Finset.mem_sort, Prod.mk.injEq]
  constructor
  · rintro ⟨q, hq, rfl, rfl⟩
    exact ⟨hq, rfl⟩
  · rintro ⟨hp, rfl⟩
    exact ⟨p, hp, rfl, rfl⟩

theorem primeCoordinates_pairwise (n : ℕ) :
    (primeCoordinates n).Pairwise (fun x y => x.1 < y.1) := by
  simpa only [primeCoordinates, List.pairwise_map] using n.primeFactors.sortedLT_sort.pairwise

theorem primeCoordinates_length (n : ℕ) :
    (primeCoordinates n).length = n.primeFactors.card := by
  simp [primeCoordinates, Finset.length_sort]

theorem primeCoordinates_prime_pos {n : ℕ} {x : ℕ × ℕ}
    (hx : x ∈ primeCoordinates n) : x.1.Prime ∧ 0 < x.2 := by
  obtain ⟨p, a⟩ := x
  obtain ⟨hp, rfl⟩ := mem_primeCoordinates.mp hx
  exact ⟨Nat.prime_of_mem_primeFactors hp, by
    rw [Nat.pos_iff_ne_zero, ← Finsupp.mem_support_iff, Nat.support_factorization]
    exact hp⟩

theorem primeCoordinates_odd {n : ℕ} (hn : Odd n) {x : ℕ × ℕ}
    (hx : x ∈ primeCoordinates n) : Odd x.1 := by
  obtain ⟨p, a⟩ := x
  exact hn.of_dvd_nat (Nat.dvd_of_mem_primeFactors (mem_primeCoordinates.mp hx).1)

theorem primeCoordinates_prod_map (n : ℕ) (f : ℕ × ℕ → ℕ) :
    ((primeCoordinates n).map f).prod =
      ∏ p ∈ n.primeFactors, f (p, n.factorization p) := by
  rw [primeCoordinates, List.map_map, ← List.prod_toFinset _ (Finset.sort_nodup _ _),
    Finset.sort_toFinset]
  rfl

theorem primeCoordinates_prod {n : ℕ} (hn : n ≠ 0) :
    ((primeCoordinates n).map (fun x => x.1 ^ x.2)).prod = n := by
  rw [primeCoordinates_prod_map]
  exact (Nat.prod_primeFactors_pow_factorization hn).symm

theorem primeCoordinates_three {n : ℕ} (hodd : Odd n) (hthree : 3 ∣ n) :
    ∃ xs : List (ℕ × ℕ), primeCoordinates n = (3, n.factorization 3) :: xs ∧
      ∀ x ∈ xs, 5 ≤ x.1 := by
  have hp : 3 ∈ n.primeFactors := Nat.mem_primeFactors.mpr
    ⟨by decide, hthree, hodd.pos.ne'⟩
  let tail := n.primeFactors.erase 3
  have htail (p : ℕ) (hp' : p ∈ tail) : 5 ≤ p := by
    obtain ⟨hne, hmem⟩ := Finset.mem_erase.mp hp'
    have hmin := (Nat.prime_of_mem_primeFactors hmem).one_lt
    obtain ⟨k, hk⟩ := hodd.of_dvd_nat (Nat.dvd_of_mem_primeFactors hmem)
    omega
  have hlo : ∀ p ∈ tail, 3 ≤ p := fun p hp' => (show 3 ≤ 5 by decide).trans (htail p hp')
  have hn3 : 3 ∉ tail := Finset.notMem_erase _ _
  refine ⟨tail.sort.map (fun p => (p, n.factorization p)), ?_, ?_⟩
  · rw [primeCoordinates, ← Finset.insert_erase hp, Finset.sort_insert (· ≤ ·) hlo hn3]
    rfl
  · intro x hx
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
    exact htail p ((Finset.mem_sort (· ≤ ·)).mp hp)

end OddWeirdSubproblems

namespace OddWeirdSubproblems

open Finset

theorem pseudoperfectOfDvd {d n : ℕ} (hn : 0 < n) (hd : d ∣ n)
    (hp : d.Pseudoperfect) : n.Pseudoperfect := by
  obtain ⟨k, rfl⟩ := hd
  obtain ⟨_, s, hsub, hsum⟩ := hp
  have hk := Nat.pos_of_mul_pos_left hn
  let scale : ℕ ↪ ℕ := ⟨(· * k), fun _ _ h => Nat.eq_of_mul_eq_mul_right hk h⟩
  refine ⟨hn, s.map scale, ?_, ?_⟩
  · intro x hx
    obtain ⟨a, ha, rfl⟩ := mem_map.mp hx
    obtain ⟨had, halt⟩ := Nat.mem_properDivisors.mp (hsub ha)
    exact Nat.mem_properDivisors.mpr
      ⟨Nat.mul_dvd_mul_right had k, Nat.mul_lt_mul_of_pos_right halt hk⟩
  · rw [sum_map]
    change (∑ a ∈ s, a * k) = d * k
    rw [← sum_mul, hsum]

theorem primitiveWeirdDivisor {n : ℕ} (hw : n.Weird) :
    ∃ d : ℕ, d ∣ n ∧ d.Weird ∧ ∀ k ∈ d.properDivisors, k.Deficient := by
  have hex : ∃ d : ℕ, d ∣ n ∧ ¬ d.Deficient :=
    ⟨n, dvd_rfl, fun h => (not_lt_of_gt hw.1) h⟩
  let d := Nat.find hex
  have hd : d ∣ n := (Nat.find_spec hex).1
  have hnd : ¬ d.Deficient := (Nat.find_spec hex).2
  have hpos : 0 < d := Nat.pos_of_dvd_of_pos hd hw.1.pos
  have hnp : ¬ d.Pseudoperfect := fun hp => hw.2 (pseudoperfectOfDvd hw.1.pos hd hp)
  refine ⟨d, hd, ⟨?_, hnp⟩, ?_⟩
  · by_contra hna
    exact hnp (((Nat.perfect_iff_not_abundant_and_not_deficient hpos.ne).2
      ⟨hna, hnd⟩).pseudoperfect)
  · intro k hk
    obtain ⟨hkd, hlt⟩ := Nat.mem_properDivisors.mp hk
    by_contra! hndef
    exact (not_le_of_gt hlt) (Nat.find_min' hex ⟨hkd.trans hd, hndef⟩)

theorem primeDivisorNcard (n : ℕ) :
    {p : ℕ | p ∈ n.divisors ∧ p.Prime}.ncard = n.primeFactors.card := by
  have hs : {p : ℕ | p ∈ n.divisors ∧ p.Prime} = (n.primeFactors : Set ℕ) := by
    ext p
    simp only [Set.mem_ofPred_eq, Finset.mem_coe, Nat.mem_primeFactors, Nat.mem_divisors]
    tauto
  rw [hs, Set.ncard_coe_finset]

theorem atLeastSixOfPrimitive
    (verify : ∀ m : ℕ, Odd m → m.Abundant → m.primeFactors.card ≤ 5 →
      (∀ d ∈ m.properDivisors, d.Deficient) → m.Pseudoperfect) :
    ∀ n : ℕ, Odd n → n.Weird → 6 ≤ {p : ℕ | p ∈ n.divisors ∧ p.Prime}.ncard := by
  intro n ho hw
  rw [primeDivisorNcard]
  by_contra! hc
  obtain ⟨d, hd, hdw, hproper⟩ := primitiveWeirdDivisor hw
  have hcard := Finset.card_le_card (Nat.primeFactors_mono hd hw.1.pos.ne')
  exact hdw.2 (verify d (ho.of_dvd_nat hd) hdw.1 (by omega) hproper)

end OddWeirdSubproblems

namespace OddWeird

def primeSaturationRatio (p : ℕ) : ℚ := 1 + 1 / ((p : ℚ) - 1)

private theorem primeSaturationRatio_one_le {p : ℕ} (hp : 1 < p) :
    1 ≤ primeSaturationRatio p := by
  have hp' : (1 : ℚ) < p := by exact_mod_cast hp
  have hinv : (0 : ℚ) ≤ 1 / ((p : ℚ) - 1) := by positivity
  unfold primeSaturationRatio
  linarith

private theorem primeSaturationRatio_antitone {a b : ℕ} (ha : 1 < a) (hab : a ≤ b) :
    primeSaturationRatio b ≤ primeSaturationRatio a := by
  have ha' : (1 : ℚ) < a := by exact_mod_cast ha
  have hab' : (a : ℚ) ≤ b := by exact_mod_cast hab
  simpa only [primeSaturationRatio, add_comm] using add_le_add_left
    (one_div_le_one_div_of_le (sub_pos.mpr ha') (sub_le_sub_right hab' 1)) 1

private theorem primeSaturationRatio_prod_le (k : ℕ) (S : Finset ℕ) (b : ℕ) (hb : 1 < b)
    (hcard : S.card = k) (hS : ∀ p ∈ S, Odd p ∧ b ≤ p) :
    (∏ p ∈ S, primeSaturationRatio p) ≤
      ∏ i ∈ Finset.range k, primeSaturationRatio (b + 2 * i) := by
  induction k generalizing S b with
  | zero => simp [Finset.card_eq_zero.mp hcard]
  | succ k ih =>
    have hne : S.Nonempty := Finset.card_pos.mp (by omega)
    let p := S.min' hne
    have hp : p ∈ S := Finset.min'_mem S hne
    have htail (q : ℕ) (hq : q ∈ S.erase p) : Odd q ∧ b + 2 ≤ q := by
      obtain ⟨hqne, hqS⟩ := Finset.mem_erase.mp hq
      have hpq : p ≤ q := Finset.min'_le S q hqS
      obtain ⟨hpo, hbp⟩ := hS p hp
      obtain ⟨hqo, _⟩ := hS q hqS
      refine ⟨hqo, ?_⟩
      rcases hpo with ⟨a, ha⟩
      rcases hqo with ⟨c, hc⟩
      omega
    have hc : (S.erase p).card = k := by rw [Finset.card_erase_of_mem hp, hcard]; omega
    have htailLe := ih (S.erase p) (b + 2) (by omega) hc htail
    rw [← Finset.prod_erase_mul S primeSaturationRatio hp,
      Finset.prod_range_succ', Nat.mul_zero, Nat.add_zero]
    have hshift : ∏ i ∈ Finset.range k, primeSaturationRatio (b + 2 + 2 * i) =
        ∏ i ∈ Finset.range k, primeSaturationRatio (b + 2 * (i + 1)) := by
      refine Finset.prod_congr rfl fun i _ => ?_
      congr 1
      omega
    refine mul_le_mul (htailLe.trans_eq hshift) (primeSaturationRatio_antitone hb (hS p hp).2)
      (zero_le_one.trans (primeSaturationRatio_one_le (hb.trans_le (hS p hp).2))) ?_
    exact Finset.prod_nonneg fun i _ => zero_le_one.trans (primeSaturationRatio_one_le (by omega))

private theorem geomRatio_le_primeSaturationRatio (p a : ℕ) (hp : 1 < p) :
    (∑ i ∈ Finset.range (a + 1), (p : ℚ) ^ i) / (p : ℚ) ^ a ≤ primeSaturationRatio p := by
  have hp' : (1 : ℚ) < p := by exact_mod_cast hp
  have hm : (0 : ℚ) < (p : ℚ) - 1 := sub_pos.mpr hp'
  have hpow : (0 : ℚ) < (p : ℚ) ^ a := by positivity
  have hr : primeSaturationRatio p = (p : ℚ) / ((p : ℚ) - 1) := by
    unfold primeSaturationRatio
    apply (eq_div_iff hm.ne').mpr
    rw [add_mul, one_mul, div_mul_cancel₀ _ hm.ne']
    ring
  rw [hr, div_le_div_iff₀ hpow hm, geom_sum_mul, pow_succ]
  linarith

private theorem abundancyIndex_eq_factorization_product {n : ℕ} (hn : n ≠ 0) :
    n.abundancyIndex = ∏ p ∈ n.primeFactors,
      (∑ i ∈ Finset.range (n.factorization p + 1), (p : ℚ) ^ i) / (p : ℚ) ^ n.factorization p := by
  have hsigma := ArithmeticFunction.sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul
    (k := 1) hn
  rw [ArithmeticFunction.sigma_one_apply] at hsigma
  simp only [mul_one] at hsigma
  have hpow := Nat.prod_primeFactors_pow_factorization hn
  rw [Nat.abundancyIndex, hsigma]
  conv_lhs =>
    arg 2
    rw [hpow]
  simp only [Nat.cast_prod, Nat.cast_sum, Nat.cast_pow, ← Finset.prod_div_distrib]

theorem abundancyIndex_le_of_odd_of_primeFactors_sdiff_card_le {n b k : ℕ} {E : Finset ℕ}
    (hodd : Odd n) (hb : 1 < b) (hcard : (n.primeFactors \ E).card ≤ k)
    (hmin : ∀ p ∈ n.primeFactors \ E, b ≤ p) :
    n.abundancyIndex ≤
      (∏ p ∈ n.primeFactors ∩ E,
        (∑ i ∈ Finset.range (n.factorization p + 1), (p : ℚ) ^ i) / (p : ℚ) ^ n.factorization p) *
      ∏ i ∈ Finset.range k, primeSaturationRatio (b + 2 * i) := by
  have hn : n ≠ 0 := by
    rcases hodd with ⟨a, ha⟩
    omega
  let S := n.primeFactors \ E
  let R (p : ℕ) :=
    (∑ i ∈ Finset.range (n.factorization p + 1), (p : ℚ) ^ i) / (p : ℚ) ^ n.factorization p
  have hR (p : ℕ) : 0 ≤ R p := by
    unfold R
    positivity
  have hS (p : ℕ) (hp : p ∈ S) : Odd p ∧ b ≤ p :=
    ⟨hodd.of_dvd_nat (Nat.dvd_of_mem_primeFactors (Finset.mem_sdiff.mp hp).1), hmin p hp⟩
  have hproduct : (∏ p ∈ S, R p) ≤ ∏ i ∈ Finset.range k, primeSaturationRatio (b + 2 * i) := by
    calc
      _ ≤ ∏ p ∈ S, primeSaturationRatio p :=
        Finset.prod_le_prod (fun p _ => hR p) (fun p hp =>
          geomRatio_le_primeSaturationRatio p _ (hb.trans_le (hmin p hp)))
      _ ≤ ∏ i ∈ Finset.range S.card, primeSaturationRatio (b + 2 * i) :=
        primeSaturationRatio_prod_le _ S b hb rfl hS
      _ ≤ ∏ i ∈ Finset.range k, primeSaturationRatio (b + 2 * i) :=
        Finset.prod_le_prod_of_subset_of_one_le (Finset.range_mono hcard)
          (fun i _ => zero_le_one.trans (primeSaturationRatio_one_le (by omega)))
          (fun i _ _ => primeSaturationRatio_one_le (by omega))
  rw [abundancyIndex_eq_factorization_product hn]
  change (∏ p ∈ n.primeFactors, R p) ≤ (∏ p ∈ n.primeFactors ∩ E, R p) * _
  conv_lhs =>
    rw [← Finset.sdiff_union_inter n.primeFactors E,
      Finset.prod_union (Finset.disjoint_sdiff_inter n.primeFactors E),
      mul_comm (∏ p ∈ S, R p)]
  exact mul_le_mul_of_nonneg_left hproduct (Finset.prod_nonneg fun p _ => hR p)

theorem deficient_of_odd_of_primeFactors_card_le_five_of_not_three_dvd {n : ℕ}
    (hodd : Odd n) (hcard : n.primeFactors.card ≤ 5) (hthree : ¬ 3 ∣ n) : n.Deficient := by
  have hn : n ≠ 0 := by
    rintro rfl
    exact hthree (dvd_zero 3)
  have hS (p : ℕ) (hp : p ∈ n.primeFactors) : 5 ≤ p := by
    have hpn := Nat.dvd_of_mem_primeFactors hp
    have hpo := hodd.of_dvd_nat hpn
    have hp3 : p ≠ 3 := fun h => hthree (h ▸ hpn)
    have hp1 := (Nat.prime_of_mem_primeFactors hp).one_lt
    rcases hpo with ⟨a, ha⟩
    omega
  have hindex : n.abundancyIndex ≤ ∏ i ∈ Finset.range 5, primeSaturationRatio (5 + 2 * i) := by
    simpa using abundancyIndex_le_of_odd_of_primeFactors_sdiff_card_le (E := ∅) (k := 5)
      hodd (b := 5) (by decide) (by simpa using hcard) (fun p hp => hS p (by simpa using hp))
  have h := hindex.trans_lt (show (∏ i ∈ Finset.range 5, primeSaturationRatio (5 + 2 * i)) < 2 by
    norm_num [Finset.prod_range_succ, primeSaturationRatio])
  have hn' : (0 : ℚ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  rw [Nat.abundancyIndex, div_lt_iff₀ hn'] at h
  have hsum : ∑ d ∈ n.divisors, d < 2 * n := by exact_mod_cast h
  rw [Nat.sum_divisors_eq_sum_properDivisors_add_self] at hsum
  unfold Nat.Deficient
  omega

end OddWeird

namespace OddWeirdSubproblems

theorem noPrimitiveWeird_three_of_coordinate_roots {k lower : ℕ} {fixed : Bool}
    (roots : ∀ r ≤ k, (⟨[⟨3, lower, fixed⟩], 5, r⟩ : Box).Closed)
    {n : ℕ} (ho : Odd n) (hw : n.Weird) (hc : n.primeFactors.card ≤ k + 1)
    (hproper : ∀ d ∈ n.properDivisors, d.Deficient) (h3 : 3 ∣ n)
    (hval : lower ≤ n.factorization 3) (hfixed : fixed = true → lower = n.factorization 3) :
    False := by
  obtain ⟨ys, hys, hmin⟩ := primeCoordinates_three ho h3
  let xs : Coordinates := [(3, n.factorization 3)]
  have hcat : primeCoordinates n = xs ++ ys := hys
  have hn : number (xs ++ ys) = n := by
    rw [← hcat]
    exact primeCoordinates_prod ho.pos.ne'
  have hpw : (xs ++ ys).Pairwise (fun x y => x.1 < y.1) := hcat ▸ primeCoordinates_pairwise n
  have hprime (x : ℕ × ℕ) (hx : x ∈ xs ++ ys) : x.1.Prime ∧ 0 < x.2 :=
    primeCoordinates_prime_pos (hcat.symm ▸ hx)
  have hlen := primeCoordinates_length n
  rw [hcat] at hlen
  simp only [xs, List.cons_append, List.nil_append, List.length_cons] at hlen
  have hlen' : ys.length ≤ k := by omega
  have ht : TailFits 5 ys := by
    apply tailFits_of_sorted (by decide : 2 < 5) hmin _
      (List.pairwise_append.mp hpw).2.1
    intro x hx
    have hxmem : x ∈ xs ++ ys := List.mem_append_right _ hx
    exact ⟨(hprime x hxmem).1, primeCoordinates_odd ho (hcat.symm ▸ hxmem),
      (hprime x hxmem).2⟩
  have hfit : List.Forall₂ Slot.Fits [⟨3, lower, fixed⟩] xs :=
    .cons ⟨show Nat.Prime 3 by decide, rfl, hval, hfixed⟩ .nil
  exact roots ys.length hlen' xs ys ⟨hfit, ht, rfl⟩ ⟨fun x hx => (hprime x hx).1, hpw⟩
    (hn.symm ▸ hw) (hn.symm ▸ hproper)

theorem atLeastSix_of_threeRoots
    (one : ∀ r ≤ 4, (⟨[⟨3, 1, true⟩], 5, r⟩ : Box).Closed)
    (high : ∀ r ≤ 4, (⟨[⟨3, 2, false⟩], 5, r⟩ : Box).Closed) :
    ∀ n : ℕ, Odd n → n.Weird → 6 ≤ {p : ℕ | p ∈ n.divisors ∧ p.Prime}.ncard := by
  apply atLeastSixOfPrimitive
  intro n ho ha hc hproper
  by_contra hpp
  have h3 : 3 ∣ n := by
    by_contra h
    exact (not_lt_of_gt ha)
      (OddWeird.deficient_of_odd_of_primeFactors_card_le_five_of_not_three_dvd ho hc h)
  have hprime : Nat.Prime 3 := by decide
  have hpositive := hprime.factorization_pos_of_dvd ho.pos.ne' h3
  by_cases h9 : 2 ≤ n.factorization 3
  · exact noPrimitiveWeird_three_of_coordinate_roots high ho ⟨ha, hpp⟩ hc hproper h3 h9
      (by simp)
  · exact noPrimitiveWeird_three_of_coordinate_roots one ho ⟨ha, hpp⟩ hc hproper h3
      (by omega) (by omega)

end OddWeirdSubproblems

namespace OddWeirdSubproblems

def witnessOk (n s : ℕ) (ds : List ℕ) : Bool :=
  ds.all (fun d => decide (d ∣ n ∧ d < n)) && tightlySorted ds && decide (s = 2 * n + ds.sum)

theorem witnessOk_closes {b : Box} {ds : List ℕ}
    (h : witnessOk (number b.minimum) (divisorSum b.minimum) ds = true) :
    b.Closed := by
  simp only [witnessOk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  exact close_minimum_witness (tightlySorted_nodup h.1.2) (by simpa using h.1.1) h.2

def decrementOk (fs : Coordinates) (i : ℕ) : Bool :=
  let ds := decrement fs i
  decide (number ds < number fs ∧ 2 * number ds ≤ divisorSum ds)

def minimumOk (witness : ℕ → List ℕ) (b : Box) : Bool :=
  let n := number b.minimum
  let s := divisorSum b.minimum
  decide (0 < b.remaining) || decide (s = 2 * n) ||
    (List.range b.slots.length).any (decrementOk b.minimum) || witnessOk n s (witness n)

theorem minimumOk_closes {witness : ℕ → List ℕ} {b : Box}
    (hnondef : 2 * number b.minimum ≤ divisorSum b.minimum)
    (h : minimumOk witness b = true) : b.Closed := by
  simp only [minimumOk, Bool.or_eq_true, decide_eq_true_eq, List.any_eq_true] at h
  rcases h with ((h | h) | h) | h
  · exact close_minimum_with_tail h hnondef
  · exact close_minimum_eq_two h
  · obtain ⟨i, _, hi⟩ := h
    simp only [decrementOk, decide_eq_true_eq] at hi
    exact close_minimum_decrement hnondef hi.1 hi.2
  · exact witnessOk_closes h

def chooseSlot (b : Box) : Option ℕ :=
  ((b.slots.zipIdx.filter (fun (s, _) => !s.fixed)).foldl
    (fun best (s, i) =>
      let key := s.prime ^ (s.exponent + 1)
      if (b.remaining == 0 || key < b.next) && key < best.1
      then (key, some i) else best)
    (b.slots.foldl (fun n s => max n (s.prime ^ (s.exponent + 1) + 1)) 1, none)).2

def replay (witness : ℕ → List ℕ) : ℕ → Box → Bool
  | 0, _ => false
  | fuel + 1, b =>
    if 2 * number b.minimum ≤ divisorSum b.minimum then minimumOk witness b
    else if b.upperNum ≤ 2 * b.upperDen then true
    else match (chooseSlot b).bind (fun i => b.slots[i]?.map (fun s => (i, s))) with
    | some (i, s) =>
      if s.fixed then false else
      replay witness fuel {b with slots := b.slots.set i {s with fixed := true}} &&
      replay witness fuel {b with slots := b.slots.set i {s with exponent := s.exponent + 1}}
    | none =>
      match b.remaining with
      | 0 => false
      | r + 1 =>
        replay witness fuel ⟨b.slots, b.next + 2, r + 1⟩ &&
        if b.next.minFac = b.next then
          replay witness fuel ⟨b.slots ++ [⟨b.next, 1, false⟩], b.next + 2, r⟩
        else true

theorem replay_closes {witness : ℕ → List ℕ} {fuel : ℕ} {b : Box}
    (hlo : 1 < b.next) (hodd : Odd b.next) (h : replay witness fuel b = true) :
    b.Closed := by
  induction fuel generalizing b with
  | zero => simp [replay] at h
  | succ fuel ih =>
    rw [replay] at h
    split at h
    · exact minimumOk_closes ‹_› h
    split at h
    · exact close_of_upperNum_le hlo ‹_›
    split at h
    next i s hs =>
      have hi : b.slots[i]? = some s := by
        have hb := Option.bind_eq_some_iff.mp hs
        obtain ⟨j, _, hj⟩ := hb
        cases hg : b.slots[j]? <;> simp_all
      split at h
      · contradiction
      · have hf : s.fixed = false := by simp_all
        obtain ⟨h₁, h₂⟩ := Bool.and_eq_true_iff.mp h
        exact close_split_slot hi hf (ih hlo hodd h₁) (ih hlo hodd h₂)
    next =>
      rcases b with ⟨ss, p, r⟩
      cases r with
      | zero => contradiction
      | succ r =>
        obtain ⟨hskip, htake⟩ := Bool.and_eq_true_iff.mp h
        have hodd' : Odd (p + 2) := by
          obtain ⟨k, hk⟩ := hodd
          exact ⟨k + 1, by dsimp at hk; omega⟩
        have hlo' : 1 < p + 2 := by dsimp at hlo; omega
        apply close_split_next hodd (ih hlo' hodd' hskip)
        intro hp
        exact ih hlo' hodd' (by simpa only [if_pos hp.minFac_eq] using htake)

def slotEqual (a b : Slot) : Bool :=
  decide ((a.prime, a.exponent, a.fixed) = (b.prime, b.exponent, b.fixed))

theorem slotEqual_iff_eq (a b : Slot) : slotEqual a b = true ↔ a = b := by
  cases a; cases b; simp [slotEqual, Slot.mk.injEq]

def slotsEqual : List Slot → List Slot → Bool
  | [], [] => true
  | a :: as, b :: bs => slotEqual a b && slotsEqual as bs
  | _, _ => false

theorem slotsEqual_iff_eq (as bs : List Slot) : slotsEqual as bs = true ↔ as = bs := by
  induction as generalizing bs <;> cases bs <;>
    simp [slotsEqual, slotEqual_iff_eq, *]

def boxEqual (a b : Box) : Bool :=
  slotsEqual a.slots b.slots && decide (a.next = b.next) && decide (a.remaining = b.remaining)

theorem boxEqual_iff_eq (a b : Box) : boxEqual a b = true ↔ a = b := by
  cases a; cases b; simp [boxEqual, slotsEqual_iff_eq, Box.mk.injEq, and_assoc]

end OddWeirdSubproblems

namespace OddWeirdSubproblems

def Box.ClosedBelow (b : Box) (B : ℕ) : Prop :=
  ∀ xs ys, b.Matches xs ys → PrimeCoordinates (xs ++ ys) →
    number (xs ++ ys) < B → (number (xs ++ ys)).Weird →
    (∀ d ∈ (number (xs ++ ys)).properDivisors, d.Deficient) → False

theorem closedBelow_of_closed {b : Box} (h : b.Closed) (B : ℕ) : b.ClosedBelow B :=
  fun xs ys hm hv _ hw hp => h xs ys hm hv hw hp

theorem closeBelow_split_slot {b : Box} {B i : ℕ} {s : Slot}
    (hi : b.slots[i]? = some s) (hf : s.fixed = false)
    (h₁ : ({b with slots := b.slots.set i {s with fixed := true}} : Box).ClosedBelow B)
    (h₂ : ({b with slots := b.slots.set i {s with exponent := s.exponent + 1}} : Box).ClosedBelow B) :
    b.ClosedBelow B := by
  intro xs ys ⟨hf₂, ht, hr⟩ hp hlt hw hprim
  rcases forall₂_slot_split hf₂ hi hf with h | h
  · exact h₁ xs ys ⟨h, ht, hr⟩ hp hlt hw hprim
  · exact h₂ xs ys ⟨h, ht, hr⟩ hp hlt hw hprim

theorem closeBelow_split_next {ss : List Slot} {B p r : ℕ} (hodd : Odd p)
    (hskip : (⟨ss, p + 2, r + 1⟩ : Box).ClosedBelow B)
    (htake : p.Prime → (⟨ss ++ [⟨p, 1, false⟩], p + 2, r⟩ : Box).ClosedBelow B) :
    (⟨ss, p, r + 1⟩ : Box).ClosedBelow B := by
  intro xs ys ⟨hx, hy, hlen⟩ hcoord hlt hw hprim
  cases ys with
  | nil => simp at hlen
  | cons y ys =>
    obtain ⟨q, e⟩ := y
    obtain ⟨hpq, hqlo, hq, hqodd, he, ht⟩ := hy
    change p ≤ q at hpq
    by_cases heq : q = p
    · subst q
      have hfit : Slot.Fits ⟨p, 1, false⟩ (p, e) := ⟨hq, rfl, he, by simp⟩
      have eq : xs ++ (p, e) :: ys = (xs ++ [(p, e)]) ++ ys := by simp [List.append_assoc]
      rw [eq] at hcoord hlt hw hprim
      exact htake hq (xs ++ [(p, e)]) ys
        ⟨List.rel_append hx (.cons hfit .nil), ht, by simpa using hlen⟩ hcoord hlt hw hprim
    · have hqmin : p + 2 ≤ q := by
        obtain ⟨a, ha⟩ := hodd
        obtain ⟨b, hb⟩ := hqodd
        omega
      exact hskip xs ((q, e) :: ys) ⟨hx, ⟨hqmin, hqlo, hq, hqodd, he, ht⟩, hlen⟩
        hcoord hlt hw hprim

end OddWeirdSubproblems

namespace OddWeirdSubproblems

open Finset

theorem squarefreeExcess {m q s : ℕ} (hq : q.Prime) (hfresh : ¬ q ∣ m)
    (hs : (∑ d ∈ m.divisors, d) = s) (hdef : s ≤ 2 * m) :
    (∑ d ∈ (m * q).divisors, d) + (2 * m - s) * q = 2 * (m * q) + s := by
  have hc : m.Coprime q := (hq.coprime_iff_not_dvd.mpr hfresh).symm
  have hqsum : (∑ d ∈ q.divisors, d) = 1 + q := by
    rw [hq.divisors]
    simp [hq.ne_one.symm]
  have hadd := congrArg (· * q) (Nat.sub_add_cancel hdef)
  rw [Nat.add_mul, Nat.mul_assoc] at hadd
  rw [hc.sum_divisors_mul, hs, hqsum, Nat.mul_add, Nat.mul_one]
  omega

theorem squarefreePseudoperfectOfSubset {m q s h : ℕ} (hq : q.Prime) (hfresh : ¬ q ∣ m)
    (hs : (∑ d ∈ m.divisors, d) = s) (hdef : s ≤ 2 * m)
    (hh : h = 0 ∨ h ∈ m.properDivisors) {t : Finset ℕ} (ht : t ⊆ m.divisors)
    (htsum : (∑ d ∈ t, d) + (2 * m - s + h) * q = s) :
    (m * q).Pseudoperfect := by
  have hm : 0 < m := Nat.pos_of_ne_zero (fun hm => hfresh (hm ▸ dvd_zero q))
  have hmq : 0 < m * q := Nat.mul_pos hm hq.pos
  have hltmq : m < m * q := by simpa using Nat.mul_lt_mul_of_pos_left hq.one_lt hm
  have heq := squarefreeExcess hq hfresh hs hdef
  rw [Nat.add_mul] at htsum
  have hbase : t ⊆ (m * q).properDivisors := by
    intro d hd
    have hdvd := (Nat.mem_divisors.mp (ht hd)).1
    exact Nat.mem_properDivisors.mpr
      ⟨hdvd.trans (dvd_mul_right m q),
        (Nat.le_of_dvd hm hdvd).trans_lt hltmq⟩
  suffices hex : ∃ u ⊆ (m * q).properDivisors, ∑ d ∈ u, d = (∑ d ∈ t, d) + h * q by
    obtain ⟨u, hu, hus⟩ := hex
    refine ⟨hmq, (m * q).properDivisors \ u, Finset.sdiff_subset, ?_⟩
    have hc := Finset.sum_sdiff (f := fun d : ℕ => d) hu
    rw [Nat.sum_divisors_eq_sum_properDivisors_add_self] at heq
    omega
  rcases hh with rfl | hh
  · exact ⟨t, hbase, by simp⟩
  · obtain ⟨hdiv, hlt⟩ := Nat.mem_properDivisors.mp hh
    have hmem : h * q ∈ (m * q).properDivisors := Nat.mem_properDivisors.mpr
      ⟨Nat.mul_dvd_mul_right hdiv q, Nat.mul_lt_mul_of_pos_right hlt hq.pos⟩
    have hnot : h * q ∉ t := fun htq =>
      hfresh ((dvd_mul_left q h).trans (Nat.mem_divisors.mp (ht htq)).1)
    refine ⟨insert (h * q) t, Finset.insert_subset hmem hbase, ?_⟩
    rw [Finset.sum_insert hnot, Nat.add_comm]

theorem squarefreePseudoperfectOfInterval {m q s h a b : ℕ} (hq : q.Prime)
    (hfresh : ¬ q ∣ m) (hs : (∑ d ∈ m.divisors, d) = s) (hdef : s ≤ 2 * m)
    (hh : h = 0 ∨ h ∈ m.properDivisors)
    (hcover : ∀ x, a ≤ x → x ≤ b → ∃ t ⊆ m.divisors, ∑ d ∈ t, d = x)
    (hlo : a + (2 * m - s + h) * q ≤ s)
    (hhi : s ≤ b + (2 * m - s + h) * q) : (m * q).Pseudoperfect := by
  obtain ⟨t, ht, hsum⟩ := hcover (s - (2 * m - s + h) * q) (by omega) (by omega)
  exact squarefreePseudoperfectOfSubset hq hfresh hs hdef hh ht (by omega)

theorem subsetSumIntervalInsert {D : Finset ℕ} {v a b : ℕ} (hv : v ∉ D)
    (hcover : ∀ x, a ≤ x → x ≤ b → ∃ t ⊆ D, ∑ d ∈ t, d = x)
    (htouch : a + v ≤ b + 1) :
    ∀ x, a ≤ x → x ≤ b + v → ∃ t ⊆ insert v D, ∑ d ∈ t, d = x := by
  intro x ha hb
  by_cases hx : x ≤ b
  · obtain ⟨t, ht, hs⟩ := hcover x ha hx
    exact ⟨t, ht.trans (Finset.subset_insert v D), hs⟩
  · obtain ⟨t, ht, hs⟩ := hcover (x - v) (by omega) (by omega)
    refine ⟨insert v t, Finset.insert_subset_insert _ ht, ?_⟩
    rw [Finset.sum_insert (fun h => hv (ht h)), hs]
    omega

theorem subsetSumIntervalReflect {D : Finset ℕ} {a b : ℕ}
    (hcover : ∀ x, a ≤ x → x ≤ b → ∃ t ⊆ D, ∑ d ∈ t, d = x)
    (hab : a ≤ b) (hb : b ≤ ∑ d ∈ D, d) :
    ∀ x, (∑ d ∈ D, d) - b ≤ x → x ≤ (∑ d ∈ D, d) - a →
      ∃ t ⊆ D, ∑ d ∈ t, d = x := by
  intro x hlow hhigh
  obtain ⟨t, ht, hs⟩ := hcover ((∑ d ∈ D, d) - x) (by omega) (by omega)
  refine ⟨D \ t, Finset.sdiff_subset, ?_⟩
  have htotal := Finset.sum_sdiff (f := fun d : ℕ => d) ht
  omega

theorem squarefreePseudoperfectOfProperInterval {m q s h a b c : ℕ} (hq : q.Prime)
    (hfresh : ¬ q ∣ m) (hs : (∑ d ∈ m.divisors, d) = s) (hdef : s ≤ 2 * m)
    (hh : h = 0 ∨ h ∈ m.properDivisors) (hc : c = 0 ∨ c = m)
    (hcover : ∀ x, a ≤ x → x ≤ b → ∃ t ⊆ m.properDivisors, ∑ d ∈ t, d = x)
    (hlo : a + c + (2 * m - s + h) * q ≤ s)
    (hhi : s ≤ b + c + (2 * m - s + h) * q) : (m * q).Pseudoperfect := by
  refine squarefreePseudoperfectOfInterval hq hfresh hs hdef hh ?_ hlo hhi
  intro x hx hy
  have hm : m ≠ 0 := fun hm => hfresh (hm ▸ dvd_zero q)
  obtain ⟨t, ht, hsum⟩ := hcover (x - c) (by omega) (by omega)
  have hbase : t ⊆ m.divisors := fun d hd =>
    Nat.mem_divisors.mpr ⟨(Nat.mem_properDivisors.mp (ht hd)).1, hm⟩
  rcases hc with hz | he
  · subst c
    exact ⟨t, hbase, by simpa using hsum⟩
  · subst c
    have hnot : m ∉ t := fun h => (lt_irrefl m) (Nat.mem_properDivisors.mp (ht h)).2
    refine ⟨insert m t, Finset.insert_subset (Nat.mem_divisors.mpr ⟨dvd_rfl, hm⟩) hbase, ?_⟩
    rw [Finset.sum_insert hnot, hsum]
    omega

end OddWeirdSubproblems

namespace OddWeirdSubproblems

theorem close_jump_next {ss : List Slot} {p stop r : ℕ}
    (hskip : (⟨ss, stop, r + 1⟩ : Box).Closed)
    (htake : ∀ q, p ≤ q → q < stop → q.Prime → Odd q →
      (⟨ss ++ [⟨q, 1, false⟩], q + 2, r⟩ : Box).Closed) :
    (⟨ss, p, r + 1⟩ : Box).Closed := by
  intro xs ys ⟨hx, hy, hlen⟩ hcoord hw hprim
  cases ys with
  | nil => simp at hlen
  | cons y ys =>
    obtain ⟨q, e⟩ := y
    obtain ⟨hpq, hqlo, hq, hqodd, he, ht⟩ := hy
    by_cases hqcut : q < stop
    · have hfit : Slot.Fits ⟨q, 1, false⟩ (q, e) :=
        ⟨hq, rfl, he, by simp⟩
      have eq : xs ++ (q, e) :: ys = (xs ++ [(q, e)]) ++ ys := by simp [List.append_assoc]
      rw [eq] at hcoord hw hprim
      exact htake q hpq hqcut hq hqodd (xs ++ [(q, e)]) ys
        ⟨List.rel_append hx (.cons hfit .nil), ht, by simpa using hlen⟩ hcoord hw hprim
    · exact hskip xs ((q, e) :: ys)
        ⟨hx, ⟨Nat.le_of_not_gt hqcut, hqlo, hq, hqodd, he, ht⟩, hlen⟩ hcoord hw hprim

theorem close_squarefree_interval
    {ss : List Slot} {q next : ℕ} {m s h a b c : ℕ}
    (hm : number (ss.map Slot.minimum) = m)
    (hs : divisorSum (ss.map Slot.minimum) = s)
    (hdef : s ≤ 2 * m)
    (hh : h = 0 ∨ (h ∣ m ∧ h < m)) (hc : c = 0 ∨ c = m)
    (hcover : ∀ x, a ≤ x → x ≤ b → ∃ t ⊆ m.properDivisors, ∑ d ∈ t, d = x)
    (hlo : a + c + (2 * m - s + h) * q ≤ s)
    (hhi : s ≤ b + c + (2 * m - s + h) * q)
    (hnd : (2 * m - s) * q ≤ s) :
    (⟨ss ++ [⟨q, 1, false⟩], next, 0⟩ : Box).Closed := by
  let box : Box := ⟨ss ++ [⟨q, 1, false⟩], next, 0⟩
  intro xs ys hmatch hvalid hw hprim
  have hminimum : PrimeCoordinates box.minimum :=
    minimum_valid hmatch.1 (primeCoordinates_left hvalid)
  have hcoords : box.minimum = ss.map Slot.minimum ++ [(q, 1)] := by
    simp [box, Box.minimum, Slot.minimum]
  rw [hcoords] at hminimum
  have hq : q.Prime := hminimum.1 (q, 1) (by simp)
  have hqcop : q.Coprime m := by
    rw [← hm]
    apply Nat.coprime_list_prod_right_iff.mpr
    intro w hw
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hw
    have hyq := (List.pairwise_append.mp hminimum.2).2.2 y hy (q, 1) (by simp)
    rw [← pow_one q]
    exact Nat.coprime_pow_primes _ _ hq (hminimum.1 y (List.mem_append_left _ hy)) (Ne.symm hyq.ne)
  have hsum : ∑ d ∈ m.divisors, d = s := by
    rw [← hm, ← divisorSum_eq (primeCoordinates_left hminimum), hs]
  have hnot : ¬ q ∣ m := hq.coprime_iff_not_dvd.mp hqcop
  have hpp : (m * q).Pseudoperfect := squarefreePseudoperfectOfProperInterval hq hnot
    hsum hdef (hh.imp_right Nat.mem_properDivisors.mpr) hc hcover hlo hhi
  have hn : number box.minimum = m * q := by
    rw [hcoords, number_append, hm]
    simp [number]
  have hd : 2 * number box.minimum ≤ divisorSum box.minimum := by
    rw [divisorSum_eq (hcoords.symm ▸ hminimum), hn]
    have he := squarefreeExcess hq hnot hsum hdef
    omega
  exact close_at_nondeficient_minimum hd (Or.inr (Or.inl (hn.symm ▸ hpp)))
    xs ys hmatch hvalid hw hprim

theorem close_nondeficient_squarefree_prefix {ss : List Slot} {q next r : ℕ}
    (hr : 0 < r)
    (hnondef : 2 * number (ss.map Slot.minimum) * q ≤
      divisorSum (ss.map Slot.minimum) * (1 + q)) :
    (⟨ss ++ [⟨q, 1, false⟩], next, r⟩ : Box).Closed := by
  apply close_minimum_with_tail (b := ⟨ss ++ [({ prime := q, exponent := 1, fixed := false } : Slot)], next, r⟩) hr
  change 2 * number ((ss ++ [({ prime := q, exponent := 1, fixed := false } : Slot)]).map Slot.minimum) ≤
    divisorSum ((ss ++ [({ prime := q, exponent := 1, fixed := false } : Slot)]).map Slot.minimum)
  rw [List.map_append, number_append, divisorSum_append, ← Nat.mul_assoc]
  simpa [Slot.minimum, number, divisorSum, powerSum] using hnondef

def HeadRangeClosed (ss : List Slot) (r lo hi : ℕ) : Prop :=
  ∀ q, lo ≤ q → q < hi → q.Prime → Odd q →
    (⟨ss ++ [⟨q, 1, false⟩], q + 2, r⟩ : Box).Closed

theorem headRange_join {ss : List Slot} {r lo mid hi : ℕ}
    (h₁ : HeadRangeClosed ss r lo mid) (h₂ : HeadRangeClosed ss r mid hi) :
    HeadRangeClosed ss r lo hi := by
  intro q hqlo hqhi hp ho
  by_cases h : q < mid
  · exact h₁ q hqlo h hp ho
  · exact h₂ q (Nat.le_of_not_gt h) hqhi hp ho

theorem headRange_single {ss : List Slot} {r q : ℕ}
    (h : q.Prime → Odd q → (⟨ss ++ [⟨q, 1, false⟩], q + 2, r⟩ : Box).Closed) :
    HeadRangeClosed ss r q (q + 1) := by
  intro p hlo hhi hp ho
  have e : p = q := by omega
  subst p
  exact h hp ho

theorem headRange_squarefree {ss : List Slot} {m s h a b c lo hi : ℕ}
    (hm : number (ss.map Slot.minimum) = m)
    (hs : divisorSum (ss.map Slot.minimum) = s)
    (hdef : s ≤ 2 * m)
    (hh : h = 0 ∨ (h ∣ m ∧ h < m)) (hc : c = 0 ∨ c = m)
    (hcover : ∀ x, a ≤ x → x ≤ b → ∃ t ⊆ m.properDivisors, ∑ d ∈ t, d = x)
    (hlow : s ≤ b + c + (2 * m - s + h) * lo)
    (hhigh : a + c + (2 * m - s + h) * (hi - 1) ≤ s) :
    HeadRangeClosed ss 0 lo hi := by
  intro q hqlo hqhi _ _
  have hu : q ≤ hi - 1 := by omega
  have ha := Nat.mul_le_mul_left (2 * m - s + h) hu
  have hb := Nat.mul_le_mul_left (2 * m - s + h) hqlo
  have hc' := Nat.mul_le_mul_right q (show 2 * m - s ≤ 2 * m - s + h by omega)
  exact close_squarefree_interval hm hs hdef hh hc hcover (by omega) (by omega) (by omega)

theorem decrement_append_left {xs ys : Coordinates} {i : ℕ} (hi : i < xs.length) :
    decrement (xs ++ ys) i = decrement xs i ++ ys := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
    rcases x with ⟨p, e⟩
    cases i with
    | zero => rfl
    | succ i =>
      have hi' : i < xs.length := by simpa using hi
      simp [decrement, ih hi']

theorem product_after_head (ss : List Slot) (q : ℕ) :
    number ((ss ++ [({ prime := q, exponent := 1, fixed := false } : Slot)]).map Slot.minimum)
    = number (ss.map Slot.minimum) * q := by
  rw [List.map_append, number_append]
  simp [number, Slot.minimum]

theorem headRange_decrement_nondeficient {ss : List Slot} {r lo hi i z t : ℕ}
    (hi' : i < ss.length)
    (hz : number (decrement (ss.map Slot.minimum) i) = z)
    (ht : divisorSum (decrement (ss.map Slot.minimum) i) = t)
    (hzlt : z < number (ss.map Slot.minimum))
    (hcut : (2 * z - t) * (hi - 1) ≤ t) :
    HeadRangeClosed ss r lo hi := by
  intro q _ hqhi hq _
  let b : Box := ⟨ss ++ [⟨q, 1, false⟩], q + 2, r⟩
  intro xs ys hfit hcoord hw hprim
  have hv : PrimeCoordinates b.minimum :=
    minimum_valid hfit.1 (primeCoordinates_left hcoord)
  have hminimum : b.minimum = ss.map Slot.minimum ++ [(q, 1)] := by
    simp [b, Box.minimum, Slot.minimum]
  have hcut' : 2 * (z * q) ≤ t * (1 + q) := by
    have hq' : q ≤ hi - 1 := by omega
    have h₁ := (Nat.mul_le_mul_left (2 * z - t) hq').trans hcut
    have h₂ := Nat.mul_le_mul_right q (show 2 * z ≤ 2 * z - t + t by omega)
    rw [Nat.add_mul] at h₂
    rw [← Nat.mul_assoc, Nat.mul_add]
    simp only [Nat.mul_one]
    omega
  have hdcoords : decrement b.minimum i = decrement (ss.map Slot.minimum) i ++ [(q, 1)] := by
    rw [hminimum, decrement_append_left (by simpa using hi')]
  have hdn : number (decrement b.minimum i) = z * q := by
    rw [hdcoords, number_append, hz]
    simp [number]
  have hds : divisorSum (decrement b.minimum i) = t * (1 + q) := by
    rw [hdcoords, divisorSum_append, ht]
    simp [divisorSum, powerSum]
  have hdnd : ¬ (number (decrement b.minimum i)).Deficient := by
    rw [deficient_iff_divisorSum_lt (decrement_coordinates hv i), hdn, hds]
    exact hcut'.not_gt
  have hdnlt : number (decrement b.minimum i) < number b.minimum := by
    rw [hdn, show number b.minimum = _ from product_after_head ss q]
    exact Nat.mul_lt_mul_of_pos_right hzlt hq.pos
  have hminDvd : number b.minimum ∣ number (xs ++ ys) := by
    rw [number_append]
    exact dvd_mul_of_dvd_left (minimum_dvd hfit.1) _
  have hdvd := (decrement_dvd b.minimum i).trans hminDvd
  have hlt := hdnlt.trans_le (Nat.le_of_dvd hw.1.pos hminDvd)
  exact hdnd (hprim _ (Nat.mem_properDivisors.mpr ⟨hdvd, hlt⟩))

end OddWeirdSubproblems

namespace OddWeirdSubproblems

theorem closeBelow_jump_next {ss : List Slot} {B p stop r : ℕ}
    (hskip : (⟨ss, stop, r + 1⟩ : Box).ClosedBelow B)
    (htake : ∀ q, p ≤ q → q < stop → q.Prime → Odd q →
      (⟨ss ++ [⟨q, 1, false⟩], q + 2, r⟩ : Box).ClosedBelow B) :
    (⟨ss, p, r + 1⟩ : Box).ClosedBelow B := by
  intro xs ys ⟨hx, hy, hlen⟩ hcoord hsize hw hprim
  cases ys with
  | nil => simp at hlen
  | cons y ys =>
    obtain ⟨q, e⟩ := y
    obtain ⟨hpq, hqlo, hq, hqodd, he, ht⟩ := hy
    by_cases hqcut : q < stop
    · have hfit : Slot.Fits ⟨q, 1, false⟩ (q, e) := ⟨hq, rfl, he, by simp⟩
      have hsplit : xs ++ (q, e) :: ys = (xs ++ [(q, e)]) ++ ys := by simp [List.append_assoc]
      rw [hsplit] at hcoord hsize hw hprim
      exact htake q hpq hqcut hq hqodd (xs ++ [(q, e)]) ys
        ⟨List.rel_append hx (.cons hfit .nil), ht, by simpa using hlen⟩ hcoord hsize hw hprim
    · exact hskip xs ((q, e) :: ys)
        ⟨hx, ⟨Nat.le_of_not_gt hqcut, hqlo, hq, hqodd, he, ht⟩, hlen⟩ hcoord hsize hw hprim

end OddWeirdSubproblems

namespace OddWeirdSubproblems

def RankFloor : List ℕ → Coordinates → Prop
  | [], _ => True
  | _ :: _, [] => True
  | p :: ps, x :: xs => p ≤ x.1 ∧ RankFloor ps xs

theorem tailFits_weaken {p q : ℕ} {xs : Coordinates} (hp : p ≤ q) (h : TailFits q xs) :
    TailFits p xs := by
  cases xs with
  | nil => trivial
  | cons x xs =>
    obtain ⟨r, e⟩ := x
    obtain ⟨hlo, hpos, hprime, hodd, he, ht⟩ := h
    exact ⟨hp.trans hlo, hpos, hprime, hodd, he, ht⟩

theorem number_ge_floor_product {ps : List ℕ} {xs : Coordinates}
    (hr : RankFloor ps xs) (hlen : ps.length ≤ xs.length)
    (hp : ∀ x ∈ xs, x.1.Prime ∧ 0 < x.2) : ps.prod ≤ number xs := by
  induction ps generalizing xs with
  | nil => exact number_pos (fun x hx => (hp x hx).1)
  | cons p ps ih =>
    cases xs with
    | nil => simp at hlen
    | cons x xs =>
      obtain ⟨q, e⟩ := x
      obtain ⟨hle, ht⟩ := hr
      obtain ⟨hq, he⟩ := hp (q, e) (by simp)
      have hpq : p ≤ q ^ e := hle.trans (by
        simpa using Nat.pow_le_pow_right hq.pos (show 1 ≤ e by omega))
      exact Nat.mul_le_mul hpq
        (ih ht (by simpa using hlen) (fun y hy => hp y (List.mem_cons_of_mem _ hy)))

theorem one_le_limitingIndex {p : ℕ} (hp : 1 < p) : 1 ≤ limitingIndex p := by
  have hp' : (1 : ℚ) < p := by exact_mod_cast hp
  unfold limitingIndex
  rw [le_div_iff₀ (sub_pos.mpr hp')]
  linarith

theorem floorIndex_ge_one {ps : List ℕ} (hp : ∀ p ∈ ps, 1 < p) :
    1 ≤ (ps.map limitingIndex).prod := by
  induction ps with
  | nil => simp
  | cons p ps ih =>
    simp only [List.map_cons, List.prod_cons]
    exact one_le_mul_of_one_le_of_one_le (one_le_limitingIndex (hp p (by simp)))
      (ih (fun q hq => hp q (by simp [hq])))

theorem floorIndex_upper {ps : List ℕ} {xs : Coordinates}
    (hr : RankFloor ps xs) (hlen : xs.length ≤ ps.length)
    (hp : ∀ p ∈ ps, 1 < p) :
    (xs.map fun x => index x.1 x.2).prod ≤ (ps.map limitingIndex).prod := by
  induction ps generalizing xs with
  | nil =>
    have hn : xs = [] := by simpa using hlen
    simp [hn]
  | cons p ps ih =>
    cases xs with
    | nil => exact floorIndex_ge_one hp
    | cons x xs =>
      obtain ⟨q, e⟩ := x
      obtain ⟨hpq, ht⟩ := hr
      have hp' := hp p (by simp)
      have hq : 1 < q := hp'.trans_le hpq
      exact mul_le_mul ((index_le_limitingIndex hq).trans (limitingIndex_antitone hp' hpq))
        (ih ht (by simpa using hlen) (fun r hr => hp r (by simp [hr])))
        (coordinate_prod_nonneg _) (limitingIndex_nonneg hp')

end OddWeirdSubproblems

namespace OddWeirdSubproblems

def hasOddFactor (n : ℕ) : ℕ → ℕ → Bool
  | 0, _ => false
  | fuel + 1, d =>
    if n < d * d then false
    else if n % d = 0 then true
    else hasOddFactor n fuel (d + 2)

theorem hasOddFactor_false_of_prime {n : ℕ} (hp : n.Prime) (fuel d : ℕ)
    (hd : 2 ≤ d) : hasOddFactor n fuel d = false := by
  induction fuel generalizing d with
  | zero => rfl
  | succ fuel ih =>
    rw [hasOddFactor]
    split
    · rfl
    · next h =>
      have hlt : d < n := by
        have h₂ := Nat.mul_le_mul_right d hd
        omega
      have hmod : n % d ≠ 0 := by
        intro hmod
        rcases (Nat.dvd_prime hp).mp (Nat.dvd_of_mod_eq_zero hmod) with h₁ | hn
        · omega
        · omega
      exact (if_neg hmod).trans (ih (d + 2) (by omega))

def mayBeOddPrime (n : ℕ) : Bool := !hasOddFactor n n 3

theorem mayBeOddPrime_of_prime {n : ℕ} (hp : n.Prime) : mayBeOddPrime n = true := by
  simp [mayBeOddPrime, hasOddFactor_false_of_prime hp]

end OddWeirdSubproblems

namespace OddWeirdSubproblems

def firstAllowedOdd (p : ℕ) : ℕ → ℕ
  | 0 => p
  | fuel + 1 => if mayBeOddPrime p then p else firstAllowedOdd (p + 2) fuel

theorem firstAllowedOdd_ge (p fuel : ℕ) : p ≤ firstAllowedOdd p fuel := by
  induction fuel generalizing p with
  | zero => rfl
  | succ fuel ih =>
    rw [firstAllowedOdd]
    split
    · rfl
    · exact (Nat.le_add_right _ _).trans (ih _)

theorem firstAllowedOdd_odd {p : ℕ} (hp : Odd p) (fuel : ℕ) : Odd (firstAllowedOdd p fuel) := by
  induction fuel generalizing p with
  | zero => exact hp
  | succ fuel ih =>
    rw [firstAllowedOdd]
    split
    · exact hp
    · exact ih (by obtain ⟨k, hk⟩ := hp; exact ⟨k + 1, by omega⟩)

theorem firstAllowedOdd_le_prime {p q : ℕ} (hp : Odd p) (hq : Odd q)
    (hprime : q.Prime) (hle : p ≤ q) (fuel : ℕ) : firstAllowedOdd p fuel ≤ q := by
  induction fuel generalizing p with
  | zero => exact hle
  | succ fuel ih =>
    rw [firstAllowedOdd]
    split
    · exact hle
    · next h =>
      have hneq : p ≠ q := by
        intro he
        subst q
        exact h (mayBeOddPrime_of_prime hprime)
      obtain ⟨a, ha⟩ := hp
      obtain ⟨b, hb⟩ := hq
      exact ih ⟨a + 1, by omega⟩ (by omega)

def tailPrimeFloor (p : ℕ) : ℕ → List ℕ
  | 0 => []
  | r + 1 =>
    let q := firstAllowedOdd p 32
    q :: tailPrimeFloor (q + 2) r

theorem tailPrimeFloor_length (p r : ℕ) : (tailPrimeFloor p r).length = r := by
  induction r generalizing p with
  | zero => rfl
  | succ r ih => simp only [tailPrimeFloor, List.length_cons, ih]

theorem tailPrimeFloor_gt_one {p : ℕ} (hp : 1 < p) (r : ℕ) :
    ∀ q ∈ tailPrimeFloor p r, 1 < q := by
  induction r generalizing p with
  | zero => simp [tailPrimeFloor]
  | succ r ih =>
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact hp.trans_le (firstAllowedOdd_ge _ _)
    · apply ih (hp.trans_le ((firstAllowedOdd_ge _ _).trans (Nat.le_add_right _ _))) _ hq

theorem tailPrimeFloor_correct {p : ℕ} (hp : Odd p) {xs : Coordinates} (ht : TailFits p xs)
    (r : ℕ) : RankFloor (tailPrimeFloor p r) xs := by
  induction r generalizing p xs with
  | zero => trivial
  | succ r ih =>
    cases xs with
    | nil => trivial
    | cons x xs =>
      obtain ⟨q, e⟩ := x
      obtain ⟨hlo, _, hprime, hodd, _, ht'⟩ := ht
      have hfirst := firstAllowedOdd_le_prime hp hodd hprime hlo 32
      have hodd' : Odd (firstAllowedOdd p 32 + 2) := by
        obtain ⟨k, hk⟩ := firstAllowedOdd_odd hp 32
        exact ⟨k + 1, by omega⟩
      exact ⟨hfirst, ih hodd' (tailFits_weaken (by omega) ht')⟩

private theorem tailFits_prime_pos {p : ℕ} {xs : Coordinates} (ht : TailFits p xs) :
    ∀ x ∈ xs, x.1.Prime ∧ 0 < x.2 := by
  induction xs generalizing p with
  | nil => simp
  | cons x xs ih =>
    obtain ⟨q, e⟩ := x
    obtain ⟨_, _, hq, _, he, htail⟩ := ht
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact ⟨hq, he⟩
    · exact ih htail y hy

theorem tailPrimeFloor_product_le {p : ℕ} (hp : Odd p) {xs : Coordinates} (ht : TailFits p xs)
    {r : ℕ} (hr : r ≤ xs.length) : (tailPrimeFloor p r).prod ≤ number xs := by
  exact number_ge_floor_product (tailPrimeFloor_correct hp ht _)
    (by simpa only [tailPrimeFloor_length] using hr) (tailFits_prime_pos ht)

theorem closeBelow_of_ranked_minimum_ge {b : Box} {B : ℕ} (hodd : Odd b.next)
    (hB : B ≤ number b.minimum * (tailPrimeFloor b.next b.remaining).prod) : b.ClosedBelow B := by
  intro xs ys ⟨hf, ht, hy⟩ hcoord hlt _ _
  have hx := Nat.le_of_dvd (number_pos (primeCoordinates_left hcoord).1) (minimum_dvd hf)
  have hy' := tailPrimeFloor_product_le hodd ht hy.ge
  rw [number_append] at hlt
  exact hlt.not_ge (hB.trans (Nat.mul_le_mul hx hy'))

def rankedUpperNum (b : Box) : ℕ :=
  (b.slots.map Slot.upperNum).prod * (tailPrimeFloor b.next b.remaining).prod

def rankedUpperDen (b : Box) : ℕ :=
  (b.slots.map Slot.upperDen).prod * ((tailPrimeFloor b.next b.remaining).map (· - 1)).prod

private theorem ranked_indices_eq {ps : List ℕ} (h : ∀ p ∈ ps, 1 < p) :
    (ps.map limitingIndex).prod = (ps.prod : ℚ) / (((ps.map (· - 1)).prod : ℕ) : ℚ) := by
  induction ps with
  | nil => simp
  | cons p ps ih =>
    have hp : 1 ≤ p := (h p (by simp)).le.trans (by omega)
    simp only [List.map_cons, List.prod_cons, Nat.cast_mul]
    rw [ih (fun q hq => h q (by simp [hq])), ← div_mul_div_comm, limitingIndex, Nat.cast_sub hp]
    simp

private theorem ranked_floor_den_pos {ps : List ℕ} (h : ∀ p ∈ ps, 1 < p) :
    0 < (ps.map (· - 1)).prod := by
  induction ps with
  | nil => decide
  | cons p ps ih =>
    have hp := h p (by simp)
    exact Nat.mul_pos (by omega : 0 < p - 1) (ih (fun q hq => h q (by simp [hq])))

theorem close_of_ranked_upper {b : Box} (hnext : 1 < b.next) (hodd : Odd b.next)
    (hbound : rankedUpperNum b ≤ 2 * rankedUpperDen b) : b.Closed := by
  intro xs ys ⟨hslots, htail, hlen⟩ hvalid hw _
  let ps := tailPrimeFloor b.next b.remaining
  have hp : ∀ q ∈ ps, 1 < q := tailPrimeFloor_gt_one hnext _
  have hslot (s : Slot) (hs : s ∈ b.slots) : 1 < s.prime := by
    obtain ⟨x, _, hx⟩ := exists_fit_of_mem hslots hs
    rw [hx.2.1]
    exact hx.1.one_lt
  have hden : 0 < rankedUpperDen b := Nat.mul_pos (slot_den_pos hslot) (ranked_floor_den_pos hp)
  have hupper : (b.slots.map Slot.upper).prod * (ps.map limitingIndex).prod ≤ 2 := by
    rw [slot_upper_eq hslot, ranked_indices_eq hp, div_mul_div_comm, ← Nat.cast_mul, ← Nat.cast_mul]
    change (rankedUpperNum b : ℚ) / (rankedUpperDen b : ℚ) ≤ 2
    rw [div_le_iff₀ (by exact_mod_cast hden)]
    exact_mod_cast hbound
  have hrat := floorIndex_upper (tailPrimeFloor_correct hodd htail b.remaining)
    (by simpa only [tailPrimeFloor_length] using hlen.le) hp
  have hle : ((xs ++ ys).map (fun x => index x.1 x.2)).prod ≤ 2 := by
    rw [List.map_append, List.prod_append]
    exact (mul_le_mul (slot_prod_upper hslots) hrat (coordinate_prod_nonneg _)
      ((coordinate_prod_nonneg _).trans (slot_prod_upper hslots))).trans hupper
  rw [coordinate_index_eq, divisorSum_eq hvalid, ← Nat.abundancyIndex] at hle
  exact (Nat.abundant_iff_two_lt_abundancyIndex.mp hw.1).not_ge hle

end OddWeirdSubproblems

namespace OddWeirdSubproblems

theorem closeBelow_fix_slot_of_size {b : Box} {B i : ℕ} {s : Slot}
    (hi : b.slots[i]? = some s) (hf : s.fixed = false) (hodd : Odd b.next)
    (hB : B ≤ number ({b with slots := b.slots.set i {s with exponent := s.exponent + 1}} : Box).minimum *
      (tailPrimeFloor b.next b.remaining).prod)
    (hfixed : ({b with slots := b.slots.set i {s with fixed := true}} : Box).ClosedBelow B) :
    b.ClosedBelow B :=
  closeBelow_split_slot hi hf hfixed (closeBelow_of_ranked_minimum_ge hodd hB)

def sizeFixedSlot (B : ℕ) (b : Box) : Option (ℕ × Slot) :=
  let floor := (tailPrimeFloor b.next b.remaining).prod
  ((List.range b.slots.length).filterMap fun i => b.slots[i]?.map fun s => (i, s)).find?
    fun (i, s) => !s.fixed &&
      decide (B ≤ number ({b with slots := b.slots.set i {s with exponent := s.exponent + 1}} : Box).minimum * floor)

theorem sizeFixedSlot_closes {B i : ℕ} {b : Box} {s : Slot}
    (h : sizeFixedSlot B b = some (i, s)) (hodd : Odd b.next)
    (hfixed : ({b with slots := b.slots.set i {s with fixed := true}} : Box).ClosedBelow B) :
    b.ClosedBelow B := by
  unfold sizeFixedSlot at h
  have hmem := List.find?_some h
  have hprune := List.mem_of_find?_eq_some h
  obtain ⟨j, _, hslot⟩ := List.mem_filterMap.mp hprune
  obtain ⟨u, hu, he⟩ := Option.map_eq_some_iff.mp hslot
  cases he
  simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hmem
  exact closeBelow_fix_slot_of_size hu hmem.1 hodd hmem.2 hfixed

end OddWeirdSubproblems

namespace OddWeirdSubproblems

open Finset

def exponentBudget (B : ℕ) (b : Box) : ℕ :=
  (B - 1) / (number b.minimum * (tailPrimeFloor b.next b.remaining).prod)

private def floorSlot (p : ℕ) : Slot := ⟨p, 1, false⟩

private def exponentCapSlot (R : ℕ) (s : Slot) : ℕ × ℕ :=
  (s.prime, if s.fixed then s.exponent else s.exponent + Nat.log s.prime R)

def exponentCapCoordinates (B : ℕ) (b : Box) : Coordinates :=
  ((b.slots ++ (tailPrimeFloor b.next b.remaining).map floorSlot).map
    (exponentCapSlot (exponentBudget B b)))

def exponentCapOk (B : ℕ) (b : Box) : Bool :=
  let cs := exponentCapCoordinates B b
  decide (divisorSum cs ≤ 2 * number cs)

private theorem index_succ_of_pos {p e : ℕ} (hp : 0 < p) :
    index p (e + 1) = index p e + 1 / (p : ℚ) ^ (e + 1) := by
  have hsum : powerSum p (e + 1) = p * powerSum p e + 1 := by
    simp only [powerSum_eq_sum]
    exact geom_sum_succ
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne'
  unfold index
  rw [hsum, Nat.cast_add, Nat.cast_mul, Nat.cast_one, add_div, pow_succ',
    mul_div_mul_left _ _ hp0]

private theorem index_mono_exponent {p : ℕ} (hp : 0 < p) : Monotone (index p) := by
  apply monotone_nat_of_le_succ
  intro e
  rw [index_succ_of_pos hp]
  exact le_add_of_nonneg_right (by positivity)

private theorem index_antitone_base {p q : ℕ} (hp : 0 < p) (hpq : p ≤ q) (e : ℕ) :
    index q e ≤ index p e := by
  induction e with
  | zero => simp [index, powerSum]
  | succ e ih =>
    rw [index_succ_of_pos hp, index_succ_of_pos (hp.trans_le hpq)]
    have hpR : (0 : ℚ) < p := by exact_mod_cast hp
    have hpqR : (p : ℚ) ≤ q := by exact_mod_cast hpq
    exact add_le_add ih (one_div_le_one_div_of_le (pow_pos hpR _)
      (pow_le_pow_left₀ hpR.le hpqR _))

private def NumericalFit (s : Slot) (x : ℕ × ℕ) : Prop :=
  1 < s.prime ∧ s.prime ≤ x.1 ∧ s.exponent ≤ x.2 ∧ (s.fixed = true → s.exponent = x.2)

private theorem numericalFit_of_slotFits {ss : List Slot} {xs : Coordinates}
    (h : List.Forall₂ Slot.Fits ss xs) : List.Forall₂ NumericalFit ss xs := by
  apply h.imp
  intro s x hx
  obtain ⟨hp, hq, he, hfix⟩ := hx
  exact ⟨hq ▸ hp.one_lt, hq.le, he, hfix⟩

private theorem numericalFit_of_rankFloor {ps : List ℕ} {xs : Coordinates} {p : ℕ}
    (hr : RankFloor ps xs) (hl : ps.length = xs.length)
    (hps : ∀ q ∈ ps, 1 < q) (ht : TailFits p xs) :
    List.Forall₂ NumericalFit (ps.map floorSlot) xs := by
  induction ps generalizing xs p with
  | nil =>
    have hx : xs = [] := List.length_eq_zero_iff.mp hl.symm
    subst xs
    exact .nil
  | cons q ps ih =>
    cases xs with
    | nil => simp at hl
    | cons x xs =>
      obtain ⟨t, e⟩ := x
      obtain ⟨hle, htail⟩ := hr
      obtain ⟨_, _, _, _, he, ht'⟩ := ht
      exact .cons ⟨hps q (by simp), hle, he, by simp [floorSlot]⟩
        (ih htail (by simpa using hl) (fun q' hq' => hps q' (List.mem_cons_of_mem _ hq')) ht')

private theorem numericalFit_pow_le {s : Slot} {x : ℕ × ℕ} (h : NumericalFit s x) :
    s.prime ^ s.exponent ≤ x.1 ^ x.2 :=
  (Nat.pow_le_pow_right (Nat.zero_lt_one.trans h.1) h.2.2.1).trans
    (Nat.pow_le_pow_left h.2.1 _)

private theorem numericalFit_minimum_pos_le {ss : List Slot} {xs : Coordinates}
    (h : List.Forall₂ NumericalFit ss xs) :
    0 < number (ss.map Slot.minimum) ∧ number (ss.map Slot.minimum) ≤ number xs := by
  induction h with
  | nil => exact ⟨Nat.one_pos, le_rfl⟩
  | @cons s x ss xs hx _ ih =>
    simp only [List.map_cons, number_cons, Slot.minimum]
    exact ⟨Nat.mul_pos (pow_pos (Nat.zero_lt_one.trans hx.1) _) ih.1,
      Nat.mul_le_mul (numericalFit_pow_le hx) ih.2⟩

private theorem numericalFit_cap {ss : List Slot} {xs : Coordinates} {R : ℕ}
    (h : List.Forall₂ NumericalFit ss xs)
    (hsize : number xs < number (ss.map Slot.minimum) * (R + 1)) :
    List.Forall₂ (fun s x => NumericalFit s x ∧ x.2 ≤ (exponentCapSlot R s).2) ss xs := by
  induction h with
  | nil => exact .nil
  | @cons s x ss xs hx ht ih =>
    simp only [List.map_cons, number_cons, Slot.minimum] at hsize
    have htail := numericalFit_minimum_pos_le ht
    have hp : 0 < s.prime := Nat.zero_lt_one.trans hx.1
    have hsizeTail : number xs < number (ss.map Slot.minimum) * (R + 1) := by
      apply Nat.lt_of_mul_lt_mul_left (a := s.prime ^ s.exponent)
      rw [← Nat.mul_assoc]
      exact (Nat.mul_le_mul_right _ (numericalFit_pow_le hx)).trans_lt hsize
    have hpower : s.prime ^ (x.2 - s.exponent) ≤ R := by
      by_contra! hh
      have hmul : (s.prime ^ s.exponent * number (ss.map Slot.minimum)) *
          s.prime ^ (x.2 - s.exponent) ≤ x.1 ^ x.2 * number xs := by
        calc
          _ = s.prime ^ x.2 * number (ss.map Slot.minimum) := by
            rw [mul_right_comm, ← pow_add, Nat.add_sub_of_le hx.2.2.1]
          _ ≤ _ := Nat.mul_le_mul (Nat.pow_le_pow_left hx.2.1 _) htail.2
      exact hsize.not_ge ((Nat.mul_le_mul_left _ (Nat.succ_le_of_lt hh)).trans hmul)
    have he : x.2 ≤ (exponentCapSlot R s).2 := by
      cases hf : s.fixed
      · have hh := Nat.le_log_of_pow_le hx.1 hpower
        simp only [exponentCapSlot, hf, Bool.false_eq_true, if_false]
        have hle := hx.2.2.1
        omega
      · simp [exponentCapSlot, hf, hx.2.2.2 hf]
    exact .cons ⟨hx, he⟩ (ih hsizeTail)

private theorem indices_le_exponentCap {ss : List Slot} {xs : Coordinates} {R : ℕ}
    (h : List.Forall₂ (fun s x => NumericalFit s x ∧ x.2 ≤ (exponentCapSlot R s).2) ss xs) :
    (xs.map (fun x => index x.1 x.2)).prod ≤
      ((ss.map (exponentCapSlot R)).map (fun x => index x.1 x.2)).prod := by
  induction h with
  | nil => simp
  | @cons s x ss xs hx _ ih =>
    have hp : 0 < s.prime := Nat.zero_lt_one.trans hx.1.1
    have hhead : index x.1 x.2 ≤ index (exponentCapSlot R s).1 (exponentCapSlot R s).2 :=
      (index_antitone_base hp hx.1.2.1 _).trans (index_mono_exponent hp hx.2)
    simp only [List.map_cons, List.prod_cons]
    exact mul_le_mul hhead ih (coordinate_prod_nonneg xs) (index_nonneg _ _)

private theorem match_capped_numericalFit {b : Box} {B : ℕ} {xs ys : Coordinates}
    (hnext : 1 < b.next) (hodd : Odd b.next) (hmatch : b.Matches xs ys)
    (hsize : number (xs ++ ys) < B) :
    List.Forall₂ (fun s x => NumericalFit s x ∧ x.2 ≤ (exponentCapSlot (exponentBudget B b) s).2)
      (b.slots ++ (tailPrimeFloor b.next b.remaining).map floorSlot) (xs ++ ys) := by
  obtain ⟨hslots, ht, hl⟩ := hmatch
  let ps := tailPrimeFloor b.next b.remaining
  let ss := b.slots ++ ps.map floorSlot
  let A := number b.minimum * ps.prod
  let R := exponentBudget B b
  have hfit : List.Forall₂ NumericalFit ss (xs ++ ys) :=
    List.rel_append (numericalFit_of_slotFits hslots)
      (numericalFit_of_rankFloor (tailPrimeFloor_correct hodd ht b.remaining)
        ((tailPrimeFloor_length b.next b.remaining).trans hl.symm)
        (tailPrimeFloor_gt_one hnext _) ht)
  have hAeq : number (ss.map Slot.minimum) = A := by
    simp only [ss, A, Box.minimum, List.map_append, number_append]
    congr 1
    induction ps with
    | nil => rfl
    | cons p ps ih => simp only [List.map_cons, number_cons, List.prod_cons, Slot.minimum, floorSlot,
        pow_one, ih]
  have hA : 0 < A := hAeq ▸ (numericalFit_minimum_pos_le hfit).1
  have hnextSize : B - 1 < A * (R + 1) := by
    rw [Nat.mul_comm, ← Nat.div_lt_iff_lt_mul hA]
    exact Nat.lt_succ_self _
  have hR : number (xs ++ ys) < number (ss.map Slot.minimum) * (R + 1) := by
    rw [hAeq]
    omega
  exact numericalFit_cap hfit hR

theorem abundancyIndex_le_exponentCap_of_matches_below {b : Box} {B : ℕ} {xs ys : Coordinates}
    (hnext : 1 < b.next) (hodd : Odd b.next) (hmatch : b.Matches xs ys)
    (hcoords : PrimeCoordinates (xs ++ ys)) (hsize : number (xs ++ ys) < B) :
    (number (xs ++ ys)).abundancyIndex ≤
      (divisorSum (exponentCapCoordinates B b) : ℚ) / (number (exponentCapCoordinates B b) : ℚ) := by
  have h := indices_le_exponentCap (match_capped_numericalFit hnext hodd hmatch hsize)
  change _ ≤ ((exponentCapCoordinates B b).map (fun x => index x.1 x.2)).prod at h
  rw [coordinate_index_eq, coordinate_index_eq, divisorSum_eq hcoords, ← Nat.abundancyIndex] at h
  exact h

theorem closeBelow_of_exponentCap {b : Box} {B : ℕ} (hnext : 1 < b.next) (hodd : Odd b.next)
    (hcap : divisorSum (exponentCapCoordinates B b) ≤ 2 * number (exponentCapCoordinates B b)) :
    b.ClosedBelow B := by
  intro xs ys hmatch hcoords hsize hw _
  have h := abundancyIndex_le_exponentCap_of_matches_below hnext hodd hmatch hcoords hsize
  let z := (number (exponentCapCoordinates B b) : ℚ)
  have hz : 0 ≤ z := by positivity
  have hh : (divisorSum (exponentCapCoordinates B b) : ℚ) ≤ 2 * z := by
    dsimp only [z]
    exact_mod_cast hcap
  have hle : (divisorSum (exponentCapCoordinates B b) : ℚ) / z ≤ 2 := by
    refine (div_le_div_of_nonneg_right hh hz).trans ?_
    by_cases h0 : z = 0
    · simp [h0]
    · simp [h0]
  exact (Nat.abundant_iff_two_lt_abundancyIndex.mp hw.1).not_ge (h.trans hle)

theorem exponentCapOk_closes {b : Box} {B : ℕ} (hnext : 1 < b.next) (hodd : Odd b.next)
    (h : exponentCapOk B b = true) : b.ClosedBelow B :=
  closeBelow_of_exponentCap hnext hodd (of_decide_eq_true h)

private def freezeSlot (R : ℕ) (s : Slot) : Slot :=
  {s with fixed := s.fixed || decide (R < s.prime)}

def freezeSizeSlots (B : ℕ) (b : Box) : Box :=
  {b with slots := b.slots.map (freezeSlot (exponentBudget B b))}

private theorem slots_fit_frozen {ss : List Slot} {xs : Coordinates} {R : ℕ}
    (hf : List.Forall₂ Slot.Fits ss xs)
    (hcap : List.Forall₂ (fun s x => NumericalFit s x ∧ x.2 ≤ (exponentCapSlot R s).2) ss xs) :
    List.Forall₂ Slot.Fits (ss.map (freezeSlot R)) xs := by
  induction hf with
  | nil => exact .nil
  | @cons s x ss xs hs _ ih =>
    cases hcap with
    | cons hc hcs =>
      refine .cons ⟨hs.1, hs.2.1, hs.2.2.1, ?_⟩ (ih hcs)
      intro hfix
      change (s.fixed || decide (R < s.prime)) = true at hfix
      obtain hf | hsmall := Bool.or_eq_true_iff.mp hfix
      · exact hs.2.2.2 hf
      · have hlog : Nat.log s.prime R = 0 := Nat.log_of_lt (of_decide_eq_true hsmall)
        apply Nat.le_antisymm hs.2.2.1
        have hre := hc.2
        simp only [exponentCapSlot, hlog, Nat.add_zero, ite_self] at hre
        exact hre

theorem freezeSizeSlots_closes {B : ℕ} {b : Box} (hnext : 1 < b.next) (hodd : Odd b.next)
    (h : (freezeSizeSlots B b).ClosedBelow B) : b.ClosedBelow B := by
  intro xs ys hmatch hcoords hsize hw hproper
  have hslots := List.forall₂_take b.slots.length
    (match_capped_numericalFit hnext hodd hmatch hsize)
  rw [hmatch.1.length_eq] at hslots
  have hx : (b.slots ++ (tailPrimeFloor b.next b.remaining).map floorSlot).take xs.length = b.slots := by
    rw [← hmatch.1.length_eq]
    simp
  rw [hx, List.take_left] at hslots
  exact h xs ys ⟨slots_fit_frozen hmatch.1 hslots, hmatch.2⟩ hcoords hsize hw hproper

end OddWeirdSubproblems

namespace OddWeirdSubproblems

open Finset

def Covered (D : Finset ℕ) (a b : ℕ) : Prop :=
  ∀ x, a ≤ x → x ≤ b → ∃ t ⊆ D, ∑ d ∈ t, d = x

def bitsStep (bits value : ℕ) : ℕ := bits ||| (bits <<< value)

def subsetBits : List ℕ → ℕ
  | [] => 1
  | w :: ws => bitsStep (subsetBits ws) w

theorem testBit_subsetBits {ds : List ℕ} (hnodup : ds.Nodup) {x : ℕ}
    (h : (subsetBits ds).testBit x = true) :
    ∃ t ⊆ ds.toFinset, ∑ d ∈ t, d = x := by
  induction ds generalizing x with
  | nil =>
    have hx : x = 0 := by
      cases x with
      | zero => rfl
      | succ x =>
        change (1 : ℕ).testBit (x + 1) = true at h
        simp [Nat.testBit_succ] at h
    exact ⟨∅, by simp, by simp [hx]⟩
  | cons w ws ih =>
    obtain ⟨hnmem, hnd⟩ := List.nodup_cons.mp hnodup
    simp only [subsetBits, bitsStep, Nat.testBit_or, Nat.testBit_shiftLeft,
      Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases h with hl | ⟨hlo, hr⟩
    · obtain ⟨t, ht, hs⟩ := ih hnd hl
      exact ⟨t, ht.trans (by simp), hs⟩
    · obtain ⟨t, ht, hs⟩ := ih hnd hr
      have hnot : w ∉ t := fun hmem => hnmem (List.mem_toFinset.mp (ht hmem))
      refine ⟨insert w t, by simpa using Finset.insert_subset_insert w ht, ?_⟩
      rw [sum_insert hnot, hs]
      omega

def bitIntervalOk (ds : List ℕ) (a b : ℕ) : Bool :=
  let mask := 2 ^ (b + 1 - a) - 1
  decide (((subsetBits ds >>> a) &&& mask) = mask)

theorem cover_of_bitIntervalOk {ds : List ℕ} {a b : ℕ}
    (hnodup : ds.Nodup) (h : bitIntervalOk ds a b = true) :
    Covered ds.toFinset a b := by
  intro x hlo hhi
  simp only [bitIntervalOk, decide_eq_true_eq] at h
  have hb := congrArg (fun k : ℕ => k.testBit (x - a)) h
  have hj : x - a < b + 1 - a := by omega
  simp only [Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one,
    decide_eq_true hj, Bool.and_true] at hb
  rw [show a + (x - a) = x by omega] at hb
  exact testBit_subsetBits hnodup hb

def growIntervalOk (a : ℕ) : ℕ → List ℕ → Bool
  | _, [] => true
  | b, w :: ws => decide (a + w ≤ b + 1) && growIntervalOk a (b + w) ws

theorem cover_of_growIntervalOk {ds ws : List ℕ} {a b : ℕ}
    (hnodup : (ds ++ ws).Nodup) (hcover : Covered ds.toFinset a b)
    (h : growIntervalOk a b ws = true) :
    Covered (ds ++ ws).toFinset a (b + ws.sum) := by
  induction ws generalizing ds b with
  | nil => simpa using hcover
  | cons w ws ih =>
    simp only [growIntervalOk, Bool.and_eq_true, decide_eq_true_eq] at h
    have heq : ds ++ w :: ws = (ds ++ [w]) ++ ws := by simp [List.append_assoc]
    rw [heq] at hnodup ⊢
    rw [List.sum_cons, ← Nat.add_assoc]
    apply ih hnodup _ h.2
    have hnot : w ∉ ds.toFinset := by
      intro hw
      have hnd : (ds ++ [w]).Nodup := (List.nodup_append.mp hnodup).1
      exact (List.nodup_append.mp hnd).2.2 _ (List.mem_toFinset.mp hw) _ (by simp) rfl
    have heq' : (ds ++ [w]).toFinset = insert w ds.toFinset := by
      ext d
      simp
    rw [heq']
    exact subsetSumIntervalInsert hnot hcover h.1

theorem cover_mono {D E : Finset ℕ} {a b : ℕ} (hDE : D ⊆ E)
    (h : Covered D a b) : Covered E a b := by
  intro x hx hy
  obtain ⟨t, ht, hs⟩ := h x hx hy
  exact ⟨t, ht.trans hDE, hs⟩

def divisorListOk (n : ℕ) (ds : List ℕ) : Bool :=
  tightlySorted ds && ds.all (fun d => decide (d ∣ n ∧ d < n))

theorem divisorListOk_sound {n : ℕ} {ds : List ℕ} (h : divisorListOk n ds = true) :
    ds.Nodup ∧ ds.toFinset ⊆ n.properDivisors := by
  simp only [divisorListOk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  exact ⟨tightlySorted_nodup h.1, fun d hd => Nat.mem_properDivisors.mpr (h.2 d (List.mem_toFinset.mp hd))⟩

theorem cover_of_validated_growth {n a b : ℕ} {ds ws : List ℕ}
    (hd : divisorListOk n (ds ++ ws) = true)
    (hb : bitIntervalOk ds a b = true) (hg : growIntervalOk a b ws = true) :
    Covered n.properDivisors a (b + ws.sum) := by
  obtain ⟨hnodup, hsub⟩ := divisorListOk_sound hd
  exact cover_mono hsub (cover_of_growIntervalOk hnodup
    (cover_of_bitIntervalOk (List.nodup_append.mp hnodup).1 hb) hg)

theorem sum_toFinset_of_nodup {ds : List ℕ} (h : ds.Nodup) :
    ∑ d ∈ ds.toFinset, d = ds.sum := by
  simpa using List.sum_toFinset (fun x : ℕ => x) h

end OddWeirdSubproblems

namespace OddWeirdSubproblems

def divisorsFromCoordinates : Coordinates → List ℕ
  | [] => [1]
  | (p, e) :: fs =>
    let ds := divisorsFromCoordinates fs
    (List.range (e + 1)).flatMap (fun i => ds.map (fun d => d * p ^ i))

def mergeDivisors : ℕ → List ℕ → List ℕ → List ℕ
  | 0, xs, ys => xs ++ ys
  | _ + 1, [], ys => ys
  | _ + 1, xs, [] => xs
  | fuel + 1, x :: xs, y :: ys =>
    if x ≤ y then x :: mergeDivisors fuel xs (y :: ys)
    else y :: mergeDivisors fuel (x :: xs) ys

def sortDivisors : ℕ → List ℕ → List ℕ
  | 0, ds => ds
  | _ + 1, [] => []
  | _ + 1, [d] => [d]
  | fuel + 1, ds =>
    let (lo, hi) := ds.splitAt (ds.length / 2)
    mergeDivisors ds.length (sortDivisors fuel lo) (sortDivisors fuel hi)

private def divisorLayers (p : ℕ) (ds : List ℕ) : ℕ → ℕ → List ℕ
  | 0, w => ds.map (· * w)
  | e + 1, w =>
    let scale := ds.map (· * w)
    let rest := divisorLayers p ds e (w * p)
    mergeDivisors (ds.length * (e + 2)) scale rest

def sortedDivisors : Coordinates → List ℕ
  | [] => [1]
  | (p, e) :: fs => divisorLayers p (sortedDivisors fs) e 1

def smallPrefix : ℕ → List ℕ → List ℕ
  | _, [] => []
  | room, d :: ds => if d ≤ room then d :: smallPrefix (room - d) ds else []

def highestPresent : ℕ → ℕ → ℕ → ℕ
  | 0, _, lo => lo
  | fuel + 1, bits, lo =>
    let mid := lo + 2 ^ fuel
    if bits >>> mid = 0 then highestPresent fuel bits lo
    else highestPresent fuel bits mid

def effectiveLow (bits total : ℕ) : ℕ :=
  let mask := 2 ^ (total / 2 + 1) - 1
  let missing := mask ^^^ (mask &&& bits)
  if missing = 0 then 0 else highestPresent 10 missing 0 + 1

def bitWitness : List ℕ → ℕ → List ℕ
  | [], _ => []
  | w :: ws, x =>
    if (subsetBits ws).testBit x then bitWitness ws x
    else w :: bitWitness ws (x - w)

end OddWeirdSubproblems

namespace OddWeirdSubproblems

open Finset

structure IntervalSource where
  kind : ℕ
  low : ℕ
  high : ℕ

structure CoreCoverage where
  proper : List ℕ
  small : List ℕ
  growing : List ℕ
  seedLo : ℕ
  seedHi : ℕ
  central : List IntervalSource

def IntervalSource.ok (n : ℕ) (c : CoreCoverage) (t : IntervalSource) : Bool :=
  if t.kind = 0 then
    divisorListOk n (c.small ++ c.growing) &&
      bitIntervalOk c.small c.seedLo c.seedHi &&
      growIntervalOk c.seedLo c.seedHi c.growing &&
      decide (c.seedLo ≤ t.low ∧ t.high ≤ c.seedHi + c.growing.sum)
  else if t.kind = 1 then
    divisorListOk n c.small && bitIntervalOk c.small t.low t.high
  else if t.kind = 2 then
    divisorListOk n c.proper && tightlySorted c.small &&
      decide (c.small = c.proper.take c.small.length) &&
      bitIntervalOk c.small t.low t.high &&
      decide (t.low ≤ t.high ∧ t.high ≤ c.proper.sum)
  else false

end OddWeirdSubproblems

namespace OddWeirdSubproblems

def bestDeletionBound (ss : List Slot) (stop : ℕ) : Option (ℕ × ℕ) :=
  let fs := ss.map Slot.minimum
  (List.range ss.length).foldl (fun best i =>
    let ds := decrement fs i
    let z := number ds
    let t := divisorSum ds
    let d := 2 * z - t
    let jump := if d = 0 then stop else min stop (t / d + 1)
    if z < number fs && (best.map Prod.snd).getD 0 < jump then some (i, jump) else best) none

end OddWeirdSubproblems

namespace OddWeirdSubproblems

def nextThreshold (b : Box) : ℕ :=
  let n := number b.minimum
  let s := divisorSum b.minimum
  let bound := s / (2 * n - s)
  2 * ((bound + 1) / 2) + 1

theorem nextThreshold_odd (b : Box) : Odd (nextThreshold b) :=
  ⟨_, rfl⟩

theorem threshold_odd_product_le {b : Box} {q : ℕ} (hq : Odd q)
    (hlt : q < nextThreshold b)
    (hdef : divisorSum b.minimum < 2 * number b.minimum) :
    (2 * number b.minimum - divisorSum b.minimum) * q ≤ divisorSum b.minimum := by
  let d := 2 * number b.minimum - divisorSum b.minimum
  have hd : 0 < d := Nat.sub_pos_of_lt hdef
  let k := divisorSum b.minimum / d
  have hqk : q ≤ k := by
    obtain ⟨a, ha⟩ := hq
    change q < 2 * ((k + 1) / 2) + 1 at hlt
    omega
  exact (Nat.mul_le_mul_left d hqk).trans (Nat.mul_div_le _ _)

def chooseWideSlot (b : Box) : Option ℕ :=
  let num := (b.slots.map Slot.upperNum).prod
  let den := (b.slots.map Slot.upperDen).prod
  let limit := if b.remaining = 1 then
      if num < 2 * den && (2 * den - 1) / (2 * den - num) - b.next < 20
      then b.next else 0
    else if b.remaining = 2 && 100 < b.next then b.next * b.next else b.next
  ((b.slots.zipIdx.filter (fun (s, _) => !s.fixed)).foldl
    (fun best (s, i) =>
      let key := s.prime ^ (s.exponent + 1)
      if (limit = 0 || b.remaining = 0 || key < limit) &&
        key < best.1
      then (key, some i) else best)
    (b.slots.foldl (fun n s => max n (s.prime ^ (s.exponent + 1) + 1)) 1, none)).2

end OddWeirdSubproblems

namespace OddWeirdSubproblems

structure LiteralInterval where
  seed : List ℕ
  growth : List ℕ
  low : ℕ
  seedHigh : ℕ
  multiple : ℕ
  shift : ℕ

def literalIntervalOk (n s first stop : ℕ) (a : LiteralInterval) : Bool :=
  let high := a.seedHigh + a.growth.sum
  let slope := 2 * n - s + a.multiple
  divisorListOk n (a.seed ++ a.growth) &&
  bitIntervalOk a.seed a.low a.seedHigh &&
  growIntervalOk a.low a.seedHigh a.growth &&
  decide (s ≤ 2 * n ∧ (a.multiple = 0 ∨ (a.multiple ∣ n ∧ a.multiple < n)) ∧
    (a.shift = 0 ∨ a.shift = n) ∧
    s ≤ high + a.shift + slope * first ∧ a.low + a.shift + slope * (stop - 1) ≤ s)

theorem literalIntervalOk_closes {ss : List Slot} {first stop : ℕ} {a : LiteralInterval}
    (h : literalIntervalOk (number (ss.map Slot.minimum)) (divisorSum (ss.map Slot.minimum))
      first stop a = true) : HeadRangeClosed ss 0 first stop := by
  simp only [literalIntervalOk, Bool.and_eq_true, decide_eq_true_eq] at h
  exact headRange_squarefree rfl rfl h.2.1 h.2.2.1 h.2.2.2.1
    (cover_of_validated_growth h.1.1.1 h.1.1.2 h.1.2) h.2.2.2.2.1 h.2.2.2.2.2

inductive SweepAction where
  | nonprimitive (i stop : ℕ)
  | interval (stop : ℕ) (cert : LiteralInterval)
  | composite (stop : ℕ)
  | point (witness : List ℕ)

def SweepAction.stop (first : ℕ) : SweepAction → ℕ
  | .nonprimitive _ stop | .interval stop _ | .composite stop => stop
  | .point _ => first + 1

def sweepActionOk (ss : List Slot) (first : ℕ) : SweepAction → Bool
  | .nonprimitive i stop =>
    let fs := ss.map Slot.minimum
    let ds := decrement fs i
    let z := number ds
    let t := divisorSum ds
    decide (i < ss.length ∧ z < number fs ∧ (2 * z - t) * (stop - 1) ≤ t)
  | .interval stop cert =>
    let fs := ss.map Slot.minimum
    literalIntervalOk (number fs) (divisorSum fs) first stop cert
  | .composite stop =>
    (List.range (stop - first)).all
      (fun j => decide ((first + j) % 2 = 0) || !mayBeOddPrime (first + j))
  | .point ds =>
    let b : Box := ⟨ss ++ [⟨first, 1, false⟩], first + 2, 0⟩
    decide (2 * number b.minimum ≤ divisorSum b.minimum) &&
      minimumOk (fun _ => ds) b

theorem sweepActionOk_closes {ss : List Slot} {first : ℕ} {a : SweepAction}
    (h : sweepActionOk ss first a = true) : HeadRangeClosed ss 0 first (a.stop first) := by
  cases a with
  | nonprimitive i stop =>
    simp only [sweepActionOk, decide_eq_true_eq] at h
    exact headRange_decrement_nondeficient h.1 rfl rfl h.2.1 h.2.2
  | interval stop cert =>
    exact literalIntervalOk_closes h
  | composite stop =>
    simp only [sweepActionOk, List.all_eq_true, Bool.or_eq_true, decide_eq_true_eq,
      Bool.not_eq_true'] at h
    intro q hlo hhi hp ho
    change q < stop at hhi
    have hno := h (q - first) (List.mem_range.mpr (by omega))
    rw [show first + (q - first) = q by omega] at hno
    rcases hno with he | hnp
    · obtain ⟨k, hk⟩ := ho
      omega
    · exact (Bool.false_ne_true (hnp.symm.trans (mayBeOddPrime_of_prime hp))).elim
  | point ds =>
    simp only [sweepActionOk, Bool.and_eq_true, decide_eq_true_eq] at h
    exact headRange_single (fun _ _ => minimumOk_closes h.1 h.2)

end OddWeirdSubproblems

namespace OddWeirdSubproblems

def divisorsAtMost : Coordinates → ℕ → List ℕ
  | [], B => if 1 ≤ B then [1] else []
  | (p, e) :: fs, B =>
    (List.range (e + 1)).flatMap (fun i =>
      let w := p ^ i
      if w ≤ B then (divisorsAtMost fs (B / w)).map (fun d => d * w)
      else [])

def cappedExponent (p cap : ℕ) : ℕ → ℕ
  | 0 => 0
  | e + 1 => if p ^ (e + 1) ≤ cap then e + 1 else cappedExponent p cap e

def largestDivisorSearch : Coordinates → ℕ → ℕ
  | [], B => if B = 0 then 0 else 1
  | (p, e) :: fs, B =>
    if B = 0 then 0
    else if p ^ e * number fs ≤ B then p ^ e * number fs
    else if fs.isEmpty then p ^ cappedExponent p B e
    else
      let lo := cappedExponent p (B / number fs) e
      let hi := cappedExponent p B e
      (List.range (hi + 1 - lo)).foldl (fun best j =>
        let w := p ^ (lo + j)
        max best (w * largestDivisorSearch fs (B / w))) 0

def largestDivisorUpTo (fs : Coordinates) (B : ℕ) : ℕ :=
  largestDivisorSearch fs.reverse B

def greedyWitness (fs : Coordinates) (seed : List ℕ) (bits : ℕ) :
    ℕ → ℕ → ℕ → Option (List ℕ)
  | 0, _, _ => none
  | fuel + 1, cap, target =>
    if target ≤ seed.sum && bits.testBit target then some (bitWitness seed target)
    else
      let d := largestDivisorUpTo fs (min cap target)
      if d ≤ seed.sum then none
      else
        (greedyWitness fs seed bits fuel (d - 1) (target - d)).map (d :: ·)

def sparseHintedWitness (fs : Coordinates) (slot h target : ℕ) : Option (List ℕ) := do
  let (p, _) ← fs[slot]?
  let rest := fs.eraseIdx slot
  let shift := h * p
  if target < shift then none else
    let ds := sortDivisors 20 (divisorsAtMost rest 1024)
    let seed := smallPrefix 1024 ds
    let target := target - shift
    let chosen ← greedyWitness rest seed (subsetBits seed) 64 (number rest) target
    pure (if shift = 0 then chosen else shift :: chosen)

end OddWeirdSubproblems

namespace OddWeirdSubproblems

def packedIndexWitness (fs : Coordinates) (slot h : ℕ) : List ℕ :=
  let n := number fs
  let s := divisorSum fs
  (sparseHintedWitness fs slot h (s - 2 * n)).getD [] |> sortDivisors 30

end OddWeirdSubproblems

namespace OddWeirdSubproblems

def readVarNat : ℕ → List ℕ → Option (ℕ × List ℕ)
  | 0, _ | _, [] => none
  | fuel + 1, b :: bs =>
    if b < 128 then some (b, bs)
    else (readVarNat fuel bs).map (fun (n, rest) => (b % 128 + 128 * n, rest))

def readNatList : ℕ → List ℕ → Option (List ℕ × List ℕ)
  | 0, rest => some ([], rest)
  | n + 1, bs => do
    let (value, tail) ← readVarNat 64 bs
    let (values, rest) ← readNatList n tail
    pure (value :: values, rest)

def readLengthPrefixed (bs : List ℕ) : Option (List ℕ × List ℕ) := do
  let (n, rest) ← readVarNat 64 bs
  readNatList n rest

private def readPackedBytes : ℕ → ℕ → ℕ → List ℕ → List ℕ
  | 0, n, v, tail => (List.range n).foldr (fun i acc => ((v >>> (8 * i)) % 256) :: acc) tail
  | fuel + 1, n, v, tail =>
    if n ≤ 8 then readPackedBytes 0 n v tail
    else
      let mid := n / 2
      let bits := 8 * mid
      readPackedBytes fuel mid (v % (1 <<< bits))
        (readPackedBytes fuel (n - mid) (v >>> bits) tail)

def bytesFromNat (n v : ℕ) : List ℕ := readPackedBytes 16 n v []

private def readLittleBytes : ℕ → List ℕ → Option (ℕ × List ℕ)
  | 0, data => some (0, data)
  | _ + 1, [] => none
  | n + 1, byte :: data => do
    let (value, rest) ← readLittleBytes n data
    pure (byte + (value <<< 8), rest)

private def copyPacked (value size distance count : ℕ) : ℕ :=
  let chunk := value >>> (8 * (size - distance))
  let wholeBytes := count - count % distance
  let whole := chunk * (((1 <<< (8 * wholeBytes)) - 1) / ((1 <<< (8 * distance)) - 1))
  let remainder := chunk % (1 <<< (8 * (count % distance)))
  whole + (remainder <<< (8 * wholeBytes))

def expandPackedTokens : ℕ → List ℕ → ℕ → ℕ → Option (List ℕ)
  | _, [], size, value => some (bytesFromNat size value)
  | 0, _ :: _, _, _ => none
  | fuel + 1, token :: data, size, value => do
    let (arg, rest) ← readVarNat 64 data
    if token = 0 then
      let (chunk, rest) ← readLittleBytes arg rest
      expandPackedTokens fuel rest (size + arg) (value + (chunk <<< (8 * size)))
    else if token = 1 && 0 < arg && arg ≤ size then
      let (count, rest) ← readVarNat 64 rest
      let chunk := copyPacked value size arg count
      expandPackedTokens fuel rest (size + count) (value + (chunk <<< (8 * size)))
    else none

def decodeInterval (bs : List ℕ) : Option (LiteralInterval × List ℕ) := do
  let (seed, rest) ← readLengthPrefixed bs
  let (growth, rest) ← readLengthPrefixed rest
  let (lo, rest) ← readVarNat 64 rest
  let (hi, rest) ← readVarNat 64 rest
  let (h, rest) ← readVarNat 64 rest
  let (c, rest) ← readVarNat 64 rest
  pure (⟨seed, growth, lo, hi, h, c⟩, rest)

def decodeSweepAction : List ℕ → Option (SweepAction × List ℕ)
  | [] => none
  | 0 :: rest => do
    let (i, rest) ← readVarNat 64 rest
    let (stop, rest) ← readVarNat 64 rest
    pure (.nonprimitive i stop, rest)
  | 1 :: rest => do
    let (stop, rest) ← readVarNat 64 rest
    let (cert, rest) ← decodeInterval rest
    pure (.interval stop cert, rest)
  | 2 :: rest => do
    let (stop, rest) ← readVarNat 64 rest
    pure (.composite stop, rest)
  | 3 :: rest => do
    let (ds, rest) ← readLengthPrefixed rest
    pure (.point ds, rest)
  | _ => none

end OddWeirdSubproblems

namespace OddWeirdSubproblems

def takeLargestWeight (cap : ℕ) : List ℕ → ℕ → ℕ × List ℕ
  | [], best => (best, [])
  | d :: ds, best =>
    if d ≤ cap then takeLargestWeight cap ds d else (best, d :: ds)

def scanGrowth (low target : ℕ) : ℕ → ℕ → List ℕ → Option (List ℕ)
  | 0, _, _ => none
  | fuel + 1, high, ds =>
    if target ≤ high then some []
    else
      let (d, rest) := takeLargestWeight (high + 1 - low) ds 0
      if d = 0 then none
      else (scanGrowth low target fuel (high + d) rest).map (d :: ·)

def sortedGrowth (fs : Coordinates) (low seedMax target high : ℕ) : Option (List ℕ) :=
  if target ≤ high then some [] else
    let ds := (sortedDivisors fs).dropWhile (· ≤ seedMax)
    scanGrowth low target 96 high (ds.takeWhile (· < number fs))

end OddWeirdSubproblems

namespace OddWeirdSubproblems

def decodePoint (b : Box) (data : List ℕ) : Option (List ℕ × List ℕ) := do
  let (tag, rest) ← readVarNat 64 data
  let i := tag / 8
  let j := tag % 8
  let fs := b.minimum
  let h := if j < 2 then j else ((fs.eraseIdx i)[j - 2]?.map Prod.fst).getD 0
  pure (packedIndexWitness fs i h, rest)

def minimumNeedsWitness (b : Box) : Bool := !minimumOk (fun _ => []) b

structure PointReplay where
  verify : Box → List ℕ → Option (List ℕ)
  sound : ∀ {b data tail}, verify b data = some tail → b.Closed

def PointReplay.ofDivisors (read : Box → List ℕ → Option (List ℕ × List ℕ)) : PointReplay where
  verify b data := do
    let (ds, tail) ← read b data
    if witnessOk (number b.minimum) (divisorSum b.minimum) ds then some tail else none
  sound := by
    intro b data tail h
    obtain ⟨⟨ds, tail'⟩, _, h⟩ := Option.bind_eq_some_iff.mp h
    dsimp only at h
    split at h
    · exact witnessOk_closes ‹_›
    · contradiction

def consumeMinimum (checkPoint : PointReplay) (b : Box) (data : List ℕ) : Option (List ℕ) :=
  if minimumNeedsWitness b then checkPoint.verify b data else some data

theorem consumeMinimum_closes
    {readPoint : PointReplay} {b : Box} {data tail : List ℕ}
    (hnd : 2 * number b.minimum ≤ divisorSum b.minimum)
    (h : consumeMinimum readPoint b data = some tail) : b.Closed := by
  unfold consumeMinimum minimumNeedsWitness at h
  split at h
  · exact readPoint.sound h
  · next hn =>
    have hm : minimumOk (fun _ => []) b = true := by simpa using hn
    exact minimumOk_closes hnd hm

def divisorOfRank (rank : ℕ) (xs : Coordinates) : ℕ :=
  let result := xs.reverse.foldl (fun (r, value) (p, e) =>
    (r / (e + 1), value * p ^ (r % (e + 1)))) (rank, 1)
  result.2

def rankDivisorList (fs : Coordinates) (gaps : List ℕ) : List ℕ :=
  let result := gaps.foldl (fun (previous, ds) gap =>
    let rank := previous + gap
    (rank, divisorOfRank (rank - 1) fs :: ds)) (0, [])
  sortDivisors 20 result.2

def decodeRankDivisors (fs : Coordinates) (bs : List ℕ) :
    Option (List ℕ × List ℕ) := do
  let (ds, rest) ← readLengthPrefixed bs
  pure (rankDivisorList fs ds, rest)

def decodeStreamAction (b : Box) (first top : ℕ) (bs : List ℕ) :
    Option (SweepAction × List ℕ) := do
  let (tag, rest) ← readVarNat 64 bs
  if tag = 0 then
    let (gap, rest) ← readVarNat 64 rest
    pure (.composite (first + gap), rest)
  else if tag = 1 then
    let (ds, rest) ← decodeRankDivisors (b.minimum ++ [(first, 1)]) rest
    pure (.point ds, rest)
  else
    let selector := (tag - 2) / 2
    let useCore := selector % 2
    let j := selector / 2
    let h := if j < 2 then j else (b.slots[j - 2]?.map Slot.prime).getD 0
    let n := number b.minimum
    let s := divisorSum b.minimum
    let shift := if useCore = 0 then 0 else n
    let candidates := sortDivisors 20 (divisorsAtMost b.minimum (min 1024 (n - 1)))
    let seed := smallPrefix 1024 candidates
    let lo := effectiveLow (subsetBits seed) seed.sum
    let hi := seed.sum - lo
    let slope := 2 * n - s + h
    let stop := min top ((s - shift - lo) / slope + 1)
    if (tag - 2) % 2 = 0 then
      let goal := s - (shift + slope * first)
      let ds ← sortedGrowth b.minimum lo (seed.getLast?.getD 0) goal hi
      pure (.interval stop ⟨seed, ds, lo, hi, h, shift⟩, rest)
    else
      let (ds, rest) ← decodeRankDivisors b.minimum rest
      pure (.interval stop ⟨seed, ds, lo, hi, h, shift⟩, rest)

abbrev SweepReader := Box → ℕ → ℕ → List ℕ → Option (SweepAction × List ℕ)

structure SweepVerifier where
  run : Box → ℕ → ℕ → List ℕ → Option (ℕ × List ℕ)
  sound : ∀ {b first top data stop tail}, run b first top data = some (stop, tail) →
    HeadRangeClosed b.slots 0 first stop

def SweepVerifier.ofActions (reader : SweepReader) : SweepVerifier where
  run b first top data := do
    let (a, rest) ← reader b first top data
    if sweepActionOk b.slots first a then some (a.stop first, rest) else none
  sound := by
    intro b first top data stop tail h
    obtain ⟨⟨a, rest⟩, _, h⟩ := Option.bind_eq_some_iff.mp h
    dsimp only at h
    split at h
    · have he : a.stop first = stop := by simpa using congrArg (Option.map Prod.fst) h
      exact he ▸ sweepActionOk_closes ‹_›
    · contradiction

def consumeSweep (readSweep : SweepVerifier) (b : Box) (stop : ℕ) : ℕ → ℕ → List ℕ → Option (List ℕ)
  | 0, first, data => if stop ≤ first then some data else none
  | fuel + 1, first, data =>
    if stop ≤ first then none else do
      let (next, rest) ← readSweep.run b first stop data
      if first < next then
        consumeSweep readSweep b stop fuel next rest
      else none

theorem consumeSweep_closes {readSweep : SweepVerifier} {b : Box} {stop fuel first : ℕ}
    {data tail : List ℕ} (h : consumeSweep readSweep b stop fuel first data = some tail) :
    HeadRangeClosed b.slots 0 first stop := by
  induction fuel generalizing first data with
  | zero =>
    simp only [consumeSweep] at h
    split at h
    · intro q hlo hhi
      omega
    · contradiction
  | succ fuel ih =>
    simp only [consumeSweep] at h
    split at h
    · contradiction
    · next hl =>
      obtain ⟨⟨next, rest⟩, ha, h⟩ := Option.bind_eq_some_iff.mp h
      dsimp only at h
      split at h
      · exact headRange_join (readSweep.sound ha) (ih h)
      · contradiction

def consumeWholeSweep (readSweep : SweepVerifier) (b : Box) (stop : ℕ) (data : List ℕ) : Option (List ℕ) := do
  let (count, rest) ← readVarNat 64 data
  match bestDeletionBound b.slots stop with
  | some (i, jump) =>
    if b.next < jump then
      if sweepActionOk b.slots b.next (.nonprimitive i jump) then
        consumeSweep readSweep b stop count jump rest
      else none
    else consumeSweep readSweep b stop count b.next rest
  | none => consumeSweep readSweep b stop count b.next rest

theorem consumeWholeSweep_closes {readSweep : SweepVerifier} {b : Box} {stop : ℕ} {data tail : List ℕ}
    (h : consumeWholeSweep readSweep b stop data = some tail) : HeadRangeClosed b.slots 0 b.next stop := by
  unfold consumeWholeSweep at h
  cases hd : readVarNat 64 data with
  | none => simp [hd] at h
  | some row =>
    obtain ⟨count, rest⟩ := row
    rw [hd] at h
    dsimp only at h
    split at h
    · next i jump heq =>
      split at h
      · split at h
        · exact headRange_join (sweepActionOk_closes (a := .nonprimitive i jump) ‹_›) (consumeSweep_closes h)
        · contradiction
      · exact consumeSweep_closes h
    · exact consumeSweep_closes h

structure BranchPruning where
  verify : Box → List ℕ → Option (Bool × List ℕ)
  sound : ∀ {b data tail}, verify b data = some (true, tail) → b.Closed

def BranchPruning.none : BranchPruning where
  verify _ data := some (false, data)
  sound := by
    intro _ _ _ h
    simp at h

def streamReplay (readPoint : PointReplay) (readSweep : SweepVerifier)
    (prune : BranchPruning) (cut : Box → Bool) : ℕ → Box → List ℕ → Option (List ℕ)
  | 0, _, _ => none
  | fuel + 1, b, data =>
    if cut b then some data
    else do
      let (closed, data) ← prune.verify b data
      if closed then some data
      else if 2 * number b.minimum ≤ divisorSum b.minimum then consumeMinimum readPoint b data
      else if b.upperNum ≤ 2 * b.upperDen then some data
      else if 0 < b.remaining && b.next < nextThreshold b then
        (if b.remaining = 1 then consumeWholeSweep readSweep b (nextThreshold b) data else some data).bind
          (streamReplay readPoint readSweep prune cut fuel {b with next := nextThreshold b})
      else match (chooseWideSlot b).bind (fun i => b.slots[i]?.map (fun s => (i, s))) with
      | some (i, s) => do
        if s.fixed then none else
          let data ← streamReplay readPoint readSweep prune cut fuel {b with slots := b.slots.set i {s with fixed := true}} data
          streamReplay readPoint readSweep prune cut fuel {b with slots := b.slots.set i {s with exponent := s.exponent + 1}} data
      | none =>
        match b.remaining with
        | 0 => none
        | r + 1 => do
          let data ← streamReplay readPoint readSweep prune cut fuel ⟨b.slots, b.next + 2, r + 1⟩ data
          if mayBeOddPrime b.next then
            streamReplay readPoint readSweep prune cut fuel ⟨b.slots ++ [⟨b.next, 1, false⟩], b.next + 2, r⟩ data
          else some data

theorem stream_threshold_closes {readSweep : SweepVerifier} {ss : List Slot} {p r : ℕ} {data : List ℕ}
    (hdef : divisorSum (ss.map Slot.minimum) < 2 * number (ss.map Slot.minimum))
    (hcheck : r = 0 → ∃ tail,
      let b : Box := ⟨ss, p, 1⟩
      consumeWholeSweep readSweep b (nextThreshold b) data = some tail)
    (hskip : (⟨ss, nextThreshold ⟨ss, p, r + 1⟩, r + 1⟩ : Box).Closed) :
    (⟨ss, p, r + 1⟩ : Box).Closed := by
  apply close_jump_next hskip
  intro q hp hq hprime ho
  cases r with
  | zero =>
    obtain ⟨tail, h⟩ := hcheck rfl
    exact consumeWholeSweep_closes h q hp hq hprime ho
  | succ r =>
    apply close_nondeficient_squarefree_prefix (Nat.succ_pos _)
    have hu := threshold_odd_product_le ho hq hdef
    have h := Nat.mul_le_mul_right q
      (show 2 * number (ss.map Slot.minimum) ≤
        2 * number (ss.map Slot.minimum) - divisorSum (ss.map Slot.minimum) +
          divisorSum (ss.map Slot.minimum) by omega)
    rw [Nat.add_mul] at h
    rw [Nat.mul_add, Nat.mul_one]
    exact le_trans h (Nat.add_le_add_right hu _)

theorem streamReplay_closes
    {readPoint : PointReplay} {readSweep : SweepVerifier} {prune : BranchPruning} {cut : Box → Bool} {fuel : ℕ} {b : Box} {data tail : List ℕ}
    (hcut : ∀ box, cut box = true → box.Closed)
    (hlo : 1 < b.next) (hodd : Odd b.next) (h : streamReplay readPoint readSweep prune cut fuel b data = some tail) :
    b.Closed := by
  induction fuel generalizing b data tail with
  | zero => simp [streamReplay] at h
  | succ fuel ih =>
    rw [streamReplay] at h
    split at h
    · exact hcut b ‹_›
    obtain ⟨⟨closed, input⟩, hprune, h⟩ := Option.bind_eq_some_iff.mp h
    cases closed
    · simp only [Bool.false_eq_true, if_false] at h
      split at h
      · exact consumeMinimum_closes ‹_› h
      next hnondef =>
        split at h
        · exact close_of_upperNum_le hlo ‹_›
        split at h
        next hguard =>
          obtain ⟨hr, hnext⟩ : 0 < b.remaining ∧ b.next < nextThreshold b := by simpa using hguard
          rcases b with ⟨ss, p, r⟩
          cases r with
          | zero => exact (Nat.lt_irrefl 0 hr).elim
          | succ r =>
            have hnd : divisorSum (ss.map Slot.minimum) <
                2 * number (ss.map Slot.minimum) := Nat.lt_of_not_ge hnondef
            have hs : ∃ mid,
                (if r + 1 = 1 then consumeWholeSweep readSweep ⟨ss, p, r + 1⟩
                  (nextThreshold ⟨ss, p, r + 1⟩) input else some input) = some mid ∧
                streamReplay readPoint readSweep prune cut fuel ⟨ss, nextThreshold ⟨ss, p, r + 1⟩, r + 1⟩ mid = some tail :=
              Option.bind_eq_some_iff.mp h
            obtain ⟨mid, hmid, hend⟩ := hs
            apply stream_threshold_closes (readSweep := readSweep) (data := input) hnd _
              (ih (hlo.trans hnext) (nextThreshold_odd _) hend)
            intro heq
            subst r
            exact ⟨mid, by simpa using hmid⟩
        next =>
          split at h
          next i s hs =>
            have hi : b.slots[i]? = some s := by
              obtain ⟨j, _, hj⟩ := Option.bind_eq_some_iff.mp hs
              cases hg : b.slots[j]? <;> simp_all
            split at h
            · contradiction
            · have hf : s.fixed = false := by simp_all
              obtain ⟨mid, h₁, h₂⟩ := Option.bind_eq_some_iff.mp h
              exact close_split_slot hi hf (ih hlo hodd h₁) (ih hlo hodd h₂)
          next =>
            rcases b with ⟨ss, p, r⟩
            cases r with
            | zero => contradiction
            | succ r =>
              obtain ⟨mid, hskip, htake⟩ := Option.bind_eq_some_iff.mp h
              have hodd' : Odd (p + 2) := by
                obtain ⟨k, hk⟩ := hodd
                exact ⟨k + 1, by dsimp at hk; omega⟩
              have hlo' : 1 < p + 2 := by dsimp at hlo; omega
              apply close_split_next hodd (ih hlo' hodd' hskip)
              intro hp
              exact ih hlo' hodd' (by simpa only [if_pos (mayBeOddPrime_of_prime hp)] using htake)
    · exact prune.sound hprune

def checkPacked (readPoint : PointReplay) (readSweep : SweepVerifier)
    (cut : Box → Bool) (fuel : ℕ) (b : Box) (count value : ℕ) (prune : BranchPruning := .none) : Bool :=
  match expandPackedTokens count (bytesFromNat count value) 0 0 with
  | none => false
  | some raw => match streamReplay readPoint readSweep prune cut fuel b raw with
    | some [] => true
    | _ => false

theorem checkPackedBlock
    {readPoint : PointReplay} {b : Box} {cut : Box → Bool} {fuel count value : ℕ}
    (readSweep : SweepVerifier := .ofActions decodeStreamAction)
    (prune : BranchPruning := .none)
    (hcut : ∀ box, cut box = true → box.Closed) (hlo : 1 < b.next) (hodd : Odd b.next)
    (h : checkPacked readPoint readSweep cut fuel b count value prune = true) : b.Closed := by
  unfold checkPacked at h
  split at h
  · contradiction
  · split at h
    · exact streamReplay_closes hcut hlo hodd ‹_›
    · contradiction

inductive ClosedCuts : List Box → Prop
  | nil : ClosedCuts []
  | cons {b : Box} {bs : List Box} : b.Closed → ClosedCuts bs → ClosedCuts (b :: bs)

theorem ClosedCuts.closedOfMem {cuts : List Box} (hcuts : ClosedCuts cuts)
    {b : Box} (hb : b ∈ cuts) : b.Closed := by
  induction hcuts with
  | nil => simp at hb
  | cons hd _ ih =>
    rcases List.mem_cons.mp hb with rfl | hb
    · exact hd
    · exact ih hb

end OddWeirdSubproblems

namespace OddWeirdSubproblems

def boundedSweepEnd (B : ℕ) (b : Box) : ℕ :=
  min (nextThreshold b) (2 * (((B - 1) / number b.minimum + 1) / 2) + 1)

private theorem boundedSweep_closes {B : ℕ} {b : Box} {data tail : List ℕ}
    {readSweep : SweepVerifier}
    (h : consumeWholeSweep readSweep b (boundedSweepEnd B b) data = some tail)
    (hrest : ({b with next := nextThreshold b} : Box).ClosedBelow B)
    (hr : b.remaining = 1) : b.ClosedBelow B := by
  rcases b with ⟨ss, p, r⟩
  change r = 1 at hr
  subst r
  apply closeBelow_jump_next (stop := nextThreshold ⟨ss, p, 1⟩) hrest
  intro q hq hqhi hp hodd
  by_cases hcut : q < boundedSweepEnd B ⟨ss, p, 1⟩
  · exact closedBelow_of_closed (consumeWholeSweep_closes h q hq hcut hp hodd) B
  · intro xs ys hm hv hlt _ _
    have hy : ys = [] := List.length_eq_zero_iff.mp hm.2.2
    have hx := Nat.le_of_dvd (number_pos (primeCoordinates_left hv).1) (minimum_dvd hm.1)
    have hmpos : 0 < number (ss.map Slot.minimum) := by
      have hvalid := minimum_valid hm.1 (primeCoordinates_left hv)
      simp only [List.map_append, List.map_cons, List.map_nil] at hvalid
      exact number_pos (primeCoordinates_left hvalid).1
    have hu : (B - 1) / number (ss.map Slot.minimum) < q := by
      unfold boundedSweepEnd at hcut
      change ¬ q < min (nextThreshold ⟨ss, p, 1⟩)
        (2 * (((B - 1) / number (ss.map Slot.minimum) + 1) / 2) + 1) at hcut
      omega
    have hsize := Nat.lt_mul_of_div_lt hu hmpos
    rw [Nat.mul_comm] at hsize
    dsimp only at hx
    rw [List.map_append] at hx
    change number (ss.map Slot.minimum ++ [(q, 1)]) ≤ number xs at hx
    rw [number_append, number_cons] at hx
    simp only [pow_one, show number [] = 1 from rfl, mul_one] at hx
    simp only [hy, List.append_nil] at hlt
    omega

private theorem thresholdSweep_closes {B : ℕ} {b : Box} {data tail : List ℕ}
    {readSweep : SweepVerifier} {limited : Bool}
    (h : consumeWholeSweep readSweep b
      (if limited then boundedSweepEnd B b else nextThreshold b) data = some tail)
    (hrest : ({b with next := nextThreshold b} : Box).ClosedBelow B)
    (hr : b.remaining = 1) : b.ClosedBelow B := by
  cases limited
  · rcases b with ⟨ss, p, r⟩
    change r = 1 at hr
    subst r
    apply closeBelow_jump_next (stop := nextThreshold ⟨ss, p, 1⟩) hrest
    intro q hq hqhi hp hodd
    exact closedBelow_of_closed (consumeWholeSweep_closes h q hq hqhi hp hodd) B
  · exact boundedSweep_closes h hrest hr

private theorem closeBelow_skip_composites {ss : List Slot} {B p r fuel : ℕ}
    (hodd : Odd p) (h : (⟨ss, firstAllowedOdd p fuel, r + 1⟩ : Box).ClosedBelow B) :
    (⟨ss, p, r + 1⟩ : Box).ClosedBelow B :=
  closeBelow_jump_next h fun _ hlo hhi hp hq =>
    (hhi.not_ge (firstAllowedOdd_le_prime hodd hq hp hlo fuel)).elim

private def normalizeSlots (fast : Bool) (B : ℕ) (b : Box) : Box :=
  if fast then freezeSizeSlots B b else b

private theorem normalizeSlots_closedBelow {B : ℕ} {b : Box} (fast : Bool)
    (hlo : 1 < b.next) (hodd : Odd b.next)
    (h : (normalizeSlots fast B b).ClosedBelow B) : b.ClosedBelow B := by
  cases fast
  · exact h
  · exact freezeSizeSlots_closes hlo hodd h

def replayWithSizeLimit (limited fast : Bool) (B : ℕ) (readPoint : PointReplay) (readSweep : SweepVerifier)
    (prune : BranchPruning) (cut : Box → Bool) : ℕ → Box → List ℕ → Option (List ℕ)
  | 0, _, _ => none
  | fuel + 1, b, data =>
    if cut b then some data
    else if limited && decide (B ≤ number b.minimum * (tailPrimeFloor b.next b.remaining).prod) then some data
    else if (limited && fast) && exponentCapOk B b then some data
    else
      let b := normalizeSlots (limited && fast) B b
      match (if !limited || fast then none else sizeFixedSlot B b) with
      | some (i, s) =>
        replayWithSizeLimit limited fast B readPoint readSweep prune cut fuel
          {b with slots := b.slots.set i {s with fixed := true}} data
      | none =>
        if rankedUpperNum b ≤ 2 * rankedUpperDen b then some data
        else do
          let (closed, data) ← prune.verify b data
          if closed then some data
          else if 2 * number b.minimum ≤ divisorSum b.minimum then consumeMinimum readPoint b data
          else if 0 < b.remaining && b.next < nextThreshold b then
            (if b.remaining = 1 then consumeWholeSweep readSweep b
                (if limited then boundedSweepEnd B b else nextThreshold b) data
              else some data).bind
              (replayWithSizeLimit limited fast B readPoint readSweep prune cut fuel {b with next := nextThreshold b})
          else match (chooseWideSlot b).bind (fun i => b.slots[i]?.map (fun s => (i, s))) with
          | some (i, s) => do
            if s.fixed then none else
              let data ← replayWithSizeLimit limited fast B readPoint readSweep prune cut fuel
                {b with slots := b.slots.set i {s with fixed := true}} data
              replayWithSizeLimit limited fast B readPoint readSweep prune cut fuel
                {b with slots := b.slots.set i {s with exponent := s.exponent + 1}} data
          | none =>
            match b.remaining with
            | 0 => none
            | r + 1 =>
              let q := firstAllowedOdd b.next 32
              if b.next < q then
                replayWithSizeLimit limited fast B readPoint readSweep prune cut fuel ⟨b.slots, q, r + 1⟩ data
              else do
                let data ← replayWithSizeLimit limited fast B readPoint readSweep prune cut fuel
                  ⟨b.slots, b.next + 2, r + 1⟩ data
                if mayBeOddPrime b.next then
                  replayWithSizeLimit limited fast B readPoint readSweep prune cut fuel
                    ⟨b.slots ++ [⟨b.next, 1, false⟩], b.next + 2, r⟩ data
                else some data

theorem replayWithSizeLimit_closes
    {limited fast : Bool} {B : ℕ} {readPoint : PointReplay} {readSweep : SweepVerifier} {prune : BranchPruning}
    {cut : Box → Bool} {fuel : ℕ} {b : Box} {data tail : List ℕ}
    (hcut : ∀ box, cut box = true → box.ClosedBelow B)
    (hlo : 1 < b.next) (hodd : Odd b.next)
    (h : replayWithSizeLimit limited fast B readPoint readSweep prune cut fuel b data = some tail) :
    b.ClosedBelow B := by
  induction fuel generalizing b data tail with
  | zero => contradiction
  | succ fuel ih =>
    rw [replayWithSizeLimit] at h
    split at h
    · exact hcut b ‹_›
    split at h
    · exact closeBelow_of_ranked_minimum_ge hodd (of_decide_eq_true (Bool.and_eq_true_iff.mp ‹_›).2)
    split at h
    · exact exponentCapOk_closes hlo hodd ((Bool.and_eq_true_iff.mp ‹_›).2)
    apply normalizeSlots_closedBelow (limited && fast) hlo hodd
    have hlo' : 1 < (normalizeSlots (limited && fast) B b).next := by
      cases limited <;> cases fast <;> simpa [normalizeSlots, freezeSizeSlots] using hlo
    have hodd' : Odd (normalizeSlots (limited && fast) B b).next := by
      cases limited <;> cases fast <;> simpa [normalizeSlots, freezeSizeSlots] using hodd
    dsimp only at h
    generalize hbox : normalizeSlots (limited && fast) B b = normalized at h ⊢
    rw [hbox] at hlo' hodd'
    clear hlo hodd
    rename_i h_cut h_min h_cap
    clear h_cut h_min h_cap hbox b
    have hlo := hlo'
    have hodd := hodd'
    clear hlo' hodd'
    split at h
    · next i s hsize =>
      have hsize' : sizeFixedSlot B normalized = some (i, s) := by cases limited <;> cases fast <;> simp_all
      exact sizeFixedSlot_closes hsize' hodd (ih hlo hodd h)
    · split at h
      · exact closedBelow_of_closed (close_of_ranked_upper hlo hodd ‹_›) B
      obtain ⟨⟨closed, input⟩, hprune, h⟩ := Option.bind_eq_some_iff.mp h
      cases closed
      · simp only [Bool.false_eq_true, if_false] at h
        split at h
        · exact closedBelow_of_closed (consumeMinimum_closes ‹_› h) B
        next hnondef =>
          split at h
          next hguard =>
            obtain ⟨hr, hnext⟩ : 0 < normalized.remaining ∧ normalized.next < nextThreshold normalized := by simpa using hguard
            obtain ⟨mid, hmid, hend⟩ := Option.bind_eq_some_iff.mp h
            have hskip := ih (hlo.trans hnext) (nextThreshold_odd _) hend
            rcases normalized with ⟨ss, p, r⟩
            cases r with
            | zero => exact (Nat.lt_irrefl 0 hr).elim
            | succ r =>
              cases r with
              | zero => exact thresholdSweep_closes (limited := limited) (by simpa using hmid) hskip rfl
              | succ r =>
                apply closeBelow_jump_next hskip
                intro q _ hq _ ho
                apply closedBelow_of_closed _ B
                apply close_nondeficient_squarefree_prefix (by omega)
                have hnd : divisorSum (ss.map Slot.minimum) <
                    2 * number (ss.map Slot.minimum) := Nat.lt_of_not_ge hnondef
                have hu := threshold_odd_product_le ho hq hnd
                have hbase := Nat.mul_le_mul_right q
                  (show 2 * number (ss.map Slot.minimum) ≤
                    2 * number (ss.map Slot.minimum) - divisorSum (ss.map Slot.minimum) +
                      divisorSum (ss.map Slot.minimum) by omega)
                rw [Nat.add_mul] at hbase
                rw [Nat.mul_add, Nat.mul_one]
                exact le_trans hbase (Nat.add_le_add_right hu _)
          next =>
            split at h
            next i s hs =>
              have hi : normalized.slots[i]? = some s := by
                obtain ⟨j, _, hj⟩ := Option.bind_eq_some_iff.mp hs
                cases hg : normalized.slots[j]? <;> simp_all
              split at h
              · contradiction
              · have hf : s.fixed = false := by simp_all
                obtain ⟨mid, h₁, h₂⟩ := Option.bind_eq_some_iff.mp h
                exact closeBelow_split_slot hi hf (ih hlo hodd h₁) (ih hlo hodd h₂)
            next =>
              rcases normalized with ⟨ss, p, r⟩
              cases r with
              | zero => contradiction
              | succ r =>
                dsimp only at h
                split at h
                · exact closeBelow_skip_composites hodd
                    (ih (hlo.trans_le (firstAllowedOdd_ge _ _)) (firstAllowedOdd_odd hodd _) h)
                · obtain ⟨mid, hskip, htake⟩ := Option.bind_eq_some_iff.mp h
                  have hodd' : Odd (p + 2) := by
                    obtain ⟨k, hk⟩ := hodd
                    exact ⟨k + 1, by dsimp at hk; omega⟩
                  have hlo' : 1 < p + 2 := by dsimp at hlo; omega
                  apply closeBelow_split_next hodd (ih hlo' hodd' hskip)
                  intro hp
                  exact ih hlo' hodd' (by simpa only [if_pos (mayBeOddPrime_of_prime hp)] using htake)
      · exact closedBelow_of_closed (prune.sound hprune) B

private theorem unboundedReplay_independent_of_bound
    (B : ℕ) (readPoint : PointReplay) (readSweep : SweepVerifier) (prune : BranchPruning)
    (cut : Box → Bool) (fuel : ℕ) (b : Box) (data : List ℕ) :
    replayWithSizeLimit false true 0 readPoint readSweep prune cut fuel b data =
      replayWithSizeLimit false true B readPoint readSweep prune cut fuel b data := by
  induction fuel generalizing b data with
  | zero => rfl
  | succ fuel ih =>
    simp only [replayWithSizeLimit, Bool.false_and, Bool.false_eq_true, if_false,
      normalizeSlots, Bool.not_false, Bool.true_or, if_true, ih]

def unboundedRankedStream (readPoint : PointReplay) (readSweep : SweepVerifier)
    (prune : BranchPruning) (cut : Box → Bool) : ℕ → Box → List ℕ → Option (List ℕ) :=
  replayWithSizeLimit false true 0 readPoint readSweep prune cut

theorem unboundedRankedStream_closes
    {readPoint : PointReplay} {readSweep : SweepVerifier} {prune : BranchPruning}
    {cut : Box → Bool} {fuel : ℕ} {b : Box} {data tail : List ℕ}
    (hcut : ∀ box, cut box = true → box.Closed)
    (hlo : 1 < b.next) (hodd : Odd b.next)
    (h : unboundedRankedStream readPoint readSweep prune cut fuel b data = some tail) :
    b.Closed := by
  intro xs ys hm hv hw hp
  let B := number (xs ++ ys) + 1
  change replayWithSizeLimit false true 0 readPoint readSweep prune cut fuel b data = some tail at h
  rw [unboundedReplay_independent_of_bound B] at h
  exact replayWithSizeLimit_closes (fun box hc => closedBelow_of_closed (hcut box hc) B)
    hlo hodd h xs ys hm hv (Nat.lt_succ_self _) hw hp

end OddWeirdSubproblems

namespace OddWeirdSubproblems

open Finset

def PrefixGapBound : ℕ → List ℕ → Prop
  | _, [] => True
  | G, d :: ds => d ≤ G ∧ PrefixGapBound (G + d) ds

theorem PrefixGapBound.scale {G : ℕ} {ds : List ℕ} (h : PrefixGapBound G ds) (v : ℕ) :
    PrefixGapBound (v * G) (ds.map (v * ·)) := by
  induction ds generalizing G with
  | nil => trivial
  | cons d ds ih =>
    obtain ⟨hd, hs⟩ := h
    exact ⟨Nat.mul_le_mul_left v hd, by simpa only [Nat.mul_add] using ih hs⟩

private theorem growIntervalOk_of_prefixGapBound {C T G : ℕ} {ws : List ℕ}
    (hgap : PrefixGapBound G ws) (hwidth : G + 2 * C ≤ T + 1) :
    growIntervalOk C (T - C) ws = true := by
  induction ws generalizing T G with
  | nil => rfl
  | cons w ws ih =>
    obtain ⟨hw, htail⟩ := hgap
    simp only [growIntervalOk, Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨by omega, ?_⟩
    rw [show T - C + w = T + w - C by omega]
    exact ih htail (by omega)

theorem cover_of_fresh_prefixGapBound {D : Finset ℕ} {ws : List ℕ} {C T G : ℕ}
    (hcover : Covered D C (T - C)) (hnd : ws.Nodup) (hfresh : Disjoint D ws.toFinset)
    (hgap : PrefixGapBound G ws) (hwidth : G + 2 * C ≤ T + 1) :
    Covered (D ∪ ws.toFinset) C (T + ws.sum - C) := by
  have hnodup : (D.toList ++ ws).Nodup := by
    apply List.nodup_append.mpr
    refine ⟨Finset.nodup_toList _, hnd, ?_⟩
    intro d hd d' hd' h
    subst d'
    exact (Finset.disjoint_left.mp hfresh) (Finset.mem_toList.mp hd) (List.mem_toFinset.mpr hd')
  have hg := cover_of_growIntervalOk hnodup (by simpa using hcover)
    (growIntervalOk_of_prefixGapBound hgap hwidth)
  simpa only [List.toFinset_append, Finset.toList_toFinset, show T - C + ws.sum = T + ws.sum - C by omega]
    using hg

private theorem sumDivisors_coprime_prime_power {u p : ℕ} (hp : p.Prime) (hpu : ¬ p ∣ u)
    (b : ℕ) : (∑ d ∈ (u * p ^ b).divisors, d) =
      (∑ d ∈ u.divisors, d) * ∑ j ∈ range (b + 1), p ^ j := by
  rw [((hp.coprime_iff_not_dvd.mpr hpu).symm.pow_right b).sum_divisors_mul,
    Nat.sum_divisors_prime_pow hp]

private theorem sumProperDivisors_raise_coprime_prime_power {u p a : ℕ}
    (hp : p.Prime) (hpu : ¬ p ∣ u) :
    (∑ d ∈ (u * p ^ (a + 1)).properDivisors, d) =
      (∑ d ∈ (u * p ^ a).properDivisors, d) + p ^ (a + 1) * (∑ d ∈ u.properDivisors, d) + u * p ^ a := by
  let hsum := sumDivisors_coprime_prime_power hp hpu
  have h : (∑ d ∈ (u * p ^ (a + 1)).divisors, d) =
      (∑ d ∈ (u * p ^ a).divisors, d) + (∑ d ∈ u.divisors, d) * p ^ (a + 1) := by
    rw [hsum, hsum, sum_range_succ, Nat.mul_add]
  rw [Nat.sum_divisors_eq_sum_properDivisors_add_self (n := u),
    Nat.sum_divisors_eq_sum_properDivisors_add_self (n := u * p ^ a),
    Nat.sum_divisors_eq_sum_properDivisors_add_self (n := u * p ^ (a + 1)), Nat.add_mul,
    mul_comm (∑ d ∈ u.properDivisors, d)] at h
  omega

theorem cover_raise_coprime_prime_power {u p a C G : ℕ} {ds : List ℕ}
    (hu : 0 < u) (hp : p.Prime) (hpu : ¬ p ∣ u) (hnd : ds.Nodup)
    (hds : ds.toFinset = u.properDivisors) (hgap : PrefixGapBound G ds) :
    let m := u * p ^ a
    let n := u * p ^ (a + 1)
    let v := p ^ (a + 1)
    let T := ∑ d ∈ m.properDivisors, d
    let U := ∑ d ∈ u.properDivisors, d
    Covered m.properDivisors C (T - C) →
    v * G + 2 * C ≤ T + 1 →
    m + 2 * C ≤ T + v * U + 1 →
    Covered n.properDivisors C ((∑ d ∈ n.properDivisors, d) - C) := by
  intro m n v T U hcover hscaled hlast
  let ws := ds.map (v * ·)
  have hv : 0 < v := pow_pos hp.pos _
  have hm : 0 < m := Nat.mul_pos hu (pow_pos hp.pos _)
  have hn : n = m * p := by simp only [n, m, pow_succ, mul_assoc]
  have hvnot : ¬ v ∣ m := by
    intro hvm
    apply hpu
    apply (Nat.mul_dvd_mul_iff_left (pow_pos hp.pos a)).mp
    simpa only [v, m, pow_succ, mul_comm p, mul_comm u] using hvm
  have hval {d : ℕ} (hd : d ∈ ws.toFinset) : ∃ e ∈ u.properDivisors, d = v * e := by
    obtain ⟨e, he, heq⟩ := List.mem_map.mp (List.mem_toFinset.mp hd)
    exact ⟨e, hds ▸ List.mem_toFinset.mpr he, heq.symm⟩
  have hfresh : Disjoint m.properDivisors ws.toFinset := by
    apply Finset.disjoint_left.mpr
    intro d hd hd'
    obtain ⟨e, _, rfl⟩ := hval hd'
    exact hvnot ((dvd_mul_right v e).trans (Nat.mem_properDivisors.mp hd).1)
  have hws : ws.Nodup := hnd.map (mul_right_injective₀ hv.ne')
  have hsum : ws.sum = v * U := by
    unfold U
    rw [← hds, sum_toFinset_of_nodup hnd]
    simpa only [List.map_id, ws, id_eq] using List.sum_map_mul_left ds id v
  have hc := cover_of_fresh_prefixGapBound hcover hws hfresh (hgap.scale v) hscaled
  rw [hsum] at hc
  have hnot : m ∉ m.properDivisors ∪ ws.toFinset := by
    intro h
    rcases Finset.mem_union.mp h with h | h
    · exact Nat.self_notMem_properDivisors h
    · obtain ⟨e, _, he⟩ := hval h
      exact hvnot ⟨e, he⟩
  have hmore := subsetSumIntervalInsert hnot hc (by omega : C + m ≤ T + v * U - C + 1)
  have hsub : insert m (m.properDivisors ∪ ws.toFinset) ⊆ n.properDivisors := by
    have hmlt : m < n := by
      rw [hn]
      simpa only [mul_one] using Nat.mul_lt_mul_of_pos_left hp.one_lt hm
    have hmdvd : m ∣ n := hn ▸ dvd_mul_right m p
    intro d hd
    rcases Finset.mem_insert.mp hd with rfl | hd
    · exact Nat.mem_properDivisors.mpr ⟨hmdvd, hmlt⟩
    rcases Finset.mem_union.mp hd with hd | hd
    · exact Nat.mem_properDivisors.mpr
        ⟨(Nat.mem_properDivisors.mp hd).1.trans hmdvd, (Nat.mem_properDivisors.mp hd).2.trans hmlt⟩
    · obtain ⟨e, he, rfl⟩ := hval hd
      obtain ⟨hdvd, hlt⟩ := Nat.mem_properDivisors.mp he
      change v * e ∈ (u * v).properDivisors
      rw [mul_comm u v]
      exact Nat.mem_properDivisors.mpr ⟨mul_dvd_mul_left v hdvd, Nat.mul_lt_mul_of_pos_left hlt hv⟩
  have htotal : (∑ d ∈ n.properDivisors, d) = T + v * U + m :=
    sumProperDivisors_raise_coprime_prime_power (a := a) hp hpu
  rw [htotal, show T + v * U + m - C = T + v * U - C + m by omega]
  exact cover_mono hsub hmore

private theorem mul_sumProperDivisors_le_raise_coprime_prime_power {u p a : ℕ}
    (hp : p.Prime) (hpu : ¬ p ∣ u) :
    p * (∑ d ∈ (u * p ^ a).properDivisors, d) ≤ (∑ d ∈ (u * p ^ (a + 1)).properDivisors, d) := by
  have h : (∑ d ∈ (u * p ^ (a + 1)).divisors, d) =
      p * (∑ d ∈ (u * p ^ a).divisors, d) + ∑ d ∈ u.divisors, d := by
    rw [sumDivisors_coprime_prime_power hp hpu (a + 1), sumDivisors_coprime_prime_power hp hpu a,
      geom_sum_succ, Nat.mul_add, Nat.mul_one, mul_left_comm]
  have hm : u * p ^ (a + 1) = p * (u * p ^ a) := by
    rw [pow_succ]
    ac_rfl
  rw [Nat.sum_divisors_eq_sum_properDivisors_add_self (n := u * p ^ (a + 1)),
    Nat.sum_divisors_eq_sum_properDivisors_add_self (n := u * p ^ a), Nat.mul_add] at h
  conv at h =>
    lhs
    arg 2
    rw [hm]
  omega

theorem cover_raise_coprime_prime_power_add {u p a C G : ℕ} {ds : List ℕ}
    (hu : 0 < u) (hp : p.Prime) (hpu : ¬ p ∣ u) (hC : 0 < C) (hnd : ds.Nodup)
    (hds : ds.toFinset = u.properDivisors) (hgap : PrefixGapBound G ds) :
    let m := u * p ^ a
    let v := p ^ (a + 1)
    let T := ∑ d ∈ m.properDivisors, d
    let U := ∑ d ∈ u.properDivisors, d
    Covered m.properDivisors C (T - C) →
    v * G + 2 * C ≤ T + 1 →
    m + 2 * C ≤ T + v * U + 1 →
    ∀ j : ℕ, let n := u * p ^ (a + j)
      Covered n.properDivisors C ((∑ d ∈ n.properDivisors, d) - C) := by
  intro m v T U hcover hscaled hlast j
  let M (b : ℕ) := u * p ^ b
  let V (b : ℕ) := p ^ (b + 1)
  let S (b : ℕ) := ∑ d ∈ (M b).properDivisors, d
  have hpush {x y : ℕ} (h : x + 2 * C ≤ y + 1) :
      p * x + 2 * C ≤ p * y + 1 := by
    have hm := Nat.mul_le_mul_left p (show x + (2 * C - 1) ≤ y by omega)
    rw [Nat.mul_add] at hm
    have hl := Nat.le_mul_of_pos_left (2 * C - 1) hp.pos
    omega
  have hstep (b : ℕ) (hc : Covered (M b).properDivisors C (S b - C))
      (hs : V b * G + 2 * C ≤ S b + 1) (hl : M b + 2 * C ≤ S b + V b * U + 1) :
      Covered (M (b + 1)).properDivisors C (S (b + 1) - C) ∧
      V (b + 1) * G + 2 * C ≤ S (b + 1) + 1 ∧
      M (b + 1) + 2 * C ≤ S (b + 1) + V (b + 1) * U + 1 := by
    have hM : M (b + 1) = p * M b := by
      unfold M
      rw [pow_succ]
      ac_rfl
    have hV : V (b + 1) = p * V b := by simp only [V, pow_succ']
    have hS : p * S b ≤ S (b + 1) := mul_sumProperDivisors_le_raise_coprime_prime_power hp hpu
    refine ⟨cover_raise_coprime_prime_power (a := b) hu hp hpu hnd hds hgap hc hs hl, ?_, ?_⟩
    · rw [hV, mul_assoc]
      exact (hpush hs).trans (Nat.add_le_add_right hS 1)
    · rw [hM, hV, mul_assoc p (V b) U]
      have hh := hpush hl
      rw [Nat.mul_add] at hh
      exact hh.trans (Nat.add_le_add_right (Nat.add_le_add_right hS _) 1)
  have hall (i : ℕ) : Covered (M (a + i)).properDivisors C (S (a + i) - C) ∧
      V (a + i) * G + 2 * C ≤ S (a + i) + 1 ∧
      M (a + i) + 2 * C ≤ S (a + i) + V (a + i) * U + 1 := by
    induction i with
    | zero => exact ⟨hcover, hscaled, hlast⟩
    | succ i ih => exact hstep (a + i) ih.1 ih.2.1 ih.2.2
  exact (hall j).1

end OddWeirdSubproblems

namespace OddWeirdSubproblems

open Finset

def GapUpTo (n g : ℕ) : Prop :=
  ∀ d ∈ n.properDivisors, d ≤ g + ∑ x ∈ n.properDivisors.filter (· < d), x

instance (n g : ℕ) : Decidable (GapUpTo n g) := by
  unfold GapUpTo
  infer_instance

private theorem sum_filtered_toFinset_eq_listSum {ds : List ℕ} (hnd : ds.Nodup) (d : ℕ) :
    (∑ x ∈ ds.toFinset.filter (· < d), x) = (ds.filter (fun x => decide (x < d))).sum := by
  rw [← sum_toFinset_of_nodup (hnd.filter (fun x => decide (x < d))), List.toFinset_filter]
  simp

private theorem prefixGapBound_of_sortedLT {ds : List ℕ} {g : ℕ} (hs : ds.SortedLT)
    (hg : ∀ d ∈ ds, d ≤ g + (ds.filter (fun x => decide (x < d))).sum) :
    PrefixGapBound g ds := by
  induction ds generalizing g with
  | nil => trivial
  | cons w ds ih =>
    obtain ⟨hsmall, htail⟩ := List.pairwise_cons.mp hs.pairwise
    refine ⟨?_, ih htail.sortedLT ?_⟩
    · have hnil : ds.filter (fun d => decide (d < w)) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro d hd
        simpa only [decide_eq_true_eq] using not_lt_of_gt (hsmall d hd)
      have hw := hg w List.mem_cons_self
      simpa [List.filter_cons, hnil] using hw
    · intro d hd
      have hh := hg d (List.mem_cons_of_mem _ hd)
      simpa [List.filter_cons, hsmall d hd, Nat.add_assoc] using hh

theorem GapUpTo.prefixGapBound_sort {n g : ℕ} (hg : GapUpTo n g) :
    PrefixGapBound g n.properDivisors.sort := by
  let ds := n.properDivisors.sort
  have hd : ds.toFinset = n.properDivisors := Finset.sort_toFinset _ _
  apply prefixGapBound_of_sortedLT (Finset.sortedLT_sort n.properDivisors)
  intro d hmem
  rw [← sum_filtered_toFinset_eq_listSum (Finset.sort_nodup _ _) d, hd]
  exact hg d (hd ▸ List.mem_toFinset.mpr hmem)

end OddWeirdSubproblems

namespace OddWeirdSubproblems

open Finset

def HasSubsetSum (D : Finset ℕ) (x : ℕ) : Prop := ∃ t ⊆ D, ∑ d ∈ t, d = x

def DenseLowSums (D : Finset ℕ) (C G : ℕ) : Prop :=
  ∀ j, j + G ≤ C → ∃ x, j ≤ x ∧ x < j + G ∧ HasSubsetSum D x

theorem DenseLowSums.mono {D E : Finset ℕ} {C G : ℕ} (h : DenseLowSums D C G)
    (hsub : D ⊆ E) : DenseLowSums E C G := by
  intro j hj
  obtain ⟨x, hx, hy, t, ht, hs⟩ := h j hj
  exact ⟨x, hx, hy, t, ht.trans hsub, hs⟩

theorem gapUpTo_of_central_and_low {n C G : ℕ}
    (hG : 0 < G) (hC : 2 * C ≤ ∑ d ∈ n.properDivisors, d)
    (hcovered : Covered n.properDivisors C ((∑ d ∈ n.properDivisors, d) - C))
    (hlow : DenseLowSums n.properDivisors C G) : GapUpTo n G := by
  intro d hd
  let D := n.properDivisors
  let T := ∑ v ∈ D, v
  let S := ∑ v ∈ D.filter (· < d), v
  change d ≤ G + S
  by_contra! hgap
  have hdT : d ≤ T := single_le_sum (f := fun x : ℕ => x) (fun _ _ => Nat.zero_le _) hd
  have hC' : 2 * C ≤ T := hC
  have hgap' : S + G < d := by omega
  obtain ⟨x, hx, hx', t, hsub, hsum⟩ : ∃ x, S < x ∧ x ≤ S + G ∧ HasSubsetSum D x := by
    by_cases hS : S < C
    · by_cases hspace : S + 1 + G ≤ C
      · obtain ⟨x, hx, hx', hp⟩ := hlow (S + 1) hspace
        exact ⟨x, by omega, by omega, hp⟩
      · have hc := hcovered C le_rfl (by omega : C ≤ T - C)
        exact ⟨C, hS, by omega, hc⟩
    · by_cases hS' : S < T - C
      · have hc := hcovered (S + 1) (by omega) (by omega : S + 1 ≤ T - C)
        exact ⟨S + 1, by omega, by omega, hc⟩
      · let j := T - (S + G)
        have hj : j + G ≤ C := by dsimp [j]; omega
        obtain ⟨z, hz, hz', t, ht, hs⟩ := hlow j hj
        have ht' := sum_sdiff (f := fun v : ℕ => v) ht
        change (∑ v ∈ D \ t, v) + (∑ v ∈ t, v) = T at ht'
        refine ⟨T - z, ?_, ?_, D \ t, sdiff_subset, ?_⟩
        · dsimp [j] at hz'
          omega
        · dsimp [j] at hz
          omega
        · omega
  have hsmall : t ⊆ D.filter (· < d) := by
    intro v hv
    refine Finset.mem_filter.mpr ⟨hsub hv, ?_⟩
    have hle : v ≤ ∑ k ∈ t, k := single_le_sum (f := fun k : ℕ => k) (fun _ _ => Nat.zero_le _) hv
    omega
  have hle : (∑ v ∈ t, v) ≤ S := sum_le_sum_of_subset hsmall
  omega

private def spreadLowBits : ℕ → ℕ → ℕ
  | 0, _ => 0
  | g + 1, bits => bits ||| (spreadLowBits g bits >>> 1)

private theorem spreadLowBits_sound {g bits j : ℕ}
    (h : (spreadLowBits g bits).testBit j = true) :
    ∃ i < g, bits.testBit (j + i) = true := by
  induction g generalizing j with
  | zero => simp [spreadLowBits] at h
  | succ g ih =>
    simp only [spreadLowBits, Nat.testBit_or, Nat.testBit_shiftRight, Bool.or_eq_true] at h
    rcases h with h | h
    · exact ⟨0, Nat.zero_lt_succ _, by simpa using h⟩
    · obtain ⟨i, hi, hbit⟩ := ih h
      refine ⟨i + 1, by omega, ?_⟩
      rw [show j + (i + 1) = 1 + j + i by omega]
      exact hbit

def lowDensityOk (ds : List ℕ) (C G : ℕ) : Bool :=
  let mask := 2 ^ (C + 1 - G) - 1
  decide ((spreadLowBits G (subsetBits ds) &&& mask) = mask)

theorem lowDensityOk_sound {ds : List ℕ} {C G : ℕ} (hn : ds.Nodup)
    (h : lowDensityOk ds C G = true) : DenseLowSums ds.toFinset C G := by
  intro j hj
  simp only [lowDensityOk, decide_eq_true_eq] at h
  have hbit := congrArg (fun bits : ℕ => bits.testBit j) h
  have hj' : j < C + 1 - G := by omega
  simp only [Nat.testBit_and, Nat.testBit_two_pow_sub_one, decide_eq_true hj', Bool.and_true] at hbit
  obtain ⟨i, hi, hsum⟩ := spreadLowBits_sound hbit
  exact ⟨j + i, by omega, by omega, testBit_subsetBits hn hsum⟩

def lowModulusOk (ds : List ℕ) (C M : ℕ) : Bool :=
  let bits := subsetBits ds
  (List.range C).all (fun i => !(decide (M ∣ i)) || bits.testBit i)

theorem lowModulusOk_sound {ds : List ℕ} {C M : ℕ} (hn : ds.Nodup)
    (h : lowModulusOk ds C M = true) : ∀ i < C, M ∣ i → HasSubsetSum ds.toFinset i := by
  intro i hi hd
  simp only [lowModulusOk, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    Bool.not_eq_true', decide_eq_false_iff_not] at h
  exact testBit_subsetBits hn ((h i hi).resolve_left fun hno => hno hd)

theorem pseudoperfect_of_central_and_modulus {n C M : ℕ}
    (hA : n.Abundant) (hc : C ≤ n)
    (hcover : Covered n.properDivisors C ((∑ d ∈ n.properDivisors, d) - C))
    (hsmall : ∀ x < C, M ∣ x → HasSubsetSum n.properDivisors x)
    (hm : M ∣ 2 * n) (hs : M ∣ ∑ d ∈ n.divisors, d) : n.Pseudoperfect := by
  let T := ∑ d ∈ n.properDivisors, d
  let excess := T - n
  have ha : n < T := hA
  have heq := Nat.sum_divisors_eq_sum_properDivisors_add_self (n := n)
  change (∑ d ∈ n.divisors, d) = T + n at heq
  have hdvd : M ∣ excess := by
    have hd := Nat.dvd_sub hs hm
    rwa [heq, show T + n - 2 * n = excess by dsimp [excess]; omega] at hd
  have hwitness : HasSubsetSum n.properDivisors excess := by
    by_cases h : excess < C
    · exact hsmall excess h hdvd
    · exact hcover excess (by omega) (by dsimp [excess]; omega : excess ≤ T - C)
  obtain ⟨t, ht, hsum⟩ := hwitness
  refine ⟨hA.pos, n.properDivisors \ t, sdiff_subset, ?_⟩
  have hdiff := sum_sdiff (f := fun v : ℕ => v) ht
  change (∑ v ∈ n.properDivisors \ t, v) + (∑ v ∈ t, v) = T at hdiff
  dsimp [excess] at hsum
  omega

end OddWeirdSubproblems

namespace OddWeirdSubproblems

open Finset

theorem cover_of_fresh_finset_steps {D E : Finset ℕ} {C T : ℕ}
    (hcover : Covered D C (T - C)) (hdis : Disjoint D E)
    (hstep : ∀ d ∈ E, d + 2 * C ≤ T + (∑ x ∈ E.filter (· < d), x) + 1) :
    Covered (D ∪ E) C (T + (∑ x ∈ E, x) - C) := by
  induction E using Finset.induction_on_max with
  | empty => simpa using hcover
  | insert d E hlt ih =>
    have hnd : d ∉ E := fun hd => (lt_irrefl d) (hlt d hd)
    have hfilter (x : ℕ) (hx : x ≤ d) : (insert d E).filter (· < x) = E.filter (· < x) := by
      rw [Finset.filter_insert, if_neg (not_lt_of_ge hx)]
    have hc := ih (hdis.mono_right (Finset.subset_insert _ _)) (fun x hx => by
      have h := hstep x (Finset.mem_insert_of_mem hx)
      rwa [hfilter x (hlt x hx).le] at h)
    have hb := hstep d (Finset.mem_insert_self _ _)
    rw [hfilter d le_rfl, Finset.filter_true_of_mem hlt] at hb
    have hnot : d ∉ D ∪ E := by
      have hdD : d ∉ D := fun hd =>
        (Finset.disjoint_left.mp hdis) hd (Finset.mem_insert_self _ _)
      simp [hdD, hnd]
    have hc' := subsetSumIntervalInsert hnot hc (by omega : C + d ≤ T + (∑ x ∈ E, x) - C + 1)
    rw [Finset.sum_insert hnd, Finset.union_insert]
    rw [show T + (d + ∑ x ∈ E, x) - C = T + (∑ x ∈ E, x) - C + d by omega]
    exact hc'

theorem cover_raise_existing_prime {u q a C G : ℕ}
    (hu : 0 < u) (hq : q.Prime) (hqu : ¬ q ∣ u) (ha : 0 < a) :
    let n := u * q ^ a
    let T := ∑ d ∈ n.properDivisors, d
    GapUpTo n G → Covered n.properDivisors C (T - C) →
    q * G + 2 * C ≤ (∑ d ∈ u.divisors, d) + 1 →
    Covered (n * q).properDivisors C ((∑ d ∈ (n * q).properDivisors, d) - C) := by
  intro n T hgap hcover hbound
  let D := n.properDivisors
  let E := (n * q).properDivisors \ D
  have hn : 0 < n := Nat.mul_pos hu (pow_pos hq.pos a)
  have hnlt : n < n * q := by
    simpa only [mul_one] using Nat.mul_lt_mul_of_pos_left hq.one_lt hn
  have hDn : D ⊆ (n * q).properDivisors := by
    intro d hd
    obtain ⟨hdiv, hlt⟩ := Nat.mem_properDivisors.mp hd
    exact Nat.mem_properDivisors.mpr ⟨hdiv.trans (dvd_mul_right n q), hlt.trans hnlt⟩
  have hDis : Disjoint D E := Finset.sdiff_disjoint.symm
  have hUnion : D ∪ E = (n * q).properDivisors := by
    exact (Finset.union_comm D E).trans (Finset.sdiff_union_of_subset hDn)
  have hqn : q ∣ n := by
    have hqa : q ∣ q ^ a := by
      simpa only [pow_one] using pow_dvd_pow q ha
    exact dvd_mul_of_dvd_right hqa u
  have hU : u.divisors ⊆ D := by
    have hpow : 1 < q ^ a := by
      simpa only [pow_zero] using pow_lt_pow_right₀ hq.one_lt ha
    have hult : u < n := by
      simpa only [mul_one] using Nat.mul_lt_mul_of_pos_left hpow hu
    intro d hd
    have hdu := Nat.dvd_of_mem_divisors hd
    exact Nat.mem_properDivisors.mpr
      ⟨hdu.trans (dvd_mul_right u (q ^ a)), (Nat.le_of_dvd hu hdu).trans_lt hult⟩
  have hstep (d : ℕ) (hd : d ∈ E) :
      d + 2 * C ≤ T + (∑ x ∈ E.filter (· < d), x) + 1 := by
    obtain ⟨hdnq, hdn⟩ := Finset.mem_sdiff.mp hd
    obtain ⟨hdiv, hlt⟩ := Nat.mem_properDivisors.mp hdnq
    have hqd : q ∣ d := by
      by_contra hnot
      have hcop := (hq.coprime_iff_not_dvd.mpr hnot).symm
      have hdiv' := hcop.dvd_of_dvd_mul_right hdiv
      have hdlt : d < n := lt_of_le_of_ne (Nat.le_of_dvd hn hdiv')
        (fun heq => hnot (heq.symm ▸ hqn))
      exact hdn (Nat.mem_properDivisors.mpr ⟨hdiv', hdlt⟩)
    obtain ⟨w, rfl⟩ := hqd
    have hw : w ∈ D := Nat.mem_properDivisors.mpr
      ⟨(Nat.mul_dvd_mul_iff_left hq.pos).mp (by simpa only [mul_comm n q] using hdiv),
        (Nat.mul_lt_mul_left hq.pos).mp (by simpa only [mul_comm n q] using hlt)⟩
    let I := (D.filter (· < w)).image (q * ·)
    have hscale : I ⊆ D ∪ E.filter (· < q * w) := by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨hyD, hyw⟩ := Finset.mem_filter.mp hy
      obtain ⟨hyd, hyn⟩ := Nat.mem_properDivisors.mp hyD
      by_cases hmem : q * y ∈ D
      · exact Finset.mem_union_left _ hmem
      · have hnew : q * y ∈ (n * q).properDivisors := by
          rw [mul_comm n q]
          exact Nat.mem_properDivisors.mpr ⟨mul_dvd_mul_left q hyd, Nat.mul_lt_mul_of_pos_left hyn hq.pos⟩
        exact Finset.mem_union_right _ (Finset.mem_filter.mpr
          ⟨Finset.mem_sdiff.mpr ⟨hnew, hmem⟩, Nat.mul_lt_mul_of_pos_left hyw hq.pos⟩)
    have hIU : Disjoint u.divisors I := by
      apply Finset.disjoint_left.mpr
      intro x hx hxI
      obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hxI
      exact hqu ((dvd_mul_right q y).trans (Nat.dvd_of_mem_divisors hx))
    have htot := Finset.sum_le_sum_of_subset (f := fun x : ℕ => x)
      (Finset.union_subset (hU.trans Finset.subset_union_left) hscale)
    rw [Finset.sum_union hIU, Finset.sum_union (hDis.mono_right (Finset.filter_subset _ _))] at htot
    have hgw := Nat.mul_le_mul_left q (hgap w hw)
    rw [Nat.mul_add] at hgw
    have hIsum : (∑ x ∈ I, x) = q * (∑ x ∈ D.filter (· < w), x) := by
      unfold I
      rw [Finset.sum_image (fun _ _ _ _ h => mul_left_cancel₀ hq.ne_zero h), ← Finset.mul_sum]
    change _ ≤ q * G + q * (∑ x ∈ D.filter (· < w), x) at hgw
    rw [← hIsum] at hgw
    change _ ≤ T + (∑ x ∈ E.filter (· < q * w), x) at htot
    omega
  have hf := cover_of_fresh_finset_steps hcover hDis hstep
  change Covered (D ∪ E) C (((∑ x ∈ D, x) + ∑ x ∈ E, x) - C) at hf
  rw [← Finset.sum_union hDis, hUnion] at hf
  exact hf

end OddWeirdSubproblems

namespace OddWeirdSubproblems

open Finset

private theorem properDivisorSubsetOfDvd {n m : ℕ} (hm : 0 < m) (h : n ∣ m) :
    n.properDivisors ⊆ m.properDivisors := by
  intro d hd
  obtain ⟨hdvd, hdlt⟩ := Nat.mem_properDivisors.mp hd
  exact Nat.mem_properDivisors.mpr ⟨hdvd.trans h, hdlt.trans_le (Nat.le_of_dvd hm h)⟩

theorem cover_mul_existing_prime_factors {u k C G : ℕ} (hu : 0 < u) (hk : 0 < k)
    (hG : 0 < G) (hC : 2 * C ≤ ∑ d ∈ u.properDivisors, d)
    (hcovered : Covered u.properDivisors C ((∑ d ∈ u.properDivisors, d) - C))
    (hlow : DenseLowSums u.properDivisors C G)
    (hprimes : ∀ q : ℕ, q.Prime → q ∣ k →
      q ∣ u ∧ q * G + 2 * C ≤ (∑ d ∈ (ordCompl[q] u).divisors, d) + 1) :
    Covered (u * k).properDivisors C ((∑ d ∈ (u * k).properDivisors, d) - C) := by
  revert hk hprimes
  induction k using induction_on_primes with
  | zero => omega
  | one =>
    intro _ _
    simpa using hcovered
  | prime_mul q k hq ih =>
    intro hkq hprimes
    have hk : 0 < k := Nat.pos_of_mul_pos_left hkq
    have hcov := ih hk (fun p hp hpk => hprimes p hp (dvd_mul_of_dvd_right hpk q))
    let n := u * k
    have hn : 0 < n := Nat.mul_pos hu hk
    have hun : u ∣ n := dvd_mul_right u k
    have hsub := properDivisorSubsetOfDvd hn hun
    have hgap : GapUpTo n G :=
      gapUpTo_of_central_and_low hG (hC.trans (Finset.sum_le_sum_of_subset hsub))
        hcov (hlow.mono hsub)
    obtain ⟨hqu, hbound⟩ := hprimes q hq (dvd_mul_right q k)
    let v := ordCompl[q] n
    have hv : 0 < v := Nat.ordCompl_pos q hn.ne'
    have hqv : ¬ q ∣ v := hq.coprime_iff_not_dvd.mp (Nat.coprime_ordCompl hq hn.ne')
    have hqn : q ∣ n := dvd_mul_of_dvd_left hqu k
    have ha : 0 < n.factorization q := hq.factorization_pos_of_dvd hn.ne' hqn
    have hvn : v * q ^ n.factorization q = n :=
      (mul_comm _ _).trans (Nat.ordProj_mul_ordCompl_eq_self n q)
    have hsubv : (ordCompl[q] u).divisors ⊆ v.divisors :=
      Nat.divisors_subset_of_dvd hv.ne' (Nat.ordCompl_dvd_ordCompl_of_dvd hun q)
    have hbudget : q * G + 2 * C ≤ (∑ d ∈ v.divisors, d) + 1 :=
      hbound.trans (Nat.add_le_add_right (Finset.sum_le_sum_of_subset hsubv) 1)
    have hlift := cover_raise_existing_prime (C := C) (G := G) hv hq hqv ha
      (by simpa only [hvn] using hgap) (by simpa only [hvn] using hcov) hbudget
    simpa only [hvn, n, Nat.mul_assoc, mul_comm k q] using hlift

end OddWeirdSubproblems

namespace OddWeirdSubproblems

theorem freshPrime_deficiency_lt {u s t r : ℕ} (hu : 0 < u) (ht : 1 < t)
    (hs : s ≤ 2 * u)
    (hratio : 2 < ((s : ℚ) / u) * ((t : ℚ) / ((t : ℚ) - 1)) ^ r) :
    (2 * u - s) * t < 2 * r * u := by
  have huq : (0 : ℚ) < u := by exact_mod_cast hu
  have htq : (1 : ℚ) < t := by exact_mod_cast ht
  have htq0 : (0 : ℚ) < t := zero_lt_one.trans htq
  have hz : (0 : ℚ) < ((t : ℚ) - 1) / t := div_pos (sub_pos.mpr htq) htq0
  have hrecip : ((t : ℚ) / ((t : ℚ) - 1)) ^ r =
      ((((t : ℚ) - 1) / t) ^ r)⁻¹ := by
    rw [← inv_pow, inv_div]
  rw [hrecip, ← div_eq_mul_inv, lt_div_iff₀ (pow_pos hz r)] at hratio
  have hzsub : ((t : ℚ) - 1) / t - 1 = -(1 / (t : ℚ)) := by
    rw [sub_div, div_self htq0.ne', sub_sub_cancel_left]
  have hbern := one_add_mul_sub_le_pow ((by norm_num : (-1 : ℚ) ≤ 0).trans hz.le) r
  rw [hzsub, mul_neg, ← sub_eq_add_neg, mul_one_div] at hbern
  have hmul := mul_lt_mul_of_pos_right
    ((lt_div_iff₀ huq).mp ((mul_le_mul_of_nonneg_left hbern (by norm_num : (0 : ℚ) ≤ 2)).trans_lt
      hratio)) htq0
  have hclear : 2 * (1 - (r : ℚ) / t) * (u : ℚ) * (t : ℚ) =
      2 * (u : ℚ) * (t : ℚ) - 2 * (r : ℚ) * (u : ℚ) := by
    calc
      _ = 2 * (u : ℚ) * ((1 - (r : ℚ) / t) * (t : ℚ)) := by ring
      _ = _ := by rw [sub_mul, one_mul, div_mul_cancel₀ _ htq0.ne']; ring
  rw [hclear] at hmul
  have hq : (2 * (u : ℚ) - s) * (t : ℚ) < 2 * (r : ℚ) * (u : ℚ) := by
    nlinarith only [hmul]
  exact_mod_cast (show (((2 * u - s : ℕ) : ℚ) * (t : ℚ)) < 2 * (r : ℚ) * (u : ℚ) by
    simpa only [Nat.cast_sub hs, Nat.cast_mul, Nat.cast_ofNat] using hq)

theorem freshPrimeBudget_of_ratio {u s t P r : ℕ} (hu : 0 < u) (ht : 1 < t)
    (hus : u ≤ s) (hs : s ≤ 2 * u) (hP : 2 * r ≤ P) (hPt : P ≤ t)
    (hratio : 2 < ((s : ℚ) / u) * ((t : ℚ) / ((t : ℚ) - 1)) ^ r) :
    (2 * u - s) * t < 2 * r * u ∧ (P - 2 * r) * u < P * (s - u) := by
  have htbudget := freshPrime_deficiency_lt hu ht hs hratio
  have hPbudget := (Nat.mul_le_mul_left (2 * u - s) hPt).trans_lt htbudget
  have hsum : 2 * u - s + (s - u) = u := by omega
  have h₁ := congrArg (fun n : ℕ => P * n) hsum
  have h₂ := congrArg (fun n : ℕ => n * u) (Nat.sub_add_cancel hP)
  simp only [Nat.mul_add, Nat.add_mul] at h₁ h₂
  rw [Nat.mul_comm (2 * u - s) P] at hPbudget
  exact ⟨htbudget, by omega⟩

theorem freshPrimeBudget {u t P r : ℕ} (hu : 0 < u) (hdef : u.Deficient)
    (ht : 1 < t) (hP : 2 * r ≤ P) (hPt : P ≤ t)
    (hratio : 2 < u.abundancyIndex * ((t : ℚ) / ((t : ℚ) - 1)) ^ r) :
    (2 * u - ∑ d ∈ u.divisors, d) * t < 2 * r * u ∧
      (P - 2 * r) * u < P * (∑ d ∈ u.properDivisors, d) := by
  have hsum : (∑ d ∈ u.divisors, d) = (∑ d ∈ u.properDivisors, d) + u :=
    Nat.sum_divisors_eq_sum_properDivisors_add_self
  have hus : u ≤ ∑ d ∈ u.divisors, d := by omega
  have hs : (∑ d ∈ u.divisors, d) ≤ 2 * u := by
    unfold Nat.Deficient at hdef
    omega
  have h := freshPrimeBudget_of_ratio hu ht hus hs hP hPt hratio
  simpa only [hsum, Nat.add_sub_cancel_right] using h

theorem abundancyIndex_le_pow_of_fresh_primes {v t r : ℕ} (hv : 0 < v) (ht : 1 < t)
    (hcard : v.primeFactors.card ≤ r) (hmin : ∀ p ∈ v.primeFactors, t ≤ p) :
    v.abundancyIndex ≤ ((t : ℚ) / ((t : ℚ) - 1)) ^ r := by
  let localIndex (p : ℕ) : ℚ :=
    (∑ i ∈ Finset.range (v.factorization p + 1), (p : ℚ) ^ i) /
      (p : ℚ) ^ v.factorization p
  have hindex : v.abundancyIndex = ∏ p ∈ v.primeFactors, localIndex p := by
    have hsigma := ArithmeticFunction.sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul
      (k := 1) hv.ne'
    rw [ArithmeticFunction.sigma_one_apply] at hsigma
    simp only [mul_one] at hsigma
    rw [Nat.abundancyIndex, hsigma]
    conv_lhs => arg 2; rw [Nat.prod_primeFactors_pow_factorization hv.ne']
    simp only [localIndex, Nat.cast_prod, Nat.cast_sum, Nat.cast_pow, ← Finset.prod_div_distrib]
  have htq : (1 : ℚ) < t := by exact_mod_cast ht
  have hone : (1 : ℚ) ≤ (t : ℚ) / ((t : ℚ) - 1) := by
    exact (one_le_div (sub_pos.mpr htq)).mpr (by linarith)
  rw [hindex]
  refine (Finset.prod_le_prod (g := fun _ => (t : ℚ) / ((t : ℚ) - 1))
    (fun p _ => ?_) (fun p hp => ?_)).trans ?_
  · unfold localIndex
    exact div_nonneg (Finset.sum_nonneg fun _ _ => pow_nonneg (Nat.cast_nonneg p) _)
      (pow_nonneg (Nat.cast_nonneg p) _)
  · have hpq : (t : ℚ) ≤ p := by exact_mod_cast hmin p hp
    have hpq1 := htq.trans_le hpq
    calc
      localIndex p ≤ (p : ℚ) / ((p : ℚ) - 1) := by
        unfold localIndex
        rw [div_le_div_iff₀ (pow_pos (show (0 : ℚ) < p by linarith) _) (sub_pos.mpr hpq1),
          geom_sum_mul, pow_succ]
        linarith
      _ ≤ (t : ℚ) / ((t : ℚ) - 1) := by
        rw [div_le_div_iff₀ (sub_pos.mpr hpq1) (sub_pos.mpr htq)]
        nlinarith
  · rw [Finset.prod_const]
    exact pow_le_pow_right₀ hone hcard

theorem freshPrimeBudget_of_coprime_completion {u v t P r : ℕ}
    (hdef : u.Deficient) (hcop : u.Coprime v) (habund : (u * v).Abundant)
    (ht : 1 < t) (hP : 2 * r ≤ P) (hPt : P ≤ t)
    (hcard : v.primeFactors.card ≤ r) (hmin : ∀ p ∈ v.primeFactors, t ≤ p) :
    (2 * u - ∑ d ∈ u.divisors, d) * t < 2 * r * u ∧
      (P - 2 * r) * u < P * (∑ d ∈ u.properDivisors, d) := by
  have hu := Nat.pos_of_mul_pos_right habund.pos
  have hv := Nat.pos_of_mul_pos_left habund.pos
  have hidx := Nat.abundant_iff_two_lt_abundancyIndex.mp habund
  have hmul : (u * v).abundancyIndex = u.abundancyIndex * v.abundancyIndex := by
    simp only [Nat.abundancyIndex, hcop.sum_divisors_mul, Nat.cast_mul, div_mul_div_comm]
  rw [hmul] at hidx
  have huindex : 0 ≤ u.abundancyIndex := by unfold Nat.abundancyIndex; positivity
  exact freshPrimeBudget hu hdef ht hP hPt
    (hidx.trans_le (mul_le_mul_of_nonneg_left
      (abundancyIndex_le_pow_of_fresh_primes hv ht hcard hmin) huindex))

end OddWeirdSubproblems

namespace OddWeirdSubproblems

open Finset

theorem coprime_coordinateProduct {p : ℕ} {xs : Coordinates} (hp : p.Prime)
    (hv : ∀ x ∈ xs, x.1.Prime) (hf : ∀ x ∈ xs, p ≠ x.1) : p.Coprime (number xs) := by
  apply Nat.coprime_list_prod_right_iff.mpr
  intro w hw
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hw
  rw [← pow_one p]
  exact Nat.coprime_pow_primes _ _ hp (hv x hx) (hf x hx)

theorem erase_coordinate {fs : Coordinates} {p e : ℕ}
    (hv : PrimeCoordinates fs) (hm : (p, e) ∈ fs) :
    let rest := fs.erase (p, e)
    PrimeCoordinates rest ∧ p.Prime ∧ ¬p ∣ number rest ∧ number fs = number rest * p ^ e := by
  intro rest
  have hrest : PrimeCoordinates rest :=
    ⟨fun x hx => hv.1 x (List.erase_subset hx), hv.2.erase (p, e)⟩
  have hp := hv.1 (p, e) hm
  have hpw : (fs.map Prod.fst).Pairwise (· ≠ ·) :=
    List.pairwise_map.mpr (hv.2.imp fun h => Nat.ne_of_lt h)
  have hperm := List.perm_cons_erase hm
  have hn : p ∉ rest.map Prod.fst := by
    have hd := (hperm.map Prod.fst).nodup_iff.mp hpw
    exact (List.nodup_cons.mp hd).1
  have hfresh (x : ℕ × ℕ) (hx : x ∈ rest) : p ≠ x.1 := by
    intro he
    apply hn
    rw [he]
    exact List.mem_map_of_mem hx
  refine ⟨hrest, hp, hp.coprime_iff_not_dvd.mp (coprime_coordinateProduct hp hrest.1 hfresh), ?_⟩
  have hnum := (hperm.map (fun x => x.1 ^ x.2)).prod_nat
  simpa [number, Nat.mul_comm] using hnum

theorem cover_proper_central {n lo hi : ℕ}
    (h : Covered n.properDivisors lo hi) (hlo : lo ≤ hi)
    (hhi : hi ≤ ∑ d ∈ n.properDivisors, d)
    (hmid : (∑ d ∈ n.properDivisors, d) / 2 ≤ hi) :
    Covered n.properDivisors lo ((∑ d ∈ n.properDivisors, d) - lo) := by
  intro x hx hy
  by_cases hx' : x ≤ hi
  · exact h x hx hx'
  · exact subsetSumIntervalReflect h hlo hhi x (by omega) hy

structure CentralCoverData where
  seed : List ℕ
  growth : List ℕ
  low : ℕ
  seedHigh : ℕ

def CentralCoverData.ok (data : CentralCoverData) (n total : ℕ) : Bool :=
  let high := data.seedHigh + data.growth.sum
  divisorListOk n (data.seed ++ data.growth) &&
    bitIntervalOk data.seed data.low data.seedHigh &&
    growIntervalOk data.low data.seedHigh data.growth &&
    decide (data.low ≤ high ∧ high ≤ total ∧ total / 2 ≤ high)

theorem CentralCoverData.sound {data : CentralCoverData} {n total : ℕ}
    (hsum : ∑ d ∈ n.properDivisors, d = total) (h : data.ok n total = true) :
    Covered n.properDivisors data.low (total - data.low) := by
  simp only [CentralCoverData.ok, Bool.and_eq_true, decide_eq_true_eq] at h
  rw [← hsum]
  exact cover_proper_central (cover_of_validated_growth h.1.1.1 h.1.1.2 h.1.2)
    h.2.1 (hsum.symm ▸ h.2.2.1) (hsum.symm ▸ h.2.2.2)

end OddWeirdSubproblems

namespace OddWeirdSubproblems

open Finset

private theorem affine_mul_bound_of_le {base u a b c : ℕ}
    (hbase : 0 < base) (hu : base ≤ u) (h : a * base + c ≤ b * base) :
    a * u + c ≤ b * u := by
  have hab : a ≤ b := (Nat.mul_le_mul_right_iff hbase).mp (le_trans (Nat.le_add_right _ _) h)
  have hd := Nat.mul_le_mul_left (b - a) hu
  have hb := Nat.sub_add_cancel hab
  have hb₁ := congrArg (· * base) hb
  have hb₂ := congrArg (· * u) hb
  rw [Nat.add_mul] at hb₁ hb₂
  omega

def FreshIntervalBudget (base P r C G M : ℕ) : Prop :=
  let R := base * (P - 2 * r)
  let Z := base * P
  let K := (2 * C - 1) * P
  2 * r * G * Z + M * K ≤ M * R ∧ Z + K ≤ (P + 1) * R

instance (base P r C G M : ℕ) : Decidable (FreshIntervalBudget base P r C G M) := by
  unfold FreshIntervalBudget
  infer_instance

theorem FreshIntervalBudget.lift {base P r C G M u v p a : ℕ}
    (hbudget : FreshIntervalBudget base P r C G M) (hbase : 0 < base) (hle : base ≤ u)
    (hC : 0 < C) (hP : 2 * r < P) (hPt : P ≤ p)
    (hp : p.Prime) (hpu : ¬ p ∣ u) (hdef : u.Deficient)
    (hcop : u.Coprime v) (hA : (u * v).Abundant)
    (hcard : v.primeFactors.card ≤ r) (hmin : ∀ q ∈ v.primeFactors, p ≤ q)
    (hM : M ∣ 2 * u - ∑ d ∈ u.divisors, d) (hgap : GapUpTo u G)
    (hcover : Covered u.properDivisors C ((∑ d ∈ u.properDivisors, d) - C)) :
    Covered (u * p ^ a).properDivisors C ((∑ d ∈ (u * p ^ a).properDivisors, d) - C) := by
  let T := ∑ d ∈ u.properDivisors, d
  let delta := 2 * u - ∑ d ∈ u.divisors, d
  let k := 2 * C - 1
  have hu := hbase.trans_le hle
  have hp0 : 0 < P := Nat.zero_le _ |>.trans_lt hP
  have hT : T < u := hdef
  have hs := Nat.sum_divisors_eq_sum_properDivisors_add_self (n := u)
  have hdelta : 0 < delta := by dsimp [delta, T] at *; omega
  have hM0 : 0 < M := Nat.pos_of_dvd_of_pos hM hdelta
  have hMle := Nat.le_of_dvd hdelta hM
  have ⟨hpbound, hTbound⟩ :=
    freshPrimeBudget_of_coprime_completion hdef hcop hA hp.one_lt hP.le hPt hcard hmin
  change delta * p < 2 * r * u at hpbound
  change (P - 2 * r) * u < P * T at hTbound
  have ha₁ : (2 * r * G * P) * u + M * (k * P) ≤ (M * (P - 2 * r)) * u := by
    apply affine_mul_bound_of_le hbase hle
    simpa only [FreshIntervalBudget, k, Nat.mul_left_comm, Nat.mul_comm, Nat.mul_assoc] using hbudget.1
  have hb₁ : p * G + k ≤ T := by
    apply (Nat.mul_le_mul_right_iff (Nat.mul_pos hM0 hp0)).mp
    calc
      (p * G + k) * (M * P) ≤ (2 * r * G * P) * u + M * (k * P) := by
        have hm := Nat.mul_le_mul_right (G * P)
          ((Nat.mul_le_mul_right p hMle).trans hpbound.le)
        rw [Nat.add_mul]
        apply Nat.add_le_add
        · simpa only [Nat.mul_left_comm, Nat.mul_comm, Nat.mul_assoc] using hm
        · exact le_of_eq (by ac_rfl)
      _ ≤ (M * (P - 2 * r)) * u := ha₁
      _ ≤ T * (M * P) := by
        simpa only [Nat.mul_left_comm, Nat.mul_comm, Nat.mul_assoc] using
          Nat.mul_le_mul_left M hTbound.le
  have ha₂ : P * u + k * P ≤ ((P + 1) * (P - 2 * r)) * u := by
    apply affine_mul_bound_of_le hbase hle
    simpa only [FreshIntervalBudget, k, Nat.mul_left_comm, Nat.mul_comm, Nat.mul_assoc] using hbudget.2
  have hb₂ : u + k ≤ (p + 1) * T := by
    apply (Nat.mul_le_mul_right_iff hp0).mp
    calc
      (u + k) * P = P * u + k * P := by rw [Nat.add_mul, mul_comm u P]
      _ ≤ ((P + 1) * (P - 2 * r)) * u := ha₂
      _ ≤ ((P + 1) * T) * P := by
        simpa only [Nat.mul_left_comm, Nat.mul_comm, Nat.mul_assoc] using
          Nat.mul_le_mul_left (P + 1) hTbound.le
      _ ≤ ((p + 1) * T) * P := by
        exact Nat.mul_le_mul_right P (Nat.mul_le_mul_right T (Nat.succ_le_succ hPt))
  have ha := cover_raise_coprime_prime_power_add (a := 0) hu hp hpu hC
    (Finset.sort_nodup _ _) (Finset.sort_toFinset _ _) hgap.prefixGapBound_sort
  simp only [pow_zero, mul_one, zero_add, pow_one] at ha
  refine ha hcover (by dsimp [k] at hb₁; omega) ?_ a
  change u + 2 * C ≤ T + p * T + 1
  rw [Nat.add_mul, Nat.one_mul] at hb₂
  dsimp [k] at hb₂
  omega

theorem coordinatePrime_dvd_exists {p : ℕ} {ys : Coordinates} (hp : p.Prime)
    (hvalid : ∀ x ∈ ys, x.1.Prime) (hd : p ∣ number ys) : ∃ x ∈ ys, x.1 = p := by
  induction ys with
  | nil =>
    have h := Nat.dvd_one.mp (show p ∣ 1 by simpa [number] using hd)
    exact (hp.ne_one h).elim
  | cons y ys ih =>
    rw [number_cons] at hd
    rcases hp.dvd_mul.mp hd with h | h
    · rcases (Nat.dvd_prime (hvalid y (by simp))).mp (hp.dvd_of_dvd_pow h) with h | h
      · exact (hp.ne_one h).elim
      · exact ⟨y, by simp, h.symm⟩
    · obtain ⟨q, hq, he⟩ := ih (fun x hx => hvalid x (List.mem_cons_of_mem _ hx)) h
      exact ⟨q, List.mem_cons_of_mem _ hq, he⟩

theorem primeFactors_card_number_le {ys : Coordinates} (hv : ∀ x ∈ ys, x.1.Prime) :
    (number ys).primeFactors.card ≤ ys.length := by
  have hsub : (number ys).primeFactors ⊆ (ys.map Prod.fst).toFinset := by
    intro p hp
    obtain ⟨x, hx, he⟩ := coordinatePrime_dvd_exists
      (Nat.prime_of_mem_primeFactors hp) hv (Nat.dvd_of_mem_primeFactors hp)
    exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨x, hx, he⟩)
  exact (card_le_card hsub).trans (by simpa using List.toFinset_card_le (ys.map Prod.fst))

theorem properDivisors_subset_of_dvd {u v : ℕ} (hv : 0 < v) (huv : u ∣ v) :
    u.properDivisors ⊆ v.properDivisors := by
  intro d h
  obtain ⟨hd, hlt⟩ := Nat.mem_properDivisors.mp h
  exact Nat.mem_properDivisors.mpr ⟨hd.trans huv, hlt.trans_le (Nat.le_of_dvd hv huv)⟩

private theorem tailFits_mono_start {xs : Coordinates} {p q : ℕ} (hle : p ≤ q)
    (h : TailFits q xs) : TailFits p xs := by
  cases xs with
  | nil => trivial
  | cons x xs =>
    obtain ⟨u, e⟩ := x
    exact ⟨hle.trans h.1, h.2⟩

theorem cover_fresh_tail_with_lift {base P r C G M u : ℕ} {ys : Coordinates}
    (hbase : 0 < base) (hbu : base ≤ u) (hG : 0 < G)
    (lift : ∀ {x v p a}, base ≤ x → P ≤ p → p.Prime → ¬ p ∣ x → x.Deficient →
      x.Coprime v → (x * v).Abundant → v.primeFactors.card ≤ r →
      (∀ q ∈ v.primeFactors, p ≤ q) → M ∣ (2 * x - ∑ d ∈ x.divisors, d) →
      GapUpTo x G →
      Covered x.properDivisors C ((∑ d ∈ x.properDivisors, d) - C) →
      Covered (x * p ^ a).properDivisors C ((∑ d ∈ (x * p ^ a).properDivisors, d) - C))
    (hv : PrimeCoordinates ys) (htail : TailFits P ys) (hr : ys.length ≤ r)
    (hcop : u.Coprime (number ys))
    (hA : (u * number ys).Abundant)
    (hprim : ∀ d ∈ (u * number ys).properDivisors, d.Deficient)
    (hsigma : M ∣ ∑ d ∈ u.divisors, d) (h2u : M ∣ 2 * u)
    (hCT : 2 * C ≤ ∑ d ∈ u.properDivisors, d)
    (hlow : DenseLowSums u.properDivisors C G)
    (hcover : Covered u.properDivisors C ((∑ d ∈ u.properDivisors, d) - C)) :
    Covered (u * number ys).properDivisors C ((∑ d ∈ (u * number ys).properDivisors, d) - C) := by
  induction ys generalizing u with
  | nil => simpa [number] using hcover
  | cons y ys ih =>
    obtain ⟨p, e⟩ := y
    obtain ⟨hPt, _, hp, _, he, htail'⟩ := htail
    have hu : 0 < u := hbase.trans_le hbu
    have hv' : PrimeCoordinates ys :=
      ⟨fun x hx => hv.1 x (List.mem_cons_of_mem _ hx), (List.pairwise_cons.mp hv.2).2⟩
    have he' : 1 ≤ e := by omega
    have hnum : 1 < number ((p, e) :: ys) := by
      rw [number_cons]
      have hw : p ≤ p ^ e := by simpa using Nat.pow_le_pow_right hp.pos he'
      exact (hp.one_lt.trans_le hw).trans_le (Nat.le_mul_of_pos_right _ (number_pos hv'.1))
    have hdef : u.Deficient := hprim u (Nat.mem_properDivisors.mpr
      ⟨dvd_mul_right _ _, by simpa using Nat.mul_lt_mul_of_pos_left hnum hu⟩)
    have hM := Nat.dvd_sub h2u hsigma
    have hpmin (q : ℕ) (hq : q ∈ (number ((p, e) :: ys)).primeFactors) : p ≤ q := by
      obtain ⟨x, hx, hxe⟩ := coordinatePrime_dvd_exists (Nat.prime_of_mem_primeFactors hq)
        hv.1 (Nat.dvd_of_mem_primeFactors hq)
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hxe.symm ▸ le_rfl
      · exact hxe ▸ ((List.pairwise_cons.mp hv.2).1 x hx).le
    have hpu : u.Coprime p := by
      apply hcop.of_dvd_right
      rw [number_cons]
      exact (dvd_pow_self p (by omega : e ≠ 0)).trans (dvd_mul_right _ _)
    have hc : Covered (u * p ^ e).properDivisors C
        ((∑ d ∈ (u * p ^ e).properDivisors, d) - C) :=
      lift hbu hPt hp (hp.coprime_iff_not_dvd.mp hpu.symm) hdef
        hcop hA ((primeFactors_card_number_le hv.1).trans hr) hpmin hM
        (gapUpTo_of_central_and_low hG hCT hcover hlow) hcover
    let u' := u * p ^ e
    have hu' : 0 < u' := Nat.mul_pos hu (pow_pos hp.pos _)
    have hdiv : u ∣ u' := dvd_mul_right _ _
    have hsub := properDivisors_subset_of_dvd hu' hdiv
    have heq : u * number ((p, e) :: ys) = u' * number ys := by
      rw [number_cons, Nat.mul_assoc]
    rw [heq] at hA hprim ⊢
    apply ih (hbu.trans (Nat.le_of_dvd hu' hdiv)) hv' _ _ _ hA hprim _ _
      (hCT.trans (sum_le_sum_of_subset hsub)) (hlow.mono hsub) hc
    · exact tailFits_mono_start (show P ≤ p + 2 by omega) htail'
    · exact (Nat.le_succ _).trans hr
    · apply Nat.Coprime.mul_left
      · apply hcop.of_dvd_right
        rw [number_cons]
        exact dvd_mul_left _ _
      · apply Nat.Coprime.pow_left
        exact coprime_coordinateProduct hp hv'.1
          (fun x hx => ((List.pairwise_cons.mp hv.2).1 x hx).ne)
    · change M ∣ ∑ d ∈ (u * p ^ e).divisors, d
      rw [(hpu.pow_right e).sum_divisors_mul]
      exact hsigma.trans (dvd_mul_right _ _)
    · exact h2u.trans (by dsimp [u']; rw [← Nat.mul_assoc]; exact dvd_mul_right _ _)

theorem cover_fresh_tail {base P r C G M u : ℕ} {ys : Coordinates}
    (hbase : 0 < base) (hbu : base ≤ u) (hC : 0 < C) (hG : 0 < G)
    (hP : 2 * r < P) (hbudget : FreshIntervalBudget base P r C G M)
    (hv : PrimeCoordinates ys) (htail : TailFits P ys) (hr : ys.length ≤ r)
    (hcop : u.Coprime (number ys))
    (hA : (u * number ys).Abundant)
    (hprim : ∀ d ∈ (u * number ys).properDivisors, d.Deficient)
    (hsigma : M ∣ ∑ d ∈ u.divisors, d) (h2u : M ∣ 2 * u)
    (hCT : 2 * C ≤ ∑ d ∈ u.properDivisors, d)
    (hlow : DenseLowSums u.properDivisors C G)
    (hcover : Covered u.properDivisors C ((∑ d ∈ u.properDivisors, d) - C)) :
    Covered (u * number ys).properDivisors C ((∑ d ∈ (u * number ys).properDivisors, d) - C) :=
  cover_fresh_tail_with_lift hbase hbu hG (fun hx => hbudget.lift hbase hx hC hP)
    hv htail hr hcop hA hprim hsigma h2u hCT hlow hcover

end OddWeirdSubproblems

namespace OddWeirdSubproblems

open Finset

private def properSum (n : ℕ) : ℕ := ∑ d ∈ n.properDivisors, d

private theorem sumDivisors_fresh_pow {u q : ℕ} (hq : q.Prime) (hqu : ¬ q ∣ u)
    (a : ℕ) :
    (∑ d ∈ (u * q ^ a).divisors, d) =
      (∑ d ∈ u.divisors, d) * ∑ j ∈ range (a + 1), q ^ j := by
  rw [((hq.coprime_iff_not_dvd.mpr hqu).symm.pow_right a).sum_divisors_mul,
    Nat.sum_divisors_prime_pow hq]

private theorem properSum_fresh_pow_step {u q : ℕ} (hq : q.Prime) (hqu : ¬ q ∣ u)
    (a : ℕ) :
    properSum (u * q ^ (a + 1)) = properSum (u * q ^ a) + q ^ (a + 1) * properSum u +
      u * q ^ a := by
  have h := calc
    (∑ d ∈ (u * q ^ (a + 1)).divisors, d) =
        (∑ d ∈ u.divisors, d) * ∑ j ∈ range (a + 1 + 1), q ^ j :=
      sumDivisors_fresh_pow hq hqu (a + 1)
    _ = (∑ d ∈ (u * q ^ a).divisors, d) + (∑ d ∈ u.divisors, d) * q ^ (a + 1) := by
      rw [sum_range_succ, Nat.mul_add, sumDivisors_fresh_pow hq hqu a]
  rw [Nat.sum_divisors_eq_sum_properDivisors_add_self (n := u * q ^ (a + 1)),
    Nat.sum_divisors_eq_sum_properDivisors_add_self (n := u * q ^ a),
    Nat.sum_divisors_eq_sum_properDivisors_add_self (n := u), Nat.add_mul,
    mul_comm (∑ d ∈ u.properDivisors, d)] at h
  unfold properSum
  omega

private theorem properSum_scale_le_fresh_pow {u q : ℕ} (hq : q.Prime) (hqu : ¬ q ∣ u)
    (a : ℕ) : q * properSum (u * q ^ a) ≤ properSum (u * q ^ (a + 1)) := by
  have h : (∑ d ∈ (u * q ^ (a + 1)).divisors, d) =
      q * (∑ d ∈ (u * q ^ a).divisors, d) + ∑ d ∈ u.divisors, d := by
    rw [sumDivisors_fresh_pow hq hqu (a + 1), sumDivisors_fresh_pow hq hqu a,
      geom_sum_succ, Nat.mul_add, Nat.mul_one, mul_left_comm]
  have hscale : u * q ^ (a + 1) = q * (u * q ^ a) := by
    rw [pow_succ]
    ac_rfl
  rw [Nat.sum_divisors_eq_sum_properDivisors_add_self (n := u * q ^ (a + 1)),
    Nat.sum_divisors_eq_sum_properDivisors_add_self (n := u * q ^ a), Nat.mul_add] at h
  conv at h =>
    lhs
    arg 2
    rw [hscale]
  unfold properSum
  omega

private theorem cover_raise_fresh_pow_alternate {u q a C G : ℕ} {ds : List ℕ}
    (hu : 1 < u) (hq : q.Prime) (hqu : ¬ q ∣ u) (hnd : ds.Nodup)
    (hds : ds.toFinset = u.properDivisors.erase 1) (hgap : PrefixGapBound (G + 1) ds) :
    let m := u * q ^ a
    let v := q ^ (a + 1)
    let T := properSum m
    Covered m.properDivisors C (T - C) →
      v + 2 * C ≤ T + 1 →
      m + 2 * C ≤ T + v + 1 →
      v * G + 2 * C ≤ T + m + 1 →
      Covered (u * q ^ (a + 1)).properDivisors C (properSum (u * q ^ (a + 1)) - C) := by
  intro m v T hcover hfirst hsecond hthird
  let n := u * q ^ (a + 1)
  let ws := ds.map (v * ·)
  have hv : 0 < v := pow_pos hq.pos _
  have hm : 0 < m := Nat.mul_pos (Nat.zero_lt_one.trans hu) (pow_pos hq.pos _)
  have hn : n = m * q := by simp only [n, m, pow_succ, mul_assoc]
  have hvnot : ¬ v ∣ m := by
    intro h
    apply hqu
    apply (Nat.mul_dvd_mul_iff_left (pow_pos hq.pos a)).mp
    simpa only [v, m, pow_succ, mul_comm q, mul_comm u] using h
  have hvm : v ≠ m := fun he => hvnot (he ▸ dvd_rfl)
  have hvfresh : v ∉ m.properDivisors := fun h => hvnot (Nat.mem_properDivisors.mp h).1
  have hmfresh : m ∉ insert v m.properDivisors := by
    intro h
    rcases Finset.mem_insert.mp h with he | hm'
    · exact hvm he.symm
    · exact Nat.self_notMem_properDivisors hm'
  have hcover₁ := subsetSumIntervalInsert hvfresh hcover (by omega : C + v ≤ T - C + 1)
  have hcover₂ := subsetSumIntervalInsert hmfresh hcover₁ (by omega : C + m ≤ T - C + v + 1)
  have hinterval : Covered (insert m (insert v m.properDivisors)) C (T + v + m - C) := by
    rwa [show T + v + m - C = T - C + v + m by omega]
  have hval {d : ℕ} (hd : d ∈ ws.toFinset) : ∃ e ∈ u.properDivisors, e ≠ 1 ∧ d = v * e := by
    obtain ⟨e, he, heq⟩ := List.mem_map.mp (List.mem_toFinset.mp hd)
    have hei := Finset.mem_erase.mp (hds ▸ List.mem_toFinset.mpr he)
    exact ⟨e, hei.2, hei.1, heq.symm⟩
  have hdisjoint : Disjoint (insert m (insert v m.properDivisors)) ws.toFinset := by
    apply Finset.disjoint_left.mpr
    intro d hd hd'
    obtain ⟨e, _, he, rfl⟩ := hval hd'
    rcases Finset.mem_insert.mp hd with hm' | hd
    · exact hvnot ⟨e, hm'.symm⟩
    rcases Finset.mem_insert.mp hd with hv' | hd
    · apply he
      apply mul_left_cancel₀ hv.ne'
      simpa only [mul_one] using hv'
    · exact hvnot ((dvd_mul_right v e).trans (Nat.mem_properDivisors.mp hd).1)
  have hws : ws.Nodup := hnd.map (mul_right_injective₀ hv.ne')
  have hwidth : v * (G + 1) + 2 * C ≤ T + v + m + 1 := by
    rw [Nat.mul_add, Nat.mul_one]
    omega
  have hfinal := cover_of_fresh_prefixGapBound hinterval hws hdisjoint (hgap.scale v) hwidth
  have hsub : insert m (insert v m.properDivisors) ∪ ws.toFinset ⊆ n.properDivisors := by
    have hmlt : m < n := by
      rw [hn]
      simpa only [mul_one] using Nat.mul_lt_mul_of_pos_left hq.one_lt hm
    have hmdvd : m ∣ n := hn ▸ dvd_mul_right m q
    intro d hd
    rcases Finset.mem_union.mp hd with hd | hd
    · rcases Finset.mem_insert.mp hd with rfl | hd
      · exact Nat.mem_properDivisors.mpr ⟨hmdvd, hmlt⟩
      rcases Finset.mem_insert.mp hd with rfl | hd
      · refine Nat.mem_properDivisors.mpr ⟨dvd_mul_left v u, ?_⟩
        simpa only [one_mul] using Nat.mul_lt_mul_of_pos_right hu hv
      · obtain ⟨hdvd, hlt⟩ := Nat.mem_properDivisors.mp hd
        exact Nat.mem_properDivisors.mpr ⟨hdvd.trans hmdvd, hlt.trans hmlt⟩
    · obtain ⟨e, he, _, rfl⟩ := hval hd
      obtain ⟨hdvd, hlt⟩ := Nat.mem_properDivisors.mp he
      change v * e ∈ (u * v).properDivisors
      rw [mul_comm u v]
      exact Nat.mem_properDivisors.mpr ⟨mul_dvd_mul_left v hdvd, Nat.mul_lt_mul_of_pos_left hlt hv⟩
  have hone : 1 ∈ u.properDivisors := Nat.mem_properDivisors.mpr ⟨one_dvd _, hu⟩
  have hsum : ds.sum + 1 = properSum u := by
    rw [← sum_toFinset_of_nodup hnd, hds]
    exact Finset.sum_erase_add _ (fun d => d) hone
  have hscaled : ws.sum = v * ds.sum := by
    simpa only [List.map_id, ws, id_eq] using List.sum_map_mul_left ds id v
  have htotal : properSum n = T + v + m + ws.sum := by
    rw [show properSum n = T + v * properSum u + m from properSum_fresh_pow_step hq hqu a,
      ← hsum, hscaled, Nat.mul_add, Nat.mul_one]
    ac_rfl
  change Covered n.properDivisors C (properSum n - C)
  rw [htotal]
  exact cover_mono hsub hfinal

theorem cover_coprime_prime_power_alternate {u q C G : ℕ}
    (hu : 0 < u) (hq : q.Prime) (hqu : ¬ q ∣ u) (hC : 0 < C)
    (hgap : GapUpTo u G) :
    let T := ∑ d ∈ u.properDivisors, d
    Covered u.properDivisors C (T - C) →
    q + 2 * C ≤ T + 1 →
    u + 2 * C ≤ T + q + 1 →
    q * G + 2 * C ≤ T + u + 1 →
    ∀ a : ℕ, Covered (u * q ^ a).properDivisors C ((∑ d ∈ (u * q ^ a).properDivisors, d) - C) := by
  intro T hcover hfirst hsecond hthird
  have hu' : 1 < u := by
    by_contra! h
    have he : u = 1 := by omega
    have hT : T = 0 := by simp [T, he]
    have hp := hq.one_lt
    omega
  let ds := (u.properDivisors.erase 1).sort
  have hone : 1 ∈ u.properDivisors := Nat.mem_properDivisors.mpr ⟨one_dvd _, hu'⟩
  have hs : u.properDivisors.sort = 1 :: ds := by
    calc
      _ = (insert 1 (u.properDivisors.erase 1)).sort := by rw [Finset.insert_erase hone]
      _ = _ := by
        apply Finset.sort_insert (· ≤ ·)
        · intro d hd
          have hdiv := (Nat.mem_properDivisors.mp ((Finset.mem_erase.mp hd).2)).1
          exact Nat.pos_of_dvd_of_pos hdiv hu
        · simp
  have hds : ds.toFinset = u.properDivisors.erase 1 := Finset.sort_toFinset _ _
  have hrest : PrefixGapBound (G + 1) ds := by
    have hg := hgap.prefixGapBound_sort
    rw [hs] at hg
    exact hg.2
  let M (a : ℕ) := u * q ^ a
  let V (a : ℕ) := q ^ (a + 1)
  let S (a : ℕ) := properSum (M a)
  have hpush {x y : ℕ} (h : x + 2 * C ≤ y + 1) : q * x + 2 * C ≤ q * y + 1 := by
    have hm := Nat.mul_le_mul_left q (show x + (2 * C - 1) ≤ y by omega)
    rw [Nat.mul_add] at hm
    have hl := Nat.le_mul_of_pos_left (2 * C - 1) hq.pos
    omega
  have hall (a : ℕ) : Covered (M a).properDivisors C (S a - C) ∧
      V a + 2 * C ≤ S a + 1 ∧ M a + 2 * C ≤ S a + V a + 1 ∧
      V a * G + 2 * C ≤ S a + M a + 1 := by
    induction a with
    | zero => simpa [M, V, S, properSum, T] using ⟨hcover, hfirst, hsecond, hthird⟩
    | succ a ih =>
      obtain ⟨hc, h₁, h₂, h₃⟩ := ih
      have hm : M (a + 1) = q * M a := by unfold M; rw [pow_succ]; ac_rfl
      have hv : V (a + 1) = q * V a := by simp only [V, pow_succ']
      have hs : q * S a ≤ S (a + 1) := properSum_scale_le_fresh_pow hq hqu a
      refine ⟨cover_raise_fresh_pow_alternate (a := a) hu' hq hqu
          (Finset.sort_nodup _ _) hds hrest hc h₁ h₂ h₃, ?_, ?_, ?_⟩
      · rw [hv]
        exact (hpush h₁).trans (Nat.add_le_add_right hs 1)
      · rw [hm, hv]
        have hh := hpush h₂
        rw [Nat.mul_add] at hh
        exact hh.trans (Nat.add_le_add_right (Nat.add_le_add_right hs _) 1)
      · rw [hv, mul_assoc, hm]
        have hh := hpush h₃
        rw [Nat.mul_add] at hh
        exact hh.trans (Nat.add_le_add_right (Nat.add_le_add_right hs _) 1)
  intro a
  exact (hall a).1

end OddWeirdSubproblems

namespace OddWeirdSubproblems

def FreshTwoCaseBudget (base P r C G M : ℕ) : Prop :=
  let R := base * (P - 2 * r)
  let Z := base * P
  let K := (2 * C - 1) * P
  2 * r * Z + M * K ≤ M * R ∧
    Z + K ≤ (P + 1) * R ∧
    2 * r * G * Z + M * K ≤ M * (R + Z) ∧
    2 * r * G * base + (G + 1) * K ≤ R

instance (base P r C G M : ℕ) : Decidable (FreshTwoCaseBudget base P r C G M) := by
  unfold FreshTwoCaseBudget
  infer_instance

private theorem affine_mul_mono {base u a b c : ℕ}
    (hb : 0 < base) (hu : base ≤ u) (h : a * base + c ≤ b * base) :
    a * u + c ≤ b * u := by
  have hab : a ≤ b := (Nat.mul_le_mul_right_iff hb).mp (le_trans (Nat.le_add_right _ _) h)
  have hbase : c ≤ (b - a) * base := by
    have he := congrArg (· * base) (Nat.sub_add_cancel hab)
    rw [Nat.add_mul] at he
    omega
  have hnew := hbase.trans (Nat.mul_le_mul_left _ hu)
  have he := congrArg (· * u) (Nat.sub_add_cancel hab)
  rw [Nat.add_mul] at he
  omega

theorem FreshTwoCaseBudget.alternatives {base u T P r C G M p : ℕ}
    (h : FreshTwoCaseBudget base P r C G M) (hbase : 0 < base) (hle : base ≤ u)
    (hC : 0 < C) (hP : 2 * r < P) (hPp : P ≤ p) (hT : T < u)
    (hM : M ∣ u - T) (hprime : (u - T) * p < 2 * r * u)
    (hratio : (P - 2 * r) * u < P * T) :
    (p * G + 2 * C ≤ T + 1 ∧ u + 2 * C ≤ (p + 1) * T + 1) ∨
    (p + 2 * C ≤ T + 1 ∧ u + 2 * C ≤ T + p + 1 ∧
      p * G + 2 * C ≤ T + u + 1) := by
  let k := 2 * C - 1
  let R := (P - 2 * r) * u
  have hPpos : 0 < P := by omega
  have hdelta : 0 < u - T := by omega
  have hMpos : 0 < M := Nat.pos_of_dvd_of_pos hM hdelta
  have hMle : M ≤ u - T := Nat.le_of_dvd hdelta hM
  have hMp : M * p ≤ 2 * r * u := ((Nat.mul_le_mul_right p hMle).trans_lt hprime).le
  have hk₂ : k + 1 = 2 * C := by dsimp [k]; omega
  change 2 * r * (base * P) + M * (k * P) ≤ M * (base * (P - 2 * r)) ∧
    base * P + k * P ≤ (P + 1) * (base * (P - 2 * r)) ∧
    2 * r * G * (base * P) + M * (k * P) ≤ M * (base * (P - 2 * r) + base * P) ∧
    2 * r * G * base + (G + 1) * (k * P) ≤ base * (P - 2 * r) at h
  have ha : 2 * r * (u * P) + M * (k * P) ≤ M * R := by
    have hx : (2 * r * P) * base + M * (k * P) ≤ (M * (P - 2 * r)) * base :=
      by simpa only [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using h.1
    simpa only [R, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using affine_mul_mono hbase hle hx
  have hb : u * P + k * P ≤ (P + 1) * R := by
    have hx : P * base + k * P ≤ ((P + 1) * (P - 2 * r)) * base :=
      by simpa only [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using h.2.1
    simpa only [R, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using affine_mul_mono hbase hle hx
  have hc : 2 * r * G * (u * P) + M * (k * P) ≤ M * (R + P * u) := by
    have hx : (2 * r * G * P) * base + M * (k * P) ≤
        (M * (P - 2 * r + P)) * base := by
      simp only [Nat.mul_add, Nat.add_mul]
      simpa only [Nat.mul_add, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using h.2.2.1
    have hv := affine_mul_mono hbase hle hx
    simpa only [R, Nat.mul_add, Nat.add_mul, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hv
  have hd : 2 * r * G * u + (G + 1) * (k * P) ≤ R := by
    apply affine_mul_mono hbase hle
    simpa only [Nat.mul_comm (P - 2 * r) base] using h.2.2.2
  have hR : R ≤ P * T := hratio.le
  have hqk : p + k ≤ T := by
    apply (Nat.mul_le_mul_right_iff (Nat.mul_pos hMpos hPpos)).mp
    calc
      (p + k) * (M * P) = (M * p) * P + M * (k * P) := by rw [Nat.add_mul]; ac_rfl
      _ ≤ 2 * r * (u * P) + M * (k * P) := by
        simpa only [Nat.mul_assoc] using Nat.add_le_add_right (Nat.mul_le_mul_right P hMp) _
      _ ≤ M * R := ha
      _ ≤ T * (M * P) := by
        simpa only [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using Nat.mul_le_mul_left M hR
  have hlast : u + k ≤ (p + 1) * T := by
    apply (Nat.mul_le_mul_right_iff hPpos).mp
    rw [Nat.add_mul]
    calc
      _ ≤ (P + 1) * R := hb
      _ ≤ (P + 1) * (P * T) := Nat.mul_le_mul_left _ hR
      _ ≤ (p + 1) * T * P := by
        have hm := Nat.mul_le_mul_right (P * T) (Nat.succ_le_succ hPp)
        simpa only [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hm
  by_cases hsmall : p * G + k ≤ T
  · left
    omega
  · right
    have hscaled : p * G + k ≤ T + u := by
      apply (Nat.mul_le_mul_right_iff (Nat.mul_pos hMpos hPpos)).mp
      calc
        (p * G + k) * (M * P) = (M * p) * (G * P) + M * (k * P) := by rw [Nat.add_mul]; ac_rfl
        _ ≤ 2 * r * G * (u * P) + M * (k * P) := by
          simpa only [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
            Nat.add_le_add_right (Nat.mul_le_mul_right (G * P) hMp) _
        _ ≤ M * (R + P * u) := hc
        _ ≤ (T + u) * (M * P) := by
          simpa only [Nat.mul_add, Nat.add_mul, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
            Nat.mul_le_mul_left M (Nat.add_le_add_right hR (P * u))
    have hmiss : G * (u - T + k) + k ≤ T := by
      apply (Nat.mul_le_mul_right_iff hPpos).mp
      have huT : (u - T) * P + T * P = u * P := by rw [← Nat.add_mul, Nat.sub_add_cancel hT.le]
      have hd₀ : P * u - T * P ≤ 2 * r * u := by
        have hsum : R + 2 * r * u = P * u := by
          unfold R
          rw [← Nat.add_mul, Nat.sub_add_cancel hP.le]
        have hRT : R ≤ T * P := by simpa only [Nat.mul_comm T P] using hR
        exact Nat.sub_le_iff_le_add.mpr (by
          rw [← hsum, Nat.add_comm]
          exact Nat.add_le_add_left hRT _)
      have he := Nat.mul_le_mul_left G hd₀
      have hd₁ : (u - T) * P = P * u - T * P := by
        rw [Nat.mul_comm P u]
        omega
      rw [← hd₁] at he
      calc
        _ = G * ((u - T) * P) + (G + 1) * (k * P) := by
          simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul]
          ac_rfl
        _ ≤ 2 * r * G * u + (G + 1) * (k * P) := by
          simpa only [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
            Nat.add_le_add_right he ((G + 1) * (k * P))
        _ ≤ R := hd
        _ ≤ T * P := by simpa only [Nat.mul_comm T P] using hR
    have hwide : u - T + k < p := by
      by_contra! hm
      have hx := Nat.mul_le_mul_right G hm
      rw [Nat.mul_comm (u - T + k) G] at hx
      omega
    exact ⟨by omega, by omega, by omega⟩

open Finset

theorem FreshTwoCaseBudget.lift {base P r C G M u v p a : ℕ}
    (hbudget : FreshTwoCaseBudget base P r C G M) (hbase : 0 < base) (hle : base ≤ u)
    (hC : 0 < C) (hP : 2 * r < P) (hPt : P ≤ p)
    (hp : p.Prime) (hpu : ¬ p ∣ u) (hdef : u.Deficient)
    (hcop : u.Coprime v) (hA : (u * v).Abundant)
    (hcard : v.primeFactors.card ≤ r) (hmin : ∀ q ∈ v.primeFactors, p ≤ q)
    (hM : M ∣ 2 * u - ∑ d ∈ u.divisors, d) (hgap : GapUpTo u G)
    (hcover : Covered u.properDivisors C ((∑ d ∈ u.properDivisors, d) - C)) :
    Covered (u * p ^ a).properDivisors C ((∑ d ∈ (u * p ^ a).properDivisors, d) - C) := by
  let T := ∑ d ∈ u.properDivisors, d
  have hsum : (∑ d ∈ u.divisors, d) = T + u := Nat.sum_divisors_eq_sum_properDivisors_add_self
  have hdeficiency : 2 * u - (∑ d ∈ u.divisors, d) = u - T := by rw [hsum]; omega
  obtain ⟨hprime, hratio⟩ :=
    freshPrimeBudget_of_coprime_completion hdef hcop hA hp.one_lt hP.le hPt hcard hmin
  rw [hdeficiency] at hprime hM
  obtain ⟨hw, hlast⟩ | ⟨hfirst, hsecond, hthird⟩ :=
    hbudget.alternatives hbase hle hC hP hPt hdef hM hprime hratio
  · have hstep := cover_raise_coprime_prime_power_add (a := 0) (hbase.trans_le hle) hp hpu hC
      (Finset.sort_nodup _ _) (Finset.sort_toFinset _ _) hgap.prefixGapBound_sort
    simp only [pow_zero, mul_one, zero_add, pow_one] at hstep
    apply hstep hcover hw _ a
    change u + 2 * C ≤ T + p * T + 1
    calc
      _ ≤ (p + 1) * T + 1 := hlast
      _ = _ := by rw [Nat.add_mul, Nat.one_mul]; ac_rfl
  · exact cover_coprime_prime_power_alternate (hbase.trans_le hle) hp hpu hC hgap
      hcover hfirst hsecond hthird a

theorem cover_fresh_tail_of_twoCaseBudget {base P r C G M u : ℕ} {ys : Coordinates}
    (hbase : 0 < base) (hbu : base ≤ u) (hC : 0 < C) (hG : 0 < G)
    (hP : 2 * r < P) (hbudget : FreshTwoCaseBudget base P r C G M)
    (hv : PrimeCoordinates ys) (htail : TailFits P ys) (hr : ys.length ≤ r)
    (hcop : u.Coprime (number ys))
    (hA : (u * number ys).Abundant)
    (hprim : ∀ d ∈ (u * number ys).properDivisors, d.Deficient)
    (hsigma : M ∣ ∑ d ∈ u.divisors, d) (h2u : M ∣ 2 * u)
    (hCT : 2 * C ≤ ∑ d ∈ u.properDivisors, d)
    (hlow : DenseLowSums u.properDivisors C G)
    (hcover : Covered u.properDivisors C ((∑ d ∈ u.properDivisors, d) - C)) :
    Covered (u * number ys).properDivisors C ((∑ d ∈ (u * number ys).properDivisors, d) - C) :=
  cover_fresh_tail_with_lift hbase hbu hG (fun hx => hbudget.lift hbase hx hC hP)
    hv htail hr hcop hA hprim hsigma h2u hCT hlow hcover

end OddWeirdSubproblems

namespace OddWeirdSubproblems

def CentralCoverData.growUntil (low target : ℕ) : ℕ → List ℕ → List ℕ
  | _, [] => []
  | high, d :: ds =>
    if high < target && low + d ≤ high + 1 then
      d :: CentralCoverData.growUntil low target (high + d) ds
    else []

def buildCentralCover (fs : Coordinates) : CentralCoverData :=
  let n := number fs
  let total := divisorSum fs - n
  let ds := (sortedDivisors fs).takeWhile (· < n)
  let seed := smallPrefix 1024 ds
  let low := effectiveLow (subsetBits seed) seed.sum
  let high := seed.sum - low
  let growth := CentralCoverData.growUntil low (total / 2) high (ds.drop seed.length)
  ⟨seed, growth, low, high⟩

theorem headRange_of_valid_core {ss : List Slot} {first stop : ℕ}
    (h : PrimeCoordinates (ss.map Slot.minimum) → HeadRangeClosed ss 0 first stop) :
    HeadRangeClosed ss 0 first stop := by
  intro q hlo hhi hp ho xs ys hmatch hvalid hw hproper
  have hc := minimum_valid hmatch.1 (primeCoordinates_left hvalid)
  have hpref : PrimeCoordinates (ss.map Slot.minimum) := by
    change PrimeCoordinates ((ss ++ [(⟨q, 1, false⟩ : Slot)]).map Slot.minimum) at hc
    rw [List.map_append] at hc
    exact primeCoordinates_left hc
  exact h hpref q hlo hhi hp ho xs ys hmatch hvalid hw hproper

end OddWeirdSubproblems

namespace OddWeirdSubproblems

def paletteModulus (b : Box) : ℕ :=
  Nat.gcd (2 * number b.minimum)
    ((b.slots.filter Slot.fixed).map fun s => powerSum s.prime s.exponent).prod

theorem fixedPowerSum_prod_dvd {ss : List Slot} {xs : Coordinates}
    (hfit : List.Forall₂ Slot.Fits ss xs) :
    ((ss.filter Slot.fixed).map fun s => powerSum s.prime s.exponent).prod ∣ divisorSum xs := by
  induction hfit with
  | nil => simp [divisorSum]
  | @cons s x ss xs hs _ ih =>
    cases hf : s.fixed
    · simpa [List.filter_cons, hf, divisorSum] using
        dvd_mul_of_dvd_right ih (powerSum x.1 x.2)
    · have hsum : powerSum s.prime s.exponent = powerSum x.1 x.2 := by
        rw [hs.2.1, hs.2.2.2 hf]
      simpa [List.filter_cons, hf, hsum, divisorSum] using
        Nat.mul_dvd_mul (dvd_rfl : powerSum x.1 x.2 ∣ powerSum x.1 x.2) ih

theorem paletteModulus_dvd_append {b : Box} {xs : Coordinates}
    (hfit : List.Forall₂ Slot.Fits b.slots xs) (tail : Coordinates) :
    paletteModulus b ∣ 2 * number (xs ++ tail) ∧
      paletteModulus b ∣ divisorSum (xs ++ tail) := by
  constructor
  · have hmin : number b.minimum ∣ number xs := minimum_dvd hfit
    have hg : paletteModulus b ∣ 2 * number b.minimum := Nat.gcd_dvd_left _ _
    rw [number_append]
    exact hg.trans (Nat.mul_dvd_mul_left 2 (dvd_mul_of_dvd_left hmin _))
  · have hg : paletteModulus b ∣
        ((b.slots.filter Slot.fixed).map fun s => powerSum s.prime s.exponent).prod :=
      Nat.gcd_dvd_right _ _
    rw [divisorSum_append]
    exact dvd_mul_of_dvd_left (hg.trans (fixedPowerSum_prod_dvd hfit)) _

end OddWeirdSubproblems

namespace OddWeirdSubproblems

open Finset

private theorem number_of_fits_mul {ss : List Slot} {xs : Coordinates}
    (h : List.Forall₂ Slot.Fits ss xs) :
    ∃ k : ℕ, 0 < k ∧ number xs = number (ss.map Slot.minimum) * k ∧
      ∀ q, q.Prime → q ∣ k → ∃ s ∈ ss, s.fixed = false ∧ s.prime = q := by
  induction h with
  | nil =>
    refine ⟨1, Nat.one_pos, by simp [number], ?_⟩
    exact fun q hq hd => (hq.ne_one (Nat.dvd_one.mp hd)).elim
  | @cons s x ss xs hx htail ih =>
    obtain ⟨hq, he, hle, hfix⟩ := hx
    obtain ⟨k, hk, hnumber, hprimes⟩ := ih
    let extra := x.2 - s.exponent
    refine ⟨s.prime ^ extra * k, Nat.mul_pos (pow_pos (he ▸ hq.pos) _) hk, ?_, ?_⟩
    · simp only [number_cons, List.map_cons, Slot.minimum, hnumber]
      rw [← he, ← Nat.add_sub_of_le hle, pow_add]
      dsimp [extra]
      ac_rfl
    · intro p hp hd
      rcases hp.dvd_mul.mp hd with h | h
      · have hf : s.fixed = false := by
          cases hf : s.fixed
          · rfl
          · have hzero : extra = 0 := by dsimp [extra]; rw [hfix hf]; simp
            rw [hzero, pow_zero] at h
            exact (hp.ne_one (Nat.dvd_one.mp h)).elim
        have hs : s.prime.Prime := he ▸ hq
        rcases (Nat.dvd_prime hs).mp (hp.dvd_of_dvd_pow h) with h | hp'
        · exact (hp.ne_one h).elim
        · exact ⟨s, by simp, hf, hp'.symm⟩
      · obtain ⟨t, ht, hfix', heq⟩ := hprimes p hp h
        exact ⟨t, List.mem_cons_of_mem _ ht, hfix', heq⟩

private theorem coprime_coordinate_concat {xs ys : Coordinates} (hv : PrimeCoordinates (xs ++ ys)) :
    (number xs).Coprime (number ys) := by
  apply Nat.coprime_list_prod_right_iff.mpr
  intro z hz
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hz
  have hy' := hv.1 y (List.mem_append_right _ hy)
  apply Nat.Coprime.pow_right
  apply Nat.Coprime.symm
  exact coprime_coordinateProduct hy'
    (primeCoordinates_left hv).1 (fun x hx =>
      ((List.pairwise_append.mp hv.2).2.2 x hx y hy).ne.symm)

theorem properSum_of_validCoordinates {fs : Coordinates} (hv : PrimeCoordinates fs) :
    ∑ d ∈ (number fs).properDivisors, d = divisorSum fs - number fs := by
  have hs := Nat.sum_divisors_eq_sum_properDivisors_add_self (n := number fs)
  rw [← divisorSum_eq hv] at hs
  omega

def paletteBudgetsOkAt (useAlternate : Bool) (b : Box) (M G : ℕ) (data : CentralCoverData) : Bool :=
  let fs := b.minimum
  let n := number fs
  let T := divisorSum fs - n
  let C := data.low
  lowDensityOk data.seed C G && lowModulusOk data.seed C M &&
    decide (0 < C ∧ 0 < G ∧ C ≤ n ∧ 2 * C ≤ T) &&
    b.slots.all (fun s => s.fixed || decide (0 < s.exponent ∧
      s.prime * G + 2 * C ≤ divisorSum (fs.erase s.minimum) + 1)) &&
    decide (b.remaining = 0 ∨ (2 * b.remaining < b.next ∧
      (FreshIntervalBudget n b.next b.remaining C G M ∨
        (useAlternate = true ∧ FreshTwoCaseBudget n b.next b.remaining C G M))))

def paletteBudgetsOkWith (useAlternate : Bool) (b : Box) (G : ℕ)
    (data : CentralCoverData) : Bool :=
  paletteBudgetsOkAt useAlternate b (paletteModulus b) G data

theorem paletteBudgetsOkAt_excludes {useAlternate : Bool} {b : Box} {M G : ℕ}
    {data : CentralCoverData} {Q : Coordinates → Prop}
    (hM : ∀ {xs}, List.Forall₂ Slot.Fits b.slots xs → Q xs → ∀ ys,
      M ∣ 2 * number (xs ++ ys) ∧ M ∣ divisorSum (xs ++ ys))
    (hdata : PrimeCoordinates b.minimum →
      Covered (number b.minimum).properDivisors data.low
        (divisorSum b.minimum - number b.minimum - data.low) ∧
      data.seed.Nodup ∧ data.seed.toFinset ⊆ (number b.minimum).properDivisors)
    (hok : paletteBudgetsOkAt useAlternate b M G data = true) :
    ∀ xs ys, b.Matches xs ys → Q xs → PrimeCoordinates (xs ++ ys) →
      (number (xs ++ ys)).Weird → (∀ d ∈ (number (xs ++ ys)).properDivisors, d.Deficient) →
      False := by
  intro xs ys hmatch hQ hv hw hprim
  have hxs := primeCoordinates_left hv
  have hys : PrimeCoordinates ys :=
    ⟨fun y hy => hv.1 y (List.mem_append_right _ hy), (List.pairwise_append.mp hv.2).2.1⟩
  have hbase := minimum_valid hmatch.1 hxs
  let n := number b.minimum
  let C := data.low
  let u := number xs
  simp only [paletteBudgetsOkAt, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq,
    List.all_eq_true] at hok
  obtain ⟨⟨⟨⟨hlow, hmod⟩, hc, hg, hcn, hcT⟩, hslots⟩, htail⟩ := hok
  obtain ⟨hcert, hsnd, hseedsub⟩ := hdata hbase
  have hbaseT := properSum_of_validCoordinates hbase
  have hfixedLow : DenseLowSums n.properDivisors C G := (lowDensityOk_sound hsnd hlow).mono hseedsub
  have hfixedMod : ∀ x < C, M ∣ x → HasSubsetSum n.properDivisors x := by
    intro x hx hdx
    obtain ⟨t, ht, hs⟩ := lowModulusOk_sound hsnd hmod x hx hdx
    exact ⟨t, ht.trans hseedsub, hs⟩
  have hn : 0 < n := number_pos hbase.1
  have hu : 0 < u := number_pos hxs.1
  obtain ⟨k, hk, heq, hprimes⟩ := number_of_fits_mul hmatch.1
  have heq' : u = n * k := heq
  have hnU : n ∣ u := ⟨k, heq'⟩
  have hNle : n ≤ u := Nat.le_of_dvd hu hnU
  have hsub := properDivisors_subset_of_dvd hu hnU
  have hcofactor (q : ℕ) (hp : q.Prime) (hd : q ∣ k) :
      q ∣ n ∧ q * G + 2 * C ≤ (∑ d ∈ (ordCompl[q] n).divisors, d) + 1 := by
    obtain ⟨s, hs, hfix, hp'⟩ := hprimes q hp hd
    obtain ⟨he, hbudget⟩ := (hslots s hs).resolve_left (by simp [hfix])
    have hsm : (q, s.exponent) ∈ b.minimum := by
      exact List.mem_map.mpr ⟨s, hs, by simp [Slot.minimum, hp']⟩
    let rest := b.minimum.erase (q, s.exponent)
    obtain ⟨hrest, hq, hnot, hnumber⟩ := erase_coordinate hbase hsm
    have hrest' : PrimeCoordinates rest := hrest
    have hnot' : ¬ q ∣ number rest := hnot
    have hnumber' : n = number rest * q ^ s.exponent := hnumber
    have hc : ordCompl[q] n = number rest := by
      rw [hnumber', Nat.mul_comm, Nat.ordCompl_pow_mul_of_not_dvd _ hq hnot']
    constructor
    · have hdvd : q ^ s.exponent ∣ n := by
        rw [hnumber']
        exact dvd_mul_left _ _
      exact (dvd_pow_self q he.ne').trans hdvd
    · rw [hc, ← divisorSum_eq hrest']
      simpa only [Slot.minimum, hp'] using hbudget
  have hpreCover : Covered u.properDivisors C ((∑ d ∈ u.properDivisors, d) - C) := by
    rw [heq']
    exact cover_mul_existing_prime_factors hn hk hg (hbaseT.symm ▸ hcT)
      (hbaseT.symm ▸ hcert) hfixedLow hcofactor
  rw [number_append] at hw hprim
  have hfull : Covered (u * number ys).properDivisors C
      ((∑ d ∈ (u * number ys).properDivisors, d) - C) := by
    rcases htail with hzero | ⟨hf, hb⟩
    · have he : ys = [] := List.length_eq_zero_iff.mp (hmatch.2.2.trans hzero)
      simpa [he, number] using hpreCover
    · have hmd := hM hmatch.1 hQ []
      simp only [List.append_nil] at hmd
      have hsigma : M ∣ ∑ d ∈ u.divisors, d := by rw [← divisorSum_eq hxs]; exact hmd.2
      have hct := (hbaseT.symm ▸ hcT).trans (sum_le_sum_of_subset hsub)
      rcases hb with hb | ⟨_, hb⟩
      · exact cover_fresh_tail hn hNle hc hg hf hb hys hmatch.2.1 hmatch.2.2.le
          (coprime_coordinate_concat hv) hw.1 hprim hsigma hmd.1 hct (hfixedLow.mono hsub) hpreCover
      · exact cover_fresh_tail_of_twoCaseBudget hn hNle hc hg hf hb hys hmatch.2.1
          hmatch.2.2.le (coprime_coordinate_concat hv) hw.1 hprim hsigma hmd.1
          hct (hfixedLow.mono hsub) hpreCover
  have hmul : n ∣ u * number ys := hnU.trans (dvd_mul_right _ _)
  have hfullSub := properDivisors_subset_of_dvd hw.1.pos hmul
  have hs : divisorSum (xs ++ ys) = ∑ d ∈ (u * number ys).divisors, d := by
    rw [divisorSum_eq hv, number_append]
  have hm := hM hmatch.1 hQ ys
  rw [number_append, hs] at hm
  apply hw.2
  apply pseudoperfect_of_central_and_modulus hw.1
    (hcn.trans (Nat.le_of_dvd hw.1.pos hmul)) hfull _ hm.1 hm.2
  intro x hx hdx
  obtain ⟨t, ht, hs⟩ := hfixedMod x hx hdx
  exact ⟨t, ht.trans hfullSub, hs⟩

theorem paletteBudgetsOkWith_closes {useAlternate : Bool} {b : Box} {G : ℕ} {data : CentralCoverData}
    (hdata : PrimeCoordinates b.minimum →
      Covered (number b.minimum).properDivisors data.low
        (divisorSum b.minimum - number b.minimum - data.low) ∧
      data.seed.Nodup ∧ data.seed.toFinset ⊆ (number b.minimum).properDivisors)
    (hok : paletteBudgetsOkWith useAlternate b G data = true) : b.Closed := by
  intro xs ys hm hv hw hp
  exact paletteBudgetsOkAt_excludes (Q := fun _ => True)
    (fun hfit _ ys => paletteModulus_dvd_append hfit ys) hdata hok xs ys hm trivial hv hw hp

theorem CentralCoverData.seed_sound {data : CentralCoverData} {n T : ℕ}
    (hok : data.ok n T = true) : data.seed.Nodup ∧ data.seed.toFinset ⊆ n.properDivisors := by
  simp only [CentralCoverData.ok, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨hnodup, hseed⟩ := divisorListOk_sound hok.1.1.1
  refine ⟨(List.nodup_append.mp hnodup).1, ?_⟩
  intro x hx
  exact hseed (List.mem_toFinset.mpr (List.mem_append_left _ (List.mem_toFinset.mp hx)))

end OddWeirdSubproblems

namespace OddWeirdSubproblems

open Finset

def knownTailLiftOk (C G : ℕ) (pre : Coordinates) : Coordinates → Bool
  | [] => true
  | (p, e) :: ys =>
    let m := number pre
    let T := divisorSum pre - m
    decide (p * G + 2 * C ≤ T + 1 ∧ m + 2 * C ≤ (p + 1) * T + 1) &&
      knownTailLiftOk C G (pre ++ [(p, e)]) ys

theorem knownTailLiftOk_sound {pre ys : Coordinates} {C G : ℕ}
    (hv : PrimeCoordinates (pre ++ ys)) (hC : 0 < C) (hG : 0 < G)
    (hCT : 2 * C ≤ ∑ d ∈ (number pre).properDivisors, d)
    (hlow : DenseLowSums (number pre).properDivisors C G)
    (hcovered : Covered (number pre).properDivisors C
      ((∑ d ∈ (number pre).properDivisors, d) - C))
    (hok : knownTailLiftOk C G pre ys = true) :
    Covered (number (pre ++ ys)).properDivisors C
      ((∑ d ∈ (number (pre ++ ys)).properDivisors, d) - C) := by
  induction ys generalizing pre with
  | nil => simpa only [List.append_nil] using hcovered
  | cons y ys ih =>
    obtain ⟨p, e⟩ := y
    let m := number pre
    let T := ∑ d ∈ m.properDivisors, d
    let new := pre ++ [(p, e)]
    have hpre := primeCoordinates_left hv
    have hm : 0 < m := number_pos hpre.1
    have hp : p.Prime := hv.1 (p, e) (List.mem_append_right _ (by simp))
    have hnot : ¬ p ∣ m := by
      apply hp.coprime_iff_not_dvd.mp
      exact coprime_coordinateProduct hp hpre.1 fun x hx =>
        ((List.pairwise_append.mp hv.2).2.2 x hx (p, e) (by simp)).ne.symm
    have hT : T = divisorSum pre - m := properSum_of_validCoordinates hpre
    simp only [knownTailLiftOk, Bool.and_eq_true, decide_eq_true_eq] at hok
    have hlift := cover_raise_coprime_prime_power_add (a := 0) hm hp hnot hC
      (Finset.sort_nodup _ _) (Finset.sort_toFinset _ _)
      (gapUpTo_of_central_and_low hG hCT hcovered hlow).prefixGapBound_sort
    simp only [pow_zero, mul_one, zero_add, pow_one] at hlift
    have hs : p * G + 2 * C ≤ T + 1 := by rw [hT]; exact hok.1.1
    have hl : m + 2 * C ≤ T + p * T + 1 := by
      rw [hT]
      simpa only [Nat.add_mul, Nat.one_mul, Nat.add_comm (p * _)] using hok.1.2
    have heq : number new = m * p ^ e := by
      rw [number_append, number_cons, show number [] = 1 from rfl, Nat.mul_one]
    have hv' : PrimeCoordinates (new ++ ys) := by
      simpa only [new, List.append_assoc, List.singleton_append] using hv
    have hm' : 0 < number new := number_pos (primeCoordinates_left hv').1
    have hsub := properDivisors_subset_of_dvd hm' (heq.symm ▸ dvd_mul_right m (p ^ e))
    have hnew := ih hv' (hCT.trans (sum_le_sum_of_subset hsub)) (hlow.mono hsub)
      (heq.symm ▸ hlift hcovered hs hl e) hok.2
    simpa only [new, List.append_assoc, List.singleton_append] using hnew

def prefixPaletteOkWith (useAlternate : Bool) (b : Box) (G k : ℕ) : Bool :=
  let pre := b.minimum.take k
  let data := buildCentralCover pre
  data.ok (number pre) (divisorSum pre - number pre) &&
  decide (2 * data.low ≤ divisorSum pre - number pre) &&
  knownTailLiftOk data.low G pre (b.minimum.drop k) &&
  paletteBudgetsOkWith useAlternate b G data

theorem prefixCoverFromData {b : Box} {G k : ℕ}
    (hv : PrimeCoordinates b.minimum) :
    let pre := b.minimum.take k
    let data := buildCentralCover pre
    data.ok (number pre) (divisorSum pre - number pre) = true →
    2 * data.low ≤ divisorSum pre - number pre →
    0 < data.low → 0 < G → lowDensityOk data.seed data.low G = true →
    knownTailLiftOk data.low G pre (b.minimum.drop k) = true →
    Covered (number b.minimum).properDivisors data.low
      (divisorSum b.minimum - number b.minimum - data.low) ∧
    data.seed.Nodup ∧ data.seed.toFinset ⊆ (number b.minimum).properDivisors := by
  intro pre data hdata hCT hC hG hlow htail
  let ys := b.minimum.drop k
  have heq : pre ++ ys = b.minimum := List.take_append_drop k _
  have hv' : PrimeCoordinates (pre ++ ys) := heq.symm ▸ hv
  have hpre := primeCoordinates_left hv'
  have hsum := properSum_of_validCoordinates hpre
  have hcovered := CentralCoverData.sound hsum hdata
  have ⟨hnd, hsub⟩ := CentralCoverData.seed_sound hdata
  have hdense := (lowDensityOk_sound hnd hlow).mono hsub
  have hc := knownTailLiftOk_sound hv' hC hG
    (hsum.symm ▸ hCT) hdense (hsum.symm ▸ hcovered) htail
  have hdvd : number pre ∣ number b.minimum := by
    rw [← heq, number_append]
    exact dvd_mul_right _ _
  rw [heq, properSum_of_validCoordinates hv] at hc
  exact ⟨hc, hnd, hsub.trans (properDivisors_subset_of_dvd (number_pos hv.1) hdvd)⟩

theorem prefixPaletteOkWith_closes {useAlternate : Bool} {b : Box} {G k : ℕ}
    (hok : prefixPaletteOkWith useAlternate b G k = true) : b.Closed := by
  simp only [prefixPaletteOkWith, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨hdata, hCT⟩, htail⟩, hbudget⟩ := hok
  apply paletteBudgetsOkWith_closes _ hbudget
  intro hv
  have hstats := hbudget
  simp only [paletteBudgetsOkWith, paletteBudgetsOkAt, Bool.and_eq_true, decide_eq_true_eq] at hstats
  exact prefixCoverFromData hv hdata hCT hstats.1.1.2.1 hstats.1.1.2.2.1 hstats.1.1.1.1 htail

end OddWeirdSubproblems

namespace OddWeirdSubproblems

def prefixSweepOk (b : Box) (first stop G k h shift : ℕ) : Bool :=
  let fs := b.minimum
  let pre := fs.take k
  let data := buildCentralCover pre
  let n := number fs
  let s := divisorSum fs
  let slope := 2 * n - s + h
  data.ok (number pre) (divisorSum pre - number pre) &&
    lowDensityOk data.seed data.low G &&
    knownTailLiftOk data.low G pre (fs.drop k) &&
    decide (2 * data.low ≤ divisorSum pre - number pre ∧ 0 < data.low ∧ 0 < G ∧
      s ≤ 2 * n ∧ (h = 0 ∨ (h ∣ n ∧ h < n)) ∧ (shift = 0 ∨ shift = n) ∧
      s ≤ s - n - data.low + shift + slope * first ∧
      data.low + shift + slope * (stop - 1) ≤ s)

theorem prefixSweepOk_closes {b : Box} {first stop G k h shift : ℕ}
    (hok : prefixSweepOk b first stop G k h shift = true) : HeadRangeClosed b.slots 0 first stop := by
  simp only [prefixSweepOk, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨hdata, hdense⟩, htail⟩, hwidth, hC, hG, hs, hh, hshift, hfirst, hstop⟩ := hok
  apply headRange_of_valid_core
  intro hv
  have hcover := (prefixCoverFromData hv hdata hwidth hC hG hdense htail).1
  exact headRange_squarefree rfl rfl hs hh hshift hcover hfirst hstop

end OddWeirdSubproblems

namespace OddWeirdSubproblems

open Finset

def pointBitsOk (n s : ℕ) (seed picks : List ℕ) (shift : ℕ) : Bool :=
  let used := 2 * n + picks.sum + shift
  divisorListOk n (seed ++ picks) &&
    (decide (shift = 0) ||
      (decide (shift ∣ n ∧ shift < n) && !(seed ++ picks).contains shift)) &&
    decide (used ≤ s) && (subsetBits seed).testBit (s - used)

theorem pointBitsOk_closes {b : Box} {seed picks : List ℕ} {shift : ℕ}
    (h : pointBitsOk (number b.minimum) (divisorSum b.minimum) seed picks shift = true) :
    b.Closed := by
  simp only [pointBitsOk, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq,
    Bool.not_eq_true'] at h
  obtain ⟨⟨⟨hdiv, hshift⟩, hbudget⟩, hbits⟩ := h
  obtain ⟨hnd, hsub⟩ := divisorListOk_sound hdiv
  obtain ⟨hseed, hpicks, hd⟩ := List.nodup_append.mp hnd
  obtain ⟨t, ht, hsum⟩ := testBit_subsetBits hseed hbits
  have htdiv : t ⊆ (number b.minimum).properDivisors := by
    intro d hdmem
    exact hsub (List.mem_toFinset.mpr (List.mem_append_left _ (List.mem_toFinset.mp (ht hdmem))))
  have hpdiv : picks.toFinset ⊆ (number b.minimum).properDivisors := by
    intro d hdmem
    exact hsub (List.mem_toFinset.mpr (List.mem_append_right _ (List.mem_toFinset.mp hdmem)))
  have hdisj : Disjoint t picks.toFinset := by
    refine Finset.disjoint_left.mpr (fun d hdt hdp => ?_)
    exact hd d (List.mem_toFinset.mp (ht hdt)) d (List.mem_toFinset.mp hdp) rfl
  let u := t ∪ picks.toFinset
  have hudiv : u ⊆ (number b.minimum).properDivisors := union_subset htdiv hpdiv
  have husum : ∑ d ∈ u, d = (∑ d ∈ t, d) + picks.sum := by
    dsimp [u]
    rw [sum_union hdisj, sum_toFinset_of_nodup hpicks]
  have close (v : Finset ℕ) (hv : v ⊆ (number b.minimum).properDivisors)
      (hs : divisorSum b.minimum = 2 * number b.minimum + ∑ d ∈ v, d) : b.Closed := by
    apply close_minimum_witness (ds := v.toList) (Finset.nodup_toList v)
    · intro d hm
      exact Nat.mem_properDivisors.mp (hv (Finset.mem_toList.mp hm))
    · simpa only [Finset.sum_toList] using hs
  rcases hshift with rfl | ⟨hproper, hnot⟩
  · apply close u hudiv
    omega
  · have hnot' : shift ∉ u := by
      intro hm
      have havoid : shift ∉ seed ++ picks := by simpa using hnot
      rcases Finset.mem_union.mp hm with htm | hpm
      · exact havoid (List.mem_append_left _ (List.mem_toFinset.mp (ht htm)))
      · exact havoid (List.mem_append_right _ (List.mem_toFinset.mp hpm))
    apply close (insert shift u) (insert_subset (Nat.mem_properDivisors.mpr hproper) hudiv)
    rw [sum_insert hnot']
    omega

end OddWeirdSubproblems

namespace OddWeirdSubproblems

def pivotPosition (xs : Coordinates) : ℕ :=
  ((xs.zipIdx).foldl (fun (largest, best) ((_, e), i) =>
    if largest < e then (e, i) else (largest, best)) (0, 0)).2

def reconstructLargePicks (fs : Coordinates) (p e : ℕ) :
    List ℕ → ℕ → ℕ → List ℕ × ℕ
  | [], _, target => ([], target)
  | rank :: ranks, cap, target =>
    let base := divisorOfRank rank fs
    let exponent := cappedExponent p (min cap target / base) e
    let d := base * p ^ exponent
    let (ds, remainder) := reconstructLargePicks fs p e ranks (d - 1) (target - d)
    (d :: ds, remainder)

def guidedBitPointOk (b : Box) (slot h : ℕ) (ranks : List ℕ) : Bool :=
  let fs := b.minimum
  let rest := fs.eraseIdx slot
  let k := pivotPosition rest
  let (p, e) := rest[k]?.getD (1, 0)
  let shift := (fs[slot]?.map Prod.fst).getD 0 * h
  let target := divisorSum fs - 2 * number fs - shift
  let (ds, _) := reconstructLargePicks (rest.eraseIdx k) p e ranks (number rest) target
  let seed := smallPrefix 1024 (sortDivisors 20 (divisorsAtMost rest 1024))
  pointBitsOk (number fs) (divisorSum fs) seed ds.reverse shift

def verifyGuidedBitPoint (b : Box) (data : List ℕ) : Option (List ℕ) := do
  let (tag, rest) ← readVarNat 64 data
  let i := tag / 8
  let j := tag % 8
  let fs := b.minimum
  let h := if j < 2 then j else ((fs.eraseIdx i)[j - 2]?.map Prod.fst).getD 0
  let (ranks, rest) ← readLengthPrefixed rest
  if guidedBitPointOk b i h ranks then some rest else none

def guidedBitPoint : PointReplay where
  verify := verifyGuidedBitPoint
  sound := by
    intro b data tail h
    unfold verifyGuidedBitPoint at h
    obtain ⟨⟨tag, rest⟩, _, h⟩ := Option.bind_eq_some_iff.mp h
    dsimp only at h
    obtain ⟨⟨ranks, rest'⟩, _, h⟩ := Option.bind_eq_some_iff.mp h
    dsimp only at h
    generalize hok : guidedBitPointOk b (tag / 8) _ ranks = ok at h
    cases ok
    · contradiction
    · exact pointBitsOk_closes (by simpa only [guidedBitPointOk] using hok)

end OddWeirdSubproblems

namespace OddWeirdSubproblems

private def rankedBoundedPoint : PointReplay :=
  PointReplay.ofDivisors fun b data => do
    let (count, tail) ← readVarNat 64 data
    if count = 0 then decodeRankDivisors b.minimum tail else readNatList count tail

private def verifyBoundedPoint (b : Box) (data : List ℕ) : Option (List ℕ) :=
  match data with
  | 0 :: 0 :: rest => guidedBitPoint.verify b rest
  | _ => rankedBoundedPoint.verify b data

def boundedPoint : PointReplay where
  verify := verifyBoundedPoint
  sound := by
    intro b data tail h
    unfold verifyBoundedPoint at h
    split at h
    · exact guidedBitPoint.sound h
    · exact rankedBoundedPoint.sound h

private def decodeBoundedSweepAction : SweepReader := fun b first _ data =>
  match data with
  | 5 :: tail => do
    let (ds, rest) ← decodeRankDivisors (b.minimum ++ [(first, 1)]) tail
    pure (.point ds, rest)
  | _ => decodeSweepAction data

private def literalBoundedSweep : SweepVerifier :=
  SweepVerifier.ofActions decodeBoundedSweepAction

private def sweepCoreShift (b : Box) (tag : ℕ) : ℕ :=
  if tag = 1 then number b.minimum else 0

private def verifyPrefixSweep (b : Box) (first : ℕ) (data : List ℕ) :
    Option (ℕ × List ℕ) := do
  let (params, rest) ← readNatList 5 data
  let [stop, G, k, h, j] := params | none
  if prefixSweepOk b first stop G k h (sweepCoreShift b j) then some (stop, rest) else none

private theorem verifyPrefixSweep_sound {b : Box} {first stop : ℕ} {data tail : List ℕ}
    (h : verifyPrefixSweep b first data = some (stop, tail)) : HeadRangeClosed b.slots 0 first stop := by
  unfold verifyPrefixSweep at h
  obtain ⟨⟨params, rest⟩, _, h⟩ := Option.bind_eq_some_iff.mp h
  dsimp only at h
  split at h
  · split at h
    · have he := congrArg Prod.fst (Option.some.inj h)
      dsimp only at he
      subst stop
      exact prefixSweepOk_closes ‹_›
    · contradiction
  · contradiction

def boundedSweep : SweepVerifier where
  run b first top data :=
    if data.head? = some 4 then verifyPrefixSweep b first (data.drop 1)
    else literalBoundedSweep.run b first top data
  sound := by
    intro b first top data stop tail h
    change (if data.head? = some 4 then verifyPrefixSweep b first (data.drop 1)
      else literalBoundedSweep.run b first top data) = some (stop, tail) at h
    split at h
    · exact verifyPrefixSweep_sound h
    · exact literalBoundedSweep.sound h

def boundedPalettePruningWith (useAlternate : Bool) : BranchPruning where
  verify b data := do
    let (G, rest) ← readVarNat 64 data
    if G = 0 then some (false, rest)
    else do
      let (k, rest) ← readVarNat 64 rest
      if prefixPaletteOkWith useAlternate b G k then some (true, rest) else none
  sound := by
    intro b data tail h
    obtain ⟨⟨G, rest⟩, _, h⟩ := Option.bind_eq_some_iff.mp h
    dsimp only at h
    split at h
    · simp at h
    · obtain ⟨⟨k, input⟩, _, h⟩ := Option.bind_eq_some_iff.mp h
      dsimp only at h
      split at h
      · exact prefixPaletteOkWith_closes ‹_›
      · contradiction

inductive ClosedBelowCuts (B : ℕ) : List Box → Prop
  | nil : ClosedBelowCuts B []
  | cons {b : Box} {bs : List Box} :
      b.ClosedBelow B → ClosedBelowCuts B bs → ClosedBelowCuts B (b :: bs)

theorem ClosedBelowCuts.closedOfMem {B : ℕ} {cuts : List Box} (hcuts : ClosedBelowCuts B cuts)
    {b : Box} (hb : b ∈ cuts) : b.ClosedBelow B := by
  induction hcuts with
  | nil => simp at hb
  | cons hd _ ih =>
    rcases List.mem_cons.mp hb with rfl | hb
    · exact hd
    · exact ih hb

end OddWeirdSubproblems

namespace OddWeirdSubproblems

structure HuffmanBook where
  primary : ℕ
  spillIndex : ℕ
  spillWidth : ℕ
  spill : ℕ

def HuffmanBook.lookup (book : HuffmanBook) (bits : ℕ) : Option (ℕ × ℕ) := do
  let lowBits := bits % 256
  let entry := (book.primary >>> (12 * lowBits)) % 4096
  let entry ← if entry = 0 then do
      let group := (book.spillIndex >>> (8 * lowBits)) % 256
      if group = 0 then none else
        let size := 2 ^ book.spillWidth
        let index := (group - 1) * size + (bits >>> 8) % size
        some ((book.spill >>> (12 * index)) % 4096)
    else some entry
  if entry = 0 then none else some ((entry - 1) / 256 + 1, (entry - 1) % 256)

def decodeHuffman (book : HuffmanBook) : ℕ → ℕ → Option (List ℕ)
  | 0, _ => some []
  | count + 1, bits => do
    let (length, byte) ← book.lookup bits
    let rest ← decodeHuffman book count (bits >>> length)
    pure (byte :: rest)

private def rankedBook : HuffmanBook :=
  ⟨0x30562410100020351110100030261210172a20340610100030561910100020350810100030260d10172020340410100030561e10100020350910100030260f10172620340610100030561610173c20350710100030260b10171a20340410100030562110100020351110100030261010172820340610100030561810175a20350810100030260c10171d20340410100030561b10100020350910100030260e10172320340610100030561510173020350710100030260a10171420340410100030562410100020351110100030261210172920340610100030561910100020350810100030260d10171f20340410100030561e10100020350910100030260f10172520340610100030561610173620350710100030260b10171720340410100030562110100020351110100030261010172720340610100030561810174820350810100030260c10171c20340410100030561b10100020350910100030260e10172220340610100030561510172d20350710100030260a101713203404101, 0x2a0000002900000028000000000000002700000026000000250000000000000024000000230000002200000000000000210000000000000020000000000000001f0000001e0000001d000000000000001c000000000000001b000000000000001a0000001900000018000000000000001700000000000000160000000000000015000000140000001300000000000000120000001100000010000000000000000f0000000e0000000d000000000000000c000000000000000b000000000000000a000000090000000800000000000000070000000000000006000000000000000500000004000000030000000000000002000000000000000100000000000000, 5, 0xcb5bedbf9be3bfdbe7bf5bdfbffbebbf7be1bfbbe5bf1bddca3bedbf9be3bfdbe7bf5bdfbffbebbf7be1bfbbe5bf1bdd8458428458428458428458428458428458428458428458428458428458428458428458428458428458428458428458429aa99e9a299c9aa99e9a299c9aa99e9a299c9aa99e9a299c9aa99e9a299c9aa99e9a299c9aa99e9a299c9aa99e9a299ca95a8da91a89a93a8ba8fa87a95a8da91a89a93a8ba8fa87a95a8da91a89a93a8ba8fa87a95a8da91a89a93a8ba8fa8782f82e82f82e82f82e82f82e82f82e82f82e82f82e82f82e82f82e82f82e82f82e82f82e82f82e82f82e82f82e82f82e958956957955958956957955958956957955958956957955958956957955958956957955958956957955958956957955ae4adcae0ad6ae2adaadead1ae4adcae0ad6ae2adaadead1ae4adcae0ad6ae2adaadead1ae4adcae0ad6ae2adaadead183983883983883983883983883983883983883983883983883983883983883983883983883983883983883983883983897897297596c97897297596c97897297596c97897297596c97897297596c97897297596c97897297596c97897297596c9f09ea9ec9e89f09ea9ec9e89f09ea9ec9e89f09ea9ec9e89f09ea9ec9e89f09ea9ec9e89f09ea9ec9e89f09ea9ec9e8860854860854860854860854860854860854860854860854860854860854860854860854860854860854860854860854bb3b7fba7b76bafb7cb9bb00bb1b7db9fb71babb7bb83b00bb3b7fba7b76bafb7cb9bb00bb1b7db9fb71babb7bb83b0083e83d83e83d83e83d83e83d83e83d83e83d83e83d83e83d83e83d83e83d83e83d83e83d83e83d83e83d83e83d83e83d99298e99098c99298e99098c99298e99098c99298e99098c99298e99098c99298e99098c99298e99098c99298e99098ca74a6ea70a6ba73a6da6fa6aa74a6ea70a6ba73a6da6fa6aa74a6ea70a6ba73a6da6fa6aa74a6ea70a6ba73a6da6fa6a94c94994a94494c94994a94494c94994a94494c94994a94494c94994a94494c94994a94494c94994a94494c94994a944ac0ab0ab6aa9ab7aadab2aa8ac0ab0ab6aa9ab7aadab2aa8ac0ab0ab6aa9ab7aadab2aa8ac0ab0ab6aa9ab7aadab2aa883483383483383483383483383483383483383483383483383483383483383483383483383483383483383483383483396295f96195e96295f96195e96295f96195e96295f96195e96295f96195e96295f96195e96295f96195e96295f96195e9c29bc9be9ba9c29bc9be9ba9c29bc9be9ba9c29bc9be9ba9c29bc9be9ba9c29bc9be9ba9c29bc9be9ba9c29bc9be9ba84e84b84e84b84e84b84e84b84e84b84e84b84e84b84e84b84e84b84e84b84e84b84e84b84e84b84e84b84e84b84e84bbdbbc7bd3bbfbd7bc3bcdbbbbd9bc5bcfbbdbd5bc1bcbbb9bdbbc7bd3bbfbd7bc3bcdbbbbd9bc5bcfbbdbd5bc1bcbbb984083f84083f84083f84083f84083f84083f84083f84083f84083f84083f84083f84083f84083f84083f84083f84083f99a99699899499a99699899499a99699899499a99699899499a99699899499a99699899499a99699899499a996998994a86a7ea81a79a85a7aa80a77a86a7ea81a79a85a7aa80a77a86a7ea81a79a85a7aa80a77a86a7ea81a79a85a7aa80a7782c82b82c82b82c82b82c82b82c82b82c82b82c82b82c82b82c82b82c82b82c82b82c82b82c82b82c82b82c82b82c82b95394f95294d95394f95294d95394f95294d95394f95294d95394f95294d95394f95294d95394f95294d95394f95294dad0ac9accac6aceac8acaac4ad0ac9accac6aceac8acaac4ad0ac9accac6aceac8acaac4ad0ac9accac6aceac8acaac48378358378358378358378358378358378358378358378358378358378358378358378358378358378358378358378359689649669639689649669639689649669639689649669639689649669639689649669639689649669639689649669639e69d49d89d29e69d49d89d29e69d49d89d29e69d49d89d29e69d49d89d29e69d49d89d29e69d49d89d29e69d49d89d2851850851850851850851850851850851850851850851850851850851850851850851850851850851850851850851850afcaf3af8aeeafaaefaf6ae9afcaf3af8aeeafaaefaf6ae9afcaf3af8aeeafaaefaf6ae9afcaf3af8aeeafaaefaf6ae983b83a83b83a83b83a83b83a83b83a83b83a83b83a83b83a83b83a83b83a83b83a83b83a83b83a83b83a83b83a83b83a98a98498898298a98498898298a98498898298a98498898298a98498898298a98498898298a98498898298a984988982a679f49fe9f2a659f49fe9f2a679f49fe9f2a659f49fe9f2a679f49fe9f2a659f49fe9f2a679f49fe9f2a659f49fe9f2943869941869943869941869943869941869943869941869943869941869943869941869943869941869943869941869aa6aa0aa4a99aa5a9daa1a97aa6aa0aa4a99aa5a9daa1a97aa6aa0aa4a99aa5a9daa1a97aa6aa0aa4a99aa5a9daa1a9783283183283183283183283183283183283183283183283183283183283183283183283183283183283183283183283195d95b95c95995d95b95c95995d95b95c95995d95b95c95995d95b95c95995d95b95c95995d95b95c95995d95b95c9599b89ae9b49ac9b89ae9b49ac9b89ae9b49ac9b89ae9b49ac9b89ae9b49ac9b89ae9b49ac9b89ae9b49ac9b89ae9b49ac847846847846847846847846847846847846847846847846847846847846847846847846847846847846847846847846⟩

def checkUnboundedRankedBlock (fuel : ℕ) (b : Box) (cuts : List Box) (count value : ℕ) : Bool :=
  match decodeHuffman rankedBook count value with
  | none => false
  | some data =>
    match unboundedRankedStream boundedPoint boundedSweep (boundedPalettePruningWith true)
        (fun q => cuts.any (boxEqual q)) fuel b data with
    | some [] => true
    | _ => false

theorem replayCloses {b : Box} {cuts : List Box}
    (hcuts : ClosedCuts cuts) (fuel count value : ℕ)
    (hlo : 1 < b.next) (hodd : Odd b.next)
    (h : checkUnboundedRankedBlock fuel b cuts count value = true) :
    b.Closed := by
  unfold checkUnboundedRankedBlock at h
  split at h
  · contradiction
  · split at h
    · apply unboundedRankedStream_closes _ hlo hodd ‹_›
      intro q hq
      obtain ⟨c, hc, he⟩ := List.any_eq_true.mp hq
      exact (boxEqual_iff_eq q c).mp he ▸ hcuts.closedOfMem hc
    · contradiction

end OddWeirdSubproblems

namespace OddWeirdSubproblems

private theorem nineSmallBlock1 : (⟨[⟨3, 2, false⟩], 5, 0⟩ : Box).Closed := by
  apply replay_closes (witness := (fun _ => [])) (fuel := 1)
  · exact (show 1 < 5 by decide)
  · exact ⟨2, rfl⟩
  · decide +kernel

theorem nineSmallComputed0 : (⟨[⟨3, 2, false⟩], 5, 0⟩ : Box).Closed :=
  nineSmallBlock1

private theorem nineSmallBlock2 : (⟨[⟨3, 2, false⟩], 5, 1⟩ : Box).Closed := by
  apply replay_closes (witness := (fun _ => [])) (fuel := 1)
  · exact (show 1 < 5 by decide)
  · exact ⟨2, rfl⟩
  · decide +kernel

theorem nineSmallComputed1 : (⟨[⟨3, 2, false⟩], 5, 1⟩ : Box).Closed :=
  nineSmallBlock2

private def nineSmallBlock3Rows : List (Nat × List Nat) := [
    (1575, [5, 9, 15, 45]),
    (945, [1, 5, 9, 15]),
    (2205, [5, 7, 9, 15]),
    (7425, [1, 5, 9, 15]),
    (131625, [3, 9, 15, 25, 27, 75, 125, 135, 225, 375]),
    (342225, [5, 9, 15, 25, 27, 39, 45, 65, 75, 81, 117, 135, 169, 195, 225, 351, 405]),
    (78975, [1, 25]),
    (570375, [1, 3, 5, 9, 25, 27, 75, 125, 225, 675]),
]

private theorem nineSmallBlock3 : (⟨[⟨3, 2, false⟩], 5, 2⟩ : Box).Closed := by
  apply replay_closes (witness := (fun n => (nineSmallBlock3Rows.lookup n).getD [])) (fuel := 12)
  · exact (show 1 < 5 by decide)
  · exact ⟨2, rfl⟩
  · decide +kernel

theorem nineSmallComputed2 : (⟨[⟨3, 2, false⟩], 5, 2⟩ : Box).Closed :=
  nineSmallBlock3

end OddWeirdSubproblems

namespace OddWeirdSubproblems

private def oneFourBlock0 : Box := ⟨[⟨3,1,true⟩],5,3⟩
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private def oneFourBlock0Closed : oneFourBlock0.Closed := by
  apply checkPackedBlock (readPoint := PointReplay.ofDivisors decodePoint) (fuel := 18) (count := 24) (value := 0x809080c1009010100040102010603101810010006021600)
    (cut := fun _ => false)
  · simp
  · exact (show 1 < 5 by decide)
  · exact ⟨2,rfl⟩
  · decide +kernel

theorem oneFourRootClosed : (⟨[⟨3,1,true⟩],5,3⟩ : Box).Closed := oneFourBlock0Closed

end OddWeirdSubproblems

namespace OddWeirdSubproblems

private def oneFiveBlock0 : Box := ⟨[⟨3,1,true⟩,⟨5,2,false⟩,⟨7,1,false⟩],39,2⟩
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private def oneFiveBlock0Closed : oneFiveBlock0.Closed := by
  apply checkPackedBlock (readPoint := PointReplay.ofDivisors decodePoint) (fuel := 34) (count := 283) (value := 0x222518012018202000002016010e000505010501c40105600100000420051d06000518011c1601181c01001602180d0818181b16010520130005018301151d1014100d0016010100160208200f00051f01040a0120021d000016012512012001001602050008051d00181801001602000016011809010016021d011601202018001601100225181601251d041808022001001202001008150000000500184d000557011004181820251816012023101d051601080000101d10100c0100160220002216012012000800001d22002018120000240031000532010d25160100251015101001091816011800101818011000000016010400160100182400190500001d2000180018000100160225011a100018001920180020003f00)
    (cut := fun _ => false)
  · simp
  · exact (show 1 < 39 by decide)
  · exact ⟨19,rfl⟩
  · decide +kernel

private def oneFiveBlock1 : Box := ⟨[⟨3,1,true⟩,⟨5,1,false⟩,⟨7,1,false⟩],9,2⟩
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private def oneFiveBlock1Closed : oneFiveBlock1.Closed := by
  apply checkPackedBlock (readPoint := PointReplay.ofDivisors decodePoint) (fuel := 52) (count := 559) (value := 0x60c01001801000202010002060404251005060102010503020406010b0c1701200503010203090309081701010d100d2d00096a010406080f0804102502010d0000010203100005018501010203010b0c030125020a000945010b01020804080505031010000008010012020100060218001d231000001500160121000502a201090a0101000102020a0101020c080702001a08010006160005640102020808130804081000181d251d0e000502a001211601202016011601000808220303030403050c030306020a01020303031117011b1d0d2400063d01010100064b0104080101060802060f0b0201000e0201000212000802e5010702b7010f1714040010222200181d15250e0101000602010002160017028501010102000602a9011f07040409160116010d1d12010d091601010006140011028201061213080425100800010012021d0100120225180500042300202524001d00087d011d011d00040005790125210200051401210023000400052401001816010020060005560116010200054401151601210400062c011020230300050701052101001602002400231601001001001602051b140005280100001d1800010016021601160116011d1816012205010016021201000023081f000809011801001602050005090124180200060a01201800001601010016020100120d000601010b2a010a1f01061c17140408181d250a251a0801001602140100120101010201010202020401010202010104020413171404101810203000)
    (cut := fun b => boxEqual b oneFiveBlock0)
  · intro b h
    have e := (boxEqual_iff_eq _ _).mp h
    exact e.symm ▸ oneFiveBlock0Closed
  · exact (show 1 < 9 by decide)
  · exact ⟨4,rfl⟩
  · decide +kernel

private def oneFiveBlock2 : Box := ⟨[⟨3,1,true⟩],5,4⟩
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private def oneFiveBlock2Closed : oneFiveBlock2.Closed := by
  apply checkPackedBlock (readPoint := PointReplay.ofDivisors decodePoint) (fuel := 30) (count := 188) (value := 0x1810000020010016020a000529010e03011107010d010201010d0c0f1702241d1808232401001602101d1000030100160201000100020105090307010d0301080b170208010001010306070b0607170218101d010002030105030309010b090a1702200100010201030a0e061702001c0001000102040402020807130d0602010101010105020a01031418081001000e02140010120900101300082000142518140820000818100100101d2000180d00180008180018200001aa00)
    (cut := fun b => boxEqual b oneFiveBlock1)
  · intro b h
    have e := (boxEqual_iff_eq _ _).mp h
    exact e.symm ▸ oneFiveBlock1Closed
  · exact (show 1 < 5 by decide)
  · exact ⟨2,rfl⟩
  · decide +kernel

theorem oneFiveRootClosed : (⟨[⟨3,1,true⟩],5,4⟩ : Box).Closed := oneFiveBlock2Closed

end OddWeirdSubproblems

namespace OddWeirdSubproblems

private def nineFourBlock0 : Box := ⟨[⟨3,2,false⟩,⟨5,1,false⟩],13,2⟩
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private def nineFourBlock0Closed : nineFourBlock0.Closed := by
  apply checkPackedBlock (readPoint := PointReplay.ofDivisors decodePoint) (fuel := 38) (count := 377) (value := 0x20101010205000618010406060d0704031910010e0106010100060101010202010101010401010602060f0b08041009101c01012a00060201010203010203030306110b010100020f000801bd010b0404081008000008030001191c010004060603030208081c1014180018140806011a180818101018081012011c1010181a10101019191201181918080c18081801010012021a14181a1a010012021c50000601c8011a0100063601081a1a101b0c100c1818141901001202120110081018180b120108181c00055a010c10101c1a110e011201080b000506010653011808141c010012021401000a020808041812011814081410100a140e011018010001020202040606070f02080818001008101c1818101019081201181018103f000545011410181813141010141001001202181014141b140810101201181c0c181c141a020810120100081800080018000801000a021a1812101c08101018081403101b0100120210181408081201101810101018101818105500)
    (cut := fun _ => false)
  · simp
  · exact (show 1 < 13 by decide)
  · exact ⟨6,rfl⟩
  · decide +kernel

private def nineFourBlock1 : Box := ⟨[⟨3,2,false⟩],5,3⟩
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private def nineFourBlock1Closed : nineFourBlock1.Closed := by
  apply checkPackedBlock (readPoint := PointReplay.ofDivisors decodePoint) (fuel := 29) (count := 132) (value := 0x100020604041c0801141c1a010012021a1410140203060301080102090913010412010c02100e010202040606030f0803180c1c18080812080100120209081c0e0108080801000a020814001401000602100100010102010a030a080000100400081b100810180808101b080818081003101800181010181808180818081c1008018100)
    (cut := fun b => boxEqual b nineFourBlock0)
  · intro b h
    have e := (boxEqual_iff_eq _ _).mp h
    exact e.symm ▸ nineFourBlock0Closed
  · exact (show 1 < 5 by decide)
  · exact ⟨2,rfl⟩
  · decide +kernel

theorem nineFourRootClosed : (⟨[⟨3,2,false⟩],5,3⟩ : Box).Closed := nineFourBlock1Closed

end OddWeirdSubproblems

namespace OddWeirdSubproblems

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
mutual
  private theorem rb0 : (⟨[⟨3,5,false⟩,⟨7,2,false⟩,⟨17,1,false⟩,⟨19,1,false⟩],45,1⟩ : Box).Closed :=
    replayCloses (.nil)
      22 121 0x14f5ea17a000489c99ed0e5797d391c2bd00af375e9d4b0ba79000e677b5395f6d0f4ed010408428d3d35b6e2f374b200000b3d9f1fa7e3c5e8001ec2e2f7bb5e8bfafa79000000000000
      (by decide) ⟨22, rfl⟩ (by decide +kernel)

  private theorem rb1 : (⟨[⟨3,4,true⟩,⟨7,2,false⟩,⟨17,1,false⟩,⟨19,1,false⟩],31,1⟩ : Box).Closed :=
    replayCloses (.nil)
      16 103 0x2a95a8768010855aa187680108109cd62f2962000656a979c3880559a876b5bf62e9e40662dd4dd9cec9640001a4f97add9c54c00840000000
      (by decide) ⟨15, rfl⟩ (by decide +kernel)

  private theorem rb2 : (⟨[⟨3,3,false⟩,⟨7,2,false⟩,⟨17,1,false⟩,⟨19,1,false⟩],21,1⟩ : Box).Closed :=
    replayCloses (.cons rb1 (.cons rb0 (.nil)))
      21 208 0x182850b200420690a5e64041021028d1a97aad2790380e2d7b68086b7ebdeda0701daed7e71da003d7ac99f6d00000104084003eaa5982a293141c6973260b079a2c6ea08d7a9d7bcf4064bcf5e0004102120d0eec9bdfa4f20463cc780198a673be7a000000186904960b2e662b504
      (by decide) ⟨10, rfl⟩ (by decide +kernel)

  private theorem rb3 : (⟨[⟨3,2,false⟩,⟨7,1,false⟩,⟨17,1,false⟩,⟨19,1,false⟩],21,1⟩ : Box).Closed :=
    replayCloses (.cons rb2 (.nil))
      14 61 0x18656d6f7158902bd14bcc81962a50b20134ae40000084cbdb50d6c59000000
      (by decide) ⟨10, rfl⟩ (by decide +kernel)

  private theorem rb4 : (⟨[⟨3,6,false⟩,⟨7,3,false⟩,⟨13,2,false⟩,⟨23,2,false⟩],103,1⟩ : Box).Closed :=
    replayCloses (.nil)
      14 191 0x230dc55b97164e981552cd5bc71ba0468e4e4d685937400840089b327e7f49ba020807a687eb6de592f4008441008b2b42c2fb64dd002100039a6767db406b4627742fe93b40084002a0696cc5fdcba7900213a8ec1799c97bd92a6004251d1930bc1db7974bd0021002102da6c0e9775e1bc8febcae144c0000000
      (by decide) ⟨51, rfl⟩ (by decide +kernel)

  private theorem rb5 : (⟨[⟨3,5,false⟩,⟨7,3,false⟩,⟨13,2,false⟩,⟨23,1,false⟩],65,1⟩ : Box).Closed :=
    replayCloses (.cons rb4 (.nil))
      19 242 0x228d435bdc80366a1a1ad8f2041a99ae4fce2f4001a9ae2bd0b8bd036d1e1f5ee40a354f50b7a4cd0000165b3e3e38ed039ac56bdf30b0b6400210013aed37ece676bf8dd7b3c8000000072e9999a94a06dd694166ab1420956810417e4051b0687d74041221886e81142954bcc814f3742f4000ca360ccf8e3a604dc33ab62e246004200000061d0208cfc8
      (by decide) ⟨32, rfl⟩ (by decide +kernel)

  private theorem rb6 : (⟨[⟨3,5,false⟩,⟨7,2,false⟩,⟨13,2,false⟩,⟨23,1,false⟩],55,1⟩ : Box).Closed :=
    replayCloses (.cons rb5 (.nil))
      20 157 0x305ea1da00695c801485e5af30114a350f99010400a4ab3d56c5e8082005eeebd62c81d87d4326037543a7b900012b5430b200073491fae2e2e2e97a004204229c1a51a16164b200000000003ed020a4fc8
      (by decide) ⟨27, rfl⟩ (by decide +kernel)

  private theorem rb7 : (⟨[⟨3,4,false⟩,⟨7,2,false⟩,⟨13,1,false⟩,⟨23,1,false⟩],31,1⟩ : Box).Closed :=
    replayCloses (.cons rb6 (.nil))
      18 151 0x1cb2c9d7b17a001e62d66c4020ea9df3e7a015bbd7af72000323bf5e5f7d018e4d285c5c44c049fd6d4ce0e2f400050786b4ec59000000041bdf3087b590bd00a791a9799000006da0086b7c8084b5a0084d7c8
      (by decide) ⟨15, rfl⟩ (by decide +kernel)
end

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
mutual
  private theorem rb8 : (⟨[⟨3,3,false⟩,⟨7,1,false⟩,⟨13,1,false⟩,⟨31,1,false⟩],43,1⟩ : Box).Closed :=
    replayCloses (.nil)
      15 115 0xaf3143eb1e408a06156f6d039aa46d7ae800647356f6d0000410008a54af3d5e9da5901456f1e9d993b400cbd54d617e64cd00003e3e393fbf496400000000
      (by decide) ⟨21, rfl⟩ (by decide +kernel)

  private theorem rb9 : (⟨[⟨3,4,false⟩,⟨7,2,false⟩,⟨13,2,false⟩,⟨29,1,false⟩],45,1⟩ : Box).Closed :=
    replayCloses (.nil)
      16 135 0x392a861ba0208c7d6e8d7b1da05191a6f2e0db64bd002100000ead54eef6d0128b2617f49da055f5bdfbcc8010806553531be7d42e9e40c3a3a53697078ba7901040012f2cfdf3fbf69e40000000
      (by decide) ⟨22, rfl⟩ (by decide +kernel)

  private theorem rb10 : (⟨[⟨3,3,false⟩,⟨7,1,false⟩,⟨13,1,false⟩,⟨29,1,false⟩],31,1⟩ : Box).Closed :=
    replayCloses (.cons rb9 (.nil))
      17 252 0xe62c7af6d01aa1f50bd039af508501ad5abcf3200561a00000695686e81cc7a84e8082117aad5bc4606d513bdb400840196bd7af5d022b7a9deb1fa015e6bd7b80432ad4374008403835a60000820928d43e7a9201cd326b7b717a0453a35aad8b200420f64d0d2f3d000000034d29d3c77ec782cc50109dca640eca946f58b0036ef559492400000
      (by decide) ⟨15, rfl⟩ (by decide +kernel)

  private theorem rb11 : (⟨[⟨3,2,false⟩,⟨7,1,false⟩,⟨13,1,false⟩],25,2⟩ : Box).Closed :=
    replayCloses (.cons rb10 (.cons rb8 (.nil)))
      25 126 0x1c155d008d2d5ea762f40daf7e8768007550daf6d022756868c000008408ad57204d831ab799002106c69a68e2f40a3eac697071da069d3c86e2e3b40000000000000
      (by decide) ⟨12, rfl⟩ (by decide +kernel)

  private theorem rb12 : (⟨[⟨3,12,false⟩,⟨7,7,false⟩,⟨13,2,true⟩,⟨19,2,true⟩],41019,1⟩ : Box).Closed :=
    replayCloses (.nil)
      21 298 0x17bfa5f4082bdff9ff9187579938b65e8f4e98000082bdfe8fe600415eff7bf3082020a5bf17f308225bfbba0414b7e0ff2190c57a674696eb234010d25a7ccce7748980331e4b1ea49500397bd47071da0356a3b43f5f6df7dbaa16e800000094f0bd020a53c7ff90253e4f408294fd7fe402b7f67e81055bfefff2021b2335b2f33c1ff7c70a4600420008294f43f98129e5ba0414a7aefe40020a37f87fcc213cf7408284f9bfe4086fc5e81050dfc7fc800414aff77f98
      (by decide) ⟨20509, rfl⟩ (by decide +kernel)

  private theorem rb13 : (⟨[⟨3,8,false⟩,⟨7,5,false⟩,⟨13,2,true⟩,⟨19,2,true⟩],7529,1⟩ : Box).Closed :=
    replayCloses (.cons rb12 (.nil))
      28 260 0x6c5b3ddfd8fd000dd6eb7d5b65b7b4cd00000597ecf4082b2f83fe40b2fb5f4082b2fcbff20497f9fa041497cfff902e7f4dd020ae7f1dfc8044ff47a04144ff0ffc84101053dffdfe614eebba04153b81fe40082bf7f3fe6004143bf1fcc0020acddeff3082020b1bfa5fcc41d2cbef2cac9fa000d17ccf4082d17ebff90020b45f4df98189fe374082c4fe37fc8004167ffc3fe6104e3d1e81078f0ffc8
      (by decide) ⟨3764, rfl⟩ (by decide +kernel)

  private theorem rb14 : (⟨[⟨3,7,true⟩,⟨7,4,false⟩,⟨13,2,true⟩,⟨19,2,false⟩],4265,1⟩ : Box).Closed :=
    replayCloses (.nil)
      19 325 0x828b7f3f9841010516ea7f3082020a2dfcff30020a5dfdbf30a77dee81054ef43fc814efede81054ef6dfc8004143bf6ff30837ddd020a0de0ff2004141bc6fcc0325ee7a04164bdbff9154a9227971ea000d27f3f4082d279fff20041693eb7e6019af81e81059af9dff2104653e07a041653e77fcf389f4c20bcf3bf70b74f2d2d5b2fab89d97a00002f5ba04105f77f20f9cefa041f9c3ff900b3d6e810567ddfce6d7d3082e7cffdc312cf758a0002fafa0410b57fe401707a0410b53fc80104d757f980
      (by decide) ⟨2132, rfl⟩ (by decide +kernel)

  private theorem rb15 : (⟨[⟨3,7,false⟩,⟨7,4,false⟩,⟨13,2,true⟩,⟨19,2,false⟩],1691,1⟩ : Box).Closed :=
    replayCloses (.cons rb14 (.cons rb13 (.nil)))
      18 117 0x1078e3bf3052e2fd020d2efffc8cb958f8e2164ed000041a5f8fe6025eb740824beefe40083575bf304cecfd020ccfbffc8027767a0419d83fe4008227fbf72b7d3083c9bff04
      (by decide) ⟨845, rfl⟩ (by decide +kernel)
end

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
mutual
  private theorem rb16 : (⟨[⟨3,6,true⟩,⟨7,4,false⟩,⟨13,3,false⟩,⟨19,2,true⟩],8395,1⟩ : Box).Closed :=
    replayCloses (.nil)
      23 348 0xd53cdbdf9f8f8ed7d385da0712dfffb5dcf97a5d32600420020a63df7e608eb7b69139a865b3b6b2da588000008298fcdf9841123f99e810523fd7ff2004150ff17f3010808281ffcff30a8df76bfbc725e800aefd0f4082aeffeff902bbfbdd020abbf43fc804a7c37408294fd6fe44cf07c365375491303a72359d0ee7a9ca7fdd1c2ed00004157b8bfe6004157bfdfe60041487ef7e60176fe7a0415dba3fe4208082defe3bf30108082ebe6ff3195d6cb81ece16f3aaece18147539eea7e930000041c5e1ff3062f27a041c5f5ff9026277bf5ced69386000083562ff980
      (by decide) ⟨4197, rfl⟩ (by decide +kernel)

  private theorem rb17 : (⟨[⟨3,6,true⟩,⟨7,3,false⟩,⟨13,2,true⟩,⟨19,2,false⟩],1115,1⟩ : Box).Closed :=
    replayCloses (.nil)
      14 216 0x82b68ff30f62dd75dd8f200087a7a041432ffe42080828627f9889ef9cbe7a0041b9e81060dbff90106c7a0418347fe421819d83238cd0023c30bfa167b244c068b66b7a680000083ce1fe60e4374083cd6fe4055f3e8106ae3ff222a19d33838f205d6a876b8b8c98011592b47877499a001ea7ee9c7900000418a27f980
      (by decide) ⟨557, rfl⟩ (by decide +kernel)

  private theorem rb18 : (⟨[⟨3,6,true⟩,⟨7,3,false⟩,⟨13,2,false⟩,⟨19,2,false⟩],1115,1⟩ : Box).Closed :=
    replayCloses (.cons rb17 (.cons rb16 (.nil)))
      16 167 0x7dd5f4082fb17fe7b67a6105ee9fdc1d43d0209dfbfe4075774082740ff232dac2f4fb7550e3593a059e591fcfda6000008386f7f98b323d3f5c42c9e4000041c34bfcc0422d6dd020ad3dfc82d85aea7b4ac7a74c0000041ead7f98039b3e81079ffff20
      (by decide) ⟨557, rfl⟩ (by decide +kernel)

  private theorem rb19 : (⟨[⟨3,7,false⟩,⟨7,4,false⟩,⟨13,3,false⟩,⟨19,1,true⟩],357,1⟩ : Box).Closed :=
    replayCloses (.nil)
      17 194 0x20c327a767113002110faad75b6c764a9801081093696b67763260000002086cff30cd6af1e9c44c0084e5be6d74e3b400840847bc61b930dc6e8019429aeed58dd00000000041081fcc05ebebf3b38ed0399323eb071ba00420d70faddb38c9801082583b3bb171fa000000821ddf98
      (by decide) ⟨178, rfl⟩ (by decide +kernel)

  private theorem rb20 : (⟨[⟨3,7,false⟩,⟨7,3,false⟩,⟨13,2,false⟩,⟨19,1,true⟩],311,1⟩ : Box).Closed :=
    replayCloses (.cons rb19 (.nil))
      18 230 0xca54a952b1e40084eaa4c9d1c6e8003bcb4616078393b40000000041517f3119b07d7ae8000020ad3f981a86943b4064ab35ee40e2a368c2e3b40008b5889f49800009cf40829bff9116ac1f5838cd03295a3abd63c8008ab55b0711a00000828eff3018a550fae80d42b52bd62c800cad4a1ba00ccc42f1500000
      (by decide) ⟨155, rfl⟩ (by decide +kernel)

  private theorem rb21 : (⟨[⟨3,5,false⟩,⟨7,3,false⟩,⟨13,2,false⟩,⟨19,1,true⟩],225,1⟩ : Box).Closed :=
    replayCloses (.cons rb20 (.nil))
      14 113 0x20ac3f98e7a6bf5fae3b40e696bd60e3c801ccd199a5c6e80000a1fa0415dffc8105f4082a9ff90cb1f523eda00263d020a47fe400af7408290ff2104
      (by decide) ⟨112, rfl⟩ (by decide +kernel)

  private theorem rb22 : (⟨[⟨3,8,false⟩,⟨7,3,true⟩,⟨13,2,true⟩,⟨19,2,false⟩],1691,1⟩ : Box).Closed :=
    replayCloses (.nil)
      20 253 0x186f7b7e693c5e80a6a706868aeed2f50bd400000413b17f980104ee1fcc1573a43c69491a0001dadd0209dddfc8ea4f1b5bb1e4019081c1a58f20115681a1f098000018667a041c3affe40020e1b1fcc29b21bcb03c5e800020e18efcc0020ed2bfcc208082867bf311592d2d63c80099d3bf7a4c000ea77d020f50ffe41d4afa041eb97f90020f5edf9800416acff98
      (by decide) ⟨845, rfl⟩ (by decide +kernel)

  private theorem rb23 : (⟨[⟨3,5,false⟩,⟨7,2,false⟩,⟨13,2,false⟩,⟨19,1,false⟩],103,1⟩ : Box).Closed :=
    replayCloses (.cons rb21 (.cons rb18 (.cons rb22 (.cons rb15 (.nil)))))
      34 461 0x28e3693a5dd95d9a5e800020e1d7ff37e60041c3cfff3fe60c3d7fd5f408387aff17fe4008233e9fa3fcc1bbebee7a041ddf5f6ffeb3e0a2580d0c2f4434b2c4a4986c58416333c9ff701d52feee8107aa5f83fccfdf6be984167efcbff70108defefba0416f7f23fc84104bf1dd020a5fbefe85e17ca9717625db9e70b8b9273f726661b16107b79bf700153a3febe8106a747eaffca787d9f4c20a9e1e27fb8084041673faff65fb9e9841cbf33f821ad91d8d336393a6017b638bb3fa3497a0000208ef0ff3076ef74083db43fc80075f5f4082eb57fe43f3d30828667f716646e7eba34af6eb3c8000083d78fe60041eb7bf300054f74082566ff90020b3b7f9728a4b4797524e5e65cc7a0f41104efdd020f49fe53ba61057efee004167bfcc208ddba0416bdfc8
      (by decide) ⟨51, rfl⟩ (by decide +kernel)
end

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
mutual
  private theorem rb24 : (⟨[⟨3,4,false⟩,⟨7,1,true⟩,⟨13,1,false⟩,⟨19,1,false⟩],25,1⟩ : Box).Closed :=
    replayCloses (.nil)
      18 217 0x90850b20042056ba0772942c8095ab50bd0298a942c000010915a2c52c4029a690cd002108ac56af002662a5ee400005552d5e7a0452950c501af287d79900031728590224b53cc000000152c52f3204528d5bcc81950d93a762c8010b0617a000042000001c69993262637504
      (by decide) ⟨12, rfl⟩ (by decide +kernel)

  private theorem rb25 : (⟨[⟨3,4,true⟩,⟨7,3,false⟩,⟨13,2,false⟩,⟨19,2,false⟩],139,1⟩ : Box).Closed :=
    replayCloses (.nil)
      19 252 0x934db6cf7d3c44c035f5b5d9bae3b40034e9cbbdccf1fa066f7653d6e769b9dd3b400002e4f1797cf4063e732d8ec6c5d20000c6b1a176bcbedd3c8148afed8afabfd725e800000002cdd020a9dfc8ea9675b77b3d92f40f596eee5f7d00210650cb69b2b8bd0000010582fe61ea5a78d6c790068d8ab7a68014f336ef6d0198f9dbe71e40001bcf4082c8ff91d87356f720000082db7f98
      (by decide) ⟨69, rfl⟩ (by decide +kernel)

  private theorem rb26 : (⟨[⟨3,3,true⟩,⟨7,2,false⟩,⟨13,1,false⟩,⟨19,1,false⟩],43,1⟩ : Box).Closed :=
    replayCloses (.nil)
      19 149 0xb18f5eb16408b56687680ce9adadf6d00210008b4856ad62c0136add7af62f403295839a962014ade56f720358a1f1ad8b20001c92946ad8a0098b2727f63c800000000010bef98410768107b7c8084
      (by decide) ⟨21, rfl⟩ (by decide +kernel)

  private theorem rb27 : (⟨[⟨3,3,false⟩,⟨7,1,false⟩,⟨13,1,false⟩,⟨19,1,false⟩],25,1⟩ : Box).Closed :=
    replayCloses (.cons rb24 (.cons rb26 (.cons rb25 (.cons rb23 (.nil)))))
      22 165 0x1543bb77a4c00c690bcc035835ab7b4c00029227c7a71c300034646b7b68004fdabd9bc3243b0d9a3eda0041c51bf6771da0000000020b16fcc0420010eafcc04214e8021c9f90020daf988f299003a9eab799000000
      (by decide) ⟨12, rfl⟩ (by decide +kernel)

  private theorem rb28 : (⟨[⟨3,3,true⟩,⟨7,2,false⟩,⟨13,1,false⟩,⟨17,1,false⟩],57,1⟩ : Box).Closed :=
    replayCloses (.nil)
      18 228 0x2ec5adcecf717a021dd5bc7db407b27f68f9e801080a6dbb5cedac5e803476b72f9e8010800010b21fcc51bae761130001bf74010b49fe432185eab63b40c32a56ef4d00913e4ef6d000aa542c7800652d59bc0041850ed00943c308d000198b8b0fd00000000085af7e62a9d5af79e81c100106d7e638231d020ecfc8084
      (by decide) ⟨28, rfl⟩ (by decide +kernel)

  private theorem rb29 : (⟨[⟨3,3,false⟩,⟨7,1,true⟩,⟨13,1,false⟩,⟨17,1,false⟩],29,1⟩ : Box).Closed :=
    replayCloses (.nil)
      20 209 0x42a50b20042321a64003238c9a1c5900211b614df6755120001c10aa51a17a00001262b1dade92c8134ea1dde7a0004ab1d3c6f49640000001f6802149f91c112d30434f124c514f5642f40e094c5720001168021f5f20210021d3e6192421e00848b4a6400840c55d00000
      (by decide) ⟨14, rfl⟩ (by decide +kernel)

  private theorem rb30 : (⟨[⟨3,2,false⟩,⟨7,1,false⟩,⟨13,1,false⟩,⟨17,1,false⟩],19,1⟩ : Box).Closed :=
    replayCloses (.cons rb29 (.cons rb28 (.nil)))
      24 189 0x704a5f747541a70ff308211bfc101aedb5f9f4980727b5784c00083dee802183a1fe41fb5be8021fdbbff2012fcfa00852f1ff8ed9e98084eddfee382054cf401095affe66eaa12555e68b16021262fee3820010aedfcd1ba602161bfe081080109afcc00823be60ba8021a3e4704
      (by decide) ⟨9, rfl⟩ (by decide +kernel)

  private theorem rb31 : (⟨[⟨3,3,false⟩,⟨7,1,false⟩,⟨11,1,false⟩,⟨43,1,false⟩],45,1⟩ : Box).Closed :=
    replayCloses (.nil)
      26 178 0x6566f5eda02a421400420420064b55bdb40084084069583bbcf4008408418cabdf30bf30ba79018defd5bf7e93c801938bae0ece2e9da0321bce9667b325e81076b59f2e0f17a0001af8c6ad8b8e980f4943f1d178fd00000000000236b99efec2fef33318b4102100
      (by decide) ⟨22, rfl⟩ (by decide +kernel)
end

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
mutual
  private theorem rb32 : (⟨[⟨3,5,false⟩,⟨7,3,false⟩,⟨11,2,false⟩,⟨41,1,false⟩],53,1⟩ : Box).Closed :=
    replayCloses (.nil)
      22 237 0x3a98a9799002134e8d2ad8b8e980108108109d869677f62f40248e8e4fd71ba00420c69cfd797164ed00210021014e95af5e85fda79010403a698de9e58ee9da0054a56ead33b3b365903a759c6eae5717a00186d9ab160b92f40008b981d3c7964bd02a950b36d7eb27680020811b6661745fa725e80108000000001bb49992869548696665563969a2d96f9d90f1d9a2c78
      (by decide) ⟨26, rfl⟩ (by decide +kernel)

  private theorem rb33 : (⟨[⟨3,3,false⟩,⟨7,1,false⟩,⟨11,1,false⟩],43,2⟩ : Box).Closed :=
    replayCloses (.cons rb31 (.nil))
      24 79 0x20c8daadeda00420420012c8dfb9717974e980c368d2d0f7392f409b1b1da5a5c44c04100210000000000
      (by decide) ⟨21, rfl⟩ (by decide +kernel)

  private theorem rb34 : (⟨[⟨3,3,false⟩,⟨7,1,false⟩,⟨11,1,false⟩],39,2⟩ : Box).Closed :=
    replayCloses (.cons rb33 (.cons rb32 (.nil)))
      21 117 0x4694ad7b6801084d5ea87d62c8114ad2f70fa92c800108086a696d7db40410000004b426f5bec5e1c54cc50109169824a8c5516628836629794c00840840000
      (by decide) ⟨19, rfl⟩ (by decide +kernel)

  private theorem rb35 : (⟨[⟨3,7,false⟩,⟨7,3,false⟩,⟨11,3,false⟩,⟨31,2,false⟩],169,1⟩ : Box).Closed :=
    replayCloses (.nil)
      14 228 0x22b5fb774e3b4020eccb6d395c74c05db60d2ddbb4b206dc9ea7cbc3f2f974a98017769776761687a48c0003581ef693f6e2260654d8ce8bc2f4b93f40084198f9334a16b62d9640084084038935adc39ced395a1c2ed0000190381fe769e3a60721b9de5faf17a072a71fdf6d2f2d0ecdd00053cb113934bcbfb9615900211739e1fec2c9da0001b40d28ad5afb2bfdc5e4008408400000
      (by decide) ⟨84, rfl⟩ (by decide +kernel)

  private theorem rb36 : (⟨[⟨3,6,false⟩,⟨7,3,false⟩,⟨11,2,false⟩,⟨31,1,true⟩],123,1⟩ : Box).Closed :=
    replayCloses (.nil)
      20 179 0xb7551812726c777b6800c91b1ddeda00dc33b26b63b4001b758ccf9e8116ad56ad5a48d0037ced8b4b0b276818656285138ed000cdd583fec2e37400008a16eb23e3a009819185e80d8617d5e85937403ac89d1f6d000003a6d4e56af993b4000000004164df98084
      (by decide) ⟨61, rfl⟩ (by decide +kernel)

  private theorem rb37 : (⟨[⟨3,5,false⟩,⟨7,3,false⟩,⟨11,2,false⟩,⟨31,1,false⟩],87,1⟩ : Box).Closed :=
    replayCloses (.cons rb36 (.cons rb35 (.nil)))
      18 243 0x53166cd9ab56d25400dc191e5f6e2f40279730be7a045a6a8dc3fa769640084060a764d27cb9dc1d964000006e3ea2b1b47ab47ad2d162d47d33069895662ad0325b2c78c3436df6f9e80cb5a33bd62c80d8766762dafed2540004550e6f58b0027333d38dc6c9da074199dafb656574ed002105db287ebed9593b4008400001af74082c87f90108082d5bf30020d5ff301080836bf98
      (by decide) ⟨43, rfl⟩ (by decide +kernel)

  private theorem rb38 : (⟨[⟨3,4,false⟩,⟨7,2,false⟩,⟨11,2,false⟩,⟨31,1,false⟩],47,1⟩ : Box).Closed :=
    replayCloses (.cons rb37 (.nil))
      18 165 0x35306b56c59002100e94ab7a4c0084839313bbf62f4025addb5f9c4a801081080000af408227e426b484e8010812496bcf404aaa56637400840cb4d307db400000e3a51ba148d4d928b3658d5a08108020fcfcc04215a00860fc8
      (by decide) ⟨23, rfl⟩ (by decide +kernel)

  private theorem rb39 : (⟨[⟨3,5,false⟩,⟨7,3,false⟩,⟨11,2,false⟩,⟨37,1,false⟩],61,1⟩ : Box).Closed :=
    replayCloses (.nil)
      19 185 0x8a34acde7a00421185bd0befa0550b774fb680a6346adeda004200985a329ff7749da066c6b297171ba000004206defd9df3d009b324d634edae9640272d2b42e2c9640000cacbd37cbfafe3caf4bd00210000000c3a0fad53a61b514da0b0d993cdcc5a74890b05515ab31e0210104af98
      (by decide) ⟨30, rfl⟩ (by decide +kernel)
end

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
mutual
  private theorem rb40 : (⟨[⟨3,4,false⟩,⟨7,2,false⟩,⟨11,1,false⟩,⟨37,1,false⟩],39,1⟩ : Box).Closed :=
    replayCloses (.cons rb39 (.nil))
      27 205 0x29ee7af6d00210e9de34ab6326041d56a17a0345abcf58b2000108753d42c8001b42dacceec6e80c16878bf1d2fc795fd70ac80dbc363fd89ccf57d3b400104000000000ddae64cc97b890c58e5a69a1ee0931e02112d00425be4062a54bdc8010810996a950f20042042052ab4c00840000
      (by decide) ⟨19, rfl⟩ (by decide +kernel)

  private theorem rb41 : (⟨[⟨3,3,false⟩,⟨7,1,false⟩,⟨11,1,false⟩],33,2⟩ : Box).Closed :=
    replayCloses (.cons rb34 (.cons rb40 (.nil)))
      14 50 0x18ccdefafb4c062a168c4d890084021009cbb7ebd8a00000000
      (by decide) ⟨16, rfl⟩ (by decide +kernel)

  private theorem rb42 : (⟨[⟨3,8,false⟩,⟨7,4,false⟩,⟨11,4,false⟩,⟨29,2,false⟩],309,1⟩ : Box).Closed :=
    replayCloses (.nil)
      15 252 0x6da3670f4e2c9da051f76c76bdafb5e4bd000d716437071b8dd3b4041007b17ddaeebed7caf489813769ae4eea5a585b3c804b59de9e4e3b7dd3b4003ebc71b9aeb8ba7680bb030bf4ae2f4000410034ceee0e1716579616681554d8f4ececc99a026324f693fae0ca70381c0e9590104000cb978f8ee73afb2b66e80d6b6179797f7ed33400a3eaf336cdeafdb3725e800000066eb6e673dcfdb63a1eac2ed032c6ff6ebd2e1bd877d2f400841040000
      (by decide) ⟨154, rfl⟩ (by decide +kernel)

  private theorem rb43 : (⟨[⟨3,8,false⟩,⟨7,4,false⟩,⟨11,3,false⟩,⟨29,2,false⟩],291,1⟩ : Box).Closed :=
    replayCloses (.cons rb42 (.nil))
      18 184 0x18e674dc1c176392f40397707b5e5c5e80820b3ecf564b92e8be5d2f4000119f4c7d0b99cf79647264c0248d967cd3697f59e404110439c38b6b8b29fec5b3c8082006c8d37268617974f2000029b19181a1dad2e2e2f2e2f2004220801336f62be57e5d2fced5aaf5696680820420000000020a03f98
      (by decide) ⟨145, rfl⟩ (by decide +kernel)

  private theorem rb44 : (⟨[⟨3,7,false⟩,⟨7,3,true⟩,⟨11,3,false⟩,⟨29,2,false⟩],263,1⟩ : Box).Closed :=
    replayCloses (.nil)
      19 246 0xeaa54aad5a49d006f985dded3030eec56ddae2f4023a3c35acc4a800114ac50d2c668137b66707f62f40022a1d185dd8bd000e4dd7f7b4c0dbcb1cd5b164000c3a34b9da1cafee5b2f4064335a5dd8bd010430c9e31a17f56c5b3c80b3eecd74bc5c5e80d7ea99ce4bc5e80003ac0fae6db63bab5599a00420000042926b4b473bcb0b0bb40035160e975c5d25404b956c52f2c964000104000000
      (by decide) ⟨131, rfl⟩ (by decide +kernel)

  private theorem rb45 : (⟨[⟨3,7,false⟩,⟨7,3,false⟩,⟨11,3,false⟩,⟨29,2,false⟩],243,1⟩ : Box).Closed :=
    replayCloses (.cons rb44 (.cons rb43 (.nil)))
      11 61 0x256b3f70e2c9da069deeb657d260659b07c7db8bcba4e800002a3e81053fff90020a4df98
      (by decide) ⟨121, rfl⟩ (by decide +kernel)

  private theorem rb46 : (⟨[⟨3,6,false⟩,⟨7,3,false⟩,⟨11,2,false⟩,⟨29,1,true⟩],169,1⟩ : Box).Closed :=
    replayCloses (.nil)
      19 220 0xa07d40e0e0c9e400840359e2c17bb1da00420095975bae2e2f40039a538eff73b27680108010845b5a986eec768006b39191c0ef3bee57b3b4000000004165bfcc33346c99c76800000d57d020b0bff2382856ade327681f68fe85e8001c32ab6ec7681495aa778a800014295fbf63b4024d8f8ecf9e80000379f4082d8ffc8084
      (by decide) ⟨84, rfl⟩ (by decide +kernel)

  private theorem rb47 : (⟨[⟨3,5,false⟩,⟨7,3,false⟩,⟨11,2,false⟩,⟨29,1,false⟩],107,1⟩ : Box).Closed :=
    replayCloses (.cons rb46 (.cons rb45 (.nil)))
      20 184 0xad63bf3fdc64c0cbc6d56fd8f20359bd50fd616962d9640005de995a9eaf2c97a024fdb85f97cbe9c97a0060e2befb757b74dd000a3f6c671df1fe727e80d58c8e57d740000eaa6d6cf8e3340000045ba0414bbf900082d17f30108c27a04161bfc81bf74082d27f90108c3ba04167dfc8
      (by decide) ⟨53, rfl⟩ (by decide +kernel)
end

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
mutual
  private theorem rb48 : (⟨[⟨3,4,false⟩,⟨7,2,false⟩,⟨11,1,false⟩,⟨29,1,false⟩],37,1⟩ : Box).Closed :=
    replayCloses (.cons rb47 (.nil))
      24 257 0x67aad9ad5693b404308191c1c7680108321b56bdb401b8e85d58bd022bd032a86d492a0418589afce3b400021000004165df980840416cdf98084f5d02086fe404200826bf30108010b1f988c52b4f720042069a4280084cb06b42f40084182e1adee40ee0a5ee402363e3133b1e4001953d7ac79002100000004103f3010808397cc0420010e6f98
      (by decide) ⟨18, rfl⟩ (by decide +kernel)

  private theorem rb49 : (⟨[⟨3,3,false⟩,⟨7,2,false⟩,⟨11,1,false⟩,⟨29,1,false⟩],31,1⟩ : Box).Closed :=
    replayCloses (.cons rb48 (.nil))
      14 116 0x5306b43b409b164c2f40032c52859032cde50d6ad2590021002ce4e4d6f3d002100000418df3049310b00108c775ef5ee4008400034d345725166628
      (by decide) ⟨15, rfl⟩ (by decide +kernel)

  private theorem rb50 : (⟨[⟨3,3,true⟩,⟨7,2,false⟩,⟨11,2,false⟩,⟨23,1,false⟩],53,1⟩ : Box).Closed :=
    replayCloses (.nil)
      14 202 0x13eb4bf7b4c02b5b75f1f2980108459ab46fd8bd000f8e95a37ebda5900012d0cd717df40084001a774010b7efe4042326e802161dfc88363bbc7ca60042472a5080042006af4010aafe4771a5fbcf400848a96210022d254310023c31343fab49e4008441000010557e60210041b9f98
      (by decide) ⟨26, rfl⟩ (by decide +kernel)

  private theorem rb51 : (⟨[⟨3,7,false⟩,⟨7,4,false⟩,⟨11,1,true⟩,⟨23,2,false⟩],369,1⟩ : Box).Closed :=
    replayCloses (.nil)
      14 174 0x652333f5ad8f200422080020866ff3134ad3f78e32601b54e9335b17a0127374c2f4000000d5f4082117fe4042068f4082187fe439b9ad8bed301aedbd9adb6964f2000489c1f9c5c668012d394fe6fb8f20042042000070f4082173fc80840104227f98
      (by decide) ⟨184, rfl⟩ (by decide +kernel)

  private theorem rb52 : (⟨[⟨3,4,false⟩,⟨7,2,false⟩,⟨11,1,false⟩,⟨23,1,false⟩],53,1⟩ : Box).Closed :=
    replayCloses (.cons rb51 (.nil))
      27 286 0x2100414b9bf462fa61062cffc102100214fbf34ee98085af7f04e0b4d2562c80108958d8d6f4d002109ea978dac44c0027a6aa60fad2c801080000085fa0414fffc8ba75ab5e1300095ba87e719a0000020bd020a1ffe427a36d76b8818000637408211bfe4042020aa7fcc153a46c7cf400844343630f20000020aabfcc04230bf4082cfffc80846d3e8105aeff901080829bf98084002145f98
      (by decide) ⟨26, rfl⟩ (by decide +kernel)

  private theorem rb53 : (⟨[⟨3,3,false⟩,⟨7,2,false⟩,⟨11,1,false⟩,⟨23,1,false⟩],27,1⟩ : Box).Closed :=
    replayCloses (.cons rb52 (.cons rb50 (.nil)))
      14 68 0x2a16a19a0042174022a54a97b9002108c1ad0a980b9642c80000000968104b7c8
      (by decide) ⟨13, rfl⟩ (by decide +kernel)

  private theorem rb54 : (⟨[⟨3,4,false⟩,⟨7,2,false⟩,⟨11,1,false⟩,⟨31,1,false⟩],33,1⟩ : Box).Closed :=
    replayCloses (.cons rb38 (.nil))
      25 184 0x442d433400848b07166f0d030d94a1da0458cd9bdc8000008634685e804a67aad8ed00210000030313a3eb1da029d295ef72003ee4c9ed91a52790021000000000dda5c4a8a0f331cb49966434b2663c04225a8f9b2da7ad2379a2c5010845a0087d7c8
      (by decide) ⟨16, rfl⟩ (by decide +kernel)

  private theorem rb55 : (⟨[⟨3,3,false⟩,⟨7,1,false⟩,⟨11,1,false⟩],31,2⟩ : Box).Closed :=
    replayCloses (.cons rb41 (.cons rb54 (.nil)))
      15 117 0x21b5ea1ba013560d6f6d000633a6b93f5c5e801081438be7f63b4000001d681042f905795c80cc54a1e400000a52c43c801085786a5e640000000
      (by decide) ⟨15, rfl⟩ (by decide +kernel)
end

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
mutual
  private theorem rb56 : (⟨[⟨3,2,false⟩,⟨7,1,false⟩,⟨11,1,false⟩],25,2⟩ : Box).Closed :=
    replayCloses (.cons rb55 (.cons rb49 (.nil)))
      17 65 0x1152ada0254b4859000002953d0021008b16aadebf496400840840000000
      (by decide) ⟨12, rfl⟩ (by decide +kernel)

  private theorem rb57 : (⟨[⟨3,4,false⟩,⟨7,1,true⟩,⟨11,2,false⟩,⟨19,1,false⟩],51,1⟩ : Box).Closed :=
    replayCloses (.nil)
      18 197 0x6b160faf3d00281a18d23a492a001c6ec9f32000007966a1dd8b200421d6ab5e3e930000008582ff3113b4f7ad4c90000623d0042c0ffc80840085a8ff30108cdba00858f7f219e4a1da0033d56d00ad3cc46c768000001ebd0042ebf901080043abf30108b3a00868fc8
      (by decide) ⟨25, rfl⟩ (by decide +kernel)

  private theorem rb58 : (⟨[⟨3,3,false⟩,⟨7,1,true⟩,⟨11,1,false⟩,⟨19,1,false⟩],35,1⟩ : Box).Closed :=
    replayCloses (.cons rb57 (.nil))
      18 155 0x5216216404b06d54f8002854c814d29800b1642c8000962afa0082a50b200745a425400bd10b2032952859000000032d73edbaf452d0408433680214df22ac5320011b401086f90a355b8000
      (by decide) ⟨17, rfl⟩ (by decide +kernel)

  private theorem rb59 : (⟨[⟨3,2,true⟩,⟨7,1,false⟩,⟨11,1,false⟩,⟨19,1,false⟩],21,1⟩ : Box).Closed :=
    replayCloses (.nil)
      19 146 0xecacd781055c801082560a0043108001142ada00421b79c30bd006a1d6dac1c76810727a677b68010800000d6aae8010800001751210b24c998ad410ac7a85e8010a484000000
      (by decide) ⟨10, rfl⟩ (by decide +kernel)

  private theorem rb60 : (⟨[⟨3,2,false⟩,⟨7,1,false⟩,⟨11,1,false⟩,⟨19,1,false⟩],21,1⟩ : Box).Closed :=
    replayCloses (.cons rb59 (.cons rb58 (.nil)))
      17 201 0x108048f4d5924ccccc44a10870fe602160ffee002106b9ba12842d537e6021a59ff82208082aaff309f4c20b71fe087638737a68010877af1dde9a004200042d17f98188f4010b03ff21355c804543430ed00000337a0085aff90820020f1fa8d4d43e093161062f820010fde60
      (by decide) ⟨10, rfl⟩ (by decide +kernel)

  private theorem rb61 : (⟨[⟨3,3,false⟩,⟨7,1,true⟩,⟨11,1,false⟩,⟨23,1,false⟩],27,1⟩ : Box).Closed :=
    replayCloses (.nil)
      17 205 0x5256216406599002101052c54b1e400846ee52f320000546a1a1f32006a8deab63b40000006da4982dc10a68b14b4970599705458f0108010c5f3116ba0042305a63cc80108108256b10f2004200000010fde61a90858009a5000d6ac9bde64000000
      (by decide) ⟨13, rfl⟩ (by decide +kernel)

  private theorem rb62 : (⟨[⟨3,3,false⟩,⟨7,1,true⟩,⟨11,1,false⟩,⟨17,1,false⟩],45,1⟩ : Box).Closed :=
    replayCloses (.nil)
      19 260 0x108010d5d3fd4c582ccccdc82926e62c0434aefc1021002149bf30108dbba0085a0ff11d5282d10b2662d3a5cd1242c998923215720652b4854c0cad163cc800250aa680492d7998f200000cd50f3200000010b16fcc04266f4010b5ff20212ad00420bf202100084af98aa360c2c8007ce802179f9010801094fcc062a64022b5a5af3d000000
      (by decide) ⟨22, rfl⟩ (by decide +kernel)

  private theorem rb63 : (⟨[⟨3,2,false⟩,⟨7,1,false⟩,⟨11,1,false⟩,⟨17,1,false⟩],19,1⟩ : Box).Closed :=
    replayCloses (.cons rb62 (.nil))
      15 218 0x1091c3d09506367f98415b7f82042034df59544298989d505a4fe610657f700042ebe5a9014a97af30114bd43b400840ac58a16008b77e85e801080025a1a1cbcd52842cd16316820423ad004217c8eabca5ee400840846b9698f00042000001089f301a53207255b4000009a82159ba28
      (by decide) ⟨9, rfl⟩ (by decide +kernel)
end

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
mutual
  private theorem rb64 : (⟨[⟨3,2,false⟩,⟨7,1,false⟩,⟨11,1,false⟩],13,2⟩ : Box).Closed :=
    replayCloses (.cons rb63 (.cons rb56 (.cons rb61 (.cons rb53 (.cons rb60 (.nil))))))
      18 139 0xd87a6525cccccc5acfa8bc894c4c4a421643f9808517e24e082680217bdd50408d3099ea10083e4e86e801080676c4616240000927b607c6b24021101950dd0000000000
      (by decide) ⟨6, rfl⟩ (by decide +kernel)

  private theorem rb65 : (⟨[⟨3,3,false⟩,⟨5,2,false⟩,⟨37,1,false⟩,⟨47,1,false⟩],49,1⟩ : Box).Closed :=
    replayCloses (.nil)
      17 172 0x8a543404801043152c401b0e3d6ec46809005ab5eab62340eeedb57adae9e404812034b9ad3bf49e4000190c4eac9fd27901200000a60e8d2dd8f2024351c7efd8ed02cf4f9933a164dd0002289f61c99d27901200000000
      (by decide) ⟨24, rfl⟩ (by decide +kernel)

  private theorem rb66 : (⟨[⟨3,5,false⟩,⟨5,3,false⟩,⟨37,1,false⟩,⟨43,1,false⟩,⟨67,1,false⟩],69,0⟩ : Box).Closed :=
    replayCloses (.nil)
      11 154 0x96aad330b3a4a980760faf5ea30398a0686b63c80aad1d1dd5a4f200031cda393e1a0058a995e6d76ba790091bd68e8e3c809004f552bcf5259018c29d53938f20058bc5b2dc790000090a750fac46809000350f9f9a6d364ed00000
      (by decide) ⟨34, rfl⟩ (by decide +kernel)

  private theorem rb67 : (⟨[⟨3,5,false⟩,⟨5,3,false⟩,⟨37,1,false⟩,⟨43,1,false⟩],49,1⟩ : Box).Closed :=
    replayCloses (.cons rb66 (.nil))
      20 167 0x3d5298090c4a54bdc8057ab583ee40e23ea11a0119d7b47271ba07316a87680000245503dab7ec9fda468090064f470d9eb4b000599599fcc8f1da024000005186e31b4d96d2e9da024000000003b49ed1bd49971b185b2c52d04
      (by decide) ⟨24, rfl⟩ (by decide +kernel)

  private theorem rb68 : (⟨[⟨3,3,false⟩,⟨5,2,false⟩,⟨37,1,false⟩],43,2⟩ : Box).Closed :=
    replayCloses (.cons rb65 (.cons rb67 (.nil)))
      14 59 0xd150e8fb680d58debd3b1e40482b34eddee400000236a34b71509318b41000
      (by decide) ⟨21, rfl⟩ (by decide +kernel)

  private theorem rb69 : (⟨[⟨3,5,false⟩,⟨5,4,false⟩,⟨31,1,false⟩,⟨53,1,false⟩],69,1⟩ : Box).Closed :=
    replayCloses (.nil)
      20 176 0x236bb0e5854de4826b8647c340484806ae6cc59d8f20001b79c3ebdb40032b2617cf404828d0dccb697e64f20356f55dd68bb26f11a0000000153b50323c994fb3e5e585a30037676b99eaf2f172b6768093c7676b9733c2fc7e38593036d1d676a2bdadec8eced01200480000000
      (by decide) ⟨34, rfl⟩ (by decide +kernel)

  private theorem rb70 : (⟨[⟨3,3,false⟩,⟨5,2,false⟩,⟨31,1,false⟩],55,2⟩ : Box).Closed :=
    replayCloses (.nil)
      19 162 0xca9507ff6d032429eb06153029c34a97ac4680904d67aade5301219aa768eec74c0002adae3617f62f40488bc7d42c2e2f400012009a070786f6d7f42d9e40a50fd76b3b17a024091966dad9f38ed006a47c627f49640000000000
      (by decide) ⟨27, rfl⟩ (by decide +kernel)

  private theorem rb71 : (⟨[⟨3,3,false⟩,⟨5,2,false⟩,⟨31,1,false⟩],49,2⟩ : Box).Closed :=
    replayCloses (.cons rb70 (.cons rb69 (.nil)))
      15 91 0x142818468106143a3e1a02403318c5e60002f689e59e60931ddafba64753d3548d998f091969863d3faf42ce85d2f40000000
      (by decide) ⟨24, rfl⟩ (by decide +kernel)
end

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
mutual
  private theorem rb72 : (⟨[⟨3,6,false⟩,⟨5,4,false⟩,⟨31,2,false⟩,⟨43,1,false⟩],95,1⟩ : Box).Closed :=
    replayCloses (.nil)
      17 157 0xe1bd5e9d3a4a98187368c3460654bd64defd24680900524647d6ec7901ac56fd938ed014d2c7aad3a4ed012030cededad5f9586fa68c04800000198a1f55ab49da03af8eac9dae2f400e2636b64fe93b4048480000057a0484fc8
      (by decide) ⟨47, rfl⟩ (by decide +kernel)

  private theorem rb73 : (⟨[⟨3,6,false⟩,⟨5,4,false⟩,⟨31,1,false⟩,⟨43,1,false⟩],87,1⟩ : Box).Closed :=
    replayCloses (.cons rb72 (.nil))
      15 153 0xc95eb77b9010e0fab5eba0321425786809015dacc9f5d000031439bdc801e8b14b16400db0777af5d01200198c9cd938cd00950747c3404822d3cb3d7a92c80004d0bc697ac7680900000000971f98
      (by decide) ⟨43, rfl⟩ (by decide +kernel)

  private theorem rb74 : (⟨[⟨3,5,false⟩,⟨5,3,false⟩,⟨31,1,false⟩,⟨43,1,false⟩],65,1⟩ : Box).Closed :=
    replayCloses (.cons rb73 (.nil))
      17 141 0x240e0dac1c4680166dd0c9804d3167801200e0b14bd7a925403af5691f6d000250fcc2fccb64bd01b90cefd7a4850120018f6d1d5ea164ed03d6569ebca6024000000025f3f3090474094cfc8
      (by decide) ⟨32, rfl⟩ (by decide +kernel)

  private theorem rb75 : (⟨[⟨3,3,false⟩,⟨5,2,false⟩,⟨31,1,false⟩,⟨43,1,false⟩],45,1⟩ : Box).Closed :=
    replayCloses (.cons rb74 (.nil))
      18 136 0x4d5a52f6d0120ae1a5bab62a6013160c37404368e3471da0240091cd1a55bd46045ebd60dac68c06cae6f7b900009a80f88f6f52c83459b15b1000000001f681249f9091169848
      (by decide) ⟨22, rfl⟩ (by decide +kernel)

  private theorem rb76 : (⟨[⟨3,6,false⟩,⟨5,4,false⟩,⟨31,1,false⟩,⟨47,1,false⟩],89,1⟩ : Box).Closed :=
    replayCloses (.nil)
      22 175 0x488bdcf56bd494a02401b57b2dccefbedfd6790192c594dc6ca7a790194271dfcff49e4000ed34b5b6bb325e8090000000950f4d9ea16974f20244d2dddc5fe7d5e97a44c08d8dab99e2e0e4a980900cc5afd379bdd783a5e80c1614ceef50b6766179000000000000
      (by decide) ⟨44, rfl⟩ (by decide +kernel)

  private theorem rb77 : (⟨[⟨3,3,false⟩,⟨5,2,false⟩,⟨31,1,false⟩],43,2⟩ : Box).Closed :=
    replayCloses (.cons rb71 (.cons rb76 (.cons rb75 (.nil))))
      20 233 0x34d8ddeb1da06d834a7784c048238d1adbb17a005434a97aad26e800000b3a660f7324a82c5891d040ad56ade7a0052b57af32000706faf5fb17a059c5799dfbf691a024090001d3a60862c896499996ab169d0490c7b9313c9b2c4ad444803a04bf7c88a1830cd012029572024351af7cf9e80900000090ef984800
      (by decide) ⟨21, rfl⟩ (by decide +kernel)

  private theorem rb78 : (⟨[⟨3,6,false⟩,⟨5,4,false⟩,⟨31,2,false⟩,⟨37,1,true⟩],171,1⟩ : Box).Closed :=
    replayCloses (.nil)
      20 194 0x1b191ad5b1da0550d54a960c91a024118a152a58b207062d52c790018dceceef3d0121204dc71738dd0149c1ddbab49a301204801adeeedcf9787a7680d7e7e5e9babe393b40480000000004990fe6125436b071e4000f2f996db71a30121206aba79b6dc54c0000000
      (by decide) ⟨85, rfl⟩ (by decide +kernel)

  private theorem rb79 : (⟨[⟨3,6,false⟩,⟨5,4,false⟩,⟨31,2,false⟩,⟨37,1,false⟩],145,1⟩ : Box).Closed :=
    replayCloses (.cons rb78 (.nil))
      21 260 0x121b989e5eec97a0241d7ce57cce4ba2e4fd0121200c0e3b35fafc7e3f1cb7855300aa9d566237b716cb20240009075ef949c2c6fee2f2f2d8e97902cc98b8763d1caf8ec70bc8009090000032df40933bff2382a59a46b6ed2340486bb7a8eec99da590386c1e76577b25e80000009335fe608daf52d96c2c97a066ccfcd6c5c5e809013c8da3bb749e40090fd5b763b40000049b8fe60603d024c77fc8
      (by decide) ⟨72, rfl⟩ (by decide +kernel)
end

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
mutual
  private theorem rb80 : (⟨[⟨3,6,false⟩,⟨5,4,false⟩,⟨31,1,false⟩,⟨37,1,false⟩],129,1⟩ : Box).Closed :=
    replayCloses (.cons rb79 (.nil))
      17 225 0x2b4bdfbd63c81160d0c3a6051e58335bdea48d012006ebf7af7202401e35be7e717a0240000c07ae6683d2c6d296c95db336c21ab1613e8ad5e64d63ccb043963c07a9d5ab62f401ad1bdfbcf40001a8fa0499fffc8abd40c2a60651a9433400ab553d00a9d6a17a0240469830dd0022ad3bbd74000000000126edf98
      (by decide) ⟨64, rfl⟩ (by decide +kernel)

  private theorem rb81 : (⟨[⟨3,6,false⟩,⟨5,4,false⟩,⟨31,1,false⟩,⟨41,1,false⟩],97,1⟩ : Box).Closed :=
    replayCloses (.nil)
      16 208 0x10755699fd8bd01ae1c9dafefd244c02bcf53ab63940cb150f776b3d93f400034eeadfaf62f40557afd0b4b25e80901c752fef0980900a697cc234048480000048b7f3091eba04837f22ae1d191f4d012329de66f588d012369da3c3eb1e400a191ade7a0124f5aa956ada42800090001ae81295fc8
      (by decide) ⟨48, rfl⟩ (by decide +kernel)

  private theorem rb82 : (⟨[⟨3,4,true⟩,⟨5,3,false⟩,⟨31,1,false⟩,⟨37,1,false⟩],85,1⟩ : Box).Closed :=
    replayCloses (.nil)
      14 169 0x52f7ced7f62f400855b4006acfd3bc26014a039bd49e00001b2ade5ac5aa959003266c7af52620240000090afe620d2ad0c181968f9abdc804b350f200011795a36ec5e804e55cd5e49004808a950d0f868000000971f9848
      (by decide) ⟨42, rfl⟩ (by decide +kernel)

  private theorem rb83 : (⟨[⟨3,3,false⟩,⟨5,2,false⟩,⟨31,1,false⟩],39,2⟩ : Box).Closed :=
    replayCloses (.cons rb77 (.cons rb81 (.nil)))
      20 249 0xd778ce9dfa4bd01208e2f7ef3d01209a72d54b1000001235f98ca570e8c8e3c8091c9d2308d000363a3a3238cd0000039740932fc848f9d024f3f203d56864c0a5ad1879002ae1f55b76e93b404814d2d593b5c7900000030ea24b2a7999968b169d324165c905bba29b9895a889002407e61223682c849e8c5a41f5b37541603a5b2c78480
      (by decide) ⟨19, rfl⟩ (by decide +kernel)

  private theorem rb84 : (⟨[⟨3,3,false⟩,⟨5,2,false⟩,⟨31,1,false⟩],33,2⟩ : Box).Closed :=
    replayCloses (.cons rb83 (.cons rb82 (.cons rb80 (.nil))))
      23 178 0x1c35aa5bbf49da0194ac9c5c5ad264c04848001b8fa04998ff218e4c8faf5180731c44fae8000024c3bf31962c191919193c80352ae4003a1ea47c0601cd1f5ebcf40000060dd024d5bf90916bd0246bf905ce81239f90900936f98480
      (by decide) ⟨16, rfl⟩ (by decide +kernel)

  private theorem rb85 : (⟨[⟨3,4,false⟩,⟨5,3,false⟩,⟨29,1,false⟩,⟨59,1,false⟩],61,1⟩ : Box).Closed :=
    replayCloses (.nil)
      20 204 0x24ab509d02aa5a323eb1da024083cadeb1a3012196b26b56dd27901212030c2f5a3ed301232ede393b5a59346024000a74a54da6fe85d3c809091ce676d7cf4069a4a5e42c2e99a0000000003ed4533b5f2f030a4c5090e6742bdcb7b974ed01e96d8ed7f5b64e981db7a9d4b976ba79012000000
      (by decide) ⟨30, rfl⟩ (by decide +kernel)

  private theorem rb86 : (⟨[⟨3,3,false⟩,⟨5,2,false⟩,⟨29,1,false⟩],55,2⟩ : Box).Closed :=
    replayCloses (.cons rb85 (.nil))
      20 183 0xb3152a58b20245286d5ac1c7900ecd5ab56c4680756adbbcf400012001b078647c4604191f1a593ba4d1809024000c6148c4eec64c0e834a948d6ada7901a9af6c9c9f5268c04ce1adeda0004d237a47763340a50c69dbb11a004dedbf42e2f40000000000
      (by decide) ⟨27, rfl⟩ (by decide +kernel)

  private theorem rb87 : (⟨[⟨3,3,false⟩,⟨5,2,false⟩,⟨29,1,false⟩],49,2⟩ : Box).Closed :=
    replayCloses (.cons rb86 (.nil))
      22 240 0x2421a5ea1ba0242189bd3a763a602441a8da6faa6c9d300943333a171e4004800008e983cc8494ca2c58a024736ef6d0122294347cc481d15ab56fd246801b0b3628ed6e5fd8b0b740000001a7494f8674f39312b49b4d19a73f3efb16cb1e1201229f980f54a1da024050fadde7a02424068ee87680c6e66bf33bf4983001200000769800
      (by decide) ⟨24, rfl⟩ (by decide +kernel)
end

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
mutual
  private theorem rb88 : (⟨[⟨3,6,false⟩,⟨5,4,false⟩,⟨29,2,false⟩,⟨43,2,false⟩],137,1⟩ : Box).Closed :=
    replayCloses (.nil)
      16 210 0x658ad5af5ea495000daf3d7a680900d4307f5693c809026e2b6f0eb3c593a6011b6fccb65b3bf699a0240d43340fafecaf2d9da024024000031ee998e7ab85e17d5d672a73f072c597744a58d5447c12b18b1e14fd7485dafefda44c0244e91b6bea77e8585e40020c6c5e1f53a5ba5e80090152d6fcfabef647a7e800000034ee8126fdfc8
      (by decide) ⟨68, rfl⟩ (by decide +kernel)

  private theorem rb89 : (⟨[⟨3,5,false⟩,⟨5,4,false⟩,⟨29,1,false⟩,⟨43,1,false⟩],95,1⟩ : Box).Closed :=
    replayCloses (.cons rb88 (.nil))
      16 245 0x5286952ad8d18149593bbcf40b31be617c460240453a952f58ed00387c6b79e800a376ef3d0120172b6cfa4c048480000049b37e612012f5f986bb4d7872674953036a1bd652e3b40258eedaf8ecc9da07758303f6980002403195eab7edd2790025b43fbebcbcba5e809cd3686db8bcba5e800041b3fbcbfdc48c0000002afd02457fc84801235f98
      (by decide) ⟨47, rfl⟩ (by decide +kernel)

  private theorem rb90 : (⟨[⟨3,3,false⟩,⟨5,2,false⟩,⟨29,1,false⟩,⟨43,1,false⟩],45,1⟩ : Box).Closed :=
    replayCloses (.cons rb89 (.nil))
      20 228 0x2471d0254bf2290ad5bdb4048e1bcf5e9301209643bbd5693b40eba8697ec5e5d3340480000001263f3090025d3f309694a60452a7a024112490b20469a52f720240960f6f5662f4064ad52f6d026c5686e800065038cddbd49640480000004b2f98e4ab6800066d34598282ccc62d0448
      (by decide) ⟨22, rfl⟩ (by decide +kernel)

  private theorem rb91 : (⟨[⟨3,6,false⟩,⟨5,4,false⟩,⟨29,1,false⟩,⟨41,1,false⟩],121,1⟩ : Box).Closed :=
    replayCloses (.nil)
      20 240 0x26a9c5e6e4d364e98090024c97f98a56d7a762a6024351ad64fac5e8126748e9e3e327681d15699afefda79006dd13136dc44c0000ab5a31375a1c9c5858564000000004998fe61ccb76bfa17193008e8ccfb73b8bd00aad93f3e03000d3638b3596fe92f40db9391d58b99ef647644c00065d8994f07a3ece56ced0120000012643f98486a3e81267fff2120126cdf98
      (by decide) ⟨60, rfl⟩ (by decide +kernel)

  private theorem rb92 : (⟨[⟨3,4,false⟩,⟨5,3,false⟩,⟨29,1,false⟩,⟨41,1,false⟩],53,1⟩ : Box).Closed :=
    replayCloses (.cons rb91 (.nil))
      21 206 0x387c7d7afd268c0024647499fafd7f62c2b206ec3706db93652c5b34600000031ee81269bfe424024d5bf30900249bf984804857f30770e376edd2768091123eb77b6804dbb77aad8ed03983f37ab7e93b40000dd58b6b1dad8bcb67900000000d5d025cbf90900922fcc240c74096cfc8
      (by decide) ⟨26, rfl⟩ (by decide +kernel)

  private theorem rb93 : (⟨[⟨3,3,false⟩,⟨5,2,false⟩,⟨29,1,false⟩,⟨41,1,false⟩],43,1⟩ : Box).Closed :=
    replayCloses (.cons rb92 (.nil))
      15 108 0x9014a9e80115aa50d18091962b226f62c80007715e79895012000004af7cc558a54bdb40486bca1f5eb1e4000000492f9848
      (by decide) ⟨21, rfl⟩ (by decide +kernel)

  private theorem rb94 : (⟨[⟨3,9,false⟩,⟨5,6,false⟩,⟨29,2,false⟩,⟨37,2,false⟩],461,1⟩ : Box).Closed :=
    replayCloses (.nil)
      19 210 0x3d7dd2ebd5f7b23d3f404853099fcfdbfa5757575717681c60717d66bedb1fd7b5c28d001204ecd6db1ffcec6ff66a3743bc2cd0000000000a495331dfac8e56c72b8bc8024242401e0dbd8b73e6f2b6edec3bc4e976809000000066fa26306b7aaf567974565aac4327ae8deb8975eba37a5f5fd7fc55bcf497afed74ac90e21ebea0d255796da9154bcd5e0f3124
      (by decide) ⟨230, rfl⟩ (by decide +kernel)

  private theorem rb95 : (⟨[⟨3,7,false⟩,⟨5,4,false⟩,⟨29,2,false⟩,⟨37,2,false⟩],347,1⟩ : Box).Closed :=
    replayCloses (.cons rb94 (.nil))
      17 245 0x69e1a18efd6c7d9e95301761777a7bdb1c97a024088cafafd7164ed018efd6b6766eba668090058e4eb3c1e2f40b375ad9c2eaeae99a00000016be8120cbff2120217d0241a7fe424074fa048377fc8239435b93cb25e809029d999dadec5e800075bbb74a72b3dd2f40683a50d2d6a5cb666800900fbeb8786eb4392f4053c335dd4bdb8bfb16179000000004823bf309002418df98
      (by decide) ⟨173, rfl⟩ (by decide +kernel)
end

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
mutual
  private theorem rb96 : (⟨[⟨3,6,false⟩,⟨5,4,false⟩,⟨29,2,false⟩,⟨37,2,false⟩],279,1⟩ : Box).Closed :=
    replayCloses (.cons rb95 (.nil))
      16 167 0x1063b1de5fd0b25e8090bb8ccfb3c5e592f40683b5faeeb6c9e404812397d9fccf7cbc8e4bd00d617a78be74763e59585e4000000125e81257ffc82ae726b7ec5e814870d6dd8d1801a71b439dcee2a606d0333ebe697dba668006ded94fc7ca6000002dbe8125effc8
      (by decide) ⟨139, rfl⟩ (by decide +kernel)

  private theorem rb97 : (⟨[⟨3,7,false⟩,⟨5,5,false⟩,⟨29,2,false⟩,⟨37,1,true⟩],305,1⟩ : Box).Closed :=
    replayCloses (.nil)
      17 177 0x1c15aa59b064cd032f3d93b5c593b40ab570eefae2f40236393ea66664f2000242aa148d6c64c035bd4be6ebcd93740048ca1bcdf1b6e326065659289c7680d68d7237ef9d3b40000377be31a53bcfb3d3b400000f999fcd2c593b40480000000494dfe612012457f98
      (by decide) ⟨152, rfl⟩ (by decide +kernel)

  private theorem rb98 : (⟨[⟨3,5,true⟩,⟨5,4,false⟩,⟨29,1,false⟩,⟨37,1,false⟩],177,1⟩ : Box).Closed :=
    replayCloses (.nil)
      19 179 0x2d3acfd0b8a9809023dd024a6ff90d162d56ad259002869cdfae226024000924df98663d56f6d0194ee876800560eedd5b19300662858dd8d180341c52f6d00cb47c6193000d99a352c6680000331858dc9c1c93a000000000d77d024d1ffc848
      (by decide) ⟨88, rfl⟩ (by decide +kernel)

  private theorem rb99 : (⟨[⟨3,4,false⟩,⟨5,3,false⟩,⟨29,1,false⟩,⟨37,1,false⟩],63,1⟩ : Box).Closed :=
    replayCloses (.cons rb98 (.cons rb97 (.cons rb96 (.nil))))
      26 282 0x91b37af5180901692bd780c010f0e686e80c686c7c7cf408bc86b9c9934600065626addba4ed00ae5aab794c08b863533749e4000a8535d377cd2d3460000000233e8124f7fc82aa71be3efa00002480fe639d38c7cd2934600000977409203fc848049a4fe600498cff3090ddba049af7f203942f5eb18800024dbbf31c85839bd46000c5ba049977f212012f5f9848012d5f98
      (by decide) ⟨31, rfl⟩ (by decide +kernel)

  private theorem rb100 : (⟨[⟨3,3,false⟩,⟨5,2,false⟩,⟨29,1,false⟩,⟨37,1,false⟩],39,1⟩ : Box).Closed :=
    replayCloses (.cons rb99 (.nil))
      19 164 0x210a952c790121a2356f58bd00ab5ea1da072031ab62c80009007cc9de7a02400000b3a43dac68680c91a8316247411ab54a123012394b14bd6346000000974fcc452b57af3d010d95a1da000017b4091ef9091e698
      (by decide) ⟨19, rfl⟩ (by decide +kernel)

  private theorem rb101 : (⟨[⟨3,5,false⟩,⟨5,3,false⟩,⟨29,1,false⟩,⟨47,1,false⟩],65,1⟩ : Box).Closed :=
    replayCloses (.nil)
      18 189 0xab140d2a58324680d50e2c85fd254c04804864ed1d1ad8f202400025abf984804b97e602d52adbb1d301230d2ad0e98035131367cfe92f4048296a964eefd26e81944e9670fa85d3c8155aa59bc1400032c1a5e59ea7694a02400000000955f3090b3a04a8fc8
      (by decide) ⟨32, rfl⟩ (by decide +kernel)

  private theorem rb102 : (⟨[⟨3,4,false⟩,⟨5,3,false⟩,⟨29,1,false⟩,⟨47,1,false⟩],49,1⟩ : Box).Closed :=
    replayCloses (.cons rb101 (.nil))
      21 116 0xd5aada024156b756f6d0121220d0e2b7b6809090ca54bd56c790120152379e595af59001b6bea66762a60739dd4b135a4f200000000000093ef98
      (by decide) ⟨24, rfl⟩ (by decide +kernel)

  private theorem rb103 : (⟨[⟨3,3,false⟩,⟨5,2,false⟩,⟨29,1,false⟩],33,2⟩ : Box).Closed :=
    replayCloses (.cons rb87 (.cons rb102 (.cons rb90 (.cons rb93 (.cons rb100 (.nil))))))
      21 92 0x28c63cc8118a50ed01201052d3dc803b8f2e7b75f154c8240055ee7af58ed0121a91a878716400000000000
      (by decide) ⟨16, rfl⟩ (by decide +kernel)
end

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
mutual
  private theorem rb104 : (⟨[⟨3,3,false⟩,⟨5,2,false⟩,⟨41,1,false⟩,⟨43,1,false⟩],49,1⟩ : Box).Closed :=
    replayCloses (.nil)
      18 140 0x105830f20070c8c8fa8c0481200dab7cd37cf400383335b6b3a174dd012003e3b5ad4dfd0b4b0b4b8bc8091368f273d919ef8c8ec8d0000290b1bbd3400048001a4e4cb69bfa174ed01200000000
      (by decide) ⟨24, rfl⟩ (by decide +kernel)

  private theorem rb105 : (⟨[⟨3,5,false⟩,⟨5,3,false⟩,⟨37,1,false⟩,⟨41,1,false⟩],51,1⟩ : Box).Closed :=
    replayCloses (.nil)
      17 195 0x22f5ead7b4c048e62a503ee40dad52854c09a75eadee405335ed35f9f99334000122ac1adebca60058e1b5ee404834ccdec6d3717a0240090a687c727e67497a0246d23a37bcf406b11a66b7cc99a0240986f185f993c8002400eb35f3e6f7e85d2340480000000dda04977c8
      (by decide) ⟨25, rfl⟩ (by decide +kernel)

  private theorem rb106 : (⟨[⟨3,3,false⟩,⟨5,2,false⟩,⟨37,1,false⟩],39,2⟩ : Box).Closed :=
    replayCloses (.cons rb68 (.cons rb105 (.nil)))
      16 115 0x14f5ea11a0240cb58a5e496020d0ed76b0b0b27a80000000966f9808421640e62c42a603456a1e40480021abd79901206a51ab7b900000000
      (by decide) ⟨19, rfl⟩ (by decide +kernel)

  private theorem rb107 : (⟨[⟨3,3,false⟩,⟨5,2,false⟩],31,3⟩ : Box).Closed :=
    replayCloses (.cons rb106 (.cons rb104 (.cons rb84 (.nil))))
      21 96 0x22169a7a8c00858c7ac59026c44ccde9d27680902400053c999d3a16174c980909107479b3bf42d2d2d9030001200000000
      (by decide) ⟨15, rfl⟩ (by decide +kernel)

  private theorem rb108 : (⟨[⟨3,5,false⟩,⟨5,4,false⟩,⟨23,2,false⟩,⟨89,1,false⟩],105,1⟩ : Box).Closed :=
    replayCloses (.nil)
      21 224 0x15231313e7a06d66ea1adea4f2024240bb0dd2b5e85fef2cacae2ed008d8ee9ad93deec2d9e4004848002074a1c1c790121751d19d933a74e8564024ccd626cf527900120000a064d349d3a77efd8ac80909106d6b66b3a7b0b83b3c81b6eed0bede593460241b5053315eabeae6bb3c809eb2f670bd2f2bd2ecf2045630df4fc9df9de76790004800000000
      (by decide) ⟨52, rfl⟩ (by decide +kernel)

  private theorem rb109 : (⟨[⟨3,4,false⟩,⟨5,2,false⟩,⟨23,1,false⟩],91,2⟩ : Box).Closed :=
    replayCloses (.nil)
      22 113 0x184e4f0def9fd0b67a8090d68f0d2fd5a4f20459ae7d7ec7900048120000cb07076b4b0b4b3db3c81d673b9d9ed2cae9e40e1dd57a1616167b679000000000000
      (by decide) ⟨45, rfl⟩ (by decide +kernel)

  private theorem rb110 : (⟨[⟨3,4,false⟩,⟨5,2,false⟩,⟨23,1,false⟩,⟨83,1,false⟩],85,1⟩ : Box).Closed :=
    replayCloses (.nil)
      17 178 0x24b4a5838cd0068d7ab44e3b40d335a1a5c9a5fda5e804686674b3d7e9d679001200012b5fcc72968c4eec68c0276a5bbf62f404822cd830f2009a1c9dafe8593b4051c323eb16404800e8f5933a77ed2c8000000092afcc2422eb8218f15e8aca2c6ad04480
      (by decide) ⟨42, rfl⟩ (by decide +kernel)

  private theorem rb111 : (⟨[⟨3,3,false⟩,⟨5,2,false⟩,⟨23,1,false⟩],81,2⟩ : Box).Closed :=
    replayCloses (.cons rb110 (.cons rb109 (.cons rb108 (.nil))))
      20 111 0x652b583838f2072dbd7a9d27281868b7f62ff64bd00cac17b80012012f5230e98044214ad6334063432393bb1da0355c3ebcf40480000e3a600000
      (by decide) ⟨40, rfl⟩ (by decide +kernel)
end

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
mutual
  private theorem rb112 : (⟨[⟨3,7,false⟩,⟨5,4,false⟩,⟨23,2,false⟩,⟨73,1,false⟩],137,1⟩ : Box).Closed :=
    replayCloses (.nil)
      19 254 0x1b50fa89fd8ed01a98adea30120c3c3aadb4bed92a6036db38bd93f3f367900000310bcf58e50190d0e0fa681c9315ad63c81a75b9dfdcb4b26e800902415677d677db8b27680000d170c2fdbbe7e6c8d0269519ed616fb2bcb2b2b8bb4065ec9924667c667c76715901212004822edcde4e5b4de5b23402a57a78be9f672b23b2a60000000000cdba0ded2d2c6f8dd293aeda2c58b74895caa9248434859aac78
      (by decide) ⟨68, rfl⟩ (by decide +kernel)

  private theorem rb113 : (⟨[⟨3,3,false⟩,⟨5,2,false⟩,⟨23,1,false⟩],75,2⟩ : Box).Closed :=
    replayCloses (.cons rb111 (.nil))
      20 178 0xe89f513ea301af5e52f588d012120b39b339ee774725e809090039d185c5a6e2f4048480004de8128dfc843035a11a035aa37cf9e809061a3a7b7dc592f40484800357a04957f212012e3f309006d70c8fac768116ec999f9c74c04800000
      (by decide) ⟨37, rfl⟩ (by decide +kernel)

  private theorem rb114 : (⟨[⟨3,3,false⟩,⟨5,2,false⟩,⟨23,1,false⟩],73,2⟩ : Box).Closed :=
    replayCloses (.cons rb113 (.cons rb112 (.nil)))
      18 180 0x6af7a89f3d00295eb76ec790095393bbc260003696a47762f406834bd7b900006cdd024d3bf90179eb76ec7900035d9efcc2c9da000000249bf984804857f30915681205f9016a956b0718301202b48d6f3d000059d32640d37720c5891d044800
      (by decide) ⟨36, rfl⟩ (by decide +kernel)

  private theorem rb115 : (⟨[⟨3,7,false⟩,⟨5,4,false⟩,⟨23,2,false⟩,⟨67,1,false⟩],163,1⟩ : Box).Closed :=
    replayCloses (.nil)
      17 267 0x5e636b637f5374bd022dde313eba0240aa96fcc0f1707a5e81146dafb7169b25e8090241a74fae8e5707d9e95301214eaa6cf7da60711c1e986feeee0f070bc81d34b6ebd9e97cb95eccd0000000d86c671dbdcb8b2b676809000000359f4484315967965333658b21e926e49c97dd4e155ec2b5effdf3731e1ae9e199bdf325e8015aa191f6d0120237b2727f63a602461c6f91b971a300001aa9c99de7a024000341e812653fc8
      (by decide) ⟨81, rfl⟩ (by decide +kernel)

  private theorem rb116 : (⟨[⟨3,6,false⟩,⟨5,4,false⟩,⟨23,2,false⟩,⟨67,1,false⟩],143,1⟩ : Box).Closed :=
    replayCloses (.cons rb115 (.nil))
      19 194 0x5287f48eec6e80c9d1b748d693c8014a66b5ac7680d76e1b9bd8ed000297af5afd8ed02695e4edae2f4006383ea752e2f40885acd2323279012000b1bada5c5b6c9da02406c6dad7787267ba6680d6cef7eb1d91cae91a00000cbb4da5fb87a3b1d9a30165c37ab46f1b1dd0bc02400000000024d47f98
      (by decide) ⟨71, rfl⟩ (by decide +kernel)

  private theorem rb117 : (⟨[⟨3,5,false⟩,⟨5,3,false⟩,⟨23,1,false⟩,⟨67,1,false⟩],79,1⟩ : Box).Closed :=
    replayCloses (.cons rb116 (.nil))
      22 126 0x6f1f55bf62340eeb369d38d1809041868fec44c000053e7ae6fce2f40532d89aefa793d5e0eced01b894dc44fe7a768000000000cdba0498f7f212137a04a37f21201295f98
      (by decide) ⟨39, rfl⟩ (by decide +kernel)

  private theorem rb118 : (⟨[⟨3,3,false⟩,⟨5,2,false⟩,⟨23,1,false⟩,⟨67,1,false⟩],69,1⟩ : Box).Closed :=
    replayCloses (.cons rb117 (.nil))
      21 188 0x34b0707dc8037334f2000859a1a3032d564a856bcd200d521f6fb680004181a989f53b27f59e4048030f6f53b152cef2d9230000000011740942fc84808e81299f9110a50f20004a5a43c80ddb6234eb2b59640639a86379e80046991bdb40000000
      (by decide) ⟨34, rfl⟩ (by decide +kernel)

  private theorem rb119 : (⟨[⟨3,7,false⟩,⟨5,5,false⟩,⟨23,2,false⟩,⟨61,1,false⟩],229,1⟩ : Box).Closed :=
    replayCloses (.nil)
      22 254 0x19b834b2dc1ff64bd00eb24666e6b49e404814dea277623408a762e7f63b40b3a3e375b3b3ecf4bb3c8090002ad9991c773bcba5e8187bbeaf385ecf4be59585e40480032e4e33e2efb69d0eabfae27f5d2918090909000000022dd713cbf85752bf2f6af6bb2af6cbf162cc07149ba08900928df9893039a1666eb254c04d6e876809024550b7736eb8ed02cfa7a9c67fbb3f6e9da024090000345e8126c7fc8
      (by decide) ⟨114, rfl⟩ (by decide +kernel)
end

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
mutual
  private theorem rb120 : (⟨[⟨3,7,false⟩,⟨5,4,false⟩,⟨23,2,false⟩,⟨61,1,false⟩],213,1⟩ : Box).Closed :=
    replayCloses (.cons rb119 (.nil))
      15 137 0x3766c6342fd73ba5e81548e6dd238ed012000a572edb5ad7bf42c2f202424000009345fcc152a770e6c76809049354af0d012396eb4b58cd000a3b31dd1ad8ed000000006d3d024c5ffc8
      (by decide) ⟨106, rfl⟩ (by decide +kernel)

  private theorem rb121 : (⟨[⟨3,6,false⟩,⟨5,4,false⟩,⟨23,2,false⟩,⟨61,1,false⟩],179,1⟩ : Box).Closed :=
    replayCloses (.cons rb120 (.nil))
      13 163 0x1cf533b5d9c593b40aa3577167b8e9800305e81261ffe41d0ba775d71da04189fd0a980197ce6dafae805784d76fcc9da000153a9b99df71a3000001befa049b3ff90c86756f5ea4cd00b38d9afcfb716489800144eeade38d1800000024d37f98
      (by decide) ⟨89, rfl⟩ (by decide +kernel)

  private theorem rb122 : (⟨[⟨3,4,false⟩,⟨5,3,false⟩,⟨23,1,false⟩,⟨61,1,false⟩],63,1⟩ : Box).Closed :=
    replayCloses (.cons rb121 (.nil))
      21 241 0x155ea5ba27f49da03d89d836b113000a469191ddba4f200acfcd6c1f2c97a0254c5ac4012014fa9ed272b8bd012d9a5ab269648d01200000049a8fe62ae1a1adeab49e40eb74cc3a6041d57a1ba000579eb6bf38e980566b6d2fb680000024c87f309009376fcc24025ebf980a748c8eec79000137a04a37f212057a0484fc848012f9f98
      (by decide) ⟨31, rfl⟩ (by decide +kernel)

  private theorem rb123 : (⟨[⟨3,7,false⟩,⟨5,4,false⟩,⟨23,2,false⟩,⟨59,1,false⟩],243,1⟩ : Box).Closed :=
    replayCloses (.nil)
      20 262 0x22dd1eaf178fd006ddc1e2d0f47a3b3b40630be74723c5e809019bf9e37b3d5a2f57c767680f40d0ecfd7fae57f4bd01af53a16c74386fa7e80000ce73b2f07a3a1f5755d571389f2e180900000092e3f982ac954b756dda79012090a352fdb327680900009223f984804969fe6120124bbf304767e617e71d30123a9d9ad6cccf4f8d9ba051ad7ae72717a015ca6beacfd2790000011ee812537fc8480125dbf98
      (by decide) ⟨121, rfl⟩ (by decide +kernel)

  private theorem rb124 : (⟨[⟨3,5,false⟩,⟨5,3,false⟩,⟨23,1,false⟩,⟨59,1,false⟩],93,1⟩ : Box).Closed :=
    replayCloses (.cons rb123 (.nil))
      20 261 0x30faa50b83c74c0636364ccec5e80186e717dbe7a029c6c4cb76b3a4f200000977409203fc84851ba0490dff211999bd0b8bd00004946fcc00d17a049b1ff22ac6e76fbfdc54c02ac68716cc64c00a39dc52d2c5e800a74b27b437d93740000001263bfcc24309e81261bfc80e18543ebd56d234048c3eb746f6e2f40000192fa049b9ff9090d87d024cb7fc84804aaff98
      (by decide) ⟨46, rfl⟩ (by decide +kernel)

  private theorem rb125 : (⟨[⟨3,3,false⟩,⟨5,2,false⟩,⟨23,1,false⟩,⟨59,1,false⟩],61,1⟩ : Box).Closed :=
    replayCloses (.cons rb124 (.nil))
      19 194 0x2a62c54b10a061d191ade1a0053cc5bb363c8014f41855ab66d2c024354ac9d3b12a000000306e8126adfc848b5e81235fc84809740962fc868a1694b140658a55bca60241142a50f201c95e43c80900000474094cfc8480480fcc0594a16400048
      (by decide) ⟨30, rfl⟩ (by decide +kernel)

  private theorem rb126 : (⟨[⟨3,9,false⟩,⟨5,6,false⟩,⟨23,2,true⟩,⟨53,2,false⟩],841,1⟩ : Box).Closed :=
    replayCloses (.nil)
      21 226 0xa54fedd8b8f20757bdbfa958e4bd00281d9d999ad0b9da6c2f2006f993c9c8e564dd00000db9436d66e6f367b8b0bc8077a9afedafe93b40481bcfb767d3c5e809001ddda1e678394e8bd2a6031a9bd8d96f364f2024240335b43d2ec78bd01232aef98b4b7da1ff6cf2045d351b35c9a1ceb3c80000000000244d9fcc46f767b2b63fcf2be97a0240004bdf409129ffc8
      (by decide) ⟨420, rfl⟩ (by decide +kernel)

  private theorem rb127 : (⟨[⟨3,9,false⟩,⟨5,6,false⟩,⟨23,3,false⟩,⟨53,2,false⟩],899,1⟩ : Box).Closed :=
    replayCloses (.nil)
      14 309 0x14d97d6d57bd92f6bfd735c2c981679b83e2e5757b3d3260241b4e7b5dd7e2fabc972de6bc2bd01202ccef5a7e5eab86f55d97a024240014a1e812a7eff91fb03ecf17c745c91302a723ecf87fdd1c9d301207dd595d57dafbd93f40ecd91ff73be5e560bb2f404804f79daf64f4eef1f1c564048000004a9fdf98ca549c5fa745f8e6bb2f4075ded67f9f97ab2b55d97a0240350dd7cdd2fd7fd7f4bd032c1b6c6733c3a5d1cac2f20006da9e37bb4d94eb72cd7639ae979000000a7f74095327f9126a65737c7671716ccd01efad2f2ecc764d180000095387f98
      (by decide) ⟨449, rfl⟩ (by decide +kernel)
end

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
mutual
  private theorem rb128 : (⟨[⟨3,7,false⟩,⟨5,4,true⟩,⟨23,2,false⟩,⟨53,2,false⟩],625,1⟩ : Box).Closed :=
    replayCloses (.nil)
      15 190 0xaa8637af0d026d9e4e6b49db617dbcb43c5da0003273bce06dbe5c8fd3b2f4048480008c9e8128ebff209e9b070686f7d7db0ac809000478f409449ff9010a54af589503a958d9b55a4cd002e9a5ea171c30000e1cd5bc6d499a02405099aeef37690300000012881fcc002513df9848
      (by decide) ⟨312, rfl⟩ (by decide +kernel)

  private theorem rb129 : (⟨[⟨3,7,false⟩,⟨5,4,false⟩,⟨23,2,false⟩,⟨53,1,false⟩],513,1⟩ : Box).Closed :=
    replayCloses (.cons rb128 (.cons rb126 (.cons rb127 (.nil))))
      20 193 0x69d1b4f9bebfabf239aecbd010c2c8d27bde594f87676809034cee69b65ef38aeabd585da0003af8baaf15f7b45ed7d3a60652ad677db8d8cf73b3b400000012a637e612012276ff3196a7ee9f9765e16abf1c2f20732bb3d91b2f3e5b23400000024afa0489cbfc848012278ff30911b3d025107fc8012e0bf9848
      (by decide) ⟨256, rfl⟩ (by decide +kernel)

  private theorem rb130 : (⟨[⟨3,5,false⟩,⟨5,3,false⟩,⟨23,2,false⟩,⟨53,1,false⟩],161,1⟩ : Box).Closed :=
    replayCloses (.cons rb129 (.nil))
      20 319 0x25c1bf30e6154eb79bcdb6e9c3010f67c3e1f8e6b92260724ecbc1c17cb25e8006de66fdbbf49e403dd5eaeddbf8ed1bfafa44c0480088ee8128befe424025c97f304b9f535cef8ca7a54c075b6eaf99d337b48d00003a2f409763fe4241d77d025d1ffc8ee3e812e63fc8004bab7e61200b1e8120a3ff232f5a74e2e24600011dd02417dfc81bcf593e5300254cb6dbaa53a5fed9e400000029ba04823bf90144e773b8b8c98000092fbfcc24098f409247fe424024cf7f98
      (by decide) ⟨80, rfl⟩ (by decide +kernel)

  private theorem rb131 : (⟨[⟨3,4,false⟩,⟨5,2,true⟩,⟨23,1,false⟩,⟨53,1,false⟩],65,1⟩ : Box).Closed :=
    replayCloses (.nil)
      18 150 0x2694540298f50c9804d3d795b17a024030532012556d5ed3000a798f5eb164048000f99c35b12a02400000012e812c5f90900911f98662b5ebcf40182943c8045aa97af0d0120000
      (by decide) ⟨32, rfl⟩ (by decide +kernel)

  private theorem rb132 : (⟨[⟨3,3,false⟩,⟨5,2,false⟩,⟨23,1,false⟩,⟨53,1,false⟩],55,1⟩ : Box).Closed :=
    replayCloses (.cons rb131 (.cons rb130 (.nil)))
      24 205 0x1219f7409311fe4122727f4efd25e80752cd5bc7664ed03286ac50d9c35aca01201a21a3bb19a005adddf5f6e3f400e737496fce2c97a0242eac6c7162fda580000662f5f5c6e9eabb0368a110d9d25d972b6dd2f404800000012643f9848049bf7e61201262df9848012b5fcc0093ef9848
      (by decide) ⟨27, rfl⟩ (by decide +kernel)

  private theorem rb133 : (⟨[⟨3,5,true⟩,⟨5,5,false⟩,⟨23,2,false⟩,⟨47,2,false⟩],2739,1⟩ : Box).Closed :=
    replayCloses (.nil)
      22 292 0x4804956febfcd5bc0f4c24d5bc4ff0424ee2f46f4ebaf0ecbd00b7542e8c99a169e400183fe8f409307fc3ff2004983fe0fe606dbf0fd024db7fbff9090deffd7d024defeaffc839dd6abc97938b978bb3c8000024cb7c0fe60012677fedf9848049a5fe2ff311f5a8be93000683c4fa049a0fdbfe4009329f4bf98180fc3d024c07b9fe40024cc7d37e619f74bd024cfbdfff2067dc4fa0499f7dbfe40024c9bc6fcc240091589fdf7cf4c25f41ff04
      (by decide) ⟨1369, rfl⟩ (by decide +kernel)

  private theorem rb134 : (⟨[⟨3,4,true⟩,⟨5,3,false⟩,⟨23,1,false⟩,⟨47,1,false⟩],151,1⟩ : Box).Closed :=
    replayCloses (.nil)
      21 159 0x3691c1ddd3b326e8094ceeddfb1130010e9230dd00032bd550c940001963d66f0006289e9cdd326e81340f8fefeeafefcd9da00000002bbe81251ffc8a3758cf0bd2e2b91e9fa00000092e3f98480496efcc24024dd7f9848
      (by decide) ⟨75, rfl⟩ (by decide +kernel)

  private theorem rb135 : (⟨[⟨3,4,false⟩,⟨5,2,true⟩,⟨23,1,false⟩,⟨47,1,false⟩],77,1⟩ : Box).Closed :=
    replayCloses (.nil)
      19 193 0x2409093a6adee7250e4865a5450d9eb4b20000d8746c8d1af69da000000366e99926660b320b30782c90d8a1a8d5a7784c04889ad9b718b2e53b20256b10a98000009346fcc00965ff30900972fcc2085a7990122aa56a1ba01356d55ab63f40480000
      (by decide) ⟨38, rfl⟩ (by decide +kernel)
end

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
mutual
  private theorem rb136 : (⟨[⟨3,3,false⟩,⟨5,2,false⟩,⟨23,1,false⟩,⟨47,1,false⟩],49,1⟩ : Box).Closed :=
    replayCloses (.cons rb135 (.cons rb134 (.cons rb133 (.nil))))
      26 198 0x2496f5f52391c2fb7db8ac800051a5f40951f3ff2004a8f77e602f6e2f36f3c7e819b8bfde595e593260000911b5fe6008e8fa0488dfffc804a6f3fe60004a6a1fd14efa6128ab7f8224009059bfdce7a612e6ffe08900906eff30908374092adfc81977409301fe41874090cfc848
      (by decide) ⟨24, rfl⟩ (by decide +kernel)

  private theorem rb137 : (⟨[⟨3,5,false⟩,⟨5,2,true⟩,⟨23,1,false⟩,⟨43,1,false⟩],91,1⟩ : Box).Closed :=
    replayCloses (.nil)
      18 250 0x28f8d71ad93244c0641a7ac5903915ab546b349500a856ad7ac48c000480049baff31946cd0dd00001260bfcc654a942f4063abd7a8d8dd000a63d434601d4c69e640a42c5e598b20240071e578b6b55e3648326a87d62c80000000c67d024cf7fc866af3552c590066a15af320115468eac9ad5acb202400000dbba049a0ff212012f5f98
      (by decide) ⟨45, rfl⟩ (by decide +kernel)

  private theorem rb138 : (⟨[⟨3,4,true⟩,⟨5,5,false⟩,⟨23,2,false⟩,⟨43,2,false⟩],913,1⟩ : Box).Closed :=
    replayCloses (.nil)
      21 236 0x126b036a4616ce9da0241216230d95cdc5e59582ec7ca000000002494cff309009255df9860b4bfce074bf4f4bd00004929efcc00249637e61222f1f4094563fc88f05f1d9cec913012004a29efcc24454dd0251477f222856313d3ba4f201962e1a5c3ba4ed00030a360dacd5b49500656a52df0490000002d3f409055ffe424017f74090593fc8
      (by decide) ⟨456, rfl⟩ (by decide +kernel)

  private theorem rb139 : (⟨[⟨3,4,false⟩,⟨5,3,false⟩,⟨23,1,false⟩,⟨43,1,false⟩],91,1⟩ : Box).Closed :=
    replayCloses (.cons rb138 (.nil))
      20 313 0x240249ba7fc926e60b3454925dcc071612c3a3f822402414bf906e98499fff823decb550dad9d3c8006f676bf395d2fd3d226000052b7d0254bbff2037a6c63bb5c5e80000254f6fcc050b943071e40e033ba7db400e46b2d638ed02a7e2b9b83c4e800004fee812264ff202737409133bf9110842c62001167e8128efff200128edfe618c3e7eb75c4e809002514df9803acf409703fe42425be8124effc8481a6fa0498dff8d74c252bfb8
      (by decide) ⟨45, rfl⟩ (by decide +kernel)

  private theorem rb140 : (⟨[⟨3,3,false⟩,⟨5,2,false⟩,⟨23,1,false⟩,⟨43,1,false⟩],45,1⟩ : Box).Closed :=
    replayCloses (.cons rb139 (.cons rb137 (.nil)))
      13 87 0x2b562f2d62c81976a1b3d460241d1794bcc014c56d0000048d7e60045d0250bf2123369952982c99a2c62d04
      (by decide) ⟨22, rfl⟩ (by decide +kernel)

  private theorem rb141 : (⟨[⟨3,6,false⟩,⟨5,4,false⟩,⟨23,2,false⟩,⟨71,1,false⟩],127,1⟩ : Box).Closed :=
    replayCloses (.nil)
      22 219 0x64aa55b071e404851667169b8bd0121200fa8da918993c809090299ae0e87c3fec953039dd96d6743d1f6763b3740481202c543edceed64f2031e4fe76b93a5e97a6680eb75a55da6c67a3d3b4000000000065dd7afdbdd859d9edb76cc5a774108ccc6a6fcd364e9809091d4856b37addbacf202419b49c67f591ff79656cd18000000376e8126bdfc8
      (by decide) ⟨63, rfl⟩ (by decide +kernel)

  private theorem rb142 : (⟨[⟨3,3,false⟩,⟨5,2,false⟩,⟨23,1,false⟩],63,2⟩ : Box).Closed :=
    replayCloses (.cons rb114 (.cons rb141 (.cons rb118 (.nil))))
      24 137 0x6a35a27d26024218df5f9f9a6c97a02424775a313f3f32b8b2b0bb40000000122dfcc24025abf984804917e606c50e6ad8ed00642c62b5e49601212000b9d02473f2120000
      (by decide) ⟨31, rfl⟩ (by decide +kernel)

  private theorem rb143 : (⟨[⟨3,3,false⟩,⟨5,2,false⟩,⟨23,1,false⟩],43,2⟩ : Box).Closed :=
    replayCloses (.cons rb142 (.cons rb122 (.cons rb125 (.cons rb132 (.cons rb136 (.cons rb140 (.nil)))))))
      27 103 0xee52f5ea301202b54a1da024725885e8091ca56a1ba0005b3df86fd6d5b6480909026bb44eac9f5a7280000000053a6000000
      (by decide) ⟨21, rfl⟩ (by decide +kernel)
end

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
mutual
  private theorem rb144 : (⟨[⟨3,4,false⟩,⟨5,2,true⟩,⟨23,1,false⟩,⟨41,1,false⟩],101,1⟩ : Box).Closed :=
    replayCloses (.nil)
      23 278 0x1b691ab79e80904f45e50e6925402690b4958b20309cdeb750c6d3c80002034b746bd25e8007a0caf3cf5a5903960a5e030006e7aa5eba0000002edd024af7f209c3e64fec54c0ca562756c66809011b51f566ead5acf20098d43d3bb1da00000024dcff9848049b6ff30cd7d024d2ffc80049b0fe6120126cdf98a42952f0d0060c52f5895029e7a9ded300000abf40915ff2120
      (by decide) ⟨50, rfl⟩ (by decide +kernel)

  private theorem rb145 : (⟨[⟨3,6,false⟩,⟨5,2,true⟩,⟨23,2,false⟩,⟨37,2,false⟩],503,1⟩ : Box).Closed :=
    replayCloses (.nil)
      20 269 0x53730bc66b63244c04875f9a58bcde6e774fd0120008bb7d02517dff90454be8128bcffc84804a2d1fe6031b278f36664fd012024c6b71333bdbf30a54048000128a5bf309002415cfe6198b0615301200482cdfe600b17d024159ff909017f74090593fc80b3ba0482fefe400cf3f409327ffc84866374093237fc80a06491d2c64b20000913c7f3147156f1f09800012dba04893dfc8
      (by decide) ⟨251, rfl⟩ (by decide +kernel)

  private theorem rb146 : (⟨[⟨3,4,false⟩,⟨5,2,true⟩,⟨23,1,false⟩,⟨37,1,false⟩],135,1⟩ : Box).Closed :=
    replayCloses (.cons rb145 (.nil))
      19 273 0x8c2ec6b4aab920047f7409464ff208eee8128c1fe4115285e8000251edfcc016e6ac59000012ea7fcc24025c27f3006c72697b681b50f6d2071da00009716fcc001a7e8120afff20120adfe628c4d2c9f7d000095f409072ff222c69a799000bd66b5ed3008d5084a80000096fa0493bff2121a6fa0498dff90d57d024c2ffc8e63d59eda000009319fe6120
      (by decide) ⟨67, rfl⟩ (by decide +kernel)

  private theorem rb147 : (⟨[⟨3,3,false⟩,⟨5,2,false⟩,⟨23,1,false⟩],31,2⟩ : Box).Closed :=
    replayCloses (.cons rb143 (.cons rb144 (.cons rb146 (.nil))))
      17 230 0x480d1f471a417df984984fe0891c742d4897e6128be080905297d014a98bfcc241fbfc1064dd024c3bf9bbab130787759894eb84804af7cc0900905edfbaafa612ecbfc1048049acefd4d5f4c2548bff044804ba0fe5bbae62599834b52998ad58844801253bf316e9849977f0415740932fe424024dbe6000
      (by decide) ⟨15, rfl⟩ (by decide +kernel)

  private theorem rb148 : (⟨[⟨3,5,true⟩,⟨5,5,false⟩,⟨19,3,false⟩],115,2⟩ : Box).Closed :=
    replayCloses (.nil)
      20 227 0x51d2f52d92b25e800333f4c048e8fd687f56c5b3b400019cf5c2686168aba2862c5acf411b6fa61a6fa506c4acdb210f2cd9628635d89dadb697974bd01206e3d4782cc5ac1c42ca56a9aac5154ebdfab63c8090379f4c5ec0d6f1b2b497a033c755ebdba4f202543242eec7680123badbe9300006b3e986d3ea292370d2b7258e5e6cb1683d04000000120
      (by decide) ⟨57, rfl⟩ (by decide +kernel)

  private theorem rb149 : (⟨[⟨3,5,true⟩,⟨5,5,false⟩,⟨19,3,false⟩],105,2⟩ : Box).Closed :=
    replayCloses (.cons rb148 (.nil))
      16 211 0x14697150cae0f174e98090a7a714a57fb25e80001add0241ddfc8480490bfe636b9c6327fbedf6d97a00077349c17edb1c9530120f59af0cb6f42feb33400000517a04963fe4240248cfe62a9575c1e2e2c9530120236b9bb3359dea16c8d000dd6b72c77971ba6e809001f1f45a6ce9dcb4385da00000082fa04953ff2000
      (by decide) ⟨52, rfl⟩ (by decide +kernel)

  private theorem rb150 : (⟨[⟨3,5,true⟩,⟨5,5,false⟩,⟨19,2,false⟩],101,2⟩ : Box).Closed :=
    replayCloses (.cons rb149 (.nil))
      17 183 0x172b537fb2b2ba5e8090150ccc4e0eb4953002ac89a595fae2e97a03af77b536c7ab7699300000048297f309009074fe610c2f1b5e38b268c0485df4585c5c592f4008fbbb9ea72bcb268c0000000483d7f98dbc1617c71230043cd85b3d62f404800002c7a04828ffc8048
      (by decide) ⟨50, rfl⟩ (by decide +kernel)

  private theorem rb151 : (⟨[⟨3,6,true⟩,⟨5,6,false⟩,⟨19,3,false⟩],129,2⟩ : Box).Closed :=
    replayCloses (.nil)
      20 339 0x80f4c72d3d4e338cf16c72bcb0bb40138dfd45e8e17aba1d9230006bae20783fd93b4048000176e9963417b2ade5968b14dba9a4950b56e0f753d7a3562ab7513969c919df747edb1d9da04ce156a6de7ababab66e8009002cdd53579679aaa58d216ab2ab149ba08ce7ae6272f50ae5d87560d558b59e8209e6cd6271697e79696971790376f7e74b63a1eac4ece980000c67a0b144d56ad4b5aac1cb16d3d0186284295e84ab059eca83cc7865be986ebe9862be94e31084ad2562aa46f3558a34d46e37ebedd1e97a0240dc7a9b495834a179ea9532cb14351e98000000000
      (by decide) ⟨64, rfl⟩ (by decide +kernel)
end

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
mutual
  private theorem rb152 : (⟨[⟨3,6,true⟩,⟨5,5,false⟩,⟨19,3,false⟩],105,2⟩ : Box).Closed :=
    replayCloses (.cons rb151 (.nil))
      17 280 0x693f38d9dd24681071fde5a1eac97a024157ce4d0cf7fbcba5e817bcb6b3313c64c0003d353653756abd226024000094437e6004ba1ff309009735fe62ad3a6d5b71da006e574b741755c9fa0240025dc7f3091c67d025cf7fc84804b977e634f37d52b1cac97a01960e0e2e76648d01b8fd7491f2caf2d0e17680000009056ff30900904aff301be7b27db4b3a7b6668000020beb97b10a165321782b33558a048000
      (by decide) ⟨52, rfl⟩ (by decide +kernel)

  private theorem rb153 : (⟨[⟨3,6,true⟩,⟨5,5,false⟩,⟨19,3,false⟩],101,2⟩ : Box).Closed :=
    replayCloses (.cons rb152 (.nil))
      19 265 0x9b4d8437fb0b1bcb67680917b2bb3c1d8e564e980907058babb4eabd5a1eac4f17681e6ca1adc3a2fc7a5e80904cf93e1b2fa687d5d57676809000000254c5fcc0192e478a5fde5d5b3b40000a6cf409520ff9091491e812a41ff9090091267f318727f56fd8f2042e8b94e9597d5d5d2f400dda9defa735edbb5ec9b91c2bd0120000094be812279ff9090091347f98269fd8efb6800009139bf3090025173f980
      (by decide) ⟨50, rfl⟩ (by decide +kernel)

  private theorem rb154 : (⟨[⟨3,9,false⟩,⟨5,4,true⟩,⟨19,3,false⟩],141,2⟩ : Box).Closed :=
    replayCloses (.nil)
      25 245 0x345e89e65dd96fd9a6a705d90fa4b3e58b05e8255a3ea4697a93c809012bb64fcfa9dfa161790120001a1fa63a2b6e2b2665616870b740480019efa0c5597b8c2b45458b5df411a6fa489a4249297982c49a50798a1bafa628ecc7727f72f2f2d9a301212064be9359f95bf7d2e33c48ecd16282b26ca5a5c5e8090d7b7369d6a5cba7681d521a66fb8b677b23d2e9590000001bcfa60000000
      (by decide) ⟨70, rfl⟩ (by decide +kernel)

  private theorem rb155 : (⟨[⟨3,8,false⟩,⟨5,4,true⟩,⟨19,3,false⟩],133,2⟩ : Box).Closed :=
    replayCloses (.cons rb154 (.nil))
      23 283 0x754d8fee9e9d9d3b4048cdb6eef9a58e980900b77409283fc8c30b35e8ef2c97a0002edd024af7f208e8eb72796164bd012060bd54e495bcecb77ff4ce9678b16f3d04673d3ce12b23b529caf4f1a3cceaa7ee6e62d67a081bab5b4b0bed92f400baf8de94f3b2768000d77d31b66a6d37f622607326e726f6764d181c6f7ebafec68c000693d30cd7d31c86eaadf30b254c0481a2faee249415965aab063c83cc519bc3aa9bf5fd8ba5e8000cc7a6000000000
      (by decide) ⟨66, rfl⟩ (by decide +kernel)

  private theorem rb156 : (⟨[⟨3,8,false⟩,⟨5,4,true⟩,⟨19,3,false⟩],109,2⟩ : Box).Closed :=
    replayCloses (.cons rb155 (.nil))
      18 266 0xacd27d32bcb244c0480012e0bf98096e0f56af6c9d3000ed3d025c5ffc848e4be812ee7fe4151a3b0be7a02eef707d68f2f2cad9da0004db31da4e75a725e809000045fa0482fffc8480b9e8120b7ff2337dca5fa164a980c9563abf62f400bc7ce53ddd0ba76800000249aff311bd38adfb19301202f1fd0a98090f4ea999e9e9f1d3b406133b3bfb17974fd0120000159f4092ffff20000
      (by decide) ⟨54, rfl⟩ (by decide +kernel)

  private theorem rb157 : (⟨[⟨3,8,false⟩,⟨5,4,true⟩,⟨19,3,false⟩],105,2⟩ : Box).Closed :=
    replayCloses (.cons rb156 (.nil))
      13 79 0x30dcd0e4d2cefed2260346df6352ee92f40482f7171b43f4980900009458fe6004a307f309114dd02511dfc80
      (by decide) ⟨52, rfl⟩ (by decide +kernel)

  private theorem rb158 : (⟨[⟨3,8,true⟩,⟨5,6,false⟩,⟨19,3,false⟩],153,2⟩ : Box).Closed :=
    replayCloses (.nil)
      17 277 0x166bbade4efb43fee97a06189fdddc5b6ef74e981340f4ff7c72b2768009004375396d67cbcb2b6768007d3cd3b2bb2f13d2f4048001bcf4c13de7173bc392f40246b6f2fcd70b75e9c3012000b7b55e966bff76bd5bae278bb4048001befae8a55d2fd23bea9fc9ee6cb1436df4c137d636d6c9ed2c2c28180ccb6d647f9f0f56ced012000184f4c315f5559729f771b6d7f683d8f47c394fd72c501b1359d6763fec993013217ebd9e2460240325f5cf3ce4ed55d7870fb31df0b658a000000
      (by decide) ⟨76, rfl⟩ (by decide +kernel)

  private theorem rb159 : (⟨[⟨3,9,false⟩,⟨5,6,false⟩,⟨19,3,false⟩],153,2⟩ : Box).Closed :=
    replayCloses (.nil)
      15 342 0x88d2333b34b6dd3b400de1f4ed3a1d2e0f87668c00baea7434ab72e9da0043f70dcff7fb638585da001b50e4eb7671da01af2c9ad7594efba7681b6cdee1c771da0003d4dfaea769f0e4bd0000060bd2ae8d7b5af68caf4a8dfd57a95e4a6e62de7a08cc69b38b6d9346066ef76b4df9f6e2e9c30099f8f97f30baa56ced01200baeb653eaef395d3b4001201b4f4ca2f2a62a2f355e69663159986c5befa08bbe9c6cee8f87fac76385da00523630d81f76c9ecf6179001a8989ace3b35c17a5e8090000c77d30499c1b523b3fbf59e40481a4f4c355f4c315f4957f357ff2f607febd570a5fb293558a000000
      (by decide) ⟨76, rfl⟩ (by decide +kernel)
end

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
mutual
  private theorem rb160 : (⟨[⟨3,8,false⟩,⟨5,6,false⟩,⟨19,3,false⟩],139,2⟩ : Box).Closed :=
    replayCloses (.cons rb158 (.cons rb159 (.nil)))
      18 241 0x4f8a94e2bd5d5fafeb857a02451a4e16173b5b4bcaf15e16e80158374766db4b2b2b0bc80902439a4f3b63338b29db77b2b2391f2f2000000000bf74debc2c5feabb515eaaae952fed7cb15c7d04538bd76723fec953012049ba61ad253e1df7f62e97a02408374c00ebc9caf0f96564d18090028dd24eaab67fd1d88fc581b3dfb56fe35962837410333dd1a9787fdd3b40480185fae4bf0b1e10859efa52bc42e58b73f41000
      (by decide) ⟨69, rfl⟩ (by decide +kernel)

  private theorem rb161 : (⟨[⟨3,8,false⟩,⟨5,6,false⟩,⟨19,3,false⟩],133,2⟩ : Box).Closed :=
    replayCloses (.cons rb160 (.nil))
      18 146 0x619dc9d0ef72ff74765e8090a7068727e777ce9e40c36a3b1da5b6ef749d0189d38395fecad8eced0120120e13bb876392a6071f256daaeabd589d97a0002424f1536b72fed775dd7f5c2bd01212090da69d0e965616ced00000000121e980
      (by decide) ⟨66, rfl⟩ (by decide +kernel)

  private theorem rb162 : (⟨[⟨3,8,false⟩,⟨5,6,false⟩,⟨19,3,false⟩,⟨127,1,false⟩],129,1⟩ : Box).Closed :=
    replayCloses (.nil)
      18 212 0xd57626fb1ac7a395b2f40e26d6ebd3cd93b40139a2be5735dd775e9da000030db3a736dba768194a8cf87fdd595d2f40e78ecd2eaec715e953012002abe574b2bab55e9c30121218c76a6770fe64ed000003281c599d0f164bd0000f9b399fb78b85e5d589e2d1813617e5e07d5e5bf5761dfeb85ba00242400000028bd12cb99e6a46a18505b98f4530d8af3d04
      (by decide) ⟨64, rfl⟩ (by decide +kernel)

  private theorem rb163 : (⟨[⟨3,8,false⟩,⟨5,5,false⟩,⟨19,3,false⟩,⟨113,1,false⟩],115,1⟩ : Box).Closed :=
    replayCloses (.nil)
      27 266 0x2e6cd696fb5ac7a5e81cc60bd2e4bb1e8f4bd00995e974bcbab244c04800ddee36cfee8e48981574fec9959592a6041b2e93e2f73bce4898004cf5b83fb87abebdae270bb4044c5b29d936a6767172801b4a476b19d2dd7d391f0f1468090619d8379ed75bebfd715e2be2dd01cd8c8db757660715eced0091a5607cbe5eaf15eced000000120000012eb3f980b4a1d1e97fd932602ec0ef527c3dd43a1d9da024001c77d025c1ffc848eabe812e17fe424025c67f98
      (by decide) ⟨57, rfl⟩ (by decide +kernel)

  private theorem rb164 : (⟨[⟨3,8,false⟩,⟨5,5,false⟩,⟨19,3,false⟩],111,2⟩ : Box).Closed :=
    replayCloses (.cons rb163 (.cons rb162 (.cons rb161 (.nil))))
      19 168 0x5b650ec7a3c5e8026ca4f75f756574fd02ad6eebecae274048048c3ddd9fd8b5bdb8b65e80d07c6266bb5daed7f7e85a50a02424024654678bf1df7574bd03286c28ed0e17b3fee8e176809001a38a96578bb1d9da02400000a6fa83e6ebed0dfd515f37b53fdafcb658a13d0401200
      (by decide) ⟨55, rfl⟩ (by decide +kernel)

  private theorem rb165 : (⟨[⟨3,9,false⟩,⟨5,6,false⟩,⟨19,3,false⟩,⟨103,1,true⟩],1137,1⟩ : Box).Closed :=
    replayCloses (.nil)
      15 196 0x932bfda4e470393a6026d0e3b8b23c76809056f7627a64729c9da024095919df71bcb27e80909000054be8120bcffc8480ac7a0482a3ff21eb9a5e5fee2a602439b1b3ebedcec92301200000482c1fcc453a1c3c9e0df74ed000048281fcc052e6f3646eb03d274048ca9386dd71b8d1800000905bdf98
      (by decide) ⟨568, rfl⟩ (by decide +kernel)

  private theorem rb166 : (⟨[⟨3,9,false⟩,⟨5,6,false⟩,⟨19,3,false⟩,⟨103,2,false⟩],1271,1⟩ : Box).Closed :=
    replayCloses (.nil)
      18 222 0x3d49cf7db7d9af15d0ec89810ba1c1da735e1bdbb7d2f404808ba7a04a297ff21222a9e8128b6ffc8033a16771bcb27681ddd4ed1f199e9d9856404814d41ff6fb15f57a64c004c9729fe85fed0fdb15d0f56968c0486bca66627fbede59585640000000128a27f30009450bfcc135bfaa63b29eae9a3012008a17d025169ff9166cbbd69d2b2f79d57644c04800128ba7f98
      (by decide) ⟨635, rfl⟩ (by decide +kernel)

  private theorem rb167 : (⟨[⟨3,8,false⟩,⟨5,5,false⟩,⟨19,3,false⟩,⟨103,2,false⟩],1073,1⟩ : Box).Closed :=
    replayCloses (.cons rb166 (.nil))
      18 175 0xab279bd3cb8d91e9da02475a9df7e61bed755e9fa0240af64e9af79de7274c0369ae8d2c5f9f9a5b23404836c99acea9aec0f66dbbdc5e40480000004a2a6fcc65eb07c3eafabaaf4bd0075facec1eebce4fd006ad794573f5c9f9c5c5a5640484800000b4fd024157ff90900905fdf98
      (by decide) ⟨536, rfl⟩ (by decide +kernel)
end

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
mutual
  private theorem rb168 : (⟨[⟨3,8,false⟩,⟨5,5,false⟩,⟨19,3,false⟩,⟨103,1,false⟩],105,1⟩ : Box).Closed :=
    replayCloses (.cons rb167 (.cons rb165 (.nil)))
      21 90 0x2dd296dbb329c99301239ad86e2d2f0e3ba768032f53e5e2767140febb1c28980000000024ca5fcc03217a04991ffe4240093267f98
      (by decide) ⟨52, rfl⟩ (by decide +kernel)

  private theorem rb169 : (⟨[⟨3,8,false⟩,⟨5,5,false⟩,⟨19,3,false⟩,⟨107,1,false⟩],109,1⟩ : Box).Closed :=
    replayCloses (.nil)
      21 259 0xdce74d78aeab93260240d6b47495c181e9ba02ef0c0ef71edfdfd9aec7639af979000c9e9cd6939d0bcbc3d595a51a0240900000952dbf30867b0383237dc6e9da0246ed0db796d38592f4048000294dd02548efe4555d9539f4ece3756cd18090000244a5fcc74f1b5a97abbae4c9809016d4f76140fd391e9da024001d6e57b9c57c5b25627e3c51a0240000000913f7f984827cfa0489c7fe424129ba04891dfc8
      (by decide) ⟨54, rfl⟩ (by decide +kernel)

  private theorem rb170 : (⟨[⟨3,8,false⟩,⟨5,5,false⟩,⟨19,3,false⟩],103,2⟩ : Box).Closed :=
    replayCloses (.cons rb169 (.cons rb164 (.cons rb168 (.nil))))
      28 249 0x6f4e27b4b55c37a1d97a02465c375dadb7171ba68c0480036abef6b6d7cbff5f8b9aeeb9ae97901236e541b9a5b7dfee779797fb2b2ac8002400000135bac366499b9712cc933713c99b97655c4e55c1aac82dca6e690b8a08e0ed773f6ff6c72b65e81cb7559df995bcecbd012000489edfcc24a7a6f767b9eebceebb2f40480008c5e8128e3fe424454f40946dff9091183d025153fc800
      (by decide) ⟨51, rfl⟩ (by decide +kernel)

  private theorem rb171 : (⟨[⟨3,10,false⟩,⟨5,6,false⟩,⟨19,3,false⟩,⟨101,2,false⟩],1789,1⟩ : Box).Closed :=
    replayCloses (.nil)
      19 350 0x33d4ac7bddd1d94e070bb404825361b79e8ca77ddcff3d5c5da03999e9f2ffdf2fab63e5f85ba04559e2fe74b67ee5d59595a51a0240915b1dcedb77abfd9c5763bfab6ddecb7e968c048004802ac5e91ef634c8fd76193e123f1d7f5db6ee17dda2f8de4616e63561fa089155cf409556ffe40d5bcbce46078d81d9ba0240009553bfcc24025542ff30b3850dcaf2bfe9fd7a64c0eb93a1ad1389c97a06db5cafab81c17fb4bd00048e5130727ebe375c5bae29500292e4bece077dfed8f56ab89c4f9768090124bc6fe5f1bd8e579bc4e57f9bd2dd000035b56ddedf7738ae2755cd735d2d18000001552fa04aaf3ff2004aa91fcc24009557df98
      (by decide) ⟨894, rfl⟩ (by decide +kernel)

  private theorem rb172 : (⟨[⟨3,8,false⟩,⟨5,5,false⟩,⟨19,2,true⟩],101,2⟩ : Box).Closed :=
    replayCloses (.nil)
      31 96 0x4924924924924924924924924800000012492492492480000000000480000
      (by decide) ⟨50, rfl⟩ (by decide +kernel)

  private theorem rb173 : (⟨[⟨3,7,false⟩,⟨5,5,false⟩,⟨19,2,false⟩],101,2⟩ : Box).Closed :=
    replayCloses (.cons rb172 (.cons rb170 (.cons rb171 (.nil))))
      23 284 0xe0335b1ca77df4e472385a30120ab87a04aab9fe42402556f7e6191b568e9ada5b6e2c2cd02b61b8a57eeae27a5e8006475b17f68fc72b4385da0000255477e61200aa5e8122b7ffc815e738d4deaf9687a64c048caddbb4efabf672b45da8fb2f4065fe7e05db64be2e162713b1f8f979012048000048a95fe6120122a87f30cbf0ff40d8e56c5bd2f40ca464d189bafcc76f62fb69728000024540fe6002abba048a81fe42465edd02596f7f2120128b17f98048
      (by decide) ⟨50, rfl⟩ (by decide +kernel)

  private theorem rb174 : (⟨[⟨3,6,true⟩,⟨5,4,true⟩,⟨19,3,false⟩],109,2⟩ : Box).Closed :=
    replayCloses (.nil)
      26 350 0x31ae0e17db8bd0002e7a0482dffc80120a9fcc41f219bd6e92340484b06b78ece3460126348c8ece3b40000120eefcc0434a5eab56f565900aa5ab14ab49e4048004971fe60ee1a5eb7630600087740927dfc873137be7171130120049b9ff3009313fe61b6fa6194f515542cb70da6aa6cb1693d0466be9ba719d9665ffa9c2b3164be82305f4d62b29430715328b16e3d052aa10c5b962acd4f4798b79f5114d0ed707ed95a1f2d9ba0000cc7a61b0f506dd49ee5753362c5acfa64cc95a2a4bccb782cdcc590f5100000000000
      (by decide) ⟨54, rfl⟩ (by decide +kernel)

  private theorem rb175 : (⟨[⟨3,6,true⟩,⟨5,4,true⟩,⟨19,2,false⟩],101,2⟩ : Box).Closed :=
    replayCloses (.cons rb174 (.nil))
      27 145 0x2f69272a74ceee5b3b404800128a5fcc112be8128e5fe444f7409466ff90025d17f300972efcc1c1ba04bab7f200124924924924924924924920000000000000
      (by decide) ⟨50, rfl⟩ (by decide +kernel)
end

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
mutual
  private theorem rb176 : (⟨[⟨3,6,true⟩,⟨5,4,false⟩,⟨19,2,false⟩],101,2⟩ : Box).Closed :=
    replayCloses (.cons rb175 (.cons rb153 (.nil)))
      31 64 0x12492492492492492492492480000000004800000
      (by decide) ⟨50, rfl⟩ (by decide +kernel)

  private theorem rb177 : (⟨[⟨3,5,true⟩,⟨5,4,true⟩,⟨19,3,false⟩],105,2⟩ : Box).Closed :=
    replayCloses (.nil)
      22 323 0x871235b763c8091c752d2e77164bd008a87c7e677efda4680900000923bfcc3535f5bbdbfa4bd002335d327f62f4000012457f98407a0491dff232f7297aa543a780018cf597a96583c179375cb16d3d301958b251262d34b3558b7df511b6fa619afa7adcc842a4bca2c50c57d61b064d8a85a9253658b25f44f33d1652a5eaa9b2c5a2fa88d87a1bd798a4d2c3598b59f5c1aa18c5e72f3458b21ea2319ae266cbdcb8bcb0bb4001acfa5df50aaac4c590f4126951373ebe7f699a000d07a6000000000
      (by decide) ⟨52, rfl⟩ (by decide +kernel)

  private theorem rb178 : (⟨[⟨3,8,false⟩,⟨5,4,true⟩,⟨19,3,false⟩],103,2⟩ : Box).Closed :=
    replayCloses (.cons rb157 (.nil))
      14 155 0xcdc5fab7f79687a5e8090025491fcc6ef94d81fcfb64c980000953a7f98832afbcb3b193000291dd0254befe425c38bb3eba0240c6b7a6b03fa4ed002a1c6e8d273a4ed0003aa952bc54000000489fbfcc01357d02448bff20
      (by decide) ⟨51, rfl⟩ (by decide +kernel)

  private theorem rb179 : (⟨[⟨3,8,false⟩,⟨5,4,true⟩,⟨19,2,true⟩],101,2⟩ : Box).Closed :=
    replayCloses (.nil)
      29 87 0x4924924924924924924924920000001249249249200000000000000
      (by decide) ⟨50, rfl⟩ (by decide +kernel)

  private theorem rb180 : (⟨[⟨3,5,false⟩,⟨5,3,false⟩,⟨19,1,false⟩],101,2⟩ : Box).Closed :=
    replayCloses (.cons rb177 (.cons rb150 (.cons rb176 (.cons rb179 (.cons rb178 (.cons rb173 (.nil)))))))
      28 248 0x3d35e9818575dda7681c6168ea75afbfda1d9da00111b7b9ddac8e87a5e80481d6f8cf687aa8767681b62eece7f3aafbfdb3b400480000120a7bf30900905edf988c58dd1e5fec99300002c6e8120a37fc823533da5f6e326000024ca9fcc2452e7a04a96ffe40240042fa04834ffc8480483a7f98a6ab54bd7adda468006e33b9df6e226000016dd02413dfc804804848
      (by decide) ⟨50, rfl⟩ (by decide +kernel)

  private theorem rb181 : (⟨[⟨3,13,false⟩,⟨5,8,false⟩,⟨19,4,false⟩,⟨97,3,false⟩],9085,1⟩ : Box).Closed :=
    replayCloses (.nil)
      19 369 0x1958ea9ed98f2b687f673d9cf0a2602419bcef757a5fa6f25cd7cbff5e2dd01214d779bddc1d97acff4b7faf60dd2dd012369cfd7ec7950e1bda8f8d6cbece7d91fd95fd91fdb9fb57fb73febb40484800000afcf40915a3fe439d4e27eb0bfad4ae2db657f3e59a024015fdf40915e7ff21ebdca1647a7a696476dded2f2024c8ced3e9c6f8febe578bb406313c9c771edcafd5decaf35fd7ca34048048032577cc4abd6edd36d1bb76f67dfebb0ef67ddac18026bbbdd4ec87fafdafdaff37aaf56d07b31f643ead18000000057d7d02456affc82795313fb077497abe5e574bb40096335c1f67c3e5ff2fcbfafcbf4bb406303b3a60e2a2f470b75c379aec72a3404800002b0be8122ba7fe42415bee8122b23fc8
      (by decide) ⟨4542, rfl⟩ (by decide +kernel)

  private theorem rb182 : (⟨[⟨3,10,false⟩,⟨5,7,false⟩,⟨19,3,false⟩,⟨97,2,false⟩],7369,1⟩ : Box).Closed :=
    replayCloses (.cons rb181 (.nil))
      27 328 0xccbe6da5fe2d0ef6c7ff5d26e15e8091d2693959a56db6dfce478a0600a6464e6e0c903bdaa9b8395b1fee5c5b1fa802412c7d3dee9735a0beafe60bbcf57562713f2c8002400002457e7f98623e338da6e9760dd8f7b36edbbcd7ca34063caf63e6a61bf5ddbb17671b2a54048184d77c716266cbeda72bf30b2b43a1f9ca000000915e1fe612004a0e97f30900941f8ff309007e3d0240727fe424025fb7df98a32a55d74bebfd735d8370bb400012fdc1fcc1fbedd025fbbdfc848048a70bf984829df740914e47f90900259396fcc240247b7df98
      (by decide) ⟨3684, rfl⟩ (by decide +kernel)

  private theorem rb183 : (⟨[⟨3,10,false⟩,⟨5,6,false⟩,⟨19,3,false⟩,⟨97,2,false⟩],6803,1⟩ : Box).Closed :=
    replayCloses (.cons rb182 (.nil))
      28 251 0x1c872da1e678b63c58ef2d8e97680249cad6ef6c75a3b59cae2ed00eeb95afaeb716eb8b6dc51a0302e5bf5e07439af60becbd012018d77cb1edda33f1ed7abaaf979590000000004927a3fcc12f44c0fb7e6dbcbcb0bb400004927cdf98049274df98004af70ff984804af7c7f98483dcdf4091ecdff91ccdade58b8b3315eef6f2d57ab2a34000012dd85fe6004b7607f3090024bbb3f984807657d0243bcbfc8
      (by decide) ⟨3401, rfl⟩ (by decide +kernel)
end

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
mutual
  private theorem rb184 : (⟨[⟨3,9,false⟩,⟨5,6,false⟩,⟨19,3,false⟩,⟨97,2,false⟩],5529,1⟩ : Box).Closed :=
    replayCloses (.cons rb183 (.nil))
      17 149 0x49c23bea36b67677b2b8a340480123d9efcc0091ee37e612012ddd9fcc246ec4fa04b77b7fc8485d81e8125d9dff2120121db6fcc76f8f40976c9ff9076e0f40976d4ff2121b64fd024db9ffe4240258ee8124b7dfc8
      (by decide) ⟨2764, rfl⟩ (by decide +kernel)

  private theorem rb185 : (⟨[⟨3,10,false⟩,⟨5,7,false⟩,⟨19,3,false⟩,⟨97,1,true⟩],4151,1⟩ : Box).Closed :=
    replayCloses (.nil)
      24 274 0x1d6d0e76eb4bd3caf6768194289f4e87b3e3d2f40480aa9ba3abf9dd7daf4d181867393cbcaf97f1c57b32602405195ea26ebf595eaf161768091b49b9f8e577a6bf1fee6f8bb4048000014df74092991fe424024a6bbf30bb0db1f9e4e27f56767680013b60c4eced74f202400029b6e812533dfc848fa4fd025f67ff9090097d2bfcc39b519f278de593b40485a73c6f97f9f8e4c9809007d13e812fbb7fc84824d2f40949dfff21201213f3f98
      (by decide) ⟨2075, rfl⟩ (by decide +kernel)

  private theorem rb186 : (⟨[⟨3,8,false⟩,⟨5,5,false⟩,⟨19,3,false⟩,⟨97,1,true⟩],2965,1⟩ : Box).Closed :=
    replayCloses (.cons rb185 (.nil))
      19 219 0x7399cf706476d937400024d774094981fe424098bf40909bfff228fb0c2c1ad27680002647a0484c1ff9090024f70fe604eafa0484c5ff90900909f1fe6120127bc7f9804b8e2fe6000498d2fe61270fef979adbd5e93a0005dfdd025764ff212012ba5bf30900951fefcc025471bf30011fee8122393fc848
      (by decide) ⟨1482, rfl⟩ (by decide +kernel)

  private theorem rb187 : (⟨[⟨3,7,false⟩,⟨5,5,false⟩,⟨19,2,false⟩,⟨97,1,false⟩],1201,1⟩ : Box).Closed :=
    replayCloses (.cons rb186 (.cons rb184 (.nil)))
      32 267 0x34dec5f5d1cd75a2bd8ec78bb40480934207d381d17b582e97cf2da70bd5f9402400000241b17fcc51eaf54bbaff5fd7f1d97a024006c2f40906c7ff90901b7be8120da7ff21203787a04836e7f90900945d9fcc243af4f4093acbff9045eb2737ebaf8ecc295003ab3d575ecbbf1d17a44c0001d7c7d024eb63fc81d61ba049d75bf909016bddd0256b83fc8480484e6ff30024b677e612012e70fe6120122b17f98
      (by decide) ⟨600, rfl⟩ (by decide +kernel)

  private theorem rb188 : (⟨[⟨3,6,true⟩,⟨5,5,false⟩,⟨19,2,false⟩,⟨97,1,false⟩],879,1⟩ : Box).Closed :=
    replayCloses (.nil)
      18 250 0x7585d97d9e8f4627a5e809000915dbfcc24024562ff30558f4091547fe401513e8122bb7fc848cb87d025956ff915624dedf69607a768090bbcbc76b23b36dd3b4000c4d6749d366bfb96ced01212000049295fe6120124a47f309b93c3d37dc6e800de5addfdc7680254da9c5c5e593260166b3f2ff33bc72768090000025e3e8124ac7f901178f4094527fe42433e7a049947fc8
      (by decide) ⟨439, rfl⟩ (by decide +kernel)

  private theorem rb189 : (⟨[⟨3,8,false⟩,⟨5,4,true⟩,⟨19,3,false⟩,⟨97,2,false⟩],1685,1⟩ : Box).Closed :=
    replayCloses (.nil)
      18 211 0x58b547687e73b5bf62e2d2f200000024065bf30ebf3ba7b99fa745e9130120004bad3fe612012ea27f3087db434394ed72e9930121867d9d0edbb325e8091dbe5e36ebd375cd7c5b2f40032792da1f1f9cef2c28d0000004bab1fcc2400975ddf987a0725d368bd2e47a5e8090b3d26b2323b6c97a001cbee812e48ff212004b90df98
      (by decide) ⟨842, rfl⟩ (by decide +kernel)

  private theorem rb190 : (⟨[⟨3,6,false⟩,⟨5,4,false⟩,⟨19,2,false⟩,⟨97,1,false⟩],487,1⟩ : Box).Closed :=
    replayCloses (.cons rb188 (.cons rb189 (.cons rb187 (.nil))))
      24 238 0x93e37586fb4c0a9c76c7d386c67fb56ced00002aa5f40955e7fe40095523f9848aafba04aa91fe416f0eb7778e386006d76bbe3fa95f7e6ced00004aa8efcc2400915e7fcc1503d02454eff9000245677e6120128aa7f30900533e8120af7fc80bda9ce999592f4026e56767439ecf6f6ac2ed0000019bbe812663ff905367a04a907fc84800489f3f98
      (by decide) ⟨243, rfl⟩ (by decide +kernel)

  private theorem rb191 : (⟨[⟨3,4,true⟩,⟨5,3,false⟩,⟨19,1,false⟩,⟨97,1,false⟩],115,1⟩ : Box).Closed :=
    replayCloses (.nil)
      17 146 0x197ae9d3d4602405a855b76edda668027da7366c48c0481230f8e76ce5fd27e8187c9d4a96e9234048000d369717ca602400000c77d024c1ffc81ab6e87680900309e81261bfc8486e3e812663fc848
      (by decide) ⟨57, rfl⟩ (by decide +kernel)
end

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
mutual
  private theorem rb192 : (⟨[⟨3,4,false⟩,⟨5,3,false⟩,⟨19,1,false⟩,⟨97,1,false⟩],115,1⟩ : Box).Closed :=
    replayCloses (.cons rb191 (.cons rb190 (.nil)))
      21 161 0x37319cadb6f392f40480004a3bbf30911ede8128b6fe4779e812e47fc8004bb6ff3091d07a04b94ff23bf7409749fe413540d2f15000e2dd025cbbf909000904cfe612141e8124a7f9090dfba049a4ff20
      (by decide) ⟨57, rfl⟩ (by decide +kernel)

  private theorem rb193 : (⟨[⟨3,4,true⟩,⟨5,5,false⟩,⟨19,2,false⟩],101,2⟩ : Box).Closed :=
    replayCloses (.nil)
      16 225 0x1d562958ad2580480613d30c57d0dabcd526311b95a2c592fadb4b069eab16ea5658b45f510ad6c2dde35b17f62c2ed012001a8f4c55aa75e858592f40481acfaa38b28acf69b31643d04a3babcdea525e8090900c07a482928eb351b12439628234acdd659c3ebd42c4001a774c336e9801200001249249249201200000
      (by decide) ⟨50, rfl⟩ (by decide +kernel)

  private theorem rb194 : (⟨[⟨3,4,false⟩,⟨5,3,false⟩,⟨19,1,false⟩],101,2⟩ : Box).Closed :=
    replayCloses (.cons rb193 (.cons rb180 (.nil)))
      20 231 0x14ac696784ccd9048e8a9b7bf63a6000d17d41a5e0bd54490b33658b71e824989ad5b67664ed00a6d7e617a000de7d31cd5836da5e592f4020c6f6e2f2e2f4000643d30ca8c66c780481a0f4c371f51690b3512cb33458b51f411ab754c7a90a982d1ee6a997314755ab78f8ecc9da0240d9ba60000004924924920000012120
      (by decide) ⟨50, rfl⟩ (by decide +kernel)

  private theorem rb195 : (⟨[⟨3,4,false⟩,⟨5,2,false⟩,⟨19,1,false⟩],91,2⟩ : Box).Closed :=
    replayCloses (.cons rb194 (.cons rb192 (.nil)))
      18 229 0x12f5fcc1210a5e6400a874cdeda02400256bf311aa14af6501203575558ab73312cc5574100f5ea2ccb8966ecad10d356289bcf55bca6020acc51b164000b5d30c158fadd5a7696404848001248048b5ea97cba61662fcfb9a2c757a08c956a952ad25901658ade6404818f8f8e4dec5e80006ba60124800000
      (by decide) ⟨45, rfl⟩ (by decide +kernel)

  private theorem rb196 : (⟨[⟨3,5,false⟩,⟨5,3,false⟩,⟨19,1,false⟩,⟨89,1,false⟩],129,1⟩ : Box).Closed :=
    replayCloses (.nil)
      28 354 0x900952fdbfa2eb74c251637fc1120012fbfbf75dbe984ba9bff041aa72ddd33edd3f4048ca277b69f570de1be9fa0249e4fd7352c0f4ed002a9c50ace7d5e8585c56000000ab87d025556ff90915537409551dfc82da95e67970648980c6772705d97fd244c05ddec8f867b4bdba48c000048aa5fcc01533d02456bff9090096593f984804a285fe612190bd024c8fff224e253dac2e32601c9ed2da7e93000012659ff30914b9e812a5bff90900485e812247ff8347a612083ff70901c3e8120adff349e9849baff7090c97d024dcffc8
      (by decide) ⟨64, rfl⟩ (by decide +kernel)

  private theorem rb197 : (⟨[⟨3,4,false⟩,⟨5,2,true⟩,⟨19,1,false⟩,⟨89,1,false⟩],91,1⟩ : Box).Closed :=
    replayCloses (.nil)
      19 140 0x8b218bcc8117a6a1f6d0120198b1eda02407a91b999d50ba768187dbadd6ef707270c00000272c51a87349640008b0607564f8c4e96400000000b7a04baff910655a854c048004ad7e6120
      (by decide) ⟨45, rfl⟩ (by decide +kernel)

  private theorem rb198 : (⟨[⟨3,4,false⟩,⟨5,2,false⟩,⟨19,1,false⟩],85,2⟩ : Box).Closed :=
    replayCloses (.cons rb195 (.cons rb197 (.cons rb196 (.nil))))
      22 138 0x337c6f46fd8bd000587d02496ff90900921df986335c50bedfd25e804d13adbdfab62e913000b39ff74e6fecae4723857a0000000922df984801241bf309009371fcc240c1ba049ab7f200
      (by decide) ⟨42, rfl⟩ (by decide +kernel)

  private theorem rb199 : (⟨[⟨3,5,false⟩,⟨5,3,false⟩,⟨19,1,false⟩,⟨83,1,false⟩],143,1⟩ : Box).Closed :=
    replayCloses (.nil)
      23 225 0x4804997a9fc9b33e98493607f04f5952dbdf3d31dc1e5d9c5da00009339f4bf9848673f17a0499cfe3fe451d577b3b4bf75f2bd32600db35f96f61b75e4fd00006b3f47d024d67dfffc8486bbfe3e8126bbf63fc848049a77e7fdd386e98490e97f044804acf9ff30900092db3fc976fa6124beffc112012e73f961e984959fe0890d0fd024ddffc8
      (by decide) ⟨71, rfl⟩ (by decide +kernel)
end

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
mutual
  private theorem rb200 : (⟨[⟨3,4,false⟩,⟨5,2,true⟩,⟨19,1,false⟩,⟨83,1,false⟩],85,1⟩ : Box).Closed :=
    replayCloses (.nil)
      22 132 0x12120e9ad43b4048480cb14d76bb58585b2c81b4ea59981e6ece97a024090000000d5ba049b77f20ad51ab5ec5e809090066f40935ff21238e812a5f9014ab4c000
      (by decide) ⟨42, rfl⟩ (by decide +kernel)

  private theorem rb201 : (⟨[⟨3,4,false⟩,⟨5,2,true⟩,⟨19,1,false⟩,⟨79,1,false⟩],81,1⟩ : Box).Closed :=
    replayCloses (.nil)
      20 171 0x2592bd7b901212e63d34048480a4a1a5e59eb4f200000000933efcc75934ab794c0484800126ddf98272951b07cf5a590121202d255ab58ed0000193740930efe4240252bf3195ab3d70ce93940002574090afc80
      (by decide) ⟨40, rfl⟩ (by decide +kernel)

  private theorem rb202 : (⟨[⟨3,3,false⟩,⟨5,2,false⟩,⟨19,1,false⟩],81,2⟩ : Box).Closed :=
    replayCloses (.cons rb198 (.cons rb200 (.cons rb199 (.nil))))
      24 175 0x23ee3e39dc59326001bab66b7d717a05583ea96ead2790120000120e6fcc24227e81253ffc8485f7d024b3ff90a9abccd8f0009f5f3fbca6018714cfcfcfb64bd0000012527f309028be8124cffc848049b4fe61200499b7e60120
      (by decide) ⟨40, rfl⟩ (by decide +kernel)

  private theorem rb203 : (⟨[⟨3,3,false⟩,⟨5,2,false⟩,⟨19,1,false⟩],75,2⟩ : Box).Closed :=
    replayCloses (.cons rb202 (.cons rb201 (.nil)))
      19 169 0x245277d025487ff062f4c24147fdc24024877e63a7740977efe424726e812e1dfc8480e9e812097ff2120120f1fcc06afa04822ffc8480e9f40906eff909002411df984845ba0492efe4240d7ba04990ff20480
      (by decide) ⟨37, rfl⟩ (by decide +kernel)

  private theorem rb204 : (⟨[⟨3,5,false⟩,⟨5,2,true⟩,⟨19,1,false⟩,⟨73,1,false⟩],85,1⟩ : Box).Closed :=
    replayCloses (.nil)
      22 233 0x1aad79eb19a073c143740481a0c68d5b19300484812c52854c0662d31a62c800048c8cab294e9d65903a852b5eda032193aac6c64b200000000371e812627fe43652a166b5eb4b200331dd7ab56fda68c024e959bc54000001b0f409339fe46dda742f40834b06d7a8c00ab15aa5e600001af7409321fe4240256bf98
      (by decide) ⟨42, rfl⟩ (by decide +kernel)

  private theorem rb205 : (⟨[⟨3,4,true⟩,⟨5,5,false⟩,⟨19,2,false⟩,⟨73,1,false⟩],687,1⟩ : Box).Closed :=
    replayCloses (.nil)
      16 256 0x4df33b7690b174ed01202ed6b42c5c6c9ba02406f9938dbecac97a000015afa0482cbff202b64e8e8f4ece9da02449f353323238dd34600c86cafcff3b6c9d301200000482b1fcc24334fd024cafff21229dbe812a7dff90c6a68654371da0005367a04a907fc81bc717f48e2c9d3006303cbeb4b46969da055ed96c2decec9da000014ddf409531ffc848a74fa04a9bbfe4240485f409134ffc8
      (by decide) ⟨343, rfl⟩ (by decide +kernel)

  private theorem rb206 : (⟨[⟨3,3,false⟩,⟨5,2,false⟩,⟨19,1,false⟩],73,2⟩ : Box).Closed :=
    replayCloses (.cons rb203 (.cons rb204 (.cons rb205 (.nil))))
      20 208 0x2402485ff2416414890b162de7d04f5c6c0eb60e87254c048e303a4f47db8898000091317f309009123bf3127eba30df518000251a7fcc0009474ff309009287fcc240d47a049a1ffb974c244bf7134ad5ebc260058d34f11809001a52b86b4e92c80000096afe60004ae7e6120
      (by decide) ⟨36, rfl⟩ (by decide +kernel)

  private theorem rb207 : (⟨[⟨3,4,true⟩,⟨5,3,false⟩,⟨19,1,false⟩,⟨71,1,false⟩],201,1⟩ : Box).Closed :=
    replayCloses (.nil)
      29 313 0x1dbb65db757eb6e97a00341d3276b7afb83854024000000901c5fcc64eeb8a9b2b69c993003b5bada1fadd64ed004fd6a7bb7d95a1fcfcc29180902400002407f7f984803a3d024070ffc863bfb4de2fc723f1d97a01aeb73b69fe743e5ddab0bb4053b038dcdc326e8001e78bd4f8b99d2e87b3644c01f7870ba56b064c98000002407fbf309001c6e812031bfe42472dba04b93dfc84804b2c5fe61202a5f40905e7fe4240254d1fe0c9e9848227f04480fee8120c9fe6bbe98498dffb848
      (by decide) ⟨100, rfl⟩ (by decide +kernel)
end

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
mutual
  private theorem rb208 : (⟨[⟨3,3,false⟩,⟨5,2,false⟩,⟨19,1,false⟩],69,2⟩ : Box).Closed :=
    replayCloses (.cons rb206 (.cons rb207 (.nil)))
      26 264 0x1203c7a04824ffcdf7d309327ff70024c57f9574c24cbf8255660dea58a9809091183931af62f400642856ad8ed01ac1e9c7cc2eed3b400000065be8afd16d5ae2485cef82d92b558b49e8224309e81261bfc88a15af5eb1da02445ab17af3202400024c17f98594ac5e62c8090dc1834a949640000613e8126dbfe424025ebf98f5e81275fc8480ab40902fc8480
      (by decide) ⟨34, rfl⟩ (by decide +kernel)

  private theorem rb209 : (⟨[⟨3,6,false⟩,⟨5,2,true⟩,⟨19,2,false⟩,⟨67,1,false⟩],193,1⟩ : Box).Closed :=
    replayCloses (.nil)
      18 260 0x1e2b1794325901228c29d652c54c01894b55acd25903691cde3e3fa4ed01a8d1b5569d264c048000004976fcc24024b37e60484b334b4bb1d272404d10b562540cad4acd1b12a02401d6ccae1e99993460240000020dd49a13270e9b3653130b658a120049b9ff30562346bd8fd0006a7e81265ffe465432b4f5180901729307db40099a560f98e5000000126b3f98
      (by decide) ⟨96, rfl⟩ (by decide +kernel)

  private theorem rb210 : (⟨[⟨3,3,false⟩,⟨5,2,false⟩,⟨19,1,false⟩],63,2⟩ : Box).Closed :=
    replayCloses (.cons rb208 (.cons rb209 (.nil)))
      20 320 0x9112be8128e5fe467a61245ffdc024293ee7ada4a56e6782cc4834949fb3f9849bf7d9fee267edd02533defe418773d025876ffe400954e57f94ff74c24a6c7f82000971e9fcd69fa6126b8ff822402516df955f4c2492ff044801260bf8b7a6128dfc112b5e7af298007d42972f1201350faf5e530391313656c6e80900baac6316400006e3d024c4ffc84860dd024d5bf9082b50b20451b342f400ee6b379900002de812ebfe401c740952fc8480
      (by decide) ⟨31, rfl⟩ (by decide +kernel)

  private theorem rb211 : (⟨[⟨3,6,false⟩,⟨5,2,true⟩,⟨19,2,false⟩,⟨61,1,false⟩],267,1⟩ : Box).Closed :=
    replayCloses (.nil)
      18 247 0x24d5832ad5ad3b40db066b35d58c98090733cc1a1855b4b2024007c9543a389501200000482e7f309016be8120cbff2120120e1fcc301a583eda0018f5a7b680909000024143f984809ee8120cdff2120096e8120aefe47556bd68e2c80900241ddf980120c6fcc75256d3c74002c66844c0120a5e6400000012577f98
      (by decide) ⟨133, rfl⟩ (by decide +kernel)

  private theorem rb212 : (⟨[⟨3,5,false⟩,⟨5,2,true⟩,⟨19,1,false⟩,⟨59,1,false⟩],117,1⟩ : Box).Closed :=
    replayCloses (.nil)
      25 268 0x1d9ed8b477497a0240582e189a6e774b2000014aa6f8f8e0ecd97a02400000251c3f989bdbb5f1cefe92f4009274e8cd67690a0000025113fcc24025d0ff9848e2be812ecbfc84804824ff98e9dd025dfbf90042f409047ff9090024143f985d56a57b17a00c7c6f52f298045ad2d7a8c01ad1b5db74d6e76b64280900000024a6ff3090024b0fe612012603f98
      (by decide) ⟨58, rfl⟩ (by decide +kernel)

  private theorem rb213 : (⟨[⟨3,3,false⟩,⟨5,2,false⟩,⟨19,1,false⟩],61,2⟩ : Box).Closed :=
    replayCloses (.cons rb210 (.cons rb211 (.nil)))
      19 200 0x91c7fbe864b8ef7f984a2c2fe089002482fe6f3e984981ff8274deaf56c5e8002c3e8124b7fc8030950d1801296909500cb162e1a1c59000000116e8124bbf90900935efcc258f5ebca601563e3e34b1da000a2854bcc80000c7ba049a6ff90900096afe6120
      (by decide) ⟨30, rfl⟩ (by decide +kernel)

  private theorem rb214 : (⟨[⟨3,3,false⟩,⟨5,2,false⟩,⟨19,1,false⟩],55,2⟩ : Box).Closed :=
    replayCloses (.cons rb213 (.cons rb212 (.nil)))
      18 100 0x9007afa0482affcd67a612633fb88954a97ac6e80042a56bd623400830a07b70e3c000000dfba049a4ff200cbf4093afc8480
      (by decide) ⟨27, rfl⟩ (by decide +kernel)

  private theorem rb215 : (⟨[⟨3,2,true⟩,⟨5,2,false⟩,⟨19,1,false⟩],33,2⟩ : Box).Closed :=
    replayCloses (.nil)
      17 77 0x42d43460240c14a1da00500d4c595ac93c801400001d5963f4f2beeace16b93c5000000000
      (by decide) ⟨16, rfl⟩ (by decide +kernel)
end

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
mutual
  private theorem rb216 : (⟨[⟨3,3,false⟩,⟨5,2,false⟩,⟨19,1,false⟩],49,2⟩ : Box).Closed :=
    replayCloses (.cons rb214 (.nil))
      21 312 0x241475ba192a32df984aa8efe08241589f425a456c7f984bec9fc104804bd727fcbb0dd309659fff04480120387fc158f4c2415cff04da126ae1b1b5a4a800024160fe6120120b47f9848a52f409537ffc8482217a04a23ffcb9fa6125bffdc24024c97f3195a317ac5900e8a59a8716402a9d1a97be80002add024b77f212012627fcc240024d3bf11d2482c48582d162d3a430ed435a1e666256920b33733042b2c691201229f980
      (by decide) ⟨24, rfl⟩ (by decide +kernel)

  private theorem rb217 : (⟨[⟨3,2,true⟩,⟨5,2,false⟩,⟨19,1,false⟩],29,2⟩ : Box).Closed :=
    replayCloses (.cons rb215 (.nil))
      18 249 0x556aa8c00a1b95a7794c006a42b58c5010786b59e1a035ea356f3d002800002f6945b2a66ee8c58eed32c4f33dc1668b1cb51121b6812adf222aad5e048a42a001ae19d0cd000003cd024e7c88b29420091b62ce1f58a980cf5ea1da0258c433400a002814698f310063bb46f5ec6e80140000011b40906f9091a6980
      (by decide) ⟨14, rfl⟩ (by decide +kernel)

  private theorem rb218 : (⟨[⟨3,2,false⟩,⟨5,1,false⟩,⟨19,1,false⟩],29,2⟩ : Box).Closed :=
    replayCloses (.cons rb217 (.cons rb216 (.nil)))
      30 315 0x24706e88a4117fcc24ab7f041219b7469a4d5bf30915f040120222fd106946fff98490bfe08902bd02427e4b4c245bee004800e1f45ad20a1fe6126ebfc11201225fa2d20123a2f445a5c17f309223f82619da7d7c719303ad2cd1f9c5e800350e90f20456d50a980010d2464707769ba000000913e7f30900912dbf3091c97d1069745fe612547f82240319eaab449e093122d26d3f984bd7f70900911f98000000a0
      (by decide) ⟨14, rfl⟩ (by decide +kernel)

  private theorem rb219 : (⟨[⟨3,8,false⟩,⟨5,2,true⟩,⟨17,3,false⟩],141,2⟩ : Box).Closed :=
    replayCloses (.nil)
      17 164 0x20e355ead89501200663d30d47a61898ad4ab5efd65e8090450e2a1f52590000190f4c65e2b56a9d3bf59640000180f4c0000cc7a6188f5d5997312ccc92e4ba90a1b14319f4c301e98966a4282c164d4b05e6280000
      (by decide) ⟨70, rfl⟩ (by decide +kernel)

  private theorem rb220 : (⟨[⟨3,8,false⟩,⟨5,2,true⟩,⟨17,3,false⟩],111,2⟩ : Box).Closed :=
    replayCloses (.cons rb219 (.nil))
      20 286 0x3206871ea8649501213316ac1ad2590120004911fcc311f277ea525e81dcc1f55b113024cd7a6f4ad19374000182f44b2e084210a14953558b79e820189a8ab62a602445ab0687cc8090489e99adce8ead50b0bb40480beb5bd6aa593740cad40c8dcc4eb7f5685640000001befa8b3ef882ecc9d5f5a0be6cb16bbe8233563163d49640481a4f4c0554687b70eee1b3940030324973ea6726cb200048d69ac2fcc91301200001bafa600000
      (by decide) ⟨55, rfl⟩ (by decide +kernel)

  private theorem rb221 : (⟨[⟨3,8,false⟩,⟨5,2,true⟩,⟨17,3,false⟩],105,2⟩ : Box).Closed :=
    replayCloses (.cons rb220 (.nil))
      14 163 0x190c1cd0b34964023039aa8d93bf59ca02406da3a3c3838326e8090d76d9bd4b749da00000217e8124fffc84804905fcc6185e37ab5292f40486323a52c9ad244c0480363bab52c5e80152a98de78cef9b2c809000008efa04907ff200
      (by decide) ⟨52, rfl⟩ (by decide +kernel)

  private theorem rb222 : (⟨[⟨3,7,false⟩,⟨5,2,true⟩,⟨17,3,false⟩],101,2⟩ : Box).Closed :=
    replayCloses (.cons rb221 (.nil))
      21 220 0xcb53ca54a969640659e8c1dd2590000faa57bf5693f40295353aab6e92f40258e267f42fce9da02400000133d0241affe424044f409046ff2161d297a4c00b7c26364cd6877b29cae2bd002b1b1f2d0b3df99efce2ed01200000000b1e8120a3ff2092498a18b200d552a5e6406c35b07db400000207a048277fc8048
      (by decide) ⟨50, rfl⟩ (by decide +kernel)

  private theorem rb223 : (⟨[⟨3,6,true⟩,⟨5,2,true⟩,⟨17,2,true⟩],103,2⟩ : Box).Closed :=
    replayCloses (.nil)
      20 226 0x15a62c631e4026ed5a17a00029be81246ffc8482931ab87164000004969fe63a92ad78680027dd02488ff232c1d567a4c0488b17aaf55a4f200000924df986daafb5fe61692401a4f40936bff218afa049b2ff20126a3f98623d024c0ffc8049bf7e622c7a86e800c27d024db7fc800000000
      (by decide) ⟨51, rfl⟩ (by decide +kernel)
end

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
mutual
  private theorem rb224 : (⟨[⟨3,6,true⟩,⟨5,2,true⟩,⟨17,3,false⟩],111,2⟩ : Box).Closed :=
    replayCloses (.nil)
      17 272 0xcb07ca1f3202461b1c55a963260007c360f9900000494efcc024db7f9803252a1e1e1bd3ace50000613d024c37f90140d4d8c4eef9bd6428000305f410a05eb69b51b662dc7a1add1526e887a966ab16f3ea22036a15aa525901200e9e4d7e6f49640001bcfa61b4fa0c50842160850c58b41e82324b07746dd5bd42b20240341e80d8ab25d142890e58b09f411b8fa8a5892ccc842dcd962d47d040000000
      (by decide) ⟨55, rfl⟩ (by decide +kernel)

  private theorem rb225 : (⟨[⟨3,6,true⟩,⟨5,2,true⟩,⟨17,2,false⟩],101,2⟩ : Box).Closed :=
    replayCloses (.cons rb223 (.cons rb224 (.nil)))
      15 188 0x22d52b4ad8d180709c5ef49800005374090477f218ead4a963f401558a5eb18a000009273f98272851a962c80900024b8fe603562d52f525900262c98d7b17a014b387869639404800004919fe60002b556b3cf400ac4eb3ca6000009273f980
      (by decide) ⟨50, rfl⟩ (by decide +kernel)

  private theorem rb226 : (⟨[⟨3,8,false⟩,⟨5,2,true⟩,⟨17,2,true⟩],129,2⟩ : Box).Closed :=
    replayCloses (.nil)
      19 261 0xd5ab5497a93c80000db7d30d57d37264a310b062caac514f3162f31279012064bebd7f5b0d82d1d0aa2c5a2fa08d87ae499325e65a2c50d34aeda7af5eacf20650a54bd62340001acfa4acc4aa589668b1434d8d58adebd59ca0240341e988adb56b274ed2c800000004d3152a58f20240d67d0cf26671c9dcd3331643d0456b35e6bb3ebc900ad62cf0d000643d30c07a6000000
      (by decide) ⟨64, rfl⟩ (by decide +kernel)

  private theorem rb227 : (⟨[⟨3,8,false⟩,⟨5,2,true⟩,⟨17,2,true⟩],103,2⟩ : Box).Closed :=
    replayCloses (.cons rb226 (.nil))
      15 259 0x871a7af58fd032cd2bb46b24e50000483bbf314c4219a0196ab56598cd0120000096e8120aefe4550856bc540488a8634ef58e980908676a874c009cbc858852590000000492dfe632e56b86cad25e8090d6237af58898000092fa04973ff212004909fe609e4bce1c64c08eda4ef53a4a98000319e82e50aea59998b69ea28989f51c553537be7162df7d440000
      (by decide) ⟨51, rfl⟩ (by decide +kernel)

  private theorem rb228 : (⟨[⟨3,6,false⟩,⟨5,2,true⟩,⟨17,2,false⟩],101,2⟩ : Box).Closed :=
    replayCloses (.cons rb225 (.cons rb227 (.cons rb222 (.nil))))
      11 45 0xab56ab5e640002c7a04828ffc848081e81209dff20480
      (by decide) ⟨50, rfl⟩ (by decide +kernel)

  private theorem rb229 : (⟨[⟨3,4,true⟩,⟨5,4,true⟩,⟨17,3,false⟩],175,2⟩ : Box).Closed :=
    replayCloses (.nil)
      23 263 0x1dc8543eab6ed234048004969fcc4db3b5e5f3d01200577d024a3ff90bcfa04963ff202342cd9bd4988090cb71697fb248c0e54f6d1f5d0000447a04903ff2169f4092bbfe4203d0248eff91350e3070b43a1e97a00000921df98cdbaceb6c2e2260369c6d94b0b276809000920df9864bd024d7ffc8235353a6ef185d254000012667fcc024c4ff98000000000
      (by decide) ⟨87, rfl⟩ (by decide +kernel)

  private theorem rb230 : (⟨[⟨3,4,true⟩,⟨5,4,true⟩,⟨17,3,false⟩],141,2⟩ : Box).Closed :=
    replayCloses (.cons rb229 (.nil))
      17 230 0x11194e57cf400012efbfcc24025d27f300736ee9d9d993860072c1919d4a4c4002a81c79ea9494006b1da59df298000009759fe619291d9f1d993b40393ab7efd8fd00000483e7f313594b8be530000b1e8120a3ff224fee9d9d9c4e8091ce697b7db8bd0000120befcc0185c3c323ea4b00900043740906b7f2000000
      (by decide) ⟨70, rfl⟩ (by decide +kernel)

  private theorem rb231 : (⟨[⟨3,4,true⟩,⟨5,4,true⟩,⟨17,3,false⟩],117,2⟩ : Box).Closed :=
    replayCloses (.cons rb230 (.nil))
      16 215 0x59e29ed8c8c5763d32602406f6725e0ecc8e47a5e800075bdd025d50ff212012e4cfe60126b3bf300095573f980bb9eb619385f36db23caf15e800002496f7e604a9ba04928efe42402514f7e609ddbed2eac44c0029f3e812a71ff90914f6e812a6f7f212c5ac1dd8ed00024cf409135ffc8480489e3f980000
      (by decide) ⟨58, rfl⟩ (by decide +kernel)
end

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
mutual
  private theorem rb232 : (⟨[⟨3,4,true⟩,⟨5,6,false⟩,⟨17,3,false⟩],199,2⟩ : Box).Closed :=
    replayCloses (.nil)
      22 306 0x918295693c800706b4acce764bd0120480457d30a0f4c5d1a972e2fee5c5b3460244dd3b393f3c3b5fd3bf42d28d00075b1aeb74746fba68c000012eebb9e0c1b2cf76d65b2c54ee822edd2de6a876b2cb2cc698e58a6dd058ed2b79e66aac929aac7809593c3ebd7ed3c80909026dd650ed9b47ccf20c58aadd0459baa52081a638acd1629374109aa06366f55b4802408374c51c60f828bdad2fd8b8a0a795b69617550f961687cb4ba600240563e324e8d9dd2740000185fa60000000
      (by decide) ⟨99, rfl⟩ (by decide +kernel)

  private theorem rb233 : (⟨[⟨3,4,true⟩,⟨5,6,false⟩,⟨17,3,false⟩],181,2⟩ : Box).Closed :=
    replayCloses (.cons rb232 (.nil))
      15 256 0x53aa84fec593260058fd7dfee2a600001cdd02419dfc86132ddd8bcb254c0480b468636edaed65b4b0a001a491b140fdbaaced00000013df48d617989cbd97a21e66666038a3be90eac1ae8d25431590e58adbea2283a5edd7a4c980f4ed1f5fb1b268c048e49d35a756cee9230002eb3e6ca588981ebadded9ab6bcba5e80900025be981224c0fad1c6e2c9c300004d7d69aab4f52172f5e8b1557d04000
      (by decide) ⟨90, rfl⟩ (by decide +kernel)

  private theorem rb234 : (⟨[⟨3,4,true⟩,⟨5,6,false⟩,⟨17,3,false⟩],159,2⟩ : Box).Closed :=
    replayCloses (.cons rb233 (.nil))
      16 211 0x3addd35ab78c9ba01c66a773b5a4fd0003a3740970dff22373b7acfdfbf69fa02432956d9f1d99374013ada5a1fcc2c97a001ebe8b83a5f6d0f4dd01200000377d02418ffe4599aeb76b93cb274c0481204d4f278b53d527e80000024143f98b3036da5f9fafed3a602405e83d32da5ab4898090000241edf980000
      (by decide) ⟨79, rfl⟩ (by decide +kernel)

  private theorem rb235 : (⟨[⟨3,4,true⟩,⟨5,6,false⟩,⟨17,3,false⟩],153,2⟩ : Box).Closed :=
    replayCloses (.cons rb234 (.nil))
      17 130 0x352adb7accec97a01db5ad75c6eec6e9da000904a9dd1323bb1ba7680033958559dae9b02fcbeb6c4e50238db118ed2b6c2fb7f62f202400000729e812eb7fe4091562eb0df6d0000e2be812ecbfc80
      (by decide) ⟨76, rfl⟩ (by decide +kernel)

  private theorem rb236 : (⟨[⟨3,4,true⟩,⟨5,6,false⟩,⟨17,2,true⟩],181,2⟩ : Box).Closed :=
    replayCloses (.nil)
      20 298 0x16ebd56c76800287eb0d2b352152b24b33658a33d04683ba47c34048155f4c28be989ad87e727f497a024060ece36710bfacf20000223d443868a87b82a2c561e821950dad1cd279032928634efd27680002b3e9bb2a56e66668b1487a08af744bde5ca28d418b147baecb562d5e5960a65962b7751166ea2850a0f292b3149ba08a3758736964add10a4d962837410a856b46b5693c809020dd30c97aa468621259642d162dcfd04627e98000000000
      (by decide) ⟨90, rfl⟩ (by decide +kernel)

  private theorem rb237 : (⟨[⟨3,4,true⟩,⟨5,6,false⟩,⟨17,2,true⟩],141,2⟩ : Box).Closed :=
    replayCloses (.cons rb236 (.nil))
      21 254 0x4286ef55a4f201ca1b5eb37a923400223ba04a2fbf90900970bfe6012e87fcc01e56a07dc80000971dfe6012eadf9864d64e4fac99d67900000337d024137fe41d62a1a35a4f20242aa188589280000e1e8120b9fe401ddc3fbe617f697a000011dd02417dfc8632af6adafe9226024156337a763c8000089fae4b1590f054f43162bcf410000000
      (by decide) ⟨70, rfl⟩ (by decide +kernel)

  private theorem rb238 : (⟨[⟨3,4,true⟩,⟨5,6,false⟩,⟨17,2,true⟩],129,2⟩ : Box).Closed :=
    replayCloses (.cons rb237 (.nil))
      18 218 0x43aa962b6e93b4048a4d7461637efda64c000a91e8122a0ffc80a9ee8122b37fc848cbdbd02595b7f229abd56b58cd001b14217ac6e8014786872754ccefd66e8000000093367f984804a9e7fcc365e794ad496002b57343c3b585d3c8001a70eedd8ed00e4cdaf0ea92a60240000254a5fe612012a777e6000
      (by decide) ⟨64, rfl⟩ (by decide +kernel)

  private theorem rb239 : (⟨[⟨3,4,true⟩,⟨5,5,false⟩,⟨17,2,true⟩],121,2⟩ : Box).Closed :=
    replayCloses (.cons rb238 (.nil))
      16 119 0x10f0dbeb2749530393ba6db6bc64c98002439899d891c192260000092d5df98480496f6fe600490f4ff3014281c1b58cd00083e3d025064ffc80838dd0250637fc8120
      (by decide) ⟨60, rfl⟩ (by decide +kernel)
end

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
mutual
  private theorem rb240 : (⟨[⟨3,4,true⟩,⟨5,6,false⟩,⟨17,3,false⟩],139,2⟩ : Box).Closed :=
    replayCloses (.cons rb235 (.nil))
      16 261 0x2a7a9cd718d81e8e9757fb8bb40a9c2d9856dfcef3bed37565697680000050be8120b4ffc802a1e8120bf7fc8e3d33b57f6164bd0120285a366ae592f403b6a9c5c6e3b400000120b47f98480499bbfcc273ab162d292f405d8ed2ca77df6c9fa007af2c1e9a34b43d2f4000004a217f309115be8128bbff214c0d9331b17a05566b86471bbb759c30000128f1fcc4d6244eec6c9da0001183d025153fc800
      (by decide) ⟨69, rfl⟩ (by decide +kernel)

  private theorem rb241 : (⟨[⟨3,4,true⟩,⟨5,6,false⟩,⟨17,3,false⟩,⟨127,2,false⟩],4563,1⟩ : Box).Closed :=
    replayCloses (.nil)
      21 276 0x8d6d58f8dd6278766dbf34b460241c7f637c6b6379b0381c29181b5d7f3e1b0cf2be9fd331a27cbb40480009dd3f4094ed7ff9090094ef6ff30094eeeff3013b8be8129db3ff200deed6ced2c5c1b3a6000094ec4fe61227787a04a76e7f913ba3d0253b87fe400094ef0ff3090090ef4ff30905b17e8122dbfff21d77dd5c3b36fe3eafd3b22602400925fdfe604b6be8124b97fe425c5f40925b3ff21200492e0fe612004a3717f98
      (by decide) ⟨2281, rfl⟩ (by decide +kernel)

  private theorem rb242 : (⟨[⟨3,4,true⟩,⟨5,6,false⟩,⟨17,3,false⟩],129,2⟩ : Box).Closed :=
    replayCloses (.cons rb240 (.nil))
      20 324 0x14b9dad6eeead3656c898126672693d1b4e4bd00172dd2a64743caf4fd03966e31d9d4a16c9d0001cd4c297356daf2d9a303689c7ad2149da03ae8cf73bc39593f40003be6d636be36db3b40bbfb4bf1dbae07f9e0d97a004d0df749e1fecad5ba16976800000090d7bfcc240d93d024375ff909035374090d1dfc863f36b54a8d233a0616280002436b7e6120838be8128367fe42475cdd025d677f21ace8f4fea1ff74bd01208b4fd025157ff909115efa04a2a7ff222fdf40945cffe4002515aff3090162f40905c7fc800
      (by decide) ⟨64, rfl⟩ (by decide +kernel)

  private theorem rb243 : (⟨[⟨3,4,true⟩,⟨5,5,false⟩,⟨17,2,false⟩],117,2⟩ : Box).Closed :=
    replayCloses (.cons rb239 (.cons rb242 (.cons rb241 (.nil))))
      21 134 0x73cdd024e73bf90c734ed387864dd00cb1668fa8c000004ace9ff30916617d025674ffc84804b4ccff31c6b8c5edc59346004ddfbf62e2260000096995fe600fb27a04beebff204800
      (by decide) ⟨58, rfl⟩ (by decide +kernel)

  private theorem rb244 : (⟨[⟨3,5,true⟩,⟨5,4,true⟩,⟨17,3,false⟩],283,2⟩ : Box).Closed :=
    replayCloses (.nil)
      23 227 0x1b48d4fef1d993b40e0303b3bb1930000ddf409063ff91151376386c85b3340000a5f4c07f74c45e735af6d7e7d42c2e2f200005f74c070fa632e51b1135af690a00005774c06374c13ebc31ab42eea1d0e878b7404805cfd31cc563673496464a1c50e9c376bbb75364bd000179e9850fd30acf410f043d06cbd6e4cd5628cf41000000000480
      (by decide) ⟨141, rfl⟩ (by decide +kernel)

  private theorem rb245 : (⟨[⟨3,5,true⟩,⟨5,4,true⟩,⟨17,3,false⟩],253,2⟩ : Box).Closed :=
    replayCloses (.cons rb244 (.nil))
      20 218 0x598efcfef298090771e812e27fe4771f409731fe4756e812eddfc8240e3eb8b83b38db3b400cba687cb3d7efd0b0a340aa1e62952dda6680000025ddbf980b7bc3a33b76addba144c0482b068674e8d3b4c4000a868c8e376b2d8ee28500480000085e81208fff2177c6568ce95dda64c0484800e9e812097ff2000000
      (by decide) ⟨126, rfl⟩ (by decide +kernel)

  private theorem rb246 : (⟨[⟨3,5,true⟩,⟨5,4,true⟩,⟨17,3,false⟩],229,2⟩ : Box).Closed :=
    replayCloses (.cons rb245 (.nil))
      18 243 0x2f5662fcff6574bd00a4a856f55a48d000012278ff30900913bbf30d63697b7cf4048889b5e3e3e327680139b1dd1f9f9dda5e80000009461ff3095686eeddb38dd3b404800128d9fe600c2f51a97db27e80e6b42fac6e2f404809a4cd2a55a4bd0000128f1fe60af450d6c590122aed13b38b8dc6e9da0066f27359eeef9e5a1d93a00000025cf7f980000
      (by decide) ⟨114, rfl⟩ (by decide +kernel)

  private theorem rb247 : (⟨[⟨3,5,true⟩,⟨5,4,true⟩,⟨17,3,false⟩],213,2⟩ : Box).Closed :=
    replayCloses (.cons rb246 (.nil))
      12 107 0x48967fcc06316b17064ed001a744fe858d1806d0aca1adea4f20000012e7a04896ffe401ded92a7bcb2ba7680000913e7f9848250f40913f7fc800
      (by decide) ⟨106, rfl⟩ (by decide +kernel)
end

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
mutual
  private theorem rb248 : (⟨[⟨3,5,true⟩,⟨5,4,true⟩,⟨17,2,true⟩],259,2⟩ : Box).Closed :=
    replayCloses (.nil)
      26 243 0x31c9dac32600010bd02411ffe44de9b67756b36b6790000277d02410ffe4054f40906dff9009062ff3136943933bd497a024009068fe6096aad52c58000e1e8120b9fe405f7409048ff21204821bf314d1a51a77e85d2f40010bf40927ffe4267e8125bffc803650687cc7ab2800119e81255ffc80495dfe6000000000000
      (by decide) ⟨129, rfl⟩ (by decide +kernel)

  private theorem rb249 : (⟨[⟨3,5,true⟩,⟨5,4,true⟩,⟨17,2,true⟩],225,2⟩ : Box).Closed :=
    replayCloses (.cons rb248 (.nil))
      19 234 0x22a5e4ef9c74c00012885fe632b558a5e5ad2c001133e8128bdff234d97bd79e80253599b3d62f400004a2dbf3194ac5e6297ad254036f3c7f784c000ed3d025c5ffc86421798b527802a96840c00659c3ebd623400012e53f98a7b94bd63c800025cfbf30cf7354a9492a0195952b7cc9e4000012e4df98000000
      (by decide) ⟨112, rfl⟩ (by decide +kernel)

  private theorem rb250 : (⟨[⟨3,5,true⟩,⟨5,4,true⟩,⟨17,2,true⟩],173,2⟩ : Box).Closed :=
    replayCloses (.cons rb249 (.nil))
      21 398 0x3a6ff1f40974df63fc83a5fe4f4341e974bf89fcc24b6fff7e08349fede8683d2693f5bf9848e71bfe080969c5fe60049ecdfee50f4c25c9dff048a14a4c6693c8090025464ff98012c317fccceeb618aedc6361e8e58b096517fc118cae9f1f9b24ed000122b4ff980af1f4091563fc4cdf4c244ebff7009655bfcc009659df891dd30912bbf824573d02515bff90025168fe8bee984a37bf048adba04a29efe4014cf40905affeea7e984ba2fee19085a343a34b4f201c6bd3ba171d300e4a6677b4c000029bdd0254a1fe0f5f4c24157fee00c6c62962340165e62a56a495000004a30ff980000000
      (by decide) ⟨86, rfl⟩ (by decide +kernel)

  private theorem rb251 : (⟨[⟨3,5,true⟩,⟨5,7,false⟩,⟨17,2,true⟩],281,2⟩ : Box).Closed :=
    replayCloses (.nil)
      24 211 0x1d1ba618ecfa369696974e980d40ed71b0bb593b4000297a60480377d30935db54b65b0b264c0480387a60287ae6434579af33dd4b355884cfa08103d3019dd30379ed2170c963cdf45000096e982bb70dec66923404810bf4c24bd531e516e65a869b2c50a9fa6105e82a24908deda142ca65562800000000000
      (by decide) ⟨140, rfl⟩ (by decide +kernel)

  private theorem rb252 : (⟨[⟨3,5,true⟩,⟨5,6,false⟩,⟨17,2,true⟩],271,2⟩ : Box).Closed :=
    replayCloses (.cons rb251 (.nil))
      31 305 0x698deab1b4ddae99a02400709f40976dff239b740971efe4025c1bf300606a7eb2dc9a5a5b3c80001e7e81209fff20354e8599c74c0001209dfe6120d9f40907fffc8d3c3eb865b8bd000267d02417bfe40241fdf9808ee8120befe404b74090577f2125e821e660bd2a12b162b9fa08c47c7d6ec768090024b9ff30a9fa669252f34c5b821ab96289faee252854a18a56e6a532e63c1189998dab6bfb4bd01205e7a600000000000000
      (by decide) ⟨135, rfl⟩ (by decide +kernel)

  private theorem rb253 : (⟨[⟨3,5,true⟩,⟨5,6,false⟩,⟨17,2,true⟩],241,2⟩ : Box).Closed :=
    replayCloses (.cons rb252 (.nil))
      15 246 0x32f4d0ab44c99a0352b1091800d44e0f4fd71b4b0b644c013cde98d5f52d2d9da02403ac75add33a9696cf200000011bbe8128c7ff200f9a3fbf6e9334048db17a8fec468090002516df9835b1f567cfe85d2f404843a366ea6e2f4048004bacfe6191a379a3bab69e4048ca07cf59ab499a0001d57d025c2ffc863b8787cadbb4f2000769f40975dff200000
      (by decide) ⟨120, rfl⟩ (by decide +kernel)

  private theorem rb254 : (⟨[⟨3,5,true⟩,⟨5,6,false⟩,⟨17,2,true⟩],229,2⟩ : Box).Closed :=
    replayCloses (.cons rb253 (.nil))
      16 129 0x259fa0489dffe4240244d9fcc3358ae7d7a9226024004f1e812249ff9090091287f31b50c4faad935b4cd0122ccceafdfb19301236d9c6fcc6f525e8090000009442fe6000
      (by decide) ⟨114, rfl⟩ (by decide +kernel)

  private theorem rb255 : (⟨[⟨3,5,true⟩,⟨5,6,true⟩,⟨17,3,false⟩],285,2⟩ : Box).Closed :=
    replayCloses (.nil)
      28 244 0x776e98e7e729d369687cbab648c0000d9e8ac5262e58ad61b14bd1a7a3cc4267a0906d4e854393fb4f202401bbe980edf4c76d838d1da743a1d0f56874a74000089ea2f72b76a1b23421e6cb144cf33e59da6cac97a00070f4c060f4c06f74c04f741a49ebbdc77b9e782aac43bba0819dd3006c87879d9592f4048035ba60c9d4ced1d2f2ead0e17680007b7a6125e9800000000000120
      (by decide) ⟨142, rfl⟩ (by decide +kernel)
end

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
mutual
  private theorem rb256 : (⟨[⟨3,5,true⟩,⟨5,7,false⟩,⟨17,3,false⟩],285,2⟩ : Box).Closed :=
    replayCloses (.nil)
      29 277 0x70ee98f5d9acee63b2b05fb6cfd01d61b59fe9ecea1e9a3012002e7a602f7d651b956c7a0d9e2a160b558a00d4c92beb33fb6bfa17179012000277d3193e9e1f53ac7aba64c0480327a60247a8363f55db347f8d8df073597b45f9a1ab10e1e8205358cf3bb5dd43a1eac2ed012003a7d301c3e980dee980aee980b6e906a9347c819211a570f2c51b727cdbdfaca5cb65e819b0b67f4ae7756c7676809001ede986b53d4fa69b33aba5e8090217e9800000000000120
      (by decide) ⟨142, rfl⟩ (by decide +kernel)

  private theorem rb257 : (⟨[⟨3,5,true⟩,⟨5,6,false⟩,⟨17,3,false⟩],279,2⟩ : Box).Closed :=
    replayCloses (.cons rb255 (.cons rb256 (.nil)))
      13 230 0x39b5f3d5b71b8de5b3b4048480e63d156db1831bd4c72b2d963d47a0a5b5f69b65e0a8b1e18e366dbbb6bedd2f404804c7634a955ad3e5a1c29180a73386db6569b9dd5b2f4048000eb3ea2dcf13c868da30acb1e43d040e3c30d1ad5ab6eb3340480abb138f6e3a60241ac2a2f76e959ae56ced00000012e23f982b56337ef55b4cd0116dd69616cc93a000025c67f9800
      (by decide) ⟨139, rfl⟩ (by decide +kernel)

  private theorem rb258 : (⟨[⟨3,5,true⟩,⟨5,6,false⟩,⟨17,3,false⟩],271,2⟩ : Box).Closed :=
    replayCloses (.cons rb257 (.nil))
      17 192 0x4ede4ea1fdfb48d01229b37581f2ff7fba7e81b43eb2339de7cb43b2f40481200e33d025d5ffc80bd93a5cbcb2ba5e80e687eb9ad63740934d96c77a717a00035ce6cd75c6e80bbddada9fceac9d3002b77bfbf4afcead34602400cba2f3bdddd7a56566b85a301ac5e6ccf2fea5f6d93a0000000755f40970bff200
      (by decide) ⟨135, rfl⟩ (by decide +kernel)

  private theorem rb259 : (⟨[⟨3,5,true⟩,⟨5,6,false⟩,⟨17,3,false⟩],253,2⟩ : Box).Closed :=
    replayCloses (.cons rb258 (.nil))
      18 206 0x14786cfae2f2c9930123973efdc59595d22607369d9c1e5e5e5b3b40048630b26c99e592f404800008b1e8128a3ff230ca73a9bcbcb5b4e98091339cff4ac2f2c953000d30bcbb53be7c72bfdd5c5c3002e696376d7db0b668c00000008cee8128fefe406d4c76539ef2cae97a04df38b8dc6e376796ced00120012e0bf98000
      (by decide) ⟨126, rfl⟩ (by decide +kernel)

  private theorem rb260 : (⟨[⟨3,5,true⟩,⟨5,6,false⟩,⟨17,3,false⟩],241,2⟩ : Box).Closed :=
    replayCloses (.cons rb259 (.nil))
      13 221 0x3693c58d2b4392a602403da303c1da705e913001ad4ff767b5bed8f4bd01200000489fbfcc05acb74ad99246025e6ecc77cf4004e79695b1da07989c1c6f4e2f400ad9af4e7616246024073633b6dcc2c9da0000004a9e81226dff9016cd27fa5b5a5716cbd000d2d62e1ad5acc400f5c5673da5dd25e800011a7e8128afff2120128c3fe600
      (by decide) ⟨120, rfl⟩ (by decide +kernel)

  private theorem rb261 : (⟨[⟨3,5,true⟩,⟨5,6,false⟩,⟨17,3,false⟩],229,2⟩ : Box).Closed :=
    replayCloses (.cons rb260 (.nil))
      17 284 0x670df51b873343dd644c020f4db7150ffbcba5e8006fa8523a5f9d5d22601eb359563fed0f57975615e80900000024c91fcc31e4e874756af2e9130120012660fe61219ddd024cc1fe4357a35685b1c97a00a619b06f3b99dab96878bb4048000a6cf409520ff91de696ebcbb3cba7680124749e76d3f6c97a00014ddf409531ffc848a5afa04a997fe4534e18d1a86b56b2000c17370f4ecc9da0000122fd0244bfff212090bd02448fff2000
      (by decide) ⟨114, rfl⟩ (by decide +kernel)

  private theorem rb262 : (⟨[⟨3,5,true⟩,⟨5,6,false⟩,⟨17,3,false⟩],225,2⟩ : Box).Closed :=
    replayCloses (.cons rb261 (.nil))
      13 92 0x903367a049907fc89add7f667e75656cbd006501d5e6346b59e00e9cb7f385a54b244c0000193be812643ff9090cc5f40932cffc80
      (by decide) ⟨112, rfl⟩ (by decide +kernel)

  private theorem rb263 : (⟨[⟨3,5,true⟩,⟨5,6,false⟩,⟨17,3,false⟩],213,2⟩ : Box).Closed :=
    replayCloses (.cons rb262 (.nil))
      16 192 0x1777b7a8779ff64bd0000482d9fcc0090553f98269662352f54bd42a00cdaeef6fb9da5d5a1d99300dd86e8f53daff60bd3260000014afa0482e5fe439b9c1f2e76fb26e819b8dafa0bb4f47a7680901b6571ab59c5f0ff59da0000016afa04828bff2120120a47f309b9b5bcb238d93a60000090503f980
      (by decide) ⟨106, rfl⟩ (by decide +kernel)
end

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
mutual
  private theorem rb264 : (⟨[⟨3,5,true⟩,⟨5,6,false⟩,⟨17,3,false⟩,⟨199,1,false⟩],201,1⟩ : Box).Closed :=
    replayCloses (.nil)
      21 214 0x396729d8e1babc779d97a0016ac543615cdd75b4ab56befb75620240000025c7fbf30c6994dfce57dba5e806d5ca5f5a5d9d3b400362bde72467f9ed7d2f40000038f0fa04b8d6ff90900931a5fcc245d9be812ba6ffc85b42558ed7ebe3659012030ca95aabbd329d99dd1d2a0000004aefdfe6028d2fa04a8f9ff9090091d1df98
      (by decide) ⟨100, rfl⟩ (by decide +kernel)

  private theorem rb265 : (⟨[⟨3,5,true⟩,⟨5,6,false⟩,⟨17,3,false⟩],199,2⟩ : Box).Closed :=
    replayCloses (.cons rb264 (.cons rb263 (.nil)))
      19 247 0x267b38acbee7c3b2f139ae15e81e6879b8f5b3b3a6e816787733d82ef395e5a1eaead2bd03ceeeee0ff3b6d2d2260000157cfa04aae3ff2122aeee812ab07f9156f74095543fc8480122b4ff9835938606eb23248c048a3eadbb39dc68c05a763e7f63740c3e68dad2e071796400106c37c7c69607a7681b57706262653a6ff6ced0000002a4fd024567ff9090091513f982b37d02454dff900024550fe600
      (by decide) ⟨99, rfl⟩ (by decide +kernel)

  private theorem rb266 : (⟨[⟨3,5,true⟩,⟨5,6,false⟩,⟨17,3,false⟩],195,2⟩ : Box).Closed :=
    replayCloses (.cons rb265 (.nil))
      23 208 0xcd27233ba797169796148c023796f97b06fd7fd7fd3eaf6b0b260246d0355f4bb9b5fe6fcdec898090900000256767f98b9fcdd66bfd7cae1be91301eace9536fb9d93a60240000959f1fe612012330bf98480494ecfe63937b5f8affb6cddd7f1d97a01acd76b1329e8fb385fdfdc5da024006986e812d3adfc80fbdba04bedefe424025c7e7f980
      (by decide) ⟨97, rfl⟩ (by decide +kernel)

  private theorem rb267 : (⟨[⟨3,5,true⟩,⟨5,6,false⟩,⟨17,3,false⟩,⟨193,2,false⟩],6975,1⟩ : Box).Closed :=
    replayCloses (.nil)
      21 344 0x394ded5bdd6dbb5fc7b5ec89809027d365dd7abf9fd7a2ecbd000d925b2b7db9f9a5b6c0f168c048000b9c374095cf5bf90907385e81239c7ff901ebfebf278dec9faf6adecdb85f1f2ed0022793a99eca74dfd05e768705f2caf200001ce27a048e71bfc8039f8f4091ce4ffc839d0f4091cff7fc84839e8fa048e77fff21275bbd5eadaffb2bb2f4048a3aaf75e0e872386fa74c00000498f17f3091b3d6e812d9f77f21201269d0fe6067734dd2f3c2febe2d97a02434ed39cf6bfad9b7274c048001243d5fe60e70b1d9af0383f5e97a00eb39d4e17e9e6715e993000001243b6fcc2400964fcff98
      (by decide) ⟨3487, rfl⟩ (by decide +kernel)

  private theorem rb268 : (⟨[⟨3,5,true⟩,⟨5,6,false⟩,⟨17,3,false⟩],193,2⟩ : Box).Closed :=
    replayCloses (.cons rb266 (.cons rb267 (.nil)))
      24 199 0xcacd5a60c2d691a02449cee6719ccf4dce9ba064e49cf5b7ddaec7cb66e800007a5d79af0df56574918000000093ef4fe607d95f4093ef2ff21e9286d677a64d18003ef0f4093edcff200127deefcc2402493d6fcc240253b53f98a36568559c8c97a02400965e1fcc00965f6fcc015bf3e812ade3ff20
      (by decide) ⟨96, rfl⟩ (by decide +kernel)

  private theorem rb269 : (⟨[⟨3,5,true⟩,⟨5,8,false⟩,⟨17,5,false⟩,⟨191,2,false⟩],25915,1⟩ : Box).Closed :=
    replayCloses (.nil)
      18 251 0x674387154e6a1d36717962003b65f57f9dad79ae6bdd763de57c7cbb4048000012613ceff309009309fc7f3090c27a6e812613c77f225719e37b35b5ec37f8bdae7bab4a740000186fd3f40930df5ffe424024c37f6ff309030df7dd024c37c8ff21ae526cdb9e68ea8ce8725fee2f55808a86109989cedd646172d2f200000932bf8bfe60657fd3d024cafe5ffc8657fbdd024cafe87f90032bf86e812657fadfc8
      (by decide) ⟨12957, rfl⟩ (by decide +kernel)

  private theorem rb270 : (⟨[⟨3,5,true⟩,⟨5,6,false⟩,⟨17,3,false⟩],187,2⟩ : Box).Closed :=
    replayCloses (.cons rb268 (.cons rb269 (.nil)))
      27 337 0x79bef77539af85f364767e800024cd7e1ff30335fb3e81266bffffe42eeccd7fbc33a4bd008dcd734b4bedb1e97a0240d6cfe7d3738adb4afbc3f9a5da03ad9b747dba69ba44c0000066be5ba0499afaefe40024d2fe27f30d57ef7409355f43fc80012617fa3f984804989fdf7e612180f85f409301fa7fe43ae07f9f2d86fed79af35d97a02402e97febfd7b46f6bc8e97a000321fede812643edbf902bd689c99aff36bfa5e801ae57d6cb75767cdf4bd000001263deaff300936ee2ff9806ddcafa049b77cbfc8483379df40966f0ffe4247ce67d025f3bdff200
      (by decide) ⟨93, rfl⟩ (by decide +kernel)

  private theorem rb271 : (⟨[⟨3,5,true⟩,⟨5,5,false⟩,⟨17,3,false⟩],181,2⟩ : Box).Closed :=
    replayCloses (.cons rb270 (.nil))
      3 4 0x120
      (by decide) ⟨90, rfl⟩ (by decide +kernel)
end

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
mutual
  private theorem rb272 : (⟨[⟨3,5,true⟩,⟨5,4,true⟩,⟨17,3,false⟩],183,2⟩ : Box).Closed :=
    replayCloses (.cons rb247 (.nil))
      16 323 0x1ce9a4f8bad29c97a059f4f33c6eed1d8ff59da076dedaf2f4ed64d18000136cf4094d07fc84804a68efcc2402506b7f98dbc17f60ff497a031c19af8e356d7f591a0240024074ff9801203c3f98eba7a04ba97ff20012ea07f31078673d1f9d1cade766e80900024d737e60aaf7d025553ff90900955cdf98048aedfe6120122a47f3091962f40965c7fc8cbd14a86b6ed29403ba2cea5f6da7a5e8000143740905adfc8635add3bb1a30121b0c285bb17a00000933f7f980000
      (by decide) ⟨91, rfl⟩ (by decide +kernel)

  private theorem rb273 : (⟨[⟨3,5,true⟩,⟨5,4,true⟩,⟨17,2,false⟩],173,2⟩ : Box).Closed :=
    replayCloses (.cons rb250 (.cons rb272 (.nil)))
      19 314 0x15dff6dd024577fcf7f20048ad3fdbfcc15a7ebba048ad3f03fc802abffa7a048aaff97ff2120122a67a6fcc024550fd3f980122bf7f4ff9802ac7ccfa048ab1f7bfe465adfcfd02596b79fff2004b2d6f9bfcc0256be2fd02495afbfff44cf8dd30946bfc5ff7090177fbbe8120bbfc7ff377fa1e9849bbff4ff709009331f7dfb67edd3096cf7bf8265ff9f40965fe3ff2004b2ff77e61d703d024eb9dff2001275fb7f3090094ae87f300951c2ff30024474bf9802bdbe8122bf7fefbe7a612fb0ffb800
      (by decide) ⟨86, rfl⟩ (by decide +kernel)

  private theorem rb274 : (⟨[⟨3,6,true⟩,⟨5,4,true⟩,⟨17,4,false⟩],347,2⟩ : Box).Closed :=
    replayCloses (.nil)
      30 300 0xe13e989b9381e2c5f6d0f4bd003a8fa63b774c3ad0d7dd5cb25e8090716eacf2a666bc1629072c7b3741398c933733be67592a000079fa60217a602c6d0d3657fb27e800133d3017be898a60a4d9b3cf7365886efa08153d30ca747b78eabdb5b310000357d2e0ad598310b4a5e0aab14052fa602c7ae492ca89e42b3952b121e621a3d0466b37aa5eb769ca0240133e8ac55de253310a56e6ab1413b60c77dbba4bd000fa958b8beddda76800074fa60000000000000
      (by decide) ⟨173, rfl⟩ (by decide +kernel)

  private theorem rb275 : (⟨[⟨3,6,true⟩,⟨5,4,true⟩,⟨17,3,false⟩],283,2⟩ : Box).Closed :=
    replayCloses (.cons rb274 (.nil))
      18 318 0x6e2c9a5a5fa4bd010ce91e9f6d0019238dd5b103019136b07671fa0044f6db0b0b0b0ba64c0480349caa5f389180009956dad0bab7697a0000004c9e812275ff90496ea2f58a1a5b998939494d5624f6f412387aa4eb305aab0798b658c50f41398323732a17542d9fa0011a3e8e842dcc571326543cd56317dd0489ee9d6dc99e50654306d9628e40e53fecaf2c9d3000239ba68ac18c490c5a90b96314dd0426a851a9569254003a6faaa487ad58389210acb2c51c17d7076aca481b355a2c7b8f410000000480
      (by decide) ⟨141, rfl⟩ (by decide +kernel)

  private theorem rb276 : (⟨[⟨3,6,true⟩,⟨5,4,true⟩,⟨17,3,false⟩],265,2⟩ : Box).Closed :=
    replayCloses (.cons rb275 (.nil))
      19 253 0x49c52a93b4f15300272749d0e2d2f6c2d0e1768156af1f19191dda5900002917e812a5fff90900953e7f304e6c0ed3b4e164bd000a7efa04a9cffe4245337d02549bff210cd6061bb38b248c0029ddd0254c1fe44d0b83b3bb193005df34bd66a93b40000012a6b7e634e37d5ef3d01200d0c0e95a72b43d2f400cab6a74bab74953002f77b734a96161616870bb40480000012274fe60000
      (by decide) ⟨132, rfl⟩ (by decide +kernel)

  private theorem rb277 : (⟨[⟨3,6,true⟩,⟨5,4,true⟩,⟨17,3,false⟩],253,2⟩ : Box).Closed :=
    replayCloses (.cons rb276 (.nil))
      13 108 0x17b8b17f7f7fbfd85b226004c6d93bdb8bd00000482edfe61202c5f4090567fe41af6a9c5c1dd8dd3b403b6ed0a4687d696400001266eff30900932d7f9800
      (by decide) ⟨126, rfl⟩ (by decide +kernel)

  private theorem rb278 : (⟨[⟨3,6,true⟩,⟨5,4,true⟩,⟨17,2,true⟩],315,2⟩ : Box).Closed :=
    replayCloses (.nil)
      30 267 0x4b98fe63a7740977efe4726e812e1dfc8085e81208fff2030fd0241effe4074f40904bff9009056ff31469697bd260005afa04832ffc8048217f9860f215ac580480120d1fcc15ea6b6b26962e993032952a746c523a5900000120d9fe619319ae36beb4cd0000e9f40906eff90cd06560c6f3d7a850a0001e3e8120b1fe405f7409048ff200000000000000
      (by decide) ⟨157, rfl⟩ (by decide +kernel)

  private theorem rb279 : (⟨[⟨3,6,true⟩,⟨5,4,true⟩,⟨17,2,true⟩],259,2⟩ : Box).Closed :=
    replayCloses (.cons rb278 (.nil))
      21 246 0x3474fab3e64bd0003a42d68e3c80000254d6fcc2aad42f588500025afa048997fe41189c59b59d264c020ee8585e8000091247f304a6e8122477f20aad3b6be1300004a367f3157aa5bab6e93b4000128edfe62cece4ccfac44c018da327e6cf9d33400022fba04a247f909749e812ed7fe4651b179a3ba4f200755f40970bff2000000000
      (by decide) ⟨129, rfl⟩ (by decide +kernel)
end

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
mutual
  private theorem rb280 : (⟨[⟨3,6,true⟩,⟨5,4,true⟩,⟨17,2,true⟩],205,2⟩ : Box).Closed :=
    replayCloses (.cons rb279 (.nil))
      24 357 0x255b6df983d7e7a04bd68ffaaa68d29469a5949aac58496e1fdc41f1e8128327fe400757d024062ffc17f74c24178ff71cf1f40972c7f9090093593fa90bd3095367f046b9ba049acefe41562fa04aab3ff53fba612a5fffdc159dd02457f7f2004b2bdfe26cfa61225eff8225edd02496f7f208be7a04a2a3fe8b1e984a387f7009456bfcc1174fa04a2ddff45f74c2515dfb82794cf9fd274c0128a8737add8e18059f3a787e7e64e9800000cf1e812649ff91474c59659fb4c980354b1642e3260000095277f9800000000
      (by decide) ⟨102, rfl⟩ (by decide +kernel)

  private theorem rb281 : (⟨[⟨3,6,true⟩,⟨5,7,false⟩,⟨17,2,true⟩],369,2⟩ : Box).Closed :=
    replayCloses (.nil)
      23 235 0xe6dd25092c80e0e6e568b14746e9835d6feb27b3d9ee9da0240052f4c6d26d74dd3da59ecf6154c04800c5e9853f5c189cee76f69e40000e9e98631af62ddbbf69e40480377d3019be921ae42b592b773658864f410d717d6869b0b0b3db2f40431bc674f71d30000095f4c052fa62b6bbd33dd58bd01200d1e98091e92e5640c9a5a94adc1410ae621c3d040000000000
      (by decide) ⟨184, rfl⟩ (by decide +kernel)

  private theorem rb282 : (⟨[⟨3,6,true⟩,⟨5,7,false⟩,⟨17,2,true⟩],295,2⟩ : Box).Closed :=
    replayCloses (.cons rb281 (.nil))
      28 337 0x912bb733b97f4f74e9809011dbe84d13c4a54492d4858ad58c54f4105df386bb7a96967b0bb40002227a8fd41e62a75062c63d7d0420dad513fab52b23404822c7a610e2b7ac59ec97a045e4247dc8090351c55b27f52e913000886e98637383b5ad3a7ba5e81966cef77c460240739eb9650b94217a2a43506ac7acf4139afa035a86896526e8b1eabe82725f4c731eaaf2b912970c692cb2c7a8f5162d4c5252f7654a95563c65137217af56580483a0f4c36f4c373b8da596e91a00995759ded9ec97a000071ee980000000000
      (by decide) ⟨147, rfl⟩ (by decide +kernel)

  private theorem rb283 : (⟨[⟨3,6,true⟩,⟨5,7,false⟩,⟨17,2,true⟩],281,2⟩ : Box).Closed :=
    replayCloses (.cons rb282 (.nil))
      13 118 0x1200d0f937db3d92a60005227a04a91bfc800d98ad7ac668005247a04a907fe41b74ccdcecdcd2b3c8031a1a1d5e35a7b3db2f40195364e2949e4048000048953f9800
      (by decide) ⟨140, rfl⟩ (by decide +kernel)

  private theorem rb284 : (⟨[⟨3,6,true⟩,⟨5,6,true⟩,⟨17,2,true⟩],349,2⟩ : Box).Closed :=
    replayCloses (.nil)
      32 252 0x25c17f98cbc99b27b0b274c0480b1a51db2bbddeef2c28d000012e23f98e03d025c77fc8eddd025d07f9106f60ecd0fcc9e4048012e2df98e0dd025d5bf9009059ff300907cfe60120fdfe601209dfe622a1d593dd96f774f2000193d0241d7fe4052fa0483cffc8048217f98048247f30da63bbacf5ea77e85e4000387a600000000000000
      (by decide) ⟨174, rfl⟩ (by decide +kernel)

  private theorem rb285 : (⟨[⟨3,6,true⟩,⟨5,6,false⟩,⟨17,2,true⟩],281,2⟩ : Box).Closed :=
    replayCloses (.cons rb284 (.cons rb283 (.nil)))
      23 259 0x359acb2772c97a0106d7addb3f3270c014faddfbd4600005297d0254f3ff2199a6ac52f5a58036c1859393ea48d000004a9d3fcc51f1dd5df50b25e8000244f5fe6120dc6cea5fdfa4bd0022a7a04a36ffc86cddd7a17f497a0000946aff3009470fe6012e4bf986138b4b3dc5e8031d986d69d0b4ba768001d67a04b81ff22b746bb332dc5e800025c57f98000000000
      (by decide) ⟨140, rfl⟩ (by decide +kernel)

  private theorem rb286 : (⟨[⟨3,6,true⟩,⟨5,6,false⟩,⟨17,2,true⟩],259,2⟩ : Box).Closed :=
    replayCloses (.cons rb285 (.nil))
      16 290 0xc6cf55ab52c97a0046485cdb5e737ca585e40480008abba04a281fe400945edfcc2405f3d024151ff202b1989d9c7900cddd2df9f9c74c00002a6e8120a3bf9090c93f409333ffc8daa6864766e77691a0057593b4cf993b5b3c801066786542f5fb4f2000024cfdfe6121993d024cebff22b74c1bd4b0b4ba5e8011dd5ab52e2a60047b63967b3a4c98000329ba04991dfc81b26e786271da01ce646e7f638600014b3f40953bffc80000
      (by decide) ⟨129, rfl⟩ (by decide +kernel)

  private theorem rb287 : (⟨[⟨3,6,true⟩,⟨5,6,false⟩,⟨17,2,true⟩],243,2⟩ : Box).Closed :=
    replayCloses (.cons rb286 (.nil))
      11 101 0x36bc8618f9d3b4002b07a048aa9fe4009156df984804b2fdfe60124bc7f30c7a6a3677efd0b648c000124a07f309096b740925ddfc800
      (by decide) ⟨121, rfl⟩ (by decide +kernel)
end

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
mutual
  private theorem rb288 : (⟨[⟨3,6,true⟩,⟨5,7,false⟩,⟨17,4,false⟩],385,2⟩ : Box).Closed :=
    replayCloses (.nil)
      27 231 0x1dfba632b1eafabf75c5755eaf3785530267dab3a9c5b61627670c000038f74c70ee98eede988ae7eb894e53d9e5b3b4048034fd319b45fd6863bb9cea1d0e144c0e23899f6f1705ead9da0240062f4c41f19d5f3885eecf6967b4bcbc81eb4369c17650e27a5e8090240133d301d3d3013be980adf4c59d6f0e8e544e87cb4389e2e18000044f4ccb3dc4a9db6567aa556280000000000
      (by decide) ⟨192, rfl⟩ (by decide +kernel)

  private theorem rb289 : (⟨[⟨3,6,true⟩,⟨5,7,false⟩,⟨17,4,false⟩],339,2⟩ : Box).Closed :=
    replayCloses (.cons rb288 (.nil))
      22 310 0x3685935b47fde5a1eac2fd00008dee9883ca5b05ccf57f313b326024119dd773dd58d01d55d549a6248798c477412178b45d8fc7f313d2f4048229bac36303a69a4968368360f777301c5076e76db6dbee374ed01200e27e980bb52c3a525e80071df427157721a4388de6ac7af37314072c5f5a9c6d37e7e7f62a0037c71be3c677dbab670c000039afaa4212b486cd35635b590b563d57d04b59d03f373b33871a995941200ef3e980b6ed0d9e395aae270a460001d87a5ace58b3496ca46ce55950f9b98a00000000
      (by decide) ⟨169, rfl⟩ (by decide +kernel)

  private theorem rb290 : (⟨[⟨3,6,true⟩,⟨5,7,false⟩,⟨17,4,false⟩],295,2⟩ : Box).Closed :=
    replayCloses (.cons rb289 (.nil))
      18 280 0x12279ff31d393f3a2fc79d85b4f575715e8091eba5ccc76c74b5656ce980000913b7f980a1544cee99e1859d8a8019c0c2fcf2c8e56c7648c0000096be92d275925998b548c6cdcb1252fa0906a7dd7ef9f9fd646803dcdf6fee9ddcb03b246024001267d6d6bcb98434a03a60db2c4903d040f5d9c8d6d1ed7aba1c2bd000303735e6e7169bea179000008bdf486c4e6c2f50aa529315349b98c4efa09b789e5d2d5edd513857a066d8d0e34beaf47f363853a024240462fa6000000
      (by decide) ⟨147, rfl⟩ (by decide +kernel)

  private theorem rb291 : (⟨[⟨3,6,true⟩,⟨5,7,false⟩,⟨17,3,false⟩],283,2⟩ : Box).Closed :=
    replayCloses (.cons rb290 (.nil))
      13 162 0x1accedb19d67132b63b3740e99cf78bb6d97a1f571389e2ed010cb793cec779649180000174fa0482ddff200b87d024156ff90960f4ecf2e2a6024016f74090543fc800482d6fcc452699dc5e581e9da01c37379bcbfa9b4b3a171668090000c96e8126577f20480
      (by decide) ⟨141, rfl⟩ (by decide +kernel)

  private theorem rb292 : (⟨[⟨3,6,true⟩,⟨5,6,true⟩,⟨17,4,false⟩],355,2⟩ : Box).Closed :=
    replayCloses (.nil)
      34 358 0x1c17a8bdc89ee831acf23780d973141215277ddcfabd5d2f405df191e8d2c5727680072df5c4f254a47d529237b2d2aac794f410347db8de581c9a3003aafa6398f51a4ad1bde517932cb1ea3d12c86c55cb65e1acd790798f11ea24d65cb69be3e5a1e9fa0241c87a6384fa44ae0d1f3d8b5e6598d58a39774c776e98e8dd30127e99078d2e1f341e565b2c4317a08d39cfeb15c17eb574a98000042f4c074f4c05efad3e72f462bb2c4eb2a2b31e6280edf4c066faeb97a29d1bd12425782579b98a3a785cd65bb5f9aaf489809007afa23081c58ac06cb3c92ccd5628000000000000000
      (by decide) ⟨177, rfl⟩ (by decide +kernel)

  private theorem rb293 : (⟨[⟨3,6,true⟩,⟨5,6,true⟩,⟨17,4,false⟩],295,2⟩ : Box).Closed :=
    replayCloses (.cons rb292 (.nil))
      20 363 0x323ea7399eae2ba1d97a001f4fa68b9ef17edaaeced0014f699ecf9617974898000091317f31b6a767cde715c4f489805ef691e99582fabd226001b53c9ce72bcbc2ee85a1c4e9768090000091327f319bbd96ee82f97974bd00004898bfcc321b1836bd6edd0b1000903d02449dff238dec6caf9f1c2d0ecc9800476fa27a2b68c6c50c5e41cb18a9e8247cfaa5b9239b9596bc4b282aac62c7a091ddd12c27d50181863c4f454b56319dd09958bd18b1e0f74dcb1e04eb7bb83b4e2b93f40023dba03e58852b01b7292e8c63cc635ba09c7d3ace9676f3d5d3f4048231ba0a346dd4169e095e495896e6310dd0400000000
      (by decide) ⟨147, rfl⟩ (by decide +kernel)

  private theorem rb294 : (⟨[⟨3,6,true⟩,⟨5,6,false⟩,⟨17,3,false⟩],279,2⟩ : Box).Closed :=
    replayCloses (.cons rb293 (.cons rb291 (.nil)))
      13 245 0x74f0e0ff3f6f2e9fa000090593f980285f40905a7fe4240533e8120af7fc814d4ca773332babcb65e806dad9cecbde78a98000024150fe6120120afbf3193c9bd05c2d57254c03aa45d8e17742f2d91300000bdba0482defe41eeb76bd3b3cb254c0484bcb5c31dd9c6e9da01c6d5b7bb7dc4e8000009322ff98e9fab6f17332b0b55d91300e9f372ba5cb0bcba5e800009522ff9812000
      (by decide) ⟨139, rfl⟩ (by decide +kernel)

  private theorem rb295 : (⟨[⟨3,6,true⟩,⟨5,6,false⟩,⟨17,3,false⟩],273,2⟩ : Box).Closed :=
    replayCloses (.cons rb294 (.nil))
      18 229 0x267ddb9b1fb6f3a1e97a02407d647b5174b6bedb2f4048004a289fe61222cee8128bfbf91abc4f8fc715fd74bcdec9d0008abba04a281fe424009458df9863f5f5336dfd8dd374048338d99b5bdace169da006db8c67a797f1e9da0001d383732a2bf97db246024000002517b7e612028bf409057ffe473bbb5beece24600d4f50b7b8d18000017cf4090547fc80
      (by decide) ⟨136, rfl⟩ (by decide +kernel)
end

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
mutual
  private theorem rb296 : (⟨[⟨3,6,true⟩,⟨5,6,false⟩,⟨17,3,false⟩],265,2⟩ : Box).Closed :=
    replayCloses (.cons rb295 (.nil))
      19 247 0x15bd369e6ad2b63aceced01d7eb8b4ddd8385d2f405da9e1da779f9755c574385ba0000658dd025946ff9025b3d024941ff212b9e8124adffc8480124a27f3090092543f989dcee4c1735ec7eaabb2f406dcafcbceeafee95fd59ae176809042f0ba9dcfd7cd3617e656874bb4000430adb95f8e7baa6bd5852301200004b17d024959ff9090092503f984ba7d02496eff90095774092503fc84804a2f3fe600
      (by decide) ⟨132, rfl⟩ (by decide +kernel)

  private theorem rb297 : (⟨[⟨3,6,true⟩,⟨5,6,false⟩,⟨17,3,false⟩],253,2⟩ : Box).Closed :=
    replayCloses (.cons rb296 (.nil))
      19 276 0x16b7305ce8595f95d2f404d922796172eee5b3b40009cbf5a1b8f58beacc9816be173586f95f9727eb89c2dd01ccef9d52db5bba71766db4bc8000c46c616eb1d5f3cb2b63e5e5e400000012e6cff30900973dbf9804b9cdf98481aedf40935f7fe424024d70ff308be9e2fcbcd7d1eae913006f995d329e3740000ab9e8122adffc848048aa5fe602574d77d5369697fbfdfecaf672ac8000056afa048a8bff200122bfbf3090543740915adfc800
      (by decide) ⟨126, rfl⟩ (by decide +kernel)

  private theorem rb298 : (⟨[⟨3,6,true⟩,⟨5,6,false⟩,⟨17,3,false⟩],243,2⟩ : Box).Closed :=
    replayCloses (.cons rb297 (.nil))
      17 143 0x20d9d5ead1cac9d303692fbb3ad7ef537fb4b0a460000362fa0486b3ff21206e1e8121ae7f90900941b9fcc54e5b7b67376763d27401ab535b9349d2fd6b72e2e5000020e2f40941e3fe400250607f309007d7d02406affc80
      (by decide) ⟨121, rfl⟩ (by decide +kernel)

  private theorem rb299 : (⟨[⟨3,6,true⟩,⟨5,6,false⟩,⟨17,3,false⟩,⟨241,2,false⟩],3919,1⟩ : Box).Closed :=
    replayCloses (.nil)
      16 223 0x1b7329c2ad4b9796ced000538be8125367fe44d23733df6ced5d226065d3638349dd747cbfd9595a5e400036eb6359f17ad9ae1bd97a02400000929d9fe61201253cdf984804a4f8ff3166368c57dceeb95d5b2f40db53f6e57c5dafb3a5e809031c185f3f38f201972a986cac6e9a5272ddac0fdb2a00dcedcb94d666ebcdd9c540024000094991fcc240f6cf4093d07fc8
      (by decide) ⟨1959, rfl⟩ (by decide +kernel)

  private theorem rb300 : (⟨[⟨3,6,true⟩,⟨5,6,false⟩,⟨17,3,false⟩,⟨239,1,false⟩],241,1⟩ : Box).Closed :=
    replayCloses (.nil)
      22 221 0x36d4e1795f5729f57139ae15e8000256b93f9863a3b9ff7fb05c2eaeac289802279af2952d2c0173b5fb4e6bfed5fe6db6cbd002c583a3ba26c9ac2def9a5880275b59e362755c97a0009000016bf3e812b5e3ff212012358bfe6121cfcfa049cf1ff90a767cab747165f6b7b657fb2a540001ce1fa049cfbff9039edf40939fbff200123323f9848fb67d025f7fffc8
      (by decide) ⟨120, rfl⟩ (by decide +kernel)

  private theorem rb301 : (⟨[⟨3,6,true⟩,⟨5,7,false⟩,⟨17,3,false⟩,⟨233,2,false⟩],10525,1⟩ : Box).Closed :=
    replayCloses (.nil)
      23 258 0xcf3143727879b9a16975b8bca8048e58fb7c693b25b2b66c7e5f97cbb4005df4e6bc9cd63b0bfb0b672d28d00000004ad7e1fe6004ad7b6fcc241af17e81235efffc839d8d80fd52dfd7fd396f613e15e8001af63d0246bd1ff9006be0f4091af53fc8eca26942c7c767176716680006bcb74091af5dfc848d5fcfd025abcfff90768c9ea374dab6ecdb71668006c689a191bae2e2f8c2f20000025abff7e61201295f47f984804b171df98
      (by decide) ⟨5262, rfl⟩ (by decide +kernel)

  private theorem rb302 : (⟨[⟨3,6,true⟩,⟨5,6,false⟩,⟨17,3,false⟩],235,2⟩ : Box).Closed :=
    replayCloses (.cons rb300 (.cons rb298 (.cons rb299 (.nil))))
      21 155 0x31a6ef7f56729c993012049dd617739ae666b99e585a3000000484ecfe60133be812130ffe4240242787f3091c717a04b8f1ff2189fdd297164d180c6a74bd3de1e8f4dd002f6a76bcafeed7f5e9a300000127b1bf30031f5f40931abff200
      (by decide) ⟨117, rfl⟩ (by decide +kernel)

  private theorem rb303 : (⟨[⟨3,6,true⟩,⟨5,6,false⟩,⟨17,3,false⟩],231,2⟩ : Box).Closed :=
    replayCloses (.cons rb302 (.cons rb301 (.nil)))
      20 169 0x32abd2fe0ed37ec7bfaf4fd020e49cf96e766fb63b27400dacf42a50bd3d3d30bc0331f0986f6dd8d99c5cefcf2f00013ca1fae6ef6fb2395b1e2ed0039de7e3da76f646db63f2fcba5da0000000952f1bf3173bafd7ff3d9e592a60004bf1f40912ec7f90906cf7ba04b6743fc84804bf64ff980
      (by decide) ⟨115, rfl⟩ (by decide +kernel)
end

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
mutual
  private theorem rb304 : (⟨[⟨3,6,true⟩,⟨5,6,false⟩,⟨17,2,true⟩],231,2⟩ : Box).Closed :=
    replayCloses (.cons rb287 (.nil))
      21 240 0x4a8d8fe60a3a3e812a37fff200488df7e612012c3ebfcc29b0583d373246800523da669bdddae99a0240000dfdd024364ff2004a0f4fe61200f9fa0480cfff91964d0e4d37bb0ba64c00e93b46e9adbb4f200eb23038ded662fb6ccd012000000313d0240637f9002406bbf31540f0ccc8e3a600a7374fcf88c000012eb17f301d7cfa04bae3ff2000
      (by decide) ⟨115, rfl⟩ (by decide +kernel)

  private theorem rb305 : (⟨[⟨3,6,true⟩,⟨5,6,false⟩,⟨17,2,true⟩,⟨223,1,false⟩],225,1⟩ : Box).Closed :=
    replayCloses (.nil)
      20 216 0x1b03ccf7b6b0783b2f40036d87b7a729e0f33ace47f3d9f2f203de4381e4dd7b3b1d97a00000025cb86fcc2432e4fd024cbcfff23973a3e4e970763b1d9d300a9d4c4c8ed4aef74bd000065f0f40932ee7f90900952fdbf98e5f68723fd8a98000c73be8126387ff206d59ac7871da0000961c4fe6004b0ffbf3074fa7a04ba72ffe407ed9fa04bf7bffc8
      (by decide) ⟨112, rfl⟩ (by decide +kernel)

  private theorem rb306 : (⟨[⟨3,6,true⟩,⟨5,5,false⟩,⟨17,2,true⟩],217,2⟩ : Box).Closed :=
    replayCloses (.cons rb305 (.cons rb304 (.nil)))
      21 200 0x79f2828766db8b2b63c513012000120db9fcc00906f6ff3006eb740906f77f23ac503c5fab5b74c98010da934d9d2768000093af0ff3090e6b7d024e6effc82584c0f340e3b29e77eb5a9468000166fba04acc8ff2120123387fcc2eda7c3ecff6326000a697a0494efff9090274fd02426bffc800048
      (by decide) ⟨108, rfl⟩ (by decide +kernel)

  private theorem rb307 : (⟨[⟨3,6,true⟩,⟨5,5,false⟩,⟨17,2,false⟩],205,2⟩ : Box).Closed :=
    replayCloses (.cons rb306 (.cons rb303 (.nil)))
      27 242 0x2430efa791e88a4c3be9f87f30934f8fc3ff820904b9f4bd0244b9fbffe09efc7a61209ef8ffdc31b99aeb694a9de3bdb1da5e9958803daaf7cd8c929d2dafec764794a8090000952cffaff3052cfff740952cfe4ff20a67fd77409533fe07f9090095367d9fe62963fdba04a963f7bf900095337e2ff82d7e2fa6120b5ff3fc1120096e4fd02412de7ff909009315ffbfccbc9fa61265e17f0401200
      (by decide) ⟨102, rfl⟩ (by decide +kernel)

  private theorem rb308 : (⟨[⟨3,10,false⟩,⟨5,4,true⟩,⟨17,2,true⟩],399,2⟩ : Box).Closed :=
    replayCloses (.nil)
      20 290 0x706e920a6ea7990842b20ab98a2293a64e1c99da7900000093f499e499a2b227bb82b98862f4136d24dde5e93260054576a55b87d596400480267a603a7a602a7a60337d31372aab27d7eb2cf2059a1f535f9c5e800007afa0a3b6c3da0febfadd3dbe68b1406afa8df96bb7da5a55daef3617b6bb4ccdcc5000001fbe980a9e980cdf51eeee4b82c1530789640710c9e8209f386cfd3333a7e809005afa604ca957bd6d64c9809004afa600000000
      (by decide) ⟨199, rfl⟩ (by decide +kernel)

  private theorem rb309 : (⟨[⟨3,10,false⟩,⟨5,4,true⟩,⟨17,2,true⟩],349,2⟩ : Box).Closed :=
    replayCloses (.cons rb308 (.nil))
      24 322 0x1ccfd16f6b5fd78abbcb655e10ad963d4fd04aab9e236bd691a0241ce7a4ebb2175d835b247612d921ab1eb3d04038a3769d88500003b6fa0ae44f730565831e4ccc071e5be8a7ed8efb693d2c07a8862c794f513a2fa4b994ba9e64821e6e881c50ceda33ad68c99a0019543a79abc9d6628000761e89515753c4a60c56556285333250e9f393a4680001dfba63693f70cec64c00a07949c3659a46800073eeb924b99a43d782cd5628e9dd3011e9f386c92f400c5252daa4b20001c9ba6000000000
      (by decide) ⟨174, rfl⟩ (by decide +kernel)

  private theorem rb310 : (⟨[⟨3,10,false⟩,⟨5,4,true⟩,⟨17,2,true⟩],295,2⟩ : Box).Closed :=
    replayCloses (.cons rb309 (.nil))
      20 270 0x1253438b2b4e92f40486cb47176d374ebd0a34048000240f4999b82cc1518879a6a603893fba084e1f4922a162c85b8214d5624dee8232376f2d56f5a79012027b7a0de53a5f46f1d929b8b5b2777962486e823155acadb5f5a5e8030da3c38bd008eccd6cf5649da000458f4c1568b07d7adda6e8107ca6569d279012008f1f4d47a5fb306ec9b6ade166317dd04a49ca0654e91d3c8090650c1c48c9e4000385fa60000000
      (by decide) ⟨147, rfl⟩ (by decide +kernel)

  private theorem rb311 : (⟨[⟨3,10,false⟩,⟨5,4,true⟩,⟨17,2,true⟩],279,2⟩ : Box).Closed :=
    replayCloses (.cons rb310 (.nil))
      15 143 0x24cc5fcc24024cfdfe60953a6ab9dac97a000093327f3087cb5bbdb402ad58a86871da00003317d024cb3ff218f4ecde9d3a4a98091162cdeacf5244c0481bcd1c185ba4f2000000254c5fe6000
      (by decide) ⟨139, rfl⟩ (by decide +kernel)
end

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
mutual
  private theorem rb312 : (⟨[⟨3,9,true⟩,⟨5,4,true⟩,⟨17,2,true⟩],361,2⟩ : Box).Closed :=
    replayCloses (.nil)
      28 335 0x32b321e7aa5a72810626ce1f58ed00004bb8fe604cd7a6f7e9d254c048012e43f98e13e812edbfe40dabdd56a54b48d012004baf7e6387740973efe4776f409736fe4456c31be6749530120048297f3009042fe60120fdfe602f7d55f8431b8a3b0aec76bbe6cb10ddf410337d47992582a6654b050b37310c9e8afd5ee36bb2592e2f6f8f79621ebea7707edeed36dd70b2d162480794aedabd6d74f2000193d0241d7fe406afa6a596a7a0c96516212be82052fa53b41bdb92d335ff76fb775621e3d040000000000000
      (by decide) ⟨180, rfl⟩ (by decide +kernel)

  private theorem rb313 : (⟨[⟨3,9,true⟩,⟨5,4,true⟩,⟨17,2,true⟩],285,2⟩ : Box).Closed :=
    replayCloses (.cons rb312 (.nil))
      26 247 0x254d1fcc2566968d5b1d3000278fa048963fc80930714aa1c70d9ca0000244aefcc01c1d5e629491a001117e8128bfff20128e1fcc158b562c529254002387d02515bfe4773f40971fff202cd9a8748d5acb2c8001c4fd025d3ffc86b3529ae3e64bd00004b8cfe60ab58ab70ccc913009bcc57a6674ed3b4000e53d025d6ffc80000000000
      (by decide) ⟨142, rfl⟩ (by decide +kernel)

  private theorem rb314 : (⟨[⟨3,9,true⟩,⟨5,4,true⟩,⟨17,2,true⟩],251,2⟩ : Box).Closed :=
    replayCloses (.cons rb313 (.nil))
      22 280 0x1cc5e812e71ff2004b903f9804aaa6fcc0091553f98cadba04b29efe40092587fcc45dbe8128beffc822f1e8128a4ffc88bfba04a2c9fe42402517b7e61558a8736ef5a79006690ad63d492a01cd7aadec3000000482aefcc11d2974c2fe92f40483bcd70eea5246805189f1afcc2c97a0000024ccdfe60036a15aa527900ec30a46b6234014c396cdaa1b9bdb585e40000012670fe60000000
      (by decide) ⟨125, rfl⟩ (by decide +kernel)

  private theorem rb315 : (⟨[⟨3,10,false⟩,⟨5,4,true⟩,⟨17,2,true⟩],253,2⟩ : Box).Closed :=
    replayCloses (.cons rb311 (.nil))
      20 231 0x643dcd6693c8005583d025554ff2120122bcff981b566a1a5a38d2340193b142a55a969e4000ca07a04b29dff212012ca9bf304f1a9a3ac92f404800128be7f309009459bfcc4563d025151ff9091178fa04a2b1fe415e238b3633401ab5297cfefda6e8090000168f4090587fe45287d87d74000048289fe600000
      (by decide) ⟨126, rfl⟩ (by decide +kernel)

  private theorem rb316 : (⟨[⟨3,9,false⟩,⟨5,4,true⟩,⟨17,2,true⟩],241,2⟩ : Box).Closed :=
    replayCloses (.cons rb314 (.cons rb315 (.nil)))
      19 223 0xe262d1dd3a4bd0000488c2fe600488deff3011a1e81223fbfe405250dce4fef9d386000091d83f98048ed1fe60048ecefcc124786274f526e80002586e7f301b49fa04b6cfff218dad266cf525e80158a8718c49e40296595bd6a93f40caa77528d1a17e6cd1809000000975a3f983afee812eb27f9090097277f9800
      (by decide) ⟨120, rfl⟩ (by decide +kernel)

  private theorem rb317 : (⟨[⟨3,9,false⟩,⟨5,4,true⟩,⟨17,2,true⟩,⟨229,1,false⟩],231,1⟩ : Box).Closed :=
    replayCloses (.nil)
      20 209 0x542a6d0c2f1e6f36cbd001acc56a162d9a5644c0002df27a048b7ebff2120b7b1e8122de8ffc88ace726b6ef55acdd000122df07f3000916f5df98ebff3e812ebfc7fe4075ffee812ebf93fc84804aafccfe60295aa97eb4a9697a00cdd6a9267769e40000049d773f98ba158d379719300001295f9ff309147c3d0254773fc8
      (by decide) ⟨115, rfl⟩ (by decide +kernel)

  private theorem rb318 : (⟨[⟨3,9,false⟩,⟨5,4,true⟩,⟨17,2,true⟩],229,2⟩ : Box).Closed :=
    replayCloses (.cons rb317 (.cons rb316 (.nil)))
      18 183 0x174f967a4c000763ba04876fbf9076d2f40976efff9091dba3d025db87fe400956f9ff300249b27fcc24024eb63f988a56ad30714b48d000e387e812e3effe424025c6a7f30719ee812e39bfe411b5afe99bd3a742c2ed0002ef9e812ba8ff909009118bfe6000
      (by decide) ⟨114, rfl⟩ (by decide +kernel)

  private theorem rb319 : (⟨[⟨3,8,true⟩,⟨5,4,true⟩,⟨17,2,true⟩],355,2⟩ : Box).Closed :=
    replayCloses (.nil)
      33 269 0x66aca5fa664bd003aafa04b85ff91d87a04b9cff23bf7409749fe412d06168e3c801d7ba04b90ff23a7740977efe46de78deb3d4953012004bb37e600e6f35a6d6f69e40000483cff9804824ff98048367f3009076ff3009056ff31b6a86214a474f202400905aff301abe81208bff20317d024167fe401b01c5e4a3593a1590000f1e9800000000000000
      (by decide) ⟨177, rfl⟩ (by decide +kernel)
end

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
mutual
  private theorem rb320 : (⟨[⟨3,8,true⟩,⟨5,4,true⟩,⟨17,2,true⟩],283,2⟩ : Box).Closed :=
    replayCloses (.cons rb319 (.nil))
      22 246 0x91bb788d693c80550bd7a91dd268c0000499edf980c70ee99f5244c00012a6f7e612a70eacda32324680012dba04893dfc8269663d52ada7900026374091237fc8e0335c9d5ea4bd00004a2e7f30178d1d662f400012889fe632c1b985b2742c2d9da00047b740946f7f2012e87fcc6daa469786800025c67f300976dfe60000000000
      (by decide) ⟨141, rfl⟩ (by decide +kernel)

  private theorem rb321 : (⟨[⟨3,8,true⟩,⟨5,4,true⟩,⟨17,2,true⟩],229,2⟩ : Box).Closed :=
    replayCloses (.cons rb320 (.nil))
      23 282 0x68adc5669394036f0ecb6f7d64f2000001eefa0480f1ffc8012cb13f9804bcf6ff30698bf40969bfff20e91e8123a0ffc8012dbcff980496c9fcc00921b1fcc024d6eff30357dd024d48ff20abee8122a47f90025949ff300925e3f9812d1f409257fff20128b7bf30454dd0251477f20120be7f3005dbe8120beffc865cf40932dffc811d0ad66c7ab3c800cc1e812654ff20000000000
      (by decide) ⟨114, rfl⟩ (by decide +kernel)

  private theorem rb322 : (⟨[⟨3,8,true⟩,⟨5,4,true⟩,⟨17,2,true⟩],223,2⟩ : Box).Closed :=
    replayCloses (.cons rb321 (.nil))
      11 101 0x729ff3e86bbe9729f47fe612407f0ff042a36681d2952d2f40392495b9bcd92a60004afa3d0252be1ff9002473d1fe5c4b0496649e65121ab161235f6fc100
      (by decide) ⟨111, rfl⟩ (by decide +kernel)

  private theorem rb323 : (⟨[⟨3,8,true⟩,⟨5,4,true⟩,⟨17,4,false⟩],385,2⟩ : Box).Closed :=
    replayCloses (.nil)
      27 320 0x725f4c759f497b5764bff3d559e0d97d2e997f3558f21e8215e38d9e9c6ece371b0b740483a0f4c761f4164a1ee6a1659672e5e0ae63d7ba09cdba26a85a48ca87bb82b2c51c16336287d694a006d0d36cd52b24e800716ea3d69263cf77218f12ccdcc7b37413d7bbb5beeadd25e80014bd30167e985fe57e597fce5597b9eaf332fcd5628f5ed4acddbb9687670c000085e980c3f5cf33dc9589667890d299980e2173d041db191e4d2d8ff52eac2bd00000e9e9809df4c056fa602a7ab5db9fc2b3b65faac27c5c210e58a0000000000000
      (by decide) ⟨192, rfl⟩ (by decide +kernel)

  private theorem rb324 : (⟨[⟨3,8,true⟩,⟨5,4,true⟩,⟨17,4,false⟩],319,2⟩ : Box).Closed :=
    replayCloses (.cons rb323 (.nil))
      26 349 0x26774142850792ae364164b18f3124774112c9db707aa5797974ed01200224fd453655d95335e6830a55cc0718f9e82452fa0c7a9652c5b287982ae4980e318be8247cfa6acc162aaf7310b2cb558c58f410d6474adf3eb56c72b0b7400023a7d7244b45aa4c942cc495ab481c6207a091ddd05eaa4d3cc4b51f452c6ac633ba09d496f4e0e17e74a98056dd64747c7d58ff4ac2e180001c2fd31de7a08535036a16aab59b2c79cf4136d9b9a5aa1776913003aefa6182cd6beb8fdfa96172800074df4c924c9572ab55725e6893c999b6c784f410000000000
      (by decide) ⟨159, rfl⟩ (by decide +kernel)

  private theorem rb325 : (⟨[⟨3,8,true⟩,⟨5,4,true⟩,⟨17,3,false⟩],285,2⟩ : Box).Closed :=
    replayCloses (.cons rb324 (.nil))
      17 198 0x1cc58fd4bed93f40068782c68c9ca000024cc5fcc751a9eb995a1e95300439323a38dc1d9d3b4000292be812a72ff20379b8a3b69ed6d3d2f40029a3e812a5fffc80286d6314b7591a0000953dbf30a696feda7aa174bd01226a9c6dcf2ee92f402cc4d14f53a543d2f4000090bd02448fff20000120
      (by decide) ⟨142, rfl⟩ (by decide +kernel)

  private theorem rb326 : (⟨[⟨3,8,true⟩,⟨5,4,true⟩,⟨17,3,false⟩],271,2⟩ : Box).Closed :=
    replayCloses (.cons rb325 (.nil))
      18 247 0x6d85abf7ad592a600629306976e1bd3a159000048ad1fe6120122b1bf309196efa04b2c7ff20124aa7f3025f3e8124b8ffc80492d1fcc0024968ff31161fa04a2f7ff2120128aa7f30900945f3fcc025158fe6120128bfbf31b6d6471bb38a98012d54f0c2dd268c038ec1dd8ddd244c00903ada55b113000fd65396eed526e8000001167740945fdfc8000
      (by decide) ⟨135, rfl⟩ (by decide +kernel)

  private theorem rb327 : (⟨[⟨3,9,true⟩,⟨5,4,true⟩,⟨17,4,false⟩],369,2⟩ : Box).Closed :=
    replayCloses (.nil)
      36 332 0x1dcfd55f2f15d2fde74bcbd2cbd97b2f49aac50cdd86d56d1dd6428090739e925a532cb52598b7042921e63d67a09cf7d2d5162b3127964d40f9aac7aefa09d27a8b73154cd506ab332cacd564363c27a093669adcf2fcc953003b8f4c04d646e757b64bd00388f4c77ee98e5dd31d3ba63bb7a63a374c079fa56bb61ecbc90bf3b3165fd8bf46ac50127eb9967990c2f52c95a2aab10c5e82061fa0b651b06141ca8348582b98a03a7a602f7d12d16e0856698f2c86cd2b9886efa082794ac1eafeeae5a1c29180006efa60000000000000000
      (by decide) ⟨184, rfl⟩ (by decide +kernel)
end

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
mutual
  private theorem rb328 : (⟨[⟨3,9,true⟩,⟨5,4,true⟩,⟨17,4,false⟩],313,2⟩ : Box).Closed :=
    replayCloses (.cons rb327 (.nil))
      21 314 0x4d438b646cecae9d3000a74fa04a9bbfe429c1c5efeda70b0b65e8091e6f70fa8583838db346000025496fcc34da9e3697ceed3a6001207a04893bfe4139ba95d01f07b3c7578dcfc8ae4b65893dbd3214dd2a65f97f365f13b458f0d148c4f0d9b5f985856400022b7d0490b21417ab3063b69e8f318a9e8229ed5dd6f0cceab4f742bd01208f5f4c47cfac38e5036e0a82cd16a8551e63163d04e3add199b3fb274c0023fba8c5f9c5766bec16597e667faba42d58c78fa084aee371eddd244c0638d1ceee85937404808d6e9800000000
      (by decide) ⟨156, rfl⟩ (by decide +kernel)

  private theorem rb329 : (⟨[⟨3,9,true⟩,⟨5,4,true⟩,⟨17,3,false⟩],279,2⟩ : Box).Closed :=
    replayCloses (.cons rb328 (.nil))
      19 261 0x92533fcc240249777e6121286e8124b5bf9009454bf980128a67f3054d71cdbae38606d6eb167b5afba4e800025174fe602289e8128a37f91b4a72dc1df7e6574e980759bd8bab97dba74c0392d86cdd6962e93a0072e56b170d9eaf42b200000015f74090523fc8b353a3c3edd5bb4898005367a04a907fc8e13732d9daa174898011d3964d365bb9fafd0b74000029e3d025493ff20004800
      (by decide) ⟨139, rfl⟩ (by decide +kernel)

  private theorem rb330 : (⟨[⟨3,9,true⟩,⟨5,4,true⟩,⟨17,3,false⟩],259,2⟩ : Box).Closed :=
    replayCloses (.cons rb329 (.nil))
      15 175 0x1d54f40975b7fe41d70fa04baadff21239dbe812e7dff900955b3f98012abc7f309009551df9804aa96fcc0091533f9848048ab1fcc025944ff3002594b7e60e919ad6f6d693b400f4564ea5bbd599a00009654df9800492c3fe60000
      (by decide) ⟨129, rfl⟩ (by decide +kernel)

  private theorem rb331 : (⟨[⟨3,11,false⟩,⟨5,4,true⟩,⟨17,4,false⟩],421,2⟩ : Box).Closed :=
    replayCloses (.nil)
      17 132 0x3b774c090aa7f59d43a5ddcb6768001d9ba639374c045fa0a6edcfecbf5762bf558e7e2b16280b3f4c4dd32a666bf3f367e9d8bc8000042f4c06cf4abe2eebf8e96fdaafe539f9e65ed96280fdf4c05efa600000000
      (by decide) ⟨210, rfl⟩ (by decide +kernel)

  private theorem rb332 : (⟨[⟨3,10,false⟩,⟨5,4,true⟩,⟨17,4,false⟩],391,2⟩ : Box).Closed :=
    replayCloses (.cons rb331 (.nil))
      26 314 0xe8beb1765ed6fec0fe159e5f979ce579b2c7b8f41398f415a966696531f45af3558f51ea2cbd54c7f578ae967f5d674bc83563c47a886b5335c1d9c5c6e36ce18090741e98234a36ab5f30b67e8585a51a031eeca81cb776ed2f4048036c627d3cedcf762bf985da00001c7ba639774c719ac3ebf5c1dda68c00ecdd31ddbd30c35ac7addbb4f2024014bd30167ea326c82cd2dd12522a18f310d3f410217a603eb2a3528593a606d5a16ce371b254c000267a603f7d3017beaab37725667821660369bcc4377d04000000000000
      (by decide) ⟨195, rfl⟩ (by decide +kernel)

  private theorem rb333 : (⟨[⟨3,10,false⟩,⟨5,4,true⟩,⟨17,4,false⟩],367,2⟩ : Box).Closed :=
    replayCloses (.cons rb332 (.nil))
      17 320 0x26f24ed3d1b4e870b67e80cf70c3766149c302b627eb9de5fdfb4e98000eb49c0e7b5bfb0ba74c0087281a1edaae6e76bf34ac814adcdc5d579c9930005dededacfcc9b1e0ec9180bb75e583950b27680000111dd77316a8aa0a162485664dcc5087697f7f7db254c04875b1a1b3976bcba64c0240e1bd349eab4e5796878b86000110dd31de7a66a795c1a490a1528d49b98a176b699fee76174bd01214d4e2ed7f53656d3a1c2ed0120003b4f4c33cc8ddbd7aad6428090103c3c3f393ebd42c2e2cd0393ac91b58dd9c6d9da024001ca7a600000
      (by decide) ⟨183, rfl⟩ (by decide +kernel)

  private theorem rb334 : (⟨[⟨3,10,false⟩,⟨5,4,true⟩,⟨17,4,false⟩],339,2⟩ : Box).Closed :=
    replayCloses (.cons rb333 (.nil))
      16 230 0x3acfead6dc1f2e9930029afac36f42c2d2c29500002377d0524963c762ccc492595cc07189df4126aee371b4b742e9d301208c8d8dd7cc9b25b8bebf52f2e5018c97abbb9627e38aec70a2602400000466fa8af3a3bf24d7eaf0ba697fe85d32d5628abb76d583a35b7591a024118be989bc8ee31797fbbb9797170c093e3231383bb174ed000023a7d365fd9d9c5c9d5ea176597f32fcd563103d040000
      (by decide) ⟨169, rfl⟩ (by decide +kernel)

  private theorem rb335 : (⟨[⟨3,10,false⟩,⟨5,4,true⟩,⟨17,4,false⟩],315,2⟩ : Box).Closed :=
    replayCloses (.cons rb334 (.nil))
      16 208 0x3ae294eddba87a64c048642763ca523a62809000009533bf313668d2dadcb43d3f400b277aadba4f5000096da1f6ccff6174e980103e6cf616fbfd95e5853a0520719b4747f69ca00011a9f59b9a1f2b6d615901200000933e9868624a138950b4535589207a084f079a39b77aad0a340a9d8db7973717fba768000004b6e98000
      (by decide) ⟨157, rfl⟩ (by decide +kernel)
end

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
mutual
  private theorem rb336 : (⟨[⟨3,10,false⟩,⟨5,4,true⟩,⟨17,4,false⟩],295,2⟩ : Box).Closed :=
    replayCloses (.cons rb335 (.nil))
      20 232 0xd4b7df6c2c2c993032ad5b67a71c3032daee7c3d58ed00004c0f9bf35bdbaa16cbd006b3776dbbb964bd0000a49fa04a99ffe44d35d3e776e8585b326024079e7f617fbaa16c898090c6070b16a733ab4c9800000254d5fe600dd753b25b2bba16cbd000e247a706eb24e81944fb677f712300000f29cf6bab73fdebd42ed008e694f077bdbfddd668c00000002923d025483ff2000
      (by decide) ⟨147, rfl⟩ (by decide +kernel)

  private theorem rb337 : (⟨[⟨3,10,false⟩,⟨5,4,true⟩,⟨17,3,false⟩],283,2⟩ : Box).Closed :=
    replayCloses (.cons rb336 (.nil))
      17 246 0x49edda60e371b67680bb0b6f8e37d5efd79cae2e180071f1c1b6cef993f4000da9989b6d6fda768066dac1ff6f5e7ab4b0b74000846b3e774cfcce851a000000259dd02497f7f2120128a97f30f424d31b8dd00004a2f3fe612004a2e9fcc72d477a69b2bbb4898167a666b529dbac7644c0cb074c693366d6161714a80041bdc3ab17fbab4bd012000120bc7f309014cfa0482bdff20480
      (by decide) ⟨141, rfl⟩ (by decide +kernel)

  private theorem rb338 : (⟨[⟨3,10,false⟩,⟨5,4,true⟩,⟨17,3,false⟩],279,2⟩ : Box).Closed :=
    replayCloses (.cons rb337 (.nil))
      20 201 0x364ee18d23a3bacb202ea3939bf49ca06d238bd4b54e95a1f2e2ed00003e2de55afbcba5e8156cb8ceddbe672b2335d8e17e800005bdd19d2baa574bd00258ca9efcf2eadd644c0480d75bd31afbe58f4e98052eb6511def57dbcef3a5da0240ebe38373fb074a5617971768000000009252bfcc2402494cff309095774092503fc80
      (by decide) ⟨139, rfl⟩ (by decide +kernel)

  private theorem rb339 : (⟨[⟨3,10,false⟩,⟨5,4,true⟩,⟨17,3,false⟩],273,2⟩ : Box).Closed :=
    replayCloses (.cons rb338 (.nil))
      20 210 0x5eeb637ea4fdbba56c8980259303eb760c2c1d985da0166076db397fb274c04801d9ae0e360bf57bf6ae2e1809000000025942ff3090096513fcc339b5f3f3b30b4d18154369b8f6fe93b40e768d1a66352e9da00195cf6a9c1c768072a7a7360e2c9da061c6d7f48e3260006c7bbba57fba7680000000965a3fcc24009654df980
      (by decide) ⟨136, rfl⟩ (by decide +kernel)

  private theorem rb340 : (⟨[⟨3,10,false⟩,⟨5,4,true⟩,⟨17,3,false⟩],259,2⟩ : Box).Closed :=
    replayCloses (.cons rb339 (.nil))
      22 256 0x983c373ede592f403ba76dc6c174beb4bd002f59642e9bae923009eeb1be32a7baa16571768000000189f40901edff200480fb7e6123aa9e812eb6ffc84804bab6fcc357dd024d48ff206a3ba049abefe42402556cfe6122a91e812aa0ffc80b6f4e676bdbbb07ab4b8a460091dc855df9bae0f97ecbd00000004aab1fcc154cfa04aabdff212012aa5bf309055efa048aa7ff2000
      (by decide) ⟨129, rfl⟩ (by decide +kernel)

  private theorem rb341 : (⟨[⟨3,10,false⟩,⟨5,4,true⟩,⟨17,3,false⟩,⟨251,1,false⟩],253,1⟩ : Box).Closed :=
    replayCloses (.nil)
      23 242 0x59d8a97d69796c918001b5bdb6dedcf574bd008c0d8d8c8cd60765f657169590120e7f9ea7c3832abb19f77ab8d4a74000369503cd9237d717b657f4acacab202400000024f777e60e86d98dc1d9c6e9a30008ecd70b9991f8e4723cae95e80003d6dd024f4f7f212012e367fcc59e50b03c9f54b4b664c05da4f73c2f7b45ece97a03acd7eba527fa7baaced000004b8e8fe61218eb740931eefe42402547a7f98
      (by decide) ⟨126, rfl⟩ (by decide +kernel)

  private theorem rb342 : (⟨[⟨3,9,false⟩,⟨5,4,true⟩,⟨17,3,false⟩],243,2⟩ : Box).Closed :=
    replayCloses (.cons rb330 (.cons rb341 (.cons rb340 (.nil))))
      20 311 0x41eecf707fb1fa0301f21a191ddeaccd014e36eb437b6b6dfd8b0b34000169ee8125b37fc8480496b6fcc24db3db6d89b6e2d9da035e63714393f5fd8b0bc800021f9e8124347fc8480490fb7e6120129b7bf3001d1be73bf31dc5d346073ad6719f0e57f3f4e470af400036bb9da74df6c6999ed8e274b4600000c75ba0498f77f212012a373f9848237dd0244647f91b40f8fead6dad8b66e80160f9cd6adeac9d0bc801b78e81f2ff64bd00001243edf980129a47f309035afa0486cbff2000
      (by decide) ⟨121, rfl⟩ (by decide +kernel)

  private theorem rb343 : (⟨[⟨3,12,false⟩,⟨5,4,true⟩,⟨17,5,false⟩,⟨241,2,false⟩],12929,1⟩ : Box).Closed :=
    replayCloses (.nil)
      16 184 0x14d365b8decedbfb4bb2a60339a9a51399dacaf97b6c8d2c9801cf220a1726b66dadd6ebcb9404817716eb5a4657cdb6cd18000000972f3bfcc24025cbc4fe619738a150d29575ad0ac8076f2bafaad9bd6c8e46c8980000025cbc8fe614eafce5795f06574e9809153d1aaf75cef8c8f07f5ad8af40000049570bf98
      (by decide) ⟨6464, rfl⟩ (by decide +kernel)
end

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
mutual
  private theorem rb344 : (⟨[⟨3,10,false⟩,⟨5,4,true⟩,⟨17,3,false⟩,⟨241,2,false⟩],9531,1⟩ : Box).Closed :=
    replayCloses (.cons rb343 (.nil))
      21 308 0x32f6696e2b1d8f9b99c2fd0065ebd45d8f4e1783b30bf40480001255dcfe61201255eeff31e7768ea67bf5b5a5f2c2bd00679da07462654ad2d62cd00a305e8ea64d56dd9c18513007353e436bd385ccecc2bd0000055cafa04957cbfc8caa647c3b33b5a50bfbdb4bc0000024ab86fcc240252ba1fcc32ea6e7abc8c0d8e56cbd01214d2fed7cbf8364dd86fcd7b3260240a795cde74bfa53f1cb7b1e2bd000038e27a04b8e37f911c335e4ff4cc57a7e8006d9ba6bab558e8745c289800014bf9e812a5d1ff21218e47a0498e0ffc8
      (by decide) ⟨4765, rfl⟩ (by decide +kernel)

  private theorem rb345 : (⟨[⟨3,9,false⟩,⟨5,4,true⟩,⟨17,3,false⟩,⟨241,1,true⟩],8193,1⟩ : Box).Closed :=
    replayCloses (.nil)
      24 266 0xee6ced76bf36dd3b406a7bba9697d91d2460001a98d7375c5fda76809005c9c4e8ca72d9de5caf2e29d012000018ff7d024c7cffe415536d54dcfed3b400063c9e81263ebff218d970b49cedbc9c2fb61717680000c7a3e81263bfff90cf2c950bcc1d254048018ebba0498e07f9031d3740931c77f20012d9d4fe61201259daff300911fb7f3013385f4094cf4ffc84804a0e17f9883b3f40941f7ff9002507e3f980
      (by decide) ⟨4096, rfl⟩ (by decide +kernel)

  private theorem rb346 : (⟨[⟨3,9,false⟩,⟨5,4,true⟩,⟨17,3,false⟩],241,2⟩ : Box).Closed :=
    replayCloses (.cons rb342 (.cons rb345 (.cons rb344 (.nil))))
      10 52 0x1cf1ba048e71bfe40c7c3d024c773fc84801243d1fcc09386e81249eb7f20
      (by decide) ⟨120, rfl⟩ (by decide +kernel)

  private theorem rb347 : (⟨[⟨3,12,false⟩,⟨5,4,true⟩,⟨17,5,false⟩,⟨239,2,false⟩],23543,1⟩ : Box).Closed :=
    replayCloses (.nil)
      15 307 0x6787756ebd9e57a1b6c2bd0006c7fadd024d8ffbbf909009331e4ff98663c2f409331e3ffc848012663d6ff3009331ef7f98198fabe812663c5ff9009331f17f9848004998fd3fcc29858ceddbbaf0dedbe3644c075aef90319f9ce578bb3b2ff32b2a54000663f0fa04998f5bfe40cc7e6e812663e77f21aa713d5d963a4e53c5c5c5ba000c8fe4fd024c8ff3ffc80012647f3bfcc56e5739ed7daf4e97b5d595daf1656576800351f07a049a8f53fc848049a8f9df986a3e37409351e37fc80012687f73f98
      (by decide) ⟨11771, rfl⟩ (by decide +kernel)

  private theorem rb348 : (⟨[⟨3,10,false⟩,⟨5,4,true⟩,⟨17,3,false⟩,⟨239,2,false⟩],14275,1⟩ : Box).Closed :=
    replayCloses (.cons rb347 (.nil))
      24 290 0x117a5ba335840cafe70b2600009343fc5fcc009343fadfe62cc0e476bfa9707a7e802ee0c8d275f4ae9130176d5aa9aed91df5f3ab552d1800000d0ff57d024d0fe2ffc80049a1ff4ff3009343fe6fcc0311ef7d024c47a7ff2012607fc3fcc00d87d3f409361ebffc848049befe4fe632e99503ded0fc72368dc2bd00da75e91e9dad6e6d96400e75df2f3517b35babb32600000c27cb7409309f5dfc80126dbfb3f9804998fddfe60004998ff9fe61201266decff98
      (by decide) ⟨7137, rfl⟩ (by decide +kernel)

  private theorem rb349 : (⟨[⟨3,9,false⟩,⟨5,4,true⟩,⟨17,3,false⟩],233,2⟩ : Box).Closed :=
    replayCloses (.cons rb346 (.cons rb348 (.nil)))
      21 161 0xca17bbdd8afabcac8ecbd00dbb7686c8c29d7369eebcef385d2f57280000024c3beaff3193c2ffbc38df3274c036e569d97e2ee6c7a44c00001261df67f986edf9ba049bb7cefe405e5bac5b99d2b668c0000499b7c5fcc240095af0bfcc245589f40955edff200
      (by decide) ⟨116, rfl⟩ (by decide +kernel)

  private theorem rb350 : (⟨[⟨3,8,true⟩,⟨5,7,false⟩,⟨17,2,true⟩],391,2⟩ : Box).Closed :=
    replayCloses (.nil)
      27 350 0x1366f39b83eec2e9a300038efa5abfcfd8ba5663da97623e98e58f2df413a4f5dd6287e869ee8c58f09e82705f4c8bb4585d55a56b3f16a7f65f9aac7b8f4138cfa4cca96e4d1a5bd61643cc7a0f41105bd5ae6b491a03ae0d2eeccc2c9da000741e98530e9a58d94fe7e7bb3a16979018fb8e6d1fadd74f200075ee98eddd31ddba614e289c6e76cc1ff7f428d014ef6d3cee8f11300120e2dd658b1255941031a1e66ab1ecdd04e8dd30167e9aaaa10a4f754addc155621a7e823ad299f5edbec2e95301200c5e98085e980c3f58bb2fc5d292e9b8ed73b32bdcf125b9885cf410000000000000
      (by decide) ⟨195, rfl⟩ (by decide +kernel)

  private theorem rb351 : (⟨[⟨3,8,true⟩,⟨5,7,false⟩,⟨17,2,true⟩],347,2⟩ : Box).Closed :=
    replayCloses (.cons rb350 (.nil))
      23 311 0x639a93c1fee5932602404f6f4c10c6a93d4b01a4bdc16e6038921ba08c7c11b77364f2000452f41659796e55143cb73558c59fa0847a6d3e6fcfef9a5b3c800046cf4962fcab92ecd4bb727df2c6267a09113d266f3ec9aae9eaba421be58c7afa086b139dfd4da592f40258ecd276d85a1e9da000450f4c5eda769d0f978727e80900470fa61ab58b9dfdfa4bd000896e94544f55e429299a62d56286675c62e234048539a4c5c6ae1ce9d0b4b4a3402ac6b5ac9f9938602400044374c705e9800000000
      (by decide) ⟨173, rfl⟩ (by decide +kernel)
end

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
mutual
  private theorem rb352 : (⟨[⟨3,8,true⟩,⟨5,7,false⟩,⟨17,2,true⟩],295,2⟩ : Box).Closed :=
    replayCloses (.cons rb351 (.nil))
      17 331 0x25b76b54a27f491a001be64cea6fe93f40000499edf98a68ccdea5a6ff74bd00ae191c6e371fa0240c8687d60e964bd002ed8393ba76ed3c803d613bb1030001aa181e37f7f64e9801cdb73c3c5fdc3d1d95300000004a9e7fcc6d63a393baeb246803aea74768e5649d0000004a993f9827efa83e44d2aa8d60e56cb126efa5159e0a0b21cbd42ca49301c784c95e796a97ab3940e3c9db693f5cb248c04800963d26e4b545dbcb042e589347aebccc54b912962a285642f31270f41e0c5968931ab1262cb3dcc07124000000
      (by decide) ⟨147, rfl⟩ (by decide +kernel)

  private theorem rb353 : (⟨[⟨3,8,true⟩,⟨5,7,false⟩,⟨17,2,true⟩],283,2⟩ : Box).Closed :=
    replayCloses (.cons rb352 (.nil))
      9 74 0x12ca67f9883abd52c5c44c09a1b83d37af56d2340000ca3ba04b2befe44543d02517eff9002516f7e600
      (by decide) ⟨141, rfl⟩ (by decide +kernel)

  private theorem rb354 : (⟨[⟨3,8,true⟩,⟨5,6,true⟩,⟨17,2,true⟩],385,2⟩ : Box).Closed :=
    replayCloses (.nil)
      32 275 0xe87e812eeffe4156eb67e7f7ef9b3b400e5be812e77fe42989e996f7717a00709e812e1bfc80934a55acd55ab7a9d4ac800009779fe636aa5ef9c5e801d07a04b94ff2012efdf9804bb77e63977409701fe4025d5bf3106489b99ade933400004b937e601208bfe6012093fe60217a04823ffc80f9e8120a3fe411b18ef0fcd9cba790000b9e8120b7ff200000000000000
      (by decide) ⟨192, rfl⟩ (by decide +kernel)

  private theorem rb355 : (⟨[⟨3,8,true⟩,⟨5,6,true⟩,⟨17,2,true⟩],333,2⟩ : Box).Closed :=
    replayCloses (.cons rb354 (.nil))
      19 234 0x3a737772cf64bd0095dd39bea9b276800474f3865b8bfb4bd008b150eeadcbf3cb679000001226cff3107465bdde5c5e800025117fcc31f1c7cf84c00234fd02515ffe415358dabdb889800474f40944bff90c7674787db8d5b5b3d400004a357f9804a307f30094777e61aa199fdfbd72e9fa0240094537e6392f40975fff2000000000
      (by decide) ⟨166, rfl⟩ (by decide +kernel)

  private theorem rb356 : (⟨[⟨3,8,true⟩,⟨5,6,true⟩,⟨17,2,true⟩],295,2⟩ : Box).Closed :=
    replayCloses (.cons rb355 (.nil))
      15 223 0x1263e52b9ad13bb4cd008353c39393fb6748d00683e6ebdfa4bd00006537409323bf9027a637a9ec2c2e9fa031d9a1aee2ce9386003457bcc9fdb3a790014f68ef0f37bb5a5bcb8bc80000025485fcc530707a737adda7900033a35a99fdfb4f20005357d02548bff23285ad51393bb4f20735663d63c80015ce4ecfef993460000244edfe600000
      (by decide) ⟨147, rfl⟩ (by decide +kernel)

  private theorem rb357 : (⟨[⟨3,8,true⟩,⟨5,6,false⟩,⟨17,2,true⟩],279,2⟩ : Box).Closed :=
    replayCloses (.cons rb356 (.cons rb353 (.nil)))
      16 183 0xcbb58e4e369bdd9ed9e40aa4c7cd2e3b404800012cb17f3090096513f98012caa7f30025970fe62b6dbf5bd8b7a769e40004b2aefcc0979fa04929fff208d92e9fdcbcba5e8045baf7af98593f400e85a30b1235b4c180298d7b113f324680000116b740945ddfc8000
      (by decide) ⟨139, rfl⟩ (by decide +kernel)

  private theorem rb358 : (⟨[⟨3,9,true⟩,⟨5,7,false⟩,⟨17,2,true⟩],411,2⟩ : Box).Closed :=
    replayCloses (.nil)
      25 303 0x1d6bb7a567b8c98090751e82d12ac1a50629397b0eac788f4102d1d5ed81fe9ee9e4000ec3d258bf62fd8bb2ecbae8e2fc8bc2f2b85926438a384fae4b8927992b5262ccf3282071418674cfd7749e40532477167b3d93b4000ea3e98eddd31c3ba6296650ed7d64d6b3c8090716ea2d55b10b16aa9a2c7b374138374c4563538dcefccec1e0e1790000a5e980b3f4cf3c9824a1b7256e2537314049fa66df2bf2b7eed5ff95979d99c1ceb658862f4106d335cc4fabae9e40480267a600000000000
      (by decide) ⟨205, rfl⟩ (by decide +kernel)

  private theorem rb359 : (⟨[⟨3,9,true⟩,⟨5,7,false⟩,⟨17,2,true⟩],355,2⟩ : Box).Closed :=
    replayCloses (.cons rb358 (.nil))
      25 353 0x1cfad36fbfdc5e8090eba3bd89bec0f967bfd85e400008fdf41eee640fac5a92c872c6277d046a5797dad2b254c002217d762ecba23ebb97eb9d82ff472c51183d2c5db8f145d2aecbd2e971fcb1881e8244f74962fcc8bf353fd2f2bf32f8ba2fc4f31445b74c492b8312526534d66a792e8a1c635ba081b13a736fb8bc39ecac2e18000725e98672a3a4775d748d0329af4ce99c592340481d6db5ddaf2df67b3d9585da02401d67a4145d255db0f64bfccba2ed0ba65b98a02a1e6d27b5feff74a9809075df4c41c6f7ebcb2bc39595853a0001dd7d05982c1660acac11ac84ac54c363d57d04000000000
      (by decide) ⟨177, rfl⟩ (by decide +kernel)
end

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
mutual
  private theorem rb360 : (⟨[⟨3,9,true⟩,⟨5,7,false⟩,⟨17,2,true⟩],315,2⟩ : Box).Closed :=
    replayCloses (.cons rb359 (.nil))
      17 233 0xca0755cc4eefda790121a2ca77df9fec97a00a8ca8d7b96174e98000025493fe6012252fe6091dc1aeed7070ba5e80c6558e4e4e8fd616cf20650b53fbdb89d00018f8f0c2dcd693c8005e8589dd8b248c0000266fa048937fe441c4d6db83fed2e91300024f74c45838a6bea96fba5e80013dba61ef1c6e379b4b4ba6e80900452f40714b0daf55dc485cb18b3f41000000
      (by decide) ⟨157, rfl⟩ (by decide +kernel)

  private theorem rb361 : (⟨[⟨3,9,true⟩,⟨5,7,false⟩,⟨17,2,true⟩],283,2⟩ : Box).Closed :=
    replayCloses (.cons rb360 (.nil))
      17 171 0x48a96fcc196cf4096507fc88a17a04a28fff21222edf40945f7fe425c8687777677f74bd006bdc637e697fba5e80900dab1b2d91e3a600000093387f3007168fadd8bb3baccd008a871bab7cff74bd00adbac369394e7b25e8000032fba049923fc80000
      (by decide) ⟨141, rfl⟩ (by decide +kernel)

  private theorem rb362 : (⟨[⟨3,9,true⟩,⟨5,6,true⟩,⟨17,2,true⟩],399,2⟩ : Box).Closed :=
    replayCloses (.nil)
      28 294 0x1c77d025c1ffc8da4d6d9bb97f69d3003aafa04b85ff915bb31af637267bddb23400004bb0fe6387676d674e85d22604d4762a1ddeb4f200009721fcc0dc3889a54ab699a024009751fe6012ec3fcc72ee812e03fc8eedd025d7bf904707379cdf3bb3bbb0bc80901d9ba04ba77f2022fd02417ffe4024167fcc3059bf7cfcc93a025c37acfd8ed00004834ff9869a1b7b5736967b666800062f409071ff2000000000000
      (by decide) ⟨199, rfl⟩ (by decide +kernel)

  private theorem rb363 : (⟨[⟨3,9,true⟩,⟨5,6,true⟩,⟨17,2,true⟩],319,2⟩ : Box).Closed :=
    replayCloses (.cons rb362 (.nil))
      28 279 0x15a76d54dfd25e800124fd0244cfff2096be812265ff904cee81227f7f2092dd0244aefe401e19d73a3ea4f200009469ff304b36d2c5fd25e80113be812887ff230cae1c5d3b3b3b366680169a6327f7ed3c800025163f98242a56bd63940023fba04a327f91b76a5c36db277eb2f40480128cefcc44b74094577f2012e67fcc51b1b5a790b0b0b65e8016375aed77dbfb4ed00004bb4fe6000000000000
      (by decide) ⟨159, rfl⟩ (by decide +kernel)

  private theorem rb364 : (⟨[⟨3,9,true⟩,⟨5,6,false⟩,⟨17,2,true⟩],279,2⟩ : Box).Closed :=
    replayCloses (.cons rb363 (.cons rb361 (.nil)))
      22 250 0x32e9aeeaf9d1c9130002b37d02454dff90024574ff3015c3d02455cff20048af6fcc65f3d025951ff2269ad8e4c6cec2e9da00009656bfcc3ae2a1e6c4cef9a5b3c80009453bfcc009454bfcc256686b469d0b0ba74c00012640fe618eaa6c2a600146f1bdea752e9d3000199dd024cfefe4068e6ddbbf7ce9a3002ad49aa872637eb39400002973d0254b7ff20000000
      (by decide) ⟨139, rfl⟩ (by decide +kernel)

  private theorem rb365 : (⟨[⟨3,9,true⟩,⟨5,6,false⟩,⟨17,2,true⟩],273,2⟩ : Box).Closed :=
    replayCloses (.cons rb364 (.nil))
      13 92 0x54ed437c6b6d67bab0bc8000358dd024d46ff9002554eff31570ee89e6e34600f79e38fd8d93b400004aac9fcc05533e812aaf7fc80
      (by decide) ⟨136, rfl⟩ (by decide +kernel)

  private theorem rb366 : (⟨[⟨3,11,false⟩,⟨5,6,true⟩,⟨17,2,true⟩],421,2⟩ : Box).Closed :=
    replayCloses (.nil)
      22 207 0x131de59d3a749fa04d0aef97bd42e9da0007377771b3d85d3a60001c47a6384fa63b8faa382ec47c217de9ec3b279c3962820cab7d737b96ced000038f74c74ee98eadd1cfb3a6dbf66e3e950e15a8e1660bc21798a3a374c3ad3aeea6fa9d3acbd01200a5e980f3f4c119227c944cb67b4b0bc800069fa60367a60000000000
      (by decide) ⟨210, rfl⟩ (by decide +kernel)

  private theorem rb367 : (⟨[⟨3,10,false⟩,⟨5,6,true⟩,⟨17,2,true⟩],399,2⟩ : Box).Closed :=
    replayCloses (.cons rb366 (.nil))
      28 388 0x1cf7d5215227996b335253558f5df4126e1e99d4b8c98001dd7d2ea3d1fa8e73b31ce75d56d3d233e599c961b1eabe820352f4deae74f20241d47a43f28dda70b5347e65bf268e486ac788f4120e8fd76b4b4b4b3db3b4000ec3d725dccb3cd16a958a65cc51c27d263b51fa8e739ced27c2ecfd47c3a56e6283bc67356ddf3a7681360da8d732deee9da001d47d31dbba63a774c352b0637cd93dd2f404838b74c73b2c3f297f4ad3d2ec476abab1ecdd04e0dd30ddc6b5d9d3bd7e85e4000297a602cfd31db86739ce7e39ce73b4e16a5a72623392986c50127e9af7ea5a7693fd4705f83d3b69f4d56218bd040d9e89e66ab3599a98a5e0b562133d040000000000000
      (by decide) ⟨199, rfl⟩ (by decide +kernel)
end

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
mutual
  private theorem rb368 : (⟨[⟨3,10,false⟩,⟨5,6,true⟩,⟨17,2,true⟩],369,2⟩ : Box).Closed :=
    replayCloses (.cons rb367 (.nil))
      19 254 0x29d1b45ceeeeefcfa85e40d39b1cdf54b264c000023a7d6cf47ef9d9f745d82d27d88ff472c6207a0913dd77771315330596351ab1429f237ec9a585a5b2460240045b75c80d8214151da93558c6b74122f1ddcddddd93a600319ac68dedf5cbcb64e80000070bf4c6de3b75cd693c8146b50e4c8e37401ae9f31b0b248c002b6d5afad371fa076d7bdbb5f6fed2740003acf4c87e5e9f8e1b69e37b36f6bdf87162800000
      (by decide) ⟨184, rfl⟩ (by decide +kernel)

  private theorem rb369 : (⟨[⟨3,10,false⟩,⟨5,6,true⟩,⟨17,2,true⟩],351,2⟩ : Box).Closed :=
    replayCloses (.cons rb368 (.nil))
      13 185 0x106876636d79648980456244d36f64cb6cf200000452f44ccea675159d49e478f51fae7ab18b3f411af1b6eeeedefda64c048567d6ceefdf3a68c043a6a99f53bdb4b668c00008fdf5dc46cc862a67a2141ab189df412289c55dc59ef774a9815bf5c5554b248c04800885f45792e44a55d146f2d5628000
      (by decide) ⟨175, rfl⟩ (by decide +kernel)

  private theorem rb370 : (⟨[⟨3,10,true⟩,⟨5,7,false⟩,⟨17,2,true⟩],421,2⟩ : Box).Closed :=
    replayCloses (.nil)
      24 275 0x7b5d74f6fef53db2f40276aeda72d85d1e93a000751eb993333325c95995372f770521c788f413bf74c709f5ccbc7e75c7652ee15323fe2ecf2f5628a54c2bdb3a3bb48d0120ebdd31cbba639b74559970532e44c42c167ae92cb21c51d1ba6022fd2d67ff677f03eaf3abb4fbb310a5e82055364abb7df9fecafec5e4048a58f8ed6ebf5a6e9e40000a5e9808d275bd72f2e97a02401a7e980de1b9f54b0b4b2b2b0b740484802e7a60000000000
      (by decide) ⟨210, rfl⟩ (by decide +kernel)

  private theorem rb371 : (⟨[⟨3,10,false⟩,⟨5,7,false⟩,⟨17,2,true⟩],411,2⟩ : Box).Closed :=
    replayCloses (.cons rb370 (.nil))
      26 261 0x1952a2dc1fcf7616c8d01202a736b7db2df6e0fbb23c5e4001203bcfae65f17ec5f911f95d97e2fdf3d21ab14731eaaf172502e9589fd1755d7efcad963d47a08719f1f9dad2c8ecf2024001c07a6384fa63b0fa0aca2a5dc18f2d65558f31ebdd04eddd31cdba63bb7a6029db268737aada66817b8abaf60e4ed01200297a602cfd62f145c35bd976512f8bf371f91764980e281ded8dc6ca7839ee9d301200b9e9800000000000
      (by decide) ⟨205, rfl⟩ (by decide +kernel)

  private theorem rb372 : (⟨[⟨3,10,false⟩,⟨5,7,false⟩,⟨17,2,true⟩],381,2⟩ : Box).Closed :=
    replayCloses (.cons rb371 (.nil))
      19 242 0x11139de5fee2f4048da4c6d6bec2fed2f4048088ee986ada7e7d42c2e97a02429e9dac0e478b7da5a59595a5da0242400118dd05aa898b56314a8ac5cb1886e82743f5cbfaea2d5dacbb4bfb7ffd6eef2d4ecbc98798f39ea2c1cbdc144b2a4cd9e6e63c21a199fae2eefd8b648c048e8d81c4d0e5b2d91d99a00000769e98230d6c0e93fdddc1d99a00001d27a6e3e2e90ae17bf4b938bb326ab1e13d0400000
      (by decide) ⟨190, rfl⟩ (by decide +kernel)

  private theorem rb373 : (⟨[⟨3,10,false⟩,⟨5,7,false⟩,⟨17,2,true⟩],351,2⟩ : Box).Closed :=
    replayCloses (.cons rb372 (.nil))
      20 232 0xda74316b6ec5d3b404802637514bbbb892528d0a8adcd14c362486e821b52dac674b25e8090011b3d732cd316aa56e64ad4a4dcc6267a0daed0db1faaf9db75f55e94578b18fdf5132b64ea6743f6cefec2f2024240044afa539315d761b6d3c3a7da75368b18c5f411ad6c4f7716fbfdd2f40482287a61ab7b6afd4b244c0480a3046f01d90bfa169468090900011c3e9800000
      (by decide) ⟨175, rfl⟩ (by decide +kernel)

  private theorem rb374 : (⟨[⟨3,10,false⟩,⟨5,7,false⟩,⟨17,2,true⟩],319,2⟩ : Box).Closed :=
    replayCloses (.cons rb373 (.nil))
      18 357 0xc86aada373f5d3c81940f9230bcda585b2340aa87c6b56fac9da06d9a868695693c8002400cb327750e4fed3c814d4e6bfbbbfd9ecad9da00000529ba04a91dfc8da06369fd96f77fb664c041ba373b38d180900049df4cba210a1259a98c492575a7986c49dbe962ecbaa5c5795c9f9c57b2edc7e5892b7d33218f24a6924b53b50798924da667cbcb8bd012020e8d0d7a53f985f9e1ff69790394e36b8dbae365b6790380c227f676eba668002400012fba5395edfba1d84f9543bb54fb528af9624dee82452b1ea4717e74f204dcb9b8ddd4b439eff616680900012bba4a8761bf6edcab21fabc0e46bf7e56cb12477410000
      (by decide) ⟨159, rfl⟩ (by decide +kernel)

  private theorem rb375 : (⟨[⟨3,10,false⟩,⟨5,7,false⟩,⟨17,2,true⟩],295,2⟩ : Box).Closed :=
    replayCloses (.cons rb374 (.nil))
      17 181 0x96d5343ab073a7ba44c0480012644fe612198be812659ff91c954375c6e2d2e9da0242400c91e812641ff9186342eeb9ad270c06ba79bcdc5c7e80900024cc1fcc4dd35bdbea17fba64c048da87ce716742e9130122a86ced1e99196e9e40480000126437e60000
      (by decide) ⟨147, rfl⟩ (by decide +kernel)
end

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
mutual
  private theorem rb376 : (⟨[⟨3,10,false⟩,⟨5,7,false⟩,⟨17,2,true⟩],283,2⟩ : Box).Closed :=
    replayCloses (.cons rb375 (.nil))
      18 249 0x240f6f1d9fafd696cf20240d4363139be7174dd012002b87a048ab9fe412a727865bfa47a5e8000091503f9868fafb7e71da0046ab7a9985d234001b27b5fce2b82e4dd000000a8ee8122afbf90009154df98e23e9e3bb7dfee97a024195334617e77736cf20240042b999d996e2e9da0299d330beb236d8ed9da005a86c36878e1f77f42f2000000009254df98488a17a04a28fff200
      (by decide) ⟨141, rfl⟩ (by decide +kernel)

  private theorem rb377 : (⟨[⟨3,10,false⟩,⟨5,7,false⟩,⟨17,2,true⟩],281,2⟩ : Box).Closed :=
    replayCloses (.cons rb376 (.nil))
      10 85 0xaaca1c7ad993340480abdbd02555b7f208deefebefea5d226001834399d3787274c0000ab3f40915dffe4241513d024546ff20
      (by decide) ⟨140, rfl⟩ (by decide +kernel)

  private theorem rb378 : (⟨[⟨3,10,false⟩,⟨5,6,true⟩,⟨17,2,true⟩],315,2⟩ : Box).Closed :=
    replayCloses (.cons rb369 (.nil))
      18 228 0xcb46b973edfda5e8090558f8cfadd27900029a7e812a57ff90091297f304d1c199eefb67ba44c0532353ebd63b4014eb7cb6cf64ed000a48f9a597bbba44c09b06a637d73b26e8000652b5b5a96164bd002cd0d8de37bdb3de585e40010d8cb7f777f52cf6cbd000000012266ff30ebadd9adea742e9530120093dd30d66abbf52c2e9fa024013dba600000
      (by decide) ⟨157, rfl⟩ (by decide +kernel)

  private theorem rb379 : (⟨[⟨3,10,false⟩,⟨5,6,true⟩,⟨17,2,true⟩],285,2⟩ : Box).Closed :=
    replayCloses (.cons rb378 (.nil))
      18 222 0x9a98af68c8fab2340022c5e8128b8ff909114efa04a287ff212ca46e7ebf3edfda44c04865ee9c9fdf3279006648c2b7ef5a79002d99acd7db9d93c800557b14e91d1f9d3c809000003247a049907fe42e56a5d3fbe74ed000d8caf9f58fd01202cf36f6afdedfda74c06b48d333dc4e80003de4bc647d69e4000001265f7e60000
      (by decide) ⟨142, rfl⟩ (by decide +kernel)

  private theorem rb380 : (⟨[⟨3,10,false⟩,⟨5,6,false⟩,⟨17,2,true⟩,⟨277,1,false⟩],279,1⟩ : Box).Closed :=
    replayCloses (.nil)
      24 245 0x6d8d8edf7f4f6574fd01200e2f05a5adbb4f5012121aa8da5aaf5374c980c746c5b6db9dd3d40000b9afbaa468bcaf63fafebc51301200000000049ad1fcc1ac67b5fed8f1d300006b07a049aa9fe4359dd024d7f7f201aa6e8126a3bf90135552c7c74f20243335bd7d4b64d180900024d737e6004aaf3fe62ae9e812aa5ffc8da489b6d9c36693a0000095553f98
      (by decide) ⟨139, rfl⟩ (by decide +kernel)

  private theorem rb381 : (⟨[⟨3,10,false⟩,⟨5,6,false⟩,⟨17,2,true⟩],273,2⟩ : Box).Closed :=
    replayCloses (.cons rb380 (.cons rb379 (.cons rb377 (.nil))))
      19 151 0xdb865b8f5ddfdfacc9800181a9ad23b373a790000aadf4091577fe4241543d02457eff91362958b57cd37e696176807996c2c4e4f8d6b2f404800002adba048a9efe43313a16988d0329ae4f8fec5eee9da00000096573f98000
      (by decide) ⟨136, rfl⟩ (by decide +kernel)

  private theorem rb382 : (⟨[⟨3,10,false⟩,⟨5,6,false⟩,⟨17,2,true⟩],271,2⟩ : Box).Closed :=
    replayCloses (.cons rb381 (.nil))
      27 234 0x2f61b1df3d39da3d2a6065c353d303dcf574bd036918ed76950e874b64e800194353f1ced2f2fe95f1e2ed0123a86bfad5bf67cdf6bd913030fccf7270bd5fbaf45d91300000000000d8f40901a3ff21200ccfa0480deff90eb2375d1a4f96974bd002590de9b5fb9b5acf200a6bbab3e647a5e80000077ba0480d0ff22a81d3a647d49e4048012eacff98004bae9fcc24025d5f7e60
      (by decide) ⟨135, rfl⟩ (by decide +kernel)

  private theorem rb383 : (⟨[⟨3,10,false⟩,⟨5,6,false⟩,⟨17,2,true⟩],265,2⟩ : Box).Closed :=
    replayCloses (.cons rb382 (.nil))
      25 228 0x3a764d0fec5e6e9e40488bd4653fefe74b4b674c0416b079b4bcdd3c80eb9b4898ce768e7b679000cb7b531dadf5c1cf7bbab8bc809003aecd4fd63bbb97fb8385e4048cabb03ddcdb5f770e56565697900000000837be812834ffe4240250727f30d5d793aef0e564bd00020d8f40941a3ff202a999a6e373b25e80041cee81283fdfc800317e812037ffe42402407a7f980
      (by decide) ⟨132, rfl⟩ (by decide +kernel)
end

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
mutual
  private theorem rb384 : (⟨[⟨3,10,false⟩,⟨5,6,false⟩,⟨17,2,true⟩,⟨257,1,false⟩],259,1⟩ : Box).Closed :=
    replayCloses (.nil)
      24 251 0x49af0d96db6fed3c8074535e9e9cec4d2767900adcf1bcdaae5bc97a041ded59a5e3b59d6391e28d00048000fb57d025f45ff90a6f6291fdf38ba7900dbd871bbba6ebbacf20000097de3f984804be89fe61224c5fa04a4dfff91a6df3a1eac2d2e91300031add9fac91a00012677d025261ffc8093b3e81293ffff20121313f984813a3d024270ffc807b4fd024f57ff9090c7cfd024c67ffc8
      (by decide) ⟨129, rfl⟩ (by decide +kernel)

  private theorem rb385 : (⟨[⟨3,10,false⟩,⟨5,6,false⟩,⟨17,2,true⟩],253,2⟩ : Box).Closed :=
    replayCloses (.cons rb384 (.cons rb383 (.nil)))
      17 127 0x4b0e8ff3061aee812c303fc84804b0c37e614fb37bb0b15c9130120004b6f9fcc240096ddbfcc55e468d23d35b4cd00004b69efcc0024b69ff3090874fd02486bffc800
      (by decide) ⟨126, rfl⟩ (by decide +kernel)

  private theorem rb386 : (⟨[⟨3,9,true⟩,⟨5,6,false⟩,⟨17,2,true⟩],253,2⟩ : Box).Closed :=
    replayCloses (.cons rb365 (.nil))
      18 314 0x34ea5cdc5c5c5d3b40e561b1cde375d3c81b6cd8f99da591f0ece180054ed3b4f73c9caf35cacd70bc8090a7370d31f2d0f4818000000909a6fcc0093dfbfcc1c787a04b8dcff2122e89e812ba37f90096d0df9816f9e8125a8ff90024b7b7e61210f7740921c1fe405b343f5c5c1cae97a00001b3f40901efff200480d8fe6123ac5e812eb8ff90eb43d33b9616574898005c9cb674674b25e8001d5efa04baa7ff232d4fbb6375898ce87fa962f20007583d025d54ff212012e5cfe60000
      (by decide) ⟨126, rfl⟩ (by decide +kernel)

  private theorem rb387 : (⟨[⟨3,10,false⟩,⟨5,7,false⟩,⟨17,2,true⟩,⟨251,2,false⟩],6947,1⟩ : Box).Closed :=
    replayCloses (.nil)
      21 331 0x36ed3595f58575dd49c2f2039b4fbb6bf838ae5beafd8e15e8046079b49f8e579d91f2ff71668000900091ee77e63a9a323fa97e716cf202431f1a6daf99eef74f2024007badd0247bddfc8646e1852b269bfacf200a6123a37beb73a7901ccad4fc6ebfb6b95d9d300049d2e4ee6165b83c1d9e4000000ddc5e812dde3fe4306fcff653dcfbb23b334067279b27372e0f4cd02cdd7673bc3fa7be3fd0bc80001bb8bd025bbc7fc80ddadf4096eddff9090096ecb7e612177dba049777bf90a753b6ceecf473dd2f4048004b2c2ff300259607f30900253bc3f98
      (by decide) ⟨3473, rfl⟩ (by decide +kernel)

  private theorem rb388 : (⟨[⟨3,9,false⟩,⟨5,6,false⟩,⟨17,2,true⟩],239,2⟩ : Box).Closed :=
    replayCloses (.cons rb386 (.cons rb385 (.cons rb387 (.nil))))
      22 262 0x48285f0bfb9ef8bf4c25cf7f7ff8203da42f186ed23404834da719e4d2f4f974bd0000edd9f40976ffffc83b787d025db5bfe400936ceff31b5a78a2614bd3ded97a07751d58bd3a77e85a30022b9e5b5d2964f200000956e8ff30900906e2fe60bdbad7d3dd593f40480add9e812ad83fe40ded8efd64b91f8f48980000956e4fe6120124b0bf9813607a0493677fc84875a9e81275dbff2000
      (by decide) ⟨119, rfl⟩ (by decide +kernel)

  private theorem rb389 : (⟨[⟨3,8,true⟩,⟨5,6,true⟩,⟨17,4,false⟩],403,2⟩ : Box).Closed :=
    replayCloses (.nil)
      31 401 0x1a51d89d3bb67e85859ed28d01200896ea9db946a8e55363943cc16e0b30d8c537413a2f4c779e95212505a736c99b2cb1e73d04edbe8a859a38d55c37996782b3731e5be9366e1658b7b5cdf959f7abdeddbf336fe8f31e53d4475cd49d2f1f172ba5e815b55f9bb5b2f4b95e57eced000394f4c6dc373e5ff6aba1e9930120eabe98e8bea2c6dd43c37ae55c4924a6e63dc7a08bbe303dd05c4e4e98090751e9890b4b58b3ddccb52549aab0c0e3c47a09da7d13c1e5aaefac4318ad963d07a09dfba63b8faee6374b0596acf654932e63d47d04e7dd61b3495662a5cb676d963d7ba09ddba639374c746e980f3f4997765e085ee7b2ad8d5252a08d8a000000000000000
      (by decide) ⟨201, rfl⟩ (by decide +kernel)

  private theorem rb390 : (⟨[⟨3,8,true⟩,⟨5,6,true⟩,⟨17,4,false⟩],349,2⟩ : Box).Closed :=
    replayCloses (.cons rb389 (.nil))
      23 324 0x2448bfe62cc2eafc3f3b9d2cd7cdf5717680001267a0489affe4301d27f9cceade7a5e8001317d0244b3ff2085e173da5b2f55e97a00049ee989b352723e5f0779f57cb0af404827d636a95bcef3e5d5d5c523000024374c46cf4ba2f15e4306942f2342aac6267a5d57a34a565a35799e1bd979046c63f7d4485fd63b35e2f3bbb755713c5da006ce772787f5dd7a44c00023b7d4524ec1b52d4a4a7c35aac62a7a093577bb23e1d2f5755d97a024118be988c1e90d9a253c1e52ac485724dcc6207a08154d177ae73b0b43b2f404822fba60000000000
      (by decide) ⟨174, rfl⟩ (by decide +kernel)

  private theorem rb391 : (⟨[⟨3,8,true⟩,⟨5,6,true⟩,⟨17,4,false⟩],313,2⟩ : Box).Closed :=
    replayCloses (.cons rb390 (.nil))
      15 223 0x177a647f9f2c5715f2d97a00d667fa9395f6f2e91300c9c6d4e958eab92a600000527e8120b3ffc86bdfd8b4af3b1c4ecbd000dc525ccc2c4e1687674c01d72bd977a6e0ccfcc4ec70b7404800000120b87f30d875b1dd9d9e5d2460107d3386f4b6be6f35eac2d180000cf6e81266f7f22f7369c3d1c2c4f4898000254adfe618d67d9dcdf7abd5e5b2f400012a6b7e600000
      (by decide) ⟨156, rfl⟩ (by decide +kernel)
end

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
mutual
  private theorem rb392 : (⟨[⟨3,8,true⟩,⟨5,6,true⟩,⟨17,4,false⟩],295,2⟩ : Box).Closed :=
    replayCloses (.cons rb391 (.nil))
      15 121 0x5375d1c6c37a5b5ead2cafe2918000094527fcc009457bfcc29a4ee76bc5fb75756c8980914b450a2626b7ef9851a0098d0ecfcfaf9d3c802ec4fcd278bcdf579bf37857a00000115774094503fc800
      (by decide) ⟨147, rfl⟩ (by decide +kernel)

  private theorem rb393 : (⟨[⟨3,8,true⟩,⟨5,7,false⟩,⟨17,4,false⟩],445,2⟩ : Box).Closed :=
    replayCloses (.nil)
      21 246 0xef3e82f7733c5439583660737a9262071ea3d0483a3431d96ff7967b4b0a34048038cfa63a7e55799f6c4f5756270bb40480380f4c77ee989bceeea7f335d5775d9130120ea3e98e1dd30bb59fa8ce952baeabd5fae27f5f2e181666b643717262b89d97a05ed177d8595fb46f9be97a000358e1fe7838af63f1cd763c513000038b74552c42cc790b146c690f9f3731ecdd04eede98bdfd6df2e16eb93f40480297a6000000000
      (by decide) ⟨222, rfl⟩ (by decide +kernel)

  private theorem rb394 : (⟨[⟨3,8,true⟩,⟨5,7,false⟩,⟨17,4,false⟩],391,2⟩ : Box).Closed :=
    replayCloses (.cons rb393 (.nil))
      25 316 0x5d85adaafd9d2fd0f48980044cfa600c8f14a7d5f6b85baeca98090478fa67ddb0ff656bdf4a65dd0565de2cf321fe623ed07c908d8c5f7412f617e779fd7e5b46e27f5c2ed00008b6e86c6f623e35acfa5dd26e0797e6bbddacfe75631add0485f4c8e57f1f8e87cbab0af40483a9fa63a2f4c5ed0cf15f696c7b5d97a0241d77d31db7d72d4296f9a5e5255506ac796fa25905aaa1acd2c5782550dcd321b1e53d44652bca7a5d2c2ed7ab13c5c301200eebeb83d14a1691bccf58b149e60f32cb5487144d25ab529d0e967b2b3d9ed2cd00000e2be9800000000
      (by decide) ⟨195, rfl⟩ (by decide +kernel)

  private theorem rb395 : (⟨[⟨3,8,true⟩,⟨5,7,false⟩,⟨17,4,false⟩],351,2⟩ : Box).Closed :=
    replayCloses (.cons rb394 (.nil))
      23 354 0x9aee4fe7b5c4febd5b2f403a735f2febcad5727e8024fc7d9bcbc39ee99a00000013e7a048947fc826afa0878ac7a6b9b29634f3d79b989297d049bda74e5a1e0f873d9ecf657979000009a3e8965c5597728ab773dcacadc48561bcc7624dee82129ba893cf131795a6c9598d3dc4c42b0d893dbd2ee7b2b46989566e87899341038f027a6ce1cd7f3ab75d91301208f9e989b1f5dceb3c6fe723b27404802377d2aad7bf98efe2cdbc4285ab7ea7b9bf7b29f683e4846c6277d049a0648d435b87e76bfa9bfb96205efd7eb99df7fbc37bf4ae8e9668000046afa8f13152ca4c9b5ea4af2c18aba236280000000
      (by decide) ⟨175, rfl⟩ (by decide +kernel)

  private theorem rb396 : (⟨[⟨3,8,true⟩,⟨5,7,false⟩,⟨17,4,false⟩],333,2⟩ : Box).Closed :=
    replayCloses (.cons rb395 (.nil))
      13 149 0x13f5e19adf797febfd7644c05319d0d83763f6dbb7b76f6768153e191def8eac8f49d024cb6872b7df52768000000953f7f98035dd9feee70deeba1d9930120012a677e6217e32dcaf3375f2ead97a00378d8e73e5fcf9647ab0a460240014e6e812a677f2000
      (by decide) ⟨166, rfl⟩ (by decide +kernel)

  private theorem rb397 : (⟨[⟨3,8,true⟩,⟨5,7,false⟩,⟨17,4,false⟩],309,2⟩ : Box).Closed :=
    replayCloses (.cons rb396 (.nil))
      15 284 0x8b47a04a2c3ff21222fee8128b27f9006f5361777ec5d3c809010a1238a96ceadacefd2de560120008abba04a281fe454f471be9e6bac9ba031f4f074b79dd775ed766e8000002517b7f302bc4e577dd1d0f5796eb857a024134c991d69aef3aaecbd005d8525d2d3775e743b22600921b9fdbbe717161468090000054be8120bcffc803938db397e667757abab8af404ae667a6fb0382f4ed0120dbb39ee676dd9c6c8f5614e809001a3a34b1b8bfac8d000001264f7e60000
      (by decide) ⟨154, rfl⟩ (by decide +kernel)

  private theorem rb398 : (⟨[⟨3,8,true⟩,⟨5,7,false⟩,⟨17,3,false⟩,⟨283,1,false⟩],285,1⟩ : Box).Closed :=
    replayCloses (.nil)
      18 227 0x192ecbfd5baba1c4ecbd01213616872b75c5d9c6eaeae2ed0034faffcf6769bf35cafd91301cce783dae8c8e07b3ab0bb406393a395ff457cdec3bd92300030c2fed2d5e6f25e80d42163bd8ec7687aba563b1f2f8f57a8090000000240787f9848eba7a04ba97ff219db93ceee78dd012392f1e1bcfd393460246d5323ddccf8bcaf55d9da016debd3dcedf64ed00000012ea77f9848012ebc7f98
      (by decide) ⟨142, rfl⟩ (by decide +kernel)

  private theorem rb399 : (⟨[⟨3,8,true⟩,⟨5,7,false⟩,⟨17,3,false⟩],281,2⟩ : Box).Closed :=
    replayCloses (.cons rb398 (.cons rb397 (.nil)))
      19 215 0x20d0f40941fdff21200fcf40901a3fe4240240627f9863cb2696b3f4f56476768091d38ef27d5eb6ec5b1cd70b8600eb9d0dd5a5b5ff1d93a024000000955bdf9848048ad3fe62cd774bcd7df1cd735d9da074f877580fd54df9bf37b3eecfbc593001a2ed1d94ef72d367b2b8bc8000094b7409255dfc8ca75ab4edbc3dcf4dd0000128a4ff9801200
      (by decide) ⟨140, rfl⟩ (by decide +kernel)
end

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
mutual
  private theorem rb400 : (⟨[⟨3,8,true⟩,⟨5,6,false⟩,⟨17,3,false⟩],279,2⟩ : Box).Closed :=
    replayCloses (.cons rb399 (.cons rb392 (.nil)))
      14 225 0x55f86eb23ecfebfee97a000064fd024073ffc800ecfa0480ffffc848ea17a04ba8fff214f0d943d5839af4bd01d7b52d2db934d9efe851a0000975b3f983a99f409757bfe4048dd79bf9f2dd74daae1768001d40f409753bfe40724fd025ccfff220cd6e787e3bd79e97a006f27ddc7cf17a3e589d0f176809012861747abfa489800024579ff3090091553f9812000
      (by decide) ⟨139, rfl⟩ (by decide +kernel)

  private theorem rb401 : (⟨[⟨3,8,true⟩,⟨5,6,false⟩,⟨17,3,false⟩,⟨271,1,false⟩],273,1⟩ : Box).Closed :=
    replayCloses (.nil)
      25 199 0x3691c9caf878b15e2bd9da026d8d2f9f9d9e1c0ece180146cbb2fd9fa715edb23e5b1e2ed001b4e0e2b185b26bd5f1f8e6bb1caf20246d0bdbcb944d77c767171468000000005dede812badbf90914767a04a8c1ff212012239bfcc42e8bcce6beafd366bd326004a69f8f8eebe6fa5e800047f7d024479ffc80048eadfe612012c3e3f98
      (by decide) ⟨136, rfl⟩ (by decide +kernel)

  private theorem rb402 : (⟨[⟨3,8,true⟩,⟨5,6,false⟩,⟨17,3,false⟩,⟨269,1,false⟩],271,1⟩ : Box).Closed :=
    replayCloses (.nil)
      24 204 0x1ce342db15ff62c8e56168c00dd4e1ba9d965ea7a9c174bf2a0b8afe32df56d59b783f58d6400000065cee9def9703fd25d9c300ebf69f0f267b4db1cd7668c04848000049ee1fcc0f60f4093d53fc848049ee6fcc24024c727f31d39adcd2c6f2bffa56cc9804192f4626eb9595d2a600000931fdfe602eb1e812ba8ffc848a38dd0254637fc8
      (by decide) ⟨135, rfl⟩ (by decide +kernel)

  private theorem rb403 : (⟨[⟨3,8,true⟩,⟨5,6,false⟩,⟨17,3,false⟩,⟨263,1,false⟩],265,1⟩ : Box).Closed :=
    replayCloses (.nil)
      18 206 0x137c7d0249b63fc8bbd4afdb37673fb3b26edb7d9930120216374f1e2ed1bfae34afc4e970c0000049363bf300926f37e60236cfd0251bdffe4240251be3fcc247ae374097ac6ff91b4af2ec2d6e2d35b69c685c5fd8b6bc0001ebf3e812f5e3ff2176ba9aff9eaff8f4a98007ac4fa04bd7b7fc848012b5a1fcc2439eee8127383fc8
      (by decide) ⟨132, rfl⟩ (by decide +kernel)

  private theorem rb404 : (⟨[⟨3,8,true⟩,⟨5,6,false⟩,⟨17,3,false⟩],259,2⟩ : Box).Closed :=
    replayCloses (.cons rb403 (.cons rb402 (.cons rb401 (.cons rb400 (.nil)))))
      20 178 0x921e9fe61210f0fa0490d6ff9091352fa04a6f3ff21b72bfaf4bfb4df5696ca980002535aff300379fa04869fff219c34bf34b964e9800134afa04a6e5fe424025348fe6120699e8121b5ffc83a17a338ef0f87a76800024361ff3000d7dd024348ff20000
      (by decide) ⟨129, rfl⟩ (by decide +kernel)

  private theorem rb405 : (⟨[⟨3,9,true⟩,⟨5,6,true⟩,⟨17,4,false⟩],433,2⟩ : Box).Closed :=
    replayCloses (.nil)
      26 304 0xcb16946787d42ce85c564000efbe957b31ae6b3c1b41a091e1bd5dfb98dcbd9f98a217e9ece9745fb7542d0e15e809007ebe5ed3eaf9687ab1385da000729e980345df74b9585932600709e98e4be985ded99c97a3e5f9656cbd00273a4f4beae0b8af4ed000e23d30a68ba6f170b1385d3260241c87a638cfac36e0b3c13393e36482cdcc7a0f41380f4c71ee98eedd31d5baea63c962d42f255146b3cb731e2dd058a51a1590b1859a942e58f1d1ba6022fd34efe6dded7bd2a5df159b7e54df079be90b33040e214bd04000000000000
      (by decide) ⟨216, rfl⟩ (by decide +kernel)

  private theorem rb406 : (⟨[⟨3,9,true⟩,⟨5,6,true⟩,⟨17,4,false⟩],369,2⟩ : Box).Closed :=
    replayCloses (.cons rb405 (.nil))
      25 360 0x4cee829af372a2ade659608de5040e248ee82452f4cbbcb7a4ca1ddbb7c1b4efeabfead3bf99b792980e3167e82b0dff56cdd5ee9bd8f74d1bb0eedbbd26ab1e24d367b7dd25381f2d9da001187ea3ca2a66eca80ca81b2cb3cb908d8c4cf4100ecce783e1cac2d0ec898090454f4c3194f865b79d5743d2a600458f4c13b60d1783b4ec7ab43d5c5da00044cfa1ae7bb835d8d4361ba6bb0f5f6ddec97d98eff31444f74366c1cdcb5d8da3aed9b77b39f6dde1bd88fa507d80e2803cbc952d191ddba15901202af9fe7fda58af9756278b74000886e98e4bd31d393c67b4da5f1c2c4e278ba6000719e890f3310b2d4854ac6179cacf301c7b4f410000000000
      (by decide) ⟨184, rfl⟩ (by decide +kernel)

  private theorem rb407 : (⟨[⟨3,9,true⟩,⟨5,6,true⟩,⟨17,4,false⟩],315,2⟩ : Box).Closed :=
    replayCloses (.cons rb406 (.nil))
      23 284 0xe3e6296d2eaeae97a024015cf409056ffe466dd687276b4bd5c2d9fa000ce1e81265cff209274caf2f638ae8765e801b25cf63528af974d1809073f68c76078de581c0e16e8000254f3fe6298ad42f3d56dd64a8005207a04a93bfe41ac2c377bbdbef2f2d9da00009527bf31486e812a6b7f21ab2e9767c5fcf5743b3f400093be812243ff919bb365f8f96d395d3f4008ea7a7ce0fd7f65757579bd29180000499f48cd97a186f1ac7f5dcdab762dd6efa76b6e7f0f31240f4100000000
      (by decide) ⟨157, rfl⟩ (by decide +kernel)
end

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
mutual
  private theorem rb408 : (⟨[⟨3,9,true⟩,⟨5,6,true⟩,⟨17,3,false⟩],283,2⟩ : Box).Closed :=
    replayCloses (.cons rb407 (.nil))
      17 191 0xabe3877dd1eafea5b3f40083fdd0250727f9002407a7f305bbb9b99f67fa4fd0000eefa0480e3ff9000901e1fe6012abe7f30554be812abcffc80492d1fcc0978fa0492b1fe44533d02516bff904593d025175ff900945f3fcc55b5d4f177bf36db6d8e15e80000094583f98000480
      (by decide) ⟨141, rfl⟩ (by decide +kernel)

  private theorem rb409 : (⟨[⟨3,9,true⟩,⟨5,7,false⟩,⟨17,4,false⟩],423,2⟩ : Box).Closed :=
    replayCloses (.nil)
      28 409 0x9a4c1e1daf2cd7daecbd0120e73d44397b2d1c1e5557974526aa081c7acf411d72bc797fdd5d5a1c4e148c048038cf51ea3eedadd4c6a8181a436e63da7a09db7d2643e9656bde952d3bb154d7bd2b49f643ec87d98fb21fe8a1c796facadfbe0dab70a7fb2d7f61dc2b059f7cb1e3a4f5dcca0c1f2195e792857339580e3c27a08d428da5db76bdaeebfae15e80900715f4c731eb96495c06b2f56a97967bb93330d8f51eb925650ad7ed2ccf73d4b732c071e3b0f4cbb99e6a82cd2d16b06b6287bb2a65b6286ba7f3999affb0b43b2f405df1dee7696af2d0eced0120390f4c739bc3d9d97aaf6bd2f40483a0f4c74af49d2aae8727e809075ee98e1dd31cdba639374c706e980000000000000
      (by decide) ⟨211, rfl⟩ (by decide +kernel)

  private theorem rb410 : (⟨[⟨3,9,true⟩,⟨5,7,false⟩,⟨17,4,false⟩],369,2⟩ : Box).Closed :=
    replayCloses (.cons rb409 (.nil))
      23 414 0x554ec6eee5e581c8e14e8090137ba6032633e1d9d9e581d9da0004c6e931254375ad2942f69c1c6ac490dd04e3b3dd9edb78bddcb65e800462f435ce8f1bdcdcd13feaf3bb3537ecda8fc6f83834c0718f9e8205ca0729cd7dd79ead9d3012089df4b968d527a21407962376cde63153d046ab8e67aaca5fd0b0ba395e59a02424011e3d051317891b160cec5e68ace56ee61b18b1e8246cfa5d5495142d2f35e8b4f018798c50f4109ea8b9d35eebaf56cbd012008e1f4c4dbd92e5bf8e5bd57a54c048023dbd321f4996fdec47dab76f4b6ef06d37edb7ec7bc29799f7038c6374c47d28becd27c2cdbb7efdcc87da6fe2b21fe6e63c4cf667bf5fab9afcbb5d9fa006c0d67c9f677df1c2d87785da024240154c69dab6b92f40480221ba6000000000
      (by decide) ⟨184, rfl⟩ (by decide +kernel)

  private theorem rb411 : (⟨[⟨3,9,true⟩,⟨5,7,false⟩,⟨17,4,false⟩],339,2⟩ : Box).Closed :=
    replayCloses (.cons rb410 (.nil))
      18 256 0x29e4f4b9ce56965756cbd01217733caf3b75ed7264c00004a943f98638b26cf2f79ed7a5e80519513da6b3a96470ba395a51a02400053c7d0254b1fe44cf13babfb75687a74c048091a5f99a6eab56fa7e8090000254e6fcc13a7a04892ffe401f326cbce27aba5e80ca6a8e217969696146800032ed27cdfd1d91c8f56176809000491e84f2b35ea86a6bbaaf3cd5624e1e80d32ef1a861bfbefdcc6b56e66a6fc6b3ef5624d9f5100000
      (by decide) ⟨169, rfl⟩ (by decide +kernel)

  private theorem rb412 : (⟨[⟨3,9,true⟩,⟨5,7,false⟩,⟨17,4,false⟩],333,2⟩ : Box).Closed :=
    replayCloses (.cons rb411 (.nil))
      10 93 0x4cfeb1d94fabdaeabd5b2f407a6badd98cff392460001f4f9b75eb72fd8e8743857a06d05cd78bd2e4bf1e9d300004d57eed83729da743b56f65e809000329ba04991dfc80
      (by decide) ⟨166, rfl⟩ (by decide +kernel)

  private theorem rb413 : (⟨[⟨3,9,true⟩,⟨5,7,false⟩,⟨17,4,false⟩],315,2⟩ : Box).Closed :=
    replayCloses (.cons rb412 (.nil))
      19 228 0x93eaf3fd7d8ec8f56ce18091b797bdb4f74d7c9f6d2f1f8e6be5e4003238b954e0f689b5e5373b3d95d560000000004a296fcc24024179ff31cc53787aaabdaf56c8980bb938369c7713a0240867b0b9ddd19e672391c2ed000c6765eecaf6bf623e56c9d0098dfabc8f8735f9bdbb7b3b4000e9b4f964beae4a9800006fd717162be5d5d326017b75d1b4e53a1fcf2f0f478bc80900000c85f409334ffc800
      (by decide) ⟨157, rfl⟩ (by decide +kernel)

  private theorem rb414 : (⟨[⟨3,9,true⟩,⟨5,7,false⟩,⟨17,3,false⟩],285,2⟩ : Box).Closed :=
    replayCloses (.cons rb413 (.nil))
      18 294 0x62de6e67e5c97d5d8ec70b74035f256e81c9723d3b40039360bbaf97febc57f1cd70b86034549d6ecf476dded07d8f735e2ed000006b3ba049afefe4245573d02555bff9016d78735c576ade27a44c048cbc718de6d6fdf36790000124a27f31d53d6e172b2392740367d3e37dacff392f400bdd2cbc6ce8ae4918000025a3d024961ff91179fa04a29fff208a67a04a2d7ff202ebb354fd2da59595d1d2f2024658aebb3e6371b653647a395e5e400008b27a04a2ebff208bc7a04a293ff2000120
      (by decide) ⟨142, rfl⟩ (by decide +kernel)

  private theorem rb415 : (⟨[⟨3,9,true⟩,⟨5,7,false⟩,⟨17,3,false⟩],283,2⟩ : Box).Closed :=
    replayCloses (.cons rb414 (.nil))
      17 272 0x42e46d4e86f643e57f566b857a039a4f37d6eb8df1f97670c063bdd9c5fdcdf56eb89c4f14e8090194e7b31bcbc772b8af2b2b63a5da01287dde191c8e0703b3b4000323035353f5a1a58df99d4bcac0240000094193fe61220ecf4094183fe42441d1f40941bfff90165ba3fde1c17cba54c0487bc546729f2c97a00bba9cd7f7a713eaf4bd003861b35e6e316969616681154d0ea705e57254c00000aa66b0dd9dd5bdbcbcb4bc809000001067ba04a0e6ff909001adf40901bbff20
      (by decide) ⟨141, rfl⟩ (by decide +kernel)
end

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
mutual
  private theorem rb416 : (⟨[⟨3,9,true⟩,⟨5,6,false⟩,⟨17,3,false⟩],279,2⟩ : Box).Closed :=
    replayCloses (.cons rb408 (.cons rb415 (.nil)))
      18 141 0x239d375be5e27e3d3b40c3b5e1b6de5f85d1e9795f478b4b34000398ac6f3dce0755cacd70b740000129bc7f984804a6cefcc24024362ff3090094185fcc035afa0486cbff201a1ba0486d6fe4244199f40941bdff200
      (by decide) ⟨139, rfl⟩ (by decide +kernel)

  private theorem rb417 : (⟨[⟨3,9,true⟩,⟨5,6,false⟩,⟨17,3,false⟩,⟨271,1,false⟩],273,1⟩ : Box).Closed :=
    replayCloses (.nil)
      20 255 0x4d96ed7abbacd7b5fd7b24602411b3375efb65f8bf1f1775cd7f5d2f202471535e57dd3677bdd91cac8f946800000090989fe632f3c76697c7e5c0f2b853a00ebe56aaf8687f5e9d30120a9d77bb95ee749dd6dbeda5a3959ae546800000009099efcc243da7e8127abffc84804b8f0fe62cc970391c0fabfd4b644c000c8f6c1f1b9dacb7e677ea588117ab9c9e1faccecd9640000e32be812e3cbfc8063ddd024c707f909146b7d02546effc8
      (by decide) ⟨136, rfl⟩ (by decide +kernel)

  private theorem rb418 : (⟨[⟨3,9,true⟩,⟨5,6,false⟩,⟨17,3,false⟩,⟨269,1,false⟩],271,1⟩ : Box).Closed :=
    replayCloses (.nil)
      17 255 0xe9c762693bed8e6bd59af9be2fd014c3656ccea19efb6f72f2f2f2e5019b5f8e4da7769ff64dd937653c289800ebdb0fa6f683d37b3ee57ecdbb2460001a777d025a71ffc8dde6cb67b63d589e9fa000025a7d7f9848d37dd025a647f9091f60f4097d53fc855f07c7ab552e57d5b2f402a4736365b3d8d29e2ff796946800716e9431db6d672b67680010363bdcd1db4e3391c8e956e5e595f2c800001f42fa04bed3ff2004f4f4090997ff212012e30bf98
      (by decide) ⟨135, rfl⟩ (by decide +kernel)

  private theorem rb419 : (⟨[⟨3,9,true⟩,⟨5,6,false⟩,⟨17,3,false⟩],265,2⟩ : Box).Closed :=
    replayCloses (.cons rb418 (.cons rb417 (.cons rb416 (.nil))))
      20 192 0xa6c78787a76b8df9e585e404800dbf7d025b73ff906debe812daaffc8485bf7d024b73ff90092d73f9805a9ba04968efe4326fae1db68b93b40258e57a6fe3d1a5ff6d8e17680000092dd3f9816c9e8125baffc84843f3d024868ff91c4d386b48c99a0000921d3fe6000490f77e6000
      (by decide) ⟨132, rfl⟩ (by decide +kernel)

  private theorem rb420 : (⟨[⟨3,10,true⟩,⟨5,6,true⟩,⟨17,4,false⟩],423,2⟩ : Box).Closed :=
    replayCloses (.nil)
      28 419 0x19b5dcce53f6c2d0f4898090739e9b9977c737f203ebf766dfcdbbda370ac7bd3731eb3d0403adeef0d97e5eaf975756274bb4000e33d25dd36eeb376c3edbbdafd9a77b16ecb531ab1ed3d04edbebaa6f4cbbd336ea6fd964dc2b6ef69de5bc0eac796fa679a9ee62a86fd679ab732c071e3a6fa666dd96bfcad5bd2a5ddb9af7b46e143c7eac784f4121799fa7359de5d0e274389c4e944c000e2be98e63d0568df2b66eb7753bb29bdaf336f60dd80fb74798f51e894cd79a2e50b064a50f65e596038f1d87a65cc3bd77356fe2a937f32d5bf9a77b6ef5c7d01fe8a1c51c693a4f4ba555c4f4bd01ad246b4cccfcfcd9e400390f4c06f6f6ce76ae5dd43857a0241d07a60215275a56d776e8ae15e809075ee98e1dd31cdba639374c746e980000000000000
      (by decide) ⟨211, rfl⟩ (by decide +kernel)

  private theorem rb421 : (⟨[⟨3,11,false⟩,⟨5,6,true⟩,⟨17,4,false⟩],435,2⟩ : Box).Closed :=
    replayCloses (.nil)
      30 239 0x53b4e7c5d57ba27a5e8001c77d30c7bb25c977df2e5627ab13c57a02401d37d3011b467b8d94f66076768090755f4c779f4c6ddae653b2f15d57cb43d589d2ed01200ec3d31d67d33237b90b4c58e3d1698bcdcc51da7d3313979ac7ba21652b462b059dacb21c51d87d47b88f8686e86aa4a6d58a3a774c776e98036b5fabd5fb5fa6f2b35f37c52300000e4dd31d1ba6000000000000
      (by decide) ⟨217, rfl⟩ (by decide +kernel)

  private theorem rb422 : (⟨[⟨3,10,false⟩,⟨5,6,true⟩,⟨17,4,false⟩],399,2⟩ : Box).Closed :=
    replayCloses (.cons rb420 (.cons rb421 (.nil)))
      18 376 0x8d9f4d07cb7a62dd80fb06ec7bf336f6edec7bd9774d563143d04534349ea7abc5f8e87644c0dda9a2e73ad4b13d5d589e2dd01917334a0bbaf9bff6c89800240470fa6037d39ac6cef570bcb65e809011ede8aa1df95ab781addd7ef6bdf9bd90fc58c6374ccbb82b2ecbd149e0842b26ca14c55b9a9e242f63c34de7e91fec0f4ed009adacff53696abd3860240118dd32ef8ab774b3725b77507c3dbc515cb14743f4cbb96f8bc90ef0ad1bb61f6dded3bc2d9bb6efe66dfc930d8a2686d77667bb9ff796cbd033726074ba3a5b1e9ba0240350d99cfaba1de715d5713c5da02400759e98007589d991f67ab0b43b2f40531393e5fe7d5da70b64e8019b0accec170b55eac4e174c000886e980000
      (by decide) ⟨199, rfl⟩ (by decide +kernel)

  private theorem rb423 : (⟨[⟨3,10,false⟩,⟨5,6,true⟩,⟨17,4,false⟩],385,2⟩ : Box).Closed :=
    replayCloses (.cons rb422 (.nil))
      14 151 0xe9e6d9e2f2bdaf8e16870ba60246d19e99db1ce8585a1c29d0000089df4e77b1bd68ebb7363b6ef99ece8e9cf0def1adcc62a7a08a6f6571be78b89f2d97a041d99accd5715eac4ece1800492f56b1f2cae9fa00000442fa5cd3bda77f354dfcb5fb6ef662a1de98f85bb7e63163d0400
      (by decide) ⟨192, rfl⟩ (by decide +kernel)
end

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
mutual
  private theorem rb424 : (⟨[⟨3,10,false⟩,⟨5,6,true⟩,⟨17,4,false⟩],351,2⟩ : Box).Closed :=
    replayCloses (.cons rb423 (.nil))
      22 345 0x86c4e0ff797b2f2bcb0af404813e63f6c570b274c0480292dd0254aefe43196d69d79f2ea85b326024000244e9fcc131b5a6d2e363b8d81c2ed029fb163befa0006dd67396df62b85d2260056acbb9fef57edd1d9da00000491eb82aaf29f2d59ea5552aac49c3d29ddb77b6ef6ddedbbe2c9bf0596bded3bf8b7b77440e24d9f5136a4f1b29df7e60be5b2a602404dee980b672727169bab96cfd0120098dd2dded3bd35ef61df165df14b7b5507d9b7b31ab124374139b32333d5d5727e80900767a71abbb0bfa9614680909000118bd32ef61bf25877d5ebf69bf6cde4b732a0fb4ef63de980e31f3d04000000
      (by decide) ⟨175, rfl⟩ (by decide +kernel)

  private theorem rb425 : (⟨[⟨3,10,false⟩,⟨5,6,true⟩,⟨17,4,false⟩,⟨331,1,false⟩],333,1⟩ : Box).Closed :=
    replayCloses (.nil)
      16 191 0x12c616267abaae2743a1e2bd036f5fba706539374053db463b4bfddda768090118b9da1fcd5743d226055aa1bf59186df7491800a64b96f8c57fdeaf96cbd026a9e9c1c6b9aaffbba1768090900174e4e8f8fdb79d0ece98153bac97a62c37aaffb2bf35e2ed00020eb747d79fa9616967b8bc80d4353d5f9c2c4f745743c5da0024000000093217f98
      (by decide) ⟨166, rfl⟩ (by decide +kernel)

  private theorem rb426 : (⟨[⟨3,10,false⟩,⟨5,6,true⟩,⟨17,4,false⟩],319,2⟩ : Box).Closed :=
    replayCloses (.cons rb425 (.cons rb424 (.nil)))
      17 194 0x1d70be19ed5715d0f4c981cd4cdadee37769da029935bd305e8fe7c766e80900bbeb3c9fe7d5c1713b2f4039f5c5b6e2f2e93a003193a69b7df1f8e27644c0000126537e639b5baee81ecf2c0ece1809014d9f40953fffe412a6b6e89fdbbe7e6179012399339cf7fb1389e9d3008ef6ebd2fd574bab35f37e6f8b26000000254f1fe60000
      (by decide) ⟨159, rfl⟩ (by decide +kernel)

  private theorem rb427 : (⟨[⟨3,10,false⟩,⟨5,6,true⟩,⟨17,4,false⟩],309,2⟩ : Box).Closed :=
    replayCloses (.cons rb426 (.nil))
      23 227 0x4df2554db7060703b2740022a5e8128b7ffc822d9e8128a0ff9116a9acee4f671b03b27400685c1e4f4dd7dd3740480022cdf4094537fe400945e3f98758cfd7b787bb574c98012351749f8f1bd3789d97a053d06978bfec17a54c0248d9ef4e77562b85aaf56976800070ecd717e777aaae6b85a302284357ee1b1bafd614a8000000000945adf98480a97a0482dfff2000
      (by decide) ⟨154, rfl⟩ (by decide +kernel)

  private theorem rb428 : (⟨[⟨3,10,true⟩,⟨5,7,false⟩,⟨17,4,false⟩],463,2⟩ : Box).Closed :=
    replayCloses (.nil)
      20 227 0x191cda6a96cacf6561790000ec3d7353ce50a18baa82c3698f0501c51cc6de998afebb76f13fafebc5c30000e33eb990fb11f623fcc87cab71f603e95bb76ad5bb1df8569de94986c515bdbc70bdaf7657fb05cf75747ab15ea8d0120000e7dd3062d7983c32bcb9e7b2b2dcc51cbba638774c31c1c2f10dffb2b75d9130120777b6aabb1eed07b21ecfbb32600001d9ba63bb7a60000000
      (by decide) ⟨231, rfl⟩ (by decide +kernel)

  private theorem rb429 : (⟨[⟨3,10,true⟩,⟨5,7,false⟩,⟨17,4,false⟩],421,2⟩ : Box).Closed :=
    replayCloses (.cons rb428 (.nil))
      21 415 0x55ecb8d94ff391c8f5614e8090047b7a0b21fe643ec142b56ec47d9f7e57ffdaefd90ff30ef10a0718c6e82b96d330bc10bc18f33dd065586c78ef3d062cf297999259b29de5018d881c5016974ca5bafebd2f405dedbdeed17b5cd78aeced012039cf4c159f7a4c87db6fda6fdbf70e7ff311fe643fcdcc7acf4126c2f93acecbe77e7ebeac2bd0120ebbe980b940c8e2ca19dfa17f42f2b2031aec578cf4687abcb43857a02409072df4152f72963372d3c7dca0d58f29e82735f4ce72baed978d736adc3b7edbbdbffedf7ebb5da6b3fcc7aafa081a323db3b73ebfb0b4b4b2bcbc809006ebda739ca761decb7e57ec9180eb19d8e97f6bb76f270c0000ee3d3016cd978dfafcbf0b13d5857a0240af358d35e66ab89dd713faf144c0a3e4ff5e703e5d591d93a00240711e980000000
      (by decide) ⟨210, rfl⟩ (by decide +kernel)

  private theorem rb430 : (⟨[⟨3,11,false⟩,⟨5,7,false⟩,⟨17,4,false⟩],463,2⟩ : Box).Closed :=
    replayCloses (.nil)
      18 275 0x3ab75b95e9b6389fd7f5fd78af4048bdf4e5b29feb2f75ed767680909015be69f1723e6f2bfab2bcdf9bd9b7caf401da2f86ddbdae6bb0ef63dd90f67de2bd0002faf6acf55e91f2de72b8bc800000711e985359ce725e3cba1eadd7f5e2ed012120e43d30d66d4e6bf5735e6bfd7abf5e2bd032e53d85e6dd6f391c8e478bb40480480e7dd31cbba638774c73d76749ff6f385aafebfaf17e80d4e1ed6c1b8aeeb89d97a0240241c5ba6addbb2df851fa0becbbb7eed5bf054d7bc6b558a3bb7a60000000
      (by decide) ⟨231, rfl⟩ (by decide +kernel)

  private theorem rb431 : (⟨[⟨3,10,false⟩,⟨5,7,false⟩,⟨17,4,false⟩],403,2⟩ : Box).Closed :=
    replayCloses (.cons rb429 (.cons rb430 (.nil)))
      23 351 0x37a7abda74b0baba5e809011a3ea6d98d5db9eef2dcd97b073fdb77b11f1b1bccd97a5db3ee36317dd0426cc8e339eccc5713b2f40adb51ded7dfdfd85a5d1cad2f2024024044b75cddfe1fdc3dff972aa3eddbe50b16314dd04dbd381f8f542eae9d300484808a6e98e0bd31d0fd31ef2fc6b9aed76d17d1e8e17ddaefa6dec77eac51cf7d45b774a2dbbb11f65bf4aff15f7f15a0ff3291fd040e289b97272d9afdb55e97a0241cb7d31966d543dd85d1d2d2cae28d0121200eebe989ba65b65c1705f57b5d97a0530b9cec7cb15ed7a7680901dc7a639b67e5eabd5dae2765e8090751ebb960b2cf372513438a8689e6038a0000000000
      (by decide) ⟨201, rfl⟩ (by decide +kernel)
end

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
mutual
  private theorem rb432 : (⟨[⟨3,10,false⟩,⟨5,7,false⟩,⟨17,4,false⟩],375,2⟩ : Box).Closed :=
    replayCloses (.cons rb431 (.nil))
      17 328 0x139ba1a346b9b98d1b1bc6aedcdcd88f87afd9cae86d7b8571e3624f6f41267b345fe7e5ea8aeebb22602401c74d9cdf2f537e69b4b0b0b4baa5400a553aee3dbfbf52cf67bcb3402323e8354f2b6d677efd0b2b94001200008b3f437779635b778d1b1bdcc227d29f833335f98d8dee71becd80d36d8c49fa099b53839aec76385e5d585930122cce7e3aaed1bfaf574bd01232725837e5eebeaeafd7648c0012008fdf49311f643fcc87d98fb5eed42ddbb01fcc87d82c7bb01fa62c1438c4efa0914beb9eeabac9f5eea596b05ab18c5f41177cebe8e7bc5c57ab644c0f5858df2ba6fa3b76f68dd91301204808d1e9800000
      (by decide) ⟨187, rfl⟩ (by decide +kernel)

  private theorem rb433 : (⟨[⟨3,10,false⟩,⟨5,7,false⟩,⟨17,4,false⟩],361,2⟩ : Box).Closed :=
    replayCloses (.cons rb432 (.nil))
      13 207 0x71b95f966bfae1be9530098a95a77ddafa91f0e7b3da59a0240004f1e997256add997341fee683e9321fe4d37f4a65de2c7bc1b2dfb2dfb11fe663892c7a65b775e7c2d7bb01ed07f965bf61ddab21fe683fd1e624d1ea23af36b396f67b9f5705d570af40358d839af68dc2fd7f5d87785c30120120903e9e970df6b86f13a1c2fd01212000268fa3a0683d6ea51497349aac49bdd0400
      (by decide) ⟨180, rfl⟩ (by decide +kernel)

  private theorem rb434 : (⟨[⟨3,10,false⟩,⟨5,7,false⟩,⟨17,4,false⟩],349,2⟩ : Box).Closed :=
    replayCloses (.cons rb433 (.nil))
      17 182 0x1196f681f97dae176bb2260245353d9a59595aaed1bb2a602400053a7d0254ddff226759e2b9daf6ba1c37b2260240523ba04a97dfc82777874705f8e1bd0ecbd012394329e0fe757974c9809019b2bfed90bb5ed765e80a6c8ba1d1ff6c7f5d97a0240906194fe6fb6adf6bd2f4048480000261fa6000
      (by decide) ⟨174, rfl⟩ (by decide +kernel)

  private theorem rb435 : (⟨[⟨3,10,false⟩,⟨5,7,false⟩,⟨17,4,false⟩,⟨337,1,false⟩],339,1⟩ : Box).Closed :=
    replayCloses (.nil)
      18 248 0xe9e2b3d6f9785baf6bb2f40db47f599fee24602424077af366be5e27b5c4ecbd020c97adb2fed82f56c3bd9130120a6a7c3a355dd767de9da0306f57e1bd29f37b09f65bf0a7400bdd9dafd7a1d9b785b56f670c0db1697d36d89f5755f5757abd2bd0000e43b1aafd5e8ed5be9da001f4edd7138ded1bb5fb3860000000016d799d5d5eab6ef2b66dc2dd008c975c6af5e5ebdf34b0bcb9400cbb43673fd335a167b05e2f20240000000323ba04997dfc8
      (by decide) ⟨169, rfl⟩ (by decide +kernel)

  private theorem rb436 : (⟨[⟨3,10,false⟩,⟨5,7,false⟩,⟨17,4,false⟩],319,2⟩ : Box).Closed :=
    replayCloses (.cons rb435 (.cons rb434 (.nil)))
      18 267 0x14e74da5b5c3786fa5e800614963e3e333930bfa1616165590369994f762e8e0bb11f35c2bd00efd75e4f74a70391d93a000167cf51ab52cafc4ecfd012120000499dbfcc79fdddb4e470393460709bce16e7c393b404811582efbbb1b268c0480001267aff302ce2be36dbcb0df4bd00291eafd9df6f536c47d96fd9f78bb409bd3bd1a76ab46feb89d877c5da00555dd4fa74bb66ed9bd3b404800018d770b99a6f2cd789c4ec3be2ed01212000004a963f98000
      (by decide) ⟨159, rfl⟩ (by decide +kernel)

  private theorem rb437 : (⟨[⟨3,10,false⟩,⟨5,7,false⟩,⟨17,4,false⟩],315,2⟩ : Box).Closed :=
    replayCloses (.cons rb436 (.nil))
      12 66 0x196cec8afdb75ead9d30120e3836537752fb6ebb2f404848008b87d025156ff90900945adf980
      (by decide) ⟨157, rfl⟩ (by decide +kernel)

  private theorem rb438 : (⟨[⟨3,10,false⟩,⟨5,7,false⟩,⟨17,4,false⟩],313,2⟩ : Box).Closed :=
    replayCloses (.cons rb437 (.nil))
      20 226 0x93a9b45c4d6795ec763f1e2ed000dd7eb29d92d9dc3e1d2cf747cbc809036553093cb9ddf3fa161696969697cb2024121b0db1f3d3a5ceca7c3e595b1caeac40000630a993a71b33fb56565797900000004a299fcc5503ba8707c648d011efb7271b63c6e9da002eeaaef27f5dee3749d01204d3e6fa74bf23fafe3f1cd78af4035c9a5fb0dfd9eae47683edbbb6ef15e809000000001166fa04a29bff20
      (by decide) ⟨156, rfl⟩ (by decide +kernel)

  private theorem rb439 : (⟨[⟨3,10,false⟩,⟨5,7,false⟩,⟨17,4,false⟩,⟨307,1,false⟩],309,1⟩ : Box).Closed :=
    replayCloses (.nil)
      16 184 0x26bd73fdd4f8bfaf4389c2bd0122d7d6d0f976ade27cdf4e98086e695a7cbcbcb0381c2ed006aef9bdf4f16cbc6f8e478bb400a4d6ea79a97a9ecac2cf697900012000124b17f3002495cfe639f5ecfe67394f73d3b40486a1bdbd7a77e697f5f7969668090000000925dbfcc31ad359efb6fb23d2a60000092593f98
      (by decide) ⟨154, rfl⟩ (by decide +kernel)
end

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
mutual
  private theorem rb440 : (⟨[⟨3,10,false⟩,⟨5,7,false⟩,⟨17,4,false⟩,⟨293,1,false⟩],295,1⟩ : Box).Closed :=
    replayCloses (.nil)
      23 307 0x1d526b46705e360723852301211cf539acb62bcdb5e1bcd7639af976815391f4f1bc3782f8715c4e57f14e8007b49aa9b4303fad2ef6577b2b2babc80481f6fd706e6959735f37c5da0024004cf5b19d37c5b29fabcdecdb85930007586c379b25f2799e37382ffbaba3959a06d0e5e5a6265b4a956c5c5c5c5e5f2c804d4e4aafcda5da5f89c2cf627ca340004800000049aa9fcc24024d7aff3007cbd35f1eeb56f13b3f404853b32df58b1d8af2b2b63c5da071eaf05c37f995d5d2a60001cae693b2f2773a6c573d8af5796680900000035e3d024d49ff909009351df98
      (by decide) ⟨147, rfl⟩ (by decide +kernel)

  private theorem rb441 : (⟨[⟨3,10,false⟩,⟨5,7,false⟩,⟨17,3,false⟩],285,2⟩ : Box).Closed :=
    replayCloses (.cons rb440 (.cons rb439 (.cons rb438 (.nil))))
      25 186 0x1cb307d3c6f0f8723b2460054ee85fde591e9da0031caf74a86fb5d0f4fd010e87672e57eaec7a6e815bd3e9da793dd85d5d595c5e40003ba7dae6f385bceddbd9930120cbeb134db5feae0bd5b2f401b55cd1769f2e57ab648c01201226765ecff70765f9bdd766e800090000025edd02496f7f2120128bcff9800120
      (by decide) ⟨142, rfl⟩ (by decide +kernel)

  private theorem rb442 : (⟨[⟨3,10,false⟩,⟨5,7,false⟩,⟨17,3,false⟩,⟨283,2,false⟩],2459,1⟩ : Box).Closed :=
    replayCloses (.nil)
      22 270 0x5eecd7fb1dd2ec7e3b3b402dc9deecc8c0fcb81c8e17681071b53736bfba16c37ecfd02b6166a1d1b6d3697f4f65697900022b1e9e4e6bb58cffb0b2b2bcbc8090056eb7354c6d1a19ce967b0b3dd5d5d5e4003a62b9e9cd75bef2f2e2f20241954f3793eceb4a7e5f973d95d5e59a0242eeefed5eecfbcd7ac3ea776a7e174c00000001ba7a048697ff2120121bb7f98480486b5fe600c0c2c7f3b3cbd5a5f1cac57cbc80909000090de3f9800486a1fcc2441d9e8128307fc8
      (by decide) ⟨1229, rfl⟩ (by decide +kernel)

  private theorem rb443 : (⟨[⟨3,11,false⟩,⟨5,7,false⟩,⟨17,4,false⟩,⟨281,2,false⟩],2795,1⟩ : Box).Closed :=
    replayCloses (.nil)
      23 336 0x5383adacbf65f9bd88fb2f406a9d9fdcce0bbec8ff385a3010cb67776f3b1e37c7e5c2ed03999f90f57958589c4e14e8006aa9ae0ff796dbbd85e400009358cfc64763d2eabe595b1d2ed0111e4fe6944e57acec7e3c5da05ee8d8f3756e96d2c8e967b3de5e4001ec984a745fa7b9f2c0e1768153f26b33a399fcf2d2f1cad28d00000aaabe374bdaf1d8eed7f5c2ed00d675fa5f86f69def3e6fabcdf1768091b72b1d353d6da78b97872b2b63b1d8e57c9500000edadedc35d8ce0bf1cf65747a3951a02424061c6f39d37cd83a2f07cbe3b0dfb56fca3408b06c77b2ac7e5c4f97ebfd7d1f2f2024000000000248747f98480490f77e61201243cdf98
      (by decide) ⟨1397, rfl⟩ (by decide +kernel)

  private theorem rb444 : (⟨[⟨3,10,false⟩,⟨5,7,false⟩,⟨17,3,false⟩],281,2⟩ : Box).Closed :=
    replayCloses (.cons rb441 (.cons rb442 (.cons rb443 (.nil))))
      21 266 0x1467b3df4e5386f55d8eced0000129bcff98480129ae7f309135774094d03fc8481ac7a0486a3ff2393326679dd2f9796ced00eb9cee57c1cd7a5cad93a07336febf23e2f2bdefaeced0001a14be39dc191e9da03585c8c97d5fd76735eced000000121adbf300d4dd0243477f2120128367fcc59d5cd55c97cb25e8087e7b39986f0fcbd3b400ca8bc6ed6c76cdff656cdd01200083f3d025068ff909002506f7f9848012833df980
      (by decide) ⟨140, rfl⟩ (by decide +kernel)

  private theorem rb445 : (⟨[⟨3,10,false⟩,⟨5,7,false⟩,⟨17,3,false⟩,⟨277,1,true⟩],2935,1⟩ : Box).Closed :=
    replayCloses (.nil)
      24 247 0xa7c86e7060763d3b40dbb617cdc6f773fcece180d42d939af0775eeb0ef0bb40480da0785e372bd2c2dab7b3b400038d74d9baf4b9ae2bf2fc2ed0157e9e6f0d8ecfbdd77dfae14e8194346ebeb54b69b4dfd4b4b3400000484835e4f1b6c7f25da8f89da9fd9f70bb400000000c3ede812c36dfc84804b6d3fe61236fdf4096dcffe4734637d6d3f2f55e9c3000012da27f3090025b58fe61216c9e8125baffc8
      (by decide) ⟨1467, rfl⟩ (by decide +kernel)

  private theorem rb446 : (⟨[⟨3,10,false⟩,⟨5,7,false⟩,⟨17,4,false⟩,⟨277,2,false⟩],3151,1⟩ : Box).Closed :=
    replayCloses (.nil)
      21 387 0x54fca4e5b19fcfd7aafab853a0075555e07f3daf0df179bfd78bb4048ca1b23addaf3ab3f5fcaf61bf68dcafd735da376a3404867903db0734ab5cdbad2ece2db6db6b94000480003abbaa58f8d607146a6e8e2e56592c50a4fd624964389d1dd263c958fea4fe67e5561f19de89234e7d8af79fb5945f038f1d5b734b75ff7ebaaecbd009f319df697664723b3740530db1aeda79dbece859ee2cd000631ac7671bb5adfa9616681142e8f27ebf3237dc6fe78bb40caa79b0d96fa7438ce7b3dd1cf794680900aa72dd2ff3f1f5791c8e16e8090000091d6df9848048e86fcc2461b9e812c36ffe421cb61bafb25dab795b1f8f14e809001230ae6939affdeaf8b89cada37e39af5790120000c35be812c377fe42418617d025874ffc8
      (by decide) ⟨1575, rfl⟩ (by decide +kernel)

  private theorem rb447 : (⟨[⟨3,10,false⟩,⟨5,6,false⟩,⟨17,3,false⟩,⟨277,1,false⟩],279,1⟩ : Box).Closed :=
    replayCloses (.cons rb445 (.cons rb446 (.nil)))
      19 300 0x246debe812daaffc827a4d0fee581e93a07aef6cb8aef3bce8713b32604429b19c5768dd877f1d97a000075af55e1bd37fef8ffbfa15e80000096196fcc246d17e812dafffc8393393cdbad8f1796176803ac8f2d1ddea9b64e9ee28d01200036adf4096d77fe4240092d73f9865db4f6bfdcd8ba7681ca1e4e1339dc6e9da0006c0e2ca1e1fed274008ef8e371b49ee72b67680001b4b74096d5dfc80125a2ff983a47474b7dace4918051b1b9c1e0f164e180000092ddbfcc240024874ff98
      (by decide) ⟨139, rfl⟩ (by decide +kernel)
end

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
mutual
  private theorem rb448 : (⟨[⟨3,12,false⟩,⟨5,8,false⟩,⟨17,5,false⟩,⟨271,2,false⟩],4569,1⟩ : Box).Closed :=
    replayCloses (.nil)
      15 270 0x154b68775e0bf9e1f2c57f1e2ed0397343bad3acf872bd5c978bb400dd9b9caf93bae0f8bb1c4e56c735caf2073871b27d766eb0395c5b6ef656575668009014cd13cbfb17169796146801bb3f9daf3cc5e5df64755f8f17966bf1f9e400000e49d27236dfacd703f1f8f1768090db4e765fa7adfae97d9ed763fae6bb46f54680000007df3d328b96af044c275895b4b721ba42749cac8d1a54ec51c8be555d9b76bddb4fe6f674c0236cbf4e7b15eb3c59ae57965656546800719e9d4e0bfce0725fd70bb4048003e99e812fb5ffc8
      (by decide) ⟨2284, rfl⟩ (by decide +kernel)

  private theorem rb449 : (⟨[⟨3,10,false⟩,⟨5,6,true⟩,⟨17,3,false⟩,⟨271,2,false⟩],4041,1⟩ : Box).Closed :=
    replayCloses (.nil)
      18 234 0x2286d2f181db64759d9230188dd736357cfaa585640483a0f2e6715d37fb35d97a02ed4d8ecd93a87d9d6fee2d8e5656c76bc8000a736a74bf8daf876389d2e2918090bba9c8c2cd3a3b0b63ada3e5e5e404848000012130bf98e9c3ebf9dee58595b2f40198f375bd399e6729dead63e5e5e40484800000484f4fe6013ebe8121357fe4136647c62bdd74ba5e805527d7170f6b03d37400001213cdf9848
      (by decide) ⟨2020, rfl⟩ (by decide +kernel)

  private theorem rb450 : (⟨[⟨3,10,false⟩,⟨5,6,false⟩,⟨17,3,false⟩,⟨271,1,false⟩],273,1⟩ : Box).Closed :=
    replayCloses (.cons rb449 (.cons rb448 (.nil)))
      27 215 0x12e1bdbe65bb5b1d0f5615e8033d3af6376bc391f0e571773e5e4048a9c8f6fce3385baf63e6f2b35d2f20000007d7be980fab7d025f5dff9091f7cfa04bee3ff2123ecee812fbfbf905b3db2fcbe2eeb95e5f1fd78bb400366b3df9ceed7e595959af176800009498bfe6004a4c2fe60012932bfcc24024f69ff307195f40971e5fe4245da7e812babffc8
      (by decide) ⟨136, rfl⟩ (by decide +kernel)

  private theorem rb451 : (⟨[⟨3,11,false⟩,⟨5,8,false⟩,⟨17,4,false⟩,⟨269,2,false⟩],5137,1⟩ : Box).Closed :=
    replayCloses (.nil)
      18 350 0x32746d1b9fecb71707c3fcef391fe7abc80ced68daeee6f2d278bcbcb7dbeeacd012032a631d95bab6e7b36d95fce47f9fe7e79012039bcdc559ceb1df6b3ed57d84fb09f4bb40484804803cc7740979befe473ccbd137b353767c6db8b6db6db6d4a8090d15acc361b9373eda6c2d2cf654a800374f7b19c281f67fab7e89d8ec7e39aed79000003cd37409798efe400939f3fe60127317fcc0b3c6ca7c3aaf574fd022bd938d9ed0ef7177b0bc8000e64fd024e73ffc863aa076bea46eb1df9c5c5e403a57d2eb5576389d0f5617e8059a19ee976de6fcb13b2f4012b99ad681d1755f976768090000000939d9fcc24024e697f98
      (by decide) ⟨2568, rfl⟩ (by decide +kernel)

  private theorem rb452 : (⟨[⟨3,10,false⟩,⟨5,6,true⟩,⟨17,3,false⟩,⟨269,2,false⟩],4547,1⟩ : Box).Closed :=
    replayCloses (.nil)
      22 247 0x54eebeea5ecf57eba5b22600bb3a7bf303b4f9787cb0bb4002a676ec1cd713a5b2a6039aee2c585fec1b16ed1bb1e289809010a9c1ead37978be59ecafd2ed0000cac57286ad26686979656c72a9400000000cfcfa048cf1ff9027eb2ab385b2f264c00033d3e81233bbfe42419f6e81233bdfc8a9cf6c7b389b6c8f9656170c023254d03a1fd6b56e5c5e4003a7b3cb79f8ffbfa56cc9806992f471bd8e6b95fd2f40000d323d025a60ffc848
      (by decide) ⟨2273, rfl⟩ (by decide +kernel)

  private theorem rb453 : (⟨[⟨3,10,false⟩,⟨5,6,false⟩,⟨17,3,false⟩,⟨269,1,false⟩],271,1⟩ : Box).Closed :=
    replayCloses (.cons rb452 (.cons rb451 (.nil)))
      19 158 0x4873edd024e77bf915527dd89f57b5fc72b639af14e805533cdc48e9bcad67f5f8f170c04800012b327fcc73b54e972b8b0391d93a01c33cced3aaf564a9800002567f7f9848012b3d3fcc2469bee812d323fc83e85f4097da7fe42409e1e8121373fc8
      (by decide) ⟨135, rfl⟩ (by decide +kernel)

  private theorem rb454 : (⟨[⟨3,13,false⟩,⟨5,8,false⟩,⟨17,4,true⟩,⟨263,2,false⟩],9411,1⟩ : Box).Closed :=
    replayCloses (.nil)
      17 321 0x1a4e4e8cad3872bbd95d9c5decacd002c1e9c9d39b2bc389ce8ae979036b52e872b45fd723b3b4048000e7eade4fc6865be4feb46ec763dda372a34000010efba42ff4a4a91fd33fd27feaefc90a0ffcb3fe81ff2f0798a1210fbba0490f07f91cedec39bf4f6075b87bda5e406f5c991e6c17abb9c0e478a4606dcd8992f87f70e6b8af962765bfca7400003cbd7ec50e2db7177b6da51a0000021eb740921f77f20370b94ffb55f37bcf4bd01959c57d2e53fcedbbf1c8f2bc5d30002d233c1ed7b1f37d326025e75bee76d3e1eac8f57168c001a346799e670b73fcf575717680000d393f40934f3ffc80049a733f98
      (by decide) ⟨4705, rfl⟩ (by decide +kernel)

  private theorem rb455 : (⟨[⟨3,12,false⟩,⟨5,8,false⟩,⟨17,5,false⟩,⟨263,2,false⟩],9411,1⟩ : Box).Closed :=
    replayCloses (.nil)
      16 314 0x24879bfcc29d2e693c9eec763bf38b7da59a02445130bf66f4e9773e1d8ff3e1cafe7abc81c07482e0ba2e8b94ed9bb2ef9bd2ed0120480010e57d02487cbfc83a47cbe17434b95d8e56176801b49dcf0e8f7b0aabeae57c735cd72a740a9f9a899996c9759c0e078a46001b48caf5986f369677dbec8e5716c76395f50a024000002487d3fcc1cfcecefb9babf1d8fc70bb400001243d1fe62aa19edd799ed7ab92f9bf8f168c0486031a46a7f6cc6779fe76ddec8e5790000043d1f40921dfffc81b86d48e4e9795e2cd7e3c53a0659bdc87075736f42fccf7f52ea8500000049a74bf98
      (by decide) ⟨4705, rfl⟩ (by decide +kernel)
end

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
mutual
  private theorem rb456 : (⟨[⟨3,10,false⟩,⟨5,7,false⟩,⟨17,3,false⟩,⟨263,2,false⟩],7417,1⟩ : Box).Closed :=
    replayCloses (.cons rb455 (.cons rb454 (.nil)))
      23 257 0x399d1745c67d9e0fc7ede5daecc7c4e57901200001a733d024d3d7ff202d27bb9bfb972bfaecbd00001a70be81269e9ff909153cdf40954e6ffc8482b13e8122bdbfe4025070bf983db1dee0c4f2c9763f1cd735d2dd014dd7ebf6765eafc9da003d65fabd9b7c2febe2fd7e385d303afdd70ba5f95f2fdbc3b23f95fc523000020e27a04a0e37f90772e4f6b43b4fbb8bbddee2f200002507a3f980839ee81283cdff212004bf74ff9848048f6b7f98
      (by decide) ⟨3708, rfl⟩ (by decide +kernel)

  private theorem rb457 : (⟨[⟨3,10,false⟩,⟨5,6,false⟩,⟨17,3,false⟩,⟨263,1,false⟩],265,1⟩ : Box).Closed :=
    replayCloses (.cons rb456 (.nil))
      22 266 0xcc51b078727e6ebfba76767959018fb74c5fed17f9f8ecbf1e2ed012003dac77ae1c1959a97eb8b8b2ac800064f57d025938bff21cf0faf583f363d38be38ac81dc99bee94a4703b6c2ed000327e3d0259393ff20c9e8fa04b277fff210c2c22776ce374ed003746d7e97d7f2be0ed7b3f400004b27edf980049f717f3090fb3dd024fb9bfe45ecafa04af797f9073a6f1df2edbabfabfb3cb0a260005eef74095ed0ff21201db3f4090ef7ff90905b83d0245b53fc8
      (by decide) ⟨132, rfl⟩ (by decide +kernel)

  private theorem rb458 : (⟨[⟨3,15,false⟩,⟨5,10,false⟩,⟨17,6,false⟩,⟨257,2,true⟩],64923,1⟩ : Box).Closed :=
    replayCloses (.nil)
      19 443 0x35db1f1c1f8c8ecf379b8b4bcb2bd4024d66b1a1b9b071dece97969656566800339436869d793f54bcdc5c5becaf0f87e79000f9e335a573e9d2ddcd95becacaeaf203ac953b3b5fcdce473df9eae2bfd2b3dd1cd7ebc80900a75ba9e37364c6faf8dfebf171395fd5d5d5f3c8000014be2f4c3186ea7d39bc9191bafe81df6fbc3d59a0194d7943bb739bb3f9c5a59595b1f0ed79002487681f4c97d5f2bdf747ab15dd735dd775faf20000002414bdcfe6120120a5e77f98ca6b7bca1f6e3d6edecadf7872bc3b5e400926cd671dd373b3c7c38af57562bb51a0240002414be6ff30009052f4bfcc048d39c0d1723c335f37b1e2ed0000a5f87d075fc3f7f943d7c367e69bfa51dc227e9259e0dbf92113e56ae50e5f0a3fed6438852f3dd0427284296f0ef719dd9bed2df657900487d4e7e5e2bdbf7e9eaff37f1d2ed00000120a5ebbf30009052f0df984804837ffe7f98
      (by decide) ⟨32461, rfl⟩ (by decide +kernel)

  private theorem rb459 : (⟨[⟨3,17,false⟩,⟨5,11,false⟩,⟨17,6,false⟩,⟨257,3,false⟩],65473,1⟩ : Box).Closed :=
    replayCloses (.nil)
      20 387 0x8364f6e8f07a3439a97f3f2f2bf9f57d5f9e4036a4f938ee0d360bf2fc703aafc7e3fcf579012041bca17269b538d89eeeafb9c8e56476bc8004981baf83bced07f57ddd5fabdaafb61f6d3e57680ca660cb673dad8f7bc3f2f6deafc7abc8006064cd536cdcafbbadfd69fccaeaeac4e87abababab432a02ef691b5efebf244df687cb68dda3775cd7abc800107e44c1d8d6779fd7abdaf6797572bb51a02ed761b6bdf14afc57e383b6c579aed5bb56f5790000006a07d3defa79b270bacf2becfe6dbd5f5705d0f56ab89eae6b00000009045fc3fe6145a3c9d6c1795ef3e1c9755cac8fc7e3dafb5fd7901b379bebdd6d6759e77b3bd29ff78bc5f1f8ec763c19501201cf286c7667539af65fc76391c8fc7b5f56680eb0313272713e63939ce95a760dff796f389fd7f5c4ec3be6e500000004822ff4fe61201208bf53f98
      (by decide) ⟨32736, rfl⟩ (by decide +kernel)

  private theorem rb460 : (⟨[⟨3,15,false⟩,⟨5,10,false⟩,⟨17,5,false⟩,⟨257,2,false⟩],64923,1⟩ : Box).Closed :=
    replayCloses (.cons rb458 (.cons rb459 (.nil)))
      23 372 0xf684ed5ddd2beba577a7677b6deeef77b030024955f93a6f23acfabaaecbbb1dab7b1eec7bd5e4073cb572e58df53dec37d9e581eaeae5760df9e40480001208bfebfcc24009045ff1fcc73b7293b5cd761775ab5bbc77b6db6f964002bb5325779b2dbecd7f3aafe756175627ab13c185000075c2f1beb7a61b65e7b4b4bf3bdb0bab4389fd769dc0f9014d77cd9def37f3c1d2785e97a5def1e8e6bf3940012000004822ff77e61a86ce9d57d992e3bcbf35c1775c176edfebb0ef68dfd7032a0000009045ff6fcc27bb7281c66c69b9db77bf9fe7abd40036d54f6f18595d62fb3caf75cd768dfd76bc803589f9213de0c2c7d3ef75ede7855301200000120bfff3fe6120120bff91fcc2402414bc77e6120
      (by decide) ⟨32461, rfl⟩ (by decide +kernel)

  private theorem rb461 : (⟨[⟨3,15,false⟩,⟨5,10,false⟩,⟨17,5,false⟩,⟨257,2,false⟩],64727,1⟩ : Box).Closed :=
    replayCloses (.cons rb460 (.nil))
      2 10 0x120f3f3df98
      (by decide) ⟨32363, rfl⟩ (by decide +kernel)

  private theorem rb462 : (⟨[⟨3,15,false⟩,⟨5,8,true⟩,⟨17,5,false⟩,⟨257,2,false⟩],62733,1⟩ : Box).Closed :=
    replayCloses (.nil)
      21 472 0x836a7755cd2e9dacf77be32b2babc81b577d9395eb0b9ed170bfbf44e5656d79018f2c53592f3b333e9c1ddb323951a00240007cfa3e831ffcdbf692a91bed54f436ad7c4f9b7853ffaf7864fd30c7f9d0a7fb2cb2c8710f9f87d530fc0da86ef847fc34ffa0fb5d3c327871ff5df872ff3b490b3f60b3f03887cfbdd4403c333885e9d31716db2bbd9595e4039e769d0d6c3b9a47bbcdad6ddedb7c85001a86c8e174f4d733fb545755c4e16eb89fa95012068d439ae7c6b697a66725e67e5f0f56d4a80000000241f3cf7e608af436e718d91c1ddfab5b717177be59017616a2bed7caf8d9edafd2fccadd761de276bc80031badd606eba64d9765dd79aec768df571389f94a0000007cf4dd0241f3c77f212028fcafa04828ff2ff212030fe0f409061fa9fe4061f99f409061fbdff2398afb2d8ec2d17f5f8e14e80060607354f686e8e8f6c6db6b536f5367beac800009061f9efcc2407bfeefa0483dff1ffc8480120b9e17f98
      (by decide) ⟨31366, rfl⟩ (by decide +kernel)

  private theorem rb463 : (⟨[⟨3,13,true⟩,⟨5,9,false⟩,⟨17,5,false⟩,⟨257,2,false⟩],63813,1⟩ : Box).Closed :=
    replayCloses (.nil)
      17 219 0x9077ff9ff309009077fe1ff30b685cd4ea96eb6d52d2db696dbbddeef7d7281954d777b63e99dd69bbb1617b395b1caf96404800120efffefcc240241a7e9bf31b728d66a958bf78c8dd62777ceaa00cb93e5f86e0e2bf97abf79c4febbaf562be6f6bc809000009069fa6fcc2402415ff67fcc0503a6b76b9df57d85fd2b3d959564048000482bff67f9848012093f9df9848
      (by decide) ⟨31906, rfl⟩ (by decide +kernel)
end

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
mutual
  private theorem rb464 : (⟨[⟨3,13,false⟩,⟨5,8,false⟩,⟨17,5,false⟩,⟨257,2,false⟩],62189,1⟩ : Box).Closed :=
    replayCloses (.cons rb462 (.cons rb463 (.cons rb461 (.nil))))
      18 409 0x48297a5fe6120120a5e47f30a2b9f6d8d8d379bcbbdd9b6ef77b6db564036f274d786496e6e9baeb71766dbbdb564000004837ff17f30901e7fd7d0241e7eaffc80f3febe8120f3f57fe424079ff1e8120f3f27fe406ded4f5b6fde7bc38b6d3eda7db0fa5ba04d14eb793dd8b7d82e562b95d1caf20065238ad58c769381d9ebd7ec1fe95fef964000004827ffcff984800482cfd4fe612034fe37409069f8dff2004838fe2ff30c1b39d16cb6ca1e77db4b5bdbe3b1f8fce50068d631b54ce969d2caca7e9fa7e9c8ed72809000187edba04830fcf7f200482e7c5fcc024173f8ff30005bfeb740905bff77f2020fecf409041f83fe40133c4f40904cf1bfc82d86d2fe2c37e3b55cb7f185da0000904cf8df9800
      (by decide) ⟨31094, rfl⟩ (by decide +kernel)

  private theorem rb465 : (⟨[⟨3,13,false⟩,⟨5,8,false⟩,⟨17,5,false⟩,⟨257,2,false⟩],60613,1⟩ : Box).Closed :=
    replayCloses (.cons rb464 (.nil))
      2 14 0x74f87e8120e9fdffc8
      (by decide) ⟨30306, rfl⟩ (by decide +kernel)

  private theorem rb466 : (⟨[⟨3,15,false⟩,⟨5,10,false⟩,⟨17,4,true⟩,⟨257,3,false⟩],62245,1⟩ : Box).Closed :=
    replayCloses (.nil)
      18 317 0x1d2d3bef4c67f5fcbf2fabfd74b74026cd03830303bd2373f373ab76af6f2caf2d0e35009090117aa9a4ef70cd763c5f2e6bdafbd95e40439aa733dafed92febcae5be2dd0120cad769ce73aee2a6f623e7bc3b66f9bcadd7e3f234048000036789f40906cfdbfe4240241b3f77e6173dbaa2bb5dda592f7b6dfcf97901207ae73b7db1c77a653dec974bc80000241b3fb7f301b5dc2e2bc57b5fe586f65bff5e2d181960ebb3acbee78bd5c77a7071bcb34001200012083f5bfcc06c2bb39e37baf3bcbbcf561796278babc809bcb0baecac2eb69ee715fcba5e4000012083f8bfcc24041fe6e812083f9dfc8
      (by decide) ⟨31122, rfl⟩ (by decide +kernel)

  private theorem rb467 : (⟨[⟨3,14,false⟩,⟨5,9,false⟩,⟨17,4,true⟩,⟨257,2,false⟩],61225,1⟩ : Box).Closed :=
    replayCloses (.cons rb466 (.nil))
      19 344 0x1c6bc178395bed5715f5616e812697979595fb6e37b46fab9af17680004cfe3d024133c9ff9004cfb3e812099ffffe40575e4f36a70d89f4e5b95e9bfd9af35ea8d00d69b4b6a17d794e6b9ae176800000133df740904cf23fc8487bdc2ecbd8fa6c7cb0b7400035fe4fd0241aff9ffe4006bfdefa04835fe9ffc848035ffc7d0241aff63fc80482678efcc00906bfe4fe6137c848aed3eec57e5f91e2ed00639349f27cdacf166bcaf2bc5c300e8abb2b5b75d5745c57fcf170c032b210b55ed1bfaf64dd9da0029cdadace1b2a5b25c172da6f173d95e40000000e9e67d0241d3deff90004bfc2f40904bfc7ff90901cffc3d0241cff73fc8
      (by decide) ⟨30612, rfl⟩ (by decide +kernel)

  private theorem rb468 : (⟨[⟨3,13,false⟩,⟨5,8,false⟩,⟨17,4,true⟩,⟨257,2,false⟩],58271,1⟩ : Box).Closed :=
    replayCloses (.cons rb467 (.nil))
      17 284 0x83675270bc9f67c3f2f6787d5f2f202401cffe7e8120e7f9fff2004839ff47f3098d0f538ce47bb2b91c2ed000b475ba67773f2eabaaf2bed74bc809000017be7ba0482f7e6ff90014ff3be8120a7f87ff21200c7ffee8120c7fc9fe4349a4ea7756cd03e9b6e2cd0000483efedbf30056fa5e8120adfbffe42402415be17f980bbf91e8120bbf83ff200482effc7f9800a9f0fd024153fbff900905dff77e600120dbf85fe6026fefba04826fe47f900075ffafa0483afeaffc8
      (by decide) ⟨29135, rfl⟩ (by decide +kernel)

  private theorem rb469 : (⟨[⟨3,12,false⟩,⟨5,8,false⟩,⟨17,4,true⟩,⟨257,2,false⟩],58271,1⟩ : Box).Closed :=
    replayCloses (.cons rb468 (.nil))
      13 116 0x1b086c6cece73dd5fcff3a5e400036ffa7a04836fe5ffc80120dbffefcc066ff6e8120cdfbdfc8004826ff37f98480483affa7f980e5f33d0241cbf5ffc819ba72b1a7b7d42cd0000
      (by decide) ⟨29135, rfl⟩ (by decide +kernel)

  private theorem rb470 : (⟨[⟨3,10,true⟩,⟨5,8,false⟩,⟨17,5,false⟩,⟨257,2,false⟩],45087,1⟩ : Box).Closed :=
    replayCloses (.nil)
      18 341 0x6d0aeef66be3d3ba871b074bfde1eacaf9e01200044ffafa04913f57fe43503278e1765f57f2ffb69f17b5c57f5e2baafcb00900002489ffefcc2429ff13d024a7fc6ff23b681e5da471b3885ddf5fae2eaa0000daa85030b0b1a56b76ced7675780cac7d3f1acf1787db0b7a47c395d1eac5715fa8d01200001253fe57f9825775ba394ecaff16c27d9b70b260006a6eb832adb35e4f27d4a7cb0b2ac80000024a7fe8ff3090024a2fabfcc242c7e3ba04963f7dfc849e8f5b5a8755fa7e9d8b76adcb7a5ba000bbfdefa04977fa7ff205dff5ba04977feefe40249cf7bfcc009cfadd0249cfddfc8
      (by decide) ⟨22543, rfl⟩ (by decide +kernel)

  private theorem rb471 : (⟨[⟨3,11,false⟩,⟨5,7,false⟩,⟨17,4,false⟩,⟨257,2,false⟩],41277,1⟩ : Box).Closed :=
    replayCloses (.cons rb469 (.cons rb465 (.nil)))
      24 344 0x24ec0fccca7cdaa7fcb43ba5ddbcfb0bf4a26000173d4f40905cfb7fe424024173caff31140dec9a9e1c6cb647347716db6dd5ca00005cfcdd024173e77f2120120d9fe7f300906cff3f980367fdf40906cfcffe46cf5b1a078ded3baae5bcd763de29180728673bae978bdd6c3eced00000120d9efbf3090024107f9bf309009074fabfcc02410ff83f9803b7ef7409076fa1fe421e4fa70616a9ed37eedb378bb40037db69da57a7abfabf0b74014e8e53daecbbf0e462bd93a00000241f7f93f98000adf8be8120adf67fe4009052fe1fe6120120c9fbdf984804925ff7f98
      (by decide) ⟨20638, rfl⟩ (by decide +kernel)
end

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
mutual
  private theorem rb472 : (⟨[⟨3,10,false⟩,⟨5,7,false⟩,⟨17,3,false⟩,⟨257,2,false⟩],21865,1⟩ : Box).Closed :=
    replayCloses (.cons rb471 (.cons rb470 (.nil)))
      26 229 0x7b35d1c95305fe795f57caf1768065edd6caa4f173b1ddcfc7abd5f9768031b5cde4e4f2148ed3d1b1d87789caf2000000024acf63f98159e7ba04959f37fc8e8be383fdb2ee6bc2d99300ad92cd389a2f33a2efbb5bef0f96680000081ff1e81240fc9ff90009207f7bf3090abfc2f4092aff1ffe40249efaefcc000924ffc3fcc240a9fd8f4092a7f47fe424307fd6e81260ffddfc8
      (by decide) ⟨10932, rfl⟩ (by decide +kernel)

  private theorem rb473 : (⟨[⟨3,10,false⟩,⟨5,6,true⟩,⟨17,3,false⟩,⟨283,1,false⟩],285,1⟩ : Box).Closed :=
    replayCloses (.nil)
      16 236 0x1b40da77fbbdadcbcb0bb409b33e192ec73bdb55c4eabc5c30121aa7b363b6b4db6fb7179797979000000121a9bf315b55f338ae57ffb2ba74c0e40f98a5be5ffb0bab0bb400004a0fcfe61220ff740941c9fe40c6876b15cafff6ebb3860316d27a9d0f2c774ed03d67395d9fcf4759e97a000140c9e559f1b9bdfb1590000020c8f4094183ff2101d1f9dee6ada6e80000941befcc2400777d024071ffc8
      (by decide) ⟨142, rfl⟩ (by decide +kernel)

  private theorem rb474 : (⟨[⟨3,10,false⟩,⟨5,6,false⟩,⟨17,3,false⟩],259,2⟩ : Box).Closed :=
    replayCloses (.cons rb473 (.cons rb427 (.cons rb444 (.cons rb447 (.cons rb450 (.cons rb453 (.cons rb457 (.nil))))))))
      29 267 0x94d0bfcc24025348fe614c286e37b386f7a569615e8000094dbdf98481ad7d024365ff909106cfd02507bffc8049a89fe606bbba049ac1fe42455f3d025551ff218f98dda3ba1796cbd01a574470bb9d2cacacd7cde974c001779b35e9e581e374ed00012cdf4092537fe42ecaf1fee376653d2f402a921b0dbd136dd3b40b3f5e4e472d9afe3baece18010bd3f7369389c9c300000004ac7a0492a3ff20048000000
      (by decide) ⟨129, rfl⟩ (by decide +kernel)

  private theorem rb475 : (⟨[⟨3,9,true⟩,⟨5,7,false⟩,⟨17,3,false⟩,⟨263,2,false⟩],6843,1⟩ : Box).Closed :=
    replayCloses (.nil)
      21 267 0xf6cbd274bff359cafd7676809006ccbd57f559d8f96ced012137b3efe3a78d98f2b2b67e81962b1d52a146a1e9e9fd4bc02409046f97e4e0bb6e8f973b8b2b35f8e6bd5e40480000049c4fa04927dbfe407ba71dbaf8d99de5ecf97c7ca34000049cb740924ebbf9015e9dcbcb37d75b6d91db69468033b41c505ed7f5c57664c0bdd6d8df65b33ab3dd59595a59a00000257b67fcc4d6adf57d6d8cffaf2bd3f40002f777d0257b8ffe4241ed6fa048f6effc84804877e7f98
      (by decide) ⟨3421, rfl⟩ (by decide +kernel)

  private theorem rb476 : (⟨[⟨3,9,true⟩,⟨5,7,false⟩,⟨17,3,false⟩,⟨257,2,false⟩],17537,1⟩ : Box).Closed :=
    replayCloses (.nil)
      20 380 0x126c7fd7f986db26a66647ebf5a5b6db6db6ddeeae500ca075386c9a3adb9bec2e76c7cbabc000024d8ffcff3090d8fcf7409363f9bfe4024d8fd77e60b30a2b95fb27ffef176eff0ba6000619a1b5dc6d6e6def6cee58800009363f4df984801260bdeff309009305e3bf3009323f87fcc0c8fcafa04991fe5fe4323fc3d024c8fdcff200647e3ba04991fbefe4024d0fc8fe60049a1ffefcc55933a53c79729eae570a740057baff5a2f9bca96f75c578b740085e97cdf1f57bd79d877b36e16e809000009377fc5fcc24377ffee8126eff93fc8049acf73f9801acfc3d024d67b9fe424024db7f9ff3090db7e2fd024db7efffc8
      (by decide) ⟨8768, rfl⟩ (by decide +kernel)

  private theorem rb477 : (⟨[⟨3,9,true⟩,⟨5,6,false⟩,⟨17,3,false⟩],253,2⟩ : Box).Closed :=
    replayCloses (.cons rb419 (.cons rb475 (.cons rb476 (.nil))))
      19 231 0x12683d8fe602fd6679b65d2f97a4e8012abe953c5fcfce95300001a0f7dd024d0791fe431dff3f40931df9fff2018efeefa0498efe3ff9090366e1ba049b37adfc84855f07a04957a9fe41d55fd7f93d2febc9930327b5b2e66c5bfae7ba44c04836aec3753deea78da4e37d7db8bca54000004a767bf3117d67bddbadb76796ced0000121dd3fe600124ba3f98480483737f9800
      (by decide) ⟨126, rfl⟩ (by decide +kernel)

  private theorem rb478 : (⟨[⟨3,8,true⟩,⟨5,7,false⟩,⟨17,3,false⟩,⟨257,2,false⟩],12399,1⟩ : Box).Closed :=
    replayCloses (.nil)
      29 309 0x72566b9345d379afa6dbb5fcbdafcbb40198ea7c3e9e9cdeedf693a50b7dc5d1f9080900eb75bafa70af4a7936adc2d37cbe8e87cdecdbb56febc001bad76bb092e07350e76d3f2fb5ee7cbcbe580000000000de3ba04837befe42ee4ed62bd97b5ed7f4e180000241bfb7f309197f17a04b2ff1ff222a0a160c4fe85cd6b9bb38b2ac80398596ca7b5c5d9d9b6ef77b2bcbc800002597f47f98004b2fe77e622faf6dce979b23c6eac8e474b740001275fcfe61201275ceff3006064d5fb6b3d9edd767169468000ebc6e81275c6ff909097ed7d02497f2ffc848
      (by decide) ⟨6199, rfl⟩ (by decide +kernel)

  private theorem rb479 : (⟨[⟨3,12,false⟩,⟨5,6,true⟩,⟨17,4,true⟩,⟨257,2,false⟩],33957,1⟩ : Box).Closed :=
    replayCloses (.nil)
      18 248 0x12b5376bb589ddcb8d81e2ed00963b3cdb181e18ee76db8b9de5ca0032a69be37acfcbf37f4b7859300517b74f52b9bb5ddb38da5da029aeea7adeec1749b4dfec5743a1ca9d0000004936f17f98136e87a04936ff7fc87393a6f7c76bd3bac9d00e365d69bcb0bedd2f400011ef17e81247bdfff9008f7c3f40923dfdffc847bf9fa0491ef3ffe4023df67d0248f7ffff90092ade4fe60156edba04956e7bf90b37b3d024b3707fc80
      (by decide) ⟨16978, rfl⟩ (by decide +kernel)
end

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
mutual
  private theorem rb480 : (⟨[⟨3,10,false⟩,⟨5,6,false⟩,⟨17,3,false⟩,⟨257,1,false⟩],16443,1⟩ : Box).Closed :=
    replayCloses (.cons rb479 (.cons rb472 (.nil)))
      24 403 0x80f81e812407ceff90203ebba04901f03fc8480494efa7f30a777be81253ba7ff21214eed7d024a7797fe42400929dcf7e614ee77d024a770ffe40a7703d024a773bfe429dc7740929ddf7f2000497ef7bfcc2fdf07a0497ef53fc810ee97a0490ef7ffc80490eff7f98010ee87a0490eff7fc80495effdf980124dbb3fe6136ff7d0249b7cffe4009b743d0249b7fbfe40092cdf8ff30900933ff91fcc0fb13c5c2dcfabc5dec2ed0018cfd3d024c6797ff212012633f8fe618cf33e812633deff900c67b6e812633cf7f23681d199d267474accd000126fbe9bf300024d9ff37f984801263bfb3f9848
      (by decide) ⟨8221, rfl⟩ (by decide +kernel)

  private theorem rb481 : (⟨[⟨3,7,false⟩,⟨5,5,false⟩,⟨17,3,false⟩],231,2⟩ : Box).Closed :=
    replayCloses (.cons rb404 (.cons rb478 (.cons rb477 (.cons rb474 (.cons rb480 (.nil))))))
      21 156 0x24d5be8fe600012012e17f4dfa28afcce7a5ff2fd4f4ae18bcbb705635e986c584971f8df8232fe7a0499747fc8a3033db50b9be9d6c5b1e2ed00015d9fa04857dffe402bb6e81215cf7f212004ae767fcc2434e77d024d387ff200048120
      (by decide) ⟨115, rfl⟩ (by decide +kernel)

  private theorem rb482 : (⟨[⟨3,9,false⟩,⟨5,4,true⟩,⟨17,2,true⟩,⟨227,1,false⟩],16997,1⟩ : Box).Closed :=
    replayCloses (.nil)
      27 336 0x72cb45032a956b39400aca6d50f4d6b3f42ed01203af5039b5b8b1691302cd4c98bb74dcccd9ab170c000000496df5df9817bfb3f4092f7fdffe40092f7fbdf98aa86b4ad0d3c80304d697ac4953006bcd1a5a4cc91300000124b7fcfe600492df13f9804eff4fd0249dfd7ff9009277fadf98056ff67a0495bf83fe4213c2f409213c7ff90086fc9e812437f5ff9090bcf99f4092f3ef7fc86a26a2e195a32b3b0b340014ee27a0494ee37f900092fdfa7f3009373ff6fcc12143b70e249500001268bfb7f9848
      (by decide) ⟨8498, rfl⟩ (by decide +kernel)

  private theorem rb483 : (⟨[⟨3,8,true⟩,⟨5,4,true⟩,⟨17,3,false⟩],241,2⟩ : Box).Closed :=
    replayCloses (.cons rb326 (.nil))
      17 298 0x8daec2cce06ebfd716ca98090025bbabfcc1bba3e812ddbfff90900976f8ff315b7dd0255b23fc82b61ba04ab75bf9000926eb7e634e943a52dfd4bab65e81c61b7b263537db2b648c04809bda13a382ef3d2f4000048ef5fe6004b0c4fe612012dba7f980486eefcc10627a04a0c6ff21200c9fa0480e7ff90097367f9848e7b7a04b96dfc848049a95fe61b0da72bfb2b264c002b4fd024557ff9090091593f98482a07a048a9dff200000
      (by decide) ⟨120, rfl⟩ (by decide +kernel)

  private theorem rb484 : (⟨[⟨3,7,false⟩,⟨5,4,true⟩,⟨17,2,false⟩],219,2⟩ : Box).Closed :=
    replayCloses (.cons rb322 (.cons rb318 (.cons rb482 (.cons rb483 (.cons rb349 (.nil))))))
      20 143 0x12012e03ff7e53ba9e98494ee6ffc11e8ec4f4d57faf2b95d97a0001cf4fd02473afff232d1d4f27f5d53399d91300001239ff7e6123a75dd025d381fe42424e67d02493bdff20004819b7e9e81266de5ffc800120
      (by decide) ⟨109, rfl⟩ (by decide +kernel)

  private theorem rb485 : (⟨[⟨3,8,true⟩,⟨5,6,false⟩,⟨17,2,true⟩],259,2⟩ : Box).Closed :=
    replayCloses (.cons rb357 (.nil))
      18 255 0x2536eff3090094debfcc0094d8df98480486e1fe6105af5cdf575d3c8029e4f66d3c1ff6574bd00003af1e812ea4ffc83ab6e812ea7bf90900972d7f9853c9e76f7ee1c91300b3e79896c2cf74bd000e7cfa04b9c7fe400973dbf309009355bfcc5191dec2cacf64c98057376b8dc59595d246000156b740955ddfc80ac3f40915effe402457eff300562fa048ab3ff20000
      (by decide) ⟨129, rfl⟩ (by decide +kernel)

  private theorem rb486 : (⟨[⟨3,8,true⟩,⟨5,6,false⟩,⟨17,2,true⟩],243,2⟩ : Box).Closed :=
    replayCloses (.cons rb485 (.nil))
      19 226 0x65e9cebefb68727e80d49c31df533bab5289e28d0003a766c989cdcdd334026bac6e5c1cac97a02400002416bbf3090095ad4fe60f3fdd025e727f909067dba048cef7f208d6ddddad2b244c075e5e9d6d3bbea16cf202401b13b1f4e2723fd95f570af40000012a327fcc2402546b7f98230369c4e29ee0ffb67900008e6fa0488cdff9090091d7df9800
      (by decide) ⟨121, rfl⟩ (by decide +kernel)

  private theorem rb487 : (⟨[⟨3,7,false⟩,⟨5,4,false⟩,⟨17,2,false⟩],205,2⟩ : Box).Closed :=
    replayCloses (.cons rb484 (.cons rb486 (.cons rb388 (.cons rb481 (.nil)))))
      29 299 0x91176fe9f40945dbf77fc1e88792f25667b2f042ccc0716128c1ea7f71167e17d025167f4ffc80128b3fa3fcc009477fd37e612238fdcf409471fb7ff21223dfe4fd0251eff9ffe40d59d57c3b1eaeafa44c000128cdfd3fcc0446ff5f409446fabff2123a3fdb7409747f9efe42d7fb3d024b5fc1ff20012427fdfe6012487c4ff3002490ff6fcc00923df8ff3025dc7740925ddf7f204dbdb740926de7bf90009371e97f72fdbd30932efffc1001204800
      (by decide) ⟨102, rfl⟩ (by decide +kernel)
end

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
mutual
  private theorem rb488 : (⟨[⟨3,5,true⟩,⟨5,6,false⟩,⟨17,2,true⟩],199,2⟩ : Box).Closed :=
    replayCloses (.cons rb254 (.nil))
      16 273 0xc7c95ebc7264f2008606f48e31da0001d5774097503fc8012e74fe6120126b4ff9804a299fe622dee8128a87f9041c4cfec6e800009452df980d89c42fce3a6000686b0f0d93acb01a7fb1dc1db71d3000cb77d68786964bd000012a6eff30b0e2b5fb1da00568d684e8000052d7d0254cbff2391bb42c66fda7681954f993f3c32ddad91a0031ad439a963b4000012a577e612012a537e60000
      (by decide) ⟨99, rfl⟩ (by decide +kernel)

  private theorem rb489 : (⟨[⟨3,5,true⟩,⟨5,4,false⟩,⟨17,2,false⟩],173,2⟩ : Box).Closed :=
    replayCloses (.cons rb273 (.cons rb488 (.cons rb271 (.nil))))
      21 203 0x32e9a9a6fa2a58b642cd00001ee9f4093dbbfe40093d2df98ca133bbe726b7d6cf200000931e9fcc240244667f30091d43f980123a7bf3061c1e812c353fc804b69efcc24025b537e600125bfbf300631a6cea592f40480128383f9801203f3f984804bafdfe60001200
      (by decide) ⟨86, rfl⟩ (by decide +kernel)

  private theorem rb490 : (⟨[⟨3,4,true⟩,⟨5,4,true⟩,⟨17,2,true⟩],165,2⟩ : Box).Closed :=
    replayCloses (.nil)
      25 248 0x1566a523ee400031ba048237fc8036a4776ec76800024b4fe60ab3cf3cc000bafa0492bff2096b15ab62c80008afa04965fe402480fe6012427f98587d02496ff914d5e52f440047ba0494dff20125dbf9804989ff31162a6bcf53b49500060bd024c3ffc864944fa9d27a800379eba966a56b46968b16b3d040000000000
      (by decide) ⟨82, rfl⟩ (by decide +kernel)

  private theorem rb491 : (⟨[⟨3,4,true⟩,⟨5,4,false⟩,⟨17,2,false⟩],103,2⟩ : Box).Closed :=
    replayCloses (.cons rb490 (.cons rb231 (.cons rb243 (.nil))))
      24 290 0x3a14bd6edd26e8090024962fe6004a285fd163d309441ff82024cadfe6004999dfb8b74c25cbbf8205e2a356adc3a7280900244fefcc04e6e8122677f222e7a04a2dffc823d7d025157fe431f3133f38e98011d9dd937bd49e40000e5dd025c07f91379e59e7a000117e8120bfff2398b217cf401a8503e68eec9d31000000c5f409059ff90ddccd23ea4f2015a6ef5eda000090777e6000000000
      (by decide) ⟨51, rfl⟩ (by decide +kernel)

  private theorem rb492 : (⟨[⟨3,4,true⟩,⟨5,3,false⟩,⟨17,1,false⟩],101,2⟩ : Box).Closed :=
    replayCloses (.cons rb491 (.nil))
      4 7 0x12048
      (by decide) ⟨50, rfl⟩ (by decide +kernel)

  private theorem rb493 : (⟨[⟨3,5,true⟩,⟨5,2,true⟩,⟨17,3,false⟩],101,2⟩ : Box).Closed :=
    replayCloses (.nil)
      19 305 0x1962b54a95293100004961fe632d58a1f3200d86e776ad50ba5e80000024bb7e63990bd7ac79000667e8126dffe472ca57ab63260244d88dfbd26000de7a04991ff20ae1b2b52c5e800024c77f986c3d05821799e88545658b59f412a1e085e0b31643d446d3e959856e8b6938a1be6cb1683d048b07c89f32000371f4cd4b74782a94ad962d47d04a692b07362540481a8fa65cc10c42c16583c83cc50c5692ad42921012000000000
      (by decide) ⟨50, rfl⟩ (by decide +kernel)

  private theorem rb494 : (⟨[⟨3,4,true⟩,⟨5,2,true⟩,⟨17,1,false⟩],101,2⟩ : Box).Closed :=
    replayCloses (.nil)
      14 234 0x1952d3cf5ea4f200033eeba285ee0862cc4b658b5ee8233c6f42f4006bdd3062c526ecbccb2c50d146c58b450f0d45048069dd30ddba63b8eea54bf49d300062dd6564c5424ae49b2c5b37410000e67a85e800d7ba04990ff219abc9631e402790f0fa8c0001265df980499b7e61ab740936efe4326e81261dfc8000048
      (by decide) ⟨50, rfl⟩ (by decide +kernel)

  private theorem rb495 : (⟨[⟨3,4,false⟩,⟨5,2,true⟩,⟨17,1,false⟩],101,2⟩ : Box).Closed :=
    replayCloses (.cons rb494 (.cons rb493 (.cons rb228 (.nil))))
      22 189 0xe43646b31fa000bb74092bdfc867a3cf6500004946fcc15eaab79e8065643cf72000024d0ff98db570faf29800da7a0498bff90d37d024c6ffc8633e81267bfe4024dfbf30cfba04988ff200c9ab5598bd0120049af7e600000000120
      (by decide) ⟨50, rfl⟩ (by decide +kernel)
end

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
mutual
  private theorem rb496 : (⟨[⟨3,7,false⟩,⟨5,2,true⟩,⟨17,2,false⟩,⟨97,1,false⟩],425,1⟩ : Box).Closed :=
    replayCloses (.nil)
      22 238 0x32852bb69c33ae6ce501230cea4b495dacad9fa051c55ae2e676dd2f40000000e87e812eeffe4054c9dd30b25e809000975dfe6153770fa8c0480392fa04bb9ff9112b4a54b1ca0240009751fcc24025c7bf3057821eb11a0065085e9a000073ee812e23fc88d3d43b401755a60001d1ba04b86ff90900241b3f98
      (by decide) ⟨212, rfl⟩ (by decide +kernel)

  private theorem rb497 : (⟨[⟨3,4,false⟩,⟨5,2,true⟩,⟨17,1,false⟩,⟨97,1,false⟩],109,1⟩ : Box).Closed :=
    replayCloses (.cons rb496 (.nil))
      17 227 0x4c854bd7af5a590120048267f31dc95030b1da02400241ebfcc024163f9800120fefcc2ab562a5ebd691a01133330c9809000024a2ff309458388debd49930068a963c540199b27866b8cd0000000121e8125f7fc848049b77e6025696bd460554a9439400640e3d7928000309f40936dff2120
      (by decide) ⟨54, rfl⟩ (by decide +kernel)

  private theorem rb498 : (⟨[⟨3,4,false⟩,⟨5,2,false⟩,⟨17,1,false⟩,⟨97,1,false⟩],99,1⟩ : Box).Closed :=
    replayCloses (.cons rb497 (.nil))
      7 69 0x9147cdd554894c4c68e9ba02951c77f30939b6fe88240092bbfcc87a6126d3fc10d5e81255fc8
      (by decide) ⟨49, rfl⟩ (by decide +kernel)

  private theorem rb499 : (⟨[⟨3,6,true⟩,⟨5,4,true⟩,⟨17,3,false⟩],229,2⟩ : Box).Closed :=
    replayCloses (.cons rb277 (.nil))
      18 330 0x6d230de1df7564bd003793b296fb0bbb4ed0120b3239dd1fda3fda5e800025b6eff302d8bd024b71ff21210eafa0490c5ff91062fd02506fffc820f0f40941b9fe4240240657f98272f4e8703a6c97a03ac2c9c9b274acad9da000093593f980126a27f9848aa67a04aad7ff2136d7d6b5b7f49da05d43d9ed75b95f2e5767e8001544f409551bfc82a81e812aa77fc8aabba04aa81fe40158bd024571ff2097b1b93cdcd1dd346031ceb79723f1c8f2bb2f40004b3ba0492fefe41145fa04a2bfff2120128b77f980000
      (by decide) ⟨114, rfl⟩ (by decide +kernel)

  private theorem rb500 : (⟨[⟨3,7,false⟩,⟨5,2,true⟩,⟨17,2,false⟩,⟨89,1,false⟩],699,1⟩ : Box).Closed :=
    replayCloses (.nil)
      24 295 0x17295db6bba48980363676d7275b25e800359030a148c9a3000c8a26a38696cb20000002567e8124bbffc8480492ddfe612ddf409258ffe424009258bfcc45475cc4d285baecc2b2006cd8e696c4d37db65900004abba049281fe4240094517fcc24024160fe612012640fe626d306cf0980002415b7e632f709f5ea364d9e40000a1ba0482d6fe4450a18a5aa4b2000ccdf409326ffc848a7afa04a957fe42404d3f40912bffc8
      (by decide) ⟨349, rfl⟩ (by decide +kernel)

  private theorem rb501 : (⟨[⟨3,4,false⟩,⟨5,2,false⟩,⟨17,1,false⟩],91,2⟩ : Box).Closed :=
    replayCloses (.cons rb495 (.cons rb492 (.cons rb489 (.cons rb280 (.cons rb499 (.cons rb307 (.cons rb487 (.cons rb498 (.nil)))))))))
      30 208 0x1cc6d7b626db6d8ed9da051f17c5c972b99c993003960bd4935faed6eb75c564048002cc2fa04ace9ff9090096999fe609a303f5a57592f4039d3439df5d000004be85fcc002526dbf31b72a5f3a3a6c91300ea567c3a5c7e800002547bbf3090475ba0488f77f21230d0f40961fdff20000004812000
      (by decide) ⟨45, rfl⟩ (by decide +kernel)

  private theorem rb502 : (⟨[⟨3,4,false⟩,⟨5,2,false⟩,⟨17,1,false⟩],85,2⟩ : Box).Closed :=
    replayCloses (.cons rb501 (.cons rb500 (.nil)))
      16 217 0x241c9ba2ad2eedfcc24a37e0809122ff98480489e3fcc452f40946fff900468f409461ff90187e8120f7ff20089e81208dfe4042fa04834ffc800207a048277fcd77d30934dfee12190f40937dff23a6cd0c980570cef5e7a0005a5286681d06cb3c26000345f409333ff2004de8128dfc80
      (by decide) ⟨42, rfl⟩ (by decide +kernel)

  private theorem rb503 : (⟨[⟨3,8,false⟩,⟨5,2,true⟩,⟨17,2,true⟩,⟨83,2,false⟩],4459,1⟩ : Box).Closed :=
    replayCloses (.nil)
      25 386 0xc3f3ca26f72eda5e8002fdefba0497ef23fc8485fbd374092fde3bf90908778bd024877c7fc843bc9e81243bebff2010ee47a0490ee0ffc84fbc4fa0493efdbfe4027df5ba0493efddfc847bc0f40923de77fc800491efedf98e2aa3d1279003b6692b9a69da0000926df3bf300249b7c6fcc0a3713d024a371bfc8012437f87f300cffe4fd024cfff3ffc848049a7fc2fe632f332b68c2d394000c4e6c1aeb4b9dacac5640000049abff77e600126dbfdbf98c35a54a99d9932600329fbbe812653f1ffc806dbf33e8126dbf7bfe40aff7d0242be7ff201979be81265cdff83767d30906ceffb8
      (by decide) ⟨2229, rfl⟩ (by decide +kernel)
end

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
mutual
  private theorem rb504 : (⟨[⟨3,5,false⟩,⟨5,2,true⟩,⟨17,1,false⟩,⟨83,1,false⟩],133,1⟩ : Box).Closed :=
    replayCloses (.cons rb503 (.nil))
      19 308 0x48049bcf3dfbd713d3097aed7f82240253b5dfaeb6e984ae96fc1120129373f98480125a97f31c868da859992140380f28d639ad69640002313d0244637f91cd2d7a9509280000488e8fe6120123b67f984804bae9fcc05ca950d0eaa1d25400e7b7a04b96dfc80012ca67f89bdd3091307f827468e0eec6e8091546c1f55b12a0004d1e812261ff90911fbe8128e7ff2012895fe61200128a6fcaafa612417f8224309e81261bfc8
      (by decide) ⟨66, rfl⟩ (by decide +kernel)

  private theorem rb505 : (⟨[⟨3,3,false⟩,⟨5,2,false⟩,⟨17,1,false⟩,⟨79,1,false⟩],81,1⟩ : Box).Closed :=
    replayCloses (.nil)
      21 294 0x120ab0fd114aab9fcc254b9fe08000a770dd01497ef4bf984997793ff04a3eda6e2e771d3008d3e6eb75c1c9d3002dac0e0e0ecf2e97a000002456cff30159dd02457f7f208a87a04a2fdff2368563c3a3a3e3e36590000120acff98019e3e812658ff75ee984b9f7f7090de7a04991ff209aa268695693f40001257bf31379c3ebda602445db49de7a01c14a1a300cb069966334000000124dbf300376e8126bdfc848
      (by decide) ⟨40, rfl⟩ (by decide +kernel)

  private theorem rb506 : (⟨[⟨3,3,false⟩,⟨5,2,false⟩,⟨17,1,false⟩],75,2⟩ : Box).Closed :=
    replayCloses (.cons rb505 (.cons rb502 (.cons rb504 (.nil))))
      18 116 0x90134fd1d52249ff309068fe094c57a153000627e81269ffe4556a952f7202415e7a866801287b6af0d00000049acfe6006ede81266dfc81200
      (by decide) ⟨37, rfl⟩ (by decide +kernel)

  private theorem rb507 : (⟨[⟨3,2,true⟩,⟨5,2,false⟩,⟨17,1,false⟩],39,2⟩ : Box).Closed :=
    replayCloses (.nil)
      17 108 0xd156d00ebd6217a005053cb50a98014065e8a1bdfa4bd00000000234d21e400eb147406631ebdc81560e4c3b4000a000000
      (by decide) ⟨19, rfl⟩ (by decide +kernel)

  private theorem rb508 : (⟨[⟨3,2,true⟩,⟨5,2,false⟩,⟨17,1,false⟩,⟨31,1,false⟩],33,1⟩ : Box).Closed :=
    replayCloses (.nil)
      25 236 0x112959692bab2114a942260043942000752d5af301369bbd7b680000d66274ec5e80650b152f300a64f5a42c1c900f05dbca6061daf8d2f6d9a536c800014b154bd7a9200d1591acc40028090bd7ac199dae9600008a1c19d638b8ba54c0ca1ebc711dfdfaca0000000000e5d00532fc80a012b9f980a01229f984804a2f98
      (by decide) ⟨16, rfl⟩ (by decide +kernel)

  private theorem rb509 : (⟨[⟨3,2,true⟩,⟨5,2,false⟩,⟨17,1,false⟩,⟨29,1,false⟩],31,1⟩ : Box).Closed :=
    replayCloses (.nil)
      18 147 0x23a5687e8019798b8674eb34c181d50d0ecf9e80014000d5ba00a6ddfc80a002937f30140242bf980a08e81299f90d52a50a98014334d216000a1400654359e08090000025a048b7c8
      (by decide) ⟨15, rfl⟩ (by decide +kernel)

  private theorem rb510 : (⟨[⟨3,2,true⟩,⟨5,2,false⟩,⟨17,1,false⟩],29,2⟩ : Box).Closed :=
    replayCloses (.cons rb509 (.cons rb508 (.cons rb507 (.nil))))
      21 108 0x55ea94c00a22c340190a5a7800280ac5ea1da035a52a1c1c4000000003368124df222956980754bd43b40cb495e780000000
      (by decide) ⟨14, rfl⟩ (by decide +kernel)

  private theorem rb511 : (⟨[⟨3,4,true⟩,⟨5,4,false⟩,⟨29,2,false⟩,⟨31,2,false⟩],459,1⟩ : Box).Closed :=
    replayCloses (.nil)
      19 248 0x7376ab4f0711301206375b189d9fafccb7968743a500480000acfd024177ff90cc7ca766bbbdd5ab3b4b43e500480002d9e8120a0ff9090170f4090573fc803646b51e9dda7900634b3bdbfb1130120000b07a0482a9fe424009322ff98480499f3fcc4d9343732b0b268c06ae7078b03e5eafe97a00241496e812a577f212090bd02448fff201225cfe600048993f98
      (by decide) ⟨229, rfl⟩ (by decide +kernel)
end

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
mutual
  private theorem rb512 : (⟨[⟨3,2,false⟩,⟨5,1,false⟩],25,3⟩ : Box).Closed :=
    replayCloses (.cons rb107 (.cons rb103 (.cons rb511 (.nil))))
      27 211 0x120048a91fc4ddf4c24487ff044804bb77e55ba6125bbf821d2bc6c7d7400eed638f6d0000012e9df984804b937e60289c66f6d00ea350ecf9e8013bb8a54a769c9a30000000357d024117fe424283d02494ff212004996ff6af4c24abf82240248bf3090968122df2000
      (by decide) ⟨12, rfl⟩ (by decide +kernel)

  private theorem rb513 : (⟨[⟨3,2,false⟩,⟨5,1,false⟩,⟨19,1,false⟩],21,2⟩ : Box).Closed :=
    replayCloses (.cons rb218 (.nil))
      25 234 0xb95acdeba005007d434cd6324003c069692a4ed0006561cd4388000000014d4ff984a10ada63b400a2ead5a601a7e716d7a4c00001acf4014c0ff9014024c87f3014024c9bf3090aba04997f210f9ebd79e8014150a97af7200ddc85e801400034e812a9f90900096efb8d05724154b31bab80a00
      (by decide) ⟨10, rfl⟩ (by decide +kernel)

  private theorem rb514 : (⟨[⟨3,2,false⟩,⟨5,1,false⟩],19,3⟩ : Box).Closed :=
    replayCloses (.cons rb513 (.cons rb512 (.cons rb147 (.nil))))
      20 155 0x48013f3e972ea22747a1921323f984b9bbfd112012cbfecb4c253be08442800282429423400a083c34a77ac5e8014050141c90faadc324032878af00000000254a94c00a0280000a000
      (by decide) ⟨9, rfl⟩ (by decide +kernel)

  private theorem rb515 : (⟨[⟨3,4,true⟩,⟨5,2,true⟩,⟨13,1,true⟩],661,2⟩ : Box).Closed :=
    replayCloses (.nil)
      33 288 0x29a3e812a5fffc8a6b740953bbf900953dbf98279fa04893ffe4262a142c79002142f765000048987fcc2af1cda75f37043140001224eff304c9e812275ff904c5f40912cffc8048923f98250f40913f7fc8cb156d1b1ab4f2000481e81224eff90489f40913b7fc8039b162a5cd567900026f74091287f904aee812240ff201227b7e609cdd0de0366e1a9bab2d9624f6f410000000000000000
      (by decide) ⟨330, rfl⟩ (by decide +kernel)

  private theorem rb516 : (⟨[⟨3,4,true⟩,⟨5,2,true⟩,⟨13,1,true⟩],589,2⟩ : Box).Closed :=
    replayCloses (.cons rb515 (.nil))
      25 262 0x64210cd012004999bfcc054aa8c00012678fe619a3d024cc3ff229e62cf098195a92b163c800024c89fe6195dd024c81fe4325ba04995dfc8e2abaa5ebd697a000024cf6fe63a92cb829204d2bba28000254e9fcc0254b5fe632aa50f98cd000012a4aff314f1e812a49ff91495e43c80900254a1fcc5227d0254edff2000000000000
      (by decide) ⟨294, rfl⟩ (by decide +kernel)

  private theorem rb517 : (⟨[⟨3,4,true⟩,⟨5,2,true⟩,⟨13,1,true⟩],511,2⟩ : Box).Closed :=
    replayCloses (.cons rb516 (.nil))
      20 322 0x64ad217b90000492a9fc766e925bbfe6128b9fc12a862c5ee40298b10bd0062a562a66ad3b400000124a97f8e2dd24ab7fcc251fbfc12295f4154a2a5fe6128b1fe08579419300259286e8001178fa0aa5168ff30945f7f040482c3fe3a0f4828dfe612e5ffe090734af15432468000144f5c4a8f442a905ebfcc25c0ffb80b67d05520a87f30977bff04048281fc751e905edf984ba6ff048b4a54bd8600051dd02415f7f1dc7a4cefff04049973f98000000000
      (by decide) ⟨255, rfl⟩ (by decide +kernel)

  private theorem rb518 : (⟨[⟨3,4,true⟩,⟨5,2,true⟩,⟨13,1,true⟩],501,2⟩ : Box).Closed :=
    replayCloses (.cons rb517 (.nil))
      13 103 0x154b542260057aa87e800158dd0148a86fcc244f1fc10af2c844c01a958874c00af2552d5ea4dd0000004b285fe0297a597f7f30912fbf0400
      (by decide) ⟨250, rfl⟩ (by decide +kernel)

  private theorem rb519 : (⟨[⟨3,3,false⟩,⟨5,2,false⟩,⟨17,1,false⟩],69,2⟩ : Box).Closed :=
    replayCloses (.cons rb506 (.nil))
      18 226 0x120125a7f31cdba04b8f7f21201209dfe6096b8706d56d5a500006efa04831ffc80048367f9aefa6126f7fe08900d67d024dfffee5d30942fdc24024024a8fe604e2e1ddbb749fa00006cfa0483fffe4019dd0241fdfc804823bf300092a7fcde7d309351fc11200126fdfaad3091cfc11200
      (by decide) ⟨34, rfl⟩ (by decide +kernel)
end

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
mutual
  private theorem rb520 : (⟨[⟨3,3,false⟩,⟨5,2,false⟩,⟨17,1,false⟩],45,2⟩ : Box).Closed :=
    replayCloses (.cons rb519 (.nil))
      25 343 0x1201261dfa6a5b16c3262c24d3f04012002bee88a4170ff30970dfe0890096afe6004805e7a32d250ff9849b0fe08900922fcc024558bd114aa85fcc25491fc100393fd9fa04b93ff7ff864b93fe8ff30927bf47fee120012467f9af74c24d07f82247ce81279f9009014bd1d520f3fe61267ffe08dd26350d6939400004a9a3f98dad42d1b3d59a428000024489fe61223a7d053a5183f984929fc10069beaaa27931310a749a4fe61295fdc2402587e600000
      (by decide) ⟨22, rfl⟩ (by decide +kernel)

  private theorem rb521 : (⟨[⟨3,2,false⟩,⟨5,1,false⟩],15,3⟩ : Box).Closed :=
    replayCloses (.cons rb514 (.cons rb510 (.cons rb520 (.nil))))
      21 269 0x14071ee864ba0ff3014ab7e09c800abbcc0050cadf4452654fe612e53fc102860bd452782f44ea9379fcc251bfb80a56a16012f54a1e1a01543e56f5d000e62746bd8c4048000049acff3014366e81269dfc80a038e85a912fcc2517c13902412b7d0148953f98482a7f82090ab7405245bf30930efe0824375f45ad266bfcc25abf040000a0000
      (by decide) ⟨7, rfl⟩ (by decide +kernel)

  private theorem rb522 : (⟨[⟨3,2,true⟩,⟨5,6,false⟩,⟨11,2,true⟩],199,2⟩ : Box).Closed :=
    replayCloses (.nil)
      20 258 0x13b595ac9deb4a98000082f5140d9cbc492ccc579e824d1bb5aedc3a691a000026be92f7215558a1662aafa09952955a762f408b4843260325aa37b6800090f4c283d30bf75b79257658b260acb15c7d04547d30183835b562f400a00d2a583aa356b2742e180002ddd7331496782b2a98b14072ed8e1c46800025dd73ce566545259458a9dd0445ba6ee646f150f32cb658a00000000
      (by decide) ⟨99, rfl⟩ (by decide +kernel)

  private theorem rb523 : (⟨[⟨3,2,true⟩,⟨5,6,false⟩,⟨11,2,true⟩],159,2⟩ : Box).Closed :=
    replayCloses (.cons rb522 (.nil))
      20 264 0x8a10bd63c814b210f5d0020e0d6b3cf4000e73d005737ff212f558d58a9801414b458c499a0050150f5eb1c30000002bb0fe622950b5e1a0050052f40141bffe4125696bcc40028db56ad5e5300000283d7f98ca5528786800010be802834ffc8cab9c3c38c980005b7401413dfc80a6e802823bf90d42556ad8e98000a9fa5a692a893144fd040000000
      (by decide) ⟨79, rfl⟩ (by decide +kernel)

  private theorem rb524 : (⟨[⟨3,2,true⟩,⟨5,6,false⟩,⟨11,2,true⟩],141,2⟩ : Box).Closed :=
    replayCloses (.cons rb523 (.nil))
      16 228 0x2a55ad54b17a01940f6c4af2b69000a000002a9b3f980a29f3e802a9c7fe4450a4c52f525e805496a8ea1d2b597a00055af52b5693b400a000a5774015481fe412a9a78020e2c1c5c38ed001898a1ee4000002898bf980cdcbcf73d70d9e405cd1dd1ab78e97a000011b3d005441ff22ad5e4326000005464fe6000
      (by decide) ⟨70, rfl⟩ (by decide +kernel)

  private theorem rb525 : (⟨[⟨3,2,true⟩,⟨5,6,false⟩,⟨11,2,true⟩],139,2⟩ : Box).Closed :=
    replayCloses (.cons rb524 (.nil))
      15 102 0x19a8d434b193005162b50c66814756e92742474c98003ddac179e800000d62fa00a6acffc8ca27778d0e2f400a00029adefcc05001455cfe60
      (by decide) ⟨69, rfl⟩ (by decide +kernel)

  private theorem rb526 : (⟨[⟨3,2,true⟩,⟨5,6,false⟩,⟨11,4,false⟩],243,2⟩ : Box).Closed :=
    replayCloses (.nil)
      21 254 0x26be9ac691a4706b79a5458aabe8220be99e67b77d4c42c12a16e6e62863e70e8d93a4c980140eb24f2a9dd731a67154c000000447a13a5991b16bdcf754caac561e8271f531aa17742d9da0329b329676ed2f400a0b3837599d1954bfbd52fea5da000140233e985a7d30bf75d57565159b58de5bb2c571f41297bd50ccee85d3460050140b8fa6003031a6b7a96aa6d2c2c980002a3e980000000
      (by decide) ⟨121, rfl⟩ (by decide +kernel)

  private theorem rb527 : (⟨[⟨3,2,true⟩,⟨5,6,false⟩,⟨11,4,false⟩],213,2⟩ : Box).Closed :=
    replayCloses (.cons rb526 (.nil))
      17 375 0x1af523931b476ba44c063cae74850e56c938500a0b3b59ae4d6f9dda68c000002dba00a09efe4749a0b4c7ef9b2f408ab8ad1c78f0d96002802800c6e8028237fc834f0ccd2d525e80d95aa93eb27480050050092f4c876adb570c6b3458ae7eaac5ab75af50c4217a3963c724ddeb4919246004d7cbcf98b4bfa17680000a2f510b03a6aa1b86cc579e820189f1f9daccc2eeb3460050486e8f0f0fe9200000b4f4830777aad6e780d3658a7be83d1674e8fb9eaaa3963c0362d58a748e908047c47071a79e366d715001401402bbea0d9cbdddfba49e0acb1477d52148c3c86188d53e6cb15b7d4400000
      (by decide) ⟨106, rfl⟩ (by decide +kernel)
end

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
mutual
  private theorem rb528 : (⟨[⟨3,2,true⟩,⟨5,6,false⟩,⟨11,4,false⟩],183,2⟩ : Box).Closed :=
    replayCloses (.cons rb527 (.nil))
      16 264 0xc3238e199f992f400a29b323335a9497a0051176b257addbb4d18010e56ae71b33b5b2c000001d87a00ae73fc81313a62fd8a98011a56ae686e6671b65800a0000e13e802bb6ff91c74b9b277cc9130028515ac54a949e400a03b374015d3bf904f192492199e0ec805001e7e802827ffc80bb7e9d4b749d3003559668e38601d43e66f1c70c00a00291e9b999facedd65e80140000141a3f980000
      (by decide) ⟨91, rfl⟩ (by decide +kernel)

  private theorem rb529 : (⟨[⟨3,2,true⟩,⟨5,6,false⟩,⟨11,4,false⟩],175,2⟩ : Box).Closed :=
    replayCloses (.cons rb528 (.nil))
      11 135 0xb050b9b652bd65e801401193d005475ff9014442fa00a8d3ff230c9bb1a34a48981a64f53742cb74c980140005450fe61356634c54c08ad142b62001404b058f8e3b4000000a8f1fe600
      (by decide) ⟨87, rfl⟩ (by decide +kernel)

  private theorem rb530 : (⟨[⟨3,2,true⟩,⟨5,6,false⟩,⟨11,4,false⟩],165,2⟩ : Box).Closed :=
    replayCloses (.cons rb529 (.nil))
      22 215 0x6452707f66d3c005001f54a152ada768036544cdebc6db83e1fb69620452784db6d6d6ca5dae2b01db54eac52a5ed8d0bf40000000000a67b7f3086674713a5b8ba64c00a36e1c991c9fd4b4dd00029e7e802a93ffe40500154a9fcc0871bf5f9b317559da029b6ecb71647d9e0d97a0000001257d0051397f90140051267f9800
      (by decide) ⟨82, rfl⟩ (by decide +kernel)

  private theorem rb531 : (⟨[⟨3,2,true⟩,⟨5,6,false⟩,⟨11,4,false⟩,⟨157,1,false⟩],159,1⟩ : Box).Closed :=
    replayCloses (.nil)
      15 201 0x28d0de91c9c1cda48c0031134df69800001456cff301400515e3fcc0573740145677f20ef4d1b10a4dd00281e9d6599a4dd008a14397aa526206da3b3ba778cab6dcc2ed000280032a5f4015979ff90146523d0056507fe431d7ac71fa4ed001a4dda6989d006a75abd8c76800001970fa00acab7fc8
      (by decide) ⟨79, rfl⟩ (by decide +kernel)

  private theorem rb532 : (⟨[⟨3,2,true⟩,⟨5,6,false⟩,⟨11,4,false⟩,⟨151,1,false⟩],153,1⟩ : Box).Closed :=
    replayCloses (.nil)
      17 248 0x475bdb6bfaf6ad226032c6cd4e7b3b169b65e8001445e8a76a9db3d367800003686e802b6d6fe4050014b61ff30140052d23f98cdc636a766e756993002805bdba00a5b7bf90086f7d00521a7ff21659ae7d7400a29242d5438f00123f5f19d4b9dd3b404b90d8e9276800050135774015340ff202800a9a9bf30140dbbe80286c7ff206f9f4014371ff9000dddd0050d83fc8
      (by decide) ⟨76, rfl⟩ (by decide +kernel)

  private theorem rb533 : (⟨[⟨3,2,true⟩,⟨5,6,false⟩,⟨11,4,false⟩],151,2⟩ : Box).Closed :=
    replayCloses (.cons rb532 (.cons rb531 (.cons rb530 (.nil))))
      17 154 0x328a56a87369000a1cf2b50be3ba4bd00280002f9f4014171ff9187cc6164e6fda768000014174ff314606123bbc64bd002860e5231b1da000000505cdf988f1862dd89d000860eef1c68c0000652f4014cdfff2000
      (by decide) ⟨75, rfl⟩ (by decide +kernel)

  private theorem rb534 : (⟨[⟨3,2,true⟩,⟨5,4,true⟩,⟨11,4,false⟩],199,2⟩ : Box).Closed :=
    replayCloses (.nil)
      28 363 0x531acb9a5ba4fd002864ab56bd1eb4f20050001c3d00505cff2029ba00a08efe40052fbfcc65535af52daeedd0bbb16e80140096fa614df5969e35b3ca0b31427a089afaaa1aacf31832a1262c555f41171e9909554f3cb39421666ab14c7a0810b479aaa666c8050263d01b54d427498a23d59f65410a55d97bb285932038f0a0f4c11b9b9d19d8c980140b8fa6161f54b2362d582d9782d18ac166038a3dd25cbd42cc42569662172c780d1ad3b552d5a70c00012ee996b2c9621e7baa0e58a9dd046a696a5ac69006cbf62b5293740014ee9800000000000
      (by decide) ⟨99, rfl⟩ (by decide +kernel)

  private theorem rb535 : (⟨[⟨3,2,true⟩,⟨5,4,true⟩,⟨11,4,false⟩],165,2⟩ : Box).Closed :=
    replayCloses (.cons rb534 (.nil))
      16 245 0x4e6e802899dfc80a002a317f3148da46a50b25e80146565a9191dd2768049b9c4ceadd264c000002a35bf314b3f52f3d000a4a86adeacb33400003a2fa00ae67fe4345d3a3f3f325e807214d6cdae2f4032852b49d8e980000719f4015cf7fc88acf583838ed0000fdf40141cffe4054f40141b7fe465da10a5ea4c400a00f1e802824ffc8000000
      (by decide) ⟨82, rfl⟩ (by decide +kernel)
end

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
mutual
  private theorem rb536 : (⟨[⟨3,2,true⟩,⟨5,4,true⟩,⟨11,4,false⟩],151,2⟩ : Box).Closed :=
    replayCloses (.cons rb535 (.nil))
      14 221 0x9d50b0bc30b244c0231a5af518000005650df986db4b5eb12300a52dd0bcf401ae59a86c9d5b4ed0000004afba00a4a47f91b5e95bbc26000c89e802991bfc88c5eb4a58f00052a0717820000014cbefcc0da6a87add2400539aa6368c2eed3b40000987e80289effe40995aba7e71ba00001227a00a246ff2000
      (by decide) ⟨75, rfl⟩ (by decide +kernel)

  private theorem rb537 : (⟨[⟨3,2,true⟩,⟨5,4,true⟩,⟨11,3,false⟩],137,2⟩ : Box).Closed :=
    replayCloses (.cons rb536 (.nil))
      16 186 0x1400524ff33fc366e1493ff8ff3014cf7f07f821adcd371b9dcef8e9d3002549ea4ef19d8bd7bf5295e4000029d786fcc0500156ba1fcc05001497e97f980a04f5ba00a13eefe4050015bbd3f9853660d2f0980141573740155677f20282b4fd005155ffe4051962f4015971ff200028
      (by decide) ⟨68, rfl⟩ (by decide +kernel)

  private theorem rb538 : (⟨[⟨3,2,true⟩,⟨5,4,true⟩,⟨11,2,true⟩],173,2⟩ : Box).Closed :=
    replayCloses (.nil)
      26 279 0xa69642162800a197297a680000141c3f983a9baa4480001419df98e5a87af6d00000a096fcc0052fbfcc45e5b1e930011df401483ff9194255af4400427a00a437f90552b5ebd46002abe80290bff2169f4014aeff9156a858a163c800b774014a0ff210ee80293efe42edd0052bdfc845ba00a4bbf90014a37e60aa54a60020dd0052adfc800000000000
      (by decide) ⟨86, rfl⟩ (by decide +kernel)

  private theorem rb539 : (⟨[⟨3,2,true⟩,⟨5,4,true⟩,⟨11,2,true⟩],129,2⟩ : Box).Closed :=
    replayCloses (.cons rb538 (.nil))
      21 301 0x1172849439a4f2000d53d0050db7fe41d69fa1bd172f3131ea4fd0d1b85758bf980a679ff44838b14ba93b400a000a8b4ff980a002a2aefd1add301512df82005050bfcc0014cf3feee3d3015cc7f0400a8a5fcc11d3d00544bff9116be802a32ffc8002a387f30b9af5e9a01d4f05ac6201b76adebc260000005775fe62ac5284a80218de59e93000ecdd00574efe472aa97ac5e80652bb5b800000a0fdfe600000000
      (by decide) ⟨64, rfl⟩ (by decide +kernel)

  private theorem rb540 : (⟨[⟨3,2,true⟩,⟨5,4,false⟩,⟨11,2,true⟩],125,2⟩ : Box).Closed :=
    replayCloses (.cons rb539 (.cons rb525 (.nil)))
      23 312 0x70503136a16b4b2f4063035a4d5a30b6617742d2a980026ebc07071a7900069df9ba00a69df3bf90005326fe7f3000530ef73f9861de4fd00530ef9ffe40376f8bd005376fc7fc80a002983783f98b5e27d0055afdbfe400051af6bfcc050bbb3d0052ec1ff21312370e2f40290b4c50a1268c0e7281f552ab699a06d03034b550ea8d67680000106a7a00a83b7fe4106bba00a8303fc80a394bd005737ffc8000a01dd9e8028760ff900050edaff305989e84a1567d7f980a8307fc100
      (by decide) ⟨62, rfl⟩ (by decide +kernel)

  private theorem rb541 : (⟨[⟨3,2,true⟩,⟨5,2,true⟩,⟨11,3,false⟩],101,2⟩ : Box).Closed :=
    replayCloses (.nil)
      15 183 0xc54b79e801461e58c7be8000371e812627fe40195a6943c343a58000004988fe62aa54a11a0050024d07f30d4ac1aab1ca0000dfba049a4ff200b14a9dc32780db1ea794c000067dd024c47f90d5bae583553079e68b162dd040280000
      (by decide) ⟨50, rfl⟩ (by decide +kernel)

  private theorem rb542 : (⟨[⟨3,2,true⟩,⟨5,3,false⟩,⟨11,2,false⟩],101,2⟩ : Box).Closed :=
    replayCloses (.cons rb540 (.cons rb537 (.cons rb533 (.nil))))
      37 229 0x13adc42fce2db74fd0119f98af2303e5c1cd7fb15e8014001a64fad678b1bcdd6c2898014006d0f285b593fbe7f7ee5a5ba03d09abb399f67e9cf6144c0e3aed2e6fd5dd7a4ecdbd97a0000000026bba00a1303fc80a00284eb7e602800a7b67f30140053d4df98516bf44ca93b400a000ae3a3f98063fbe80298f3ff90141d9dd0051dfdfc800a00a0000a0
      (by decide) ⟨50, rfl⟩ (by decide +kernel)

  private theorem rb543 : (⟨[⟨3,2,true⟩,⟨5,2,false⟩,⟨11,1,false⟩],91,2⟩ : Box).Closed :=
    replayCloses (.cons rb542 (.cons rb541 (.nil)))
      16 165 0x966ad79901955652c59012000613d024c37f900d87a0499cff2028049bf7e639aedab562c8000dc7d024cc7f9106bab3d4e9346000024c7bf3197b90bc0090024cbbf30ddba049af7f2000000a00
      (by decide) ⟨45, rfl⟩ (by decide +kernel)
end

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
mutual
  private theorem rb544 : (⟨[⟨3,2,true⟩,⟨5,2,false⟩,⟨11,1,false⟩],81,2⟩ : Box).Closed :=
    replayCloses (.cons rb543 (.nil))
      17 187 0xd4d2c74e922602400024a4fe602804905fe62297a868c00ab5534000004966fcd9ba61266dfc1028ab4c09251bda6024656a14aa58e18021ed3a1530000004906fcc251ab4c0001b6fa049bdff9370629373042e58b096afee02800
      (by decide) ⟨40, rfl⟩ (by decide +kernel)

  private theorem rb545 : (⟨[⟨3,4,true⟩,⟨5,2,true⟩,⟨13,1,true⟩],463,2⟩ : Box).Closed :=
    replayCloses (.cons rb518 (.nil))
      18 306 0x656eea6254000480ecff30019ee82a901c1fe6120b5bf04eb27a04baebff20eb47a0aa5d41ff984993bfc12a952b17a6803155cc63f4038ac6af49805257908980000356be88a4d6aff309535ffc102f73d794c002a54a13a0115321130064a8433400002ab5f5164317a2154aad5fe612a76ffb8ea52864c002acee82fd682cc4c48a55477e612a577f714f7479e8001b4d9a54ac69e40000122ba7f80c5e96567fcc244a9fc1000000
      (by decide) ⟨231, rfl⟩ (by decide +kernel)

  private theorem rb546 : (⟨[⟨3,4,true⟩,⟨5,2,true⟩,⟨13,1,true⟩],391,2⟩ : Box).Closed :=
    replayCloses (.cons rb545 (.nil))
      26 470 0x26f83d0249bd4ff2035fe7d0246bf1ff8648d7ffff9849b787fb8f9ef74097ce87f902ce57d0c92cecffcc24e65ffc13b787a04bb6e7f9056eb743255bcdf98488c77f04a59aa97af5244c0004ace6ff3019a5f5c99744ce2fae434376a4869a2c40a46617f984a0e8ff1269f1e812d327fe40a617d6d1bc3501b2ccc46494f8fe612037dfb8bb27a04aeebff20ba9ba0295d6dfcc25542ff04a3f3e812a3c7fe4046cfd01488d7ff9848adfff0404b0e2ff3061b6e80a5875bf309654bfc116d3f4092d5ffe40b52fa2292d8bfcc2497eff046b4d3d78e800094d8bf9826b5f40529b57f984a2d7ff0483bbe812838ffe4107c7a02941f9fe6120a9ffc100dcf40901b7ff21200fafa1a864e1f440dafa0aa4072ffcc24144ff4400000000000
      (by decide) ⟨195, rfl⟩ (by decide +kernel)

  private theorem rb547 : (⟨[⟨3,2,false⟩,⟨5,1,false⟩],13,3⟩ : Box).Closed :=
    replayCloses (.cons rb521 (.cons rb546 (.nil)))
      23 152 0xa2e74a2a244298fcc051afb80281da00aedf5d49a862f326662b544028b3401467c80012e9fffdf983a2f63d025d17a3ff200cdfd1f409066fdfffc3241ddd0ff309335fedfb80004812120a00000
      (by decide) ⟨6, rfl⟩ (by decide +kernel)

  private theorem rb548 : (⟨[⟨3,2,false⟩,⟨7,1,false⟩,⟨17,1,false⟩],19,2⟩ : Box).Closed :=
    replayCloses (.cons rb3 (.nil))
      21 187 0x162ad9bdb404bb50faf3d00210084a5993ebcf40e794b756c7901af3346f58b200565a140000000471e4ebd88980c84aa5ee400843281b543c3ea4b20658a350d6c59022b3c8590398ad62f3d00000840084ab76b7f67717a001e1baf36b63b400000000000
      (by decide) ⟨9, rfl⟩ (by decide +kernel)

  private theorem rb549 : (⟨[⟨3,3,false⟩,⟨7,2,false⟩,⟨13,1,false⟩,⟨23,1,false⟩],25,1⟩ : Box).Closed :=
    replayCloses (.cons rb7 (.nil))
      20 163 0x110ad52f61801091795a13a01567a9de7a061e1ada045a5a87680001081abd52a58b00579ea1ba004204d1b275ec590000a44ce87e80d62f5eab62c80000f66c1e6f2c2f2c2d9da0042000000001c699941664ccd1637504
      (by decide) ⟨12, rfl⟩ (by decide +kernel)

  private theorem rb550 : (⟨[⟨3,2,false⟩,⟨7,1,false⟩],15,3⟩ : Box).Closed :=
    replayCloses (.cons rb548 (.nil))
      28 77 0x14e6e9a1d0e8b92f40e1b278bdec8fc7a5e800a7b72e4f1657d3d3c81b776939ede7adb6fa7659000000000000000
      (by decide) ⟨7, rfl⟩ (by decide +kernel)

  private theorem rb551 : (⟨[⟨3,2,false⟩],7,4⟩ : Box).Closed :=
    replayCloses (.cons rb550 (.cons rb11 (.cons rb549 (.cons rb27 (.cons rb30 (.cons rb64 (.nil)))))))
      23 118 0x1868314c9898ad413821215c801ee56f58b203208400002ac53d00a95ea10a022a990000000000006ab7aadeb16400c40000000
      (by decide) ⟨3, rfl⟩ (by decide +kernel)
end

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
mutual
  private theorem rb552 : (⟨[⟨3,2,true⟩,⟨5,2,false⟩,⟨11,1,false⟩],73,2⟩ : Box).Closed :=
    replayCloses (.cons rb544 (.nil))
      18 246 0x6d5db87cc64c0488bd8b160e22600004e1e81225cff2025b7409127bf911abe81288bff2028012881fcc045fa0482fffc800327a12a4113f9849acfe0814025abf3012d4a8de7a004b2969eb1fa0119bd14a1490000048307f309011dd02417dfc8834b57af3d00e62b6800002a3d01955108e9223f9849af7ee02804897e600
      (by decide) ⟨36, rfl⟩ (by decide +kernel)

  private theorem rb553 : (⟨[⟨3,2,true⟩,⟨5,2,false⟩,⟨11,1,false⟩],55,2⟩ : Box).Closed :=
    replayCloses (.cons rb552 (.nil))
      25 308 0x2863dd09526ddf984b0fc100a19b742549ab7e6122be0801433df87e80a4cf7dcfe6124bf5ffe08456a1d300004bce9ff30900939adfe6018defa02931ddfe6126af7fc13983436698f2000025142fe600640f445267f7e612e9df82051eba04837f206498a1e6280482599a6316401964a36ac4a800000563d024151ff9014024c99fcc05009527bf3009725fcc01d87a12a5d67f98491efc1028048d7e60000
      (by decide) ⟨27, rfl⟩ (by decide +kernel)

  private theorem rb554 : (⟨[⟨3,2,false⟩],5,4⟩ : Box).Closed :=
    replayCloses (.cons rb551 (.cons rb547 (.cons rb553 (.nil))))
      20 154 0x50014309e860a657fe60284fc100a3a744c54408534fcc0569f7001461eee802b0e0ff0c15b41ff3015965ffb80280b1e99e5dc12620520d1fcc24d1ffdc01432df4254994fe61255fc100000a00000
      (by decide) ⟨2, rfl⟩ (by decide +kernel)
end

theorem nineFiveRankedRoot_closed : (⟨[⟨3,2,false⟩],5,4⟩ : Box).Closed :=
  rb554

end OddWeirdSubproblems

open OddWeirdSubproblems

private theorem threeOnceTiny (r : ℕ) (hr : r ≤ 2) :
    (⟨[⟨3, 1, true⟩], 5, r⟩ : Box).Closed := by
  interval_cases r
  all_goals
    apply close_of_upperNum_le (show 1 < 5 by decide)
    decide +kernel

theorem OMA.solution : type_of% @Erdos470.erdos_470.variants.odd_weird_prime_div := by
  apply atLeastSix_of_threeRoots
  · intro r hr
    by_cases hs : r ≤ 2
    · exact threeOnceTiny r hs
    · interval_cases r
      · exact oneFourRootClosed
      · exact oneFiveRootClosed
  · intro r hr
    interval_cases r
    · exact nineSmallComputed0
    · exact nineSmallComputed1
    · exact nineSmallComputed2
    · exact nineFourRootClosed
    · exact nineFiveRankedRoot_closed
