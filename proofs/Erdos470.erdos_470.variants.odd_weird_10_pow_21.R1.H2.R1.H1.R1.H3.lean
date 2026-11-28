import OMAReductions.R_Erdos470_erdos_470_variants_odd_weird_10_pow_21_R1_H2_R1_H1_R1
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

def replayWithCuts (witness : ℕ → List ℕ) (cut : Box → Bool) : ℕ → Box → Bool
  | 0, _ => false
  | fuel + 1, b =>
    if cut b then true
    else if 2 * number b.minimum ≤ divisorSum b.minimum then minimumOk witness b
    else if b.upperNum ≤ 2 * b.upperDen then true
    else match (chooseSlot b).bind (fun i => b.slots[i]?.map (fun s => (i, s))) with
    | some (i, s) =>
      if s.fixed then false else
      replayWithCuts witness cut fuel {b with slots := b.slots.set i {s with fixed := true}} &&
      replayWithCuts witness cut fuel {b with slots := b.slots.set i {s with exponent := s.exponent + 1}}
    | none =>
      match b.remaining with
      | 0 => false
      | r + 1 =>
        replayWithCuts witness cut fuel ⟨b.slots, b.next + 2, r + 1⟩ &&
        if b.next.minFac = b.next then
          replayWithCuts witness cut fuel ⟨b.slots ++ [⟨b.next, 1, false⟩], b.next + 2, r⟩
        else true

theorem replayWithCuts_closes {witness : ℕ → List ℕ} {cut : Box → Bool} {fuel : ℕ} {b : Box}
    (hcut : ∀ box, cut box = true → box.Closed)
    (hlo : 1 < b.next) (hodd : Odd b.next) (h : replayWithCuts witness cut fuel b = true) :
    b.Closed := by
  induction fuel generalizing b with
  | zero => simp [replayWithCuts] at h
  | succ fuel ih =>
    rw [replayWithCuts] at h
    split at h
    · exact hcut b ‹_›
    split at h
    · exact minimumOk_closes ‹_› h
    split at h
    · exact close_of_upperNum_le hlo ‹_›
    split at h
    next i s hs =>
      have hi : b.slots[i]? = some s := by
        obtain ⟨j, _, hj⟩ := Option.bind_eq_some_iff.mp hs
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

end OddWeirdSubproblems

namespace OddWeirdSubproblems

open scoped BigOperators

/-- The prime factorization of `n` as an increasing list of prime and exponent pairs. -/
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

theorem primeCoordinates_sigma {n : ℕ} (hn : n ≠ 0) :
    ((primeCoordinates n).map (fun x => ∑ i ∈ Finset.range (x.2 + 1), x.1 ^ i)).prod =
      ArithmeticFunction.sigma 1 n := by
  rw [primeCoordinates_prod_map,
    ArithmeticFunction.sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul hn]
  simp

/-- A nonzero natural number has an exact increasing coordinate list for its
prime powers and divisor sum. When the number is odd, so is every row prime. -/
theorem exists_primeCoordinates {n : ℕ} (hn : n ≠ 0) :
    ∃ xs : List (ℕ × ℕ),
      xs.Pairwise (fun x y => x.1 < y.1) ∧
      (∀ x ∈ xs, x.1.Prime ∧ 0 < x.2 ∧ (Odd n → Odd x.1)) ∧
      xs.length = n.primeFactors.card ∧
      (xs.map (fun x => x.1 ^ x.2)).prod = n ∧
      (xs.map (fun x => ∑ i ∈ Finset.range (x.2 + 1), x.1 ^ i)).prod =
        ArithmeticFunction.sigma 1 n := by
  refine ⟨primeCoordinates n, primeCoordinates_pairwise n, ?_,
    primeCoordinates_length n, primeCoordinates_prod hn, primeCoordinates_sigma hn⟩
  intro x hx
  exact ⟨(primeCoordinates_prime_pos hx).1, (primeCoordinates_prime_pos hx).2,
    fun ho => primeCoordinates_odd ho hx⟩

/-- The first two coordinates in the branch with exact valuation one at three
and a factor of five. All remaining coordinates start at seven. -/
theorem primeCoordinates_three_one_five {n : ℕ} (hodd : Odd n)
    (hthree : n.factorization 3 = 1) (hfive : 5 ∣ n) :
    ∃ xs : List (ℕ × ℕ), primeCoordinates n = (3, 1) :: (5, n.factorization 5) :: xs ∧
      0 < n.factorization 5 ∧ ∀ x ∈ xs, 7 ≤ x.1 := by
  have hn : n ≠ 0 := by
    rcases hodd with ⟨k, hk⟩
    omega
  have h3 : 3 ∈ n.primeFactors := by
    rw [← Nat.support_factorization, Finsupp.mem_support_iff, hthree]
    decide
  have h5 : 5 ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨by decide, hfive, hn⟩
  have h5' : 5 ∈ n.primeFactors.erase 3 := Finset.mem_erase.mpr ⟨by decide, h5⟩
  let tail := (n.primeFactors.erase 3).erase 5
  have htail (p : ℕ) (hp : p ∈ tail) : 7 ≤ p := by
    have ⟨hp5, hp'⟩ := Finset.mem_erase.mp hp
    have ⟨hp3, hp''⟩ := Finset.mem_erase.mp hp'
    have hp1 := (Nat.prime_of_mem_primeFactors hp'').one_lt
    obtain ⟨k, hk⟩ := hodd.of_dvd_nat (Nat.dvd_of_mem_primeFactors hp'')
    omega
  have h3bound : ∀ p ∈ insert 5 tail, 3 ≤ p := by
    intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · decide
    · exact (by decide : 3 ≤ 7).trans (htail p hp)
  have h5bound : ∀ p ∈ tail, 5 ≤ p := fun p hp => (by decide : 5 ≤ 7).trans (htail p hp)
  have hn3 : 3 ∉ insert 5 tail := by
    intro h
    rcases Finset.mem_insert.mp h with h | h
    · contradiction
    · have := htail 3 h
      omega
  have hn5 : 5 ∉ tail := by
    intro h
    exact (Finset.mem_erase.mp h).1 rfl
  have hfac : n.primeFactors = insert 3 (insert 5 tail) := by
    rw [show insert 5 tail = n.primeFactors.erase 3 from Finset.insert_erase h5',
      Finset.insert_erase h3]
  refine ⟨tail.sort.map (fun p => (p, n.factorization p)), ?_,
    Nat.Prime.factorization_pos_of_dvd (by decide) hn hfive, ?_⟩
  · rw [primeCoordinates, hfac, Finset.sort_insert (· ≤ ·) h3bound hn3,
      Finset.sort_insert (· ≤ ·) h5bound hn5]
    simp [hthree]
  · intro x hx
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
    exact htail p ((Finset.mem_sort (· ≤ ·)).mp hp)

/-- The ordered prime coordinates of an odd multiple of three begin with
the exact valuation at three. -/
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

/-- The product of the least possible distinct odd primes after the slots. -/
def tailMinimum : ℕ → ℕ → ℕ
  | _, 0 => 1
  | p, r + 1 => p * tailMinimum (p + 2) r

theorem tailMinimum_mono {p q : ℕ} (hpq : p ≤ q) (r : ℕ) :
    tailMinimum p r ≤ tailMinimum q r := by
  induction r generalizing p q with
  | zero => simp [tailMinimum]
  | succ r ih => exact Nat.mul_le_mul hpq (ih (by omega))

theorem tailMinimum_le_number {ys : Coordinates} {p : ℕ} (h : TailFits p ys) :
    tailMinimum p ys.length ≤ number ys := by
  induction ys generalizing p with
  | nil => simp [tailMinimum, number]
  | cons y ys ih =>
    obtain ⟨q, e⟩ := y
    obtain ⟨hpq, _, hprime, _, he, ht⟩ := h
    rw [number_cons]
    simp only [List.length_cons, tailMinimum]
    refine Nat.mul_le_mul (hpq.trans ?_) ?_
    · simpa using (Nat.pow_le_pow_right hprime.pos (show 1 ≤ e by omega))
    · exact (tailMinimum_mono (show p + 2 ≤ q + 2 by omega) _).trans (ih ht)

def Box.ClosedBelow (b : Box) (B : ℕ) : Prop :=
  ∀ xs ys, b.Matches xs ys → PrimeCoordinates (xs ++ ys) →
    number (xs ++ ys) < B → (number (xs ++ ys)).Weird →
    (∀ d ∈ (number (xs ++ ys)).properDivisors, d.Deficient) → False

theorem closeBelow_of_minimum_ge {b : Box} {B : ℕ}
    (hB : B ≤ number b.minimum * tailMinimum b.next b.remaining) :
    b.ClosedBelow B := by
  intro xs ys ⟨hf, ht, hy⟩ hcoord hlt hw _
  have hxpos : 0 < number xs := number_pos (primeCoordinates_left hcoord).1
  have hx : number b.minimum ≤ number xs := Nat.le_of_dvd hxpos (minimum_dvd hf)
  have hy' := tailMinimum_le_number ht
  rw [hy] at hy'
  rw [number_append] at hlt
  exact hlt.not_ge (hB.trans (Nat.mul_le_mul hx hy'))

theorem closedBelow_of_closed {b : Box} (h : b.Closed) (B : ℕ) : b.ClosedBelow B :=
  fun xs ys hm hv _ hw hp => h xs ys hm hv hw hp

/-- A root with no fixed coordinates covers every odd integer of the given
support, and the lower product bound rules out sufficiently long supports. -/
theorem noPrimitiveWeirdBelow_of_roots {B k : ℕ}
    (hsize : B ≤ tailMinimum 3 (k + 1))
    (hroots : ∀ r ≤ k, (⟨[], 3, r⟩ : Box).ClosedBelow B)
    {n : ℕ} (hn : n < B) (ho : Odd n) (hw : n.Weird)
    (hproper : ∀ d ∈ n.properDivisors, d.Deficient) : False := by
  obtain ⟨ys, horder, hprime, _, hprod, _⟩ := exists_primeCoordinates ho.pos.ne'
  have hlocal (x : ℕ × ℕ) (hx : x ∈ ys) : x.1.Prime ∧ Odd x.1 ∧ 0 < x.2 :=
    ⟨(hprime x hx).1, (hprime x hx).2.2 ho, (hprime x hx).2.1⟩
  have ht : TailFits 3 ys := by
    apply tailFits_of_sorted (by decide : 2 < 3) _ hlocal horder
    intro x hx
    have hp := ((hlocal x hx).1.one_lt)
    obtain ⟨a, ha⟩ := (hlocal x hx).2.1
    omega
  have heq : number ys = n := hprod
  have hlength : ys.length ≤ k := by
    by_contra! hl
    have hmono : ∀ s t : ℕ, s ≤ t → ∀ p : ℕ, 0 < p →
        tailMinimum p s ≤ tailMinimum p t := by
      intro s t h
      induction h with
      | refl => intros; rfl
      | @step t h ih =>
        intro p hp
        exact (ih p hp).trans (by
          rw [tailMinimum]
          exact (tailMinimum_mono (show p ≤ p + 2 by omega) t).trans
            (Nat.le_mul_of_pos_left _ hp))
    have hh := hsize.trans ((hmono _ _ (by omega) 3 (by decide)).trans
      (tailMinimum_le_number ht))
    omega
  exact hroots ys.length hlength [] ys ⟨.nil, ht, rfl⟩
    ⟨fun x hx => (hprime x hx).1, horder⟩ (heq.symm ▸ hn)
    (heq.symm ▸ hw) (heq.symm ▸ hproper)

def replayBelow (B : ℕ) (witness : ℕ → List ℕ) : ℕ → Box → Bool
  | 0, _ => false
  | fuel + 1, b =>
    if B ≤ number b.minimum * tailMinimum b.next b.remaining then true
    else if 2 * number b.minimum ≤ divisorSum b.minimum then minimumOk witness b
    else if b.upperNum ≤ 2 * b.upperDen then true
    else match (chooseSlot b).bind (fun i => b.slots[i]?.map (fun s => (i, s))) with
    | some (i, s) =>
      if s.fixed then false else
      replayBelow B witness fuel {b with slots := b.slots.set i {s with fixed := true}} &&
      replayBelow B witness fuel {b with slots := b.slots.set i {s with exponent := s.exponent + 1}}
    | none =>
      match b.remaining with
      | 0 => false
      | r + 1 =>
        replayBelow B witness fuel ⟨b.slots, b.next + 2, r + 1⟩ &&
        if b.next.minFac = b.next then
          replayBelow B witness fuel ⟨b.slots ++ [⟨b.next, 1, false⟩], b.next + 2, r⟩
        else true

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

theorem replayBelow_closes {B : ℕ} {witness : ℕ → List ℕ} {fuel : ℕ} {b : Box}
    (hlo : 1 < b.next) (hodd : Odd b.next) (h : replayBelow B witness fuel b = true) :
    b.ClosedBelow B := by
  induction fuel generalizing b with
  | zero => simp [replayBelow] at h
  | succ fuel ih =>
    rw [replayBelow] at h
    split at h
    · exact closeBelow_of_minimum_ge ‹_›
    split at h
    · exact closedBelow_of_closed (minimumOk_closes ‹_› h) B
    split at h
    · exact closedBelow_of_closed (close_of_upperNum_le hlo ‹_›) B
    split at h
    next i s hs =>
      have hi : b.slots[i]? = some s := by
        obtain ⟨j, _, hj⟩ := Option.bind_eq_some_iff.mp hs
        cases hg : b.slots[j]? <;> simp_all
      split at h
      · contradiction
      · have hf : s.fixed = false := by simp_all
        obtain ⟨h₁, h₂⟩ := Bool.and_eq_true_iff.mp h
        exact closeBelow_split_slot hi hf (ih hlo hodd h₁) (ih hlo hodd h₂)
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
        apply closeBelow_split_next hodd (ih hlo' hodd' hskip)
        intro hp
        exact ih hlo' hodd' (by simpa only [if_pos hp.minFac_eq] using htake)

end OddWeirdSubproblems

namespace OddWeirdSubproblems

/-- A rank list specifies a lower bound for each initial prime coordinate.
When fewer coordinates occur, the unused lower bounds have no effect. -/
def RankFloor : List ℕ → Coordinates → Prop
  | [], _ => True
  | _ :: _, [] => True
  | p :: ps, x :: xs => p ≤ x.1 ∧ RankFloor ps xs

def gapOk (lo hi : ℕ) : Bool :=
  (List.range (hi - lo)).all (fun j => decide ((lo + j).minFac ≠ lo + j))

def floorSteps : List ℕ → Bool
  | p :: q :: ps => gapOk (p + 2) q && floorSteps (q :: ps)
  | _ => true

theorem no_prime_of_gapOk {lo hi q : ℕ} (h : gapOk lo hi = true)
    (hlo : lo ≤ q) (hhi : q < hi) (hp : q.Prime) : False := by
  simp only [gapOk, List.all_eq_true, decide_eq_true_eq] at h
  have hn := h (q - lo) (List.mem_range.mpr (by omega))
  rw [show lo + (q - lo) = q by omega] at hn
  exact hn hp.minFac_eq

theorem tailFits_weaken {p q : ℕ} {xs : Coordinates} (hp : p ≤ q) (h : TailFits q xs) :
    TailFits p xs := by
  cases xs with
  | nil => trivial
  | cons x xs =>
    obtain ⟨r, e⟩ := x
    obtain ⟨hlo, hpos, hprime, hodd, he, ht⟩ := h
    exact ⟨hp.trans hlo, hpos, hprime, hodd, he, ht⟩

theorem tailFits_gap {p q : ℕ} {xs : Coordinates} (h : gapOk p q = true) (ht : TailFits p xs) :
    TailFits q xs := by
  cases xs with
  | nil => trivial
  | cons x xs =>
    obtain ⟨r, e⟩ := x
    obtain ⟨hlo, hpos, hprime, hodd, he, hx⟩ := ht
    have hq : q ≤ r := Nat.le_of_not_gt fun hlt => no_prime_of_gapOk h hlo hlt hprime
    exact ⟨hq, hpos, hprime, hodd, he, hx⟩

theorem rankFloor_of_steps {p : ℕ} {ps : List ℕ} {xs : Coordinates}
    (hsteps : floorSteps (p :: ps) = true) (ht : TailFits p xs) : RankFloor (p :: ps) xs := by
  induction ps generalizing p xs with
  | nil =>
    cases xs with
    | nil => trivial
    | cons x xs =>
      obtain ⟨q, e⟩ := x
      exact ⟨ht.1, trivial⟩
  | cons r ps ih =>
    cases xs with
    | nil => trivial
    | cons x xs =>
      obtain ⟨q, e⟩ := x
      obtain ⟨hpq, _, _, _, _, ht⟩ := ht
      obtain ⟨hg, hnext⟩ := Bool.and_eq_true_iff.mp hsteps
      refine ⟨hpq, ih hnext ?_⟩
      exact tailFits_gap hg (tailFits_weaken (by omega : p + 2 ≤ q + 2) ht)

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

private def roughFloors : List ℕ := [7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59]

/-- Fang's two starting primes are sufficient below 10^21. The bound uses
the smallest possible ordered support and the limiting prime-power indices. -/
theorem smallOddAbundant_has_three_or_five {n : ℕ} (hn : n < 10 ^ 21)
    (ho : Odd n) (ha : n.Abundant) : 3 ∣ n ∨ 5 ∣ n := by
  by_contra! h
  obtain ⟨xs, horder, hcoord, _, hprod, _⟩ := exists_primeCoordinates ho.pos.ne'
  have hnumber : number xs = n := hprod
  have ht : TailFits 7 xs := by
    apply tailFits_of_sorted (by decide : 2 < 7) _ _ horder
    · intro x hx
      have hprime := (hcoord x hx).1
      have ho' := (hcoord x hx).2.2 ho
      have hd : x.1 ∣ n := by
        have hpow : x.1 ^ x.2 ∣ number xs := by
          apply List.dvd_prod (List.mem_map.mpr ⟨x, hx, rfl⟩)
        have he := (hcoord x hx).2.1
        exact (dvd_pow_self _ he.ne').trans (hnumber ▸ hpow)
      have h3 : x.1 ≠ 3 := fun eq => h.1 (eq ▸ hd)
      have h5 : x.1 ≠ 5 := fun eq => h.2 (eq ▸ hd)
      have hp := hprime.one_lt
      obtain ⟨k, hk⟩ := ho'
      omega
    · intro x hx
      obtain ⟨hp, he, hodd⟩ := hcoord x hx
      exact ⟨hp, hodd ho, he⟩
  have hlen : xs.length ≤ roughFloors.length := by
    by_contra! hl
    have hr : RankFloor (roughFloors ++ [61]) xs :=
      rankFloor_of_steps (by decide +kernel) ht
    have hb := number_ge_floor_product hr (by simp; omega) (fun x hx =>
      ⟨(hcoord x hx).1, (hcoord x hx).2.1⟩)
    have hh : 10 ^ 21 ≤ (roughFloors ++ [61]).prod := by decide +kernel
    rw [hnumber] at hb
    omega
  have hr : RankFloor roughFloors xs := rankFloor_of_steps (by decide +kernel) ht
  have hbound := floorIndex_upper hr hlen (by
    intro p hp
    simp only [roughFloors, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide)
  have hrat : (roughFloors.map limitingIndex).prod < 2 := by decide +kernel
  rw [coordinate_index_eq, divisorSum_eq ⟨fun x hx => (hcoord x hx).1, horder⟩,
    hnumber, ← Nat.abundancyIndex] at hbound
  exact (Nat.abundant_iff_two_lt_abundancyIndex.mp ha).not_ge (hbound.trans hrat.le)

theorem support_lt_of_floor_product {p B n : ℕ} {ps : List ℕ}
    (hn : n < B) (ho : Odd n) (hp : 2 < p)
    (hfloor : ∀ q ∈ n.primeFactors, p ≤ q)
    (hsteps : floorSteps (p :: ps) = true)
    (hprod : B ≤ (p :: ps).prod) :
    n.primeFactors.card < (p :: ps).length := by
  let xs := primeCoordinates n
  have hlocal (x : ℕ × ℕ) (hx : x ∈ xs) : x.1.Prime ∧ Odd x.1 ∧ 0 < x.2 := by
    have h := primeCoordinates_prime_pos hx
    exact ⟨h.1, primeCoordinates_odd ho hx, h.2⟩
  have ht : TailFits p xs := by
    apply tailFits_of_sorted hp _ hlocal (primeCoordinates_pairwise n)
    intro x hx
    obtain ⟨q, e⟩ := x
    exact hfloor q (mem_primeCoordinates.mp hx).1
  have hr := rankFloor_of_steps hsteps ht
  have hlen : xs.length = n.primeFactors.card := primeCoordinates_length n
  have heq : number xs = n := primeCoordinates_prod ho.pos.ne'
  by_contra! hc
  have h := number_ge_floor_product hr (by omega) (fun x hx =>
    ⟨(hlocal x hx).1, (hlocal x hx).2.2⟩)
  omega

private def floorTo61 : List ℕ := 5 :: roughFloors ++ [61]

theorem oddBelow10Pow21_primeFactors_card_le_sixteen {n : ℕ}
    (hn : n < 10 ^ 21) (ho : Odd n) : n.primeFactors.card ≤ 16 := by
  have hf (q : ℕ) (hq : q ∈ n.primeFactors) : 3 ≤ q := by
    have hprime := Nat.prime_of_mem_primeFactors hq
    obtain ⟨k, hk⟩ := ho.of_dvd_nat (Nat.dvd_of_mem_primeFactors hq)
    have hmin := hprime.one_lt
    omega
  have h := support_lt_of_floor_product (ps := floorTo61) hn ho (by decide) hf
    (by decide +kernel) (by decide +kernel)
  have h17 : n.primeFactors.card < 17 := by simpa [floorTo61, roughFloors] using h
  omega

theorem coprimeThreeOddBelow10Pow21_primeFactors_card_le_fifteen {n : ℕ}
    (hn : n < 10 ^ 21) (ho : Odd n) (h3 : ¬ 3 ∣ n) : n.primeFactors.card ≤ 15 := by
  have hf (q : ℕ) (hq : q ∈ n.primeFactors) : 5 ≤ q := by
    have hprime := Nat.prime_of_mem_primeFactors hq
    have hd := Nat.dvd_of_mem_primeFactors hq
    obtain ⟨k, hk⟩ := ho.of_dvd_nat hd
    have hmin := hprime.one_lt
    have hneq : q ≠ 3 := fun heq => h3 (heq ▸ hd)
    omega
  have h := support_lt_of_floor_product (ps := roughFloors ++ [61]) hn ho (by decide) hf
    (by decide +kernel) (by decide +kernel)
  have h16 : n.primeFactors.card < 16 := by simpa [roughFloors] using h
  omega

theorem coprimeThree_oddAbundant_primeFactors_card_ge_seven {n : ℕ} (ho : Odd n)
    (ha : n.Abundant) (h3 : ¬ 3 ∣ n) : 7 ≤ n.primeFactors.card := by
  by_contra! hc
  let xs := primeCoordinates n
  have hlocal (x : ℕ × ℕ) (hx : x ∈ xs) : x.1.Prime ∧ Odd x.1 ∧ 0 < x.2 := by
    have h := primeCoordinates_prime_pos hx
    exact ⟨h.1, primeCoordinates_odd ho hx, h.2⟩
  have ht : TailFits 5 xs := by
    apply tailFits_of_sorted (by decide : 2 < 5) _ hlocal (primeCoordinates_pairwise n)
    intro x hx
    obtain ⟨p, e⟩ := x
    have hd := Nat.dvd_of_mem_primeFactors (mem_primeCoordinates.mp hx).1
    have hp : p ≠ 3 := fun heq => h3 (heq ▸ hd)
    have hlo := (hlocal (p, e) hx).1.one_lt
    obtain ⟨a, ha⟩ := (hlocal (p, e) hx).2.1
    omega
  have hf : RankFloor [5, 7, 11, 13, 17, 19] xs :=
    rankFloor_of_steps (by decide +kernel) ht
  have hlen : xs.length ≤ 6 := by
    have h := primeCoordinates_length n
    change xs.length = n.primeFactors.card at h
    omega
  have h := floorIndex_upper hf hlen (by
    intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  have he : number xs = n := primeCoordinates_prod ho.pos.ne'
  rw [coordinate_index_eq, divisorSum_eq ⟨fun x hx => (hlocal x hx).1,
    primeCoordinates_pairwise n⟩, he, ← Nat.abundancyIndex] at h
  have hlt : ([5, 7, 11, 13, 17, 19].map limitingIndex).prod < 2 := by decide +kernel
  exact (Nat.abundant_iff_two_lt_abundancyIndex.mp ha).not_ge (h.trans hlt.le)

/-- Exact ranked bound using the five smallest permitted prime divisors. -/
theorem oddCoprimeThreeAtMostFive_abundancyIndex_le {n : ℕ} (ho : Odd n)
    (h3 : ¬ 3 ∣ n) (hc : n.primeFactors.card ≤ 5) :
    n.abundancyIndex ≤ (5 / 4) * (7 / 6) * (11 / 10) * (13 / 12) * (17 / 16) := by
  let xs := primeCoordinates n
  have hlocal (x : ℕ × ℕ) (hx : x ∈ xs) : x.1.Prime ∧ Odd x.1 ∧ 0 < x.2 := by
    have h := primeCoordinates_prime_pos hx
    exact ⟨h.1, primeCoordinates_odd ho hx, h.2⟩
  have ht : TailFits 5 xs := by
    apply tailFits_of_sorted (by decide : 2 < 5) _ hlocal (primeCoordinates_pairwise n)
    intro x hx
    obtain ⟨p, e⟩ := x
    have hd := Nat.dvd_of_mem_primeFactors (mem_primeCoordinates.mp hx).1
    have hp : p ≠ 3 := fun heq => h3 (heq ▸ hd)
    have hlo := (hlocal (p, e) hx).1.one_lt
    obtain ⟨a, ha⟩ := (hlocal (p, e) hx).2.1
    omega
  have hf : RankFloor [5, 7, 11, 13, 17] xs :=
    rankFloor_of_steps (by decide +kernel) ht
  have hlen : xs.length ≤ 5 := (primeCoordinates_length n).symm ▸ hc
  have h := floorIndex_upper hf hlen (by
    intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl <;> decide)
  have he : number xs = n := primeCoordinates_prod ho.pos.ne'
  rw [coordinate_index_eq, divisorSum_eq ⟨fun x hx => (hlocal x hx).1,
    primeCoordinates_pairwise n⟩, he, ← Nat.abundancyIndex] at h
  exact h.trans (by decide +kernel)

end OddWeirdSubproblems

namespace OddWeirdSubproblems

open Finset

/-- Scaling a representing subset preserves distinctness and proper divisibility. -/
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

/-- Choose the least nondeficient divisor. A perfect divisor already gives a
pseudoperfect representation, so the selected divisor is weird and primitive.
The relation `d ∣ n` lets callers transfer their own restrictions. -/
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

/-- The target's set cardinality counts precisely the distinct prime factors. -/
theorem primeDivisorNcard (n : ℕ) :
    {p : ℕ | p ∈ n.divisors ∧ p.Prime}.ncard = n.primeFactors.card := by
  have hs : {p : ℕ | p ∈ n.divisors ∧ p.Prime} = (n.primeFactors : Set ℕ) := by
    ext p
    simp only [Set.mem_ofPred_eq, Finset.mem_coe, Nat.mem_primeFactors, Nat.mem_divisors]
    tauto
  rw [hs, Set.ncard_coe_finset]

/-- A primitive-abundant exclusion through five distinct primes suffices for
the first Erdős 470 variant. -/
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

/-- The strict cutoff also passes to the primitive divisor. -/
theorem noOddWeirdBelowOfPrimitive {B : ℕ}
    (verify : ∀ m < B, Odd m → m.Abundant →
      (∀ d ∈ m.properDivisors, d.Deficient) → m.Pseudoperfect) :
    ∀ n < B, Odd n → ¬ n.Weird := by
  intro n hn ho hw
  obtain ⟨d, hd, hdw, hproper⟩ := primitiveWeirdDivisor hw
  have hlt := (Nat.le_of_dvd hw.1.pos hd).trans_lt hn
  exact hdw.2 (verify d hlt (ho.of_dvd_nat hd) hdw.1 hproper)

end OddWeirdSubproblems

namespace OddWeirdSubproblems

/-- Start sorted coordinates at a known least prime divisor. -/
theorem primeCoordinates_start {n p : ℕ} (hm : p ∈ n.primeFactors)
    (hp : ∀ q ∈ n.primeFactors, p ≤ q) :
    ∃ xs, primeCoordinates n = (p, n.factorization p) :: xs := by
  let rest := n.primeFactors.erase p
  have hlo : ∀ q ∈ rest, p ≤ q := fun q hq => hp q (Finset.mem_erase.mp hq).2
  have hnot : p ∉ rest := Finset.notMem_erase _ _
  refine ⟨rest.sort.map (fun q => (q, n.factorization q)), ?_⟩
  rw [primeCoordinates, ← Finset.insert_erase hm, Finset.sort_insert (· ≤ ·) hlo hnot]
  rfl

theorem fangRoots_cover {n : ℕ} (hn : n < 10 ^ 21) (ho : Odd n) (ha : n.Abundant) :
    ∃ p a ys, (p = 3 ∨ p = 5) ∧
      primeCoordinates n = [(p, a)] ++ ys ∧
      Slot.Fits ⟨p, 1, false⟩ (p, a) ∧ TailFits (p + 2) ys ∧
      ys.length + 1 = n.primeFactors.card := by
  have h35 := smallOddAbundant_has_three_or_five hn ho ha
  let p := if 3 ∣ n then 3 else 5
  have hp : p = 3 ∨ p = 5 := by unfold p; split <;> simp
  have hprime : p.Prime := by
    rcases hp with h | h <;> rw [h] <;> decide
  have hd : p ∣ n := by
    unfold p
    split <;> rename_i h
    · exact h
    · exact h35.resolve_left h
  have hm : p ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨hprime, hd, ho.pos.ne'⟩
  have hleast (q : ℕ) (hq : q ∈ n.primeFactors) : p ≤ q := by
    have hqprime := Nat.prime_of_mem_primeFactors hq
    have hqd := Nat.dvd_of_mem_primeFactors hq
    have hmin := hqprime.one_lt
    obtain ⟨i, hi⟩ := ho.of_dvd_nat hqd
    unfold p
    split <;> rename_i h
    · omega
    · have hne : q ≠ 3 := fun he => h (he ▸ hqd)
      omega
  obtain ⟨ys, heq⟩ := primeCoordinates_start hm hleast
  let a := n.factorization p
  have hlen : ys.length + 1 = n.primeFactors.card := by
    have h := primeCoordinates_length n
    rw [heq, List.length_cons] at h
    exact h
  have hpw := primeCoordinates_pairwise n
  rw [heq, List.pairwise_cons] at hpw
  have hx (x : ℕ × ℕ) (hx : x ∈ ys) : x ∈ primeCoordinates n := by
    rw [heq]
    exact List.mem_cons_of_mem _ hx
  have hpo : Odd p := ho.of_dvd_nat hd
  have htail : TailFits (p + 2) ys := by
    apply tailFits_of_sorted (by omega : 2 < p + 2) _ _ hpw.2
    · intro x h
      have hq := hpw.1 x h
      obtain ⟨i, hi⟩ := hpo
      obtain ⟨j, hj⟩ := primeCoordinates_odd ho (hx x h)
      change p < x.1 at hq
      omega
    · intro x h
      have h' := primeCoordinates_prime_pos (hx x h)
      exact ⟨h'.1, primeCoordinates_odd ho (hx x h), h'.2⟩
  exact ⟨p, a, ys, hp, heq, ⟨hprime, rfl,
    hprime.factorization_pos_of_dvd ho.pos.ne' hd, by simp⟩, htail, hlen⟩

/-- A bounded root at five discharges its matching support and exponent range. -/
theorem noPrimitiveWeird10Pow21_coprimeThree_of_exponentRoot {n r e : ℕ} {fixed : Bool}
    (root : (⟨[⟨5, e, fixed⟩], 7, r⟩ : Box).ClosedBelow (10 ^ 21))
    (hn : n < 10 ^ 21) (ho : Odd n) (h3 : ¬ 3 ∣ n)
    (hc : n.primeFactors.card = r + 1)
    (hproper : ∀ d ∈ n.properDivisors, d.Deficient)
    (hlo : e ≤ n.factorization 5) (hfix : fixed = true → e = n.factorization 5) :
    ¬ n.Weird := by
  intro hw
  obtain ⟨p, a, ys, hp, heq, hfit, ht, hlen⟩ := fangRoots_cover hn ho hw.1
  have hlen' : ys.length = r := by omega
  have hp5 : p = 5 := by
    rcases hp with rfl | h
    · have hm : (3, a) ∈ primeCoordinates n := by rw [heq]; simp
      exact (h3 (Nat.dvd_of_mem_primeFactors (mem_primeCoordinates.mp hm).1)).elim
    · exact h
  subst p
  have hnum : number ([(5, a)] ++ ys) = n := by
    rw [← heq]
    exact primeCoordinates_prod ho.pos.ne'
  have hcoords : PrimeCoordinates ([(5, a)] ++ ys) := by
    rw [← heq]
    exact ⟨fun x hx => (primeCoordinates_prime_pos hx).1, primeCoordinates_pairwise n⟩
  have heq5 := (mem_primeCoordinates.mp (show (5, a) ∈ primeCoordinates n by rw [heq]; simp)).2
  have hfit' : Slot.Fits ⟨5, e, fixed⟩ (5, a) := by
    rw [heq5]
    exact ⟨(by decide : (5 : ℕ).Prime), rfl, hlo, hfix⟩
  exact root [(5, a)] ys ⟨.cons hfit' .nil, ht, hlen'⟩ hcoords
    (hnum.symm ▸ hn) (hnum.symm ▸ hw) (hnum.symm ▸ hproper)

/-- A bounded root at five discharges the matching support coprime to three. -/
theorem noPrimitiveWeird10Pow21_coprimeThree_of_root {n r : ℕ}
    (root : (⟨[⟨5, 1, false⟩], 7, r⟩ : Box).ClosedBelow (10 ^ 21))
    (hn : n < 10 ^ 21) (ho : Odd n) (h3 : ¬ 3 ∣ n)
    (hc : n.primeFactors.card = r + 1)
    (hproper : ∀ d ∈ n.properDivisors, d.Deficient) : ¬ n.Weird := by
  intro hw
  have hFive := (smallOddAbundant_has_three_or_five hn ho hw.1).resolve_left h3
  have hlo := (by decide : (5 : ℕ).Prime).factorization_pos_of_dvd ho.pos.ne' hFive
  exact noPrimitiveWeird10Pow21_coprimeThree_of_exponentRoot root hn ho h3 hc hproper hlo
    (by simp) hw

/-- Fang's two starting primes and the support window after proving the first
variant suffice for the bounded exclusion. -/
theorem noOddWeird10Pow21_of_support_and_fangRoots
    (h6 : ∀ n : ℕ, Odd n → n.Weird → 6 ≤ n.primeFactors.card)
    (h3 : ∀ r, 5 ≤ r → r ≤ 15 → (⟨[⟨3, 1, false⟩], 5, r⟩ : Box).ClosedBelow (10 ^ 21))
    (h5 : ∀ r, 6 ≤ r → r ≤ 14 → (⟨[⟨5, 1, false⟩], 7, r⟩ : Box).ClosedBelow (10 ^ 21)) :
    ∀ n < 10 ^ 21, Odd n → ¬ n.Weird := by
  intro n hn ho hw
  obtain ⟨d, hdn, hdw, hproper⟩ := primitiveWeirdDivisor hw
  have hdlt : d < 10 ^ 21 := (Nat.le_of_dvd hw.1.pos hdn).trans_lt hn
  have hdodd : Odd d := ho.of_dvd_nat hdn
  obtain ⟨p, a, ys, hp, heq, hfit, ht, hlen⟩ := fangRoots_cover hdlt hdodd hdw.1
  have hlow := h6 d hdodd hdw
  have hrlow : 5 ≤ ys.length := by omega
  have hnum : number ([(p, a)] ++ ys) = d := by
    rw [← heq]
    exact primeCoordinates_prod hdodd.pos.ne'
  have hcoord : PrimeCoordinates ([(p, a)] ++ ys) := by
    rw [← heq]
    exact ⟨fun x hx => (primeCoordinates_prime_pos hx).1, primeCoordinates_pairwise d⟩
  have hc : (⟨[⟨p, 1, false⟩], p + 2, ys.length⟩ : Box).ClosedBelow (10 ^ 21) := by
    rcases hp with rfl | rfl
    · have hhi := oddBelow10Pow21_primeFactors_card_le_sixteen hdlt hdodd
      exact h3 ys.length hrlow (by omega)
    · have hnot3 : ¬ 3 ∣ d := by
        intro h3
        obtain ⟨zs, hz, _⟩ := primeCoordinates_three hdodd h3
        rw [hz] at heq
        simp at heq
      have hhi := coprimeThreeOddBelow10Pow21_primeFactors_card_le_fifteen hdlt hdodd hnot3
      have hlo := coprimeThree_oddAbundant_primeFactors_card_ge_seven hdodd hdw.1 hnot3
      exact h5 ys.length (by omega) (by omega)
  exact hc [(p, a)] ys ⟨.cons hfit .nil, ht, rfl⟩ hcoord
    (hnum.symm ▸ hdlt) (hnum.symm ▸ hdw) (hnum.symm ▸ hproper)

end OddWeirdSubproblems

namespace OddWeirdSubproblems

open Finset

/-- Multiplication by a new prime gives an affine equation for the excess over twice the number. -/
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

/-- A core subset sum may be extended by one multiple of the new prime to
represent the excess of the squarefree extension. -/
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

/-- A certified interval of core subset sums excludes all supported prime extensions. -/
theorem squarefreePseudoperfectOfInterval {m q s h a b : ℕ} (hq : q.Prime)
    (hfresh : ¬ q ∣ m) (hs : (∑ d ∈ m.divisors, d) = s) (hdef : s ≤ 2 * m)
    (hh : h = 0 ∨ h ∈ m.properDivisors)
    (hcover : ∀ x, a ≤ x → x ≤ b → ∃ t ⊆ m.divisors, ∑ d ∈ t, d = x)
    (hlo : a + (2 * m - s + h) * q ≤ s)
    (hhi : s ≤ b + (2 * m - s + h) * q) : (m * q).Pseudoperfect := by
  obtain ⟨t, ht, hsum⟩ := hcover (s - (2 * m - s + h) * q) (by omega) (by omega)
  exact squarefreePseudoperfectOfSubset hq hfresh hs hdef hh ht (by omega)

/-- A fresh divisor extends a covered interval whenever its two translates touch. -/
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

/-- Complementing within the divisor set reflects an interval of covered sums. -/
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

/-- A proper-divisor interval may be shifted by the core before adjoining the prime. -/
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

/-- A jump covers every possible head prime in the skipped interval. -/
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

theorem forall₂_append_singleton {ss : List Slot} {s : Slot} {xs : Coordinates}
    (h : List.Forall₂ Slot.Fits (ss ++ [s]) xs) :
    ∃ as x, xs = as ++ [x] ∧ List.Forall₂ Slot.Fits ss as ∧ s.Fits x := by
  induction ss generalizing xs with
  | nil =>
    simp only [List.nil_append, List.forall₂_cons_left_iff, List.forall₂_nil_left_iff] at h
    obtain ⟨x, _, hx, rfl, rfl⟩ := h
    exact ⟨[], x, rfl, .nil, hx⟩
  | cons t ss ih =>
    simp only [List.cons_append, List.forall₂_cons_left_iff] at h
    obtain ⟨x, xs, hx, hxs, rfl⟩ := h
    obtain ⟨as, y, rfl, ht, hy⟩ := ih hxs
    exact ⟨x :: as, y, rfl, .cons hx ht, hy⟩

/-- When the fresh prime is small, the minimum with exponent one is already
nondeficient. A pseudoperfect certificate for that minimum closes the entire
box, including all greater exponents of the fresh or old primes. -/
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

/-- If a fresh factor makes the minimum nondeficient while another distinct
prime is still required, every member of the branch has a nondeficient divisor. -/
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

theorem headRange_empty_of_composites {ss : List Slot} {r lo hi : ℕ}
    (h : ((List.range (hi - lo)).all (fun i => decide ((lo + i).minFac ≠ lo + i))) = true) :
    HeadRangeClosed ss r lo hi := by
  intro q hlo hhi hp _
  simp only [List.all_eq_true, decide_eq_true_eq] at h
  have hbad := h (q - lo) (List.mem_range.mpr (by omega))
  rw [show lo + (q - lo) = q by omega] at hbad
  exact (hbad hp.minFac_eq).elim

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

theorem headRange_nondeficient_prefix {ss : List Slot} {r lo hi m s : ℕ}
    (hr : 0 < r) (hm : number (ss.map Slot.minimum) = m)
    (hs : divisorSum (ss.map Slot.minimum) = s)
    (hcut : (2 * m - s) * (hi - 1) ≤ s) :
    HeadRangeClosed ss r lo hi := by
  intro q _ hqhi _ _
  apply close_nondeficient_squarefree_prefix hr
  rw [hm, hs, Nat.mul_add, Nat.mul_one]
  have hq : q ≤ hi - 1 := by omega
  have h₁ := (Nat.mul_le_mul_left (2 * m - s) hq).trans hcut
  have h₂ := Nat.mul_le_mul_right q (show 2 * m ≤ 2 * m - s + s by omega)
  rw [Nat.add_mul] at h₂
  omega

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

theorem sigma_after_head (ss : List Slot) (q : ℕ) :
    divisorSum ((ss ++ [({ prime := q, exponent := 1, fixed := false } : Slot)]).map Slot.minimum)
    = divisorSum (ss.map Slot.minimum) * (1 + q) := by
  rw [List.map_append, divisorSum_append]
  simp [divisorSum, powerSum, Slot.minimum]

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

/-- A jump at a fixed size cutoff closes the skipped heads and the continuation. -/
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

private theorem tailMinimum_pos_of_pos (p r : ℕ) (hp : 0 < p) : 0 < tailMinimum p r := by
  induction r generalizing p with
  | zero => simp [tailMinimum]
  | succ r ih =>
    rw [tailMinimum]
    exact Nat.mul_pos hp (ih _ (by omega))

/-- If the head of a nonempty tail is at least `stop`, then the slot minimum
multiplied by `stop` is a lower bound for the completed number. -/
theorem minimum_mul_head_le_of_matches {ss : List Slot} {xs ys : Coordinates} {stop r : ℕ}
    (hmatch : (⟨ss, stop, r + 1⟩ : Box).Matches xs ys) (hcoord : PrimeCoordinates (xs ++ ys)) :
    number (ss.map Slot.minimum) * stop ≤ number (xs ++ ys) := by
  obtain ⟨hfit, ht, hlen⟩ := hmatch
  have hslots : number (ss.map Slot.minimum) ≤ number xs :=
    Nat.le_of_dvd (number_pos (primeCoordinates_left hcoord).1) (minimum_dvd hfit)
  have htail := tailMinimum_le_number ht
  change ys.length = r + 1 at hlen
  rw [hlen, tailMinimum] at htail
  have hstop : stop ≤ number ys :=
    (Nat.le_mul_of_pos_right stop (tailMinimum_pos_of_pos (stop + 2) r (by omega))).trans htail
  rw [number_append]
  exact Nat.mul_le_mul hslots hstop

/-- A finite head range closes the box below `B` once the slot minimum
times the first unchecked head reaches `B`. Taking `r = 0` gives the
last-prime cutoff. -/
theorem closeBelow_of_headRange_size_stop {ss : List Slot} {B p stop r : ℕ}
    (hrange : HeadRangeClosed ss r p stop)
    (hsize : B ≤ number (ss.map Slot.minimum) * stop) :
    (⟨ss, p, r + 1⟩ : Box).ClosedBelow B := by
  apply closeBelow_jump_next (stop := stop)
  · intro xs ys hmatch hcoord hlt _ _
    exact hlt.not_ge (hsize.trans (minimum_mul_head_le_of_matches hmatch hcoord))
  · intro q hqlo hqhi hq hodd
    exact closedBelow_of_closed (hrange q hqlo hqhi hq hodd) B

end OddWeirdSubproblems

namespace OddWeirdSubproblems

/-- A structurally recursive composite test for certificate replay. Finding
any proper factor is sufficient to omit a prime branch. -/
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

/-! Certified dynamic lower bounds for the distinct primes in a tail. -/

namespace OddWeirdSubproblems

/-- Advance past at most `fuel` odd composite numbers. A stopped scan is
still a lower bound, whether or not its returned endpoint is prime. -/
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

/-! Use the size cutoff to fix an exponent before testing divisor coverage. -/

namespace OddWeirdSubproblems

/-- This split need only be searched at its fixed exponent if raising
the exponent makes the minimum possible completion too large. -/
theorem closeBelow_fix_slot_of_size {b : Box} {B i : ℕ} {s : Slot}
    (hi : b.slots[i]? = some s) (hf : s.fixed = false) (hodd : Odd b.next)
    (hB : B ≤ number ({b with slots := b.slots.set i {s with exponent := s.exponent + 1}} : Box).minimum *
      (tailPrimeFloor b.next b.remaining).prod)
    (hfixed : ({b with slots := b.slots.set i {s with fixed := true}} : Box).ClosedBelow B) :
    b.ClosedBelow B :=
  closeBelow_split_slot hi hf hfixed (closeBelow_of_ranked_minimum_ge hodd hB)

/-- Find the first open slot whose next exponent would exceed the size budget. -/
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

/-- The additional exponent budget is measured relative to the minimum
product of all old slots and all ranked fresh prime floors. -/
def exponentBudget (B : ℕ) (b : Box) : ℕ :=
  (B - 1) / (number b.minimum * (tailPrimeFloor b.next b.remaining).prod)

private def floorSlot (p : ℕ) : Slot := ⟨p, 1, false⟩

private def exponentCapSlot (R : ℕ) (s : Slot) : ℕ × ℕ :=
  (s.prime, if s.fixed then s.exponent else s.exponent + Nat.log s.prime R)

/-- Keep fixed exponents and cap each open exponent by the integer logarithm
of the leftover size budget. Fresh slots use the ranked prime floors. -/
def exponentCapCoordinates (B : ℕ) (b : Box) : Coordinates :=
  ((b.slots ++ (tailPrimeFloor b.next b.remaining).map floorSlot).map
    (exponentCapSlot (exponentBudget B b)))

/-- The finite cap is checked with natural cross-products. -/
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

/-- The abundancy index of a completion below `B` is bounded by the product
of its independently size-capped prime-power indices. -/
theorem abundancyIndex_le_exponentCap_of_matches_below {b : Box} {B : ℕ} {xs ys : Coordinates}
    (hnext : 1 < b.next) (hodd : Odd b.next) (hmatch : b.Matches xs ys)
    (hcoords : PrimeCoordinates (xs ++ ys)) (hsize : number (xs ++ ys) < B) :
    (number (xs ++ ys)).abundancyIndex ≤
      (divisorSum (exponentCapCoordinates B b) : ℚ) / (number (exponentCapCoordinates B b) : ℚ) := by
  have h := indices_le_exponentCap (match_capped_numericalFit hnext hodd hmatch hsize)
  change _ ≤ ((exponentCapCoordinates B b).map (fun x => index x.1 x.2)).prod at h
  rw [coordinate_index_eq, coordinate_index_eq, divisorSum_eq hcoords, ← Nat.abundancyIndex] at h
  exact h

/-- A size-capped upper product at most two closes the box below `B`. -/
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

/-- Fix all old exponents that cannot grow below the size cutoff in one pass.
The minimum value and the count of fresh factors stay the same. -/
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

/-- Verify that each next divisor touches the current interval, then extend. -/
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

theorem cover_of_verified_divisor_interval {n a b : ℕ} {ds ws : List ℕ}
    (hnodup : (ds ++ ws).Nodup)
    (hdiv : ∀ d ∈ ds ++ ws, d ∣ n ∧ d < n)
    (hbit : bitIntervalOk ds a b = true)
    (hgrow : growIntervalOk a b ws = true) :
    Covered n.properDivisors a (b + ws.sum) := by
  have hnd := (List.nodup_append.mp hnodup).1
  have hc := cover_of_growIntervalOk hnodup (cover_of_bitIntervalOk hnd hbit) hgrow
  intro x hlo hhi
  obtain ⟨t, ht, hs⟩ := hc x hlo hhi
  exact ⟨t, fun d hd => Nat.mem_properDivisors.mpr (hdiv d (List.mem_toFinset.mp (ht hd))), hs⟩

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

theorem cover_of_validated_bits {n a b : ℕ} {ds : List ℕ}
    (hd : divisorListOk n ds = true) (hb : bitIntervalOk ds a b = true) :
    Covered n.properDivisors a b :=
  cover_mono (divisorListOk_sound hd).2 (cover_of_bitIntervalOk (divisorListOk_sound hd).1 hb)

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

theorem cover_reflected_bits {n a b : ℕ} {small ds : List ℕ}
    (hd : divisorListOk n ds = true) (hsmall : small.toFinset ⊆ ds.toFinset)
    (hs : small.Nodup) (hb : bitIntervalOk small a b = true)
    (hab : a ≤ b) (hb' : b ≤ ds.sum) :
    Covered n.properDivisors (ds.sum - b) (ds.sum - a) := by
  obtain ⟨hnd, hsub⟩ := divisorListOk_sound hd
  have hc := cover_mono hsmall (cover_of_bitIntervalOk hs hb)
  rw [← sum_toFinset_of_nodup hnd] at hb' ⊢
  exact cover_mono hsub (subsetSumIntervalReflect hc hab hb')

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
  | fuel + 1, ds =>
    if ds.length < 2 then ds
    else
      let mid := ds.length / 2
      mergeDivisors ds.length (sortDivisors fuel (ds.take mid)) (sortDivisors fuel (ds.drop mid))

def sortedDivisors (fs : Coordinates) : List ℕ :=
  sortDivisors 30 (divisorsFromCoordinates fs)

def smallPrefix : ℕ → List ℕ → List ℕ
  | _, [] => []
  | room, d :: ds => if d ≤ room then d :: smallPrefix (room - d) ds else []

def growPrefix (a : ℕ) : ℕ → List ℕ → List ℕ
  | _, [] => []
  | b, d :: ds =>
    if a + d ≤ b + 1 then d :: growPrefix a (b + d) ds else []

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

def peelGrowth (a : ℕ) : List ℕ → ℕ → ℕ → List ℕ × ℕ
  | [], _, x => ([], x)
  | w :: ws, b, x =>
    if b - w < x then
      let (ds, y) := peelGrowth a ws (b - w) (x - w)
      (w :: ds, y)
    else peelGrowth a ws (b - w) x

/-- Recover an actual subset from the bitset and translated central interval.
Every proposed subset is checked independently by `witnessOk`. -/
def intervalWitness (ds : List ℕ) (x : ℕ) : Option (List ℕ) :=
  let short := smallPrefix 1024 ds
  let bits := subsetBits short
  if bits.testBit x then some (bitWitness short x)
  else
    let a := effectiveLow bits short.sum
    let b := short.sum - a
    if b < a then none
    else
      let extra := growPrefix a b (ds.drop short.length)
      let high := b + extra.sum
      if a ≤ x && x ≤ high then
        let (ws, y) := peelGrowth a extra.reverse high x
        if bits.testBit y then some (ws ++ bitWitness short y) else none
      else none

def cofactorWitness (fs : Coordinates) (p i target : ℕ) : Option (List ℕ) :=
  let rest := fs.eraseIdx i
  let ds := sortedDivisors rest
  let shifts := [0, p] ++ rest.map (fun t => p * t.1)
  shifts.findSome? (fun w =>
    if w ≤ target then
      (intervalWitness ds (target - w)).map (fun chosen =>
        if w = 0 then chosen else w :: chosen)
    else none)

def hintedWitness (fs : Coordinates) (i h target : ℕ) : Option (List ℕ) := do
  let (p, _) ← fs[i]?
  let scaled := p * h
  if target < scaled then none
  else
    let ds := sortedDivisors (fs.eraseIdx i)
    let chosen ← intervalWitness ds (target - scaled)
    pure (if scaled = 0 then chosen else scaled :: chosen)

def hintedWitnessOk (fs : Coordinates) (i h : ℕ) : Bool :=
  let n := number fs
  let s := divisorSum fs
  match hintedWitness fs i h (s - 2 * n) with
  | some ds => witnessOk n s (sortDivisors 30 ds)
  | none => false

theorem hintedWitnessOk_closes {b : Box} {i h : ℕ}
    (hok : hintedWitnessOk b.minimum i h = true) : b.Closed := by
  unfold hintedWitnessOk at hok
  dsimp only at hok
  split at hok
  · exact witnessOk_closes hok
  · contradiction

def suggestedWitness (fs : Coordinates) (target : ℕ) : Option (List ℕ) :=
  fs.zipIdx.reverse.findSome? (fun ((p, _), i) => cofactorWitness fs p i target)

def automaticWitnessOk (fs : Coordinates) : Bool :=
  let n := number fs
  let s := divisorSum fs
  match suggestedWitness fs (s - 2 * n) with
  | none => false
  | some ds => witnessOk n s (sortDivisors 30 ds)

theorem automaticWitnessOk_closes {b : Box} (h : automaticWitnessOk b.minimum = true) :
    b.Closed := by
  change (match suggestedWitness b.minimum (divisorSum b.minimum - 2 * number b.minimum) with
    | none => false
    | some ds => witnessOk (number b.minimum) (divisorSum b.minimum) (sortDivisors 30 ds)) = true at h
  split at h
  · contradiction
  · exact witnessOk_closes h

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

def zeroRun : ℕ → ℕ → ℕ → ℕ
  | 0, _, lo => lo
  | fuel + 1, bits, lo =>
    let mid := lo + 2 ^ fuel
    if bits &&& (2 ^ mid - 1) = 0 then zeroRun fuel bits mid
    else zeroRun fuel bits lo

def bitRunsAux : ℕ → ℕ → ℕ → List (ℕ × ℕ)
  | 0, _, _ => []
  | fuel + 1, bits, offset =>
    if bits = 0 then []
    else
      let first := zeroRun 11 bits 0
      let start := bits >>> first
      let mask := 2 ^ (1025 - (offset + first)) - 1
      let missing := mask ^^^ (start &&& mask)
      let count := if missing = 0 then 1025 - (offset + first) else zeroRun 11 missing 0
      let low := offset + first
      let next := low + count
      if count = 0 then []
      else (low, next - 1) :: bitRunsAux fuel (start >>> count) next

def bitRuns (bits size : ℕ) : List (ℕ × ℕ) :=
  bitRunsAux size (bits &&& (2 ^ size - 1)) 0 |>.map (fun (a, b) => (a, min b (size - 1)))

def makeCoverage (fs : Coordinates) : CoreCoverage :=
  let proper := (sortedDivisors fs).dropLast
  let small := smallPrefix 1024 proper
  let bits := subsetBits small
  let a := effectiveLow bits small.sum
  let b := small.sum - a
  let growing := if a ≤ b then growPrefix a b (proper.drop small.length) else []
  ⟨proper, small, growing, a, b, if a ≤ b then [⟨0, a, b + growing.sum⟩] else []⟩

def IntervalSource.endpoints (c : CoreCoverage) (t : IntervalSource) : ℕ × ℕ :=
  if t.kind = 2 then (c.proper.sum - t.high, c.proper.sum - t.low)
  else (t.low, t.high)

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

theorem intervalSource_ok_covers {n : ℕ} {c : CoreCoverage} {t : IntervalSource}
    (h : t.ok n c = true) :
    Covered n.properDivisors (t.endpoints c).1 (t.endpoints c).2 := by
  unfold IntervalSource.ok at h
  by_cases h0 : t.kind = 0
  · simp only [if_pos h0, Bool.and_eq_true, decide_eq_true_eq] at h
    simp only [IntervalSource.endpoints, show t.kind ≠ 2 by omega, if_false]
    have hcv := cover_of_validated_growth h.1.1.1 h.1.1.2 h.1.2
    intro x hx hy
    exact hcv x (h.2.1.trans hx) (hy.trans h.2.2)
  by_cases h1 : t.kind = 1
  · simp only [if_neg h0, if_pos h1, Bool.and_eq_true] at h
    simpa only [IntervalSource.endpoints, show t.kind ≠ 2 by omega, if_false] using
      (cover_of_validated_bits h.1 h.2)
  by_cases h2 : t.kind = 2
  · simp only [if_neg h0, if_neg h1, if_pos h2, Bool.and_eq_true, decide_eq_true_eq] at h
    simp only [IntervalSource.endpoints, if_pos h2]
    apply cover_reflected_bits h.1.1.1.1 _ (tightlySorted_nodup h.1.1.1.2) h.1.2 h.2.1 h.2.2
    intro x hx
    apply List.mem_toFinset.mpr
    have hx' := List.mem_toFinset.mp hx
    rw [h.1.1.2] at hx'
    exact List.mem_of_mem_take hx'
  · simp [h0, h1, h2] at h

structure SweepInterval where
  source : IntervalSource
  multiple : ℕ
  shift : ℕ
  remainUntil : ℕ

def sweepIntervalOk (n s first stop : ℕ) (c : CoreCoverage) (a : SweepInterval) : Bool :=
  let (low, high) := a.source.endpoints c
  let slope := 2 * n - s + a.multiple
  a.source.ok n c &&
  decide (s ≤ 2 * n ∧ (a.multiple = 0 ∨ (a.multiple ∣ n ∧ a.multiple < n)) ∧
    (a.shift = 0 ∨ a.shift = n) ∧
    s ≤ high + a.shift + slope * first ∧ low + a.shift + slope * (stop - 1) ≤ s)

theorem sweepIntervalOk_closes {ss : List Slot} {first stop : ℕ}
    {c : CoreCoverage} {a : SweepInterval}
    (h : sweepIntervalOk (number (ss.map Slot.minimum)) (divisorSum (ss.map Slot.minimum))
      first stop c a = true) : HeadRangeClosed ss 0 first stop := by
  dsimp [sweepIntervalOk] at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact headRange_squarefree rfl rfl h.2.1 h.2.2.1 h.2.2.2.1
    (intervalSource_ok_covers h.1) h.2.2.2.2.1 h.2.2.2.2.2

def bestSweepFrom (n s first stop : ℕ) (ss : List Slot)
    (c : CoreCoverage) (sources : List IntervalSource) : Option SweepInterval :=
  ([0, 1] ++ ss.map Slot.prime).foldl (fun best h =>
    sources.foldl (fun best source =>
      let (lo, hi) := IntervalSource.endpoints c source
      let slope := 2 * n - s + h
      [0, n].foldl (fun best shift =>
        let endAt := min stop ((s - (lo + shift)) / slope + 1)
        if first < endAt && lo + shift ≤ s && s ≤ hi + shift + slope * first &&
          (best.map SweepInterval.remainUntil).getD first < endAt
        then some ⟨source, h, shift, endAt⟩
        else best) best) best) none

def bestSweepInterval (n s first stop : ℕ) (ss : List Slot)
    (c : CoreCoverage) : Option SweepInterval :=
  (bestSweepFrom n s first stop ss c c.central).orElse (fun _ =>
    let runs := bitRuns (subsetBits c.small) (c.small.sum + 1)
    let sources := runs.map (fun (l, h) => ⟨1, l, h⟩) ++
      runs.map (fun (l, h) => ⟨2, l, h⟩)
    bestSweepFrom n s first stop ss c sources)

end OddWeirdSubproblems

namespace OddWeirdSubproblems

def minimumAutoOk (fallback : ℕ → List ℕ) (b : Box) : Bool :=
  minimumOk fallback b || automaticWitnessOk b.minimum

theorem minimumAutoOk_closes {fallback : ℕ → List ℕ} {b : Box}
    (hnondef : 2 * number b.minimum ≤ divisorSum b.minimum)
    (h : minimumAutoOk fallback b = true) : b.Closed := by
  rcases Bool.or_eq_true_iff.mp h with hm | hw
  · exact minimumOk_closes hnondef hm
  · exact automaticWitnessOk_closes hw

def bestDeletionBound (ss : List Slot) (stop : ℕ) : Option (ℕ × ℕ) :=
  let fs := ss.map Slot.minimum
  (List.range ss.length).foldl (fun best i =>
    let ds := decrement fs i
    let z := number ds
    let t := divisorSum ds
    let d := 2 * z - t
    let jump := if d = 0 then stop else min stop (t / d + 1)
    if z < number fs && (best.map Prod.snd).getD 0 < jump then some (i, jump) else best) none

def sweepStep (fallback : ℕ → List ℕ) (ss : List Slot)
    (c : CoreCoverage) (first stop : ℕ) : Option ℕ :=
  let fs := ss.map Slot.minimum
  let n := number fs
  let s := divisorSum fs
  match bestSweepInterval n s first stop ss c with
  | some a =>
    if sweepIntervalOk n s first a.remainUntil c a then some a.remainUntil else none
  | none =>
    if first % 2 = 0 || first.minFac ≠ first then some (first + 1)
    else
      let b : Box := ⟨ss ++ [⟨first, 1, false⟩], first + 2, 0⟩
      if 2 * number b.minimum ≤ divisorSum b.minimum && minimumAutoOk fallback b
      then some (first + 1)
      else none

theorem sweepStep_sound {fallback : ℕ → List ℕ} {ss : List Slot}
    {c : CoreCoverage} {first stop next : ℕ}
    (h : sweepStep fallback ss c first stop = some next) :
    HeadRangeClosed ss 0 first next := by
  unfold sweepStep at h
  dsimp only at h
  split at h
  · next a ha =>
    split at h
    · have eq := Option.some.inj h
      rw [← eq]
      exact sweepIntervalOk_closes ‹_›
    · contradiction
  · split at h
    · next hc =>
      have eq := Option.some.inj h
      rw [← eq]
      apply headRange_single
      intro hp ho
      have hc' : first % 2 = 0 ∨ first.minFac ≠ first := by simpa using hc
      rcases hc' with he | hn
      · obtain ⟨k, hk⟩ := ho
        omega
      · exact (hn hp.minFac_eq).elim
    · split at h
      · next hb =>
        have eq := Option.some.inj h
        rw [← eq]
        apply headRange_single
        intro _ _
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
        exact minimumAutoOk_closes hb.1 hb.2
      · contradiction

def sweepReplay (fallback : ℕ → List ℕ) (ss : List Slot) (c : CoreCoverage)
    (stop : ℕ) : ℕ → ℕ → Bool
  | 0, first => decide (stop ≤ first)
  | fuel + 1, first =>
    if stop ≤ first then true
    else match sweepStep fallback ss c first stop with
    | none => false
    | some next => decide (first < next) && sweepReplay fallback ss c stop fuel next

theorem sweepReplay_sound {fallback : ℕ → List ℕ} {ss : List Slot}
    {c : CoreCoverage} {fuel first stop : ℕ}
    (h : sweepReplay fallback ss c stop fuel first = true) :
    HeadRangeClosed ss 0 first stop := by
  induction fuel generalizing first with
  | zero =>
    simp only [sweepReplay, decide_eq_true_eq] at h
    intro q hqlo hqhi
    omega
  | succ fuel ih =>
    rw [sweepReplay] at h
    split at h
    · intro q hqlo hqhi
      omega
    split at h
    · contradiction
    · next next hstep =>
      exact headRange_join (sweepStep_sound hstep) (ih (Bool.and_eq_true_iff.mp h).2)

def closeSweepOk (fallback : ℕ → List ℕ) (ss : List Slot) (fuel first stop : ℕ) : Bool :=
  let fs := ss.map Slot.minimum
  let c := makeCoverage fs
  match bestDeletionBound ss stop with
  | some (i, jump) =>
    if first < jump then
      let ds := decrement fs i
      let z := number ds
      let t := divisorSum ds
      decide (i < ss.length ∧ z < number fs ∧ (2 * z - t) * (jump - 1) ≤ t) &&
        sweepReplay fallback ss c stop fuel jump
    else sweepReplay fallback ss c stop fuel first
  | none => sweepReplay fallback ss c stop fuel first

theorem closeSweepOk_sound {fallback : ℕ → List ℕ} {ss : List Slot}
    {fuel first stop : ℕ} (h : closeSweepOk fallback ss fuel first stop = true) :
    HeadRangeClosed ss 0 first stop := by
  unfold closeSweepOk at h
  dsimp only at h
  split at h
  · next i jump heq =>
    split at h
    · simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      exact headRange_join (headRange_decrement_nondeficient h.1.1 rfl rfl h.1.2.1 h.1.2.2)
        (sweepReplay_sound h.2)
    · exact sweepReplay_sound h
  · exact sweepReplay_sound h

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

theorem sweep_threshold_closes {ss : List Slot} {p r : ℕ} {fallback : ℕ → List ℕ}
    (hdef : divisorSum (ss.map Slot.minimum) < 2 * number (ss.map Slot.minimum))
    (hcheck : r = 0 →
      let b : Box := ⟨ss, p, 1⟩
      closeSweepOk fallback ss 5000 p (nextThreshold b) = true)
    (hskip : (⟨ss, nextThreshold ⟨ss, p, r + 1⟩, r + 1⟩ : Box).Closed) :
    (⟨ss, p, r + 1⟩ : Box).Closed := by
  apply close_jump_next hskip
  intro q hp hq hprime ho
  cases r with
  | zero => exact closeSweepOk_sound (hcheck rfl) q hp hq hprime ho
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

def wideReplay (fallback : ℕ → List ℕ) (cut : Box → Bool) : ℕ → Box → Bool
  | 0, _ => false
  | fuel + 1, b =>
    if cut b then true
    else if 2 * number b.minimum ≤ divisorSum b.minimum then minimumAutoOk fallback b
    else if b.upperNum ≤ 2 * b.upperDen then true
    else if 0 < b.remaining && b.next < nextThreshold b then
      (if b.remaining = 1 then closeSweepOk fallback b.slots 5000 b.next (nextThreshold b) else true) &&
      wideReplay fallback cut fuel {b with next := nextThreshold b}
    else match (chooseWideSlot b).bind (fun i => b.slots[i]?.map (fun s => (i, s))) with
    | some (i, s) =>
      if s.fixed then false else
      wideReplay fallback cut fuel {b with slots := b.slots.set i {s with fixed := true}} &&
      wideReplay fallback cut fuel {b with slots := b.slots.set i {s with exponent := s.exponent + 1}}
    | none =>
      match b.remaining with
      | 0 => false
      | r + 1 =>
        wideReplay fallback cut fuel ⟨b.slots, b.next + 2, r + 1⟩ &&
        if b.next.minFac = b.next then
          wideReplay fallback cut fuel ⟨b.slots ++ [⟨b.next, 1, false⟩], b.next + 2, r⟩
        else true

theorem wideReplay_closes {fallback : ℕ → List ℕ} {cut : Box → Bool} {fuel : ℕ} {b : Box}
    (hcut : ∀ box, cut box = true → box.Closed)
    (hlo : 1 < b.next) (hodd : Odd b.next) (h : wideReplay fallback cut fuel b = true) :
    b.Closed := by
  induction fuel generalizing b with
  | zero => simp [wideReplay] at h
  | succ fuel ih =>
    rw [wideReplay] at h
    split at h
    · exact hcut b ‹_›
    split at h
    · exact minimumAutoOk_closes ‹_› h
    next hnondef =>
      split at h
      · exact close_of_upperNum_le hlo ‹_›
      split at h
      next hguard =>
        obtain ⟨hr, hnext⟩ : 0 < b.remaining ∧ b.next < nextThreshold b := by simpa using hguard
        obtain ⟨h₁, h₂⟩ := Bool.and_eq_true_iff.mp h
        rcases b with ⟨ss, p, r⟩
        cases r with
        | zero => exact (Nat.lt_irrefl 0 hr).elim
        | succ r =>
          have hnd : divisorSum (ss.map Slot.minimum) <
              2 * number (ss.map Slot.minimum) := Nat.lt_of_not_ge hnondef
          apply sweep_threshold_closes (fallback := fallback) hnd _ (ih (hlo.trans hnext) (nextThreshold_odd _) h₂)
          intro heq
          subst r
          simpa using h₁
      next =>
        split at h
        next i s hs =>
          have hi : b.slots[i]? = some s := by
            obtain ⟨j, _, hj⟩ := Option.bind_eq_some_iff.mp hs
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

end OddWeirdSubproblems

namespace OddWeirdSubproblems

/-- A supplied seed and its adjoining weights certify an interval without
recomputing or sorting every proper divisor of the core. -/
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

def literalSweepOk (ss : List Slot) (stop : ℕ) : ℕ → List SweepAction → Bool
  | first, [] => decide (stop ≤ first)
  | first, a :: acts =>
    sweepActionOk ss first a && literalSweepOk ss stop (a.stop first) acts

theorem literalSweepOk_closes {ss : List Slot} {first stop : ℕ} {acts : List SweepAction}
    (h : literalSweepOk ss stop first acts = true) : HeadRangeClosed ss 0 first stop := by
  induction acts generalizing first with
  | nil =>
    simp only [literalSweepOk, decide_eq_true_eq] at h
    intro q hlo hhi
    omega
  | cons a acts ih =>
    obtain ⟨ha, ht⟩ := Bool.and_eq_true_iff.mp h
    exact headRange_join (sweepActionOk_closes ha) (ih ht)

structure LiteralInputs where
  point : Box → List ℕ
  sweep : Box → List SweepAction

theorem literal_threshold_closes {ss : List Slot} {p r : ℕ} {acts : List SweepAction}
    (hdef : divisorSum (ss.map Slot.minimum) < 2 * number (ss.map Slot.minimum))
    (hcheck : r = 0 →
      let b : Box := ⟨ss, p, 1⟩
      literalSweepOk ss (nextThreshold b) p acts = true)
    (hskip : (⟨ss, nextThreshold ⟨ss, p, r + 1⟩, r + 1⟩ : Box).Closed) :
    (⟨ss, p, r + 1⟩ : Box).Closed := by
  apply close_jump_next hskip
  intro q hp hq hprime ho
  cases r with
  | zero => exact literalSweepOk_closes (hcheck rfl) q hp hq hprime ho
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

def literalReplay (inputs : LiteralInputs) (cut : Box → Bool) : ℕ → Box → Bool
  | 0, _ => false
  | fuel + 1, b =>
    if cut b then true
    else if 2 * number b.minimum ≤ divisorSum b.minimum then minimumOk (fun _ => inputs.point b) b
    else if b.upperNum ≤ 2 * b.upperDen then true
    else if 0 < b.remaining && b.next < nextThreshold b then
      (if b.remaining = 1 then literalSweepOk b.slots (nextThreshold b) b.next (inputs.sweep b) else true) &&
      literalReplay inputs cut fuel {b with next := nextThreshold b}
    else match (chooseWideSlot b).bind (fun i => b.slots[i]?.map (fun s => (i, s))) with
    | some (i, s) =>
      if s.fixed then false else
      literalReplay inputs cut fuel {b with slots := b.slots.set i {s with fixed := true}} &&
      literalReplay inputs cut fuel {b with slots := b.slots.set i {s with exponent := s.exponent + 1}}
    | none =>
      match b.remaining with
      | 0 => false
      | r + 1 =>
        literalReplay inputs cut fuel ⟨b.slots, b.next + 2, r + 1⟩ &&
        if mayBeOddPrime b.next then
          literalReplay inputs cut fuel ⟨b.slots ++ [⟨b.next, 1, false⟩], b.next + 2, r⟩
        else true

theorem literalReplay_closes {inputs : LiteralInputs} {cut : Box → Bool} {fuel : ℕ} {b : Box}
    (hcut : ∀ box, cut box = true → box.Closed)
    (hlo : 1 < b.next) (hodd : Odd b.next) (h : literalReplay inputs cut fuel b = true) :
    b.Closed := by
  induction fuel generalizing b with
  | zero => simp [literalReplay] at h
  | succ fuel ih =>
    rw [literalReplay] at h
    split at h
    · exact hcut b ‹_›
    split at h
    · exact minimumOk_closes ‹_› h
    next hnondef =>
      split at h
      · exact close_of_upperNum_le hlo ‹_›
      split at h
      next hguard =>
        obtain ⟨hr, hnext⟩ : 0 < b.remaining ∧ b.next < nextThreshold b := by simpa using hguard
        obtain ⟨h₁, h₂⟩ := Bool.and_eq_true_iff.mp h
        rcases b with ⟨ss, p, r⟩
        cases r with
        | zero => exact (Nat.lt_irrefl 0 hr).elim
        | succ r =>
          have hnd : divisorSum (ss.map Slot.minimum) <
              2 * number (ss.map Slot.minimum) := Nat.lt_of_not_ge hnondef
          apply literal_threshold_closes (acts := inputs.sweep ⟨ss, p, r + 1⟩) hnd _ (ih (hlo.trans hnext) (nextThreshold_odd _) h₂)
          intro heq
          subst r
          simpa using h₁
      next =>
        split at h
        next i s hs =>
          have hi : b.slots[i]? = some s := by
            obtain ⟨j, _, hj⟩ := Option.bind_eq_some_iff.mp hs
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
            exact ih hlo' hodd' (by simpa only [if_pos (mayBeOddPrime_of_prime hp)] using htake)

end OddWeirdSubproblems

namespace OddWeirdSubproblems

/-- Compute only divisors that could take part in a small subset sum. -/
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

/-- Select a large divisor without forming and sorting the divisor list.
Higher primes lead the exponent search, and a whole feasible tail returns
its product immediately. The returned weights are verified by the caller. -/
def largestDivisorUpTo (fs : Coordinates) (B : ℕ) : ℕ :=
  largestDivisorSearch fs.reverse B

/-- Suggest a small witness by subtracting descending divisors until the
remainder can be represented in the short, computed bitset. -/
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

def sparseHintedWitnessOk (fs : Coordinates) (slot h : ℕ) : Bool :=
  let n := number fs
  let s := divisorSum fs
  match sparseHintedWitness fs slot h (s - 2 * n) with
  | some ds => witnessOk n s (sortDivisors 30 ds)
  | none => false

theorem sparseHintedWitnessOk_closes {b : Box} {slot h : ℕ}
    (hok : sparseHintedWitnessOk b.minimum slot h = true) : b.Closed := by
  unfold sparseHintedWitnessOk at hok
  dsimp only at hok
  split at hok
  · exact witnessOk_closes hok
  · contradiction

/-- Suggest only those adjoining weights needed by a specified interval
endpoint. The additional strict lower bound keeps them above the seed. -/
def sparseGrowth (fs : Coordinates) (low seedMax target : ℕ) :
    ℕ → ℕ → ℕ → Option (List ℕ)
  | 0, _, _ => none
  | fuel + 1, hi, previous =>
    if target ≤ hi then some [] else
      let bound := hi + 1 - low
      let value := largestDivisorUpTo fs (min (number fs - 1) bound)
      if value ≤ seedMax || value ≤ previous then none
      else (sparseGrowth fs low seedMax target fuel (hi + value) value).map (value :: ·)

def sparseIntervalWitness (fs : Coordinates) (target : ℕ) : Option (List ℕ) :=
  let ds := sortDivisors 20 (divisorsAtMost fs 1024)
  let seed := smallPrefix 1024 ds
  let bits := subsetBits seed
  if target ≤ seed.sum && bits.testBit target then some (bitWitness seed target)
  else
    let low := effectiveLow bits seed.sum
    let high := seed.sum - low
    if target < low || high < low then none else do
      let growth ← sparseGrowth fs low (seed.getLast?.getD 0) target 64 high 0
      let (large, rest) := peelGrowth low growth.reverse (high + growth.sum) target
      if bits.testBit rest then some (large ++ bitWitness seed rest) else none

def sparseWitnessHint (fs : Coordinates) (slot h target : ℕ) : Option (List ℕ) := do
  let (p, _) ← fs[slot]?
  let shift := p * h
  if target < shift then none else
    let ds ← sparseIntervalWitness (fs.eraseIdx slot) (target - shift)
    pure (if shift = 0 then ds else shift :: ds)

end OddWeirdSubproblems

namespace OddWeirdSubproblems

/-- Recover a short interval proof using a selected shift and endpoint. The
arithmetic checker subsequently verifies every generated divisor and sum. -/
def recoverInterval (fs : Coordinates) (first h shift : ℕ) : Option LiteralInterval :=
  let n := number fs
  let s := divisorSum fs
  let d := 2 * n - s
  let candidates := sortDivisors 20 (divisorsAtMost fs (min 1024 (n - 1)))
  let seed := smallPrefix 1024 candidates
  let lo := effectiveLow (subsetBits seed) seed.sum
  let hi := seed.sum - lo
  let goal := s - (shift + (d + h) * first)
  (sparseGrowth fs lo (seed.getLast?.getD 0) goal 96 hi 0).map (fun ds =>
    ⟨seed, ds, lo, hi, h, shift⟩)

theorem recoverInterval_closes {ss : List Slot} {first stop h shift : ℕ}
    (hcheck : match recoverInterval (ss.map Slot.minimum) first h shift with
      | none => false
      | some cert => sweepActionOk ss first (.interval stop cert)) :
    HeadRangeClosed ss 0 first stop := by
  split at hcheck
  · contradiction
  · exact sweepActionOk_closes (by simpa using hcheck)

def packedIndexWitness (fs : Coordinates) (slot h : ℕ) : List ℕ :=
  let n := number fs
  let s := divisorSum fs
  (sparseHintedWitness fs slot h (s - 2 * n)).getD [] |> sortDivisors 30

end OddWeirdSubproblems

namespace OddWeirdSubproblems

/-- Read a bounded base-128 natural number from a byte list. -/
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

def bytesFromNat : ℕ → ℕ → List ℕ
  | 0, _ => []
  | n + 1, v => v % 256 :: bytesFromNat n (v / 256)

/-- Read a backward copy with the overlap semantics used by LZ compressors. -/
def copyFromBuffer : ℕ → ℕ → Array ℕ → Option (Array ℕ)
  | 0, _, buf => some buf
  | n + 1, distance, buf => do
    if distance = 0 || buf.size < distance then none else
      let byte ← buf[buf.size - distance]?
      copyFromBuffer n distance (buf.push byte)

/-- Token 0 is followed by a run of literal bytes, token 1 by a backward
distance and copy length. The checker validates the resulting mathematical
certificates regardless of how this byte stream was produced. -/
def expandTokens : ℕ → List ℕ → Array ℕ → Option (Array ℕ)
  | 0, [], buf => some buf
  | 0, _, _ => none
  | _ + 1, [], buf => some buf
  | fuel + 1, token :: rest, buf =>
    if token = 0 then do
      let (n, bytes) ← readVarNat 64 rest
      if bytes.length < n then none else
        expandTokens fuel (bytes.drop n) (buf ++ (bytes.take n).toArray)
    else if token = 1 then do
      let (distance, rest) ← readVarNat 64 rest
      let (n, tail) ← readVarNat 64 rest
      let buf ← copyFromBuffer n distance buf
      expandTokens fuel tail buf
    else none

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

/-- Use one packed natural for the backward-copy window. The replay checks
the values obtained from the decoder before using them as certificates. -/
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

def decodeSweep : ℕ → List ℕ → Option (List SweepAction × List ℕ)
  | 0, rest => some ([], rest)
  | n + 1, bs => do
    let (action, rest) ← decodeSweepAction bs
    let (actions, rest) ← decodeSweep n rest
    pure (action :: actions, rest)

def decodeWitnessRows : ℕ → ℕ → List ℕ → Option (List (ℕ × List ℕ) × List ℕ)
  | 0, _, rest => some ([], rest)
  | count + 1, previous, bs => do
    let (delta, rest) ← readVarNat 64 bs
    let value := previous + delta
    let (ds, rest) ← readLengthPrefixed rest
    let (rows, rest) ← decodeWitnessRows count value rest
    pure ((value, ds) :: rows, rest)

def decodeSweepRows :
    ℕ → ℕ → List ℕ → Option (List ((ℕ × ℕ) × List SweepAction) × List ℕ)
  | 0, _, rest => some ([], rest)
  | count + 1, previous, bs => do
    let (delta, rest) ← readVarNat 64 bs
    let value := previous + delta
    let (first, rest) ← readVarNat 64 rest
    let (size, rest) ← readVarNat 64 rest
    let (acts, rest) ← decodeSweep size rest
    let (rows, rest) ← decodeSweepRows count value rest
    pure (((value, first), acts) :: rows, rest)

/-- The typed checker receives the decoded data and verifies every rule. A
missing row gives an empty payload and can pass only when that payload itself
justifies the requested closure. -/
def unpackedInputs (raw : List ℕ) : Option LiteralInputs := do
  let (pointCount, rest) ← readVarNat 64 raw
  let (points, rest) ← decodeWitnessRows pointCount 0 rest
  let (sweepCount, rest) ← readVarNat 64 rest
  let (sweeps, []) ← decodeSweepRows sweepCount 0 rest | none
  pure ⟨fun b => (points.lookup (number b.minimum)).getD [],
    fun b => (sweeps.lookup (number b.minimum, b.next)).getD []⟩

def packedInputs (count value : ℕ) : Option LiteralInputs := do
  let data ← expandTokens count (bytesFromNat count value) #[]
  unpackedInputs data.toList

end OddWeirdSubproblems

namespace OddWeirdSubproblems

/-- Return the largest weight at most the cap and the unexamined tail. -/
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

/-- Reuse the sorted divisor list across all growth steps of one interval.
The caller checks the resulting weights and overlap inequalities. -/
def sortedGrowth (fs : Coordinates) (low seedMax target high : ℕ) : Option (List ℕ) :=
  if target ≤ high then some [] else
    let ds := (sortedDivisors fs).dropWhile (· ≤ seedMax)
    scanGrowth low target 96 high (ds.takeWhile (· < number fs))

end OddWeirdSubproblems

namespace OddWeirdSubproblems

/-- Decode the factor and shift hint for a sparse point witness. -/
def decodePoint (b : Box) (data : List ℕ) : Option (List ℕ × List ℕ) := do
  let (tag, rest) ← readVarNat 64 data
  let i := tag / 8
  let j := tag % 8
  let fs := b.minimum
  let h := if j < 2 then j else ((fs.eraseIdx i)[j - 2]?.map Prod.fst).getD 0
  pure (packedIndexWitness fs i h, rest)

/-- The old rules close a minimum without using a payload when the number
is perfect, an extension is required, or a deletion is nondeficient. -/
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

theorem checkUnpackedBlock
    {readPoint : PointReplay} {b : Box} {cut : Box → Bool} {fuel count value : ℕ}
    (readSweep : SweepVerifier := .ofActions decodeStreamAction)
    (prune : BranchPruning := .none)
    (hcut : ∀ box, cut box = true → box.Closed) (hlo : 1 < b.next) (hodd : Odd b.next)
    (h : streamReplay readPoint readSweep prune cut fuel b (bytesFromNat count value) = some []) : b.Closed :=
  streamReplay_closes hcut hlo hodd h

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

theorem checkPackedCuts {readPoint : PointReplay} {readSweep : SweepVerifier}
    {b : Box} {cuts : List Box} (prune : BranchPruning) (hcuts : ClosedCuts cuts)
    (fuel count value : ℕ) (hlo : 1 < b.next) (hodd : Odd b.next)
    (h : checkPacked readPoint readSweep (fun q => cuts.any (boxEqual q)) fuel b count value prune = true) :
    b.Closed := by
  apply checkPackedBlock (readSweep := readSweep) (prune := prune) _ hlo hodd h
  intro q hq
  obtain ⟨c, hc, he⟩ := List.any_eq_true.mp hq
  have hqc := (boxEqual_iff_eq q c).mp he
  subst c
  exact hcuts.closedOfMem hc

end OddWeirdSubproblems

/-! Replay a compressed bounded search with certified range and size pruning. -/

namespace OddWeirdSubproblems

/-- An odd endpoint past every fresh prime that can fit under the cutoff. -/
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

/-- The ranked floor proves the search always moves past skipped composite
heads, even when the scan exhausts its rotation budget. -/
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

private def raiseAfterOddExclusion (b : Box) (i : ℕ) (s : Slot) : Box :=
  let step := if Even s.exponent then 2 else 1
  {b with slots := b.slots.set i {s with exponent := s.exponent + step}}

/-- A verified split may skip the odd exponents at one existing slot. -/
structure OddSplitReplay where
  verify : Box → List ℕ → Option (Option (ℕ × Slot) × List ℕ)
  sound : ∀ {b data i s rest B}, verify b data = some (some (i, s), rest) →
    (Even s.exponent → ({b with slots := b.slots.set i {s with fixed := true}} : Box).ClosedBelow B) →
    (raiseAfterOddExclusion b i s).ClosedBelow B → b.ClosedBelow B

def OddSplitReplay.none : OddSplitReplay where
  verify _ data := some (Option.none, data)
  sound := by
    intro _ _ _ _ _ _ h
    simp at h

/-- Verify a complete subtree. A certificate may close a box by an
unbounded rule. Size checks and the end of each last-prime sweep use `B`. -/
def replayWithSizeLimit (limited fast : Bool) (B : ℕ) (readPoint : PointReplay) (readSweep : SweepVerifier)
    (prune : BranchPruning) (oddSplit : OddSplitReplay)
    (cut : Box → Bool) : ℕ → Box → List ℕ → Option (List ℕ)
  | 0, _, _ => none
  | fuel + 1, b, data =>
    if cut b then some data
    else if limited && decide (B ≤ number b.minimum * (tailPrimeFloor b.next b.remaining).prod) then some data
    else if (limited && fast) && exponentCapOk B b then some data
    else
      let b := normalizeSlots (limited && fast) B b
      match (if !limited || fast then none else sizeFixedSlot B b) with
      | some (i, s) =>
        replayWithSizeLimit limited fast B readPoint readSweep prune oddSplit cut fuel
          {b with slots := b.slots.set i {s with fixed := true}} data
      | none =>
        if rankedUpperNum b ≤ 2 * rankedUpperDen b then some data
        else do
          let (closed, data) ← prune.verify b data
          if closed then some data
          else do
            let (split, data) ← oddSplit.verify b data
            match split with
            | some (i, s) => do
              let data ← (if Even s.exponent then
                  replayWithSizeLimit limited fast B readPoint readSweep prune oddSplit cut fuel
                    {b with slots := b.slots.set i {s with fixed := true}} data
                else some data)
              replayWithSizeLimit limited fast B readPoint readSweep prune oddSplit cut fuel
                (raiseAfterOddExclusion b i s) data
            | none =>
              if 2 * number b.minimum ≤ divisorSum b.minimum then consumeMinimum readPoint b data
              else if 0 < b.remaining && b.next < nextThreshold b then
                (if b.remaining = 1 then consumeWholeSweep readSweep b
                    (if limited then boundedSweepEnd B b else nextThreshold b) data
                  else some data).bind
                  (replayWithSizeLimit limited fast B readPoint readSweep prune oddSplit cut fuel {b with next := nextThreshold b})
              else match (chooseWideSlot b).bind (fun i => b.slots[i]?.map (fun s => (i, s))) with
              | some (i, s) => do
                if s.fixed then none else
                  let data ← replayWithSizeLimit limited fast B readPoint readSweep prune oddSplit cut fuel
                    {b with slots := b.slots.set i {s with fixed := true}} data
                  replayWithSizeLimit limited fast B readPoint readSweep prune oddSplit cut fuel
                    {b with slots := b.slots.set i {s with exponent := s.exponent + 1}} data
              | none =>
                match b.remaining with
                | 0 => none
                | r + 1 =>
                  let q := firstAllowedOdd b.next 32
                  if b.next < q then
                    replayWithSizeLimit limited fast B readPoint readSweep prune oddSplit cut fuel ⟨b.slots, q, r + 1⟩ data
                  else do
                    let data ← replayWithSizeLimit limited fast B readPoint readSweep prune oddSplit cut fuel
                      ⟨b.slots, b.next + 2, r + 1⟩ data
                    if mayBeOddPrime b.next then
                      replayWithSizeLimit limited fast B readPoint readSweep prune oddSplit cut fuel
                        ⟨b.slots ++ [⟨b.next, 1, false⟩], b.next + 2, r⟩ data
                    else some data

theorem replayWithSizeLimit_closes
    {limited fast : Bool} {B : ℕ} {readPoint : PointReplay} {readSweep : SweepVerifier} {prune : BranchPruning}
    {oddSplit : OddSplitReplay} {cut : Box → Bool} {fuel : ℕ} {b : Box} {data tail : List ℕ}
    (hcut : ∀ box, cut box = true → box.ClosedBelow B)
    (hlo : 1 < b.next) (hodd : Odd b.next)
    (h : replayWithSizeLimit limited fast B readPoint readSweep prune oddSplit cut fuel b data = some tail) :
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
        obtain ⟨⟨split, rest⟩, hsplit, h⟩ := Option.bind_eq_some_iff.mp h
        cases split with
        | some row =>
          obtain ⟨i, s⟩ := row
          dsimp only at h
          obtain ⟨mid, hfixed, hraise⟩ := Option.bind_eq_some_iff.mp h
          apply oddSplit.sound hsplit _ (ih hlo hodd hraise)
          intro heven
          rw [if_pos heven] at hfixed
          exact ih hlo hodd hfixed
        | none =>
          dsimp only at h
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

def boundedStreamWith (fast : Bool) (B : ℕ) (readPoint : PointReplay) (readSweep : SweepVerifier)
    (prune : BranchPruning) (cut : Box → Bool) : ℕ → Box → List ℕ → Option (List ℕ) :=
  replayWithSizeLimit true fast B readPoint readSweep prune .none cut

theorem boundedStreamWith_closes
    {fast : Bool} {B : ℕ} {readPoint : PointReplay} {readSweep : SweepVerifier} {prune : BranchPruning}
    {cut : Box → Bool} {fuel : ℕ} {b : Box} {data tail : List ℕ}
    (hcut : ∀ box, cut box = true → box.ClosedBelow B)
    (hlo : 1 < b.next) (hodd : Odd b.next)
    (h : boundedStreamWith fast B readPoint readSweep prune cut fuel b data = some tail) :
    b.ClosedBelow B :=
  replayWithSizeLimit_closes hcut hlo hodd h

private theorem unboundedReplay_independent_of_bound
    (B : ℕ) (readPoint : PointReplay) (readSweep : SweepVerifier) (prune : BranchPruning)
    (cut : Box → Bool) (fuel : ℕ) (b : Box) (data : List ℕ) :
    replayWithSizeLimit false true 0 readPoint readSweep prune .none cut fuel b data =
      replayWithSizeLimit false true B readPoint readSweep prune .none cut fuel b data := by
  induction fuel generalizing b data with
  | zero => rfl
  | succ fuel ih =>
    simp only [replayWithSizeLimit, Bool.false_and, Bool.false_eq_true, if_false,
      normalizeSlots, Bool.not_false, Bool.true_or, if_true, ih]

def unboundedRankedStream (readPoint : PointReplay) (readSweep : SweepVerifier)
    (prune : BranchPruning) (cut : Box → Bool) : ℕ → Box → List ℕ → Option (List ℕ) :=
  replayWithSizeLimit false true 0 readPoint readSweep prune .none cut

theorem unboundedRankedStream_closes
    {readPoint : PointReplay} {readSweep : SweepVerifier} {prune : BranchPruning}
    {cut : Box → Bool} {fuel : ℕ} {b : Box} {data tail : List ℕ}
    (hcut : ∀ box, cut box = true → box.Closed)
    (hlo : 1 < b.next) (hodd : Odd b.next)
    (h : unboundedRankedStream readPoint readSweep prune cut fuel b data = some tail) :
    b.Closed := by
  intro xs ys hm hv hw hp
  let B := number (xs ++ ys) + 1
  change replayWithSizeLimit false true 0 readPoint readSweep prune .none cut fuel b data = some tail at h
  rw [unboundedReplay_independent_of_bound B] at h
  exact replayWithSizeLimit_closes (fun box hc => closedBelow_of_closed (hcut box hc) B)
    hlo hodd h xs ys hm hv (Nat.lt_succ_self _) hw hp

def boundedStream (B : ℕ) (readPoint : PointReplay) (readSweep : SweepVerifier)
    (prune : BranchPruning) (cut : Box → Bool) : ℕ → Box → List ℕ → Option (List ℕ) :=
  boundedStreamWith false B readPoint readSweep prune cut

theorem boundedStream_closes
    {B : ℕ} {readPoint : PointReplay} {readSweep : SweepVerifier} {prune : BranchPruning}
    {cut : Box → Bool} {fuel : ℕ} {b : Box} {data tail : List ℕ}
    (hcut : ∀ box, cut box = true → box.ClosedBelow B)
    (hlo : 1 < b.next) (hodd : Odd b.next)
    (h : boundedStream B readPoint readSweep prune cut fuel b data = some tail) :
    b.ClosedBelow B :=
  boundedStreamWith_closes hcut hlo hodd h

end OddWeirdSubproblems

namespace OddWeirdSubproblems

open Finset

/-- Each weight is at most `G` plus the sum of the preceding weights. -/
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

/-- Append fresh weights in order to a covered central interval. The budget
allows each weight to exceed its preceding weights' sum by at most `G`. -/
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

/-- Raise the exponent of `p` by appending the scaled proper divisors of `u`,
then the old full number `m`. The two budget tests express the first interval
lift with additive inequalities over naturals. -/
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

/-- If the first interval lift succeeds with a positive lower endpoint, the
same ordered cofactor divisors and budget tests certify all higher exponents. -/
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

/-- Each proper divisor is at most `g` plus the sum of the smaller proper divisors. -/
def GapUpTo (n g : ℕ) : Prop :=
  ∀ d ∈ n.properDivisors, d ≤ g + ∑ x ∈ n.properDivisors.filter (· < d), x

instance (n g : ℕ) : Decidable (GapUpTo n g) := by
  unfold GapUpTo
  infer_instance

/-- Multiplying by any prime propagates the proper-divisor gap bound,
including when the prime already divides the core. -/
theorem GapUpTo.mul_prime {u q g : ℕ} (hg : GapUpTo u g) (hu : 0 < u) (hq : q.Prime) :
    GapUpTo (u * q) (max (q * g) (2 * u - ∑ d ∈ u.divisors, d)) := by
  let G := max (q * g) (2 * u - ∑ d ∈ u.divisors, d)
  have hle : q * g ≤ G := le_max_left _ _
  have hult : u < u * q := by
    simpa only [mul_one] using Nat.mul_lt_mul_of_pos_left hq.one_lt hu
  have hsub : u.properDivisors ⊆ (u * q).properDivisors := by
    intro d hd
    obtain ⟨hdvd, hlt⟩ := Nat.mem_properDivisors.mp hd
    exact Nat.mem_properDivisors.mpr ⟨hdvd.trans (dvd_mul_right u q), hlt.trans hult⟩
  have hsum (d : ℕ) : (∑ x ∈ u.properDivisors.filter (· < d), x) ≤
      ∑ x ∈ (u * q).properDivisors.filter (· < d), x := by
    apply Finset.sum_le_sum_of_subset
    intro x hx
    obtain ⟨hx, hlt⟩ := Finset.mem_filter.mp hx
    exact Finset.mem_filter.mpr ⟨hsub hx, hlt⟩
  intro d hd
  obtain ⟨hdvd, hdlt⟩ := Nat.mem_properDivisors.mp hd
  obtain ⟨a, b, ha, hb, rfl⟩ := exists_dvd_and_dvd_of_dvd_mul hdvd
  rcases (Nat.dvd_prime hq).mp hb with hb | hb
  · subst b
    simp only [mul_one]
    have hal := Nat.le_of_dvd hu ha
    by_cases h : a = u
    · subst a
      have hB : 2 * u - ∑ d ∈ u.divisors, d ≤ G := le_max_right _ _
      rw [Nat.sum_divisors_eq_sum_properDivisors_add_self] at hB
      have hsumu : u.properDivisors.filter (· < u) = u.properDivisors :=
        Finset.filter_true_of_mem fun d hd => (Nat.mem_properDivisors.mp hd).2
      have hs := hsum u
      rw [hsumu] at hs
      omega
    · have hap : a ∈ u.properDivisors := Nat.mem_properDivisors.mpr ⟨ha, lt_of_le_of_ne hal h⟩
      exact (hg a hap).trans (Nat.add_le_add ((Nat.le_mul_of_pos_left g hq.pos).trans hle) (hsum a))
  · subst b
    have hap : a ∈ u.properDivisors := Nat.mem_properDivisors.mpr
      ⟨ha, (Nat.mul_lt_mul_right hq.pos).mp hdlt⟩
    rw [mul_comm a q]
    have hscaled : (u.properDivisors.filter (· < a)).image (q * ·) ⊆
        (u * q).properDivisors.filter (· < q * a) := by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨hy, hylt⟩ := Finset.mem_filter.mp hy
      obtain ⟨hyd, hyu⟩ := Nat.mem_properDivisors.mp hy
      refine Finset.mem_filter.mpr ⟨?_, Nat.mul_lt_mul_of_pos_left hylt hq.pos⟩
      rw [mul_comm u q]
      exact Nat.mem_properDivisors.mpr ⟨mul_dvd_mul_left q hyd, Nat.mul_lt_mul_of_pos_left hyu hq.pos⟩
    have hsumScaled := Finset.sum_le_sum_of_subset (f := fun x : ℕ => x) hscaled
    rw [Finset.sum_image (fun _ _ _ _ h => mul_left_cancel₀ hq.ne_zero h), ← Finset.mul_sum] at hsumScaled
    exact (Nat.mul_le_mul_left q (hg a hap)).trans (by
      rw [Nat.mul_add]
      exact Nat.add_le_add hle hsumScaled)

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

/-- Sorting the proper divisors gives a duplicate-free increasing list
whose prefix gap is bounded by `g`. -/
theorem GapUpTo.prefixGapBound_sort {n g : ℕ} (hg : GapUpTo n g) :
    PrefixGapBound g n.properDivisors.sort := by
  let ds := n.properDivisors.sort
  have hd : ds.toFinset = n.properDivisors := Finset.sort_toFinset _ _
  apply prefixGapBound_of_sortedLT (Finset.sortedLT_sort n.properDivisors)
  intro d hmem
  rw [← sum_filtered_toFinset_eq_listSum (Finset.sort_nodup _ _) d, hd]
  exact hg d (hd ▸ List.mem_toFinset.mpr hmem)

private theorem le_gap_add_sum_smaller_of_prefixGapBound {ds : List ℕ} {g d : ℕ}
    (hg : PrefixGapBound g ds) (hd : d ∈ ds) :
    d ≤ g + (ds.filter (fun x => decide (x < d))).sum := by
  induction ds generalizing g with
  | nil => simp at hd
  | cons w ds ih =>
    rcases hg with ⟨hw, htail⟩
    by_cases h : w < d
    · have hmem : d ∈ ds := (List.mem_cons.mp hd).resolve_left (by omega)
      simpa [List.filter_cons, h, Nat.add_assoc] using ih htail hmem
    · exact ((Nat.le_of_not_gt h).trans hw).trans (Nat.le_add_right _ _)

/-- A gap certificate in any order, including prime-power layers, bounds
the gap after sorting the same proper divisors. -/
theorem PrefixGapBound.gapUpTo {ds : List ℕ} {n g : ℕ} (hg : PrefixGapBound g ds)
    (hnd : ds.Nodup) (hds : ds.toFinset = n.properDivisors) : GapUpTo n g := by
  intro d hd
  rw [← hds, sum_filtered_toFinset_eq_listSum hnd]
  exact le_gap_add_sum_smaller_of_prefixGapBound hg (List.mem_toFinset.mp (hds.symm ▸ hd))

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

def lowDensityOk (ds : List ℕ) (C G : ℕ) : Bool :=
  let bits := subsetBits ds
  (List.range (C + 1 - G)).all (fun j =>
    (List.range G).any (fun i => bits.testBit (j + i)))

theorem lowDensityOk_sound {ds : List ℕ} {C G : ℕ} (hn : ds.Nodup)
    (h : lowDensityOk ds C G = true) : DenseLowSums ds.toFinset C G := by
  intro j hj
  simp only [lowDensityOk, List.all_eq_true, List.any_eq_true, List.mem_range] at h
  obtain ⟨i, hi, hbit⟩ := h j (by omega)
  exact ⟨j + i, by omega, by omega, testBit_subsetBits hn hbit⟩

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

/-- Append fresh weights in increasing order. The sum of the fresh weights
smaller than `d` is the extra budget available when inserting `d`. -/
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

/-- A gap bound for the old proper divisors gives a central interval lift
for a prime already present. The divisors of the prime-free cofactor supply
a disjoint budget for the new weights. -/
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

/-- Increasing the exponents of primes already present preserves the
central interval if each prime passes the lift budget at the original core. -/
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

/-- Saturating at most \(r\) fresh prime factors above \(t\) bounds the
deficiency of the current prefix. -/
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

/-- The bound on the next prime and the accompanying lower bound on the sum
of the proper divisors, written without rational denominators. -/
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

/-- The fresh-prime budget for a deficient prefix, given a saturated upper
bound from its smallest possible new prime. -/
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

/-- The divisor-sum ratio of a fresh cofactor with at most (r) prime
factors is at most the product obtained by saturating each at (t). -/
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

/-- Apply the budget to an actual abundant coprime extension whose fresh
primes are at least (t). -/
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

private def primeLayers (p : ℕ) (full : List ℕ) : ℕ → List ℕ
  | 0 => []
  | e + 1 => primeLayers p full e ++ full.map (p ^ e * ·)

/-- Read the full layers in exponent order, then the final proper-divisor layer. -/
def primePowerProperDivisorList (u p e : ℕ) (ds : List ℕ) : List ℕ :=
  primeLayers p (ds ++ [u]) e ++ ds.map (p ^ e * ·)

/-- The maximum of the first and last full layer bounds and the final proper
layer bound. Here `s` is the sum of all divisors of the cofactor `u`. -/
def layeredGapBound (u p s g : ℕ) : ℕ → ℕ
  | 0 => g
  | e + 1 =>
    let f := max g (2 * u - s)
    max (max f (p ^ e * f - s * ((p ^ e - 1) / (p - 1))))
      (p ^ (e + 1) * g - s * ((p ^ (e + 1) - 1) / (p - 1)))

private theorem mem_primeLayers {p e d : ℕ} {full : List ℕ} :
    d ∈ primeLayers p full e ↔ ∃ j < e, ∃ b ∈ full, d = p ^ j * b := by
  induction e with
  | zero => simp [primeLayers]
  | succ e ih =>
    simp only [primeLayers, List.mem_append, ih, List.mem_map]
    constructor
    · rintro (⟨j, hj, b, hb, rfl⟩ | ⟨b, hb, rfl⟩)
      · exact ⟨j, hj.trans (Nat.lt_succ_self _), b, hb, rfl⟩
      · exact ⟨e, Nat.lt_succ_self _, b, hb, rfl⟩
    · rintro ⟨j, hj, b, hb, rfl⟩
      by_cases h : j = e
      · subst j
        exact Or.inr ⟨b, hb, rfl⟩
      · exact Or.inl ⟨j, by omega, b, hb, rfl⟩

private theorem nodup_append_primeLayer {p e : ℕ} {full tail : List ℕ} (hp : 0 < p)
    (hfull : ∀ b ∈ full, ¬ p ∣ b) (hprev : (primeLayers p full e).Nodup) (htail : tail.Nodup) :
    (primeLayers p full e ++ tail.map (p ^ e * ·)).Nodup := by
  apply List.nodup_append.mpr
  refine ⟨hprev, htail.map (mul_right_injective₀ (pow_ne_zero e hp.ne')), ?_⟩
  intro d hd d' hd' heq
  obtain ⟨j, hj, b, hb, rfl⟩ := mem_primeLayers.mp hd
  obtain ⟨b', _, rfl⟩ := List.mem_map.mp hd'
  have hpow : p ^ (j + 1) ∣ p ^ e * b' :=
    (pow_dvd_pow p (Nat.succ_le_of_lt hj)).trans (dvd_mul_right _ _)
  rw [← heq, pow_succ] at hpow
  exact hfull b hb ((Nat.mul_dvd_mul_iff_left (pow_pos hp j)).mp hpow)

/-- The layered list enumerates the proper divisors exactly once. -/
theorem primePowerProperDivisorList_spec {u p e : ℕ} {ds : List ℕ} (hu : 0 < u)
    (hp : p.Prime) (hpu : ¬ p ∣ u) (hnd : ds.Nodup) (hds : ds.toFinset = u.properDivisors) :
    (primePowerProperDivisorList u p e ds).Nodup ∧
      (primePowerProperDivisorList u p e ds).toFinset = (u * p ^ e).properDivisors := by
  let full := ds ++ [u]
  have hu' : u ∉ ds := fun h => Nat.self_notMem_properDivisors (hds ▸ List.mem_toFinset.mpr h)
  have hfull : full.toFinset = u.divisors := by
    rw [← Nat.insert_self_properDivisors hu.ne', ← hds]
    ext d
    simp [full]
  have hfullNd : full.Nodup := by
    apply List.nodup_append.mpr
    refine ⟨hnd, by simp, ?_⟩
    intro b hb c hc hbc
    rw [List.mem_singleton.mp hc] at hbc
    exact hu' (hbc ▸ hb)
  have hfullDvd (b : ℕ) (hb : b ∈ full) : b ∣ u :=
    Nat.dvd_of_mem_divisors (hfull ▸ List.mem_toFinset.mpr hb)
  have hfresh (b : ℕ) (hb : b ∈ full) : ¬ p ∣ b := fun hd => hpu (hd.trans (hfullDvd b hb))
  have hprev (j : ℕ) : (primeLayers p full j).Nodup := by
    induction j with
    | zero => simp [primeLayers]
    | succ j ih => exact nodup_append_primeLayer hp.pos hfresh ih hfullNd
  refine ⟨nodup_append_primeLayer hp.pos hfresh (hprev e) hnd, ?_⟩
  ext d
  change d ∈ (primeLayers p full e ++ ds.map (p ^ e * ·)).toFinset ↔ _
  rw [List.mem_toFinset, List.mem_append, mem_primeLayers, List.mem_map, Nat.mem_properDivisors]
  constructor
  · rintro (⟨j, hj, b, hb, rfl⟩ | ⟨b, hb, rfl⟩)
    · have hbu := hfullDvd b hb
      refine ⟨?_, ?_⟩
      · simpa only [mul_comm u (p ^ e)] using mul_dvd_mul (pow_dvd_pow p hj.le) hbu
      · calc
          _ ≤ p ^ j * u := Nat.mul_le_mul_left _ (Nat.le_of_dvd hu hbu)
          _ < p ^ e * u := Nat.mul_lt_mul_of_pos_right (pow_lt_pow_right₀ hp.one_lt hj) hu
          _ = _ := mul_comm _ _
    · obtain ⟨hbu, hlt⟩ := Nat.mem_properDivisors.mp (hds ▸ List.mem_toFinset.mpr hb)
      rw [mul_comm u (p ^ e)]
      exact ⟨mul_dvd_mul_left _ hbu, Nat.mul_lt_mul_of_pos_left hlt (pow_pos hp.pos e)⟩
  · rintro ⟨hdiv, hlt⟩
    obtain ⟨b, q, hbu, hq, rfl⟩ := exists_dvd_and_dvd_of_dvd_mul hdiv
    obtain ⟨j, hj, rfl⟩ := (Nat.dvd_prime_pow hp).mp hq
    by_cases hje : j = e
    · subst j
      have hbu' : b ∈ u.properDivisors := Nat.mem_properDivisors.mpr
        ⟨hbu, (Nat.mul_lt_mul_right (pow_pos hp.pos e)).mp hlt⟩
      exact Or.inr ⟨b, List.mem_toFinset.mp (hds.symm ▸ hbu'), mul_comm _ _⟩
    · have hbu' : b ∈ u.divisors := Nat.mem_divisors.mpr ⟨hbu, hu.ne'⟩
      exact Or.inl ⟨j, by omega, b, List.mem_toFinset.mp (hfull.symm ▸ hbu'), mul_comm _ _⟩

private theorem prefixGapBound_mono {G H : ℕ} {ds : List ℕ}
    (h : PrefixGapBound G ds) (hGH : G ≤ H) : PrefixGapBound H ds := by
  induction ds generalizing G H with
  | nil => trivial
  | cons d ds ih =>
    obtain ⟨hd, htail⟩ := h
    exact ⟨hd.trans hGH, ih htail (Nat.add_le_add_right hGH d)⟩

private theorem prefixGapBound_append {G : ℕ} {xs ys : List ℕ}
    (hx : PrefixGapBound G xs) (hy : PrefixGapBound (G + xs.sum) ys) :
    PrefixGapBound G (xs ++ ys) := by
  induction xs generalizing G with
  | nil => simpa using hy
  | cons d ds ih =>
    obtain ⟨hd, htail⟩ := hx
    refine ⟨hd, ih htail ?_⟩
    simpa only [List.sum_cons, add_assoc] using hy

private theorem sum_scaledList (v : ℕ) (ds : List ℕ) : (ds.map (v * ·)).sum = v * ds.sum := by
  simpa only [List.map_id, id_eq] using List.sum_map_mul_left ds id v

private theorem sum_primeLayers (p : ℕ) (full : List ℕ) (e : ℕ) :
    (primeLayers p full e).sum = full.sum * ∑ j ∈ range e, p ^ j := by
  induction e with
  | zero => simp [primeLayers]
  | succ e ih =>
    rw [primeLayers, List.sum_append, ih, sum_scaledList, sum_range_succ, Nat.mul_add,
      mul_comm (p ^ e) full.sum]

private theorem prefixGapBound_primeLayers {p H f : ℕ} {full : List ℕ} {e : ℕ}
    (hfull : PrefixGapBound f full)
    (hbound : ∀ j < e, p ^ j * f - full.sum * (∑ i ∈ range j, p ^ i) ≤ H) :
    PrefixGapBound H (primeLayers p full e) := by
  induction e with
  | zero => trivial
  | succ e ih =>
    rw [primeLayers]
    refine prefixGapBound_append (ih (fun j hj => hbound j (hj.trans (Nat.lt_succ_self _)))) ?_
    have hb := hbound e (Nat.lt_succ_self _)
    exact prefixGapBound_mono (hfull.scale (p ^ e)) (by rw [sum_primeLayers]; omega)

/-- Within the full layers the difference is monotone in one direction,
according to which of `s` and `(p - 1) * f` is greater. -/
private theorem layerGap_le_endpoints {p s f e j : ℕ} (hp : 1 ≤ p) (hj : j ≤ e) :
    p ^ j * f - s * (∑ i ∈ range j, p ^ i) ≤
      max f (p ^ e * f - s * (∑ i ∈ range e, p ^ i)) := by
  let F (i : ℕ) := p ^ i * f - s * (∑ k ∈ range i, p ^ k)
  change F j ≤ max f (F e)
  have hF0 : F 0 = f := by simp [F]
  have hF (i : ℕ) : F (i + 1) =
      (p ^ i * f + p ^ i * ((p - 1) * f)) -
        (s * (∑ k ∈ range i, p ^ k) + p ^ i * s) := by
    have hpf : f + (p - 1) * f = p * f := by
      calc
        _ = (1 + (p - 1)) * f := by rw [Nat.add_mul, one_mul]
        _ = _ := by rw [show 1 + (p - 1) = p by omega]
    dsimp only [F]
    rw [sum_range_succ, Nat.mul_add, mul_comm s (p ^ i), ← Nat.mul_add, hpf,
      pow_succ, mul_assoc]
  by_cases h : s ≤ (p - 1) * f
  · have hm : Monotone F := monotone_nat_of_le_succ fun i => by
      have hi := Nat.mul_le_mul_left (p ^ i) h
      rw [hF i]
      unfold F
      omega
    exact (hm hj).trans (le_max_right _ _)
  · have hm : Antitone F := antitone_nat_of_succ_le fun i => by
      have hi := Nat.mul_le_mul_left (p ^ i) (Nat.le_of_not_ge h)
      rw [hF i]
      unfold F
      omega
    have hh := hm (Nat.zero_le j)
    rw [hF0] at hh
    exact hh.trans (le_max_left _ _)

/-- The layered enumeration is duplicate-free, contains exactly the proper
divisors of `u * p ^ e`, and has the endpoint bound computed by `layeredGapBound`. -/
theorem layeredGapBound_sound {u p e g : ℕ} {ds : List ℕ} (hu : 0 < u)
    (hp : p.Prime) (hpu : ¬ p ∣ u) (hnd : ds.Nodup) (hds : ds.toFinset = u.properDivisors)
    (hgap : PrefixGapBound g ds) :
    let ws := primePowerProperDivisorList u p e ds
    ws.Nodup ∧ ws.toFinset = (u * p ^ e).properDivisors ∧
      PrefixGapBound (layeredGapBound u p (∑ d ∈ u.divisors, d) g e) ws := by
  obtain ⟨hn, hd⟩ := primePowerProperDivisorList_spec (e := e) hu hp hpu hnd hds
  refine ⟨hn, hd, ?_⟩
  cases e with
  | zero => simpa [layeredGapBound, primePowerProperDivisorList, primeLayers] using hgap
  | succ e =>
    let full := ds ++ [u]
    let s := ∑ d ∈ u.divisors, d
    let f := max g (2 * u - s)
    let H := layeredGapBound u p s g (e + 1)
    have hT : ds.sum = ∑ d ∈ u.properDivisors, d := by
      rw [← hds, sum_toFinset_of_nodup hnd]
    have hs : s = ds.sum + u := by
      rw [hT]
      exact Nat.sum_divisors_eq_sum_properDivisors_add_self
    have hfullsum : full.sum = s := by simp [full, hs]
    have hfull : PrefixGapBound f full := by
      apply prefixGapBound_append (prefixGapBound_mono hgap (le_max_left g (2 * u - s)))
      refine ⟨?_, trivial⟩
      have hf : 2 * u - s ≤ f := le_max_right _ _
      omega
    have hends : max f (p ^ e * f - s * (∑ i ∈ range e, p ^ i)) ≤ H := by
      rw [Nat.geomSum_eq hp.two_le]
      exact le_max_left _ _
    have hproperEnd : p ^ (e + 1) * g - s * (∑ i ∈ range (e + 1), p ^ i) ≤ H := by
      rw [Nat.geomSum_eq hp.two_le]
      exact le_max_right _ _
    have hb (j : ℕ) (hj : j < e + 1) : p ^ j * f - full.sum * (∑ i ∈ range j, p ^ i) ≤ H := by
      rw [hfullsum]
      exact (layerGap_le_endpoints hp.one_lt.le (Nat.le_of_lt_succ hj)).trans hends
    change PrefixGapBound H (primeLayers p full (e + 1) ++ ds.map (p ^ (e + 1) * ·))
    apply prefixGapBound_append (prefixGapBound_primeLayers hfull hb)
    exact prefixGapBound_mono (hgap.scale (p ^ (e + 1))) (by rw [sum_primeLayers, hfullsum]; omega)

end OddWeirdSubproblems

namespace OddWeirdSubproblems

open Finset

def coordinateGap : Coordinates → ℕ
  | [] => 0
  | (p, e) :: xs => layeredGapBound (number xs) p (divisorSum xs) (coordinateGap xs) e

theorem coprime_coordinateProduct {p : ℕ} {xs : Coordinates} (hp : p.Prime)
    (hv : ∀ x ∈ xs, x.1.Prime) (hf : ∀ x ∈ xs, p ≠ x.1) : p.Coprime (number xs) := by
  apply Nat.coprime_list_prod_right_iff.mpr
  intro w hw
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hw
  rw [← pow_one p]
  exact Nat.coprime_pow_primes _ _ hp (hv x hx) (hf x hx)

theorem coordinateGap_sound {fs : Coordinates} (hv : PrimeCoordinates fs) :
    ∃ ds : List ℕ, ds.Nodup ∧ ds.toFinset = (number fs).properDivisors ∧
      PrefixGapBound (coordinateGap fs) ds := by
  induction fs with
  | nil => exact ⟨[], by simp [number, PrefixGapBound]⟩
  | cons x xs ih =>
    obtain ⟨p, e⟩ := x
    have htail : PrimeCoordinates xs :=
      ⟨fun x hx => hv.1 x (List.mem_cons_of_mem _ hx), (List.pairwise_cons.mp hv.2).2⟩
    have hp := hv.1 (p, e) (by simp)
    have hf := hp.coprime_iff_not_dvd.mp (coprime_coordinateProduct hp htail.1
      (fun x hx => Nat.ne_of_lt ((List.pairwise_cons.mp hv.2).1 x hx)))
    obtain ⟨ds, hn, hd, hg⟩ := ih htail
    refine ⟨primePowerProperDivisorList (number xs) p e ds, ?_⟩
    simpa only [coordinateGap, number_cons, mul_comm (p ^ e), ← divisorSum_eq htail] using
      layeredGapBound_sound (e := e) (number_pos htail.1) hp hf hn hd hg

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

/-- A covered interval reaching the midpoint of the full divisor total
extends to its reflection by taking complements. -/
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

private theorem properSum_coordinatePower {rest : Coordinates} {p : ℕ}
    (hv : PrimeCoordinates rest) (hp : p.Prime) (hf : ¬ p ∣ number rest) (e : ℕ) :
    ∑ d ∈ (number rest * p ^ e).properDivisors, d =
      divisorSum rest * powerSum p e - number rest * p ^ e := by
  have hs := Nat.sum_divisors_eq_sum_properDivisors_add_self (n := number rest * p ^ e)
  rw [((hp.coprime_iff_not_dvd.mpr hf).symm.pow_right e).sum_divisors_mul,
    Nat.sum_divisors_prime_pow hp, ← powerSum_eq_sum, ← divisorSum_eq hv] at hs
  omega

def liftCoverOk (fs : Coordinates) (p e a : ℕ) (data : CentralCoverData) : Bool :=
  let rest := fs.erase (p, e)
  let u := number rest
  let s := divisorSum rest
  let m := u * p ^ a
  let T := s * powerSum p a - m
  let v := p ^ (a + 1)
  data.ok m T &&
    decide (a ≤ e ∧ 0 < data.low ∧
      v * coordinateGap rest + 2 * data.low ≤ T + 1 ∧
      m + 2 * data.low ≤ T + v * (s - u) + 1)

/-- A small central certificate at one exponent verifies the interval for
the original core. The cofactor gap bound is evaluated arithmetically. -/
theorem liftCoverOk_sound {fs : Coordinates} {p e a : ℕ} {data : CentralCoverData}
    (hv : PrimeCoordinates fs) (hm : (p, e) ∈ fs) (h : liftCoverOk fs p e a data = true) :
    Covered (number fs).properDivisors data.low (divisorSum fs - number fs - data.low) := by
  obtain ⟨hrest, hp, hf, hnum⟩ := erase_coordinate hv hm
  let rest := fs.erase (p, e)
  obtain ⟨ds, hd, hds, hgap⟩ := coordinateGap_sound hrest
  simp only [liftCoverOk, Bool.and_eq_true, decide_eq_true_eq] at h
  have hsum := properSum_coordinatePower hrest hp hf a
  have hcover := CentralCoverData.sound hsum h.1
  have hcofactor : ∑ d ∈ (number rest).properDivisors, d = divisorSum rest - number rest := by
    have ht := Nat.sum_divisors_eq_sum_properDivisors_add_self (n := number rest)
    rw [← divisorSum_eq hrest] at ht
    dsimp [rest] at ht ⊢
    omega
  have hraised := cover_raise_coprime_prime_power_add (a := a)
    (number_pos hrest.1) hp hf h.2.2.1 hd hds hgap
    (by rw [hsum]; exact hcover) (by rw [hsum]; exact h.2.2.2.1)
    (by rw [hsum, hcofactor]; exact h.2.2.2.2) (e - a)
  rw [Nat.add_sub_of_le h.2.1, ← hnum] at hraised
  have hT := Nat.sum_divisors_eq_sum_properDivisors_add_self (n := number fs)
  rw [← divisorSum_eq hv] at hT
  rw [show divisorSum fs - number fs = ∑ d ∈ (number fs).properDivisors, d by omega]
  exact hraised

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

/-- The two initial rational budget tests, cleared of denominators. -/
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

/-- Follow the actual prime-power tail of a primitive abundant completion.
Every unfinished prefix is deficient, which supplies the fresh-prime bound
at each step. The two division-free budget inequalities remain valid as the
prefix grows. -/
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

/-- Append the fresh prime first, then the old full number, then the
remaining scaled proper divisors. The three budgets persist at all powers. -/
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

/-! Integer budgets for switching between two orders of adjacent divisor layers. -/

namespace OddWeirdSubproblems

/-- Sufficient conditions at the box minimum for either of the two central
interval lifts to apply at every later deficient prefix. -/
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

def centralCoverFromGrowth (fs : Coordinates) (growth : List ℕ) : CentralCoverData :=
  let ds := divisorsAtMost fs (min 1024 (number fs - 1))
  let seed := smallPrefix 1024 (sortDivisors 20 ds)
  let low := effectiveLow (subsetBits seed) seed.sum
  ⟨seed, growth, low, seed.sum - low⟩

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

def liftedSweepStep (b : Box) (first stop h shift p e a : ℕ) (data : CentralCoverData) : Bool :=
  let fs := b.minimum
  let n := number fs
  let s := divisorSum fs
  let slope := 2 * n - s + h
  liftCoverOk fs p e a data &&
    decide (s ≤ 2 * n ∧ (h = 0 ∨ (h ∣ n ∧ h < n)) ∧
      (shift = 0 ∨ shift = n) ∧
      s ≤ s - n - data.low + shift + slope * first ∧
      data.low + shift + slope * (stop - 1) ≤ s)

theorem liftedSweepStep_closes {b : Box} {first stop h shift p e a : ℕ} {data : CentralCoverData}
    (hmem : (p, e) ∈ b.minimum) (hok : liftedSweepStep b first stop h shift p e a data = true) :
    HeadRangeClosed b.slots 0 first stop := by
  simp only [liftedSweepStep, Bool.and_eq_true, decide_eq_true_eq] at hok
  apply headRange_of_valid_core
  intro hv
  exact headRange_squarefree rfl rfl hok.2.1 hok.2.2.1 hok.2.2.2.1
    (liftCoverOk_sound hv hmem hok.1) hok.2.2.2.2.1 hok.2.2.2.2.2

def readCentralCover (guided : Bool) (fs : Coordinates) (input : List ℕ) :
    Option (CentralCoverData × List ℕ) :=
  if guided then do
    let (growth, tail) ← decodeRankDivisors fs input
    pure (centralCoverFromGrowth fs growth, tail)
  else some (buildCentralCover fs, input)

private def certifiedLiftedAction (b : Box) (first top selector : ℕ) (data : List ℕ) :
    Option (ℕ × List ℕ) := do
  let (slot, rest) ← readVarNat 64 data
  let (gap, rest) ← readVarNat 64 rest
  let (p, e) ← b.minimum[slot / 8]?
  let base := (p, slot % 8) :: b.minimum.erase (p, e)
  let (cert, rest) ← readCentralCover (decide (32 ≤ selector)) base rest
  let j := (selector % 32) / 2
  let h := if j < 2 then j else (b.slots[j - 2]?.map Slot.prime).getD 0
  let shift := (selector % 2) * number b.minimum
  let stop := min top (first + gap)
  if liftedSweepStep b first stop h shift p e (slot % 8) cert then some (stop, rest) else none

private theorem certifiedLiftedAction_sound {b : Box} {first top selector stop : ℕ} {data tail : List ℕ}
    (hc : certifiedLiftedAction b first top selector data = some (stop, tail)) :
    HeadRangeClosed b.slots 0 first stop := by
  unfold certifiedLiftedAction at hc
  obtain ⟨⟨slot, rest⟩, _, hc⟩ := Option.bind_eq_some_iff.mp hc
  dsimp only at hc
  obtain ⟨⟨gap, rest'⟩, _, hc⟩ := Option.bind_eq_some_iff.mp hc
  dsimp only at hc
  obtain ⟨⟨p, e⟩, hslot, hc⟩ := Option.bind_eq_some_iff.mp hc
  dsimp only at hc
  obtain ⟨⟨cert, rest''⟩, _, hc⟩ := Option.bind_eq_some_iff.mp hc
  dsimp only at hc
  have hm := List.mem_of_getElem? hslot
  generalize hok : liftedSweepStep b first (min top (first + gap)) _ _ p e (slot % 8) cert = ok at hc
  cases ok
  · contradiction
  · have he : min top (first + gap) = stop := by simpa using congrArg (Option.map Prod.fst) hc
    exact he ▸ liftedSweepStep_closes hm hok

def liftedSweep : SweepVerifier where
  run b first top data := do
    let (tag, rest) ← readVarNat 64 data
    if tag < 32 then (SweepVerifier.ofActions decodeStreamAction).run b first top data
    else certifiedLiftedAction b first top (tag - 32) rest
  sound := by
    intro b first top data stop tail h
    obtain ⟨⟨tag, rest⟩, _, h⟩ := Option.bind_eq_some_iff.mp h
    dsimp only at h
    split at h
    · exact (SweepVerifier.ofActions decodeStreamAction).sound h
    · exact certifiedLiftedAction_sound h

end OddWeirdSubproblems

namespace OddWeirdSubproblems

/-- The modulus carried by the minimum prefix and the divisor sums at its
fixed exponents. -/
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

/-- The modulus survives all admissible exponent increases, and adjoining
any tail preserves both divisibilities. -/
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

theorem paletteModulus_dvd_of_matches {b : Box} {xs ys : Coordinates}
    (hmatch : b.Matches xs ys) :
    paletteModulus b ∣ 2 * number (xs ++ ys) ∧
      paletteModulus b ∣ divisorSum (xs ++ ys) :=
  paletteModulus_dvd_append hmatch.1 ys

/-- In particular, the fixed modulus persists at each intermediate prefix
formed by adjoining the first \(j\) coordinates of the fresh tail. -/
theorem paletteModulus_dvd_take {b : Box} {xs ys : Coordinates}
    (hmatch : b.Matches xs ys) (j : ℕ) :
    paletteModulus b ∣ 2 * number (xs ++ ys.take j) ∧
      paletteModulus b ∣ divisorSum (xs ++ ys.take j) :=
  paletteModulus_dvd_append hmatch.1 (ys.take j)

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

/-- Central coverage, low subset sums, and the arithmetic budgets exclude
every weird completion of the box. -/
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

def paletteBudgetsOk : Box → ℕ → CentralCoverData → Bool :=
  paletteBudgetsOkWith false

theorem paletteBudgetsOk_closes {b : Box} {G : ℕ} {data : CentralCoverData}
    (hdata : PrimeCoordinates b.minimum →
      Covered (number b.minimum).properDivisors data.low
        (divisorSum b.minimum - number b.minimum - data.low) ∧
      data.seed.Nodup ∧ data.seed.toFinset ⊆ (number b.minimum).properDivisors)
    (hok : paletteBudgetsOk b G data = true) : b.Closed :=
  paletteBudgetsOkWith_closes hdata hok

theorem CentralCoverData.seed_sound {data : CentralCoverData} {n T : ℕ}
    (hok : data.ok n T = true) : data.seed.Nodup ∧ data.seed.toFinset ⊆ n.properDivisors := by
  simp only [CentralCoverData.ok, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨hnodup, hseed⟩ := divisorListOk_sound hok.1.1.1
  refine ⟨(List.nodup_append.mp hnodup).1, ?_⟩
  intro x hx
  exact hseed (List.mem_toFinset.mpr (List.mem_append_left _ (List.mem_toFinset.mp hx)))

def paletteWithOk (b : Box) (G : ℕ) (data : CentralCoverData) : Bool :=
  data.ok (number b.minimum) (divisorSum b.minimum - number b.minimum) && paletteBudgetsOk b G data

theorem paletteWithOk_closes {b : Box} {G : ℕ} {data : CentralCoverData}
    (hok : paletteWithOk b G data = true) : b.Closed := by
  obtain ⟨hdata, hcheck⟩ := Bool.and_eq_true_iff.mp hok
  apply paletteBudgetsOk_closes _ hcheck
  intro hv
  exact ⟨CentralCoverData.sound (properSum_of_validCoordinates hv) hdata, CentralCoverData.seed_sound hdata⟩

def paletteLiftOk (b : Box) (G p e a : ℕ) (data : CentralCoverData) : Bool :=
  liftCoverOk b.minimum p e a data && paletteBudgetsOk b G data

theorem paletteLiftOk_closes {b : Box} {G p e a : ℕ} {data : CentralCoverData}
    (hmem : (p, e) ∈ b.minimum) (hok : paletteLiftOk b G p e a data = true) : b.Closed := by
  obtain ⟨hdata, hcheck⟩ := Bool.and_eq_true_iff.mp hok
  apply paletteBudgetsOk_closes _ hcheck
  intro hv
  have hc := liftCoverOk_sound hv hmem hdata
  simp only [liftCoverOk, Bool.and_eq_true, decide_eq_true_eq] at hdata
  obtain ⟨_, _, _, heq⟩ := erase_coordinate hv hmem
  obtain ⟨hsnd, hsub⟩ := CentralCoverData.seed_sound hdata.1
  have hdiv : number (b.minimum.erase (p, e)) * p ^ a ∣ number b.minimum := by
    rw [heq]
    exact Nat.mul_dvd_mul_left _ (pow_dvd_pow p hdata.2.1)
  exact ⟨hc, hsnd, hsub.trans (properDivisors_subset_of_dvd (number_pos hv.1) hdiv)⟩

def paletteOk (b : Box) (G : ℕ) : Bool := paletteWithOk b G (buildCentralCover b.minimum)

theorem paletteOk_closes {b : Box} {G : ℕ} (h : paletteOk b G = true) : b.Closed :=
  paletteWithOk_closes h

end OddWeirdSubproblems

/-! Build a central interval from a short prefix of a box's known factors. -/

namespace OddWeirdSubproblems

open Finset

/-- At each known prime, check the two inequalities for lifting the cover
to all powers of that prime. -/
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

def prefixPaletteOk : Box → ℕ → ℕ → Bool := prefixPaletteOkWith false

theorem prefixPaletteOk_closes {b : Box} {G k : ℕ} (hok : prefixPaletteOk b G k = true) :
    b.Closed := prefixPaletteOkWith_closes hok

end OddWeirdSubproblems

/-! Check a squarefree prime interval using a central cover rebuilt from a short factor prefix. -/

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

/-- The large picked divisors and the small bitset seed are listed in
increasing order. The optional shift may lie on either side of the seed. -/
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

def guidedPointWitness (b : Box) (slot h : ℕ) (ranks : List ℕ) : List ℕ :=
  let fs := b.minimum
  let rest := fs.eraseIdx slot
  let k := pivotPosition rest
  let (p, e) := rest[k]?.getD (1, 0)
  let shift := (fs[slot]?.map Prod.fst).getD 0 * h
  let target := divisorSum fs - 2 * number fs - shift
  let (ds, small) := reconstructLargePicks (rest.eraseIdx k) p e ranks (number rest) target
  let short := smallPrefix 1024 (sortDivisors 20 (divisorsAtMost rest 1024))
  let seed := bitWitness short small
  sortDivisors 20 (if shift = 0 then ds ++ seed else shift :: (ds ++ seed))

theorem guidedPointWitness_closes {b : Box} {slot h : ℕ} {ranks : List ℕ}
    (hok : witnessOk (number b.minimum) (divisorSum b.minimum)
      (guidedPointWitness b slot h ranks) = true) : b.Closed :=
  witnessOk_closes hok

def decodeGuidedPoint (b : Box) (data : List ℕ) : Option (List ℕ × List ℕ) := do
  let (tag, rest) ← readVarNat 64 data
  let i := tag / 8
  let j := tag % 8
  let fs := b.minimum
  let h := if j < 2 then j else ((fs.eraseIdx i)[j - 2]?.map Prod.fst).getD 0
  let (ranks, rest) ← readLengthPrefixed rest
  pure (guidedPointWitness b i h ranks, rest)

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

/-- Use a direct rank hint for the larger cofactors and the single-byte
cofactor hint for the smaller ones. Both cases use the same witness checks. -/
def hybridPoint : PointReplay where
  verify b data := match data with
    | [] => none
    | tag :: rest =>
      if 64 ≤ tag then guidedBitPoint.verify b ((tag - 64) :: rest)
      else (PointReplay.ofDivisors decodePoint).verify b data
  sound := by
    intro b data tail h
    cases data with
    | nil => contradiction
    | cons tag rest =>
      dsimp only at h
      split at h
      · exact guidedBitPoint.sound h
      · exact (PointReplay.ofDivisors decodePoint).sound h

end OddWeirdSubproblems

/-! Input codecs for the bounded stream replay. -/

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

def checkBoundedBlockUsing (oddSplit : OddSplitReplay) (fast : Bool) (B fuel : ℕ) (b : Box) (cuts : List Box) (count value : ℕ) : Bool :=
  match expandPackedTokens count (bytesFromNat count value) 0 0 with
  | none => false
  | some data =>
    match replayWithSizeLimit true fast B boundedPoint boundedSweep (boundedPalettePruningWith fast) oddSplit
        (fun q => cuts.any (boxEqual q)) fuel b data with
    | some [] => true
    | _ => false

theorem checkBoundedBlockUsing_closes {oddSplit : OddSplitReplay} {fast : Bool} {B : ℕ} {b : Box} {cuts : List Box}
    (hcuts : ClosedBelowCuts B cuts) (fuel count value : ℕ)
    (hlo : 1 < b.next) (hodd : Odd b.next)
    (h : checkBoundedBlockUsing oddSplit fast B fuel b cuts count value = true) :
    b.ClosedBelow B := by
  unfold checkBoundedBlockUsing at h
  split at h
  · contradiction
  · split at h
    · apply replayWithSizeLimit_closes _ hlo hodd ‹_›
      intro q hq
      obtain ⟨c, hc, he⟩ := List.any_eq_true.mp hq
      exact (boxEqual_iff_eq q c).mp he ▸ hcuts.closedOfMem hc
    · contradiction

def checkBoundedBlockWith : Bool → ℕ → ℕ → Box → List Box → ℕ → ℕ → Bool :=
  checkBoundedBlockUsing .none

theorem checkBoundedBlockWith_closes {fast : Bool} {B : ℕ} {b : Box} {cuts : List Box}
    (hcuts : ClosedBelowCuts B cuts) (fuel count value : ℕ)
    (hlo : 1 < b.next) (hodd : Odd b.next)
    (h : checkBoundedBlockWith fast B fuel b cuts count value = true) :
    b.ClosedBelow B :=
  checkBoundedBlockUsing_closes hcuts fuel count value hlo hodd h

def checkBoundedBlock : ℕ → ℕ → Box → List Box → ℕ → ℕ → Bool :=
  checkBoundedBlockWith false

theorem checkBoundedBlock_closes {B : ℕ} {b : Box} {cuts : List Box}
    (hcuts : ClosedBelowCuts B cuts) (fuel count value : ℕ)
    (hlo : 1 < b.next) (hodd : Odd b.next)
    (h : checkBoundedBlock B fuel b cuts count value = true) :
    b.ClosedBelow B :=
  checkBoundedBlockWith_closes hcuts fuel count value hlo hodd h

end OddWeirdSubproblems

/-! A conditional modulus from an odd exponent at an open slot. -/

namespace OddWeirdSubproblems

theorem primeSucc_dvd_powerSum_of_odd (p : ℕ) {e : ℕ} (he : Odd e) :
    p + 1 ∣ powerSum p e := by
  obtain ⟨k, rfl⟩ := he
  induction k with
  | zero => simp [powerSum, Nat.add_comm]
  | succ k ih =>
    rw [show 2 * (k + 1) + 1 = 2 * k + 1 + 2 by omega, powerSum, powerSum]
    rw [Nat.add_assoc]
    apply Nat.dvd_add ih
    have heq : 2 * k + 2 + 1 = (2 * k + 1 + 1) + 1 := by omega
    rw [heq, pow_succ p (2 * k + 1 + 1)]
    have hs : p ^ (2 * k + 1 + 1) + p ^ (2 * k + 1 + 1) * p =
        p ^ (2 * k + 1 + 1) * (p + 1) := by
      rw [Nat.mul_add, Nat.mul_one, Nat.add_comm]
    rw [hs]
    exact dvd_mul_left _ _

private def fixedSigma (ss : List Slot) : ℕ :=
  ((ss.filter Slot.fixed).map fun s => powerSum s.prime s.exponent).prod

private theorem oddSlot_product_dvd {ss : List Slot} {xs : Coordinates} {i : ℕ} {s : Slot}
    {x : ℕ × ℕ} (hfit : List.Forall₂ Slot.Fits ss xs)
    (hi : ss[i]? = some s) (hx : xs[i]? = some x) (hopen : s.fixed = false) (he : Odd x.2) :
    fixedSigma ss * (s.prime + 1) ∣ divisorSum xs := by
  induction hfit generalizing i with
  | nil => simp at hi
  | @cons t y ts ys ht _ ih =>
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hi hx
      subst t
      subst y
      have hd : s.prime + 1 ∣ powerSum x.1 x.2 := by
        rw [ht.2.1]
        exact primeSucc_dvd_powerSum_of_odd x.1 he
      have htail : fixedSigma ts ∣ divisorSum ys := fixedPowerSum_prod_dvd ‹_›
      simpa only [fixedSigma, List.filter_cons, hopen, Bool.false_eq_true, if_false, divisorSum,
        List.map_cons, List.prod_cons, Nat.mul_comm] using Nat.mul_dvd_mul hd htail
    | succ i =>
      simp only [List.getElem?_cons_succ] at hi hx
      have hd := ih hi hx
      cases htFixed : t.fixed
      · simpa only [fixedSigma, List.filter_cons, htFixed, Bool.false_eq_true, if_false, divisorSum,
          List.map_cons, List.prod_cons] using dvd_mul_of_dvd_right hd (powerSum y.1 y.2)
      · have heq : powerSum t.prime t.exponent = powerSum y.1 y.2 := by
          rw [ht.2.1, ht.2.2.2 htFixed]
        simpa only [fixedSigma, List.filter_cons, htFixed, if_true, divisorSum, List.map_cons,
          List.prod_cons, heq, Nat.mul_assoc] using
          Nat.mul_dvd_mul_left (powerSum y.1 y.2) hd

/-- This stronger modulus persists through all completions of the old slots
in which the specified open slot has odd exponent. -/
def oddSlotModulus (b : Box) (s : Slot) : ℕ :=
  Nat.gcd (2 * number b.minimum) (fixedSigma b.slots * (s.prime + 1))

theorem oddSlotModulus_dvd_append {b : Box} {xs : Coordinates} {i : ℕ} {s : Slot}
    {x : ℕ × ℕ} (hfit : List.Forall₂ Slot.Fits b.slots xs)
    (hi : b.slots[i]? = some s) (hx : xs[i]? = some x) (hopen : s.fixed = false) (he : Odd x.2)
    (tail : Coordinates) :
    oddSlotModulus b s ∣ 2 * number (xs ++ tail) ∧ oddSlotModulus b s ∣ divisorSum (xs ++ tail) := by
  constructor
  · rw [number_append]
    exact (Nat.gcd_dvd_left _ _).trans
      (Nat.mul_dvd_mul_left 2 (dvd_mul_of_dvd_left (minimum_dvd hfit) _))
  · rw [divisorSum_append]
    exact dvd_mul_of_dvd_left
      ((Nat.gcd_dvd_right _ _).trans (oddSlot_product_dvd hfit hi hx hopen he)) _

end OddWeirdSubproblems

/-! Exclude the odd-exponent part of a box using its stronger divisor-sum modulus. -/

namespace OddWeirdSubproblems

def oddPrefixPaletteOk (b : Box) (s : Slot) (G k : ℕ) : Bool :=
  let pre := b.minimum.take k
  let data := buildCentralCover pre
  data.ok (number pre) (divisorSum pre - number pre) &&
    decide (2 * data.low ≤ divisorSum pre - number pre) &&
    knownTailLiftOk data.low G pre (b.minimum.drop k) &&
    paletteBudgetsOkAt true b (oddSlotModulus b s) G data

theorem oddPrefixPaletteOk_excludes {b : Box} {i G k : ℕ} {s : Slot}
    (hi : b.slots[i]? = some s) (hopen : s.fixed = false) (hok : oddPrefixPaletteOk b s G k = true)
    {xs ys : Coordinates} {x : ℕ × ℕ}
    (hmatch : b.Matches xs ys) (hx : xs[i]? = some x) (he : Odd x.2)
    (hv : PrimeCoordinates (xs ++ ys)) (hw : (number (xs ++ ys)).Weird)
    (hproper : ∀ d ∈ (number (xs ++ ys)).properDivisors, d.Deficient) : False := by
  simp only [oddPrefixPaletteOk, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨hdata, hCT⟩, htail⟩, hbudget⟩ := hok
  apply paletteBudgetsOkAt_excludes
    (Q := fun cs => ∃ x, cs[i]? = some x ∧ Odd x.2) _ _ hbudget xs ys hmatch ⟨x, hx, he⟩
    hv hw hproper
  · rintro cs hfit ⟨y, hy, hyodd⟩ ts
    exact oddSlotModulus_dvd_append hfit hi hy hopen hyodd ts
  · intro hvalid
    have hstats := hbudget
    simp only [paletteBudgetsOkAt, Bool.and_eq_true, decide_eq_true_eq] at hstats
    exact prefixCoverFromData hvalid hdata hCT hstats.1.1.2.1 hstats.1.1.2.2.1
      hstats.1.1.1.1 htail

private theorem forall₂_slot_at {ss : List Slot} {xs : Coordinates} {i : ℕ} {s : Slot}
    (hfit : List.Forall₂ Slot.Fits ss xs) (hi : ss[i]? = some s) :
    ∃ x, xs[i]? = some x ∧ s.Fits x ∧
      ∀ t : Slot, t.Fits x → List.Forall₂ Slot.Fits (ss.set i t) xs := by
  induction hfit generalizing i with
  | nil => simp at hi
  | @cons t x ss xs hf rest ih =>
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
      subst t
      exact ⟨x, rfl, hf, fun v hv => .cons hv rest⟩
    | succ i =>
      obtain ⟨y, hy, hfy, hreplace⟩ := ih hi
      exact ⟨y, hy, hfy, fun v hv => .cons hf (hreplace v hv)⟩

/-- An odd-exponent palette exclusion lets the next split skip odd
exponents immediately. Each child can be proved as an ordinary box. -/
theorem closeBelow_of_oddSlotSplit {b : Box} {B i G k : ℕ} {s : Slot}
    (hi : b.slots[i]? = some s) (hopen : s.fixed = false)
    (hok : oddPrefixPaletteOk b s G k = true)
    (hfixed : Even s.exponent →
      ({b with slots := b.slots.set i {s with fixed := true}} : Box).ClosedBelow B)
    (hraise : let step := if Even s.exponent then 2 else 1
      ({b with slots := b.slots.set i {s with exponent := s.exponent + step}} : Box).ClosedBelow B) :
    b.ClosedBelow B := by
  intro xs ys hmatch hv hsize hw hproper
  obtain ⟨x, hx, hfit, hreplace⟩ := forall₂_slot_at hmatch.1 hi
  obtain heven | hodd := Nat.even_or_odd x.2
  · have hmin := hfit.2.2.1
    by_cases hs : Even s.exponent
    · by_cases heq : s.exponent = x.2
      · exact hfixed hs xs ys
          ⟨hreplace _ ⟨hfit.1, hfit.2.1, hmin, fun _ => heq⟩, hmatch.2⟩ hv hsize hw hproper
      · have hstep : s.exponent + 2 ≤ x.2 := by
          obtain ⟨a, ha⟩ := hs
          obtain ⟨c, hc⟩ := heven
          omega
        exact hraise xs ys
          ⟨hreplace _ ⟨hfit.1, hfit.2.1, by simp [hs, hstep], by simp [hopen]⟩,
            hmatch.2⟩ hv hsize hw hproper
    · have hstep : s.exponent + 1 ≤ x.2 := by
        have hne : s.exponent ≠ x.2 := fun heq => hs (heq.symm ▸ heven)
        omega
      exact hraise xs ys
        ⟨hreplace _ ⟨hfit.1, hfit.2.1, by simp [hs, hstep], by simp [hopen]⟩,
          hmatch.2⟩ hv hsize hw hproper
  · exact oddPrefixPaletteOk_excludes hi hopen hok hmatch hx hodd hv hw hproper

end OddWeirdSubproblems

/-! Decode optional checked odd-exponent exclusions in the bounded replay. -/

namespace OddWeirdSubproblems

private def readOddSplit (b : Box) (data : List ℕ) : Option (Option (ℕ × Slot) × List ℕ) := do
  let (tag, rest) ← readVarNat 64 data
  if tag = 0 then some (none, rest)
  else do
    let s ← b.slots[tag - 1]?
    let (G, rest) ← readVarNat 64 rest
    let (k, rest) ← readVarNat 64 rest
    if !s.fixed && oddPrefixPaletteOk b s G k then some (some (tag - 1, s), rest)
    else none

def fangOddSplit : OddSplitReplay where
  verify := readOddSplit
  sound := by
    intro b data i s rest B h
    unfold readOddSplit at h
    obtain ⟨⟨tag, input⟩, _, h⟩ := Option.bind_eq_some_iff.mp h
    dsimp only at h
    split at h
    · simp at h
    · obtain ⟨s', hs, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨⟨G, input⟩, _, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨⟨k, remaining⟩, _, h⟩ := Option.bind_eq_some_iff.mp h
      dsimp only at h
      split at h
      · have hgood : (!s'.fixed && oddPrefixPaletteOk b s' G k) = true := by assumption
        have ⟨he, htail⟩ := Prod.mk.inj (Option.some.inj h)
        have ⟨hi, hval⟩ := Prod.mk.inj (Option.some.inj he)
        subst i
        subst s
        obtain ⟨hopen, hcheck⟩ := Bool.and_eq_true_iff.mp hgood
        exact closeBelow_of_oddSlotSplit hs (by simpa using hopen) hcheck
      · contradiction

def checkParityBoundedBlock : ℕ → ℕ → Box → List Box → ℕ → ℕ → Bool :=
  checkBoundedBlockUsing fangOddSplit true

theorem checkParityBoundedBlock_closes {B : ℕ} {b : Box} {cuts : List Box}
    (hcuts : ClosedBelowCuts B cuts) (fuel count value : ℕ)
    (hlo : 1 < b.next) (hodd : Odd b.next)
    (h : checkParityBoundedBlock B fuel b cuts count value = true) :
    b.ClosedBelow B :=
  checkBoundedBlockUsing_closes hcuts fuel count value hlo hodd h

end OddWeirdSubproblems

namespace OddWeirdSubproblems


set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangFiveEightAt6Block0 : (⟨[⟨5,6,true⟩,⟨7,1,false⟩,⟨11,1,false⟩,⟨13,1,false⟩,⟨19,1,false⟩,⟨29,1,false⟩],31,2⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkParityBoundedBlock_closes (B := 10 ^ 21) (.nil)
    20 129 0x4040505000c0193010d3601062601080100051a010e220104040400030500073f010304060003040607000533010f01010941012502010004001344010001000b1401040100092e010304040300050401030408000005000728010304040300051601030402000a0801060004040505000504010404070300060101000100
    (by decide) ⟨15, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangFiveEightAt6Block1 : (⟨[⟨5,6,true⟩,⟨7,2,false⟩,⟨11,2,false⟩,⟨13,2,true⟩,⟨19,1,false⟩,⟨23,1,false⟩,⟨31,1,false⟩],39,1⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkParityBoundedBlock_closes (B := 10 ^ 21) (.nil)
    15 68 0x60100072b010e31010601000f43014901000649010a0e01091401090a01040402000811010304030408000304080900120101003d020100000304000035020100000f00
    (by decide) ⟨19, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangFiveEightAt6Block2 : (⟨[⟨5,6,true⟩,⟨7,1,false⟩,⟨11,1,false⟩,⟨13,2,true⟩,⟨19,1,false⟩,⟨23,1,false⟩],33,2⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkParityBoundedBlock_closes (B := 10 ^ 21) (.nil)
    16 60 0x304050004050005480106040107000404050500093a010801000d1001040400030005240117010105040106040700000003040509002a0101000100
    (by decide) ⟨16, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangFiveEightAt6Block3 : (⟨[⟨5,6,true⟩,⟨7,1,false⟩,⟨11,1,false⟩,⟨13,2,true⟩,⟨19,1,false⟩,⟨23,1,false⟩,⟨29,1,false⟩],31,1⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkParityBoundedBlock_closes (B := 10 ^ 21) (.nil)
    15 104 0x404030403040807000b3701113401470100064e010b1001070100060101092001050100070e01030100055801070100070a010801000501011013012f02010000030407000a01010c0c010b0e010501000a0101050a010304040407000404070900080101000100
    (by decide) ⟨15, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangFiveEightAt6Block4 : (⟨[⟨5,6,true⟩,⟨7,1,false⟩,⟨11,1,false⟩,⟨13,4,true⟩,⟨19,1,false⟩,⟨23,1,false⟩,⟨31,1,false⟩],33,1⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkParityBoundedBlock_closes (B := 10 ^ 21) (.nil)
    14 57 0x3040200124c013f02010300060b013702010300072a0105040106040803000d1401080100110e010304020017010100270201000000000800
    (by decide) ⟨16, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangFiveEightAt6Block5 : (⟨[⟨5,6,true⟩,⟨7,1,false⟩,⟨11,1,false⟩,⟨13,4,true⟩,⟨19,1,false⟩,⟨23,1,false⟩],31,2⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkParityBoundedBlock_closes (B := 10 ^ 21) (.cons fangFiveEightAt6Block4 (.nil))
    15 37 0x6040404070004040709001826010504010604070003040700000003040c00210101000100
    (by decide) ⟨15, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangFiveEightAt6Block6 : (⟨[⟨5,6,true⟩,⟨7,1,false⟩,⟨11,1,false⟩,⟨13,6,false⟩,⟨19,1,false⟩,⟨23,1,false⟩],25,2⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkParityBoundedBlock_closes (B := 10 ^ 21) (.nil)
    16 65 0x304030404000623012b01000933010915010304060408050005290103040200142601270201000000000404070006040700030405120016010100060404000500
    (by decide) ⟨12, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangFiveEightAt6Block7 : (⟨[⟨5,6,true⟩,⟨7,1,false⟩,⟨11,1,false⟩,⟨13,2,true⟩,⟨19,1,false⟩,⟨23,1,false⟩],25,2⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkParityBoundedBlock_closes (B := 10 ^ 21) (.cons fangFiveEightAt6Block3 (.cons fangFiveEightAt6Block2 (.cons fangFiveEightAt6Block1 (.nil))))
    20 100 0x304020005200105040106040803000a010105040103040803000b52010123480c362a1801862c0d01d203034818062a01170c240116190005140145262204029e01fb1e23252c1c050c0f001d1f01030402001401010a0d012702010300090101000100
    (by decide) ⟨12, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangFiveEightAt6Block8 : (⟨[⟨5,6,true⟩,⟨7,1,false⟩,⟨11,1,false⟩,⟨13,2,true⟩,⟨17,1,false⟩],31,3⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkParityBoundedBlock_closes (B := 10 ^ 21) (.nil)
    16 39 0x516011a3e010610011424011c01010504010504080000050005040105040703000a0101000100
    (by decide) ⟨15, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangFiveEightAt6Block9 : (⟨[⟨5,6,true⟩,⟨7,1,false⟩,⟨11,1,false⟩,⟨13,2,true⟩,⟨17,1,false⟩,⟨29,1,false⟩,⟨37,1,false⟩],39,1⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkParityBoundedBlock_closes (B := 10 ^ 21) (.nil)
    13 41 0x404060300091e01133001062601100e01121a010504010504080300050701040402002d0101000100
    (by decide) ⟨19, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangFiveEightAt6Block10 : (⟨[⟨5,6,true⟩,⟨7,2,false⟩,⟨11,2,false⟩,⟨13,2,true⟩,⟨17,1,false⟩,⟨29,1,false⟩,⟨31,1,false⟩],35,1⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkParityBoundedBlock_closes (B := 10 ^ 21) (.nil)
    14 87 0x50100052d01183e013f01000d230105040103040803000d4f0137020103000a01010e2a01010102040820174732022e2070018f1c140b01b1040114000000041b00071001120a01030402000d0101002f020100000600
    (by decide) ⟨17, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangFiveEightAt6Block11 : (⟨[⟨5,6,true⟩,⟨7,1,false⟩,⟨11,1,false⟩,⟨13,2,true⟩,⟨17,1,false⟩,⟨29,1,false⟩,⟨31,1,false⟩],33,1⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkParityBoundedBlock_closes (B := 10 ^ 21) (.cons fangFiveEightAt6Block10 (.nil))
    16 34 0x260101181a0103040200090101050401050408030018010100230201000000000800
    (by decide) ⟨16, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangFiveEightAt6Block12 : (⟨[⟨5,6,true⟩,⟨7,1,false⟩,⟨11,1,false⟩,⟨13,4,true⟩,⟨17,1,false⟩,⟨29,1,false⟩,⟨31,1,false⟩],33,1⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkParityBoundedBlock_closes (B := 10 ^ 21) (.nil)
    14 51 0x30403040305000817011010010e2501040402000501010d080103040803001f0101140e0105040105040803001b0101000100
    (by decide) ⟨16, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangFiveEightAt6Block13 : (⟨[⟨5,6,true⟩,⟨7,1,false⟩,⟨11,1,false⟩,⟨13,4,true⟩,⟨17,1,false⟩,⟨29,1,false⟩],31,2⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkParityBoundedBlock_closes (B := 10 ^ 21) (.cons fangFiveEightAt6Block12 (.nil))
    14 44 0x1000e0e010b2a0105040803001801010d0e0108000000000500140e0105040105040703000c0101000100
    (by decide) ⟨15, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangFiveEightAt6Block14 : (⟨[⟨5,6,true⟩,⟨7,1,false⟩,⟨11,1,false⟩,⟨13,1,false⟩,⟨17,1,false⟩,⟨29,1,false⟩],31,2⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkParityBoundedBlock_closes (B := 10 ^ 21) (.cons fangFiveEightAt6Block11 (.cons fangFiveEightAt6Block9 (.cons fangFiveEightAt6Block13 (.nil))))
    17 62 0x40402000c1b01050402001001010e3e01120101173e0104040603000a240105040105040803000e010105040105040703000a0101050401050404000400
    (by decide) ⟨15, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangFiveEightAt6Block15 : (⟨[⟨5,6,true⟩,⟨7,1,false⟩,⟨11,1,false⟩,⟨13,2,true⟩,⟨17,1,false⟩,⟨23,1,false⟩,⟨43,1,false⟩],45,1⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkParityBoundedBlock_closes (B := 10 ^ 21) (.nil)
    14 44 0xb6701072201410201000005001931011225010a0601030400000005001010010d0101050401050407000400
    (by decide) ⟨22, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangFiveEightAt6Block16 : (⟨[⟨5,6,true⟩,⟨7,1,false⟩,⟨11,1,false⟩,⟨13,2,true⟩,⟨17,1,false⟩,⟨23,1,false⟩,⟨41,2,true⟩],43,1⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkParityBoundedBlock_closes (B := 10 ^ 21) (.nil)
    13 57 0xa01010b68010f27011d21010401000a3d0115360103019f24126c2e0294018102b1354f540c11000801010504010504080300140101000100
    (by decide) ⟨21, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangFiveEightAt6Block17 : (⟨[⟨5,6,true⟩,⟨7,2,false⟩,⟨11,2,false⟩,⟨13,2,true⟩,⟨17,1,true⟩,⟨23,1,false⟩,⟨37,1,false⟩],55,1⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkParityBoundedBlock_closes (B := 10 ^ 21) (.nil)
    11 92 0x301000637010f710149020202080408301d73019c3801d90248044028240112050200001b00064201063e010801010d1f013002a01848072f01973a7201de150201010e12000d180103040304050408000504080b000c0101000100
    (by decide) ⟨27, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangFiveEightAt6Block18 : (⟨[⟨5,6,true⟩,⟨7,2,false⟩,⟨11,1,true⟩,⟨13,2,true⟩,⟨17,1,false⟩,⟨23,1,false⟩,⟨37,1,false⟩],39,1⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkParityBoundedBlock_closes (B := 10 ^ 21) (.nil)
    13 77 0x901011b77012d020103001516010e0101050401050408000000666c02561401e10b54035a0c2a12300601100000000601da3c0c018f7701ad100c0242100c24102e02011231001a0101000100
    (by decide) ⟨19, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangFiveEightAt6Block19 : (⟨[⟨5,6,true⟩,⟨7,1,false⟩,⟨11,1,false⟩,⟨13,2,true⟩,⟨17,1,false⟩,⟨23,1,false⟩],39,2⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkParityBoundedBlock_closes (B := 10 ^ 21) (.cons fangFiveEightAt6Block15 (.cons fangFiveEightAt6Block16 (.nil)))
    17 39 0x30100124d010904010504070300091b010304050408000007001e1001050402002b0101000100
    (by decide) ⟨19, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangFiveEightAt6Block20 : (⟨[⟨5,6,true⟩,⟨7,2,false⟩,⟨11,2,false⟩,⟨13,2,true⟩,⟨17,1,true⟩,⟨23,1,false⟩,⟨31,1,false⟩],77,1⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkParityBoundedBlock_closes (B := 10 ^ 21) (.nil)
    14 112 0x3040200063f010c180aca10220bca0ac50c970ca4010ad80828220201101700083c010f2101710201000005000a29010d2b01125c01050c010652010621010f39015f0201030008310100000000030500072b010301000f270159020103000f010105040105040803000c0101000100
    (by decide) ⟨38, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangFiveEightAt6Block21 : (⟨[⟨5,6,true⟩,⟨7,2,false⟩,⟨11,1,true⟩,⟨13,2,true⟩,⟨17,1,false⟩,⟨23,1,false⟩,⟨31,1,false⟩],49,1⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkParityBoundedBlock_closes (B := 10 ^ 21) (.nil)
    12 110 0x701010d67014d0201000000060005540137350c0245081102c3422a01d2070e0006740101040618486c24481a2d1f01050c1903f006600a03141600051b010a01012b4a011139014a261a1c0393780b301f2a24010c0e000f1a0103040304050408000504080b00100101000100
    (by decide) ⟨24, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangFiveEightAt6Block22 : (⟨[⟨5,6,true⟩,⟨7,2,false⟩,⟨11,1,false⟩,⟨13,2,true⟩,⟨17,1,false⟩,⟨23,1,false⟩,⟨31,1,false⟩],33,1⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkParityBoundedBlock_closes (B := 10 ^ 21) (.cons fangFiveEightAt6Block21 (.cons fangFiveEightAt6Block20 (.nil)))
    19 131 0x5040504030400000309000d3401070e019502010000050600071a0101870201000003070005040106510104040200120101072a0100007102010000245b1101b4019001a706032d4248090f0607231831121d00050601080100050c0100000200080a0105040304080500100101006502000607014d02010000000031020100000c00
    (by decide) ⟨16, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangFiveEightAt6Block23 : (⟨[⟨5,6,true⟩,⟨7,1,false⟩,⟨11,1,false⟩,⟨13,2,true⟩,⟨17,1,false⟩,⟨23,1,false⟩],33,2⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkParityBoundedBlock_closes (B := 10 ^ 21) (.cons fangFiveEightAt6Block19 (.cons fangFiveEightAt6Block18 (.cons fangFiveEightAt6Block17 (.nil))))
    17 88 0x5040504080500074d010c540151020103000838010501000b3a014d020100000c184801d8060c2b386266036f4818062a1804260714000000051f0009100105040000000003040809000d100143020103000e0101000100
    (by decide) ⟨16, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangFiveEightAt6Block24 : (⟨[⟨5,6,true⟩,⟨7,2,false⟩,⟨11,1,true⟩,⟨13,2,true⟩,⟨17,2,false⟩,⟨23,1,false⟩,⟨29,1,false⟩],55,1⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkParityBoundedBlock_closes (B := 10 ^ 21) (.nil)
    15 118 0x304080005050009250103010018019c010304030300050e010801000b6f01030402001052014f02010000030407000a520101920cb801b50e8905d95f04f1100290010a00000001af07960ebb028c0686170d01a206aa0190090605f724093f24491231001601010504010504080300170101000100
    (by decide) ⟨27, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangFiveEightAt6Block25 : (⟨[⟨5,6,true⟩,⟨7,2,false⟩,⟨11,2,false⟩,⟨13,2,true⟩,⟨17,1,true⟩,⟨23,1,false⟩,⟨29,1,false⟩],91,1⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkParityBoundedBlock_closes (B := 10 ^ 21) (.nil)
    13 157 0x3040404040500054d0101950201000003040504000001890201000028019010060a02af2c02023a460804140817010112000000002b00133c010b7d010c24017d020100001301d15a2103b52f166606010a00001400115e016d0201000000003f05f40e8001a23106dd05bd520606180c24010e1b000501010d1801050401050100050801000002000e10010504030408000304080900140101000100
    (by decide) ⟨45, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangFiveEightAt6Block26 : (⟨[⟨5,6,true⟩,⟨7,2,false⟩,⟨11,1,false⟩,⟨13,2,true⟩,⟨17,1,false⟩,⟨23,1,false⟩,⟨29,1,false⟩],31,1⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkParityBoundedBlock_closes (B := 10 ^ 21) (.cons fangFiveEightAt6Block24 (.cons fangFiveEightAt6Block25 (.nil)))
    16 192 0x304030401ed020108000601870101db0201000004040800075a01bf0100066101040404040400054a01a90207e06607bc019d15ad01c107bc3002030a05021500063f01000001970400062c01040400000304080004090005060103040304080500112e0101810201000000005b0201000003040504080005040816000751011801010c39013f02010000010102080c04080c180202080c300202080c240b011e27030c131c0828180c01202600050701030402000b01010037020100000600
    (by decide) ⟨15, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangFiveEightAt6Block27 : (⟨[⟨5,6,true⟩,⟨7,1,false⟩,⟨11,1,false⟩,⟨13,2,true⟩,⟨17,1,false⟩,⟨23,1,false⟩,⟨29,1,false⟩],31,1⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkParityBoundedBlock_closes (B := 10 ^ 21) (.cons fangFiveEightAt6Block26 (.nil))
    15 42 0x150101144001072c01070100092001172201091c01040402000d010105040105040803001a0101000100
    (by decide) ⟨15, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangFiveEightAt6Block28 : (⟨[⟨5,6,true⟩,⟨7,2,false⟩,⟨11,1,true⟩,⟨13,4,true⟩,⟨17,1,false⟩,⟨23,1,false⟩,⟨37,1,false⟩],39,1⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkParityBoundedBlock_closes (B := 10 ^ 21) (.nil)
    11 67 0x2e01010e0e0106010105040105040800010201010204010102080101020805074815000507010957010102080c015f186004080b0160787771082a1500120101000100
    (by decide) ⟨19, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangFiveEightAt6Block29 : (⟨[⟨5,6,true⟩,⟨7,1,false⟩,⟨11,1,false⟩,⟨13,4,true⟩,⟨17,1,false⟩,⟨23,1,false⟩],39,2⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkParityBoundedBlock_closes (B := 10 ^ 21) (.nil)
    15 47 0x50402000544010504080004000f19010715013101000d250105040105040703000f120133020103002b0101000100
    (by decide) ⟨19, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangFiveEightAt6Block30 : (⟨[⟨5,6,true⟩,⟨7,2,false⟩,⟨11,1,true⟩,⟨13,4,true⟩,⟨17,1,false⟩,⟨23,1,false⟩,⟨31,1,false⟩],49,1⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkParityBoundedBlock_closes (B := 10 ^ 21) (.nil)
    11 56 0x30402001b3e010196270101e101af282101ed28320a0f001423010e01010e23010304080005040807000b0e0139020103000d0101000100
    (by decide) ⟨24, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangFiveEightAt6Block31 : (⟨[⟨5,6,true⟩,⟨7,1,false⟩,⟨11,1,false⟩,⟨13,4,true⟩,⟨17,1,false⟩,⟨23,1,false⟩,⟨31,1,false⟩],33,1⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkParityBoundedBlock_closes (B := 10 ^ 21) (.cons fangFiveEightAt6Block30 (.nil))
    16 73 0x3040200063601101b016b02010000030403040504030c00114d01630201000005040700093001094c011224014f020103000f14010f01010c0a0105040105040803000c0101000100
    (by decide) ⟨16, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangFiveEightAt6Block32 : (⟨[⟨5,6,true⟩,⟨7,2,false⟩,⟨11,1,true⟩,⟨13,4,true⟩,⟨17,1,false⟩,⟨23,1,false⟩,⟨29,1,false⟩],55,1⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkParityBoundedBlock_closes (B := 10 ^ 21) (.nil)
    13 43 0x304050403040707001314011419012041011a1d0141020103000b01010f120105040803000e0101000100
    (by decide) ⟨27, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangFiveEightAt6Block33 : (⟨[⟨5,6,true⟩,⟨7,1,false⟩,⟨11,1,false⟩,⟨13,4,true⟩,⟨17,1,false⟩,⟨23,1,false⟩,⟨29,1,false⟩],31,1⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkParityBoundedBlock_closes (B := 10 ^ 21) (.cons fangFiveEightAt6Block32 (.nil))
    14 80 0x30402000516010b69010189020100000307000513010401000751017d02010000040403040304080003040810001114015f020103001501011212010b0101100c010504010504080300180101000100
    (by decide) ⟨15, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangFiveEightAt6Block34 : (⟨[⟨5,6,true⟩,⟨7,1,false⟩,⟨11,1,false⟩,⟨13,6,true⟩,⟨17,1,false⟩,⟨23,1,false⟩],31,2⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkParityBoundedBlock_closes (B := 10 ^ 21) (.nil)
    13 44 0x530010301001334010919010801000f1d010518010800050404001101010504010504070300140101000100
    (by decide) ⟨15, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangFiveEightAt6Block35 : (⟨[⟨5,6,true⟩,⟨7,1,false⟩,⟨11,1,false⟩,⟨13,6,false⟩,⟨17,1,false⟩,⟨23,1,false⟩],25,2⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkParityBoundedBlock_closes (B := 10 ^ 21) (.cons fangFiveEightAt6Block34 (.nil))
    14 33 0x40400000003040304070a00270101050401050408030018010100050404000500
    (by decide) ⟨12, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangFiveEightAt6Block36 : (⟨[⟨5,6,true⟩,⟨7,1,false⟩,⟨11,1,false⟩,⟨13,4,false⟩,⟨17,1,false⟩,⟨23,1,false⟩],25,2⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkParityBoundedBlock_closes (B := 10 ^ 21) (.cons fangFiveEightAt6Block35 (.cons fangFiveEightAt6Block33 (.cons fangFiveEightAt6Block31 (.cons fangFiveEightAt6Block29 (.cons fangFiveEightAt6Block28 (.nil))))))
    19 40 0xf1501030405040000030408000f01011225010801000f120139020103000f010100050404000500
    (by decide) ⟨12, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangFiveEightAt6Block37 : (⟨[⟨5,6,true⟩,⟨7,1,false⟩,⟨11,1,false⟩,⟨13,1,false⟩,⟨17,1,false⟩],25,3⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkParityBoundedBlock_closes (B := 10 ^ 21) (.cons fangFiveEightAt6Block14 (.cons fangFiveEightAt6Block8 (.nil)))
    17 52 0x1336011244010c0c0109180105040803000601010d1801080000030005040105040703000a010109040105040400000000000800
    (by decide) ⟨12, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangFiveEightAt6Block38 : (⟨[⟨5,6,true⟩,⟨7,2,false⟩,⟨11,1,false⟩,⟨13,2,true⟩,⟨17,1,false⟩,⟨19,1,false⟩],61,2⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkParityBoundedBlock_closes (B := 10 ^ 21) (.nil)
    13 32 0x304030405040700050407000000030410001215010504080300220101000100
    (by decide) ⟨30, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangFiveEightAt6Block39 : (⟨[⟨5,6,true⟩,⟨7,2,false⟩,⟨11,1,false⟩,⟨13,2,true⟩,⟨17,1,false⟩,⟨19,1,false⟩,⟨53,1,false⟩],55,1⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkParityBoundedBlock_closes (B := 10 ^ 21) (.nil)
    14 148 0x67c016f02019b099809ef01f713904d018b08af01e10a910a05020000031b00051e01080100120186014702010000050408000304060c000e4d0118062a4e073704018001ba5d1801c018010e1200051401080008580f029b01f87d2c344c150a0f00093f0117370802e903865303b806240618070c0000000014000f160143020103000b1101080a0103040200070101000100
    (by decide) ⟨27, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangFiveEightAt6Block40 : (⟨[⟨5,6,true⟩,⟨7,2,false⟩,⟨11,1,true⟩,⟨13,2,true⟩,⟨17,1,false⟩,⟨19,1,false⟩,⟨47,1,false⟩],49,1⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkParityBoundedBlock_closes (B := 10 ^ 21) (.nil)
    16 36 0x6160108010005100103040504080005040809001930011c0f0103040200150101000100
    (by decide) ⟨24, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangFiveEightAt6Block41 : (⟨[⟨5,6,true⟩,⟨7,1,false⟩,⟨11,1,false⟩,⟨13,2,true⟩,⟨17,1,false⟩,⟨19,1,false⟩],49,2⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkParityBoundedBlock_closes (B := 10 ^ 21) (.cons fangFiveEightAt6Block39 (.cons fangFiveEightAt6Block38 (.nil)))
    19 71 0x304000300080f010601000514010700000004000717013f02010000030403040504080005040810000b19011010285d7b04ef3d2003483c0d0c00000003041300290101000100
    (by decide) ⟨24, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangFiveEightAt6Block42 : (⟨[⟨5,6,true⟩,⟨7,1,false⟩,⟨11,1,false⟩,⟨13,2,true⟩,⟨17,1,false⟩,⟨19,1,false⟩,⟨43,1,false⟩],45,1⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkParityBoundedBlock_closes (B := 10 ^ 21) (.nil)
    18 86 0x647010e018201050b0100006b02010500064f01080003040805000934010801000f20016301000d3f0155020103000f01010d22010304030405040807000b12013902010000030407000a0101050401050407000400
    (by decide) ⟨22, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangFiveEightAt6Block43 : (⟨[⟨5,6,true⟩,⟨7,1,false⟩,⟨11,1,false⟩,⟨13,2,true⟩,⟨17,1,false⟩,⟨19,1,false⟩,⟨41,1,false⟩],43,1⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkParityBoundedBlock_closes (B := 10 ^ 21) (.nil)
    17 121 0x40406030005019c01030402000b3b010801000d54016f01000a570157020100005f0600064701080100070101072301051c010304020008480101296c425502fd01b566294a0a000e000a17010a1a013d02010000030407000609013502010300090101050401050408000000000700050401050407000400
    (by decide) ⟨21, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangFiveEightAt6Block44 : (⟨[⟨5,6,true⟩,⟨7,1,true⟩,⟨11,2,false⟩,⟨13,2,true⟩,⟨17,1,false⟩,⟨19,1,false⟩,⟨31,1,false⟩],35,1⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkParityBoundedBlock_closes (B := 10 ^ 21) (.nil)
    14 80 0x83f010b0101050401040408030005270103040504080005040800000b001a4b010304000006152d0e330d01830303010198631e070e15000f1c01040401a002831919625010010a0d00190101000100
    (by decide) ⟨17, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangFiveEightAt6Block45 : (⟨[⟨5,6,true⟩,⟨7,2,false⟩,⟨11,1,true⟩,⟨13,2,true⟩,⟨17,1,true⟩,⟨19,1,false⟩,⟨31,1,false⟩],83,1⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkParityBoundedBlock_closes (B := 10 ^ 21) (.nil)
    14 96 0x3040400086f010600030404000b3901ab02010000030600050601050100053c01606010640a1f2320018f01f33d6001b0110e12000701010e26010193020100007702010900060f0104040304080003040809000d010100030400000500
    (by decide) ⟨41, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangFiveEightAt6Block46 : (⟨[⟨5,6,true⟩,⟨7,2,false⟩,⟨11,1,false⟩,⟨13,2,true⟩,⟨17,1,false⟩,⟨19,1,false⟩,⟨31,1,false⟩],35,1⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkParityBoundedBlock_closes (B := 10 ^ 21) (.cons fangFiveEightAt6Block45 (.nil))
    18 265 0x73101d30100063101d204020300060801090e01b50100060e010701e801dd0100082301069f0200050801069e040204000512010901c501048504030005018a010501cf01e1020a2609035c4e28712e030a050200000304030401be0c54780c02f2019d1b2d18080202481808281808260201162f00070101052901b502020818024624480408100821276c01e71401db4544260201160502b3020320000847010297022217316c0c670501a3019201b204250c0502950203000001cf1c0008510101c102105a18361e6c1e029001bd0c0b1306010e0501bf02031900061201060901040100090a0103040803000c010109160101a102010000030400007302010d00080101000100
    (by decide) ⟨17, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangFiveEightAt6Block47 : (⟨[⟨5,6,true⟩,⟨7,1,false⟩,⟨11,1,false⟩,⟨13,2,true⟩,⟨17,1,false⟩,⟨19,1,false⟩],33,2⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkParityBoundedBlock_closes (B := 10 ^ 21) (.cons fangFiveEightAt6Block43 (.cons fangFiveEightAt6Block42 (.cons fangFiveEightAt6Block41 (.cons fangFiveEightAt6Block40 (.nil)))))
    22 102 0x606010504040407000404070900072b0101950201000073020109000857016b02010300060b0155020103000813010304030404000f2e0165020100040007100103040404080004040809000513010801001019010304000000004302010900130101000100
    (by decide) ⟨16, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangFiveEightAt6Block48 : (⟨[⟨5,6,true⟩,⟨7,1,true⟩,⟨11,2,false⟩,⟨13,2,true⟩,⟨17,1,false⟩,⟨19,1,false⟩,⟨29,1,false⟩],37,1⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkParityBoundedBlock_closes (B := 10 ^ 21) (.nil)
    13 89 0x83501050c01080101060c01063c01054c01000005040805000b0101073f010c1b013d02010300070101050a010304040407000404070900080101050801040406000404080700050701030402000b01010033020100000600
    (by decide) ⟨18, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangFiveEightAt6Block49 : (⟨[⟨5,6,true⟩,⟨7,1,true⟩,⟨11,1,false⟩,⟨13,2,true⟩,⟨17,1,false⟩,⟨19,1,false⟩,⟨29,1,false⟩],37,1⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkParityBoundedBlock_closes (B := 10 ^ 21) (.cons fangFiveEightAt6Block48 (.nil))
    14 85 0x50404030005200106040108010005380105040803000601010e1a010b1401070000000005000504010504080300091f01060c013527690959750101c1173554060d3b01121400070a010404060300140101000100
    (by decide) ⟨18, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangFiveEightAt6Block50 : (⟨[⟨5,6,true⟩,⟨7,1,false⟩,⟨11,1,false⟩,⟨13,2,true⟩,⟨17,1,false⟩,⟨19,1,false⟩,⟨29,1,false⟩],31,1⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkParityBoundedBlock_closes (B := 10 ^ 21) (.cons fangFiveEightAt6Block49 (.nil))
    17 331 0x20008029801052b01b5040103000507019d0100050801079c040300053c010501c40107690105b70401000006000d01d301f701000801d3010199023a06e806c103ba2503d406050210000601a90100000299020101040606060c060c122402040c124802040c121a2e244826070198040f653c0c18132205022b000601010653010801000501830101e7020c3035131a2e01f269080202300c080f0d0c1808020102160501e5020101020202040202080202080c182d000505010202080c3048181c14470148060401a524052405140005370103040600000001d5021533048604b42d5204c40dc1080501d3020300000304030403040700030407000000018902010000030433000501010067020102020201010204010102040305040c13000506012001010204080404081004040820020204081b051b14012c05020000000025020100002300
    (by decide) ⟨15, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangFiveEightAt6Block51 : (⟨[⟨5,6,true⟩,⟨7,1,true⟩,⟨11,2,false⟩,⟨13,2,true⟩,⟨17,2,false⟩,⟨19,1,false⟩,⟨23,1,false⟩],89,1⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkParityBoundedBlock_closes (B := 10 ^ 21) (.nil)
    13 120 0x5010005430102950201000001db08000649017701f0486a0303018d01a477402e0101010e1200070101050c01d3020100000500070e01b9020100000404070006180101b302010400060c0101a102010400060801062101080a01040100050a01060601030408000304080700120101007d020100000600
    (by decide) ⟨44, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangFiveEightAt6Block52 : (⟨[⟨5,6,true⟩,⟨7,1,true⟩,⟨11,1,true⟩,⟨13,2,true⟩,⟨17,1,false⟩,⟨19,1,false⟩,⟨23,1,false⟩],53,1⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkParityBoundedBlock_closes (B := 10 ^ 21) (.nil)
    16 98 0x5040400072b0108018e011901010b1201030408000305000663010743010a010110130141020103000d0101051e0101f1245d3202d6093f092d010a000000001100050401040100051001030400000504050408000504080d000e0101000100
    (by decide) ⟨26, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangFiveEightAt6Block53 : (⟨[⟨5,6,true⟩,⟨7,1,false⟩,⟨11,1,false⟩,⟨13,2,true⟩,⟨17,1,false⟩,⟨19,1,false⟩,⟨23,1,false⟩],25,1⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkParityBoundedBlock_closes (B := 10 ^ 21) (.cons fangFiveEightAt6Block52 (.cons fangFiveEightAt6Block51 (.nil)))
    16 136 0x70a01093001030406d3040100000204120612352b03a90718183c243601df500a103001141f0007090105040200082a0101a1020100000304000001910201000008fc109f05e005d202971101a606dc34310a22000f2b017302010300072501050a010606010304080003040807001101010504010404080300090c015902010300080101000100
    (by decide) ⟨12, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangFiveEightAt6Block54 : (⟨[⟨5,6,true⟩,⟨7,2,false⟩,⟨11,1,false⟩,⟨13,4,true⟩,⟨17,1,false⟩,⟨19,1,false⟩],55,2⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkParityBoundedBlock_closes (B := 10 ^ 21) (.nil)
    14 41 0x806010304060003040600082c01000100293a01030405040705001b12010504080300180101000100
    (by decide) ⟨27, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangFiveEightAt6Block55 : (⟨[⟨5,6,true⟩,⟨7,1,false⟩,⟨11,1,false⟩,⟨13,4,true⟩,⟨17,1,false⟩,⟨19,1,false⟩,⟨47,1,false⟩],49,1⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkParityBoundedBlock_closes (B := 10 ^ 21) (.nil)
    14 61 0x30100050d01590100061301040402000a39015302010300082a0145020103000a0c010501000b1701120d010808010609010304060300180101000100
    (by decide) ⟨24, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangFiveEightAt6Block56 : (⟨[⟨5,6,true⟩,⟨7,1,true⟩,⟨11,1,false⟩,⟨13,4,true⟩,⟨17,1,false⟩,⟨19,1,false⟩,⟨31,1,false⟩],35,1⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkParityBoundedBlock_closes (B := 10 ^ 21) (.nil)
    13 66 0x100074e010301000652011114013702010000000007000e100103040003000d37012f02010000050404040800040c00160e0105040105040803000c0101000100
    (by decide) ⟨17, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangFiveEightAt6Block57 : (⟨[⟨5,6,true⟩,⟨7,1,false⟩,⟨11,1,false⟩,⟨13,4,true⟩,⟨17,1,false⟩,⟨19,1,false⟩],33,2⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkParityBoundedBlock_closes (B := 10 ^ 21) (.cons fangFiveEightAt6Block55 (.cons fangFiveEightAt6Block54 (.nil)))
    21 94 0x50404040700040700052e015b02010300050c013f01000c300137020103000608010801000f260153020100003d020100003b0b00102001050401050407000304030400004902010d000c13010b0b01090c010304060300280101000100
    (by decide) ⟨16, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangFiveEightAt6Block58 : (⟨[⟨5,6,true⟩,⟨7,1,true⟩,⟨11,1,false⟩,⟨13,4,true⟩,⟨17,1,false⟩,⟨19,1,false⟩,⟨29,1,false⟩],37,1⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkParityBoundedBlock_closes (B := 10 ^ 21) (.nil)
    14 62 0x90e0103040200080d01085101080e011459010f43010d3801080100101a010720010701000a010105040105040803000b0e010404060300140101000100
    (by decide) ⟨18, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangFiveEightAt6Block59 : (⟨[⟨5,6,true⟩,⟨7,1,true⟩,⟨11,1,true⟩,⟨13,4,true⟩,⟨17,1,false⟩,⟨19,1,false⟩,⟨23,1,false⟩],55,1⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkParityBoundedBlock_closes (B := 10 ^ 21) (.nil)
    13 70 0x501000f1701510201000004040304080a0013420143020103000701010504010404080300071d01050405040800050408001401a22c4f1c087f7c6b030a16001e0101000100
    (by decide) ⟨27, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangFiveEightAt6Block60 : (⟨[⟨5,6,true⟩,⟨7,1,false⟩,⟨11,1,false⟩,⟨13,4,true⟩,⟨17,1,false⟩,⟨19,1,false⟩],25,2⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkParityBoundedBlock_closes (B := 10 ^ 21) (.cons fangFiveEightAt6Block57 (.cons fangFiveEightAt6Block56 (.cons fangFiveEightAt6Block58 (.nil))))
    17 164 0x6080108320104a104010400063c01060100082401028102010400053e01eb0100063e01060100051d0107000003000c4e016b0100053f01063c01030405a3040005080105a204020400091401fb010006080101b90200060c01051f01ad0100083d01790201000005000632010a0e01019d02010005000911017d010006110108000200081f016f02010000030407000610015701000607012302010300070101000100
    (by decide) ⟨12, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangFiveEightAt6Block61 : (⟨[⟨5,6,true⟩,⟨7,1,false⟩,⟨11,1,false⟩,⟨13,6,true⟩,⟨17,1,false⟩,⟨19,1,false⟩],31,2⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkParityBoundedBlock_closes (B := 10 ^ 21) (.nil)
    20 71 0x602010a0b01196e012f0100051f0107040105040803000f480123020100000404040800060c010504010504070003040007000e0e010b11010304060003040600250101000100
    (by decide) ⟨15, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangFiveEightAt6Block62 : (⟨[⟨5,6,true⟩,⟨7,1,false⟩,⟨11,1,false⟩,⟨13,6,false⟩,⟨17,1,false⟩,⟨19,1,false⟩],21,2⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkParityBoundedBlock_closes (B := 10 ^ 21) (.cons fangFiveEightAt6Block61 (.nil))
    17 101 0x55f010a14010aed0200084f01040100090f015d02010000050407000a1e014302010300074d01097001080100174f0137020100000304030800061301030402000615010700000300101b010401000704010504080004040607001d010100050404000500
    (by decide) ⟨10, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangFiveEightAt6Block63 : (⟨[⟨5,6,true⟩,⟨7,1,false⟩,⟨11,1,false⟩,⟨13,4,false⟩,⟨17,1,false⟩,⟨19,1,false⟩],21,2⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkParityBoundedBlock_closes (B := 10 ^ 21) (.cons fangFiveEightAt6Block62 (.cons fangFiveEightAt6Block60 (.cons fangFiveEightAt6Block59 (.nil))))
    18 95 0x501010927010ae902000508010ae80402000003040304000b00080401053001030402000501011017010542010511010b1f010301000711016f010008170104040803000501010609015d0100080901370201030005010100050404000500
    (by decide) ⟨10, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangFiveEightAt6Block64 : (⟨[⟨5,6,true⟩,⟨7,1,false⟩,⟨11,1,false⟩,⟨13,1,false⟩,⟨17,1,false⟩],21,3⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkParityBoundedBlock_closes (B := 10 ^ 21) (.cons fangFiveEightAt6Block37 (.cons fangFiveEightAt6Block36 (.cons fangFiveEightAt6Block27 (.cons fangFiveEightAt6Block23 (.cons fangFiveEightAt6Block22 (.nil))))))
    21 109 0x62c017a018a02cb01280501c32101a1296b1001010e000000241a039f601001d001b30d403d23010c00002800112e01304b01a201a16c1b1204020301019201b128441b123f1b1b33020101181d001001010c1001050401050408030010010105040105040400000000000800
    (by decide) ⟨10, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangFiveEightAt6Block65 : (⟨[⟨5,6,true⟩,⟨7,1,false⟩,⟨11,1,false⟩,⟨13,1,false⟩],19,4⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkParityBoundedBlock_closes (B := 10 ^ 21) (.cons fangFiveEightAt6Block0 (.cons fangFiveEightAt6Block7 (.cons fangFiveEightAt6Block6 (.cons fangFiveEightAt6Block5 (.nil)))))
    22 94 0x304030404000616014901000548010774010c2201070801050002000634010304070300070601030100082e010d28012f02010000030600052c012b02010000000003040404070004040710000c010109040106040403000a0101000100
    (by decide) ⟨9, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangFiveEightAt6Block66 : (⟨[⟨5,6,true⟩,⟨7,1,false⟩,⟨11,1,false⟩],15,5⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkParityBoundedBlock_closes (B := 10 ^ 21) (.nil)
    20 78 0x614011d1320029802c1026c02b72b070a0e001530010e18010501000710010d01010504010304070000000304000900090c01091e010b0801070004040505000504010404080300140101000100
    (by decide) ⟨7, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangFiveEightAt6Block67 : (⟨[⟨5,6,true⟩],7,7⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkParityBoundedBlock_closes (B := 10 ^ 21) (.cons fangFiveEightAt6Block66 (.cons fangFiveEightAt6Block65 (.cons fangFiveEightAt6Block64 (.cons fangFiveEightAt6Block63 (.cons fangFiveEightAt6Block53 (.cons fangFiveEightAt6Block50 (.cons fangFiveEightAt6Block47 (.cons fangFiveEightAt6Block46 (.cons fangFiveEightAt6Block44 (.nil))))))))))
    30 61 0x504040300051c010604010800040406000504080900101c0112160105040105040803000f250123020103000b010105040105040403000e0101000100
    (by decide) ⟨3, rfl⟩ (by decide +kernel)

theorem fangFiveEightAt6_closed : (⟨[⟨5,6,true⟩],7,7⟩ : Box).ClosedBelow (10 ^ 21) :=
  fangFiveEightAt6Block67

end OddWeirdSubproblems

open OddWeirdSubproblems

theorem OMA.solution : OMA.R_Erdos470_erdos_470_variants_odd_weird_10_pow_21_R1_H2_R1_H1_R1.H3 := by
  intro n hn ho ha hp h3 hc he
  by_contra hnp
  have hw : n.Weird := ⟨ha, hnp⟩
  exact noPrimitiveWeird10Pow21_coprimeThree_of_exponentRoot fangFiveEightAt6_closed
      hn ho h3 hc hp (by omega) (by omega) hw
