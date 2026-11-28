import OMAReductions.R_Erdos470_erdos_470_variants_odd_weird_prime_div_R1_H2_R1

/-!
Proof of Erdos470.erdos_470.variants.odd_weird_prime_div.R1.H2.R1.H1 via verified
prime-factorization branching and small-excess subset-sum certificates.
-/

namespace Erdos470H1Proof

open Finset ArithmeticFunction

inductive Par where | odd | even deriving DecidableEq

structure Entry where
  p : Nat
  minA : Nat
  exact : Bool
  par : Par
  deriving DecidableEq

inductive Cert where
  | A
  | B
  | M (g : Nat)
  | N (g : Nat)
  | R1 (g : Nat) (w1 : List Nat) (w2 : Nat)
  | S7 (p : Nat) (c0 c1 c2 c3 c4 : Cert)
  | P (p : Nat) (c0 c1 c2 : Cert)
  | X (cur : List Nat) (cs : List Cert)
  | T (curA : Nat) (e1W : List Nat) (e2W : List Nat)
  | L (cur : List Nat) (e1W : List Nat) (e2W : List Nat) (cs : List Cert)
  | R2 (qStop : Nat) (cs : List (Nat × Cert × Cert))
  | K (idx : Nat)

open Cert

def isPrimeAux (n d fuel : Nat) : Bool :=
  match fuel with
  | 0 => false
  | fuel + 1 =>
    if d * d > n then true else if n % d == 0 then false else isPrimeAux n (d + 2) fuel

def isPrimeBool (n : Nat) : Bool :=
  if n < 2 then false else if n == 2 then true else if n % 2 == 0 then false else isPrimeAux n 3 n

def nextPrime (n : Nat) (fuel : Nat := 100) : Option Nat :=
  match fuel with
  | 0 => none
  | fuel + 1 => if isPrimeBool n then some n else nextPrime (n + 1) fuel

def sigPP (p a : Nat) : Nat := (p ^ (a + 1) - 1) / (p - 1)

def addPowers (acc : List Nat) (p k pe : Nat) (out : List Nat) : List Nat :=
  match k with
  | 0 => out
  | k + 1 =>
    let added := if pe ≤ 63 then acc.filterMap (fun d => let v := d * pe; if v ≤ 63 then some v else none) else []
    addPowers acc p k (pe * p) (out ++ added)

def divsUpTo63 (spec : List Entry) : List Nat :=
  spec.foldl (fun acc e => addPowers acc e.p (e.minA + 1) 1 []) [1]

def subsetMask (divs : List Nat) : Nat :=
  divs.foldl (fun acc d => if d ≤ 63 then (acc ||| (acc <<< d)) % 18446744073709551616 else acc) 1

def checkBits (ss : Nat) (hasOdd allEven needMod4 : Bool) (g x : Nat) (acc : List Nat) : List Nat :=
  match x with
  | 0 => acc
  | n + 1 =>
    let idx := 63 - n
    let ok := (!hasOdd || idx % 2 == 0) && (!allEven || idx % 2 == 1) && (!needMod4 || idx % 4 == 2) &&
              (idx % g == 0) && ((ss / (2 ^ idx)) % 2 == 0)
    checkBits ss hasOdd allEven needMod4 g n (if ok then idx :: acc else acc)

def checkBitsStep (ss : Nat) (idx step fuel : Nat) : Bool :=
  match fuel with
  | 0 => true
  | n + 1 =>
    if idx > 63 then true
    else if (ss / (2 ^ idx)) % 2 == 0 then false
    else checkBitsStep ss (idx + step) step n

def checkG (spec : List Entry) (g : Nat) : Bool :=
  if g == 0 then false else
  let minM := spec.foldl (fun acc e => acc * e.p ^ e.minA) 1
  let sigKnown := spec.foldl (fun acc e =>
    let f := if e.exact then sigPP e.p e.minA else if e.par == .odd then e.p + 1 else 1
    acc * f) 1
  sigKnown % g == 0 && (2 * minM) % g == 0

def allowedEEmpty (spec : List Entry) (g : Nat) : Bool :=
  checkG spec g &&
  let ss := subsetMask (divsUpTo63 spec)
  let hasOdd := spec.any (·.par == .odd)
  let allEven := (5 - spec.length == 0) && spec.all (·.par == .even)
  let oddCount := spec.countP (·.par == .odd)
  let needMod4 := (oddCount ≥ 2) || spec.any (fun e => e.par == .odd && e.p % 4 == 3)
  if needMod4 then
    if g % 4 == 0 then true
    else if g % 2 == 0 then checkBitsStep ss g (2 * g) 64
    else checkBitsStep ss (2 * g) (4 * g) 64
  else if hasOdd then
    if g % 2 == 0 then checkBitsStep ss g g 64
    else checkBitsStep ss (2 * g) (2 * g) 64
  else if allEven then
    if g % 2 == 0 then true
    else checkBitsStep ss g (2 * g) 64
  else checkBitsStep ss g g 64

def allowedEMask (spec : List Entry) (g : Nat) : List Nat :=
  let ss := subsetMask (divsUpTo63 spec)
  let hasOdd := spec.any (·.par == .odd)
  let allEven := (5 - spec.length == 0) && spec.all (·.par == .even)
  let oddCount := spec.countP (·.par == .odd)
  let needMod4 := (oddCount ≥ 2) || spec.any (fun e => e.par == .odd && e.p % 4 == 3)
  (checkBits ss hasOdd allEven needMod4 g 63 []).reverse

-- =====================================================================
-- Soundness lemmas
-- =====================================================================

lemma sigma_one_eq_sum_proper_add (n : ℕ) :
    sigma 1 n = (∑ d ∈ n.properDivisors, d) + n := by
  rw [ArithmeticFunction.sigma_one_apply]
  simpa using Nat.sum_divisors_eq_sum_properDivisors_add_self (n := n)

lemma abundant_iff_two_mul_lt_sigma (n : ℕ) :
    n.Abundant ↔ 2 * n < sigma 1 n := by
  rw [Nat.Abundant, sigma_one_eq_sum_proper_add]
  omega

lemma deficient_iff_sigma_lt_two_mul (n : ℕ) :
    n.Deficient ↔ sigma 1 n < 2 * n := by
  rw [Nat.Deficient, sigma_one_eq_sum_proper_add]
  omega

lemma geom_sum_mul_pred (p a : ℕ) (hp : 1 < p) :
    (p - 1) * ∑ i ∈ range (a + 1), p ^ i = p ^ (a + 1) - 1 := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [sum_range_succ, mul_add, ih]
    have h1 : 1 ≤ p ^ (a + 1) := Nat.one_le_pow _ _ (by omega)
    have hsub : (p - 1) * p ^ (a + 1) = p ^ (a + 1) * p - p ^ (a + 1) := by
      rw [Nat.sub_mul, one_mul, mul_comm]
    have hle : p ^ (a + 1) ≤ p ^ (a + 1 + 1) := by
      rw [pow_succ]
      exact Nat.le_mul_of_pos_right _ (by omega)
    rw [hsub, ← pow_succ]
    omega

lemma sigPP_eq_geomSum (p a : ℕ) (hp : 1 < p) :
    sigPP p a = ∑ i ∈ range (a + 1), p ^ i := by
  rw [sigPP, ← geom_sum_mul_pred p a hp, Nat.mul_div_cancel_left _ (Nat.sub_pos_of_lt hp)]

lemma sigma_one_prime_pow {p : ℕ} (hp : p.Prime) (a : ℕ) :
    sigma 1 (p ^ a) = sigPP p a := by
  rw [ArithmeticFunction.sigma_one_apply, Nat.sum_divisors_prime_pow hp, sigPP_eq_geomSum p a hp.one_lt]

lemma sigPP_pos {p : ℕ} (hp : 1 < p) (a : ℕ) : 0 < sigPP p a := by
  rw [sigPP_eq_geomSum p a hp]
  exact sum_pos' (fun _ _ => Nat.zero_le _) ⟨0, mem_range.mpr (Nat.succ_pos _), by simp⟩

lemma sigPP_lt_bound {p : ℕ} (hp : 1 < p) (a : ℕ) :
    sigPP p a * (p - 1) < p * p ^ a := by
  rw [sigPP_eq_geomSum p a hp, mul_comm, geom_sum_mul_pred p a hp, ← pow_succ']
  exact Nat.sub_lt (Nat.pow_pos (Nat.zero_lt_of_lt hp)) one_pos

lemma sigPP_mono {p : ℕ} (hp : 1 < p) {a b : ℕ} (hab : a ≤ b) :
    sigPP p a * p ^ b ≤ sigPP p b * p ^ a := by
  have hsub : 0 < p - 1 := Nat.sub_pos_of_lt hp
  apply Nat.le_of_mul_le_mul_left _ hsub
  have hmul (k : ℕ) : (p - 1) * sigPP p k = p ^ (k + 1) - 1 := by
    rw [sigPP_eq_geomSum p k hp, geom_sum_mul_pred p k hp]
  calc (p - 1) * (sigPP p a * p ^ b)
      = ((p - 1) * sigPP p a) * p ^ b := by ring
    _ = (p ^ (a + 1) - 1) * p ^ b := by rw [hmul a]
    _ = p ^ (a + 1 + b) - p ^ b := by rw [Nat.sub_mul, one_mul, ← pow_add]
    _ ≤ p ^ (b + 1 + a) - p ^ a := by
        rw [show a + 1 + b = b + 1 + a by omega]
        exact Nat.sub_le_sub_left (Nat.pow_le_pow_right (by omega) hab) _
    _ = (p ^ (b + 1) - 1) * p ^ a := by rw [Nat.sub_mul, one_mul, ← pow_add]
    _ = ((p - 1) * sigPP p b) * p ^ a := by rw [hmul b]
    _ = (p - 1) * (sigPP p b * p ^ a) := by ring

lemma sigPP_odd_iff {p : ℕ} (hp : 1 < p) (hodd : Odd p) (a : ℕ) :
    Odd (sigPP p a) ↔ Even a := by
  rw [sigPP_eq_geomSum p a hp]
  induction a with
  | zero => simp
  | succ a ih =>
    rw [sum_range_succ, Nat.odd_add, ih, Nat.even_add_one]
    have hnot : ¬ Even (p ^ (a + 1)) := Nat.not_even_iff_odd.mpr hodd.pow
    simp [hnot]

lemma succ_dvd_sigPP {p : ℕ} (hp : 1 < p) {a : ℕ} (ha : Odd a) :
    p + 1 ∣ sigPP p a := by
  rw [sigPP_eq_geomSum p a hp]
  obtain ⟨k, rfl⟩ := ha
  induction k with
  | zero =>
    simp [sum_range_succ, Nat.add_comm]
  | succ k ih =>
    rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 by omega, sum_range_succ, sum_range_succ]
    rw [show (∑ x ∈ range (2 * k + 1 + 1), p ^ x) + p ^ (2 * k + 1 + 1) + p ^ (2 * k + 1 + 1 + 1)
      = (∑ x ∈ range (2 * k + 1 + 1), p ^ x) + p ^ (2 * k + 2) * (p + 1) by ring]
    exact dvd_add ih (dvd_mul_left _ _)

lemma checkFactor_not_prime {q d : ℕ} (h : (1 < d && d < q && q % d == 0) = true) : ¬ q.Prime := by
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  exact Nat.not_prime_of_dvd_of_lt (Nat.dvd_of_mod_eq_zero h3) h1 h2

lemma isPrimeAux_sound {n d fuel : ℕ} (h : isPrimeAux n d fuel = true)
    (hn : 2 < n) (hodd : Odd n) (hd : 3 ≤ d) (hdodd : Odd d)
    (hprev : ∀ k, 3 ≤ k → k < d → ¬ k ∣ n) : n.Prime := by
  induction fuel generalizing d with
  | zero => simp [isPrimeAux] at h
  | succ fuel ih =>
    unfold isPrimeAux at h
    split_ifs at h with hgt hdvd
    · refine Nat.prime_def_lt'.mpr ⟨by omega, fun k hk1 hkn hkdiv => ?_⟩
      by_cases hk2 : k = 2
      · subst hk2; exact hodd.not_two_dvd_nat hkdiv
      have hk3 : 3 ≤ k := by omega
      by_cases hkd : k < d
      · exact hprev k hk3 hkd hkdiv
      have hdiv_lt : n / k < d := by
        by_contra hge
        rw [not_lt] at hge
        have hmul : d * d ≤ k * (n / k) := Nat.mul_le_mul (by omega) hge
        rw [Nat.mul_div_cancel' hkdiv] at hmul
        nlinarith
      have hdiv3 : 3 ≤ n / k := by
        by_contra hlt
        have hlt' : n / k < 3 := Nat.lt_of_not_le hlt
        have hmul : k * (n / k) = n := Nat.mul_div_cancel' hkdiv
        match hq : n / k with
        | 0 => rw [hq, mul_zero] at hmul; omega
        | 1 => rw [hq, mul_one] at hmul; omega
        | 2 => rw [hq] at hmul; exact hodd.not_two_dvd_nat ⟨k, by linarith⟩
        | _ + 3 => omega
      exact hprev (n / k) hdiv3 hdiv_lt (Nat.div_dvd_of_dvd hkdiv)
    · have hdodd2 : Odd (d + 2) := by obtain ⟨k, rfl⟩ := hdodd; exact ⟨k + 1, by omega⟩
      exact ih h (by omega) hdodd2 (fun k hk1 hk2 => by
        by_cases heq : k = d
        · subst heq; exact fun div => hdvd (beq_iff_eq.mpr (Nat.mod_eq_zero_of_dvd div))
        by_cases heq1 : k = d + 1
        · subst heq1
          have keven : Even (d + 1) := hdodd.add_one
          intro div
          exact hodd.not_two_dvd_nat (keven.two_dvd.trans div)
        exact hprev k hk1 (by omega))

lemma isPrimeAux_of_prime {n d fuel : ℕ} (hp : n.Prime) (hd : 3 ≤ d)
    (hf1 : 1 ≤ fuel) (hfuel : 2 * n + 3 ≤ d + 2 * fuel) :
    isPrimeAux n d fuel = true := by
  induction fuel generalizing d with
  | zero => omega
  | succ fuel ih =>
    unfold isPrimeAux
    split_ifs with hgt hdvd
    · rfl
    · exfalso
      have hdiv : d ∣ n := Nat.dvd_of_mod_eq_zero (beq_iff_eq.mp hdvd)
      have hdlt : d < n := by
        by_contra hge
        have : n ≤ d := by omega
        have hn2 : 2 ≤ n := hp.two_le
        have : n < d * d := by nlinarith
        exact hgt this
      rcases hp.eq_one_or_self_of_dvd d hdiv with h1 | hself <;> omega
    · have hle : d * d ≤ n := by omega
      have hdn : d ≤ n := by nlinarith
      have h2n : 3 ≤ n := by
        have := hp.two_le
        by_contra hlt
        have hn2 : n = 2 := by omega
        subst hn2; nlinarith
      exact ih (by omega) (by omega) (by omega)

lemma isPrimeBool_iff {n : ℕ} : isPrimeBool n = true ↔ n.Prime := by
  constructor
  · intro h
    unfold isPrimeBool at h
    split_ifs at h with h1 h2 h3
    · have h2' : n = 2 := beq_iff_eq.mp h2
      subst h2'; exact Nat.prime_two
    · have hne2 : n ≠ 2 := fun heq => h2 (beq_iff_eq.mpr heq)
      have hodd : Odd n := Nat.not_even_iff_odd.mp
        (fun he => h3 (beq_iff_eq.mpr (Nat.mod_eq_zero_of_dvd he.two_dvd)))
      exact isPrimeAux_sound h (by omega) hodd (by omega) (by decide) (fun k hk1 hk2 => by omega)
  · intro hp
    unfold isPrimeBool
    split_ifs with h1 h2 h3
    · exfalso; exact (Nat.not_lt_of_ge hp.two_le) h1
    · rfl
    · exfalso
      have h2d : 2 ∣ n := Nat.dvd_of_mod_eq_zero (beq_iff_eq.mp h3)
      have hne2 : n ≠ 2 := fun heq => h2 (beq_iff_eq.mpr heq)
      rcases hp.eq_one_or_self_of_dvd 2 h2d with h | h <;> omega
    · exact isPrimeAux_of_prime hp (by omega) (by omega) (by omega)

lemma nextPrime_spec {n fuel q : ℕ} (h : nextPrime n fuel = some q) :
    n ≤ q ∧ q.Prime ∧ ∀ r, n ≤ r → r < q → ¬ r.Prime := by
  induction fuel generalizing n with
  | zero => simp [nextPrime] at h
  | succ fuel ih =>
    unfold nextPrime at h
    split_ifs at h with hp
    · injection h with hq; subst hq
      exact ⟨le_rfl, isPrimeBool_iff.mp hp, fun r hr1 hr2 => by omega⟩
    · obtain ⟨hq1, hqp, hqr⟩ := ih h
      refine ⟨by omega, hqp, fun r hr1 hr2 => ?_⟩
      by_cases heq : r = n
      · subst heq; exact fun hrp => hp (isPrimeBool_iff.mpr hrp)
      · exact hqr r (by omega) hr2

-- =====================================================================
-- Subset-sum bitmask soundness
-- =====================================================================

lemma testBit_eq_div_mod_two (x k : ℕ) : x.testBit k = ((x / 2 ^ k) % 2 == 1) := by
  rw [Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.and_comm, Nat.and_one_is_mod]
  rcases Nat.mod_two_eq_zero_or_one (x / 2 ^ k) with h | h <;> simp [h]

lemma testBit_subsetMask_step (acc d k : ℕ) (hk : k < 64) :
    ((if d ≤ 63 then (acc ||| (acc <<< d)) % 18446744073709551616 else acc).testBit k = true) →
    acc.testBit k = true ∨ (d ≤ k ∧ acc.testBit (k - d) = true) := by
  intro h
  split_ifs at h with hd
  · have hmod : ((acc ||| (acc <<< d)) % 2 ^ 64).testBit k = (acc ||| (acc <<< d)).testBit k :=
      Nat.testBit_mod_two_pow _ 64 k |>.trans (by simp [hk])
    change ((acc ||| (acc <<< d)) % 2 ^ 64).testBit k = true at h
    rw [hmod, Nat.testBit_or, Nat.testBit_shiftLeft, Bool.or_eq_true] at h
    rcases h with h1 | h2
    · exact Or.inl h1
    · simp only [Bool.and_eq_true, decide_eq_true_eq] at h2
      exact Or.inr h2
  · exact Or.inl h

lemma subsetMask_foldl_sound (divs : List Nat) (hnodup : divs.Nodup)
    (prev : Finset Nat) (hdisj : Disjoint prev divs.toFinset) (acc : ℕ)
    (hinv : ∀ k < 64, acc.testBit k = true → ∃ s ⊆ prev, s.sum id = k) :
    ∀ k < 64, (divs.foldl (fun a d => if d ≤ 63 then (a ||| (a <<< d)) % 18446744073709551616 else a) acc).testBit k = true →
      ∃ s ⊆ prev ∪ divs.toFinset, s.sum id = k := by
  induction divs generalizing prev acc with
  | nil =>
    intro k hk h
    simpa using hinv k hk h
  | cons d ds ih =>
    rw [List.nodup_cons] at hnodup
    rw [List.toFinset_cons, Finset.disjoint_insert_right] at hdisj
    simp only [List.foldl_cons]
    have hdisj' : Disjoint (insert d prev) ds.toFinset :=
      Finset.disjoint_insert_left.mpr ⟨by simpa using hnodup.1, hdisj.2⟩
    have hinv' : ∀ k < 64,
        (if d ≤ 63 then (acc ||| (acc <<< d)) % 18446744073709551616 else acc).testBit k = true →
        ∃ s ⊆ insert d prev, s.sum id = k := by
      intro k hk h
      rcases testBit_subsetMask_step acc d k hk h with h1 | ⟨hdk, h2⟩
      · obtain ⟨s, hs, hsum⟩ := hinv k hk h1
        exact ⟨s, hs.trans (Finset.subset_insert d prev), hsum⟩
      · obtain ⟨s, hs, hsum⟩ := hinv (k - d) (by omega) h2
        have hd_not : d ∉ s := fun hmem => hdisj.1 (hs hmem)
        refine ⟨insert d s, Finset.insert_subset_insert d hs, ?_⟩
        rw [Finset.sum_insert hd_not, id_eq, hsum]
        omega
    intro k hk hfold
    obtain ⟨s, hs, hsum⟩ := ih hnodup.2 (insert d prev) hdisj' _ hinv' k hk hfold
    refine ⟨s, hs.trans ?_, hsum⟩
    intro x hx
    simp only [Finset.mem_union, List.mem_toFinset, List.mem_cons]
    rcases Finset.mem_union.mp hx with hx' | hx'
    · rcases Finset.mem_insert.mp hx' with rfl | hx''
      · right; left; rfl
      · left; exact hx''
    · right; right; exact List.mem_toFinset.mp hx'

lemma subsetMask_sound {divs : List Nat} (hnodup : divs.Nodup) {k : ℕ} (hk : k < 64)
    (hbit : ((subsetMask divs / 2 ^ k) % 2 == 1) = true) :
    ∃ s ⊆ divs.toFinset, s.sum id = k := by
  have ht : (subsetMask divs).testBit k = true := by
    rw [testBit_eq_div_mod_two]
    exact hbit
  unfold subsetMask at ht
  have hinv : ∀ j < 64, (1 : ℕ).testBit j = true → ∃ s ⊆ (∅ : Finset ℕ), s.sum id = j := by
    intro j _ hj
    have hj0 : j = 0 := by
      by_contra hne
      have hdiv : (1 : ℕ) / 2 ^ j = 0 := Nat.div_eq_of_lt (by have : 2 ≤ 2 ^ j := Nat.le_self_pow hne 2; omega)
      rw [testBit_eq_div_mod_two, hdiv] at hj
      simp at hj
    subst hj0
    exact ⟨∅, Subset.rfl, by simp⟩
  have h := subsetMask_foldl_sound divs hnodup ∅ (Finset.disjoint_empty_left _) 1 hinv k hk ht
  simpa using h

-- =====================================================================
-- Remainder of checker definitions
-- =====================================================================

def maxAbTail (k q n d : Nat) : Nat × Nat :=
  match k with
  | 0 => (n, d)
  | k + 1 => match nextPrime q with
    | none => (1, 0)
    | some q' => maxAbTail k (q' + 1) (n * q') (d * (q' - 1))

def maxAbSpec (spec : List Entry) (minP rem : Nat) : Nat × Nat :=
  let (n0, d0) := spec.foldl (fun (n, d) e =>
    if e.exact then (n * sigPP e.p e.minA, d * e.p ^ e.minA) else (n * e.p, d * (e.p - 1))) (1, 1)
  maxAbTail rem minP n0 d0

def minNumAb (spec : List Entry) : Nat × Nat :=
  spec.foldl (fun (m, s) e => (m * e.p ^ e.minA, s * sigPP e.p e.minA)) (1, 1)

def checkFactor (q d : Nat) : Bool := 1 < d && d < q && q % d == 0

def checkE1Loop : Nat → List Nat → Bool
  | _, [] => true
  | q, d :: ds => checkFactor q d && checkE1Loop (q + 1) ds

def checkE2Loop (loNum loDen hiNum hiDen dLbNum dLbDen : Nat) : Nat → List Nat → Bool
  | _, [] => true
  | q, c :: ds =>
    let ok := if c % 2 == 0 then checkFactor q (c / 2)
      else
        let eMin := c / 2
        if loNum + loDen ≤ q * loDen || eMin < 2 then false
        else
          let gapLoNum := loNum + loDen - q * loDen
          let gapHiNum := hiNum + hiDen - q * hiDen
          let qe := q ^ eMin
          let qPrev := q ^ (eMin - 1)
          (eMin == 2 || qPrev * gapHiNum * loDen ≤ hiDen * loNum) &&
          qe * gapLoNum * hiDen > hiNum * loDen &&
          dLbNum * (qe * gapLoNum * hiDen - hiNum * loDen) ≥ 64 * (q - 1) * dLbDen * loDen * hiDen
    ok && checkE2Loop loNum loDen hiNum hiDen dLbNum dLbDen (q + 1) ds

def prodWithCur : List Entry → List Nat → Nat → Nat → Nat × Nat
  | [], _, b, sb => (b, sb)
  | e :: es, cs, b, sb =>
    if e.exact then prodWithCur es cs (b * e.p ^ e.minA) (sb * sigPP e.p e.minA)
    else match cs with
      | [] => (b, sb)
      | c :: rest => prodWithCur es rest (b * e.p ^ c) (sb * sigPP e.p c)

def checkRem1TailWit (spec : List Entry) (cur : List Nat) (LNum LDen minQ : Nat)
    (e1W : List Nat) (e2W : List Nat) : Bool :=
  let (bMin, sbMin) := prodWithCur spec cur 1 1
  if 2 * bMin ≤ sbMin || 2 * LDen ≤ LNum then false
  else
    let DMin := 2 * bMin - sbMin
    let loNum := sbMin; let loDen := DMin
    let hiNum := LNum; let hiDen := 2 * LDen - LNum
    let dLbNum := (2 * LDen - LNum) * bMin; let dLbDen := LDen
    let lhsE1 := loNum * dLbNum; let subE1 := 63 * loDen * dLbDen; let denE1 := loDen * dLbNum
    let qE1Lo := if lhsE1 > subE1 then (lhsE1 - subE1 + denE1 - 1) / denE1 else 0
    let qE1Hi := (hiNum - 1) / hiDen
    let lo1 := max minQ qE1Lo
    let e1Ok := if qE1Hi < lo1 then e1W.isEmpty else
      e1W.length == qE1Hi + 1 - lo1 && checkE1Loop lo1 e1W
    if !e1Ok then false
    else
      let qE2Lo := loNum / loDen + 1; let qE2Hi := 1 + (hiNum - 1) / hiDen
      let lo2 := max minQ qE2Lo
      if qE2Hi < lo2 then e2W.isEmpty else
      e2W.length == qE2Hi + 1 - lo2 && checkE2Loop loNum loDen hiNum hiDen dLbNum dLbDen lo2 e2W

def stepNF1 (p b sb : Nat) (miss : List Nat) (fuel pe spe : Nat) : Bool :=
  match fuel with
  | 0 => false
  | fuel + 1 =>
    if sb * spe ≥ 2 * b * pe then let E := sb * spe - 2 * b * pe; E == 0 || E ≥ 64 || !(miss.contains E)
    else stepNF1 p b sb miss fuel (pe * p * p) (spe * p * p + p + 1)

def checkNF1Go (miss : List Nat) (pref : List Entry) : List Entry → Bool
  | [] => false
  | e :: rest =>
    if !e.exact then
      let (b, sb) := minNumAb (pref ++ rest)
      stepNF1 e.p b sb miss 100 (e.p ^ e.minA) (sigPP e.p e.minA)
    else checkNF1Go miss (pref ++ [e]) rest

def stepRem1E2 (q2 sb : Nat) (miss : List Nat) (fuel : Nat) (E : Int) : Bool :=
  match fuel with
  | 0 => false
  | fuel + 1 =>
    if E ≥ 0 then let En := E.toNat; En == 0 || En ≥ 64 || !(miss.contains En)
    else stepRem1E2 q2 sb miss fuel (↑q2 * E + ↑sb)

def checkR1E1 (sb D : Nat) (miss : List Nat) : Nat → List Nat → Bool
  | _, [] => true
  | q, d :: ds =>
    let ok := if d > 0 then checkFactor q d else !(miss.contains (sb - D * q))
    ok && checkR1E1 sb D miss (q + 1) ds

def checkRem1NF0 (b sb minQ : Nat) (miss w1 : List Nat) (w2 : Nat) : Bool :=
  let D := 2 * b - sb
  let qLo := max minQ (if sb ≥ 63 then (sb - 63 + D - 1) / D else 0)
  let qHi := if sb ≥ 1 then (sb - 1) / D else 0
  let e1Ok := if qHi < qLo then w1.isEmpty else w1.length == qHi + 1 - qLo && checkR1E1 sb D miss qLo w1
  if !e1Ok then false else
    let q2 := (2 * b) / D
    if q2 ≥ minQ && 2 * b > D * q2 && 2 * b < D * (q2 + 1) then
      if w2 > 0 then checkFactor q2 w2 else stepRem1E2 q2 sb miss 100 (-↑D)
    else true

def expandStepA (go : List Entry → Cert → Bool) (pref : List Entry) (e : Entry) (rest' : List Entry)
    (c a : Nat) : List Cert → List Cert × Bool
  | [] => if a ≥ c then ([], true) else ([], false)
  | sub :: more =>
    if a ≥ c then (sub :: more, true)
    else if go (pref ++ [{ e with minA := a, exact := true }] ++ rest') sub then
      expandStepA go pref e rest' c (a + 2) more
    else ([], false)

def expandFree (go : List Entry → Cert → Bool) (pref : List Entry) (rest : List Entry)
    (cur : List Nat) (cs : List Cert) : Bool :=
  match rest with
  | [] => cur.isEmpty && cs.isEmpty
  | e :: rest' =>
    if e.exact then expandFree go (pref ++ [e]) rest' cur cs
    else match cur with
      | [] => false
      | c :: curRest =>
        c ≥ e.minA && (c - e.minA) % 2 == 0 &&
        let (remCs, ok) := expandStepA go pref e rest' c e.minA cs
        ok && expandFree go (pref ++ [{ e with minA := c, exact := false }]) rest' curRest remCs

def checkR2 (go : List Entry → Nat → Cert → Bool) (spec : List Entry) (qStop curP : Nat)
    (cs : List (Nat × Cert × Cert)) : Bool :=
  match cs with
  | [] => nextPrime curP == some qStop
  | (q, c1, c2) :: rest =>
    nextPrime curP == some q && q < qStop &&
    go (spec ++ [⟨q, 1, false, .odd⟩]) (q + 1) c1 &&
    go (spec ++ [⟨q, 2, false, .even⟩]) (q + 1) c2 &&
    checkR2 go spec qStop (q + 1) rest

def checkCert (leafOk : Nat → List Entry → Nat → Bool) (fuel : Nat) (c : Cert) (spec : List Entry) (minP : Nat) : Bool :=
  match fuel with
  | 0 => false
  | fuel + 1 =>
  match c with
  | .A =>
    let (m, s) := minNumAb spec
    if s < 2 * m then false
    else let E := s - 2 * m; if E == 0 || E ≥ 64 then true else ((subsetMask (divsUpTo63 spec) / (2 ^ E)) % 2) == 1
  | .B =>
    let (n, d) := maxAbSpec spec minP (5 - spec.length)
    0 < d && n ≤ 2 * d
  | .M g => allowedEEmpty spec g
  | .N g =>
    let freeCnt := spec.countP (fun e => !e.exact)
    checkG spec g && 5 - spec.length == 0 && freeCnt == 1 && checkNF1Go (allowedEMask spec g) [] spec
  | .R1 g w1 w2 =>
    let freeCnt := spec.countP (fun e => !e.exact)
    let (m, s) := minNumAb spec
    match nextPrime minP with
    | none => false
    | some minQ => checkG spec g && 5 - spec.length == 1 && freeCnt == 0 && s < 2 * m && checkRem1NF0 m s minQ (allowedEMask spec g) w1 w2
  | .S7 p c0 c1 c2 c3 c4 =>
    nextPrime minP == some p && p ≤ 7 &&
    checkCert leafOk fuel c0 spec (p + 1) &&
    checkCert leafOk fuel c1 (spec ++ [⟨p, 1, true, .odd⟩]) (p + 1) &&
    checkCert leafOk fuel c2 (spec ++ [⟨p, 2, true, .even⟩]) (p + 1) &&
    checkCert leafOk fuel c3 (spec ++ [⟨p, 3, false, .odd⟩]) (p + 1) &&
    checkCert leafOk fuel c4 (spec ++ [⟨p, 4, false, .even⟩]) (p + 1)
  | .P p c0 c1 c2 =>
    nextPrime minP == some p &&
    checkCert leafOk fuel c0 spec (p + 1) &&
    checkCert leafOk fuel c1 (spec ++ [⟨p, 1, false, .odd⟩]) (p + 1) &&
    checkCert leafOk fuel c2 (spec ++ [⟨p, 2, false, .even⟩]) (p + 1)
  | .X cur cs =>
    let freeCnt := spec.countP (fun e => !e.exact)
    let (abN, abD) := maxAbSpec spec minP 0
    freeCnt > 0 && 0 < abD && (5 - spec.length == 0 || abN ≥ 2 * abD) &&
    cur.length == freeCnt &&
    (let (b, sb) := prodWithCur spec cur 1 1
     if sb < 2 * b then false else
     let E := sb - 2 * b
     E == 0 || E ≥ 64 || ((subsetMask (divsUpTo63 spec) / (2 ^ E)) % 2) == 1) &&
    expandFree (fun sp sub => checkCert leafOk fuel sub sp minP) [] spec cur cs
  | .T curA e1W e2W =>
    let freeCnt := spec.countP (fun e => !e.exact)
    let (abN, abD) := maxAbSpec spec minP 0
    match nextPrime minP, spec.find? (fun e => !e.exact) with
    | some minQ, some fe => 5 - spec.length == 1 && freeCnt == 1 && fe.minA == curA &&
      0 < abD && abN < 2 * abD && checkRem1TailWit spec [curA] abN abD minQ e1W e2W
    | _, _ => false
  | .L cur e1W e2W cs =>
    let freeCnt := spec.countP (fun e => !e.exact)
    let (abN, abD) := maxAbSpec spec minP 0
    match nextPrime minP with
    | none => false
    | some minQ => 5 - spec.length == 1 && freeCnt > 0 && 0 < abD && abN < 2 * abD && cur.length == freeCnt &&
      checkRem1TailWit spec cur abN abD minQ e1W e2W &&
      expandFree (fun sp sub => checkCert leafOk fuel sub sp minP) [] spec cur cs
  | .R2 qStop cs =>
    let (abN, abD) := maxAbSpec spec minP 0
    5 - spec.length == 2 && 0 < abD && abN < 2 * abD &&
    abN * qStop * (qStop + 2) ≤ 2 * abD * (qStop - 1) * (qStop + 1) &&
    checkR2 (fun sp mp sub => checkCert leafOk fuel sub sp mp) spec qStop minP cs
  | .K idx => leafOk idx spec minP

-- =====================================================================
-- Target Goal & SpecValid invariant
-- =====================================================================

def Goal (m : ℕ) : Prop :=
  ∃ s : Finset ℕ, (∀ d ∈ s, d ∣ m) ∧ s.sum id = sigma 1 m - 2 * m

def EntryValid (m minP : ℕ) (e : Entry) : Prop :=
  e.p.Prime ∧ e.p < minP ∧ Odd e.p ∧ e.p ∣ m ∧
  1 ≤ e.minA ∧ e.minA ≤ m.factorization e.p ∧
  (e.exact = true → m.factorization e.p = e.minA) ∧
  (match e.par with | .odd => Odd (m.factorization e.p) | .even => Even (m.factorization e.p)) ∧
  e.minA % 2 = m.factorization e.p % 2

def SpecValid (m : ℕ) (spec : List Entry) (minP : ℕ) : Prop :=
  (spec.map (·.p)).Pairwise (· < ·) ∧
  (∀ e ∈ spec, EntryValid m minP e) ∧
  (∀ q ∈ m.primeFactors, (∃ e ∈ spec, e.p = q) ∨ minP ≤ q)

-- =====================================================================
-- Multiplicative factorization & foldl lemmas
-- =====================================================================

lemma sigma_one_eq_prod_primeFactors {n : ℕ} (hn : n ≠ 0) :
    sigma 1 n = ∏ p ∈ n.primeFactors, sigPP p (n.factorization p) := by
  have hmult := ArithmeticFunction.isMultiplicative_sigma (k := 1)
  rw [hmult.multiplicative_factorization _ hn]
  refine Finset.prod_congr rfl fun p hp => ?_
  exact sigma_one_prime_pow (Nat.prime_of_mem_primeFactors hp) (n.factorization p)

lemma foldl_mul_eq {α : Type*} (l : List α) (f : α → ℕ) (init : ℕ) :
    l.foldl (fun acc x => acc * f x) init = init * (l.map f).prod := by
  induction l generalizing init with
  | nil => simp
  | cons a t ih =>
    simp only [List.foldl_cons, List.map_cons, List.prod_cons, ih]
    ring

lemma list_prod_toFinset {l : List Entry} (hpw : (l.map (·.p)).Pairwise (· < ·)) (f : Entry → ℕ) :
    (l.map f).prod = ∏ e ∈ l.toFinset, f e := by
  have hnd : l.Nodup := by
    have hndp : (l.map (·.p)).Nodup := hpw.imp (fun h => Nat.ne_of_lt h)
    exact hndp.of_map _
  exact (List.prod_toFinset f hnd).symm

-- =====================================================================
-- divsUpTo63 soundness
-- =====================================================================

lemma addPowers_spec {m p : ℕ} (hm : m ≠ 0) (hp : p.Prime)
    (acc : List Nat) (hacc_nd : acc.Nodup)
    (hacc : ∀ d ∈ acc, 0 < d ∧ d ∣ m ∧ d ≤ 63 ∧ ∀ q ∈ d.primeFactors, q < p)
    (k j : ℕ) (hpow : ∀ i < k, j + i ≤ m.factorization p)
    (out : List Nat) (hout_nd : out.Nodup)
    (hout : ∀ d ∈ out, 0 < d ∧ d ∣ m ∧ d ≤ 63 ∧ (∀ q ∈ d.primeFactors, q ≤ p) ∧ d.factorization p < j) :
    (addPowers acc p k (p ^ j) out).Nodup ∧
    ∀ d ∈ addPowers acc p k (p ^ j) out,
      0 < d ∧ d ∣ m ∧ d ≤ 63 ∧ ∀ q ∈ d.primeFactors, q ≤ p := by
  induction k generalizing j out with
  | zero =>
    simp only [addPowers]
    exact ⟨hout_nd, fun d hd => let ⟨a, b, c, d1, _⟩ := hout d hd; ⟨a, b, c, d1⟩⟩
  | succ k ih =>
    simp only [addPowers]
    set pe := p ^ j
    have hpe_pos : 0 < pe := Nat.pow_pos hp.pos
    set added := if pe ≤ 63 then acc.filterMap (fun d => let v := d * pe; if v ≤ 63 then some v else none) else []
    have hadded_nd : added.Nodup := by
      change (if pe ≤ 63 then acc.filterMap (fun d => let v := d * pe; if v ≤ 63 then some v else none) else []).Nodup
      split_ifs
      · refine hacc_nd.filterMap fun a b c h1 h2 => ?_
        dsimp only at h1 h2
        split_ifs at h1 with ha <;> simp at h1
        split_ifs at h2 with hb <;> simp at h2
        subst h1
        exact Nat.eq_of_mul_eq_mul_right hpe_pos h2.symm
      · exact List.nodup_nil
    have hadded_prop : ∀ v ∈ added, 0 < v ∧ v ∣ m ∧ v ≤ 63 ∧ (∀ q ∈ v.primeFactors, q ≤ p) ∧ v.factorization p = j := by
      intro v hv
      change v ∈ (if pe ≤ 63 then acc.filterMap (fun d => let v := d * pe; if v ≤ 63 then some v else none) else []) at hv
      split_ifs at hv with hpe63
      · rw [List.mem_filterMap] at hv
        obtain ⟨d, hd_mem, hdv⟩ := hv
        dsimp only at hdv
        split_ifs at hdv with hv63
        injection hdv with hveq; subst hveq
        obtain ⟨hd_pos, hdm, _, hdp⟩ := hacc d hd_mem
        have hnpd : ¬ p ∣ d := fun hdvd => by
          have hp_mem : p ∈ d.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hdvd, hd_pos.ne'⟩
          exact Nat.lt_irrefl p (hdp p hp_mem)
        have hcop : Nat.Coprime d pe := by
          exact (hp.coprime_iff_not_dvd.mpr hnpd).symm.pow_right j
        have hpe_dvd : pe ∣ m :=
          (hp.pow_dvd_iff_le_factorization hm).mpr (by simpa using hpow 0 (Nat.zero_lt_succ k))
        have hfac : (d * pe).factorization p = j := by
          rw [Nat.factorization_mul hd_pos.ne' hpe_pos.ne', Finsupp.coe_add, Pi.add_apply]
          rw [Nat.factorization_eq_zero_of_not_dvd hnpd, zero_add]
          simp [pe, hp.factorization_pow]
        refine ⟨Nat.mul_pos hd_pos hpe_pos, hcop.mul_dvd_of_dvd_of_dvd hdm hpe_dvd, hv63, ?_, hfac⟩
        intro q hq
        rw [Nat.primeFactors_mul hd_pos.ne' hpe_pos.ne', Finset.mem_union] at hq
        rcases hq with hq1 | hq2
        · exact (hdp q hq1).le
        · have hqp := Nat.prime_of_mem_primeFactors hq2
          have hqd : q ∣ p ^ j := Nat.dvd_of_mem_primeFactors hq2
          have hqdp : q ∣ p := hqp.dvd_of_dvd_pow hqd
          exact le_of_eq ((hp.dvd_iff_eq hqp.ne_one).mp hqdp).symm
      · simp at hv
    have hdisj : out.Disjoint added := by
      intro x hx1 hx2
      have h1 := (hout x hx1).2.2.2.2
      have h2 := (hadded_prop x hx2).2.2.2.2
      omega
    have hpow' : ∀ i < k, (j + 1) + i ≤ m.factorization p := fun i hi => by
      rw [show (j + 1) + i = j + (i + 1) by omega]
      exact hpow (i + 1) (Nat.succ_lt_succ hi)
    have hout' : ∀ d ∈ out ++ added, 0 < d ∧ d ∣ m ∧ d ≤ 63 ∧ (∀ q ∈ d.primeFactors, q ≤ p) ∧ d.factorization p < j + 1 := by
      intro d hd
      rw [List.mem_append] at hd
      rcases hd with hd1 | hd2
      · obtain ⟨a, b, c, e, f⟩ := hout d hd1
        exact ⟨a, b, c, e, by omega⟩
      · obtain ⟨a, b, c, e, f⟩ := hadded_prop d hd2
        exact ⟨a, b, c, e, by omega⟩
    have hnd' : (out ++ added).Nodup := hout_nd.append hadded_nd hdisj
    rw [show pe * p = p ^ (j + 1) by simp [pe, pow_succ]]
    exact ih (j + 1) hpow' (out ++ added) hnd' hout'

lemma divsUpTo63_sound {m : ℕ} (hm : m ≠ 0) {spec : List Entry} {minP : ℕ}
    (hs : SpecValid m spec minP) :
    (divsUpTo63 spec).Nodup ∧ ∀ d ∈ divsUpTo63 spec, 0 < d ∧ d ∣ m ∧ d ≤ 63 := by
  have hfold : ∀ (l : List Entry) (bound : ℕ) (acc : List Nat),
      (l.map (·.p)).Pairwise (· < ·) →
      (∀ e ∈ l, EntryValid m minP e ∧ bound < e.p) →
      acc.Nodup →
      (∀ d ∈ acc, 0 < d ∧ d ∣ m ∧ d ≤ 63 ∧ ∀ q ∈ d.primeFactors, q ≤ bound) →
      let res := l.foldl (fun a e => addPowers a e.p (e.minA + 1) 1 []) acc
      res.Nodup ∧ ∀ d ∈ res, 0 < d ∧ d ∣ m ∧ d ≤ 63 := by
    intro l
    induction l with
    | nil =>
      intro _ acc _ _ hnd hacc
      exact ⟨hnd, fun d hd => let ⟨a, b, c, _⟩ := hacc d hd; ⟨a, b, c⟩⟩
    | cons e es ih =>
      intro bound acc hpw hev hnd hacc
      simp only [List.foldl_cons]
      have he := hev e List.mem_cons_self
      have hpw_cons := List.pairwise_cons.mp hpw
      have he_p := he.1.1
      have hacc_lt : ∀ d ∈ acc, 0 < d ∧ d ∣ m ∧ d ≤ 63 ∧ ∀ q ∈ d.primeFactors, q < e.p := by
        intro d hd
        obtain ⟨a, b, c, hq⟩ := hacc d hd
        exact ⟨a, b, c, fun q hqm => lt_of_le_of_lt (hq q hqm) he.2⟩
      have hpow : ∀ i < e.minA + 1, 0 + i ≤ m.factorization e.p := fun i hi => by
        have := he.1.2.2.2.2.2.1; omega
      have hstep := addPowers_spec hm he_p acc hnd hacc_lt (e.minA + 1) 0 hpow [] List.nodup_nil (by simp)
      simp only [pow_zero] at hstep
      refine ih e.p _ hpw_cons.2 (fun e' he' => ?_) hstep.1 hstep.2
      exact ⟨(hev e' (List.mem_cons_of_mem e he')).1, hpw_cons.1 e'.p (List.mem_map_of_mem he')⟩
  have hbase : ([1] : List Nat).Nodup ∧ ∀ d ∈ ([1] : List Nat), 0 < d ∧ d ∣ m ∧ d ≤ 63 ∧ ∀ q ∈ d.primeFactors, q ≤ 0 := by
    refine ⟨List.nodup_singleton 1, fun d hd => ?_⟩
    simp only [List.mem_singleton] at hd; subst hd; simp
  exact hfold spec 0 [1] hs.1 (fun e he => ⟨hs.2.1 e he, Nat.lt_of_lt_of_le (by omega) (hs.2.1 e he).1.two_le⟩) hbase.1 hbase.2

-- =====================================================================
-- SpecValid operations & product factorization
-- =====================================================================

lemma specValid_mono_minP {m : ℕ} {spec : List Entry} {minP minP' : ℕ}
    (hs : SpecValid m spec minP) (hle : minP ≤ minP')
    (hrem : ∀ q ∈ m.primeFactors, (∃ e ∈ spec, e.p = q) ∨ minP' ≤ q) :
    SpecValid m spec minP' :=
  ⟨hs.1, fun e he => let ev := hs.2.1 e he; ⟨ev.1, lt_of_lt_of_le ev.2.1 hle, ev.2.2⟩, hrem⟩

lemma specValid_ext {m minP : ℕ} {spec : List Entry} (hs : SpecValid m spec minP)
    {p minA : ℕ} {exact : Bool} {par : Par}
    (hp : p.Prime) (hmin : minP ≤ p) (hodd : Odd p) (hdvd : p ∣ m)
    (h1 : 1 ≤ minA) (hle : minA ≤ m.factorization p)
    (hex : exact = true → m.factorization p = minA)
    (hpar : match par with | .odd => Odd (m.factorization p) | .even => Even (m.factorization p))
    (hminpar : minA % 2 = m.factorization p % 2)
    (hrem : ∀ q ∈ m.primeFactors, (∃ e ∈ spec, e.p = q) ∨ q = p ∨ p + 1 ≤ q) :
    SpecValid m (spec ++ [⟨p, minA, exact, par⟩]) (p + 1) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [List.map_append, List.map_singleton, List.pairwise_append]
    refine ⟨hs.1, List.pairwise_singleton _ _, fun x hx y hy => ?_⟩
    rw [List.mem_map] at hx
    obtain ⟨e, he, rfl⟩ := hx
    rw [List.mem_singleton] at hy; subst hy
    exact lt_of_lt_of_le (hs.2.1 e he).2.1 hmin
  · intro e he
    rw [List.mem_append, List.mem_singleton] at he
    rcases he with he | rfl
    · have ev := hs.2.1 e he
      exact ⟨ev.1, lt_of_lt_of_le ev.2.1 (by omega), ev.2.2⟩
    · exact ⟨hp, Nat.lt_succ_self p, hodd, hdvd, h1, hle, hex, hpar, hminpar⟩
  · intro q hq
    rcases hrem q hq with ⟨e, he, hqp⟩ | hqp | hge
    · left; exact ⟨e, List.mem_append_left _ he, hqp⟩
    · subst hqp
      left; exact ⟨⟨q, minA, exact, par⟩, List.mem_append_right _ (List.mem_singleton_self _), rfl⟩
    · right; exact hge

lemma spec_map_p_nodup {m : ℕ} {spec : List Entry} {minP : ℕ} (hs : SpecValid m spec minP) :
    (spec.map (·.p)).Nodup :=
  hs.1.imp (fun h => Nat.ne_of_lt h)

lemma spec_toFinset_subset {m : ℕ} {spec : List Entry} {minP : ℕ} (hm : m ≠ 0)
    (hs : SpecValid m spec minP) :
    (spec.map (·.p)).toFinset ⊆ m.primeFactors := by
  intro q hq
  rw [List.mem_toFinset, List.mem_map] at hq
  obtain ⟨e, he, rfl⟩ := hq
  have ev := hs.2.1 e he
  exact Nat.mem_primeFactors.mpr ⟨ev.1, ev.2.2.2.1, hm⟩

lemma spec_toFinset_card {m : ℕ} {spec : List Entry} {minP : ℕ} (hs : SpecValid m spec minP) :
    (spec.map (·.p)).toFinset.card = spec.length := by
  rw [List.toFinset_card_of_nodup (spec_map_p_nodup hs), List.length_map]

lemma prod_spec_factor_split {m : ℕ} (hm : m ≠ 0) {spec : List Entry} {minP : ℕ}
    (hs : SpecValid m spec minP) :
    (m = (spec.map (fun e => e.p ^ m.factorization e.p)).prod *
          ∏ q ∈ m.primeFactors \ (spec.map (·.p)).toFinset, q ^ m.factorization q) ∧
    (sigma 1 m = (spec.map (fun e => sigPP e.p (m.factorization e.p))).prod *
          ∏ q ∈ m.primeFactors \ (spec.map (·.p)).toFinset, sigPP q (m.factorization q)) := by
  set S := (spec.map (·.p)).toFinset
  have hsub : S ⊆ m.primeFactors := spec_toFinset_subset hm hs
  have hnd : spec.Nodup := (spec_map_p_nodup hs).of_map _
  have hndp : (spec.map (·.p)).Nodup := spec_map_p_nodup hs
  have hprod_m : (spec.map (fun e => e.p ^ m.factorization e.p)).prod =
      ∏ q ∈ S, q ^ m.factorization q := by
    rw [list_prod_toFinset hs.1]
    have h1 : S = spec.toFinset.image (·.p) := by
      ext q; simp [S]
    rw [h1, Finset.prod_image]
    intro a ha b hb hab
    simp only [Finset.mem_coe, List.mem_toFinset] at ha hb
    by_contra hne
    have : ∀ l : List Entry, (l.map (·.p)).Nodup → ∀ a ∈ l, ∀ b ∈ l, a.p = b.p → a = b := by
      intro l hl
      induction l with
      | nil => simp
      | cons x xs ih =>
        rw [List.map_cons, List.nodup_cons] at hl
        intro a ha b hb hab'
        rcases List.mem_cons.mp ha with rfl | ha' <;> rcases List.mem_cons.mp hb with rfl | hb'
        · rfl
        · exfalso; exact hl.1 (hab' ▸ List.mem_map_of_mem hb')
        · exfalso; exact hl.1 (hab'.symm ▸ List.mem_map_of_mem ha')
        · exact ih hl.2 a ha' b hb' hab'
    exact hne (this spec hndp a ha b hb hab)
  have hprod_s : (spec.map (fun e => sigPP e.p (m.factorization e.p))).prod =
      ∏ q ∈ S, sigPP q (m.factorization q) := by
    rw [list_prod_toFinset hs.1]
    have h1 : S = spec.toFinset.image (·.p) := by ext q; simp [S]
    rw [h1, Finset.prod_image]
    intro a ha b hb hab
    simp only [Finset.mem_coe, List.mem_toFinset] at ha hb
    by_contra hne
    have : ∀ l : List Entry, (l.map (·.p)).Nodup → ∀ a ∈ l, ∀ b ∈ l, a.p = b.p → a = b := by
      intro l hl
      induction l with
      | nil => simp
      | cons x xs ih =>
        rw [List.map_cons, List.nodup_cons] at hl
        intro a ha b hb hab'
        rcases List.mem_cons.mp ha with rfl | ha' <;> rcases List.mem_cons.mp hb with rfl | hb'
        · rfl
        · exfalso; exact hl.1 (hab' ▸ List.mem_map_of_mem hb')
        · exfalso; exact hl.1 (hab'.symm ▸ List.mem_map_of_mem ha')
        · exact ih hl.2 a ha' b hb' hab'
    exact hne (this spec hndp a ha b hb hab)
  constructor
  · rw [hprod_m, mul_comm, Finset.prod_sdiff hsub]
    exact Nat.prod_primeFactors_pow_factorization hm
  · rw [hprod_s, mul_comm, Finset.prod_sdiff hsub]
    exact sigma_one_eq_prod_primeFactors hm

lemma prod_spec_dvd_and_sigma {m : ℕ} (hm : m ≠ 0) {spec : List Entry} {minP : ℕ}
    (hs : SpecValid m spec minP) (expFn : Entry → ℕ)
    (hle : ∀ e ∈ spec, expFn e ≤ m.factorization e.p) :
    let B := (spec.map (fun e => e.p ^ expFn e)).prod
    let SB := (spec.map (fun e => sigPP e.p (expFn e))).prod
    0 < B ∧ B ∣ m ∧ sigma 1 B = SB := by
  intro B SB
  have hB_pos : 0 < B := by
    dsimp [B]
    exact List.prod_pos fun x hx => by
      rw [List.mem_map] at hx
      obtain ⟨e, he, rfl⟩ := hx
      exact Nat.pow_pos (hs.2.1 e he).1.pos
  have h_dvd_list : ∀ l : List Entry, (l.map (·.p)).Pairwise (· < ·) →
      (∀ e ∈ l, EntryValid m minP e ∧ expFn e ≤ m.factorization e.p) →
      (l.map (fun e => e.p ^ expFn e)).prod ∣ m ∧
      sigma 1 (l.map (fun e => e.p ^ expFn e)).prod = (l.map (fun e => sigPP e.p (expFn e))).prod := by
    intro l hpw hl
    induction l with
    | nil => simp
    | cons e es ih =>
      rw [List.map_cons, List.pairwise_cons] at hpw
      have he := hl e List.mem_cons_self
      have ih_res := ih hpw.2 (fun e' he' => hl e' (List.mem_cons_of_mem e he'))
      have hep := he.1.1
      have hpow_dvd : e.p ^ expFn e ∣ m := (hep.pow_dvd_iff_le_factorization hm).mpr he.2
      have hcop : Nat.Coprime (e.p ^ expFn e) (es.map (fun e' => e'.p ^ expFn e')).prod := by
        have hcop_gen : ∀ l' : List Entry, (∀ e' ∈ l', EntryValid m minP e' ∧ e.p < e'.p) →
            Nat.Coprime (e.p ^ expFn e) (l'.map (fun e' => e'.p ^ expFn e')).prod := by
          intro l' hl'
          induction l' with
          | nil => simp
          | cons y ys ihy =>
            simp only [List.map_cons, List.prod_cons]
            have hy := hl' y List.mem_cons_self
            have h1 : Nat.Coprime (e.p ^ expFn e) (y.p ^ expFn y) :=
              (hep.coprime_iff_not_dvd.mpr fun h => absurd (Nat.dvd_prime hy.1.1 |>.mp h |>.resolve_left hep.ne_one) hy.2.ne).pow _ _
            exact h1.mul_right (ihy fun e' he' => hl' e' (List.mem_cons_of_mem y he'))
        exact hcop_gen es fun e' he' => ⟨(hl e' (List.mem_cons_of_mem e he')).1, hpw.1 e'.p (List.mem_map_of_mem he')⟩
      refine ⟨hcop.mul_dvd_of_dvd_of_dvd hpow_dvd ih_res.1, ?_⟩
      simp only [List.map_cons, List.prod_cons]
      rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop,
          sigma_one_prime_pow hep, ih_res.2]
  have hres := h_dvd_list spec hs.1 (fun e he => ⟨hs.2.1 e he, hle e he⟩)
  exact ⟨hB_pos, hres.1, hres.2⟩

-- =====================================================================
-- Parity, mod 4, checkG, allowedEEmpty, allowedEMask soundness
-- =====================================================================

lemma list_map_prod_dvd {α : Type*} (l : List α) (f g : α → ℕ) (h : ∀ x ∈ l, f x ∣ g x) :
    (l.map f).prod ∣ (l.map g).prod := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.map_cons, List.prod_cons]
    exact mul_dvd_mul (h a List.mem_cons_self) (ih fun x hx => h x (List.mem_cons_of_mem a hx))

lemma checkG_sound {m : ℕ} (hm : m ≠ 0) {spec : List Entry} {minP g : ℕ}
    (hs : SpecValid m spec minP) (hg : checkG spec g = true) :
    0 < g ∧ g ∣ sigma 1 m ∧ g ∣ 2 * m := by
  unfold checkG at hg
  split_ifs at hg with hg0
  have hgpos : 0 < g := Nat.pos_of_ne_zero (fun h => hg0 (beq_iff_eq.mpr h))
  simp only [Bool.and_eq_true, beq_iff_eq] at hg
  obtain ⟨hsig, hmin⟩ := hg
  have hminM_dvd : spec.foldl (fun acc e => acc * e.p ^ e.minA) 1 ∣ m := by
    rw [foldl_mul_eq, one_mul]
    exact (prod_spec_dvd_and_sigma hm hs (·.minA) (fun e he => (hs.2.1 e he).2.2.2.2.2.1)).2.1
  have hsigK_dvd : spec.foldl (fun acc e =>
      acc * (if e.exact then sigPP e.p e.minA else if e.par == .odd then e.p + 1 else 1)) 1 ∣ sigma 1 m := by
    rw [foldl_mul_eq, one_mul]
    rw [(prod_spec_factor_split hm hs).2]
    refine dvd_mul_of_dvd_left (list_map_prod_dvd spec _ _ fun e he => ?_) _
    have ev := hs.2.1 e he
    split_ifs with hex hodd
    · rw [ev.2.2.2.2.2.2.1 hex]
    · have hpar : e.par = .odd := by simpa using hodd
      have hv : Odd (m.factorization e.p) := by simpa [hpar] using ev.2.2.2.2.2.2.2.1
      exact succ_dvd_sigPP ev.1.one_lt hv
    · exact one_dvd _
  have hsig_dvd : g ∣ sigma 1 m := by
    refine (Nat.dvd_of_mod_eq_zero hsig).trans ?_
    simpa only [beq_iff_eq] using hsigK_dvd
  exact ⟨hgpos, hsig_dvd, (Nat.dvd_of_mod_eq_zero hmin).trans (mul_dvd_mul_left 2 hminM_dvd)⟩

lemma checkBitsStep_sound (ss step : ℕ) (hstep : 0 < step) :
    ∀ (fuel idx : ℕ), checkBitsStep ss idx step fuel = true →
      ∀ k, idx ≤ k → k ≤ 63 → (k - idx) % step = 0 → (k - idx) / step < fuel →
        ((ss / 2 ^ k) % 2 == 1) = true := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _ _ _ _ hk; exact absurd hk (Nat.not_lt_zero _)
  | succ fuel ih =>
    intro idx hchk k hik hk63 hmod hdiv
    unfold checkBitsStep at hchk
    split_ifs at hchk with hgt hbit
    · omega
    · by_cases heq : k = idx
      · subst heq
        rcases Nat.mod_two_eq_zero_or_one (ss / 2 ^ k) with h0 | h1
        · exfalso; exact hbit (beq_iff_eq.mpr h0)
        · exact beq_iff_eq.mpr h1
      · have hk_ge : idx + step ≤ k := by
          have : 0 < k - idx := by omega
          have hdvd : step ∣ k - idx := Nat.dvd_of_mod_eq_zero hmod
          have : step ≤ k - idx := Nat.le_of_dvd this hdvd
          omega
        have hmod' : (k - (idx + step)) % step = 0 := by
          rw [show k - idx = (k - (idx + step)) + step by omega, Nat.add_mod_right] at hmod
          exact hmod
        have hdiv' : (k - (idx + step)) / step < fuel := by
          rw [show k - idx = (k - (idx + step)) + step by omega, Nat.add_div_right _ hstep] at hdiv
          exact Nat.lt_of_succ_lt_succ hdiv
        exact ih (idx + step) hchk k hk_ge hk63 hmod' hdiv'

lemma checkBits_mem_iff (ss : ℕ) (hasOdd allEven needMod4 : Bool) (g : ℕ) :
    ∀ x ≤ 63, ∀ acc k,
      k ∈ checkBits ss hasOdd allEven needMod4 g x acc ↔
      k ∈ acc ∨ (63 - x < k ∧ k ≤ 63 ∧
        ((!hasOdd || k % 2 == 0) && (!allEven || k % 2 == 1) && (!needMod4 || k % 4 == 2) &&
         (k % g == 0) && ((ss / (2 ^ k)) % 2 == 0)) = true) := by
  intro x
  induction x with
  | zero =>
    intro _ acc k
    simp only [checkBits, Nat.sub_zero, iff_self_or]
    intro ⟨h1, h2, _⟩; omega
  | succ n ih =>
    intro hle acc k
    unfold checkBits
    dsimp only
    split_ifs with hok
    · rw [ih (by omega) _ k, List.mem_cons]
      constructor
      · rintro ((rfl | ha) | ⟨h1, h2, h3⟩)
        · right; exact ⟨by omega, by omega, hok⟩
        · left; exact ha
        · right; exact ⟨by omega, h2, h3⟩
      · rintro (ha | ⟨h1, h2, h3⟩)
        · left; right; exact ha
        · by_cases heq : k = 63 - n
          · subst heq; left; left; rfl
          · right; exact ⟨by omega, h2, h3⟩
    · rw [ih (by omega) _ k]
      constructor
      · rintro (ha | ⟨h1, h2, h3⟩)
        · left; exact ha
        · right; exact ⟨by omega, h2, h3⟩
      · rintro (ha | ⟨h1, h2, h3⟩)
        · left; exact ha
        · right
          refine ⟨?_, h2, h3⟩
          by_contra hlt
          have heq : k = 63 - n := by omega
          subst heq; exact hok h3

lemma spec_parity_even_sigma {m : ℕ} (hm : m ≠ 0) {spec : List Entry} {minP : ℕ}
    (hs : SpecValid m spec minP) (hodd : spec.any (·.par == .odd) = true) :
    2 ∣ sigma 1 m := by
  rw [List.any_eq_true] at hodd
  obtain ⟨e, he, hpar⟩ := hodd
  have ev := hs.2.1 e he
  have hpe : e.par = .odd := by simpa using hpar
  have hv : Odd (m.factorization e.p) := by simpa [hpe] using ev.2.2.2.2.2.2.2.1
  have h2succ : 2 ∣ e.p + 1 := (ev.2.2.1.add_one).two_dvd
  have hdvd_s : sigPP e.p (m.factorization e.p) ∣ sigma 1 m := by
    rw [(prod_spec_factor_split hm hs).2]
    exact dvd_mul_of_dvd_left (List.dvd_prod (List.mem_map_of_mem he)) _
  exact h2succ.trans ((succ_dvd_sigPP ev.1.one_lt hv).trans hdvd_s)

lemma spec_allEven_odd_sigma {m : ℕ} (hm : m ≠ 0) (hm_card : m.primeFactors.card ≤ 5)
    {spec : List Entry} {minP : ℕ} (hs : SpecValid m spec minP)
    (hlen : 5 - spec.length = 0) (hall : spec.all (·.par == .even) = true) :
    Odd (sigma 1 m) := by
  have hsub : (spec.map (·.p)).toFinset ⊆ m.primeFactors := spec_toFinset_subset hm hs
  have hcard : (spec.map (·.p)).toFinset.card = m.primeFactors.card := by
    have := spec_toFinset_card hs
    have hle := Finset.card_le_card hsub
    omega
  have heq : (spec.map (·.p)).toFinset = m.primeFactors :=
    Finset.eq_of_subset_of_card_le hsub (by omega)
  have hrem_empty : m.primeFactors \ (spec.map (·.p)).toFinset = ∅ := by
    rw [heq, Finset.sdiff_self]
  rw [(prod_spec_factor_split hm hs).2, hrem_empty, Finset.prod_empty, mul_one]
  rw [List.all_eq_true] at hall
  have hodd_prod : ∀ l : List Entry, (∀ e ∈ l, EntryValid m minP e ∧ e.par = .even) →
      Odd (l.map (fun e => sigPP e.p (m.factorization e.p))).prod := by
    intro l hl
    induction l with
    | nil => simp
    | cons e es ih =>
      simp only [List.map_cons, List.prod_cons]
      have he := hl e List.mem_cons_self
      have hv : Even (m.factorization e.p) := by simpa [he.2] using he.1.2.2.2.2.2.2.2.1
      have h1 : Odd (sigPP e.p (m.factorization e.p)) := (sigPP_odd_iff he.1.1.one_lt he.1.2.2.1 _).mpr hv
      exact h1.mul (ih fun e' he' => hl e' (List.mem_cons_of_mem e he'))
  exact hodd_prod spec fun e he => ⟨hs.2.1 e he, by simpa using hall e he⟩

lemma spec_needMod4_dvd_sigma {m : ℕ} (hm : m ≠ 0) {spec : List Entry} {minP : ℕ}
    (hs : SpecValid m spec minP)
    (h4 : (decide (2 ≤ spec.countP (·.par == .odd)) || spec.any (fun e => e.par == .odd && e.p % 4 == 3)) = true) :
    4 ∣ sigma 1 m := by
  rw [Bool.or_eq_true] at h4
  rcases h4 with hcnt | hany
  · rw [decide_eq_true_eq] at hcnt
    have hnd : spec.Nodup := (spec_map_p_nodup hs).of_map _
    have h2 : ∀ l : List Entry, l.Nodup → 2 ≤ l.countP (·.par == .odd) →
        (∀ e ∈ l, EntryValid m minP e) →
        4 ∣ (l.map (fun e => if e.par == .odd then 2 else 1)).prod := by
      intro l hnd' hc hl
      induction l with
      | nil => simp at hc
      | cons e es ih =>
        rw [List.nodup_cons] at hnd'
        simp only [List.map_cons, List.prod_cons] at hc ⊢
        rw [List.countP_cons] at hc
        by_cases he : (e.par == .odd) = true
        · simp only [he, ite_true] at hc ⊢
          have hc1 : 1 ≤ es.countP (·.par == .odd) := by omega
          have h2_es : ∀ l' : List Entry, 1 ≤ l'.countP (·.par == .odd) →
              2 ∣ (l'.map (fun e => if e.par == .odd then 2 else 1)).prod := by
            intro l' hl'
            induction l' with
            | nil => simp at hl'
            | cons x xs ihx =>
              simp only [List.map_cons, List.prod_cons] at hl' ⊢
              rw [List.countP_cons] at hl'
              by_cases hx : (x.par == .odd) = true
              · simp only [hx, ite_true]; exact dvd_mul_right 2 _
              · have hxf : (x.par == .odd) = false := Bool.eq_false_iff.mpr hx
                simp only [hxf, Bool.false_eq_true, ite_false] at hl' ⊢
                exact dvd_mul_of_dvd_right (ihx (by omega)) _
          exact mul_dvd_mul dvd_rfl (h2_es es hc1)
        · have hef : (e.par == .odd) = false := Bool.eq_false_iff.mpr he
          simp only [hef, Bool.false_eq_true, ite_false] at hc ⊢
          exact dvd_mul_of_dvd_right (ih hnd'.2 (by omega) fun x hx => hl x (List.mem_cons_of_mem e hx)) _
    have hdvd1 := h2 spec hnd hcnt hs.2.1
    have hdvd2 : (spec.map (fun e => if e.par == .odd then 2 else 1)).prod ∣
        (spec.map (fun e => sigPP e.p (m.factorization e.p))).prod := by
      refine list_map_prod_dvd spec _ _ fun e he => ?_
      split_ifs with hpar
      · have ev := hs.2.1 e he
        have hpe : e.par = .odd := by simpa using hpar
        have hv : Odd (m.factorization e.p) := by simpa [hpe] using ev.2.2.2.2.2.2.2.1
        exact (ev.2.2.1.add_one.two_dvd).trans (succ_dvd_sigPP ev.1.one_lt hv)
      · exact one_dvd _
    rw [(prod_spec_factor_split hm hs).2]
    exact hdvd1.trans (hdvd2.trans (dvd_mul_right _ _))
  · rw [List.any_eq_true] at hany
    obtain ⟨e, he, hcond⟩ := hany
    simp only [Bool.and_eq_true, beq_iff_eq] at hcond
    obtain ⟨hpar, hmod4⟩ := hcond
    have ev := hs.2.1 e he
    have hv : Odd (m.factorization e.p) := by simpa [hpar] using ev.2.2.2.2.2.2.2.1
    have h4succ : 4 ∣ e.p + 1 := Nat.dvd_of_mod_eq_zero (by omega)
    have hdvd_s : sigPP e.p (m.factorization e.p) ∣ sigma 1 m := by
      rw [(prod_spec_factor_split hm hs).2]
      exact dvd_mul_of_dvd_left (List.dvd_prod (List.mem_map_of_mem he)) _
    exact h4succ.trans ((succ_dvd_sigPP ev.1.one_lt hv).trans hdvd_s)

lemma allowedEEmpty_sound {m : ℕ} (hm_odd : Odd m) (hm_ab : m.Abundant)
    (hm_card : m.primeFactors.card ≤ 5) (_h64 : 64 ≤ m)
    {spec : List Entry} {minP g : ℕ} (hs : SpecValid m spec minP)
    (hE : sigma 1 m - 2 * m < 64) (ha : allowedEEmpty spec g = true) : Goal m := by
  have hm0 : m ≠ 0 := hm_odd.pos.ne'
  have h2m_lt : 2 * m < sigma 1 m := (abundant_iff_two_mul_lt_sigma m).mp hm_ab
  set E := sigma 1 m - 2 * m
  have hE1 : 1 ≤ E := by omega
  have hE63 : E ≤ 63 := by omega
  unfold allowedEEmpty at ha
  simp only [Bool.and_eq_true] at ha
  obtain ⟨hg_chk, hchk⟩ := ha
  obtain ⟨hg_pos, hg_sig, hg_2m⟩ := checkG_sound hm0 hs hg_chk
  have hg_E : g ∣ E := Nat.dvd_sub hg_sig hg_2m
  have hE_mod_g : E % g = 0 := Nat.mod_eq_zero_of_dvd hg_E
  set hasOdd := spec.any (·.par == .odd)
  set allEven := (5 - spec.length == 0) && spec.all (·.par == .even)
  set oddCount := spec.countP (·.par == .odd)
  set needMod4 := (decide (2 ≤ oddCount)) || spec.any (fun e => e.par == .odd && e.p % 4 == 3)
  have h_even : hasOdd = true → E % 2 = 0 := fun h => by
    have h2 : 2 ∣ sigma 1 m := spec_parity_even_sigma hm0 hs h
    have h2E : 2 ∣ E := Nat.dvd_sub h2 (dvd_mul_right 2 m)
    exact Nat.mod_eq_zero_of_dvd h2E
  have h_odd : allEven = true → E % 2 = 1 := fun h => by
    simp only [allEven, Bool.and_eq_true, beq_iff_eq] at h
    have hos : Odd (sigma 1 m) := spec_allEven_odd_sigma hm0 hm_card hs h.1 h.2
    obtain ⟨k, hk⟩ := hos
    have : (2 * k + 1 - 2 * m) % 2 = 1 := by omega
    rw [← hk] at this; exact this
  have h_mod4 : needMod4 = true → E % 4 = 2 := fun h => by
    have h4 : 4 ∣ sigma 1 m := spec_needMod4_dvd_sigma hm0 hs h
    obtain ⟨k, hk⟩ := h4
    obtain ⟨t, ht⟩ := hm_odd
    have : (4 * k - 2 * (2 * t + 1)) % 4 = 2 := by omega
    rw [← hk, ← ht] at this; exact this
  set ss := subsetMask (divsUpTo63 spec)
  have hbit : ((ss / 2 ^ E) % 2 == 1) = true := by
    split_ifs at hchk with hm4 hm4g4 hm4g2 ho hog2 hae haeg2
    · exfalso; have := h_mod4 hm4; have : 4 ∣ g := Nat.dvd_of_mod_eq_zero (beq_iff_eq.mp hm4g4); have : 4 ∣ E := this.trans hg_E; omega
    · have := h_mod4 hm4
      have hg2 : g % 2 = 0 := beq_iff_eq.mp hm4g2
      have hE_ge : g ≤ E := Nat.le_of_dvd (by omega) hg_E
      have hmod2g : (E - g) % (2 * g) = 0 := by
        obtain ⟨q, hq⟩ := hg_E
        have hqodd : Odd q := by
          by_contra hne
          obtain ⟨r, hr⟩ := Nat.not_odd_iff_even.mp hne
          have h4g : 4 ∣ 2 * g := by omega
          have h4E : 4 ∣ E := by rw [hq, show g * q = (2 * g) * r by rw [hr]; ring]; exact dvd_mul_of_dvd_left (by omega) r
          omega
        obtain ⟨r, rfl⟩ := hqodd
        rw [hq, show g * (2 * r + 1) - g = r * (2 * g) by rw [show g * (2 * r + 1) = r * (2 * g) + g by ring, Nat.add_sub_cancel]]
        exact Nat.mul_mod_left r (2 * g)
      have hdiv : (E - g) / (2 * g) < 64 :=
        lt_of_le_of_lt (Nat.div_le_self (E - g) (2 * g)) (by omega)
      exact checkBitsStep_sound ss (2 * g) (by omega) 64 g hchk E hE_ge hE63 hmod2g hdiv
    · have := h_mod4 hm4
      have hg2 : g % 2 ≠ 0 := fun h => hm4g2 (beq_iff_eq.mpr h)
      have hg_odd : Odd g := Nat.not_even_iff_odd.mp (fun he => hg2 (Nat.mod_eq_zero_of_dvd he.two_dvd))
      have h2g_dvd : 2 * g ∣ E := by
        have h2E : 2 ∣ E := Nat.dvd_of_mod_eq_zero (by omega)
        exact (Nat.coprime_two_left.mpr hg_odd).mul_dvd_of_dvd_of_dvd h2E hg_E
      have hE_ge : 2 * g ≤ E := Nat.le_of_dvd (by omega) h2g_dvd
      have hmod4g : (E - 2 * g) % (4 * g) = 0 := by
        obtain ⟨q, hq⟩ := h2g_dvd
        have hqodd : Odd q := by
          by_contra hne
          obtain ⟨r, hr⟩ := Nat.not_odd_iff_even.mp hne
          have : 4 ∣ E := by rw [hq, hr]; ring_nf; omega
          omega
        obtain ⟨r, rfl⟩ := hqodd
        rw [hq, show 2 * g * (2 * r + 1) - 2 * g = r * (4 * g) by rw [show 2 * g * (2 * r + 1) = r * (4 * g) + 2 * g by ring, Nat.add_sub_cancel]]
        exact Nat.mul_mod_left r (4 * g)
      have hdiv : (E - 2 * g) / (4 * g) < 64 :=
        lt_of_le_of_lt (Nat.div_le_self (E - 2 * g) (4 * g)) (by omega)
      exact checkBitsStep_sound ss (4 * g) (by omega) 64 (2 * g) hchk E hE_ge hE63 hmod4g hdiv
    · have := h_even ho
      have hE_ge : g ≤ E := Nat.le_of_dvd (by omega) hg_E
      have hmodg : (E - g) % g = 0 := Nat.mod_eq_zero_of_dvd (Nat.dvd_sub hg_E dvd_rfl)
      have hdiv : (E - g) / g < 64 := lt_of_le_of_lt (Nat.div_le_self (E - g) g) (by omega)
      exact checkBitsStep_sound ss g hg_pos 64 g hchk E hE_ge hE63 hmodg hdiv
    · have := h_even ho
      have hg2 : g % 2 ≠ 0 := fun h => hog2 (beq_iff_eq.mpr h)
      have hg_odd : Odd g := Nat.not_even_iff_odd.mp (fun he => hg2 (Nat.mod_eq_zero_of_dvd he.two_dvd))
      have h2g_dvd : 2 * g ∣ E := (Nat.coprime_two_left.mpr hg_odd).mul_dvd_of_dvd_of_dvd (Nat.dvd_of_mod_eq_zero (by omega)) hg_E
      have hE_ge : 2 * g ≤ E := Nat.le_of_dvd (by omega) h2g_dvd
      have hmod2g : (E - 2 * g) % (2 * g) = 0 := Nat.mod_eq_zero_of_dvd (Nat.dvd_sub h2g_dvd dvd_rfl)
      have hdiv : (E - 2 * g) / (2 * g) < 64 := lt_of_le_of_lt (Nat.div_le_self (E - 2 * g) (2 * g)) (by omega)
      exact checkBitsStep_sound ss (2 * g) (by omega) 64 (2 * g) hchk E hE_ge hE63 hmod2g hdiv
    · exfalso; have := h_odd (Bool.and_eq_true_iff.mpr hae); have : 2 ∣ g := Nat.dvd_of_mod_eq_zero (beq_iff_eq.mp haeg2); have : 2 ∣ E := this.trans hg_E; omega
    · have := h_odd (Bool.and_eq_true_iff.mpr hae)
      have hE_ge : g ≤ E := Nat.le_of_dvd (by omega) hg_E
      have hmod2g : (E - g) % (2 * g) = 0 := by
        obtain ⟨q, hq⟩ := hg_E
        have hqodd : Odd q := by
          by_contra hne
          obtain ⟨r, hr⟩ := Nat.not_odd_iff_even.mp hne
          have : E % 2 = 0 := by rw [hq, hr]; ring_nf; omega
          omega
        obtain ⟨r, rfl⟩ := hqodd
        rw [hq, show g * (2 * r + 1) - g = r * (2 * g) by rw [show g * (2 * r + 1) = r * (2 * g) + g by ring, Nat.add_sub_cancel]]
        exact Nat.mul_mod_left r (2 * g)
      have hdiv : (E - g) / (2 * g) < 64 :=
        lt_of_le_of_lt (Nat.div_le_self (E - g) (2 * g)) (by omega)
      exact checkBitsStep_sound ss (2 * g) (by omega) 64 g hchk E hE_ge hE63 hmod2g hdiv
    · have hE_ge : g ≤ E := Nat.le_of_dvd (by omega) hg_E
      have hmodg : (E - g) % g = 0 := Nat.mod_eq_zero_of_dvd (Nat.dvd_sub hg_E dvd_rfl)
      have hdiv : (E - g) / g < 64 := lt_of_le_of_lt (Nat.div_le_self (E - g) g) (by omega)
      exact checkBitsStep_sound ss g hg_pos 64 g hchk E hE_ge hE63 hmodg hdiv
  obtain ⟨hnd, hdivs⟩ := divsUpTo63_sound hm0 hs
  obtain ⟨s, hs_sub, hsum⟩ := subsetMask_sound hnd (by omega) hbit
  refine ⟨s, fun d hd => (hdivs d (List.mem_toFinset.mp (hs_sub hd))).2.1, hsum⟩

lemma goal_of_not_mem_allowedEMask {m : ℕ} (hm_odd : Odd m) (hm_ab : m.Abundant)
    (hm_card : m.primeFactors.card ≤ 5)
    {spec : List Entry} {minP g : ℕ} (hs : SpecValid m spec minP)
    (hg_chk : checkG spec g = true)
    (hE_lt : sigma 1 m - 2 * m < 64)
    (hnot : (allowedEMask spec g).contains (sigma 1 m - 2 * m) = false) : Goal m := by
  have hm0 : m ≠ 0 := hm_odd.pos.ne'
  have h2m_lt : 2 * m < sigma 1 m := (abundant_iff_two_mul_lt_sigma m).mp hm_ab
  set E := sigma 1 m - 2 * m
  have hE1 : 1 ≤ E := by omega
  have hE63 : E ≤ 63 := by omega
  obtain ⟨hg_pos, hg_sig, hg_2m⟩ := checkG_sound hm0 hs hg_chk
  have hg_E : g ∣ E := Nat.dvd_sub hg_sig hg_2m
  set hasOdd := spec.any (·.par == .odd)
  set allEven := (5 - spec.length == 0) && spec.all (·.par == .even)
  set oddCount := spec.countP (·.par == .odd)
  set needMod4 := (decide (2 ≤ oddCount)) || spec.any (fun e => e.par == .odd && e.p % 4 == 3)
  have h1 : (!hasOdd || E % 2 == 0) = true := by
    rw [Bool.or_eq_true]; by_cases h : hasOdd = true
    · right; rw [beq_iff_eq]; exact Nat.mod_eq_zero_of_dvd (Nat.dvd_sub (spec_parity_even_sigma hm0 hs h) (dvd_mul_right 2 m))
    · left; simp [h]
  have h2 : (!allEven || E % 2 == 1) = true := by
    rw [Bool.or_eq_true]; by_cases h : allEven = true
    · right; rw [beq_iff_eq]
      simp only [allEven, Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨k, hk⟩ := spec_allEven_odd_sigma hm0 hm_card hs h.1 h.2
      have : (2 * k + 1 - 2 * m) % 2 = 1 := by omega
      rw [← hk] at this; exact this
    · left; simp [h]
  have h3 : (!needMod4 || E % 4 == 2) = true := by
    rw [Bool.or_eq_true]; by_cases h : needMod4 = true
    · right; rw [beq_iff_eq]
      obtain ⟨k, hk⟩ := spec_needMod4_dvd_sigma hm0 hs h
      obtain ⟨t, ht⟩ := hm_odd
      have : (4 * k - 2 * (2 * t + 1)) % 4 = 2 := by omega
      rw [← hk, ← ht] at this; exact this
    · left; simp [h]
  have h4 : (E % g == 0) = true := beq_iff_eq.mpr (Nat.mod_eq_zero_of_dvd hg_E)
  have hbit : ((subsetMask (divsUpTo63 spec) / 2 ^ E) % 2 == 1) = true := by
    by_contra hbad
    have h0 : ((subsetMask (divsUpTo63 spec) / 2 ^ E) % 2 == 0) = true := by
      rcases Nat.mod_two_eq_zero_or_one (subsetMask (divsUpTo63 spec) / 2 ^ E) with hz | ho
      · exact beq_iff_eq.mpr hz
      · exfalso; exact hbad (beq_iff_eq.mpr ho)
    have hmem : E ∈ allowedEMask spec g := by
      unfold allowedEMask
      rw [List.mem_reverse, checkBits_mem_iff _ _ _ _ _ 63 (le_rfl) [] E]
      right
      refine ⟨by omega, hE63, ?_⟩
      change ((((!hasOdd || E % 2 == 0) && (!allEven || E % 2 == 1) && (!needMod4 || E % 4 == 2) &&
               (E % g == 0) && ((subsetMask (divsUpTo63 spec) / 2 ^ E) % 2 == 0)) = true))
      rw [h1, h2, h3, h4, h0]; rfl
    have hc : (allowedEMask spec g).contains E = true := List.contains_iff_mem.mpr hmem
    rw [hc] at hnot
    exact Bool.noConfusion hnot
  obtain ⟨hnd, hdivs⟩ := divsUpTo63_sound hm0 hs
  obtain ⟨s, hs_sub, hsum⟩ := subsetMask_sound hnd (by omega) hbit
  exact ⟨s, fun d hd => (hdivs d (List.mem_toFinset.mp (hs_sub hd))).2.1, hsum⟩

-- =====================================================================
-- maxAbTail, maxAbSpec, prodWithCur, expandFree, tail, NF1, R1, R2
-- =====================================================================

lemma maxAbTail_spec (m : ℕ) :
    ∀ (rem : ℕ) (q n0 d0 : ℕ) (qs : List ℕ) (A B : ℕ),
      0 < d0 → A * d0 ≤ B * n0 →
      qs.Pairwise (· < ·) → qs.length ≤ rem →
      (∀ r ∈ qs, r.Prime ∧ q ≤ r) →
      ∀ n d, maxAbTail rem q n0 d0 = (n, d) → 0 < d →
      (A * (qs.map (fun r => sigPP r (m.factorization r))).prod) * d ≤
      (B * (qs.map (fun r => r ^ m.factorization r)).prod) * n := by
  intro rem
  induction rem with
  | zero =>
    intro q n0 d0 qs A B _ hAB _ hlen _ n d hmax _
    have hnil : qs = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hlen)
    subst hnil
    simp only [maxAbTail] at hmax
    injection hmax with hn hd; subst hn; subst hd
    simpa using hAB
  | succ rem ih =>
    intro q n0 d0 qs A B hd0 hAB hpw hlen hqp n d hmax hdpos
    simp only [maxAbTail] at hmax
    cases hnp : nextPrime q with
    | none =>
      rw [hnp] at hmax
      injection hmax with _ hd
      omega
    | some q' =>
      rw [hnp] at hmax
      obtain ⟨hqq', hq'p, hq'min⟩ := nextPrime_spec hnp
      have hq'1 : 1 < q' := hq'p.one_lt
      have hd0' : 0 < d0 * (q' - 1) := Nat.mul_pos hd0 (Nat.sub_pos_of_lt hq'1)
      cases qs with
      | nil =>
        have hAB' : A * (d0 * (q' - 1)) ≤ B * (n0 * q') := by
          have hq'le : q' - 1 ≤ q' := Nat.sub_le q' 1
          calc A * (d0 * (q' - 1)) = (A * d0) * (q' - 1) := by ring
            _ ≤ (B * n0) * q' := Nat.mul_le_mul hAB hq'le
            _ = B * (n0 * q') := by ring
        simpa using ih (q' + 1) (n0 * q') (d0 * (q' - 1)) [] A B hd0' hAB'
          List.Pairwise.nil (Nat.zero_le _) (by simp) n d hmax hdpos
      | cons r rs =>
        rw [List.pairwise_cons] at hpw
        rw [List.length_cons] at hlen
        have hr := hqp r List.mem_cons_self
        have hq'r : q' ≤ r := by
          by_contra hlt
          exact hq'min r hr.2 (Nat.lt_of_not_le hlt) hr.1
        have hrs_p : ∀ y ∈ rs, y.Prime ∧ q' + 1 ≤ y := fun y hy => by
          have hy' := hqp y (List.mem_cons_of_mem r hy)
          have hry := hpw.1 y hy
          exact ⟨hy'.1, by omega⟩
        have hsig_r : sigPP r (m.factorization r) * (q' - 1) ≤ q' * r ^ m.factorization r := by
          have h1 : sigPP r (m.factorization r) * (r - 1) ≤ r * r ^ m.factorization r :=
            (sigPP_lt_bound hr.1.one_lt (m.factorization r)).le
          have h2 : r * (q' - 1) ≤ q' * (r - 1) := by
            zify [hq'1.le, hr.1.one_lt.le]
            nlinarith
          have hr1_pos : 0 < r - 1 := Nat.sub_pos_of_lt hr.1.one_lt
          apply Nat.le_of_mul_le_mul_right _ hr1_pos
          calc sigPP r (m.factorization r) * (q' - 1) * (r - 1)
              = (sigPP r (m.factorization r) * (r - 1)) * (q' - 1) := by ring
            _ ≤ (r * r ^ m.factorization r) * (q' - 1) := Nat.mul_le_mul_right _ h1
            _ = (r * (q' - 1)) * r ^ m.factorization r := by ring
            _ ≤ (q' * (r - 1)) * r ^ m.factorization r := Nat.mul_le_mul_right _ h2
            _ = q' * r ^ m.factorization r * (r - 1) := by ring
        have hAB' : (A * sigPP r (m.factorization r)) * (d0 * (q' - 1)) ≤
                    (B * r ^ m.factorization r) * (n0 * q') := by
          calc (A * sigPP r (m.factorization r)) * (d0 * (q' - 1))
              = (A * d0) * (sigPP r (m.factorization r) * (q' - 1)) := by ring
            _ ≤ (B * n0) * (q' * r ^ m.factorization r) := Nat.mul_le_mul hAB hsig_r
            _ = (B * r ^ m.factorization r) * (n0 * q') := by ring
        have ih_res := ih (q' + 1) (n0 * q') (d0 * (q' - 1)) rs
          (A * sigPP r (m.factorization r)) (B * r ^ m.factorization r)
          hd0' hAB' hpw.2 (Nat.le_of_succ_le_succ hlen) hrs_p n d hmax hdpos
        simpa [List.map_cons, List.prod_cons, mul_assoc] using ih_res

lemma maxAbSpec_spec_part {m : ℕ} {spec : List Entry} {minP : ℕ} (hs : SpecValid m spec minP) :
    let (n0, d0) := spec.foldl (fun (n, d) e =>
      if e.exact then (n * sigPP e.p e.minA, d * e.p ^ e.minA) else (n * e.p, d * (e.p - 1))) (1, 1)
    0 < d0 ∧
    (spec.map (fun e => sigPP e.p (m.factorization e.p))).prod * d0 ≤
    (spec.map (fun e => e.p ^ m.factorization e.p)).prod * n0 := by
  have hfold_gen : ∀ l : List Entry, (∀ e ∈ l, EntryValid m minP e) →
      ∀ n0 d0 A B : ℕ, 0 < d0 → A * d0 ≤ B * n0 →
      let res := l.foldl (fun (nd : ℕ × ℕ) e =>
        if e.exact then (nd.1 * sigPP e.p e.minA, nd.2 * e.p ^ e.minA)
        else (nd.1 * e.p, nd.2 * (e.p - 1))) (n0, d0)
      0 < res.2 ∧
      (A * (l.map (fun e => sigPP e.p (m.factorization e.p))).prod) * res.2 ≤
      (B * (l.map (fun e => e.p ^ m.factorization e.p)).prod) * res.1 := by
    intro l hl n0 d0 A B hd0 hAB
    induction l generalizing n0 d0 A B with
    | nil => simpa using ⟨hd0, hAB⟩
    | cons e es ih =>
      have he := hl e List.mem_cons_self
      simp only [List.foldl_cons, List.map_cons, List.prod_cons]
      split_ifs with hex
      · have hev : m.factorization e.p = e.minA := he.2.2.2.2.2.2.1 hex
        have hd0' : 0 < d0 * e.p ^ e.minA := Nat.mul_pos hd0 (Nat.pow_pos he.1.pos)
        have hAB' : (A * sigPP e.p (m.factorization e.p)) * (d0 * e.p ^ e.minA) ≤
                    (B * e.p ^ m.factorization e.p) * (n0 * sigPP e.p e.minA) := by
          rw [hev]
          calc (A * sigPP e.p e.minA) * (d0 * e.p ^ e.minA)
              = (A * d0) * (sigPP e.p e.minA * e.p ^ e.minA) := by ring
            _ ≤ (B * n0) * (e.p ^ e.minA * sigPP e.p e.minA) := Nat.mul_le_mul hAB (by rw [mul_comm])
            _ = (B * e.p ^ e.minA) * (n0 * sigPP e.p e.minA) := by ring
        simpa [mul_assoc] using ih (fun x hx => hl x (List.mem_cons_of_mem e hx))
          (n0 * sigPP e.p e.minA) (d0 * e.p ^ e.minA) _ _ hd0' hAB'
      · have hd0' : 0 < d0 * (e.p - 1) := Nat.mul_pos hd0 (Nat.sub_pos_of_lt he.1.one_lt)
        have hlt : sigPP e.p (m.factorization e.p) * (e.p - 1) ≤ e.p * e.p ^ m.factorization e.p :=
          (sigPP_lt_bound he.1.one_lt _).le
        have hAB' : (A * sigPP e.p (m.factorization e.p)) * (d0 * (e.p - 1)) ≤
                    (B * e.p ^ m.factorization e.p) * (n0 * e.p) := by
          calc (A * sigPP e.p (m.factorization e.p)) * (d0 * (e.p - 1))
              = (A * d0) * (sigPP e.p (m.factorization e.p) * (e.p - 1)) := by ring
            _ ≤ (B * n0) * (e.p * e.p ^ m.factorization e.p) := Nat.mul_le_mul hAB hlt
            _ = (B * e.p ^ m.factorization e.p) * (n0 * e.p) := by ring
        simpa [mul_assoc] using ih (fun x hx => hl x (List.mem_cons_of_mem e hx))
          (n0 * e.p) (d0 * (e.p - 1)) _ _ hd0' hAB'
  have h := hfold_gen spec hs.2.1 1 1 1 1 Nat.one_pos le_rfl
  simpa using h

lemma pairwise_lt_of_le_nodup {l : List ℕ} (hle : l.Pairwise (· ≤ ·)) (hnd : l.Nodup) :
    l.Pairwise (· < ·) := by
  induction l with
  | nil => exact List.Pairwise.nil
  | cons a t ih =>
    rw [List.pairwise_cons] at hle ⊢
    rw [List.nodup_cons] at hnd
    exact ⟨fun x hx => lt_of_le_of_ne (hle.1 x hx) (fun h => hnd.1 (h ▸ hx)), ih hle.2 hnd.2⟩

lemma maxAbSpec_sound {m : ℕ} (hm : m ≠ 0) (hm_card : m.primeFactors.card ≤ 5)
    {spec : List Entry} {minP rem n d : ℕ} (hs : SpecValid m spec minP)
    (_hspec_len : spec.length ≤ 5) (hrem : rem = 5 - spec.length)
    (hmax : maxAbSpec spec minP rem = (n, d)) (hd : 0 < d) :
    sigma 1 m * d ≤ m * n := by
  unfold maxAbSpec at hmax
  obtain ⟨hd0, hspec_le⟩ := maxAbSpec_spec_part hs
  set S_out := m.primeFactors \ (spec.map (·.p)).toFinset
  set qs := S_out.sort (· ≤ ·)
  have hpw : qs.Pairwise (· < ·) :=
    pairwise_lt_of_le_nodup (Finset.pairwise_sort S_out (· ≤ ·)) (Finset.sort_nodup S_out (· ≤ ·))
  have hlen : qs.length ≤ rem := by
    rw [Finset.length_sort, hrem]
    have hsub := spec_toFinset_subset hm hs
    have hcard : S_out.card = m.primeFactors.card - (spec.map (·.p)).toFinset.card := by
      dsimp only [S_out]
      rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hsub]
    rw [spec_toFinset_card hs] at hcard
    omega
  have hqp : ∀ r ∈ qs, r.Prime ∧ minP ≤ r := by
    intro r hr
    rw [Finset.mem_sort, Finset.mem_sdiff] at hr
    have hrp := Nat.prime_of_mem_primeFactors hr.1
    rcases hs.2.2 r hr.1 with ⟨e, he, rfl⟩ | hmin
    · exfalso; exact hr.2 (List.mem_toFinset.mpr (List.mem_map_of_mem he))
    · exact ⟨hrp, hmin⟩
  have hprod_qs_m : (qs.map (fun r => r ^ m.factorization r)).prod =
      ∏ q ∈ S_out, q ^ m.factorization q := by
    rw [← List.prod_toFinset _ (Finset.sort_nodup _ _), Finset.sort_toFinset]
  have hprod_qs_s : (qs.map (fun r => sigPP r (m.factorization r))).prod =
      ∏ q ∈ S_out, sigPP q (m.factorization q) := by
    rw [← List.prod_toFinset _ (Finset.sort_nodup _ _), Finset.sort_toFinset]
  have hsplit := prod_spec_factor_split hm hs
  have hbound := maxAbTail_spec m rem minP _ _ qs _ _ hd0 hspec_le hpw hlen hqp n d hmax hd
  rw [hprod_qs_m, hprod_qs_s] at hbound
  conv_lhs => rw [hsplit.2]
  conv_rhs => rw [hsplit.1]
  exact hbound

lemma maxAbSpec_zero_sound {m : ℕ} (_hm : m ≠ 0) {spec : List Entry} {minP n d : ℕ}
    (hs : SpecValid m spec minP) (hmax : maxAbSpec spec minP 0 = (n, d)) :
    0 < d ∧
    (spec.map (fun e => sigPP e.p (m.factorization e.p))).prod * d ≤
    (spec.map (fun e => e.p ^ m.factorization e.p)).prod * n := by
  unfold maxAbSpec at hmax
  simp only [maxAbTail] at hmax
  have h := maxAbSpec_spec_part hs
  rcases hL : spec.foldl (fun (nd : ℕ × ℕ) e =>
      if e.exact then (nd.1 * sigPP e.p e.minA, nd.2 * e.p ^ e.minA) else (nd.1 * e.p, nd.2 * (e.p - 1))) (1, 1) with ⟨n0, d0⟩
  change (let (n0, d0) := spec.foldl (fun (nd : ℕ × ℕ) e =>
      if e.exact then (nd.1 * sigPP e.p e.minA, nd.2 * e.p ^ e.minA) else (nd.1 * e.p, nd.2 * (e.p - 1))) (1, 1);
      (n0, d0) = (n, d)) at hmax
  change (let (n0, d0) := spec.foldl (fun (nd : ℕ × ℕ) e =>
      if e.exact then (nd.1 * sigPP e.p e.minA, nd.2 * e.p ^ e.minA) else (nd.1 * e.p, nd.2 * (e.p - 1))) (1, 1);
      0 < d0 ∧ (spec.map (fun e => sigPP e.p (m.factorization e.p))).prod * d0 ≤
      (spec.map (fun e => e.p ^ m.factorization e.p)).prod * n0) at h
  rw [hL] at hmax h
  injection hmax with hn hd
  subst hn; subst hd
  exact h

-- =====================================================================
-- prodWithCur & expandFree soundness
-- =====================================================================

lemma prodWithCur_mul (l : List Entry) (cur : List Nat) (x y b0 sb0 : ℕ) :
    prodWithCur l cur (x * b0) (y * sb0) =
    (x * (prodWithCur l cur b0 sb0).1, y * (prodWithCur l cur b0 sb0).2) := by
  induction l generalizing cur b0 sb0 with
  | nil => simp [prodWithCur]
  | cons e es ih =>
    simp only [prodWithCur]
    split_ifs with hex
    · rw [mul_assoc, mul_assoc, ih cur (b0 * e.p ^ e.minA) (sb0 * sigPP e.p e.minA)]
    · cases cur with
      | nil => simp
      | cons c cs => simp only [mul_assoc]; exact ih cs (b0 * e.p ^ c) (sb0 * sigPP e.p c)

inductive CurGe (m : ℕ) : List Entry → List Nat → Prop where
  | nil : CurGe m [] []
  | exact {e es cur} : e.exact = true → CurGe m es cur → CurGe m (e :: es) cur
  | free {e es c cur} : e.exact = false → c ≤ m.factorization e.p →
      CurGe m es cur → CurGe m (e :: es) (c :: cur)

lemma curGe_prodWithCur {m : ℕ} (_hm : m ≠ 0) {l : List Entry} {cur : List Nat}
    (hcg : CurGe m l cur) {minP : ℕ} (hpw : (l.map (·.p)).Pairwise (· < ·))
    (hev : ∀ e ∈ l, EntryValid m minP e) :
    let (b, sb) := prodWithCur l cur 1 1
    let B_l := (l.map (fun e => e.p ^ m.factorization e.p)).prod
    let SB_l := (l.map (fun e => sigPP e.p (m.factorization e.p))).prod
    0 < b ∧ b ∣ B_l ∧ sigma 1 b = sb ∧ sb * B_l ≤ SB_l * b ∧
    (∀ q ∈ b.primeFactors, ∃ e ∈ l, e.p = q) := by
  induction hcg with
  | nil =>
    simp [prodWithCur]
  | @exact e es cur hex hcg' ih =>
    rw [List.map_cons, List.pairwise_cons] at hpw
    have he := hev e List.mem_cons_self
    obtain ⟨hbpos, hbdvd, hbsig, hble, hbpf⟩ :=
      ih hpw.2 (fun x hx => hev x (List.mem_cons_of_mem e hx))
    set b_es := (prodWithCur es cur 1 1).1
    set sb_es := (prodWithCur es cur 1 1).2
    have hpow_eq : m.factorization e.p = e.minA := he.2.2.2.2.2.2.1 hex
    have hcop : Nat.Coprime (e.p ^ e.minA) b_es := by
      refine (he.1.coprime_iff_not_dvd.mpr fun hdvd => ?_).pow_left _
      have hmem : e.p ∈ b_es.primeFactors := Nat.mem_primeFactors.mpr ⟨he.1, hdvd, hbpos.ne'⟩
      obtain ⟨e', he', heq⟩ := hbpf e.p hmem
      have hlt := hpw.1 e'.p (List.mem_map_of_mem he')
      omega
    have hprod_eq : prodWithCur (e :: es) cur 1 1 = (e.p ^ e.minA * b_es, sigPP e.p e.minA * sb_es) := by
      simp only [prodWithCur, hex, ite_true, one_mul]
      simpa only [mul_one] using prodWithCur_mul es cur (e.p ^ e.minA) (sigPP e.p e.minA) 1 1
    rw [hprod_eq]
    refine ⟨Nat.mul_pos (Nat.pow_pos he.1.pos) hbpos, ?_, ?_, ?_, ?_⟩
    · simp only [List.map_cons, List.prod_cons, hpow_eq]
      exact mul_dvd_mul_left _ hbdvd
    · rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop,
          sigma_one_prime_pow he.1, hbsig]
    · simp only [List.map_cons, List.prod_cons, hpow_eq]
      calc (sigPP e.p e.minA * sb_es) * (e.p ^ e.minA * (es.map (fun x => x.p ^ m.factorization x.p)).prod)
          = (sigPP e.p e.minA * e.p ^ e.minA) * (sb_es * (es.map (fun x => x.p ^ m.factorization x.p)).prod) := by ring
        _ ≤ (sigPP e.p e.minA * e.p ^ e.minA) * ((es.map (fun x => sigPP x.p (m.factorization x.p))).prod * b_es) :=
            Nat.mul_le_mul_left _ hble
        _ = (sigPP e.p e.minA * (es.map (fun x => sigPP x.p (m.factorization x.p))).prod) * (e.p ^ e.minA * b_es) := by ring
    · intro q hq
      rw [Nat.primeFactors_mul (Nat.pow_pos he.1.pos).ne' hbpos.ne', Finset.mem_union] at hq
      rcases hq with hq1 | hq2
      · have hqp := Nat.prime_of_mem_primeFactors hq1
        have hqd := hqp.dvd_of_dvd_pow (Nat.dvd_of_mem_primeFactors hq1)
        exact ⟨e, List.mem_cons_self, (he.1.dvd_iff_eq hqp.ne_one).mp hqd⟩
      · obtain ⟨e', he', heq⟩ := hbpf q hq2
        exact ⟨e', List.mem_cons_of_mem e he', heq⟩
  | @free e es c cur hex hle hcg' ih =>
    rw [List.map_cons, List.pairwise_cons] at hpw
    have he := hev e List.mem_cons_self
    obtain ⟨hbpos, hbdvd, hbsig, hble, hbpf⟩ :=
      ih hpw.2 (fun x hx => hev x (List.mem_cons_of_mem e hx))
    set b_es := (prodWithCur es cur 1 1).1
    set sb_es := (prodWithCur es cur 1 1).2
    have hcop : Nat.Coprime (e.p ^ c) b_es := by
      refine (he.1.coprime_iff_not_dvd.mpr fun hdvd => ?_).pow_left _
      have hmem : e.p ∈ b_es.primeFactors := Nat.mem_primeFactors.mpr ⟨he.1, hdvd, hbpos.ne'⟩
      obtain ⟨e', he', heq⟩ := hbpf e.p hmem
      have hlt := hpw.1 e'.p (List.mem_map_of_mem he')
      omega
    have hprod_eq : prodWithCur (e :: es) (c :: cur) 1 1 = (e.p ^ c * b_es, sigPP e.p c * sb_es) := by
      simp only [prodWithCur, hex, Bool.false_eq_true, ↓reduceIte, one_mul]
      simpa only [mul_one] using prodWithCur_mul es cur (e.p ^ c) (sigPP e.p c) 1 1
    rw [hprod_eq]
    refine ⟨Nat.mul_pos (Nat.pow_pos he.1.pos) hbpos, ?_, ?_, ?_, ?_⟩
    · simp only [List.map_cons, List.prod_cons]
      exact mul_dvd_mul (Nat.pow_dvd_pow e.p hle) hbdvd
    · rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop,
          sigma_one_prime_pow he.1, hbsig]
    · simp only [List.map_cons, List.prod_cons]
      have hmono := sigPP_mono he.1.one_lt hle
      calc (sigPP e.p c * sb_es) * (e.p ^ m.factorization e.p * (es.map (fun x => x.p ^ m.factorization x.p)).prod)
          = (sigPP e.p c * e.p ^ m.factorization e.p) * (sb_es * (es.map (fun x => x.p ^ m.factorization x.p)).prod) := by ring
        _ ≤ (sigPP e.p (m.factorization e.p) * e.p ^ c) * ((es.map (fun x => sigPP x.p (m.factorization x.p))).prod * b_es) :=
            Nat.mul_le_mul hmono hble
        _ = (sigPP e.p (m.factorization e.p) * (es.map (fun x => sigPP x.p (m.factorization x.p))).prod) * (e.p ^ c * b_es) := by ring
    · intro q hq
      rw [Nat.primeFactors_mul (Nat.pow_pos he.1.pos).ne' hbpos.ne', Finset.mem_union] at hq
      rcases hq with hq1 | hq2
      · have hqp := Nat.prime_of_mem_primeFactors hq1
        have hqd := hqp.dvd_of_dvd_pow (Nat.dvd_of_mem_primeFactors hq1)
        exact ⟨e, List.mem_cons_self, (he.1.dvd_iff_eq hqp.ne_one).mp hqd⟩
      · obtain ⟨e', he', heq⟩ := hbpf q hq2
        exact ⟨e', List.mem_cons_of_mem e he', heq⟩

lemma entryValid_update {m minP : ℕ} {e : Entry} (ev : EntryValid m minP e)
    (a : ℕ) (ex : Bool) (h1 : 1 ≤ a) (hle : a ≤ m.factorization e.p)
    (hex : ex = true → m.factorization e.p = a)
    (hminpar : a % 2 = m.factorization e.p % 2) :
    EntryValid m minP { e with minA := a, exact := ex } :=
  ⟨ev.1, ev.2.1, ev.2.2.1, ev.2.2.2.1, h1, hle, hex, ev.2.2.2.2.2.2.2.1, hminpar⟩

lemma specValid_replace_mid {m minP : ℕ} {pref rest : List Entry} {e e' : Entry}
    (hs : SpecValid m (pref ++ e :: rest) minP) (hp : e'.p = e.p) (hev' : EntryValid m minP e') :
    SpecValid m (pref ++ e' :: rest) minP := by
  refine ⟨?_, ?_, ?_⟩
  · have hpw := hs.1
    rw [List.map_append, List.map_cons, hp] at *
    exact hpw
  · intro x hx
    rw [List.mem_append, List.mem_cons] at hx
    rcases hx with hx | rfl | hx
    · exact hs.2.1 x (List.mem_append_left _ hx)
    · exact hev'
    · exact hs.2.1 x (List.mem_append_right _ (List.mem_cons_of_mem e hx))
  · intro q hq
    rcases hs.2.2 q hq with ⟨x, hx, hxq⟩ | hmin
    · rw [List.mem_append, List.mem_cons] at hx
      rcases hx with hx | rfl | hx
      · left; exact ⟨x, List.mem_append_left _ hx, hxq⟩
      · left; exact ⟨e', List.mem_append_right _ List.mem_cons_self, hp.trans hxq⟩
      · left; exact ⟨x, List.mem_append_right _ (List.mem_cons_of_mem e' hx), hxq⟩
    · right; exact hmin

lemma expandStepA_sound {m minP : ℕ} (go : List Entry → Cert → Bool)
    (hgo : ∀ sp sub, go sp sub = true → SpecValid m sp minP → Goal m)
    (pref : List Entry) (e : Entry) (rest : List Entry) (c a : ℕ) (cs remCs : List Cert)
    (hs : SpecValid m (pref ++ e :: rest) minP) (_he_ex : e.exact = false)
    (ha_le : a ≤ m.factorization e.p) (ha_1 : 1 ≤ a)
    (ha_par : a % 2 = m.factorization e.p % 2)
    (hstep : expandStepA go pref e rest c a cs = (remCs, true)) :
    c ≤ m.factorization e.p ∨ Goal m := by
  induction cs generalizing a with
  | nil =>
    simp only [expandStepA] at hstep
    split_ifs at hstep with hac
    · left; omega
    · simp at hstep
  | cons sub more ih =>
    simp only [expandStepA] at hstep
    by_cases hac : a ≥ c
    · simp only [hac, ↓reduceIte] at hstep; left; omega
    · simp only [hac, ↓reduceIte] at hstep
      split_ifs at hstep with hsub
      · by_cases heq : m.factorization e.p = a
        · right
          have ev := hs.2.1 e (List.mem_append_right _ List.mem_cons_self)
          have ev' := entryValid_update ev a true ha_1 ha_le (fun _ => heq) ha_par
          exact hgo _ sub hsub (by simpa only [List.append_assoc, List.singleton_append] using specValid_replace_mid hs (e' := { e with minA := a, exact := true }) rfl ev')
        · have hle2 : a + 2 ≤ m.factorization e.p := by omega
          have hpar2 : (a + 2) % 2 = m.factorization e.p % 2 := by omega
          exact ih (a + 2) hle2 (by omega) hpar2 hstep
      · simp at hstep

lemma expandFree_sound {m minP : ℕ} (go : List Entry → Cert → Bool)
    (hgo : ∀ sp sub, go sp sub = true → SpecValid m sp minP → Goal m)
    (pref rest : List Entry) (cur : List Nat) (cs : List Cert)
    (hs : SpecValid m (pref ++ rest) minP)
    (hexp : expandFree go pref rest cur cs = true) :
    CurGe m rest cur ∨ Goal m := by
  induction rest generalizing pref cur cs with
  | nil =>
    simp only [expandFree, Bool.and_eq_true, List.isEmpty_iff] at hexp
    obtain ⟨hcur, _⟩ := hexp
    subst hcur
    left; exact CurGe.nil
  | cons e rest' ih =>
    unfold expandFree at hexp
    split_ifs at hexp with hex
    · have hs' : SpecValid m ((pref ++ [e]) ++ rest') minP := by
        simpa [List.append_assoc] using hs
      rcases ih (pref ++ [e]) cur cs hs' hexp with hcg | hg
      · left; exact CurGe.exact hex hcg
      · right; exact hg
    · cases cur with
      | nil => simp at hexp
      | cons c curRest =>
        dsimp only at hexp
        simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hexp
        obtain ⟨⟨hc_ge, hc_par⟩, hpair_ok⟩ := hexp
        rcases hpair : expandStepA go pref e rest' c e.minA cs with ⟨remCs, ok⟩
        rw [hpair] at hpair_ok
        simp only at hpair_ok
        obtain ⟨hok, hexp_rest⟩ := hpair_ok
        subst hok
        have hex_f : e.exact = false := Bool.eq_false_iff.mpr hex
        have ev := hs.2.1 e (List.mem_append_right _ List.mem_cons_self)
        rcases expandStepA_sound go hgo pref e rest' c e.minA cs remCs hs hex_f
            ev.2.2.2.2.2.1 ev.2.2.2.2.1 ev.2.2.2.2.2.2.2.2 hpair with hc_le | hg
        · have hc_par_m : c % 2 = m.factorization e.p % 2 := by
            obtain ⟨k, hk⟩ : ∃ k, c = e.minA + 2 * k := ⟨(c - e.minA) / 2, by omega⟩
            rw [hk, show (e.minA + 2 * k) % 2 = e.minA % 2 by omega]
            exact ev.2.2.2.2.2.2.2.2
          have ev' := entryValid_update ev c false (Nat.le_trans ev.2.2.2.2.1 hc_ge) hc_le (by simp) hc_par_m
          have hs' : SpecValid m ((pref ++ [{ e with minA := c, exact := false }]) ++ rest') minP := by
            simpa [List.append_assoc] using specValid_replace_mid hs (e' := { e with minA := c, exact := false }) rfl ev'
          rcases ih (pref ++ [{ e with minA := c, exact := false }]) curRest remCs hs' hexp_rest with hcg | hg
          · left; exact CurGe.free hex_f hc_le hcg
          · right; exact hg
        · right; exact hg

-- =====================================================================
-- Excess recurrence for prime power extension m = b * q ^ v
-- =====================================================================

lemma excess_rec_step (b q sb : ℕ) (hq : q.Prime) (k : ℕ) :
    ((sb * sigPP q (k + 1) : ℤ) - 2 * (b * q ^ (k + 1) : ℤ)) =
    (q : ℤ) * ((sb * sigPP q k : ℤ) - 2 * (b * q ^ k : ℤ)) + (sb : ℤ) := by
  have hsig : sigPP q (k + 1) = q * sigPP q k + 1 := by
    rw [sigPP_eq_geomSum q (k + 1) hq.one_lt, sigPP_eq_geomSum q k hq.one_lt,
        Finset.sum_range_succ']
    simp only [pow_zero, Finset.mul_sum]
    have : ∀ x ∈ range (k + 1), q * q ^ x = q ^ (x + 1) := fun x _ => by rw [← pow_succ']
    rw [Finset.sum_congr rfl this]
  rw [hsig, pow_succ]
  push_cast
  ring

lemma excess_closed_form (b q sb D : ℕ) (hq : q.Prime) (hD : sb + D = 2 * b) (t : ℕ) :
    ((q : ℤ) - 1) * ((sb * sigPP q t : ℤ) - 2 * (b * q ^ t : ℤ)) =
    (q : ℤ) ^ t * ((D : ℤ) + (sb : ℤ) - (q : ℤ) * (D : ℤ)) - (sb : ℤ) := by
  induction t with
  | zero =>
    have h0 : sigPP q 0 = 1 := by rw [sigPP_eq_geomSum q 0 hq.one_lt]; simp
    rw [h0]; simp
    have hsub : (sb : ℤ) - 2 * (b : ℤ) = -(D : ℤ) := by
      have hDz : (sb : ℤ) + (D : ℤ) = 2 * (b : ℤ) := by exact_mod_cast hD
      linarith
    rw [hsub]; ring
  | succ t ih =>
    rw [excess_rec_step b q sb hq t, pow_succ']
    calc ((q : ℤ) - 1) * ((q : ℤ) * ((sb * sigPP q t : ℤ) - 2 * (b * q ^ t : ℤ)) + (sb : ℤ))
        = (q : ℤ) * (((q : ℤ) - 1) * ((sb * sigPP q t : ℤ) - 2 * (b * q ^ t : ℤ))) + ((q : ℤ) - 1) * (sb : ℤ) := by ring
      _ = (q : ℤ) * ((q : ℤ) ^ t * ((D : ℤ) + (sb : ℤ) - (q : ℤ) * (D : ℤ)) - (sb : ℤ)) + ((q : ℤ) - 1) * (sb : ℤ) := by rw [ih]
      _ = _ := by ring

lemma rem1_structure {m : ℕ} (hm_odd : Odd m) (_hm_ab : m.Abundant)
    (hm_card : m.primeFactors.card ≤ 5) {spec : List Entry} {minP minQ : ℕ}
    (hs : SpecValid m spec minP) (hlen : 5 - spec.length = 1)
    (hnp : nextPrime minP = some minQ) :
    let b := (spec.map (fun e => e.p ^ m.factorization e.p)).prod
    let sb := (spec.map (fun e => sigPP e.p (m.factorization e.p))).prod
    (b = m ∧ sigma 1 m = sb) ∨
    (∃ q v, q.Prime ∧ minQ ≤ q ∧ ¬ (∃ e ∈ spec, e.p = q) ∧ b.Coprime q ∧ 1 ≤ v ∧
      m = b * q ^ v ∧ sigma 1 m = sb * sigPP q v ∧ 0 < b ∧ sigma 1 b = sb) := by
  have hm0 : m ≠ 0 := hm_odd.pos.ne'
  set S := (spec.map (·.p)).toFinset
  have hsub := spec_toFinset_subset hm0 hs
  have hcard_S : S.card = spec.length := spec_toFinset_card hs
  have hcard_sdiff : (m.primeFactors \ S).card = m.primeFactors.card - S.card := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hsub]
  have hcard_le1 : (m.primeFactors \ S).card ≤ 1 := by omega
  have hsplit := prod_spec_factor_split hm0 hs
  set b := (spec.map (fun e => e.p ^ m.factorization e.p)).prod
  set sb := (spec.map (fun e => sigPP e.p (m.factorization e.p))).prod
  have hb_prop := prod_spec_dvd_and_sigma hm0 hs (fun e => m.factorization e.p) (fun _ _ => le_rfl)
  by_cases hempty : m.primeFactors \ S = ∅
  · left
    dsimp only [S] at hempty
    simp only [hempty, Finset.prod_empty, mul_one] at hsplit
    exact ⟨hsplit.1.symm, hsplit.2⟩
  · right
    have hcard_pos : 0 < (m.primeFactors \ S).card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hempty)
    have hcard_eq1 : (m.primeFactors \ S).card = 1 := by omega
    obtain ⟨q, hq_sing⟩ := Finset.card_eq_one.mp hcard_eq1
    have hq_mem : q ∈ m.primeFactors \ S := hq_sing ▸ Finset.mem_singleton_self q
    rw [Finset.mem_sdiff] at hq_mem
    have hqp := Nat.prime_of_mem_primeFactors hq_mem.1
    have hq_not_spec : ¬ (∃ e ∈ spec, e.p = q) := fun ⟨e, he, heq⟩ =>
      hq_mem.2 (List.mem_toFinset.mpr (List.mem_map.mpr ⟨e, he, heq⟩))
    have hq_ge_minP : minP ≤ q := (hs.2.2 q hq_mem.1).resolve_left hq_not_spec
    obtain ⟨hminPQ, hminQp, hminQ_lt⟩ := nextPrime_spec hnp
    have hq_ge_minQ : minQ ≤ q := by
      by_contra hlt
      exact hminQ_lt q hq_ge_minP (Nat.lt_of_not_le hlt) hqp
    have hq_cop : b.Coprime q := by
      refine hqp.coprime_iff_not_dvd.mpr (fun hdvd => ?_) |>.symm
      have hdvd_spec : ∀ l : List Entry, (∀ e ∈ l, EntryValid m minP e) →
          q ∣ (l.map (fun e => e.p ^ m.factorization e.p)).prod → ∃ e ∈ l, e.p = q := by
        intro l hl hd
        induction l with
        | nil => simp at hd; exact absurd hd hqp.ne_one
        | cons e es ih =>
          simp only [List.map_cons, List.prod_cons] at hd
          rcases hqp.dvd_mul.mp hd with h1 | h2
          · have hqd : q ∣ e.p := hqp.dvd_of_dvd_pow h1
            have hep := (hl e List.mem_cons_self).1
            exact ⟨e, List.mem_cons_self, (hep.dvd_iff_eq hqp.ne_one).mp hqd⟩
          · obtain ⟨e', he', heq⟩ := ih (fun x hx => hl x (List.mem_cons_of_mem e hx)) h2
            exact ⟨e', List.mem_cons_of_mem e he', heq⟩
      exact hq_not_spec (hdvd_spec spec hs.2.1 hdvd)
    have hv : 1 ≤ m.factorization q := hqp.factorization_pos_of_dvd hm0 (Nat.dvd_of_mem_primeFactors hq_mem.1)
    dsimp only [S] at hq_sing
    simp only [hq_sing, Finset.prod_singleton] at hsplit
    exact ⟨q, m.factorization q, hqp, hq_ge_minQ, hq_not_spec, hq_cop, hv, hsplit.1, hsplit.2, hb_prop.1, hb_prop.2.2⟩

-- =====================================================================
-- checkRem1TailWit, stepNF1, checkRem1NF0, checkR2 soundness
-- =====================================================================

lemma checkE1Loop_sound : ∀ ds lo q, checkE1Loop lo ds = true →
    lo ≤ q → q < lo + ds.length → ¬ q.Prime := by
  intro ds
  induction ds with
  | nil => intro lo q _ h1 h2; simp at h2; omega
  | cons d ds ih =>
    intro lo q hchk h1 h2
    simp only [checkE1Loop, Bool.and_eq_true] at hchk
    simp only [List.length_cons] at h2
    by_cases heq : q = lo
    · subst heq; exact checkFactor_not_prime hchk.1
    · exact ih (lo + 1) q hchk.2 (by omega) (by omega)

lemma checkE2Loop_sound (loNum loDen hiNum hiDen dLbNum dLbDen : ℕ) :
    ∀ ds lo q, checkE2Loop loNum loDen hiNum hiDen dLbNum dLbDen lo ds = true →
    lo ≤ q → q < lo + ds.length → q.Prime →
    ∃ eMin, 2 ≤ eMin ∧ loNum + loDen > q * loDen ∧
      (eMin = 2 ∨ q ^ (eMin - 1) * (hiNum + hiDen - q * hiDen) * loDen ≤ hiDen * loNum) ∧
      q ^ eMin * (loNum + loDen - q * loDen) * hiDen > hiNum * loDen ∧
      dLbNum * (q ^ eMin * (loNum + loDen - q * loDen) * hiDen - hiNum * loDen) ≥
        64 * (q - 1) * dLbDen * loDen * hiDen := by
  intro ds
  induction ds with
  | nil => intro lo q _ h1 h2; simp at h2; omega
  | cons c ds ih =>
    intro lo q hchk h1 h2 hqp
    simp only [checkE2Loop, Bool.and_eq_true] at hchk
    simp only [List.length_cons] at h2
    by_cases heq : q = lo
    · subst heq
      have hok := hchk.1
      by_cases hc0 : (c % 2 == 0) = true
      · rw [if_pos hc0] at hok; exfalso; exact checkFactor_not_prime hok hqp
      · rw [if_neg hc0] at hok
        by_cases hbad : (loNum + loDen ≤ q * loDen || c / 2 < 2) = true
        · rw [if_pos hbad] at hok; exact Bool.noConfusion hok
        · rw [if_neg hbad] at hok
          simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, not_le, not_lt] at hbad
          simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at hok
          exact ⟨c / 2, hbad.2, hbad.1, hok.1.1, hok.1.2, hok.2⟩
    · exact ih (lo + 1) q hchk.2 (by omega) (by omega) hqp

lemma checkRem1TailWit_sound {m : ℕ} (hm_odd : Odd m) (hm_ab : m.Abundant)
    (hm_card : m.primeFactors.card ≤ 5) (hm_prim : ∀ d ∈ m.properDivisors, d.Deficient)
    (hE_lt : sigma 1 m - 2 * m < 64)
    {spec : List Entry} {minP minQ LNum LDen : ℕ} (hs : SpecValid m spec minP)
    (hlen : 5 - spec.length = 1) (hnp : nextPrime minP = some minQ)
    (hL : maxAbSpec spec minP 0 = (LNum, LDen)) (hLD : 0 < LDen) (hL_lt : LNum < 2 * LDen)
    {cur : List Nat} (hcg : CurGe m spec cur)
    {e1W : List Nat} {e2W : List Nat}
    (hwit : checkRem1TailWit spec cur LNum LDen minQ e1W e2W = true) : False := by
  have hm0 : m ≠ 0 := hm_odd.pos.ne'
  have h2m_lt : 2 * m < sigma 1 m := (abundant_iff_two_mul_lt_sigma m).mp hm_ab
  have hcur_all := curGe_prodWithCur hm0 hcg hs.1 hs.2.1
  set bMin := (prodWithCur spec cur 1 1).1
  set sbMin := (prodWithCur spec cur 1 1).2
  obtain ⟨hbMin_pos, hbMin_dvd_B, hsbMin_sig, hcur_le, _⟩ := hcur_all
  unfold checkRem1TailWit at hwit
  dsimp only at hwit
  by_cases hbad : (2 * bMin ≤ sbMin || 2 * LDen ≤ LNum) = true
  · rw [if_pos hbad] at hwit; exact Bool.noConfusion hwit
  rw [if_neg hbad] at hwit
  simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, not_le] at hbad
  have hDMin_pos : 0 < 2 * bMin - sbMin := by omega
  have hsbMin_lt : sbMin < 2 * bMin := hbad.1
  have hmax0 := (maxAbSpec_zero_sound hm0 hs hL).2
  rcases rem1_structure hm_odd hm_ab hm_card hs hlen hnp with ⟨hbm, hsm⟩ |
      ⟨q, v, hqp, hq_ge, _, hq_cop, hv1, hm_eq, hsig_eq, hb_pos, hb_sig⟩
  · -- m = b, so sigma 1 m * LDen <= m * LNum < 2 * m * LDen, contradicting h2m_lt
    rw [← hsm] at hmax0
    rw [hbm] at hmax0
    nlinarith only [hmax0, h2m_lt, hLD, hL_lt]
  · -- m = b * q ^ v with 1 ≤ v
    set b := (spec.map (fun e => e.p ^ m.factorization e.p)).prod
    set sb := (spec.map (fun e => sigPP e.p (m.factorization e.p))).prod
    have hb_proper : b ∈ m.properDivisors := by
      refine Nat.mem_properDivisors.mpr ⟨⟨q ^ v, hm_eq⟩, ?_⟩
      have hqv1 : 1 < q ^ v := one_lt_pow₀ hqp.one_lt (by omega)
      calc b = b * 1 := (mul_one b).symm
        _ < b * q ^ v := Nat.mul_lt_mul_of_pos_left hqv1 hb_pos
        _ = m := hm_eq.symm
    have hb_def : sb < 2 * b := by
      rw [← hb_sig, ← deficient_iff_sigma_lt_two_mul]
      exact hm_prim b hb_proper
    set D := 2 * b - sb
    have hD_pos : 0 < D := by omega
    have hD_eq : sb + D = 2 * b := by omega
    have hbMin_le_b : bMin ≤ b := Nat.le_of_dvd hb_pos hbMin_dvd_B
    set DMin := 2 * bMin - sbMin
    set loNum := sbMin; set loDen := DMin
    set hiNum := LNum; set hiDen := 2 * LDen - LNum
    set dLbNum := (2 * LDen - LNum) * bMin; set dLbDen := LDen
    have hlo_ineq : loNum * D ≤ sb * loDen := by
      dsimp only [loNum, loDen, D, DMin]
      have h1 : (sbMin : ℤ) * b ≤ sb * bMin := by exact_mod_cast hcur_le
      have hs1 : ((2 * b - sb : ℕ) : ℤ) = 2 * b - sb := Int.ofNat_sub hb_def.le
      have hs2 : ((2 * bMin - sbMin : ℕ) : ℤ) = 2 * bMin - sbMin := Int.ofNat_sub hsbMin_lt.le
      zify; rw [hs1, hs2]; nlinarith only [h1]
    have hhi_ineq : sb * hiDen ≤ hiNum * D := by
      dsimp only [hiNum, hiDen, D]
      have h1 : (sb : ℤ) * LDen ≤ b * LNum := by exact_mod_cast hmax0
      have hs1 : ((2 * LDen - LNum : ℕ) : ℤ) = 2 * LDen - LNum := Int.ofNat_sub hL_lt.le
      have hs2 : ((2 * b - sb : ℕ) : ℤ) = 2 * b - sb := Int.ofNat_sub hb_def.le
      zify; rw [hs1, hs2]; nlinarith only [h1]
    have hdLb_ineq : dLbNum ≤ D * dLbDen := by
      dsimp only [dLbNum, dLbDen, D]
      have h1 : (2 * LDen - LNum) * bMin ≤ (2 * LDen - LNum) * b := Nat.mul_le_mul_left _ hbMin_le_b
      have h2 : (2 * LDen - LNum) * b ≤ (2 * b - sb) * LDen := by
        have h3 : (sb : ℤ) * LDen ≤ b * LNum := by exact_mod_cast hmax0
        have hs1 : ((2 * LDen - LNum : ℕ) : ℤ) = 2 * LDen - LNum := Int.ofNat_sub hL_lt.le
        have hs2 : ((2 * b - sb : ℕ) : ℤ) = 2 * b - sb := Int.ofNat_sub hb_def.le
        zify; rw [hs1, hs2]; nlinarith only [h3]
      exact h1.trans h2
    -- Split e1Ok vs e2Ok from hwit
    set lhsE1 := loNum * dLbNum; set subE1 := 63 * loDen * dLbDen; set denE1 := loDen * dLbNum
    set qE1Lo := if lhsE1 > subE1 then (lhsE1 - subE1 + denE1 - 1) / denE1 else 0
    set qE1Hi := (hiNum - 1) / hiDen
    set lo1 := max minQ qE1Lo
    have he1_ok : (if qE1Hi < lo1 then e1W.isEmpty else e1W.length == qE1Hi + 1 - lo1 && checkE1Loop lo1 e1W) = true := by
      by_contra hf
      have hf' : (if qE1Hi < lo1 then e1W.isEmpty else e1W.length == qE1Hi + 1 - lo1 && checkE1Loop lo1 e1W) = false :=
        Bool.eq_false_iff.mpr hf
      simp only [hf', Bool.not_false, ↓reduceIte] at hwit
      -- Wait: if e1Ok is false, hwit is false!
      exact Bool.noConfusion hwit
    have he2_ok : (if 1 + (hiNum - 1) / hiDen < max minQ (loNum / loDen + 1) then e2W.isEmpty
        else e2W.length == 1 + (hiNum - 1) / hiDen + 1 - max minQ (loNum / loDen + 1) &&
          checkE2Loop loNum loDen hiNum hiDen dLbNum dLbDen (max minQ (loNum / loDen + 1)) e2W) = true := by
      rw [if_neg (by simp [he1_ok])] at hwit
      exact hwit
    by_cases hv_eq1 : v = 1
    · subst hv_eq1
      have hsig1 : sigPP q 1 = q + 1 := by rw [sigPP_eq_geomSum q 1 hqp.one_lt]; simp [Finset.sum_range_succ]; omega
      rw [pow_one] at hm_eq
      rw [hsig1] at hsig_eq
      have hE_eq : sigma 1 m - 2 * m = sb - D * q := by
        conv_lhs => rw [hsig_eq, hm_eq]
        zify [show 2 * (b * q) ≤ sb * (q + 1) by rw [← hm_eq, ← hsig_eq]; exact h2m_lt.le,
              show D * q ≤ sb by
                have : (D : ℤ) * q ≤ sb := by
                  have hDz : (sb : ℤ) + D = 2 * b := by exact_mod_cast hD_eq
                  have hm2 : (2 : ℤ) * (b * q) < sb * (q + 1) := by exact_mod_cast (by rw [← hm_eq, ← hsig_eq]; exact h2m_lt)
                  nlinarith only [hDz, hm2]
                exact_mod_cast this]
        have : (sb : ℤ) + D = 2 * b := by exact_mod_cast hD_eq
        nlinarith only [this]
      have hE_1 : 1 ≤ sb - D * q := by omega
      have hE_63 : sb - D * q ≤ 63 := by omega
      have hq_hi : q ≤ qE1Hi := by
        have hhi_pos : 0 < hiDen := by omega
        have h1 : D * q + 1 ≤ sb := by omega
        have h2 : (D * q + 1) * hiDen ≤ hiNum * D := (Nat.mul_le_mul_right hiDen h1).trans hhi_ineq
        have h3 : q * hiDen < hiNum := by nlinarith only [h2, hD_pos, hhi_pos]
        have h4 : q * hiDen ≤ hiNum - 1 := by omega
        exact (Nat.le_div_iff_mul_le hhi_pos).mpr h4
      have hq_lo : qE1Lo ≤ q := by
        dsimp only [qE1Lo]
        split_ifs with hsub
        · have hden_pos : 0 < denE1 := Nat.mul_pos hDMin_pos (Nat.mul_pos (by omega) hbMin_pos)
          rw [Nat.div_le_iff_le_mul_add_pred hden_pos]
          have h1 : sb ≤ D * q + 63 := by omega
          have h2 : loNum * D ≤ (D * q + 63) * loDen := hlo_ineq.trans (Nat.mul_le_mul_right loDen h1)
          have h3 : loNum * dLbNum ≤ loNum * (D * dLbDen) := Nat.mul_le_mul_left loNum hdLb_ineq
          have h4 : lhsE1 ≤ denE1 * q + subE1 := by
            dsimp only [lhsE1, denE1, subE1, dLbNum, dLbDen] at h3 ⊢
            have h2' : loNum * D * ((2 * LDen - LNum) * bMin) ≤ (D * q + 63) * loDen * ((2 * LDen - LNum) * bMin) :=
              Nat.mul_le_mul_right _ h2
            have hdLb_le' : (2 * LDen - LNum) * bMin ≤ D * LDen := hdLb_ineq
            nlinarith only [h2', h3, hdLb_le', hD_pos]
          have hsub_le : ∀ x y z w : ℕ, y < x → 0 < z → x ≤ w + y → x - y + z - 1 ≤ w + (z - 1) := fun _ _ _ _ _ _ _ => by omega
          exact hsub_le lhsE1 subE1 denE1 (denE1 * q) hsub hden_pos h4
        · exact Nat.zero_le q
      have hlo1 : lo1 ≤ q := max_le hq_ge hq_lo
      have hnot_lt : ¬ qE1Hi < lo1 := by omega
      rw [if_neg hnot_lt, Bool.and_eq_true, beq_iff_eq] at he1_ok
      exact checkE1Loop_sound e1W lo1 q he1_ok.2 hlo1 (by omega) hqp
    · -- 2 ≤ v
      have hv2 : 2 ≤ v := by omega
      have hbq_proper : b * q ∈ m.properDivisors := by
        refine Nat.mem_properDivisors.mpr ⟨⟨q ^ (v - 1), by rw [hm_eq, mul_assoc, ← pow_succ', Nat.sub_add_cancel (by omega)]⟩, ?_⟩
        have hqv1 : q < q ^ v := lt_self_pow₀ hqp.one_lt (by omega)
        calc b * q < b * q ^ v := Nat.mul_lt_mul_of_pos_left hqv1 hb_pos
          _ = m := hm_eq.symm
      have hbq_def : sigma 1 (b * q) < 2 * (b * q) := (deficient_iff_sigma_lt_two_mul _).mp (hm_prim _ hbq_proper)
      have hq_sig1 : sigma 1 q = q + 1 := by
        simpa [pow_one] using (sigma_one_prime_pow hqp 1).trans
          (by rw [sigPP_eq_geomSum q 1 hqp.one_lt]; simp [Finset.sum_range_succ]; omega)
      have hbq_sig : sigma 1 (b * q) = sb * (q + 1) := by
        rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hq_cop, hb_sig, hq_sig1]
      rw [hbq_sig] at hbq_def
      have hE1_neg : (sb : ℤ) - (D : ℤ) * q < 0 := by
        have h1 : (sb : ℤ) * (q + 1) < 2 * (b * q) := by exact_mod_cast hbq_def
        have h2 : (sb : ℤ) + D = 2 * b := by exact_mod_cast hD_eq
        nlinarith only [h1, h2]
      have hcf_v := excess_closed_form b q sb D hqp hD_eq v
      have hEv_pos : 0 < (sb * sigPP q v : ℤ) - 2 * (b * q ^ v : ℤ) := by
        have hm_z : (b : ℤ) * (q : ℤ) ^ v = m := by exact_mod_cast hm_eq.symm
        have hs_z : (sb : ℤ) * sigPP q v = sigma 1 m := by exact_mod_cast hsig_eq.symm
        rw [hm_z, hs_z]
        have hm2z : (2 * m : ℤ) < sigma 1 m := by exact_mod_cast h2m_lt
        omega
      have hq_pos_sub : (0 : ℤ) < (q : ℤ) - 1 := by have := hqp.one_lt; omega
      have hgap_pos : (0 : ℤ) < (D : ℤ) + (sb : ℤ) - (q : ℤ) * (D : ℤ) := by
        by_contra hle
        have hle' : (D : ℤ) + sb - q * D ≤ 0 := by omega
        have h1 := mul_nonpos_of_nonneg_of_nonpos (pow_nonneg (Nat.cast_nonneg q) v) hle'
        have h2 := mul_pos hq_pos_sub hEv_pos
        linarith only [h1, h2, hcf_v]
      have hq_lo2 : loNum / loDen + 1 ≤ q := by
        have : loNum < q * loDen := by
          have hloz : (loNum : ℤ) * D ≤ sb * loDen := by exact_mod_cast hlo_ineq
          have hDz : (sb : ℤ) + D = 2 * b := by exact_mod_cast hD_eq
          have hbq : (sb : ℤ) * (q + 1) < 2 * (b * q) := by exact_mod_cast hbq_def
          have hqD : (sb : ℤ) < D * q := by nlinarith only [hDz, hbq]
          have hDz_pos : (0 : ℤ) < D := by exact_mod_cast hD_pos
          have hlo_zpos : (0 : ℤ) < loDen := by exact_mod_cast hDMin_pos
          zify
          nlinarith only [hloz, hqD, hDz_pos, hlo_zpos]
        exact Nat.div_lt_of_lt_mul (by rw [mul_comm]; exact this)
      have hq_hi2 : q ≤ 1 + (hiNum - 1) / hiDen := by
        have hhi_pos : 0 < hiDen := by omega
        have h1 : ((q : ℤ) - 1) * D < sb := by linarith only [hgap_pos]
        have hhiz : (sb : ℤ) * hiDen ≤ hiNum * D := by exact_mod_cast hhi_ineq
        have hDz_pos : (0 : ℤ) < D := by exact_mod_cast hD_pos
        have hhi_zpos : (0 : ℤ) < hiDen := by exact_mod_cast hhi_pos
        have h2 : (q - 1) * hiDen < hiNum := by
          zify [hqp.one_lt.le]; nlinarith only [h1, hhiz, hDz_pos, hhi_zpos]
        have h3 : (q - 1) * hiDen ≤ hiNum - 1 := Nat.le_sub_one_of_lt h2
        have h4 : q - 1 ≤ (hiNum - 1) / hiDen := (Nat.le_div_iff_mul_le hhi_pos).mpr h3
        omega
      set lo2 := max minQ (loNum / loDen + 1)
      set hi2 := 1 + (hiNum - 1) / hiDen
      have hlo2 : lo2 ≤ q := max_le hq_ge hq_lo2
      have hnot_lt2 : ¬ hi2 < lo2 := by omega
      rw [if_neg hnot_lt2, Bool.and_eq_true, beq_iff_eq] at he2_ok
      obtain ⟨eMin, heMin2, hgap_lo_pos, heMin_prev, hqe_pos, h64_bound⟩ :=
        checkE2Loop_sound loNum loDen hiNum hiDen dLbNum dLbDen e2W lo2 q he2_ok.2 hlo2 (by omega) hqp
      have heMin_le_v : eMin ≤ v := by
        by_cases he2 : eMin = 2
        · omega
        · have hprev_ineq := heMin_prev.resolve_left he2
          by_contra hlt
          have hv_le : v ≤ eMin - 1 := by omega
          have hcf_prev := excess_closed_form b q sb D hqp hD_eq (eMin - 1)
          have hpow_le : (q : ℤ) ^ v ≤ (q : ℤ) ^ (eMin - 1) := by
            exact_mod_cast Nat.pow_le_pow_right hqp.pos hv_le
          have h_le_prev : ((q : ℤ) - 1) * ((sb * sigPP q v : ℤ) - 2 * (b * q ^ v : ℤ)) ≤
              ((q : ℤ) - 1) * ((sb * sigPP q (eMin - 1) : ℤ) - 2 * (b * q ^ (eMin - 1) : ℤ)) := by
            rw [hcf_v, hcf_prev]
            nlinarith only [hpow_le, hgap_pos]
          have hprev_nonpos : ((q : ℤ) - 1) * ((sb * sigPP q (eMin - 1) : ℤ) - 2 * (b * q ^ (eMin - 1) : ℤ)) ≤ 0 := by
            have hhi_pos : (0 : ℤ) < hiDen := by exact_mod_cast (by omega : 0 < hiDen)
            have hlo_pos : (0 : ℤ) < loDen := by exact_mod_cast hDMin_pos
            have hqhi_le : q * hiDen ≤ hiNum + hiDen := by
              have h2 : ((q : ℤ) - 1) * D < sb := by linarith only [hgap_pos]
              have h3 : (sb : ℤ) * hiDen ≤ hiNum * D := by exact_mod_cast hhi_ineq
              have h4 : (0 : ℤ) < D := by exact_mod_cast hD_pos
              have h5 : ((q : ℤ) - 1) * hiDen < hiNum := by nlinarith only [h2, h3, h4, hhi_pos]
              zify; linarith only [h5]
            have hgap_hi_le : ((D : ℤ) + sb - q * D) * hiDen ≤ D * ((hiNum : ℤ) + hiDen - q * hiDen) := by
              have h3 : (sb : ℤ) * hiDen ≤ hiNum * D := by exact_mod_cast hhi_ineq
              linarith only [h3]
            have h1 : (D : ℤ) * loNum ≤ sb * loDen := by
              rw [mul_comm (D : ℤ) loNum]; exact_mod_cast hlo_ineq
            have h2 : (q : ℤ) ^ (eMin - 1) * ((hiNum : ℤ) + hiDen - q * hiDen) * loDen ≤ hiDen * loNum := by
              have hprev_z : ((q ^ (eMin - 1) * (hiNum + hiDen - q * hiDen) * loDen : ℕ) : ℤ) ≤ ((hiDen * loNum : ℕ) : ℤ) := by
                exact_mod_cast hprev_ineq
              push_cast [hqhi_le] at hprev_z
              exact hprev_z
            rw [hcf_prev]
            have hpow_nn : (0 : ℤ) ≤ (q : ℤ) ^ (eMin - 1) := pow_nonneg (Nat.cast_nonneg q) (eMin - 1)
            have hstep1 : (q : ℤ) ^ (eMin - 1) * ((D : ℤ) + sb - q * D) * (hiDen * loDen) ≤
                D * ((q : ℤ) ^ (eMin - 1) * ((hiNum : ℤ) + hiDen - q * hiDen) * loDen) := by
              have := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hgap_hi_le hlo_pos.le) hpow_nn
              linarith only [this]
            have hstep2 : D * ((q : ℤ) ^ (eMin - 1) * ((hiNum : ℤ) + hiDen - q * hiDen) * loDen) ≤ D * (hiDen * loNum) :=
              mul_le_mul_of_nonneg_left h2 (by exact_mod_cast hD_pos.le)
            have hstep3 : (hiDen : ℤ) * (D * loNum) ≤ hiDen * (sb * loDen) :=
              mul_le_mul_of_nonneg_left h1 hhi_pos.le
            have hcomb : ((q : ℤ) ^ (eMin - 1) * ((D : ℤ) + sb - q * D) - sb) * (hiDen * loDen) ≤ 0 := by
              linarith only [hstep1, hstep2, hstep3]
            nlinarith only [hcomb, mul_pos hhi_pos hlo_pos]
          nlinarith only [hq_pos_sub, hEv_pos, h_le_prev, hprev_nonpos]
      -- Now at eMin ≤ v, E(eMin) ≥ 64!
      have hE_eMin_ge : (64 : ℤ) ≤ (sb * sigPP q eMin : ℤ) - 2 * (b * q ^ eMin : ℤ) := by
        have hcf_e := excess_closed_form b q sb D hqp hD_eq eMin
        have hlo_pos : (0 : ℤ) < loDen := by exact_mod_cast hDMin_pos
        have hhi_pos : (0 : ℤ) < hiDen := by exact_mod_cast (by omega : 0 < hiDen)
        have hdLb_pos : (0 : ℤ) < dLbDen := by exact_mod_cast hLD
        have hdLb_z : (dLbNum : ℤ) ≤ D * dLbDen := by exact_mod_cast hdLb_ineq
        have h1_le : q * loDen ≤ loNum + loDen := hgap_lo_pos.le
        have h2_le : hiNum * loDen ≤ q ^ eMin * (loNum + loDen - q * loDen) * hiDen := hqe_pos.le
        have h64_z : (64 : ℤ) * (q - 1) * dLbDen * loDen * hiDen ≤
            dLbNum * ((q : ℤ) ^ eMin * (loNum + loDen - q * loDen) * hiDen - hiNum * loDen) := by
          have h3 : ((64 * (q - 1) * dLbDen * loDen * hiDen : ℕ) : ℤ) ≤
              ((dLbNum * (q ^ eMin * (loNum + loDen - q * loDen) * hiDen - hiNum * loDen) : ℕ) : ℤ) := by
            exact_mod_cast h64_bound
          push_cast [hqp.one_lt.le, h1_le, h2_le] at h3
          exact h3
        have hsub_nonneg : 0 ≤ (q : ℤ) ^ eMin * (loNum + loDen - q * loDen) * hiDen - hiNum * loDen := by
          have h2z : ((hiNum * loDen : ℕ) : ℤ) ≤ ((q ^ eMin * (loNum + loDen - q * loDen) * hiDen : ℕ) : ℤ) := by
            exact_mod_cast h2_le
          push_cast [h1_le] at h2z
          linarith only [h2z]
        have h64_D : (64 : ℤ) * (q - 1) * dLbDen * loDen * hiDen ≤
            D * dLbDen * ((q : ℤ) ^ eMin * (loNum + loDen - q * loDen) * hiDen - hiNum * loDen) := by
          calc (64 : ℤ) * (q - 1) * dLbDen * loDen * hiDen
              ≤ dLbNum * ((q : ℤ) ^ eMin * (loNum + loDen - q * loDen) * hiDen - hiNum * loDen) := h64_z
            _ ≤ (D * dLbDen) * ((q : ℤ) ^ eMin * (loNum + loDen - q * loDen) * hiDen - hiNum * loDen) :=
                mul_le_mul_of_nonneg_right hdLb_z hsub_nonneg
        have h_rhs : D * ((q : ℤ) ^ eMin * (loNum + loDen - q * loDen) * hiDen - hiNum * loDen) ≤
            loDen * hiDen * (((q : ℤ) - 1) * ((sb * sigPP q eMin : ℤ) - 2 * (b * q ^ eMin : ℤ))) := by
          rw [hcf_e]
          have hpow_nn : (0 : ℤ) ≤ (q : ℤ) ^ eMin := pow_nonneg (Nat.cast_nonneg q) eMin
          have hloz : (D : ℤ) * loNum ≤ sb * loDen := by
            rw [mul_comm (D : ℤ) loNum]; exact_mod_cast hlo_ineq
          have hhiz : (sb : ℤ) * hiDen ≤ hiNum * D := by exact_mod_cast hhi_ineq
          have ha : (D : ℤ) * (loNum + loDen - q * loDen) ≤ loDen * (D + sb - q * D) := by linarith only [hloz]
          have hb : (loDen : ℤ) * hiDen * sb ≤ D * hiNum * loDen := by nlinarith only [hhiz, hlo_pos]
          have hc := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ha hpow_nn) hhi_pos.le
          linarith only [hb, hc]
        have hpos_all : 0 < dLbDen * loDen * hiDen * ((q : ℤ) - 1) :=
          mul_pos (mul_pos (mul_pos hdLb_pos hlo_pos) hhi_pos) hq_pos_sub
        nlinarith only [h64_D, mul_le_mul_of_nonneg_left h_rhs hdLb_pos.le, hpos_all]
      by_cases hev : eMin = v
      · subst hev
        have hm_z : (b : ℤ) * (q : ℤ) ^ eMin = m := by exact_mod_cast hm_eq.symm
        have hs_z : (sb : ℤ) * sigPP q eMin = sigma 1 m := by exact_mod_cast hsig_eq.symm
        rw [hm_z, hs_z] at hE_eMin_ge; omega
      · have hbq_e_proper : b * q ^ eMin ∈ m.properDivisors := by
          refine Nat.mem_properDivisors.mpr ⟨⟨q ^ (v - eMin), by rw [hm_eq, mul_assoc, ← pow_add, Nat.add_sub_cancel' heMin_le_v]⟩, ?_⟩
          have hpow_lt : q ^ eMin < q ^ v := Nat.pow_lt_pow_right hqp.one_lt (by omega)
          calc b * q ^ eMin < b * q ^ v := Nat.mul_lt_mul_of_pos_left hpow_lt hb_pos
            _ = m := hm_eq.symm
        have hbq_e_def := (deficient_iff_sigma_lt_two_mul _).mp (hm_prim _ hbq_e_proper)
        have hbq_e_sig : sigma 1 (b * q ^ eMin) = sb * sigPP q eMin := by
          rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (hq_cop.pow_right eMin),
              hb_sig, sigma_one_prime_pow hqp eMin]
        rw [hbq_e_sig] at hbq_e_def
        zify at hbq_e_def
        omega

lemma stepNF1_sound {m : ℕ} (_hm_odd : Odd m) (hm_ab : m.Abundant)
    (_hm_card : m.primeFactors.card ≤ 5) (hm_prim : ∀ d ∈ m.properDivisors, d.Deficient)
    (hE_lt : sigma 1 m - 2 * m < 64)
    {spec : List Entry} {minP g : ℕ} (_hs : SpecValid m spec minP) (_hg : checkG spec g = true)
    {p b sb : ℕ} (hp : p.Prime) (hb_pos : 0 < b) (hb_sig : sigma 1 b = sb) (hcop : b.Coprime p)
    (hpe_m : m = b * p ^ (m.factorization p) ∧ sigma 1 m = sb * sigPP p (m.factorization p))
    (hmiss : ∀ E, E = sigma 1 m - 2 * m → E < 64 → (allowedEMask spec g).contains E = false → Goal m) :
    ∀ fuel a, stepNF1 p b sb (allowedEMask spec g) fuel (p ^ a) (sigPP p a) = true →
      a ≤ m.factorization p → a % 2 = m.factorization p % 2 → Goal m := by
  intro fuel
  induction fuel with
  | zero => intro _ h; simp [stepNF1] at h
  | succ fuel ih =>
    intro a hstep ha_le ha_par
    have hm_eq := hpe_m.1
    have hsig_eq := hpe_m.2
    have h2m_lt : 2 * m < sigma 1 m := (abundant_iff_two_mul_lt_sigma m).mp hm_ab
    unfold stepNF1 at hstep
    split_ifs at hstep with hab
    · by_cases heq : a = m.factorization p
      · subst heq
        rw [mul_assoc 2 b, ← hm_eq, ← hsig_eq] at hab
        have hE_eq : sb * sigPP p (m.factorization p) - 2 * (b * p ^ m.factorization p) = sigma 1 m - 2 * m := by
          rw [← hm_eq, ← hsig_eq]
        simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at hstep
        rcases hstep with (h0 | h64) | hnot
        · rw [mul_assoc 2 b] at h0; omega
        · rw [mul_assoc 2 b] at h64; omega
        · exact hmiss (sigma 1 m - 2 * m) rfl hE_lt (by
            by_contra hc
            have hc' : (allowedEMask spec g).contains (sigma 1 m - 2 * m) = true := by
              cases h : (allowedEMask spec g).contains (sigma 1 m - 2 * m)
              · exact absurd h hc
              · rfl
            rw [mul_assoc 2 b, hE_eq, hc'] at hnot
            simp at hnot)
      · exfalso
        have hlt : a < m.factorization p := lt_of_le_of_ne ha_le heq
        have hprop : b * p ^ a ∈ m.properDivisors := by
          refine Nat.mem_properDivisors.mpr ⟨⟨p ^ (m.factorization p - a), ?_⟩, ?_⟩
          · conv_lhs => rw [hm_eq]
            rw [mul_assoc, ← pow_add, Nat.add_sub_cancel' ha_le]
          · have : p ^ a < p ^ m.factorization p := Nat.pow_lt_pow_right hp.one_lt hlt
            calc b * p ^ a < b * p ^ m.factorization p := Nat.mul_lt_mul_of_pos_left this hb_pos
              _ = m := hm_eq.symm
        have hdef := (deficient_iff_sigma_lt_two_mul _).mp (hm_prim _ hprop)
        rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (hcop.pow_right a),
            hb_sig, sigma_one_prime_pow hp a, ← mul_assoc 2 b] at hdef
        omega
    · have hne : a ≠ m.factorization p := by
        intro heq; subst heq; rw [mul_assoc 2 b, ← hm_eq, ← hsig_eq] at hab; omega
      have hle2 : a + 2 ≤ m.factorization p := by omega
      have hpow2 : p ^ a * p * p = p ^ (a + 2) := by rw [pow_succ, pow_succ]
      have hsig2 : sigPP p a * p * p + p + 1 = sigPP p (a + 2) := by
        have hrec : ∀ k, sigPP p (k + 1) = sigPP p k * p + 1 := fun k => by
          rw [sigPP_eq_geomSum p (k + 1) hp.one_lt, sigPP_eq_geomSum p k hp.one_lt,
              Finset.sum_range_succ', Finset.sum_mul]
          simp only [pow_zero]
          have : ∀ x ∈ range (k + 1), p ^ x * p = p ^ (x + 1) := fun x _ => by rw [← pow_succ]
          rw [Finset.sum_congr rfl this]
        rw [hrec (a + 1), hrec a]
        ring
      rw [hpow2, hsig2] at hstep
      exact ih (a + 2) hstep hle2 (by omega)

lemma checkNF1Go_aux {m : ℕ} (hm_odd : Odd m) (hm_ab : m.Abundant)
    (hm_card : m.primeFactors.card ≤ 5) (hm_prim : ∀ d ∈ m.properDivisors, d.Deficient)
    (hE_lt : sigma 1 m - 2 * m < 64)
    {spec : List Entry} {minP g : ℕ} (hs : SpecValid m spec minP) (hg : checkG spec g = true)
    (hlen : 5 - spec.length = 0) (hfree : spec.countP (fun e => !e.exact) = 1) :
    ∀ pref rest, spec = pref ++ rest →
      (∀ e ∈ pref, e.exact = true) →
      checkNF1Go (allowedEMask spec g) pref rest = true → Goal m := by
  have hm0 : m ≠ 0 := hm_odd.pos.ne'
  have hsub := spec_toFinset_subset hm0 hs
  have hcard_S := spec_toFinset_card hs
  have hS_eq : (spec.map (·.p)).toFinset = m.primeFactors :=
    Finset.eq_of_subset_of_card_le hsub (by have := Finset.card_le_card hsub; omega)
  have hrem_empty : m.primeFactors \ (spec.map (·.p)).toFinset = ∅ := by rw [hS_eq, Finset.sdiff_self]
  have hsplit := prod_spec_factor_split hm0 hs
  simp only [hrem_empty, Finset.prod_empty, mul_one] at hsplit
  intro pref rest hsp hpref hchk
  induction rest generalizing pref with
  | nil => simp [checkNF1Go] at hchk
  | cons e es ih =>
    unfold checkNF1Go at hchk
    split_ifs at hchk with hex
    · dsimp only at hchk
      have he : e ∈ spec := hsp ▸ List.mem_append_right _ List.mem_cons_self
      have hev := hs.2.1 e he
      have hex_f : e.exact = false := Bool.eq_false_iff.mpr (by simpa using hex)
      have hes_cnt : es.countP (fun x => !x.exact) = 0 := by
        have hc := hfree
        rw [hsp, List.countP_append, List.countP_cons] at hc
        have hpref0 : pref.countP (fun x => !x.exact) = 0 :=
          List.countP_eq_zero.mpr (fun x hx => by simp [hpref x hx])
        simp only [hex_f, Bool.not_false, ite_true] at hc
        omega
      have hall_ex : ∀ x ∈ pref ++ es, x.exact = true := fun x hx => by
        rw [List.mem_append] at hx
        rcases hx with hx | hx
        · exact hpref x hx
        · have := (List.countP_eq_zero.mp hes_cnt) x hx
          simpa using this
      have hmin_eq : minNumAb (pref ++ es) =
          (((pref ++ es).map (fun x => x.p ^ m.factorization x.p)).prod,
           ((pref ++ es).map (fun x => sigPP x.p (m.factorization x.p))).prod) := by
        unfold minNumAb
        have h1 : (pref ++ es).foldl (fun (nd : ℕ × ℕ) x => (nd.1 * x.p ^ x.minA, nd.2 * sigPP x.p x.minA)) (1, 1) =
            ((pref ++ es).foldl (fun acc x => acc * x.p ^ x.minA) 1,
             (pref ++ es).foldl (fun acc x => acc * sigPP x.p x.minA) 1) := by
          have hgen : ∀ (l : List Entry) (a b : ℕ),
              l.foldl (fun (nd : ℕ × ℕ) x => (nd.1 * x.p ^ x.minA, nd.2 * sigPP x.p x.minA)) (a, b) =
              (l.foldl (fun acc x => acc * x.p ^ x.minA) a,
               l.foldl (fun acc x => acc * sigPP x.p x.minA) b) := fun l => by
            induction l with
            | nil => intro _ _; rfl
            | cons y ys ihl => intro a b; simp [ihl]
          exact hgen (pref ++ es) 1 1
        rw [h1, foldl_mul_eq, foldl_mul_eq, one_mul, one_mul]
        congr 1 <;> refine congrArg List.prod (List.map_congr_left fun x hx => ?_)
        · have hx_ev := hs.2.1 x (hsp ▸ by rw [List.mem_append] at hx ⊢; rcases hx with h | h; exact Or.inl h; exact Or.inr (List.mem_cons_of_mem e h))
          rw [hx_ev.2.2.2.2.2.2.1 (hall_ex x hx)]
        · have hx_ev := hs.2.1 x (hsp ▸ by rw [List.mem_append] at hx ⊢; rcases hx with h | h; exact Or.inl h; exact Or.inr (List.mem_cons_of_mem e h))
          rw [hx_ev.2.2.2.2.2.2.1 (hall_ex x hx)]
      set b := ((pref ++ es).map (fun x => x.p ^ m.factorization x.p)).prod
      set sb := ((pref ++ es).map (fun x => sigPP x.p (m.factorization x.p))).prod
      rw [hmin_eq] at hchk
      have hb_pos : 0 < b := List.prod_pos fun z hz => by
        rw [List.mem_map] at hz; obtain ⟨x, hx, rfl⟩ := hz
        have hx_ev := hs.2.1 x (hsp ▸ by rw [List.mem_append] at hx ⊢; rcases hx with h | h; exact Or.inl h; exact Or.inr (List.mem_cons_of_mem e h))
        exact Nat.pow_pos hx_ev.1.pos
      have hm_eq : m = b * e.p ^ m.factorization e.p := by
        conv_lhs => rw [hsplit.1, hsp]
        simp only [List.map_append, List.map_cons, List.prod_append, List.prod_cons, b]
        ring
      have hsig_eq : sigma 1 m = sb * sigPP e.p (m.factorization e.p) := by
        conv_lhs => rw [hsplit.2, hsp]
        simp only [List.map_append, List.map_cons, List.prod_append, List.prod_cons, sb]
        ring
      have hcop : b.Coprime e.p := by
        refine hev.1.coprime_iff_not_dvd.mpr (fun hdvd => ?_) |>.symm
        have hndp := spec_map_p_nodup hs
        rw [hsp, List.map_append, List.map_cons] at hndp
        have hdvd_mem : ∃ x ∈ pref ++ es, x.p = e.p := by
          have : ∀ l : List Entry, (∀ x ∈ l, EntryValid m minP x) →
              e.p ∣ (l.map (fun x => x.p ^ m.factorization x.p)).prod → ∃ x ∈ l, x.p = e.p := by
            intro l hl hd
            induction l with
            | nil => simp at hd; exact absurd hd hev.1.ne_one
            | cons x xs ihl =>
              simp only [List.map_cons, List.prod_cons] at hd
              rcases hev.1.dvd_mul.mp hd with h1 | h2
              · have hxd := hev.1.dvd_of_dvd_pow h1
                have hxp := (hl x List.mem_cons_self).1
                exact ⟨x, List.mem_cons_self, (hxp.dvd_iff_eq hev.1.ne_one).mp hxd⟩
              · obtain ⟨y, hy, heq⟩ := ihl (fun z hz => hl z (List.mem_cons_of_mem x hz)) h2
                exact ⟨y, List.mem_cons_of_mem x hy, heq⟩
          exact this (pref ++ es) (fun x hx => hs.2.1 x (hsp ▸ by rw [List.mem_append] at hx ⊢; rcases hx with h | h; exact Or.inl h; exact Or.inr (List.mem_cons_of_mem e h))) hdvd
        obtain ⟨x, hx, hxp⟩ := hdvd_mem
        rw [List.nodup_append] at hndp
        rw [List.mem_append] at hx
        rcases hx with hx | hx
        · exact hndp.2.2 e.p (List.mem_map.mpr ⟨x, hx, hxp⟩) e.p (List.mem_map.mpr ⟨e, List.mem_cons_self, rfl⟩) rfl
        · have hnd2 := hndp.2.1
          rw [List.nodup_cons] at hnd2
          exact hnd2.1 (hxp ▸ List.mem_map_of_mem hx)
      have hb_sig : sigma 1 b = sb := by
        have h_all_eq : b = ((pref ++ es).map (fun x => x.p ^ m.factorization x.p)).prod := rfl
        have : ∀ l : List Entry, (l.map (·.p)).Pairwise (· < ·) → (∀ x ∈ l, EntryValid m minP x) →
            sigma 1 (l.map (fun x => x.p ^ m.factorization x.p)).prod =
            (l.map (fun x => sigPP x.p (m.factorization x.p))).prod := by
          intro l hpw hl
          induction l with
          | nil => simp
          | cons x xs ihl =>
            rw [List.map_cons, List.pairwise_cons] at hpw
            have hx := hl x List.mem_cons_self
            have ih' := ihl hpw.2 (fun z hz => hl z (List.mem_cons_of_mem x hz))
            have hcop_x : Nat.Coprime (x.p ^ m.factorization x.p) (xs.map (fun z => z.p ^ m.factorization z.p)).prod := by
              have hgen : ∀ l' : List Entry, (∀ z ∈ l', EntryValid m minP z ∧ x.p < z.p) →
                  Nat.Coprime (x.p ^ m.factorization x.p) (l'.map (fun z => z.p ^ m.factorization z.p)).prod := by
                intro l' hl'
                induction l' with
                | nil => simp
                | cons y ys ihy =>
                  simp only [List.map_cons, List.prod_cons]
                  have hy := hl' y List.mem_cons_self
                  have hc1 : Nat.Coprime (x.p ^ m.factorization x.p) (y.p ^ m.factorization y.p) :=
                    (hx.1.coprime_iff_not_dvd.mpr fun h => absurd ((Nat.dvd_prime hy.1.1).mp h |>.resolve_left hx.1.ne_one) hy.2.ne).pow _ _
                  exact hc1.mul_right (ihy fun z hz => hl' z (List.mem_cons_of_mem y hz))
              exact hgen xs fun z hz => ⟨hl z (List.mem_cons_of_mem x hz), hpw.1 z.p (List.mem_map_of_mem hz)⟩
            simp only [List.map_cons, List.prod_cons]
            rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop_x, sigma_one_prime_pow hx.1, ih']
        have hpw_pe : ((pref ++ es).map (·.p)).Pairwise (· < ·) := by
          have hpw := hs.1
          rw [hsp, List.map_append, List.map_cons] at hpw
          exact hpw.sublist (by simp)
        exact this (pref ++ es) hpw_pe (fun x hx => hs.2.1 x (hsp ▸ by rw [List.mem_append] at hx ⊢; rcases hx with h | h; exact Or.inl h; exact Or.inr (List.mem_cons_of_mem e h)))
      have hmiss : ∀ E, E = sigma 1 m - 2 * m → E < 64 → (allowedEMask spec g).contains E = false → Goal m :=
        fun E hEeq hElt hnot => by subst hEeq; exact goal_of_not_mem_allowedEMask hm_odd hm_ab hm_card hs hg hElt hnot
      exact stepNF1_sound hm_odd hm_ab hm_card hm_prim hE_lt hs hg hev.1 hb_pos hb_sig hcop
        ⟨hm_eq, hsig_eq⟩ hmiss 100 e.minA hchk hev.2.2.2.2.2.1 hev.2.2.2.2.2.2.2.2
    · have hsp' : spec = (pref ++ [e]) ++ es := by rw [hsp]; simp
      have hex_t : e.exact = true := by simpa using hex
      exact ih (pref ++ [e]) hsp' (fun x hx => by
        rw [List.mem_append, List.mem_singleton] at hx
        rcases hx with hx | rfl
        · exact hpref x hx
        · exact hex_t) hchk

lemma stepRem1E2_sound {m : ℕ} (hm_odd : Odd m) (hm_ab : m.Abundant)
    (hm_card : m.primeFactors.card ≤ 5) (hm_prim : ∀ d ∈ m.properDivisors, d.Deficient)
    (hE_lt : sigma 1 m - 2 * m < 64)
    {spec : List Entry} {minP g : ℕ} (hs : SpecValid m spec minP) (hg : checkG spec g = true)
    {q b sb D v : ℕ} (hq : q.Prime) (hb_pos : 0 < b) (hb_sig : sigma 1 b = sb)
    (hcop : b.Coprime q) (hm_eq : m = b * q ^ v) (hsig_eq : sigma 1 m = sb * sigPP q v)
    (_hD : sb + D = 2 * b) :
    ∀ fuel k, stepRem1E2 q sb (allowedEMask spec g) fuel ((sb * sigPP q k : ℤ) - 2 * (b * q ^ k : ℤ)) = true →
      k ≤ v → Goal m := by
  intro fuel
  induction fuel with
  | zero => intro _ h; simp [stepRem1E2] at h
  | succ fuel ih =>
    intro k hstep hk_le
    have h2m_lt : 2 * m < sigma 1 m := (abundant_iff_two_mul_lt_sigma m).mp hm_ab
    unfold stepRem1E2 at hstep
    split_ifs at hstep with hnonneg
    · by_cases heq : k = v
      · rcases heq with rfl
        set En := ((sb * sigPP q k : ℤ) - 2 * (b * q ^ k : ℤ)).toNat
        have hEn_eq : En = sigma 1 m - 2 * m := by
          have hm_z : (b : ℤ) * (q : ℤ) ^ k = m := by exact_mod_cast hm_eq.symm
          have hs_z : (sb : ℤ) * sigPP q k = sigma 1 m := by exact_mod_cast hsig_eq.symm
          dsimp only [En]
          rw [hm_z, hs_z]
          omega
        simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at hstep
        rcases hstep with (h0 | h64) | hnot
        · omega
        · omega
        · exact goal_of_not_mem_allowedEMask hm_odd hm_ab hm_card hs hg hE_lt (hEn_eq ▸ by
            cases hc : (allowedEMask spec g).contains En
            · rfl
            · rw [hc] at hnot; simp at hnot)
      · exfalso
        have hlt : k < v := lt_of_le_of_ne hk_le heq
        have hprop : b * q ^ k ∈ m.properDivisors := by
          refine Nat.mem_properDivisors.mpr ⟨⟨q ^ (v - k), ?_⟩, ?_⟩
          · rw [hm_eq, mul_assoc, ← pow_add, Nat.add_sub_cancel' hk_le]
          · have : q ^ k < q ^ v := Nat.pow_lt_pow_right hq.one_lt hlt
            calc b * q ^ k < b * q ^ v := Nat.mul_lt_mul_of_pos_left this hb_pos
              _ = m := hm_eq.symm
        have hdef := (deficient_iff_sigma_lt_two_mul _).mp (hm_prim _ hprop)
        rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (hcop.pow_right k),
            hb_sig, sigma_one_prime_pow hq k] at hdef
        zify at hdef; omega
    · have hne : k ≠ v := by
        intro heq; rcases heq with rfl
        have hm_z : (b : ℤ) * (q : ℤ) ^ k = m := by exact_mod_cast hm_eq.symm
        have hs_z : (sb : ℤ) * sigPP q k = sigma 1 m := by exact_mod_cast hsig_eq.symm
        rw [hm_z, hs_z] at hnonneg; omega
      have hle1 : k + 1 ≤ v := by omega
      rw [← excess_rec_step b q sb hq k] at hstep
      exact ih (k + 1) hstep hle1

lemma checkR1E1_sound (sb D : ℕ) (miss : List Nat) :
    ∀ ds lo q, checkR1E1 sb D miss lo ds = true → lo ≤ q → q < lo + ds.length →
      q.Prime → miss.contains (sb - D * q) = false := by
  intro ds
  induction ds with
  | nil => intro lo q _ h1 h2; simp at h2; omega
  | cons d ds ih =>
    intro lo q hchk h1 h2 hqp
    simp only [checkR1E1, Bool.and_eq_true] at hchk
    simp only [List.length_cons] at h2
    by_cases heq : q = lo
    · subst heq
      have hok := hchk.1
      split_ifs at hok with hd0
      · exfalso; exact checkFactor_not_prime hok hqp
      · cases hc : miss.contains (sb - D * q)
        · rfl
        · rw [hc] at hok; simp at hok
    · exact ih (lo + 1) q hchk.2 (by omega) (by omega) hqp

lemma checkRem1NF0_sound {m : ℕ} (hm_odd : Odd m) (hm_ab : m.Abundant)
    (hm_card : m.primeFactors.card ≤ 5) (hm_prim : ∀ d ∈ m.properDivisors, d.Deficient)
    (hE_lt : sigma 1 m - 2 * m < 64)
    {spec : List Entry} {minP minQ g b sb : ℕ} (hs : SpecValid m spec minP)
    (hg : checkG spec g = true) (hlen : 5 - spec.length = 1) (hnp : nextPrime minP = some minQ)
    (hmin : minNumAb spec = (b, sb)) (hexact : spec.countP (fun e => !e.exact) = 0)
    (hlt : sb < 2 * b)
    (hr1 : checkRem1NF0 b sb minQ (allowedEMask spec g) w1 w2 = true) : Goal m := by
  have hm0 : m ≠ 0 := hm_odd.pos.ne'
  have h2m_lt : 2 * m < sigma 1 m := (abundant_iff_two_mul_lt_sigma m).mp hm_ab
  have hall_ex : ∀ e ∈ spec, e.exact = true := fun e he => by
    have := (List.countP_eq_zero.mp hexact) e he; simpa using this
  have hmin_eq : minNumAb spec =
      ((spec.map (fun e => e.p ^ m.factorization e.p)).prod,
       (spec.map (fun e => sigPP e.p (m.factorization e.p))).prod) := by
    unfold minNumAb
    have hgen : ∀ (l : List Entry) (x y : ℕ),
        l.foldl (fun (nd : ℕ × ℕ) e => (nd.1 * e.p ^ e.minA, nd.2 * sigPP e.p e.minA)) (x, y) =
        (l.foldl (fun acc e => acc * e.p ^ e.minA) x, l.foldl (fun acc e => acc * sigPP e.p e.minA) y) := fun l => by
      induction l with
      | nil => intro _ _; rfl
      | cons a t ihl => intro x y; simp [ihl]
    rw [hgen spec 1 1, foldl_mul_eq, foldl_mul_eq, one_mul, one_mul]
    congr 1 <;> refine congrArg List.prod (List.map_congr_left fun e he => ?_)
    · rw [(hs.2.1 e he).2.2.2.2.2.2.1 (hall_ex e he)]
    · rw [(hs.2.1 e he).2.2.2.2.2.2.1 (hall_ex e he)]
  rw [hmin] at hmin_eq
  injection hmin_eq with hb_prod hsb_prod
  rcases rem1_structure hm_odd hm_ab hm_card hs hlen hnp with ⟨hbm, hsm⟩ |
      ⟨q, v, hqp, hq_ge, _, hq_cop, hv1, hm_eq, hsig_eq, hb_pos, hb_sig⟩
  · exfalso; rw [hb_prod, hsb_prod, hbm, ← hsm] at hlt; omega
  · rw [← hb_prod] at hb_pos hb_sig hm_eq hq_cop
    rw [← hsb_prod] at hb_sig hsig_eq
    unfold checkRem1NF0 at hr1
    dsimp only at hr1
    set D := 2 * b - sb
    have hD_pos : 0 < D := by omega
    have hD_eq : sb + D = 2 * b := by omega
    set qLo := max minQ (if sb ≥ 63 then (sb - 63 + D - 1) / D else 0)
    set qHi := if sb ≥ 1 then (sb - 1) / D else 0
    have he1_ok : (if qHi < qLo then w1.isEmpty else w1.length == qHi + 1 - qLo && checkR1E1 sb D (allowedEMask spec g) qLo w1) = true := by
      by_contra hf
      have hf' : (if qHi < qLo then w1.isEmpty else w1.length == qHi + 1 - qLo && checkR1E1 sb D (allowedEMask spec g) qLo w1) = false :=
        Bool.eq_false_iff.mpr hf
      rw [if_pos (by simp [hf'])] at hr1; exact Bool.noConfusion hr1
    have hr2_ok : (if (2 * b) / D ≥ minQ && 2 * b > D * ((2 * b) / D) && 2 * b < D * ((2 * b) / D + 1) then
        if w2 > 0 then checkFactor ((2 * b) / D) w2 else stepRem1E2 ((2 * b) / D) sb (allowedEMask spec g) 100 (-↑D)
        else true) = true := by
      rw [if_neg (by simp [he1_ok])] at hr1; exact hr1
    by_cases hv_eq1 : v = 1
    · subst hv_eq1
      have hsig1 : sigPP q 1 = q + 1 := by rw [sigPP_eq_geomSum q 1 hqp.one_lt]; simp [Finset.sum_range_succ]; omega
      rw [pow_one] at hm_eq
      rw [hsig1] at hsig_eq
      have hE_eq : sigma 1 m - 2 * m = sb - D * q := by
        conv_lhs => rw [hsig_eq, hm_eq]
        zify [show 2 * (b * q) ≤ sb * (q + 1) by rw [← hm_eq, ← hsig_eq]; exact h2m_lt.le,
              show D * q ≤ sb by
                have : (D : ℤ) * q ≤ sb := by
                  have hDz : (sb : ℤ) + D = 2 * b := by exact_mod_cast hD_eq
                  have hm2 : (2 : ℤ) * (b * q) < sb * (q + 1) := by exact_mod_cast (by rw [← hm_eq, ← hsig_eq]; exact h2m_lt)
                  nlinarith only [hDz, hm2]
                exact_mod_cast this]
        have : (sb : ℤ) + D = 2 * b := by exact_mod_cast hD_eq
        nlinarith only [this]
      have hE1 : 1 ≤ sb - D * q := by omega
      have hE63 : sb - D * q ≤ 63 := by omega
      have hq_hi : q ≤ qHi := by
        dsimp only [qHi]
        rw [if_pos (by omega)]
        have hmul : q * D ≤ sb - 1 := by rw [mul_comm]; omega
        exact (Nat.le_div_iff_mul_le hD_pos).mpr hmul
      have hq_lo : qLo ≤ q := by
        refine max_le hq_ge ?_
        split_ifs with h63
        · rw [Nat.div_le_iff_le_mul_add_pred hD_pos]
          have hsub_le : ∀ x y z w : ℕ, y ≤ x → 0 < z → x ≤ w + y → x - y + z - 1 ≤ w + (z - 1) := fun _ _ _ _ _ _ _ => by omega
          have h1 : sb ≤ D * q + 63 := by omega
          exact hsub_le sb 63 D (D * q) h63 hD_pos h1
        · exact Nat.zero_le q
      have hnot_lt : ¬ qHi < qLo := by omega
      rw [if_neg hnot_lt, Bool.and_eq_true, beq_iff_eq] at he1_ok
      have hnot := checkR1E1_sound sb D (allowedEMask spec g) w1 qLo q he1_ok.2 hq_lo (by omega) hqp
      rw [← hE_eq] at hnot
      exact goal_of_not_mem_allowedEMask hm_odd hm_ab hm_card hs hg hE_lt hnot
    · have hv2 : 2 ≤ v := by omega
      have hbq_proper : b * q ∈ m.properDivisors := by
        refine Nat.mem_properDivisors.mpr ⟨⟨q ^ (v - 1), by rw [hm_eq, mul_assoc, ← pow_succ', Nat.sub_add_cancel (by omega)]⟩, ?_⟩
        have hqv1 : q < q ^ v := lt_self_pow₀ hqp.one_lt (by omega)
        calc b * q < b * q ^ v := Nat.mul_lt_mul_of_pos_left hqv1 hb_pos
          _ = m := hm_eq.symm
      have hbq_def : sigma 1 (b * q) < 2 * (b * q) := (deficient_iff_sigma_lt_two_mul _).mp (hm_prim _ hbq_proper)
      have hq_sig1 : sigma 1 q = q + 1 := by
        simpa [pow_one] using (sigma_one_prime_pow hqp 1).trans
          (by rw [sigPP_eq_geomSum q 1 hqp.one_lt]; simp [Finset.sum_range_succ]; omega)
      rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hq_cop, hb_sig, hq_sig1] at hbq_def
      have hcf := excess_closed_form b q sb D hqp hD_eq v
      have hEv_pos : 0 < (sb * sigPP q v : ℤ) - 2 * (b * q ^ v : ℤ) := by
        have hm_z : (b : ℤ) * (q : ℤ) ^ v = m := by exact_mod_cast hm_eq.symm
        have hs_z : (sb : ℤ) * sigPP q v = sigma 1 m := by exact_mod_cast hsig_eq.symm
        rw [hm_z, hs_z]
        have hm2z : (2 * m : ℤ) < sigma 1 m := by exact_mod_cast h2m_lt
        omega
      have hq_pos_sub : (0 : ℤ) < (q : ℤ) - 1 := by have := hqp.one_lt; omega
      have hDq_lt : D * q < 2 * b := by
        by_contra hge
        have hle : (D : ℤ) + sb - q * D ≤ 0 := by
          have : (2 : ℤ) * b ≤ D * q := by exact_mod_cast Nat.le_of_not_lt hge
          have hDz : (sb : ℤ) + D = 2 * b := by exact_mod_cast hD_eq
          linarith only [this, hDz]
        have h1 := mul_nonpos_of_nonneg_of_nonpos (pow_nonneg (Nat.cast_nonneg q) v) hle
        have h2 := mul_pos hq_pos_sub hEv_pos
        linarith only [h1, h2, hcf]
      have h2b_lt : 2 * b < D * (q + 1) := by
        have h1 : (sb : ℤ) * (q + 1) < 2 * (b * q) := by exact_mod_cast hbq_def
        have h2 : (sb : ℤ) + D = 2 * b := by exact_mod_cast hD_eq
        zify; nlinarith only [h1, h2]
      have hq_eq : (2 * b) / D = q := by
        rw [mul_comm D q] at hDq_lt
        rw [mul_comm D (q + 1)] at h2b_lt
        exact Nat.div_eq_of_lt_le hDq_lt.le h2b_lt
      rw [hq_eq] at hr2_ok
      have hcond_true : (q ≥ minQ && 2 * b > D * q && 2 * b < D * (q + 1)) = true := by
        simp only [Bool.and_eq_true, decide_eq_true_eq]
        exact ⟨⟨hq_ge, hDq_lt⟩, h2b_lt⟩
      rw [if_pos hcond_true] at hr2_ok
      split_ifs at hr2_ok with hw2
      · exfalso; exact checkFactor_not_prime hr2_ok hqp
      · have h0 : (-↑D : ℤ) = (sb * sigPP q 0 : ℤ) - 2 * (b * q ^ 0 : ℤ) := by
          have hs0 : sigPP q 0 = 1 := by rw [sigPP_eq_geomSum q 0 hqp.one_lt]; simp
          rw [hs0, pow_zero]
          simp only [Nat.cast_one, mul_one]
          zify at hD_eq; linarith
        rw [h0] at hr2_ok
        exact stepRem1E2_sound hm_odd hm_ab hm_card hm_prim hE_lt hs hg hqp hb_pos hb_sig hq_cop hm_eq hsig_eq hD_eq 100 0 hr2_ok (Nat.zero_le v)

lemma checkR2_sound {m : ℕ} (hm_odd : Odd m) (hm_ab : m.Abundant)
    (hm_card : m.primeFactors.card ≤ 5)
    (go : List Entry → Nat → Cert → Bool)
    (hgo : ∀ sp mp sub, go sp mp sub = true → SpecValid m sp mp → Goal m)
    (spec : List Entry) (qStop : ℕ) (hs_orig : SpecValid m spec minP)
    (hlen : 5 - spec.length = 2)
    (hmax0 : maxAbSpec spec minP 0 = (abN, abD)) (habD : 0 < abD) (_hab_lt : abN < 2 * abD)
    (hqStop_bound : abN * qStop * (qStop + 2) ≤ 2 * abD * (qStop - 1) * (qStop + 1)) :
    ∀ cs curP, SpecValid m spec curP → minP ≤ curP →
      checkR2 go spec qStop curP cs = true → Goal m := by
  intro cs
  induction cs with
  | nil =>
    intro curP hs hmin hchk
    simp only [checkR2, beq_iff_eq] at hchk
    obtain ⟨hcur_q, hqp_stop, hq_none⟩ := nextPrime_spec hchk
    exfalso
    have hm0 : m ≠ 0 := hm_odd.pos.ne'
    have h2m_lt : 2 * m < sigma 1 m := (abundant_iff_two_mul_lt_sigma m).mp hm_ab
    have hspec_bound := (maxAbSpec_zero_sound hm0 hs_orig hmax0).2
    have hsplit := prod_spec_factor_split hm0 hs
    set S := (spec.map (·.p)).toFinset
    set S_out := m.primeFactors \ S
    set qs := S_out.sort (· ≤ ·)
    have hsub := spec_toFinset_subset hm0 hs
    have hcard_S := spec_toFinset_card hs
    have hcard_sdiff : S_out.card = m.primeFactors.card - spec.length := by
      dsimp only [S_out]
      rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hsub, hcard_S]
    have hpw : qs.Pairwise (· < ·) :=
      pairwise_lt_of_le_nodup (Finset.pairwise_sort S_out (· ≤ ·)) (Finset.sort_nodup S_out (· ≤ ·))
    have hlen_qs : qs.length ≤ 2 := by rw [Finset.length_sort]; omega
    have hqp_all : ∀ r ∈ qs, r.Prime ∧ Odd r ∧ qStop ≤ r := by
      intro r hr
      rw [Finset.mem_sort, Finset.mem_sdiff] at hr
      have hrp := Nat.prime_of_mem_primeFactors hr.1
      have hrodd : Odd r := hm_odd.of_dvd_nat (Nat.dvd_of_mem_primeFactors hr.1)
      have hrcur : curP ≤ r := (hs.2.2 r hr.1).resolve_left (fun ⟨e, he, heq⟩ =>
        hr.2 (List.mem_toFinset.mpr (List.mem_map.mpr ⟨e, he, heq⟩)))
      have hr_ge : qStop ≤ r := by
        by_contra hlt
        exact hq_none r hrcur (Nat.lt_of_not_le hlt) hrp
      exact ⟨hrp, hrodd, hr_ge⟩
    have hqStop_gt1 : 1 < qStop := hqp_stop.one_lt
    -- Bound (qs.map sigPP).prod * ((qStop - 1) * (qStop + 1)) ≤ (qs.map pow).prod * (qStop * (qStop + 2))
    have htail_bound : (qs.map (fun r => sigPP r (m.factorization r))).prod * ((qStop - 1) * (qStop + 1)) ≤
        (qs.map (fun r => r ^ m.factorization r)).prod * (qStop * (qStop + 2)) := by
      match qs with
      | [] =>
        simp only [List.map_nil, List.prod_nil, one_mul]
        nlinarith only [Nat.sub_le qStop 1, hqStop_gt1]
      | [r1] =>
        have hr1 := hqp_all r1 List.mem_cons_self
        have h1 : sigPP r1 (m.factorization r1) * (r1 - 1) ≤ r1 * r1 ^ m.factorization r1 :=
          (sigPP_lt_bound hr1.1.one_lt _).le
        have h2 : r1 * (qStop - 1) ≤ qStop * (r1 - 1) := by zify [hqStop_gt1.le, hr1.1.one_lt.le]; nlinarith only [hr1.2.2]
        have h3 : sigPP r1 (m.factorization r1) * (qStop - 1) ≤ qStop * r1 ^ m.factorization r1 := by
          apply Nat.le_of_mul_le_mul_right _ (Nat.sub_pos_of_lt hr1.1.one_lt)
          calc sigPP r1 (m.factorization r1) * (qStop - 1) * (r1 - 1)
              = (sigPP r1 (m.factorization r1) * (r1 - 1)) * (qStop - 1) := by ring
            _ ≤ (r1 * r1 ^ m.factorization r1) * (qStop - 1) := Nat.mul_le_mul_right _ h1
            _ = (r1 * (qStop - 1)) * r1 ^ m.factorization r1 := by ring
            _ ≤ (qStop * (r1 - 1)) * r1 ^ m.factorization r1 := Nat.mul_le_mul_right _ h2
            _ = qStop * r1 ^ m.factorization r1 * (r1 - 1) := by ring
        simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
        have h4 : qStop + 1 ≤ qStop + 2 := by omega
        calc _ = (sigPP r1 (m.factorization r1) * (qStop - 1)) * (qStop + 1) := by ring
          _ ≤ (qStop * r1 ^ m.factorization r1) * (qStop + 2) := Nat.mul_le_mul h3 h4
          _ = _ := by ring
      | [r1, r2] =>
        rw [List.pairwise_cons] at hpw
        have hr1 := hqp_all r1 List.mem_cons_self
        have hr2 := hqp_all r2 (List.mem_cons_of_mem r1 List.mem_cons_self)
        have hr12_lt : r1 < r2 := hpw.1 r2 List.mem_cons_self
        have hr2_ge : qStop + 2 ≤ r2 := by
          have hr1_even : r1 + 1 ≠ r2 := by
            intro heq
            have hne : Even (r1 + 1) := hr1.2.1.add_one
            rw [heq] at hne
            exact Nat.not_even_iff_odd.mpr hr2.2.1 hne
          omega
        have hb1 : sigPP r1 (m.factorization r1) * (qStop - 1) ≤ qStop * r1 ^ m.factorization r1 := by
          apply Nat.le_of_mul_le_mul_right _ (Nat.sub_pos_of_lt hr1.1.one_lt)
          have h1 := (sigPP_lt_bound hr1.1.one_lt (m.factorization r1)).le
          have h2 : r1 * (qStop - 1) ≤ qStop * (r1 - 1) := by zify [hqStop_gt1.le, hr1.1.one_lt.le]; nlinarith only [hr1.2.2]
          calc sigPP r1 (m.factorization r1) * (qStop - 1) * (r1 - 1)
              = (sigPP r1 (m.factorization r1) * (r1 - 1)) * (qStop - 1) := by ring
            _ ≤ (r1 * r1 ^ m.factorization r1) * (qStop - 1) := Nat.mul_le_mul_right _ h1
            _ = (r1 * (qStop - 1)) * r1 ^ m.factorization r1 := by ring
            _ ≤ (qStop * (r1 - 1)) * r1 ^ m.factorization r1 := Nat.mul_le_mul_right _ h2
            _ = qStop * r1 ^ m.factorization r1 * (r1 - 1) := by ring
        have hb2 : sigPP r2 (m.factorization r2) * (qStop + 1) ≤ (qStop + 2) * r2 ^ m.factorization r2 := by
          apply Nat.le_of_mul_le_mul_right _ (Nat.sub_pos_of_lt hr2.1.one_lt)
          have h1 := (sigPP_lt_bound hr2.1.one_lt (m.factorization r2)).le
          have h2 : r2 * (qStop + 1) ≤ (qStop + 2) * (r2 - 1) := by zify [hr2.1.one_lt.le]; nlinarith only [hr2_ge]
          calc sigPP r2 (m.factorization r2) * (qStop + 1) * (r2 - 1)
              = (sigPP r2 (m.factorization r2) * (r2 - 1)) * (qStop + 1) := by ring
            _ ≤ (r2 * r2 ^ m.factorization r2) * (qStop + 1) := Nat.mul_le_mul_right _ h1
            _ = (r2 * (qStop + 1)) * r2 ^ m.factorization r2 := by ring
            _ ≤ ((qStop + 2) * (r2 - 1)) * r2 ^ m.factorization r2 := Nat.mul_le_mul_right _ h2
            _ = (qStop + 2) * r2 ^ m.factorization r2 * (r2 - 1) := by ring
        simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
        calc _ = (sigPP r1 (m.factorization r1) * (qStop - 1)) * (sigPP r2 (m.factorization r2) * (qStop + 1)) := by ring
          _ ≤ (qStop * r1 ^ m.factorization r1) * ((qStop + 2) * r2 ^ m.factorization r2) := Nat.mul_le_mul hb1 hb2
          _ = _ := by ring
      | _ :: _ :: _ :: _ => simp at hlen_qs
    have hprod_qs_m : (qs.map (fun r => r ^ m.factorization r)).prod = ∏ q ∈ S_out, q ^ m.factorization q := by
      rw [← List.prod_toFinset _ (Finset.sort_nodup _ _), Finset.sort_toFinset]
    have hprod_qs_s : (qs.map (fun r => sigPP r (m.factorization r))).prod = ∏ q ∈ S_out, sigPP q (m.factorization q) := by
      rw [← List.prod_toFinset _ (Finset.sort_nodup _ _), Finset.sort_toFinset]
    rw [hprod_qs_m, hprod_qs_s] at htail_bound
    have hmul_all : sigma 1 m * (abD * (qStop - 1) * (qStop + 1)) ≤
        m * (abN * qStop * (qStop + 2)) := by
      conv_lhs => rw [hsplit.2]
      conv_rhs => rw [hsplit.1]
      calc ((spec.map (fun e => sigPP e.p (m.factorization e.p))).prod * ∏ q ∈ S_out, sigPP q (m.factorization q)) *
            (abD * (qStop - 1) * (qStop + 1))
          = ((spec.map (fun e => sigPP e.p (m.factorization e.p))).prod * abD) *
            ((∏ q ∈ S_out, sigPP q (m.factorization q)) * ((qStop - 1) * (qStop + 1))) := by ring
        _ ≤ ((spec.map (fun e => e.p ^ m.factorization e.p)).prod * abN) *
            ((∏ q ∈ S_out, q ^ m.factorization q) * (qStop * (qStop + 2))) :=
            Nat.mul_le_mul hspec_bound htail_bound
        _ = _ := by ring
    have hpos_den : 0 < abD * (qStop - 1) * (qStop + 1) :=
      Nat.mul_pos (Nat.mul_pos habD (Nat.sub_pos_of_lt hqStop_gt1)) (Nat.succ_pos _)
    nlinarith
  | cons item rest ih =>
    rcases item with ⟨q, c1, c2⟩
    intro curP hs hmin hchk
    simp only [checkR2, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hchk
    obtain ⟨⟨⟨⟨hnp, hq_lt⟩, hc1⟩, hc2⟩, hrest⟩ := hchk
    obtain ⟨hcur_q, hqp, hq_none⟩ := nextPrime_spec hnp
    by_cases hqdvd : q ∣ m
    · have hqodd : Odd q := hm_odd.of_dvd_nat hqdvd
      have hfac_pos : 1 ≤ m.factorization q := hqp.factorization_pos_of_dvd hm_odd.pos.ne' hqdvd
      have hrem_q : ∀ r ∈ m.primeFactors, (∃ e ∈ spec, e.p = r) ∨ r = q ∨ q + 1 ≤ r := by
        intro r hr
        rcases hs.2.2 r hr with ⟨e, he, rfl⟩ | hrcur
        · left; exact ⟨e, he, rfl⟩
        · have hrp := Nat.prime_of_mem_primeFactors hr
          have hqr : q ≤ r := by by_contra hlt; exact hq_none r hrcur (Nat.lt_of_not_le hlt) hrp
          by_cases heq : r = q
          · right; left; exact heq
          · right; right; omega
      rcases Nat.even_or_odd (m.factorization q) with heven | hodd
      · refine hgo _ (q + 1) c2 hc2 ?_
        exact specValid_ext hs hqp hcur_q hqodd hqdvd
          (by omega) (by obtain ⟨k, hk⟩ := heven; omega) (by simp) (by simpa using heven)
          (by obtain ⟨k, hk⟩ := heven; omega) hrem_q
      · refine hgo _ (q + 1) c1 hc1 ?_
        exact specValid_ext hs hqp hcur_q hqodd hqdvd
          (by omega) (by omega) (by simp) (by simpa using hodd)
          (by obtain ⟨k, hk⟩ := hodd; omega) hrem_q
    · have hrem' : ∀ r ∈ m.primeFactors, (∃ e ∈ spec, e.p = r) ∨ q + 1 ≤ r := by
        intro r hr
        rcases hs.2.2 r hr with ⟨e, he, rfl⟩ | hrcur
        · left; exact ⟨e, he, rfl⟩
        · have hrp := Nat.prime_of_mem_primeFactors hr
          have hqr : q ≤ r := by by_contra hlt; exact hq_none r hrcur (Nat.lt_of_not_le hlt) hrp
          have hne : r ≠ q := fun heq => hqdvd (heq ▸ Nat.dvd_of_mem_primeFactors hr)
          right; omega
      exact ih (q + 1) (specValid_mono_minP hs (by omega) hrem') (by omega) hrest

lemma spec_length_le_five {m : ℕ} (hm : m ≠ 0) (hm_card : m.primeFactors.card ≤ 5)
    {spec : List Entry} {minP : ℕ} (hs : SpecValid m spec minP) : spec.length ≤ 5 := by
  have := Finset.card_le_card (spec_toFinset_subset hm hs)
  rw [spec_toFinset_card hs] at this
  omega

lemma checkCert_sound {m : ℕ} (hm_odd : Odd m) (hm_ab : m.Abundant)
    (hm_card : m.primeFactors.card ≤ 5) (hm_prim : ∀ d ∈ m.properDivisors, d.Deficient)
    (hE_lt : sigma 1 m - 2 * m < 64) (h64 : 64 ≤ m)
    (leafOk : Nat → List Entry → Nat → Bool)
    (hLeaf : ∀ idx sp mp, leafOk idx sp mp = true → SpecValid m sp mp → Goal m) :
    ∀ fuel c spec minP, checkCert leafOk fuel c spec minP = true →
      SpecValid m spec minP → Goal m := by
  intro fuel
  have hm0 : m ≠ 0 := hm_odd.pos.ne'
  have h2m_lt : 2 * m < sigma 1 m := (abundant_iff_two_mul_lt_sigma m).mp hm_ab
  induction fuel with
  | zero => intro _ _ _ h; simp [checkCert] at h
  | succ fuel ih =>
    intro c spec minP hchk hs
    have hlen5 : spec.length ≤ 5 := spec_length_le_five hm0 hm_card hs
    unfold checkCert at hchk
    cases c with
    | A =>
      dsimp only at hchk
      have hmin_eq : minNumAb spec =
          ((spec.map (fun e => e.p ^ e.minA)).prod, (spec.map (fun e => sigPP e.p e.minA)).prod) := by
        unfold minNumAb
        have hgen : ∀ (l : List Entry) (x y : ℕ),
            l.foldl (fun (nd : ℕ × ℕ) e => (nd.1 * e.p ^ e.minA, nd.2 * sigPP e.p e.minA)) (x, y) =
            (l.foldl (fun acc e => acc * e.p ^ e.minA) x, l.foldl (fun acc e => acc * sigPP e.p e.minA) y) := fun l => by
          induction l with | nil => intro _ _; rfl | cons a t ihl => intro x y; simp [ihl]
        rw [hgen spec 1 1, foldl_mul_eq, foldl_mul_eq, one_mul, one_mul]
      obtain ⟨hb_pos, hb_dvd, hb_sig⟩ :=
        prod_spec_dvd_and_sigma hm0 hs (·.minA) (fun e he => (hs.2.1 e he).2.2.2.2.2.1)
      set b := (spec.map (fun e => e.p ^ e.minA)).prod
      set sb := (spec.map (fun e => sigPP e.p e.minA)).prod
      change (let (m_1, s) := minNumAb spec;
        if s < 2 * m_1 then false
        else let E := s - 2 * m_1; if E == 0 || E ≥ 64 then true else ((subsetMask (divsUpTo63 spec) / (2 ^ E)) % 2) == 1) = true at hchk
      rw [hmin_eq] at hchk
      dsimp only at hchk
      by_cases hlt : sb < 2 * b
      · rw [if_pos hlt] at hchk; exact Bool.noConfusion hchk
      rw [if_neg hlt] at hchk
      by_cases hbm : b = m
      · subst hbm
        rw [← hb_sig] at hchk
        by_cases he0 : (sigma 1 b - 2 * b == 0 || sigma 1 b - 2 * b ≥ 64) = true
        · simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at he0
          rcases he0 with he0 | h64' <;> omega
        · rw [if_neg he0] at hchk
          obtain ⟨hnd, hdivs⟩ := divsUpTo63_sound hm0 hs
          obtain ⟨s, hs_sub, hsum⟩ := subsetMask_sound hnd (by omega) hchk
          exact ⟨s, fun d hd => (hdivs d (List.mem_toFinset.mp (hs_sub hd))).2.1, hsum⟩
      · exfalso
        have hprop : b ∈ m.properDivisors :=
          Nat.mem_properDivisors.mpr ⟨hb_dvd, lt_of_le_of_ne (Nat.le_of_dvd hm_odd.pos hb_dvd) hbm⟩
        have hdef := (deficient_iff_sigma_lt_two_mul _).mp (hm_prim b hprop)
        rw [hb_sig] at hdef
        omega
    | B =>
      dsimp only at hchk
      rcases hmax_eq : maxAbSpec spec minP (5 - spec.length) with ⟨n, d⟩
      rw [hmax_eq] at hchk
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hchk
      have hbound := maxAbSpec_sound hm0 hm_card hs hlen5 rfl hmax_eq hchk.1
      exfalso; nlinarith
    | M g =>
      exact allowedEEmpty_sound hm_odd hm_ab hm_card h64 hs hE_lt hchk
    | N g =>
      simp only [Bool.and_eq_true, beq_iff_eq] at hchk
      exact checkNF1Go_aux hm_odd hm_ab hm_card hm_prim hE_lt hs hchk.1.1.1 hchk.1.1.2 hchk.1.2
        [] spec rfl (by simp) hchk.2
    | R1 g w1 w2 =>
      dsimp only at hchk
      cases hnp : nextPrime minP with
      | none => rw [hnp] at hchk; simp at hchk
      | some minQ =>
        rw [hnp] at hchk
        simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hchk
        rcases hmin_eq : minNumAb spec with ⟨b, sb⟩
        rw [hmin_eq] at hchk
        exact checkRem1NF0_sound hm_odd hm_ab hm_card hm_prim hE_lt hs
          hchk.1.1.1.1 hchk.1.1.1.2 hnp hmin_eq hchk.1.1.2 hchk.1.2 hchk.2
    | S7 p c0 c1 c2 c3 c4 =>
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hchk
      obtain ⟨⟨⟨⟨⟨⟨hnp, hp7⟩, hc0⟩, hc1⟩, hc2⟩, hc3⟩, hc4⟩ := hchk
      obtain ⟨hmin_p, hpp, hp_none⟩ := nextPrime_spec hnp
      by_cases hpdvd : p ∣ m
      · have hpodd : Odd p := hm_odd.of_dvd_nat hpdvd
        have hfac_pos : 1 ≤ m.factorization p := hpp.factorization_pos_of_dvd hm0 hpdvd
        have hrem_p : ∀ q ∈ m.primeFactors, (∃ e ∈ spec, e.p = q) ∨ q = p ∨ p + 1 ≤ q := by
          intro q hq
          rcases hs.2.2 q hq with ⟨e, he, rfl⟩ | hqmin
          · left; exact ⟨e, he, rfl⟩
          · have hqp := Nat.prime_of_mem_primeFactors hq
            have hpq : p ≤ q := by by_contra hlt; exact hp_none q hqmin (Nat.lt_of_not_le hlt) hqp
            by_cases heq : q = p
            · right; left; exact heq
            · right; right; omega
        by_cases h1 : m.factorization p = 1
        · refine ih c1 _ (p + 1) hc1 (specValid_ext hs hpp hmin_p hpodd hpdvd
            le_rfl hfac_pos (fun _ => h1) (by rw [h1]; exact odd_one) (by rw [h1]) hrem_p)
        · by_cases h2 : m.factorization p = 2
          · refine ih c2 _ (p + 1) hc2 (specValid_ext hs hpp hmin_p hpodd hpdvd
              (by omega) (by omega) (fun _ => h2) (by rw [h2]; exact even_two) (by rw [h2]) hrem_p)
          · rcases Nat.even_or_odd (m.factorization p) with heven | hodd
            · refine ih c4 _ (p + 1) hc4 ?_
              exact specValid_ext hs hpp hmin_p hpodd hpdvd
                (by omega) (by obtain ⟨k, hk⟩ := heven; omega) (by simp) (by simpa using heven)
                (by obtain ⟨k, hk⟩ := heven; omega) hrem_p
            · refine ih c3 _ (p + 1) hc3 ?_
              exact specValid_ext hs hpp hmin_p hpodd hpdvd
                (by omega) (by omega) (by simp) (by simpa using hodd)
                (by obtain ⟨k, hk⟩ := hodd; omega) hrem_p
      · have hrem' : ∀ q ∈ m.primeFactors, (∃ e ∈ spec, e.p = q) ∨ p + 1 ≤ q := by
          intro q hq
          rcases hs.2.2 q hq with ⟨e, he, rfl⟩ | hqmin
          · left; exact ⟨e, he, rfl⟩
          · have hqp := Nat.prime_of_mem_primeFactors hq
            have hpq : p ≤ q := by by_contra hlt; exact hp_none q hqmin (Nat.lt_of_not_le hlt) hqp
            have hne : q ≠ p := fun heq => hpdvd (heq ▸ Nat.dvd_of_mem_primeFactors hq)
            right; omega
        exact ih c0 spec (p + 1) hc0 (specValid_mono_minP hs (by omega) hrem')
    | P p c0 c1 c2 =>
      simp only [Bool.and_eq_true, beq_iff_eq] at hchk
      obtain ⟨⟨⟨hnp, hc0⟩, hc1⟩, hc2⟩ := hchk
      obtain ⟨hmin_p, hpp, hp_none⟩ := nextPrime_spec hnp
      by_cases hpdvd : p ∣ m
      · have hpodd : Odd p := hm_odd.of_dvd_nat hpdvd
        have hfac_pos : 1 ≤ m.factorization p := hpp.factorization_pos_of_dvd hm0 hpdvd
        have hrem_p : ∀ q ∈ m.primeFactors, (∃ e ∈ spec, e.p = q) ∨ q = p ∨ p + 1 ≤ q := by
          intro q hq
          rcases hs.2.2 q hq with ⟨e, he, rfl⟩ | hqmin
          · left; exact ⟨e, he, rfl⟩
          · have hqp := Nat.prime_of_mem_primeFactors hq
            have hpq : p ≤ q := by by_contra hlt; exact hp_none q hqmin (Nat.lt_of_not_le hlt) hqp
            by_cases heq : q = p
            · right; left; exact heq
            · right; right; omega
        rcases Nat.even_or_odd (m.factorization p) with heven | hodd
        · refine ih c2 _ (p + 1) hc2 ?_
          exact specValid_ext hs hpp hmin_p hpodd hpdvd
            (by omega) (by obtain ⟨k, hk⟩ := heven; omega) (by simp) (by simpa using heven) (by obtain ⟨k, hk⟩ := heven; omega) hrem_p
        · refine ih c1 _ (p + 1) hc1 ?_
          exact specValid_ext hs hpp hmin_p hpodd hpdvd
            (by omega) (by omega) (by simp) (by simpa using hodd) (by obtain ⟨k, hk⟩ := hodd; omega) hrem_p
      · have hrem' : ∀ q ∈ m.primeFactors, (∃ e ∈ spec, e.p = q) ∨ p + 1 ≤ q := by
          intro q hq
          rcases hs.2.2 q hq with ⟨e, he, rfl⟩ | hqmin
          · left; exact ⟨e, he, rfl⟩
          · have hqp := Nat.prime_of_mem_primeFactors hq
            have hpq : p ≤ q := by by_contra hlt; exact hp_none q hqmin (Nat.lt_of_not_le hlt) hqp
            have hne : q ≠ p := fun heq => hpdvd (heq ▸ Nat.dvd_of_mem_primeFactors hq)
            right; omega
        exact ih c0 spec (p + 1) hc0 (specValid_mono_minP hs (by omega) hrem')
    | X cur cs =>
      dsimp only at hchk
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hchk
      obtain ⟨⟨⟨⟨⟨_, _⟩, _⟩, _⟩, hprod_chk⟩, hexp⟩ := hchk
      have hgo : ∀ sp sub, checkCert leafOk fuel sub sp minP = true → SpecValid m sp minP → Goal m :=
        fun sp sub h => ih sub sp minP h
      rcases expandFree_sound (fun sp sub => checkCert leafOk fuel sub sp minP) hgo [] spec cur cs hs hexp with hcg | hg
      · obtain ⟨hb_pos, hb_dvd_B, hb_sig, _, _⟩ := curGe_prodWithCur hm0 hcg hs.1 hs.2.1
        set b := (prodWithCur spec cur 1 1).1
        set sb := (prodWithCur spec cur 1 1).2
        have hB_dvd_m : (spec.map (fun e => e.p ^ m.factorization e.p)).prod ∣ m :=
          (prod_spec_dvd_and_sigma hm0 hs (fun e => m.factorization e.p) (fun _ _ => le_rfl)).2.1
        have hb_dvd_m : b ∣ m := hb_dvd_B.trans hB_dvd_m
        split_ifs at hprod_chk with hlt
        by_cases hbm : b = m
        · subst hbm
          rw [← hb_sig] at hprod_chk
          simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at hprod_chk
          rcases hprod_chk with (he0 | he64) | hbit
          · exfalso; omega
          · exfalso; omega
          · obtain ⟨hnd, hdivs⟩ := divsUpTo63_sound hm0 hs
            obtain ⟨s, hs_sub, hsum⟩ := subsetMask_sound hnd (by omega) (beq_iff_eq.mpr hbit)
            exact ⟨s, fun d hd => (hdivs d (List.mem_toFinset.mp (hs_sub hd))).2.1, hsum⟩
        · exfalso
          have hprop : b ∈ m.properDivisors :=
            Nat.mem_properDivisors.mpr ⟨hb_dvd_m, lt_of_le_of_ne (Nat.le_of_dvd hm_odd.pos hb_dvd_m) hbm⟩
          have hdef := (deficient_iff_sigma_lt_two_mul _).mp (hm_prim b hprop)
          rw [hb_sig] at hdef
          omega
      · exact hg
    | T curA e1W e2W =>
      dsimp only at hchk
      rcases hnp : nextPrime minP with _ | minQ
      · rw [hnp] at hchk; simp at hchk
      · rcases hfind : spec.find? (fun e => !e.exact) with _ | fe
        · rw [hnp, hfind] at hchk; simp at hchk
        · rw [hnp, hfind] at hchk
          rcases hL : maxAbSpec spec minP 0 with ⟨abN, abD⟩
          rw [hL] at hchk
          simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hchk
          obtain ⟨⟨⟨⟨⟨hlen1, hfree1⟩, hfe_min⟩, habD⟩, habN⟩, hwit⟩ := hchk
          -- Construct CurGe m spec [curA] from freeCnt == 1 and fe.minA == curA!
          have hcg : CurGe m spec [curA] := by
            have hmem : fe ∈ spec ∧ (!fe.exact) = true := by
              have := List.find?_some hfind
              exact ⟨List.mem_of_find?_eq_some hfind, this⟩
            have hex_f : fe.exact = false := Bool.eq_false_iff.mpr (by simpa using hmem.2)
            have hcur_gen : ∀ l : List Entry, (∀ e ∈ l, EntryValid m minP e) →
                l.countP (fun e => !e.exact) = 1 → fe ∈ l → fe.minA = curA →
                CurGe m l [curA] := by
              intro l hl hc hfel hmin_eq
              induction l with
              | nil => simp at hfel
              | cons x xs ihl =>
                rw [List.countP_cons] at hc
                by_cases hx : x.exact = true
                · simp only [hx, Bool.not_true] at hc
                  rcases List.mem_cons.mp hfel with rfl | hxs
                  · simp [hx] at hex_f
                  · exact CurGe.exact hx (ihl (fun y hy => hl y (List.mem_cons_of_mem x hy)) hc hxs)
                · have hxf : x.exact = false := Bool.eq_false_iff.mpr hx
                  simp only [hxf, Bool.not_false, ite_true] at hc
                  have hxs0 : xs.countP (fun e => !e.exact) = 0 := by omega
                  have hx_eq : x = fe := by
                    rcases List.mem_cons.mp hfel with rfl | hxs
                    · rfl
                    · have := (List.countP_eq_zero.mp hxs0) fe hxs; simp [hex_f] at this
                  subst hx_eq
                  have hcg_xs : CurGe m xs [] := by
                    clear ihl hc hfel hl
                    induction xs with
                    | nil => exact CurGe.nil
                    | cons y ys ihys =>
                      rw [List.countP_cons] at hxs0
                      have hy_ex : y.exact = true := by
                        by_contra hyf
                        have hyf' : y.exact = false := Bool.eq_false_iff.mpr hyf
                        simp [hyf'] at hxs0
                      simp only [hy_ex, Bool.not_true] at hxs0
                      exact CurGe.exact hy_ex (ihys hxs0)
                  exact CurGe.free hex_f (hmin_eq ▸ (hl x List.mem_cons_self).2.2.2.2.2.1) hcg_xs
            exact hcur_gen spec hs.2.1 hfree1 hmem.1 hfe_min
          exact absurd (checkRem1TailWit_sound hm_odd hm_ab hm_card hm_prim hE_lt hs hlen1 hnp hL habD habN hcg hwit) id
    | L cur e1W e2W cs =>
      dsimp only at hchk
      rcases hnp : nextPrime minP with _ | minQ
      · rw [hnp] at hchk; simp at hchk
      · rw [hnp] at hchk
        rcases hL : maxAbSpec spec minP 0 with ⟨abN, abD⟩
        rw [hL] at hchk
        simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hchk
        obtain ⟨⟨⟨⟨⟨⟨hlen1, _⟩, habD⟩, habN⟩, _⟩, hwit⟩, hexp⟩ := hchk
        have hgo : ∀ sp sub, checkCert leafOk fuel sub sp minP = true → SpecValid m sp minP → Goal m :=
          fun sp sub h => ih sub sp minP h
        rcases expandFree_sound (fun sp sub => checkCert leafOk fuel sub sp minP) hgo [] spec cur cs hs hexp with hcg | hg
        · exact absurd (checkRem1TailWit_sound hm_odd hm_ab hm_card hm_prim hE_lt hs hlen1 hnp hL habD habN hcg hwit) id
        · exact hg
    | R2 qStop cs =>
      dsimp only at hchk
      rcases hL : maxAbSpec spec minP 0 with ⟨abN, abD⟩
      rw [hL] at hchk
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hchk
      obtain ⟨⟨⟨⟨hlen2, habD⟩, habN⟩, hqStop⟩, hr2⟩ := hchk
      have hgo : ∀ sp mp sub, checkCert leafOk fuel sub sp mp = true → SpecValid m sp mp → Goal m :=
        fun sp mp sub h => ih sub sp mp h
      exact checkR2_sound hm_odd hm_ab hm_card (fun sp mp sub => checkCert leafOk fuel sub sp mp)
        hgo spec qStop hs hlen2 hL habD habN hqStop cs minP hs le_rfl hr2
    | K idx =>
      exact hLeaf idx spec minP hchk hs

-- =====================================================================
-- Root lemmas & bottom-up chunk combinator
-- =====================================================================

lemma three_dvd_of_odd_abundant {m : ℕ} (hm_odd : Odd m) (hm_ab : m.Abundant)
    (hm_card : m.primeFactors.card ≤ 5) : 3 ∣ m := by
  by_contra h3
  have hm0 : m ≠ 0 := hm_odd.pos.ne'
  have hs : SpecValid m [] 5 := by
    refine ⟨List.Pairwise.nil, by simp, fun q hq => Or.inr ?_⟩
    have hqp := Nat.prime_of_mem_primeFactors hq
    have hqd := Nat.dvd_of_mem_primeFactors hq
    have hq2 : q ≠ 2 := fun he => hm_odd.not_two_dvd_nat (he ▸ hqd)
    have hq3 : q ≠ 3 := fun he => h3 (he ▸ hqd)
    have hq_ge2 := hqp.two_le
    by_contra hlt
    have h5 : q = 2 ∨ q = 3 ∨ q = 4 := by omega
    rcases h5 with rfl | rfl | rfl
    · exact hq2 rfl
    · exact hq3 rfl
    · exact absurd hqp (by decide)
  have hmax : maxAbSpec [] 5 5 = (85085, 46080) := by decide
  have hbound := maxAbSpec_sound hm0 hm_card hs (by simp) rfl hmax (by omega)
  have h2m_lt : 2 * m < sigma 1 m := (abundant_iff_two_mul_lt_sigma m).mp hm_ab
  omega

lemma sixtyFour_le_of_odd_abundant_three_dvd {m : ℕ} (hm_odd : Odd m) (hm_ab : m.Abundant)
    (h3 : 3 ∣ m) : 64 ≤ m := by
  by_contra hlt
  have hlt' : m < 64 := Nat.lt_of_not_le hlt
  have h2m_lt : 2 * m < ∑ d ∈ m.divisors, d := by
    simpa [ArithmeticFunction.sigma_one_apply] using (abundant_iff_two_mul_lt_sigma m).mp hm_ab
  have hdec : ∀ n < 64, n % 2 = 1 → n % 3 = 0 → ∑ d ∈ n.divisors, d ≤ 2 * n := by decide
  have hle := hdec m hlt' (Nat.odd_iff.mp hm_odd) (Nat.mod_eq_zero_of_dvd h3)
  omega

lemma root_specValid {m : ℕ} (hm_odd : Odd m) (h3 : 3 ∣ m) :
    (m.factorization 3 = 1 ∧ SpecValid m [⟨3, 1, true, .odd⟩] 5) ∨
    (m.factorization 3 = 2 ∧ SpecValid m [⟨3, 2, true, .even⟩] 5) ∨
    (3 ≤ m.factorization 3 ∧ Odd (m.factorization 3) ∧ SpecValid m [⟨3, 3, false, .odd⟩] 5) ∨
    (4 ≤ m.factorization 3 ∧ Even (m.factorization 3) ∧ SpecValid m [⟨3, 4, false, .even⟩] 5) := by
  have hm0 : m ≠ 0 := hm_odd.pos.ne'
  have h3p : Nat.Prime 3 := by decide
  have h3odd : Odd 3 := by decide
  have hfac : 1 ≤ m.factorization 3 := h3p.factorization_pos_of_dvd hm0 h3
  have hbase : SpecValid m [] 3 := ⟨List.Pairwise.nil, by simp, fun q hq => by
    have hqp := Nat.prime_of_mem_primeFactors hq
    have hqd := Nat.dvd_of_mem_primeFactors hq
    have hq2 : q ≠ 2 := fun he => hm_odd.not_two_dvd_nat (he ▸ hqd)
    have := hqp.two_le
    right; omega⟩
  have hrem3 : ∀ q ∈ m.primeFactors, (∃ e ∈ ([] : List Entry), e.p = q) ∨ q = 3 ∨ 3 + 1 ≤ q := by
    intro q hq
    have hqp := Nat.prime_of_mem_primeFactors hq
    have hqd := Nat.dvd_of_mem_primeFactors hq
    have hq2 : q ≠ 2 := fun he => hm_odd.not_two_dvd_nat (he ▸ hqd)
    have := hqp.two_le
    right
    by_cases hq3 : q = 3
    · left; exact hq3
    · right; omega
  have hrem5 : ∀ (a : ℕ) (ex : Bool) (par : Par),
      ∀ q ∈ m.primeFactors, (∃ e ∈ ([⟨3, a, ex, par⟩] : List Entry), e.p = q) ∨ 5 ≤ q := by
    intro a ex par q hq
    have hqp := Nat.prime_of_mem_primeFactors hq
    have hqd := Nat.dvd_of_mem_primeFactors hq
    have hq2 : q ≠ 2 := fun he => hm_odd.not_two_dvd_nat (he ▸ hqd)
    by_cases hq3 : q = 3
    · left; exact ⟨⟨3, a, ex, par⟩, List.mem_singleton_self _, hq3.symm⟩
    · right
      rcases lt_trichotomy q 4 with hlt4 | rfl | hgt4
      · have := hqp.two_le; omega
      · exact absurd hqp (by decide)
      · exact hgt4
  by_cases h1 : m.factorization 3 = 1
  · left
    have h3_1 : SpecValid m [⟨3, 1, true, .odd⟩] 4 :=
      specValid_ext hbase h3p le_rfl h3odd h3 le_rfl hfac (fun _ => h1) (by rw [h1]; exact odd_one) (by rw [h1]) hrem3
    exact ⟨h1, specValid_mono_minP h3_1 (by omega) (hrem5 1 true .odd)⟩
  · by_cases h2 : m.factorization 3 = 2
    · right; left
      have h3_2 : SpecValid m [⟨3, 2, true, .even⟩] 4 :=
        specValid_ext hbase h3p le_rfl h3odd h3 (by omega) (by omega) (fun _ => h2) (by rw [h2]; exact even_two) (by rw [h2]) hrem3
      exact ⟨h2, specValid_mono_minP h3_2 (by omega) (hrem5 2 true .even)⟩
    · rcases Nat.even_or_odd (m.factorization 3) with heven | hodd
      · right; right; right
        have h4 : 4 ≤ m.factorization 3 := by obtain ⟨k, hk⟩ := heven; omega
        have h3_4 : SpecValid m [⟨3, 4, false, .even⟩] 4 :=
          specValid_ext hbase h3p le_rfl h3odd h3 (by omega) h4 (by simp) (by simpa using heven) (by obtain ⟨k, hk⟩ := heven; omega) hrem3
        exact ⟨h4, heven, specValid_mono_minP h3_4 (by omega) (hrem5 4 false .even)⟩
      · right; right; left
        have h3_ge : 3 ≤ m.factorization 3 := by obtain ⟨k, hk⟩ := hodd; omega
        have h3_3 : SpecValid m [⟨3, 3, false, .odd⟩] 4 :=
          specValid_ext hbase h3p le_rfl h3odd h3 (by omega) h3_ge (by simp) (by simpa using hodd) (by obtain ⟨k, hk⟩ := hodd; omega) hrem3
        exact ⟨h3_ge, hodd, specValid_mono_minP h3_3 (by omega) (hrem5 3 false .odd)⟩

lemma goal_to_H1 {m : ℕ} (hm_ab : m.Abundant) (_h64 : 64 ≤ m) (_hE_lt : (sigma 1 m : ℤ) - 2 * (m : ℤ) < 64)
    (hg : Goal m) :
    let E : ℤ := (sigma 1 m : ℕ) - 2 * (m : ℤ)
    ∃ s ⊆ m.properDivisors.filter (fun d : ℕ => (d : ℤ) ≤ E), (∑ d ∈ s, (d : ℤ)) = E := by
  obtain ⟨s, hs_dvd, hs_sum⟩ := hg
  have h2m_lt : 2 * m < sigma 1 m := (abundant_iff_two_mul_lt_sigma m).mp hm_ab
  refine ⟨s, fun d hd => Finset.mem_filter.mpr ⟨Nat.mem_properDivisors.mpr ⟨hs_dvd d hd, ?_⟩, ?_⟩, ?_⟩
  · have hd_le_sum : d ≤ s.sum id := Finset.single_le_sum (f := id) (fun _ _ => Nat.zero_le _) hd
    omega
  · have hd_le_sum : d ≤ s.sum id := Finset.single_le_sum (f := id) (fun _ _ => Nat.zero_le _) hd
    omega
  · have hz : (∑ x ∈ s, (x : ℤ)) = ((s.sum id : ℕ) : ℤ) := by simp
    rw [hz, hs_sum]
    omega

def leafOk (ts : List (List Entry × Nat)) (bound idx : Nat) (sp : List Entry) (mp : Nat) : Bool :=
  idx < bound && ts[idx]? == some (sp, mp)

lemma leafOk_sound {m : ℕ} (ts : List (List Entry × Nat)) (k : ℕ)
    (hprev : ∀ i < k, ∀ sp mp, ts[i]? = some (sp, mp) → SpecValid m sp mp → Goal m) :
    ∀ idx sp mp, leafOk ts k idx sp mp = true → SpecValid m sp mp → Goal m := by
  intro idx sp mp hok hs
  unfold leafOk at hok
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hok
  exact hprev idx hok.1 sp mp hok.2 hs

def checkChunk (ts : List (List Entry × Nat)) (k : Nat) (c : Cert) : Bool :=
  match ts[k]? with
  | none => false
  | some (sp, mp) => checkCert (leafOk ts k) 30 c sp mp

lemma checkChunk_sound {m : ℕ} (hm_odd : Odd m) (hm_ab : m.Abundant)
    (hm_card : m.primeFactors.card ≤ 5)
    (hm_prim : ∀ d ∈ m.properDivisors, d.Deficient)
    (hE_lt : sigma 1 m - 2 * m < 64) (h64 : 64 ≤ m)
    (ts : List (List Entry × Nat)) (k : ℕ) (c : Cert)
    (ht : checkChunk ts k c = true)
    (hprev : ∀ i < k, ∀ sp mp, ts[i]? = some (sp, mp) → SpecValid m sp mp → Goal m) :
    ∀ i < k + 1, ∀ sp mp, ts[i]? = some (sp, mp) → SpecValid m sp mp → Goal m := by
  intro i hi sp mp hts hs
  rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | rfl
  · exact hprev i hlt sp mp hts hs
  · unfold checkChunk at ht
    rw [hts] at ht
    exact checkCert_sound hm_odd hm_ab hm_card hm_prim hE_lt h64 (leafOk ts i)
      (leafOk_sound ts i hprev) 30 c sp mp ht hs


private def ts : List (List Entry × Nat) := [([⟨3,1,true,.odd⟩],5),([⟨3,2,true,.even⟩],5),([⟨3,3,false,.odd⟩,⟨5,4,false,.even⟩,⟨17,2,false,.even⟩],18),([⟨3,3,false,.odd⟩],6),([⟨3,3,false,.odd⟩],5),([⟨3,4,false,.even⟩,⟨5,4,false,.even⟩,⟨17,2,false,.even⟩,⟨257,2,false,.even⟩],258),([⟨3,4,false,.even⟩,⟨5,4,false,.even⟩,⟨17,2,false,.even⟩],18),([⟨3,4,false,.even⟩,⟨5,4,false,.even⟩],6),([⟨3,4,false,.even⟩],5)]
private def c0 : Cert := (S7 5 B (S7 7 (P 11 B (M 6) (M 6)) (M 6) (M 6) (M 6) (M 6)) (S7 7 (P 11 (P 13 B (P 17 B (M 6) (L [3,2] [] [4] [B])) (P 17 B (M 6) (L [2,2] [] [4] []))) (M 6) (P 13 (P 17 (P 19 B (L [2,3] [] [4] [(L [4] [] [5] [B])]) (L [2,2] [] [4] [])) (M 6) (L [4,2] [] [5] [(T 2 [] [4])])) (L [4,5] [] [5] [(L [3] [] [6] [(R1 2 [] 2)]),(T 4 [] [4]),(L [6] [] [7] [(M 50)])]) (L [4,4] [] [5] [(T 2 [2] [4,6]),(M 6)]))) (P 11 (P 13 (R2 37 [(17,A,A),(19,(M 10),(L [4] [] [6] [(M 6)])),(23,(M 6),(T 2 [2] [4,6])),(29,(M 30),(T 2 [] [4])),(31,(M 62),(M 62))]) A A) A A) (M 6) (P 11 (P 13 (R2 59 [(17,A,A),(19,A,A),(23,A,A),(29,(M 30),(L [5,4] [19,2,5,2,3,2] [38,4,10,4,6,4,58] [(M 50),(L [7] [3] [6,4] [(M 6)])])),(31,(M 62),(M 62)),(37,(L [7,3] [] [4] [(M 50),(M 6),(T 7 [] [6])]),(L [7,4] [] [4] [(M 50),(M 6),(M 42)])),(41,(M 42),(L [3,2] [2,5,2] [4,10,4,6] [])),(43,(L [5,3] [] [5] [(M 50),(T 5 [] [4])]),(L [5,2] [] [5] [(M 50)])),(47,(M 6),(L [5,2] [] [4] [(M 50)])),(53,B,B)]) A A) A A) (P 11 (P 13 (R2 59 [(17,A,A),(19,A,A),(23,A,A),(29,(M 30),(L [6,4] [2] [4,58] [(L [4] [] [4] [(R1 2 [] 3)]),(T 6 [3] [6,4])])),(31,(M 62),(M 62)),(37,(L [6,3] [] [4] [(L [3] [] [5] [(R1 2 [] 2)]),(T 6 [] [6])]),(L [6,4] [] [4] [(T 2 [] [5]),(M 42)])),(41,(M 42),(L [4,2] [2] [4,6] [])),(43,(L [4,3] [] [5] [(T 4 [3] [6,4])]),(L [6,2] [] [5] [(L [4] [] [5] [(M 6)])])),(47,(M 6),(L [4,2] [] [4] [])),(53,B,B)]) A A) A A)) (S7 7 (P 11 (P 13 B (M 6) (M 6)) (M 6) (M 6)) (M 6) (M 6) (M 6) (M 6)) (S7 7 (P 11 (P 13 B (P 17 B (M 6) (L [4,3,2] [] [4] [(L [4,2] [] [6] [])])) (P 17 B (M 6) (L [4,4,2] [] [4] [(M 6)]))) (M 6) (P 13 (P 17 (P 19 B (L [4,4,3] [] [4] [(M 190),(L [4,4] [] [4] [])]) (L [4,4,2] [] [4] [(M 38)])) (M 6) (L [6,4,2] [] [4] [(M 22),(L [6,2] [] [5] [])])) (L [6,4,3] [2] [4,22] [(M 22),(L [6,3] [3] [6,4] [(T 6 [] [5])]),(L [6,4] [] [14] [])]) (L [6,4,4] [] [22] [(M 22),(L [6,4] [3] [6,4] [(M 6)]),(M 6)]))) (P 11 (P 13 (R2 41 [(17,A,A),(19,A,A),(23,(M 6),(L [6,4] [] [4] [(L [4] [] [10] [(R1 14 [] 0)]),(T 6 [] [4])])),(29,(M 30),(L [6,2] [] [5] [(T 2 [] [5])])),(31,(L [6,3] [] [4] [(L [3] [] [5] [(R1 2 [] 2)]),(T 6 [] [5])]),(L [6,2] [] [4] [(T 2 [] [5])])),(37,(L [6,3] [] [5] [(T 1 [3] [6,4]),(T 6 [] [6])]),(L [6,2] [] [5] [(T 2 [] [4])]))]) A A) A A) (M 6) (P 11 (P 13 (R2 71 [(17,A,A),(19,A,A),(23,A,A),(29,A,A),(31,A,A),(37,(L [8,7,3] [3,2] [6,4,10] [(L [7,3] [3] [6,4] [(M 50),(M 6),(T 7 [] [6])]),(L [5,3] [2,13,2,3,2,5,2,7,2,3,2,31,2,19] [4,26,4,6,4,10,4,14,4,6,4,62,4,38,4] [(M 50),(L [7] [] [4] [(M 6)])]),(M 50),(M 6),(L [8,7] [] [10] [])]),(L [8,7,4] [2] [4,10] [(L [7,4] [] [4] [(M 50),(M 6),(M 42)]),(L [5,4] [13,2,3,2,5,2,7,2,3,2,31,2,19] [26,4,6,4,10,4,14,4,6,4,62,4,38,4] [(M 50),(M 42)]),(M 50),(M 6),(M 42)])),(41,(M 42),(L [6,5,2] [3,2] [6,4,14] [(L [5,4] [] [5] [(M 50),(T 5 [] [4])]),(M 50)])),(43,(L [6,5,3] [] [10] [(L [5,3] [3] [6,4] [(M 50),(L [7] [] [4] [(M 258)])]),(M 50),(L [8,5] [] [5] [(L [7] [] [5] [(M 258)])])]),(L [6,5,2] [2] [4,10] [(L [5,2] [3] [6,4] [(M 50)]),(M 50)])),(47,(M 6),(L [8,5,2] [] [4] [(L [5,2] [] [22] [(M 50)]),(L [5,4] [] [4] [(M 50),(L [7] [] [4] [(M 6)])]),(M 50)])),(53,(M 6),(L [8,7,2] [] [4] [(L [5,2] [] [4] [(M 50)]),(L [5,2] [] [5] [(M 50)]),(M 50),(M 6)])),(59,(M 30),(L [6,5,2] [] [4] [(L [3,2] [5,2,3] [10,4,6,4] []),(M 50)])),(61,(L [6,5,1] [2,5] [4,10,4] [(L [5,3] [] [4] [(M 50),(T 5 [] [4])]),(M 50)]),(L [4,5,2] [2,5] [4,10,4] [(M 50)])),(67,(L [6,5,1] [3] [6,4] [(L [5,3] [] [4] [(M 50),(T 5 [] [5])]),(M 50)]),(L [4,5,2] [2,3] [4,6,4] [(M 50)]))]) A A) A A) (P 11 (P 13 (R2 71 [(17,A,A),(19,A,A),(23,A,A),(29,A,A),(31,A,A),(37,(L [8,6,3] [2,3,2] [4,6,4,10] [(L [6,3] [2,3] [4,6,4] [(L [3] [] [4] [(R1 2 [] 3)]),(T 6 [2] [4,6])]),(L [6,3] [2,19] [4,38,4] [(L [3] [2] [4,6] [(R1 2 [] 5)]),(L [8] [] [4] [(R1 2 [] 0)])]),(L [8,5] [2] [4,6] [(T 8 [] [4]),(M 10)]),(L [8,6] [] [10] [])]),(L [8,6,4] [3,2] [6,4,10] [(L [6,4] [3] [6,4] [(L [4] [] [4] [(M 42)]),(M 42)]),(L [6,4] [2,19] [4,38,4] [(L [4] [] [6] [(M 42)]),(M 42)]),(L [8,4] [2] [4,6] [(M 42)]),(M 42)])),(41,(M 42),(L [6,6,2] [3,2] [6,4,14] [(L [6,4] [] [5] [(T 2 [2] [4,14]),(T 6 [] [4])]),(L [8,4] [] [5] [(L [4] [] [4] [(R1 2 [] 2)]),(L [10] [] [4] [(R1 2 [] 0)])])])),(43,(L [6,4,3] [2,3,2] [4,6,4,10] [(L [6,3] [] [4] [(L [3] [] [5] [(R1 2 [] 2)]),(T 6 [] [4])]),(L [8,6] [] [5] [(L [8] [] [5] [(R1 2 [] 2),(R1 2 [] 2)]),(T 8 [] [5])])]),(L [6,4,2] [2,3,2] [4,6,4,10] [(L [6,2] [3] [6,4] [(T 2 [] [5])])])),(47,(M 6),(L [6,6,2] [] [4] [(L [4,2] [2] [4,22] []),(L [8,4] [] [5] [(T 2 [] [4]),(L [10] [] [7] [(R1 2 [] 2)])])])),(53,(M 6),(L [8,6,2] [] [4] [(L [4,2] [3] [6,4] []),(L [4,2] [] [5] []),(L [8,2] [] [5] [])])),(59,(M 30),(L [6,4,2] [] [4] [(L [4,2] [3] [6,4] [])])),(61,(L [6,4,3] [5] [10,4] [(L [6,3] [] [4] [(L [3] [] [5] [(R1 2 [] 3)]),(T 6 [] [4])]),(L [6,6] [] [4] [(L [8] [] [4] [(R1 2 [] 0)])])]),(L [6,4,2] [5] [10,4] [(L [6,2] [] [4] [(T 2 [] [5])])])),(67,(L [6,4,1] [2,3] [4,6,4] [(L [4,3] [] [4] [(T 4 [] [5])])]),(L [4,4,2] [2,3] [4,6,4] []))]) A A) A A)))
private def c1 : Cert := (S7 5 (S7 7 B (P 11 (P 13 B (M 182) (M 26)) (R2 23 [(13,(M 546),(M 78)),(17,(M 18),(L [3,2] [] [4] [(L [4] [] [5] [(R1 6 [] 2)])])),(19,(L [5,3] [] [4] [B,(L [3] [] [5] [B]),B]),(L [5,4] [] [4] [B,(T 2 [] [5]),(M 18)]))]) (P 13 (P 17 (P 19 B (L [4,3] [] [4] [(M 266),B]) (L [4,4] [] [4] [(M 266),(T 4 [] [5])])) (M 18) (L [2,2] [3] [6,4] [])) (M 182) (M 26))) (P 11 (P 13 B (M 546) (M 39)) (M 18) (R2 29 [(13,(M 546),(M 39)),(17,(M 18),(L [4,2] [2] [4,10] [(M 21)])),(19,(M 114),(M 57)),(23,(M 18),(L [4,2] [] [5] [B]))])) (P 11 (P 13 B (M 182) (M 26)) (R2 29 [(13,(M 546),(M 78)),(17,(M 18),(L [3,3,2] [2,3,2] [4,6,4,10] [(L [5,2] [] [4] [(L [4] [] [4] [(R1 6 [] 0)])])])),(19,(L [3,3,3] [3] [6,4] [(L [3,3] [] [6] [(T 3 [] [4])]),(L [5,5] [] [5] [(T 3 [] [4]),(T 5 [] [4])])]),(L [3,3,2] [2,3] [4,6,4] [(L [3,2] [] [6] [])])),(23,(M 18),(L [5,3,2] [] [4] [(L [3,2] [] [5] [B]),B]))]) (P 13 (P 17 (P 19 (P 23 B (L [5,4,3] [] [4] [(L [2,3] [] [5] [(L [4] [] [4] [(M 42)])]),(M 42),(L [5,4] [] [4] [])]) (L [5,4,2] [] [4] [(L [4,2] [] [5] [(M 14)]),(M 14)])) (L [3,4,3] [3] [6,4] [(M 266),(L [7,4] [] [5] [(T 4 [] [4]),(M 114)])]) (L [3,4,2] [3] [6,4] [(M 266)])) (M 18) (L [3,4,2] [3,2] [6,4,10] [(M 14)])) (M 182) A)) (P 11 (P 13 B (M 182) (M 13)) (R2 29 [(13,(M 546),(M 78)),(17,(M 18),(L [4,3,2] [2] [4,10] [(L [4,2] [] [4] [])])),(19,(L [4,3,3] [3] [6,4] [(L [4,3] [] [6] [(T 4 [] [4])]),(L [6,5] [] [5] [(T 3 [] [4]),(T 6 [] [4])])]),(L [4,3,2] [3] [6,4] [(L [4,2] [] [6] [])])),(23,(M 18),(L [4,3,2] [] [4] [B]))]) (P 13 (P 17 (P 19 (P 23 B (L [4,4,3] [] [4] [(M 42),(L [4,4] [] [4] [])]) (L [4,4,2] [] [4] [(M 7)])) (L [4,2,3] [2,3] [4,6,4] [(L [6,4] [] [5] [(T 2 [3] [6,4]),(M 266)])]) (L [4,2,2] [2,3] [4,6,4] [])) (M 18) (L [4,4,2] [2] [4,10] [(M 7)])) (M 182) A))) (S7 7 (P 11 (P 13 (P 17 B (M 18) (M 6)) (M 78) (M 78)) (M 18) (M 6)) (M 6) A A A) (S7 7 (P 11 (P 13 (P 17 (P 19 (P 23 B (M 6) (R2 31 [(29,(M 30),(L [2,2] [2] [4,6] []))])) (M 10) (R2 37 [(23,(M 6),(L [4,2] [2] [4,10] [(M 3)])),(29,(M 30),(L [2,2] [] [5] [])),(31,(M 62),(M 31))])) (M 18) (R2 41 [(19,A,A),(23,(M 6),(L [4,4] [] [5] [(L [4] [] [4] [(R1 1 [] 0)]),(T 4 [] [4])])),(29,(M 30),(L [4,2] [2] [4,6] [(L [4] [] [4] [(R1 1 [] 0)])])),(31,(M 62),(M 31)),(37,(L [2,3] [2] [4,6] [(T 2 [] [5])]),(L [2,2] [2] [4,6] []))])) (M 26) (M 13)) (M 6) (P 13 (P 17 (P 19 (R2 137 [(23,A,A),(29,A,A),(31,A,A),(37,A,A),(41,A,A),(43,A,A),(47,A,A),(53,A,A),(59,A,A),(61,A,A),(67,(X [4,3] [(L [3] [] [5] [(R1 2 [] 11)]),(L [6] [2] [4,14] [(M 10)])]),(X [4,2] [(L [4] [] [5] [(M 3)])])),(71,(M 18),(L [6,4] [] [10] [(T 2 [7] [14,4]),(M 5),(T 6 [] [6])])),(73,(L [6,3] [] [4] [(L [3] [] [4] [(R1 2 [] 2)]),(M 10),(T 6 [] [6])]),(L [6,4] [] [4] [(T 2 [] [4]),(M 5),(M 3)])),(79,(M 10),(L [4,2] [3] [6,4] [(T 2 [] [4])])),(83,(M 6),(L [6,2] [] [5] [(T 2 [] [10]),(M 5)])),(89,(M 90),(L [4,2] [] [4] [(T 2 [] [6])])),(97,(L [4,3] [5] [10,4] [(T 1 [2,3,2,5] [4,6,4,10,4]),(L [6] [] [5] [(M 10)])]),(L [4,2] [5] [10,4] [(T 2 [] [4])])),(101,(M 6),(L [4,2] [] [4] [(T 2 [] [4])])),(103,(L [6,3] [] [5] [(L [3] [] [5] [(R1 2 [] 2)]),(M 10),(T 6 [] [22])]),(L [6,2] [] [5] [(T 2 [] [5]),(M 5)])),(107,(M 18),(L [4,2] [] [4] [(T 2 [] [5])])),(109,(M 110),(L [4,2] [] [5] [(T 2 [] [6])])),(113,(M 6),(L [6,2] [] [4] [(T 2 [] [4]),(M 5)])),(127,(L [4,1] [2] [4,6] [B]),(L [4,2] [] [6] [B])),(131,B,B)]) A A) A A) A A)) A A A A) (S7 7 (P 11 (P 13 (P 17 (P 19 (P 23 B (M 18) (M 6)) (M 30) (M 6)) (M 18) (M 6)) (M 78) (M 78)) (M 18) (M 6)) A A A A) (S7 7 (P 11 (P 13 (P 17 (P 19 (P 23 B (M 6) (R2 37 [(29,(M 30),(L [6,2,2] [] [4] [(L [2,2] [] [5] [])])),(31,(L [4,2,1] [2,3] [4,6,4] []),(L [4,2,2] [3] [6,4] []))])) (M 10) (R2 43 [(23,(M 6),(L [6,4,4] [5] [10,4] [(L [4,4] [] [10] [(M 3),(T 4 [] [4])]),(M 3),(L [6,4] [7] [14,4] [])])),(29,(M 30),(L [6,2,2] [3] [6,4] [(L [4,2] [] [4] [(M 3)])])),(31,(L [4,2,3] [3,2] [6,4,10] [(L [6,4] [] [5] [(L [4] [] [4] [(M 6)]),(M 6)])]),(L [4,2,2] [3,2] [6,4,10] [])),(37,(M 38),(L [6,2,2] [] [4] [(L [2,2] [] [5] [])])),(41,(M 6),(L [8,4,4] [] [7] [B,B,B,B]))])) (M 18) (R2 53 [(19,A,A),(23,A,A),(29,(M 30),(L [6,4,4] [] [4] [(L [2,2] [2,3,2,11,2] [4,6,4,22,4,10] []),(L [6,2] [3] [6,4] []),(L [6,4] [] [5] [])])),(31,(L [6,4,3] [] [5] [(L [4,3] [] [5] [(L [5] [] [5] [(R1 2 [] 2),(R1 2 [] 0)]),(T 4 [] [4])]),(L [6,3] [] [4] [(T 6 [] [6])]),(L [6,4] [] [5] [])]),(L [6,4,4] [] [5] [(L [4,4] [] [5] [(L [4] [] [5] [(M 3)]),(M 3)]),(L [6,2] [] [4] []),(M 3)])),(37,(L [4,2,3] [2,3] [4,6,4] [(L [6,4] [] [5] [(T 2 [2] [4,10]),(T 6 [] [4])])]),(L [4,2,2] [2,3] [4,6,4] [])),(41,(M 6),(L [6,4,2] [] [5] [(L [2,2] [3] [6,4] []),(L [6,2] [] [4] [])])),(43,(L [4,2,3] [2] [4,10] [(L [6,4] [] [4] [(L [4] [] [5] [(R1 2 [] 2)]),(T 6 [] [5])])]),(L [4,2,2] [2] [4,10] [])),(47,B,B)])) (M 26) (M 13)) (M 6) (P 13 (P 17 (P 19 (R2 293 [(23,A,A),(29,A,A),(31,A,A),(37,A,A),(41,A,A),(43,A,A),(47,A,A),(53,A,A),(59,A,A),(61,A,A),(67,A,A),(71,A,A),(73,A,A),(79,A,A),(83,A,A),(89,A,A),(97,A,A),(101,A,A),(103,A,A),(107,A,A),(109,A,A),(113,A,A),(127,(X [4,4,1] [(X [6,1] [(L [3] [] [4] [(R1 22 [] 3)])])]),(X [4,4,2] [(X [6,2] [(L [4] [] [4] [(M 33)])])])),(131,(M 66),(X [4,4,2] [(L [12,4] [] [14] [(L [4] [] [6] [(R1 11 [] 2)]),(L [4] [] [4] [(R1 1 [] 3)]),(L [4] [] [14] [(R1 1 [] 2)]),(L [4] [] [5] [(R1 1 [] 3)]),(T 12 [3] [6,4])])])),(137,(M 6),(X [4,4,2] [(L [10,2] [2,3,2] [4,6,4,86] [(L [4] [] [4] [(R1 11 [] 0)]),(T 2 [2,5,2] [4,10,4,6]),(L [4] [] [34] [(R1 1 [] 0)])])])),(139,(M 10),(X [6,4,2] [(L [8,4] [] [4] [(T 2 [] [46]),(M 55),(L [4] [] [5] [(M 33)]),(M 33)]),(L [10,4] [] [4] [(L [4] [] [4] [(M 3)]),(L [4] [] [4] [(M 3)]),(M 3)])])),(149,(M 150),(L [10,8,4] [] [4] [(L [6,2] [2] [4,6] [(T 2 [3] [6,4]),(M 55)]),(L [6,2] [2,11,2,7,2] [4,22,4,14,4,6] [(T 2 [] [14]),(M 5)]),(L [8,4] [] [5] [(T 2 [] [5]),(M 5),(T 2 [2,31,2,7,2,3] [4,62,4,14,4,6,4]),(T 8 [] [62])]),(L [10,2] [] [4] []),(M 5),(L [10,4] [] [5] [(T 10 [] [10])]),(L [10,8] [] [4] [])])),(151,(L [10,6,3] [] [10] [(L [6,3] [] [4] [(L [3] [] [4] [(R1 22 [] 5)]),(M 110),(T 6 [] [5])]),(L [6,3] [] [4] [(L [3] [] [5] [(R1 2 [] 0)]),(M 10),(T 6 [] [4])]),(L [6,3] [] [4] [(L [3] [] [5] [(R1 2 [] 19)]),(M 10),(L [8] [] [4] [(R1 2 [] 0)])]),(L [10,3] [] [4] [(T 10 [] [38])]),(M 10),(L [10,6] [] [22] [])]),(L [10,6,4] [] [10] [(L [6,2] [] [4] [(T 2 [] [4]),(M 55)]),(L [6,2] [5,2,3] [10,4,6,4] [(L [4] [] [5] [(M 3)]),(M 5)]),(L [6,4] [] [4] [(T 2 [] [5]),(M 5),(M 3)]),(L [10,4] [] [4] [(M 3)]),(M 5),(M 3)])),(157,(L [8,6,3] [2] [4,22] [(L [6,3] [] [4] [(L [3] [] [4] [(R1 22 [] 3)]),(M 110),(T 6 [] [4])]),(L [4,3] [7,2,5,2,3,2,23,2,41,2,3,2,5,2,7,2,3] [14,4,10,4,6,4,46,4,82,4,6,4,10,4,14,4,6,4] [(L [3] [] [4] [(R1 2 [] 3)]),(L [6] [] [4] [(M 10)])]),(L [10,3] [] [4] [(L [3] [] [5] [(R1 2 [] 3)]),(T 10 [] [6])]),(M 10),(L [10,6] [] [4] [(T 6 [] [5])])]),(L [8,6,2] [3,2] [6,4,22] [(L [6,2] [] [4] [(T 2 [] [4]),(M 55)]),(L [4,2] [2,7,2,5,2,3,2,23,2,41,2,3,2,5,2,7,2,3] [4,14,4,10,4,6,4,46,4,82,4,6,4,10,4,14,4,6,4] [(T 2 [] [4])]),(L [10,4] [] [4] [(T 2 [] [5]),(M 3)]),(M 5)])),(163,(L [8,6,3] [2] [4,6] [(L [6,3] [] [5] [(L [3] [] [4] [(R1 22 [] 2)]),(M 110),(T 6 [] [5])]),(L [6,3] [] [4] [(L [3] [] [6] [(R1 2 [] 2)]),(M 10),(T 6 [] [4])]),(L [8,3] [] [4] [(T 8 [] [14])]),(M 10),(L [8,6] [2] [4,6] [])]),(L [8,6,2] [2] [4,6] [(L [6,2] [] [5] [(T 2 [] [4]),(M 55)]),(L [6,2] [] [4] [(T 2 [] [6]),(M 5)]),(L [8,2] [] [4] []),(M 5)])),(167,(M 6),(L [10,6,4] [] [5] [(L [4,2] [2,3,2,19] [4,6,4,38,4] [(T 2 [] [4])]),(L [6,2] [] [10] [(T 2 [] [6]),(M 5)]),(L [6,2] [] [4] [(T 2 [] [22]),(M 5)]),(L [10,2] [] [22] []),(M 5),(L [10,8] [] [5] [(L [12] [] [5] [(R1 1 [] 2)])])])),(173,(M 6),(L [10,6,4] [] [4] [(L [4,2] [2,3] [4,6,4] [(T 2 [] [4])]),(L [4,2] [2,29,2,3] [4,58,4,6,4] [(T 2 [2] [4,22])]),(L [6,2] [] [5] [(T 2 [] [4]),(M 5)]),(L [10,2] [] [4] []),(M 5),(L [10,6] [] [5] [])])),(179,(M 90),(L [8,4,2] [2,3,2,17] [4,6,4,34,4] [(L [6,2] [] [5] [(T 2 [] [4]),(M 55)]),(L [4,2] [2,3,2] [4,6,4,10] [(T 2 [] [14])]),(L [8,2] [] [4] [])])),(181,(L [8,4,3] [17,2,3] [34,4,6,4] [(L [6,3] [] [4] [(L [3] [] [4] [(R1 22 [] 5)]),(M 110),(T 6 [] [4])]),(L [6,3] [] [4] [(T 1 [2,11,2,3,2,5] [4,22,4,6,4,10,4]),(M 10),(T 6 [] [14])]),(L [8,3] [] [6] [(T 8 [] [4])]),(L [8,6] [] [10] [(M 10)])]),(L [8,4,2] [17,2,3] [34,4,6,4] [(L [6,2] [] [4] [(T 2 [] [4]),(M 55)]),(L [6,2] [] [4] [(T 2 [] [4]),(M 5)]),(L [8,2] [] [6] [])])),(191,(M 6),(L [8,4,2] [3,2,7] [6,4,14,4] [(L [4,2] [3] [6,4] [(T 2 [] [4])]),(L [6,2] [] [5] [(T 2 [] [26]),(M 5)]),(L [8,2] [] [6] [])])),(193,(L [8,6,3] [] [4] [(L [4,1] [2,3,2,11,2,5,2,3] [4,6,4,22,4,10,4,6,4] [(L [3] [] [6] [(R1 22 [] 2)])]),(L [4,3] [2,13] [4,26,4] [(T 1 [2,17,2,3] [4,34,4,6,4]),(T 4 [2] [4,38])]),(L [8,1] [2,3,2,5] [4,6,4,10,4] []),(M 10),(L [8,6] [] [6] [])]),(L [8,6,2] [] [4] [(L [4,2] [2,3] [4,6,4] [(T 2 [] [6])]),(L [4,2] [2,13] [4,26,4] [(T 2 [] [4])]),(L [8,2] [] [4] []),(M 5)])),(197,(M 198),(L [6,4,2] [17,2,23,2,3] [34,4,46,4,6,4] [(L [4,2] [3,2] [6,4,10] [(T 2 [] [6])]),(L [8,2] [] [4] [(T 2 [] [4])])])),(199,(M 50),(L [6,4,2] [3,2,5,2,11] [6,4,10,4,22,4] [(L [6,2] [] [4] [(T 2 [] [6]),(M 55)]),(L [8,2] [] [5] [(T 2 [] [14])])])),(211,(L [8,6,3] [] [22] [(L [4,1] [2,17,2,3] [4,34,4,6,4] [(T 1 [2,3] [4,6,4])]),(L [4,3] [3] [6,4] [(T 1 [3,2] [6,4,10]),(L [6] [] [4] [(M 10)])]),(L [8,3] [] [5] [(T 8 [] [4])]),(M 10),(L [8,6] [] [4] [])]),(L [8,6,2] [] [22] [(L [4,2] [3] [6,4] [(T 2 [] [4])]),(L [4,2] [3] [6,4] [(T 2 [] [10])]),(L [8,2] [] [5] []),(M 5)])),(223,(L [8,4,3] [13] [26,4] [(L [4,1] [5,2,3] [10,4,6,4] [(L [3] [] [4] [(R1 22 [] 2)])]),(L [6,3] [] [4] [(L [3] [] [6] [(R1 2 [] 0)]),(M 10),(T 6 [] [6])]),(L [8,1] [2,3] [4,6,4] []),(L [8,6] [] [5] [(M 10)])]),(L [8,4,2] [13] [26,4] [(L [4,2] [3] [6,4] [(T 2 [] [4])]),(L [6,2] [] [4] [(T 2 [] [6]),(M 5)]),(L [8,2] [] [4] [])])),(227,(M 6),(L [8,4,2] [17] [34,4] [(L [6,2] [] [4] [(T 2 [] [4]),(M 55)]),(L [6,2] [] [4] [(T 2 [] [14]),(M 5)]),(L [8,2] [2] [4,6] [])])),(229,(M 10),(L [8,4,2] [5] [10,4] [(L [4,2] [] [14] [(T 2 [] [6])]),(L [6,2] [] [4] [(T 2 [] [4]),(M 5)]),(L [8,2] [] [26] [])])),(233,(M 18),(L [8,4,2] [2] [4,6] [(L [4,2] [2] [4,10] [(T 2 [] [6])]),(L [6,2] [] [5] [(T 2 [] [6]),(M 5)]),(L [8,2] [] [4] [])])),(239,(M 30),(L [8,6,2] [] [4] [(L [4,2] [2] [4,34] [(T 2 [] [4])]),(L [6,2] [] [5] [(T 2 [] [4]),(M 5)]),(L [8,2] [] [5] []),(M 5)])),(241,(M 242),(L [8,4,2] [5] [10,4] [(L [4,2] [] [22] [(T 2 [] [4])]),(L [6,2] [] [4] [(T 2 [] [4]),(M 5)]),(L [8,2] [] [5] [])])),(251,(M 18),(L [6,4,2] [2,5] [4,10,4] [(L [4,2] [] [6] [B]),(L [6,2] [3] [6,4] [])])),(257,(M 6),(L [6,4,2] [2,5] [4,10,4] [(L [4,2] [2] [4,10] [B]),B])),(263,(M 66),(L [10,6,2] [] [5] [(L [4,2] [] [14] [B]),(L [4,2] [] [6] [B]),(L [4,2] [] [4] [B]),B,(M 5)])),(269,(M 90),(L [8,4,2] [] [4] [(L [6,2] [] [5] [B,(M 55)]),(L [6,2] [] [5] [B,(M 5)]),B])),(271,(L [6,4,1] [3,2,5] [6,4,10,4] [(L [4,3] [] [4] [B,(T 4 [] [5])]),B]),(L [6,4,2] [2,5] [4,10,4] [(L [4,2] [] [4] [B]),B])),(277,(L [6,4,1] [2,3] [4,6,4] [B,B]),(L [6,4,2] [3] [6,4] [B,B])),(281,(M 6),(L [8,6,2] [] [4] [B,(L [6,2] [] [5] [B,(M 5)]),B,(M 5)])),(283,B,B)]) A A) A A) A A)) A A A A))
private def c2 : Cert := (R2 521 [(19,A,A),(23,A,A),(29,A,A),(31,A,A),(37,A,A),(41,A,A),(43,A,A),(47,A,A),(53,A,A),(59,(M 30),A),(61,(X [5,4,2,1] [(M 10)]),(X [5,4,2,2] [(M 10)])),(67,(M 34),(X [5,4,2,2] [(M 10)])),(71,(M 18),(X [5,4,2,2] [(M 10)])),(73,(X [5,4,2,1] [(M 10)]),(X [5,4,2,2] [(M 10)])),(79,(M 10),(X [5,4,2,2] [(M 10)])),(83,(M 6),(X [5,4,2,2] [(M 10)])),(89,(M 90),(X [5,4,2,2] [(M 10)])),(97,(X [5,4,2,1] [(M 10)]),(X [5,4,2,2] [(M 10)])),(101,(M 102),(X [5,4,2,2] [(M 10)])),(103,(X [5,4,2,1] [(M 10)]),(X [5,4,2,2] [(M 10)])),(107,(M 54),(X [5,4,2,2] [(M 10)])),(109,(M 10),(X [5,4,2,2] [(M 10)])),(113,(M 6),(X [5,4,2,2] [(M 10)])),(127,(X [5,4,2,1] [B]),(X [5,4,2,2] [B])),(131,(M 6),(X [5,4,2,2] [B])),(137,(M 6),(X [5,4,2,2] [B])),(139,(M 10),(X [5,4,2,2] [B])),(149,(M 150),(X [5,4,2,2] [B])),(151,(X [5,4,2,1] [B]),(X [5,4,2,2] [B])),(157,(X [5,4,2,1] [B]),(X [5,4,2,2] [B])),(163,(X [5,4,2,1] [B]),(X [5,4,2,2] [B])),(167,(M 6),(X [5,4,2,2] [B])),(173,(M 6),(X [7,4,2,2] [B,(X [6,2,2] [(X [4,2] [(L [4] [] [4] [(R1 2 [] 2)])])])])),(179,(M 90),(X [7,4,2,2] [B,(X [6,2,2] [(L [8,4] [] [86] [(T 2 [5,2,11,2] [10,4,22,4,6]),(L [4] [2] [4,6] [(R1 2 [] 2)]),(L [4] [] [4] [(R1 2 [] 31)]),(T 8 [] [4])])])])),(181,(X [7,4,2,1] [B,(X [6,2,1] [(L [6,3] [41] [82,4] [(L [3] [] [14] [(R1 2 [] 3)]),(L [3] [] [4] [(R1 2 [] 29)]),(T 6 [3] [6,4])])])]),(X [7,4,2,2] [B,(X [6,2,2] [(L [6,4] [41] [82,4] [(L [4] [] [14] [(M 6)]),(L [4] [] [4] [(M 6)]),(M 6)])])])),(191,(M 6),(X [7,4,2,2] [B,(L [14,8,4] [] [4] [(L [6,2] [2] [4,6] [(T 2 [] [5]),(T 2 [2] [4,6])]),(L [6,4] [2] [4,6] [(L [4] [] [5] [(R1 2 [] 7)]),(L [4] [] [4] [(R1 2 [] 2)]),(T 6 [19] [38,4])]),(L [8,4] [] [4] [(T 2 [2,3] [4,6,4]),(L [4] [] [4] [(R1 2 [] 5)]),(L [4] [] [4] [(R1 2 [] 2)]),(T 8 [] [6])]),(L [6,4] [2] [4,6] [(L [4] [] [5] [(R1 2 [] 2)]),(L [4] [] [6] [(R1 2 [] 2)]),(T 6 [2,47] [4,94,4])]),(L [8,4] [] [5] [(L [4] [] [5] [(R1 2 [] 7)]),(L [4] [] [82] [(R1 2 [] 0)]),(L [4] [] [4] [(R1 2 [] 3)]),(T 8 [] [4])]),(L [14,4] [] [5] [(T 14 [] [14])]),(L [14,4] [] [82] [(T 14 [] [4])]),(L [14,4] [] [4] [(T 14 [] [6])]),(L [14,8] [] [5] [])])])),(193,(X [7,4,2,1] [B,(L [10,6,3] [2,5,2] [4,10,4,34] [(L [4,3] [2,5,2,3] [4,10,4,6,4] [(L [3] [] [10] [(R1 2 [] 3)]),(T 4 [2,3,2,43] [4,6,4,86,4])]),(L [6,3] [] [146] [(L [3] [] [10] [(R1 2 [] 3)]),(L [3] [] [14] [(R1 2 [] 3)]),(T 6 [7] [14,4])]),(L [8,3] [] [5] [(L [3] [] [4] [(R1 2 [] 3)]),(L [3] [] [6] [(R1 2 [] 5)]),(L [5] [] [5] [(R1 2 [] 2),(M 250)]),(T 8 [] [10])]),(L [10,3] [] [4] [(T 10 [] [4])]),(L [10,3] [2,11] [4,22,4] [(T 10 [2] [4,34])]),(L [12,6] [] [5] [(T 6 [] [5])])])]),(X [7,4,2,2] [B,(L [10,6,4] [5,2] [10,4,34] [(L [6,2] [3] [6,4] [(T 2 [] [10]),(L [4] [] [4] [(M 6)])]),(L [6,4] [] [146] [(T 2 [2] [4,10]),(L [4] [] [14] [(M 6)]),(M 6)]),(L [6,4] [] [5] [(T 2 [31] [62,4]),(L [4] [] [6] [(M 6)]),(M 6)]),(L [10,2] [2,5] [4,10,4] []),(L [10,4] [2,11] [4,22,4] [(M 6)]),(M 6)])])),(197,(M 18),(X [7,4,2,2] [B,(L [10,6,4] [2] [4,122] [(L [6,2] [] [4] [(T 2 [2] [4,38]),(T 2 [] [6])]),(L [6,2] [2,7,2] [4,14,4,6] [(T 2 [3] [6,4]),(T 2 [2,3,2] [4,6,4,14])]),(L [6,2] [2,7,2,3] [4,14,4,6,4] [(T 2 [19] [38,4]),(T 2 [47,2,3] [94,4,6,4])]),(L [10,2] [2] [4,6] []),(L [10,2] [71,2,3,2] [142,4,6,4,10] []),(L [12,6] [] [4] [(T 6 [] [5])])])])),(199,(M 50),(X [7,4,2,2] [B,(L [10,6,4] [] [5] [(L [4,2] [3,2,7] [6,4,14,4] [(T 2 [2] [4,10])]),(L [6,4] [] [5] [(T 2 [7] [14,4]),(T 2 [37,2] [74,4,6]),(M 6)]),(L [6,2] [19,2] [38,4,6] [(T 2 [] [4]),(T 2 [2,3] [4,6,4])]),(L [10,2] [2] [4,6] []),(L [10,4] [] [4] [(M 6)]),(M 6)])])),(211,(X [7,4,2,1] [B,(L [8,4,3] [2,3,2,5] [4,6,4,10,4] [(L [4,3] [3] [6,4] [(L [3] [] [4] [(R1 2 [] 2)]),(T 4 [3] [6,4])]),(L [4,3] [2,3] [4,6,4] [(L [3] [] [6] [(R1 2 [] 0)]),(T 4 [2,3,2] [4,6,4,34])]),(L [8,3] [7] [14,4] [(T 8 [3] [6,4])]),(L [10,6] [] [6] [(L [6] [] [5] [(R1 2 [] 0)]),(T 10 [] [4])])])]),(X [7,4,2,2] [B,(L [8,6,2] [2,5] [4,10,4] [(L [4,2] [3] [6,4] [(T 2 [] [4])]),(L [4,2] [2,3] [4,6,4] [(T 2 [] [6])]),(L [8,2] [7] [14,4] []),(L [10,2] [] [6] [(L [4] [] [4] [(M 6)])])])])),(223,(X [7,6,2,1] [B,(L [8,4,3] [2,13] [4,26,4] [(L [4,3] [] [58] [(L [3] [] [4] [(R1 2 [] 7)]),(T 4 [] [5])]),(L [4,3] [17] [34,4] [(L [3] [] [4] [(R1 2 [] 2)]),(T 4 [7] [14,4])]),(L [8,3] [] [4] [(T 8 [] [4])]),(L [10,6] [] [5] [(L [6] [] [4] [(R1 2 [] 0)]),(T 10 [] [4])])]),(X [7,4,1] [(X [9,1] [(M 10)])])]),(X [7,6,2,2] [B,(L [8,4,2] [2,13] [4,26,4] [(L [4,2] [2] [4,58] [(T 2 [] [4])]),(L [4,2] [17] [34,4] [(L [4] [] [4] [(M 6)])]),(L [8,2] [] [4] [])]),(X [7,4,2] [(X [9,2] [(M 10)])])])),(227,(M 6),(X [7,6,2,2] [B,(L [6,4,2] [2,3,2,11,2,5,2,3,2,17,2,7,2,3,2,5,2] [4,6,4,22,4,10,4,6,4,34,4,14,4,6,4,10,4,62] [(L [4,2] [] [5] [(T 2 [] [6])]),(L [8,2] [] [4] [(T 2 [] [5])])]),(X [7,4,2] [(L [19,4] [2] [4,10] [(M 10),(L [4] [] [14] [(R1 2 [] 0)]),(M 10),(L [4] [] [4] [(R1 2 [] 2)]),(M 170),(L [4] [] [4] [(R1 2 [] 2)]),(T 19 [2] [4,134])])])])),(229,(M 10),(X [7,6,2,2] [B,(L [8,6,2] [2] [4,14] [(L [4,2] [2] [4,6] [(T 2 [] [34])]),(L [4,2] [2] [4,6] [(T 2 [] [4])]),(L [8,2] [3] [6,4] []),(L [10,2] [] [4] [(T 2 [] [5])])]),(X [9,4,2] [(M 10),(L [15,4] [2,83,2,3,2,5] [4,166,4,6,4,10,4] [(L [4] [] [4] [(M 6)]),(M 10),(L [4] [] [5] [(M 6)]),(M 6)])])])),(233,(M 18),(X [7,6,2,2] [B,(L [8,6,2] [2] [4,10] [(L [4,2] [] [4] [(T 2 [] [6])]),(L [4,2] [7] [14,4] [(T 2 [] [4])]),(L [8,2] [] [58] []),(L [10,2] [] [4] [(T 2 [] [5])])]),(X [9,4,2] [(M 10),(L [15,2] [2,5,2,17,2,3] [4,10,4,34,4,6,4] [(T 2 [7,2,3] [14,4,6,4]),(M 10),(T 2 [2,5,2,3] [4,10,4,6,4])])])])),(239,(M 30),(X [7,6,4,2] [B,(L [8,4,2] [11] [22,4] [(L [4,2] [] [14] [(T 2 [] [4])]),(L [4,2] [3] [6,4] [(T 2 [] [14])]),(L [8,2] [] [6] [])]),(L [17,6,4] [2,3,2] [4,6,4,194] [(M 10),(L [8,4] [] [5] [(L [4] [] [5] [(R1 2 [] 2)]),(L [4] [] [4] [(R1 2 [] 0)]),(L [4] [] [4] [(R1 2 [] 3)]),(T 8 [] [6])]),(M 10),(L [8,4] [] [4] [(T 2 [3] [6,4]),(L [4] [] [4] [(R1 2 [] 2)]),(L [4] [] [5] [(R1 2 [] 2)]),(T 8 [] [5])]),(M 170),(L [17,2] [2,61] [4,122,4] []),(L [17,4] [5,2] [10,4,6] [(L [19] [] [6] [(R1 2 [] 0)])]),(L [17,6] [19,2,3] [38,4,6,4] [])]),(X [9,6,2] [(M 10)])])),(241,(X [7,6,4,1] [B,(L [8,4,3] [3] [6,4] [(L [4,3] [] [4] [(L [3] [] [10] [(R1 2 [] 0)]),(T 4 [] [4])]),(L [4,3] [] [4] [(L [3] [] [4] [(R1 2 [] 2)]),(T 4 [] [5])]),(L [10,3] [] [5] [(L [3] [] [4] [(R1 2 [] 3)]),(T 10 [] [6])]),(L [8,4] [2] [4,6] [])]),(L [15,6,3] [2,5,2,3] [4,10,4,6,4] [(M 10),(L [6,3] [] [6] [(L [3] [] [5] [(R1 2 [] 2)]),(L [3] [] [4] [(R1 2 [] 5)]),(T 6 [] [62])]),(M 10),(L [6,3] [] [4] [(L [3] [] [10] [(R1 2 [] 2)]),(L [3] [] [4] [(R1 2 [] 2)]),(T 6 [] [4])]),(L [15,3] [7] [14,4] [(T 15 [] [4])]),(L [17,3] [] [6] [(M 170),(T 17 [] [4])]),(L [17,6] [] [4] [(M 170)])]),(X [9,6,3] [(M 10),(X [11,6] [(X [8] [(R1 2 [] 5)])])])]),(X [7,6,4,2] [B,(L [8,4,2] [3] [6,4] [(L [4,2] [] [4] [(T 2 [] [10])]),(L [4,2] [] [4] [(L [4] [] [4] [(M 6)])]),(L [10,2] [] [5] [(T 2 [] [4])])]),(L [15,6,4] [2,5,2,3] [4,10,4,6,4] [(M 10),(L [6,2] [7,2,3,2,47,2,5,2] [14,4,6,4,94,4,10,4,6] [(T 2 [] [5]),(T 2 [2,59,2,11,2,3,2,5] [4,118,4,22,4,6,4,10,4])]),(M 10),(L [6,4] [] [4] [(T 2 [2] [4,10]),(L [4] [] [4] [(M 6)]),(M 6)]),(L [15,2] [7] [14,4] []),(L [17,4] [] [6] [(M 170),(M 6)]),(M 6)]),(X [9,6,2] [(M 10)])])),(251,(M 18),(X [9,6,4,2] [B,(L [8,4,2] [] [4] [(L [4,2] [] [5] [(T 2 [] [4])]),(L [4,2] [2] [4,6] [(T 2 [] [4])]),(L [8,2] [23] [46,4] [])]),(M 10),(L [15,6,4] [] [5] [(L [6,4] [] [5] [(T 2 [2] [4,6]),(L [4] [] [5] [(R1 2 [] 2)]),(T 6 [] [4])]),(M 10),(L [6,4] [] [4] [(L [4] [] [4] [(R1 2 [] 0)]),(T 2 [23] [46,4]),(T 6 [] [5])]),(L [15,2] [2] [4,10] []),(L [15,2] [2] [4,26] []),(L [15,6] [] [4] [])]),(L [15,10,2] [3,2,31,2,13,2,3] [6,4,62,4,26,4,6,4] [(L [10,2] [2,7,2,3] [4,14,4,6,4] [(T 2 [2,17] [4,34,4]),(L [4] [] [6] [(R1 2 [] 5)])]),(M 10),(L [10,2] [3,2,5,2,73,2] [6,4,10,4,146,4,6] [(T 2 [2,3,2] [4,6,4,62]),(T 2 [2,3,2,5] [4,6,4,10,4])]),(L [15,4] [3] [6,4] [(L [17] [] [4] [(M 170)])]),(L [15,4] [2,17] [4,34,4] [(T 15 [2,3] [4,6,4])])])])),(257,(M 6),(L [19,12,8,4] [19,2,13,2] [38,4,26,4,6] [B,(L [8,4,2] [] [4] [(L [4,2] [] [6] [(T 2 [] [5])]),(L [4,2] [] [4] [(T 2 [] [14])]),(L [8,2] [] [4] [])]),(M 10),(L [12,6,4] [2,3,2,89] [4,6,4,178,4] [(L [6,2] [2] [4,34] [(T 2 [] [14]),(T 2 [] [5])]),(L [6,2] [5,2,3,2,79,2,149,2,3,2,5,2,53,2,3,2,7,2,97,2,3,2,13,2,17,2,3,2,71,2] [10,4,6,4,158,4,298,4,6,4,10,4,106,4,6,4,14,4,194,4,6,4,26,4,34,4,6,4,142,4,10] [(T 2 [2] [4,6]),(L [4] [] [158] [(R1 2 [] 2)])]),(L [6,4] [3,2] [6,4,10] [(L [4] [] [4] [(R1 2 [] 0)]),(L [4] [] [6] [(R1 2 [] 2)]),(T 6 [2,3] [4,6,4])]),(L [8,4] [] [4] [(L [4] [] [5] [(R1 2 [] 2)]),(L [4] [] [4] [(R1 2 [] 0)]),(L [4] [] [5] [(R1 2 [] 0)]),(T 8 [] [10])]),(L [12,4] [] [4] [(T 12 [] [5])]),(L [12,4] [2] [4,226] [(L [14] [] [4] [(R1 2 [] 0)])]),(L [12,6] [2,7,2] [4,14,4,6] [])]),(M 10),(L [12,6,4] [2,109,2,37,2,3,2,127,2,5,2,3,2,13] [4,218,4,74,4,6,4,254,4,10,4,6,4,26,4] [(L [4,2] [2,5,2,13,2,3] [4,10,4,26,4,6,4] [(T 2 [] [10])]),(L [6,4] [3,2,5] [6,4,10,4] [(T 2 [2] [4,38]),(L [4] [] [4] [(R1 2 [] 2)]),(T 6 [11,2,3] [22,4,6,4])]),(L [6,4] [13,2,3,2,7,2,5,2,3] [26,4,6,4,14,4,10,4,6,4] [(T 2 [2] [4,10]),(L [4] [] [6] [(R1 2 [] 2)]),(L [8] [] [4] [(R1 2 [] 17)])]),(L [6,4] [2,5,2,3,2,11,2,7,2,3] [4,10,4,6,4,22,4,14,4,6,4] [(T 2 [2] [4,10]),(L [4] [] [4] [(R1 2 [] 2)]),(L [8] [] [4] [(R1 2 [] 7)])]),(L [12,2] [2,5] [4,10,4] []),(L [12,4] [7,2,3] [14,4,6,4] [(L [14] [] [4] [(R1 2 [] 7)])]),(L [14,8] [] [4] [(L [8] [] [6] [(R1 2 [] 19)]),(T 14 [] [4])])]),(M 170),(L [14,8,4] [] [4] [(L [4,2] [2,13,2,3,2,11] [4,26,4,6,4,22,4] [(T 2 [] [4])]),(L [6,4] [13,2,5] [26,4,10,4] [(T 2 [2] [4,6]),(L [4] [] [5] [(R1 2 [] 2)]),(T 6 [2,3,2] [4,6,4,86])]),(L [10,4] [] [4] [(T 2 [2] [4,94]),(L [4] [] [4] [(R1 2 [] 2)]),(L [4] [] [4] [(R1 2 [] 2)]),(L [4] [] [5] [(R1 2 [] 2)]),(T 10 [] [4])]),(L [8,4] [] [5] [(T 2 [2] [4,6]),(L [4] [] [4] [(R1 2 [] 2)]),(L [4] [] [4] [(R1 2 [] 3)]),(T 8 [] [10])]),(L [8,4] [] [5] [(T 2 [3] [6,4]),(L [4] [] [6] [(R1 2 [] 2)]),(L [4] [] [4] [(R1 2 [] 3)]),(T 8 [] [5])]),(L [14,2] [3] [6,4] []),(L [14,4] [] [4] [(T 14 [] [4])]),(L [14,4] [] [4] [(T 14 [] [4])]),(L [14,8] [] [4] [])]),(L [19,4,2] [2,13,2,3,2,11] [4,26,4,6,4,22,4] [(L [19,2] [] [4] [])]),(L [19,6,4] [2,3,2] [4,6,4,314] [(L [19,2] [2] [4,6] []),(L [19,4] [2] [4,6] [(T 19 [] [6])]),(L [19,6] [43,2,11,2] [86,4,22,4,6] [])]),(L [19,8,4] [163] [326,4] [(L [19,2] [2] [4,94] []),(L [19,4] [2] [4,14] [(T 19 [2] [4,62])]),(L [21,4] [] [4] [(M 50),(T 21 [] [4])]),(L [19,8] [3] [6,4] [])]),(L [23,8,4] [] [4] [(M 50),(L [10,4] [] [4] [(T 2 [2,3] [4,6,4]),(L [4] [] [4] [(R1 2 [] 2)]),(L [4] [] [5] [(R1 2 [] 2)]),(L [4] [] [5] [(R1 2 [] 2)]),(T 10 [] [4])]),(L [23,2] [2,3] [4,6,4] []),(L [23,4] [] [4] [(T 23 [] [4])]),(L [23,4] [] [5] [(T 23 [] [4])]),(L [23,8] [] [4] [])]),(L [19,12,2] [3] [6,4] []),(L [19,12,4] [2,37,2,3] [4,74,4,6,4] [(L [19,12] [3,2,139,2,13] [6,4,278,4,26,4] [])]),(L [19,14,4] [2] [4,10] [(L [25,4] [] [4] [(M 50),(L [4] [] [5] [(R1 2 [] 0)]),(M 10),(T 25 [] [4])]),(L [19,14] [2] [4,26] [])]),(L [19,12,8] [29,2,97,2] [58,4,194,4,6] [])])),(263,(M 6),(L [13,10,6,2] [3,2,19,2,11,2,3,2,73,2,5,2,3,2,7,2,17,2,3,2,5,2,61,2,3,2] [6,4,38,4,22,4,6,4,146,4,10,4,6,4,14,4,34,4,6,4,10,4,122,4,6,4,22] [B,(L [8,6,2] [] [5] [(L [4,2] [] [4] [(T 2 [] [4])]),(L [4,2] [] [22] [(T 2 [] [6])]),(L [8,2] [] [10] []),(L [10,2] [] [5] [(T 2 [] [4])])]),(M 10),(L [12,8,4] [] [4] [(L [4,2] [2,31,2,3] [4,62,4,6,4] [(T 2 [2] [4,6])]),(L [6,4] [] [5] [(T 2 [] [6]),(L [4] [] [4] [(R1 2 [] 5)]),(T 6 [] [4])]),(L [6,4] [] [5] [(T 2 [] [14]),(L [4] [] [4] [(R1 2 [] 2)]),(T 6 [] [6])]),(L [6,2] [2,7,2,3] [4,14,4,6,4] [(T 2 [17] [34,4]),(L [4] [] [10] [(R1 2 [] 0)])]),(L [12,2] [] [4] []),(L [12,2] [2,3,2,5] [4,6,4,10,4] []),(L [12,4] [] [5] [(T 12 [] [4])]),(L [12,8] [] [4] [])]),(M 10),(L [13,6,2] [3] [6,4] [(L [13,2] [] [4] []),(L [15,2] [] [4] [(T 2 [] [5])])]),(L [15,6,2] [3,2,19,2,7,2] [6,4,38,4,14,4,6] [(L [6,2] [5,2,3,2] [10,4,6,4,14] [(T 2 [5] [10,4]),(L [4] [] [6] [(R1 2 [] 5)])]),(L [15,2] [3] [6,4] []),(L [15,2] [2,61,2,3,2,17] [4,122,4,6,4,34,4] [])]),(L [17,6,4] [] [4] [(L [6,4] [] [10] [(T 2 [41] [82,4]),(T 2 [3,2,11,2,13] [6,4,22,4,26,4]),(T 6 [] [4])]),(M 170),(L [17,2] [7] [14,4] []),(L [17,4] [] [6] [(T 17 [] [4])]),(L [17,6] [] [26] [])]),(L [13,10,2] [2,5,2] [4,10,4,34] []),(L [15,10,4] [3,2,5,2] [6,4,10,4,62] [(L [12,4] [] [4] [(L [4] [] [4] [(R1 2 [] 0)]),(T 12 [] [22])]),(L [17,12] [] [4] [(M 170),(T 17 [] [4])])])])),(269,(M 270),(L [15,10,6,2] [2,5,2] [4,10,4,6] [B,(L [6,4,2] [5,2,7,2,3] [10,4,14,4,6,4] [(L [4,2] [] [6] [(T 2 [] [5])]),(L [8,2] [] [4] [(T 2 [] [4])])]),(M 10),(L [10,6,2] [2,29] [4,58,4] [(L [4,2] [7,2] [14,4,6] [(T 2 [] [4])]),(L [6,4] [] [5] [(T 2 [] [10]),(L [4] [] [5] [(R1 2 [] 2)]),(T 6 [] [4])]),(L [6,4] [] [4] [(T 2 [] [4]),(T 2 [3] [6,4]),(T 6 [] [5])]),(L [10,2] [] [6] []),(L [10,2] [2,3] [4,6,4] [])]),(M 10),(L [10,6,2] [11,2] [22,4,6] [(L [4,2] [3,2,37] [6,4,74,4] [(T 2 [] [4])]),(L [6,4] [] [4] [(T 2 [2] [4,6]),(T 2 [2] [4,14]),(T 6 [] [5])]),(L [6,2] [2] [4,14] [(T 2 [] [5]),(L [4] [] [4] [(R1 2 [] 2)])]),(L [10,4] [] [5] [(T 10 [] [4])]),(L [10,2] [2,59] [4,118,4] [])]),(L [15,4,2] [2,37,2] [4,74,4,26] [(L [15,2] [] [4] [])]),(L [15,6,4] [] [5] [(L [15,2] [3] [6,4] []),(L [15,2] [2,5] [4,10,4] []),(L [15,6] [3] [6,4] [])]),(L [15,6,4] [2] [4,38] [(L [15,2] [2] [4,6] []),(L [15,2] [3,2] [6,4,14] []),(L [15,6] [] [5] [])]),(L [15,10,2] [] [4] []),(L [15,10,2] [5,2] [10,4,14] [])])),(271,(M 34),(L [15,10,6,2] [3,2] [6,4,34] [B,(L [6,4,2] [2,5,2,3,2] [4,10,4,6,4,34] [(L [6,2] [] [4] [(T 2 [] [22]),(T 2 [] [5])]),(L [10,2] [] [4] [(T 2 [] [4]),(T 2 [] [5])])]),(M 10),(L [10,6,4] [] [4] [(L [4,2] [3,2] [6,4,10] [(T 2 [] [4])]),(L [6,4] [] [4] [(L [4] [] [5] [(M 6)]),(T 2 [2] [4,6]),(M 6)]),(L [6,2] [2] [4,10] [(T 2 [] [6]),(T 2 [3] [6,4])]),(L [10,2] [5] [10,4] []),(L [10,4] [] [5] [(M 6)]),(M 6)]),(M 10),(L [10,6,4] [] [5] [(L [6,2] [] [5] [(T 2 [] [4]),(T 2 [] [22])]),(L [6,2] [2] [4,6] [(T 2 [] [4]),(T 2 [7] [14,4])]),(L [6,4] [] [4] [(T 2 [] [6]),(T 2 [2] [4,46]),(M 6)]),(L [10,2] [] [4] []),(L [10,2] [3] [6,4] []),(M 6)]),(L [15,6,2] [] [4] [(L [15,2] [] [4] []),(L [15,2] [] [22] [])]),(L [15,6,4] [2] [4,38] [(L [15,2] [] [6] []),(L [17,4] [] [4] [(M 170),(M 6)]),(M 6)]),(L [17,6,4] [] [5] [(M 170),(L [17,2] [2] [4,10] []),(L [17,2] [3] [6,4] []),(M 6)]),(L [17,12,4] [] [4] [(M 170),(L [17,2] [] [5] []),(M 6)]),(L [15,10,4] [2] [4,6] [(M 6)])])),(277,(L [15,10,6,3] [] [4] [B,(L [8,6,3] [] [5] [(L [6,3] [] [5] [(T 1 [3,2,5] [6,4,10,4]),(L [3] [] [4] [(R1 2 [] 0)]),(T 6 [] [5])]),(L [4,3] [] [4] [(T 1 [2,17,2,23] [4,34,4,46,4]),(T 4 [19] [38,4])]),(L [8,1] [2,3,2,13] [4,6,4,26,4] []),(L [10,3] [] [5] [(T 1 [2,5,2,3] [4,10,4,6,4]),(T 10 [] [4])]),(L [8,6] [] [4] [])]),(M 10),(L [10,6,3] [] [6] [(L [4,3] [3,2] [6,4,38] [(L [3] [] [4] [(R1 2 [] 5)]),(L [6] [] [6] [(R1 2 [] 0)])]),(L [4,3] [2,43,2,5,2,3] [4,86,4,10,4,6,4] [(L [3] [] [10] [(R1 2 [] 2)]),(L [6] [] [34] [(R1 2 [] 5)])]),(L [4,3] [2,3,2,19,2,5,2,3] [4,6,4,38,4,10,4,6,4] [(L [3] [] [4] [(R1 2 [] 2)]),(L [6] [] [6] [(R1 2 [] 3)])]),(L [10,3] [] [5] [(T 10 [] [4])]),(L [10,3] [5] [10,4] [(T 10 [] [5])]),(L [10,6] [] [4] [])]),(M 10),(L [12,6,3] [] [4] [(L [6,3] [] [5] [(L [3] [] [4] [(R1 2 [] 11)]),(L [3] [] [4] [(R1 2 [] 2)]),(T 6 [] [4])]),(L [6,3] [] [22] [(L [3] [] [4] [(R1 2 [] 2)]),(L [3] [] [4] [(R1 2 [] 2)]),(T 6 [] [6])]),(L [4,3] [2,17,2,3,2,7,2,5] [4,34,4,6,4,14,4,10,4] [(L [3] [] [4] [(R1 2 [] 29)]),(L [6] [] [10] [(R1 2 [] 2)])]),(L [6,3] [] [5] [(L [3] [] [4] [(R1 2 [] 5)]),(L [3] [] [4] [(R1 2 [] 3)]),(T 6 [] [4])]),(L [12,3] [] [4] [(T 12 [] [10])]),(L [12,3] [] [4] [(T 12 [] [6])]),(L [12,6] [] [5] [])]),(L [15,6,3] [] [4] [(L [15,3] [] [4] [(T 15 [] [22])]),(L [15,3] [] [4] [(T 15 [] [10])]),(L [15,6] [] [4] [])]),(L [15,6,3] [] [6] [(L [15,3] [] [6] [(T 15 [] [6])]),(L [15,3] [] [4] [(T 15 [] [4])]),(L [15,6] [] [10] [])]),(L [15,4,3] [2,3,2,7,2,5,2,3] [4,6,4,14,4,10,4,6,4] [(L [15,3] [] [6] [(T 15 [] [4])]),(L [15,6] [] [5] [(T 15 [] [4])])]),(L [15,10,3] [] [5] [(L [15,10] [] [4] [])]),(L [15,10,3] [] [4] [(L [15,10] [] [10] [])]),(L [15,10,6] [2] [4,22] [])]),(L [15,10,6,2] [3] [6,4] [B,(L [8,6,2] [] [5] [(L [6,4] [] [5] [(T 2 [] [4]),(T 2 [] [4]),(M 6)]),(L [4,2] [] [4] [(T 2 [] [4])]),(L [8,2] [] [4] []),(L [10,2] [] [5] [(T 2 [] [4])])]),(M 10),(L [10,6,2] [2] [4,6] [(L [4,2] [3,2] [6,4,38] [(T 2 [] [4])]),(L [4,2] [3,2,43,2,5,2,3] [6,4,86,4,10,4,6,4] [(T 2 [] [10])]),(L [4,2] [2,3,2,19,2,5,2,3] [4,6,4,38,4,10,4,6,4] [(T 2 [3] [6,4])]),(L [10,2] [] [5] []),(L [10,2] [5] [10,4] [])]),(M 10),(L [12,6,4] [] [4] [(L [6,2] [] [5] [(T 2 [] [4]),(T 2 [3] [6,4])]),(L [6,2] [] [22] [(T 2 [] [4]),(T 2 [5] [10,4])]),(L [6,2] [5] [10,4] [(T 2 [] [4]),(L [4] [] [4] [(M 6)])]),(L [6,2] [] [5] [(T 2 [] [4]),(T 2 [7] [14,4])]),(L [12,2] [] [4] []),(L [12,2] [7] [14,4] []),(M 6)]),(L [15,6,2] [] [4] [(L [15,2] [] [4] []),(L [15,2] [] [4] [])]),(L [15,6,2] [2] [4,6] [(L [15,2] [] [6] []),(L [15,4] [] [4] [(M 6)])]),(L [15,4,2] [2,3,2,7,2,5,2,3] [4,6,4,14,4,10,4,6,4] [(L [15,2] [2] [4,6] [])]),(L [15,10,4] [] [5] [(M 6)]),(L [15,10,2] [5] [10,4] [])])),(281,(M 6),(L [13,10,6,2] [2,3,2] [4,6,4,94] [B,(L [8,4,2] [2] [4,14] [(L [4,2] [] [4] [(T 2 [] [10])]),(L [6,2] [] [5] [(T 2 [] [4]),(T 2 [] [4])]),(L [8,2] [] [6] [])]),(M 10),(L [10,6,2] [3] [6,4] [(L [4,2] [31] [62,4] [(T 2 [] [4])]),(L [4,2] [2,3,2,7,2,19] [4,6,4,14,4,38,4] [(T 2 [] [4])]),(L [6,2] [] [4] [(T 2 [] [6]),(T 2 [] [10])]),(L [10,2] [] [4] []),(L [10,4] [] [5] [(T 10 [] [4])])]),(M 10),(L [13,6,2] [2] [4,10] [(L [13,2] [] [4] []),(L [13,2] [] [5] [])]),(L [13,4,2] [2,31,2,11,2,3,2] [4,62,4,22,4,6,4,10] [(L [13,2] [] [58] [])]),(L [15,6,2] [] [4] [(L [6,4] [] [5] [(T 2 [] [4]),(T 2 [] [10]),(T 6 [] [4])]),(L [15,2] [2] [4,6] []),(L [15,4] [] [5] [(T 15 [] [4])])]),(L [13,10,2] [3] [6,4] []),(L [15,10,4] [] [5] [(L [10,2] [] [6] []),(L [17,12] [] [5] [(M 170),(T 17 [] [4])])])])),(283,(L [13,10,6,3] [2] [4,6] [B,(L [8,4,3] [] [4] [(L [4,1] [13,2,3] [26,4,6,4] [(L [3] [] [4] [(R1 2 [] 2)])]),(L [4,1] [2,5,2,3] [4,10,4,6,4] [(L [3] [] [5] [(R1 2 [] 2)])]),(L [8,3] [] [6] [(T 8 [] [5])]),(L [8,4] [] [4] [])]),(M 10),(L [10,6,3] [] [5] [(L [4,3] [5] [10,4] [(L [3] [] [5] [(R1 2 [] 13)]),(L [6] [] [4] [(R1 2 [] 0)])]),(L [6,3] [] [4] [(L [3] [] [4] [(R1 2 [] 0)]),(L [3] [] [4] [(R1 2 [] 2)]),(T 6 [] [4])]),(L [6,3] [] [4] [(L [3] [] [4] [(R1 2 [] 2)]),(L [3] [] [4] [(R1 2 [] 7)]),(T 6 [] [6])]),(L [10,3] [] [4] [(T 10 [] [6])]),(L [10,3] [] [6] [(T 10 [] [4])]),(L [10,6] [] [4] [])]),(M 10),(L [13,6,3] [2] [4,22] [(L [13,3] [] [4] [(T 13 [2] [4,14])]),(L [13,3] [] [5] [(T 13 [3] [6,4])]),(L [13,6] [] [10] [])]),(L [13,6,3] [3,2] [6,4,10] [(L [15,3] [] [4] [(L [3] [] [5] [(R1 2 [] 2)]),(T 15 [] [6])]),(L [15,3] [] [4] [(L [3] [] [5] [(R1 2 [] 2)]),(T 15 [3] [6,4])]),(L [15,6] [] [4] [(T 6 [] [5])])]),(L [13,6,3] [2,17] [4,34,4] [(L [13,3] [7] [14,4] [(L [15] [] [5] [(R1 2 [] 2)])]),(L [15,3] [2] [4,10] [(L [3] [] [5] [(R1 2 [] 3)]),(T 15 [] [5])]),(L [13,6] [2,3] [4,6,4] [])]),(L [13,10,3] [] [6] [(L [13,10] [2] [4,6] [])]),(L [13,10,3] [3] [6,4] [(L [13,10] [29] [58,4] [])]),(L [13,10,6] [5,2] [10,4,26] [])]),(L [15,10,6,2] [] [6] [B,(L [8,4,2] [] [4] [(L [4,2] [] [4] [(T 2 [] [4])]),(L [4,2] [] [4] [(T 2 [] [5])]),(L [8,2] [] [6] [])]),(M 10),(L [10,6,2] [] [5] [(L [4,2] [5] [10,4] [(T 2 [] [5])]),(L [6,2] [] [4] [(T 2 [] [4]),(T 2 [] [4])]),(L [6,2] [] [4] [(T 2 [] [4]),(L [4] [] [4] [(M 6)])]),(L [10,2] [] [4] []),(L [10,2] [2] [4,6] [])]),(M 10),(L [10,6,4] [] [4] [(L [6,2] [] [4] [(T 2 [] [4]),(T 2 [] [5])]),(L [6,2] [] [6] [(T 2 [] [5]),(L [4] [] [5] [(M 6)])]),(L [6,2] [] [4] [(T 2 [] [14]),(T 2 [] [5])]),(L [10,2] [2] [4,6] []),(L [10,2] [2] [4,6] []),(M 6)]),(L [15,6,2] [] [22] [(L [15,2] [] [4] []),(L [15,2] [] [5] [])]),(L [15,4,2] [2,29,2,3,2] [4,58,4,6,4,10] [(L [15,4] [] [4] [(M 6)])]),(L [15,4,2] [2,5,2,3,2,17] [4,10,4,6,4,34,4] [(L [15,2] [7] [14,4] [])]),(L [15,10,2] [] [6] []),(L [15,10,2] [] [4] [])])),(293,(M 6),(L [13,10,6,2] [3] [6,4] [B,(L [6,4,2] [2,13,2] [4,26,4,10] [(L [4,2] [] [5] [(T 2 [] [4])]),(L [6,2] [2,13,2] [4,26,4,6] [])]),(M 10),(L [10,6,2] [] [6] [(L [6,2] [] [4] [(T 2 [] [4]),(T 2 [] [5])]),(L [4,2] [11,2] [22,4,6] [(T 2 [] [5])]),(L [6,2] [] [5] [(T 2 [] [4]),(T 2 [] [4])]),(L [10,2] [] [22] []),(L [10,2] [] [4] [])]),(M 10),(L [13,4,2] [5,2] [10,4,6] [(L [13,2] [3] [6,4] [])]),(L [13,4,2] [3,2,7,2] [6,4,14,4,22] [(L [13,2] [5] [10,4] [])]),(L [15,6,4] [] [4] [(L [6,2] [] [5] [(T 2 [] [4]),(T 2 [] [4])]),(L [15,2] [] [4] []),(L [15,2] [] [10] []),(L [17,6] [] [4] [(M 170)])]),(L [13,10,2] [] [6] []),(L [15,10,2] [] [5] [(L [10,2] [] [4] [])])])),(307,(L [13,8,4,3] [2,3,2] [4,6,4,10] [B,(L [8,4,3] [] [4] [(L [4,1] [5,2] [10,4,14] [(M 614)]),(L [4,3] [] [5] [(M 614),(T 4 [] [4])]),(M 614),(L [10,6] [] [4] [(T 4 [] [5]),(T 10 [] [5])])]),(M 10),(L [8,4,3] [2,5,2] [4,10,4,6] [(L [4,3] [3] [6,4] [(M 614),(T 4 [2] [4,14])]),(L [4,3] [3] [6,4] [(M 614),(T 4 [2,5] [4,10,4])]),(M 614),(L [8,6] [2] [4,6] [(L [10] [] [4] [(R1 2 [] 0)])])]),(M 10),(L [13,4,3] [3] [6,4] [(M 614),(L [13,4] [3] [6,4] [])]),(L [13,4,3] [2,5] [4,10,4] [(M 614),(L [13,6] [] [4] [(L [15] [] [5] [(R1 2 [] 2)])])]),(M 614),(L [15,10,6] [] [5] [(L [8,4] [2,3] [4,6,4] []),(L [15,4] [2,3] [4,6,4] []),(L [15,10] [] [6] [])])]),(L [13,8,4,2] [2,3,2] [4,6,4,10] [B,(L [8,4,2] [] [4] [(L [4,2] [2] [4,14] [(M 614)]),(L [4,2] [] [5] [(M 614)]),(M 614)]),(M 10),(L [8,4,2] [2,5,2] [4,10,4,6] [(L [4,2] [3] [6,4] [(M 614)]),(L [4,2] [3] [6,4] [(M 614)]),(M 614)]),(M 10),(L [13,4,2] [3] [6,4] [(M 614)]),(L [13,4,2] [2,5] [4,10,4] [(M 614)]),(M 614)])),(311,(M 6),(L [13,8,6,2] [11] [22,4] [B,(L [6,4,2] [13,2,3] [26,4,6,4] [(L [4,2] [] [5] [(T 2 [] [4])]),(L [8,2] [] [6] [(T 2 [] [4])])]),(M 10),(L [8,4,2] [2,3] [4,6,4] [(L [6,2] [] [5] [(T 2 [] [4]),(T 2 [] [4])]),(L [4,2] [2] [4,6] [(T 2 [] [26])]),(L [8,2] [] [4] [])]),(M 10),(L [13,4,2] [2] [4,6] [(L [13,2] [] [4] [])]),(L [13,4,2] [2,5] [4,10,4] [(L [13,2] [] [14] [])]),(L [13,8,2] [2] [4,10] []),(L [13,10,2] [2] [4,22] [(L [15,2] [] [4] [(T 2 [] [5])])])])),(313,(L [13,10,6,3] [2] [4,6] [B,(L [8,4,3] [] [5] [(L [4,1] [2,5] [4,10,4] [(L [3] [] [5] [(R1 2 [] 2)])]),(L [4,1] [2,5] [4,10,4] [(L [3] [] [4] [(R1 2 [] 2)])]),(L [8,1] [3,2] [6,4,38] []),(L [8,4] [] [6] [])]),(M 10),(L [10,6,3] [] [4] [(L [4,3] [3] [6,4] [(L [3] [] [5] [(R1 2 [] 7)]),(T 4 [] [4])]),(L [4,3] [17,2] [34,4,10] [(L [3] [] [4] [(R1 2 [] 2)]),(L [6] [] [5] [(R1 2 [] 5)])]),(L [6,3] [] [5] [(L [3] [] [4] [(R1 2 [] 2)]),(L [3] [] [4] [(R1 2 [] 3)]),(T 6 [] [38])]),(L [10,3] [] [4] [(T 10 [] [6])]),(L [10,3] [] [5] [(T 10 [] [4])]),(L [10,6] [] [38] [])]),(M 10),(L [13,6,3] [] [5] [(L [13,1] [3,2,11,2,5,2,3] [6,4,22,4,10,4,6,4] []),(L [17,3] [] [5] [(T 1 [3,2,7,2,31,2,3,2,5] [6,4,14,4,62,4,6,4,10,4]),(M 170),(T 17 [] [6])]),(L [13,6] [] [4] [])]),(L [13,4,3] [2,5] [4,10,4] [(L [13,3] [] [10] [(T 13 [] [5])]),(L [13,4] [5,2] [10,4,46] [])]),(L [15,6,3] [] [4] [(L [6,3] [] [5] [(L [3] [] [6] [(R1 2 [] 3)]),(L [3] [] [4] [(R1 2 [] 2)]),(T 6 [] [4])]),(L [15,3] [] [6] [(T 15 [] [6])]),(L [15,3] [] [4] [(T 15 [] [14])]),(L [15,6] [] [4] [])]),(L [13,10,3] [] [4] [(L [13,10] [] [4] [])]),(L [13,10,3] [] [5] [(L [13,10] [7] [14,4] [])]),(L [13,10,6] [] [5] [])]),(L [13,10,6,2] [2] [4,6] [B,(L [8,4,2] [] [5] [(L [4,2] [5] [10,4] [(T 2 [] [5])]),(L [4,2] [] [4] [(T 2 [] [4])]),(L [8,2] [] [38] [])]),(M 10),(L [10,6,2] [] [4] [(L [4,2] [3] [6,4] [(T 2 [] [5])]),(L [4,2] [17,2] [34,4,10] [(T 2 [] [4])]),(L [6,2] [] [5] [(T 2 [] [4]),(T 2 [] [4])]),(L [10,2] [] [4] []),(L [10,2] [] [5] [])]),(M 10),(L [13,6,2] [] [5] [(L [13,2] [] [4] []),(L [17,4] [] [5] [(T 2 [] [4]),(M 170),(M 6)])]),(L [13,4,2] [2,5] [4,10,4] [(L [13,2] [] [10] [])]),(L [15,6,2] [] [4] [(L [6,2] [] [5] [(T 2 [] [6]),(T 2 [] [4])]),(L [15,2] [] [6] []),(L [15,2] [] [4] [])]),(L [13,10,2] [] [4] []),(L [13,10,2] [] [5] [])])),(317,(M 6),(L [13,8,4,2] [3,2,5] [6,4,10,4] [B,(L [8,4,2] [] [4] [(L [4,2] [] [5] [(T 2 [] [26])]),(L [4,2] [] [5] [(T 2 [] [14])]),(L [8,2] [] [6] [])]),(M 10),(L [10,6,4] [] [5] [(L [4,2] [] [4] [(T 2 [] [4])]),(L [4,2] [2] [4,6] [(L [4] [] [5] [(R1 2 [] 2)])]),(L [4,2] [2,5] [4,10,4] [(T 2 [] [10])]),(L [10,2] [] [4] []),(L [10,2] [] [10] []),(L [12,8] [] [5] [(T 6 [] [4]),(T 12 [] [4])])]),(M 10),(L [13,4,2] [2] [4,14] [(L [13,2] [2] [4,6] [])]),(L [15,6,4] [] [4] [(L [6,2] [] [5] [(T 2 [] [4]),(T 2 [] [4])]),(L [15,2] [] [4] []),(L [15,2] [] [4] []),(L [15,6] [] [5] [])]),(L [13,8,2] [7] [14,4] [])])),(331,(L [13,8,4,3] [2,3] [4,6,4] [B,(L [8,4,1] [2,3] [4,6,4] [(L [4,1] [2] [4,6] [(L [3] [] [5] [(R1 2 [] 2)])]),(L [4,3] [] [4] [(T 1 [2,13] [4,26,4]),(T 4 [] [4])]),(L [8,1] [2,3] [4,6,4] [])]),(M 10),(L [8,6,3] [2] [4,10] [(L [4,3] [] [4] [(T 1 [5,2,17,2,3] [10,4,34,4,6,4]),(T 4 [] [4])]),(L [4,3] [] [6] [(L [3] [] [4] [(R1 2 [] 2)]),(T 4 [2] [4,26])]),(L [8,1] [2,5,2,3,2,29,2,17] [4,10,4,6,4,58,4,34,4] []),(L [10,3] [] [4] [(L [3] [] [5] [(R1 2 [] 2)]),(T 10 [] [5])]),(L [10,6] [] [4] [(T 6 [] [5])])]),(M 10),(L [13,6,3] [] [4] [(L [13,1] [2,3,2,7] [4,6,4,14,4] []),(L [13,3] [] [5] [(T 13 [] [5])]),(L [13,6] [] [5] [])]),(L [13,6,3] [] [4] [(L [13,1] [2,29,2,17,2,3,2] [4,58,4,34,4,6,4,10] []),(L [13,3] [] [5] [(T 13 [] [4])]),(L [13,6] [] [14] [])]),(L [13,8,3] [3] [6,4] [(L [13,8] [] [4] [])]),(L [13,8,4] [3] [6,4] [])]),(L [13,8,4,2] [2,3] [4,6,4] [B,(L [6,4,2] [2,3] [4,6,4] [(L [4,2] [] [6] [(T 2 [] [5])]),(L [6,2] [2,3] [4,6,4] [])]),(M 10),(L [8,6,2] [2] [4,10] [(L [4,2] [] [4] [(T 2 [] [4])]),(L [4,2] [] [6] [(T 2 [] [4])]),(L [8,2] [] [4] []),(L [10,2] [] [4] [(T 2 [] [5])])]),(M 10),(L [15,6,2] [] [4] [(L [6,4] [] [4] [(T 2 [] [4]),(T 2 [] [5]),(M 6)]),(L [15,2] [] [4] []),(L [15,2] [] [5] [])]),(L [13,6,2] [] [4] [(L [13,2] [] [10] []),(L [13,2] [] [5] [])]),(L [13,8,2] [3] [6,4] [])])),(337,(L [13,8,6,3] [] [5] [B,(L [8,4,3] [] [4] [(L [6,3] [] [4] [(T 1 [3] [6,4]),(L [3] [] [5] [(R1 2 [] 2)]),(T 6 [] [4])]),(L [4,1] [2,3] [4,6,4] [(T 1 [2] [4,10])]),(L [8,3] [] [5] [(T 8 [] [4])]),(L [8,4] [] [4] [])]),(M 10),(L [8,4,3] [3,2] [6,4,14] [(L [4,1] [2,3,2,19,2,11] [4,6,4,38,4,22,4] [(L [3] [] [4] [(R1 2 [] 2)])]),(L [4,3] [2] [4,6] [(T 1 [2,5,2,7,2,3,2] [4,10,4,14,4,6,4,46]),(L [6] [] [4] [(R1 2 [] 0)])]),(L [8,3] [] [4] [(L [10] [] [4] [(R1 2 [] 0)])]),(L [8,6] [] [5] [(T 8 [] [4])])]),(M 10),(L [13,4,3] [] [4] [(L [13,1] [2,7,2,3] [4,14,4,6,4] []),(L [13,6] [] [5] [(T 13 [] [4])])]),(L [13,4,3] [2] [4,6] [(L [13,3] [] [5] [(T 13 [] [5])]),(L [13,4] [17] [34,4] [])]),(L [13,8,1] [2,3,2,11,2,13,2] [4,6,4,22,4,26,4,6] []),(L [15,10,3] [] [5] [(L [8,3] [] [4] [(L [10] [] [5] [(R1 2 [] 2)])]),(L [15,3] [] [4] [(T 15 [] [4])]),(L [15,10] [] [5] [])]),(L [15,10,6] [] [4] [(L [8,6] [] [5] []),(L [15,6] [] [5] [])])]),(L [13,8,6,2] [] [5] [B,(L [8,4,2] [] [4] [(L [6,2] [] [4] [(T 2 [] [4]),(T 2 [] [5])]),(L [4,2] [3] [6,4] [(T 2 [] [10])]),(L [8,2] [] [5] [])]),(M 10),(L [8,4,2] [3,2] [6,4,14] [(L [4,2] [11] [22,4] [(T 2 [] [4])]),(L [4,2] [2] [4,6] [(T 2 [] [46])]),(L [8,2] [] [4] [])]),(M 10),(L [13,4,2] [] [4] [(L [13,2] [] [4] [])]),(L [13,4,2] [2] [4,6] [(L [13,2] [] [5] [])]),(L [13,8,2] [2] [4,6] []),(L [15,10,2] [] [5] [(L [8,2] [] [4] []),(L [15,2] [] [4] [])])])),(347,(M 6),(L [13,8,6,2] [2] [4,14] [B,(L [6,4,2] [2,5,2] [4,10,4,6] [(L [6,2] [] [4] [B,(T 2 [] [5])]),(L [8,2] [] [4] [(T 2 [] [4])])]),(M 10),(L [8,4,2] [2] [4,6] [(L [6,2] [] [5] [(T 2 [] [4]),(T 2 [] [4])]),(L [4,2] [3] [6,4] [(T 2 [] [26])]),(L [8,2] [] [6] [])]),(M 10),(L [13,4,2] [3] [6,4] [(L [13,2] [2] [4,6] [])]),(L [13,4,2] [2] [4,62] [(L [13,2] [] [4] [])]),(L [13,8,2] [] [4] []),(L [13,10,2] [] [4] [(L [15,2] [] [4] [(L [4] [] [4] [(R1 2 [] 0)])])])])),(349,(M 50),(L [11,8,4,2] [5,2] [10,4,6] [B,(L [6,4,2] [3,2,7] [6,4,14,4] [(L [4,2] [] [10] [B]),(L [6,2] [2,3] [4,6,4] [])]),(M 10),(L [8,6,2] [] [4] [(L [4,2] [3] [6,4] [(T 2 [] [5])]),(L [4,2] [2] [4,14] [(T 2 [] [6])]),(L [8,2] [2] [4,14] []),(L [10,4] [] [4] [(T 2 [] [5]),(M 6)])]),(L [13,6,2] [] [5] [(M 10),(L [13,2] [] [4] []),(L [13,2] [] [4] [])]),(L [11,4,2] [2,3] [4,6,4] [(L [11,2] [2] [4,26] [])]),(L [11,8,2] [2] [4,6] [])])),(353,(M 6),(L [11,8,4,2] [2,3] [4,6,4] [B,(L [6,4,2] [2,11] [4,22,4] [(L [4,2] [] [38] [B]),(L [6,2] [3,2] [6,4,26] [])]),(M 10),(L [8,4,2] [11] [22,4] [(L [4,2] [] [14] [(T 2 [] [4])]),(L [4,2] [3] [6,4] [(T 2 [] [14])]),(L [8,2] [2] [4,6] [])]),(L [11,4,2] [2,5] [4,10,4] [(L [11,2] [2] [4,10] [])]),(L [11,4,2] [3,2,7] [6,4,14,4] [(L [13,2] [] [5] [(M 10)])]),(L [11,8,2] [19,2] [38,4,22] [])])),(359,(M 90),(L [13,8,4,2] [2] [4,14] [B,(L [6,4,2] [2,3] [4,6,4] [B,(L [6,2] [3] [6,4] [])]),(M 10),(L [6,4,2] [2,3,2,11,2,13,2,3,2,5] [4,6,4,22,4,26,4,6,4,10,4] [(L [4,2] [] [4] [(T 2 [] [5])]),(L [8,2] [] [5] [(T 2 [] [4])])]),(M 10),(L [13,4,2] [] [4] [(L [13,2] [] [5] [])]),(L [13,4,2] [] [6] [(L [13,2] [] [4] [])]),(L [13,8,2] [] [6] [])])),(367,(L [11,8,4,3] [29,2,3] [58,4,6,4] [B,(L [8,4,1] [2] [4,34] [B,(L [4,3] [] [5] [B,(T 4 [] [4])]),B]),(M 10),(L [8,4,3] [3] [6,4] [(L [4,3] [] [6] [(L [3] [] [6] [(R1 2 [] 0)]),(L [6] [] [4] [(R1 2 [] 0)])]),(L [6,3] [] [5] [(L [3] [] [6] [(R1 2 [] 0)]),(L [3] [] [4] [(R1 2 [] 19)]),(T 6 [] [4])]),(L [8,3] [] [6] [(T 8 [7] [14,4])]),(L [10,6] [] [5] [(T 4 [] [4]),(T 10 [] [4])])]),(L [11,4,3] [3] [6,4] [(L [11,1] [2,11,2] [4,22,4,6] []),(L [13,4] [] [5] [(M 10)])]),(L [11,4,3] [7,2] [14,4,10] [(L [11,3] [2] [4,46] [(L [13] [] [4] [(M 10)])]),(L [13,4] [] [5] [(M 10)])]),(L [13,8,3] [] [4] [(M 10),(L [13,8] [] [4] [])]),(L [11,8,4] [2,3] [4,6,4] [])]),(L [11,8,4,2] [29,2,3] [58,4,6,4] [B,(L [8,4,2] [] [34] [B,(L [4,2] [] [5] [B]),B]),(M 10),(L [8,4,2] [3] [6,4] [(L [4,2] [] [6] [(T 2 [] [6])]),(L [6,2] [] [5] [(T 2 [] [6]),(T 2 [] [4])]),(L [8,2] [] [6] [])]),(L [11,4,2] [3] [6,4] [(L [11,2] [2] [4,6] [])]),(L [11,4,2] [7,2] [14,4,10] [(L [11,2] [2] [4,46] [])]),(L [13,8,2] [] [4] [(M 10)])])),(373,(M 34),(L [13,8,4,2] [2] [4,6] [B,(L [8,4,2] [] [4] [B,(L [4,2] [] [4] [B]),B]),(M 10),(L [8,4,2] [] [4] [(L [4,2] [] [4] [(T 2 [] [10])]),(L [4,2] [] [4] [(T 2 [] [4])]),(L [8,2] [13] [26,4] [])]),(M 10),(L [13,4,2] [] [6] [(L [13,2] [] [4] [])]),(L [13,4,2] [2] [4,10] [(L [13,2] [] [4] [])]),(L [13,8,2] [] [4] [])])),(379,(M 10),(L [11,6,4,2] [3,2,19,2,11,2,3,2,5] [6,4,38,4,22,4,6,4,10,4] [B,B,(M 10),(L [8,4,2] [5] [10,4] [(L [4,2] [3] [6,4] [(T 2 [] [4])]),(L [4,2] [] [4] [(T 2 [] [4])]),(L [8,2] [] [4] [])]),(L [11,4,2] [3] [6,4] [(L [13,2] [] [5] [(M 10)])]),(L [13,10,2] [] [4] [(M 10),(L [13,2] [] [4] []),(L [15,2] [] [4] [(T 2 [] [5])])])])),(383,(M 6),(L [17,12,6,2] [] [4] [B,B,(M 10),(L [8,4,2] [3] [6,4] [(L [4,2] [] [26] [(T 2 [] [6])]),(L [4,2] [] [4] [(T 2 [] [4])]),(L [8,2] [] [4] [])]),(M 10),(L [8,4,2] [] [5] [(L [4,2] [] [5] [(T 2 [] [4])]),(L [6,2] [] [4] [(T 2 [] [4]),(T 2 [] [5])]),(L [8,2] [] [10] [])]),(M 170),(L [17,4,2] [] [5] [(L [17,2] [] [6] [])]),(L [17,4,2] [] [4] [(L [17,2] [] [4] [])]),(L [17,4,2] [] [5] [(L [17,2] [] [10] [])]),(L [17,6,4] [] [4] [(L [17,2] [] [10] []),(L [17,2] [] [5] []),(L [17,6] [] [5] [])]),(L [17,12,2] [] [10] []),(L [17,12,2] [] [5] [])])),(389,(M 30),(L [11,8,4,2] [5] [10,4] [B,B,(M 10),(L [8,4,2] [2] [4,22] [(L [4,2] [] [4] [(T 2 [] [4])]),(L [4,2] [] [4] [(T 2 [] [4])]),(L [8,2] [] [5] [])]),(L [13,4,2] [] [4] [(M 10),(L [13,2] [] [6] [])]),(L [13,4,2] [] [5] [(M 10),(L [15,2] [] [5] [(T 2 [] [4])])]),(L [13,8,2] [] [4] [(M 10)])])),(397,(L [11,8,4,1] [2,5,2,3] [4,10,4,6,4] [B,B,(M 10),(L [8,6,3] [] [4] [(L [4,3] [] [4] [(T 1 [2] [4,22]),(T 4 [] [4])]),(L [4,3] [] [38] [(L [3] [] [6] [(R1 2 [] 0)]),(T 4 [] [4])]),(L [8,3] [] [4] [(T 8 [] [4])]),(L [8,3] [] [5] [(T 8 [] [4])]),(L [8,6] [2] [4,14] [])]),(L [11,4,1] [7,2,11] [14,4,22,4] [(L [11,3] [] [4] [(T 11 [] [4])])]),(L [11,4,3] [3] [6,4] [(L [11,3] [3] [6,4] [(T 11 [] [5])]),(L [13,6] [] [5] [(M 10),(T 13 [] [4])])]),(L [11,8,1] [7,2,5,2] [14,4,10,4,6] [])]),(L [11,6,4,2] [3,2,23,2,5,2,3] [6,4,46,4,10,4,6,4] [B,B,(M 10),(L [8,6,2] [] [4] [(L [4,2] [] [4] [(T 2 [] [22])]),(L [4,2] [] [38] [(T 2 [] [6])]),(L [8,2] [] [4] []),(L [8,2] [] [5] [])]),(L [11,4,2] [11] [22,4] [(L [11,2] [] [4] [])]),(L [11,6,2] [3,2,7,2,5,2] [6,4,14,4,10,4,6] [])])),(401,(M 6),(L [11,8,4,2] [2,3] [4,6,4] [B,B,(M 10),(L [8,4,2] [] [34] [(L [4,2] [] [4] [(T 2 [] [14])]),(L [4,2] [] [5] [(T 2 [] [4])]),(L [8,2] [2] [4,26] [])]),(L [11,4,2] [5] [10,4] [(L [11,2] [] [10] [])]),(L [11,4,2] [2] [4,6] [(L [11,2] [] [4] [])]),(L [13,8,2] [] [5] [(M 10)])])),(409,(M 10),(L [11,8,4,2] [3] [6,4] [B,B,(M 10),(L [8,4,2] [] [4] [(L [4,2] [2] [4,6] [(T 2 [] [4])]),(L [4,2] [2] [4,6] [(T 2 [] [38])]),(L [8,2] [] [5] [])]),(L [11,4,2] [13] [26,4] [(L [13,2] [] [5] [(M 10)])]),(L [11,4,2] [3] [6,4] [(L [11,2] [] [4] [])]),(L [13,8,2] [] [5] [(M 10)])])),(419,(M 30),(L [11,8,4,2] [5] [10,4] [B,B,(M 10),(L [8,4,2] [2] [4,22] [(L [4,2] [] [6] [(T 2 [] [4])]),(L [4,2] [] [5] [(T 2 [] [5])]),(L [8,2] [] [6] [])]),(L [13,4,2] [] [4] [(M 10),(L [13,2] [] [4] [])]),(L [11,4,2] [11,2] [22,4,6] [(L [11,2] [] [4] [])]),(L [11,8,2] [2] [4,6] [])])),(421,(L [11,8,4,3] [2] [4,6] [B,B,(M 10),(L [8,4,3] [] [4] [(L [4,1] [2,13] [4,26,4] [(T 1 [2,13] [4,26,4])]),(L [4,1] [2,7,2] [4,14,4,6] [(L [3] [] [10] [(R1 2 [] 0)])]),(L [8,3] [] [5] [(T 8 [3] [6,4])]),(L [10,6] [] [4] [(T 4 [] [5]),(T 10 [] [5])])]),(L [11,4,1] [2,3,2] [4,6,4,14] [(L [11,1] [2,5] [4,10,4] [])]),(L [11,4,3] [3] [6,4] [(L [13,3] [] [5] [(M 10),(T 13 [] [5])]),(L [13,4] [] [5] [(M 10)])]),(L [11,8,1] [2,3,2] [4,6,4,10] []),(L [13,8,4] [2] [4,22] [(M 10)])]),(L [11,8,4,2] [2] [4,6] [B,B,(M 10),(L [8,4,2] [] [4] [(L [4,2] [] [4] [(T 2 [] [4])]),(L [4,2] [2] [4,6] [(T 2 [] [10])]),(L [8,2] [] [5] [])]),(L [11,4,2] [2] [4,14] [(L [11,2] [5] [10,4] [])]),(L [11,4,2] [3] [6,4] [(L [13,2] [] [5] [(M 10)])]),(L [11,8,2] [2] [4,10] [])])),(431,(M 54),(L [11,6,4,2] [7,2,5,2,3,2] [14,4,10,4,6,4,34] [B,B,(M 10),(L [8,4,2] [3] [6,4] [(L [4,2] [2] [4,6] [(T 2 [] [14])]),(L [4,2] [] [5] [(T 2 [] [4])]),(L [8,2] [] [4] [])]),(L [11,4,2] [] [5] [(L [11,2] [2] [4,22] [])]),(L [13,8,2] [] [5] [(M 10),(L [13,2] [] [14] [])])])),(433,(L [11,8,4,1] [3,2,7] [6,4,14,4] [B,B,(M 10),(L [8,6,3] [] [4] [(L [4,1] [2,5] [4,10,4] [(L [3] [] [5] [(R1 2 [] 2)])]),(L [4,3] [] [5] [(T 1 [3,2] [6,4,10]),(T 4 [] [26])]),(L [8,3] [] [6] [(T 8 [] [5])]),(L [10,3] [] [4] [(L [3] [] [5] [(R1 2 [] 3)]),(T 10 [] [6])]),(L [8,6] [] [4] [])]),(L [11,4,1] [2,3] [4,6,4] [(L [11,1] [7,2] [14,4,6] [])]),(L [13,4,3] [] [5] [(M 10),(L [13,1] [2,3] [4,6,4] []),(L [13,4] [] [5] [])]),(L [11,8,1] [2,7] [4,14,4] [])]),(L [11,8,4,2] [7] [14,4] [B,B,(M 10),(L [8,6,2] [] [4] [(L [4,2] [] [4] [(T 2 [] [5])]),(L [4,2] [] [5] [(T 2 [] [10])]),(L [8,2] [] [6] []),(L [10,2] [] [4] [(T 2 [] [5])])]),(L [11,4,2] [] [4] [(L [11,2] [2] [4,6] [])]),(L [13,4,2] [] [5] [(M 10),(L [13,2] [] [4] [])]),(L [11,8,2] [7] [14,4] [])])),(439,(M 10),(L [11,8,4,2] [13] [26,4] [B,B,(M 10),(L [8,4,2] [5] [10,4] [(L [4,2] [3] [6,4] [(T 2 [] [4])]),(L [4,2] [] [5] [(T 2 [] [4])]),(L [8,2] [] [14] [])]),(L [11,4,2] [7] [14,4] [(L [13,2] [] [4] [(M 10)])]),(L [11,4,2] [] [5] [(L [13,2] [] [5] [(M 10)])]),(L [11,8,2] [] [4] [])])),(443,(M 6),(L [11,8,4,2] [3,2] [6,4,10] [B,B,(M 10),(L [6,4,2] [2,5,2,3] [4,10,4,6,4] [(L [4,2] [] [4] [(T 2 [] [4])]),(L [6,2] [2,3,2] [4,6,4,26] [])]),(L [11,4,2] [2] [4,6] [(L [11,2] [] [6] [])]),(L [13,4,2] [] [4] [(M 10),(L [13,2] [] [10] [])]),(L [11,8,2] [] [4] [])])),(449,(M 450),(L [13,10,6,2] [] [4] [B,B,(M 10),(L [8,6,2] [] [4] [(L [4,2] [] [6] [B]),(L [4,2] [] [22] [(L [4] [] [4] [(R1 2 [] 0)])]),(L [8,2] [] [6] []),(L [10,2] [] [4] [(T 2 [] [5])])]),(M 10),(L [13,4,2] [] [5] [B]),(L [13,4,2] [] [38] [(L [13,2] [] [4] [])]),(L [15,6,2] [] [4] [(L [4,2] [] [5] [(T 2 [] [4])]),(L [15,2] [] [4] []),(L [15,2] [] [5] [])]),(L [13,10,2] [] [4] []),(L [13,10,2] [] [5] [])])),(457,(L [11,8,4,1] [2,3] [4,6,4] [B,B,(M 10),(L [8,4,1] [3,2] [6,4,10] [(L [4,1] [2] [4,10] [B]),(L [4,3] [] [4] [(T 1 [2] [4,14]),(T 4 [] [5])]),(L [8,1] [3] [6,4] [])]),(L [11,4,1] [2] [4,6] [B]),(L [11,4,1] [2,5] [4,10,4] [(L [11,1] [2,5] [4,10,4] [])]),(L [11,8,1] [11,2] [22,4,6] [])]),(L [11,8,4,2] [3] [6,4] [B,B,(M 10),(L [8,4,2] [2] [4,10] [(L [4,2] [] [10] [B]),(L [4,2] [] [4] [(T 2 [] [14])]),(L [8,2] [] [4] [])]),(L [11,4,2] [] [6] [B]),(L [11,4,2] [5] [10,4] [(L [11,2] [5] [10,4] [])]),(L [11,8,2] [2] [4,6] [])])),(461,(M 6),(L [11,8,4,2] [3] [6,4] [B,B,(M 10),(L [6,4,2] [2,5,2,3] [4,10,4,6,4] [(L [4,2] [] [26] [B]),(L [8,2] [] [5] [(T 2 [] [4])])]),(L [11,4,2] [2] [4,10] [B]),(L [13,6,2] [] [4] [(M 10),(L [13,2] [2] [4,14] []),(L [15,2] [] [4] [(T 2 [] [5])])]),(L [11,8,2] [3] [6,4] [])])),(463,(L [13,8,6,3] [] [5] [B,B,(M 10),(L [8,4,1] [2] [4,10] [(L [4,3] [] [5] [B,(T 4 [] [4])]),(L [4,1] [2] [4,6] [(L [3] [] [4] [(R1 2 [] 0)])]),(L [8,1] [2] [4,6] [])]),(M 10),(L [13,4,1] [13,2] [26,4,6] [B]),(L [13,4,1] [5,2] [10,4,6] [(L [13,1] [3] [6,4] [])]),(L [13,8,1] [2] [4,14] []),(L [13,10,3] [] [5] [(L [13,3] [] [4] [(T 13 [] [5])]),(L [13,10] [] [5] [])]),(L [13,8,6] [] [5] [])]),(L [13,8,6,2] [] [5] [B,B,(M 10),(L [8,4,2] [] [10] [(L [4,2] [] [5] [B]),(L [4,2] [] [6] [(T 2 [] [4])]),(L [8,2] [] [6] [])]),(M 10),(L [13,4,2] [2] [4,6] [B]),(L [13,4,2] [2] [4,6] [(L [13,2] [] [4] [])]),(L [13,8,2] [] [14] []),(L [13,10,2] [] [5] [(L [13,2] [] [4] [])])])),(467,(M 18),(L [11,8,4,2] [2] [4,10] [B,B,(M 10),(L [8,4,2] [13] [26,4] [B,(L [4,2] [3] [6,4] [(T 2 [] [5])]),(L [8,2] [] [4] [])]),B,(L [11,4,2] [2] [4,6] [(L [11,2] [] [5] [])]),(L [11,8,2] [2] [4,6] [])])),(479,(M 30),(L [13,8,4,2] [] [4] [B,B,(M 10),(L [8,4,2] [] [6] [B,(L [4,2] [] [14] [B]),(L [8,2] [] [6] [])]),(M 10),B,(L [13,4,2] [] [4] [(L [13,2] [] [4] [])]),(L [13,8,2] [] [34] [])])),(487,(L [9,6,4,1] [2,23,2,3,2,13,2,5,2,3] [4,46,4,6,4,26,4,10,4,6,4] [B,B,(M 10),B,B]),(L [9,6,4,2] [23,2,3,2,13,2,5,2,3] [46,4,6,4,26,4,10,4,6,4] [B,B,(M 10),B,B])),(491,(M 6),(L [9,6,4,2] [3,2,17,2,23,2,3,2] [6,4,34,4,46,4,6,4,26] [B,B,B,B,B])),(499,(M 250),(L [13,8,4,2] [] [4] [B,B,B,(L [6,4,2] [2,11,2,3] [4,22,4,6,4] [B,B]),(M 10),B,(L [13,6,2] [] [5] [B,(L [13,2] [] [4] [])]),B])),(503,(M 18),(L [9,6,4,2] [2,3,2,5,2,11,2,3] [4,6,4,10,4,22,4,6,4] [B,B,B,B,B])),(509,B,B)])
private def c3 : Cert := (S7 7 (P 11 B (P 13 B (P 17 B (M 54) (L [5,3,3,2] [] [5] [B,B,B])) (P 17 B (M 54) (L [5,3,2,2] [] [5] [B,B]))) (P 13 B (P 17 B (M 18) (L [7,2,3,2] [] [5] [B,(M 26),B])) (P 17 B (M 18) (L [7,2,2,2] [] [5] [B,(M 26)])))) (P 11 (P 13 (P 17 B (M 18) (R2 23 [(19,(L [5,2,3] [2] [4,10] [B,(L [7,4] [] [4] [(T 2 [] [5]),(L [9] [] [4] [(R1 2 [] 0)])])]),(L [5,2,2] [2] [4,10] [B]))])) (M 14) (P 17 (R2 29 [(19,(L [7,2,3] [2,7] [4,14,4] [(L [4,3] [] [5] [(L [3] [] [4] [(R1 6 [] 2)]),(T 4 [] [4])]),(M 182),(L [7,4] [] [4] [(T 7 [] [5])])]),(L [7,2,2] [2,7] [4,14,4] [(L [4,2] [] [5] [(T 2 [] [4])]),(M 182)])),(23,(L [5,2,3] [2,3] [4,6,4] [B,(L [7,4] [] [4] [(M 546),(T 7 [] [5])])]),(L [5,2,2] [2,3] [4,6,4] [B]))]) (M 18) (L [9,4,4] [] [4] [(L [2,2] [2] [4,6] []),(M 182),(L [4,4] [] [5] [(L [4] [] [5] [(R1 6 [] 2)]),(T 4 [] [4])]),(L [9,4] [] [4] [(T 9 [] [5])]),(L [9,4] [] [5] [])]))) (R2 37 [(13,(M 42),A),(17,(M 54),(X [5,3,2] [(L [3,2] [2,3] [4,6,4] [(L [4] [] [5] [(R1 6 [] 2)])]),(L [9,4] [] [6] [(M 42),(L [4] [] [4] [(R1 6 [] 2)]),(L [11] [] [5] [(M 66)])])])),(19,(L [7,3,3] [2,3,2,7,2,5,2,3,2] [4,6,4,14,4,10,4,6,4,22] [(L [3,3] [] [4] [(L [3] [] [6] [(R1 6 [] 5)]),(T 3 [] [4])]),(M 42),(L [7,3] [] [4] [(T 7 [] [6])]),(L [9,5] [] [4] [(T 3 [3] [6,4]),(T 9 [] [5])])]),(L [7,3,4] [2,3,2,7,2,5,2,3,2] [4,6,4,14,4,10,4,6,4,22] [(L [3,2] [3] [6,4] [(T 2 [] [6])]),(M 42),(L [7,2] [3] [6,4] []),(M 18)])),(23,(M 18),(L [7,3,2] [2] [4,6] [(L [3,2] [] [5] [B]),(M 42),(L [7,2] [] [4] [])])),(29,(M 18),(L [7,3,2] [] [4] [B,(M 42),(L [7,2] [] [5] [])])),(31,(L [7,3,3] [] [4] [B,B,B,(L [7,3] [] [5] [])]),(L [7,3,2] [] [4] [B,B,B]))]) (P 13 (P 17 (P 19 (P 23 (R2 37 [(29,(L [7,4,3] [] [4] [B,(M 42),(M 42),(L [7,4] [] [4] [])]),(L [7,4,2] [] [4] [B,(M 14),(M 14)])),(31,(L [7,4,3] [] [4] [B,B,(M 14),(L [7,4] [] [5] [])]),(L [7,4,2] [] [4] [B,B,(M 14)]))]) (L [7,4,3] [] [6] [(L [4,3] [] [5] [(M 42),(T 4 [] [10])]),(M 42),(M 42),(L [7,4] [] [5] [])]) (L [7,4,2] [2] [4,6] [(L [4,2] [] [5] [(M 14)]),(M 14),(M 14)])) (L [7,4,3] [2,7,2,5,2,3,2] [4,14,4,10,4,6,4,22] [(L [2,3] [2,3] [4,6,4] [(T 2 [2,7] [4,14,4])]),(M 14),(M 266),(L [9,4] [] [4] [(T 4 [] [4])])]) (L [7,4,4] [7,2,5,2,3,2] [14,4,10,4,6,4,22] [(L [2,2] [5,2,3] [10,4,6,4] []),(M 14),(M 266),(L [9,4] [2] [4,14] [(T 4 [] [5])])])) (M 18) (X [7,2,2] [(L [4,2] [2,3] [4,6,4] [(M 14)]),(M 14)])) A A)) (P 11 (P 13 (P 17 B (M 54) (R2 29 [(19,(M 114),(M 114)),(23,(M 18),(L [7,4,2] [] [4] [B,(M 42),(L [9,2] [] [4] [(L [4] [] [4] [(M 42)])])]))])) (M 42) (P 17 (R2 37 [(19,(M 114),(M 114)),(23,(L [11,4,3] [] [4] [(L [4,3] [] [5] [(M 54),(T 4 [] [4])]),(M 1638),(L [4,3] [] [5] [(M 54),(T 4 [] [5])]),(L [6,5] [] [4] [(M 54),(L [3] [] [5] [(R1 18 [] 2)]),(T 6 [] [4]),(T 6 [] [5])]),(M 54),(L [11,4] [] [4] [])]),(L [11,4,4] [] [4] [(L [4,2] [] [5] [(T 2 [] [4])]),(M 546),(L [4,4] [] [5] [(L [4] [] [4] [(M 126)]),(M 42)]),(L [6,4] [] [4] [(T 2 [] [4]),(T 2 [] [5]),(M 42)]),(L [11,2] [2] [4,6] []),(M 42)])),(29,(L [7,4,3] [] [5] [B,(M 1638),(M 54),(L [7,4] [] [4] [])]),(L [9,4,2] [] [5] [B,(M 546),(L [4,4] [] [5] [(T 2 [] [4]),(M 78)]),(L [9,2] [] [4] [])])),(31,(L [7,4,3] [] [4] [B,(M 546),(L [9,3] [] [4] [(L [3] [] [5] [(R1 18 [] 2)]),(T 9 [] [4])]),(L [11,4] [] [5] [(T 4 [] [4]),(L [6] [] [5] [(R1 6 [] 0)])])]),(L [7,4,2] [] [4] [B,(M 546),(L [9,4] [] [4] [(T 2 [] [5]),(M 54)])]))]) (M 54) (X [5,2,2] [(L [4,2] [7,2,11] [14,4,22,4] [(M 18)])]))) (M 18) (R2 53 [(13,A,A),(17,A,A),(19,(M 114),(M 114)),(23,(M 18),(X [5,2,2] [(L [4,4] [] [4] [(M 42),(M 42)])])),(29,(M 18),(L [9,4,2] [2] [4,6] [(L [4,2] [] [4] [(M 42)]),(M 42),(L [4,2] [2] [4,14] [(M 42)]),(M 42)])),(31,(L [7,4,3] [3,2,7] [6,4,14,4] [(L [4,3] [] [4] [(M 42),(T 4 [] [4])]),(M 42),(M 42),(L [7,4] [3] [6,4] [])]),(L [7,4,2] [3,2,7] [6,4,14,4] [(L [4,2] [] [4] [(M 42)]),(M 42),(M 42)])),(37,(L [9,4,3] [] [5] [B,(M 42),(L [4,3] [] [4] [(M 42),(T 4 [] [4])]),(M 42),(L [9,4] [] [6] [])]),(L [9,4,2] [] [5] [B,(M 42),(L [4,2] [] [4] [(M 42)]),(M 42)])),(41,(M 126),(L [9,4,2] [] [5] [B,(M 42),(M 246),(M 42)])),(43,(M 66),(L [7,2,2] [2,5,2] [4,10,4,6] [B,(M 42)])),(47,B,B)])) (P 11 (P 13 (P 17 (P 19 B (P 23 B (L [9,5,3,3] [] [5] [B,B,B,B,B,B]) (L [9,5,3,4] [] [5] [B,B,B,B,B,B])) (P 23 B (L [9,5,4,3] [] [5] [B,B,B,B,B,B]) (L [9,5,4,4] [] [5] [B,B,B,B,B,B]))) (M 18) (R2 29 [(19,(L [7,5,4,3] [] [5] [(L [5,2,3] [] [4] [(L [4,3] [] [4] [(L [3] [] [5] [(R1 2 [] 0)]),(T 4 [] [5])]),(L [5,2] [] [5] [])]),(L [3,2,3] [2] [4,14] [(L [7,4] [] [4] [(L [4] [] [5] [(R1 14 [] 2)]),(M 798),(T 7 [] [5])])]),(L [7,2,3] [3] [6,4] [(L [7,2] [] [6] [])]),(L [11,7,5] [] [7] [(L [5,3] [] [4] [(T 5 [] [4])]),(L [5,3] [] [4] [(T 5 [] [4])]),(M 114),(L [11,7] [] [4] []),(L [11,7] [] [4] [])]),(L [7,5,4] [] [4] [])]),(L [7,5,4,4] [] [5] [(L [5,2,2] [] [4] [(L [4,4] [] [4] [(T 2 [] [5]),(T 4 [] [5])])]),(L [3,2,2] [2] [4,14] []),(L [7,2,2] [3] [6,4] []),(L [11,7,4] [] [7] [(L [5,2] [] [4] []),(L [5,2] [] [4] []),(M 114),(L [11,7] [] [4] [])]),(L [9,5,4] [] [5] [(L [5,4] [] [4] [])])])),(23,(L [5,3,2,3] [3,2] [6,4,10] [B,(L [7,3,2] [2] [4,6] [(M 42)])]),(L [5,3,2,2] [3,2] [6,4,10] [B]))])) (M 14) (P 17 (R2 37 [(19,(X [7,5,4,3] [(L [5,4,3] [] [4] [(L [4,3] [3] [6,4] [(L [3] [] [5] [(R1 6 [] 5)]),(L [6] [] [5] [(R1 2 [] 0)])]),(L [5,3] [] [6] [(T 5 [] [4])]),(L [5,4] [] [4] [])]),(M 182),(X [9,4,3] [(X [4,5] [(L [5] [] [5] [(R1 6 [] 0),(R1 6 [] 3)]),(T 4 [19] [38,4]),(X [6] [(R1 2 [] 2)])]),(L [15,5] [] [14] [(L [5] [] [22] [(R1 6 [] 2),(R1 6 [] 5)]),(M 546),(L [5] [] [5] [(R1 6 [] 2),(R1 6 [] 2)]),(T 15 [] [4]),(T 15 [] [4])]),(L [11,6] [] [5] [(T 4 [] [4]),(T 11 [] [4])])]),(X [9,5,3] [(L [9,7] [2,17,2,53,2] [4,34,4,106,4,6] [(M 342),(L [5] [3,2,11,2,7,2,3,2,13,2,5,2,3,2,53,2,173,2,3,2,5,2,89,2,3] [6,4,22,4,14,4,6,4,26,4,10,4,6,4,106,4,346,4,6,4,10,4,178,4,6,4] [(R1 6 [] 3),(R1 6 [] 3)]),(T 9 [] [6]),(T 9 [2,3,2] [4,6,4,34]),(M 6174)]),(L [9,5] [2,3,2] [4,6,4,26] [])]),(L [9,5,4] [2,11,2,3,2] [4,22,4,6,4,10] [(L [5,4] [2,5] [4,10,4] [])])]),(X [7,5,4,2] [(L [5,4,4] [] [4] [(L [4,2] [3] [6,4] [(L [4] [] [5] [(R1 18 [] 2)])]),(L [5,2] [2] [4,6] []),(L [5,4] [] [5] [])]),(M 182),(X [7,4,4] [(L [15,6] [] [14] [(L [6] [] [5] [(R1 18 [] 2),(R1 6 [] 3)]),(L [6] [] [22] [(R1 18 [] 3),(R1 6 [] 3)]),(M 546),(L [6] [] [5] [(R1 18 [] 2),(R1 6 [] 2)]),(T 15 [] [6]),(T 15 [2] [4,6])]),(X [11,4] [(L [6] [11] [22,4] [(R1 6 [] 2)]),(L [10] [2] [4,22] [(R1 6 [] 2),(R1 6 [] 5),(M 54)])])]),(X [9,5,4] [(L [9,6] [3,2,17,2,53,2] [6,4,34,4,106,4,6] [(M 342),(L [6] [2,3] [4,6,4] [(R1 18 [] 2),(R1 6 [] 3)]),(T 9 [] [6]),(T 9 [2,31,2,149] [4,62,4,298,4])]),(L [17,9] [2,7,2,3,2,11,2,5,2,3,2,13] [4,14,4,6,4,22,4,10,4,6,4,26,4] [(L [9] [73,2,7] [146,4,14,4] [(M 1026),(R1 18 [] 11)]),(M 1638),(L [11] [] [4] [(M 1026),(R1 18 [] 3),(R1 18 [] 5)]),(L [9] [7,2,3,2,23,2,127] [14,4,6,4,46,4,254,4] [(M 1026),(R1 18 [] 2)]),(M 1026),(L [19] [2] [4,6] [(M 31122)])])])])),(23,(L [9,5,4,3] [2] [4,6] [(L [5,4,3] [] [5] [(L [2,3] [3] [6,4] [(L [4] [] [4] [(R1 18 [] 0)])]),(L [5,3] [] [4] [(T 5 [] [4])]),(L [5,4] [] [5] [])]),(M 546),(L [5,4,3] [] [5] [(L [4,3] [] [4] [(L [3] [] [6] [(R1 18 [] 2)]),(T 4 [] [6])]),(L [5,3] [] [4] [(T 5 [] [6])]),(L [5,4] [] [4] [])]),(L [9,4,3] [] [4] [(L [9,3] [] [5] [(T 9 [] [10])]),(L [9,4] [] [4] [])]),(L [9,5,3] [] [6] [(L [9,5] [] [4] [])]),(L [9,5,4] [] [14] [])]),(L [9,5,4,4] [2] [4,6] [(L [5,4,4] [] [5] [(L [2,2] [3] [6,4] []),(L [5,2] [3] [6,4] []),(M 14)]),(M 182),(L [5,4,4] [] [5] [(L [4,4] [] [4] [(T 2 [] [6]),(M 14)]),(L [5,4] [] [4] [(M 42)]),(M 14)]),(L [9,4,2] [3] [6,4] [(L [9,4] [] [5] [(M 42)])]),(L [9,5,2] [2] [4,6] []),(M 14)])),(29,(L [7,5,4,3] [] [4] [(L [3,2,3] [] [4] [(L [3,4] [] [5] [(L [5] [] [5] [B])])]),(M 546),(L [7,4,3] [] [5] [(L [7,1] [7,2,3] [14,4,6,4] []),(L [7,4] [] [4] [])]),(L [7,5,3] [] [5] [(L [7,5] [7] [14,4] [])]),(L [7,5,4] [] [6] [])]),(L [7,5,4,2] [] [4] [(L [3,2,2] [] [4] []),(M 182),(L [7,4,2] [] [5] [(L [7,2] [3] [6,4] [])]),(L [9,5,2] [] [5] [(L [5,4] [] [5] [(M 78)])])])),(31,(L [7,5,4,3] [] [4] [B,(M 182),(L [7,4,3] [] [5] [(L [7,1] [2,3] [4,6,4] []),(L [7,4] [] [6] [])]),(L [7,5,3] [] [5] [(L [7,5] [] [6] [])]),(L [7,5,4] [] [4] [])]),(L [7,5,4,2] [] [4] [B,(M 182),(L [7,4,2] [] [5] [(L [7,2] [] [4] [])]),(L [7,5,2] [] [5] [])]))]) (M 18) (X [5,3,2,2] [(L [5,4,2] [2,3,2,5,2,11,2] [4,6,4,10,4,22,4,6] [(L [4,4] [] [10] [(L [4] [] [4] [(R1 6 [] 0)]),(T 4 [] [26])]),(L [5,4] [] [4] [(T 5 [] [4])])])]))) (R2 53 [(13,A,A),(17,(M 54),A),(19,(X [5,3,1,1] [(X [3,3,1] [(L [5,3] [2] [4,10] [(L [3] [] [6] [(R1 6 [] 2)]),(T 5 [] [5])])])]),(X [5,3,1,2] [(X [3,3,2] [(L [5,4] [] [10] [(T 2 [2,5,2,11,2] [4,10,4,22,4,6]),(M 18)])])])),(23,(M 18),(X [5,3,3,2] [(L [5,3,4] [2] [4,14] [(L [5,4] [] [5] [(T 2 [] [5]),(L [4] [] [4] [(M 42)]),(M 42)]),(L [5,2] [] [6] []),(M 42)]),(L [11,5,4] [13,2] [26,4,6] [(M 42),(L [7,4] [] [4] [(L [4] [] [5] [(M 42)]),(M 18),(M 42)]),(M 66),(L [11,4] [] [4] [(M 42)]),(M 42)])])),(29,(M 18),(L [11,5,5,4] [2] [4,22] [(L [3,3,2] [2,3] [4,6,4] [(L [5,2] [] [4] [(T 2 [] [5])])]),(M 42),(L [5,3,2] [2,5,2,3,2,13,2,7,2,3,2] [4,10,4,6,4,26,4,14,4,6,4,10] [(L [5,4] [] [4] [(T 2 [] [5]),(L [4] [] [10] [(R1 6 [] 0)]),(T 5 [] [6])]),(L [5,2] [] [4] [])]),(M 66),(L [11,5,4] [] [4] [(L [11,2] [] [4] []),(L [13,4] [] [5] [(M 42),(T 13 [] [4])]),(L [11,5] [] [6] [])]),(L [11,5,2] [] [6] []),(L [13,7,4] [] [5] [(M 42),(M 18),(L [13,7] [] [6] [])]),(L [11,5,5] [2] [4,6] [])])),(31,(L [9,5,5,3] [3] [6,4] [(L [3,3,3] [5] [10,4] [(L [3,3] [] [4] [(L [5] [] [5] [B])]),(L [5,3] [] [5] [(T 3 [] [4])])]),(M 42),(L [5,5,3] [] [5] [(L [5,3] [] [5] [(L [3] [] [4] [(R1 6 [] 5)]),(L [3] [] [6] [(R1 6 [] 3)]),(T 5 [] [4])]),(L [5,3] [] [4] [(T 5 [] [5])]),(L [5,3] [] [6] [(T 5 [] [5])]),(L [5,5] [] [5] [])]),(L [9,3,3] [13,2] [26,4,6] [(L [9,3] [] [5] [(T 9 [] [4])]),(L [9,3] [11,2] [22,4,10] [])]),(L [9,5,3] [] [5] [(L [9,5] [] [4] [])]),(L [11,7,3] [] [4] [(M 726),(M 18),(L [11,7] [] [6] [])]),(L [9,5,5] [] [4] [])]),(L [9,5,5,2] [2,3] [4,6,4] [(L [3,3,2] [2,5] [4,10,4] [(L [3,2] [] [4] [])]),(M 42),(L [5,5,4] [] [5] [(L [5,4] [] [5] [(T 2 [] [4]),(T 2 [2] [4,6]),(M 18)]),(L [5,2] [] [4] []),(L [5,2] [2] [4,6] []),(M 18)]),(L [9,3,2] [2,13,2] [4,26,4,6] [(L [9,4] [] [5] [(M 18)])]),(L [9,5,2] [] [5] []),(L [11,7,4] [] [4] [(M 726),(M 18),(M 18)])])),(37,(L [7,5,3,3] [2,7] [4,14,4] [(L [5,3,3] [] [5] [(L [3,3] [] [4] [B,(T 3 [] [5])]),B,(L [5,3] [] [4] [])]),(M 42),(L [9,5,3] [] [5] [(L [3,3] [3] [6,4] [(T 1 [7,2] [14,4,6]),(T 3 [] [4])]),(L [9,1] [7,2] [14,4,6] []),(L [9,3] [] [4] [(T 9 [] [5])]),(L [11,5] [] [4] [(M 726)])]),(L [7,5,1] [2,3] [4,6,4] []),(L [7,5,3] [5,2] [10,4,6] [])]),(L [7,5,3,2] [2,7] [4,14,4] [(L [5,3,2] [] [5] [(L [3,2] [] [4] [B]),B]),(M 42),(L [9,5,2] [] [5] [(L [3,2] [3] [6,4] [(T 2 [] [6])]),(L [9,2] [] [6] []),(L [9,2] [] [4] [])]),(L [7,5,2] [] [4] [])])),(41,(M 126),(L [9,5,5,2] [] [4] [B,(M 42),(M 246),(L [9,5,2] [] [4] [(L [9,2] [] [6] []),(L [9,2] [] [5] [])]),(L [9,5,2] [] [4] []),(L [11,7,4] [] [4] [(M 726),(M 18),(L [11,7] [] [5] [])])])),(43,(M 66),(L [9,5,3,2] [] [4] [B,(M 42),(L [5,3,2] [] [5] [(L [3,2] [5] [10,4] [B]),B]),(L [9,3,2] [] [4] [B]),B])),(47,(M 18),(L [9,5,5,2] [] [4] [B,(M 42),(L [5,3,2] [] [5] [(L [3,2] [] [4] [B]),B]),(L [9,3,2] [] [4] [B]),B,(L [11,5,2] [] [4] [(M 726)])]))]) (P 13 (P 17 (P 19 (P 23 (R2 53 [(29,(L [11,5,4,3] [2] [4,22] [(L [3,4,3] [3] [6,4] [(M 42),(L [5,4] [] [4] [(T 4 [] [4])])]),(M 42),(L [5,4,3] [3,2] [6,4,10] [(L [4,3] [] [4] [(M 42),(T 4 [2] [4,10])]),(M 42),(L [7,6] [] [4] [(M 18),(T 7 [] [5])])]),(M 726),(L [11,6,3] [] [4] [(M 42),(L [11,3] [] [5] [(T 11 [] [5])]),(L [11,6] [] [5] [])]),(M 42),(L [11,5,4] [] [6] [])]),(L [11,5,4,4] [2] [4,22] [(L [3,4,2] [2,3] [4,6,4] [(M 14)]),(M 14),(L [5,4,2] [2,7,2,3,2] [4,14,4,6,4,10] [(L [4,4] [] [4] [(M 14),(T 4 [] [6])]),(M 14)]),(M 242),(L [11,6,4] [] [4] [(M 14),(L [11,4] [] [5] [(T 11 [] [4])]),(L [11,6] [] [6] [])]),(M 14),(L [11,5,4] [2] [4,6] [])])),(31,(L [9,5,4,3] [3] [6,4] [(L [3,4,3] [5] [10,4] [(M 14),(L [5,4] [] [5] [(T 4 [] [4])])]),(M 14),(L [5,4,3] [] [5] [(L [6,3] [] [5] [(M 14),(L [3] [] [4] [(R1 2 [] 2)]),(T 6 [] [4])]),(M 14),(L [5,4] [] [5] [])]),(L [9,4,3] [2] [4,6] [(M 14),(L [9,4] [] [10] [])]),(M 14),(L [9,5,4] [] [4] [])]),(L [9,5,4,2] [2,3] [4,6,4] [(L [3,4,2] [5] [10,4] [(M 14)]),(M 14),(L [5,4,4] [] [5] [(L [6,4] [] [5] [(M 14),(T 2 [] [4]),(T 6 [] [4])]),(M 14),(L [5,4] [] [4] [])]),(L [9,4,2] [13,2] [26,4,6] [(M 14)]),(M 14)])),(37,(L [7,5,4,3] [7] [14,4] [(L [5,4,3] [] [5] [(L [4,3] [] [4] [(M 14),(T 4 [] [5])]),(M 14),(L [5,4] [] [4] [])]),(M 14),(L [9,4,3] [] [5] [(L [4,3] [] [4] [(M 14),(T 4 [] [4])]),(M 14),(L [11,6] [] [4] [(M 242),(L [13] [] [4] [(M 14)])])]),(M 14),(L [7,5,4] [5,2] [10,4,6] [])]),(L [7,5,4,2] [7] [14,4] [(L [5,4,2] [] [5] [(L [4,2] [] [4] [(M 14)]),(M 14)]),(M 14),(L [9,4,2] [] [5] [(L [4,2] [] [4] [(M 14)]),(M 14)]),(M 14)])),(41,(M 42),(L [9,5,4,2] [] [4] [B,(M 14),(M 82),(L [9,4,2] [] [4] [(M 14)]),(M 14)])),(43,(M 22),(L [9,5,4,2] [] [4] [B,(M 14),(L [5,4,2] [] [5] [(L [2,2] [2,3,2,5] [4,6,4,10,4] []),(M 14)]),(L [9,2,2] [3,2,5] [6,4,10,4] []),(M 14)])),(47,(L [9,5,4,3] [] [4] [B,(M 42),(L [5,4,3] [] [5] [(L [2,1] [2,5,2,3] [4,10,4,6,4] []),(M 42),(L [5,4] [] [4] [])]),(L [9,2,1] [2,5,2,3] [4,10,4,6,4] []),(M 42),(L [9,5,4] [] [4] [])]),(L [9,5,4,2] [] [4] [B,(M 14),(L [5,4,2] [] [5] [(L [2,2] [5,2,3] [10,4,6,4] []),(M 14)]),(L [9,2,2] [2,3] [4,6,4] []),(M 14)]))]) (X [5,3,2,1] [(L [5,4,3] [] [14] [(L [4,3] [] [5] [(M 42),(T 4 [] [4])]),(M 42),(L [5,4] [3] [6,4] [])])]) (X [5,3,2,2] [(L [5,4,2] [3,2] [6,4,14] [(L [4,4] [] [5] [(M 14),(M 14)]),(M 14)])])) (X [5,3,2,1] [(X [3,2,3] [(X [3,4] [(M 266)])])]) A) A A) A A)) (P 11 (P 13 (P 17 (P 19 B (P 23 B (L [9,6,3,3] [] [5] [B,B,B,(L [11,3,3] [] [7] [(L [5,5] [] [7] [B,B,B,B]),B,B]),B,B]) (L [9,6,3,4] [] [5] [B,B,B,(L [11,3,4] [] [7] [(L [5,4] [] [7] [B,B,B]),B,B]),B,B])) (P 23 B (L [9,6,4,3] [] [5] [B,B,B,(L [11,4,3] [] [7] [(L [4,5] [] [7] [B,B,B]),B,B]),B,B]) (L [9,6,4,4] [] [5] [B,B,B,(L [9,4,4] [] [7] [B,B]),B,B]))) (M 18) (R2 29 [(19,(L [9,4,4,3] [] [5] [(L [4,2,3] [] [4] [(L [4,2] [] [5] [])]),(L [4,2,3] [] [14] [(L [6,4] [] [4] [(T 2 [] [5]),(T 6 [] [5])])]),(L [6,4,3] [] [5] [(L [2,3] [] [4] [(T 2 [3] [6,4])]),(L [6,3] [] [4] [(T 6 [] [4])]),(L [6,4] [] [4] [])]),(L [11,6,5] [] [7] [(L [4,3] [] [4] [(T 4 [] [4])]),(L [11,3] [] [4] [(T 11 [] [4])]),(L [11,6] [] [4] []),(L [11,6] [] [4] [])]),(L [9,4,4] [] [4] [])]),(L [9,4,4,4] [] [5] [(L [4,2,2] [] [4] []),(L [4,2,2] [2] [4,14] []),(L [6,4,4] [] [5] [(L [2,2] [] [4] []),(L [6,2] [] [4] []),(L [6,4] [] [4] [])]),(L [11,6,4] [] [7] [(L [4,2] [] [4] []),(L [11,2] [] [4] []),(L [11,6] [] [4] [])]),(L [9,6,4] [] [5] [(L [11,4] [] [7] [(T 4 [] [4])])])])),(23,(L [5,4,2,3] [3,2] [6,4,10] [B,(L [7,4,2] [] [6] [(M 42)])]),(L [5,4,2,2] [3,2] [6,4,10] [B]))])) (M 14) (P 17 (R2 37 [(19,(X [7,4,4,3] [(L [4,4,3] [] [4] [(L [4,3] [] [6] [(T 4 [] [4])]),(L [4,4] [] [4] [])]),(M 182),(X [9,4,3] [(L [10,7] [2] [4,6] [(L [7] [] [5] [(R1 6 [] 0),(R1 6 [] 2),(M 6174)]),(L [7] [] [4] [(R1 6 [] 3),(R1 6 [] 2),(M 6174)]),(M 1026),(T 10 [] [6]),(T 10 [2] [4,34]),(M 6174)]),(L [9,6] [3,2] [6,4,26] [(L [11] [] [6] [(R1 6 [] 0)])])]),(L [9,6,4] [11,2,3,2] [22,4,6,4,10] [(L [6,4] [5] [10,4] [(T 4 [] [10])]),(L [11,4] [] [5] [(T 4 [] [4])])])]),(X [7,4,4,2] [(L [4,4,4] [] [4] [(L [4,2] [2] [4,6] []),(L [4,4] [] [5] [])]),(M 182),(X [9,4,4] [(L [10,6] [53,2] [106,4,6] [(L [6] [] [5] [(R1 18 [] 5),(R1 6 [] 2)]),(L [6] [2,7] [4,14,4] [(R1 18 [] 2),(R1 6 [] 2)]),(M 1026),(T 10 [] [6]),(T 10 [] [4])]),(L [17,10] [2,5,2,3,2,13] [4,10,4,6,4,26,4] [(L [10] [7] [14,4] [(R1 18 [] 2),(R1 18 [] 2),(M 3078)]),(M 1638),(L [12] [] [4] [(R1 18 [] 2),(R1 18 [] 2),(M 3078),(R1 18 [] 0)]),(L [10] [127] [254,4] [(R1 18 [] 2),(R1 18 [] 2),(M 3078)]),(T 17 [] [6]),(L [19] [] [5] [(M 31122)]),(M 3078)])])])),(23,(L [9,4,4,3] [2] [4,6] [(L [6,4,3] [] [5] [(L [2,3] [] [4] [(L [4] [] [5] [(R1 18 [] 2)])]),(L [6,3] [] [4] [(T 6 [] [4])]),(L [6,4] [] [5] [])]),(M 546),(L [6,4,3] [] [5] [(L [4,3] [] [4] [(L [3] [] [5] [(R1 18 [] 2)]),(T 4 [] [4])]),(L [6,3] [] [4] [(T 6 [] [6])]),(L [6,4] [] [4] [])]),(L [9,4,3] [2] [4,6] [(L [9,4] [3] [6,4] [])]),(L [9,4,4] [] [14] [])]),(L [9,4,4,4] [2] [4,6] [(L [6,4,4] [] [5] [(L [2,2] [3] [6,4] []),(L [6,2] [3] [6,4] []),(M 14)]),(M 182),(L [6,4,4] [] [5] [(L [4,4] [] [4] [(L [4] [] [5] [(M 42)]),(M 14)]),(L [6,4] [] [4] [(M 42)]),(M 14)]),(L [9,4,2] [2] [4,6] []),(M 14)])),(29,(L [7,4,4,3] [] [4] [(L [4,2,3] [] [4] [(L [4,2] [] [5] [])]),(M 546),(L [9,4,3] [] [5] [(L [6,3] [] [5] [(T 1 [7,2,3] [14,4,6,4]),(T 6 [] [4])]),(L [9,4] [] [4] [])]),(L [7,4,4] [] [6] [])]),(L [7,4,4,2] [] [4] [(L [4,2,2] [] [4] []),(M 182),(L [9,4,2] [] [5] [(L [6,4] [] [5] [(T 2 [] [4]),(M 78)])])])),(31,(L [7,4,4,3] [] [4] [B,(M 182),(L [7,4,3] [] [5] [(L [7,4] [] [6] [])]),(L [7,4,4] [] [4] [])]),(L [7,4,4,2] [] [4] [B,(M 182),(L [7,4,2] [] [5] [])]))]) (M 18) (X [5,4,2,2] [(L [4,4,4] [11,2] [22,4,6] [(L [6,4] [] [4] [(L [4] [] [4] [(R1 6 [] 0)]),(T 6 [] [4])]),(L [6,4] [] [4] [(T 4 [] [4])])])]))) (R2 53 [(13,A,A),(17,(M 54),A),(19,(X [5,4,1,1] [(X [4,3,1] [(L [4,3] [2,7,2] [4,14,4,10] [(L [6] [] [5] [(R1 6 [] 2)])])])]),(X [5,4,1,2] [(X [4,3,2] [(L [4,4] [7,2] [14,4,10] [(M 18)])])])),(23,(M 18),(X [5,4,3,2] [(L [4,3,4] [2,3,2] [4,6,4,14] [(L [4,2] [2] [4,6] []),(M 42)]),(L [11,6,4] [] [6] [(M 42),(L [6,4] [] [4] [(L [4] [] [5] [(M 42)]),(M 42)]),(M 66),(L [11,4] [] [4] [(M 42)]),(M 42)])])),(29,(M 18),(L [9,6,5,4] [2] [4,22] [(L [4,3,2] [] [4] [(L [4,2] [] [4] [])]),(M 42),(L [4,5,2] [2,3,2,13,2,7,2,3,2] [4,6,4,26,4,14,4,6,4,10] [(L [4,2] [] [4] []),(L [6,2] [5,2,3] [10,4,6,4] [(L [4] [] [5] [(R1 6 [] 2)])])]),(L [13,7,4] [] [4] [(M 66),(M 42),(L [13,2] [] [6] []),(L [13,4] [] [5] [(T 13 [] [6])]),(M 126),(L [13,7] [] [4] [])]),(L [9,6,2] [] [6] []),(L [13,6,4] [] [5] [(M 726),(M 42),(L [13,6] [] [6] [])]),(L [9,6,5] [2] [4,6] [])])),(31,(L [9,4,5,3] [2,3] [4,6,4] [(L [4,3,3] [] [4] [(L [4,3] [] [4] [(T 4 [] [5])]),(L [4,3] [] [5] [])]),(M 42),(L [6,5,3] [] [5] [(L [3,3] [5,2] [10,4,6] [(L [3] [] [4] [(R1 6 [] 0)]),(L [5] [] [4] [(R1 6 [] 2)])]),(L [6,3] [] [4] [(T 6 [] [5])]),(L [6,3] [] [6] [(T 6 [] [5])]),(L [6,5] [] [5] [])]),(L [9,6,3] [] [5] [(L [13,5] [] [5] [(M 66),(M 42),(T 13 [] [5]),(T 13 [] [7])]),(L [9,6] [] [4] [])]),(L [11,6,3] [] [4] [(M 726),(L [11,3] [] [4] [(L [13] [] [4] [(M 42)])]),(L [11,6] [] [6] [])]),(L [9,4,5] [3] [6,4] [])]),(L [9,6,5,2] [2,3] [4,6,4] [(L [4,3,2] [] [4] [(L [4,2] [] [4] [])]),(M 42),(L [6,5,4] [] [5] [(L [3,2] [2,5,2] [4,10,4,6] [(T 2 [] [4])]),(L [6,2] [] [4] []),(L [6,2] [2] [4,6] []),(M 18)]),(L [9,5,4] [] [4] [(L [13,4] [] [5] [(M 66),(M 42),(M 18)]),(L [11,4] [] [4] [(M 726),(M 18)]),(M 18)]),(L [9,6,2] [] [5] []),(L [11,6,4] [] [4] [(M 726),(M 18)])])),(37,(L [7,4,3,3] [2,7] [4,14,4] [(L [4,3,3] [] [5] [B,(L [4,5] [] [4] [(L [6] [] [4] [(R1 6 [] 0)])])]),(M 42),(L [7,4,1] [2,3] [4,6,4] []),(L [7,4,3] [5,2] [10,4,6] [])]),(L [7,4,3,2] [2,7] [4,14,4] [(L [4,3,2] [] [5] [B]),(M 42),(L [7,4,2] [] [4] [])])),(41,(M 126),(L [9,6,5,2] [] [4] [B,(M 42),(M 246),(L [11,5,2] [] [4] [(M 66),(L [11,2] [] [4] []),(L [11,2] [] [5] [])]),(L [9,6,2] [] [4] []),(L [11,6,4] [] [4] [(M 726),(L [11,6] [] [5] [])])])),(43,(M 66),(L [9,4,5,2] [] [4] [B,(M 42),(L [4,3,2] [] [5] [B]),B,(L [9,6,2] [] [4] [(L [9,2] [] [5] [])])])),(47,(M 18),(L [9,4,5,2] [] [4] [B,(M 42),(L [4,3,2] [] [5] [B]),B,(L [11,6,2] [] [4] [(M 726),(L [11,2] [] [5] [])])]))]) (P 13 (P 17 (P 19 (P 23 (R2 53 [(29,(L [11,6,4,3] [2] [4,22] [(L [4,4,3] [] [4] [(M 42),(L [6,4] [] [4] [(L [6] [] [4] [(R1 6 [] 0)])])]),(M 42),(L [4,4,3] [13,2,7,2,3,2] [26,4,14,4,6,4,10] [(M 42),(L [6,6] [] [4] [(T 4 [2] [4,26]),(T 6 [] [5])])]),(M 726),(L [13,6,5] [] [4] [(M 42),(M 42),(L [13,3] [] [5] [(T 13 [] [4])]),(L [13,6] [] [4] []),(L [13,6] [] [5] [])]),(M 42),(L [11,6,4] [] [6] [])]),(L [11,6,4,4] [] [22] [(L [4,4,2] [] [4] [(M 14)]),(M 14),(L [4,4,2] [5,2,3,2,13,2,7,2,3,2] [10,4,6,4,26,4,14,4,6,4,10] [(M 14)]),(M 242),(L [13,6,4] [] [4] [(M 14),(M 14),(L [13,4] [] [5] [(T 13 [] [6])]),(L [13,6] [] [4] [])]),(M 14),(L [11,6,4] [2] [4,6] [])])),(31,(L [9,6,4,3] [3] [6,4] [(L [4,2,3] [2,5] [4,10,4] [(L [4,4] [] [5] [(M 14)])]),(M 14),(L [6,4,3] [] [5] [(L [4,3] [] [6] [(M 14),(L [6] [] [4] [(R1 2 [] 0)])]),(M 14),(L [6,4] [] [5] [])]),(L [11,4,3] [] [4] [(M 242),(M 14),(L [11,4] [] [6] [])]),(M 14),(L [9,6,4] [] [4] [])]),(L [9,6,4,2] [2,3] [4,6,4] [(L [4,4,2] [] [4] [(M 14)]),(M 14),(L [6,4,4] [] [5] [(L [4,2] [2] [4,6] [(M 14)]),(M 14),(L [6,4] [] [4] [])]),(L [11,4,4] [] [4] [(M 242),(M 14),(L [11,4] [] [5] [])]),(M 14)])),(37,(L [7,4,4,3] [7] [14,4] [(L [4,4,3] [] [5] [(M 14),(L [4,4] [] [4] [])]),(M 14),(M 14),(L [7,4,4] [5,2] [10,4,6] [])]),(L [7,4,4,2] [2,7] [4,14,4] [(L [4,4,2] [] [5] [(M 14)]),(M 14),(M 14)])),(41,(M 42),(L [9,6,4,2] [] [4] [B,(M 14),(M 82),(L [11,4,4] [] [4] [(M 242),(M 14),(L [11,6] [] [4] [(T 11 [] [5])])]),(M 14)])),(43,(M 22),(L [9,4,4,2] [] [4] [B,(M 14),(L [4,4,2] [] [5] [(M 14)]),(M 14)])),(47,(L [9,4,4,3] [] [4] [B,(M 42),(L [4,4,3] [] [5] [(M 42),(L [4,4] [] [4] [])]),(M 42),(L [9,4,4] [] [4] [])]),(L [9,6,4,2] [] [4] [B,(M 14),(L [4,4,2] [] [5] [(M 14)]),(L [11,4,2] [] [4] [(M 242),(M 14)]),(M 14)]))]) (X [5,4,2,1] [(L [4,4,3] [2] [4,14] [(M 42),(L [4,4] [3] [6,4] [])])]) (X [5,4,2,2] [(L [4,4,2] [2,3,2] [4,6,4,14] [(M 14)])])) (X [5,4,2,1] [(X [4,2,3] [(X [4,4] [(M 266)])])]) A) A A) A A)))
private def c4 : Cert := (S7 5 (K 3) (M 6) (S7 7 (P 11 (P 13 (P 17 (P 19 (P 23 (P 29 (P 31 (P 37 B (R2 47 [(41,(M 6),(L [7,3,2] [2] [4,14] [B,(L [1,2] [2,3] [4,6,4] []),(L [7,2] [] [5] [])])),(43,B,B)]) (R2 47 [(41,(M 6),(L [7,2,2] [2] [4,14] [B,(L [2,2] [] [4] [])])),(43,B,B)])) (M 62) (M 62)) (M 30) (R2 53 [(31,(M 62),(M 62)),(37,(L [9,2,3] [] [6] [(M 10),(L [2,3] [] [6] [(T 2 [] [4])]),(M 10),(L [9,2] [] [4] [])]),(L [9,2,2] [2] [4,6] [(M 10),(L [2,2] [] [6] []),(M 10)])),(41,(M 6),(L [7,2,2] [7] [14,4] [B,(L [4,2] [] [5] [(T 2 [] [4])])])),(43,(L [9,4,3] [] [4] [B,(L [2,1] [3,2] [6,4,10] []),(M 10),(L [9,3] [] [5] [(T 9 [] [6])]),(L [9,4] [] [6] [])]),(L [9,4,2] [] [4] [B,(L [2,2] [] [10] []),(M 10),(L [9,2] [] [5] [])])),(47,(M 6),(L [7,2,2] [2] [4,6] [B,(L [2,2] [3] [6,4] [])]))])) (M 6) (R2 71 [(29,(M 30),(X [5,2,2] [(M 10)])),(31,(M 62),(M 62)),(37,(L [11,4,3] [2,5,2,19,2] [4,10,4,38,4,6] [(M 10),(L [4,3] [] [4] [(L [3] [] [4] [(R1 2 [] 2)]),(T 4 [] [4])]),(M 10),(L [4,3] [2] [4,46] [(L [3] [2] [4,6] [(R1 2 [] 3)]),(T 4 [] [6])]),(L [11,3] [11,2,3,2] [22,4,6,4,58] [(T 11 [] [4])]),(L [11,4] [2] [4,26] [])]),(L [11,4,4] [5,2,19,2] [10,4,38,4,6] [(M 10),(L [4,2] [11,2,5,2,3] [22,4,10,4,6,4] [(L [4] [] [4] [(M 6)])]),(M 10),(L [4,4] [] [46] [(L [4] [] [6] [(M 6)]),(M 6)]),(L [11,4] [2,3,2] [4,6,4,58] [(M 6)]),(M 6)])),(41,(M 6),(L [9,4,2] [17,2,3] [34,4,6,4] [(M 10),(L [2,2] [2,5,2,3] [4,10,4,6,4] []),(M 410),(L [11,2] [2] [4,6] [(L [4] [] [4] [(R1 2 [] 2)])])])),(43,(L [9,2,3] [3,2,5,2,7] [6,4,10,4,14,4] [(M 10),(L [4,3] [] [4] [(L [3] [] [6] [(R1 2 [] 2)]),(T 4 [] [4])]),(M 10),(L [9,4] [2] [4,6] [(L [11] [] [4] [(R1 2 [] 0)])])]),(L [9,2,2] [3,2,5,2,7] [6,4,10,4,14,4] [(M 10),(L [4,4] [] [4] [(T 2 [] [6]),(M 6)]),(M 10)])),(47,(M 6),(L [9,4,2] [] [5] [(M 10),(L [2,2] [2] [4,10] []),(M 10),(L [9,2] [] [5] [])])),(53,(M 54),(L [9,4,2] [] [4] [B,(L [2,2] [5] [10,4] []),(M 10),(L [9,2] [] [5] [])])),(59,(M 30),(L [9,2,2] [2] [4,14] [B,(L [2,2] [2] [4,6] []),(M 10)])),(61,(L [7,2,3] [5] [10,4] [B,(L [2,1] [3,2] [6,4,14] []),(L [9,2] [] [4] [(M 10)])]),(L [7,2,2] [5] [10,4] [B,(L [2,2] [] [14] [])])),(67,(L [7,2,1] [2,3] [4,6,4] [B,B]),(L [7,2,2] [3] [6,4] [B,B]))])) (M 10) (R2 109 [(23,A,A),(29,A,A),(31,A,A),(37,(M 38),(X [5,2,2] [(M 10)])),(41,(M 6),(X [5,2,2] [(M 10)])),(43,(X [5,2,1] [(M 10)]),(X [5,2,2] [(M 10)])),(47,(M 6),(X [5,2,2] [(M 10)])),(53,(M 54),(X [7,2,2] [(M 10),(L [4,4] [17] [34,4] [(M 6),(T 4 [3] [6,4])])])),(59,(M 30),(L [13,6,4] [] [4] [(M 10),(L [4,2] [] [5] [(M 6)]),(M 10),(L [4,4] [] [5] [(M 6),(T 4 [] [6])]),(M 10),(M 6),(L [19,6] [] [4] [(L [4] [] [5] [(R1 2 [] 7)]),(M 10),(M 38),(T 19 [] [14]),(L [21] [] [4] [(M 50)])]),(L [13,6] [] [14] [])])),(61,(L [11,4,3] [2] [4,6] [(M 10),(L [4,3] [] [26] [(M 6),(T 4 [] [5])]),(M 10),(M 122),(M 6),(L [11,4] [5] [10,4] [])]),(L [11,4,2] [5,2] [10,4,6] [(M 10),(L [4,2] [2] [4,26] [(M 6)]),(M 10),(M 122),(M 6)])),(67,(L [9,4,3] [7,2] [14,4,34] [B,(L [2,3] [3,2,7,2,5,2] [6,4,14,4,10,4,6] [(L [4] [] [4] [(M 6)])]),(M 10),(M 6),(L [11,4] [] [5] [(T 4 [] [4])])]),(L [9,4,2] [7,2] [14,4,34] [B,(L [2,2] [3,2,7,2,5,2] [6,4,14,4,10,4,6] []),(M 10),(M 6)])),(71,(M 18),(L [9,4,2] [2,3] [4,6,4] [B,(L [4,2] [] [4] [(M 6)]),(M 10),(M 6)])),(73,(L [9,4,3] [] [4] [B,(L [4,3] [] [4] [(M 6),(T 4 [] [6])]),(M 10),(M 6),(L [9,4] [7] [14,4] [])]),(L [11,4,2] [] [4] [B,(L [4,2] [] [4] [(M 6)]),(M 10),(L [4,4] [] [4] [(M 6),(M 6)]),(M 6)])),(79,(M 10),(L [9,4,2] [] [5] [B,(L [4,2] [] [4] [(M 6)]),(M 10),(M 6)])),(83,(M 6),(L [11,4,2] [] [5] [B,(L [4,2] [] [6] [(M 6)]),(M 10),(L [2,2] [3,2,5] [6,4,10,4] []),(M 6)])),(89,(M 90),(L [11,4,2] [] [5] [B,(L [2,2] [5,2] [10,4,6] []),(M 10),(L [4,2] [] [4] [(M 6)]),(M 6)])),(97,(L [7,2,1] [3,2,7,2,11,2] [6,4,14,4,22,4,6] [B,(L [4,1] [2] [4,6] [(M 6)])]),(L [7,2,2] [2,7,2,11,2] [4,14,4,22,4,6] [B,(L [2,2] [2] [4,6] [])])),(101,(M 6),(L [7,4,2] [5,2] [10,4,6] [B,B,(M 6)])),(103,(L [9,4,3] [] [4] [B,B,(M 10),(M 6),(L [9,4] [] [5] [])]),(L [9,4,2] [] [4] [B,B,(M 10),(M 6)])),(107,(M 54),(L [9,4,2] [] [4] [B,B,B,B]))])) (M 18) (R2 167 [(19,A,A),(23,A,A),(29,A,A),(31,A,A),(37,A,A),(41,(M 6),A),(43,(X [5,2,1] [(M 10)]),(X [5,2,2] [(M 10)])),(47,(M 6),(X [5,2,2] [(M 10)])),(53,(M 54),(X [5,2,2] [(M 10)])),(59,(M 30),(X [5,2,2] [(M 10)])),(61,(X [5,2,1] [(M 10)]),(X [5,2,2] [(M 10)])),(67,(M 34),(X [5,2,2] [(M 10)])),(71,(M 18),(X [5,2,2] [(M 10)])),(73,(X [5,2,1] [(M 10)]),(X [5,2,2] [(M 10)])),(79,(M 10),(X [7,2,2] [(M 10),(L [6,4] [] [6] [(L [4] [] [5] [(M 6)]),(L [4] [] [5] [(M 6)]),(M 6)])])),(83,(M 6),(X [7,4,2] [B,(L [4,2] [7,2] [14,4,10] [(T 2 [23] [46,4])]),(L [17,4] [2,3,2,113] [4,6,4,226,4] [(M 10),(L [4] [] [4] [(R1 2 [] 2)]),(M 10),(L [4] [] [4] [(R1 2 [] 19)]),(M 170),(T 17 [2,19,2] [4,38,4,6])])])),(89,(M 90),(L [13,4,4] [3,2] [6,4,14] [B,(L [4,2] [] [6] [(T 2 [] [4])]),(M 10),(L [4,2] [2,3,2,5,2] [4,6,4,10,4,22] [(L [4] [] [5] [(R1 2 [] 2)])]),(M 10),(L [13,2] [2,5] [4,10,4] []),(L [13,6] [] [5] [(T 13 [23] [46,4])])])),(97,(L [13,6,3] [] [4] [B,(L [4,3] [] [4] [(L [3] [] [7] [(R1 2 [] 2)]),(T 4 [2] [4,6])]),(M 10),(L [4,3] [] [10] [(L [3] [] [4] [(R1 2 [] 2)]),(T 4 [] [4])]),(M 10),(L [13,3] [] [4] [(T 13 [] [4])]),(L [13,3] [] [5] [(T 13 [] [4])]),(L [13,6] [] [4] [])]),(L [13,6,4] [] [4] [B,(L [4,2] [] [4] [(L [4] [] [7] [(M 6)])]),(M 10),(L [4,2] [2] [4,10] [(T 2 [] [4])]),(M 10),(L [13,2] [13] [26,4] []),(L [13,2] [] [5] []),(M 6)])),(101,(M 102),(L [11,4,2] [2] [4,6] [B,(L [4,2] [] [6] [(T 2 [] [4])]),(M 10),(L [4,2] [2] [4,14] [(T 2 [] [22])]),(L [11,2] [2] [4,10] [])])),(103,(L [13,6,3] [] [5] [B,(L [4,3] [] [5] [(L [3] [] [4] [(R1 2 [] 7)]),(T 4 [] [6])]),(M 10),(L [4,3] [] [6] [(L [3] [] [10] [(R1 2 [] 3)]),(T 4 [2] [4,6])]),(M 10),(L [13,3] [] [4] [(T 13 [] [4])]),(L [13,3] [] [4] [(T 13 [] [4])]),(L [13,6] [] [4] [])]),(L [13,6,4] [] [5] [B,(L [4,2] [] [5] [(T 2 [5] [10,4])]),(M 10),(L [4,2] [] [6] [(T 2 [] [10])]),(M 10),(L [13,2] [] [4] []),(L [13,2] [] [4] []),(M 6)])),(107,(M 54),(L [11,4,2] [] [34] [B,(L [4,2] [2] [4,6] [(T 2 [] [4])]),(M 10),(L [4,4] [] [5] [(T 2 [] [4]),(T 4 [] [4])]),(L [11,2] [] [4] [])])),(109,(M 10),(L [9,4,2] [2,5] [4,10,4] [B,(L [4,2] [] [4] [(T 2 [] [4])]),(M 10),(L [9,2] [3,2] [6,4,22] [])])),(113,(M 6),(L [9,4,2] [5,2] [10,4,6] [B,(L [4,2] [] [4] [(T 2 [] [4])]),(M 10),(L [13,2] [] [5] [(T 2 [] [10]),(M 10)])])),(127,(L [9,4,1] [3,2,5,2] [6,4,10,4,26] [B,(L [4,1] [3,2] [6,4,10] [(T 1 [2,3] [4,6,4])]),(M 10),(L [9,3] [5] [10,4] [(T 9 [3] [6,4])])]),(L [9,4,2] [2] [4,26] [B,(L [4,2] [] [10] [(T 2 [] [4])]),(M 10),(L [9,2] [5] [10,4] [])])),(131,(M 6),(L [11,4,2] [] [5] [B,(L [4,2] [] [6] [(T 2 [] [6])]),(M 10),(L [6,2] [] [5] [(T 2 [] [4]),(L [4] [] [5] [(R1 2 [] 2)])]),(L [11,2] [] [5] [])])),(137,(M 6),(L [9,4,2] [] [4] [B,(L [4,2] [] [5] [(T 2 [] [14])]),(M 10),(L [9,2] [] [6] [])])),(139,(M 10),(L [13,4,2] [] [4] [B,(L [4,2] [] [4] [(T 2 [] [6])]),(M 10),(L [4,2] [] [5] [(T 2 [] [4])]),(M 10),(L [13,2] [] [14] [])])),(149,(M 150),(L [11,4,2] [] [4] [B,(L [4,2] [] [4] [B]),(M 10),(L [4,2] [] [5] [(T 2 [] [4])]),(L [11,2] [] [10] [])])),(151,(L [7,4,1] [2,3,2,5,2,11,2] [4,6,4,10,4,22,4,6] [B,B,(L [11,3] [] [4] [(M 10),(L [3] [] [5] [(R1 2 [] 2)]),(T 11 [] [4])])]),(L [7,4,2] [3,2,5,2,11,2] [6,4,10,4,22,4,6] [B,B,(L [11,2] [] [4] [(M 10),(T 2 [] [5])])])),(157,(L [11,4,3] [] [4] [B,B,(M 10),(L [4,3] [] [5] [(L [3] [] [5] [(R1 2 [] 2)]),(T 4 [] [4])]),(L [11,3] [] [4] [(T 11 [] [4])]),(L [11,4] [] [5] [])]),(L [11,4,2] [] [4] [B,B,(M 10),(L [4,2] [] [5] [(T 2 [] [5])]),(L [11,2] [] [4] [])])),(163,(L [11,4,3] [] [5] [B,B,(M 10),(L [4,1] [3] [6,4] [B]),(L [11,3] [] [5] [B]),(L [11,4] [3] [6,4] [])]),(L [11,4,2] [] [5] [B,B,(M 10),(L [4,2] [] [4] [B]),(L [11,2] [] [5] [])]))])) (X [5,1] [(M 10)]) (X [5,2] [(M 10)])) A A) A A A A) (M 6) (S7 7 (P 11 (P 13 (P 17 (P 19 (P 23 (P 29 (P 31 (P 37 (P 41 B (M 6) (R2 53 [(43,(L [7,6,2,3] [] [5] [B,(L [4,2,1] [2,5,2] [4,10,4,6] []),(L [7,2,3] [] [4] [(L [7,2] [] [4] [])]),(L [7,6,2] [] [5] [])]),(L [7,6,2,2] [] [5] [B,(L [4,2,2] [5,2] [10,4,6] []),(L [9,2,2] [] [4] [(M 410)])])),(47,(M 6),(L [7,6,2,2] [2] [4,10] [B,B,(L [11,2,2] [] [4] [(M 410),(L [4,2] [] [4] [(L [4] [] [4] [(R1 2 [] 0)])])])]))])) (R2 59 [(41,(M 6),(L [9,6,3,2] [] [4] [B,(L [6,3,2] [] [4] [(L [3,2] [] [5] [(T 2 [] [5])]),(L [6,2] [] [6] [])]),(M 410),(L [9,1,2] [2,3,2,7] [4,6,4,14,4] []),(L [9,6,2] [] [4] [])])),(43,(L [7,6,3,3] [] [5] [B,(L [6,3,3] [] [5] [(L [3,1] [3,2] [6,4,10] [(L [3] [] [4] [(R1 2 [] 2)])]),(L [6,3] [] [4] [(L [8] [] [4] [(R1 2 [] 0)])]),(L [6,3] [] [4] [])]),(L [9,3,3] [] [4] [(M 10),(L [9,3] [] [4] [(T 9 [] [4])]),(L [9,3] [] [6] [])]),(L [7,6,3] [3] [6,4] [(L [9,6] [] [5] [(M 10)])]),(L [9,6,3] [] [5] [(M 10)])]),(L [7,6,3,2] [] [5] [B,(L [6,3,2] [] [5] [(L [1,2] [2,3,2] [4,6,4,10] []),(L [6,2] [] [4] [])]),(L [9,3,2] [] [4] [(M 10),(L [9,2] [] [4] [])]),(L [7,6,2] [3] [6,4] [])])),(47,(M 6),(L [7,4,3,2] [2,3] [4,6,4] [B,(L [6,3,2] [] [5] [(L [1,2] [5,2,3] [10,4,6,4] []),(L [6,2] [] [4] [])]),(L [9,6,2] [] [5] [(M 10),(L [9,2] [] [4] [])])])),(53,B,B)]) (R2 59 [(41,(M 6),(L [9,6,2,2] [] [4] [B,(L [6,2,2] [] [4] [(L [2,2] [] [5] [])]),(M 410),(L [9,2,2] [] [4] [])])),(43,(L [9,6,2,3] [] [5] [B,(L [6,2,3] [] [5] [(L [2,1] [3,2] [6,4,10] []),(L [6,2] [] [4] [])]),(M 10),(L [9,2,3] [] [4] [(L [9,2] [] [6] [])]),(L [9,6,4] [] [5] [(M 6)])]),(L [9,6,2,2] [] [5] [B,(L [6,2,2] [] [5] [(L [2,2] [] [10] [])]),(M 10),(L [9,2,2] [] [4] [])])),(47,(M 6),(L [7,4,2,2] [2,3] [4,6,4] [B,(L [6,2,2] [] [5] [(L [2,2] [] [4] [])])])),(53,B,B)])) (R2 67 [(37,(L [11,8,3,3] [] [4] [(M 10),(L [6,3,3] [2] [4,10] [(L [3,3] [] [6] [(L [3] [] [6] [(R1 2 [] 2)]),(T 3 [] [4])]),(L [6,3] [] [4] [(T 6 [] [14])]),(L [6,3] [] [10] [])]),(M 10),(L [8,3,3] [] [5] [(L [3,3] [] [6] [(L [3] [] [10] [(R1 2 [] 5)]),(T 3 [] [10])]),(L [3,3] [] [4] [(L [3] [] [4] [(R1 2 [] 0)]),(T 3 [] [4])]),(L [8,3] [] [10] [(T 8 [] [5])]),(L [8,3] [] [4] [])]),(L [11,3,3] [] [4] [(L [11,3] [] [10] [(T 11 [] [10])]),(L [11,3] [] [10] [])]),(L [11,3,3] [] [5] [(L [11,3] [] [10] [(T 11 [] [5])]),(L [11,3] [] [4] [])]),(L [11,8,3] [] [10] [(L [11,8] [] [5] [])]),(L [11,8,3] [] [5] [])]),(L [11,8,3,4] [] [4] [(M 10),(L [6,3,2] [2] [4,10] [(L [3,2] [] [6] [(T 2 [] [6])]),(L [6,2] [3] [6,4] [])]),(M 10),(L [8,3,4] [] [5] [(L [3,2] [2] [4,6] [(T 2 [2] [4,10])]),(L [3,4] [] [4] [(T 2 [] [4]),(M 6)]),(L [8,2] [2] [4,10] []),(M 6)]),(L [11,3,2] [3] [6,4] [(L [11,2] [2] [4,10] [])]),(L [11,3,4] [] [5] [(L [11,2] [2] [4,10] []),(M 6)]),(L [11,8,2] [] [10] []),(M 6)])),(41,(M 6),(L [9,6,3,2] [3] [6,4] [(M 10),(L [4,3,2] [2,5,2,3,2] [4,10,4,6,4,14] [(L [6,2] [3] [6,4] [(T 2 [] [4])])]),(M 410),(L [9,3,2] [3] [6,4] [(L [9,2] [2] [4,14] [])]),(L [9,6,2] [] [6] [])])),(43,(L [7,4,3,3] [5,2,3,2,7,2,11] [10,4,6,4,14,4,22,4] [(M 10),(L [6,3,3] [] [4] [(L [3,3] [] [5] [(L [3] [] [14] [(R1 2 [] 3)]),(T 3 [] [4])]),(L [6,3] [] [4] [(L [10] [] [4] [(R1 2 [] 0),(M 62)])]),(L [6,3] [] [6] [])]),(L [9,6,3] [] [4] [(M 10),(L [9,3] [] [4] [(T 9 [] [6])]),(L [9,6] [] [4] [])]),(L [9,6,3] [] [4] [(M 10),(L [9,3] [] [4] [])])]),(L [7,4,3,2] [5,2,3,2,7,2,11] [10,4,6,4,14,4,22,4] [(M 10),(L [6,3,2] [] [4] [(L [3,2] [] [5] [(T 2 [] [14])]),(L [6,2] [] [4] [])]),(L [9,6,2] [] [4] [(M 10),(L [9,2] [] [4] [])])])),(47,(M 6),(L [11,8,3,2] [] [4] [B,(L [4,3,2] [2,5] [4,10,4] [(L [6,2] [] [5] [(T 2 [] [14])])]),(M 10),(L [6,3,2] [] [5] [(L [3,2] [2] [4,10] [(T 2 [] [4])]),(L [6,2] [] [4] [])]),(L [11,3,2] [] [10] [(L [11,2] [] [4] [])]),(L [13,5,4] [] [4] [(M 10),(L [13,4] [] [5] [(T 13 [] [4])]),(L [15,4] [] [4] [(T 2 [] [5]),(T 15 [] [5])]),(L [13,5] [] [5] [])]),(L [11,8,2] [] [5] [])])),(53,(M 54),(L [11,6,3,2] [] [5] [B,(L [6,3,2] [] [5] [(L [3,2] [] [6] [(T 2 [] [10])]),(L [6,2] [] [4] [])]),(M 10),(L [8,3,2] [] [5] [(L [3,2] [] [14] [(T 2 [] [5])]),(L [3,4] [] [5] [(T 2 [] [5]),(L [5] [] [5] [(R1 2 [] 0)])]),(L [8,2] [] [5] [])]),(L [11,3,2] [] [14] [(L [11,2] [] [5] [])]),(L [11,6,2] [] [5] [])])),(59,(M 30),(L [9,6,3,2] [] [4] [B,(L [6,3,2] [] [4] [(L [3,2] [] [5] [B]),B]),(M 10),(L [9,3,2] [] [5] [(L [9,2] [] [4] [])]),(L [9,6,2] [] [4] [])])),(61,B,B)]) (R2 67 [(37,(L [11,8,4,3] [] [4] [(M 10),(L [6,4,3] [2] [4,10] [(L [2,3] [] [6] [(T 2 [3] [6,4])]),(M 6),(L [6,4] [] [10] [])]),(M 10),(L [8,4,3] [] [5] [(L [2,3] [2] [4,6] [(T 2 [3,2] [6,4,10])]),(L [4,3] [] [4] [(M 6),(T 4 [] [4])]),(M 6),(L [8,4] [] [4] [])]),(L [11,2,3] [3] [6,4] [(L [11,2] [2] [4,10] [])]),(L [11,4,3] [] [5] [(M 6),(L [11,4] [] [4] [])]),(M 6),(L [11,8,4] [] [5] [])]),(L [11,8,4,4] [] [4] [(M 10),(L [6,4,2] [2] [4,10] [(L [2,2] [2] [4,6] []),(M 6)]),(M 10),(L [8,4,4] [] [5] [(L [4,2] [2] [4,6] [(M 6)]),(L [4,4] [] [4] [(M 6),(M 6)]),(M 6),(M 6)]),(L [11,2,2] [2,3] [4,6,4] []),(L [11,4,4] [] [5] [(M 6),(M 6)]),(M 6),(M 6)])),(41,(M 6),(L [9,6,2,2] [2,3] [4,6,4] [(M 10),(L [4,2,2] [2,5,2,3,2] [4,10,4,6,4,14] []),(M 410),(L [9,2,2] [2,3] [4,6,4] [])])),(43,(L [7,4,2,3] [5,2,3,2,7,2,11] [10,4,6,4,14,4,22,4] [(M 10),(L [6,2,3] [] [4] [(L [2,3] [] [5] [(T 2 [5] [10,4])]),(L [6,2] [2] [4,6] [])]),(L [9,6,4] [] [4] [(M 10),(L [9,2] [] [4] []),(M 6)])]),(L [7,4,2,2] [2,5,2,3,2,7,2,11] [4,10,4,6,4,14,4,22,4] [(M 10),(L [6,2,2] [] [4] [(L [4,2] [] [5] [(M 6)])])])),(47,(M 6),(L [11,8,4,2] [] [4] [B,(L [6,2,2] [] [4] [(L [4,2] [] [4] [(M 6)])]),(M 10),(L [6,2,2] [] [5] [(L [2,2] [2] [4,10] [])]),(L [11,2,2] [2] [4,10] []),(L [13,4,4] [] [4] [(M 10),(M 6),(L [13,4] [] [5] [])]),(M 6)])),(53,(M 54),(L [9,6,4,2] [] [5] [B,(L [6,2,2] [] [5] [(L [2,2] [] [6] [])]),(M 10),(L [9,2,2] [2] [4,14] []),(M 6)])),(59,(M 30),(L [9,6,2,2] [] [4] [B,(L [6,2,2] [] [4] [(L [2,2] [] [5] [])]),(M 10),(L [9,2,2] [] [5] [])])),(61,B,B)])) (M 30) (R2 71 [(31,(X [5,4,2,1] [(M 10)]),(X [5,4,2,2] [(M 10)])),(37,(L [11,8,4,3] [] [4] [(M 10),(L [6,2,3] [2,17,2,3] [4,34,4,6,4] [(L [2,3] [2,5,2] [4,10,4,6] [(L [4] [] [4] [(R1 2 [] 2)])]),(L [8,4] [] [5] [(L [4] [] [4] [(R1 2 [] 2)]),(L [10] [] [5] [(R1 2 [] 2)])])]),(M 10),(L [6,4,3] [13,2,3] [26,4,6,4] [(L [4,3] [] [5] [(L [3] [] [4] [(R1 2 [] 0)]),(T 4 [] [6])]),(L [6,3] [2,11,2] [4,22,4,10] [(T 6 [3] [6,4])]),(L [6,4] [2,3] [4,6,4] [])]),(L [11,4,3] [] [4] [(L [11,3] [] [10] [(T 11 [] [4])]),(L [11,4] [2] [4,34] [])]),(L [11,4,3] [] [10] [(L [11,3] [5] [10,4] [(T 11 [] [5])]),(L [11,4] [] [4] [])]),(L [13,10,5] [] [5] [(M 10),(L [15,5] [] [5] [(L [3] [] [4] [(R1 2 [] 5)]),(T 15 [] [10]),(M 10)]),(L [13,10] [] [10] []),(M 10)]),(L [11,8,4] [] [4] [])]),(L [11,8,4,4] [] [4] [(M 10),(L [6,2,2] [2,7,2,17,2,3] [4,14,4,34,4,6,4] [(L [4,2] [2] [4,6] [(L [4] [] [4] [(M 6)])])]),(M 10),(L [6,4,4] [13,2,3] [26,4,6,4] [(L [4,4] [] [5] [(L [4] [] [4] [(M 6)]),(M 6)]),(L [6,2] [2,7,2,3,2,11,2] [4,14,4,6,4,22,4,10] []),(M 6)]),(L [11,4,4] [] [4] [(L [11,2] [3,2,7,2] [6,4,14,4,10] []),(M 6)]),(L [11,4,2] [2,13,2,3,2] [4,26,4,6,4,10] [(L [11,2] [3,2,11,2,5] [6,4,22,4,10,4] [])]),(L [13,10,4] [] [5] [(M 10),(L [15,4] [] [5] [(T 2 [2,5,2,3] [4,10,4,6,4]),(M 6)]),(M 6)]),(M 6)])),(41,(M 6),(L [7,6,2,2] [3,2,7,2,5,2,3,2,11] [6,4,14,4,10,4,6,4,22,4] [(M 10),(L [6,4,4] [] [5] [(L [2,2] [2] [4,10] []),(L [6,2] [7] [14,4] []),(L [8,4] [] [5] [(T 4 [] [4])])]),(L [11,4,4] [] [5] [(M 410),(L [2,2] [2,3] [4,6,4] []),(L [11,2] [] [6] []),(L [11,4] [] [4] [])])])),(43,(L [9,6,4,3] [2] [4,26] [(M 10),(L [6,4,3] [] [5] [(L [2,3] [] [5] [(T 2 [2] [4,6])]),(L [6,3] [] [4] [(T 6 [] [5])]),(L [8,4] [] [4] [(L [6] [] [4] [(R1 2 [] 0)])])]),(M 10),(L [9,2,3] [3] [6,4] [(L [9,2] [2,3] [4,6,4] [])]),(L [11,8,3] [] [4] [(L [6,3] [] [5] [(T 6 [] [6])]),(L [11,3] [] [5] [(T 11 [] [4])]),(L [11,8] [] [4] [])]),(L [9,6,4] [2] [4,10] [])]),(L [9,6,4,2] [2] [4,26] [(M 10),(L [6,4,2] [] [5] [(L [4,2] [] [5] [(L [4] [] [5] [(M 6)])]),(L [6,2] [] [4] [])]),(M 10),(L [9,2,2] [3] [6,4] []),(L [11,8,4] [] [4] [(L [6,2] [] [5] []),(L [11,2] [] [5] []),(M 6)])])),(47,(M 6),(L [7,4,2,2] [2,7,2,11,2,3,2,5] [4,14,4,22,4,6,4,10,4] [B,(L [6,2,2] [] [5] [(L [4,2] [] [4] [(T 2 [] [5])])])])),(53,(M 54),(L [7,4,2,2] [2,3,2,5] [4,6,4,10,4] [B,(L [6,2,2] [] [10] [(L [4,2] [] [5] [(T 2 [] [4])])])])),(59,(M 30),(L [7,6,2,2] [2] [4,6] [B,(L [6,2,2] [] [5] [(L [2,2] [] [5] [])]),(L [9,2,2] [] [5] [(M 10)])])),(61,(L [7,6,2,1] [3,2] [6,4,14] [B,(L [6,2,1] [2,3] [4,6,4] [(L [2,3] [] [4] [(T 2 [] [5])])]),(L [7,2,3] [2,3] [4,6,4] [(L [9,2] [] [4] [(M 10)])])]),(L [7,4,2,2] [2,3,2] [4,6,4,14] [B,(L [4,2,2] [2,3] [4,6,4] [])])),(67,B,B)])) (M 6) (R2 101 [(29,A,A),(31,(X [5,4,2,1] [(M 10)]),(X [5,4,2,2] [(M 10)])),(37,(X [5,4,2,1] [(M 10)]),(X [5,4,2,2] [(M 10)])),(41,(M 6),(X [5,4,2,2] [(M 10)])),(43,(X [5,4,2,1] [(M 10)]),(X [5,4,2,2] [(M 10)])),(47,(M 6),(X [7,4,2,2] [(M 10),(X [6,4,2] [(L [6,4] [] [5] [(L [4] [] [58] [(R1 2 [] 3)]),(L [4] [] [6] [(R1 2 [] 0)]),(T 6 [] [10])]),(L [12,4] [2,3,2,13,2] [4,6,4,26,4,10] [(L [4] [2,3] [4,6,4] [(R1 2 [] 3)]),(L [6] [] [5] [(R1 2 [] 2),(R1 2 [] 3)]),(L [4] [5,2,67] [10,4,134,4] [(R1 2 [] 2)]),(T 12 [3] [6,4])])])])),(53,(M 54),(L [11,8,4,2] [2,5,2,3,2,7,2,31,2] [4,10,4,6,4,14,4,62,4,6] [(M 10),(L [6,4,2] [3,2,7,2] [6,4,14,4,10] [(L [4,2] [5] [10,4] [(T 2 [] [10])]),(L [8,4] [] [5] [(T 2 [2] [4,6]),(T 8 [] [4])])]),(M 10),(L [8,4,4] [] [5] [(L [4,4] [] [5] [(L [4] [] [4] [(R1 2 [] 0)]),(T 4 [] [6])]),(L [4,2] [2,7,2,3,2,5] [4,14,4,6,4,10,4] [(T 2 [2,5,2,3,2] [4,10,4,6,4,22])]),(L [8,4] [] [6] [(T 8 [3] [6,4])]),(L [8,4] [] [5] [])]),(L [11,4,4] [3] [6,4] [(L [11,4] [3] [6,4] [(L [13] [] [5] [(M 10)])]),(L [11,4] [17] [34,4] [])]),(L [11,4,4] [13,2] [26,4,6] [(L [13,4] [] [4] [(M 10),(T 13 [] [5])]),(L [11,4] [23,2] [46,4,6] [])]),(L [11,8,4] [2,3] [4,6,4] [(L [13,10] [] [5] [(M 10),(L [15] [] [5] [(R1 2 [] 2)])])])])),(59,(M 30),(L [11,6,4,2] [2,3] [4,6,4] [(M 10),(L [8,4,2] [] [5] [(L [4,2] [] [6] [(T 2 [] [4])]),(L [4,2] [] [4] [(T 2 [] [4])]),(L [8,2] [] [6] [])]),(M 10),(L [8,4,2] [] [4] [(L [4,2] [] [4] [(T 2 [] [5])]),(L [4,4] [] [5] [(T 2 [] [4]),(T 4 [] [4])]),(L [8,2] [] [34] [])]),(L [11,2,2] [2,5,2,3,2,13,2,7] [4,10,4,6,4,26,4,14,4] []),(L [11,6,2] [17,2] [34,4,10] [])])),(61,(L [11,8,4,3] [] [5] [B,(L [6,4,3] [2] [4,14] [(L [2,3] [2,3] [4,6,4] [(L [4] [] [5] [(R1 2 [] 0)])]),(L [10,3] [] [4] [(L [3] [] [5] [(R1 2 [] 3)]),(L [3] [] [5] [(R1 2 [] 3)]),(T 10 [] [6])]),(L [6,4] [] [4] [])]),(M 10),(M 122),(L [11,4,3] [] [4] [(L [11,3] [2] [4,22] [(T 11 [] [4])]),(L [11,4] [] [5] [])]),(L [11,4,3] [] [4] [(L [11,3] [] [4] [(T 11 [] [6])]),(L [11,4] [] [4] [])]),(L [11,8,3] [] [10] [(L [11,8] [] [4] [])]),(L [11,8,4] [] [6] [])]),(L [11,8,4,2] [] [5] [B,(L [6,4,2] [2] [4,14] [(L [2,2] [11,2,3] [22,4,6,4] []),(L [10,4] [] [4] [(T 2 [] [5]),(T 2 [] [5]),(M 6)])]),(M 10),(M 122),(L [11,4,4] [] [4] [(L [11,2] [2] [4,22] []),(M 6)]),(L [11,4,2] [] [4] [(L [11,2] [3] [6,4] [])]),(L [11,8,2] [2] [4,10] [])])),(67,(L [11,8,4,3] [] [4] [B,(L [6,2,3] [3,2,5] [6,4,10,4] [(L [2,1] [2,11,2,5,2,3] [4,22,4,10,4,6,4] []),(L [10,4] [] [7] [(L [4] [] [4] [(R1 2 [] 2)]),(L [4] [] [4] [(R1 2 [] 0)]),(T 10 [] [5])])]),(M 10),(L [6,4,3] [] [5] [(L [2,3] [3,2,5] [6,4,10,4] [(T 2 [2,3] [4,6,4])]),(L [6,3] [] [4] [(T 6 [] [4])]),(L [6,4] [] [6] [])]),(L [11,2,3] [3,2,5] [6,4,10,4] [(L [11,4] [] [5] [(T 11 [] [4])])]),(L [13,4,3] [] [4] [(M 10),(L [13,3] [] [4] [(T 13 [] [4])]),(L [13,4] [] [6] [])]),(L [11,8,3] [] [6] [(L [11,8] [] [22] [])]),(L [11,8,4] [] [4] [])]),(L [11,8,4,2] [] [4] [B,(L [6,2,2] [3,2,5] [6,4,10,4] [(L [2,2] [2,3] [4,6,4] [])]),(M 10),(L [6,4,2] [] [5] [(L [2,2] [3,2,5] [6,4,10,4] []),(L [6,2] [] [4] [])]),(L [11,2,2] [3,2,5] [6,4,10,4] []),(L [13,4,4] [] [4] [(M 10),(L [13,2] [] [4] []),(M 6)]),(L [11,8,2] [] [6] [])])),(71,(M 18),(L [9,6,4,2] [2] [4,26] [B,(L [6,4,2] [] [5] [(M 142),(L [6,2] [] [4] [])]),(M 10),(M 142),(L [11,6,2] [] [5] [(L [8,2] [] [5] [(T 2 [] [4])])])])),(73,(L [9,6,4,3] [2] [4,6] [B,(L [6,2,3] [3] [6,4] [(L [2,1] [11,2,3,2] [22,4,6,4,10] []),(L [6,4] [] [5] [(T 6 [] [4])])]),(M 10),(L [9,4,3] [] [5] [(L [9,3] [] [5] [(T 9 [] [10])]),(L [9,4] [] [6] [])]),(L [11,8,3] [] [5] [(L [6,1] [2,3,2,5] [4,6,4,10,4] []),(L [13,3] [] [5] [(M 730),(T 13 [] [4])]),(L [11,8] [] [4] [])]),(L [9,6,4] [] [4] [])]),(L [9,6,4,2] [2] [4,6] [B,(L [6,2,2] [3] [6,4] [(L [2,2] [2] [4,10] [])]),(M 10),(L [9,4,2] [] [5] [(L [9,2] [] [5] [])]),(L [11,8,2] [] [5] [(L [6,2] [] [4] []),(L [13,4] [] [5] [(M 730),(M 6)])])])),(79,(M 10),(L [7,6,2,2] [2,7,2,3] [4,14,4,6,4] [B,(L [6,4,2] [2] [4,10] [(L [2,2] [2] [4,6] []),(M 158)]),(L [9,2,2] [3] [6,4] [(M 10)])])),(83,(M 6),(L [7,4,2,2] [3,2,7,2,11,2,3,2,5] [6,4,14,4,22,4,6,4,10,4] [B,(L [6,4,2] [] [5] [(L [4,2] [] [4] [(T 2 [] [5])]),(L [6,2] [] [4] [])])])),(89,(M 90),(L [11,6,4,2] [] [4] [B,(L [6,2,2] [] [4] [B]),(M 10),(L [8,4,2] [] [4] [(L [4,2] [] [4] [(T 2 [] [5])]),(L [4,2] [] [5] [(T 2 [] [4])]),(L [8,4] [] [5] [(L [10] [] [5] [(R1 2 [] 0)])])]),(L [11,4,2] [] [4] [(L [11,2] [] [5] [])]),(L [11,6,2] [] [5] [])])),(97,(L [9,6,4,3] [] [5] [B,B,(M 10),B,(L [9,6,3] [] [4] [(L [9,6] [] [5] [])]),(L [11,6,4] [] [4] [(L [8,4] [] [4] [(T 4 [] [5])])])]),(L [9,6,4,2] [] [5] [B,B,(M 10),B,(L [9,6,2] [] [4] [])]))])) (M 10) (R2 191 [(23,A,A),(29,A,A),(31,A,A),(37,A,A),(41,A,A),(43,(X [5,4,2,1] [(M 10)]),A),(47,(M 6),(X [5,4,2,2] [(M 10)])),(53,(M 54),(X [5,4,2,2] [(M 10)])),(59,(M 30),(X [5,4,2,2] [(M 10)])),(61,(X [5,4,2,1] [(M 10)]),(X [5,4,2,2] [(M 10)])),(67,(X [5,4,2,1] [(M 10)]),(X [5,4,2,2] [(M 10)])),(71,(M 18),(X [5,4,2,2] [(M 10)])),(73,(X [5,4,2,1] [(M 10)]),(X [5,4,2,2] [(M 10)])),(79,(M 10),(X [5,4,2,2] [(M 10)])),(83,(M 6),(X [7,4,2,2] [(M 10),(X [6,2,2] [(L [6,4] [] [6] [(M 6),(L [4] [139] [278,4] [(M 38)]),(M 38)])])])),(89,(M 90),(X [7,4,2,2] [B,(L [8,4,4] [2,5,2] [4,10,4,22] [(L [4,2] [2,3,2] [4,6,4,26] [(M 6)]),(L [4,4] [11,2] [22,4,10] [(M 6),(L [6] [] [4] [(R1 2 [] 0)])]),(M 6),(L [10,6] [] [4] [(M 38),(T 10 [] [5])])])])),(97,(L [15,10,6,3] [61,2,3,2] [122,4,6,4,10] [B,(L [8,4,3] [] [6] [(L [4,3] [] [6] [(M 6),(T 4 [] [4])]),(L [4,3] [] [6] [(M 6),(T 4 [] [10])]),(M 6),(L [8,4] [] [4] [])]),(M 10),(L [10,6,3] [13,2] [26,4,6] [(L [6,3] [] [10] [(M 6),(L [3] [] [5] [(R1 2 [] 0)]),(T 6 [] [4])]),(L [6,3] [] [6] [(M 6),(L [3] [] [4] [(R1 2 [] 3)]),(T 6 [] [6])]),(M 38),(M 6),(L [10,3] [2,5] [4,10,4] [(T 10 [59] [118,4])]),(L [10,6] [] [10] [])]),(M 10),(L [10,6,3] [3,2,17] [6,4,34,4] [(L [4,3] [2,3] [4,6,4] [(M 6),(T 4 [2] [4,6])]),(L [6,3] [2] [4,6] [(M 6),(L [3] [59] [118,4] [(R1 2 [] 2)]),(T 6 [] [4])]),(M 38),(M 6),(L [12,3] [7] [14,4] [(L [5] [] [4] [(R1 2 [] 2),(M 10)]),(T 12 [] [4])]),(L [10,6] [] [5] [])]),(L [15,6,3] [] [5] [(M 6),(L [15,3] [] [6] [(T 15 [] [4])]),(L [15,6] [] [4] [])]),(L [17,6,5] [] [5] [(M 10),(M 6),(L [17,3] [5] [10,4] [(T 17 [] [4])]),(L [17,6] [] [4] []),(M 10)]),(M 38),(M 6),(L [17,12,5] [] [5] [(M 10),(L [17,3] [2,67] [4,134,4] [(T 17 [] [4])]),(L [17,12] [] [6] []),(M 10)]),(L [15,10,6] [] [10] [])]),(L [15,10,6,4] [2,3,2] [4,6,4,10] [B,(L [8,4,2] [2] [4,6] [(L [4,2] [] [6] [(M 6)]),(L [4,2] [] [6] [(M 6)]),(M 6)]),(M 10),(L [10,6,4] [2] [4,6] [(L [6,4] [] [10] [(M 6),(L [4] [] [5] [(M 6)]),(M 6)]),(L [6,4] [] [6] [(M 6),(L [4] [] [4] [(M 6)]),(M 6)]),(M 38),(M 6),(L [10,4] [5] [10,4] [(M 6)]),(M 6)]),(M 10),(L [10,6,4] [2,17] [4,34,4] [(L [4,2] [2,3,2,13,2,17,2,3] [4,6,4,26,4,34,4,6,4] [(M 6)]),(L [6,4] [] [6] [(M 6),(L [4] [] [4] [(M 6)]),(M 6)]),(M 38),(M 6),(L [10,4] [2,7] [4,14,4] [(M 6)]),(M 6)]),(L [15,6,4] [] [5] [(M 6),(L [15,2] [3,2,13,2,17,2] [6,4,26,4,34,4,6] []),(M 6)]),(L [17,6,4] [] [5] [(M 10),(M 6),(L [17,4] [] [4] [(M 6)]),(M 6)]),(M 38),(M 6),(L [17,12,4] [] [5] [(M 10),(L [17,4] [67] [134,4] [(M 6)]),(M 6)]),(M 6)])),(101,(M 6),(L [13,8,4,4] [5,2,3,2] [10,4,6,4,38] [B,(L [6,4,2] [2,3,2,17] [4,6,4,34,4] [(L [4,2] [11] [22,4] [(M 6)]),(M 6)]),(M 10),(L [8,4,2] [17,2,5,2,3,2] [34,4,10,4,6,4,22] [(L [4,2] [2,5] [4,10,4] [(M 6)]),(L [4,4] [3] [6,4] [(M 6),(L [6] [] [14] [(R1 2 [] 0)])]),(M 6)]),(M 10),(L [13,4,4] [2] [4,58] [(M 6),(L [15,6] [] [4] [(T 4 [] [5]),(T 15 [] [5])])]),(L [13,6,4] [] [5] [(M 6),(L [15,4] [] [4] [(L [4] [] [5] [(R1 2 [] 2)]),(T 15 [] [6])]),(L [13,6] [3] [6,4] [])]),(M 6),(L [13,10,4] [2,5] [4,10,4] [(M 38)])])),(103,(L [11,8,4,3] [7,2,3,2,11] [14,4,6,4,22,4] [B,(L [8,4,3] [] [5] [(L [4,3] [] [10] [(M 6),(T 4 [] [4])]),(L [4,3] [] [4] [(M 6),(T 4 [] [4])]),(M 6),(L [8,4] [] [4] [])]),(M 10),(L [8,4,3] [2,3] [4,6,4] [(L [4,3] [] [4] [(M 6),(T 4 [] [4])]),(L [4,3] [2] [4,34] [(M 6),(T 4 [3] [6,4])]),(M 6),(L [8,4] [3] [6,4] [])]),(L [11,4,3] [2,5] [4,10,4] [(M 6),(L [11,4] [2] [4,6] [])]),(L [15,6,3] [] [4] [(M 10),(L [4,3] [] [5] [(M 6),(T 4 [3] [6,4])]),(M 6),(L [15,3] [] [5] [(T 15 [] [4])]),(L [15,6] [] [4] [])]),(M 6),(L [13,8,4] [2] [4,10] [(M 10)])]),(L [11,8,4,2] [13,2,7,2,3,2,11] [26,4,14,4,6,4,22,4] [B,(L [8,4,2] [] [5] [(L [4,2] [] [10] [(M 6)]),(L [4,2] [] [4] [(M 6)]),(M 6)]),(M 10),(L [8,4,2] [29,2,3] [58,4,6,4] [(L [4,2] [13] [26,4] [(M 6)]),(L [4,2] [2,3,2] [4,6,4,34] [(M 6)]),(M 6)]),(L [11,4,2] [3,2,5] [6,4,10,4] [(M 6)]),(L [15,6,4] [] [4] [(M 10),(L [4,4] [] [5] [(M 6),(M 6)]),(M 6),(L [15,4] [] [5] [(M 6)]),(M 6)]),(M 6)])),(107,(M 54),(L [11,8,4,2] [2,13,2] [4,26,4,10] [B,(L [6,4,2] [3,2] [6,4,22] [(L [4,2] [] [4] [(M 6)]),(M 6)]),(M 10),(L [8,4,2] [3] [6,4] [(L [4,2] [2] [4,6] [(M 6)]),(L [4,2] [29] [58,4] [(M 6)]),(M 6)]),(L [11,4,2] [2] [4,46] [(M 6)]),(L [13,4,2] [11] [22,4] [(M 10),(M 6)]),(M 6)])),(109,(M 10),(L [13,10,4,4] [] [5] [B,(L [8,4,2] [2] [4,6] [(L [4,2] [] [6] [(M 6)]),(L [4,2] [] [5] [(M 6)]),(M 6)]),(M 10),(L [6,4,2] [2,19,2,11,2,3,2,5] [4,38,4,22,4,6,4,10,4] [(L [4,2] [] [4] [(M 6)]),(M 6)]),(M 10),(L [13,4,2] [2] [4,10] [(M 6)]),(L [13,4,2] [2] [4,6] [(M 6)]),(M 38),(M 6),(M 6)])),(113,(M 114),(L [13,8,4,4] [] [4] [B,(L [8,4,2] [] [4] [(L [4,2] [] [10] [(M 6)]),(L [4,2] [] [5] [(M 6)]),(M 6)]),(M 10),(L [6,4,2] [2,3,2,7,2] [4,6,4,14,4,10] [(L [4,2] [] [5] [(M 6)]),(M 6)]),(M 10),(L [13,4,2] [3] [6,4] [(M 6)]),(L [13,4,2] [2] [4,6] [(M 6)]),(M 6),(L [13,10,6] [] [4] [(M 38),(L [15,10] [] [4] [(T 10 [] [5])])])])),(127,(L [13,8,4,3] [] [4] [B,(L [6,4,3] [11] [22,4] [(L [4,3] [] [10] [(M 762),(T 4 [] [6])]),(M 762),(L [6,4] [3] [6,4] [])]),(M 10),(L [6,4,3] [5,2] [10,4,6] [(L [4,3] [] [4] [(M 762),(T 4 [] [5])]),(M 762),(L [6,4] [2,13] [4,26,4] [])]),(M 10),(L [13,4,1] [3,2,11,2,7,2,3] [6,4,22,4,14,4,6,4] [(M 762)]),(L [13,4,3] [] [4] [(M 762),(L [13,4] [] [5] [])]),(M 762),(L [13,8,4] [] [4] [])]),(L [13,10,4,2] [] [4] [B,(L [6,4,2] [11] [22,4] [(L [4,2] [] [10] [(M 762)]),(M 762)]),(M 10),(L [6,4,2] [5,2] [10,4,6] [(L [4,2] [] [4] [(M 762)]),(M 762)]),(M 10),(L [13,4,2] [] [4] [(M 762)]),(L [13,4,2] [] [4] [(M 762)]),(M 38),(M 762)])),(131,(M 6),(L [11,6,4,2] [2,5] [4,10,4] [B,(L [8,4,2] [] [5] [(L [2,2] [5,2,7,2,3,2,13] [10,4,14,4,6,4,26,4] []),(L [4,2] [] [4] [(M 6)]),(M 6)]),(M 10),(L [8,4,2] [] [4] [(L [4,2] [] [4] [(M 6)]),(L [4,2] [] [4] [(M 6)]),(M 6)]),(L [11,4,2] [11] [22,4] [(M 6)]),(M 6)])),(137,(M 6),(L [11,8,4,2] [] [4] [B,(L [6,2,2] [2,5,2,7,2,3,2] [4,10,4,14,4,6,4,26] [(L [2,2] [3,2,7,2,5,2] [6,4,14,4,10,4,6] [])]),(M 10),(L [6,4,2] [3] [6,4] [(L [4,2] [] [14] [(M 6)]),(M 6)]),(L [11,4,2] [2] [4,34] [(M 6)]),(L [13,4,2] [] [5] [(M 10),(M 6)]),(M 6)])),(139,(M 10),(L [13,10,6,2] [] [4] [B,(L [6,4,2] [] [4] [(L [4,2] [] [4] [(M 6)]),(M 6)]),(M 10),(L [6,4,2] [5] [10,4] [(L [4,2] [] [6] [(M 6)]),(M 6)]),(M 10),(L [13,4,2] [] [4] [(M 6)]),(L [13,4,2] [] [4] [(M 6)]),(M 38),(M 6),(L [13,10,4] [] [4] [(M 6)])])),(149,(M 150),(L [9,6,4,2] [5,2,3] [10,4,6,4] [B,(L [6,4,2] [3] [6,4] [(L [4,2] [] [4] [(M 6)]),(M 6)]),(M 10),(L [9,4,2] [5] [10,4] [(M 6)]),(M 6)])),(151,(M 38),(L [9,6,4,2] [7,2] [14,4,6] [B,(L [6,4,2] [] [4] [(L [4,2] [] [5] [(M 6)]),(M 6)]),(M 10),(L [11,4,2] [] [5] [(L [4,2] [] [4] [(M 6)]),(M 6)]),(M 6)])),(157,(L [9,6,4,3] [3,2] [6,4,10] [B,(L [6,4,1] [2] [4,6] [(L [4,3] [] [5] [(M 6),(T 4 [] [4])]),(M 6)]),(M 10),(L [11,4,3] [] [5] [(L [4,1] [2,3] [4,6,4] [(M 6)]),(M 6),(L [11,4] [] [6] [])]),(M 6),(L [11,6,4] [2] [4,6] [(L [8,4] [] [4] [(T 4 [] [5])])])]),(L [9,6,4,2] [3,2] [6,4,10] [B,(L [6,4,2] [] [6] [(L [4,2] [] [5] [(M 6)]),(M 6)]),(M 10),(L [11,4,2] [] [5] [(L [4,2] [] [4] [(M 6)]),(M 6)]),(M 6)])),(163,(L [9,6,4,3] [2,3] [4,6,4] [B,(L [6,4,1] [2,5] [4,10,4] [B,(M 6)]),(M 10),(L [9,4,1] [3,2,5] [6,4,10,4] [(M 6)]),(M 6),(L [13,8,4] [] [4] [(L [8,4] [] [5] [(T 4 [] [4])]),(M 10),(L [13,4] [] [5] [])])]),(L [9,6,4,2] [2,3] [4,6,4] [B,(L [6,4,2] [5] [10,4] [B,(M 6)]),(M 10),(L [9,4,2] [5] [10,4] [(M 6)]),(M 6)])),(167,(M 6),(L [11,8,4,2] [] [4] [B,B,(M 10),(L [8,4,2] [] [5] [(L [2,2] [2,7,2,5,2,3] [4,14,4,10,4,6,4] []),(L [2,2] [5,2,7,2,3,2,13] [10,4,14,4,6,4,26,4] []),(M 6)]),(L [11,2,2] [7,2,5,2,3,2] [14,4,10,4,6,4,22] []),(L [11,4,2] [] [5] [(M 6)]),(M 6)])),(173,(M 6),(L [9,6,4,2] [3] [6,4] [B,B,(M 10),(L [9,4,2] [] [4] [(M 6)]),(M 6)])),(179,(M 90),(L [9,6,4,2] [2] [4,10] [B,B,(M 10),(L [11,4,2] [] [5] [(L [4,2] [] [4] [(M 6)]),(M 6)]),(M 6)])),(181,(L [9,6,4,1] [2,3,2] [4,6,4,14] [B,B,(M 10),B,(M 6)]),(L [9,6,4,2] [2] [4,14] [B,B,(M 10),B,(M 6)]))])) (M 18) (K 2)) (X [5,4,1] [(M 10)]) A) A A) A A A A))
private def c5 : Cert := (L [18,12,8,4] [2,3,2,19,2,13,2] [4,6,4,38,4,26,4,6] [B,(L [10,6,2] [] [4] [(L [4,2] [2,13] [4,26,4] [(T 2 [] [4])]),(L [4,2] [11,2,29] [22,4,58,4] [(T 2 [] [5])]),(L [6,4] [] [4] [(T 2 [] [4]),(T 2 [] [4]),(T 6 [] [5])]),(L [10,2] [] [6] []),(L [10,4] [] [5] [(T 10 [] [4])])]),(L [16,8,4] [] [5] [(L [4,2] [5,2,13,2,3] [10,4,26,4,6,4] [(T 2 [] [4])]),(L [6,4] [31] [62,4] [(L [4] [] [5] [(R1 1 [] 2)]),(T 2 [2,19,2,3,2,17,2,5,2,3] [4,38,4,6,4,34,4,10,4,6,4]),(T 6 [] [4])]),(L [6,4] [] [4] [(L [4] [] [4] [(R1 1 [] 0)]),(L [4] [] [178] [(R1 1 [] 2)]),(T 6 [2] [4,86])]),(L [8,4] [] [4] [(L [4] [] [5] [(R1 1 [] 2)]),(L [4] [] [4] [(R1 1 [] 7)]),(L [4] [] [5] [(R1 1 [] 2)]),(T 8 [] [4])]),(L [6,4] [] [4] [(L [4] [] [5] [(R1 1 [] 2)]),(L [4] [] [34] [(R1 1 [] 13)]),(T 6 [2] [4,6])]),(L [6,4] [] [4] [(L [4] [] [5] [(R1 1 [] 2)]),(L [4] [] [34] [(R1 1 [] 2)]),(T 6 [2] [4,6])]),(L [16,4] [] [5] [(T 16 [] [4])]),(L [16,4] [] [34] [(T 16 [] [4])]),(L [16,4] [] [4] [(T 16 [] [4])]),(L [16,8] [] [6] [])]),(L [14,8,4] [] [4] [(L [6,2] [2] [4,14] [(T 2 [] [4]),(L [4] [] [5] [(R1 1 [] 2)])]),(L [8,4] [] [4] [(T 2 [2] [4,6]),(L [4] [] [5] [(R1 1 [] 3)]),(L [4] [] [4] [(R1 1 [] 2)]),(T 8 [] [4])]),(L [8,4] [] [4] [(T 2 [2] [4,10]),(L [4] [] [6] [(R1 1 [] 3)]),(L [4] [] [6] [(R1 1 [] 101)]),(T 8 [] [4])]),(L [8,4] [] [5] [(T 2 [61,2] [122,4,6]),(L [4] [] [10] [(R1 1 [] 7)]),(L [4] [] [10] [(R1 1 [] 17)]),(T 8 [] [5])]),(L [6,4] [2,7,2,31,2,3] [4,14,4,62,4,6,4] [(T 2 [2] [4,6]),(L [4] [] [14] [(R1 1 [] 7)]),(L [8] [] [4] [(R1 1 [] 2)])]),(L [14,2] [2] [4,6] []),(L [14,4] [] [5] [(T 14 [] [5])]),(L [14,4] [] [4] [(T 14 [] [4])]),(L [14,8] [] [6] [])]),(L [12,8,4] [5,2,19] [10,4,38,4] [(L [6,2] [2] [4,26] [(T 2 [17] [34,4]),(L [4] [] [5] [(R1 1 [] 2)])]),(L [6,4] [3,2,11] [6,4,22,4] [(T 2 [3] [6,4]),(L [4] [] [10] [(R1 1 [] 3)]),(T 6 [2,43,2] [4,86,4,38])]),(L [6,4] [11,2,3,2,7,2,17,2,3,2] [22,4,6,4,14,4,34,4,6,4,26] [(T 2 [3] [6,4]),(L [4] [] [14] [(R1 1 [] 0)]),(L [8] [] [4] [(R1 1 [] 5)])]),(L [8,4] [] [14] [(T 2 [5] [10,4]),(L [4] [] [6] [(R1 1 [] 239)]),(L [4] [] [478] [(R1 1 [] 3)]),(T 8 [] [10])]),(L [12,2] [2] [4,6] []),(L [12,4] [3,2,5] [6,4,10,4] [(T 12 [19,2,17] [38,4,34,4])]),(L [12,4] [5,2,3] [10,4,6,4] [(T 12 [3,2,5] [6,4,10,4])]),(L [12,8] [2,7,2] [4,14,4,6] [])]),(L [12,6,4] [2,5,2,19,2,3,2,37,2,7,2,3,2,89] [4,10,4,38,4,6,4,74,4,14,4,6,4,178,4] [(L [4,2] [5,2,13,2,3,2,11] [10,4,26,4,6,4,22,4] [(T 2 [] [10])]),(L [6,4] [2,19,2] [4,38,4,146] [(T 2 [5] [10,4]),(L [4] [] [6] [(R1 1 [] 2)]),(T 6 [2,3,2] [4,6,4,26])]),(L [8,4] [] [6] [(T 2 [3] [6,4]),(L [4] [] [4] [(R1 1 [] 229)]),(L [4] [] [14] [(R1 1 [] 5)]),(T 8 [] [6])]),(L [8,4] [] [4] [(L [4] [] [4] [(R1 1 [] 0)]),(L [4] [] [4] [(R1 1 [] 2)]),(L [4] [] [4] [(R1 1 [] 0)]),(T 8 [] [5])]),(L [12,4] [] [4] [(T 12 [] [5])]),(L [12,4] [47,2,97] [94,4,194,4] [(L [14] [] [5] [(R1 1 [] 2)])]),(L [12,6] [2,5,2,3,2,181,2,7,2,3,2,5,2,13] [4,10,4,6,4,362,4,14,4,6,4,10,4,26,4] [])]),(L [12,8,4] [3,2,17] [6,4,34,4] [(L [4,2] [5,2,13,2,3,2,11] [10,4,26,4,6,4,22,4] [(T 2 [5] [10,4])]),(L [6,4] [2,23,2] [4,46,4,22] [(T 2 [2] [4,6]),(L [4] [] [5] [(R1 1 [] 2)]),(T 6 [2,3,2] [4,6,4,10])]),(L [8,4] [] [5] [(T 2 [2] [4,94]),(L [4] [] [6] [(R1 1 [] 3)]),(L [4] [] [5] [(R1 1 [] 0)]),(T 8 [] [6])]),(L [8,4] [2] [4,6] [(T 2 [2] [4,6]),(L [4] [] [4] [(R1 1 [] 2)]),(L [4] [] [4] [(R1 1 [] 11)]),(T 8 [] [6])]),(L [12,2] [3] [6,4] []),(L [12,4] [2,17,2,3] [4,34,4,6,4] [(L [16] [] [4] [(R1 1 [] 2),(R1 1 [] 0)])]),(L [12,4] [2,43,2,79] [4,86,4,158,4] [(L [14] [] [4] [(R1 1 [] 89)])]),(L [12,8] [3,2,71] [6,4,142,4] [])]),(L [18,4,2] [2,13,2,3,2,11] [4,26,4,6,4,22,4] [(L [18,2] [] [4] [])]),(L [18,6,4] [5,2,3,2] [10,4,6,4,314] [(L [18,2] [2] [4,6] []),(L [18,4] [2] [4,6] [(T 18 [2] [4,6])]),(L [18,6] [2,43,2,11,2] [4,86,4,22,4,6] [])]),(L [18,8,4] [2,3,2,163] [4,6,4,326,4] [(L [18,2] [2] [4,94] []),(L [18,4] [2,5,2] [4,10,4,14] [(T 18 [2,197,2] [4,394,4,62])]),(L [20,4] [] [4] [(L [4] [] [10] [(R1 1 [] 3)]),(T 20 [] [4])]),(L [18,8] [2,181,2,3] [4,362,4,6,4] [])]),(L [22,8,4] [] [4] [(L [8,4] [] [4] [(T 2 [2] [4,6]),(L [4] [] [4] [(R1 1 [] 3)]),(L [4] [] [4] [(R1 1 [] 2)]),(T 8 [] [6])]),(L [8,4] [] [5] [(T 2 [2,3] [4,6,4]),(L [4] [] [5] [(R1 1 [] 2)]),(L [4] [] [5] [(R1 1 [] 2)]),(T 8 [] [4])]),(L [22,2] [2,3] [4,6,4] []),(L [22,4] [] [4] [(T 22 [] [4])]),(L [22,4] [] [5] [(T 22 [] [4])]),(L [22,8] [] [4] [])]),(L [18,12,2] [3] [6,4] []),(L [18,14,4] [37,2,3] [74,4,6,4] [(L [20,4] [2] [4,74] [(L [4] [] [6] [(R1 1 [] 17)]),(T 20 [2] [4,278])]),(L [18,14] [2,139,2,13] [4,278,4,26,4] [])]),(L [20,14,4] [2] [4,10] [(L [14,4] [] [5] [(L [4] [] [4] [(R1 1 [] 2)]),(T 14 [] [5])]),(L [24,4] [] [4] [(L [4] [] [5] [(R1 1 [] 0)]),(L [4] [] [5] [(R1 1 [] 2)]),(T 24 [] [4])]),(L [20,14] [] [26] [])]),(L [18,12,8] [2,3,2,29,2,97,2] [4,6,4,58,4,194,4,6] [])])
private def c6 : Cert := (R2 521 [(19,A,A),(23,A,A),(29,A,A),(31,A,A),(37,A,A),(41,A,A),(43,A,A),(47,A,A),(53,A,A),(59,A,A),(61,A,A),(67,A,A),(71,A,A),(73,A,A),(79,A,A),(83,A,A),(89,A,A),(97,A,A),(101,A,A),(103,A,A),(107,A,A),(109,A,A),(113,A,A),(127,(X [6,4,2,1] [(L [12,6,3] [2] [4,6] [(L [6,3] [] [4] [(L [3] [] [4] [(R1 2 [] 7)]),(L [3] [] [5] [(R1 2 [] 3)]),(T 6 [] [4])]),(L [6,3] [] [6] [(L [3] [] [94] [(R1 2 [] 2)]),(L [3] [] [4] [(R1 2 [] 3)]),(T 6 [] [10])]),(L [6,3] [3] [6,4] [(L [3] [] [4] [(R1 2 [] 13)]),(L [3] [] [4] [(R1 2 [] 19)]),(T 6 [] [46])]),(L [8,5] [] [4] [(L [3] [] [4] [(R1 2 [] 2)]),(L [3] [3] [6,4] [(R1 2 [] 2)]),(L [3] [] [5] [(R1 2 [] 2)]),(T 8 [] [4]),(M 10)]),(L [12,3] [] [4] [(T 12 [] [14])]),(L [12,3] [] [14] [(T 12 [] [4])]),(L [12,6] [] [74] [])])]),(X [6,4,2,2] [(L [12,6,4] [] [6] [(L [6,2] [2,47] [4,94,4] [(L [4] [] [4] [(M 3)]),(L [4] [] [5] [(M 3)])]),(L [6,4] [] [6] [(T 2 [7,2,3,2] [14,4,6,4,94]),(L [4] [] [4] [(M 3)]),(M 3)]),(L [6,4] [] [4] [(L [4] [] [4] [(M 3)]),(L [4] [] [4] [(M 3)]),(M 3)]),(L [8,4] [] [4] [(T 2 [2,3,2,5] [4,6,4,10,4]),(L [4] [] [4] [(M 3)]),(L [4] [] [5] [(M 3)]),(M 3)]),(L [12,2] [2,3,2,5] [4,6,4,10,4] []),(L [12,4] [] [14] [(M 3)]),(M 3)])])),(131,(M 6),(X [6,4,2,2] [(L [10,6,2] [5,2,3] [10,4,6,4] [(L [6,4] [] [5] [(T 2 [] [6]),(T 2 [3] [6,4]),(T 6 [] [4])]),(L [6,4] [] [4] [(T 2 [2,19] [4,38,4]),(T 2 [31,2,5] [62,4,10,4]),(T 6 [] [6])]),(L [6,4] [] [10] [(T 2 [2,11] [4,22,4]),(L [4] [] [4] [(R1 1 [] 0)]),(T 6 [] [4])]),(L [10,2] [2] [4,14] []),(L [10,4] [] [5] [(T 10 [] [4])])])])),(137,(M 6),(X [6,4,2,2] [(L [8,4,2] [2,23,2] [4,46,4,10] [(L [4,2] [2] [4,6] [(L [4] [] [4] [(R1 1 [] 0)])]),(L [4,2] [2,7] [4,14,4] [(T 2 [3] [6,4])]),(L [10,4] [] [5] [(T 2 [] [4]),(T 10 [] [4])])])])),(139,(M 10),(X [6,4,2,2] [(L [10,6,2] [] [5] [(L [4,2] [2] [4,6] [(T 2 [] [4])]),(L [4,2] [3,2] [6,4,10] [(T 2 [] [5])]),(L [6,4] [] [5] [(T 2 [] [22]),(T 2 [3] [6,4]),(M 3)]),(L [10,2] [] [22] []),(L [10,2] [] [4] [])])])),(149,(M 150),(X [6,4,2,2] [(L [8,4,2] [2] [4,26] [(L [4,2] [] [4] [(T 2 [] [5])]),(L [4,2] [3] [6,4] [(T 2 [] [4])]),(L [8,2] [3] [6,4] [])])])),(151,(X [6,4,2,1] [(L [6,4,3] [3,2,23,2,5,2,3] [6,4,46,4,10,4,6,4] [(L [4,3] [11] [22,4] [(L [3] [] [4] [(R1 2 [] 2)]),(T 4 [] [5])]),(L [6,3] [3,2,7,2,5] [6,4,14,4,10,4] [(L [8] [3] [6,4] [(R1 2 [] 5)])]),(L [8,4] [5] [10,4] [(T 4 [13] [26,4])])])]),(X [6,4,2,2] [(L [6,4,2] [3,2,23,2,5,2,3] [6,4,46,4,10,4,6,4] [(L [4,2] [11] [22,4] [(T 2 [] [4])]),(L [6,2] [3,2,7,2,5] [6,4,14,4,10,4] [])])])),(157,(X [6,4,2,1] [(L [8,6,3] [] [5] [(L [4,3] [] [4] [(L [3] [] [5] [(R1 2 [] 2)]),(T 4 [] [4])]),(L [4,3] [] [4] [(T 1 [3,2,17,2,23,2,3,2,13,2,5] [6,4,34,4,46,4,6,4,26,4,10,4]),(T 4 [] [4])]),(L [8,1] [2,23,2,3,2,13,2,5,2,3,2,7] [4,46,4,6,4,26,4,10,4,6,4,14,4] []),(L [10,3] [] [5] [(L [3] [] [4] [(R1 2 [] 2)]),(T 10 [] [4])]),(L [8,6] [] [4] [])])]),(X [6,4,2,2] [(L [8,6,2] [] [5] [(L [4,2] [] [4] [(L [4] [] [5] [(M 3)])]),(L [4,2] [] [4] [(T 2 [] [4])]),(L [8,2] [] [4] []),(L [10,4] [] [5] [(T 2 [] [4]),(M 3)])])])),(163,(X [6,4,2,1] [(L [6,4,3] [17,2,23,2] [34,4,46,4,6] [(L [4,3] [] [4] [(L [3] [] [10] [(R1 2 [] 0)]),(T 4 [] [4])]),(L [8,3] [] [5] [(T 1 [2,7,2,3,2,11,2,5] [4,14,4,6,4,22,4,10,4]),(T 8 [2] [4,6])]),(L [6,4] [11,2,3] [22,4,6,4] [])])]),(X [6,4,2,2] [(L [6,4,2] [17,2,23,2] [34,4,46,4,6] [(L [4,2] [] [4] [(T 2 [] [10])]),(L [8,2] [] [5] [(T 2 [] [4])])])])),(167,(M 6),(X [6,4,2,2] [(L [8,4,2] [] [4] [(L [4,2] [] [10] [(T 2 [] [34])]),(L [4,2] [] [6] [(T 2 [] [10])]),(L [8,2] [] [6] [])])])),(173,(M 6),(X [6,4,2,2] [(L [6,4,2] [2,5] [4,10,4] [(L [4,2] [2] [4,34] [(T 2 [] [4])]),(L [8,2] [] [5] [(T 2 [] [22])])])])),(179,(M 90),(X [6,4,2,2] [(L [8,4,2] [2] [4,6] [(L [4,2] [] [6] [(T 2 [] [4])]),(L [4,2] [] [4] [(T 2 [] [26])]),(L [8,2] [] [5] [])])])),(181,(X [6,4,2,1] [(L [6,4,3] [2,3] [4,6,4] [(L [4,3] [] [10] [(L [3] [] [5] [(R1 2 [] 2)]),(T 4 [] [6])]),(L [6,3] [2,3] [4,6,4] [(T 6 [2,5] [4,10,4])]),(L [6,4] [3,2,5] [6,4,10,4] [])])]),(X [6,4,2,2] [(L [6,4,2] [2,3] [4,6,4] [(L [4,2] [] [10] [(T 2 [] [5])]),(L [6,2] [2,3] [4,6,4] [])])])),(191,(M 6),(X [6,4,2,2] [(L [8,6,2] [] [5] [(L [4,2] [] [4] [(T 2 [] [4])]),(L [4,2] [] [6] [(T 2 [] [6])]),(L [8,2] [] [4] []),(L [10,2] [] [5] [(T 2 [] [4])])])])),(193,(X [6,4,2,1] [(L [6,4,3] [2,3] [4,6,4] [(L [4,3] [] [4] [(T 1 [5,2] [10,4,6]),(L [6] [] [4] [(R1 2 [] 0)])]),(L [6,1] [2,5,2,3] [4,10,4,6,4] []),(L [8,4] [] [4] [(T 4 [] [5])])])]),(X [6,4,2,2] [(L [6,4,2] [2,3] [4,6,4] [(L [4,2] [] [4] [(T 2 [] [6])]),(L [6,2] [3] [6,4] [])])])),(197,(M 18),(X [6,4,2,2] [(L [6,4,2] [2] [4,6] [(L [4,2] [] [4] [(T 2 [] [4])]),(L [8,2] [] [5] [(T 2 [] [4])])])])),(199,(M 50),(X [6,4,2,2] [(L [6,4,2] [2] [4,6] [(L [4,2] [] [14] [(T 2 [] [4])]),(L [8,2] [] [4] [(T 2 [] [5])])])])),(211,(X [8,4,2,1] [(L [6,4,1] [7,2,3] [14,4,6,4] [(L [4,3] [] [5] [(T 1 [3] [6,4]),(T 4 [5] [10,4])]),(L [6,1] [2,3] [4,6,4] [])]),(X [6,2,1] [(X [4,1] [(L [3] [] [4] [(R1 2 [] 2)])])])]),(X [8,4,2,2] [(L [6,4,2] [3] [6,4] [(L [4,2] [] [5] [(T 2 [] [4])]),(L [6,2] [3] [6,4] [])]),(X [6,2,2] [(X [4,2] [(T 2 [3,2,13,2,29] [6,4,26,4,58,4])])])])),(223,(X [8,6,2,1] [(L [8,4,3] [] [4] [(L [4,3] [] [14] [(T 1 [5] [10,4]),(L [6] [] [4] [(R1 2 [] 0)])]),(L [4,3] [] [5] [(T 1 [5] [10,4]),(T 4 [] [4])]),(L [8,1] [5,2] [10,4,6] []),(L [8,4] [] [5] [])]),(X [6,4,1] [(L [6,3] [] [4] [(L [3] [] [22] [(R1 2 [] 2)]),(L [3] [] [4] [(R1 2 [] 3)]),(T 6 [] [4])]),(L [12,3] [] [4] [(L [3] [] [34] [(R1 2 [] 2)]),(L [3] [] [10] [(R1 2 [] 3)]),(L [3] [] [62] [(R1 2 [] 3)]),(T 12 [] [14])])]),(X [8,4,1] [(X [10,1] [(X [3] [(R1 2 [] 2)])])])]),(X [8,4,2,2] [(L [8,4,2] [] [4] [(L [4,2] [] [14] [(T 2 [] [4])]),(L [4,2] [] [5] [(T 2 [] [4])]),(L [8,2] [] [6] [])]),(X [6,4,2] [(L [6,4] [] [4] [(T 2 [2] [4,22]),(L [4] [] [4] [(M 3)]),(M 3)]),(L [12,4] [] [4] [(L [4] [] [34] [(M 3)]),(L [4] [] [10] [(M 3)]),(L [4] [] [62] [(M 3)]),(M 3)])])])),(227,(M 6),(X [8,6,2,2] [(L [6,4,2] [5] [10,4] [(L [4,2] [] [4] [(T 2 [] [5])]),(L [6,2] [2] [4,6] [])]),(X [6,4,2] [(L [6,2] [2] [4,14] [(T 2 [] [4]),(T 2 [3] [6,4])]),(L [12,4] [] [4] [(L [4] [] [4] [(R1 1 [] 0)]),(T 2 [5,2,3] [10,4,6,4]),(L [4] [] [5] [(R1 1 [] 2)]),(T 12 [] [6])])]),(X [8,4,2] [(L [20,4] [] [10] [(L [4] [] [4] [(R1 1 [] 2)]),(L [4] [] [5] [(R1 1 [] 71)]),(L [4] [] [122] [(R1 1 [] 2)]),(L [4] [] [4] [(R1 1 [] 2)]),(L [4] [] [4] [(R1 1 [] 3)]),(L [4] [] [5] [(R1 1 [] 5)]),(T 20 [2] [4,134])])])])),(229,(M 10),(X [8,6,2,2] [(L [6,4,2] [2] [4,6] [(L [4,2] [] [5] [(T 2 [] [5])]),(L [6,2] [2] [4,14] [])]),(X [8,4,2] [(L [6,2] [2] [4,10] [(T 2 [2] [4,6]),(L [4] [] [4] [(M 3)])]),(L [8,4] [3] [6,4] [(L [4] [] [4] [(M 3)]),(L [4] [] [22] [(M 3)]),(L [4] [] [4] [(M 3)]),(M 3)]),(L [10,4] [] [5] [(T 2 [2,3] [4,6,4]),(M 3)])]),(X [8,4,2] [(L [16,4] [2,5] [4,10,4] [(L [4] [] [5] [(M 3)]),(L [4] [] [4] [(M 3)]),(L [4] [] [4] [(M 3)]),(L [4] [] [4] [(M 3)]),(M 3)])])])),(233,(M 18),(X [8,6,2,2] [(L [6,4,2] [3] [6,4] [(L [4,2] [2] [4,26] [B]),(L [6,2] [11] [22,4] [])]),(L [12,6,4] [] [5] [(L [4,2] [2,3,2,13,2] [4,6,4,26,4,22] [(T 2 [] [4])]),(L [6,4] [2] [4,34] [(T 2 [3] [6,4]),(L [4] [] [34] [(R1 1 [] 2)]),(T 6 [] [5])]),(L [6,4] [] [4] [(T 2 [3] [6,4]),(L [4] [] [4] [(R1 1 [] 7)]),(T 6 [] [4])]),(L [6,4] [] [6] [(T 2 [2] [4,26]),(T 2 [2,3,2,17,2,5,2,3,2,23,2,59,2,3,2,5] [4,6,4,34,4,10,4,6,4,46,4,118,4,6,4,10,4]),(T 6 [] [14])]),(L [12,2] [2] [4,26] []),(L [12,4] [3] [6,4] [(T 12 [] [4])]),(L [12,6] [] [6] [])]),(X [8,4,2] [(L [14,2] [2,3,2,5,2,17,2,3] [4,6,4,10,4,34,4,6,4] [(T 2 [19,2] [38,4,14]),(T 2 [3,2,31] [6,4,62,4]),(T 2 [2,3,2,5] [4,6,4,10,4])])])])),(239,(M 30),(X [8,6,2,2] [(L [6,4,2] [7] [14,4] [B,(L [6,2] [2] [4,26] [])]),(L [10,6,2] [13,2,5] [26,4,10,4] [(L [6,2] [] [4] [(T 2 [2] [4,6]),(T 2 [] [5])]),(L [6,4] [] [5] [(T 2 [] [34]),(T 2 [2,3] [4,6,4]),(T 6 [] [6])]),(L [6,2] [2,3] [4,6,4] [(T 2 [2] [4,10]),(T 2 [2,19] [4,38,4])]),(L [10,2] [] [4] []),(L [10,4] [] [4] [(L [12] [] [4] [(R1 1 [] 0)])])]),(L [16,6,4] [101,2,11,2,3,2] [202,4,22,4,6,4,194] [(L [6,4] [] [4] [(T 2 [2] [4,10]),(L [4] [] [14] [(R1 1 [] 43)]),(T 6 [] [6])]),(L [6,4] [2] [4,6] [(T 2 [2,5] [4,10,4]),(L [4] [] [6] [(R1 1 [] 5)]),(T 6 [7] [14,4])]),(L [8,4] [] [5] [(T 2 [2] [4,6]),(L [4] [] [6] [(R1 1 [] 2)]),(L [4] [] [4] [(R1 1 [] 2)]),(T 8 [] [74])]),(L [6,4] [5] [10,4] [(T 2 [5,2] [10,4,122]),(L [4] [] [46] [(R1 1 [] 5)]),(T 6 [3,2] [6,4,38])]),(L [16,2] [2,61] [4,122,4] []),(L [16,4] [2,7,2,5,2] [4,14,4,10,4,6] [(L [18] [2] [4,6] [(R1 1 [] 7)])]),(L [16,6] [2,11,2,19,2,3] [4,22,4,38,4,6,4] [])])])),(241,(X [8,6,4,1] [(L [8,4,3] [] [4] [B,(L [4,3] [] [5] [B,(T 4 [] [4])]),B,(L [8,4] [] [5] [])]),(L [10,6,3] [3] [6,4] [(L [6,3] [] [6] [(L [3] [] [46] [(R1 2 [] 2)]),(L [3] [] [5] [(R1 2 [] 2)]),(T 6 [] [4])]),(L [6,3] [] [4] [(L [3] [] [4] [(R1 2 [] 2)]),(L [3] [] [4] [(R1 2 [] 0)]),(T 6 [] [5])]),(L [6,3] [] [4] [(L [3] [] [4] [(R1 2 [] 3)]),(L [3] [] [5] [(R1 2 [] 2)]),(T 6 [] [4])]),(L [10,3] [] [5] [(T 10 [] [4])]),(L [10,3] [] [4] [(T 10 [] [4])]),(L [10,6] [] [5] [])]),(L [16,6,3] [2,3] [4,6,4] [(L [6,3] [] [4] [(L [3] [] [6] [(R1 2 [] 3)]),(L [3] [] [4] [(R1 2 [] 2)]),(T 6 [] [4])]),(L [6,3] [] [14] [(L [3] [] [6] [(R1 2 [] 0)]),(L [3] [] [4] [(R1 2 [] 2)]),(T 6 [] [58])]),(L [6,3] [] [4] [(L [3] [] [4] [(R1 2 [] 3)]),(L [3] [] [5] [(R1 2 [] 19)]),(L [8] [] [5] [(R1 2 [] 2)])]),(L [6,3] [] [4] [(L [3] [] [14] [(R1 2 [] 3)]),(L [3] [] [6] [(R1 2 [] 2)]),(T 6 [] [4])]),(L [16,3] [] [4] [(T 16 [] [4])]),(L [16,3] [2] [4,6] [(T 16 [3] [6,4])]),(L [18,6] [] [4] [(L [8] [] [4] [(R1 2 [] 0)])])]),(X [10,6,1] [(L [12,3] [2,5,2,107,2,3,2,43,2,71] [4,10,4,214,4,6,4,86,4,142,4] [(L [3] [2] [4,62] [(R1 2 [] 7)]),(L [5] [] [4] [(R1 2 [] 2),(R1 2 [] 3)]),(L [3] [3,2,271] [6,4,542,4] [(R1 2 [] 3)]),(T 12 [5] [10,4])])])]),(X [8,6,4,2] [(L [8,4,2] [] [4] [B,(L [4,2] [] [5] [B]),B]),(L [10,6,2] [43,2,3] [86,4,6,4] [(L [6,2] [] [6] [(T 2 [] [46]),(L [4] [] [5] [(M 3)])]),(L [6,4] [] [4] [(T 2 [13] [26,4]),(L [4] [] [4] [(M 3)]),(M 3)]),(L [6,2] [3] [6,4] [(T 2 [] [4]),(L [4] [] [5] [(M 3)])]),(L [10,2] [] [5] []),(L [10,4] [] [4] [(M 3)])]),(L [16,6,4] [2,3] [4,6,4] [(L [6,2] [5,2,3,2,7] [10,4,6,4,14,4] [(T 2 [] [6]),(T 2 [2,11,2,3] [4,22,4,6,4])]),(L [6,4] [] [14] [(T 2 [2] [4,6]),(L [4] [] [4] [(M 3)]),(M 3)]),(L [6,4] [] [4] [(T 2 [43] [86,4]),(L [4] [] [5] [(M 3)]),(M 3)]),(L [6,4] [] [4] [(T 2 [2] [4,14]),(L [4] [] [6] [(M 3)]),(M 3)]),(L [16,2] [7] [14,4] []),(L [16,4] [2] [4,6] [(M 3)]),(M 3)]),(X [10,6,2] [(L [12,4] [2,107,2,3,2,43,2,71] [4,214,4,6,4,86,4,142,4] [(L [4] [] [62] [(M 3)]),(L [4] [] [4] [(M 3)]),(L [4] [] [4] [(M 3)]),(M 3)])])])),(251,(M 18),(X [8,6,4,2] [B,(L [10,6,2] [2] [4,6] [(L [6,2] [] [4] [(T 2 [] [4]),(L [4] [] [5] [(R1 1 [] 2)])]),(L [6,4] [] [5] [(T 2 [] [46]),(T 2 [] [4]),(T 6 [] [4])]),(L [6,2] [] [5] [(T 2 [] [4]),(T 2 [] [4])]),(L [10,2] [] [4] []),(L [10,2] [3] [6,4] [])]),(L [16,6,4] [] [5] [(L [6,2] [5] [10,4] [(T 2 [] [10]),(L [4] [] [4] [(R1 1 [] 0)])]),(L [6,2] [2] [4,14] [(T 2 [2] [4,6]),(L [4] [] [4] [(R1 1 [] 0)])]),(L [6,2] [2] [4,14] [(T 2 [3] [6,4]),(L [4] [] [5] [(R1 1 [] 2)])]),(L [6,2] [3] [6,4] [(T 2 [] [4]),(T 2 [3] [6,4])]),(L [16,2] [2] [4,10] []),(L [16,2] [2] [4,26] []),(L [16,6] [] [4] [])]),(L [14,10,4] [2,31,2,13,2,3] [4,62,4,26,4,6,4] [(L [10,2] [53,2,3] [106,4,6,4] [(T 2 [2,3] [4,6,4]),(L [4] [] [5] [(R1 1 [] 3)])]),(L [10,2] [2,5,2,29,2] [4,10,4,58,4,6] [(L [4] [] [4] [(R1 1 [] 0)]),(T 2 [5,2,71,2] [10,4,142,4,6])]),(L [10,4] [7] [14,4] [(T 2 [2,23,2] [4,46,4,38]),(T 2 [2,53,2,3] [4,106,4,6,4]),(L [12] [] [4] [(R1 1 [] 0)])]),(L [14,4] [2,7,2,3] [4,14,4,6,4] [(L [16] [] [4] [(R1 1 [] 3)])]),(L [16,4] [17] [34,4] [(L [4] [] [6] [(R1 1 [] 7)]),(T 16 [3] [6,4])]),(L [16,10] [2,31] [4,62,4] [(L [12] [] [5] [(R1 1 [] 2)])])])])),(257,(M 6),(K 5)),(263,(M 6),(L [14,10,6,2] [2,7,2,17,2,3,2,5,2,61,2,3,2] [4,14,4,34,4,6,4,10,4,122,4,6,4,22] [B,(L [8,6,2] [2,3] [4,6,4] [(L [4,2] [11] [22,4] [(T 2 [] [6])]),(L [6,4] [] [5] [(T 2 [] [10]),(T 2 [] [4]),(T 6 [] [4])]),(L [10,2] [] [5] [(T 2 [] [4])]),(L [10,2] [] [4] [(T 2 [] [4])])]),(L [10,6,2] [3,2,17] [6,4,34,4] [(L [4,2] [11,2,3] [22,4,6,4] [(T 2 [] [6])]),(L [6,4] [] [5] [(T 2 [3] [6,4]),(L [4] [] [4] [(R1 1 [] 2)]),(T 6 [] [22])]),(L [6,4] [] [6] [(T 2 [11] [22,4]),(T 2 [2,3] [4,6,4]),(T 6 [] [5])]),(L [10,2] [3] [6,4] []),(L [10,2] [2,11,2] [4,22,4,10] [])]),(L [10,6,2] [31,2,5,2,3,2,61] [62,4,10,4,6,4,122,4] [(L [4,2] [11,2,23,2] [22,4,46,4,6] [(T 2 [] [4])]),(L [6,2] [2,3,2,7] [4,6,4,14,4] [(T 2 [3] [6,4]),(L [4] [] [4] [(R1 1 [] 2)])]),(L [6,4] [] [166] [(T 2 [3] [6,4]),(T 2 [2,11,2,89] [4,22,4,178,4]),(T 6 [] [5])]),(L [10,2] [2] [4,6] []),(L [10,4] [2,11] [4,22,4] [(T 10 [2] [4,6])])]),(L [10,6,4] [2,89] [4,178,4] [(L [6,2] [2] [4,26] [(T 2 [] [74]),(T 2 [2] [4,6])]),(L [6,2] [5,2,3,2] [10,4,6,4,26] [(T 2 [3] [6,4]),(T 2 [5,2,11,2] [10,4,22,4,6])]),(L [6,4] [] [4] [(T 2 [] [10]),(L [4] [] [10] [(R1 1 [] 2)]),(T 6 [] [5])]),(L [10,2] [2] [4,14] []),(L [14,4] [] [5] [(T 2 [2,5,2,7,2] [4,10,4,14,4,6]),(T 2 [2,7,2,3] [4,14,4,6,4]),(T 14 [] [4])]),(L [10,6] [31,2] [62,4,6] [])]),(L [14,4,2] [2,13,2,3] [4,26,4,6,4] [(L [14,2] [] [4] [])]),(L [16,6,2] [2,19,2,7,2] [4,38,4,14,4,6] [(L [6,4] [] [6] [(T 2 [] [6]),(T 2 [3,2,7,2] [6,4,14,4,122]),(T 6 [] [10])]),(L [16,2] [3] [6,4] []),(L [16,2] [61,2,3,2,17] [122,4,6,4,34,4] [])]),(L [16,6,4] [] [4] [(L [6,2] [89,2,3,2,7] [178,4,6,4,14,4] [(T 2 [] [14]),(L [4] [] [6] [(R1 1 [] 2)])]),(L [16,2] [7] [14,4] []),(L [16,4] [2] [4,6] [(T 16 [3] [6,4])]),(L [16,6] [] [26] [])]),(L [14,10,2] [2] [4,34] []),(L [16,10,4] [2,5,2] [4,10,4,62] [(L [12,4] [] [5] [(T 2 [2,5,2,3,2] [4,10,4,6,4,74]),(T 12 [] [4])]),(L [18,12] [] [4] [(L [12] [] [5] [(R1 1 [] 37)]),(T 18 [] [4])])])])),(269,(M 270),(L [16,10,6,2] [5,2] [10,4,6] [B,(L [8,6,2] [3] [6,4] [(L [6,2] [] [4] [(T 2 [] [4]),(T 2 [] [5])]),(L [4,2] [2,3] [4,6,4] [(T 2 [] [4])]),(L [8,2] [5] [10,4] []),(L [10,2] [] [4] [(T 2 [] [5])])]),(L [10,6,2] [2] [4,6] [(L [6,2] [2] [4,6] [(T 2 [] [14]),(T 2 [] [4])]),(L [6,2] [2] [4,6] [(T 2 [] [4]),(T 2 [3] [6,4])]),(L [10,6] [] [7] [(T 2 [] [4]),(T 2 [] [4]),(T 2 [] [4]),(T 2 [] [4]),(T 10 [] [4]),(T 10 [] [4])]),(L [10,2] [] [6] []),(L [10,2] [2] [4,6] [])]),(L [10,6,2] [2,47] [4,94,4] [(L [4,2] [2,7,2] [4,14,4,6] [(T 2 [] [26])]),(L [6,2] [2] [4,6] [(T 2 [] [4]),(L [4] [] [5] [(R1 1 [] 2)])]),(L [6,2] [2] [4,38] [(T 2 [] [6]),(T 2 [3,2] [6,4,22])]),(L [10,2] [] [4] []),(L [10,2] [2,5] [4,10,4] [])]),(L [8,6,2] [2,5,2,3,2,29,2,59,2,3,2,5,2,7,2,3] [4,10,4,6,4,58,4,118,4,6,4,10,4,14,4,6,4] [(L [4,2] [19,2,3] [38,4,6,4] [(T 2 [] [6])]),(L [6,2] [13] [26,4] [(T 2 [] [4]),(T 2 [2] [4,6])]),(L [10,2] [] [4] [(T 2 [2] [4,86])]),(L [10,2] [2,13] [4,26,4] [(T 2 [5] [10,4])])]),(L [10,6,4] [2] [4,10] [(L [4,2] [3,2,37] [6,4,74,4] [(T 2 [] [4])]),(L [6,2] [2] [4,6] [(T 2 [] [6]),(T 2 [3] [6,4])]),(L [6,4] [] [5] [(T 2 [] [4]),(T 2 [2] [4,6]),(T 6 [] [6])]),(L [10,4] [] [4] [(T 10 [] [5])]),(L [10,2] [2,5] [4,10,4] []),(L [12,6] [] [4] [(T 6 [] [5])])]),(L [16,4,2] [2,37,2] [4,74,4,26] [(L [16,2] [] [4] [])]),(L [16,6,4] [] [5] [(L [16,2] [] [4] []),(L [16,2] [5] [10,4] []),(L [16,6] [] [4] [])]),(L [16,6,4] [] [38] [(L [16,2] [2] [4,6] []),(L [16,2] [2] [4,14] []),(L [16,6] [] [5] [])]),(L [16,10,2] [] [4] []),(L [16,10,2] [5,2] [10,4,14] [])])),(271,(M 34),(L [14,10,6,2] [2,3,2] [4,6,4,34] [B,(L [10,6,2] [] [5] [(L [4,2] [3] [6,4] [(T 2 [] [10])]),(L [4,2] [2] [4,6] [(T 2 [] [5])]),(L [6,2] [] [4] [(T 2 [] [4]),(T 2 [] [4])]),(L [10,2] [] [34] []),(L [10,2] [] [5] [])]),(L [12,8,4] [] [4] [(L [6,2] [] [6] [(T 2 [] [6]),(T 2 [] [5])]),(L [6,2] [] [14] [(T 2 [] [10]),(T 2 [] [4])]),(L [6,2] [] [4] [(T 2 [] [26]),(T 2 [2] [4,6])]),(L [6,4] [] [5] [(T 2 [] [6]),(T 2 [] [6]),(M 3)]),(L [12,2] [] [6] []),(L [12,2] [3] [6,4] []),(L [12,2] [] [5] []),(M 3)]),(L [10,6,2] [67,2] [134,4,6] [(L [4,2] [2,7,2] [4,14,4,38] [(T 2 [] [4])]),(L [6,2] [2] [4,62] [(T 2 [3] [6,4]),(T 2 [3] [6,4])]),(L [4,2] [5,2,3,2,41,2,17,2,3,2,5,2,11,2,3] [10,4,6,4,82,4,34,4,6,4,10,4,22,4,6,4] [(T 2 [] [6])]),(L [10,2] [] [4] []),(L [10,2] [5,2] [10,4,22] [])]),(L [10,6,2] [3] [6,4] [(L [4,2] [3,2,11] [6,4,22,4] [(T 2 [] [38])]),(L [6,4] [] [5] [(T 2 [] [4]),(T 2 [5] [10,4]),(M 3)]),(L [6,4] [] [5] [(T 2 [] [5]),(T 2 [2] [4,6]),(M 3)]),(L [10,2] [] [4] []),(L [10,2] [2] [4,38] [])]),(L [16,6,2] [] [4] [(L [6,4] [] [4] [(T 2 [] [4]),(T 2 [] [22]),(M 3)]),(L [16,2] [] [4] []),(L [16,2] [] [22] [])]),(L [16,6,2] [2] [4,38] [(L [6,4] [] [4] [(T 2 [] [6]),(T 2 [3] [6,4]),(M 3)]),(L [16,2] [] [6] []),(L [18,4] [] [4] [(T 2 [] [5]),(M 3)])]),(L [18,6,4] [] [5] [(L [6,2] [2] [4,10] [(T 2 [] [4]),(T 2 [19] [38,4])]),(L [6,2] [5] [10,4] [(T 2 [2] [4,10]),(T 2 [3] [6,4])]),(L [18,2] [2] [4,10] []),(L [18,2] [3] [6,4] []),(M 3)]),(L [16,12,4] [] [4] [(L [10,2] [] [5] []),(L [16,2] [] [5] []),(M 3)]),(L [16,10,4] [2] [4,6] [(L [10,4] [] [5] [(M 3)]),(M 3)])])),(277,(L [14,10,6,3] [3] [6,4] [B,(L [8,4,3] [3,2] [6,4,10] [(L [4,3] [2] [4,14] [(T 1 [2,5,2,3,2,19,2,11] [4,10,4,6,4,38,4,22,4]),(T 4 [] [5])]),(L [6,3] [] [5] [(L [3] [] [4] [(R1 2 [] 2)]),(L [3] [] [4] [(R1 2 [] 2)]),(T 6 [] [6])]),(L [8,3] [7] [14,4] [(T 8 [3] [6,4])]),(L [10,6] [] [5] [(L [6] [] [4] [(R1 2 [] 0)]),(T 10 [] [5])])]),(L [8,4,3] [7,2,3,2,47,2,19,2,3,2] [14,4,6,4,94,4,38,4,6,4,26] [(L [4,3] [5,2] [10,4,6] [(T 1 [2,3,2,11,2,5,2,3,2,17,2,7,2,3,2,5,2] [4,6,4,22,4,10,4,6,4,34,4,14,4,6,4,10,4,62]),(T 4 [3] [6,4])]),(L [6,3] [] [34] [(L [3] [] [4] [(R1 2 [] 2)]),(L [3] [] [4] [(R1 2 [] 17)]),(T 6 [] [10])]),(L [10,3] [] [14] [(L [3] [] [5] [(R1 2 [] 29)]),(T 10 [] [14])]),(L [10,6] [] [6] [(T 4 [2,11,2,3,2] [4,22,4,6,4,10]),(T 10 [] [4])])]),(L [10,6,3] [] [5] [(L [4,3] [7,2] [14,4,6] [(L [3] [] [4] [(R1 2 [] 3)]),(L [6] [] [4] [(R1 2 [] 0)])]),(L [8,3] [] [4] [(L [3] [] [4] [(R1 2 [] 0)]),(L [3] [] [4] [(R1 2 [] 5)]),(L [3] [] [5] [(R1 2 [] 2)]),(T 8 [] [4])]),(L [4,3] [2,11,2,3,2,37,2,5] [4,22,4,6,4,74,4,10,4] [(L [3] [] [4] [(R1 2 [] 3)]),(T 4 [3,2,5,2,7,2,3] [6,4,10,4,14,4,6,4])]),(L [10,3] [] [4] [(T 10 [] [10])]),(L [10,3] [37] [74,4] [(T 10 [] [4])]),(L [10,6] [] [6] [])]),(L [8,6,3] [3,2,7,2,5,2] [6,4,14,4,10,4,6] [(L [4,3] [2,3] [4,6,4] [(L [3] [] [5] [(R1 2 [] 2)]),(L [6] [] [10] [(R1 2 [] 0)])]),(L [6,3] [] [6] [(L [3] [] [10] [(R1 2 [] 7)]),(L [3] [] [26] [(R1 2 [] 2)]),(T 6 [] [5])]),(L [10,3] [] [4] [(L [3] [] [4] [(R1 2 [] 2)]),(T 10 [] [4])]),(L [10,3] [] [34] [(L [3] [] [5] [(R1 2 [] 2)]),(T 10 [] [5])]),(L [8,6] [13,2,3,2,5] [26,4,6,4,10,4] [])]),(L [14,6,3] [] [4] [(L [14,3] [] [4] [(T 14 [] [22])]),(L [14,3] [] [4] [(T 14 [2] [4,10])]),(L [14,6] [] [4] [])]),(L [14,6,3] [2] [4,6] [(L [14,3] [] [6] [(T 14 [] [6])]),(L [16,3] [] [4] [(L [3] [] [5] [(R1 2 [] 2)]),(T 16 [] [4])]),(L [14,6] [2] [4,10] [])]),(L [14,4,3] [2,3,2,7,2,5,2,3] [4,6,4,14,4,10,4,6,4] [(L [14,3] [2] [4,6] [(T 14 [] [4])]),(L [14,6] [] [5] [(L [16] [] [4] [(R1 2 [] 0)])])]),(L [16,10,3] [] [5] [(L [10,3] [] [4] [(T 10 [] [4])]),(L [16,10] [] [4] [])]),(L [14,10,3] [5] [10,4] [(L [14,10] [] [10] [])]),(L [14,10,6] [2] [4,22] [])]),(L [14,10,6,2] [2,3] [4,6,4] [B,(L [8,4,2] [3,2] [6,4,10] [(L [4,2] [2] [4,14] [(T 2 [] [4])]),(L [6,2] [] [5] [(T 2 [] [4]),(T 2 [] [4])]),(L [8,2] [7] [14,4] [])]),(L [8,4,2] [7,2,3,2,47,2,19,2,3,2] [14,4,6,4,94,4,38,4,6,4,26] [(L [4,2] [5,2] [10,4,6] [(T 2 [] [62])]),(L [6,2] [] [34] [(T 2 [] [4]),(T 2 [5] [10,4])]),(L [10,2] [] [14] [(T 2 [] [5])])]),(L [10,6,2] [] [5] [(L [4,2] [7,2] [14,4,6] [(T 2 [] [4])]),(L [8,4] [] [4] [(T 2 [] [4]),(T 2 [] [4]),(T 2 [] [5]),(M 3)]),(L [4,2] [2,11,2,3,2,37,2,5] [4,22,4,6,4,74,4,10,4] [(T 2 [] [4])]),(L [10,2] [] [4] []),(L [10,2] [37] [74,4] [])]),(L [8,6,2] [3,2,7,2,5,2] [6,4,14,4,10,4,6] [(L [4,2] [2,3] [4,6,4] [(T 2 [] [5])]),(L [6,2] [2] [4,6] [(T 2 [2] [4,10]),(T 2 [] [26])]),(L [10,2] [] [4] [(T 2 [] [4])]),(L [10,2] [2] [4,34] [(T 2 [] [5])])]),(L [14,6,2] [] [4] [(L [14,2] [] [4] []),(L [14,2] [] [4] [])]),(L [14,6,2] [2] [4,6] [(L [14,2] [] [6] []),(L [16,4] [] [4] [(T 2 [] [5]),(M 3)])]),(L [14,4,2] [17,2,3,2,7,2,5,2,3] [34,4,6,4,14,4,10,4,6,4] [(L [14,2] [2] [4,6] [])]),(L [16,10,4] [] [5] [(L [10,2] [] [4] []),(M 3)]),(L [14,10,2] [5] [10,4] [])])),(281,(M 6),(L [14,8,6,2] [2,7,2,3,2] [4,14,4,6,4,94] [B,(L [8,4,2] [2,3] [4,6,4] [(L [6,2] [] [4] [(T 2 [] [4]),(T 2 [] [5])]),(L [4,2] [2] [4,6] [(T 2 [] [4])]),(L [8,2] [] [4] [])]),(L [8,4,2] [2,5,2,11,2,3,2,41] [4,10,4,22,4,6,4,82,4] [(L [4,2] [2] [4,6] [(T 2 [] [6])]),(L [6,2] [2] [4,10] [(T 2 [] [6]),(T 2 [] [4])]),(L [10,2] [] [4] [(T 2 [] [4])])]),(L [10,6,2] [] [14] [(L [6,4] [] [5] [(T 2 [] [34]),(T 2 [] [5]),(T 6 [] [4])]),(L [6,2] [2] [4,14] [(T 2 [] [4]),(T 2 [11] [22,4])]),(L [4,2] [3,2,29,2,5,2] [6,4,58,4,10,4,6] [(T 2 [] [4])]),(L [10,2] [] [4] []),(L [10,2] [] [10] [])]),(L [12,6,4] [] [4] [(L [6,2] [] [4] [(T 2 [] [10]),(T 2 [] [4])]),(L [4,2] [5,2,3,2,31] [10,4,6,4,62,4] [(T 2 [] [6])]),(L [6,2] [] [5] [(T 2 [2] [4,26]),(L [4] [] [4] [(R1 1 [] 0)])]),(L [6,2] [] [5] [(T 2 [] [4]),(T 2 [5] [10,4])]),(L [12,2] [] [4] []),(L [12,2] [5] [10,4] []),(L [12,6] [] [5] [])]),(L [14,6,2] [] [10] [(L [14,2] [] [4] []),(L [14,2] [] [5] [])]),(L [14,4,2] [31,2,11,2,3,2] [62,4,22,4,6,4,10] [(L [14,2] [] [58] [])]),(L [14,8,2] [2,3] [4,6,4] []),(L [16,10,4] [] [5] [(L [10,2] [] [4] [(T 2 [] [4])]),(L [16,4] [] [5] [(T 16 [] [4])]),(L [18,12] [] [5] [(T 10 [] [4]),(T 18 [] [4])])])])),(283,(L [14,10,6,3] [] [6] [B,(L [8,6,3] [2] [4,6] [(L [4,3] [] [4] [(L [3] [] [4] [(R1 2 [] 17)]),(T 4 [] [5])]),(L [4,3] [2] [4,6] [(L [3] [] [4] [(R1 2 [] 23)]),(T 4 [2] [4,6])]),(L [8,1] [2,5,2,3,2,7,2,31,2,3,2,5] [4,10,4,6,4,14,4,62,4,6,4,10,4] []),(L [10,3] [] [4] [(L [3] [] [5] [(R1 2 [] 7)]),(T 10 [] [4])]),(L [8,6] [2] [4,6] [])]),(L [10,6,3] [13] [26,4] [(L [4,3] [3] [6,4] [(L [3] [] [4] [(R1 2 [] 3)]),(L [6] [] [4] [(R1 2 [] 0)])]),(L [6,3] [] [10] [(L [3] [] [5] [(R1 2 [] 2)]),(L [3] [] [5] [(R1 2 [] 2)]),(T 6 [] [5])]),(L [6,3] [] [5] [(L [3] [] [4] [(R1 2 [] 0)]),(L [3] [] [5] [(R1 2 [] 2)]),(T 6 [] [4])]),(L [10,3] [] [74] [(T 10 [] [4])]),(L [10,3] [] [4] [(T 10 [] [6])]),(L [10,6] [] [4] [])]),(L [12,6,3] [] [4] [(L [6,3] [] [5] [(L [3] [] [6] [(R1 2 [] 2)]),(L [3] [] [4] [(R1 2 [] 23)]),(T 6 [] [4])]),(L [6,3] [] [4] [(L [3] [] [4] [(R1 2 [] 31)]),(L [3] [] [5] [(R1 2 [] 5)]),(T 6 [] [6])]),(L [4,3] [3,2,37,2,11] [6,4,74,4,22,4] [(L [3] [] [6] [(R1 2 [] 3)]),(L [6] [] [4] [(R1 2 [] 2)])]),(L [6,3] [] [5] [(L [3] [] [4] [(R1 2 [] 2)]),(L [3] [] [22] [(R1 2 [] 5)]),(T 6 [] [4])]),(L [12,3] [] [4] [(T 12 [] [46])]),(L [12,3] [] [22] [(T 12 [] [10])]),(L [12,6] [] [4] [])]),(L [8,6,3] [5,2,3,2] [10,4,6,4,34] [(L [6,3] [] [5] [(L [3] [] [6] [(R1 2 [] 2)]),(L [3] [] [4] [(R1 2 [] 3)]),(T 6 [] [4])]),(L [6,3] [] [58] [(L [3] [] [4] [(R1 2 [] 0)]),(L [3] [] [4] [(R1 2 [] 2)]),(T 6 [] [4])]),(L [8,3] [2] [4,14] [(L [10] [] [5] [(R1 2 [] 19)])]),(L [10,3] [] [4] [(L [3] [] [4] [(R1 2 [] 5)]),(T 10 [] [4])]),(L [10,6] [] [6] [(T 6 [] [5])])]),(L [14,6,3] [] [22] [(L [14,3] [] [4] [(T 14 [] [14])]),(L [14,3] [] [5] [(T 14 [] [4])]),(L [14,6] [] [10] [])]),(L [14,4,3] [2,29,2,3,2] [4,58,4,6,4,10] [(L [16,3] [] [4] [(L [3] [] [5] [(R1 2 [] 2)]),(T 16 [] [6])]),(L [14,6] [] [4] [(T 14 [3] [6,4])])]),(L [14,4,3] [2,5,2,3,2,17] [4,10,4,6,4,34,4] [(L [14,3] [7] [14,4] [(T 14 [] [5])]),(L [14,6] [3] [6,4] [(L [16] [] [5] [(R1 2 [] 2)])])]),(L [14,10,3] [] [6] [(L [14,10] [2] [4,6] [])]),(L [14,10,3] [] [4] [(L [14,10] [] [4] [])]),(L [14,10,6] [2] [4,26] [])]),(L [14,10,6,2] [2] [4,6] [B,(L [8,6,2] [2] [4,6] [(L [4,2] [] [4] [(T 2 [] [4])]),(L [4,2] [7,2] [14,4,6] [(T 2 [] [4])]),(L [8,2] [] [4] []),(L [10,2] [] [4] [(T 2 [] [5])])]),(L [10,6,2] [13] [26,4] [(L [4,2] [3] [6,4] [(T 2 [] [4])]),(L [6,2] [] [10] [(T 2 [] [5]),(T 2 [] [5])]),(L [6,2] [] [5] [(T 2 [] [4]),(T 2 [] [5])]),(L [10,2] [] [74] []),(L [10,2] [3] [6,4] [])]),(L [12,6,4] [] [4] [(L [6,2] [] [5] [(T 2 [] [6]),(T 2 [] [4])]),(L [6,2] [3] [6,4] [(T 2 [] [4]),(T 2 [] [5])]),(L [4,2] [3,2,37,2,11] [6,4,74,4,22,4] [(T 2 [] [6])]),(L [6,2] [] [5] [(T 2 [] [4]),(T 2 [2] [4,22])]),(L [12,2] [] [4] []),(L [12,2] [2] [4,22] []),(M 3)]),(L [8,6,2] [5,2,3,2] [10,4,6,4,34] [(L [6,2] [] [5] [(T 2 [] [6]),(T 2 [] [4])]),(L [6,2] [2] [4,58] [(T 2 [] [4]),(T 2 [] [4])]),(L [8,2] [2] [4,14] []),(L [10,4] [] [4] [(T 2 [] [4]),(M 3)])]),(L [14,6,2] [2] [4,22] [(L [14,2] [] [4] []),(L [14,2] [] [5] [])]),(L [14,6,2] [2] [4,10] [(L [16,2] [] [4] [(T 2 [] [5])]),(L [16,2] [] [4] [(L [4] [] [4] [(M 3)])])]),(L [14,4,2] [2,5,2,3,2,17] [4,10,4,6,4,34,4] [(L [14,2] [7] [14,4] [])]),(L [14,10,2] [] [6] []),(L [14,10,2] [3] [6,4] [])])),(293,(M 6),(L [14,10,6,2] [3] [6,4] [B,(L [10,6,2] [] [4] [(L [4,2] [5] [10,4] [(T 2 [] [5])]),(L [4,2] [3] [6,4] [(T 2 [] [4])]),(L [4,2] [] [5] [(T 2 [] [10])]),(L [10,2] [] [10] []),(L [10,2] [] [5] [])]),(L [10,6,2] [] [4] [(L [4,2] [2] [4,6] [(T 2 [] [10])]),(L [6,2] [] [4] [(T 2 [] [4]),(L [4] [] [4] [(R1 1 [] 0)])]),(L [4,2] [2,31] [4,62,4] [(T 2 [] [62])]),(L [10,2] [] [4] []),(L [10,2] [] [62] [])]),(L [10,6,2] [] [5] [(L [6,2] [] [4] [(T 2 [] [4]),(T 2 [] [5])]),(L [4,2] [2,5,2] [4,10,4,6] [(T 2 [2] [4,6])]),(L [6,2] [] [6] [(T 2 [] [6]),(T 2 [] [4])]),(L [10,2] [] [4] []),(L [10,2] [] [4] [])]),(L [10,6,2] [] [5] [(L [4,2] [5] [10,4] [(T 2 [] [6])]),(L [4,2] [2,3] [4,6,4] [(T 2 [] [4])]),(L [4,2] [2,3,2] [4,6,4,10] [(T 2 [] [5])]),(L [10,2] [] [4] []),(L [10,2] [] [4] [])]),(L [14,4,2] [2] [4,6] [(L [14,2] [] [4] [])]),(L [14,4,2] [2,7,2] [4,14,4,22] [(L [14,2] [5] [10,4] [])]),(L [16,6,2] [] [4] [(L [6,2] [] [5] [(T 2 [] [4]),(T 2 [2] [4,10])]),(L [16,2] [] [4] []),(L [16,2] [] [10] [])]),(L [14,10,2] [] [6] []),(L [16,10,2] [] [5] [(L [10,4] [] [5] [(L [12] [] [5] [(R1 1 [] 2)])])])])),(307,(L [12,8,6,3] [3,2] [6,4,10] [B,(L [8,4,1] [19,2,5,2,3,2,29,2,17] [38,4,10,4,6,4,58,4,34,4] [(L [4,1] [2,5,2,17,2,3] [4,10,4,34,4,6,4] [(M 614)]),(L [4,3] [3] [6,4] [(M 614),(T 4 [] [5])]),(M 614)]),(L [10,6,3] [] [4] [(L [4,3] [] [4] [(M 614),(T 4 [] [4])]),(L [6,3] [] [5] [(M 614),(L [3] [] [22] [(R1 2 [] 3)]),(T 6 [] [4])]),(L [6,3] [] [5] [(M 614),(L [3] [] [4] [(R1 2 [] 3)]),(T 6 [] [4])]),(M 614),(L [10,3] [] [5] [(T 10 [] [4])]),(L [10,6] [] [46] [])]),(L [8,4,3] [7,2,3] [14,4,6,4] [(L [4,3] [3] [6,4] [(M 614),(L [6] [] [5] [(R1 2 [] 2)])]),(L [6,3] [] [5] [(M 614),(L [3] [] [4] [(R1 2 [] 2)]),(T 6 [] [4])]),(M 614),(L [8,4] [5,2,3] [10,4,6,4] [])]),(L [12,4,3] [2,3] [4,6,4] [(M 614),(L [12,4] [3] [6,4] [])]),(L [12,4,3] [3,2,5] [6,4,10,4] [(M 614),(L [14,6] [] [4] [(L [6] [] [5] [(R1 2 [] 3)]),(T 14 [] [5])])]),(M 614),(L [14,8,3] [2,3] [4,6,4] [(L [10,3] [] [4] [(L [3] [] [5] [(R1 2 [] 11)]),(T 10 [] [4])]),(L [14,8] [2] [4,6] [])]),(L [14,10,6] [] [5] [(L [8,6] [2] [4,6] []),(L [14,6] [] [4] [])])]),(L [12,8,6,2] [3,2] [6,4,10] [B,(L [6,4,2] [3,2,19,2,5,2,3,2,29,2,17] [6,4,38,4,10,4,6,4,58,4,34,4] [(L [4,2] [] [4] [(M 307)]),(M 307)]),(L [10,6,2] [] [4] [(L [4,2] [] [4] [(M 307)]),(L [6,2] [] [5] [(M 307),(T 2 [] [22])]),(L [6,2] [] [5] [(M 307),(T 2 [] [4])]),(M 307),(L [10,2] [] [5] [])]),(L [8,4,2] [7,2,3] [14,4,6,4] [(L [4,2] [3] [6,4] [(M 307)]),(L [6,2] [] [5] [(M 307),(T 2 [] [4])]),(M 307)]),(L [12,4,2] [2,3] [4,6,4] [(M 307)]),(L [12,4,2] [3,2,5] [6,4,10,4] [(M 307)]),(M 307),(L [14,8,2] [2,3] [4,6,4] [(L [10,2] [] [4] [(T 2 [] [5])])])])),(311,(M 6),(L [12,8,6,2] [2,11] [4,22,4] [B,(L [8,4,2] [2] [4,22] [(L [4,2] [] [4] [(T 2 [] [6])]),(L [6,4] [] [4] [(T 2 [] [4]),(T 2 [] [5]),(T 6 [] [5])]),(L [8,2] [] [4] [])]),(L [8,4,2] [2,17] [4,34,4] [(L [4,2] [3] [6,4] [(T 2 [] [6])]),(L [6,2] [] [5] [(T 2 [] [6]),(T 2 [] [4])]),(L [8,2] [] [10] [])]),(L [8,6,2] [2] [4,6] [(L [4,2] [] [6] [(T 2 [] [4])]),(L [4,2] [2] [4,10] [(T 2 [] [5])]),(L [8,2] [3] [6,4] []),(L [10,2] [] [5] [(T 2 [] [4])])]),(L [12,4,2] [2] [4,6] [(L [14,2] [] [4] [(T 2 [] [5])])]),(L [12,4,2] [2,5] [4,10,4] [(L [12,2] [] [14] [])]),(L [12,8,2] [2] [4,10] []),(L [14,8,2] [2] [4,22] [(L [10,2] [] [4] [(T 2 [] [5])])])])),(313,(L [14,8,6,3] [2] [4,6] [B,(L [10,6,3] [] [4] [(L [4,1] [2,23,2,3,2] [4,46,4,6,4,22] [(L [3] [] [4] [(R1 2 [] 2)])]),(L [4,3] [2] [4,10] [(L [3] [] [14] [(R1 2 [] 5)]),(T 4 [] [6])]),(L [4,3] [] [5] [(L [3] [] [5] [(R1 2 [] 2)]),(T 4 [] [4])]),(L [10,3] [] [5] [(T 10 [] [4])]),(L [10,3] [] [5] [(T 10 [] [4])]),(L [10,6] [] [4] [])]),(L [10,6,3] [] [4] [(L [4,3] [3] [6,4] [(L [3] [] [4] [(R1 2 [] 2)]),(T 4 [] [22])]),(L [4,3] [5] [10,4] [(L [3] [] [5] [(R1 2 [] 0)]),(T 4 [2,3] [4,6,4])]),(L [6,3] [] [5] [(L [3] [] [4] [(R1 2 [] 0)]),(L [3] [] [4] [(R1 2 [] 2)]),(T 6 [] [4])]),(L [10,3] [] [5] [(T 10 [] [4])]),(L [10,3] [] [4] [(T 10 [] [5])]),(L [10,6] [] [4] [])]),(L [8,4,3] [19,2,3] [38,4,6,4] [(L [4,3] [31] [62,4] [(T 1 [2,17,2,3,2,11] [4,34,4,6,4,22,4]),(L [6] [] [5] [(R1 2 [] 2)])]),(L [4,3] [2] [4,6] [(L [3] [] [4] [(R1 2 [] 7)]),(T 4 [5,2] [10,4,6])]),(L [8,1] [3,2,29,2,5,2,3,2,13,2,23,2] [6,4,58,4,10,4,6,4,26,4,46,4,6] []),(L [8,4] [2,37] [4,74,4] [])]),(L [12,6,3] [] [4] [(L [6,3] [] [5] [(T 1 [3,2,11,2,5,2,3] [6,4,22,4,10,4,6,4]),(T 1 [2,3,2,7,2,31,2,3,2,5] [4,6,4,14,4,62,4,6,4,10,4]),(T 6 [] [6])]),(L [4,3] [2] [4,10] [(L [3] [] [4] [(R1 2 [] 0)]),(T 4 [5] [10,4])]),(L [6,3] [] [5] [(L [3] [] [6] [(R1 2 [] 3)]),(L [3] [] [22] [(R1 2 [] 2)]),(T 6 [] [14])]),(L [6,3] [] [5] [(L [3] [] [6] [(R1 2 [] 3)]),(L [3] [] [4] [(R1 2 [] 2)]),(T 6 [] [4])]),(L [12,3] [] [6] [(T 12 [] [6])]),(L [12,3] [] [4] [(T 12 [] [4])]),(L [12,6] [] [4] [])]),(L [14,6,3] [] [5] [(L [14,1] [3,2,11,2,5,2,3] [6,4,22,4,10,4,6,4] []),(L [16,3] [] [5] [(T 1 [3,2,7,2,31,2,3,2,5] [6,4,14,4,62,4,6,4,10,4]),(T 16 [] [6])]),(L [14,6] [] [4] [])]),(L [14,4,3] [5] [10,4] [(L [14,3] [] [10] [(T 14 [] [5])]),(L [14,4] [2] [4,46] [])]),(L [14,8,3] [3] [6,4] [(L [14,8] [3] [6,4] [])]),(L [14,10,3] [] [5] [(L [14,3] [] [4] [(T 14 [] [14])]),(L [14,10] [] [4] [])]),(L [14,10,6] [] [5] [(L [14,6] [] [4] [])])]),(L [14,8,6,2] [2] [4,6] [B,(L [10,6,2] [] [4] [(L [4,2] [2] [4,22] [(T 2 [] [4])]),(L [4,2] [2] [4,10] [(T 2 [] [14])]),(L [4,2] [] [5] [(T 2 [] [5])]),(L [10,2] [] [5] []),(L [10,2] [] [5] [])]),(L [10,6,2] [] [4] [(L [4,2] [3] [6,4] [(T 2 [] [4])]),(L [4,2] [5] [10,4] [(T 2 [] [5])]),(L [6,2] [] [5] [(T 2 [] [4]),(T 2 [] [4])]),(L [10,2] [] [5] []),(L [10,2] [] [4] [])]),(L [8,4,2] [19,2,3] [38,4,6,4] [(L [4,2] [31] [62,4] [(T 2 [] [4])]),(L [4,2] [2] [4,6] [(T 2 [] [4])]),(L [8,2] [] [6] [])]),(L [12,6,4] [] [4] [(L [6,2] [] [5] [(T 2 [] [4]),(T 2 [] [4])]),(L [4,2] [2] [4,10] [(T 2 [] [4])]),(L [6,4] [] [5] [(T 2 [] [6]),(T 2 [] [22]),(M 3)]),(L [6,2] [] [5] [(T 2 [] [6]),(T 2 [] [4])]),(L [12,2] [] [6] []),(L [12,2] [] [4] []),(M 3)]),(L [14,6,2] [] [5] [(L [14,2] [] [4] []),(L [16,4] [] [5] [(T 2 [] [4]),(M 3)])]),(L [14,4,2] [5] [10,4] [(L [14,2] [] [10] [])]),(L [14,8,2] [3] [6,4] []),(L [14,10,2] [] [5] [(L [14,2] [] [4] [])])])),(317,(M 6),(L [12,8,4,2] [2,3,2,5] [4,6,4,10,4] [B,(L [8,4,2] [2] [4,6] [(L [4,2] [] [5] [(T 2 [] [4])]),(L [4,2] [2] [4,38] [(T 2 [] [4])]),(L [8,2] [2] [4,14] [])]),(L [8,4,2] [2,17] [4,34,4] [(L [4,2] [2] [4,14] [(T 2 [] [6])]),(L [6,2] [] [5] [(T 2 [] [22]),(T 2 [3] [6,4])]),(L [8,2] [] [5] [])]),(L [8,4,2] [2,5] [4,10,4] [(L [4,2] [5] [10,4] [(T 2 [] [38])]),(L [4,2] [3] [6,4] [(T 2 [] [4])]),(L [8,2] [17] [34,4] [])]),(L [12,4,2] [2] [4,14] [(L [12,2] [2] [4,6] [])]),(L [16,6,4] [] [4] [(L [6,2] [] [4] [(T 2 [3] [6,4]),(T 2 [] [5])]),(L [6,2] [] [5] [(T 2 [] [4]),(T 2 [] [4])]),(L [16,2] [] [4] []),(L [16,2] [] [4] []),(L [16,6] [] [5] [])]),(L [12,8,2] [7] [14,4] [])])),(331,(L [12,8,4,3] [2,3] [4,6,4] [B,(L [8,4,3] [] [5] [(L [4,3] [] [4] [(T 1 [2,13,2] [4,26,4,10]),(T 4 [] [6])]),(L [4,3] [] [4] [(T 1 [7,2,3] [14,4,6,4]),(T 4 [] [34])]),(L [8,3] [3] [6,4] [(T 8 [] [4])]),(L [8,4] [] [4] [])]),(L [8,4,3] [2] [4,6] [(L [4,1] [2,3,2,7,2,13] [4,6,4,14,4,26,4] [(L [3] [] [4] [(R1 2 [] 7)])]),(L [6,3] [] [5] [(L [3] [] [4] [(R1 2 [] 0)]),(L [3] [] [4] [(R1 2 [] 2)]),(T 6 [] [6])]),(L [8,1] [2,11,2,13,2,3,2] [4,22,4,26,4,6,4,10] []),(L [8,4] [3,2] [6,4,10] [])]),(L [8,6,3] [2] [4,6] [(L [6,3] [] [4] [(L [3] [] [6] [(R1 2 [] 0)]),(L [3] [] [5] [(R1 2 [] 19)]),(T 6 [] [4])]),(L [6,3] [] [5] [(T 1 [19,2,5,2,3,2,29,2] [38,4,10,4,6,4,58,4,34]),(L [3] [] [4] [(R1 2 [] 0)]),(T 6 [] [4])]),(L [8,3] [] [5] [(T 8 [3] [6,4])]),(L [10,3] [] [4] [(L [3] [] [5] [(R1 2 [] 2)]),(T 10 [] [6])]),(L [8,6] [] [6] [])]),(L [14,6,3] [] [4] [(L [4,3] [] [5] [(T 1 [19,2,3,2,7] [38,4,6,4,14,4]),(T 4 [] [5])]),(L [14,1] [2,3,2,7] [4,6,4,14,4] []),(L [14,3] [] [5] [(T 14 [] [5])]),(L [14,6] [] [5] [])]),(L [14,6,3] [] [4] [(L [6,3] [] [5] [(T 1 [3,2,29,2,17,2,3,2] [6,4,58,4,34,4,6,4,10]),(L [3] [] [4] [(R1 2 [] 0)]),(T 6 [] [4])]),(L [14,1] [2,29,2,17,2,3,2] [4,58,4,34,4,6,4,10] []),(L [14,3] [] [5] [(T 14 [] [4])]),(L [14,6] [] [14] [])]),(L [12,8,3] [3] [6,4] [(L [14,8] [] [4] [(L [10] [] [4] [(R1 2 [] 0)])])]),(L [12,8,4] [2,3] [4,6,4] [])]),(L [12,8,4,2] [2,3] [4,6,4] [B,(L [8,4,2] [] [5] [(L [4,2] [] [4] [(T 2 [] [10])]),(L [4,2] [] [4] [(T 2 [] [4])]),(L [8,2] [3] [6,4] [])]),(L [8,4,2] [2] [4,6] [(L [4,2] [] [4] [(T 2 [] [4])]),(L [6,2] [] [5] [(T 2 [] [4]),(T 2 [] [4])]),(L [8,2] [] [10] [])]),(L [8,6,2] [2] [4,6] [(L [6,2] [] [4] [(T 2 [] [6]),(T 2 [] [5])]),(L [6,2] [] [5] [(T 2 [] [34]),(T 2 [] [4])]),(L [8,2] [] [5] []),(L [10,2] [] [4] [(T 2 [] [5])])]),(L [14,6,2] [] [4] [(L [4,2] [] [5] [(T 2 [] [4])]),(L [14,2] [] [4] []),(L [14,2] [] [5] [])]),(L [14,6,2] [] [4] [(L [6,2] [] [5] [(T 2 [] [10]),(T 2 [] [4])]),(L [14,2] [] [10] []),(L [14,2] [] [5] [])]),(L [12,8,2] [3] [6,4] [])])),(337,(L [14,8,6,3] [] [5] [B,(L [8,4,3] [2] [4,10] [(L [4,1] [2,3,2,7] [4,6,4,14,4] [(T 1 [2,3] [4,6,4])]),(L [4,1] [19,2,3,2,7] [38,4,6,4,14,4] [(L [3] [] [5] [(R1 2 [] 2)])]),(L [8,1] [2,3,2,7] [4,6,4,14,4] []),(L [8,6] [] [4] [(L [10] [] [4] [(R1 2 [] 0)])])]),(L [8,4,3] [2] [4,38] [(L [6,3] [] [4] [(L [3] [] [5] [(R1 2 [] 2)]),(L [3] [] [5] [(R1 2 [] 2)]),(T 6 [] [5])]),(L [4,3] [] [4] [(L [3] [] [5] [(R1 2 [] 0)]),(T 4 [5] [10,4])]),(L [8,3] [5] [10,4] [(L [10] [] [4] [(R1 2 [] 0)])]),(L [8,6] [] [4] [(L [10] [] [4] [(R1 2 [] 0)])])]),(L [8,4,3] [2] [4,10] [(L [4,3] [2] [4,6] [(L [3] [] [4] [(R1 2 [] 2)]),(T 4 [] [6])]),(L [4,3] [2] [4,6] [(L [3] [] [5] [(R1 2 [] 0)]),(L [6] [] [4] [(R1 2 [] 0)])]),(L [8,3] [2] [4,22] [(T 8 [] [4])]),(L [8,4] [2] [4,10] [])]),(L [10,6,3] [] [5] [(L [4,3] [7] [14,4] [(T 1 [2,7,2,3] [4,14,4,6,4]),(T 4 [] [4])]),(L [4,3] [2] [4,6] [(L [3] [] [5] [(R1 2 [] 2)]),(T 4 [2] [4,34])]),(L [4,3] [3] [6,4] [(T 1 [5,2,3,2,11,2,13] [10,4,6,4,22,4,26,4]),(T 4 [] [4])]),(L [10,1] [2,3,2,11,2,13] [4,6,4,22,4,26,4] []),(L [10,3] [] [4] [(T 10 [] [4])]),(L [10,6] [] [5] [])]),(L [14,4,3] [] [4] [(L [14,1] [2,7,2,3] [4,14,4,6,4] []),(L [14,6] [] [5] [(T 14 [] [4])])]),(L [14,4,3] [2] [4,6] [(L [14,3] [] [5] [(T 14 [] [5])]),(L [14,4] [17] [34,4] [])]),(L [14,8,1] [2,3,2,11,2,13,2] [4,6,4,22,4,26,4,6] []),(L [14,10,3] [] [5] [(L [14,3] [] [4] [(T 14 [] [4])]),(L [14,10] [] [5] [])]),(L [16,10,6] [] [4] [(L [12,6] [] [4] [(T 6 [] [5]),(T 6 [] [5])]),(L [16,6] [] [5] [])])]),(L [14,8,6,2] [] [5] [B,(L [8,4,2] [2] [4,10] [(L [4,2] [7] [14,4] [(T 2 [] [4])]),(L [4,2] [] [4] [(T 2 [] [5])]),(L [8,2] [] [4] [])]),(L [8,4,2] [2] [4,38] [(L [6,2] [] [4] [(T 2 [] [5]),(T 2 [] [5])]),(L [4,2] [] [4] [(T 2 [] [5])]),(L [8,2] [5] [10,4] [])]),(L [8,4,2] [2] [4,10] [(L [4,2] [2] [4,6] [(T 2 [] [4])]),(L [4,2] [2] [4,6] [(T 2 [] [5])]),(L [8,2] [2] [4,22] [])]),(L [10,6,2] [] [5] [(L [4,2] [7] [14,4] [(T 2 [] [4])]),(L [4,2] [2] [4,6] [(T 2 [] [5])]),(L [4,2] [3] [6,4] [(T 2 [] [4])]),(L [10,2] [] [4] []),(L [10,2] [] [4] [])]),(L [14,4,2] [] [4] [(L [14,2] [] [4] [])]),(L [14,4,2] [2] [4,6] [(L [14,2] [] [5] [])]),(L [14,8,2] [2] [4,6] []),(L [14,10,2] [] [5] [(L [14,2] [] [4] [])])])),(347,(M 6),(L [12,8,6,2] [2] [4,14] [B,(L [8,4,2] [] [5] [(L [4,2] [] [4] [(T 2 [] [4])]),(L [4,2] [23] [46,4] [(T 2 [] [4])]),(L [8,2] [] [4] [])]),(L [8,4,2] [2] [4,6] [(L [4,2] [] [10] [(T 2 [] [4])]),(L [4,2] [] [4] [(T 2 [] [4])]),(L [8,2] [] [4] [])]),(L [10,6,2] [] [4] [(L [6,2] [] [5] [(T 2 [] [4]),(T 2 [] [4])]),(L [4,2] [5] [10,4] [(T 2 [] [4])]),(L [6,2] [] [5] [(T 2 [] [4]),(T 2 [] [4])]),(L [10,2] [] [4] []),(L [10,2] [] [5] [])]),(L [12,4,2] [3] [6,4] [(L [12,2] [2] [4,6] [])]),(L [12,4,2] [2] [4,62] [(L [12,2] [11] [22,4] [])]),(L [14,8,2] [] [4] [(L [10,2] [] [4] [(T 2 [] [5])])]),(L [14,8,2] [] [4] [(L [10,2] [] [4] [(T 2 [] [5])])])])),(349,(M 50),(L [12,8,4,2] [2] [4,6] [B,(L [8,4,2] [5] [10,4] [(L [4,2] [] [6] [(T 2 [] [4])]),(L [4,2] [] [4] [(T 2 [] [4])]),(L [8,2] [] [4] [])]),(L [8,4,2] [2] [4,22] [(L [4,2] [2] [4,14] [(T 2 [] [4])]),(L [4,2] [] [4] [(T 2 [] [4])]),(L [8,2] [] [4] [])]),(L [8,4,2] [3] [6,4] [(L [4,2] [3] [6,4] [(T 2 [] [10])]),(L [6,2] [] [5] [(T 2 [] [4]),(T 2 [] [4])]),(L [10,2] [] [4] [(T 2 [] [5])])]),(L [12,6,2] [] [5] [(L [12,2] [7] [14,4] []),(L [12,2] [] [4] [])]),(L [12,4,2] [3] [6,4] [(L [12,2] [] [26] [])]),(L [12,8,2] [] [6] [])])),(353,(M 6),(L [10,8,4,2] [13,2,5,2,3] [26,4,10,4,6,4] [B,(L [8,4,2] [3] [6,4] [(L [4,2] [] [14] [(T 2 [] [4])]),(L [4,2] [] [4] [(T 2 [] [5])]),(L [8,2] [] [10] [])]),(L [10,6,2] [] [5] [(L [6,2] [] [5] [(T 2 [] [4]),(T 2 [] [4])]),(L [6,2] [] [5] [(T 2 [] [4]),(T 2 [] [4])]),(L [4,2] [] [4] [(T 2 [] [5])]),(L [10,2] [] [5] []),(L [10,2] [] [4] [])]),(L [10,4,2] [23,2,5] [46,4,10,4] [(L [10,2] [7,2] [14,4,10] [])]),(L [10,4,2] [2,11,2,3,2,7] [4,22,4,6,4,14,4] [(L [12,2] [] [5] [(T 2 [] [4])])]),(L [10,8,2] [3,2,19,2] [6,4,38,4,22] [])])),(359,(M 90),(L [12,8,4,2] [2] [4,14] [B,(L [8,4,2] [] [4] [(L [4,2] [] [4] [(T 2 [] [10])]),(L [4,2] [] [6] [(T 2 [] [4])]),(L [8,2] [] [4] [])]),(L [6,4,2] [29,2,3,2,5,2,7,2,3,2] [58,4,6,4,10,4,14,4,6,4,46] [(L [4,2] [2] [4,6] [(T 2 [] [38])]),(L [8,2] [] [10] [(T 2 [] [5])])]),(L [8,4,2] [2] [4,6] [(L [4,2] [13] [26,4] [(T 2 [] [10])]),(L [4,2] [2] [4,10] [(T 2 [] [5])]),(L [8,2] [7] [14,4] [])]),(L [12,4,2] [] [4] [(L [12,2] [] [5] [])]),(L [12,4,2] [2] [4,6] [(L [12,2] [5] [10,4] [])]),(L [12,8,2] [2] [4,6] [])])),(367,(L [12,8,4,3] [2,3] [4,6,4] [B,(L [8,4,3] [2] [4,6] [(L [4,3] [] [5] [(L [3] [] [4] [(R1 2 [] 2)]),(T 4 [3] [6,4])]),(L [4,3] [] [4] [(T 1 [2,3] [4,6,4]),(T 4 [] [5])]),(L [10,3] [] [4] [(L [3] [] [5] [(R1 2 [] 7)]),(T 10 [] [14])]),(L [8,4] [] [4] [])]),(L [8,6,3] [] [5] [(L [6,3] [] [5] [(T 1 [2,3] [4,6,4]),(L [3] [] [4] [(R1 2 [] 3)]),(T 6 [] [4])]),(L [4,3] [2] [4,6] [(T 1 [5,2,3] [10,4,6,4]),(T 4 [3] [6,4])]),(L [8,3] [2] [4,10] [(T 8 [] [5])]),(L [8,1] [11,2,5,2,3] [22,4,10,4,6,4] []),(L [8,6] [] [4] [])]),(L [10,6,3] [] [4] [(L [6,3] [] [4] [(T 1 [7,2] [14,4,22]),(L [3] [] [5] [(R1 2 [] 2)]),(T 6 [] [5])]),(L [4,3] [2] [4,6] [(L [3] [] [6] [(R1 2 [] 7)]),(T 4 [3] [6,4])]),(L [4,3] [] [5] [(T 1 [23,2,5,2] [46,4,10,4,6]),(T 4 [] [4])]),(L [10,1] [23,2,5,2] [46,4,10,4,6] []),(L [10,3] [] [5] [(T 10 [] [4])]),(L [10,6] [] [4] [])]),(L [12,4,3] [] [4] [(L [12,1] [2,11,2] [4,22,4,6] []),(L [12,6] [] [5] [(L [14] [] [5] [(R1 2 [] 2)])])]),(L [12,4,3] [2] [4,10] [(L [12,3] [] [46] [(L [14] [] [4] [(R1 2 [] 0)])]),(L [12,4] [] [5] [])]),(L [14,8,3] [] [4] [(L [10,3] [] [4] [(L [3] [] [5] [(R1 2 [] 2)]),(T 10 [] [4])]),(L [14,8] [] [4] [])]),(L [12,8,4] [3] [6,4] [])]),(L [12,8,4,2] [2,3] [4,6,4] [B,(L [8,4,2] [2] [4,6] [(L [4,2] [] [5] [(T 2 [] [4])]),(L [4,2] [] [4] [(T 2 [] [4])]),(L [10,2] [] [4] [(T 2 [] [5])])]),(L [8,6,2] [] [5] [(L [6,2] [] [5] [(T 2 [] [4]),(T 2 [] [4])]),(L [4,2] [2] [4,6] [(T 2 [] [4])]),(L [8,2] [2] [4,10] []),(L [8,2] [] [4] [])]),(L [10,6,2] [] [4] [(L [6,2] [] [4] [(T 2 [] [22]),(T 2 [] [5])]),(L [4,2] [2] [4,6] [(T 2 [] [6])]),(L [4,2] [] [5] [(T 2 [] [6])]),(L [10,2] [] [6] []),(L [10,2] [] [5] [])]),(L [12,4,2] [] [4] [(L [12,2] [] [6] [])]),(L [12,4,2] [2] [4,10] [(L [12,2] [] [46] [])]),(L [14,8,2] [] [4] [(L [10,2] [] [4] [(T 2 [] [5])])])])),(373,(M 34),(L [12,8,4,2] [2] [4,6] [B,(L [8,6,2] [] [5] [(L [4,2] [] [4] [(T 2 [] [4])]),(L [4,2] [] [4] [(T 2 [] [6])]),(L [8,2] [] [46] []),(L [10,2] [] [5] [(T 2 [] [4])])]),(L [8,4,2] [2] [4,22] [(L [4,2] [] [10] [(T 2 [] [4])]),(L [4,2] [] [5] [(T 2 [] [4])]),(L [8,2] [] [4] [])]),(L [10,6,2] [] [4] [(L [4,2] [] [5] [(T 2 [] [5])]),(L [4,2] [] [6] [(T 2 [] [26])]),(L [4,2] [] [5] [(T 2 [] [10])]),(L [10,2] [] [10] []),(L [10,2] [] [5] [])]),(L [12,4,2] [] [6] [(L [12,2] [] [4] [])]),(L [12,4,2] [2] [4,10] [(L [14,2] [] [4] [(T 2 [] [5])])]),(L [12,8,2] [17] [34,4] [])])),(379,(M 10),(L [10,6,4,2] [5,2,3,2,19,2,11,2,3,2,5] [10,4,6,4,38,4,22,4,6,4,10,4] [B,(L [8,4,2] [] [4] [(L [4,2] [] [4] [(T 2 [] [4])]),(L [4,2] [] [4] [(T 2 [] [4])]),(L [8,2] [] [22] [])]),(L [8,4,2] [5] [10,4] [(L [4,2] [2] [4,6] [(T 2 [] [4])]),(L [4,2] [2] [4,14] [(T 2 [] [4])]),(L [8,2] [] [10] [])]),(L [10,4,2] [2,3] [4,6,4] [(L [12,2] [] [5] [(T 2 [] [6])])]),(L [14,10,2] [] [4] [(L [8,2] [] [6] [(T 2 [] [6])]),(L [8,2] [] [5] [(T 2 [] [4])]),(L [14,2] [] [4] []),(L [16,2] [] [4] [(T 2 [] [5])])])])),(383,(M 6),(L [16,12,6,4] [] [4] [B,(L [8,4,2] [] [5] [(L [4,2] [] [26] [(L [4] [] [5] [(R1 1 [] 0)])]),(L [4,2] [] [10] [(T 2 [] [6])]),(L [8,2] [] [4] [])]),(L [8,4,2] [2] [4,6] [(L [6,2] [] [5] [(T 2 [] [4]),(T 2 [] [4])]),(L [6,2] [] [4] [(T 2 [] [4]),(T 2 [] [5])]),(L [10,2] [] [4] [(T 2 [] [5])])]),(L [8,4,2] [3] [6,4] [(L [4,2] [] [6] [(T 2 [] [5])]),(L [4,2] [2] [4,6] [(T 2 [] [6])]),(L [8,2] [] [6] [])]),(L [8,6,2] [] [5] [(L [4,2] [] [5] [(T 2 [] [4])]),(L [6,2] [] [4] [(T 2 [] [5]),(T 2 [] [5])]),(L [8,2] [] [10] []),(L [10,2] [] [5] [(T 2 [] [4])])]),(L [8,4,2] [] [5] [(L [4,2] [] [5] [(T 2 [] [4])]),(L [4,2] [] [4] [(T 2 [] [4])]),(L [8,2] [] [10] [])]),(L [16,4,2] [] [5] [(L [16,2] [2] [4,6] [])]),(L [16,4,2] [] [4] [(L [16,2] [] [4] [])]),(L [16,4,2] [] [5] [(L [16,2] [] [10] [])]),(L [18,6,4] [] [4] [(L [4,2] [] [5] [(T 2 [] [10])]),(L [18,2] [] [10] []),(L [18,2] [] [5] []),(L [18,6] [] [5] [])]),(L [16,12,2] [] [10] []),(L [16,12,2] [] [5] []),(L [18,12,6] [] [4] [(L [12,8] [] [4] [(T 12 [] [5])])])])),(389,(M 30),(L [12,8,4,2] [5] [10,4] [B,(L [6,4,2] [2,7,2,3] [4,14,4,6,4] [(L [4,2] [] [4] [(T 2 [] [5])]),(L [8,2] [] [4] [(T 2 [] [14])])]),(L [8,6,2] [] [5] [(L [4,2] [2] [4,6] [(T 2 [] [4])]),(L [4,2] [2] [4,46] [(T 2 [] [4])]),(L [8,2] [] [6] []),(L [10,2] [] [5] [(T 2 [] [4])])]),(L [8,4,2] [] [5] [(L [4,2] [] [4] [(T 2 [] [10])]),(L [4,2] [] [4] [(T 2 [] [4])]),(L [8,2] [3] [6,4] [])]),(L [12,4,2] [] [4] [(L [12,2] [2] [4,6] [])]),(L [12,4,2] [] [5] [(L [14,2] [] [5] [(T 2 [] [4])])]),(L [14,8,2] [] [4] [(L [10,2] [] [4] [(T 2 [] [5])])])])),(397,(L [10,8,4,1] [2,23,2,5,2,3] [4,46,4,10,4,6,4] [B,(L [8,6,3] [] [5] [(L [4,3] [] [5] [(L [3] [] [5] [(R1 2 [] 2)]),(T 4 [3] [6,4])]),(L [4,1] [5,2] [10,4,6] [(T 1 [3] [6,4])]),(L [8,3] [] [5] [(T 8 [] [4])]),(L [10,3] [] [5] [(T 1 [7] [14,4]),(T 10 [] [14])]),(L [8,6] [] [14] [])]),(L [8,4,3] [] [6] [(L [4,1] [5,2] [10,4,6] [(L [3] [] [5] [(R1 2 [] 3)])]),(L [4,1] [2,5,2] [4,10,4,6] [(L [3] [] [6] [(R1 2 [] 2)])]),(L [8,3] [] [5] [(T 8 [] [10])]),(L [8,4] [] [4] [])]),(L [10,4,1] [2,7,2,11] [4,14,4,22,4] [(L [12,3] [] [4] [(L [3] [] [5] [(R1 2 [] 3)]),(T 12 [] [4])])]),(L [12,4,3] [3] [6,4] [(L [4,3] [] [5] [(L [3] [] [4] [(R1 2 [] 0)]),(T 4 [] [4])]),(L [12,3] [] [4] [(T 12 [] [5])]),(L [14,6] [] [5] [(T 4 [] [4]),(T 14 [] [4])])]),(L [10,8,1] [2,7,2,5,2] [4,14,4,10,4,6] [])]),(L [10,8,4,2] [5,2,3] [10,4,6,4] [B,(L [8,6,2] [] [5] [(L [4,2] [] [5] [(T 2 [] [5])]),(L [4,2] [] [6] [(T 2 [] [4])]),(L [8,2] [] [5] []),(L [10,2] [] [5] [(T 2 [] [4])])]),(L [8,4,2] [] [6] [(L [4,2] [] [6] [(T 2 [] [5])]),(L [4,2] [] [6] [(T 2 [] [6])]),(L [8,2] [] [5] [])]),(L [10,4,2] [2,11] [4,22,4] [(L [12,2] [] [4] [(T 2 [] [5])])]),(L [12,4,2] [3] [6,4] [(L [4,2] [] [5] [(T 2 [] [4])]),(L [12,2] [] [4] [])]),(L [10,8,2] [2,5,2] [4,10,4,6] [])])),(401,(M 6),(L [10,8,4,2] [2,19,2,3] [4,38,4,6,4] [B,(L [6,4,2] [2,3,2,13] [4,6,4,26,4] [(L [4,2] [] [4] [(T 2 [] [6])]),(L [8,2] [] [26] [(T 2 [] [4])])]),(L [8,4,2] [] [6] [(L [4,2] [] [26] [(T 2 [] [4])]),(L [4,2] [] [6] [(T 2 [] [4])]),(L [8,2] [] [4] [])]),(L [10,4,2] [2,5] [4,10,4] [(L [10,2] [2] [4,10] [])]),(L [10,4,2] [2,17,2] [4,34,4,6] [(L [10,2] [2,13] [4,26,4] [])]),(L [12,8,2] [] [5] [(L [8,2] [] [6] [])])])),(409,(M 10),(L [10,8,4,2] [7,2,3] [14,4,6,4] [B,(L [6,4,2] [2,11,2,3] [4,22,4,6,4] [(L [4,2] [] [4] [B]),(L [8,2] [] [4] [(T 2 [] [5])])]),(L [8,4,2] [] [5] [(L [4,2] [] [4] [(T 2 [] [4])]),(L [6,2] [] [4] [(T 2 [] [5]),(T 2 [] [5])]),(L [8,2] [] [14] [])]),(L [10,4,2] [2,13] [4,26,4] [(L [14,2] [] [5] [(T 2 [] [6]),(T 2 [] [4])])]),(L [12,4,2] [] [4] [(L [6,2] [] [4] [(T 2 [] [4]),(T 2 [] [5])]),(L [12,2] [] [4] [])]),(L [12,8,2] [] [5] [(L [8,2] [] [6] [])])])),(419,(M 30),(L [12,8,4,2] [5] [10,4] [B,(L [8,4,2] [2] [4,10] [(L [4,2] [] [4] [B]),(L [4,2] [] [6] [(T 2 [] [10])]),(L [10,2] [] [4] [(T 2 [] [5])])]),(L [8,4,2] [2] [4,10] [(L [4,2] [17] [34,4] [(T 2 [] [4])]),(L [4,2] [17] [34,4] [(T 2 [] [4])]),(L [8,2] [] [4] [])]),(L [10,6,2] [] [4] [(L [6,2] [] [5] [(T 2 [] [5]),(T 2 [] [4])]),(L [4,2] [] [4] [(T 2 [] [6])]),(L [4,2] [] [5] [(T 2 [] [5])]),(L [10,2] [] [5] []),(L [10,2] [] [5] [])]),(L [12,4,2] [] [4] [(L [12,2] [] [4] [])]),(L [12,4,2] [2] [4,6] [(L [12,2] [] [4] [])]),(L [12,8,2] [2] [4,6] [])])),(421,(L [10,8,4,3] [2,11,2] [4,22,4,6] [B,(L [8,4,1] [2,3] [4,6,4] [(L [4,3] [] [4] [B,(T 4 [] [5])]),(L [6,3] [] [5] [(T 1 [11,2] [22,4,6]),(T 1 [7] [14,4]),(T 6 [] [14])]),(L [8,1] [2] [4,10] [])]),(L [6,4,1] [7,2,5,2,3,2,17] [14,4,10,4,6,4,34,4] [(L [4,3] [] [4] [(T 1 [11] [22,4]),(T 4 [] [5])]),(L [8,3] [2] [4,26] [(T 1 [7,2] [14,4,6]),(T 8 [] [5])])]),(L [10,4,1] [5,2,3,2] [10,4,6,4,14] [(L [10,1] [3,2,5] [6,4,10,4] [])]),(L [12,4,3] [3] [6,4] [(L [4,3] [] [5] [(L [3] [] [5] [(R1 2 [] 3)]),(T 4 [] [5])]),(L [12,3] [] [5] [(T 12 [] [5])]),(L [12,4] [] [5] [])]),(L [10,8,3] [3,2] [6,4,10] [(L [12,8] [] [6] [(T 8 [] [5])])]),(L [12,8,4] [2] [4,22] [(L [8,4] [] [4] [])])]),(L [10,8,4,2] [2,11,2] [4,22,4,6] [B,(L [8,4,2] [3] [6,4] [(L [4,2] [] [4] [B]),(L [6,2] [] [5] [(T 2 [] [6]),(T 2 [] [4])]),(L [8,2] [] [10] [])]),(L [6,4,2] [5,2,3,2,17] [10,4,6,4,34,4] [(L [4,2] [] [4] [(T 2 [] [4])]),(L [8,2] [2] [4,26] [(T 2 [] [6])])]),(L [10,4,2] [3,2] [6,4,14] [(L [10,2] [2,5] [4,10,4] [])]),(L [12,4,2] [3] [6,4] [(L [4,2] [] [5] [(T 2 [] [5])]),(L [12,2] [] [5] [])]),(L [10,8,2] [3,2] [6,4,10] [])])),(431,(M 54),(L [10,6,4,2] [3,2,7,2,5,2,3,2] [6,4,14,4,10,4,6,4,34] [B,(L [8,4,2] [] [4] [B,(L [4,2] [] [10] [(T 2 [] [4])]),(L [8,2] [] [4] [])]),(L [8,4,2] [] [6] [(L [4,2] [] [4] [(T 2 [] [4])]),(L [4,2] [] [4] [(T 2 [] [4])]),(L [8,2] [] [4] [])]),(L [12,4,2] [] [5] [(L [4,2] [] [4] [(T 2 [] [4])]),(L [12,2] [] [22] [])]),(L [12,8,2] [] [5] [(L [6,2] [2,7,2] [4,14,4,6] []),(L [12,2] [] [14] [])])])),(433,(L [10,8,4,1] [2,3,2,7] [4,6,4,14,4] [B,(L [6,4,1] [13,2,3,2,5] [26,4,6,4,10,4] [B,(L [8,1] [3] [6,4] [(L [3] [] [5] [B])])]),(L [8,4,1] [3,2] [6,4,10] [(L [4,1] [5,2] [10,4,6] [(T 1 [2,3] [4,6,4])]),(L [4,3] [] [4] [(T 1 [2] [4,10]),(L [6] [] [5] [(R1 2 [] 2)])]),(L [8,1] [3,2] [6,4,14] [])]),(L [10,4,1] [11,2,3] [22,4,6,4] [(L [10,1] [2,7,2] [4,14,4,6] [])]),(L [12,4,3] [] [5] [(L [4,3] [] [5] [(L [3] [] [4] [(R1 2 [] 0)]),(T 4 [] [6])]),(L [12,1] [2,3] [4,6,4] []),(L [12,4] [] [5] [])]),(L [10,8,1] [2,19,2,7] [4,38,4,14,4] [])]),(L [10,8,4,2] [2,7] [4,14,4] [B,(L [6,4,2] [2,3,2,5] [4,6,4,10,4] [B,(L [8,2] [] [4] [(T 2 [] [5])])]),(L [8,4,2] [] [10] [(L [4,2] [] [6] [(T 2 [] [4])]),(L [4,2] [] [4] [(T 2 [] [10])]),(L [8,2] [] [14] [])]),(L [10,4,2] [3] [6,4] [(L [10,2] [7,2] [14,4,6] [])]),(L [12,4,2] [] [5] [(L [4,2] [] [5] [(T 2 [] [4])]),(L [12,2] [] [4] [])]),(L [10,8,2] [2,7] [4,14,4] [])])),(439,(M 10),(L [10,8,4,2] [2,13] [4,26,4] [B,(L [6,4,2] [5,2,3] [10,4,6,4] [B,B]),(L [8,6,2] [] [4] [(L [4,2] [] [5] [(T 2 [] [6])]),(L [4,2] [] [38] [(T 2 [] [4])]),(L [8,2] [] [4] []),(L [12,2] [] [4] [(T 2 [] [5]),(T 2 [] [5])])]),(L [10,4,2] [2,7] [4,14,4] [(L [14,2] [] [4] [(T 2 [] [4]),(T 2 [] [5])])]),(L [12,4,2] [] [5] [(L [4,2] [] [10] [(T 2 [] [14])]),(L [14,2] [] [5] [(T 2 [] [4])])]),(L [10,8,2] [3] [6,4] [])])),(443,(M 6),(L [10,8,4,2] [2,3,2] [4,6,4,10] [B,(L [6,4,2] [3,2,11] [6,4,22,4] [B,B]),(L [10,6,2] [] [5] [(L [4,2] [] [4] [(T 2 [] [5])]),(L [4,2] [] [4] [(T 2 [] [5])]),(L [4,2] [] [4] [(T 2 [] [4])]),(L [10,2] [] [4] []),(L [10,2] [] [4] [])]),(L [10,4,2] [5,2] [10,4,6] [(L [10,2] [2] [4,6] [])]),(L [12,6,2] [] [4] [(L [4,2] [] [4] [(T 2 [] [26])]),(L [12,2] [2] [4,10] []),(L [14,2] [] [4] [(T 2 [] [5])])]),(L [10,8,2] [3] [6,4] [])])),(449,(M 450),(L [14,8,6,2] [] [4] [B,(L [8,4,2] [] [5] [B,(L [4,2] [] [4] [B]),B]),(L [6,4,2] [2,3,2,5] [4,6,4,10,4] [(L [6,2] [] [5] [B,(T 2 [] [4])]),(L [6,2] [2,3,2,5] [4,6,4,10,4] [])]),(L [8,4,2] [3] [6,4] [(L [4,2] [7] [14,4] [B]),(L [4,2] [] [5] [(T 2 [] [6])]),(L [8,2] [] [4] [])]),(L [10,6,2] [] [4] [(L [4,2] [] [5] [B]),(L [4,2] [] [38] [(T 2 [] [4])]),(L [4,2] [] [5] [(T 2 [] [46])]),(L [10,2] [] [4] []),(L [10,2] [] [5] [])]),(L [14,4,2] [] [5] [B]),(L [14,4,2] [] [38] [(L [14,2] [] [4] [])]),(L [14,8,2] [] [4] []),(L [14,8,2] [] [5] [])])),(457,(L [12,8,4,1] [2,3] [4,6,4] [B,B,(L [10,6,3] [] [4] [(L [4,1] [2,3] [4,6,4] [B]),(L [4,1] [2,13] [4,26,4] [(T 1 [3] [6,4])]),(L [4,3] [] [5] [(T 1 [2,5] [4,10,4]),(T 4 [] [4])]),(L [10,1] [2,5] [4,10,4] []),(L [10,3] [] [5] [(T 10 [] [4])]),(L [10,6] [] [4] [])]),(L [8,4,3] [] [4] [(L [4,3] [] [4] [B,(T 4 [] [5])]),(L [4,1] [2,3] [4,6,4] [(T 1 [3] [6,4])]),(L [8,1] [2] [4,22] []),(L [8,6] [] [5] [(L [10] [] [5] [(R1 2 [] 2)])])]),(L [12,4,1] [2] [4,6] [B]),(L [12,4,1] [2,5] [4,10,4] [(L [12,1] [2,5] [4,10,4] [])]),(L [12,8,1] [11,2] [22,4,6] [])]),(L [10,8,4,2] [2,3] [4,6,4] [B,B,(L [10,6,2] [] [4] [(L [4,2] [3] [6,4] [B]),(L [4,2] [13] [26,4] [(T 2 [] [4])]),(L [4,2] [] [5] [(T 2 [] [4])]),(L [10,2] [] [4] []),(L [10,2] [] [5] [])]),(L [10,4,2] [2] [4,6] [B]),(L [10,4,2] [2,5] [4,10,4] [(L [10,2] [2,5] [4,10,4] [])]),(L [10,8,2] [11,2] [22,4,6] [])])),(461,(M 6),(L [10,8,4,2] [2,3] [4,6,4] [B,B,(L [8,6,2] [] [4] [(L [4,2] [] [22] [B]),(L [4,2] [] [4] [(T 2 [] [4])]),(L [8,2] [] [6] []),(L [8,2] [] [5] [])]),(L [10,4,2] [3,2] [6,4,10] [B]),(L [12,6,2] [] [4] [(L [4,2] [] [4] [(T 2 [] [5])]),(L [12,2] [2] [4,14] []),(L [16,2] [] [4] [(T 2 [] [5]),(L [4] [] [4] [(R1 1 [] 0)])])]),(L [10,8,2] [2,3] [4,6,4] [])])),(463,(L [14,8,6,3] [] [5] [B,B,(L [6,4,1] [3,2,19,2,7,2] [6,4,38,4,14,4,6] [(L [4,1] [2] [4,6] [B]),(L [6,1] [2,3,2,7] [4,6,4,14,4] [])]),(L [8,4,3] [] [5] [(L [4,1] [2] [4,26] [B]),(L [4,3] [] [10] [(T 1 [5,2] [10,4,6]),(T 4 [] [5])]),(L [8,3] [] [4] [(T 8 [] [5])]),(L [8,4] [3] [6,4] [])]),(L [10,6,3] [] [5] [(L [4,1] [13,2] [26,4,6] [B]),(L [4,1] [5,2] [10,4,6] [(T 1 [3] [6,4])]),(L [4,3] [] [4] [(T 1 [2] [4,14]),(T 4 [] [5])]),(L [10,1] [2] [4,14] []),(L [10,3] [] [4] [(T 10 [] [5])]),(L [10,6] [] [5] [])]),(L [14,4,1] [13,2] [26,4,6] [B]),(L [14,4,1] [5,2] [10,4,6] [(L [14,1] [3] [6,4] [])]),(L [14,8,1] [2] [4,14] []),(L [14,10,3] [] [5] [(L [14,3] [] [4] [(T 14 [] [5])]),(L [14,10] [] [5] [])]),(L [14,8,6] [] [5] [])]),(L [14,8,6,2] [] [5] [B,B,(L [6,4,2] [19,2,7,2] [38,4,14,4,6] [(L [4,2] [] [6] [B]),(L [6,2] [3,2,7] [6,4,14,4] [])]),(L [8,4,2] [] [5] [(L [4,2] [] [26] [B]),(L [4,2] [] [10] [(T 2 [] [6])]),(L [8,2] [] [4] [])]),(L [10,6,2] [] [5] [(L [4,2] [2] [4,6] [B]),(L [4,2] [2] [4,6] [(T 2 [] [4])]),(L [4,2] [] [4] [(T 2 [] [14])]),(L [10,2] [] [14] []),(L [10,2] [] [4] [])]),(L [14,4,2] [2] [4,6] [B]),(L [14,4,2] [2] [4,6] [(L [14,2] [] [4] [])]),(L [14,8,2] [] [14] []),(L [14,10,2] [] [5] [(L [14,2] [] [4] [])])])),(467,(M 18),(L [12,8,4,2] [2] [4,10] [B,B,(L [8,4,2] [] [6] [B,(L [4,2] [] [10] [(T 2 [] [5])]),(L [8,2] [] [4] [])]),(L [8,4,2] [] [5] [B,(L [4,2] [] [26] [(T 2 [] [4])]),(L [8,2] [] [10] [])]),B,(L [12,4,2] [2] [4,6] [(L [12,2] [] [5] [])]),(L [12,8,2] [2] [4,6] [])])),(479,(M 30),(L [12,8,4,2] [] [4] [B,B,(L [6,4,2] [2,3,2] [4,6,4,26] [B,B]),(L [10,6,2] [] [5] [B,(L [4,2] [] [6] [(T 2 [] [6])]),(L [4,2] [] [4] [(T 2 [] [4])]),(L [10,2] [] [4] []),(L [10,2] [] [4] [])]),B,(L [12,4,2] [] [4] [(L [12,2] [] [4] [])]),(L [12,8,2] [] [34] [])])),(487,(L [10,6,4,1] [3,2,13,2,5,2,3] [6,4,26,4,10,4,6,4] [B,B,(L [8,6,3] [] [4] [B,(L [4,1] [3] [6,4] [B]),B,(L [10,3] [] [4] [(L [3] [] [5] [(R1 2 [] 2)]),(T 10 [] [4])]),(L [10,6] [] [5] [(T 6 [] [4])])]),B,B]),(L [10,6,4,2] [13,2,5,2,3] [26,4,10,4,6,4] [B,B,(L [8,6,2] [] [4] [B,(L [4,2] [] [4] [B]),B,(L [10,2] [] [4] [(T 2 [] [5])])]),B,B])),(491,(M 6),(L [10,6,4,2] [2,23,2,3,2] [4,46,4,6,4,26] [B,B,(L [6,4,2] [2,11,2] [4,22,4,6] [B,B]),B,B])),(499,(M 250),(L [12,8,4,2] [] [4] [B,B,(L [8,4,2] [2] [4,14] [B,(L [4,2] [] [6] [B]),B]),(L [10,6,2] [] [5] [B,(L [4,2] [] [6] [B]),(L [4,2] [] [4] [B]),B,(L [10,2] [] [4] [])]),B,(L [14,6,2] [] [5] [(L [4,2] [] [4] [B]),B,(L [14,2] [] [4] [])]),B])),(503,(M 18),(L [10,6,4,2] [5,2,11,2,3] [10,4,22,4,6,4] [B,B,B,B,B])),(509,B,B)])
private def c7 : Cert := (S7 7 (P 11 (P 13 (P 17 (P 19 (P 23 (P 29 (P 31 (P 37 (P 41 B (M 6) (R2 53 [(43,(L [8,6,2,3] [] [5] [(L [4,2,3] [2] [4,14] [(L [6,2] [] [4] [(T 2 [] [5])])]),(L [6,2,3] [] [4] [(L [4,3] [] [7] [(T 1 [3] [6,4]),(T 4 [] [6])]),(L [6,2] [] [4] [])]),(L [8,2,3] [] [4] [(L [8,2] [] [4] [])]),(L [8,6,2] [] [5] [])]),(L [8,6,2,2] [] [5] [(L [4,2,2] [2] [4,14] []),(L [6,4,2] [] [4] [(L [4,4] [] [7] [(T 2 [] [4]),(M 3)]),(L [6,4] [] [4] [(M 3)])]),(L [8,2,2] [] [4] [])])),(47,(M 6),(L [8,6,2,2] [2] [4,10] [B,(L [6,2,2] [] [5] [B]),(L [10,2,2] [] [4] [(L [2,2] [] [5] [])])]))])) (R2 59 [(41,(M 6),(L [8,6,3,2] [] [4] [(L [6,3,2] [] [4] [(L [3,2] [] [5] [(T 2 [] [6])]),(L [6,2] [] [4] [])]),(L [4,3,2] [2] [4,14] [(L [6,2] [] [5] [(T 2 [] [4])])]),(L [8,1,2] [2,3,2,7] [4,6,4,14,4] []),(L [8,6,2] [3] [6,4] [])])),(43,(L [8,6,3,3] [] [5] [(L [4,3,1] [2,5] [4,10,4] [(L [6,3] [] [4] [(L [3] [] [5] [(R1 2 [] 2)]),(T 6 [] [5])])]),(L [6,3,3] [] [5] [(L [3,3] [] [4] [(T 1 [2,5] [4,10,4]),(T 3 [] [5])]),(L [6,3] [] [4] [(T 6 [] [10])]),(L [6,3] [] [4] [])]),(L [8,3,3] [] [4] [(L [8,3] [] [4] [(T 8 [] [4])]),(L [8,3] [] [6] [])]),(L [8,6,3] [3] [6,4] [(L [8,6] [] [5] [])]),(L [10,6,3] [] [5] [(L [6,3] [] [4] [])])]),(L [8,6,3,2] [] [5] [(L [4,3,2] [5] [10,4] [(L [6,2] [] [4] [(T 2 [] [5])])]),(L [6,3,2] [] [5] [(L [3,2] [3] [6,4] [(T 2 [] [4])]),(L [6,4] [] [4] [(M 6)])]),(L [10,3,2] [] [4] [(L [3,4] [] [4] [(T 2 [] [4]),(M 6)]),(L [10,2] [] [4] [])]),(L [8,6,2] [3] [6,4] [])])),(47,(M 6),(L [8,4,3,2] [2,3] [4,6,4] [B,(L [6,3,2] [] [4] [(L [3,2] [] [5] [(T 2 [] [4])]),(L [6,2] [] [5] [])]),(L [8,6,2] [] [5] [(L [8,2] [] [4] [])])])),(53,B,B)]) (R2 59 [(41,(M 6),(L [8,6,2,2] [] [4] [(L [6,2,2] [] [4] [(L [2,2] [] [5] [])]),(L [4,2,2] [3,2] [6,4,14] []),(L [8,2,2] [] [4] [])])),(43,(L [8,6,2,3] [] [5] [(L [4,2,1] [2,5] [4,10,4] []),(L [6,2,3] [] [5] [(L [2,3] [3] [6,4] [(T 2 [] [5])]),(L [6,2] [] [4] [])]),(L [10,2,3] [] [4] [(L [4,3] [] [4] [(M 6),(T 4 [] [6])]),(L [10,2] [] [6] [])]),(L [10,6,4] [] [5] [(L [6,2] [] [4] []),(M 6)])]),(L [8,6,2,2] [] [5] [(L [4,2,2] [5] [10,4] []),(L [6,2,2] [] [5] [(L [2,2] [3] [6,4] [])]),(L [10,2,2] [] [4] [(L [4,4] [] [4] [(M 3),(M 3)])])])),(47,(M 6),(L [8,4,2,2] [2,3] [4,6,4] [B,(L [6,2,2] [] [4] [(L [2,2] [] [5] [])])])),(53,B,B)])) (R2 67 [(37,(L [12,8,3,3] [] [4] [(L [4,3,3] [2,5,2,3] [4,10,4,6,4] [(L [6,3] [] [6] [(L [3] [] [4] [(R1 2 [] 5)]),(L [8] [] [4] [(R1 2 [] 0)])]),(L [8,3] [] [5] [(T 3 [] [6]),(T 3 [] [4])])]),(L [6,3,3] [3] [6,4] [(L [3,3] [] [6] [(L [3] [] [4] [(R1 2 [] 5)]),(T 3 [] [6])]),(L [6,3] [] [6] [(T 6 [] [4])]),(L [8,3] [] [5] [(T 3 [] [4])])]),(L [8,3,3] [] [5] [(L [3,3] [] [4] [(L [3] [] [4] [(R1 2 [] 2)]),(T 3 [] [6])]),(L [5,3] [] [5] [(L [3] [] [6] [(R1 2 [] 2)]),(M 74),(T 5 [] [4])]),(L [8,3] [] [4] [(T 8 [] [4])]),(L [8,3] [] [6] [])]),(L [8,5,3] [] [4] [(L [3,3] [] [4] [(L [3] [] [10] [(R1 2 [] 5)]),(T 3 [] [10])]),(L [3,3] [] [5] [(L [3] [] [10] [(R1 2 [] 0)]),(T 3 [] [4])]),(L [8,3] [] [10] [(T 8 [] [5])]),(M 74),(L [8,5] [] [5] [])]),(L [12,3,3] [] [4] [(L [12,3] [] [10] [(T 12 [] [10])]),(L [12,3] [] [10] [])]),(L [12,3,3] [] [5] [(L [12,3] [] [10] [(T 12 [] [5])]),(L [12,3] [] [4] [])]),(L [12,8,3] [] [10] [(L [12,8] [] [5] [])]),(L [12,8,3] [] [5] [])]),(L [10,8,3,4] [] [4] [(L [6,3,2] [] [4] [(L [3,4] [] [4] [(L [4] [] [4] [(M 6)]),(M 6)]),(L [6,2] [] [6] [])]),(L [6,3,2] [3] [6,4] [(L [3,2] [2] [4,6] [(T 2 [] [4])]),(L [6,2] [2] [4,6] [])]),(L [6,3,4] [] [5] [(L [3,4] [] [4] [(L [4] [] [4] [(M 6)]),(M 6)]),(L [6,2] [3] [6,4] []),(M 6)]),(L [10,3,2] [3] [6,4] [(L [10,2] [2] [4,10] [])]),(L [10,3,4] [] [5] [(L [10,2] [2] [4,10] []),(M 6)]),(L [10,8,2] [] [10] []),(M 6)])),(41,(M 6),(L [8,6,3,2] [2,3] [4,6,4] [(L [6,3,2] [] [5] [(L [3,2] [] [6] [(T 2 [] [4])]),(L [6,2] [] [4] [])]),(L [6,3,2] [] [14] [(L [3,4] [] [4] [(L [4] [] [5] [(R1 2 [] 2)]),(T 3 [] [5])]),(L [6,2] [] [6] [])]),(L [8,3,2] [2,3] [4,6,4] [(L [8,2] [2] [4,14] [])]),(L [8,6,2] [2] [4,6] [])])),(43,(L [8,4,3,3] [2,3,2,7,2,11] [4,6,4,14,4,22,4] [(L [6,3,3] [] [6] [(L [3,3] [] [5] [(L [3] [] [5] [(R1 2 [] 2)]),(T 3 [] [4])]),(L [6,3] [] [6] [(T 6 [] [4])]),(L [6,3] [] [4] [])]),(L [6,3,3] [] [10] [(L [3,3] [] [6] [(L [3] [] [4] [(R1 2 [] 5)]),(T 3 [] [6])]),(L [6,3] [] [5] [(T 6 [] [5])]),(L [10,5] [] [7] [(T 3 [] [4]),(M 62),(T 10 [] [4])])]),(L [10,6,3] [] [4] [(L [6,3] [] [5] [(L [3] [] [4] [(R1 2 [] 2)]),(L [8] [] [4] [(R1 2 [] 0)])]),(L [10,3] [] [4] [(T 10 [] [6])]),(L [10,6] [] [4] [])]),(L [10,6,3] [] [4] [(L [8,5] [] [4] [(T 3 [] [4]),(T 3 [] [5]),(T 8 [] [5])]),(L [10,3] [] [4] [])])]),(L [8,4,3,2] [2,3,2,7,2,11] [4,6,4,14,4,22,4] [(L [6,3,2] [] [6] [(L [3,2] [] [5] [(T 2 [] [5])]),(L [6,2] [] [6] [])]),(L [6,3,2] [] [10] [(L [3,2] [] [6] [(T 2 [] [4])]),(L [6,2] [] [5] [])]),(L [10,6,2] [] [4] [(L [6,2] [] [5] [(T 2 [] [4])]),(L [10,2] [] [4] [])])])),(47,(M 6),(L [10,8,3,4] [] [4] [(L [4,3,2] [2,3] [4,6,4] [(L [4,2] [2] [4,10] [])]),(L [4,3,2] [7,2] [14,4,6] [(L [6,2] [] [10] [(T 2 [] [5])])]),(L [6,3,2] [] [5] [(L [3,2] [] [4] [(T 2 [] [4])]),(L [6,2] [] [4] [])]),(L [10,3,2] [] [10] [(L [10,2] [] [4] [])]),(L [12,5,4] [] [4] [(L [3,2] [] [5] [(T 2 [] [4])]),(L [12,4] [] [5] [(T 12 [] [4])]),(L [14,4] [] [4] [(T 2 [] [5]),(T 14 [] [5])]),(L [12,5] [] [5] [])]),(L [10,8,4] [] [5] [(L [12,8] [] [5] [(T 8 [] [7])])]),(L [12,8,3] [] [4] [(L [8,3] [] [5] [])])])),(53,(M 54),(L [10,6,3,2] [] [5] [(L [6,3,2] [] [5] [B,B]),(L [4,3,2] [2,3] [4,6,4] [(L [4,2] [3] [6,4] [])]),(L [4,3,2] [2,7] [4,14,4] [(L [8,4] [] [7] [(T 2 [] [5]),(T 2 [] [4]),(T 8 [] [4])])]),(L [10,3,2] [] [14] [(L [10,2] [] [5] [])]),(L [10,6,2] [] [5] [])])),(59,(M 30),(L [8,6,3,2] [] [4] [B,(L [4,3,2] [5] [10,4] [(L [6,2] [] [4] [(T 2 [] [5])])]),(L [8,3,2] [] [5] [(L [8,2] [] [4] [])]),(L [8,6,2] [3] [6,4] [])])),(61,B,B)]) (R2 67 [(37,(L [10,8,4,3] [] [4] [(L [6,2,3] [3] [6,4] [(L [4,3] [] [4] [(M 6),(T 4 [] [6])]),(L [8,4] [] [5] [(T 2 [] [4]),(M 6)])]),(L [6,2,3] [2,3] [4,6,4] [(L [2,3] [2] [4,6] [(T 2 [2] [4,6])]),(L [8,4] [] [5] [(L [4] [] [4] [(M 6)]),(M 6)])]),(L [6,4,3] [] [5] [(L [4,3] [] [4] [(M 6),(T 4 [] [6])]),(M 6),(L [6,4] [2] [4,6] [])]),(L [10,2,3] [2,3] [4,6,4] [(L [10,2] [2] [4,10] [])]),(L [10,4,3] [] [5] [(M 6),(L [10,4] [] [4] [])]),(M 6),(L [10,8,4] [] [5] [])]),(L [10,8,4,4] [] [4] [(L [6,2,2] [3] [6,4] [(L [4,4] [] [4] [(M 3),(M 3)])]),(L [6,2,2] [5,2,3] [10,4,6,4] [(L [4,2] [2] [4,6] [(M 3)])]),(L [6,4,4] [] [5] [(L [4,4] [] [4] [(M 3),(M 3)]),(M 3),(M 3)]),(L [10,4,2] [3] [6,4] [(M 3)]),(L [10,4,4] [] [5] [(M 3),(M 3)]),(M 3),(M 3)])),(41,(M 6),(L [8,6,2,2] [2,3] [4,6,4] [(L [6,2,2] [] [5] [(L [2,2] [] [6] [])]),(L [6,2,2] [2] [4,14] [(L [4,4] [] [4] [(M 3),(T 4 [] [5])])]),(L [8,2,2] [2,3] [4,6,4] [])])),(43,(L [8,4,2,3] [2,3,2,7,2,11] [4,6,4,14,4,22,4] [(L [6,2,3] [] [6] [(L [2,3] [] [5] [(T 2 [] [4])]),(L [6,2] [7] [14,4] [])]),(L [6,2,3] [] [10] [(L [2,3] [] [6] [(T 2 [2] [4,6])]),(L [10,4] [] [7] [(T 2 [] [4]),(M 62),(M 6)])]),(L [10,6,4] [] [4] [(L [8,4] [] [4] [(L [4] [] [4] [(M 6)]),(T 2 [] [5]),(M 6)]),(L [10,2] [] [4] []),(M 6)])]),(L [8,4,2,2] [2,3,2,7,2,11] [4,6,4,14,4,22,4] [(L [6,2,2] [] [6] [(L [2,2] [] [5] [])]),(L [6,2,2] [2] [4,10] [(L [2,2] [] [6] [])])])),(47,(M 6),(L [10,8,4,4] [] [4] [(L [4,2,2] [2,3] [4,6,4] []),(L [4,2,2] [2,7,2] [4,14,4,6] []),(L [6,2,2] [] [5] [(L [2,2] [] [4] [])]),(L [10,2,2] [2] [4,10] []),(L [12,4,4] [] [4] [(L [2,2] [] [5] []),(M 3),(L [12,4] [] [5] [])]),(M 3),(L [12,8,4] [] [4] [(L [8,4] [] [5] [])])])),(53,(M 54),(L [10,6,4,2] [] [5] [(L [6,2,2] [] [5] [B]),(L [4,2,2] [2,3] [4,6,4] []),(L [4,2,2] [2,7] [4,14,4] []),(L [10,2,2] [] [14] []),(M 3)])),(59,(M 30),(L [8,6,2,2] [] [4] [B,(L [4,2,2] [5] [10,4] []),(L [10,2,2] [] [5] [(L [4,2] [] [5] [(M 3)])])])),(61,B,B)])) (M 30) (R2 71 [(31,(X [6,4,2,1] [(L [10,4,5] [] [4] [(L [4,5] [] [4] [(L [3] [5] [10,4] [(R1 2 [] 2)]),(T 4 [] [5]),(T 4 [] [5])]),(L [4,5] [] [4] [(L [3] [2,3] [4,6,4] [(R1 2 [] 13)]),(T 4 [] [10]),(T 4 [] [4])]),(M 62),(L [10,3] [3] [6,4] [(T 10 [] [6])]),(L [10,4] [] [6] []),(L [10,4] [] [4] [])])]),(X [6,4,2,2] [(L [10,4,4] [] [4] [(L [4,4] [] [4] [(L [4] [] [4] [(M 3)]),(M 3)]),(L [6,4] [] [4] [(L [4] [] [4] [(M 3)]),(L [6] [] [4] [(M 3),(M 5)]),(M 3)]),(M 31),(L [10,4] [] [4] [(M 3)]),(M 3)])])),(37,(L [12,8,4,3] [] [4] [(L [6,2,3] [7] [14,4] [(L [2,3] [3] [6,4] [(T 2 [] [4])]),(L [6,2] [2] [4,10] [])]),(L [8,4,3] [] [6] [(L [4,3] [] [4] [(L [3] [] [5] [(R1 2 [] 2)]),(T 4 [] [5])]),(L [4,3] [] [5] [(L [3] [] [34] [(R1 2 [] 2)]),(T 4 [] [4])]),(L [8,3] [] [6] [(T 8 [] [10])]),(L [8,4] [] [6] [])]),(L [6,4,3] [11,2,5] [22,4,10,4] [(L [4,3] [] [14] [(L [3] [] [4] [(R1 2 [] 0)]),(T 4 [] [5])]),(L [8,3] [] [5] [(L [3] [2] [4,6] [(R1 2 [] 0)]),(T 8 [] [4])]),(L [8,4] [] [5] [(T 4 [] [4])])]),(L [8,4,3] [] [5] [(L [4,3] [] [5] [(L [3] [] [4] [(R1 2 [] 2)]),(T 4 [] [4])]),(L [4,3] [] [4] [(L [3] [] [4] [(R1 2 [] 2)]),(T 4 [] [6])]),(L [8,3] [] [6] [(T 8 [] [4])]),(L [8,4] [] [5] [])]),(L [12,4,3] [] [4] [(L [12,3] [] [10] [(T 12 [] [4])]),(L [12,4] [] [34] [])]),(L [12,4,3] [] [10] [(L [12,3] [5] [10,4] [(T 12 [] [5])]),(L [12,4] [] [4] [])]),(L [14,8,5] [] [5] [(L [12,5] [] [7] [(L [3] [] [4] [(R1 2 [] 2)]),(L [3] [] [4] [(R1 2 [] 5)]),(T 12 [] [10]),(M 10)]),(L [14,8] [] [10] []),(M 10)]),(L [12,8,4] [] [4] [])]),(L [12,8,4,4] [] [4] [(L [6,2,2] [2,7] [4,14,4] [(L [2,2] [3] [6,4] [])]),(L [8,4,4] [] [6] [(L [4,4] [] [4] [(L [4] [] [5] [(M 3)]),(M 3)]),(L [4,4] [] [5] [(L [4] [] [34] [(M 3)]),(M 3)]),(L [8,2] [2,17,2] [4,34,4,6] []),(M 3)]),(L [6,4,2] [7,2,3,2,11,2,5] [14,4,6,4,22,4,10,4] [(L [4,2] [2,3,2] [4,6,4,14] [(T 2 [13,2,3] [26,4,6,4])]),(L [8,4] [] [5] [(L [4] [] [6] [(M 3)]),(M 3)])]),(L [8,4,4] [] [5] [(L [4,4] [] [5] [(T 2 [3,2,7] [6,4,14,4]),(M 3)]),(L [4,4] [] [4] [(T 2 [2,3,2,11] [4,6,4,22,4]),(M 3)]),(L [8,2] [11,2,5,2] [22,4,10,4,6] []),(M 3)]),(L [12,4,4] [] [4] [(L [12,2] [2,7,2] [4,14,4,10] []),(M 3)]),(L [12,4,2] [2,13,2,3,2] [4,26,4,6,4,10] [(L [12,2] [3,2,11,2,5] [6,4,22,4,10,4] [])]),(L [14,8,4] [] [5] [(L [12,6] [] [7] [(T 2 [2,5,2,3] [4,10,4,6,4]),(T 2 [2,5,2,3] [4,10,4,6,4]),(M 3),(T 12 [] [4])]),(M 3)]),(M 3)])),(41,(M 6),(L [8,6,2,2] [5,2,3,2,11] [10,4,6,4,22,4] [(L [8,4,4] [] [5] [(L [4,2] [] [5] [(T 2 [] [4])]),(L [2,2] [] [4] []),(L [8,2] [] [4] []),(L [8,4] [] [4] [])]),(L [8,4,4] [] [4] [(L [4,4] [] [5] [(T 2 [] [5]),(T 4 [] [4])]),(L [4,2] [] [5] [(T 2 [3] [6,4])]),(L [8,2] [] [4] []),(L [8,4] [] [5] [])]),(L [10,4,4] [] [5] [(L [4,2] [] [6] [(L [4] [] [4] [(R1 1 [] 0)])]),(L [10,2] [] [6] []),(L [10,4] [] [4] [])])])),(43,(L [10,6,4,3] [2] [4,26] [(L [6,2,3] [3] [6,4] [(L [4,3] [] [5] [(T 1 [7,2,3,2,5] [14,4,6,4,10,4]),(T 4 [] [4])]),(L [6,2] [2] [4,10] [])]),(L [6,4,3] [] [5] [(L [4,3] [] [5] [(L [3] [] [4] [(R1 2 [] 0)]),(T 4 [] [4])]),(L [6,3] [] [4] [(T 6 [11] [22,4])]),(L [6,4] [2] [4,10] [])]),(L [8,4,3] [] [4] [(L [2,3] [2] [4,6] [(T 2 [] [4])]),(L [4,3] [] [5] [(L [3] [] [4] [(R1 2 [] 2)]),(T 4 [] [6])]),(L [8,3] [] [4] [(T 8 [] [6])]),(L [8,4] [] [4] [])]),(L [10,2,3] [3] [6,4] [(L [10,2] [3] [6,4] [])]),(L [10,8,3] [] [4] [(L [10,3] [] [5] [(T 10 [3] [6,4])]),(L [10,8] [] [4] [])]),(L [10,6,4] [2] [4,10] [])]),(L [10,6,4,2] [2] [4,26] [(L [6,2,2] [3] [6,4] [(L [4,4] [] [5] [(T 2 [] [4]),(M 3)])]),(L [6,4,4] [] [5] [(L [4,2] [] [5] [(T 2 [] [4])]),(L [6,2] [5] [10,4] []),(M 3)]),(L [8,4,4] [] [4] [(L [2,2] [2] [4,6] []),(L [4,2] [] [5] [(T 2 [] [4])]),(L [8,2] [] [4] []),(M 3)]),(L [10,2,2] [3] [6,4] []),(L [10,8,4] [] [4] [(L [10,2] [] [5] []),(M 3)])])),(47,(M 6),(L [6,4,2,2] [2,5,2,3,2,7,2,11,2,3,2,5] [4,10,4,6,4,14,4,22,4,6,4,10,4] [(L [6,4,2] [] [5] [(L [2,2] [2] [4,6] []),(L [8,2] [] [5] [(L [4] [] [5] [(R1 1 [] 2)])])])])),(53,(M 54),(L [8,4,2,2] [2,3,2,5] [4,6,4,10,4] [(L [6,2,2] [] [6] [(L [2,2] [] [5] [])]),(L [6,2,2] [] [4] [(L [2,2] [] [5] [])])])),(59,(M 30),(L [8,6,2,2] [2] [4,6] [(L [6,4,2] [] [5] [B,(L [8,2] [] [5] [B])]),(L [4,2,2] [2,7] [4,14,4] []),(L [10,2,2] [] [5] [(L [4,2] [] [5] [(T 2 [] [4])])])])),(61,(L [8,4,2,1] [2,3,2] [4,6,4,14] [B,(L [6,2,3] [2] [4,6] [(L [2,3] [] [5] [(L [4] [] [4] [(R1 2 [] 0)])]),(L [6,2] [] [5] [])])]),(L [8,4,2,2] [3,2] [6,4,14] [B,(L [6,2,2] [2] [4,6] [(L [2,2] [] [5] [])])])),(67,B,B)])) (M 6) (R2 101 [(29,A,A),(31,A,A),(37,A,A),(41,(M 6),A),(43,(X [6,4,2,1] [(L [10,6,5] [] [5] [(L [4,3] [] [4] [(L [3] [] [4] [(R1 2 [] 2)]),(T 4 [] [22])]),(L [4,3] [] [6] [(L [3] [] [4] [(R1 2 [] 2)]),(L [6] [] [5] [(R1 2 [] 2)])]),(L [4,3] [13] [26,4] [(L [3] [] [6] [(R1 2 [] 13)]),(T 4 [] [6])]),(L [10,3] [] [4] [(T 10 [] [26])]),(L [10,3] [] [4] [(T 10 [] [6])]),(L [10,6] [] [6] []),(M 50)])]),(X [6,4,2,2] [(L [10,6,4] [] [5] [(L [4,4] [] [4] [(L [4] [] [4] [(M 3)]),(M 3)]),(L [4,4] [] [6] [(L [4] [] [4] [(M 3)]),(M 3)]),(L [4,4] [13] [26,4] [(L [4] [] [6] [(M 3)]),(M 3)]),(L [10,4] [] [4] [(M 3)]),(L [10,4] [] [4] [(M 3)]),(M 3)])])),(47,(M 6),(X [6,4,2,2] [(L [8,4,2] [2,3] [4,6,4] [(L [4,4] [] [5] [(T 2 [3] [6,4]),(T 4 [] [4])]),(L [4,4] [] [4] [(T 2 [2] [4,6]),(T 4 [] [5])]),(L [8,4] [] [5] [(T 8 [] [4])])])])),(53,(M 54),(L [10,8,4,4] [3,2,7,2,31,2] [6,4,14,4,62,4,6] [(L [8,4,4] [] [4] [(L [4,2] [] [4] [(L [4] [] [4] [(R1 1 [] 0)])]),(L [4,2] [] [5] [(T 2 [] [4])]),(L [8,4] [] [5] [(T 8 [] [4])]),(L [8,4] [] [5] [])]),(L [8,4,2] [5,2,23] [10,4,46,4] [(L [4,2] [3,2] [6,4,38] [(T 2 [3,2] [6,4,34])]),(L [4,4] [] [6] [(T 2 [2,3,2] [4,6,4,34]),(T 4 [] [4])]),(L [8,4] [3] [6,4] [(T 8 [] [5])])]),(L [8,4,2] [2,11,2,3,2,7] [4,22,4,6,4,14,4] [(L [6,4] [] [4] [(T 2 [23,2,3] [46,4,6,4]),(L [4] [] [5] [(R1 1 [] 2)]),(T 6 [] [4])]),(L [4,4] [] [5] [(T 2 [2,29,2,3] [4,58,4,6,4]),(T 4 [] [4])]),(L [10,4] [] [4] [(L [4] [] [5] [(R1 1 [] 2)]),(T 10 [] [6])])]),(L [12,4,4] [] [4] [(M 23),(L [12,4] [] [4] [(T 12 [] [5])]),(L [12,4] [] [4] [])]),(L [12,4,4] [2] [4,6] [(M 23),(L [12,4] [] [4] [(L [14] [] [5] [(R1 1 [] 0)])]),(L [12,4] [2] [4,6] [])]),(L [12,8,4] [3] [6,4] [(M 23),(L [14,10] [] [5] [(T 8 [] [4]),(L [16] [] [5] [(R1 1 [] 2)])])]),(L [12,8,4] [5,2] [10,4,6] [(M 23)])])),(59,(M 30),(L [10,6,4,2] [2,3] [4,6,4] [(L [6,4,2] [2] [4,6] [(L [2,2] [7] [14,4] []),(L [6,2] [] [5] [])]),(L [6,4,2] [2,17] [4,34,4] [(L [4,2] [] [10] [(T 2 [7] [14,4])]),(L [8,2] [] [5] [(T 2 [] [4])])]),(L [6,2,2] [2,11,2,3,2,17,2,5,2,3,2] [4,22,4,6,4,34,4,10,4,6,4,14] [(L [4,2] [] [6] [(T 2 [] [4])])]),(L [10,2,2] [2,5,2,3,2,13,2,7] [4,10,4,6,4,26,4,14,4] []),(L [10,6,2] [17,2] [34,4,10] [])])),(61,(L [10,8,4,3] [] [5] [(L [6,2,3] [3] [6,4] [(L [2,1] [2,11,2,3,2] [4,22,4,6,4,10] []),(L [6,2] [2,5] [4,10,4] [])]),(L [6,2,3] [3,2,5,2,13,2] [6,4,10,4,26,4,6] [(L [4,3] [] [6] [(L [3] [] [4] [(R1 2 [] 3)]),(T 4 [] [14])]),(L [6,4] [] [5] [(L [8] [] [5] [(R1 2 [] 2)])])]),(L [8,4,3] [] [5] [(L [4,3] [] [6] [(L [3] [] [6] [(R1 2 [] 2)]),(T 4 [] [4])]),(L [4,3] [] [4] [(L [3] [] [4] [(R1 2 [] 2)]),(T 4 [] [5])]),(L [8,3] [] [5] [(T 8 [] [22])]),(L [8,4] [] [4] [])]),(L [10,4,3] [] [4] [(L [10,3] [2] [4,22] [(T 10 [] [4])]),(L [10,4] [] [5] [])]),(L [10,4,3] [] [4] [(L [10,3] [3] [6,4] [(T 10 [] [6])]),(L [10,4] [] [4] [])]),(L [10,8,3] [2] [4,10] [(L [10,8] [3] [6,4] [])]),(L [10,8,4] [] [6] [])]),(L [12,8,4,2] [] [5] [(L [6,2,2] [3] [6,4] [(L [2,2] [2] [4,10] [])]),(L [6,2,2] [3,2,5,2,13,2] [6,4,10,4,26,4,6] [(L [4,2] [2] [4,6] [(T 2 [] [4])])]),(L [8,4,2] [] [5] [(L [4,2] [2] [4,6] [(T 2 [] [6])]),(L [4,2] [] [4] [(T 2 [] [4])]),(L [8,2] [] [5] [])]),(M 23),(L [12,4,2] [] [4] [(L [12,2] [2] [4,22] [])]),(L [12,4,2] [] [4] [(L [12,2] [3] [6,4] [])]),(L [12,8,2] [2] [4,10] [])])),(67,(L [10,8,4,3] [] [4] [(L [6,4,3] [] [5] [(L [2,3] [2] [4,6] [(L [4] [] [5] [(R1 2 [] 2)])]),(L [6,3] [] [4] [(T 6 [3] [6,4])]),(L [6,4] [] [4] [])]),(L [8,4,3] [] [4] [(L [2,3] [13,2,3] [26,4,6,4] [(L [4] [] [6] [(R1 2 [] 0)])]),(L [4,3] [] [5] [(L [3] [] [5] [(R1 2 [] 2)]),(T 4 [] [4])]),(L [8,3] [] [5] [(T 8 [] [4])]),(L [8,4] [] [10] [])]),(L [6,4,3] [] [4] [(L [2,3] [2,3,2] [4,6,4,10] [(T 2 [5,2] [10,4,6])]),(L [8,3] [] [5] [(L [3] [] [7] [(R1 2 [] 5)]),(T 8 [] [10])]),(L [6,4] [11] [22,4] [])]),(L [10,2,3] [3,2,5] [6,4,10,4] [(L [10,4] [] [5] [(T 10 [] [4])])]),(L [12,4,3] [] [4] [(M 46),(L [12,3] [] [4] [(T 12 [] [4])]),(L [12,4] [] [6] [])]),(L [10,8,3] [] [6] [(L [10,8] [] [22] [])]),(L [10,8,4] [3] [6,4] [])]),(L [10,8,4,2] [] [4] [(L [6,4,2] [] [5] [(L [2,2] [2] [4,6] []),(L [6,2] [] [4] [])]),(L [8,4,4] [] [4] [(L [2,2] [13,2,3] [26,4,6,4] []),(L [4,2] [] [5] [(L [4] [] [5] [(M 3)])]),(L [8,2] [] [5] []),(M 3)]),(L [6,4,2] [3] [6,4] [(L [2,2] [2,3,2] [4,6,4,10] []),(L [8,2] [] [5] [(L [4] [] [7] [(M 3)])])]),(L [10,2,2] [3,2,5] [6,4,10,4] []),(L [12,4,4] [] [4] [(M 23),(L [12,2] [] [4] []),(M 3)]),(L [10,8,2] [] [6] [])])),(71,(M 18),(L [8,6,4,2] [2] [4,26] [(L [6,2,2] [3] [6,4] [(M 71)]),(L [6,4,2] [] [5] [(M 71),(L [6,2] [] [10] [])]),(M 71),(L [10,6,2] [] [5] [(L [6,2] [3] [6,4] [])])])),(73,(L [10,6,4,3] [2] [4,6] [(L [4,2,1] [7,2,3,2,5] [14,4,6,4,10,4] []),(L [6,2,1] [2,11,2,5,2,3] [4,22,4,10,4,6,4] [(L [2,3] [2] [4,6] [(L [4] [] [4] [(R1 2 [] 2)])])]),(L [8,4,3] [] [4] [(L [4,3] [] [4] [(T 1 [2,5,2,3] [4,10,4,6,4]),(T 4 [] [4])]),(L [4,3] [] [5] [(L [3] [] [10] [(R1 2 [] 0)]),(T 4 [] [6])]),(L [8,3] [] [4] [(T 8 [] [5])]),(L [8,4] [] [6] [])]),(L [10,4,3] [] [5] [(L [10,3] [] [5] [(T 10 [] [10])]),(L [10,4] [] [6] [])]),(L [10,8,3] [] [5] [(L [12,3] [] [5] [(M 46),(T 12 [] [4])]),(L [10,8] [] [4] [])]),(L [10,6,4] [] [4] [])]),(L [10,6,4,2] [2] [4,6] [(L [4,2,2] [2,3,2,5] [4,6,4,10,4] []),(L [4,2,2] [2,3,2,11,2,5,2,3] [4,6,4,22,4,10,4,6,4] []),(L [8,4,2] [] [4] [(L [4,2] [] [4] [(T 2 [] [4])]),(L [4,2] [] [5] [(T 2 [] [10])]),(L [8,2] [] [4] [])]),(L [10,4,2] [] [5] [(L [10,2] [] [5] [])]),(L [10,8,2] [] [5] [(L [12,4] [] [5] [(M 23),(M 3)])])])),(79,(M 10),(L [8,6,2,2] [7,2,3] [14,4,6,4] [(L [4,2,2] [2,5,2] [4,10,4,6] []),(L [6,4,2] [] [4] [(L [2,2] [2] [4,6] []),(M 79)]),(L [8,2,2] [2,3] [4,6,4] [])])),(83,(M 6),(L [8,4,2,2] [7,2,11,2,3,2,5] [14,4,22,4,6,4,10,4] [B,(L [6,2,2] [3,2] [6,4,14] [(L [4,2] [] [4] [(T 2 [] [5])])])])),(89,(M 90),(L [10,6,4,2] [] [4] [B,(L [6,4,2] [] [4] [(L [2,2] [2] [4,6] []),(L [6,2] [] [5] [])]),(L [6,4,2] [] [5] [(L [4,2] [] [5] [(T 2 [] [4])]),(L [6,2] [] [4] [])]),(L [10,4,2] [] [4] [(L [10,2] [] [5] [])]),(L [10,8,2] [] [5] [(L [12,2] [] [5] [(M 23)])])])),(97,(L [10,6,4,3] [] [5] [B,B,(L [6,4,3] [] [4] [B,(L [6,3] [] [5] [B]),(L [6,4] [] [5] [])]),B,(L [10,6,3] [] [4] [(L [10,6] [] [5] [])]),(L [10,6,4] [] [4] [])]),(L [10,6,4,2] [] [5] [B,B,(L [6,4,2] [] [4] [B,(L [6,2] [] [5] [])]),B,(L [10,6,2] [] [4] [])]))])) (M 10) (R2 191 [(23,A,A),(29,A,A),(31,A,A),(37,A,A),(41,A,A),(43,A,A),(47,A,A),(53,A,A),(59,A,A),(61,A,A),(67,(X [6,4,2,1] [(X [6,2,1] [(X [4,3] [(M 6),(L [6] [] [4] [(R1 2 [] 2)])])])]),(X [6,4,2,2] [(X [6,2,2] [(X [4,2] [(M 3)])])])),(71,(M 18),(X [6,4,2,2] [(L [10,6,4] [] [5] [(M 71),(L [4,4] [3,2] [6,4,34] [(M 3),(L [6] [] [4] [(R1 1 [] 5)])]),(M 19),(M 3),(L [10,4] [] [4] [(T 10 [] [4])]),(L [10,6] [] [4] [])])])),(73,(X [6,4,2,1] [(L [8,4,3] [2] [4,58] [(L [4,3] [] [6] [(M 6),(T 4 [7] [14,4])]),(L [4,3] [3] [6,4] [(M 6),(L [6] [] [4] [(R1 2 [] 0)])]),(M 6),(L [8,4] [2] [4,6] [])])]),(X [6,4,2,2] [(L [8,4,2] [2,11,2,3,2] [4,22,4,6,4,58] [(L [4,2] [7,2] [14,4,6] [(M 3)]),(L [4,4] [3] [6,4] [(M 3),(M 3)]),(M 3)])])),(79,(M 10),(X [6,4,2,2] [(L [6,4,2] [2,5,2,3,2] [4,10,4,6,4,14] [(L [4,2] [3] [6,4] [(M 3)]),(M 3)])])),(83,(M 6),(X [6,4,2,2] [(L [6,4,2] [2,13] [4,26,4] [(L [4,2] [] [4] [(M 3)]),(M 3)])])),(89,(M 90),(X [8,4,2,2] [(L [6,4,2] [2] [4,6] [(L [4,4] [] [5] [(M 3),(T 4 [] [4])]),(M 3)]),(X [6,2,2] [(X [4,2] [(M 3)])])])),(97,(L [16,10,6,3] [2,3,2] [4,6,4,10] [(L [6,4,3] [] [4] [(L [4,1] [5,2,7,2,3] [10,4,14,4,6,4] [(M 6)]),(M 6),(L [6,4] [] [4] [])]),(L [8,4,3] [2,5,2] [4,10,4,6] [(L [6,3] [] [5] [(M 6),(L [3] [] [4] [(R1 2 [] 19)]),(T 6 [] [4])]),(L [4,3] [11] [22,4] [(M 6),(L [6] [] [4] [(R1 2 [] 0)])]),(M 6),(L [10,6] [] [4] [(M 38),(T 10 [] [5])])]),(L [12,6,5] [] [5] [(L [4,3] [2,3] [4,6,4] [(M 6),(T 4 [2] [4,6])]),(L [6,3] [37] [74,4] [(M 6),(L [3] [] [4] [(R1 2 [] 17)]),(T 6 [] [4])]),(M 38),(L [6,3] [5] [10,4] [(M 6),(L [3] [] [4] [(R1 2 [] 3)]),(T 6 [] [6])]),(M 6),(L [12,3] [2] [4,6] [(T 12 [] [6])]),(L [12,6] [] [6] []),(M 10)]),(L [10,6,3] [3,2,19] [6,4,38,4] [(L [4,3] [3,2] [6,4,14] [(M 6),(T 4 [43] [86,4])]),(L [6,5] [] [5] [(M 6),(L [3] [3] [6,4] [(R1 2 [] 2)]),(T 6 [] [6]),(M 10)]),(M 38),(M 6),(L [10,3] [2,3,2] [4,6,4,14] [(T 10 [] [4])]),(L [10,6] [] [4] [])]),(L [12,6,5] [2] [4,14] [(L [4,3] [2,17] [4,34,4] [(M 6),(L [6] [] [5] [(R1 2 [] 2)])]),(L [6,3] [2] [4,118] [(M 6),(L [3] [11] [22,4] [(R1 2 [] 2)]),(T 6 [] [4])]),(M 38),(L [6,5] [] [5] [(M 6),(L [5] [] [5] [(R1 2 [] 41),(M 10)]),(T 6 [3] [6,4]),(M 10)]),(M 6),(L [12,3] [2] [4,6] [(T 12 [] [82])]),(L [12,6] [] [4] []),(M 10)]),(L [12,8,5] [] [4] [(L [6,3] [] [5] [(M 6),(L [3] [] [6] [(R1 2 [] 2)]),(T 6 [] [6])]),(L [6,3] [] [4] [(M 6),(L [3] [2] [4,6] [(R1 2 [] 5)]),(T 6 [] [4])]),(M 38),(L [6,3] [3] [6,4] [(M 6),(L [5] [] [4] [(R1 2 [] 5),(M 10)]),(T 6 [] [4])]),(M 6),(L [12,3] [2] [4,10] [(T 12 [] [10])]),(L [12,5] [] [5] [(T 12 [] [4]),(M 10)]),(L [12,8] [] [4] []),(M 10)]),(L [16,6,3] [] [5] [(M 6),(L [16,3] [] [6] [(T 16 [] [4])]),(L [16,6] [] [4] [])]),(L [16,6,5] [] [5] [(M 6),(L [16,3] [5] [10,4] [(T 16 [] [4])]),(L [16,6] [] [4] []),(M 10)]),(M 38),(M 6),(L [16,12,5] [] [5] [(L [16,3] [2,67] [4,134,4] [(T 16 [] [4])]),(L [16,12] [] [6] []),(M 10)]),(L [16,10,6] [] [10] [])]),(L [16,10,6,4] [3,2] [6,4,10] [(L [6,4,2] [5] [10,4] [(L [2,2] [3,2,5,2,7,2,3] [6,4,10,4,14,4,6,4] []),(M 3)]),(L [8,4,2] [3,2,41,2,5,2] [6,4,82,4,10,4,6] [(L [6,4] [] [5] [(M 3),(T 2 [7] [14,4]),(M 3)]),(L [4,2] [2,3,2,11] [4,6,4,22,4] [(M 3)]),(M 3)]),(L [12,6,4] [] [5] [(L [4,4] [2,3] [4,6,4] [(M 3),(M 3)]),(L [6,4] [] [4] [(M 3),(L [4] [] [4] [(M 3)]),(M 3)]),(M 19),(L [6,4] [] [4] [(M 3),(L [4] [] [4] [(M 3)]),(M 3)]),(M 3),(L [12,4] [] [6] [(M 3)]),(M 3)]),(L [10,6,4] [2,19] [4,38,4] [(L [4,4] [3,2] [6,4,14] [(M 3),(M 3)]),(L [6,4] [] [5] [(M 3),(L [4] [] [4] [(M 3)]),(M 3)]),(M 19),(M 3),(L [10,4] [3,2] [6,4,14] [(M 3)]),(M 3)]),(L [12,6,4] [2] [4,14] [(L [4,2] [2,23,2,3,2,13,2,17] [4,46,4,6,4,26,4,34,4] [(M 3)]),(L [6,4] [] [118] [(M 3),(L [4] [] [4] [(M 3)]),(M 3)]),(M 19),(L [6,4] [] [5] [(M 3),(L [4] [] [5] [(M 3)]),(M 3)]),(M 3),(L [12,4] [] [6] [(M 3)]),(M 3)]),(L [12,8,4] [] [4] [(L [6,4] [] [5] [(M 3),(T 2 [3,2,13,2,17,2] [6,4,26,4,34,4,6]),(M 3)]),(L [6,4] [] [4] [(M 3),(L [4] [] [6] [(M 3)]),(M 3)]),(M 19),(L [6,4] [] [4] [(M 3),(L [4] [] [4] [(M 3)]),(M 3)]),(M 3),(L [12,4] [] [10] [(M 3)]),(L [12,4] [] [5] [(M 3)]),(M 3)]),(L [16,6,4] [] [5] [(M 3),(L [16,2] [3,2,13,2,17,2] [6,4,26,4,34,4,6] []),(M 3)]),(L [16,6,4] [] [5] [(M 3),(L [16,4] [5] [10,4] [(M 3)]),(M 3)]),(M 19),(M 3),(L [16,12,4] [] [5] [(L [16,4] [67] [134,4] [(M 3)]),(M 3)]),(M 3)])),(101,(M 6),(L [12,8,4,4] [2,5,2,3,2] [4,10,4,6,4,38] [(L [6,4,2] [] [10] [(L [4,2] [] [6] [(M 3)]),(M 3)]),(L [10,4,4] [] [4] [(L [4,4] [] [4] [(M 3),(L [6] [] [4] [(R1 1 [] 0)])]),(L [4,4] [] [5] [(M 3),(T 4 [] [4])]),(M 19),(M 3),(L [10,4] [] [5] [])]),(L [10,4,4] [2] [4,6] [(L [4,2] [2] [4,38] [(M 3)]),(L [6,4] [] [58] [(M 3),(L [4] [] [5] [(R1 1 [] 3)]),(T 6 [] [4])]),(M 19),(M 3),(L [10,4] [5] [10,4] [])]),(L [8,4,2] [2,3,2,5,2,7,2] [4,6,4,10,4,14,4,6] [(L [4,4] [] [5] [(M 3),(T 4 [3] [6,4])]),(L [4,2] [43,2,3,2,17] [86,4,6,4,34,4] [(M 3)]),(M 3)]),(L [12,4,4] [2] [4,58] [(M 3),(L [14,6] [] [4] [(L [6] [] [5] [(R1 1 [] 2)]),(T 14 [] [5])])]),(L [14,6,4] [] [5] [(L [6,4] [] [5] [(M 3),(L [4] [] [4] [(R1 1 [] 2)]),(T 6 [] [4])]),(M 3),(L [14,4] [] [4] [(T 14 [2] [4,6])]),(L [14,6] [] [4] [])]),(M 3),(L [14,10,4] [2,5] [4,10,4] [(L [10,6] [] [4] [(M 19),(T 10 [] [4])]),(M 19)])])),(103,(L [10,8,4,3] [2,19,2,3,2,13,2,7,2,3,2,11] [4,38,4,6,4,26,4,14,4,6,4,22,4] [(L [6,4,1] [2,7,2,5,2] [4,14,4,10,4,6] [(L [4,3] [] [4] [(M 6),(T 4 [] [4])]),(M 6)]),(L [10,4,3] [] [5] [(L [4,3] [] [4] [(M 6),(T 4 [] [4])]),(L [4,3] [3] [6,4] [(M 6),(T 4 [11] [22,4])]),(M 38),(M 6),(L [10,4] [] [6] [])]),(L [8,4,3] [2,3] [4,6,4] [(L [4,3] [2] [4,6] [(M 6),(T 4 [] [14])]),(L [6,3] [] [4] [(M 6),(L [3] [] [5] [(R1 2 [] 5)]),(T 6 [] [10])]),(M 6),(L [12,6] [] [5] [(M 38),(T 4 [] [4]),(T 12 [] [4])])]),(L [10,4,3] [2,31,2,3,2,5] [4,62,4,6,4,10,4] [(M 6),(L [12,4] [] [6] [(T 4 [] [5])])]),(L [14,6,3] [] [4] [(L [4,3] [2] [4,58] [(M 6),(T 4 [17] [34,4])]),(L [6,3] [] [5] [(M 6),(L [3] [] [4] [(R1 2 [] 3)]),(T 6 [] [6])]),(M 6),(L [14,3] [] [5] [(T 14 [] [4])]),(L [14,6] [] [4] [])]),(M 6),(L [12,8,4] [3,2] [6,4,10] [(L [8,4] [2] [4,6] [])])]),(L [10,8,4,2] [2,5,2,19,2,3,2,13,2,7,2,3,2,11] [4,10,4,38,4,6,4,26,4,14,4,6,4,22,4] [(L [6,2,2] [2,3,2,7,2,5,2] [4,6,4,14,4,10,4,6] [(L [4,2] [] [4] [(M 3)])]),(L [10,4,4] [] [5] [(L [4,2] [3] [6,4] [(M 3)]),(L [4,2] [3] [6,4] [(M 3)]),(M 19),(M 3),(M 3)]),(L [8,4,4] [2,3] [4,6,4] [(L [4,2] [2] [4,6] [(M 3)]),(L [6,4] [] [4] [(M 3),(L [4] [] [5] [(M 3)]),(M 3)]),(M 3),(M 3)]),(L [10,4,2] [2,31,2,3,2,5] [4,62,4,6,4,10,4] [(M 3)]),(L [14,6,4] [] [4] [(L [4,4] [2] [4,58] [(M 3),(M 3)]),(L [6,4] [] [5] [(M 3),(T 2 [2,3] [4,6,4]),(M 3)]),(M 3),(L [14,4] [] [5] [(M 3)]),(M 3)]),(M 3)])),(107,(M 54),(L [12,8,4,2] [13,2] [26,4,10] [(L [6,4,2] [] [4] [(L [4,2] [] [5] [(M 3)]),(M 3)]),(L [8,4,2] [11] [22,4] [(L [4,2] [] [4] [(M 3)]),(L [4,2] [] [4] [(M 3)]),(M 3)]),(L [10,4,4] [] [5] [(L [4,2] [2] [4,26] [(M 3)]),(L [4,2] [2] [4,6] [(M 3)]),(M 19),(M 3),(L [10,4] [] [4] [])]),(L [10,6,4] [] [4] [(L [4,2] [2] [4,6] [(M 3)]),(L [4,2] [2] [4,6] [(M 3)]),(M 19),(M 3),(L [10,2] [] [5] []),(L [10,6] [] [5] [])]),(L [12,4,2] [] [46] [(M 3)]),(L [12,4,2] [2,11] [4,22,4] [(M 3)]),(M 3)])),(109,(M 10),(L [14,10,4,4] [] [5] [(L [6,4,2] [5] [10,4] [(L [4,2] [] [10] [(M 3)]),(M 3)]),(L [6,4,2] [3,2,7,2,11] [6,4,14,4,22,4] [(L [4,2] [] [4] [(M 3)]),(M 3)]),(L [8,4,2] [3] [6,4] [(L [4,2] [] [6] [(M 3)]),(L [4,2] [2] [4,6] [(M 3)]),(M 3)]),(L [8,4,2] [2] [4,26] [(L [4,2] [2] [4,6] [(M 3)]),(L [4,2] [] [10] [(M 3)]),(M 3)]),(L [10,6,4] [] [5] [(L [4,2] [2] [4,10] [(M 3)]),(L [4,2] [2] [4,6] [(M 3)]),(M 19),(M 3),(L [10,2] [] [4] []),(M 3)]),(L [14,4,2] [] [10] [(M 3)]),(L [14,4,2] [2] [4,6] [(M 3)]),(M 19),(M 3),(M 3)])),(113,(M 114),(L [14,8,4,4] [] [4] [(L [6,4,2] [] [10] [(L [4,2] [] [4] [(M 3)]),(M 3)]),(L [8,4,2] [] [4] [(L [4,2] [] [4] [(M 3)]),(L [4,2] [] [5] [(M 3)]),(M 3)]),(L [8,4,2] [] [4] [(L [4,2] [] [4] [(M 3)]),(L [6,4] [] [4] [(M 3),(T 2 [] [5]),(T 6 [] [5])]),(M 3)]),(L [6,4,2] [2,5,2,3,2,17] [4,10,4,6,4,34,4] [(L [4,2] [] [4] [(M 3)]),(M 3)]),(L [10,4,4] [] [4] [(L [4,2] [] [6] [(M 3)]),(L [4,2] [2] [4,6] [(M 3)]),(M 19),(M 3),(L [10,4] [] [5] [])]),(L [14,4,2] [3] [6,4] [(M 3)]),(L [14,4,2] [2] [4,6] [(M 3)]),(M 3),(L [14,10,6] [] [4] [(M 19),(L [16,10] [] [4] [(L [12] [] [4] [(R1 1 [] 0)])])])])),(127,(L [14,8,4,3] [] [4] [(L [6,4,3] [] [5] [(L [4,1] [3,2] [6,4,22] [(M 762)]),(M 762),(L [6,4] [] [4] [])]),(L [8,4,3] [] [5] [(L [4,1] [2,5,2,3,2] [4,10,4,6,4,26] [(M 762)]),(L [4,1] [17,2,5,2,3,2] [34,4,10,4,6,4,14] [(M 762)]),(M 762),(L [8,4] [] [4] [])]),(L [6,4,3] [2,3] [4,6,4] [(L [4,3] [] [4] [(M 762),(T 4 [] [6])]),(M 762),(L [8,4] [] [5] [(T 4 [7] [14,4])])]),(L [8,4,3] [] [5] [(L [4,1] [2,3,2,11,2,7,2,3] [4,6,4,22,4,14,4,6,4] [(M 762)]),(L [4,3] [] [6] [(M 762),(T 4 [] [4])]),(M 762),(L [8,4] [] [4] [])]),(L [10,4,3] [] [4] [(L [4,1] [3,2,11,2,7,2,3] [6,4,22,4,14,4,6,4] [(M 762)]),(L [4,3] [] [4] [(M 762),(T 4 [] [5])]),(M 38),(M 762),(L [10,4] [] [4] [])]),(L [14,4,1] [3,2,11,2,7,2,3] [6,4,22,4,14,4,6,4] [(M 762)]),(L [14,4,3] [] [4] [(M 762),(L [14,4] [] [5] [])]),(M 762),(L [14,8,4] [] [4] [])]),(L [14,10,4,2] [] [4] [(L [6,4,2] [] [5] [(L [2,2] [2,3,2] [4,6,4,22] []),(M 381)]),(L [8,4,2] [] [5] [(L [4,2] [] [26] [(M 381)]),(L [4,2] [] [14] [(M 381)]),(M 381)]),(L [6,4,2] [2,3] [4,6,4] [(L [4,2] [] [4] [(M 381)]),(M 381)]),(L [8,4,2] [] [5] [(L [4,2] [] [4] [(M 381)]),(L [4,2] [] [6] [(M 381)]),(M 381)]),(L [10,4,4] [] [4] [(L [4,2] [] [4] [(M 381)]),(L [4,2] [] [4] [(M 381)]),(M 19),(M 381),(M 3)]),(L [14,4,2] [] [4] [(M 381)]),(L [14,4,2] [] [4] [(M 381)]),(M 19),(M 381)])),(131,(M 6),(L [10,6,4,2] [2,5] [4,10,4] [(L [6,2,2] [3,2,11] [6,4,22,4] [(L [4,2] [] [4] [B])]),(L [6,4,2] [5] [10,4] [(L [4,2] [] [6] [(M 3)]),(M 3)]),(L [8,4,2] [] [4] [(L [4,2] [2] [4,6] [(M 3)]),(L [4,2] [] [4] [(M 3)]),(M 3)]),(L [10,4,2] [11] [22,4] [(M 3)]),(M 3)])),(137,(M 6),(L [12,8,4,2] [] [4] [B,(L [10,4,2] [] [4] [(L [4,2] [] [6] [(M 3)]),(L [4,2] [] [5] [(M 3)]),(M 19),(M 3)]),(L [8,4,2] [] [5] [(L [4,2] [] [4] [(M 3)]),(L [4,2] [] [4] [(M 3)]),(M 3)]),(L [8,4,2] [] [5] [(L [4,2] [] [4] [(M 3)]),(L [4,2] [] [4] [(M 3)]),(M 3)]),(L [12,4,2] [2] [4,34] [(M 3)]),(L [12,4,2] [] [5] [(M 3)]),(M 3)])),(139,(M 10),(L [14,10,4,2] [] [4] [B,(L [8,4,2] [] [4] [(L [4,2] [] [4] [(M 3)]),(L [4,2] [] [5] [(M 3)]),(M 3)]),(L [6,4,2] [2] [4,6] [(L [4,2] [] [4] [(M 3)]),(M 3)]),(L [8,4,2] [] [5] [(L [4,2] [] [4] [(M 3)]),(L [4,2] [] [4] [(M 3)]),(M 3)]),(L [10,6,4] [] [4] [(L [4,2] [] [4] [(M 3)]),(L [4,2] [] [4] [(M 3)]),(M 19),(M 3),(L [10,2] [] [5] []),(M 3)]),(L [14,4,2] [] [4] [(M 3)]),(L [14,4,2] [] [4] [(M 3)]),(M 19),(M 3)])),(149,(M 150),(L [10,6,4,2] [2,3] [4,6,4] [B,(L [6,4,2] [] [4] [(L [2,2] [5,2,7,2,3,2,13] [10,4,14,4,6,4,26,4] []),(M 3)]),(L [8,4,2] [] [4] [(L [4,2] [] [6] [(M 3)]),(L [4,2] [] [5] [(M 3)]),(M 3)]),(L [10,4,2] [] [4] [(M 3)]),(M 3)])),(151,(M 38),(L [10,6,4,2] [2] [4,6] [B,(L [6,4,2] [] [5] [(L [4,2] [] [14] [(M 3)]),(M 3)]),(L [8,4,2] [] [4] [(L [4,2] [] [4] [(M 3)]),(L [4,2] [] [5] [(M 3)]),(M 3)]),(L [10,4,2] [] [5] [(M 3)]),(M 3)])),(157,(L [10,6,4,3] [2] [4,10] [B,(L [6,4,1] [2,3] [4,6,4] [(L [4,1] [2,5] [4,10,4] [(M 6)]),(M 6)]),(L [8,4,3] [] [4] [(L [4,3] [] [6] [(M 6),(T 4 [] [5])]),(L [4,3] [] [5] [(M 6),(T 4 [] [5])]),(M 6),(L [8,4] [] [4] [])]),(L [10,4,3] [] [5] [(M 6),(L [10,4] [] [6] [])]),(M 6),(L [10,8,4] [2] [4,6] [(L [12,4] [] [4] [(L [6] [] [4] [(R1 2 [] 0)])])])]),(L [10,6,4,2] [2] [4,10] [B,(L [6,2,2] [3,2,5,2,7,2,3] [6,4,10,4,14,4,6,4] [(L [2,2] [2,3,2,7,2,5] [4,6,4,14,4,10,4] [])]),(L [8,4,2] [] [4] [(L [4,2] [] [6] [(M 3)]),(L [4,2] [] [5] [(M 3)]),(M 3)]),(L [10,4,2] [] [5] [(M 3)]),(M 3)])),(163,(L [10,6,4,3] [3] [6,4] [B,(L [6,2,1] [3,2,7,2,5,2,3,2] [6,4,14,4,10,4,6,4,22] [(L [4,1] [3] [6,4] [(M 6)])]),(L [8,4,3] [] [5] [(L [4,1] [2] [4,6] [(M 6)]),(L [4,3] [] [4] [(M 6),(T 4 [] [4])]),(M 6),(L [8,4] [] [5] [])]),(L [10,4,1] [2,5] [4,10,4] [(M 6)]),(M 6),(L [12,8,4] [] [4] [(L [6,4] [] [5] []),(L [12,4] [] [5] [])])]),(L [10,6,4,2] [3] [6,4] [B,(L [6,2,2] [7,2,5,2,3,2] [14,4,10,4,6,4,22] [(L [4,2] [] [4] [(M 3)])]),(L [8,4,2] [] [5] [(L [4,2] [] [6] [(M 3)]),(L [4,2] [] [4] [(M 3)]),(M 3)]),(L [10,4,2] [5] [10,4] [(M 3)]),(M 3)])),(167,(M 6),(L [10,8,4,2] [] [4] [B,(L [6,4,2] [] [14] [(L [4,2] [] [5] [(M 3)]),(M 3)]),(L [6,2,2] [2,5,2,7,2,3,2] [4,10,4,14,4,6,4,26] [(L [2,2] [3,2,7,2,5,2] [6,4,14,4,10,4,6] [])]),(L [10,2,2] [7,2,5,2,3,2] [14,4,10,4,6,4,22] []),(L [10,4,2] [] [5] [(M 3)]),(M 3)])),(173,(M 6),(L [10,6,4,2] [3] [6,4] [B,(L [6,4,2] [2] [4,6] [(L [4,2] [] [6] [(M 3)]),(M 3)]),(L [8,4,2] [] [4] [(L [4,2] [] [4] [(M 3)]),(L [4,2] [] [5] [(M 3)]),(M 3)]),(L [10,4,2] [] [4] [(M 3)]),(M 3)])),(179,(M 90),(L [8,6,4,2] [7,2] [14,4,10] [B,(L [6,2,2] [2,3,2,5,2,11] [4,6,4,10,4,22,4] [B]),(L [12,4,2] [] [5] [(L [4,2] [] [5] [(M 3)]),(L [6,4] [] [7] [(M 3),(T 2 [] [4]),(T 6 [] [4])]),(M 3)]),(M 3)])),(181,(L [10,6,4,1] [3,2] [6,4,14] [B,B,(L [6,4,3] [2] [4,6] [B,(M 6),(L [10,6] [] [4] [(T 4 [] [5]),(M 38),(T 10 [] [5])])]),B,(M 6)]),(L [8,6,4,2] [2,3,2] [4,6,4,14] [B,B,B,(M 3)]))])) (M 18) (K 6)) A A) A A) A A A A)
private def c8 : Cert := (S7 5 (S7 7 (P 11 B (P 13 B (P 17 B (M 54) (L [6,3,3,2] [] [5] [B,B,B])) (P 17 B (M 54) (L [6,3,2,2] [] [5] [B,B]))) (P 13 B (P 17 B (M 18) (L [6,2,3,2] [] [5] [B,B])) (P 17 B (M 18) (P 19 B (X [6,2,2,2,3] [B,B]) (X [6,2,2,2,2] [B]))))) (P 11 (P 13 (P 17 B (M 18) (R2 23 [(19,(L [6,2,3] [] [10] [(L [2,3] [] [5] [B]),(L [8,2] [] [4] [(T 2 [] [5])])]),(L [6,2,2] [] [10] [(L [2,2] [] [5] [])]))])) (M 14) (P 17 (R2 29 [(19,(L [6,2,3] [2,7] [4,14,4] [(L [2,3] [] [5] [(L [4] [] [5] [(R1 6 [] 0)])]),(L [8,4] [] [4] [(L [4] [] [5] [(R1 6 [] 2)]),(T 8 [] [5])])]),(L [6,4,2] [2,7] [4,14,4] [(L [4,2] [] [5] [(L [4] [] [5] [(R1 18 [] 2)])]),(L [8,2] [2] [4,14] [(L [4] [] [4] [(R1 18 [] 0)])])])),(23,(L [6,2,3] [3] [6,4] [(L [4,3] [] [4] [(L [3] [] [5] [B]),B]),(L [8,4] [] [4] [(T 2 [] [5]),(T 8 [] [5])])]),(L [6,2,2] [3] [6,4] [(L [4,2] [] [4] [(T 2 [] [5])])]))]) (M 18) (L [8,4,4] [] [4] [(L [2,2] [5,2] [10,4,6] []),(L [4,4] [] [4] [(T 2 [2] [4,6]),(T 4 [] [5])]),(L [10,4] [] [4] [(M 78),(T 10 [] [5])]),(L [8,4] [] [5] [])]))) (R2 37 [(13,A,A),(17,(M 54),(X [6,3,2] [(M 66),(L [8,4] [2] [4,6] [(L [4] [] [22] [(R1 6 [] 0)]),(L [10] [] [5] [(R1 6 [] 2)])])])),(19,(L [8,3,3] [2,5,2,3,2] [4,10,4,6,4,22] [(M 66),(L [5,3] [] [5] [(L [3] [] [4] [(R1 6 [] 0)]),(L [3] [2] [4,6] [(R1 6 [] 2)]),(T 5 [] [10])]),(L [8,3] [] [4] [(T 8 [] [6])]),(L [8,5] [] [4] [(L [10] [] [5] [(R1 6 [] 2)])])]),(L [8,3,4] [2,5,2,3,2] [4,10,4,6,4,22] [(M 66),(L [5,4] [] [5] [(L [4] [] [4] [(M 18)]),(T 2 [2,5,2,11,2] [4,10,4,22,4,6]),(M 18)]),(L [8,2] [3] [6,4] []),(M 18)])),(23,(M 18),(L [8,3,2] [] [6] [(M 66),(L [3,2] [] [5] [(T 2 [] [5])]),(L [8,2] [] [4] [])])),(29,(M 18),(L [8,3,2] [] [4] [(M 66),(L [3,2] [] [5] [(T 2 [] [5])]),(L [8,2] [] [5] [])])),(31,(L [6,3,3] [] [4] [B,B,(L [8,3] [] [5] [B])]),(L [6,3,2] [] [4] [B,B]))]) (P 13 (P 17 (P 19 (P 23 (R2 37 [(29,(L [8,4,3] [] [4] [(M 726),(L [4,3] [] [5] [(M 42),(T 4 [] [6])]),(M 42),(L [8,4] [] [4] [])]),(L [8,4,2] [] [4] [(M 242),(L [4,2] [] [5] [(M 14)]),(M 14)])),(31,(L [6,4,3] [] [4] [B,(M 14),(L [8,4] [] [5] [B])]),(L [6,4,2] [] [4] [B,(M 14)]))]) (L [8,4,3] [] [6] [(M 726),(L [4,3] [] [5] [(M 42),(T 4 [] [4])]),(M 42),(L [8,4] [] [5] [])]) (L [8,4,2] [] [6] [(M 242),(L [4,2] [] [5] [(M 14)]),(M 14)])) (L [8,4,3] [3,2] [6,4,22] [(M 242),(L [4,3] [] [5] [(M 266),(T 4 [] [10])]),(M 266),(L [8,4] [] [4] [])]) (L [8,4,2] [3,2,7,2,5,2,3,2] [6,4,14,4,10,4,6,4,22] [(M 242),(L [4,4] [] [5] [(M 266),(T 4 [] [4])]),(M 266)])) (M 18) (X [6,2,2] [(M 242)])) A A)) (P 11 (P 13 (P 17 B (M 54) (R2 29 [(19,(M 114),(M 57)),(23,(M 18),(L [8,2,2] [] [4] [B,(L [2,2] [] [5] [])]))])) (M 42) (P 17 (R2 37 [(19,(M 114),(M 57)),(23,(L [10,4,3] [] [4] [(L [4,3] [] [4] [(M 54),(T 4 [] [4])]),(L [4,3] [] [6] [(M 54),(T 4 [] [4])]),(M 234),(M 54),(L [10,4] [] [4] [])]),(L [10,4,4] [] [4] [(L [4,2] [] [4] [(T 2 [] [4])]),(L [4,2] [2] [4,6] [(T 2 [7] [14,4])]),(M 39),(L [10,2] [2] [4,6] []),(M 21)])),(29,(L [8,4,3] [] [5] [(L [2,3] [] [6] [(L [4] [] [4] [(M 54)])]),(L [2,3] [3] [6,4] [(L [4] [] [4] [(M 54)])]),(M 54),(L [8,4] [] [4] [])]),(L [8,4,2] [] [5] [(L [2,2] [] [6] []),(L [2,2] [3] [6,4] []),(L [8,2] [] [4] [])])),(31,(L [6,4,3] [] [4] [B,(L [10,3] [] [4] [(L [3] [] [5] [(R1 18 [] 3)]),(M 234),(T 10 [] [4])]),(L [10,4] [] [5] [(T 4 [] [4]),(M 78)])]),(L [8,4,2] [] [4] [B,(L [4,4] [] [4] [(T 2 [] [5]),(T 4 [] [5])]),(L [10,4] [] [4] [(M 117),(M 27)])]))]) (M 54) (X [6,2,2] [(X [4,4] [(M 9),(L [6] [3,2] [6,4,10] [(R1 3 [] 2)])])]))) (M 18) (R2 53 [(13,A,A),(17,A,A),(19,A,A),(23,(M 18),(X [6,2,2] [(M 363)])),(29,(M 18),(L [10,4,2] [2] [4,6] [(M 363),(L [4,2] [3] [6,4] [(M 21)]),(L [4,4] [] [4] [(M 21),(T 4 [] [5])]),(M 21)])),(31,(L [8,4,3] [7] [14,4] [(M 726),(L [6,3] [] [4] [(M 42),(L [3] [] [5] [(R1 6 [] 0)]),(T 6 [] [4])]),(M 42),(L [8,4] [] [4] [])]),(L [8,4,2] [2,7] [4,14,4] [(M 363),(L [6,4] [] [4] [(M 21),(T 2 [] [5]),(M 9)]),(M 21)])),(37,(L [10,4,3] [] [5] [(M 726),(L [4,3] [] [4] [(M 42),(T 4 [] [5])]),(L [6,5] [] [7] [(M 42),(L [3] [] [4] [(R1 6 [] 3)]),(T 6 [] [6]),(L [8] [] [9] [(R1 6 [] 2)])]),(M 42),(L [10,4] [] [6] [])]),(L [10,4,2] [] [5] [(M 363),(L [4,2] [] [4] [(M 21)]),(L [6,4] [] [7] [(M 21),(T 2 [] [4]),(M 63)]),(M 21)])),(41,(M 126),(L [8,4,2] [] [5] [(M 363),(L [4,2] [] [5] [(M 21)]),(M 21)])),(43,(M 66),(L [6,4,2] [5,2] [10,4,6] [B,(M 21)])),(47,B,B)])) (P 11 (P 13 (P 17 (P 19 B (P 23 B (L [10,5,3,3] [] [5] [B,B,(L [5,3,3] [] [7] [B,B,B]),B,B,B]) (L [10,5,3,4] [] [5] [B,B,(L [5,3,4] [] [7] [B,B,B]),B,B,B])) (P 23 B (L [10,5,4,3] [] [5] [B,B,(L [5,4,3] [] [7] [B,B,B]),B,B,B]) (L [10,5,4,4] [] [5] [B,B,(L [5,4,4] [] [7] [B,B,B]),B,B,B]))) (M 18) (R2 29 [(19,(L [8,5,4,3] [] [5] [(L [5,4,3] [] [4] [(L [4,3] [] [5] [(L [3] [] [4] [(R1 2 [] 2)]),(T 4 [] [4])]),(L [5,3] [] [5] [(T 5 [] [6])]),(L [5,4] [] [6] [])]),(L [3,2,3] [2,3] [4,6,4] [(L [3,2] [2] [4,6] [])]),(L [8,2,3] [3] [6,4] [(L [8,2] [] [6] [])]),(L [12,7,5] [] [7] [(L [5,3] [] [4] [(T 5 [] [4])]),(L [5,3] [] [4] [(T 5 [] [4])]),(M 114),(L [12,7] [] [4] []),(L [12,7] [] [4] [])]),(L [8,5,4] [] [4] [])]),(L [8,5,4,4] [] [5] [(L [5,4,4] [] [4] [(L [4,4] [] [5] [(T 2 [] [4]),(T 4 [] [7])]),(L [5,2] [] [5] []),(L [5,4] [] [5] [])]),(L [3,2,2] [2,3] [4,6,4] []),(L [8,2,2] [3] [6,4] []),(L [12,7,4] [] [7] [(L [5,2] [] [4] []),(L [5,2] [] [4] []),(M 114),(L [12,7] [] [4] [])]),(L [10,5,4] [] [5] [(L [7,4] [] [5] [(M 342)])])])),(23,(L [6,3,2,1] [2,3,2] [4,6,4,10] [(L [5,4,3] [] [5] [(L [2,3] [] [4] [(L [4] [] [5] [(R1 6 [] 0)])]),(L [7,3] [] [7] [(M 18),(T 7 [] [5])]),(L [5,4] [] [5] [])])]),(L [6,3,2,2] [2] [4,10] [(L [5,4,2] [] [5] [(L [2,2] [] [4] []),(L [7,4] [] [7] [(T 2 [] [4]),(T 7 [] [4])])])]))])) (M 14) (P 17 (R2 37 [(19,(X [6,5,4,3] [(L [7,4,5] [] [4] [(L [4,3] [] [4] [(L [3] [] [4] [(R1 6 [] 0)]),(T 4 [] [4])]),(M 114),(L [7,3] [3] [6,4] [(T 7 [] [4])]),(L [7,4] [] [4] []),(L [7,4] [] [5] [])]),(X [8,4,3] [(L [6,5] [] [10] [(L [5] [] [4] [(R1 6 [] 2),(R1 6 [] 0)]),(L [5] [2] [4,10] [(R1 2 [] 2),(R1 2 [] 0)]),(T 6 [] [4]),(L [8] [] [4] [(R1 2 [] 0)])]),(L [14,5] [2] [4,14] [(M 78),(L [5] [] [6] [(R1 6 [] 5),(R1 6 [] 3)]),(L [5] [] [4] [(R1 6 [] 2),(R1 6 [] 3)]),(T 14 [] [4]),(T 14 [] [4])]),(L [12,6] [] [5] [(M 26),(T 4 [] [4]),(T 12 [] [4])])]),(X [8,5,3] [(L [7,5] [2] [4,82] [(M 342),(T 7 [] [4]),(T 7 [3] [6,4])]),(L [10,5] [3,2] [6,4,26] [(M 78)])]),(L [10,5,4] [2,3,2] [4,6,4,10] [(L [5,4] [3,2] [6,4,26] []),(M 26)])]),(X [8,5,4,2] [(L [7,4,4] [] [4] [(L [4,4] [] [4] [(L [4] [] [4] [(R1 18 [] 3)]),(T 4 [] [6])]),(M 114),(L [7,4] [] [4] [(T 7 [] [5])]),(L [7,4] [] [5] [])]),(X [5,4,4] [(L [6,4] [2,3,2,17,2] [4,6,4,34,4,10] [(L [4] [11] [22,4] [(R1 18 [] 5)]),(L [4] [2,3,2,7,2] [4,6,4,14,4,10] [(R1 6 [] 3)]),(L [8] [] [5] [(R1 6 [] 2)])]),(L [7,4] [2,7,2,3,2] [4,14,4,6,4,82] [(M 342),(L [9] [] [4] [(R1 18 [] 0)])]),(L [9,8] [3,2,17,2,5,2] [6,4,34,4,10,4,6] [(M 342),(L [6] [17,2,173,2,3,2,7,2,5,2,3,2,23,2,61,2,3,2,5,2,7,2,3,2,31,2] [34,4,346,4,6,4,14,4,10,4,6,4,46,4,122,4,6,4,10,4,14,4,6,4,62,4,106] [(R1 6 [] 3)]),(L [11] [] [4] [(R1 6 [] 0)]),(L [11] [] [5] [(R1 6 [] 5)])])]),(X [8,4,4] [(L [14,6] [] [14] [(M 78),(L [6] [] [6] [(R1 18 [] 2),(R1 6 [] 2)]),(L [4] [43,2,3,2,19] [86,4,6,4,38,4] [(R1 18 [] 2)]),(T 14 [] [6]),(T 14 [2] [4,6])]),(X [10,4] [(M 78)])]),(X [8,5,4] [(L [18,9] [3,2,11,2,5,2,3,2,13] [6,4,22,4,10,4,6,4,26,4] [(M 234),(L [9] [2,17,2,3] [4,34,4,6,4] [(M 1026),(R1 18 [] 3)]),(L [9] [2,17,2,5,2,3] [4,34,4,10,4,6,4] [(M 1026),(R1 18 [] 7)]),(M 234),(L [11] [] [4] [(M 1026),(R1 18 [] 2),(R1 18 [] 61)]),(M 1026),(L [20] [] [6] [(R1 18 [] 0)])])])])),(23,(L [8,5,4,3] [2] [4,6] [(L [3,4,3] [2,3] [4,6,4] [(L [5,3] [] [5] [(L [3] [] [5] [(R1 18 [] 3)]),(T 5 [] [4])]),(L [3,4] [5] [10,4] [])]),(L [5,4,3] [] [6] [(L [4,3] [] [5] [(L [3] [] [4] [(R1 18 [] 2)]),(T 4 [] [10])]),(L [7,5] [] [7] [(M 54),(T 7 [] [4]),(T 7 [] [4])]),(L [5,4] [] [4] [])]),(L [8,4,3] [3] [6,4] [(L [10,3] [] [5] [(M 234),(T 10 [] [10])]),(L [8,4] [] [4] [])]),(L [8,5,3] [] [6] [(L [8,5] [3] [6,4] [])]),(L [8,5,4] [] [14] [])]),(L [8,5,4,4] [2] [4,6] [(L [5,4,2] [3] [6,4] [(L [4,4] [] [4] [(T 2 [] [5]),(M 14)]),(L [5,2] [] [5] [])]),(L [5,4,2] [2] [4,6] [(L [4,4] [] [5] [(T 2 [] [4]),(M 14)]),(L [7,4] [] [7] [(T 2 [] [4]),(M 42)])]),(L [8,4,2] [2,3] [4,6,4] [(L [10,4] [] [5] [(M 78),(M 42)])]),(L [8,5,2] [2] [4,6] []),(M 14)])),(29,(L [8,5,4,3] [] [4] [(L [3,4,3] [] [4] [(L [5,3] [] [4] [(L [3] [] [5] [(R1 18 [] 0)]),(T 5 [] [5])]),(L [5,4] [] [4] [(T 4 [] [5])])]),(L [5,4,3] [] [5] [(L [2,1] [2,7,2,3] [4,14,4,6,4] []),(L [5,1] [7,2,3] [14,4,6,4] []),(L [5,4] [] [4] [])]),(L [8,4,3] [] [5] [(L [8,1] [7,2,3] [14,4,6,4] []),(L [8,4] [] [4] [])]),(L [8,5,3] [] [5] [(L [8,5] [] [4] [])]),(L [8,5,4] [] [6] [])]),(L [8,5,4,2] [] [4] [(L [3,4,2] [] [4] [(L [5,4] [] [4] [(T 2 [] [5]),(M 78)])]),(L [5,4,2] [] [5] [(L [2,2] [3] [6,4] []),(L [5,2] [] [4] [])]),(L [8,4,2] [] [5] [(L [8,2] [] [4] [])]),(L [8,5,2] [] [5] [])])),(31,(L [8,5,4,3] [] [4] [(L [3,2,3] [3] [6,4] [(L [3,4] [2] [4,6] [(L [5] [] [4] [(R1 6 [] 0)])])]),(L [5,4,3] [] [5] [(L [2,3] [3] [6,4] [(L [4] [] [4] [(R1 6 [] 0)])]),(L [5,1] [2,3] [4,6,4] []),(L [5,4] [] [6] [])]),(L [8,4,3] [] [5] [(L [8,1] [2,3] [4,6,4] []),(L [8,4] [] [6] [])]),(L [8,5,3] [] [5] [(L [8,5] [] [6] [])]),(L [8,5,4] [] [4] [])]),(L [8,5,4,2] [] [4] [(L [3,2,2] [3] [6,4] []),(L [5,4,2] [] [5] [(L [2,2] [3] [6,4] []),(L [5,2] [] [4] [])]),(L [8,4,2] [] [5] [(L [8,2] [] [4] [])]),(L [8,5,2] [] [5] [])]))]) (M 18) A)) (R2 53 [(13,A,A),(17,A,A),(19,A,A),(23,(M 18),(X [4,3,3,2] [(L [10,5,4] [2,13,2] [4,26,4,6] [(M 66),(L [5,4] [5] [10,4] [(L [4] [] [4] [(M 42)]),(M 42)]),(L [5,4] [2,3] [4,6,4] [(L [4] [] [4] [(M 42)]),(M 42)]),(L [10,4] [] [4] [(M 42)]),(M 42)])])),(29,(M 18),(L [10,5,5,4] [2] [4,22] [(M 66),(L [5,5,4] [2] [4,6] [(L [3,2] [3,2,5,2,13,2,3] [6,4,10,4,26,4,6,4] [(T 2 [] [6])]),(L [5,2] [] [4] []),(L [5,4] [3] [6,4] [(L [7] [] [5] [(M 18)])]),(L [5,5] [5] [10,4] [])]),(L [7,5,4] [] [4] [(L [5,4] [] [4] [(T 2 [] [4]),(L [4] [] [6] [(R1 6 [] 2)]),(T 5 [] [10])]),(M 18),(L [7,2] [] [6] []),(L [7,4] [] [4] [(T 7 [] [4])]),(L [7,5] [] [4] [])]),(L [12,5,4] [] [4] [(L [7,4] [] [4] [(T 2 [] [4]),(T 2 [3,2,5] [6,4,10,4]),(M 126),(T 7 [] [4])]),(L [12,2] [] [4] []),(L [12,4] [] [5] [(T 12 [3] [6,4])]),(L [12,5] [] [6] [])]),(L [10,5,2] [] [6] []),(L [12,7,4] [] [5] [(L [7,4] [] [4] [(M 18),(T 7 [] [4])]),(M 18),(L [12,7] [] [6] [])]),(L [10,5,5] [2] [4,6] [])])),(31,(L [8,5,5,3] [2,3] [4,6,4] [(M 66),(L [5,3,3] [2,13] [4,26,4] [(L [5,3] [] [6] [(L [3] [] [4] [(R1 6 [] 2)]),(L [3] [] [5] [(R1 6 [] 3)]),(T 5 [] [4])]),(L [5,3] [] [4] [(T 5 [] [4])]),(L [5,3] [11] [22,4] [])]),(L [8,3,3] [2,13,2] [4,26,4,6] [(L [10,3] [] [5] [(L [3] [] [4] [(R1 6 [] 2)]),(T 10 [] [4])]),(L [8,3] [11,2] [22,4,10] [])]),(L [8,5,3] [] [5] [(L [10,5] [] [4] [(T 5 [] [5])])]),(L [10,7,3] [] [4] [(L [5,3] [] [4] [(T 5 [] [4])]),(M 18),(L [10,7] [] [6] [])]),(L [8,5,5] [3] [6,4] [])]),(L [10,5,5,2] [2,3] [4,6,4] [(M 66),(L [5,5,2] [13] [26,4] [(L [5,2] [2] [4,6] [(T 2 [] [4]),(L [4] [] [5] [(M 18)])]),(L [5,2] [] [4] []),(L [5,4] [] [4] [(M 18)])]),(L [5,5,4] [] [4] [(L [5,2] [13] [26,4] [(T 2 [] [4]),(L [4] [] [4] [(M 18)])]),(L [5,4] [] [5] [(M 18)]),(L [5,4] [] [4] [(M 18)]),(M 18)]),(L [10,3,2] [2,13,2] [4,26,4,6] [(L [10,4] [] [5] [(M 18)])]),(L [10,5,2] [] [5] []),(L [10,7,4] [] [4] [(M 18),(M 18)])])),(37,(L [8,5,3,3] [7] [14,4] [(M 66),(L [5,5,3] [] [5] [(L [3,3] [] [10] [(T 1 [2,7] [4,14,4]),(T 3 [] [4])]),(L [5,1] [7,2] [14,4,6] []),(L [5,3] [] [4] [(T 5 [] [5])]),(L [5,5] [] [5] [])]),(L [8,5,3] [] [5] [(L [8,1] [7,2] [14,4,6] []),(L [8,3] [] [4] [(T 8 [] [5])]),(L [10,5] [] [4] [(T 5 [] [5])])]),(L [8,5,1] [2,3] [4,6,4] []),(L [8,5,3] [2] [4,6] [])]),(L [8,5,3,2] [7] [14,4] [(M 66),(L [5,5,4] [] [5] [(L [3,2] [] [10] [(T 2 [] [4])]),(L [5,2] [] [6] []),(L [5,2] [] [4] []),(M 126)]),(L [10,5,2] [] [5] [(L [5,4] [] [5] [(T 2 [] [6]),(T 2 [] [4]),(M 126)]),(L [10,2] [] [6] []),(L [10,2] [] [4] [])]),(L [8,5,2] [] [4] [])])),(41,(M 126),(L [8,5,5,2] [] [4] [(M 66),(L [7,7,4] [] [4] [(L [3,2] [] [6] [(T 2 [] [4])]),(M 18),(L [7,2] [] [6] []),(L [7,2] [] [5] []),(M 126),(L [7,7] [] [5] [])]),(L [10,5,2] [] [4] [(L [3,2] [] [5] [(T 2 [] [6])]),(L [10,2] [] [6] []),(L [10,2] [] [5] [])]),(L [8,5,2] [] [4] []),(L [10,7,4] [] [4] [(L [5,2] [] [5] []),(M 18),(L [10,7] [] [5] [])])])),(43,(M 66),(L [8,5,5,2] [] [4] [(M 66),(L [3,3,2] [2,5] [4,10,4] [B]),(L [8,3,2] [] [4] [B]),B,(L [10,5,2] [] [4] [(L [7,4] [] [4] [(M 774),(M 18)])])])),(47,(M 18),(L [8,5,5,2] [] [4] [B,(L [3,3,2] [3] [6,4] [B]),(L [8,3,2] [] [4] [B]),B,(L [10,5,2] [] [4] [(L [5,2] [] [5] [])])]))]) (P 13 (P 17 (P 19 (P 23 (R2 53 [(29,(L [10,7,4,3] [2] [4,22] [(M 726),(L [5,4,3] [2] [4,6] [(L [4,3] [3] [6,4] [(M 42),(L [6] [] [5] [(R1 6 [] 2)])]),(M 42),(L [5,4] [] [22] [])]),(L [7,4,3] [] [4] [(L [6,3] [] [4] [(M 42),(L [5] [] [4] [(R1 6 [] 11),(R1 6 [] 0)]),(T 6 [] [22])]),(M 18),(M 42),(L [7,6] [] [5] [(T 7 [] [4])])]),(L [12,6,3] [] [4] [(L [6,5] [] [4] [(M 42),(L [3] [] [5] [(R1 6 [] 0)]),(T 6 [] [5]),(T 6 [] [5])]),(M 42),(L [12,3] [] [5] [(T 12 [] [5])]),(L [12,6] [] [5] [])]),(M 18),(M 42),(L [10,7,4] [] [6] [])]),(L [10,7,4,4] [2] [4,22] [(M 242),(L [5,4,4] [2] [4,6] [(L [4,2] [13,2,3] [26,4,6,4] [(M 14)]),(M 14),(L [5,4] [5] [10,4] [])]),(L [7,4,4] [] [4] [(L [4,4] [] [4] [(M 14),(T 4 [2] [4,10])]),(L [6,4] [] [4] [(M 42),(L [4] [] [5] [(R1 6 [] 3)]),(T 6 [] [4])]),(M 14),(L [7,4] [] [4] [])]),(L [10,6,4] [] [4] [(M 14),(L [10,4] [] [5] [(T 10 [] [4])]),(L [10,6] [2] [4,6] [])]),(L [10,6,4] [2] [4,22] [(M 42),(L [12,4] [] [4] [(L [4] [] [5] [(R1 6 [] 0)]),(T 12 [] [4])]),(L [10,6] [2] [4,6] [])]),(M 14),(L [10,7,4] [2] [4,6] [])])),(31,(L [8,5,4,3] [2,3] [4,6,4] [(M 242),(L [5,4,3] [13] [26,4] [(L [4,3] [2] [4,6] [(M 14),(T 4 [] [4])]),(M 14),(L [5,4] [] [4] [])]),(L [8,4,3] [13,2] [26,4,6] [(M 14),(L [8,4] [2] [4,10] [])]),(M 14),(L [8,5,4] [3] [6,4] [])]),(L [10,5,4,2] [2,3] [4,6,4] [(M 242),(L [5,4,2] [2,13] [4,26,4] [(L [4,2] [2] [4,6] [(M 14)]),(M 14)]),(L [5,4,4] [] [4] [(L [4,2] [2,13] [4,26,4] [(M 14)]),(M 14),(L [5,4] [] [5] [])]),(L [10,4,2] [2] [4,6] [(M 14)]),(M 14)])),(37,(L [8,5,4,3] [] [4] [(M 242),(L [5,4,3] [] [5] [(L [4,3] [] [10] [(M 14),(T 4 [] [4])]),(M 14),(L [5,4] [] [5] [])]),(L [8,4,3] [] [5] [(M 14),(L [10,6] [] [4] [(T 4 [] [5]),(L [14] [] [4] [(R1 2 [] 0),(R1 2 [] 0)])])]),(M 14),(L [8,5,4] [2] [4,6] [])]),(L [8,5,4,2] [] [4] [(M 242),(L [5,4,4] [] [5] [(L [4,2] [] [10] [(M 14)]),(M 14),(M 42)]),(L [10,4,2] [] [5] [(L [4,4] [] [5] [(M 14),(M 42)]),(M 14)]),(M 14)])),(41,(M 42),(L [10,5,4,2] [] [4] [(M 242),(L [7,6,4] [] [4] [(L [4,2] [] [6] [(M 14)]),(L [4,2] [] [5] [(M 42)]),(M 14),(L [7,2] [] [5] []),(L [7,6] [] [5] [])]),(L [5,4,4] [] [4] [(L [4,2] [] [5] [(M 14)]),(M 14),(L [7,4] [] [4] [(L [6] [] [4] [(R1 6 [] 0)])])]),(L [10,4,2] [] [4] [(M 14)]),(M 14)])),(43,(M 22),(L [8,5,4,2] [] [4] [(M 242),(L [3,4,2] [2,5] [4,10,4] [(M 14)]),(L [8,2,2] [3,2,5] [6,4,10,4] []),(M 14)])),(47,(L [8,5,4,3] [] [4] [B,(L [3,4,1] [5,2,3] [10,4,6,4] [(M 42)]),(L [8,2,1] [2,5,2,3] [4,10,4,6,4] []),(M 42),(L [8,5,4] [] [4] [])]),(L [8,5,4,2] [] [4] [B,(L [3,2,2] [2,5,2,3] [4,10,4,6,4] []),(L [8,2,2] [2,3] [4,6,4] []),(M 14)]))]) (X [6,3,2,1] [(M 726)]) A) A A) A A) A A)) (P 11 (P 13 (P 17 (P 19 B (P 23 B (L [10,6,3,3] [] [5] [B,B,(L [6,3,3] [] [7] [B,B,B]),(L [10,3,3] [] [7] [B,B]),B,B]) (L [10,6,3,4] [] [5] [B,B,(L [6,3,4] [] [7] [B,B,B]),(L [10,3,4] [] [7] [B,B]),B,B])) (P 23 B (L [10,6,4,3] [] [5] [B,B,(L [6,4,3] [] [7] [B,B,B]),(L [10,4,3] [] [7] [B,B]),B,B]) (L [10,6,4,4] [] [5] [B,B,(L [6,4,4] [] [7] [B,B,B]),(L [10,4,4] [] [7] [B,B]),B,B]))) (M 18) (P 19 (P 23 B (L [6,4,2,1] [2,3,2] [4,6,4,10] [(L [4,4,3] [] [5] [(L [6,3] [] [7] [(L [3] [] [4] [(R1 6 [] 0)]),(T 6 [] [5])]),(L [4,4] [] [5] [])])]) (L [6,4,2,2] [2] [4,10] [(L [4,4,2] [] [5] [(L [6,4] [] [7] [(T 2 [] [4]),(T 6 [] [4])])])])) (L [8,4,4,3] [] [5] [(L [6,4,3] [] [4] [(L [2,3] [] [5] [(T 2 [2] [4,6])]),(L [6,3] [] [5] [(T 6 [] [6])]),(L [6,4] [] [6] [])]),(L [4,2,3] [3] [6,4] [(L [4,2] [] [6] [])]),(L [12,6,5] [] [7] [(L [4,3] [] [4] [(T 4 [] [4])]),(L [4,3] [] [4] [(T 4 [] [4])]),(L [12,3] [] [4] [(T 12 [] [4])]),(L [12,6] [] [4] []),(L [12,6] [] [4] [])]),(L [8,4,4] [] [4] [])]) (L [8,4,4,4] [] [5] [(L [6,4,4] [] [4] [(L [2,2] [] [5] []),(L [6,2] [] [5] []),(L [6,4] [] [5] [])]),(L [4,2,2] [3] [6,4] []),(L [12,6,4] [] [7] [(L [4,2] [] [4] []),(L [4,2] [] [4] []),(L [12,2] [] [4] []),(L [12,6] [] [4] [])]),(L [8,6,4] [] [5] [(L [12,4] [] [7] [(T 4 [] [4]),(T 4 [] [4])])])]))) (M 14) (P 17 (R2 37 [(19,(X [6,4,4,3] [(L [6,4,5] [] [4] [(L [4,3] [] [5] [(L [3] [] [4] [(R1 6 [] 2)]),(T 4 [] [5])]),(L [6,3] [3] [6,4] [(T 6 [] [4])]),(L [6,4] [] [4] []),(L [6,4] [] [5] [])]),(X [8,4,3] [(L [6,5] [2,19,2,3,2,29,2,7,2,3,2] [4,38,4,6,4,58,4,14,4,6,4,82] [(L [5] [] [6] [(R1 6 [] 2),(R1 6 [] 2)]),(T 6 [] [4]),(L [8] [] [4] [(R1 6 [] 2)])]),(L [10,6] [2] [4,26] [(M 78),(T 10 [2] [4,6])])]),(L [10,6,4] [2] [4,10] [(L [6,4] [2] [4,26] [(T 4 [2] [4,6])]),(M 26),(L [12,4] [] [5] [(T 4 [] [4])])])]),(X [8,4,4,2] [(L [6,4,4] [] [4] [(L [4,4] [] [5] [(L [4] [] [4] [(R1 9 [] 2)]),(T 4 [2] [4,6])]),(L [6,4] [] [4] [(T 6 [] [5])]),(L [6,4] [] [5] [])]),(X [4,4,4] [(L [6,4] [3,2,11,2,19,2,3,2,29,2,7,2,3,2] [6,4,22,4,38,4,6,4,58,4,14,4,6,4,82] [(L [6] [] [6] [(R1 9 [] 2),(R1 3 [] 2)]),(L [8] [] [4] [(R1 9 [] 3)])]),(L [10,8] [2] [4,6] [(L [8] [] [4] [(R1 3 [] 0),(R1 3 [] 5)]),(L [8] [] [4] [(R1 3 [] 2),(R1 3 [] 2)]),(M 513),(T 10 [31] [62,4]),(L [12] [] [5] [(R1 3 [] 2)])])]),(X [8,4,4] [(L [18,10] [3,2,13] [6,4,26,4] [(M 117),(L [10] [] [4] [(R1 9 [] 5),(R1 9 [] 3),(M 1539)]),(L [10] [3] [6,4] [(R1 9 [] 0),(R1 9 [] 2),(M 1539)]),(M 117),(L [10] [17] [34,4] [(R1 9 [] 2),(R1 9 [] 2),(M 1539)]),(T 18 [] [6]),(L [20] [] [5] [(R1 9 [] 2)]),(M 1539)])])])),(23,(L [8,6,4,3] [2] [4,6] [(L [4,4,3] [] [4] [(L [4,3] [] [5] [(T 4 [] [4])]),(L [4,4] [] [4] [])]),(L [4,4,3] [] [6] [(L [8,5] [] [7] [(L [3] [] [4] [(R1 18 [] 2)]),(L [3] [] [4] [(R1 18 [] 2)]),(T 8 [] [4]),(T 8 [] [4])]),(L [4,4] [3] [6,4] [])]),(L [10,4,3] [] [4] [(M 78),(L [10,3] [] [6] [(T 10 [] [6])]),(L [10,4] [] [14] [])]),(L [8,6,3] [] [6] [(L [8,6] [3] [6,4] [])]),(L [8,6,4] [] [14] [])]),(L [8,6,4,4] [2] [4,6] [(L [4,4,2] [3] [6,4] [(L [4,2] [] [5] [])]),(L [4,4,2] [2] [4,6] [(L [8,4] [] [7] [(T 2 [3] [6,4]),(T 2 [] [4]),(M 21)])]),(L [10,4,4] [] [4] [(M 13),(L [10,2] [2] [4,6] []),(M 7)]),(L [8,6,2] [2] [4,6] []),(M 7)])),(29,(L [8,4,4,3] [] [4] [(L [4,4,3] [] [4] [(L [6,3] [] [4] [(L [3] [] [5] [(R1 18 [] 0)]),(T 6 [] [5])]),(L [4,4] [] [4] [])]),(L [4,4,3] [] [5] [(L [4,1] [7,2,3] [14,4,6,4] []),(L [4,4] [] [4] [])]),(L [8,4,3] [] [5] [(L [8,4] [] [4] [])]),(L [8,4,4] [] [6] [])]),(L [8,4,4,2] [] [4] [(L [4,4,2] [] [4] [(L [6,4] [] [4] [(T 2 [] [5]),(M 39)])]),(L [4,4,2] [] [5] [(L [4,2] [] [4] [])]),(L [8,4,2] [] [5] [])])),(31,(L [8,4,4,3] [] [4] [(L [4,2,1] [2,3] [4,6,4] []),(L [4,4,3] [] [5] [(L [4,1] [2,3] [4,6,4] []),(L [4,4] [] [6] [])]),(L [8,4,3] [] [5] [(L [8,4] [] [6] [])]),(L [8,4,4] [] [4] [])]),(L [8,4,4,2] [] [4] [(L [4,2,2] [3] [6,4] []),(L [4,4,2] [] [5] [(L [4,2] [] [4] [])]),(L [8,4,2] [] [5] [])]))]) (M 18) A)) (R2 53 [(13,A,A),(17,A,A),(19,A,A),(23,(M 18),(X [4,4,3,2] [(L [10,6,4] [2] [4,6] [(M 66),(L [6,4] [] [4] [(L [4] [] [6] [(M 42)]),(M 42)]),(L [6,4] [] [4] [(L [4] [] [6] [(M 42)]),(M 42)]),(L [10,4] [7] [14,4] [(M 42)]),(M 42)])])),(29,(M 18),(L [10,6,5,4] [] [22] [(M 66),(L [6,5,4] [] [6] [(L [5,4] [] [4] [(L [4] [] [4] [(R1 6 [] 0)]),(L [4] [] [5] [(R1 6 [] 2)]),(T 5 [] [5])]),(L [6,2] [] [4] []),(L [6,4] [3] [6,4] [(L [8] [] [5] [(M 174)])]),(L [6,5] [5] [10,4] [])]),(L [6,5,4] [] [4] [(L [5,4] [] [6] [(T 2 [2] [4,6]),(T 2 [13,2,7] [26,4,14,4]),(T 5 [] [10])]),(L [6,2] [] [6] []),(L [6,4] [] [4] [(T 6 [] [4])]),(L [6,5] [] [4] [])]),(L [14,7,4] [] [4] [(L [5,4] [] [5] [(T 2 [] [6]),(T 2 [3,2,5] [6,4,10,4]),(T 5 [] [6])]),(L [5,4] [] [5] [(T 2 [] [6]),(L [4] [] [5] [(R1 6 [] 3)]),(T 5 [] [6])]),(L [14,2] [] [6] []),(L [14,4] [] [5] [(T 14 [] [6])]),(M 126),(L [14,7] [] [4] [])]),(L [10,6,2] [] [6] []),(L [12,8,4] [] [5] [(L [6,4] [] [4] [(T 6 [] [4])]),(M 174),(L [12,8] [] [6] [])]),(L [10,6,5] [] [6] [])])),(31,(L [8,6,5,3] [2,3] [4,6,4] [(M 66),(L [4,5,3] [2,13] [4,26,4] [(L [4,3] [] [4] [(T 4 [5] [10,4])]),(L [6,3] [] [4] [(L [3] [] [4] [(R1 6 [] 2)]),(T 6 [] [22])]),(L [4,5] [11] [22,4] [])]),(L [10,5,3] [] [4] [(L [5,3] [] [4] [(L [3] [] [4] [(R1 6 [] 0)]),(L [3] [] [4] [(R1 6 [] 2)]),(T 5 [] [4])]),(L [12,5] [] [5] [(L [3] [] [4] [(R1 6 [] 0)]),(T 12 [] [5]),(T 12 [] [7])]),(L [10,3] [] [4] [(L [14] [] [4] [(R1 6 [] 0),(R1 6 [] 0)])]),(L [10,5] [] [6] [])]),(L [8,6,3] [] [5] [(L [10,6] [] [4] [(T 6 [] [5])])]),(L [10,6,3] [] [4] [(L [6,3] [] [4] [(T 6 [] [4])]),(L [10,6] [] [6] [])]),(L [8,6,5] [3] [6,4] [])]),(L [10,6,5,2] [3] [6,4] [(M 66),(L [6,5,2] [13] [26,4] [(L [5,4] [] [4] [(T 2 [] [4]),(T 2 [3] [6,4]),(M 18)]),(L [6,2] [] [4] []),(L [6,4] [] [4] [(M 18)])]),(L [6,5,4] [] [4] [(L [5,4] [] [4] [(T 2 [] [4]),(T 2 [3] [6,4]),(M 18)]),(L [6,4] [] [5] [(M 18)]),(L [6,4] [] [4] [(M 18)]),(M 18)]),(L [10,5,4] [] [4] [(L [12,4] [] [5] [(T 2 [] [4]),(M 18)]),(L [10,4] [] [4] [(M 18)]),(M 18)]),(L [10,6,2] [] [5] []),(L [10,6,4] [] [4] [(M 18)])])),(37,(L [8,4,3,3] [7] [14,4] [(M 66),(L [6,5,3] [] [5] [(L [3,3] [] [4] [(T 1 [7,2] [14,4,6]),(L [5] [] [5] [(R1 6 [] 2)])]),(L [6,1] [7,2] [14,4,6] []),(L [6,3] [] [4] [(T 6 [] [5])]),(L [6,5] [] [5] [])]),(L [8,4,1] [2,3] [4,6,4] []),(L [8,4,3] [5,2] [10,4,6] [])]),(L [8,4,3,2] [7] [14,4] [(M 66),(L [6,5,4] [] [5] [(L [3,2] [] [4] [(T 2 [] [6])]),(L [6,2] [] [6] []),(L [6,2] [] [4] []),(M 126)]),(L [8,4,2] [] [4] [])])),(41,(M 126),(L [8,6,5,2] [] [4] [(M 66),(L [8,7,4] [] [4] [(L [3,2] [] [5] [(T 2 [] [6])]),(L [3,2] [] [5] [(T 2 [] [6])]),(L [8,2] [] [6] []),(L [8,2] [] [5] []),(M 126),(L [8,7] [] [5] [])]),(L [10,5,4] [] [4] [(L [3,2] [] [5] [(T 2 [] [4])]),(L [10,2] [] [4] []),(L [10,2] [] [5] []),(L [12,5] [] [4] [(T 5 [] [5])])]),(L [8,6,2] [] [4] []),(L [10,6,4] [] [4] [(L [6,2] [] [5] []),(L [10,6] [] [5] [])])])),(43,(M 66),(L [8,4,5,2] [] [4] [(M 66),(L [4,3,2] [5] [10,4] [B]),B,(L [10,6,2] [] [4] [(L [6,4] [] [4] [(T 2 [] [5]),(M 18)]),(L [10,2] [] [5] [])])])),(47,(M 18),(L [8,6,5,2] [] [4] [B,(L [4,3,2] [] [4] [B]),(L [10,5,2] [] [4] [(L [3,2] [] [5] [B]),B,(L [10,2] [] [5] [])]),B,(L [10,6,2] [] [4] [(L [6,2] [] [5] [])])]))]) (P 13 (P 17 (P 19 (P 23 (R2 53 [(29,(L [10,6,4,3] [2] [4,22] [(M 726),(L [6,4,3] [2] [4,6] [(L [4,3] [] [4] [(M 42),(T 4 [2] [4,6])]),(M 42),(L [6,4] [] [22] [])]),(L [6,4,3] [] [4] [(L [4,3] [2] [4,6] [(M 42),(T 4 [3] [6,4])]),(M 42),(L [6,6] [] [5] [(T 6 [] [4])])]),(L [14,6,5] [] [4] [(L [6,3] [] [5] [(M 42),(L [3] [] [4] [(R1 6 [] 2)]),(T 6 [] [4])]),(L [4,3] [] [5] [(M 42),(T 4 [] [4])]),(M 42),(L [14,3] [] [5] [(T 14 [] [4])]),(L [14,6] [] [4] []),(L [14,6] [] [5] [])]),(M 42),(L [10,6,4] [] [6] [])]),(L [10,6,4,4] [2] [4,22] [(M 121),(L [6,4,4] [2] [4,6] [(L [4,4] [] [4] [(M 7),(T 4 [] [5])]),(M 7),(L [6,4] [5] [10,4] [])]),(L [6,4,4] [] [4] [(L [4,4] [2] [4,6] [(M 7),(T 4 [2] [4,10])]),(M 7),(L [6,4] [] [4] [])]),(L [14,6,4] [] [4] [(L [6,4] [] [5] [(M 7),(L [4] [] [4] [(R1 1 [] 2)]),(T 6 [] [6])]),(L [4,4] [] [5] [(M 7),(T 4 [] [6])]),(M 7),(L [14,4] [] [5] [(T 14 [] [6])]),(L [14,6] [] [4] [])]),(M 7),(L [10,6,4] [2] [4,6] [])])),(31,(L [8,6,4,3] [2,3] [4,6,4] [(M 242),(L [4,4,3] [2,13] [4,26,4] [(M 14),(L [4,4] [11] [22,4] [])]),(L [10,4,3] [] [4] [(L [4,3] [] [4] [(M 14),(T 4 [] [4])]),(M 14),(L [10,4] [] [6] [])]),(M 14),(L [8,6,4] [3] [6,4] [])]),(L [10,6,4,2] [3] [6,4] [(M 121),(L [6,4,2] [13] [26,4] [(L [4,4] [] [4] [(M 7),(T 4 [] [5])]),(M 7)]),(L [6,4,4] [] [4] [(L [4,4] [] [4] [(M 7),(T 4 [] [5])]),(M 7),(L [6,4] [] [5] [])]),(L [10,4,4] [] [4] [(M 7),(L [10,4] [] [5] [])]),(M 7)])),(37,(L [8,4,4,3] [7] [14,4] [(M 242),(L [6,4,3] [] [5] [(L [4,3] [] [4] [(M 14),(T 4 [] [5])]),(M 14),(L [6,4] [] [5] [])]),(M 14),(L [8,4,4] [2] [4,6] [])]),(L [8,4,4,2] [7] [14,4] [(M 121),(L [6,4,4] [] [5] [(L [4,2] [] [4] [(M 7)]),(M 7),(M 21)]),(M 7)])),(41,(M 42),(L [8,6,4,2] [] [4] [(M 121),(L [8,6,4] [] [4] [(L [4,2] [] [5] [(M 7)]),(L [4,2] [] [5] [(M 7)]),(M 7),(L [8,2] [] [5] []),(L [8,6] [] [5] [])]),(L [10,4,4] [] [4] [(L [4,2] [] [5] [(M 7)]),(M 7),(L [12,6] [] [4] [(T 4 [] [5]),(T 12 [] [5])])]),(M 7)])),(43,(M 22),(L [8,6,4,2] [] [4] [(M 121),(L [4,2,2] [3,2,5] [6,4,10,4] []),(L [10,4,2] [] [4] [(L [4,4] [] [4] [(M 7),(L [6] [] [4] [(R1 3 [] 0)])]),(M 7)]),(M 7)])),(47,(L [8,6,4,3] [] [4] [B,(L [4,2,1] [2,5,2,3] [4,10,4,6,4] []),(L [10,4,3] [] [4] [(L [4,3] [] [5] [(M 42),(T 4 [] [4])]),(M 42),(L [10,4] [] [4] [])]),(M 42),(L [8,6,4] [] [4] [])]),(L [8,6,4,2] [] [4] [B,(L [4,2,2] [2,3] [4,6,4] []),(L [10,4,2] [] [4] [(L [4,2] [] [5] [(M 7)]),(M 7)]),(M 7)]))]) (X [6,4,2,1] [(M 726)]) A) A A) A A) A A))) (M 6) (S7 7 (P 11 (P 13 (P 17 (P 19 (P 23 (P 29 (P 31 (P 37 B (R2 47 [(41,(M 6),(L [6,3,2] [2] [4,14] [B,(L [8,2] [] [5] [(T 2 [] [4])])])),(43,B,B)]) (R2 47 [(41,(M 6),(L [6,2,2] [2] [4,14] [B])),(43,B,B)])) (M 62) (M 31)) (M 30) (R2 53 [(31,(M 62),(M 31)),(37,(L [8,2,3] [2] [4,6] [(L [2,3] [] [4] [(T 2 [] [5])]),(L [2,3] [] [10] [(L [4] [] [5] [(R1 2 [] 2)])]),(L [8,2] [] [4] [])]),(L [8,2,2] [2] [4,6] [(L [2,2] [] [4] []),(L [2,2] [2] [4,10] [])])),(41,(M 6),(L [6,2,2] [3,2,7] [6,4,14,4] [(L [2,2] [] [5] [])])),(43,(L [10,4,3] [] [4] [(L [2,1] [2] [4,10] []),(L [2,3] [] [6] [(T 2 [] [5])]),(L [2,3] [] [5] [(T 2 [] [6])]),(L [10,3] [] [5] [(T 10 [] [6])]),(L [10,4] [] [6] [])]),(L [10,4,2] [] [4] [(L [2,2] [] [10] []),(L [2,2] [] [6] []),(L [2,2] [] [5] []),(L [10,2] [] [5] [])])),(47,(M 6),(L [8,2,2] [2] [4,6] [B,(L [2,2] [] [5] [])]))])) (M 6) (R2 71 [(29,A,A),(31,(M 62),A),(37,(L [12,4,3] [2,19,2] [4,38,4,6] [(L [2,3] [7,2,5] [14,4,10,4] [(L [4] [] [5] [(R1 2 [] 3)])]),(L [4,3] [] [6] [(L [3] [] [4] [(R1 2 [] 2)]),(T 4 [] [4])]),(L [4,5] [] [5] [(L [3] [] [4] [(R1 2 [] 0)]),(T 4 [] [4]),(M 10)]),(M 46),(L [12,3] [3,2] [6,4,58] [(T 12 [] [4])]),(L [12,4] [] [26] [])]),(L [12,4,4] [19,2] [38,4,6] [(L [2,2] [2,7,2,5] [4,14,4,10,4] []),(L [4,4] [] [6] [(L [4] [] [4] [(M 3)]),(M 3)]),(L [4,4] [] [5] [(L [4] [] [4] [(M 3)]),(M 3)]),(M 23),(L [12,4] [2] [4,58] [(M 3)]),(M 3)])),(41,(M 6),(L [8,4,2] [2,7,2,17,2,3] [4,14,4,34,4,6,4] [(L [4,2] [] [4] [(T 2 [] [5])]),(L [4,2] [] [5] [(L [4] [] [4] [(R1 1 [] 0)])]),(L [10,4] [] [6] [(L [4] [] [5] [(R1 1 [] 2)]),(L [12] [] [4] [(M 23)])])])),(43,(L [8,2,3] [2,3,2,5,2,7] [4,6,4,10,4,14,4] [(L [2,3] [2] [4,10] [(L [4] [] [4] [(R1 2 [] 0)])]),(L [4,3] [] [4] [(L [3] [] [6] [(R1 2 [] 2)]),(T 4 [] [5])]),(L [10,4] [] [6] [(L [4] [] [5] [(R1 2 [] 2)]),(T 10 [] [4])])]),(L [8,4,2] [5,2,7] [10,4,14,4] [(L [2,2] [2] [4,10] []),(L [4,2] [] [4] [(T 2 [] [6])]),(L [10,2] [3] [6,4] [(L [4] [] [4] [(M 3)])])])),(47,(M 6),(L [10,4,2] [] [5] [(L [2,2] [2] [4,6] []),(L [2,2] [2] [4,6] []),(L [4,2] [] [4] [(T 2 [] [4])]),(L [10,2] [] [5] [])])),(53,(M 54),(L [8,4,2] [] [4] [(L [2,2] [3] [6,4] []),(L [2,2] [2] [4,6] []),(L [8,2] [] [5] [])])),(59,(M 30),(L [8,2,2] [2] [4,14] [(L [2,2] [] [4] []),(L [2,2] [2] [4,6] [])])),(61,(L [8,2,3] [5] [10,4] [B,(L [4,3] [] [5] [(T 1 [3] [6,4]),(T 4 [] [6])]),(L [8,4] [] [4] [(L [10] [] [4] [(R1 2 [] 0)])])]),(L [8,2,2] [5] [10,4] [B,(L [4,2] [] [5] [(T 2 [] [4])])])),(67,(L [8,2,1] [2,3] [4,6,4] [B,(L [4,3] [] [4] [(L [3] [] [5] [(R1 2 [] 2)]),(T 4 [] [5])])]),(L [8,2,2] [] [4] [B,(L [4,2] [] [4] [(T 2 [] [5])])]))])) (M 10) (R2 109 [(23,A,A),(29,A,A),(31,A,A),(37,A,A),(41,A,A),(43,A,A),(47,(M 6),(X [6,2,2] [(L [4,4] [] [4] [(M 3),(T 4 [] [4])])])),(53,(M 54),(X [8,2,2] [(L [4,2] [] [6] [(M 3)]),(X [4,2] [(M 3)])])),(59,(M 30),(L [14,6,4] [] [4] [(L [4,2] [] [5] [(M 3)]),(L [4,2] [2,5] [4,10,4] [(M 3)]),(L [4,4] [] [10] [(M 3),(T 4 [] [5])]),(L [4,2] [2,3,2] [4,6,4,14] [(M 3)]),(L [4,4] [] [5] [(M 3),(T 4 [] [14])]),(M 3),(L [18,6] [] [4] [(L [4] [] [5] [(R1 1 [] 7)]),(L [4] [] [5] [(R1 1 [] 7)]),(T 18 [] [14]),(L [22] [] [4] [(R1 1 [] 0),(R1 1 [] 0)])]),(L [14,6] [] [14] [])])),(61,(L [10,4,3] [5,2] [10,4,6] [(L [4,3] [] [4] [(M 6),(T 4 [] [5])]),(L [4,3] [] [6] [(M 6),(T 4 [] [4])]),(L [4,3] [] [4] [(M 6),(T 4 [] [4])]),(M 6),(L [10,4] [5] [10,4] [])]),(L [10,4,2] [2,5,2] [4,10,4,6] [(L [4,2] [] [4] [(M 3)]),(L [4,2] [2] [4,6] [(M 3)]),(L [4,2] [17] [34,4] [(M 3)]),(M 3)])),(67,(L [8,4,3] [2,3,2,7,2] [4,6,4,14,4,34] [(L [4,3] [] [4] [(M 6),(T 4 [] [4])]),(L [4,3] [] [6] [(M 6),(T 4 [] [5])]),(M 6),(L [10,4] [] [5] [(T 4 [] [6])])]),(L [8,4,2] [2,3,2,7,2] [4,6,4,14,4,34] [(L [4,2] [] [4] [(M 3)]),(L [4,2] [] [6] [(M 3)]),(M 3)])),(71,(M 18),(L [10,4,2] [3] [6,4] [(L [2,2] [2,3] [4,6,4] []),(L [2,2] [7,2,5,2,3,2] [14,4,10,4,6,4,22] []),(L [4,2] [] [5] [(M 3)]),(M 3)])),(73,(L [10,4,3] [] [4] [(L [4,3] [] [5] [(M 6),(T 4 [] [6])]),(L [4,3] [] [4] [(M 6),(T 4 [] [22])]),(L [2,3] [2,5,2,3,2,11] [4,10,4,6,4,22,4] [(L [4] [] [4] [(M 6)])]),(M 6),(L [10,4] [] [4] [])]),(L [10,4,2] [] [4] [(L [4,2] [] [5] [(M 3)]),(L [4,4] [] [4] [(M 3),(M 3)]),(L [2,2] [2,5,2,3,2,11] [4,10,4,6,4,22,4] []),(M 3)])),(79,(M 10),(L [10,4,2] [] [5] [(L [4,2] [] [5] [(M 3)]),(L [4,2] [] [14] [(M 3)]),(L [2,2] [2,13,2,3] [4,26,4,6,4] []),(M 3)])),(83,(M 6),(L [12,4,2] [] [5] [(L [2,2] [2] [4,10] []),(L [2,2] [11,2,5] [22,4,10,4] []),(L [2,2] [2,3,2] [4,6,4,10] []),(L [4,4] [] [5] [(M 3),(M 19)]),(M 3)])),(89,(M 90),(L [10,4,2] [] [5] [B,(L [4,4] [] [5] [(M 3),(L [6] [] [7] [(R1 1 [] 2)])]),(L [4,2] [] [4] [(M 3)]),(M 3)])),(97,(L [8,2,1] [2,7,2,11,2] [4,14,4,22,4,6] [B,(L [4,1] [5] [10,4] [(M 6)])]),(L [6,2,2] [2,5,2,3,2,7,2,11,2] [4,10,4,6,4,14,4,22,4,6] [B])),(101,(M 6),(L [8,2,2] [2,5,2] [4,10,4,6] [B,(L [4,2] [] [6] [(M 3)])])),(103,(L [8,4,3] [] [4] [B,(L [4,3] [] [5] [(M 6),(T 4 [] [4])]),(M 6),(L [10,4] [] [5] [(T 4 [] [4])])]),(L [8,4,2] [] [4] [B,(L [4,2] [] [5] [(M 3)]),(M 3)])),(107,(M 54),(L [10,4,2] [] [4] [B,B,(L [4,2] [] [5] [B]),B]))])) (M 18) (R2 167 [(19,A,A),(23,A,A),(29,A,A),(31,A,A),(37,A,A),(41,A,A),(43,A,A),(47,A,A),(53,A,A),(59,A,A),(61,(X [6,2,1] [(X [2,3] [(X [4] [(R1 2 [] 2)])])]),A),(67,(M 34),(X [6,2,2] [(L [4,4] [2] [4,6] [(L [4] [] [5] [(M 3)]),(M 3)])])),(71,(M 18),(X [6,2,2] [(L [4,2] [23] [46,4] [(L [4] [] [5] [(R1 1 [] 2)])])])),(73,(X [6,2,1] [(L [4,3] [] [5] [(L [3] [] [26] [(R1 2 [] 3)]),(T 4 [] [4])])]),(X [6,2,2] [(L [4,2] [] [5] [(T 2 [] [26])])])),(79,(M 10),(X [6,2,2] [(L [4,2] [] [4] [(T 2 [] [5])])])),(83,(M 6),(X [8,4,2] [(L [4,2] [] [22] [(T 2 [] [5])]),(L [6,4] [] [10] [(L [4] [] [58] [(R1 1 [] 2)]),(L [4] [] [4] [(R1 1 [] 5)]),(T 6 [] [26])]),(L [18,4] [2,113] [4,226,4] [(L [4] [3] [6,4] [(R1 1 [] 2)]),(L [4] [] [5] [(R1 1 [] 23)]),(L [4] [] [4] [(R1 1 [] 2)]),(L [4] [2] [4,6] [(R1 1 [] 2)]),(L [4] [] [4] [(R1 1 [] 0)]),(T 18 [2] [4,6])])])),(89,(M 90),(L [12,4,4] [2,3,2] [4,6,4,14] [(L [2,2] [3,2,7,2,5,2,3,2,11] [6,4,14,4,10,4,6,4,22,4] []),(L [4,2] [2,5] [4,10,4] [(T 2 [2] [4,6])]),(L [6,4] [] [4] [(L [4] [] [4] [(R1 1 [] 2)]),(L [4] [] [5] [(R1 1 [] 2)]),(T 6 [] [6])]),(L [4,4] [2] [4,6] [(T 2 [3,2] [6,4,14]),(T 4 [2,11] [4,22,4])]),(L [12,2] [2,5] [4,10,4] []),(L [14,6] [] [5] [(T 4 [2,23] [4,46,4]),(T 14 [] [4])])])),(97,(L [14,6,3] [] [4] [(L [4,3] [] [10] [(L [3] [] [26] [(R1 2 [] 2)]),(T 4 [] [4])]),(L [4,3] [] [4] [(L [3] [] [4] [(R1 2 [] 5)]),(T 4 [] [4])]),(L [4,3] [] [4] [(L [3] [] [4] [(R1 2 [] 2)]),(T 4 [2] [4,10])]),(L [4,3] [] [34] [(L [3] [] [4] [(R1 2 [] 17)]),(T 4 [] [4])]),(L [4,3] [] [5] [(L [3] [] [26] [(R1 2 [] 2)]),(T 4 [3] [6,4])]),(L [14,3] [] [4] [(T 14 [] [4])]),(L [14,3] [] [5] [(T 14 [] [4])]),(L [14,6] [] [4] [])]),(L [14,6,4] [] [4] [(L [4,2] [] [10] [(T 2 [] [26])]),(L [4,2] [] [4] [(T 2 [5] [10,4])]),(L [4,2] [13] [26,4] [(T 2 [] [4])]),(L [4,2] [] [34] [(T 2 [] [4])]),(L [4,2] [] [5] [(T 2 [] [26])]),(L [14,2] [13] [26,4] []),(L [14,2] [] [5] []),(M 3)])),(101,(M 102),(L [12,4,2] [2] [4,6] [(L [4,2] [] [5] [(T 2 [] [4])]),(L [4,2] [11] [22,4] [(T 2 [] [4])]),(L [4,2] [2] [4,6] [(T 2 [] [4])]),(L [6,4] [] [4] [(T 2 [3] [6,4]),(T 2 [] [5]),(T 6 [] [5])]),(L [12,2] [2] [4,10] [])])),(103,(L [12,6,3] [] [5] [(L [4,3] [] [4] [(L [3] [] [6] [(R1 2 [] 0)]),(T 4 [] [4])]),(L [4,3] [] [4] [(L [3] [] [6] [(R1 2 [] 2)]),(T 4 [] [10])]),(L [4,3] [] [4] [(L [3] [] [5] [(R1 2 [] 2)]),(T 4 [] [4])]),(L [4,3] [] [10] [(L [3] [] [6] [(R1 2 [] 0)]),(T 4 [] [38])]),(L [12,3] [] [4] [(T 12 [] [4])]),(L [12,3] [] [4] [(T 12 [] [4])]),(L [12,6] [] [4] [])]),(L [12,6,4] [] [5] [(L [4,2] [] [4] [(T 2 [] [6])]),(L [4,2] [] [4] [(T 2 [] [6])]),(L [4,2] [] [4] [(T 2 [] [5])]),(L [4,2] [] [10] [(T 2 [] [6])]),(L [12,2] [] [4] []),(L [12,2] [] [4] []),(M 3)])),(107,(M 54),(L [10,4,2] [2] [4,34] [(L [4,2] [] [4] [(T 2 [] [10])]),(L [4,2] [] [4] [(T 2 [] [5])]),(L [6,4] [] [4] [(T 2 [] [4]),(T 2 [] [5]),(T 6 [] [5])]),(L [10,2] [19] [38,4] [])])),(109,(M 10),(L [10,4,2] [5] [10,4] [(L [2,2] [2,11,2,5] [4,22,4,10,4] []),(L [4,2] [] [4] [(T 2 [] [10])]),(L [4,4] [] [4] [(T 2 [] [10]),(M 3)]),(L [10,2] [2] [4,22] [])])),(113,(M 6),(L [8,4,2] [2,17,2,5,2] [4,34,4,10,4,6] [(L [4,2] [] [5] [(T 2 [] [6])]),(L [4,2] [2] [4,6] [(T 2 [] [5])]),(L [12,2] [] [5] [(T 2 [] [4]),(T 2 [] [4])])])),(127,(L [8,4,3] [2,5,2] [4,10,4,26] [B,(L [4,1] [3,2,13] [6,4,26,4] [(L [3] [] [6] [(R1 2 [] 2)])]),(L [10,3] [5] [10,4] [(L [3] [] [5] [(R1 2 [] 2)]),(T 10 [] [4])]),(L [10,4] [3] [6,4] [(T 4 [] [5])])]),(L [8,4,2] [2,5,2] [4,10,4,26] [B,(L [2,2] [3,2,5,2,7,2,3,2,13] [6,4,10,4,14,4,6,4,26,4] []),(L [10,2] [5] [10,4] [(T 2 [] [5])])])),(131,(M 6),(L [10,4,2] [] [5] [B,(L [4,2] [] [5] [(T 2 [] [4])]),(L [4,2] [] [6] [(T 2 [] [4])]),(L [10,2] [] [5] [])])),(137,(M 6),(L [8,4,2] [2,5] [4,10,4] [B,(L [4,2] [] [5] [(T 2 [] [6])]),(L [8,2] [5,2] [10,4,6] [])])),(139,(M 10),(L [12,4,2] [] [4] [B,(L [4,2] [] [5] [(T 2 [] [4])]),(L [2,2] [3,2,7,2,5,2,3,2] [6,4,14,4,10,4,6,4,22] []),(L [4,2] [] [5] [(T 2 [] [14])]),(L [12,2] [] [14] [])])),(149,(M 150),(L [10,4,2] [] [4] [B,(L [4,2] [] [4] [(T 2 [] [4])]),(L [2,2] [3,2,5,2,11,2,3] [6,4,10,4,22,4,6,4] []),(L [10,2] [2] [4,10] [])])),(151,(L [8,4,1] [5,2,11,2] [10,4,22,4,6] [B,(L [4,3] [] [4] [(L [3] [] [4] [(R1 2 [] 2)]),(T 4 [] [4])]),(L [12,3] [] [4] [(L [3] [] [4] [(R1 2 [] 0)]),(L [3] [] [5] [(R1 2 [] 2)]),(T 12 [] [4])])]),(L [8,4,2] [11,2] [22,4,6] [B,(L [4,2] [] [4] [(T 2 [] [4])]),(L [12,2] [] [4] [(T 2 [] [4]),(T 2 [] [5])])])),(157,(L [10,4,3] [] [4] [B,(L [4,1] [3] [6,4] [B]),(L [4,1] [3] [6,4] [(T 1 [3] [6,4])]),(L [12,3] [] [4] [(L [3] [] [5] [(R1 2 [] 2)]),(T 12 [] [4])]),(L [12,4] [] [5] [(T 4 [] [4])])]),(L [10,4,2] [] [4] [B,(L [4,2] [] [4] [B]),(L [4,2] [] [4] [(T 2 [] [4])]),(L [12,2] [] [4] [(T 2 [] [5])])])),(163,(L [12,4,3] [] [5] [B,B,(L [4,1] [2] [4,6] [B]),(L [4,1] [3] [6,4] [(L [3] [] [5] [B])]),(L [12,3] [] [5] [B]),(L [12,4] [3] [6,4] [])]),(L [12,4,2] [] [5] [B,B,(L [4,2] [] [6] [B]),(L [4,2] [] [4] [(T 2 [] [5])]),(L [12,2] [] [5] [])]))])) (X [4,3] [(X [6] [(R2 773 [(17,A,A),(19,A,A),(23,A,A),(29,A,A),(31,A,A),(37,A,A),(41,A,A),(43,A,A),(47,A,A),(53,A,A),(59,A,A),(61,A,A),(67,A,A),(71,A,A),(73,A,A),(79,A,A),(83,A,A),(89,A,A),(97,A,A),(101,A,A),(103,A,A),(107,A,A),(109,A,A),(113,A,A),(127,A,A),(131,A,A),(137,A,A),(139,A,A),(149,A,A),(151,A,A),(157,A,A),(163,A,A),(167,A,A),(173,A,A),(179,A,A),(181,A,A),(191,A,A),(193,A,A),(197,A,A),(199,A,A),(211,A,A),(223,A,A),(227,A,A),(229,A,A),(233,A,A),(239,A,A),(241,A,A),(251,A,A),(257,A,A),(263,A,A),(269,A,A),(271,A,A),(277,A,A),(281,A,A),(283,A,A),(293,A,A),(307,A,A),(311,A,A),(313,A,A),(317,A,A),(331,A,A),(337,A,A),(347,A,A),(349,A,A),(353,A,A),(359,A,A),(367,A,A),(373,A,A),(379,A,A),(383,A,A),(389,(M 390),(L [4] [] [10] [(R1 2 [] 2)])),(397,(L [3] [] [4] [(R1 2 [] 2)]),(T 2 [2,7,2,5] [4,14,4,10,4])),(401,(M 6),(T 2 [2,5] [4,10,4])),(409,(M 10),(T 2 [] [4])),(419,(M 30),(T 2 [] [5])),(421,(L [3] [] [4] [(R1 2 [] 2)]),(T 2 [] [4])),(431,(M 54),(T 2 [] [4])),(433,(L [3] [] [4] [(R1 2 [] 2)]),(T 2 [] [4])),(439,(M 10),(T 2 [] [14])),(443,(M 6),(T 2 [] [4])),(449,(M 450),(T 2 [] [5])),(457,(L [3] [] [4] [(R1 2 [] 2)]),(T 2 [] [4])),(461,(M 6),(T 2 [] [4])),(463,(L [3] [] [5] [(R1 2 [] 3)]),(T 2 [] [5])),(467,(M 234),(T 2 [] [4])),(479,(M 30),(T 2 [] [4])),(487,(L [3] [] [14] [(R1 2 [] 3)]),(T 2 [] [14])),(491,(M 6),(T 2 [] [4])),(499,(M 50),(T 2 [] [5])),(503,(M 18),(T 2 [] [6])),(509,(M 30),(T 2 [] [5])),(521,(M 18),(T 2 [] [6])),(523,(L [3] [] [5] [(R1 2 [] 3)]),(T 2 [] [5])),(541,(T 1 [2,3,2,5,2,23] [4,6,4,10,4,46,4]),(T 2 [] [4])),(547,(L [3] [] [4] [(R1 2 [] 2)]),(T 2 [] [4])),(557,(M 18),(T 2 [] [14])),(563,(M 6),(T 2 [] [5])),(569,(M 30),(T 2 [] [6])),(571,(M 26),(T 2 [] [4])),(577,(L [3] [] [4] [(R1 2 [] 2)]),(T 2 [] [4])),(587,(M 6),(T 2 [] [10])),(593,(M 54),(T 2 [] [6])),(599,(M 150),(T 2 [] [4])),(601,(T 1 [2,3,2,5] [4,6,4,10,4]),(T 2 [] [4])),(607,(L [3] [] [22] [(R1 2 [] 0)]),(T 2 [] [22])),(613,(T 1 [2,3] [4,6,4]),(T 2 [] [4])),(617,(M 6),(T 2 [] [34])),(619,(M 10),(T 2 [] [5])),(631,(L [3] [] [4] [(R1 2 [] 0)]),(T 2 [] [4])),(641,(M 6),(T 2 [] [6])),(643,(L [3] [] [5] [(R1 2 [] 3)]),(T 2 [] [5])),(647,(M 162),(T 2 [] [4])),(653,(M 6),(T 2 [] [26])),(659,(M 30),(T 2 [] [4])),(661,(T 1 [2,7] [4,14,4]),(T 2 [] [4])),(673,(T 1 [2,3] [4,6,4]),(T 2 [] [4])),(677,(M 6),(T 2 [] [4])),(683,(M 18),(T 2 [] [4])),(691,(L [3] [] [6] [(R1 2 [] 0)]),(T 2 [] [6])),(701,(M 702),(T 2 [] [5])),(709,(M 10),(T 2 [] [46])),(719,(M 90),(T 2 [] [6])),(727,(M 26),(T 2 [] [4])),(733,(T 1 [2] [4,6]),(T 2 [] [6])),(739,(M 10),(T 2 [] [5])),(743,(M 6),(T 2 [] [6])),(751,(L [3] [] [5] [(R1 2 [] 2)]),(T 2 [] [5])),(757,(T 1 [2] [4,14]),(T 2 [] [14])),(761,(M 6),(T 2 [] [4])),(769,(M 10),(T 2 [] [4]))])])]) A) A A) A A A A) (M 6) (K 7))
private theorem t0 : checkChunk ts 0 c0 = true := by decide +kernel
private theorem t1 : checkChunk ts 1 c1 = true := by decide +kernel
private theorem t2 : checkChunk ts 2 c2 = true := by decide +kernel
private theorem t3 : checkChunk ts 3 c3 = true := by decide +kernel
private theorem t4 : checkChunk ts 4 c4 = true := by decide +kernel
private theorem t5 : checkChunk ts 5 c5 = true := by decide +kernel
private theorem t6 : checkChunk ts 6 c6 = true := by decide +kernel
private theorem t7 : checkChunk ts 7 c7 = true := by decide +kernel
private theorem t8 : checkChunk ts 8 c8 = true := by decide +kernel

theorem prove_H1 : OMA.R_Erdos470_erdos_470_variants_odd_weird_prime_div_R1_H2_R1.H1 := by
  intro m hm_odd hm_ab hm_card hm_prim hm_le hm_primes E hE_lt_int
  clear hm_le hm_primes
  have h_dvd3 : 3 ∣ m := three_dvd_of_odd_abundant hm_odd hm_ab hm_card
  have h64 : 64 ≤ m := sixtyFour_le_of_odd_abundant_three_dvd hm_odd hm_ab h_dvd3
  have hE_lt : sigma 1 m - 2 * m < 64 := by dsimp only [E] at hE_lt_int; omega
  have hc0 : ∀ i < 0, ∀ sp mp, ts[i]? = some (sp, mp) → SpecValid m sp mp → Goal m := fun _ hi => absurd hi (Nat.not_lt_zero _)
  have hc1 := checkChunk_sound hm_odd hm_ab hm_card hm_prim hE_lt h64 ts 0 c0 t0 hc0
  have hc2 := checkChunk_sound hm_odd hm_ab hm_card hm_prim hE_lt h64 ts 1 c1 t1 hc1
  have hc3 := checkChunk_sound hm_odd hm_ab hm_card hm_prim hE_lt h64 ts 2 c2 t2 hc2
  have hc4 := checkChunk_sound hm_odd hm_ab hm_card hm_prim hE_lt h64 ts 3 c3 t3 hc3
  have hc5 := checkChunk_sound hm_odd hm_ab hm_card hm_prim hE_lt h64 ts 4 c4 t4 hc4
  have hc6 := checkChunk_sound hm_odd hm_ab hm_card hm_prim hE_lt h64 ts 5 c5 t5 hc5
  have hc7 := checkChunk_sound hm_odd hm_ab hm_card hm_prim hE_lt h64 ts 6 c6 t6 hc6
  have hc8 := checkChunk_sound hm_odd hm_ab hm_card hm_prim hE_lt h64 ts 7 c7 t7 hc7
  have hc9 := checkChunk_sound hm_odd hm_ab hm_card hm_prim hE_lt h64 ts 8 c8 t8 hc8
  rcases root_specValid hm_odd h_dvd3 with ⟨_, hs1⟩ | ⟨_, hs2⟩ | ⟨_, _, hs3⟩ | ⟨_, _, hs4⟩
  · exact goal_to_H1 hm_ab h64 hE_lt_int (hc9 0 (by decide) _ _ rfl hs1)
  · exact goal_to_H1 hm_ab h64 hE_lt_int (hc9 1 (by decide) _ _ rfl hs2)
  · exact goal_to_H1 hm_ab h64 hE_lt_int (hc9 4 (by decide) _ _ rfl hs3)
  · exact goal_to_H1 hm_ab h64 hE_lt_int (hc9 8 (by decide) _ _ rfl hs4)

end Erdos470H1Proof

theorem OMA.solution : OMA.R_Erdos470_erdos_470_variants_odd_weird_prime_div_R1_H2_R1.H1 :=
  Erdos470H1Proof.prove_H1
