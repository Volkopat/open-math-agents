import OMAStatements.S_oeis_a059992

/-
Problem: De Vlieger's inclusion for OEIS A059992.
Credit: @marcusbuffett. Thanks to @marcelopierry for the earlier 2-adic plan on the desk.

Represent a record and its challenger by decreasing exponent vectors on the
first primes. Single- and triple-prime exchanges constrain the exponents.
A central binomial coefficient estimate forces more common factors of two
than the divisor-count gap allows for large supports. On the ten remaining
support pairs, check the ordered root boxes using the certificate witnesses.
-/

namespace A059992Certificate

def witnesses : List (List Nat) := [
  [2,1,1],
  [3,1,1],
  [3,2,1],
  [4,2,1],
  [3,1,1,1],
  [4,1,1,1],
  [3,2,1,1],
  [3,2,1,1,1],
  [4,4,1,1],
  [4,2,2,1],
  [4,3,1,1,1],
  [6,2,1,1,1],
  [6,3,1,1,1],
  [5,2,1,1,1,1],
  [4,2,1,1,1,1],
  [4,3,1,1,1,1],
  [5,3,1,1,1,1],
  [4,4,2,1,1,1],
  [5,3,1,1,1,1,1]
]

def programs : List (List (List Nat)) := [
  [[1,2],[0,1,0,1],[2],[1]],
  [[2,3],[0,1,2,1],[0,0,0,4],[0,0,1,1],[1],[0,0,1,2],[0,1,0,2],[3],[5,0,1,3],[3],[3],[1]],
  [[2,4],[5,2,3,4]],
  [[3,4],[0,1,3,1],[0,0,0,4],[0,0,1,2],[0,0,2,1],[3],[0,0,0,2],[4,4],[0,0,0,3],[4,5],[4,6],[3],[3],[5,7,8,4]],
  [[3,5],[5,9,8,4]],
  [[4,5],[0,0,0,2],[1],[0,0,0,3],[3],[0,0,2,2],[0,0,3,1],[3],[0,1,2,1],[0,0,1,3],[0,0,1,2],[0,0,0,5],[5,10,11,4],[4,12],[3],[4,13],[3],[3]],
  [[4,6],[0,0,0,6],[0,0,2,1],[1],[0,0,2,2],[0,1,1,2],[3],[0,0,1,4],[5,14,15,5],[0,0,0,5],[3],[5,15,16,5],[3],[3]],
  [[4,7],[0,0,2,2],[1],[3]],
  [[5,7],[0,0,0,6],[0,0,2,1],[1],[0,0,2,2],[0,1,1,2],[3],[5,17,18,5],[3],[3]],
  [[5,8],[0,0,2,2],[1],[3]]
]

-- Indices into the prime table and into box coordinates are zero-based.
def primes : List Nat :=
  [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97,101,103,107,109,113,127,131,137]

def p (i : Nat) := primes[i]!
def exps (j : Nat) (f : Nat → Nat) := (List.range j).map f
def D (es : List Nat) := (es.map Nat.succ).prod
def V (es : List Nat) := (es.zipWith (fun e q => q^e) primes).prod
def floorLog (q x : Nat) := ((List.range 8).filter (fun i => q^(i+1) ≤ x)).length
def c (j i : Nat) := floorLog (p i) (p j) + 1
def onesCount (j : Nat) := ([0,0,0,0,0,1,2,2,3,4,4] : List Nat)[j]?.getD 5
def suffix (es : List Nat) (s : Nat) := es.take (es.length-s) ++ List.replicate s 1
def mUpper (j gap : Nat) := suffix (exps j (fun i => 2*c j i-1+(gap-1)/2^(j-1))) (onesCount j)
def nLower (k : Nat) := exps k (fun i => max 1 (floorLog (p i) (p (k-1)-1)))
def nUpper (k : Nat) := suffix (exps k (fun i => 2*c k i-2)) (onesCount k)

def triple (a b s : Nat) :=
  let t := a-s+1
  s == 0 || (t ≥ 3 && p (t-3)*p (t-2)*p (t-1) > p b*p (b+1))

def smallPrimeChecks :=
  ((List.range 138).filter Nat.Prime == primes) &&
  ((List.range 10).all fun i => triple (i+1) (i+1) (onesCount (i+1))) &&
  ([[11,12,5],[13,15,5],[16,31,6]] : List (List Nat)).all fun r =>
    triple r[0]! r[1]! r[2]! && 2^r[2]! > 2*r[1]!

def chebRows := ([[32,47,7,9,450],[48,63,7,10,660],[64,127,8,11,1430]] : List (List Nat)).all fun r =>
  let a := r[0]!; let b := r[1]!; let s := r[2]!; let v := r[3]!; let x := r[4]!
  x%2 == 0 && x ≥ 8 && x ≤ 2^v && x ≥ v*(b+3) &&
    a ≥ s+4 && (3*(a-s-1)-5)^3 > x^2 && 2^s > 2*b

def cutoffs : List Nat := [2,4,5,7,8,9,10,14,17,19]
def lowerWitness : List (List Nat) :=
  [[],[3,2,1,1,1],[5,3,1,1,1],[4,3,2,1,1,1,1],[6,2,2,1,1,1,1,1],
   [6,3,2,2,1,1,1,1,1],[6,3,2,2,1,1,1,1,1,1],[],[],[]]

def cutoffChecks :=
  ((List.range 7).all fun i =>
    let j := i+1
    2^(3*j+1) > (exps j (fun t => 4*c j t-1)).prod + (2*j+1)) &&
  ((List.range 10).all fun i =>
    let j := i+1; let k := cutoffs[i]!+1; let w := lowerWitness[i]!
    let cap := D (mUpper j (2*j)) + 2*j
    2^k > cap || (V w ≤ V (nLower k) && D w > cap))

def pairs := (List.range 10).flatMap fun i =>
  let j := i+1
  (((List.range (cutoffs[i]!-j)).map (fun h => j+h+1)).filter
    (fun k => 2^(min (onesCount j) (onesCount k)) ≤ k-j)).map (fun k => [j,k])

-- f(e+1)/f(e) decreases for f(e)=(e+1)^b/q^e. The two neighboring comparisons
-- certify a maximum on all positive exponents.
def maximizers (b : Nat) : List Nat := match b with
  | 3 => [3,2] | 4 => [5,3,2,1] | 5 => [6,4,2,2,1] | _ => []
def peakChecks := [3,4,5].all fun b => ((maximizers b).zip primes).all fun (e,q) =>
  e ≥ 1 && (e == 1 || q*e^b ≤ (e+1)^b) && (e+2)^b ≤ q*(e+1)^b

structure Box where
  ml : List Nat
  mu : List Nat
  nl : List Nat
  nu : List Nat

def fixed (lo hi : List Nat) :=
  (lo.zipWith (fun a b => if a == b then a+1 else 1) hi).prod

def closes (j gap : Nat) (b : Box) (op : List Nat) : Bool :=
  let dl := max (D b.nl) (D b.ml+1)
  let du := min (D b.nu) (D b.mu+gap)
  let x := max 7 (max (V b.ml+1) (V b.nl))
  match op with
  | [1] => dl > du
  | [2] => x > V b.nu
  | [3] => (fixed b.ml b.mu).gcd (fixed b.nl b.nu) > gap
  | [4,i] => let w := witnesses[i]!; V w < x && D w ≥ du
  | [5,i,h,a] =>
    let w := witnesses[i]!; let u := witnesses[h]!; let e := (maximizers a).take j
    let md := max dl (D w+1) - gap
    e.length == j && V w < x && D u ≥ du &&
      (D e)^a * min (V u) (V b.nu) ≤ V e * md^a
  | _ => false

def split (b : Box) (side i h : Nat) : Box × Box :=
  let left (es : List Nat) := es.mapIdx (fun t e => if t ≥ i then min e h else e)
  let right (es : List Nat) := es.mapIdx (fun t e => if t ≤ i then max e (h+1) else e)
  if side == 0 then ({b with mu := left b.mu}, {b with ml := right b.ml})
  else ({b with nu := left b.nu}, {b with nl := right b.nl})

def replay (j gap : Nat) : List (List Nat) → List Box → Bool
  | [], bs => bs.isEmpty
  | _, [] => false
  | op::ops, b::bs => match op with
    | [0,side,i,h] =>
      let (l,r) := split b side i h
      i < (if side == 0 then b.ml else b.nl).length && replay j gap ops (l::r::bs)
    | _ => closes j gap b op && replay j gap ops bs

def runProgram : List (List Nat) → Bool
  | [j,k]::ops => replay j (k-j) ops [⟨List.replicate j 1, mUpper j (k-j), nLower k, nUpper k⟩]
  | _ => false

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem finite_certificate :
    (smallPrimeChecks && chebRows && cutoffChecks && peakChecks &&
     (programs.map (fun t => t.head!) == pairs) && programs.all runProgram) = true := by decide

end A059992Certificate

namespace A059992
open Finset
noncomputable abbrev q := Nat.nth Nat.Prime

theorem q_strict : StrictMono q := Nat.nth_strictMono Nat.infinite_setOfPred_prime

theorem cheb (t : ℕ) (ht : 4 ≤ t) :
    2^(2*t) < (2*t)^((2*t).primeCounting+1) := by
  have he : 2^(2*t) = 4^t := by rw [pow_mul]; norm_num
  rw [he, pow_succ]
  have hprod : t.centralBinom ≤ (2*t)^(2*t).primeCounting := by
    rw [← Nat.prod_pow_factorization_centralBinom t]
    have hf : (∏ p ∈ range (2*t+1), p ^ t.centralBinom.factorization p) =
        ∏ p ∈ (2*t).primesLE, p ^ t.centralBinom.factorization p := by
      symm
      apply prod_subset (filter_subset _ _)
      intro p hp hnp
      have : ¬ p.Prime := fun h => hnp (mem_filter.mpr ⟨hp,h⟩)
      simp [Nat.factorization_eq_zero_of_not_prime _ this]
    rw [hf]
    calc
      _ ≤ ∏ _p ∈ (2*t).primesLE, (2*t) := by
        apply prod_le_prod' (fun p _ => ?_)
        simpa [Nat.centralBinom_eq_two_mul_choose] using
          (Nat.pow_factorization_choose_le (p := p) (k := t) (n := 2*t) (by omega))
      _ = _ := by simp [Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range,
        Nat.primesLE_eq_filter_range]
  exact (Nat.four_pow_lt_mul_centralBinom t ht).trans_le (by nlinarith)

theorem q_bound {t v i : ℕ} (ht : 4 ≤ t) (hv : 2*t ≤ 2^v) (hi : v*(i+1) ≤ 2*t) :
    q i ≤ 2*t := by
  have hc := cheb t ht
  by_contra! hn
  have hl : (2*t).primeCounting ≤ i :=
    Nat.le_nth_of_count_le (p := Nat.Prime) (Nat.succ_le_of_lt hn : 2*t+1 ≤ q i)
  have hh : (2*t)^((2*t).primeCounting+1) ≤ (2^v)^(i+1) :=
    (Nat.pow_le_pow_left hv _).trans (Nat.pow_le_pow_right (by positivity) (by omega))
  rw [← pow_mul] at hh
  exact (not_lt_of_ge (Nat.pow_le_pow_right (by decide : 0 < 2) hi)) (hc.trans_le hh)

theorem lower_q (i : ℕ) : 3*i ≤ q i + 8 := by
  by_cases h : q i < 7
  · have hp := Nat.add_two_le_nth_prime i
    change i+2 ≤ q i at hp
    have hcnt := Nat.monotone_primeCounting' h.le
    rw [Nat.primeCounting'_nth_eq] at hcnt
    have : Nat.primeCounting' 7 = 3 := by decide
    omega
  · have hh := Nat.primeCounting'_add_le (a:=6) (k:=7) (by decide) (by decide) (q i - 7)
    have he : 7 + (q i - 7) = q i := by omega
    rw [he, Nat.primeCounting'_nth_eq] at hh
    have h1 : Nat.primeCounting' 7 = 3 := by decide
    have h2 : Nat.totient 6 = 2 := by decide
    rw [h1,h2] at hh
    omega


def Triple (h s : ℕ) : Prop := s+2 ≤ h ∧
  q h * q (h+1) < q (h-s-2) * q (h-s-1) * q (h-s)

theorem triple_of_cube {h s x : ℕ} (hs : s+2 ≤ h) (hx : q (h+1) ≤ x)
    (hb : x^2 ≤ (q (h-s-2))^3) : Triple h s := by
  have hp := q_strict.monotone (Nat.le_succ h)
  have ha := q_strict (show h-s-2 < h-s-1 by omega)
  have hc := q_strict (show h-s-1 < h-s by omega)
  have hn := Nat.add_two_le_nth_prime (h-s-2)
  change h-s-2+2 ≤ q (h-s-2) at hn
  refine ⟨hs, (Nat.mul_le_mul (hp.trans hx) hx).trans_lt ?_⟩
  rw [← sq]
  apply hb.trans_lt
  exact (by rw [pow_succ, sq]; gcongr <;> omega : (q (h-s-2))^3 < q (h-s-2)*q (h-s-1)*q (h-s))

theorem dyadic_aux (u : ℕ) (hu : 7 ≤ u) : 3*u+20 ≤ 2^u ∧
    4*(u+1) ≤ 2^u ∧ 2*(u+1)^2 ≤ 2^u := by
  induction u, hu using Nat.le_induction with
  | base => decide
  | succ u hu ih =>
    obtain ⟨h1,h2,h3⟩ := ih
    rw [pow_succ]
    refine ⟨by omega, by omega, ?_⟩
    nlinarith [Nat.zero_le ((u-2)^2), Nat.mul_le_mul_right u hu]

theorem dyadic_triple {h u : ℕ} (hu : 7 ≤ u) (hl : 2^u ≤ h) (hr : h < 2^(u+1)) :
    Triple h (u+2) ∧ 2*h < 2^(u+2) := by
  obtain ⟨h1,h2,h3⟩ := dyadic_aux u hu
  rw [pow_succ] at hr
  let t := 2^u*(2*u+2)
  have ht : 4 ≤ t := by dsimp [t]; nlinarith
  have hv : 2*t ≤ 2^(2*u) := by
    rw [two_mul u, pow_add]
    dsimp [t]
    nlinarith [Nat.mul_le_mul_left (2^u) h2]
  have hi : 2*u*((h+1)+1) ≤ 2*t := by
    dsimp [t]
    nlinarith [Nat.mul_le_mul_left (2*u) (show h+2 ≤ 2^u*2+1 by omega)]
  have hx := q_bound ht hv hi
  have hp := lower_q (h-(u+2)-2)
  have hd : 2*2^u ≤ q (h-(u+2)-2) := by omega
  have hc : (2*t)^2 ≤ (2*2^u)^3 := by
    dsimp [t]
    nlinarith [Nat.mul_le_mul_left (8*(2^u)^2) h3]
  exact ⟨triple_of_cube (by omega) hx (hc.trans (Nat.pow_le_pow_left hd 3)), by
    rw [show u+2=u+1+1 by omega, pow_succ, pow_succ]; omega⟩

theorem row_triple {a b s v t h : ℕ} (hal : a ≤ h) (hbr : h ≤ b)
    (hs : s+2 ≤ a) (ht : 4 ≤ t) (hv : 2*t ≤ 2^v) (hi : v*(b+2) ≤ 2*t)
    (hb : (2*t)^2 ≤ (3*(a-s-2)-8)^3) : Triple h s := by
  have hp := lower_q (h-s-2)
  exact triple_of_cube (by omega)
    (q_bound ht hv (le_trans (Nat.mul_le_mul_left _ (by omega)) hi))
    (hb.trans (Nat.pow_le_pow_left (by omega) _))

theorem small_row {a b s h : ℕ} (hl : a ≤ h) (hr : h ≤ b) (hs : s+2 ≤ a)
    (hh : q b * q (b+1) < q (a-s-2)*q (a-s-1)*q (a-s)) : Triple h s := by
  refine ⟨by omega, (Nat.mul_le_mul (q_strict.monotone hr) (q_strict.monotone (by omega))).trans_lt
    (hh.trans_le ?_)⟩
  gcongr <;> apply q_strict.monotone <;> omega

theorem q_eq {i p : ℕ} (hp : p.Prime) (hi : Nat.count Nat.Prime p = i) : q i = p :=
  hi ▸ Nat.nth_count hp


set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem many_ones_test (h : ℕ) (hh : 11 ≤ h) : ∃ s, Triple h s ∧ 2*h < 2^s := by
  by_cases h12 : h ≤ 12
  · refine ⟨5, small_row hh h12 (by decide) ?_, by omega⟩
    norm_num only
    rw [q_eq (p:=41) (by decide) (by decide), q_eq (p:=43) (by decide) (by decide),
      q_eq (p:=11) (by decide) (by decide), q_eq (p:=13) (by decide) (by decide),
      q_eq (p:=17) (by decide) (by decide)]
    decide
  by_cases h15 : h ≤ 15
  · refine ⟨5, small_row (a:=13) (by omega) h15 (by decide) ?_, by omega⟩
    norm_num only
    rw [q_eq (p:=53) (by decide) (by decide), q_eq (p:=59) (by decide) (by decide),
      q_eq (p:=17) (by decide) (by decide), q_eq (p:=19) (by decide) (by decide),
      q_eq (p:=23) (by decide) (by decide)]
    decide
  by_cases h31 : h ≤ 31
  · refine ⟨6, small_row (a:=16) (by omega) h31 (by decide) ?_, by omega⟩
    norm_num only
    rw [q_eq (p:=131) (by decide) (by decide), q_eq (p:=137) (by decide) (by decide),
      q_eq (p:=23) (by decide) (by decide), q_eq (p:=29) (by decide) (by decide),
      q_eq (p:=31) (by decide) (by decide)]
    decide
  by_cases h47 : h ≤ 47
  · exact ⟨7, row_triple (a:=32) (v:=9) (t:=225) (by omega) h47 (by decide) (by decide)
      (by decide) (by decide) (by decide), by omega⟩
  by_cases h63 : h ≤ 63
  · exact ⟨7, row_triple (a:=48) (v:=10) (t:=330) (by omega) h63 (by decide) (by decide)
      (by decide) (by decide) (by decide), by omega⟩
  by_cases h127 : h ≤ 127
  · exact ⟨8, row_triple (a:=64) (v:=11) (t:=715) (by omega) h127 (by decide) (by decide)
      (by decide) (by decide) (by decide), by omega⟩
  exact ⟨_, dyadic_triple (Nat.log_mono_right (b:=2) (show 128 ≤ h by omega))
    (Nat.pow_log_le_self _ (by omega)) (Nat.lt_pow_succ_log_self (by decide) h)⟩


noncomputable def value {k : ℕ} (e : Fin k → ℕ) : ℕ := ∏ i : Fin k, q i ^ e i
def tau {k : ℕ} (e : Fin k → ℕ) : ℕ := ∏ i, (e i + 1)

theorem q_pos (i : ℕ) : 0 < q i := (Nat.prime_nth_prime i).pos
theorem value_pos {k} (e : Fin k → ℕ) : 0 < value e :=
  prod_pos fun (i : Fin k) _ => pow_pos (q_pos i) _

theorem valuation {k} (e : Fin k → ℕ) (p : ℕ) :
    (value e).factorization p = ∑ i : Fin k, if q i = p then e i else 0 := by
  rw [value, Nat.factorization_prod_apply (fun (i : Fin k) _ => pow_ne_zero _ (q_pos i).ne')]
  simp_rw [Nat.Prime.factorization_pow (Nat.prime_nth_prime _), Finsupp.single_apply]

theorem valuation_at {k} (e : Fin k → ℕ) (i : Fin k) : (value e).factorization (q i) = e i := by
  simp [valuation, q_strict.injective.eq_iff, Fin.val_inj]

theorem value_support {k} (e : Fin k → ℕ) :
    (value e).primeFactors = (univ.filter fun i => e i ≠ 0).image (fun i : Fin k => q i) := by
  ext p
  rw [← Nat.support_factorization, Finsupp.mem_support_iff, valuation]
  by_cases hex : ∃ i : Fin k, q i = p
  · obtain ⟨i,rfl⟩ := hex
    simp [q_strict.injective.eq_iff, Fin.val_inj]
  · simp [fun (i : Fin k) => show q i ≠ p from fun h => hex ⟨i,h⟩]

theorem value_card {k} (e : Fin k → ℕ) : (value e).divisors.card = tau e := by
  rw [Nat.card_divisors (value_pos e).ne', value_support, prod_image]
  · simp_rw [valuation_at]
    simp [tau, prod_filter]
    exact prod_congr rfl fun i _ => by split_ifs with hi <;> simp_all
  · exact (q_strict.injective.comp Fin.val_injective).injOn

theorem value_omega {k} (e : Fin k → ℕ) (he : ∀ i, 0 < e i) :
    (value e).primeFactors.card = k := by
  rw [value_support, card_image_of_injective _ (show Function.Injective (fun i : Fin k => q i) from q_strict.injective.comp Fin.val_injective)]
  simp [fun i => (he i).ne']

theorem compress (n : ℕ) (hn : 0 < n) :
    ∃ e : Fin n.primeFactors.card → ℕ, (∀ i, 0 < e i) ∧
      tau e = n.divisors.card ∧ value e ≤ n := by
  classical
  let r := n.primeFactors.orderEmbOfFin rfl
  let e := fun i => n.factorization (r i)
  have hr (i) : r i ∈ n.primeFactors := orderEmbOfFin_mem _ _ _
  have hp (i) := Nat.prime_of_mem_primeFactors (hr i)
  have he (i) : 0 < e i := by
    apply Nat.pos_of_ne_zero
    exact Finsupp.mem_support_iff.mp (show r i ∈ n.factorization.support from hr i)
  have hq (i : Fin n.primeFactors.card) : q i ≤ r i := by
    have hin : StrictMono (fun j => Nat.count Nat.Prime (r j)) := fun a b hab =>
      Nat.count_strict_mono (hp a) (r.strictMono hab)
    have hle : ∀ j : Fin n.primeFactors.card, j.val ≤ Nat.count Nat.Prime (r j) := by
      rintro ⟨m,hm⟩
      induction m with
      | zero => exact Nat.zero_le _
      | succ m ih => exact Nat.succ_le_of_lt ((ih (by omega)).trans_lt (hin (show (⟨m,by omega⟩ : Fin n.primeFactors.card) < ⟨m+1,hm⟩ from Nat.lt_succ_self _)))
    simpa [q, Nat.nth_count (hp i)] using q_strict.monotone (hle i)
  have hprod (f : ℕ → ℕ) : (∏ i, f (r i)) = ∏ p ∈ n.primeFactors, f p := by
    simpa [r] using (prod_image (s:=univ) (g:=r) (f:=f) r.injective.injOn).symm
  refine ⟨e, he, (hprod _).trans (Nat.card_divisors hn.ne').symm, ?_⟩
  calc
    value e ≤ ∏ i, r i ^ e i := prod_le_prod' fun i _ => Nat.pow_le_pow_left (hq i) _
    _ = n := (hprod (fun p => p^n.factorization p)).trans (Nat.prod_primeFactors_pow_factorization hn.ne').symm

theorem prod_pair {k} (f : Fin k → ℕ) (i j : Fin k) (hij : i ≠ j) :
    (∏ x, f x) = f i * f j * ∏ x ∈ (univ.erase i).erase j, f x := by
  rw [mul_assoc, mul_prod_erase _ _ (by simp [hij.symm]), mul_prod_erase _ _ (mem_univ i)]

theorem swapped_lt {k} (e : Fin k → ℕ) (i j : Fin k) (hij : i < j) (hinv : e i < e j) :
    value (e ∘ Equiv.swap i j) < value e := by
  have hd := Nat.sub_pos_of_lt hinv
  have hq := q_strict (show (i:ℕ) < j from hij)
  have hpow := Nat.pow_lt_pow_left hq (n:=e j-e i) hd.ne'
  have heq : e j = e i + (e j-e i) := by omega
  have hlocal : q i ^ e j * q j ^ e i < q i ^ e i * q j ^ e j := by
    nth_rw 1 2 [heq]
    repeat rw [pow_add]
    have ha := pow_pos (q_pos i) (e i)
    have hb := pow_pos (q_pos j) (e i)
    nlinarith [Nat.mul_lt_mul_of_pos_left hpow (Nat.mul_pos ha hb)]
  rw [value, value, prod_pair _ i j hij.ne, prod_pair (fun x => q x ^ e x) i j hij.ne]
  simp only [Function.comp_apply, Equiv.swap_apply_left, Equiv.swap_apply_right]
  apply lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right hlocal (prod_pos fun (x : Fin k) _ => pow_pos (q_pos x) _))
  apply Nat.mul_le_mul_left
  apply le_of_eq
  apply prod_congr rfl
  intro x hx
  simp only [mem_erase] at hx
  rw [Equiv.swap_apply_of_ne_of_ne hx.2.1 hx.1]

theorem canonical (n : ℕ) (hn : 0 < n) :
    ∃ e : Fin n.primeFactors.card → ℕ, (∀ i, 0 < e i) ∧ Antitone e ∧
      tau e = n.divisors.card ∧ value e ≤ n := by
  classical
  let P := fun y => ∃ e : Fin n.primeFactors.card → ℕ, (∀ i, 0 < e i) ∧
    tau e = n.divisors.card ∧ value e = y
  obtain ⟨b,hb,hd,hv⟩ := compress n hn
  have hex : ∃ y, P y := ⟨_,b,hb,hd,rfl⟩
  obtain ⟨e,he,hd',hv'⟩ := Nat.find_spec hex
  refine ⟨e,he,?_,hd',hv'.le.trans ((Nat.find_min' hex ⟨b,hb,hd,rfl⟩).trans hv)⟩
  intro i j hij
  by_contra! hinv
  have hlt := swapped_lt e i j (lt_of_le_of_ne hij (fun h => by subst j; simp at hinv)) hinv
  have h := Nat.find_min' hex (m:=value (e ∘ Equiv.swap i j)) ⟨_, fun x => he _, ?_, rfl⟩
  · omega
  · exact ((Equiv.swap i j).bijective.prod_comp (fun x => e x+1)).trans hd'


def rest {k} (e : Fin k → ℕ) (i : Fin k) := ∏ x ∈ univ.erase i, (e x+1)
noncomputable def core {k} (e : Fin k → ℕ) (i : Fin k) :=
  ∏ x ∈ univ.erase i, q x ^ e x

theorem rest_lb {k} {e : Fin k → ℕ} (he : ∀ i, 0 < e i) (i : Fin k) :
    2^(k-1) ≤ rest e i := by
  unfold rest
  simpa using (prod_le_prod' (s:=univ.erase i) (f:=fun _ => 2) (g:=fun x => e x+1)
    (fun x _ => by have := he x; omega))

theorem tau_lb {k} {e : Fin k → ℕ} (he : ∀ i, 0 < e i) : 2^k ≤ tau e := by
  simpa [tau] using (prod_le_prod' (s:=univ) (f:=fun _ => 2) (g:=fun x => e x+1)
    (fun x _ => by have := he x; omega))

theorem prod_change {k} (f : Fin k → ℕ → ℕ) (e : Fin k → ℕ) (i : Fin k) (x : ℕ) :
    (∏ t, f t (Function.update e i x t)) = f i x * ∏ t ∈ univ.erase i, f t (e t) := by
  rw [← mul_prod_erase univ (fun t => f t (Function.update e i x t)) (mem_univ i)]
  simp only [Function.update_self]
  congr 1
  exact prod_congr rfl fun t ht => by rw [Function.update_of_ne (mem_erase.mp ht).1]

theorem value_change {k} (e : Fin k → ℕ) (i : Fin k) (x) :
    value (Function.update e i x) = q i ^ x * core e i := prod_change (fun t a => q t ^ a) e i x
theorem tau_change {k} (e : Fin k → ℕ) (i : Fin k) (x) :
    tau (Function.update e i x) = (x+1) * rest e i := prod_change (fun _ a => a+1) e i x
theorem value_head {k} (e : Fin k → ℕ) (i : Fin k) :
    value e = q i ^ e i * core e i := (mul_prod_erase _ _ (mem_univ i)).symm
theorem tau_head {k} (e : Fin k → ℕ) (i : Fin k) :
    tau e = (e i+1) * rest e i := (mul_prod_erase _ _ (mem_univ i)).symm
theorem core_pos {k} (e : Fin k → ℕ) (i : Fin k) : 0 < core e i :=
  prod_pos fun (x : Fin k) _ => pow_pos (q_pos x) _
theorem rest_pos {k} (e : Fin k → ℕ) (i : Fin k) : 0 < rest e i :=
  prod_pos fun _ _ => Nat.succ_pos _

def extend {k} (e : Fin k → ℕ) (x : ℕ) : Fin (k+1) → ℕ := Fin.lastCases x e
theorem value_extend {k} (e : Fin k → ℕ) (x) :
    value (extend e x) = value e * q k ^ x := by simp [value, Fin.prod_univ_castSucc, extend]
theorem tau_extend {k} (e : Fin k → ℕ) (x) :
    tau (extend e x) = tau e * (x+1) := by simp [tau, Fin.prod_univ_castSucc, extend]

def Budget {k} (e : Fin k → ℕ) (g : ℕ) := ∀ {h} (f : Fin h → ℕ),
  value f < value e → tau f < tau e + g

noncomputable def cutoff (h i : ℕ) := Nat.log (q i) (q h) + 1
theorem single_swap {k} {e : Fin k → ℕ} {g} (hb : Budget e g) (i : Fin k)
    (hc : cutoff k i ≤ e i) :
    2*(e i - cutoff k i+1)*rest e i < (e i+1)*rest e i+g := by
  let c := cutoff k i
  obtain ⟨d,hd⟩ := Nat.exists_eq_add_of_le hc
  have hq : q k < q i ^ c := Nat.lt_pow_succ_log_self (Nat.prime_nth_prime i).one_lt _
  have h := hb (extend (Function.update e i d) 1)
  rw [value_extend, value_change, pow_one, value_head e i, hd, pow_add] at h
  have hlt : q i ^ d * core e i * q k < q i ^ cutoff k i * q i ^ d * core e i := by
    rw [mul_assoc (q i ^ cutoff k i), mul_comm (q i ^ cutoff k i)]
    exact Nat.mul_lt_mul_of_pos_left hq (Nat.mul_pos (pow_pos (q_pos i) _) (core_pos e i))
  specialize h hlt
  rw [tau_extend, tau_change, tau_head e i, hd] at h
  rw [hd, Nat.add_sub_cancel_left]
  simpa only [mul_comm 2, mul_assoc, Nat.reduceAdd] using h

theorem a_upper {k} {e : Fin k → ℕ} (hb : Budget e 0) (i : Fin k) :
    e i ≤ 2*cutoff k i-2 := by
  have hc : 1 ≤ cutoff k i := Nat.le_add_left _ _
  by_contra! hn
  have h := single_swap hb i (by omega)
  have hp := rest_pos e i
  have hle : e i+1 ≤ 2*(e i-cutoff k i+1) := by omega
  have := Nat.mul_le_mul_right (rest e i) hle
  omega

theorem b_sharp {k} {e : Fin k → ℕ} {g} (hg : 0 < g) (hb : Budget e g)
    (he : ∀ i, 0 < e i) (i : Fin k) :
    e i ≤ 2*cutoff k i-1 + (g-1)/2^(k-1) := by
  have hc : 1 ≤ cutoff k i := Nat.le_add_left _ _
  by_cases h : e i < 2*cutoff k i
  · exact le_trans (by omega : e i ≤ 2*cutoff k i-1) (Nat.le_add_right _ _)
  have hh := single_swap hb i (by omega)
  let t := e i+1-2*cutoff k i
  have h1 : t+(e i+1) = 2*(e i-cutoff k i+1) := by dsimp [t]; omega
  rw [← h1, add_mul] at hh
  have h2 : t*2^(k-1) ≤ g-1 := by
    have := Nat.mul_le_mul_left t (rest_lb he i)
    omega
  have := (Nat.le_div_iff_mul_le (by positivity)).mpr h2
  dsimp [t] at this
  omega

theorem b_coarse {k} {e : Fin k → ℕ} {g} (hg : 2*g ≤ tau e) (hb : Budget e g)
    (i : Fin k) : e i ≤ 4*cutoff k i-2 := by
  have hc : 1 ≤ cutoff k i := Nat.le_add_left _ _
  by_contra! hn
  have h := single_swap hb i (by omega)
  have hle : 3*(e i+1) ≤ 4*(e i-cutoff k i+1) := by omega
  rw [tau_head e i] at hg
  nlinarith [Nat.mul_le_mul_right (rest e i) hle]

noncomputable def lowerExp (k i : ℕ) : ℕ := max 1 (Nat.log (q i) (q (k-1)-1))


def decAt {k} (e : Fin k → ℕ) (i : Fin k) := Function.update e i (e i-1)
theorem value_dec {k} (e : Fin k → ℕ) (i : Fin k) (he : 1 ≤ e i) :
    value (decAt e i)*q i = value e := by
  rw [decAt, value_change, value_head e i, mul_right_comm, ← pow_succ,
    Nat.sub_add_cancel he]
theorem tau_dec {k} (e : Fin k → ℕ) (i : Fin k) (he : 1 ≤ e i) :
    tau (decAt e i) = e i * rest e i := by
  rw [decAt, tau_change, Nat.sub_add_cancel he]
theorem dec_cost {k} (e : Fin k → ℕ) (i : Fin k) (he : 2 ≤ e i) :
    2*tau e ≤ 3*tau (decAt e i) := by
  rw [tau_dec e i (by omega),tau_head e i]
  nlinarith [Nat.mul_le_mul_right (rest e i) he]

theorem a_lower {k} {e : Fin k → ℕ} (he : ∀ i, 0 < e i) (hb : Budget e 0) (i : Fin k) :
    lowerExp k i ≤ e i := by
  refine max_le (he i) ?_
  let j : Fin k := ⟨k-1, by have := i.isLt; omega⟩
  change Nat.log (q i) (q j-1) ≤ e i
  have hq := (Nat.prime_nth_prime j).one_lt
  change 1 < q j at hq
  by_cases hij : i = j
  · rw [hij,Nat.log_of_lt (by omega)]; omega
  by_contra! hn
  have hp := Nat.pow_le_of_le_log (by omega : q j-1 ≠ 0) (Nat.succ_le_of_lt hn)
  let f := decAt e j
  have hf : f i = e i := Function.update_of_ne hij _ _
  let y := Function.update f i (2*e i+1)
  have hv : value y = value f * q i^(e i+1) := by
    rw [value_change, value_head f i, hf, show 2*e i+1=e i+(e i+1) by omega,pow_add]
    ac_rfl
  have hd : tau y = 2*tau f := by
    rw [tau_change, tau_head f i,hf]; ring
  have hl : value y < value e := by
    rw [hv, ← value_dec e j (he j)]
    apply Nat.mul_lt_mul_of_pos_left _ (value_pos f)
    exact Nat.lt_of_le_of_lt hp (by omega)
  have hh := hb y hl
  rw [hd, tau_dec e j (he j), tau_head e j] at hh
  have := he j
  nlinarith [Nat.mul_le_mul_right (rest e j) this]

theorem triple_ones {k s g} {e : Fin k → ℕ} (he : ∀ i, 0 < e i) (hm : Antitone e)
    (hb : Budget e g) (ht : Triple k s) (hg : 27*g ≤ 5*tau e) (i : Fin k)
    (hi : k-s ≤ i.val) : e i = 1 := by
  obtain ⟨hs,ht⟩ := ht
  let a : Fin k := ⟨k-s-2,by omega⟩
  let b : Fin k := ⟨k-s-1,by omega⟩
  let c : Fin k := ⟨k-s,by have := i.isLt; omega⟩
  have hab : a < b := by change k-s-2 < k-s-1; omega
  have hbc : b < c := by change k-s-1 < k-s; omega
  have hci : c ≤ i := hi
  by_contra! hn
  have h1 := he i
  have ha : 2 ≤ e a := le_trans (by omega : 2 ≤ e i) (hm (hab.le.trans (hbc.le.trans hci)))
  have hbe : 2 ≤ e b := le_trans (by omega : 2 ≤ e i) (hm (hbc.le.trans hci))
  have hce : 2 ≤ e c := le_trans (by omega : 2 ≤ e i) (hm hci)
  let f := decAt e a
  let f' := decAt f b
  let f'' := decAt f' c
  have hb' : 2 ≤ f b := by simpa [f,decAt,hab.ne'] using hbe
  have hc' : 2 ≤ f' c := by simpa [f',f,decAt,hbc.ne', (hab.trans hbc).ne'] using hce
  have h1 := value_dec e a (by omega)
  have h2 := value_dec f b (by omega)
  have h3 := value_dec f' c (by omega)
  change value f * _ = _ at h1
  change value f' * _ = _ at h2
  change value f'' * _ = _ at h3
  have hx : value e = value f'' * (q a * q b * q c) := by
    rw [← h1, ← h2, ← h3]; ring
  let y := extend (extend f'' 1) 1
  have hy : value y < value e := by
    rw [hx]; simp only [y,value_extend,pow_one,mul_assoc]
    apply Nat.mul_lt_mul_of_pos_left _ (value_pos f'')
    simpa only [mul_assoc] using ht
  have h4 := dec_cost e a ha
  have h5 := dec_cost f b hb'
  have h6 := dec_cost f' c hc'
  have hh := hb y hy
  simp only [y,tau_extend] at hh
  change 2*tau e ≤ 3*tau f at h4
  change 2*tau f ≤ 3*tau f' at h5
  change 2*tau f' ≤ 3*tau f'' at h6
  omega

theorem suffix_dvd {k s} {e : Fin k → ℕ} (hs : s ≤ k)
    (h : ∀ i : Fin k, k-s ≤ i.val → e i = 1) : 2^s ∣ tau e := by
  let b : Fin k → ℕ := fun i => if k-s ≤ i.val then 2 else 1
  have hb : (∏ i, b i) ∣ tau e := prod_dvd_prod_of_dvd _ _ fun i _ => by
    dsimp [b]; split_ifs with hi
    · simp [h i hi]
    · simp
  have hc : (∏ i, b i) = 2^s := by
    simp only [b, ← Finset.prod_filter]
    rw [prod_const]
    congr 1
    have hset : (univ.filter fun i : Fin k => k-s ≤ i.val) =
        univ \ (univ.filter fun i : Fin k => i.val < k-s) := by ext x; simp
    rw [hset,card_sdiff_of_subset (subset_univ _)]
    have heq : (univ.filter fun i : Fin k => i.val < k-s) =
        univ.image (fun i : Fin (k-s) => (⟨i.val,by omega⟩ : Fin k)) := by
      ext x
      simp only [mem_filter,mem_univ,true_and,mem_image]
      constructor
      · exact fun hx => ⟨⟨x.val,hx⟩,rfl⟩
      · rintro ⟨i,rfl⟩
        exact i.isLt
    rw [heq, card_image_of_injective _ (by intro a b hab; exact Fin.ext (congrArg (fun x : Fin k => x.val) hab))]
    simp; omega
  rwa [hc] at hb

theorem gap_impossible {a b g s t : ℕ} (ha : 2^s ∣ a) (hb : 2^t ∣ b) (hlt : b<a)
    (hg : a ≤ b+g) (hs : g<2^s) (ht : g<2^t) : False := by
  have hma := (pow_dvd_pow 2 (min_le_left s t)).trans ha
  have hmb := (pow_dvd_pow 2 (min_le_right s t)).trans hb
  have := Nat.le_of_dvd (Nat.sub_pos_of_lt hlt) (Nat.dvd_sub hma hmb)
  rcases le_total s t with h|h
  · rw [min_eq_left h] at this; omega
  · rw [min_eq_right h] at this; omega


structure Bad {k j : ℕ} (a : Fin k → ℕ) (b : Fin j → ℕ) : Prop where
  apos : ∀ i, 0 < a i
  bpos : ∀ i, 0 < b i
  amono : Antitone a
  bmono : Antitone b
  recA : Budget a 0
  sizes : value b < value a
  big : 7 ≤ value a
  gap : tau a + j ≤ tau b + k

namespace Bad
variable {k j : ℕ} {a : Fin k → ℕ} {b : Fin j → ℕ} (H : Bad a b)
include H
theorem dlt : tau b < tau a := by simpa using H.recA b H.sizes
theorem dim : j < k := by have := H.dlt; have := H.gap; omega
theorem recB : Budget b (k-j) := by
  intro h f hf
  have := H.recA f (hf.trans H.sizes)
  have := H.gap
  omega

theorem jpos : 0 < j := by
  by_contra! hn
  obtain rfl : j=0 := by omega
  have hd : tau b = 1 := by simp [tau]
  have hh := tau_lb H.apos
  have hg := H.gap
  have hk : k ≤ 1 := by
    by_contra! hk
    have hh' : ∀ n ≥ 2, n+1 < 2^n := by
      intro n h
      induction n,h using Nat.le_induction with
      | base => decide
      | succ n _ h => rw [pow_succ]; omega
    have := hh' k hk
    omega
  have hd' := H.dim
  obtain rfl : k = 1 := by omega
  have hb := a_upper H.recA (0 : Fin 1)
  have hcut : cutoff 1 0 = 2 := by simp [cutoff,q]; decide
  have hv := H.big
  simp [value,q] at hv
  change a 0 ≤ 2*cutoff 1 0-2 at hb
  rw [hcut] at hb
  have := Nat.pow_le_pow_right (n:=2) (by decide) hb
  norm_num at this
  omega

theorem gain2 : 2*(k-j) ≤ tau b := by
  have hj := H.jpos
  have hk := H.dim
  have h : ∀ n ≥ 2, 3*(n-1) ≤ 2^n := by
    intro n hn
    induction n,hn using Nat.le_induction with
    | base => decide
    | succ n hn ih => rw [pow_succ]; omega
  have := h k (by omega)
  have := H.gap
  have := tau_lb H.apos
  omega

theorem gain27 (hk : 5 ≤ k) : 27*(k-j) ≤ 5*tau b := by
  have hj := H.jpos
  have h : ∀ n ≥ 5, 32*(n-1) ≤ 5*2^n := by
    intro n hn
    induction n,hn using Nat.le_induction with
    | base => decide
    | succ n hn ih => rw [pow_succ]; omega
  have := h k hk
  have := H.gap
  have := tau_lb H.apos
  omega
end Bad

theorem q_exp (j : ℕ) : q j ≤ 2^(j+1) := by
  induction j with
  | zero => simp [q]
  | succ j ih =>
    obtain ⟨p,hp,hl,hu⟩ := Nat.bertrand (q j) (q_pos _).ne'
    have h := Nat.count_strict_mono (Nat.prime_nth_prime j) hl
    rw [Nat.count_nth_of_infinite Nat.infinite_setOfPred_prime] at h
    have h' := q_strict.monotone (Nat.succ_le_of_lt h)
    change q (j+1) ≤ Nat.nth Nat.Prime (Nat.count Nat.Prime p) at h'
    rw [Nat.nth_count hp] at h'
    rw [pow_succ]
    omega

theorem cutoff_le (j i : ℕ) : cutoff j i ≤ j+2 := by
  have h := q_exp j
  have h2 := Nat.add_two_le_nth_prime i
  change i+2 ≤ q i at h2
  have hp := Nat.pow_log_le_self (q i) (q_pos j).ne'
  have := (Nat.pow_le_pow_left (by omega : 2 ≤ q i) (Nat.log (q i) (q j))).trans
    (hp.trans h)
  have := (pow_le_pow_iff_right₀ (by decide : 1 < (2:ℕ))).mp this
  dsimp [cutoff]; omega

theorem dim_aux {j : ℕ} (hj : 8 ≤ j) : j*j ≤ 2^(j-1) ∧ 4*(j+2) ≤ 2^(j-1) := by
  induction j,hj using Nat.le_induction with
  | base => decide
  | succ j hj ih =>
    obtain ⟨ha,hb⟩ := ih
    rw [show j.succ-1 = j-1+1 by omega, pow_succ]
    refine ⟨?_,by omega⟩
    nlinarith [Nat.mul_le_mul_right j hj]

noncomputable def primorial (k : ℕ) := value (fun _ : Fin k => 1)
theorem prim_step (k : ℕ) : primorial (k+1) = primorial k * q k := by
  simp [primorial,value,Fin.prod_univ_castSucc]
theorem prim_pos (k : ℕ) : 0 < primorial k := value_pos _
theorem prim_mono : Monotone primorial := monotone_nat_of_le_succ fun n => by
  rw [prim_step]; exact Nat.le_mul_of_pos_right _ (q_pos _)
theorem prim_lb (j r : ℕ) : primorial j * q j ^ r ≤ primorial (j+r) := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [← Nat.add_assoc,prim_step,pow_succ,← mul_assoc]
    exact Nat.mul_le_mul ih (q_strict.monotone (Nat.le_add_right _ _))

theorem dim_large {k j} {a : Fin k → ℕ} {b : Fin j → ℕ} (H : Bad a b) (hj : 8 ≤ j) :
    k ≤ 3*j := by
  obtain ⟨h1,h2⟩ := dim_aux hj
  have hco i := b_coarse H.gain2 H.recB i
  have hb : tau b ≤ (2^(j-1))^j := by
    unfold tau
    trans ∏ _i : Fin j, 2^(j-1)
    swap
    · simp
    apply prod_le_prod'
    intro i _
    have := hco i
    have := cutoff_le j i
    omega
  have hkl := tau_lb H.apos
  have hg := H.gap
  have hd := H.dim
  have hl : 2^(k-1) ≤ tau b := by
    have hrec : 2^k = 2^(k-1)*2 := by rw [←pow_succ]; congr 1; omega
    have hlin : k ≤ 2^(k-1) := by have := (Nat.lt_two_pow_self : k-1 < 2^(k-1)); omega
    omega
  rw [←pow_mul] at hb
  have hs := (pow_le_pow_iff_right₀ (by decide : 1 < (2:ℕ))).mp (hl.trans hb)
  have hk2 : k ≤ j*j := by
    have he : j-1+1=j := by omega
    have := congrArg (fun x => x*j) he
    simp only [add_mul,one_mul] at this
    omega
  have hgap : k-j ≤ 2^(j-1) := by omega
  have hcut (i : Fin j) : b i ≤ 2*cutoff j i-1 := by
    have := b_sharp (by omega) H.recB H.bpos i
    rwa [Nat.div_eq_of_lt (by omega), add_zero] at this
  have hdouble : value a ≤ 2*value b := by
    let i : Fin j := ⟨0,by omega⟩
    let f := Function.update b i (b i+1)
    have hv : value f = 2*value b := by
      rw [value_change,value_head b i,pow_succ]; simp [i,q]; ring
    by_contra! hn
    have hh := H.recA f (hv.trans_lt hn)
    rw [tau_change] at hh
    have hrr := rest_lb H.bpos i
    rw [tau_head b i] at hg
    nlinarith
  have hm : value b ≤ primorial j * q j ^ (2*j) := by
    have hlocal (i : Fin j) : q i ^ b i ≤ q i * q j ^ 2 := by
      have h := hcut i
      have hpow := Nat.pow_log_le_self (q i) (q_pos j).ne'
      have hh : b i ≤ Nat.log (q i) (q j)*2+1 := by dsimp [cutoff] at h; omega
      refine (Nat.pow_le_pow_right (q_pos i) hh).trans ?_
      rw [pow_succ,pow_mul,mul_comm]
      exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hpow 2)
    have ht := prod_le_prod' (s:=univ) (fun i _ => hlocal i)
    simpa [value,primorial,prod_mul_distrib,pow_mul] using ht
  by_contra! hn
  have hsize : primorial k ≤ value a := by
    unfold primorial value
    exact prod_le_prod' fun i _ => Nat.pow_le_pow_right (q_pos i) (H.apos i)
  have hcmp := prim_mono (show j+2*j+1 ≤ k by omega)
  rw [prim_step] at hcmp
  have hpp := prim_lb j (2*j)
  have hp := Nat.add_two_le_nth_prime (j+2*j)
  change j+2*j+2 ≤ q (j+2*j) at hp
  have ht := Nat.mul_le_mul_right (q (j+2*j)) hpp
  have hppos := Nat.mul_pos (prim_pos j) (pow_pos (q_pos j) (2*j))
  nlinarith [Nat.mul_lt_mul_of_pos_left (by omega : 2 < q (j+2*j)) hppos]

theorem no_large {k j} {a : Fin k → ℕ} {b : Fin j → ℕ} (H : Bad a b) (hj : 11 ≤ j) : False := by
  have hd := H.dim
  have hk := dim_large H (by omega)
  obtain ⟨s,hta,hs⟩ := many_ones_test k (by omega)
  obtain ⟨t,htb,ht⟩ := many_ones_test j hj
  have ha := suffix_dvd (by have := hta.1; omega : s ≤ k)
    (triple_ones H.apos H.amono H.recA hta (by simp))
  have hb := suffix_dvd (by have := htb.1; omega : t ≤ j)
    (triple_ones H.bpos H.bmono H.recB htb (H.gain27 (by omega)))
  exact gap_impossible (g:=k-j) ha hb H.dlt (by have := H.gap; omega) (by omega) (by omega)


open A059992Certificate (onesCount cutoffs lowerWitness witnesses programs)

def primeAt (i : ℕ) : ℕ := A059992Certificate.primes[i]?.getD 0
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem primeAt_eq {i : ℕ} (hi : i < 33) : q i = primeAt i := by
  have ht : ∀ t : Fin 33, (primeAt t).Prime ∧ Nat.count Nat.Prime (primeAt t) = t.val := by decide
  exact q_eq (ht ⟨i,hi⟩).1 (ht ⟨i,hi⟩).2

def cut (h i : ℕ) := Nat.log (primeAt i) (primeAt h)+1
theorem cut_eq {h i} (hh : h < 33) (hi : i < 33) : cutoff h i = cut h i := by
  rw [cutoff,cut,primeAt_eq hh,primeAt_eq hi]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem coarse_small {j : ℕ} (hj : 0 < j) (hj' : j ≤ 7) :
    (∏ i : Fin j, (4*cut j i-1)) + (2*j+1) < 2^(3*j+1) := by
  have hs : ∀ t : Fin 8, t.val ≠ 0 →
      (∏ i : Fin t.val, (4*cut t i-1)) + (2*t.val+1) < 2^(3*t.val+1) := by decide
  exact hs ⟨j,by omega⟩ hj.ne'

theorem pow_diff {l k : ℕ} (hl : l ≤ k) : 2^l + k ≤ 2^k + l := by
  induction k,hl using Nat.le_induction with
  | base => rfl
  | succ k _ ih =>
    rw [pow_succ]
    have hp : 0 < 2^k := by positivity
    omega

theorem dim_small {k j} {a : Fin k → ℕ} {b : Fin j → ℕ} (H : Bad a b) (hj : j ≤ 7) :
    k ≤ 3*j := by
  by_contra! hn
  have h := coarse_small H.jpos hj
  have h1 : tau b ≤ ∏ i : Fin j, (4*cut j i-1) := by
    apply prod_le_prod'
    intro i _
    have hh := b_coarse H.gain2 H.recB i
    rw [cut_eq (by omega) (by have := i.isLt; omega)] at hh
    have hp : 1 ≤ cut j i := Nat.le_add_left _ _
    omega
  have := pow_diff hn
  have := H.gap
  have := tau_lb H.apos
  omega

theorem dims {k j} {a : Fin k → ℕ} {b : Fin j → ℕ} (H : Bad a b) :
    j ≤ 10 ∧ k ≤ 3*j := by
  have hj : j ≤ 10 := by by_contra! hn; exact no_large H hn
  exact ⟨hj, if h : j ≤ 7 then dim_small H h else dim_large H (by omega)⟩

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem ones_spec {h : ℕ} (hh : h ≤ 30) :
    onesCount h ≤ h ∧ (onesCount h ≠ 0 → 5 ≤ h ∧ Triple h (onesCount h)) := by
  have ht : ∀ x : Fin 31, let h := x.val; let s := onesCount h
    s ≤ h ∧ (s ≠ 0 → 5 ≤ h ∧ s+2 ≤ h ∧
      primeAt h * primeAt (h+1) < primeAt (h-s-2)*primeAt (h-s-1)*primeAt (h-s)) := by decide
  obtain ⟨hs,hp⟩ := ht ⟨h,by omega⟩
  refine ⟨hs,fun h0 => ?_⟩
  obtain ⟨h5,h2,hp⟩ := hp h0
  refine ⟨h5,h2,?_⟩
  simpa only [primeAt_eq (show h < 33 by omega),primeAt_eq (show h+1 < 33 by omega),
    primeAt_eq (show h-onesCount h-2 < 33 by omega),primeAt_eq (show h-onesCount h-1 < 33 by omega),
    primeAt_eq (show h-onesCount h < 33 by omega)] using hp

def low (k i : ℕ) := max 1 (Nat.log (primeAt i) (primeAt (k-1)-1))
def upA (k i : ℕ) := if k-onesCount k ≤ i then 1 else 2*cut k i-2
def upB (j z i : ℕ) := if j-onesCount j ≤ i then 1 else 2*cut j i-1 + (z-1)/2^(j-1)

namespace Bad
variable {k j : ℕ} {a : Fin k → ℕ} {b : Fin j → ℕ} (H : Bad a b)
include H
theorem suffixA (i : Fin k) (hi : k-onesCount k ≤ i.val) : a i = 1 := by
  obtain ⟨hj,hk⟩ := dims H
  have hh := ones_spec (by omega : k ≤ 30)
  have hn : onesCount k ≠ 0 := by have := i.isLt; omega
  exact triple_ones H.apos H.amono H.recA (hh.2 hn).2 (by simp) i hi
theorem suffixB (i : Fin j) (hi : j-onesCount j ≤ i.val) : b i = 1 := by
  obtain ⟨hj,hk⟩ := dims H
  have hh := ones_spec (by omega : j ≤ 30)
  have hn : onesCount j ≠ 0 := by have := i.isLt; omega
  obtain ⟨h5,ht⟩ := hh.2 hn
  exact triple_ones H.bpos H.bmono H.recB ht (H.gain27 (by have := H.dim; omega)) i hi

theorem lowA (i : Fin k) : low k i ≤ a i := by
  obtain ⟨hj,hk⟩ := dims H
  have h := a_lower H.apos H.recA i
  simpa only [lowerExp,low,primeAt_eq (show i.val < 33 by have := i.isLt; omega),
    primeAt_eq (show k-1 < 33 by omega)] using h

theorem highA (i : Fin k) : a i ≤ upA k i := by
  obtain ⟨hj,hk⟩ := dims H
  unfold upA; split_ifs with h
  · exact (H.suffixA i h).le
  simpa only [cut_eq (show k < 33 by omega) (show i.val < 33 by have := i.isLt; omega)]
    using a_upper H.recA i
theorem highB (i : Fin j) : b i ≤ upB j (k-j) i := by
  obtain ⟨hj,hk⟩ := dims H
  unfold upB; split_ifs with h
  · exact (H.suffixB i h).le
  simpa only [cut_eq (show j < 33 by omega) (show i.val < 33 by have := i.isLt; omega)]
    using b_sharp (by have := H.dim; omega) H.recB H.bpos i

theorem record_le {h} (f : Fin h → ℕ) (hf : value f ≤ value a) : tau f ≤ tau a := by
  rcases hf.eq_or_lt with he|hl
  · rw [← value_card, ← value_card,he]
  · have := H.recA f hl; omega

theorem keeps_gap : 2^(min (onesCount j) (onesCount k)) ≤ k-j := by
  obtain ⟨hj,hk⟩ := dims H
  have ha := suffix_dvd (ones_spec (by omega : k ≤ 30)).1 H.suffixA
  have hb := suffix_dvd (ones_spec (by omega : j ≤ 30)).1 H.suffixB
  have hg := H.gap
  have hlt := H.dlt
  by_contra! hh
  exact gap_impossible (g:=k-j) ha hb hlt (by omega)
    (hh.trans_le (Nat.pow_le_pow_right (by decide) (min_le_right _ _)))
    (hh.trans_le (Nat.pow_le_pow_right (by decide) (min_le_left _ _)))
end Bad


def sizeAt {k : ℕ} (start : ℕ) (e : Fin k → ℕ) := ∏ i : Fin k, primeAt (start+i.val) ^ e i
theorem size_eq {k : ℕ} (hk : k ≤ 33) (e : Fin k → ℕ) : value e = sizeAt 0 e := by
  apply prod_congr rfl
  intro i _
  simp only [zero_add,primeAt_eq (show i.val < 33 by have := i.isLt; omega)]

def expAt (w : List ℕ) (i : Fin w.length) := w[i.val]
def stats (w : List ℕ) : ℕ × ℕ := (sizeAt 0 (expAt w),tau (expAt w))
def boundWitness (j : ℕ) : List ℕ := lowerWitness[j-1]?.getD []

def cap (j k : ℕ) := tau (fun i : Fin j => upB j (k-j) i) + (k-j)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem cover_num : ∀ j : Fin 11, ∀ k : Fin 31, 0 < j.val → j.val < k.val → k.val ≤ 3*j.val →
    2^(min (onesCount j) (onesCount k)) ≤ k.val-j.val →
    2^k.val ≤ cap j k →
    ((stats (boundWitness j)).1 ≤ sizeAt 0 (fun i : Fin k.val => low k i) →
      (stats (boundWitness j)).2 ≤ cap j k) →
    [j.val,k.val] ∈ A059992Certificate.pairs := by decide

theorem covered {k j} {a : Fin k → ℕ} {b : Fin j → ℕ} (H : Bad a b) :
    [j,k] ∈ A059992Certificate.pairs := by
  obtain ⟨hj,hk⟩ := dims H
  have hd := H.gap
  have ht : tau b ≤ tau (fun i : Fin j => upB j (k-j) i) :=
    prod_le_prod' fun i _ => Nat.add_le_add_right (H.highB i) 1
  have hc : tau a ≤ cap j k := by unfold cap; omega
  apply cover_num ⟨j,by omega⟩ ⟨k,by omega⟩ H.jpos H.dim hk H.keeps_gap ((tau_lb H.apos).trans hc)
  let w := boundWitness j
  intro hw
  have hlen : w.length ≤ 33 := by
    have h : ∀ x : Fin 11, (boundWitness x).length ≤ 33 := by decide
    exact h ⟨j,by omega⟩
  have hs : value (expAt w) ≤ value a := by
    rw [size_eq hlen,size_eq (by omega : k ≤ 33)]
    exact hw.trans (prod_le_prod' fun i _ => Nat.pow_le_pow_right
      (by rw [zero_add,← primeAt_eq (show i.val < 33 by have := i.isLt; omega)]; exact q_pos _) (H.lowA i))
  exact (H.record_le _ hs).trans hc

-- Enumerate the ordered exponent vectors in a certified root box. Each entry
-- carries just the integer and its divisor count, which are all the leaf tests need.
def enumerate (lo hi : ℕ → ℕ) (start : ℕ) : ℕ → ℕ → List (ℕ × ℕ)
  | 0, _ => [(1,1)]
  | k+1, prev =>
    ((List.range (min (hi start) prev + 1)).filter (fun x => lo start ≤ x)).flatMap fun d =>
      (enumerate lo hi (start+1) k d).map fun (v,t) => (primeAt start ^ d * v, (d+1)*t)

theorem enum_mem {lo hi : ℕ → ℕ} {s k u : ℕ} (e : Fin k → ℕ) (hm : Antitone e)
    (hl : ∀ i : Fin k, lo (s+i) ≤ e i) (hh : ∀ i : Fin k, e i ≤ hi (s+i))
    (hu : ∀ i, e i ≤ u) : (sizeAt s e,tau e) ∈ enumerate lo hi s k u := by
  induction k generalizing s u with
  | zero => simp [sizeAt,tau,enumerate]
  | succ k ih =>
    let f : Fin k → ℕ := fun i => e i.succ
    have hrec : (sizeAt (s+1) f,tau f) ∈ enumerate lo hi (s+1) k (e 0) := by
      apply ih f (hm.comp_monotone (fun _ _ h => Nat.succ_le_succ h))
      · intro i; simpa [f, Fin.val_succ, Nat.add_left_comm, Nat.add_assoc, Nat.add_comm] using hl i.succ
      · intro i; simpa [f, Fin.val_succ, Nat.add_left_comm, Nat.add_assoc, Nat.add_comm] using hh i.succ
      · intro i; exact hm (Fin.zero_le _)
    rw [enumerate,List.mem_flatMap]
    refine ⟨e 0, ?_, List.mem_map.mpr ⟨_,hrec,?_⟩⟩
    · have h0 := hl 0
      have h1 := hh 0
      simp only [Fin.val_zero,add_zero] at h0 h1
      simp only [List.mem_filter,List.mem_range,decide_eq_true_eq]
      exact ⟨by have := hu 0; omega,h0⟩
    · simp [sizeAt,tau,Fin.prod_univ_succ,f,Fin.val_succ,Nat.add_left_comm,Nat.add_comm]

def admissible (ws : List (ℕ × ℕ)) (a : ℕ × ℕ) : Bool :=
  7 ≤ a.1 && ws.all fun w => w.1 ≥ a.1 || w.2 < a.2
def pairTest (j k : ℕ) : Bool :=
  let ws := witnesses.map stats
  let bs := enumerate (fun _ => 1) (upB j (k-j)) 0 j 200
  (enumerate (low k) (upA k) 0 k 200).all fun a =>
    !admissible ws a || bs.all fun b => !(b.1 < a.1 && b.2 < a.2 && a.2+j ≤ b.2+k)

theorem admissible_record {k j} {a : Fin k → ℕ} {b : Fin j → ℕ} (H : Bad a b) :
    admissible (witnesses.map stats) (value a,tau a) := by
  simp only [admissible, Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true,List.mem_map,
    Bool.or_eq_true, forall_exists_index,and_imp,forall_apply_eq_imp_iff₂]
  refine ⟨H.big,?_⟩
  intro w hw
  by_cases h : (stats w).1 ≥ value a
  · exact Or.inl h
  · right
    have hh : witnesses.all (fun w => w.length ≤ 33) := by decide
    have hl := List.all_eq_true.mp hh w hw
    have hv : value (expAt w) < value a := by rw [size_eq (by simpa using hl)]; exact Nat.lt_of_not_ge h
    simpa [stats] using H.recA (expAt w) hv

theorem pairTest_false {k j} {a : Fin k → ℕ} {b : Fin j → ℕ} (H : Bad a b) :
    pairTest j k = false := by
  obtain ⟨hj,hk⟩ := dims H
  have ha := enum_mem (s:=0) (u:=200) a H.amono (by simpa using H.lowA) (by simpa using H.highA)
    (fun i => by have := a_upper H.recA i; have := cutoff_le k i; omega)
  have hb := enum_mem (lo:=fun _ => 1) (s:=0) (u:=200) b H.bmono H.bpos (by simpa using H.highB)
    (fun i => by have := b_coarse H.gain2 H.recB i; have := cutoff_le j i; omega)
  rw [← size_eq (by omega)] at ha hb
  by_contra! hn
  have ht : pairTest j k = true := Bool.eq_true_of_not_eq_false hn
  obtain ht := List.all_eq_true.mp ht _ ha
  have had := admissible_record H
  simp only [had,Bool.not_true,Bool.false_or] at ht
  have hh := List.all_eq_true.mp ht _ hb
  simp [H.sizes,H.dlt,H.gap] at hh


def rootTest (prog : List (List ℕ)) : Bool :=
  match prog.head! with
  | [j,k] => pairTest j k
  | _ => false

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem root_checks : programs.all rootTest = true := by decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem impossible {k j} {a : Fin k → ℕ} {b : Fin j → ℕ} (H : Bad a b) : False := by
  have ht := A059992Certificate.finite_certificate
  simp only [Bool.and_eq_true, beq_iff_eq] at ht
  have hm := covered H
  rw [← ht.1.2] at hm
  obtain ⟨prog,hprog,heq⟩ := List.mem_map.mp hm
  have hv := List.all_eq_true.mp root_checks prog hprog
  change prog.head! = [j,k] at heq
  unfold rootTest at hv
  rw [heq] at hv
  change pairTest j k = true at hv
  rw [pairTest_false H] at hv
  exact Bool.noConfusion hv

def nonprimeCount (n : ℕ) := (n.divisors.filter fun d => ¬ d.Prime).card
theorem count_partition (n : ℕ) : n.primeFactors.card + nonprimeCount n = n.divisors.card := by
  rw [Nat.primeFactors_eq_to_filter_divisors_prime]
  exact Finset.card_filter_add_card_filter_not _

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem conclusion (n : ℕ) (hn : 1 ≤ n)
    (hr : ∀ y, 1 ≤ y → y < n → y.divisors.card < n.divisors.card)
    (h2 : n ≠ 2) (h6 : n ≠ 6) (m : ℕ) (hm : 1 ≤ m) (hlt : m<n) :
    nonprimeCount m < nonprimeCount n := by
  by_cases hsmall : n < 7
  · have ht : ∀ n m : Fin 7, 1 ≤ n.val → n.val ≠ 2 → n.val ≠ 6 → 1 ≤ m.val → m.val < n.val →
        (∀ y : Fin 7, 1 ≤ y.val → y.val < n.val → y.val.divisors.card < n.val.divisors.card) →
        nonprimeCount m < nonprimeCount n := by decide
    exact ht ⟨n,hsmall⟩ ⟨m,hlt.trans hsmall⟩ hn h2 h6 hm hlt (fun y => hr y)
  by_contra! hnp
  obtain ⟨a,ha,ham,hda,hva⟩ := canonical n hn
  obtain ⟨b,hb,hbm,hdb,hvb⟩ := canonical m hm
  have heq : value a = n := by
    apply hva.eq_of_not_lt
    intro hf
    have hh := hr _ (value_pos a) hf
    simp [value_card,hda] at hh
  apply impossible (a:=a) (b:=b)
  refine ⟨ha,hb,ham,hbm,?_,by omega,by omega,?_⟩
  · intro h f hf
    rw [heq] at hf
    simpa [value_card,hda] using hr _ (value_pos f) hf
  · have := count_partition n
    have := count_partition m
    omega

end A059992

theorem OMA.solution : type_of% @OMA.S_oeis_a059992.main := by
  intro n hn h2 h6 m hm hlt
  exact A059992.conclusion n hn.1 hn.2 h2 h6 m hm hlt
