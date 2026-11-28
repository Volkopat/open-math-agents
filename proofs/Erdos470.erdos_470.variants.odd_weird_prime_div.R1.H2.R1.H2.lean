import OMAReductions.R_Erdos470_erdos_470_variants_odd_weird_prime_div_R1_H2_R1

/-!
Proof of Erdos470.erdos_470.variants.odd_weird_prime_div.R1.H2.R1.H2 via
prime-factorization branching, dense cofactor interval/gap certificates
preserved under prime-power extensions, and explicit pseudoperfect survivor witnesses.
-/

namespace Erdos470H2Proof

open Finset ArithmeticFunction

inductive Par where | odd | even deriving DecidableEq

structure Entry where
  p : Nat
  minA : Nat
  exact : Bool
  par : Par
  deriving DecidableEq

structure Seed where
  fac : List (Nat × Nat)
  cutB : Nat
  p0 : Nat
  freeP : List Nat
  deriving DecidableEq

inductive Cert where
  | B
  | AL
  | NP (i : Nat)
  | AS (idx : Nat)
  | AC (qIdx seedIdx : Nat) (copIdxs : List Nat)
  | KR (qIdx seedIdx : Nat) (copIdxs : List Nat)
  | K5 (seedIdx : Nat) (copIdxs : List Nat) (sub : Cert)
  | KV (qIdx seedIdx : Nat) (copIdxs : List Nat) (sub : Cert)
  | K3 (seedIdx : Nat) (copIdxs : List Nat) (sub : Cert)
  | SF (idx : Nat) (cEx cHi : Cert)
  | S7 (p : Nat) (c0 c1 c2 c3 c4 : Cert)
  | SP (p : Nat) (c0 c1 c2 c3 : Cert)

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

def mergeNat : List Nat → List Nat → Nat → List Nat
  | [], ys, _ => ys
  | xs, [], _ => xs
  | _, _, 0 => []
  | x :: xs, y :: ys, fuel + 1 =>
    if x ≤ y then x :: mergeNat xs (y :: ys) fuel else y :: mergeNat (x :: xs) ys fuel

def mergePairs : List (List Nat) → List (List Nat)
  | [] => []
  | [x] => [x]
  | x :: y :: rest => mergeNat x y (x.length + y.length + 1) :: mergePairs rest

def mergeAll (fuel : Nat) (xss : List (List Nat)) : List Nat :=
  match fuel, xss with
  | _, [] => []
  | _, [x] => x
  | 0, x :: _ => x
  | fuel + 1, _ => mergeAll fuel (mergePairs xss)

def fastSort10 (xs : List Nat) : List Nat :=
  mergeAll 10 (xs.map fun x => [x])

def allDivsStep (acc : List Nat) (p k pe : Nat) : List Nat :=
  match k with
  | 0 => []
  | k + 1 => acc.map (· * pe) ++ allDivsStep acc p k (pe * p)

def allDivsOfFac (fac : List (Nat × Nat)) : List Nat :=
  fac.foldl (fun acc (p, e) => allDivsStep acc p (e + 1) 1) [1]

def mergeStep (a b curA curB : Nat) (acc : List (Nat × Nat)) : Nat × Nat × List (Nat × Nat) :=
  if a ≤ curB + 1 then (curA, max curB b, acc)
  else (a, b, (curA, curB) :: acc)

def mergeIvsLoop (iv1 iv2 : List (Nat × Nat)) (curA curB : Nat) (acc : List (Nat × Nat)) : Nat → List (Nat × Nat)
  | 0 => ((curA, curB) :: acc).reverse
  | fuel + 1 =>
    match iv1, iv2 with
    | [], [] => ((curA, curB) :: acc).reverse
    | (a, b) :: t1, [] =>
      let (ca, cb, acc') := mergeStep a b curA curB acc
      mergeIvsLoop t1 [] ca cb acc' fuel
    | [], (a, b) :: t2 =>
      let (ca, cb, acc') := mergeStep a b curA curB acc
      mergeIvsLoop [] t2 ca cb acc' fuel
    | (a1, b1) :: t1, (a2, b2) :: t2 =>
      if a1 ≤ a2 then
        let (ca, cb, acc') := mergeStep a1 b1 curA curB acc
        mergeIvsLoop t1 ((a2, b2) :: t2) ca cb acc' fuel
      else
        let (ca, cb, acc') := mergeStep a2 b2 curA curB acc
        mergeIvsLoop ((a1, b1) :: t1) t2 ca cb acc' fuel

def mergeIvs (iv1 iv2 : List (Nat × Nat)) : List (Nat × Nat) :=
  match iv1, iv2 with
  | [], l => l
  | l, [] => l
  | (a1, b1) :: t1, (a2, b2) :: t2 =>
    if a1 ≤ a2 then mergeIvsLoop t1 ((a2, b2) :: t2) a1 b1 [] (t1.length + t2.length + 2)
    else mergeIvsLoop ((a1, b1) :: t1) t2 a2 b2 [] (t1.length + t2.length + 2)

def has64Cov : List (Nat × Nat) → Nat → Bool
  | [], _ => false
  | (a, b) :: rest, hi => (a ≤ 64 && hi ≤ b) || has64Cov rest hi

def gap6OkAux (prevB : Nat) : List (Nat × Nat) → Bool
  | [] => true
  | (a, b) :: rest => a ≤ prevB + 6 && gap6OkAux b rest

def gap6Ok (lastEnd : Nat) : List (Nat × Nat) → Bool
  | [] => false
  | (0, b1) :: rest => gap6OkAux b1 rest && (match ((0, b1) :: rest).getLast? with | some (_, e) => e == lastEnd | none => false)
  | _ => false

def checkDenseTail (S : Nat) : List Nat → Bool
  | [] => true
  | d :: ds => d + 127 ≤ S && checkDenseTail (S + d) ds

def checkDenseLoop (B S : Nat) (ivs : List (Nat × Nat)) : List Nat → Bool
  | [] => false
  | d :: ds =>
    let shifted := ivs.map (fun (a, bb) => (a + d, bb + d))
    let ivs' := mergeIvs ivs shifted
    let S' := S + d
    if d == B then
      128 ≤ S' && B + 127 ≤ S' && has64Cov ivs' (S' - 64) && gap6Ok S' ivs' && checkDenseTail S' ds
    else if d > B then false
    else checkDenseLoop B S' ivs' ds

def addPowersCut (acc : List Nat) (p k pe cut : Nat) (out : List Nat) : List Nat :=
  match k with
  | 0 => out
  | k + 1 =>
    if pe > cut then out
    else
      let added := acc.filterMap (fun d => let v := d * pe; if v ≤ cut then some v else none)
      addPowersCut acc p k (pe * p) cut (out ++ added)

def allSmoothUpTo (primes : List Nat) (cut : Nat) : List Nat :=
  primes.foldl (fun acc p => addPowersCut acc p (cut + 1) 1 cut []) [1]

def check2a (pdivs : List Nat) (smooth : List Nat) (B r : Nat) : Bool :=
  smooth.all fun w =>
    let rz := r * w
    if rz ≤ B then true
    else
      let sLt := pdivs.foldl (fun acc x => if x < rz then acc + x else acc) 0
      rz + 127 ≤ sLt

def check2b (fac : List (Nat × Nat)) (b D r : Nat) : Bool :=
  let c0Fac := fac.filter (fun (p, _) => p != r)
  let c0Divs := allDivsOfFac c0Fac
  let rhs := c0Divs.foldl (fun acc t => if r < t then acc + (b / t) else acc) 0
  D + 127 ≤ r * rhs

def checkFacLoop (prev : Nat) : List (Nat × Nat) → Bool
  | [] => true
  | (p, e) :: rest => prev < p && isPrimeBool p && 1 ≤ e && checkFacLoop p rest

def checkSeedFull (sd : Seed) : Bool :=
  if sd.fac.isEmpty || sd.cutB == 0 || !checkFacLoop 2 sd.fac then false
  else
    let b : Nat := sd.fac.foldl (fun acc pe => acc * pe.1 ^ pe.2) 1
    let sig : Nat := sd.fac.foldl (fun acc pe => acc * sigPP pe.1 pe.2) 1
    if sig < b then false
    else
      let P := sig - b
      if P != sd.p0 || P < 2392 || b + 127 > 4 * P || 2 * b ≤ sig then false
      else
        let D := 2 * b - sig
        let raw := (allDivsOfFac sd.fac).filter (· < b)
        if raw.length > 1024 then false
        else
          let pdivs := fastSort10 raw
          if !checkDenseLoop sd.cutB 0 [(0, 0)] pdivs then false
          else if sd.freeP.isEmpty then true
          else
            let primes := sd.fac.map (·.1)
            let smooth := allSmoothUpTo primes sd.cutB
            sd.freeP.all fun r => primes.contains r && check2a pdivs smooth sd.cutB r && check2b sd.fac b D r

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

def gcdList (target : Nat) : List Entry → Bool
  | [] => false
  | e :: es => (e.exact && Nat.gcd (sigPP e.p e.minA) target > 1) || gcdList target es

def guaranteedD2Ext (spec : List Entry) : Bool :=
  let pprod := spec.foldl (fun acc e => acc * e.p) 1
  spec.any (·.par == .odd) || gcdList pprod spec

def guaranteedD2 (spec : List Entry) : Bool :=
  guaranteedD2Ext spec ||
  (spec.all (·.exact) &&
   let (b, sb) := minNumAb spec
   sb + 2 ≤ 2 * b)

def splitEntriesLoop (idx : Nat) : List Entry → List Nat → List Entry → List Entry → Option (List Entry × List Entry)
  | [], [], base, cop => some (base.reverse, cop.reverse)
  | [], _ :: _, _, _ => none
  | e :: es, [], base, cop => splitEntriesLoop (idx + 1) es [] (e :: base) cop
  | e :: es, k :: ks, base, cop =>
    if idx == k then splitEntriesLoop (idx + 1) es ks base (e :: cop)
    else splitEntriesLoop (idx + 1) es (k :: ks) (e :: base) cop

def checkBaseExt (entries : List Entry) (sd : Seed) (copIdxs : List Nat) (skipFree : Bool) (extraCop : Nat) : Bool :=
  match splitEntriesLoop 0 entries copIdxs [] [] with
  | none => false
  | some (base, cop) =>
    !base.isEmpty &&
    base.map (fun e => (e.p, e.minA)) == sd.fac &&
    (skipFree || base.all (fun e => e.exact || sd.freeP.contains e.p)) &&
    cop.all (fun e => 6 * e.p ≤ sd.p0 - 127) &&
    6 * extraCop ≤ sd.p0 - 127

def checkSurv (mVal sVal : Nat) (xs : List Nat) : Bool :=
  let ok := xs.all (fun d => 0 < d && d < mVal && mVal % d == 0)
  ok && !xs.isEmpty && xs.Nodup && xs.sum + 2 * mVal == sVal

def listSet (l : List Entry) (idx : Nat) (v : Entry) : List Entry :=
  match l, idx with
  | [], _ => []
  | _ :: xs, 0 => v :: xs
  | x :: xs, n + 1 => x :: listSet xs n v

def checkCert (seeds : List Seed) (survs : List (Nat × List Nat)) (allowMore : Bool) (fuel : Nat)
    (c : Cert) (spec : List Entry) (minP : Nat) : Bool :=
  match fuel with
  | 0 => false
  | fuel + 1 =>
  match c with
  | .B =>
    let rem := if allowMore then 5 - spec.length else 0
    let (n, d) := maxAbSpec spec minP rem
    0 < d && n ≤ 2 * d
  | .AL =>
    let (m, s) := minNumAb spec
    2 * m < s && s - 2 * m < 64
  | .NP i =>
    let (m, s) := minNumAb spec
    if s ≤ 2 * m then false
    else match spec[i]? with
      | none => false
      | some e =>
        let spec2 := if e.minA == 1 then spec.eraseIdx i else listSet spec i { e with minA := e.minA - 1 }
        let (m2, s2) := minNumAb spec2
        2 * m2 ≤ s2
  | .AS idx =>
    let (m, s) := minNumAb spec
    if s ≤ 2 * m then false
    else match survs[idx]? with
      | none => false
      | some (mv, xs) => mv == m && checkSurv m s xs
  | .AC qi si copIdxs =>
    let (m, s) := minNumAb spec
    if s ≤ 2 * m then false
    else match spec[qi]?, seeds[si]? with
      | some qE, some sd =>
        let others := spec.eraseIdx qi
        let (b, sb) := minNumAb others
        (qE.minA > 1 || sb + 2 ≤ 2 * b) && checkBaseExt others sd copIdxs true 0
      | _, _ => false
  | .KR qi si copIdxs =>
    (!allowMore || 5 - spec.length == 0) &&
    match spec[qi]?, seeds[si]? with
    | some qE, some sd =>
      let others := spec.eraseIdx qi
      (!(qE.par == .odd && qE.minA == 1) || guaranteedD2 others) &&
      checkBaseExt others sd copIdxs false 0
    | _, _ => false
  | .K5 si copIdxs sub =>
    allowMore && 5 - spec.length == 1 &&
    match seeds[si]? with
    | none => false
    | some sd =>
      guaranteedD2 spec && checkBaseExt spec sd copIdxs false 0 &&
      checkCert seeds survs false fuel sub spec minP
  | .KV qi si copIdxs sub =>
    allowMore && 5 - spec.length == 1 &&
    let (abN, abD) := maxAbSpec spec minP 0
    if abD == 0 || 2 * abD ≤ abN then false
    else
      let qMax := (2 * abD - 1) / (2 * abD - abN)
      match spec[qi]?, seeds[si]? with
      | some qE, some sd =>
        let others := spec.eraseIdx qi
        !(qE.par == .odd && qE.minA == 1) &&
        checkBaseExt others sd copIdxs false qMax &&
        checkCert seeds survs false fuel sub spec minP
      | _, _ => false
  | .K3 si copIdxs sub =>
    allowMore && 5 - spec.length == 2 &&
    match seeds[si]? with
    | none => false
    | some sd =>
      let (abN, abD) := maxAbSpec spec minP 0
      let p4Next := max minP ((sd.p0 - 127) / 6 + 1)
      guaranteedD2Ext spec && 0 < abD && p4Next ≥ 2 &&
      abN * p4Next * p4Next ≤ 2 * abD * (p4Next - 1) * (p4Next - 1) &&
      checkBaseExt spec sd copIdxs false 0 &&
      checkCert seeds survs false fuel sub spec minP
  | .SF idx cEx cHi =>
    match spec[idx]? with
    | none => false
    | some e =>
      !e.exact &&
      checkCert seeds survs allowMore fuel cEx (listSet spec idx { e with exact := true }) minP &&
      checkCert seeds survs allowMore fuel cHi (listSet spec idx { e with minA := e.minA + 2 }) minP
  | .S7 p c0 c1 c2 c3 c4 =>
    allowMore && nextPrime minP == some p && p ≤ 7 &&
    checkCert seeds survs true fuel c0 spec (p + 1) &&
    checkCert seeds survs true fuel c1 (spec ++ [⟨p, 1, true, .odd⟩]) (p + 1) &&
    checkCert seeds survs true fuel c2 (spec ++ [⟨p, 2, true, .even⟩]) (p + 1) &&
    checkCert seeds survs true fuel c3 (spec ++ [⟨p, 3, false, .odd⟩]) (p + 1) &&
    checkCert seeds survs true fuel c4 (spec ++ [⟨p, 4, false, .even⟩]) (p + 1)
  | .SP p c0 c1 c2 c3 =>
    allowMore && nextPrime minP == some p &&
    checkCert seeds survs true fuel c0 spec (p + 1) &&
    checkCert seeds survs true fuel c1 (spec ++ [⟨p, 1, true, .odd⟩]) (p + 1) &&
    checkCert seeds survs true fuel c2 (spec ++ [⟨p, 2, false, .even⟩]) (p + 1) &&
    checkCert seeds survs true fuel c3 (spec ++ [⟨p, 3, false, .odd⟩]) (p + 1)

-- =====================================================================
-- Basic arithmetic & primality soundness
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
-- Target invariants & SpecValid
-- =====================================================================

def Rep (n : ℕ) (x : ℤ) : Prop :=
  ∃ s ⊆ n.properDivisors, (∑ d ∈ s, (d : ℤ)) = x

def PropSum (n : ℕ) : ℤ :=
  ∑ d ∈ n.properDivisors, (d : ℤ)

def SeedOk (b : ℕ) : Prop :=
  1 < b ∧
  2392 ≤ PropSum b ∧
  (b : ℤ) + 127 ≤ 4 * PropSum b ∧
  (∀ y : ℤ, 64 ≤ y → y ≤ PropSum b - 64 → Rep b y) ∧
  (∀ k : ℤ, 0 ≤ k → k < PropSum b → ∃ i : ℤ, Rep b i ∧ k - 6 < i ∧ i ≤ k)

def NoCertExt (m : ℕ) : Prop :=
  ¬ ∃ b q j : ℕ, m = b * q^(j+1) ∧ 1 < b ∧ q.Prime ∧ b.Coprime q ∧ 3 ≤ q ∧
    let P := ∑ d ∈ b.properDivisors, (d : ℤ)
    let R := fun x : ℤ => ∃ s ⊆ b.properDivisors, (∑ d ∈ s, (d : ℤ)) = x
    2392 ≤ P ∧ (j = 0 → 2 ≤ (b : ℤ) - P) ∧
    (∀ y : ℤ, 64 ≤ y → y ≤ P-64 → R y) ∧
    (∀ k : ℤ, 0 ≤ k → k < P → ∃ i : ℤ, R i ∧ k-6 < i ∧ i ≤ k)

lemma false_of_seedOk {m b q j : ℕ}
    (hm_no : NoCertExt m)
    (hs : SeedOk b) (hm : m = b * q ^ (j + 1)) (hq : q.Prime) (hcop : b.Coprime q) (hq3 : 3 ≤ q)
    (hD2 : j = 0 → 2 ≤ (b : ℤ) - PropSum b) : False :=
  hm_no ⟨b, q, j, hm, hs.1, hq, hcop, hq3, hs.2.1, hD2, hs.2.2.2.1, hs.2.2.2.2⟩

def EntryValid (m minP : ℕ) (e : Entry) : Prop :=
  e.p.Prime ∧ e.p < minP ∧ Odd e.p ∧ e.p ∣ m ∧
  1 ≤ e.minA ∧ e.minA ≤ m.factorization e.p ∧
  (e.exact = true → m.factorization e.p = e.minA) ∧
  (match e.par with | .odd => Odd (m.factorization e.p) | .even => Even (m.factorization e.p)) ∧
  e.minA % 2 = m.factorization e.p % 2

def SpecValid (m : ℕ) (spec : List Entry) (minP : ℕ) (allowMore : Bool) : Prop :=
  (spec.map (·.p)).Pairwise (· < ·) ∧
  (∀ e ∈ spec, EntryValid m minP e) ∧
  (if allowMore then ∀ q ∈ m.primeFactors, (∃ e ∈ spec, e.p = q) ∨ minP ≤ q
   else ∀ q ∈ m.primeFactors, ∃ e ∈ spec, e.p = q)

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
  have hndp : (l.map (·.p)).Nodup := hpw.imp (fun h => Nat.ne_of_lt h)
  have hnd : l.Nodup := List.Nodup.of_map (·.p) hndp
  exact (List.prod_toFinset f hnd).symm

lemma list_map_prod_dvd {α : Type*} (l : List α) (f g : α → ℕ) (h : ∀ x ∈ l, f x ∣ g x) :
    (l.map f).prod ∣ (l.map g).prod := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.map_cons, List.prod_cons]
    exact mul_dvd_mul (h a List.mem_cons_self) (ih fun x hx => h x (List.mem_cons_of_mem a hx))

lemma spec_map_p_nodup {m : ℕ} {spec : List Entry} {minP : ℕ} {am : Bool}
    (hs : SpecValid m spec minP am) : (spec.map (·.p)).Nodup :=
  hs.1.imp (fun h => Nat.ne_of_lt h)

lemma spec_toFinset_subset {m : ℕ} {spec : List Entry} {minP : ℕ} {am : Bool}
    (hm : m ≠ 0) (hs : SpecValid m spec minP am) :
    (spec.map (·.p)).toFinset ⊆ m.primeFactors := by
  intro q hq
  rw [List.mem_toFinset, List.mem_map] at hq
  obtain ⟨e, he, rfl⟩ := hq
  have ev := hs.2.1 e he
  exact Nat.mem_primeFactors.mpr ⟨ev.1, ev.2.2.2.1, hm⟩

lemma spec_toFinset_card {m : ℕ} {spec : List Entry} {minP : ℕ} {am : Bool}
    (hs : SpecValid m spec minP am) :
    (spec.map (·.p)).toFinset.card = spec.length := by
  rw [List.toFinset_card_of_nodup (spec_map_p_nodup hs), List.length_map]

lemma specValid_mono_minP {m : ℕ} {spec : List Entry} {minP minP' : ℕ}
    (hs : SpecValid m spec minP true) (hle : minP ≤ minP')
    (hrem : ∀ q ∈ m.primeFactors, (∃ e ∈ spec, e.p = q) ∨ minP' ≤ q) :
    SpecValid m spec minP' true :=
  ⟨hs.1, fun e he => let ev := hs.2.1 e he; ⟨ev.1, lt_of_lt_of_le ev.2.1 hle, ev.2.2⟩, hrem⟩

lemma specValid_ext {m minP : ℕ} {spec : List Entry} (hs : SpecValid m spec minP true)
    {p minA : ℕ} {exact : Bool} {par : Par}
    (hp : p.Prime) (hmin : minP ≤ p) (hodd : Odd p) (hdvd : p ∣ m)
    (h1 : 1 ≤ minA) (hle : minA ≤ m.factorization p)
    (hex : exact = true → m.factorization p = minA)
    (hpar : match par with | .odd => Odd (m.factorization p) | .even => Even (m.factorization p))
    (hminpar : minA % 2 = m.factorization p % 2)
    (hrem : ∀ q ∈ m.primeFactors, (∃ e ∈ spec, e.p = q) ∨ q = p ∨ p + 1 ≤ q) :
    SpecValid m (spec ++ [⟨p, minA, exact, par⟩]) (p + 1) true := by
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

lemma spec_mem_p_unique {l : List Entry} (hnd : (l.map (·.p)).Nodup)
    {a b : Entry} (ha : a ∈ l) (hb : b ∈ l) (hab : a.p = b.p) : a = b := by
  induction l with
  | nil => simp at ha
  | cons x xs ih =>
    rw [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.mp ha with rfl | ha' <;> rcases List.mem_cons.mp hb with rfl | hb'
    · rfl
    · exfalso; exact hnd.1 (hab ▸ List.mem_map_of_mem hb')
    · exfalso; exact hnd.1 (hab.symm ▸ List.mem_map_of_mem ha')
    · exact ih hnd.2 ha' hb'

lemma prod_spec_factor_split {m : ℕ} (hm : m ≠ 0) {spec : List Entry} {minP : ℕ} {am : Bool}
    (hs : SpecValid m spec minP am) :
    (m = (spec.map (fun e => e.p ^ m.factorization e.p)).prod *
          ∏ q ∈ m.primeFactors \ (spec.map (·.p)).toFinset, q ^ m.factorization q) ∧
    (sigma 1 m = (spec.map (fun e => sigPP e.p (m.factorization e.p))).prod *
          ∏ q ∈ m.primeFactors \ (spec.map (·.p)).toFinset, sigPP q (m.factorization q)) := by
  set S := (spec.map (·.p)).toFinset
  have hsub : S ⊆ m.primeFactors := spec_toFinset_subset hm hs
  have hndp : (spec.map (·.p)).Nodup := spec_map_p_nodup hs
  have hprod_m : (spec.map (fun e => e.p ^ m.factorization e.p)).prod =
      ∏ q ∈ S, q ^ m.factorization q := by
    rw [list_prod_toFinset hs.1]
    have h1 : S = spec.toFinset.image (·.p) := by ext q; simp [S]
    rw [h1, Finset.prod_image]
    intro a ha b hb hab
    simp only [Finset.mem_coe, List.mem_toFinset] at ha hb
    exact spec_mem_p_unique hndp ha hb hab
  have hprod_s : (spec.map (fun e => sigPP e.p (m.factorization e.p))).prod =
      ∏ q ∈ S, sigPP q (m.factorization q) := by
    rw [list_prod_toFinset hs.1]
    have h1 : S = spec.toFinset.image (·.p) := by ext q; simp [S]
    rw [h1, Finset.prod_image]
    intro a ha b hb hab
    simp only [Finset.mem_coe, List.mem_toFinset] at ha hb
    exact spec_mem_p_unique hndp ha hb hab
  constructor
  · rw [hprod_m, mul_comm, Finset.prod_sdiff hsub]
    exact Nat.prod_primeFactors_pow_factorization hm
  · rw [hprod_s, mul_comm, Finset.prod_sdiff hsub]
    exact sigma_one_eq_prod_primeFactors hm

lemma prod_entries_dvd_and_sigma {m minP : ℕ} (hm : m ≠ 0)
    (l : List Entry) (hpw : (l.map (·.p)).Pairwise (· < ·))
    (hev : ∀ e ∈ l, EntryValid m minP e)
    (expFn : Entry → ℕ) (hle : ∀ e ∈ l, expFn e ≤ m.factorization e.p) :
    let B := (l.map (fun e => e.p ^ expFn e)).prod
    let SB := (l.map (fun e => sigPP e.p (expFn e))).prod
    0 < B ∧ B ∣ m ∧ sigma 1 B = SB := by
  intro B SB
  have hB_pos : 0 < B := by
    dsimp [B]
    exact List.prod_pos fun x hx => by
      rw [List.mem_map] at hx; obtain ⟨e, he, rfl⟩ := hx
      exact Nat.pow_pos (hev e he).1.pos
  have h_aux : ∀ l' : List Entry, (l'.map (·.p)).Pairwise (· < ·) →
      (∀ e ∈ l', EntryValid m minP e ∧ expFn e ≤ m.factorization e.p) →
      (l'.map (fun e => e.p ^ expFn e)).prod ∣ m ∧
      sigma 1 (l'.map (fun e => e.p ^ expFn e)).prod = (l'.map (fun e => sigPP e.p (expFn e))).prod := by
    intro l' hpw' hl'
    induction l' with
    | nil => simp
    | cons e es ih =>
      rw [List.map_cons, List.pairwise_cons] at hpw'
      have he := hl' e List.mem_cons_self
      have ih_res := ih hpw'.2 (fun e' he' => hl' e' (List.mem_cons_of_mem e he'))
      have hep := he.1.1
      have hpow_dvd : e.p ^ expFn e ∣ m := (hep.pow_dvd_iff_le_factorization hm).mpr he.2
      have hcop : Nat.Coprime (e.p ^ expFn e) (es.map (fun e' => e'.p ^ expFn e')).prod := by
        have hcop_gen : ∀ l'' : List Entry, (∀ e' ∈ l'', EntryValid m minP e' ∧ e.p < e'.p) →
            Nat.Coprime (e.p ^ expFn e) (l''.map (fun e' => e'.p ^ expFn e')).prod := by
          intro l'' hl''
          induction l'' with
          | nil => simp
          | cons y ys ihy =>
            simp only [List.map_cons, List.prod_cons]
            have hy := hl'' y List.mem_cons_self
            have h1 : Nat.Coprime (e.p ^ expFn e) (y.p ^ expFn y) :=
              (hep.coprime_iff_not_dvd.mpr fun h => absurd (Nat.dvd_prime hy.1.1 |>.mp h |>.resolve_left hep.ne_one) hy.2.ne).pow _ _
            exact h1.mul_right (ihy fun e' he' => hl'' e' (List.mem_cons_of_mem y he'))
        exact hcop_gen es fun e' he' => ⟨(hl' e' (List.mem_cons_of_mem e he')).1, hpw'.1 e'.p (List.mem_map_of_mem he')⟩
      refine ⟨hcop.mul_dvd_of_dvd_of_dvd hpow_dvd ih_res.1, ?_⟩
      simp only [List.map_cons, List.prod_cons]
      rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop,
          sigma_one_prime_pow hep, ih_res.2]
  have hres := h_aux l hpw (fun e he => ⟨hev e he, hle e he⟩)
  exact ⟨hB_pos, hres.1, hres.2⟩

lemma prod_entries_factorization {m minP : ℕ}
    (l : List Entry) (hpw : (l.map (·.p)).Pairwise (· < ·))
    (hev : ∀ e ∈ l, EntryValid m minP e)
    (expFn : Entry → ℕ) :
    let B := (l.map (fun e => e.p ^ expFn e)).prod
    (∀ e ∈ l, B.factorization e.p = expFn e) ∧
    (∀ q ∈ B.primeFactors, ∃ e ∈ l, e.p = q) := by
  induction l with
  | nil => simp
  | cons e es ih =>
    rw [List.map_cons, List.pairwise_cons] at hpw
    have he := hev e List.mem_cons_self
    have ih_res := ih hpw.2 (fun x hx => hev x (List.mem_cons_of_mem e hx))
    set Bes := (es.map (fun x => x.p ^ expFn x)).prod
    have hBes_pos : 0 < Bes := List.prod_pos fun x hx => by
      rw [List.mem_map] at hx; obtain ⟨y, hy, rfl⟩ := hx
      exact Nat.pow_pos (hev y (List.mem_cons_of_mem e hy)).1.pos
    have hep := he.1
    have hpe_pos : 0 < e.p ^ expFn e := Nat.pow_pos hep.pos
    have hne_e : ¬ e.p ∣ Bes := fun hd => by
      have hm := Nat.mem_primeFactors.mpr ⟨hep, hd, hBes_pos.ne'⟩
      obtain ⟨y, hy, hyq⟩ := ih_res.2 e.p hm
      have := hpw.1 y.p (List.mem_map_of_mem hy)
      omega
    have hfac_mul := Nat.factorization_mul hpe_pos.ne' hBes_pos.ne'
    constructor
    · intro x hx
      simp only [List.map_cons, List.prod_cons]
      rw [hfac_mul, Finsupp.coe_add, Pi.add_apply]
      rcases List.mem_cons.mp hx with rfl | hxs
      · rw [hep.factorization_pow, Finsupp.single_eq_same, Nat.factorization_eq_zero_of_not_dvd hne_e, add_zero]
      · have hne : x.p ≠ e.p := (hpw.1 x.p (List.mem_map_of_mem hxs)).ne'
        rw [hep.factorization_pow, Finsupp.single_eq_of_ne hne, zero_add]
        exact ih_res.1 x hxs
    · intro q hq
      simp only [List.map_cons, List.prod_cons] at hq
      rw [Nat.primeFactors_mul hpe_pos.ne' hBes_pos.ne', Finset.mem_union] at hq
      rcases hq with hq1 | hq2
      · have hqp := Nat.prime_of_mem_primeFactors hq1
        have hqd := hqp.dvd_of_dvd_pow (Nat.dvd_of_mem_primeFactors hq1)
        exact ⟨e, List.mem_cons_self, (hep.dvd_iff_eq hqp.ne_one).mp hqd⟩
      · obtain ⟨y, hy, hyq⟩ := ih_res.2 q hq2
        exact ⟨y, List.mem_cons_of_mem e hy, hyq⟩

-- =====================================================================
-- minNumAb, maxAbSpec, pairwise_lt_of_le_nodup
-- =====================================================================

lemma minNumAb_eq (l : List Entry) :
    minNumAb l = ((l.map (fun e => e.p ^ e.minA)).prod, (l.map (fun e => sigPP e.p e.minA)).prod) := by
  unfold minNumAb
  have hgen : ∀ (l' : List Entry) (x y : ℕ),
      l'.foldl (fun (nd : ℕ × ℕ) e => (nd.1 * e.p ^ e.minA, nd.2 * sigPP e.p e.minA)) (x, y) =
      (l'.foldl (fun acc e => acc * e.p ^ e.minA) x, l'.foldl (fun acc e => acc * sigPP e.p e.minA) y) := fun l' => by
    induction l' with | nil => intro _ _; rfl | cons a t ihl => intro x y; simp [ihl]
  rw [hgen l 1 1, foldl_mul_eq, foldl_mul_eq, one_mul, one_mul]

lemma pairwise_lt_of_le_nodup {l : List ℕ} (hle : l.Pairwise (· ≤ ·)) (hnd : l.Nodup) :
    l.Pairwise (· < ·) := by
  induction l with
  | nil => exact List.Pairwise.nil
  | cons a t ih =>
    rw [List.pairwise_cons] at hle ⊢
    rw [List.nodup_cons] at hnd
    exact ⟨fun x hx => lt_of_le_of_ne (hle.1 x hx) (fun h => hnd.1 (h ▸ hx)), ih hle.2 hnd.2⟩

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

lemma maxAbSpec_spec_part {m : ℕ} {spec : List Entry} {minP : ℕ} {am : Bool}
    (hs : SpecValid m spec minP am) :
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

lemma maxAbSpec_sound {m : ℕ} (hm : m ≠ 0) (hm_card : m.primeFactors.card ≤ 5)
    {spec : List Entry} {minP rem n d : ℕ} {am : Bool} (hs : SpecValid m spec minP am)
    (hrem : rem = if am then 5 - spec.length else 0)
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
    cases am
    · simp only [Bool.false_eq_true, ↓reduceIte]
      have h_empty : S_out = ∅ := by
        ext q
        simp only [S_out, Finset.mem_sdiff, Finset.notMem_empty, iff_false, not_and, not_not]
        intro hq
        obtain ⟨e, he, heq⟩ := hs.2.2 q hq
        exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨e, he, heq⟩)
      simp [h_empty]
    · simp only [↓reduceIte]
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
    cases am
    · exfalso
      obtain ⟨e, he, heq⟩ := hs.2.2 r hr.1
      exact hr.2 (List.mem_toFinset.mpr (List.mem_map.mpr ⟨e, he, heq⟩))
    · rcases hs.2.2 r hr.1 with ⟨e, he, rfl⟩ | hmin
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

lemma maxAbSpec_zero_sound {m : ℕ} {spec : List Entry} {minP n d : ℕ} {am : Bool}
    (hs : SpecValid m spec minP am) (hmax : maxAbSpec spec minP 0 = (n, d)) :
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
-- fastSort10, allDivsOfFac, allSmoothUpTo soundness
-- =====================================================================

lemma mergeNat_perm : ∀ (fuel : ℕ) (xs ys : List ℕ),
    xs.length + ys.length < fuel → List.Perm (mergeNat xs ys fuel) (xs ++ ys) := by
  intro fuel
  induction fuel with
  | zero => intro xs ys h; omega
  | succ fuel ih =>
    intro xs ys hlen
    cases xs with
    | nil => simp [mergeNat]
    | cons x xs =>
      cases ys with
      | nil => simp [mergeNat]
      | cons y ys =>
        unfold mergeNat
        split_ifs
        · refine List.Perm.cons x (ih xs (y :: ys) (by simp at hlen ⊢; omega))
        · have ih' := ih (x :: xs) ys (by simp at hlen ⊢; omega)
          have hcons : List.Perm (y :: (x :: xs ++ ys)) ((x :: xs) ++ y :: ys) :=
            (List.perm_middle (l₁ := x :: xs) (l₂ := ys) (a := y)).symm
          exact (List.Perm.cons y ih').trans hcons

lemma mergeNat_pairwise : ∀ (fuel : ℕ) (xs ys : List ℕ),
    xs.Pairwise (· ≤ ·) → ys.Pairwise (· ≤ ·) → xs.length + ys.length < fuel →
    (mergeNat xs ys fuel).Pairwise (· ≤ ·) := by
  intro fuel
  induction fuel with
  | zero => intro xs ys _ _ h; omega
  | succ fuel ih =>
    intro xs ys hxs hys hlen
    cases xs with
    | nil => simpa [mergeNat] using hys
    | cons x xs =>
      cases ys with
      | nil => simpa [mergeNat] using hxs
      | cons y ys =>
        unfold mergeNat
        rw [List.pairwise_cons] at hxs hys
        split_ifs with hxy
        · rw [List.pairwise_cons]
          refine ⟨fun z hz => ?_, ih xs (y :: ys) hxs.2 (List.pairwise_cons.mpr hys) (by simp at hlen ⊢; omega)⟩
          have hperm := mergeNat_perm fuel xs (y :: ys) (by simp at hlen ⊢; omega)
          rw [hperm.mem_iff, List.mem_append, List.mem_cons] at hz
          rcases hz with hx | rfl | hy
          · exact hxs.1 z hx
          · exact hxy
          · exact le_trans hxy (hys.1 z hy)
        · rw [List.pairwise_cons]
          refine ⟨fun z hz => ?_, ih (x :: xs) ys (List.pairwise_cons.mpr hxs) hys.2 (by simp at hlen ⊢; omega)⟩
          have hperm := mergeNat_perm fuel (x :: xs) ys (by simp at hlen ⊢; omega)
          rw [hperm.mem_iff, List.mem_append, List.mem_cons] at hz
          rcases hz with (rfl | hx) | hy
          · omega
          · exact le_trans (by omega) (hxs.1 z hx)
          · exact hys.1 z hy

lemma mergePairs_spec (xss : List (List ℕ)) (hpw : ∀ l ∈ xss, l.Pairwise (· ≤ ·)) :
    (∀ l ∈ mergePairs xss, l.Pairwise (· ≤ ·)) ∧
    List.Perm (mergePairs xss).flatten xss.flatten ∧
    2 * (mergePairs xss).length ≤ xss.length + 1 := by
  match xss with
  | [] => simp [mergePairs]
  | [x] => simp [mergePairs, hpw]
  | x :: y :: rest =>
    have hrest := mergePairs_spec rest (fun l hl => hpw l (by simp [hl]))
    have hx := hpw x (by simp)
    have hy := hpw y (by simp)
    have hm_pw := mergeNat_pairwise (x.length + y.length + 1) x y hx hy (by omega)
    have hm_perm := mergeNat_perm (x.length + y.length + 1) x y (by omega)
    refine ⟨?_, ?_, ?_⟩
    · intro l hl
      simp only [mergePairs, List.mem_cons] at hl
      rcases hl with rfl | hl'
      · exact hm_pw
      · exact hrest.1 l hl'
    · simp only [mergePairs, List.flatten_cons]
      simpa [List.append_assoc] using hm_perm.append hrest.2.1
    · simp only [mergePairs, List.length_cons]
      omega

lemma mergeAll_spec : ∀ (fuel : ℕ) (xss : List (List ℕ)),
    xss.length ≤ 2 ^ fuel → (∀ l ∈ xss, l.Pairwise (· ≤ ·)) →
    (mergeAll fuel xss).Pairwise (· ≤ ·) ∧ List.Perm (mergeAll fuel xss) xss.flatten := by
  intro fuel
  induction fuel with
  | zero =>
    intro xss hlen hpw
    match xss with
    | [] => simp [mergeAll]
    | [x] => simp [mergeAll, hpw]
    | _ :: _ :: _ => simp at hlen
  | succ fuel ih =>
    intro xss hlen hpw
    match xss with
    | [] => simp [mergeAll]
    | [x] => simp [mergeAll, hpw]
    | x :: y :: rest =>
      have hmp := mergePairs_spec (x :: y :: rest) hpw
      have hlen' : (mergePairs (x :: y :: rest)).length ≤ 2 ^ fuel := by
        have hpow : 2 ^ (fuel + 1) = 2 * 2 ^ fuel := by ring
        omega
      have ih_res := ih (mergePairs (x :: y :: rest)) hlen' hmp.1
      change (mergeAll fuel (mergePairs (x :: y :: rest))).Pairwise (· ≤ ·) ∧
             List.Perm (mergeAll fuel (mergePairs (x :: y :: rest))) (x :: y :: rest).flatten
      exact ⟨ih_res.1, ih_res.2.trans hmp.2.1⟩

lemma fastSort10_spec {xs : List ℕ} (hlen : xs.length ≤ 1024) :
    (fastSort10 xs).Pairwise (· ≤ ·) ∧ List.Perm (fastSort10 xs) xs := by
  unfold fastSort10
  have h := mergeAll_spec 10 (xs.map fun x => [x]) (by simpa using hlen)
    (fun l hl => by rw [List.mem_map] at hl; obtain ⟨x, _, rfl⟩ := hl; exact List.pairwise_singleton _ _)
  have hflat : ∀ l : List ℕ, (l.map fun x => [x]).flatten = l := fun l => by
    induction l with | nil => rfl | cons x xs ih => simp [ih]
  rw [hflat xs] at h
  exact h

lemma allDivsStep_mem (acc : List ℕ) (p : ℕ) :
    ∀ k j d, d ∈ allDivsStep acc p k (p ^ j) ↔ ∃ a ∈ acc, ∃ i < k, d = a * p ^ (j + i) := by
  intro k
  induction k with
  | zero => simp [allDivsStep]
  | succ k ih =>
    intro j d
    simp only [allDivsStep, List.mem_append, List.mem_map]
    rw [show p ^ j * p = p ^ (j + 1) by ring, ih (j + 1) d]
    constructor
    · rintro (⟨a, ha, rfl⟩ | ⟨a, ha, i, hi, rfl⟩)
      · exact ⟨a, ha, 0, Nat.zero_lt_succ k, by simp⟩
      · exact ⟨a, ha, i + 1, Nat.succ_lt_succ hi, by ring_nf⟩
    · rintro ⟨a, ha, i, hi, rfl⟩
      cases i with
      | zero => left; exact ⟨a, ha, by simp⟩
      | succ i => right; exact ⟨a, ha, i, Nat.lt_of_succ_lt_succ hi, by ring_nf⟩

lemma allDivsStep_nodup {p : ℕ} (hp : p.Prime) (acc : List ℕ) (hnd : acc.Nodup)
    (hpos : ∀ a ∈ acc, 0 < a) (hndvd : ∀ a ∈ acc, ¬ p ∣ a) :
    ∀ k j, (allDivsStep acc p k (p ^ j)).Nodup := by
  intro k
  induction k with
  | zero => intro j; simp [allDivsStep]
  | succ k ih =>
    intro j
    simp only [allDivsStep]
    have hpe_pos : 0 < p ^ j := Nat.pow_pos hp.pos
    have hnd1 : (acc.map (· * p ^ j)).Nodup :=
      hnd.map (fun a b hab => Nat.eq_of_mul_eq_mul_right hpe_pos hab)
    have hnd2 : (allDivsStep acc p k (p ^ (j + 1))).Nodup := ih (j + 1)
    rw [show p ^ j * p = p ^ (j + 1) by ring]
    refine hnd1.append hnd2 fun d hd1 hd2 => ?_
    rw [List.mem_map] at hd1
    obtain ⟨a, ha, rfl⟩ := hd1
    rw [allDivsStep_mem] at hd2
    obtain ⟨a', ha', i, _, heq⟩ := hd2
    have ha_pos := hpos a ha
    have ha'_pos := hpos a' ha'
    have hfac := congrArg (fun x => x.factorization p) heq
    rw [Nat.factorization_mul ha_pos.ne' hpe_pos.ne',
        Nat.factorization_mul ha'_pos.ne' (Nat.pow_pos hp.pos).ne',
        Finsupp.coe_add, Finsupp.coe_add, Pi.add_apply, Pi.add_apply,
        Nat.factorization_eq_zero_of_not_dvd (hndvd a ha),
        Nat.factorization_eq_zero_of_not_dvd (hndvd a' ha'),
        zero_add, zero_add, hp.factorization_pow, hp.factorization_pow,
        Finsupp.single_eq_same, Finsupp.single_eq_same] at hfac
    omega

lemma checkFacLoop_sound : ∀ (prev : ℕ) (fac : List (ℕ × ℕ)),
    checkFacLoop prev fac = true →
    (fac.map (·.1)).Pairwise (· < ·) ∧
    ∀ pe ∈ fac, prev < pe.1 ∧ pe.1.Prime ∧ 1 ≤ pe.2 := by
  intro prev fac h
  induction fac generalizing prev with
  | nil => simp
  | cons pe rest ih =>
    unfold checkFacLoop at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨hprev, hp⟩, he⟩, hrest⟩ := h
    have hprime := isPrimeBool_iff.mp hp
    have ih_res := ih pe.1 hrest
    constructor
    · rw [List.map_cons, List.pairwise_cons]
      refine ⟨fun q hq => ?_, ih_res.1⟩
      rw [List.mem_map] at hq; obtain ⟨x, hx, rfl⟩ := hq
      exact (ih_res.2 x hx).1
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact ⟨hprev, hprime, he⟩
      · have := ih_res.2 x hx'
        exact ⟨lt_trans hprev this.1, this.2⟩

lemma checkFacLoop_mono {p₁ p₂ : ℕ} (hle : p₁ ≤ p₂) (fac : List (ℕ × ℕ))
    (h : checkFacLoop p₂ fac = true) : checkFacLoop p₁ fac = true := by
  cases fac with
  | nil => simp [checkFacLoop]
  | cons pe rest =>
    unfold checkFacLoop at h ⊢
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h ⊢
    exact ⟨⟨⟨by omega, h.1.1.2⟩, h.1.2⟩, h.2⟩

lemma checkFacLoop_filter (pred : (ℕ × ℕ) → Bool) :
    ∀ (prev : ℕ) (fac : List (ℕ × ℕ)), checkFacLoop prev fac = true → checkFacLoop prev (fac.filter pred) = true := by
  intro prev fac h
  induction fac generalizing prev with
  | nil => simp [checkFacLoop]
  | cons pe rest ih =>
    unfold checkFacLoop at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    rw [List.filter_cons]
    split_ifs
    · unfold checkFacLoop
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨h.1, ih pe.1 h.2⟩
    · exact checkFacLoop_mono (Nat.le_of_lt h.1.1.1) _ (ih pe.1 h.2)

lemma allDivsOfFac_spec (fac : List (ℕ × ℕ)) (prev : ℕ) (hchk : checkFacLoop prev fac = true) :
    let b := fac.foldl (fun acc pe => acc * pe.1 ^ pe.2) 1
    0 < b ∧ (allDivsOfFac fac).Nodup ∧ ∀ d, d ∈ allDivsOfFac fac ↔ d ∈ b.divisors := by
  have hfold : ∀ (l : List (ℕ × ℕ)) (bd : ℕ) (acc : List ℕ) (P : ℕ),
      checkFacLoop bd l = true →
      0 < P → acc.Nodup →
      (∀ d ∈ acc, 0 < d ∧ d ∣ P ∧ ∀ q ∈ d.primeFactors, q ≤ bd) →
      (∀ d, d ∈ acc ↔ d ∈ P.divisors) →
      let P' := l.foldl (fun a pe => a * pe.1 ^ pe.2) P
      let res := l.foldl (fun a (p, e) => allDivsStep a p (e + 1) 1) acc
      0 < P' ∧ res.Nodup ∧ ∀ d, d ∈ res ↔ d ∈ P'.divisors := by
    intro l
    induction l with
    | nil =>
      intro bd acc P _ hP hnd _ hiff
      exact ⟨hP, hnd, hiff⟩
    | cons pe rest ih =>
      intro bd acc P hchk_l hP hnd hacc hiff
      rcases pe with ⟨p, e⟩
      have hspec := checkFacLoop_sound bd ((p, e) :: rest) hchk_l
      have hpe := hspec.2 (p, e) List.mem_cons_self
      have hbd_p : bd < p := hpe.1
      have hp : p.Prime := hpe.2.1
      have hchk_rest : checkFacLoop p rest = true := by
        unfold checkFacLoop at hchk_l
        simp only [Bool.and_eq_true] at hchk_l
        exact hchk_l.2
      have hP' : 0 < P * p ^ e := Nat.mul_pos hP (Nat.pow_pos hp.pos)
      have hndvd_acc : ∀ a ∈ acc, ¬ p ∣ a := fun a ha hdvd => by
        have h := hacc a ha
        have hm := Nat.mem_primeFactors.mpr ⟨hp, hdvd, h.1.ne'⟩
        have := h.2.2 p hm
        omega
      have hnd' : (allDivsStep acc p (e + 1) 1).Nodup := by
        simpa using allDivsStep_nodup hp acc hnd (fun a ha => (hacc a ha).1) hndvd_acc (e + 1) 0
      have hiff' : ∀ d, d ∈ allDivsStep acc p (e + 1) 1 ↔ d ∈ (P * p ^ e).divisors := by
        intro d
        have hm := allDivsStep_mem acc p (e + 1) 0 d
        simp only [pow_zero, zero_add] at hm
        rw [hm]
        constructor
        · rintro ⟨a, ha, i, hi, rfl⟩
          have ha_prop := (hiff a).mp ha
          have ha_dvd := Nat.dvd_of_mem_divisors ha_prop
          exact Nat.mem_divisors.mpr ⟨mul_dvd_mul ha_dvd (pow_dvd_pow p (Nat.lt_succ_iff.mp hi)), hP'.ne'⟩
        · intro hd
          obtain ⟨hd_dvd, _⟩ := Nat.mem_divisors.mp hd
          have hd_pos : 0 < d := Nat.pos_of_dvd_of_pos hd_dvd hP'
          have hp_P : ¬ p ∣ P := by
            intro hdvd
            obtain ⟨_, hP_dvd, hP_pf⟩ := hacc P ((hiff P).mpr (Nat.mem_divisors.mpr ⟨dvd_rfl, hP.ne'⟩))
            have := hP_pf p (Nat.mem_primeFactors.mpr ⟨hp, hdvd, hP.ne'⟩)
            omega
          have hfac_d : d.factorization p ≤ e := by
            have := Nat.factorization_le_iff_dvd hd_pos.ne' hP'.ne' |>.mpr hd_dvd p
            rw [Nat.factorization_mul hP.ne' (Nat.pow_pos hp.pos).ne', Finsupp.coe_add, Pi.add_apply,
                Nat.factorization_eq_zero_of_not_dvd hp_P, zero_add, hp.factorization_pow, Finsupp.single_eq_same] at this
            exact this
          set i := d.factorization p
          have hpi_dvd : p ^ i ∣ d := (hp.pow_dvd_iff_le_factorization hd_pos.ne').mpr le_rfl
          set a := d / p ^ i
          have hda : a * p ^ i = d := Nat.div_mul_cancel hpi_dvd
          have ha_dvd_mul : a ∣ P * p ^ e := (dvd_mul_right a (p ^ i)).trans (hda ▸ hd_dvd)
          have hnp_a : ¬ p ∣ a := by
            intro hpa
            have hpa' : p ^ (i + 1) ∣ d := by
              obtain ⟨r, hr⟩ := hpa
              rw [← hda, hr]
              exact ⟨r, by ring⟩
            have := (hp.pow_dvd_iff_le_factorization hd_pos.ne').mp hpa'
            omega
          have hcop_ap : Nat.Coprime a (p ^ e) := (hp.coprime_iff_not_dvd.mpr hnp_a).symm.pow_right e
          have ha_dvd_P : a ∣ P := hcop_ap.dvd_of_dvd_mul_right ha_dvd_mul
          exact ⟨a, (hiff a).mpr (Nat.mem_divisors.mpr ⟨ha_dvd_P, hP.ne'⟩), i, Nat.lt_succ_of_le hfac_d, hda.symm⟩
      have hacc' : ∀ d ∈ allDivsStep acc p (e + 1) 1, 0 < d ∧ d ∣ P * p ^ e ∧ ∀ q ∈ d.primeFactors, q ≤ p := by
        intro d hd
        obtain ⟨hd_dvd, _⟩ := Nat.mem_divisors.mp ((hiff' d).mp hd)
        have hd_pos := Nat.pos_of_dvd_of_pos hd_dvd hP'
        refine ⟨hd_pos, hd_dvd, fun q hq => ?_⟩
        have hqd := Nat.dvd_of_mem_primeFactors hq
        have hqp := Nat.prime_of_mem_primeFactors hq
        have hqmul := hqd.trans hd_dvd
        rcases hqp.dvd_mul.mp hqmul with hqP | hqpe
        · have := (hacc P ((hiff P).mpr (Nat.mem_divisors.mpr ⟨dvd_rfl, hP.ne'⟩))).2.2 q
            (Nat.mem_primeFactors.mpr ⟨hqp, hqP, hP.ne'⟩)
          omega
        · have hqdp := hqp.dvd_of_dvd_pow hqpe
          exact le_of_eq ((hp.dvd_iff_eq hqp.ne_one).mp hqdp).symm
      exact ih p (allDivsStep acc p (e + 1) 1) (P * p ^ e) hchk_rest hP' hnd' hacc' hiff'
  exact hfold fac prev [1] 1 hchk Nat.one_pos (List.nodup_singleton 1)
    (fun d hd => by simp only [List.mem_singleton] at hd; subst hd; simp)
    (fun d => by simp)

lemma addPowersCut_mono (acc : List ℕ) (p cut : ℕ) :
    ∀ k pe out x, x ∈ out → x ∈ addPowersCut acc p k pe cut out := by
  intro k
  induction k with
  | zero => intro pe out x hx; simpa [addPowersCut] using hx
  | succ k ih =>
    intro pe out x hx
    unfold addPowersCut
    dsimp only
    split_ifs
    · exact hx
    · exact ih (pe * p) _ x (List.mem_append.mpr (Or.inl hx))

lemma addPowersCut_mem (acc : List ℕ) (p cut : ℕ) (hp : 1 < p) :
    ∀ k pe out w₀ i, 0 < w₀ → w₀ ∈ acc → w₀ * (pe * p ^ i) ≤ cut → i < k →
      w₀ * (pe * p ^ i) ∈ addPowersCut acc p k pe cut out := by
  intro k
  induction k with
  | zero => intro _ _ _ _ _ _ _ hi; omega
  | succ k ih =>
    intro pe out w₀ i hw0_pos hw0 hle hi
    unfold addPowersCut
    dsimp only
    have hpe_le : pe ≤ cut := by
      have h1 : 1 ≤ p ^ i := Nat.one_le_pow _ _ (by omega)
      have h2 : pe ≤ pe * p ^ i := Nat.le_mul_of_pos_right pe h1
      have h3 : pe * p ^ i ≤ w₀ * (pe * p ^ i) := Nat.le_mul_of_pos_left _ hw0_pos
      omega
    have hnot : ¬ pe > cut := by omega
    rw [if_neg hnot]
    cases i with
    | zero =>
      simp only [pow_zero, mul_one] at hle ⊢
      have hmem : w₀ * pe ∈ acc.filterMap (fun d => let v := d * pe; if v ≤ cut then some v else none) := by
        rw [List.mem_filterMap]
        exact ⟨w₀, hw0, by dsimp only; rw [if_pos hle]⟩
      exact addPowersCut_mono acc p cut k (pe * p) _ _ (List.mem_append.mpr (Or.inr hmem))
    | succ i =>
      have hi' : i < k := Nat.lt_of_succ_lt_succ hi
      have hle' : w₀ * ((pe * p) * p ^ i) ≤ cut := by
        simpa [pow_succ, mul_assoc, mul_left_comm, mul_comm] using hle
      simpa [pow_succ, mul_assoc, mul_left_comm, mul_comm] using
        ih (pe * p) _ w₀ i hw0_pos hw0 hle' hi'

lemma allSmoothUpTo_complete (primes : List ℕ) (cut : ℕ) (hp : ∀ p ∈ primes, p.Prime) :
    ∀ w, 0 < w → w ≤ cut → (∀ q ∈ w.primeFactors, q ∈ primes) → w ∈ allSmoothUpTo primes cut := by
  have hmain : ∀ (l : List ℕ) (acc : List ℕ) (baseP : List ℕ),
      (∀ p ∈ l, p.Prime) →
      (∀ w, 0 < w → w ≤ cut → (∀ q ∈ w.primeFactors, q ∈ baseP) → w ∈ acc) →
      ∀ w, 0 < w → w ≤ cut → (∀ q ∈ w.primeFactors, q ∈ baseP ++ l) →
        w ∈ l.foldl (fun a p => addPowersCut a p (cut + 1) 1 cut []) acc := by
    intro l
    induction l with
    | nil =>
      intro acc baseP _ hacc w hw0 hle hpf
      simpa using hacc w hw0 hle (fun q hq => by simpa using hpf q hq)
    | cons p ps ih =>
      intro acc baseP hlp hacc w hw0 hle hpf
      have hpp := hlp p List.mem_cons_self
      simp only [List.foldl_cons]
      refine ih _ (baseP ++ [p]) (fun x hx => hlp x (List.mem_cons_of_mem p hx)) ?_ w hw0 hle ?_
      · intro u hu0 hule hupf
        set i := u.factorization p
        have hpi_dvd : p ^ i ∣ u := (hpp.pow_dvd_iff_le_factorization hu0.ne').mpr le_rfl
        set u₀ := u / p ^ i
        have hu_eq : u₀ * p ^ i = u := Nat.div_mul_cancel hpi_dvd
        have hu0_pos : 0 < u₀ := Nat.pos_of_dvd_of_pos ⟨p ^ i, hu_eq.symm⟩ hu0
        have hu0_le : u₀ ≤ cut := le_trans (Nat.div_le_self u (p ^ i)) hule
        have hu0_pf : ∀ q ∈ u₀.primeFactors, q ∈ baseP := by
          intro q hq
          have hqp := Nat.prime_of_mem_primeFactors hq
          have hqd := Nat.dvd_of_mem_primeFactors hq
          have hqu : q ∈ u.primeFactors := Nat.mem_primeFactors.mpr ⟨hqp, hqd.trans (Nat.div_dvd_of_dvd hpi_dvd), hu0.ne'⟩
          have hqp_in := hupf q hqu
          rw [List.mem_append, List.mem_singleton] at hqp_in
          rcases hqp_in with hqb | hqp_eq
          · exact hqb
          · exfalso
            subst q
            have hqpi : p ^ (i + 1) ∣ u := by
              obtain ⟨r, hr⟩ := hqd
              rw [← hu_eq, hr]
              exact ⟨r, by ring⟩
            have := (hpp.pow_dvd_iff_le_factorization hu0.ne').mp hqpi
            omega
        have hu0_mem : u₀ ∈ acc := hacc u₀ hu0_pos hu0_le hu0_pf
        have hi_lt : i < cut + 1 := by
          have h2p : 2 ≤ p := hpp.two_le
          have hi1 : i < 2 ^ i := Nat.lt_two_pow_self
          have h2pi : 2 ^ i ≤ p ^ i := Nat.pow_le_pow_left h2p i
          have hpi_le_u : p ^ i ≤ u := Nat.le_of_dvd hu0 hpi_dvd
          omega
        have hmul_le : u₀ * (1 * p ^ i) ≤ cut := by simpa [hu_eq] using hule
        simpa [hu_eq] using addPowersCut_mem acc p cut hpp.one_lt (cut + 1) 1 [] u₀ i hu0_pos hu0_mem hmul_le hi_lt
      · intro q hq
        have := hpf q hq
        simpa [List.mem_append] using this
  intro w hw0 hle hpf
  have h1 : ∀ u, 0 < u → u ≤ cut → (∀ q ∈ u.primeFactors, q ∈ ([] : List ℕ)) → u ∈ ([1] : List ℕ) := by
    intro u hu0 _ hupf
    have hu1 : u = 1 := by
      by_contra hne
      obtain ⟨q, hqp, hqd⟩ := Nat.exists_prime_and_dvd hne
      have hqm : q ∈ u.primeFactors := Nat.mem_primeFactors.mpr ⟨hqp, hqd, hu0.ne'⟩
      exact absurd (hupf q hqm) (by simp)
    subst hu1; simp
  exact hmain primes [1] [] hp h1 w hw0 hle (by simpa using hpf)

-- =====================================================================
-- IvsSound, gap6Ok, checkDenseLoop, DenseSeed
-- =====================================================================

def IvsSound (U : Finset ℕ) (ivs : List (ℕ × ℕ)) : Prop :=
  ∀ a b y : ℕ, (a, b) ∈ ivs → a ≤ b ∧ (a ≤ y → y ≤ b → ∃ s ⊆ U, s.sum id = y)

lemma mergeStep_sound {U : Finset ℕ} (a b curA curB : ℕ) (acc : List (ℕ × Nat))
    (hab : a ≤ b) (hcur : curA ≤ curB)
    (h1 : ∀ y, a ≤ y → y ≤ b → ∃ s ⊆ U, s.sum id = y)
    (h2 : ∀ y, curA ≤ y → y ≤ curB → ∃ s ⊆ U, s.sum id = y)
    (hacc : IvsSound U acc) :
    let (ca, cb, acc') := mergeStep a b curA curB acc
    ca ≤ cb ∧ (∀ y, ca ≤ y → y ≤ cb → ∃ s ⊆ U, s.sum id = y) ∧ IvsSound U acc' := by
  unfold mergeStep
  split_ifs with hle
  · refine ⟨le_trans hcur (le_max_left _ _), fun y hy1 hy2 => ?_, hacc⟩
    by_cases hyb : y ≤ curB
    · exact h2 y hy1 hyb
    · exact h1 y (by omega) ((le_max_iff.mp hy2).resolve_left (by omega))
  · refine ⟨hab, h1, fun a' b' y hmem => ?_⟩
    rw [List.mem_cons] at hmem
    rcases hmem with heq | hmem'
    · injection heq with ha hb; subst ha; subst hb
      exact ⟨hcur, h2 y⟩
    · exact hacc a' b' y hmem'

lemma mergeIvsLoop_sound {U : Finset ℕ} :
    ∀ (fuel : ℕ) (iv1 iv2 : List (ℕ × ℕ)) (curA curB : ℕ) (acc : List (ℕ × ℕ)),
      IvsSound U iv1 → IvsSound U iv2 → curA ≤ curB →
      (∀ y, curA ≤ y → y ≤ curB → ∃ s ⊆ U, s.sum id = y) →
      IvsSound U acc →
      IvsSound U (mergeIvsLoop iv1 iv2 curA curB acc fuel) := by
  intro fuel
  induction fuel with
  | zero =>
    intro iv1 iv2 curA curB acc _ _ hcur hc hacc
    unfold mergeIvsLoop
    intro a b y hmem
    rw [List.mem_reverse, List.mem_cons] at hmem
    rcases hmem with heq | hmem'
    · injection heq with ha hb; subst ha; subst hb; exact ⟨hcur, hc y⟩
    · exact hacc a b y hmem'
  | succ fuel ih =>
    intro iv1 iv2 curA curB acc hiv1 hiv2 hcur hc hacc
    unfold mergeIvsLoop
    cases iv1 with
    | nil =>
      cases iv2 with
      | nil =>
        intro a b y hmem
        rw [List.mem_reverse, List.mem_cons] at hmem
        rcases hmem with heq | hmem'
        · injection heq with ha hb; subst ha; subst hb; exact ⟨hcur, hc y⟩
        · exact hacc a b y hmem'
      | cons p2 t2 =>
        rcases p2 with ⟨a, b⟩
        have hp := hiv2 a b a (List.mem_cons_self)
        have hstep := mergeStep_sound a b curA curB acc hp.1 hcur
          (fun y hy1 hy2 => (hiv2 a b y List.mem_cons_self).2 hy1 hy2) hc hacc
        exact ih [] t2 _ _ _ (by simp [IvsSound])
          (fun a' b' y hm => hiv2 a' b' y (List.mem_cons_of_mem _ hm))
          hstep.1 hstep.2.1 hstep.2.2
    | cons p1 t1 =>
      cases iv2 with
      | nil =>
        rcases p1 with ⟨a, b⟩
        have hp := hiv1 a b a (List.mem_cons_self)
        have hstep := mergeStep_sound a b curA curB acc hp.1 hcur
          (fun y hy1 hy2 => (hiv1 a b y List.mem_cons_self).2 hy1 hy2) hc hacc
        exact ih t1 [] _ _ _
          (fun a' b' y hm => hiv1 a' b' y (List.mem_cons_of_mem _ hm))
          (by simp [IvsSound]) hstep.1 hstep.2.1 hstep.2.2
      | cons p2 t2 =>
        rcases p1 with ⟨a1, b1⟩
        rcases p2 with ⟨a2, b2⟩
        dsimp only
        split_ifs
        · have hp := hiv1 a1 b1 a1 (List.mem_cons_self)
          have hstep := mergeStep_sound a1 b1 curA curB acc hp.1 hcur
            (fun y hy1 hy2 => (hiv1 a1 b1 y List.mem_cons_self).2 hy1 hy2) hc hacc
          exact ih t1 ((a2, b2) :: t2) _ _ _
            (fun a' b' y hm => hiv1 a' b' y (List.mem_cons_of_mem _ hm))
            hiv2 hstep.1 hstep.2.1 hstep.2.2
        · have hp := hiv2 a2 b2 a2 (List.mem_cons_self)
          have hstep := mergeStep_sound a2 b2 curA curB acc hp.1 hcur
            (fun y hy1 hy2 => (hiv2 a2 b2 y List.mem_cons_self).2 hy1 hy2) hc hacc
          exact ih ((a1, b1) :: t1) t2 _ _ _ hiv1
            (fun a' b' y hm => hiv2 a' b' y (List.mem_cons_of_mem _ hm))
            hstep.1 hstep.2.1 hstep.2.2

lemma mergeIvs_sound {U : Finset ℕ} {iv1 iv2 : List (ℕ × ℕ)}
    (h1 : IvsSound U iv1) (h2 : IvsSound U iv2) :
    IvsSound U (mergeIvs iv1 iv2) := by
  unfold mergeIvs
  cases iv1 with
  | nil => exact h2
  | cons p1 t1 =>
    cases iv2 with
    | nil => exact h1
    | cons p2 t2 =>
      rcases p1 with ⟨a1, b1⟩
      rcases p2 with ⟨a2, b2⟩
      dsimp only
      split_ifs
      · have hp := h1 a1 b1 a1 List.mem_cons_self
        exact mergeIvsLoop_sound _ t1 ((a2, b2) :: t2) a1 b1 []
          (fun a b y hm => h1 a b y (List.mem_cons_of_mem _ hm)) h2 hp.1
          (fun y hy1 hy2 => (h1 a1 b1 y List.mem_cons_self).2 hy1 hy2) (by simp [IvsSound])
      · have hp := h2 a2 b2 a2 List.mem_cons_self
        exact mergeIvsLoop_sound _ ((a1, b1) :: t1) t2 a2 b2 []
          h1 (fun a b y hm => h2 a b y (List.mem_cons_of_mem _ hm)) hp.1
          (fun y hy1 hy2 => (h2 a2 b2 y List.mem_cons_self).2 hy1 hy2) (by simp [IvsSound])

lemma ivsSound_insert_shift {U : Finset ℕ} {d : ℕ} (hd : d ∉ U) {ivs : List (ℕ × ℕ)}
    (hiv : IvsSound U ivs) :
    IvsSound (insert d U) (ivs.map (fun (a, bb) => (a + d, bb + d))) := by
  intro a' b' y hmem
  rw [List.mem_map] at hmem
  obtain ⟨⟨a, b⟩, hab, heq⟩ := hmem
  injection heq with ha hb
  subst ha; subst hb
  have h1 := hiv a b (y - d) hab
  refine ⟨by omega, fun hy1 hy2 => ?_⟩
  obtain ⟨s, hs, hsum⟩ := h1.2 (by omega) (by omega)
  refine ⟨insert d s, Finset.insert_subset_insert d hs, ?_⟩
  have hdn : d ∉ s := fun h => hd (hs h)
  rw [Finset.sum_insert hdn, id_eq, hsum]
  omega

lemma ivsSound_mono {U : Finset ℕ} (d : ℕ) {ivs : List (ℕ × ℕ)} (hiv : IvsSound U ivs) :
    IvsSound (insert d U) ivs := fun a b y hmem =>
  let h := hiv a b y hmem
  ⟨h.1, fun hy1 hy2 => let ⟨s, hs, hsum⟩ := h.2 hy1 hy2; ⟨s, hs.trans (Finset.subset_insert d U), hsum⟩⟩

lemma has64Cov_sound {U : Finset ℕ} {ivs : List (ℕ × ℕ)} (hiv : IvsSound U ivs) {hi : ℕ}
    (hcov : has64Cov ivs hi = true) :
    ∀ y, 64 ≤ y → y ≤ hi → ∃ s ⊆ U, s.sum id = y := by
  induction ivs with
  | nil => simp [has64Cov] at hcov
  | cons p rest ih =>
    rcases p with ⟨a, b⟩
    unfold has64Cov at hcov
    rw [Bool.or_eq_true] at hcov
    rcases hcov with hc | hr
    · simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      intro y hy1 hy2
      exact (hiv a b y List.mem_cons_self).2 (by omega) (by omega)
    · exact ih (fun a' b' y' hm => hiv a' b' y' (List.mem_cons_of_mem _ hm)) hr

lemma gap6OkAux_cov {U : Finset ℕ} :
    ∀ (l : List (ℕ × ℕ)) (prevB lastEnd : ℕ),
      IvsSound U l → gap6OkAux prevB l = true →
      (∃ s ⊆ U, s.sum id = prevB) →
      (match l.getLast? with | some (_, e) => e == lastEnd | none => prevB == lastEnd) = true →
      ∀ k, prevB ≤ k → k < lastEnd →
        ∃ i, (∃ s ⊆ U, s.sum id = i) ∧ i ≤ k ∧ k < i + 6 := by
  intro l
  induction l with
  | nil =>
    intro prevB lastEnd _ _ _ hlast k hk1 hk2
    simp only [List.getLast?_nil, beq_iff_eq] at hlast
    omega
  | cons p rest ih =>
    intro prevB lastEnd hivs haux hprev hlast k hk1 hk2
    rcases p with ⟨a, b⟩
    unfold gap6OkAux at haux
    simp only [Bool.and_eq_true, decide_eq_true_eq] at haux
    have hab := hivs a b b List.mem_cons_self
    by_cases hka : k < a
    · exact ⟨prevB, hprev, hk1, by omega⟩
    · by_cases hkb : k ≤ b
      · exact ⟨k, (hivs a b k List.mem_cons_self).2 (by omega) hkb, le_rfl, by omega⟩
      · have hb_rep : ∃ s ⊆ U, s.sum id = b := hab.2 hab.1 le_rfl
        have hlast' : (match rest.getLast? with | some (_, e) => e == lastEnd | none => b == lastEnd) = true := by
          cases rest with
          | nil => simpa using hlast
          | cons p' r' =>
            rw [List.getLast?_cons_cons] at hlast
            cases hgl : (p' :: r').getLast? with
            | none => exfalso; have hnil := List.getLast?_eq_none_iff.mp hgl; simp at hnil
            | some x => rcases x with ⟨_, e⟩; simpa [hgl] using hlast
        exact ih b lastEnd (fun a' b' y' hm => hivs a' b' y' (List.mem_cons_of_mem _ hm))
          haux.2 hb_rep hlast' k (by omega) hk2

lemma gap6Ok_sound {U : Finset ℕ} {ivs : List (ℕ × ℕ)} {lastEnd : ℕ}
    (hiv : IvsSound U ivs) (hgap : gap6Ok lastEnd ivs = true) :
    ∀ k, k < lastEnd → ∃ i, (∃ s ⊆ U, s.sum id = i) ∧ i ≤ k ∧ k < i + 6 := by
  cases ivs with
  | nil => simp [gap6Ok] at hgap
  | cons p rest =>
    rcases p with ⟨a, b⟩
    cases a with
    | succ _ => simp [gap6Ok] at hgap
    | zero =>
      unfold gap6Ok at hgap
      simp only [Bool.and_eq_true] at hgap
      obtain ⟨haux, hlast⟩ := hgap
      have h0b := hiv 0 b
      intro k hk
      by_cases hkb : k ≤ b
      · exact ⟨k, (h0b k List.mem_cons_self).2 (Nat.zero_le _) hkb, le_rfl, by omega⟩
      · have hb_rep : ∃ s ⊆ U, s.sum id = b := (h0b b List.mem_cons_self).2 (Nat.zero_le _) le_rfl
        have hlast' : (match rest.getLast? with | some (_, e) => e == lastEnd | none => b == lastEnd) = true := by
          cases rest with
          | nil => simpa using hlast
          | cons p' r' =>
            rw [List.getLast?_cons_cons] at hlast
            cases hgl : (p' :: r').getLast? with
            | none => exfalso; have hnil := List.getLast?_eq_none_iff.mp hgl; simp at hnil
            | some x => rcases x with ⟨_, e⟩; simpa [hgl] using hlast
        exact gap6OkAux_cov rest b lastEnd
          (fun a' b' y' hm => hiv a' b' y' (List.mem_cons_of_mem _ hm))
          haux hb_rep hlast' k (by omega) hk

lemma checkDenseTail_sound (b₀ : ℕ) :
    ∀ (ds : List ℕ) (U : Finset ℕ),
      ds.Pairwise (· < ·) →
      (∀ d ∈ ds, d ∈ b₀.properDivisors) →
      U ⊆ b₀.properDivisors →
      (∀ x ∈ U, ∀ d ∈ ds, x < d) →
      (∀ d ∈ ds, ∀ x ∈ b₀.properDivisors, x < d → x ∈ U ∨ x ∈ ds) →
      checkDenseTail (∑ x ∈ U, x) ds = true →
      ∀ d ∈ ds, d + 127 ≤ ∑ x ∈ b₀.properDivisors.filter (· < d), x := by
  intro ds
  induction ds with
  | nil => simp
  | cons d ds ih =>
    intro U hpw hds hU_sub hU_lt hcov htail d' hd'
    rw [List.pairwise_cons] at hpw
    unfold checkDenseTail at htail
    simp only [Bool.and_eq_true, decide_eq_true_eq] at htail
    have hd_not : d ∉ U := fun h => Nat.lt_irrefl d (hU_lt d h d List.mem_cons_self)
    have hU_sub_lt : U ⊆ b₀.properDivisors.filter (· < d) := by
      intro x hx
      exact Finset.mem_filter.mpr ⟨hU_sub hx, hU_lt x hx d List.mem_cons_self⟩
    have hsum_le : ∑ x ∈ U, x ≤ ∑ x ∈ b₀.properDivisors.filter (· < d), x :=
      Finset.sum_le_sum_of_subset hU_sub_lt
    rcases List.mem_cons.mp hd' with rfl | hds'
    · omega
    · have hsum_eq : (∑ x ∈ U, x) + d = ∑ x ∈ insert d U, x := by
        rw [Finset.sum_insert hd_not]; ring
      rw [hsum_eq] at htail
      refine ih (insert d U) hpw.2 (fun y hy => hds y (List.mem_cons_of_mem d hy)) ?_ ?_ ?_ htail.2 d' hds'
      · exact Finset.insert_subset_iff.mpr ⟨hds d List.mem_cons_self, hU_sub⟩
      · intro x hx y hy
        rw [Finset.mem_insert] at hx
        rcases hx with rfl | hxU
        · exact hpw.1 y hy
        · exact hU_lt x hxU y (List.mem_cons_of_mem d hy)
      · intro y hy x hx hxy
        rcases hcov y (List.mem_cons_of_mem d hy) x hx hxy with hxU | hxds
        · left; exact Finset.mem_insert_of_mem hxU
        · rcases List.mem_cons.mp hxds with rfl | hxds'
          · left; exact Finset.mem_insert_self _ _
          · right; exact hxds'


-- =====================================================================
-- DenseFrom, DenseSeed, checkDenseLoop, checkSeedFull soundness
-- =====================================================================

def DenseFrom (B n : ℕ) : Prop :=
  ∀ d ∈ n.properDivisors, B < d → d + 127 ≤ ∑ x ∈ n.properDivisors.filter (· < d), x

def DenseSeed (b₀ n B : ℕ) : Prop :=
  1 < b₀ ∧ b₀ ∣ n ∧
  2392 ≤ PropSum n ∧
  (n : ℤ) + 127 ≤ 4 * PropSum n ∧
  (let U₀ := b₀.properDivisors.filter (· ≤ B)
   let S_B := ∑ x ∈ U₀, x
   128 ≤ S_B ∧ B + 127 ≤ S_B ∧
   (∀ y : ℕ, 64 ≤ y → y ≤ S_B - 64 → ∃ s ⊆ U₀, s.sum id = y) ∧
   (∀ k : ℕ, k < S_B → ∃ i : ℕ, (∃ s ⊆ U₀, s.sum id = i) ∧ i ≤ k ∧ k < i + 6)) ∧
  DenseFrom B n

lemma denseSeed_pos {b₀ n B : ℕ} (hd : DenseSeed b₀ n B) : 0 < n := by
  by_contra h0
  have hn0 : n = 0 := by omega
  have hP := hd.2.2.1
  rw [hn0] at hP
  simp [PropSum] at hP

lemma propSum_eq_nat (n : ℕ) : PropSum n = ((∑ d ∈ n.properDivisors, d : ℕ) : ℤ) := by
  simp [PropSum]

lemma propSum_mul_le {b n : ℕ} (hb : 0 < b) (hbn : b ∣ n) :
    ((n / b : ℕ) : ℤ) * PropSum b ≤ PropSum n := by
  obtain ⟨k, rfl⟩ := hbn
  by_cases hk0 : k = 0
  · subst hk0; simp [PropSum]
  have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
  have hmul_div : b * k / b = k := Nat.mul_div_cancel_left k hb
  rw [hmul_div]
  have hsub : b.divisors.image (· * k) ⊆ (b * k).divisors := by
    intro y hy
    rw [Finset.mem_image] at hy
    obtain ⟨d, hd, rfl⟩ := hy
    obtain ⟨hdb, _⟩ := Nat.mem_divisors.mp hd
    exact Nat.mem_divisors.mpr ⟨mul_dvd_mul_right hdb k, (Nat.mul_pos hb hkpos).ne'⟩
  have hinj : Function.Injective (· * k) := fun x y hxy => Nat.eq_of_mul_eq_mul_right hkpos hxy
  have hsum_div : k * ∑ d ∈ b.divisors, d ≤ ∑ x ∈ (b * k).divisors, x := by
    have him : ∑ y ∈ b.divisors.image (· * k), y = ∑ d ∈ b.divisors, (d * k) :=
      Finset.sum_image (fun x _ y _ h => hinj h)
    calc k * ∑ d ∈ b.divisors, d
        = ∑ d ∈ b.divisors, (d * k) := by rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun _ _ => mul_comm _ _
      _ = ∑ y ∈ b.divisors.image (· * k), y := him.symm
      _ ≤ ∑ x ∈ (b * k).divisors, x := Finset.sum_le_sum_of_subset hsub
  have hsig_b : ∑ d ∈ b.divisors, d = (∑ d ∈ b.properDivisors, d) + b :=
    Nat.sum_divisors_eq_sum_properDivisors_add_self
  have hsig_bk : ∑ d ∈ (b * k).divisors, d = (∑ d ∈ (b * k).properDivisors, d) + b * k :=
    Nat.sum_divisors_eq_sum_properDivisors_add_self
  have hle_nat : k * (∑ d ∈ b.properDivisors, d) ≤ ∑ d ∈ (b * k).properDivisors, d := by
    have : k * ((∑ d ∈ b.properDivisors, d) + b) ≤ (∑ d ∈ (b * k).properDivisors, d) + b * k := by
      rwa [← hsig_b, ← hsig_bk]
    nlinarith
  rw [propSum_eq_nat, propSum_eq_nat]
  exact_mod_cast hle_nat

lemma checkDenseLoop_sound (b₀ B : ℕ) :
    ∀ (ds : List ℕ) (U : Finset ℕ) (ivs : List (ℕ × ℕ)),
      ds.Pairwise (· < ·) →
      (∀ d ∈ ds, d ∈ b₀.properDivisors) →
      U ⊆ b₀.properDivisors →
      (∀ x ∈ U, ∀ d ∈ ds, x < d) →
      (∀ d ∈ ds, ∀ x ∈ b₀.properDivisors, x < d → x ∈ U ∨ x ∈ ds) →
      (∀ x ∈ b₀.properDivisors, x ∉ ds → x ∈ U) →
      IvsSound U ivs →
      checkDenseLoop B (∑ x ∈ U, x) ivs ds = true →
      (let U₀ := b₀.properDivisors.filter (· ≤ B)
       let S_B := ∑ x ∈ U₀, x
       128 ≤ S_B ∧ B + 127 ≤ S_B ∧
       (∀ y : ℕ, 64 ≤ y → y ≤ S_B - 64 → ∃ s ⊆ U₀, s.sum id = y) ∧
       (∀ k : ℕ, k < S_B → ∃ i : ℕ, (∃ s ⊆ U₀, s.sum id = i) ∧ i ≤ k ∧ k < i + 6)) ∧
      DenseFrom B b₀ := by
  intro ds
  induction ds with
  | nil =>
    intro U ivs _ _ _ _ _ _ _ hchk
    simp [checkDenseLoop] at hchk
  | cons d ds ih =>
    intro U ivs hpw hds hU_sub hU_lt hcov hmiss hivs hchk
    rw [List.pairwise_cons] at hpw
    have hd_mem := hds d List.mem_cons_self
    have hd_not : d ∉ U := fun h => Nat.lt_irrefl d (hU_lt d h d List.mem_cons_self)
    set U' := insert d U
    have hU'_sub : U' ⊆ b₀.properDivisors := Finset.insert_subset_iff.mpr ⟨hd_mem, hU_sub⟩
    have hS' : (∑ x ∈ U, x) + d = ∑ x ∈ U', x := by rw [Finset.sum_insert hd_not]; ring
    have hivs' : IvsSound U' (mergeIvs ivs (ivs.map (fun (a, bb) => (a + d, bb + d)))) :=
      mergeIvs_sound (ivsSound_mono d hivs) (ivsSound_insert_shift hd_not hivs)
    unfold checkDenseLoop at hchk
    dsimp only at hchk
    split_ifs at hchk with hdB hdgt
    · have hd_eq : d = B := beq_iff_eq.mp hdB
      subst hd_eq
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hchk
      obtain ⟨⟨⟨⟨h128, hB127⟩, hcov64⟩, hgap6⟩, htail⟩ := hchk
      rw [hS'] at h128 hB127 hcov64 hgap6 htail
      have hU'_eq : U' = b₀.properDivisors.filter (· ≤ d) := by
        ext x
        rw [Finset.mem_filter]
        constructor
        · intro hx
          refine ⟨hU'_sub hx, ?_⟩
          rw [Finset.mem_insert] at hx
          rcases hx with rfl | hxU
          · exact le_rfl
          · exact le_of_lt (hU_lt x hxU d List.mem_cons_self)
        · intro ⟨hxb, hxle⟩
          rcases eq_or_lt_of_le hxle with rfl | hxlt
          · exact Finset.mem_insert_self _ _
          · rcases hcov d List.mem_cons_self x hxb hxlt with hxU | hxds
            · exact Finset.mem_insert_of_mem hxU
            · exfalso
              rcases List.mem_cons.mp hxds with rfl | hxds'
              · omega
              · have := hpw.1 x hxds'; omega
      refine ⟨?_, ?_⟩
      · rw [← hU'_eq]
        refine ⟨h128, hB127, has64Cov_sound hivs' hcov64, gap6Ok_sound hivs' hgap6⟩
      · have hU'_lt : ∀ x ∈ U', ∀ y ∈ ds, x < y := fun x hx y hy => by
          rw [Finset.mem_insert] at hx
          rcases hx with rfl | hxU
          · exact hpw.1 y hy
          · exact hU_lt x hxU y (List.mem_cons_of_mem d hy)
        have hcov' : ∀ y ∈ ds, ∀ x ∈ b₀.properDivisors, x < y → x ∈ U' ∨ x ∈ ds := fun y hy x hx hxy => by
          rcases hcov y (List.mem_cons_of_mem d hy) x hx hxy with hxU | hxds
          · left; exact Finset.mem_insert_of_mem hxU
          · rcases List.mem_cons.mp hxds with rfl | hxds'
            · left; exact Finset.mem_insert_self _ _
            · right; exact hxds'
        have htail_res := checkDenseTail_sound b₀ ds U' hpw.2
          (fun y hy => hds y (List.mem_cons_of_mem d hy)) hU'_sub hU'_lt hcov' htail
        intro y hy hdy
        apply htail_res y
        by_contra hy_not
        have hy_in_U' : y ∈ U' := by
          by_cases hyd : y = d
          · omega
          · exact Finset.mem_insert_of_mem (hmiss y hy (by simp [List.mem_cons, hyd, hy_not]))
        rw [hU'_eq, Finset.mem_filter] at hy_in_U'
        omega
    · have hU'_lt : ∀ x ∈ U', ∀ y ∈ ds, x < y := fun x hx y hy => by
        rw [Finset.mem_insert] at hx
        rcases hx with rfl | hxU
        · exact hpw.1 y hy
        · exact hU_lt x hxU y (List.mem_cons_of_mem d hy)
      have hcov' : ∀ y ∈ ds, ∀ x ∈ b₀.properDivisors, x < y → x ∈ U' ∨ x ∈ ds := fun y hy x hx hxy => by
        rcases hcov y (List.mem_cons_of_mem d hy) x hx hxy with hxU | hxds
        · left; exact Finset.mem_insert_of_mem hxU
        · rcases List.mem_cons.mp hxds with rfl | hxds'
          · left; exact Finset.mem_insert_self _ _
          · right; exact hxds'
      have hmiss' : ∀ x ∈ b₀.properDivisors, x ∉ ds → x ∈ U' := fun x hx hnx => by
        by_cases hxd : x = d
        · subst hxd; exact Finset.mem_insert_self _ _
        · exact Finset.mem_insert_of_mem (hmiss x hx (by simp [List.mem_cons, hxd, hnx]))
      rw [hS'] at hchk
      exact ih U' (mergeIvs ivs (ivs.map (fun (a, bb) => (a + d, bb + d)))) hpw.2
        (fun y hy => hds y (List.mem_cons_of_mem d hy)) hU'_sub hU'_lt hcov' hmiss' hivs' hchk

-- Wait: fix the 2-line sorry in `checkDenseLoop_sound` (`hy_in_U'`)!
-- Also write `checkSeedFull_sound`, `denseSeed_mul_mem`, `denseSeed_to_seedOk`, `seedOk_mul_prime_pow`,
-- `checkBaseExt_sound`, `checkCert_sound`, `prove_H2`.

lemma foldl_fac_prod_sigma : ∀ (l : List (ℕ × ℕ)) (prev : ℕ),
    checkFacLoop prev l = true →
    let b := l.foldl (fun acc pe => acc * pe.1 ^ pe.2) 1
    let sig := l.foldl (fun acc pe => acc * sigPP pe.1 pe.2) 1
    0 < b ∧ sigma 1 b = sig ∧
    (∀ q ∈ b.primeFactors, ∃ pe ∈ l, pe.1 = q) ∧
    (l ≠ [] → 1 < b) := by
  have hgen : ∀ (l : List (ℕ × ℕ)) (prev b0 s0 : ℕ),
      checkFacLoop prev l = true → 0 < b0 → sigma 1 b0 = s0 →
      (∀ q ∈ b0.primeFactors, q ≤ prev) →
      let b := l.foldl (fun acc pe => acc * pe.1 ^ pe.2) b0
      let sig := l.foldl (fun acc pe => acc * sigPP pe.1 pe.2) s0
      0 < b ∧ sigma 1 b = sig ∧
      (∀ q ∈ b.primeFactors, (q ∈ b0.primeFactors ∨ ∃ pe ∈ l, pe.1 = q)) := by
    intro l
    induction l with
    | nil =>
      intro prev b0 s0 _ hb0 hs0 _
      exact ⟨hb0, hs0, fun q hq => Or.inl hq⟩
    | cons pe rest ih =>
      intro prev b0 s0 hchk hb0 hs0 hpf0
      have hspec := checkFacLoop_sound prev (pe :: rest) hchk
      have hpe := hspec.2 pe List.mem_cons_self
      have hchk_r : checkFacLoop pe.1 rest = true := by
        unfold checkFacLoop at hchk; simp only [Bool.and_eq_true] at hchk; exact hchk.2
      have hpe_pos : 0 < pe.1 ^ pe.2 := Nat.pow_pos hpe.2.1.pos
      have hb1 : 0 < b0 * pe.1 ^ pe.2 := Nat.mul_pos hb0 hpe_pos
      have hcop : Nat.Coprime b0 (pe.1 ^ pe.2) := by
        refine (hpe.2.1.coprime_iff_not_dvd.mpr fun hdvd => ?_).symm.pow_right pe.2
        have := hpf0 pe.1 (Nat.mem_primeFactors.mpr ⟨hpe.2.1, hdvd, hb0.ne'⟩)
        omega
      have hs1 : sigma 1 (b0 * pe.1 ^ pe.2) = s0 * sigPP pe.1 pe.2 := by
        rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop, hs0, sigma_one_prime_pow hpe.2.1]
      have hpf1 : ∀ q ∈ (b0 * pe.1 ^ pe.2).primeFactors, q ≤ pe.1 := by
        intro q hq
        rw [Nat.primeFactors_mul hb0.ne' hpe_pos.ne', Finset.mem_union] at hq
        rcases hq with hq1 | hq2
        · exact le_trans (hpf0 q hq1) (Nat.le_of_lt hpe.1)
        · have hqp := Nat.prime_of_mem_primeFactors hq2
          have hqd := hpe.2.1.dvd_iff_eq hqp.ne_one |>.mp (hqp.dvd_of_dvd_pow (Nat.dvd_of_mem_primeFactors hq2))
          exact le_of_eq hqd.symm
      have ih_res := ih pe.1 (b0 * pe.1 ^ pe.2) (s0 * sigPP pe.1 pe.2) hchk_r hb1 hs1 hpf1
      refine ⟨ih_res.1, ih_res.2.1, fun q hq => ?_⟩
      rcases ih_res.2.2 q hq with hq1 | ⟨x, hx, hxq⟩
      · rw [Nat.primeFactors_mul hb0.ne' hpe_pos.ne', Finset.mem_union] at hq1
        rcases hq1 with hq1' | hq2'
        · exact Or.inl hq1'
        · right; refine ⟨pe, List.mem_cons_self, ?_⟩
          have hqp := Nat.prime_of_mem_primeFactors hq2'
          exact hpe.2.1.dvd_iff_eq hqp.ne_one |>.mp (hqp.dvd_of_dvd_pow (Nat.dvd_of_mem_primeFactors hq2'))
      · right; exact ⟨x, List.mem_cons_of_mem pe hx, hxq⟩
  intro l prev hchk
  have h := hgen l prev 1 1 hchk Nat.one_pos (by simp) (by simp)
  refine ⟨h.1, h.2.1, fun q hq => ?_, fun hne => ?_⟩
  · rcases h.2.2 q hq with h1 | h2
    · simp at h1
    · exact h2
  · cases l with
    | nil => exact absurd rfl hne
    | cons pe rest =>
      have hspec := checkFacLoop_sound prev (pe :: rest) hchk
      have hpe := hspec.2 pe List.mem_cons_self
      have h1 : pe.1 ^ pe.2 ∣ (pe :: rest).foldl (fun acc x => acc * x.1 ^ x.2) 1 := by
        rw [foldl_mul_eq, one_mul, List.map_cons, List.prod_cons]
        exact dvd_mul_right _ _
      have hgt1 : 1 < pe.1 ^ pe.2 := Nat.one_lt_pow (by omega) hpe.2.1.one_lt
      exact lt_of_lt_of_le hgt1 (Nat.le_of_dvd h.1 h1)

def SeedValid (sd : Seed) : Prop :=
  sd.fac ≠ [] ∧
  checkFacLoop 2 sd.fac = true ∧
  (let b₀ := sd.fac.foldl (fun acc pe => acc * pe.1 ^ pe.2) 1
   sigma 1 b₀ < 2 * b₀ ∧
   PropSum b₀ = (sd.p0 : ℤ) ∧
   DenseSeed b₀ b₀ sd.cutB ∧
   (∀ r ∈ sd.freeP, r ∈ sd.fac.map (·.1) ∧
     (∀ w, 0 < w → w ≤ sd.cutB → (∀ q ∈ w.primeFactors, q ∈ sd.fac.map (·.1)) →
       sd.cutB < r * w → r * w + 127 ≤ ∑ x ∈ b₀.properDivisors.filter (· < r * w), x) ∧
     (let c₀Fac := sd.fac.filter (fun (p, _) => p != r)
      let c₀ := c₀Fac.foldl (fun acc pe => acc * pe.1 ^ pe.2) 1
      c₀ ∣ b₀ ∧ ¬ r ∣ c₀ ∧
      (2 * b₀ - sigma 1 b₀) + 127 ≤ r * ∑ t ∈ c₀.divisors.filter (r < ·), (b₀ / t))))

lemma checkSeedFull_sound (sd : Seed) (hsd : checkSeedFull sd = true) : SeedValid sd := by
  unfold checkSeedFull at hsd
  have hne_fac : sd.fac ≠ [] := fun h => by simp [h] at hsd
  have hcut_pos : sd.cutB ≠ 0 := fun h => by simp [h] at hsd
  have hfac_chk : checkFacLoop 2 sd.fac = true := by
    by_contra h
    have hf : checkFacLoop 2 sd.fac = false := Bool.eq_false_iff.mpr h
    rw [if_pos (by simp [hf])] at hsd
    exact Bool.noConfusion hsd
  rw [if_neg (by simp [hne_fac, hcut_pos, hfac_chk])] at hsd
  obtain ⟨hb0_pos, hb0_sig, hb0_pf, hb0_gt1⟩ := foldl_fac_prod_sigma sd.fac 2 hfac_chk
  set b₀ := sd.fac.foldl (fun acc pe => acc * pe.1 ^ pe.2) 1
  set sig := sd.fac.foldl (fun acc pe => acc * sigPP pe.1 pe.2) 1
  have hsig_ge : b₀ ≤ sig := by
    by_contra hlt
    rw [if_pos (Nat.lt_of_not_le hlt)] at hsd
    exact Bool.noConfusion hsd
  rw [if_neg (Nat.not_lt_of_ge hsig_ge)] at hsd
  dsimp only at hsd
  have hp_good : ¬ (sig - b₀ != sd.p0 || decide (sig - b₀ < 2392) || decide (b₀ + 127 > 4 * (sig - b₀)) || decide (2 * b₀ ≤ sig)) = true := by
    intro h
    rw [if_pos h] at hsd
    exact Bool.noConfusion hsd
  rw [if_neg hp_good] at hsd
  simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, not_lt] at hp_good
  have hp_eq : sig - b₀ = sd.p0 := by
    by_contra hne
    exact hp_good.1.1.1 (bne_iff_ne.mpr hne)
  have hP2392 : 2392 ≤ sig - b₀ := hp_good.1.1.2
  have hb127 : b₀ + 127 ≤ 4 * (sig - b₀) := hp_good.1.2
  have hdef : sig < 2 * b₀ := Nat.lt_of_not_le hp_good.2
  set raw := (allDivsOfFac sd.fac).filter (· < b₀)
  have hraw_len : raw.length ≤ 1024 := by
    by_contra hgt
    rw [if_pos (Nat.lt_of_not_le hgt)] at hsd
    exact Bool.noConfusion hsd
  rw [if_neg (Nat.not_lt_of_ge hraw_len)] at hsd
  obtain ⟨hpdivs_pw, hpdivs_perm⟩ := fastSort10_spec hraw_len
  obtain ⟨_, hall_nd, hall_iff⟩ := allDivsOfFac_spec sd.fac 2 hfac_chk
  have hraw_nd : raw.Nodup := hall_nd.filter _
  have hpdivs_nd : (fastSort10 raw).Nodup := hpdivs_perm.nodup_iff.mpr hraw_nd
  have hpdivs_lt : (fastSort10 raw).Pairwise (· < ·) := pairwise_lt_of_le_nodup hpdivs_pw hpdivs_nd
  have hpdivs_mem : ∀ d, d ∈ fastSort10 raw ↔ d ∈ b₀.properDivisors := by
    intro d
    rw [hpdivs_perm.mem_iff, List.mem_filter, hall_iff, Nat.mem_divisors, Nat.mem_properDivisors, decide_eq_true_eq]
    exact ⟨fun ⟨⟨hd, _⟩, hlt⟩ => ⟨hd, hlt⟩, fun ⟨hd, hlt⟩ => ⟨⟨hd, hb0_pos.ne'⟩, hlt⟩⟩
  have hpdivs_finset : (fastSort10 raw).toFinset = b₀.properDivisors := by
    ext d; rw [List.mem_toFinset, hpdivs_mem]
  have hd_chk : checkDenseLoop sd.cutB 0 [(0, 0)] (fastSort10 raw) = true := by
    by_contra h
    have hf : (!checkDenseLoop sd.cutB 0 [(0, 0)] (fastSort10 raw)) = true := by
      simp [Bool.eq_false_iff.mpr h]
    rw [if_pos hf] at hsd
    exact Bool.noConfusion hsd
  rw [if_neg (by simp [hd_chk])] at hsd
  have hdense_res := checkDenseLoop_sound b₀ sd.cutB (fastSort10 raw) ∅ [(0, 0)] hpdivs_lt
    (fun d hd => (hpdivs_mem d).mp hd) (Finset.empty_subset _) (by simp)
    (fun d hd x hx hxd => Or.inr ((hpdivs_mem x).mpr hx))
    (fun x hx hnx => absurd ((hpdivs_mem x).mpr hx) hnx)
    (fun a b y hm => by
      rw [List.mem_singleton] at hm; injection hm with ha hb; subst ha; subst hb
      exact ⟨le_rfl, fun hy1 hy2 => ⟨∅, Finset.empty_subset _, by simp; omega⟩⟩)
    (by simpa using hd_chk)
  have hPropSum_b0 : PropSum b₀ = (sd.p0 : ℤ) := by
    have hsig_eq := sigma_one_eq_sum_proper_add b₀
    rw [hb0_sig] at hsig_eq
    rw [propSum_eq_nat]
    omega
  have hDenseSeed : DenseSeed b₀ b₀ sd.cutB := by
    refine ⟨hb0_gt1 hne_fac, dvd_rfl, ?_, ?_, hdense_res.1, hdense_res.2⟩
    · rw [hPropSum_b0]; omega
    · rw [hPropSum_b0]; omega
  refine ⟨hne_fac, hfac_chk, hb0_sig.symm ▸ hdef, hPropSum_b0, hDenseSeed, ?_⟩
  intro r hr
  have hr_all : (sd.fac.map (·.1)).contains r = true ∧
      check2a (fastSort10 raw) (allSmoothUpTo (sd.fac.map (·.1)) sd.cutB) sd.cutB r = true ∧
      check2b sd.fac b₀ (2 * b₀ - sig) r = true := by
    by_cases hfe : sd.freeP.isEmpty = true
    · rw [List.isEmpty_iff] at hfe; rw [hfe] at hr; simp at hr
    · rw [if_neg hfe, List.all_eq_true] at hsd
      have h := hsd r hr
      simp only [Bool.and_eq_true] at h
      exact ⟨h.1.1, h.1.2, h.2⟩
  have hr_mem : r ∈ sd.fac.map (·.1) := List.contains_iff_mem.mp hr_all.1
  have hprimes_p : ∀ p ∈ sd.fac.map (·.1), p.Prime := fun p hp => by
    rw [List.mem_map] at hp; obtain ⟨pe, hpe, rfl⟩ := hp
    exact ((checkFacLoop_sound 2 sd.fac hfac_chk).2 pe hpe).2.1
  refine ⟨hr_mem, ?_, ?_⟩
  · intro w hw0 hwle hwpf hgt
    have hw_in := allSmoothUpTo_complete (sd.fac.map (·.1)) sd.cutB hprimes_p w hw0 hwle hwpf
    have h2a := hr_all.2.1
    unfold check2a at h2a
    rw [List.all_eq_true] at h2a
    have hw_ok := h2a w hw_in
    dsimp only at hw_ok
    rw [if_neg (by omega), decide_eq_true_eq] at hw_ok
    have hfold_sum : ∀ (l : List ℕ) (init : ℕ),
        l.foldl (fun acc x => if x < r * w then acc + x else acc) init =
        init + (l.filter (· < r * w)).sum := fun l => by
      induction l with
      | nil => simp
      | cons a t ih =>
        intro init
        by_cases ha : a < r * w <;> simp [ha, ih]; omega
    rw [hfold_sum (fastSort10 raw) 0, zero_add] at hw_ok
    have hsum_eq : ((fastSort10 raw).filter (· < r * w)).sum = ∑ x ∈ b₀.properDivisors.filter (· < r * w), x := by
      have h1 := List.sum_toFinset id (hpdivs_nd.filter (· < r * w))
      simp only [List.map_id, id_eq] at h1
      rw [← h1]
      congr 1; ext x; simp [← hpdivs_finset]
    rw [← hsum_eq]
    exact hw_ok
  · set c₀Fac := sd.fac.filter (fun (p, _) => p != r)
    set c₀ := c₀Fac.foldl (fun acc pe => acc * pe.1 ^ pe.2) 1
    have hc0_chk := checkFacLoop_filter (fun (p, _) => p != r) 2 sd.fac hfac_chk
    obtain ⟨hc0_pos, _, hc0_pf, _⟩ := foldl_fac_prod_sigma c₀Fac 2 hc0_chk
    have hc0_dvd : c₀ ∣ b₀ := by
      dsimp [c₀, b₀]
      rw [foldl_mul_eq, foldl_mul_eq, one_mul, one_mul]
      have hsub : ∀ l : List (ℕ × ℕ),
          ((l.filter (fun (p, _) => p != r)).map (fun pe => pe.1 ^ pe.2)).prod ∣
          (l.map (fun pe => pe.1 ^ pe.2)).prod := fun l => by
        induction l with
        | nil => simp
        | cons x xs ih =>
          rw [List.filter_cons]
          split_ifs
          · simp only [List.map_cons, List.prod_cons]; exact mul_dvd_mul_left _ ih
          · simp only [List.map_cons, List.prod_cons]; exact dvd_mul_of_dvd_right ih _
      exact hsub sd.fac
    have hnr_c0 : ¬ r ∣ c₀ := by
      intro hdvd
      have hrp := hprimes_p r hr_mem
      obtain ⟨pe, hpe_mem, hpe_r⟩ := hc0_pf r (Nat.mem_primeFactors.mpr ⟨hrp, hdvd, hc0_pos.ne'⟩)
      rw [List.mem_filter] at hpe_mem
      have : (pe.1 != r) = true := hpe_mem.2
      simp [hpe_r] at this
    refine ⟨hc0_dvd, hnr_c0, ?_⟩
    obtain ⟨_, hc0_nd, hc0_iff⟩ := allDivsOfFac_spec c₀Fac 2 hc0_chk
    have h2b := hr_all.2.2
    unfold check2b at h2b
    dsimp only at h2b
    rw [decide_eq_true_eq] at h2b
    have hfold_b : ∀ (l : List ℕ) (init : ℕ),
        l.foldl (fun acc t => if r < t then acc + b₀ / t else acc) init =
        init + ((l.filter (r < ·)).map (b₀ / ·)).sum := fun l => by
      induction l with
      | nil => simp
      | cons a t ih =>
        intro init
        by_cases ha : r < a <;> simp [ha, ih]; omega
    rw [hfold_b (allDivsOfFac c₀Fac) 0, zero_add] at h2b
    have hsum_eq : (((allDivsOfFac c₀Fac).filter (r < ·)).map (b₀ / ·)).sum =
        ∑ t ∈ c₀.divisors.filter (r < ·), b₀ / t := by
      have hc0_f : (allDivsOfFac c₀Fac).toFinset = c₀.divisors := by
        ext d; rw [List.mem_toFinset, hc0_iff]
      have hfilt_nd : ((allDivsOfFac c₀Fac).filter (r < ·)).Nodup := hc0_nd.filter _
      have hfilt_eq : ((allDivsOfFac c₀Fac).filter (r < ·)).toFinset = c₀.divisors.filter (r < ·) := by
        ext d; simp [← hc0_f]
      rw [← hfilt_eq, List.sum_toFinset (b₀ / ·) hfilt_nd]
    rw [hsum_eq, ← hb0_sig] at h2b
    exact h2b


-- =====================================================================
-- denseSeed_mul_mem, denseSeed_to_seedOk, seedOk_mul_prime_pow
-- =====================================================================

lemma properDivisors_subset_mul_right {a b : ℕ} (_ha : 0 < a) (hb : 1 < b) :
    a.properDivisors ⊆ (a * b).properDivisors := by
  intro d hd
  obtain ⟨hda, hlt⟩ := Nat.mem_properDivisors.mp hd
  refine Nat.mem_properDivisors.mpr ⟨hda.trans (dvd_mul_right _ _), ?_⟩
  exact lt_of_lt_of_le hlt (Nat.le_mul_of_pos_right a (by omega))

lemma denseSeed_mul_mem {sd : Seed} (hsv : SeedValid sd) {n r : ℕ}
    (hdn : DenseSeed (sd.fac.foldl (fun acc pe => acc * pe.1 ^ pe.2) 1) n sd.cutB)
    (hnpf : ∀ q ∈ n.primeFactors, q ∈ sd.fac.map (·.1))
    (hr_free : r ∈ sd.freeP) (hr_prime : r.Prime) :
    DenseSeed (sd.fac.foldl (fun acc pe => acc * pe.1 ^ pe.2) 1) (n * r) sd.cutB := by
  set b₀ := sd.fac.foldl (fun acc pe => acc * pe.1 ^ pe.2) 1
  have hn_pos : 0 < n := denseSeed_pos hdn
  obtain ⟨hb0_gt1, hb0_dvd, hP_ge, h4P, hU0, hdense⟩ := hdn
  obtain ⟨_, _, hsig_lt_2b0, _, hDenseB0, hfree_all⟩ := hsv
  obtain ⟨hr_mem, h2a, hc0_dvd, hnr_c0, h2b⟩ := hfree_all r hr_free
  set c₀ := (sd.fac.filter (fun (p, _) => p != r)).foldl (fun acc pe => acc * pe.1 ^ pe.2) 1
  have hb0_pos : 0 < b₀ := by omega
  have hr_gt1 : 1 < r := hr_prime.one_lt
  have hbnr : b₀ ∣ n * r := hb0_dvd.trans (dvd_mul_right _ _)
  have hk_pos : 0 < n / b₀ := Nat.div_pos (Nat.le_of_dvd hn_pos hb0_dvd) hb0_pos
  have hkn : (n / b₀) * b₀ = n := Nat.div_mul_cancel hb0_dvd
  have hP_mono : PropSum n ≤ PropSum (n * r) := by
    rw [propSum_eq_nat, propSum_eq_nat]
    exact_mod_cast Finset.sum_le_sum_of_subset (properDivisors_subset_mul_right hn_pos hr_gt1)
  have h4P_nr : ((n * r : ℕ) : ℤ) + 127 ≤ 4 * PropSum (n * r) := by
    have hmul := propSum_mul_le hb0_pos hbnr
    have hdiv_eq : (n * r) / b₀ = (n / b₀) * r := by
      calc (n * r) / b₀ = ((n / b₀) * b₀ * r) / b₀ := by rw [hkn]
        _ = (b₀ * ((n / b₀) * r)) / b₀ := by ring_nf
        _ = (n / b₀) * r := Nat.mul_div_cancel_left _ hb0_pos
    rw [hdiv_eq] at hmul
    have hb0_4P : (b₀ : ℤ) + 127 ≤ 4 * PropSum b₀ := hDenseB0.2.2.2.1
    have hkr_pos : (1 : ℤ) ≤ ((n / b₀ * r : ℕ) : ℤ) := by
      have : 1 ≤ (n / b₀) * r := Nat.mul_pos hk_pos hr_prime.pos
      exact_mod_cast this
    have hn_eq_z : ((n * r : ℕ) : ℤ) = ((n / b₀ * r : ℕ) : ℤ) * (b₀ : ℤ) := by
      push_cast
      have : (n * r) = ((n / b₀) * r) * b₀ := by
        calc n * r = ((n / b₀) * b₀) * r := by rw [hkn]
          _ = ((n / b₀) * r) * b₀ := by ring
      exact_mod_cast this
    nlinarith
  refine ⟨hb0_gt1, hbnr, le_trans hP_ge hP_mono, h4P_nr, hU0, ?_⟩
  intro d hd_mem hBd
  obtain ⟨hd_dvd, hd_lt⟩ := Nat.mem_properDivisors.mp hd_mem
  have hd_pos : 0 < d := Nat.pos_of_dvd_of_pos hd_dvd (Nat.mul_pos hn_pos hr_prime.pos)
  set a := n.factorization r
  by_cases hdiv_pow : r ^ (a + 1) ∣ d
  · set z := d / r
    have hdrz : d = r * z := (Nat.mul_div_cancel' (dvd_trans (by rw [pow_succ]; exact dvd_mul_left _ _) hdiv_pow)).symm
    have hz_dvd : z ∣ n := by
      rw [hdrz] at hd_dvd
      exact Nat.dvd_of_mul_dvd_mul_left hr_prime.pos (by rwa [mul_comm r n])
    have hz_lt : z < n := by
      rw [hdrz, mul_comm n r] at hd_lt
      exact Nat.lt_of_mul_lt_mul_left hd_lt
    have hz_mem : z ∈ n.properDivisors := Nat.mem_properDivisors.mpr ⟨hz_dvd, hz_lt⟩
    have hz_pos : 0 < z := Nat.pos_of_dvd_of_pos hz_dvd hn_pos
    by_cases hzB : z ≤ sd.cutB
    · have hz_pf : ∀ q ∈ z.primeFactors, q ∈ sd.fac.map (·.1) := fun q hq => by
        have hqp := Nat.prime_of_mem_primeFactors hq
        have hqn : q ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨hqp, (Nat.dvd_of_mem_primeFactors hq).trans hz_dvd, hn_pos.ne'⟩
        exact hnpf q hqn
      have h2a_res := h2a z hz_pos hzB hz_pf (by rwa [← hdrz])
      rw [← hdrz] at h2a_res
      have hb0_sub : b₀.properDivisors.filter (· < d) ⊆ (n * r).properDivisors.filter (· < d) := by
        intro x hx
        rw [Finset.mem_filter] at hx ⊢
        obtain ⟨hx1, hx2⟩ := Nat.mem_properDivisors.mp hx.1
        refine ⟨Nat.mem_properDivisors.mpr ⟨hx1.trans hbnr, ?_⟩, hx.2⟩
        have hb0_le_n : b₀ ≤ n := Nat.le_of_dvd hn_pos hb0_dvd
        have : n < n * r := lt_mul_of_one_lt_right hn_pos hr_gt1
        omega
      exact le_trans h2a_res (Finset.sum_le_sum_of_subset hb0_sub)
    · have hz_gt : sd.cutB < z := Nat.lt_of_not_le hzB
      have hzd := hdense z hz_mem hz_gt
      have hsub_img : (n.properDivisors.filter (· < z)).image (r * ·) ⊆ (n * r).properDivisors.filter (· < d) := by
        intro y hy
        rw [Finset.mem_image] at hy
        obtain ⟨x, hx, rfl⟩ := hy
        rw [Finset.mem_filter] at hx ⊢
        obtain ⟨hx1, hx2⟩ := Nat.mem_properDivisors.mp hx.1
        refine ⟨Nat.mem_properDivisors.mpr ⟨mul_dvd_mul_left r hx1 |>.trans (by rw [mul_comm n r]), ?_⟩, ?_⟩
        · rw [mul_comm n r]; exact Nat.mul_lt_mul_of_pos_left hx2 hr_prime.pos
        · rw [hdrz]; exact Nat.mul_lt_mul_of_pos_left hx.2 hr_prime.pos
      have hinj : Function.Injective (r * ·) := fun x y h => Nat.eq_of_mul_eq_mul_left hr_prime.pos h
      have hsum_img : ∑ x ∈ n.properDivisors.filter (· < z), r * x ≤ ∑ y ∈ (n * r).properDivisors.filter (· < d), y := by
        have him : ∑ y ∈ (n.properDivisors.filter (· < z)).image (r * ·), y = ∑ x ∈ n.properDivisors.filter (· < z), r * x :=
          Finset.sum_image (fun x _ y _ h => hinj h)
        calc ∑ x ∈ n.properDivisors.filter (· < z), r * x
            = ∑ y ∈ (n.properDivisors.filter (· < z)).image (r * ·), y := him.symm
          _ ≤ ∑ y ∈ (n * r).properDivisors.filter (· < d), y := Finset.sum_le_sum_of_subset hsub_img
      rw [← Finset.mul_sum] at hsum_img
      have hrz : r * (z + 127) ≤ r * ∑ x ∈ n.properDivisors.filter (· < z), x := Nat.mul_le_mul_left r hzd
      nlinarith
  · -- Case ¬ r^(a+1) ∣ d, so d ∣ n
    have hd_dvd_n : d ∣ n := by
      rw [← Nat.factorization_le_iff_dvd hd_pos.ne' hn_pos.ne']
      intro q
      have hdnr := (Nat.factorization_le_iff_dvd hd_pos.ne' (Nat.mul_pos hn_pos hr_prime.pos).ne').mpr hd_dvd q
      rw [Nat.factorization_mul hn_pos.ne' hr_prime.pos.ne', Finsupp.coe_add, Pi.add_apply, hr_prime.factorization] at hdnr
      by_cases hqr : q = r
      · subst hqr
        by_contra hgt
        have hle : a + 1 ≤ d.factorization q := by omega
        exact hdiv_pow ((hr_prime.pow_dvd_iff_le_factorization hd_pos.ne').mpr hle)
      · rw [Finsupp.single_eq_of_ne hqr, add_zero] at hdnr
        exact hdnr
    by_cases hdn_eq : d = n
    · subst d
      have hn_sub : n.properDivisors ⊆ (n * r).properDivisors.filter (· < n) := by
        intro x hx
        rw [Finset.mem_filter]
        obtain ⟨_, hx2⟩ := Nat.mem_properDivisors.mp hx
        exact ⟨properDivisors_subset_mul_right hn_pos hr_gt1 hx, hx2⟩
      set T := c₀.divisors.filter (r < ·)
      let f := fun t => r * (n / t)
      have hf_mem : ∀ t ∈ T, f t ∈ (n * r).properDivisors.filter (· < n) := by
        intro t ht
        rw [Finset.mem_filter] at ht ⊢
        obtain ⟨ht_dvd, _⟩ := Nat.mem_divisors.mp ht.1
        have htn : t ∣ n := ht_dvd.trans (hc0_dvd.trans hb0_dvd)
        have ht_pos : 0 < t := Nat.pos_of_dvd_of_pos htn hn_pos
        have hnt_dvd : n / t ∣ n := Nat.div_dvd_of_dvd htn
        have hf_lt : f t < n := by
          dsimp [f]
          calc r * (n / t) < t * (n / t) := Nat.mul_lt_mul_of_pos_right ht.2 (Nat.div_pos (Nat.le_of_dvd hn_pos htn) ht_pos)
            _ = n := Nat.mul_div_cancel' htn
        have hf_dvd : f t ∣ n * r := by
          dsimp [f]; rw [mul_comm n r]; exact mul_dvd_mul_left r hnt_dvd
        have hnnr : n < n * r := lt_mul_of_one_lt_right hn_pos hr_gt1
        exact ⟨Nat.mem_properDivisors.mpr ⟨hf_dvd, lt_trans hf_lt hnnr⟩, hf_lt⟩
      have hf_inj : Set.InjOn f T := by
        intro t₁ ht₁ t₂ ht₂ heq
        rw [Finset.mem_coe, Finset.mem_filter] at ht₁ ht₂
        have ht1n : t₁ ∣ n := (Nat.mem_divisors.mp ht₁.1).1.trans (hc0_dvd.trans hb0_dvd)
        have ht2n : t₂ ∣ n := (Nat.mem_divisors.mp ht₂.1).1.trans (hc0_dvd.trans hb0_dvd)
        have hf_pos : 0 < f t₁ := Nat.mul_pos hr_prime.pos (Nat.div_pos (Nat.le_of_dvd hn_pos ht1n) (Nat.pos_of_dvd_of_pos ht1n hn_pos))
        have h1 : f t₁ * t₁ = r * n := by dsimp [f]; rw [mul_assoc, Nat.div_mul_cancel ht1n]
        have h2 : f t₂ * t₂ = r * n := by dsimp [f]; rw [mul_assoc, Nat.div_mul_cancel ht2n]
        rw [← heq] at h2
        exact Nat.eq_of_mul_eq_mul_left hf_pos (h1.trans h2.symm)
      have hdisj : Disjoint n.properDivisors (T.image f) := by
        rw [Finset.disjoint_left]
        intro y hy1 hy2
        rw [Finset.mem_image] at hy2
        obtain ⟨t, ht, rfl⟩ := hy2
        rw [Finset.mem_filter] at ht
        have htc0 : t ∣ c₀ := (Nat.mem_divisors.mp ht.1).1
        have htn : t ∣ n := htc0.trans (hc0_dvd.trans hb0_dvd)
        have hy_dvd : f t ∣ n := (Nat.mem_properDivisors.mp hy1).1
        obtain ⟨q, hq⟩ := hy_dvd
        have hft_pos : 0 < f t := Nat.mul_pos hr_prime.pos (Nat.div_pos (Nat.le_of_dvd hn_pos htn) (Nat.pos_of_dvd_of_pos htn hn_pos))
        have hprod : f t * t = r * (f t * q) := by
          calc f t * t = r * n := by dsimp [f]; rw [mul_assoc, Nat.div_mul_cancel htn]
            _ = r * (f t * q) := by rw [hq]
        have ht_eq : t = r * q := Nat.eq_of_mul_eq_mul_left hft_pos (by rwa [mul_left_comm] at hprod)
        exact hnr_c0 (dvd_trans ⟨q, ht_eq⟩ htc0)
      have hsum_split : (∑ x ∈ n.properDivisors, x) + ∑ y ∈ T.image f, y ≤
          ∑ x ∈ (n * r).properDivisors.filter (· < n), x := by
        rw [← Finset.sum_union hdisj]
        exact Finset.sum_le_sum_of_subset (Finset.union_subset hn_sub (Finset.image_subset_iff.mpr hf_mem))
      have hsum_img : ∑ y ∈ T.image f, y = (n / b₀) * (r * ∑ t ∈ T, (b₀ / t)) := by
        rw [Finset.sum_image (fun x hx y hy h => hf_inj hx hy h)]
        have hterm : ∀ t ∈ T, f t = (n / b₀) * (r * (b₀ / t)) := fun t ht => by
          rw [Finset.mem_filter] at ht
          have htb : t ∣ b₀ := (Nat.mem_divisors.mp ht.1).1.trans hc0_dvd
          have hnt : n / t = (n / b₀) * (b₀ / t) := by
            have h1 : n = ((n / b₀) * (b₀ / t)) * t := by
              rw [mul_assoc, Nat.div_mul_cancel htb, hkn]
            have ht_pos : 0 < t := Nat.pos_of_dvd_of_pos htb hb0_pos
            conv_lhs => rw [h1]
            exact Nat.mul_div_cancel _ ht_pos
          dsimp [f]; rw [hnt]; ring
        rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]; congr 1; rw [← Finset.mul_sum]
      have hPn : (n / b₀ : ℤ) * PropSum b₀ ≤ PropSum n := propSum_mul_le hb0_pos hb0_dvd
      have hsig_b0 : sigma 1 b₀ = (∑ x ∈ b₀.properDivisors, x) + b₀ := sigma_one_eq_sum_proper_add b₀
      have hPn_nat : (n / b₀) * (∑ x ∈ b₀.properDivisors, x) ≤ ∑ x ∈ n.properDivisors, x := by
        rw [propSum_eq_nat, propSum_eq_nat] at hPn
        exact_mod_cast hPn
      have hsig_lt' : sigma 1 b₀ < 2 * b₀ := hsig_lt_2b0
      have hsum_b0_eq : (∑ x ∈ b₀.properDivisors, x) + (2 * b₀ - sigma 1 b₀) = b₀ := by omega
      have h_ge : n + 127 ≤ (∑ x ∈ n.properDivisors, x) + ∑ y ∈ T.image f, y := by
        rw [hsum_img]
        have h1 : (n / b₀) * (b₀ + 127) ≤ (∑ x ∈ n.properDivisors, x) + (n / b₀) * (r * ∑ t ∈ T, b₀ / t) := by
          calc (n / b₀) * (b₀ + 127)
              = (n / b₀) * ((∑ x ∈ b₀.properDivisors, x) + (2 * b₀ - sigma 1 b₀) + 127) := by
                conv_lhs => rhs; rw [← hsum_b0_eq]
            _ = (n / b₀) * (∑ x ∈ b₀.properDivisors, x) + (n / b₀) * (2 * b₀ - sigma 1 b₀ + 127) := by ring
            _ ≤ (∑ x ∈ n.properDivisors, x) + (n / b₀) * (r * ∑ t ∈ T, b₀ / t) :=
                add_le_add hPn_nat (Nat.mul_le_mul_left _ h2b)
        have h2 : n + 127 ≤ (n / b₀) * (b₀ + 127) := by
          rw [mul_add, hkn]
          linarith [Nat.le_mul_of_pos_left 127 hk_pos]
        exact le_trans h2 h1
      exact le_trans h_ge hsum_split
    · have hd_lt_n : d < n := lt_of_le_of_ne (Nat.le_of_dvd hn_pos hd_dvd_n) hdn_eq
      have hd_mem_n : d ∈ n.properDivisors := Nat.mem_properDivisors.mpr ⟨hd_dvd_n, hd_lt_n⟩
      have hsub_n : n.properDivisors.filter (· < d) ⊆ (n * r).properDivisors.filter (· < d) := by
        intro x hx
        rw [Finset.mem_filter] at hx ⊢
        exact ⟨properDivisors_subset_mul_right hn_pos hr_gt1 hx.1, hx.2⟩
      exact le_trans (hdense d hd_mem_n hBd) (Finset.sum_le_sum_of_subset hsub_n)


lemma denseSeed_to_seedOk {b₀ b B : ℕ} (hd : DenseSeed b₀ b B) : SeedOk b := by
  have hb_pos : 0 < b := denseSeed_pos hd
  obtain ⟨hb0_gt1, hb0_dvd, hP_ge, h4P, hU0, hdense⟩ := hd
  obtain ⟨h128, hB127, hcov0, hgap0⟩ := hU0
  have hb0_pos : 0 < b₀ := by omega
  have hb_gt1 : 1 < b := lt_of_lt_of_le hb0_gt1 (Nat.le_of_dvd hb_pos hb0_dvd)
  set U₀ := b₀.properDivisors.filter (· ≤ B)
  have hU0_sub : U₀ ⊆ b.properDivisors := by
    intro x hx
    rw [Finset.mem_filter] at hx
    obtain ⟨hx1, hx2⟩ := Nat.mem_properDivisors.mp hx.1
    exact Nat.mem_properDivisors.mpr ⟨hx1.trans hb0_dvd, lt_of_lt_of_le hx2 (Nat.le_of_dvd hb_pos hb0_dvd)⟩
  set L := (b.properDivisors \ U₀).sort (· ≤ ·)
  have hL_nd : L.Nodup := Finset.sort_nodup _ _
  have hL_pw : L.Pairwise (· < ·) := pairwise_lt_of_le_nodup (Finset.pairwise_sort _ _) hL_nd
  have hstep : ∀ (ds : List ℕ) (U : Finset ℕ),
      ds.Pairwise (· < ·) →
      (∀ d ∈ ds, d ∈ b.properDivisors) →
      U ⊆ b.properDivisors →
      U₀ ⊆ U →
      (∀ d ∈ ds, d ∉ U) →
      (∀ x ∈ b.properDivisors, x ∈ U ∨ x ∈ ds) →
      128 ≤ ∑ x ∈ U, x → B + 127 ≤ ∑ x ∈ U, x →
      (∀ y : ℕ, 64 ≤ y → y ≤ (∑ x ∈ U, x) - 64 → ∃ s ⊆ U, s.sum id = y) →
      (∀ k : ℕ, k < ∑ x ∈ U, x → ∃ i : ℕ, (∃ s ⊆ U, s.sum id = i) ∧ i ≤ k ∧ k < i + 6) →
      (∀ y : ℕ, 64 ≤ y → y ≤ (∑ x ∈ b.properDivisors, x) - 64 → ∃ s ⊆ b.properDivisors, s.sum id = y) ∧
      (∀ k : ℕ, k < ∑ x ∈ b.properDivisors, x → ∃ i : ℕ, (∃ s ⊆ b.properDivisors, s.sum id = i) ∧ i ≤ k ∧ k < i + 6) := by
    intro ds
    induction ds with
    | nil =>
      intro U _ _ hU_sub _ _ hpart _ _ hcov hgap
      have hU_eq : U = b.properDivisors := Finset.Subset.antisymm hU_sub (fun x hx => (hpart x hx).resolve_right (by simp))
      rw [← hU_eq]
      exact ⟨hcov, hgap⟩
    | cons d ds ih =>
      intro U hpw hds hU_sub hU0_inU hdisj hpart h128 hB hcov hgap
      rw [List.pairwise_cons] at hpw
      have hd_mem := hds d List.mem_cons_self
      have hd_not : d ∉ U := hdisj d List.mem_cons_self
      have hd_127 : d + 127 ≤ ∑ x ∈ U, x := by
        by_cases hdB : d ≤ B
        · exact le_trans (by omega) hB
        · have hB_lt : B < d := Nat.lt_of_not_le hdB
          have hsub_lt : b.properDivisors.filter (· < d) ⊆ U := by
            intro x hx
            rw [Finset.mem_filter] at hx
            rcases hpart x hx.1 with hxU | hxds
            · exact hxU
            · exfalso
              rcases List.mem_cons.mp hxds with rfl | hxds'
              · omega
              · have := hpw.1 x hxds'; omega
          exact le_trans (hdense d hd_mem hB_lt) (Finset.sum_le_sum_of_subset hsub_lt)
      set U' := insert d U
      have hS' : ∑ x ∈ U', x = (∑ x ∈ U, x) + d := by rw [Finset.sum_insert hd_not, add_comm]
      have hcov' : ∀ y : ℕ, 64 ≤ y → y ≤ (∑ x ∈ U', x) - 64 → ∃ s ⊆ U', s.sum id = y := by
        intro y hy1 hy2
        rw [hS'] at hy2
        by_cases hyS : y ≤ (∑ x ∈ U, x) - 64
        · obtain ⟨s, hs, hsum⟩ := hcov y hy1 hyS
          exact ⟨s, hs.trans (Finset.subset_insert d U), hsum⟩
        · obtain ⟨s, hs, hsum⟩ := hcov (y - d) (by omega) (by omega)
          have hd_ns : d ∉ s := fun h => hd_not (hs h)
          refine ⟨insert d s, Finset.insert_subset_insert d hs, ?_⟩
          rw [Finset.sum_insert hd_ns, id_eq, hsum]
          omega
      have hgap' : ∀ k : ℕ, k < ∑ x ∈ U', x → ∃ i : ℕ, (∃ s ⊆ U', s.sum id = i) ∧ i ≤ k ∧ k < i + 6 := by
        intro k hk
        rw [hS'] at hk
        by_cases hkS : k < ∑ x ∈ U, x
        · obtain ⟨i, ⟨s, hs, hsum⟩, hi1, hi2⟩ := hgap k hkS
          exact ⟨i, ⟨s, hs.trans (Finset.subset_insert d U), hsum⟩, hi1, hi2⟩
        · obtain ⟨j, ⟨s, hs, hsum⟩, hj1, hj2⟩ := hgap (k - d) (by omega)
          have hd_ns : d ∉ s := fun h => hd_not (hs h)
          refine ⟨j + d, ⟨insert d s, Finset.insert_subset_insert d hs, ?_⟩, by omega, by omega⟩
          rw [Finset.sum_insert hd_ns, id_eq, hsum, add_comm]
      refine ih U' hpw.2 (fun y hy => hds y (List.mem_cons_of_mem d hy))
        (Finset.insert_subset_iff.mpr ⟨hd_mem, hU_sub⟩) (hU0_inU.trans (Finset.subset_insert d U)) ?_ ?_ (by omega) (by omega) hcov' hgap'
      · intro y hy hy_in
        rw [Finset.mem_insert] at hy_in
        rcases hy_in with rfl | hyU
        · exact Nat.lt_irrefl y (hpw.1 y hy)
        · exact hdisj y (List.mem_cons_of_mem d hy) hyU
      · intro x hx
        rcases hpart x hx with hxU | hxds
        · left; exact Finset.mem_insert_of_mem hxU
        · rcases List.mem_cons.mp hxds with rfl | hxds'
          · left; exact Finset.mem_insert_self _ _
          · right; exact hxds'
  have hres := hstep L U₀ hL_pw
    (fun d hd => by rw [Finset.mem_sort, Finset.mem_sdiff] at hd; exact hd.1)
    hU0_sub Subset.rfl
    (fun d hd => by rw [Finset.mem_sort, Finset.mem_sdiff] at hd; exact hd.2)
    (fun x hx => by
      by_cases hxU : x ∈ U₀
      · left; exact hxU
      · right; rw [Finset.mem_sort, Finset.mem_sdiff]; exact ⟨hx, hxU⟩)
    h128 hB127 hcov0 hgap0
  refine ⟨hb_gt1, hP_ge, h4P, ?_, ?_⟩
  · intro y hy1 hy2
    have hy2' : y.toNat ≤ (∑ x ∈ b.properDivisors, x) - 64 := by
      rw [propSum_eq_nat] at hy2; omega
    obtain ⟨s, hs_sub, hsum⟩ := hres.1 y.toNat (by omega) hy2'
    refine ⟨s, hs_sub, ?_⟩
    have hz : (∑ x ∈ s, (x : ℤ)) = ((s.sum id : ℕ) : ℤ) := by simp
    rw [hz, hsum]; omega
  · intro k hk1 hk2
    have hk2' : k.toNat < ∑ x ∈ b.properDivisors, x := by
      rw [propSum_eq_nat] at hk2; omega
    obtain ⟨i, ⟨s, hs_sub, hsum⟩, hi1, hi2⟩ := hres.2 k.toNat hk2'
    refine ⟨(i : ℤ), ⟨s, hs_sub, ?_⟩, by omega, by omega⟩
    have hz : (∑ x ∈ s, (x : ℤ)) = ((s.sum id : ℕ) : ℤ) := by simp
    rw [hz, hsum]


lemma rep_mono {a b : ℕ} (_ha : 0 < a) (hab : a ∣ b) (hlt : a ≤ b) {x : ℤ} (hr : Rep a x) : Rep b x := by
  obtain ⟨s, hs, hsum⟩ := hr
  refine ⟨s, fun d hd => ?_, hsum⟩
  obtain ⟨hd1, hd2⟩ := Nat.mem_properDivisors.mp (hs hd)
  exact Nat.mem_properDivisors.mpr ⟨hd1.trans hab, lt_of_lt_of_le hd2 hlt⟩

lemma rep_complement {n : ℕ} {x : ℤ} (hr : Rep n x) : Rep n (PropSum n - x) := by
  obtain ⟨s, hs, hsum⟩ := hr
  refine ⟨n.properDivisors \ s, Finset.sdiff_subset, ?_⟩
  have h := Finset.sum_sdiff hs (f := fun d : ℕ => (d : ℤ))
  change (∑ d ∈ n.properDivisors \ s, (d : ℤ)) + ∑ d ∈ s, (d : ℤ) = PropSum n at h
  linarith

lemma propSum_mul_prime_pow_succ {b r j : ℕ} (_hb : 0 < b) (hr : r.Prime) (hcop : b.Coprime r) :
    PropSum (b * r ^ (j + 1)) = (b : ℤ) + PropSum b + (r : ℤ) * PropSum (b * r ^ j) := by
  have h1 := sigma_one_eq_sum_proper_add (b * r ^ (j + 1))
  have h2 := sigma_one_eq_sum_proper_add b
  have h3 := sigma_one_eq_sum_proper_add (b * r ^ j)
  have hrec : sigma 1 (b * r ^ (j + 1)) = r * sigma 1 (b * r ^ j) + sigma 1 b := by
    rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (hcop.pow_right (j + 1)),
        ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (hcop.pow_right j),
        sigma_one_prime_pow hr, sigma_one_prime_pow hr,
        sigPP_eq_geomSum r (j + 1) hr.one_lt, sigPP_eq_geomSum r j hr.one_lt]
    rw [show ∑ i ∈ range (j + 1 + 1), r ^ i = 1 + r * ∑ i ∈ range (j + 1), r ^ i by
      clear h1 h2 h3
      induction j with
      | zero => simp [sum_range_succ, pow_zero, pow_one]
      | succ k ih =>
        calc ∑ i ∈ range (k + 1 + 1 + 1), r ^ i
            = (∑ i ∈ range (k + 1 + 1), r ^ i) + r ^ (k + 1 + 1) := sum_range_succ _ _
          _ = (1 + r * ∑ i ∈ range (k + 1), r ^ i) + r ^ (k + 1 + 1) := by rw [ih]
          _ = 1 + r * ((∑ i ∈ range (k + 1), r ^ i) + r ^ (k + 1)) := by rw [pow_succ]; ring
          _ = 1 + r * ∑ i ∈ range (k + 1 + 1), r ^ i := by rw [← sum_range_succ]]
    ring
  have hnat : ∑ d ∈ (b * r ^ (j + 1)).properDivisors, d =
      b + (∑ d ∈ b.properDivisors, d) + r * ∑ d ∈ (b * r ^ j).properDivisors, d := by
    have hpow_eq : b * r ^ (j + 1) = r * (b * r ^ j) := by rw [pow_succ]; ring
    rw [h1, h2, h3] at hrec
    linarith [hrec, hpow_eq]
  rw [propSum_eq_nat, propSum_eq_nat, propSum_eq_nat, hnat]
  push_cast
  ring

lemma seedOk_mul_prime_pow {b r a : ℕ} (hs : SeedOk b)
    (hr : r.Prime) (hcop : b.Coprime r) (hr3 : 3 ≤ r) (_ha : 1 ≤ a)
    (hr_bound : 6 * (r : ℤ) ≤ PropSum b - 127) :
    SeedOk (b * r ^ a) ∧ PropSum b ≤ PropSum (b * r ^ a) := by
  obtain ⟨hb1, hP2392, hb4P, hmid, hgap⟩ := hs
  have hb_pos : 0 < b := by omega
  have hstep : ∀ j : ℕ, SeedOk (b * r ^ j) ∧ PropSum b ≤ PropSum (b * r ^ j) := by
    intro j
    induction j with
    | zero =>
      have hs0 : SeedOk b := ⟨hb1, hP2392, hb4P, hmid, hgap⟩
      simpa only [pow_zero, mul_one] using And.intro hs0 le_rfl
    | succ j ih =>
      obtain ⟨hsj, hPj⟩ := ih
      set m_j := b * r ^ j
      set m_next := b * r ^ (j + 1)
      have hm_j_pos : 0 < m_j := Nat.mul_pos hb_pos (Nat.pow_pos hr.pos)
      have hm_next_pos : 0 < m_next := Nat.mul_pos hb_pos (Nat.pow_pos hr.pos)
      have hm_next_gt1 : 1 < m_next := lt_of_lt_of_le hb1 (Nat.le_mul_of_pos_right b (Nat.pow_pos hr.pos))
      have hP_next_eq : PropSum m_next = (b : ℤ) + PropSum b + (r : ℤ) * PropSum m_j :=
        propSum_mul_prime_pow_succ hb_pos hr hcop
      have hP_next_ge : PropSum b ≤ PropSum m_next := by
        have : 0 ≤ PropSum m_j := by have := hsj.2.1; omega
        have : (0 : ℤ) ≤ b := by omega
        nlinarith
      have hb_dvd_next : b ∣ m_next := dvd_mul_of_dvd_left dvd_rfl _
      have h4P_next : (m_next : ℤ) + 127 ≤ 4 * PropSum m_next := by
        have hmul := propSum_mul_le hb_pos hb_dvd_next
        have hdiv : m_next / b = r ^ (j + 1) := Nat.mul_div_cancel_left _ hb_pos
        rw [hdiv] at hmul
        have hr_pow : (1 : ℤ) ≤ ((r ^ (j + 1) : ℕ) : ℤ) := by
          have : 1 ≤ r ^ (j + 1) := Nat.one_le_pow _ _ hr.pos
          exact_mod_cast this
        have hm_z : (m_next : ℤ) = (b : ℤ) * ((r ^ (j + 1) : ℕ) : ℤ) := by push_cast; rfl
        nlinarith
      have hlayers : ∀ i, Rep m_j i → ∀ y, Rep b y →
          Rep m_next (y + (r : ℤ) * i) ∧ Rep m_next ((b : ℤ) + y + (r : ℤ) * i) := by
        intro i hi y hy
        obtain ⟨t, ht, rfl⟩ := hi
        obtain ⟨s, hs_sub, rfl⟩ := hy
        have hbm : b ∣ m_j := dvd_mul_right _ _
        have hnr : ¬ r ∣ b := hr.coprime_iff_not_dvd.mp hcop.symm
        have hm_eq : m_next = r * m_j := by dsimp [m_next, m_j]; rw [pow_succ]; ring
        have inj : Function.Injective (r * ·) := fun x y eq => Nat.eq_of_mul_eq_mul_left hr.pos eq
        have hscaled : t.image (r * ·) ⊆ m_next.properDivisors := by
          intro x hx
          rw [Finset.mem_image] at hx
          obtain ⟨z, hz, rfl⟩ := hx
          obtain ⟨hzd, hzlt⟩ := Nat.mem_properDivisors.mp (ht hz)
          rw [hm_eq]
          exact Nat.mem_properDivisors.mpr ⟨mul_dvd_mul_left r hzd, Nat.mul_lt_mul_of_pos_left hzlt hr.pos⟩
        have hsub_b : s ⊆ m_next.properDivisors := fun x hx => by
          obtain ⟨hxd, hxlt⟩ := Nat.mem_properDivisors.mp (hs_sub hx)
          exact Nat.mem_properDivisors.mpr ⟨hxd.trans hb_dvd_next, lt_of_lt_of_le hxlt (Nat.le_of_dvd hm_next_pos hb_dvd_next)⟩
        have hdisj1 : Disjoint s (t.image (r * ·)) := by
          rw [Finset.disjoint_left]
          intro x hx hx'
          rw [Finset.mem_image] at hx'
          obtain ⟨z, _, rfl⟩ := hx'
          exact hnr ((dvd_mul_right r z).trans (Nat.mem_properDivisors.mp (hs_sub hx)).1)
        have hdisj2 : Disjoint (insert b s) (t.image (r * ·)) := by
          rw [Finset.disjoint_left]
          intro x hx hx'
          rw [Finset.mem_image] at hx'
          obtain ⟨z, _, rfl⟩ := hx'
          rw [Finset.mem_insert] at hx
          rcases hx with rfl | hx
          · exact hnr (dvd_mul_right r z)
          · exact hnr ((dvd_mul_right r z).trans (Nat.mem_properDivisors.mp (hs_sub hx)).1)
        have hb_mem : b ∈ m_next.properDivisors := Nat.mem_properDivisors.mpr
          ⟨hb_dvd_next, lt_mul_of_one_lt_right hb_pos (Nat.one_lt_pow (by omega) hr.one_lt)⟩
        have hb_not : b ∉ s := fun h => Nat.self_notMem_properDivisors (hs_sub h)
        constructor
        · refine ⟨s ∪ t.image (r * ·), Finset.union_subset hsub_b hscaled, ?_⟩
          rw [Finset.sum_union hdisj1, Finset.sum_image (fun x _ y _ eq => inj eq), Finset.mul_sum]
          simp
        · refine ⟨insert b s ∪ t.image (r * ·), Finset.union_subset (Finset.insert_subset_iff.mpr ⟨hb_mem, hsub_b⟩) hscaled, ?_⟩
          rw [Finset.sum_union hdisj2, Finset.sum_insert hb_not, Finset.sum_image (fun x _ y _ eq => inj eq), Finset.mul_sum]
          simp
      have hendA : Rep m_j (PropSum m_j) := ⟨m_j.properDivisors, Subset.rfl, rfl⟩
      have hmid_next : ∀ x : ℤ, 64 ≤ x → x ≤ PropSum m_next - 64 → Rep m_next x := by
        intro x hx1 hx2
        rw [hP_next_eq] at hx2
        have hwide : (r : ℤ) * 6 ≤ PropSum b - 2 * 64 + 1 := by omega
        have hoverlap : (b : ℤ) + 2 * 64 ≤ PropSum b + (r : ℤ) * PropSum m_j + 1 := by
          have : (3 : ℤ) * PropSum b ≤ (r : ℤ) * PropSum m_j := by
            have : 0 ≤ PropSum b := by omega
            nlinarith
          omega
        exact OMA.R_Erdos470_erdos_470_variants_odd_weird_prime_div_R1_H2_R1.OddWeirdPowerLayers.middle_next
          (A := Rep m_j) (B := Rep b) (C := Rep m_next) (P := PropSum b) (T := PropSum m_j) (b := (b : ℤ))
          (L := 64) (g := 6) (r := (r : ℤ))
          (by omega) hwide hoverlap hendA hsj.2.2.2.2 hmid hlayers x hx1 (by omega)
      have hgap_next : ∀ k : ℤ, 0 ≤ k → k < PropSum m_next → ∃ i : ℤ, Rep m_next i ∧ k - 6 < i ∧ i ≤ k := by
        intro k hk1 hk2
        have hbm_le : b ≤ m_next := Nat.le_of_dvd hm_next_pos hb_dvd_next
        by_cases hk64 : k < 64
        · obtain ⟨i, hi_rep, hi1, hi2⟩ := hgap k hk1 (by omega)
          exact ⟨i, rep_mono hb_pos hb_dvd_next hbm_le hi_rep, hi1, hi2⟩
        · by_cases hkmid : k ≤ PropSum m_next - 64
          · exact ⟨k, hmid_next k (by omega) hkmid, by omega, le_rfl⟩
          · set k₀ := PropSum b - (PropSum m_next - k)
            have hk0_nonneg : 0 ≤ k₀ := by omega
            have hk0_lt : k₀ < PropSum b := by omega
            obtain ⟨i₀, hi0_rep, hi0_1, hi0_2⟩ := hgap k₀ hk0_nonneg hk0_lt
            have hj_rep : Rep m_next (PropSum b - i₀) :=
              rep_mono hb_pos hb_dvd_next hbm_le (rep_complement hi0_rep)
            exact ⟨PropSum m_next - (PropSum b - i₀), rep_complement hj_rep, by omega, by omega⟩
      exact ⟨⟨hm_next_gt1, le_trans hP2392 hP_next_ge, h4P_next, hmid_next, hgap_next⟩, hP_next_ge⟩
  exact hstep a

-- =====================================================================
-- checkBaseExt_sound, guaranteedD2Ext_sound, guaranteedD2_sound
-- =====================================================================

lemma splitEntriesLoop_spec :
    ∀ (idx : ℕ) (entries : List Entry) (copIdxs : List Nat) (accB accC base cop : List Entry),
      (entries.map (·.p)).Pairwise (· < ·) →
      (∀ x ∈ accB, ∀ y ∈ entries, x.p < y.p) →
      (∀ x ∈ accC, ∀ y ∈ entries, x.p < y.p) →
      (accB.reverse.map (·.p)).Pairwise (· < ·) →
      (accC.reverse.map (·.p)).Pairwise (· < ·) →
      (∀ x ∈ accB, ∀ y ∈ accC, x.p ≠ y.p) →
      splitEntriesLoop idx entries copIdxs accB accC = some (base, cop) →
      (base.map (·.p)).Pairwise (· < ·) ∧ (cop.map (·.p)).Pairwise (· < ·) ∧
      (∀ x ∈ base, x ∈ accB ∨ x ∈ entries) ∧ (∀ x ∈ cop, x ∈ accC ∨ x ∈ entries) ∧
      (∀ x ∈ base, ∀ y ∈ cop, x.p ≠ y.p) ∧
      (∀ f : Entry → ℕ, (entries.map f).prod * (accB.map f).prod * (accC.map f).prod = (base.map f).prod * (cop.map f).prod) := by
  intro idx entries
  induction entries generalizing idx with
  | nil =>
    intro copIdxs accB accC base cop _ _ _ hpwB hpwC hdisj hsp
    cases copIdxs with
    | nil =>
      simp only [splitEntriesLoop] at hsp
      injection hsp with h1; injection h1 with hb hc
      subst hb; subst hc
      refine ⟨hpwB, hpwC, fun x hx => Or.inl (by simpa using hx), fun x hx => Or.inl (by simpa using hx), ?_, ?_⟩
      · intro x hx y hy; simp only [List.mem_reverse] at hx hy; exact hdisj x hx y hy
      · intro f; simp [List.map_reverse, List.prod_reverse]
    | cons _ _ => simp [splitEntriesLoop] at hsp
  | cons e es ih =>
    intro copIdxs accB accC base cop hpw hltB hltC hpwB hpwC hdisj hsp
    rw [List.map_cons, List.pairwise_cons] at hpw
    have he_ltB : ∀ x ∈ accB, x.p < e.p := fun x hx => hltB x hx e List.mem_cons_self
    have he_ltC : ∀ x ∈ accC, x.p < e.p := fun x hx => hltC x hx e List.mem_cons_self
    have hstepB : ((e :: accB).reverse.map (·.p)).Pairwise (· < ·) := by
      rw [List.reverse_cons, List.map_append, List.map_singleton, List.pairwise_append]
      refine ⟨hpwB, List.pairwise_singleton _ _, fun q hq q' hq' => ?_⟩
      rw [List.mem_map] at hq; obtain ⟨x, hx, rfl⟩ := hq
      rw [List.mem_singleton] at hq'; subst hq'
      exact he_ltB x (List.mem_reverse.mp hx)
    have hstepC : ((e :: accC).reverse.map (·.p)).Pairwise (· < ·) := by
      rw [List.reverse_cons, List.map_append, List.map_singleton, List.pairwise_append]
      refine ⟨hpwC, List.pairwise_singleton _ _, fun q hq q' hq' => ?_⟩
      rw [List.mem_map] at hq; obtain ⟨x, hx, rfl⟩ := hq
      rw [List.mem_singleton] at hq'; subst hq'
      exact he_ltC x (List.mem_reverse.mp hx)
    have hlt_es : ∀ x ∈ e :: accB, ∀ y ∈ es, x.p < y.p := fun x hx y hy => by
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact hpw.1 y.p (List.mem_map_of_mem hy)
      · exact hltB x hx' y (List.mem_cons_of_mem e hy)
    have hlt_esC : ∀ x ∈ e :: accC, ∀ y ∈ es, x.p < y.p := fun x hx y hy => by
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact hpw.1 y.p (List.mem_map_of_mem hy)
      · exact hltC x hx' y (List.mem_cons_of_mem e hy)
    unfold splitEntriesLoop at hsp
    cases copIdxs with
    | nil =>
      have res := ih (idx + 1) [] (e :: accB) accC base cop hpw.2 hlt_es
        (fun x hx y hy => hltC x hx y (List.mem_cons_of_mem e hy)) hstepB hpwC
        (fun x hx y hy => by
          rcases List.mem_cons.mp hx with rfl | hx'
          · exact (he_ltC y hy).ne'
          · exact hdisj x hx' y hy) hsp
      refine ⟨res.1, res.2.1, fun x hx => ?_, fun x hx => ?_, res.2.2.2.2.1, fun f => ?_⟩
      · rcases res.2.2.1 x hx with hx' | hx'
        · rcases List.mem_cons.mp hx' with rfl | hx''
          · right; exact List.mem_cons_self
          · left; exact hx''
        · right; exact List.mem_cons_of_mem e hx'
      · rcases res.2.2.2.1 x hx with hx' | hx'
        · left; exact hx'
        · right; exact List.mem_cons_of_mem e hx'
      · have := res.2.2.2.2.2 f
        simp only [List.map_cons, List.prod_cons] at this ⊢
        linarith
    | cons k ks =>
      dsimp only at hsp
      split_ifs at hsp with hik
      · have res := ih (idx + 1) ks accB (e :: accC) base cop hpw.2
          (fun x hx y hy => hltB x hx y (List.mem_cons_of_mem e hy)) hlt_esC hpwB hstepC
          (fun x hx y hy => by
            rcases List.mem_cons.mp hy with rfl | hy'
            · exact (he_ltB x hx).ne
            · exact hdisj x hx y hy') hsp
        refine ⟨res.1, res.2.1, fun x hx => ?_, fun x hx => ?_, res.2.2.2.2.1, fun f => ?_⟩
        · rcases res.2.2.1 x hx with hx' | hx'
          · left; exact hx'
          · right; exact List.mem_cons_of_mem e hx'
        · rcases res.2.2.2.1 x hx with hx' | hx'
          · rcases List.mem_cons.mp hx' with rfl | hx''
            · right; exact List.mem_cons_self
            · left; exact hx''
          · right; exact List.mem_cons_of_mem e hx'
        · have := res.2.2.2.2.2 f
          simp only [List.map_cons, List.prod_cons] at this ⊢
          linarith
      · have res := ih (idx + 1) (k :: ks) (e :: accB) accC base cop hpw.2 hlt_es
          (fun x hx y hy => hltC x hx y (List.mem_cons_of_mem e hy)) hstepB hpwC
          (fun x hx y hy => by
            rcases List.mem_cons.mp hx with rfl | hx'
            · exact (he_ltC y hy).ne'
            · exact hdisj x hx' y hy) hsp
        refine ⟨res.1, res.2.1, fun x hx => ?_, fun x hx => ?_, res.2.2.2.2.1, fun f => ?_⟩
        · rcases res.2.2.1 x hx with hx' | hx'
          · rcases List.mem_cons.mp hx' with rfl | hx''
            · right; exact List.mem_cons_self
            · left; exact hx''
          · right; exact List.mem_cons_of_mem e hx'
        · rcases res.2.2.2.1 x hx with hx' | hx'
          · left; exact hx'
          · right; exact List.mem_cons_of_mem e hx'
        · have := res.2.2.2.2.2 f
          simp only [List.map_cons, List.prod_cons] at this ⊢
          linarith

lemma cop_fold_seedOk {m minP : ℕ} (p0 : ℕ)
    (l : List Entry) (cur : ℕ)
    (hpw_l : (l.map (·.p)).Pairwise (· < ·))
    (hl : ∀ c ∈ l, EntryValid m minP c ∧ 6 * (c.p : ℤ) ≤ (p0 : ℤ) - 127 ∧ ∀ q ∈ cur.primeFactors, q ≠ c.p)
    (hs : SeedOk cur) (hP : (p0 : ℤ) ≤ PropSum cur) :
    SeedOk (cur * (l.map (fun e => e.p ^ m.factorization e.p)).prod) ∧
    (p0 : ℤ) ≤ PropSum (cur * (l.map (fun e => e.p ^ m.factorization e.p)).prod) := by
  induction l generalizing cur with
  | nil => simpa using ⟨hs, hP⟩
  | cons c cs ih =>
    rw [List.map_cons, List.pairwise_cons] at hpw_l
    have hc := hl c List.mem_cons_self
    have hc_ev := hc.1
    have hc3 : 3 ≤ c.p := by
      have := hc_ev.1.two_le
      have hne2 : c.p ≠ 2 := fun h => by have := hc_ev.2.2.1; rw [h] at this; exact absurd this (by decide)
      omega
    have hcur_pos : 0 < cur := by have := hs.1; omega
    have hcop_c : cur.Coprime c.p := by
      refine (hc_ev.1.coprime_iff_not_dvd.mpr fun hdvd => ?_).symm
      exact hc.2.2 c.p (Nat.mem_primeFactors.mpr ⟨hc_ev.1, hdvd, hcur_pos.ne'⟩) rfl
    have hc_bnd : 6 * (c.p : ℤ) ≤ PropSum cur - 127 := by linarith [hc.2.1, hP]
    have hc_a : 1 ≤ m.factorization c.p := le_trans hc_ev.2.2.2.2.1 hc_ev.2.2.2.2.2.1
    obtain ⟨hs1, hP1⟩ := seedOk_mul_prime_pow hs hc_ev.1 hcop_c hc3 hc_a hc_bnd
    have ih_res := ih (cur * c.p ^ m.factorization c.p) hpw_l.2 (fun y hy => by
      have hy' := hl y (List.mem_cons_of_mem c hy)
      refine ⟨hy'.1, hy'.2.1, fun q hq => ?_⟩
      rw [Nat.primeFactors_mul hcur_pos.ne' (Nat.pow_pos hc_ev.1.pos).ne', Finset.mem_union] at hq
      rcases hq with hq1 | hq2
      · exact hy'.2.2 q hq1
      · have hqp := Nat.prime_of_mem_primeFactors hq2
        have hqd := hc_ev.1.dvd_iff_eq hqp.ne_one |>.mp (hqp.dvd_of_dvd_pow (Nat.dvd_of_mem_primeFactors hq2))
        have := hpw_l.1 y.p (List.mem_map_of_mem hy)
        omega) hs1 (le_trans hP hP1)
    simpa [List.map_cons, List.prod_cons, mul_assoc] using ih_res

lemma prod_pow_eq_minA_mul_diff {m minP : ℕ} (l : List Entry)
    (hl : ∀ e ∈ l, EntryValid m minP e) :
    (l.map (fun e => e.p ^ m.factorization e.p)).prod =
    (l.map (fun e => e.p ^ e.minA)).prod * (l.map (fun e => e.p ^ (m.factorization e.p - e.minA))).prod := by
  induction l with
  | nil => simp
  | cons e es ih =>
    have he := hl e List.mem_cons_self
    have hle := he.2.2.2.2.2.1
    have he_eq : e.p ^ m.factorization e.p = e.p ^ e.minA * e.p ^ (m.factorization e.p - e.minA) := by
      rw [← pow_add, Nat.add_sub_cancel' hle]
    simp only [List.map_cons, List.prod_cons]
    rw [he_eq, ih (fun x hx => hl x (List.mem_cons_of_mem e hx))]
    ring

lemma checkBaseExt_sound {m minP : ℕ} (_hm_odd : Odd m)
    (entries : List Entry) (hpw : (entries.map (·.p)).Pairwise (· < ·))
    (hev : ∀ e ∈ entries, EntryValid m minP e)
    (sd : Seed) (hsv : SeedValid sd) (copIdxs : List Nat) (skipFree : Bool) (extraCop : Nat)
    (hskip : skipFree = true → ∀ e ∈ entries, m.factorization e.p = e.minA)
    (hchk : checkBaseExt entries sd copIdxs skipFree extraCop = true) :
    let b := (entries.map (fun e => e.p ^ m.factorization e.p)).prod
    SeedOk b ∧ (sd.p0 : ℤ) ≤ PropSum b ∧ 6 * (extraCop : ℤ) ≤ PropSum b - 127 := by
  unfold checkBaseExt at hchk
  rcases hsp : splitEntriesLoop 0 entries copIdxs [] [] with _ | ⟨base, cop⟩
  · rw [hsp] at hchk; simp at hchk
  · rw [hsp] at hchk
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hchk
    obtain ⟨⟨⟨⟨hne_base, hfac_eq⟩, hfree_ok⟩, hcop_ok⟩, hextra_ok⟩ := hchk
    have hsplit := splitEntriesLoop_spec 0 entries copIdxs [] [] base cop hpw (by simp) (by simp) (by simp) (by simp) (by simp) hsp
    have hbase_ev : ∀ e ∈ base, EntryValid m minP e := fun e he =>
      hev e ((hsplit.2.2.1 e he).resolve_left (by simp))
    have hcop_ev : ∀ e ∈ cop, EntryValid m minP e := fun e he =>
      hev e ((hsplit.2.2.2.1 e he).resolve_left (by simp))
    set b₀ := sd.fac.foldl (fun acc pe => acc * pe.1 ^ pe.2) 1
    have hb0_eq : b₀ = (base.map (fun e => e.p ^ e.minA)).prod := by
      dsimp [b₀]
      rw [foldl_mul_eq, one_mul, ← hfac_eq]
      simp [List.map_map, Function.comp_def]
    have hprimes_eq : sd.fac.map (·.1) = base.map (·.p) := by
      rw [← hfac_eq]; simp [List.map_map, Function.comp_def]
    -- Build DenseSeed from b₀ up to b_base by adding excess powers for each e ∈ base
    have hd_fold : ∀ (l : List Entry) (cur : ℕ),
        (l.map (·.p)).Pairwise (· < ·) →
        (∀ e ∈ l, EntryValid m minP e ∧ e ∈ base) →
        DenseSeed b₀ cur sd.cutB →
        (∀ q ∈ cur.primeFactors, q ∈ sd.fac.map (·.1)) →
        DenseSeed b₀ (cur * (l.map (fun e => e.p ^ (m.factorization e.p - e.minA))).prod) sd.cutB := by
      intro l
      induction l with
      | nil => intro cur _ _ hdc _; simpa using hdc
      | cons e es ih =>
        intro cur hpw_l hl hdc hcur_pf
        rw [List.map_cons, List.pairwise_cons] at hpw_l
        have he := hl e List.mem_cons_self
        have he_ev := he.1
        set diff := m.factorization e.p - e.minA
        have hstep_pow : ∀ k : ℕ, (0 < k → e.p ∈ sd.freeP) →
            DenseSeed b₀ (cur * e.p ^ k) sd.cutB ∧ (∀ q ∈ (cur * e.p ^ k).primeFactors, q ∈ sd.fac.map (·.1)) := by
          intro k hk_free
          induction k with
          | zero => refine ⟨by simpa using hdc, by simpa using hcur_pf⟩
          | succ k ihk =>
            obtain ⟨hdc_k, hpf_k⟩ := ihk (fun _ => hk_free (Nat.succ_pos k))
            have hfree_e : e.p ∈ sd.freeP := hk_free (Nat.succ_pos k)
            rw [pow_succ, ← mul_assoc]
            refine ⟨denseSeed_mul_mem hsv hdc_k hpf_k hfree_e he_ev.1, fun q hq => ?_⟩
            have hmul_pos : 0 < cur * e.p ^ k := denseSeed_pos hdc_k
            rw [Nat.primeFactors_mul hmul_pos.ne' he_ev.1.pos.ne', Finset.mem_union] at hq
            rcases hq with hq1 | hq2
            · exact hpf_k q hq1
            · rw [Nat.Prime.primeFactors he_ev.1, Finset.mem_singleton] at hq2
              subst hq2
              rw [hprimes_eq]
              exact List.mem_map_of_mem he.2
        have hdiff_free : 0 < diff → e.p ∈ sd.freeP := fun hpos => by
          cases hsf : skipFree
          · simp only [hsf, Bool.false_eq_true, false_or, List.all_eq_true, Bool.or_eq_true] at hfree_ok
            rcases hfree_ok e he.2 with hex | hmem
            · have := he_ev.2.2.2.2.2.2.1 hex; omega
            · exact List.contains_iff_mem.mp hmem
          · have := hskip hsf e ((hsplit.2.2.1 e he.2).resolve_left (by simp)); omega
        obtain ⟨hdc_next, hpf_next⟩ := hstep_pow diff hdiff_free
        have ih_res := ih (cur * e.p ^ diff) hpw_l.2 (fun x hx => hl x (List.mem_cons_of_mem e hx)) hdc_next hpf_next
        simpa [List.map_cons, List.prod_cons, mul_assoc] using ih_res
    have hb0_pf : ∀ q ∈ b₀.primeFactors, q ∈ sd.fac.map (·.1) := fun q hq => by
      obtain ⟨pe, hpe, rfl⟩ := (foldl_fac_prod_sigma sd.fac 2 hsv.2.1).2.2.1 q hq
      exact List.mem_map_of_mem hpe
    have hdense_base := hd_fold base b₀ hsplit.1 (fun e he => ⟨hbase_ev e he, he⟩) hsv.2.2.2.2.1 hb0_pf
    have hpw_base := hsplit.1
    have hdisj_bc := hsplit.2.2.2.2.1
    have hpw_cop := hsplit.2.1
    have hsp_prod := hsplit.2.2.2.2.2 (fun e => e.p ^ m.factorization e.p)
    set bBase := (base.map (fun (e : Entry) => e.p ^ m.factorization e.p)).prod
    have hb_base_eq : bBase = b₀ * (base.map (fun e => e.p ^ (m.factorization e.p - e.minA))).prod := by
      rw [hb0_eq]; exact prod_pow_eq_minA_mul_diff base hbase_ev
    rw [← hb_base_eq] at hdense_base
    have hSeed_base : SeedOk bBase := denseSeed_to_seedOk hdense_base
    have hb0_pos : 0 < b₀ := by have := hsv.2.2.2.2.1.1; omega
    have hP_base_ge : (sd.p0 : ℤ) ≤ PropSum bBase := by
      rw [← hsv.2.2.2.1]
      have hmul := propSum_mul_le hb0_pos hdense_base.2.1
      have hpos_div : (1 : ℤ) ≤ ((bBase / b₀ : ℕ) : ℤ) := by
        have hpos_b : 0 < bBase := denseSeed_pos hdense_base
        exact_mod_cast Nat.div_pos (Nat.le_of_dvd hpos_b hdense_base.2.1) hb0_pos
      have hP0_nonneg : 0 ≤ PropSum b₀ := by rw [hsv.2.2.2.1]; omega
      nlinarith
    rw [List.all_eq_true] at hcop_ok
    have h127 : 127 ≤ sd.p0 := by have := hsv.2.2.2.2.1.2.2.1; rw [hsv.2.2.2.1] at this; omega
    have hbase_disj : ∀ c ∈ cop, EntryValid m minP c ∧ 6 * (c.p : ℤ) ≤ (sd.p0 : ℤ) - 127 ∧
        ∀ q ∈ bBase.primeFactors, q ≠ c.p := by
      intro c hc
      have hc_ev := hcop_ev c hc
      have h6 : 6 * c.p ≤ sd.p0 - 127 := by simpa using hcop_ok c hc
      refine ⟨hc_ev, by omega, fun q hq => ?_⟩
      obtain ⟨b', hb', hbq⟩ := (prod_entries_factorization base hpw_base hbase_ev (fun e => m.factorization e.p)).2 q hq
      rw [← hbq]
      exact hdisj_bc b' hb' c hc
    have hres := cop_fold_seedOk sd.p0 cop bBase hpw_cop hbase_disj hSeed_base hP_base_ge
    have hb_entries_eq : (entries.map (fun e => e.p ^ m.factorization e.p)).prod =
        bBase * (cop.map (fun e => e.p ^ m.factorization e.p)).prod := by
      simpa [bBase] using hsp_prod
    rw [hb_entries_eq]
    have hextra_z : 6 * (extraCop : ℤ) ≤ (sd.p0 : ℤ) - 127 := by omega
    exact ⟨hres.1, hres.2, le_trans hextra_z (by linarith [hres.2])⟩

-- =====================================================================
-- guaranteedD2Ext_sound, guaranteedD2_sound
-- =====================================================================

lemma guaranteedD2Ext_sound {b : ℕ} (hb_odd : Odd b) (hb_def : b.Deficient)
    (spec : List Entry) (hpw : (spec.map (·.p)).Pairwise (· < ·))
    (hev : ∀ e ∈ spec, e.p.Prime ∧ e.p ∣ b ∧ e.minA ≤ b.factorization e.p ∧
      (e.exact = true → b.factorization e.p = e.minA) ∧
      (e.par = .odd → Odd (b.factorization e.p)))
    (hchk : guaranteedD2Ext spec = true) :
    2 ≤ (b : ℤ) - PropSum b := by
  have hdef := (deficient_iff_sigma_lt_two_mul b).mp hb_def
  have hsig_eq := sigma_one_eq_sum_proper_add b
  have hb_pos : 0 < b := hb_odd.pos
  have hb_ne : b ≠ 0 := hb_pos.ne'
  unfold guaranteedD2Ext at hchk
  rw [Bool.or_eq_true] at hchk
  rcases hchk with hodd | hgcd
  · rw [List.any_eq_true] at hodd
    obtain ⟨e, he, hpar⟩ := hodd
    have hpe : e.par = .odd := by simpa using hpar
    have he' := hev e he
    have hodd_exp := he'.2.2.2.2 hpe
    have h2_succ : 2 ∣ e.p + 1 := by
      have : Odd e.p := hb_odd.of_dvd_nat he'.2.1
      exact this.add_one.two_dvd
    have hdvd_sig : sigPP e.p (b.factorization e.p) ∣ sigma 1 b := by
      rw [sigma_one_eq_prod_primeFactors hb_ne]
      exact Finset.dvd_prod_of_mem _ (Nat.mem_primeFactors.mpr ⟨he'.1, he'.2.1, hb_ne⟩)
    have h2_sig : 2 ∣ sigma 1 b := h2_succ.trans ((succ_dvd_sigPP he'.1.one_lt hodd_exp).trans hdvd_sig)
    have h2_D : 2 ∣ 2 * b - sigma 1 b := Nat.dvd_sub (dvd_mul_right 2 b) h2_sig
    have hle : 2 ≤ 2 * b - sigma 1 b := Nat.le_of_dvd (by omega) h2_D
    rw [propSum_eq_nat]; omega
  · have hg_aux : ∀ (target : ℕ) (l : List Entry), (∀ e ∈ l, e ∈ spec) → gcdList target l = true →
        ∃ e ∈ l, e.exact = true ∧ 1 < Nat.gcd (sigPP e.p e.minA) target := by
      intro target l hl hgl
      induction l with
      | nil => simp [gcdList] at hgl
      | cons x xs ih =>
        unfold gcdList at hgl
        rw [Bool.or_eq_true] at hgl
        rcases hgl with hx | hxs
        · simp only [Bool.and_eq_true, decide_eq_true_eq] at hx
          exact ⟨x, List.mem_cons_self, hx.1, hx.2⟩
        · obtain ⟨e, he, hex, hgt⟩ := ih (fun y hy => hl y (List.mem_cons_of_mem x hy)) hxs
          exact ⟨e, List.mem_cons_of_mem x he, hex, hgt⟩
    obtain ⟨e, he_mem, hex, hgt1⟩ := hg_aux _ spec (fun _ h => h) hgcd
    have he' := hev e he_mem
    set g := Nat.gcd (sigPP e.p e.minA) (spec.foldl (fun acc x => acc * x.p) 1)
    have hg_sig : g ∣ sigma 1 b := by
      refine (Nat.gcd_dvd_left _ _).trans ?_
      rw [← he'.2.2.2.1 hex, sigma_one_eq_prod_primeFactors hb_ne]
      exact Finset.dvd_prod_of_mem _ (Nat.mem_primeFactors.mpr ⟨he'.1, he'.2.1, hb_ne⟩)
    have hg_pprod : g ∣ (spec.map (·.p)).prod := by
      rw [← one_mul (spec.map (·.p)).prod, ← foldl_mul_eq]
      exact Nat.gcd_dvd_right _ _
    have hpprod_b : (spec.map (·.p)).prod ∣ b := by
      have hsub : (spec.map (·.p)).toFinset ⊆ b.primeFactors := fun q hq => by
        rw [List.mem_toFinset, List.mem_map] at hq
        obtain ⟨x, hx, rfl⟩ := hq
        exact Nat.mem_primeFactors.mpr ⟨(hev x hx).1, (hev x hx).2.1, hb_ne⟩
      rw [list_prod_toFinset hpw]
      have himg : (spec.toFinset.image (·.p)) = (spec.map (·.p)).toFinset := by ext q; simp
      have hndp : (spec.map (·.p)).Nodup := hpw.imp (fun h => Nat.ne_of_lt h)
      have hprod_eq : ∏ x ∈ spec.toFinset, x.p = ∏ q ∈ (spec.map (·.p)).toFinset, q := by
        rw [← himg, Finset.prod_image]
        intro x hx y hy hxy
        simp only [Finset.mem_coe, List.mem_toFinset] at hx hy
        exact spec_mem_p_unique hndp hx hy hxy
      rw [hprod_eq]
      exact (Finset.prod_dvd_prod_of_subset _ _ id hsub).trans (by
        have hS_dvd : ∀ S : Finset ℕ, (∀ q ∈ S, q ∈ b.primeFactors) → (∏ q ∈ S, q) ∣ b := fun S hS => by
          conv_rhs => rw [Nat.prod_primeFactors_pow_factorization hb_ne]
          calc ∏ q ∈ S, q ∣ ∏ q ∈ b.primeFactors, q := Finset.prod_dvd_prod_of_subset _ _ id hS
            _ ∣ ∏ q ∈ b.primeFactors, q ^ b.factorization q :=
              Finset.prod_dvd_prod_of_dvd _ _ fun q hq =>
                dvd_pow_self q (Nat.pos_iff_ne_zero.mp ((Nat.prime_of_mem_primeFactors hq).factorization_pos_of_dvd hb_ne (Nat.dvd_of_mem_primeFactors hq)))
        exact hS_dvd b.primeFactors (fun _ h => h))
    have hg_2b : g ∣ 2 * b := (hg_pprod.trans hpprod_b).trans (dvd_mul_left b 2)
    have hg_D : g ∣ 2 * b - sigma 1 b := Nat.dvd_sub hg_2b hg_sig
    have hle : g ≤ 2 * b - sigma 1 b := Nat.le_of_dvd (by omega) hg_D
    rw [propSum_eq_nat]; omega

lemma guaranteedD2_sound {b : ℕ} (hb_odd : Odd b) (hb_def : b.Deficient)
    (spec : List Entry) (hpw : (spec.map (·.p)).Pairwise (· < ·))
    (hev : ∀ e ∈ spec, e.p.Prime ∧ e.p ∣ b ∧ e.minA ≤ b.factorization e.p ∧
      (e.exact = true → b.factorization e.p = e.minA) ∧
      (e.par = .odd → Odd (b.factorization e.p)))
    (hspec_all : spec.all (·.exact) = true → b = (minNumAb spec).1 ∧ sigma 1 b = (minNumAb spec).2)
    (hchk : guaranteedD2 spec = true) :
    2 ≤ (b : ℤ) - PropSum b := by
  unfold guaranteedD2 at hchk
  rw [Bool.or_eq_true] at hchk
  rcases hchk with hext | hex
  · exact guaranteedD2Ext_sound hb_odd hb_def spec hpw hev hext
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at hex
    obtain ⟨hall, hle⟩ := hex
    obtain ⟨hb_eq, hs_eq⟩ := hspec_all hall
    have hsig := sigma_one_eq_sum_proper_add b
    rw [← hb_eq, ← hs_eq] at hle
    rw [propSum_eq_nat]; omega


-- =====================================================================
-- List helpers & checkCert_sound
-- =====================================================================

lemma eraseIdx_spec {α : Type*} : ∀ (l : List α) (i : ℕ) (x : α),
    l[i]? = some x →
    (∀ y ∈ l.eraseIdx i, y ∈ l) ∧
    (∀ (f : α → ℕ), (l.map f).prod = f x * ((l.eraseIdx i).map f).prod) ∧
    (∀ (g : α → ℕ), (l.map g).Pairwise (· < ·) → ((l.eraseIdx i).map g).Pairwise (· < ·) ∧ g x ∉ (l.eraseIdx i).map g) := by
  intro l
  induction l with
  | nil => intro i x h; simp at h
  | cons a t ih =>
    intro i x h
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero] at h
      injection h with hax; subst hax
      refine ⟨fun y hy => List.mem_cons_of_mem a hy, fun f => by simp, fun g hg => ?_⟩
      rw [List.eraseIdx_zero, List.tail_cons]
      rw [List.map_cons, List.pairwise_cons] at hg
      exact ⟨hg.2, fun hmem => Nat.lt_irrefl _ (hg.1 _ hmem)⟩
    | succ i =>
      simp only [List.getElem?_cons_succ] at h
      have ih_res := ih i x h
      refine ⟨fun y hy => ?_, fun f => ?_, fun g hg => ?_⟩
      · rw [List.eraseIdx_cons_succ, List.mem_cons] at hy
        rcases hy with rfl | hy'
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem a (ih_res.1 y hy')
      · rw [List.eraseIdx_cons_succ, List.map_cons, List.map_cons, List.prod_cons, List.prod_cons, ih_res.2.1 f]
        ring
      · rw [List.eraseIdx_cons_succ, List.map_cons, List.pairwise_cons]
        rw [List.map_cons, List.pairwise_cons] at hg
        have ih_g := ih_res.2.2 g hg.2
        refine ⟨⟨fun q hq => hg.1 q ?_, ih_g.1⟩, ?_⟩
        · rw [List.mem_map] at hq ⊢; obtain ⟨y, hy, rfl⟩ := hq; exact ⟨y, ih_res.1 y hy, rfl⟩
        · rw [List.mem_cons]; rintro (heq | hmem)
          · have hmem_x : x ∈ t := List.mem_of_getElem? h
            have := hg.1 (g x) (List.mem_map_of_mem hmem_x)
            omega
          · exact ih_g.2 hmem

lemma listSet_spec : ∀ (l : List Entry) (i : ℕ) (e v : Entry),
    l[i]? = some e → v.p = e.p →
    (listSet l i v).map (·.p) = l.map (·.p) ∧
    (∀ x ∈ listSet l i v, x = v ∨ x ∈ l) ∧
    (∀ (f : Entry → ℕ), ((listSet l i v).map f).prod = f v * ((l.eraseIdx i).map f).prod) := by
  intro l
  induction l with
  | nil => intro i e v h; simp at h
  | cons a t ih =>
    intro i e v h hvp
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero] at h
      injection h with hae; subst hae
      refine ⟨by simp [listSet, hvp], fun x hx => ?_, fun f => by simp [listSet]⟩
      simp only [listSet, List.mem_cons] at hx
      rcases hx with rfl | hxt
      · left; rfl
      · right; exact List.mem_cons_of_mem a hxt
    | succ i =>
      simp only [List.getElem?_cons_succ] at h
      have ih_res := ih i e v h hvp
      refine ⟨by simp [listSet, ih_res.1], fun x hx => ?_, fun f => ?_⟩
      · simp only [listSet, List.mem_cons] at hx
        rcases hx with rfl | hxt
        · right; exact List.mem_cons_self
        · rcases ih_res.2.1 x hxt with rfl | hxt'
          · left; rfl
          · right; exact List.mem_cons_of_mem a hxt'
      · simp only [listSet, List.eraseIdx_cons_succ, List.map_cons, List.prod_cons, ih_res.2.2 f]
        ring

lemma checkSurv_sound {m s : ℕ} (hm_pos : 0 < m) (hm_sig : sigma 1 m = s)
    (xs : List ℕ) (hchk : checkSurv m s xs = true) : m.Pseudoperfect := by
  unfold checkSurv at hchk
  simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hchk
  obtain ⟨⟨⟨hall, _⟩, hnd_b⟩, hsum⟩ := hchk
  have hnd : xs.Nodup := by simpa using hnd_b
  rw [List.all_eq_true] at hall
  have hsub : xs.toFinset ⊆ m.properDivisors := by
    intro d hd
    rw [List.mem_toFinset] at hd
    have h := hall d hd
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    exact Nat.mem_properDivisors.mpr ⟨Nat.dvd_of_mod_eq_zero h.2, h.1.2⟩
  have hsum_z : (∑ d ∈ xs.toFinset, (d : ℤ)) = (sigma 1 m : ℤ) - 2 * (m : ℤ) := by
    have hz : (∑ d ∈ xs.toFinset, (d : ℤ)) = ((∑ d ∈ xs.toFinset, d : ℕ) : ℤ) := by simp
    have hsum_nat : ∑ d ∈ xs.toFinset, d = xs.sum := by simpa using List.sum_toFinset id hnd
    rw [hz, hsum_nat, hm_sig]
    omega
  exact OMA.R_Erdos470_erdos_470_variants_odd_weird_prime_div_R1_H2_R1.pseudoperfect_of_excess hm_pos hsub hsum_z

lemma spec_length_le_five {m : ℕ} (hm : m ≠ 0) (hm_card : m.primeFactors.card ≤ 5)
    {spec : List Entry} {minP : ℕ} {am : Bool} (hs : SpecValid m spec minP am) :
    spec.length ≤ 5 := by
  have := Finset.card_le_card (spec_toFinset_subset hm hs)
  rw [spec_toFinset_card hs] at this
  omega

lemma spec_all_primes {m : ℕ} (hm0 : m ≠ 0) (hm_card : m.primeFactors.card ≤ 5)
    {spec : List Entry} {minP : ℕ} {am : Bool} (hs : SpecValid m spec minP am)
    (hfull : am = false ∨ 5 ≤ spec.length) :
    ∀ q ∈ m.primeFactors, ∃ e ∈ spec, e.p = q := by
  rcases hfull with rfl | hlen5
  · exact hs.2.2
  · have hsub := spec_toFinset_subset hm0 hs
    have hcard : m.primeFactors.card ≤ (spec.map (·.p)).toFinset.card := by
      rw [spec_toFinset_card hs]; omega
    have heq := Finset.eq_of_subset_of_card_le hsub hcard
    intro q hq
    rw [← heq, List.mem_toFinset, List.mem_map] at hq
    exact hq

lemma spec_erase_split {m minP : ℕ} {am : Bool} (hm0 : m ≠ 0) (_hm_odd : Odd m)
    {spec : List Entry} (hs : SpecValid m spec minP am)
    (hall_p : ∀ q ∈ m.primeFactors, ∃ e ∈ spec, e.p = q)
    {qi : ℕ} {qE : Entry} (hget : spec[qi]? = some qE) :
    let others := spec.eraseIdx qi
    let b := (others.map (fun e => e.p ^ m.factorization e.p)).prod
    (others.map (·.p)).Pairwise (· < ·) ∧
    (∀ e ∈ others, EntryValid m minP e) ∧
    m = b * qE.p ^ ((m.factorization qE.p - 1) + 1) ∧
    qE.p.Prime ∧ b.Coprime qE.p ∧ 3 ≤ qE.p ∧ b < m ∧
    (∀ e ∈ others, e.p ∣ b ∧ m.factorization e.p = b.factorization e.p ∧
      (e.par = .odd → Odd (b.factorization e.p))) := by
  intro others b
  have her := eraseIdx_spec spec qi qE hget
  have hpw_oth : (others.map (·.p)).Pairwise (· < ·) := (her.2.2 _ hs.1).1
  have hnot_mem : qE.p ∉ others.map (·.p) := (her.2.2 _ hs.1).2
  have hev_oth : ∀ e ∈ others, EntryValid m minP e := fun e he => hs.2.1 e (her.1 e he)
  have hq_mem : qE ∈ spec := List.mem_of_getElem? hget
  have hq_ev := hs.2.1 qE hq_mem
  have hq3 : 3 ≤ qE.p := by
    have := hq_ev.1.two_le
    have hne2 : qE.p ≠ 2 := fun h => by have := hq_ev.2.2.1; rw [h] at this; exact absurd this (by decide)
    omega
  have h_sdiff_empty : m.primeFactors \ (spec.map (·.p)).toFinset = ∅ := by
    ext q
    simp only [Finset.mem_sdiff, Finset.notMem_empty, iff_false, not_and, not_not]
    intro hq
    obtain ⟨e, he, rfl⟩ := hall_p q hq
    exact List.mem_toFinset.mpr (List.mem_map_of_mem he)
  have hm_prod : m = (spec.map (fun e => e.p ^ m.factorization e.p)).prod := by
    have hsp := (prod_spec_factor_split hm0 hs).1
    rw [h_sdiff_empty, Finset.prod_empty, mul_one] at hsp
    exact hsp
  have hm_split : m = b * qE.p ^ ((m.factorization qE.p - 1) + 1) := by
    have hperm := her.2.1 (fun e => e.p ^ m.factorization e.p)
    rw [← hm_prod] at hperm
    have h1 : 1 ≤ m.factorization qE.p := le_trans hq_ev.2.2.2.2.1 hq_ev.2.2.2.2.2.1
    have hperm' : m = b * qE.p ^ m.factorization qE.p := hperm.trans (mul_comm _ _)
    calc m = b * qE.p ^ m.factorization qE.p := hperm'
      _ = b * qE.p ^ ((m.factorization qE.p - 1) + 1) := by rw [Nat.sub_add_cancel h1]
  have hb_pos : 0 < b := List.prod_pos fun x hx => by
    rw [List.mem_map] at hx; obtain ⟨e, he, rfl⟩ := hx
    exact Nat.pow_pos (hev_oth e he).1.pos
  have hcop_bq : b.Coprime qE.p := by
    refine (hq_ev.1.coprime_iff_not_dvd.mpr fun hdvd => ?_).symm
    obtain ⟨e, he, heq⟩ := (prod_entries_factorization others hpw_oth hev_oth (fun x => m.factorization x.p)).2
      qE.p (Nat.mem_primeFactors.mpr ⟨hq_ev.1, hdvd, hb_pos.ne'⟩)
    exact hnot_mem (heq ▸ List.mem_map_of_mem he)
  have hb_lt_m : b < m := by
    rw [hm_split]
    have hpow_gt : 1 < qE.p ^ ((m.factorization qE.p - 1) + 1) :=
      one_lt_pow₀ (by omega) (Nat.succ_ne_zero _)
    exact lt_mul_of_one_lt_right hb_pos hpow_gt
  have hfac_oth := (prod_entries_factorization others hpw_oth hev_oth (fun x => m.factorization x.p)).1
  refine ⟨hpw_oth, hev_oth, hm_split, hq_ev.1, hcop_bq, hq3, hb_lt_m, fun e he => ?_⟩
  have he_ev := hev_oth e he
  have hfac_e : m.factorization e.p = b.factorization e.p := (hfac_oth e he).symm
  have hdvd_e : e.p ∣ b := by
    have h1 : 1 ≤ b.factorization e.p := by rw [← hfac_e]; exact le_trans he_ev.2.2.2.2.1 he_ev.2.2.2.2.2.1
    exact pow_one e.p ▸ (Nat.Prime.pow_dvd_iff_le_factorization he_ev.1 hb_pos.ne').mpr h1
  exact ⟨hdvd_e, hfac_e, fun hpar => by
    have hp_m := he_ev.2.2.2.2.2.2.2.1
    rw [hpar] at hp_m
    rwa [← hfac_e]⟩

lemma sigPP_mul_le_of_le {r a p4Next : ℕ} (hr : r.Prime) (hp4 : 2 ≤ p4Next) (hle : p4Next ≤ r) :
    sigPP r a * (p4Next - 1) ≤ p4Next * r ^ a := by
  have h1 : sigPP r a * (r - 1) ≤ r * r ^ a := (sigPP_lt_bound hr.one_lt a).le
  have h2 : r * (p4Next - 1) ≤ p4Next * (r - 1) := by zify [show 1 ≤ p4Next by omega, hr.one_lt.le]; nlinarith
  have hr1 : 0 < r - 1 := Nat.sub_pos_of_lt hr.one_lt
  apply Nat.le_of_mul_le_mul_right _ hr1
  calc sigPP r a * (p4Next - 1) * (r - 1)
      = (sigPP r a * (r - 1)) * (p4Next - 1) := by ring
    _ ≤ (r * r ^ a) * (p4Next - 1) := Nat.mul_le_mul_right _ h1
    _ = (r * (p4Next - 1)) * r ^ a := by ring
    _ ≤ (p4Next * (r - 1)) * r ^ a := Nat.mul_le_mul_right _ h2
    _ = p4Next * r ^ a * (r - 1) := by ring

lemma finset_prod_sigPP_le_of_card_le_two {m p4Next : ℕ} {S : Finset ℕ}
    (hcard : S.card ≤ 2) (hp4 : 2 ≤ p4Next) (hS : ∀ r ∈ S, r.Prime ∧ p4Next ≤ r) :
    (∏ r ∈ S, sigPP r (m.factorization r)) * (p4Next - 1) ^ 2 ≤
    p4Next ^ 2 * (∏ r ∈ S, r ^ m.factorization r) := by
  have hsub_le : p4Next - 1 ≤ p4Next := Nat.sub_le _ _
  have hcard_cases : S.card = 0 ∨ S.card = 1 ∨ S.card = 2 := by omega
  rcases hcard_cases with h0 | h1 | h2
  · rw [Finset.card_eq_zero.mp h0]
    simp only [Finset.prod_empty, one_mul, mul_one]
    exact Nat.pow_le_pow_left hsub_le 2
  · obtain ⟨r, rfl⟩ := Finset.card_eq_one.mp h1
    have hr := hS r (Finset.mem_singleton_self r)
    have hmul := sigPP_mul_le_of_le hr.1 hp4 hr.2 (a := m.factorization r)
    simp only [Finset.prod_singleton]
    calc sigPP r (m.factorization r) * (p4Next - 1) ^ 2
        = (sigPP r (m.factorization r) * (p4Next - 1)) * (p4Next - 1) := by ring
      _ ≤ (p4Next * r ^ m.factorization r) * p4Next := Nat.mul_le_mul hmul hsub_le
      _ = p4Next ^ 2 * r ^ m.factorization r := by ring
  · obtain ⟨r1, r2, hne, rfl⟩ := Finset.card_eq_two.mp h2
    have hr1 := hS r1 (Finset.mem_insert_self _ _)
    have hr2 := hS r2 (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
    have hmul1 := sigPP_mul_le_of_le hr1.1 hp4 hr1.2 (a := m.factorization r1)
    have hmul2 := sigPP_mul_le_of_le hr2.1 hp4 hr2.2 (a := m.factorization r2)
    rw [Finset.prod_pair hne, Finset.prod_pair hne]
    calc (sigPP r1 (m.factorization r1) * sigPP r2 (m.factorization r2)) * (p4Next - 1) ^ 2
        = (sigPP r1 (m.factorization r1) * (p4Next - 1)) * (sigPP r2 (m.factorization r2) * (p4Next - 1)) := by ring
      _ ≤ (p4Next * r1 ^ m.factorization r1) * (p4Next * r2 ^ m.factorization r2) := Nat.mul_le_mul hmul1 hmul2
      _ = p4Next ^ 2 * (r1 ^ m.factorization r1 * r2 ^ m.factorization r2) := by ring

lemma guaranteedD2_of_entries {m minP b : ℕ} (hm_odd : Odd m) (hb_pos : 0 < b)
    (hb_dvd_m : b ∣ m) (hb_lt_m : b < m) (hm_prim : ∀ d ∈ m.properDivisors, d.Deficient)
    (spec : List Entry) (hpw : (spec.map (·.p)).Pairwise (· < ·))
    (hev : ∀ e ∈ spec, EntryValid m minP e)
    (hb_eq : b = (spec.map (fun e => e.p ^ m.factorization e.p)).prod)
    (hfac : ∀ e ∈ spec, e.p ∣ b ∧ m.factorization e.p = b.factorization e.p)
    (hgd2 : guaranteedD2 spec = true) :
    2 ≤ (b : ℤ) - PropSum b := by
  have hb_odd : Odd b := hm_odd.of_dvd_nat hb_dvd_m
  have hb_def : b.Deficient := hm_prim b (Nat.mem_properDivisors.mpr ⟨hb_dvd_m, hb_lt_m⟩)
  have hev_b : ∀ e ∈ spec, e.p.Prime ∧ e.p ∣ b ∧ e.minA ≤ b.factorization e.p ∧
      (e.exact = true → b.factorization e.p = e.minA) ∧
      (e.par = .odd → Odd (b.factorization e.p)) := fun e he =>
    let h := hev e he
    let hf := hfac e he
    ⟨h.1, hf.1, hf.2 ▸ h.2.2.2.2.2.1, fun hx => hf.2 ▸ h.2.2.2.2.2.2.1 hx,
     fun hpar => by
       have hp_m := h.2.2.2.2.2.2.2.1
       rw [hpar] at hp_m
       rwa [← hf.2]⟩
  refine guaranteedD2_sound hb_odd hb_def spec hpw hev_b (fun hall => ?_) hgd2
  rw [List.all_eq_true] at hall
  have hb_min : b = (spec.map (fun e => e.p ^ e.minA)).prod := by
    rw [hb_eq]
    congr 1
    apply List.map_congr_left
    intro e he
    rw [(hev e he).2.2.2.2.2.2.1 (hall e he)]
  obtain ⟨_, _, hsig⟩ := prod_entries_dvd_and_sigma hb_pos.ne' spec hpw
    (fun e he =>
      let h := hev e he
      let hf := hfac e he
      ⟨h.1, h.2.1, h.2.2.1, hf.1, h.2.2.2.2.1, hf.2 ▸ h.2.2.2.2.2.1,
       fun hx => hf.2 ▸ h.2.2.2.2.2.2.1 hx,
       by cases hp : e.par
          · have hp_m := h.2.2.2.2.2.2.2.1; rw [hp] at hp_m; simp only; rwa [← hf.2]
          · have hp_m := h.2.2.2.2.2.2.2.1; rw [hp] at hp_m; simp only; rwa [← hf.2],
       hf.2 ▸ h.2.2.2.2.2.2.2.2⟩)
    (·.minA) (fun e he => (hfac e he).2 ▸ (hev e he).2.2.2.2.2.1)
  rw [minNumAb_eq spec]
  exact ⟨hb_min, by rw [hb_min, hsig]⟩

lemma cert_NP_sound {m minP : ℕ} {am : Bool} (hm_pos : 0 < m)
    (hm_prim : ∀ d ∈ m.properDivisors, d.Deficient)
    {spec : List Entry} (hs : SpecValid m spec minP am)
    {qi : ℕ}
    (hchk : (let (mv, s) := minNumAb spec
      if s ≤ 2 * mv then false
      else match spec[qi]? with
        | none => false
        | some e =>
          let spec2 := if e.minA == 1 then spec.eraseIdx qi else listSet spec qi { e with minA := e.minA - 1 }
          let (m2, s2) := minNumAb spec2
          2 * m2 ≤ s2) = true) : False := by
  have hm0 : m ≠ 0 := hm_pos.ne'
  rw [minNumAb_eq spec] at hchk
  dsimp only at hchk
  set b := (spec.map (fun e => e.p ^ e.minA)).prod
  split_ifs at hchk with hle_ab
  rcases hget : spec[qi]? with _ | qE
  · rw [hget] at hchk; simp at hchk
  · rw [hget] at hchk
    dsimp only at hchk
    have hq_mem : qE ∈ spec := List.mem_of_getElem? hget
    have hq_ev := hs.2.1 qE hq_mem
    obtain ⟨hb_pos, hb_dvd, hb_sig⟩ :=
      prod_entries_dvd_and_sigma hm0 spec hs.1 hs.2.1 (·.minA) (fun e he => (hs.2.1 e he).2.2.2.2.2.1)
    have hbm : b = m := by
      by_contra hne
      have hprop : b ∈ m.properDivisors :=
        Nat.mem_properDivisors.mpr ⟨hb_dvd, lt_of_le_of_ne (Nat.le_of_dvd hm_pos hb_dvd) hne⟩
      have hdef := (deficient_iff_sigma_lt_two_mul _).mp (hm_prim b hprop)
      rw [hb_sig] at hdef; omega
    have her := eraseIdx_spec spec qi qE hget
    have hpw2 : ((spec.eraseIdx qi).map (·.p)).Pairwise (· < ·) := (her.2.2 _ hs.1).1
    have hnot_q : qE.p ∉ (spec.eraseIdx qi).map (·.p) := (her.2.2 _ hs.1).2
    have hev2 : ∀ e ∈ spec.eraseIdx qi, EntryValid m minP e := fun e he => hs.2.1 e (her.1 e he)
    obtain ⟨hb2_pos, hb2_dvd, hb2_sig⟩ :=
      prod_entries_dvd_and_sigma hm0 _ hpw2 hev2 (·.minA) (fun e he => (hev2 e he).2.2.2.2.2.1)
    set b2 := ((spec.eraseIdx qi).map (fun e => e.p ^ e.minA)).prod
    by_cases h1 : qE.minA = 1
    · have h1b : (qE.minA == 1) = true := beq_iff_eq.mpr h1
      rw [if_pos h1b, minNumAb_eq] at hchk
      dsimp only at hchk
      rw [decide_eq_true_eq] at hchk
      have hb2_lt : b2 < b := by
        have := her.2.1 (fun e => e.p ^ e.minA)
        change b = qE.p ^ qE.minA * b2 at this
        rw [this, h1, pow_one]
        exact lt_mul_of_one_lt_left hb2_pos hq_ev.1.one_lt
      have hprop : b2 ∈ m.properDivisors := Nat.mem_properDivisors.mpr ⟨hb2_dvd, hbm ▸ hb2_lt⟩
      have hdef := (deficient_iff_sigma_lt_two_mul _).mp (hm_prim _ hprop)
      rw [hb2_sig] at hdef; omega
    · have h1f : (qE.minA == 1) = false := Bool.eq_false_iff.mpr (fun h => h1 (beq_iff_eq.mp h))
      rw [if_neg (by simp [h1f]), minNumAb_eq] at hchk
      dsimp only at hchk
      rw [decide_eq_true_eq] at hchk
      set qE' : Entry := { qE with minA := qE.minA - 1 }
      have hls := listSet_spec spec qi qE qE' hget rfl
      have hm2_eq : ((listSet spec qi qE').map (fun e => e.p ^ e.minA)).prod = qE.p ^ (qE.minA - 1) * b2 :=
        hls.2.2 (fun e => e.p ^ e.minA)
      have hs2_eq : ((listSet spec qi qE').map (fun e => sigPP e.p e.minA)).prod =
          sigPP qE.p (qE.minA - 1) * ((spec.eraseIdx qi).map (fun e => sigPP e.p e.minA)).prod :=
        hls.2.2 (fun e => sigPP e.p e.minA)
      have hcop : Nat.Coprime (qE.p ^ (qE.minA - 1)) b2 := by
        refine (hq_ev.1.coprime_iff_not_dvd.mpr fun hdvd => ?_).pow_left _
        obtain ⟨e, he, heq⟩ := (prod_entries_factorization _ hpw2 hev2 (·.minA)).2
          qE.p (Nat.mem_primeFactors.mpr ⟨hq_ev.1, hdvd, hb2_pos.ne'⟩)
        exact hnot_q (heq ▸ List.mem_map_of_mem he)
      have hpow_dvd : qE.p ^ (qE.minA - 1) ∣ m :=
        (hq_ev.1.pow_dvd_iff_le_factorization hm0).mpr (by have := hq_ev.2.2.2.2.2.1; omega)
      have hm2_dvd : qE.p ^ (qE.minA - 1) * b2 ∣ m := hcop.mul_dvd_of_dvd_of_dvd hpow_dvd hb2_dvd
      have hm2_lt : qE.p ^ (qE.minA - 1) * b2 < b := by
        have := her.2.1 (fun e => e.p ^ e.minA)
        change b = qE.p ^ qE.minA * b2 at this
        rw [this]
        exact Nat.mul_lt_mul_of_pos_right (Nat.pow_lt_pow_right hq_ev.1.one_lt (by have := hq_ev.2.2.2.2.1; omega)) hb2_pos
      have hm2_sig : sigma 1 (qE.p ^ (qE.minA - 1) * b2) =
          sigPP qE.p (qE.minA - 1) * ((spec.eraseIdx qi).map (fun e => sigPP e.p e.minA)).prod := by
        rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop, sigma_one_prime_pow hq_ev.1, hb2_sig]
      have hprop : qE.p ^ (qE.minA - 1) * b2 ∈ m.properDivisors :=
        Nat.mem_properDivisors.mpr ⟨hm2_dvd, hbm ▸ hm2_lt⟩
      have hdef := (deficient_iff_sigma_lt_two_mul _).mp (hm_prim _ hprop)
      rw [hm2_eq, hs2_eq] at hchk
      rw [hm2_sig] at hdef
      omega

lemma cert_AC_sound {m minP : ℕ} {am : Bool} (hm_odd : Odd m)
    (hm_prim : ∀ d ∈ m.properDivisors, d.Deficient) (hm_no : NoCertExt m)
    (seeds : List Seed) (hSeeds : ∀ (i : ℕ) (s : Seed), seeds[i]? = some s → SeedValid s)
    {spec : List Entry} (hs : SpecValid m spec minP am)
    {qi si : ℕ} {copIdxs : List ℕ}
    (hchk : (let (mv, s) := minNumAb spec
      if s ≤ 2 * mv then false
      else match spec[qi]?, seeds[si]? with
        | some qE, some sd =>
          let others := spec.eraseIdx qi
          let (b, sb) := minNumAb others
          (qE.minA > 1 || sb + 2 ≤ 2 * b) && checkBaseExt others sd copIdxs true 0
        | _, _ => false) = true) : False := by
  have hm_pos : 0 < m := hm_odd.pos
  have hm0 : m ≠ 0 := hm_pos.ne'
  rw [minNumAb_eq spec] at hchk
  dsimp only at hchk
  split_ifs at hchk with hle_ab
  rcases hqget : spec[qi]? with _ | qE
  · rw [hqget] at hchk; simp at hchk
  · rcases hsget : seeds[si]? with _ | sd
    · rw [hqget, hsget] at hchk; simp at hchk
    · rw [hqget, hsget] at hchk
      simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hchk
      obtain ⟨hd2_ok, hbase_ok⟩ := hchk
      have hq_ev := hs.2.1 qE (List.mem_of_getElem? hqget)
      obtain ⟨hb_pos, hb_dvd, hb_sig⟩ :=
        prod_entries_dvd_and_sigma hm0 spec hs.1 hs.2.1 (·.minA) (fun e he => (hs.2.1 e he).2.2.2.2.2.1)
      have hm_eq_min : m = (spec.map (fun e => e.p ^ e.minA)).prod := by
        by_contra hne
        have hprop : (spec.map (fun e => e.p ^ e.minA)).prod ∈ m.properDivisors :=
          Nat.mem_properDivisors.mpr ⟨hb_dvd, lt_of_le_of_ne (Nat.le_of_dvd hm_pos hb_dvd) (Ne.symm hne)⟩
        have hdef := (deficient_iff_sigma_lt_two_mul _).mp (hm_prim _ hprop)
        rw [hb_sig] at hdef; omega
      have hm_fac_eq : ∀ e ∈ spec, m.factorization e.p = e.minA := fun e he => by
        rw [hm_eq_min]
        exact (prod_entries_factorization spec hs.1 hs.2.1 (·.minA)).1 e he
      have hall_p : ∀ q ∈ m.primeFactors, ∃ e ∈ spec, e.p = q := fun q hq => by
        rw [hm_eq_min] at hq
        exact (prod_entries_factorization spec hs.1 hs.2.1 (·.minA)).2 q hq
      set others := spec.eraseIdx qi
      have her := eraseIdx_spec spec qi qE hqget
      obtain ⟨hpw_oth, hev_oth, hm_split, hqp, hcop_bq, hq3, _, _⟩ :=
        spec_erase_split hm0 hm_odd hs hall_p hqget
      have hskip_oth : ∀ e ∈ others, m.factorization e.p = e.minA := fun e he => hm_fac_eq e (her.1 e he)
      obtain ⟨hSeed_b, _, _⟩ := checkBaseExt_sound hm_odd others hpw_oth hev_oth sd
        (hSeeds si sd hsget) copIdxs true 0 (fun _ => hskip_oth) hbase_ok
      set b := (others.map (fun e => e.p ^ m.factorization e.p)).prod
      have hD2 : m.factorization qE.p - 1 = 0 → 2 ≤ (b : ℤ) - PropSum b := fun hj0 => by
        have hq1 : qE.minA = 1 := by
          have hfm := hm_fac_eq qE (List.mem_of_getElem? hqget)
          have h1 := hq_ev.2.2.2.2.1
          omega
        rcases hd2_ok with hgt1 | hsb
        · omega
        · rw [minNumAb_eq others] at hsb
          have hb_min : b = (others.map (fun e => e.p ^ e.minA)).prod := by
            dsimp [b]; congr 1; apply List.map_congr_left; intro e he; rw [hskip_oth e he]
          obtain ⟨_, _, hsb_eq⟩ := prod_entries_dvd_and_sigma hm0 others hpw_oth hev_oth (·.minA)
            (fun e he => (hev_oth e he).2.2.2.2.2.1)
          rw [← hb_min] at hsb hsb_eq
          have hsig_eq := sigma_one_eq_sum_proper_add b
          rw [hsb_eq] at hsig_eq
          rw [propSum_eq_nat]
          omega
      exact false_of_seedOk hm_no hSeed_b hm_split hqp hcop_bq hq3 hD2

lemma cert_KR_sound {m minP : ℕ} {allowMore : Bool} (hm_odd : Odd m)
    (hm_card : m.primeFactors.card ≤ 5) (hm_prim : ∀ d ∈ m.properDivisors, d.Deficient)
    (hm_no : NoCertExt m)
    (seeds : List Seed) (hSeeds : ∀ (i : ℕ) (s : Seed), seeds[i]? = some s → SeedValid s)
    {spec : List Entry} (hs : SpecValid m spec minP allowMore)
    {qi si : ℕ} {copIdxs : List ℕ}
    (hchk : ((!allowMore || 5 - spec.length == 0) &&
      match spec[qi]?, seeds[si]? with
      | some qE, some sd =>
        let others := spec.eraseIdx qi
        (!(qE.par == .odd && qE.minA == 1) || guaranteedD2 others) &&
        checkBaseExt others sd copIdxs false 0
      | _, _ => false) = true) : False := by
  have hm0 : m ≠ 0 := hm_odd.pos.ne'
  simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq] at hchk
  obtain ⟨hfull_b, hmatch⟩ := hchk
  have hfull : allowMore = false ∨ 5 ≤ spec.length := by
    rcases hfull_b with ham | hsub0
    · left; exact ham
    · right; have := spec_length_le_five hm0 hm_card hs; omega
  have hall_p := spec_all_primes hm0 hm_card hs hfull
  rcases hqget : spec[qi]? with _ | qE
  · rw [hqget] at hmatch; simp at hmatch
  · rcases hsget : seeds[si]? with _ | sd
    · rw [hqget, hsget] at hmatch; simp at hmatch
    · rw [hqget, hsget] at hmatch
      simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hmatch
      obtain ⟨hd2_cond, hbase_ok⟩ := hmatch
      set others := spec.eraseIdx qi
      obtain ⟨hpw_oth, hev_oth, hm_split, hqp, hcop_bq, hq3, hb_lt_m, hb_oth_fac⟩ :=
        spec_erase_split hm0 hm_odd hs hall_p hqget
      obtain ⟨hSeed_b, _, _⟩ := checkBaseExt_sound hm_odd others hpw_oth hev_oth sd
        (hSeeds si sd hsget) copIdxs false 0 (by simp) hbase_ok
      set b := (others.map (fun e => e.p ^ m.factorization e.p)).prod
      have hq_ev := hs.2.1 qE (List.mem_of_getElem? hqget)
      have hD2 : m.factorization qE.p - 1 = 0 → 2 ≤ (b : ℤ) - PropSum b := fun hj0 => by
        rcases hd2_cond with hnot_odd1 | hgd2
        · exfalso
          have hf1 : m.factorization qE.p = 1 := by
            have := le_trans hq_ev.2.2.2.2.1 hq_ev.2.2.2.2.2.1; omega
          have hmin1 : qE.minA = 1 := by
            have := hq_ev.2.2.2.2.1; have := hq_ev.2.2.2.2.2.1; omega
          have hpar_odd : qE.par = .odd := by
            cases hp : qE.par
            · rfl
            · have hev := hq_ev.2.2.2.2.2.2.2.1; rw [hp, hf1] at hev; exact absurd hev (by decide)
          simp [hpar_odd, hmin1] at hnot_odd1
        · have hb_pos : 0 < b := by have := hSeed_b.1; omega
          have hb_dvd_m : b ∣ m := by rw [hm_split]; exact dvd_mul_right _ _
          exact guaranteedD2_of_entries hm_odd hb_pos hb_dvd_m hb_lt_m hm_prim others hpw_oth hev_oth rfl
            (fun e he => ⟨(hb_oth_fac e he).1, (hb_oth_fac e he).2.1⟩) hgd2
      exact false_of_seedOk hm_no hSeed_b hm_split hqp hcop_bq hq3 hD2

lemma cert_K5_false {m minP : ℕ} {am : Bool} (hm_odd : Odd m)
    (hm_card : m.primeFactors.card ≤ 5) (hm_prim : ∀ d ∈ m.properDivisors, d.Deficient)
    (hm_no : NoCertExt m)
    {spec : List Entry} (hs : SpecValid m spec minP am) (hrem1 : 5 - spec.length = 1)
    {sd : Seed} (hsv : SeedValid sd) {copIdxs : List ℕ}
    (hgd2 : guaranteedD2 spec = true)
    (hbase_ok : checkBaseExt spec sd copIdxs false 0 = true)
    (hnot_all : ¬ ∀ q ∈ m.primeFactors, ∃ e ∈ spec, e.p = q) : False := by
  have hm0 : m ≠ 0 := hm_odd.pos.ne'
  push Not at hnot_all
  obtain ⟨q, hqm, hq_out⟩ := hnot_all
  set S := (spec.map (·.p)).toFinset
  have hsub_fin : S ⊆ m.primeFactors := spec_toFinset_subset hm0 hs
  have hq_notS : q ∉ S := fun h => by
    rw [List.mem_toFinset, List.mem_map] at h
    obtain ⟨e, he, rfl⟩ := h
    exact hq_out e he rfl
  have hcardS : S.card = 4 := by
    rw [spec_toFinset_card hs]
    have := spec_length_le_five hm0 hm_card hs
    omega
  have hm_pf_eq : insert q S = m.primeFactors :=
    Finset.eq_of_subset_of_card_le (Finset.insert_subset hqm hsub_fin)
      (by rw [Finset.card_insert_of_notMem hq_notS, hcardS]; exact hm_card)
  have hsdiff_eq : m.primeFactors \ S = {q} := by
    rw [← hm_pf_eq]
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
    exact ⟨fun ⟨hx, hnx⟩ => hx.resolve_right hnx, fun hx => ⟨Or.inl hx, hx ▸ hq_notS⟩⟩
  set b := (spec.map (fun e => e.p ^ m.factorization e.p)).prod
  have hm_split_raw := (prod_spec_factor_split hm0 hs).1
  rw [hsdiff_eq, Finset.prod_singleton] at hm_split_raw
  have hqp : q.Prime := Nat.prime_of_mem_primeFactors hqm
  have hq_dvd : q ∣ m := Nat.dvd_of_mem_primeFactors hqm
  have hq1 : 1 ≤ m.factorization q := hqp.factorization_pos_of_dvd hm0 hq_dvd
  have hm_split : m = b * q ^ ((m.factorization q - 1) + 1) := by
    rw [Nat.sub_add_cancel hq1]; exact hm_split_raw
  have hq3 : 3 ≤ q := by
    have := hqp.two_le
    have hq2 : q ≠ 2 := fun h => hm_odd.not_two_dvd_nat (h ▸ hq_dvd)
    omega
  obtain ⟨hSeed_b, _, _⟩ := checkBaseExt_sound hm_odd spec hs.1 hs.2.1 sd
    hsv copIdxs false 0 (by simp) hbase_ok
  have hb_pos : 0 < b := by have := hSeed_b.1; omega
  have hcop_bq : b.Coprime q := by
    refine (hqp.coprime_iff_not_dvd.mpr fun hdvd => ?_).symm
    obtain ⟨e, he, heq⟩ := (prod_entries_factorization spec hs.1 hs.2.1 (fun x => m.factorization x.p)).2
      q (Nat.mem_primeFactors.mpr ⟨hqp, hdvd, hb_pos.ne'⟩)
    exact hq_out e he heq
  have hb_lt_m : b < m := by
    rw [hm_split]
    exact lt_mul_of_one_lt_right hb_pos (one_lt_pow₀ (by omega) (Nat.succ_ne_zero _))
  have hb_dvd_m : b ∣ m := by rw [hm_split]; exact dvd_mul_right _ _
  have hfac_b := (prod_entries_factorization spec hs.1 hs.2.1 (fun x => m.factorization x.p)).1
  have hD2 : m.factorization q - 1 = 0 → 2 ≤ (b : ℤ) - PropSum b := fun _ =>
    guaranteedD2_of_entries hm_odd hb_pos hb_dvd_m hb_lt_m hm_prim spec hs.1 hs.2.1 rfl
      (fun e he =>
        let ev := hs.2.1 e he
        let hfe := (hfac_b e he).symm
        ⟨pow_one e.p ▸ (Nat.Prime.pow_dvd_iff_le_factorization ev.1 hb_pos.ne').mpr (by rw [← hfe]; exact le_trans ev.2.2.2.2.1 ev.2.2.2.2.2.1),
         hfe⟩) hgd2
  exact false_of_seedOk hm_no hSeed_b hm_split hqp hcop_bq hq3 hD2

lemma cert_KV_false {m minP : ℕ} {am : Bool} (hm_odd : Odd m) (hm_ab : m.Abundant)
    (hm_card : m.primeFactors.card ≤ 5) (hm_no : NoCertExt m)
    {spec : List Entry} (hs : SpecValid m spec minP am) (hrem1 : 5 - spec.length = 1)
    {abN abD : ℕ} (hmax : maxAbSpec spec minP 0 = (abN, abD))
    (habD_pos : abD ≠ 0) (hab_lt : abN < 2 * abD)
    {qi : ℕ} {qE : Entry} (hqget : spec[qi]? = some qE)
    {sd : Seed} (hsv : SeedValid sd) {copIdxs : List ℕ}
    (hnot_odd1 : ¬ (qE.par == .odd && qE.minA == 1) = true)
    (hbase_ok : checkBaseExt (spec.eraseIdx qi) sd copIdxs false ((2 * abD - 1) / (2 * abD - abN)) = true)
    (hnot_all : ¬ ∀ q ∈ m.primeFactors, ∃ e ∈ spec, e.p = q) : False := by
  have hm0 : m ≠ 0 := hm_odd.pos.ne'
  have h2m_lt : 2 * m < sigma 1 m := (abundant_iff_two_mul_lt_sigma m).mp hm_ab
  push Not at hnot_all
  obtain ⟨q5, hqm, hq5_out⟩ := hnot_all
  set S := (spec.map (·.p)).toFinset
  have hsub_fin : S ⊆ m.primeFactors := spec_toFinset_subset hm0 hs
  have hq5_notS : q5 ∉ S := fun h => by
    rw [List.mem_toFinset, List.mem_map] at h
    obtain ⟨e, he, rfl⟩ := h
    exact hq5_out e he rfl
  have hcardS : S.card = 4 := by
    rw [spec_toFinset_card hs]
    have := spec_length_le_five hm0 hm_card hs
    omega
  have hm_pf_eq : insert q5 S = m.primeFactors :=
    Finset.eq_of_subset_of_card_le (Finset.insert_subset hqm hsub_fin)
      (by rw [Finset.card_insert_of_notMem hq5_notS, hcardS]; exact hm_card)
  have hsdiff_eq : m.primeFactors \ S = {q5} := by
    rw [← hm_pf_eq]
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
    exact ⟨fun ⟨hx, hnx⟩ => hx.resolve_right hnx, fun hx => ⟨Or.inl hx, hx ▸ hq5_notS⟩⟩
  have hsplit_both := prod_spec_factor_split hm0 hs
  rw [hsdiff_eq, Finset.prod_singleton, Finset.prod_singleton] at hsplit_both
  set bSpec := (spec.map (fun e => e.p ^ m.factorization e.p)).prod
  set sSpec := (spec.map (fun e => sigPP e.p (m.factorization e.p))).prod
  have hbSpec_pos : 0 < bSpec := List.prod_pos fun x hx => by
    rw [List.mem_map] at hx; obtain ⟨e, he, rfl⟩ := hx
    exact Nat.pow_pos (hs.2.1 e he).1.pos
  have hq5p : q5.Prime := Nat.prime_of_mem_primeFactors hqm
  have hq5_dvd : q5 ∣ m := Nat.dvd_of_mem_primeFactors hqm
  have hq5_a : 1 ≤ m.factorization q5 := hq5p.factorization_pos_of_dvd hm0 hq5_dvd
  have hq5_3 : 3 ≤ q5 := by
    have := hq5p.two_le
    have hne2 : q5 ≠ 2 := fun h => hm_odd.not_two_dvd_nat (h ▸ hq5_dvd)
    omega
  have hmax0 := maxAbSpec_zero_sound hs hmax
  have hsig_q5 : sigPP q5 (m.factorization q5) * (q5 - 1) < q5 * q5 ^ m.factorization q5 :=
    sigPP_lt_bound hq5p.one_lt _
  have hmul_ab : 2 * bSpec * q5 ^ m.factorization q5 * abD * (q5 - 1) <
      bSpec * abN * q5 * q5 ^ m.factorization q5 := by
    have h1 : 2 * bSpec * q5 ^ m.factorization q5 < sSpec * sigPP q5 (m.factorization q5) := by
      rw [mul_assoc, ← hsplit_both.1, ← hsplit_both.2]; exact h2m_lt
    have hpos_f : 0 < abD * (q5 - 1) := Nat.mul_pos (Nat.pos_of_ne_zero habD_pos) (Nat.sub_pos_of_lt hq5p.one_lt)
    have h2 : (2 * bSpec * q5 ^ m.factorization q5) * (abD * (q5 - 1)) <
        (sSpec * sigPP q5 (m.factorization q5)) * (abD * (q5 - 1)) := Nat.mul_lt_mul_of_pos_right h1 hpos_f
    have h3 : (sSpec * sigPP q5 (m.factorization q5)) * (abD * (q5 - 1)) ≤
        (bSpec * abN) * (q5 * q5 ^ m.factorization q5) := by
      calc (sSpec * sigPP q5 (m.factorization q5)) * (abD * (q5 - 1))
          = (sSpec * abD) * (sigPP q5 (m.factorization q5) * (q5 - 1)) := by ring
        _ ≤ (bSpec * abN) * (q5 * q5 ^ m.factorization q5) := Nat.mul_le_mul hmax0.2 hsig_q5.le
    nlinarith
  have hq5_ineq : 2 * abD * (q5 - 1) < abN * q5 := by
    have hpos_bq : 0 < bSpec * q5 ^ m.factorization q5 := Nat.mul_pos hbSpec_pos (Nat.pow_pos hq5p.pos)
    nlinarith
  have hq5_le_qMax : q5 ≤ (2 * abD - 1) / (2 * abD - abN) := by
    have hden_pos : 0 < 2 * abD - abN := by omega
    rw [Nat.le_div_iff_mul_le hden_pos]
    zify [show abN ≤ 2 * abD by omega, show 1 ≤ 2 * abD by omega, show 1 ≤ q5 by omega] at hq5_ineq ⊢
    nlinarith
  set others := spec.eraseIdx qi
  have her := eraseIdx_spec spec qi qE hqget
  have hpw_oth : (others.map (·.p)).Pairwise (· < ·) := (her.2.2 _ hs.1).1
  have hnot_q : qE.p ∉ others.map (·.p) := (her.2.2 _ hs.1).2
  have hev_oth : ∀ e ∈ others, EntryValid m minP e := fun e he => hs.2.1 e (her.1 e he)
  obtain ⟨hSeed_oth, _, hqMax_bnd⟩ := checkBaseExt_sound hm_odd others hpw_oth hev_oth sd
    hsv copIdxs false ((2 * abD - 1) / (2 * abD - abN)) (by simp) hbase_ok
  set bOth := (others.map (fun e => e.p ^ m.factorization e.p)).prod
  have hbOth_pos : 0 < bOth := by have := hSeed_oth.1; omega
  have hcop_oth_q5 : bOth.Coprime q5 := by
    refine (hq5p.coprime_iff_not_dvd.mpr fun hdvd => ?_).symm
    obtain ⟨e, he, heq⟩ := (prod_entries_factorization others hpw_oth hev_oth (fun x => m.factorization x.p)).2
      q5 (Nat.mem_primeFactors.mpr ⟨hq5p, hdvd, hbOth_pos.ne'⟩)
    exact hq5_out e (her.1 e he) heq
  have hq5_bnd : 6 * (q5 : ℤ) ≤ PropSum bOth - 127 := by
    have : (q5 : ℤ) ≤ ((2 * abD - 1) / (2 * abD - abN) : ℕ) := by exact_mod_cast hq5_le_qMax
    omega
  obtain ⟨hSeed_b, _⟩ := seedOk_mul_prime_pow hSeed_oth hq5p hcop_oth_q5 hq5_3 hq5_a hq5_bnd
  set b := bOth * q5 ^ m.factorization q5
  have hq_ev := hs.2.1 qE (List.mem_of_getElem? hqget)
  have hq_ne_q5 : qE.p ≠ q5 := fun heq => hq5_out qE (List.mem_of_getElem? hqget) heq
  have hcop_oth_qE : bOth.Coprime qE.p := by
    refine (hq_ev.1.coprime_iff_not_dvd.mpr fun hdvd => ?_).symm
    obtain ⟨e, he, heq⟩ := (prod_entries_factorization others hpw_oth hev_oth (fun x => m.factorization x.p)).2
      qE.p (Nat.mem_primeFactors.mpr ⟨hq_ev.1, hdvd, hbOth_pos.ne'⟩)
    exact hnot_q (heq ▸ List.mem_map_of_mem he)
  have hcop_bq : b.Coprime qE.p :=
    hcop_oth_qE.mul_left ((hq_ev.1.coprime_iff_not_dvd.mpr fun hdvd =>
      hq_ne_q5 ((hq5p.dvd_iff_eq hq_ev.1.ne_one).mp hdvd).symm).symm.pow_left (m.factorization q5))
  have hm_split : m = b * qE.p ^ ((m.factorization qE.p - 1) + 1) := by
    have h1 : 1 ≤ m.factorization qE.p := le_trans hq_ev.2.2.2.2.1 hq_ev.2.2.2.2.2.1
    have hperm := her.2.1 (fun e => e.p ^ m.factorization e.p)
    change bSpec = qE.p ^ m.factorization qE.p * bOth at hperm
    calc m = bSpec * q5 ^ m.factorization q5 := hsplit_both.1
      _ = (qE.p ^ m.factorization qE.p * bOth) * q5 ^ m.factorization q5 := by rw [hperm]
      _ = b * qE.p ^ m.factorization qE.p := by dsimp [b]; ring
      _ = b * qE.p ^ ((m.factorization qE.p - 1) + 1) := by rw [Nat.sub_add_cancel h1]
  have hq3 : 3 ≤ qE.p := by
    have := hq_ev.1.two_le
    have hne2 : qE.p ≠ 2 := fun h => by have := hq_ev.2.2.1; rw [h] at this; exact absurd this (by decide)
    omega
  have hj_ne0 : m.factorization qE.p - 1 = 0 → 2 ≤ (b : ℤ) - PropSum b := fun hj0 => by
    exfalso
    have hf1 : m.factorization qE.p = 1 := by
      have := le_trans hq_ev.2.2.2.2.1 hq_ev.2.2.2.2.2.1; omega
    have hmin1 : qE.minA = 1 := by
      have := hq_ev.2.2.2.2.1; have := hq_ev.2.2.2.2.2.1; omega
    have hpar_odd : qE.par = .odd := by
      cases hp : qE.par
      · rfl
      · have hev := hq_ev.2.2.2.2.2.2.2.1; rw [hp, hf1] at hev; exact absurd hev (by decide)
    simp [hpar_odd, hmin1] at hnot_odd1
  exact false_of_seedOk hm_no hSeed_b hm_split hq_ev.1 hcop_bq hq3 hj_ne0

lemma cert_K3_false {m minP : ℕ} (hm_odd : Odd m) (hm_ab : m.Abundant)
    (hm_card : m.primeFactors.card ≤ 5) (hm_prim : ∀ d ∈ m.properDivisors, d.Deficient)
    (hm_no : NoCertExt m)
    {spec : List Entry} (hs : SpecValid m spec minP true) (hrem2 : 5 - spec.length = 2)
    {sd : Seed} (hsv : SeedValid sd) {copIdxs : List ℕ}
    {abN abD : ℕ} (hmax : maxAbSpec spec minP 0 = (abN, abD))
    (hgd2 : guaranteedD2Ext spec = true) (habD_pos : 0 < abD)
    (hp4_ge2 : 2 ≤ max minP ((sd.p0 - 127) / 6 + 1))
    (hquad : abN * max minP ((sd.p0 - 127) / 6 + 1) * max minP ((sd.p0 - 127) / 6 + 1) ≤
      2 * abD * (max minP ((sd.p0 - 127) / 6 + 1) - 1) * (max minP ((sd.p0 - 127) / 6 + 1) - 1))
    (hbase_ok : checkBaseExt spec sd copIdxs false 0 = true)
    (hnot_all : ¬ ∀ q ∈ m.primeFactors, ∃ e ∈ spec, e.p = q) : False := by
  have hm0 : m ≠ 0 := hm_odd.pos.ne'
  have h2m_lt : 2 * m < sigma 1 m := (abundant_iff_two_mul_lt_sigma m).mp hm_ab
  set S := (spec.map (·.p)).toFinset
  set S_out := m.primeFactors \ S
  have hsub_fin : S ⊆ m.primeFactors := spec_toFinset_subset hm0 hs
  have hcardS : S.card = 3 := by
    rw [spec_toFinset_card hs]
    have := spec_length_le_five hm0 hm_card hs
    omega
  have hcard_Sout : S_out.card ≤ 2 := by
    dsimp [S_out]
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hsub_fin, hcardS]
    omega
  have hSout_ne : S_out.Nonempty := by
    push Not at hnot_all
    obtain ⟨q, hqm, hq_out⟩ := hnot_all
    exact ⟨q, Finset.mem_sdiff.mpr ⟨hqm, fun h => by
      rw [List.mem_toFinset, List.mem_map] at h; obtain ⟨e, he, rfl⟩ := h; exact hq_out e he rfl⟩⟩
  set p4Next := max minP ((sd.p0 - 127) / 6 + 1)
  have hSout_ge : ∀ r ∈ S_out, r.Prime ∧ minP ≤ r := fun r hr => by
    rw [Finset.mem_sdiff] at hr
    have hrp := Nat.prime_of_mem_primeFactors hr.1
    rcases hs.2.2 r hr.1 with ⟨e, he, rfl⟩ | hmin
    · exfalso; exact hr.2 (List.mem_toFinset.mpr (List.mem_map_of_mem he))
    · exact ⟨hrp, hmin⟩
  have hex_lt : ∃ r0 ∈ S_out, r0 < p4Next := by
    by_contra hnone
    push Not at hnone
    have hprod_bound := finset_prod_sigPP_le_of_card_le_two (m := m) hcard_Sout hp4_ge2
      (fun r hr => ⟨(hSout_ge r hr).1, hnone r hr⟩)
    have hsplit_both := prod_spec_factor_split hm0 hs
    have hmax0 := maxAbSpec_zero_sound hs hmax
    have hpos_mul : 0 < abD * (p4Next - 1) ^ 2 :=
      Nat.mul_pos habD_pos (Nat.pow_pos (Nat.sub_pos_of_lt (by omega)))
    have hsig_le : sigma 1 m * (abD * (p4Next - 1) ^ 2) ≤ m * (abN * p4Next ^ 2) := by
      conv_lhs => rw [hsplit_both.2]
      conv_rhs => rw [hsplit_both.1]
      calc ((spec.map (fun e => sigPP e.p (m.factorization e.p))).prod *
              ∏ q ∈ S_out, sigPP q (m.factorization q)) * (abD * (p4Next - 1) ^ 2)
          = ((spec.map (fun e => sigPP e.p (m.factorization e.p))).prod * abD) *
              ((∏ q ∈ S_out, sigPP q (m.factorization q)) * (p4Next - 1) ^ 2) := by ring
        _ ≤ ((spec.map (fun e => e.p ^ m.factorization e.p)).prod * abN) *
              (p4Next ^ 2 * ∏ q ∈ S_out, q ^ m.factorization q) := Nat.mul_le_mul hmax0.2 hprod_bound
        _ = ((spec.map (fun e => e.p ^ m.factorization e.p)).prod *
              ∏ q ∈ S_out, q ^ m.factorization q) * (abN * p4Next ^ 2) := by ring
    have hquad' : abN * p4Next ^ 2 ≤ 2 * (abD * (p4Next - 1) ^ 2) := by
      calc abN * p4Next ^ 2 = abN * p4Next * p4Next := by ring
        _ ≤ 2 * abD * (p4Next - 1) * (p4Next - 1) := hquad
        _ = 2 * (abD * (p4Next - 1) ^ 2) := by ring
    have hsig_le2 : sigma 1 m * (abD * (p4Next - 1) ^ 2) ≤ (2 * m) * (abD * (p4Next - 1) ^ 2) := by
      calc sigma 1 m * (abD * (p4Next - 1) ^ 2)
          ≤ m * (abN * p4Next ^ 2) := hsig_le
        _ ≤ m * (2 * (abD * (p4Next - 1) ^ 2)) := Nat.mul_le_mul_left m hquad'
        _ = (2 * m) * (abD * (p4Next - 1) ^ 2) := by ring
    have := Nat.le_of_mul_le_mul_right hsig_le2 hpos_mul
    omega
  obtain ⟨r0, hr0_mem, hr0_lt⟩ := hex_lt
  have hr0_ge := hSout_ge r0 hr0_mem
  have hr0_bnd_nat : 6 * r0 ≤ sd.p0 - 127 := by
    have : r0 < (sd.p0 - 127) / 6 + 1 := by
      have := hr0_ge.2
      dsimp [p4Next] at hr0_lt
      omega
    have : r0 ≤ (sd.p0 - 127) / 6 := by omega
    exact Nat.le_trans (Nat.mul_le_mul_left 6 this) (Nat.mul_div_le (sd.p0 - 127) 6)
  obtain ⟨hSeed_spec, hP_spec, _⟩ := checkBaseExt_sound hm_odd spec hs.1 hs.2.1 sd
    hsv copIdxs false 0 (by simp) hbase_ok
  set bSpec := (spec.map (fun e => e.p ^ m.factorization e.p)).prod
  have hbSpec_pos : 0 < bSpec := by have := hSeed_spec.1; omega
  have hr0_in_m : r0 ∈ m.primeFactors := (Finset.mem_sdiff.mp hr0_mem).1
  have hr0_notS : r0 ∉ S := (Finset.mem_sdiff.mp hr0_mem).2
  have hr0_dvd : r0 ∣ m := Nat.dvd_of_mem_primeFactors hr0_in_m
  have hr0_3 : 3 ≤ r0 := by
    have := hr0_ge.1.two_le
    have hne2 : r0 ≠ 2 := fun h => hm_odd.not_two_dvd_nat (h ▸ hr0_dvd)
    omega
  have hr0_a : 1 ≤ m.factorization r0 := hr0_ge.1.factorization_pos_of_dvd hm0 hr0_dvd
  have hcop_spec_r0 : bSpec.Coprime r0 := by
    refine (hr0_ge.1.coprime_iff_not_dvd.mpr fun hdvd => ?_).symm
    obtain ⟨e, he, heq⟩ := (prod_entries_factorization spec hs.1 hs.2.1 (fun x => m.factorization x.p)).2
      r0 (Nat.mem_primeFactors.mpr ⟨hr0_ge.1, hdvd, hbSpec_pos.ne'⟩)
    exact hr0_notS (heq ▸ List.mem_toFinset.mpr (List.mem_map_of_mem he))
  have hfac_spec := (prod_entries_factorization spec hs.1 hs.2.1 (fun x => m.factorization x.p)).1
  have hm_split_raw := (prod_spec_factor_split hm0 hs).1
  by_cases hrem_empty : S_out.erase r0 = ∅
  · have hSout_eq : S_out = {r0} := by
      have h1 := Finset.insert_erase hr0_mem
      rw [hrem_empty] at h1
      simpa using h1.symm
    have hprod_eq : ∏ q ∈ m.primeFactors \ (spec.map (·.p)).toFinset, q ^ m.factorization q = r0 ^ m.factorization r0 := by
      change ∏ q ∈ S_out, q ^ m.factorization q = _
      rw [hSout_eq, Finset.prod_singleton]
    rw [hprod_eq] at hm_split_raw
    have hm_split : m = bSpec * r0 ^ ((m.factorization r0 - 1) + 1) := by
      rw [Nat.sub_add_cancel hr0_a]; exact hm_split_raw
    have hb_lt_m : bSpec < m := by
      rw [hm_split]; exact lt_mul_of_one_lt_right hbSpec_pos (one_lt_pow₀ (by omega) (Nat.succ_ne_zero _))
    have hb_dvd_m : bSpec ∣ m := by rw [hm_split]; exact dvd_mul_right _ _
    have hb_odd : Odd bSpec := hm_odd.of_dvd_nat hb_dvd_m
    have hb_def : bSpec.Deficient := hm_prim bSpec (Nat.mem_properDivisors.mpr ⟨hb_dvd_m, hb_lt_m⟩)
    have hD2 : m.factorization r0 - 1 = 0 → 2 ≤ (bSpec : ℤ) - PropSum bSpec := fun _ =>
      guaranteedD2Ext_sound hb_odd hb_def spec hs.1
        (fun e he => let ev := hs.2.1 e he; let hfe := (hfac_spec e he).symm;
          ⟨ev.1, pow_one e.p ▸ (Nat.Prime.pow_dvd_iff_le_factorization ev.1 hbSpec_pos.ne').mpr (by rw [← hfe]; exact le_trans ev.2.2.2.2.1 ev.2.2.2.2.2.1),
           hfe ▸ ev.2.2.2.2.2.1, fun hx => hfe ▸ ev.2.2.2.2.2.2.1 hx,
           fun hpar => by have hp_m := ev.2.2.2.2.2.2.2.1; rw [hpar] at hp_m; rwa [← hfe]⟩) hgd2
    exact false_of_seedOk hm_no hSeed_spec hm_split hr0_ge.1 hcop_spec_r0 hr0_3 hD2
  · have hrem_card : (S_out.erase r0).card = 1 := by
      have hne := Finset.nonempty_iff_ne_empty.mpr hrem_empty
      have h1 := Finset.card_erase_of_mem hr0_mem
      have := hne.card_pos
      omega
    obtain ⟨q5, hq5_eq⟩ := Finset.card_eq_one.mp hrem_card
    have hq5_in_erase : q5 ∈ S_out.erase r0 := by rw [hq5_eq]; exact Finset.mem_singleton_self q5
    have hq5_ne_r0 : q5 ≠ r0 := (Finset.mem_erase.mp hq5_in_erase).1
    have hq5_mem : q5 ∈ S_out := (Finset.mem_erase.mp hq5_in_erase).2
    have hq5_in_m : q5 ∈ m.primeFactors := (Finset.mem_sdiff.mp hq5_mem).1
    have hq5_notS : q5 ∉ S := (Finset.mem_sdiff.mp hq5_mem).2
    have hq5_ge := hSout_ge q5 hq5_mem
    have hq5_dvd : q5 ∣ m := Nat.dvd_of_mem_primeFactors hq5_in_m
    have hq5_3 : 3 ≤ q5 := by
      have := hq5_ge.1.two_le
      have hne2 : q5 ≠ 2 := fun h => hm_odd.not_two_dvd_nat (h ▸ hq5_dvd)
      omega
    have hq5_a : 1 ≤ m.factorization q5 := hq5_ge.1.factorization_pos_of_dvd hm0 hq5_dvd
    have hSout_eq : S_out = insert q5 {r0} := by
      have h1 := Finset.insert_erase hr0_mem
      rw [hq5_eq] at h1
      rw [← h1, Finset.pair_comm]
    have hr0_bnd_z : 6 * (r0 : ℤ) ≤ PropSum bSpec - 127 := by
      have h127 : (127 : ℤ) ≤ sd.p0 := by
        have := hsv.2.2.2.2.1.2.2.1
        rw [hsv.2.2.2.1] at this
        omega
      have : 6 * (r0 : ℤ) ≤ (sd.p0 : ℤ) - 127 := by omega
      linarith
    obtain ⟨hSeed_b, _⟩ := seedOk_mul_prime_pow hSeed_spec hr0_ge.1 hcop_spec_r0 hr0_3 hr0_a hr0_bnd_z
    set b := bSpec * r0 ^ m.factorization r0
    have hm_split : m = b * q5 ^ ((m.factorization q5 - 1) + 1) := by
      have hprod_eq : ∏ q ∈ m.primeFactors \ (spec.map (·.p)).toFinset, q ^ m.factorization q =
          q5 ^ m.factorization q5 * r0 ^ m.factorization r0 := by
        change ∏ q ∈ S_out, q ^ m.factorization q = _
        rw [hSout_eq, Finset.prod_insert (by simpa using hq5_ne_r0), Finset.prod_singleton]
      rw [hprod_eq] at hm_split_raw
      rw [Nat.sub_add_cancel hq5_a]
      calc m = bSpec * (q5 ^ m.factorization q5 * r0 ^ m.factorization r0) := hm_split_raw
        _ = (bSpec * r0 ^ m.factorization r0) * q5 ^ m.factorization q5 := by ring
    have hcop_spec_q5 : bSpec.Coprime q5 := by
      refine (hq5_ge.1.coprime_iff_not_dvd.mpr fun hdvd => ?_).symm
      obtain ⟨e, he, heq⟩ := (prod_entries_factorization spec hs.1 hs.2.1 (fun x => m.factorization x.p)).2
        q5 (Nat.mem_primeFactors.mpr ⟨hq5_ge.1, hdvd, hbSpec_pos.ne'⟩)
      exact hq5_notS (heq ▸ List.mem_toFinset.mpr (List.mem_map_of_mem he))
    have hcop_bq : b.Coprime q5 :=
      hcop_spec_q5.mul_left ((hq5_ge.1.coprime_iff_not_dvd.mpr fun hdvd =>
        hq5_ne_r0 ((hr0_ge.1.dvd_iff_eq hq5_ge.1.ne_one).mp hdvd).symm).symm.pow_left (m.factorization r0))
    have hb_pos : 0 < b := by have := hSeed_b.1; omega
    have hb_lt_m : b < m := by
      rw [hm_split]; exact lt_mul_of_one_lt_right hb_pos (one_lt_pow₀ (by omega) (Nat.succ_ne_zero _))
    have hb_dvd_m : b ∣ m := by rw [hm_split]; exact dvd_mul_right _ _
    have hb_odd : Odd b := hm_odd.of_dvd_nat hb_dvd_m
    have hb_def : b.Deficient := hm_prim b (Nat.mem_properDivisors.mpr ⟨hb_dvd_m, hb_lt_m⟩)
    have hfac_b_eq : ∀ e ∈ spec, b.factorization e.p = m.factorization e.p := fun e he => by
      have hne : e.p ≠ r0 := fun heq => hr0_notS (heq ▸ List.mem_toFinset.mpr (List.mem_map_of_mem he))
      rw [Nat.factorization_mul hbSpec_pos.ne' (Nat.pow_pos hr0_ge.1.pos).ne', Finsupp.coe_add, Pi.add_apply,
          hr0_ge.1.factorization_pow, Finsupp.single_eq_of_ne hne, add_zero, hfac_spec e he]
    have hD2 : m.factorization q5 - 1 = 0 → 2 ≤ (b : ℤ) - PropSum b := fun _ =>
      guaranteedD2Ext_sound hb_odd hb_def spec hs.1
        (fun e he => let ev := hs.2.1 e he; let hfe := hfac_b_eq e he;
          ⟨ev.1, pow_one e.p ▸ (Nat.Prime.pow_dvd_iff_le_factorization ev.1 hb_pos.ne').mpr (by rw [hfe]; exact le_trans ev.2.2.2.2.1 ev.2.2.2.2.2.1),
           hfe ▸ ev.2.2.2.2.2.1, fun hx => hfe ▸ ev.2.2.2.2.2.2.1 hx,
           fun hpar => by have hp_m := ev.2.2.2.2.2.2.2.1; rw [hpar] at hp_m; rwa [hfe]⟩) hgd2
    exact false_of_seedOk hm_no hSeed_b hm_split hq5_ge.1 hcop_bq hq5_3 hD2

lemma nextPrime_rem_dvd {m minP p : ℕ} {spec : List Entry}
    (hs : SpecValid m spec minP true) (hnp : nextPrime minP = some p) :
    (∀ q ∈ m.primeFactors, (∃ e ∈ spec, e.p = q) ∨ q = p ∨ p + 1 ≤ q) ∧
    (¬ p ∣ m → ∀ q ∈ m.primeFactors, (∃ e ∈ spec, e.p = q) ∨ p + 1 ≤ q) := by
  obtain ⟨_, _, hmin_p⟩ := nextPrime_spec hnp
  refine ⟨fun q hq => ?_, fun hdvd q hq => ?_⟩
  · rcases hs.2.2 q hq with hspec | hge
    · left; exact hspec
    · rcases lt_trichotomy q p with hlt | rfl | hgt
      · exfalso; exact hmin_p q hge hlt (Nat.prime_of_mem_primeFactors hq)
      · right; left; rfl
      · right; right; exact hgt
  · rcases hs.2.2 q hq with hspec | hge
    · left; exact hspec
    · right
      rcases lt_trichotomy q p with hlt | rfl | hgt
      · exfalso; exact hmin_p q hge hlt (Nat.prime_of_mem_primeFactors hq)
      · exfalso; exact hdvd (Nat.dvd_of_mem_primeFactors hq)
      · exact hgt

lemma checkCert_sound {m : ℕ} (hm_odd : Odd m) (hm_ab : m.Abundant)
    (hm_card : m.primeFactors.card ≤ 5) (hm_prim : ∀ d ∈ m.properDivisors, d.Deficient)
    (hm_E : 64 ≤ (sigma 1 m : ℤ) - 2 * (m : ℤ)) (hm_no : NoCertExt m)
    (seeds : List Seed) (hSeeds : ∀ s ∈ seeds, SeedValid s)
    (survs : List (ℕ × List ℕ)) :
    ∀ fuel c allowMore spec minP,
      checkCert seeds survs allowMore fuel c spec minP = true →
      SpecValid m spec minP allowMore →
      (∀ (idx : ℕ) (mv : ℕ) (xs : List ℕ), survs[idx]? = some (mv, xs) →
        mv = m → checkSurv m (sigma 1 m) xs = true → m.Pseudoperfect) →
      m.Pseudoperfect := by
  intro fuel
  have hm_pos : 0 < m := hm_odd.pos
  have hm0 : m ≠ 0 := hm_pos.ne'
  have h2m_lt : 2 * m < sigma 1 m := (abundant_iff_two_mul_lt_sigma m).mp hm_ab
  induction fuel with
  | zero => intro _ _ _ _ h; simp [checkCert] at h
  | succ fuel ih =>
    intro c allowMore spec minP hchk hs hSurvFn
    have hSeeds_get : ∀ i s, seeds[i]? = some s → SeedValid s := fun i s hget =>
      hSeeds s (List.mem_of_getElem? hget)
    unfold checkCert at hchk
    cases c with
    | B =>
      dsimp only at hchk
      rcases hmax : maxAbSpec spec minP (if allowMore then 5 - spec.length else 0) with ⟨n, d⟩
      rw [hmax] at hchk
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hchk
      have hbound := maxAbSpec_sound hm0 hm_card hs rfl hmax hchk.1
      exfalso; nlinarith
    | AL =>
      dsimp only at hchk
      rw [minNumAb_eq spec] at hchk
      dsimp only at hchk
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hchk
      obtain ⟨hb_pos, hb_dvd, hb_sig⟩ :=
        prod_entries_dvd_and_sigma hm0 spec hs.1 hs.2.1 (·.minA) (fun e he => (hs.2.1 e he).2.2.2.2.2.1)
      set b := (spec.map (fun e => e.p ^ e.minA)).prod
      by_cases hbm : b = m
      · subst hbm; rw [← hb_sig] at hchk; exfalso; omega
      · exfalso
        have hprop : b ∈ m.properDivisors :=
          Nat.mem_properDivisors.mpr ⟨hb_dvd, lt_of_le_of_ne (Nat.le_of_dvd hm_pos hb_dvd) hbm⟩
        have hdef := (deficient_iff_sigma_lt_two_mul _).mp (hm_prim b hprop)
        rw [hb_sig] at hdef; omega
    | NP qi =>
      exact False.elim (cert_NP_sound hm_pos hm_prim hs hchk)
    | AS idx =>
      dsimp only at hchk
      rw [minNumAb_eq spec] at hchk
      dsimp only at hchk
      split_ifs at hchk with hle_ab
      rcases hget : survs[idx]? with _ | ⟨mv, xs⟩
      · rw [hget] at hchk; simp at hchk
      · rw [hget] at hchk
        simp only [Bool.and_eq_true, beq_iff_eq] at hchk
        obtain ⟨hvm, hsurv⟩ := hchk
        obtain ⟨hb_pos, hb_dvd, hb_sig⟩ :=
          prod_entries_dvd_and_sigma hm0 spec hs.1 hs.2.1 (·.minA) (fun e he => (hs.2.1 e he).2.2.2.2.2.1)
        have hbm : (spec.map (fun e => e.p ^ e.minA)).prod = m := by
          by_contra hne
          have hprop : (spec.map (fun e => e.p ^ e.minA)).prod ∈ m.properDivisors :=
            Nat.mem_properDivisors.mpr ⟨hb_dvd, lt_of_le_of_ne (Nat.le_of_dvd hm_pos hb_dvd) hne⟩
          have hdef := (deficient_iff_sigma_lt_two_mul _).mp (hm_prim _ hprop)
          rw [hb_sig] at hdef; omega
        rw [hbm] at hvm
        rw [← hb_sig, hbm] at hsurv
        exact hSurvFn idx mv xs hget hvm hsurv
    | AC qi si copIdxs =>
      exact False.elim (cert_AC_sound hm_odd hm_prim hm_no seeds hSeeds_get hs hchk)
    | KR qi si copIdxs =>
      exact False.elim (cert_KR_sound hm_odd hm_card hm_prim hm_no seeds hSeeds_get hs hchk)
    | K5 si copIdxs sub =>
      dsimp only at hchk
      simp only [Bool.and_eq_true, beq_iff_eq] at hchk
      obtain ⟨⟨ham_t, hrem1⟩, hmatch⟩ := hchk
      rcases hsget : seeds[si]? with _ | sd
      · rw [hsget] at hmatch; simp at hmatch
      · rw [hsget] at hmatch
        simp only [Bool.and_eq_true] at hmatch
        obtain ⟨⟨hgd2, hbase_ok⟩, hsub_ok⟩ := hmatch
        by_cases hall_p : ∀ q ∈ m.primeFactors, ∃ e ∈ spec, e.p = q
        · exact ih sub false spec minP hsub_ok ⟨hs.1, hs.2.1, hall_p⟩ hSurvFn
        · exact False.elim (cert_K5_false hm_odd hm_card hm_prim hm_no hs hrem1
            (hSeeds_get si sd hsget) hgd2 hbase_ok hall_p)
    | KV qi si copIdxs sub =>
      dsimp only at hchk
      simp only [Bool.and_eq_true, beq_iff_eq] at hchk
      obtain ⟨⟨ham_t, hrem1⟩, hrest⟩ := hchk
      rcases hmax : maxAbSpec spec minP 0 with ⟨abN, abD⟩
      rw [hmax] at hrest
      dsimp only at hrest
      split_ifs at hrest with hbad
      have hbad_f : abD ≠ 0 ∧ abN < 2 * abD := by
        simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq, not_or, not_le] at hbad
        exact hbad
      rcases hqget : spec[qi]? with _ | qE
      · rw [hqget] at hrest; simp at hrest
      · rcases hsget : seeds[si]? with _ | sd
        · rw [hqget, hsget] at hrest; simp at hrest
        · rw [hqget, hsget] at hrest
          simp only [Bool.and_eq_true, Bool.not_eq_true'] at hrest
          obtain ⟨⟨hnot_odd1, hbase_ok⟩, hsub_ok⟩ := hrest
          by_cases hall_p : ∀ q ∈ m.primeFactors, ∃ e ∈ spec, e.p = q
          · exact ih sub false spec minP hsub_ok ⟨hs.1, hs.2.1, hall_p⟩ hSurvFn
          · exact False.elim (cert_KV_false hm_odd hm_ab hm_card hm_no hs hrem1 hmax
              hbad_f.1 hbad_f.2 hqget (hSeeds_get si sd hsget) (by simp [hnot_odd1]) hbase_ok hall_p)
    | K3 si copIdxs sub =>
      dsimp only at hchk
      simp only [Bool.and_eq_true, beq_iff_eq] at hchk
      obtain ⟨⟨ham_t, hrem2⟩, hrest⟩ := hchk
      subst ham_t
      rcases hsget : seeds[si]? with _ | sd
      · rw [hsget] at hrest; simp at hrest
      · rw [hsget] at hrest
        rcases hmax : maxAbSpec spec minP 0 with ⟨abN, abD⟩
        dsimp only at hrest
        rw [hmax] at hrest
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hrest
        obtain ⟨⟨⟨⟨⟨hgd2, habD_pos⟩, hp4_ge2⟩, hquad⟩, hbase_ok⟩, hsub_ok⟩ := hrest
        by_cases hall_p : ∀ q ∈ m.primeFactors, ∃ e ∈ spec, e.p = q
        · exact ih sub false spec minP hsub_ok ⟨hs.1, hs.2.1, hall_p⟩ hSurvFn
        · exact False.elim (cert_K3_false hm_odd hm_ab hm_card hm_prim hm_no hs hrem2
            (hSeeds_get si sd hsget) hmax hgd2 habD_pos hp4_ge2 hquad hbase_ok hall_p)
    | SF idx cEx cHi =>
      dsimp only at hchk
      rcases hget : spec[idx]? with _ | e
      · rw [hget] at hchk; simp at hchk
      · rw [hget] at hchk
        simp only [Bool.and_eq_true, Bool.not_eq_true'] at hchk
        obtain ⟨⟨_, hEx_ok⟩, hHi_ok⟩ := hchk
        have he_ev := hs.2.1 e (List.mem_of_getElem? hget)
        by_cases hex : m.factorization e.p = e.minA
        · set e' : Entry := { e with exact := true }
          have hls := listSet_spec spec idx e e' hget rfl
          have hs' : SpecValid m (listSet spec idx e') minP allowMore := by
            refine ⟨by rw [hls.1]; exact hs.1, fun x hx => ?_, ?_⟩
            · rcases hls.2.1 x hx with rfl | hx_orig
              · exact ⟨he_ev.1, he_ev.2.1, he_ev.2.2.1, he_ev.2.2.2.1, he_ev.2.2.2.2.1,
                  he_ev.2.2.2.2.2.1, fun _ => hex, he_ev.2.2.2.2.2.2.2.1, he_ev.2.2.2.2.2.2.2.2⟩
              · exact hs.2.1 x hx_orig
            · have hmap_eq : ∀ q, (∃ x ∈ listSet spec idx e', x.p = q) ↔ (∃ x ∈ spec, x.p = q) := fun q => by
                simpa [List.mem_map] using congrArg (q ∈ ·) hls.1
              cases allowMore
              · simpa [hmap_eq] using hs.2.2
              · simpa [hmap_eq] using hs.2.2
          exact ih cEx allowMore (listSet spec idx e') minP hEx_ok hs' hSurvFn
        · let e' : Entry := { e with minA := e.minA + 2 }
          have hls := listSet_spec spec idx e e' hget rfl
          have hle2 : e.minA + 2 ≤ m.factorization e.p := by
            have := he_ev.2.2.2.2.2.1
            have := he_ev.2.2.2.2.2.2.2.2
            omega
          have hs' : SpecValid m (listSet spec idx e') minP allowMore := by
            refine ⟨by rw [hls.1]; exact hs.1, fun x hx => ?_, ?_⟩
            · rcases hls.2.1 x hx with rfl | hx_orig
              · dsimp only [e']
                exact ⟨he_ev.1, he_ev.2.1, he_ev.2.2.1, he_ev.2.2.2.1, by change 1 ≤ e.minA + 2; omega,
                  hle2, fun h => absurd h (by
                    intro htrue
                    exact hex (he_ev.2.2.2.2.2.2.1 htrue)),
                  he_ev.2.2.2.2.2.2.2.1, by change (e.minA + 2) % 2 = m.factorization e.p % 2; have := he_ev.2.2.2.2.2.2.2.2; omega⟩
              · exact hs.2.1 x hx_orig
            · have hmap_eq : ∀ q, (∃ x ∈ listSet spec idx e', x.p = q) ↔ (∃ x ∈ spec, x.p = q) := fun q => by
                simpa [List.mem_map] using congrArg (q ∈ ·) hls.1
              cases allowMore
              · simpa [hmap_eq] using hs.2.2
              · simpa [hmap_eq] using hs.2.2
          exact ih cHi allowMore (listSet spec idx e') minP hHi_ok hs' hSurvFn
    | S7 p c0 c1 c2 c3 c4 =>
      dsimp only at hchk
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hchk
      obtain ⟨⟨⟨⟨⟨⟨⟨ham_t, hnp⟩, _⟩, hc0⟩, hc1⟩, hc2⟩, hc3⟩, hc4⟩ := hchk
      subst ham_t
      obtain ⟨hminp, hp, _⟩ := nextPrime_spec hnp
      obtain ⟨hrem, hrem0⟩ := nextPrime_rem_dvd hs hnp
      by_cases hdvd : p ∣ m
      · have hp_odd : Odd p := hm_odd.of_dvd_nat hdvd
        have h1 : 1 ≤ m.factorization p := hp.factorization_pos_of_dvd hm0 hdvd
        by_cases hf1 : m.factorization p = 1
        · exact ih c1 true (spec ++ [⟨p, 1, true, .odd⟩]) (p + 1) hc1
            (specValid_ext hs hp hminp hp_odd hdvd le_rfl (by omega) (fun _ => hf1)
              (by rw [hf1]; exact odd_one) (by rw [hf1]) hrem) hSurvFn
        · by_cases hf2 : m.factorization p = 2
          · exact ih c2 true (spec ++ [⟨p, 2, true, .even⟩]) (p + 1) hc2
              (specValid_ext hs hp hminp hp_odd hdvd (by omega) (by omega) (fun _ => hf2)
                (by rw [hf2]; exact even_two) (by rw [hf2]) hrem) hSurvFn
          · rcases Nat.even_or_odd (m.factorization p) with heven | hodd
            · have hf4 : 4 ≤ m.factorization p := by obtain ⟨k, hk⟩ := heven; omega
              exact ih c4 true (spec ++ [⟨p, 4, false, .even⟩]) (p + 1) hc4
                (specValid_ext hs hp hminp hp_odd hdvd (by omega) hf4 (by simp)
                  (by simpa using heven) (by obtain ⟨k, hk⟩ := heven; omega) hrem) hSurvFn
            · have hf3 : 3 ≤ m.factorization p := by obtain ⟨k, hk⟩ := hodd; omega
              exact ih c3 true (spec ++ [⟨p, 3, false, .odd⟩]) (p + 1) hc3
                (specValid_ext hs hp hminp hp_odd hdvd (by omega) hf3 (by simp)
                  (by simpa using hodd) (by obtain ⟨k, hk⟩ := hodd; omega) hrem) hSurvFn
      · exact ih c0 true spec (p + 1) hc0 (specValid_mono_minP hs (by omega) (hrem0 hdvd)) hSurvFn
    | SP p c0 c1 c2 c3 =>
      dsimp only at hchk
      simp only [Bool.and_eq_true, beq_iff_eq] at hchk
      obtain ⟨⟨⟨⟨⟨ham_t, hnp⟩, hc0⟩, hc1⟩, hc2⟩, hc3⟩ := hchk
      subst ham_t
      obtain ⟨hminp, hp, _⟩ := nextPrime_spec hnp
      obtain ⟨hrem, hrem0⟩ := nextPrime_rem_dvd hs hnp
      by_cases hdvd : p ∣ m
      · have hp_odd : Odd p := hm_odd.of_dvd_nat hdvd
        have h1 : 1 ≤ m.factorization p := hp.factorization_pos_of_dvd hm0 hdvd
        by_cases hf1 : m.factorization p = 1
        · exact ih c1 true (spec ++ [⟨p, 1, true, .odd⟩]) (p + 1) hc1
            (specValid_ext hs hp hminp hp_odd hdvd le_rfl (by omega) (fun _ => hf1)
              (by rw [hf1]; exact odd_one) (by rw [hf1]) hrem) hSurvFn
        · rcases Nat.even_or_odd (m.factorization p) with heven | hodd
          · have hf2 : 2 ≤ m.factorization p := by obtain ⟨k, hk⟩ := heven; omega
            exact ih c2 true (spec ++ [⟨p, 2, false, .even⟩]) (p + 1) hc2
              (specValid_ext hs hp hminp hp_odd hdvd (by omega) hf2 (by simp)
                (by simpa using heven) (by obtain ⟨k, hk⟩ := heven; omega) hrem) hSurvFn
          · have hf3 : 3 ≤ m.factorization p := by obtain ⟨k, hk⟩ := hodd; omega
            exact ih c3 true (spec ++ [⟨p, 3, false, .odd⟩]) (p + 1) hc3
              (specValid_ext hs hp hminp hp_odd hdvd (by omega) hf3 (by simp)
                (by simpa using hodd) (by obtain ⟨k, hk⟩ := hodd; omega) hrem) hSurvFn
      · exact ih c0 true spec (p + 1) hc0 (specValid_mono_minP hs (by omega) (hrem0 hdvd)) hSurvFn

-- =====================================================================
-- Root lemmas & main H2 combinator
-- =====================================================================

lemma three_dvd_of_odd_abundant {m : ℕ} (hm_odd : Odd m) (hm_ab : m.Abundant)
    (hm_card : m.primeFactors.card ≤ 5) : 3 ∣ m := by
  by_contra h3
  have hm0 : m ≠ 0 := hm_odd.pos.ne'
  have hs : SpecValid m [] 5 true := by
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
  have hbound := maxAbSpec_sound hm0 hm_card hs rfl hmax (by omega)
  have h2m_lt : 2 * m < sigma 1 m := (abundant_iff_two_mul_lt_sigma m).mp hm_ab
  omega

lemma root_specValid {m : ℕ} (hm_odd : Odd m) (h3 : 3 ∣ m) :
    (m.factorization 3 = 1 ∧ SpecValid m [⟨3, 1, true, .odd⟩] 5 true) ∨
    (m.factorization 3 = 2 ∧ SpecValid m [⟨3, 2, true, .even⟩] 5 true) ∨
    (3 ≤ m.factorization 3 ∧ Odd (m.factorization 3) ∧ SpecValid m [⟨3, 3, false, .odd⟩] 5 true) ∨
    (4 ≤ m.factorization 3 ∧ Even (m.factorization 3) ∧ SpecValid m [⟨3, 4, false, .even⟩] 5 true) := by
  have hm0 : m ≠ 0 := hm_odd.pos.ne'
  have h3p : Nat.Prime 3 := by decide
  have h3odd : Odd 3 := by decide
  have hfac : 1 ≤ m.factorization 3 := h3p.factorization_pos_of_dvd hm0 h3
  have hbase : SpecValid m [] 3 true := ⟨List.Pairwise.nil, by simp, fun q hq => by
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
    have h3_1 : SpecValid m [⟨3, 1, true, .odd⟩] 4 true :=
      specValid_ext hbase h3p le_rfl h3odd h3 le_rfl hfac (fun _ => h1) (by rw [h1]; exact odd_one) (by rw [h1]) hrem3
    exact ⟨h1, specValid_mono_minP h3_1 (by omega) (hrem5 1 true .odd)⟩
  · by_cases h2 : m.factorization 3 = 2
    · right; left
      have h3_2 : SpecValid m [⟨3, 2, true, .even⟩] 4 true :=
        specValid_ext hbase h3p le_rfl h3odd h3 (by omega) (by omega) (fun _ => h2) (by rw [h2]; exact even_two) (by rw [h2]) hrem3
      exact ⟨h2, specValid_mono_minP h3_2 (by omega) (hrem5 2 true .even)⟩
    · rcases Nat.even_or_odd (m.factorization 3) with heven | hodd
      · right; right; right
        have h4 : 4 ≤ m.factorization 3 := by obtain ⟨k, hk⟩ := heven; omega
        have h3_4 : SpecValid m [⟨3, 4, false, .even⟩] 4 true :=
          specValid_ext hbase h3p le_rfl h3odd h3 (by omega) h4 (by simp) (by simpa using heven) (by obtain ⟨k, hk⟩ := heven; omega) hrem3
        exact ⟨h4, heven, specValid_mono_minP h3_4 (by omega) (hrem5 4 false .even)⟩
      · right; right; left
        have h3_ge : 3 ≤ m.factorization 3 := by obtain ⟨k, hk⟩ := hodd; omega
        have h3_3 : SpecValid m [⟨3, 3, false, .odd⟩] 4 true :=
          specValid_ext hbase h3p le_rfl h3odd h3 (by omega) h3_ge (by simp) (by simpa using hodd) (by obtain ⟨k, hk⟩ := hodd; omega) hrem3
        exact ⟨h3_ge, hodd, specValid_mono_minP h3_3 (by omega) (hrem5 3 false .odd)⟩

lemma prove_H2_from_certs (seeds : List Seed) (survs : List (ℕ × List ℕ))
    (c1 c2 c3 c4 : Cert)
    (hSeeds : ∀ s ∈ seeds, SeedValid s)
    (hc1 : checkCert seeds survs true 200 c1 [⟨3, 1, true, .odd⟩] 5 = true)
    (hc2 : checkCert seeds survs true 200 c2 [⟨3, 2, true, .even⟩] 5 = true)
    (hc3 : checkCert seeds survs true 200 c3 [⟨3, 3, false, .odd⟩] 5 = true)
    (hc4 : checkCert seeds survs true 200 c4 [⟨3, 4, false, .even⟩] 5 = true) :
    OMA.R_Erdos470_erdos_470_variants_odd_weird_prime_div_R1_H2_R1.H2 := by
  intro m hm_odd hm_ab hm_card hm_prim _ _ hm_E hm_no
  have h3 : 3 ∣ m := three_dvd_of_odd_abundant hm_odd hm_ab hm_card
  have hSurvFn : ∀ (idx : ℕ) (mv : ℕ) (xs : List ℕ), survs[idx]? = some (mv, xs) →
      mv = m → checkSurv m (sigma 1 m) xs = true → m.Pseudoperfect :=
    fun _ _ xs _ _ hchk => checkSurv_sound hm_odd.pos rfl xs hchk
  rcases root_specValid hm_odd h3 with ⟨_, hs1⟩ | ⟨_, hs2⟩ | ⟨_, _, hs3⟩ | ⟨_, _, hs4⟩
  · exact checkCert_sound hm_odd hm_ab hm_card hm_prim hm_E hm_no seeds hSeeds survs
      200 c1 true [⟨3, 1, true, .odd⟩] 5 hc1 hs1 hSurvFn
  · exact checkCert_sound hm_odd hm_ab hm_card hm_prim hm_E hm_no seeds hSeeds survs
      200 c2 true [⟨3, 2, true, .even⟩] 5 hc2 hs2 hSurvFn
  · exact checkCert_sound hm_odd hm_ab hm_card hm_prim hm_E hm_no seeds hSeeds survs
      200 c3 true [⟨3, 3, false, .odd⟩] 5 hc3 hs3 hSurvFn
  · exact checkCert_sound hm_odd hm_ab hm_card hm_prim hm_E hm_no seeds hSeeds survs
      200 c4 true [⟨3, 4, false, .even⟩] 5 hc4 hs4 hSurvFn

-- =====================================================================
-- Certified seed chunks, survivor table, and branch certificates
-- =====================================================================

def sch0 : List Seed := [⟨[(3,1),(5,1),(7,1),(13,2)],91,17391,[13]⟩, ⟨[(3,1),(5,1),(7,1),(13,3)],91,226275,[13]⟩, ⟨[(3,1),(5,1),(7,1),(17,2)],85,28599,[17]⟩, ⟨[(3,1),(5,1),(7,1),(17,3)],85,486375,[17]⟩, ⟨[(3,1),(5,1),(7,1),(19,2)],95,35247,[19]⟩, ⟨[(3,1),(5,1),(7,1),(19,3)],95,669885,[19]⟩, ⟨[(3,1),(5,1),(7,1),(29,1)],105,2715,[]⟩, ⟨[(3,1),(5,1),(7,1),(31,1)],105,2889,[]⟩, ⟨[(3,1),(5,1),(7,1),(31,2)],105,89751,[]⟩, ⟨[(3,1),(5,1),(7,1),(41,1)],123,3759,[]⟩, ⟨[(3,1),(5,1),(7,1),(43,1)],129,3933,[]⟩, ⟨[(3,1),(5,1),(7,1),(47,1)],141,4281,[]⟩, ⟨[(3,1),(5,1),(7,1),(61,1)],183,5499,[]⟩, ⟨[(3,1),(5,1),(7,1),(67,1)],335,6021,[]⟩, ⟨[(3,1),(5,1),(7,2),(17,1)],85,12129,[]⟩]
theorem schOk0 : sch0.all checkSeedFull = true := by decide +kernel
def sch1 : List Seed := [⟨[(3,1),(5,1),(7,2),(17,2)],85,207561,[17]⟩, ⟨[(3,1),(5,1),(7,2),(17,3)],85,3529905,[17]⟩, ⟨[(3,1),(5,1),(7,2),(19,1)],95,13395,[]⟩, ⟨[(3,1),(5,1),(7,2),(19,2)],95,255873,[19]⟩, ⟨[(3,1),(5,1),(7,2),(19,3)],95,4862955,[19]⟩, ⟨[(3,1),(5,1),(7,2),(23,1)],105,15927,[]⟩, ⟨[(3,1),(5,1),(7,2),(23,2)],105,367689,[23]⟩, ⟨[(3,1),(5,1),(7,2),(23,3)],105,8458215,[23]⟩, ⟨[(3,1),(5,1),(7,3),(17,1)],85,85335,[7]⟩, ⟨[(3,1),(5,1),(7,3),(17,2)],85,1460295,[7,17]⟩, ⟨[(3,1),(5,1),(7,3),(17,3)],85,24834615,[7,17]⟩, ⟨[(3,1),(5,1),(7,3),(19,1)],95,94245,[7]⟩, ⟨[(3,1),(5,1),(7,3),(19,2)],95,1800255,[7,19]⟩, ⟨[(3,1),(5,1),(7,3),(19,3)],95,34214445,[7,19]⟩, ⟨[(3,1),(5,1),(7,3),(23,1)],105,112065,[7]⟩]
theorem schOk1 : sch1.all checkSeedFull = true := by decide +kernel
def sch2 : List Seed := [⟨[(3,1),(5,1),(7,3),(23,2)],105,2587095,[7,23]⟩, ⟨[(3,1),(5,1),(7,3),(23,3)],105,59512785,[7,23]⟩, ⟨[(3,1),(5,1),(7,4),(17,1)],85,597777,[7]⟩, ⟨[(3,1),(5,1),(7,4),(17,2)],85,10229433,[7,17]⟩, ⟨[(3,1),(5,1),(7,4),(17,3)],85,173967585,[7,17]⟩, ⟨[(3,1),(5,1),(7,4),(19,1)],95,660195,[7]⟩, ⟨[(3,1),(5,1),(7,4),(19,2)],95,12610929,[7,19]⟩, ⟨[(3,1),(5,1),(7,4),(19,3)],95,239674875,[7,19]⟩, ⟨[(3,1),(5,1),(7,4),(23,1)],105,785031,[7]⟩, ⟨[(3,1),(5,1),(7,4),(23,2)],105,18122937,[7,23]⟩, ⟨[(3,1),(5,1),(7,4),(23,3)],105,416894775,[7,23]⟩, ⟨[(3,1),(5,1),(11,1),(13,2)],143,24819,[13]⟩, ⟨[(3,1),(5,1),(11,1),(13,3)],143,322935,[13]⟩, ⟨[(3,1),(5,1),(11,1),(23,1)],115,3117,[]⟩, ⟨[(3,1),(5,1),(11,1),(29,1)],145,3855,[]⟩]
theorem schOk2 : sch2.all checkSeedFull = true := by decide +kernel
def sch3 : List Seed := [⟨[(3,1),(5,1),(11,2),(13,1)],121,21093,[11]⟩, ⟨[(3,1),(5,1),(11,2),(13,2)],121,277401,[11,13]⟩, ⟨[(3,1),(5,1),(11,2),(13,3)],121,3609405,[11,13]⟩, ⟨[(3,1),(5,1),(11,3),(13,1)],121,232359,[11]⟩, ⟨[(3,1),(5,1),(11,3),(13,2)],121,3055803,[11,13]⟩, ⟨[(3,1),(5,1),(11,3),(13,3)],121,39760575,[11,13]⟩, ⟨[(3,1),(5,2),(7,1),(19,1)],75,9865,[]⟩, ⟨[(3,1),(5,2),(7,1),(19,2)],75,188427,[19]⟩, ⟨[(3,1),(5,2),(7,1),(19,3)],75,3581105,[19]⟩, ⟨[(3,1),(5,2),(7,1),(23,1)],69,11733,[]⟩, ⟨[(3,1),(5,2),(7,1),(23,2)],69,270851,[23]⟩, ⟨[(3,1),(5,2),(7,1),(23,3)],69,6230565,[23]⟩, ⟨[(3,1),(5,2),(7,1),(29,1)],75,14535,[]⟩, ⟨[(3,1),(5,2),(7,1),(29,2)],75,422507,[29]⟩, ⟨[(3,1),(5,2),(7,1),(29,3)],75,12253695,[29]⟩]
theorem schOk3 : sch3.all checkSeedFull = true := by decide +kernel
def sch4 : List Seed := [⟨[(3,1),(5,2),(7,1),(31,1)],93,15469,[]⟩, ⟨[(3,1),(5,2),(7,1),(31,2)],93,480531,[31]⟩, ⟨[(3,1),(5,2),(7,1),(31,3)],93,14897453,[31]⟩, ⟨[(3,1),(5,2),(7,2)],75,3393,[]⟩, ⟨[(3,1),(5,2),(7,3)],75,23875,[7]⟩, ⟨[(3,1),(5,2),(7,4)],75,167249,[7]⟩, ⟨[(3,1),(5,2),(11,1),(13,1)],55,10107,[]⟩, ⟨[(3,1),(5,2),(11,1),(17,1)],55,12759,[]⟩, ⟨[(3,1),(5,2),(11,1),(17,2)],55,218391,[17]⟩, ⟨[(3,1),(5,2),(11,1),(17,3)],55,3714135,[17]⟩, ⟨[(3,1),(5,2),(11,2)],121,7417,[11]⟩, ⟨[(3,1),(5,2),(11,3)],121,81711,[11]⟩, ⟨[(3,1),(5,2),(13,2)],169,10017,[13]⟩, ⟨[(3,1),(5,2),(13,3)],169,130345,[13]⟩, ⟨[(3,1),(5,3),(7,1),(23,1)],69,59433,[5]⟩]
theorem schOk4 : sch4.all checkSeedFull = true := by decide +kernel
def sch5 : List Seed := [⟨[(3,1),(5,3),(7,1),(23,2)],69,1371951,[5,23]⟩, ⟨[(3,1),(5,3),(7,1),(23,3)],69,31559865,[5,23]⟩, ⟨[(3,1),(5,3),(7,1),(29,1)],75,73635,[5]⟩, ⟨[(3,1),(5,3),(7,1),(29,2)],75,2140407,[5,29]⟩, ⟨[(3,1),(5,3),(7,1),(29,3)],75,62076795,[5,29]⟩, ⟨[(3,1),(5,3),(7,1),(31,1)],93,78369,[5]⟩, ⟨[(3,1),(5,3),(7,1),(31,2)],93,2434431,[5,31]⟩, ⟨[(3,1),(5,3),(7,1),(31,3)],93,75472353,[5,31]⟩, ⟨[(3,1),(5,3),(7,1),(37,1)],105,92571,[5]⟩, ⟨[(3,1),(5,3),(7,1),(37,2)],105,3430119,[5,37]⟩, ⟨[(3,1),(5,3),(7,1),(37,3)],105,126919395,[5,37]⟩, ⟨[(3,1),(5,3),(7,2)],75,17193,[5]⟩, ⟨[(3,1),(5,3),(7,3)],75,120975,[5,7]⟩, ⟨[(3,1),(5,3),(7,4)],75,847449,[5,7]⟩, ⟨[(3,1),(5,3),(11,1)],125,3363,[5]⟩]
theorem schOk5 : sch5.all checkSeedFull = true := by decide +kernel
def sch6 : List Seed := [⟨[(3,1),(5,3),(11,2)],121,37617,[5,11]⟩, ⟨[(3,1),(5,3),(11,3)],121,414411,[5,11]⟩, ⟨[(3,1),(5,3),(13,1)],125,3861,[5]⟩, ⟨[(3,1),(5,3),(13,2)],125,50817,[5,13]⟩, ⟨[(3,1),(5,3),(13,3)],125,661245,[5,13]⟩, ⟨[(3,1),(5,4),(7,1)],105,11867,[5]⟩, ⟨[(3,1),(5,4),(7,2)],75,86193,[5]⟩, ⟨[(3,1),(5,4),(7,3)],75,606475,[5,7]⟩, ⟨[(3,1),(5,4),(7,4)],75,4248449,[5,7]⟩, ⟨[(3,1),(5,4),(11,1)],125,16863,[5]⟩, ⟨[(3,1),(5,4),(11,2)],121,188617,[5,11]⟩, ⟨[(3,1),(5,4),(11,3)],121,2077911,[5,11]⟩, ⟨[(3,1),(5,4),(13,1)],125,19361,[5]⟩, ⟨[(3,1),(5,4),(13,2)],125,254817,[5,13]⟩, ⟨[(3,1),(5,4),(13,3)],125,3315745,[5,13]⟩]
theorem schOk6 : sch6.all checkSeedFull = true := by decide +kernel
def sch7 : List Seed := [⟨[(3,1),(7,1),(11,1),(19,1)],133,3291,[]⟩, ⟨[(3,1),(7,1),(13,1),(17,1)],119,3423,[]⟩, ⟨[(3,1),(7,1),(13,1),(19,1)],133,3773,[]⟩, ⟨[(3,2),(5,1),(7,1),(107,1)],315,33687,[]⟩, ⟨[(3,2),(5,1),(7,1),(107,2)],315,3605133,[107]⟩, ⟨[(3,2),(5,1),(7,1),(107,3)],315,385749855,[107]⟩, ⟨[(3,2),(5,1),(7,1),(109,1)],315,34305,[]⟩, ⟨[(3,2),(5,1),(7,1),(109,2)],315,3739869,[109]⟩, ⟨[(3,2),(5,1),(7,1),(109,3)],315,407646345,[109]⟩, ⟨[(3,2),(5,1),(7,1),(113,1)],315,35541,[]⟩, ⟨[(3,2),(5,1),(7,1),(113,2)],315,4016757,[113]⟩, ⟨[(3,2),(5,1),(7,1),(113,3)],315,453894165,[113]⟩, ⟨[(3,2),(5,1),(7,1),(127,1)],315,39867,[]⟩, ⟨[(3,2),(5,1),(7,1),(127,2)],315,5063733,[127]⟩, ⟨[(3,2),(5,1),(7,1),(127,3)],315,643094715,[127]⟩]
theorem schOk7 : sch7.all checkSeedFull = true := by decide +kernel
def sch8 : List Seed := [⟨[(3,2),(5,1),(7,1),(131,1)],315,41103,[]⟩, ⟨[(3,2),(5,1),(7,1),(131,2)],315,5385117,[131]⟩, ⟨[(3,2),(5,1),(7,1),(131,3)],315,705450951,[131]⟩, ⟨[(3,2),(5,1),(7,1),(137,1)],105,42957,[]⟩, ⟨[(3,2),(5,1),(7,1),(137,2)],105,5885733,[137]⟩, ⟨[(3,2),(5,1),(7,1),(137,3)],105,806346045,[137]⟩, ⟨[(3,2),(5,1),(7,1),(139,1)],105,43575,[]⟩, ⟨[(3,2),(5,1),(7,1),(139,2)],105,6057549,[139]⟩, ⟨[(3,2),(5,1),(7,1),(139,3)],105,841999935,[139]⟩, ⟨[(3,2),(5,1),(7,1),(149,1)],105,46665,[]⟩, ⟨[(3,2),(5,1),(7,1),(149,2)],105,6953709,[149]⟩, ⟨[(3,2),(5,1),(7,1),(149,3)],105,1036103265,[149]⟩, ⟨[(3,2),(5,1),(7,1),(151,1)],105,47283,[]⟩, ⟨[(3,2),(5,1),(7,1),(151,2)],105,7140357,[151]⟩, ⟨[(3,2),(5,1),(7,1),(151,3)],105,1078194531,[151]⟩]
theorem schOk8 : sch8.all checkSeedFull = true := by decide +kernel
def sch9 : List Seed := [⟨[(3,2),(5,1),(7,1),(157,1)],105,49137,[]⟩, ⟨[(3,2),(5,1),(7,1),(157,2)],105,7715133,[157]⟩, ⟨[(3,2),(5,1),(7,1),(157,3)],105,1211276505,[157]⟩, ⟨[(3,2),(5,1),(7,1),(163,1)],105,50991,[]⟩, ⟨[(3,2),(5,1),(7,1),(163,2)],105,8312157,[163]⟩, ⟨[(3,2),(5,1),(7,1),(163,3)],105,1354882215,[163]⟩, ⟨[(3,2),(5,1),(7,1),(167,1)],105,52227,[]⟩, ⟨[(3,2),(5,1),(7,1),(167,2)],105,8722533,[167]⟩, ⟨[(3,2),(5,1),(7,1),(167,3)],105,1456663635,[167]⟩, ⟨[(3,2),(5,1),(7,1),(173,1)],105,54081,[]⟩, ⟨[(3,2),(5,1),(7,1),(173,2)],105,9356637,[173]⟩, ⟨[(3,2),(5,1),(7,1),(173,3)],105,1618698825,[173]⟩, ⟨[(3,2),(5,1),(7,1),(179,1)],105,55935,[]⟩, ⟨[(3,2),(5,1),(7,1),(179,2)],105,10012989,[179]⟩, ⟨[(3,2),(5,1),(7,1),(179,3)],105,1792325655,[179]⟩]
theorem schOk9 : sch9.all checkSeedFull = true := by decide +kernel
def sch10 : List Seed := [⟨[(3,2),(5,1),(7,1),(181,1)],105,56553,[]⟩, ⟨[(3,2),(5,1),(7,1),(181,2)],105,10236717,[181]⟩, ⟨[(3,2),(5,1),(7,1),(181,3)],105,1852846401,[181]⟩, ⟨[(3,2),(5,1),(7,1),(191,1)],191,59643,[]⟩, ⟨[(3,2),(5,1),(7,1),(191,2)],191,11392437,[191]⟩, ⟨[(3,2),(5,1),(7,1),(191,3)],191,2175956091,[191]⟩, ⟨[(3,2),(5,1),(7,1),(193,1)],193,60261,[]⟩, ⟨[(3,2),(5,1),(7,1),(193,2)],193,11630997,[193]⟩, ⟨[(3,2),(5,1),(7,1),(193,3)],193,2244783045,[193]⟩, ⟨[(3,2),(5,1),(7,1),(197,1)],197,61497,[]⟩, ⟨[(3,2),(5,1),(7,1),(197,2)],197,12115533,[197]⟩, ⟨[(3,2),(5,1),(7,1),(197,3)],197,2386760625,[197]⟩, ⟨[(3,2),(5,1),(7,1),(199,1)],199,62115,[]⟩, ⟨[(3,2),(5,1),(7,1),(199,2)],199,12361509,[199]⟩, ⟨[(3,2),(5,1),(7,1),(199,3)],199,2459940915,[199]⟩]
theorem schOk10 : sch10.all checkSeedFull = true := by decide +kernel
def sch11 : List Seed := [⟨[(3,2),(5,1),(11,1),(19,1)],55,9315,[]⟩, ⟨[(3,2),(5,1),(11,1),(23,1)],55,11079,[]⟩, ⟨[(3,2),(5,1),(11,1),(23,2)],55,255753,[23]⟩, ⟨[(3,2),(5,1),(11,1),(23,3)],55,5883255,[23]⟩, ⟨[(3,2),(5,1),(11,1),(29,1)],87,13725,[]⟩, ⟨[(3,2),(5,1),(11,1),(29,2)],87,398961,[29]⟩, ⟨[(3,2),(5,1),(11,1),(29,3)],87,11570805,[29]⟩, ⟨[(3,2),(5,1),(11,1),(31,1)],93,14607,[]⟩, ⟨[(3,2),(5,1),(11,1),(31,2)],93,453753,[31]⟩, ⟨[(3,2),(5,1),(11,1),(31,3)],93,14067279,[31]⟩, ⟨[(3,2),(5,1),(11,2)],99,4929,[11]⟩, ⟨[(3,2),(5,1),(11,3)],99,54297,[11]⟩, ⟨[(3,2),(5,1),(13,1),(17,1)],51,9711,[]⟩, ⟨[(3,2),(5,1),(13,1),(17,2)],51,166179,[17]⟩, ⟨[(3,2),(5,1),(13,1),(17,3)],51,2826135,[17]⟩]
theorem schOk11 : sch11.all checkSeedFull = true := by decide +kernel
def sch12 : List Seed := [⟨[(3,2),(5,1),(13,1),(19,1)],57,10725,[]⟩, ⟨[(3,2),(5,1),(13,1),(23,1)],65,12753,[]⟩, ⟨[(3,2),(5,1),(13,1),(23,2)],65,294411,[23]⟩, ⟨[(3,2),(5,1),(13,1),(23,3)],65,6772545,[23]⟩, ⟨[(3,2),(5,1),(13,2)],117,6669,[13]⟩, ⟨[(3,2),(5,1),(13,3)],117,86775,[13]⟩, ⟨[(3,2),(5,1),(17,1),(19,1)],57,13545,[]⟩, ⟨[(3,2),(5,1),(17,2),(19,1)],57,231825,[17]⟩, ⟨[(3,2),(5,1),(17,3),(19,1)],57,3942585,[17]⟩, ⟨[(3,2),(5,1),(19,2)],171,13473,[19]⟩, ⟨[(3,2),(5,1),(19,3)],171,256065,[19]⟩, ⟨[(3,2),(5,2),(11,1),(53,1)],53,129969,[]⟩, ⟨[(3,2),(5,2),(11,1),(53,2)],53,6893193,[53]⟩, ⟨[(3,2),(5,2),(11,1),(53,3)],53,365344065,[53]⟩, ⟨[(3,2),(5,2),(11,1),(67,1)],55,163023,[]⟩]
theorem schOk12 : sch12.all checkSeedFull = true := by decide +kernel
def sch13 : List Seed := [⟨[(3,2),(5,2),(11,1),(67,2)],55,10927377,[67]⟩, ⟨[(3,2),(5,2),(11,1),(67,3)],55,732139095,[67]⟩, ⟨[(3,2),(5,2),(11,1),(71,1)],55,172467,[]⟩, ⟨[(3,2),(5,2),(11,1),(71,2)],55,12249993,[71]⟩, ⟨[(3,2),(5,2),(11,1),(71,3)],55,869754339,[71]⟩, ⟨[(3,2),(5,2),(11,1),(73,1)],55,177189,[]⟩, ⟨[(3,2),(5,2),(11,1),(73,2)],55,12939633,[73]⟩, ⟨[(3,2),(5,2),(11,1),(73,3)],55,944598045,[73]⟩, ⟨[(3,2),(5,2),(11,1),(79,1)],55,191355,[]⟩, ⟨[(3,2),(5,2),(11,1),(79,2)],55,15121881,[79]⟩, ⟨[(3,2),(5,2),(11,1),(79,3)],55,1194633435,[79]⟩, ⟨[(3,2),(5,2),(11,1),(83,2)],55,16671153,[83]⟩, ⟨[(3,2),(5,2),(11,1),(83,3)],55,1383710535,[83]⟩, ⟨[(3,2),(5,2),(11,2)],55,26374,[11]⟩, ⟨[(3,2),(5,2),(11,3)],55,290517,[11]⟩]
theorem schOk13 : sch13.all checkSeedFull = true := by decide +kernel
def sch14 : List Seed := [⟨[(3,2),(5,2),(11,4)],55,3196090,[]⟩, ⟨[(3,2),(5,2),(13,1)],65,2717,[]⟩, ⟨[(3,2),(5,2),(13,2)],65,35724,[13]⟩, ⟨[(3,2),(5,2),(13,3)],65,464815,[13]⟩, ⟨[(3,2),(5,2),(17,1)],75,3429,[]⟩, ⟨[(3,2),(5,2),(17,2)],75,58696,[17]⟩, ⟨[(3,2),(5,2),(17,3)],75,998235,[17]⟩, ⟨[(3,2),(5,2),(19,1)],75,3785,[]⟩, ⟨[(3,2),(5,2),(19,2)],75,72318,[19]⟩, ⟨[(3,2),(5,2),(19,3)],75,1374445,[19]⟩, ⟨[(3,2),(5,2),(23,1)],75,4497,[]⟩, ⟨[(3,2),(5,2),(23,2)],75,103834,[23]⟩, ⟨[(3,2),(5,2),(23,3)],75,2388585,[23]⟩, ⟨[(3,2),(5,2),(29,1)],87,5565,[]⟩, ⟨[(3,2),(5,2),(29,2)],87,161788,[29]⟩]
theorem schOk14 : sch14.all checkSeedFull = true := by decide +kernel
def sch15 : List Seed := [⟨[(3,2),(5,2),(37,1)],111,6989,[]⟩, ⟨[(3,2),(5,2),(37,2)],111,258996,[37]⟩, ⟨[(3,2),(5,2),(41,1)],123,7701,[]⟩, ⟨[(3,2),(5,2),(43,1)],129,8057,[]⟩, ⟨[(3,2),(5,2),(43,2)],129,346854,[]⟩, ⟨[(3,2),(5,2),(47,1)],141,8769,[]⟩, ⟨[(3,2),(5,2),(47,2)],141,412546,[47]⟩, ⟨[(3,2),(5,2),(47,3)],141,19390065,[47]⟩, ⟨[(3,2),(5,2),(59,1)],177,10905,[]⟩, ⟨[(3,2),(5,2),(59,2)],177,643798,[59]⟩, ⟨[(3,2),(5,2),(59,3)],177,37984485,[59]⟩, ⟨[(3,2),(5,2),(61,1)],183,11261,[]⟩, ⟨[(3,2),(5,2),(61,2)],183,687324,[61]⟩, ⟨[(3,2),(5,2),(61,3)],183,41927167,[61]⟩, ⟨[(3,2),(5,3),(11,1)],55,11961,[5]⟩]
theorem schOk15 : sch15.all checkSeedFull = true := by decide +kernel
def sch16 : List Seed := [⟨[(3,2),(5,3),(11,2)],55,133599,[5,11]⟩, ⟨[(3,2),(5,3),(11,3)],55,1471617,[5,11]⟩, ⟨[(3,2),(5,3),(13,1)],65,13767,[5]⟩, ⟨[(3,2),(5,3),(13,2)],65,180999,[5,13]⟩, ⟨[(3,2),(5,3),(13,3)],65,2355015,[5,13]⟩, ⟨[(3,2),(5,3),(17,1)],75,17379,[5]⟩, ⟨[(3,2),(5,3),(17,2)],75,297471,[5,17]⟩, ⟨[(3,2),(5,3),(17,3)],75,5059035,[5,17]⟩, ⟨[(3,2),(5,3),(19,1)],75,19185,[5]⟩, ⟨[(3,2),(5,3),(19,2)],75,366543,[5,19]⟩, ⟨[(3,2),(5,3),(19,3)],75,6966345,[5,19]⟩, ⟨[(3,2),(5,3),(23,1)],75,22797,[5]⟩, ⟨[(3,2),(5,3),(23,2)],75,526359,[5,23]⟩, ⟨[(3,2),(5,3),(23,3)],75,12108285,[5,23]⟩, ⟨[(3,2),(5,4),(11,1)],55,59961,[5]⟩]
theorem schOk16 : sch16.all checkSeedFull = true := by decide +kernel
def sch17 : List Seed := [⟨[(3,2),(5,4),(11,2)],55,669724,[5,11]⟩, ⟨[(3,2),(5,4),(11,3)],55,7377117,[5,11]⟩, ⟨[(3,2),(5,4),(11,4)],55,81158440,[11]⟩, ⟨[(3,2),(5,4),(13,1)],65,69017,[5]⟩, ⟨[(3,2),(5,4),(13,2)],65,907374,[5,13]⟩, ⟨[(3,2),(5,4),(13,3)],65,11806015,[5,13]⟩, ⟨[(3,2),(5,4),(17,1)],75,87129,[5]⟩, ⟨[(3,2),(5,4),(17,2)],75,1491346,[5,17]⟩, ⟨[(3,2),(5,4),(17,3)],75,25363035,[5,17]⟩, ⟨[(3,2),(5,4),(19,1)],75,96185,[5]⟩, ⟨[(3,2),(5,4),(19,2)],75,1837668,[5,19]⟩, ⟨[(3,2),(5,4),(19,3)],75,34925845,[5,19]⟩, ⟨[(3,2),(5,4),(23,1)],75,114297,[5]⟩, ⟨[(3,2),(5,4),(23,2)],75,2638984,[5,23]⟩, ⟨[(3,2),(5,4),(23,3)],75,60706785,[5,23]⟩]
theorem schOk17 : sch17.all checkSeedFull = true := by decide +kernel
def sch18 : List Seed := [⟨[(3,2),(5,4),(29,2)],87,4112638,[5,29]⟩, ⟨[(3,2),(5,4),(37,2)],111,6584646,[5,37]⟩, ⟨[(3,2),(5,4),(41,2)],123,8037994,[5,41]⟩, ⟨[(3,2),(5,4),(43,2)],125,8819004,[5,43]⟩, ⟨[(3,2),(7,1),(11,1),(13,1)],77,8463,[]⟩, ⟨[(3,2),(7,1),(11,1),(13,2)],77,111267,[13]⟩, ⟨[(3,2),(7,1),(11,1),(13,3)],77,1447719,[13]⟩, ⟨[(3,2),(7,1),(11,1),(17,1)],63,10683,[]⟩, ⟨[(3,2),(7,1),(11,1),(17,2)],63,182859,[17]⟩, ⟨[(3,2),(7,1),(11,1),(17,3)],63,3109851,[17]⟩, ⟨[(3,2),(7,1),(11,2)],99,6209,[11]⟩, ⟨[(3,2),(7,1),(11,3)],99,68403,[11]⟩, ⟨[(3,2),(7,1),(13,2),(17,2)],63,2765841,[13,17]⟩, ⟨[(3,2),(7,1),(13,2),(17,3)],63,47038329,[13,17]⟩, ⟨[(3,2),(7,1),(13,3),(17,2)],63,35987861,[13,17]⟩]
theorem schOk18 : sch18.all checkSeedFull = true := by decide +kernel
def sch19 : List Seed := [⟨[(3,2),(7,1),(13,3),(17,3)],63,612041157,[13,17]⟩, ⟨[(3,2),(7,2),(11,1)],77,4041,[]⟩, ⟨[(3,2),(7,2),(11,2)],77,45192,[11]⟩, ⟨[(3,2),(7,2),(11,3)],77,497853,[11]⟩, ⟨[(3,2),(7,2),(13,1)],91,4641,[]⟩, ⟨[(3,2),(7,2),(13,2)],91,61074,[13]⟩, ⟨[(3,2),(7,2),(13,3)],91,794703,[13]⟩, ⟨[(3,2),(7,3),(11,1)],77,28443,[7]⟩, ⟨[(3,2),(7,3),(11,2)],77,318073,[7,11]⟩, ⟨[(3,2),(7,3),(11,3)],77,3504003,[7,11]⟩, ⟨[(3,2),(7,3),(13,1)],91,32669,[7]⟩, ⟨[(3,2),(7,3),(13,2)],91,429897,[7,13]⟩, ⟨[(3,2),(7,3),(13,3)],91,5593861,[7,13]⟩, ⟨[(3,2),(7,4),(11,1)],77,199257,[7]⟩, ⟨[(3,2),(7,4),(11,2)],77,2228240,[7,11]⟩]
theorem schOk19 : sch19.all checkSeedFull = true := by decide +kernel
def sch20 : List Seed := [⟨[(3,2),(7,4),(11,3)],77,24547053,[7,11]⟩, ⟨[(3,2),(7,4),(13,1)],91,228865,[7]⟩, ⟨[(3,2),(7,4),(13,2)],91,3011658,[7,13]⟩, ⟨[(3,2),(7,4),(13,3)],91,39187967,[7,13]⟩, ⟨[(3,2),(7,4),(17,2)],119,4933790,[7,17]⟩, ⟨[(3,2),(7,4),(19,2)],147,6072504,[7,19]⟩, ⟨[(3,2),(7,4),(23,2)],147,8705228,[7,23]⟩, ⟨[(3,3),(5,1),(11,1),(37,1)],45,54495,[3]⟩, ⟨[(3,3),(5,1),(11,1),(37,2)],45,2019195,[3,37]⟩, ⟨[(3,3),(5,1),(11,1),(37,3)],45,74713095,[3,37]⟩, ⟨[(3,3),(5,1),(11,1),(41,1)],45,60075,[3]⟩, ⟨[(3,3),(5,1),(11,1),(41,2)],45,2465955,[3,41]⟩, ⟨[(3,3),(5,1),(11,1),(41,3)],45,101107035,[3,41]⟩, ⟨[(3,3),(5,1),(11,1),(43,1)],45,62865,[3]⟩, ⟨[(3,3),(5,1),(11,1),(43,2)],45,2706075,[3,43]⟩]
theorem schOk20 : sch20.all checkSeedFull = true := by decide +kernel
def sch21 : List Seed := [⟨[(3,3),(5,1),(11,1),(43,3)],45,116364105,[3,43]⟩, ⟨[(3,3),(5,1),(11,1),(47,1)],47,68445,[3]⟩, ⟨[(3,3),(5,1),(11,1),(47,2)],47,3219795,[3,47]⟩, ⟨[(3,3),(5,1),(11,1),(47,3)],47,151333245,[3,47]⟩, ⟨[(3,3),(5,1),(11,1),(53,1)],53,76815,[3]⟩, ⟨[(3,3),(5,1),(11,1),(53,2)],53,4074075,[3,53]⟩, ⟨[(3,3),(5,1),(11,1),(53,3)],53,215928855,[3,53]⟩, ⟨[(3,3),(5,1),(11,1),(59,1)],55,85185,[3]⟩, ⟨[(3,3),(5,1),(11,1),(59,2)],55,5028795,[3,59]⟩, ⟨[(3,3),(5,1),(11,1),(59,3)],55,296701785,[3,59]⟩, ⟨[(3,3),(5,1),(11,1),(61,1)],55,87975,[3]⟩, ⟨[(3,3),(5,1),(11,1),(61,2)],55,5369355,[3,61]⟩, ⟨[(3,3),(5,1),(11,1),(61,3)],55,327533535,[3,61]⟩, ⟨[(3,3),(5,1),(11,1),(67,1)],55,96345,[3]⟩, ⟨[(3,3),(5,1),(11,1),(67,2)],55,6457995,[3,67]⟩]
theorem schOk21 : sch21.all checkSeedFull = true := by decide +kernel
def sch22 : List Seed := [⟨[(3,3),(5,1),(11,1),(67,3)],55,432688545,[3,67]⟩, ⟨[(3,3),(5,1),(11,1),(71,1)],55,101925,[3]⟩, ⟨[(3,3),(5,1),(11,1),(71,2)],55,7239555,[3,71]⟩, ⟨[(3,3),(5,1),(11,1),(71,3)],55,514011285,[3,71]⟩, ⟨[(3,3),(5,1),(11,1),(73,1)],55,104715,[3]⟩, ⟨[(3,3),(5,1),(11,1),(73,2)],55,7647075,[3,73]⟩, ⟨[(3,3),(5,1),(11,1),(73,3)],55,558239355,[3,73]⟩, ⟨[(3,3),(5,1),(11,1),(79,1)],79,113085,[3]⟩, ⟨[(3,3),(5,1),(11,1),(79,2)],79,8936595,[3,79]⟩, ⟨[(3,3),(5,1),(11,1),(79,3)],79,705993885,[3,79]⟩, ⟨[(3,3),(5,1),(11,1),(83,1)],83,118665,[3]⟩, ⟨[(3,3),(5,1),(11,1),(83,2)],83,9852075,[3,83]⟩, ⟨[(3,3),(5,1),(11,1),(83,3)],83,817725105,[3,83]⟩, ⟨[(3,3),(5,1),(11,1),(89,1)],89,127035,[3]⟩, ⟨[(3,3),(5,1),(11,1),(89,2)],89,11308995,[3,89]⟩]
theorem schOk22 : sch22.all checkSeedFull = true := by decide +kernel
def sch23 : List Seed := [⟨[(3,3),(5,1),(11,1),(89,3)],89,1006503435,[3,89]⟩, ⟨[(3,3),(5,1),(11,1),(97,1)],97,138195,[3]⟩, ⟨[(3,3),(5,1),(11,1),(97,2)],97,13407795,[3,97]⟩, ⟨[(3,3),(5,1),(11,1),(97,3)],97,1300558995,[3,97]⟩, ⟨[(3,3),(5,1),(11,1),(101,1)],99,143775,[3]⟩, ⟨[(3,3),(5,1),(11,1),(101,2)],99,14524155,[3,101]⟩, ⟨[(3,3),(5,1),(11,1),(101,3)],99,1466942535,[3,101]⟩, ⟨[(3,3),(5,1),(11,1),(103,1)],99,146565,[3]⟩, ⟨[(3,3),(5,1),(11,1),(103,2)],99,15099075,[3,103]⟩, ⟨[(3,3),(5,1),(11,1),(103,3)],99,1555207605,[3,103]⟩, ⟨[(3,3),(5,1),(11,1),(107,1)],99,152145,[3]⟩, ⟨[(3,3),(5,1),(11,1),(107,2)],99,16282395,[3,107]⟩, ⟨[(3,3),(5,1),(11,1),(107,3)],99,1742219145,[3,107]⟩, ⟨[(3,3),(5,1),(11,2)],99,15585,[3,11]⟩, ⟨[(3,3),(5,1),(11,3)],99,171675,[3,11]⟩]
theorem schOk23 : sch23.all checkSeedFull = true := by decide +kernel
def sch24 : List Seed := [⟨[(3,3),(5,1),(13,1),(29,1)],65,49905,[3]⟩, ⟨[(3,3),(5,1),(13,1),(29,2)],65,1450605,[3,29]⟩, ⟨[(3,3),(5,1),(13,1),(29,3)],65,42070905,[3,29]⟩, ⟨[(3,3),(5,1),(13,1),(37,1)],45,62745,[3]⟩, ⟨[(3,3),(5,1),(13,1),(37,2)],45,2324925,[3,37]⟩, ⟨[(3,3),(5,1),(13,1),(37,3)],45,86025585,[3,37]⟩, ⟨[(3,3),(5,1),(13,1),(41,1)],45,69165,[3]⟩, ⟨[(3,3),(5,1),(13,1),(41,2)],45,2839125,[3,41]⟩, ⟨[(3,3),(5,1),(13,1),(41,3)],45,116407485,[3,41]⟩, ⟨[(3,3),(5,1),(13,1),(43,1)],45,72375,[3]⟩, ⟨[(3,3),(5,1),(13,1),(43,2)],45,3115485,[3,43]⟩, ⟨[(3,3),(5,1),(13,1),(43,3)],45,133969215,[3,43]⟩, ⟨[(3,3),(5,1),(13,1),(47,1)],47,78795,[3]⟩, ⟨[(3,3),(5,1),(13,1),(47,2)],47,3706725,[3,47]⟩, ⟨[(3,3),(5,1),(13,1),(47,3)],47,174219435,[3,47]⟩]
theorem schOk24 : sch24.all checkSeedFull = true := by decide +kernel
def sch25 : List Seed := [⟨[(3,3),(5,1),(13,1),(53,1)],53,88425,[3]⟩, ⟨[(3,3),(5,1),(13,1),(53,2)],53,4689885,[3,53]⟩, ⟨[(3,3),(5,1),(13,1),(53,3)],53,248567265,[3,53]⟩, ⟨[(3,3),(5,1),(13,1),(59,1)],59,98055,[3]⟩, ⟨[(3,3),(5,1),(13,1),(59,2)],59,5788605,[3,59]⟩, ⟨[(3,3),(5,1),(13,1),(59,3)],59,341531055,[3,59]⟩, ⟨[(3,3),(5,1),(13,1),(61,1)],61,101265,[3]⟩, ⟨[(3,3),(5,1),(13,1),(61,2)],61,6180525,[3,61]⟩, ⟨[(3,3),(5,1),(13,1),(61,3)],61,377015385,[3,61]⟩, ⟨[(3,3),(5,1),(13,2)],117,21105,[3,13]⟩, ⟨[(3,3),(5,1),(13,3)],117,274605,[3,13]⟩, ⟨[(3,3),(5,1),(17,1),(19,1)],51,42795,[3]⟩, ⟨[(3,3),(5,1),(17,1),(29,1)],85,63045,[3]⟩, ⟨[(3,3),(5,1),(17,1),(29,2)],85,1832625,[3,29]⟩, ⟨[(3,3),(5,1),(17,1),(29,3)],85,53150445,[3,29]⟩]
theorem schOk25 : sch25.all checkSeedFull = true := by decide +kernel
def sch26 : List Seed := [⟨[(3,3),(5,1),(17,1),(37,1)],85,79245,[3]⟩, ⟨[(3,3),(5,1),(17,1),(37,2)],85,2936385,[3,37]⟩, ⟨[(3,3),(5,1),(17,1),(37,3)],85,108650565,[3,37]⟩, ⟨[(3,3),(5,1),(17,1),(41,2)],51,3585465,[3,41]⟩, ⟨[(3,3),(5,1),(17,1),(41,3)],51,147008385,[3,41]⟩, ⟨[(3,3),(5,1),(17,2)],135,34665,[3,17]⟩, ⟨[(3,3),(5,1),(17,3)],135,589545,[3,17]⟩, ⟨[(3,3),(5,1),(19,1),(29,1)],87,69615,[3]⟩, ⟨[(3,3),(5,1),(19,1),(29,2)],87,2023635,[3,29]⟩, ⟨[(3,3),(5,1),(19,1),(29,3)],87,58690215,[3,29]⟩, ⟨[(3,3),(5,1),(19,2)],95,42705,[3,19]⟩, ⟨[(3,3),(5,1),(19,3)],95,811635,[3,19]⟩, ⟨[(3,3),(5,1),(23,1)],115,2655,[3]⟩, ⟨[(3,3),(5,1),(23,2)],115,61305,[3,23]⟩, ⟨[(3,3),(5,1),(23,3)],115,1410255,[3,23]⟩]
theorem schOk26 : sch26.all checkSeedFull = true := by decide +kernel
def sch27 : List Seed := [⟨[(3,3),(5,1),(31,1)],135,3495,[3]⟩, ⟨[(3,3),(5,1),(31,2)],135,108585,[3,31]⟩, ⟨[(3,3),(5,1),(31,3)],135,3366375,[3,31]⟩, ⟨[(3,3),(5,2),(13,1)],65,8585,[]⟩, ⟨[(3,3),(5,2),(13,2)],65,112845,[13]⟩, ⟨[(3,3),(5,2),(13,3)],65,1468225,[13]⟩, ⟨[(3,3),(5,2),(17,1)],75,10845,[3]⟩, ⟨[(3,3),(5,2),(17,2)],75,185605,[3,17]⟩, ⟨[(3,3),(5,2),(17,3)],75,3156525,[3,17]⟩, ⟨[(3,3),(5,2),(19,1)],57,11975,[3]⟩, ⟨[(3,3),(5,2),(19,2)],57,228765,[3,19]⟩, ⟨[(3,3),(5,2),(19,3)],57,4347775,[3,19]⟩, ⟨[(3,3),(5,2),(23,1)],69,14235,[3]⟩, ⟨[(3,3),(5,2),(23,2)],69,328645,[3,23]⟩, ⟨[(3,3),(5,2),(23,3)],69,7560075,[3,23]⟩]
theorem schOk27 : sch27.all checkSeedFull = true := by decide +kernel
def sch28 : List Seed := [⟨[(3,3),(5,2),(29,1)],75,17625,[3]⟩, ⟨[(3,3),(5,2),(29,2)],75,512365,[3,29]⟩, ⟨[(3,3),(5,2),(29,3)],75,14859825,[3,29]⟩, ⟨[(3,3),(5,2),(31,1)],75,18755,[3]⟩, ⟨[(3,3),(5,2),(31,2)],75,582645,[3,31]⟩, ⟨[(3,3),(5,2),(31,3)],75,18063235,[3,31]⟩, ⟨[(3,3),(5,2),(37,1)],75,22145,[3]⟩, ⟨[(3,3),(5,2),(37,2)],75,820605,[3,37]⟩, ⟨[(3,3),(5,2),(37,3)],75,30363625,[3,37]⟩, ⟨[(3,3),(5,3)],125,2865,[]⟩, ⟨[(3,3),(5,3),(13,1)],65,43485,[5]⟩, ⟨[(3,3),(5,3),(17,1)],75,54945,[3,5]⟩, ⟨[(3,3),(5,3),(17,2)],75,940305,[3,5,17]⟩, ⟨[(3,3),(5,3),(17,3)],75,15991425,[3,5,17]⟩, ⟨[(3,3),(5,3),(19,1)],57,60675,[3,5]⟩]
theorem schOk28 : sch28.all checkSeedFull = true := by decide +kernel
def sch29 : List Seed := [⟨[(3,3),(5,3),(19,2)],57,1159065,[3,5,19]⟩, ⟨[(3,3),(5,3),(19,3)],57,22028475,[3,5,19]⟩, ⟨[(3,3),(5,3),(23,1)],69,72135,[3,5]⟩, ⟨[(3,3),(5,3),(23,2)],69,1665345,[3,5,23]⟩, ⟨[(3,3),(5,3),(23,3)],69,38309175,[3,5,23]⟩, ⟨[(3,3),(5,3),(29,1)],75,89325,[3,5]⟩, ⟨[(3,3),(5,3),(29,2)],75,2596665,[3,5,29]⟩, ⟨[(3,3),(5,3),(29,3)],75,75309525,[3,5,29]⟩, ⟨[(3,3),(5,3),(31,1)],75,95055,[3,5]⟩, ⟨[(3,3),(5,3),(31,2)],75,2952945,[3,5,31]⟩, ⟨[(3,3),(5,3),(31,3)],75,91547535,[3,5,31]⟩, ⟨[(3,3),(5,3),(37,1)],75,112245,[3,5]⟩, ⟨[(3,3),(5,3),(37,2)],75,4159305,[3,5,37]⟩, ⟨[(3,3),(5,3),(37,3)],75,153900525,[3,5,37]⟩, ⟨[(3,3),(5,3),(41,1)],123,123705,[3,5]⟩]
theorem schOk29 : sch29.all checkSeedFull = true := by decide +kernel
def sch30 : List Seed := [⟨[(3,3),(5,3),(41,2)],123,5078145,[3,5,41]⟩, ⟨[(3,3),(5,3),(41,3)],123,208210185,[3,5,41]⟩, ⟨[(3,3),(5,4),(13,1)],65,217985,[5]⟩, ⟨[(3,3),(5,4),(17,1)],75,275445,[3,5]⟩, ⟨[(3,3),(5,4),(17,2)],75,4713805,[3,5,17]⟩, ⟨[(3,3),(5,4),(17,3)],75,80165925,[3,5,17]⟩, ⟨[(3,3),(5,4),(19,1)],57,304175,[3,5]⟩, ⟨[(3,3),(5,4),(19,2)],57,5810565,[3,5,19]⟩, ⟨[(3,3),(5,4),(19,3)],57,110431975,[3,5,19]⟩, ⟨[(3,3),(5,4),(23,1)],69,361635,[3,5]⟩, ⟨[(3,3),(5,4),(23,2)],69,8348845,[3,5,23]⟩, ⟨[(3,3),(5,4),(23,3)],69,192054675,[3,5,23]⟩, ⟨[(3,3),(5,4),(29,1)],75,447825,[3,5]⟩, ⟨[(3,3),(5,4),(29,2)],75,13018165,[3,5,29]⟩, ⟨[(3,3),(5,4),(29,3)],75,377558025,[3,5,29]⟩]
theorem schOk30 : sch30.all checkSeedFull = true := by decide +kernel
def sch31 : List Seed := [⟨[(3,3),(5,4),(31,1)],75,476555,[3,5]⟩, ⟨[(3,3),(5,4),(31,2)],75,14804445,[3,5,31]⟩, ⟨[(3,3),(5,4),(31,3)],75,458969035,[3,5,31]⟩, ⟨[(3,3),(5,4),(37,1)],75,562745,[3,5]⟩, ⟨[(3,3),(5,4),(37,2)],75,20852805,[3,5,37]⟩, ⟨[(3,3),(5,4),(37,3)],75,771585025,[3,5,37]⟩, ⟨[(3,3),(5,4),(41,1)],123,620205,[3,5]⟩, ⟨[(3,3),(5,4),(41,2)],123,25459645,[3,5,41]⟩, ⟨[(3,3),(5,4),(41,3)],123,1043876685,[3,5,41]⟩, ⟨[(3,3),(7,1),(11,1),(13,1)],63,26733,[3]⟩, ⟨[(3,3),(7,1),(11,2)],77,19691,[3,11]⟩, ⟨[(3,3),(7,1),(11,3)],77,216921,[3,11]⟩, ⟨[(3,3),(7,1),(13,2)],91,26619,[3,13]⟩, ⟨[(3,3),(7,1),(13,3)],91,346367,[3,13]⟩, ⟨[(3,3),(7,1),(17,1)],119,2547,[3]⟩]
theorem schOk31 : sch31.all checkSeedFull = true := by decide +kernel
def sch32 : List Seed := [⟨[(3,3),(7,1),(17,2)],119,43619,[3,17]⟩, ⟨[(3,3),(7,1),(17,3)],119,741843,[3,17]⟩, ⟨[(3,3),(7,1),(19,1)],133,2809,[3]⟩, ⟨[(3,3),(7,1),(19,2)],133,53691,[3,19]⟩, ⟨[(3,3),(7,1),(19,3)],133,1020449,[3,19]⟩, ⟨[(3,3),(7,1),(23,1)],161,3333,[3]⟩, ⟨[(3,3),(7,1),(23,2)],161,76979,[3,23]⟩, ⟨[(3,3),(7,1),(23,3)],161,1770837,[3,23]⟩, ⟨[(3,3),(7,1),(29,2)],189,119771,[3,29]⟩, ⟨[(3,3),(7,1),(29,3)],189,3473679,[3,29]⟩, ⟨[(3,3),(7,2),(11,1)],63,12807,[3]⟩, ⟨[(3,3),(7,2),(11,2)],63,143157,[3,11]⟩, ⟨[(3,3),(7,2),(11,3)],63,1577007,[3,11]⟩, ⟨[(3,3),(7,2),(13,1)],63,14721,[3]⟩, ⟨[(3,3),(7,2),(13,2)],63,193653,[3,13]⟩]
theorem schOk32 : sch32.all checkSeedFull = true := by decide +kernel
def sch33 : List Seed := [⟨[(3,3),(7,2),(13,3)],63,2519769,[3,13]⟩, ⟨[(3,3),(7,2),(17,1)],63,18549,[3]⟩, ⟨[(3,3),(7,2),(17,2)],63,317613,[3,17]⟩, ⟨[(3,3),(7,2),(17,3)],63,5401701,[3,17]⟩, ⟨[(3,3),(7,3),(11,1)],63,90129,[3,7]⟩, ⟨[(3,3),(7,3),(11,2)],63,1007419,[3,7,11]⟩, ⟨[(3,3),(7,3),(11,3)],63,11097609,[3,7,11]⟩, ⟨[(3,3),(7,3),(13,1)],63,103607,[3,7]⟩, ⟨[(3,3),(7,3),(13,2)],63,1362891,[3,7,13]⟩, ⟨[(3,3),(7,3),(13,3)],63,17733583,[3,7,13]⟩, ⟨[(3,3),(7,3),(17,1)],63,130563,[3,7]⟩, ⟨[(3,3),(7,3),(17,2)],63,2235571,[3,7,17]⟩, ⟨[(3,3),(7,3),(17,3)],63,38020707,[3,7,17]⟩, ⟨[(3,3),(7,3),(19,2)],133,2752779,[3,7,19]⟩, ⟨[(3,3),(7,3),(19,3)],133,52318801,[3,7,19]⟩]
theorem schOk33 : sch33.all checkSeedFull = true := by decide +kernel
def sch34 : List Seed := [⟨[(3,3),(7,4),(11,1)],63,631383,[3,7]⟩, ⟨[(3,3),(7,4),(11,2)],63,7057253,[3,7,11]⟩, ⟨[(3,3),(7,4),(11,3)],63,77741823,[3,7,11]⟩, ⟨[(3,3),(7,4),(13,1)],63,725809,[3,7]⟩, ⟨[(3,3),(7,4),(13,2)],63,9547557,[3,7,13]⟩, ⟨[(3,3),(7,4),(13,3)],63,124230281,[3,7,13]⟩, ⟨[(3,3),(7,4),(17,1)],63,914661,[3,7]⟩, ⟨[(3,3),(7,4),(17,2)],63,15661277,[3,7,17]⟩, ⟨[(3,3),(7,4),(17,3)],63,266353749,[3,7,17]⟩, ⟨[(3,3),(7,4),(19,2)],133,19284693,[3,7,19]⟩, ⟨[(3,3),(7,4),(19,3)],133,366521207,[3,7,19]⟩, ⟨[(3,3),(11,2),(13,2),(17,2)],99,139319373,[3,11,13,17]⟩, ⟨[(3,3),(11,2),(13,2),(17,3)],99,2369402901,[3,11,13,17]⟩, ⟨[(3,3),(11,2),(13,3),(17,2)],99,1812785089,[3,11,13,17]⟩, ⟨[(3,3),(11,2),(13,3),(17,3)],99,30830008113,[3,11,13,17]⟩]
theorem schOk34 : sch34.all checkSeedFull = true := by decide +kernel
def sch35 : List Seed := [⟨[(3,3),(11,3),(13,2),(17,2)],99,1534760343,[3,11,13,17]⟩, ⟨[(3,3),(11,3),(13,2),(17,3)],99,26101642311,[3,11,13,17]⟩, ⟨[(3,3),(11,3),(13,3),(17,2)],99,19969862379,[3,11,13,17]⟩, ⟨[(3,3),(11,3),(13,3),(17,3)],99,339627033243,[3,11,13,17]⟩, ⟨[(3,4),(5,1),(11,1)],81,4257,[3]⟩, ⟨[(3,4),(5,1),(11,2)],81,47553,[3,11]⟩, ⟨[(3,4),(5,1),(11,3)],81,523809,[3,11]⟩, ⟨[(3,4),(5,1),(13,1)],65,4899,[3]⟩, ⟨[(3,4),(5,1),(13,2)],65,64413,[3,13]⟩, ⟨[(3,4),(5,1),(13,3)],65,838095,[3,13]⟩, ⟨[(3,4),(5,1),(17,1)],81,6183,[3]⟩, ⟨[(3,4),(5,1),(17,2)],81,105837,[3,17]⟩, ⟨[(3,4),(5,1),(17,3)],81,1799955,[3,17]⟩, ⟨[(3,4),(5,1),(19,1)],81,6825,[3]⟩, ⟨[(3,4),(5,1),(19,2)],81,130401,[3,19]⟩]
theorem schOk35 : sch35.all checkSeedFull = true := by decide +kernel
def sch36 : List Seed := [⟨[(3,4),(5,1),(19,3)],81,2478345,[3,19]⟩, ⟨[(3,4),(5,1),(23,1)],81,8109,[3]⟩, ⟨[(3,4),(5,1),(23,2)],81,187233,[3,23]⟩, ⟨[(3,4),(5,1),(23,3)],81,4307085,[3,23]⟩, ⟨[(3,4),(5,2),(13,1)],65,26189,[]⟩, ⟨[(3,4),(5,2),(17,1)],75,33093,[3]⟩, ⟨[(3,4),(5,2),(17,2)],75,566332,[3,17]⟩, ⟨[(3,4),(5,2),(17,3)],75,9631395,[3,17]⟩, ⟨[(3,4),(5,2),(19,1)],57,36545,[3]⟩, ⟨[(3,4),(5,2),(19,2)],57,698106,[3,19]⟩, ⟨[(3,4),(5,2),(19,3)],57,13267765,[3,19]⟩, ⟨[(3,4),(5,2),(23,1)],69,43449,[3]⟩, ⟨[(3,4),(5,2),(23,2)],69,1003078,[3,23]⟩, ⟨[(3,4),(5,2),(23,3)],69,23074545,[3,23]⟩, ⟨[(3,4),(5,2),(29,1)],75,53805,[3]⟩]
theorem schOk36 : sch36.all checkSeedFull = true := by decide +kernel
def sch37 : List Seed := [⟨[(3,4),(5,2),(29,2)],75,1564096,[3,29]⟩, ⟨[(3,4),(5,2),(29,3)],75,45362535,[3,29]⟩, ⟨[(3,4),(5,2),(31,1)],75,57257,[3]⟩, ⟨[(3,4),(5,2),(31,2)],75,1778718,[3,31]⟩, ⟨[(3,4),(5,2),(31,3)],75,55144009,[3,31]⟩, ⟨[(3,4),(5,2),(37,1)],75,67613,[3]⟩, ⟨[(3,4),(5,2),(37,2)],75,2505432,[3,37]⟩, ⟨[(3,4),(5,2),(37,3)],75,92704735,[3,37]⟩, ⟨[(3,4),(5,2),(41,1)],75,74517,[]⟩, ⟨[(3,4),(5,2),(41,2)],75,3058948,[3,41]⟩, ⟨[(3,4),(5,2),(43,1)],75,77969,[]⟩, ⟨[(3,4),(5,2),(43,2)],75,3356418,[3,43]⟩, ⟨[(3,4),(5,2),(47,1)],75,84873,[3]⟩, ⟨[(3,4),(5,2),(47,2)],75,3992782,[3,47]⟩, ⟨[(3,4),(5,2),(47,3)],75,187664505,[3,47]⟩]
theorem schOk37 : sch37.all checkSeedFull = true := by decide +kernel
def sch38 : List Seed := [⟨[(3,4),(5,2),(53,1)],75,95229,[3]⟩, ⟨[(3,4),(5,2),(53,2)],75,5050888,[3,53]⟩, ⟨[(3,4),(5,2),(53,3)],75,267700815,[3,53]⟩, ⟨[(3,4),(5,2),(59,1)],75,105585,[]⟩, ⟨[(3,4),(5,2),(59,2)],75,6233266,[3,59]⟩, ⟨[(3,4),(5,2),(61,1)],75,109037,[3]⟩, ⟨[(3,4),(5,2),(61,2)],75,6655008,[3,61]⟩, ⟨[(3,4),(5,2),(67,1)],75,119393,[3]⟩, ⟨[(3,4),(5,2),(67,2)],75,8003082,[3,67]⟩, ⟨[(3,4),(5,2),(67,3)],75,536210245,[3,67]⟩, ⟨[(3,4),(5,2),(71,1)],75,126297,[3]⟩, ⟨[(3,4),(5,2),(71,2)],75,8970838,[3,71]⟩, ⟨[(3,4),(5,2),(71,3)],75,636933249,[3,71]⟩, ⟨[(3,4),(5,2),(73,1)],73,129749,[3]⟩, ⟨[(3,4),(5,2),(73,2)],73,9475428,[3,73]⟩]
theorem schOk38 : sch38.all checkSeedFull = true := by decide +kernel
def sch39 : List Seed := [⟨[(3,4),(5,2),(73,3)],73,691709995,[3,73]⟩, ⟨[(3,4),(5,2),(79,1)],79,140105,[3]⟩, ⟨[(3,4),(5,2),(79,2)],79,11072046,[3,79]⟩, ⟨[(3,4),(5,2),(79,3)],79,874695385,[3,79]⟩, ⟨[(3,4),(5,2),(83,1)],81,147009,[3]⟩, ⟨[(3,4),(5,2),(83,2)],81,12205498,[3,83]⟩, ⟨[(3,4),(5,2),(83,3)],81,1013060085,[3,83]⟩, ⟨[(3,4),(5,2),(89,2)],81,14009236,[3,89]⟩, ⟨[(3,4),(5,2),(97,2)],81,16607532,[3,97]⟩, ⟨[(3,4),(5,2),(101,2)],81,17989528,[3,101]⟩, ⟨[(3,4),(5,2),(103,2)],81,18701238,[3,103]⟩, ⟨[(3,4),(5,2),(107,2)],81,20166082,[3,107]⟩, ⟨[(3,4),(5,2),(109,2)],81,20919216,[3,109]⟩, ⟨[(3,4),(5,2),(113,2)],81,22466908,[3,113]⟩, ⟨[(3,4),(5,2),(127,2)],81,28318782,[3,127]⟩]
theorem schOk39 : sch39.all checkSeedFull = true := by decide +kernel
def sch40 : List Seed := [⟨[(3,4),(5,2),(131,2)],81,30115018,[3,131]⟩, ⟨[(3,4),(5,2),(137,2)],81,32912932,[3,137]⟩, ⟨[(3,4),(5,2),(139,2)],81,33873186,[3,139]⟩, ⟨[(3,4),(5,2),(149,2)],81,38881576,[3,149]⟩, ⟨[(3,4),(5,2),(151,2)],81,39924678,[3,151]⟩, ⟨[(3,4),(5,2),(157,2)],81,43136832,[3,157]⟩, ⟨[(3,4),(5,2),(163,2)],81,46473258,[3,163]⟩, ⟨[(3,4),(5,3)],81,8751,[]⟩, ⟨[(3,4),(5,3),(17,1)],75,167643,[3,5]⟩, ⟨[(3,4),(5,3),(17,2)],75,2868807,[3,5,17]⟩, ⟨[(3,4),(5,3),(17,3)],75,48788595,[3,5,17]⟩, ⟨[(3,4),(5,3),(19,1)],57,185145,[3,5]⟩, ⟨[(3,4),(5,3),(19,2)],57,3536631,[3,5,19]⟩, ⟨[(3,4),(5,3),(19,3)],57,67214865,[3,5,19]⟩, ⟨[(3,4),(5,3),(23,1)],69,220149,[3,5]⟩]
theorem schOk40 : sch40.all checkSeedFull = true := by decide +kernel
def sch41 : List Seed := [⟨[(3,4),(5,3),(23,2)],69,5082303,[3,5,23]⟩, ⟨[(3,4),(5,3),(23,3)],69,116911845,[3,5,23]⟩, ⟨[(3,4),(5,3),(29,1)],75,272655,[3,5]⟩, ⟨[(3,4),(5,3),(29,2)],75,7925871,[3,5,29]⟩, ⟨[(3,4),(5,3),(29,3)],75,229869135,[3,5,29]⟩, ⟨[(3,4),(5,3),(31,1)],75,290157,[3,5]⟩, ⟨[(3,4),(5,3),(31,2)],75,9013743,[3,5,31]⟩, ⟨[(3,4),(5,3),(31,3)],75,279444909,[3,5,31]⟩, ⟨[(3,4),(5,3),(37,1)],75,342663,[3,5]⟩, ⟨[(3,4),(5,3),(37,2)],75,12697407,[3,5,37]⟩, ⟨[(3,4),(5,3),(37,3)],75,469822935,[3,5,37]⟩, ⟨[(3,4),(5,3),(41,1)],75,377667,[3,5]⟩, ⟨[(3,4),(5,3),(41,2)],75,15503223,[3,5,41]⟩, ⟨[(3,4),(5,3),(41,3)],75,635651019,[3,5,41]⟩, ⟨[(3,4),(5,4)],81,43876,[3,5]⟩]
theorem schOk41 : sch41.all checkSeedFull = true := by decide +kernel
def sch42 : List Seed := [⟨[(3,4),(5,4),(17,1)],75,840393,[3,5]⟩, ⟨[(3,4),(5,4),(17,3)],75,244574595,[3,5,17]⟩, ⟨[(3,4),(5,4),(19,1)],57,928145,[3,5]⟩, ⟨[(3,4),(5,4),(19,3)],57,336950365,[3,5,19]⟩, ⟨[(3,4),(5,4),(23,1)],69,1103649,[3,5]⟩, ⟨[(3,4),(5,4),(23,3)],69,586098345,[3,5,23]⟩, ⟨[(3,4),(5,4),(29,1)],75,1366905,[3,5]⟩, ⟨[(3,4),(5,4),(29,3)],75,1152402135,[3,5,29]⟩, ⟨[(3,4),(5,4),(31,1)],75,1454657,[3,5]⟩, ⟨[(3,4),(5,4),(31,3)],75,1400949409,[3,5,31]⟩, ⟨[(3,4),(5,4),(37,1)],75,1717913,[3,5]⟩, ⟨[(3,4),(5,4),(37,3)],75,2355413935,[3,5,37]⟩, ⟨[(3,4),(5,4),(41,1)],75,1893417,[3,5]⟩, ⟨[(3,4),(5,4),(41,3)],75,3186803019,[3,5,41]⟩, ⟨[(3,4),(5,4),(97,2)],81,422090382,[3,5,97]⟩]
theorem schOk42 : sch42.all checkSeedFull = true := by decide +kernel
def sch43 : List Seed := [⟨[(3,4),(5,4),(127,2)],81,719772132,[5,127]⟩, ⟨[(3,4),(5,4),(257,2)],81,2922347182,[3,5,257]⟩, ⟨[(3,4),(5,4),(263,2)],81,3059807308,[3,5,263]⟩, ⟨[(3,4),(7,1),(11,1)],77,5379,[3]⟩, ⟨[(3,4),(7,1),(11,2)],77,60137,[3,11]⟩, ⟨[(3,4),(7,1),(11,3)],77,662475,[3,11]⟩, ⟨[(3,4),(7,1),(13,1)],81,6181,[3]⟩, ⟨[(3,4),(7,1),(13,2)],81,81321,[3,13]⟩, ⟨[(3,4),(7,1),(13,3)],81,1058141,[3,13]⟩, ⟨[(3,4),(7,1),(17,1)],81,7785,[3]⟩, ⟨[(3,4),(7,1),(17,2)],81,133313,[3,17]⟩, ⟨[(3,4),(7,1),(17,3)],81,2267289,[3,17]⟩, ⟨[(3,4),(7,2),(11,1)],63,39105,[3]⟩, ⟨[(3,4),(7,2),(11,2)],63,437052,[3,11]⟩, ⟨[(3,4),(7,2),(11,3)],63,4814469,[3,11]⟩]
theorem schOk43 : sch43.all checkSeedFull = true := by decide +kernel
def sch44 : List Seed := [⟨[(3,4),(7,2),(13,1)],63,44961,[3]⟩, ⟨[(3,4),(7,2),(13,2)],63,591390,[3,13]⟩, ⟨[(3,4),(7,2),(13,3)],63,7694967,[3,13]⟩, ⟨[(3,4),(7,2),(17,1)],63,56673,[3]⟩, ⟨[(3,4),(7,2),(17,2)],63,970338,[3,17]⟩, ⟨[(3,4),(7,2),(17,3)],63,16502643,[3,17]⟩, ⟨[(3,4),(7,3),(11,1)],63,275187,[3,7]⟩, ⟨[(3,4),(7,3),(11,2)],63,3075457,[3,7,11]⟩, ⟨[(3,4),(7,3),(11,3)],63,33878427,[3,7,11]⟩, ⟨[(3,4),(7,3),(13,1)],63,316421,[3,7]⟩, ⟨[(3,4),(7,3),(13,2)],63,4161873,[3,7,13]⟩, ⟨[(3,4),(7,3),(13,3)],63,54152749,[3,7,13]⟩, ⟨[(3,4),(7,3),(17,1)],63,398889,[3,7]⟩, ⟨[(3,4),(7,3),(17,2)],63,6829513,[3,7,17]⟩, ⟨[(3,4),(7,3),(17,3)],63,116150121,[3,7,17]⟩]
theorem schOk44 : sch44.all checkSeedFull = true := by decide +kernel
def sch45 : List Seed := [⟨[(3,4),(7,3),(19,2)],57,8410737,[3,7,19]⟩, ⟨[(3,4),(7,3),(19,3)],57,159852403,[3,7,19]⟩, ⟨[(3,4),(7,4),(11,1)],63,1927761,[3,7]⟩, ⟨[(3,4),(7,4),(11,2)],63,21544292,[3,7,11]⟩, ⟨[(3,4),(7,4),(11,3)],63,237326133,[3,7,11]⟩, ⟨[(3,4),(7,4),(13,1)],63,2216641,[3,7]⟩, ⟨[(3,4),(7,4),(13,2)],63,29155254,[3,7,13]⟩, ⟨[(3,4),(7,4),(13,3)],63,379357223,[3,7,13]⟩, ⟨[(3,4),(7,4),(17,1)],63,2794401,[3,7]⟩, ⟨[(3,4),(7,4),(17,2)],63,47843738,[3,7,17]⟩, ⟨[(3,4),(7,4),(17,3)],63,813682467,[3,7,17]⟩, ⟨[(3,4),(7,4),(19,2)],57,58921260,[3,7,19]⟩, ⟨[(3,4),(7,4),(19,3)],57,1119842861,[3,7,19]⟩, ⟨[(3,4),(7,4),(23,1)],63,3661041,[3,7]⟩, ⟨[(3,4),(7,4),(23,2)],63,84542864,[3,7,23]⟩]
theorem schOk45 : sch45.all checkSeedFull = true := by decide +kernel
def sch46 : List Seed := [⟨[(3,4),(7,4),(29,2)],63,131641670,[3,7,29]⟩, ⟨[(3,4),(7,4),(31,2)],63,149652312,[3,7,31]⟩, ⟨[(3,4),(7,4),(37,2)],63,210617358,[3,7,37]⟩, ⟨[(3,4),(7,4),(41,2)],63,257038322,[3,7,41]⟩, ⟨[(3,4),(7,4),(43,2)],63,281982084,[3,7,43]⟩, ⟨[(3,4),(7,4),(47,2)],63,335336168,[3,7,47]⟩, ⟨[(3,4),(13,2),(17,1)],117,165861,[3,13]⟩, ⟨[(3,4),(13,2),(17,2)],117,2841780,[3,13,17]⟩, ⟨[(3,4),(13,2),(17,3)],117,48332403,[3,13,17]⟩, ⟨[(3,4),(13,2),(19,2)],81,3494754,[13,19]⟩, ⟨[(3,4),(13,2),(19,3)],81,66422469,[3,13,19]⟩, ⟨[(3,4),(13,3),(17,2)],117,36980287,[3,13,17]⟩, ⟨[(3,4),(13,3),(17,3)],117,628952859,[3,13,17]⟩, ⟨[(3,5),(5,1),(11,1)],81,12843,[3]⟩, ⟨[(3,5),(5,1),(13,1)],65,14781,[]⟩]
theorem schOk46 : sch46.all checkSeedFull = true := by decide +kernel
def sch47 : List Seed := [⟨[(3,5),(5,1),(19,1)],81,20595,[]⟩, ⟨[(3,5),(5,1),(47,1)],135,47727,[]⟩, ⟨[(3,6),(5,2)],81,15658,[]⟩, ⟨[(3,6),(5,2),(83,2)],81,110714134,[83]⟩, ⟨[(3,6),(5,4)],81,398008,[5]⟩, ⟨[(3,6),(5,6)],81,9956758,[5]⟩, ⟨[(3,6),(7,4),(13,2)],63,264447618,[7]⟩, ⟨[(3,6),(7,4),(13,4)],63,44734508344,[7,13]⟩, ⟨[(3,8),(5,2),(83,2)],81,997291858,[3,83]⟩, ⟨[(3,8),(5,4)],81,3585196,[3]⟩, ⟨[(3,8),(5,6)],81,89688946,[3,5]⟩, ⟨[(3,8),(7,4),(13,2)],63,2382078894,[3,7]⟩, ⟨[(3,8),(13,2),(19,2)],81,285863994,[3,19]⟩, ⟨[(5,1),(7,1),(11,1),(13,1)],385,3059,[]⟩]
theorem schOk47 : sch47.all checkSeedFull = true := by decide +kernel
def seedChunks : List (List Seed) := [sch0, sch1, sch2, sch3, sch4, sch5, sch6, sch7, sch8, sch9, sch10, sch11, sch12, sch13, sch14, sch15, sch16, sch17, sch18, sch19, sch20, sch21, sch22, sch23, sch24, sch25, sch26, sch27, sch28, sch29, sch30, sch31, sch32, sch33, sch34, sch35, sch36, sch37, sch38, sch39, sch40, sch41, sch42, sch43, sch44, sch45, sch46, sch47]
def allSeeds : List Seed := seedChunks.flatten
theorem allChunksOk : seedChunks.all (fun ch => ch.all checkSeedFull) = true := by
  simp only [seedChunks, List.all_cons, List.all_nil, Bool.and_true, schOk0, schOk1, schOk2, schOk3, schOk4, schOk5, schOk6, schOk7, schOk8, schOk9, schOk10, schOk11, schOk12, schOk13, schOk14, schOk15, schOk16, schOk17, schOk18, schOk19, schOk20, schOk21, schOk22, schOk23, schOk24, schOk25, schOk26, schOk27, schOk28, schOk29, schOk30, schOk31, schOk32, schOk33, schOk34, schOk35, schOk36, schOk37, schOk38, schOk39, schOk40, schOk41, schOk42, schOk43, schOk44, schOk45, schOk46, schOk47]
lemma allSeeds_valid : ∀ s ∈ allSeeds, SeedValid s := by
  intro s hs
  rw [allSeeds, List.mem_flatten] at hs
  rcases hs with ⟨ch, hch, hs_ch⟩
  have h1 : ch.all checkSeedFull = true := (List.all_eq_true.mp allChunksOk) ch hch
  exact checkSeedFull_sound s (List.all_eq_true.mp h1 s hs_ch)
def allSurvs : List (Nat × List Nat) := [(1575,[1,5,7,15,21,25]), (3465,[1,3,7,9,11,15,33,35,45,55,63,77,99,105]), (4095,[3,5,9,13,21,35,39,45,63,91,105,117]), (5355,[3,5,9,15,17,21,35,45,63,85,105,119]), (5775,[7,11,15,21,25,33,35,55,75,77]), (5985,[3,5,9,15,19,21,35,45,57,63,105,133]), (6435,[1,3,9,11,13,15,33,39,45,65]), (6825,[3,5,7,13,15,21,25,35,39,75]), (7245,[1,3,5,9,15,21,35,45,63,69,105,115]), (8085,[1,3,5,7,15,21,33,35,49,77]), (9135,[1,3,5,7,9,21,29,35,45,63,87,145]), (9765,[1,3,5,7,9,15,21,31,35,63,93,155]), (11655,[3,5,7,15,21,35,37,63,105,111]), (12705,[1,3,7,11,15,21,33,35]), (12915,[5,9,15,35,41,45,105,123]), (13545,[3,5,7,15,21,35,43,45,63,129]), (14805,[1,3,7,15,21,35,45,47,63,105]), (16695,[1,5,7,9,15,21,35,45,63,105]), (18585,[1,3,5,7,9,15,21,45,59,105]), (19215,[1,3,5,9,15,21,35,45,61,63]), (19635,[3,5,7,11,15,21,33,35,51,55,77,85,105,119,165,187,231,255,357,385]), (21105,[5,7,9,15,21,35,63,67]), (22365,[3,7,9,15,21,35,45,63]), (22995,[1,5,7,9,21,35,45,63]), (24885,[1,3,5,7,15,21,35,63]), (26145,[1,3,5,7,9,21,35,45]), (28035,[3,7,9,15,21,35]), (28215,[1,5,9,11,15,19,27,33,45,55,95,99,135,165,171,285]), (29835,[1,5,13,15,17,27,39,45,51,65,85,117,135,195]), (31395,[5,7,13,15,21,23,35,65,69,91,105,161,195,273,299,345]), (33345,[1,3,5,9,13,15,19,27,39,45,57,65,95,117]), (33915,[3,5,7,15,19,21,35,51,57,85,95,105,119,133,255,285]), (41055,[1,3,5,15,17,21,23,35,51,69,105,115,119,255]), (42735,[1,3,5,7,15,21,33,35,37,77,105,111,165,185,231,259,385,407]), (43065,[1,3,9,11,15,27,29,33,55,87]), (45885,[3,5,15,19,21,23,35,69,95,105]), (49875,[3,7,15,19,21,25]), (50505,[3,5,7,15,21,35,37,65,91,105,111,185,195,259]), (61215,[1,3,5,7,15,21,33,35,53,55,77,105,159,165,231,265,371,385]), (68145,[1,5,7,11,15,21,33,55,59,77,165,177,231,295,385,413]), (72345,[3,7,13,15,21,35,53,65,91,159]), (76725,[1,5,9,11,25,31,33,45,55,75,93,99,155,165,225,275]), (80535,[3,5,7,15,21,35,59,65]), (82005,[3,5,7,11,15,33,35,55,71,77,105,165,213,231,355,497]), (84315,[1,3,5,7,15,21,33,35,73,77,105,165,219,231,365,511]), (91245,[7,11,15,33,35,55,77,79,105,165,231,237,385,395]), (95865,[1,3,5,11,15,21,33,35,55,77,105,165,231,249,385,415]), (102795,[1,3,5,7,11,21,33,35,55,77,89,105,231,267,385,445]), (112035,[7,11,15,21,33,35,55,77,97,105,165,231,385,485]), (116655,[3,5,7,11,15,33,55,77,101,105,165,231,385,505]), (118965,[1,3,7,11,15,21,33,35,55,77,103,105,165,231,309,515]), (123585,[1,5,11,15,21,33,35,77,105,107,165,231,321,535]), (125895,[1,5,7,11,21,33,35,55,105,109,165,231,327,545]), (130515,[1,3,5,11,15,21,33,55,77,105,165,231,339,565]), (146685,[1,5,11,15,21,33,35,55,77,127,165,231,381,385]), (151305,[1,5,7,11,15,33,35,55,77,105,165,231,385,393]), (158235,[1,3,5,7,11,21,33,55,77,105,137,231,385,411]), (160545,[5,7,11,15,21,33,35,55,77,105,139,165,385,417]), (172095,[3,7,11,15,33,35,55,105,149,165,385,447]), (174405,[5,7,11,21,33,35,55,77,151,165,385,453]), (181335,[7,11,15,33,35,55,77,105,157,165,231,471]), (188265,[3,11,15,21,33,35,55,105,163,165,231,489]), (192885,[1,5,7,15,21,33,35,55,77,105,165,167,231,385]), (199815,[3,5,7,11,15,21,33,35,77,105,165,173,231,385]), (206745,[1,3,5,7,11,15,33,35,55,105,165,179,231,385]), (209055,[1,3,5,11,15,21,33,35,55,77,165,181,231,385]), (220605,[3,7,15,21,33,35,55,77,105,191,231,385]), (222915,[1,5,7,11,15,21,33,35,55,77,105,165,231,385]), (227535,[3,7,11,15,33,35,55,77,105,165,231,385]), (229845,[1,3,5,11,15,21,33,35,55,77,105,165,199,385]), (243705,[1,5,7,15,21,33,35,55,105,165,211,385]), (257565,[1,3,5,7,11,15,33,35,55,77,105,165,223,231]), (262185,[1,5,7,15,21,33,55,77,105,165,227,231]), (264495,[3,5,11,15,21,33,35,77,105,165,229,231]), (269115,[1,5,7,15,21,33,35,55,105,165,231,233]), (276045,[1,3,5,11,15,33,35,55,77,165,231,239]), (278355,[1,3,5,11,15,21,33,55,77,165,231,241]), (289905,[3,7,15,21,33,55,77,105,231,251]), (296835,[1,3,5,11,15,33,35,55,77,105,165,257]), (303765,[1,5,7,11,15,21,33,55,77,105,165,231]), (310695,[5,7,11,21,33,35,77,105,165,231]), (313005,[7,11,15,21,33,35,55,105,165,231]), (319935,[3,7,15,21,33,35,55,77,165,231]), (324555,[3,7,11,15,21,33,55,77,165,231]), (326865,[1,5,7,11,21,33,55,77,165,231]), (338415,[1,5,7,11,21,33,55,77,105,231]), (342225,[5,9,15,25,27,39,45,65,75,81,117,135,169,195,225,351,405]), (354585,[3,5,7,11,21,33,35,77,105,165]), (359205,[1,5,7,11,21,33,35,55,105,165]), (361515,[7,11,15,33,35,55,105,165]), (366135,[1,3,7,11,15,33,35,55,77,165]), (382305,[1,3,5,7,11,21,33,55,77,105]), (389235,[7,11,15,21,33,35,55,105]), (400785,[3,7,11,15,21,33,55,77]), (403095,[1,5,7,11,21,33,55,77]), (407715,[1,3,5,7,11,15,21,33,35,55]), (414645,[3,5,7,11,15,21,33,55]), (423885,[3,5,11,15,33,35]), (430815,[7,11,15,33])]
def c3_1 : Cert := (S7 5 B (S7 7 (SP 11 B (SP 13 B B (K5 41 [] B) (K5 42 [] B)) (SP 13 B (K5 45 [] B) (K5 46 [] B) (K5 47 [] B)) (SP 13 B (K5 48 [] B) (K5 49 [] B) (K5 50 [] B))) (SP 11 (SP 13 (SP 17 (SP 19 B (SP 23 B (AS 35) (NP 4) (NP 4)) (K5 4 [] B) (K5 5 [] B)) (SP 19 (SP 23 (SP 29 (SP 31 B B (AC 3 8 []) (NP 4)) (AC 3 6 []) (NP 4) (NP 4)) (AS 32) (NP 4) (NP 4)) (AS 31) (NP 4) (NP 4)) (K5 2 [] B) (K5 3 [] B)) (SP 17 (SP 19 (SP 23 (SP 29 (SP 31 (SP 37 (SP 41 (SP 43 (SP 47 (SP 53 (SP 59 (SP 61 B (AC 3 12 []) (NP 4) (NP 4)) (AS 42) (NP 4) (NP 4)) (AS 40) (NP 4) (NP 4)) (AC 3 11 []) (NP 4) (NP 4)) (AC 3 10 []) (NP 4) (NP 4)) (AC 3 9 []) (NP 4) (NP 4)) (AS 37) (NP 4) (NP 4)) (AC 3 7 []) (NP 4) (NP 4)) (AC 3 6 []) (NP 4) (NP 4)) (AS 29) (NP 4) (NP 4)) (AC 1 107 []) (NP 4) (NP 4)) (AC 1 106 []) (NP 4) (NP 4)) (K5 0 [] B) (K5 1 [] B)) (SP 13 (SP 17 (SP 19 (SP 23 (SP 29 (SP 31 (SP 37 (SP 41 (SP 43 (SP 47 (SP 53 (SP 59 (SP 61 (SP 67 (SP 71 (SP 73 (SP 79 (SP 83 (SP 89 (SP 97 (SP 101 (SP 103 (SP 107 (SP 109 (SP 113 (SP 127 (SP 131 (SP 137 (SP 139 (SP 149 (SP 151 (SP 157 (SP 163 (SP 167 (SP 173 (SP 179 (SP 181 (SP 191 (SP 193 (SP 197 (SP 199 (SP 211 (SP 223 (SP 227 (SP 229 (SP 233 (SP 239 (SP 241 (SP 251 (SP 257 (SP 263 (SP 269 (SP 271 (SP 277 (SP 281 (SP 283 (SP 293 (SP 307 (SP 311 (SP 313 (SP 317 (SP 331 (SP 337 (SP 347 (SP 349 (SP 353 (SP 359 (SP 367 (SP 373 (SP 379 (SP 383 B AL (NP 4) (NP 4)) AL (NP 4) (NP 4)) (AS 98) (NP 4) (NP 4)) (AS 97) (NP 4) (NP 4)) (AS 96) (NP 4) (NP 4)) (AS 95) (NP 4) (NP 4)) (AS 94) (NP 4) (NP 4)) (AS 93) (NP 4) (NP 4)) (AS 92) (NP 4) (NP 4)) (AS 91) (NP 4) (NP 4)) (AS 90) (NP 4) (NP 4)) (AS 89) (NP 4) (NP 4)) (AS 88) (NP 4) (NP 4)) (AS 87) (NP 4) (NP 4)) (AS 85) (NP 4) (NP 4)) (AS 84) (NP 4) (NP 4)) (AS 83) (NP 4) (NP 4)) (AS 82) (NP 4) (NP 4)) (AS 81) (NP 4) (NP 4)) (AS 80) (NP 4) (NP 4)) (AS 79) (NP 4) (NP 4)) (AS 78) (NP 4) (NP 4)) (AS 77) (NP 4) (NP 4)) (AS 76) (NP 4) (NP 4)) (AS 75) (NP 4) (NP 4)) (AS 74) (NP 4) (NP 4)) (AS 73) (NP 4) (NP 4)) (AS 72) (NP 4) (NP 4)) (AS 71) (NP 4) (NP 4)) (AS 70) (NP 4) (NP 4)) (AS 69) (NP 4) (NP 4)) (AS 68) (NP 4) (NP 4)) (AS 67) (NP 4) (NP 4)) (AS 66) (NP 4) (NP 4)) (AS 65) (NP 4) (NP 4)) (AS 64) (NP 4) (NP 4)) (AS 63) (NP 4) (NP 4)) (AS 62) (NP 4) (NP 4)) (AS 61) (NP 4) (NP 4)) (AS 60) (NP 4) (NP 4)) (AS 59) (NP 4) (NP 4)) (AS 58) (NP 4) (NP 4)) (AS 57) (NP 4) (NP 4)) (AS 56) (NP 4) (NP 4)) (AS 55) (NP 4) (NP 4)) (AS 54) (NP 4) (NP 4)) (AS 53) (NP 4) (NP 4)) (AS 52) (NP 4) (NP 4)) (AS 51) (NP 4) (NP 4)) (AS 50) (NP 4) (NP 4)) (AS 49) (NP 4) (NP 4)) (AS 48) (NP 4) (NP 4)) (AS 47) (NP 4) (NP 4)) (AS 46) (NP 4) (NP 4)) (AS 45) (NP 4) (NP 4)) (AS 44) (NP 4) (NP 4)) (AS 43) (NP 4) (NP 4)) (AC 3 13 []) (NP 4) (NP 4)) (AC 3 12 []) (NP 4) (NP 4)) (AS 39) (NP 4) (NP 4)) (AS 38) (NP 4) (NP 4)) (AC 3 11 []) (NP 4) (NP 4)) (AC 3 10 []) (NP 4) (NP 4)) (AC 3 9 []) (NP 4) (NP 4)) (AS 33) (NP 4) (NP 4)) (AC 3 7 []) (NP 4) (NP 4)) (AC 2 44 []) (NP 4) (NP 4)) (AC 2 43 []) (NP 4) (NP 4)) (AC 1 105 []) (NP 4) (NP 4)) (AS 20) (NP 4) (NP 4)) (AC 0 718 []) (NP 4) (NP 4)) (AS 13) (NP 3)) (SP 11 (SP 13 (SP 17 (SP 19 (SP 23 B (K5 20 [] B) (K5 21 [] B) (K5 22 [] B)) (K5 17 [] B) (K5 18 [] B) (K5 19 [] B)) (K5 14 [] B) (K5 15 [] B) (K5 16 [] B)) AL (NP 3) (NP 3)) (AS 9) (NP 2) (NP 2)) (SP 11 (SP 13 (SP 17 (SP 19 (SP 23 B (K5 29 [] B) (K5 30 [] B) (K5 31 [] B)) (K5 26 [] B) (K5 27 [] B) (K5 28 [] B)) (K5 23 [] B) (K5 24 [] B) (K5 25 [] B)) (NP 2) (NP 2) (NP 2)) (NP 2) (NP 2) (NP 2)) (SP 11 (SP 13 (SP 17 (SP 19 (SP 23 B (K5 38 [] B) (K5 39 [] B) (K5 40 [] B)) (K5 35 [] B) (K5 36 [] B) (K5 37 [] B)) (K5 32 [] B) (K5 33 [] B) (K5 34 [] B)) (NP 2) (NP 2) (NP 2)) (NP 2) (NP 2) (NP 2))) (S7 7 (SP 11 (SP 13 B B (K3 72 [] B) (K3 73 [] B)) (SP 13 (SP 17 B (K5 67 [] B) (K5 68 [] B) (K5 69 [] B)) (K5 66 [] B) (K5 72 [2] B) (K5 73 [2] B)) (K3 70 [] B) (K3 71 [] B)) (SP 11 (SP 13 (SP 17 (SP 19 (SP 23 (SP 29 (SP 31 B (K5 60 [] B) (K5 61 [] B) (K5 62 [] B)) (K5 57 [] B) (K5 58 [] B) (K5 59 [] B)) (K5 54 [] B) (K5 55 [] B) (K5 56 [] B)) (K5 51 [] B) (K5 52 [] B) (K5 53 [] B)) AL (NP 3) (NP 3)) (AS 7) (NP 3) (NP 3)) (AS 4) (NP 1) (NP 1)) (K3 63 [] B) (K3 64 [] B) (K3 65 [] B)) (S7 7 (SP 11 (SP 13 B (K3 92 [] B) (K3 93 [] B) (K3 94 [] B)) (K3 89 [] B) (K3 90 [] B) (K3 91 [] B)) (SP 11 (SP 13 (SP 17 (SP 19 (SP 23 (SP 29 (SP 31 (SP 37 B (K5 83 [] B) (K5 84 [] B) (K5 85 [] B)) (K5 80 [] B) (K5 81 [] B) (K5 82 [] B)) (K5 77 [] B) (K5 78 [] B) (K5 79 [] B)) (K5 74 [] B) (K5 75 [] B) (K5 76 [] B)) (AS 36) (NP 3) (NP 3)) (NP 1) (NP 1) (NP 1)) (NP 1) (NP 1) (NP 1)) (NP 1) (NP 1) (NP 1)) (K3 86 [] B) (K3 87 [] B) (K3 88 [] B)) (S7 7 (SP 11 (SP 13 B (K3 102 [] B) (K3 103 [] B) (K3 104 [] B)) (K3 99 [] B) (K3 100 [] B) (K3 101 [] B)) (K3 95 [] B) (K3 96 [] B) (K3 97 [] B) (K3 98 [] B)))
theorem ok_c3_1 : checkCert allSeeds allSurvs true 200 c3_1 [⟨3,1,true,.odd⟩] 5 = true := by decide +kernel
def c3_2 : Cert := (S7 5 (S7 7 B (SP 11 (SP 13 B B (SP 17 B B (K5 282 [] B) (K5 283 [] B)) (SP 17 B B (K5 284 [] B) (K5 285 [] B))) (SP 13 (SP 17 B (K5 277 [] B) (K5 278 [] B) (K5 279 [] B)) (K5 274 [] B) (K5 275 [] B) (K5 276 [] B)) (K3 280 [] B) (K3 281 [] B)) (SP 11 (SP 13 B (K3 289 [] B) (K3 290 [] B) (K3 291 [] B)) (K3 286 [] B) (K3 287 [] B) (K3 288 [] B)) (SP 11 (SP 13 B (K3 295 [] B) (K3 296 [] B) (K3 297 [] B)) (K3 292 [] B) (K3 293 [] B) (K3 294 [] B)) (SP 11 (SP 13 B (K3 301 [] B) (K3 302 [] B) (K3 303 [] B)) (K3 298 [] B) (SP 13 (SP 17 (SP 19 (SP 23 B (K5 299 [3] B) (KV 2 306 [] B) (K5 299 [3] B)) (K5 299 [3] B) (KV 2 305 [] B) (K5 299 [3] B)) (K5 299 [3] B) (KV 2 304 [] B) (K5 299 [3] B)) (K5 299 [3] B) (NP 1) (NP 1)) (K3 300 [] B))) (S7 7 (SP 11 (SP 13 (SP 17 B (SP 19 B (K5 186 [] B) (K5 189 [2] B) (K5 190 [2] B)) (SP 19 B (K5 187 [] B) (K5 189 [2] B) (K5 190 [2] B)) (SP 19 B (K5 188 [] B) (K5 189 [2] B) (K5 190 [2] B))) (SP 17 (SP 19 (SP 23 B (K5 181 [] B) (K5 182 [] B) (K5 183 [] B)) (K5 180 [] B) (K5 189 [2] B) (K5 190 [2] B)) (K5 177 [] B) (K5 178 [] B) (K5 179 [] B)) (K3 184 [] B) (K3 185 [] B)) (SP 13 (SP 17 (SP 19 (SP 23 (SP 29 (SP 31 B (K5 172 [] B) (K5 173 [] B) (K5 174 [] B)) (K5 169 [] B) (K5 170 [] B) (K5 171 [] B)) (K5 166 [] B) (K5 167 [] B) (K5 168 [] B)) (K5 165 [] B) (K5 189 [2] B) (K5 190 [2] B)) AL (NP 3) (NP 3)) (AS 6) (NP 3) (NP 3)) (K3 175 [] B) (K3 176 [] B)) (SP 11 (SP 13 (SP 17 (SP 19 (SP 23 (SP 29 (SP 31 (SP 37 (SP 41 (SP 43 (SP 47 (SP 53 (SP 59 (SP 61 (SP 67 (SP 71 (SP 73 (SP 79 (SP 83 (SP 89 (SP 97 (SP 101 (SP 103 (SP 107 (SP 109 (SP 113 (SP 127 (SP 131 (SP 137 (SP 139 (SP 149 (SP 151 (SP 157 (SP 163 (SP 167 (SP 173 (SP 179 (SP 181 (SP 191 (SP 193 (SP 197 (SP 199 B (K5 162 [] B) (K5 163 [] B) (K5 164 [] B)) (K5 159 [] B) (K5 160 [] B) (K5 161 [] B)) (K5 156 [] B) (K5 157 [] B) (K5 158 [] B)) (K5 153 [] B) (K5 154 [] B) (K5 155 [] B)) (K5 150 [] B) (K5 151 [] B) (K5 152 [] B)) (K5 147 [] B) (K5 148 [] B) (K5 149 [] B)) (K5 144 [] B) (K5 145 [] B) (K5 146 [] B)) (K5 141 [] B) (K5 142 [] B) (K5 143 [] B)) (K5 138 [] B) (K5 139 [] B) (K5 140 [] B)) (K5 135 [] B) (K5 136 [] B) (K5 137 [] B)) (K5 132 [] B) (K5 133 [] B) (K5 134 [] B)) (K5 129 [] B) (K5 130 [] B) (K5 131 [] B)) (K5 126 [] B) (K5 127 [] B) (K5 128 [] B)) (K5 123 [] B) (K5 124 [] B) (K5 125 [] B)) (K5 120 [] B) (K5 121 [] B) (K5 122 [] B)) (K5 117 [] B) (K5 118 [] B) (K5 119 [] B)) (K5 114 [] B) (K5 115 [] B) (K5 116 [] B)) (K5 111 [] B) (K5 112 [] B) (K5 113 [] B)) (K5 108 [] B) (K5 109 [] B) (K5 110 [] B)) AL (NP 3) (NP 3)) AL (NP 3) (NP 3)) AL (NP 3) (NP 3)) (AS 26) (NP 3) (NP 3)) (AS 25) (NP 3) (NP 3)) (AS 24) (NP 3) (NP 3)) (AS 23) (NP 3) (NP 3)) (AS 22) (NP 3) (NP 3)) (AS 21) (NP 3) (NP 3)) (AS 19) (NP 3) (NP 3)) (AS 18) (NP 3) (NP 3)) (AS 17) (NP 3) (NP 3)) (AS 16) (NP 3) (NP 3)) (AS 15) (NP 3) (NP 3)) (AS 14) (NP 3) (NP 3)) (AS 12) (NP 3) (NP 3)) (AS 11) (NP 3) (NP 3)) (AS 10) (NP 3) (NP 3)) (AS 8) (NP 3) (NP 3)) (AS 5) (NP 3) (NP 3)) (AS 3) (NP 3) (NP 3)) (AS 2) (NP 3) (NP 3)) (AS 1) (NP 0) (NP 0)) AL (NP 2) (NP 2)) (S7 7 (SP 11 (SP 13 (SP 17 (SP 19 (SP 23 B (K3 220 [] B) (SP 29 B (K5 221 [3] B) (KV 2 224 [] B) (K5 221 [3] B)) (K3 222 [] B)) (K3 217 [] B) (SP 23 (SP 29 (SP 31 B (K5 218 [3] B) (K5 218 [3] B) (K5 218 [3] B)) (K5 218 [3] B) (KV 2 224 [] B) (K5 218 [3] B)) (K5 218 [3] B) (KV 2 221 [] B) (K5 218 [3] B)) (K3 219 [] B)) (K3 214 [] B) (SP 19 (SP 23 (SP 29 (SP 31 (SP 37 B (K5 215 [3] B) (KV 2 226 [] B) (K5 215 [3] B)) (K5 215 [3] B) (K5 215 [3] B) (K5 215 [3] B)) (K5 215 [3] B) (KV 2 224 [] B) (K5 215 [3] B)) (K5 215 [3] B) (KV 2 221 [] B) (K5 215 [3] B)) (AC 2 217 []) (NP 2) (NP 2)) (K3 216 [] B)) (K3 211 [] B) (K3 212 [] B) (K3 213 [] B)) (SP 13 (SP 17 (SP 19 (SP 23 (SP 29 (SP 31 (SP 37 (SP 41 (SP 43 (SP 47 (SP 53 (SP 59 (SP 61 (SP 67 (SP 71 (SP 73 (SP 79 (SP 83 B B (K5 206 [] B) (K5 207 [] B)) (K5 203 [] B) (K5 204 [] B) (K5 205 [] B)) (K5 200 [] B) (K5 201 [] B) (K5 202 [] B)) (K5 197 [] B) (K5 198 [] B) (K5 199 [] B)) (K5 194 [] B) (K5 195 [] B) (K5 196 [] B)) (K5 236 [2] B) (K5 237 [2] B) (K5 238 [2] B)) (K5 233 [2] B) (K5 234 [2] B) (K5 235 [2] B)) (K5 191 [] B) (K5 192 [] B) (K5 193 [] B)) (K5 230 [2] B) (K5 231 [2] B) (K5 232 [2] B)) (K5 228 [2] B) (AC 2 229 []) (NP 3)) (AC 2 227 []) (NP 3) (NP 3)) (AC 2 225 []) (NP 3) (NP 3)) (AS 41) (NP 3) (NP 3)) (AC 2 223 []) (NP 3) (NP 3)) (AC 2 220 []) (NP 3) (NP 3)) (AC 2 217 []) (NP 3) (NP 3)) (NP 1) (NP 1) (NP 1)) (NP 1) (NP 1) (NP 1)) (SP 13 (SP 17 (SP 19 (SP 23 (SP 29 (SP 31 (SP 37 (SP 41 (SP 43 (SP 47 (SP 53 (SP 59 (SP 61 (SP 67 (SP 71 (SP 73 (SP 79 (SP 83 (SP 89 (SP 97 (SP 101 (SP 103 (SP 107 (SP 109 (SP 113 (SP 127 B (K5 208 [3] B) (KV 3 208 [] B) (K5 208 [3] B)) (K5 208 [3] B) (KV 3 208 [] B) (K5 208 [3] B)) (K5 208 [3] B) (KV 3 208 [] B) (K5 208 [3] B)) (K5 208 [3] B) (KV 3 208 [] B) (K5 208 [3] B)) (K5 208 [3] B) (KV 3 208 [] B) (K5 208 [3] B)) (K5 208 [3] B) (KV 3 208 [] B) (K5 208 [3] B)) (K5 208 [3] B) (KV 3 208 [] B) (K5 208 [3] B)) (K5 208 [3] B) (KV 3 208 [] B) (K5 208 [3] B)) (K5 208 [3] B) (KV 3 208 [] B) (K5 208 [3] B)) (K5 208 [3] B) (KV 3 208 [] B) (K5 208 [3] B)) (K5 208 [3] B) (KV 3 208 [] B) (K5 208 [3] B)) (K5 208 [3] B) (KV 3 208 [] B) (K5 208 [3] B)) (K5 208 [3] B) (SF 2 (KV 3 208 [] B) (AC 3 210 [])) (K5 208 [3] (KR 3 208 []))) (AC 2 236 []) (NP 3) (NP 3)) (AC 2 233 []) (NP 3) (NP 3)) (AC 3 208 []) (NP 3) (NP 3)) (AC 2 230 []) (NP 3) (NP 3)) (AC 2 228 []) (NP 2) (NP 2)) (NP 2) (NP 2) (NP 2)) (NP 2) (NP 2) (NP 2)) (NP 2) (NP 2) (NP 2)) (NP 2) (NP 2) (NP 2)) (NP 2) (NP 2) (NP 2)) (NP 1) (NP 1) (NP 1)) (NP 1) (NP 1) (NP 1)) (NP 1) (NP 1) (NP 1)) (K3 209 [] B)) (AS 0) (NP 1) (NP 1) (NP 1)) (S7 7 (SP 11 (SP 13 (SP 17 (SP 19 (SP 23 B (K3 251 [] B) (K3 252 [] B) (K3 253 [] B)) (K3 248 [] B) (K3 249 [] B) (K3 250 [] B)) (K3 245 [] B) (K3 246 [] B) (K3 247 [] B)) (K3 242 [] B) (K3 243 [] B) (K3 244 [] B)) (K3 239 [] B) (K3 240 [] B) (K3 241 [] B)) (NP 1) (NP 1) (NP 1) (NP 1)) (S7 7 (SP 11 (SP 13 (SP 17 (SP 19 (SP 23 B (K3 267 [] B) (SP 29 (SP 31 B (K5 268 [3] B) (KV 3 268 [] B) (K5 268 [3] B)) (K5 268 [3] B) (KV 2 270 [] B) (K5 268 [3] B)) (K3 269 [] B)) (K3 264 [] B) (SP 23 (SP 29 (SP 31 (SP 37 (SP 41 B B (KV 2 272 [] B) (K5 265 [3] B)) (K5 265 [3] B) (KV 2 271 [] B) (K5 265 [3] B)) (K5 265 [3] B) (KV 3 265 [] B) (K5 265 [3] B)) (K5 265 [3] B) (KV 2 270 [] B) (K5 265 [3] B)) (K5 265 [3] B) (KV 2 268 [] B) (K5 265 [3] B)) (K3 266 [] B)) (K3 261 [] B) (SP 19 (SP 23 (SP 29 (SP 31 (SP 37 (SP 41 (SP 43 B (K5 262 [3] B) (KV 2 273 [] B) (K5 262 [3] B)) (K5 262 [3] B) (KV 2 272 [] B) (K5 262 [3] B)) (K5 262 [3] B) (KV 2 271 [] B) (K5 262 [3] B)) (K5 262 [3] B) (KV 3 262 [] B) (K5 262 [3] B)) (K5 262 [3] B) (KV 2 270 [] B) (K5 262 [3] B)) (AC 2 267 []) (NP 1) (NP 1)) (NP 1) (NP 1) (NP 1)) (K3 263 [] B)) (K3 258 [] B) (K3 259 [] B) (K3 260 [] B)) (K3 254 [] B) (SP 13 (SP 17 (SP 19 (SP 23 (SP 29 (SP 31 (SP 37 (SP 41 (SP 43 (SP 47 (SP 53 (SP 59 (SP 61 (SP 67 (SP 71 (SP 73 (SP 79 (SP 83 (SP 89 (SP 97 (SP 101 (SP 103 (SP 107 (SP 109 (SP 113 (SP 127 (SP 131 (SP 137 (SP 139 (SP 149 (SP 151 (SP 157 (SP 163 (SP 167 (SP 173 (SP 179 (SP 181 (SP 191 (SP 193 (SP 197 (SP 199 (SP 211 (SP 223 (SP 227 (SP 229 (SP 233 (SP 239 (SP 241 (SP 251 (SP 257 (SP 263 (SP 269 (SP 271 (SP 277 (SP 281 B (K5 255 [3] B) (KV 3 255 [] B) (K5 255 [3] B)) (K5 255 [3] B) (KV 3 255 [] B) (K5 255 [3] B)) (K5 255 [3] B) (KV 3 255 [] B) (K5 255 [3] B)) (K5 255 [3] B) (KV 3 255 [] B) (K5 255 [3] B)) (K5 255 [3] B) (KV 3 255 [] B) (K5 255 [3] B)) (K5 255 [3] B) (KV 3 255 [] B) (K5 255 [3] B)) (K5 255 [3] B) (KV 3 255 [] B) (K5 255 [3] B)) (K5 255 [3] B) (KV 3 255 [] B) (K5 255 [3] B)) (K5 255 [3] B) (KV 3 255 [] B) (K5 255 [3] B)) (K5 255 [3] B) (KV 3 255 [] B) (K5 255 [3] B)) (K5 255 [3] B) (KV 3 255 [] B) (K5 255 [3] B)) (K5 255 [3] B) (KV 3 255 [] B) (K5 255 [3] B)) (K5 255 [3] B) (KV 3 255 [] B) (K5 255 [3] B)) (K5 255 [3] B) (KV 3 255 [] B) (K5 255 [3] B)) (K5 255 [3] B) (KV 3 255 [] B) (K5 255 [3] B)) (K5 255 [3] B) (KV 3 255 [] B) (K5 255 [3] B)) (K5 255 [3] B) (KV 3 255 [] B) (K5 255 [3] B)) (K5 255 [3] B) (KV 3 255 [] B) (K5 255 [3] B)) (K5 255 [3] B) (KV 3 255 [] B) (K5 255 [3] B)) (K5 255 [3] B) (KV 3 255 [] B) (K5 255 [3] B)) (K5 255 [3] B) (KV 3 255 [] B) (K5 255 [3] B)) (K5 255 [3] B) (KV 3 255 [] B) (K5 255 [3] B)) (K5 255 [3] B) (KV 3 255 [] B) (K5 255 [3] B)) (K5 255 [3] B) (KV 3 255 [] B) (K5 255 [3] B)) (K5 255 [3] B) (KV 3 255 [] B) (K5 255 [3] B)) (K5 255 [3] B) (KV 3 255 [] B) (K5 255 [3] B)) (K5 255 [3] (SF 2 B (SF 1 B (NP 1)))) (SF 2 (KV 3 255 [] B) (SF 1 (K5 257 [3] B) (NP 1))) (K5 255 [3] (KR 3 255 []))) (K5 255 [3] (SF 2 B (SF 1 B (NP 1)))) (SF 2 (KV 3 255 [] B) (AC 3 257 [])) (K5 255 [3] (KR 3 255 []))) (K5 255 [3] (SF 2 B (NP 2))) (SF 2 (KV 3 255 [] B) (NP 2)) (K5 255 [3] (KR 3 255 []))) (K5 255 [3] (SF 2 (SF 1 B (NP 1)) (NP 2))) (SF 2 (SF 1 (K5 255 [3] B) (NP 1)) (NP 2)) (K5 255 [3] (KR 3 255 []))) (AC 3 255 []) (NP 3) (NP 3)) (AC 3 255 []) (NP 3) (NP 3)) (AC 3 255 []) (NP 1) (NP 1)) (NP 1) (NP 1) (NP 1)) (NP 1) (NP 1) (NP 1)) (NP 1) (NP 1) (NP 1)) (NP 1) (NP 1) (NP 1)) (NP 1) (NP 1) (NP 1)) (NP 1) (NP 1) (NP 1)) (NP 1) (NP 1) (NP 1)) (NP 1) (NP 1) (NP 1)) (NP 1) (NP 1) (NP 1)) (NP 1) (NP 1) (NP 1)) (NP 1) (NP 1) (NP 1)) (NP 1) (NP 1) (NP 1)) (NP 1) (NP 1) (NP 1)) (NP 1) (NP 1) (NP 1)) (NP 1) (NP 1) (NP 1)) (NP 1) (NP 1) (NP 1)) (NP 1) (NP 1) (NP 1)) (NP 1) (NP 1) (NP 1)) (NP 1) (NP 1) (NP 1)) (NP 1) (NP 1) (NP 1)) (NP 1) (NP 1) (NP 1)) (NP 1) (NP 1) (NP 1)) (K3 256 [] B)) (NP 1) (NP 1) (NP 1) (NP 1)))
theorem ok_c3_2 : checkCert allSeeds allSurvs true 200 c3_2 [⟨3,2,true,.even⟩] 5 = true := by decide +kernel
def c3_3 : Cert := (S7 5 (S7 7 (SP 11 B B (SP 13 B B (SP 17 B B (K5 521 [] B) (K5 522 [] B)) (SP 17 B B (K5 523 [] B) (K5 524 [] B))) (SP 13 B B (SP 17 B B (K5 525 [] B) (K5 526 [] B)) (SP 17 B B (K5 527 [] B) (K5 528 [] B)))) (SP 11 (SP 13 (SP 17 B (K3 479 [] B) (K3 480 [] B) (K3 481 [] B)) (SP 17 (SP 19 B (K5 482 [2] B) (K5 483 [2] B) (K5 484 [2] B)) (K5 479 [2] B) (K5 480 [2] B) (K5 481 [2] B)) (K3 477 [] B) (K3 478 [] B)) (SP 13 (SP 17 (SP 19 (SP 23 (SP 29 B B (K5 488 [2] B) (K5 489 [2] B)) (K5 485 [2] B) (K5 486 [2] B) (K5 487 [2] B)) (K5 482 [2] B) (K5 483 [2] B) (K5 484 [2] B)) (K5 479 [2] B) (K5 480 [2] B) (K5 481 [2] B)) (K5 474 [] (SF 0 B (NP 0))) AL (NP 3)) (K3 475 [] B) (K3 476 [] B)) (SP 11 (SP 13 (SP 17 B (K3 496 [] B) (K3 497 [] B) (K3 498 [] B)) (K3 493 [] B) (K3 494 [] B) (K3 495 [] B)) (K3 490 [] B) (K3 491 [] B) (K3 492 [] B)) (SP 11 (SP 13 (SP 17 (SP 19 B B (K3 508 [] B) (K3 509 [] B)) (K3 505 [] B) (K3 506 [] B) (K3 507 [] B)) (K3 502 [] B) (K3 503 [] B) (K3 504 [] B)) (K3 499 [] B) (K3 500 [] B) (K3 501 [] B)) (SP 11 (SP 13 (SP 17 (SP 19 B B (K3 519 [] B) (K3 520 [] B)) (K3 516 [] B) (K3 517 [] B) (K3 518 [] B)) (K3 513 [] B) (K3 514 [] B) (K3 515 [] B)) (K3 510 [] B) (K3 511 [] B) (K3 512 [] B))) (S7 7 (SP 11 (SP 13 (SP 17 (SP 19 (SP 23 B (K3 402 [] B) (K3 403 [] B) (K3 404 [] B)) (SP 23 (SP 29 (SP 31 B (K5 405 [2] B) (K5 406 [2] B) (K5 407 [2] B)) (K5 397 [] B) (K5 398 [] B) (K5 399 [] B)) (K5 402 [2] B) (K5 403 [2] B) (K5 404 [2] B)) (K3 400 [] B) (K3 401 [] B)) (SP 19 (SP 23 (SP 29 (SP 31 (SP 37 (SP 41 B B (K5 393 [] B) (K5 394 [] B)) (K5 390 [] B) (K5 391 [] B) (K5 392 [] B)) (K5 405 [2] B) (K5 406 [2] B) (K5 407 [2] B)) (K5 387 [] B) (K5 388 [] B) (K5 389 [] B)) (K5 402 [2] B) (K5 403 [2] B) (K5 404 [2] B)) (K5 386 [] (SF 0 B (AC 2 705 []))) (K5 400 [2] (KR 2 400 [])) (K5 401 [2] (KR 2 401 []))) (K3 395 [] B) (K3 396 [] B)) (SP 17 (SP 19 (SP 23 (SP 29 (SP 31 (SP 37 (SP 41 (SP 43 (SP 47 (SP 53 (SP 59 (SP 61 B (K5 381 [] B) (K5 382 [] B) (K5 383 [] B)) (K5 378 [] B) (K5 379 [] B) (K5 380 [] B)) (K5 375 [] B) (K5 376 [] B) (K5 377 [] B)) (K5 372 [] B) (K5 373 [] B) (K5 374 [] B)) (K5 369 [] B) (K5 370 [] B) (K5 371 [] B)) (K5 366 [] B) (K5 367 [] B) (K5 368 [] B)) (K5 363 [] B) (K5 364 [] B) (K5 365 [] B)) (K5 405 [2] (KR 2 405 [])) (K5 406 [2] (KR 2 406 [])) (K5 407 [2] (KR 2 407 []))) (K5 360 [] (SF 0 B (AC 3 704 []))) (K5 361 [] (SF 0 B (NP 3))) (K5 362 [] (SF 0 B (NP 3)))) (K5 402 [2] (KR 2 402 [])) (AC 2 403 []) (NP 3)) (AS 30) (NP 3) (NP 3)) (AS 28) (NP 3) (NP 3)) (K3 384 [] B) (K3 385 [] B)) (SP 13 (SP 17 (SP 19 (SP 23 (SP 29 (SP 31 (SP 37 (SP 41 (SP 43 (SP 47 (SP 53 (SP 59 (SP 61 (SP 67 (SP 71 (SP 73 (SP 79 (SP 83 (SP 89 (SP 97 (SP 101 (SP 103 (SP 107 B (K5 355 [] B) (K5 356 [] B) (K5 357 [] B)) (K5 352 [] B) (K5 353 [] B) (K5 354 [] B)) (K5 349 [] B) (K5 350 [] B) (K5 351 [] B)) (K5 346 [] B) (K5 347 [] B) (K5 348 [] B)) (K5 343 [] B) (K5 344 [] B) (K5 345 [] B)) (K5 340 [] B) (K5 341 [] B) (K5 342 [] B)) (K5 337 [] B) (K5 338 [] B) (K5 339 [] B)) (K5 334 [] B) (K5 335 [] B) (K5 336 [] B)) (K5 331 [] B) (K5 332 [] B) (K5 333 [] B)) (K5 328 [] B) (K5 329 [] B) (K5 330 [] B)) (K5 325 [] B) (K5 326 [] B) (K5 327 [] B)) (K5 322 [] B) (K5 323 [] B) (K5 324 [] B)) (K5 319 [] (SF 0 B (KR 3 703 []))) (K5 320 [] (SF 0 B (KR 3 703 []))) (K5 321 [] (SF 0 B (KR 3 703 [])))) (K5 316 [] (SF 0 B (AC 2 706 []))) (K5 317 [] (SF 0 B (NP 3))) (K5 318 [] (SF 0 B (NP 3)))) (K5 313 [] (SF 0 B (NP 0))) (K5 314 [] (SF 0 B (NP 0))) (K5 315 [] (SF 0 B (NP 0)))) (K5 310 [] (SF 0 B (NP 0))) (K5 311 [] (SF 0 B (NP 0))) (K5 312 [] (SF 0 B (NP 0)))) (K5 307 [] (SF 0 B (NP 0))) (K5 308 [] (SF 0 B (NP 0))) (K5 309 [] (SF 0 B (NP 0)))) (AC 2 405 []) (NP 3) (NP 3)) (AS 34) (NP 3) (NP 3)) (AC 2 402 []) (NP 3) (NP 3)) (AS 27) (NP 3) (NP 3)) (NP 0) (NP 0) (NP 0)) (NP 0) (NP 0) (NP 0)) (K3 358 [] B) (K3 359 [] B)) AL (NP 0) (NP 0) (NP 0)) (S7 7 (SP 11 (SP 13 (SP 17 (SP 19 (SP 23 (SP 29 (SP 31 (SP 37 B (K3 426 [] B) (K3 427 [] B) (K3 428 [] B)) (K3 423 [] B) (K3 424 [] B) (K3 425 [] B)) (K3 420 [] B) (K3 421 [] B) (K3 422 [] B)) (K3 417 [] B) (K3 418 [] B) (K3 419 [] B)) (K3 414 [] B) (K3 415 [] B) (K3 416 [] B)) (K3 411 [] B) (K3 412 [] B) (K3 413 [] B)) (SF 0 (K3 408 [] B) AL) (SF 0 (K3 409 [] B) (NP 0)) (SF 0 (K3 410 [] B) (NP 0))) AL (NP 2) (NP 2)) (NP 0) (NP 0) (NP 0) (NP 0)) (S7 7 (SP 11 (SP 13 (SP 17 (SP 19 (SP 23 (SP 29 (SP 31 (SP 37 (SP 41 B (K3 449 [] B) (K3 450 [] B) (K3 451 [] B)) (K3 446 [] B) (K3 447 [] B) (K3 448 [] B)) (K3 443 [] B) (K3 444 [] B) (K3 445 [] B)) (K3 440 [] B) (K3 441 [] B) (K3 442 [] B)) (K3 437 [] B) (K3 438 [] B) (K3 439 [] B)) (K3 434 [] B) (K3 435 [] B) (K3 436 [] B)) (K3 431 [] B) (K3 432 [] B) (K3 433 [] B)) (SF 0 (K3 430 [] B) (NP 0)) (AC 2 429 []) (NP 2)) (NP 1) (NP 1) (NP 1)) (NP 0) (NP 0) (NP 0) (NP 0)) (S7 7 (SP 11 (SP 13 (SP 17 (SP 19 (SP 23 (SP 29 (SP 31 (SP 37 (SP 41 B (K3 471 [] B) (K3 472 [] B) (K3 473 [] B)) (K3 468 [] B) (K3 469 [] B) (K3 470 [] B)) (K3 465 [] B) (K3 466 [] B) (K3 467 [] B)) (K3 462 [] B) (K3 463 [] B) (K3 464 [] B)) (K3 459 [] B) (K3 460 [] B) (K3 461 [] B)) (K3 456 [] B) (K3 457 [] B) (K3 458 [] B)) (K3 453 [] B) (K3 454 [] B) (K3 455 [] B)) (SF 0 (K3 452 [] B) (NP 0)) (NP 1) (NP 1)) (NP 1) (NP 1) (NP 1)) (NP 0) (NP 0) (NP 0) (NP 0)))
theorem ok_c3_3 : checkCert allSeeds allSurvs true 200 c3_3 [⟨3,3,false,.odd⟩] 5 = true := by decide +kernel
def c3_4 : Cert := (S7 5 (S7 7 (SP 11 B B (SP 13 B B (SP 17 B B (KV 1 697 [] B) (K5 698 [1] B)) (SP 17 B B (K5 701 [1] B) (K5 702 [1] B))) (SP 13 B B (SP 17 B B (K5 697 [1] B) (K5 698 [1] B)) (SP 17 B B (K5 701 [1] B) (K5 702 [1] B)))) (SP 11 (SP 13 (SP 17 B (K3 654 [] B) (K3 655 [] B) (K3 656 [] B)) (K3 651 [] B) (K3 652 [] B) (K3 653 [] B)) (K3 648 [] B) (K3 649 [] B) (K3 650 [] B)) (SP 11 (SP 13 (SP 17 B (K3 663 [] B) (K3 664 [] B) (K3 665 [] B)) (K3 660 [] B) (K3 661 [] B) (K3 662 [] B)) (K3 657 [] B) (K3 658 [] B) (K3 659 [] B)) (SP 11 (SP 13 (SP 17 (SP 19 B B (K3 675 [] B) (K3 676 [] B)) (K3 672 [] B) (K3 673 [] B) (K3 674 [] B)) (K3 669 [] B) (K3 670 [] B) (K3 671 [] B)) (K3 666 [] B) (K3 667 [] B) (K3 668 [] B)) (SP 11 (SP 13 (SP 17 (SP 19 B B (SP 23 B B (KV 2 689 [] B) (K5 686 [3] B)) (K3 687 [] B)) (K3 683 [] B) (SP 19 (SP 23 B (K5 684 [3] B) (KV 2 689 [] B) (K5 684 [3] B)) (K5 684 [3] B) (KV 2 686 [] B) (K5 684 [3] B)) (K3 685 [] B)) (K3 680 [] B) (SP 17 (SP 19 (SP 23 (SP 29 (SP 31 B (K5 681 [3] B) (KV 2 691 [] B) (K5 681 [3] B)) (K5 681 [3] B) (KV 2 690 [] B) (K5 681 [3] B)) (K5 681 [3] B) (KV 2 689 [] B) (K5 681 [3] B)) (K5 681 [3] B) (SF 0 (KV 1 699 [] B) (SF 0 (SF 2 (K5 711 [3] B) (SF 3 (K5 712 [3] B) (NP 2))) (SF 2 (K5 716 [3] (KR 1 717 [])) (NP 0)))) (K5 681 [3] (KR 1 700 []))) (K5 681 [3] (KR 1 696 [])) (NP 1) (NP 1)) (K3 682 [] B)) (K3 677 [] B) (SP 13 (SP 17 (SP 19 (SP 23 (SP 29 (SP 31 (SP 37 (SP 41 (SP 43 (SP 47 B (K5 678 [3] B) (KV 2 695 [] B) (K5 678 [3] B)) (K5 678 [3] B) (KV 2 694 [] B) (K5 678 [3] B)) (K5 678 [3] B) (KV 2 693 [] B) (K5 678 [3] B)) (K5 678 [3] B) (KV 2 692 [] B) (K5 678 [3] B)) (K5 678 [3] B) (KV 2 691 [] B) (K5 678 [3] B)) (K5 678 [3] B) (KV 2 690 [] B) (K5 678 [3] B)) (K5 678 [3] (KR 2 688 [])) (NP 1) (NP 1)) (NP 1) (NP 0) (NP 0)) (NP 0) (NP 0) (NP 0)) (NP 0) (NP 0) (NP 0)) (K3 679 [] B))) (S7 7 (SP 11 (SP 13 (SP 17 (SP 19 (SP 23 B (K3 541 [] B) (K3 542 [] B) (K3 543 [] B)) (K3 538 [] B) (K3 539 [] B) (K3 540 [] B)) (K3 535 [] B) (K3 536 [] B) (K3 537 [] B)) (K3 532 [] B) (K3 533 [] B) (K3 534 [] B)) (K3 529 [] B) (K3 530 [] B) (K3 531 [] B)) (NP 0) (NP 0) (NP 0) (NP 0)) (S7 7 (SP 11 (SP 13 (SP 17 (SP 19 (SP 23 (SP 29 (SP 31 (SP 37 B (K3 560 [] B) (SP 41 B (K5 561 [3] B) (KV 2 564 [] B) (K5 561 [3] B)) (K3 562 [] B)) (K3 557 [] B) (K3 558 [] B) (K3 559 [] B)) (K3 554 [] B) (SP 31 (SP 37 (SP 41 (SP 43 (SP 47 B (K5 555 [3] B) (KV 2 568 [] B) (K5 555 [3] B)) (K5 555 [3] B) (KV 2 566 [] B) (K5 555 [3] B)) (K5 555 [3] B) (KV 2 564 [] B) (K5 555 [3] B)) (K5 555 [3] B) (KV 2 561 [] B) (K5 555 [3] B)) (K5 555 [3] B) (K5 555 [3] B) (K5 555 [3] B)) (K3 556 [] B)) (K3 551 [] B) (SP 29 (SP 31 (SP 37 (SP 41 (SP 43 (SP 47 (SP 53 (SP 59 (SP 61 (SP 67 B (K5 552 [3] B) (KV 2 578 [] B) (K5 552 [3] B)) (K5 552 [3] B) (KV 2 576 [] B) (K5 552 [3] B)) (K5 552 [3] B) (KV 2 574 [] B) (K5 552 [3] B)) (K5 552 [3] B) (KV 2 571 [] B) (K5 552 [3] B)) (K5 552 [3] B) (KV 2 568 [] B) (K5 552 [3] B)) (K5 552 [3] B) (KV 2 566 [] B) (K5 552 [3] B)) (K5 552 [3] B) (KV 2 564 [] B) (K5 552 [3] B)) (K5 552 [3] B) (KV 2 561 [] B) (K5 552 [3] B)) (K5 552 [3] (KR 2 557 [])) (AC 2 558 []) (NP 3)) (AC 2 554 []) (NP 2) (NP 2)) (K3 553 [] B)) (K3 548 [] B) (SP 23 (SP 29 (SP 31 (SP 37 (SP 41 (SP 43 (SP 47 (SP 53 (SP 59 (SP 61 (SP 67 (SP 71 (SP 73 (SP 79 (SP 83 (SP 89 (SP 97 (SP 101 (SP 103 (SP 107 B (K5 549 [3] B) (KV 2 596 [] B) (K5 549 [3] B)) (K5 549 [3] B) (KV 2 595 [] B) (K5 549 [3] B)) (K5 549 [3] B) (KV 2 594 [] B) (K5 549 [3] B)) (K5 549 [3] B) (KV 2 593 [] B) (K5 549 [3] B)) (K5 549 [3] B) (KV 2 592 [] B) (K5 549 [3] B)) (K5 549 [3] B) (KV 2 590 [] B) (K5 549 [3] B)) (K5 549 [3] B) (KV 2 587 [] B) (K5 549 [3] B)) (K5 549 [3] B) (KV 2 584 [] B) (K5 549 [3] B)) (K5 549 [3] B) (KV 2 581 [] B) (K5 549 [3] B)) (K5 549 [3] B) (KV 2 578 [] B) (K5 549 [3] B)) (K5 549 [3] B) (KV 2 576 [] B) (K5 549 [3] B)) (K5 549 [3] B) (KV 2 574 [] B) (K5 549 [3] B)) (K5 549 [3] (KR 2 570 [])) (SF 0 (KV 2 571 [] B) (SF 0 (SF 2 (K5 707 [2,3] B) (NP 2)) (NP 0))) (K5 549 [3] (KR 2 572 []))) (K5 549 [3] (KR 2 567 [])) (SF 0 (KV 2 568 [] B) (NP 0)) (K5 549 [3] (KR 2 569 []))) (AC 2 565 []) (NP 3) (NP 3)) (AC 2 563 []) (NP 3) (NP 3)) (NP 2) (NP 2) (NP 2)) (NP 0) (NP 0) (NP 0)) (NP 0) (NP 0) (NP 0)) (NP 0) (NP 0) (NP 0)) (K3 550 [] B)) (K3 545 [] B) (SP 19 (SP 23 (SP 29 (SP 31 (SP 37 (SP 41 (SP 43 (SP 47 (SP 53 (SP 59 (SP 61 (SP 67 (SP 71 (SP 73 (SP 79 (SP 83 (SP 89 (SP 97 (SP 101 (SP 103 (SP 107 (SP 109 (SP 113 (SP 127 (SP 131 (SP 137 (SP 139 (SP 149 (SP 151 (SP 157 (SP 163 B (K5 546 [3] B) (KV 2 606 [] B) (K5 546 [3] B)) (K5 546 [3] B) (KV 2 605 [] B) (K5 546 [3] B)) (K5 546 [3] B) (KV 2 604 [] B) (K5 546 [3] B)) (K5 546 [3] B) (KV 2 603 [] B) (K5 546 [3] B)) (K5 546 [3] B) (KV 2 602 [] B) (K5 546 [3] B)) (K5 546 [3] B) (KV 2 601 [] B) (K5 546 [3] B)) (K5 546 [3] B) (KV 2 600 [] B) (K5 546 [3] B)) (K5 546 [3] B) (KV 2 599 [] B) (K5 546 [3] B)) (K5 546 [3] B) (KV 2 598 [] B) (K5 546 [3] B)) (K5 546 [3] B) (KV 2 597 [] B) (K5 546 [3] B)) (K5 546 [3] B) (KV 2 596 [] B) (K5 546 [3] B)) (K5 546 [3] B) (KV 2 595 [] B) (K5 546 [3] B)) (K5 546 [3] B) (KV 2 594 [] B) (K5 546 [3] B)) (K5 546 [3] B) (KV 2 593 [] B) (K5 546 [3] B)) (K5 546 [3] B) (KV 2 592 [] B) (K5 546 [3] B)) (K5 546 [3] (KR 2 589 [])) (SF 0 (KV 2 590 [] B) (SF 0 (KV 2 708 [] B) (SF 2 (KV 2 713 [] B) (NP 0)))) (K5 546 [3] (KR 2 591 []))) (K5 546 [3] (KR 2 586 [])) (SF 0 (KV 2 587 [] B) (AC 2 707 [2])) (K5 546 [3] (KR 2 588 []))) (K5 546 [3] (KR 2 583 [])) (SF 0 (KV 2 584 [] B) (NP 0)) (K5 546 [3] (KR 2 585 []))) (K5 546 [3] (KR 2 580 [])) (SF 0 (KV 2 581 [] B) (NP 0)) (K5 546 [3] (KR 2 582 []))) (K5 546 [3] (KR 2 577 [])) (SF 0 (KV 2 578 [] B) (NP 0)) (K5 546 [3] (KR 2 579 []))) (K5 546 [3] (KR 2 575 [])) (AC 2 576 []) (NP 3)) (AC 2 573 []) (NP 3) (NP 3)) (AC 2 570 []) (NP 3) (NP 3)) (NP 2) (NP 2) (NP 2)) (NP 2) (NP 2) (NP 2)) (NP 2) (NP 0) (NP 0)) (NP 0) (NP 0) (NP 0)) (NP 0) (NP 0) (NP 0)) (NP 0) (NP 0) (NP 0)) (NP 0) (NP 0) (NP 0)) (NP 0) (NP 0) (NP 0)) (K3 547 [] B)) (SF 0 (K3 544 [] B) (NP 0)) (AS 86) (NP 2)) (NP 0) (NP 0) (NP 0)) (NP 0) (NP 0) (NP 0) (NP 0)) (S7 7 (SP 11 (SP 13 (SP 17 (SP 19 (SP 23 (SP 29 (SP 31 (SP 37 (SP 41 B (K3 626 [] B) (K3 627 [] B) (K3 628 [] B)) (K3 623 [] B) (K3 624 [] B) (K3 625 [] B)) (K3 620 [] B) (K3 621 [] B) (K3 622 [] B)) (K3 617 [] B) (K3 618 [] B) (K3 619 [] B)) (K3 614 [] B) (K3 615 [] B) (K3 616 [] B)) (K3 611 [] B) (K3 612 [] B) (K3 613 [] B)) (K3 608 [] B) (K3 609 [] B) (K3 610 [] B)) (AC 2 607 []) (NP 0) (NP 0)) (NP 0) (NP 0) (NP 0)) (NP 0) (NP 0) (NP 0) (NP 0)) (S7 7 (SP 11 (SP 13 (SP 17 (SP 19 (SP 23 (SP 29 (SP 31 (SP 37 (SP 41 B (K3 642 [] B) (SP 43 (SP 47 B (K5 629 [2,3] B) (KV 2 629 [2] B) (K5 629 [2,3] B)) (K5 629 [2,3] B) (KV 2 629 [2] B) (K5 629 [2,3] B)) (K3 643 [] B)) (K3 640 [] B) (SP 41 (SP 43 (SP 47 B (K5 629 [2,3] B) (KV 2 629 [2] B) (K5 629 [2,3] B)) (K5 629 [2,3] B) (KV 2 629 [2] B) (K5 629 [2,3] B)) (K5 629 [2,3] B) (KV 2 629 [2] B) (K5 629 [2,3] B)) (K3 641 [] B)) (K3 638 [] B) (SP 37 (SP 41 (SP 43 (SP 47 (SP 53 (SP 59 B (K5 629 [2,3] B) (KV 2 629 [2] B) (K5 629 [2,3] B)) (K5 629 [2,3] B) (KV 2 629 [2] B) (K5 629 [2,3] B)) (K5 629 [2,3] B) (KV 2 629 [2] B) (K5 629 [2,3] B)) (K5 629 [2,3] B) (KV 2 629 [2] B) (K5 629 [2,3] B)) (K5 629 [2,3] B) (KV 2 629 [2] B) (K5 629 [2,3] B)) (K5 629 [2,3] B) (KV 2 629 [2] B) (K5 629 [2,3] B)) (K3 639 [] B)) (K3 636 [] B) (SP 31 (SP 37 (SP 41 (SP 43 (SP 47 (SP 53 (SP 59 (SP 61 B (K5 629 [2,3] B) (KV 2 629 [2] B) (K5 629 [2,3] B)) (K5 629 [2,3] B) (KV 2 629 [2] B) (K5 629 [2,3] B)) (K5 629 [2,3] B) (KV 2 629 [2] B) (K5 629 [2,3] B)) (K5 629 [2,3] B) (KV 2 629 [2] B) (K5 629 [2,3] B)) (K5 629 [2,3] B) (KV 2 629 [2] B) (K5 629 [2,3] B)) (K5 629 [2,3] B) (KV 2 629 [2] B) (K5 629 [2,3] B)) (K5 629 [2,3] B) (KV 2 629 [2] B) (K5 629 [2,3] B)) (K5 629 [2,3] (KR 2 629 [2])) (SF 0 (KV 2 629 [2] B) (NP 0)) (K5 629 [2,3] (KR 2 629 [2]))) (K3 637 [] B)) (K3 634 [] B) (SP 29 (SP 31 (SP 37 (SP 41 (SP 43 (SP 47 (SP 53 (SP 59 (SP 61 (SP 67 (SP 71 (SP 73 (SP 79 (SP 83 (SP 89 (SP 97 B (K5 629 [2,3] B) (KV 2 629 [2] B) (K5 629 [2,3] B)) (K5 629 [2,3] B) (KV 2 629 [2] B) (K5 629 [2,3] B)) (K5 629 [2,3] B) (KV 2 629 [2] B) (K5 629 [2,3] B)) (K5 629 [2,3] B) (KV 2 629 [2] B) (K5 629 [2,3] B)) (K5 629 [2,3] B) (KV 2 629 [2] B) (K5 629 [2,3] B)) (K5 629 [2,3] B) (KV 2 629 [2] B) (K5 629 [2,3] B)) (K5 629 [2,3] B) (KV 2 629 [2] B) (K5 629 [2,3] B)) (K5 629 [2,3] B) (KV 2 629 [2] B) (K5 629 [2,3] B)) (K5 629 [2,3] B) (KV 2 629 [2] B) (K5 629 [2,3] B)) (K5 629 [2,3] B) (KV 2 629 [2] B) (K5 629 [2,3] B)) (K5 629 [2,3] (KR 2 629 [2])) (SF 0 (KV 2 629 [2] B) (NP 3)) (K5 629 [2,3] (KR 2 629 [2]))) (K5 629 [2,3] (KR 2 629 [2])) (SF 0 (KV 2 629 [2] B) (NP 0)) (K5 629 [2,3] (KR 2 629 [2]))) (K5 629 [2,3] (KR 2 629 [2])) (AC 2 629 [2]) (NP 3)) (NP 1) (NP 1) (NP 1)) (NP 1) (NP 1) (NP 1)) (NP 0) (NP 0) (NP 0)) (K3 635 [] B)) (K3 632 [] B) (SP 23 (SP 29 (SP 31 (SP 37 (SP 41 (SP 43 (SP 47 (SP 53 (SP 59 (SP 61 (SP 67 (SP 71 (SP 73 (SP 79 (SP 83 (SP 89 (SP 97 (SP 101 (SP 103 (SP 107 (SP 109 (SP 113 (SP 127 (SP 131 (SP 137 (SP 139 (SP 149 (SP 151 (SP 157 (SP 163 (SP 167 (SP 173 (SP 179 (SP 181 B (K5 629 [2,3] B) (KV 2 629 [2] B) (K5 629 [2,3] B)) (K5 629 [2,3] B) (KV 2 629 [2] B) (K5 629 [2,3] B)) (K5 629 [2,3] B) (KV 2 629 [2] B) (K5 629 [2,3] B)) (K5 629 [2,3] B) (KV 2 629 [2] B) (K5 629 [2,3] B)) (K5 629 [2,3] B) (KV 2 629 [2] B) (K5 629 [2,3] B)) (K5 629 [2,3] B) (KV 2 629 [2] B) (K5 629 [2,3] B)) (K5 629 [2,3] B) (KV 2 629 [2] B) (K5 629 [2,3] B)) (K5 629 [2,3] B) (KV 2 629 [2] B) (K5 629 [2,3] B)) (K5 629 [2,3] B) (KV 2 629 [2] B) (K5 629 [2,3] B)) (K5 629 [2,3] B) (KV 2 629 [2] B) (K5 629 [2,3] B)) (K5 629 [2,3] B) (KV 2 629 [2] B) (K5 629 [2,3] B)) (K5 629 [2,3] B) (KV 2 629 [2] B) (K5 629 [2,3] B)) (K5 629 [2,3] B) (KV 2 629 [2] B) (K5 629 [2,3] B)) (K5 629 [2,3] B) (KV 2 629 [2] B) (K5 629 [2,3] B)) (K5 629 [2,3] B) (KV 2 629 [2] B) (K5 629 [2,3] B)) (K5 629 [2,3] B) (KV 2 629 [2] B) (K5 629 [2,3] B)) (K5 629 [2,3] B) (KV 2 629 [2] B) (K5 629 [2,3] B)) (K5 629 [2,3] B) (KV 2 644 [] B) (K5 629 [2,3] B)) (K5 629 [2,3] (KR 2 629 [2])) (SF 0 (KV 2 629 [2] B) (SF 0 (SF 1 (SF 2 (K5 709 [2,3] B) (NP 2)) (NP 1)) (NP 0))) (K5 629 [2,3] (KR 2 629 [2]))) (K5 629 [2,3] (KR 2 629 [2])) (SF 0 (KV 2 629 [2] B) (NP 3)) (K5 629 [2,3] (KR 2 629 [2]))) (K5 629 [2,3] (KR 2 629 [2])) (SF 0 (KV 2 629 [2] B) (NP 0)) (K5 629 [2,3] (KR 2 629 [2]))) (K5 629 [2,3] (KR 2 629 [2])) (SF 0 (KV 2 629 [2] B) (NP 0)) (K5 629 [2,3] (KR 2 629 [2]))) (K5 629 [2,3] (KR 2 629 [2])) (SF 0 (KV 2 629 [2] B) (NP 0)) (K5 629 [2,3] (KR 2 629 [2]))) (K5 629 [2,3] (KR 2 629 [2])) (SF 0 (SF 1 (SF 2 (K5 629 [2,3] B) (NP 2)) (NP 1)) (NP 0)) (K5 629 [2,3] (KR 2 629 [2]))) (AC 2 629 [2]) (NP 1) (NP 1)) (NP 1) (NP 1) (NP 1)) (NP 1) (NP 1) (NP 1)) (NP 1) (NP 1) (NP 1)) (NP 1) (NP 0) (NP 0)) (NP 0) (NP 0) (NP 0)) (NP 0) (NP 0) (NP 0)) (NP 0) (NP 0) (NP 0)) (NP 0) (NP 0) (NP 0)) (NP 0) (NP 0) (NP 0)) (K3 633 [] B)) (K3 630 [] B) (SP 19 (SP 23 (SP 29 (SP 31 (SP 37 (SP 41 (SP 43 (SP 47 (SP 53 (SP 59 (SP 61 (SP 67 (SP 71 (SP 73 (SP 79 (SP 83 (SP 89 (SP 97 (SP 101 (SP 103 (SP 107 (SP 109 (SP 113 (SP 127 (SP 131 (SP 137 (SP 139 (SP 149 (SP 151 (SP 157 (SP 163 (SP 167 (SP 173 (SP 179 (SP 181 (SP 191 (SP 193 (SP 197 (SP 199 (SP 211 (SP 223 (SP 227 (SP 229 (SP 233 (SP 239 (SP 241 (SP 251 (SP 257 (SP 263 (SP 269 (SP 271 (SP 277 (SP 281 (SP 283 (SP 293 (SP 307 (SP 311 (SP 313 (SP 317 (SP 331 (SP 337 (SP 347 (SP 349 (SP 353 (SP 359 (SP 367 (SP 373 (SP 379 (SP 383 (SP 389 (SP 397 (SP 401 (SP 409 (SP 419 (SP 421 (SP 431 (SP 433 (SP 439 (SP 443 (SP 449 (SP 457 (SP 461 (SP 463 (SP 467 (SP 479 (SP 487 (SP 491 (SP 499 (SP 503 B (K5 629 [2,3] B) (KV 2 629 [2] B) (K5 629 [2,3] B)) (K5 629 [2,3] B) (KV 2 629 [2] B) (K5 629 [2,3] B)) (K5 629 [2,3] B) (KV 2 629 [2] B) (K5 629 [2,3] B)) (K5 629 [2,3] B) (KV 2 629 [2] B) (K5 629 [2,3] B)) (K5 629 [2,3] B) (KV 2 629 [2] B) (K5 629 [2,3] B)) (K5 629 [2,3] B) (KV 2 629 [2] B) (K5 629 [2,3] B)) (K5 629 [2,3] B) (KV 2 629 [2] B) (K5 629 [2,3] B)) (K5 629 [2,3] B) (KV 2 629 [2] B) (K5 629 [2,3] B)) (K5 629 [2,3] B) (KV 2 629 [2] B) (K5 629 [2,3] B)) (K5 629 [2,3] B) (KV 2 629 [2] B) (K5 629 [2,3] B)) (K5 629 [2,3] B) (KV 2 629 [2] B) (K5 629 [2,3] B)) (K5 629 [2,3] B) (KV 2 629 [2] B) (K5 629 [2,3] B)) (K5 629 [2,3] B) (KV 2 629 [2] B) (K5 629 [2,3] B)) (K5 629 [2,3] B) (KV 2 629 [2] B) (K5 629 [2,3] B)) (K5 629 [2,3] B) (KV 2 629 [2] B) (K5 629 [2,3] B)) (K5 629 [2,3] B) (KV 2 629 [2] B) (K5 629 [2,3] B)) (K5 629 [2,3] B) (KV 2 629 [2] B) (K5 629 [2,3] B)) (K5 629 [2,3] B) (KV 2 629 [2] B) (K5 629 [2,3] B)) (K5 629 [2,3] B) (KV 2 629 [2] B) (K5 629 [2,3] B)) (K5 629 [2,3] B) (KV 2 629 [2] B) (K5 629 [2,3] B)) (K5 629 [2,3] B) (KV 2 629 [2] B) (K5 629 [2,3] B)) (K5 629 [2,3] B) (KV 2 629 [2] B) (K5 629 [2,3] B)) (K5 629 [2,3] B) (KV 2 629 [2] B) (K5 629 [2,3] B)) (K5 629 [2,3] B) (KV 2 629 [2] B) (K5 629 [2,3] B)) (K5 629 [2,3] B) (KV 2 629 [2] B) (K5 629 [2,3] B)) (K5 629 [2,3] B) (KV 2 629 [2] B) (K5 629 [2,3] B)) (K5 629 [2,3] B) (KV 2 629 [2] B) (K5 629 [2,3] B)) (K5 629 [2,3] B) (KV 2 629 [2] B) (K5 629 [2,3] B)) (K5 629 [2,3] B) (KV 2 629 [2] B) (K5 629 [2,3] B)) (K5 629 [2,3] B) (KV 2 629 [2] B) (K5 629 [2,3] B)) (K5 629 [2,3] B) (KV 2 629 [2] B) (K5 629 [2,3] B)) (K5 629 [2,3] B) (KV 2 629 [2] B) (K5 629 [2,3] B)) (K5 629 [2,3] B) (KV 2 629 [2] B) (K5 629 [2,3] B)) (K5 629 [2,3] B) (KV 2 629 [2] B) (K5 629 [2,3] B)) (K5 629 [2,3] B) (KV 2 629 [2] B) (K5 629 [2,3] B)) (K5 629 [2,3] B) (KV 2 629 [2] B) (K5 629 [2,3] B)) (K5 629 [2,3] B) (KV 2 629 [2] B) (K5 629 [2,3] B)) (K5 629 [2,3] B) (KV 2 629 [2] B) (K5 629 [2,3] B)) (K5 629 [2,3] B) (KV 2 629 [2] B) (K5 629 [2,3] B)) (K5 629 [2,3] B) (KV 2 629 [2] B) (K5 629 [2,3] B)) (K5 629 [2,3] B) (KV 2 647 [] B) (K5 629 [2,3] B)) (K5 629 [2,3] B) (KV 2 646 [] B) (K5 629 [2,3] B)) (K5 629 [2,3] (KR 2 629 [2])) (SF 0 B (SF 0 (KV 2 709 [2] B) (SF 1 (KV 2 714 [2] B) (SF 2 (KV 2 715 [2] B) (NP 2))))) (K5 629 [2,3] (KR 2 629 [2]))) (K5 629 [2,3] (KR 2 629 [2])) (SF 0 (KV 2 629 [2] B) (SF 0 (KV 2 709 [2] B) (SF 1 (KV 2 714 [2] B) (SF 2 (SF 0 (KV 2 715 [2] B) (NP 0)) (NP 0))))) (K5 629 [2,3] (KR 2 629 [2]))) (K5 629 [2,3] (KR 2 629 [2])) (SF 0 (KV 2 629 [2] B) (SF 0 (KV 2 709 [2] B) (SF 1 (KV 2 714 [2] B) (AC 2 715 [2])))) (K5 629 [2,3] (KR 2 629 [2]))) (K5 629 [2,3] (KR 2 629 [2])) (SF 0 (KV 2 629 [2] B) (SF 0 (KV 2 709 [2] B) (SF 1 (SF 2 (KV 2 714 [2] B) (NP 2)) (NP 0)))) (K5 629 [2,3] (KR 2 629 [2]))) (K5 629 [2,3] (KR 2 629 [2])) (SF 0 (KV 2 629 [2] B) (SF 0 (SF 1 (KV 2 709 [2] B) (SF 2 (KV 2 710 [2] B) (SF 1 (KV 2 710 [2] B) (NP 1)))) (SF 1 (SF 2 (KV 2 714 [2] B) (NP 2)) (NP 0)))) (K5 629 [2,3] (KR 2 629 [2]))) (K5 629 [2,3] (KR 2 629 [2])) (SF 0 (KV 2 629 [2] B) (SF 0 (SF 1 (KV 2 709 [2] B) (SF 2 (KV 2 710 [2] B) (NP 2))) (SF 1 (SF 2 (KV 2 714 [2] B) (NP 0)) (NP 0)))) (K5 629 [2,3] (KR 2 629 [2]))) (K5 629 [2,3] (KR 2 629 [2])) (SF 0 (KV 2 629 [2] B) (SF 0 (SF 1 (KV 2 709 [2] B) (SF 2 (KV 2 710 [2] B) (NP 1))) (AC 2 714 [2]))) (K5 629 [2,3] (KR 2 629 [2]))) (K5 629 [2,3] (KR 2 629 [2])) (SF 0 (KV 2 629 [2] B) (SF 0 (SF 1 (SF 2 (KV 2 709 [2] B) (NP 2)) (NP 1)) (NP 0))) (K5 629 [2,3] (KR 2 629 [2]))) (K5 629 [2,3] (KR 2 629 [2])) (SF 0 (KV 2 629 [2] B) (NP 3)) (K5 629 [2,3] (KR 2 629 [2]))) (K5 629 [2,3] (KR 2 629 [2])) (SF 0 (KV 2 629 [2] B) (NP 3)) (K5 629 [2,3] (KR 2 629 [2]))) (K5 629 [2,3] (KR 2 629 [2])) (SF 0 (KV 2 629 [2] B) (NP 3)) (K5 629 [2,3] (KR 2 629 [2]))) (K5 629 [2,3] (KR 2 629 [2])) (SF 0 (KV 2 629 [2] B) (NP 3)) (K5 629 [2,3] (KR 2 629 [2]))) (K5 629 [2,3] (KR 2 629 [2])) (SF 0 (KV 2 629 [2] B) (NP 3)) (K5 629 [2,3] (KR 2 629 [2]))) (K5 629 [2,3] (KR 2 629 [2])) (SF 0 (KV 2 629 [2] B) (NP 3)) (K5 629 [2,3] (KR 2 629 [2]))) (K5 629 [2,3] (KR 2 629 [2])) (SF 0 (KV 2 629 [2] B) (NP 3)) (K5 629 [2,3] (KR 2 629 [2]))) (K5 629 [2,3] (KR 2 629 [2])) (SF 0 (KV 2 629 [2] B) (NP 0)) (K5 629 [2,3] (KR 2 629 [2]))) (K5 629 [2,3] (KR 2 629 [2])) (SF 0 (KV 2 629 [2] B) (NP 0)) (K5 629 [2,3] (KR 2 629 [2]))) (K5 629 [2,3] (KR 2 629 [2])) (SF 0 (KV 2 629 [2] B) (NP 0)) (K5 629 [2,3] (KR 2 629 [2]))) (K5 629 [2,3] (KR 2 629 [2])) (SF 0 (KV 2 629 [2] B) (NP 0)) (K5 629 [2,3] (KR 2 629 [2]))) (K5 629 [2,3] (KR 2 629 [2])) (SF 0 (KV 2 629 [2] B) (NP 0)) (K5 629 [2,3] (KR 2 629 [2]))) (K5 629 [2,3] (KR 2 629 [2])) (SF 0 (KV 2 629 [2] B) (NP 0)) (K5 629 [2,3] (KR 2 629 [2]))) (K5 629 [2,3] (KR 2 629 [2])) (SF 0 (KV 2 629 [2] B) (NP 0)) (K5 629 [2,3] (KR 2 629 [2]))) (K5 629 [2,3] (KR 2 629 [2])) (SF 0 (KV 2 629 [2] B) (NP 0)) (K5 629 [2,3] (KR 2 629 [2]))) (K5 629 [2,3] (KR 2 629 [2])) (SF 0 (KV 2 645 [] B) (NP 0)) (K5 629 [2,3] (KR 2 629 [2]))) (AC 2 629 [2]) (NP 3) (NP 3)) (AC 2 629 [2]) (NP 3) (NP 3)) (AC 2 629 [2]) (NP 3) (NP 3)) (AC 2 629 [2]) (NP 3) (NP 3)) (NP 1) (NP 1) (NP 1)) (NP 1) (NP 1) (NP 1)) (NP 1) (NP 1) (NP 1)) (NP 1) (NP 1) (NP 1)) (NP 1) (NP 1) (NP 1)) (NP 1) (NP 1) (NP 1)) (NP 1) (NP 1) (NP 1)) (NP 1) (NP 1) (NP 1)) (NP 1) (NP 1) (NP 1)) (NP 1) (NP 0) (NP 0)) (NP 0) (NP 0) (NP 0)) (NP 0) (NP 0) (NP 0)) (NP 0) (NP 0) (NP 0)) (NP 0) (NP 0) (NP 0)) (NP 0) (NP 0) (NP 0)) (NP 0) (NP 0) (NP 0)) (NP 0) (NP 0) (NP 0)) (NP 0) (NP 0) (NP 0)) (NP 0) (NP 0) (NP 0)) (K3 631 [] B)) (NP 1) (NP 0) (NP 0)) (NP 0) (NP 0) (NP 0)) (NP 0) (NP 0) (NP 0) (NP 0)))
theorem ok_c3_4 : checkCert allSeeds allSurvs true 200 c3_4 [⟨3,4,false,.even⟩] 5 = true := by decide +kernel

lemma h2_proved : OMA.R_Erdos470_erdos_470_variants_odd_weird_prime_div_R1_H2_R1.H2 :=
  prove_H2_from_certs allSeeds allSurvs c3_1 c3_2 c3_3 c3_4 allSeeds_valid ok_c3_1 ok_c3_2 ok_c3_3 ok_c3_4

end Erdos470H2Proof

theorem OMA.solution : OMA.R_Erdos470_erdos_470_variants_odd_weird_prime_div_R1_H2_R1.H2 :=
  Erdos470H2Proof.h2_proved
