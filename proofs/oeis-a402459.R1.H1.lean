import OMAReductions.R_oeis_a402459_R1
import Mathlib

namespace TernaryFactorPrimes

private def modPowAux (m a : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 1 % m
  | fuel + 1, e =>
    let r := modPowAux m a fuel (e / 2)
    (a ^ (e % 2) * r * r) % m

private theorem modPowAux_eq (m a fuel e : ℕ) (h : e < 2 ^ fuel) :
    modPowAux m a fuel e = a ^ e % m := by
  induction fuel generalizing e with
  | zero =>
    have he : e = 0 := by simpa using h
    simp [he, modPowAux]
  | succ fuel ih =>
    have next : e / 2 < 2 ^ fuel := by
      rw [pow_succ] at h
      omega
    have same : modPowAux m a fuel (e / 2) ≡ a ^ (e / 2) [MOD m] := by
      rw [ih _ next]
      simp [Nat.ModEq]
    have eq := ((Nat.ModEq.refl (a ^ (e % 2))).mul same).mul same
    have decomp : e % 2 + e / 2 + e / 2 = e := by omega
    simpa only [modPowAux, Nat.ModEq, ← pow_add, decomp] using eq

def modPow (m a e : ℕ) : ℕ := modPowAux m a (e.log2 + 1) e

theorem modPow_eq (m a e : ℕ) : modPow m a e = a ^ e % m := by
  by_cases zero : e = 0
  · simp [modPow, zero, modPowAux]
  exact modPowAux_eq m a _ e ((Nat.log2_lt zero).mp (Nat.lt_succ_self _))


structure Row where
  value : ℕ
  generator : ℕ
  factors : List (ℕ × ℕ)
deriving Inhabited

def valid (rows : ℕ → Row) (i : ℕ) : Prop :=
  let r := rows i
  r.value = 2 ∨
    2 < r.value ∧
    r.factors.all (fun f => decide (f.1 < i)) = true ∧
    (r.factors.map (fun f => (rows f.1).value^f.2)).prod = r.value-1 ∧
    modPow r.value r.generator (r.value-1) = 1 ∧
    r.factors.all (fun f => modPow r.value r.generator ((r.value-1)/(rows f.1).value) != 1) = true

private theorem divides_some {D : Type*} (p : ℕ) (hp : p.Prime)
    (ls : List D) (f : D → ℕ) (hd : p ∣ (ls.map f).prod) :
    ∃ a ∈ ls, p ∣ f a := by
  induction ls with
  | nil =>
      simp only [List.map_nil, List.prod_nil] at hd
      exact (hp.not_dvd_one hd).elim
  | cons a lst ih =>
      rw [List.map_cons, List.prod_cons] at hd
      rcases hp.dvd_mul.mp hd with h | h
      · exact ⟨a,List.mem_cons_self,h⟩
      · obtain ⟨b,hb,hd⟩ := ih h
        exact ⟨b,List.mem_cons_of_mem _ hb,hd⟩

theorem valid_prime (rows : ℕ → Row) (i : ℕ) (h : valid rows i)
    (prev : ∀ j < i, (rows j).value.Prime) : (rows i).value.Prime := by
  let r := rows i
  rcases h with h | ⟨hn,horder,hprod,hexp,hneq⟩
  · have h' : (rows i).value = 2 := h
    simpa only [h'] using Nat.prime_two
  · change r.value.Prime
    have hrn : 2 < r.value := hn
    have hone : 1 < r.value := by omega
    have hcast (e : ℕ) (hE : (r.generator : ZMod r.value)^e = 1) :
        modPow r.value r.generator e = 1 := by
      have ht := congrArg ZMod.val hE
      rw [← Nat.cast_pow, ZMod.val_natCast, ZMod.val_one_eq_one_mod, ← modPow_eq,
        Nat.mod_eq_of_lt hone] at ht
      exact ht
    apply lucas_primality r.value (r.generator : ZMod r.value)
    · have hp : modPow r.value r.generator (r.value-1) = 1 := hexp
      rw [← (Nat.cast_one : ((1 : ℕ) : ZMod r.value) = 1), ← Nat.cast_pow,
        ZMod.natCast_eq_natCast_iff', ← modPow_eq, hp, Nat.mod_eq_of_lt hone]
    · intro q hq hdiv heq
      rw [← hprod] at hdiv
      obtain ⟨f,hf,hfd⟩ := divides_some q hq r.factors (fun f => (rows f.1).value^f.2) hdiv
      have hprev : f.1 < i := by simpa using (List.all_eq_true.mp horder f hf)
      have hqeq : q = (rows f.1).value :=
        (Nat.prime_dvd_prime_iff_eq hq (prev f.1 hprev)).mp (hq.dvd_of_dvd_pow hfd)
      have hbad : modPow r.value r.generator ((r.value-1)/(rows f.1).value) ≠ 1 := by
        simpa using (List.all_eq_true.mp hneq f hf)
      apply hbad
      exact hcast _ (by simpa only [hqeq] using heq)

theorem every_prime (rows : ℕ → Row) (n : ℕ)
    (h : ∀ i < n, valid rows i) (i : ℕ) (hi : i<n) : (rows i).value.Prime := by
  induction i using Nat.strong_induction_on with
  | h i ih =>
      exact valid_prime rows i (h i hi) (fun j hj => ih j hj (hj.trans hi))

instance validDecidable (rows : ℕ → Row) (i : ℕ) : Decidable (valid rows i) := by
  unfold valid
  infer_instance

end TernaryFactorPrimes

namespace TernaryFactorPairs

def upperTail (r a : ℕ) : List ℕ → List ℕ
  | [] => []
  | b :: bs => if r ≤ 4 * (a * b) ^ 2 then upperTail r a bs else b :: bs

theorem upperTail_sublist (r a : ℕ) (bs : List ℕ) : List.Sublist (upperTail r a bs) bs := by
  induction bs with
  | nil => exact List.Sublist.slnil
  | cons b bs ih =>
    by_cases h : r ≤ 4 * (a * b) ^ 2
    · simp only [upperTail, if_pos h]
      exact ih.cons b
    · simp only [upperTail, if_neg h]
      exact List.Sublist.refl _

theorem mem_upperTail {r a a' b : ℕ} (h : a ≤ a') (hb : 4 * (a' * b) ^ 2 < r)
    {bs : List ℕ} (hm : b ∈ bs) : b ∈ upperTail r a bs := by
  induction bs with
  | nil => simp at hm
  | cons c cs ih =>
    by_cases hcut : r ≤ 4 * (a * c) ^ 2
    · rw [upperTail, if_pos hcut]
      rcases List.mem_cons.mp hm with rfl | hm
      · have hsq : (a * b) ^ 2 ≤ (a' * b) ^ 2 :=
          Nat.pow_le_pow_left (Nat.mul_le_mul_right b h) 2
        omega
      · exact ih hm
    · rw [upperTail, if_neg hcut]
      exact hm

def lowerScan (r a : ℕ) (check : ℕ → Bool) : List ℕ → Bool
  | [] => true
  | b :: bs =>
    if 6 * (a * b) ^ 2 ≤ r then true
    else check (a * b) && lowerScan r a check bs

theorem lowerScan_sound {r a b : ℕ} {check : ℕ → Bool} {bs : List ℕ}
    (hs : bs.Pairwise (· ≥ ·)) (hb : r < 6 * (a * b) ^ 2)
    (hm : b ∈ bs) (hc : lowerScan r a check bs = true) : check (a * b) = true := by
  induction bs with
  | nil => simp at hm
  | cons c cs ih =>
    obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hs
    have hbc : b ≤ c := by
      rcases List.mem_cons.mp hm with rfl | hm
      · exact le_rfl
      · exact hhead b hm
    have hsq : (a * b) ^ 2 ≤ (a * c) ^ 2 :=
      Nat.pow_le_pow_left (Nat.mul_le_mul_left a hbc) 2
    rw [lowerScan, if_neg (show ¬ 6 * (a * c) ^ 2 ≤ r by omega), Bool.and_eq_true] at hc
    rcases List.mem_cons.mp hm with rfl | hm
    · exact hc.1
    · exact ih htail hm hc.2

def cover (r : ℕ) (check : ℕ → Bool) : List ℕ → List ℕ → Bool
  | [], _ => true
  | a :: as, bs =>
    let tail := upperTail r a bs
    lowerScan r a check tail && cover r check as tail

theorem cover_sound {r a b : ℕ} {check : ℕ → Bool} {as bs : List ℕ}
    (ha : as.Pairwise (· ≤ ·)) (hb : bs.Pairwise (· ≥ ·))
    (hma : a ∈ as) (hmb : b ∈ bs)
    (hu : 4 * (a * b) ^ 2 < r) (hl : r < 6 * (a * b) ^ 2)
    (hc : cover r check as bs = true) : check (a * b) = true := by
  induction as generalizing bs with
  | nil => simp at hma
  | cons c cs ih =>
    obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp ha
    have sorted : (upperTail r c bs).Pairwise (· ≥ ·) := hb.sublist (upperTail_sublist r c bs)
    rw [cover, Bool.and_eq_true] at hc
    rcases List.mem_cons.mp hma with rfl | hm
    · exact lowerScan_sound sorted hl (mem_upperTail le_rfl hu hmb) hc.1
    · exact ih htail sorted hm (mem_upperTail (hhead a hm) hu hmb) hc.2

def factorProduct (ps : List (ℕ × ℕ)) : ℕ := (ps.map fun (p,k) => p ^ k).prod

def mergeFuel (le : ℕ → ℕ → Bool) : ℕ → List ℕ → List ℕ → List ℕ
  | 0, xs, ys => xs ++ ys
  | _+1, [], ys => ys
  | _+1, xs, [] => xs
  | n+1, x::xs, y::ys =>
    if le x y then x :: mergeFuel le n xs (y::ys)
    else y :: mergeFuel le n (x::xs) ys

theorem mergeFuel_eq (le : ℕ → ℕ → Bool) (fuel : ℕ) (xs ys : List ℕ)
    (h : xs.length+ys.length ≤ fuel) : mergeFuel le fuel xs ys = List.merge xs ys le := by
  induction fuel generalizing xs ys with
  | zero =>
    have hx : xs = [] := List.length_eq_zero_iff.mp (by omega)
    have hy : ys = [] := List.length_eq_zero_iff.mp (by omega)
    subst xs ys
    simp [mergeFuel]
  | succ fuel ih =>
    cases xs with
    | nil => cases ys <;> simp [mergeFuel]
    | cons x xs =>
      cases ys with
      | nil => simp [mergeFuel]
      | cons y ys =>
        simp only [List.length_cons] at h
        by_cases hb : le x y = true
        · simp only [mergeFuel, List.merge, hb, if_true]
          rw [ih xs (y::ys) (by simp only [List.length_cons]; omega)]
        · simp only [mergeFuel, List.merge, hb, Bool.false_eq_true, if_false]
          rw [ih (x::xs) ys (by simp only [List.length_cons]; omega)]

def mergeFast (le : ℕ → ℕ → Bool) (xs ys : List ℕ) : List ℕ :=
  mergeFuel le (xs.length+ys.length) xs ys

theorem mergeFast_eq (le : ℕ → ℕ → Bool) (xs ys : List ℕ) :
    mergeFast le xs ys = List.merge xs ys le := mergeFuel_eq le _ xs ys le_rfl

def mergeAll (le : ℕ → ℕ → Bool) : List (List ℕ) → List ℕ
  | [] => []
  | l :: ls => mergeFast le l (mergeAll le ls)

theorem mem_mergeAll {le : ℕ → ℕ → Bool} {ls : List (List ℕ)} {l : List ℕ}
    {d : ℕ} (hl : l ∈ ls) (hd : d ∈ l) : d ∈ mergeAll le ls := by
  induction ls with
  | nil => simp at hl
  | cons a as ih =>
    rw [mergeAll, mergeFast_eq, List.mem_merge]
    rcases List.mem_cons.mp hl with rfl | ht
    · exact Or.inl hd
    · exact Or.inr (ih ht)

theorem mergeAll_sorted {le : ℕ → ℕ → Bool}
    (trans : ∀ a b c, le a b → le b c → le a c)
    (total : ∀ a b, le a b || le b a)
    {ls : List (List ℕ)} (h : ∀ l ∈ ls, l.Pairwise (fun a b => le a b = true)) :
    (mergeAll le ls).Pairwise (fun a b => le a b = true) := by
  induction ls with
  | nil => simp [mergeAll]
  | cons l ls ih =>
    rw [mergeAll, mergeFast_eq]
    exact List.pairwise_merge trans total _ _ (h l (by simp))
      (ih (fun row hr => h row (List.mem_cons_of_mem _ hr)))

def orderedDivisors (le : ℕ → ℕ → Bool) : List (ℕ × ℕ) → List ℕ
  | [] => [1]
  | (p,k) :: ps =>
    let ds := orderedDivisors le ps
    mergeAll le ((List.range (k+1)).map fun i => ds.map fun d => p^i*d)

theorem mem_divisors {le : ℕ → ℕ → Bool} {ps : List (ℕ × ℕ)} (hp : ∀ x ∈ ps, x.1.Prime) {d : ℕ}
    (hd : d ∣ factorProduct ps) : d ∈ orderedDivisors le ps := by
  induction ps generalizing d with
  | nil =>
    have h : d = 1 := Nat.dvd_one.mp hd
    simp [h, orderedDivisors]
  | cons term ps ih =>
    obtain ⟨p,k⟩ := term
    change d ∣ p^k*factorProduct ps at hd
    obtain ⟨a,b,ha,hb,rfl⟩ := exists_dvd_and_dvd_of_dvd_mul hd
    have prime : p.Prime := hp (p,k) (by simp)
    obtain ⟨i,hi,rfl⟩ := (Nat.dvd_prime_pow prime).mp ha
    have member := ih (fun x hx => hp x (List.mem_cons_of_mem _ hx)) hb
    rw [orderedDivisors]
    refine mem_mergeAll (l := (orderedDivisors le ps).map fun d => p^i*d) ?_ ?_
    · exact List.mem_map.mpr ⟨i, List.mem_range.mpr (by omega), rfl⟩
    · exact List.mem_map.mpr ⟨b, member, rfl⟩

theorem divisors_sorted {le : ℕ → ℕ → Bool}
    (trans : ∀ a b c, le a b → le b c → le a c)
    (total : ∀ a b, le a b || le b a)
    (scale : ∀ k a b, le a b → le (k*a) (k*b)) (ps : List (ℕ × ℕ)) :
    (orderedDivisors le ps).Pairwise (fun a b => le a b = true) := by
  induction ps with
  | nil => simp [orderedDivisors]
  | cons term ps ih =>
    obtain ⟨p,k⟩ := term
    rw [orderedDivisors]
    apply mergeAll_sorted trans total
    intro l hl
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hl
    exact List.pairwise_map.mpr (ih.imp (fun {a b} hab => scale (p^i) a b hab))

def ascending (ps : List (ℕ × ℕ)) : List ℕ := orderedDivisors (fun a b => decide (a ≤ b)) ps

def descending (ps : List (ℕ × ℕ)) : List ℕ := orderedDivisors (fun a b => decide (b ≤ a)) ps

def candidates (r : ℕ) (check : ℕ → Bool) (ps qs : List (ℕ × ℕ)) : Bool :=
  cover r check (ascending ps) (descending qs)

theorem candidates_sound {r d : ℕ} {check : ℕ → Bool} {ps qs : List (ℕ × ℕ)}
    (hp : ∀ x ∈ ps, x.1.Prime) (hq : ∀ x ∈ qs, x.1.Prime)
    (hr : factorProduct ps * factorProduct qs = r)
    (hd : d ∣ r) (hu : 4*d^2 < r) (hl : r < 6*d^2)
    (hc : candidates r check ps qs = true) : check d = true := by
  rw [← hr] at hd
  obtain ⟨a,b,ha,hb,rfl⟩ := exists_dvd_and_dvd_of_dvd_mul hd
  have ma : a ∈ ascending ps := mem_divisors hp ha
  have mb : b ∈ descending qs := mem_divisors hq hb
  have sa : (ascending ps).Pairwise (· ≤ ·) := by
    simpa only [decide_eq_true_eq, ascending] using
      divisors_sorted (le := fun a b => decide (a ≤ b))
        (by intro a b c; simpa only [decide_eq_true_eq] using (@Nat.le_trans a b c))
        (by intro a b; simp only [Bool.or_eq_true, decide_eq_true_eq]; exact Nat.le_total a b)
        (by intro k a b; simpa only [decide_eq_true_eq] using (show a ≤ b → k*a ≤ k*b from Nat.mul_le_mul_left k)) ps
  have sb : (descending qs).Pairwise (· ≥ ·) := by
    simpa only [decide_eq_true_eq, descending] using
      divisors_sorted (le := fun a b => decide (b ≤ a))
        (by
          intro a b c
          simp only [decide_eq_true_eq]
          exact fun h₁ h₂ => Nat.le_trans h₂ h₁)
        (by intro a b; simp only [Bool.or_eq_true, decide_eq_true_eq]; exact Nat.le_total b a)
        (by intro k a b; simpa only [decide_eq_true_eq] using (show b ≤ a → k*b ≤ k*a from Nat.mul_le_mul_left k)) qs
  exact cover_sound sa sb ma mb hu hl hc

def containsTwo : ℕ → ℕ → Bool
  | 0, _ => false
  | f+1, n => (n%3 == 2) || containsTwo f (n/3)

theorem containsTwo_sound {fuel n : ℕ} (h : containsTwo fuel n = true) :
    2 ∈ Nat.digits 3 n := by
  induction fuel generalizing n with
  | zero => exact Bool.noConfusion h
  | succ f ih =>
    by_cases hn : n = 0
    · subst n
      simp [containsTwo] at h
      exact ih h
    rw [Nat.digits_eq_cons_digits_div (by decide) hn]
    simp only [containsTwo, Bool.or_eq_true, beq_iff_eq] at h
    rcases h with h | h
    · rw [h]
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih h)

def excludes (r d : ℕ) : Bool :=
  let e := r/d
  let twice := e-d
  (twice%2 == 1) || containsTwo 30 ((twice/2)^2)

theorem excludes_sound {r d e x : ℕ} (hd : 0 < d)
    (hp : d*e=r) (he : e=d+2*x) (h : excludes r d = true) :
    2 ∈ Nat.digits 3 (x*x) := by
  have hdiv : r/d=e := Nat.div_eq_of_eq_mul_left hd (by simpa [Nat.mul_comm] using hp.symm)
  simp only [excludes, hdiv, he, Nat.add_sub_cancel_left, Nat.mul_mod_right] at h
  have hx : 2*x/2 = x := by omega
  rw [hx, pow_two] at h
  exact containsTwo_sound h

end TernaryFactorPairs

namespace TernaryFactorPairs

open TernaryFactorPrimes


private def row0 (i : ℕ) : Row :=
  (bif Nat.ble i 11 then (bif Nat.ble i 5 then (bif Nat.ble i 2 then (bif Nat.ble i 1 then (bif Nat.ble i 0 then ⟨2,0,[]⟩ else ⟨3,2,[(0,1)]⟩) else ⟨5,2,[(0,2)]⟩) else (bif Nat.ble i 4 then (bif Nat.ble i 3 then ⟨7,3,[(0,1),(1,1)]⟩ else ⟨11,2,[(0,1),(2,1)]⟩) else ⟨13,2,[(0,2),(1,1)]⟩)) else (bif Nat.ble i 8 then (bif Nat.ble i 7 then (bif Nat.ble i 6 then ⟨17,3,[(0,4)]⟩ else ⟨19,2,[(0,1),(1,2)]⟩) else ⟨23,5,[(0,1),(4,1)]⟩) else (bif Nat.ble i 10 then (bif Nat.ble i 9 then ⟨29,2,[(0,2),(3,1)]⟩ else ⟨31,3,[(0,1),(1,1),(2,1)]⟩) else ⟨37,2,[(0,2),(1,2)]⟩))) else (bif Nat.ble i 17 then (bif Nat.ble i 14 then (bif Nat.ble i 13 then (bif Nat.ble i 12 then ⟨41,6,[(0,3),(2,1)]⟩ else ⟨43,3,[(0,1),(1,1),(3,1)]⟩) else ⟨47,5,[(0,1),(8,1)]⟩) else (bif Nat.ble i 16 then (bif Nat.ble i 15 then ⟨53,2,[(0,2),(5,1)]⟩ else ⟨59,2,[(0,1),(9,1)]⟩) else ⟨61,2,[(0,2),(1,1),(2,1)]⟩)) else (bif Nat.ble i 20 then (bif Nat.ble i 19 then (bif Nat.ble i 18 then ⟨67,2,[(0,1),(1,1),(4,1)]⟩ else ⟨71,7,[(0,1),(2,1),(3,1)]⟩) else ⟨73,5,[(0,3),(1,2)]⟩) else (bif Nat.ble i 22 then (bif Nat.ble i 21 then ⟨79,3,[(0,1),(1,1),(5,1)]⟩ else ⟨83,2,[(0,1),(12,1)]⟩) else ⟨89,3,[(0,3),(4,1)]⟩))))

private def row1 (i : ℕ) : Row :=
  (bif Nat.ble i 35 then (bif Nat.ble i 29 then (bif Nat.ble i 26 then (bif Nat.ble i 25 then (bif Nat.ble i 24 then ⟨97,5,[(0,5),(1,1)]⟩ else ⟨101,2,[(0,2),(2,2)]⟩) else ⟨103,5,[(0,1),(1,1),(6,1)]⟩) else (bif Nat.ble i 28 then (bif Nat.ble i 27 then ⟨107,2,[(0,1),(15,1)]⟩ else ⟨109,6,[(0,2),(1,3)]⟩) else ⟨113,3,[(0,4),(3,1)]⟩)) else (bif Nat.ble i 32 then (bif Nat.ble i 31 then (bif Nat.ble i 30 then ⟨127,3,[(0,1),(1,2),(3,1)]⟩ else ⟨131,2,[(0,1),(2,1),(5,1)]⟩) else ⟨137,3,[(0,3),(6,1)]⟩) else (bif Nat.ble i 34 then (bif Nat.ble i 33 then ⟨139,2,[(0,1),(1,1),(8,1)]⟩ else ⟨149,2,[(0,2),(11,1)]⟩) else ⟨151,6,[(0,1),(1,1),(2,2)]⟩))) else (bif Nat.ble i 41 then (bif Nat.ble i 38 then (bif Nat.ble i 37 then (bif Nat.ble i 36 then ⟨157,5,[(0,2),(1,1),(5,1)]⟩ else ⟨163,2,[(0,1),(1,4)]⟩) else ⟨167,5,[(0,1),(22,1)]⟩) else (bif Nat.ble i 40 then (bif Nat.ble i 39 then ⟨173,2,[(0,2),(13,1)]⟩ else ⟨179,2,[(0,1),(23,1)]⟩) else ⟨181,2,[(0,2),(1,2),(2,1)]⟩)) else (bif Nat.ble i 44 then (bif Nat.ble i 43 then (bif Nat.ble i 42 then ⟨191,19,[(0,1),(2,1),(7,1)]⟩ else ⟨193,5,[(0,6),(1,1)]⟩) else ⟨197,2,[(0,2),(3,2)]⟩) else (bif Nat.ble i 46 then (bif Nat.ble i 45 then ⟨199,3,[(0,1),(1,2),(4,1)]⟩ else ⟨211,2,[(0,1),(1,1),(2,1),(3,1)]⟩) else ⟨223,3,[(0,1),(1,1),(11,1)]⟩))))

private def row2 (i : ℕ) : Row :=
  (bif Nat.ble i 59 then (bif Nat.ble i 53 then (bif Nat.ble i 50 then (bif Nat.ble i 49 then (bif Nat.ble i 48 then ⟨227,2,[(0,1),(29,1)]⟩ else ⟨229,6,[(0,2),(1,1),(7,1)]⟩) else ⟨239,7,[(0,1),(3,1),(6,1)]⟩) else (bif Nat.ble i 52 then (bif Nat.ble i 51 then ⟨241,7,[(0,4),(1,1),(2,1)]⟩ else ⟨251,6,[(0,1),(2,3)]⟩) else ⟨257,3,[(0,8)]⟩)) else (bif Nat.ble i 56 then (bif Nat.ble i 55 then (bif Nat.ble i 54 then ⟨263,5,[(0,1),(31,1)]⟩ else ⟨269,2,[(0,2),(18,1)]⟩) else ⟨271,6,[(0,1),(1,3),(2,1)]⟩) else (bif Nat.ble i 58 then (bif Nat.ble i 57 then ⟨277,5,[(0,2),(1,1),(8,1)]⟩ else ⟨281,3,[(0,3),(2,1),(3,1)]⟩) else ⟨283,3,[(0,1),(1,1),(14,1)]⟩))) else (bif Nat.ble i 65 then (bif Nat.ble i 62 then (bif Nat.ble i 61 then (bif Nat.ble i 60 then ⟨293,2,[(0,2),(20,1)]⟩ else ⟨307,5,[(0,1),(1,2),(6,1)]⟩) else ⟨311,17,[(0,1),(2,1),(10,1)]⟩) else (bif Nat.ble i 64 then (bif Nat.ble i 63 then ⟨313,10,[(0,3),(1,1),(5,1)]⟩ else ⟨317,2,[(0,2),(21,1)]⟩) else ⟨347,2,[(0,1),(39,1)]⟩)) else (bif Nat.ble i 68 then (bif Nat.ble i 67 then (bif Nat.ble i 66 then ⟨349,2,[(0,2),(1,1),(9,1)]⟩ else ⟨359,7,[(0,1),(40,1)]⟩) else ⟨367,6,[(0,1),(1,1),(17,1)]⟩) else (bif Nat.ble i 70 then (bif Nat.ble i 69 then ⟨373,2,[(0,2),(1,1),(10,1)]⟩ else ⟨383,5,[(0,1),(42,1)]⟩) else ⟨389,2,[(0,2),(24,1)]⟩))))

private def row3 (i : ℕ) : Row :=
  (bif Nat.ble i 83 then (bif Nat.ble i 77 then (bif Nat.ble i 74 then (bif Nat.ble i 73 then (bif Nat.ble i 72 then ⟨401,3,[(0,4),(2,2)]⟩ else ⟨409,21,[(0,3),(1,1),(6,1)]⟩) else ⟨419,2,[(0,1),(4,1),(7,1)]⟩) else (bif Nat.ble i 76 then (bif Nat.ble i 75 then ⟨421,2,[(0,2),(1,1),(2,1),(3,1)]⟩ else ⟨431,7,[(0,1),(2,1),(13,1)]⟩) else ⟨433,5,[(0,4),(1,3)]⟩)) else (bif Nat.ble i 80 then (bif Nat.ble i 79 then (bif Nat.ble i 78 then ⟨439,15,[(0,1),(1,1),(20,1)]⟩ else ⟨443,2,[(0,1),(5,1),(6,1)]⟩) else ⟨461,2,[(0,2),(2,1),(8,1)]⟩) else (bif Nat.ble i 82 then (bif Nat.ble i 81 then ⟨463,3,[(0,1),(1,1),(3,1),(4,1)]⟩ else ⟨479,13,[(0,1),(50,1)]⟩) else ⟨487,3,[(0,1),(1,5)]⟩))) else (bif Nat.ble i 89 then (bif Nat.ble i 86 then (bif Nat.ble i 85 then (bif Nat.ble i 84 then ⟨491,2,[(0,1),(2,1),(3,2)]⟩ else ⟨499,7,[(0,1),(1,1),(22,1)]⟩) else ⟨503,5,[(0,1),(52,1)]⟩) else (bif Nat.ble i 88 then (bif Nat.ble i 87 then ⟨509,2,[(0,2),(30,1)]⟩ else ⟨521,3,[(0,3),(2,1),(5,1)]⟩) else ⟨523,2,[(0,1),(1,2),(9,1)]⟩)) else (bif Nat.ble i 92 then (bif Nat.ble i 91 then (bif Nat.ble i 90 then ⟨547,2,[(0,1),(1,1),(3,1),(5,1)]⟩ else ⟨557,2,[(0,2),(33,1)]⟩) else ⟨563,2,[(0,1),(58,1)]⟩) else (bif Nat.ble i 94 then (bif Nat.ble i 93 then ⟨569,3,[(0,3),(19,1)]⟩ else ⟨571,3,[(0,1),(1,1),(2,1),(7,1)]⟩) else ⟨577,5,[(0,6),(1,2)]⟩))))

private def row4 (i : ℕ) : Row :=
  (bif Nat.ble i 107 then (bif Nat.ble i 101 then (bif Nat.ble i 98 then (bif Nat.ble i 97 then (bif Nat.ble i 96 then ⟨587,2,[(0,1),(60,1)]⟩ else ⟨593,3,[(0,4),(11,1)]⟩) else ⟨601,7,[(0,3),(1,1),(2,2)]⟩) else (bif Nat.ble i 100 then (bif Nat.ble i 99 then ⟨607,3,[(0,1),(1,1),(25,1)]⟩ else ⟨613,2,[(0,2),(1,2),(6,1)]⟩) else ⟨617,3,[(0,3),(3,1),(4,1)]⟩)) else (bif Nat.ble i 104 then (bif Nat.ble i 103 then (bif Nat.ble i 102 then ⟨631,3,[(0,1),(1,2),(2,1),(3,1)]⟩ else ⟨641,3,[(0,7),(2,1)]⟩) else ⟨653,2,[(0,2),(37,1)]⟩) else (bif Nat.ble i 106 then (bif Nat.ble i 105 then ⟨661,2,[(0,2),(1,1),(2,1),(4,1)]⟩ else ⟨673,5,[(0,5),(1,1),(3,1)]⟩) else ⟨677,2,[(0,2),(5,2)]⟩))) else (bif Nat.ble i 113 then (bif Nat.ble i 110 then (bif Nat.ble i 109 then (bif Nat.ble i 108 then ⟨683,5,[(0,1),(4,1),(10,1)]⟩ else ⟨691,3,[(0,1),(1,1),(2,1),(8,1)]⟩) else ⟨709,2,[(0,2),(1,1),(16,1)]⟩) else (bif Nat.ble i 112 then (bif Nat.ble i 111 then ⟨739,3,[(0,1),(1,2),(12,1)]⟩ else ⟨743,5,[(0,1),(3,1),(15,1)]⟩) else ⟨751,3,[(0,1),(1,1),(2,3)]⟩)) else (bif Nat.ble i 116 then (bif Nat.ble i 115 then (bif Nat.ble i 114 then ⟨757,2,[(0,2),(1,3),(3,1)]⟩ else ⟨769,11,[(0,8),(1,1)]⟩) else ⟨787,2,[(0,1),(1,1),(31,1)]⟩) else (bif Nat.ble i 118 then (bif Nat.ble i 117 then ⟨797,2,[(0,2),(45,1)]⟩ else ⟨809,3,[(0,3),(25,1)]⟩) else ⟨821,2,[(0,2),(2,1),(12,1)]⟩))))

private def row5 (i : ℕ) : Row :=
  (bif Nat.ble i 131 then (bif Nat.ble i 125 then (bif Nat.ble i 122 then (bif Nat.ble i 121 then (bif Nat.ble i 120 then ⟨829,2,[(0,2),(1,2),(8,1)]⟩ else ⟨839,11,[(0,1),(74,1)]⟩) else ⟨853,2,[(0,2),(1,1),(19,1)]⟩) else (bif Nat.ble i 124 then (bif Nat.ble i 123 then ⟨859,2,[(0,1),(1,1),(4,1),(5,1)]⟩ else ⟨881,3,[(0,4),(2,1),(4,1)]⟩) else ⟨883,2,[(0,1),(1,2),(3,2)]⟩)) else (bif Nat.ble i 128 then (bif Nat.ble i 127 then (bif Nat.ble i 126 then ⟨907,2,[(0,1),(1,1),(35,1)]⟩ else ⟨911,17,[(0,1),(2,1),(3,1),(5,1)]⟩) else ⟨937,5,[(0,3),(1,2),(5,1)]⟩) else (bif Nat.ble i 130 then (bif Nat.ble i 129 then ⟨941,2,[(0,2),(2,1),(14,1)]⟩ else ⟨991,6,[(0,1),(1,2),(2,1),(4,1)]⟩) else ⟨1021,10,[(0,2),(1,1),(2,1),(6,1)]⟩))) else (bif Nat.ble i 137 then (bif Nat.ble i 134 then (bif Nat.ble i 133 then (bif Nat.ble i 132 then ⟨1031,14,[(0,1),(2,1),(26,1)]⟩ else ⟨1063,3,[(0,1),(1,2),(16,1)]⟩) else ⟨1069,6,[(0,2),(1,1),(23,1)]⟩) else (bif Nat.ble i 136 then (bif Nat.ble i 135 then ⟨1091,2,[(0,1),(2,1),(28,1)]⟩ else ⟨1093,5,[(0,2),(1,1),(3,1),(5,1)]⟩) else ⟨1097,3,[(0,3),(32,1)]⟩)) else (bif Nat.ble i 140 then (bif Nat.ble i 139 then (bif Nat.ble i 138 then ⟨1117,2,[(0,2),(1,2),(10,1)]⟩ else ⟨1181,7,[(0,2),(2,1),(16,1)]⟩) else ⟨1187,2,[(0,1),(97,1)]⟩) else (bif Nat.ble i 142 then (bif Nat.ble i 141 then ⟨1193,3,[(0,3),(34,1)]⟩ else ⟨1213,2,[(0,2),(1,1),(25,1)]⟩) else ⟨1223,5,[(0,1),(5,1),(14,1)]⟩))))

private def row6 (i : ℕ) : Row :=
  (bif Nat.ble i 155 then (bif Nat.ble i 149 then (bif Nat.ble i 146 then (bif Nat.ble i 145 then (bif Nat.ble i 144 then ⟨1297,10,[(0,4),(1,4)]⟩ else ⟨1307,2,[(0,1),(104,1)]⟩) else ⟨1321,13,[(0,3),(1,1),(2,1),(4,1)]⟩) else (bif Nat.ble i 148 then (bif Nat.ble i 147 then ⟨1327,3,[(0,1),(1,1),(5,1),(6,1)]⟩ else ⟨1361,3,[(0,4),(2,1),(6,1)]⟩) else ⟨1471,6,[(0,1),(1,1),(2,1),(3,2)]⟩)) else (bif Nat.ble i 152 then (bif Nat.ble i 151 then (bif Nat.ble i 150 then ⟨1483,2,[(0,1),(1,1),(5,1),(7,1)]⟩ else ⟨1487,5,[(0,1),(112,1)]⟩) else ⟨1489,14,[(0,4),(1,1),(10,1)]⟩) else (bif Nat.ble i 154 then (bif Nat.ble i 153 then ⟨1579,3,[(0,1),(1,1),(54,1)]⟩ else ⟨1583,5,[(0,1),(3,1),(29,1)]⟩) else ⟨1597,11,[(0,2),(1,1),(3,1),(7,1)]⟩))) else (bif Nat.ble i 161 then (bif Nat.ble i 158 then (bif Nat.ble i 157 then (bif Nat.ble i 156 then ⟨1601,3,[(0,6),(2,2)]⟩ else ⟨1621,2,[(0,2),(1,4),(2,1)]⟩) else ⟨1721,3,[(0,3),(2,1),(13,1)]⟩) else (bif Nat.ble i 160 then (bif Nat.ble i 159 then ⟨1733,2,[(0,2),(77,1)]⟩ else ⟨1759,6,[(0,1),(1,1),(60,1)]⟩) else ⟨1811,6,[(0,1),(2,1),(41,1)]⟩)) else (bif Nat.ble i 164 then (bif Nat.ble i 163 then (bif Nat.ble i 162 then ⟨1823,5,[(0,1),(127,1)]⟩ else ⟨1871,14,[(0,1),(2,1),(4,1),(6,1)]⟩) else ⟨1933,5,[(0,2),(1,1),(3,1),(8,1)]⟩) else (bif Nat.ble i 166 then (bif Nat.ble i 165 then ⟨1999,3,[(0,1),(1,3),(11,1)]⟩ else ⟨2017,5,[(0,5),(1,2),(3,1)]⟩) else ⟨2063,5,[(0,1),(132,1)]⟩))))

private def row7 (i : ℕ) : Row :=
  (bif Nat.ble i 179 then (bif Nat.ble i 173 then (bif Nat.ble i 170 then (bif Nat.ble i 169 then (bif Nat.ble i 168 then ⟨2081,3,[(0,5),(2,1),(5,1)]⟩ else ⟨2083,2,[(0,1),(1,1),(65,1)]⟩) else ⟨2141,2,[(0,2),(2,1),(27,1)]⟩) else (bif Nat.ble i 172 then (bif Nat.ble i 171 then ⟨2161,23,[(0,4),(1,3),(2,1)]⟩ else ⟨2243,2,[(0,1),(7,1),(16,1)]⟩) else ⟨2267,2,[(0,1),(4,1),(26,1)]⟩)) else (bif Nat.ble i 176 then (bif Nat.ble i 175 then (bif Nat.ble i 174 then ⟨2269,2,[(0,2),(1,4),(3,1)]⟩ else ⟨2309,2,[(0,2),(95,1)]⟩) else ⟨2347,3,[(0,1),(1,1),(6,1),(8,1)]⟩) else (bif Nat.ble i 178 then (bif Nat.ble i 177 then ⟨2521,17,[(0,3),(1,2),(2,1),(3,1)]⟩ else ⟨2593,7,[(0,5),(1,4)]⟩) else ⟨2647,3,[(0,1),(1,3),(3,2)]⟩))) else (bif Nat.ble i 185 then (bif Nat.ble i 182 then (bif Nat.ble i 181 then (bif Nat.ble i 180 then ⟨2683,2,[(0,1),(1,2),(34,1)]⟩ else ⟨2741,2,[(0,2),(2,1),(32,1)]⟩) else ⟨2851,2,[(0,1),(1,1),(2,2),(7,1)]⟩) else (bif Nat.ble i 184 then (bif Nat.ble i 183 then ⟨2857,11,[(0,3),(1,1),(3,1),(6,1)]⟩ else ⟨2887,5,[(0,1),(1,1),(5,1),(11,1)]⟩) else ⟨2897,3,[(0,4),(41,1)]⟩)) else (bif Nat.ble i 188 then (bif Nat.ble i 187 then (bif Nat.ble i 186 then ⟨3079,6,[(0,1),(1,4),(7,1)]⟩ else ⟨3083,2,[(0,1),(8,1),(18,1)]⟩) else ⟨3163,3,[(0,1),(1,1),(6,1),(10,1)]⟩) else (bif Nat.ble i 190 then (bif Nat.ble i 189 then ⟨3187,2,[(0,1),(1,3),(16,1)]⟩ else ⟨3203,2,[(0,1),(156,1)]⟩) else ⟨3253,2,[(0,2),(1,1),(56,1)]⟩))))

private def row8 (i : ℕ) : Row :=
  (bif Nat.ble i 203 then (bif Nat.ble i 197 then (bif Nat.ble i 194 then (bif Nat.ble i 193 then (bif Nat.ble i 192 then ⟨3307,2,[(0,1),(1,1),(7,1),(9,1)]⟩ else ⟨3389,3,[(0,2),(3,1),(4,2)]⟩) else ⟨3407,5,[(0,1),(5,1),(31,1)]⟩) else (bif Nat.ble i 196 then (bif Nat.ble i 195 then ⟨3449,3,[(0,3),(76,1)]⟩ else ⟨3467,2,[(0,1),(159,1)]⟩) else ⟨3517,2,[(0,2),(1,1),(60,1)]⟩)) else (bif Nat.ble i 200 then (bif Nat.ble i 199 then (bif Nat.ble i 198 then ⟨3581,2,[(0,2),(2,1),(40,1)]⟩ else ⟨3607,5,[(0,1),(1,1),(98,1)]⟩) else ⟨3637,2,[(0,2),(1,2),(25,1)]⟩) else (bif Nat.ble i 202 then (bif Nat.ble i 201 then ⟨3761,3,[(0,4),(2,1),(14,1)]⟩ else ⟨3767,5,[(0,1),(3,1),(55,1)]⟩) else ⟨3769,7,[(0,3),(1,1),(36,1)]⟩))) else (bif Nat.ble i 209 then (bif Nat.ble i 206 then (bif Nat.ble i 205 then (bif Nat.ble i 204 then ⟨3847,5,[(0,1),(1,1),(103,1)]⟩ else ⟨3851,2,[(0,1),(2,2),(3,1),(4,1)]⟩) else ⟨3889,11,[(0,4),(1,5)]⟩) else (bif Nat.ble i 208 then (bif Nat.ble i 207 then ⟨3911,13,[(0,1),(2,1),(6,1),(8,1)]⟩ else ⟨4019,2,[(0,1),(3,2),(12,1)]⟩) else ⟨4099,2,[(0,1),(1,1),(108,1)]⟩)) else (bif Nat.ble i 212 then (bif Nat.ble i 211 then (bif Nat.ble i 210 then ⟨4283,2,[(0,1),(170,1)]⟩ else ⟨4297,5,[(0,3),(1,1),(40,1)]⟩) else ⟨4339,10,[(0,1),(1,2),(51,1)]⟩) else (bif Nat.ble i 214 then (bif Nat.ble i 213 then ⟨4561,11,[(0,4),(1,1),(2,1),(7,1)]⟩ else ⟨4583,5,[(0,1),(9,1),(21,1)]⟩) else ⟨4931,6,[(0,1),(2,1),(6,1),(9,1)]⟩))))

private def row9 (i : ℕ) : Row :=
  (bif Nat.ble i 227 then (bif Nat.ble i 221 then (bif Nat.ble i 218 then (bif Nat.ble i 217 then (bif Nat.ble i 216 then ⟨5081,3,[(0,3),(2,1),(30,1)]⟩ else ⟨5501,2,[(0,2),(2,3),(4,1)]⟩) else ⟨5563,2,[(0,1),(1,3),(26,1)]⟩) else (bif Nat.ble i 220 then (bif Nat.ble i 219 then ⟨5569,13,[(0,6),(1,1),(9,1)]⟩ else ⟨5659,2,[(0,1),(1,1),(8,1),(12,1)]⟩) else ⟨5843,2,[(0,1),(8,1),(30,1)]⟩)) else (bif Nat.ble i 224 then (bif Nat.ble i 223 then (bif Nat.ble i 222 then ⟨6037,5,[(0,2),(1,1),(86,1)]⟩ else ⟨6091,7,[(0,1),(1,1),(2,1),(3,1),(9,1)]⟩) else ⟨6133,5,[(0,2),(1,1),(3,1),(20,1)]⟩) else (bif Nat.ble i 226 then (bif Nat.ble i 225 then ⟨6301,10,[(0,2),(1,2),(2,2),(3,1)]⟩ else ⟨6481,7,[(0,4),(1,4),(2,1)]⟩) else ⟨6553,10,[(0,3),(1,2),(3,1),(5,1)]⟩))) else (bif Nat.ble i 233 then (bif Nat.ble i 230 then (bif Nat.ble i 229 then (bif Nat.ble i 228 then ⟨6569,3,[(0,3),(119,1)]⟩ else ⟨6829,2,[(0,2),(1,1),(93,1)]⟩) else ⟨6883,2,[(0,1),(1,1),(10,1),(11,1)]⟩) else (bif Nat.ble i 232 then (bif Nat.ble i 231 then ⟨6899,2,[(0,1),(195,1)]⟩ else ⟨6917,2,[(0,2),(3,1),(5,1),(7,1)]⟩) else ⟨7333,6,[(0,2),(1,1),(5,1),(14,1)]⟩)) else (bif Nat.ble i 236 then (bif Nat.ble i 235 then (bif Nat.ble i 234 then ⟨7369,7,[(0,3),(1,1),(61,1)]⟩ else ⟨7487,5,[(0,1),(7,1),(44,1)]⟩) else ⟨7507,2,[(0,1),(1,3),(33,1)]⟩) else (bif Nat.ble i 238 then (bif Nat.ble i 237 then ⟨7691,2,[(0,1),(2,1),(115,1)]⟩ else ⟨7753,10,[(0,3),(1,1),(6,1),(7,1)]⟩) else ⟨7823,5,[(0,1),(207,1)]⟩))))

private def row10 (i : ℕ) : Row :=
  (bif Nat.ble i 251 then (bif Nat.ble i 245 then (bif Nat.ble i 242 then (bif Nat.ble i 241 then (bif Nat.ble i 240 then ⟨8069,2,[(0,2),(166,1)]⟩ else ⟨8209,7,[(0,4),(1,3),(7,1)]⟩) else ⟨8233,10,[(0,3),(1,1),(3,3)]⟩) else (bif Nat.ble i 244 then (bif Nat.ble i 243 then ⟨8951,13,[(0,1),(2,2),(40,1)]⟩ else ⟨9151,3,[(0,1),(1,1),(2,2),(17,1)]⟩) else ⟨9521,3,[(0,4),(2,1),(3,1),(6,1)]⟩)) else (bif Nat.ble i 248 then (bif Nat.ble i 247 then (bif Nat.ble i 246 then ⟨9601,13,[(0,7),(1,1),(2,2)]⟩ else ⟨9613,2,[(0,2),(1,3),(23,1)]⟩) else ⟨10069,2,[(0,2),(1,1),(121,1)]⟩) else (bif Nat.ble i 250 then (bif Nat.ble i 249 then ⟨10141,2,[(0,2),(1,1),(2,1),(5,2)]⟩ else ⟨10301,2,[(0,2),(2,2),(26,1)]⟩) else ⟨10453,5,[(0,2),(1,1),(5,1),(18,1)]⟩))) else (bif Nat.ble i 257 then (bif Nat.ble i 254 then (bif Nat.ble i 253 then (bif Nat.ble i 252 then ⟨10847,5,[(0,1),(4,1),(6,1),(9,1)]⟩ else ⟨11059,10,[(0,1),(1,1),(7,1),(24,1)]⟩) else ⟨11161,7,[(0,3),(1,2),(2,1),(10,1)]⟩) else (bif Nat.ble i 256 then (bif Nat.ble i 255 then ⟨11243,5,[(0,1),(3,1),(4,1),(20,1)]⟩ else ⟨11617,10,[(0,5),(1,1),(4,2)]⟩) else ⟨12119,7,[(0,1),(20,1),(22,1)]⟩)) else (bif Nat.ble i 260 then (bif Nat.ble i 259 then (bif Nat.ble i 258 then ⟨12413,2,[(0,2),(9,1),(27,1)]⟩ else ⟨12653,2,[(0,2),(188,1)]⟩) else ⟨12853,5,[(0,2),(1,3),(3,1),(6,1)]⟩) else (bif Nat.ble i 262 then (bif Nat.ble i 261 then ⟨13627,2,[(0,1),(1,2),(114,1)]⟩ else ⟨13799,7,[(0,1),(231,1)]⟩) else ⟨14009,3,[(0,3),(6,1),(26,1)]⟩))))

private def row11 (i : ℕ) : Row :=
  (bif Nat.ble i 275 then (bif Nat.ble i 269 then (bif Nat.ble i 266 then (bif Nat.ble i 265 then (bif Nat.ble i 264 then ⟨14177,3,[(0,5),(79,1)]⟩ else ⟨14321,3,[(0,4),(2,1),(40,1)]⟩) else ⟨14401,11,[(0,6),(1,2),(2,2)]⟩) else (bif Nat.ble i 268 then (bif Nat.ble i 267 then ⟨14549,2,[(0,2),(200,1)]⟩ else ⟨14557,2,[(0,2),(1,1),(142,1)]⟩) else ⟨14831,11,[(0,1),(2,1),(150,1)]⟩)) else (bif Nat.ble i 272 then (bif Nat.ble i 271 then (bif Nat.ble i 270 then ⟨14843,2,[(0,1),(12,1),(41,1)]⟩ else ⟨15061,2,[(0,2),(1,1),(2,1),(52,1)]⟩) else ⟨15077,2,[(0,2),(203,1)]⟩) else (bif Nat.ble i 274 then (bif Nat.ble i 273 then ⟨15241,11,[(0,3),(1,1),(2,1),(30,1)]⟩ else ⟨16103,5,[(0,1),(22,1),(24,1)]⟩) else ⟨16493,2,[(0,2),(3,1),(7,1),(10,1)]⟩))) else (bif Nat.ble i 281 then (bif Nat.ble i 278 then (bif Nat.ble i 277 then (bif Nat.ble i 276 then ⟨16829,2,[(0,2),(3,1),(98,1)]⟩ else ⟨16921,17,[(0,3),(1,2),(2,1),(14,1)]⟩) else ⟨17569,11,[(0,5),(1,2),(17,1)]⟩) else (bif Nat.ble i 280 then (bif Nat.ble i 279 then ⟨17923,2,[(0,1),(1,1),(9,1),(26,1)]⟩ else ⟨18211,7,[(0,1),(1,1),(2,1),(99,1)]⟩) else ⟨18427,2,[(0,1),(1,1),(11,1),(22,1)]⟩)) else (bif Nat.ble i 284 then (bif Nat.ble i 283 then (bif Nat.ble i 282 then ⟨19441,13,[(0,4),(1,5),(2,1)]⟩ else ⟨19489,19,[(0,5),(1,1),(3,1),(9,1)]⟩) else ⟨19927,6,[(0,1),(1,5),(12,1)]⟩) else (bif Nat.ble i 286 then (bif Nat.ble i 285 then ⟨20149,2,[(0,2),(1,1),(8,1),(20,1)]⟩ else ⟨20693,2,[(0,2),(3,1),(111,1)]⟩) else ⟨21061,7,[(0,2),(1,4),(2,1),(5,1)]⟩))))

private def row12 (i : ℕ) : Row :=
  (bif Nat.ble i 299 then (bif Nat.ble i 293 then (bif Nat.ble i 290 then (bif Nat.ble i 289 then (bif Nat.ble i 288 then ⟨21341,2,[(0,2),(2,1),(4,1),(24,1)]⟩ else ⟨21997,7,[(0,2),(1,2),(5,1),(14,1)]⟩) else ⟨22619,2,[(0,1),(13,1),(54,1)]⟩) else (bif Nat.ble i 292 then (bif Nat.ble i 291 then ⟨22907,5,[(0,1),(5,1),(124,1)]⟩ else ⟨24169,11,[(0,3),(1,1),(7,1),(15,1)]⟩) else ⟨24379,2,[(0,1),(1,1),(6,1),(50,1)]⟩)) else (bif Nat.ble i 296 then (bif Nat.ble i 295 then (bif Nat.ble i 294 then ⟨25411,7,[(0,1),(1,1),(2,1),(3,1),(4,2)]⟩ else ⟨25867,2,[(0,1),(1,3),(82,1)]⟩) else ⟨26701,22,[(0,2),(1,1),(2,2),(23,1)]⟩) else (bif Nat.ble i 298 then (bif Nat.ble i 297 then ⟨26713,10,[(0,3),(1,2),(3,1),(15,1)]⟩ else ⟨27967,3,[(0,1),(1,1),(16,1),(21,1)]⟩) else ⟨28537,5,[(0,3),(1,1),(9,1),(12,1)]⟩))) else (bif Nat.ble i 305 then (bif Nat.ble i 302 then (bif Nat.ble i 301 then (bif Nat.ble i 300 then ⟨29917,2,[(0,2),(1,3),(57,1)]⟩ else ⟨30091,21,[(0,1),(1,1),(2,1),(6,1),(16,1)]⟩) else ⟨33703,5,[(0,1),(1,1),(12,1),(32,1)]⟩) else (bif Nat.ble i 304 then (bif Nat.ble i 303 then ⟨34511,7,[(0,1),(2,1),(3,1),(6,1),(9,1)]⟩ else ⟨37963,2,[(0,1),(1,3),(7,1),(11,1)]⟩) else ⟨38453,2,[(0,2),(247,1)]⟩)) else (bif Nat.ble i 308 then (bif Nat.ble i 307 then (bif Nat.ble i 306 then ⟨40277,2,[(0,2),(248,1)]⟩ else ⟨43577,3,[(0,3),(5,1),(74,1)]⟩) else ⟨50077,2,[(0,2),(1,2),(5,1),(27,1)]⟩) else (bif Nat.ble i 310 then (bif Nat.ble i 309 then ⟨51157,5,[(0,2),(1,2),(3,2),(9,1)]⟩ else ⟨51169,14,[(0,5),(1,1),(5,1),(12,1)]⟩) else ⟨51631,15,[(0,1),(1,1),(2,1),(158,1)]⟩))))

private def row13 (i : ℕ) : Row :=
  (bif Nat.ble i 323 then (bif Nat.ble i 317 then (bif Nat.ble i 314 then (bif Nat.ble i 313 then (bif Nat.ble i 312 then ⟨52553,3,[(0,3),(228,1)]⟩ else ⟨53923,5,[(0,1),(1,1),(4,1),(7,1),(13,1)]⟩) else ⟨54409,7,[(0,3),(1,1),(173,1)]⟩) else (bif Nat.ble i 316 then (bif Nat.ble i 315 then ⟨58937,3,[(0,3),(15,1),(33,1)]⟩ else ⟨59561,3,[(0,3),(2,1),(152,1)]⟩) else ⟨63499,3,[(0,1),(1,1),(7,1),(91,1)]⟩)) else (bif Nat.ble i 320 then (bif Nat.ble i 319 then (bif Nat.ble i 318 then ⟨74821,6,[(0,2),(1,1),(2,1),(9,1),(13,1)]⟩ else ⟨75181,2,[(0,2),(1,1),(2,1),(3,1),(40,1)]⟩) else ⟨76631,7,[(0,1),(2,1),(21,1),(24,1)]⟩) else (bif Nat.ble i 322 then (bif Nat.ble i 321 then ⟨76801,17,[(0,10),(1,1),(2,2)]⟩ else ⟨76907,2,[(0,1),(305,1)]⟩) else ⟨81509,2,[(0,2),(3,1),(12,1),(19,1)]⟩))) else (bif Nat.ble i 329 then (bif Nat.ble i 326 then (bif Nat.ble i 325 then (bif Nat.ble i 324 then ⟨98377,5,[(0,3),(1,1),(209,1)]⟩ else ⟨101917,5,[(0,2),(1,2),(7,1),(34,1)]⟩) else ⟨102673,5,[(0,4),(1,2),(8,1),(10,1)]⟩) else (bif Nat.ble i 328 then (bif Nat.ble i 327 then ⟨104003,2,[(0,1),(34,1),(66,1)]⟩ else ⟨107671,6,[(0,1),(1,1),(2,1),(11,1),(24,1)]⟩) else ⟨124909,18,[(0,2),(1,1),(3,1),(151,1)]⟩)) else (bif Nat.ble i 332 then (bif Nat.ble i 331 then (bif Nat.ble i 330 then ⟨125269,2,[(0,2),(1,1),(4,1),(5,1),(20,1)]⟩ else ⟨131713,5,[(0,7),(1,1),(3,3)]⟩) else ⟨136531,2,[(0,1),(1,2),(2,1),(11,1),(12,1)]⟩) else (bif Nat.ble i 334 then (bif Nat.ble i 333 then ⟨151141,2,[(0,2),(1,1),(2,1),(4,1),(49,1)]⟩ else ⟨153059,2,[(0,1),(26,1),(112,1)]⟩) else ⟨155203,3,[(0,1),(1,1),(295,1)]⟩))))

private def row14 (i : ℕ) : Row :=
  (bif Nat.ble i 347 then (bif Nat.ble i 341 then (bif Nat.ble i 338 then (bif Nat.ble i 337 then (bif Nat.ble i 336 then ⟨160207,3,[(0,1),(1,1),(296,1)]⟩ else ⟨162119,11,[(0,1),(4,1),(234,1)]⟩) else ⟨163019,2,[(0,1),(323,1)]⟩) else (bif Nat.ble i 340 then (bif Nat.ble i 339 then ⟨172321,13,[(0,5),(1,1),(2,1),(67,1)]⟩ else ⟨176419,2,[(0,1),(1,6),(4,2)]⟩) else ⟨179801,3,[(0,3),(2,2),(9,1),(10,1)]⟩)) else (bif Nat.ble i 344 then (bif Nat.ble i 343 then (bif Nat.ble i 342 then ⟨182239,15,[(0,1),(1,1),(3,1),(212,1)]⟩ else ⟨188831,11,[(0,1),(2,1),(8,1),(119,1)]⟩) else ⟨197441,6,[(0,6),(2,1),(101,1)]⟩) else (bif Nat.ble i 346 then (bif Nat.ble i 345 then ⟨207169,19,[(0,6),(1,1),(5,1),(22,1)]⟩ else ⟨221101,22,[(0,2),(1,1),(2,2),(4,1),(18,1)]⟩) else ⟨229837,7,[(0,2),(1,1),(27,1),(40,1)]⟩))) else (bif Nat.ble i 353 then (bif Nat.ble i 350 then (bif Nat.ble i 349 then (bif Nat.ble i 348 then ⟨247547,2,[(0,1),(5,1),(245,1)]⟩ else ⟨248749,2,[(0,2),(1,1),(7,1),(135,1)]⟩) else ⟨252401,3,[(0,4),(2,2),(102,1)]⟩) else (bif Nat.ble i 352 then (bif Nat.ble i 351 then ⟨256057,11,[(0,3),(1,1),(14,1),(48,1)]⟩ else ⟨259717,6,[(0,2),(1,1),(8,1),(129,1)]⟩) else ⟨267131,2,[(0,1),(2,1),(297,1)]⟩)) else (bif Nat.ble i 356 then (bif Nat.ble i 355 then (bif Nat.ble i 354 then ⟨282389,2,[(0,2),(48,1),(62,1)]⟩ else ⟨284989,6,[(0,2),(1,1),(4,1),(6,1),(30,1)]⟩) else ⟨298801,7,[(0,4),(1,2),(2,2),(22,1)]⟩) else (bif Nat.ble i 358 then (bif Nat.ble i 357 then ⟨324151,3,[(0,1),(1,1),(2,2),(171,1)]⟩ else ⟨324239,11,[(0,1),(337,1)]⟩) else ⟨328777,10,[(0,3),(1,1),(3,1),(7,1),(26,1)]⟩))))

private def row15 (i : ℕ) : Row :=
  (bif Nat.ble i 371 then (bif Nat.ble i 365 then (bif Nat.ble i 362 then (bif Nat.ble i 361 then (bif Nat.ble i 360 then ⟨341273,3,[(0,3),(9,1),(149,1)]⟩ else ⟨351397,2,[(0,2),(1,2),(13,1),(48,1)]⟩) else ⟨357073,5,[(0,4),(1,1),(13,1),(39,1)]⟩) else (bif Nat.ble i 364 then (bif Nat.ble i 363 then ⟨363889,13,[(0,4),(1,2),(3,1),(7,2)]⟩ else ⟨368089,11,[(0,3),(1,1),(3,2),(63,1)]⟩) else ⟨381319,3,[(0,1),(1,1),(3,2),(144,1)]⟩)) else (bif Nat.ble i 368 then (bif Nat.ble i 367 then (bif Nat.ble i 366 then ⟨381371,2,[(0,1),(2,1),(4,1),(196,1)]⟩ else ⟨387631,6,[(0,1),(1,2),(2,1),(16,1),(20,1)]⟩) else ⟨391151,13,[(0,1),(2,2),(239,1)]⟩) else (bif Nat.ble i 370 then (bif Nat.ble i 369 then ⟨394201,7,[(0,3),(1,3),(2,2),(20,1)]⟩ else ⟨398581,2,[(0,2),(1,1),(2,1),(3,1),(5,1),(20,1)]⟩) else ⟨419999,13,[(0,1),(69,1),(92,1)]⟩))) else (bif Nat.ble i 377 then (bif Nat.ble i 374 then (bif Nat.ble i 373 then (bif Nat.ble i 372 then ⟨430697,5,[(0,3),(3,1),(237,1)]⟩ else ⟨449131,3,[(0,1),(1,1),(2,1),(4,1),(148,1)]⟩) else ⟨478351,3,[(0,1),(1,2),(2,2),(133,1)]⟩) else (bif Nat.ble i 376 then (bif Nat.ble i 375 then ⟨513407,5,[(0,1),(8,1),(254,1)]⟩ else ⟨530713,5,[(0,3),(1,6),(3,1),(5,1)]⟩) else ⟨564779,2,[(0,1),(354,1)]⟩)) else (bif Nat.ble i 380 then (bif Nat.ble i 379 then (bif Nat.ble i 378 then ⟨570461,7,[(0,2),(2,1),(4,1),(178,1)]⟩ else ⟨593291,6,[(0,1),(2,1),(21,1),(113,1)]⟩) else ⟨603901,10,[(0,2),(1,2),(2,2),(4,1),(17,1)]⟩) else (bif Nat.ble i 382 then (bif Nat.ble i 381 then ⟨638147,5,[(0,1),(6,1),(32,2)]⟩ else ⟨644747,2,[(0,1),(7,3),(14,1)]⟩) else ⟨647753,5,[(0,3),(3,1),(13,1),(55,1)]⟩))))

private def row16 (i : ℕ) : Row :=
  (bif Nat.ble i 395 then (bif Nat.ble i 389 then (bif Nat.ble i 386 then (bif Nat.ble i 385 then (bif Nat.ble i 384 then ⟨652909,2,[(0,2),(1,1),(314,1)]⟩ else ⟨659671,12,[(0,1),(1,1),(2,1),(4,1),(165,1)]⟩) else ⟨681229,7,[(0,2),(1,2),(30,1),(34,1)]⟩) else (bif Nat.ble i 388 then (bif Nat.ble i 387 then ⟨682901,2,[(0,2),(2,2),(229,1)]⟩ else ⟨714893,2,[(0,2),(63,1),(94,1)]⟩) else ⟨755551,11,[(0,1),(1,2),(2,2),(8,1),(20,1)]⟩)) else (bif Nat.ble i 392 then (bif Nat.ble i 391 then (bif Nat.ble i 390 then ⟨797161,17,[(0,3),(1,1),(2,1),(3,1),(5,1),(20,1)]⟩ else ⟨839999,17,[(0,1),(371,1)]⟩) else ⟨927001,14,[(0,3),(1,2),(2,3),(26,1)]⟩) else (bif Nat.ble i 394 then (bif Nat.ble i 393 then ⟨956353,7,[(0,6),(1,1),(6,1),(60,1)]⟩ else ⟨961243,3,[(0,1),(1,1),(336,1)]⟩) else ⟨972409,19,[(0,3),(1,1),(10,1),(145,1)]⟩))) else (bif Nat.ble i 401 then (bif Nat.ble i 398 then (bif Nat.ble i 397 then (bif Nat.ble i 396 then ⟨976231,11,[(0,1),(1,2),(2,1),(252,1)]⟩ else ⟨1028263,3,[(0,1),(1,1),(6,2),(97,1)]⟩) else ⟨1129559,7,[(0,1),(377,1)]⟩) else (bif Nat.ble i 400 then (bif Nat.ble i 399 then ⟨1160839,3,[(0,1),(1,3),(3,1),(11,1),(22,1)]⟩ else ⟨1190701,11,[(0,2),(1,5),(2,2),(3,2)]⟩) else ⟨1226831,7,[(0,1),(2,1),(4,1),(7,1),(96,1)]⟩)) else (bif Nat.ble i 404 then (bif Nat.ble i 403 then (bif Nat.ble i 402 then ⟨1249091,2,[(0,1),(2,1),(329,1)]⟩ else ⟨1309313,3,[(0,7),(15,1),(43,1)]⟩) else ⟨1546073,3,[(0,3),(4,1),(278,1)]⟩) else (bif Nat.ble i 406 then (bif Nat.ble i 405 then ⟨1548587,2,[(0,1),(5,1),(316,1)]⟩ else ⟨1616161,17,[(0,5),(1,1),(2,1),(3,1),(5,1),(11,1)]⟩) else ⟨1797031,3,[(0,1),(1,2),(2,1),(12,1),(83,1)]⟩))))

private def row17 (i : ℕ) : Row :=
  (bif Nat.ble i 419 then (bif Nat.ble i 413 then (bif Nat.ble i 410 then (bif Nat.ble i 409 then (bif Nat.ble i 408 then ⟨1903757,2,[(0,2),(8,1),(286,1)]⟩ else ⟨1904971,2,[(0,1),(1,1),(2,1),(317,1)]⟩) else ⟨1960789,2,[(0,2),(1,1),(15,1),(187,1)]⟩) else (bif Nat.ble i 412 then (bif Nat.ble i 411 then ⟨1975931,6,[(0,1),(2,1),(4,2),(8,1),(19,1)]⟩ else ⟨2132771,2,[(0,1),(2,1),(56,1),(116,1)]⟩) else ⟨2172539,2,[(0,1),(29,1),(247,1)]⟩)) else (bif Nat.ble i 416 then (bif Nat.ble i 415 then (bif Nat.ble i 414 then ⟨2382953,5,[(0,3),(4,1),(5,1),(169,1)]⟩ else ⟨2521621,6,[(0,2),(1,2),(2,1),(263,1)]⟩) else ⟨2526913,10,[(0,6),(1,2),(12,1),(27,1)]⟩) else (bif Nat.ble i 418 then (bif Nat.ble i 417 then ⟨2747711,7,[(0,1),(2,1),(3,1),(6,1),(175,1)]⟩ else ⟨3186217,10,[(0,3),(1,5),(4,1),(34,1)]⟩) else ⟨3462881,3,[(0,5),(2,1),(8,1),(129,1)]⟩))) else (bif Nat.ble i 425 then (bif Nat.ble i 422 then (bif Nat.ble i 421 then (bif Nat.ble i 420 then ⟨3701101,2,[(0,2),(1,1),(2,2),(5,2),(20,1)]⟩ else ⟨3755707,5,[(0,1),(1,1),(13,1),(268,1)]⟩) else ⟨3961333,2,[(0,2),(1,3),(13,1),(122,1)]⟩) else (bif Nat.ble i 424 then (bif Nat.ble i 423 then ⟨4025239,3,[(0,1),(1,1),(3,1),(50,1),(72,1)]⟩ else ⟨4162861,7,[(0,2),(1,3),(2,1),(5,1),(97,1)]⟩) else ⟨4404047,5,[(0,1),(10,1),(52,1),(59,1)]⟩)) else (bif Nat.ble i 428 then (bif Nat.ble i 427 then (bif Nat.ble i 426 then ⟨4904821,2,[(0,2),(1,3),(2,1),(10,1),(60,1)]⟩ else ⟨4975759,3,[(0,1),(1,2),(7,1),(267,1)]⟩) else ⟨5112661,10,[(0,2),(1,1),(2,1),(3,2),(11,1),(14,1)]⟩) else (bif Nat.ble i 430 then (bif Nat.ble i 429 then ⟨5181941,3,[(0,2),(2,1),(6,1),(273,1)]⟩ else ⟨5301533,2,[(0,2),(7,1),(21,1),(125,1)]⟩) else ⟨5385997,5,[(0,2),(1,2),(3,1),(4,1),(9,1),(18,1)]⟩))))

private def row18 (i : ℕ) : Row :=
  (bif Nat.ble i 443 then (bif Nat.ble i 437 then (bif Nat.ble i 434 then (bif Nat.ble i 433 then (bif Nat.ble i 432 then ⟨5603291,2,[(0,1),(2,1),(3,1),(4,1),(7,1),(70,1)]⟩ else ⟨5664931,2,[(0,1),(1,1),(2,1),(343,1)]⟩) else ⟨5774023,5,[(0,1),(1,2),(24,1),(192,1)]⟩) else (bif Nat.ble i 436 then (bif Nat.ble i 435 then ⟨6942713,3,[(0,3),(3,2),(23,1),(45,1)]⟩ else ⟨7360987,3,[(0,1),(1,1),(401,1)]⟩) else ⟨8866391,7,[(0,1),(2,1),(5,1),(51,1),(59,1)]⟩)) else (bif Nat.ble i 440 then (bif Nat.ble i 439 then (bif Nat.ble i 438 then ⟨12553493,2,[(0,2),(3,1),(8,1),(25,1),(43,1)]⟩ else ⟨13097927,5,[(0,1),(11,1),(54,1),(106,1)]⟩) else ⟨13150933,5,[(0,2),(1,1),(44,1),(218,1)]⟩) else (bif Nat.ble i 442 then (bif Nat.ble i 441 then ⟨15638533,5,[(0,2),(1,1),(3,1),(5,1),(265,1)]⟩ else ⟨15923777,3,[(0,6),(4,1),(290,1)]⟩) else ⟨16591823,5,[(0,1),(5,1),(381,1)]⟩))) else (bif Nat.ble i 449 then (bif Nat.ble i 446 then (bif Nat.ble i 445 then (bif Nat.ble i 444 then ⟨17163827,2,[(0,1),(119,1),(251,1)]⟩ else ⟨18702169,14,[(0,3),(1,1),(11,1),(287,1)]⟩) else ⟨18912419,6,[(0,1),(3,1),(10,1),(307,1)]⟩) else (bif Nat.ble i 448 then (bif Nat.ble i 447 then ⟨20381027,2,[(0,1),(9,1),(361,1)]⟩ else ⟨21520151,7,[(0,1),(2,2),(30,1),(193,1)]⟩) else ⟨21523361,6,[(0,5),(2,1),(6,1),(12,1),(43,1)]⟩)) else (bif Nat.ble i 452 then (bif Nat.ble i 451 then (bif Nat.ble i 450 then ⟨22041683,2,[(0,1),(5,1),(8,1),(9,1),(10,1),(12,1)]⟩ else ⟨22071677,2,[(0,2),(4,1),(18,1),(235,1)]⟩) else ⟨22115783,5,[(0,1),(5,1),(103,1),(147,1)]⟩) else (bif Nat.ble i 454 then (bif Nat.ble i 453 then ⟨22149217,10,[(0,5),(1,2),(322,1)]⟩ else ⟨22690571,6,[(0,1),(2,1),(3,1),(357,1)]⟩) else ⟨22996651,2,[(0,1),(1,1),(2,2),(7,1),(240,1)]⟩))))

private def row19 (i : ℕ) : Row :=
  (bif Nat.ble i 467 then (bif Nat.ble i 461 then (bif Nat.ble i 458 then (bif Nat.ble i 457 then (bif Nat.ble i 456 then ⟨23863523,2,[(0,1),(110,1),(276,1)]⟩ else ⟨24312923,2,[(0,1),(11,1),(25,1),(191,1)]⟩) else ⟨25132867,5,[(0,1),(1,1),(4,1),(44,1),(164,1)]⟩) else (bif Nat.ble i 460 then (bif Nat.ble i 459 then ⟨26050081,11,[(0,5),(1,1),(2,1),(3,1),(238,1)]⟩ else ⟨32234893,2,[(0,2),(1,1),(9,1),(46,1),(78,1)]⟩) else ⟨33034273,5,[(0,5),(1,1),(25,1),(194,1)]⟩)) else (bif Nat.ble i 464 then (bif Nat.ble i 463 then (bif Nat.ble i 462 then ⟨34132751,7,[(0,1),(2,3),(332,1)]⟩ else ⟨41354231,7,[(0,1),(2,1),(8,1),(341,1)]⟩) else ⟨42521761,11,[(0,5),(1,4),(2,1),(6,1),(43,1)]⟩) else (bif Nat.ble i 466 then (bif Nat.ble i 465 then ⟨47283557,2,[(0,2),(10,1),(365,1)]⟩ else ⟨47763361,23,[(0,5),(1,2),(2,1),(12,1),(118,1)]⟩) else ⟨51457561,34,[(0,3),(1,1),(2,1),(3,1),(4,1),(219,1)]⟩))) else (bif Nat.ble i 473 then (bif Nat.ble i 470 then (bif Nat.ble i 469 then (bif Nat.ble i 468 then ⟨56737873,5,[(0,4),(1,2),(8,1),(11,1),(81,1)]⟩ else ⟨59274119,7,[(0,1),(22,1),(362,1)]⟩) else ⟨72919087,3,[(0,1),(1,1),(6,1),(388,1)]⟩) else (bif Nat.ble i 472 then (bif Nat.ble i 471 then ⟨76082653,5,[(0,2),(1,4),(13,2),(30,1)]⟩ else ⟨78477137,3,[(0,4),(426,1)]⟩) else ⟨78719947,2,[(0,1),(1,1),(15,1),(348,1)]⟩)) else (bif Nat.ble i 476 then (bif Nat.ble i 475 then (bif Nat.ble i 474 then ⟨83151337,5,[(0,3),(1,1),(13,1),(44,1),(73,1)]⟩ else ⟨85907447,5,[(0,1),(14,1),(79,1),(167,1)]⟩) else ⟨96656723,2,[(0,1),(14,1),(397,1)]⟩) else (bif Nat.ble i 478 then (bif Nat.ble i 477 then ⟨104474177,3,[(0,6),(13,1),(304,1)]⟩ else ⟨105340409,3,[(0,3),(7,1),(29,1),(224,1)]⟩) else ⟨109688713,5,[(0,3),(1,1),(3,1),(384,1)]⟩))))

private def row20 (i : ℕ) : Row :=
  (bif Nat.ble i 491 then (bif Nat.ble i 485 then (bif Nat.ble i 482 then (bif Nat.ble i 481 then (bif Nat.ble i 480 then ⟨119779213,5,[(0,2),(1,1),(3,1),(6,1),(11,1),(173,1)]⟩ else ⟨129159847,6,[(0,1),(1,9),(6,1),(43,1)]⟩) else ⟨132694699,3,[(0,1),(1,1),(452,1)]⟩) else (bif Nat.ble i 484 then (bif Nat.ble i 483 then ⟨136243931,2,[(0,1),(2,1),(31,1),(327,1)]⟩ else ⟨156385331,2,[(0,1),(2,1),(441,1)]⟩) else ⟨172514977,7,[(0,5),(1,1),(407,1)]⟩)) else (bif Nat.ble i 488 then (bif Nat.ble i 487 then (bif Nat.ble i 486 then ⟨210680819,2,[(0,1),(478,1)]⟩ else ⟨232285523,2,[(0,1),(3,1),(443,1)]⟩) else ⟨335268397,2,[(0,2),(1,4),(11,1),(298,1)]⟩) else (bif Nat.ble i 490 then (bif Nat.ble i 489 then ⟨356911757,2,[(0,2),(126,1),(324,1)]⟩ else ⟨358254649,41,[(0,3),(1,2),(427,1)]⟩) else ⟨358291751,11,[(0,1),(2,3),(23,1),(274,1)]⟩))) else (bif Nat.ble i 497 then (bif Nat.ble i 494 then (bif Nat.ble i 493 then (bif Nat.ble i 492 then ⟨432853009,11,[(0,4),(1,1),(3,1),(8,1),(21,1),(110,1)]⟩ else ⟨433750657,5,[(0,7),(1,1),(398,1)]⟩) else ⟨496250773,6,[(0,2),(1,1),(463,1)]⟩) else (bif Nat.ble i 496 then (bif Nat.ble i 495 then ⟨521402591,17,[(0,1),(2,1),(28,1),(374,1)]⟩ else ⟨550554229,10,[(0,2),(1,2),(3,1),(11,1),(32,1),(76,1)]⟩) else ⟨582372997,11,[(0,2),(1,1),(197,1),(262,1)]⟩)) else (bif Nat.ble i 500 then (bif Nat.ble i 499 then (bif Nat.ble i 498 then ⟨597046729,7,[(0,3),(1,1),(7,1),(403,1)]⟩ else ⟨620451599,11,[(0,1),(5,1),(456,1)]⟩) else ⟨854871637,2,[(0,2),(1,1),(7,1),(8,1),(338,1)]⟩) else (bif Nat.ble i 502 then (bif Nat.ble i 501 then ⟨857643277,2,[(0,2),(1,1),(3,2),(11,1),(21,1),(85,1)]⟩ else ⟨929020693,11,[(0,2),(1,1),(6,1),(8,1),(71,1),(87,1)]⟩) else ⟨1000527599,7,[(0,1),(3,1),(19,2),(264,1)]⟩))))

private def row21 (i : ℕ) : Row :=
  (bif Nat.ble i 515 then (bif Nat.ble i 509 then (bif Nat.ble i 506 then (bif Nat.ble i 505 then (bif Nat.ble i 504 then ⟨1001523179,2,[(0,1),(8,1),(9,1),(11,1),(26,1),(44,1)]⟩ else ⟨1036745531,10,[(0,1),(2,1),(22,1),(402,1)]⟩) else ⟨1162320517,5,[(0,2),(1,10),(3,1),(7,1),(11,1)]⟩) else (bif Nat.ble i 508 then (bif Nat.ble i 507 then ⟨1375381201,11,[(0,4),(1,1),(2,2),(77,1),(179,1)]⟩ else ⟨1403808961,17,[(0,6),(1,1),(2,1),(10,1),(13,1),(137,1)]⟩) else ⟨1743831169,7,[(0,7),(1,1),(6,1),(353,1)]⟩)) else (bif Nat.ble i 512 then (bif Nat.ble i 511 then (bif Nat.ble i 510 then ⟨1824179209,7,[(0,3),(1,1),(7,2),(62,1),(107,1)]⟩ else ⟨1846794457,11,[(0,3),(1,2),(5,1),(6,1),(57,1),(74,1)]⟩) else ⟨2093124281,6,[(0,3),(2,1),(5,1),(423,1)]⟩) else (bif Nat.ble i 514 then (bif Nat.ble i 513 then ⟨2141470543,5,[(0,1),(1,1),(489,1)]⟩ else ⟨2413941289,34,[(0,3),(1,1),(4,2),(17,1),(261,1)]⟩) else ⟨2453987681,3,[(0,5),(2,1),(198,1),(210,1)]⟩))) else (bif Nat.ble i 521 then (bif Nat.ble i 518 then (bif Nat.ble i 517 then (bif Nat.ble i 516 then ⟨2664097031,7,[(0,1),(2,1),(3,1),(6,1),(88,1),(211,1)]⟩ else ⟨2860659169,23,[(0,5),(1,1),(10,1),(394,1)]⟩) else ⟨2867101189,2,[(0,2),(1,1),(3,1),(47,1),(334,1)]⟩) else (bif Nat.ble i 520 then (bif Nat.ble i 519 then ⟨3499901929,11,[(0,3),(1,2),(6,1),(11,1),(28,1),(110,1)]⟩ else ⟨4011586307,5,[(0,1),(3,1),(5,1),(450,1)]⟩) else ⟨4098005627,2,[(0,1),(4,1),(5,2),(27,1),(250,1)]⟩)) else (bif Nat.ble i 524 then (bif Nat.ble i 523 then (bif Nat.ble i 522 then ⟨4795973261,2,[(0,2),(2,1),(5,2),(23,1),(27,1),(34,1)]⟩ else ⟨5960866633,5,[(0,3),(1,1),(3,1),(21,1),(373,1)]⟩) else ⟨5970467291,2,[(0,1),(2,1),(498,1)]⟩) else (bif Nat.ble i 526 then (bif Nat.ble i 525 then ⟨7151459701,10,[(0,2),(1,1),(2,2),(3,1),(4,1),(6,1),(280,1)]⟩ else ⟨7326129407,5,[(0,1),(202,1),(395,1)]⟩) else ⟨9500438809,23,[(0,3),(1,6),(3,1),(10,1),(236,1)]⟩))))

private def row22 (i : ℕ) : Row :=
  (bif Nat.ble i 539 then (bif Nat.ble i 533 then (bif Nat.ble i 530 then (bif Nat.ble i 529 then (bif Nat.ble i 528 then ⟨14425532687,5,[(0,1),(15,1),(16,1),(18,1),(39,1),(45,1)]⟩ else ⟨14781691751,14,[(0,1),(2,3),(3,1),(8,1),(79,1),(120,1)]⟩) else ⟨15417089899,2,[(0,1),(1,1),(3,1),(34,1),(108,1),(199,1)]⟩) else (bif Nat.ble i 532 then (bif Nat.ble i 531 then ⟨15768033143,5,[(0,1),(20,1),(90,1),(344,1)]⟩ else ⟨17189128703,5,[(0,1),(11,1),(487,1)]⟩) else ⟨18138570679,3,[(0,1),(1,3),(24,1),(419,1)]⟩)) else (bif Nat.ble i 536 then (bif Nat.ble i 535 then (bif Nat.ble i 534 then ⟨22434744889,11,[(0,3),(1,2),(10,2),(358,1)]⟩ else ⟨23535794707,5,[(0,1),(1,1),(8,1),(18,1),(105,1),(205,1)]⟩) else ⟨24127552321,17,[(0,6),(1,1),(2,1),(458,1)]⟩) else (bif Nat.ble i 538 then (bif Nat.ble i 537 then ⟨25480398173,2,[(0,2),(7,1),(488,1)]⟩ else ⟨26751945361,13,[(0,4),(1,1),(2,1),(3,1),(442,1)]⟩) else ⟨56625998353,5,[(0,4),(1,1),(3,1),(4,1),(22,1),(44,1),(128,1)]⟩))) else (bif Nat.ble i 545 then (bif Nat.ble i 542 then (bif Nat.ble i 541 then (bif Nat.ble i 540 then ⟨61070817601,11,[(0,6),(1,2),(2,2),(5,1),(33,1),(176,1)]⟩ else ⟨76801257619,2,[(0,1),(1,1),(34,1),(475,1)]⟩) else ⟨76831835389,22,[(0,2),(1,1),(3,1),(4,1),(474,1)]⟩) else (bif Nat.ble i 544 then (bif Nat.ble i 543 then ⟨86950696619,2,[(0,1),(12,2),(38,1),(52,1),(101,1)]⟩ else ⟨99810171997,2,[(0,2),(1,1),(6,1),(53,1),(408,1)]⟩) else ⟨112646596429,2,[(0,2),(1,3),(18,1),(26,1),(333,1)]⟩)) else (bif Nat.ble i 548 then (bif Nat.ble i 547 then (bif Nat.ble i 546 then ⟨116683167431,19,[(0,1),(2,1),(319,1),(335,1)]⟩ else ⟨127522693159,6,[(0,1),(1,1),(3,2),(493,1)]⟩) else ⟨128653413121,17,[(0,8),(1,2),(2,1),(13,1),(352,1)]⟩) else (bif Nat.ble i 550 then (bif Nat.ble i 549 then ⟨129739194341,2,[(0,2),(2,1),(3,3),(446,1)]⟩ else ⟨140073863861,2,[(0,2),(2,1),(3,1),(503,1)]⟩) else ⟨156845134219,2,[(0,1),(1,1),(44,1),(482,1)]⟩))))

private def row23 (i : ℕ) : Row :=
  (bif Nat.ble i 563 then (bif Nat.ble i 557 then (bif Nat.ble i 554 then (bif Nat.ble i 553 then (bif Nat.ble i 552 then ⟨209908650307,2,[(0,1),(1,1),(16,1),(28,1),(140,1),(214,1)]⟩ else ⟨226877757059,2,[(0,1),(7,1),(524,1)]⟩) else ⟨239789806103,10,[(0,1),(3,1),(4,1),(28,1),(185,1),(215,1)]⟩) else (bif Nat.ble i 556 then (bif Nat.ble i 555 then ⟨262268397893,2,[(0,2),(259,1),(429,1)]⟩ else ⟨282429005041,23,[(0,4),(1,12),(2,1),(3,1),(5,1),(20,1)]⟩) else ⟨374857981681,11,[(0,4),(1,1),(2,1),(3,1),(5,1),(444,1)]⟩)) else (bif Nat.ble i 560 then (bif Nat.ble i 559 then (bif Nat.ble i 558 then ⟨391632555001,29,[(0,3),(1,1),(2,4),(160,1),(270,1)]⟩ else ⟨392038110671,7,[(0,1),(2,1),(21,1),(494,1)]⟩) else ⟨399478897991,17,[(0,1),(2,1),(13,1),(502,1)]⟩) else (bif Nat.ble i 562 then (bif Nat.ble i 561 then ⟨441019876741,2,[(0,2),(1,1),(2,1),(7,1),(18,1),(434,1)]⟩ else ⟨465092326319,11,[(0,1),(25,1),(181,1),(391,1)]⟩) else ⟨469188795247,3,[(0,1),(1,1),(9,1),(21,1),(462,1)]⟩))) else (bif Nat.ble i 569 then (bif Nat.ble i 566 then (bif Nat.ble i 565 then (bif Nat.ble i 564 then ⟨759432757177,5,[(0,3),(1,2),(6,1),(499,1)]⟩ else ⟨839163686147,2,[(0,1),(180,1),(484,1)]⟩) else ⟨1269699947531,2,[(0,1),(2,1),(3,1),(533,1)]⟩) else (bif Nat.ble i 568 then (bif Nat.ble i 567 then ⟨1534179947851,10,[(0,1),(1,3),(2,2),(4,1),(14,1),(26,1),(288,1)]⟩ else ⟨1815022056473,3,[(0,3),(553,1)]⟩) else ⟨2098303812601,11,[(0,3),(1,1),(2,2),(16,1),(469,1)]⟩)) else (bif Nat.ble i 572 then (bif Nat.ble i 571 then (bif Nat.ble i 570 then ⟨2549755542947,2,[(0,1),(24,1),(40,1),(162,1),(306,1)]⟩ else ⟨2663568851051,2,[(0,1),(2,2),(6,1),(8,1),(483,1)]⟩) else ⟨2688291691313,3,[(0,4),(12,1),(521,1)]⟩) else (bif Nat.ble i 574 then (bif Nat.ble i 573 then ⟨3981923614021,7,[(0,2),(1,1),(2,1),(4,2),(21,1),(435,1)]⟩ else ⟨4981237066807,5,[(0,1),(1,1),(3,1),(4,2),(5,1),(17,1),(56,1),(213,1)]⟩) else ⟨5091715167131,2,[(0,1),(2,1),(6,1),(8,1),(16,1),(451,1)]⟩))))

private def row24 (i : ℕ) : Row :=
  (bif Nat.ble i 587 then (bif Nat.ble i 581 then (bif Nat.ble i 578 then (bif Nat.ble i 577 then (bif Nat.ble i 576 then ⟨6273542442241,37,[(0,8),(1,2),(2,1),(8,1),(170,1),(253,1)]⟩ else ⟨12183990097481,3,[(0,3),(2,1),(375,1),(379,1)]⟩) else ⟨24472341743191,6,[(0,1),(1,1),(2,1),(4,1),(46,1),(134,1),(359,1)]⟩) else (bif Nat.ble i 580 then (bif Nat.ble i 579 then ⟨37644053098601,7,[(0,3),(2,2),(5,1),(269,1),(396,1)]⟩ else ⟨46856955592849,7,[(0,4),(1,1),(339,1),(433,1)]⟩) else ⟨61554625584169,23,[(0,3),(1,1),(387,1),(421,1)]⟩)) else (bif Nat.ble i 584 then (bif Nat.ble i 583 then (bif Nat.ble i 582 then ⟨70601370627701,2,[(0,2),(2,2),(4,1),(8,1),(11,1),(177,1),(300,1)]⟩ else ⟨110133112994711,7,[(0,1),(2,1),(5,1),(130,1),(500,1)]⟩) else ⟨122615954416367,5,[(0,1),(415,1),(457,1)]⟩) else (bif Nat.ble i 586 then (bif Nat.ble i 585 then ⟨135477418439917,2,[(0,2),(1,2),(3,2),(541,1)]⟩ else ⟨150224123975857,5,[(0,4),(1,1),(3,1),(9,1),(530,1)]⟩) else ⟨270547105429567,7,[(0,1),(1,3),(3,1),(9,1),(12,1),(61,1),(410,1)]⟩))) else (bif Nat.ble i 593 then (bif Nat.ble i 590 then (bif Nat.ble i 589 then (bif Nat.ble i 588 then ⟨301256733620657,3,[(0,4),(4,1),(8,1),(220,1),(440,1)]⟩ else ⟨311593540432981,6,[(0,2),(1,1),(2,1),(5,1),(560,1)]⟩) else ⟨368459311928441,6,[(0,3),(2,1),(19,1),(549,1)]⟩) else (bif Nat.ble i 592 then (bif Nat.ble i 591 then ⟨402546032623057,13,[(0,4),(1,1),(3,1),(38,1),(161,1),(422,1)]⟩ else ⟨419460012167869,2,[(0,2),(1,2),(3,1),(123,1),(216,1),(366,1)]⟩) else ⟨475384700124973,2,[(0,2),(1,2),(4,1),(10,1),(18,1),(56,1),(412,1)]⟩)) else (bif Nat.ble i 596 then (bif Nat.ble i 595 then (bif Nat.ble i 594 then ⟨560088668384411,2,[(0,1),(2,1),(4,1),(575,1)]⟩ else ⟨926510094425921,7,[(0,6),(2,1),(6,1),(12,1),(43,1),(449,1)]⟩) else ⟨989947158849251,2,[(0,1),(2,3),(3,1),(153,1),(490,1)]⟩) else (bif Nat.ble i 598 then (bif Nat.ble i 597 then ⟨1354201762851719,11,[(0,1),(4,1),(581,1)]⟩ else ⟨1611479891519807,7,[(0,1),(3,2),(4,1),(23,1),(315,1),(355,1)]⟩) else ⟨2515407025396723,2,[(0,1),(1,1),(437,1),(465,1)]⟩))))

private def row25 (i : ℕ) : Row :=
  (bif Nat.ble i 611 then (bif Nat.ble i 605 then (bif Nat.ble i 602 then (bif Nat.ble i 601 then (bif Nat.ble i 600 then ⟨2678679843416981,2,[(0,2),(2,1),(5,1),(6,1),(59,1),(513,1)]⟩ else ⟨3996503920492271,13,[(0,1),(2,1),(4,1),(6,1),(29,1),(51,1),(472,1)]⟩) else ⟨5357359686833963,2,[(0,1),(600,1)]⟩) else (bif Nat.ble i 604 then (bif Nat.ble i 603 then ⟨9460375336977361,14,[(0,4),(1,1),(2,1),(20,1),(293,1),(453,1)]⟩ else ⟨12557612956332313,10,[(0,3),(1,5),(4,1),(15,1),(18,1),(190,1),(311,1)]⟩) else ⟨15680976156013433,3,[(0,3),(4,1),(8,1),(117,1),(272,1),(382,1)]⟩)) else (bif Nat.ble i 608 then (bif Nat.ble i 607 then (bif Nat.ble i 606 then ⟨20633721467992697,3,[(0,3),(3,1),(590,1)]⟩ else ⟨36214795668330833,5,[(0,4),(3,1),(18,1),(291,1),(486,1)]⟩) else ⟨61557605176233223,5,[(0,1),(1,2),(3,1),(15,1),(21,1),(546,1)]⟩) else (bif Nat.ble i 610 then (bif Nat.ble i 609 then ⟨144542918285300809,11,[(0,3),(1,3),(3,1),(5,1),(7,1),(11,1),(80,1),(454,1)]⟩ else ⟨145171177264407947,2,[(0,1),(21,1),(271,1),(312,1),(399,1)]⟩) else ⟨150094634909578633,5,[(0,3),(1,18),(3,1),(5,1),(7,1),(11,1),(114,1)]⟩))) else (bif Nat.ble i 617 then (bif Nat.ble i 614 then (bif Nat.ble i 613 then (bif Nat.ble i 612 then ⟨302733747979631317,2,[(0,2),(1,2),(279,1),(563,1)]⟩ else ⟨380808546861411923,2,[(0,1),(4,1),(13,1),(591,1)]⟩) else ⟨489769993189671059,2,[(0,1),(16,1),(41,1),(204,1),(523,1)]⟩) else (bif Nat.ble i 616 then (bif Nat.ble i 615 then ⟨862970652262943171,2,[(0,1),(2,1),(6,1),(141,1),(405,1),(417,1)]⟩ else ⟨2461243576713869557,2,[(0,2),(1,2),(3,2),(6,2),(8,1),(552,1)]⟩) else ⟨2821964307371847613,2,[(0,2),(1,2),(5,1),(172,1),(572,1)]⟩)) else (bif Nat.ble i 620 then (bif Nat.ble i 619 then (bif Nat.ble i 618 then ⟨3747607031112307667,2,[(0,1),(15,1),(350,1),(550,1)]⟩ else ⟨6193396676178514477,2,[(0,2),(1,2),(14,1),(37,1),(244,1),(515,1)]⟩) else ⟨6962353413269964253,2,[(0,2),(1,1),(11,1),(605,1)]⟩) else (bif Nat.ble i 622 then (bif Nat.ble i 621 then ⟨10624346875389299603,2,[(0,1),(4,1),(11,1),(28,1),(133,1),(545,1)]⟩ else ⟨44626806191326911791,13,[(0,1),(2,1),(3,2),(6,1),(602,1)]⟩) else ⟨82064241848634269407,5,[(0,1),(1,1),(3,2),(5,1),(13,1),(90,1),(136,1),(174,1),(364,1)]⟩))))

private def row26 (i : ℕ) : Row :=
  (bif Nat.ble i 635 then (bif Nat.ble i 629 then (bif Nat.ble i 626 then (bif Nat.ble i 625 then (bif Nat.ble i 624 then ⟨179389574442728507719,7,[(0,1),(1,3),(3,1),(8,1),(606,1)]⟩ else ⟨8483579948526729282259,2,[(0,1),(1,1),(4,1),(64,1),(404,1),(555,1)]⟩) else ⟨12812432238302009985937,7,[(0,4),(1,3),(4,1),(6,1),(87,1),(589,1)]⟩) else (bif Nat.ble i 628 then (bif Nat.ble i 627 then ⟨27625994464180190188727,5,[(0,1),(3,1),(4,1),(624,1)]⟩ else ⟨37945127666529000523013,2,[(0,2),(4,1),(9,1),(52,1),(342,1),(360,1),(409,1)]⟩) else ⟨52370346649565455417091,2,[(0,1),(2,1),(8,1),(31,1),(109,1),(599,1)]⟩)) else (bif Nat.ble i 632 then (bif Nat.ble i 631 then (bif Nat.ble i 630 then ⟨105293313660391861035901,10,[(0,2),(1,1),(2,2),(4,1),(9,1),(13,1),(17,1),(592,1)]⟩ else ⟨397881837642577477902049,11,[(0,5),(1,2),(3,1),(6,1),(23,1),(77,1),(588,1)]⟩) else ⟨760498135401509315602139,2,[(0,1),(13,1),(75,1),(518,1),(526,1)]⟩) else (bif Nat.ble i 634 then (bif Nat.ble i 633 then ⟨950996059627210897943351,7,[(0,1),(2,2),(11,1),(22,1),(619,1)]⟩ else ⟨1108439448677340328268341,7,[(0,2),(1,1),(2,1),(16,1),(485,1),(568,1)]⟩) else ⟨3745603812007166116831643,2,[(0,1),(3,1),(5,1),(122,1),(222,1),(601,1)]⟩))) else (bif Nat.ble i 641 then (bif Nat.ble i 638 then (bif Nat.ble i 637 then (bif Nat.ble i 636 then ⟨5042939439565996049162197,2,[(0,2),(1,2),(6,1),(23,1),(470,1),(566,1)]⟩ else ⟨26273701844015319144827917,2,[(0,2),(1,1),(10,1),(23,1),(115,1),(345,1),(574,1)]⟩) else ⟨49689406026576989858275933,2,[(0,2),(1,1),(191,1),(477,1),(577,1)]⟩) else (bif Nat.ble i 640 then (bif Nat.ble i 639 then ⟨86630432442539925437931403,5,[(0,1),(1,2),(17,1),(497,1),(585,1)]⟩ else ⟨48845962828028421155731228333,2,[(0,2),(1,1),(3,2),(10,1),(24,1),(627,1)]⟩) else ⟨50316775668019759306202964023,7,[(0,1),(3,1),(25,1),(564,1),(580,1)]⟩)) else (bif Nat.ble i 644 then (bif Nat.ble i 643 then (bif Nat.ble i 642 then ⟨1716841910146256242328924544641,6,[(0,7),(2,1),(6,1),(12,1),(43,1),(449,1),(595,1)]⟩ else ⟨9224937607646071321168643513317,6,[(0,2),(1,5),(42,1),(638,1)]⟩) else ⟨78958087694609321439660131899631,11,[(0,1),(2,1),(7,1),(21,1),(232,1),(632,1)]⟩) else (bif Nat.ble i 646 then (bif Nat.ble i 645 then ⟨1999827817517387044561568810795329,7,[(0,6),(1,1),(12,1),(565,1),(612,1)]⟩ else ⟨3754733257489862401973357979128773,5,[(0,2),(1,1),(4,2),(17,1),(19,1),(90,1),(136,1),(516,1),(557,1)]⟩) else ⟨56285039669323321560176619734844253,2,[(0,2),(1,2),(436,1),(551,1),(597,1)]⟩))))

private def row27 (i : ℕ) : Row :=
  (bif Nat.ble i 651 then (bif Nat.ble i 649 then (bif Nat.ble i 648 then ⟨301515315752300874236564235591357673,7,[(0,3),(1,1),(30,1),(168,1),(432,1),(625,1)]⟩ else ⟨657890411545272648205502849240259841,7,[(0,8),(1,8),(2,1),(4,3),(66,1),(507,1),(584,1)]⟩) else (bif Nat.ble i 650 then ⟨48965028505045123993421250406516036571557,2,[(0,2),(1,2),(4,1),(27,1),(330,1),(643,1)]⟩ else ⟨526256453012063980796131127321354599535039,7,[(0,1),(4,1),(29,1),(201,1),(647,1)]⟩)) else (bif Nat.ble i 653 then (bif Nat.ble i 652 then ⟨6957596529882152968992225251835887181478451547013,2,[(0,2),(1,1),(3,1),(5,1),(26,1),(61,1),(100,1),(131,1),(163,1),(260,1),(301,1),(303,1),(481,1),(544,1)]⟩ else ⟨2,0,[]⟩) else (bif Nat.ble i 654 then ⟨2,0,[]⟩ else ⟨2,0,[]⟩)))

private def row (i : ℕ) : Row :=
  (bif Nat.ble i 23 then (row0 i) else (bif Nat.ble i 47 then (row1 i) else (bif Nat.ble i 71 then (row2 i) else (bif Nat.ble i 95 then (row3 i) else (bif Nat.ble i 119 then (row4 i) else (bif Nat.ble i 143 then (row5 i) else (bif Nat.ble i 167 then (row6 i) else (bif Nat.ble i 191 then (row7 i) else (bif Nat.ble i 215 then (row8 i) else (bif Nat.ble i 239 then (row9 i) else (bif Nat.ble i 263 then (row10 i) else (bif Nat.ble i 287 then (row11 i) else (bif Nat.ble i 311 then (row12 i) else (bif Nat.ble i 335 then (row13 i) else (bif Nat.ble i 359 then (row14 i) else (bif Nat.ble i 383 then (row15 i) else (bif Nat.ble i 407 then (row16 i) else (bif Nat.ble i 431 then (row17 i) else (bif Nat.ble i 455 then (row18 i) else (bif Nat.ble i 479 then (row19 i) else (bif Nat.ble i 503 then (row20 i) else (bif Nat.ble i 527 then (row21 i) else (bif Nat.ble i 551 then (row22 i) else (bif Nat.ble i 575 then (row23 i) else (bif Nat.ble i 599 then (row24 i) else (bif Nat.ble i 623 then (row25 i) else (bif Nat.ble i 647 then (row26 i) else (bif Nat.ble i 655 then (row27 i) else ⟨2,0,[]⟩))))))))))))))))))))))))))))

private def factors0 (i : ℕ) : List (ℕ × ℕ) × List (ℕ × ℕ) :=
  (bif Nat.ble i 11 then (bif Nat.ble i 5 then (bif Nat.ble i 2 then (bif Nat.ble i 1 then (bif Nat.ble i 0 then ([],[]) else ([(0,2)],[])) else ([(5,1)],[])) else (bif Nat.ble i 4 then (bif Nat.ble i 3 then ([(0,3)],[(2,1)]) else ([(4,2)],[])) else ([(0,2)],[(5,1),(3,1)]))) else (bif Nat.ble i 8 then (bif Nat.ble i 7 then (bif Nat.ble i 6 then ([(136,1)],[]) else ([(0,4)],[(12,1),(2,1)])) else ([(114,1)],[(5,1)])) else (bif Nat.ble i 10 then (bif Nat.ble i 9 then ([(4,2),(17,1)],[(0,2)]) else ([(205,1)],[(8,1)])) else ([(0,3),(3,1)],[(20,1),(5,1),(2,1)])))) else (bif Nat.ble i 17 then (bif Nat.ble i 14 then (bif Nat.ble i 13 then (bif Nat.ble i 12 then ([(390,1)],[]) else ([(0,2)],[(136,1),(90,1)])) else ([(4,2)],[(213,1),(5,1)])) else (bif Nat.ble i 16 then (bif Nat.ble i 15 then ([(0,5),(2,1)],[(43,1),(12,1),(6,1)]) else ([(303,1)],[(163,1)])) else ([(0,2),(7,1),(3,1)],[(114,1),(11,1),(5,1)]))) else (bif Nat.ble i 20 then (bif Nat.ble i 19 then (bif Nat.ble i 18 then ([(363,1)],[(155,1)]) else ([(0,3),(139,1),(17,1)],[(4,2),(2,2)])) else ([(364,1),(5,1)],[(136,1)])) else (bif Nat.ble i 22 then (bif Nat.ble i 21 then ([(0,2),(18,1)],[(205,1),(105,1),(8,1)]) else ([(504,1)],[(14,1)])) else ([(0,4),(5,1),(2,1)],[(226,1),(20,1),(12,1),(3,1)])))))

private def factors1 (i : ℕ) : List (ℕ × ℕ) × List (ℕ × ℕ) :=
  (bif Nat.ble i 35 then (bif Nat.ble i 29 then (bif Nat.ble i 26 then (bif Nat.ble i 25 then (bif Nat.ble i 24 then ([(4,2)],[(368,1),(243,1)]) else ([(0,2)],[(390,1),(370,1)])) else ([(241,1),(77,1),(5,1)],[(114,1),(28,1)])) else (bif Nat.ble i 28 then (bif Nat.ble i 27 then ([(0,3),(90,1),(2,1)],[(275,1),(136,1),(9,1)]) else ([(447,1),(16,1)],[(299,1)])) else ([(4,2),(213,1),(17,1),(5,1)],[(0,2),(56,1),(10,1),(3,1)]))) else (bif Nat.ble i 32 then (bif Nat.ble i 31 then (bif Nat.ble i 30 then ([(425,1),(108,1)],[(326,1)]) else ([(0,6),(6,1)],[(449,1),(43,1),(12,1),(2,1)])) else ([(514,1),(8,1)],[(205,1),(5,1)])) else (bif Nat.ble i 34 then (bif Nat.ble i 33 then ([(0,2),(131,1),(26,1)],[(303,1),(163,1),(61,1)]) else ([(4,2),(19,1)],[(516,1),(136,1)])) else ([(0,3),(20,1),(7,1),(3,1)],[(376,1),(114,1),(11,1),(5,1),(2,1)])))) else (bif Nat.ble i 41 then (bif Nat.ble i 38 then (bif Nat.ble i 37 then (bif Nat.ble i 36 then ([(532,1)],[(439,1)]) else ([(0,2),(182,1)],[(363,1),(325,1),(155,1)])) else ([(5,2),(227,1)],[(390,1),(233,1),(63,1)])) else (bif Nat.ble i 40 then (bif Nat.ble i 39 then ([(0,4),(464,1),(17,1)],[(4,2),(2,2),(139,1),(12,1)]) else ([(543,1),(22,1)],[(416,1)])) else ([(3,2),(364,1),(136,1),(13,1)],[(0,2),(174,1),(90,1),(5,1)]))) else (bif Nat.ble i 44 then (bif Nat.ble i 43 then (bif Nat.ble i 42 then ([(613,1)],[(76,1)]) else ([(0,3),(205,1),(18,1),(2,1)],[(378,1),(217,1),(105,1),(8,1)])) else ([(4,2),(157,1),(41,1)],[(392,1),(213,1),(114,1),(5,1)])) else (bif Nat.ble i 46 then (bif Nat.ble i 45 then ([(0,2),(14,1)],[(535,1),(504,1)]) else ([(476,1),(289,1)],[(428,1),(143,1)])) else ([(0,5),(43,1),(20,1),(6,1),(3,1)],[(226,1),(115,1),(95,1),(24,1),(12,1),(5,1),(2,1)])))))

private def factors2 (i : ℕ) : List (ℕ × ℕ) × List (ℕ × ℕ) :=
  (bif Nat.ble i 59 then (bif Nat.ble i 53 then (bif Nat.ble i 50 then (bif Nat.ble i 49 then (bif Nat.ble i 48 then ([(331,1),(242,1),(136,1)],[(309,1),(208,1),(84,1)]) else ([(4,2),(455,1),(243,1),(17,1)],[(0,2),(368,1),(35,1)])) else ([(544,1),(260,1),(5,1)],[(303,1),(163,1)])) else (bif Nat.ble i 52 then (bif Nat.ble i 51 then ([(0,3),(370,1),(2,1)],[(522,1),(390,1),(15,1)]) else ([(618,1),(27,1)],[(292,1)])) else ([(0,2),(241,1),(77,1),(11,1),(5,1)],[(284,1),(282,1),(114,1),(28,1),(7,1),(3,1)]))) else (bif Nat.ble i 56 then (bif Nat.ble i 55 then (bif Nat.ble i 54 then ([(4,3),(146,1)],[(594,1),(205,1),(8,1)]) else ([(0,4),(136,1),(12,1),(2,1)],[(383,1),(372,1),(275,1),(90,1),(9,1)])) else ([(510,1),(349,1),(49,1)],[(363,1),(155,1),(5,1)])) else (bif Nat.ble i 58 then (bif Nat.ble i 57 then ([(0,2),(299,1),(89,1)],[(447,1),(431,1),(223,1),(16,1)]) else ([(614,1)],[(528,1)])) else ([(0,3),(466,1),(213,1),(56,1),(17,1),(5,1)],[(4,2),(2,2),(139,1),(20,1),(10,1),(3,1)])))) else (bif Nat.ble i 65 then (bif Nat.ble i 62 then (bif Nat.ble i 61 then (bif Nat.ble i 60 then ([(630,1)],[(380,1)]) else ([(0,2),(326,1),(108,1)],[(534,1),(425,1),(230,1)])) else ([(609,1),(136,1),(5,1)],[(364,1),(114,1)])) else (bif Nat.ble i 64 then (bif Nat.ble i 63 then ([(0,7),(12,1),(2,1)],[(595,1),(449,1),(43,1),(6,1)]) else ([(4,2),(390,1)],[(583,1),(420,1),(31,1)])) else ([(0,2),(294,1),(105,1),(8,1),(3,1)],[(514,1),(340,1),(205,1),(18,1),(5,1)]))) else (bif Nat.ble i 68 then (bif Nat.ble i 67 then (bif Nat.ble i 66 then ([(593,1),(346,1)],[(561,1)]) else ([(0,3),(303,1),(131,1),(26,1)],[(509,1),(393,1),(163,1),(61,1),(2,1)])) else ([(616,1),(57,1),(5,1)],[(504,1),(14,1)])) else (bif Nat.ble i 70 then (bif Nat.ble i 69 then ([(4,2),(557,1),(136,1),(19,1)],[(0,2),(516,1),(90,1),(17,1)]) else ([(646,1)],[])) else ([(0,4),(114,1),(12,1),(7,1),(3,1)],[(556,1),(376,1),(226,1),(20,1),(11,1),(5,1),(2,1)])))))

private def factors3 (i : ℕ) : List (ℕ × ℕ) × List (ℕ × ℕ) :=
  (bif Nat.ble i 83 then (bif Nat.ble i 77 then (bif Nat.ble i 74 then (bif Nat.ble i 73 then (bif Nat.ble i 72 then ([(603,1),(285,1)],[(531,1),(255,1)]) else ([(0,2),(439,1),(281,1)],[(532,1),(468,1),(328,1)])) else ([(4,2),(246,1),(213,1),(5,1)],[(569,1),(368,1),(243,1),(98,1)])) else (bif Nat.ble i 76 then (bif Nat.ble i 75 then ([(0,3),(363,1),(182,1),(2,1)],[(537,1),(430,1),(325,1),(155,1)]) else ([(542,1),(467,1),(136,1)],[(525,1),(205,1),(8,1)])) else ([(5,2),(390,1),(249,1),(227,1),(63,1),(21,1)],[(0,2),(370,1),(233,1),(184,1),(36,1),(3,1)]))) else (bif Nat.ble i 80 then (bif Nat.ble i 79 then (bif Nat.ble i 78 then ([(610,1),(492,1)],[(559,1)]) else ([(0,5),(548,1),(266,1),(43,1),(12,1)],[(4,2),(2,2),(464,1),(139,1),(17,1),(6,1)])) else ([(604,1),(241,1),(114,1),(28,1)],[(400,1),(206,1),(77,1),(5,1)])) else (bif Nat.ble i 82 then (bif Nat.ble i 81 then ([(0,2),(416,1),(22,1)],[(587,1),(543,1),(302,1)]) else ([(633,1),(257,1)],[(505,1),(38,1)])) else ([(0,3),(364,1),(183,1),(136,1),(20,1),(9,1),(2,1)],[(3,2),(479,1),(275,1),(174,1),(90,1),(13,1),(5,1)])))) else (bif Nat.ble i 89 then (bif Nat.ble i 86 then (bif Nat.ble i 85 then (bif Nat.ble i 84 then ([(4,2),(303,1)],[(615,1),(571,1),(163,1)]) else ([(0,2),(76,1)],[(623,1),(613,1)])) else ([(586,1),(447,1),(299,1),(5,1)],[(460,1),(318,1),(16,1)])) else (bif Nat.ble i 88 then (bif Nat.ble i 87 then ([(0,4),(217,1),(105,1),(18,1),(8,1)],[(539,1),(414,1),(378,1),(205,1),(23,1),(12,1),(2,1)]) else ([(636,1),(40,1)],[(598,1)])) else ([(4,2),(392,1),(367,1),(157,1),(56,1),(17,1),(10,1),(5,1)],[(0,2),(389,1),(213,1),(114,1),(41,1),(11,1),(7,1),(3,1)]))) else (bif Nat.ble i 92 then (bif Nat.ble i 91 then (bif Nat.ble i 90 then ([(635,1),(390,1)],[(520,1),(136,1)]) else ([(0,3),(504,1),(14,1)],[(582,1),(535,1),(438,1),(2,1)])) else ([(637,1),(326,1),(108,1)],[(425,1),(138,1),(5,1)])) else (bif Nat.ble i 94 then (bif Nat.ble i 93 then ([(0,2),(428,1),(289,1),(143,1)],[(567,1),(476,1),(351,1),(277,1)]) else ([(4,2),(155,1)],[(644,1),(363,1),(42,1)])) else ([(0,6),(226,1),(95,1),(24,1),(12,1),(5,1),(2,1)],[(536,1),(449,1),(321,1),(115,1),(43,1),(20,1),(6,1),(3,1)])))))

private def factors4 (i : ℕ) : List (ℕ × ℕ) × List (ℕ × ℕ) :=
  (bif Nat.ble i 107 then (bif Nat.ble i 101 then (bif Nat.ble i 98 then (bif Nat.ble i 97 then (bif Nat.ble i 96 then ([(640,1),(320,1)],[(570,1)]) else ([(0,2),(331,1),(242,1),(136,1),(84,1)],[(547,1),(501,1),(309,1),(208,1),(90,1)])) else ([(626,1),(418,1),(114,1),(5,1)],[(514,1),(205,1),(8,1)])) else (bif Nat.ble i 100 then (bif Nat.ble i 99 then ([(2,3),(4,2),(369,1),(243,1),(35,1),(17,1)],[(0,3),(540,1),(455,1),(368,1),(139,1),(25,1)]) else ([(641,1),(461,1)],[(562,1)])) else ([(0,2),(303,1),(260,1),(131,1),(61,1),(5,1)],[(544,1),(481,1),(301,1),(163,1),(100,1),(26,1),(3,1)]))) else (bif Nat.ble i 104 then (bif Nat.ble i 103 then (bif Nat.ble i 102 then ([(652,1)],[]) else ([(0,4),(390,1),(15,1),(2,1)],[(579,1),(522,1),(512,1),(370,1),(12,1)])) else ([(4,2),(406,1),(225,1),(136,1),(19,1)],[(538,1),(516,1),(364,1),(213,1),(75,1),(5,1)])) else (bif Nat.ble i 106 then (bif Nat.ble i 105 then ([(0,2),(473,1),(27,1)],[(618,1),(608,1),(292,1)]) else ([(650,1),(308,1)],[(347,1)])) else ([(0,3),(284,1),(241,1),(77,1),(20,1),(7,1),(3,1)],[(611,1),(376,1),(282,1),(114,1),(28,1),(11,1),(5,1),(2,1)])))) else (bif Nat.ble i 113 then (bif Nat.ble i 110 then (bif Nat.ble i 109 then (bif Nat.ble i 108 then ([(621,1),(519,1),(135,1)],[(554,1),(495,1)]) else ([(4,3),(578,1),(205,1),(105,1),(17,1)],[(0,2),(594,1),(385,1),(146,1),(18,1),(8,1)])) else ([(620,1),(480,1),(439,1)],[(532,1),(445,1),(5,1)])) else (bif Nat.ble i 112 then (bif Nat.ble i 111 then ([(0,5),(283,1),(136,1),(43,1),(12,1),(6,1)],[(607,1),(383,1),(372,1),(275,1),(90,1),(29,1),(9,1),(2,1)]) else ([(651,1),(154,1)],[(413,1),(48,1)])) else ([(0,2),(363,1),(325,1),(186,1),(155,1),(5,1)],[(510,1),(506,1),(349,1),(313,1),(182,1),(49,1),(3,1)]))) else (bif Nat.ble i 116 then (bif Nat.ble i 115 then (bif Nat.ble i 114 then ([(4,2),(504,1),(14,1)],[(629,1),(576,1),(411,1)]) else ([(0,3),(431,1),(258,1),(89,1),(2,1)],[(628,1),(447,1),(299,1),(223,1),(16,1)])) else ([(5,2),(424,1),(233,1),(114,1)],[(617,1),(511,1),(390,1),(227,1),(63,1)])) else (bif Nat.ble i 118 then (bif Nat.ble i 117 then ([(0,2),(528,1)],[(634,1),(614,1),(189,1)]) else ([(631,1),(303,1),(136,1)],[(622,1),(163,1),(50,1)])) else ([(0,4),(466,1),(459,1),(226,1),(139,1),(51,1),(17,1),(10,1),(3,1)],[(4,2),(2,2),(464,1),(356,1),(213,1),(56,1),(20,1),(12,1),(5,1)])))))

private def factors5 (i : ℕ) : List (ℕ × ℕ) × List (ℕ × ℕ) :=
  (bif Nat.ble i 123 then (bif Nat.ble i 121 then (bif Nat.ble i 120 then ([(649,1),(256,1),(8,1)],[(573,1),(205,1)]) else ([(0,2),(380,1)],[(639,1),(630,1),(68,1)])) else (bif Nat.ble i 122 then ([(645,1),(416,1),(22,1)],[(543,1),(310,1),(5,1)]) else ([(0,3),(517,1),(425,1),(230,1),(2,1)],[(534,1),(527,1),(508,1),(326,1),(108,1)]))) else (bif Nat.ble i 125 then (bif Nat.ble i 124 then ([(4,2),(529,1),(368,1),(52,1)],[(596,1),(558,1),(491,1),(243,1)]) else ([(3,2),(609,1),(364,1),(174,1),(125,1),(90,1),(13,1),(7,1)],[(0,2),(496,1),(177,1),(136,1),(114,1),(30,1),(11,1),(5,1)])) else (bif Nat.ble i 126 then ([(648,1),(448,1),(221,1)],[(471,1),(386,1)]) else ([(0,8),(12,1),(2,1)],[(642,1),(595,1),(449,1),(43,1),(6,1)]))))

private def factors (i : ℕ) : List (ℕ × ℕ) × List (ℕ × ℕ) :=
  (bif Nat.ble i 23 then (factors0 i) else (bif Nat.ble i 47 then (factors1 i) else (bif Nat.ble i 71 then (factors2 i) else (bif Nat.ble i 95 then (factors3 i) else (bif Nat.ble i 119 then (factors4 i) else (bif Nat.ble i 127 then (factors5 i) else ([],[])))))))

private def each (n : ℕ) (p : ℕ → Bool) : Bool := (List.range n).all p

private theorem each_of {n i : ℕ} {p : ℕ → Bool} (h : each n p = true) (hi : i < n) : p i = true :=
  List.all_eq_true.mp h i (List.mem_range.mpr hi)

private def indexed (ps : List (ℕ × ℕ)) : List (ℕ × ℕ) :=
  ps.map fun (i,k) => ((row i).value,k)

private def checkedLength (i : ℕ) : Bool :=
  let (a,b) := factors i
  let (ps,qs) := (indexed a,indexed b)
  let r := (3^(i+1)-1)/2
  ((a ++ b).all (fun s => decide (s.1 < 653)) &&
    (factorProduct ps * factorProduct qs == r)) &&
    candidates r (excludes r) ps qs

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem P0 : each 16 (fun i => decide (valid row (0+i))) = true := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem P1 : each 16 (fun i => decide (valid row (16+i))) = true := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem P2 : each 16 (fun i => decide (valid row (32+i))) = true := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem P3 : each 16 (fun i => decide (valid row (48+i))) = true := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem P4 : each 16 (fun i => decide (valid row (64+i))) = true := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem P5 : each 16 (fun i => decide (valid row (80+i))) = true := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem P6 : each 16 (fun i => decide (valid row (96+i))) = true := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem P7 : each 16 (fun i => decide (valid row (112+i))) = true := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem P8 : each 16 (fun i => decide (valid row (128+i))) = true := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem P9 : each 16 (fun i => decide (valid row (144+i))) = true := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem P10 : each 16 (fun i => decide (valid row (160+i))) = true := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem P11 : each 16 (fun i => decide (valid row (176+i))) = true := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem P12 : each 16 (fun i => decide (valid row (192+i))) = true := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem P13 : each 16 (fun i => decide (valid row (208+i))) = true := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem P14 : each 16 (fun i => decide (valid row (224+i))) = true := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem P15 : each 16 (fun i => decide (valid row (240+i))) = true := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem P16 : each 16 (fun i => decide (valid row (256+i))) = true := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem P17 : each 16 (fun i => decide (valid row (272+i))) = true := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem P18 : each 16 (fun i => decide (valid row (288+i))) = true := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem P19 : each 16 (fun i => decide (valid row (304+i))) = true := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem P20 : each 16 (fun i => decide (valid row (320+i))) = true := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem P21 : each 16 (fun i => decide (valid row (336+i))) = true := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem P22 : each 16 (fun i => decide (valid row (352+i))) = true := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem P23 : each 16 (fun i => decide (valid row (368+i))) = true := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem P24 : each 16 (fun i => decide (valid row (384+i))) = true := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem P25 : each 16 (fun i => decide (valid row (400+i))) = true := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem P26 : each 16 (fun i => decide (valid row (416+i))) = true := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem P27 : each 16 (fun i => decide (valid row (432+i))) = true := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem P28 : each 16 (fun i => decide (valid row (448+i))) = true := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem P29 : each 16 (fun i => decide (valid row (464+i))) = true := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem P30 : each 16 (fun i => decide (valid row (480+i))) = true := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem P31 : each 16 (fun i => decide (valid row (496+i))) = true := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem P32 : each 16 (fun i => decide (valid row (512+i))) = true := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem P33 : each 16 (fun i => decide (valid row (528+i))) = true := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem P34 : each 16 (fun i => decide (valid row (544+i))) = true := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem P35 : each 16 (fun i => decide (valid row (560+i))) = true := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem P36 : each 16 (fun i => decide (valid row (576+i))) = true := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem P37 : each 16 (fun i => decide (valid row (592+i))) = true := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem P38 : each 16 (fun i => decide (valid row (608+i))) = true := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem P39 : each 16 (fun i => decide (valid row (624+i))) = true := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem P40 : each 16 (fun i => decide (valid row (640+i))) = true := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem D0 : each 8 (fun i => checkedLength (0+i)) = true := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem D1 : each 8 (fun i => checkedLength (8+i)) = true := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem D2 : each 8 (fun i => checkedLength (16+i)) = true := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem D3 : each 8 (fun i => checkedLength (24+i)) = true := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem D4 : each 8 (fun i => checkedLength (32+i)) = true := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem D5 : each 8 (fun i => checkedLength (40+i)) = true := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem D6 : each 8 (fun i => checkedLength (48+i)) = true := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem D7 : each 8 (fun i => checkedLength (56+i)) = true := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem D8 : each 8 (fun i => checkedLength (64+i)) = true := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem D9 : each 8 (fun i => checkedLength (72+i)) = true := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem D10 : each 8 (fun i => checkedLength (80+i)) = true := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem D11 : each 8 (fun i => checkedLength (88+i)) = true := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem D12 : each 8 (fun i => checkedLength (96+i)) = true := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem D13 : each 8 (fun i => checkedLength (104+i)) = true := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem D14 : each 8 (fun i => checkedLength (112+i)) = true := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem D15 : each 8 (fun i => checkedLength (120+i)) = true := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem allPrimes (i : ℕ) (hi : i < 653) : decide (valid row i) = true := by
  let q := i/16
  let r := i%16
  have hq : q < 41 := by dsimp [q]; omega
  have hr : r < 16 := Nat.mod_lt _ (by decide)
  have hk : i = 16*q+r := by dsimp [q,r]; omega
  have block : each 16 (fun j => decide (valid row (16*q+j))) = true := by
    interval_cases q
    · exact P0
    · exact P1
    · exact P2
    · exact P3
    · exact P4
    · exact P5
    · exact P6
    · exact P7
    · exact P8
    · exact P9
    · exact P10
    · exact P11
    · exact P12
    · exact P13
    · exact P14
    · exact P15
    · exact P16
    · exact P17
    · exact P18
    · exact P19
    · exact P20
    · exact P21
    · exact P22
    · exact P23
    · exact P24
    · exact P25
    · exact P26
    · exact P27
    · exact P28
    · exact P29
    · exact P30
    · exact P31
    · exact P32
    · exact P33
    · exact P34
    · exact P35
    · exact P36
    · exact P37
    · exact P38
    · exact P39
    · exact P40
  have result := each_of (p := fun j => decide (valid row (16*q+j))) block hr
  rw [hk]
  exact result

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem allLengths (i : ℕ) (hi : i < 128) : checkedLength i = true := by
  let q := i/8
  let r := i%8
  have hq : q < 16 := by dsimp [q]; omega
  have hr : r < 8 := Nat.mod_lt _ (by decide)
  have hk : i = 8*q+r := by dsimp [q,r]; omega
  have block : each 8 (fun j => checkedLength (8*q+j)) = true := by
    interval_cases q
    · exact D0
    · exact D1
    · exact D2
    · exact D3
    · exact D4
    · exact D5
    · exact D6
    · exact D7
    · exact D8
    · exact D9
    · exact D10
    · exact D11
    · exact D12
    · exact D13
    · exact D14
    · exact D15
  have result := each_of (p := fun j => checkedLength (8*q+j)) block hr
  rw [hk]
  exact result

private theorem factor_primes (rows : ∀ i : ℕ, i < 653 → decide (valid row i) = true)
    {a b : List (ℕ × ℕ)} (h : (a++b).all (fun s => decide (s.1 < 653)) = true) :
    (∀ s ∈ indexed a, s.1.Prime) ∧ (∀ s ∈ indexed b, s.1.Prime) := by
  have primeRows : ∀ i < 653, (row i).value.Prime :=
    every_prime row 653 (fun i hi => of_decide_eq_true (rows i hi))
  have primePart (ps : List (ℕ × ℕ)) (hp : ∀ s ∈ ps, s ∈ a ++ b) :
      ∀ s ∈ indexed ps, s.1.Prime := by
    intro s hs
    obtain ⟨⟨i,k⟩,hk,rfl⟩ := List.mem_map.mp hs
    exact primeRows i (of_decide_eq_true (List.all_eq_true.mp h (i,k) (hp _ hk)))
  exact ⟨primePart a (fun _ hs => List.mem_append_left _ hs),
         primePart b (fun _ hs => List.mem_append_right _ hs)⟩

private theorem factor_exclusion (rows : ∀ i : ℕ, i < 653 → decide (valid row i) = true)
    {i d e x : ℕ} (h : checkedLength i = true)
    (hd : 0 < d) (hde : d*e=(3^(i+1)-1)/2)
    (hcomp : 4*d<e ∧ e<6*d) (he : e = d+2*x) :
    2 ∈ Nat.digits 3 (x*x) := by
  let r := (3^(i+1)-1)/2
  change d*e=r at hde
  have hh : ((factors i).1 ++ (factors i).2).all (fun s => decide (s.1 < 653)) = true := by
    have hh := h
    unfold checkedLength at hh
    exact (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hh).1).1
  have fact := factor_primes rows hh
  have hpair : factorProduct (indexed (factors i).1) * factorProduct (indexed (factors i).2) = r :=
    beq_iff_eq.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp h).1).2
  have hcheck := (Bool.and_eq_true_iff.mp h).2
  have hu : 4*d^2 < r := by
    have mul := Nat.mul_lt_mul_of_pos_left hcomp.1 hd
    rw [← hde]
    nlinarith
  have hl : r < 6*d^2 := by
    have mul := Nat.mul_lt_mul_of_pos_left hcomp.2 hd
    rw [← hde]
    nlinarith
  exact excludes_sound hd hde he (candidates_sound fact.1 fact.2 hpair ⟨e,hde.symm⟩ hu hl hcheck)

private theorem shift_twice (ds : List ℕ) :
    2*Nat.ofDigits 3 (ds.map (fun d => d+1)) + 1 =
    2*Nat.ofDigits 3 ds + 3^ds.length := by
  induction ds with
  | nil => decide
  | cons d ds ih =>
    simp only [List.map_cons, Nat.ofDigits_cons, List.length_cons, pow_succ]
    omega

private theorem digit_bound (ds : List ℕ) (h : ∀ d ∈ ds, d ≤ 1) :
    2*Nat.ofDigits 3 ds < 3^ds.length := by
  induction ds with
  | nil => decide
  | cons d ds ih =>
    have ha := h d (by simp)
    have hb := ih (fun t ht => h t (List.mem_cons_of_mem _ ht))
    simp only [Nat.ofDigits_cons, List.length_cons, pow_succ]
    omega

private theorem comparable_factors {d e x : ℕ} (hd : 0 < d) (he : e = d+2*x)
    (hu : x*x ≤ d*e) (hl : 2*(d*e) < 3*(x*x)) : 4*d < e ∧ e < 6*d := by
  zify at *
  constructor
  · by_contra! h
    have hs : (0:ℤ) ≤ 3*d-2*x := by omega
    have ht : (0:ℤ) ≤ 6*x+d := by positivity
    rw [he] at hl
    nlinarith [mul_nonneg hs ht, sq_nonneg (d:ℤ)]
  · by_contra! h
    have hs : (0:ℤ) ≤ 2*x-5*d := by omega
    have ht : (0:ℤ) ≤ 2*x+d := by positivity
    rw [he] at hu
    nlinarith [mul_nonneg hs ht, mul_pos hd hd]

theorem finite_range (rows : ∀ i : ℕ, i < 653 → decide (valid row i) = true)
    (lengths : ∀ i : ℕ, i < 128 → checkedLength i = true) :
    OMA.R_oeis_a402459_R1.H1 := by
  intro m hm hlen hs hdig ht
  obtain ⟨x,hx⟩ := hs
  obtain ⟨y,hy⟩ := ht
  let L := (Nat.digits 3 m).length
  have hpos : 0 < L := List.length_pos_iff.mpr (Nat.digits_ne_nil_iff_ne_zero.mpr hm.ne')
  have hnext : L-1+1 = L := by omega
  have hindex : L-1 < 128 := by change L ≤ 128 at hlen; omega
  have shift := shift_twice (Nat.digits 3 m)
  rw [Nat.ofDigits_digits,hy] at shift
  change 2*(y*y)+1 = 2*m+3^L at shift
  have low := Nat.base_pow_length_digits_le 3 m (by decide) hm.ne'
  change 3^L ≤ 3*m at low
  have high := digit_bound (Nat.digits 3 m) (by
    intro i hi
    have ha := Nat.digits_lt_base (by decide : 1 < 3) hi
    have hb : i ≠ 2 := fun h => hdig (h ▸ hi)
    omega)
  rw [Nat.ofDigits_digits] at high
  change 2*m < 3^L at high
  have hpow : 1 < 3^L := Nat.one_lt_pow hpos.ne' (by decide)
  have hxy : x < y := by
    by_contra! h
    have := Nat.mul_self_le_mul_self h
    rw [hx] at shift
    omega
  let d := y-x
  let e := y+x
  have hd : 0 < d := Nat.sub_pos_of_lt hxy
  have heq : d+x=y := Nat.sub_add_cancel hxy.le
  have he : e=d+2*x := by dsimp [e]; omega
  have hw : 2*(d*e)+1 = 3^L := by
    rw [hx, ← heq] at shift
    rw [he]
    nlinarith [shift]
  have hequal : d*e = (3^(L-1+1)-1)/2 := by rw [hnext]; omega
  have hr := comparable_factors hd he (by rw [← hx]; omega) (by rw [← hx]; omega)
  exact hdig (hx ▸ factor_exclusion rows (lengths _ hindex) hd hequal hr he)

end TernaryFactorPairs

theorem OMA.solution : OMA.R_oeis_a402459_R1.H1 := by
  exact TernaryFactorPairs.finite_range TernaryFactorPairs.allPrimes TernaryFactorPairs.allLengths