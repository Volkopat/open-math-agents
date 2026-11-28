import OMAReductions.R_OeisA247824_conjecture_2_R1

/-! Legendre's recursion and Meissel's semiprime correction for two exact prime ranks.
The recursion and its divisibility argument adapt Daniel Veljjanoski’s Palomar proof
as formalized in OeisA100475.conjecture by @rleshner (Apache-2.0).
https://github.com/veljjanoski/oeis100475-palomar/tree/0968200356e449a24a023264821d4ea966091cf0
-/
open Finset
namespace OMA.R_OeisA247824_conjecture_2_R1_H1_R1

lemma legendre {ps : List ℕ} (hsort : ps.Pairwise (· > ·)) (hprime : ∀ p ∈ ps, Nat.Prime p)
    (hcomp : ∀ p ∈ ps, ∀ q, Nat.Prime q → q < p → q ∈ ps) (x : ℕ) :
    ps.foldr (fun (p : ℕ) (f : ℕ → ℕ) (t : ℕ) => if t < p then (if t = 0 then 0 else 1) else f t - f (t / p)) id x =
      ((Icc 1 x).filter (fun n => ∀ p ∈ ps, ¬ p ∣ n)).card := by
  let sieveSet (ps : List ℕ) (x : ℕ) := (Icc 1 x).filter (fun n => ∀ p ∈ ps, ¬ p ∣ n)
  have mem_sieveSet {ps : List ℕ} {x n : ℕ} :
      n ∈ sieveSet ps x ↔ (1 ≤ n ∧ n ≤ x) ∧ ∀ p ∈ ps, ¬ p ∣ n := by
    simp [sieveSet]
  
  have sieveSet_nil (x : ℕ) : sieveSet [] x = Finset.Icc 1 x := by
    ext n; simp [sieveSet]
  
  /- Legendre's recursion step. -/
  have card_sieveSet_cons {p : ℕ} {ps : List ℕ} (hp : p.Prime) (hps : ∀ q ∈ ps, q.Prime ∧ q ≠ p)
      (x : ℕ) :
      (sieveSet (p :: ps) x).card = (sieveSet ps x).card - (sieveSet ps (x / p)).card := by
    have hsplit : sieveSet (p :: ps) x = (sieveSet ps x).filter (fun n => ¬ p ∣ n) := by
      ext n; simp [sieveSet, List.mem_cons]; tauto
    have himage : (sieveSet ps x).filter (fun n => p ∣ n) = (sieveSet ps (x / p)).image (p * ·) := by
      ext n
      simp only [Finset.mem_filter, mem_sieveSet, Finset.mem_image]
      constructor
      · rintro ⟨⟨⟨h1, hx⟩, hq⟩, ⟨m, rfl⟩⟩
        refine ⟨m, ⟨⟨?_, ?_⟩, ?_⟩, rfl⟩
        · rcases Nat.eq_zero_or_pos m with rfl | hm
          · simp at h1
          · exact hm
        · exact (Nat.le_div_iff_mul_le hp.pos).2 (by rw [mul_comm]; exact hx)
        · intro q hq' hdvd
          exact hq q hq' (dvd_mul_of_dvd_right hdvd p)
      · rintro ⟨m, ⟨⟨h1, hm⟩, hq⟩, rfl⟩
        refine ⟨⟨⟨?_, ?_⟩, ?_⟩, dvd_mul_right p m⟩
        · exact Nat.one_le_iff_ne_zero.2 (mul_ne_zero hp.ne_zero (by omega))
        · rw [mul_comm]; exact (Nat.le_div_iff_mul_le hp.pos).1 hm
        · intro q hq' hdvd
          obtain ⟨hqp, hqne⟩ := hps q hq'
          rcases (Nat.Prime.dvd_mul hqp).1 hdvd with h | h
          · exact hqne ((Nat.prime_dvd_prime_iff_eq hqp hp).1 h)
          · exact hq q hq' h
    have hcard := Finset.card_filter_add_card_filter_not (s := sieveSet ps x) (fun n => p ∣ n)
    rw [himage, Finset.card_image_of_injective _ (mul_right_injective₀ hp.ne_zero)] at hcard
    rw [hsplit]
    omega
  
  /- Pruning: below `p`, only `1` survives the sieve by all primes less than `p`. -/
  have card_sieveSet_of_lt {p : ℕ} {ps : List ℕ} (hps : ∀ q ∈ ps, q.Prime)
      (hcomplete : ∀ q, q.Prime → q < p → q ∈ ps) {x : ℕ} (hx : x < p) :
      (sieveSet (p :: ps) x).card = if x = 0 then 0 else 1 := by
    split_ifs with h0
    · subst h0; simp [sieveSet]
    · have : sieveSet (p :: ps) x = {1} := by
        ext n
        simp only [mem_sieveSet, Finset.mem_singleton, List.mem_cons, forall_eq_or_imp]
        constructor
        · rintro ⟨⟨h1, hnx⟩, -, hq⟩
          by_contra hne
          have hn1 : n ≠ 1 := hne
          have hmf := Nat.minFac_prime hn1
          have hlt : Nat.minFac n < p := lt_of_le_of_lt (Nat.minFac_le (by omega)) (by omega)
          exact hq _ (hcomplete _ hmf hlt) (Nat.minFac_dvd n)
        · rintro rfl
          refine ⟨⟨le_rfl, by omega⟩, ?_, ?_⟩
          · intro h
            have := Nat.le_of_dvd one_pos h
            omega
          · intro q hq; exact Nat.Prime.not_dvd_one (hps q hq)
      rw [this, Finset.card_singleton]
  
  change _ = (sieveSet ps x).card
  induction ps generalizing x with
  | nil => simp [sieveSet_nil]
  | cons p ps ih =>
    obtain ⟨hgt,hs⟩ := List.pairwise_cons.mp hsort
    have hp := hprime p List.mem_cons_self
    have hq (q) (hq : q ∈ ps) := hprime q (List.mem_cons_of_mem p hq)
    have hc (q) (h : q.Prime) (lt : q < p) : q ∈ ps := by
      rcases List.mem_cons.mp (hcomp p List.mem_cons_self q h lt) with eq | hm
      · omega
      · exact hm
    have closed (r) (hr : r ∈ ps) (q) (h : q.Prime) (lt : q < r) := hc q h (lt.trans (hgt r hr))
    simp only [List.foldr_cons]
    split_ifs with lt zero
    · rw [card_sieveSet_of_lt hq hc lt, if_pos zero]
    · rw [card_sieveSet_of_lt hq hc lt, if_neg zero]
    · rw [card_sieveSet_cons hp (fun q h => ⟨hq q h, (hgt q h).ne⟩), ih hs hq closed, ih hs hq closed]

lemma legendre_range (y x : ℕ) :
    (((List.range (y+1)).filter (fun p => decide p.Prime)).reverse.foldr
      (fun (p : ℕ) (f : ℕ → ℕ) (t : ℕ) => if t < p then (if t = 0 then 0 else 1) else f t - f (t / p)) id x) =
    ((Icc 1 x).filter (fun n => ∀ p ∈ Nat.primesLE y, ¬ p ∣ n)).card := by
  let ps := ((List.range (y+1)).filter (fun p => decide p.Prime)).reverse
  have mem (p : ℕ) : p ∈ ps ↔ p ∈ Nat.primesLE y := by simp [ps, Nat.mem_primesLE]
  have hsort : ps.Pairwise (· > ·) := by
    apply List.pairwise_reverse.mpr
    exact List.pairwise_lt_range.filter _
  have e := legendre hsort (fun p hp => Nat.prime_of_mem_primesLE ((mem p).mp hp))
    (fun p hp q hq hlt => (mem q).mpr (Nat.mem_primesLE.mpr ⟨hlt.le.trans (Nat.le_of_mem_primesLE ((mem p).mp hp)), hq⟩)) x
  convert e using 1
  congr 1
  ext n
  simp only [mem_filter, mem_Icc, mem]

/-- At a cube-root cutoff, every surviving composite has exactly two prime factors,
with multiplicity. Sorting the factors makes this parametrization injective. -/
lemma meissel {x y z : ℕ} (hx : 1 ≤ x) (hy : y ≤ x) (cube : x < (y+1)^3)
    (sq : x < (z+1)^2) :
    ((Icc 1 x).filter (fun n => ∀ p ∈ Nat.primesLE y, ¬ p ∣ n)).card +
      (Nat.primesLE y).card = 1 + (Nat.primesLE x).card +
      ∑ p ∈ (Nat.primesLE z).filter (y < ·), ((Nat.primesLE (x/p)).filter (p ≤ ·)).card := by
  classical
  let R := (Icc 1 x).filter (fun n => ∀ p ∈ Nat.primesLE y, ¬ p ∣ n)
  let T := R.filter (fun n => n ≠ 1 ∧ ¬n.Prime)
  let B := (Nat.primesLE z).filter (y < ·)
  let Q (p : ℕ) := (Nat.primesLE (x/p)).filter (p ≤ ·)
  have memR (n) : n ∈ R ↔ (1 ≤ n ∧ n ≤ x) ∧ ∀ p ∈ Nat.primesLE y, ¬ p ∣ n := by simp [R]
  have memT (n) : n ∈ T ↔ n ∈ R ∧ n ≠ 1 ∧ ¬n.Prime := by simp [T]
  have memB (p) : p ∈ B ↔ (p ≤ z ∧ p.Prime) ∧ y < p := by simp [B, Nat.mem_primesLE]
  have memQ (p q) : q ∈ Q p ↔ (q ≤ x/p ∧ q.Prime) ∧ p ≤ q := by simp [Q, Nat.mem_primesLE]
  have least {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (pq : p ≤ q) : (p*q).minFac = p := by
    have hn : p*q ≠ 1 := by have := hp.two_le; have := hq.two_le; nlinarith
    have hm := Nat.minFac_prime hn
    apply le_antisymm (Nat.minFac_le_of_dvd hp.two_le (dvd_mul_right p q))
    rcases hm.dvd_mul.mp (Nat.minFac_dvd (p*q)) with a | b
    · exact ((Nat.prime_dvd_prime_iff_eq hm hp).mp a).symm.le
    · exact pq.trans_eq ((Nat.prime_dvd_prime_iff_eq hm hq).mp b).symm
  have pair : (B.sigma Q).card = T.card := by
    apply card_bij (fun a _ => a.1 * a.2)
    · intro ⟨p,q⟩ h
      obtain ⟨hb,hq⟩ := mem_sigma.mp h
      obtain ⟨⟨_,pp⟩,yp⟩ := (memB p).mp hb
      obtain ⟨⟨ub,qp⟩,ord⟩ := (memQ p q).mp hq
      have pos := Nat.mul_pos pp.pos qp.pos
      have bound : p*q ≤ x := by simpa [mul_comm] using (Nat.le_div_iff_mul_le pp.pos).mp ub
      apply (memT _).mpr
      refine ⟨(memR _).mpr ⟨⟨pos,bound⟩, ?_⟩, ?_, ?_⟩
      · intro r hr hd
        obtain ⟨ry,rp⟩ := Nat.mem_primesLE.mp hr
        rcases rp.dvd_mul.mp hd with a | b
        · have := (Nat.prime_dvd_prime_iff_eq rp pp).mp a; omega
        · have := (Nat.prime_dvd_prime_iff_eq rp qp).mp b; omega
      · have := pp.two_le; have := qp.two_le; dsimp; nlinarith
      · intro prime
        have := (Nat.prime_dvd_prime_iff_eq pp prime).mp (dvd_mul_right p q)
        have := pp.two_le; have := qp.two_le; dsimp at *; nlinarith
    · intro ⟨p,q⟩ ha ⟨r,s⟩ hb eq
      obtain ⟨ha,hq⟩ := mem_sigma.mp ha
      obtain ⟨hb,hs⟩ := mem_sigma.mp hb
      obtain ⟨⟨_,pp⟩,_⟩ := (memB p).mp ha
      obtain ⟨⟨_,rp⟩,_⟩ := (memB r).mp hb
      obtain ⟨⟨_,qp⟩,a⟩ := (memQ p q).mp hq
      obtain ⟨⟨_,sp⟩,b⟩ := (memQ r s).mp hs
      change p*q=r*s at eq
      have same := (least pp qp a).symm.trans ((congrArg Nat.minFac eq).trans (least rp sp b))
      subst r
      obtain rfl := Nat.eq_of_mul_eq_mul_left pp.pos eq
      rfl
    · intro n hn
      obtain ⟨hr,ne,np⟩ := (memT n).mp hn
      obtain ⟨⟨pos,bound⟩,rough⟩ := (memR n).mp hr
      let p := n.minFac
      let q := n / p
      have pp : p.Prime := Nat.minFac_prime ne
      have product : p*q = n := Nat.mul_div_cancel' (Nat.minFac_dvd n)
      have ord : p ≤ q := Nat.minFac_le_div pos np
      have yp : y < p := by
        by_contra! h
        exact rough _ (Nat.mem_primesLE.mpr ⟨h,pp⟩) (Nat.minFac_dvd n)
      have qp : q.Prime := by
        by_contra hq
        have qpos : 0 < q := pp.pos.trans_le ord
        have qq := Nat.minFac_sq_le_self qpos hq
        have qne : q ≠ 1 := by have := pp.two_le; omega
        have rprime := Nat.minFac_prime qne
        have yr : y < q.minFac := by
          by_contra! h
          apply rough _ (Nat.mem_primesLE.mpr ⟨h,rprime⟩)
          rw [← product]
          exact dvd_mul_of_dvd_right (Nat.minFac_dvd q) _
        have b := Nat.mul_le_mul (show y+1 ≤ p by omega)
          (le_trans (Nat.pow_le_pow_left (show y+1 ≤ q.minFac by omega) 2) qq)
        nlinarith only [product,b,bound,cube]
      have pz : p ≤ z := by
        by_contra! h
        have a := Nat.mul_le_mul (show z+1≤p by omega) (show z+1≤q by omega)
        nlinarith only [product,a,sq,bound]
      refine ⟨⟨p,q⟩, mem_sigma.mpr ⟨(memB _).mpr ⟨⟨pz,pp⟩,yp⟩,
        (memQ _ _).mpr ⟨⟨(Nat.le_div_iff_mul_le pp.pos).mpr ?_,qp⟩,ord⟩⟩, product⟩
      simpa [mul_comm,product] using (product.le.trans bound)
  have primepart : R.filter Nat.Prime = (Nat.primesLE x).filter (fun n => ¬ n ≤ y) := by
    ext n
    simp only [mem_filter,memR,Nat.mem_primesLE]
    constructor
    · rintro ⟨⟨⟨_,ub⟩,r⟩,np⟩
      exact ⟨⟨ub,np⟩,fun h => r n ⟨h,np⟩ (dvd_refl n)⟩
    · rintro ⟨⟨ub,np⟩,gt⟩
      refine ⟨⟨⟨np.one_le,ub⟩,fun p hp hd => ?_⟩, np⟩
      exact gt (((Nat.prime_dvd_prime_iff_eq hp.2 np).mp hd) ▸ hp.1)
  have low : (Nat.primesLE x).filter (· ≤ y) = Nat.primesLE y := by
    ext n
    simp only [mem_filter,Nat.mem_primesLE]
    exact ⟨fun h => ⟨h.2,h.1.2⟩, fun h => ⟨⟨h.1.trans hy,h.2⟩,h.1⟩⟩
  have other : R.filter (fun n => ¬n.Prime) = insert 1 T := by
    ext n
    simp only [mem_filter,mem_insert,memT]
    constructor
    · rintro ⟨hr,hp⟩; by_cases h : n=1
      · exact Or.inl h
      · exact Or.inr ⟨hr,h,hp⟩
    · rintro (rfl | ⟨hr,_,hp⟩)
      · exact ⟨(memR _).mpr ⟨⟨le_rfl,hx⟩,fun p hp => (Nat.prime_of_mem_primesLE hp).not_dvd_one⟩,Nat.not_prime_one⟩
      · exact ⟨hr,hp⟩
  have one : 1 ∉ T := fun h => ((memT 1).mp h).2.1 rfl
  have v := card_filter_add_card_filter_not (s:=R) Nat.Prime
  have w := card_filter_add_card_filter_not (s:=Nat.primesLE x) (· ≤ y)
  rw [primepart,other,card_insert_of_notMem one] at v
  rw [low] at w
  rw [card_sigma] at pair
  change R.card + _ = 1 + _ + ∑ p ∈ B, (Q p).card
  omega

/-- Interval subtraction evaluates each row of the semiprime count using only ordinary prime counts. -/
lemma prime_row {p t : ℕ} (pos : 0 < p) (le : p ≤ t) :
    ((Nat.primesLE t).filter (p ≤ ·)).card = Nat.primeCounting t - Nat.primeCounting (p-1) := by
  have eq : (Nat.primesLE t).filter (fun n => ¬p ≤ n) = Nat.primesLE (p-1) := by
    ext n
    simp only [mem_filter,Nat.mem_primesLE]
    constructor
    · rintro ⟨⟨_,pr⟩,lt⟩; exact ⟨by omega,pr⟩
    · rintro ⟨ub,pr⟩; exact ⟨⟨by omega,pr⟩,by omega⟩
  have h := card_filter_add_card_filter_not (s:=Nat.primesLE t) (p ≤ ·)
  rw [eq, Nat.primesLE_card_eq_primeCounting, Nat.primesLE_card_eq_primeCounting] at h
  omega

lemma rank_of_parts {x y z a b r : ℕ} (hx : 1 ≤ x) (hy : y ≤ x) (cube : x < (y+1)^3)
    (sq : x < (z+1)^2) (zs : z*z ≤ x)
    (sieved : (((List.range (y+1)).filter (fun p => decide p.Prime)).reverse.foldr
      (fun (p : ℕ) (f : ℕ → ℕ) (t : ℕ) => if t < p then (if t = 0 then 0 else 1) else f t - f (t / p)) id x) +
      (Nat.primesLE y).card = a)
    (pairs : (∑ p ∈ (Nat.primesLE z).filter (y < ·), (Nat.primeCounting (x/p) - Nat.primeCounting (p-1))) = b)
    (result : 1+r+b = a) : Nat.primeCounting x = r := by
  have e := meissel hx hy cube sq
  have row (p : ℕ) (hp : p ∈ (Nat.primesLE z).filter (y < ·)) := by
    have bound := Nat.le_of_mem_primesLE (mem_filter.mp hp).1
    have pos := (Nat.prime_of_mem_primesLE (mem_filter.mp hp).1).pos
    exact prime_row pos ((Nat.le_div_iff_mul_le pos).mpr ((Nat.mul_le_mul bound bound).trans zs))
  rw [legendre_range] at sieved
  rw [sum_congr rfl row, pairs, Nat.primesLE_card_eq_primeCounting x] at e
  omega

lemma empty_correction (x y : ℕ) :
    (∑ p ∈ (Nat.primesLE y).filter (y < ·), (Nat.primeCounting (x/p) - Nat.primeCounting (p-1))) = 0 := by
  have b : (Nat.primesLE y).filter (y < ·) = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro n hn
    exact (not_lt_of_ge (Nat.le_of_mem_primesLE (mem_filter.mp hn).1)) (mem_filter.mp hn).2
  rw [b,sum_empty]

/-- The smaller instance needs no semiprime correction at the square-root cutoff. -/
def H1 : Prop :=
  ((List.range (4568+1)).filter (fun p => decide p.Prime)).reverse.foldr (fun (p : ℕ) (f : ℕ → ℕ) (t : ℕ) =>
    if t < p then (if t = 0 then 0 else 1) else f t - f (t / p)) id 20868472 +
    (Nat.primesLE 4568).card = 1322164

/-- The partial sieve stops after the primes at most the cube root. -/
def H2 : Prop :=
  ((List.range (43399+1)).filter (fun p => decide p.Prime)).reverse.foldr (fun (p : ℕ) (f : ℕ → ℕ) (t : ℕ) =>
    if t < p then (if t = 0 then 0 else 1) else f t - f (t / p)) id 81744924555066 +
    (Nat.primesLE 43399).card = 4327835360391

/-- Count products p*q with p ≤ q and both primes greater than the cube root. -/
def H3 : Prop :=
  (∑ p ∈ (Nat.primesLE 9041289).filter (43399 < ·),
    (Nat.primeCounting (81744924555066/p) - Nat.primeCounting (p-1))) = 1690902959215

theorem main : H1 → H2 → H3 → OMA.R_OeisA247824_conjecture_2_R1.H1 := by
  intro hs hl hc
  unfold H1 at hs
  unfold H2 at hl
  unfold H3 at hc
  change Nat.primeCounting 20868472 = 1322163 ∧ Nat.primeCounting 81744924555066 = 2636932401175
  exact ⟨rank_of_parts (x:=20868472) (y:=4568) (z:=4568) (a:=1322164) (b:=0)
      (by decide) (by decide) (by decide) (by decide) (by decide) hs (empty_correction 20868472 4568) (by decide),
    rank_of_parts (x:=81744924555066) (y:=43399) (z:=9041289) (a:=4327835360391) (b:=1690902959215)
      (by decide) (by decide) (by decide) (by decide) (by decide) hl hc (by decide)⟩

end OMA.R_OeisA247824_conjecture_2_R1_H1_R1
