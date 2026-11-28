import OMAStatements.S_oeis_a321334
import Mathlib

namespace SquarefreeSums

def qualifies (n : ℕ) : Prop :=
  2 ≤ n ∧ ∀ s : ℕ, n ≤ 2*s → s < n → Squarefree s → Squarefree (n-s)

def known : List ℕ := [2,3,4,5,6,7,8,12,13,16,36]

end SquarefreeSums

/-! The progression count is the method of Mincu and Panaitopol, Lemma 5
and Theorem 6 of *On some properties of squarefree and squareful numbers*
(2006), https://ssmr.ro/bulletin/pdf/1/panamincu.pdf. We apply it to the
upper half of the interval, as required by Frank M Jackson's OEIS A321334,
and use an elementary telescoping estimate for the reciprocal squares. -/

namespace SquarefreeSums
open Finset

private theorem div_step (K j : ℕ) :
    K / (j+3)^2 + K / (j+3) ≤ K / (j+2) := by
  apply (Nat.le_div_iff_mul_le (by omega)).mpr
  have h := Nat.div_mul_le_self (K/(j+3)) (j+3)
  rw [Nat.div_div_eq_div_mul, ←sq] at h
  have g := Nat.div_mul_le_self K (j+3)
  calc
    _ = K/(j+3)^2*(j+2) + K/(j+3)*(j+2) := by rw [Nat.add_mul]
    _ ≤ K/(j+3)^2*(j+3) + K/(j+3)*(j+2) := by gcongr; omega
    _ ≤ K/(j+3) + K/(j+3)*(j+2) := Nat.add_le_add_right h _
    _ = K/(j+3)*(j+3) := by ring
    _ ≤ K := g

private theorem tail (K t : ℕ) :
    (∑ i ∈ range t, K/(i+3)^2) + K/(t+2) ≤ K/2 := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [sum_range_succ]
    change (∑ i ∈ range t, K/(i+3)^2) + K/(t+3)^2 + K/(t+3) ≤ K/2
    rw [Nat.add_assoc]
    exact (Nat.add_le_add_left (div_step K t) _).trans ih

private theorem budget (K R : ℕ) :
    (∑ i ∈ range R, (K/(i+2)^2+1)) ≤ K/4+K/2+R := by
  simp only [sum_add_distrib, sum_const, card_range, smul_eq_mul, mul_one]
  rcases R with _ | t
  · simp
  · rw [Finset.sum_range_succ']
    have h := (Nat.le_add_right _ _).trans (tail K t)
    change (∑ i ∈ range t, K/(i+3)^2) + K/4 + (t+1) ≤ K/4+K/2+(t+1)
    omega

private def hit (n p K d : ℕ) : Finset ℕ :=
  if d.Prime ∧ d ≠ p then
    (range K).filter (fun j => p^2*(j+1) ≡ n [MOD d^2])
  else ∅

private theorem hits_le (n p K d : ℕ) (hp : p.Prime) :
    (hit n p K d).card ≤ K/d^2+1 := by
  by_cases hd : d.Prime ∧ d ≠ p
  · have hc := Nat.coprime_pow_primes 2 2 hd.1 hp hd.2
    have hh : (hit n p K d).card ≤ (range (K/d^2+1)).card := by
      apply card_le_card_of_injOn (fun j : ℕ => (j+1)/d^2)
      · intro j hj
        have hj' : j < K ∧ p^2*(j+1) ≡ n [MOD d^2] := by simpa [hit,hd] using hj
        exact mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right hj'.1))
      · intro a ha b hb he
        have ha' : a < K ∧ p^2*(a+1) ≡ n [MOD d^2] := by simpa [hit,hd] using ha
        have hb' : b < K ∧ p^2*(b+1) ≡ n [MOD d^2] := by simpa [hit,hd] using hb
        have hmod : a+1 ≡ b+1 [MOD d^2] :=
          Nat.ModEq.cancel_left_of_coprime hc (ha'.2.trans hb'.2.symm)
        have ha'' := Nat.div_add_mod (a+1) (d^2)
        have hb'' := Nat.div_add_mod (b+1) (d^2)
        change (a+1)/d^2 = (b+1)/d^2 at he
        change (a+1)%d^2 = (b+1)%d^2 at hmod
        rw [he,hmod] at ha''
        omega
    simpa using hh
  · simp [hit,hd]

/-- A long interval in this progression contains a squarefree integer. -/
theorem sieve_bound {n p : ℕ} (hp : p.Prime) (hpn : ¬p^2 ∣ n)
    (hbad : ∀ s : ℕ, n ≤ 2*s → s < n → p^2 ∣ n-s → ¬ Squarefree s) :
    n < 100*p^4 := by
  let K := n/(2*p^2)
  let R := n.sqrt
  have hpp := hp.pos
  have key : range K ⊆ (range R).biUnion (fun i => hit n p K (i+2)) := by
    intro j hj
    have hj' := mem_range.mp hj
    have hp2 : 0 < 2*p^2 := by positivity
    have hb : (j+1)*(2*p^2) ≤ n := (Nat.le_div_iff_mul_le hp2).mp (by omega : j+1 ≤ K)
    let m := p^2*(j+1)
    have hm : 0 < m := Nat.mul_pos (pow_pos hp.pos _) (by omega)
    have hm' : 2*m ≤ n := by dsimp [m]; nlinarith only [hb]
    have hsub : n-(n-m)=m := by omega
    have hns := hbad (n-m) (by omega) (by omega) (by rw [hsub]; exact dvd_mul_right ..)
    obtain ⟨d,hd,hdvd⟩ : ∃ d : ℕ, ∃ _ : d.Prime, d*d ∣ n-m := by
      simpa only [Nat.squarefree_iff_prime_squarefree, not_forall, Classical.not_imp, not_not] using hns
    have hmpos : 0 < n-m := by omega
    have dlow := hd.two_le
    have dupper : d ≤ R := Nat.le_sqrt.mpr ((Nat.le_of_dvd hmpos hdvd).trans (Nat.sub_le ..))
    have hdmod : m ≡ n [MOD d^2] := (Nat.modEq_iff_dvd' (by omega : m ≤ n)).mpr (by simpa [sq] using hdvd)
    have hne : d ≠ p := by
      rintro rfl
      apply hpn
      rw [←Nat.modEq_zero_iff_dvd]
      exact hdmod.symm.trans ((dvd_mul_right (d^2) (j+1)).modEq_zero_nat)
    refine mem_biUnion.mpr ⟨d-2,mem_range.mpr (by omega),?_⟩
    rw [show d-2+2=d by omega,hit,if_pos ⟨hd,hne⟩]
    exact mem_filter.mpr ⟨hj,hdmod⟩
  have count : K ≤ K/4+K/2+R := calc
    K = (range K).card := (card_range _).symm
    _ ≤ _ := card_le_card key
    _ ≤ ∑ i ∈ range R, (hit n p K (i+2)).card := card_biUnion_le
    _ ≤ _ := sum_le_sum (fun i _ => hits_le n p K (i+2) hp)
    _ ≤ _ := budget K R
  have hK : K ≤ 4*R := by omega
  have hp2 : 0 < 2*p^2 := by positivity
  have nlt : n < (K+1)*(2*p^2) := by
    apply (Nat.div_lt_iff_lt_mul hp2).mp
    exact Nat.lt_succ_self K
  by_contra! high
  have hR : 10*p^2 ≤ R := Nat.le_sqrt.mpr (by nlinarith only [high])
  have hlo := Nat.sqrt_le n
  change R*R ≤ n at hlo
  have hp' := hp.two_le
  nlinarith [Nat.mul_le_mul_right (2*p^2) hK, Nat.mul_le_mul_right R hR,
    Nat.mul_le_mul_left (p^2) hR, sq_nonneg (p:ℤ)]

end SquarefreeSums

namespace SquarefreeSums
open Finset

private theorem primorial_lower {m : ℕ} (hm : 12 ≤ m) :
    10*(m+1)^2 ≤ primorial m := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    by_cases hb : m < 24
    · by_cases h12 : m = 12
      · subst m
        decide +kernel
      · have hl : 10*24^2 ≤ primorial 13 := by decide +kernel
        exact (Nat.mul_le_mul_left 10 (Nat.pow_le_pow_left (by omega : m+1 ≤ 24) 2)).trans
          (hl.trans (primorial_mono (by omega)))
    · let t := m/2
      have ht : 12 ≤ t := by dsimp [t]; omega
      have htm : t < m := by dsimp [t]; omega
      obtain ⟨p,hp,htp,hpm⟩ := Nat.exists_prime_lt_and_le_two_mul t (by omega)
      have hpm' : p ≤ m := by dsimp [t] at hpm; omega
      have hn : p ∉ Nat.primesLE t := fun h => (not_le_of_gt htp) (Nat.mem_primesLE.mp h).1
      have hd : p*primorial t ∣ primorial m := by
        rw [primorial_eq_prod_primesLE, primorial_eq_prod_primesLE,
          ← Finset.prod_insert (f := fun x : ℕ => x) hn]
        apply Finset.prod_dvd_prod_of_subset
        intro q hq
        rcases mem_insert.mp hq with rfl | hq
        · exact Nat.mem_primesLE.mpr ⟨hpm',hp⟩
        · exact Nat.mem_primesLE.mpr ⟨(Nat.mem_primesLE.mp hq).1.trans htm.le,(Nat.mem_primesLE.mp hq).2⟩
      have hsize : m+1 ≤ 2*(t+1) := by dsimp [t]; omega
      calc 10*(m+1)^2 ≤ 10*(2*(t+1))^2 := Nat.mul_le_mul_left 10 (Nat.pow_le_pow_left hsize 2)
           _ = 4*(10*(t+1)^2) := by ring
           _ ≤ p*primorial t := Nat.mul_le_mul (by omega) (ih t htm ht)
           _ ≤ primorial m := Nat.le_of_dvd (primorial_pos m) hd

theorem finite_shape {n : ℕ} (hn : qualifies n) :
    ∃ p ∈ ([2,3,5,7,11] : List ℕ), ¬p^2 ∣ n ∧
      (primorial (p-1))^2 ∣ n ∧ n < 100*p^4 := by
  classical
  have hpos : 0 < n := lt_of_lt_of_le (by decide : 0 < 2) hn.1
  have hex : ∃ p : ℕ, p.Prime ∧ ¬p^2 ∣ n := by
    obtain ⟨p,hle,hp⟩ := Nat.exists_infinite_primes (n+1)
    exact ⟨p,hp,fun h => by have := Nat.le_of_dvd hpos h; nlinarith [hp.two_le]⟩
  let p := Nat.find hex
  have hp : p.Prime ∧ ¬p^2 ∣ n := Nat.find_spec hex
  have hcap : n < 100*p^4 := sieve_bound hp.1 hp.2 (by
    intro s hlo hhi hd hsq
    exact Nat.squarefree_iff_prime_squarefree.mp (hn.2 s hlo hhi hsq) p hp.1 (by simpa [sq] using hd))
  have hprod : (primorial (p-1))^2 ∣ n := by
    rw [primorial_eq_prod_primesLE, ← Finset.prod_pow]
    apply Finset.prod_dvd_of_isRelPrime
    · intro u hu v hv huv
      exact Nat.coprime_iff_isRelPrime.mp (Nat.coprime_pow_primes 2 2
        (Nat.mem_primesLE.mp hu).2 (Nat.mem_primesLE.mp hv).2 huv)
    · intro u hu
      obtain ⟨hle,hpr⟩ := Nat.mem_primesLE.mp hu
      by_contra h
      have := Nat.find_min' hex ⟨hpr,h⟩
      change p ≤ u at this
      have := hp.1.two_le
      omega
  have hp13 : p < 13 := by
    by_contra! hlarge
    have hl := primorial_lower (m := p-1) (by omega)
    rw [show p-1+1=p by omega] at hl
    have h' := (Nat.pow_le_pow_left hl 2).trans (Nat.le_of_dvd hpos hprod)
    nlinarith only [h',hcap]
  have hsmall : ∀ a : Fin 13, a.val.Prime → a.val ∈ ([2,3,5,7,11] : List ℕ) := by decide +kernel
  exact ⟨p,hsmall ⟨p,hp13⟩ hp.1,hp.2,hprod,hcap⟩

end SquarefreeSums

namespace SquarefreeSums

private def offsets (p : ℕ) : List ℕ :=
  match p with
  | 2 => [4,8,12,18]
  | 3 => [9,18,25]
  | 5 => [25,50,75]
  | 7 => [98,49]
  | _ => [121]

private def witness (n d : ℕ) : Bool :=
  decide (0 < d ∧ 2*d ≤ n ∧ Squarefree (n-d) ∧ ¬Squarefree d)

private theorem witness_excludes {n d : ℕ} (hn : qualifies n) (hw : witness n d = true) :
    False := by
  rcases of_decide_eq_true hw with ⟨hd,hbound,hs,ht⟩
  apply ht
  have h := hn.2 (n-d) (by omega) (by omega) hs
  rwa [show n-(n-d) = d by omega] at h

private def stride (p : ℕ) := (primorial (p-1))^2

private def checkBucket (p : ℕ) : Bool :=
  (List.range ((100*p^4-1) / stride p + 1)).all fun j =>
    let n := stride p * j
    decide (n < 2 ∨ p^2 ∣ n ∨ n ∈ known) || (offsets p).any (witness n)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem bucket2 : checkBucket 2 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem bucket3 : checkBucket 3 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem bucket5 : checkBucket 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem bucket7 : checkBucket 7 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem bucket11 : checkBucket 11 = true := by decide +kernel

theorem mem_known_of_shape {n : ℕ} (hn : qualifies n)
    (hshape : ∃ p ∈ ([2,3,5,7,11] : List ℕ),
      ¬ p^2 ∣ n ∧ (primorial (p-1))^2 ∣ n ∧ n < 100*p^4) : n ∈ known := by
  obtain ⟨p,hp,hmissing,hdiv,hcap⟩ := hshape
  have checked : checkBucket p = true := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl|rfl|rfl|rfl|rfl
    exacts [bucket2, bucket3, bucket5, bucket7, bucket11]
  change stride p ∣ n at hdiv
  obtain ⟨j,hj⟩ := hdiv
  have hpos : 0 < stride p := pow_pos (primorial_pos _) _
  have hmem : j ∈ List.range ((100*p^4-1) / stride p + 1) := by
    apply List.mem_range.mpr
    apply Nat.lt_succ_of_le
    apply (Nat.le_div_iff_mul_le hpos).mpr
    rw [Nat.mul_comm, ←hj]
    omega
  have h := List.all_eq_true.mp checked j hmem
  change (decide (stride p*j < 2 ∨ p^2 ∣ stride p*j ∨ stride p*j ∈ known) ||
      (offsets p).any (witness (stride p*j))) = true at h
  rw [←hj] at h
  simp only [Bool.or_eq_true] at h
  rcases h with h|h
  · rcases of_decide_eq_true h with h|h|h
    · exact False.elim ((Nat.not_lt_of_ge hn.1) h)
    · exact (hmissing h).elim
    · exact h
  · obtain ⟨d,_,hd⟩ := List.any_eq_true.mp h
    exact (witness_excludes hn hd).elim

private def checkTerm (n : ℕ) : Bool :=
  decide (2 ≤ n) && (List.range n).all fun s =>
    decide (n ≤ 2*s → Squarefree s → Squarefree (n-s))

private theorem checked_terms : known.all checkTerm = true := by decide +kernel

theorem qualifies_of_known {n : ℕ} (hn : n ∈ known) : qualifies n := by
  have h := List.all_eq_true.mp checked_terms n hn
  simp only [checkTerm, Bool.and_eq_true] at h
  refine ⟨of_decide_eq_true h.1, fun s h2 hs hsf => ?_⟩
  exact of_decide_eq_true (List.all_eq_true.mp h.2 s (List.mem_range.mpr hs)) h2 hsf

end SquarefreeSums

namespace SquarefreeSums

private def hasUpper (n : ℕ) : Bool :=
  (List.range n).any fun s => decide (n ≤ 2*s ∧ Squarefree s)

private theorem upper_for_known {n : ℕ} (hn : n ∈ known) :
    ∃ s, OMA.S_oeis_a321334.upperSquarefree n s := by
  have audited : known.all hasUpper = true := by decide +kernel
  obtain ⟨s,hs,h⟩ := List.any_eq_true.mp (List.all_eq_true.mp audited n hn)
  have ht : n ≤ 2*s ∧ Squarefree s := of_decide_eq_true h
  exact ⟨s,ht.1,List.mem_range.mp hs,ht.2⟩

end SquarefreeSums

theorem OMA.solution : type_of% @OMA.S_oeis_a321334.main := by
  intro n
  constructor
  · intro h
    obtain ⟨s,hs,hsn,_⟩ := h.1
    have hq : SquarefreeSums.qualifies n :=
      ⟨by omega, fun s hu hs hf => h.2 s ⟨hu,hs,hf⟩⟩
    exact SquarefreeSums.mem_known_of_shape hq (SquarefreeSums.finite_shape hq)
  · intro h
    exact ⟨SquarefreeSums.upper_for_known h, fun s hs =>
      (SquarefreeSums.qualifies_of_known h).2 s hs.1 hs.2.1 hs.2.2⟩
