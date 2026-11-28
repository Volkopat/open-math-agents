import OMAStatements.S_oeis_a316553
import Mathlib

open OMA.S_oeis_a316553 Matrix Finset
open scoped MatrixGroups

/- A determinant-one matrix squares to the identity precisely when it equals its adjugate. -/
private abbrev SL2Triples (R : Type*) [CommRing R] :=
  {t : R × R × R // 2*t.2.1 = 0 ∧ 2*t.2.2 = 0 ∧ t.1^2-t.2.1*t.2.2 = 1}

private lemma sl2_involution_iff {R : Type*} [CommRing R] (g : SL(2,R)) :
    g^2 = 1 ↔ g 0 0 = g 1 1 ∧ 2 * g 0 1 = 0 ∧ 2 * g 1 0 = 0 := by
  rw [sq, mul_eq_one_iff_eq_inv, Matrix.SpecialLinearGroup.SL2_inv_expl]
  constructor
  · intro h
    have hh := (Matrix.SpecialLinearGroup.ext_iff _ _).mp h
    have h01 : g 0 1 = -(g 0 1) := hh 0 1
    have h10 : g 1 0 = -(g 1 0) := hh 1 0
    exact ⟨hh 0 0, by linear_combination h01, by linear_combination h10⟩
  · rintro ⟨hd, h01, h10⟩
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j
    · exact hd
    · change g 0 1 = -(g 0 1)
      linear_combination h01
    · change g 1 0 = -(g 1 0)
      linear_combination h10
    · exact hd.symm

private def sl2_triple_equiv (R : Type*) [CommRing R] :
    {g : SL(2,R) // g^2 = 1} ≃ SL2Triples R where
  toFun x := by
    let g := x.val
    refine ⟨(g 0 0, g 0 1, g 1 0), ?_⟩
    obtain ⟨hd,h01,h10⟩ := (sl2_involution_iff g).mp x.property
    refine ⟨h01,h10,?_⟩
    have hdet := Matrix.SpecialLinearGroup.det_coe g
    rw [Matrix.det_fin_two] at hdet
    change g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 at hdet
    simpa only [← hd, sq] using hdet
  invFun t := by
    let a := t.val.1
    let b := t.val.2.1
    let c := t.val.2.2
    let g : SL(2,R) := ⟨!![a,b;c,a], by simpa only [Matrix.det_fin_two_of, sq] using t.property.2.2⟩
    exact ⟨g, (sl2_involution_iff g).mpr ⟨rfl,t.property.1,t.property.2.1⟩⟩
  left_inv x := by
    apply Subtype.ext
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j
    · rfl
    · rfl
    · rfl
    · exact ((sl2_involution_iff x.val).mp x.property).1
  right_inv t := by
    obtain ⟨⟨a,b,c⟩, h⟩ := t
    rfl

private lemma sl2_count_triples (n : ℕ) (hn : 1 ≤ n) :
    a n + 1 = Nat.card (SL2Triples (ZMod n)) := by
  classical
  let _ : NeZero n := ⟨by omega⟩
  let G := SL(2, ZMod n)
  let _ : Fintype G := Fintype.ofFinite _
  rw [← Nat.card_congr (sl2_triple_equiv (ZMod n))]
  change Nat.card {g : G // orderOf g = 2} + 1 = Nat.card {g : G // g^2 = 1}
  have hiff (g : G) : g^2 = 1 ↔ orderOf g = 2 ∨ g = 1 := by
    rw [orderOf_eq_prime_iff]
    by_cases h : g = 1 <;> simp [h]
  rw [Nat.card_congr (Equiv.subtypeEquivRight hiff)]
  simp only [Nat.card_eq_fintype_card]
  rw [Fintype.card_subtype_or_disjoint]
  · simp
  · apply disjoint_iff_inf_le.mpr
    intro g ⟨h, hg⟩
    change g = 1 at hg
    simp [hg] at h

/- Chinese remaindering turns the three scalar equations into independent equations at the prime powers dividing n. -/
private def sl2_triple_map {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (t : SL2Triples R) : SL2Triples S :=
  ⟨(f t.val.1, f t.val.2.1, f t.val.2.2),
    by simpa [map_ofNat] using congrArg f t.property.1,
    by simpa [map_ofNat] using congrArg f t.property.2.1,
    by simpa using congrArg f t.property.2.2⟩

private def sl2_triple_congr {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) : SL2Triples R ≃ SL2Triples S where
  toFun := sl2_triple_map e.toRingHom
  invFun := sl2_triple_map e.symm.toRingHom
  left_inv t := by apply Subtype.ext; simp [sl2_triple_map]
  right_inv t := by apply Subtype.ext; simp [sl2_triple_map]

private def sl2_triple_pi {ι : Type*} (R : ι → Type*) [∀ i, CommRing (R i)] :
    SL2Triples (∀ i, R i) ≃ (∀ i, SL2Triples (R i)) where
  toFun t i := sl2_triple_map (Pi.evalRingHom R i) t
  invFun f :=
    ⟨(fun i => (f i).val.1, fun i => (f i).val.2.1, fun i => (f i).val.2.2),
      funext fun i => (f i).property.1, funext fun i => (f i).property.2.1,
      funext fun i => (f i).property.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

private lemma sl2_triples_crt (n : ℕ) (hn : 0 < n) :
    Nat.card (SL2Triples (ZMod n)) =
      ∏ p : n.primeFactors, Nat.card (SL2Triples (ZMod ((p : ℕ) ^ n.factorization p))) := by
  rw [← Nat.card_pi]
  exact Nat.card_congr ((sl2_triple_congr (ZMod.equivPi n hn.ne')).trans (sl2_triple_pi _))

/- For an odd prime power, the off-diagonal entries vanish and the only possibilities are ±I. -/
private theorem sl2_odd_prime_power_card {p e : ℕ} (hp : p.Prime) (hodd : p ≠ 2) (he : 0 < e) :
    Nat.card {x : ZMod (p ^ e) × ZMod (p ^ e) × ZMod (p ^ e) //
      2 * x.2.1 = 0 ∧ 2 * x.2.2 = 0 ∧ x.1 ^ 2 - x.2.1 * x.2.2 = 1} = 2 := by
  classical
  let _ : Fact p.Prime := ⟨hp⟩
  let _ : NeZero (p ^ e) := ⟨pow_ne_zero _ hp.ne_zero⟩
  let R := ZMod (p ^ e)
  let π : R →+* ZMod p := ZMod.castHom (dvd_pow_self p he.ne') (ZMod p)
  have hunit {x : R} (hx : π x ≠ 0) : IsUnit x := by
    rw [← ZMod.natCast_zmod_val x, ZMod.isUnit_iff_coprime]
    apply Nat.Coprime.pow_right
    apply Nat.Coprime.symm
    apply hp.coprime_iff_not_dvd.mpr
    intro hdiv
    apply hx
    rw [← ZMod.natCast_zmod_val x, map_natCast]
    exact (ZMod.natCast_eq_zero_iff _ _).mpr hdiv
  have hp2 : (2 : ZMod p) ≠ 0 := by
    intro hz
    have hd := (ZMod.natCast_eq_zero_iff 2 p).mp hz
    exact hodd (((Nat.dvd_prime Nat.prime_two).mp hd).resolve_left hp.ne_one)
  have hπ2 : π 2 = 2 := by simpa only [map_one, one_add_one_eq_two] using map_add π 1 1
  have htwo : IsUnit (2 : R) := hunit (hπ2 ▸ hp2)
  have hne : (1 : R) ≠ -1 := by
    intro h
    have h' : (2 : R) = 0 := by linear_combination h
    exact hp2 (by simpa [hπ2] using congrArg π h')
  have roots {a : R} (ha : a ^ 2 = 1) : a = 1 ∨ a = -1 := by
    have hprod : (a - 1) * (a + 1) = 0 := by linear_combination ha
    by_cases hz : π (a - 1) = 0
    · have hπ : π a = 1 := sub_eq_zero.mp (by simpa using hz)
      have hunit' := hunit (x := a + 1) (by simpa [hπ, ← one_add_one_eq_two] using hp2)
      exact Or.inl (sub_eq_zero.mp (hunit'.mul_left_eq_zero.mp hprod))
    · exact Or.inr (eq_neg_of_add_eq_zero_left ((hunit hz).mul_right_eq_zero.mp hprod))
  let P (x : R × R × R) := 2 * x.2.1 = 0 ∧ 2 * x.2.2 = 0 ∧ x.1 ^ 2 - x.2.1 * x.2.2 = 1
  change Nat.card {x : R × R × R // P x} = 2
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hpairs : (Finset.univ.filter P) = {((1 : R), 0, 0), (-1, 0, 0)} := by
    ext ⟨a,b,c⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, P, Finset.mem_insert,
      Finset.mem_singleton, Prod.mk.injEq]
    constructor
    · rintro ⟨hb, hc, ha⟩
      obtain rfl := htwo.mul_right_eq_zero.mp hb
      obtain rfl := htwo.mul_right_eq_zero.mp hc
      simpa using roots (a := a) (by simpa using ha)
    · rintro (⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩) <;> norm_num
  rw [hpairs]
  simp [hne]

/- At modulus 2^(k+3), write an odd root as 2t+1. Then 2^(k+1) divides one of the consecutive integers t and t+1, leaving exactly four representatives. -/
private lemma oma_two_roots (k : ℕ) : Nat.card {a : ZMod (2^(k+3)) // a^2=1} = 4 := by
  classical
  let m := 2^(k+1)
  have hm : 2 ≤ m := by dsimp [m]; exact Nat.le_self_pow (by omega) _
  have hn : 2^(k+3) = 4*m := by dsimp [m]; ring
  rw [hn]
  let _ : NeZero (4*m) := ⟨by omega⟩
  let R := ZMod (4*m)
  let F : Finset ℕ := {1, 2*m-1, 2*m+1, 4*m-1}
  have small {i : ℕ} (hi : i ∈ F) : i < 4*m := by
    simp only [F,mem_insert,mem_singleton] at hi
    rcases hi with rfl|rfl|rfl|rfl <;> omega
  have Fcard : F.card = 4 := by
    dsimp only [F]
    rw [card_insert_of_notMem (by simp only [mem_insert,mem_singleton]; omega),
      card_insert_of_notMem (by simp only [mem_insert,mem_singleton]; omega),
      card_insert_of_notMem (by simp only [mem_singleton]; omega), card_singleton]
  have classify (a : R) (h : a^2=1) : a.val ∈ F := by
    have av := ZMod.val_lt a
    have he : a.val^2 ≡ 1 [MOD 4*m] := by
      apply (ZMod.natCast_eq_natCast_iff ..).mp
      simpa [R] using h
    have h2 := he.of_dvd (by exact ⟨2*m, by omega⟩ : 2 ∣ 4*m)
    have hodd : Odd (a.val^2) := by simpa [Nat.ModEq, Nat.odd_iff] using h2
    obtain ⟨t,ht⟩ := (Nat.odd_pow_iff (by decide : 2 ≠ 0)).mp hodd
    have heq : 4*m ∣ 4*(t*(t+1)) := by
      apply (ZMod.natCast_eq_zero_iff _ _).mp
      have eqn : (a.val^2 : ℕ) = 1+4*(t*(t+1)) := by rw [ht]; ring
      have h' := (ZMod.natCast_eq_natCast_iff ..).mpr he
      rw [eqn,Nat.cast_add,Nat.cast_one] at h'
      exact add_right_inj (a := (1 : R)) |>.mp (by simpa using h')
    have dh : m ∣ t*(t+1) := (Nat.mul_dvd_mul_iff_left (by decide : 0<4)).mp heq
    have alternatives : m ∣ t ∨ m ∣ t+1 := by
      by_cases par : 2 ∣ t
      · exact Or.inl ((Nat.prime_iff.mp Nat.prime_two).pow_dvd_of_dvd_mul_right _ (by omega) dh)
      · exact Or.inr ((Nat.prime_iff.mp Nat.prime_two).pow_dvd_of_dvd_mul_left _ par dh)
    have classifySmall {u : ℕ} (hu : u ≤ 2*m) (hd : m ∣ u) : u = 0 ∨ u = m ∨ u = 2*m := by
      obtain ⟨z,rfl⟩ := hd
      have hz : z ≤ 2 := by
        by_contra! hgt
        have := Nat.mul_le_mul_left m (by omega : 3 ≤ z)
        omega
      interval_cases z <;> simp [Nat.mul_comm]
    simp only [F,mem_insert,mem_singleton]
    rcases alternatives with d | d
    · have := classifySmall (by omega) d; omega
    · have := classifySmall (by omega) d; omega
  have valid {i : ℕ} (hi : i ∈ F) : (i : R)^2 = 1 := by
    change (i : ZMod (4*m))^2 = 1
    have zero : (4:ZMod (4*m))*(m:ZMod (4*m))=0 := by
      simpa only [Nat.cast_mul,Nat.cast_ofNat] using ZMod.natCast_self (4*m)
    simp only [F,mem_insert,mem_singleton] at hi
    rcases hi with rfl|rfl|rfl|rfl
    · simp
    · simp only [Nat.cast_sub (by omega : 1 ≤ 2*m),Nat.cast_one,Nat.cast_mul,Nat.cast_ofNat]
      linear_combination ((m:R)-1)*zero
    · simp only [Nat.cast_add,Nat.cast_one,Nat.cast_mul,Nat.cast_ofNat]
      linear_combination ((m:R)+1)*zero
    · simp only [Nat.cast_sub (by omega : 1 ≤ 4*m),Nat.cast_one,Nat.cast_mul,Nat.cast_ofNat]
      linear_combination ((4:R)*m-2)*zero
  let eqv : {a : R // a^2=1} ≃ F := {
    toFun := fun a => ⟨a.val.val, classify _ a.property⟩
    invFun := fun i => ⟨(i.val:R), valid i.property⟩
    left_inv := fun a => Subtype.ext (ZMod.natCast_zmod_val _)
    right_inv := fun i => Subtype.ext (ZMod.val_natCast_of_lt (small i.property)) }
  exact (Nat.card_congr eqv).trans (by simpa using Fcard)

/- Count the off-diagonal entries and scalar square roots at powers of two. -/
private lemma oma_sl2_two_power
    (roots : ∀ k : ℕ, Nat.card {a : ZMod (2^(k+3)) // a^2=1} = 4)
    (e : ℕ) (he : 1 ≤ e) :
    Nat.card {x : ZMod (2^e) × ZMod (2^e) × ZMod (2^e) //
      2*x.2.1=0 ∧ 2*x.2.2=0 ∧ x.1^2-x.2.1*x.2.2=1} = 2^(1+min 3 e) := by
  rcases e with _ | _ | _ | k
  · omega
  · rw [Nat.card_eq_fintype_card]
    decide
  · rw [Nat.card_eq_fintype_card]
    decide
  let N := 2^(k+3)
  let H := 2^(k+2)
  have hpos : 0 < H := by dsimp [H]; positivity
  have hN : N = 2*H := by dsimp [N,H]; ring
  let _ : NeZero N := ⟨by omega⟩
  let h : ZMod N := H
  have hne : h ≠ 0 := by
    change (H : ZMod N) ≠ 0
    intro e
    have := Nat.le_of_dvd hpos ((ZMod.natCast_eq_zero_iff H N).mp e)
    omega
  have ht : 2*h = 0 := by
    have hcast := (ZMod.natCast_eq_zero_iff (2*H) N).mpr (by rw [hN])
    simpa [h] using hcast
  have classify (z : ZMod N) : 2*z=0 ↔ z=0 ∨ z=h := by
    refine ⟨fun hz => ?_, fun hz => ?_⟩
    · have hdvd : N ∣ 2*z.val := (ZMod.natCast_eq_zero_iff ..).mp (by simpa using hz)
      have hdvd' : 2*H ∣ 2*z.val := hN ▸ hdvd
      have hd := (Nat.mul_dvd_mul_iff_left (by decide : 0<2)).mp hdvd'
      have hsmall := ZMod.val_lt z
      obtain ⟨w, hw⟩ := hd
      have hwlt : w < 2 := by
        by_contra! hc
        have hh := Nat.mul_le_mul_left H hc
        omega
      have hvals : z.val = 0 ∨ z.val = H := by interval_cases w <;> simp_all
      rcases hvals with hz' | hz'
      · left
        simpa [hz'] using (ZMod.natCast_zmod_val z).symm
      · right
        simpa [h, hz'] using (ZMod.natCast_zmod_val z).symm
    · rcases hz with rfl | rfl
      · simp
      · exact ht
  have hh : h*h=0 := by
    have evenH : H = 2 * 2^(k+1) := by dsimp [H]; ring
    have hhalf : h = 2*(2^(k+1) : ZMod N) := by dsimp [h]; rw [evenH]; push_cast; rfl
    calc h*h = (2*h)*(2^(k+1)) := by nth_rw 2 [hhalf]; ring
         _ = 0 := by rw [ht, zero_mul]
  have prod_zero {u v : ZMod N} (hu : 2*u=0) (hv : 2*v=0) : u*v=0 := by
    rcases (classify u).mp hu with rfl | rfl <;> rcases (classify v).mp hv with rfl | rfl <;> simp [hh]
  have card_torsion : Nat.card {z : ZMod N // 2*z=0} = 2 := by
    let pair : Finset (ZMod N) := {0,h}
    have equiv := Equiv.subtypeEquivRight (fun z : ZMod N =>
      show (2*z=0) ↔ z ∈ pair by simpa [pair] using classify z)
    rw [Nat.card_congr equiv, Nat.card_eq_fintype_card, Fintype.card_coe]
    simp [pair, hne.symm]
  let E : {x : ZMod N × ZMod N × ZMod N // 2*x.2.1=0 ∧ 2*x.2.2=0 ∧ x.1^2-x.2.1*x.2.2=1} ≃
      {a : ZMod N // a^2=1} × {b : ZMod N // 2*b=0} × {c : ZMod N // 2*c=0} := {
    toFun x := ⟨⟨x.1.1, by simpa [prod_zero x.2.1 x.2.2.1] using x.2.2.2⟩,
      ⟨x.1.2.1,x.2.1⟩, ⟨x.1.2.2,x.2.2.1⟩⟩
    invFun x := ⟨⟨x.1.1,x.2.1.1,x.2.2.1⟩, x.2.1.2, x.2.2.2,
      by simpa [prod_zero x.2.1.2 x.2.2.2] using x.1.2⟩
    left_inv _ := rfl
    right_inv _ := rfl }
  rw [Nat.card_congr E, Nat.card_prod, Nat.card_prod, card_torsion, roots k,
    Nat.min_eq_left (show 3 ≤ k+3 by omega)]
  decide

/- Multiply the local counts. -/
private lemma sl2_local_card_product (n : ℕ) (f : n.primeFactors → ℕ)
    (two : ∀ p : n.primeFactors, (p : ℕ) = 2 → f p = 2 ^ (1 + min 3 (n.factorization 2)))
    (odd : ∀ p : n.primeFactors, (p : ℕ) ≠ 2 → f p = 2) :
    (∏ p, f p) = 2 ^ (n.primeFactors.card + min 3 (padicValNat 2 n)) := by
  classical
  rw [← n.factorization_def Nat.prime_two]
  by_cases h : 2 ∈ n.primeFactors
  · let t : n.primeFactors := ⟨2, h⟩
    have hf (p : n.primeFactors) :
        f p = 2 * (if p = t then 2 ^ min 3 (n.factorization 2) else 1) := by
      split_ifs with he
      · subst p
        simpa [pow_add] using two t rfl
      · simpa using odd p (fun hp => he (Subtype.ext hp))
    simp_rw [hf]
    rw [Finset.prod_mul_distrib]
    simp [pow_add]
  · have hzero : n.factorization 2 = 0 := Finsupp.notMem_support_iff.mp (by simpa using h)
    have hf (p : n.primeFactors) : f p = 2 :=
      odd p (fun hp => h (hp ▸ p.property))
    simp [hf, hzero]

theorem OMA.solution : type_of% @OMA.S_oeis_a316553.main := by
  intro n hn
  have h := sl2_count_triples n hn
  rw [sl2_triples_crt n hn] at h
  have hprod := sl2_local_card_product n (fun p =>
    Nat.card (SL2Triples (ZMod ((p : ℕ)^n.factorization p))))
  have vp (p : n.primeFactors) : 0 < n.factorization p :=
    (Nat.prime_of_mem_primeFactors p.2).factorization_pos_of_dvd
      (by omega) (Nat.dvd_of_mem_primeFactors p.2)
  have two (p : n.primeFactors) (hp : (p : ℕ) = 2) :
      Nat.card (SL2Triples (ZMod ((p : ℕ)^n.factorization p))) =
        2^(1+min 3 (n.factorization 2)) := by
    have he := vp p
    rw [hp] at he ⊢
    exact oma_sl2_two_power oma_two_roots _ he
  have odd (p : n.primeFactors) (hp : (p : ℕ) ≠ 2) :
      Nat.card (SL2Triples (ZMod ((p : ℕ)^n.factorization p))) = 2 :=
    sl2_odd_prime_power_card (Nat.prime_of_mem_primeFactors p.2) hp (vp p)
  rw [hprod two odd] at h
  omega
