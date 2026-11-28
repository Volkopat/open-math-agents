import OMAStatements.S_oeis_a140320

namespace OrderGrowth

theorem four_valuation (j : ℕ) :
    padicValNat 3 (4^(3^j)-1) = j+1 := by
  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
  have h := padicValNat.pow_sub_pow (p:=3) (x:=4) (y:=1)
    (by decide : Odd 3) (by decide) (by decide) (by decide)
    (n:=3^j) (by positivity)
  simpa [padicValNat.prime_pow, Nat.add_comm] using h

theorem four_power_iff (m j : ℕ) :
    (4 : ZMod (3^m))^(3^j)=1 ↔ m ≤ j+1 := by
  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
  have hpow : 1 < 4^(3^j) := one_lt_pow₀ (by decide) (by positivity)
  have cast : ((4^(3^j)-1 : ℕ) : ZMod (3^m)) =
      (4 : ZMod (3^m))^(3^j)-1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ 4^(3^j))]
    simp
  calc
    (4 : ZMod (3^m))^(3^j)=1 ↔ ((4^(3^j)-1 : ℕ) : ZMod (3^m))=0 := by
      rw [cast,sub_eq_zero]
    _ ↔ 3^m ∣ 4^(3^j)-1 := ZMod.natCast_eq_zero_iff _ _
    _ ↔ m ≤ padicValNat 3 (4^(3^j)-1) := padicValNat_dvd_iff_le (by omega)
    _ ↔ m ≤ j+1 := by rw [four_valuation]

theorem order_pow (k : ℕ) : OMA.S_oeis_a140320.ordTwo (3^(k+1)) = 2 * 3^k := by
  unfold OMA.S_oeis_a140320.ordTwo
  apply orderOf_eq_of_pow_and_pow_div_prime (by positivity)
  · rw [pow_mul, show (2 : ZMod (3^(k+1)))^2=4 by norm_num]
    exact (four_power_iff (k+1) k).2 (by omega)
  · intro p hp hd
    rcases hp.dvd_mul.mp hd with htwo | hthree
    · have equal : p=2 := ((Nat.dvd_prime Nat.prime_two).mp htwo).resolve_left hp.ne_one
      subst p
      have exp : (2*3^k)/2=3^k := by omega
      rw [exp]
      intro bad
      have div3 : 3 ∣ 3^(k+1) := ⟨3^k,by rw [pow_succ]; ring⟩
      let f : ZMod (3^(k+1)) →+* ZMod 3 := ZMod.castHom div3 (ZMod 3)
      have mapped := congrArg f bad
      simp only [map_pow,map_ofNat,map_one] at mapped
      have odd : Odd (3^k) := (by decide : Odd (3:ℕ)).pow
      rw [show (2 : ZMod 3)= -1 by decide,odd.neg_one_pow] at mapped
      exact (by decide : (-1 : ZMod 3) ≠ 1) mapped
    · have div : p ∣ 3 := hp.dvd_of_dvd_pow hthree
      have equal : p=3 := ((Nat.dvd_prime (by decide : Nat.Prime 3)).mp div).resolve_left hp.ne_one
      subst p
      cases k with
      | zero => norm_num at hthree
      | succ k =>
        have exp : (2*3^(k+1))/3=2*3^k := by rw [pow_succ]; omega
        rw [exp,pow_mul,show (2 : ZMod (3^(k+1+1)))^2=4 by norm_num]
        intro bad
        have impossible := (four_power_iff (k+1+1) k).1 bad
        omega

end OrderGrowth

namespace OrderGrowth
open Finset OMA.S_oeis_a140320

lemma order_one : ordTwo 1=1 := by
  unfold ordTwo
  rw [Subsingleton.elim (2 : ZMod 1) 1, orderOf_one]

lemma order_tot (n : ℕ) (h : Nat.Coprime 2 n) : ordTwo n ∣ n.totient := by
  apply orderOf_dvd_of_pow_eq_one
  have t := (ZMod.natCast_eq_natCast_iff (2^n.totient) 1 n).2 (Nat.ModEq.pow_totient h)
  simpa using t

lemma order_reduces {d n : ℕ} (hd : d ∣ n) : ordTwo d ∣ ordTwo n := by
  let f := ZMod.castHom hd (ZMod d)
  have t := orderOf_map_dvd f.toMonoidHom (2 : ZMod n)
  change orderOf (f 2) ∣ orderOf (2 : ZMod n) at t
  simpa only [map_ofNat,ordTwo] using t

lemma odd_number (n : ℕ) : Nat.Coprime 2 (2*n+1) := by
  exact Nat.coprime_two_left.mpr ⟨n,by omega⟩

theorem lower (n : ℕ) : 2*n+1 ≤ a137576 n := by
  let N := 2*n+1
  have hN : 0<N := by simp [N]
  have hc : Nat.Coprime 2 N := odd_number n
  have hp : 0<ordTwo N := Nat.pos_of_dvd_of_pos (order_tot N hc) (Nat.totient_pos.mpr hN)
  have h1 : 1∈N.divisors := Nat.one_mem_divisors.mpr hN.ne'
  have sw : (∑ d ∈ N.divisors.erase 1, d.totient/ordTwo d)+1 =
      ∑ d ∈ N.divisors, d.totient/ordTwo d := by
    simpa [order_one] using
      Finset.sum_erase_add N.divisors (fun d : ℕ => d.totient/ordTwo d) h1
  have st : (∑ d ∈ N.divisors.erase 1, d.totient)+1=N := by
    simpa [Nat.sum_totient] using Finset.sum_erase_add N.divisors Nat.totient h1
  have bound : (∑ d ∈ N.divisors.erase 1, d.totient) ≤
      ordTwo N * ∑ d ∈ N.divisors.erase 1, d.totient/ordTwo d := by
    rw [Finset.mul_sum]
    apply sum_le_sum
    intro d hd
    have hdvd := Nat.dvd_of_mem_divisors (Finset.mem_of_mem_erase hd)
    have htot := order_tot d (Nat.Coprime.of_dvd_right hdvd hc)
    have hle := Nat.le_of_dvd hp (order_reduces hdvd)
    calc
      d.totient = ordTwo d * (d.totient/ordTwo d) := (Nat.mul_div_cancel' htot).symm
      _ ≤ ordTwo N * (d.totient/ordTwo d) := Nat.mul_le_mul_right _ hle
  change N ≤ 1+ordTwo N*((∑ d ∈ N.divisors, d.totient/ordTwo d)-1)
  rw [← sw, Nat.add_sub_cancel]
  omega

theorem prime_equality (n : ℕ) (hp : (2*n+1).Prime) : a137576 n=2*n+1 := by
  let N := 2*n+1
  change N.Prime at hp
  change 1+ordTwo N*((∑ d ∈ N.divisors, d.totient/ordTwo d)-1)=N
  rw [hp.divisors]
  simp only [sum_insert (show 1 ∉ ({N} : Finset ℕ) by simpa using hp.ne_one.symm),
    sum_singleton, Nat.totient_one, order_one, Nat.div_one]
  have cut (q : ℕ) : 1+q-1=q := by omega
  rw [cut (N.totient/ordTwo N),
    Nat.mul_div_cancel' (order_tot N (odd_number n)),
    Nat.totient_prime hp]
  omega

theorem power_value (k : ℕ) :
    a137576 ((3^k-1)/2)=2*k*3^(k-1)+1 := by
  have hodd : Odd (3^k) := (by decide : Odd (3 : ℕ)).pow
  obtain ⟨u,hu⟩ := hodd
  have hn : 2*((3^k-1)/2)+1=3^k := by omega
  have ratio (j : ℕ) : (3^j).totient / ordTwo (3^j) = 1 := by
    cases j with
    | zero => simp [order_one]
    | succ t =>
      rw [order_pow, Nat.totient_prime_pow_succ (by decide : Nat.Prime 3)]
      rw [show 3^t*(3-1)=2*3^t by ring]
      exact Nat.div_self (by positivity)
  have hs : (∑ d ∈ (3^k).divisors, d.totient / ordTwo d) = k+1 := by
    rw [Nat.divisors_prime_pow (by decide : Nat.Prime 3)]
    simp [Finset.sum_map, ratio]
  change 1+ordTwo (2*((3^k-1)/2)+1)*
    ((∑ d ∈ (2*((3^k-1)/2)+1).divisors, d.totient/ordTwo d)-1)=_
  rw [hn,hs]
  cases k with
  | zero => simp [order_one]
  | succ t =>
    rw [order_pow]
    simp only [Nat.add_sub_cancel]
    ring

theorem prime_often (N : ℕ) : ∃ n ≥ N, a137576 n=2*n+1 := by
  obtain ⟨p,hp,prime⟩ := Nat.exists_infinite_primes (2*N+3)
  have hodd := prime.odd_of_ne_two (by omega)
  obtain ⟨n, hn⟩ := hodd
  have e : 2*n+1=p := by omega
  exact ⟨n,by omega,prime_equality n (e.symm ▸ prime)⟩

lemma power_large (k : ℕ) : k < 3^k := by
  induction k with
  | zero => decide
  | succ k ih => rw [pow_succ]; omega

theorem unbounded (B N : ℕ) : ∃ n : ℕ, N ≤ n ∧ B*n < a137576 n := by
  let k := 3*(B+N+1)
  let n := (3^(k+1)-1)/2
  have hp := power_large k
  have hn : N ≤ n := by dsimp [n]; rw [pow_succ]; dsimp [k] at hp ⊢; omega
  have hn' : n ≤ 3*3^k := by dsimp [n]; rw [pow_succ]; omega
  have hB : B*n ≤ (3*B)*3^k := by
    calc B*n ≤ B*(3*3^k) := Nat.mul_le_mul_left B hn'
         _ = _ := by ring
  have hk : 3*B ≤ 2*(k+1) := by dsimp [k]; omega
  have hh := Nat.mul_le_mul_right (3^k) hk
  refine ⟨n,hn,?_⟩
  rw [show a137576 n=2*(k+1)*3^k+1 by simpa [n] using power_value (k+1)]
  omega

end OrderGrowth

theorem OMA.solution : type_of% @OMA.S_oeis_a140320.main :=
  ⟨OrderGrowth.power_value, OrderGrowth.lower, OrderGrowth.prime_equality,
    OrderGrowth.prime_often, OrderGrowth.unbounded⟩
