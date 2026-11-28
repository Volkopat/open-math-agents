import OMAReductions.R_arxiv_2604_17847_R1_H2_R1

-- Credit: @wispiANt
namespace OMA.R_arxiv_2604_17847_R1_H2_R1_H3_R1

open OMA.R_arxiv_2604_17847_R1 (rank_dvd_index)
open OMA.S_arxiv_2604_17847
open OMA.R_arxiv_2604_17847_R1_H2_R1

-- The complete 3-primary condition is a single iterated cubic equation.
def H1 : Prop :=
  ∀ q : ℕ, q.Prime → 1000 < q → 96 < pisano q →
    let h := pisano q / 2
    (¬ (q ∣ (ordCompl[q] (Nat.fib h)).totient ∨
        q ∣ (ordCompl[q] (ordCompl[2*q+1] (2*Nat.fib (h+1) - Nat.fib h))).totient)) → q % 15 = 8 →
    let t := pisano q/4
    q ^ 2 ∣ (if Even t then 2*Nat.fib (t+1)-Nat.fib t else Nat.fib t) → (2*q+1).Prime →
    let c := 2*(q+1)/pisano q
    ¬ (rankOfApparition (2*q+1)).Coprime c →
    ¬ (3 ∣ c ∧ (rankOfApparition (2*q+1)).Coprime (c/3) ∧
      ∃ x : ZMod (2*q+1), x^3 + 3*x = 1) →
    ¬ (c=3 ∧ Odd t) →
    ∃ x : ZMod (2*q+1), (fun y : ZMod (2*q+1) => y^3+3*y)^[c.factorization 3] x = 1

-- At the other shared primes only their rank valuations remain.
def H2 : Prop :=
  ∀ q : ℕ, q.Prime → 1000 < q → 96 < pisano q →
    let h := pisano q / 2
    (¬ (q ∣ (ordCompl[q] (Nat.fib h)).totient ∨
        q ∣ (ordCompl[q] (ordCompl[2*q+1] (2*Nat.fib (h+1) - Nat.fib h))).totient)) → q % 15 = 8 →
    let t := pisano q/4
    q ^ 2 ∣ (if Even t then 2*Nat.fib (t+1)-Nat.fib t else Nat.fib t) → (2*q+1).Prime →
    let c := 2*(q+1)/pisano q
    ¬ (rankOfApparition (2*q+1)).Coprime c →
    ¬ (3 ∣ c ∧ (rankOfApparition (2*q+1)).Coprime (c/3) ∧
      ∃ x : ZMod (2*q+1), x^3 + 3*x = 1) →
    ∀ l : ℕ, l.Prime → 7 ≤ l → l ∣ c → l ∣ rankOfApparition (2*q+1) →
      (rankOfApparition (2*q+1)).factorization l ≤ (pisano q).factorization l

-- Equal Fermat quotients in the odd-quarter case must produce a surviving witness.
def H3 : Prop :=
  ∀ q m : ℕ, q.Prime → 1000<q → 96<pisano q → q%15=8 →
    q+1=6*(2*m+1) → pisano q=4*(2*m+1) → (2*q+1).Prime →
    (¬ ∃ x : ZMod (2*q+1), x^3+3*x=1) →
    ((Nat.fib m)^(q-1)-1)/q ≡ ((Nat.fib (m+1))^(q-1)-1)/q [MOD q] →
    ∃ k : ℕ, 100<k ∧ Even k ∧ k%40≠14 ∧ k%40≠22 ∧ (k*q+1).Prime ∧
      k*q+1 ∣ Nat.fib (4*(2*m+1))

lemma cubic_trace {K : Type*} [Field K] {u v : K} (prod : u*v = -1) (e : ℕ) :
    (fun x : K => x^3+3*x)^[e] (u+v) = u^(3^e)+v^(3^e) := by
  induction e with
  | zero => simp
  | succ e ih =>
    rw [Function.iterate_succ_apply', ih, pow_succ 3 e, pow_mul, pow_mul]
    have h : u^(3^e)*v^(3^e) = -1 := by
      rw [←mul_pow, prod, (show Odd (3^e) from (by decide : Odd 3).pow).neg_one_pow]
    linear_combination 3*(u^(3^e)+v^(3^e))*h

lemma map_cubic_trace {p : ℕ} [Fact p.Prime] {K : Type*} [Field K] [Algebra (ZMod p) K]
    (x : ZMod p) (e : ℕ) :
    algebraMap (ZMod p) K ((fun y : ZMod p => y^3+3*y)^[e] x) =
      (fun y : K => y^3+3*y)^[e] (algebraMap (ZMod p) K x) := by
  induction e with
  | zero => rfl
  | succ e ih => simp only [Function.iterate_succ_apply', map_add, map_pow, map_mul, map_ofNat, ih]

lemma trace_pair {K : Type*} [Field K] [IsAlgClosed K] (two : (2 : K) ≠ 0) (x : K) :
    ∃ u v : K, u+v=x ∧ u*v = -1 := by
  obtain ⟨s,hs⟩ := IsAlgClosed.exists_pow_nat_eq (x^2+4) (by decide : 0 < 2)
  let u := (x+s)/2
  have twice : u*2=x+s := div_mul_cancel₀ _ two
  refine ⟨u,x-u,by ring,?_⟩
  apply mul_left_cancel₀ (pow_ne_zero 2 two)
  linear_combination -(2*u+s-x)*twice - hs

lemma frobenius_pair {p : ℕ} [Fact p.Prime] {K : Type*} [Field K] [CharP K p]
    {u v : K} (prod : u*v = -1) (fixed : (u+v)^p=u+v) :
    u^p=u ∨ u^p=v := by
  have trace : u^p+v^p=u+v := by rwa [add_pow_char] at fixed
  have norm : u^p*v^p = -1 := by
    rw [←mul_pow, prod, neg_one_pow_char]
  apply (mul_eq_zero.mp (show (u^p-u)*(u^p-v)=0 by
    linear_combination u^p*trace - norm + prod)).imp sub_eq_zero.mp sub_eq_zero.mp

lemma fibonacci_pair {p : ℕ} [Fact p.Prime] {K : Type*} [Field K] [CharP K p]
    (hl : 5 < p) (zero : p ∣ Nat.fib (p+1)) {a b : K} (sum : a+b=1) (prod : a*b = -1) :
    a^2=a+1 ∧ b^2=b+1 ∧ a-b ≠ 0 ∧ a^p=b := by
  have A : a^2=a+1 := by linear_combination a*sum-prod
  have B : b^2=b+1 := by linear_combination b*sum-prod
  have diff : a-b ≠ 0 := by
    intro same
    have five : (5 : K) ≠ 0 := CharP.cast_ne_zero_of_ne_of_prime K (by decide : Nat.Prime 5) (show p ≠ 5 by omega)
    exact five (by linear_combination (2*a-1)*sum + (2*a-1)*same - 4*A)
  refine ⟨A,B,diff,?_⟩
  rcases frobenius_pair prod (by rw [sum,one_pow]) with fix | swap
  · have f : a^p+b^p=1 := by rw [←add_pow_char,sum,one_pow]
    have fb : b^p=b := by linear_combination f - fix - sum
    have h := fib_root_difference A B (p+1)
    rw [(CharP.cast_eq_zero_iff K p _).mpr zero, zero_mul, pow_succ, pow_succ, fix, fb] at h
    exact (diff (by linear_combination -h - A + B)).elim
  · exact swap

lemma cubic_tower_iff {p e : ℕ} (hp : p.Prime) (hl : 5 < p)
    (zero : p ∣ Nat.fib (p+1)) (divides : 3^e ∣ p+1) :
    (∃ x : ZMod p, (fun y : ZMod p => y^3+3*y)^[e] x = 1) ↔
      p ∣ Nat.fib ((p+1)/3^e) := by
  let : Fact p.Prime := ⟨hp⟩
  let K := AlgebraicClosure (ZMod p)
  let k := 3^e
  let n := (p+1)/k
  have whole : k*n = p+1 := Nat.mul_div_cancel' divides
  have odd : Odd k := (by decide : Odd 3).pow
  have two : (2 : K) ≠ 0 := CharP.cast_ne_zero_of_ne_of_prime K Nat.prime_two (show p ≠ 2 by omega)
  constructor
  · rintro ⟨x,hx⟩
    let X := algebraMap (ZMod p) K x
    obtain ⟨u,v,tr,prod⟩ := trace_pair two X
    have sum : u^k+v^k=1 := by
      rw [← cubic_trace prod, tr, ←map_cubic_trace, hx, map_one]
    have norm : u^k*v^k = -1 := by rw [←mul_pow,prod,odd.neg_one_pow]
    obtain ⟨A,B,diff,swap⟩ := fibonacci_pair hl zero sum norm
    have fixed : (u+v)^p=u+v := by rw [tr]; simp [X, ←map_pow, ZMod.pow_card]
    have uv : u^p=v := by
      rcases frobenius_pair prod fixed with fix | ex
      · rw [←pow_mul, Nat.mul_comm k p, pow_mul, fix] at swap
        exact (diff (sub_eq_zero.mpr swap)).elim
      · exact ex
    rw [add_pow_char,uv] at fixed
    have vu : v^p=u := by linear_combination fixed
    have eq : u^(p+1)=v^(p+1) := by rw [pow_succ,pow_succ,uv,vu,mul_comm]
    have h := fib_root_difference A B n
    rw [←pow_mul, ←pow_mul, whole, eq, sub_self] at h
    exact (CharP.cast_eq_zero_iff K p _).mp ((mul_eq_zero.mp h).resolve_right diff)
  · intro short
    obtain ⟨a,b,sum,prod⟩ := trace_pair two (1 : K)
    obtain ⟨A,B,_,swap⟩ := fibonacci_pair hl zero sum prod
    have az : a ≠ 0 := by rintro rfl; simp at prod
    obtain ⟨u,hu⟩ := IsAlgClosed.exists_pow_nat_eq a (show 0 < k by positivity)
    have uz : u ≠ 0 := by rintro rfl; simp [show k ≠ 0 by positivity] at hu; exact az hu.symm
    let v := -(u⁻¹)
    have uv : u*v = -1 := by dsimp only [v]; rw [mul_neg, mul_inv_cancel₀ uz]
    have hv : v^k=b := by
      apply mul_left_cancel₀ az
      rw [←hu, ←mul_pow, uv, odd.neg_one_pow, hu, prod]
    have h := fib_root_difference A B n
    rw [(CharP.cast_eq_zero_iff K p _).mpr short,zero_mul] at h
    have same : u^(p+1)=v^(p+1) := by
      rw [←whole,pow_mul,pow_mul,hu,hv]
      exact sub_eq_zero.mp h.symm
    have sq : u^(p+1)*u^(p+1)=1 := by
      calc _ = u^(p+1)*v^(p+1) := by rw [←same]
           _ = 1 := by rw [←mul_pow,uv,pow_succ,neg_one_pow_char]; ring
    have nontriv : u^(p+1) ≠ 1 := by
      intro one
      have bad : a^(p+1)=1 := by rw [←hu,←pow_mul,Nat.mul_comm k _,pow_mul,one,one_pow]
      rw [pow_succ,swap,mul_comm,prod] at bad
      exact two (by linear_combination -bad)
    have minus : u^(p+1) = -1 := by
      rcases mul_self_eq_one_iff.mp sq with pos | neg
      · exact (nontriv pos).elim
      · exact neg
    have up : u^p=v := by
      apply mul_right_cancel₀ uz
      rw [←pow_succ,minus,mul_comm,uv]
    have vz : v ≠ 0 := by rintro h; rw [h,mul_zero] at uv; simp at uv
    have vp : v^p=u := by
      apply mul_right_cancel₀ vz
      rw [←pow_succ,←same,minus,uv]
    have fixed : (u+v)^p=u+v := by rw [add_pow_char,up,vp,add_comm]
    obtain ⟨i,hi⟩ := (mem_bot_iff_intCast p K).mp ((Subfield.mem_bot_iff_pow_eq_self K p).mpr fixed)
    refine ⟨i, (algebraMap (ZMod p) K).injective ?_⟩
    rw [map_cubic_trace,map_intCast,hi,cubic_trace uv,hu,hv,sum,map_one]

-- Removing exactly the 3-part of C does not change v₃(P).
lemma alignment_local_iff {q : ℕ} (hq : q.Prime) (hl : 5 < q)
    (residue : q%15=8) (hp : (2*q+1).Prime) :
    let c := 2*(q+1)/pisano q
    2*q+1 ∣ Nat.fib (pisano q) ↔
      (∃ x : ZMod (2*q+1), (fun y : ZMod (2*q+1) => y^3+3*y)^[c.factorization 3] x = 1) ∧
      ∀ l : ℕ, l.Prime → 7 ≤ l → l ∣ c → l ∣ rankOfApparition (2*q+1) →
        (rankOfApparition (2*q+1)).factorization l ≤ (pisano q).factorization l := by
  intro c
  let P := pisano q
  let k := 3^c.factorization 3
  let m := (2*q+1+1)/k
  let : NeZero q := ⟨hq.ne_zero⟩
  have Ppos : 0 < P := (period_and_returns q).1
  have total : P*c = 2*q+1+1 := by
    have h := Nat.mul_div_cancel' (nonsplit_period_cofactor hq hl (by omega)).1
    dsimp [P,c]; omega
  have cn : c ≠ 0 := by intro z; rw [z,mul_zero] at total; omega
  have strip : k ∣ c := Nat.ordProj_dvd c 3
  have divides : k ∣ 2*q+1+1 := total ▸ dvd_mul_of_dvd_right strip _
  have index : m = P*(c/k) := by
    dsimp only [m]; rw [←total,Nat.mul_div_assoc _ strip]
  have mpos : 0 < m := Nat.div_pos (Nat.le_of_dvd (by omega) divides) (by positivity)
  have zero := zero_at_selected_neighbor hp (by omega)
  rw [if_neg (by omega)] at zero
  have test := cubic_tower_iff hp (by omega) zero divides
  have locals := companion_odd_tests_iff hq hl residue hp
  constructor
  · intro aligned
    exact ⟨test.mpr (aligned.trans (Nat.fib_dvd _ _ (show P ∣ m by rw [index]; exact dvd_mul_right ..))),
      fun l pr big lc _ => locals.mp aligned l pr (by omega) lc⟩
  · rintro ⟨root,large⟩
    apply locals.mpr
    intro l pr above lc
    by_cases lr : l ∣ rankOfApparition (2*q+1)
    · by_cases three : l=3
      · subst l
        have rr := OMA.R_arxiv_2604_17847_R1.rank_dvd_index mpos (test.mp root)
        have rn : rankOfApparition (2*q+1) ≠ 0 := by intro z; rw [z,zero_dvd_iff] at rr; omega
        have h := (Nat.factorization_le_iff_dvd rn mpos.ne').mpr rr 3
        have unit : ¬ 3 ∣ c/k := Nat.not_dvd_ordCompl Nat.prime_three cn
        have nz : c/k ≠ 0 := by intro z; exact unit (z ▸ dvd_zero _)
        rw [index,Nat.factorization_mul Ppos.ne' nz,Finsupp.add_apply,
          Nat.factorization_eq_zero_of_not_dvd unit,add_zero] at h
        exact h
      · have notFive : l ≠ 5 := by
          intro eq
          subst l
          have d : 5 ∣ 2*q+1+1 := total ▸ dvd_mul_of_dvd_right lc _
          omega
        have big : 7 ≤ l := by
          by_contra! small
          have choices : l = 4 ∨ l = 6 := by omega
          rcases choices with rfl | rfl <;> norm_num at pr
        exact large l pr big lc lr
    · simp [Nat.factorization_eq_zero_of_not_dvd lr]

-- With a pure power of three there is no second local obstruction.
lemma alignment_three_power_iff {q e : ℕ} (hq : q.Prime) (hl : 5 < q)
    (residue : q%15=8) (hp : (2*q+1).Prime) (cofactor : 2*(q+1)/pisano q=3^e) :
    2*q+1 ∣ Nat.fib (pisano q) ↔
      ∃ x : ZMod (2*q+1), (fun y : ZMod (2*q+1) => y^3+3*y)^[e] x = 1 := by
  have h := alignment_local_iff hq hl residue hp
  dsimp only at h
  rw [cofactor,Nat.factorization_pow_self Nat.prime_three] at h
  constructor
  · exact fun z => (h.mp z).1
  · intro root
    refine h.mpr ⟨root, ?_⟩
    intro l prime big divides _
    have small := Nat.le_of_dvd (by decide : 0 < 3) (prime.dvd_of_dvd_pow divides)
    omega

lemma indices {q : ℕ} (hq : q.Prime) (large : 5 < q) (residue : q%15=8)
    (three : 2*(q+1)/pisano q=3) :
    pisano q=4*((q+1)/6) ∧ q+1=6*((q+1)/6) := by
  have full := (nonsplit_period_cofactor hq large (by omega)).1
  have mul := Nat.mul_div_cancel' full
  rw [three] at mul
  have hp := even_period (by omega : 2 < q)
  have hh := half_eq_twice_quarter hq large residue
  obtain ⟨u,hu⟩ := hp
  omega

lemma first_zero {q t : ℕ} (hq : q.Prime) (pos : 0<t) (odd : Odd t)
    (period : pisano q=4*t) : q ∣ Nat.fib t ∧ rankOfApparition q=t := by
  let : NeZero q := ⟨hq.ne_zero⟩
  have h := ((period_dvd_double_iff q (2*t)).mp (by rw [period]; exact dvd_of_eq (by omega)))
  rw [if_pos (by exact even_iff_two_dvd.mpr (dvd_mul_right ..)), Nat.fib_two_mul] at h
  have divides : q ∣ Nat.fib t := by
    rcases hq.dvd_mul.mp h with yes | no
    · exact yes
    · have small := (period_dvd_double_iff q t).mpr (by simpa [Nat.not_even_iff_odd.mpr odd] using no)
      rw [period] at small
      have := Nat.le_of_dvd (show 0<2*t by omega) small
      omega
  have first : 0 < rankOfApparition q ∧ q ∣ Nat.fib (rankOfApparition q) :=
    Nat.sInf_mem (s := {k : ℕ | 0<k ∧ q ∣ Nat.fib k}) ⟨t,pos,divides⟩
  have lb := fourfold_return first.2
  rw [period] at lb
  have := Nat.le_of_dvd (show 0<2*(2*rankOfApparition q) by omega) lb
  have := Nat.le_of_dvd pos (rank_dvd_index pos divides)
  exact ⟨divides,by omega⟩

lemma power_difference {q a b d : ℕ} (hq : q.Prime) (large : 2<q) (ab : a ≤ b)
    (unit : ¬q ∣ b) (zero : q ∣ b^2+a^2) (dpos : 0<d) (dsmall : d<q) (k : ℕ) :
    q^k ∣ b^2+a^2 ↔ a^(4*d) ≡ b^(4*d) [MOD q^k] := by
  let : Fact q.Prime := ⟨hq⟩
  have b0 : (b : ZMod q) ≠ 0 := fun h => unit ((ZMod.natCast_eq_zero_iff ..).mp h)
  have h := (ZMod.natCast_eq_zero_iff ..).mpr zero
  push_cast at h
  have h4 : (b : ZMod q)^4 = (a : ZMod q)^4 := by
    linear_combination ((b : ZMod q)^2-(a : ZMod q)^2)*h
  have a0 : (a : ZMod q) ≠ 0 := by
    intro z
    simp [z,b0] at h
  have diff : ¬q ∣ b^2-a^2 := by
    intro test
    have hz := (ZMod.natCast_eq_zero_iff ..).mpr test
    rw [Nat.cast_sub (Nat.pow_le_pow_left ab 2)] at hz
    push_cast at hz
    have two : (2 : ZMod q) ≠ 0 := CharP.cast_ne_zero_of_ne_of_prime _ Nat.prime_two (show q ≠ 2 by omega)
    exact (mul_ne_zero two (pow_ne_zero 2 b0)) (by linear_combination h+hz)
  let g := ∑ i ∈ Finset.range d, (b^4)^i*(a^4)^(d-1-i)
  have free : ¬q ∣ g := by
    intro hit
    have hz := (ZMod.natCast_eq_zero_iff ..).mpr hit
    dsimp only [g] at hz
    push_cast at hz
    rw [h4,geom_sum₂_self] at hz
    have du : (d : ZMod q) ≠ 0 := fun z => (Nat.not_dvd_of_pos_of_lt dpos dsmall) ((ZMod.natCast_eq_zero_iff ..).mp z)
    exact (mul_ne_zero du (pow_ne_zero _ (pow_ne_zero _ a0))) hz
  have delta : b^4-a^4=(b^2-a^2)*(b^2+a^2) := by
    zify [Nat.pow_le_pow_left ab 2,Nat.pow_le_pow_left ab 4]
    ring
  have product : b^(4*d)-a^(4*d)=(g*(b^2-a^2))*(b^2+a^2) := by
    rw [pow_mul,pow_mul,←geom_sum₂_mul_of_ge (Nat.pow_le_pow_left ab 4),delta,mul_assoc]
  rw [Nat.modEq_iff_dvd' (Nat.pow_le_pow_left ab _),product]
  exact ⟨fun hit => dvd_mul_of_dvd_right hit _, fun hit =>
    (((hq.coprime_iff_not_dvd.mpr free).mul_right (hq.coprime_iff_not_dvd.mpr diff)).pow_left k).dvd_of_dvd_mul_left hit⟩

lemma odd_quarter_power_test {q m : ℕ} (hq : q.Prime) (large : 5<q)
    (size : q+1=6*(2*m+1)) (period : pisano q=4*(2*m+1)) (k : ℕ) :
    q^k ∣ Nat.fib (2*m+1) ↔
      (Nat.fib m)^(q-1) ≡ (Nat.fib (m+1))^(q-1) [MOD q^k] := by
  obtain ⟨zero,rank⟩ := first_zero hq (by omega) (show Odd (2*m+1) from ⟨m,rfl⟩) period
  have unit : ¬ q ∣ Nat.fib (m+1) := by
    intro test
    have rd := rank_dvd_index (Nat.succ_pos m) test
    rw [rank] at rd
    have := Nat.le_of_dvd (Nat.succ_pos m) rd
    omega
  rw [Nat.fib_two_mul_add_one] at zero ⊢
  have d : q-1=4*((q-1)/4) := by omega
  rw [d]
  exact power_difference hq (by omega) Nat.fib_le_fib_succ unit zero (by omega) (by omega) k

lemma quotient_digit {q a b : ℕ} (hq : q.Prime) (au : ¬q ∣ a) (bu : ¬q ∣ b) :
    a^(q-1) ≡ b^(q-1) [MOD q^2] ↔
      (a^(q-1)-1)/q ≡ (b^(q-1)-1)/q [MOD q] := by
  have one (x : ℕ) (unit : ¬q ∣ x) : q*((x^(q-1)-1)/q)+1 = x^(q-1) := by
    have pos : 0 < x := Nat.pos_of_ne_zero (fun e => unit (e ▸ dvd_zero _))
    have powpos := pow_pos pos (q-1)
    have flt := Nat.ModEq.pow_totient (hq.coprime_iff_not_dvd.mpr unit).symm
    rw [Nat.totient_prime hq] at flt
    have divides := (Nat.modEq_iff_dvd' powpos).mp flt.symm
    rw [Nat.mul_div_cancel' divides]; omega
  constructor
  · intro h
    have e : q*((a^(q-1)-1)/q)+1 ≡ q*((b^(q-1)-1)/q)+1 [MOD q*q] := by
      simpa only [one a au,one b bu,pow_two] using h
    exact Nat.ModEq.mul_left_cancel' hq.ne_zero (Nat.ModEq.add_right_cancel' 1 e)
  · intro h
    have e := (h.mul_left' q).add (Nat.ModEq.refl 1)
    simpa only [one a au,one b bu,pow_two] using e

lemma stable_iff_equal_quotients {q m : ℕ} (hq : q.Prime) (large : 5<q) (residue : q%15=8)
    (size : q+1=6*(2*m+1)) (period : pisano q=4*(2*m+1)) :
    pisano (q^2)=pisano q ↔
      ((Nat.fib m)^(q-1)-1)/q ≡ ((Nat.fib (m+1))^(q-1)-1)/q [MOD q] := by
  have rank := (first_zero hq (by omega) (show Odd (2*m+1) from ⟨m,rfl⟩) period).2
  have unit (j : ℕ) (pos : 0<j) (small : j<2*m+1) : ¬q ∣ Nat.fib j := by
    intro test
    have rd := rank_dvd_index pos test
    rw [rank] at rd
    exact small.not_ge (Nat.le_of_dvd pos rd)
  have test := (stable_residue_half_iff hq large residue).trans (half_quarter_square_iff hq large residue)
  rw [show pisano q/4=2*m+1 by omega,if_neg (by simp)] at test
  exact test.trans ((odd_quarter_power_test hq large size period 2).trans
    (quotient_digit hq (unit m (by omega) (by omega)) (unit (m+1) (by omega) (by omega))))

-- For odd t, primes nonsplit at 5 and equal to 7 mod 8 cannot divide F_(4t).
lemma excluded_prime {s t : ℕ} (hs : s.Prime) (large : 5<s) (odd : Odd t)
    (eight : s%8=7) (ns : ¬(s%5=1 ∨ s%5=4)) : ¬s ∣ Nat.fib (4*t) := by
  intro zero
  let : NeZero s := ⟨hs.ne_zero⟩
  have small := (period_dvd_double_iff s (4*t)).mpr
    (by simpa only [if_pos (show Even (4*t) from ⟨2*t,by omega⟩)] using zero)
  obtain ⟨fits,_,oc⟩ := nonsplit_period_cofactor hs large ns
  let c := 2*(s+1)/pisano s
  have full : pisano s*c=2*(s+1) := Nat.mul_div_cancel' fits
  have div : 16 ∣ pisano s*c := by rw [full]; omega
  have cop : (2^4).Coprime c := (Nat.prime_two.coprime_iff_not_dvd.mpr
    (fun h => (Nat.not_even_iff_odd.mpr oc) (even_iff_two_dvd.mpr h))).pow_left 4
  have big : 16 ∣ pisano s := cop.dvd_of_dvd_mul_right div
  have := big.trans small
  obtain ⟨u,hu⟩ := odd
  omega

lemma multiplier_sieve {q k m : ℕ} (residue : q%15=8) (size : q+1=6*(2*m+1))
    (prime : (k*q+1).Prime) (big : 100<k) (bad : k%40=14 ∨ k%40=22) :
    ¬ (k*q+1 ∣ Nat.fib (4*(2*m+1))) := by
  have lp : 5<k*q+1 := by nlinarith
  have eight : (k*q+1)%8=7 := by
    rw [Nat.add_mod, Nat.mul_mod]
    have kr : k%8=6 := by omega
    rw [kr]
    have qr : q%8=1 ∨ q%8=5 := by omega
    rcases qr with h | h <;> rw [h]
  have ns : ¬((k*q+1)%5=1 ∨ (k*q+1)%5=4) := by
    rw [Nat.add_mod,Nat.mul_mod,show q%5=3 by omega]
    have : k%5=4 ∨ k%5=2 := by omega
    rcases this with h | h <;> rw [h] <;> decide
  exact excluded_prime prime lp ⟨m,rfl⟩ eight ns

lemma allowed_witness_iff {q m : ℕ} (hq : q.Prime) (large : 53<q) (residue : q%15=8)
    (size : q+1=6*(2*m+1)) (period : pisano q=4*(2*m+1)) :
    (q ∣ (ordCompl[q] (Nat.fib (pisano q/2))).totient ∨
     q ∣ (ordCompl[q] (ordCompl[2*q+1] (2*Nat.fib (pisano q/2+1)-Nat.fib (pisano q/2)))).totient) ↔
    ∃ k : ℕ, 100<k ∧ Even k ∧ k%40≠14 ∧ k%40≠22 ∧ (k*q+1).Prime ∧
      k*q+1 ∣ Nat.fib (4*(2*m+1)) := by
  let : NeZero q := ⟨hq.ne_zero⟩
  have halves := other_witness_half_tests hq large
  dsimp only at halves
  rw [←halves,companion_removed_witness hq
    (Nat.fib_pos.mpr (period_and_returns q).1).ne']
  constructor
  · rintro ⟨s,hs,cong,zero,other⟩
    obtain ⟨k,hk,he,rfl⟩ := witness_multiplier hq (by omega) hs cong
    have big : 100<k := by
      by_contra! small
      have unique := unique_witness_through_100 hq large hk he small hs ((rank_test_at_period hs hq).mpr zero)
      exact other (by rw [unique])
    rw [period] at zero
    have sieve := fun h => multiplier_sieve residue size hs big h zero
    exact ⟨k,big,he,fun h => sieve (.inl h),fun h => sieve (.inr h),hs,zero⟩
  · rintro ⟨k,big,_,_,_,prime,zero⟩
    refine ⟨k*q+1,prime,by simp [Nat.ModEq,Nat.add_mod],period ▸ zero,?_⟩
    intro e
    have eq : k*q=2*q := by omega
    have := Nat.eq_of_mul_eq_mul_right hq.pos eq
    omega


lemma parent_iff : (H1 ∧ H2 ∧ H3) ↔ OMA.R_arxiv_2604_17847_R1_H2_R1.H3 := by
  constructor
  · rintro ⟨tower,large,exceptional⟩ q hq high long h noOther res t square hp c cop cubic
    have half := (half_quarter_square_iff hq (by omega) res).mpr square
    apply (companion_quarter_iff hq (by omega) res half hp).mp
    by_cases special : c=3 ∧ Odd t
    · obtain ⟨period,size⟩ := indices hq (by omega) res special.1
      obtain ⟨m,hm⟩ := special.2
      have split : (q+1)/6=2*m+1 := by dsimp [t] at hm; omega
      rw [split] at period size
      by_contra miss
      have c3 : 2*(q+1)/pisano q=3^1 := special.1
      have noRoot : ¬ ∃ x : ZMod (2*q+1), x^3+3*x=1 := by
        simpa only [Function.iterate_one] using mt (alignment_three_power_iff hq (by omega) res hp c3).mpr miss
      have stable := (stable_residue_half_iff hq (by omega) res).mpr half
      have digits := (stable_iff_equal_quotients hq (by omega) res size period).mp stable
      have hit := exceptional q m hq high long res size period hp noRoot digits
      exact noOther ((allowed_witness_iff hq (by omega) res size period).mpr hit)
    · exact (alignment_local_iff hq (by omega) res hp).mpr
        ⟨tower q hq high long noOther res square hp cop cubic special,
         large q hq high long noOther res square hp cop cubic⟩
  · intro parent
    refine ⟨?_,?_,?_⟩
    · intro q hq high long h noOther res t square hp c cop cubic _
      have half := (half_quarter_square_iff hq (by omega) res).mpr square
      have aligned := (companion_quarter_iff hq (by omega) res half hp).mpr
        (parent q hq high long noOther res square hp cop cubic)
      exact ((alignment_local_iff hq (by omega) res hp).mp aligned).1
    · intro q hq high long h noOther res t square hp c cop cubic
      have half := (half_quarter_square_iff hq (by omega) res).mpr square
      have aligned := (companion_quarter_iff hq (by omega) res half hp).mpr
        (parent q hq high long noOther res square hp cop cubic)
      exact ((alignment_local_iff hq (by omega) res hp).mp aligned).2
    · intro q m hq high long res size period hp noRoot digits
      by_contra noWitness
      have noOther := mt (allowed_witness_iff hq (by omega) res size period).mp noWitness
      have stable := (stable_iff_equal_quotients hq (by omega) res size period).mpr digits
      have half := (stable_residue_half_iff hq (by omega) res).mp stable
      have square := (half_quarter_square_iff hq (by omega) res).mp half
      have c3 : 2*(q+1)/pisano q=3^1 := by
        rw [size,period,show 2*(6*(2*m+1))=4*(2*m+1)*3 by ring,
          Nat.mul_div_cancel_left _ (by positivity : 0<4*(2*m+1))]
        decide
      have miss : ¬ 2*q+1 ∣ Nat.fib (pisano q) := by
        apply mt (alignment_three_power_iff hq (by omega) res hp c3).mp
        simpa only [Function.iterate_one] using noRoot
      have cop := mt (alignment_of_coprime_cofactor hq (by omega) res hp) miss
      have test := parent q hq high long noOther res square hp cop (fun h => noRoot h.2.2)
      exact miss ((companion_quarter_iff hq (by omega) res half hp).mpr test)

theorem main : H1 → H2 → H3 → OMA.R_arxiv_2604_17847_R1_H2_R1.H3 :=
  fun tower large exceptional => parent_iff.mp ⟨tower,large,exceptional⟩

end OMA.R_arxiv_2604_17847_R1_H2_R1_H3_R1
