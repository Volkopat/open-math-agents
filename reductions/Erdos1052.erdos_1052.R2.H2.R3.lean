import OMAReductions.R_Erdos1052_erdos_1052_R2

/-!
# Two prime counts for a fixed odd powerful core

A bound for the number of simple Mersenne primes, together with one for
simple primes q congruent to 31 modulo 32 whose shifted odd part is another
simple prime, implies exponent finiteness. Merge vertices and core demands
are controlled by prime-factor multiplicities. All ordinary prime steps
left after removing boundedly many vertices have multiplier 2 or 8.
A finite closed set and a reciprocal tail estimate force a fresh
exception at each successive scale if the exponent is large.

Credit: @ubuwaits
-/

namespace OMA.R_Erdos1052_erdos_1052_R2_H2_R3

/-- Bound the number of simple Mersenne primes in a completion of a fixed core. -/
def H1 : Prop :=
  ∀ c : ℕ, Odd c → (∀ p ∈ c.primeFactors, 2 ≤ c.factorization p) →
    ∃ K : ℕ, ∀ a : ℕ, ∀ S : Finset ℕ,
      let b := 2^a*c
      let u := ∏ p ∈ b.primeFactors, (1+p^b.factorization p)
      5 ≤ a → 4 ≤ S.card → S ⊆ Finset.Icc 3 u →
      (∀ p ∈ S, p.Prime ∧ ¬p ∣ b) →
      u*(∏ p ∈ S, (1+p)) = (2*b)*(∏ p ∈ S, p) →
      (S.filter (fun q => ordCompl[2] (1+q)=1)).card ≤ K

/-- Bound long shifts whose odd part is itself a single simple prime. -/
def H2 : Prop :=
  ∀ c : ℕ, Odd c → (∀ p ∈ c.primeFactors, 2 ≤ c.factorization p) →
    ∃ K : ℕ, ∀ a : ℕ, ∀ S : Finset ℕ,
      let b := 2^a*c
      let u := ∏ p ∈ b.primeFactors, (1+p^b.factorization p)
      5 ≤ a → 4 ≤ S.card → S ⊆ Finset.Icc 3 u →
      (∀ p ∈ S, p.Prime ∧ ¬p ∣ b) →
      u*(∏ p ∈ S, (1+p)) = (2*b)*(∏ p ∈ S, p) →
      (S.filter (fun q => ordCompl[2] (1+q)∈S ∧ 32∣1+q)).card ≤ K


/-- A constant jump permutes residues at the starting prime. -/
theorem constant_jump_impossible (f : ℕ → ℕ) (j : ℕ) (hj : 0<j)
    (hp : ∀ n, (f n).Prime) (hl : ∀ n, 5<f n)
    (step : ∀ n, f (n+1)+1=2^j*f n) : False := by
  let p := f 0
  let : Fact p.Prime := ⟨hp 0⟩
  let z (n : ℕ) : ZMod p := f n
  have htwo : (2:ZMod p)≠0 := by
    intro he
    have hd : p∣2 := (ZMod.natCast_eq_zero_iff 2 p).mp (by simpa using he)
    have := Nat.le_of_dvd (by decide : 0<2) hd
    have := hl 0
    dsimp [p] at *
    omega
  have transition n : z (n+1)+1=2^j*z n := by
    simpa only [z,Nat.cast_add,Nat.cast_one,Nat.cast_pow,Nat.cast_ofNat,Nat.cast_mul]
      using congrArg (fun t : ℕ => (t:ZMod p)) (step n)
  have undo (n t : ℕ) (he : z (n+t)=z n) : z t=z 0 := by
    induction n with
    | zero => simpa using he
    | succ n ih =>
      apply ih
      apply mul_left_cancel₀ (pow_ne_zero j htwo)
      rw [←transition,←transition]
      rw [Nat.succ_add] at he
      rw [he]
  obtain ⟨i,k,hik,he⟩ := Set.Finite.exists_lt_map_eq_of_forall_mem
    (f:=z) (fun n => Set.mem_univ (z n)) (Set.toFinite Set.univ)
  let t := k-i
  have ht : 0<t := by dsimp [t]; omega
  have zero : z t=0 := (undo i t (by rwa [show i+t=k by dsimp [t]; omega,eq_comm])).trans
    (ZMod.natCast_self p)
  have hd := (ZMod.natCast_eq_zero_iff (f t) p).mp zero
  have eq := ((hp t).dvd_iff_eq (hp 0).ne_one).mp hd
  have multi : 2≤(2:ℕ)^j := Nat.le_pow hj
  have increasing : StrictMono f := strictMono_nat_of_lt_succ fun n => by
    have := Nat.mul_le_mul_right (f n) multi
    have := step n
    have := hl n
    omega
  exact (increasing ht).ne eq.symm

/-- The two ordinary successors above five admit no infinite chain. -/
theorem two_jump_wellFounded :
    WellFounded (fun q r : ℕ => r.Prime ∧ 5<r ∧ q.Prime ∧ 5<q ∧
      (q+1=2*r ∨ q+1=8*r)) := by
  apply wellFounded_iff_isEmpty_descending_chain.mpr
  refine ⟨fun ⟨f,hf⟩ => ?_⟩
  have allowed n : f n % 5≠0 := fun h => by
    have div := Nat.dvd_iff_mod_eq_zero.mpr h
    have eq := ((hf n).1.dvd_iff_eq (by decide : 5≠1)).mp div
    have := (hf n).2.1
    omega
  have trans n : f (n+1)%5≠4 ∧
      (f n%5=3 → f (n+1)%5=3 ∧ f (n+1)+1=8*f n) ∧
      (f n%5=2 → f (n+1)%5=3) ∧
      (f n%5=1 → f (n+1)%5=1 → f (n+1)+1=2*f n) := by
    have := allowed n
    have := allowed (n+1)
    rcases (hf n).2.2.2.2 with h | h <;> omega
  by_cases hit : ∃ k, f k%5=3
  · obtain ⟨k,hk⟩ := hit
    have stuck (n : ℕ) : f (k+n)%5=3 := by
      induction n with
      | zero => simpa using hk
      | succ n ih => exact ((trans (k+n)).2.1 ih).1
    exact constant_jump_impossible (fun n => f (k+n)) 3 (by decide)
      (fun n => (hf _).1) (fun n => (hf _).2.1)
      (fun n => ((trans (k+n)).2.1 (stuck n)).2)
  · push Not at hit
    have ones n : f (n+1)%5=1 := by
      have h2 : f (n+1)%5≠2 := fun h => hit _ ((trans (n+1)).2.2.1 h)
      have := (trans n).1
      have := allowed (n+1)
      have := hit (n+1)
      omega
    exact constant_jump_impossible (fun n => f (n+1)) 1 (by decide)
      (fun n => (hf _).1) (fun n => (hf _).2.1)
      (fun n => (trans (n+1)).2.2.2 (ones n) (ones (n+1)))

/-- Any finite starting interval extends to a finite set closed under both prime steps. -/
theorem finite_closed_cover (m : ℕ) :
    ∃ F : Finset ℕ, (∀ p ≤ m, p ∈ F) ∧ ∀ r ∈ F, ∀ q : ℕ,
      r.Prime → 5<r → q.Prime → 5<q → (q+1=2*r ∨ q+1=8*r) → q∈F := by
  classical
  let R (r q : ℕ) := r.Prime ∧ 5<r ∧ q.Prime ∧ 5<q ∧ (q+1=2*r ∨ q+1=8*r)
  have finiteFrom (r : ℕ) : {q | Relation.ReflTransGen R r q}.Finite := by
    induction r using two_jump_wellFounded.induction with
    | h r ih =>
      let next := {q | R r q}
      have hn : next.Finite := (Set.finite_le_nat (8*r)).subset fun q hq => by
        change q≤8*r
        rcases hq.2.2.2.2 with h | h <;> omega
      apply ((Set.finite_singleton r).union (hn.biUnion fun q hq => ih q hq)).subset
      intro q hq
      rcases hq.cases_head with rfl | ⟨k,hk,hq⟩
      · exact Or.inl rfl
      · exact Or.inr (Set.mem_iUnion₂.mpr ⟨k,hk,hq⟩)
  let reachable := ⋃ r ∈ Set.Iic m, {q | Relation.ReflTransGen R r q}
  have hfin : reachable.Finite := (Set.finite_Iic m).biUnion (fun r _ => finiteFrom r)
  refine ⟨hfin.toFinset, fun r hr => hfin.mem_toFinset.mpr ?_, ?_⟩
  · exact Set.mem_iUnion₂.mpr ⟨r,hr,.refl⟩
  · intro r hr q hrp h5 hqp hq5 hstep
    obtain ⟨k,hk,path⟩ := Set.mem_iUnion₂.mp (hfin.mem_toFinset.mp hr)
    exact hfin.mem_toFinset.mpr (Set.mem_iUnion₂.mpr ⟨k,hk,path.tail ⟨hrp,h5,hqp,hq5,hstep⟩⟩)

/-- With an injective predecessor growing by at least a factor two in q-1,
the reciprocal tail is small in terms of the number of exceptions. -/
theorem tail_sum {S E : Finset ℕ} {d : ℕ → ℕ} (hE : E ⊆ S)
    (hr : ∀ q ∈ S\E, d q ∈ S ∧ 2*(d q-1) ≤ q-1)
    (hinj : Set.InjOn d (↑(S\E) : Set ℕ)) (X : ℕ) (hX : 0<X) :
    ∑ q ∈ S with 2*X+1<q, (1 : ℚ)/q ≤ 2*E.card/X := by
  classical
  let f (q : ℕ) : ℚ := 1/(max X (q-1) : ℕ)
  have hx (q : ℕ) : 0 < max X (q-1) := hX.trans_le (le_max_left ..)
  have hf q : 0 ≤ f q := (one_div_pos.mpr (by exact_mod_cast hx q)).le
  have upper q : f q ≤ 1/(X:ℚ) :=
    one_div_le_one_div_of_le (by exact_mod_cast hX) (by exact_mod_cast le_max_left X (q-1))
  have cost (q : ℕ) (hq : q∈S\E) :
      (if 2*X+1<q then (1:ℚ)/q else 0) ≤ f (d q)-f q := by
    have h := (hr q hq).2
    by_cases large : 2*X+1<q
    · rw [if_pos large]
      have hmax : 2*max X (d q-1) ≤ q-1 := by omega
      have hq1 : 0 < q-1 := by omega
      have a : (1:ℚ)/q ≤ 1/(q-1 : ℕ) := one_div_le_one_div_of_le
        (by exact_mod_cast hq1) (by exact_mod_cast Nat.sub_le q 1)
      have b : (2:ℚ)/(q-1 : ℕ) ≤ f (d q) := by
        apply (div_le_div_iff₀ (by exact_mod_cast hq1) (by exact_mod_cast hx (d q))).mpr
        simpa using (show (2:ℚ)*(max X (d q-1) : ℕ) ≤ (q-1 : ℕ) by exact_mod_cast hmax)
      have he : f q = 1/(q-1 : ℕ) := by
        change (1:ℚ)/↑(max X (q-1)) = _
        rw [max_eq_right (show X≤q-1 by omega)]
      rw [he]
      linarith [show (2:ℚ)/(q-1 : ℕ)=1/(q-1 : ℕ)+1/(q-1 : ℕ) by ring]
    · rw [if_neg large, sub_nonneg]
      apply one_div_le_one_div_of_le (by exact_mod_cast hx (d q))
      exact_mod_cast max_le_max_left X (show d q-1≤q-1 by omega)
  have image_le : ∑ q ∈ S\E, f (d q) ≤ ∑ q ∈ S, f q := by
    rw [← Finset.sum_image hinj]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.image_subset_iff.mpr fun q hq => (hr q hq).1)
      (fun q _ _ => hf q)
  have he : ∑ q ∈ E, f q ≤ (E.card:ℚ)/X := by
    calc _ ≤ ∑ _ ∈ E, 1/(X:ℚ) := Finset.sum_le_sum fun q _ => upper q
         _ = _ := by simp [div_eq_mul_inv]
  have hreg := Finset.sum_le_sum cost
  rw [Finset.sum_sub_distrib] at hreg
  let fee (q : ℕ) : ℚ := if 2*X+1<q then 1/(q:ℚ) else 0
  have hes : ∑ q ∈ E, fee q ≤ (E.card:ℚ)/X := by
    apply le_trans (Finset.sum_le_sum (g:=fun _ => 1/(X:ℚ)) (fun q (_ : q∈E) => ?_))
    · simp [div_eq_mul_inv]
    · dsimp only [fee]
      split_ifs with h
      · exact one_div_le_one_div_of_le (by exact_mod_cast hX) (by exact_mod_cast (show X≤q by omega))
      · positivity
  have h₁ := Finset.sum_sdiff hE (f:=f)
  have h₂ := Finset.sum_sdiff hE (f:=fee)
  rw [Finset.sum_filter]
  change ∑ q ∈ S, fee q ≤ _
  change ∑ q ∈ S\E, fee q ≤ _ at hreg
  rw [mul_div_assoc]
  linarith

/-- Removing factors from the reciprocal product costs at most the sum of their losses. -/
theorem inverse_product_gap {S T : Finset ℕ} (hT : T⊆S) :
    0 ≤ (∏ q ∈ T, (q:ℚ)/(q+1)) - (∏ q ∈ S, (q:ℚ)/(q+1)) ∧
    (∏ q ∈ T, (q:ℚ)/(q+1)) - (∏ q ∈ S, (q:ℚ)/(q+1)) ≤
      ∑ q ∈ S\T, (1:ℚ)/(q+1) := by
  classical
  let w (q : ℕ) : ℚ := (q:ℚ)/(q+1)
  have hpos q : 0 ≤ w q := by dsimp [w]; positivity
  have hu q : w q ≤ 1 := by dsimp [w]; apply (div_le_one (by positivity)).mpr; linarith
  have prod_le (A : Finset ℕ) : ∏ q ∈ A, w q ≤ 1 :=
    Finset.prod_le_one (fun q _ => hpos q) (fun q _ => hu q)
  have hrec (A : Finset ℕ) : 1-(∏ q ∈ A, w q) ≤ ∑ q ∈ A, (1:ℚ)/(q+1) := by
    induction A using Finset.induction_on with
    | empty => simp
    | @insert q A hq ih =>
      rw [Finset.prod_insert hq, Finset.sum_insert hq]
      have hw : 1-w q = 1/(q+1:ℚ) := by dsimp [w]; field_simp; ring
      nlinarith [mul_nonneg (sub_nonneg.mpr (hu q)) (sub_nonneg.mpr (prod_le A))]
  have hprod := Finset.prod_sdiff hT (f:=w)
  change 0 ≤ (∏ q ∈ T, w q) - (∏ q ∈ S, w q) ∧ _ ≤ _
  rw [←hprod]
  have Tpos := Finset.prod_nonneg (fun q (_ : q ∈ T) => hpos q)
  have rest := sub_nonneg.mpr (prod_le (S\T))
  constructor
  · nlinarith [mul_nonneg Tpos rest]
  · change (∏ q ∈ T, w q) - (∏ q ∈ S\T, w q)*(∏ q ∈ T, w q) ≤ _
    nlinarith [mul_nonneg (sub_nonneg.mpr (prod_le T)) rest, hrec (S\T)]

/-- A sufficiently large exponent requires a new exceptional vertex in a finite interval. -/
theorem forces_mark (K M : ℕ) (C : ℚ) (hC : 0<C) :
    ∃ L A : ℕ, M ≤ L ∧ ∀ (a : ℕ) (S E : Finset ℕ) (d : ℕ → ℕ),
      E ⊆ S → E.card ≤ K →
      (∀ q ∈ S\E, d q ∈ S ∧ (d q).Prime ∧ 5<d q ∧ q.Prime ∧ 5<q ∧
        (q+1=2*d q ∨ q+1=8*d q)) →
      Set.InjOn d (↑(S\E) : Set ℕ) →
      (∏ q ∈ S, (q:ℚ)/(q+1)) = C*(1+1/(2:ℚ)^a) →
      A < a → ∃ q ∈ E, M<q ∧ q≤L := by
  classical
  obtain ⟨F,hF,closed⟩ := finite_closed_cover M
  let Q (s : Finset ℕ) : ℚ := ∏ q ∈ s, (q:ℚ)/(q+1)
  let distance (s : Finset ℕ) : ℚ := if C<Q s then Q s-C else 1
  have hne : F.powerset.Nonempty := ⟨∅,by simp⟩
  let g := F.powerset.inf' hne distance
  have hg : 0<g := (Finset.lt_inf'_iff hne).mpr fun T _ => by
    dsimp only [distance]; split_ifs with h <;> linarith
  obtain ⟨X,hX⟩ := exists_nat_gt (4*((K:ℚ)+1)/g)
  have hXq : 0<(X:ℚ) := lt_trans (by positivity) hX
  have hXn : 0<X := by exact_mod_cast hXq
  obtain ⟨A,hAn⟩ := exists_nat_gt (4*C/g)
  have hA : 4*C/g < (2:ℚ)^A := hAn.trans (by exact_mod_cast (Nat.lt_two_pow_self (n:=A)))
  let L := max M (2*X+1)
  refine ⟨L,A,le_max_left ..,?_⟩
  intro a S E d hE hK hr hinj hbal ha
  by_contra! none
  have inside (q : ℕ) (hq : q∈S) (hl : q≤L) : q∈F := by
    induction q using Nat.strong_induction_on with
    | h q ih =>
      by_cases he : q∈E
      · exact hF q (by by_contra! hx; have := none q he hx; omega)
      · obtain ⟨hd,hp,h5,hqp,hq5,step⟩ := hr q (Finset.mem_sdiff.mpr ⟨hq,he⟩)
        have hlt : d q<q := by rcases step with h | h <;> omega
        exact closed (d q) (ih _ hlt hd (hlt.le.trans hl)) q hp h5 hqp hq5 step
  let T := S ∩ F
  have hT : T⊆S := Finset.inter_subset_left
  have hTF : T⊆F := Finset.inter_subset_right
  obtain ⟨mono,loss⟩ := inverse_product_gap hT
  change 0 ≤ Q T-Q S at mono
  change Q T-Q S ≤ _ at loss
  change Q S = _ at hbal
  have powpos : (0:ℚ)<2^a := by positivity
  have hCT : C<Q T := by
    rw [hbal] at mono
    nlinarith [div_pos hC powpos,show C*(1+1/(2:ℚ)^a)=C+C/2^a by ring]
  have hdist := Finset.inf'_le distance (Finset.mem_powerset.mpr hTF)
  change g ≤ distance T at hdist
  rw [show distance T=Q T-C by simp [distance,hCT]] at hdist
  have hrest : S\T ⊆ S.filter (fun q => 2*X+1<q) := by
    intro q hq
    obtain ⟨hs,ht⟩ := Finset.mem_sdiff.mp hq
    refine Finset.mem_filter.mpr ⟨hs,?_⟩
    by_contra! small
    exact ht (Finset.mem_inter.mpr ⟨hs,inside q hs (small.trans (le_max_right ..))⟩)
  have htail : ∑ q ∈ S\T, (1:ℚ)/(q+1) ≤ 2*E.card/X := calc
    _ ≤ ∑ q ∈ S\T, (1:ℚ)/q := Finset.sum_le_sum fun q hq => by
      have hlarge := (Finset.mem_filter.mp (hrest hq)).2
      exact one_div_le_one_div_of_le (by exact_mod_cast (show 0<q by omega)) (by linarith)
    _ ≤ _ := (Finset.sum_le_sum_of_subset_of_nonneg hrest (fun q _ _ => by positivity)).trans
      (tail_sum hE (fun q hq => ⟨(hr q hq).1, by
        have h := (hr q hq).2.2.2.2.2
        rcases h with h | h <;> omega⟩) hinj X hXn)
  have hx := (div_lt_iff₀ hg).mp hX
  have hcap : (2:ℚ)*E.card/X < g/2 := by
    apply (div_lt_iff₀ hXq).mpr
    have hk : (E.card:ℚ)≤K := by exact_mod_cast hK
    nlinarith
  have hpower := (div_lt_iff₀ hg).mp (hA.trans_le (pow_le_pow_right₀ (by norm_num) ha.le))
  have hsmall : C/(2:ℚ)^a < g/2 := by apply (div_lt_iff₀ powpos).mpr; nlinarith
  rw [hbal,show C*(1+1/(2:ℚ)^a)=C+C/2^a by ring] at loss
  linarith

/-- Disjoint witness intervals cannot all contain a mark when there are at most K. -/
theorem finite_of_mark_intervals {K : ℕ} (P : ℕ → Finset ℕ → Prop)
    (size : ∀ a E, P a E → E.card≤K)
    (progress : ∀ M : ℕ, ∃ L A : ℕ, M≤L ∧
      ∀ a E, P a E → A<a → ∃ q∈E, M<q ∧ q≤L) :
    {a | ∃ E, P a E}.Finite := by
  classical
  have count (i : ℕ) : ∀ M : ℕ, ∃ A : ℕ, ∀ a E, P a E → A<a →
      i≤(E.filter (M<·)).card := by
    induction i with
    | zero => exact fun M => ⟨0,fun _ _ _ _ => Nat.zero_le _⟩
    | succ i ih =>
      intro M
      obtain ⟨L,A,hML,newMark⟩ := progress M
      obtain ⟨B,previous⟩ := ih L
      refine ⟨max A B,?_⟩
      intro a E hP ha
      obtain ⟨q,hq,hm,hl⟩ := newMark a E hP (lt_of_le_of_lt (le_max_left ..) ha)
      have hcnt := previous a E hP (lt_of_le_of_lt (le_max_right ..) ha)
      have subset : E.filter (L<·) ⊂ E.filter (M<·) := by
        apply Finset.ssubset_iff_subset_ne.mpr
        refine ⟨Finset.monotone_filter_right _ (fun _ _ h => lt_of_le_of_lt hML h),?_⟩
        intro he
        have mem : q∈E.filter (M<·) := Finset.mem_filter.mpr ⟨hq,hm⟩
        rw [←he] at mem
        exact (not_lt_of_ge hl) (Finset.mem_filter.mp mem).2
      exact lt_of_le_of_lt hcnt (Finset.card_lt_card subset)
  obtain ⟨A,hA⟩ := count (K+1) 0
  apply (Set.finite_Iic A).subset
  rintro a ⟨E,hE⟩
  by_contra! h
  have big := (hA a E hE (show A<a by exact Nat.lt_of_not_ge h)).trans (Finset.card_filter_le ..)
  have := size a E hE
  omega


open ArithmeticFunction

private theorem omega_prod (s : Finset ℕ) (d : ℕ → ℕ) (hd : ∀ q ∈ s, d q ≠ 0) :
    cardFactors (∏ q ∈ s, d q) = ∑ q ∈ s, cardFactors (d q) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert q s hq ih =>
    rw [Finset.prod_insert hq, Finset.sum_insert hq, cardFactors_mul (hd q (by simp))
      (Finset.prod_ne_zero_iff.mpr fun r hr => hd r (by simp [hr])), ih (fun r hr => hd r (by simp [hr]))]

private theorem omega_mono {x y : ℕ} (hy : y ≠ 0) (hd : x ∣ y) :
    cardFactors x ≤ cardFactors y := by
  obtain ⟨z,rfl⟩ := hd
  rw [cardFactors_mul (left_ne_zero_of_mul hy) (right_ne_zero_of_mul hy)]
  omega

private theorem product_valuation (S : Finset ℕ) (hp : ∀ q ∈ S, q.Prime) (p : ℕ) :
    (∏ q ∈ S, q).factorization p = if p∈S then 1 else 0 := by
  rw [Nat.factorization_prod (fun q hq => (hp q hq).ne_zero), Finsupp.finsetSum_apply]
  rw [Finset.sum_congr rfl (fun q hq => by rw [(hp q hq).factorization, Finsupp.single_apply])]
  exact Finset.sum_ite_eq' S p _

/-- The number of shifts divisible by a given prime is limited by its supply in c and S. -/
theorem demand_budget {c : ℕ} {S : Finset ℕ} {d : ℕ → ℕ} (hc : c ≠ 0)
    (hp : ∀ q ∈ S, q.Prime) (hd : ∀ q ∈ S, d q ≠ 0)
    (balance : (∏ q ∈ S, d q) ∣ c * ∏ q ∈ S, q) {p : ℕ} (prime : p.Prime) :
    (S.filter (fun q => p ∣ d q)).card ≤ c.factorization p + (if p∈S then 1 else 0) := by
  classical
  have hS := Finset.prod_ne_zero_iff.mpr (fun q hq => (hp q hq).ne_zero)
  have hD := Finset.prod_ne_zero_iff.mpr hd
  have val := (Nat.factorization_le_iff_dvd hD (mul_ne_zero hc hS)).mpr balance p
  rw [Nat.factorization_mul hc hS, Finsupp.add_apply,
    product_valuation S hp,
    Nat.factorization_prod hd, Finsupp.finsetSum_apply] at val
  apply le_trans _ val
  rw [Finset.card_filter]
  apply Finset.sum_le_sum
  intro q hq
  split_ifs with h
  · exact (prime.dvd_iff_one_le_factorization (hd q hq)).mp h
  · omega

/-- Unary shifts with an ordinary predecessor are injective, including across unused branches. -/
theorem demand_inj {c : ℕ} {S : Finset ℕ} {d : ℕ → ℕ} (hc : c ≠ 0)
    (hp : ∀ q ∈ S, q.Prime) (hout : ∀ q ∈ S, ¬q ∣ c)
    (hd : ∀ q ∈ S, d q ≠ 0) (balance : (∏ q ∈ S, d q) ∣ c * ∏ q ∈ S, q)
    {q r : ℕ} (hq : q∈S) (hr : r∈S) (hm : d q∈S) (he : d q=d r) : q=r := by
  classical
  have h := demand_budget hc hp hd balance (hp _ hm)
  rw [Nat.factorization_eq_zero_of_not_dvd (hout _ hm), if_pos hm] at h
  apply Finset.card_le_one.mp h q (Finset.mem_filter.mpr ⟨hq,dvd_rfl⟩) r
    (Finset.mem_filter.mpr ⟨hr,he ▸ dvd_rfl⟩)

/-- Each composite shift spends at least one extra prime factor, and each
single outside prime spends a factor of c. -/
theorem nonordinary_demands {c : ℕ} {S : Finset ℕ} {d : ℕ → ℕ} (hc : c ≠ 0)
    (hp : ∀ q ∈ S, q.Prime) (hd : ∀ q ∈ S, d q ≠ 0)
    (balance : (∏ q ∈ S, d q) ∣ c * ∏ q ∈ S, q) :
    (S.filter (fun q => d q∉S)).card ≤
      2*cardFactors c + 2*(S.filter (fun q => d q=1)).card := by
  classical
  let V := S.filter (fun q => (d q).Prime ∧ d q∉S)
  have hV : V ⊆ S := Finset.filter_subset ..
  have div := (Finset.prod_dvd_prod_of_subset V S d hV).trans balance
  have cop : (∏ q ∈ V, d q).Coprime (∏ p ∈ S, p) := by
    apply Nat.coprime_prod_left_iff.mpr
    intro q hq
    obtain ⟨hprime,hout⟩ := (Finset.mem_filter.mp hq).2
    apply Nat.coprime_prod_right_iff.mpr
    intro r hr
    apply hprime.coprime_iff_not_dvd.mpr
    intro h
    exact hout (((hp _ hr).dvd_iff_eq hprime.ne_one).mp h ▸ hr)
  have hVC := omega_mono hc (cop.dvd_of_dvd_mul_right div)
  rw [omega_prod V d (fun q hq => hd q (hV hq))] at hVC
  have vone : ∑ q ∈ V, cardFactors (d q) = V.card := by
    exact (Finset.sum_congr rfl (fun q hq =>
      cardFactors_apply_prime (Finset.mem_filter.mp hq).2.1)).trans (by simp)
  rw [vone] at hVC
  have hsp := Finset.prod_ne_zero_iff.mpr (fun q hq => (hp q hq).ne_zero)
  have budget := omega_mono (mul_ne_zero hc hsp) balance
  rw [omega_prod S d hd, cardFactors_mul hc hsp,
    omega_prod S (fun q => q) (fun q hq => (hp q hq).ne_zero)] at budget
  have ones : ∑ q ∈ S, cardFactors q = S.card :=
    (Finset.sum_congr rfl (fun q hq => cardFactors_apply_prime (hp q hq))).trans (by simp)
  rw [ones] at budget
  have point (q : ℕ) (hq : q∈S) :
      (if d q∉S then 1 else 0) + 1 ≤ cardFactors (d q) +
      2*(if d q=1 then 1 else 0) + (if (d q).Prime ∧ d q∉S then 1 else 0) := by
    have zero := @cardFactors_eq_zero_iff_eq_zero_or_one (d q)
    have one := @cardFactors_eq_one_iff_prime (d q)
    have hz := hd q hq
    split_ifs <;> grind
  have hand := Finset.sum_le_sum point
  simp only [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one,
    ←Finset.mul_sum, ←Finset.card_filter] at hand
  dsimp only [V] at hVC
  omega

/-- All but boundedly many primes are ordinary steps of sizes one and three. -/
theorem choose_marks {c A B : ℕ} {S : Finset ℕ} (hc : c ≠ 0)
    (hp : ∀ q ∈ S, q.Prime) (hout : ∀ q ∈ S, ¬q ∣ c)
    (balance : (∏ q ∈ S, ordCompl[2] (1+q)) ∣ c * ∏ q ∈ S, q)
    (starts : (S.filter (fun q => ordCompl[2] (1+q)=1)).card ≤ A)
    (large : (S.filter (fun q => ordCompl[2] (1+q)∈S ∧ 32 ∣ 1+q)).card ≤ B) :
    ∃ E : Finset ℕ, E⊆S ∧ E.card ≤ 2*cardFactors c+2*A+B+2*(c.factorization 3+7) ∧
      (∀ q ∈ S\E, let r := ordCompl[2] (1+q)
        r∈S ∧ r.Prime ∧ 5<r ∧ q.Prime ∧ 5<q ∧ (q+1=2*r ∨ q+1=8*r)) ∧
      Set.InjOn (fun q => ordCompl[2] (1+q)) (↑(S\E) : Set ℕ) := by
  classical
  let d (q : ℕ) := ordCompl[2] (1+q)
  have hd (q : ℕ) (_ : q∈S) : d q ≠ 0 := (Nat.ordCompl_pos 2 (by omega : 1+q≠0)).ne'
  let N := S.filter (fun q => d q∉S)
  let O := S.filter (fun q => d q∈S ∧ 32∣1+q)
  let small := S.filter (·≤5)
  let third := S.filter (fun q => 3∣d q)
  let Z := small ∪ third
  let parents := S.filter (fun q => d q∈Z)
  let E := N ∪ O ∪ Z ∪ parents
  have hZ : Z⊆S := Finset.union_subset (Finset.filter_subset ..) (Finset.filter_subset ..)
  have hE : E⊆S := Finset.union_subset (Finset.union_subset
    (Finset.union_subset (Finset.filter_subset ..) (Finset.filter_subset ..)) hZ) (Finset.filter_subset ..)
  have inj {q r : ℕ} (hq : q∈S) (hr : r∈S) (hm : d q∈S) (he : d q=d r) : q=r :=
    demand_inj hc hp hout hd balance hq hr hm he
  have hsmall : small.card ≤ 6 := by
    have sub : small ⊆ Finset.range 6 :=
      fun q hq => Finset.mem_range.mpr (by have := (Finset.mem_filter.mp hq).2; omega)
    simpa using Finset.card_le_card sub
  have hthree := demand_budget hc hp hd balance Nat.prime_three
  have hthird : third.card ≤ c.factorization 3+1 := by
    change third.card ≤ _ at hthree
    split_ifs at hthree <;> omega
  have zsize : Z.card ≤ c.factorization 3+7 := by
    have h := Finset.card_union_le small third
    change Z.card ≤ _ at h
    omega
  have hparents : parents.card ≤ Z.card := by
    apply Finset.card_le_card_of_injOn d (fun q hq => (Finset.mem_filter.mp hq).2)
    intro q hq r hr he
    exact inj (Finset.mem_filter.mp hq).1 (Finset.mem_filter.mp hr).1
      (hZ (Finset.mem_filter.mp hq).2) he
  have hN := nonordinary_demands hc hp hd balance
  change N.card ≤ _ at hN
  change (S.filter (fun q => d q=1)).card≤A at starts
  change O.card≤B at large
  have get {q : ℕ} (hq : q∈S\E) : q∈S ∧ d q∈S ∧ q∉Z ∧ d q∉Z ∧ ¬32∣1+q := by
    obtain ⟨hs,he⟩ := Finset.mem_sdiff.mp hq
    have he' : q∉N ∧ q∉O ∧ q∉Z ∧ q∉parents := by
      simpa only [E, Finset.mem_union, not_or, and_assoc] using he
    have hm : d q∈S := by by_contra h; exact he'.1 (Finset.mem_filter.mpr ⟨hs,h⟩)
    exact ⟨hs,hm,he'.2.2.1,fun h => he'.2.2.2 (Finset.mem_filter.mpr ⟨hs,h⟩),
      fun h => he'.2.1 (Finset.mem_filter.mpr ⟨hs,hm,h⟩)⟩
  have modthree {q : ℕ} (hq : q∈S) (hz : q∉Z) : 5<q ∧ q%3=1 := by
    have h5 : 5<q := by
      by_contra! h
      exact hz (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hq,h⟩))
    have h1 : ¬3 ∣ 1+q := fun h => hz (Finset.mem_union_right _ (Finset.mem_filter.mpr
      ⟨hq,Nat.dvd_ordCompl_of_dvd_not_dvd h (by decide : ¬2 ∣ 3)⟩))
    have h0 : ¬3 ∣ q := fun h => by
      have he := ((hp q hq).dvd_iff_eq (by decide : 3≠1)).mp h
      omega
    exact ⟨h5,by omega⟩
  refine ⟨E,hE,?_,?_,?_⟩
  · have h1 := Finset.card_union_le N O
    have h2 := Finset.card_union_le (N∪O) Z
    have h3 := Finset.card_union_le (N∪O∪Z) parents
    change E.card ≤ _ at h3
    omega
  · intro q hq
    obtain ⟨hs,hm,hz,hrz,high⟩ := get hq
    obtain ⟨hq5,h3⟩ := modthree hs hz
    obtain ⟨hr5,hr3⟩ := modthree hm hrz
    refine ⟨hm,hp _ hm,hr5,hp q hs,hq5,?_⟩
    let j := (1+q).factorization 2
    have hv : 2^j*d q = 1+q := Nat.ordProj_mul_ordCompl_eq_self _ _
    have jpos : 0<j := Nat.prime_two.factorization_pos_of_dvd (by omega) (by
      rcases (hp q hs).eq_two_or_odd with h | h <;> omega)
    have jsmall : j<5 := by
      by_contra! h
      apply high
      exact (Nat.pow_dvd_pow 2 h).trans (Nat.ordProj_dvd (1+q) 2)
    change q+1=2*d q ∨ q+1=8*d q
    interval_cases j <;> norm_num at hv <;> omega
  · intro q hq r hr he
    exact inj (get hq).1 (get hr).1 (get hq).2.1 he

private theorem sigma_power_two_times {a c : ℕ} (ha : 0 < a) (hc : Odd c) (hc0 : c ≠ 0) :
    (∏ p ∈ (2^a*c).primeFactors, (1+p^(2^a*c).factorization p)) = (2^a+1)*(∏ p ∈ c.primeFactors, (1+p^c.factorization p)) := by
  have hb : (2:ℕ)^a ≠ 0 := pow_ne_zero _ (by decide)
  have h2c : ¬2 ∣ c := by obtain ⟨i,hi⟩ := hc; omega
  have h2 : 2 ∉ c.primeFactors := fun h => h2c (Nat.dvd_of_mem_primeFactors h)
  have hfac (p : ℕ) : (2^a*c).factorization p =
      (if 2=p then a else 0) + c.factorization p := by
    rw [Nat.factorization_mul hb hc0,Nat.prime_two.factorization_pow]
    simp [Finsupp.single_apply,eq_comm]
  have h2val : c.factorization 2 = 0 := Nat.factorization_eq_zero_of_not_dvd h2c
  rw [Nat.primeFactors_mul hb hc0,Nat.primeFactors_prime_pow ha.ne' Nat.prime_two,
    Finset.singleton_union,Finset.prod_insert h2,hfac]
  simp only [if_true,h2val,add_zero,Nat.add_comm 1 (2^a)]
  congr 1
  apply Finset.prod_congr rfl
  intro p hp
  have he : 2 ≠ p := fun e => h2 (e ▸ hp)
  rw [hfac, if_neg he, zero_add]

private theorem inverse_balance {a c : ℕ} {S : Finset ℕ} (ha : 0<a) (hc : Odd c)
    (hbal : (∏ p ∈ (2^a*c).primeFactors, (1+p^(2^a*c).factorization p))*
      (∏ q ∈ S, (1+q)) = 2*(2^a*c)*(∏ q ∈ S, q)) :
    (∏ q ∈ S, (q:ℚ)/(q+1)) =
      ((∏ p ∈ c.primeFactors, (1+p^c.factorization p) : ℕ):ℚ)/(2*c)*(1+1/(2:ℚ)^a) := by
  let σ := ∏ p ∈ c.primeFactors, (1+p^c.factorization p)
  have hcq : (0:ℚ)<c := by exact_mod_cast hc.pos
  have hq : (∏ q ∈ S, ((q:ℚ)+1)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun q _ => by positivity)
  rw [sigma_power_two_times ha hc hc.pos.ne'] at hbal
  change (2^a+1)*σ*(∏ q ∈ S, (1+q))=2*(2^a*c)*(∏ q ∈ S, q) at hbal
  have hv : ((2:ℚ)^a+1)*(σ:ℚ)*(∏ q ∈ S, ((q:ℚ)+1)) =
      2*(2^a*(c:ℚ))*(∏ q ∈ S, (q:ℚ)) := by
    simpa only [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,Nat.cast_add,Nat.cast_one,
      Nat.cast_prod,add_comm (1:ℚ)] using congrArg (Nat.cast : ℕ → ℚ) hbal
  rw [Finset.prod_div_distrib]
  change _ = (σ:ℚ)/(2*c)*(1+1/(2:ℚ)^a)
  field_simp
  nlinarith

private theorem odd_demands_divide {a c : ℕ} {S : Finset ℕ}
    (hbal : (∏ p ∈ (2^a*c).primeFactors, (1+p^(2^a*c).factorization p))*
      (∏ q ∈ S, (1+q)) = 2*(2^a*c)*(∏ q ∈ S, q)) :
    (∏ q ∈ S, ordCompl[2] (1+q)) ∣ c*∏ q ∈ S, q := by
  have hd := Finset.prod_dvd_prod_of_dvd (s:=S) (fun q : ℕ => ordCompl[2] (1+q))
    (fun q => 1+q) (fun q _ => Nat.ordCompl_dvd (1+q) 2)
  have hm := hd.trans (dvd_mul_left (∏ q ∈ S, (1+q))
    (∏ p ∈ (2^a*c).primeFactors, (1+p^(2^a*c).factorization p)))
  rw [hbal, show 2*(2^a*c)*(∏ q ∈ S, q) = 2^(a+1)*(c*∏ q ∈ S, q) by rw [pow_succ]; ac_rfl] at hm
  have hcop : (∏ q ∈ S, ordCompl[2] (1+q)).Coprime 2 :=
    Nat.coprime_prod_left_iff.mpr fun q _ =>
      (Nat.prime_two.coprime_iff_not_dvd.mpr (Nat.not_dvd_ordCompl Nat.prime_two (by omega : 1+q≠0))).symm
  exact (hcop.pow_right (a+1)).dvd_of_dvd_mul_left hm

theorem main : H1 → H2 → OMA.R_Erdos1052_erdos_1052_R2.H2 := by
  classical
  intro h₁ h₂ c hc powerful
  obtain ⟨A,starts⟩ := h₁ c hc powerful
  obtain ⟨B,large⟩ := h₂ c hc powerful
  let K := 2*ArithmeticFunction.cardFactors c+2*A+B+2*(c.factorization 3+7)
  let σ := ∏ p ∈ c.primeFactors, (1+p^c.factorization p)
  let C : ℚ := σ/(2*c : ℚ)
  have hcq : (0:ℚ)<c := by exact_mod_cast hc.pos
  have hσ : 0<σ := Finset.prod_pos fun p _ => by omega
  have hC : 0<C := by dsimp [C]; positivity
  let d (q : ℕ) := ordCompl[2] (1+q)
  let P (a : ℕ) (E : Finset ℕ) := E.card≤K ∧ ∃ S : Finset ℕ, E⊆S ∧
    (∀ q ∈ S\E, d q∈S ∧ (d q).Prime ∧ 5<d q ∧ q.Prime ∧ 5<q ∧
      (q+1=2*d q ∨ q+1=8*d q)) ∧ Set.InjOn d (↑(S\E) : Set ℕ) ∧
    (∏ q ∈ S, (q:ℚ)/(q+1))=C*(1+1/(2:ℚ)^a)
  have fin := finite_of_mark_intervals (K:=K) P (fun _ _ h => h.1) (by
    intro M
    obtain ⟨L,W,hML,h⟩ := forces_mark K M C hC
    refine ⟨L,W,hML,?_⟩
    rintro a E ⟨hk,S,hes,reg,inj,bal⟩ ha
    exact h a S E d hes hk reg inj bal ha)
  apply fin.subset
  rintro a ⟨ha,S,hs,hsub,hp,bal⟩
  have sa := starts a S ha hs hsub hp bal
  have sb := large a S ha hs hsub hp bal
  have hd := odd_demands_divide bal
  obtain ⟨E,hE,hK,hreg,hinj⟩ := choose_marks hc.pos.ne' (fun q hq => (hp q hq).1)
    (fun q hq h => (hp q hq).2 (dvd_mul_of_dvd_right h _)) hd sa sb
  exact ⟨E,hK,S,hE,hreg,hinj,inverse_balance (by omega) hc bal⟩

end OMA.R_Erdos1052_erdos_1052_R2_H2_R3
