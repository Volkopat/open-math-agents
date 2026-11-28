import OMAStatements.S_oeis_a007850

/-!
# Completing a squarefree core with its two largest primes
Credit: @Pixelstorm44. The positive-multiplier characterization is due to
Grau and Oller-Marcén (J. Integer Seq. 15 (2012), 12.4.1).
The Lean proof of that characterization below is from @frido22's R1.
The two-prime completion and the divisor-pair reduction follow it.
-/

namespace OMA.R_oeis_a007850_R2

open Finset OMA.S_oeis_a007850

/-- All prime - factor summands except the `p` term vanish modulo `p`. -/
lemma derivative_at_prime {n p : ℕ} (hp : p ∈ n.primeFactors) :
    arithDeriv n ≡ n.factorization p * (n / p) [MOD p] := by
  let f := fun q => n.factorization q * (n / q)
  have div : p ∣ ∑ q ∈ n.primeFactors.erase p, f q := by
    apply Finset.dvd_sum
    intro q hq
    obtain ⟨ne, mem⟩ := Finset.mem_erase.mp hq
    have pq := Nat.Prime.dvd_mul_of_dvd_ne ne.symm (Nat.prime_of_mem_primeFactors hp)
      (Nat.prime_of_mem_primeFactors mem) (Nat.dvd_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors mem)
    apply dvd_mul_of_dvd_right _ (n.factorization q)
    exact (Nat.dvd_div_iff_mul_dvd (Nat.dvd_of_mem_primeFactors mem)).mpr (by simpa [Nat.mul_comm] using pq)
  change (∑ q ∈ n.primeFactors, f q) ≡ f p [MOD p]
  rw [← Finset.sum_erase_add _ f hp]
  simpa only [zero_add] using (Nat.modEq_zero_iff_dvd.mpr div).add_right (f p)

lemma giuga_squarefree {n : ℕ} (h : IsGiuga n) : Squarefree n := by
  obtain ⟨hn, _, cond⟩ := h
  apply Nat.squarefree_iff_prime_squarefree.mpr
  intro p prime repeated
  have dp : p ∣ n := (dvd_mul_right p p).trans repeated
  have dn := (Nat.dvd_div_iff_mul_dvd dp).mpr repeated
  have pos : 0 < n / p := Nat.div_pos (Nat.le_of_dvd (by omega) dp) prime.pos
  have gap := cond p (Nat.mem_primeFactors.mpr ⟨prime, dp, by omega⟩)
  have d := Nat.dvd_sub dn gap
  have : p ∣ 1 := by rwa [show n / p - (n / p - 1) = 1 by omega] at d
  exact prime.not_dvd_one this

lemma squarefree_of_residue {n a : ℕ} (hn : 0 < n) (eq : arithDeriv n = a * n + 1) : Squarefree n := by
  apply Nat.squarefree_iff_prime_squarefree.mpr
  intro p prime repeated
  have dp : p ∣ n := (dvd_mul_right p p).trans repeated
  have dn := (Nat.dvd_div_iff_mul_dvd dp).mpr repeated
  have res := derivative_at_prime (Nat.mem_primeFactors.mpr ⟨prime, dp, hn.ne'⟩)
  have zd := (Nat.modEq_zero_iff_dvd.mpr (dvd_mul_of_dvd_right dn (n.factorization p)))
  have dz := Nat.modEq_zero_iff_dvd.mp (res.trans zd)
  have da : p ∣ a * n := dvd_mul_of_dvd_right dp a
  rw [eq] at dz
  exact prime.not_dvd_one (by simpa using (Nat.dvd_sub dz da))

private lemma derivative_of_squarefree {n : ℕ} (sf : Squarefree n) :
    arithDeriv n = ∑ p ∈ n.primeFactors, n / p := by
  apply sum_congr rfl
  intro p mem
  simp [Nat.factorization_eq_one_of_squarefree sf (Nat.prime_of_mem_primeFactors mem)
    (Nat.dvd_of_mem_primeFactors mem)]

private lemma derivative_at_prime_of_squarefree {n p : ℕ} (sf : Squarefree n) (mem : p ∈ n.primeFactors) :
    arithDeriv n ≡ n / p [MOD p] := by
  simpa [Nat.factorization_eq_one_of_squarefree sf (Nat.prime_of_mem_primeFactors mem)
    (Nat.dvd_of_mem_primeFactors mem)] using derivative_at_prime mem

/-- The positive - multiplier characterization of Grau and Oller - Marcén. -/
lemma giuga_iff_multiplier {n : ℕ} (hn : 0 < n) :
    IsGiuga n ↔ ∃ a : ℕ, 0 < a ∧ arithDeriv n = a * n + 1 := by
  constructor
  · intro h
    have sf := giuga_squarefree h
    obtain ⟨large, composite, cond⟩ := h
    obtain ⟨p, mem⟩ := Nat.nonempty_primeFactors.mpr large
    have prime := Nat.prime_of_mem_primeFactors mem
    have dp := Nat.dvd_of_mem_primeFactors mem
    have qpos := Nat.div_pos (Nat.le_of_mem_primeFactors mem) prime.pos
    have qbig : 1 < n / p := by
      by_contra! hq
      have eq := Nat.div_mul_cancel dp
      rw [show n / p = 1 by omega, one_mul] at eq
      exact composite (eq ▸ prime)
    have big : 1 < arithDeriv n := by
      rw [derivative_of_squarefree sf]
      exact qbig.trans_le (single_le_sum (fun _ _ => Nat.zero_le _) mem)
    have div : n ∣ arithDeriv n - 1 := by
      have pos : arithDeriv n - 1 ≠ 0 := by omega
      nth_rw 1 [← Nat.prod_primeFactors_of_squarefree sf]
      rw [Nat.prod_primeFactors_dvd_iff pos]
      intro q hq
      have qp := Nat.prime_of_mem_primeFactors hq
      apply Nat.mem_primeFactors.mpr
      refine ⟨qp, ?_, pos⟩
      have qpos := Nat.div_pos (Nat.le_of_mem_primeFactors hq) qp.pos
      have rem := (Nat.modEq_iff_dvd' (show 1 ≤ n / q by omega)).mpr (cond q hq)
      exact (rem.trans (derivative_at_prime_of_squarefree sf hq).symm).dvd'
    obtain ⟨a, eq⟩ := div
    refine ⟨a, ?_, ?_⟩
    · by_contra! ha
      simp [show a = 0 by omega] at eq
      omega
    · rw [Nat.mul_comm] at eq
      omega
  · rintro ⟨a, ha, eq⟩
    have large : 1 < n := by
      by_contra! hn'
      simp_all [show n = 1 by omega, arithDeriv]
    have composite : ¬ n.Prime := by
      intro prime
      have val : arithDeriv n = 1 := by simp [arithDeriv, prime, prime.pos]
      have := Nat.mul_pos ha hn
      omega
    refine ⟨large, composite, ?_⟩
    intro p mem
    have atp := derivative_at_prime_of_squarefree (squarefree_of_residue hn eq) mem
    have da : p ∣ a * n := dvd_mul_of_dvd_right (Nat.dvd_of_mem_primeFactors mem) a
    rw [eq] at atp
    have res : 1 ≡ a * n + 1 [MOD p] := by
      simpa using ((Nat.modEq_zero_iff_dvd.mpr da).symm.add_right 1)
    exact (res.trans atp).dvd'

/-- Strip the largest prime from a squarefree integer. -/
lemma strip_largest {n : ℕ} (hn : 1 < n) (sf : Squarefree n) :
    ∃ m p : ℕ, n = m*p ∧ 0 < m ∧ p.Prime ∧ Squarefree m ∧
      ∀ r ∈ m.primeFactors, r < p := by
  let p := n.primeFactors.max' (Nat.nonempty_primeFactors.mpr hn)
  have mem : p ∈ n.primeFactors := Finset.max'_mem _ _
  obtain ⟨hp, hd, _⟩ := Nat.mem_primeFactors.mp mem
  let m := n / p
  have e : m*p = n := Nat.div_mul_cancel hd
  have s : Squarefree (m*p) := e ▸ sf
  have cop := (Nat.coprime_of_squarefree_mul s).symm
  have hm : 0 < m := Nat.div_pos (Nat.le_of_mem_primeFactors mem) hp.pos
  refine ⟨m, p, e.symm, hm, hp, s.squarefree_of_dvd (dvd_mul_right m p), ?_⟩
  intro r hr
  have memn : r ∈ n.primeFactors := by
    rw [← e, Nat.primeFactors_mul hm.ne' hp.ne_zero]
    exact Finset.mem_union_left _ hr
  refine lt_of_le_of_ne (Finset.le_max' _ _ memn) ?_
  rintro rfl
  exact (hp.coprime_iff_not_dvd.mp cop) (Nat.dvd_of_mem_primeFactors hr)

/-- The product rule when appending a fresh prime. -/
lemma append_prime {m p : ℕ} (hm : 0 < m) (hp : p.Prime) (sf : Squarefree (m*p)) :
    arithDeriv (m*p) = arithDeriv m*p + m := by
  have sm := sf.squarefree_of_dvd (dvd_mul_right m p)
  have fresh : p ∉ m.primeFactors := fun h =>
    (hp.coprime_iff_not_dvd.mp (Nat.coprime_of_squarefree_mul sf).symm)
      (Nat.dvd_of_mem_primeFactors h)
  rw [derivative_of_squarefree sf, derivative_of_squarefree sm, Nat.primeFactors_mul hm.ne' hp.ne_zero,
    hp.primeFactors, Finset.union_singleton, Finset.sum_insert fresh, Nat.mul_div_cancel _ hp.pos,
    Finset.sum_mul, add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro r hr
  rw [Nat.mul_comm m p, Nat.mul_div_assoc _ (Nat.dvd_of_mem_primeFactors hr), Nat.mul_comm]

/-- The gap to the next multiple of the core is determined before the two
largest primes are known. Their transformed values give complementary divisors. -/
lemma core_data {m p q a : ℕ} (hm : 0 < m) (hp : 2 ≤ p) (hpq : p < q)
    (ha : 2 ≤ a)
    (eqn : (arithDeriv m*p + m)*q + m*p = a*(m*p*q)+1) :
    m < arithDeriv m ∧
    let d := m - arithDeriv m % m
    ∃ u v : ℕ, 0 < u ∧ u < v ∧ u*v = m^2-d ∧
      m+u = d*p ∧ m+v = d*q := by
  let D := arithDeriv m
  change (D*p+m)*q+m*p = a*(m*p*q)+1 at eqn
  have pqpos : 0 < p*q := Nat.mul_pos (by omega) (by omega)
  have excess : D*(p*q) < (a*m)*(p*q) := by
    nlinarith [show 1 < m*p by nlinarith]
  have lower : D < a*m := (Nat.mul_lt_mul_right pqpos).mp excess
  let d := a*m-D
  have gap : D+d = a*m := Nat.add_sub_of_le lower.le
  have basic : d*(p*q)+1 = m*(p+q) := by
    nlinarith only [eqn, congrArg (· * (p*q)) gap]
  have cap : p+q ≤ p*q := by nlinarith only [hpq, Nat.mul_le_mul_right q hp]
  have dm : d < m := (Nat.mul_lt_mul_right pqpos).mp (by
    have := Nat.mul_le_mul_left m cap
    omega)
  have dpos : 0 < d := by omega
  obtain ⟨b, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show a ≠ 0 by omega)
  have Dform : D = (m-d) + m*b := by
    rw [Nat.succ_mul, Nat.mul_comm b m] at gap
    omega
  have canon : m - D % m = d := by
    rw [Dform, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
    omega
  have big : m < D := by
    have bm := Nat.mul_le_mul_left m (show 1 ≤ b by omega)
    simp only [Nat.mul_one] at bm
    omega
  refine ⟨big, ?_⟩
  change ∃ u v : ℕ, 0 < u ∧ u < v ∧ u*v = m^2-(m-D%m) ∧
    m+u = (m-D%m)*p ∧ m+v = (m-D%m)*q
  rw [canon]
  have posp : m < d*p := (Nat.mul_lt_mul_right (show 0 < q by omega)).mp (by
    nlinarith only [basic, show 1 < m*p by nlinarith])
  have order := Nat.mul_lt_mul_of_pos_left hpq dpos
  let u := d*p-m
  let v := d*q-m
  have eu : m+u = d*p := Nat.add_sub_of_le posp.le
  have ev : m+v = d*q := Nat.add_sub_of_le (posp.trans order).le
  refine ⟨u,v,by omega,by omega,?_,eu,ev⟩
  have product : u*v+d = m^2 := by
    nlinarith only [congrArg (· * (m+v)) eu, congrArg (· * (d*p)) ev,
      congrArg (· * d) basic, congrArg (· * m) eu, congrArg (· * m) ev]
  omega

/-- The search for the smaller new prime is confined to m < dp < 2m. -/
lemma completion_window {m d p u v : ℕ} (hm : 0 < m) (hd : 0 < d)
    (pos : 0 < u) (ord : u < v) (prod : u*v = m^2-d) (ep : m+u = d*p) :
    m < d*p ∧ d*p < 2*m := by
  have small : u < m := by
    by_contra! h
    have hu := Nat.mul_le_mul h (le_trans h ord.le)
    have mm : 0 < m^2 := by positivity
    rw [prod, ← sq] at hu
    omega
  omega

/-- A squarefree core is coprime to its gap. Locally its derivative is
m/r modulo r, which is nonzero at every prime r dividing m. -/
lemma gap_coprime {m : ℕ} (hm : 0 < m) (sf : Squarefree m) :
    (m - arithDeriv m % m).Coprime m := by
  let D := arithDeriv m
  let d := m-D%m
  have gap : D+d = (D/m+1)*m := by
    have rem := Nat.mod_lt D hm
    have recov := Nat.mod_add_div D m
    dsimp [d]
    rw [Nat.add_mul, Nat.mul_comm (D/m) m, one_mul]
    omega
  apply Nat.coprime_of_dvd
  intro r prime rd rm
  change r ∣ d at rd
  have sumdvd : r ∣ D+d := gap ▸ dvd_mul_of_dvd_right rm _
  have rD : r ∣ D := by simpa using Nat.dvd_sub sumdvd rd
  have mem := Nat.mem_primeFactors.mpr ⟨prime, rm, hm.ne'⟩
  have vanishes := (derivative_at_prime_of_squarefree sf mem).symm.trans
    (Nat.modEq_zero_iff_dvd.mpr rD)
  have repeated := (Nat.dvd_div_iff_mul_dvd rm).mp (Nat.modEq_zero_iff_dvd.mp vanishes)
  exact Nat.squarefree_iff_prime_squarefree.mp sf r prime repeated

/-- Checking the residue of the smaller divisor automatically checks its partner. -/
lemma complementary_residue {m d u v : ℕ} (cop : d.Coprime m) (small : d ≤ m^2)
    (product : u*v = m^2-d) (residue : d ∣ m+u) : d ∣ m+v := by
  apply cop.dvd_mul_left.mp
  have prod : u*v+d = m^2 := by omega
  have eq : m*(m+v) = (m+u)*v+d := by nlinarith only [prod]
  rw [eq]
  exact dvd_add (dvd_mul_of_dvd_left residue _) (dvd_refl _)

/-- Conversely, a prime pair passing the divisor test yields a Giuga number.
Its multiplier is determined by integer division on the smaller core. -/
lemma complete_pair {m d p q u v : ℕ} (hm : 0 < m) (sf : Squarefree m)
    (gap : d = m - arithDeriv m % m) (hp : p.Prime) (hq : q.Prime)
    (ord : p < q) (top : ∀ r ∈ m.primeFactors, r < p)
    (product : u*v = m^2-d) (ep : m+u = d*p) (eq : m+v = d*q) :
    IsGiuga (m*p*q) ∧
    arithDeriv (m*p*q) = (arithDeriv m / m + 1)*(m*p*q)+1 := by
  let D := arithDeriv m
  have rem := Nat.mod_lt D hm
  change d = m-D%m at gap
  have hd : 0 < d := by omega
  have dl : d ≤ m^2 := by nlinarith only [show d ≤ m by omega, hm, Nat.mul_le_mul_left m hm]
  have prod : u*v+d = m^2 := by omega
  have balance : d*(p*q)+1 = m*(p+q) := by
    apply Nat.eq_of_mul_eq_mul_left hd
    nlinarith only [prod, congrArg (· * (m+v)) ep, congrArg (· * (d*p)) eq,
      congrArg (· * m) ep, congrArg (· * m) eq]
  have s1 : Squarefree (m*p) := by
    apply Nat.squarefree_mul_iff.mpr
    refine ⟨(hp.coprime_iff_not_dvd.mpr ?_).symm, sf, hp.squarefree⟩
    intro h
    exact lt_irrefl _ (top p (Nat.mem_primeFactors.mpr ⟨hp,h,hm.ne'⟩))
  have s2 : Squarefree (m*p*q) := by
    apply Nat.squarefree_mul_iff.mpr
    refine ⟨(hq.coprime_iff_not_dvd.mpr ?_).symm, s1, hq.squarefree⟩
    intro h
    rcases hq.dvd_mul.mp h with h | h
    · exact (top q (Nat.mem_primeFactors.mpr ⟨hq,h,hm.ne'⟩)).not_ge ord.le
    · exact ord.not_ge (Nat.le_of_dvd hp.pos h)
  have multiple : D+d = (D/m+1)*m := by
    have h := Nat.mod_add_div D m
    rw [Nat.add_mul, Nat.mul_comm (D/m) m, one_mul]
    omega
  have deriv : arithDeriv (m*p*q) = (D/m+1)*(m*p*q)+1 := by
    rw [append_prime (Nat.mul_pos hm hp.pos) hq s2, append_prime hm hp s1]
    change (D*p+m)*q+m*p = (D/m+1)*(m*p*q)+1
    nlinarith only [balance, congrArg (· * (p*q)) multiple]
  exact ⟨(giuga_iff_multiplier (Nat.mul_pos (Nat.mul_pos hm hp.pos) hq.pos)).mpr
    ⟨D/m+1, Nat.zero_lt_succ _, deriv⟩, deriv⟩

/-- The single residue test and the two primality tests suffice. In particular,
a failing instance of either exclusion below would yield an actual solution
of the derivative equation with the multiplier displayed here. -/
lemma lift_divisors {m d u v : ℕ} (hm : 0 < m) (sf : Squarefree m)
    (gap : d = m - arithDeriv m % m) (huv : u < v)
    (product : u*v = m^2-d) (residue : d ∣ m+u)
    (top : ∀ r ∈ m.primeFactors, r < (m+u)/d)
    (hp : ((m+u)/d).Prime) (hq : ((m+v)/d).Prime) :
    let n := m*((m+u)/d)*((m+v)/d)
    IsGiuga n ∧ arithDeriv n = (arithDeriv m/m+1)*n+1 := by
  have small : d ≤ m^2 := by
    nlinarith only [show d ≤ m by omega, hm, Nat.mul_le_mul_left m hm]
  have other := complementary_residue (gap ▸ gap_coprime hm sf) small product residue
  have ep : m+u = d*((m+u)/d) := (Nat.mul_div_cancel' residue).symm
  have eq : m+v = d*((m+v)/d) := (Nat.mul_div_cancel' other).symm
  have ord : (m+u)/d < (m+v)/d := by
    by_contra! h
    have le := Nat.mul_le_mul_left d h
    omega
  exact complete_pair hm sf gap hp hq ord top product ep eq

/-- Unit gap: factor (m-1)(m+1). A completion requires the two
divisors translated by m to be the two largest primes. -/
def H1 : Prop := ∀ m : ℕ, 0 < m → Squarefree m → m < arithDeriv m →
  m - arithDeriv m % m = 1 → ∀ u v : ℕ, 0 < u → u < v → u*v = m^2-1 →
  (∀ r ∈ m.primeFactors, r < m+u) → (m+u).Prime → ¬ (m+v).Prime

/-- Larger gap: retain only complementary divisors in the required residue
class and above the cutoff from the largest prime of the core. -/
def H2 : Prop := ∀ m : ℕ, 0 < m → Squarefree m → m < arithDeriv m →
  let d := m - arithDeriv m % m
  2 ≤ d → ∀ u v : ℕ, 0 < u → u < v → u*v = m^2-d →
  d ∣ m+u → (∀ r ∈ m.primeFactors, r < (m+u)/d) →
  ((m+u)/d).Prime → ¬ ((m+v)/d).Prime

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a007850.main := by
  intro unitGap largerGap n hn
  constructor
  · intro giuga
    obtain ⟨a, ha, eqn⟩ := (giuga_iff_multiplier hn).mp giuga
    by_cases one : a = 1
    · simpa [one] using eqn
    exfalso
    obtain ⟨t, q, en, ht, hq, st, top⟩ := strip_largest giuga.1 (giuga_squarefree giuga)
    have ht' : 1 < t := by
      by_contra! small
      have enq : n = q := by simpa [show t=1 by omega] using en
      exact giuga.2.1 (enq ▸ hq)
    obtain ⟨m, p, et, hm, hp, sm, first⟩ := strip_largest ht' st
    have hpq : p < q := top p (Nat.mem_primeFactors.mpr
      ⟨hp, et ▸ dvd_mul_left p m, ht.ne'⟩)
    have rule := append_prime ht hq (en ▸ giuga_squarefree giuga)
    have rule' := append_prime hm hp (et ▸ st)
    rw [en, rule, et, rule'] at eqn
    obtain ⟨big, u, v, hu, huv, prod, ep, eq⟩ :=
      core_data hm hp.two_le hpq (by omega) eqn
    let d := m - arithDeriv m % m
    change m+u = d*p at ep
    change m+v = d*q at eq
    have hd : 0 < d := by dsimp [d]; have := Nat.mod_lt (arithDeriv m) hm; omega
    by_cases unit : d = 1
    · have Ep : m+u = p := by simpa [unit] using ep
      have Eq : m+v = q := by simpa [unit] using eq
      apply unitGap m hm sm big unit u v hu huv (by simpa only [← unit] using prod)
      · simpa only [Ep] using first
      · simpa only [Ep] using hp
      · simpa only [Eq] using hq
    · have Ep := Nat.div_eq_of_eq_mul_right hd ep
      have Eq := Nat.div_eq_of_eq_mul_right hd eq
      apply largerGap m hm sm big (show 2 ≤ d by omega) u v hu huv prod
        ⟨p,ep⟩
      · change ∀ r ∈ m.primeFactors, r < (m+u)/d
        simpa only [Ep] using first
      · change ((m+u)/d).Prime
        simpa only [Ep] using hp
      · change ((m+v)/d).Prime
        simpa only [Eq] using hq
  · intro eqn
    exact (giuga_iff_multiplier hn).mpr ⟨1, by decide, by simpa using eqn⟩

end OMA.R_oeis_a007850_R2
