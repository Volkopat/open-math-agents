import FormalConjectures.Wikipedia.AgohGiuga

/-!
# Lower bound on the decimal digit length of strong Giuga numbers

We prove that every strong Giuga number has at least 13,000 decimal digits, following
the normal-set framework of Giuga and Borwein–Borwein–Borwein–Girgensohn combined with
a 3-case edge-matching dual certificate verified by kernel reduction.
-/

-- Problem: Agoh-Giuga conjecture —  13000 le digits length of isStrongGiuga
-- Upstream: formal-conjectures FormalConjectures/Wikipedia/AgohGiuga.lean:254 (declaration AgohGiuga.agoh_giuga.variants._13000_le_digits_length_of_isStrongGiuga)
-- Credit: @<your GitHub handle> (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace AgohGiugaSolution

open scoped Nat

/- ### Part 1: Giuga's elementary characterization of strong Giuga numbers -/

private lemma sum_pow_zmod_eq_zero_of_not_dvd {p k : ℕ} [Fact p.Prime] (hk : ¬ (p - 1 ∣ k)) :
    ∑ x : ZMod p, x ^ k = 0 := by
  have hp : p.Prime := Fact.out
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
  have hord : orderOf g = p - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card,
      ZMod.card_units_eq_totient, Nat.totient_prime hp]
  have hgk_ne : (g : ZMod p) ^ k ≠ 1 := by
    intro h
    have h1 : g ^ k = 1 := by
      ext
      simpa [Units.val_pow_eq_pow_val] using h
    rw [← orderOf_dvd_iff_pow_eq_one, hord] at h1
    exact hk h1
  have hmul : (g : ZMod p) ^ k * ∑ x : ZMod p, x ^ k = ∑ x : ZMod p, x ^ k := by
    rw [Finset.mul_sum]
    have hbij : ∑ x : ZMod p, ((g : ZMod p) * x) ^ k = ∑ x : ZMod p, x ^ k := by
      refine Fintype.sum_bijective (fun x : ZMod p => (g : ZMod p) * x) ?_ _ _ (fun _ => rfl)
      exact (Units.mulLeft g).bijective
    simpa [mul_pow] using hbij
  have hsub : ((g : ZMod p) ^ k - 1) * ∑ x : ZMod p, x ^ k = 0 := by
    rw [sub_mul, one_mul, hmul, sub_self]
  exact (mul_eq_zero.mp hsub).resolve_left (sub_ne_zero.mpr hgk_ne)

private lemma sum_pow_zmod_eq_neg_one_of_dvd {p k : ℕ} [Fact p.Prime] (hk0 : 0 < k)
    (hk : p - 1 ∣ k) :
    ∑ x : ZMod p, x ^ k = -1 := by
  have hp : p.Prime := Fact.out
  obtain ⟨m, rfl⟩ := hk
  have hterm : ∀ x : ZMod p, x ^ ((p - 1) * m) = if x = 0 then 0 else 1 := by
    intro x
    split_ifs with hx
    · subst hx
      exact zero_pow (Nat.ne_of_gt hk0)
    · rw [pow_mul, ZMod.pow_card_sub_one_eq_one hx, one_pow]
  simp_rw [hterm, Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const, nsmul_eq_mul,
    mul_one]
  have hcard : (Finset.univ.filter (fun x : ZMod p => ¬ x = 0)).card = p - 1 := by
    have h1 : Finset.univ.filter (fun x : ZMod p => ¬ x = 0) = Finset.univ.erase (0 : ZMod p) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, and_true]
    rw [h1, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, ZMod.card]
  rw [hcard, Nat.cast_sub hp.one_lt.le, ZMod.natCast_self, Nat.cast_one, zero_sub]

private lemma sum_Ioo_zmod_eq {a p : ℕ} (ha : 1 < a) (hp : p ∣ a) :
    ((∑ i ∈ Finset.Ioo 0 a, i ^ (a - 1) : ℕ) : ZMod p) =
      ((a / p : ℕ) : ZMod p) * ∑ r ∈ Finset.range p, (r : ZMod p) ^ (a - 1) := by
  have ha1 : a - 1 ≠ 0 := by omega
  have hIoo : ∑ i ∈ Finset.Ioo 0 a, i ^ (a - 1) = ∑ i ∈ Finset.range a, i ^ (a - 1) := by
    rw [Finset.range_eq_Ico]
    have hsub : Finset.Ioo 0 a = (Finset.Ico 0 a).erase 0 := by
      ext x
      simp [Finset.mem_Ioo, Finset.mem_erase]
      omega
    rw [hsub]
    have h0 : (0 : ℕ) ∈ Finset.Ico 0 a := by simp; omega
    rw [← Finset.add_sum_erase _ _ h0, zero_pow ha1, zero_add]
  rw [hIoo, Nat.cast_sum]
  obtain ⟨m, hm⟩ := hp
  have hm_eq : a / p = m := by
    by_cases hp0 : p = 0
    · subst hp0; simp at hm; omega
    · rw [hm, Nat.mul_div_cancel_left m (Nat.pos_of_ne_zero hp0)]
  rw [hm_eq]
  have hsum : ∀ n : ℕ,
      ∑ i ∈ Finset.range (p * n), ((i : ℕ) : ZMod p) ^ (a - 1) =
        (n : ZMod p) * ∑ r ∈ Finset.range p, (r : ZMod p) ^ (a - 1) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Nat.mul_succ, Finset.sum_range_add, ih, Nat.cast_succ, add_mul, one_mul]
      congr 1
      refine Finset.sum_congr rfl fun r _ => ?_
      simp [Nat.cast_add, Nat.cast_mul]
  simpa [hm] using hsum m

private lemma sum_range_zmod_eq_univ (p k : ℕ) [NeZero p] :
    ∑ r ∈ Finset.range p, (r : ZMod p) ^ k = ∑ x : ZMod p, x ^ k := by
  refine Finset.sum_bij (fun r _ => (r : ZMod p)) (fun _ _ => Finset.mem_univ _) ?_ ?_ (fun _ _ => rfl)
  · intro r₁ hr₁ r₂ hr₂ h
    rw [Finset.mem_range] at hr₁ hr₂
    have := congr_arg ZMod.val h
    simpa [ZMod.val_natCast_of_lt hr₁, ZMod.val_natCast_of_lt hr₂] using this
  · intro x _
    exact ⟨x.val, Finset.mem_range.mpr x.val_lt, ZMod.natCast_zmod_val x⟩

private lemma strongGiuga_props {a : ℕ} (ha : AgohGiuga.IsStrongGiuga a) :
    (1 < a) ∧
    (Squarefree a) ∧
    (∀ p ∈ a.primeFactors, p % 2 = 1 ∧ 3 ≤ p) ∧
    (∀ p ∈ a.primeFactors, ∀ q ∈ a.primeFactors, ¬ (p ∣ q - 1)) ∧
    (a + 1 ≤ ∑ p ∈ a.primeFactors, a / p) := by
  obtain ⟨hcomp, hdvd_sum⟩ := ha
  have ha1 : 1 < a := hcomp.1
  have ha_not_prime : ¬ a.Prime := hcomp.2
  have ha0 : a ≠ 0 := by omega
  have h1 : ∀ p ∈ a.primeFactors, (p - 1) ∣ (a - 1) ∧ p ∣ (a / p - 1) := by
    intro p hp_mem
    have hp : p.Prime := Nat.prime_of_mem_primeFactors hp_mem
    have hpa : p ∣ a := Nat.dvd_of_mem_primeFactors hp_mem
    have : Fact p.Prime := ⟨hp⟩
    have hzero : ((1 + ∑ i ∈ Finset.Ioo 0 a, i ^ (a - 1) : ℕ) : ZMod p) = 0 :=
      (ZMod.natCast_eq_zero_iff _ _).mpr (hpa.trans hdvd_sum)
    rw [Nat.cast_add, Nat.cast_one, sum_Ioo_zmod_eq ha1 hpa, sum_range_zmod_eq_univ] at hzero
    have hpm1 : (p - 1) ∣ (a - 1) := by
      by_contra hnot
      rw [sum_pow_zmod_eq_zero_of_not_dvd hnot, mul_zero, add_zero] at hzero
      exact one_ne_zero hzero
    refine ⟨hpm1, ?_⟩
    rw [sum_pow_zmod_eq_neg_one_of_dvd (by omega) hpm1] at hzero
    have hap_pos : 1 ≤ a / p := Nat.div_pos (Nat.le_of_dvd (by omega) hpa) hp.pos
    have hcast : ((a / p - 1 : ℕ) : ZMod p) = 0 := by
      rw [Nat.cast_sub hap_pos, Nat.cast_one]
      linear_combination -hzero
    exact (ZMod.natCast_eq_zero_iff _ _).mp hcast
  have hpm1 : ∀ p ∈ a.primeFactors, (p - 1) ∣ (a - 1) := fun p hp => (h1 p hp).1
  have hgiuga : ∀ p ∈ a.primeFactors, p ∣ (a / p - 1) := fun p hp => (h1 p hp).2
  have hsq : Squarefree a := by
    rw [Nat.squarefree_iff_prime_squarefree]
    intro p hp hp2
    have hpa : p ∣ a := (dvd_mul_left p p).trans (by simpa [sq] using hp2)
    have hmem : p ∈ a.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpa, ha0⟩
    have hdiv1 : p ∣ a / p - 1 := hgiuga p hmem
    have hdiv2 : p ∣ a / p := by
      obtain ⟨k, hk⟩ := hp2
      have : a / p = p * k := by
        rw [hk, mul_assoc, Nat.mul_div_cancel_left _ hp.pos]
      exact ⟨k, this⟩
    have hap_pos : 1 ≤ a / p := Nat.div_pos (Nat.le_of_dvd (by omega) hpa) hp.pos
    have : p ∣ 1 := by
      have hsub := Nat.dvd_sub hdiv2 hdiv1
      rwa [Nat.sub_sub_self hap_pos] at hsub
    exact hp.not_dvd_one this
  have hprod : ∏ p ∈ a.primeFactors, p = a := Nat.prod_primeFactors_of_squarefree hsq
  have hcard2 : 2 ≤ a.primeFactors.card := by
    by_contra hlt
    have hlt' : a.primeFactors.card < 2 := Nat.lt_of_not_ge hlt
    interval_cases hc : a.primeFactors.card
    · rw [Finset.card_eq_zero] at hc
      rw [hc, Finset.prod_empty] at hprod
      omega
    · obtain ⟨p, hp⟩ := Finset.card_eq_one.mp hc
      have hmem : p ∈ a.primeFactors := by rw [hp]; simp
      have hprime : p.Prime := Nat.prime_of_mem_primeFactors hmem
      rw [hp, Finset.prod_singleton] at hprod
      exact ha_not_prime (hprod ▸ hprime)
  have hodd_all : ∀ p ∈ a.primeFactors, p % 2 = 1 ∧ 3 ≤ p := by
    have h2not : 2 ∉ a.primeFactors := by
      intro h2
      obtain ⟨p, hp_mem, hp_ne⟩ := Finset.exists_mem_ne (by omega : 1 < a.primeFactors.card) 2
      have hp : p.Prime := Nat.prime_of_mem_primeFactors hp_mem
      have hp_odd : 2 ∣ p - 1 := by
        rcases hp.eq_two_or_odd with rfl | hodd
        · exact absurd rfl hp_ne
        · omega
      have h2_am1 : 2 ∣ a - 1 := hp_odd.trans (hpm1 p hp_mem)
      have h2_a : 2 ∣ a := Nat.dvd_of_mem_primeFactors h2
      have : 2 ∣ 1 := by
        have := Nat.dvd_sub h2_a h2_am1
        rwa [Nat.sub_sub_self (by omega)] at this
      omega
    intro p hp_mem
    have hp : p.Prime := Nat.prime_of_mem_primeFactors hp_mem
    have hp_ne2 : p ≠ 2 := fun h => h2not (h ▸ hp_mem)
    rcases hp.eq_two_or_odd with rfl | hodd
    · exact absurd rfl hp_ne2
    · exact ⟨hodd, by have := hp.two_le; omega⟩
  have hnorm : ∀ p ∈ a.primeFactors, ∀ q ∈ a.primeFactors, ¬ (p ∣ q - 1) := by
    intro p hp q hq hpq
    have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hp_a : p ∣ a := Nat.dvd_of_mem_primeFactors hp
    have hp_am1 : p ∣ a - 1 := hpq.trans (hpm1 q hq)
    have : p ∣ 1 := by
      have := Nat.dvd_sub hp_a hp_am1
      rwa [Nat.sub_sub_self (by omega)] at this
    exact hp_prime.not_dvd_one this
  have hsum_ge : a + 1 ≤ ∑ p ∈ a.primeFactors, a / p := by
    have hge2 : 2 ≤ ∑ p ∈ a.primeFactors, a / p := by
      obtain ⟨p₁, hp₁, p₂, hp₂, hne⟩ := Finset.one_lt_card.mp (by omega : 1 < a.primeFactors.card)
      have hpair : ({p₁, p₂} : Finset ℕ) ⊆ a.primeFactors := by
        intro x hx; simp at hx; rcases hx with rfl | rfl <;> assumption
      have hle := Finset.sum_le_sum_of_subset (f := fun p => a / p) hpair
      rw [Finset.sum_pair hne] at hle
      have hp1_le : 1 ≤ a / p₁ := Nat.div_pos (Nat.le_of_dvd (by omega) (Nat.dvd_of_mem_primeFactors hp₁))
        (Nat.prime_of_mem_primeFactors hp₁).pos
      have hp2_le : 1 ≤ a / p₂ := Nat.div_pos (Nat.le_of_dvd (by omega) (Nat.dvd_of_mem_primeFactors hp₂))
        (Nat.prime_of_mem_primeFactors hp₂).pos
      omega
    set M := (∑ p ∈ a.primeFactors, a / p) - 1
    have hM_pos : 0 < M := by omega
    have hM_dvd : a ∣ M := by
      rw [← hprod, Nat.prod_primeFactors_dvd_iff hM_pos.ne']
      intro q hq
      rw [Nat.mem_primeFactors]
      refine ⟨Nat.prime_of_mem_primeFactors hq, ?_, hM_pos.ne'⟩
      have hsplit : ∑ p ∈ a.primeFactors, a / p = a / q + ∑ p ∈ a.primeFactors.erase q, a / p :=
        (Finset.add_sum_erase _ _ hq).symm
      have haq_pos : 1 ≤ a / q := Nat.div_pos (Nat.le_of_dvd (by omega) (Nat.dvd_of_mem_primeFactors hq))
        (Nat.prime_of_mem_primeFactors hq).pos
      have hM_eq : M = (a / q - 1) + ∑ p ∈ a.primeFactors.erase q, a / p := by
        dsimp [M]; rw [hsplit]; omega
      rw [hM_eq]
      refine dvd_add (hgiuga q hq) (Finset.dvd_sum fun p hp => ?_)
      have hp_ne : p ≠ q := (Finset.mem_erase.mp hp).1
      have hp_mem : p ∈ a.primeFactors := (Finset.mem_erase.mp hp).2
      have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp_mem
      have hq_prime : q.Prime := Nat.prime_of_mem_primeFactors hq
      have hcop : Nat.Coprime p q := (Nat.coprime_primes hp_prime hq_prime).mpr hp_ne
      have hpq : p * q ∣ a := hcop.mul_dvd_of_dvd_of_dvd
        (Nat.dvd_of_mem_primeFactors hp_mem) (Nat.dvd_of_mem_primeFactors hq)
      obtain ⟨k, hk⟩ := hpq
      refine ⟨k, ?_⟩
      rw [hk, mul_assoc, Nat.mul_div_cancel_left _ hp_prime.pos]
    have ha_le_M : a ≤ M := Nat.le_of_dvd hM_pos hM_dvd
    omega
  exact ⟨ha1, hsq, hodd_all, hnorm, hsum_ge⟩

/- ### Part 2: Verified piecewise-constant logarithm, candidate sieve, Trie, and dual bound -/

private def N_CUT : ℕ := 40000
private def L_CUT : ℕ := 244
private def LAM : ℕ := 9760000 -- 40000 * 244
private def TARGET_L : ℕ := 693280 -- 16 * 43330
private def BUDGET : ℕ := 9066720 -- LAM - TARGET_L

inductive LogTree
  | leaf (c : ℕ) : LogTree
  | branch (t : ℕ) (lt ge : LogTree) : LogTree

def LogTree.eval (n : ℕ) : LogTree → ℕ
  | .leaf c => c
  | .branch t l r =>
    match Nat.ble t n with
    | false => l.eval n
    | true => r.eval n

def LogTree.valid (lo : ℕ) : LogTree → Bool
  | .leaf c => Nat.ble (Nat.pow 2 c) (Nat.pow lo 16)
  | .branch t l r =>
    match Nat.ble lo t with
    | false => false
    | true =>
      match l.valid lo with
      | false => false
      | true => r.valid t

private lemma LogTree.pow_eval_le {lo n : ℕ} {lt : LogTree} (h : lt.valid lo = true) (hlo : lo ≤ n) :
    2 ^ lt.eval n ≤ n ^ 16 := by
  induction lt generalizing lo with
  | leaf c =>
    simp only [valid, Nat.ble_eq] at h
    exact h.trans (Nat.pow_le_pow_left hlo 16)
  | branch t l r ihl ihr =>
    simp only [valid] at h
    cases hlot : Nat.ble lo t with
    | false => simp [hlot] at h
    | true =>
      simp only [hlot] at h
      cases hl : l.valid lo with
      | false => simp [hl] at h
      | true =>
        simp only [hl] at h
        simp only [eval]
        cases htn : Nat.ble t n with
        | false => exact ihl hl hlo
        | true => exact ihr h (Nat.ble_eq.mp htn)

private def chkDiv (n d : ℕ) (k : Bool) : Bool :=
  match Nat.beq (Nat.mod n d) 0 with
  | true => Nat.beq n d
  | false => k

private lemma chkDiv_eq_true_of_prime {p d : ℕ} (hp : p.Prime) (hd : 2 ≤ d) {k : Bool}
    (hk : k = true) : chkDiv p d k = true := by
  unfold chkDiv
  cases h : Nat.beq (Nat.mod p d) 0 with
  | false => exact hk
  | true =>
    have hmod : p % d = 0 := Nat.beq_eq.mp h
    have hdvd : d ∣ p := Nat.dvd_of_mod_eq_zero hmod
    have heq : p = d := ((hp.eq_one_or_self_of_dvd d hdvd).resolve_left (by omega)).symm
    exact Nat.beq_eq.mpr heq

private def isCandOdd (n : ℕ) : Bool :=
  chkDiv n 3 (chkDiv n 5 (chkDiv n 7 (chkDiv n 11 (chkDiv n 13 (chkDiv n 17 (chkDiv n 19
  (chkDiv n 23 (chkDiv n 29 (chkDiv n 31 (chkDiv n 37 (chkDiv n 41 (chkDiv n 43 (chkDiv n 47
  (chkDiv n 53 (chkDiv n 59 (chkDiv n 61 (chkDiv n 67 (chkDiv n 71 (chkDiv n 73 (chkDiv n 79
  (chkDiv n 83 (chkDiv n 89 (chkDiv n 97 (chkDiv n 101 true))))))))))))))))))))))))

private lemma isCandOdd_of_prime {p : ℕ} (hp : p.Prime) : isCandOdd p = true := by
  unfold isCandOdd
  repeat apply chkDiv_eq_true_of_prime hp (by omega)
  rfl

-- 4-ary MSB-first trie of depth d covering [0, 4^d)
inductive Trie
  | empty : Trie
  | leaf (val : ℕ) : Trie
  | node (c0 c1 c2 c3 : Trie) : Trie

def Trie.WF : ℕ → Trie → Prop
  | _, .empty => True
  | 0, .leaf _ => True
  | d + 1, .node c0 c1 c2 c3 => c0.WF d ∧ c1.WF d ∧ c2.WF d ∧ c3.WF d
  | _, _ => False

def Trie.single : ℕ → ℕ → ℕ → Trie
  | 0, _, v => .leaf v
  | d + 1, k, v =>
    let s := Nat.pow 4 d
    let q := Nat.div k s
    let r := Nat.mod k s
    let sub := Trie.single d r v
    match q with
    | 0 => .node sub .empty .empty .empty
    | 1 => .node .empty sub .empty .empty
    | 2 => .node .empty .empty sub .empty
    | _ => .node .empty .empty .empty sub

def Trie.add : Trie → Trie → Trie
  | .empty, t => t
  | t, .empty => t
  | .leaf a, .leaf b => .leaf (Nat.add a b)
  | .node a0 a1 a2 a3, .node b0 b1 b2 b3 =>
    .node (a0.add b0) (a1.add b1) (a2.add b2) (a3.add b3)
  | t, _ => t

def Trie.lookup : ℕ → ℕ → Trie → ℕ
  | _, _, .empty => 0
  | 0, _, .leaf v => v
  | d + 1, r, .node c0 c1 c2 c3 =>
    let s := Nat.pow 4 d
    let q := Nat.div r s
    let rem := Nat.mod r s
    match q with
    | 0 => c0.lookup d rem
    | 1 => c1.lookup d rem
    | 2 => c2.lookup d rem
    | _ => c3.lookup d rem
  | _, _, _ => 0

private lemma Trie.wf_single (d k v : ℕ) : (Trie.single d k v).WF d := by
  induction d generalizing k with
  | zero => trivial
  | succ d ih =>
    simp only [single]
    cases hq : Nat.div k (Nat.pow 4 d) with
    | zero => exact ⟨ih _, by simp [WF], by simp [WF], by simp [WF]⟩
    | succ q1 =>
      cases q1 with
      | zero => exact ⟨by simp [WF], ih _, by simp [WF], by simp [WF]⟩
      | succ q2 =>
        cases q2 with
        | zero => exact ⟨by simp [WF], by simp [WF], ih _, by simp [WF]⟩
        | succ _ => exact ⟨by simp [WF], by simp [WF], by simp [WF], ih _⟩

private lemma Trie.wf_add {d : ℕ} {t1 t2 : Trie} (h1 : t1.WF d) (h2 : t2.WF d) :
    (t1.add t2).WF d := by
  induction d generalizing t1 t2 with
  | zero =>
    cases t1 <;> cases t2 <;> simp_all [WF, add]
  | succ d ih =>
    cases t1 <;> cases t2 <;> simp_all [WF, add]

private lemma nat_div (a b : ℕ) : Nat.div a b = a / b := rfl
private lemma nat_mod (a b : ℕ) : Nat.mod a b = a % b := rfl
private lemma nat_pow (a b : ℕ) : Nat.pow a b = a ^ b := rfl
private lemma nat_add (a b : ℕ) : Nat.add a b = a + b := rfl
private lemma nat_sub (a b : ℕ) : Nat.sub a b = a - b := rfl
private lemma nat_mul (a b : ℕ) : Nat.mul a b = a * b := rfl

private lemma Trie.lookup_single {d k r v : ℕ} (hk : k < 4 ^ d) (hr : r < 4 ^ d) :
    (Trie.single d k v).lookup d r = if r = k then v else 0 := by
  induction d generalizing k r with
  | zero =>
    have hk0 : k = 0 := by omega
    have hr0 : r = 0 := by omega
    subst hk0; subst hr0; rfl
  | succ d ih =>
    have hs : 0 < 4 ^ d := by positivity
    have hqk : k / 4 ^ d < 4 := by
      rw [Nat.div_lt_iff_lt_mul hs]; simpa [pow_succ'] using hk
    have hqr : r / 4 ^ d < 4 := by
      rw [Nat.div_lt_iff_lt_mul hs]; simpa [pow_succ'] using hr
    have hrk_iff : r = k ↔ r / 4 ^ d = k / 4 ^ d ∧ r % 4 ^ d = k % 4 ^ d := by
      constructor
      · rintro rfl; exact ⟨rfl, rfl⟩
      · rintro ⟨hq, hrem⟩
        have h1 := Nat.div_add_mod r (4 ^ d)
        have h2 := Nat.div_add_mod k (4 ^ d)
        rw [hq, hrem] at h1
        omega
    have hrm : r % 4 ^ d < 4 ^ d := Nat.mod_lt r hs
    have hkm : k % 4 ^ d < 4 ^ d := Nat.mod_lt k hs
    simp only [single, nat_div, nat_mod, nat_pow]
    have hqk0 : 0 ≤ k / 4 ^ d := Nat.zero_le _
    have hqr0 : 0 ≤ r / 4 ^ d := Nat.zero_le _
    rcases (by omega : k / 4 ^ d = 0 ∨ k / 4 ^ d = 1 ∨ k / 4 ^ d = 2 ∨ k / 4 ^ d = 3) with
      hkv | hkv | hkv | hkv <;>
    rcases (by omega : r / 4 ^ d = 0 ∨ r / 4 ^ d = 1 ∨ r / 4 ^ d = 2 ∨ r / 4 ^ d = 3) with
      hrv | hrv | hrv | hrv <;>
    simp [hkv, hrv, lookup, nat_div, nat_mod, ih hkm hrm, hrk_iff]

private lemma Trie.lookup_add {d r : ℕ} {t1 t2 : Trie} (h1 : t1.WF d) (h2 : t2.WF d) :
    (t1.add t2).lookup d r = t1.lookup d r + t2.lookup d r := by
  induction d generalizing r t1 t2 with
  | zero =>
    cases t1 <;> cases t2 <;> simp_all [WF, add, lookup]
  | succ d ih =>
    cases t1 <;> cases t2 <;> simp_all [WF, add, lookup]
    cases Nat.div r (Nat.pow 4 d) with
    | zero => rfl
    | succ q1 =>
      cases q1 with
      | zero => rfl
      | succ q2 =>
        cases q2 with
        | zero => rfl
        | succ _ => rfl

-- Simultaneous trie walk summing step (base + r) (t.lookup d r) over r < 4^d
def sumTrieEmpty (step : ℕ → ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0, base => step base 0
  | d + 1, base =>
    match Nat.ble 20000 base with
    | true => 0
    | false =>
      let s := Nat.pow 4 d
      Nat.add (Nat.add (sumTrieEmpty step d base) (sumTrieEmpty step d (Nat.add base s)))
              (Nat.add (sumTrieEmpty step d (Nat.add base (Nat.mul 2 s)))
                       (sumTrieEmpty step d (Nat.add base (Nat.mul 3 s))))

def sumTrie (step : ℕ → ℕ → ℕ) : ℕ → ℕ → Trie → ℕ
  | 0, base, .empty => step base 0
  | 0, base, .leaf cov => step base cov
  | 0, base, _ => step base 0
  | d + 1, base, .empty => sumTrieEmpty step (d + 1) base
  | d + 1, base, .node c0 c1 c2 c3 =>
    match Nat.ble 20000 base with
    | true => 0
    | false =>
      let s := Nat.pow 4 d
      Nat.add (Nat.add (sumTrie step d base c0) (sumTrie step d (Nat.add base s) c1))
              (Nat.add (sumTrie step d (Nat.add base (Nat.mul 2 s)) c2)
                       (sumTrie step d (Nat.add base (Nat.mul 3 s)) c3))
  | d + 1, base, _ => sumTrieEmpty step (d + 1) base

private lemma sum_range_four_mul (f : ℕ → ℕ) (s : ℕ) :
    ∑ r ∈ Finset.range (4 * s), f r =
      (∑ r ∈ Finset.range s, f r + ∑ r ∈ Finset.range s, f (s + r)) +
      (∑ r ∈ Finset.range s, f (2 * s + r) + ∑ r ∈ Finset.range s, f (3 * s + r)) := by
  have h4 : 4 * s = (s + s) + (s + s) := by omega
  rw [h4, Finset.sum_range_add]
  congr 1
  · exact Finset.sum_range_add f s s
  · rw [Finset.sum_range_add]
    congr 1 <;> refine Finset.sum_congr rfl fun r _ => ?_ <;> congr 1 <;> omega

private lemma sumTrieEmpty_eq (step : ℕ → ℕ → ℕ)
    (hzero : ∀ k cov, 20000 ≤ k → step k cov = 0)
    (d base : ℕ) :
    sumTrieEmpty step d base = ∑ r ∈ Finset.range (4 ^ d), step (base + r) 0 := by
  induction d generalizing base with
  | zero => simp [sumTrieEmpty]
  | succ d ih =>
    simp only [sumTrieEmpty]
    cases hb : Nat.ble 20000 base with
    | true =>
      have hge : 20000 ≤ base := Nat.ble_eq.mp hb
      symm
      exact Finset.sum_eq_zero fun r _ => hzero _ _ (by omega)
    | false =>
      have hpow : 4 ^ (d + 1) = 4 * 4 ^ d := by rw [pow_succ']
      rw [hpow, sum_range_four_mul]
      simp only [nat_add, nat_mul, nat_pow, ih]
      congr 1 <;> congr 1 <;> refine Finset.sum_congr rfl fun r _ => ?_ <;>
        congr 1 <;> omega

private lemma sumTrie_eq (step : ℕ → ℕ → ℕ)
    (hzero : ∀ k cov, 20000 ≤ k → step k cov = 0)
    (d base : ℕ) (t : Trie) (ht : t.WF d) :
    sumTrie step d base t =
      ∑ r ∈ Finset.range (4 ^ d), step (base + r) (t.lookup d r) := by
  induction d generalizing base t with
  | zero =>
    cases t with
    | empty => simp [sumTrie, Trie.lookup]
    | leaf v => simp [sumTrie, Trie.lookup]
    | node => exact False.elim ht
  | succ d ih =>
    cases t with
    | empty =>
      simp only [sumTrie, Trie.lookup]
      exact sumTrieEmpty_eq step hzero (d + 1) base
    | leaf _ => exact False.elim ht
    | node c0 c1 c2 c3 =>
      simp only [sumTrie]
      cases hb : Nat.ble 20000 base with
      | true =>
        have hge : 20000 ≤ base := Nat.ble_eq.mp hb
        symm
        exact Finset.sum_eq_zero fun r _ => hzero _ _ (by omega)
      | false =>
        have hpow : 4 ^ (d + 1) = 4 * 4 ^ d := by rw [pow_succ']
        rw [hpow, sum_range_four_mul]
        simp only [nat_add, nat_mul, nat_pow]
        rw [ih base c0 ht.1, ih (base + 4 ^ d) c1 ht.2.1,
            ih (base + 2 * 4 ^ d) c2 ht.2.2.1, ih (base + 3 * 4 ^ d) c3 ht.2.2.2]
        have hs : 0 < 4 ^ d := by positivity
        have h0 : ∀ r ∈ Finset.range (4 ^ d),
            Trie.lookup (d + 1) r (.node c0 c1 c2 c3) = c0.lookup d r := by
          intro r hr
          rw [Finset.mem_range] at hr
          simp [Trie.lookup, nat_div, nat_mod, Nat.div_eq_of_lt hr, Nat.mod_eq_of_lt hr]
        have h1 : ∀ r ∈ Finset.range (4 ^ d),
            Trie.lookup (d + 1) (4 ^ d + r) (.node c0 c1 c2 c3) = c1.lookup d r := by
          intro r hr
          rw [Finset.mem_range] at hr
          have hd1 : (4 ^ d + r) / 4 ^ d = 1 := by
            rw [Nat.add_div_left r hs, Nat.div_eq_of_lt hr]
          have hm1 : (4 ^ d + r) % 4 ^ d = r := by
            rw [Nat.add_mod_left, Nat.mod_eq_of_lt hr]
          simp [Trie.lookup, nat_div, nat_mod, hd1, hm1]
        have h2 : ∀ r ∈ Finset.range (4 ^ d),
            Trie.lookup (d + 1) (2 * 4 ^ d + r) (.node c0 c1 c2 c3) = c2.lookup d r := by
          intro r hr
          rw [Finset.mem_range] at hr
          have hd2 : (2 * 4 ^ d + r) / 4 ^ d = 2 := by
            rw [mul_comm 2, Nat.mul_add_div hs, Nat.div_eq_of_lt hr]
          have hm2 : (2 * 4 ^ d + r) % 4 ^ d = r := by
            rw [mul_comm 2, Nat.mul_add_mod, Nat.mod_eq_of_lt hr]
          simp [Trie.lookup, nat_div, nat_mod, hd2, hm2]
        have h3 : ∀ r ∈ Finset.range (4 ^ d),
            Trie.lookup (d + 1) (3 * 4 ^ d + r) (.node c0 c1 c2 c3) = c3.lookup d r := by
          intro r hr
          rw [Finset.mem_range] at hr
          have hd3 : (3 * 4 ^ d + r) / 4 ^ d = 3 := by
            rw [mul_comm 3, Nat.mul_add_div hs, Nat.div_eq_of_lt hr]
          have hm3 : (3 * 4 ^ d + r) % 4 ^ d = r := by
            rw [mul_comm 3, Nat.mul_add_mod, Nat.mod_eq_of_lt hr]
          simp [Trie.lookup, nat_div, nat_mod, hd3, hm3]
        congr 1
        · congr 1
          · refine Finset.sum_congr rfl fun r hr => by rw [h0 r hr]
          · refine Finset.sum_congr rfl fun r hr => by rw [h1 r hr, add_assoc]
        · congr 1
          · refine Finset.sum_congr rfl fun r hr => by rw [h2 r hr, add_assoc]
          · refine Finset.sum_congr rfl fun r hr => by rw [h3 r hr, add_assoc]

-- Balanced binary tree of dual matching edges (u, v, c)
inductive ET
  | e (u v c : ℕ) : ET
  | n (l r : ET) : ET

def L : List ℕ → ET
  | u :: v :: c :: r => .n (.e u v c) (L r)
  | _ => .e 3 7 0

def ET.toTrie : ET → Trie
  | .e u v c => (Trie.single 8 (Nat.div (Nat.sub u 1) 2) c).add
                (Trie.single 8 (Nat.div (Nat.sub v 1) 2) c)
  | .n l r => l.toTrie.add r.toTrie

def ET.valid : ET → Bool
  | .e u v _ =>
    match Nat.ble 3 u with
    | false => false
    | true =>
      match Nat.ble (Nat.add u 1) v with
      | false => false
      | true =>
        match Nat.ble v 39999 with
        | false => false
        | true =>
          match Nat.beq (Nat.mod u 2) 1 with
          | false => false
          | true =>
            match Nat.beq (Nat.mod v 2) 1 with
            | false => false
            | true => Nat.beq (Nat.mod (Nat.sub v 1) u) 0
  | .n l r =>
    match l.valid with
    | false => false
    | true => r.valid

def ET.sumC : ET → ℕ
  | .e _ _ c => c
  | .n l r => Nat.add l.sumC r.sumC

private lemma ET.wf_toTrie (et : ET) : et.toTrie.WF 8 := by
  induction et with
  | e u v c => exact Trie.wf_add (Trie.wf_single _ _ _) (Trie.wf_single _ _ _)
  | n l r ihl ihr => exact Trie.wf_add ihl ihr

private lemma ET.sum_lookup_le (S : Finset ℕ)
    (hodd : ∀ p ∈ S, p % 2 = 1)
    (hnorm : ∀ p ∈ S, ∀ q ∈ S, ¬ (p ∣ q - 1))
    (hlt : ∀ p ∈ S, p < 40000)
    (et : ET) (hv : et.valid = true) :
    ∑ p ∈ S, et.toTrie.lookup 8 ((p - 1) / 2) ≤ et.sumC := by
  induction et with
  | e u v c =>
    simp only [valid] at hv
    -- Extract all 6 conditions from hv
    have hu3 : 3 ≤ u := by
      cases h : Nat.ble 3 u <;> simp [h] at hv; exact Nat.ble_eq.mp h
    have huv : u + 1 ≤ v := by
      have h1 : Nat.ble 3 u = true := Nat.ble_eq.mpr hu3
      simp only [h1] at hv
      cases h : Nat.ble (Nat.add u 1) v <;> simp [h] at hv; exact Nat.ble_eq.mp h
    have hvN : v ≤ 39999 := by
      have h1 : Nat.ble 3 u = true := Nat.ble_eq.mpr hu3
      have h2 : Nat.ble (Nat.add u 1) v = true := Nat.ble_eq.mpr huv
      simp only [h1, h2] at hv
      cases h : Nat.ble v 39999 <;> simp [h] at hv; exact Nat.ble_eq.mp h
    have huodd : u % 2 = 1 := by
      have h1 : Nat.ble 3 u = true := Nat.ble_eq.mpr hu3
      have h2 : Nat.ble (Nat.add u 1) v = true := Nat.ble_eq.mpr huv
      have h3 : Nat.ble v 39999 = true := Nat.ble_eq.mpr hvN
      simp only [h1, h2, h3] at hv
      cases h : Nat.beq (Nat.mod u 2) 1 <;> simp [h] at hv; exact Nat.beq_eq.mp h
    have hvodd : v % 2 = 1 := by
      have h1 : Nat.ble 3 u = true := Nat.ble_eq.mpr hu3
      have h2 : Nat.ble (Nat.add u 1) v = true := Nat.ble_eq.mpr huv
      have h3 : Nat.ble v 39999 = true := Nat.ble_eq.mpr hvN
      have h4 : Nat.beq (Nat.mod u 2) 1 = true := Nat.beq_eq.mpr huodd
      simp only [h1, h2, h3, h4] at hv
      cases h : Nat.beq (Nat.mod v 2) 1 <;> simp [h] at hv; exact Nat.beq_eq.mp h
    have hdvd : u ∣ v - 1 := by
      have h1 : Nat.ble 3 u = true := Nat.ble_eq.mpr hu3
      have h2 : Nat.ble (Nat.add u 1) v = true := Nat.ble_eq.mpr huv
      have h3 : Nat.ble v 39999 = true := Nat.ble_eq.mpr hvN
      have h4 : Nat.beq (Nat.mod u 2) 1 = true := Nat.beq_eq.mpr huodd
      have h5 : Nat.beq (Nat.mod v 2) 1 = true := Nat.beq_eq.mpr hvodd
      simp only [h1, h2, h3, h4, h5] at hv
      exact Nat.dvd_of_mod_eq_zero (Nat.beq_eq.mp hv)
    have hterm : ∀ p ∈ S,
        (ET.e u v c).toTrie.lookup 8 ((p - 1) / 2) =
          (if p = u then c else 0) + (if p = v then c else 0) := by
      intro p hp
      have hpodd := hodd p hp
      have hplt := hlt p hp
      simp only [toTrie, nat_sub, nat_div]
      rw [Trie.lookup_add (Trie.wf_single _ _ _) (Trie.wf_single _ _ _),
          Trie.lookup_single (by omega) (by omega),
          Trie.lookup_single (by omega) (by omega)]
      have hequ : (p - 1) / 2 = (u - 1) / 2 ↔ p = u := by omega
      have heqv : (p - 1) / 2 = (v - 1) / 2 ↔ p = v := by omega
      simp [hequ, heqv]
    rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
    simp only [sumC]
    by_cases huS : u ∈ S <;> by_cases hvS : v ∈ S
    · exact absurd hdvd (hnorm u huS v hvS)
    · simp [huS, hvS]
    · simp [huS, hvS]
    · simp [huS, hvS]
  | n l r ihl ihr =>
    simp only [valid] at hv
    cases hl : l.valid with
    | false => simp [hl] at hv
    | true =>
      simp only [hl] at hv
      have hterm : ∀ p ∈ S,
          (ET.n l r).toTrie.lookup 8 ((p - 1) / 2) =
            l.toTrie.lookup 8 ((p - 1) / 2) + r.toTrie.lookup 8 ((p - 1) / 2) := by
        intro p _
        exact Trie.lookup_add l.wf_toTrie r.wf_toTrie
      rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib]
      simp only [sumC, nat_add]
      exact Nat.add_le_add (ihl hl) (ihr hv)


/- ### Part 3: Concrete LogTree, weight reduction, and 3-case certificates -/

private def myLogTree : LogTree :=
  LogTree.branch 40000 (LogTree.branch 8934 (LogTree.branch 2897 (LogTree.branch 470 (LogTree.branch 40 (LogTree.branch 8 (LogTree.branch 3 (LogTree.leaf 0) (LogTree.leaf 25)) (LogTree.branch 17 (LogTree.leaf 45) (LogTree.leaf 65))) (LogTree.branch 182 (LogTree.branch 95 (LogTree.leaf 85) (LogTree.leaf 105)) (LogTree.branch 305 (LogTree.leaf 120) (LogTree.leaf 132)))) (LogTree.branch 1387 (LogTree.branch 862 (LogTree.branch 664 (LogTree.leaf 142) (LogTree.leaf 150)) (LogTree.branch 1117 (LogTree.leaf 156) (LogTree.leaf 162))) (LogTree.branch 2048 (LogTree.branch 1723 (LogTree.leaf 167) (LogTree.leaf 172)) (LogTree.branch 2436 (LogTree.leaf 176) (LogTree.leaf 180))))) (LogTree.branch 6317 (LogTree.branch 4871 (LogTree.branch 3757 (LogTree.branch 3299 (LogTree.leaf 184) (LogTree.leaf 187)) (LogTree.branch 4278 (LogTree.leaf 190) (LogTree.leaf 193))) (LogTree.branch 5793 (LogTree.branch 5548 (LogTree.leaf 196) (LogTree.leaf 199)) (LogTree.branch 6050 (LogTree.leaf 200) (LogTree.leaf 201)))) (LogTree.branch 7513 (LogTree.branch 6889 (LogTree.branch 6597 (LogTree.leaf 202) (LogTree.leaf 203)) (LogTree.branch 7194 (LogTree.leaf 204) (LogTree.leaf 205))) (LogTree.branch 8192 (LogTree.branch 7845 (LogTree.leaf 206) (LogTree.leaf 207)) (LogTree.branch 8555 (LogTree.leaf 208) (LogTree.leaf 209)))))) (LogTree.branch 17867 (LogTree.branch 12634 (LogTree.branch 10624 (LogTree.branch 9742 (LogTree.branch 9329 (LogTree.leaf 210) (LogTree.leaf 211)) (LogTree.branch 10174 (LogTree.leaf 212) (LogTree.leaf 213))) (LogTree.branch 11586 (LogTree.branch 11095 (LogTree.leaf 214) (LogTree.leaf 215)) (LogTree.branch 12099 (LogTree.leaf 216) (LogTree.leaf 217)))) (LogTree.branch 15025 (LogTree.branch 13778 (LogTree.branch 13194 (LogTree.leaf 218) (LogTree.leaf 219)) (LogTree.branch 14388 (LogTree.leaf 220) (LogTree.leaf 221))) (LogTree.branch 16384 (LogTree.branch 15690 (LogTree.leaf 222) (LogTree.leaf 223)) (LogTree.branch 17110 (LogTree.leaf 224) (LogTree.leaf 225))))) (LogTree.branch 25268 (LogTree.branch 21248 (LogTree.branch 19484 (LogTree.branch 18658 (LogTree.leaf 226) (LogTree.leaf 227)) (LogTree.branch 20347 (LogTree.leaf 228) (LogTree.leaf 229))) (LogTree.branch 23171 (LogTree.branch 22189 (LogTree.leaf 230) (LogTree.leaf 231)) (LogTree.branch 24197 (LogTree.leaf 232) (LogTree.leaf 233)))) (LogTree.branch 30049 (LogTree.branch 27555 (LogTree.branch 26387 (LogTree.leaf 234) (LogTree.leaf 235)) (LogTree.branch 28775 (LogTree.leaf 236) (LogTree.leaf 237))) (LogTree.branch 32768 (LogTree.branch 31379 (LogTree.leaf 238) (LogTree.leaf 239)) (LogTree.branch 34219 (LogTree.leaf 240) (LogTree.branch 35734 (LogTree.leaf 241) (LogTree.leaf 242)))))))) (LogTree.leaf 244)

private lemma myLogTree_valid : myLogTree.valid 1 = true := by rfl

private lemma two_pow_eval_le (p : ℕ) (hp : 1 ≤ p) : 2 ^ myLogTree.eval p ≤ p ^ 16 :=
  LogTree.pow_eval_le myLogTree_valid hp

private def weightOf (n : ℕ) : ℕ :=
  Nat.sub (Nat.div (Nat.add LAM (Nat.sub n 1)) n) (myLogTree.eval n)

private lemma weightOf_eq_zero_of_ge {p : ℕ} (hp : 40000 ≤ p) : weightOf p = 0 := by
  have hev : myLogTree.eval p = 244 := by
    simp only [myLogTree, LogTree.eval, Nat.ble_eq.mpr hp]
  unfold weightOf
  rw [hev, nat_sub, nat_div, nat_add, nat_sub]
  have hdiv : (LAM + (p - 1)) / p ≤ 244 := by
    have hlt : LAM + (p - 1) < p * 245 := by
      dsimp [LAM]
      omega
    have h1 : (LAM + (p - 1)) / p < 245 := (Nat.div_lt_iff_lt_mul (by omega)).mpr (by linarith)
    omega
  omega

private lemma lam_le_mul_eval_add_weight {p : ℕ} (hp : 1 ≤ p) :
    LAM ≤ p * (myLogTree.eval p + weightOf p) := by
  have hceil : LAM ≤ p * ((LAM + (p - 1)) / p) := by
    have hmod := Nat.div_add_mod (LAM + (p - 1)) p
    have hlt := Nat.mod_lt (LAM + (p - 1)) (by omega : 0 < p)
    omega
  have hw : (LAM + (p - 1)) / p ≤ myLogTree.eval p + weightOf p := by
    unfold weightOf
    rw [nat_sub, nat_div, nat_add, nat_sub]
    omega
  exact hceil.trans (Nat.mul_le_mul_left p hw)

private lemma digits_ge_13000_of_weight_bound {a : ℕ}
    (ha : AgohGiuga.IsStrongGiuga a)
    (hw : ∑ p ∈ a.primeFactors.filter (· < 40000), weightOf p ≤ BUDGET) :
    13000 ≤ (Nat.digits 10 a).length := by
  obtain ⟨ha1, hsq, hodd, _, hsum_ge⟩ := strongGiuga_props ha
  set S := a.primeFactors
  have hprod : ∏ p ∈ S, p = a := Nat.prod_primeFactors_of_squarefree hsq
  have hw_all : ∑ p ∈ S, weightOf p ≤ BUDGET := by
    have hsplit := (Finset.sum_filter_add_sum_filter_not S (· < 40000) weightOf).symm
    have hzero : ∑ p ∈ S.filter (fun x => ¬ x < 40000), weightOf p = 0 :=
      Finset.sum_eq_zero fun p hp => weightOf_eq_zero_of_ge (by
        have := (Finset.mem_filter.mp hp).2; omega)
    rw [hsplit, hzero, add_zero]
    exact hw
  have hterm : ∀ p ∈ S, LAM * (a / p) ≤ a * (myLogTree.eval p + weightOf p) := by
    intro p hp
    have hp3 : 3 ≤ p := (hodd p hp).2
    have hpa : p ∣ a := Nat.dvd_of_mem_primeFactors hp
    have hmul : p * (a / p) = a := Nat.mul_div_cancel' hpa
    calc
      LAM * (a / p) ≤ (p * (myLogTree.eval p + weightOf p)) * (a / p) :=
        Nat.mul_le_mul_right _ (lam_le_mul_eval_add_weight (by omega))
      _ = (p * (a / p)) * (myLogTree.eval p + weightOf p) := by ring
      _ = a * (myLogTree.eval p + weightOf p) := by rw [hmul]
  have hsum_ineq : LAM * (a + 1) ≤ a * (∑ p ∈ S, myLogTree.eval p + ∑ p ∈ S, weightOf p) := by
    calc
      LAM * (a + 1) ≤ LAM * ∑ p ∈ S, a / p := Nat.mul_le_mul_left _ hsum_ge
      _ = ∑ p ∈ S, LAM * (a / p) := Finset.mul_sum _ _ _
      _ ≤ ∑ p ∈ S, a * (myLogTree.eval p + weightOf p) := Finset.sum_le_sum hterm
      _ = a * ∑ p ∈ S, (myLogTree.eval p + weightOf p) := (Finset.mul_sum _ _ _).symm
      _ = a * (∑ p ∈ S, myLogTree.eval p + ∑ p ∈ S, weightOf p) := by rw [Finset.sum_add_distrib]
  have hlam_lt : LAM < ∑ p ∈ S, myLogTree.eval p + ∑ p ∈ S, weightOf p := by
    have h1 : a * LAM < a * (∑ p ∈ S, myLogTree.eval p + ∑ p ∈ S, weightOf p) := by
      have : LAM * (a + 1) = a * LAM + LAM := by ring
      have : 0 < LAM := by decide
      omega
    exact Nat.lt_of_mul_lt_mul_left h1
  have hL_ge : TARGET_L ≤ ∑ p ∈ S, myLogTree.eval p := by
    have : LAM - BUDGET = TARGET_L := by decide
    omega
  have hpow2 : 2 ^ TARGET_L ≤ a ^ 16 := by
    calc
      2 ^ TARGET_L ≤ 2 ^ (∑ p ∈ S, myLogTree.eval p) := Nat.pow_le_pow_right (by norm_num) hL_ge
      _ = ∏ p ∈ S, 2 ^ myLogTree.eval p := (Finset.prod_pow_eq_pow_sum _ _ _).symm
      _ ≤ ∏ p ∈ S, p ^ 16 := Finset.prod_le_prod' fun p hp =>
        two_pow_eval_le p (by have := (hodd p hp).2; omega)
      _ = (∏ p ∈ S, p) ^ 16 := Finset.prod_pow S 16 (fun p => p)
      _ = a ^ 16 := by rw [hprod]
  have h10 : (10 ^ 12999) ^ 16 ≤ 2 ^ TARGET_L := by
    have hstep : 10 ^ 12999 ≤ 2 ^ 43330 := by
      have h1 : 10 ^ 12999 = (10 ^ 3) ^ 4333 := by
        have : 12999 = 3 * 4333 := by norm_num
        rw [this, pow_mul]
      have h2 : (2 ^ 10) ^ 4333 = 2 ^ 43330 := by
        have : 43330 = 10 * 4333 := by norm_num
        rw [this, pow_mul]
      rw [h1, ← h2]
      exact Nat.pow_le_pow_left (by norm_num) 4333
    have h3 : (2 ^ 43330) ^ 16 = 2 ^ TARGET_L := by
      have : TARGET_L = 43330 * 16 := by decide
      rw [this, pow_mul]
    rw [← h3]
    exact Nat.pow_le_pow_left hstep 16
  have ha_ge : 10 ^ 12999 ≤ a :=
    (Nat.pow_le_pow_iff_left (by norm_num : 16 ≠ 0)).mp (h10.trans hpow2)
  have hlt_dig : 12999 < (Nat.digits 10 a).length :=
    (Nat.lt_digits_length_iff (by norm_num : 1 < 10) a).mpr ha_ge
  omega

private def stepCase (filt : ℕ → Bool) (k cov : ℕ) : ℕ :=
  match Nat.ble 20000 k with
  | true => 0
  | false =>
    match Nat.beq k 0 with
    | true => 0
    | false =>
      let n := Nat.add (Nat.mul 2 k) 1
      match filt n with
      | false => 0
      | true =>
        match isCandOdd n with
        | false => 0
        | true => Nat.sub (weightOf n) cov

private lemma stepCase_zero_ge (filt : ℕ → Bool) (k cov : ℕ) (hk : 20000 ≤ k) :
    stepCase filt k cov = 0 := by
  simp only [stepCase, Nat.ble_eq.mpr hk]

private lemma sum_weight_filter_le (S : Finset ℕ) (filt : ℕ → Bool) (et : ET)
    (hprime : ∀ p ∈ S, p.Prime)
    (hodd : ∀ p ∈ S, p % 2 = 1 ∧ 3 ≤ p)
    (hnorm : ∀ p ∈ S, ∀ q ∈ S, ¬ (p ∣ q - 1))
    (hlt : ∀ p ∈ S, p < 40000)
    (hfilt : ∀ p ∈ S, filt p = true)
    (hv : et.valid = true) :
    ∑ p ∈ S, weightOf p ≤ et.sumC + sumTrie (stepCase filt) 8 0 et.toTrie := by
  have hpoint : ∀ p ∈ S,
      weightOf p ≤ et.toTrie.lookup 8 ((p - 1) / 2) +
        stepCase filt ((p - 1) / 2) (et.toTrie.lookup 8 ((p - 1) / 2)) := by
    intro p hp
    have hpo := hodd p hp
    have hplt := hlt p hp
    have hk_lt : (p - 1) / 2 < 20000 := by omega
    have hk_ne0 : (p - 1) / 2 ≠ 0 := by omega
    have hble : Nat.ble 20000 ((p - 1) / 2) = false := by
      cases h : Nat.ble 20000 ((p - 1) / 2) with
      | false => rfl
      | true => have := Nat.ble_eq.mp h; omega
    have hbeq : Nat.beq ((p - 1) / 2) 0 = false := by
      cases h : Nat.beq ((p - 1) / 2) 0 with
      | false => rfl
      | true => exact absurd (Nat.beq_eq.mp h) hk_ne0
    have hn_eq : Nat.add (Nat.mul 2 ((p - 1) / 2)) 1 = p := by
      rw [nat_add, nat_mul]; omega
    have hstep : stepCase filt ((p - 1) / 2) (et.toTrie.lookup 8 ((p - 1) / 2)) =
        weightOf p - et.toTrie.lookup 8 ((p - 1) / 2) := by
      unfold stepCase
      rw [hble, hbeq]
      dsimp only
      rw [hn_eq, hfilt p hp, isCandOdd_of_prime (hprime p hp), nat_sub]
    rw [hstep]
    omega
  have h1 : ∑ p ∈ S, weightOf p ≤
      ∑ p ∈ S, et.toTrie.lookup 8 ((p - 1) / 2) +
      ∑ p ∈ S, stepCase filt ((p - 1) / 2) (et.toTrie.lookup 8 ((p - 1) / 2)) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum hpoint
  have h2 : ∑ p ∈ S, et.toTrie.lookup 8 ((p - 1) / 2) ≤ et.sumC :=
    et.sum_lookup_le S (fun p hp => (hodd p hp).1) hnorm hlt hv
  have h3 : ∑ p ∈ S, stepCase filt ((p - 1) / 2) (et.toTrie.lookup 8 ((p - 1) / 2)) ≤
      sumTrie (stepCase filt) 8 0 et.toTrie := by
    rw [sumTrie_eq (stepCase filt) (stepCase_zero_ge filt) 8 0 et.toTrie et.wf_toTrie]
    have hinj : Set.InjOn (fun p => (p - 1) / 2) (S : Set ℕ) := by
      intro p₁ hp₁ p₂ hp₂ heq
      dsimp only at heq
      have h1 := (hodd p₁ hp₁).1
      have h2 := (hodd p₂ hp₂).1
      omega
    have himg : S.image (fun p => (p - 1) / 2) ⊆ Finset.range (4 ^ 8) := by
      intro k hk
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hk
      have := hlt p hp
      rw [Finset.mem_range]
      omega
    calc
      ∑ p ∈ S, stepCase filt ((p - 1) / 2) (et.toTrie.lookup 8 ((p - 1) / 2))
          = ∑ r ∈ S.image (fun p => (p - 1) / 2), stepCase filt r (et.toTrie.lookup 8 r) :=
        (Finset.sum_image (f := fun r => stepCase filt r (et.toTrie.lookup 8 r))
          (fun p₁ hp₁ p₂ hp₂ h => hinj hp₁ hp₂ h)).symm
      _ ≤ ∑ r ∈ Finset.range (4 ^ 8), stepCase filt r (et.toTrie.lookup 8 r) :=
        Finset.sum_le_sum_of_subset himg
      _ = ∑ r ∈ Finset.range (4 ^ 8), stepCase filt (0 + r) (et.toTrie.lookup 8 r) := by
        simp_rw [zero_add]
  exact h1.trans (Nat.add_le_add h2 h3)

private def filt1 (n : ℕ) : Bool :=
  Nat.beq (Nat.mod n 3) 2

private def filt2 (n : ℕ) : Bool :=
  match Nat.beq n 3 with
  | true => false
  | false =>
    match Nat.beq n 5 with
    | true => false
    | false =>
      match Nat.beq (Nat.mod n 5) 1 with
      | true => false
      | false => true

private def filt3 (n : ℕ) : Bool :=
  match Nat.beq n 3 with
  | true => false
  | false =>
    match Nat.beq n 5 with
    | true => false
    | false => true

private def etCase1_0 : ET := L [5,11,887228,17,137,71136,5,281,34614,5,521,18592,5,761,12676,5,971,9896,83,1163,8231,653,1307,7306,5,1571,6046,5,1871,5045,5,2111,4448,173,2423,3853,17,2687,3453,113,2939,3137,23,3359,2719,479,3833,2357,2039,4079,2203,89,4451,2000,2399,4799,1841,83,5147,1701,2699,5399,1612,23,5843,1471,83,6143,1388,3329,6659,1263,3491,6983,1194,149,7451,1105,3803,7607,1078,29,8237,977,197,8669,917,4481,8963,879,467,9341,834,17,9623,804,1229,9833,781,17,10133,752,5231,10463,720,5501,11003,674,29,11369,644,17,11663,621,17,12071,593,6173,12347,574,293,12893,539,947,13259,518,977,13679,495,29,14153,470,17,14621,447,23,14951,432,479,15329,415,7823,15647,402,29,16067,385,17,16253,378,197,16943,353,1223,17123,345,2207,17657,328,29,17981,317,53,18233,310,83,18593,299,9473,18947,289,263,19463,275,1433,20063,259,10271,20543,247,2609,20873,239,173,21107,234,10733,21467,225,10883,21767,219,29,22157,211,2801,22409,205,2837,22697,200,17,23087,192,17,23393,186,11813,23627,182,29,24071,174,23,24473,166,23,24749,162,23,25163,155,23,25439,150]
private def etCase1_1 : ET := L [5,41,237964,83,167,58339,5,311,31251,293,587,16485,5,821,11738,23,1013,9479,5,1181,8103,659,1319,7238,113,1583,5999,5,1901,4963,5,2141,4383,5,2441,3819,5,2711,3421,53,2969,3104,173,3461,2633,17,3911,2306,2063,4127,2175,557,4457,1997,23,4877,1806,23,5153,1699,677,5417,1606,17,5849,1469,17,6257,1359,3389,6779,1237,29,7019,1187,17,7481,1100,3821,7643,1071,317,8243,977,53,8693,914,17,9011,874,293,9377,830,29,9629,803,4919,9839,780,29,10151,750,29,10499,717,29,11021,672,89,11393,642,29,11717,617,83,12119,589,17,12377,572,6449,12899,539,17,13397,510,23,13709,493,7079,14159,470,563,14639,446,1877,15017,429,7673,15347,414,7841,15683,401,503,16097,384,8273,16547,366,653,16979,351,23,17159,344,17,17681,328,17,17987,317,29,18329,307,17,18701,295,173,19031,286,977,19541,272,17,20129,257,467,20549,246,653,20897,239,17,21149,233,827,21503,224,29,21809,218,359,22259,208,11243,22487,204,23,22817,197,11549,23099,192,11699,23399,186,11831,23663,181,12041,24083,174,12251,24503,166,29,24767,162,293,25199,155,29,25463,150]
private def etCase1_2 : ET := L [23,47,207575,89,179,54421,173,347,27995,23,599,16152,419,839,11483,509,1019,9423,593,1187,8061,5,1361,7010,5,1601,5930,5,1931,4883,269,2153,4358,1223,2447,3809,5,2741,3381,1499,2999,3071,1733,3467,2629,89,3917,2302,2069,4139,2169,23,4463,1994,17,4931,1784,17,5237,1668,17,5441,1598,293,5861,1466,449,6287,1352,3413,6827,1227,503,7043,1182,197,7487,1099,3851,7703,1062,17,8297,969,4349,8699,913,113,9041,870,17,9419,826,173,9689,797,197,9851,779,5081,10163,749,53,10601,708,149,11027,672,5711,11423,640,23,11777,613,467,12143,587,29,12413,570,6491,12983,534,269,13451,507,983,13763,491,7151,14303,463,7349,14699,443,53,15053,427,1097,15359,414,7853,15707,399,83,16103,384,2069,16553,366,23,17021,350,1229,17207,343,887,17741,326,9029,18059,315,23,18401,305,2339,18713,295,149,19073,285,983,19661,269,1439,20147,257,113,20567,246,1493,20903,238,10589,21179,232,269,21521,224,23,21851,217,17,22271,208,1607,22499,203,29,22853,197,17,23189,189,2927,23417,185,383,23747,179,17,24107,173,557,24509,166,17,24821,161,197,25217,155]
private def etCase1_3 : ET := L [29,59,165339,5,191,50980,5,401,24208,5,641,15085,5,881,10923,5,1031,9311,149,1193,8020,683,1367,6978,809,1619,5862,17,1973,4775,53,2333,4008,1229,2459,3790,17,2789,3320,23,3083,2982,29,3539,2571,53,3923,2298,17,4217,2125,17,4523,1965,617,4937,1781,263,5261,1660,2753,5507,1577,419,5867,1464,29,6323,1342,857,6857,1221,53,7103,1171,23,7499,1097,3863,7727,1058,113,8363,960,23,8741,908,659,9227,848,23,9431,824,113,9719,794,17,9929,771,509,10181,746,5303,10607,708,23,11087,667,5741,11483,635,5903,11807,611,6101,12203,583,1559,12473,566,6521,13043,531,29,13457,507,53,13781,489,29,14327,462,17,14723,442,83,15107,425,7691,15383,413,197,15761,397,8069,16139,382,23,16607,364,8513,17027,350,8663,17327,339,467,17747,325,17,18089,314,9209,18419,304,9371,18743,294,9539,19079,285,1409,19727,267,10091,20183,256,10313,20627,245,29,20939,238,10613,21227,231,17,21557,223,17,21863,217,857,22283,208,23,22541,202,11471,22943,195,29,23201,189,617,23447,185,17,23801,179,23,24197,171,29,24593,164,17,24923,159,17,25229,154]
private def etCase1_4 : ET := L [5,71,137380,113,227,42876,5,431,22514,17,647,14944,5,911,10558,5,1061,9043,17,1259,7591,23,1427,6673,17,1667,5688,23,1979,4760,5,2351,3976,5,2531,3677,5,2801,580,1559,3119,2946,449,3593,2530,2003,4007,2246,53,4241,2112,2273,4547,1954,353,4943,1779,659,5273,1655,89,5519,1573,2963,5927,1447,113,6329,1341,17,6869,1218,89,7121,1167,3761,7523,1092,977,7817,1043,4211,8423,951,4373,8747,907,149,9239,847,4733,9467,820,4871,9743,790,5003,10007,764,269,10223,742,5333,10667,701,797,11159,660,359,11489,635,17,11867,607,6113,12227,582,17,12479,566,6551,13103,527,53,13463,506,173,13841,486,449,14369,460,389,14783,440,17,15131,424,773,15461,410,359,15797,395,23,16193,380,17,16661,362,2129,17033,350,17,17477,334,17,17783,324,9059,18119,313,419,18437,304,17,18803,293,17,19211,282,23,19781,266,17,20231,255,17,20639,244,1049,20981,237,1523,21323,228,10781,21563,223,17,22067,213,29,22331,207,17,22577,202,53,23003,194,113,23279,188,317,23459,185,11909,23819,178,12101,24203,171,23,24611,164,1787,25019,158,12641,25283,153]
private def etCase1_5 : ET := L [5,101,96529,29,233,41769,17,443,21900,5,701,13773,29,929,10350,5,1091,8790,29,1277,7481,5,1451,6560,53,1697,5585,5,2081,4515,5,2381,3924,5,2591,3587,1409,2819,3283,29,3191,2875,113,3617,2512,17,4013,2243,2129,4259,2102,29,4583,1937,113,4973,1767,29,5279,1653,113,5651,1529,23,5981,1432,17,6359,1333,3449,6899,1211,509,7127,1166,29,7541,1089,563,7883,1032,17,8501,941,4391,8783,903,89,9257,845,677,9479,819,257,9767,788,503,10061,759,23,10259,739,17,10847,686,563,11261,652,827,11579,628,1487,11897,605,29,12239,581,6263,12527,563,29,13109,527,17,13499,505,17,13907,482,7211,14423,456,23,14813,438,23,15227,419,149,15497,408,7901,15803,395,2027,16217,379,17,16763,359,449,17063,348,23,17573,331,29,17807,324,17,18191,311,9221,18443,304,2357,18857,291,23,19367,277,113,19889,263,17,20333,253,10331,20663,244,23,21023,236,17,21353,228,10799,21599,222,89,22073,213,11171,22343,206,263,22619,201,29,23027,193,17,23291,188,29,23549,183,11939,23879,177,3041,24329,169,17,24617,164,569,25037,157,23,25301,152]
private def etCase1_6 : ET := L [53,107,91110,17,239,40717,5,461,21040,359,719,13425,5,941,10216,29,1103,8693,23,1289,7410,5,1481,6424,5,1721,5505,149,2087,4501,23,2393,3903,5,2621,3544,29,2843,3253,23,3221,2847,269,3767,2401,23,4049,2221,29,4409,2021,83,4649,1907,2543,5087,1723,269,5381,1618,29,5801,1483,3023,6047,1415,809,6473,1306,23,6947,1201,29,7193,1153,947,7577,1083,4019,8039,1008,4271,8543,935,17,8807,900,29,9281,842,17,9521,815,89,9791,785,5039,10079,757,17,10337,732,89,10859,685,1409,11273,651,83,11621,624,89,11927,603,6131,12263,579,6269,12539,562,263,13151,525,6761,13523,503,17,14009,477,17,14519,452,7433,14867,436,17,15233,419,1109,15527,407,419,15923,390,8111,16223,379,23,16883,355,83,17099,347,17,17579,331,8951,17903,320,479,18203,311,29,18503,302,53,18869,291,29,19373,277,23,19919,262,2549,20393,250,23,20747,242,10529,21059,235,10691,21383,227,293,21683,221,83,22079,213,53,22367,206,11321,22643,201,11519,23039,193,53,23321,187,11783,23567,183,53,23957,176,17,24413,167,947,24623,164,3137,25097,156,12653,25307,152]
private def etCase1_7 : ET := L [5,131,74399,5,251,38765,5,491,19736,53,743,12986,17,953,10086,5,1151,8318,5,1301,7340,5,1511,6293,5,1811,5218,1049,2099,4474,5,2411,3873,83,2657,3494,1439,2879,3211,17,3299,2772,1889,3779,2393,509,4073,2207,17,4421,2015,2339,4679,1893,2549,5099,1719,2693,5387,1616,2903,5807,1481,17,6053,1412,17,6563,1286,17,6971,1197,3623,7247,1142,17,7583,1082,17,8093,999,269,8609,925,29,8933,884,23,9293,841,4793,9587,808,29,9803,784,5051,10103,755,5171,10343,731,17,10949,678,5639,11279,651,23,11639,623,17,11969,600,23,12329,575,23,12743,548,6581,13163,524,83,13613,498,17,14111,472,23,14537,451,173,14879,435,7649,15299,416,17,15641,403,53,16007,387,29,16241,378,29,16937,353,389,17117,346,53,17597,330,8969,17939,319,569,18209,310,23,18539,301,9461,18923,289,89,19403,277,89,19937,262,10253,20507,247,1487,20819,240,659,21089,234,10709,21419,226,23,21713,220,503,22133,211,509,22397,205,17,22679,200,887,23063,193,23,23369,186,11801,23603,182,12011,24023,175,29,24419,167,89,24743,162,17,25127,156,12671,25343,152]
private def etCase1 : ET :=
  ET.n (ET.n (ET.n etCase1_0 etCase1_1) (ET.n etCase1_2 etCase1_3)) (ET.n (ET.n etCase1_4 etCase1_5) (ET.n etCase1_6 etCase1_7))

private def etCase2_0 : ET := L [7,29,336487,17,137,71136,19,229,42501,173,347,27995,19,457,21225,7,617,15677,359,719,13425,13,859,11213,7,1009,9517,17,1123,8530,13,1327,7193,7,1499,6345,67,1609,5899,433,1733,5460,59,1889,4995,7,2017,4667,367,2203,4255,7,2339,3997,7,2437,3825,83,2657,3494,7,2843,3253,7,2969,3104,7,3137,2928,7,3319,2754,13,3433,2656,59,3659,2481,7,3823,2363,23,4003,2249,2063,4127,2175,7,4243,2111,67,4423,2014,383,4597,1931,7,4733,1870,7,4957,1773,83,5147,1701,109,5233,1670,227,5449,1596,23,5659,1526,1453,5813,1479,7,5923,1448,23,6073,1407,173,6229,1366,7,6343,1337,809,6473,1306,19,6689,1257,7,6833,1226,7,6959,1199,7,7127,1166,7,7253,1141,7,7477,1101,947,7577,1083,1283,7699,1062,19,7829,1041,37,7993,1015,13,8243,977,7,8387,956,97,8537,936,4373,8747,907,1487,8923,885,23,9109,862,7,9283,842,7,9437,824,4793,9587,808,19,9767,788,13,9907,774,17,10099,755,233,10253,739,13,10427,724,7,10529,714,13,10687,700,2713,10853,686,7,11047,670,7,11159,660,7,11299,649,7,11467,637,727,11633,623,13,11779,613,13,11909,604,17,12037,595,23,12329,575,17,12479,566,13,12637,555,7,12853,542,3259,13037,531,59,13217,520,17,13397,510,83,13613,498,2287,13723,493,769,13843,486,3499,13997,478,1193,14317,462,17,14519,452,59,14633,446,17,14723,442,13,14873,436,3793,15173,422,7643,15287,417,19,15467,410,373,15667,401,83,15937,390,577,16157,382,13,16433,370,19,16607,364,109,16787,358,257,16963,352,23,17113,346,619,17333,339,17,17443,335,83,17597,330,17,17783,324,73,17959,318,19,18127,313,4567,18269,309,13,18539,301,13,18773,293,19,19153,283,13,19319,279,17,19483,274,13,19709,268,23,19919,262,1433,20063,259,563,20269,254,19,20369,251,13,20593,245,13,20749,242,109,20929,238,17,21149,233,17,21319,228,13,21503,224,257,21589,223,10883,21767,219,13,21997,214,5527,22109,212,5569,22277,208,1879,22549,202,13,22699,199,5743,22973,194,11549,23099,192,17,23393,186,17,23563,183,1319,23743,180,13,23869,177,13,24077,174,13,24337,169,227,24517,166,23,24749,162,23,24979,158,23,25163,155,6337,25349,152,6367,25469,150]
private def etCase2_1 : ET := L [7,43,226892,23,139,70111,7,239,40717,7,379,25620,7,463,20948,107,643,15037,7,743,12986,73,877,10973,23,1013,9479,7,1163,8231,683,1367,6978,257,1543,6159,13,1613,5884,97,1747,5415,7,1933,4878,13,2029,4639,7,2213,4235,17,2347,3983,1229,2459,3790,17,2687,3453,7,2857,3237,503,3019,3049,17,3163,2902,13,3329,2745,577,3463,2632,17,3673,2471,479,3833,2357,17,4013,2243,1033,4133,2172,89,4273,2095,13,4447,2002,13,4603,1928,13,4759,1858,13,4967,1769,7,5153,1699,7,5237,1668,37,5477,1586,13,5669,1523,7,5839,1472,2963,5927,1447,7,6133,1391,17,6257,1359,397,6353,1335,17,6529,1293,1117,6703,1254,73,6863,1220,109,6977,1195,1193,7159,1160,19,7297,1133,19,7487,1099,17,7583,1082,13,7723,1058,13,7853,1036,7,8009,1012,17,8263,974,233,8389,956,1423,8539,935,7,8779,903,7,8933,884,13,9127,860,23,9293,841,13,9439,824,89,9613,805,37,9769,788,17,9929,771,17,10133,752,23,10259,739,163,10433,723,587,10567,711,2677,10709,698,89,10859,685,19,11059,669,7,11173,659,23,11317,648,359,11489,635,23,11639,623,7,11789,612,1987,11923,603,503,12073,593,17,12343,574,7,12503,564,13,12689,552,3229,12917,538,7,13049,530,23,13249,518,13,13417,509,619,13619,498,13,13729,492,13,13859,485,2333,13999,478,13,14327,462,173,14533,451,13,14639,446,73,14747,441,173,14879,435,17,15199,421,13,15289,417,13,15497,408,13,15679,401,2677,16063,385,19,16189,380,13,16459,369,1187,16619,364,37,16799,357,13,16979,351,17,17137,345,263,17359,338,727,17449,335,89,17623,329,59,17819,323,107,17977,317,193,18143,312,109,18313,307,19,18583,300,37,18797,293,13,19163,283,23,19367,277,3253,19519,273,1409,19727,267,89,19937,262,1117,20107,258,23,20287,254,19,20407,250,10313,20627,245,1297,20753,242,19,20939,238,3527,21163,233,1523,21323,228,19,21509,224,193,21617,222,173,21799,218,19,22003,214,1229,22123,212,13,22283,208,19,22573,202,1033,22727,199,1277,22987,194,19,23143,191,11699,23399,186,11783,23567,183,383,23747,179,373,23873,177,13,24103,173,19,24359,168,67,24523,165,1033,24793,161,6247,24989,158,13,25169,155,2113,25357,151]
private def etCase2_2 : ET := L [23,47,207575,37,149,65399,67,269,36163,97,389,24958,233,467,20768,17,647,14944,7,757,12743,7,883,10898,509,1019,9423,19,1217,7858,7,1373,6947,97,1553,6118,809,1619,5862,73,1753,5396,487,1949,4836,19,2053,4579,13,2237,4187,19,2357,3965,619,2477,3761,7,2689,3450,1439,2879,3211,23,3037,3030,59,3187,2879,557,3343,2733,17,3469,2627,7,3697,2453,107,3853,2344,7,4019,2239,2069,4139,2169,67,4289,2083,557,4457,1997,19,4637,1912,7,4789,1846,23,4969,1769,7,5167,1693,7,5279,1653,83,5479,1586,947,5683,1519,23,5843,1471,73,5987,1431,37,6143,1388,1567,6269,1356,17,6359,1333,7,6553,1288,13,6709,1252,17,6869,1218,17,7039,1183,13,7177,1156,13,7307,1131,13,7489,1099,7,7589,1081,3863,7727,1058,19,7867,1034,17,8059,1005,13,8269,973,23,8419,952,7,8597,927,163,8803,900,19,8969,879,7,9157,856,59,9323,837,19,9463,821,7,9619,804,7,9787,786,5003,10007,764,37,10139,751,59,10267,738,13,10453,721,5303,10607,708,2683,10733,696,23,10903,682,2767,11069,668,2803,11213,656,59,11329,647,479,11497,634,7,11663,621,2953,11813,611,67,11927,603,7,12097,591,6173,12347,574,7,12517,563,23,12697,551,2153,12919,538,7,13063,530,947,13259,518,13,13469,506,853,13649,497,19,13757,491,17,13873,484,17,14009,477,7193,14387,459,23,14537,451,37,14653,446,23,14767,440,19,14897,435,317,15217,420,7649,15299,416,1109,15527,407,19,15733,398,13,16069,385,23,16193,380,19,16493,368,13,16693,361,13,16823,357,19,16987,351,23,17159,344,2897,17383,337,17,17477,334,2207,17657,328,13,17837,323,17,17987,317,13,18149,312,37,18353,306,83,18593,299,17,18803,293,17,19177,282,359,19387,277,13,19553,272,823,19753,267,3323,19939,262,107,20117,258,59,20297,253,13,20437,249,17,20639,244,97,20759,242,13,20983,237,10589,21179,232,13,21347,228,163,21517,224,37,21683,221,3637,21823,218,787,22037,213,503,22133,211,59,22303,207,17,22577,202,1423,22769,198,479,22993,194,13,23167,191,19,23447,185,983,23593,182,17,23767,179,11939,23879,177,17,24107,173,17,24379,168,12263,24527,165,13,24883,160,13,25013,158,17,25229,154,1153,25367,151]
private def etCase2_3 : ET := L [13,53,184066,13,157,62061,23,277,35115,17,409,23732,83,499,19418,163,653,14805,193,773,12477,17,919,10465,173,1039,9238,13,1223,7819,233,1399,6810,19,1559,6094,23,1657,5724,37,1777,5321,17,1973,4775,7,2087,4501,373,2239,4184,397,2383,3920,7,2549,3649,19,2699,3437,13,2887,3201,7,3067,2999,67,3217,2850,7,3347,2730,7,3529,2579,13,3719,2438,17,3877,2328,23,4049,2221,173,4153,2161,7,4327,2063,23,4463,1994,7,4649,1907,7,4817,1834,13,4993,1759,863,5179,1689,887,5323,1638,7,5503,1578,1423,5693,1516,17,5849,1469,7,6007,1425,13,6163,1383,523,6277,1354,59,6373,1330,17,6563,1286,17,6733,1247,37,6883,1215,7,7043,1182,3593,7187,1155,7,7309,1131,23,7499,1097,7,7603,1078,17,7753,1053,13,7879,1032,13,8087,1000,17,8297,969,7,8429,950,1433,8599,927,7,8807,900,19,9007,874,2293,9173,854,173,9343,834,37,9473,820,17,9623,804,13,9803,784,13,10037,761,1693,10159,749,107,10273,738,1307,10457,721,13,10609,707,7,10739,695,1823,10939,679,23,11087,667,7,11243,654,7,11369,644,13,11519,633,7,11677,620,73,11827,610,19,11933,602,73,12119,589,7,12377,572,6263,12527,563,73,12703,551,7,12923,538,37,13099,528,67,13267,517,3373,13493,505,17,13669,496,2293,13759,491,257,13879,484,73,14017,477,109,14389,458,3637,14549,450,349,14659,445,19,14783,440,3733,14933,433,23,15227,419,23,15319,416,2593,15559,406,359,15797,395,383,16087,384,2027,16217,379,2753,16519,367,23,16699,361,23,16837,356,59,16993,351,4297,17189,343,8693,17387,337,1459,17509,333,109,17659,328,13,17863,322,19,18013,316,19,18203,311,73,18397,305,13,18617,299,89,18869,291,23,19183,282,89,19403,277,2447,19577,271,37,19759,266,4987,19949,262,17,20129,257,1129,20323,253,5113,20453,249,10343,20687,243,577,20773,241,17,21013,236,107,21187,232,17,21353,228,17,21523,224,23,21713,220,17,21863,217,3677,22063,213,13,22153,211,19,22307,207,5653,22613,201,13,22777,198,397,23027,193,17,23189,189,977,23449,185,19,23599,182,283,23773,179,569,23899,177,19,24169,172,12203,24407,167,17,24617,164,17,24889,160,569,25037,157,13,25247,154,907,25397,151]
private def etCase2_4 : ET := L [13,79,123460,83,167,58339,73,293,33191,19,419,23162,7,547,17701,7,659,14669,199,797,12096,13,937,10261,59,1063,9026,13,1249,7653,23,1427,6673,263,1579,6015,7,1667,5688,19,1787,5290,23,1979,4760,1049,2099,4474,19,2243,4176,199,2389,3910,163,2609,3561,17,2789,3320,727,2909,3172,19,3079,2986,37,3257,2813,23,3359,2719,7,3557,2557,23,3727,2432,7,3907,2309,13,4057,2216,7,4159,2157,1087,4349,2052,83,4483,1985,97,4657,1903,23,4877,1806,7,4999,1757,1297,5189,1685,2693,5387,1616,2753,5507,1577,479,5749,1499,7,5867,1464,503,6037,1417,1549,6197,1374,7,6287,1352,13,6397,1324,367,6607,1275,7,6763,1241,3449,6899,1211,7,7057,1180,13,7229,1146,13,7333,1126,1879,7517,1093,3803,7607,1078,7,7757,1053,7,7883,1032,7,8093,999,7,8317,966,7,8443,948,479,8623,923,7,8849,894,37,9029,871,7,9199,851,19,9349,833,7,9479,819,83,9629,803,7,9829,781,7,10039,761,7,10193,745,17,10303,735,7,10459,721,7,10613,707,7,10753,694,7,10949,678,59,11093,666,7,11257,653,7,11383,643,17,11527,632,487,11689,619,17,11833,609,83,11953,601,13,12143,587,2063,12379,572,17,12547,561,7,12713,550,19,12959,536,7,13147,498,1109,13309,515,17,13499,505,977,13679,495,983,13763,491,17,13907,482,13,14197,468,89,14419,456,1213,14557,450,19,14669,445,2467,14803,439,97,14939,433,17,15233,419,479,15329,415,17,15607,404,13,15809,395,503,16097,384,17,16253,378,1033,16529,367,1193,16703,361,97,16879,355,947,17047,349,1229,17207,343,23,17389,337,19,17519,333,13,17707,327,1489,17869,321,97,18043,315,569,18209,310,9209,18419,304,13,18643,298,4729,18917,289,97,19207,282,809,19417,276,23,19597,271,1237,19793,266,1109,19963,261,373,20143,257,10163,20327,253,19,20483,248,739,20693,243,17,20809,241,37,21017,236,13,21269,229,509,21379,227,13,21529,224,17,21727,220,1823,21877,217,17,22067,213,19,22193,209,37,22349,206,263,22619,201,23,22817,197,19,23029,193,13,23297,187,37,23459,185,13,23609,182,19,23789,179,37,23977,176,23,24197,171,17,24413,167,13,24623,164,17,24923,159,1567,25073,157,59,25253,154,397,25409,151]
private def etCase2_5 : ET := L [17,103,94653,89,179,54421,17,307,31660,73,439,22101,37,593,16317,7,673,14353,7,827,11652,7,953,10086,89,1069,8975,17,1259,7591,7,1429,6663,7,1583,5999,283,1699,5578,13,1847,5113,83,1993,4726,7,2129,4409,7,2269,4126,13,2393,3903,109,2617,3550,233,2797,3310,7,2927,3151,23,3083,2982,17,3299,2772,7,3389,2693,199,3583,2537,7,3739,2424,89,3917,2302,509,4073,2207,17,4217,2125,727,4363,2044,1129,4517,1968,7,4663,1901,13,4889,1801,2543,5087,1723,433,5197,1683,17,5407,1610,89,5519,1573,107,5779,1490,163,5869,1463,19,6043,1416,1033,6199,1374,67,6299,1349,7,6427,1317,7,6637,1268,283,6793,1234,7,6917,1208,19,7069,1177,67,7237,1144,7,7393,1116,7,7547,1088,19,7639,1072,59,7789,1048,59,7907,1028,19,8209,981,37,8363,960,17,8467,945,19,8627,923,7,8863,893,13,9049,869,107,9203,851,1567,9403,827,1187,9497,817,67,9649,801,1229,9833,781,7,10067,758,19,10223,742,7,10333,732,97,10477,719,7,10627,705,5399,10799,690,83,10957,677,7,11117,663,1409,11273,651,89,11393,642,7,11579,628,7,11719,617,17,11867,607,17,11969,600,2027,12163,586,107,12413,570,523,12553,561,193,12739,549,23,12973,535,17,13159,524,13,13313,515,563,13513,504,163,13693,494,383,13789,488,37,13913,482,13,14249,465,233,14447,455,809,14563,450,2447,14683,444,23,14813,438,227,14983,431,2543,15259,418,1279,15349,414,19,15619,403,13,15887,392,83,16103,384,199,16319,376,8273,16547,366,17,16729,360,23,16883,355,19,17063,348,13,17239,342,1087,17393,337,37,17539,332,739,17737,326,37,17909,319,4519,18077,314,23,18217,310,37,18427,304,283,18679,296,17,18973,288,3203,19219,281,13,19423,276,19,19609,270,13,19813,265,17,19993,261,1439,20147,257,13,20333,253,59,20533,247,17,20707,243,1487,20819,240,23,21023,236,3547,21283,229,1783,21397,227,17,21557,223,13,21737,220,13,21893,216,89,22073,213,5557,22229,209,233,22369,206,59,22657,200,19,22877,196,17,23053,193,107,23327,187,163,23473,184,97,23669,181,5953,23813,178,2999,23993,175,367,24223,170,2039,24469,166,13,24649,163,4157,24943,159,37,25087,157,13,25273,153,19,25423,150]
private def etCase2_6 : ET := L [7,113,86267,7,197,49424,13,313,31051,13,443,21900,13,599,16152,13,677,14267,23,829,11624,7,967,9938,7,1093,8774,7,1289,7410,13,1483,6415,7,1597,5945,7,1709,5544,13,1873,5039,37,1999,4711,89,2137,4392,7,2297,4074,109,2399,3893,7,2633,3527,1409,2819,3283,13,2939,3137,193,3089,2976,19,3307,2765,13,3407,2678,7,3613,2515,7,3767,2401,37,3923,2298,2039,4079,2203,19,4219,2124,7,4397,2027,7,4523,1965,73,4673,1896,19,4903,1795,23,5107,1716,7,5209,1678,7,5419,1606,7,5573,1553,7,5783,1489,67,5897,1456,3023,6047,1415,7,6203,1373,109,6323,1342,13,6449,1312,1663,6653,1265,19,6803,1232,23,6947,1201,3539,7079,1175,17,7243,1143,929,7433,1109,17,7549,1087,7,7673,1066,487,7793,1047,37,7919,1026,7,8219,980,523,8369,959,7,8513,939,1453,8719,911,13,8867,892,7,9059,868,7,9227,848,13,9413,826,19,9539,813,59,9677,798,4919,9839,780,839,10069,758,569,10243,740,17,10337,732,7,10487,718,37,10657,702,7,10837,687,13,10973,676,17,11119,663,5639,11279,651,1907,11443,638,7,11593,626,19,11743,616,7,11887,606,13,11987,599,3049,12197,584,7,12433,569,233,12583,559,23,12743,548,7,12979,534,13,13183,523,13,13339,513,17,13567,501,107,13697,494,13,13807,487,13,13963,479,59,14279,464,19,14479,454,19,14593,448,7349,14699,443,353,14827,438,3769,15077,426,13,15263,418,1097,15359,414,7823,15647,402,13,15913,391,733,16127,383,67,16349,374,2069,16553,366,19,16759,359,13,16927,353,1423,17077,348,13,17317,339,8699,17399,336,23,17573,331,19,17747,325,83,17929,319,17,18089,314,13,18253,309,769,18457,303,109,18749,294,97,19013,287,13,19267,280,19,19457,275,17,19687,268,367,19819,265,1669,20029,260,23,20149,257,727,20357,251,23,20563,246,3457,20743,242,13,20879,239,173,21107,234,37,21313,228,19,21433,226,3593,21559,223,3623,21739,219,23,21943,215,19,22079,213,227,22247,208,509,22397,205,17,22679,200,13,22907,196,13,23063,193,19,23333,187,89,23497,184,13,23687,181,19,23827,178,13,23999,175,23,24289,169,19,24473,166,199,24677,163,3119,24953,159,13,25117,156,12653,25307,152,23,25439,150]
private def etCase2_7 : ET := L [7,127,76746,37,223,43647,7,337,28830,7,449,21606,17,613,15780,59,709,13616,107,857,11239,83,997,9634,19,1103,8693,7,1303,7329,373,1493,6371,73,1607,5907,7,1723,5493,7,1877,5028,7,2003,4701,7,2143,4379,577,2309,4051,7,2423,3853,7,2647,3508,59,2833,3266,739,2957,3117,7,3109,2956,23,3313,2759,853,3413,2673,607,3643,2493,13,3797,2381,73,3943,2286,683,4099,2192,7,4229,2118,19,4409,2021,2273,4547,1954,787,4723,1874,7,4943,1779,853,5119,1711,13,5227,1672,907,5443,1598,7,5657,1527,2903,5807,1481,13,5903,1454,17,6053,1412,7,6217,1369,7,6329,1341,7,6469,1307,7,6679,1259,569,6829,1227,193,6949,1201,67,7103,1171,3623,7247,1142,233,7457,1104,3779,7559,1086,7,7687,1064,977,7817,1043,1987,7949,1021,7,8233,978,349,8377,958,7,8527,937,7,8737,909,13,8893,889,37,9103,863,13,9257,845,17,9419,826,37,9547,812,7,9689,797,7,9857,779,5039,10079,757,109,10247,740,863,10357,730,73,10513,716,5333,10667,701,17,10847,686,37,11027,672,929,11149,661,19,11287,650,59,11447,638,13,11597,626,23,11777,613,1487,11897,605,23,12007,597,6113,12227,582,173,12457,567,1049,12589,559,7,12769,547,7,13007,533,19,13187,523,163,13367,512,1697,13577,500,23,13709,493,3457,13829,486,6983,13967,479,397,14293,463,2417,14503,452,23,14629,447,13,14717,443,59,14869,436,13,15107,425,19,15277,417,83,15439,411,163,15649,402,19,15923,390,8069,16139,382,19,16417,371,2767,16603,364,17,16763,359,73,16937,353,83,17099,347,8663,17327,339,2903,17419,336,17,17579,331,17,17749,325,67,17957,318,13,18097,314,163,18257,309,23,18493,302,17,18769,294,227,19069,285,73,19273,280,37,19463,275,67,19699,268,19,19913,263,13,20047,259,13,20177,256,13,20359,251,13,20567,246,23,20747,242,59,20887,239,13,21139,233,73,21317,228,199,21493,225,109,21583,223,37,21757,219,67,21977,215,263,22093,212,359,22259,208,13,22543,202,2837,22697,200,89,22963,195,17,23087,192,23,23369,186,13,23557,183,59,23719,180,13,23843,178,4007,24043,174,6079,24317,169,557,24509,166,89,24743,162,19,24967,158,17,25127,156,19,25309,152,37,25457,150]
private def etCase2 : ET :=
  ET.n (ET.n (ET.n etCase2_0 etCase2_1) (ET.n etCase2_2 etCase2_3)) (ET.n (ET.n etCase2_4 etCase2_5) (ET.n etCase2_6 etCase2_7))

private def etCase3_0 : ET := L [11,23,424283,11,89,109578,19,191,50980,47,283,34368,11,353,27517,11,419,23162,7,491,19736,101,607,15938,11,661,14624,41,739,13058,107,857,11239,17,919,10465,509,1019,9423,19,1103,8693,101,1213,7885,13,1301,7340,179,1433,6644,17,1531,6208,271,1627,5832,97,1747,5415,17,1871,5045,499,1997,4716,13,2081,4515,19,2243,4176,19,2357,3965,1229,2459,3790,163,2609,3561,31,2729,3397,19,2851,3244,41,2953,3122,17,3163,2902,37,3257,2813,73,3359,2719,349,3491,2609,101,3637,2497,13,3797,2381,17,3911,2306,509,4073,2207,47,4231,2117,37,4441,2005,19,4561,1947,73,4673,1896,401,4813,1835,13,4993,1759,17,5101,1718,31,5209,1678,887,5323,1638,151,5437,1600,13,5591,1547,41,5741,1502,17,5849,1469,31,5953,1440,1013,6079,1405,1033,6199,1374,47,6299,1349,17,6427,1317,47,6581,1282,97,6791,1235,1151,6907,1210,17,7039,1183,1201,7207,1150,13,7307,1131,19,7487,1099,947,7577,1083,769,7691,1064,487,7793,1047,59,7907,1028,61,8053,1005,17,8161,989,17,8263,974,37,8363,960,17,8467,945,19,8627,923,1451,8707,912,4391,8783,903,179,8951,881,13,9049,869,73,9199,851,19,9311,839,13,9439,322,19,9539,813,811,9733,792,1229,9833,781,829,9949,770,17,10099,755,47,10247,740,401,10427,724,587,10567,711,59,10739,695,101,10909,681,263,11047,670,797,11159,660,19,11287,650,5711,11423,640,17,11663,621,151,11779,613,19,11933,602,251,12049,595,37,12211,583,6173,12347,574,173,12457,567,233,12583,559,193,12739,549,107,12841,543,929,13007,533,263,13151,525,31,13331,514,17,13499,505,853,13649,497,2293,13759,491,769,13843,486,6983,13967,479,17,14111,472,1193,14317,462,37,14431,456,1459,14591,448,2447,14683,444,19,14821,438,47,14947,432,151,15101,425,17,15233,419,7673,15347,414,1291,15493,408,17,15641,403,31,15749,397,2657,15943,390,41,16073,385,19,16189,380,19,16417,371,1381,16573,365,17,16729,360,17,16831,356,73,16937,353,4273,17093,347,31,17299,340,17,17443,335,31,17609,330,887,17741,326,991,17839,323,17,17987,317,19,18127,313,3037,18223,310,31,18353,306,179,18617,299,37,18797,293,19,19001,287,139,19183,282,73,19273,280,1619,19429,276,181,19549,272,17,19687,268,31,19841,264,47,20023,260,41,20173,256,563,20269,254,227,20431,249,10313,20627,245,1151,20719,243,577,20773,241,109,20929,238,31,21019,236,241,21209,232,1523,21323,228,139,21407,226,17,21523,224,2161,21611,222,59,21713,220,173,21799,218,1823,21877,217,2203,22031,214,5527,22109,212,17,22271,208,2239,22391,205,1879,22549,202,59,22657,200,1423,22769,198,31,22879,196,59,23011,194,577,23081,192,829,23213,189,167,23381,186,151,23557,183,31,23623,182,59,23719,180,11909,23819,178,797,23911,177,4003,24019,175,41,24109,173,12143,24287,169,37,24421,167,61,24523,165,41,24683,163,17,24821,161,3119,24953,159,1567,25073,157,59,25253,154,19,25423,150]
private def etCase3_1 : ET := L [7,29,336487,17,103,94653,7,197,49424,73,293,33191,179,359,27055,7,421,23051,251,503,19262,17,613,15780,7,673,14353,7,743,12986,11,859,11213,13,937,10261,17,1021,9404,277,1109,8645,19,1217,7858,31,1303,7329,719,1439,6616,257,1543,6159,277,1663,5702,73,1753,5396,13,1873,5039,37,1999,4711,1049,2099,4474,19,2281,4103,17,2381,3924,619,2477,3761,109,2617,3550,13,2731,3394,17,2857,3237,19,3041,3026,1583,3167,2898,181,3259,2811,13,3407,2678,13,3511,2593,31,3659,2481,13,3823,2363,37,3923,2298,2039,4079,2203,101,4243,2111,13,4447,2002,17,4591,1933,59,4721,1875,487,4871,1808,17,4999,1757,37,5107,1716,13,5227,1672,31,5333,1635,17,5441,1598,47,5641,1532,479,5749,1499,13,5851,1469,13,5981,1432,61,6101,1399,37,6217,1369,109,6323,1342,13,6449,1312,37,6661,1263,19,6803,1232,691,6911,1209,19,7069,1177,601,7213,1149,61,7321,1129,13,7489,1099,17,7583,1082,3851,7703,1062,19,7829,1041,37,7919,1026,17,8059,1005,19,8171,988,13,8269,973,523,8369,959,17,8501,941,719,8629,923,1453,8719,911,163,8803,900,4481,8963,879,101,9091,864,107,9203,851,59,9323,837,19,9463,821,37,9547,812,541,9739,792,4919,9839,780,151,9967,768,17,10133,752,233,10253,739,163,10433,723,2647,10589,709,31,10789,691,1367,10937,679,691,11057,669,31,11161,660,269,11299,649,1907,11443,638,139,11677,620,59,11801,612,47,11939,602,17,12071,593,6113,12227,582,1031,12373,572,17,12479,566,1049,12589,559,277,12743,548,17,12853,542,271,13009,533,17,13159,524,19,13339,513,563,13513,504,17,13669,496,983,13763,491,41,13859,485,3499,13997,478,61,14153,470,179,14321,462,401,14437,456,19,14593,448,17,14723,442,41,14843,437,3739,14957,432,17,15131,424,587,15263,418,1279,15349,414,47,15511,408,7823,15647,402,7901,15803,395,101,15959,389,383,16087,384,541,16231,379,2741,16447,370,19,16607,364,31,16741,359,61,16837,356,257,16963,352,31,17113,346,37,17317,339,41,17467,334,1471,17653,328,19,17747,325,17,17851,322,19,18013,316,37,18131,313,31,18229,310,167,18371,306,1867,18671,296,17,18803,293,97,19013,287,97,19207,282,193,19301,279,19,19457,275,47,19553,272,31,19717,268,3313,19879,263,257,20047,259,97,20177,256,59,20297,253,73,20441,249,17,20639,244,691,20731,242,101,20807,241,19,20939,238,61,21107,234,101,21211,232,97,21341,228,19,21433,226,17,21557,223,1801,21613,222,17,21727,220,991,21803,218,2741,21929,216,787,22037,213,1229,22123,212,5569,22277,208,509,22397,205,37,22571,202,17,22679,200,73,22777,198,881,22907,196,1151,23021,193,17,23087,192,31,23251,188,17,23393,186,19,23561,183,11813,23627,182,1187,23741,180,19,23827,178,1993,23917,177,4007,24043,174,2011,24133,173,4051,24307,169,101,24443,167,4091,24547,165,823,24691,163,41,24847,160,19,24967,158,37,25087,157,12641,25283,153,4241,25447,150]
private def etCase3_2 : ET := L [7,43,226892,7,113,86267,11,199,48926,17,307,31660,61,367,26463,73,439,22101,13,521,18592,7,617,15677,13,677,14267,7,757,12743,431,863,11154,47,941,10216,173,1039,9238,31,1117,8576,13,1223,7819,13,1327,7193,241,1447,6578,97,1553,6118,17,1667,5688,37,1777,5321,59,1889,4995,13,2003,4701,19,2129,4409,41,2297,4074,13,2393,3903,139,2503,3720,47,2633,3527,461,2767,3348,13,2861,3232,17,3061,3005,59,3187,2879,109,3271,2800,853,3413,2673,41,3527,2581,17,3673,2471,479,3833,2357,73,3943,2286,31,4093,2195,61,4271,2096,97,4463,1994,383,4597,1931,787,4723,1874,13,4889,1801,41,5003,1755,853,5119,1711,523,5231,1670,107,5351,1628,227,5449,1596,101,5657,1527,107,5779,1490,61,5857,1467,41,5987,1431,17,6121,1394,173,6229,1366,151,6343,1337,59,6491,1302,139,6673,1260,569,6829,1227,13,6917,1208,509,7127,1166,401,7219,1147,13,7333,1126,163,7499,1097,271,7589,1081,13,7723,1058,13,7853,1036,1321,7927,1025,2017,8069,1003,47,8179,987,47,8273,972,349,8377,958,19,8513,939,61,8663,918,97,8731,909,17,8807,900,19,8969,879,37,9103,863,1151,9209,850,173,9343,834,37,9473,820,4793,9587,808,2437,9749,790,31,9859,778,277,9973,767,37,10139,751,59,10267,738,1307,10457,721,17,10609,707,5399,10799,690,1823,10939,679,19,11059,669,19,11173,659,41,11317,648,59,11447,638,73,11681,620,73,11827,610,1993,11959,601,31,12091,592,17,12241,581,17,12377,572,19,12503,564,97,12611,557,19,12769,547,179,12889,540,181,13033,531,61,13177,523,41,13367,512,47,13537,502,19,13681,495,383,13789,488,17,13873,484,2333,13999,478,7079,14159,470,31,14323,462,31,14447,455,17,14621,447,73,14747,441,59,14869,436,227,14983,431,541,15149,423,509,15271,418,1097,15359,414,37,15541,407,163,15649,402,19,15809,395,41,15991,388,1609,16091,384,17,16253,378,47,16451,370,1187,16619,364,19,16759,359,401,16843,356,19,16987,351,17,17137,345,433,17321,339,17,17477,334,2207,17657,328,17,17749,325,1789,17891,320,41,18041,315,47,18143,312,73,18251,309,73,18397,305,17,18701,295,17,18871,291,173,19031,286,17,19211,282,1609,19309,279,37,19463,275,19,19571,271,1409,19727,267,17,19891,263,401,20051,259,10091,20183,256,17,20333,253,5113,20453,249,59,20651,244,3457,20743,242,17,20809,241,499,20959,237,271,21139,233,1061,21221,231,17,21353,228,61,21473,225,3593,21559,223,193,21617,222,19,21737,220,47,21809,218,61,21961,215,3677,22063,213,461,22129,212,47,22279,208,2801,22409,205,19,22573,202,2269,22691,200,11393,22787,198,47,22937,195,19,23029,193,11549,23099,192,277,23269,188,11699,23399,186,17,23563,183,179,23629,182,1319,23743,180,2383,23831,178,997,23929,176,167,24049,174,431,24137,173,19,24359,168,2039,24469,166,107,24611,164,139,24743,162,1381,24859,160,227,24971,158,3137,25097,156,12653,25307,152,101,25453,150]
private def etCase3_3 : ET := L [13,53,184066,7,127,76746,7,211,46136,31,311,31251,31,373,26035,13,443,21900,7,547,17701,7,631,15326,11,683,14140,19,761,12676,73,877,10973,7,953,10086,7,1051,9131,17,1123,8530,41,1231,7767,17,1361,7010,37,1481,6424,19,1559,6094,139,1669,5681,19,1787,5290,19,1901,4963,1013,2027,4643,107,2141,4383,577,2309,4051,109,2399,3893,47,2539,3665,17,2687,3453,17,2789,3320,13,2887,3201,73,3067,2999,1601,3203,2864,17,3299,2772,13,3433,2656,61,3539,2571,41,3691,2458,641,3847,2348,997,3989,2257,1033,4133,2172,179,4297,2079,751,4507,1973,13,4603,1928,13,4733,1870,19,4903,1795,167,5011,1752,31,5147,1701,109,5233,1670,269,5381,1618,37,5477,1586,41,5659,1526,59,5783,1489,163,5869,1463,13,6007,1425,73,6133,1391,17,6257,1359,17,6359,1333,163,6521,1295,19,6689,1257,61,6833,1226,151,6947,1201,13,7151,1161,13,7229,1146,167,7349,1124,139,7507,1096,181,7603,1078,3863,7727,1058,19,7867,1034,31,7937,1023,101,8081,1001,13,8191,985,1381,8287,970,233,8389,956,97,8537,936,241,8677,916,13,8737,909,47,8837,896,13,8971,878,13,9127,860,461,9221,849,19,9349,833,73,9491,818,17,9623,804,19,9767,788,47,9871,777,139,10009,764,5081,10163,749,107,10273,738,97,10477,719,37,10657,702,19,10831,688,17,10949,678,41,11071,668,2803,11213,656,59,11329,647,31,11471,636,487,11689,619,17,11833,609,17,11969,600,73,12119,589,6131,12263,579,59,12391,571,139,12511,564,6329,12659,553,1279,12791,546,1291,12911,538,233,13049,530,19,13187,523,17,13397,510,17,13567,501,37,13691,494,6899,13799,488,257,13879,484,17,14009,477,7103,14207,467,19,14327,462,241,14461,454,31,14633,446,461,14753,441,173,14879,435,139,15013,430,101,15151,423,19,15277,417,61,15373,413,2593,15559,406,1567,15671,401,881,15859,393,151,16007,387,97,16103,384,163,16301,376,1373,16477,369,4159,16637,363,17,16763,359,241,16871,355,59,16993,351,47,17203,343,619,17333,339,1459,17509,333,109,17659,328,37,17761,325,37,17909,319,31,18043,315,349,18149,312,163,18257,309,37,18427,304,9371,18743,294,31,18911,290,227,19069,285,1601,19213,281,179,19333,278,31,19469,275,2447,19577,271,139,19739,267,19,19913,263,31,20089,258,101,20201,256,3391,20347,251,19,20483,248,47,20681,243,41,20747,242,1487,20819,240,47,20963,237,31,21143,233,10613,21227,231,167,21377,227,179,21481,225,10781,21563,223,41,21649,221,3623,21739,219,101,21817,218,41,21977,215,17,22067,213,19,22193,209,59,22303,207,17,22441,204,17,22577,202,2837,22697,200,19,22801,198,41,22961,195,11519,23039,193,257,23131,191,17,23291,188,19,23447,185,11783,23567,183,11831,23663,181,31,23747,179,1193,23861,178,17,23971,176,401,24061,174,19,24169,172,2437,24371,168,19,24473,166,17,24617,164,269,24749,162,691,24877,160,181,24979,158,31,25111,156,19,25309,152,37,25457,150]
private def etCase3_4 : ET := L [11,67,145587,13,131,74399,37,223,43647,13,313,31051,7,379,25620,7,449,21606,139,557,17381,107,643,15037,7,701,13773,193,773,12477,11,881,1114,7,967,9938,59,1063,9026,47,1129,8483,13,1249,7653,7,1373,6384,13,1483,6415,263,1579,6015,47,1693,5598,181,1811,5218,193,1931,4883,13,2029,4639,17,2143,4379,167,2339,3997,241,2411,3873,31,2543,3658,19,2699,3437,31,2791,3317,181,2897,3186,19,3079,2986,401,3209,2858,19,3307,2765,431,3449,2643,59,3541,2570,37,3701,2451,107,3853,2344,17,4013,2243,173,4153,2161,271,4337,2058,47,4513,1970,19,4637,1912,19,4751,1862,17,4931,1784,251,5021,1748,41,5167,1693,17,5237,1668,2693,5387,1616,2741,5483,1585,13,5669,1523,193,5791,1487,13,5903,1454,601,6011,1424,37,6143,1388,31,6263,1358,1061,6367,1331,17,6529,1293,13,6709,1252,19,6841,1224,193,6949,1201,1193,7159,1160,17,7243,1143,13,7411,1112,1879,7517,1093,3803,7607,1078,17,7753,1053,41,7873,1033,1987,7949,1021,13,8087,1000,19,8209,981,829,8291,970,61,8419,952,1423,8539,935,31,8681,916,19,8741,908,13,8867,892,19,9007,874,61,9151,857,31,9239,847,1567,9403,827,1187,9497,817,107,9631,803,37,9769,788,61,9883,776,193,10037,761,31,10169,748,17,10303,735,107,10487,718,1069,10691,699,17,10847,686,499,10979,675,241,11087,667,73,11243,654,227,11351,645,383,11491,635,101,11717,617,17,11867,607,19,11971,600,3037,12149,587,31,12277,578,31,12401,571,19,12541,562,181,12671,553,1601,12809,544,1619,12953,536,109,13081,529,59,13217,520,61,13421,509,1697,13577,500,163,13693,494,59,13807,487,139,13901,483,73,14017,477,7121,14243,466,797,14347,461,19,14479,454,563,14639,446,47,14759,441,19,14897,435,1877,15017,429,3793,15173,422,7649,15299,416,31,15377,413,139,15569,405,7841,15683,401,47,15887,392,167,16033,386,179,16111,383,41,16319,376,19,16493,368,37,16651,363,109,16787,358,97,16879,355,37,17021,350,1229,17207,343,17,17341,338,19,17519,333,17,17681,328,47,17767,325,997,17947,318,47,18049,315,101,18181,311,4567,18269,309,41,18451,303,109,18749,294,4729,18917,289,3181,19087,285,641,19231,281,167,19373,277,59,19471,275,9791,19583,271,823,19753,267,433,19919,262,47,20117,258,3371,20227,255,19,20369,251,61,20497,248,10343,20687,243,19,20749,242,73,20879,239,1049,20981,237,17,21149,233,3547,21283,229,509,21379,227,3583,21499,224,31,21577,223,19,21661,221,37,21757,219,61,21839,217,47,21997,214,31,22073,213,37,22201,209,19,22307,207,41,22469,204,5653,22613,201,97,22699,199,181,22807,197,5743,22973,194,17,23053,193,19,23143,191,37,23311,187,37,23459,185,3931,23587,182,61,23669,181,2969,23753,179,17,23869,177,37,23977,176,12041,24083,174,31,24181,172,17,24379,168,17,24481,166,947,24623,164,4127,24763,162,17,24889,160,6247,24989,158,17,25127,156,41,25339,152]
private def etCase3_5 : ET := L [7,71,137380,17,137,71136,19,229,42501,11,331,29355,97,389,24958,19,457,21225,19,571,16951,17,647,14944,59,709,13616,101,809,11915,7,883,10898,97,971,9896,181,1087,8823,7,1163,8231,17,1259,7591,233,1399,6810,31,1489,6388,19,1597,5945,61,1709,5544,61,1831,5159,487,1949,4836,19,2053,4579,269,2153,4358,13,2341,3994,151,2417,3863,13,2549,3649,41,2707,3426,233,2797,3310,1451,2903,3179,193,3089,2976,269,3229,2839,151,3323,2751,173,3461,2633,17,3571,2547,13,3719,2438,17,3877,2328,41,4019,2239,17,4217,2125,241,4339,2057,251,4519,1967,31,4651,1906,13,4759,1858,59,4957,1773,31,5023,1748,47,5171,1692,263,5261,1660,17,5407,1610,2753,5507,1577,947,5683,1519,1453,5813,1479,47,5923,1448,19,6043,1416,41,6151,1386,1567,6269,1356,59,6373,1330,13,6553,1288,17,6733,1247,47,6863,1220,17,6971,1197,13,7177,1156,3623,7247,1142,929,7433,1109,13,7541,1089,19,7639,1072,277,7757,1053,179,7877,1033,37,7993,1015,17,8093,999,587,8219,980,691,8293,969,4211,8423,951,13,8581,929,181,8689,915,4373,8747,907,13,8893,889,17,9011,874,109,9157,856,13,9257,845,181,9413,826,317,9511,816,41,9677,798,163,9781,786,4943,9887,776,719,10067,758,509,10181,746,1033,10331,732,181,10499,717,2677,10709,698,2713,10853,686,5501,11003,674,47,11093,666,563,11261,652,271,11383,643,479,11497,634,31,11719,617,1487,11897,605,461,11987,599,1013,12157,586,41,12301,577,47,12409,570,17,12547,561,61,12689,552,641,12821,544,19,12959,536,37,13099,528,2203,13219,520,269,13451,507,151,13591,500,107,13697,494,3457,13829,486,17,13907,482,167,14029,476,19,14251,465,41,14351,461,17,14519,452,37,14653,446,107,14767,440,829,14923,434,167,15031,428,2531,15187,421,37,15319,416,19,15391,413,19,15581,405,2621,15727,398,241,15907,391,73,16061,385,269,16141,382,61,16349,374,2753,16519,367,17,16661,362,37,16799,357,2111,16889,354,947,17047,349,17,17239,342,263,17359,338,37,17539,332,227,17707,327,17,17783,324,41,17959,318,17,18089,314,17,18191,311,41,18287,308,769,18457,303,17,18769,294,9461,18923,289,1367,19139,283,401,19249,281,17,19381,277,541,19477,275,19,19609,270,37,19759,266,41,19927,262,10061,20123,258,17,20231,255,1699,20389,250,19,20521,247,17,20707,243,1297,20753,242,59,20887,239,269,20983,237,41,21157,233,37,21313,228,31,21391,227,19,21509,224,109,21583,223,37,21683,221,10883,21767,219,19,21851,217,19,22003,214,19,22079,213,5557,22229,209,11171,22343,206,2251,22511,203,263,22619,201,811,22709,199,31,22817,197,1277,22987,194,61,23059,193,11579,23159,191,107,23327,187,163,23473,184,983,23593,182,263,23671,181,17,23767,179,181,23893,177,109,23981,175,73,24091,174,263,24197,171,271,24391,168,12251,24503,166,12329,24659,163,61,24767,162,17,24923,159,37,25013,158,839,25171,155,6337,25349,152]
private def etCase3_6 : ET := L [13,79,123460,37,149,65399,7,239,40717,7,337,28830,11,397,24453,7,463,20948,37,593,16317,163,653,14805,11,727,13276,41,821,11738,151,907,10605,61,977,9834,109,1091,8790,13,1171,8173,641,1283,7446,31,1427,6673,107,1499,6345,73,1607,5907,41,1723,5493,13,1847,5113,13,1951,4831,1031,2063,4555,37,2221,4219,17,2347,3983,173,2423,3853,17,2551,3646,271,2711,3421,1409,2819,3283,19,2927,3151,37,3109,2956,13,3251,2819,13,3329,2745,577,3463,2632,179,3581,2539,47,3761,2406,97,3881,2325,61,4027,2234,19,4219,2124,19,4409,2021,17,4523,1965,97,4657,1903,797,4783,1848,13,4967,1769,101,5051,1737,1297,5189,1685,13,5279,1653,41,5413,1608,31,5519,1573,1423,5693,1516,97,5821,1477,2963,5927,1447,3023,6047,1415,13,6163,1383,19,6271,1356,13,6397,1324,17,6563,1286,13,6761,1241,17,6869,1218,109,6977,1195,3593,7187,1155,37,7253,1141,233,7457,1104,17,7549,1087,3821,7643,1071,431,7759,1052,13,7879,1032,13,8009,1012,811,8111,997,823,8231,978,17,8297,969,41,8447,948,269,8609,925,41,8693,914,73,8761,906,1487,8923,885,751,9013,873,2293,9173,854,17,9283,842,17,9419,826,17,9521,815,173,9689,797,233,9787,786,41,9923,772,839,10069,758,19,10223,742,41,10333,732,73,10513,716,17,10711,698,61,10859,685,19,11021,672,17,11119,663,1409,11273,651,41,11399,642,17,11527,632,17,11731,616,541,11903,604,1201,12011,597,19,12161,586,61,12323,576,107,12413,570,523,12553,561,73,12703,551,2137,12823,544,2161,12967,535,6551,13103,527,947,13259,518,37,13469,506,41,13613,498,2287,13723,493,461,13831,486,37,13913,482,251,14057,475,59,14279,464,109,14389,458,173,14533,451,349,14659,445,19,14783,440,3733,14933,433,251,15061,427,17,15199,421,479,15329,415,31,15439,411,17,15607,404,19,15733,398,17,15913,391,2677,16063,385,577,16157,382,101,16363,374,1033,16529,367,107,16693,361,41,16811,357,47,16921,353,19,17063,348,719,17257,341,181,17377,337,61,17569,331,41,17713,327,59,17819,323,107,17977,317,9059,18119,313,19,18203,311,61,18301,308,31,18539,301,19,18773,293,9479,18959,288,19,19153,283,9629,19259,280,277,19391,277,17,19483,274,983,19661,269,41,19763,266,499,19961,261,17,20129,257,2531,20249,254,31,20399,250,59,20533,247,19,20711,243,97,20759,242,1493,20903,238,17,21013,236,107,21187,232,73,21317,228,1783,21397,227,163,21517,224,251,21587,223,241,21691,220,5443,21773,219,3643,21859,217,5503,22013,214,47,22091,212,227,22247,208,37,22349,206,751,22531,203,11321,22643,201,1033,22727,199,2287,22871,196,479,22993,194,887,23063,193,17,23189,189,19,23333,187,181,23531,183,19,23599,182,47,23689,181,19,23789,179,569,23899,177,2999,23993,175,251,24097,174,12101,24203,171,12203,24407,167,19,24511,166,2467,24671,163,59,24781,161,277,24931,159,139,25021,158,17,25229,154,2113,25357,151]
private def etCase3_7 : ET := L [41,83,117506,13,157,62061,7,281,34614,173,347,27995,17,409,23732,233,467,20768,13,599,16152,7,659,14669,61,733,13166,7,827,11652,7,911,10558,7,1009,9517,7,1093,8774,59,1181,8103,7,1289,7410,17,1429,6663,151,1511,6293,13,1613,5884,433,1733,5460,31,1861,5073,17,1973,4775,47,2069,4542,13,2237,4187,47,2351,3976,61,2441,3819,37,2591,3587,151,2719,3410,59,2833,3266,13,2939,3137,13,3121,2944,271,3253,2817,37,3331,2744,17,3469,2627,601,3607,2519,269,3767,2401,31,3907,2309,13,4057,2216,151,4229,2118,13,4421,2015,2273,4547,1954,37,4663,1901,19,4789,1846,277,4987,1762,47,5077,1727,433,5197,1683,241,5303,1645,181,5431,1602,31,5581,1550,19,5701,1513,139,5839,1472,2969,5939,1444,17,6053,1412,1549,6197,1374,523,6277,1354,107,6421,1319,73,6571,1284,3389,6779,1237,31,6883,1215,233,6991,1193,31,7193,1153,19,7297,1133,17,7481,1100,3779,7559,1086,61,7687,1064,59,7789,1048,563,7883,1032,167,8017,1011,31,8123,995,13,8243,977,277,8311,967,47,8461,946,479,8623,923,4349,8699,913,19,8779,903,31,8929,885,37,9029,871,17,9181,854,101,9293,841,41,9431,824,2383,9533,813,101,9697,796,109,9811,783,17,9929,771,5039,10079,757,569,10243,740,17,10337,732,47,10529,714,2683,10733,696,181,10861,685,37,11027,672,929,11149,661,5639,11279,651,163,11411,641,31,11657,622,19,11743,616,1987,11923,603,17,12037,595,3049,12197,584,17,12343,574,37,12433,569,1571,12569,560,227,12713,550,1069,12829,543,47,12973,535,41,13121,526,277,13297,516,3373,13493,505,619,13619,498,19,13757,491,173,13841,486,179,13963,479,7043,14087,473,17,14281,464,7211,14423,456,97,14551,450,19,14669,445,2467,14803,439,97,14939,433,3769,15077,426,317,15217,420,73,15331,415,19,15467,410,19,15619,403,61,15739,398,19,15923,390,277,16067,385,31,16183,381,31,16369,374,251,16567,366,1193,16703,361,601,16829,356,31,16927,353,1423,17077,348,19,17291,340,109,17441,335,17,17579,331,277,17729,326,2971,17827,323,31,17981,317,151,18121,313,569,18209,310,109,18313,307,19,18583,300,31,18787,293,17,18973,288,17,19177,282,19,19267,280,109,19403,277,31,19531,272,41,19681,268,1237,19793,266,17,19993,261,73,20149,257,1013,20261,254,19,20407,250,10271,20543,247,5179,20717,243,31,20771,241,523,20921,238,37,21017,236,163,21191,232,17,21319,228,107,21401,227,269,21521,224,257,21589,223,31,21701,220,3631,21787,218,17,21863,217,3671,22027,214,263,22093,212,31,22259,208,233,22369,206,17,22543,202,151,22651,200,11369,22739,199,19,22877,196,31,23003,194,769,23071,193,1933,23197,189,19,23371,186,1471,23537,183,227,23609,182,2371,23711,180,17,23801,179,139,23909,177,4001,24007,175,17,24107,173,97,24251,170,17,24413,167,227,24517,166,31,24677,163,1033,24793,161,4157,24943,159,569,25037,157,601,25243,154,1153,25367,151]
private def etCase3 : ET :=
  ET.n (ET.n (ET.n etCase3_0 etCase3_1) (ET.n etCase3_2 etCase3_3)) (ET.n (ET.n etCase3_4 etCase3_5) (ET.n etCase3_6 etCase3_7))

private lemma etCase1_valid : etCase1.valid = true := by rfl
private lemma etCase2_valid : etCase2.valid = true := by rfl
private lemma etCase3_valid : etCase3.valid = true := by rfl

private lemma case1_bound :
    Nat.ble (Nat.add (weightOf 3) (Nat.add etCase1.sumC (sumTrie (stepCase filt1) 8 0 etCase1.toTrie))) BUDGET = true := by
  rfl

private lemma case2_bound :
    Nat.ble (Nat.add (weightOf 5) (Nat.add etCase2.sumC (sumTrie (stepCase filt2) 8 0 etCase2.toTrie))) BUDGET = true := by
  decide +kernel

private lemma case3_bound :
    Nat.ble (Nat.add etCase3.sumC (sumTrie (stepCase filt3) 8 0 etCase3.toTrie)) BUDGET = true := by
  decide +kernel

private theorem digits_ge_13000 (a : ℕ) (ha : AgohGiuga.IsStrongGiuga a) :
    13000 ≤ (Nat.digits 10 a).length := by
  obtain ⟨_, _, hodd, hnorm, _⟩ := strongGiuga_props ha
  apply digits_ge_13000_of_weight_bound ha
  set S := a.primeFactors
  set Slt := S.filter (· < 40000)
  by_cases h3 : 3 ∈ S
  · have h3lt : 3 ∈ Slt := Finset.mem_filter.mpr ⟨h3, by norm_num⟩
    have hsplit : ∑ p ∈ Slt, weightOf p = weightOf 3 + ∑ p ∈ Slt.erase 3, weightOf p :=
      (Finset.add_sum_erase _ _ h3lt).symm
    rw [hsplit]
    have hfilt1 : ∀ p ∈ Slt.erase 3, filt1 p = true := by
      intro p hp
      have hp_ne3 : p ≠ 3 := (Finset.mem_erase.mp hp).1
      have hp_S : p ∈ S := (Finset.mem_filter.mp (Finset.mem_erase.mp hp).2).1
      have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp_S
      have hndvd3 : ¬ (3 ∣ p) := fun h => hp_ne3 (((hp_prime.eq_one_or_self_of_dvd 3 h).resolve_left (by omega)).symm)
      have hndvd_pm1 : ¬ (3 ∣ p - 1) := hnorm 3 h3 p hp_S
      have hmod2 : p % 3 = 2 := by
        have h3p : 3 ≤ p := (hodd p hp_S).2
        have h0 : p % 3 ≠ 0 := fun h => hndvd3 (Nat.dvd_of_mod_eq_zero h)
        have h1 : p % 3 ≠ 1 := fun h => hndvd_pm1 (Nat.dvd_of_mod_eq_zero (by omega))
        omega
      exact Nat.beq_eq.mpr hmod2
    have hle := sum_weight_filter_le (Slt.erase 3) filt1 etCase1
      (fun p hp => Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp (Finset.mem_erase.mp hp).2).1)
      (fun p hp => hodd p (Finset.mem_filter.mp (Finset.mem_erase.mp hp).2).1)
      (fun p hp q hq => hnorm p (Finset.mem_filter.mp (Finset.mem_erase.mp hp).2).1
                                q (Finset.mem_filter.mp (Finset.mem_erase.mp hq).2).1)
      (fun p hp => (Finset.mem_filter.mp (Finset.mem_erase.mp hp).2).2)
      hfilt1 etCase1_valid
    have hbnd := Nat.ble_eq.mp case1_bound
    rw [nat_add, nat_add] at hbnd
    omega
  · by_cases h5 : 5 ∈ S
    · have h5lt : 5 ∈ Slt := Finset.mem_filter.mpr ⟨h5, by norm_num⟩
      have hsplit : ∑ p ∈ Slt, weightOf p = weightOf 5 + ∑ p ∈ Slt.erase 5, weightOf p :=
        (Finset.add_sum_erase _ _ h5lt).symm
      rw [hsplit]
      have hfilt2 : ∀ p ∈ Slt.erase 5, filt2 p = true := by
        intro p hp
        have hp_ne5 : p ≠ 5 := (Finset.mem_erase.mp hp).1
        have hp_S : p ∈ S := (Finset.mem_filter.mp (Finset.mem_erase.mp hp).2).1
        have hp_ne3 : p ≠ 3 := fun h => h3 (h ▸ hp_S)
        have hndvd_pm1 : ¬ (5 ∣ p - 1) := hnorm 5 h5 p hp_S
        have h3p : 3 ≤ p := (hodd p hp_S).2
        have hmod1 : p % 5 ≠ 1 := fun h => hndvd_pm1 (Nat.dvd_of_mod_eq_zero (by omega))
        unfold filt2
        have hb3 : Nat.beq p 3 = false := by
          cases h : Nat.beq p 3 with | false => rfl | true => exact absurd (Nat.beq_eq.mp h) hp_ne3
        have hb5 : Nat.beq p 5 = false := by
          cases h : Nat.beq p 5 with | false => rfl | true => exact absurd (Nat.beq_eq.mp h) hp_ne5
        have hbm : Nat.beq (Nat.mod p 5) 1 = false := by
          cases h : Nat.beq (Nat.mod p 5) 1 with
          | false => rfl
          | true => exact absurd (Nat.beq_eq.mp h) hmod1
        rw [hb3, hb5, hbm]
      have hle := sum_weight_filter_le (Slt.erase 5) filt2 etCase2
        (fun p hp => Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp (Finset.mem_erase.mp hp).2).1)
        (fun p hp => hodd p (Finset.mem_filter.mp (Finset.mem_erase.mp hp).2).1)
        (fun p hp q hq => hnorm p (Finset.mem_filter.mp (Finset.mem_erase.mp hp).2).1
                                  q (Finset.mem_filter.mp (Finset.mem_erase.mp hq).2).1)
        (fun p hp => (Finset.mem_filter.mp (Finset.mem_erase.mp hp).2).2)
        hfilt2 etCase2_valid
      have hbnd := Nat.ble_eq.mp case2_bound
      rw [nat_add, nat_add] at hbnd
      omega
    · have hfilt3 : ∀ p ∈ Slt, filt3 p = true := by
        intro p hp
        have hp_S : p ∈ S := (Finset.mem_filter.mp hp).1
        have hp_ne3 : p ≠ 3 := fun h => h3 (h ▸ hp_S)
        have hp_ne5 : p ≠ 5 := fun h => h5 (h ▸ hp_S)
        unfold filt3
        have hb3 : Nat.beq p 3 = false := by
          cases h : Nat.beq p 3 with | false => rfl | true => exact absurd (Nat.beq_eq.mp h) hp_ne3
        have hb5 : Nat.beq p 5 = false := by
          cases h : Nat.beq p 5 with | false => rfl | true => exact absurd (Nat.beq_eq.mp h) hp_ne5
        rw [hb3, hb5]
      have hle := sum_weight_filter_le Slt filt3 etCase3
        (fun p hp => Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1)
        (fun p hp => hodd p (Finset.mem_filter.mp hp).1)
        (fun p hp q hq => hnorm p (Finset.mem_filter.mp hp).1 q (Finset.mem_filter.mp hq).1)
        (fun p hp => (Finset.mem_filter.mp hp).2)
        hfilt3 etCase3_valid
      have hbnd := Nat.ble_eq.mp case3_bound
      rw [nat_add] at hbnd
      omega

end AgohGiugaSolution

theorem OMA.solution : type_of% @AgohGiuga.agoh_giuga.variants._1000_le_digits_length_of_isStrongGiuga := by
  intro a ha
  have h := AgohGiugaSolution.digits_ge_13000 a ha
  omega
