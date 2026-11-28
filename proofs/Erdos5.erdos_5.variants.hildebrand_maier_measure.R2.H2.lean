import OMAReductions.R_Erdos5_erdos_5_variants_hildebrand_maier_measure_R2
import Mathlib

/-!
# Hildebrand and Maier's two-column upper-bound sieve

This proves step R2.H2 of Erdős problem 5. For two offsets with difference
less than z², the only exceptional primes divide the primorial or consist
of at most one further prime. The squarefree sieve on row indices bounds
the prime pairs uniformly in the offsets and the primorial.

The CRT second-moment argument and squarefree divisor estimates adapt
marcusbuffett's Erdős–Ricci proof (PR #4061), based on Genbox's Erdős 968
sieve (PR #3395). The affine residue lemmas are from the merged Brun proof
(PR #11409). The local-factor bounds use steveDOTdigital's R2 (PR #10024).
Source: Hildebrand and Maier, Gaps between prime numbers (1988), Lemma 3.
Credit: @yuka30240.
-/

noncomputable section
open Finset Filter Asymptotics
namespace HildebrandMaierSieve

structure Columns where
  modulus : ℕ
  first : ℕ
  second : ℕ

def bad (t : Columns) (p : ℕ) : Finset ℕ :=
  (range p).filter (fun r => p ∣ t.first + t.modulus*r ∨ p ∣ t.second + t.modulus*r)

def rho (t : Columns) (p : ℕ) := (bad t p).card
def mult (t : Columns) (d : ℕ) := ∏ p ∈ d.primeFactors, rho t p
def localVal (t : Columns) (p r : ℕ) : ℝ := (rho t p:ℝ)/p - (if r ∈ bad t p then 1 else 0)
def K (t : Columns) (d n : ℕ) : ℝ := ∏ p ∈ d.primeFactors, localVal t p (n%p)

theorem bad_subset (t : Columns) {p : ℕ} (_hp : 0 < p) : bad t p ⊆ range p :=
  filter_subset _ _

theorem val_bound (t : Columns) {p : ℕ} (hp : p.Prime) (r : ℕ) : |localVal t p r| ≤ 1 := by
  have h : (rho t p:ℝ)/(p:ℝ) ≤ 1 := (div_le_one (by exact_mod_cast hp.pos)).2 (by
    exact_mod_cast (Finset.card_le_card (bad_subset t hp.pos)).trans_eq (Finset.card_range p))
  unfold localVal
  split_ifs <;> rw [abs_le] <;> constructor <;> linarith [show (0:ℝ) ≤ (rho t p:ℝ)/p by positivity]

theorem K_bound (t : Columns) (d n : ℕ) : |K t d n| ≤ 1 := by
  rw [K,Finset.abs_prod]
  exact Finset.prod_le_one (fun _ _ => abs_nonneg _) (fun p hp => val_bound t (Nat.prime_of_mem_primeFactors hp) _)

theorem K_sifted (t : Columns) {d n : ℕ} (hd : Squarefree d)
    (no : ∀ p ∈ d.primeFactors, n%p ∉ bad t p) : K t d n = (mult t d:ℝ)/(d:ℝ) := by
  unfold K mult
  push_cast
  calc
    _ = ∏ p ∈ d.primeFactors, ((rho t p:ℝ)/p) := by
      apply Finset.prod_congr rfl
      intro p hp
      simp [localVal,no p hp]
    _ = _ := by
      rw [Finset.prod_div_distrib]
      congr 1
      rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hd]

theorem crt_sum (P : Finset ℕ) (hp : ∀ p ∈ P, p.Prime) (start : ℕ)
    (g : ℕ → ℕ → ℝ) :
    ∑ i ∈ Finset.range (∏ p ∈ P, p), ∏ p ∈ P, g p ((start+i)%p) =
    ∏ p ∈ P, ∑ j ∈ Finset.range p, g p j := by
  classical
  let a (p : P) := p.val
  have hne (p : P) : a p ≠ 0 := (hp _ p.prop).ne_zero
  let (p : P) : NeZero (a p) := ⟨hne p⟩
  let m := ∏ p : P, a p
  have : NeZero m := ⟨Finset.prod_ne_zero_iff.mpr (fun p _ => hne p)⟩
  let e := ZMod.prodEquivPi a (fun i j hij => (Nat.coprime_primes (hp _ i.prop) (hp _ j.prop)).mpr
    (fun eq => hij (Subtype.ext eq)))
  let shift := Equiv.addLeft (start : ZMod m)
  let F (v : (p : P) → ZMod (a p)) := ∏ p, g p.val (v p).val
  have aux (q : ℕ) [NeZero q] (i : Fin q) : ZMod.finEquiv q i = (i.val : ZMod q) := by
    cases q with
    | zero => exact (NeZero.ne 0 rfl).elim
    | succ q => apply Fin.ext; exact (Nat.mod_eq_of_lt i.isLt).symm
  have eqg (i : Fin m) : F (e (shift (ZMod.finEquiv m i))) = ∏ p ∈ P, g p ((start+i.val)%p) := by
    change (∏ p : P, g p.val ((e ((start:ZMod m)+ZMod.finEquiv m i)) p).val) = _
    rw [aux, ← Nat.cast_add]
    rw [map_natCast]
    change (∏ p : P, g p.val (((start+i.val:ℕ) : ZMod (a p)).val)) = _
    simp only [ZMod.val_natCast]
    exact Finset.prod_coe_sort P (fun p => g p ((start+i.val)%p))
  have hm : m = ∏ p ∈ P, p := Finset.prod_coe_sort P id
  rw [← hm,← Fin.sum_univ_eq_sum_range]
  calc
    _ = ∑ i : Fin m, F (e (shift (ZMod.finEquiv m i))) := Finset.sum_congr rfl (fun i _ => (eqg i).symm)
    _ = ∑ v, F v := Equiv.sum_comp (((ZMod.finEquiv m).toEquiv.trans shift).trans e.toEquiv) F
    _ = ∏ p : P, ∑ j : ZMod (a p), g p.val j.val := (Fintype.prod_sum (fun (p : P) (j : ZMod (a p)) => g p.val j.val)).symm
    _ = ∏ p : P, ∑ j ∈ Finset.range p.val, g p.val j := by
      apply Finset.prod_congr rfl
      intro p _
      rw [← Fin.sum_univ_eq_sum_range]
      symm
      calc
        _ = ∑ i : Fin (a p), g p.val (ZMod.finEquiv (a p) i).val := by
          apply Finset.sum_congr rfl
          intro i _
          rw [aux,ZMod.val_natCast,Nat.mod_eq_of_lt i.isLt]
        _ = _ := Equiv.sum_comp (ZMod.finEquiv (a p)).toEquiv (fun j => g p.val j.val)
    _ = _ := Finset.prod_coe_sort P (fun p => ∑ j ∈ Finset.range p, g p j)

def cell (t : Columns) (d p r : ℕ) : ℝ := if p ∈ d.primeFactors then localVal t p r else 1

theorem K_extend (t : Columns) {d : ℕ} {P : Finset ℕ} (h : d.primeFactors ⊆ P) (n : ℕ) :
    K t d n = ∏ p ∈ P, cell t d p (n%p) := by
  calc
    _ = ∏ p ∈ d.primeFactors, cell t d p (n%p) := by
      apply Finset.prod_congr rfl
      intro p hp
      simp [cell,hp]
    _ = _ := Finset.prod_subset h (by intro p _ hp; simp [cell,hp])

theorem indicators (t : Columns) {p : ℕ} (hp : 0 < p) (x : ℝ) :
    (∑ r ∈ range p, if r ∈ bad t p then x else 0) = (rho t p:ℝ)*x := by
  rw [← Finset.sum_filter]
  have eq : (range p).filter (· ∈ bad t p) = bad t p := by
    ext r
    simp only [Finset.mem_filter]
    exact and_iff_right_of_imp (fun h => bad_subset t hp h)
  simp [eq,rho]

theorem local_zero (t : Columns) {p : ℕ} (hp : 0 < p) :
    ∑ r ∈ range p, localVal t p r = 0 := by
  simp only [localVal,Finset.sum_sub_distrib,indicators t hp,Finset.sum_const,Finset.card_range,nsmul_eq_mul]
  have h : (0:ℝ)<p := by exact_mod_cast hp
  field_simp
  ring

theorem local_sq (t : Columns) {p : ℕ} (hp : 0 < p) :
    ∑ r ∈ range p, localVal t p r * localVal t p r ≤ (rho t p:ℝ) := by
  let a := (rho t p:ℝ)/p
  have e (r : ℕ) : localVal t p r * localVal t p r =
      a^2 + (if r ∈ bad t p then 1-2*a else 0) := by
    unfold localVal; dsimp [a]; split_ifs <;> ring
  simp_rw [e]
  rw [Finset.sum_add_distrib,indicators t hp]
  simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]
  dsimp [a]
  have h : (0:ℝ)<p := by exact_mod_cast hp
  field_simp
  nlinarith [sq_nonneg (rho t p:ℝ),mul_nonneg h.le (sq_nonneg (rho t p:ℝ))]

def period (d e : ℕ) := ∏ p ∈ d.primeFactors ∪ e.primeFactors, p

theorem period_property {d e : ℕ} (hd : Squarefree d) (he : Squarefree e) :
    0 < period d e ∧ period d e ≤ d*e := by
  let P := d.primeFactors ∪ e.primeFactors
  have pp (p) (hp : p ∈ P) : p.Prime :=
    (Finset.mem_union.mp hp).elim Nat.prime_of_mem_primeFactors Nat.prime_of_mem_primeFactors
  have h1 : 0 < period d e := Finset.prod_pos (fun p hp => (pp p hp).pos)
  have h2 : 0 < ∏ p ∈ d.primeFactors ∩ e.primeFactors, p :=
    Finset.prod_pos (fun p hp => (Nat.prime_of_mem_primeFactors (Finset.mem_inter.mp hp).1).pos)
  refine ⟨h1, ?_⟩
  calc
    _ ≤ period d e * (∏ p ∈ d.primeFactors ∩ e.primeFactors, p) := Nat.le_mul_of_pos_right _ h2
    _ = d*e := by rw [period,Finset.prod_union_inter,Nat.prod_primeFactors_of_squarefree hd,Nat.prod_primeFactors_of_squarefree he]

theorem block (t : Columns) {d e : ℕ} (hd : Squarefree d) (he : Squarefree e) (start : ℕ) :
    ∑ i ∈ range (period d e), K t d (start+i)*K t e (start+i) ≤
      if d=e then (mult t d:ℝ) else 0 := by
  let P := d.primeFactors ∪ e.primeFactors
  have pp (p) (hp : p ∈ P) : p.Prime :=
    (Finset.mem_union.mp hp).elim Nat.prime_of_mem_primeFactors Nat.prime_of_mem_primeFactors
  let g (p r : ℕ) := cell t d p r * cell t e p r
  have ec (n : ℕ) : K t d n*K t e n = ∏ p ∈ P, g p (n%p) := by
    rw [K_extend t (P := P) Finset.subset_union_left, K_extend t (d := e) (P := P) Finset.subset_union_right,
      ← Finset.prod_mul_distrib]
  simp_rw [ec]
  change ∑ i ∈ range (∏ p ∈ P, p), _ ≤ _
  rw [crt_sum P pp start g]
  by_cases eq : d=e
  · subst e
    rw [if_pos rfl]
    change _ ≤ ((∏ p ∈ d.primeFactors, rho t p : ℕ):ℝ)
    push_cast
    dsimp [P]
    rw [Finset.union_idempotent]
    apply Finset.prod_le_prod
    · intro p _
      exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
    · intro p hp
      simpa only [g,cell,if_pos hp] using local_sq t (Nat.prime_of_mem_primeFactors hp).pos
  · rw [if_neg eq]
    apply le_of_eq
    apply Finset.prod_eq_zero_iff.mpr
    have neq : d.primeFactors ≠ e.primeFactors := by
      intro hp
      have := congrArg (fun x : Finset ℕ => ∏ p ∈ x, p) hp
      simp [Nat.prod_primeFactors_of_squarefree hd,Nat.prod_primeFactors_of_squarefree he] at this
      contradiction
    obtain ⟨p,hp⟩ := Finset.ext_iff.not.mp neq |> Classical.not_forall.mp
    by_cases hpd : p ∈ d.primeFactors
    · have hpe : p ∉ e.primeFactors := by tauto
      have hm : p ∈ P := Finset.mem_union_left _ hpd
      exact ⟨p,hm,by simpa only [g,cell,if_pos hpd,if_neg hpe,mul_one] using local_zero t (pp p hm).pos⟩
    · have hpe : p ∈ e.primeFactors := by tauto
      have hm : p ∈ P := Finset.mem_union_right _ hpe
      exact ⟨p,hm,by simpa only [g,cell,if_neg hpd,if_pos hpe,one_mul] using local_zero t (pp p hm).pos⟩
theorem interval_corr (t : Columns) {d e : ℕ} (hd : Squarefree d) (he : Squarefree e) (start h : ℕ) :
    ∑ i ∈ range h, K t d (start+i)*K t e (start+i) ≤
      (if d=e then (h:ℝ)*mult t d/d else 0) + d*e := by
  let m := period d e
  have hm := (period_property hd he).1
  have hm0 : 0 < m := hm
  have hblocks (b : ℕ) :
      ∑ i ∈ range (b*m), K t d (start+i)*K t e (start+i) ≤ (b:ℝ)*(if d=e then (mult t d:ℝ) else 0) := by
    induction b with
    | zero => simp
    | succ b ih =>
      rw [Nat.succ_mul,Finset.sum_range_add,Nat.cast_succ,add_mul,one_mul]
      apply add_le_add ih
      simpa [Nat.add_assoc] using block t hd he (start+b*m)
  have hrest (b r : ℕ) : ∑ i ∈ range r, K t d (start+(b+i))*K t e (start+(b+i)) ≤ r := by
    calc
      _ ≤ ∑ i ∈ range r, (1:ℝ) := Finset.sum_le_sum fun i _ =>
        (le_abs_self _).trans (by rw [abs_mul]; exact
          (mul_le_mul (K_bound t d _) (K_bound t e _) (abs_nonneg _) zero_le_one).trans_eq (one_mul _))
      _ = _ := by simp
  have hx : h/m*m+h%m = h := Nat.div_add_mod' h m
  conv_lhs => rw [← hx,Finset.sum_range_add]
  have H := add_le_add (hblocks (h/m)) (hrest (h/m*m) (h%m))
  apply H.trans
  have hr : ((h%m:ℕ):ℝ) ≤ (d:ℝ)*e := by
    exact_mod_cast (Nat.mod_lt h hm0).le.trans (period_property hd he).2
  apply add_le_add _ hr
  by_cases eq : d=e
  · subst e
    have hdm : m=d := by simp [m,period,Nat.prod_primeFactors_of_squarefree hd]
    simp only [if_true,hdm]
    rw [le_div_iff₀ (by exact_mod_cast Nat.pos_of_ne_zero hd.ne_zero : (0:ℝ) < d)]
    have hd' : ((h/d:ℕ):ℝ)*d ≤ h := by exact_mod_cast Nat.div_mul_le_self h d
    nlinarith [mul_le_mul_of_nonneg_right hd' (Nat.cast_nonneg (mult t d) : (0:ℝ) ≤ _)]
  · simp [eq]

def divisorsTo (Q : ℕ) : Finset ℕ := (Icc 1 Q).filter Squarefree
def mass (t : Columns) (Q : ℕ) : ℝ := ∑ d ∈ divisorsTo Q, (mult t d:ℝ)/(d:ℝ)
def kernel (t : Columns) (Q n : ℕ) : ℝ := ∑ d ∈ divisorsTo Q, K t d n

theorem energy (t : Columns) (start h Q : ℕ) :
    ∑ i ∈ range h, kernel t Q (start+i)^2 ≤ h*mass t Q + (Q:ℝ)^4 := by
  let D := divisorsTo Q
  have hd (d : ℕ) (h : d ∈ D) : d ≤ Q ∧ Squarefree d := by
    obtain ⟨h,h'⟩ := Finset.mem_filter.mp h
    exact ⟨(Finset.mem_Icc.mp h).2,h'⟩
  have hcard : D.card ≤ Q := (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq
    (show (Icc 1 Q).card = Q by simp)
  have hsum (i : ℕ) : kernel t Q (start+i)^2 =
      ∑ d ∈ D, ∑ e ∈ D, K t d (start+i)*K t e (start+i) := by
    simp [kernel,D,pow_two,Finset.mul_sum,mul_comm]
  simp_rw [hsum]
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑ d ∈ D, ∑ e ∈ D, ((if d=e then (h:ℝ)*mult t d/d else 0)+(Q:ℝ)^2) := by
      apply Finset.sum_le_sum
      intro d hD
      rw [Finset.sum_comm]
      apply Finset.sum_le_sum
      intro e hE
      apply (interval_corr t (hd d hD).2 (hd e hE).2 start h).trans
      apply add_le_add le_rfl
      exact_mod_cast (Nat.mul_le_mul (hd d hD).1 (hd e hE).1).trans_eq (pow_two Q).symm
    _ = h * mass t Q + (D.card:ℝ)^2*Q^2 := by
      simp [Finset.sum_add_distrib, mass,← Finset.mul_sum,div_eq_mul_inv,D,mul_assoc,pow_two]
    _ ≤ _ := by
      apply add_le_add le_rfl
      calc
        _ ≤ (Q:ℝ)^2*Q^2 := by gcongr
        _ = _ := by ring

def sfMass (Q : ℕ) : ℝ := ∑ d ∈ divisorsTo Q, 1/(d:ℝ)
def zetaTwo : ℝ := ∑' n : ℕ, 1/(n:ℝ)^2

theorem size_mass (Q : ℕ) : Real.log (Q+1 : ℕ) ≤ zetaTwo*sfMass Q := by
  classical
  let I := Finset.Icc 1 Q
  let D := divisorsTo Q
  choose a b eqn sf using Nat.sq_mul_squarefree
  let pair (n : ℕ) := (b n,a n)
  have hinj : Function.Injective pair := by
    intro n m h
    have eb : b n = b m := congrArg Prod.fst h
    have ea : a n = a m := congrArg Prod.snd h
    rw [←eqn n,eb,ea,eqn m]
  have sub : I.image pair ⊆ I ×ˢ D := by
    rintro u hu
    obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨hn1,hnQ⟩ := Finset.mem_Icc.mp hn
    have e := eqn n
    have ha : 0 < a n := by by_contra! hz; simp [Nat.eq_zero_of_le_zero hz] at e; omega
    have hb : 0 < b n := by by_contra! hz; simp [Nat.eq_zero_of_le_zero hz] at e; omega
    have ha' := Nat.le_mul_of_pos_left (a n) (pow_pos hb 2)
    have hb' := Nat.le_mul_of_pos_right (b n ^ 2) ha
    have hb2 : b n ≤ b n^2 := by nlinarith
    change (b n,a n) ∈ I ×ˢ D
    exact Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨hb,by dsimp; omega⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨ha,by dsimp; omega⟩,sf n⟩⟩
  let wt (u : ℕ × ℕ) : ℝ := (1/(u.1:ℝ)^2)*(1/(u.2:ℝ))
  calc
    _ ≤ (harmonic Q : ℝ) := log_add_one_le_harmonic Q
    _ = ∑ n ∈ I, wt (pair n) := by
      simp only [harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast]
      apply Finset.sum_congr rfl
      intro n _
      have e := eqn n
      dsimp [wt,pair]
      conv_lhs => rw [←e]
      push_cast
      simp [one_div,mul_comm]
    _ = ∑ u ∈ I.image pair, wt u := (Finset.sum_image hinj.injOn).symm
    _ ≤ ∑ u ∈ I ×ˢ D, wt u := Finset.sum_le_sum_of_subset_of_nonneg sub
        (fun _ _ _ => by dsimp [wt]; positivity)
    _ = (∑ b ∈ I, 1/(b:ℝ)^2)*sfMass Q := by
      rw [Finset.sum_product]
      simp [wt,D,sfMass,Finset.sum_mul,Finset.mul_sum]
      exact Finset.sum_comm
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => by positivity)
      exact (Real.summable_one_div_nat_pow.mpr (by decide : 1 < 2)).sum_le_tsum I (fun _ _ => by positivity)

def divMass (Q : ℕ) : ℝ := ∑ d ∈ divisorsTo Q, (d.divisors.card:ℝ)/d

theorem square_mass (R : ℕ) :
    sfMass R ^ 2 ≤ zetaTwo*divMass (R^2) := by
  classical
  let D := divisorsTo R
  let E := divisorsTo (R^2)
  let I := Finset.Icc 1 R
  let g (x : ℕ×ℕ) := x.1.gcd x.2
  let u (x : ℕ×ℕ) := x.1/g x
  let v (x : ℕ×ℕ) := x.2/g x
  let d (x : ℕ×ℕ) := u x*v x
  let T := I ×ˢ (E.sigma fun k : ℕ => k.divisors)
  let embed (x : ℕ×ℕ) : ℕ × (Σ _ : ℕ, ℕ) := (g x,⟨d x,u x⟩)
  let w (y : ℕ × (Σ _ : ℕ, ℕ)) : ℝ := (1/(y.1:ℝ)^2)*(1/(y.2.1:ℝ))
  have gu (x : ℕ×ℕ) : g x*u x = x.1 := Nat.mul_div_cancel' (Nat.gcd_dvd_left ..)
  have gv (x : ℕ×ℕ) : g x*v x = x.2 := Nat.mul_div_cancel' (Nat.gcd_dvd_right ..)
  have dataFor {a : ℕ} (ha : a ∈ D) : 0 < a ∧ a ≤ R ∧ Squarefree a := by
    have z := Finset.mem_filter.mp ha
    exact ⟨(Finset.mem_Icc.mp z.1).1,(Finset.mem_Icc.mp z.1).2,z.2⟩
  have up (x : ℕ×ℕ) (hx : x ∈ D ×ˢ D) : 0 < u x := by
    have a := (dataFor (Finset.mem_product.mp hx).1).1
    by_contra! hz
    have ee := gu x
    rw [show u x=0 by omega,mul_zero] at ee
    omega
  have map {x : ℕ×ℕ} (hx : x ∈ D ×ˢ D) : embed x ∈ T := by
    obtain ⟨ha,hb⟩ := Finset.mem_product.mp hx
    obtain ⟨ap,ar,asf⟩ := dataFor ha
    obtain ⟨bp,br,bsf⟩ := dataFor hb
    have gp : 0 < g x := Nat.gcd_pos_of_pos_left _ ap
    have ga := Nat.le_of_dvd ap (Nat.gcd_dvd_left x.1 x.2)
    have ua := Nat.div_le_self x.1 (g x)
    have vb := Nat.div_le_self x.2 (g x)
    have dsf : Squarefree (d x) := (Nat.squarefree_mul (Nat.coprime_div_gcd_div_gcd gp)).mpr
      ⟨asf.squarefree_of_dvd (dvd_of_mul_left_dvd (gu x).dvd),bsf.squarefree_of_dvd (dvd_of_mul_left_dvd (gv x).dvd)⟩
    have dr : d x ≤ R^2 := by rw [pow_two]; exact Nat.mul_le_mul (ua.trans ar) (vb.trans br)
    apply Finset.mem_product.mpr
    refine ⟨Finset.mem_Icc.mpr ⟨gp,ga.trans ar⟩,Finset.mem_sigma.mpr ⟨?_,?_⟩⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨Nat.pos_of_ne_zero dsf.ne_zero,dr⟩,dsf⟩
    · exact Nat.mem_divisors.mpr ⟨dvd_mul_right _ _,dsf.ne_zero⟩
  have inj : Set.InjOn embed ↑(D ×ˢ D) := by
    intro x hx y hy e
    have eg : g x = g y := congrArg Prod.fst e
    have ed : u x*v x = u y*v y := congrArg (fun z => z.2.1) e
    have eu : u x = u y := congrArg (fun z => z.2.2) e
    rw [←eu] at ed
    have ev := Nat.eq_of_mul_eq_mul_left (up x hx) ed
    exact Prod.ext (by rw [←gu x,←gu y,eg,eu]) (by rw [←gv x,←gv y,eg,ev])
  have sub : (D ×ˢ D).image embed ⊆ T := by
    intro y hy
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
    exact map hx
  have wh (x : ℕ×ℕ) : w (embed x) = (1/(x.1:ℝ))*(1/(x.2:ℝ)) := by
    have eq : g x^2*d x=x.1*x.2 := by rw [←gu x,←gv x]; dsimp [d]; ring
    dsimp [w,embed]
    simp only [one_div,←mul_inv_rev]
    congr 1
    exact_mod_cast (show d x*g x^2=x.2*x.1 by simpa [mul_comm] using eq)
  calc
    _ = ∑ x ∈ D ×ˢ D, w (embed x) := by
      simp_rw [wh]
      rw [Finset.sum_product,pow_two]
      dsimp [sfMass,D]
      simp only [Finset.sum_mul,Finset.mul_sum]
      exact Finset.sum_comm
    _ = ∑ y ∈ (D ×ˢ D).image embed, w y := (Finset.sum_image inj).symm
    _ ≤ ∑ y ∈ T, w y := Finset.sum_le_sum_of_subset_of_nonneg sub (fun _ _ _ => by dsimp [w]; positivity)
    _ = (∑ i ∈ I, 1/(i:ℝ)^2)*(∑ k ∈ E, (k.divisors.card:ℝ)/k) := by
      rw [Finset.sum_product,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_sigma,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      simp [w,div_eq_mul_inv]
      ring
    _ ≤ zetaTwo*divMass (R^2) := by
      apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => by positivity)
      exact (Real.summable_one_div_nat_pow.mpr (by decide : 1 < 2)).sum_le_tsum I (fun _ _ => by positivity)

def loss (t : ℕ) : ℝ := ∑ g ∈ t.divisors, (g.divisors.card:ℝ)/g

theorem divMass_le (cols : Columns) {t : ℕ} (ht : 0 < t) (Q : ℕ)
    (clean_mult : ∀ {k : ℕ}, Squarefree k → k.Coprime t → mult cols k = k.divisors.card) :
    divMass Q ≤ loss t * mass cols Q := by
  classical
  let D := divisorsTo Q
  let pair (d : ℕ) := (d.gcd t,d/d.gcd t)
  let w (p : ℕ × ℕ) : ℝ := ((p.1.divisors.card:ℝ)/p.1)*((mult cols p.2:ℝ)/p.2)
  have ep (d : ℕ) : (pair d).1*(pair d).2=d := Nat.mul_div_cancel' (Nat.gcd_dvd_left ..)
  have inj : Function.Injective pair := by
    intro d e h
    simpa only [ep] using congrArg (fun p : ℕ × ℕ => p.1*p.2) h
  have into {d : ℕ} (hd : d ∈ D) : pair d ∈ t.divisors ×ˢ D := by
    obtain ⟨hds,hs⟩ := Finset.mem_filter.mp hd
    have sk : Squarefree (pair d).2 := hs.squarefree_of_dvd (dvd_of_mul_left_dvd (ep d).dvd)
    exact Finset.mem_product.mpr ⟨Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right ..,ht.ne'⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨Nat.pos_of_ne_zero sk.ne_zero,
        (Nat.div_le_self ..).trans (Finset.mem_Icc.mp hds).2⟩,sk⟩⟩
  have wh {d : ℕ} (hd : d ∈ D) : w (pair d)=(d.divisors.card:ℝ)/d := by
    have hs := (Finset.mem_filter.mp hd).2
    have sk := (Finset.mem_filter.mp (Finset.mem_product.mp (into hd)).2).2
    have cop : (pair d).1.Coprime (pair d).2 := Nat.coprime_of_squarefree_mul ((ep d).symm ▸ hs)
    have cnt : d.divisors.card = (pair d).1.divisors.card * (pair d).2.divisors.card := by
      simpa only [ep] using cop.card_divisors_mul
    dsimp only [w]
    rw [clean_mult sk (Nat.coprime_div_gcd_of_squarefree hs ht.ne'),div_mul_div_comm,cnt,Nat.cast_mul]
    congr 1
    exact_mod_cast ep d
  calc
    _ = ∑ p ∈ D.image pair, w p := by
      rw [Finset.sum_image inj.injOn]
      exact Finset.sum_congr rfl fun d hd => (wh hd).symm
    _ ≤ ∑ p ∈ t.divisors ×ˢ D, w p :=
      Finset.sum_le_sum_of_subset_of_nonneg (by rintro p hp; obtain ⟨d,hd,rfl⟩ := Finset.mem_image.mp hp; exact into hd)
        (fun p _ _ => by dsimp [w]; positivity)
    _ = _ := by
      rw [Finset.sum_product]
      simp [w,loss,mass,D,Finset.sum_mul,Finset.mul_sum]
      exact Finset.sum_comm

theorem sifted_bound (t : Columns) {u R start h : ℕ} (hu : 0 < u) (hR : 1 ≤ R)
    (hh : (R^2)^4 ≤ h) (P : Finset ℕ) (hsub : P ⊆ range h)
    (sifted : ∀ i ∈ P, ∀ p : ℕ, p.Prime → p ≤ R^2 → (start+i)%p ∉ bad t p)
    (clean : ∀ {k : ℕ}, Squarefree k → k.Coprime u → mult t k = k.divisors.card) :
    (P.card:ℝ) * Real.log (R+1:ℕ)^2 ≤ (2*zetaTwo^3)*(h:ℝ)*loss u := by
  classical
  let M := mass t (R^2)
  have hQ : 1 ≤ R^2 := Nat.one_le_pow _ _ hR
  have h1 : 1 ≤ M := by
    have hm : 1 ∈ divisorsTo (R^2) := Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨le_rfl,hQ⟩,by simp⟩
    have eq : (mult t 1:ℝ)/(1:ℝ)=1 := by simp [mult]
    rw [←eq]
    simpa only [Nat.cast_one,M,mass] using Finset.single_le_sum (f:=fun d : ℕ => (mult t d:ℝ)/(d:ℝ)) (fun d _ => by positivity) hm
  have cap : (P.card:ℝ)*M^2 ≤ h*M+((R^2:ℕ):ℝ)^4 := by
    calc
      _ = ∑ i ∈ P, kernel t (R^2) (start+i)^2 := by
        have same (i : ℕ) (hi : i ∈ P) : kernel t (R^2) (start+i) = M := by
          apply Finset.sum_congr rfl
          intro d hd
          obtain ⟨hb,hsf⟩ := Finset.mem_filter.mp hd
          apply K_sifted t hsf
          intro p hp
          apply sifted i hi p (Nat.prime_of_mem_primeFactors hp)
          exact (Nat.le_of_dvd (Nat.pos_of_ne_zero hsf.ne_zero) (Nat.dvd_of_mem_primeFactors hp)).trans (mem_Icc.mp hb).2
        rw [Finset.sum_congr rfl (fun i hi => congrArg (·^2) (same i hi))]
        simp
      _ ≤ ∑ i ∈ range h, kernel t (R^2) (start+i)^2 :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => sq_nonneg _)
      _ ≤ _ := energy t start h _
  have cp : (P.card:ℝ)*M ≤ 2*h := by
    apply (le_of_mul_le_mul_right _ (by linarith : 0 < M))
    have hh' : ((R^2:ℕ):ℝ)^4 ≤ h := by exact_mod_cast hh
    nlinarith [mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg h : (0:ℝ) ≤ _)]
  have hZ : 0 ≤ zetaTwo := tsum_nonneg fun _ => by positivity
  have hlog : 0 ≤ Real.log (R+1:ℕ) := Real.log_nonneg (by exact_mod_cast Nat.le_add_left 1 R)
  have hlog2 : Real.log (R+1:ℕ)^2 ≤ zetaTwo^3*(loss u*M) := by
    calc
      _ ≤ (zetaTwo * sfMass R)^2 := by nlinarith only [sq_le_sq' (by linarith [size_mass R]) (size_mass R)]
      _ = zetaTwo^2*sfMass R^2 := mul_pow .. 
      _ ≤ zetaTwo^2*(zetaTwo*divMass (R^2)) := by gcongr; exact square_mass R
      _ ≤ zetaTwo^2*(zetaTwo*(loss u*M)) := by gcongr; exact divMass_le t hu _ clean
      _ = _ := by ring
  have hL : 0 ≤ loss u := Finset.sum_nonneg fun _ _ => by positivity
  calc
    _ ≤ P.card*(zetaTwo^3*(loss u*M)) := by gcongr
    _ = (zetaTwo^3*loss u)*(P.card*M) := by ring
    _ ≤ (zetaTwo^3*loss u)*(2*h) := by gcongr
    _ = _ := by ring

open Real UniqueFactorizationMonoid
open OMA.R_Erdos5_erdos_5_variants_hildebrand_maier_measure_R2

-- The residue-class existence and uniqueness lemmas are from the merged Brun proof.
theorem hit_exists (M b a : ℕ) (hb : 0 < b) (hc : Nat.Coprime M b) :
    ∃ r, r < b ∧ b ∣ a + M * r := by
  have : NeZero b := ⟨hb.ne'⟩
  refine ⟨(-(a : ZMod b) * ((ZMod.unitOfCoprime M hc)⁻¹ : (ZMod b)ˣ)).val, ZMod.val_lt _, ?_⟩
  rw [← ZMod.natCast_eq_zero_iff]
  push_cast
  rw [ZMod.natCast_zmod_val, ← ZMod.coe_unitOfCoprime M hc, mul_comm (-(a : ZMod b)) _,
    Units.mul_inv_cancel_left]
  exact add_neg_cancel _

theorem hit_inj (M b a r r' : ℕ) (hc : Nat.Coprime M b) (hr : r < b) (hr' : r' < b)
    (h : b ∣ a + M * r) (h' : b ∣ a + M * r') : r = r' := by
  rcases le_total r r' with hle | hle
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hle
    have e : a + M * (r + d) = (a + M * r) + M * d := by ring
    rw [e] at h'
    have h2 : b ∣ M * d := (Nat.dvd_add_right h).mp h'
    have h3 : b ∣ d := Nat.Coprime.dvd_of_dvd_mul_left hc.symm h2
    have := Nat.eq_zero_of_dvd_of_lt h3 (by omega)
    omega
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hle
    have e : a + M * (r' + d) = (a + M * r') + M * d := by ring
    rw [e] at h
    have h2 : b ∣ M * d := (Nat.dvd_add_right h').mp h
    have h3 : b ∣ d := Nat.Coprime.dvd_of_dvd_mul_left hc.symm h2
    have := Nat.eq_zero_of_dvd_of_lt h3 (by omega)
    omega

lemma rho_eq_two (t : Columns) {p : ℕ} (hp : p.Prime)
    (hq : ¬ p ∣ t.modulus) (hd : ¬ p ∣ t.second - t.first) : rho t p = 2 := by
  have cop := (hp.coprime_iff_not_dvd.mpr hq).symm
  obtain ⟨u, hu, h₁⟩ := hit_exists _ p t.first hp.pos cop
  obtain ⟨v, hv, h₂⟩ := hit_exists _ p t.second hp.pos cop
  have huv : u ≠ v := by
    rintro rfl
    exact hd (by simpa only [Nat.add_sub_add_right] using Nat.dvd_sub h₂ h₁)
  have e : bad t p = {u,v} := by
    ext r
    simp only [bad, mem_filter, mem_range, mem_insert, mem_singleton]
    constructor
    · rintro ⟨hr, h | h⟩
      · exact Or.inl (hit_inj _ _ _ _ _ cop hr hu h h₁)
      · exact Or.inr (hit_inj _ _ _ _ _ cop hr hv h h₂)
    · rintro (rfl | rfl)
      · exact ⟨hu, Or.inl h₁⟩
      · exact ⟨hv, Or.inr h₂⟩
  simp [rho, e, huv]

lemma clean_columns (t : Columns) (hn : t.modulus*(t.second-t.first) ≠ 0)
    {k : ℕ} (hs : Squarefree k) (hc : k.Coprime (radical (t.modulus*(t.second-t.first)))) :
    mult t k = k.divisors.card := by
  rw [mult, Nat.card_divisors hs.ne_zero]
  apply prod_congr rfl
  intro p hp
  have pp := Nat.prime_of_mem_primeFactors hp
  have pd := Nat.dvd_of_mem_primeFactors hp
  have outside : ¬ p ∣ t.modulus*(t.second-t.first) := by
    intro h
    have hh : p ∣ radical (t.modulus*(t.second-t.first)) :=
      (dvd_radical_iff_of_irreducible pp.prime.irreducible hn).2 h
    exact pp.not_dvd_one (hc.gcd_eq_one ▸ Nat.dvd_gcd pd hh)
  rw [Nat.factorization_eq_one_of_squarefree hs pp pd]
  exact rho_eq_two t pp (fun h => outside (dvd_mul_of_dvd_left h _))
    (fun h => outside (dvd_mul_of_dvd_right h _))

lemma loss_of_squarefree {u : ℕ} (hu : Squarefree u) :
    loss u = ∏ p ∈ u.primeFactors, (1 + 2/(p:ℝ)) := by
  rw [loss, ← Nat.divisors_filter_squarefree_of_squarefree hu,
    Nat.sum_divisors_filter_squarefree hu.ne_zero, toFinset_normalizedFactors,
    primeFactors_eq_natPrimeFactors, prod_one_add]
  apply sum_congr rfl
  intro s hs
  have hsub := mem_powerset.mp hs
  let d := ∏ p ∈ s, p
  have hd : d ∣ u := Nat.prod_primeFactors_of_squarefree hu ▸ prod_dvd_prod_of_subset _ _ _ hsub
  have hsf := hu.squarefree_of_dvd hd
  have hfac : d.primeFactors = s := Nat.primeFactors_prod (fun p hp => Nat.prime_of_mem_primeFactors (hsub hp))
  have hnum : d.divisors.card = ∏ _p ∈ s, 2 := by
    rw [Nat.card_divisors hsf.ne_zero, ← hfac]
    apply prod_congr rfl
    intro p hp
    rw [Nat.factorization_eq_one_of_squarefree hsf (Nat.prime_of_mem_primeFactors hp)
      (Nat.dvd_of_mem_primeFactors hp)]
  rw [Finset.prod_val]
  change (d.divisors.card:ℝ)/(d:ℝ) = _
  rw [hnum, prod_div_distrib, Nat.cast_prod]
  simp [d]

lemma offset_loss {z d : ℕ} (hd : 0 < d) (hsmall : d < z^2) :
    let q := primorial z
    loss (radical (q*d)) * ((q.totient:ℝ)/q)^2 ≤ 2 := by
  intro q
  let E := d.primeFactors.filter (fun p => z < p)
  have hq : 0 < q := primorial_pos z
  have partition : (q*d).primeFactors = q.primeFactors ∪ E := by
    rw [Nat.primeFactors_mul hq.ne' hd.ne']
    ext p
    simp only [mem_union, E, mem_filter]
    by_cases hp : p ∈ d.primeFactors
    · have hpr := Nat.prime_of_mem_primeFactors hp
      have inq : p ∈ q.primeFactors ↔ p ≤ z := by
        rw [Nat.mem_primeFactors_of_ne_zero hq.ne_zero]
        exact and_iff_right hpr |>.trans hpr.dvd_primorial_iff
      rw [inq]
      simp only [hp, true_and, or_true, true_iff]
      omega
    · simp [hp]
  have disj : Disjoint q.primeFactors E := by
    apply disjoint_left.mpr
    intro p hp he
    have pp := Nat.prime_of_mem_primeFactors hp
    exact (mem_filter.mp he).2.not_ge (pp.dvd_primorial_iff.mp (Nat.dvd_of_mem_primeFactors hp))
  have hE : (∏ p ∈ E, (1+2/(p:ℝ))) ≤ 2 := by
    have h := Finset.card_le_one.mp (exceptional_large_prime hd hsmall)
    rcases E.eq_empty_or_nonempty with hempty | ⟨p,hp⟩
    · simp [hempty]
    · have eq : E = {p} := by
        ext x
        simp only [mem_singleton]
        exact ⟨fun hx => h x hx p hp, fun he => he ▸ hp⟩
      rw [eq, prod_singleton]
      have pp := Nat.prime_of_mem_primeFactors (mem_filter.mp hp).1
      have hp2 : (2:ℝ) ≤ p := by exact_mod_cast pp.two_le
      have := (div_le_one (by positivity : 0 < (p:ℝ))).mpr hp2
      linarith
  rw [loss_of_squarefree squarefree_radical, Nat.primeFactors_radical, partition, prod_union disj]
  have hqprod := euler_loss hq
  have hE0 : 0 ≤ ∏ p ∈ E, (1+2/(p:ℝ)) := prod_nonneg (fun _ _ => by positivity)
  calc
    _ = ((∏ p ∈ q.primeFactors, (1+2/(p:ℝ))) * ((q.totient:ℝ)/q)^2) *
      (∏ p ∈ E, (1+2/(p:ℝ))) := by ring
    _ ≤ 1*2 := mul_le_mul hqprod hE hE0 zero_le_one
    _ = _ := by norm_num

end HildebrandMaierSieve

open HildebrandMaierSieve Real UniqueFactorizationMonoid

theorem OMA.solution : OMA.R_Erdos5_erdos_5_variants_hildebrand_maier_measure_R2.H2 := by
  have hZ : 0 ≤ zetaTwo := tsum_nonneg fun _ => by positivity
  refine ⟨256*zetaTwo^3+1, by positivity, ?_⟩
  intro z R _hz hR a b hab hsmall q W
  let t : Columns := ⟨q,a,b⟩
  let u := radical (q*(b-a))
  let s := Nat.nthRoot 8 R
  let rows := (Ioc R (2*R)).filter (fun r => (r*q+a).Prime ∧ (r*q+b).Prime)
  let P := (range R).filter (fun i => R+1+i ∈ rows)
  have hq : 0 < q := primorial_pos z
  have hu : 0 < u := Nat.radical_pos _
  have hs : 1 ≤ s := (Nat.le_nthRoot_iff (by decide : (8:ℕ) ≠ 0)).2 (by simpa using (show 1 ≤ R by omega))
  have hr : s^8 ≤ R := Nat.pow_nthRoot_le (.inl (by decide : (8:ℕ) ≠ 0))
  have hwidth : s^2 ≤ R := (pow_le_pow_right₀ hs (by decide : 2 ≤ 8)).trans hr
  have hrows : rows.card ≤ P.card := by
    apply card_le_card_of_injOn (fun r => r-(R+1))
    · intro r h
      have hr' := mem_Ioc.mp (mem_filter.mp h).1
      have e : R+1+(r-(R+1)) = r := by omega
      change r-(R+1) ∈ P
      exact mem_filter.mpr ⟨mem_range.mpr (by omega), by rwa [e]⟩
    · intro r hr' v hv he
      have aa := mem_Ioc.mp (mem_filter.mp hr').1
      have bb := mem_Ioc.mp (mem_filter.mp hv).1
      dsimp at he
      omega
  have sift (i : ℕ) (hi : i ∈ P) (p : ℕ) (pp : p.Prime) (hp : p ≤ s^2) :
      (R+1+i)%p ∉ bad t p := by
    let r := R+1+i
    obtain ⟨h₁,h₂⟩ := (mem_filter.mp (mem_filter.mp hi).2).2
    have hlt : p < r*q := lt_of_lt_of_le (by dsimp [r]; omega) (Nat.le_mul_of_pos_right r hq)
    have nodvd (v : ℕ) (hprime : (r*q+v).Prime) : ¬ p ∣ v+q*(r%p) := by
      intro h
      have he := (Nat.ModEq.dvd_iff (((Nat.mod_modEq r p).mul_left q).add_left v) dvd_rfl).mp h
      have hdvd : p ∣ r*q+v := by simpa only [mul_comm q r, add_comm v] using he
      have heq := (Nat.prime_dvd_prime_iff_eq pp hprime).mp hdvd
      omega
    intro h
    exact (mem_filter.mp h).2.elim (nodvd a h₁) (nodvd b h₂)
  have hclean {k : ℕ} (hsf : Squarefree k) (hcop : k.Coprime u) : mult t k = k.divisors.card :=
    clean_columns t (show q*(b-a) ≠ 0 from Nat.mul_ne_zero hq.ne' (by omega)) hsf hcop
  have hb := sifted_bound t hu hs (by simpa only [← pow_mul] using hr) P
    (filter_subset _ _) sift hclean
  have logbound : log R ≤ 8 * log (s+1 : ℕ) := by
    have he := Nat.lt_pow_nthRoot_add_one (by decide : (8:ℕ) ≠ 0) R
    have he' : (R:ℝ) ≤ ((s+1:ℕ):ℝ)^8 := by exact_mod_cast he.le
    simpa only [log_pow, Nat.cast_ofNat] using log_le_log (by positivity : 0 < (R:ℝ)) he'
  have hlog : 0 ≤ log (R:ℝ) := Real.log_natCast_nonneg _
  have hsq := pow_le_pow_left₀ hlog logbound 2
  let V := (q.totient:ℝ)/q
  have hEuler : loss u * V^2 ≤ 2 := offset_loss (Nat.sub_pos_of_lt hab) hsmall
  change (rows.card:ℝ)*(V*log R)^2 ≤ _
  calc
    _ ≤ (P.card:ℝ) * (8*log (s+1:ℕ))^2 * V^2 := by
      rw [mul_pow, ← mul_assoc, mul_right_comm _ (V^2)]
      gcongr
    _ = 64*((P.card:ℝ)*log (s+1:ℕ)^2)*V^2 := by ring
    _ ≤ 64*((2*zetaTwo^3)*R*loss u)*V^2 := by gcongr
    _ = (128*zetaTwo^3*R)*(loss u*V^2) := by ring
    _ ≤ (128*zetaTwo^3*R)*2 := by gcongr
    _ ≤ _ := by nlinarith [Nat.cast_nonneg (α:=ℝ) R]
